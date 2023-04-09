use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Cell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;
mod table;
use std::fs::File;
use std::io::{BufReader, Read};
use table::*;

#[derive(Debug, Clone)]
struct RangeConstrained<F: FieldExt, const RANGE: usize>(AssignedCell<Assigned<F>, F>);

#[derive(Clone, Debug)]
struct LinearConfig<F: FieldExt> {
    advice: [Column<Advice>; 200],
    s_linear: Selector,
    _marker: PhantomData<F>,
}

#[derive(Debug, Clone)]
struct NonLinearConfig<F: FieldExt, const LOOKUP_RANGE: usize> {
    s_lookup: Selector,
    col1: Column<Advice>,
    col2: Column<Advice>,
    table: RangeTableConfig<F, LOOKUP_RANGE>,
}

impl<F: FieldExt> LinearConfig<F> {
    fn configure_linear(meta: &mut ConstraintSystem<F>, advice: [Column<Advice>; 200]) -> Self {
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s_linear = meta.selector();
        meta.create_gate("linear", |meta| {
            let range = 150;
            let s_linear = meta.query_selector(s_linear);
            let val1 = meta.query_advice(advice[0], Rotation::cur());
            let val2 = meta.query_advice(advice[0], Rotation::next());
            let out = meta.query_advice(advice[150], Rotation::cur());
            let value = val1 * val2 - out;
            let mut range_check = |range: usize, value: Expression<F>| {
                (1..range).fold(value.clone(), |expr, i| {
                    let val1 = meta.query_advice(advice[i], Rotation::cur());
                    let val2 = meta.query_advice(advice[i], Rotation::next());
                    expr + val1 * val2
                })
            };

            Constraints::with_selector(s_linear, [("range check", range_check(150, value))])
        });

        Self {
            advice,
            s_linear,
            _marker: PhantomData,
        }
    }

    fn assign_array<
        const data_count: usize,
        const weight_count: usize,
        const layout_size: usize,
    >(
        &self,
        mut layouter: impl Layouter<F>,
        data_layout: [usize; layout_size],
        weight_layout: [usize; layout_size],
        data: [i32; data_count],
        weight: [i32; weight_count],
        start: usize,
        end: usize,
    ) -> Result<(AssignedCell<Assigned<F>, F>, i32), Error> {
        layouter.assign_region(
            || "Assign value for lookup range check",
            |mut region| {
                let offset = 0;
                self.s_linear.enable(&mut region, offset)?;
                // Assign value
                let mut ans = 0;
                for i in start..end {
                    let wt = weight[weight_layout[i]];
                    let dt = data[data_layout[i]];
                    region.assign_advice(
                        || "value",
                        self.advice[i - start],
                        offset,
                        || convert_to_Value(wt),
                    );
                    region.assign_advice(
                        || "value2",
                        self.advice[i - start],
                        offset + 1,
                        || convert_to_Value(dt),
                    );
                    ans += weight[weight_layout[i]] * data[data_layout[i]];
                }

                for i in end - start..150 {
                    region.assign_advice(
                        || "value",
                        self.advice[i],
                        offset,
                        || convert_to_Value(0),
                    );
                    region.assign_advice(
                        || "value2",
                        self.advice[i],
                        offset + 1,
                        || convert_to_Value(0),
                    );
                }
                let out_cell = region.assign_advice(
                    || "value",
                    self.advice[150],
                    offset,
                    || convert_to_Value(ans),
                )?;
                Ok((out_cell, ans))
            },
        )
    }
}
impl<F: FieldExt, const LOOKUP_RANGE: usize> NonLinearConfig<F, LOOKUP_RANGE> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        col1: Column<Advice>,
        col2: Column<Advice>,
    ) -> Self {
        let s_lookup = meta.complex_selector();
        let table = RangeTableConfig::configure(meta);
        meta.lookup(|meta| {
            let s_lookup = meta.query_selector(s_lookup);
            let value1 = meta.query_advice(col1, Rotation::cur());
            let value2 = meta.query_advice(col2, Rotation::cur());
            vec![
                (s_lookup.clone() * value1, table.lookup1),
                (s_lookup * value2, table.lookup2),
            ]
        });

        Self {
            s_lookup: s_lookup,
            col1: col1,
            col2: col2,
            table: table,
        }
    }

    pub fn assign_lookup(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
        value2: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F, LOOKUP_RANGE>, Error> {
        let offset: usize = 0;
        layouter.assign_region(
            || "Assign value for lookup range check",
            |mut region| {
                // Enable s_lookup
                self.s_lookup.enable(&mut region, offset)?;
                // Assign value
                region.assign_advice(|| "value", self.col1, offset, || value);
                region
                    .assign_advice(|| "value2", self.col2, offset, || value2)
                    .map(RangeConstrained)
            },
        )
    }
}

use halo2_proofs::{
    circuit::floor_planner::V1,
    dev::{FailureLocation, MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{Any, Circuit},
};

#[derive(Default)]
struct MyCircuit<F: FieldExt, const LOOKUP_RANGE: usize> {
    a_value: Value<Assigned<F>>,
}

#[derive(Clone, Debug)]
struct CircuitConfig<F: FieldExt, const LOOKUP_RANGE: usize> {
    /// For this chip, we will use two advice columns to implement our instructions.
    /// These are also the columns through which we communicate with other parts of
    /// the circuit.
    advice: [Column<Advice>; 200],
    nonlinear_config: NonLinearConfig<F, LOOKUP_RANGE>,
    linear_config: LinearConfig<F>,
}

fn Demo<T>(v: Vec<T>) -> [T; 200] {
    v.try_into().unwrap_or_else(|v: Vec<T>| {
        panic!("Expected a Vec of length {} but it was {}", 200, v.len())
    })
}

impl<F: FieldExt, const LOOKUP_RANGE: usize> Circuit<F> for MyCircuit<F, LOOKUP_RANGE> {
    type Config = CircuitConfig<F, LOOKUP_RANGE>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut advice = Vec::new();
        for i in 0..200 {
            advice.push(meta.advice_column());
        }
        let advice = Demo(advice);
        for i in 0..200 {
            meta.enable_equality(advice[i]);
        }
        let nonlinear_config =NonLinearConfig::<F, LOOKUP_RANGE>::configure(meta, advice[0], advice[1]);
        let linear_config = LinearConfig::<F>::configure_linear(meta, advice);
        Self::Config {
            nonlinear_config,
            linear_config,
            advice,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.nonlinear_config.table.load(&mut layouter)?;
        const A:i32=1;
        const B:i32=1024;
        const IMAGE_SIZE: usize = 28;
        const K_SIZE: usize = 5;
        const C1_CHANNEL: usize = 5;
        const C1_OUTPUT_SIZE: usize = 12;
        const image_size: usize = IMAGE_SIZE * IMAGE_SIZE;
        const conv1_size: usize = 1 * C1_CHANNEL * K_SIZE * K_SIZE;
        const layout1_size: usize = K_SIZE * K_SIZE * C1_CHANNEL * C1_OUTPUT_SIZE * C1_OUTPUT_SIZE;
        const layer1_compute_size: usize = 1 * K_SIZE * K_SIZE;
        let layout_data = read_int32::<{ layout1_size * 2 }>("conv1.layout");
        let mut dt_layout = [0 as usize; layout1_size];
        let mut w_layout = [0 as usize; layout1_size];
        for i in 0..layout1_size * 2 {
            if i % 2 == 0 {
                dt_layout[i / 2] = layout_data[i] as usize;
            } else {
                w_layout[i / 2] = layout_data[i] as usize;
            }
        }
        let dt = read_int32::<image_size>("img.dat");
        let conv1 = read_int32::<conv1_size>("conv1.dat");
        const STEP1: usize = 5 * 12 * 12;
        let mut output1 = [0; STEP1];
        let mut output2 = [0; STEP1];

        for i in 0..STEP1 {
            let (cell, ans) = config
                .linear_config
                .assign_array::<{ image_size }, { conv1_size }, layout1_size>(
                    layouter.namespace(|| "linear lookup place"),
                    dt_layout,
                    w_layout,
                    dt,
                    conv1,
                    i * layer1_compute_size,
                    i * layer1_compute_size + layer1_compute_size,
                )
                .unwrap();
            output1[i] = ans;
        }
        for i in 0..STEP1 {
            output2[i] = relu(output1[i]*A / B);
            config.nonlinear_config.assign_lookup(
                layouter.namespace(|| "Assign lookup value map"),
                convert_to_Value(output1[i]),
                convert_to_Value(output2[i]),
            )?;
        }
        Ok(())
    }
}
fn read_int32<const count: usize>(filename: &str) -> [i32; count] {
    let mut ret = Vec::new();
    let mut file = File::open(filename).unwrap();
    let mut buffer = vec![0; 4];
    for i in 0..count {
        file.read_exact(&mut buffer).unwrap();
        let num = i32::from_le_bytes([buffer[0], buffer[1], buffer[2], buffer[3]]);
        ret.push(num);
    }
    let ret_array = ret.try_into().unwrap_or_else(|v: Vec<i32>| {
        panic!("Expected a Vec of length {} but it was {}", count, v.len())
    });
    ret_array
}
fn main() {
    let k = 18;
    const LOOKUP_RANGE: usize = 17;
    let circuit = MyCircuit::<Fp, LOOKUP_RANGE> {
        a_value: Value::known(Fp::from(38001).into()),
    };
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
}
