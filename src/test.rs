use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Cell, Layouter, Value},
    plonk::{
        Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Instance,
        Selector,
    },
    poly::Rotation,
};
use std::time::Instant;
use std::{cmp::min, marker::PhantomData};
mod table;
use halo2_proofs::{
    circuit::floor_planner::V1,
    dev::{FailureLocation, MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{Any, Circuit},
};
use std::fs::File;
use std::io::{BufReader, Read};
use table::*;

#[derive(Clone, Debug)]
struct LinearConfig<F: FieldExt> {
    advice: [Column<Advice>; 200],
    s_linear: Selector,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct MinusConfig<F: FieldExt> {
    advice: [Column<Advice>; 200],
    s_minus: Selector,
    _marker: PhantomData<F>,
}

#[derive(Debug, Clone)]
struct NonLinearConfig<F: FieldExt> {
    s_lookup: Selector,
    col1: Column<Advice>,
    col2: Column<Advice>,
    table: NonLinearTableConfig<F>,
}

#[derive(Debug, Clone)]
struct SignConfig<F: FieldExt> {
    s_lookup: Selector,
    col1: Column<Advice>,
    col2: Column<Advice>,
    table: SignTableConfig<F>,
}

impl<F: FieldExt> LinearConfig<F> {
    fn configure_linear(meta: &mut ConstraintSystem<F>, advice: [Column<Advice>; 200]) -> Self {
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s_linear = meta.selector();
        meta.create_gate("linear", |meta| {
            let s_linear = meta.query_selector(s_linear);
            let val1 = meta.query_advice(advice[0], Rotation::cur());
            let val2 = meta.query_advice(advice[0], Rotation::next());
            let out = meta.query_advice(advice[180], Rotation::cur());
            let value = val1 * val2 - out;
            let mut linear_gate_check = |range: usize, value: Expression<F>| {
                (1..range).fold(value.clone(), |expr, i| {
                    let val1 = meta.query_advice(advice[i], Rotation::cur());
                    let val2 = meta.query_advice(advice[i], Rotation::next());
                    expr + val1 * val2
                })
            };

            Constraints::with_selector(s_linear, [("linear gate", linear_gate_check(180, value))])
        });

        Self {
            advice,
            s_linear,
            _marker: PhantomData,
        }
    }

    fn assign_linear<
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
            || "Assign value for conv/linear operator check",
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
                    ans += wt * dt;
                }
                for i in end - start..180 {
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
                    self.advice[180],
                    offset,
                    || convert_to_Value(ans),
                )?;
                Ok((out_cell, ans))
            },
        )
    }

    fn assign_dot<const count: usize>(
        &self,
        mut layouter: impl Layouter<F>,
        a: [i32; count],
        b: [i32; count],
    ) -> Result<(AssignedCell<Assigned<F>, F>, i32), Error> {
        layouter.assign_region(
            || "Assign value for dot product check",
            |mut region| {
                let offset = 0;
                self.s_linear.enable(&mut region, offset)?;
                // Assign value
                let mut ans = 0;
                for i in 0..count {
                    region.assign_advice(
                        || "value",
                        self.advice[i],
                        offset,
                        || convert_to_Value(a[i]),
                    );
                    region.assign_advice(
                        || "value2",
                        self.advice[i],
                        offset + 1,
                        || convert_to_Value(b[i]),
                    );
                    ans += a[i] * b[i];
                }
                for i in count..180 {
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
                    self.advice[180],
                    offset,
                    || convert_to_Value(ans),
                )?;
                Ok((out_cell, ans))
            },
        )
    }
}
impl<F: FieldExt> NonLinearConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        col1: Column<Advice>,
        col2: Column<Advice>,
    ) -> Self {
        let s_lookup = meta.complex_selector();
        let table = NonLinearTableConfig::configure(meta);
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
    ) -> Result<(), Error> {
        let offset: usize = 0;
        layouter.assign_region(
            || "Assign value for nonlinear lookup range check",
            |mut region| {
                // Enable s_lookup
                self.s_lookup.enable(&mut region, offset)?;
                // Assign value
                region.assign_advice(|| "value", self.col1, offset, || value);
                region.assign_advice(|| "value2", self.col2, offset, || value2)
            },
        );
        Ok(())
    }
}

impl<F: FieldExt> SignConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        col1: Column<Advice>,
        col2: Column<Advice>,
    ) -> Self {
        let s_lookup = meta.complex_selector();
        let table = SignTableConfig::configure(meta);
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
    ) -> Result<(), Error> {
        let offset: usize = 0;
        layouter.assign_region(
            || "Assign value for sign lookup range check",
            |mut region| {
                // Enable s_lookup
                self.s_lookup.enable(&mut region, offset)?;
                // Assign value
                region.assign_advice(|| "value", self.col1, offset, || value);
                region.assign_advice(|| "value2", self.col2, offset, || value2)
            },
        );
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct CircuitConfig<F: FieldExt> {
    /// For this chip, we will use two advice columns to implement our instructions.
    /// These are also the columns through which we communicate with other parts of
    /// the circuit.
    advice: [Column<Advice>; 200],
    nonlinear_config: NonLinearConfig<F>,
    linear_config: LinearConfig<F>,
    sign_config: SignConfig<F>,
    instance: Column<Instance>,
}

fn construct_conv_layer<
    F: FieldExt,
    const outputsize: usize,
    const image_size: usize,
    const conv1_size: usize,
    const layout1_size: usize,
    const layer1_compute_size: usize,
>(
    config: CircuitConfig<F>,
    mut layouter: impl Layouter<F>,
    layout_file: &str,
    weight_file: &str,
    dt: [i32; image_size],
) -> [i32; outputsize] {
    let (dt_layout, w_layout) = read_layout(layout_file);
    let conv = read_int32(weight_file);
    let mut output1 = [0; outputsize];
    let mut output2 = [0; outputsize];
    for i in 0..outputsize {
        let (cell, ans) = config
            .linear_config
            .assign_linear::<image_size, conv1_size, layout1_size>(
                layouter.namespace(|| "conv1"),
                dt_layout,
                w_layout,
                dt,
                conv,
                i * layer1_compute_size,
                i * layer1_compute_size + layer1_compute_size,
            )
            .unwrap();
        output1[i] = ans;
    }
    output1
}
fn sign(x: i32) -> i32 {
    if x > 0 {
        1
    } else {
        0
    }
}
fn construct_relu_layer<F: FieldExt, const outputsize: usize>(
    config: CircuitConfig<F>,
    mut layouter: impl Layouter<F>,
    output1: [i32; outputsize],
) -> [i32; outputsize] {
    const A: i32 = 1;
    const B: i32 = 1024;
    let mut output2 = [0; outputsize];
    for i in 0..outputsize {
        output2[i] = relu(output1[i] * A / B);
        config.nonlinear_config.assign_lookup(
            layouter.namespace(|| "relu1"),
            convert_to_Value(output1[i]),
            convert_to_Value(output2[i]),
        );
    }
    output2
}

fn construct_sign_layer<F: FieldExt, const outputsize: usize>(
    config: CircuitConfig<F>,
    mut layouter: impl Layouter<F>,
    output1: [i32; outputsize],
) -> [i32; outputsize] {
    let mut output2 = [0; outputsize];
    for i in 0..outputsize {
        output2[i] = sign(output1[i]);
        config.sign_config.assign_lookup(
            layouter.namespace(|| "sign1"),
            convert_to_Value(output1[i]),
            convert_to_Value(output2[i]),
        );
    }
    output2
}

struct MyCircuit<F: FieldExt> {
    dt: [i32; 784],
    label: [i32; 10],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = CircuitConfig<F>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self {
            dt: [0; 784],
            label: [0; 10],
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut advice = Vec::new();
        let instance = meta.instance_column();
        for i in 0..200 {
            advice.push(meta.advice_column());
        }
        let advice: [Column<Advice>; 200] = advice.try_into().unwrap();
        for i in 0..200 {
            meta.enable_equality(advice[i]);
        }
        let nonlinear_config = NonLinearConfig::<F>::configure(meta, advice[0], advice[1]);
        let linear_config = LinearConfig::<F>::configure_linear(meta, advice);
        let sign_config = SignConfig::<F>::configure(meta, advice[0], advice[1]);
        Self::Config {
            advice: advice,
            nonlinear_config: nonlinear_config,
            linear_config: linear_config,
            sign_config: sign_config,
            instance: instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.nonlinear_config.table.load(&mut layouter)?;
        config.sign_config.table.load(&mut layouter);
        const IMAGE_SIZE: usize = 28;
        const K_SIZE: usize = 5;
        const C1_CHANNEL: usize = 5;
        const C2_CHANNEL: usize = 10;
        const C1_OUTPUT_SIZE: usize = 12;
        const C2_OUTPUT_SIZE: usize = 4;
        const image_size: usize = IMAGE_SIZE * IMAGE_SIZE;
        const conv1_size: usize = 1 * C1_CHANNEL * K_SIZE * K_SIZE;
        const conv2_size: usize = C2_CHANNEL * C1_CHANNEL * K_SIZE * K_SIZE;
        const fc1_size: usize = C2_CHANNEL * C2_OUTPUT_SIZE * C2_OUTPUT_SIZE * 10;
        const layer1_compute_size: usize = 1 * K_SIZE * K_SIZE;
        const layer2_compute_size: usize = C1_CHANNEL * K_SIZE * K_SIZE;
        const layer3_compute_size: usize = C2_CHANNEL * C2_OUTPUT_SIZE * C2_OUTPUT_SIZE;
        const STEP1: usize = C1_CHANNEL * C1_OUTPUT_SIZE * C1_OUTPUT_SIZE;
        const STEP2: usize = C2_CHANNEL * C2_OUTPUT_SIZE * C2_OUTPUT_SIZE;
        const STEP3: usize = 10;

        const layout1_size: usize = 2 * K_SIZE * K_SIZE * 1 * STEP1;
        const layout2_size: usize = 2 * K_SIZE * K_SIZE * C1_CHANNEL * STEP2;
        const layout3_size: usize = 2 * C2_CHANNEL * C2_OUTPUT_SIZE * C2_OUTPUT_SIZE * 10;

        let output1: [i32; STEP1] = construct_conv_layer::<
            F,
            STEP1,
            image_size,
            conv1_size,
            layout1_size,
            layer1_compute_size,
        >(
            config.clone(),
            layouter.namespace(|| "conv1"),
            "conv1.layout",
            "conv1.dat",
            self.dt,
        );
        let output1: [i32; STEP1] = construct_relu_layer::<F, STEP1>(
            config.clone(),
            layouter.namespace(|| "relu1"),
            output1,
        );
        let output2: [i32; STEP2] =
            construct_conv_layer::<F, STEP2, STEP1, conv2_size, layout2_size, layer2_compute_size>(
                config.clone(),
                layouter.namespace(|| "conv2"),
                "conv2.layout",
                "conv2.dat",
                output1,
            );
        let output2: [i32; STEP2] = construct_relu_layer::<F, STEP2>(
            config.clone(),
            layouter.namespace(|| "relu2"),
            output2,
        );
        let logits: [i32; STEP3] =
            construct_conv_layer::<F, STEP3, STEP2, fc1_size, layout3_size, layer3_compute_size>(
                config.clone(),
                layouter.namespace(|| "fc1"),
                "fc1.layout",
                "fc1.dat",
                output2,
            );
        let (dot_cell, target_logit) = config
            .linear_config
            .assign_dot::<STEP3>(layouter.namespace(|| "dot1"), logits, self.label)
            .unwrap();
        let logits_minused: [i32; STEP3] = minus_gate(logits, target_logit);
        let logits_minus_sign: [i32; STEP3] = construct_sign_layer(
            config.clone(),
            layouter.namespace(|| "sign1"),
            logits_minused,
        );
        let mask = [1; STEP3];
        let (sign_sum_cell, sign_sum) = config
            .linear_config
            .assign_dot::<STEP3>(layouter.namespace(|| "dot2"), logits_minus_sign, mask)
            .unwrap();
        layouter.constrain_instance(sign_sum_cell.cell(), config.instance, 0);
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

fn read_layout<const layout_size: usize>(
    filename: &str,
) -> ([usize; layout_size], [usize; layout_size]) {
    let layout_data = read_int32::<layout_size>(filename);
    let mut dt_layout = [0; layout_size];
    let mut w_layout = [0; layout_size];
    for i in 0..layout_size {
        if i % 2 == 0 {
            dt_layout[i / 2] = layout_data[i] as usize;
        } else {
            w_layout[i / 2] = layout_data[i] as usize;
        }
    }
    (dt_layout, w_layout)
}

fn minus_gate<const count: usize>(a: [i32; count], b: i32) -> [i32; count] {
    let mut c = [0; count];
    for i in 0..count {
        c[i] = a[i] - b;
    }
    return c;
}

fn main() {
    let k = 18;
    const image_num: usize = 100;
    let tmp = read_int32::<{ 2 * image_num }>("results.dat");
    let mut predict = [0usize; image_num];
    let mut label = [0usize; image_num];
    for i in 0..image_num {
        predict[i] = tmp[2 * i] as usize;
        label[i] = tmp[2 * i + 1] as usize;
    }

    for i in 0..image_num {
        let dt = read_int32::<784usize>(&format!("images/img{}.dat", i));
        let mut onehot: [i32; 10] = [0; 10];
        onehot[predict[i]] = 1;
        let circuit = MyCircuit::<Fp> {
            dt: dt,
            label: onehot,
            _marker: PhantomData,
        };
        let now = Instant::now();
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(0)]]).unwrap();
        prover.assert_satisfied();
        let elapsed_time = now.elapsed();
        println!(
            "pass image {} proved its predict:{} ground truth is {}, prove took time: {}",
            i,
            predict[i],
            label[i],
            elapsed_time.as_secs()
        );
    }
}
