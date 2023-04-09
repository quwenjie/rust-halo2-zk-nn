use std::marker::PhantomData;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
mod table;
use table::*;

/// This helper checks that the value witnessed in a given cell is within a given range.
/// Depending on the range, this helper uses either a range-check expression (for small ranges),
/// or a lookup (for large ranges).
///
///        value     |    q_range_check    |   q_lookup  |  table_value  |
///       ----------------------------------------------------------------
///          v_0     |         1           |      0      |       0       |
///          v_1     |         0           |      1      |       1       |
///

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
struct RangeConstrained<F: FieldExt, const RANGE: usize>(AssignedCell<Assigned<F>, F>);


#[derive(Clone, Debug)]
struct LinearConfig<F: FieldExt> {
    advice: [Column<Advice>; 200],
    s_add: Selector,
    _marker: PhantomData<F>,
}

#[derive(Debug, Clone)]
struct RangeCheckConfig<F: FieldExt, const LOOKUP_RANGE: usize> {
    q_lookup: Selector,
    col1: Column<Advice>,
    col2: Column<Advice>,
    table: RangeTableConfig<F, LOOKUP_RANGE>,
}

impl<F: FieldExt> LinearConfig<F> {
    fn configure_linear(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 200],
    ) -> Self {
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s_add = meta.selector();
    
        // Define our multiplication gate!
        meta.create_gate("mul", |meta| {
            let range = 150;
            let s_add = meta.query_selector(s_add);
            let val1 = meta.query_advice(advice[0], Rotation::cur());
            let val2 = meta.query_advice(advice[0], Rotation::next());
            let out = meta.query_advice(advice[150], Rotation::cur());
            let value = val1 * val2 - out;
            let mut range_check = |range: usize, value: Expression<F>| {
                (1..range).fold(value.clone(), |expr, i| {
                    let val1 = meta.query_advice(advice[0], Rotation::cur());
                    let val2 = meta.query_advice(advice[0], Rotation::next());
                    expr + val1 * val2
                })
            };
    
            Constraints::with_selector(s_add, [("range check", range_check(150, value))])
        });
    
        Self { advice, s_add, _marker:PhantomData }
    }
    pub fn assign_linear(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
        value2: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        let offset:usize=0;
        layouter.assign_region(
                || "Assign value for lookup range check",
                |mut region| {
                    // Enable q_lookup
                self.s_add.enable(&mut region, offset)?;
                    // Assign value
                region.assign_advice(|| "value", self.advice[0], offset, || value);
                region.assign_advice(|| "value2", self.advice[0], offset+1, || value2);
                for i in 1..149
                {
                    region.assign_advice(|| "value", self.advice[i], offset, || value);
                    region.assign_advice(|| "value2", self.advice[i], offset+1, || value2);
                }
                region.assign_advice(|| "value", self.advice[150], offset, || Value::known(F::from(150))*value.evaluate()*value2.evaluate());
                Ok(())
            }
        );
        Ok(())
    }

}
impl<F: FieldExt, const LOOKUP_RANGE: usize> RangeCheckConfig<F, LOOKUP_RANGE> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        col1: Column<Advice>,
        col2: Column<Advice>,
    ) -> Self {
        let q_lookup = meta.complex_selector();
        let table = RangeTableConfig::configure(meta);
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let value1 = meta.query_advice(col1, Rotation::cur());
            let value2 = meta.query_advice(col2, Rotation::cur());
            vec![
                (q_lookup.clone() * value1, table.lookup1),
                (q_lookup * value2, table.lookup2),
            ]
        });

        Self {
            q_lookup: q_lookup,
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
        enable: bool,
    ) -> Result<RangeConstrained<F, LOOKUP_RANGE>, Error> {
        let offset:usize=0;
        if enable {
            layouter.assign_region(
                || "Assign value for lookup range check",
                |mut region| {
                    // Enable q_lookup
                    self.q_lookup.enable(&mut region, offset)?;
                    // Assign value
                    region.assign_advice(|| "value", self.col1, offset, || value);
                    region
                        .assign_advice(|| "value2", self.col2, offset, || value2)
                        .map(RangeConstrained)
                },
            )
        } else {
            layouter.assign_region(
                || "Assign value for lookup range check",
                |mut region| {
                    // Assign value
                    region.assign_advice(|| "value", self.col1, offset, || value);
                    region
                        .assign_advice(|| "value2", self.col2, offset, || value2)
                        .map(RangeConstrained)
                },
            )
        }
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
    b_value: Value<Assigned<F>>,
    c_value: Value<Assigned<F>>,
    d_value: Value<Assigned<F>>,
    e_value: Value<Assigned<F>>,
    f_value: Value<Assigned<F>>,
    g_value: Value<Assigned<F>>
}

#[derive(Clone, Debug)]
struct CircuitConfig<F: FieldExt, const LOOKUP_RANGE: usize> {
    /// For this chip, we will use two advice columns to implement our instructions.
    /// These are also the columns through which we communicate with other parts of
    /// the circuit.
    advice: [Column<Advice>; 200],
    nonlinear_config: RangeCheckConfig<F, LOOKUP_RANGE>,
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
        let nonlinear_config =
            RangeCheckConfig::<F, LOOKUP_RANGE>::configure(meta, advice[0], advice[1]);
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
        config.nonlinear_config.assign_lookup(
            layouter.namespace(|| "Assign lookup value map"),
            self.a_value,
            self.b_value,
            true,
        )?;
        config.nonlinear_config.assign_lookup(
            layouter.namespace(|| "Assign lookup value map"),
            self.c_value,
            self.d_value,
            true,
        )?;
        config.linear_config.assign_linear(layouter.namespace(|| "linear lookup place"), self.e_value, self.f_value);
        Ok(())
    }
}

fn main() {
    let k = 18;
    const LOOKUP_RANGE: usize = 17;
    let circuit = MyCircuit::<Fp, LOOKUP_RANGE> {
        a_value: Value::known(Fp::from(38001).into()),
        b_value: Value::known(Fp::from(19000).into()),
        c_value: Value::known(Fp::from(74002).into()),
        d_value: Value::known(Fp::from(37001).into()),
        e_value: Value::known(Fp::from(23).into()),
        f_value: Value::known(Fp::from(3).into()),
        g_value: Value::known(Fp::from(3).into()),
    };
    //println!("{}",Value::known(Fp::from(38001).into()).evaluate());
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
}
