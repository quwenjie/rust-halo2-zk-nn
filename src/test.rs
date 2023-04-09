use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
use core::marker::PhantomData;
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
struct LinearConfig {
    advice: [Column<Advice>; 200],
    s_add: Selector,
}

#[derive(Debug, Clone)]
struct RangeCheckConfig<F: FieldExt, const LOOKUP_RANGE: usize> {
    q_lookup: Selector,
    col1: Column<Advice>,
    col2: Column<Advice>,
    table: RangeTableConfig<F, LOOKUP_RANGE>,
}

impl<F: FieldExt, const LOOKUP_RANGE: usize>
    RangeCheckConfig<F, LOOKUP_RANGE>
{
    pub fn configure(meta: &mut ConstraintSystem<F>, col1: Column<Advice>,col2:Column<Advice>) -> Self {
        let q_lookup = meta.complex_selector();
        let table = RangeTableConfig::configure(meta);
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let value1 = meta.query_advice(col1, Rotation::cur());
            let value2 = meta.query_advice(col2, Rotation::cur());
            vec![(q_lookup.clone() * value1, table.lookup1),(q_lookup * value2, table.lookup2)]
        });
        
        Self {
            q_lookup:q_lookup,
            col1:col1,
            col2:col2,
            table:table,
        }
    }

    pub fn assign_lookup(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
        value2: Value<Assigned<F>>,
        offset: usize,
        enable: bool
    ) -> Result<RangeConstrained<F, LOOKUP_RANGE>, Error> {
        
        if enable
        {
            layouter.assign_region(
                || "Assign value for lookup range check",
                |mut region| {
                    // Enable q_lookup
                    self.q_lookup.enable(&mut region, offset)?;
                    // Assign value
                    region
                        .assign_advice(|| "value", self.col1, offset, || value);
                    region
                        .assign_advice(|| "value2", self.col2, offset, || value2)
                        .map(RangeConstrained)
                },
            )
        }
        else 
        {
            layouter.assign_region(
                || "Assign value for lookup range check",
                |mut region| {
                    // Assign value
                    region
                        .assign_advice(|| "value", self.col1, offset, || value);
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
struct MyCircuit<F: FieldExt,  const LOOKUP_RANGE: usize> {
        a_value: Value<Assigned<F>>,
        b_value: Value<Assigned<F>>,
        c_value: Value<Assigned<F>>,
        d_value: Value<Assigned<F>>,
        e_value: Value<Assigned<F>>,
        f_value: Value<Assigned<F>>,
    }

    #[derive(Clone, Debug)]
    struct CircuitConfig<F: FieldExt,  const LOOKUP_RANGE: usize> {
        /// For this chip, we will use two advice columns to implement our instructions.
        /// These are also the columns through which we communicate with other parts of
        /// the circuit.
        advices: [Column<Advice>; 200],
    
        nonlinear_config: RangeCheckConfig<F,LOOKUP_RANGE>,
        linear_config: LinearConfig,
    }

    fn configure_linear<F: FieldExt>(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 200],
    ) -> LinearConfig {
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s_add = meta.selector();

        // Define our multiplication gate!
        meta.create_gate("mul", |meta| {
            // To implement multiplication, we need three advice cells and a selector
            // cell. We arrange them like so:
            //
            // | a0  | a1  | s_mul |
            // |-----|-----|-------|
            // | lhs | rhs | s_mul |
            // | out |     |       |
            //
            // Gates may refer to any relative offsets we want, but each distinct
            // offset adds a cost to the proof. The most common offsets are 0 (the
            // current row), 1 (the next row), and -1 (the previous row), for which
            // `Rotation` has specific constructors.
            
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            //let rhs = meta.query_advice(advice[1], Rotation::cur());
            //let out = meta.query_advice(advice[0], Rotation::next());
            let s_add = meta.query_selector(s_add);

            // The polynomial expression returned from `create_gate` will be
            // constrained by the proving system to equal zero. Our expression
            // has the following properties:
            // - When s_mul = 0, any value is allowed in lhs, rhs, and out.
            // - When s_mul != 0, this constrains lhs * rhs = out.
            //vec![s_mul * (lhs * rhs - out)]
            vec![s_add*lhs]
        });

        LinearConfig { advice, s_add }
    }
fn Demo<T>(v: Vec<T>) -> [T; 200] 
{
        v.try_into()
            .unwrap_or_else(|v: Vec<T>| panic!("Expected a Vec of length {} but it was {}", 200, v.len()))
    }

impl<F: FieldExt, const LOOKUP_RANGE: usize> Circuit<F>
        for MyCircuit<F,  LOOKUP_RANGE>
{
        type Config = CircuitConfig<F, LOOKUP_RANGE>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }
        
        

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let mut advices = Vec::new();
            for i in 0..200 {
                advices.push(meta.advice_column());
            }
            let advices=Demo(advices);
            let nonlinear_config=RangeCheckConfig::<F, LOOKUP_RANGE>::configure(meta, advices[0],advices[1]);
            let linear_config=configure_linear::<F>(meta,advices);
            Self::Config{nonlinear_config,linear_config,advices}
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.nonlinear_config.table.load(&mut layouter)?;
            config.nonlinear_config.assign_lookup(
                layouter.namespace(|| "Assign lookup value"),
                self.a_value,
                self.b_value,
                0 as usize,
                true
            )?;
            config.nonlinear_config.assign_lookup(
                layouter.namespace(|| "Assign lookup value"),
                self.c_value,
                self.d_value,
                1 as usize,
                true
            )?;

            Ok(())
        }
    }


fn main() {
        let k = 18;
        const LOOKUP_RANGE: usize = 17;
        let circuit = MyCircuit::<Fp,  LOOKUP_RANGE> {
                    a_value: Value::known(Fp::from(38001).into()),
                    b_value: Value::known(Fp::from(19000).into()),
                    c_value: Value::known(Fp::from(74002).into()),
                    d_value: Value::known(Fp::from(37001).into()),
                    e_value: Value::known(Fp::from(75002).into()),
                    f_value: Value::known(Fp::from(37001).into()),
        };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

}

    

