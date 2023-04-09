use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, TableColumn},
};

/// A lookup table of values from 0..RANGE.
#[derive(Debug, Clone)]
pub(super) struct RangeTableConfig<F: FieldExt, const RANGE: usize> {
    pub(super) lookup1: TableColumn,
    pub(super) lookup2: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize> RangeTableConfig<F, RANGE> {
    pub(super) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let lookup1 = meta.lookup_table_column();
        let lookup2 = meta.lookup_table_column();

        Self {
            lookup1,
            lookup2,
            _marker: PhantomData,
        }
    }

    pub(super) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "load range-check table",
            |mut table| {
                
                table.assign_cell(
                    || "num_bits",
                    self.lookup1,
                    0,
                    || Value::known(F::from(0 as u64)),
                )?;
                table.assign_cell(
                    || "num_bits",
                    self.lookup2,
                    0,
                    || Value::known(F::from(0 as u64)),
                )?;
                let mut offset = 1;
                for value in 1..1<<RANGE {
                    let v2=value/2;
                    table.assign_cell(
                        || "num_bits",
                        self.lookup1,
                        offset,
                        || Value::known(F::from(value as u64)),
                    )?;
                    table.assign_cell(
                        || "num_bits",
                        self.lookup2,
                        offset,
                        || Value::known(F::from(v2 as u64)),
                    )?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }
}
