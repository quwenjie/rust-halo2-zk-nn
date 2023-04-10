use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, TableColumn, Assigned},
};

pub fn convert_to_Value<F: FieldExt>(v: i32) -> Value<Assigned<F>> {
    if v >= 0 {
        Value::known(F::from(v as u64).into())
    } else {
        let negv = -v;
        Value::known(F::from(negv as u64).neg().into())
    }
}

pub fn relu(input: i32)->i32
{
    if input<0
    {
        0
    }
    else 
    {
        input
    }
}

/// A lookup table of values from 0..RANGE.
#[derive(Debug, Clone)]
pub(super) struct NonLinearTableConfig<F: FieldExt> {
    pub(super) lookup1: TableColumn,
    pub(super) lookup2: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> NonLinearTableConfig<F> {
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
            || "load non linear table",
            |mut table| {
                let mut offset = 0;
                for value in -65536..65535 {
                    let v2=relu(value/1024);
                    table.assign_cell(
                        || "num_bits",
                        self.lookup1,
                        offset,
                        || convert_to_Value(value),
                    )?;
                    table.assign_cell(
                        || "num_bits",
                        self.lookup2,
                        offset,
                        || convert_to_Value(v2),
                    )?;
                    offset += 1;
                }
                Ok(())
            },
        )
    }
}


#[derive(Debug, Clone)]
pub(super) struct SignTableConfig<F: FieldExt> {
    pub(super) lookup1: TableColumn,
    pub(super) lookup2: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SignTableConfig<F> {
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
            || "load sign table",
            |mut table| {
                let mut offset = 0;
                for value in -65536..65535 {
                    table.assign_cell(
                        || "num_bits",
                        self.lookup1,
                        offset,
                        || convert_to_Value(value),
                    )?;
                    if value>0
                    {
                        table.assign_cell(
                        || "num_bits",
                        self.lookup2,
                        offset,
                        || convert_to_Value(1),
                        )?;
                    }
                    else {
                        table.assign_cell(
                            || "num_bits",
                            self.lookup2,
                            offset,
                            || convert_to_Value(0),
                            )?;
                        }
                    offset += 1;
                }
                Ok(())
            },
        )
    }
}
