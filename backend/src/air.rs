use std::collections::HashMap;
use std::marker::PhantomData;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use crate::{
    ast::{walkthrough_ast, BoundaryInfo, Expr},
    lookup::{BaseMessageBuilder, ByteRangeAir, Lookup, LookupType},
};

#[derive(Clone)]
pub struct RunwaiAir<F>
where
    F: Field,
{
    runwai_ast: Expr,
    pub width: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> BaseAir<F> for RunwaiAir<F> {
    fn width(&self) -> usize {
        self.width
    }
}

impl<AB: AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder> Air<AB> for RunwaiAir<AB::F>
where
    AB::F: Field + PrimeCharacteristicRing,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();

        let load_var = |is_curr: bool, col_idx: usize| {
            if is_curr {
                local[col_idx].clone()
            } else {
                next[col_idx].clone()
            }
        };

        let mut env = HashMap::<String, Expr>::new();
        let mut lookup_info = Vec::new();
        let mut conditiosn = vec![];

        walkthrough_ast(
            builder,
            &mut env,
            &mut lookup_info,
            self.runwai_ast.clone(),
            &load_var,
            "trace",
            "i",
            "n",
            BoundaryInfo::All,
            &mut conditiosn,
        );

        for c in &lookup_info {
            if c.0 == "u8" {
                let v = c.1.clone().into();
                let mul = c.2.clone();
                let l = Lookup::new(LookupType::ByteRange, v, mul);
                builder.send(l);
            }
        }
    }
}

impl<F: Field> RunwaiAir<F> {
    pub fn new(runwai_ast: Expr, width: usize) -> Self {
        Self {
            runwai_ast,
            width,
            _marker: PhantomData,
        }
    }
}

/// Enum wrapper to handle multiple AIR types in the same vector
#[derive(Clone)]
pub enum RunwaiAirInstance<F: Field> {
    Main(RunwaiAir<F>),
    ByteRange(ByteRangeAir<F>),
}

impl<F: Field> BaseAir<F> for RunwaiAirInstance<F> {
    fn width(&self) -> usize {
        match self {
            RunwaiAirInstance::Main(air) => air.width(),
            RunwaiAirInstance::ByteRange(air) => air.width(),
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            RunwaiAirInstance::Main(air) => air.preprocessed_trace(),
            RunwaiAirInstance::ByteRange(air) => air.preprocessed_trace(),
        }
    }
}

impl<AB> Air<AB> for RunwaiAirInstance<AB::F>
where
    AB: AirBuilder + AirBuilderWithPublicValues + PairBuilder + BaseMessageBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            RunwaiAirInstance::Main(air) => air.eval(builder),
            RunwaiAirInstance::ByteRange(air) => air.eval(builder),
        };
    }
}
