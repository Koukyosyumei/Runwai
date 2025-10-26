use std::collections::HashMap;
use std::marker::PhantomData;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_uni_stark::SymbolicAirBuilder;

use crate::ast::{walkthrough_ast, BoundaryInfo, Expr};

#[derive(Clone)]
pub struct RunwaiAir<F>
where
    F: Field,
{
    runwai_ast: Expr,
    width: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> BaseAir<F> for RunwaiAir<F> {
    fn width(&self) -> usize {
        self.width
    }
}

impl<AB: AirBuilderWithPublicValues> Air<AB> for RunwaiAir<AB::F>
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
        let mut conditiosn = vec![];

        walkthrough_ast(
            builder,
            &mut env,
            self.runwai_ast.clone(),
            &load_var,
            "trace",
            "i",
            "n",
            BoundaryInfo::All,
            &mut conditiosn,
        );
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
