use std::fs::File;
use std::io::Write;
use serde::{Serialize, Deserialize};

// Your specific imports
use p3_koala_bear::KoalaBear;
use p3_field::{AbstractField, Field};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_matrix::Matrix;
use p3_uni_stark::{get_symbolic_constraints, SymbolicExpression, SymbolicVariable, Entry};

use tracing::{info, trace, Level};

pub struct FibonacciAir;

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize { 2 } // 2 columns: a, b
}

impl<AB: AirBuilder> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let next = main.row_slice(1);

        builder.when_first_row().assert_eq(local[0], AB::Expr::zero()); // a_0 = 0
        builder.when_first_row().assert_eq(local[1], AB::Expr::one());  // b_0 = 1

        let a = local[0];
        let b = local[1];
        let a_next = next[0];
        let b_next = next[1];

        builder.assert_eq(a_next, b);
        builder.assert_eq(b_next, a + b);
    }
}

fn print_ast<F: Field>(expr: &SymbolicExpression<F>, depth: usize) {
    let indent = "  ".repeat(depth);
    
    match expr {
        SymbolicExpression::IsFirstRow => println!("{}├── IsFirstRow", indent),
        SymbolicExpression::IsLastRow => println!("{}├── IsLastRow", indent),
        SymbolicExpression::IsTransition => println!("{}├── IsTransition", indent),
        SymbolicExpression::Constant(c) => println!("{}├── Constant({:?})", indent, c),
        SymbolicExpression::Variable(v) => {
            let var_description = match v.entry {
                // Trace columns have offsets (Current vs Next)
                Entry::Main { offset } => {
                    let row = if offset == 0 { "Current" } else { "Next" };
                    format!("Main({}, Col {})", row, v.index)
                },
                Entry::Preprocessed { offset } => {
                    let row = if offset == 0 { "Current" } else { "Next" };
                    format!("Preprocessed({}, Col {})", row, v.index)
                },
                Entry::Permutation { offset, .. } => {
                    let row = if offset == 0 { "Current" } else { "Next" };
                    format!("Permutation({}, Col {})", row, v.index)
                },
                
                // Globals do NOT have offsets
                Entry::Public => format!("PublicInput(Idx {})", v.index),
                Entry::Challenge => format!("Challenge(Idx {})", v.index),
            };

            println!("{}├── Var({})", indent, var_description);
        },
        SymbolicExpression::Add { x, y, .. } => {
            println!("{}├── Add", indent);
            print_ast(x, depth + 1);
            print_ast(y, depth + 1);
        },
        SymbolicExpression::Sub { x, y, .. } => {
            println!("{}├── Sub", indent);
            print_ast(x, depth + 1);
            print_ast(y, depth + 1);
        },
        SymbolicExpression::Mul { x, y, .. } => {
            println!("{}├── Mul", indent);
            print_ast(x, depth + 1);
            print_ast(y, depth + 1);
        },
        SymbolicExpression::Neg { x, .. } => {
            println!("{}├── Neg", indent);
            print_ast(x, depth + 1);
        },
    }
}

fn main() {
    // tracing_subscriber::fmt()
    //     .with_max_level(Level::TRACE)
    //     .init();
    
    let air = FibonacciAir;
    type Val = KoalaBear;

    let symbolic_constraints: Vec<SymbolicExpression<Val>> = get_symbolic_constraints(&air, 0, 0);
    
    // for sc in &symbolic_constraints {
    //     trace!("{:?}", sc);
    // }

    for (i, sc) in symbolic_constraints.iter().enumerate() {
        println!("Constraint {} AST:", i);
        print_ast(sc, 0);
        println!();
    }
}
