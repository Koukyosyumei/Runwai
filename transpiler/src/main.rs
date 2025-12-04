use std::fs::File;
use std::io::Write;
use std::marker::PhantomData;
use serde::{Serialize, Serializer};

use p3_koala_bear::KoalaBear;
use p3_field::{AbstractField, Field, PrimeField32};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_matrix::Matrix;
use p3_uni_stark::{get_symbolic_constraints, SymbolicExpression, Entry};

#[derive(Serialize, Clone)]
#[serde(tag = "kind")]
enum JsonNode {
    #[serde(rename = "ConstF")]
    ConstF { val: u32 },
    
    #[serde(rename = "ConstN")]
    ConstN { val: u64 },
    
    #[serde(rename = "Var")]
    Var { name: String },
    
    #[serde(rename = "ArrIdx")]
    ArrIdx { arr: Box<JsonNode>, idx: Box<JsonNode> },
    
    #[serde(rename = "FieldExpr")]
    FieldExpr { 
        op: String, 
        lhs: Box<JsonNode>, 
        rhs: Box<JsonNode> 
    },

    #[serde(rename = "UintExpr")]
    UintExpr {
        op: String,
        lhs: Box<JsonNode>,
        rhs: Box<JsonNode>
    },
    
    #[serde(rename = "AssertE")]
    AssertE { lhs: Box<JsonNode>, rhs: Box<JsonNode> },
    
    #[serde(rename = "Branch")]
    Branch { 
        cond: Box<JsonNode>, 
        th: Box<JsonNode>, 
        els: Box<JsonNode> 
    },
    
    #[serde(rename = "BinRel")]
    BinRel { 
        op: String, 
        lhs: Box<JsonNode>, 
        rhs: Box<JsonNode> 
    },
    
    #[serde(rename = "LetIn")]
    LetIn { 
        name: String, 
        val: Box<JsonNode>, 
        body: Box<JsonNode> 
    },
}

impl JsonNode {
    fn true_assertion() -> Self {
        JsonNode::AssertE {
            lhs: Box::new(JsonNode::ConstF { val: 1 }),
            rhs: Box::new(JsonNode::ConstF { val: 1 }),
        }
    }
}

struct AstConverter;

impl AstConverter {
    fn convert<F: PrimeField32>(expr: &SymbolicExpression<F>) -> JsonNode {
        match expr {
            SymbolicExpression::Mul { x, y, .. } => {
                // Check if LHS is a selector
                if let Some(selector_node) = Self::try_as_selector(x) {
                    return JsonNode::Branch {
                        cond: Box::new(selector_node),
                        th: Box::new(Self::convert_constraint_body(y)), // Unwrap the body
                        els: Box::new(JsonNode::true_assertion()),
                    };
                }
                // Check if RHS is a selector
                if let Some(selector_node) = Self::try_as_selector(y) {
                    return JsonNode::Branch {
                        cond: Box::new(selector_node),
                        th: Box::new(Self::convert_constraint_body(x)),
                        els: Box::new(JsonNode::true_assertion()),
                    };
                }
                
                // Standard Multiplication
                JsonNode::FieldExpr {
                    op: "mul".to_string(),
                    lhs: Box::new(Self::convert(x)),
                    rhs: Box::new(Self::convert(y)),
                }
            }

            SymbolicExpression::Add { x, y, .. } => JsonNode::FieldExpr {
                op: "add".to_string(),
                lhs: Box::new(Self::convert(x)),
                rhs: Box::new(Self::convert(y)),
            },
            SymbolicExpression::Sub { x, y, .. } => JsonNode::FieldExpr {
                op: "sub".to_string(),
                lhs: Box::new(Self::convert(x)),
                rhs: Box::new(Self::convert(y)),
            },
            SymbolicExpression::Neg { x, .. } => JsonNode::FieldExpr {
                op: "sub".to_string(), // 0 - x
                lhs: Box::new(JsonNode::ConstF { val: 0 }),
                rhs: Box::new(Self::convert(x)),
            },
            
            SymbolicExpression::Constant(c) => JsonNode::ConstF { val: c.as_canonical_u32() },
            
            SymbolicExpression::Variable(v) => {
                // trace[i][col] or trace[i+1][col]
                let (arr_name, offset) = match v.entry {
                    Entry::Main { offset } => ("trace", offset),
                    Entry::Preprocessed { offset } => ("fixed", offset),
                    Entry::Permutation { offset, .. } => ("perm", offset),
                    Entry::Public => return JsonNode::Var { name: format!("pub[{}]", v.index) },
                    Entry::Challenge => return JsonNode::Var { name: format!("chal[{}]", v.index) },
                };

                // Build Index Node: "i" or "i + offset"
                let idx_node = if offset == 0 {
                    JsonNode::Var { name: "i".to_string() }
                } else {
                    JsonNode::UintExpr {
                        op: "add".to_string(),
                        lhs: Box::new(JsonNode::Var { name: "i".to_string() }),
                        rhs: Box::new(JsonNode::ConstN { val: offset as u64 }),
                    }
                };

                // Build: trace[idx][col]
                // Inner ArrIdx: trace[idx]
                let inner_access = JsonNode::ArrIdx {
                    arr: Box::new(JsonNode::Var { name: arr_name.to_string() }),
                    idx: Box::new(idx_node),
                };

                // Outer ArrIdx: (trace[idx])[col]
                JsonNode::ArrIdx {
                    arr: Box::new(inner_access),
                    idx: Box::new(JsonNode::ConstN { val: v.index as u64 }),
                }
            },

            // Fallbacks for bare selectors (should usually be caught by Mul)
            SymbolicExpression::IsFirstRow => Self::selector_first_row(),
            SymbolicExpression::IsLastRow => Self::selector_last_row(),
            SymbolicExpression::IsTransition => Self::selector_transition(),
        }
    }

    fn convert_constraint_body<F: PrimeField32>(expr: &SymbolicExpression<F>) -> JsonNode {
        match expr {
            SymbolicExpression::Sub { x, y, .. } => JsonNode::AssertE {
                lhs: Box::new(Self::convert(x)),
                rhs: Box::new(Self::convert(y)),
            },
            _ => JsonNode::AssertE {
                lhs: Box::new(Self::convert(expr)),
                rhs: Box::new(JsonNode::ConstF { val: 0 }),
            },
        }
    }

    fn try_as_selector<F: PrimeField32>(expr: &SymbolicExpression<F>) -> Option<JsonNode> {
        match expr {
            SymbolicExpression::IsFirstRow => Some(Self::selector_first_row()),
            SymbolicExpression::IsLastRow => Some(Self::selector_last_row()),
            SymbolicExpression::IsTransition => Some(Self::selector_transition()),
            _ => None,
        }
    }

    fn selector_first_row() -> JsonNode {
        JsonNode::BinRel {
            op: "eq".to_string(),
            lhs: Box::new(JsonNode::Var { name: "i".to_string() }),
            rhs: Box::new(JsonNode::ConstN { val: 0 }),
        }
    }

    fn selector_last_row() -> JsonNode {
        JsonNode::BinRel {
            op: "eq".to_string(),
            lhs: Box::new(JsonNode::Var { name: "i".to_string() }),
            rhs: Box::new(JsonNode::UintExpr {
                op: "sub".to_string(),
                lhs: Box::new(JsonNode::Var { name: "n".to_string() }),
                rhs: Box::new(JsonNode::ConstN { val: 1 }),
            }),
        }
    }

    fn selector_transition() -> JsonNode {
        JsonNode::BinRel {
            op: "lt".to_string(),
            lhs: Box::new(JsonNode::Var { name: "i".to_string() }),
            rhs: Box::new(JsonNode::UintExpr {
                op: "sub".to_string(),
                lhs: Box::new(JsonNode::Var { name: "n".to_string() }),
                rhs: Box::new(JsonNode::ConstN { val: 1 }),
            }),
        }
    }
}

pub struct FibonacciAir;

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize { 2 }
}

impl<AB: AirBuilder> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let next = main.row_slice(1);

        builder.when_first_row().assert_eq(local[0], AB::Expr::zero());
        builder.when_first_row().assert_eq(local[1], AB::Expr::one());

        let a = local[0];
        let b = local[1];
        let a_next = next[0];
        let b_next = next[1];

        builder.when_transition().assert_eq(a_next, b);
        builder.when_transition().assert_eq(b_next, a + b);
    }
}

fn main() -> std::io::Result<()> {
    let air = FibonacciAir;
    type Val = KoalaBear;

    let symbolic_constraints: Vec<SymbolicExpression<Val>> = get_symbolic_constraints(&air, 0, 0);

    let mut json_nodes: Vec<JsonNode> = symbolic_constraints
        .iter()
        .map(|expr| AstConverter::convert(expr))
        .collect();

    if json_nodes.is_empty() {
        println!("{{}}");
        return Ok(());
    }

    let last_idx = json_nodes.len() - 1;
    let last_name = format!("u{}", last_idx);
    
    let mut current_body = JsonNode::Var { name: last_name.clone() };

    for (i, node) in json_nodes.into_iter().enumerate().rev() {
        let name = format!("u{}",_to_subscript(i));
        current_body = JsonNode::LetIn {
            name,
            val: Box::new(node),
            body: Box::new(current_body),
        };
    }

    let file = File::create("constraints.json")?;
    serde_json::to_writer_pretty(file, &current_body)?;
    
    Ok(())
}

fn _to_subscript(n: usize) -> String {
    let s = n.to_string();
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '0' => out.push('₀'),
            '1' => out.push('₁'),
            '2' => out.push('₂'),
            '3' => out.push('₃'),
            '4' => out.push('₄'),
            '5' => out.push('₅'),
            '6' => out.push('₆'),
            '7' => out.push('₇'),
            '8' => out.push('₈'),
            '9' => out.push('₉'),
            _ => out.push(c),
        }
    }
    out
}
