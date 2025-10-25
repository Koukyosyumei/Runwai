use core::panic;
use std::path::Path;
use std::{collections::HashMap, fs};

use p3_air::AirBuilder;
use p3_field::{Field, PrimeCharacteristicRing};
use serde::{de::value::Error, Deserialize, Serialize};

/* ======== Operators ======== */
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BoolOp {
    And,
    Or,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum IntOp {
    Add,
    Sub,
    Mul,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FieldOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum RelOp {
    Eq,
    Lt,
    Le,
}

/* ======== Expressions ======== */
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Expr {
    ConstF {
        val: u64,
    },
    ConstN {
        val: u64,
    },
    ConstInt {
        val: i64,
    },
    ConstBool {
        val: bool,
    },
    Arr {
        elems: Vec<Expr>,
    },
    Var {
        name: String,
    },
    AssertE {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    BoolExpr {
        lhs: Box<Expr>,
        op: BoolOp,
        rhs: Box<Expr>,
    },
    FieldExpr {
        lhs: Box<Expr>,
        op: FieldOp,
        rhs: Box<Expr>,
    },
    UintExpr {
        lhs: Box<Expr>,
        op: IntOp,
        rhs: Box<Expr>,
    },
    SintExpr {
        lhs: Box<Expr>,
        op: IntOp,
        rhs: Box<Expr>,
    },
    BinRel {
        lhs: Box<Expr>,
        op: RelOp,
        rhs: Box<Expr>,
    },
    ArrIdx {
        arr: Box<Expr>,
        idx: Box<Expr>,
    },
    Len {
        arr: Box<Expr>,
    },
    Branch {
        cond: Box<Expr>,
        th: Box<Expr>,
        els: Box<Expr>,
    },
    Lam {
        param: String,
        ty: Ty,
        body: Box<Expr>,
    },
    App {
        f: Box<Expr>,
        arg: Box<Expr>,
    },
    LetIn {
        name: String,
        val: Box<Expr>,
        body: Box<Expr>,
    },
    Lookup {
        vname: String,
        cname: String,
        args: Vec<ArgPair>,
        body: Box<Expr>,
    },
    ToN {
        body: Box<Expr>,
    },
    ToF {
        body: Box<Expr>,
    },
    UtoS {
        body: Box<Expr>,
    },
    StoU {
        body: Box<Expr>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArgPair {
    pub fst: Expr,
    pub snd: Expr,
}

/* ======== Predicates ======== */
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Predicate {
    Dep {
        ident: String,
        body: Expr,
    },
    Ind {
        body: Expr,
    },
    And {
        left: Box<Predicate>,
        right: Box<Predicate>,
    },
    Or {
        left: Box<Predicate>,
        right: Box<Predicate>,
    },
    Not {
        φ: Box<Predicate>,
    },
}

/* ======== Types ======== */
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Ty {
    #[serde(rename = "unit")]
    Unit,
    #[serde(rename = "field")]
    Field,
    #[serde(rename = "uint")]
    Uint,
    #[serde(rename = "sint")]
    Sint,
    #[serde(rename = "bool")]
    Bool,
    Arr {
        ty: Box<Ty>,
        len: u64,
    },
    Refin {
        ty: Box<Ty>,
        pred: Box<Predicate>,
    },
    Func {
        param: String,
        dom: Box<Ty>,
        cond: Box<Ty>,
    },
}

/* ======== Values ======== */
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Value {
    VF {
        val: String,
    },
    VN {
        val: u64,
    },
    VInt {
        val: i64,
    },
    VUnit,
    VBool {
        val: bool,
    },
    VArr {
        elems: Vec<Value>,
    },
    VClosure {
        param: String,
        body: Expr,
        env: Vec<EnvBinding>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvBinding {
    pub name: String,
    pub val: Value,
}

/* ======== I/O Helpers ======== */
impl Expr {
    pub fn from_json_file<P: AsRef<Path>>(path: P) -> Result<Expr, std::io::Error> {
        let data = fs::read_to_string(path)?;
        let expr: Expr = serde_json::from_str(&data)?;
        Ok(expr)
    }
}

impl Expr {
    pub fn to_ab_expr<AB: AirBuilder>(
        &self,
        colid_to_var_fn: &dyn Fn(bool, usize) -> AB::Var,
        env: &HashMap<String, Expr>,
        trace_name: &String,
        row_index_name: &String,
    ) -> AB::Expr
    where
        AB::F: Field + PrimeCharacteristicRing,
    {
        match &self {
            Expr::ConstF { val } => AB::F::from_u64(*val).into(),
            Expr::ConstN { val: _val } => panic!("something went wrong"),
            Expr::ConstInt { val: _val } => panic!("something went wrong"),
            Expr::ConstBool { val: _val } => panic!("something went wrong"),
            Expr::Arr { elems } => todo!(),
            Expr::Var { name } => env.get(name).unwrap().to_ab_expr::<AB>(
                colid_to_var_fn,
                env,
                trace_name,
                row_index_name,
            ),
            Expr::AssertE { lhs, rhs } => panic!("something went wrong"),
            Expr::BoolExpr { lhs, op, rhs } => panic!("something went wrong"),
            Expr::FieldExpr { lhs, op, rhs } => {
                let lhs_ab = lhs.to_ab_expr::<AB>(colid_to_var_fn, env, trace_name, row_index_name);
                let rhs_ab = rhs.to_ab_expr::<AB>(colid_to_var_fn, env, trace_name, row_index_name);
                match op {
                    FieldOp::Add => lhs_ab + rhs_ab,
                    FieldOp::Sub => lhs_ab - rhs_ab,
                    FieldOp::Mul => lhs_ab * rhs_ab,
                    FieldOp::Div => panic!("div cannot be used within constraints"),
                }
            }
            Expr::UintExpr { lhs, op, rhs } => panic!("something went wrong"),
            Expr::SintExpr { lhs, op, rhs } => panic!("something went wrong"),
            Expr::BinRel { lhs, op, rhs } => panic!("something went wrong"),
            Expr::ArrIdx { arr, idx } => {
                if let Expr::ConstN { val } = &**idx {
                    if let Expr::ArrIdx { arr, idx } = &**arr {
                        if let Expr::Var { name } = &**arr {
                            if name == trace_name {
                                if let Expr::Var { name } = &**idx {
                                    if name == row_index_name {
                                        colid_to_var_fn(true, (*val) as usize).into()
                                    } else {
                                        panic!("unresolved name: {}", name)
                                    }
                                } else if let Expr::UintExpr {
                                    lhs,
                                    op: IntOp::Add,
                                    rhs,
                                } = &**idx
                                {
                                    if let Expr::Var { name } = &**lhs {
                                        if name == row_index_name {
                                            if let Expr::ConstN { val } = &**rhs {
                                                if *val == 1 {
                                                    colid_to_var_fn(false, (*val) as usize).into()
                                                } else {
                                                    panic!("something went wrong")
                                                }
                                            } else {
                                                panic!("something went wrong")
                                            }
                                        } else {
                                            panic!("unresolved name: {}", name)
                                        }
                                    } else {
                                        panic!("something went wrong")
                                    }
                                } else {
                                    panic!("something went wrong")
                                }
                            } else {
                                panic!("unresolved name: {}", name)
                            }
                        } else {
                            todo!()
                        }
                    } else {
                        todo!()
                    }
                } else {
                    todo!()
                }
            }
            Expr::Len { arr: _arr } => panic!("cannot use Len in the constraints"),
            Expr::Branch { cond, th, els } => todo!(),
            Expr::Lam { param, ty, body } => todo!(),
            Expr::App { f, arg } => todo!(),
            Expr::LetIn { name, val, body } => todo!(),
            Expr::Lookup {
                vname,
                cname,
                args,
                body,
            } => todo!(),
            Expr::ToN { body: _body } => panic!("cannot use toN in the constraints"),
            Expr::ToF { body: _body } => panic!("cannot use toF in the constraints"),
            Expr::UtoS { body: _body } => panic!("cannot use UtoS in the constraints"),
            Expr::StoU { body: _body } => panic!("cannot use StoU in the constraints"),
        }
    }
}

pub fn walkthrough_ast<AB: AirBuilder>(
    builder: &mut AB,
    env: &mut HashMap<String, Expr>,
    expr: Expr,
    colid_to_var_fn: &dyn Fn(bool, usize) -> AB::Var,
    trace_name: &String,
    row_index_name: &String,
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    match expr {
        Expr::AssertE { lhs, rhs } => {
            let lhs_ab: AB::Expr =
                lhs.to_ab_expr::<AB>(colid_to_var_fn, env, trace_name, row_index_name);
            let rhs_ab: AB::Expr =
                rhs.to_ab_expr::<AB>(colid_to_var_fn, env, trace_name, row_index_name);
            builder.assert_eq(lhs_ab, rhs_ab);
        }
        Expr::Branch { cond, th, els } => {
            if let Expr::BinRel {
                lhs,
                op: RelOp::Eq,
                rhs,
            } = &*cond
            {
                if let Expr::Var { name } = &**lhs {
                    if name == row_index_name {
                        if let Expr::ConstN { val } = &**rhs {
                            if *val == 0 {
                                let mut when = builder.when_first_row();
                                walkthrough_ast(
                                    &mut when,
                                    env,
                                    *th,
                                    colid_to_var_fn,
                                    trace_name,
                                    row_index_name,
                                );
                            }
                        }
                    }
                }
            } else {
                let cond_ab: AB::Expr =
                    cond.to_ab_expr::<AB>(colid_to_var_fn, env, trace_name, row_index_name);
                let mut when = builder.when(cond_ab.clone());
                walkthrough_ast(
                    &mut when,
                    env,
                    *th,
                    colid_to_var_fn,
                    trace_name,
                    row_index_name,
                );
                let mut when = builder.when_ne(cond_ab, AB::Expr::ZERO);
                walkthrough_ast(
                    &mut when,
                    env,
                    *els,
                    colid_to_var_fn,
                    trace_name,
                    row_index_name,
                );
            }
        }
        Expr::LetIn { name, val, body } => {
            walkthrough_ast(
                builder,
                env,
                *val.clone(),
                colid_to_var_fn,
                trace_name,
                row_index_name,
            );
            env.insert(name, *val);
            walkthrough_ast(
                builder,
                env,
                *body,
                colid_to_var_fn,
                trace_name,
                row_index_name,
            );
        }
        Expr::Lookup {
            vname,
            cname,
            args,
            body,
        } => todo!(),
        _ => {}
    }
}
