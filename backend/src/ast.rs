use core::panic;
use std::path::Path;
use std::{collections::HashMap, fs};

use p3_air::{AirBuilder, FilteredAirBuilder};
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

    pub fn is_dummy_assert(&self) -> bool {
        if let Expr::AssertE { lhs, rhs } = &self {
            if let Expr::ConstBool { val } = &**lhs {
                if *val {
                    if let Expr::ConstBool { val } = &**rhs {
                        if *val {
                            return true;
                        }
                    }
                }
            }
        }

        false
    }

    pub fn get_trace_i_j<AB: AirBuilder>(
        &self,
        colid_to_var_fn: &dyn Fn(bool, usize) -> AB::Var,
        trace_name: &str,
        row_index_name: &str,
    ) -> Option<AB::Expr> {
        // find `trace[i][j]`
        if let Expr::ArrIdx { arr, idx } = &self {
            if let Expr::ConstN { val } = &**idx {
                let colid = val.clone();
                if let Expr::ArrIdx { arr, idx } = &**arr {
                    if let Expr::Var { name } = &**arr {
                        if name == trace_name {
                            if let Expr::Var { name } = &**idx {
                                if name == row_index_name {
                                    return Some(colid_to_var_fn(true, colid as usize).into());
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    pub fn get_trace_ip1_j<AB: AirBuilder>(
        &self,
        colid_to_var_fn: &dyn Fn(bool, usize) -> AB::Var,
        trace_name: &str,
        row_index_name: &str,
    ) -> Option<AB::Expr> {
        // find `trace[i+1][j]`
        if let Expr::ArrIdx { arr, idx } = &self {
            if let Expr::ConstN { val } = &**idx {
                let colid = val.clone();
                if let Expr::ArrIdx { arr, idx } = &**arr {
                    if let Expr::Var { name } = &**arr {
                        if name == trace_name {
                            if let Expr::UintExpr {
                                lhs,
                                op: IntOp::Add,
                                rhs,
                            } = &**idx
                            {
                                if let Expr::Var { name } = &**lhs {
                                    if name == row_index_name {
                                        if let Expr::ConstN { val } = &**rhs {
                                            if *val == 1 {
                                                return Some(
                                                    colid_to_var_fn(false, colid as usize).into(),
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    pub fn to_ab_expr<AB: AirBuilder>(
        &self,
        colid_to_var_fn: &dyn Fn(bool, usize) -> AB::Var,
        env: &HashMap<String, Expr>,
        trace_name: &str,
        row_index_name: &str,
    ) -> AB::Expr
    where
        AB::F: Field + PrimeCharacteristicRing,
    {
        match &self {
            Expr::ConstF { val } => AB::F::from_u64(*val).into(),
            Expr::ConstN { val: _val } => panic!("something went wrong"),
            Expr::ConstInt { val: _val } => panic!("something went wrong"),
            Expr::ConstBool { val: _val } => panic!("something went wrong"),
            Expr::Arr { elems: _elems } => todo!(),
            Expr::Var { name } => env.get(name).unwrap().to_ab_expr::<AB>(
                colid_to_var_fn,
                env,
                trace_name,
                row_index_name,
            ),
            Expr::AssertE {
                lhs: _lhs,
                rhs: _rhs,
            } => panic!("something went wrong"),
            Expr::BoolExpr {
                lhs: _lhs,
                op: _op,
                rhs: _rhs,
            } => panic!("something went wrong"),
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
            Expr::UintExpr {
                lhs: _lhs,
                op: _op,
                rhs: _rhs,
            } => panic!("something went wrong"),
            Expr::SintExpr {
                lhs: _lhs,
                op: _op,
                rhs: _rhs,
            } => panic!("something went wrong"),
            Expr::BinRel {
                lhs: _lhs,
                op: _op,
                rhs: _rhs,
            } => panic!("something went wrong"),
            Expr::ArrIdx {
                arr: _arr,
                idx: _idx,
            } => {
                if let Some(ab_expr) =
                    self.get_trace_i_j::<AB>(colid_to_var_fn, trace_name, row_index_name)
                {
                    return ab_expr;
                }
                if let Some(ab_expr) =
                    self.get_trace_ip1_j::<AB>(colid_to_var_fn, trace_name, row_index_name)
                {
                    return ab_expr;
                }
                panic!("{:?} cannot be simplified to a cell representation (either trace[i][j] or trace[i+1][j])", &self)
            }
            Expr::Len { arr: _arr } => panic!("cannot use Len within the `assert`"),
            Expr::Branch {
                cond: _cond,
                th: _th,
                els: _els,
            } => todo!("currently cannot use Branch statement inside the `assert`"),
            Expr::Lam {
                param: _param,
                ty: _ty,
                body: _body,
            } => todo!(),
            Expr::App { f: _f, arg: _arg } => todo!(),
            Expr::LetIn {
                name: _name,
                val: _val,
                body: _body,
            } => panic!("cannot use LetIn within the `assert`"),
            Expr::Lookup {
                vname: _vname,
                cname: _cname,
                args: _args,
                body: _body,
            } => panic!("cannot use Lookup within the `assert`"),
            Expr::ToN { body: _body } => panic!("cannot use toN within the `assert`"),
            Expr::ToF { body: _body } => panic!("cannot use toF within the `assert`"),
            Expr::UtoS { body: _body } => panic!("cannot use UtoS within the `assert`"),
            Expr::StoU { body: _body } => panic!("cannot use StoU within the `assert`"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum BoundaryInfo {
    IsFirst,
    IsLast,
    IsTransition,
    All,
}

#[derive(Debug, Clone)]
pub enum CondInfo {
    When(Box<Expr>),
    WhenNe(Box<Expr>, Box<Expr>),
}

pub fn is_first_cond<AB: AirBuilder>(cond: &Expr, row_index_name: &str) -> bool {
    if let Expr::BinRel {
        lhs,
        op: RelOp::Eq,
        rhs,
    } = cond
    {
        if let Expr::Var { name } = &**lhs {
            if name == row_index_name {
                if let Expr::ConstN { val } = &**rhs {
                    if *val == 0 {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

pub fn is_transition_cond<AB: AirBuilder>(
    cond: &Expr,
    row_index_name: &str,
    height_name: &str,
) -> bool {
    if let Expr::BinRel {
        lhs,
        op: RelOp::Lt,
        rhs,
    } = cond
    {
        if let Expr::Var { name } = &**lhs {
            if name == row_index_name {
                if let Expr::UintExpr {
                    lhs,
                    op: IntOp::Sub,
                    rhs,
                } = &**rhs
                {
                    if let Expr::Var { name } = &**lhs {
                        if let Expr::ConstN { val } = &**rhs {
                            if name == height_name && *val == 1 {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    return false;
}

pub fn walkthrough_ast<AB: AirBuilder>(
    builder: &mut AB,
    env: &mut HashMap<String, Expr>,
    expr: Expr,
    colid_to_var_fn: &dyn Fn(bool, usize) -> AB::Var,
    trace_name: &str,
    row_index_name: &str,
    height_name: &str,
    when: BoundaryInfo,
    mut conditions: &mut Vec<CondInfo>,
) where
    AB::F: Field + PrimeCharacteristicRing,
{
    match expr {
        Expr::AssertE { lhs, rhs } => {
            let lhs_ab: AB::Expr =
                lhs.to_ab_expr::<AB>(colid_to_var_fn, env, trace_name, row_index_name);
            let rhs_ab: AB::Expr =
                rhs.to_ab_expr::<AB>(colid_to_var_fn, env, trace_name, row_index_name);

            match when {
                BoundaryInfo::IsFirst => builder.when_first_row().assert_eq(lhs_ab, rhs_ab),
                BoundaryInfo::IsLast => builder.when_last_row().assert_eq(lhs_ab, rhs_ab),
                BoundaryInfo::IsTransition => builder.when_transition().assert_eq(lhs_ab, rhs_ab),
                BoundaryInfo::All => {
                    if conditions.is_empty() {
                        builder.assert_eq(lhs_ab, rhs_ab)
                    } else {
                        // TODO: support nested filter constraints.
                        match &conditions[0] {
                            CondInfo::When(cond) => {
                                let cond_ab = cond.to_ab_expr::<AB>(
                                    colid_to_var_fn,
                                    env,
                                    trace_name,
                                    row_index_name,
                                );
                                builder.when(cond_ab).assert_eq(lhs_ab, rhs_ab)
                            }
                            CondInfo::WhenNe(cond_lhs, cond_rhs) => {
                                let cond_lhs_ab = cond_lhs.to_ab_expr::<AB>(
                                    colid_to_var_fn,
                                    env,
                                    trace_name,
                                    row_index_name,
                                );
                                let cond_rhs_ab = cond_rhs.to_ab_expr::<AB>(
                                    colid_to_var_fn,
                                    env,
                                    trace_name,
                                    row_index_name,
                                );
                                builder
                                    .when_ne(cond_lhs_ab, cond_rhs_ab)
                                    .assert_eq(lhs_ab, rhs_ab)
                            }
                        }
                    }
                }
            }
        }
        Expr::Branch { cond, th, els } => {
            if is_first_cond::<AB>(&cond, &row_index_name) {
                walkthrough_ast(
                    builder,
                    env,
                    *th,
                    colid_to_var_fn,
                    trace_name,
                    row_index_name,
                    height_name,
                    BoundaryInfo::IsFirst,
                    &mut conditions,
                );
            } else if is_transition_cond::<AB>(&cond, row_index_name, height_name) {
                walkthrough_ast(
                    builder,
                    env,
                    *th,
                    colid_to_var_fn,
                    trace_name,
                    row_index_name,
                    height_name,
                    BoundaryInfo::IsTransition,
                    &mut conditions,
                );
            } else {
                if let Expr::BinRel {
                    lhs,
                    op: RelOp::Eq,
                    rhs,
                } = &*cond
                {
                    if th.is_dummy_assert() {
                        panic!("then-statement should be dummy assert: (assert(true, true))");
                    }
                    if let Expr::ConstF { val } = &**rhs {
                        if *val == 0 {
                            conditions.push(CondInfo::When(lhs.clone()));
                            walkthrough_ast(
                                builder,
                                env,
                                *els,
                                colid_to_var_fn,
                                trace_name,
                                row_index_name,
                                height_name,
                                when,
                                conditions,
                            );
                            return;
                        }
                    }
                    if let Expr::ConstF { val } = &**lhs {
                        if *val == 0 {
                            conditions.push(CondInfo::When(rhs.clone()));
                            walkthrough_ast(
                                builder,
                                env,
                                *els,
                                colid_to_var_fn,
                                trace_name,
                                row_index_name,
                                height_name,
                                when,
                                conditions,
                            );
                            return;
                        }
                    }
                    conditions.push(CondInfo::WhenNe(lhs.clone(), rhs.clone()));
                    walkthrough_ast(
                        builder,
                        env,
                        *els,
                        colid_to_var_fn,
                        trace_name,
                        row_index_name,
                        height_name,
                        when,
                        conditions,
                    );
                }
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
                height_name,
                when.clone(),
                &mut conditions,
            );
            env.insert(name, *val);
            walkthrough_ast(
                builder,
                env,
                *body,
                colid_to_var_fn,
                trace_name,
                row_index_name,
                height_name,
                when,
                &mut conditions,
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
