use std::fs;
use std::path::Path;

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
