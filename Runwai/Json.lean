import Lean
import Lean.Data.Json.Basic
import Runwai.Ast

open Lean Json

/-- Convert BoolOp to JSON -/
def boolOpToJson : Ast.BoolOp → Json
  | .and => Json.str "and"
  | .or  => Json.str "or"

/-- Convert IntOp to JSON -/
def intOpToJson : Ast.IntOp → Json
  | .add => Json.str "add"
  | .sub => Json.str "sub"
  | .mul => Json.str "mul"

/-- Convert FieldOp to JSON -/
def fieldOpToJson : Ast.FieldOp → Json
  | .add => Json.str "add"
  | .sub => Json.str "sub"
  | .mul => Json.str "mul"
  | .div => Json.str "div"

/-- Convert RelOp to JSON -/
def relOpToJson : Ast.RelOp → Json
  | .eq => Json.str "eq"
  | .lt => Json.str "lt"
  | .le => Json.str "le"

mutual

  /-- Convert Expr to JSON -/
  partial def exprToJson : Ast.Expr → Json
    | .constF x      => mkObj [("kind", Json.str "constF"), ("val", Json.num (JsonNumber.fromNat x.val))] -- F needs `ToString` or customize
    | .constN x      => mkObj [("kind", Json.str "constN"), ("val", Json.num (JsonNumber.fromNat x))]
    | .constInt x    => mkObj [("kind", Json.str "constInt"), ("val", Json.num (JsonNumber.fromInt x))]
    | .constBool b   => mkObj [("kind", Json.str "constBool"), ("val", Json.bool b)]
    | .arr elems     => mkObj [("kind", Json.str "arr"), ("elems", Json.arr (elems.map exprToJson).toArray)]
    | .var name      => mkObj [("kind", Json.str "var"), ("name", Json.str name)]
    | .assertE lhs rhs => mkObj [("kind", Json.str "assertE"), ("lhs", exprToJson lhs), ("rhs", exprToJson rhs)]
    | .boolExpr lhs op rhs => mkObj [("kind", Json.str "boolExpr"), ("lhs", exprToJson lhs), ("op", boolOpToJson op), ("rhs", exprToJson rhs)]
    | .fieldExpr lhs op rhs => mkObj [("kind", Json.str "fieldExpr"), ("lhs", exprToJson lhs), ("op", fieldOpToJson op), ("rhs", exprToJson rhs)]
    | .uintExpr lhs op rhs => mkObj [("kind", Json.str "uintExpr"), ("lhs", exprToJson lhs), ("op", intOpToJson op), ("rhs", exprToJson rhs)]
    | .sintExpr lhs op rhs => mkObj [("kind", Json.str "sintExpr"), ("lhs", exprToJson lhs), ("op", intOpToJson op), ("rhs", exprToJson rhs)]
    | .binRel lhs op rhs => mkObj [("kind", Json.str "binRel"), ("lhs", exprToJson lhs), ("op", relOpToJson op), ("rhs", exprToJson rhs)]
    | .arrIdx xs idx => mkObj [("kind", Json.str "arrIdx"), ("arr", exprToJson xs), ("idx", exprToJson idx)]
    | .len xs       => mkObj [("kind", Json.str "len"), ("arr", exprToJson xs)]
    | .branch cond th els => mkObj [("kind", Json.str "branch"), ("cond", exprToJson cond), ("th", exprToJson th), ("els", exprToJson els)]
    | .lam param τ body => mkObj [("kind", Json.str "lam"), ("param", Json.str param), ("ty", tyToJson τ), ("body", exprToJson body)]
    | .app f arg     => mkObj [("kind", Json.str "app"), ("f", exprToJson f), ("arg", exprToJson arg)]
    | .letIn name val body => mkObj [("kind", Json.str "letIn"), ("name", Json.str name), ("val", exprToJson val), ("body", exprToJson body)]
    | .lookup vname cname args body =>
        mkObj [("kind", Json.str "lookup"),
               ("vname", Json.str vname), ("cname", Json.str cname),
               ("args", Json.arr (args.map (fun (a,b) => mkObj [("fst", exprToJson a), ("snd", exprToJson b)])).toArray),
               ("body", exprToJson body)]
    | .toN body      => mkObj [("kind", Json.str "toN"), ("body", exprToJson body)]
    | .toF body      => mkObj [("kind", Json.str "toF"), ("body", exprToJson body)]
    | .UtoS body     => mkObj [("kind", Json.str "UtoS"), ("body", exprToJson body)]
    | .StoU body     => mkObj [("kind", Json.str "StoU"), ("body", exprToJson body)]

  /-- Convert Predicate to JSON -/
  partial def predicateToJson : Ast.Predicate → Json
    | .dep ident body => mkObj [("kind", Json.str "dep"), ("ident", Json.str ident), ("body", exprToJson body)]
    | .ind body       => mkObj [("kind", Json.str "ind"), ("body", exprToJson body)]
    | .and l r        => mkObj [("kind", Json.str "and"), ("left", predicateToJson l), ("right", predicateToJson r)]
    | .or l r         => mkObj [("kind", Json.str "or"), ("left", predicateToJson l), ("right", predicateToJson r)]
    | .not φ          => mkObj [("kind", Json.str "not"), ("φ", predicateToJson φ)]

  /-- Convert Value to JSON -/
  partial def valueToJson : Ast.Value → Json
    | .vF x       => mkObj [("kind", Json.str "vF"), ("val", Json.num (JsonNumber.fromNat x.val))]
    | .vN x       => mkObj [("kind", Json.str "vN"), ("val", Json.num (JsonNumber.fromNat x))]
    | .vInt x     => mkObj [("kind", Json.str "vInt"), ("val", Json.num (JsonNumber.fromInt x))]
    | .vUnit      => mkObj [("kind", Json.str "vUnit")]
    | .vBool b    => mkObj [("kind", Json.str "vBool"), ("val", Json.bool b)]
    | .vArr elems => mkObj [("kind", Json.str "vArr"), ("elems", Json.arr (elems.map valueToJson).toArray)]
    | .vClosure param body σ =>
        mkObj [("kind", Json.str "vClosure"), ("param", Json.str param), ("body", exprToJson body),
               ("env", Json.arr (σ.map (fun (k,v) => mkObj [("name", Json.str k), ("val", valueToJson v)])).toArray)]

  /-- Convert Ty to JSON -/
  partial def tyToJson : Ast.Ty → Json
    | .unit        => Json.str "unit"
    | .field       => Json.str "field"
    | .uint        => Json.str "uint"
    | .sint        => Json.str "sint"
    | .bool        => Json.str "bool"
    | .arr ty n    => mkObj [("kind", Json.str "arr"), ("ty", tyToJson ty), ("len", Json.num (JsonNumber.fromNat n))]
    | .refin ty φ  => mkObj [("kind", Json.str "refin"), ("ty", tyToJson ty), ("pred", predicateToJson φ)]
    | .func param dom cond => mkObj [("kind", Json.str "func"), ("param", Json.str param), ("dom", tyToJson dom), ("cond", tyToJson cond)]

end

/-- Convenience function: convert Expr to JSON string -/
def exprToJsonStr (e : Ast.Expr) : String :=
  (exprToJson e).pretty

def tyToJsonStr (τ : Ast.Ty) : String :=
  (tyToJson τ).pretty
