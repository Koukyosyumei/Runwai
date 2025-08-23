import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

import Lean
import Lean.Meta
import Lean.Elab.Command

import Std.Data.HashMap.Basic

import Runwai.Field

/-!
  # Abstract Syntax Tree for Runwai Expressions

  This module defines the Abstract Syntax Tree (AST) for Runwai, including expression
  syntax (`Expr`), runtime values (`Value`), and type representations (`Type`).
  It also provides utilities for pretty-printing and equality checking.
-/

open Std (Format)

namespace Ast

/-- Boolean binary operators. -/
inductive BooleanOp where
  | and   -- ∧
  | or    -- ∨
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Integer binary operators. -/
inductive IntegerOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Field `F p` binary operators. -/
inductive FieldOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  | div   -- /
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Relational operators. -/
inductive RelOp where
  | eq   -- =
  | lt   -- <
  | le   -- ≤
  deriving DecidableEq, Repr, Lean.ToExpr

mutual
  /-- Core expressions syntax for Runwai. -/
  inductive Expr where
    | constF      : (x : F) → Expr                                       -- field constant
    | constZ      : (x : ℕ) → Expr                                       -- integer constant
    | constBool   : (b: Bool) → Expr                                     -- boolean constant
    | arr         : (elems: List Expr) → Expr                            -- [e₁, ..., eₙ]
    | var         : (name: String) → Expr                                -- variable x
    | assertE     : (lhs: Expr) → (rhs: Expr) → Expr                     -- assert e₁ = e₂
    | boolExpr    : (lhs: Expr) → (op: BooleanOp) → (rhs: Expr) → Expr
    | fieldExpr   : (lhs: Expr) → (op: FieldOp) → (rhs: Expr) → Expr
    | binRel      : (lhs: Expr) → (op: RelOp) → (rhs: Expr) → Expr       -- e₁ ⊘ e₂
    | arrIdx      : (arr: Expr) → (idx: Expr) → Expr                     -- e₁[e₂]
    | branch      : (cond: Expr) → (th: Expr) → (els: Expr) → Expr       -- if cond then e₁ else e₂
    | lam         : (param: String) → (τ: Ty) → (body: Expr) → Expr      -- λx : τ. e
    | app         : (f: Expr) → (arg: Expr) → Expr                       -- e₁ e₂
    | letIn       : (name: String) → (val: Expr) → (body: Expr) → Expr   -- let x = e₁ in e₂
    | lookup      : (name: String) → (arg: Expr) → Expr                  -- #C e₁ ... eₙ
    deriving Lean.ToExpr

  inductive Predicate where
    | lam : (ident: String) → (body: Expr) → Predicate
  deriving Lean.ToExpr

  /-- Runtime values in Runwai. -/
  inductive Value where
    | vF       : (x: F) → Value
    | vZ       : (x: ℕ) -> Value
    | vStar    : Value
    | vBool    : (b: Bool) → Value
    | vArr     : (elems: List Value) → Value
    | vClosure : (param: String) → (body: Expr) → (σ: List (String × Value)) → Value
    deriving Lean.ToExpr

  /-- Basic Types in Runwai. -/
  inductive Ty where
    | unknown  : Ty
    | unit     : Ty
    | field    : Ty                                               -- F p
    | int      : Ty
    | bool     : Ty                                               -- Bool
    | arr      : (ty: Ty) → Int → Ty                              -- [T; n]
    | refin    : (ty: Ty) → (pred: Predicate) → Ty                -- {ν : T | ϕ}
    | func     : (param: String) → (dom: Ty) → (cond: Ty) → Ty    -- x: τ₁ → τ₂
    deriving Lean.ToExpr
end

/-- Test for equality of two `Value`s. -/
partial def valueEq : Value → Value → Bool
  | Value.vF x, Value.vF y                     => x = y
  | Value.vZ x, Value.vZ y                     => x = y
  | Value.vBool b₁, Value.vBool b₂             => b₁ = b₂
  | Value.vArr xs, Value.vArr ys   =>
      if xs.length ≠ ys.length then false
      else
        List.all (List.zip xs ys) (fun (x, y) => valueEq x y)
  | _, _                                       => false

instance : BEq Value where
  beq := valueEq

/-- Convenience: `exprEq e₁ e₂` builds `e₁ = e₂` as an `Expr`. -/
def exprEq (e₁ e₂: Expr): Expr :=
  Expr.binRel e₁ RelOp.eq e₂

def constTruePred : Predicate :=
  Predicate.lam "v" (Ast.Expr.constBool true)

def v: Expr := Expr.var ".v"

structure Circuit where
  name   : String
  width  : ℤ
  goal   : Ast.Ty
  body   : Ast.Expr
deriving Lean.ToExpr

instance : Repr BooleanOp where
  reprPrec
    | BooleanOp.and, _ => Format.text "∧"
    | BooleanOp.or, _  => Format.text "∨"

instance : Repr IntegerOp where
  reprPrec
    | IntegerOp.add, _ => Format.text "+"
    | IntegerOp.sub, _ => Format.text "-"
    | IntegerOp.mul, _ => Format.text "*"

instance : Repr FieldOp where
  reprPrec
    | FieldOp.add, _ => Format.text "+"
    | FieldOp.sub, _ => Format.text "-"
    | FieldOp.mul, _ => Format.text "*"
    | FieldOp.div, _ => Format.text "/"

instance : Repr RelOp where
  reprPrec
    | RelOp.eq, _ => Format.text "="
    | RelOp.lt, _ => Format.text "<"
    | RelOp.le, _ => Format.text "≤"

mutual
  partial def exprToString : Expr → String
    | Expr.constF x          => s!"F {x.val}"
    | Expr.constZ x          => toString x
    | Expr.constBool b       => toString b
    | Expr.var name          => name
    | Expr.assertE l r       => s!"assert {exprToString l} = {exprToString r}"
    | Expr.boolExpr l op r   => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.fieldExpr l op r  => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.binRel l op r     => s!"({exprToString l} {repr op} {exprToString r})"
    | Expr.arr elems         => "[" ++ String.intercalate ", " (elems.map exprToString) ++ "]"
    | Expr.arrIdx a i        => s!"{exprToString a}[{exprToString i}]"
    | Expr.branch c e₁ e₂    => s!"if {exprToString c} then {exprToString e₁} else {exprToString e₂}"
    | Expr.lam param τ body  => s!"λ{param} : {tyToString τ}. {exprToString body}"
    | Expr.app f arg         => s!"{exprToString f} {exprToString arg}"
    | Expr.letIn n v b       => s!"let {n} = {exprToString v} in {exprToString b}"
    | Expr.lookup name arg  => s!"#{name} {exprToString arg}"


  partial def predicateToString : Predicate → String
    | Predicate.lam ident body => s!"{ident} = {exprToString body}"

  partial def tyToString : Ty → String
    | Ty.unknown        => "unknown"
    | Ty.unit           => "unit"
    | Ty.field          => "F"
    | Ty.int            => "int"
    | Ty.bool           => "Bool"
    | Ty.arr t n        => s!"[{tyToString t}; {n}]"
    | Ty.refin t p      => s!"{tyToString t} | {predicateToString p}"
    | Ty.func x d c     => s!"({x} : {tyToString d}) → {tyToString c}"
end

instance : Repr Expr where
  reprPrec e _ := Format.text (exprToString e)

/-
instance : Repr Predicate where
  reprPrec e _ := Format.text (predicateToString e)
-/

instance : Repr Ty where
  reprPrec e _ := Format.text (tyToString e)

/-- Pretty-print a `Value`. -/
def valueToString : Value → String
  | Value.vF x        => s!"F {x.val}"
  | Value.vZ x        => s!"{x}"
  | Value.vStar       => "*"
  | Value.vBool b     => toString b
  | Value.vArr vs     =>
    let elems := vs.map valueToString
    s!"[{String.intercalate ", " elems}]"
  | Value.vClosure n _ _ => s!"<closure {n}>"

instance : Repr Value where
  reprPrec v _ := Format.text (valueToString v)

instance : Repr Circuit where
  reprPrec c _ :=
    Format.text s!
"Circuit \{
  name   := \"{c.name}\",
  width  := {c.width},
  goal   := {repr c.goal},
  body   := {repr c.body}
}"

def DefaultCircuit : Circuit := {
    name   := "dummy"
    width  := 0
    goal   := Ty.refin Ty.unit constTruePred
    body   := Expr.assertE (Expr.constF 1) (Expr.constF 1)
  }

instance : Inhabited Circuit where
  default := DefaultCircuit

end Ast
