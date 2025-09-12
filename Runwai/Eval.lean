import Mathlib.Data.List.Forall2

import Runwai.Ast
import Runwai.Env

open Ast
open Env

/-!
  # Evaluator for Runwai AST

  This module implements a small-step interpreter for Runwai expressions.
  It provides functions to evaluate binary operations, relations, and
  full `Expr`s under given valuation, Chip, and type environments,
  with a fuel parameter to ensure termination.
-/

namespace Eval

/-- Evaluate a field operation `op` on two `Value.field` arguments. -/
@[simp]
def evalFieldOp (op: FieldOp) : Value → Value → Option Value
  | Value.vF x, Value.vF y =>
    some $ Value.vF $
      match op with
      | FieldOp.add => x + y
      | FieldOp.sub => x - y
      | FieldOp.mul => x * y
      | FieldOp.div => x * y.inv
  | _, _ => none

@[simp]
def evalIntegerOp (op: IntegerOp) : Value → Value → Option Value
  | Value.vZ x, Value.vZ y =>
    some $ Value.vZ $
      match op with
      | IntegerOp.add => x + y
      | IntegerOp.sub => x - y
      | IntegerOp.mul => x * y
  | _, _ => none

/-- Evaluate a relational operator `op` on two `Value` arguments. -/
@[simp]
def evalRelOp (op: RelOp) : Value → Value → Option Bool
  | Value.vF i, Value.vF j =>
    match op with
    | RelOp.eq => some (i = j)
    | _ => none
  | Value.vZ i, Value.vZ j =>
    some $ match op with
    | RelOp.eq => i = j
    | RelOp.lt => i < j
    | RelOp.le => i ≤ j
  | _, _ => none

/-- Evaluate a boolean operator `op` on two `Value.bool` arguments. -/
@[simp]
def evalBoolOp (op : BooleanOp) : Value → Value → Option Bool
  | Value.vBool x, Value.vBool y =>
    some $ match op with
    | BooleanOp.and => x && y
    | BooleanOp.or  => x || y
  | _, _ => none

mutual
  inductive EvalProp : ValEnv → ChipEnv → Expr → Value → Prop
    -- E‑VALUE
    | ConstF        {σ Δ v} : EvalProp σ Δ (Expr.constF v) (Value.vF v)
    | ConstZ        {σ Δ v} : EvalProp σ Δ (Expr.constZ v) (Value.vZ v)
    | ConstBool     {σ Δ b} : EvalProp σ Δ (Expr.constBool b) (Value.vBool b)
    | ConstArr  {σ Δ xs es} (ilength: xs.length = es.length) (ih : ∀ xe ∈ List.zip xs es, EvalProp σ Δ xe.fst xe.snd) :
        EvalProp σ Δ (Expr.arr xs) (Value.vArr es)

    | toZ {σ Δ e v} (h: EvalProp σ Δ e (Ast.Value.vF v)) :
        EvalProp σ Δ (Expr.toZ e) (Ast.Value.vZ v.val)

    -- E‑VAR
    | Var         {σ Δ x v} : lookupVal σ x = v → EvalProp σ Δ (Expr.var x) v

    -- E‑LAM
    | Lam    {σ Δ x τ body} : EvalProp σ Δ (Expr.lam x τ body) (Value.vClosure x body σ)

    -- E‑LET
    | Let      {σ Δ x e₁ e₂ v₁ v₂}
        (ih₁ : EvalProp σ Δ e₁ v₁)
        (ih₂ : EvalProp (updateVal σ x v₁) Δ e₂ v₂) :
        EvalProp σ Δ (Expr.letIn x e₁ e₂) v₂

    -- E‑APP
    | App      {σ Δ f a x body σ' va vb}
        (ih_f : EvalProp σ Δ f (Value.vClosure x body σ'))
        (ih_a : EvalProp σ Δ a va)
        --(ih_b : EvalProp (updateVal σ' x va) Δ body vb) :
        (ih_b : EvalProp σ' Δ body vb) :
        EvalProp σ Δ (Expr.app f a) vb

    -- E‑FBINOP
    | FBinOp   {σ Δ e₁ e₂ op i₁ i₂ v}
        (ih₁ : EvalProp σ Δ e₁ (Value.vF i₁))
        (ih₂ : EvalProp σ Δ e₂ (Value.vF i₂))
        (r   : evalFieldOp op (Value.vF i₁) (Value.vF i₂) = some v) :
        EvalProp σ Δ (Expr.fieldExpr e₁ op e₂) v

    -- E‑ZBINOP
    | ZBinOp   {σ Δ e₁ e₂ op i₁ i₂ v}
        (ih₁ : EvalProp σ Δ e₁ (Value.vZ i₁))
        (ih₂ : EvalProp σ Δ e₂ (Value.vZ i₂))
        (r   : evalIntegerOp op (Value.vZ i₁) (Value.vZ i₂) = some v) :
        EvalProp σ Δ (Expr.integerExpr e₁ op e₂) v

    -- E‑BOOLBINOP
    | BoolOp   {σ Δ e₁ e₂ op b₁ b₂ b}
        (ih₁ : EvalProp σ Δ e₁ (Value.vBool b₁))
        (ih₂ : EvalProp σ Δ e₂ (Value.vBool b₂))
        (bv  : evalBoolOp op (Value.vBool b₁) (Value.vBool b₂) = some b) :
        EvalProp σ Δ (Expr.boolExpr e₁ op e₂) (Value.vBool b)

    -- E‑REL
    | Rel      {σ Δ e₁ e₂ op v₁ v₂ b}
        (ih₁ : EvalProp σ Δ e₁ v₁)
        (ih₂ : EvalProp σ Δ e₂ v₂)
        (r   : evalRelOp op v₁ v₂ = some b) :
        EvalProp σ Δ (Expr.binRel e₁ op e₂) (Value.vBool b)

    -- E-BRANCH
    | IfTrue {σ Δ c e₁ e₂ v₁}
        (ihc : EvalProp σ Δ c (Value.vBool true))
        (ih₁ : EvalProp σ Δ e₁ v₁):
        EvalProp σ Δ (Expr.branch c e₁ e₂) (v₁)

    | IfFalse {σ Δ c e₁ e₂ v₂}
        (ihc : EvalProp σ Δ c (Value.vBool false))
        (ih₁ : EvalProp σ Δ e₂ v₂):
        EvalProp σ Δ (Expr.branch c e₁ e₂) (v₂)

    -- E‑ASSERT
    | Assert   {σ Δ e₁ e₂ v₁ v₂ b}
        (ih₁ : EvalProp σ Δ e₁ v₁)
        (ih₂ : EvalProp σ Δ e₂ v₂)
        (ok  : evalRelOp RelOp.eq v₁ v₂ = some b) :
        EvalProp σ Δ (Expr.assertE e₁ e₂) (Value.vUnit)

    -- E‑ARRIDX
    | ArrIdx {σ Δ a i vs j v}
        (iha : EvalProp σ Δ a (Value.vArr vs))
        (ihi : EvalProp σ Δ i (Value.vZ j))
        (idx : vs[j]? = some v) :
        EvalProp σ Δ (Expr.arrIdx a i) v

    -- E-LOOKUP
    | LookUp {σ Δ vname cname args e v}
      (ih₁: EvalProp σ Δ e v):
      EvalProp σ Δ (Expr.lookup vname cname args e) v
end

end Eval
