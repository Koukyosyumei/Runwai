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
  | Value.vBool i, Value.vBool j =>
    match op with
    | RelOp.eq => some (i = j)
    | _ => none
  | _, _ => none

/-- Evaluate a boolean operator `op` on two `Value.bool` arguments. -/
@[simp]
def evalBoolOp (op : BooleanOp) : Value → Value → Option Bool
  | Value.vBool x, Value.vBool y =>
    some $ match op with
    | BooleanOp.and => x && y
    | BooleanOp.or  => x || y
  | _, _ => none

inductive EvalProp : ValEnv → TraceEnv → ChipEnv → Expr → Value → Prop
  -- E‑VALUE
  | ConstF        {σ T Δ v} : EvalProp σ T Δ (Expr.constF v) (Value.vF v)
  | ConstZ        {σ T Δ v} : EvalProp σ T Δ (Expr.constZ v) (Value.vZ v)
  | ConstBool     {σ T Δ b} : EvalProp σ T Δ (Expr.constBool b) (Value.vBool b)
  | ConstArr  {σ T Δ xs es} (ilength: xs.length = es.length) (ih : ∀ xe ∈ List.zip xs es, EvalProp σ T Δ xe.fst xe.snd) :
      EvalProp σ T Δ (Expr.arr xs) (Value.vArr es)

  | toZ {σ T Δ e v} (h: EvalProp σ T Δ e (Ast.Value.vF v)) :
      EvalProp σ T Δ (Expr.toZ e) (Ast.Value.vZ v.val)

  -- E‑VAR
  | Var {σ T Δ x v} : lookupVal σ x = v → EvalProp σ T Δ (Expr.var x) v

  -- E‑LAM
  | Lam {σ T Δ x τ body} : EvalProp σ T Δ (Expr.lam x τ body) (Value.vClosure x body σ)

  -- E‑LET
  | Let      {σ T Δ x e₁ e₂ v₁ v₂}
      (ih₁ : EvalProp σ T Δ e₁ v₁)
      (ih₂ : EvalProp (updateVal σ x v₁) T Δ e₂ v₂) :
      EvalProp σ T Δ (Expr.letIn x e₁ e₂) v₂

  -- E‑APP
  | App      {σ T Δ f a x body σ' va vb}
      (ih_f : EvalProp σ T Δ f (Value.vClosure x body σ'))
      (ih_a : EvalProp σ T Δ a va)
      (ih_b : EvalProp (updateVal σ' x va) T Δ body vb) :
      EvalProp σ T Δ (Expr.app f a) vb

  -- E‑FBINOP
  | FBinOp   {σ T Δ e₁ e₂ op i₁ i₂ v}
      (ih₁ : EvalProp σ T Δ e₁ (Value.vF i₁))
      (ih₂ : EvalProp σ T Δ e₂ (Value.vF i₂))
      (r   : evalFieldOp op (Value.vF i₁) (Value.vF i₂) = some v) :
      EvalProp σ T Δ (Expr.fieldExpr e₁ op e₂) v

  -- E‑ZBINOP
  | ZBinOp   {σ T Δ e₁ e₂ op i₁ i₂ v}
      (ih₁ : EvalProp σ T Δ e₁ (Value.vZ i₁))
      (ih₂ : EvalProp σ T Δ e₂ (Value.vZ i₂))
      (r   : evalIntegerOp op (Value.vZ i₁) (Value.vZ i₂) = some v) :
      EvalProp σ T Δ (Expr.integerExpr e₁ op e₂) v

  -- E‑BOOLBINOP
  | BoolOp   {σ T Δ e₁ e₂ op b₁ b₂ b}
      (ih₁ : EvalProp σ T Δ e₁ (Value.vBool b₁))
      (ih₂ : EvalProp σ T Δ e₂ (Value.vBool b₂))
      (bv  : evalBoolOp op (Value.vBool b₁) (Value.vBool b₂) = some b) :
      EvalProp σ T Δ (Expr.boolExpr e₁ op e₂) (Value.vBool b)

  -- E‑REL
  | Rel      {σ T Δ e₁ e₂ op v₁ v₂ b}
      (ih₁ : EvalProp σ T Δ e₁ v₁)
      (ih₂ : EvalProp σ T Δ e₂ v₂)
      (r   : evalRelOp op v₁ v₂ = some b) :
      EvalProp σ T Δ (Expr.binRel e₁ op e₂) (Value.vBool b)

  -- E-BRANCH
  | IfTrue {σ T Δ c e₁ e₂ v₁}
      (ihc : EvalProp σ T Δ c (Value.vBool true))
      (ih₁ : EvalProp σ T Δ e₁ v₁):
      EvalProp σ T Δ (Expr.branch c e₁ e₂) (v₁)

  | IfFalse {σ T Δ c e₁ e₂ v₂}
      (ihc : EvalProp σ T Δ c (Value.vBool false))
      (ih₁ : EvalProp σ T Δ e₂ v₂):
      EvalProp σ T Δ (Expr.branch c e₁ e₂) (v₂)

  -- E‑ASSERT
  | Assert   {σ T Δ e₁ e₂ v}
      (ih₁ : EvalProp σ T Δ e₁ (Ast.Value.vF v))
      (ih₂ : EvalProp σ T Δ e₂ (Ast.Value.vF v)) :
      EvalProp σ T Δ (Expr.assertE e₁ e₂) (Value.vUnit)

  -- E‑ARRIDX
  | ArrIdx {σ T Δ a i vs j v}
      (iha : EvalProp σ T Δ a (Value.vArr vs))
      (ihi : EvalProp σ T Δ i (Value.vZ j))
      (idx : vs[j]? = some v) :
      EvalProp σ T Δ (Expr.arrIdx a i) v

  -- E-LOOKUP // This is actually the combination of E-LOOKUP and E-LETIN. We adopt this design to propoage used names in the following body.
  | LookUp {σ T Δ vname cname args e v c row}
    (h_body: EvalProp σ T Δ e v)
    (h_chip: Env.lookupChip Δ cname = c)
    (h_trace: Env.lookupTrace T c = some (Ast.Value.vArr (row)))
    (i: ℕ)
    (h_bound: i < row.length)
    (vs: List F)
    (h_evals:∀ p ∈ List.zip (args.map Prod.fst) vs,
        EvalProp σ T Δ p.fst (Value.vF p.snd))
    (h_asserts:
      let σ' := Env.updateVal (Env.updateVal σ c.ident_t (Value.vArr row)) c.ident_i (Value.vZ i)
      ∀ p ∈ List.zip vs (args.map Prod.snd),
        EvalProp σ' T Δ (Expr.assertE (Expr.constF p.fst) p.snd) Value.vUnit
    )
    :EvalProp σ T Δ (Expr.lookup vname cname args e) v

end Eval
