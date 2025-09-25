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
def evalUIntOp (op: IntOp) : Value → Value → Option Value
  | Value.vN x, Value.vN y =>
    some $ Value.vN $
      match op with
      | IntOp.add => x + y
      | IntOp.sub => x - y
      | IntOp.mul => x * y
  | _, _ => none

/-- Evaluate a relational operator `op` on two `Value` arguments. -/
@[simp]
def evalRelOp (op: RelOp) : Value → Value → Option Bool
  | Value.vF i, Value.vF j =>
    match op with
    | RelOp.eq => some (i = j)
    | _ => none
  | Value.vN i, Value.vN j =>
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
def evalBoolOp (op : BoolOp) : Value → Value → Option Bool
  | Value.vBool x, Value.vBool y =>
    some $ match op with
    | BoolOp.and => x && y
    | BoolOp.or  => x || y
  | _, _ => none

inductive EvalProp : ValEnv → TraceEnv → ChipEnv → Expr → Value → Prop
  -- E‑VALUE
  | ConstF        {σ T Δ v} : EvalProp σ T Δ (Expr.constF v) (Value.vF v)
  | ConstN        {σ T Δ v} : EvalProp σ T Δ (Expr.constN v) (Value.vN v)
  | ConstBool     {σ T Δ b} : EvalProp σ T Δ (Expr.constBool b) (Value.vBool b)
  | ConstArr  {σ T Δ xs es} (ilength: xs.length = es.length) (ih : ∀ xe ∈ List.zip xs es, EvalProp σ T Δ xe.fst xe.snd) :
      EvalProp σ T Δ (Expr.arr xs) (Value.vArr es)

  | toN {σ T Δ e v} (h: EvalProp σ T Δ e (Ast.Value.vF v)) :
      EvalProp σ T Δ (Expr.toN e) (Ast.Value.vN v.val)

  | toF {σ T Δ e v} (h: EvalProp σ T Δ e (Ast.Value.vN v)) :
      EvalProp σ T Δ (Expr.toF e) (Ast.Value.vF v)

  -- E‑VAR
  | Var {σ T Δ x v} : getVal σ x = v → EvalProp σ T Δ (Expr.var x) v

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
  | NBinOp   {σ T Δ e₁ e₂ op i₁ i₂ v}
      (ih₁ : EvalProp σ T Δ e₁ (Value.vN i₁))
      (ih₂ : EvalProp σ T Δ e₂ (Value.vN i₂))
      (r   : evalUIntOp op (Value.vN i₁) (Value.vN i₂) = some v) :
      EvalProp σ T Δ (Expr.uintExpr e₁ op e₂) v

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
      (ihi : EvalProp σ T Δ i (Value.vN j))
      (idx : vs[j]? = some v) :
      EvalProp σ T Δ (Expr.arrIdx a i) v

  | Len {σ T Δ e vs}
      (h: EvalProp σ T Δ e (Ast.Value.vArr vs)) :
      EvalProp σ T Δ (Expr.len e) (Value.vN (vs.length))

  -- E-LOOKUP
  | LookUp {σ T Δ vname cname args e v c rows}
    -- This constructor defines the semantics for a lookup expression, which serves a dual purpose:
    -- 1. It enforces a set of constraints (a "lookup argument") between the calling context
    --    and a callee chip's execution trace.
    -- 2. It provides `let-in`-like scoping, where a subsequent expression `e` is evaluated
    --    after the lookup constraints are satisfied.

    -- == Body Evaluation Semantics ==
    -- Premise for the `let-in` behavior. After all lookup constraints pass, this ensures
    -- that the body expression `e` evaluates to the final value `v` of the whole expression.
    (h_body: EvalProp σ T Δ e v)

    -- == Context Setup ==
    -- Premise to retrieve the callee's chip definition `c` from the global chip environment `Δ`.
    (h_chip: Env.getChip Δ cname = c)
    -- Premise to retrieve the callee's full execution trace `rows` from the global trace environment `T`.
    (h_trace: Env.getTrace T c = some (Ast.Value.vArr (rows)))

    -- == Verification of Callee's Trace ==
    -- Premise ensuring the internal consistency of the callee's trace. It guarantees that we
    -- are looking up into a well-formed "table" by checking that the callee's constraint body
    -- (`c.body`) holds for ALL rows `j` of its trace.
    (h_callee_validity:
      ∀ j: ℕ, (j < rows.length) →
        let σ' := Env.updateVal (Env.updateVal σ c.ident_t (Value.vArr rows)) c.ident_i (Value.vN j)
        EvalProp σ' T Δ c.body Value.vUnit
    )

    -- == Witnesses provided by the Prover ==
    (i: ℕ)
    (vs: List F)

    -- == Verification of Witnesses and Lookup Connection ==
    -- Premise checking that the witness row index `i` is within the bounds of the callee's trace.
    (h_bound: i < rows.length)
    -- Premise ensuring the argument list and the witness value list have the same length.
    (h_args_len: args.length = vs.length)
    -- Premise verifying the witness values `vs`. It proves that the caller-side expressions
    -- (`args.map Prod.fst`) indeed evaluate to the claimed values in `vs`.
    (h_evals:∀ p ∈ List.zip (args.map Prod.fst) vs,
        EvalProp σ T Δ p.fst (Value.vF p.snd))
    -- The central lookup premise. It verifies the connection between the caller and callee.
    -- Using the witness row `i` and the verified witness values `vs`, it checks that for each
    -- value-expression pair, the assertion holds in the callee's context at row `i`.
    (h_asserts:
      let σ' := Env.updateVal (Env.updateVal σ c.ident_t (Value.vArr rows)) c.ident_i (Value.vN i)
      ∀ p ∈ List.zip vs (args.map Prod.snd),
        EvalProp σ' T Δ (Expr.assertE (Expr.constF p.fst) p.snd) Value.vUnit
    )
    :EvalProp σ T Δ (Expr.lookup vname cname args e) v

end Eval
