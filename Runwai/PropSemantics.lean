import Runwai.Ast
import Runwai.Env
import Runwai.Eval

/-!
  # Predicate Semantics for Runwai

  This module interprets certain Runwai expressions as Lean `Prop`s,
  by evaluating them under a valuation environment `σ`, a circuit
  environment `Δ`, and a fuel bound `fuel`.
-/

namespace PropSemantics

/--
  Interpret a boolean or relational expression `e` as a `Prop`.

  Returns `true` exactly when
  1. `e` is a boolean operation `e₁ ∧/∨ e₂` that evaluates to `some b`
     with `b = true`, or
  2. `e` is a relational operation `e₁ =/</≤ e₂` that evaluates to
     `some b` with `b = true`, or
  3. `e` is the literal `true`.

  In all other cases, the result is `False`.
-/
def exprToProp (σ : Env.ValEnv) (Δ : Env.CircuitEnv) (e: Ast.Expr): Prop :=
  Eval.EvalProp σ Δ e (Ast.Value.vBool true)

def predToProp (σ: Env.ValEnv) (Δ: Env.CircuitEnv): Ast.Predicate → (Ast.Expr → Prop)
| Ast.Predicate.const e => fun _ => exprToProp σ Δ e
| Ast.Predicate.eq e    => fun v => exprToProp σ Δ (Ast.exprEq v e)

def varToProp (σ : Env.ValEnv) (Δ : Env.CircuitEnv) (Γ : Env.TyEnv) (ident : String): Prop :=
match Env.lookupTy Γ ident with
-- refinement types: check base-type match and predicate
| Ast.Ty.refin _ pred =>
  predToProp σ Δ pred (Ast.Expr.var ident)
-- bare field and boolean types
| Ast.Ty.field        => True
| Ast.Ty.bool         => True
| _ => False

def tyenvToProp (σ: Env.ValEnv) (Δ: Env.CircuitEnv) (Γ: Env.TyEnv): Prop :=
  ∀ (x: String) (τ: Ast.Ty), Env.lookupTy Γ x = some τ → varToProp σ Δ Γ x

end PropSemantics
