import Runwai.Ast
import Runwai.Env
import Runwai.Eval

/-!
  # Predicate Semantics for Runwai

  This module interprets certain Runwai expressions as Lean `Prop`s,
  by evaluating them under a valuation environment `σ`, a Chip
  environment `Δ`, and a fuel bound `fuel`.
-/

namespace PropSemantics

/--
Defines the semantic interpretation of an expression `e` as a formal proposition (`Prop`).

This proposition holds true if and only if `e` evaluates to the specific value `vBool true`
within the given value environment `σ` and chip environment `Δ`.
-/
@[simp]
def exprToProp (σ : Env.ValEnv) (T: Env.TraceEnv) (Δ : Env.ChipEnv) (e: Ast.Expr): Prop :=
  Eval.EvalProp σ T Δ e (Ast.Value.vBool true)

/--
Translates a syntactic predicate from a refinement type (`Ast.Predicate`) into a semantic
property in Lean's logic (`Prop`).

- `Predicate.dep`: For dependent predicates like `{x : τ | P}`, it models substitution by
  evaluating the application `(λ x:τ. P) v`.
- `Predicate.ind`: For independent predicates like `{_ : τ | P}`, it simply evaluates `P`,
  ignoring the value `v`.
- Logical connectives (`and`, `or`, `not`) are mapped directly to their logical
  counterparts in Lean (`∧`, `∨`, `¬`).
-/
@[simp]
def predToProp (σ: Env.ValEnv) (T: Env.TraceEnv) (Δ: Env.ChipEnv) (τ: Ast.Ty): Ast.Predicate → (Ast.Expr → Prop)
 | Ast.Predicate.dep ident body => fun v => exprToProp σ T Δ (Ast.Expr.app (Ast.Expr.lam ident τ body) v)
 | Ast.Predicate.ind body => fun _ => exprToProp σ T Δ body
 | Ast.Predicate.and left right => fun v => (predToProp σ T Δ τ left v) ∧ (predToProp σ T Δ τ right v)
 | Ast.Predicate.or  left right => fun v => (predToProp σ T Δ τ left v) ∨ (predToProp σ T Δ τ right v)
 | Ast.Predicate.not φ => fun v => ¬ (predToProp σ T Δ τ φ v)

/--
Defines the semantic validity condition for a single variable `ident` within a type
environment `Γ`.

It looks up the variable's type in `Γ` and checks if the variable satisfies the constraints
of that type:
- If the type is a refinement `{τ | φ}`, it uses `predToProp` to verify that the
  variable itself (as an expression `Expr.var ident`) satisfies the predicate `φ`.
- For simple, unrefined base types (`field`, `bool`, `int`), the condition is trivially true.
- For any other type or if the variable is not found, the condition is false.
-/
@[simp]
def varToProp (σ : Env.ValEnv) (T: Env.TraceEnv) (Δ : Env.ChipEnv) (Γ : Env.TyEnv) (ident : String): Prop :=
match Env.getTy Γ ident with
| Ast.Ty.refin τ pred =>
  predToProp σ T Δ τ pred (Ast.Expr.var ident)
| Ast.Ty.field        => True
| Ast.Ty.bool         => True
| Ast.Ty.int          => True
| _ => False

/--
Asserts the semantic validity of an entire type environment `Γ`.

This proposition holds if and only if **every** variable binding in the environment
satisfies its own type constraints, as checked by `varToProp`. It serves as the top-level
semantic judgment for a well-formed context, ensuring all declared properties are met.
-/
def tyenvToProp (σ: Env.ValEnv) (T: Env.TraceEnv) (Δ: Env.ChipEnv) (Γ: Env.TyEnv): Prop :=
  ∀ (x: String) (τ: Ast.Ty), Env.getTy Γ x = some τ → varToProp σ T Δ Γ x

end PropSemantics
