import Runwai.Ast
import Runwai.PropSemantics
import Runwai.Gadget.EvalLemmas


def Ast.Predicate.induction_custom
  {P : Ast.Predicate → Prop}
  (dep : ∀ (ident : String) (body : Ast.Expr), P (Ast.Predicate.dep ident body))
  (ind : ∀ (body : Ast.Expr), P (Ast.Predicate.ind body))
  (and : ∀ (l r : Ast.Predicate), P l → P r → P (Ast.Predicate.and l r))
  (or  : ∀ (l r : Ast.Predicate), P l → P r → P (Ast.Predicate.or l r))
  (not : ∀ (φ : Ast.Predicate), P φ → P (Ast.Predicate.not φ))
  (φ : Ast.Predicate) : P φ :=
  match φ with
  | Ast.Predicate.dep i b => dep i b
  | Ast.Predicate.ind b   => ind b
  | Ast.Predicate.and l r => and l r (Ast.Predicate.induction_custom dep ind and or not l) (Ast.Predicate.induction_custom dep ind and or not r)
  | Ast.Predicate.or l r  => or l r (Ast.Predicate.induction_custom dep ind and or not l) (Ast.Predicate.induction_custom dep ind and or not r)
  | Ast.Predicate.not inner => not inner (Ast.Predicate.induction_custom dep ind and or not inner)

lemma predToProp_congr {σ: Env.ValEnv} {T: Env.TraceEnv} {Δ: Env.ChipEnv} {τ: Ast.Ty}
  {φ: Ast.Predicate} {e₁ e₂: Ast.Expr}  {v: Ast.Value}
  (h₂: Eval.EvalProp σ T Δ e₁ v) (h₃: Eval.EvalProp σ T Δ e₂ v):
  PropSemantics.predToProp σ T Δ τ φ e₁ ↔ PropSemantics.predToProp σ T Δ τ φ e₂ := by {
    induction φ using Ast.Predicate.induction_custom
    {
      rename_i ident body
      constructor
      {
        intro h₁
        have : Eval.EvalProp σ T Δ ((Ast.Expr.lam ident τ body).app e₂) (Ast.Value.vBool true) := by {
          cases h₁
          rename_i ihf iha ihb
          apply Eval.EvalProp.App
          exact ihf
          exact h₃
          have hv₁ := evalprop_deterministic h₂ iha
          rw[← hv₁] at ihb
          exact ihb
        }
        unfold PropSemantics.predToProp at h₁
        unfold PropSemantics.predToProp
        exact this
      }
      {
        intro h₁
        have : Eval.EvalProp σ T Δ ((Ast.Expr.lam ident τ body).app e₁) (Ast.Value.vBool true) := by {
          cases h₁
          rename_i ihf iha ihb
          apply Eval.EvalProp.App
          exact ihf
          exact h₂
          have hv₁ := evalprop_deterministic h₃ iha
          rw[← hv₁] at ihb
          exact ihb
        }
        unfold PropSemantics.predToProp at h₁
        unfold PropSemantics.predToProp
        exact this
      }
    }
    {
      simp
    }
    {
      simp
      rename_i ih_left ih_right
      rw [ih_left]
      rw [ih_right]
    }
    {
      simp
      rename_i ih_left ih_right
      rw [ih_left]
      rw [ih_right]
    }
    {
      simp
      rename_i ih
      rw [ih]
    }
  }
