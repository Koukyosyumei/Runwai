import Runwai.Typing
import Runwai.Gadget.Utils
import Runwai.Gadget.EnvLemmas
import Runwai.Gadget.PredLemmas

open Ast

lemma var_has_subtype_in_tyenv {Γ: Env.TyEnv} {Δ: Env.ChipEnv}
    {x : String} {τ: Ast.Ty} {φ: Ast.Predicate}
    (h: Env.getTy Γ x = (Ast.Ty.refin τ φ))
    (hneq : x ≠ Ast.nu):
    Ty.SubtypeJudgment Δ Γ (τ.refin (Predicate.dep nu (exprEq (Expr.var nu) (Expr.var x)))) (τ.refin φ) := by
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v h₁ h₂
    unfold PropSemantics.tyenvToProp at h₁
    unfold PropSemantics.varToProp at h₁
    have h₃ := h₁ x (τ.refin φ)
    simp_all
    cases h₂
    rename_i ihf iha ihb
    cases ihf
    cases ihb
    rename_i ih₁ ih₂
    cases ih₁
    rename_i ih₁₁ ih₁₂
    cases ih₁₁
    rename_i ih₁₃
    simp [Env.getVal, Env.updateVal] at ih₁₃
    rename_i va v₁ v₂
    have := get_val_update_ne σ Ast.nu x va hneq
    rw[this] at ih₁₂
    have : Eval.EvalProp σ T Δ (.var x) v₂ := by {
      apply Eval.EvalProp.Var ih₁₂
    }
    simp at ih₂
    cases v₁
    cases v₂ with
    | vF val => {
      simp at ih₂
      rw[ih₂] at ih₁₃
      rw[ih₁₃] at iha
      rename_i x₁ x₂
      have h := (@predToProp_congr σ T Δ τ φ v (.var x) (.vF val) iha this).mpr h₃
      exact h
    }
    | _ => simp at ih₂
    cases v₂ with
    | vN val => {
      simp at ih₂
      rw[ih₂] at ih₁₃
      rw[ih₁₃] at iha
      rename_i h val'
      have h := (@predToProp_congr σ T Δ τ φ v (.var x) (.vN val) iha this).mpr h₃
      exact h
    }
    | _ => simp at ih₂
    cases v₂ with
    | vInt val => {
      simp at ih₂
      rw[ih₂] at ih₁₃
      rw[ih₁₃] at iha
      rename_i h val'
      have h := (@predToProp_congr σ T Δ τ φ v (.var x) (.vInt val) iha this).mpr h₃
      exact h
    }
    | _ => simp at ih₂
    cases v₂ with
    | _ => simp at ih₂
    cases v₂ with
    | vBool val => {
      simp at ih₂
      rw[ih₂] at ih₁₃
      rw[ih₁₃] at iha
      rename_i h val'
      have h := (@predToProp_congr σ T Δ τ φ v (.var x) (.vBool val) iha this).mpr h₃
      exact h
    }
    | _ => simp at ih₂
    cases v₂ with
    | _ => simp at ih₂
    cases v₂ with
    | _ => simp at ih₂

lemma var_has_type_in_tyenv {Γ: Env.TyEnv} {Δ: Env.ChipEnv} {Η: Env.UsedNames}
    {x : String} {τ: Ast.Ty} {φ: Ast.Predicate}
    (h: Env.getTy Γ x = (Ast.Ty.refin τ φ))
    (hneq : x ≠ Ast.nu):
    @Ty.TypeJudgment Δ Γ Η (Ast.Expr.var x) (Ast.Ty.refin τ φ) := by
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_Var h
    apply @var_has_subtype_in_tyenv Γ Δ
    exact h
    exact hneq

/--
If a variable `x` is typed with a refinement `{_ : unit | e}` in a semantically valid
environment, this lemma provides a proof that the expression `e` will evaluate to `true`.
-/
lemma tyenv_to_eval_expr {σ T Δ Γ x τ e} (h₁: PropSemantics.tyenvToProp σ T Δ Γ) (h₂: Env.getTy Γ x = some (Ast.Ty.refin τ (Ast.Predicate.ind e))):
  (Eval.EvalProp σ T Δ e (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp at h₁
    simp [PropSemantics.varToProp] at h₁
    have h₁' := h₁ x (Ast.Ty.refin τ (Ast.Predicate.ind e)) h₂
    rw[h₂] at h₁'
    simp at h₁'
    exact h₁'
  }

--  | Ast.Predicate.dep ident body => fun v => exprToProp σ Δ (Ast.Expr.app (Ast.Expr.lam ident τ body) v)
lemma tyenv_dep_to_eval_expr {σ T Δ Γ x τ body} (h₁: PropSemantics.tyenvToProp σ T Δ Γ) (h₂: Env.getTy Γ x = some (Ast.Ty.refin τ (Ast.Predicate.dep v body))):
  (Eval.EvalProp σ T Δ (Ast.Expr.app (Ast.Expr.lam v τ body) (Ast.Expr.var x)) (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp at h₁
    simp [PropSemantics.varToProp] at h₁
    have h₁' := h₁ x (Ast.Ty.refin τ (Ast.Predicate.dep v body)) h₂
    rw[h₂] at h₁'
    simp at h₁'
    exact h₁'
  }

/--
Deconstructs a **conjunctive type guarantee** into individual runtime proofs.

If a variable's type guarantees that `e₁ ∧ e₂` holds, this lemma allows us to derive
separate evaluation proofs for both `e₁` and `e₂`.
-/
lemma tyenv_and_to_eval_exprs {σ T Δ Γ x e₁ e₂} (h₁: PropSemantics.tyenvToProp σ T Δ Γ) (h₂: Env.getTy Γ x = some (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂)))):
  (Eval.EvalProp σ T Δ e₁ (Ast.Value.vBool true)) ∧ (Eval.EvalProp σ T Δ e₂ (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp at h₁
    simp [PropSemantics.varToProp] at h₁
    have h₁' := h₁ x (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂))) h₂
    rw[h₂] at h₁'
    simp at h₁'
    exact h₁'
  }

lemma tyenvToProp_implies_varToProp
  (σ : Env.ValEnv) (T: Env.TraceEnv) (Δ : Env.ChipEnv) (Γ : Env.TyEnv)
  (x : String) (τ : Ast.Ty) (φ : Ast.Predicate)
  (hΓx : Env.getTy Γ x = Ast.Ty.refin τ φ)
  (hmt : PropSemantics.tyenvToProp σ T Δ Γ) :
  PropSemantics.varToProp σ T Δ Γ x := by
  dsimp [PropSemantics.tyenvToProp] at hmt
  apply hmt
  exact hΓx

lemma constZ_refine_lt {Δ Γ Η x y} {h: x < y} :
  @Ty.TypeJudgment Δ Γ Η (Ast.Expr.constN x) (Ast.Ty.uint.refin (Ast.Predicate.dep Ast.nu ((Ast.Expr.var Ast.nu).binRel Ast.RelOp.lt (Ast.Expr.constN y)))) := by {
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_ConstN
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ T v h₁ h₂
  simp [PropSemantics.predToProp] at h₂ ⊢
  cases h₂
  rename_i va ih₁ ih₂ ih₃
  cases ih₁
  cases ih₃
  rename_i v₁ v₂ ih₁ ih₃ r
  cases ih₃
  simp [Eval.evalRelOp] at r
  cases v₁ <;> simp at r
  rw[r] at ih₁
  apply Eval.EvalProp.App
  apply Eval.EvalProp.Lam
  exact ih₂
  apply Eval.EvalProp.Rel
  exact ih₁
  apply Eval.EvalProp.ConstN
  simp [Eval.evalRelOp]
  exact h
}

lemma varZ_refine_lt {Δ Γ Η x v₁ v₂} {h₀: Env.getTy Γ x = (Ast.Ty.refin Ast.Ty.uint (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu) (Ast.Expr.constN v₁))))} {h₁: v₁ < v₂} {h₂: x ≠ nu} :
  @Ty.TypeJudgment Δ Γ Η (Ast.Expr.var x) (Ast.Ty.uint.refin (Ast.Predicate.dep Ast.nu ((Ast.Expr.var Ast.nu).binRel Ast.RelOp.lt (Ast.Expr.constN v₂)))) := by {
  apply Ty.TypeJudgment.TE_SUB
  apply var_has_type_in_tyenv
  exact h₀
  exact h₂
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ T v h₃ h₄
  unfold PropSemantics.tyenvToProp at h₃
  have h₅ := h₃ x ((Ty.uint.refin (Predicate.dep Ast.nu (exprEq (Expr.var Ast.nu) (Expr.constN v₁))))) h₀
  simp [PropSemantics.predToProp] at h₄ ⊢
  simp [PropSemantics.varToProp] at h₅
  rw[h₀] at h₅
  simp at h₅
  cases h₄
  rename_i ih_f ih_a ih_b
  cases ih_f
  cases ih_b
  rename_i ih₁ ih₂ r
  cases ih₁
  rename_i a
  unfold Env.getVal Env.updateVal at a
  simp at a
  rw[← a] at r
  cases ih₂
  simp [Eval.evalRelOp] at r
  rename_i va₁ va₂
  cases va₁ with
  | vN x => {
    simp at r
    apply Eval.EvalProp.App
    apply Eval.EvalProp.Lam
    exact ih_a
    apply Eval.EvalProp.Rel
    apply Eval.EvalProp.Var
    unfold Env.getVal Env.updateVal
    simp
    rfl
    apply Eval.EvalProp.ConstN
    rw[r]
    simp [Eval.evalRelOp]
    exact h₁
  }
  | _ => {
    simp at r
  }
}

lemma varZ_refine_int_diff_lt {Γ Η} (n x: String)
  (h₀: Env.getTy Γ n = (Ast.Ty.refin Ast.Ty.uint
      (Ast.Predicate.dep Ast.nu (Ast.exprEq (Ast.Expr.var Ast.nu ) (Ast.Expr.constN height)))))
  (h₁: Env.getTy Γ x = (Ast.Ty.unit.refin
      (Ast.Predicate.ind
        ((Ast.Expr.var i).binRel Ast.RelOp.lt
          ((Ast.Expr.var n).uintExpr Ast.IntOp.sub (Ast.Expr.constN d))))))
  (h₂: Env.getTy Γ i = (Ast.Ty.uint.refin φ))
  (h₃: i ≠ Ast.nu ):
  @Ty.TypeJudgment Δ Γ Η ((Ast.Expr.var i).uintExpr Ast.IntOp.add (Ast.Expr.constN d))
    (Ast.Ty.uint.refin (Ast.Predicate.dep Ast.nu  ((Ast.Expr.var Ast.nu).binRel Ast.RelOp.lt (Ast.Expr.constN height)))) := by {
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_BinOpUInt
    apply var_has_type_in_tyenv
    exact h₂
    exact h₃
    apply Ty.TypeJudgment.TE_ConstN
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v ha hb
    unfold PropSemantics.tyenvToProp at ha
    have h₀' := ha n (Ty.uint.refin (Predicate.dep Ast.nu (exprEq (Expr.var Ast.nu) (Expr.constN height)))) h₀
    have h₁' := ha x (Ty.unit.refin
      (Predicate.ind ((Expr.var i).binRel RelOp.lt ((Expr.var n).uintExpr IntOp.sub (Expr.constN d))))) h₁
    simp at h₀' h₁'
    rw[h₀] at h₀'
    simp at h₀'
    rw[h₁] at h₁'
    simp at h₁'
    cases h₀'
    rename_i ihf iha idx
    cases ihf
    cases iha
    cases idx
    rename_i ih₁ ih₂ r
    cases ih₂
    cases ih₁
    rename_i a
    unfold Env.getVal Env.updateVal at a
    simp at a
    cases h₁'
    rename_i ih₁ ih₂ r
    cases ih₁
    cases ih₂
    rename_i ih₁ ih₂ r
    cases ih₂
    cases ih₁
    simp at r
    rename_i hn' _ r' i_val _ r hi n_val hn
    rw[hn] at hn'
    rw[← hn'] at a
    rw[← a] at r'
    simp at r'
    rename_i r''
    rw[← r] at r''
    simp at hb
    cases hb
    rename_i ihf iha ihb
    cases ihf
    cases ihb
    rename_i ih₁ ih₂ r
    cases ih₁
    rename_i a
    unfold Env.getVal Env.updateVal at a
    simp at a
    cases ih₂
    rename_i ih₁ ih₂ r
    cases ih₁
    cases ih₂
    simp at r
    cases i_val with
    | vN i_val' => {
      simp at r''
      simp[PropSemantics.predToProp]
      apply Eval.EvalProp.App
      apply Eval.EvalProp.Lam
      exact iha
      apply Eval.EvalProp.Rel
      apply Eval.EvalProp.Var
      unfold Env.getVal Env.updateVal
      simp
      rfl
      apply Eval.EvalProp.ConstN
      rename_i ih₂ _ u₁ _ ih₁ _ _
      rw[← r] at ih₁
      cases u₁ with
      | vN uv₁ => {
        simp at ih₁
        rw[a]
        rw[ih₁]
        rename_i a'
        rename_i va' v2₂' i'
        have : Env.getVal (Env.updateVal σ Ast.nu va') i = Env.getVal σ i := by {
          apply get_val_update_ne
          exact h₃
        }
        rw[this] at a'
        rw[hi] at a'
        rw[r'] at r''
        simp at a'
        rw[a'] at r''
        simp [Eval.evalRelOp]
        omega
      }
      | _ => {
        simp at ih₁
      }
    }
    | _ => {
      simp at r''
    }
  }
