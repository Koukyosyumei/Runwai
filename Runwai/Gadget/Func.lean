import Runwai.Typing
import Runwai.Gadget.Utils
import Runwai.Gadget.EnvLemmas
import Runwai.Gadget.EvalLemmas

open Ast

abbrev iszero_func := (Ast.Expr.lam "x" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
      (Ast.Expr.lam "y" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
        (Ast.Expr.lam "inv" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
          ((Ast.Expr.letIn "u₁" (.assertE (.var "y") (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var "x")) .mul (.var "inv")) (.add) (.constF 1)))
            (Ast.Expr.letIn "u₂" (.assertE (.fieldExpr (.var "x") .mul (.var "y")) (.constF 0)) (.var "u₂")))))))

lemma isZero_eval_eq_branch_semantics {x y inv: Expr} {σ: Env.ValEnv} {Δ: Env.ChipEnv}
  (h₁ : Eval.EvalProp σ Δ (exprEq y ((((Expr.constF 0).fieldExpr FieldOp.sub x).fieldExpr FieldOp.mul inv).fieldExpr
                  FieldOp.add (Expr.constF 1))) (Value.vBool true))
  (h₂ : Eval.EvalProp σ Δ (exprEq (x.fieldExpr FieldOp.mul y) (Expr.constF 0)) (Value.vBool true))
  (hx : Eval.EvalProp σ Δ x xv) (hy : Eval.EvalProp σ Δ y yv) (hinv : Eval.EvalProp σ Δ inv invv) :
  Eval.EvalProp σ Δ (exprEq y (.branch (x.binRel RelOp.eq (Expr.constF 0)) (Expr.constF 1) (Expr.constF 0))) (Value.vBool true) := by {
  cases h₁; cases h₂; rename_i v₁ v₂ ih₁ ih₂ r v₃ v₄ ih₃ ih₄ ih₅
  cases ih₂; cases ih₃; cases ih₄; rename_i v₅ v₆ ih₂ ih₃ ih₄ i₃ i₄ ih₆ ih₇ ih₈
  cases ih₂; cases ih₃; rename_i i₅ i₆ ih₂ ih₃ ih₉
  cases ih₂; rename_i i₁ i₂ ih₂ ihh₁ ihh₂
  cases ih₂
  have he₁ := evalprop_deterministic hy ih₁
  have he₂ := evalprop_deterministic hx ih₆
  have he₃ := evalprop_deterministic hinv ih₃
  have he₄ := evalprop_deterministic hy ih₇
  cases ih₈; simp at ih₅; cases ih₉; simp at ih₄; cases ihh₂; simp at ih₄
  set x_val := i₃; set y_val := i₄; set inv_val := i₆
  have he₅ := evalprop_deterministic ih₆ ihh₁
  simp at r
  rw[he₄] at he₁; rw[← ih₄, ← he₁] at r
  simp_all
  rw[← he₅] at ih₅ r
  unfold exprEq; apply Eval.EvalProp.Rel; exact ih₁
  have h₃: x_val = 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 1) := by {
    intro h
    apply Eval.EvalProp.IfTrue; apply Eval.EvalProp.Rel; exact ihh₁
    apply Eval.EvalProp.ConstF; unfold Eval.evalRelOp
    simp_all; apply Eval.EvalProp.ConstF
  }
  have h₄: x_val ≠ 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 0) := by {
    intro h
    apply Eval.EvalProp.IfFalse; apply Eval.EvalProp.Rel; exact ihh₁
    apply Eval.EvalProp.ConstF; unfold Eval.evalRelOp
    simp_all; apply Eval.EvalProp.ConstF
  }
  have h₅: Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (if x_val = 0 then (Value.vF 1) else (Value.vF 0)) := by {
    by_cases h : x_val = 0
    . simp_all
    . simp_all
  }
  exact h₅
  by_cases hz: x_val = 0
  . simp_all; rw[← he₅] at ih₄; rw [zero_mul, neg_zero, zero_add] at ih₄; rw[← ih₄]; simp
  . simp_all; rw[← ih₄]; simp
}

lemma isZero_typing_soundness (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ: Env.TyEnv) (φ₁ φ₂ φ₃: Ast.Predicate)
  (x y inv u₁ u₂: String)
  (htx: Env.lookupTy Γ x = (Ty.refin Ast.Ty.field φ₁))
  (hty: Env.lookupTy Γ y = (Ty.refin Ast.Ty.field φ₂))
  (htinv: @Ty.TypeJudgment Δ Γ Η (.var inv) (Ty.refin Ast.Ty.field φ₃))
  (hne₁: ¬ x = u₁)
  (hne₂: ¬ y = u₁)
  (hne₃: ¬ u₁ = u₂):
  @Ty.TypeJudgment Δ Γ Η
    (Ast.Expr.letIn u₁ (.assertE (.var y) (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var x)) .mul (.var inv)) (.add) (.constF 1)))
      (Ast.Expr.letIn u₂ (.assertE (.fieldExpr (.var x) .mul (.var y)) (.constF 0)) (.var u₂)))
    (Ty.refin Ast.Ty.unit (Ast.Predicate.ind (exprEq (.var y) (.branch (.binRel (.var x) (.eq) (.constF 0)) (.constF 1) (.constF 0))))) := by {
    apply Ty.TypeJudgment.TE_LetIn; apply lookup_update_self;
    apply Ty.TypeJudgment.TE_Assert; apply Ty.TypeJudgment.TE_VarEnv; exact hty
    repeat apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_ConstF; apply Ty.TypeJudgment.TE_VarEnv; exact htx; exact htinv
    apply Ty.TypeJudgment.TE_ConstF; apply Ty.TypeJudgment.TE_LetIn; apply lookup_update_self
    apply Ty.TypeJudgment.TE_Assert; apply Ty.TypeJudgment.TE_BinOpField; apply Ty.TypeJudgment.TE_VarEnv
    rw[← htx]; apply lookup_update_ne; exact hne₁
    apply Ty.TypeJudgment.TE_VarEnv
    rw[← hty]; apply lookup_update_ne; exact hne₂
    apply Ty.TypeJudgment.TE_ConstF
    have h_sub : @Ty.SubtypeJudgment Δ (Env.updateTy
      (Env.updateTy Γ u₁
        (Ty.unit.refin
          (Ast.Predicate.ind
            (exprEq (Expr.var y)
              ((((Expr.constF 0).fieldExpr FieldOp.sub (.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
                (Expr.constF 1))))))
      u₂ (Ty.unit.refin (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))))
      (Ty.unit.refin (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0))))
      (Ty.unit.refin
        (Ast.Predicate.ind (exprEq (Expr.var y) (((Expr.var x).binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0))))) := by {
        apply Ty.SubtypeJudgment.TSub_Refine
        apply Ty.SubtypeJudgment.TSub_Refl
        unfold PropSemantics.tyenvToProp PropSemantics.predToProp PropSemantics.exprToProp PropSemantics.varToProp
        intro σ e h₂
        set φ₁ := (Ast.Predicate.ind
          (exprEq (Expr.var y)
            ((((Expr.constF 0).fieldExpr FieldOp.sub (Expr.var x)).fieldExpr FieldOp.mul (Expr.var inv)).fieldExpr FieldOp.add
              (Expr.constF 1))))
        set φ₂ := (Ast.Predicate.ind (exprEq ((Expr.var x).fieldExpr FieldOp.mul (Expr.var y)) (Expr.constF 0)))
        have h₃ := h₂ u₁ (Ty.unit.refin φ₁)
        have h₄: Env.lookupTy (Env.updateTy (Env.updateTy Γ u₁ (Ty.unit.refin φ₁)) u₂ (Ty.unit.refin φ₂)) u₁ = (Ty.unit.refin φ₁) := by {
          apply lookup_update_ne_of_lookup
          exact hne₃
          apply lookup_update_self
        }
        have h₅ := h₃ h₄
        rw[h₄] at h₅
        simp at h₅
        unfold PropSemantics.predToProp PropSemantics.exprToProp at h₅
        intro h₁
        apply isZero_eval_eq_branch_semantics h₅ h₁
        repeat apply Eval.EvalProp.Var; rfl
      }
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_self
    exact h_sub
}

lemma iszero_func_typing_soundness (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ: Env.TyEnv) :
  @Ty.TypeJudgment Δ Γ Η iszero_func
    (Ast.Ty.func "x" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
      (Ast.Ty.func "y" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
        (Ast.Ty.func "inv" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
          (Ty.refin Ast.Ty.unit (Ast.Predicate.ind (exprEq (.var "y") (.branch (.binRel (.var "x") (.eq) (.constF 0)) (.constF 1) (.constF 0)))))))) := by {
      repeat
        apply Ty.TypeJudgment.TE_Abs
        apply lookup_update_self
      apply isZero_typing_soundness
      apply lookup_update_ne_of_lookup
      simp
      apply lookup_update_ne_of_lookup
      simp
      apply lookup_update_self
      apply lookup_update_ne_of_lookup
      simp
      apply lookup_update_self
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_self
      repeat simp
    }
