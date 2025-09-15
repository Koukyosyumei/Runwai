import Runwai.Typing
import Runwai.Gadget.Utils
import Runwai.Gadget.EnvLemmas
import Runwai.Gadget.EvalLemmas
import Runwai.Gadget.TypingLemmas
import Runwai.Gadget.FieldLemmas

open Ast

abbrev iszero_func: Ast.Expr :=
  (.lam "x" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "y" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "inv" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (.letIn "u₁" (.assertE (.var "y") (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var "x")) .mul (.var "inv")) (.add) (.constF 1)))
    (.letIn "u₂" (.assertE (.fieldExpr (.var "x") .mul (.var "y")) (.constF 0)) (.var "u₂"))))))

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
  apply Eval.EvalProp.Rel; exact ih₁
  have h₃: x_val = 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 1) := by {
    intro h
    apply Eval.EvalProp.IfTrue; apply Eval.EvalProp.Rel; exact ihh₁
    apply Eval.EvalProp.ConstF; simp [Eval.evalRelOp]
    simp_all; apply Eval.EvalProp.ConstF
  }
  have h₄: x_val ≠ 0 → Eval.EvalProp σ Δ ((x.binRel RelOp.eq (Expr.constF 0)).branch (Expr.constF 1) (Expr.constF 0)) (Value.vF 0) := by {
    intro h
    apply Eval.EvalProp.IfFalse; apply Eval.EvalProp.Rel; exact ihh₁
    apply Eval.EvalProp.ConstF; simp [Eval.evalRelOp]
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
        unfold PropSemantics.tyenvToProp
        simp[PropSemantics.predToProp]
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
    (Ty.func "x" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ty.func "y" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ty.func "inv" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
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

abbrev koalabear_word_range_checker_func: Ast.Expr :=
  (.lam "value_0" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_0").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
  (.lam "value_1" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_1").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
  (.lam "value_2" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_2").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
  (.lam "value_3" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_3").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
  (.lam "most_sig_byte_decomp_0" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_1" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "most_sig_byte_decomp_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
  (.lam "and_most_sig_byte_decomp_0_to_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (.letIn "b₀" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_0") .mul (.fieldExpr (.var "most_sig_byte_decomp_0") .sub (.constF 1))) (.constF 0))
    (.letIn "b₁" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_1") .mul (.fieldExpr (.var "most_sig_byte_decomp_1") .sub (.constF 1))) (.constF 0))
    (.letIn "b₂" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_2") .mul (.fieldExpr (.var "most_sig_byte_decomp_2") .sub (.constF 1))) (.constF 0))
    (.letIn "b₃" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_3") .mul (.fieldExpr (.var "most_sig_byte_decomp_3") .sub (.constF 1))) (.constF 0))
    (.letIn "b₄" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_4") .mul (.fieldExpr (.var "most_sig_byte_decomp_4") .sub (.constF 1))) (.constF 0))
    (.letIn "b₅" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_5") .mul (.fieldExpr (.var "most_sig_byte_decomp_5") .sub (.constF 1))) (.constF 0))
    (.letIn "b₆" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_6") .mul (.fieldExpr (.var "most_sig_byte_decomp_6") .sub (.constF 1))) (.constF 0))
    (.letIn "b₇" (.assertE (.fieldExpr (.var "most_sig_byte_decomp_7") .mul (.fieldExpr (.var "most_sig_byte_decomp_7") .sub (.constF 1))) (.constF 0))
    (.letIn "u₁"
      (.assertE (bits_to_byte_expr "most_sig_byte_decomp_0" "most_sig_byte_decomp_1" "most_sig_byte_decomp_2" "most_sig_byte_decomp_3"
                                  "most_sig_byte_decomp_4" "most_sig_byte_decomp_5" "most_sig_byte_decomp_6" "most_sig_byte_decomp_7")
        (.var "value_3")
      )
      (.letIn "u₂" (.assertE (.var "most_sig_byte_decomp_7") (.constF 0))
      (.letIn "u₃" (.assertE (.var "and_most_sig_byte_decomp_0_to_2") (.fieldExpr (.var "most_sig_byte_decomp_0") .mul (.var "most_sig_byte_decomp_1")))
      (.letIn "u₄" (.assertE (.var "and_most_sig_byte_decomp_0_to_3") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_2") .mul (.var "most_sig_byte_decomp_2")))
      (.letIn "u₅" (.assertE (.var "and_most_sig_byte_decomp_0_to_4") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_3") .mul (.var "most_sig_byte_decomp_3")))
      (.letIn "u₆" (.assertE (.var "and_most_sig_byte_decomp_0_to_5") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_4") .mul (.var "most_sig_byte_decomp_4")))
      (.letIn "u₇" (.assertE (.var "and_most_sig_byte_decomp_0_to_6") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_5") .mul (.var "most_sig_byte_decomp_5")))
      (.letIn "u₈" (.assertE (.var "and_most_sig_byte_decomp_0_to_7") (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_6") .mul (.var "most_sig_byte_decomp_6")))
      (.letIn "u₉" (.assertE (.constF 0) (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_7") .mul (.var "value_0")))
      (.letIn "u₁₀" (.assertE (.constF 0) (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_7") .mul (.var "value_1")))
      (.letIn "u₁₁" (.assertE (.constF 0) (.fieldExpr (.var "and_most_sig_byte_decomp_0_to_7") .mul (.var "value_2")))
        (.var "u₁₁"))))))))))))))))))))))))))))))))))))))

lemma koalabear_word_range_checker_subtype_soundness {Γ Δ}
  (hb₁: Env.lookupTy Γ "b₀" = some (bit_value_type "most_sig_byte_decomp_0"))
  (hb₂ : Env.lookupTy Γ "b₁" = some (bit_value_type "most_sig_byte_decomp_1"))
  (hb₃: Env.lookupTy Γ "b₂" = some (bit_value_type "most_sig_byte_decomp_2"))
  (hb₄ : Env.lookupTy Γ "b₃" = some (bit_value_type "most_sig_byte_decomp_3"))
  (hb₅: Env.lookupTy Γ "b₄" = some (bit_value_type "most_sig_byte_decomp_4"))
  (hb₆ : Env.lookupTy Γ "b₅" = some (bit_value_type "most_sig_byte_decomp_5"))
  (hb₇: Env.lookupTy Γ "b₆" = some (bit_value_type "most_sig_byte_decomp_6"))
  (hb₈ : Env.lookupTy Γ "b₇" = some (bit_value_type "most_sig_byte_decomp_7"))
  (hu₁: Env.lookupTy Γ "u₁" = some (Ast.Ty.unit.refin
                                  (Ast.Predicate.ind
                                    (Ast.exprEq
                                      (bits_to_byte_expr "most_sig_byte_decomp_0" "most_sig_byte_decomp_1" "most_sig_byte_decomp_2" "most_sig_byte_decomp_3"
                                                        "most_sig_byte_decomp_4" "most_sig_byte_decomp_5" "most_sig_byte_decomp_6" "most_sig_byte_decomp_7")
                                      (Ast.Expr.var "value_3")))))
  (hu₂: Env.lookupTy Γ "u₂" = some                               (Ast.Ty.unit.refin
                                (Ast.Predicate.ind
                                  (Ast.exprEq (Ast.Expr.var "most_sig_byte_decomp_7") (Ast.Expr.constF 0)))))
  (hu₃: Env.lookupTy Γ "u₃" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_2" "most_sig_byte_decomp_0" "most_sig_byte_decomp_1"))
  (hu₄: Env.lookupTy Γ "u₄" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_3" "and_most_sig_byte_decomp_0_to_2" "most_sig_byte_decomp_2"))
  (hu₅: Env.lookupTy Γ "u₅" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_4" "and_most_sig_byte_decomp_0_to_3" "most_sig_byte_decomp_3"))
  (hu₆: Env.lookupTy Γ "u₆" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_5" "and_most_sig_byte_decomp_0_to_4" "most_sig_byte_decomp_4"))
  (hu₇: Env.lookupTy Γ "u₇" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_6" "and_most_sig_byte_decomp_0_to_5" "most_sig_byte_decomp_5"))
  (hu₈: Env.lookupTy Γ "u₈" = some (eq_mul_refinement "and_most_sig_byte_decomp_0_to_7" "and_most_sig_byte_decomp_0_to_6" "most_sig_byte_decomp_6"))
  (hu₉: Env.lookupTy Γ "u₉" = some                           (Ast.Ty.unit.refin
                  (Ast.Predicate.ind
                    (Ast.exprEq (Ast.Expr.constF 0)
                      ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                        (Ast.Expr.var "value_0"))))))
  (hu₁₀: Env.lookupTy Γ "u₁₀" = some                           (Ast.Ty.unit.refin
                (Ast.Predicate.ind
                  (Ast.exprEq (Ast.Expr.constF 0)
                    ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                      (Ast.Expr.var "value_1"))))))
  (hu₁₁: Env.lookupTy Γ "u₁₁" = some                           (Ast.Ty.unit.refin
                (Ast.Predicate.ind
                  (Ast.exprEq (Ast.Expr.constF 0)
                    ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                      (Ast.Expr.var "value_2"))))))
  ( hl₀: Env.lookupTy Γ "value_0" = some (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_0").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))))
  ( hl₁: Env.lookupTy Γ "value_1" = some (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_1").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))))
  ( hl₂: Env.lookupTy Γ "value_2" = some (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_2").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))))
  ( hl₃: Env.lookupTy Γ "value_3" = some (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_3").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))))
  : @Ty.SubtypeJudgment Δ Γ
      (Ty.unit.refin (Predicate.ind (exprEq (Expr.constF 0) ((Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr FieldOp.mul (Expr.var "value_2")))))
      (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
              (.binRel (.integerExpr (.integerExpr (.integerExpr
                (.toZ (.var "value_0")) .add (.integerExpr (.toZ (.var "value_1")) .mul (.constZ 256)))
                                        .add (.integerExpr (.toZ (.var "value_2")) .mul (.constZ (256^2))))
                                        .add (.integerExpr (.toZ (.var "value_3")) .mul (.constZ (256^3))))
              .lt (.constZ 2130706433)))) := by {
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ v h₁ h₂

    have hb₁' := tyenv_to_eval_expr h₁ hb₁
    have hb₂' := tyenv_to_eval_expr h₁ hb₂
    have hb₃' := tyenv_to_eval_expr h₁ hb₃
    have hb₄' := tyenv_to_eval_expr h₁ hb₄
    have hb₅' := tyenv_to_eval_expr h₁ hb₅
    have hb₆' := tyenv_to_eval_expr h₁ hb₆
    have hb₇' := tyenv_to_eval_expr h₁ hb₇
    have hb₈' := tyenv_to_eval_expr h₁ hb₈
    have hu₁' := tyenv_to_eval_expr h₁ hu₁
    have hu₂' := tyenv_to_eval_expr h₁ hu₂
    have hu₃' := tyenv_to_eval_expr h₁ hu₃
    have hu₄' := tyenv_to_eval_expr h₁ hu₄
    have hu₅' := tyenv_to_eval_expr h₁ hu₅
    have hu₆' := tyenv_to_eval_expr h₁ hu₆
    have hu₇' := tyenv_to_eval_expr h₁ hu₇
    have hu₈' := tyenv_to_eval_expr h₁ hu₈
    have hu₉' := tyenv_to_eval_expr h₁ hu₉
    have hu₁₀' := tyenv_to_eval_expr h₁ hu₁₀
    have hu₁₁' := tyenv_to_eval_expr h₁ hu₁₁
    have hl₀' := tyenv_to_eval_expr h₁ hl₀
    have hl₁' := tyenv_to_eval_expr h₁ hl₁
    have hl₂' := tyenv_to_eval_expr h₁ hl₂
    have hl₃' := tyenv_to_eval_expr h₁ hl₃

    have hb₁'' := eval_bit_expr_val hb₁'
    have hb₂'' := eval_bit_expr_val hb₂'
    have hb₃'' := eval_bit_expr_val hb₃'
    have hb₄'' := eval_bit_expr_val hb₄'
    have hb₅'' := eval_bit_expr_val hb₅'
    have hb₆'' := eval_bit_expr_val hb₆'
    have hb₇'' := eval_bit_expr_val hb₇'
    have hb₈'' := eval_bit_expr_val hb₈'
    have hu₁' := eval_bits_to_byte_expr_val hu₁'
    have hu₃'' := eval_mul_expr_val hu₃'
    have hu₄'' := eval_mul_expr_val hu₄'
    have hu₅'' := eval_mul_expr_val hu₅'
    have hu₆'' := eval_mul_expr_val hu₆'
    have hu₇'' := eval_mul_expr_val hu₇'
    have hu₈'' := eval_mul_expr_val hu₈'
    have hu₉'' := eval_eq_const_mul_val hu₉'
    have hu₁₀'' := eval_eq_const_mul_val hu₁₀'
    have hu₁₁'' := eval_eq_const_mul_val hu₁₁'

    have hvl₀ := eval_lt_val hl₀'
    have hvl₁ := eval_lt_val hl₁'
    have hvl₂ := eval_lt_val hl₂'
    have hvl₃ := eval_lt_val hl₃'

    cases hu₂'
    rename_i v₁ u₁ ih₁ ih₂ h_most_sig_byte_decomp_7_is_0
    cases ih₁
    cases ih₂
    simp [Eval.evalRelOp] at h_most_sig_byte_decomp_7_is_0
    cases v₁ <;> simp at h_most_sig_byte_decomp_7_is_0
    rename_i most_sig_byte_decomp_7 h_most_sig_byte_decomp_7_env

    unfold PropSemantics.predToProp PropSemantics.exprToProp
    obtain ⟨most_sig_byte_decomp_0, h⟩ := hb₁''
    obtain ⟨h_most_sig_byte_decomp_0_env, h_most_sig_byte_decomp_0⟩ := h
    obtain ⟨most_sig_byte_decomp_1, h⟩ := hb₂''
    obtain ⟨h_most_sig_byte_decomp_1_env, h_most_sig_byte_decomp_1⟩ := h
    obtain ⟨most_sig_byte_decomp_2, h⟩ := hb₃''
    obtain ⟨h_most_sig_byte_decomp_2_env, h_most_sig_byte_decomp_2⟩ := h
    obtain ⟨most_sig_byte_decomp_3, h⟩ := hb₄''
    obtain ⟨h_most_sig_byte_decomp_3_env, h_most_sig_byte_decomp_3⟩ := h
    obtain ⟨most_sig_byte_decomp_4, h⟩ := hb₅''
    obtain ⟨h_most_sig_byte_decomp_4_env, h_most_sig_byte_decomp_4⟩ := h
    obtain ⟨most_sig_byte_decomp_5, h⟩ := hb₆''
    obtain ⟨h_most_sig_byte_decomp_5_env, h_most_sig_byte_decomp_5⟩ := h
    obtain ⟨most_sig_byte_decomp_6, h⟩ := hb₇''
    obtain ⟨h_most_sig_byte_decomp_6_env, h_most_sig_byte_decomp_6⟩ := h
    obtain ⟨most_sig_byte_decomp_7', h⟩ := hb₈''
    obtain ⟨h_most_sig_byte_decomp_7_env', h_most_sig_byte_decomp_7⟩ := h
    rw[h_most_sig_byte_decomp_7_env] at h_most_sig_byte_decomp_7_env'
    simp at h_most_sig_byte_decomp_7_env'
    rw[← h_most_sig_byte_decomp_7_env'] at h_most_sig_byte_decomp_7

    obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇, value_3, h⟩ := hu₁'
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h_value_3_env, h_msb_rec⟩ := h
    simp at h_most_sig_byte_decomp_0_env h_most_sig_byte_decomp_1_env
            h_most_sig_byte_decomp_2_env h_most_sig_byte_decomp_3_env
            h_most_sig_byte_decomp_4_env h_most_sig_byte_decomp_5_env
            h_most_sig_byte_decomp_6_env h_most_sig_byte_decomp_7_env
    rw[h_most_sig_byte_decomp_0_env] at h₁
    rw[h_most_sig_byte_decomp_1_env] at h₂
    rw[h_most_sig_byte_decomp_2_env] at h₃
    rw[h_most_sig_byte_decomp_3_env] at h₄
    rw[h_most_sig_byte_decomp_4_env] at h₅
    rw[h_most_sig_byte_decomp_5_env] at h₆
    rw[h_most_sig_byte_decomp_6_env] at h₇
    rw[h_most_sig_byte_decomp_7_env] at h₈
    simp at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h_value_3_env
    rw[← h₁, ← h₂, ← h₃, ← h₄, ← h₅, ← h₆, ← h₇, ← h₈] at h_msb_rec

    obtain ⟨and_most_sig_byte_decomp_0_to_2, v₂, v₃, h⟩ := hu₃''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_2_env, h₂, h₃, hamm₁⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_2_env h₂ h₃ hamm₁
    rw[h_most_sig_byte_decomp_0_env] at h₂
    rw[h_most_sig_byte_decomp_1_env] at h₃
    simp at h₂ h₃ hamm₁
    rw[← h₂, ← h₃] at hamm₁


    obtain ⟨and_most_sig_byte_decomp_0_to_3, v₂, v₃, h⟩ := hu₄''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_3_env, h₂, h₃, hamm₂⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_3_env h₂ h₃ hamm₂
    rw[h_and_most_sig_byte_decomp_0_to_2_env] at h₂
    rw[h_most_sig_byte_decomp_2_env] at h₃
    simp at h₂ h₃ hamm₂
    rw[← h₂, ← h₃] at hamm₂

    obtain ⟨and_most_sig_byte_decomp_0_to_4, v₂, v₃, h⟩ := hu₅''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_4_env, h₂, h₃, hamm₃⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_4_env h₂ h₃ hamm₃
    rw[h_and_most_sig_byte_decomp_0_to_3_env] at h₂
    rw[h_most_sig_byte_decomp_3_env] at h₃
    simp at h₂ h₃ hamm₃
    rw[← h₂, ← h₃] at hamm₃

    obtain ⟨and_most_sig_byte_decomp_0_to_5, v₂, v₃, h⟩ := hu₆''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_5_env, h₂, h₃, hamm₄⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_5_env h₂ h₃ hamm₄
    rw[h_and_most_sig_byte_decomp_0_to_4_env] at h₂
    rw[h_most_sig_byte_decomp_4_env] at h₃
    simp at h₂ h₃ hamm₄
    rw[← h₂, ← h₃] at hamm₄

    obtain ⟨and_most_sig_byte_decomp_0_to_6, v₂, v₃, h⟩ := hu₇''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_6_env, h₂, h₃, hamm₅⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_6_env h₂ h₃ hamm₅
    rw[h_and_most_sig_byte_decomp_0_to_5_env] at h₂
    rw[h_most_sig_byte_decomp_5_env] at h₃
    simp at h₂ h₃ hamm₅
    rw[← h₂, ← h₃] at hamm₅

    obtain ⟨and_most_sig_byte_decomp_0_to_7, v₂, v₃, h⟩ := hu₈''
    obtain ⟨h_and_most_sig_byte_decomp_0_to_7_env, h₂, h₃, hamm₆⟩ := h
    simp at h_and_most_sig_byte_decomp_0_to_7_env h₂ h₃ hamm₆
    rw[h_and_most_sig_byte_decomp_0_to_6_env] at h₂
    rw[h_most_sig_byte_decomp_6_env] at h₃
    simp at h₂ h₃ hamm₆
    rw[← h₂, ← h₃] at hamm₆

    obtain ⟨v₁, value_0, h⟩ := hu₉''
    obtain ⟨h₁, h_value_0_env, hav₀⟩ := h
    simp at h₁ h_value_0_env hav₀
    rw[h_and_most_sig_byte_decomp_0_to_7_env] at h₁
    simp at h₁
    rw[← h₁] at hav₀


    obtain ⟨v₁, value_1, h⟩ := hu₁₀''
    obtain ⟨h₁, h_value_1_env, hav₁⟩ := h
    simp at h₁ h_value_1_env hav₁
    rw[h_and_most_sig_byte_decomp_0_to_7_env] at h₁
    simp at h₁
    rw[← h₁] at hav₁

    obtain ⟨v₁, value_2, h⟩ := hu₁₁''
    obtain ⟨h₁, h_value_2_env, hav₂⟩ := h
    simp at h₁ h_value_2_env hav₂
    rw[h_and_most_sig_byte_decomp_0_to_7_env] at h₁
    simp at h₁
    rw[← h₁] at hav₂

    obtain ⟨v₁, h₁, hvl₀⟩ := hvl₀
    simp at h₁
    rw[h_value_0_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₀

    obtain ⟨v₁, h₁, hvl₁⟩ := hvl₁
    simp at h₁
    rw[h_value_1_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₁

    obtain ⟨v₁, h₁, hvl₂⟩ := hvl₂
    simp at h₁
    rw[h_value_2_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₂

    obtain ⟨v₁, h₁, hvl₃⟩ := hvl₃
    simp at h₁
    rw[h_value_3_env] at h₁
    simp at h₁
    rw[← h₁] at hvl₃

    repeat
      repeat constructor
      assumption
    repeat constructor
    simp

    apply word32_range_under_koalabear
      (bit_value_mul_zero h_most_sig_byte_decomp_0) (bit_value_mul_zero h_most_sig_byte_decomp_1)
      (bit_value_mul_zero h_most_sig_byte_decomp_2) (bit_value_mul_zero h_most_sig_byte_decomp_3)
      (bit_value_mul_zero h_most_sig_byte_decomp_4) (bit_value_mul_zero h_most_sig_byte_decomp_5)
      (bit_value_mul_zero h_most_sig_byte_decomp_6) (bit_value_mul_zero h_most_sig_byte_decomp_7)
      h_msb_rec h_most_sig_byte_decomp_7_is_0 hamm₁ hamm₂ hamm₃ hamm₄ hamm₅ hamm₆
    simp
    exact hav₀
    simp
    exact hav₁
    simp
    repeat assumption
}

lemma koalabear_word_range_checker_func_typing_soundness (Δ: Env.ChipEnv) (Η: Env.UsedNames) (Γ: Env.TyEnv) :
  @Ty.TypeJudgment Δ Γ Η koalabear_word_range_checker_func
    (Ast.Ty.func "value_0" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_0").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
    (Ast.Ty.func "value_1" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_1").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
    (Ast.Ty.func "value_2" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_2").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
    (Ast.Ty.func "value_3" (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.ind ((Ast.Expr.var "value_3").toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256))))
    (Ast.Ty.func "most_sig_byte_decomp_0" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_1" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "most_sig_byte_decomp_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_2" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_3" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_4" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_5" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_6" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
    (Ast.Ty.func "and_most_sig_byte_decomp_0_to_7" (Ast.Ty.refin Ast.Ty.field Ast.constTruePred)
      (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
        (.binRel (.integerExpr (.integerExpr (.integerExpr
          (.toZ (.var "value_0")) .add (.integerExpr (.toZ (.var "value_1")) .mul (.constZ 256)))
                                  .add (.integerExpr (.toZ (.var "value_2")) .mul (.constZ (256^2))))
                                  .add (.integerExpr (.toZ (.var "value_3")) .mul (.constZ (256^3))))
        .lt (.constZ 2130706433)))))))))))))))))))))) := by {
  repeat
    apply Ty.TypeJudgment.TE_Abs
    apply lookup_update_self
  repeat
    apply Ty.TypeJudgment.TE_LetIn;
    apply lookup_update_self;
    apply Ty.TypeJudgment.TE_Assert
    apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    repeat apply Ty.TypeJudgment.TE_ConstF

  apply Ty.TypeJudgment.TE_LetIn;
  apply lookup_update_self;
  apply Ty.TypeJudgment.TE_Assert
  repeat apply Ty.TypeJudgment.TE_BinOpField
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  repeat
    apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    repeat apply Ty.TypeJudgment.TE_ConstF
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp

  apply Ty.TypeJudgment.TE_LetIn;
  apply lookup_update_self;
  apply Ty.TypeJudgment.TE_Assert
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  apply Ty.TypeJudgment.TE_ConstF

  repeat
    apply Ty.TypeJudgment.TE_LetIn;
    apply lookup_update_self;
    apply Ty.TypeJudgment.TE_Assert
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    apply Ty.TypeJudgment.TE_BinOpField
    repeat
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp

  repeat
    apply Ty.TypeJudgment.TE_LetIn;
    apply lookup_update_self;
    apply Ty.TypeJudgment.TE_Assert
    apply Ty.TypeJudgment.TE_ConstF
    apply Ty.TypeJudgment.TE_BinOpField
    repeat
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp

  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self
  apply koalabear_word_range_checker_subtype_soundness
  repeat
    apply lookup_update_ne
    simp
  apply lookup_update_self
  repeat
    apply lookup_update_ne
    simp
}
