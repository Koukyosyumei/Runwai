import Runwai.Typing
import Runwai.Gadget
--import Runwai.PP
import Runwai.Tactic

import Lean.Parser.Tactic

open Lean Elab Tactic


@[simp]
def assertChip : Ast.Chip := {
  name    := "assert",
  ident_t := "trace",
  ident_i := "i",
  width   := 2,
  goal    := Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.ind
      (Ast.Expr.binRel (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                       Ast.RelOp.eq (Ast.Expr.constF 2))),
  body    := (Ast.Expr.letIn "u" (Ast.Expr.assertE
              (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
              (Ast.Expr.constF 2))
            (Ast.Expr.var "u"))
}

@[simp]
def iszeroChip : Ast.Chip := {
  name    := "iszero",
  ident_t := "trace",
  ident_i := "i",
  width   := 3,
  goal    := Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.ind
      (Ast.exprEq (.var "y") (.branch (.binRel (.var "x") (.eq) (.constF 0)) (.constF 1) (.constF 0))))
  body    := (Ast.Expr.letIn "x" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
              (Ast.Expr.letIn "y" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                (Ast.Expr.letIn "inv" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 2))
                  (Ast.Expr.letIn "u₁" (.assertE (.var "y") (.fieldExpr (.fieldExpr (.fieldExpr (.constF 0) .sub (.var "x")) .mul (.var "inv")) (.add) (.constF 1)))
                    (Ast.Expr.letIn "u₂" (.assertE (.fieldExpr (.var "x") .mul (.var "y")) (.constF 0)) (.var "u₂")))
                )
              )
            )
}

@[simp]
def u8chip : Ast.Chip := {
  name := "u8",
  ident_t := "trace",
  ident_i := "i"
  width := 1,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.Expr.binRel (Ast.Expr.toZ (Ast.trace_i_j "trace" "i" 0)) Ast.RelOp.lt (Ast.Expr.constZ 256))),
  body := Ast.Expr.assertE (Ast.Expr.constF 0) (Ast.Expr.constF 0)
}

@[simp]
def wordRangeCheckerChip : Ast.Chip := {
  name := "word_range_checker",
  ident_t := "trace",
  ident_i := "i",
  width := 18,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
    (.binRel (.integerExpr (.integerExpr (.integerExpr (.toZ (.var "value_0")) .add ((.integerExpr (.toZ (.var "value_1")) .mul (.constZ 256)))) .add ((.integerExpr (.toZ (.var "value_2")) .mul (.constZ (256^2))))) .add (.integerExpr (.toZ (.var "value_3")) .mul (.constZ (256^3))))
      .lt (.constZ 2130706433)))
  body := (.letIn "value_0" (Ast.trace_i_j "trace" "i" 0)
          (.letIn "value_1" (Ast.trace_i_j "trace" "i" 1)
          (.letIn "value_2" (Ast.trace_i_j "trace" "i" 2)
          (.letIn "value_3" (Ast.trace_i_j "trace" "i" 3)
          (.letIn "most_sig_byte_decomp_0" (Ast.trace_i_j "trace" "i" 4)
          (.letIn "most_sig_byte_decomp_1" (Ast.trace_i_j "trace" "i" 5)
          (.letIn "most_sig_byte_decomp_2" (Ast.trace_i_j "trace" "i" 6)
          (.letIn "most_sig_byte_decomp_3" (Ast.trace_i_j "trace" "i" 7)
          (.letIn "most_sig_byte_decomp_4" (Ast.trace_i_j "trace" "i" 8)
          (.letIn "most_sig_byte_decomp_5" (Ast.trace_i_j "trace" "i" 9)
          (.letIn "most_sig_byte_decomp_6" (Ast.trace_i_j "trace" "i" 10)
          (.letIn "most_sig_byte_decomp_7" (Ast.trace_i_j "trace" "i" 11)
          (.letIn "and_most_sig_byte_decomp_0_to_2" (Ast.trace_i_j "trace" "i" 12)
          (.letIn "and_most_sig_byte_decomp_0_to_3" (Ast.trace_i_j "trace" "i" 13)
          (.letIn "and_most_sig_byte_decomp_0_to_4" (Ast.trace_i_j "trace" "i" 14)
          (.letIn "and_most_sig_byte_decomp_0_to_5" (Ast.trace_i_j "trace" "i" 15)
          (.letIn "and_most_sig_byte_decomp_0_to_6" (Ast.trace_i_j "trace" "i" 16)
          (.letIn "and_most_sig_byte_decomp_0_to_7" (Ast.trace_i_j "trace" "i" 17)
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
            (.lookup "l₀" "u8" [(.var "value_0", (Ast.trace_i_j "trace" "i" 0))]
            (.lookup "l₁" "u8" [(.var "value_1", (Ast.trace_i_j "trace" "i" 0))]
            (.lookup "l₂" "u8" [(.var "value_2", (Ast.trace_i_j "trace" "i" 0))]
            (.lookup "l₃" "u8" [(.var "value_3", (Ast.trace_i_j "trace" "i" 0))]
             (.var "l₃"))))))))))))))))))))))))))))))))))))))))))
}

def Δ : Env.ChipEnv := [("assert", assertChip), ("u8", u8chip)]

theorem assertChip_correct : Ty.ChipCorrect Δ assertChip 1 := by
  unfold Ty.ChipCorrect
  intro x i hs hi hrow ht hσ
  let envs := Ty.makeEnvs assertChip (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
  · apply Ty.TypeJudgment.TE_Assert
    · apply Ty.TypeJudgment.TE_ArrayIndex; apply Ty.TypeJudgment.TE_ArrayIndex; apply Ty.TypeJudgment.TE_Var
      apply lookup_update_ne
      simp
      apply Eval.EvalProp.Var; exact rfl
      simp
      exact hi
      apply Eval.EvalProp.ConstZ
      simp
    . apply Ty.TypeJudgment.TE_ConstF
  . constructor;
    apply lookup_update_self

theorem iszeroChip_correct : Ty.ChipCorrect Δ iszeroChip 1 := by
  unfold Ty.ChipCorrect
  intro x i height hs hi hrow ht
  let envs := Ty.makeEnvs iszeroChip (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  repeat
    apply Ty.TypeJudgment.TE_LetIn;
    · apply lookup_update_self;
    · auto_judgment;
  apply isZero_typing_soundness
  repeat apply lookup_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self;
  repeat decide

theorem iszeroChip_correct_long : Ty.ChipCorrect Δ iszeroChip 1 := by
  unfold Ty.ChipCorrect
  intro x i height hs hi hrow ht
  let envs := Ty.makeEnvs iszeroChip (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  unfold iszeroChip; simp
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
  · apply Ty.TypeJudgment.TE_ArrayIndex
    apply Ty.TypeJudgment.TE_ArrayIndex
    apply Ty.TypeJudgment.TE_Var
    apply lookup_update_ne
    simp
    apply Eval.EvalProp.Var
    unfold Env.lookupVal
    unfold Env.updateVal
    simp
    rfl
    simp
    exact hs
    apply Eval.EvalProp.ConstZ
    simp
  . apply Ty.TypeJudgment.TE_LetIn
    . apply lookup_update_self
    · apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_Var
      apply lookup_update_ne
      simp
      apply Eval.EvalProp.Var
      unfold Env.lookupVal
      unfold Env.updateVal
      simp
      rfl
      simp
      exact hs
      apply Eval.EvalProp.ConstZ
      simp
    . apply Ty.TypeJudgment.TE_LetIn
      . apply lookup_update_self
      · apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_Var
        apply lookup_update_ne
        simp
        apply Eval.EvalProp.Var
        unfold Env.lookupVal
        unfold Env.updateVal
        simp
        rfl
        simp
        exact hs
        apply Eval.EvalProp.ConstZ
        simp
      . apply isZero_typing_soundness
        apply lookup_update_ne; simp
        apply lookup_update_ne; simp
        apply Ty.TypeJudgment.TE_VarEnv
        apply lookup_update_self
        decide
        decide
        decide

lemma lookup_u8_val_lt_256
  (h₁: PropSemantics.tyenvToProp σ Δ Γ)
  (h₂: Env.lookupTy Γ u = some ((Ast.Ty.unit.refin
          (Ty.lookup_pred [(Ast.Expr.var x, Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
            (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
            Η))))
  (h₃: (Env.freshName Η (Env.lookupChip Δ "u8").ident_i) = new_ident_i)
  (h₄: (Env.freshName Η (Env.lookupChip Δ "u8").ident_t) = new_ident_t)
  (h₇: new_ident_t ≠ "i") :  ∃ v : F, Env.lookupVal σ x = some (Ast.Value.vF v) ∧ v.val < 256 := by {
    unfold Ty.lookup_pred at h₂
    have hu8_i : (Env.lookupChip Δ "u8").ident_i = "i" := by {
      unfold Env.lookupChip Δ
      simp
    }
    have hu8_t : (Env.lookupChip Δ "u8").ident_t = "trace" := by {
      unfold Env.lookupChip Δ
      simp
    }

    rw[h₃, h₄, hu8_i, hu8_t] at h₂
    unfold Ast.renameVarinPred Ast.renameVar at h₂
    simp at h₂
    unfold Ast.renameVarinPred Ast.renameVar at h₂
    simp at h₂
    unfold Ast.renameVar at h₂
    simp at h₂
    unfold Ast.renameVar at h₂
    simp at h₂
    unfold Ast.renameVar at h₂
    simp at h₂
    unfold Ast.renameVar at h₂
    simp at h₂
    rw [if_neg h₇] at h₂
    have hl₀' := tyenv_and_to_eval_exprs h₁ h₂

    obtain ⟨hl₀₁',hl₀₂'⟩ := hl₀'
    have hvl₀ := eval_eq_then_lt hl₀₂' hl₀₁'
    have hvl₀' := eval_lt_val hvl₀
    exact hvl₀'
  }

lemma subtype_wordRange
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
  ( hl₀ : Env.lookupTy Γ "l₀" = some ((Ast.Ty.unit.refin
            (Ty.lookup_pred [(Ast.Expr.var "value_0", Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
              (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t]))))
  ( hl₁: Env.lookupTy Γ "l₁" = some (        (Ast.Ty.unit.refin
          (Ty.lookup_pred [(Ast.Expr.var "value_1", Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
            (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
            (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t])))))
  ( hl₂: Env.lookupTy Γ "l₂" =       (Ast.Ty.unit.refin
        (Ty.lookup_pred [(Ast.Expr.var "value_2", Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
          (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
          (Ty.update_UsedNames (Env.lookupChip Δ "u8")
            (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t])))))
  ( hl₃: Env.lookupTy Γ "l₃" = (Ast.Ty.unit.refin
      (Ty.lookup_pred [(Ast.Expr.var "value_3", Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
        (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
        (Ty.update_UsedNames (Env.lookupChip Δ "u8")
          (Ty.update_UsedNames (Env.lookupChip Δ "u8")
            (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t]))))))
  : @Ty.SubtypeJudgment σ Δ Γ (Ast.Ty.unit.refin
      (Ty.lookup_pred [(Ast.Expr.var "value_3", Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
        (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
        (Ty.update_UsedNames (Env.lookupChip Δ "u8")
          (Ty.update_UsedNames (Env.lookupChip Δ "u8")
            (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t]))))) wordRangeCheckerChip.goal := by {
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro v h₁ h₂

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

    cases hu₂'
    rename_i v₁ u₁ ih₁ ih₂ h_most_sig_byte_decomp_7_is_0
    cases ih₁
    cases ih₂
    unfold Eval.evalRelOp at h_most_sig_byte_decomp_7_is_0
    cases v₁ <;> simp at h_most_sig_byte_decomp_7_is_0
    rename_i most_sig_byte_decomp_7 h_most_sig_byte_decomp_7_env

    have hu8_i : (Env.lookupChip Δ "u8").ident_i = "i" := by {
      unfold Env.lookupChip Δ
      simp
    }
    have hu8_t : (Env.lookupChip Δ "u8").ident_t = "trace" := by {
      unfold Env.lookupChip Δ
      simp
    }
    have h₁' : (Env.freshName [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t] (Env.lookupChip Δ "u8").ident_t) = "trace'" := by {
      unfold Env.freshName
      rw[hu8_t]
      simp
    }
    have h₂' : (Env.freshName [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t] (Env.lookupChip Δ "u8").ident_i) = "i'" := by {
      unfold Env.freshName
      rw[hu8_i]
      simp
    }
    have h₃' : "trace'" ≠ "i" := by simp
    have hl₀' := tyenv_and_to_eval_exprs h₁ hl₀
    have hvl₀ := lookup_u8_val_lt_256 h₁ hl₀ h₂' h₁' h₃'
    have h₁' : (Env.freshName (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t]) (Env.lookupChip Δ "u8").ident_t) = "trace'" := by {
      unfold Env.freshName
      rw[hu8_t]
      simp
      unfold Ty.update_UsedNames
      simp
    }
    have h₂' : (Env.freshName (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t]) (Env.lookupChip Δ "u8").ident_i) = "i'" := by {
      unfold Env.freshName
      rw[hu8_i]
      simp
      unfold Ty.update_UsedNames
      simp
    }
    have hl₁' := tyenv_and_to_eval_exprs h₁ hl₁
    have hvl₁ := lookup_u8_val_lt_256 h₁ hl₁ h₂' h₁' h₃'
    have h₁' : (Env.freshName (Ty.update_UsedNames (Env.lookupChip Δ "u8")
          (Ty.update_UsedNames (Env.lookupChip Δ "u8")
            (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t]))) (Env.lookupChip Δ "u8").ident_t) = "trace'" := by {
      unfold Env.freshName
      rw[hu8_t]
      simp
      unfold Ty.update_UsedNames
      simp
    }
    have h₂' : (Env.freshName (Ty.update_UsedNames (Env.lookupChip Δ "u8")
          (Ty.update_UsedNames (Env.lookupChip Δ "u8")
            (Ty.update_UsedNames (Env.lookupChip Δ "u8")
              [wordRangeCheckerChip.ident_i, wordRangeCheckerChip.ident_t]))) (Env.lookupChip Δ "u8").ident_i) = "i'" := by {
      unfold Env.freshName
      rw[hu8_i]
      simp
      unfold Ty.update_UsedNames
      simp
    }
    have hl₂' := tyenv_and_to_eval_exprs h₁ hl₂
    have hvl₂ := lookup_u8_val_lt_256 h₁ hl₂ h₂' h₁' h₃'
    have hl₃' := tyenv_and_to_eval_exprs h₁ hl₃
    have hvl₃ := lookup_u8_val_lt_256 h₁ hl₃ h₂' h₁' h₃'

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

    apply Eval.EvalProp.Rel
    . apply Eval.EvalProp.ZBinOp
      . apply Eval.EvalProp.ZBinOp
        apply Eval.EvalProp.ZBinOp
        . apply Eval.EvalProp.toZ
          apply Eval.EvalProp.Var h_value_0_env
        . apply Eval.EvalProp.ZBinOp
          . apply Eval.EvalProp.toZ
            apply Eval.EvalProp.Var h_value_1_env
          . apply Eval.EvalProp.ConstZ
          . unfold Eval.evalIntegerOp
            simp
            rfl
        . unfold Eval.evalIntegerOp
          simp
          rfl
        . apply Eval.EvalProp.ZBinOp
          . apply Eval.EvalProp.toZ
            apply Eval.EvalProp.Var h_value_2_env
          . apply Eval.EvalProp.ConstZ
          . unfold Eval.evalIntegerOp
            simp
            rfl
        . unfold Eval.evalIntegerOp
          simp
          rfl
      . apply Eval.EvalProp.ZBinOp
        . apply Eval.EvalProp.toZ
          apply Eval.EvalProp.Var h_value_3_env
        . apply Eval.EvalProp.ConstZ
        . unfold Eval.evalIntegerOp
          simp
          rfl
      . unfold Eval.evalIntegerOp
        simp
        rfl
    . apply Eval.EvalProp.ConstZ
    . unfold Eval.evalRelOp
      simp
      apply word_range_val_bound
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
      exact hav₂
      exact hvl₀
      exact hvl₁
      exact hvl₂
      exact hvl₃
}


theorem wordRangeCheckerChip_correct : Ty.ChipCorrect Δ wordRangeCheckerChip 1 := by
  unfold Ty.ChipCorrect
  intro x i hs hi hrow ht hσ
  let envs := Ty.makeEnvs assertChip (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  repeat
    apply Ty.TypeJudgment.TE_LetIn;
    · apply lookup_update_self;
    · auto_judgment;
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self;
  . apply Ty.TypeJudgment.TE_Assert
    repeat apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    apply Ty.TypeJudgment.TE_BinOpField
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    repeat apply Ty.TypeJudgment.TE_ConstF
  . repeat
      apply Ty.TypeJudgment.TE_LetIn
      apply lookup_update_self
      apply Ty.TypeJudgment.TE_Assert
      repeat
        apply Ty.TypeJudgment.TE_BinOpField
        apply Ty.TypeJudgment.TE_VarEnv
        apply lookup_update_ne
        simp
      apply Ty.TypeJudgment.TE_ConstF
      apply Ty.TypeJudgment.TE_ConstF
    apply Ty.TypeJudgment.TE_LetIn
    apply lookup_update_self
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
      apply Ty.TypeJudgment.TE_ConstF
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    apply Ty.TypeJudgment.TE_LetIn
    apply lookup_update_self
    apply Ty.TypeJudgment.TE_Assert
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    apply Ty.TypeJudgment.TE_ConstF
    repeat
      apply Ty.TypeJudgment.TE_LetIn
      apply lookup_update_self
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
      apply Ty.TypeJudgment.TE_LetIn
      apply lookup_update_self
      apply Ty.TypeJudgment.TE_Assert Ty.TypeJudgment.TE_ConstF
      apply Ty.TypeJudgment.TE_BinOpField
      repeat
        apply Ty.TypeJudgment.TE_VarEnv
        apply lookup_update_ne
        simp
    repeat
      apply Ty.TypeJudgment.TE_LookUp
      rfl; rfl; rfl
    apply Ty.TypeJudgment.TE_SUB
    apply subtype_wordRange
    repeat
      apply lookup_update_ne
      simp
    apply lookup_update_self
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_self
