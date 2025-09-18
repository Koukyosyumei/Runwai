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
def iszeroChip2: Ast.Chip := {
  name    := "iszero2",
  ident_t := "trace",
  ident_i := "i",
  width   := 3,
  goal    := Ast.Ty.refin Ast.Ty.unit
    (Ast.Predicate.ind
      (Ast.exprEq (.var "β") (.branch (.binRel (.var "α") (.eq) (.constF 0)) (.constF 1) (.constF 0))))
  body    := (Ast.Expr.letIn "α" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 0))
              (Ast.Expr.letIn "β" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 1))
                (Ast.Expr.letIn "γ" (Ast.Expr.arrIdx (Ast.Expr.arrIdx (Ast.Expr.var "trace") (Ast.Expr.var "i")) (Ast.Expr.constZ 2))
                  (Ast.Expr.letIn "u₁" (.app (.app (.app iszero_func (.var "α")) (.var "β")) (.var "γ"))
                     (.var "u₁"))
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
def koalabearWordRangeCheckerChip : Ast.Chip := {
  name := "koalabear_word_range_checker",
  ident_t := "trace",
  ident_i := "i",
  width := 18,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind
    (.binRel (.integerExpr (.integerExpr (.integerExpr (.toZ (.var "alpha_0")) .add ((.integerExpr (.toZ (.var "alpha_1")) .mul (.constZ 256)))) .add ((.integerExpr (.toZ (.var "alpha_2")) .mul (.constZ (256^2))))) .add (.integerExpr (.toZ (.var "alpha_3")) .mul (.constZ (256^3))))
      .lt (.constZ 2130706433)))
  body := (.letIn "alpha_0" (Ast.trace_i_j "trace" "i" 0)
          (.letIn "alpha_1" (Ast.trace_i_j "trace" "i" 1)
          (.letIn "alpha_2" (Ast.trace_i_j "trace" "i" 2)
          (.letIn "alpha_3" (Ast.trace_i_j "trace" "i" 3)
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
          (.lookup "l₀" "u8" [(.var "alpha_0", (Ast.trace_i_j "trace" "i" 0))]
          (.lookup "l₁" "u8" [(.var "alpha_1", (Ast.trace_i_j "trace" "i" 0))]
          (.lookup "l₂" "u8" [(.var "alpha_2", (Ast.trace_i_j "trace" "i" 0))]
          (.lookup "l₃" "u8" [(.var "alpha_3", (Ast.trace_i_j "trace" "i" 0))]
          (.letIn "u₁"
            (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app
              koalabear_word_range_checker_func
                (.var "alpha_0")) (.var "alpha_1")) (.var "alpha_2")) (.var "alpha_3"))
                (.var "most_sig_byte_decomp_0")) (.var "most_sig_byte_decomp_1"))
                (.var "most_sig_byte_decomp_2")) (.var "most_sig_byte_decomp_3"))
                (.var "most_sig_byte_decomp_4")) (.var "most_sig_byte_decomp_5"))
                (.var "most_sig_byte_decomp_6")) (.var "most_sig_byte_decomp_7"))
                (.var "and_most_sig_byte_decomp_0_to_2")) (.var "and_most_sig_byte_decomp_0_to_3"))
                (.var "and_most_sig_byte_decomp_0_to_4")) (.var "and_most_sig_byte_decomp_0_to_5"))
                (.var "and_most_sig_byte_decomp_0_to_6")) (.var "and_most_sig_byte_decomp_0_to_7"))
            (.var "u₁"))))))))))))))))))))))))
}

def Δ : Env.ChipEnv := [("assert", assertChip), ("u8", u8chip)]

theorem assertChip_correct : Ty.chipCorrect Δ assertChip 1 := by
  unfold Ty.chipCorrect
  intro i hi Γ Η
  apply Ty.TypeJudgment.TE_LetIn
  · apply lookup_update_self
  · apply Ty.TypeJudgment.TE_Assert
    · apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_Var
      apply lookup_update_ne
      simp
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_self
      apply constZ_refine_lt
      simp
    . apply Ty.TypeJudgment.TE_ConstF
  . constructor;
    apply lookup_update_self

/-
syntax "auto_trace_index" : tactic
macro_rules
| `(tactic| auto_trace_index) => `(tactic|
    repeat
      apply Ty.TypeJudgment.TE_LetIn
      · apply lookup_update_self
      · apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_ArrayIndex
        apply Ty.TypeJudgment.TE_VarEnv
        simp
        apply lookup_update_ne
        simp
        apply Ty.TypeJudgment.TE_VarEnv
        try (apply lookup_update_self)
        try (apply lookup_update_ne)
        try (simp)
        apply constZ_refine_lt
        simp
  )
-/

theorem iszeroChip_correct : Ty.chipCorrect Δ iszeroChip 1 := by
  unfold Ty.chipCorrect
  intro i hi Γ Η
  auto_trace_index
  apply isZero_typing_soundness
  repeat apply lookup_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self;
  repeat decide

theorem iszeroChip2_correct : Ty.chipCorrect Δ iszeroChip2 1 := by
  unfold Ty.chipCorrect
  intro i hi Γ Η
  auto_trace_index
  apply Ty.TypeJudgment.TE_LetIn
  rfl
  apply Ty.TypeJudgment.TE_App
  apply Ty.TypeJudgment.TE_App
  apply Ty.TypeJudgment.TE_App
  apply iszero_func_typing_soundness
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne_of_lookup
  simp
  apply lookup_update_ne_of_lookup
  simp
  apply lookup_update_self
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne_of_lookup
  simp
  apply lookup_update_self
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self

lemma eval_var_lt_of_update
  (h₀: Eval.EvalProp σ T Δ v va)
  (h₁: Eval.EvalProp σ T Δ (v.toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ t)) (Ast.Value.vBool true)):
  Eval.EvalProp (Env.updateVal σ x va) T Δ ((Ast.Expr.var x).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ t))
  (Ast.Value.vBool true) := by {
    cases h₁
    rename_i ih₁ ih₂ r
    cases ih₁
    rename_i h
    cases va with
    | vF x => {
      have := evalprop_deterministic h h₀
      simp at this
      rw[this] at r
      cases ih₂
      apply Eval.EvalProp.Rel
      apply Eval.EvalProp.toZ
      apply Eval.EvalProp.Var
      simp [Env.lookupVal, Env.updateVal]
      rfl
      apply Eval.EvalProp.ConstZ
      exact r
    }
    | _ => {
      have := evalprop_deterministic h h₀
      simp at this
    }
  }

lemma u8_lookup_refines_lt256 (x u: String)
  (h₀: Env.lookupTy Γ x = Ast.Ty.refin Ast.Ty.field φ)
  (h₁: Env.lookupTy Γ u = some ((Ast.Ty.unit.refin
          (Ty.lookup_pred [(Ast.Expr.var x, Ast.trace_i_j "trace" "i" 0)] (Env.lookupChip Δ "u8")
            (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
            Η))))
  (h₂: (Env.freshName Η (Env.lookupChip Δ "u8").ident_i) = new_ident_i)
  (h₃: (Env.freshName Η (Env.lookupChip Δ "u8").ident_t) = new_ident_t)
  (h₄: new_ident_t ≠ "i")
  (h₅: x ≠ Ast.mu):
  @Ty.TypeJudgment Δ Γ Η (Ast.Expr.var x)
    (Ast.Ty.refin Ast.Ty.field (Ast.Predicate.dep Ast.mu ((Ast.Expr.var Ast.mu).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))) := by {
    apply Ty.TypeJudgment.TE_SUB
    apply Ty.TypeJudgment.TE_Var
    exact h₀
    apply Ty.SubtypeJudgment.TSub_Refine
    apply Ty.SubtypeJudgment.TSub_Refl
    intro σ T v hty hp

    unfold Ty.lookup_pred at h₁
    have hu8_i : (Env.lookupChip Δ "u8").ident_i = "i" := by {
      unfold Env.lookupChip Δ
      simp
    }
    have hu8_t : (Env.lookupChip Δ "u8").ident_t = "trace" := by {
      unfold Env.lookupChip Δ
      simp
    }
    rw[h₂, h₃, hu8_i, hu8_t] at h₁
    simp [Ast.renameVarinPred, Ast.renameVar] at h₁
    rw [if_neg h₄] at h₁
    have he := tyenv_and_to_eval_exprs hty h₁
    obtain ⟨he₁,he₂⟩ := he
    have he₃ := eval_eq_then_lt he₂ he₁

    simp [PropSemantics.predToProp] at hp
    cases hp
    rename_i va ih_f ih_a ih_b

    have heq : Eval.EvalProp σ T Δ (Ast.exprEq v (Ast.Expr.var x)) (Ast.Value.vBool true) := by {
      cases ih_f
      cases ih_b
      rename_i ih₁ ih₂ r
      cases ih₁
      rename_i ih₁
      simp [Env.lookupVal, Env.updateVal] at ih₁
      rw[← ih₁] at r
      cases ih₂
      rename_i ih₂
      have : Env.lookupVal (Env.updateVal σ Ast.mu va) x = Env.lookupVal σ x := by {
        apply lookup_val_update_ne
        exact h₅
      }
      rw[this] at ih₂
      rw[← ih₂] at r
      apply Eval.EvalProp.Rel
      exact ih_a
      apply Eval.EvalProp.Var
      exact ih₂
      rw[← ih₂]
      exact r
    }
    have he₄ := eval_eq_then_lt heq he₃
    simp [PropSemantics.predToProp]
    apply Eval.EvalProp.App
    apply Eval.EvalProp.Lam
    exact ih_a
    apply eval_var_lt_of_update
    exact ih_a
    exact he₄
    }

lemma u8_freshName_ne_i : Env.freshName
    (Ty.update_UsedNames (Env.lookupChip Δ "u8")
      (Ty.update_UsedNames (Env.lookupChip Δ "u8")
        (Ty.update_UsedNames (Env.lookupChip Δ "u8")
          (Ty.update_UsedNames (Env.lookupChip Δ "u8") ["i", "trace"]))))
    (Env.lookupChip Δ "u8").ident_t ≠
  "i" := by {
    unfold Ty.update_UsedNames Env.lookupChip Δ
    simp [Env.freshName]
  }

theorem koalabearWordRangeCheckerChip_correct : Ty.chipCorrect Δ koalabearWordRangeCheckerChip 1 := by
  unfold Ty.chipCorrect
  intro i hi Γ Η
  auto_trace_index
  repeat
    apply Ty.TypeJudgment.TE_LookUp
    rfl; rfl; rfl
  apply Ty.TypeJudgment.TE_LetIn
  apply lookup_update_self
  repeat apply Ty.TypeJudgment.TE_App
  apply koalabear_word_range_checker_func_typing_soundness
  apply u8_lookup_refines_lt256 "alpha_0" "l₀"
  apply lookup_update_ne
  simp
  apply lookup_update_ne
  simp
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply u8_lookup_refines_lt256 "alpha_1" "l₁"
  apply lookup_update_ne
  simp
  apply lookup_update_ne
  simp
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  have hmu₀ : (Ast.mu ≠ "value_0") := by decide
  rw[if_neg hmu₀]
  rw[if_neg hmu₀]
  simp [Ast.renameVarinPred, Ast.renameVar]
  apply u8_lookup_refines_lt256 "alpha_2" "l₂"
  apply lookup_update_ne
  simp
  apply lookup_update_ne
  simp
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  have hmu₀ : (Ast.mu ≠ "value_0") := by decide
  rw[if_neg hmu₀]
  rw[if_neg hmu₀]
  simp [Ast.renameVarinPred, Ast.renameVar]
  have hmu₁ : (Ast.mu ≠ "value_1") := by decide
  rw[if_neg hmu₁]
  rw[if_neg hmu₁]
  simp [Ast.renameVarinPred, Ast.renameVar]
  have hmu₂ : (Ast.mu ≠ "value_2") := by decide
  rw[if_neg hmu₂]
  rw[if_neg hmu₂]
  apply u8_lookup_refines_lt256 "alpha_3" "l₃"
  apply lookup_update_ne
  simp
  apply lookup_update_self
  repeat rfl
  exact u8_freshName_ne_i
  decide
  rfl
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  rfl
  apply Ty.TypeJudgment.TE_VarEnv
  simp [Ast.renameVarinPred, Ast.renameVar]
  apply lookup_update_ne
  simp
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  apply And.intro
  rfl
  apply And.intro
  repeat rfl
  repeat
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_ne
    simp
    simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
    apply And.intro
    rfl
    apply And.intro
    rfl
    rfl
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_ne
  simp
  simp [Ast.renameTy, Ast.renameVarinPred, Ast.renameVar]
  rfl
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self
