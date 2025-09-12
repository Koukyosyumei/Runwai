import Runwai.Typing
import Runwai.Gadget
import Runwai.Command
import Runwai.Tactic

#runwai_register chip Assert1(trace, i, 2) -> {Unit| trace [i][1] == Fp 2} {let u = assert_eq(trace [i][1], Fp 2) in u}
#runwai_check Assert1

#runwai_register chip IsZero(trace, i, 3) -> {Unit| y == if x == Fp 0 then {Fp 1} else {Fp 0}} {
  let x = trace [i][0] in
  let y = trace [i][1] in
  let inv = trace [i][2] in
  let u₁ = assert_eq(y, ((Fp 0 - x) * inv) + Fp 1) in
  let u₂ = assert_eq(x*y, Fp 0) in u₂
}

#runwai_register chip Lookup(trace, i, 2) -> {Unit| trace [i][0] == Fp 2} {
  let u = #Assert1(trace [i][0] : trace [i][1]) in u
}

#runwai_prove Assert1 := by {
  rename_i Δ h_delta σ x i hs hi ht hty hσ σ Γ
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
}

#runwai_prove IsZero := by {
  rename_i Δ h_delta σ x i hs hi ht hty hσ σ Γ
  repeat
    apply Ty.TypeJudgment.TE_LetIn
    · apply lookup_update_self;
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
  apply isZero_typing_soundness
  repeat apply lookup_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply lookup_update_self;
  repeat decide
}

#runwai_prove Lookup := by {
  rename_i Δ h_delta trace i hs hi ht he hty hσ σ Γ
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  rw[← h_delta]
  simp
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.lookupTy Env.updateTy
  simp
  apply And.intro
  rfl
  rfl
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ v h₁ h₂
  unfold PropSemantics.tyenvToProp at h₁
  have h₃ := h₁ "u"
  unfold Env.lookupTy Env.updateTy PropSemantics.varToProp Env.lookupTy at h₃
  simp at h₃
  unfold Ty.lookup_pred at h₃
  have hat : (Env.lookupChip Δ "Assert1").ident_t = "trace" := by {
    rw[h_delta]
    unfold Env.lookupChip; simp }
  have hai : (Env.lookupChip Δ "Assert1").ident_i = "i" := by {
    rw[h_delta]
    unfold Env.lookupChip; simp }
  rw[hat, hai] at h₃
  unfold Env.freshName at h₃
  simp at h₃
  repeat unfold Ast.renameVarinPred at h₃
  repeat unfold Ast.renameVar at h₃; simp at h₃
  unfold PropSemantics.predToProp at h₃
  obtain ⟨h₄,h₅⟩ := h₃
  unfold PropSemantics.predToProp PropSemantics.exprToProp at h₄ h₅ ⊢
  apply evalProp_eq_symm at h₅
  apply evalProp_eq_trans h₅ h₄
}
