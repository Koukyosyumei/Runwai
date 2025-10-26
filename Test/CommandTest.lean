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

#runwai_compile_to_json IsZero

#runwai_register chip Lookup(trace, i, 2) -> {Unit| trace [i][0] == Fp 2} {
  let u = lookup Assert1(trace [i][0] : trace [i][1]) in u
}

#runwai_prove Δ₀ Assert1 := by {
  apply Ty.TypeJudgment.TE_LetIn
  · apply get_update_self
  · apply Ty.TypeJudgment.TE_Assert
    · apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_ArrayIndex
      apply Ty.TypeJudgment.TE_Var
      apply get_update_ne
      simp
      apply Ty.TypeJudgment.TE_VarEnv
      apply get_update_ne
      simp
      apply constZ_refine_lt
      simp
    . apply Ty.TypeJudgment.TE_ConstF
  . constructor;
    apply get_update_self
}

#runwai_prove Δ₁ IsZero := by {
  auto_trace_index
  apply isZero_typing_soundness
  repeat apply get_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply get_update_self;
  repeat decide
}

#runwai_prove Δ₂ Lookup := by {
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  simp
  apply Ty.TypeJudgment.TE_SUB
  apply Ty.TypeJudgment.TE_VarEnv
  unfold Env.getTy Env.updateTy
  simp
  apply And.intro
  rfl
  rfl
  apply Ty.SubtypeJudgment.TSub_Refine
  apply Ty.SubtypeJudgment.TSub_Refl
  intro σ T v h₁ h₂
  unfold PropSemantics.tyenvToProp at h₁
  have h₃ := h₁ "u"
  unfold Env.getTy Env.updateTy PropSemantics.varToProp Env.getTy at h₃
  simp at h₃
  unfold Ty.lookup_pred at h₃
  have hat : (Env.getChip Δ₂ "Assert1").ident_t = "trace" := by unfold Δ₂ Env.getChip; simp
  have hai : (Env.getChip Δ₂ "Assert1").ident_i = "i" := by unfold Δ₂ Env.getChip; simp
  rw[hat, hai] at h₃
  simp [Env.freshName, Ast.renameVarinPred, Ast.renameVar] at h₃
  obtain ⟨h₄,h₅⟩ := h₃
  unfold PropSemantics.predToProp PropSemantics.exprToProp at ⊢
  apply evalProp_eq_symm at h₅
  apply evalProp_eq_trans h₅ h₄
}
