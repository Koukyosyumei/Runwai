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
  let u = lookup Assert1(trace [i][0] : trace [i][1]) in u
}

#runwai_register chip u8(trace, i, 1) -> {Unit | toN(trace [i][0]) < 256} {
  assert_eq(trace [i][0], trace [i][0])
}

#runwai_register chip koalabearWordRangeCheckerChip(trace, i, 18)
  -> {Unit| (toN(alpha_0) <+> (toN(alpha_1) <*> 256) <+> (toN(alpha_1) <*> 65536) <+> (toN(alpha_1) <*> 16777216)) < 2130706433 }
{
  let alpha_0 = trace [i][0] in
  let alpha_1 = trace [i][1] in
  let alpha_2 = trace [i][2] in
  let alpha_3 = trace [i][3] in
  let l₀ = lookup u8(alpha_0 : trace [i][0]) in
  let l₁ = lookup u8(alpha_1 : trace [i][0]) in
  let l₂ = lookup u8(alpha_2 : trace [i][0]) in
  let l₃ = lookup u8(alpha_3 : trace [i][0]) in
  let koalabear_word_range_checker_func =
    lam alpha_0 : field_lt_const 256 =>
    lam alpha_1 : field_lt_const 256 =>
    lam alpha_2 : field_lt_const 256 =>
    lam alpha_3 : field_lt_const 256 =>
    lam most_sig_byte_decomp_0 : {Unit| true} =>
    lam most_sig_byte_decomp_1 : {Unit| true} =>
    lam most_sig_byte_decomp_2 : {Unit| true} =>
    lam most_sig_byte_decomp_3 : {Unit| true} =>
    lam most_sig_byte_decomp_4 : {Unit| true} =>
    lam most_sig_byte_decomp_5 : {Unit| true} =>
    lam most_sig_byte_decomp_6 : {Unit| true} =>
    lam most_sig_byte_decomp_7 : {Unit| true} =>
    lam and_most_sig_byte_decomp_0_to_2 : {Unit| true} =>
    lam and_most_sig_byte_decomp_0_to_3 : {Unit| true} =>
    lam and_most_sig_byte_decomp_0_to_4 : {Unit| true} =>
    lam and_most_sig_byte_decomp_0_to_5 : {Unit| true} =>
    lam and_most_sig_byte_decomp_0_to_6 : {Unit| true} =>
    lam and_most_sig_byte_decomp_0_to_7 : {Unit| true} =>
    let b₁ = assert_eq(most_sig_byte_decomp_0 * (most_sig_byte_decomp_0 - Fp 1), Fp 0) in
    let b₂ = assert_eq(most_sig_byte_decomp_1 * (most_sig_byte_decomp_1 - Fp 1), Fp 0) in
    let b₃ = assert_eq(most_sig_byte_decomp_2 * (most_sig_byte_decomp_2 - Fp 1), Fp 0) in
    let b₄ = assert_eq(most_sig_byte_decomp_3 * (most_sig_byte_decomp_3 - Fp 1), Fp 0) in
    let b₅ = assert_eq(most_sig_byte_decomp_4 * (most_sig_byte_decomp_4 - Fp 1), Fp 0) in
    let b₆ = assert_eq(most_sig_byte_decomp_5 * (most_sig_byte_decomp_5 - Fp 1), Fp 0) in
    let b₇ = assert_eq(most_sig_byte_decomp_6 * (most_sig_byte_decomp_6 - Fp 1), Fp 0) in
    let b₈ = assert_eq(most_sig_byte_decomp_7 * (most_sig_byte_decomp_7 - Fp 1), Fp 0) in
    let u₁ = assert_eq((((((((most_sig_byte_decomp_0 + (most_sig_byte_decomp_1 * 2)) + (most_sig_byte_decomp_2 * 4)) +
                      (most_sig_byte_decomp_3 * 8)) + (most_sig_byte_decomp_4 * 16)) + (most_sig_byte_decomp_5 * 32)) +
                      (most_sig_byte_decomp_6 * 64)) + (most_sig_byte_decomp_7 * 128)), value_3) in
    let u₂ = assert_eq(most_sig_byte_decomp_7, Fp 0) in
    let u₃ = assert_eq(and_most_sig_byte_decomp_0_to_2, most_sig_byte_decomp_0 * most_sig_byte_decomp_1) in
    let u₄ = assert_eq(and_most_sig_byte_decomp_0_to_3, and_most_sig_byte_decomp_0_to_2 * most_sig_byte_decomp_2) in
    let u₅ = assert_eq(and_most_sig_byte_decomp_0_to_4, and_most_sig_byte_decomp_0_to_3 * most_sig_byte_decomp_3) in
    let u₆ = assert_eq(and_most_sig_byte_decomp_0_to_5, and_most_sig_byte_decomp_0_to_4 * most_sig_byte_decomp_4) in
    let u₇ = assert_eq(and_most_sig_byte_decomp_0_to_6, and_most_sig_byte_decomp_0_to_5 * most_sig_byte_decomp_5) in
    let u₈ = assert_eq(and_most_sig_byte_decomp_0_to_7, and_most_sig_byte_decomp_0_to_6 * most_sig_byte_decomp_6) in
    let u₉ = assert_eq(Fp 0, and_most_sig_byte_decomp_0_to_7 * value_0) in
    let u₁₀ = assert_eq(Fp 0, and_most_sig_byte_decomp_0_to_7 * value_1) in
    let u₁₁ = assert_eq(Fp 0, and_most_sig_byte_decomp_0_to_7 * value_2) in u₁₁ in
  let u₁ = ((((((((((((((((((koalabear_word_range_checker_func (alpha_0)) (alpha_1)) (alpha_2)) (alpha_3))
          (most_sig_byte_decomp_0)) (most_sig_byte_decomp_1)) (most_sig_byte_decomp_2)) (most_sig_byte_decomp_3))
          (most_sig_byte_decomp_4)) (most_sig_byte_decomp_5)) (most_sig_byte_decomp_6)) (most_sig_byte_decomp_7))
          (and_most_sig_byte_decomp_0_to_2)) (and_most_sig_byte_decomp_0_to_3)) (and_most_sig_byte_decomp_0_to_4))
          (and_most_sig_byte_decomp_0_to_5)) (and_most_sig_byte_decomp_0_to_6)) (and_most_sig_byte_decomp_0_to_7)) in
  u₁
}

#runwai_prove Assert1 := by {
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

#runwai_prove IsZero := by {
  auto_trace_index
  apply isZero_typing_soundness
  repeat apply get_update_ne; simp
  apply Ty.TypeJudgment.TE_VarEnv
  apply get_update_self;
  repeat decide
}

#runwai_prove Lookup := by {
  rename_i Δ h_delta height hh Γ Η
  apply Ty.TypeJudgment.TE_LookUp; repeat rfl
  rw[← h_delta]
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
  have hat : (Env.getChip Δ "Assert1").ident_t = "trace" := by {
    rw[h_delta]
    unfold Env.getChip; simp }
  have hai : (Env.getChip Δ "Assert1").ident_i = "i" := by {
    rw[h_delta]
    unfold Env.getChip; simp }
  rw[hat, hai] at h₃
  simp [Env.freshName] at h₃
  simp [Ast.renameVarinPred] at h₃
  simp [Ast.renameVar] at h₃
  obtain ⟨h₄,h₅⟩ := h₃
  unfold PropSemantics.predToProp PropSemantics.exprToProp at ⊢
  apply evalProp_eq_symm at h₅
  apply evalProp_eq_trans h₅ h₄
}
