import Runwai.Typing
import Runwai.Gadget
--import Runwai.PP
import Runwai.Tactic

@[simp]
def assertCircuit : Ast.Circuit := {
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
def iszeroCircuit : Ast.Circuit := {
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
def u8chip : Ast.Circuit := {
  name := "u8",
  ident_t := "trace",
  ident_i := "i"
  width := 1,
  goal := Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind (Ast.Expr.binRel (Ast.Expr.toZ (Ast.trace_i_j "trace" "i" 0)) Ast.RelOp.lt (Ast.Expr.constZ 256))),
  body := Ast.Expr.assertE (Ast.Expr.constF 0) (Ast.Expr.constF 0)
}

@[simp]
def wordRangeCheckerCircuit : Ast.Circuit := {
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
            (.assertE (.fieldExpr
                        (.fieldExpr
                          (.fieldExpr
                            (.fieldExpr
                              (.fieldExpr
                                (.fieldExpr
                                  (.fieldExpr
                                    (.var "most_sig_byte_decomp_0")
                                    .add
                                    (.fieldExpr (.var "most_sig_byte_decomp_1") .mul (.constF 2)))
                                  .add
                                  (.fieldExpr
                                    (.var "most_sig_byte_decomp_2") .mul (.constF 4)))
                                    .add
                                    (.fieldExpr (.var "most_sig_byte_decomp_3") .mul (.constF 8))
                                )
                              .add
                              (.fieldExpr (.var "most_sig_byte_decomp_4") .mul (.constF 16))
                            )
                            .add
                            (.fieldExpr (.var "most_sig_byte_decomp_5") .mul (.constF 32))
                          )
                          .add
                          (.fieldExpr (.var "most_sig_byte_decomp_6") .mul (.constF 64))
                        )
                        .add
                        (.fieldExpr (.var "most_sig_byte_decomp_7") .mul (.constF 128))
                      )
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

def Δ : Env.CircuitEnv := [("assert", assertCircuit), ("u8", u8chip)]

lemma is_binary {x: F} (h: x * (x - 1) = 0): x = 0 ∨ x = 1 := by {
  simp_all
  rcases h with h_case | h_case
  {
    left
    exact h_case
  }
  {
    right
    apply sub_eq_iff_eq_add.mp h_case
  }
}


lemma is_binary_f_to_z {x: F} (h: x = 0 ∨ x = 1) : x.val = 0 ∨ x.val = 1 := by {
  rcases h with h_case | h_case
  {
    left
    simp
    exact h_case
  }
  {
    right
    rw[h_case]
    rfl
  }
}

lemma is_binary_less_than_one {x: ℕ} (h: x = 0 ∨ x = 1): x ≤ 1 := by {
  cases h
  {
    rename_i h
    rw[h]
    simp
  }
  {
    rename_i h
    rw[h]
  }
}

lemma is_binary_mul_is_binary {x y z: ℕ} (h₁: x = 0 ∨ x = 1) (h₂: y = 0 ∨ y = 1) (h₃: z = x * y): z = 0 ∨ z = 1 := by {
  cases h₁
  cases h₂
  simp_all
  simp_all
  simp_all
}

lemma is_binary_mul_is_binary_f {x y z: F} (h₁: x = 0 ∨ x = 1) (h₂: y = 0 ∨ y = 1) (h₃: z = x * y): z = 0 ∨ z = 1 := by {
  cases h₁
  cases h₂
  simp_all
  simp_all
  simp_all
}

lemma wordRange_correct
  {value_0 value_1 value_2 value_3 most_sig_byte_decomp_0
   most_sig_byte_decomp_1 most_sig_byte_decomp_2 most_sig_byte_decomp_3
   most_sig_byte_decomp_4 most_sig_byte_decomp_5 most_sig_byte_decomp_6 most_sig_byte_decomp_7
   and_most_sig_byte_decomp_0_to_2 and_most_sig_byte_decomp_0_to_3 and_most_sig_byte_decomp_0_to_4
   and_most_sig_byte_decomp_0_to_5 and_most_sig_byte_decomp_0_to_6 and_most_sig_byte_decomp_0_to_7: F}
  (h₀: most_sig_byte_decomp_0 * (most_sig_byte_decomp_0 - 1) = 0)
  (h₁: most_sig_byte_decomp_1 * (most_sig_byte_decomp_1 - 1) = 0)
  (h₂: most_sig_byte_decomp_2 * (most_sig_byte_decomp_2 - 1) = 0)
  (h₃: most_sig_byte_decomp_3 * (most_sig_byte_decomp_3 - 1) = 0)
  (h₄: most_sig_byte_decomp_4 * (most_sig_byte_decomp_4 - 1) = 0)
  (h₅: most_sig_byte_decomp_5 * (most_sig_byte_decomp_5 - 1) = 0)
  (h₆: most_sig_byte_decomp_6 * (most_sig_byte_decomp_6 - 1) = 0)
  (h₇: most_sig_byte_decomp_7 * (most_sig_byte_decomp_7 - 1) = 0)
  (h₉: most_sig_byte_decomp_0 + most_sig_byte_decomp_1 * 2 + most_sig_byte_decomp_2 * 4 + most_sig_byte_decomp_3 * 8 + most_sig_byte_decomp_4 * 16 + most_sig_byte_decomp_5 * 32 + most_sig_byte_decomp_6 * 64 + most_sig_byte_decomp_7 * 128 = value_3)
  (h₁₀: most_sig_byte_decomp_7 = 0)
  (h₁₁: and_most_sig_byte_decomp_0_to_2 = most_sig_byte_decomp_0 * most_sig_byte_decomp_1)
  (h₁₂: and_most_sig_byte_decomp_0_to_3 = and_most_sig_byte_decomp_0_to_2 * most_sig_byte_decomp_2)
  (h₁₃: and_most_sig_byte_decomp_0_to_4 = and_most_sig_byte_decomp_0_to_3 * most_sig_byte_decomp_3)
  (h₁₄: and_most_sig_byte_decomp_0_to_5 = and_most_sig_byte_decomp_0_to_4 * most_sig_byte_decomp_4)
  (h₁₅: and_most_sig_byte_decomp_0_to_6 = and_most_sig_byte_decomp_0_to_5 * most_sig_byte_decomp_5)
  (h₁₆: and_most_sig_byte_decomp_0_to_7 = and_most_sig_byte_decomp_0_to_6 * most_sig_byte_decomp_6)
  (h₁₇: and_most_sig_byte_decomp_0_to_7 * value_0 = 0)
  (h₁₈: and_most_sig_byte_decomp_0_to_7 * value_1 = 0)
  (h₁₉: and_most_sig_byte_decomp_0_to_7 * value_2 = 0)
  (h₂₀: value_0.val < 256)
  (h₂₁: value_1.val < 256)
  (h₂₂: value_2.val < 256)
  (h₂₃: value_3.val < 256)
  : value_0.val + value_1.val * 256 + value_2.val * (256 ^ 2) + value_3.val * (256 ^ 3) < 2130706433 := by {
  -- 1) each decomposed bit is 0 or 1
  have b0 : most_sig_byte_decomp_0 = 0 ∨ most_sig_byte_decomp_0 = 1 := is_binary h₀
  have b1 : most_sig_byte_decomp_1 = 0 ∨ most_sig_byte_decomp_1 = 1 := is_binary h₁
  have b2 : most_sig_byte_decomp_2 = 0 ∨ most_sig_byte_decomp_2 = 1 := is_binary h₂
  have b3 : most_sig_byte_decomp_3 = 0 ∨ most_sig_byte_decomp_3 = 1 := is_binary h₃
  have b4 : most_sig_byte_decomp_4 = 0 ∨ most_sig_byte_decomp_4 = 1 := is_binary h₄
  have b5 : most_sig_byte_decomp_5 = 0 ∨ most_sig_byte_decomp_5 = 1 := is_binary h₅
  have b6 : most_sig_byte_decomp_6 = 0 ∨ most_sig_byte_decomp_6 = 1 := is_binary h₆
  have b7 : most_sig_byte_decomp_7 = 0 ∨ most_sig_byte_decomp_7 = 1 := is_binary h₇
  -- 2) because bit7 = 0, value_3 ≤ 127
  have v3_le_127 : value_3.val ≤ 127 := by
    { -- value_3 = sum_{i=0..7} bit_i * 2^i and bit7 = 0 so upper bound is when bits0..6 = 1
      rw [← h₉, h₁₀]
      have : most_sig_byte_decomp_0.val + most_sig_byte_decomp_1.val * 2 + most_sig_byte_decomp_2.val * 4 + most_sig_byte_decomp_3.val * 8 +
            most_sig_byte_decomp_4.val * 16 + most_sig_byte_decomp_5.val * 32 + most_sig_byte_decomp_6.val * 64 ≤ 1 + 2 + 4 + 8 + 16 + 32 + 64 := by
      { have b0' : most_sig_byte_decomp_0.val ≤ 1 := is_binary_less_than_one (is_binary_f_to_z b0)
        have b1' : most_sig_byte_decomp_1.val ≤ 1 := is_binary_less_than_one (is_binary_f_to_z b1)
        have b2' : most_sig_byte_decomp_2.val ≤ 1 := is_binary_less_than_one (is_binary_f_to_z b2)
        have b3' : most_sig_byte_decomp_3.val ≤ 1 := is_binary_less_than_one (is_binary_f_to_z b3)
        have b4' : most_sig_byte_decomp_4.val ≤ 1 := is_binary_less_than_one (is_binary_f_to_z b4)
        have b5' : most_sig_byte_decomp_5.val ≤ 1 := is_binary_less_than_one (is_binary_f_to_z b5)
        have b6' : most_sig_byte_decomp_6.val ≤ 1 := is_binary_less_than_one (is_binary_f_to_z b6)
        gcongr
        simp
        exact b1'
        simp
        exact b2'
        simp
        exact b3'
        simp
        exact b4'
        simp
        exact b5'
        simp
        exact b6'
      }
      simp at this ⊢
      simp [ZMod.val_add, ZMod.val_mul]
      rw [Nat.mod_eq_of_lt]
      exact this
      apply Nat.lt_trans
      exact Nat.lt_succ_of_le this
      unfold p
      simp
    }
  have c0 := is_binary_mul_is_binary_f b0 b1 h₁₁
  have c1 := is_binary_mul_is_binary_f c0 b2 h₁₂
  have c2 := is_binary_mul_is_binary_f c1 b3 h₁₃
  have c3 := is_binary_mul_is_binary_f c2 b4 h₁₄
  have c4 := is_binary_mul_is_binary_f c3 b5 h₁₅
  have c5 := is_binary_f_to_z (is_binary_mul_is_binary_f c4 b6 h₁₆)
  cases c5
  {
    rename_i h
    have : value_3.val < 126 := by {
      sorry
    }
    calc
      value_0.val + value_1.val * 256 + value_2.val * 256^2 + value_3.val * 256^3
          ≤ 255 + 255*256 + 255*256^2 + 125*256^3 := by
            apply Nat.add_le_add
            apply Nat.add_le_add
            apply Nat.add_le_add
            · exact Nat.lt_succ_iff.mp h₂₀
            · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp h₂₁)
            · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp h₂₂)
            · {
              have h_le : value_3.val ≤ 125 := Nat.lt_succ_iff.mp this
              rw [Nat.mul_comm]
              exact Nat.mul_le_mul_left _ h_le
            }
      _ = 2113929215 := by simp
      _ < 2130706433 := by simp
  }
  {
    rename_i h
    have : and_most_sig_byte_decomp_0_to_7 = 1 := by {
      rw[← ZMod.val_one'] at h
      apply ZMod.val_injective
      exact h
    }
    rw[this] at h₁₇ h₁₈ h₁₉
    simp at h₁₇ h₁₈ h₁₉
    rw[h₁₇, h₁₈, h₁₉]
    simp
    rw [Nat.mul_comm]
    calc
      16777216 * value_3.val ≤ 16777216 * 127 := Nat.mul_le_mul_left 16777216 v3_le_127
      _ < 127 * 16777216 + 1 := by norm_num
  }
}

theorem wordRangeCheckerCircuit_correct : Ty.circuitCorrect Δ wordRangeCheckerCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i hs hi hrow ht hσ
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
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
    apply Ty.TypeJudgment.TE_ConstF
    apply Ty.TypeJudgment.TE_ConstF
  . repeat
      apply Ty.TypeJudgment.TE_LetIn
      apply lookup_update_self
      apply Ty.TypeJudgment.TE_Assert
      apply Ty.TypeJudgment.TE_BinOpField
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp
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
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp
    repeat
      apply Ty.TypeJudgment.TE_LetIn
      apply lookup_update_self
      apply Ty.TypeJudgment.TE_Assert
      apply Ty.TypeJudgment.TE_ConstF
      apply Ty.TypeJudgment.TE_BinOpField
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp
      apply Ty.TypeJudgment.TE_VarEnv
      apply lookup_update_ne
      simp
    apply Ty.TypeJudgment.TE_LookUp
    rfl
    rfl
    rfl
    apply Ty.TypeJudgment.TE_LookUp
    rfl
    rfl
    rfl
    apply Ty.TypeJudgment.TE_LookUp
    rfl
    rfl
    rfl
    apply Ty.TypeJudgment.TE_LookUp
    rfl
    rfl
    rfl
    set τ := (Ast.Ty.unit.refin
      (Ty.lookup_pred [(Ast.Expr.var "value_3", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
        (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
        (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
          (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]))))) with hτ
    have h_sub : @Ty.SubtypeJudgment σ Δ (Env.updateTy
    (Env.updateTy
      (Env.updateTy
        (Env.updateTy
          (Env.updateTy
            (Env.updateTy
              (Env.updateTy
                (Env.updateTy
                  (Env.updateTy
                    (Env.updateTy
                      (Env.updateTy
                        (Env.updateTy
                          (Env.updateTy
                            (Env.updateTy
                              (Env.updateTy
                                (Env.updateTy
                                  (Env.updateTy
                                    (Env.updateTy
                                      (Env.updateTy
                                        (Env.updateTy
                                          (Env.updateTy
                                            (Env.updateTy
                                              (Env.updateTy
                                                (Env.updateTy
                                                  (Env.updateTy
                                                    (Env.updateTy
                                                      (Env.updateTy
                                                        (Env.updateTy
                                                          (Env.updateTy
                                                            (Env.updateTy
                                                              (Env.updateTy
                                                                (Env.updateTy
                                                                  (Env.updateTy
                                                                    (Env.updateTy
                                                                      (Env.updateTy
                                                                        (Env.updateTy
                                                                          (Env.updateTy
                                                                            (Env.updateTy
                                                                              (Env.updateTy
                                                                                (Env.updateTy
                                                                                  (Env.updateTy
                                                                                    (Env.updateTy
                                                                                      (Env.updateTy []
                                                                                        wordRangeCheckerCircuit.ident_t
                                                                                        (((((Ast.Ty.field.refin
                                                                                                          (Ast.Predicate.ind
                                                                                                            (Ast.Expr.constBool
                                                                                                              true))).arr
                                                                                                      wordRangeCheckerCircuit.width).refin
                                                                                                  (Ast.Predicate.ind
                                                                                                    (Ast.Expr.constBool
                                                                                                      true))).arr
                                                                                              ↑x.length).refin
                                                                                          (Ast.Predicate.ind
                                                                                            (Ast.Expr.constBool true))))
                                                                                      wordRangeCheckerCircuit.ident_i
                                                                                      (Ast.Ty.int.refin
                                                                                        (Ast.Predicate.dep "v"
                                                                                          ((Ast.Expr.var "v").binRel
                                                                                            Ast.RelOp.lt
                                                                                            (Ast.Expr.constZ
                                                                                              x.length)))))
                                                                                    "value_0"
                                                                                    (Ast.Ty.field.refin
                                                                                      (Ast.Predicate.ind
                                                                                        (Ast.Expr.constBool true))))
                                                                                  "value_1"
                                                                                  (Ast.Ty.field.refin
                                                                                    (Ast.Predicate.ind
                                                                                      (Ast.Expr.constBool true))))
                                                                                "value_2"
                                                                                (Ast.Ty.field.refin
                                                                                  (Ast.Predicate.ind
                                                                                    (Ast.Expr.constBool true))))
                                                                              "value_3"
                                                                              (Ast.Ty.field.refin
                                                                                (Ast.Predicate.ind
                                                                                  (Ast.Expr.constBool true))))
                                                                            "most_sig_byte_decomp_0"
                                                                            (Ast.Ty.field.refin
                                                                              (Ast.Predicate.ind
                                                                                (Ast.Expr.constBool true))))
                                                                          "most_sig_byte_decomp_1"
                                                                          (Ast.Ty.field.refin
                                                                            (Ast.Predicate.ind
                                                                              (Ast.Expr.constBool true))))
                                                                        "most_sig_byte_decomp_2"
                                                                        (Ast.Ty.field.refin
                                                                          (Ast.Predicate.ind
                                                                            (Ast.Expr.constBool true))))
                                                                      "most_sig_byte_decomp_3"
                                                                      (Ast.Ty.field.refin
                                                                        (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                                    "most_sig_byte_decomp_4"
                                                                    (Ast.Ty.field.refin
                                                                      (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                                  "most_sig_byte_decomp_5"
                                                                  (Ast.Ty.field.refin
                                                                    (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                                "most_sig_byte_decomp_6"
                                                                (Ast.Ty.field.refin
                                                                  (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                              "most_sig_byte_decomp_7"
                                                              (Ast.Ty.field.refin
                                                                (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                            "and_most_sig_byte_decomp_0_to_2"
                                                            (Ast.Ty.field.refin
                                                              (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                          "and_most_sig_byte_decomp_0_to_3"
                                                          (Ast.Ty.field.refin
                                                            (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                        "and_most_sig_byte_decomp_0_to_4"
                                                        (Ast.Ty.field.refin
                                                          (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                      "and_most_sig_byte_decomp_0_to_5"
                                                      (Ast.Ty.field.refin
                                                        (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                    "and_most_sig_byte_decomp_0_to_6"
                                                    (Ast.Ty.field.refin (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                  "and_most_sig_byte_decomp_0_to_7"
                                                  (Ast.Ty.field.refin (Ast.Predicate.ind (Ast.Expr.constBool true))))
                                                "b₀"
                                                (Ast.Ty.unit.refin
                                                  (Ast.Predicate.ind
                                                    (Ast.exprEq
                                                      ((Ast.Expr.var "most_sig_byte_decomp_0").fieldExpr Ast.FieldOp.mul
                                                        ((Ast.Expr.var "most_sig_byte_decomp_0").fieldExpr
                                                          Ast.FieldOp.sub (Ast.Expr.constF 1)))
                                                      (Ast.Expr.constF 0)))))
                                              "b₁"
                                              (Ast.Ty.unit.refin
                                                (Ast.Predicate.ind
                                                  (Ast.exprEq
                                                    ((Ast.Expr.var "most_sig_byte_decomp_1").fieldExpr Ast.FieldOp.mul
                                                      ((Ast.Expr.var "most_sig_byte_decomp_1").fieldExpr Ast.FieldOp.sub
                                                        (Ast.Expr.constF 1)))
                                                    (Ast.Expr.constF 0)))))
                                            "b₂"
                                            (Ast.Ty.unit.refin
                                              (Ast.Predicate.ind
                                                (Ast.exprEq
                                                  ((Ast.Expr.var "most_sig_byte_decomp_2").fieldExpr Ast.FieldOp.mul
                                                    ((Ast.Expr.var "most_sig_byte_decomp_2").fieldExpr Ast.FieldOp.sub
                                                      (Ast.Expr.constF 1)))
                                                  (Ast.Expr.constF 0)))))
                                          "b₃"
                                          (Ast.Ty.unit.refin
                                            (Ast.Predicate.ind
                                              (Ast.exprEq
                                                ((Ast.Expr.var "most_sig_byte_decomp_3").fieldExpr Ast.FieldOp.mul
                                                  ((Ast.Expr.var "most_sig_byte_decomp_3").fieldExpr Ast.FieldOp.sub
                                                    (Ast.Expr.constF 1)))
                                                (Ast.Expr.constF 0)))))
                                        "b₄"
                                        (Ast.Ty.unit.refin
                                          (Ast.Predicate.ind
                                            (Ast.exprEq
                                              ((Ast.Expr.var "most_sig_byte_decomp_4").fieldExpr Ast.FieldOp.mul
                                                ((Ast.Expr.var "most_sig_byte_decomp_4").fieldExpr Ast.FieldOp.sub
                                                  (Ast.Expr.constF 1)))
                                              (Ast.Expr.constF 0)))))
                                      "b₅"
                                      (Ast.Ty.unit.refin
                                        (Ast.Predicate.ind
                                          (Ast.exprEq
                                            ((Ast.Expr.var "most_sig_byte_decomp_5").fieldExpr Ast.FieldOp.mul
                                              ((Ast.Expr.var "most_sig_byte_decomp_5").fieldExpr Ast.FieldOp.sub
                                                (Ast.Expr.constF 1)))
                                            (Ast.Expr.constF 0)))))
                                    "b₆"
                                    (Ast.Ty.unit.refin
                                      (Ast.Predicate.ind
                                        (Ast.exprEq
                                          ((Ast.Expr.var "most_sig_byte_decomp_6").fieldExpr Ast.FieldOp.mul
                                            ((Ast.Expr.var "most_sig_byte_decomp_6").fieldExpr Ast.FieldOp.sub
                                              (Ast.Expr.constF 1)))
                                          (Ast.Expr.constF 0)))))
                                  "b₇"
                                  (Ast.Ty.unit.refin
                                    (Ast.Predicate.ind
                                      (Ast.exprEq
                                        ((Ast.Expr.var "most_sig_byte_decomp_7").fieldExpr Ast.FieldOp.mul
                                          ((Ast.Expr.var "most_sig_byte_decomp_7").fieldExpr Ast.FieldOp.sub
                                            (Ast.Expr.constF 1)))
                                        (Ast.Expr.constF 0)))))
                                "u₁"
                                (Ast.Ty.unit.refin
                                  (Ast.Predicate.ind
                                    (Ast.exprEq
                                      ((((((((Ast.Expr.var "most_sig_byte_decomp_0").fieldExpr Ast.FieldOp.add
                                                                ((Ast.Expr.var "most_sig_byte_decomp_1").fieldExpr
                                                                  Ast.FieldOp.mul (Ast.Expr.constF 2))).fieldExpr
                                                            Ast.FieldOp.add
                                                            ((Ast.Expr.var "most_sig_byte_decomp_2").fieldExpr
                                                              Ast.FieldOp.mul (Ast.Expr.constF 4))).fieldExpr
                                                        Ast.FieldOp.add
                                                        ((Ast.Expr.var "most_sig_byte_decomp_3").fieldExpr
                                                          Ast.FieldOp.mul (Ast.Expr.constF 8))).fieldExpr
                                                    Ast.FieldOp.add
                                                    ((Ast.Expr.var "most_sig_byte_decomp_4").fieldExpr Ast.FieldOp.mul
                                                      (Ast.Expr.constF 16))).fieldExpr
                                                Ast.FieldOp.add
                                                ((Ast.Expr.var "most_sig_byte_decomp_5").fieldExpr Ast.FieldOp.mul
                                                  (Ast.Expr.constF 32))).fieldExpr
                                            Ast.FieldOp.add
                                            ((Ast.Expr.var "most_sig_byte_decomp_6").fieldExpr Ast.FieldOp.mul
                                              (Ast.Expr.constF 64))).fieldExpr
                                        Ast.FieldOp.add
                                        ((Ast.Expr.var "most_sig_byte_decomp_7").fieldExpr Ast.FieldOp.mul
                                          (Ast.Expr.constF 128)))
                                      (Ast.Expr.var "value_3")))))
                              "u₂"
                              (Ast.Ty.unit.refin
                                (Ast.Predicate.ind
                                  (Ast.exprEq (Ast.Expr.var "most_sig_byte_decomp_7") (Ast.Expr.constF 0)))))
                            "u₃"
                            (Ast.Ty.unit.refin
                              (Ast.Predicate.ind
                                (Ast.exprEq (Ast.Expr.var "and_most_sig_byte_decomp_0_to_2")
                                  ((Ast.Expr.var "most_sig_byte_decomp_0").fieldExpr Ast.FieldOp.mul
                                    (Ast.Expr.var "most_sig_byte_decomp_1"))))))
                          "u₄"
                          (Ast.Ty.unit.refin
                            (Ast.Predicate.ind
                              (Ast.exprEq (Ast.Expr.var "and_most_sig_byte_decomp_0_to_3")
                                ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_2").fieldExpr Ast.FieldOp.mul
                                  (Ast.Expr.var "most_sig_byte_decomp_2"))))))
                        "u₅"
                        (Ast.Ty.unit.refin
                          (Ast.Predicate.ind
                            (Ast.exprEq (Ast.Expr.var "and_most_sig_byte_decomp_0_to_4")
                              ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_3").fieldExpr Ast.FieldOp.mul
                                (Ast.Expr.var "most_sig_byte_decomp_3"))))))
                      "u₆"
                      (Ast.Ty.unit.refin
                        (Ast.Predicate.ind
                          (Ast.exprEq (Ast.Expr.var "and_most_sig_byte_decomp_0_to_5")
                            ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_4").fieldExpr Ast.FieldOp.mul
                              (Ast.Expr.var "most_sig_byte_decomp_4"))))))
                    "u₇"
                    (Ast.Ty.unit.refin
                      (Ast.Predicate.ind
                        (Ast.exprEq (Ast.Expr.var "and_most_sig_byte_decomp_0_to_6")
                          ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_5").fieldExpr Ast.FieldOp.mul
                            (Ast.Expr.var "most_sig_byte_decomp_5"))))))
                  "u₈"
                  (Ast.Ty.unit.refin
                    (Ast.Predicate.ind
                      (Ast.exprEq (Ast.Expr.var "and_most_sig_byte_decomp_0_to_7")
                        ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_6").fieldExpr Ast.FieldOp.mul
                          (Ast.Expr.var "most_sig_byte_decomp_6"))))))
                "u₉"
                (Ast.Ty.unit.refin
                  (Ast.Predicate.ind
                    (Ast.exprEq (Ast.Expr.constF 0)
                      ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                        (Ast.Expr.var "value_0"))))))
              "u₁₀"
              (Ast.Ty.unit.refin
                (Ast.Predicate.ind
                  (Ast.exprEq (Ast.Expr.constF 0)
                    ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                      (Ast.Expr.var "value_1"))))))
            "u₁₁"
            (Ast.Ty.unit.refin
              (Ast.Predicate.ind
                (Ast.exprEq (Ast.Expr.constF 0)
                  ((Ast.Expr.var "and_most_sig_byte_decomp_0_to_7").fieldExpr Ast.FieldOp.mul
                    (Ast.Expr.var "value_2"))))))
          "l₀"
          (Ast.Ty.unit.refin
            (Ty.lookup_pred [(Ast.Expr.var "value_0", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
              (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t])))
        "l₁"
        (Ast.Ty.unit.refin
          (Ty.lookup_pred [(Ast.Expr.var "value_1", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
            (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]))))
      "l₂"
      (Ast.Ty.unit.refin
        (Ty.lookup_pred [(Ast.Expr.var "value_2", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
          (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
          (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t])))))
    "l₃" τ) τ wordRangeCheckerCircuit.goal := by {
      sorry
    }
    apply Ty.TypeJudgment.TE_SUB h_sub
    apply Ty.TypeJudgment.TE_VarEnv
    apply lookup_update_self

theorem assertCircuit_correct : Ty.circuitCorrect Δ assertCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i hs hi hrow ht hσ
  let envs := Ty.makeEnvs assertCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
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

theorem iszeroCircuit_correct : Ty.circuitCorrect Δ iszeroCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi hrow ht
  let envs := Ty.makeEnvs iszeroCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
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

theorem iszeroCircuit_correct_long : Ty.circuitCorrect Δ iszeroCircuit 1 := by
  unfold Ty.circuitCorrect
  intro x i height hs hi hrow ht
  let envs := Ty.makeEnvs iszeroCircuit (Ast.Value.vArr x) (Ast.Value.vZ i) x.length
  let σ := envs.1
  let Γ := envs.2
  unfold iszeroCircuit; simp
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
