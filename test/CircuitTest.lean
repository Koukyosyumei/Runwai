import Runwai.Typing
import Runwai.Gadget
--import Runwai.PP
import Runwai.Tactic

import Lean.Parser.Tactic

open Lean Elab Tactic

abbrev bit_value_type (ident: String): Ast.Ty := (Ast.Ty.unit.refin
                                                  (Ast.Predicate.ind
                                                    (Ast.exprEq
                                                      ((Ast.Expr.var ident).fieldExpr Ast.FieldOp.mul
                                                        ((Ast.Expr.var ident).fieldExpr
                                                          Ast.FieldOp.sub (Ast.Expr.constF 1)))
                                                      (Ast.Expr.constF 0))))

abbrev bits_to_byte_expr (i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇: String) : Ast.Expr :=
                                      ((((((((Ast.Expr.var i₀).fieldExpr Ast.FieldOp.add
                                                                ((Ast.Expr.var i₁).fieldExpr
                                                                  Ast.FieldOp.mul (Ast.Expr.constF 2))).fieldExpr
                                                            Ast.FieldOp.add
                                                            ((Ast.Expr.var i₂).fieldExpr
                                                              Ast.FieldOp.mul (Ast.Expr.constF 4))).fieldExpr
                                                        Ast.FieldOp.add
                                                        ((Ast.Expr.var i₃).fieldExpr
                                                          Ast.FieldOp.mul (Ast.Expr.constF 8))).fieldExpr
                                                    Ast.FieldOp.add
                                                    ((Ast.Expr.var i₄).fieldExpr Ast.FieldOp.mul
                                                      (Ast.Expr.constF 16))).fieldExpr
                                                Ast.FieldOp.add
                                                ((Ast.Expr.var i₅).fieldExpr Ast.FieldOp.mul
                                                  (Ast.Expr.constF 32))).fieldExpr
                                            Ast.FieldOp.add
                                            ((Ast.Expr.var i₆).fieldExpr Ast.FieldOp.mul
                                              (Ast.Expr.constF 64))).fieldExpr
                                        Ast.FieldOp.add
                                        ((Ast.Expr.var i₇).fieldExpr Ast.FieldOp.mul
                                          (Ast.Expr.constF 128)))
abbrev eq_mul_refinement (i₁ i₂ i₃: String): Ast.Ty := Ast.Ty.unit.refin
                        (Ast.Predicate.ind
                          (Ast.exprEq (Ast.Expr.var i₁)
                            ((Ast.Expr.var i₂).fieldExpr Ast.FieldOp.mul
                              (Ast.Expr.var i₃))))

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

def Δ : Env.CircuitEnv := [("assert", assertCircuit), ("u8", u8chip)]

lemma bit_value_0_or_1 {x: F} (h: x * (x - 1) = 0): x = 0 ∨ x = 1 := by {
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


lemma bit_val_to_nat {x: F} (h: x = 0 ∨ x = 1) : x.val = 0 ∨ x.val = 1 := by {
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

lemma bit_le_one {x: ℕ} (h: x = 0 ∨ x = 1): x ≤ 1 := by {
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

lemma binary_mul_binary_nat {x y z: ℕ} (h₁: x = 0 ∨ x = 1) (h₂: y = 0 ∨ y = 1) (h₃: z = x * y): z = 0 ∨ z = 1 := by {
  cases h₁
  cases h₂
  simp_all
  simp_all
  simp_all
}

lemma binary_mul_binary_F {x y z: F} (h₁: x = 0 ∨ x = 1) (h₂: y = 0 ∨ y = 1) (h₃: z = x * y): z = 0 ∨ z = 1 := by {
  cases h₁
  cases h₂
  simp_all
  simp_all
  simp_all
}

lemma word_range_val_bound
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
  have b0 : most_sig_byte_decomp_0 = 0 ∨ most_sig_byte_decomp_0 = 1 := bit_value_0_or_1 h₀
  have b1 : most_sig_byte_decomp_1 = 0 ∨ most_sig_byte_decomp_1 = 1 := bit_value_0_or_1 h₁
  have b2 : most_sig_byte_decomp_2 = 0 ∨ most_sig_byte_decomp_2 = 1 := bit_value_0_or_1 h₂
  have b3 : most_sig_byte_decomp_3 = 0 ∨ most_sig_byte_decomp_3 = 1 := bit_value_0_or_1 h₃
  have b4 : most_sig_byte_decomp_4 = 0 ∨ most_sig_byte_decomp_4 = 1 := bit_value_0_or_1 h₄
  have b5 : most_sig_byte_decomp_5 = 0 ∨ most_sig_byte_decomp_5 = 1 := bit_value_0_or_1 h₅
  have b6 : most_sig_byte_decomp_6 = 0 ∨ most_sig_byte_decomp_6 = 1 := bit_value_0_or_1 h₆
  have b7 : most_sig_byte_decomp_7 = 0 ∨ most_sig_byte_decomp_7 = 1 := bit_value_0_or_1 h₇
  -- 2) because bit7 = 0, value_3 ≤ 127
  have v3_le_127 : value_3.val ≤ 127 := by
    { -- value_3 = sum_{i=0..7} bit_i * 2^i and bit7 = 0 so upper bound is when bits0..6 = 1
      rw [← h₉, h₁₀]
      have : most_sig_byte_decomp_0.val + most_sig_byte_decomp_1.val * 2 + most_sig_byte_decomp_2.val * 4 + most_sig_byte_decomp_3.val * 8 +
            most_sig_byte_decomp_4.val * 16 + most_sig_byte_decomp_5.val * 32 + most_sig_byte_decomp_6.val * 64 ≤ 1 + 2 + 4 + 8 + 16 + 32 + 64 := by
      { have b0' : most_sig_byte_decomp_0.val ≤ 1 := bit_le_one (bit_val_to_nat b0)
        have b1' : most_sig_byte_decomp_1.val ≤ 1 := bit_le_one (bit_val_to_nat b1)
        have b2' : most_sig_byte_decomp_2.val ≤ 1 := bit_le_one (bit_val_to_nat b2)
        have b3' : most_sig_byte_decomp_3.val ≤ 1 := bit_le_one (bit_val_to_nat b3)
        have b4' : most_sig_byte_decomp_4.val ≤ 1 := bit_le_one (bit_val_to_nat b4)
        have b5' : most_sig_byte_decomp_5.val ≤ 1 := bit_le_one (bit_val_to_nat b5)
        have b6' : most_sig_byte_decomp_6.val ≤ 1 := bit_le_one (bit_val_to_nat b6)
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
  have c0 := binary_mul_binary_F b0 b1 h₁₁
  have c1 := binary_mul_binary_F c0 b2 h₁₂
  have c2 := binary_mul_binary_F c1 b3 h₁₃
  have c3 := binary_mul_binary_F c2 b4 h₁₄
  have c4 := binary_mul_binary_F c3 b5 h₁₅
  have c5 := bit_val_to_nat (binary_mul_binary_F c4 b6 h₁₆)
  cases c5
  {
    rename_i h
    have : value_3.val < 127 := by {
      by_contra hcontra
      have h_eq : ZMod.val value_3 = 127 := by
        apply le_antisymm v3_le_127
        exact Nat.le_of_not_lt hcontra
      have decomp :
          most_sig_byte_decomp_0 = 1 ∧
          most_sig_byte_decomp_1 = 1 ∧
          most_sig_byte_decomp_2 = 1 ∧
          most_sig_byte_decomp_3 = 1 ∧
          most_sig_byte_decomp_4 = 1 ∧
          most_sig_byte_decomp_5 = 1 ∧
          most_sig_byte_decomp_6 = 1 := by {
          rw[h₁₀] at h₉
          rcases b0 with (rfl | rfl) <;>
          rcases b1 with (rfl | rfl) <;>
          rcases b2 with (rfl | rfl) <;>
          rcases b3 with (rfl | rfl) <;>
          rcases b4 with (rfl | rfl) <;>
          rcases b5 with (rfl | rfl) <;>
          rcases b6 with (rfl | rfl)
          all_goals
            simp at h₉
            rw[← h₉] at h_eq
            try contradiction
          simp
        }
      rcases decomp with ⟨d0, d1, d2, d3, d4, d5, d6⟩
      simp_all
    }
    calc
      value_0.val + value_1.val * 256 + value_2.val * 256^2 + value_3.val * 256^3
          ≤ 255 + 255*256 + 255*256^2 + 126*256^3 := by
            apply Nat.add_le_add
            apply Nat.add_le_add
            apply Nat.add_le_add
            · exact Nat.lt_succ_iff.mp h₂₀
            · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp h₂₁)
            · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp h₂₂)
            · {
              have h_le : value_3.val ≤ 126 := Nat.lt_succ_iff.mp this
              rw [Nat.mul_comm]
              exact Nat.mul_le_mul_left _ h_le
            }
      _ = 2130706431 := by simp
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

lemma eval_eq_then_lt {σ Δ e₁ e₂ e₃}
  (h₁: Eval.EvalProp σ Δ (Ast.exprEq e₁ e₂) (Ast.Value.vBool true))
  (h₂: Eval.EvalProp σ Δ (Ast.Expr.binRel (Ast.Expr.toZ e₂) Ast.RelOp.lt e₃) (Ast.Value.vBool true))
  : Eval.EvalProp σ Δ (Ast.Expr.binRel (Ast.Expr.toZ e₁) Ast.RelOp.lt e₃) (Ast.Value.vBool true) := by {
    cases h₂
    rename_i ih₁ ih₂ r
    cases ih₁
    rename_i h
    cases h₁
    rename_i ih₁ ih₂ r
    have hv := evalprop_deterministic h ih₂
    rename_i ev₃ hev₃ v₂ hlt ev₁ ev₂
    unfold Eval.evalRelOp at hlt
    simp at hlt
    cases ev₃ with
    | vZ v₃ => {
      simp at hlt
      rw[← hv] at r
      unfold Eval.evalRelOp at r
      simp at r
      cases ev₁ with
      | vF v₁ => {
        simp at r
        apply Eval.EvalProp.Rel
        apply Eval.EvalProp.toZ
        exact ih₁
        exact hev₃
        unfold Eval.evalRelOp
        simp
        rw[r]
        exact hlt
      }
      | _ => simp at r
    }
    | _ => simp at hlt
  }

lemma eval_mul_expr_val {σ x y z Δ} (h: Eval.EvalProp σ Δ
  (Ast.exprEq (Ast.Expr.var x)
    ((Ast.Expr.var y).fieldExpr Ast.FieldOp.mul (Ast.Expr.var z)))
  (Ast.Value.vBool true)) :
  ∃ v₁ v₂ v₃: F, Env.lookupVal σ x = some (Ast.Value.vF v₁) ∧
                 Env.lookupVal σ y = some (Ast.Value.vF v₂) ∧
                 Env.lookupVal σ z = some (Ast.Value.vF v₃) ∧
                 (v₁ = v₂ * v₃) := by {
    cases h
    rename_i v₁ v₂ ih₁ ih₂ r₂
    cases ih₁
    cases ih₂
    rename_i v₃ v₄ ih₁ ih₂ r₂'
    cases ih₁
    cases ih₂
    cases r₂'
    simp at r₂
    cases v₁ with
    | vF vf₁ => {
      simp at r₂
      use vf₁
      use v₃
      use v₄
      apply And.intro
      simp_all
      apply And.intro
      simp_all
      apply And.intro
      simp_all
      exact r₂
    }
    | _ => simp at r₂
                 }

lemma eval_bit_expr_val {σ Δ x} (h: Eval.EvalProp σ Δ
  (Ast.exprEq
    ((Ast.Expr.var x).fieldExpr Ast.FieldOp.mul
      ((Ast.Expr.var x).fieldExpr Ast.FieldOp.sub (Ast.Expr.constF 1)))
    (Ast.Expr.constF 0))
  (Ast.Value.vBool true)) : ∃ v: F, Env.lookupVal σ x = some (Ast.Value.vF v) ∧ (v = 0 ∨ v - 1 = 0) := by {
    cases h
    rename_i ih₁ ih₂ r₁;
    cases ih₁;
    rename_i ih₃ ih₄ r₂;
    cases ih₂;
    cases ih₃;
    cases ih₄;
    rename_i ih₁ ih₂ r₂;
    cases ih₁;
    cases ih₂;
    cases r₂;
    simp at r₂;
    unfold Eval.evalRelOp at r₁;
    simp at r₁;
    rw [← r₂] at r₁;
    simp at r₁;
    rename_i v₁ vf₁ h₁ vf₂ h₂
    use vf₁
    have h_eq : vf₁ = vf₂ := by {
      rw[h₂] at h₁
      simp_all
    }
    rw [← h_eq] at r₁
    apply And.intro
    simp_all
    exact r₁
  }

lemma eval_eq_const_mul_val {σ Δ x y v} (h: Eval.EvalProp σ Δ
  (Ast.exprEq (Ast.Expr.constF v)
    ((Ast.Expr.var x).fieldExpr Ast.FieldOp.mul (Ast.Expr.var y)))
  (Ast.Value.vBool true)):
  ∃ v₀ v₁: F,
  Env.lookupVal σ x = some (Ast.Value.vF v₀) ∧ Env.lookupVal σ y = some (Ast.Value.vF v₁) ∧
  v = v₀ * v₁ := by {
    cases h
    rename_i v₈ u₈ ih₁ ih₂ r₈
    cases ih₁
    cases ih₂
    rename_i v₈' u₈' ih₁ ih₂ r₈'
    cases ih₁
    cases ih₂
    unfold Eval.evalFieldOp at r₈'
    simp at r₈'
    unfold Eval.evalRelOp at r₈
    cases u₈ <;> simp at r₈
    use v₈'
    use u₈'
    simp_all
  }

lemma eval_bits_to_byte_expr_val {σ Δ x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈} (h: Eval.EvalProp σ Δ
  (Ast.exprEq
    (bits_to_byte_expr x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇)
    (Ast.Expr.var x₈))
  (Ast.Value.vBool true)) : ∃ v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈: F,
    Env.lookupVal σ x₀ = some (Ast.Value.vF v₀) ∧ Env.lookupVal σ x₁ = some (Ast.Value.vF v₁) ∧
    Env.lookupVal σ x₂ = some (Ast.Value.vF v₂) ∧ Env.lookupVal σ x₃ = some (Ast.Value.vF v₃) ∧
    Env.lookupVal σ x₄ = some (Ast.Value.vF v₄) ∧ Env.lookupVal σ x₅ = some (Ast.Value.vF v₅) ∧
    Env.lookupVal σ x₆ = some (Ast.Value.vF v₆) ∧ Env.lookupVal σ x₇ = some (Ast.Value.vF v₇) ∧
    Env.lookupVal σ x₈ = some (Ast.Value.vF v₈) ∧
    v₀ + v₁ * 2 + v₂ * 4 + v₃ * 8 + v₄ * 16 + v₅ * 32 + v₆ * 64 + v₇ * 128 = v₈ := by {
    cases h
    rename_i ih₁ ih₂ r₁
    cases ih₁
    rename_i ih₃ ih₄ r₂
    cases ih₂
    cases ih₃
    rename_i ih₇ ih₈ r₄
    cases ih₄
    rename_i ih₉ ih₁₀ r₅
    cases ih₇
    rename_i ih₁₃ ih₁₄ r₇
    cases ih₈
    rename_i ih₁₅ ih₁₆ r₈
    cases ih₉
    cases ih₁₀
    cases ih₁₃
    rename_i ih₁₇ ih₁₈ r₉
    cases ih₁₄
    rename_i ih₁₉ ih₂₀ r₁₀
    cases ih₁₅
    cases ih₁₆
    cases ih₁₇
    rename_i ih₂₁ ih₂₂ r₁₁
    cases ih₁₈
    rename_i ih₂₂ ih₂₃ r₁₂
    cases ih₁₉
    cases ih₂₀
    cases ih₂₁
    rename_i ih₂₄ ih₂₅ r₁₃
    cases ih₂₂
    cases ih₂₃
    cases ih₂₄
    rename_i ih₂₅ ih₂₆ r₁₄
    cases ih₂₅
    cases ih₂₆
    rename_i ih₂₇ ih₂₈ r₁₅
    cases ih₂₇
    cases ih₂₈
    cases ih₂₂
    rename_i ih₂₉ ih₃₀ r₁₆
    cases ih₂₉
    cases ih₃₀
    cases ih₂₅
    rename_i ih₃₁ ih₃₂ r₁₇
    cases ih₃₁
    cases ih₃₂
    unfold Eval.evalFieldOp at r₂ r₄ r₅ r₇ r₈ r₉ r₁₀ r₁₁ r₁₂ r₁₃ r₁₄ r₁₅
    simp at r₂ r₄ r₅ r₇ r₈ r₉ r₁₀ r₁₁ r₁₂ r₁₃ r₁₄ r₁₅ r₁₆ r₁₇
    rw[← r₁₅] at r₁₄
    rw[← r₁₄] at r₁₃
    rw[← r₁₃] at r₁₁
    rw[← r₁₂] at r₉
    rw[← r₁₁] at r₉
    rw[← r₁₀] at r₇
    rw[← r₉] at r₇
    rw[← r₈] at r₄
    rw[← r₇] at r₄
    rw[← r₁₆] at r₄
    rw[← r₅] at r₂
    rw[← r₄] at r₂
    rw[← r₁₇] at r₂
    rename_i e₀ v₀ fff₀ fff₁ v₂ ff₀ ff₁ ff₂ ff₃ ff₄ ff₅ h₀ f₀ f₁ f₂ h₁ f₃ f₄ f₅ h₂ f₆ f₇ h₃ f₈ f₉ h₄ f₁₀ h₅ f₁₁ h₆ f₁₂ h₇
    unfold Eval.evalRelOp at r₁
    rw[← r₂] at r₁
    cases v₀ <;> simp at r₁;
    rename_i v₉
    use f₈
    use f₁₀
    use f₁₂
    use f₁₁
    use f₅
    use f₂
    use ff₅
    use ff₂
    use v₉
    simp_all
  }

lemma tyenv_to_eval_expr {σ Δ Γ x e} (h₁: PropSemantics.tyenvToProp σ Δ Γ) (h₂: Env.lookupTy Γ x = some (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.ind e))):
  (Eval.EvalProp σ Δ e (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp PropSemantics.varToProp PropSemantics.predToProp at h₁
    have h₁' := h₁ x (Ast.Ty.unit.refin (Ast.Predicate.ind e)) h₂
    rw[h₂] at h₁'
    simp at h₁'
    unfold PropSemantics.exprToProp at h₁'
    exact h₁'
  }

lemma tyenv_and_to_eval_exprs {σ Δ Γ x e₁ e₂} (h₁: PropSemantics.tyenvToProp σ Δ Γ) (h₂: Env.lookupTy Γ x = some (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂)))):
  (Eval.EvalProp σ Δ e₁ (Ast.Value.vBool true)) ∧ (Eval.EvalProp σ Δ e₂ (Ast.Value.vBool true)) := by {
    unfold PropSemantics.tyenvToProp PropSemantics.varToProp PropSemantics.predToProp at h₁
    have h₁' := h₁ x (Ast.Ty.refin Ast.Ty.unit (Ast.Predicate.and (Ast.Predicate.ind e₁) (Ast.Predicate.ind e₂))) h₂
    rw[h₂] at h₁'
    simp at h₁'
    unfold PropSemantics.predToProp PropSemantics.exprToProp at h₁'
    exact h₁'
  }

lemma eval_lt_val {σ Δ x t} (h: Eval.EvalProp σ Δ ((Ast.Expr.var x).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ t)) (Ast.Value.vBool true)):
  ∃ v : F, Env.lookupVal σ x = some (Ast.Value.vF v) ∧ v.val < t := by {
    cases h
    rename_i ih₀ ih₁ r₁
    cases ih₀
    rename_i ih₀
    cases ih₀
    cases ih₁
    unfold Eval.evalRelOp at r₁
    simp at r₁
    rename_i v h
    use v
    simp_all
  }

lemma lookup_u8_val_lt_256
  (h₁: PropSemantics.tyenvToProp σ Δ Γ)
  (h₂: Env.lookupTy Γ u = some ((Ast.Ty.unit.refin
          (Ty.lookup_pred [(Ast.Expr.var x, Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
            (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
            Η))))
  (h₃: (Env.freshName Η (Env.lookupCircuit Δ "u8").ident_i) = new_ident_i)
  (h₄: (Env.freshName Η (Env.lookupCircuit Δ "u8").ident_t) = new_ident_t)
  (h₇: new_ident_t ≠ "i") :  ∃ v : F, Env.lookupVal σ x = some (Ast.Value.vF v) ∧ v.val < 256 := by {
    unfold Ty.lookup_pred at h₂
    have hu8_i : (Env.lookupCircuit Δ "u8").ident_i = "i" := by {
      unfold Env.lookupCircuit Δ
      simp
    }
    have hu8_t : (Env.lookupCircuit Δ "u8").ident_t = "trace" := by {
      unfold Env.lookupCircuit Δ
      simp
    }

    --rw[hu8_i] at h₃
    --rw[hu8_t] at h₄
    rw[h₃, h₄, hu8_i, hu8_t] at h₂
    -- Ast.renameVarinPred Ast.renameVar Env.freshName
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

lemma subtype_wordrage_check
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
            (Ty.lookup_pred [(Ast.Expr.var "value_0", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
              (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]))))
  ( hl₁: Env.lookupTy Γ "l₁" = some (        (Ast.Ty.unit.refin
          (Ty.lookup_pred [(Ast.Expr.var "value_1", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
            (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t])))))
  ( hl₂: Env.lookupTy Γ "l₂" =       (Ast.Ty.unit.refin
        (Ty.lookup_pred [(Ast.Expr.var "value_2", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
          (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
          (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t])))))
  ( hl₃: Env.lookupTy Γ "l₃" = (Ast.Ty.unit.refin
      (Ty.lookup_pred [(Ast.Expr.var "value_3", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
        (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
        (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
          (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]))))))
  : @Ty.SubtypeJudgment σ Δ Γ (Ast.Ty.unit.refin
      (Ty.lookup_pred [(Ast.Expr.var "value_3", Ast.trace_i_j "trace" "i" 0)] (Env.lookupCircuit Δ "u8")
        (Ast.Predicate.ind ((Ast.trace_i_j "trace" "i" 0).toZ.binRel Ast.RelOp.lt (Ast.Expr.constZ 256)))
        (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
          (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]))))) wordRangeCheckerCircuit.goal := by {
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

    have hu8_i : (Env.lookupCircuit Δ "u8").ident_i = "i" := by {
      unfold Env.lookupCircuit Δ
      simp
    }
    have hu8_t : (Env.lookupCircuit Δ "u8").ident_t = "trace" := by {
      unfold Env.lookupCircuit Δ
      simp
    }
    have h₁' : (Env.freshName [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t] (Env.lookupCircuit Δ "u8").ident_t) = "trace'" := by {
      unfold Env.freshName
      rw[hu8_t]
      simp
    }
    have h₂' : (Env.freshName [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t] (Env.lookupCircuit Δ "u8").ident_i) = "i'" := by {
      unfold Env.freshName
      rw[hu8_i]
      simp
    }
    have h₃' : "trace'" ≠ "i" := by simp
    have hl₀' := tyenv_and_to_eval_exprs h₁ hl₀
    have hvl₀ := lookup_u8_val_lt_256 h₁ hl₀ h₂' h₁' h₃'
    have h₁' : (Env.freshName (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]) (Env.lookupCircuit Δ "u8").ident_t) = "trace'" := by {
      unfold Env.freshName
      rw[hu8_t]
      simp
      unfold Ty.update_UsedNames
      simp
    }
    have h₂' : (Env.freshName (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]) (Env.lookupCircuit Δ "u8").ident_i) = "i'" := by {
      unfold Env.freshName
      rw[hu8_i]
      simp
      unfold Ty.update_UsedNames
      simp
    }
    have hl₁' := tyenv_and_to_eval_exprs h₁ hl₁
    have hvl₁ := lookup_u8_val_lt_256 h₁ hl₁ h₂' h₁' h₃'
    have h₁' : (Env.freshName (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
          (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]))) (Env.lookupCircuit Δ "u8").ident_t) = "trace'" := by {
      unfold Env.freshName
      rw[hu8_t]
      simp
      unfold Ty.update_UsedNames
      simp
    }
    have h₂' : (Env.freshName (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
          (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
            (Ty.update_UsedNames (Env.lookupCircuit Δ "u8")
              [wordRangeCheckerCircuit.ident_i, wordRangeCheckerCircuit.ident_t]))) (Env.lookupCircuit Δ "u8").ident_i) = "i'" := by {
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
          apply Eval.EvalProp.Var
          exact h_value_0_env
        . apply Eval.EvalProp.ZBinOp
          . apply Eval.EvalProp.toZ
            apply Eval.EvalProp.Var
            exact h_value_1_env
          . apply Eval.EvalProp.ConstZ
          . unfold Eval.evalIntegerOp
            simp
            rfl
        . unfold Eval.evalIntegerOp
          simp
          rfl
        . apply Eval.EvalProp.ZBinOp
          . apply Eval.EvalProp.toZ
            apply Eval.EvalProp.Var
            exact h_value_2_env
          . apply Eval.EvalProp.ConstZ
          . unfold Eval.evalIntegerOp
            simp
            rfl
        . unfold Eval.evalIntegerOp
          simp
          rfl
      . apply Eval.EvalProp.ZBinOp
        . apply Eval.EvalProp.toZ
          apply Eval.EvalProp.Var
          exact h_value_3_env
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
      simp
      exact h_most_sig_byte_decomp_0
      simp
      exact h_most_sig_byte_decomp_1
      simp
      exact h_most_sig_byte_decomp_2
      simp
      exact h_most_sig_byte_decomp_3
      simp
      exact h_most_sig_byte_decomp_4
      simp
      exact h_most_sig_byte_decomp_5
      simp
      exact h_most_sig_byte_decomp_6
      simp
      exact h_most_sig_byte_decomp_7
      exact h_msb_rec
      exact h_most_sig_byte_decomp_7_is_0
      exact hamm₁
      exact hamm₂
      exact hamm₃
      exact hamm₄
      exact hamm₅
      exact hamm₆
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
    apply Ty.TypeJudgment.TE_SUB
    apply subtype_wordrage_check
    repeat
      apply lookup_update_ne
      simp
    apply lookup_update_self
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
