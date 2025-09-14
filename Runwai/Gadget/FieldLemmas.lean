import Runwai.Typing
import Runwai.Gadget.Utils

open Ast

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

lemma bit_value_mul_zero {x: F} (h: x = 0 ∨ x - 1 = 0): x * (x - 1) = 0 := by {
  simp_all
  /-
  rcases h with h_case | h_case
  {
    left
    exact h_case
  }
  {
    right
    simp_all
  }
  -/
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
