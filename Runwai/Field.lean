--import Init.Prelude
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic  -- for `Nat.Prime`
import Mathlib.Tactic.NormNum.Core

/-!
# Finite field Fp implementation in Lean4

This file defines a prime field `Fp p` for a given prime `p`, along with
addition, multiplication, negation, inversion (via Fermat's little theorem),
and exponentiation.
-/

-- KoalaBear: 2^31 - 2^24 + 1
@[inline]
def p : Nat := 2130706433

-- TODO: prove this statement as a theorem
axiom p_is_prime: Nat.Prime p

instance : Fact p.Prime := ⟨p_is_prime⟩

instance : NeZero p := ⟨by
  rw[p]
  simp_all
⟩

/-- `F` is the prime field of order `p`, assuming `p` is prime. -/
abbrev F := ZMod p
instance [Fact p.Prime] : Field F := ZMod.instField p
--instance [Fact p.Prime] : Fintype F := ZMod.fintype p
instance [Fact p.Prime] : Inhabited F := ⟨0⟩
instance : CommRing F := ZMod.commRing p
instance : Repr F where
  reprPrec x _ := "F " ++ toString x.val

instance : Lean.ToExpr F where
  toExpr x := Lean.toExpr x.val
  toTypeExpr := Lean.mkApp (Lean.mkConst ``F) (Lean.toExpr p)
