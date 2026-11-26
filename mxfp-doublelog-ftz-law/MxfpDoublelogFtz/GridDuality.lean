/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxfpDoublelogFtz.RatOrder

/-!
# Theorem 1: Universal `E1`/`E0` Grid Equivalence & Signed–Unsigned Microscaling Duality

Proves for ALL bitwidths `w ≥ 4`:
1. IEEE-subnormal full-finite `E1 M_{w-2}` has the IDENTICAL integer and normalized rational
   quantization grid as `E0 M_{w-1}` (`INT_w`).
2. Unsigned `w`-bit `U-E_a M_b` (`a + b = w`) has the IDENTICAL nonnegative integer and
   normalized rational quantization grid as signed `(w + 1)`-bit `S-E_a M_b`.
-/

namespace MxfpDoublelogFtz

/-- Pointwise `E1`/`E0` code equivalence: for every `b` and every `code < 2 ^ (b + 1)`,
full-finite gradual-underflow `E1 M_b` decodes to the exact same integer value as `E0 M_{b+1}` (`code`). -/
theorem mxfpCodeValue_e1_eq_e0 (b code : Nat) (hcode : code < 2 ^ (b + 1)) :
    mxfpCodeValue 1 b code = mxfpCodeValue 0 (b + 1) code := by
  unfold mxfpCodeValue
  simp only [Nat.one_ne_zero, ↓reduceIte]
  have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by
    rw [Nat.pow_succ]
    omega
  have hpos : 0 < 2 ^ b := nat_pow2_pos b
  have hdiv : code / 2 ^ b < 2 := by
    have hlt : code < 2 ^ b * 2 := by omega
    exact Nat.div_lt_of_lt_mul hlt
  by_cases h0 : code / 2 ^ b = 0
  · simp only [h0, ↓reduceIte]
    have hlt : code < 2 ^ b := by
      have hdm := Nat.div_add_mod code (2 ^ b)
      rw [h0] at hdm
      have hmod := Nat.mod_lt code hpos
      omega
    exact Nat.mod_eq_of_lt hlt
  · have h1 : code / 2 ^ b = 1 := by
      have hge : 1 ≤ code / 2 ^ b := Nat.pos_of_ne_zero h0
      exact Nat.le_antisymm (Nat.le_of_lt_succ hdiv) hge
    simp only [h1, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    have hdm := Nat.div_add_mod code (2 ^ b)
    rw [h1] at hdm
    omega

/-- Maximum integer value of `E1 M_{w - 2}` equals `E0 M_{w - 1}` for all `w ≥ 2`. -/
theorem mxfpMaxInt_e1_eq_e0 (w : Nat) (hw : 2 ≤ w) :
    mxfpMaxInt 1 (w - 2) = mxfpMaxInt 0 (w - 1) := by
  unfold mxfpMaxInt
  simp only [Nat.one_ne_zero, ↓reduceIte]
  have hsub : w - 2 + 1 = w - 1 := by omega
  rw [hsub]
  simp

/-- Exact bit-for-bit integer grid equality `E1 M_{w-2} = E0 M_{w-1}` for all `w ≥ 4`. -/
theorem mxfpSignedGrid_e1_eq_e0 (w : Nat) (hw : 4 ≤ w) :
    mxfpSignedGrid w 1 = mxfpSignedGrid w 0 := by
  unfold mxfpSignedGrid
  have hsub1 : w - 1 - 1 = w - 2 := by omega
  have hsub0 : w - 1 - 0 = w - 1 := by omega
  rw [hsub1, hsub0]
  apply List.map_congr_left
  intro code hmem
  have hlt : code < 2 ^ (w - 1) := List.mem_range.mp hmem
  have hsub : w - 2 + 1 = w - 1 := by omega
  have hlt' : code < 2 ^ (w - 2 + 1) := by rw [hsub]; exact hlt
  have heq := mxfpCodeValue_e1_eq_e0 (w - 2) code hlt'
  rw [hsub] at heq
  exact heq

/-- Exact normalized rational grid equality `E1 M_{w-2} = E0 M_{w-1}` for all `w ≥ 4`. -/
theorem mxfpSignedNormGrid_e1_eq_e0 (w : Nat) (hw : 4 ≤ w) :
    mxfpSignedNormGrid w 1 = mxfpSignedNormGrid w 0 := by
  unfold mxfpSignedNormGrid
  have hsub1 : w - 1 - 1 = w - 2 := by omega
  have hsub0 : w - 1 - 0 = w - 1 := by omega
  rw [hsub1, hsub0]
  rw [mxfpMaxInt_e1_eq_e0 w (by omega)]
  rw [mxfpSignedGrid_e1_eq_e0 w hw]

/-- Exact Signed–Unsigned Microscaling Duality: unsigned `w`-bit `U-E_a M_{w - a}` has the
IDENTICAL nonnegative integer grid as signed `(w + 1)`-bit `S-E_a M_{(w + 1) - 1 - a}`. -/
theorem mxfpUnsignedGrid_eq_signed_succ (w a : Nat) :
    mxfpUnsignedGrid w a = mxfpSignedGrid (w + 1) a := by
  unfold mxfpUnsignedGrid mxfpSignedGrid
  simp

/-- Exact Signed–Unsigned Microscaling Duality for normalized rational grids. -/
theorem mxfpUnsignedNormGrid_eq_signed_succ (w a : Nat) :
    mxfpUnsignedNormGrid w a = mxfpSignedNormGrid (w + 1) a := by
  unfold mxfpUnsignedNormGrid mxfpSignedNormGrid
  simp [mxfpUnsignedGrid_eq_signed_succ]

/-- **Headline Theorem 1:** Universal `E1`/`E0` Grid Equivalence (`∀ w ≥ 4`) and
Signed–Unsigned Microscaling Duality (`∀ w a`, `U_w` grid ≡ Signed `w+1` grid). -/
theorem mxfp_e1_equals_e0_and_signed_unsigned_duality :
    (∀ w : Nat, 4 ≤ w →
      mxfpMaxInt 1 (w - 2) = 2 ^ (w - 1) - 1 ∧
      mxfpMaxInt 1 (w - 2) = mxfpMaxInt 0 (w - 1) ∧
      (∀ code : Nat, code < 2 ^ (w - 1) →
        mxfpCodeValue 1 (w - 2) code = mxfpCodeValue 0 (w - 1) code) ∧
      mxfpSignedGrid w 1 = mxfpSignedGrid w 0 ∧
      mxfpSignedNormGrid w 1 = mxfpSignedNormGrid w 0) ∧
    (∀ w a : Nat,
      mxfpUnsignedGrid w a = mxfpSignedGrid (w + 1) a ∧
      mxfpUnsignedNormGrid w a = mxfpSignedNormGrid (w + 1) a) := by
  constructor
  · intro w hw
    refine ⟨?_, mxfpMaxInt_e1_eq_e0 w (by omega), ?_, mxfpSignedGrid_e1_eq_e0 w hw,
      mxfpSignedNormGrid_e1_eq_e0 w hw⟩
    · rw [mxfpMaxInt_e1_eq_e0 w (by omega)]
      rfl
    · intro code hlt
      have hsub : w - 2 + 1 = w - 1 := by omega
      have hlt' : code < 2 ^ (w - 2 + 1) := by rw [hsub]; exact hlt
      have heq := mxfpCodeValue_e1_eq_e0 (w - 2) code hlt'
      rw [hsub] at heq
      exact heq
  · intro w a
    exact ⟨mxfpUnsignedGrid_eq_signed_succ w a, mxfpUnsignedNormGrid_eq_signed_succ w a⟩

end MxfpDoublelogFtz
