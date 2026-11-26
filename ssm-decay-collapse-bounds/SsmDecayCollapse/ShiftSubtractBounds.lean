/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse.RatZpow

/-!
# Theorems 4 & 5: Zero-Multiplier Signed Shift-Subtract Tight Bounds & Zero-Input Stall Asymmetry

Proves for the zero-multiplier 1-tap signed integer shift-subtract recurrence
`shiftSubStep r h b = h - Int.fdiv h (2^r) + b` (floor division = arithmetic right shift `>>> r`):
1. **Theorem 4 (`dyadic_shift_subtract_tight_bounds`):**
   - Exact invariant interval `[-2^R * Bmax, 2^R * Bmax + (2^R - 1)]` preserved for all
     `1 ≤ r ≤ R` and all `|b| ≤ Bmax` (`0 ≤ Bmax`).
   - Exact tight attainment of BOTH endpoints at `r = R`:
     `shiftSubStep R (shiftSubMax R Bmax) Bmax = shiftSubMax R Bmax` and
     `shiftSubStep R (shiftSubMin R Bmax) (-Bmax) = shiftSubMin R Bmax`.
   - Exact signed asymmetry: `shiftSubMax R Bmax + shiftSubMin R Bmax = 2^R - 1`.
2. **Theorem 5 (`dyadic_shift_subtract_zero_input_stall_asymmetry`):**
   - Under zero input (`b = 0`) and `r ≥ 1`:
     - Every state `0 ≤ h < 2^r` is an exact fixed point (`shiftSubStep r h 0 = h` and
       `∀ n, shiftSubIter r h n = h`).
     - Every strictly negative state `h < 0` strictly increases (`h < shiftSubStep r h 0`),
       stays `≤ 0` (`shiftSubStep r h 0 ≤ 0`), and reaches `0` in finitely many steps
       (`shiftSubIter r h h.natAbs = 0`).
-/

namespace SsmDecayCollapse

theorem int_fdiv_spec (h : Int) {d : Int} (hd : 0 < d) :
    h = d * Int.fdiv h d + h.emod d ∧ 0 ≤ h.emod d ∧ h.emod d < d := by
  have heq : Int.fdiv h d = h.ediv d := Int.fdiv_eq_ediv_of_nonneg h (by omega)
  rw [heq]
  exact ⟨(Int.mul_ediv_add_emod h d).symm, Int.emod_nonneg h (by omega), Int.emod_lt_of_pos h hd⟩

theorem int_fdiv_eq_of_bounds {h d q : Int} (hd : 0 < d)
    (hlo : d * q ≤ h) (hhi : h < d * (q + 1)) : Int.fdiv h d = q := by
  have ⟨hdiv, hr0, hrd⟩ := int_fdiv_spec h hd
  have hlo' : d * q < d * (Int.fdiv h d + 1) := by
    have : d * (Int.fdiv h d + 1) = d * Int.fdiv h d + d := by grind
    omega
  have hhi' : d * Int.fdiv h d < d * (q + 1) := by omega
  have h1 : q < Int.fdiv h d + 1 :=
    int_lt_of_mul_lt_mul_right hd (by rw [Int.mul_comm q d, Int.mul_comm (Int.fdiv h d + 1) d]; exact hlo')
  have h2 : Int.fdiv h d < q + 1 :=
    int_lt_of_mul_lt_mul_right hd (by rw [Int.mul_comm (Int.fdiv h d) d, Int.mul_comm (q + 1) d]; exact hhi')
  omega

theorem sub_fdiv_mono {h1 h2 d : Int} (hd : 0 < d) (hle : h1 ≤ h2) :
    h1 - Int.fdiv h1 d ≤ h2 - Int.fdiv h2 d := by
  have ⟨hdiv1, hr1_lo, hr1_hi⟩ := int_fdiv_spec h1 hd
  have ⟨hdiv2, hr2_lo, hr2_hi⟩ := int_fdiv_spec h2 hd
  have hq_le : Int.fdiv h1 d ≤ Int.fdiv h2 d := by
    by_cases hgt : Int.fdiv h2 d < Int.fdiv h1 d
    · have h1' : Int.fdiv h2 d + 1 ≤ Int.fdiv h1 d := by omega
      have hmul : d * (Int.fdiv h2 d + 1) ≤ d * Int.fdiv h1 d :=
        Int.mul_le_mul_of_nonneg_left h1' (by omega)
      have hexp : d * (Int.fdiv h2 d + 1) = d * Int.fdiv h2 d + d := by grind
      omega
    · omega
  have hf1 : h1 - Int.fdiv h1 d = (d - 1) * Int.fdiv h1 d + h1.emod d := by grind
  have hf2 : h2 - Int.fdiv h2 d = (d - 1) * Int.fdiv h2 d + h2.emod d := by grind
  rw [hf1, hf2]
  by_cases heq : Int.fdiv h1 d = Int.fdiv h2 d
  · rw [heq] at hdiv1 ⊢
    omega
  · have hlt : Int.fdiv h1 d + 1 ≤ Int.fdiv h2 d := by omega
    have hmul : (d - 1) * (Int.fdiv h1 d + 1) ≤ (d - 1) * Int.fdiv h2 d :=
      Int.mul_le_mul_of_nonneg_left hlt (by omega)
    have hexp : (d - 1) * (Int.fdiv h1 d + 1) = (d - 1) * Int.fdiv h1 d + (d - 1) := by grind
    omega

theorem shiftSubStep_fdiv_max {r R : Nat} (hrR : r ≤ R) (Bmax : Int) :
    Int.fdiv (shiftSubMax R Bmax) ((2 ^ r : Nat) : Int) =
      ((2 ^ (R - r) : Nat) : Int) * Bmax + (((2 ^ (R - r) : Nat) : Int) - 1) := by
  have hd : (0 : Int) < ((2 ^ r : Nat) : Int) := by
    have := nat_two_pow_pos r; omega
  have hpow : 2 ^ R = 2 ^ r * 2 ^ (R - r) := by
    rw [← Nat.pow_add]
    have : r + (R - r) = R := by omega
    rw [this]
  have hpowI : ((2 ^ R : Nat) : Int) = ((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int) := by
    rw [hpow, Int.natCast_mul]
  apply int_fdiv_eq_of_bounds hd
  · unfold shiftSubMax
    rw [hpowI]
    have hlo : ((2 ^ r : Nat) : Int) * (((2 ^ (R - r) : Nat) : Int) * Bmax + (((2 ^ (R - r) : Nat) : Int) - 1)) =
        ((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int) * Bmax +
          ((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int) - ((2 ^ r : Nat) : Int) := by grind
    omega
  · unfold shiftSubMax
    rw [hpowI]
    have hhi : ((2 ^ r : Nat) : Int) * (((2 ^ (R - r) : Nat) : Int) * Bmax + (((2 ^ (R - r) : Nat) : Int) - 1) + 1) =
        ((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int) * Bmax +
          ((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int) := by grind
    omega

theorem shiftSubStep_fdiv_min {r R : Nat} (hrR : r ≤ R) (Bmax : Int) :
    Int.fdiv (shiftSubMin R Bmax) ((2 ^ r : Nat) : Int) =
      -((2 ^ (R - r) : Nat) : Int) * Bmax := by
  have hd : (0 : Int) < ((2 ^ r : Nat) : Int) := by
    have := nat_two_pow_pos r; omega
  have hpow : 2 ^ R = 2 ^ r * 2 ^ (R - r) := by
    rw [← Nat.pow_add]
    have : r + (R - r) = R := by omega
    rw [this]
  have hpowI : ((2 ^ R : Nat) : Int) = ((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int) := by
    rw [hpow, Int.natCast_mul]
  apply int_fdiv_eq_of_bounds hd
  · unfold shiftSubMin
    rw [hpowI]
    have heq : ((2 ^ r : Nat) : Int) * (-((2 ^ (R - r) : Nat) : Int) * Bmax) =
        -(((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int)) * Bmax := by grind
    omega
  · unfold shiftSubMin
    rw [hpowI]
    have heq : ((2 ^ r : Nat) : Int) * (-((2 ^ (R - r) : Nat) : Int) * Bmax + 1) =
        -(((2 ^ r : Nat) : Int) * ((2 ^ (R - r) : Nat) : Int)) * Bmax + ((2 ^ r : Nat) : Int) := by grind
    omega

theorem shiftSubStep_invariant {r R : Nat} {Bmax h b : Int}
    (hrR : r ≤ R) (hB : 0 ≤ Bmax)
    (hh_lo : shiftSubMin R Bmax ≤ h) (hh_hi : h ≤ shiftSubMax R Bmax)
    (hb_lo : -Bmax ≤ b) (hb_hi : b ≤ Bmax) :
    shiftSubMin R Bmax ≤ shiftSubStep r h b ∧ shiftSubStep r h b ≤ shiftSubMax R Bmax := by
  have hd : (0 : Int) < ((2 ^ r : Nat) : Int) := by
    have := nat_two_pow_pos r; omega
  have hk_ge : (1 : Int) ≤ ((2 ^ (R - r) : Nat) : Int) := by
    have := nat_two_pow_pos (R - r); omega
  have hkB : Bmax ≤ ((2 ^ (R - r) : Nat) : Int) * Bmax := by
    have hmul := Int.mul_le_mul_of_nonneg_right hk_ge hB
    simpa using hmul
  constructor
  · unfold shiftSubStep
    have hmono := sub_fdiv_mono hd hh_lo
    rw [shiftSubStep_fdiv_min hrR Bmax] at hmono
    have hneg : -((2 ^ (R - r) : Nat) : Int) * Bmax = -(((2 ^ (R - r) : Nat) : Int) * Bmax) := by grind
    omega
  · unfold shiftSubStep
    have hmono := sub_fdiv_mono hd hh_hi
    rw [shiftSubStep_fdiv_max hrR Bmax] at hmono
    omega

/-- Headline Theorem 4 (`dyadic_shift_subtract_tight_bounds`). -/
theorem dyadic_shift_subtract_tight_bounds :
    (∀ (r R : Nat) (Bmax h b : Int),
      1 ≤ r → r ≤ R → 0 ≤ Bmax →
      shiftSubMin R Bmax ≤ h → h ≤ shiftSubMax R Bmax →
      -Bmax ≤ b → b ≤ Bmax →
      shiftSubMin R Bmax ≤ shiftSubStep r h b ∧ shiftSubStep r h b ≤ shiftSubMax R Bmax) ∧
    (∀ (R : Nat) (Bmax : Int),
      shiftSubStep R (shiftSubMax R Bmax) Bmax = shiftSubMax R Bmax ∧
      shiftSubStep R (shiftSubMin R Bmax) (-Bmax) = shiftSubMin R Bmax) ∧
    (∀ (R : Nat) (Bmax : Int),
      shiftSubMax R Bmax + shiftSubMin R Bmax = ((2 ^ R : Nat) : Int) - 1) := by
  refine ⟨fun r R Bmax h b _ hrR hB hlo hhi hblo hbhi =>
    shiftSubStep_invariant hrR hB hlo hhi hblo hbhi, ?_, ?_⟩
  · intro R Bmax
    constructor
    · unfold shiftSubStep
      have hf := shiftSubStep_fdiv_max (Nat.le_refl R) Bmax
      simp only [Nat.sub_self, Nat.pow_zero] at hf
      rw [hf]
      omega
    · unfold shiftSubStep
      have hf := shiftSubStep_fdiv_min (Nat.le_refl R) Bmax
      simp only [Nat.sub_self, Nat.pow_zero] at hf
      rw [hf]
      omega
  · intro R Bmax
    unfold shiftSubMax shiftSubMin
    grind

/-! ### Theorem 5: Zero-Input Signed Stall Asymmetry -/

theorem shiftSubStep_zero_fixed_of_nonneg_lt {r : Nat} {h : Int}
    (h0 : 0 ≤ h) (hlt : h < ((2 ^ r : Nat) : Int)) :
    shiftSubStep r h 0 = h := by
  unfold shiftSubStep
  have hd : (0 : Int) < ((2 ^ r : Nat) : Int) := by
    have := nat_two_pow_pos r; omega
  have hf : Int.fdiv h ((2 ^ r : Nat) : Int) = 0 :=
    int_fdiv_eq_of_bounds hd (by omega) (by simpa using hlt)
  rw [hf]
  omega

theorem shiftSubIter_zero_fixed {r : Nat} {h : Int}
    (h0 : 0 ≤ h) (hlt : h < ((2 ^ r : Nat) : Int)) (n : Nat) :
    shiftSubIter r h n = h := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [shiftSubIter, ih]
    exact shiftSubStep_zero_fixed_of_nonneg_lt h0 hlt

theorem shiftSubStep_zero_strict_inc_of_neg {r : Nat} (hr : 1 ≤ r) {h : Int} (hneg : h < 0) :
    h < shiftSubStep r h 0 ∧ shiftSubStep r h 0 ≤ 0 := by
  unfold shiftSubStep
  have hd : (2 : Int) ≤ ((2 ^ r : Nat) : Int) := by
    obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
    rw [Nat.pow_succ]
    have := nat_two_pow_pos q
    omega
  have hd_pos : (0 : Int) < ((2 ^ r : Nat) : Int) := by omega
  have ⟨hdiv, hr0, hrd⟩ := int_fdiv_spec h hd_pos
  have hq_neg : Int.fdiv h ((2 ^ r : Nat) : Int) ≤ -1 := by
    by_cases h0 : 0 ≤ Int.fdiv h ((2 ^ r : Nat) : Int)
    · have hmul : (0 : Int) ≤ ((2 ^ r : Nat) : Int) * Int.fdiv h ((2 ^ r : Nat) : Int) :=
        Int.mul_nonneg (by omega) h0
      omega
    · omega
  have hle0 : h - Int.fdiv h ((2 ^ r : Nat) : Int) ≤ 0 := by
    have heq : h - Int.fdiv h ((2 ^ r : Nat) : Int) =
        (((2 ^ r : Nat) : Int) - 1) * Int.fdiv h ((2 ^ r : Nat) : Int) + h.emod ((2 ^ r : Nat) : Int) := by grind
    have hmul : (((2 ^ r : Nat) : Int) - 1) * Int.fdiv h ((2 ^ r : Nat) : Int) ≤ -(((2 ^ r : Nat) : Int) - 1) := by
      have := Int.mul_le_mul_of_nonneg_left hq_neg (by omega : (0 : Int) ≤ ((2 ^ r : Nat) : Int) - 1)
      grind
    omega
  omega

theorem shiftSubIter_succ_left (r : Nat) (h : Int) (n : Nat) :
    shiftSubIter r h (n + 1) = shiftSubIter r (shiftSubStep r h 0) n := by
  induction n with
  | zero => rfl
  | succ j ih =>
    change shiftSubStep r (shiftSubIter r h (j + 1)) 0 =
      shiftSubStep r (shiftSubIter r (shiftSubStep r h 0) j) 0
    rw [ih]

theorem shiftSubIter_reaches_zero_of_nonpos {r : Nat} (hr : 1 ≤ r) (k : Nat) :
    ∀ h : Int, -(k : Int) ≤ h → h ≤ 0 → shiftSubIter r h k = 0 := by
  induction k with
  | zero =>
    intro h hlo hhi
    simp only [shiftSubIter]
    omega
  | succ m ih =>
    intro h hlo hhi
    rw [shiftSubIter_succ_left]
    by_cases h0 : h = 0
    · subst h0
      have hd : (0 : Int) < ((2 ^ r : Nat) : Int) := by
        have := nat_two_pow_pos r; omega
      rw [shiftSubStep_zero_fixed_of_nonneg_lt (by omega) hd]
      exact shiftSubIter_zero_fixed (by omega) hd m
    · have hneg : h < 0 := by omega
      have ⟨hinc, hle0⟩ := shiftSubStep_zero_strict_inc_of_neg hr hneg
      exact ih (shiftSubStep r h 0) (by omega) hle0

/-- Headline Theorem 5 (`dyadic_shift_subtract_zero_input_stall_asymmetry`). -/
theorem dyadic_shift_subtract_zero_input_stall_asymmetry :
    (∀ (r : Nat) (h : Int), 0 ≤ h → h < ((2 ^ r : Nat) : Int) →
      shiftSubStep r h 0 = h ∧ ∀ n : Nat, shiftSubIter r h n = h) ∧
    (∀ (r : Nat) (h : Int), 1 ≤ r → h < 0 →
      h < shiftSubStep r h 0 ∧
      shiftSubStep r h 0 ≤ 0 ∧
      ∃ n : Nat, shiftSubIter r h n = 0) := by
  refine ⟨fun r h h0 hlt => ⟨shiftSubStep_zero_fixed_of_nonneg_lt h0 hlt,
    fun n => shiftSubIter_zero_fixed h0 hlt n⟩, ?_⟩
  intro r h hr hneg
  have ⟨hinc, hle0⟩ := shiftSubStep_zero_strict_inc_of_neg hr hneg
  refine ⟨hinc, hle0, h.natAbs, ?_⟩
  apply shiftSubIter_reaches_zero_of_nonpos hr h.natAbs h
  · omega
  · omega

end SsmDecayCollapse
