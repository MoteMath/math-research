/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonclipAdamwSr.RatOrder

/-!
# Universal `m`-Bit IEEE-754 RNE AdamW Weight-Decay Freeze Radii

Pure-`Init` (zero Mathlib, zero `native_decide`) proof of Theorem 3
(`adamw_weight_decay_freeze_radii_exact`):
For every `m ≥ 1` (covering FP8-E5M2 `m = 2`, FP8-E4M3 `m = 3`, BF16 `m = 7`, FP16 `m = 10`):
1. Total RNE weight-decay freeze holds iff `ρ ≤ 2^{-(m+2)}`.
2. Strictly in `(2^{-(m+2)}, 1 / (2^{m+2} - 2))`, ONLY powers of 2 (`f = 0`) decay while
   every interior mantissa (`1 ≤ f < 2^m`) stays frozen.
3. Universal decay across all normal mantissas holds iff `ρ ≥ 1 / (2^{m+1} + 2)`.
4. Strictly in `(1 / (2^{m+1} + 4), 1 / (2^{m+1} + 2))`, `f = 1` is the unique frozen
   mantissa (last to unfreeze).
-/

namespace MuonclipAdamwSr

private theorem binadeFloat_zero (m : Nat) : binadeFloat m 0 = 1 := by
  unfold binadeFloat pow2Rat
  rw [Nat.add_zero]
  exact (rat_div_eq_iff (pow2Rat_ne_zero m)).mpr (by unfold pow2Rat; grind)

theorem wdFrozenRNE_zero_iff (m : Nat) (ρ : Rat) :
    wdFrozenRNE m 0 ρ ↔ ρ ≤ wdTotalFreezeRadius m := by
  unfold wdFrozenRNE wdLowerMidpoint wdTotalFreezeRadius
  rw [binadeFloat_zero]
  simp only [Nat.zero_mod, ↓reduceIte, Rat.one_mul]
  constructor
  · intro h
    have h1 := rat_sub_nonneg h
    apply rat_le_of_sub_nonneg
    have heq : invPow2Rat (m + 2) - ρ = (1 - ρ) - (1 - invPow2Rat (m + 2)) := by grind
    rw [heq]; exact h1
  · intro h
    have h1 := rat_sub_nonneg h
    apply rat_le_of_sub_nonneg
    have heq : (1 - ρ) - (1 - invPow2Rat (m + 2)) = invPow2Rat (m + 2) - ρ := by grind
    rw [heq]; exact h1

private theorem wd_pos_scaled_diff (m f : Nat) (hf : 1 ≤ f) (ρ : Rat) :
    (binadeFloat m f * (1 - ρ) - wdLowerMidpoint m f) * pow2Rat (m + 1) =
      1 - ((2 * (2 ^ m + f) : Nat) : Rat) * ρ := by
  have hfne : f ≠ 0 := by omega
  unfold binadeFloat wdLowerMidpoint
  simp only [hfne, ↓reduceIte]
  have h2m_ne : pow2Rat m ≠ 0 := pow2Rat_ne_zero m
  have h2m1_ne : pow2Rat (m + 1) ≠ 0 := pow2Rat_ne_zero (m + 1)
  have hsucc : pow2Rat (m + 1) = 2 * pow2Rat m := pow2Rat_succ m
  have h1 : (((2 ^ m + f : Nat) : Rat) / pow2Rat m) * pow2Rat (m + 1) =
      2 * ((2 ^ m + f : Nat) : Rat) := by
    rw [hsucc, Rat.mul_comm 2 (pow2Rat m), ← Rat.mul_assoc, rat_div_mul_cancel h2m_ne,
        Rat.mul_comm]
  have h2 : (((2 * (2 ^ m + f) - 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat (m + 1) =
      ((2 * (2 ^ m + f) - 1 : Nat) : Rat) := rat_div_mul_cancel h2m1_ne
  have hsub_cast : ((2 * (2 ^ m + f) - 1 : Nat) : Rat) =
      ((2 * (2 ^ m + f) : Nat) : Rat) - 1 := by
    have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by decide)
    have hge : 1 ≤ 2 * (2 ^ m + f) := by omega
    have hnat : (2 * (2 ^ m + f) - 1) + 1 = 2 * (2 ^ m + f) := Nat.sub_add_cancel hge
    have hcast : ((2 * (2 ^ m + f) - 1 : Nat) : Rat) + ((1 : Nat) : Rat) =
        ((2 * (2 ^ m + f) : Nat) : Rat) := by
      rw [← Rat.natCast_add, hnat]
    have hone : ((1 : Nat) : Rat) = 1 := rfl
    rw [hone] at hcast
    grind
  have hmul_cast : ((2 * (2 ^ m + f) : Nat) : Rat) = 2 * ((2 ^ m + f : Nat) : Rat) := by
    rw [Rat.natCast_mul]; rfl
  grind

theorem wdFrozenRNE_pos_even_iff (m f : Nat) (hf : 1 ≤ f) (heven : f % 2 = 0) (ρ : Rat) :
    wdFrozenRNE m f ρ ↔ ρ ≤ 1 / ((2 * (2 ^ m + f) : Nat) : Rat) := by
  unfold wdFrozenRNE
  simp only [heven, ↓reduceIte]
  have hpos : (0 : Rat) < pow2Rat (m + 1) := pow2Rat_pos (m + 1)
  have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by decide)
  have hden : (0 : Rat) < ((2 * (2 ^ m + f) : Nat) : Rat) := rat_natCast_pos (by omega)
  constructor
  · intro hle
    have hsub : (0 : Rat) ≤ binadeFloat m f * (1 - ρ) - wdLowerMidpoint m f := rat_sub_nonneg hle
    have hmul : (0 : Rat) ≤ (binadeFloat m f * (1 - ρ) - wdLowerMidpoint m f) * pow2Rat (m + 1) :=
      Rat.mul_nonneg hsub (Rat.le_of_lt hpos)
    rw [wd_pos_scaled_diff m f hf ρ] at hmul
    apply rat_le_div_of_mul_le hden
    have h1 := rat_le_of_sub_nonneg hmul
    rw [Rat.mul_comm]; exact h1
  · intro hle
    have hmul : ρ * ((2 * (2 ^ m + f) : Nat) : Rat) ≤ 1 := by
      have h := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hden)
      rw [rat_div_mul_cancel (Rat.ne_of_gt hden)] at h
      exact h
    have hsub : (0 : Rat) ≤ 1 - ((2 * (2 ^ m + f) : Nat) : Rat) * ρ := by
      apply rat_sub_nonneg
      rw [Rat.mul_comm]; exact hmul
    rw [← wd_pos_scaled_diff m f hf ρ] at hsub
    apply rat_le_of_sub_nonneg
    apply rat_le_of_mul_pos_right hpos
    rw [Rat.zero_mul]; exact hsub

theorem wdFrozenRNE_pos_odd_iff (m f : Nat) (hf : 1 ≤ f) (hodd : f % 2 = 1) (ρ : Rat) :
    wdFrozenRNE m f ρ ↔ ρ < 1 / ((2 * (2 ^ m + f) : Nat) : Rat) := by
  unfold wdFrozenRNE
  have hne : f % 2 ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  have hpos : (0 : Rat) < pow2Rat (m + 1) := pow2Rat_pos (m + 1)
  have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by decide)
  have hden : (0 : Rat) < ((2 * (2 ^ m + f) : Nat) : Rat) := rat_natCast_pos (by omega)
  constructor
  · intro hlt
    have hsub : (0 : Rat) < binadeFloat m f * (1 - ρ) - wdLowerMidpoint m f := rat_sub_pos hlt
    have hmul : (0 : Rat) < (binadeFloat m f * (1 - ρ) - wdLowerMidpoint m f) * pow2Rat (m + 1) :=
      rat_mul_pos hsub hpos
    rw [wd_pos_scaled_diff m f hf ρ] at hmul
    apply rat_lt_div_of_mul_lt hden
    have h1 := rat_lt_of_sub_pos hmul
    rw [Rat.mul_comm]; exact h1
  · intro hlt
    have hmul : ρ * ((2 * (2 ^ m + f) : Nat) : Rat) < 1 := by
      have h := rat_mul_lt_mul_of_pos_right hlt hden
      rw [rat_div_mul_cancel (Rat.ne_of_gt hden)] at h
      exact h
    have hsub : (0 : Rat) < 1 - ((2 * (2 ^ m + f) : Nat) : Rat) * ρ := by
      apply rat_sub_pos
      rw [Rat.mul_comm]; exact hmul
    rw [← wd_pos_scaled_diff m f hf ρ] at hsub
    apply rat_lt_of_sub_pos
    apply rat_lt_of_mul_pos_right hpos
    rw [Rat.zero_mul]; exact hsub

private theorem inv_lt_inv_nat {a b : Nat} (ha : 0 < a) (hab : a < b) :
    (1 : Rat) / (b : Rat) < (1 : Rat) / (a : Rat) := by
  apply rat_div_lt_div_of_cross (rat_natCast_pos (by omega)) (rat_natCast_pos ha)
  rw [Rat.one_mul, Rat.one_mul]
  exact rat_natCast_lt hab

private theorem inv_le_inv_nat {a b : Nat} (ha : 0 < a) (hab : a ≤ b) :
    (1 : Rat) / (b : Rat) ≤ (1 : Rat) / (a : Rat) := by
  apply rat_div_le_div_of_cross (rat_natCast_pos (by omega)) (rat_natCast_pos ha)
  rw [Rat.one_mul, Rat.one_mul]
  exact rat_natCast_le hab

private theorem two_pow_ge_two {m : Nat} (hm : 1 ≤ m) : 2 ≤ 2 ^ m := by
  have h : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  simpa using h

/-! ### Theorem 3: `adamw_weight_decay_freeze_radii_exact` -/

theorem adamw_weight_decay_freeze_radii_exact :
    (∀ m : Nat, 1 ≤ m →
      (∀ ρ : Rat, (∀ f : Nat, f < 2 ^ m → wdFrozenRNE m f ρ) ↔ ρ ≤ wdTotalFreezeRadius m) ∧
      (∀ ρ : Rat, wdTotalFreezeRadius m < ρ → ρ < wdInteriorFreezeSup m →
        wdDecaysRNE m 0 ρ ∧ (∀ f : Nat, 1 ≤ f → f < 2 ^ m → wdFrozenRNE m f ρ)) ∧
      (∀ ρ : Rat, (∀ f : Nat, f < 2 ^ m → wdDecaysRNE m f ρ) ↔ wdUniversalDecayThreshold m ≤ ρ) ∧
      (∀ ρ : Rat, 1 / ((2 ^ (m + 1) + 4 : Nat) : Rat) < ρ → ρ < wdUniversalDecayThreshold m →
        wdFrozenRNE m 1 ρ ∧ (∀ f : Nat, f < 2 ^ m → f ≠ 1 → wdDecaysRNE m f ρ))) ∧
    ((wdTotalFreezeRadius 2 = 1 / 16 ∧ wdInteriorFreezeSup 2 = 1 / 14 ∧
      wdUniversalDecayThreshold 2 = 1 / 10) ∧
     (wdTotalFreezeRadius 3 = 1 / 32 ∧ wdInteriorFreezeSup 3 = 1 / 30 ∧
      wdUniversalDecayThreshold 3 = 1 / 18) ∧
     (wdTotalFreezeRadius 7 = 1 / 512 ∧ wdInteriorFreezeSup 7 = 1 / 510 ∧
      wdUniversalDecayThreshold 7 = 1 / 258) ∧
     (wdTotalFreezeRadius 10 = 1 / 4096 ∧ wdInteriorFreezeSup 10 = 1 / 4094 ∧
      wdUniversalDecayThreshold 10 = 1 / 2050)) := by
  refine ⟨?_, ⟨⟨by unfold wdTotalFreezeRadius invPow2Rat pow2Rat; grind,
                by unfold wdInteriorFreezeSup; grind,
                by unfold wdUniversalDecayThreshold; grind⟩,
               ⟨by unfold wdTotalFreezeRadius invPow2Rat pow2Rat; grind,
                by unfold wdInteriorFreezeSup; grind,
                by unfold wdUniversalDecayThreshold; grind⟩,
               ⟨by unfold wdTotalFreezeRadius invPow2Rat pow2Rat; grind,
                by unfold wdInteriorFreezeSup; grind,
                by unfold wdUniversalDecayThreshold; grind⟩,
               ⟨by unfold wdTotalFreezeRadius invPow2Rat pow2Rat; grind,
                by unfold wdInteriorFreezeSup; grind,
                by unfold wdUniversalDecayThreshold; grind⟩⟩⟩
  intro m hm
  have h2m : 2 ≤ 2 ^ m := two_pow_ge_two hm
  have h2m2 : 2 ^ (m + 2) = 4 * 2 ^ m := by
    rw [Nat.pow_succ, Nat.pow_succ]; omega
  have h2m1 : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [Nat.pow_succ]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1: Total freeze iff ρ ≤ 2^{-(m+2)}
    intro ρ
    constructor
    · intro hall
      exact (wdFrozenRNE_zero_iff m ρ).mp (hall 0 (by omega))
    · intro hρ f hf
      by_cases hf0 : f = 0
      · subst hf0; exact (wdFrozenRNE_zero_iff m ρ).mpr hρ
      · have hf1 : 1 ≤ f := by omega
        have hlt_inv : wdTotalFreezeRadius m < 1 / ((2 * (2 ^ m + f) : Nat) : Rat) := by
          unfold wdTotalFreezeRadius invPow2Rat pow2Rat
          exact inv_lt_inv_nat (by omega) (by omega)
        have hρ_lt : ρ < 1 / ((2 * (2 ^ m + f) : Nat) : Rat) := rat_lt_of_le_of_lt hρ hlt_inv
        by_cases hev : f % 2 = 0
        · exact (wdFrozenRNE_pos_even_iff m f hf1 hev ρ).mpr (Rat.le_of_lt hρ_lt)
        · have hodd : f % 2 = 1 := by omega
          exact (wdFrozenRNE_pos_odd_iff m f hf1 hodd ρ).mpr hρ_lt
  · -- Part 2: Power-of-2-only decay gap
    intro ρ hlo hhi
    constructor
    · unfold wdDecaysRNE
      rw [wdFrozenRNE_zero_iff]
      exact Rat.not_le.mpr hlo
    · intro f hf1 hf
      have hle_inv : wdInteriorFreezeSup m ≤ 1 / ((2 * (2 ^ m + f) : Nat) : Rat) := by
        unfold wdInteriorFreezeSup
        exact inv_le_inv_nat (by omega) (by omega)
      have hρ_lt : ρ < 1 / ((2 * (2 ^ m + f) : Nat) : Rat) := rat_lt_of_lt_of_le hhi hle_inv
      by_cases hev : f % 2 = 0
      · exact (wdFrozenRNE_pos_even_iff m f hf1 hev ρ).mpr (Rat.le_of_lt hρ_lt)
      · have hodd : f % 2 = 1 := by omega
        exact (wdFrozenRNE_pos_odd_iff m f hf1 hodd ρ).mpr hρ_lt
  · -- Part 3: Universal decay iff ρ ≥ 1 / (2^{m+1} + 2)
    intro ρ
    constructor
    · intro hall
      have h1 : wdDecaysRNE m 1 ρ := hall 1 (by omega)
      unfold wdDecaysRNE at h1
      rw [wdFrozenRNE_pos_odd_iff m 1 (by decide) (by decide) ρ] at h1
      have hle : 1 / ((2 * (2 ^ m + 1) : Nat) : Rat) ≤ ρ := Rat.not_lt.mp h1
      have heq : 2 * (2 ^ m + 1) = 2 ^ (m + 1) + 2 := by omega
      unfold wdUniversalDecayThreshold
      rw [← heq]; exact hle
    · intro hρ f hf
      unfold wdDecaysRNE
      by_cases hf0 : f = 0
      · subst hf0
        rw [wdFrozenRNE_zero_iff]
        have hlt : wdTotalFreezeRadius m < wdUniversalDecayThreshold m := by
          unfold wdTotalFreezeRadius invPow2Rat pow2Rat wdUniversalDecayThreshold
          exact inv_lt_inv_nat (by omega) (by omega)
        exact Rat.not_le.mpr (rat_lt_of_lt_of_le hlt hρ)
      · by_cases hf1 : f = 1
        · subst hf1
          rw [wdFrozenRNE_pos_odd_iff m 1 (by decide) (by decide) ρ]
          have heq : 2 * (2 ^ m + 1) = 2 ^ (m + 1) + 2 := by omega
          unfold wdUniversalDecayThreshold at hρ
          rw [← heq] at hρ
          exact Rat.not_lt.mpr hρ
        · have hf2 : 2 ≤ f := by omega
          have hlt : 1 / ((2 * (2 ^ m + f) : Nat) : Rat) < wdUniversalDecayThreshold m := by
            unfold wdUniversalDecayThreshold
            exact inv_lt_inv_nat (by omega) (by omega)
          have hρ_gt : 1 / ((2 * (2 ^ m + f) : Nat) : Rat) < ρ := rat_lt_of_lt_of_le hlt hρ
          by_cases hev : f % 2 = 0
          · rw [wdFrozenRNE_pos_even_iff m f (by omega) hev ρ]
            exact Rat.not_le.mpr hρ_gt
          · have hodd : f % 2 = 1 := by omega
            rw [wdFrozenRNE_pos_odd_iff m f (by omega) hodd ρ]
            exact Rat.not_lt.mpr (Rat.le_of_lt hρ_gt)
  · -- Part 4: f = 1 is strictly the last mantissa to unfreeze
    intro ρ hlo hhi
    constructor
    · rw [wdFrozenRNE_pos_odd_iff m 1 (by decide) (by decide) ρ]
      have heq : 2 * (2 ^ m + 1) = 2 ^ (m + 1) + 2 := by omega
      unfold wdUniversalDecayThreshold at hhi
      rw [← heq] at hhi
      exact hhi
    · intro f hf hf1
      unfold wdDecaysRNE
      by_cases hf0 : f = 0
      · subst hf0
        rw [wdFrozenRNE_zero_iff]
        have hle : wdTotalFreezeRadius m ≤ 1 / ((2 ^ (m + 1) + 4 : Nat) : Rat) := by
          unfold wdTotalFreezeRadius invPow2Rat pow2Rat
          exact inv_le_inv_nat (by omega) (by omega)
        exact Rat.not_le.mpr (rat_lt_of_le_of_lt hle hlo)
      · have hf2 : 2 ≤ f := by omega
        have hle : 1 / ((2 * (2 ^ m + f) : Nat) : Rat) ≤ 1 / ((2 ^ (m + 1) + 4 : Nat) : Rat) :=
          inv_le_inv_nat (by omega) (by omega)
        have hρ_gt : 1 / ((2 * (2 ^ m + f) : Nat) : Rat) < ρ := rat_lt_of_le_of_lt hle hlo
        by_cases hev : f % 2 = 0
        · rw [wdFrozenRNE_pos_even_iff m f (by omega) hev ρ]
          exact Rat.not_le.mpr hρ_gt
        · have hodd : f % 2 = 1 := by omega
          rw [wdFrozenRNE_pos_odd_iff m f (by omega) hodd ρ]
          exact Rat.not_lt.mpr (Rat.le_of_lt hρ_gt)

end MuonclipAdamwSr
