/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrpoK3Kl.RatOrder

/-!
# Schulman `k3` KL Non-Negativity & `BF16` / `FP16` Negative-KL Failure Laws

Proves Headline Theorems 1 and 2 purely over `Rat` and `Nat` inside `Init` (zero Mathlib):
1. `schulman_k3_exact_nonnegativity_and_quadratic_bound`
2. `bf16_k3_negative_kl_and_deadzone_exact`
-/

namespace GrpoK3Kl

theorem k3Stab_factorization (d : Rat) :
    k3Stab d = (d * d / 24) * ((d + 2) * (d + 2) + 8) := by
  unfold k3Stab
  grind

theorem k3Stab_ge_sq_div_three (d : Rat) : (d * d) / 3 ≤ k3Stab d := by
  rw [k3Stab_factorization]
  have hsq : (0 : Rat) ≤ (d + 2) * (d + 2) := rat_mul_nonneg_sq (d + 2)
  have h8 : (8 : Rat) ≤ (d + 2) * (d + 2) + 8 := by
    have := rat_add_le_add hsq (Rat.le_refl (a := (8 : Rat)))
    have h0 : (0 : Rat) + 8 = 8 := by grind
    rw [h0] at this
    exact this
  have hd2 : (0 : Rat) ≤ d * d / 24 := rat_div_nonneg (rat_mul_nonneg_sq d) (by decide)
  have hmul := rat_mul_le_mul_of_nonneg_left h8 hd2
  have heq : (d * d / 24) * 8 = d * d / 3 := by grind
  rw [heq] at hmul
  exact hmul

theorem k3Stab_nonneg (d : Rat) : (0 : Rat) ≤ k3Stab d :=
  Rat.le_trans (rat_div_nonneg (rat_mul_nonneg_sq d) (by decide)) (k3Stab_ge_sq_div_three d)

theorem k3Stab_pos_of_ne_zero {d : Rat} (hd : d ≠ 0) : (0 : Rat) < k3Stab d := by
  have hpos : (0 : Rat) < (d * d) / 3 := rat_div_pos (rat_mul_pos_sq hd) (by decide)
  exact rat_lt_of_lt_of_le hpos (k3Stab_ge_sq_div_three d)

theorem pade22Den_ge_quarter (d : Rat) : (1 / 4 : Rat) ≤ pade22Den d := by
  unfold pade22Den
  have hsq : (0 : Rat) ≤ (d - 3) * (d - 3) := rat_mul_nonneg_sq (d - 3)
  have hdiv : (0 : Rat) ≤ ((d - 3) * (d - 3)) / 12 := rat_div_nonneg hsq (by decide)
  have heq : 1 - d / 2 + d * d / 12 = (1 / 4 : Rat) + ((d - 3) * (d - 3)) / 12 := by grind
  rw [heq]
  have h0 : (1 / 4 : Rat) + 0 = 1 / 4 := by grind
  have h := rat_add_le_add (Rat.le_refl (a := (1 / 4 : Rat))) hdiv
  rw [h0] at h
  exact h

theorem pade22Den_pos (d : Rat) : (0 : Rat) < pade22Den d :=
  rat_lt_of_lt_of_le (rat_div_pos (by decide) (by decide)) (pade22Den_ge_quarter d)

theorem pade22_k3_eq (d : Rat) :
    pade22 d - 1 - d = (d * d * (6 - d)) / (12 * pade22Den d) := by
  unfold pade22 pade22Num
  have hden : pade22Den d ≠ 0 := Rat.ne_of_gt (pade22Den_pos d)
  have h12 : (12 : Rat) ≠ 0 := by decide
  have hmul : (12 * pade22Den d) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact h12 h
    | inr h => exact hden h
  have hnum : (1 + d / 2 + d * d / 12) - (1 + d) * pade22Den d = (d * d * (6 - d)) / 12 := by
    unfold pade22Den
    grind
  calc
    (1 + d / 2 + d * d / 12) / pade22Den d - 1 - d
        = (1 + d / 2 + d * d / 12) / pade22Den d - (1 + d) := by grind
    _ = ((1 + d / 2 + d * d / 12) - (1 + d) * pade22Den d) / pade22Den d := by
      rw [Rat.div_def, Rat.div_def]
      have : (1 + d) = (1 + d) * pade22Den d * (pade22Den d)⁻¹ := by
        rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hden, Rat.mul_one]
      grind
    _ = ((d * d * (6 - d)) / 12) / pade22Den d := by rw [hnum]
    _ = (d * d * (6 - d)) / (12 * pade22Den d) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def, rat_mul_inv h12 hden, Rat.mul_comm (pade22Den d)⁻¹]
      rw [Rat.mul_assoc]

/-- Headline Theorem 1 (`schulman_k3_exact_nonnegativity_and_quadratic_bound`). -/
theorem schulman_k3_exact_nonnegativity_and_quadratic_bound :
    (∀ (d e_d : Rat), 1 + d ≤ e_d → (0 : Rat) ≤ e_d - 1 - d) ∧
    (∀ (d e_d : Rat), 1 + d < e_d → (0 : Rat) < e_d - 1 - d) ∧
    (∀ (d e_d : Rat), (0 : Rat) ≤ d → d ≤ 1 →
      expTaylor4 d ≤ e_d → e_d ≤ expTaylor3 d + d * d * d * d / 12 →
      k3QuadLower d ≤ k3Stab d ∧ k3Stab d ≤ e_d - 1 - d ∧ e_d - 1 - d ≤ k3QuadUpper d) ∧
    (∀ d : Rat,
      k3Stab d = (d * d / 24) * ((d + 2) * (d + 2) + 8) ∧
      (d * d) / 3 ≤ k3Stab d ∧
      (0 : Rat) ≤ k3Stab d ∧
      (d ≠ 0 → (0 : Rat) < k3Stab d)) ∧
    (∀ d : Rat,
      (1 / 4 : Rat) ≤ pade22Den d ∧
      (0 : Rat) < pade22Den d ∧
      pade22 d - 1 - d = (d * d * (6 - d)) / (12 * pade22Den d) ∧
      (d < 6 → (0 : Rat) ≤ pade22 d - 1 - d ∧ (d ≠ 0 → (0 : Rat) < pade22 d - 1 - d))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d e_d h
    have hsub := rat_sub_nonneg h
    have eq : e_d - (1 + d) = e_d - 1 - d := by grind
    rw [← eq]; exact hsub
  · intro d e_d h
    have hsub := rat_sub_pos h
    have eq : e_d - (1 + d) = e_d - 1 - d := by grind
    rw [← eq]; exact hsub
  · intro d e_d _hd0 _hd1 hlo hhi
    have hq_le : k3QuadLower d ≤ k3Stab d := by
      apply rat_le_of_sub_nonneg
      have hdiff : k3Stab d - k3QuadLower d = ((d * d) * (d * d)) / 24 := by
        unfold k3Stab k3QuadLower
        grind
      rw [hdiff]
      exact rat_div_nonneg (rat_mul_nonneg_sq (d * d)) (by decide)
    have hlo' : k3Stab d ≤ e_d - 1 - d := by
      have hsub := rat_sub_nonneg hlo
      have eq : e_d - expTaylor4 d = (e_d - 1 - d) - k3Stab d := by
        unfold expTaylor4 expTaylor3 k3Stab
        grind
      rw [eq] at hsub
      exact rat_le_of_sub_nonneg hsub
    have hhi' : e_d - 1 - d ≤ k3QuadUpper d := by
      have hsub := rat_sub_nonneg hhi
      have eq : (expTaylor3 d + d * d * d * d / 12) - e_d = k3QuadUpper d - (e_d - 1 - d) := by
        unfold expTaylor3 k3QuadUpper
        grind
      rw [eq] at hsub
      exact rat_le_of_sub_nonneg hsub
    exact ⟨hq_le, hlo', hhi'⟩
  · intro d
    exact ⟨k3Stab_factorization d, k3Stab_ge_sq_div_three d, k3Stab_nonneg d, k3Stab_pos_of_ne_zero⟩
  · intro d
    refine ⟨pade22Den_ge_quarter d, pade22Den_pos d, pade22_k3_eq d, ?_⟩
    intro hd6
    rw [pade22_k3_eq d]
    have h6d : (0 : Rat) < 6 - d := rat_sub_pos hd6
    have hden : (0 : Rat) < 12 * pade22Den d := rat_mul_pos (by decide) (pade22Den_pos d)
    constructor
    · exact rat_div_nonneg (Rat.mul_nonneg (rat_mul_nonneg_sq d) (Rat.le_of_lt h6d)) hden
    · intro hne
      exact rat_div_pos (rat_mul_pos (rat_mul_pos_sq hne) h6d) hden

/-! ## Theorem 2: Exact `BF16` / `FP16` Negative-KL & Dead-Zero Laws -/

theorem rneRoundsToOneAbove_iff (m : Nat) (x : Rat) :
    rneRoundsToOneAbove m x ↔ (1 ≤ x ∧ x ≤ 1 + invPow2Rat (m + 1)) := by
  unfold rneRoundsToOneAbove
  have h2 : invPow2Rat (m + 1) * 2 = invPow2Rat m := invPow2Rat_succ m
  constructor
  · rintro ⟨h1, h2'⟩
    refine ⟨h1, ?_⟩
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg h2'
    have eq : ((1 + invPow2Rat m) - x) - (x - 1) = 2 * ((1 + invPow2Rat (m + 1)) - x) := by
      grind
    rw [eq] at hsub
    have hhalf := rat_mul_le_mul_of_nonneg_left hsub (rat_div_nonneg (by decide) (by decide) : (0 : Rat) ≤ 1 / 2)
    have h0 : (1 / 2 : Rat) * 0 = 0 := by grind
    have h1' : (1 / 2 : Rat) * (2 * ((1 + invPow2Rat (m + 1)) - x)) =
        (1 + invPow2Rat (m + 1)) - x := by grind
    rw [h0, h1'] at hhalf
    exact hhalf
  · rintro ⟨h1, h2'⟩
    refine ⟨h1, ?_⟩
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg h2'
    have eq : ((1 + invPow2Rat m) - x) - (x - 1) = 2 * ((1 + invPow2Rat (m + 1)) - x) := by
      grind
    rw [eq]
    exact Rat.mul_nonneg (by decide) hsub

theorem rneRoundsToPredOfOne_iff (m : Nat) (d : Rat) :
    rneRoundsToPredOfOne m (1 - d) ↔ (invPow2Rat (m + 2) < d ∧ d ≤ invPow2Rat (m + 1)) := by
  unfold rneRoundsToPredOfOne
  have h2 : invPow2Rat (m + 2) * 2 = invPow2Rat (m + 1) := invPow2Rat_succ (m + 1)
  constructor
  · rintro ⟨hlo, _hhi, hlt⟩
    refine ⟨?_, ?_⟩
    · apply rat_lt_of_sub_pos
      have hpos := rat_sub_pos hlt
      have eq : (1 - (1 - d)) - ((1 - d) - (1 - invPow2Rat (m + 1))) =
          2 * (d - invPow2Rat (m + 2)) := by grind
      rw [eq] at hpos
      have hhalf := rat_mul_lt_mul_of_pos_left hpos (rat_div_pos (by decide) (by decide) : (0 : Rat) < 1 / 2)
      have h0 : (1 / 2 : Rat) * 0 = 0 := by grind
      have h1' : (1 / 2 : Rat) * (2 * (d - invPow2Rat (m + 2))) = d - invPow2Rat (m + 2) := by
        grind
      rw [h0, h1'] at hhalf
      exact hhalf
    · apply rat_le_of_sub_nonneg
      have hsub := rat_sub_nonneg hlo
      have eq : (1 - d) - (1 - invPow2Rat (m + 1)) = invPow2Rat (m + 1) - d := by grind
      rw [eq] at hsub
      exact hsub
  · rintro ⟨hlo, hhi⟩
    have hd_pos : (0 : Rat) < d := rat_lt_trans (invPow2Rat_pos (m + 2)) hlo
    refine ⟨?_, ?_, ?_⟩
    · apply rat_le_of_sub_nonneg
      have eq : (1 - d) - (1 - invPow2Rat (m + 1)) = invPow2Rat (m + 1) - d := by grind
      rw [eq]
      exact rat_sub_nonneg hhi
    · apply rat_le_of_sub_nonneg
      have eq : 1 - (1 - d) = d := by grind
      rw [eq]
      exact Rat.le_of_lt hd_pos
    · apply rat_lt_of_sub_pos
      have eq : (1 - (1 - d)) - ((1 - d) - (1 - invPow2Rat (m + 1))) =
          2 * (d - invPow2Rat (m + 2)) := by grind
      rw [eq]
      exact rat_mul_pos (by decide) (rat_sub_pos hlo)

theorem rneSnapsToOneBelow_iff (m : Nat) (d : Rat) :
    rneSnapsToOneBelow m (1 - d) ↔ ((0 : Rat) ≤ d ∧ d ≤ invPow2Rat (m + 2)) := by
  unfold rneSnapsToOneBelow
  have h2 : invPow2Rat (m + 2) * 2 = invPow2Rat (m + 1) := invPow2Rat_succ (m + 1)
  constructor
  · rintro ⟨⟨_hlo, hhi⟩, hmid⟩
    refine ⟨?_, ?_⟩
    · have hsub := rat_sub_nonneg hhi
      have eq : 1 - (1 - d) = d := by grind
      rw [eq] at hsub; exact hsub
    · apply rat_le_of_sub_nonneg
      have hsub := rat_sub_nonneg hmid
      have eq : ((1 - d) - (1 - invPow2Rat (m + 1))) - (1 - (1 - d)) =
          2 * (invPow2Rat (m + 2) - d) := by grind
      rw [eq] at hsub
      have hhalf := rat_mul_le_mul_of_nonneg_left hsub (rat_div_nonneg (by decide) (by decide) : (0 : Rat) ≤ 1 / 2)
      have h0 : (1 / 2 : Rat) * 0 = 0 := by grind
      have h1' : (1 / 2 : Rat) * (2 * (invPow2Rat (m + 2) - d)) =
          invPow2Rat (m + 2) - d := by grind
      rw [h0, h1'] at hhalf
      exact hhalf
  · rintro ⟨h0, hhi⟩
    have hhi1 : d ≤ invPow2Rat (m + 1) := by
      have hle : invPow2Rat (m + 2) ≤ invPow2Rat (m + 1) := by
        apply rat_le_of_sub_nonneg
        have eq : invPow2Rat (m + 1) - invPow2Rat (m + 2) = invPow2Rat (m + 2) := by grind
        rw [eq]; exact Rat.le_of_lt (invPow2Rat_pos (m + 2))
      exact Rat.le_trans hhi hle
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply rat_le_of_sub_nonneg
      have eq : (1 - d) - (1 - invPow2Rat (m + 1)) = invPow2Rat (m + 1) - d := by grind
      rw [eq]; exact rat_sub_nonneg hhi1
    · apply rat_le_of_sub_nonneg
      have eq : 1 - (1 - d) = d := by grind
      rw [eq]; exact h0
    · apply rat_le_of_sub_nonneg
      have eq : ((1 - d) - (1 - invPow2Rat (m + 1))) - (1 - (1 - d)) =
          2 * (invPow2Rat (m + 2) - d) := by grind
      rw [eq]
      exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hhi)

theorem bf16_0x3b01_val : bf16DecodePosNormal 0x3b01 = 129 / 65536 := by
  unfold bf16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x3b01 / 128) % 256 = 118 by decide, show 0x3b01 % 128 = 1 by decide,
             show (118 < 134) = true by decide, ↓reduceIte,
             show 134 - 118 = 16 by decide, show 128 + 1 = 129 by decide,
             show 2 ^ 16 = 65536 by decide]
  grind

theorem bf16_0x3b7f_val : bf16DecodePosNormal 0x3b7f = 255 / 65536 := by
  unfold bf16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x3b7f / 128) % 256 = 118 by decide, show 0x3b7f % 128 = 127 by decide,
             show (118 < 134) = true by decide, ↓reduceIte,
             show 134 - 118 = 16 by decide, show 128 + 127 = 255 by decide,
             show 2 ^ 16 = 65536 by decide]
  grind

theorem fp16_0x0c01_val : fp16DecodePosNormal 0x0c01 = 1025 / 4194304 := by
  unfold fp16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x0c01 / 1024) % 32 = 3 by decide, show 0x0c01 % 1024 = 1 by decide,
             show (3 < 25) = true by decide, ↓reduceIte,
             show 25 - 3 = 22 by decide, show 1024 + 1 = 1025 by decide,
             show 2 ^ 22 = 4194304 by decide]
  grind

/-- Headline Theorem 2 (`bf16_k3_negative_kl_and_deadzone_exact`). -/
theorem bf16_k3_negative_kl_and_deadzone_exact :
    (∀ (m : Nat) (x : Rat), rneRoundsToOneAbove m x ↔ (1 ≤ x ∧ x ≤ 1 + invPow2Rat (m + 1))) ∧
    (∀ (m : Nat) (d : Rat), rneRoundsToPredOfOne m (1 - d) ↔
      (invPow2Rat (m + 2) < d ∧ d ≤ invPow2Rat (m + 1))) ∧
    (∀ (m : Nat) (d : Rat), rneSnapsToOneBelow m (1 - d) ↔
      ((0 : Rat) ≤ d ∧ d ≤ invPow2Rat (m + 2))) ∧
    (∀ (m : Nat) (d e_d : Rat),
      invPow2Rat (m + 2) < d → d ≤ invPow2Rat (m + 1) →
      1 ≤ e_d → e_d ≤ 1 + invPow2Rat (m + 1) →
      rneRoundsToOneAbove m e_d ∧
      rneRoundsToPredOfOne m (1 - d) ∧
      (1 - invPow2Rat (m + 1)) - 1 = -invPow2Rat (m + 1) ∧
      (1 - invPow2Rat (m + 1)) - 1 < 0) ∧
    (∀ (m : Nat) (d e_d : Rat),
      (0 : Rat) < d → d ≤ invPow2Rat (m + 2) →
      1 ≤ e_d → e_d ≤ 1 + invPow2Rat (m + 1) →
      rneRoundsToOneAbove m e_d ∧
      rneSnapsToOneBelow m (1 - d) ∧
      (1 : Rat) - 1 = 0 ∧
      (0 : Rat) < k3Stab d) ∧
    (∀ d : Rat, ((1 + d) - d) - 1 = 0) ∧
    (let d := bf16DecodePosNormal 0x3b01
     d = 129 / 65536 ∧
     rneRoundsToOneAbove 7 (expTaylor4 d) ∧
     rneRoundsToPredOfOne 7 (1 - d) ∧
     (1 - invPow2Rat 8) - 1 = -(1 / 256 : Rat) ∧
     (1 - invPow2Rat 8) - 1 < 0) ∧
    (let d := fp16DecodePosNormal 0x0c01
     d = 1025 / 4194304 ∧
     rneRoundsToOneAbove 10 (expTaylor4 d) ∧
     rneRoundsToPredOfOne 10 (1 - d) ∧
     (1 - invPow2Rat 11) - 1 = -(1 / 2048 : Rat) ∧
     (1 - invPow2Rat 11) - 1 < 0) ∧
    (∀ (m : Nat) (d e_d : Rat),
      (0 : Rat) < d → 1 ≤ e_d → e_d ≤ 1 + invPow2Rat (m + 1) →
      rneRoundsToOneAbove m e_d ∧ ((1 : Rat) - 1) - d = -d ∧ ((1 : Rat) - 1) - d < 0) ∧
    (let d := bf16DecodePosNormal 0x3b7f
     d = 255 / 65536 ∧
     rneRoundsToOneAbove 7 (expTaylor4 d) ∧
     ((1 : Rat) - 1) - d = -(255 / 65536 : Rat) ∧
     ((1 : Rat) - 1) - d < 0) := by
  refine ⟨rneRoundsToOneAbove_iff, rneRoundsToPredOfOne_iff, rneSnapsToOneBelow_iff,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m d e_d hlo hhi he1 he2
    refine ⟨(rneRoundsToOneAbove_iff m e_d).mpr ⟨he1, he2⟩,
            (rneRoundsToPredOfOne_iff m d).mpr ⟨hlo, hhi⟩, ?_, ?_⟩
    · grind
    · have hneg : -invPow2Rat (m + 1) < 0 := rat_neg_of_pos (invPow2Rat_pos (m + 1))
      have heq : (1 - invPow2Rat (m + 1)) - 1 = -invPow2Rat (m + 1) := by grind
      rw [heq]; exact hneg
  · intro m d e_d hd0 hhi he1 he2
    refine ⟨(rneRoundsToOneAbove_iff m e_d).mpr ⟨he1, he2⟩,
            (rneSnapsToOneBelow_iff m d).mpr ⟨Rat.le_of_lt hd0, hhi⟩,
            by grind, k3Stab_pos_of_ne_zero (Rat.ne_of_gt hd0)⟩
  · intro d; grind
  · refine ⟨bf16_0x3b01_val, ?_, ?_, ?_, ?_⟩
    · rw [bf16_0x3b01_val, rneRoundsToOneAbove_iff]
      unfold expTaylor4 expTaylor3 invPow2Rat pow2Rat
      simp only [show 2 ^ (7 + 1) = 256 by decide]
      grind
    · rw [bf16_0x3b01_val, rneRoundsToPredOfOne_iff]
      unfold invPow2Rat pow2Rat
      simp only [show 2 ^ (7 + 2) = 512 by decide, show 2 ^ (7 + 1) = 256 by decide]
      grind
    · unfold invPow2Rat pow2Rat
      simp only [show 2 ^ 8 = 256 by decide]
      grind
    · unfold invPow2Rat pow2Rat
      simp only [show 2 ^ 8 = 256 by decide]
      grind
  · refine ⟨fp16_0x0c01_val, ?_, ?_, ?_, ?_⟩
    · rw [fp16_0x0c01_val, rneRoundsToOneAbove_iff]
      unfold expTaylor4 expTaylor3 invPow2Rat pow2Rat
      simp only [show 2 ^ (10 + 1) = 2048 by decide]
      grind
    · rw [fp16_0x0c01_val, rneRoundsToPredOfOne_iff]
      unfold invPow2Rat pow2Rat
      simp only [show 2 ^ (10 + 2) = 4096 by decide, show 2 ^ (10 + 1) = 2048 by decide]
      grind
    · unfold invPow2Rat pow2Rat
      simp only [show 2 ^ 11 = 2048 by decide]
      grind
    · unfold invPow2Rat pow2Rat
      simp only [show 2 ^ 11 = 2048 by decide]
      grind
  · intro m d e_d hd0 he1 he2
    refine ⟨(rneRoundsToOneAbove_iff m e_d).mpr ⟨he1, he2⟩, by grind, ?_⟩
    have eq : ((1 : Rat) - 1) - d = -d := by grind
    rw [eq]
    exact rat_neg_of_pos hd0
  · refine ⟨bf16_0x3b7f_val, ?_, by rw [bf16_0x3b7f_val]; grind, by rw [bf16_0x3b7f_val]; grind⟩
    rw [bf16_0x3b7f_val, rneRoundsToOneAbove_iff]
    unfold expTaylor4 expTaylor3 invPow2Rat pow2Rat
    simp only [show 2 ^ (7 + 1) = 256 by decide]
    grind

end GrpoK3Kl
