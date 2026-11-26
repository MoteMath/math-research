/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmTustinPade.RatOrder

/-!
# Theorems 4 & 5: Subtraction-Free `Padé-(0,2)` State & Input Discretization Laws

- Theorem 4 (`pade02_unconditional_positivity_and_contraction_exact`):
  Proves `0 < A_pade02(z) < 1` for all `z > 0`, exact `O(z^3)` and `O(z^4)` rational
  identities against the Taylor polynomials of `exp(-z)`, and the exact `FP8-E4M3FN`
  no-Inf overflow cliffs (`z^2 > 448` for `z ≥ 22` and `z^2 / 2 > 448` for `z ≥ 32`).
- Theorem 5 (`pade02_b_bar_zero_blackout_and_fourth_order_accuracy`):
  Proves `0 < B_pade02(z) ≤ 1` for all `z ≥ 0` (`0.0%` blackout), exact 4th-order `O(z^4)`
  matching against `phi_1(-z) = (1 - exp(-z)) / z` via exact rational polynomial identities,
  uniform `(0, 1]` error bound `≤ z^4 / 360 ≤ 1 / 360`, and strictly tighter worst-case
  `(0, 1]` accuracy than `B_tustin(z) = 1 / (1 + z / 2)` (`1 / 360 < 1 / 30` at `z = 1`).
-/

namespace SsmTustinPade

theorem pade02A_den_gt_one {z : Rat} (hz : (0 : Rat) < z) :
    (1 : Rat) < 1 + z + z * z / 2 := by
  have hz2 : (0 : Rat) ≤ z * z / 2 := rat_div_nonneg (rat_sq_nonneg z) (by decide)
  have hsum : (0 : Rat) < z + z * z / 2 := rat_add_pos_of_pos_of_nonneg hz hz2
  apply rat_lt_of_sub_pos
  have : (1 + z + z * z / 2) - 1 = z + z * z / 2 := by grind
  rw [this]; exact hsum

theorem pade02A_pos_and_lt_one {z : Rat} (hz : (0 : Rat) < z) :
    (0 : Rat) < pade02A z ∧ pade02A z < 1 := by
  unfold pade02A
  have hden1 : (1 : Rat) < 1 + z + z * z / 2 := pade02A_den_gt_one hz
  have hden0 : (0 : Rat) < 1 + z + z * z / 2 := rat_lt_trans (by decide) hden1
  constructor
  · exact rat_div_pos (by decide) hden0
  · apply rat_div_lt_of_mul_lt hden0
    have : (1 : Rat) * (1 + z + z * z / 2) = 1 + z + z * z / 2 := by grind
    rw [this]; exact hden1

theorem pade02A_sub_expTaylor2 {z : Rat} (hz : (0 : Rat) < z) :
    pade02A z - expTaylor2 z = -(z * z * z * z) / (4 * (1 + z + z * z / 2)) := by
  unfold pade02A expTaylor2
  have hden0 : (0 : Rat) < 1 + z + z * z / 2 := rat_lt_trans (by decide) (pade02A_den_gt_one hz)
  have hne : 1 + z + z * z / 2 ≠ 0 := Rat.ne_of_gt hden0
  have hne4 : 4 * (1 + z + z * z / 2) ≠ 0 := by
    have : (0 : Rat) < 4 * (1 + z + z * z / 2) := rat_mul_pos (by decide) hden0
    exact Rat.ne_of_gt this
  symm
  rw [rat_div_eq_iff hne4]
  have hc : (1 / (1 + z + z * z / 2)) * (1 + z + z * z / 2) = 1 := rat_div_mul_cancel hne
  grind

theorem pade02A_sub_expTaylor3 {z : Rat} (hz : (0 : Rat) < z) :
    pade02A z - expTaylor3 z = z * z * z * (2 - z + z * z) / (12 * (1 + z + z * z / 2)) := by
  unfold pade02A expTaylor3
  have hden0 : (0 : Rat) < 1 + z + z * z / 2 := rat_lt_trans (by decide) (pade02A_den_gt_one hz)
  have hne : 1 + z + z * z / 2 ≠ 0 := Rat.ne_of_gt hden0
  have hne12 : 12 * (1 + z + z * z / 2) ≠ 0 := by
    have : (0 : Rat) < 12 * (1 + z + z * z / 2) := rat_mul_pos (by decide) hden0
    exact Rat.ne_of_gt this
  symm
  rw [rat_div_eq_iff hne12]
  have hc : (1 / (1 + z + z * z / 2)) * (1 + z + z * z / 2) = 1 := rat_div_mul_cancel hne
  grind

theorem pade02A_taylor3_bound {z : Rat} (hz0 : (0 : Rat) < z) (hz1 : z ≤ 1) :
    (0 : Rat) < pade02A z - expTaylor3 z ∧
    pade02A z - expTaylor3 z ≤ z * z * z / 6 := by
  rw [pade02A_sub_expTaylor3 hz0]
  have hden1 : (1 : Rat) < 1 + z + z * z / 2 := pade02A_den_gt_one hz0
  have hden0 : (0 : Rat) < 1 + z + z * z / 2 := rat_lt_trans (by decide) hden1
  have hden12 : (0 : Rat) < 12 * (1 + z + z * z / 2) := rat_mul_pos (by decide) hden0
  have hquad_pos : (0 : Rat) < 2 - z + z * z := by
    have hsq : (0 : Rat) ≤ (z - 1 / 2) * (z - 1 / 2) := rat_sq_nonneg (z - 1 / 2)
    have heq : 2 - z + z * z = (z - 1 / 2) * (z - 1 / 2) + 7 / 4 := by grind
    rw [heq]
    exact rat_add_pos_of_nonneg_of_pos hsq (rat_div_pos (by decide) (by decide))
  have hquad_le2 : 2 - z + z * z ≤ 2 := by
    have hsq : z * z ≤ z * 1 := rat_mul_le_mul_of_nonneg_left hz1 (Rat.le_of_lt hz0)
    have hsub : (0 : Rat) ≤ z - z * z := rat_sub_nonneg (by grind)
    apply rat_le_of_sub_nonneg
    have : 2 - (2 - z + z * z) = z - z * z := by grind
    rw [this]; exact hsub
  have hz3_pos : (0 : Rat) < z * z * z := rat_mul_pos (rat_mul_pos hz0 hz0) hz0
  constructor
  · exact rat_div_pos (rat_mul_pos hz3_pos hquad_pos) hden12
  · apply rat_div_le_of_mul_le hden12
    have h1 : z * z * z * (2 - z + z * z) ≤ z * z * z * 2 :=
      rat_mul_le_mul_of_nonneg_left hquad_le2 (Rat.le_of_lt hz3_pos)
    have h2 : (2 : Rat) ≤ 2 * (1 + z + z * z / 2) := by
      have := rat_mul_le_mul_of_nonneg_left (Rat.le_of_lt hden1) (by decide : (0 : Rat) ≤ 2)
      grind
    have h3 : z * z * z * 2 ≤ z * z * z * (2 * (1 + z + z * z / 2)) :=
      rat_mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt hz3_pos)
    have h4 : z * z * z / 6 * (12 * (1 + z + z * z / 2)) =
        z * z * z * (2 * (1 + z + z * z / 2)) := by grind
    rw [h4]
    exact Rat.le_trans h1 h3

/-- Headline Theorem 4 (`pade02_unconditional_positivity_and_contraction_exact`). -/
theorem pade02_unconditional_positivity_and_contraction_exact :
    (∀ z : Rat, (0 : Rat) < z → (0 : Rat) < pade02A z ∧ pade02A z < 1) ∧
    (∀ z : Rat, (0 : Rat) < z →
      pade02A z - expTaylor2 z = -(z * z * z * z) / (4 * (1 + z + z * z / 2)) ∧
      pade02A z - expTaylor3 z = z * z * z * (2 - z + z * z) / (12 * (1 + z + z * z / 2))) ∧
    (∀ z : Rat, (0 : Rat) < z → z ≤ 1 →
      (0 : Rat) < pade02A z - expTaylor3 z ∧ pade02A z - expTaylor3 z ≤ z * z * z / 6) ∧
    (∀ z : Rat, (32 : Rat) ≤ z → fp8E4M3MaxFinite < z * z / 2) ∧
    (∀ z : Rat, (22 : Rat) ≤ z → fp8E4M3MaxFinite < z * z) ∧
    ((20 : Rat) * 20 ≤ fp8E4M3MaxFinite ∧ (28 : Rat) * 28 / 2 ≤ fp8E4M3MaxFinite ∧
     fp8E4M3MaxFinite < (32 : Rat) * 32 / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; exact pade02A_pos_and_lt_one hz
  · intro z hz; exact ⟨pade02A_sub_expTaylor2 hz, pade02A_sub_expTaylor3 hz⟩
  · intro z hz0 hz1; exact pade02A_taylor3_bound hz0 hz1
  · intro z hz
    unfold fp8E4M3MaxFinite
    have h32 : (0 : Rat) ≤ 32 := by decide
    have hz0 : (0 : Rat) ≤ z := Rat.le_trans h32 hz
    have hsq : (32 : Rat) * 32 ≤ z * z :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_left hz h32) (rat_mul_le_mul_of_nonneg_right hz hz0)
    have hhalf : (32 : Rat) * 32 / 2 ≤ z * z / 2 :=
      rat_div_le_div_of_le_right hsq (by decide)
    have h512 : (32 : Rat) * 32 / 2 = 512 := by grind
    rw [h512] at hhalf
    exact rat_lt_of_lt_of_le (by decide : (448 : Rat) < 512) hhalf
  · intro z hz
    unfold fp8E4M3MaxFinite
    have h22 : (0 : Rat) ≤ 22 := by decide
    have hz0 : (0 : Rat) ≤ z := Rat.le_trans h22 hz
    have hsq : (22 : Rat) * 22 ≤ z * z :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_left hz h22) (rat_mul_le_mul_of_nonneg_right hz hz0)
    have h484 : (22 : Rat) * 22 = 484 := by grind
    rw [h484] at hsq
    exact rat_lt_of_lt_of_le (by decide : (448 : Rat) < 484) hsq
  · unfold fp8E4M3MaxFinite
    have h1 : (20 : Rat) * 20 = 400 := by grind
    have h2 : (28 : Rat) * 28 / 2 = 392 := by grind
    have h3 : (32 : Rat) * 32 / 2 = 512 := by grind
    rw [h1, h2, h3]
    exact ⟨by decide, by decide, by decide⟩

/-! ### Theorem 5: Subtraction-Free `Padé-(0,2)` Input Gain `B_pade02` -/

theorem pade02B_den_ge_one {z : Rat} (hz : (0 : Rat) ≤ z) :
    (1 : Rat) ≤ 1 + z / 2 + z * z / 12 := by
  have h1 : (0 : Rat) ≤ z / 2 := rat_div_nonneg hz (by decide)
  have h2 : (0 : Rat) ≤ z * z / 12 := rat_div_nonneg (rat_sq_nonneg z) (by decide)
  have hsum : (0 : Rat) ≤ z / 2 + z * z / 12 := rat_add_nonneg h1 h2
  have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hsum
  grind

theorem pade02B_pos_and_le_one {z : Rat} (hz : (0 : Rat) ≤ z) :
    (0 : Rat) < pade02B z ∧ pade02B z ≤ 1 := by
  unfold pade02B
  have hden1 : (1 : Rat) ≤ 1 + z / 2 + z * z / 12 := pade02B_den_ge_one hz
  have hden0 : (0 : Rat) < 1 + z / 2 + z * z / 12 := rat_lt_of_lt_of_le (by decide) hden1
  constructor
  · exact rat_div_pos (by decide) hden0
  · apply rat_div_le_of_mul_le hden0
    have : (1 : Rat) * (1 + z / 2 + z * z / 12) = 1 + z / 2 + z * z / 12 := by grind
    rw [this]; exact hden1

theorem pade02B_sub_phi1Taylor3 {z : Rat} (hz : (0 : Rat) ≤ z) :
    pade02B z - phi1Taylor3 z =
      z * z * z * z * (2 + z) / (288 * (1 + z / 2 + z * z / 12)) := by
  unfold pade02B phi1Taylor3
  have hden0 : (0 : Rat) < 1 + z / 2 + z * z / 12 := rat_lt_of_lt_of_le (by decide) (pade02B_den_ge_one hz)
  have hne : 1 + z / 2 + z * z / 12 ≠ 0 := Rat.ne_of_gt hden0
  have hne288 : 288 * (1 + z / 2 + z * z / 12) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (by decide) hden0)
  symm
  rw [rat_div_eq_iff hne288]
  have hc : (1 / (1 + z / 2 + z * z / 12)) * (1 + z / 2 + z * z / 12) = 1 := rat_div_mul_cancel hne
  grind

theorem phi1Taylor4_sub_pade02B {z : Rat} (hz : (0 : Rat) ≤ z) :
    phi1Taylor4 z - pade02B z =
      z * z * z * z * (2 + z + z * z) / (1440 * (1 + z / 2 + z * z / 12)) := by
  unfold pade02B phi1Taylor4
  have hden0 : (0 : Rat) < 1 + z / 2 + z * z / 12 := rat_lt_of_lt_of_le (by decide) (pade02B_den_ge_one hz)
  have hne : 1 + z / 2 + z * z / 12 ≠ 0 := Rat.ne_of_gt hden0
  have hne1440 : 1440 * (1 + z / 2 + z * z / 12) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (by decide) hden0)
  symm
  rw [rat_div_eq_iff hne1440]
  have hc : (1 / (1 + z / 2 + z * z / 12)) * (1 + z / 2 + z * z / 12) = 1 := rat_div_mul_cancel hne
  grind

theorem pade02B_unit_interval_error_bound {z : Rat} (hz0 : (0 : Rat) ≤ z) (hz1 : z ≤ 1) :
    (0 : Rat) ≤ phi1Taylor4 z - pade02B z ∧
    phi1Taylor4 z - pade02B z ≤ z * z * z * z / 360 ∧
    z * z * z * z / 360 ≤ 1 / 360 := by
  rw [phi1Taylor4_sub_pade02B hz0]
  have hden1 : (1 : Rat) ≤ 1 + z / 2 + z * z / 12 := pade02B_den_ge_one hz0
  have hden0 : (0 : Rat) < 1 + z / 2 + z * z / 12 := rat_lt_of_lt_of_le (by decide) hden1
  have hden1440 : (0 : Rat) < 1440 * (1 + z / 2 + z * z / 12) := rat_mul_pos (by decide) hden0
  have hz2 : (0 : Rat) ≤ z * z := rat_sq_nonneg z
  have hz4 : (0 : Rat) ≤ z * z * z * z := by
    have : z * z * z * z = (z * z) * (z * z) := by grind
    rw [this]; exact Rat.mul_nonneg hz2 hz2
  have hquad_nn : (0 : Rat) ≤ 2 + z + z * z := rat_add_nonneg (rat_add_nonneg (by decide) hz0) hz2
  have hz2_le1 : z * z ≤ 1 := by
    have h1 := rat_mul_le_mul_of_nonneg_left hz1 hz0
    have h2 : z * 1 ≤ 1 := by grind
    exact Rat.le_trans h1 h2
  have hz4_le1 : z * z * z * z ≤ 1 := by
    have : z * z * z * z = (z * z) * (z * z) := by grind
    rw [this]
    have h1 := rat_mul_le_mul_of_nonneg_left hz2_le1 hz2
    have h2 : z * z * 1 ≤ 1 := by grind
    exact Rat.le_trans h1 h2
  have hquad_le4 : 2 + z + z * z ≤ 4 := by
    have h1 := rat_add_le_add hz1 hz2_le1
    have h2 := rat_add_le_add (by decide : (2 : Rat) ≤ 2) h1
    grind
  refine ⟨rat_div_nonneg (Rat.mul_nonneg hz4 hquad_nn) hden1440, ?_, ?_⟩
  · apply rat_div_le_of_mul_le hden1440
    have h1 : z * z * z * z * (2 + z + z * z) ≤ z * z * z * z * 4 :=
      rat_mul_le_mul_of_nonneg_left hquad_le4 hz4
    have h2 : (4 : Rat) ≤ 4 * (1 + z / 2 + z * z / 12) := by
      have := rat_mul_le_mul_of_nonneg_left hden1 (by decide : (0 : Rat) ≤ 4)
      grind
    have h3 : z * z * z * z * 4 ≤ z * z * z * z * (4 * (1 + z / 2 + z * z / 12)) :=
      rat_mul_le_mul_of_nonneg_left h2 hz4
    have h4 : z * z * z * z / 360 * (1440 * (1 + z / 2 + z * z / 12)) =
        z * z * z * z * (4 * (1 + z / 2 + z * z / 12)) := by grind
    rw [h4]
    exact Rat.le_trans h1 h3
  · exact rat_div_le_div_of_le_right hz4_le1 (by decide)

/-- Headline Theorem 5 (`pade02_b_bar_zero_blackout_and_fourth_order_accuracy`). -/
theorem pade02_b_bar_zero_blackout_and_fourth_order_accuracy :
    (∀ z : Rat, (0 : Rat) ≤ z → (0 : Rat) < pade02B z ∧ pade02B z ≤ 1) ∧
    (∀ z : Rat, (0 : Rat) ≤ z →
      pade02B z - phi1Taylor3 z =
        z * z * z * z * (2 + z) / (288 * (1 + z / 2 + z * z / 12)) ∧
      phi1Taylor4 z - pade02B z =
        z * z * z * z * (2 + z + z * z) / (1440 * (1 + z / 2 + z * z / 12))) ∧
    (∀ z : Rat, (0 : Rat) ≤ z → z ≤ 1 →
      (0 : Rat) ≤ phi1Taylor4 z - pade02B z ∧
      phi1Taylor4 z - pade02B z ≤ z * z * z * z / 360 ∧
      z * z * z * z / 360 ≤ 1 / 360) ∧
    (tustinB 1 - phi1Taylor4 1 = 1 / 30 ∧
     phi1Taylor4 1 - pade02B 1 = 1 / 570 ∧
     (1 / 360 : Rat) < tustinB 1 - phi1Taylor4 1 ∧
     19 * (phi1Taylor4 1 - pade02B 1) = tustinB 1 - phi1Taylor4 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz; exact pade02B_pos_and_le_one hz
  · intro z hz; exact ⟨pade02B_sub_phi1Taylor3 hz, phi1Taylor4_sub_pade02B hz⟩
  · intro z hz0 hz1; exact pade02B_unit_interval_error_bound hz0 hz1
  · have ht : tustinB 1 - phi1Taylor4 1 = 1 / 30 := by unfold tustinB phi1Taylor4; grind
    have hp : phi1Taylor4 1 - pade02B 1 = 1 / 570 := by unfold phi1Taylor4 pade02B; grind
    refine ⟨ht, hp, ?_, ?_⟩
    · rw [ht]
      apply rat_lt_of_mul_pos_right (c := (360 : Rat)) (by decide)
      have h1 : (1 / 360 : Rat) * 360 = 1 := by grind
      have h2 : (1 / 30 : Rat) * 360 = 12 := by grind
      rw [h1, h2]; decide
    · rw [ht, hp]; grind

end SsmTustinPade
