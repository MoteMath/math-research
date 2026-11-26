/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmTustinPade.RatOrder

/-!
# Theorems 2 & 3: Infinite-Memory `2×` Stall Separation & Naive ZOH `B_bar` Blackout Horizon

- Theorem 2 (`tustin_vs_zoh_infinite_memory_stall_two_x_gap`):
  Proves that `Tustin` and `Padé-(0,2)` snap to exact `+1.0` for all `0 < z ≤ 2^(-p)`
  (`1/8, 1/16, 1/256, 1/2048`), whereas `ZOH` (`exp(-z)`) snaps to `+1.0` only for
  `0 < z ≤ 2^(-(p+1))` (`1/16, 1/32, 1/512, 1/4096`), establishing an exact `2×` small-`z`
  resolution separation.
- Theorem 3 (`zoh_b_bar_catastrophic_cancellation_blackout_horizon`):
  Proves that naive `ZOH` input discretization `fl((1 - fl(exp(-z))) / z)` suffers exact
  `100%` blackout (`0.0`) for all `0 < z ≤ 2^(-(p+1))`, and proves the universal closed-form
  IEEE-754 `(0, 1]` blackout fraction `(B - f - 2) / B` (`15104 / 16256 = 118 / 127 > 92.91%`
  in `BF16`, `44 / 60 = 11 / 15` in `FP8-E5M2`, `16 / 56 = 2 / 7` in `FP8-E4M3`,
  `3072 / 15360 = 1 / 5` in `FP16`).
-/

namespace SsmTustinPade

theorem invPow2Rat_le_of_le {m n : Nat} (h : m ≤ n) : invPow2Rat n ≤ invPow2Rat m := by
  unfold invPow2Rat pow2Rat
  apply rat_div_le_div_of_le_left (by decide) (natCast_rat_pos (Nat.two_pow_pos m))
  exact natCast_rat_le (Nat.pow_le_pow_right (by omega) h)

theorem tustin_and_pade02_stall_on_horizon {p : Nat} (hp : 1 ≤ p) {z : Rat}
    (hz0 : (0 : Rat) < z) (hz : z ≤ tustinStallHorizon p) :
    rneSnapsToTwoBelow p (2 - z) ∧
    rneSnapsToTwoAbove p (2 + z) ∧
    rneSnapsToPosOneAbove p (1 + z) ∧
    rneSnapsToPosOneAbove p (1 + z * z / 2) := by
  unfold tustinStallHorizon at hz
  have h1p : invPow2Rat p ≤ invPow2Rat (p - 1) := invPow2Rat_le_of_le (by omega)
  have hle1 : invPow2Rat p ≤ (1 : Rat) := by
    have := invPow2Rat_le_of_le (m := 0) (n := p) (by omega)
    have h0 : invPow2Rat 0 = 1 := by unfold invPow2Rat pow2Rat; grind
    rw [h0] at this
    exact this
  have hz_le1 : z ≤ 1 := Rat.le_trans hz hle1
  have hz2_le_z : z * z / 2 ≤ z := by
    have hzsq : z * z ≤ z * 1 := rat_mul_le_mul_of_nonneg_left hz_le1 (Rat.le_of_lt hz0)
    have hzsq' : z * z ≤ z := by grind
    apply rat_div_le_of_mul_le (by decide : (0 : Rat) < 2)
    have h2z : z ≤ z * 2 := by
      have := rat_mul_le_mul_of_nonneg_left (by decide : (1 : Rat) ≤ 2) (Rat.le_of_lt hz0)
      grind
    exact Rat.le_trans hzsq' h2z
  have hz2_nonneg : (0 : Rat) ≤ z * z / 2 :=
    rat_div_nonneg (rat_sq_nonneg z) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold rneSnapsToTwoBelow
    constructor
    · have hsub := rat_sub_nonneg hz
      have : (2 - z) - (2 - invPow2Rat p) = invPow2Rat p - z := by grind
      exact rat_le_of_sub_nonneg (by rw [this]; exact hsub)
    · have := (Rat.add_le_add_right (c := (2 : Rat))).mpr (Rat.le_of_lt hz0)
      grind
  · unfold rneSnapsToTwoAbove
    constructor
    · have := (Rat.add_le_add_right (c := (2 : Rat))).mpr (Rat.le_of_lt hz0)
      grind
    · have hle := Rat.le_trans hz h1p
      have := (Rat.add_le_add_right (c := (2 : Rat))).mpr hle
      grind
  · unfold rneSnapsToPosOneAbove
    constructor
    · have := (Rat.add_le_add_right (c := (1 : Rat))).mpr (Rat.le_of_lt hz0)
      grind
    · have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hz
      grind
  · unfold rneSnapsToPosOneAbove
    constructor
    · have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hz2_nonneg
      grind
    · have hle := Rat.le_trans hz2_le_z hz
      have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hle
      grind

theorem zoh_stalls_on_horizon (p : Nat) {z ez : Rat}
    (hz : z ≤ zohStallHorizon p) (hlo : 1 - z ≤ ez) (hhi : ez ≤ 1) :
    rneSnapsToPosOneBelow p ez := by
  unfold rneSnapsToPosOneBelow
  unfold zohStallHorizon at hz
  refine ⟨?_, hhi⟩
  have h1 : 1 - invPow2Rat (p + 1) ≤ 1 - z := by
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hz
    have : (1 - z) - (1 - invPow2Rat (p + 1)) = invPow2Rat (p + 1) - z := by grind
    rw [this]; exact hsub
  exact Rat.le_trans h1 hlo

theorem zoh_no_stall_at_tustin_horizon {p : Nat} (hp : 2 ≤ p) {ez : Rat}
    (hup : ez < 1 - tustinStallHorizon p + tustinStallHorizon p * tustinStallHorizon p / 2) :
    ¬ rneSnapsToPosOneBelow p ez := by
  intro ⟨hlo, _⟩
  unfold tustinStallHorizon at hup
  have h1 : 1 - invPow2Rat p + invPow2Rat p * invPow2Rat p / 2 < 1 - invPow2Rat (p + 1) := by
    have h2 : invPow2Rat p = 2 * invPow2Rat (p + 1) := (two_mul_invPow2Rat_succ p).symm
    have hlt_half : invPow2Rat p * invPow2Rat p / 2 < invPow2Rat (p + 1) := by
      have hp_pos : (0 : Rat) < invPow2Rat p := invPow2Rat_pos p
      have hp_lt1 : invPow2Rat p < 1 := by
        unfold invPow2Rat pow2Rat
        apply rat_div_lt_of_mul_lt (natCast_rat_pos (Nat.two_pow_pos p))
        have h4 : 4 ≤ 2 ^ p := by
          have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp
          omega
        have h4r : (4 : Rat) ≤ ((2 ^ p : Nat) : Rat) := natCast_rat_le h4
        have : (1 : Rat) < 4 := by decide
        have := rat_lt_of_lt_of_le this h4r
        grind
      have hsq_lt : invPow2Rat p * invPow2Rat p < invPow2Rat p := by
        have := rat_mul_lt_mul_of_pos_left hp_lt1 hp_pos
        grind
      rw [invPow2Rat_succ]
      apply rat_div_lt_of_mul_lt (by decide : (0 : Rat) < 2)
      rw [rat_div_mul_cancel (by decide : (2 : Rat) ≠ 0)]
      exact hsq_lt
    apply rat_lt_of_sub_pos
    have heq : (1 - invPow2Rat (p + 1)) - (1 - invPow2Rat p + invPow2Rat p * invPow2Rat p / 2) =
        invPow2Rat (p + 1) - invPow2Rat p * invPow2Rat p / 2 := by
      rw [h2]; grind
    rw [heq]
    exact rat_sub_pos hlt_half
  exact Rat.not_le.mpr (rat_lt_trans hup h1) hlo

/-- Headline Theorem 2 (`tustin_vs_zoh_infinite_memory_stall_two_x_gap`). -/
theorem tustin_vs_zoh_infinite_memory_stall_two_x_gap :
    (tustinStallHorizon 3 = 1 / 8 ∧ tustinStallHorizon 4 = 1 / 16 ∧
     tustinStallHorizon 8 = 1 / 256 ∧ tustinStallHorizon 11 = 1 / 2048) ∧
    (zohStallHorizon 3 = 1 / 16 ∧ zohStallHorizon 4 = 1 / 32 ∧
     zohStallHorizon 8 = 1 / 512 ∧ zohStallHorizon 11 = 1 / 4096) ∧
    (∀ p : Nat,
      tustinStallHorizon p = 2 * zohStallHorizon p ∧
      tustinStallHorizon p / zohStallHorizon p = 2) ∧
    (∀ (p : Nat) (z : Rat), 1 ≤ p → (0 : Rat) < z → z ≤ tustinStallHorizon p →
      rneSnapsToTwoBelow p (2 - z) ∧
      rneSnapsToTwoAbove p (2 + z) ∧
      rneSnapsToPosOneAbove p (1 + z) ∧
      rneSnapsToPosOneAbove p (1 + z * z / 2)) ∧
    (∀ (p : Nat) (z ez : Rat), z ≤ zohStallHorizon p → 1 - z ≤ ez → ez ≤ 1 →
      rneSnapsToPosOneBelow p ez) ∧
    (∀ (p : Nat) (ez : Rat), 2 ≤ p →
      ez < 1 - tustinStallHorizon p + tustinStallHorizon p * tustinStallHorizon p / 2 →
      ¬ rneSnapsToPosOneBelow p ez) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tustinStallHorizon invPow2Rat pow2Rat; grind
  · unfold zohStallHorizon invPow2Rat pow2Rat; grind
  · intro p
    exact ⟨(two_mul_invPow2Rat_succ p).symm, invPow2Rat_div_invPow2Rat_succ p⟩
  · intro p z hp hz0 hz
    exact tustin_and_pade02_stall_on_horizon hp hz0 hz
  · intro p z ez hz hlo hhi
    exact zoh_stalls_on_horizon p hz hlo hhi
  · intro p ez hp hup
    exact zoh_no_stall_at_tustin_horizon hp hup

/-! ### Theorem 3: Naive `ZOH` `B_bar` Catastrophic Cancellation Blackout Horizon -/

theorem naiveZohBBar_blackout_exact (p : Nat) {z ez : Rat}
    (hz : z ≤ zohStallHorizon p) (hlo : 1 - z ≤ ez) (hhi : ez ≤ 1) :
    flNearOneBelow p ez = 1 ∧ naiveZohBBar p ez z = 0 := by
  have hsnap : rneSnapsToPosOneBelow p ez := zoh_stalls_on_horizon p hz hlo hhi
  have hfl : flNearOneBelow p ez = 1 := by
    unfold flNearOneBelow
    unfold rneSnapsToPosOneBelow at hsnap
    simp [hsnap]
  refine ⟨hfl, ?_⟩
  unfold naiveZohBBar
  rw [hfl]
  have : (1 : Rat) - 1 = 0 := by grind
  rw [this]
  simp [Rat.div_def]

theorem count_blackout_ratio_exact {B f : Nat} (hB : f + 3 ≤ B) :
    countUnitInterval B f = B * 2 ^ f ∧
    countBlackoutInterval B f = (B - f - 2) * 2 ^ f ∧
    (countBlackoutInterval B f : Rat) / (countUnitInterval B f : Rat) =
      ((B - f - 2 : Nat) : Rat) / (B : Rat) := by
  have hpow_pos : 1 ≤ 2 ^ f := Nat.two_pow_pos f
  have hunit : countUnitInterval B f = B * 2 ^ f := by
    unfold countUnitInterval
    have h1 : B = (B - 1) + 1 := by omega
    have h2 : B * 2 ^ f = (B - 1) * 2 ^ f + 2 ^ f := by
      conv => lhs; rw [h1]
      rw [Nat.add_mul, Nat.one_mul]
    omega
  have hblk : countBlackoutInterval B f = (B - f - 2) * 2 ^ f := by
    unfold countBlackoutInterval
    have h1 : B - f - 2 = (B - f - 3) + 1 := by omega
    have h2 : (B - f - 2) * 2 ^ f = (B - f - 3) * 2 ^ f + 2 ^ f := by
      conv => lhs; rw [h1]
      rw [Nat.add_mul, Nat.one_mul]
    omega
  refine ⟨hunit, hblk, ?_⟩
  rw [hunit, hblk]
  have hBpos : (0 : Rat) < (B : Rat) := natCast_rat_pos (by omega)
  have hden_ne : ((B * 2 ^ f : Nat) : Rat) ≠ 0 := by
    have : (0 : Rat) < ((B * 2 ^ f : Nat) : Rat) := natCast_rat_pos (Nat.mul_pos (by omega) hpow_pos)
    exact Rat.ne_of_gt this
  rw [rat_div_eq_iff hden_ne]
  have hmul_cast : ((B * 2 ^ f : Nat) : Rat) = (B : Rat) * ((2 ^ f : Nat) : Rat) := by simp
  have hblk_cast : (((B - f - 2) * 2 ^ f : Nat) : Rat) =
      ((B - f - 2 : Nat) : Rat) * ((2 ^ f : Nat) : Rat) := by simp
  rw [hmul_cast, hblk_cast]
  have hc : (((B - f - 2 : Nat) : Rat) / (B : Rat)) * (B : Rat) = ((B - f - 2 : Nat) : Rat) :=
    rat_div_mul_cancel (Rat.ne_of_gt hBpos)
  grind

/-- Headline Theorem 3 (`zoh_b_bar_catastrophic_cancellation_blackout_horizon`). -/
theorem zoh_b_bar_catastrophic_cancellation_blackout_horizon :
    (∀ (p : Nat) (z ez : Rat),
      z ≤ zohStallHorizon p → 1 - z ≤ ez → ez ≤ 1 →
      flNearOneBelow p ez = 1 ∧ naiveZohBBar p ez z = 0) ∧
    (zohStallHorizon 3 = 1 / 16 ∧ zohStallHorizon 4 = 1 / 32 ∧
     zohStallHorizon 8 = 1 / 512 ∧ zohStallHorizon 11 = 1 / 4096) ∧
    (∀ B f : Nat, f + 3 ≤ B →
      countUnitInterval B f = B * 2 ^ f ∧
      countBlackoutInterval B f = (B - f - 2) * 2 ^ f ∧
      (countBlackoutInterval B f : Rat) / (countUnitInterval B f : Rat) =
        ((B - f - 2 : Nat) : Rat) / (B : Rat)) ∧
    (countUnitInterval 127 7 = 16256 ∧ countBlackoutInterval 127 7 = 15104 ∧
     (15104 : Rat) / 16256 = 118 / 127 ∧
     (9291 / 10000 : Rat) < (15104 : Rat) / 16256 ∧
     (15104 : Rat) / 16256 < 9292 / 10000) ∧
    (countUnitInterval 15 2 = 60 ∧ countBlackoutInterval 15 2 = 44 ∧
     (44 : Rat) / 60 = 11 / 15 ∧
     countUnitInterval 7 3 = 56 ∧ countBlackoutInterval 7 3 = 16 ∧
     (16 : Rat) / 56 = 2 / 7 ∧
     countUnitInterval 15 10 = 15360 ∧ countBlackoutInterval 15 10 = 3072 ∧
     (3072 : Rat) / 15360 = 1 / 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p z ez hz hlo hhi
    exact naiveZohBBar_blackout_exact p hz hlo hhi
  · unfold zohStallHorizon invPow2Rat pow2Rat; grind
  · intro B f hB
    exact count_blackout_ratio_exact hB
  · refine ⟨by decide, by decide, by grind, ?_, ?_⟩
    · apply rat_lt_of_mul_pos_right (c := (162560000 : Rat)) (by decide)
      have h1 : (9291 / 10000 : Rat) * 162560000 = 151034496 := by grind
      have h2 : (15104 : Rat) / 16256 * 162560000 = 151040000 := by grind
      rw [h1, h2]; decide
    · apply rat_lt_of_mul_pos_right (c := (162560000 : Rat)) (by decide)
      have h1 : (15104 : Rat) / 16256 * 162560000 = 151040000 := by grind
      have h2 : (9292 / 10000 : Rat) * 162560000 = 151050752 := by grind
      rw [h1, h2]; decide
  · refine ⟨by decide, by decide, by grind, by decide, by decide, by grind,
            by decide, by decide, by grind⟩

end SsmTustinPade
