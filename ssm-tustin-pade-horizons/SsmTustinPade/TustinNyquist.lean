/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmTustinPade.RatOrder

/-!
# Theorem 1: Tustin Nyquist Snap-to-`-1.0` Horizon (`tustin_nyquist_snap_to_minus_one_horizon_exact`)

Proves both:
1. The exact rational identity `A_tustin(z) = (1 - z/2)/(1 + z/2) = -1 + 4/(z + 2) ∈ (-1, 1)`
   and its exact single-rounding IEEE-754 RNE snap-to-`-1.0` equivalence
   `4/(z + 2) ≤ 2^(-(p+1)) ↔ 2^(p+3) - 2 ≤ z`.
2. The exact two-step IEEE-754 RNE `fl(fl(2 - z) / fl(2 + z))` first-snap horizon
   `z_osc(p) = 2^(p+1) + 8` (`24` E5M2, `40` E4M3, `520` BF16, `4104` FP16), proving that
   `z_osc(p)` snaps identically to `-1.0`, the two preceding representables `2^(p+1)` and
   `2^(p+1) + 4` do not, and every representable in binades `k ≥ p + 2` (`z ≥ 2^(p+2)`)
   snaps unconditionally to `-1.0`.
-/

namespace SsmTustinPade

theorem tustinA_eq_neg_one_add {z : Rat} (hz : (0 : Rat) < z) :
    tustinA z = -1 + 4 / (z + 2) := by
  unfold tustinA
  have h1 : (0 : Rat) < 1 + z / 2 := rat_add_pos_of_pos_of_nonneg (by decide) (rat_div_nonneg (Rat.le_of_lt hz) (by decide))
  have h2 : (0 : Rat) < z + 2 := rat_add_pos_of_nonneg_of_pos (Rat.le_of_lt hz) (by decide)
  have hne1 : 1 + z / 2 ≠ 0 := Rat.ne_of_gt h1
  have hne2 : z + 2 ≠ 0 := Rat.ne_of_gt h2
  rw [rat_div_eq_iff hne1]
  have hmul : (-1 + 4 / (z + 2)) * (1 + z / 2) = -(1 + z / 2) + (4 / (z + 2)) * ((z + 2) / 2) := by
    have : (1 : Rat) + z / 2 = (z + 2) / 2 := by grind
    grind
  rw [hmul]
  have hc : (4 / (z + 2)) * ((z + 2) / 2) = 2 := by
    have hdiv : (4 / (z + 2)) * (z + 2) = 4 := rat_div_mul_cancel hne2
    grind
  rw [hc]
  grind

theorem tustinA_bounds {z : Rat} (hz : (0 : Rat) < z) :
    (-1 : Rat) < tustinA z ∧ tustinA z < 1 := by
  rw [tustinA_eq_neg_one_add hz]
  have hz2 : (0 : Rat) < z + 2 := rat_add_pos_of_nonneg_of_pos (Rat.le_of_lt hz) (by decide)
  have h4pos : (0 : Rat) < 4 / (z + 2) := rat_div_pos (by decide) hz2
  have h4lt2 : 4 / (z + 2) < 2 := by
    apply rat_div_lt_of_mul_lt hz2
    have h2z : (0 : Rat) < 2 * z := rat_mul_pos (by decide) hz
    apply rat_lt_of_sub_pos
    have : 2 * (z + 2) - 4 = 2 * z := by grind
    rw [this]; exact h2z
  constructor
  · apply rat_lt_of_sub_pos
    have : (-1 + 4 / (z + 2)) - (-1 : Rat) = 4 / (z + 2) := by grind
    rw [this]; exact h4pos
  · apply rat_lt_of_sub_pos
    have hsub : (0 : Rat) < 2 - 4 / (z + 2) := rat_sub_pos h4lt2
    have : (1 : Rat) - (-1 + 4 / (z + 2)) = 2 - 4 / (z + 2) := by grind
    rw [this]; exact hsub

theorem tustin_single_round_iff (p : Nat) {z : Rat} (hz : (0 : Rat) < z) :
    (rneSnapsToNegOne p (tustinA z) ↔ 4 / (z + 2) ≤ invPow2Rat (p + 1)) ∧
    (4 / (z + 2) ≤ invPow2Rat (p + 1) ↔ (tustinSingleRoundOscThreshold p : Rat) ≤ z) := by
  have hb := tustinA_bounds hz
  have heq := tustinA_eq_neg_one_add hz
  have hz2 : (0 : Rat) < z + 2 := rat_add_pos_of_nonneg_of_pos (Rat.le_of_lt hz) (by decide)
  have hp1 : (0 : Rat) < pow2Rat (p + 1) := pow2Rat_pos (p + 1)
  constructor
  · unfold rneSnapsToNegOne
    rw [heq]
    constructor
    · intro ⟨_, hhi⟩
      have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hhi
      grind
    · intro hle
      refine ⟨Rat.le_of_lt (by rw [← heq]; exact hb.1), ?_⟩
      have := (Rat.add_le_add_right (c := (-1 : Rat))).mpr hle
      grind
  · unfold invPow2Rat tustinSingleRoundOscThreshold
    have hpow3 : (2 ^ (p + 3) : Nat) = 4 * 2 ^ (p + 1) := by
      have : p + 3 = (p + 1) + 2 := by omega
      rw [this, Nat.pow_add]
      omega
    have hge2 : 2 ≤ 2 ^ (p + 3) := by
      have h1 : 1 ≤ 2 ^ (p + 1) := Nat.two_pow_pos (p + 1)
      omega
    have hcast : (((2 ^ (p + 3) - 2 : Nat) : Rat)) = 4 * pow2Rat (p + 1) - 2 := by
      have hadd : (2 ^ (p + 3) - 2) + 2 = 4 * 2 ^ (p + 1) := by omega
      have hrat : (((2 ^ (p + 3) - 2) + 2 : Nat) : Rat) = ((4 * 2 ^ (p + 1) : Nat) : Rat) := by
        rw [hadd]
      unfold pow2Rat
      simp at hrat
      grind
    rw [hcast]
    constructor
    · intro hle
      have h1 : 4 / (z + 2) * (z + 2) ≤ (1 / pow2Rat (p + 1)) * (z + 2) :=
        rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hz2)
      rw [rat_div_mul_cancel (Rat.ne_of_gt hz2)] at h1
      have h2 : (4 : Rat) * pow2Rat (p + 1) ≤ (1 / pow2Rat (p + 1)) * (z + 2) * pow2Rat (p + 1) :=
        rat_mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp1)
      have hc : (1 / pow2Rat (p + 1)) * (z + 2) * pow2Rat (p + 1) = z + 2 := by
        have := rat_div_mul_cancel (a := (1 : Rat)) (pow2Rat_ne_zero (p + 1))
        grind
      rw [hc] at h2
      have := (Rat.add_le_add_right (c := (-2 : Rat))).mpr h2
      grind
    · intro hge
      have h2 : 4 * pow2Rat (p + 1) ≤ z + 2 := by
        have := (Rat.add_le_add_right (c := (2 : Rat))).mpr hge
        grind
      apply rat_div_le_of_mul_le hz2
      apply rat_le_of_mul_pos_right hp1
      have hc : (1 / pow2Rat (p + 1)) * (z + 2) * pow2Rat (p + 1) = z + 2 := by
        have := rat_div_mul_cancel (a := (1 : Rat)) (pow2Rat_ne_zero (p + 1))
        grind
      rw [hc]
      exact h2

theorem two_pow_pred_even {p : Nat} (hp : 2 ≤ p) : 2 ^ (p - 1) % 2 = 0 := by
  have h1 : p - 1 = (p - 2) + 1 := by omega
  rw [h1, Nat.pow_succ]
  omega

theorem binadeRneNat_tustinOscHorizon {p : Nat} (hp : 2 ≤ p) :
    binadeUlp p (p + 1) = 4 ∧
    binadeRneNat p (p + 1) (tustinOscHorizon p + 2) = tustinOscHorizon p ∧
    binadeRneNat p (p + 1) (tustinOscHorizon p - 2) = tustinOscHorizon p := by
  have hpow : 2 ^ (p + 1) = 2 ^ (p - 1) * 4 := by
    have : p + 1 = (p - 1) + 2 := by omega
    rw [this, Nat.pow_add]
  have heven : 2 ^ (p - 1) % 2 = 0 := two_pow_pred_even hp
  have hulp : binadeUlp p (p + 1) = 4 := by
    unfold binadeUlp
    have : p + 1 + 1 - p = 2 := by omega
    rw [this]
  have h22 : (2 ^ 2 : Nat) = 4 := rfl
  have h21 : (2 ^ 1 : Nat) = 2 := rfl
  refine ⟨hulp, ?_, ?_⟩
  · unfold binadeRneNat tustinOscHorizon
    have hlt : ¬ (p + 1 < p) := by omega
    have h1 : p + 1 + 1 - p = 2 := by omega
    have h2 : p + 1 - p = 1 := by omega
    simp only [hlt, ↓reduceIte, h1, h2, h22, h21]
    have hdiv : (2 ^ (p + 1) + 8 + 2) / 4 = 2 ^ (p - 1) + 2 := by omega
    have hmod : (2 ^ (p + 1) + 8 + 2) % 4 = 2 := by omega
    have hqeven : (2 ^ (p - 1) + 2) % 2 = 0 := by omega
    simp [hdiv, hmod, hqeven]
    omega
  · unfold binadeRneNat tustinOscHorizon
    have hlt : ¬ (p + 1 < p) := by omega
    have h1 : p + 1 + 1 - p = 2 := by omega
    have h2 : p + 1 - p = 1 := by omega
    simp only [hlt, ↓reduceIte, h1, h2, h22, h21]
    have hdiv : (2 ^ (p + 1) + 6) / 4 = 2 ^ (p - 1) + 1 := by omega
    have hmod : (2 ^ (p + 1) + 6) % 4 = 2 := by omega
    have hqodd : ¬ ((2 ^ (p - 1) + 1) % 2 = 0) := by omega
    simp [hdiv, hmod, hqodd]
    omega

theorem binadeRneNat_below_tustinOscHorizon {p : Nat} (hp : 2 ≤ p) :
    binadeRneNat p (p + 1) (2 ^ (p + 1) + 4 + 2) = 2 ^ (p + 1) + 8 ∧
    binadeRneNat p (p + 1) (2 ^ (p + 1) + 4 - 2) = 2 ^ (p + 1) ∧
    binadeRneNat p (p + 1) (2 ^ (p + 1) + 2) = 2 ^ (p + 1) ∧
    binadeRneNat p p (2 ^ (p + 1) - 2) = 2 ^ (p + 1) - 2 ∧
    ¬ rneSnapsToNegOne p (-((2 ^ (p + 1) : Rat) / ((2 ^ (p + 1) + 8 : Nat) : Rat))) ∧
    ¬ rneSnapsToNegOne p (-(((2 ^ (p + 1) - 2 : Nat) : Rat) / (2 ^ (p + 1) : Rat))) := by
  have hpow : 2 ^ (p + 1) = 2 ^ (p - 1) * 4 := by
    have : p + 1 = (p - 1) + 2 := by omega
    rw [this, Nat.pow_add]
  have heven : 2 ^ (p - 1) % 2 = 0 := two_pow_pred_even hp
  have hpow_ge8 : 8 ≤ 2 ^ (p + 1) := by
    have : 2 ^ 3 ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h22 : (2 ^ 2 : Nat) = 4 := rfl
  have h21 : (2 ^ 1 : Nat) = 2 := rfl
  have h20 : (2 ^ 0 : Nat) = 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold binadeRneNat
    have hlt : ¬ (p + 1 < p) := by omega
    have h1 : p + 1 + 1 - p = 2 := by omega
    have h2 : p + 1 - p = 1 := by omega
    simp only [hlt, ↓reduceIte, h1, h2, h22, h21]
    have hdiv : (2 ^ (p + 1) + 4 + 2) / 4 = 2 ^ (p - 1) + 1 := by omega
    have hmod : (2 ^ (p + 1) + 4 + 2) % 4 = 2 := by omega
    have hqodd : ¬ ((2 ^ (p - 1) + 1) % 2 = 0) := by omega
    simp [hdiv, hmod, hqodd]
    omega
  · unfold binadeRneNat
    have hlt : ¬ (p + 1 < p) := by omega
    have h1 : p + 1 + 1 - p = 2 := by omega
    have h2 : p + 1 - p = 1 := by omega
    simp only [hlt, ↓reduceIte, h1, h2, h22, h21]
    have hdiv : (2 ^ (p + 1) + 2) / 4 = 2 ^ (p - 1) := by omega
    have hmod : (2 ^ (p + 1) + 2) % 4 = 2 := by omega
    simp [hdiv, hmod, heven]
    omega
  · unfold binadeRneNat
    have hlt : ¬ (p + 1 < p) := by omega
    have h1 : p + 1 + 1 - p = 2 := by omega
    have h2 : p + 1 - p = 1 := by omega
    simp only [hlt, ↓reduceIte, h1, h2, h22, h21]
    have hdiv : (2 ^ (p + 1) + 2) / 4 = 2 ^ (p - 1) := by omega
    have hmod : (2 ^ (p + 1) + 2) % 4 = 2 := by omega
    simp [hdiv, hmod, heven]
    omega
  · unfold binadeRneNat
    have hlt : ¬ (p < p) := by omega
    have h1 : p + 1 - p = 1 := by omega
    have h2 : p - p = 0 := by omega
    simp only [hlt, ↓reduceIte, h1, h2, h21, h20]
    have hmod : (2 ^ (p + 1) - 2) % 2 = 0 := by omega
    simp [hmod]
    omega
  · intro ⟨_, hhi⟩
    unfold invPow2Rat pow2Rat at hhi
    have hp1_pos : (0 : Rat) < ((2 ^ (p + 1) : Nat) : Rat) := natCast_rat_pos (Nat.two_pow_pos (p + 1))
    have hden_pos : (0 : Rat) < ((2 ^ (p + 1) + 8 : Nat) : Rat) := by
      have : 0 < 2 ^ (p + 1) + 8 := by omega
      exact natCast_rat_pos this
    have hcast8 : ((2 ^ (p + 1) + 8 : Nat) : Rat) = ((2 ^ (p + 1) : Nat) : Rat) + 8 := by simp
    have hrew : -((2 ^ (p + 1) : Rat) / ((2 ^ (p + 1) + 8 : Nat) : Rat)) =
        -1 + 8 / ((2 ^ (p + 1) + 8 : Nat) : Rat) := by
      have hne : ((2 ^ (p + 1) + 8 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hden_pos
      have h1 : ((2 ^ (p + 1) : Nat) : Rat) / ((2 ^ (p + 1) + 8 : Nat) : Rat) +
          8 / ((2 ^ (p + 1) + 8 : Nat) : Rat) = 1 := by
        rw [rat_add_div_same hne, ← hcast8, rat_div_eq_iff hne]
        grind
      have h2 : (2 ^ (p + 1) : Rat) = ((2 ^ (p + 1) : Nat) : Rat) := by simp
      rw [h2]; grind
    rw [hrew] at hhi
    have hle : 8 / ((2 ^ (p + 1) + 8 : Nat) : Rat) ≤ 1 / ((2 ^ (p + 1) : Nat) : Rat) := by
      have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hhi
      grind
    have hmul1 := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hden_pos)
    rw [rat_div_mul_cancel (Rat.ne_of_gt hden_pos)] at hmul1
    have hmul2 := rat_mul_le_mul_of_nonneg_right hmul1 (Rat.le_of_lt hp1_pos)
    have hc : (1 / ((2 ^ (p + 1) : Nat) : Rat)) * ((2 ^ (p + 1) + 8 : Nat) : Rat) *
        ((2 ^ (p + 1) : Nat) : Rat) = ((2 ^ (p + 1) + 8 : Nat) : Rat) := by
      have := rat_div_mul_cancel (a := (1 : Rat)) (Rat.ne_of_gt hp1_pos)
      grind
    rw [hc, hcast8] at hmul2
    have hge8 : (8 : Rat) ≤ ((2 ^ (p + 1) : Nat) : Rat) := natCast_rat_le hpow_ge8
    have hcontra : ((2 ^ (p + 1) : Nat) : Rat) + 8 < 8 * ((2 ^ (p + 1) : Nat) : Rat) := by
      apply rat_lt_of_sub_pos
      have hsub : 8 * ((2 ^ (p + 1) : Nat) : Rat) - (((2 ^ (p + 1) : Nat) : Rat) + 8) =
          7 * ((2 ^ (p + 1) : Nat) : Rat) + (-8) := by grind
      rw [hsub]
      have h56 : (56 : Rat) ≤ 7 * ((2 ^ (p + 1) : Nat) : Rat) := by
        have := rat_mul_le_mul_of_nonneg_left hge8 (by decide : (0 : Rat) ≤ 7)
        grind
      have h56' : (48 : Rat) ≤ 7 * ((2 ^ (p + 1) : Nat) : Rat) + (-8) := by
        have := (Rat.add_le_add_right (c := (-8 : Rat))).mpr h56
        have h48 : (56 : Rat) + (-8) = 48 := by grind
        rw [h48] at this
        exact this
      exact rat_lt_of_lt_of_le (by decide : (0 : Rat) < 48) h56'
    exact Rat.not_le.mpr hcontra hmul2
  · intro ⟨_, hhi⟩
    unfold invPow2Rat pow2Rat at hhi
    have hp1_pos : (0 : Rat) < ((2 ^ (p + 1) : Nat) : Rat) := natCast_rat_pos (Nat.two_pow_pos (p + 1))
    have hcast2 : ((2 ^ (p + 1) - 2 : Nat) : Rat) = ((2 ^ (p + 1) : Nat) : Rat) - 2 := by
      have hadd : (2 ^ (p + 1) - 2) + 2 = 2 ^ (p + 1) := by omega
      have hrat : (((2 ^ (p + 1) - 2) + 2 : Nat) : Rat) = ((2 ^ (p + 1) : Nat) : Rat) := by rw [hadd]
      simp at hrat
      grind
    have hrew : -(((2 ^ (p + 1) - 2 : Nat) : Rat) / (2 ^ (p + 1) : Rat)) =
        -1 + 2 / ((2 ^ (p + 1) : Nat) : Rat) := by
      have hne : ((2 ^ (p + 1) : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hp1_pos
      have h2 : (2 ^ (p + 1) : Rat) = ((2 ^ (p + 1) : Nat) : Rat) := by simp
      rw [hcast2, h2]
      have h1 : (((2 ^ (p + 1) : Nat) : Rat) - 2) / ((2 ^ (p + 1) : Nat) : Rat) +
          2 / ((2 ^ (p + 1) : Nat) : Rat) = 1 := by
        rw [rat_add_div_same hne, rat_div_eq_iff hne]
        grind
      grind
    rw [hrew] at hhi
    have hle : 2 / ((2 ^ (p + 1) : Nat) : Rat) ≤ 1 / ((2 ^ (p + 1) : Nat) : Rat) := by
      have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hhi
      grind
    have hmul := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hp1_pos)
    rw [rat_div_mul_cancel (Rat.ne_of_gt hp1_pos), rat_div_mul_cancel (Rat.ne_of_gt hp1_pos)] at hmul
    exact Rat.not_le.mpr (by decide : (1 : Rat) < 2) hmul

theorem binadeRneNat_tustin_uncond_snap {p k q : Nat} (hk : p + 2 ≤ k) (hq : 1 ≤ q) :
    binadeRneNat p k (q * binadeUlp p k + 2) = q * binadeUlp p k ∧
    binadeRneNat p k (q * binadeUlp p k - 2) = q * binadeUlp p k := by
  unfold binadeRneNat binadeUlp
  have hlt : ¬ (k < p) := by omega
  simp only [hlt, ↓reduceIte]
  have hhalf_ge4 : 4 ≤ 2 ^ (k - p) := by
    have : 2 ^ 2 ≤ 2 ^ (k - p) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hu_eq : 2 ^ (k + 1 - p) = 2 * 2 ^ (k - p) := by
    have : k + 1 - p = (k - p) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm]
  have hu_ge8 : 8 ≤ 2 ^ (k + 1 - p) := by omega
  have hu_pos : 0 < 2 ^ (k + 1 - p) := by omega
  constructor
  · have hdiv : (q * 2 ^ (k + 1 - p) + 2) / 2 ^ (k + 1 - p) = q := by
      rw [Nat.mul_comm q, Nat.mul_add_div hu_pos]
      have : 2 / 2 ^ (k + 1 - p) = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hmod : (q * 2 ^ (k + 1 - p) + 2) % 2 ^ (k + 1 - p) = 2 := by
      rw [Nat.mul_comm q, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hdiv, hmod]
    have h2lt : 2 < 2 ^ (k - p) := by omega
    simp [h2lt]
  · have hsub : q * 2 ^ (k + 1 - p) - 2 = (q - 1) * 2 ^ (k + 1 - p) + (2 ^ (k + 1 - p) - 2) := by
      have hq1 : q * 2 ^ (k + 1 - p) = (q - 1) * 2 ^ (k + 1 - p) + 2 ^ (k + 1 - p) := by
        cases q with
        | zero => omega
        | succ m =>
          simp only [Nat.add_sub_cancel, Nat.succ_mul]
      omega
    rw [hsub]
    have hdiv : ((q - 1) * 2 ^ (k + 1 - p) + (2 ^ (k + 1 - p) - 2)) / 2 ^ (k + 1 - p) = q - 1 := by
      rw [Nat.mul_comm (q - 1), Nat.mul_add_div hu_pos]
      have : (2 ^ (k + 1 - p) - 2) / 2 ^ (k + 1 - p) = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hmod : ((q - 1) * 2 ^ (k + 1 - p) + (2 ^ (k + 1 - p) - 2)) % 2 ^ (k + 1 - p) =
        2 ^ (k + 1 - p) - 2 := by
      rw [Nat.mul_comm (q - 1), Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hdiv, hmod]
    have hnotlt : ¬ (2 ^ (k + 1 - p) - 2 < 2 ^ (k - p)) := by omega
    have hgt : 2 ^ (k + 1 - p) - 2 > 2 ^ (k - p) := by omega
    simp only [hnotlt, hgt, ↓reduceIte]
    have : q - 1 + 1 = q := by omega
    rw [this]

/-- Headline Theorem 1 (`tustin_nyquist_snap_to_minus_one_horizon_exact`). -/
theorem tustin_nyquist_snap_to_minus_one_horizon_exact :
    (∀ z : Rat, (0 : Rat) < z →
      tustinA z = -1 + 4 / (z + 2) ∧ (-1 : Rat) < tustinA z ∧ tustinA z < 1) ∧
    (∀ (p : Nat) (z : Rat), (0 : Rat) < z →
      (rneSnapsToNegOne p (tustinA z) ↔ 4 / (z + 2) ≤ invPow2Rat (p + 1)) ∧
      (4 / (z + 2) ≤ invPow2Rat (p + 1) ↔ (tustinSingleRoundOscThreshold p : Rat) ≤ z)) ∧
    (tustinOscHorizon 3 = 24 ∧ tustinOscHorizon 4 = 40 ∧
     tustinOscHorizon 8 = 520 ∧ tustinOscHorizon 11 = 4104) ∧
    (∀ p : Nat, 2 ≤ p →
      binadeUlp p (p + 1) = 4 ∧
      binadeRneNat p (p + 1) (tustinOscHorizon p + 2) = tustinOscHorizon p ∧
      binadeRneNat p (p + 1) (tustinOscHorizon p - 2) = tustinOscHorizon p ∧
      binadeRneNat p (p + 1) (2 ^ (p + 1) + 4 + 2) = 2 ^ (p + 1) + 8 ∧
      binadeRneNat p (p + 1) (2 ^ (p + 1) + 4 - 2) = 2 ^ (p + 1) ∧
      ¬ rneSnapsToNegOne p (-((2 ^ (p + 1) : Rat) / ((2 ^ (p + 1) + 8 : Nat) : Rat))) ∧
      ¬ rneSnapsToNegOne p (-(((2 ^ (p + 1) - 2 : Nat) : Rat) / (2 ^ (p + 1) : Rat)))) ∧
    (∀ p k q : Nat, p + 2 ≤ k → 1 ≤ q →
      binadeRneNat p k (q * binadeUlp p k + 2) = q * binadeUlp p k ∧
      binadeRneNat p k (q * binadeUlp p k - 2) = q * binadeUlp p k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨tustinA_eq_neg_one_add hz, (tustinA_bounds hz).1, (tustinA_bounds hz).2⟩
  · intro p z hz
    exact tustin_single_round_iff p hz
  · decide
  · intro p hp
    have h1 := binadeRneNat_tustinOscHorizon hp
    have h2 := binadeRneNat_below_tustinOscHorizon hp
    exact ⟨h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2⟩
  · intro p k q hk hq
    exact binadeRneNat_tustin_uncond_snap hk hq

end SsmTustinPade
