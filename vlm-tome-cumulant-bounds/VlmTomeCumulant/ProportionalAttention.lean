/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VlmTomeCumulant.RatOrder

/-!
# Pillar 1: Unweighted Merge TV Distortion, Proportional-Attention Invariance, and Cumulant-2 Bonus

Proves Theorems 1, 2, and 3 of `VlmTomeCumulantChallenge` purely over `Init`.
-/

namespace VlmTomeCumulant

/-! ### Theorem 1: Unweighted Merge TV Distortion & Exact Ceiling -/

theorem tvUnweighted_eq_orig_sub_unw (s : Nat) (w W : Rat)
    (hs : 1 ≤ s) (hw : 0 < w) (hW : 0 < W) :
    let p' := unwClusterProb w W
    origClusterProb s w W - p' = tvUnweighted s p' := by
  intro p'
  have hs_pos : (0 : Rat) < (s : Rat) := rat_natCast_pos (by omega)
  have hsw_pos : (0 : Rat) < (s : Rat) * w := rat_mul_pos hs_pos hw
  have hden1 : (0 : Rat) < (s : Rat) * w + W := rat_add_pos_of_pos_of_nonneg hsw_pos (Rat.le_of_lt hW)
  have hden2 : (0 : Rat) < w + W := rat_add_pos_of_pos_of_nonneg hw (Rat.le_of_lt hW)
  have hden1_ne : (s : Rat) * w + W ≠ 0 := Rat.ne_of_gt hden1
  have hden2_ne : w + W ≠ 0 := Rat.ne_of_gt hden2
  have hp'_eq : p' = w / (w + W) := rfl
  have h1mp' : 1 - p' = W / (w + W) := by
    rw [hp'_eq]
    symm
    rw [rat_div_eq_iff hden2_ne]
    have hmul : (w / (w + W)) * (w + W) = w := rat_div_mul_cancel hden2_ne
    grind
  have hden3_eq : 1 + ((s : Rat) - 1) * p' = ((s : Rat) * w + W) / (w + W) := by
    rw [hp'_eq]
    symm
    rw [rat_div_eq_iff hden2_ne]
    have hmul : (w / (w + W)) * (w + W) = w := rat_div_mul_cancel hden2_ne
    grind
  have hden3_ne : 1 + ((s : Rat) - 1) * p' ≠ 0 := by
    rw [hden3_eq]
    exact Rat.ne_of_gt (rat_div_pos hden1 hden2)
  unfold origClusterProb tvUnweighted
  rw [hp'_eq, rat_div_div_eq_mul_div hden1_ne hden2_ne]
  rw [← hp'_eq]
  symm
  rw [rat_div_eq_iff hden3_ne]
  symm
  have hnum_lhs : (s : Rat) * w * (w + W) - w * ((s : Rat) * w + W) = ((s : Rat) - 1) * w * W := by
    grind
  rw [hnum_lhs, hden3_eq, h1mp', hp'_eq]
  have hprod_ne : ((s : Rat) * w + W) * (w + W) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hden1_ne h
    | inr h => exact hden2_ne h
  -- Clear denominators by multiplying both sides by (w + W)^2
  have hden2_sq_ne : (w + W) * (w + W) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hden2_ne h
    | inr h => exact hden2_ne h
  have hmul_lhs :
      (((s : Rat) - 1) * w * W / (((s : Rat) * w + W) * (w + W))) *
        (((s : Rat) * w + W) / (w + W)) =
      ((s : Rat) - 1) * w * W / ((w + W) * (w + W)) := by
    symm
    rw [rat_div_eq_iff hden2_sq_ne]
    symm
    have h1 : (((s : Rat) - 1) * w * W / (((s : Rat) * w + W) * (w + W))) *
        (((s : Rat) * w + W) * (w + W)) = ((s : Rat) - 1) * w * W :=
      rat_div_mul_cancel hprod_ne
    have h2 : (((s : Rat) * w + W) / (w + W)) * (w + W) = (s : Rat) * w + W :=
      rat_div_mul_cancel hden2_ne
    calc
      (((s : Rat) - 1) * w * W / (((s : Rat) * w + W) * (w + W))) *
          (((s : Rat) * w + W) / (w + W)) * ((w + W) * (w + W))
        = (((s : Rat) - 1) * w * W / (((s : Rat) * w + W) * (w + W))) *
            ((((s : Rat) * w + W) / (w + W)) * (w + W)) * (w + W) := by grind
      _ = (((s : Rat) - 1) * w * W / (((s : Rat) * w + W) * (w + W))) *
            ((s : Rat) * w + W) * (w + W) := by rw [h2]
      _ = (((s : Rat) - 1) * w * W / (((s : Rat) * w + W) * (w + W))) *
            (((s : Rat) * w + W) * (w + W)) := by grind
      _ = ((s : Rat) - 1) * w * W := h1
  have hmul_rhs :
      ((s : Rat) - 1) * (w / (w + W)) * (W / (w + W)) =
      ((s : Rat) - 1) * w * W / ((w + W) * (w + W)) := by
    symm
    rw [rat_div_eq_iff hden2_sq_ne]
    symm
    have h1 : (w / (w + W)) * (w + W) = w := rat_div_mul_cancel hden2_ne
    have h2 : (W / (w + W)) * (w + W) = W := rat_div_mul_cancel hden2_ne
    calc
      ((s : Rat) - 1) * (w / (w + W)) * (W / (w + W)) * ((w + W) * (w + W))
        = ((s : Rat) - 1) * ((w / (w + W)) * (w + W)) * ((W / (w + W)) * (w + W)) := by grind
      _ = ((s : Rat) - 1) * w * W := by rw [h1, h2]
  rw [hmul_lhs, hmul_rhs]

theorem tvUnweightedRat_sq_gap (r p' : Rat) (hr : 1 ≤ r) (hp0 : 0 ≤ p') :
    tvCeilingOfSqrt r - tvUnweightedRat (r * r) p' =
      (r - 1) * ((r + 1) * p' - 1) * ((r + 1) * p' - 1) /
        ((r + 1) * (1 + (r * r - 1) * p')) := by
  have hr_pos : (0 : Rat) < r := rat_lt_of_lt_of_le (by decide) hr
  have hrp1_pos : (0 : Rat) < r + 1 := rat_add_pos_of_pos_of_nonneg hr_pos (by decide)
  have hrp1_ne : r + 1 ≠ 0 := Rat.ne_of_gt hrp1_pos
  have hr2_ge1 : (1 : Rat) ≤ r * r := by
    have h1 := rat_mul_le_mul_of_nonneg_left hr (Rat.le_of_lt hr_pos)
    have h2 : (1 : Rat) ≤ r * 1 := by grind
    exact Rat.le_trans h2 h1
  have hr2m1_nn : (0 : Rat) ≤ r * r - 1 := rat_sub_nonneg hr2_ge1
  have hden_pos : (0 : Rat) < 1 + (r * r - 1) * p' :=
    rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg hr2m1_nn hp0)
  have hden_ne : 1 + (r * r - 1) * p' ≠ 0 := Rat.ne_of_gt hden_pos
  unfold tvCeilingOfSqrt tvUnweightedRat
  rw [rat_div_div_eq_mul_div hrp1_ne hden_ne]
  have hnum : (r - 1) * (1 + (r * r - 1) * p') - (r * r - 1) * p' * (1 - p') * (r + 1) =
      (r - 1) * ((r + 1) * p' - 1) * ((r + 1) * p' - 1) := by
    grind
  rw [hnum]

theorem tvUnweightedRat_le_ceiling (r p' : Rat) (hr : 1 ≤ r) (hp0 : 0 ≤ p') :
    tvUnweightedRat (r * r) p' ≤ tvCeilingOfSqrt r := by
  apply rat_le_of_sub_nonneg
  rw [tvUnweightedRat_sq_gap r p' hr hp0]
  have hr_pos : (0 : Rat) < r := rat_lt_of_lt_of_le (by decide) hr
  have hrp1_pos : (0 : Rat) < r + 1 := rat_add_pos_of_pos_of_nonneg hr_pos (by decide)
  have hrm1_nn : (0 : Rat) ≤ r - 1 := rat_sub_nonneg hr
  have hr2_ge1 : (1 : Rat) ≤ r * r := by
    have h1 := rat_mul_le_mul_of_nonneg_left hr (Rat.le_of_lt hr_pos)
    have h2 : (1 : Rat) ≤ r * 1 := by grind
    exact Rat.le_trans h2 h1
  have hden_pos : (0 : Rat) < 1 + (r * r - 1) * p' :=
    rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (rat_sub_nonneg hr2_ge1) hp0)
  have hsq_nn : (0 : Rat) ≤ ((r + 1) * p' - 1) * ((r + 1) * p' - 1) := rat_sq_nonneg _
  have hnum_nn : (0 : Rat) ≤ (r - 1) * ((r + 1) * p' - 1) * ((r + 1) * p' - 1) := by
    have : (r - 1) * ((r + 1) * p' - 1) * ((r + 1) * p' - 1) =
        (r - 1) * (((r + 1) * p' - 1) * ((r + 1) * p' - 1)) := by grind
    rw [this]
    exact Rat.mul_nonneg hrm1_nn hsq_nn
  exact rat_div_nonneg hnum_nn (rat_mul_pos hrp1_pos hden_pos)

theorem tvUnweightedRat_attains_ceiling (r : Rat) (hr : 1 ≤ r) :
    tvUnweightedRat (r * r) (1 / (r + 1)) = tvCeilingOfSqrt r := by
  have hr_pos : (0 : Rat) < r := rat_lt_of_lt_of_le (by decide) hr
  have hrp1_pos : (0 : Rat) < r + 1 := rat_add_pos_of_pos_of_nonneg hr_pos (by decide)
  have hrp1_ne : r + 1 ≠ 0 := Rat.ne_of_gt hrp1_pos
  have hp0 : (0 : Rat) ≤ 1 / (r + 1) := rat_div_nonneg (by decide) hrp1_pos
  have hgap := tvUnweightedRat_sq_gap r (1 / (r + 1)) hr hp0
  have hzero : (r + 1) * (1 / (r + 1)) - 1 = 0 := by
    rw [rat_mul_div_cancel hrp1_ne]
    grind
  rw [hzero] at hgap
  have hgap0 : tvCeilingOfSqrt r - tvUnweightedRat (r * r) (1 / (r + 1)) = 0 := by
    rw [hgap]
    have : (r - 1) * 0 * 0 = 0 := by grind
    rw [this]
    simp [Rat.div_def]
  grind

theorem tvUnweightedRat_mono_S {S1 S2 p' : Rat}
    (hS1 : 1 ≤ S1) (hS12 : S1 ≤ S2) (hp0 : 0 ≤ p') (hp1 : p' ≤ 1) :
    tvUnweightedRat S1 p' ≤ tvUnweightedRat S2 p' := by
  have hS2 : (1 : Rat) ≤ S2 := Rat.le_trans hS1 hS12
  have hd1 : (0 : Rat) < 1 + (S1 - 1) * p' :=
    rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (rat_sub_nonneg hS1) hp0)
  have hd2 : (0 : Rat) < 1 + (S2 - 1) * p' :=
    rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (rat_sub_nonneg hS2) hp0)
  apply rat_le_of_sub_nonneg
  unfold tvUnweightedRat
  rw [rat_div_div_eq_mul_div (Rat.ne_of_gt hd2) (Rat.ne_of_gt hd1)]
  have hnum : (S2 - 1) * p' * (1 - p') * (1 + (S1 - 1) * p') -
      (S1 - 1) * p' * (1 - p') * (1 + (S2 - 1) * p') =
      (S2 - S1) * p' * (1 - p') := by
    grind
  rw [hnum]
  have h1mp : (0 : Rat) ≤ 1 - p' := rat_sub_nonneg hp1
  have hdiff : (0 : Rat) ≤ S2 - S1 := rat_sub_nonneg hS12
  have hnum_nn : (0 : Rat) ≤ (S2 - S1) * p' * (1 - p') :=
    Rat.mul_nonneg (Rat.mul_nonneg hdiff hp0) h1mp
  exact rat_div_nonneg hnum_nn (rat_mul_pos hd2 hd1)

theorem tvUnweighted_le_ceiling_of_le_sq (s : Nat) (r p' : Rat)
    (hs : 1 ≤ s) (hr : 0 < r) (hsq : (s : Rat) ≤ r * r) (hp0 : 0 ≤ p') (hp1 : p' ≤ 1) :
    tvUnweighted s p' ≤ tvCeilingOfSqrt r := by
  have hs1 : (1 : Rat) ≤ (s : Rat) := rat_natCast_le hs
  have hr1 : (1 : Rat) ≤ r := by
    cases Rat.le_total (a := (1 : Rat)) (b := r) with
    | inl h => exact h
    | inr h =>
      have hlt : r * r ≤ 1 := by
        have h1 := rat_mul_le_mul_of_nonneg_left h (Rat.le_of_lt hr)
        have h2 : r * 1 ≤ 1 := by grind
        exact Rat.le_trans h1 h2
      have heq : r * r = 1 := Rat.le_antisymm hlt (Rat.le_trans hs1 hsq)
      have hne : r = 1 := by
        have h0 : (1 - r) * (1 + r) = 0 := by grind
        cases Rat.mul_eq_zero.mp h0 with
        | inl h1 => grind
        | inr h2 =>
          have : (0 : Rat) < 1 + r := rat_add_pos_of_pos_of_nonneg (by decide) (Rat.le_of_lt hr)
          exact False.elim (Rat.ne_of_gt this h2)
      rw [hne]; exact Rat.le_refl
  have hmono : tvUnweighted s p' ≤ tvUnweightedRat (r * r) p' :=
    tvUnweightedRat_mono_S hs1 hsq hp0 hp1
  exact Rat.le_trans hmono (tvUnweightedRat_le_ceiling r p' hr1 hp0)

theorem tvUnweighted_ge_ceiling_of_sq_le (s : Nat) (r : Rat)
    (_hs : 1 ≤ s) (hr : 1 ≤ r) (hsq : r * r ≤ (s : Rat)) :
    tvCeilingOfSqrt r ≤ tvUnweighted s (1 / (r + 1)) := by
  have hr_pos : (0 : Rat) < r := rat_lt_of_lt_of_le (by decide) hr
  have hrp1_pos : (0 : Rat) < r + 1 := rat_add_pos_of_pos_of_nonneg hr_pos (by decide)
  have hp0 : (0 : Rat) ≤ 1 / (r + 1) := rat_div_nonneg (by decide) hrp1_pos
  have hp1 : 1 / (r + 1) ≤ (1 : Rat) := by
    apply rat_div_le_of_mul_le hrp1_pos
    have hle : (1 : Rat) ≤ 1 * (r + 1) := by
      have := (Rat.add_le_add_right (c := (1 : Rat))).mpr hr
      grind
    exact hle
  have hr2_ge1 : (1 : Rat) ≤ r * r := by
    have h1 := rat_mul_le_mul_of_nonneg_left hr (Rat.le_of_lt hr_pos)
    have h2 : (1 : Rat) ≤ r * 1 := by grind
    exact Rat.le_trans h2 h1
  rw [← tvUnweightedRat_attains_ceiling r hr]
  exact tvUnweightedRat_mono_S hr2_ge1 hsq hp0 hp1

/-- Headline Theorem 1 (`unweighted_merge_tv_distortion_and_exact_ceiling`). -/
theorem unweighted_merge_tv_distortion_and_exact_ceiling :
    (∀ (s : Nat) (w W : Rat), 1 ≤ s → 0 < w → 0 < W →
      origClusterProb s w W - unwClusterProb w W = tvUnweighted s (unwClusterProb w W)) ∧
    (∀ (s : Nat) (r p' : Rat), 1 ≤ s → 0 < r → r * r = (s : Rat) → 0 ≤ p' → p' ≤ 1 →
      tvCeilingOfSqrt r - tvUnweighted s p' =
        (r - 1) * ((r + 1) * p' - 1) * ((r + 1) * p' - 1) /
          ((r + 1) * (1 + ((s : Rat) - 1) * p')) ∧
      tvUnweighted s p' ≤ tvCeilingOfSqrt r ∧
      tvUnweighted s (1 / (r + 1)) = tvCeilingOfSqrt r) ∧
    (∀ (s : Nat) (r p' : Rat), 1 ≤ s → 0 < r → (s : Rat) ≤ r * r → 0 ≤ p' → p' ≤ 1 →
      tvUnweighted s p' ≤ tvCeilingOfSqrt r) ∧
    (∀ (s : Nat) (r : Rat), 1 ≤ s → 1 ≤ r → r * r ≤ (s : Rat) →
      tvCeilingOfSqrt r ≤ tvUnweighted s (1 / (r + 1))) ∧
    (tvCeilingOfSqrt 2 = 1 / 3 ∧ tvUnweighted 4 (1 / 3) = 1 / 3 ∧
     tvCeilingOfSqrt 3 = 1 / 2 ∧ tvUnweighted 9 (1 / 4) = 1 / 2 ∧
     tvCeilingOfSqrt 4 = 3 / 5 ∧ tvUnweighted 16 (1 / 5) = 3 / 5) ∧
    ((∀ p' : Rat, 0 ≤ p' → p' ≤ 1 → tvUnweighted 2 p' ≤ 17158 / 100000) ∧
     (17157 / 100000 : Rat) ≤ tvUnweighted 2 (100000 / 241421) ∧
     (∀ p' : Rat, 0 ≤ p' → p' ≤ 1 → tvUnweighted 8 p' ≤ 47760 / 100000) ∧
     (47759 / 100000 : Rat) ≤ tvUnweighted 8 (100000 / 382842) ∧
     (∀ p' : Rat, 0 ≤ p' → p' ≤ 1 → tvUnweighted 32 p' ≤ 69956 / 100000) ∧
     (69955 / 100000 : Rat) ≤ tvUnweighted 32 (100000 / 665685)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s w W hs hw hW
    exact tvUnweighted_eq_orig_sub_unw s w W hs hw hW
  · intro s r p' hs hr hsq hp0 hp1
    have hs1 : (1 : Rat) ≤ (s : Rat) := rat_natCast_le hs
    have hr1 : (1 : Rat) ≤ r := by
      cases Rat.le_total (a := (1 : Rat)) (b := r) with
      | inl h => exact h
      | inr h =>
        have hlt : r * r ≤ 1 := by
          have h1 := rat_mul_le_mul_of_nonneg_left h (Rat.le_of_lt hr)
          have h2 : r * 1 ≤ 1 := by grind
          exact Rat.le_trans h1 h2
        have heq : r * r = 1 := Rat.le_antisymm hlt (by rw [hsq]; exact hs1)
        have h0 : (1 - r) * (1 + r) = 0 := by grind
        cases Rat.mul_eq_zero.mp h0 with
        | inl h1 =>
          have hr1' : r = 1 := by grind
          rw [hr1']; exact Rat.le_refl
        | inr h2 =>
          have : (0 : Rat) < 1 + r := rat_add_pos_of_pos_of_nonneg (by decide) (Rat.le_of_lt hr)
          exact False.elim (Rat.ne_of_gt this h2)
    have hgap := tvUnweightedRat_sq_gap r p' hr1 hp0
    have hle := tvUnweightedRat_le_ceiling r p' hr1 hp0
    have hatt := tvUnweightedRat_attains_ceiling r hr1
    unfold tvUnweighted
    unfold tvUnweightedRat at hgap hle hatt
    rw [hsq] at hgap hle hatt
    exact ⟨hgap, hle, hatt⟩
  · exact tvUnweighted_le_ceiling_of_le_sq
  · exact tvUnweighted_ge_ceiling_of_sq_le
  · refine ⟨by unfold tvCeilingOfSqrt; grind, by unfold tvUnweighted; grind,
            by unfold tvCeilingOfSqrt; grind, by unfold tvUnweighted; grind,
            by unfold tvCeilingOfSqrt; grind, by unfold tvUnweighted; grind⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p' hp0 hp1
      have hsq : ((2 : Nat) : Rat) ≤ (141422 / 100000 : Rat) * (141422 / 100000) := by
        have h : (141422 / 100000 : Rat) * (141422 / 100000) = ((141422 * 141422 : Nat) : Rat) / ((100000 * 100000 : Nat) : Rat) := by grind
        rw [h]
        have h2 : ((2 : Nat) : Rat) = ((2 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h2]; exact rat_div_le_div_of_nat (by omega) (by omega) (by omega)
      have h1 := tvUnweighted_le_ceiling_of_le_sq 2 (141422 / 100000) p'
        (by omega) (rat_div_pos (by decide) (by decide)) hsq hp0 hp1
      have h2 : tvCeilingOfSqrt (141422 / 100000) = ((41422 : Nat) : Rat) / ((241422 : Nat) : Rat) := by
        unfold tvCeilingOfSqrt; grind
      rw [h2] at h1
      exact Rat.le_trans h1 (rat_div_le_div_of_nat (a := 41422) (b := 241422) (c := 17158) (d := 100000) (by omega) (by omega) (by omega))
    · have hr1 : (1 : Rat) ≤ 141421 / 100000 := by
        have h : (1 : Rat) = ((1 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h]; exact rat_div_le_div_of_nat (a := 1) (b := 1) (c := 141421) (d := 100000) (by omega) (by omega) (by omega)
      have hsq : (141421 / 100000 : Rat) * (141421 / 100000) ≤ ((2 : Nat) : Rat) := by
        have h : (141421 / 100000 : Rat) * (141421 / 100000) = ((141421 * 141421 : Nat) : Rat) / ((100000 * 100000 : Nat) : Rat) := by grind
        have h2 : ((2 : Nat) : Rat) = ((2 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h, h2]; exact rat_div_le_div_of_nat (by omega) (by omega) (by omega)
      have h1 := tvUnweighted_ge_ceiling_of_sq_le 2 (141421 / 100000) (by omega) hr1 hsq
      have h2 : tvCeilingOfSqrt (141421 / 100000) = ((41421 : Nat) : Rat) / ((241421 : Nat) : Rat) := by
        unfold tvCeilingOfSqrt; grind
      have h3 : (1 : Rat) / (141421 / 100000 + 1) = 100000 / 241421 := by grind
      rw [h2, h3] at h1
      exact Rat.le_trans (rat_div_le_div_of_nat (a := 17157) (b := 100000) (c := 41421) (d := 241421) (by omega) (by omega) (by omega)) h1
    · intro p' hp0 hp1
      have hsq : ((8 : Nat) : Rat) ≤ (282843 / 100000 : Rat) * (282843 / 100000) := by
        have h : (282843 / 100000 : Rat) * (282843 / 100000) = ((282843 * 282843 : Nat) : Rat) / ((100000 * 100000 : Nat) : Rat) := by grind
        have h8 : ((8 : Nat) : Rat) = ((8 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h, h8]; exact rat_div_le_div_of_nat (by omega) (by omega) (by omega)
      have h1 := tvUnweighted_le_ceiling_of_le_sq 8 (282843 / 100000) p'
        (by omega) (rat_div_pos (by decide) (by decide)) hsq hp0 hp1
      have h2 : tvCeilingOfSqrt (282843 / 100000) = ((182843 : Nat) : Rat) / ((382843 : Nat) : Rat) := by
        unfold tvCeilingOfSqrt; grind
      rw [h2] at h1
      exact Rat.le_trans h1 (rat_div_le_div_of_nat (a := 182843) (b := 382843) (c := 47760) (d := 100000) (by omega) (by omega) (by omega))
    · have hr1 : (1 : Rat) ≤ 282842 / 100000 := by
        have h : (1 : Rat) = ((1 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h]; exact rat_div_le_div_of_nat (a := 1) (b := 1) (c := 282842) (d := 100000) (by omega) (by omega) (by omega)
      have hsq : (282842 / 100000 : Rat) * (282842 / 100000) ≤ ((8 : Nat) : Rat) := by
        have h : (282842 / 100000 : Rat) * (282842 / 100000) = ((282842 * 282842 : Nat) : Rat) / ((100000 * 100000 : Nat) : Rat) := by grind
        have h8 : ((8 : Nat) : Rat) = ((8 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h, h8]; exact rat_div_le_div_of_nat (by omega) (by omega) (by omega)
      have h1 := tvUnweighted_ge_ceiling_of_sq_le 8 (282842 / 100000) (by omega) hr1 hsq
      have h2 : tvCeilingOfSqrt (282842 / 100000) = ((182842 : Nat) : Rat) / ((382842 : Nat) : Rat) := by
        unfold tvCeilingOfSqrt; grind
      have h3 : (1 : Rat) / (282842 / 100000 + 1) = 100000 / 382842 := by grind
      rw [h2, h3] at h1
      exact Rat.le_trans (rat_div_le_div_of_nat (a := 47759) (b := 100000) (c := 182842) (d := 382842) (by omega) (by omega) (by omega)) h1
    · intro p' hp0 hp1
      have hsq : ((32 : Nat) : Rat) ≤ (565686 / 100000 : Rat) * (565686 / 100000) := by
        have h : (565686 / 100000 : Rat) * (565686 / 100000) = ((565686 * 565686 : Nat) : Rat) / ((100000 * 100000 : Nat) : Rat) := by grind
        have h32 : ((32 : Nat) : Rat) = ((32 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h, h32]; exact rat_div_le_div_of_nat (by omega) (by omega) (by omega)
      have h1 := tvUnweighted_le_ceiling_of_le_sq 32 (565686 / 100000) p'
        (by omega) (rat_div_pos (by decide) (by decide)) hsq hp0 hp1
      have h2 : tvCeilingOfSqrt (565686 / 100000) = ((465686 : Nat) : Rat) / ((665686 : Nat) : Rat) := by
        unfold tvCeilingOfSqrt; grind
      rw [h2] at h1
      exact Rat.le_trans h1 (rat_div_le_div_of_nat (a := 465686) (b := 665686) (c := 69956) (d := 100000) (by omega) (by omega) (by omega))
    · have hr1 : (1 : Rat) ≤ 565685 / 100000 := by
        have h : (1 : Rat) = ((1 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h]; exact rat_div_le_div_of_nat (a := 1) (b := 1) (c := 565685) (d := 100000) (by omega) (by omega) (by omega)
      have hsq : (565685 / 100000 : Rat) * (565685 / 100000) ≤ ((32 : Nat) : Rat) := by
        have h : (565685 / 100000 : Rat) * (565685 / 100000) = ((565685 * 565685 : Nat) : Rat) / ((100000 * 100000 : Nat) : Rat) := by grind
        have h32 : ((32 : Nat) : Rat) = ((32 : Nat) : Rat) / ((1 : Nat) : Rat) := by grind
        rw [h, h32]; exact rat_div_le_div_of_nat (by omega) (by omega) (by omega)
      have h1 := tvUnweighted_ge_ceiling_of_sq_le 32 (565685 / 100000) (by omega) hr1 hsq
      have h2 : tvCeilingOfSqrt (565685 / 100000) = ((465685 : Nat) : Rat) / ((665685 : Nat) : Rat) := by
        unfold tvCeilingOfSqrt; grind
      have h3 : (1 : Rat) / (565685 / 100000 + 1) = 100000 / 665685 := by grind
      rw [h2, h3] at h1
      exact Rat.le_trans (rat_div_le_div_of_nat (a := 69955) (b := 100000) (c := 465685) (d := 665685) (by omega) (by omega) (by omega)) h1

/-! ### Theorem 2: Proportional-Attention (`+ln s`) Exact Zero-Dispersion Invariance -/

/-- Headline Theorem 2 (`proportional_attention_zero_dispersion_exact_invariance`). -/
theorem proportional_attention_zero_dispersion_exact_invariance :
    ∀ (s m : Nat) (w : Rat) (vCl : Fin s → Rat) (u vOut : Fin m → Rat),
      1 ≤ s → 0 < w → (∀ i, 0 ≤ u i) →
      propPartition s w u = origPartition s w u ∧
      (∀ i : Fin m, u i / propPartition s w u = u i / origPartition s w u) ∧
      ((s : Rat) * w / propPartition s w u = finSum (fun _ : Fin s => w / origPartition s w u)) ∧
      collapsedTV
        ((s : Rat) * w / propPartition s w u)
        (finSum (fun _ : Fin s => w / origPartition s w u))
        (fun i => u i / propPartition s w u)
        (fun i => u i / origPartition s w u) = 0 ∧
      propAttnOutput s w vCl u vOut = origAttnOutput w vCl u vOut := by
  intro s m w vCl u vOut hs hw hu
  have hpart : propPartition s w u = origPartition s w u := by
    unfold propPartition origPartition
    rw [finSum_const]
  have hcl_prob : (s : Rat) * w / propPartition s w u =
      finSum (fun _ : Fin s => w / origPartition s w u) := by
    rw [hpart, finSum_const]
    simp only [Rat.div_def]
    grind
  have htv : collapsedTV
      ((s : Rat) * w / propPartition s w u)
      (finSum (fun _ : Fin s => w / origPartition s w u))
      (fun i => u i / propPartition s w u)
      (fun i => u i / origPartition s w u) = 0 := by
    unfold collapsedTV
    rw [hcl_prob]
    have h1 : finSum (fun _ : Fin s => w / origPartition s w u) -
        finSum (fun _ : Fin s => w / origPartition s w u) = 0 := by grind
    rw [h1, ratAbs_zero]
    have h2 : finSum (fun i : Fin m => ratAbs (u i / propPartition s w u - u i / origPartition s w u)) = 0 := by
      rw [finSum_congr (g := fun _ => (0 : Rat))]
      · exact finSum_zero m
      · intro i
        rw [hpart]
        have hsub : u i / origPartition s w u - u i / origPartition s w u = 0 := by grind
        rw [hsub, ratAbs_zero]
    rw [h2]
    grind
  have hout : propAttnOutput s w vCl u vOut = origAttnOutput w vCl u vOut := by
    unfold propAttnOutput origAttnOutput meanVal
    rw [hpart, finSum_mul_left]
    have hs_ne : (s : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (by omega))
    have hcancel : ((s : Rat) * w) * (finSum vCl / (s : Rat)) = w * finSum vCl := by
      calc ((s : Rat) * w) * (finSum vCl / (s : Rat))
          = w * ((s : Rat) * (finSum vCl / (s : Rat))) := by grind
        _ = w * finSum vCl := by rw [rat_mul_div_cancel hs_ne]
    rw [hcancel]
  refine ⟨hpart, ?_, hcl_prob, htv, hout⟩
  intro i
  rw [hpart]

/-! ### Theorem 3: Within-Cluster Dispersion Jensen Underweight & Cumulant-2 Bonus -/

theorem finSum_expTaylor2_eq {s : Nat} (η : Fin s → Rat) (hs : 1 ≤ s) (hmean : finSum η = 0) :
    finSum (fun j => expTaylor2 (η j)) / (s : Rat) = 1 + clusterVar η / 2 := by
  have hs_ne : (s : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (by omega))
  unfold expTaylor2 clusterVar
  rw [finSum_add, finSum_add, finSum_const, hmean, finSum_div_right]
  have h1 : ((s : Rat) * 1 + 0 + finSum (fun j => η j * η j) / 2) / (s : Rat) =
      1 + (finSum (fun j => η j * η j) / (s : Rat)) / 2 := by
    rw [rat_div_eq_iff hs_ne]
    have hc : ((finSum (fun j => η j * η j) / (s : Rat)) / 2) * (s : Rat) =
        finSum (fun j => η j * η j) / 2 := by
      have : ((finSum (fun j => η j * η j) / (s : Rat)) / 2) * (s : Rat) =
          ((finSum (fun j => η j * η j) / (s : Rat)) * (s : Rat)) / 2 := by
        simp only [Rat.div_def]; grind
      rw [this, rat_div_mul_cancel hs_ne]
    grind
  exact h1

theorem expTaylor4_sub_linear_pos {x : Rat} (hx : x ≠ 0) :
    (0 : Rat) < x * x / 2 + x * x * x / 6 + x * x * x * x / 24 := by
  have hident : x * x / 2 + x * x * x / 6 + x * x * x * x / 24 =
      (x * x) * ((x + 2) * (x + 2) + 8) / 24 := by
    simp only [Rat.div_def]
    grind
  rw [hident]
  have hsq : (0 : Rat) < x * x := rat_sq_pos_of_ne_zero hx
  have hquad : (0 : Rat) < (x + 2) * (x + 2) + 8 :=
    rat_add_pos_of_nonneg_of_pos (rat_sq_nonneg (x + 2)) (by decide)
  exact rat_div_pos (rat_mul_pos hsq hquad) (by decide)

theorem expTaylor4_sub_linear_nonneg (x : Rat) :
    (0 : Rat) ≤ x * x / 2 + x * x * x / 6 + x * x * x * x / 24 := by
  by_cases hx : x = 0
  · rw [hx]
    have h0 : (0 : Rat) * 0 / 2 + 0 * 0 * 0 / 6 + 0 * 0 * 0 * 0 / 24 = 0 := by grind
    rw [h0]; exact Rat.le_refl
  · exact Rat.le_of_lt (expTaylor4_sub_linear_pos hx)

/-- Headline Theorem 3 (`within_cluster_dispersion_jensen_underweight_and_cumulant2_bonus`). -/
theorem within_cluster_dispersion_jensen_underweight_and_cumulant2_bonus :
    (∀ (s : Nat) (η : Fin s → Rat), 1 ≤ s → finSum η = 0 →
      finSum (fun j => expTaylor2 (η j)) / (s : Rat) = 1 + clusterVar η / 2 ∧
      ((∃ j, η j ≠ 0) →
        (1 : Rat) < finSum (fun j => expTaylor2 (η j)) / (s : Rat) ∧
        (∀ w : Rat, 0 < w → (s : Rat) * w < w * finSum (fun j => expTaylor2 (η j))) ∧
        (1 : Rat) < finSum (fun j => expTaylor4 (η j)) / (s : Rat))) ∧
    (∀ (s : Nat) (η : Fin s → Rat), 1 ≤ s → finSum η = 0 →
      finSum (fun j => expTaylor2 (η j)) - (s : Rat) * cumulant2Factor1 (clusterVar η) = 0) ∧
    (∀ (s : Nat) (η : Fin s → Rat), 1 ≤ s → finSum η = 0 →
      finSum (fun j => expTaylor3 (η j)) / (s : Rat) - cumulant2Factor1 (clusterVar η) =
        clusterMoment3 η / 6 ∧
      finSum (fun j => expTaylor4 (η j)) / (s : Rat) - cumulant2Factor2 (clusterVar η) =
        clusterMoment3 η / 6 + (clusterMoment4 η - 3 * clusterVar η * clusterVar η) / 24) ∧
    (∀ σ : Rat,
      let η4 : Fin 4 → Rat := fun j => if j.val % 2 = 0 then σ else -σ
      finSum η4 = 0 ∧
      clusterVar η4 = σ * σ ∧
      clusterMoment3 η4 = 0 ∧
      finSum (fun j => expTaylor2 (η4 j)) / 4 - cumulant2Factor1 (clusterVar η4) = 0 ∧
      finSum (fun j => expTaylor4 (η4 j)) / 4 - 1 = σ * σ / 2 + σ * σ * σ * σ / 24 ∧
      finSum (fun j => expTaylor4 (η4 j)) / 4 - cumulant2Factor1 (clusterVar η4) =
        σ * σ * σ * σ / 24) ∧
    (let η02 : Fin 4 → Rat := fun j => if j.val % 2 = 0 then 1 / 5 else -(1 / 5)
     (finSum (fun j => expTaylor4 (η02 j)) / 4 - 1) /
       (finSum (fun j => expTaylor4 (η02 j)) / 4 - cumulant2Factor1 (clusterVar η02)) = 301) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s η hs hmean
    have hs_pos : (0 : Rat) < (s : Rat) := rat_natCast_pos (by omega)
    have hs_ne : (s : Rat) ≠ 0 := Rat.ne_of_gt hs_pos
    have h2eq := finSum_expTaylor2_eq η hs hmean
    refine ⟨h2eq, ?_⟩
    intro ⟨j0, hj0⟩
    have hvar_pos : (0 : Rat) < clusterVar η := by
      unfold clusterVar
      apply rat_div_pos _ hs_pos
      exact finSum_pos_of_nonneg_of_exists_pos
        (fun j => rat_sq_nonneg (η j))
        ⟨j0, rat_sq_pos_of_ne_zero hj0⟩
    have h2gt : (1 : Rat) < finSum (fun j => expTaylor2 (η j)) / (s : Rat) := by
      rw [h2eq]
      have hhalf : (0 : Rat) < clusterVar η / 2 := rat_div_pos hvar_pos (by decide)
      have := rat_add_lt_add_of_le_of_lt (Rat.le_refl (a := (1 : Rat))) hhalf
      grind
    have hweight : ∀ w : Rat, 0 < w → (s : Rat) * w < w * finSum (fun j => expTaylor2 (η j)) := by
      intro w hw
      have hsum_gt : (s : Rat) < finSum (fun j => expTaylor2 (η j)) := by
        have hmul := rat_mul_lt_mul_of_pos_right h2gt hs_pos
        rw [rat_div_mul_cancel hs_ne] at hmul
        grind
      have := rat_mul_lt_mul_of_pos_left hsum_gt hw
      grind
    have h4gt : (1 : Rat) < finSum (fun j => expTaylor4 (η j)) / (s : Rat) := by
      apply rat_lt_div_of_mul_lt hs_pos
      have h1 : (1 : Rat) * (s : Rat) = (s : Rat) := by grind
      rw [h1]
      have hsplit : finSum (fun j => expTaylor4 (η j)) =
          (s : Rat) + finSum (fun j => η j * η j / 2 + η j * η j * η j / 6 + η j * η j * η j * η j / 24) := by
        have hcongr : finSum (fun j => expTaylor4 (η j)) =
            finSum (fun j => (1 + η j) + (η j * η j / 2 + η j * η j * η j / 6 + η j * η j * η j * η j / 24)) := by
          apply finSum_congr; intro j; unfold expTaylor4; grind
        rw [hcongr, finSum_add, finSum_add, finSum_const, hmean]
        grind
      rw [hsplit]
      have htail_pos : (0 : Rat) < finSum (fun j => η j * η j / 2 + η j * η j * η j / 6 + η j * η j * η j * η j / 24) :=
        finSum_pos_of_nonneg_of_exists_pos
          (fun j => expTaylor4_sub_linear_nonneg (η j))
          ⟨j0, expTaylor4_sub_linear_pos hj0⟩
      have := rat_add_lt_add_of_le_of_lt (Rat.le_refl (a := (s : Rat))) htail_pos
      grind
    exact ⟨h2gt, hweight, h4gt⟩
  · intro s η hs hmean
    have hs_ne : (s : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (by omega))
    have h2eq := finSum_expTaylor2_eq η hs hmean
    have hmul : finSum (fun j => expTaylor2 (η j)) = (s : Rat) * (1 + clusterVar η / 2) := by
      have := (rat_div_eq_iff hs_ne).mp h2eq
      grind
    unfold cumulant2Factor1
    rw [hmul]
    grind
  · intro s η hs hmean
    have hs_ne : (s : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (by omega))
    have h2eq := finSum_expTaylor2_eq η hs hmean
    have h3 : finSum (fun j => expTaylor3 (η j)) / (s : Rat) - cumulant2Factor1 (clusterVar η) =
        clusterMoment3 η / 6 := by
      have hcongr : finSum (fun j => expTaylor3 (η j)) =
          finSum (fun j => expTaylor2 (η j)) + finSum (fun j => η j * η j * η j / 6) := by
        rw [← finSum_add]
        apply finSum_congr; intro j; unfold expTaylor3 expTaylor2; grind
      rw [hcongr, finSum_div_right]
      unfold cumulant2Factor1 clusterMoment3
      have hdiv_add : (finSum (fun j => expTaylor2 (η j)) + finSum (fun j => η j * η j * η j) / 6) / (s : Rat) =
          finSum (fun j => expTaylor2 (η j)) / (s : Rat) +
          (finSum (fun j => η j * η j * η j) / (s : Rat)) / 6 := by
        simp only [Rat.div_def]; grind
      rw [hdiv_add, h2eq]
      grind
    have h4 : finSum (fun j => expTaylor4 (η j)) / (s : Rat) - cumulant2Factor2 (clusterVar η) =
        clusterMoment3 η / 6 + (clusterMoment4 η - 3 * clusterVar η * clusterVar η) / 24 := by
      have hcongr : finSum (fun j => expTaylor4 (η j)) =
          finSum (fun j => expTaylor2 (η j)) +
          finSum (fun j => η j * η j * η j / 6) +
          finSum (fun j => η j * η j * η j * η j / 24) := by
        rw [← finSum_add, ← finSum_add]
        apply finSum_congr; intro j; unfold expTaylor4 expTaylor2; grind
      rw [hcongr, finSum_div_right, finSum_div_right]
      have hdiv_add : (finSum (fun j => expTaylor2 (η j)) +
          finSum (fun j => η j * η j * η j) / 6 +
          finSum (fun j => η j * η j * η j * η j) / 24) / (s : Rat) =
          finSum (fun j => expTaylor2 (η j)) / (s : Rat) +
          (finSum (fun j => η j * η j * η j) / (s : Rat)) / 6 +
          (finSum (fun j => η j * η j * η j * η j) / (s : Rat)) / 24 := by
        simp only [Rat.div_def]; grind
      rw [hdiv_add, h2eq]
      unfold cumulant2Factor2 expTaylor2 clusterMoment3 clusterMoment4
      simp only [Rat.div_def]
      grind
    exact ⟨h3, h4⟩
  · intro σ
    simp only [finSum, finSumAux, clusterVar, clusterMoment3, expTaylor2, expTaylor4,
      cumulant2Factor1, Rat.div_def]
    refine ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
  · simp only [finSum, finSumAux, clusterVar, expTaylor4, cumulant2Factor1, Rat.div_def]
    grind

end VlmTomeCumulant
