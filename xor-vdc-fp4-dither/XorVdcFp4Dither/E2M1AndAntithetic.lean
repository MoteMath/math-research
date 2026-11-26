/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XorVdcFp4Dither.RatBasic

/-!
# OCP E2M1 Harmonic-Mean Relative SR Variance & Antithetic Variance Halving (Theorems 3 & 4)

Proves:
- **Theorem 3 (`e2m1_harmonic_mean_worst_case_sr_variance`)**:
  Universal harmonic-mean bound `(x - l)(r - x) / x^2 ≤ (r - l)^2 / (4 l r)` for all `0 < l < r`
  and `x ∈ [l, r]`, attained at `x* = 2 l r / (l + r) ∈ [l, r]`, together with exact bounds on
  all 6 positive OCP E2M1 intervals (`1/8` at `2/3`, `1/24` at `6/5, 12/5, 24/5`, `1/48` at `12/7, 24/7`).
- **Theorem 4 (`antithetic_pair_sr_variance_halving`)**:
  Universal non-positive covariance `antiCov p1 p2 ≤ 0`, universal pair variance halving
  `antiPairVar p1 p2 ≤ 1/4` vs independent worst case `indPairVar (1/2) (1/2) = 1/2`, exact
  attainment `antiPairVar (1/4) (1/4) = 1/4`, and exact zero variance (`0`) on every complementary
  pair `p1 + p2 = 1` (including every midpoint `p1 = p2 = 1/2`).
-/

namespace XorVdcFp4Dither

/-! ### 1. Theorem 3: Universal Harmonic-Mean Relative SR Variance Law -/

private theorem rat_mul_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  cases Rat.mul_eq_zero.mp h with
  | inl h1 => exact ha h1
  | inr h2 => exact hb h2

private theorem harmonic_rel_var_diff_sq (l r x : Rat) (hl : l ≠ 0) (hr : r ≠ 0) (hx : x ≠ 0) :
    maxRelSrVar l r - relSrVar l r x =
    (((l + r) * x - 2 * l * r) * ((l + r) * x - 2 * l * r)) / (4 * l * r * (x * x)) := by
  unfold maxRelSrVar relSrVar srVar
  have h4lr : 4 * l * r ≠ 0 := rat_mul_ne_zero (rat_mul_ne_zero (by grind) hl) hr
  have hx2 : x * x ≠ 0 := rat_mul_ne_zero hx hx
  have hden : 4 * l * r * (x * x) ≠ 0 := rat_mul_ne_zero h4lr hx2
  grind

private theorem harmonic_rel_var_at_mean (l r : Rat) (hl : l ≠ 0) (hr : r ≠ 0) (hlr : l + r ≠ 0) :
    relSrVar l r (harmonicMean l r) = maxRelSrVar l r := by
  have h4lr : 4 * l * r ≠ 0 := rat_mul_ne_zero (rat_mul_ne_zero (by grind) hl) hr
  have h2lr : 2 * l * r ≠ 0 := rat_mul_ne_zero (rat_mul_ne_zero (by grind) hl) hr
  have hhm : harmonicMean l r ≠ 0 := by
    unfold harmonicMean
    rw [Rat.div_def]
    exact rat_mul_ne_zero h2lr (fun hinv => by
      have h1 : (l + r) * (l + r)⁻¹ = 1 := Rat.mul_inv_cancel (l + r) hlr
      rw [hinv] at h1; grind)
  have hdiff := harmonic_rel_var_diff_sq l r (harmonicMean l r) hl hr hhm
  have hzero : (l + r) * harmonicMean l r - 2 * l * r = 0 := by
    unfold harmonicMean; grind
  rw [hzero] at hdiff
  have h0 : ((0 : Rat) * 0) / (4 * l * r * (harmonicMean l r * harmonicMean l r)) = 0 := by grind
  rw [h0] at hdiff
  grind

theorem harmonicMean_in_interval {l r : Rat} (hl : (0 : Rat) < l) (hlr : l < r) :
    l ≤ harmonicMean l r ∧ harmonicMean l r ≤ r := by
  have hr : (0 : Rat) < r := Rat.lt_of_le_of_ne
    (Rat.le_trans (Rat.le_of_lt hl) (Rat.le_of_lt hlr))
    (fun h0 => Rat.not_lt.mpr (Rat.le_of_lt hl) (by rw [h0]; exact hlr))
  have hsum_pos : (0 : Rat) < l + r := rat_add_pos hl hr
  have hsum_ne : l + r ≠ 0 := Rat.ne_of_gt hsum_pos
  have hdiff_pos : (0 : Rat) < r - l := rat_sub_pos hlr
  constructor
  · apply rat_le_of_sub_nonneg
    have hsub : harmonicMean l r - l = (l * (r - l)) / (l + r) := by
      unfold harmonicMean; grind
    rw [hsub]
    exact rat_div_nonneg (Rat.mul_nonneg (Rat.le_of_lt hl) (Rat.le_of_lt hdiff_pos)) hsum_pos
  · apply rat_le_of_sub_nonneg
    have hsub : r - harmonicMean l r = (r * (r - l)) / (l + r) := by
      unfold harmonicMean; grind
    rw [hsub]
    exact rat_div_nonneg (Rat.mul_nonneg (Rat.le_of_lt hr) (Rat.le_of_lt hdiff_pos)) hsum_pos

theorem relSrVar_le_maxRelSrVar {l r x : Rat}
    (hl : (0 : Rat) < l) (hlr : l < r) (hlx : l ≤ x) (_hxr : x ≤ r) :
    relSrVar l r x ≤ maxRelSrVar l r := by
  have hr : (0 : Rat) < r := Rat.lt_of_le_of_ne
    (Rat.le_trans (Rat.le_of_lt hl) (Rat.le_of_lt hlr))
    (fun h0 => Rat.not_lt.mpr (Rat.le_of_lt hl) (by rw [h0]; exact hlr))
  have hx : (0 : Rat) < x := Rat.lt_of_le_of_ne
    (Rat.le_trans (Rat.le_of_lt hl) hlx)
    (fun h0 => Rat.not_lt.mpr hlx (by rw [← h0]; exact hl))
  apply rat_le_of_sub_nonneg
  rw [harmonic_rel_var_diff_sq l r x (Rat.ne_of_gt hl) (Rat.ne_of_gt hr) (Rat.ne_of_gt hx)]
  have hden : (0 : Rat) < 4 * l * r * (x * x) :=
    rat_mul_pos (rat_mul_pos (rat_mul_pos (by grind) hl) hr) (rat_mul_pos hx hx)
  exact rat_div_nonneg (rat_sq_nonneg ((l + r) * x - 2 * l * r)) hden

theorem e2m1_harmonic_mean_worst_case_sr_variance :
    (∀ (l r : Rat), (0 : Rat) < l → l < r →
      (l ≤ harmonicMean l r ∧ harmonicMean l r ≤ r) ∧
      (∀ x : Rat, l ≤ x → x ≤ r → relSrVar l r x ≤ maxRelSrVar l r) ∧
      relSrVar l r (harmonicMean l r) = maxRelSrVar l r) ∧
    (harmonicMean (1 / 2) 1 = 2 / 3 ∧ maxRelSrVar (1 / 2) 1 = 1 / 8) ∧
    (harmonicMean 1 (3 / 2) = 6 / 5 ∧ maxRelSrVar 1 (3 / 2) = 1 / 24) ∧
    (harmonicMean (3 / 2) 2 = 12 / 7 ∧ maxRelSrVar (3 / 2) 2 = 1 / 48) ∧
    (harmonicMean 2 3 = 12 / 5 ∧ maxRelSrVar 2 3 = 1 / 24) ∧
    (harmonicMean 3 4 = 24 / 7 ∧ maxRelSrVar 3 4 = 1 / 48) ∧
    (harmonicMean 4 6 = 24 / 5 ∧ maxRelSrVar 4 6 = 1 / 24) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l r hl hlr
    have hr : (0 : Rat) < r := Rat.lt_of_le_of_ne
      (Rat.le_trans (Rat.le_of_lt hl) (Rat.le_of_lt hlr))
      (fun h0 => Rat.not_lt.mpr (Rat.le_of_lt hl) (by rw [h0]; exact hlr))
    have hsum_ne : l + r ≠ 0 := Rat.ne_of_gt (rat_add_pos hl hr)
    refine ⟨harmonicMean_in_interval hl hlr, ?_, ?_⟩
    · intro x hlx hxr
      exact relSrVar_le_maxRelSrVar hl hlr hlx hxr
    · exact harmonic_rel_var_at_mean l r (Rat.ne_of_gt hl) (Rat.ne_of_gt hr) hsum_ne
  · exact ⟨by unfold harmonicMean; grind, by unfold maxRelSrVar; grind⟩
  · exact ⟨by unfold harmonicMean; grind, by unfold maxRelSrVar; grind⟩
  · exact ⟨by unfold harmonicMean; grind, by unfold maxRelSrVar; grind⟩
  · exact ⟨by unfold harmonicMean; grind, by unfold maxRelSrVar; grind⟩
  · exact ⟨by unfold harmonicMean; grind, by unfold maxRelSrVar; grind⟩
  · exact ⟨by unfold harmonicMean; grind, by unfold maxRelSrVar; grind⟩

/-! ### 2. Theorem 4: Universal Antithetic Paired SR Variance Halving -/

theorem antiCov_nonpos {p1 p2 : Rat}
    (hp1_0 : (0 : Rat) ≤ p1) (hp1_1 : p1 ≤ 1)
    (hp2_0 : (0 : Rat) ≤ p2) (hp2_1 : p2 ≤ 1) :
    antiCov p1 p2 ≤ 0 := by
  unfold antiCov minRat
  have h1 : (0 : Rat) ≤ p1 * p2 := Rat.mul_nonneg hp1_0 hp2_0
  have h2 : (0 : Rat) ≤ (1 - p1) * (1 - p2) :=
    Rat.mul_nonneg (rat_sub_nonneg hp1_1) (rat_sub_nonneg hp2_1)
  by_cases hle : p1 * p2 ≤ (1 - p1) * (1 - p2)
  · simp only [hle, ↓reduceIte]
    have := (Rat.add_le_add_right (c := -(p1 * p2))).mpr h1
    grind
  · simp only [hle, ↓reduceIte]
    have := (Rat.add_le_add_right (c := -((1 - p1) * (1 - p2)))).mpr h2
    grind

theorem quad_le_quarter (t : Rat) : t * (1 - t) ≤ (1 : Rat) / 4 := by
  apply rat_le_of_sub_nonneg
  have h : (1 : Rat) / 4 - t * (1 - t) = (t - (1 : Rat) / 2) * (t - (1 : Rat) / 2) := by grind
  rw [h]
  exact rat_sq_nonneg (t - (1 : Rat) / 2)

theorem antiPairVar_eq_piecewise (p1 p2 : Rat) :
    antiPairVar p1 p2 =
      if p1 + p2 ≤ 1 then (p1 + p2) * (1 - (p1 + p2))
      else (2 - (p1 + p2)) * ((p1 + p2) - 1) := by
  unfold antiPairVar antiCov minRat
  have hiff : (p1 * p2 ≤ (1 - p1) * (1 - p2)) ↔ (p1 + p2 ≤ 1) := by
    have hdiff : (1 - p1) * (1 - p2) - p1 * p2 = 1 - (p1 + p2) := by grind
    constructor
    · intro h
      have hnn : (0 : Rat) ≤ 1 - (p1 + p2) := by rw [← hdiff]; exact rat_sub_nonneg h
      exact rat_le_of_sub_nonneg hnn
    · intro h
      apply rat_le_of_sub_nonneg
      rw [hdiff]
      exact rat_sub_nonneg h
  by_cases h : p1 + p2 ≤ 1
  · have h' : p1 * p2 ≤ (1 - p1) * (1 - p2) := hiff.mpr h
    simp only [h, h', ↓reduceIte]
    grind
  · have h' : ¬ (p1 * p2 ≤ (1 - p1) * (1 - p2)) := fun hm => h (hiff.mp hm)
    simp only [h, h', ↓reduceIte]
    grind

theorem antiPairVar_le_quarter (p1 p2 : Rat) : antiPairVar p1 p2 ≤ (1 : Rat) / 4 := by
  rw [antiPairVar_eq_piecewise]
  by_cases h : p1 + p2 ≤ 1
  · simp only [h, ↓reduceIte]
    exact quad_le_quarter (p1 + p2)
  · simp only [h, ↓reduceIte]
    have hrew : (2 - (p1 + p2)) * ((p1 + p2) - 1) = ((p1 + p2) - 1) * (1 - ((p1 + p2) - 1)) := by
      grind
    rw [hrew]
    exact quad_le_quarter ((p1 + p2) - 1)

theorem antiPairVar_zero_of_sum_one {p1 p2 : Rat} (h : p1 + p2 = 1) :
    antiPairVar p1 p2 = 0 := by
  rw [antiPairVar_eq_piecewise, h]
  have hle : (1 : Rat) ≤ 1 := Rat.le_refl
  simp only [hle, ↓reduceIte]
  grind

theorem antithetic_pair_sr_variance_halving :
    (∀ p1 p2 : Rat, (0 : Rat) ≤ p1 → p1 ≤ 1 → (0 : Rat) ≤ p2 → p2 ≤ 1 →
      antiCov p1 p2 ≤ 0 ∧ antiPairVar p1 p2 ≤ 1 / 4 ∧ indPairVar p1 p2 ≤ 1 / 2) ∧
    (antiPairVar (1 / 4) (1 / 4) = 1 / 4 ∧ indPairVar (1 / 2) (1 / 2) = 1 / 2) ∧
    (∀ p1 p2 : Rat, p1 + p2 = 1 → antiPairVar p1 p2 = 0) ∧
    antiPairVar (1 / 2) (1 / 2) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p1 p2 hp1_0 hp1_1 hp2_0 hp2_1
    refine ⟨antiCov_nonpos hp1_0 hp1_1 hp2_0 hp2_1, antiPairVar_le_quarter p1 p2, ?_⟩
    unfold indPairVar
    have h1 := quad_le_quarter p1
    have h2 := quad_le_quarter p2
    have hsum : p1 * (1 - p1) + p2 * (1 - p2) ≤ (1 : Rat) / 4 + (1 : Rat) / 4 := by
      have ha : p1 * (1 - p1) + p2 * (1 - p2) ≤ (1 : Rat) / 4 + p2 * (1 - p2) :=
        (Rat.add_le_add_right (c := p2 * (1 - p2))).mpr h1
      have hb : (1 : Rat) / 4 + p2 * (1 - p2) ≤ (1 : Rat) / 4 + (1 : Rat) / 4 := by
        rw [Rat.add_comm ((1 : Rat) / 4), Rat.add_comm ((1 : Rat) / 4)]
        exact (Rat.add_le_add_right (c := (1 : Rat) / 4)).mpr h2
      exact Rat.le_trans ha hb
    have hq : (1 : Rat) / 4 + (1 : Rat) / 4 = 1 / 2 := by grind
    rw [hq] at hsum
    exact hsum
  · constructor
    · rw [antiPairVar_eq_piecewise]
      have hle : (1 : Rat) / 4 + 1 / 4 ≤ 1 := by grind
      simp only [hle, ↓reduceIte]; grind
    · unfold indPairVar; grind
  · intro p1 p2 hsum
    exact antiPairVar_zero_of_sum_one hsum
  · exact antiPairVar_zero_of_sum_one (by grind)

end XorVdcFp4Dither
