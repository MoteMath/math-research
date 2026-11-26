/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitnetContraction.RatHelpers

/-!
# Theorem 1: Universal Non-Negativity of Nearest-Neighbor Ternary Contraction

Proves for ALL `d : Nat`, ALL `γ : Rat` with `0 ≤ γ`, and ALL `x : Fin d → Rat`:
`∑_i (x_i - ternRound γ (x_i))^2 ≤ ∑_i x_i^2`
(both for non-strict `≥` tie-breaking `ternRound` and strict `>` tie-breaking `ternRoundStrict`).

Also provides exact coordinate-wise contraction gain and sign/scale-symmetry lemmas
used in the proofs of the BitNet `AbsMean`, `AbsMax`, `AbsMax/2`, and `RMS` laws.
-/

namespace BitnetContraction

/-- Coordinate-wise contraction gain identity for `ternRound` (when `0 ≤ γ`):
    `x^2 - (x - ternRound γ x)^2 = if γ / 2 ≤ |x| then 2 * γ * |x| - γ^2 else 0`. -/
theorem ternRound_gain_eq {γ : Rat} (hγ : 0 ≤ γ) (x : Rat) :
    x * x - (x - ternRound γ x) * (x - ternRound γ x) =
      if γ / 2 ≤ x.abs then 2 * γ * x.abs - γ * γ else 0 := by
  have hhalf : 0 ≤ γ / 2 := rat_div_nonneg hγ (by decide : (0 : Rat) < 2)
  unfold ternRound
  by_cases hpos : γ / 2 ≤ x
  · have hx0 : 0 ≤ x := Rat.le_trans hhalf hpos
    have habs : x.abs = x := rat_abs_eq_of_nonneg hx0
    simp only [hpos, habs, ite_true]
    grind
  · simp only [hpos, ite_false]
    by_cases hneg : x ≤ -(γ / 2)
    · have hnhalf : -(γ / 2) ≤ 0 := by
        have h1 := rat_neg_le_neg hhalf
        have hz : -(0 : Rat) = 0 := by grind
        rw [hz] at h1
        exact h1
      have hx0 : x ≤ 0 := Rat.le_trans hneg hnhalf
      have habs : x.abs = -x := rat_abs_eq_neg_of_nonpos hx0
      have hge : γ / 2 ≤ -x := by
        have h1 := rat_neg_le_neg hneg
        have h2 : -(-(γ / 2)) = γ / 2 := by grind
        rw [h2] at h1
        exact h1
      simp only [hneg, habs, hge, ite_true]
      grind
    · simp only [hneg, ite_false]
      have hlt1 : x < γ / 2 := Rat.not_le.mp hpos
      have hlt2 : -(γ / 2) < x := Rat.not_le.mp hneg
      have habs_lt : x.abs < γ / 2 := by
        cases @Rat.le_total 0 x with
        | inl hx0 =>
          rw [rat_abs_eq_of_nonneg hx0]
          exact hlt1
        | inr hx0 =>
          rw [rat_abs_eq_neg_of_nonpos hx0]
          have h1 : -x < -(-(γ / 2)) := by
            rw [Rat.lt_iff_le_and_ne] at hlt2 ⊢
            refine ⟨rat_neg_le_neg hlt2.1, ?_⟩
            intro heq
            exact hlt2.2 (by grind)
          have h2 : -(-(γ / 2)) = γ / 2 := by grind
          rw [h2] at h1
          exact h1
      have hnot : ¬ (γ / 2 ≤ x.abs) := Rat.not_le.mpr habs_lt
      simp only [hnot, ite_false]
      grind

/-- Coordinate-wise contraction gain identity for `ternRoundStrict` (when `0 ≤ γ`):
    `x^2 - (x - ternRoundStrict γ x)^2 = if γ / 2 < |x| then 2 * γ * |x| - γ^2 else 0`. -/
theorem ternRoundStrict_gain_eq {γ : Rat} (hγ : 0 ≤ γ) (x : Rat) :
    x * x - (x - ternRoundStrict γ x) * (x - ternRoundStrict γ x) =
      if γ / 2 < x.abs then 2 * γ * x.abs - γ * γ else 0 := by
  have hhalf : 0 ≤ γ / 2 := rat_div_nonneg hγ (by decide : (0 : Rat) < 2)
  unfold ternRoundStrict
  by_cases hpos : γ / 2 < x
  · have hx0 : 0 ≤ x := Rat.le_trans hhalf (Rat.le_of_lt hpos)
    have habs : x.abs = x := rat_abs_eq_of_nonneg hx0
    simp only [hpos, habs, ite_true]
    grind
  · simp only [hpos, ite_false]
    by_cases hneg : x < -(γ / 2)
    · have hnhalf : -(γ / 2) ≤ 0 := by
        have h1 := rat_neg_le_neg hhalf
        have hz : -(0 : Rat) = 0 := by grind
        rw [hz] at h1
        exact h1
      have hx0 : x ≤ 0 := Rat.le_trans (Rat.le_of_lt hneg) hnhalf
      have habs : x.abs = -x := rat_abs_eq_neg_of_nonpos hx0
      have hgt : γ / 2 < -x := by
        rw [Rat.lt_iff_le_and_ne] at hneg ⊢
        have h1 := rat_neg_le_neg hneg.1
        have h2 : -(-(γ / 2)) = γ / 2 := by grind
        rw [h2] at h1
        refine ⟨h1, ?_⟩
        intro heq
        exact hneg.2 (by grind)
      simp only [hneg, habs, hgt, ite_true]
      grind
    · simp only [hneg, ite_false]
      have hle1 : x ≤ γ / 2 := Rat.not_lt.mp hpos
      have hle2 : -(γ / 2) ≤ x := Rat.not_lt.mp hneg
      have habs_le : x.abs ≤ γ / 2 := by
        cases @Rat.le_total 0 x with
        | inl hx0 =>
          rw [rat_abs_eq_of_nonneg hx0]
          exact hle1
        | inr hx0 =>
          rw [rat_abs_eq_neg_of_nonpos hx0]
          have h1 := rat_neg_le_neg hle2
          have h2 : -(-(γ / 2)) = γ / 2 := by grind
          rw [h2] at h1
          exact h1
      have hnot : ¬ (γ / 2 < x.abs) := Rat.not_lt.mpr habs_le
      simp only [hnot, ite_false]
      grind

/-- Coordinate-wise non-negativity of `ternRound` error reduction. -/
theorem ternRound_coord_le {γ : Rat} (hγ : 0 ≤ γ) (x : Rat) :
    (x - ternRound γ x) * (x - ternRound γ x) ≤ x * x := by
  apply rat_le_of_sub_nonneg
  rw [ternRound_gain_eq hγ x]
  split
  · rename_i hge
    have hdiff : 0 ≤ 2 * x.abs - γ := by
      have h1 := rat_sub_nonneg_of_le hge
      have h2 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 2) h1
      have h3 : 2 * (x.abs - γ / 2) = 2 * x.abs - γ := by grind
      rw [h3] at h2
      exact h2
    have hmul := rat_mul_nonneg hγ hdiff
    have heq : γ * (2 * x.abs - γ) = 2 * γ * x.abs - γ * γ := by grind
    rw [heq] at hmul
    exact hmul
  · exact Rat.le_refl

/-- Coordinate-wise non-negativity of `ternRoundStrict` error reduction. -/
theorem ternRoundStrict_coord_le {γ : Rat} (hγ : 0 ≤ γ) (x : Rat) :
    (x - ternRoundStrict γ x) * (x - ternRoundStrict γ x) ≤ x * x := by
  apply rat_le_of_sub_nonneg
  rw [ternRoundStrict_gain_eq hγ x]
  split
  · rename_i hgt
    have hge : γ / 2 ≤ x.abs := Rat.le_of_lt hgt
    have hdiff : 0 ≤ 2 * x.abs - γ := by
      have h1 := rat_sub_nonneg_of_le hge
      have h2 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 2) h1
      have h3 : 2 * (x.abs - γ / 2) = 2 * x.abs - γ := by grind
      rw [h3] at h2
      exact h2
    have hmul := rat_mul_nonneg hγ hdiff
    have heq : γ * (2 * x.abs - γ) = 2 * γ * x.abs - γ * γ := by grind
    rw [heq] at hmul
    exact hmul
  · exact Rat.le_refl

/-- Total contraction gain `‖x‖_2^2 - ‖x - Q_γ(x)‖_2^2` for `ternRound`. -/
theorem ternErrSq_gain_eq {d : Nat} {γ : Rat} (hγ : 0 ≤ γ) (x : Fin d → Rat) :
    normSq x - ternErrSq γ x =
      sumRat (fun i => if γ / 2 ≤ (x i).abs then 2 * γ * (x i).abs - γ * γ else 0) := by
  unfold normSq ternErrSq
  rw [← sumRat_sub]
  exact sumRat_congr (fun i => ternRound_gain_eq hγ (x i))

/-- Total contraction gain `‖x‖_2^2 - ‖x - Q_γ^{strict}(x)‖_2^2` for `ternRoundStrict`. -/
theorem ternErrSqStrict_gain_eq {d : Nat} {γ : Rat} (hγ : 0 ≤ γ) (x : Fin d → Rat) :
    normSq x - ternErrSqStrict γ x =
      sumRat (fun i => if γ / 2 < (x i).abs then 2 * γ * (x i).abs - γ * γ else 0) := by
  unfold normSq ternErrSqStrict
  rw [← sumRat_sub]
  exact sumRat_congr (fun i => ternRoundStrict_gain_eq hγ (x i))

/-- **Theorem 1 (Universal Non-Negativity of Nearest-Neighbor Ternary Contraction):**
    For ALL `d : Nat`, ALL `γ ≥ 0`, and ALL `x : Fin d → Rat`, nearest-neighbor ternary
    rounding NEVER increases squared error (both `ternRound` and `ternRoundStrict`). -/
theorem ternary_nearest_nonneg_contraction (d : Nat) (γ : Rat) (hγ : 0 ≤ γ) (x : Fin d → Rat) :
    ternErrSq γ x ≤ normSq x ∧ ternErrSqStrict γ x ≤ normSq x :=
  ⟨sumRat_le_sumRat (fun i => ternRound_coord_le hγ (x i)),
   sumRat_le_sumRat (fun i => ternRoundStrict_coord_le hγ (x i))⟩

end BitnetContraction
