/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KroneckerCyclicFrustration.RatOrder

/-!
# Sum-of-2-Kronecker Spectral Distortion Law & K-FAC Cross-Scale Suboptimality

Proves Headline Theorem 1 (`sum_of_two_kronecker_optimal_cond_exact`) and
Headline Theorem 6 (`kfac_cross_scale_suboptimality_witness`) in pure `Init` (zero Mathlib).
-/

namespace KroneckerCyclicFrustration

/-- Helper: `1 + a * b > 0` whenever `a > 0` and `b > 0`. -/
theorem one_add_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < 1 + a * b :=
  rat_add_pos (by decide) (rat_mul_pos ha hb)

/-- Universal lower bound for ANY Kronecker preconditioner `(ℓ, r)` on `A_1 ⊗ B_1 + A_2 ⊗ B_2`
    reduced to `diag(1 + α_i β_j)`. -/
theorem sum_of_two_kronecker_lower_bound
    {n m : Nat} (α : Fin n → Rat) (β : Fin m → Rat)
    (hα : ∀ i, (0 : Rat) < α i) (hβ : ∀ j, (0 : Rat) < β j)
    (i_max i_min : Fin n) (j_max j_min : Fin m)
    (ℓ : Fin n → Rat) (r : Fin m → Rat)
    (hℓ : ∀ i, (0 : Rat) < ℓ i) (hr : ∀ j, (0 : Rat) < r j)
    (lam_min lam_max : Rat) (hlam_min : (0 : Rat) < lam_min)
    (hbound : ∀ i j,
      lam_min ≤ (1 + α i * β j) / (ℓ i * r j) ∧
      (1 + α i * β j) / (ℓ i * r j) ≤ lam_max) :
    cornerOptKappaSq (α i_max) (α i_min) (β j_max) (β j_min) ≤
      (lam_max / lam_min) * (lam_max / lam_min) := by
  have h11_hi := (hbound i_max j_max).2
  have h00_hi := (hbound i_min j_min).2
  have h10_lo := (hbound i_max j_min).1
  have h01_lo := (hbound i_min j_max).1
  have h11_pos : (0 : Rat) < (1 + α i_max * β j_max) / (ℓ i_max * r j_max) :=
    rat_div_pos (one_add_mul_pos (hα i_max) (hβ j_max)) (rat_mul_pos (hℓ i_max) (hr j_max))
  have h00_pos : (0 : Rat) < (1 + α i_min * β j_min) / (ℓ i_min * r j_min) :=
    rat_div_pos (one_add_mul_pos (hα i_min) (hβ j_min)) (rat_mul_pos (hℓ i_min) (hr j_min))
  have h10_pos : (0 : Rat) < (1 + α i_max * β j_min) / (ℓ i_max * r j_min) :=
    rat_div_pos (one_add_mul_pos (hα i_max) (hβ j_min)) (rat_mul_pos (hℓ i_max) (hr j_min))
  have h01_pos : (0 : Rat) < (1 + α i_min * β j_max) / (ℓ i_min * r j_max) :=
    rat_div_pos (one_add_mul_pos (hα i_min) (hβ j_max)) (rat_mul_pos (hℓ i_min) (hr j_max))
  have hlam_max_nonneg : (0 : Rat) ≤ lam_max := Rat.le_trans (Rat.le_of_lt h11_pos) h11_hi
  -- Numerator product ≤ lam_max^2
  have hnum : ((1 + α i_max * β j_max) / (ℓ i_max * r j_max)) *
      ((1 + α i_min * β j_min) / (ℓ i_min * r j_min)) ≤ lam_max * lam_max :=
    rat_mul_le_mul h11_hi h00_hi (Rat.le_of_lt h00_pos) hlam_max_nonneg
  -- Denominator product ≥ lam_min^2
  have hden : lam_min * lam_min ≤
      ((1 + α i_max * β j_min) / (ℓ i_max * r j_min)) *
      ((1 + α i_min * β j_max) / (ℓ i_min * r j_max)) :=
    rat_mul_le_mul h10_lo h01_lo (Rat.le_of_lt hlam_min) (Rat.le_of_lt h10_pos)
  -- Cross-multiply to get ratio ≤ (lam_max / lam_min)^2
  have hden_pos : (0 : Rat) <
      ((1 + α i_max * β j_min) / (ℓ i_max * r j_min)) *
      ((1 + α i_min * β j_max) / (ℓ i_min * r j_max)) :=
    rat_mul_pos h10_pos h01_pos
  have hlam_min_sq_pos : (0 : Rat) < lam_min * lam_min := rat_mul_pos hlam_min hlam_min
  have hratio_le :
      (((1 + α i_max * β j_max) / (ℓ i_max * r j_max)) *
       ((1 + α i_min * β j_min) / (ℓ i_min * r j_min))) /
      (((1 + α i_max * β j_min) / (ℓ i_max * r j_min)) *
       ((1 + α i_min * β j_max) / (ℓ i_min * r j_max))) ≤
      (lam_max * lam_max) / (lam_min * lam_min) := by
    apply rat_div_le_div_of_cross hden_pos hlam_min_sq_pos
    exact rat_mul_le_mul hnum hden (Rat.le_of_lt hlam_min_sq_pos)
      (Rat.mul_nonneg hlam_max_nonneg hlam_max_nonneg)
  -- Cancel all `ℓ` and `r` factors identically
  have hcancel :
      (((1 + α i_max * β j_max) / (ℓ i_max * r j_max)) *
       ((1 + α i_min * β j_min) / (ℓ i_min * r j_min))) /
      (((1 + α i_max * β j_min) / (ℓ i_max * r j_min)) *
       ((1 + α i_min * β j_max) / (ℓ i_min * r j_max))) =
      cornerOptKappaSq (α i_max) (α i_min) (β j_max) (β j_min) := by
    unfold cornerOptKappaSq
    have hlr11 : ℓ i_max * r j_max ≠ 0 := Rat.ne_of_gt (rat_mul_pos (hℓ i_max) (hr j_max))
    have hlr00 : ℓ i_min * r j_min ≠ 0 := Rat.ne_of_gt (rat_mul_pos (hℓ i_min) (hr j_min))
    have hlr10 : ℓ i_max * r j_min ≠ 0 := Rat.ne_of_gt (rat_mul_pos (hℓ i_max) (hr j_min))
    have hlr01 : ℓ i_min * r j_max ≠ 0 := Rat.ne_of_gt (rat_mul_pos (hℓ i_min) (hr j_max))
    rw [rat_div_mul_div hlr11 hlr00, rat_div_mul_div hlr10 hlr01]
    have hden_ne : (1 + α i_max * β j_min) * (1 + α i_min * β j_max) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos (one_add_mul_pos (hα i_max) (hβ j_min)) (one_add_mul_pos (hα i_min) (hβ j_max)))
    have hprod1 : (ℓ i_max * r j_max) * (ℓ i_min * r j_min) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (hℓ i_max) (hr j_max)) (rat_mul_pos (hℓ i_min) (hr j_min)))
    have hprod2 : (ℓ i_max * r j_min) * (ℓ i_min * r j_max) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (hℓ i_max) (hr j_min)) (rat_mul_pos (hℓ i_min) (hr j_max)))
    rw [rat_div_div_eq hprod1 hden_ne hprod2]
    apply rat_div_eq_of_cross
    · intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact hprod1 h
      | inr h => exact hden_ne h
    · exact hden_ne
    · grind
  have hsq : (lam_max * lam_max) / (lam_min * lam_min) = (lam_max / lam_min) * (lam_max / lam_min) :=
    (rat_div_mul_div (Rat.ne_of_gt hlam_min) (Rat.ne_of_gt hlam_min)).symm
  rw [← hcancel, ← hsq]
  exact hratio_le

/-- Four exact polynomial identities for the Corner-Geometric-Mean Preconditioner. -/
theorem corner_four_polynomial_identities (α α_max α_min β β_max β_min : Rat) :
    (1 + α * β_max) * (1 + α_min * β) - (1 + α * β) * (1 + α_min * β_max) =
      (α - α_min) * (β_max - β) ∧
    (1 + α * β_min) * (1 + α_max * β) - (1 + α * β) * (1 + α_max * β_min) =
      (α_max - α) * (β - β_min) ∧
    (1 + α * β) * (1 + α_max * β_max) - (1 + α * β_max) * (1 + α_max * β) =
      (α_max - α) * (β_max - β) ∧
    (1 + α * β) * (1 + α_min * β_min) - (1 + α * β_min) * (1 + α_min * β) =
      (α - α_min) * (β - β_min) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Universal exact attainment of the Corner-Geometric-Mean Preconditioner across the full
    eigenvalue rectangle `[α_min, α_max] × [β_min, β_max]`. -/
theorem corner_attainment_bounds
    {α_min α_max β_min β_max α β : Rat}
    (hα_min : (0 : Rat) < α_min) (hβ_min : (0 : Rat) < β_min)
    (hα1 : α_min ≤ α) (hα2 : α ≤ α_max)
    (hβ1 : β_min ≤ β) (hβ2 : β ≤ β_max) :
    1 / ((1 + α_max * β_max) * (1 + α_min * β_min)) ≤
      cornerPrecondEigSq α β α_max α_min β_max β_min ∧
    cornerPrecondEigSq α β α_max α_min β_max β_min ≤
      1 / ((1 + α_max * β_min) * (1 + α_min * β_max)) := by
  have hα : (0 : Rat) < α := rat_lt_of_lt_of_le hα_min hα1
  have hα_max : (0 : Rat) < α_max := rat_lt_of_lt_of_le hα hα2
  have hβ : (0 : Rat) < β := rat_lt_of_lt_of_le hβ_min hβ1
  have hβ_max : (0 : Rat) < β_max := rat_lt_of_lt_of_le hβ hβ2
  have h1 : (1 + α * β) * (1 + α_min * β_max) ≤ (1 + α * β_max) * (1 + α_min * β) := by
    apply rat_le_of_sub_nonneg
    rw [(corner_four_polynomial_identities α α_max α_min β β_max β_min).1]
    exact Rat.mul_nonneg (rat_sub_nonneg hα1) (rat_sub_nonneg hβ2)
  have h2 : (1 + α * β) * (1 + α_max * β_min) ≤ (1 + α * β_min) * (1 + α_max * β) := by
    apply rat_le_of_sub_nonneg
    rw [(corner_four_polynomial_identities α α_max α_min β β_max β_min).2.1]
    exact Rat.mul_nonneg (rat_sub_nonneg hα2) (rat_sub_nonneg hβ1)
  have h3 : (1 + α * β_max) * (1 + α_max * β) ≤ (1 + α * β) * (1 + α_max * β_max) := by
    apply rat_le_of_sub_nonneg
    rw [(corner_four_polynomial_identities α α_max α_min β β_max β_min).2.2.1]
    exact Rat.mul_nonneg (rat_sub_nonneg hα2) (rat_sub_nonneg hβ2)
  have h4 : (1 + α * β_min) * (1 + α_min * β) ≤ (1 + α * β) * (1 + α_min * β_min) := by
    apply rat_le_of_sub_nonneg
    rw [(corner_four_polynomial_identities α α_max α_min β β_max β_min).2.2.2]
    exact Rat.mul_nonneg (rat_sub_nonneg hα1) (rat_sub_nonneg hβ1)
  have hden_pos : (0 : Rat) < cornerEllSq α β_max β_min * cornerRSq α_max α_min β := by
    unfold cornerEllSq cornerRSq
    exact rat_mul_pos
      (rat_mul_pos (one_add_mul_pos hα hβ_max) (one_add_mul_pos hα hβ_min))
      (rat_mul_pos (one_add_mul_pos hα_max hβ) (one_add_mul_pos hα_min hβ))
  have hlo_den_pos : (0 : Rat) < (1 + α_max * β_max) * (1 + α_min * β_min) :=
    rat_mul_pos (one_add_mul_pos hα_max hβ_max) (one_add_mul_pos hα_min hβ_min)
  have hhi_den_pos : (0 : Rat) < (1 + α_max * β_min) * (1 + α_min * β_max) :=
    rat_mul_pos (one_add_mul_pos hα_max hβ_min) (one_add_mul_pos hα_min hβ_max)
  constructor
  · unfold cornerPrecondEigSq
    apply rat_div_le_div_of_cross hlo_den_pos hden_pos
    have hmul := rat_mul_le_mul h3 h4
      (Rat.le_of_lt (rat_mul_pos (one_add_mul_pos hα hβ_min) (one_add_mul_pos hα_min hβ)))
      (Rat.le_of_lt (rat_mul_pos (one_add_mul_pos hα hβ) (one_add_mul_pos hα_max hβ_max)))
    have eq1 : 1 * (cornerEllSq α β_max β_min * cornerRSq α_max α_min β) =
        ((1 + α * β_max) * (1 + α_max * β)) * ((1 + α * β_min) * (1 + α_min * β)) := by
      unfold cornerEllSq cornerRSq; grind
    have eq2 : (1 + α * β) * (1 + α * β) * ((1 + α_max * β_max) * (1 + α_min * β_min)) =
        ((1 + α * β) * (1 + α_max * β_max)) * ((1 + α * β) * (1 + α_min * β_min)) := by grind
    rw [eq1, eq2]
    exact hmul
  · unfold cornerPrecondEigSq
    apply rat_div_le_div_of_cross hden_pos hhi_den_pos
    have hmul := rat_mul_le_mul h1 h2
      (Rat.le_of_lt (rat_mul_pos (one_add_mul_pos hα hβ) (one_add_mul_pos hα_max hβ_min)))
      (Rat.le_of_lt (rat_mul_pos (one_add_mul_pos hα hβ_max) (one_add_mul_pos hα_min hβ)))
    have eq1 : (1 + α * β) * (1 + α * β) * ((1 + α_max * β_min) * (1 + α_min * β_max)) =
        ((1 + α * β) * (1 + α_min * β_max)) * ((1 + α * β) * (1 + α_max * β_min)) := by grind
    have eq2 : 1 * (cornerEllSq α β_max β_min * cornerRSq α_max α_min β) =
        ((1 + α * β_max) * (1 + α_min * β)) * ((1 + α * β_min) * (1 + α_max * β)) := by
      unfold cornerEllSq cornerRSq; grind
    rw [eq1, eq2]
    exact hmul

/-- Headline Theorem 1 (`sum_of_two_kronecker_optimal_cond_exact`). -/
theorem sum_of_two_kronecker_optimal_cond_exact :
    (∀ {n m : Nat} (α : Fin n → Rat) (β : Fin m → Rat),
      (∀ i, (0 : Rat) < α i) → (∀ j, (0 : Rat) < β j) →
      ∀ (i_max i_min : Fin n) (j_max j_min : Fin m)
        (ℓ : Fin n → Rat) (r : Fin m → Rat),
      (∀ i, (0 : Rat) < ℓ i) → (∀ j, (0 : Rat) < r j) →
      ∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
      (∀ i j, lam_min ≤ (1 + α i * β j) / (ℓ i * r j) ∧
              (1 + α i * β j) / (ℓ i * r j) ≤ lam_max) →
      cornerOptKappaSq (α i_max) (α i_min) (β j_max) (β j_min) ≤
        (lam_max / lam_min) * (lam_max / lam_min)) ∧
    (∀ α α_max α_min β β_max β_min : Rat,
      (1 + α * β_max) * (1 + α_min * β) - (1 + α * β) * (1 + α_min * β_max) =
        (α - α_min) * (β_max - β) ∧
      (1 + α * β_min) * (1 + α_max * β) - (1 + α * β) * (1 + α_max * β_min) =
        (α_max - α) * (β - β_min) ∧
      (1 + α * β) * (1 + α_max * β_max) - (1 + α * β_max) * (1 + α_max * β) =
        (α_max - α) * (β_max - β) ∧
      (1 + α * β) * (1 + α_min * β_min) - (1 + α * β_min) * (1 + α_min * β) =
        (α - α_min) * (β - β_min)) ∧
    (∀ α_min α_max β_min β_max : Rat,
      (0 : Rat) < α_min → α_min ≤ α_max → (0 : Rat) < β_min → β_min ≤ β_max →
      (∀ α β : Rat, α_min ≤ α → α ≤ α_max → β_min ≤ β → β ≤ β_max →
        1 / ((1 + α_max * β_max) * (1 + α_min * β_min)) ≤
          cornerPrecondEigSq α β α_max α_min β_max β_min ∧
        cornerPrecondEigSq α β α_max α_min β_max β_min ≤
          1 / ((1 + α_max * β_min) * (1 + α_min * β_max))) ∧
      cornerPrecondEigSq α_max β_max α_max α_min β_max β_min =
        1 / ((1 + α_max * β_min) * (1 + α_min * β_max)) ∧
      cornerPrecondEigSq α_min β_min α_max α_min β_max β_min =
        1 / ((1 + α_max * β_min) * (1 + α_min * β_max)) ∧
      cornerPrecondEigSq α_max β_min α_max α_min β_max β_min =
        1 / ((1 + α_max * β_max) * (1 + α_min * β_min)) ∧
      cornerPrecondEigSq α_min β_max α_max α_min β_max β_min =
        1 / ((1 + α_max * β_max) * (1 + α_min * β_min)) ∧
      (1 / ((1 + α_max * β_min) * (1 + α_min * β_max))) /
        (1 / ((1 + α_max * β_max) * (1 + α_min * β_min))) =
        cornerOptKappaSq α_max α_min β_max β_min) := by
  refine ⟨?_, corner_four_polynomial_identities, ?_⟩
  · intro n m α β hα hβ i_max i_min j_max j_min ℓ r hℓ hr lam_min lam_max hlam hbound
    exact sum_of_two_kronecker_lower_bound α β hα hβ i_max i_min j_max j_min ℓ r hℓ hr lam_min lam_max hlam hbound
  · intro α_min α_max β_min β_max hα_min hα_le hβ_min hβ_le
    have hα_max : (0 : Rat) < α_max := rat_lt_of_lt_of_le hα_min hα_le
    have hβ_max : (0 : Rat) < β_max := rat_lt_of_lt_of_le hβ_min hβ_le
    have h11 : (0 : Rat) < 1 + α_max * β_max := one_add_mul_pos hα_max hβ_max
    have h00 : (0 : Rat) < 1 + α_min * β_min := one_add_mul_pos hα_min hβ_min
    have h10 : (0 : Rat) < 1 + α_max * β_min := one_add_mul_pos hα_max hβ_min
    have h01 : (0 : Rat) < 1 + α_min * β_max := one_add_mul_pos hα_min hβ_max
    refine ⟨fun α β h1 h2 h3 h4 => corner_attainment_bounds hα_min hβ_min h1 h2 h3 h4,
            ?_, ?_, ?_, ?_, ?_⟩
    · unfold cornerPrecondEigSq cornerEllSq cornerRSq
      apply rat_div_eq_of_cross
      · exact Rat.ne_of_gt (rat_mul_pos (rat_mul_pos h11 h10) (rat_mul_pos h11 h01))
      · exact Rat.ne_of_gt (rat_mul_pos h10 h01)
      · grind
    · unfold cornerPrecondEigSq cornerEllSq cornerRSq
      apply rat_div_eq_of_cross
      · exact Rat.ne_of_gt (rat_mul_pos (rat_mul_pos h01 h00) (rat_mul_pos h10 h00))
      · exact Rat.ne_of_gt (rat_mul_pos h10 h01)
      · grind
    · unfold cornerPrecondEigSq cornerEllSq cornerRSq
      apply rat_div_eq_of_cross
      · exact Rat.ne_of_gt (rat_mul_pos (rat_mul_pos h11 h10) (rat_mul_pos h10 h00))
      · exact Rat.ne_of_gt (rat_mul_pos h11 h00)
      · grind
    · unfold cornerPrecondEigSq cornerEllSq cornerRSq
      apply rat_div_eq_of_cross
      · exact Rat.ne_of_gt (rat_mul_pos (rat_mul_pos h01 h00) (rat_mul_pos h11 h01))
      · exact Rat.ne_of_gt (rat_mul_pos h11 h00)
      · grind
    · unfold cornerOptKappaSq
      rw [rat_div_div_eq (Rat.ne_of_gt (rat_mul_pos h10 h01)) (by decide) (Rat.ne_of_gt (rat_mul_pos h11 h00))]
      simp only [Rat.one_mul, Rat.mul_one]

/-- Headline Theorem 6 (`kfac_cross_scale_suboptimality_witness`):
    Proves that on the `n = 2` cross-scale sum-of-2-Kronecker family `α = (1/K, K)`, `β = (1/K, K)`,
    the squared K-FAC condition number ratio over Corner-Geometric-Mean is
    `K^2 (K^2 + 3)^2 / (3 K^2 + 1)^2 > K^2 / 9` for ALL `K > 0` (hence arbitrarily large!),
    and gives the explicit exact `Rat` witness at `K = 128` achieving `> 1000x` (`> 1820x`) worse `κ^2`. -/
theorem kfac_cross_scale_suboptimality_witness :
    (∀ K : Rat, (0 : Rat) < K →
      let sumK := K + 1 / K
      let kfacRatio :=
        kfacPrecondEig 2 (1 / K) (1 / K) sumK sumK /
        kfacPrecondEig 2 (1 / K) K sumK sumK
      cornerOptKappaSq K (1 / K) K (1 / K) =
        ((K * K + 1) * (K * K + 1)) / (4 * K * K) ∧
      kfacRatio = ((K * K + 1) * (K * K + 3)) / (2 * (3 * K * K + 1)) ∧
      (kfacRatio * kfacRatio) / cornerOptKappaSq K (1 / K) K (1 / K) =
        (K * K * (K * K + 3) * (K * K + 3)) / ((3 * K * K + 1) * (3 * K * K + 1)) ∧
      (K * K) / 9 < (kfacRatio * kfacRatio) / cornerOptKappaSq K (1 / K) K (1 / K)) ∧
    (∀ C : Rat, ∃ K : Rat, (0 : Rat) < K ∧
      let sumK := K + 1 / K
      let kfacRatio :=
        kfacPrecondEig 2 (1 / K) (1 / K) sumK sumK /
        kfacPrecondEig 2 (1 / K) K sumK sumK
      C * cornerOptKappaSq K (1 / K) K (1 / K) < kfacRatio * kfacRatio) ∧
    (let K : Rat := 128
     let sumK := K + 1 / K
     let kfacRatio :=
       kfacPrecondEig 2 (1 / K) (1 / K) sumK sumK /
       kfacPrecondEig 2 (1 / K) K sumK sumK
     cornerOptKappaSq K (1 / K) K (1 / K) = (268468225 : Rat) / 65536 ∧
     1000 * cornerOptKappaSq K (1 / K) K (1 / K) < kfacRatio * kfacRatio ∧
     1800 * cornerOptKappaSq K (1 / K) K (1 / K) < kfacRatio * kfacRatio) := by
  have hmain : ∀ K : Rat, (0 : Rat) < K →
      let sumK := K + 1 / K
      let kfacRatio :=
        kfacPrecondEig 2 (1 / K) (1 / K) sumK sumK /
        kfacPrecondEig 2 (1 / K) K sumK sumK
      cornerOptKappaSq K (1 / K) K (1 / K) =
        ((K * K + 1) * (K * K + 1)) / (4 * K * K) ∧
      kfacRatio = ((K * K + 1) * (K * K + 3)) / (2 * (3 * K * K + 1)) ∧
      (kfacRatio * kfacRatio) / cornerOptKappaSq K (1 / K) K (1 / K) =
        (K * K * (K * K + 3) * (K * K + 3)) / ((3 * K * K + 1) * (3 * K * K + 1)) ∧
      (K * K) / 9 < (kfacRatio * kfacRatio) / cornerOptKappaSq K (1 / K) K (1 / K) := by
    intro K hK
    have hKne : K ≠ 0 := Rat.ne_of_gt hK
    have hK2 : (0 : Rat) < K * K := rat_mul_pos hK hK
    have hK2_1 : (0 : Rat) < K * K + 1 := rat_add_pos hK2 (by decide)
    have hK2_3 : (0 : Rat) < K * K + 3 := rat_add_pos hK2 (by decide)
    have h3K2_1 : (0 : Rat) < 3 * K * K + 1 :=
      rat_add_pos (rat_mul_pos (rat_mul_pos (by decide) hK) hK) (by decide)
    have hinv : (1 / K) * K = 1 := rat_div_mul_cancel hKne
    have hkinv : K * (1 / K) = 1 := rat_mul_div_cancel hKne
    have hinv_sq : (1 / K) * (1 / K) = 1 / (K * K) := by
      rw [rat_div_mul_div hKne hKne, Rat.one_mul]
    have hopt : cornerOptKappaSq K (1 / K) K (1 / K) =
        ((K * K + 1) * (K * K + 1)) / (4 * K * K) := by
      unfold cornerOptKappaSq
      rw [hkinv, hinv, hinv_sq]
      have h1' : (1 + K * K) * (1 + 1 / (K * K)) = ((K * K + 1) * (K * K + 1)) / (K * K) := by
        rw [← rat_div_one ((1 + K * K) * (1 + 1 / (K * K)))]
        apply rat_div_eq_of_cross (by decide) (Rat.ne_of_gt hK2)
        have hmul : (1 + 1 / (K * K)) * (K * K) = K * K + 1 := by
          rw [Rat.add_mul, Rat.one_mul, rat_div_mul_cancel (Rat.ne_of_gt hK2)]
        calc
          (1 + K * K) * (1 + 1 / (K * K)) * (K * K) = (1 + K * K) * ((1 + 1 / (K * K)) * (K * K)) := by grind
          _ = (1 + K * K) * (K * K + 1) := by rw [hmul]
          _ = ((K * K + 1) * (K * K + 1)) * 1 := by grind
      rw [h1']
      have h4 : (1 + (1 : Rat)) * (1 + (1 : Rat)) = 4 := by grind
      rw [h4]
      apply rat_div_eq_of_cross (by decide) (Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide) hK) hK))
      have hcancel : ((K * K + 1) * (K * K + 1)) / (K * K) * (4 * K * K) =
          (((K * K + 1) * (K * K + 1)) / (K * K) * (K * K)) * 4 := by grind
      rw [hcancel, rat_div_mul_cancel (Rat.ne_of_gt hK2)]
    have hlk0 : kfacLeftFactor 2 (1 / K) (K + 1 / K) = (3 * K * K + 1) / (K * K) := by
      unfold kfacLeftFactor
      have hcast : ((2 : Nat) : Rat) = 2 := by decide
      rw [hcast, ← rat_div_one (2 + (1 / K) * (K + 1 / K))]
      apply rat_div_eq_of_cross (by decide) (Rat.ne_of_gt hK2)
      have hmul : (1 / K) * (K + 1 / K) * (K * K) = K * K + 1 := by
        rw [Rat.mul_add, hinv, hinv_sq, Rat.add_mul, Rat.one_mul, rat_div_mul_cancel (Rat.ne_of_gt hK2)]
      calc
        (2 + (1 / K) * (K + 1 / K)) * (K * K) = 2 * (K * K) + (1 / K) * (K + 1 / K) * (K * K) := by grind
        _ = 2 * (K * K) + (K * K + 1) := by rw [hmul]
        _ = (3 * K * K + 1) * 1 := by grind
    have hrk0 : kfacRightFactor 2 (1 / K) (K + 1 / K) = (3 * K * K + 1) / (K * K) := hlk0
    have hrk1 : kfacRightFactor 2 K (K + 1 / K) = K * K + 3 := by
      unfold kfacRightFactor
      have hcast : ((2 : Nat) : Rat) = 2 := by decide
      rw [hcast, Rat.mul_add, hkinv]
      grind
    have hratio :
        kfacPrecondEig 2 (1 / K) (1 / K) (K + 1 / K) (K + 1 / K) /
        kfacPrecondEig 2 (1 / K) K (K + 1 / K) (K + 1 / K) =
        ((K * K + 1) * (K * K + 3)) / (2 * (3 * K * K + 1)) := by
      unfold kfacPrecondEig
      rw [hlk0, hrk0, hrk1, hinv_sq, hinv]
      have hnum1 : 1 + 1 / (K * K) = (K * K + 1) / (K * K) := by
        rw [← rat_div_one (1 + 1 / (K * K))]
        apply rat_div_eq_of_cross (by decide) (Rat.ne_of_gt hK2)
        rw [Rat.add_mul, Rat.one_mul, rat_div_mul_cancel (Rat.ne_of_gt hK2)]; grind
      have h12 : (1 + (1 : Rat)) = 2 := by grind
      rw [hnum1, h12]
      have hd1_pos : (0 : Rat) < (3 * K * K + 1) / (K * K) * ((3 * K * K + 1) / (K * K)) :=
        rat_mul_pos (rat_div_pos h3K2_1 hK2) (rat_div_pos h3K2_1 hK2)
      have hd2_pos : (0 : Rat) < (3 * K * K + 1) / (K * K) * (K * K + 3) :=
        rat_mul_pos (rat_div_pos h3K2_1 hK2) hK2_3
      rw [rat_div_div_eq (Rat.ne_of_gt hd1_pos) (by decide) (Rat.ne_of_gt hd2_pos)]
      have h2d1_ne : (3 * K * K + 1) / (K * K) * ((3 * K * K + 1) / (K * K)) * 2 ≠ 0 :=
        Rat.ne_of_gt (rat_mul_pos hd1_pos (by decide))
      have h2d_ne : 2 * (3 * K * K + 1) ≠ 0 :=
        Rat.ne_of_gt (rat_mul_pos (by decide) h3K2_1)
      apply rat_div_eq_of_cross h2d1_ne h2d_ne
      have hK4_ne : K * K * (K * K) ≠ 0 := Rat.ne_of_gt (rat_mul_pos hK2 hK2)
      have hL :
          (K * K + 1) / (K * K) * ((3 * K * K + 1) / (K * K) * (K * K + 3)) * (2 * (3 * K * K + 1)) * (K * K * (K * K)) =
          ((K * K + 1) / (K * K) * (K * K)) * ((3 * K * K + 1) / (K * K) * (K * K)) * (K * K + 3) * (2 * (3 * K * K + 1)) := by grind
      have hR :
          (K * K + 1) * (K * K + 3) * ((3 * K * K + 1) / (K * K) * ((3 * K * K + 1) / (K * K)) * 2) * (K * K * (K * K)) =
          (K * K + 1) * (K * K + 3) * 2 * (((3 * K * K + 1) / (K * K) * (K * K)) * ((3 * K * K + 1) / (K * K) * (K * K))) := by grind
      rw [rat_div_mul_cancel (Rat.ne_of_gt hK2), rat_div_mul_cancel (Rat.ne_of_gt hK2)] at hL
      rw [rat_div_mul_cancel (Rat.ne_of_gt hK2)] at hR
      have hmul0 :
          ((K * K + 1) / (K * K) * ((3 * K * K + 1) / (K * K) * (K * K + 3)) * (2 * (3 * K * K + 1)) -
           (K * K + 1) * (K * K + 3) * ((3 * K * K + 1) / (K * K) * ((3 * K * K + 1) / (K * K)) * 2)) * (K * K * (K * K)) = 0 := by
        have hsub : ∀ x y z : Rat, (x - y) * z = x * z - y * z := fun x y z => by grind
        rw [hsub, hL, hR]; grind
      cases Rat.mul_eq_zero.mp hmul0 with
      | inl h => grind
      | inr h => exact False.elim (hK4_ne h)
    have hquot :
        (((K * K + 1) * (K * K + 3)) / (2 * (3 * K * K + 1)) *
         (((K * K + 1) * (K * K + 3)) / (2 * (3 * K * K + 1)))) /
        (((K * K + 1) * (K * K + 1)) / (4 * K * K)) =
        (K * K * (K * K + 3) * (K * K + 3)) / ((3 * K * K + 1) * (3 * K * K + 1)) := by
      have h2d_ne : 2 * (3 * K * K + 1) ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) h3K2_1)
      have hnum_ne : (K * K + 1) * (K * K + 1) ≠ 0 := Rat.ne_of_gt (rat_mul_pos hK2_1 hK2_1)
      have h4K2_ne : 4 * K * K ≠ 0 := Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide) hK) hK)
      rw [rat_div_mul_div h2d_ne h2d_ne]
      rw [rat_div_div_eq (Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide) h3K2_1) (rat_mul_pos (by decide) h3K2_1))) hnum_ne h4K2_ne]
      apply rat_div_eq_of_cross
      · exact Rat.ne_of_gt (rat_mul_pos
          (rat_mul_pos (rat_mul_pos (by decide) h3K2_1) (rat_mul_pos (by decide) h3K2_1))
          (rat_mul_pos hK2_1 hK2_1))
      · exact Rat.ne_of_gt (rat_mul_pos h3K2_1 h3K2_1)
      · grind
    have hgt : (K * K) / 9 <
        (K * K * (K * K + 3) * (K * K + 3)) / ((3 * K * K + 1) * (3 * K * K + 1)) := by
      apply rat_div_lt_div_of_cross (by decide) (rat_mul_pos h3K2_1 h3K2_1)
      apply rat_lt_of_sub_pos
      have hdiff :
          K * K * (K * K + 3) * (K * K + 3) * 9 - K * K * ((3 * K * K + 1) * (3 * K * K + 1)) =
          K * K * (48 * (K * K) + 80) := by grind
      rw [hdiff]
      exact rat_mul_pos hK2 (rat_add_pos (rat_mul_pos (by decide) hK2) (by decide))
    refine ⟨hopt, hratio, ?_, ?_⟩
    · rw [hratio, hopt]; exact hquot
    · rw [hratio, hopt, hquot]; exact hgt
  refine ⟨hmain, ?_, ?_⟩
  · -- Unboundedness: for any `C`, choose `K = 3 * C + 4` if `0 ≤ C` else `K = 1`.
    intro C
    cases Rat.le_total (a := (0 : Rat)) (b := C) with
    | inl hC =>
      have hK : (0 : Rat) < 3 * C + 4 := by
        have eq : 3 * C + 4 = 4 + 3 * C := by grind
        rw [eq]
        exact rat_add_pos_of_pos_of_nonneg (a := (4 : Rat)) (b := 3 * C) (by decide) (Rat.mul_nonneg (by decide) hC)
      refine ⟨3 * C + 4, hK, ?_⟩
      have hm := hmain (3 * C + 4) hK
      have hopt_pos : (0 : Rat) < cornerOptKappaSq (3 * C + 4) (1 / (3 * C + 4)) (3 * C + 4) (1 / (3 * C + 4)) := by
        rw [hm.1]
        have hK2 := rat_mul_pos hK hK
        exact rat_div_pos (rat_mul_pos (rat_add_pos hK2 (by decide)) (rat_add_pos hK2 (by decide)))
          (rat_mul_pos (rat_mul_pos (by decide) hK) hK)
      have hC_lt : C < ((3 * C + 4) * (3 * C + 4)) / 9 := by
        apply rat_lt_of_sub_pos
        have eq : ((3 * C + 4) * (3 * C + 4)) / 9 - C = (9 * C * C + 15 * C + 16) / 9 := by
          rw [← rat_div_one (((3 * C + 4) * (3 * C + 4)) / 9 - C)]
          apply rat_div_eq_of_cross (by decide) (by decide)
          have hsub : ∀ x y z : Rat, (x - y) * z = x * z - y * z := fun x y z => by grind
          rw [hsub, rat_div_mul_cancel (by decide)]; grind
        rw [eq]
        have hnum_pos : (0 : Rat) < 9 * C * C + 15 * C + 16 := by
          have eq2 : 9 * C * C + 15 * C + 16 = (16 + 15 * C) + 9 * C * C := by grind
          rw [eq2]
          exact rat_add_pos_of_pos_of_nonneg
            (rat_add_pos_of_pos_of_nonneg (a := (16 : Rat)) (b := 15 * C) (by decide) (Rat.mul_nonneg (by decide) hC))
            (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hC)
        exact rat_div_pos hnum_pos (by decide)
      have hlt := rat_lt_trans hC_lt hm.2.2.2
      have hmul := rat_mul_lt_mul_of_pos_right hlt hopt_pos
      rw [rat_div_mul_cancel (Rat.ne_of_gt hopt_pos)] at hmul
      exact hmul
    | inr hC =>
      refine ⟨1, by decide, ?_⟩
      have hm := hmain 1 (by decide)
      have hopt_pos : (0 : Rat) < cornerOptKappaSq 1 (1 / 1) 1 (1 / 1) := by
        rw [hm.1]
        have hnum : ((1 : Rat) * 1 + 1) * (1 * 1 + 1) = 4 := by grind
        have hden : (4 : Rat) * 1 * 1 = 4 := by grind
        rw [hnum, hden]
        exact rat_div_pos (by decide) (by decide)
      have hC_lt : C < (1 * 1) / (9 : Rat) := by
        have h11 : (1 : Rat) * 1 = 1 := by grind
        rw [h11]
        exact rat_lt_of_le_of_lt hC (rat_div_pos (by decide) (by decide))
      have hlt := rat_lt_trans hC_lt hm.2.2.2
      have hmul := rat_mul_lt_mul_of_pos_right hlt hopt_pos
      rw [rat_div_mul_cancel (Rat.ne_of_gt hopt_pos)] at hmul
      exact hmul
  · -- Concrete `K = 128` witness (> 1000x, > 1800x)
    have hm := hmain 128 (by decide)
    have hopt_val : cornerOptKappaSq 128 (1 / 128) 128 (1 / 128) = (268468225 : Rat) / 65536 := by
      rw [hm.1]
      apply rat_div_eq_of_cross (by grind) (by decide)
      grind
    have hopt_pos : (0 : Rat) < cornerOptKappaSq 128 (1 / 128) 128 (1 / 128) := by
      rw [hopt_val]
      exact rat_div_pos (by decide) (by decide)
    have h1800_lt : (1800 : Rat) < (128 * 128 : Rat) / 9 := by
      rw [← rat_div_one (1800 : Rat)]
      apply rat_div_lt_div_of_cross (by decide) (by decide)
      have hL : (1800 : Rat) * 9 = 16200 := by grind
      have hR : (128 : Rat) * 128 * 1 = 16384 := by grind
      rw [hL, hR]; decide
    have h1800 : 1800 * cornerOptKappaSq 128 (1 / 128) 128 (1 / 128) <
        (kfacPrecondEig 2 (1 / 128) (1 / 128) (128 + 1 / 128) (128 + 1 / 128) /
         kfacPrecondEig 2 (1 / 128) 128 (128 + 1 / 128) (128 + 1 / 128)) *
        (kfacPrecondEig 2 (1 / 128) (1 / 128) (128 + 1 / 128) (128 + 1 / 128) /
         kfacPrecondEig 2 (1 / 128) 128 (128 + 1 / 128) (128 + 1 / 128)) := by
      have hlt := rat_lt_trans h1800_lt hm.2.2.2
      have hmul := rat_mul_lt_mul_of_pos_right hlt hopt_pos
      rw [rat_div_mul_cancel (Rat.ne_of_gt hopt_pos)] at hmul
      exact hmul
    have h1000 : 1000 * cornerOptKappaSq 128 (1 / 128) 128 (1 / 128) <
        1800 * cornerOptKappaSq 128 (1 / 128) 128 (1 / 128) :=
      rat_mul_lt_mul_of_pos_right (by decide) hopt_pos
    exact ⟨hopt_val, rat_lt_trans h1000 h1800, h1800⟩

end KroneckerCyclicFrustration
