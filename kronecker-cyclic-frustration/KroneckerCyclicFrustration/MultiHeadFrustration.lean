/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KroneckerCyclicFrustration.RatOrder

/-!
# Multi-Head Block-Diagonal Hessians, 2-Head Zero Frustration vs K-FAC, & H-Head Karp Cycle Frustration

Proves Headline Theorem 2 (`multihead_two_head_zero_frustration_and_kfac_gap`) and
Headline Theorem 3 (`multihead_cyclic_frustration_karp_cycle_bound`) in pure `Init` (zero Mathlib).
-/

namespace KroneckerCyclicFrustration

/-! ## Theorem 2: 2-Head Zero Frustration & K-FAC Quadratic Penalty -/

/-- Universal 2-head Kronecker lower bound. -/
theorem two_head_kronecker_lower_bound
    {d : Nat} (b1 b2 : Fin d → Rat)
    (hb1 : ∀ j, (0 : Rat) < b1 j) (hb2 : ∀ j, (0 : Rat) < b2 j)
    (j_max j_min : Fin d)
    (ℓ1 ℓ2 : Rat) (r : Fin d → Rat)
    (hℓ1 : (0 : Rat) < ℓ1) (hℓ2 : (0 : Rat) < ℓ2) (hr : ∀ j, (0 : Rat) < r j)
    (lam_min lam_max : Rat) (hlam_min : (0 : Rat) < lam_min)
    (hbound : ∀ j,
      lam_min ≤ b1 j / (ℓ1 * r j) ∧ b1 j / (ℓ1 * r j) ≤ lam_max ∧
      lam_min ≤ b2 j / (ℓ2 * r j) ∧ b2 j / (ℓ2 * r j) ≤ lam_max) :
    twoHeadOptKappaSq (b1 j_max) (b2 j_max) (b1 j_min) (b2 j_min) ≤
      (lam_max / lam_min) * (lam_max / lam_min) := by
  have h1max_hi := (hbound j_max).2.1
  have h2max_lo := (hbound j_max).2.2.1
  have h1min_lo := (hbound j_min).1
  have h2min_hi := (hbound j_min).2.2.2
  have h1max_pos : (0 : Rat) < b1 j_max / (ℓ1 * r j_max) :=
    rat_div_pos (hb1 j_max) (rat_mul_pos hℓ1 (hr j_max))
  have h2max_pos : (0 : Rat) < b2 j_max / (ℓ2 * r j_max) :=
    rat_div_pos (hb2 j_max) (rat_mul_pos hℓ2 (hr j_max))
  have h1min_pos : (0 : Rat) < b1 j_min / (ℓ1 * r j_min) :=
    rat_div_pos (hb1 j_min) (rat_mul_pos hℓ1 (hr j_min))
  have h2min_pos : (0 : Rat) < b2 j_min / (ℓ2 * r j_min) :=
    rat_div_pos (hb2 j_min) (rat_mul_pos hℓ2 (hr j_min))
  have hlam_max_nonneg : (0 : Rat) ≤ lam_max := Rat.le_trans (Rat.le_of_lt h1max_pos) h1max_hi
  have hnum : (b1 j_max / (ℓ1 * r j_max)) * (b2 j_min / (ℓ2 * r j_min)) ≤ lam_max * lam_max :=
    rat_mul_le_mul h1max_hi h2min_hi (Rat.le_of_lt h2min_pos) hlam_max_nonneg
  have hden : lam_min * lam_min ≤ (b2 j_max / (ℓ2 * r j_max)) * (b1 j_min / (ℓ1 * r j_min)) :=
    rat_mul_le_mul h2max_lo h1min_lo (Rat.le_of_lt hlam_min) (Rat.le_of_lt h2max_pos)
  have hratio_le :
      ((b1 j_max / (ℓ1 * r j_max)) * (b2 j_min / (ℓ2 * r j_min))) /
      ((b2 j_max / (ℓ2 * r j_max)) * (b1 j_min / (ℓ1 * r j_min))) ≤
      (lam_max * lam_max) / (lam_min * lam_min) := by
    apply rat_div_le_div_of_cross (rat_mul_pos h2max_pos h1min_pos) (rat_mul_pos hlam_min hlam_min)
    exact rat_mul_le_mul hnum hden (Rat.le_of_lt (rat_mul_pos hlam_min hlam_min))
      (Rat.mul_nonneg hlam_max_nonneg hlam_max_nonneg)
  have hcancel :
      ((b1 j_max / (ℓ1 * r j_max)) * (b2 j_min / (ℓ2 * r j_min))) /
      ((b2 j_max / (ℓ2 * r j_max)) * (b1 j_min / (ℓ1 * r j_min))) =
      twoHeadOptKappaSq (b1 j_max) (b2 j_max) (b1 j_min) (b2 j_min) := by
    unfold twoHeadOptKappaSq
    have hlr1M : ℓ1 * r j_max ≠ 0 := Rat.ne_of_gt (rat_mul_pos hℓ1 (hr j_max))
    have hlr2m : ℓ2 * r j_min ≠ 0 := Rat.ne_of_gt (rat_mul_pos hℓ2 (hr j_min))
    have hlr2M : ℓ2 * r j_max ≠ 0 := Rat.ne_of_gt (rat_mul_pos hℓ2 (hr j_max))
    have hlr1m : ℓ1 * r j_min ≠ 0 := Rat.ne_of_gt (rat_mul_pos hℓ1 (hr j_min))
    rw [rat_div_mul_div hlr1M hlr2m, rat_div_mul_div hlr2M hlr1m]
    have hprod1 : (ℓ1 * r j_max) * (ℓ2 * r j_min) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos (rat_mul_pos hℓ1 (hr j_max)) (rat_mul_pos hℓ2 (hr j_min)))
    have hprod2 : (ℓ2 * r j_max) * (ℓ1 * r j_min) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos (rat_mul_pos hℓ2 (hr j_max)) (rat_mul_pos hℓ1 (hr j_min)))
    have hnum2 : b2 j_max * b1 j_min ≠ 0 := Rat.ne_of_gt (rat_mul_pos (hb2 j_max) (hb1 j_min))
    rw [rat_div_div_eq hprod1 hnum2 hprod2]
    rw [rat_div_div_eq (Rat.ne_of_gt (hb2 j_max)) (Rat.ne_of_gt (hb1 j_min)) (Rat.ne_of_gt (hb2 j_min))]
    apply rat_div_eq_of_cross
    · exact Rat.ne_of_gt (rat_mul_pos
        (rat_mul_pos (rat_mul_pos hℓ1 (hr j_max)) (rat_mul_pos hℓ2 (hr j_min)))
        (rat_mul_pos (hb2 j_max) (hb1 j_min)))
    · exact Rat.ne_of_gt (rat_mul_pos (hb2 j_max) (hb1 j_min))
    · grind
  have hsq : (lam_max * lam_max) / (lam_min * lam_min) = (lam_max / lam_min) * (lam_max / lam_min) :=
    (rat_div_mul_div (Rat.ne_of_gt hlam_min) (Rat.ne_of_gt hlam_min)).symm
  rw [← hcancel, ← hsq]
  exact hratio_le

/-- Headline Theorem 2 (`multihead_two_head_zero_frustration_and_kfac_gap`). -/
theorem multihead_two_head_zero_frustration_and_kfac_gap :
    (∀ {d : Nat} (b1 b2 : Fin d → Rat),
      (∀ j, (0 : Rat) < b1 j) → (∀ j, (0 : Rat) < b2 j) →
      ∀ (j_max j_min : Fin d) (ℓ1 ℓ2 : Rat) (r : Fin d → Rat),
      (0 : Rat) < ℓ1 → (0 : Rat) < ℓ2 → (∀ j, (0 : Rat) < r j) →
      ∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
      (∀ j, lam_min ≤ b1 j / (ℓ1 * r j) ∧ b1 j / (ℓ1 * r j) ≤ lam_max ∧
            lam_min ≤ b2 j / (ℓ2 * r j) ∧ b2 j / (ℓ2 * r j) ≤ lam_max) →
      twoHeadOptKappaSq (b1 j_max) (b2 j_max) (b1 j_min) (b2 j_min) ≤
        (lam_max / lam_min) * (lam_max / lam_min)) ∧
    (∀ {d : Nat} (b1 b2 : Fin d → Rat),
      (∀ j, (0 : Rat) < b1 j) → (∀ j, (0 : Rat) < b2 j) →
      ∀ (j_max j_min : Fin d),
      let M_max := b1 j_max / b2 j_max
      let M_min := b1 j_min / b2 j_min
      (∀ j, M_min ≤ b1 j / b2 j ∧ b1 j / b2 j ≤ M_max) →
      let ℓ1Sq : Rat := 1
      let ℓ2Sq : Rat := 1 / (M_max * M_min)
      let rSq : Fin d → Rat := fun j => b1 j * b2 j
      (∀ j,
        M_min ≤ (b1 j * b1 j) / (ℓ1Sq * rSq j) ∧ (b1 j * b1 j) / (ℓ1Sq * rSq j) ≤ M_max ∧
        M_min ≤ (b2 j * b2 j) / (ℓ2Sq * rSq j) ∧ (b2 j * b2 j) / (ℓ2Sq * rSq j) ≤ M_max) ∧
      (b1 j_max * b1 j_max) / (ℓ1Sq * rSq j_max) = M_max ∧
      (b1 j_min * b1 j_min) / (ℓ1Sq * rSq j_min) = M_min ∧
      M_max / M_min = twoHeadOptKappaSq (b1 j_max) (b2 j_max) (b1 j_min) (b2 j_min)) ∧
    (∀ M : Rat, (1 : Rat) ≤ M →
      twoHeadOptKappaSq M 1 1 1 = M ∧
      (∀ h j : Fin 2, 1 / (1 + M) ≤ twoHeadKfacEig M h j ∧ twoHeadKfacEig M h j ≤ 1 / 2) ∧
      twoHeadKfacEig M ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 / 2 ∧
      twoHeadKfacEig M ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 / (1 + M) ∧
      (1 / 2 : Rat) / (1 / (1 + M)) = (1 + M) / 2 ∧
      (((1 + M) / 2) * ((1 + M) / 2)) / M = ((1 + M) * (1 + M)) / (4 * M)) ∧
    ((((1 + 4 : Rat) * (1 + 4)) / (4 * 4) = 25 / 16) ∧
     (((1 + 16 : Rat) * (1 + 16)) / (4 * 16) = 289 / 64) ∧
     (((1 + 64 : Rat) * (1 + 64)) / (4 * 64) = 4225 / 256) ∧
     (((1 + 256 : Rat) * (1 + 256)) / (4 * 256) = 66049 / 1024) ∧
     (((1 + 1024 : Rat) * (1 + 1024)) / (4 * 1024) = 1050625 / 4096)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d b1 b2 hb1 hb2 j_max j_min ℓ1 ℓ2 r hℓ1 hℓ2 hr lam_min lam_max hlam hbound
    exact two_head_kronecker_lower_bound b1 b2 hb1 hb2 j_max j_min ℓ1 ℓ2 r hℓ1 hℓ2 hr lam_min lam_max hlam hbound
  · intro d b1 b2 hb1 hb2 j_max j_min M_max M_min hrange
    have hMmax_pos : (0 : Rat) < b1 j_max / b2 j_max := rat_div_pos (hb1 j_max) (hb2 j_max)
    have hMmin_pos : (0 : Rat) < b1 j_min / b2 j_min := rat_div_pos (hb1 j_min) (hb2 j_min)
    have hMM_pos : (0 : Rat) < (b1 j_max / b2 j_max) * (b1 j_min / b2 j_min) :=
      rat_mul_pos hMmax_pos hMmin_pos
    have h1_simp : ∀ j : Fin d, (b1 j * b1 j) / (1 * (b1 j * b2 j)) = b1 j / b2 j := by
      intro j
      apply rat_div_eq_of_cross
      · exact Rat.ne_of_gt (rat_mul_pos (by decide) (rat_mul_pos (hb1 j) (hb2 j)))
      · exact Rat.ne_of_gt (hb2 j)
      · grind
    have h2_simp : ∀ j : Fin d,
        (b2 j * b2 j) / (1 / ((b1 j_max / b2 j_max) * (b1 j_min / b2 j_min)) * (b1 j * b2 j)) =
        ((b1 j_max / b2 j_max) * (b1 j_min / b2 j_min)) / (b1 j / b2 j) := by
      intro j
      have hratio_pos : (0 : Rat) < b1 j / b2 j := rat_div_pos (hb1 j) (hb2 j)
      have hden_pos : (0 : Rat) < 1 / ((b1 j_max / b2 j_max) * (b1 j_min / b2 j_min)) * (b1 j * b2 j) :=
        rat_mul_pos (rat_div_pos (by decide) hMM_pos) (rat_mul_pos (hb1 j) (hb2 j))
      apply rat_div_eq_of_cross (Rat.ne_of_gt hden_pos) (Rat.ne_of_gt hratio_pos)
      have hL : b2 j * b2 j * (b1 j / b2 j) = b2 j * b1 j := by
        have eq : b2 j * b2 j * (b1 j / b2 j) = b2 j * ((b1 j / b2 j) * b2 j) := by grind
        rw [eq, rat_div_mul_cancel (Rat.ne_of_gt (hb2 j))]
      have hR : (b1 j_max / b2 j_max) * (b1 j_min / b2 j_min) *
          (1 / ((b1 j_max / b2 j_max) * (b1 j_min / b2 j_min)) * (b1 j * b2 j)) =
          b1 j * b2 j := by
        have eq : (b1 j_max / b2 j_max) * (b1 j_min / b2 j_min) *
            (1 / ((b1 j_max / b2 j_max) * (b1 j_min / b2 j_min)) * (b1 j * b2 j)) =
            ((b1 j_max / b2 j_max) * (b1 j_min / b2 j_min) *
             (1 / ((b1 j_max / b2 j_max) * (b1 j_min / b2 j_min)))) * (b1 j * b2 j) := by grind
        rw [eq, rat_mul_div_cancel (Rat.ne_of_gt hMM_pos), Rat.one_mul]
      rw [hL, hR]; grind
    refine ⟨?_, h1_simp j_max, h1_simp j_min, rfl⟩
    intro j
    rw [h1_simp j, h2_simp j]
    have hj := hrange j
    have hratio_pos : (0 : Rat) < b1 j / b2 j := rat_div_pos (hb1 j) (hb2 j)
    refine ⟨hj.1, hj.2, ?_, ?_⟩
    · apply rat_le_div_of_mul_le hratio_pos
      have := rat_mul_le_mul_of_nonneg_left hj.2 (Rat.le_of_lt hMmin_pos)
      grind
    · apply rat_div_le_of_mul_le hratio_pos
      have := rat_mul_le_mul_of_nonneg_left hj.1 (Rat.le_of_lt hMmax_pos)
      grind
  · intro M hM
    have hM_pos : (0 : Rat) < M := rat_lt_of_lt_of_le (by decide) hM
    have h1M_pos : (0 : Rat) < 1 + M := rat_add_pos (by decide) hM_pos
    have hopt : twoHeadOptKappaSq M 1 1 1 = M := by
      unfold twoHeadOptKappaSq
      rw [rat_div_one, rat_div_one, rat_div_one]
    have h00 : twoHeadKfacEig M ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 / (1 + M) := by
      simp [twoHeadKfacEig, Rat.mul_one]
    have h10 : twoHeadKfacEig M ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 / 2 := by
      simp [twoHeadKfacEig, Rat.mul_one]
    have h11 : twoHeadKfacEig M ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 / (1 + M) := by
      simp only [twoHeadKfacEig]
      have h2mul : (2 : Rat) * ((1 + M) / 2) = 1 + M := rat_mul_div_cancel (by decide)
      simp [h2mul]
    have h01 : twoHeadKfacEig M ⟨0, by decide⟩ ⟨1, by decide⟩ = (2 * M) / ((1 + M) * (1 + M)) := by
      simp only [twoHeadKfacEig, ite_true, ite_false, Nat.one_ne_zero]
      apply rat_div_eq_of_cross
      · exact Rat.ne_of_gt (rat_mul_pos h1M_pos (rat_div_pos h1M_pos (by decide)))
      · exact Rat.ne_of_gt (rat_mul_pos h1M_pos h1M_pos)
      · have hmul : (2 * M) * ((1 + M) * ((1 + M) / 2)) = M * ((1 + M) * (2 * ((1 + M) / 2))) := by grind
        rw [hmul, rat_mul_div_cancel (by decide)]
    have hbound_kfac : ∀ h j : Fin 2, 1 / (1 + M) ≤ twoHeadKfacEig M h j ∧ twoHeadKfacEig M h j ≤ 1 / 2 := by
      intro h j
      match h, j with
      | ⟨0, _⟩, ⟨0, _⟩ =>
        rw [h00]
        refine ⟨Rat.le_refl, ?_⟩
        apply rat_div_le_div_of_cross h1M_pos (by decide)
        have : (1 : Rat) * 2 ≤ 1 * (1 + M) := by
          have := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hM
          grind
        exact this
      | ⟨0, _⟩, ⟨1, _⟩ =>
        rw [h01]
        constructor
        · apply rat_div_le_div_of_cross h1M_pos (rat_mul_pos h1M_pos h1M_pos)
          apply rat_le_of_sub_nonneg
          have eq : 2 * M * (1 + M) - 1 * ((1 + M) * (1 + M)) = (1 + M) * (M - 1) := by grind
          rw [eq]
          exact Rat.mul_nonneg (Rat.le_of_lt h1M_pos) (rat_sub_nonneg hM)
        · apply rat_div_le_div_of_cross (rat_mul_pos h1M_pos h1M_pos) (by decide)
          apply rat_le_of_sub_nonneg
          have eq : 1 * ((1 + M) * (1 + M)) - 2 * M * 2 = (M - 1) * (M - 1) := by grind
          rw [eq]
          exact Rat.mul_nonneg (rat_sub_nonneg hM) (rat_sub_nonneg hM)
      | ⟨1, _⟩, ⟨0, _⟩ =>
        rw [h10]
        refine ⟨?_, Rat.le_refl⟩
        apply rat_div_le_div_of_cross h1M_pos (by decide)
        have := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hM
        grind
      | ⟨1, _⟩, ⟨1, _⟩ =>
        rw [h11]
        refine ⟨Rat.le_refl, ?_⟩
        apply rat_div_le_div_of_cross h1M_pos (by decide)
        have := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hM
        grind
    have hratio_kfac : (1 / 2 : Rat) / (1 / (1 + M)) = (1 + M) / 2 := by
      rw [rat_div_div_eq (by decide) (by decide) (Rat.ne_of_gt h1M_pos)]
      simp only [Rat.one_mul, Rat.mul_one]
    have hpen_ratio : (((1 + M) / 2) * ((1 + M) / 2)) / M = ((1 + M) * (1 + M)) / (4 * M) := by
      rw [rat_div_mul_div (by decide) (by decide)]
      apply rat_div_eq_of_cross (Rat.ne_of_gt hM_pos) (Rat.ne_of_gt (rat_mul_pos (by decide) hM_pos))
      have h4 : (2 : Rat) * 2 = 4 := by grind
      rw [h4]
      have hcancel : ((1 + M) * (1 + M)) / 4 * (4 * M) = (((1 + M) * (1 + M)) / 4 * 4) * M := by grind
      rw [hcancel, rat_div_mul_cancel (by decide)]
    exact ⟨hopt, hbound_kfac, h10, h00, hratio_kfac, hpen_ratio⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply rat_div_eq_of_cross (by grind) (by decide); grind
    · apply rat_div_eq_of_cross (by grind) (by decide); grind
    · apply rat_div_eq_of_cross (by grind) (by decide); grind
    · apply rat_div_eq_of_cross (by grind) (by decide); grind
    · apply rat_div_eq_of_cross (by grind) (by decide); grind

/-! ## Theorem 3: Universal H-Head Karp Cycle Bound & Exact `2(H-1)/H` Separation -/

/-- Exact Kronecker scaling invariance of any directed cycle product `karpCycleProduct`. -/
theorem karp_cycle_kronecker_invariance
    {H d L : Nat} (hL : 0 < L)
    (b : Fin H → Fin d → Rat) (ℓ : Fin H → Rat) (r : Fin d → Rat)
    (hb : ∀ h j, (0 : Rat) < b h j) (hℓ : ∀ h, (0 : Rat) < ℓ h) (hr : ∀ j, (0 : Rat) < r j)
    (head : Fin L → Fin H) (feat : Fin L → Fin d) :
    karpScaledCycleProduct hL b ℓ r head feat = karpCycleProduct hL b head feat := by
  unfold karpScaledCycleProduct karpCycleProduct
  -- First rewrite each factor `t` by cancelling `ℓ (head t)`:
  have hstep : ∀ t : Fin L,
      (b (head t) (feat t) / (ℓ (head t) * r (feat t))) /
      (b (head t) (feat (finNext hL t)) / (ℓ (head t) * r (feat (finNext hL t)))) =
      (b (head t) (feat t) / b (head t) (feat (finNext hL t))) *
      (r (feat (finNext hL t)) / r (feat t)) := by
    intro t
    have hlt : ℓ (head t) ≠ 0 := Rat.ne_of_gt (hℓ (head t))
    have hr1 : r (feat t) ≠ 0 := Rat.ne_of_gt (hr (feat t))
    have hr2 : r (feat (finNext hL t)) ≠ 0 := Rat.ne_of_gt (hr (feat (finNext hL t)))
    have hb2 : b (head t) (feat (finNext hL t)) ≠ 0 := Rat.ne_of_gt (hb (head t) (feat (finNext hL t)))
    have hlr1 : ℓ (head t) * r (feat t) ≠ 0 := Rat.ne_of_gt (rat_mul_pos (hℓ (head t)) (hr (feat t)))
    have hlr2 : ℓ (head t) * r (feat (finNext hL t)) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos (hℓ (head t)) (hr (feat (finNext hL t))))
    rw [rat_div_div_eq hlr1 hb2 hlr2, rat_div_mul_div hb2 hr1]
    apply rat_div_eq_of_cross
    · exact Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (hℓ (head t)) (hr (feat t))) (hb (head t) (feat (finNext hL t))))
    · exact Rat.ne_of_gt (rat_mul_pos (hb (head t) (feat (finNext hL t))) (hr (feat t)))
    · grind
  rw [finProdRat_congr hstep, finProdRat_mul]
  -- Now show `finProdRat (fun t => r (feat (finNext hL t)) / r (feat t)) = 1`:
  rw [finProdRat_div _ _ (fun t => Rat.ne_of_gt (hr (feat t)))]
  have hshift := finProdRat_shift hL (fun t : Fin L => r (feat t))
  rw [hshift]
  have hprod_ne : finProdRat (fun t : Fin L => r (feat t)) ≠ 0 :=
    Rat.ne_of_gt (finProdRat_pos _ (fun t => hr (feat t)))
  have hself : finProdRat (fun t : Fin L => r (feat t)) / finProdRat (fun t : Fin L => r (feat t)) = 1 := by
    rw [Rat.div_def, Rat.mul_inv_cancel _ hprod_ne]
  rw [hself, Rat.mul_one]

/-- Universal Karp cycle lower bound: for ANY Kronecker scaling `(ℓ, r)` with spectral envelope
    `[lam_min, lam_max]`, `karpCycleProduct hL b head feat ≤ (lam_max / lam_min)^L`. -/
theorem karp_cycle_lower_bound
    {H d L : Nat} (hL : 0 < L)
    (b : Fin H → Fin d → Rat) (ℓ : Fin H → Rat) (r : Fin d → Rat)
    (hb : ∀ h j, (0 : Rat) < b h j) (hℓ : ∀ h, (0 : Rat) < ℓ h) (hr : ∀ j, (0 : Rat) < r j)
    (head : Fin L → Fin H) (feat : Fin L → Fin d)
    (lam_min lam_max : Rat) (hlam_min : (0 : Rat) < lam_min)
    (hbound : ∀ h j,
      lam_min ≤ b h j / (ℓ h * r j) ∧ b h j / (ℓ h * r j) ≤ lam_max) :
    karpCycleProduct hL b head feat ≤ ratPow (lam_max / lam_min) L := by
  rw [← karp_cycle_kronecker_invariance hL b ℓ r hb hℓ hr head feat]
  unfold karpScaledCycleProduct
  rw [← finProdRat_const L (lam_max / lam_min)]
  apply finProdRat_le_finProdRat
  · intro t
    exact Rat.le_of_lt (rat_div_pos
      (rat_div_pos (hb (head t) (feat t)) (rat_mul_pos (hℓ (head t)) (hr (feat t))))
      (rat_div_pos (hb (head t) (feat (finNext hL t))) (rat_mul_pos (hℓ (head t)) (hr (feat (finNext hL t))))))
  · intro t
    have hhi := (hbound (head t) (feat t)).2
    have hlo := (hbound (head t) (feat (finNext hL t))).1
    have hden_pos : (0 : Rat) < b (head t) (feat (finNext hL t)) / (ℓ (head t) * r (feat (finNext hL t))) :=
      rat_div_pos (hb (head t) (feat (finNext hL t))) (rat_mul_pos (hℓ (head t)) (hr (feat (finNext hL t))))
    have hlam_max_nonneg : (0 : Rat) ≤ lam_max :=
      Rat.le_trans (Rat.le_of_lt (rat_div_pos (hb (head t) (feat t)) (rat_mul_pos (hℓ (head t)) (hr (feat t))))) hhi
    apply rat_div_le_div_of_cross hden_pos hlam_min
    exact rat_mul_le_mul hhi hlo (Rat.le_of_lt hlam_min) hlam_max_nonneg

/-- Helper: on the `H`-head cyclic witness, every 2-head subproblem satisfies `κ_pair^2 ≤ M^H`. -/
theorem cyclicWitness_pairwise_bound {H : Nat} (hH : 2 ≤ H) {M : Rat} (hM : (1 : Rat) ≤ M)
    (h1 h2 j1 j2 : Fin H) :
    twoHeadOptKappaSq (cyclicWitness H M h1 j1) (cyclicWitness H M h2 j1)
                      (cyclicWitness H M h1 j2) (cyclicWitness H M h2 j2) ≤
      ratPow M H := by
  have hM_pos : (0 : Rat) < M := rat_lt_of_lt_of_le (by decide) hM
  unfold twoHeadOptKappaSq cyclicWitness
  let e11 := (j1.val + H - h1.val) % H
  let e21 := (j1.val + H - h2.val) % H
  let e12 := (j2.val + H - h1.val) % H
  let e22 := (j2.val + H - h2.val) % H
  change (ratPow M e11 / ratPow M e21) / (ratPow M e12 / ratPow M e22) ≤ ratPow M H
  have hdiv :
      (ratPow M e11 / ratPow M e21) / (ratPow M e12 / ratPow M e22) =
      ratPow M (e11 + e22) / ratPow M (e21 + e12) := by
    rw [rat_div_div_eq (ratPow_ne_zero hM_pos e21) (ratPow_ne_zero hM_pos e12) (ratPow_ne_zero hM_pos e22)]
    rw [ratPow_add, ratPow_add]
  rw [hdiv]
  apply rat_div_le_of_mul_le (ratPow_pos hM_pos (e21 + e12))
  rw [← ratPow_add]
  apply ratPow_mono_exp hM
  -- Pure modular arithmetic: `e11 + e22 ≤ H + (e21 + e12)`!
  -- Because `e11 + e22` and `e21 + e12` are congruent mod `H`, and each is `< 2 * H`,
  -- their difference is at most `H`!
  have hmod1 : (e11 + e22) % H = (e21 + e12) % H := by
    have ha1 : j1.val + H - h1.val + (j2.val + H - h2.val) =
               j1.val + H - h2.val + (j2.val + H - h1.val) := by omega
    calc
      (e11 + e22) % H = ((j1.val + H - h1.val) % H + (j2.val + H - h2.val) % H) % H := rfl
      _ = (j1.val + H - h1.val + (j2.val + H - h2.val)) % H := by rw [← Nat.add_mod]
      _ = (j1.val + H - h2.val + (j2.val + H - h1.val)) % H := by rw [ha1]
      _ = ((j1.val + H - h2.val) % H + (j2.val + H - h1.val) % H) % H := by rw [Nat.add_mod]
      _ = (e21 + e12) % H := rfl
  have he11 : e11 < H := Nat.mod_lt _ (by omega)
  have he21 : e21 < H := Nat.mod_lt _ (by omega)
  have he12 : e12 < H := Nat.mod_lt _ (by omega)
  have he22 : e22 < H := Nat.mod_lt _ (by omega)
  have hdm1 : H * ((e11 + e22) / H) + (e11 + e22) % H = e11 + e22 := Nat.div_add_mod (e11 + e22) H
  have hdm2 : H * ((e21 + e12) / H) + (e21 + e12) % H = e21 + e12 := Nat.div_add_mod (e21 + e12) H
  have hq1 : (e11 + e22) / H < 2 := by
    apply Nat.div_lt_of_lt_mul
    omega
  have hq1_le : H * ((e11 + e22) / H) ≤ H := by
    match h : (e11 + e22) / H with
    | 0 => simp
    | 1 => simp
    | k + 2 => omega
  omega

/-- Helper: on the `H`-head cyclic witness, the cycle `feat t = t`, `head t = (t + 1) mod H`
    has exact cycle product `M^{H * (H - 1)}`. -/
theorem cyclicWitness_full_cycle_product {H : Nat} (hH : 2 ≤ H) (M : Rat) :
    let hHpos : 0 < H := Nat.lt_of_lt_of_le (by decide) hH
    karpCycleProduct hHpos (cyclicWitness H M) (fun t => finNext hHpos t) (fun t => t) =
      ratPow M (H * (H - 1)) := by
  intro hHpos
  unfold karpCycleProduct cyclicWitness
  have hterm : ∀ t : Fin H,
      ratPow M ((t.val + H - (finNext hHpos t).val) % H) /
      ratPow M (((finNext hHpos t).val + H - (finNext hHpos t).val) % H) =
      ratPow M (H - 1) := by
    intro t
    have hnum_exp : (t.val + H - (finNext hHpos t).val) % H = H - 1 := by
      simp only [finNext]
      by_cases hlt : t.val + 1 < H
      · rw [Nat.mod_eq_of_lt hlt]
        have : t.val + H - (t.val + 1) = H - 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      · have hlast : t.val + 1 = H := by omega
        rw [hlast, Nat.mod_self]
        have : t.val + H - 0 = H + (H - 1) := by omega
        rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    have hden_exp : ((finNext hHpos t).val + H - (finNext hHpos t).val) % H = 0 := by
      have : (finNext hHpos t).val + H - (finNext hHpos t).val = H := by omega
      rw [this, Nat.mod_self]
    rw [hnum_exp, hden_exp]
    simp only [ratPow, rat_div_one]
  rw [finProdRat_congr hterm, finProdRat_const, ← ratPow_mul, Nat.mul_comm]

/-- Headline Theorem 3 (`multihead_cyclic_frustration_karp_cycle_bound`). -/
theorem multihead_cyclic_frustration_karp_cycle_bound :
    (∀ {H d L : Nat} (hL : 0 < L)
      (b : Fin H → Fin d → Rat) (ℓ : Fin H → Rat) (r : Fin d → Rat),
      (∀ h j, (0 : Rat) < b h j) → (∀ h, (0 : Rat) < ℓ h) → (∀ j, (0 : Rat) < r j) →
      ∀ (head : Fin L → Fin H) (feat : Fin L → Fin d),
      karpScaledCycleProduct hL b ℓ r head feat = karpCycleProduct hL b head feat ∧
      (∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
        (∀ h j, lam_min ≤ b h j / (ℓ h * r j) ∧ b h j / (ℓ h * r j) ≤ lam_max) →
        karpCycleProduct hL b head feat ≤ ratPow (lam_max / lam_min) L)) ∧
    (∀ (H : Nat), 2 ≤ H → ∀ (M : Rat), (1 : Rat) ≤ M →
      (∀ h1 h2 j1 j2 : Fin H,
        twoHeadOptKappaSq (cyclicWitness H M h1 j1) (cyclicWitness H M h2 j1)
                          (cyclicWitness H M h1 j2) (cyclicWitness H M h2 j2) ≤
          ratPow M H) ∧
      (∀ (ℓ r : Fin H → Rat), (∀ h, (0 : Rat) < ℓ h) → (∀ j, (0 : Rat) < r j) →
        ∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
        (∀ h j, lam_min ≤ cyclicWitness H M h j / (ℓ h * r j) ∧
                cyclicWitness H M h j / (ℓ h * r j) ≤ lam_max) →
        ratPow M (H * (H - 1)) ≤ ratPow (lam_max / lam_min) H) ∧
      (∀ h j : Fin H,
        (1 : Rat) ≤ cyclicWitness H M h j ∧ cyclicWitness H M h j ≤ ratPow M (H - 1))) ∧
    (cyclicFrustrationRatio 2 = 1 ∧
     cyclicFrustrationRatio 3 = 4 / 3 ∧
     cyclicFrustrationRatio 4 = 3 / 2 ∧
     cyclicFrustrationRatio 8 = 7 / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro H d L hL b ℓ r hb hℓ hr head feat
    exact ⟨karp_cycle_kronecker_invariance hL b ℓ r hb hℓ hr head feat,
           fun lam_min lam_max hlam hbound =>
             karp_cycle_lower_bound hL b ℓ r hb hℓ hr head feat lam_min lam_max hlam hbound⟩
  · intro H hH M hM
    have hM_pos : (0 : Rat) < M := rat_lt_of_lt_of_le (by decide) hM
    have hHpos : 0 < H := Nat.lt_of_lt_of_le (by decide) hH
    refine ⟨fun h1 h2 j1 j2 => cyclicWitness_pairwise_bound hH hM h1 h2 j1 j2, ?_, ?_⟩
    · intro ℓ r hℓ hr lam_min lam_max hlam hbound
      have hcyc := cyclicWitness_full_cycle_product hH M
      rw [← hcyc]
      exact karp_cycle_lower_bound hHpos (cyclicWitness H M) ℓ r
        (fun h j => ratPow_pos hM_pos _) hℓ hr
        (fun t => finNext hHpos t) (fun t => t) lam_min lam_max hlam hbound
    · intro h j
      unfold cyclicWitness
      constructor
      · have h0 : ratPow M 0 = 1 := rfl
        rw [← h0]
        exact ratPow_mono_exp hM (Nat.zero_le _)
      · apply ratPow_mono_exp hM
        have hlt : (j.val + H - h.val) % H < H := Nat.mod_lt _ hHpos
        omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold cyclicFrustrationRatio
      have h1 : ((2 - 1 : Nat) : Rat) = 1 := by decide
      have h2 : ((2 : Nat) : Rat) = 2 := by decide
      rw [h1, h2, ← rat_div_one (1 : Rat)]
      apply rat_div_eq_of_cross (by decide) (by decide); grind
    · unfold cyclicFrustrationRatio
      have h1 : ((3 - 1 : Nat) : Rat) = 2 := by decide
      have h2 : ((3 : Nat) : Rat) = 3 := by decide
      rw [h1, h2]
      apply rat_div_eq_of_cross (by decide) (by decide); grind
    · unfold cyclicFrustrationRatio
      have h1 : ((4 - 1 : Nat) : Rat) = 3 := by decide
      have h2 : ((4 : Nat) : Rat) = 4 := by decide
      rw [h1, h2]
      apply rat_div_eq_of_cross (by decide) (by decide); grind
    · unfold cyclicFrustrationRatio
      have h1 : ((8 - 1 : Nat) : Rat) = 7 := by decide
      have h2 : ((8 : Nat) : Rat) = 8 := by decide
      rw [h1, h2]
      apply rat_div_eq_of_cross (by decide) (by decide); grind

end KroneckerCyclicFrustration
