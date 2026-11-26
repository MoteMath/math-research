/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonclipAdamwSr.RatOrder

/-!
# 2-State SR-EMA Markov Chain and Exact Preconditioner Jensen Bias Laws

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
- Theorem 4 (`sr_ema_two_state_markov_exact`)
- Theorem 5 (`preconditioner_jensen_bias_exact_sqrt_vs_v`)
-/

namespace MuonclipAdamwSr

/-! ### Theorem 4: `sr_ema_two_state_markov_exact` -/

theorem sr_ema_two_state_markov_exact :
    (∀ (l Δ r β : Rat), 0 < Δ → 0 ≤ r → r ≤ Δ → 0 ≤ β → β < 1 →
      (0 ≤ srEmaPi0 r Δ ∧ 0 ≤ srEmaPi1 r Δ ∧ srEmaPi0 r Δ + srEmaPi1 r Δ = 1) ∧
      (0 ≤ srEmaP01 β r Δ ∧ srEmaP01 β r Δ ≤ 1 ∧ 0 ≤ srEmaP10 β r Δ ∧ srEmaP10 β r Δ ≤ 1) ∧
      (srEmaPi0 r Δ * srEmaP01 β r Δ = srEmaPi1 r Δ * srEmaP10 β r Δ) ∧
      (srEmaPi0 r Δ * (1 - srEmaP01 β r Δ) + srEmaPi1 r Δ * srEmaP10 β r Δ = srEmaPi0 r Δ ∧
       srEmaPi0 r Δ * srEmaP01 β r Δ + srEmaPi1 r Δ * (1 - srEmaP10 β r Δ) = srEmaPi1 r Δ) ∧
      srEmaMean l Δ r = l + r ∧
      (srEmaVar l Δ r = r * (Δ - r) ∧ r * (Δ - r) ≤ (Δ * Δ) / 4) ∧
      srEmaLambda2 β r Δ = β ∧
      ((1 - srEmaP01 β r Δ) * (1 - srEmaP10 β r Δ) - srEmaP01 β r Δ * srEmaP10 β r Δ = β)) ∧
    (srEmaVarInflation (9 / 10) = 19 ∧ srEmaVarInflation (999 / 1000) = 1999) := by
  refine ⟨?_, ⟨by unfold srEmaVarInflation; grind, by unfold srEmaVarInflation; grind⟩⟩
  intro l Δ r β hΔ hr0 hrΔ hβ0 hβ1
  have hΔne : Δ ≠ 0 := Rat.ne_of_gt hΔ
  have h1mβ : (0 : Rat) < 1 - β := rat_sub_pos hβ1
  have h1mβ_le : 1 - β ≤ 1 := by
    apply rat_le_of_sub_nonneg
    have heq : 1 - (1 - β) = β := by grind
    rw [heq]; exact hβ0
  have hΔmr : (0 : Rat) ≤ Δ - r := rat_sub_nonneg hrΔ
  have hr_div_le : r / Δ ≤ 1 := by
    apply rat_div_le_of_mul_le hΔ
    rw [Rat.one_mul]; exact hrΔ
  have hΔmr_div_le : (Δ - r) / Δ ≤ 1 := by
    apply rat_div_le_of_mul_le hΔ
    rw [Rat.one_mul]
    apply rat_le_of_sub_nonneg
    have heq : Δ - (Δ - r) = r := by grind
    rw [heq]; exact hr0
  have hpi0_nonneg : (0 : Rat) ≤ srEmaPi0 r Δ := rat_sub_nonneg hr_div_le
  have hpi1_nonneg : (0 : Rat) ≤ srEmaPi1 r Δ := rat_div_nonneg hr0 hΔ
  have hpi_sum : srEmaPi0 r Δ + srEmaPi1 r Δ = 1 := by
    unfold srEmaPi0 srEmaPi1; grind
  have hp01_nonneg : (0 : Rat) ≤ srEmaP01 β r Δ :=
    rat_div_nonneg (Rat.mul_nonneg (Rat.le_of_lt h1mβ) hr0) hΔ
  have hp01_le : srEmaP01 β r Δ ≤ 1 := by
    unfold srEmaP01
    apply rat_div_le_of_mul_le hΔ
    rw [Rat.one_mul]
    have h1 : (1 - β) * r ≤ 1 * r := rat_mul_le_mul_of_nonneg_right h1mβ_le hr0
    rw [Rat.one_mul] at h1
    exact Rat.le_trans h1 hrΔ
  have hp10_nonneg : (0 : Rat) ≤ srEmaP10 β r Δ :=
    rat_div_nonneg (Rat.mul_nonneg (Rat.le_of_lt h1mβ) hΔmr) hΔ
  have hp10_le : srEmaP10 β r Δ ≤ 1 := by
    unfold srEmaP10
    apply rat_div_le_of_mul_le hΔ
    rw [Rat.one_mul]
    have h1 : (1 - β) * (Δ - r) ≤ 1 * (Δ - r) := rat_mul_le_mul_of_nonneg_right h1mβ_le hΔmr
    rw [Rat.one_mul] at h1
    have h2 : Δ - r ≤ Δ := by
      apply rat_le_of_sub_nonneg
      have heq : Δ - (Δ - r) = r := by grind
      rw [heq]; exact hr0
    exact Rat.le_trans h1 h2
  have hΔΔ_ne : Δ * Δ ≠ 0 := Rat.ne_of_gt (rat_mul_pos hΔ hΔ)
  have hdb : srEmaPi0 r Δ * srEmaP01 β r Δ = srEmaPi1 r Δ * srEmaP10 β r Δ := by
    unfold srEmaPi0 srEmaPi1 srEmaP01 srEmaP10
    have h1 : (r / Δ) * Δ = r := rat_div_mul_cancel hΔne
    have h2 : (((1 - β) * r) / Δ) * Δ = (1 - β) * r := rat_div_mul_cancel hΔne
    have h3 : (((1 - β) * (Δ - r)) / Δ) * Δ = (1 - β) * (Δ - r) := rat_div_mul_cancel hΔne
    have hmul : ((1 - r / Δ) * ((1 - β) * r / Δ) - (r / Δ) * ((1 - β) * (Δ - r) / Δ)) *
        (Δ * Δ) = 0 := by grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 => exact False.elim (hΔΔ_ne h0)
  have hstat0 : srEmaPi0 r Δ * (1 - srEmaP01 β r Δ) + srEmaPi1 r Δ * srEmaP10 β r Δ =
      srEmaPi0 r Δ := by grind
  have hstat1 : srEmaPi0 r Δ * srEmaP01 β r Δ + srEmaPi1 r Δ * (1 - srEmaP10 β r Δ) =
      srEmaPi1 r Δ := by grind
  have hmean : srEmaMean l Δ r = l + r := by
    unfold srEmaMean srEmaPi0 srEmaPi1
    have h1 : (r / Δ) * Δ = r := rat_div_mul_cancel hΔne
    grind
  have hvar : srEmaVar l Δ r = r * (Δ - r) := by
    unfold srEmaVar srEmaPi0 srEmaPi1
    have h1 : (r / Δ) * Δ = r := rat_div_mul_cancel hΔne
    have hmul : ((1 - r / Δ) * (l - (l + r)) * (l - (l + r)) +
        (r / Δ) * ((l + Δ) - (l + r)) * ((l + Δ) - (l + r)) - r * (Δ - r)) * Δ = 0 := by grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 => exact False.elim (hΔne h0)
  have hvar_le : r * (Δ - r) ≤ (Δ * Δ) / 4 := by
    apply rat_le_div_of_mul_le (by decide)
    apply rat_le_of_sub_nonneg
    have heq : Δ * Δ - r * (Δ - r) * 4 = (Δ - 2 * r) * (Δ - 2 * r) := by grind
    rw [heq]
    exact rat_sq_nonneg (Δ - 2 * r)
  have hlam2 : srEmaLambda2 β r Δ = β := by
    unfold srEmaLambda2 srEmaP01 srEmaP10
    have h1 : (((1 - β) * r) / Δ) * Δ = (1 - β) * r := rat_div_mul_cancel hΔne
    have h2 : (((1 - β) * (Δ - r)) / Δ) * Δ = (1 - β) * (Δ - r) := rat_div_mul_cancel hΔne
    have hmul : (((1 - (1 - β) * r / Δ) + (1 - (1 - β) * (Δ - r) / Δ) - 1) - β) * Δ = 0 := by
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 => exact False.elim (hΔne h0)
  have hdet : (1 - srEmaP01 β r Δ) * (1 - srEmaP10 β r Δ) -
      srEmaP01 β r Δ * srEmaP10 β r Δ = β := by
    have heq : (1 - srEmaP01 β r Δ) * (1 - srEmaP10 β r Δ) -
        srEmaP01 β r Δ * srEmaP10 β r Δ = srEmaLambda2 β r Δ := by
      unfold srEmaLambda2; grind
    rw [heq, hlam2]
  exact ⟨⟨hpi0_nonneg, hpi1_nonneg, hpi_sum⟩,
         ⟨hp01_nonneg, hp01_le, hp10_nonneg, hp10_le⟩,
         hdb, ⟨hstat0, hstat1⟩, hmean, ⟨hvar, hvar_le⟩, hlam2, hdet⟩

/-! ### Helper Identities for Theorem 5 -/

private theorem jensenV_cubic_sos (r t : Rat) (hr : r ≠ 0) :
    4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) -
      27 * r * r * (r + 1) * (r + 1) * jensenVSq r t =
      ((r - 1) * (3 * (r + 1) * t - (r + 2))) *
      ((r - 1) * (3 * (r + 1) * t - (r + 2))) *
      ((r + 2) * (r + 2) + 3 * (r * r - 1) * (1 - t)) := by
  unfold jensenVSq
  have h1 : (t / r) * r = t := rat_div_mul_cancel hr
  have h2 : (1 - t + t / r) * r = r - t * r + t := by grind
  have h3 : 27 * r * r * (r + 1) * (r + 1) *
      ((1 + t * (r * r - 1)) * (1 - t + t / r) * (1 - t + t / r)) =
      27 * (r + 1) * (r + 1) * (1 + t * (r * r - 1)) *
      ((1 - t + t / r) * r) * ((1 - t + t / r) * r) := by grind
  rw [h3, h2]
  grind

/-! ### Theorem 5: `preconditioner_jensen_bias_exact_sqrt_vs_v` -/

theorem preconditioner_jensen_bias_exact_sqrt_vs_v :
    (∀ a b s : Rat, a ≠ b → srDirectExpect a b s = s) ∧
    (∀ r_p t : Rat, 0 < r_p →
      jensenSqrtMax r_p - jensenSqrtFactor r_p t =
        ((r_p - 1) * (t - 1 / 2)) * ((r_p - 1) * (t - 1 / 2)) / r_p ∧
      jensenSqrtFactor r_p t ≤ jensenSqrtMax r_p ∧
      jensenSqrtFactor r_p (1 / 2) = jensenSqrtMax r_p) ∧
    (jensenSqrtMax 2 = 9 / 8 ∧ jensenSqrtFactor 2 (1 / 2) = 9 / 8 ∧
     jensenSqrtMax (3 / 2) = 25 / 24 ∧
     jensenSqrtMax (5 / 4) = 81 / 80 ∧
     jensenSqrtMax (9 / 8) = 289 / 288) ∧
    (∀ r t : Rat, 1 < r → 0 ≤ t → t ≤ 1 →
      27 * r * r * (r + 1) * (r + 1) * jensenVSq r t ≤
        4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) ∧
      jensenVSq r t ≤ jensenVMaxSq r ∧
      0 < jensenVOptT r ∧ jensenVOptT r < 1 ∧
      jensenVSq r (jensenVOptT r) = jensenVMaxSq r) ∧
    ((∀ r : Rat, r * r = 2 →
        4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) =
          27 * r * r * (r + 1) * (r + 1) * ((38 - 6 * r) / 27)) ∧
     ((14142 / 10000 : Rat) * (14142 / 10000) < 2 ∧
      2 < (14143 / 10000 : Rat) * (14143 / 10000)) ∧
     (∀ s : Rat, (14142 / 10000 : Rat) ≤ s → s ≤ (14143 / 10000 : Rat) →
        (10455 / 10000 : Rat) * (10455 / 10000) < (38 - 6 * s) / 27 ∧
        (38 - 6 * s) / 27 < (10456 / 10000 : Rat) * (10456 / 10000)) ∧
     ((27 / 10 : Rat) * ((10456 / 10000 : Rat) - 1) < (9 / 8 : Rat) - 1)) := by
  refine ⟨?_, ?_, ⟨by unfold jensenSqrtMax; grind,
                   by unfold jensenSqrtFactor; grind,
                   by unfold jensenSqrtMax; grind,
                   by unfold jensenSqrtMax; grind,
                   by unfold jensenSqrtMax; grind⟩, ?_, ?_⟩
  · -- Part 1: Direct SR of 1/sqrt(v) has exact zero Jensen bias
    intro a b s hab
    unfold srDirectExpect
    have hba : b - a ≠ 0 := by intro h0; apply hab; grind
    have h1 : ((b - s) / (b - a)) * (b - a) = b - s := rat_div_mul_cancel hba
    have h2 : ((s - a) / (b - a)) * (b - a) = s - a := rat_div_mul_cancel hba
    have hmul : (((b - s) / (b - a)) * a + ((s - a) / (b - a)) * b - s) * (b - a) = 0 := by grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 => exact False.elim (hba h0)
  · -- Part 2: SR of sqrt(v) exact closed-form & attainment at t = 1/2
    intro r_p t hrp
    have hrp_ne : r_p ≠ 0 := Rat.ne_of_gt hrp
    have h4rp_ne : 4 * r_p ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) hrp)
    have hdiff : jensenSqrtMax r_p - jensenSqrtFactor r_p t =
        ((r_p - 1) * (t - 1 / 2)) * ((r_p - 1) * (t - 1 / 2)) / r_p := by
      unfold jensenSqrtMax jensenSqrtFactor
      have h1 : (((r_p + 1) * (r_p + 1)) / (4 * r_p)) * (4 * r_p) = (r_p + 1) * (r_p + 1) :=
        rat_div_mul_cancel h4rp_ne
      have h2 : (t / r_p) * r_p = t := rat_div_mul_cancel hrp_ne
      have h3 : ((((r_p - 1) * (t - 1 / 2)) * ((r_p - 1) * (t - 1 / 2))) / r_p) * r_p =
          ((r_p - 1) * (t - 1 / 2)) * ((r_p - 1) * (t - 1 / 2)) := rat_div_mul_cancel hrp_ne
      have hmul : ((r_p + 1) * (r_p + 1) / (4 * r_p) -
          (1 + t * (r_p - 1)) * (1 - t + t / r_p) -
          ((r_p - 1) * (t - 1 / 2)) * ((r_p - 1) * (t - 1 / 2)) / r_p) * (4 * r_p) = 0 := by
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (h4rp_ne h0)
    refine ⟨hdiff, ?_, ?_⟩
    · apply rat_le_of_sub_nonneg
      rw [hdiff]
      exact rat_div_nonneg (rat_sq_nonneg _) hrp
    · have hhalf : jensenSqrtMax r_p - jensenSqrtFactor r_p (1 / 2) = 0 := by
        have h := hdiff
        -- Re-instantiate directly at t = 1/2
        unfold jensenSqrtMax jensenSqrtFactor
        have h1 : (((r_p + 1) * (r_p + 1)) / (4 * r_p)) * (4 * r_p) = (r_p + 1) * (r_p + 1) :=
          rat_div_mul_cancel h4rp_ne
        have h2 : ((1 / 2 : Rat) / r_p) * r_p = 1 / 2 := rat_div_mul_cancel hrp_ne
        have hmul : ((r_p + 1) * (r_p + 1) / (4 * r_p) -
            (1 + (1 / 2) * (r_p - 1)) * (1 - 1 / 2 + (1 / 2) / r_p)) * (4 * r_p) = 0 := by
          grind
        cases Rat.mul_eq_zero.mp hmul with
        | inl h0 => exact h0
        | inr h0 => exact False.elim (h4rp_ne h0)
      grind
  · -- Part 4: SR of v exact cubic SOS bound and attainment at t*(r)
    intro r t hr ht0 ht1
    have hr_pos : (0 : Rat) < r := rat_lt_trans (by decide) hr
    have hr_ne : r ≠ 0 := Rat.ne_of_gt hr_pos
    have hrp1_pos : (0 : Rat) < r + 1 := rat_add_pos hr_pos (by decide)
    have hrp1_ne : r + 1 ≠ 0 := Rat.ne_of_gt hrp1_pos
    have hden_pos : (0 : Rat) < 27 * r * r * (r + 1) * (r + 1) := by
      have h1 : (0 : Rat) < 27 * r := rat_mul_pos (by decide) hr_pos
      have h2 : (0 : Rat) < 27 * r * r := rat_mul_pos h1 hr_pos
      have h3 : (0 : Rat) < 27 * r * r * (r + 1) := rat_mul_pos h2 hrp1_pos
      exact rat_mul_pos h3 hrp1_pos
    have hden_ne : 27 * r * r * (r + 1) * (r + 1) ≠ 0 := Rat.ne_of_gt hden_pos
    have hbound : 27 * r * r * (r + 1) * (r + 1) * jensenVSq r t ≤
        4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) := by
      apply rat_le_of_sub_nonneg
      rw [jensenV_cubic_sos r t hr_ne]
      have hsq : (0 : Rat) ≤ ((r - 1) * (3 * (r + 1) * t - (r + 2))) *
          ((r - 1) * (3 * (r + 1) * t - (r + 2))) := rat_sq_nonneg _
      have hr2m1 : (0 : Rat) ≤ r * r - 1 := by
        apply rat_sub_nonneg
        have h := rat_mul_le_mul_of_nonneg_right (Rat.le_of_lt hr) (Rat.le_of_lt hr_pos)
        rw [Rat.one_mul] at h
        exact Rat.le_trans (Rat.le_of_lt hr) h
      have h1mt : (0 : Rat) ≤ 1 - t := rat_sub_nonneg ht1
      have hlin : (0 : Rat) ≤ (r + 2) * (r + 2) + 3 * (r * r - 1) * (1 - t) := by
        apply rat_add_nonneg (rat_sq_nonneg (r + 2))
        exact Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr2m1) h1mt
      exact Rat.mul_nonneg hsq hlin
    have hdiv_bound : jensenVSq r t ≤ jensenVMaxSq r := by
      unfold jensenVMaxSq
      apply rat_le_div_of_mul_le hden_pos
      rw [Rat.mul_comm]; exact hbound
    have htstar_pos : (0 : Rat) < jensenVOptT r := by
      unfold jensenVOptT
      exact rat_div_pos (rat_add_pos hr_pos (by decide)) (rat_mul_pos (by decide) hrp1_pos)
    have htstar_lt1 : jensenVOptT r < 1 := by
      unfold jensenVOptT
      apply rat_div_lt_of_mul_lt (rat_mul_pos (by decide) hrp1_pos)
      rw [Rat.one_mul]
      apply rat_lt_of_sub_pos
      have heq : 3 * (r + 1) - (r + 2) = 2 * r + 1 := by grind
      rw [heq]
      exact rat_add_pos (rat_mul_pos (by decide) hr_pos) (by decide)
    have hattain : jensenVSq r (jensenVOptT r) = jensenVMaxSq r := by
      have hsos := jensenV_cubic_sos r (jensenVOptT r) hr_ne
      have hzero : 3 * (r + 1) * jensenVOptT r - (r + 2) = 0 := by
        unfold jensenVOptT
        have h3rp1_ne : 3 * (r + 1) ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) hrp1_pos)
        rw [rat_mul_div_cancel h3rp1_ne]; grind
      rw [hzero] at hsos
      have heq_mul : 27 * r * r * (r + 1) * (r + 1) * jensenVSq r (jensenVOptT r) =
          4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) := by grind
      unfold jensenVMaxSq
      rw [Eq.comm, rat_div_eq_iff hden_ne]
      grind
    exact ⟨hbound, hdiv_bound, htstar_pos, htstar_lt1, hattain⟩
  · -- Part 5: E4M0 exact algebraic reduction and comparison vs 9/8
    have hsq_lo : (14142 / 10000 : Rat) * (14142 / 10000) < 2 := by
      apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 100000000)
      have hL : (14142 / 10000 : Rat) * (14142 / 10000) * 100000000 = 199996164 := by grind
      have hR : (2 : Rat) * 100000000 = 200000000 := by grind
      rw [hL, hR]; decide
    have hsq_hi : (2 : Rat) < (14143 / 10000 : Rat) * (14143 / 10000) := by
      apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 100000000)
      have hL : (2 : Rat) * 100000000 = 200000000 := by grind
      have hR : (14143 / 10000 : Rat) * (14143 / 10000) * 100000000 = 200024449 := by grind
      rw [hL, hR]; decide
    have hcmp : (27 / 10 : Rat) * ((10456 / 10000 : Rat) - 1) < (9 / 8 : Rat) - 1 := by
      apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 800000)
      have hL : (27 / 10 : Rat) * ((10456 / 10000 : Rat) - 1) * 800000 = 98496 := by grind
      have hR : ((9 / 8 : Rat) - 1) * 800000 = 100000 := by grind
      rw [hL, hR]; decide
    refine ⟨?_, ⟨hsq_lo, hsq_hi⟩, ?_, hcmp⟩
    · intro r hr2
      have hmul : (4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) -
          27 * r * r * (r + 1) * (r + 1) * ((38 - 6 * r) / 27)) = 0 := by
        have h27 : ((38 - 6 * r) / 27) * 27 = 38 - 6 * r := rat_div_mul_cancel (by decide)
        grind
      grind
    · intro s hs_lo hs_hi
      have h6_lo : 6 * (14142 / 10000 : Rat) ≤ 6 * s :=
        rat_mul_le_mul_of_nonneg_left hs_lo (by decide)
      have h6_hi : 6 * s ≤ 6 * (14143 / 10000 : Rat) :=
        rat_mul_le_mul_of_nonneg_left hs_hi (by decide)
      constructor
      · apply rat_lt_div_of_mul_lt (by decide)
        have hnum : (10455 / 10000 : Rat) * (10455 / 10000) * 27 < 38 - 6 * (14143 / 10000 : Rat) := by
          apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 100000000)
          have hL : (10455 / 10000 : Rat) * (10455 / 10000) * 27 * 100000000 = 2951289675 := by grind
          have hR : (38 - 6 * (14143 / 10000 : Rat)) * 100000000 = 2951420000 := by grind
          rw [hL, hR]; decide
        have hle : 38 - 6 * (14143 / 10000 : Rat) ≤ 38 - 6 * s := by
          apply rat_le_of_sub_nonneg
          have h := rat_sub_nonneg h6_hi
          have heq : (38 - 6 * s) - (38 - 6 * (14143 / 10000 : Rat)) =
              6 * (14143 / 10000 : Rat) - 6 * s := by grind
          rw [heq]; exact h
        exact rat_lt_of_lt_of_le hnum hle
      · apply rat_div_lt_of_mul_lt (by decide)
        have hnum : 38 - 6 * (14142 / 10000 : Rat) < (10456 / 10000 : Rat) * (10456 / 10000) * 27 := by
          apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 100000000)
          have hL : (38 - 6 * (14142 / 10000 : Rat)) * 100000000 = 2951480000 := by grind
          have hR : (10456 / 10000 : Rat) * (10456 / 10000) * 27 * 100000000 = 2951854272 := by grind
          rw [hL, hR]; decide
        have hle : 38 - 6 * s ≤ 38 - 6 * (14142 / 10000 : Rat) := by
          apply rat_le_of_sub_nonneg
          have h := rat_sub_nonneg h6_lo
          have heq : (38 - 6 * (14142 / 10000 : Rat)) - (38 - 6 * s) =
              6 * s - 6 * (14142 / 10000 : Rat) := by grind
          rw [heq]; exact h
        exact rat_lt_of_le_of_lt hle hnum

end MuonclipAdamwSr
