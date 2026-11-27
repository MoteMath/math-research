/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp4OptClipping.RatOrder

/-!
# MXFP4 (`E2M1 + E8M0`) Optimal Clipping Theorems (Theorems 1, 2, and 5)

Proves:
1. `mxfp4_e8m0_scale_down_piecewise_linear_crossover`
2. `mxfp4_opt_e8m0_all_b_ef21_three_regime_law`
5. `mxfp4_opt_e8m0_never_drops_two_exponents`
-/

namespace Mxfp4OptClipping

/-! ### Helper Lemmas for Theorem 1 -/

theorem clipPenalty_on_3_7half {M : Rat} (hlo : (3 : Rat) ≤ M) (hhi : M ≤ 7 / 2) :
    clipPenalty M = 0 := by
  unfold clipPenalty
  rw [e2m1ErrSq_1_on_3_7half hlo hhi]
  grind

theorem clipPenalty_on_7half_5 {M : Rat} (hlo : (7 / 2 : Rat) ≤ M) (hhi : M ≤ 5) :
    clipPenalty M = 2 * M - 7 := by
  unfold clipPenalty
  rw [e2m1ErrSq_1_on_7half_5 hlo hhi]
  unfold sq
  grind

theorem clipPenalty_on_5_6 {M : Rat} (hlo : (5 : Rat) ≤ M) (_hhi : M ≤ 6) :
    clipPenalty M = 6 * M - 27 := by
  unfold clipPenalty
  rw [e2m1ErrSq_1_on_ge_5 hlo]
  unfold sq
  grind

theorem blockErrSq_half_sub_one (x : List Rat) :
    blockErrSq (1 / 2) x - blockErrSq 1 x = clipCost x - bulkGain x := by
  induction x with
  | nil => simp [blockErrSq, clipCost, bulkGain]
  | cons u xs ih =>
    simp only [blockErrSq, clipCost, bulkGain]
    by_cases h : (3 : Rat) < absRat u
    · have hnot : ¬ absRat u ≤ (3 : Rat) := Rat.not_le.mpr h
      simp only [h, hnot, ite_true, ite_false]
      have hehalf : e2m1ErrSq (1 / 2) u = sq (absRat u - 3) := by
        have htop := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := u) (by grind)
          (by grind)
        have hid : (1 / 2 : Rat) * 6 = 3 := by grind
        rw [hid] at htop; exact htop
      unfold clipPenalty
      rw [e2m1ErrSq_abs, hehalf]
      grind
    · have hle : absRat u ≤ (3 : Rat) := Rat.not_lt.mp h
      simp only [h, hle, ite_true, ite_false]
      grind

/-- Theorem 1: Exact MXFP4 (`E2M1 + E8M0`) Piecewise-Linear Scale-Down Crossover Law. -/
theorem mxfp4_e8m0_scale_down_piecewise_linear_crossover :
    (∀ M : Rat, 3 ≤ M → M ≤ 7 / 2 → clipPenalty M = 0) ∧
    (∀ M : Rat, 7 / 2 ≤ M → M ≤ 5 → clipPenalty M = 2 * M - 7) ∧
    (∀ M : Rat, 5 ≤ M → M ≤ 6 → clipPenalty M = 6 * M - 27) ∧
    (∀ x : List Rat,
      blockErrSq (1 / 2) x - blockErrSq 1 x = clipCost x - bulkGain x ∧
      (blockErrSq (1 / 2) x < blockErrSq 1 x ↔ clipCost x < bulkGain x)) ∧
    (∀ M Δ : Rat, 3 < M → M ≤ 7 / 2 → 0 < Δ → clipPenalty M < Δ) ∧
    (∀ M Δ : Rat, 7 / 2 ≤ M → M ≤ 5 → (clipPenalty M < Δ ↔ M < (7 + Δ) / 2)) ∧
    (∀ M Δ : Rat, 5 ≤ M → M ≤ 6 → (clipPenalty M < Δ ↔ M < 9 / 2 + Δ / 6)) ∧
    (∀ M Δ : Rat, 3 ≤ M → M ≤ 6 → 9 < Δ → clipPenalty M < Δ) := by
  refine ⟨fun M h1 h2 => clipPenalty_on_3_7half h1 h2,
          fun M h1 h2 => clipPenalty_on_7half_5 h1 h2,
          fun M h1 h2 => clipPenalty_on_5_6 h1 h2, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hdiff := blockErrSq_half_sub_one x
    refine ⟨hdiff, ?_⟩
    constructor
    · intro hlt
      have h1 := rat_sub_pos hlt
      have h2 : (0 : Rat) < bulkGain x - clipCost x := by grind
      exact rat_lt_of_sub_pos h2
    · intro hlt
      have h1 := rat_sub_pos hlt
      have h2 : (0 : Rat) < blockErrSq 1 x - blockErrSq (1 / 2) x := by grind
      exact rat_lt_of_sub_pos h2
  · intro M Δ h1 h2 hΔ
    rw [clipPenalty_on_3_7half (Rat.le_of_lt h1) h2]
    exact hΔ
  · intro M Δ h1 h2
    rw [clipPenalty_on_7half_5 h1 h2]
    constructor <;> intro h <;> grind
  · intro M Δ h1 h2
    rw [clipPenalty_on_5_6 h1 h2]
    constructor <;> intro h <;> grind
  · intro M Δ h1 h2 hΔ
    cases Rat.le_total (a := M) (b := (7 / 2 : Rat)) with
    | inl hle1 =>
      rw [clipPenalty_on_3_7half h1 hle1]
      exact rat_lt_trans (by grind) hΔ
    | inr hge1 =>
      cases Rat.le_total (a := M) (b := (5 : Rat)) with
      | inl hle2 =>
        rw [clipPenalty_on_7half_5 hge1 hle2]
        have : 2 * M - 7 ≤ 3 := by grind
        exact rat_lt_of_le_of_lt (Rat.le_trans this (by grind)) hΔ
      | inr hge2 =>
        rw [clipPenalty_on_5_6 hge2 h2]
        have : 6 * M - 27 ≤ 9 := by grind
        exact rat_lt_of_le_of_lt this hΔ

/-! ### Coordinatewise Bounds for Theorem 2 (`opt-E8M0`) -/

/-- Helper: for a convex quadratic `(a - q)^2 - w * a^2 = (1 - w)*a^2 - 2q*a + q^2` with `w ≤ 1`,
    if it is `≤ K` at endpoints `l, r`, it is `≤ K` on `[l, r]`. -/
theorem err_sub_wsq_le_on {q w K l r a : Rat} (hw : w ≤ 1)
    (hl : l ≤ a) (hr : a ≤ r)
    (hfl : sq (l - q) - w * sq l ≤ K)
    (hfr : sq (r - q) - w * sq r ≤ K) :
    sq (a - q) - w * sq a ≤ K := by
  have h1 : (1 - w) * (l * l) + (-2 * q) * l + q * q ≤ K := by
    have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by
      unfold sq; grind
    rw [hid]; exact hfl
  have h2 : (1 - w) * (r * r) + (-2 * q) * r + q * q ≤ K := by
    have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by
      unfold sq; grind
    rw [hid]; exact hfr
  have hc := convex_quad_le_of_endpoints (rat_sub_nonneg hw) hl hr h1 h2
  have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by
    unfold sq; grind
  rw [← hid]; exact hc

/-- For any `w ∈ [1/25, 1]` and any `u` with `|u| ≤ 6`, `e₁(u) - w*u² ≤ (1 - w) / 16`. -/
theorem e1_sub_wsq_le {w u : Rat} (hw_lo : (1 / 25 : Rat) ≤ w) (hw_hi : w ≤ 1)
    (hu : absRat u ≤ 6) :
    e2m1ErrSq 1 u - w * sq u ≤ (1 - w) / 16 := by
  rw [← sq_absRat u]
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
      (e2m1ErrSq 1 u ≤ sq (a - q)) →
      sq (l - q) - w * sq l ≤ (1 - w) / 16 →
      sq (r - q) - w * sq r ≤ (1 - w) / 16 →
      e2m1ErrSq 1 u - w * sq a ≤ (1 - w) / 16 := by
    intro q l r hl hr hle hfl hfr
    have hq := err_sub_wsq_le_on hw_hi hl hr hfl hfr
    have hsub : e2m1ErrSq 1 u - w * sq a ≤ sq (a - q) - w * sq a := by grind
    exact Rat.le_trans hsub hq
  -- Case split across the 8 Voronoi cells of E2M1 at s = 1
  cases Rat.le_total (a := a) (b := (1 / 4 : Rat)) with
  | inl h1 =>
    exact hstep 0 0 (1 / 4) ha0 h1 (e2m1ErrSq_le_0 1 u)
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (3 / 4 : Rat)) with
    | inl h2 =>
      exact hstep (1 / 2) (1 / 4) (3 / 4) h1 h2
        (by have := e2m1ErrSq_le_half 1 u; grind)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (5 / 4 : Rat)) with
      | inl h3 =>
        exact hstep 1 (3 / 4) (5 / 4) h2 h3
          (by have := e2m1ErrSq_le_1 1 u; grind)
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h3 =>
        cases Rat.le_total (a := a) (b := (7 / 4 : Rat)) with
        | inl h4 =>
          exact hstep (3 / 2) (5 / 4) (7 / 4) h3 h4
            (by have := e2m1ErrSq_le_3half 1 u; grind)
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h4 =>
          cases Rat.le_total (a := a) (b := (5 / 2 : Rat)) with
          | inl h5 =>
            exact hstep 2 (7 / 4) (5 / 2) h4 h5
              (by have := e2m1ErrSq_le_2 1 u; grind)
              (by unfold sq; grind) (by unfold sq; grind)
          | inr h5 =>
            cases Rat.le_total (a := a) (b := (7 / 2 : Rat)) with
            | inl h6 =>
              exact hstep 3 (5 / 2) (7 / 2) h5 h6
                (by have := e2m1ErrSq_le_3 1 u; grind)
                (by unfold sq; grind) (by unfold sq; grind)
            | inr h6 =>
              cases Rat.le_total (a := a) (b := (5 : Rat)) with
              | inl h7 =>
                exact hstep 4 (7 / 2) 5 h6 h7
                  (by have := e2m1ErrSq_le_4 1 u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)
              | inr h7 =>
                exact hstep 6 5 6 h7 hu
                  (by have := e2m1ErrSq_le_6 1 u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)

/-- For any `w ∈ [1/25, 1]` and any `u` with `|u| ≤ 3`, `e_{1/2}(u) - w*u² ≤ (1 - w) / 64`. -/
theorem ehalf_sub_wsq_le_on_le3 {w u : Rat} (hw_lo : (1 / 25 : Rat) ≤ w) (hw_hi : w ≤ 1)
    (hu : absRat u ≤ 3) :
    e2m1ErrSq (1 / 2) u - w * sq u ≤ (1 - w) / 64 := by
  rw [← sq_absRat u]
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
      (e2m1ErrSq (1 / 2) u ≤ sq (a - q)) →
      sq (l - q) - w * sq l ≤ (1 - w) / 64 →
      sq (r - q) - w * sq r ≤ (1 - w) / 64 →
      e2m1ErrSq (1 / 2) u - w * sq a ≤ (1 - w) / 64 := by
    intro q l r hl hr hle hfl hfr
    have hq := err_sub_wsq_le_on hw_hi hl hr hfl hfr
    have hsub : e2m1ErrSq (1 / 2) u - w * sq a ≤ sq (a - q) - w * sq a := by grind
    exact Rat.le_trans hsub hq
  cases Rat.le_total (a := a) (b := (1 / 8 : Rat)) with
  | inl h1 =>
    exact hstep 0 0 (1 / 8) ha0 h1 (e2m1ErrSq_le_0 (1 / 2) u)
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (3 / 8 : Rat)) with
    | inl h2 =>
      exact hstep (1 / 4) (1 / 8) (3 / 8) h1 h2
        (by have := e2m1ErrSq_le_half (1 / 2) u; grind)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (5 / 8 : Rat)) with
      | inl h3 =>
        exact hstep (1 / 2) (3 / 8) (5 / 8) h2 h3
          (by have := e2m1ErrSq_le_1 (1 / 2) u; grind)
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h3 =>
        cases Rat.le_total (a := a) (b := (7 / 8 : Rat)) with
        | inl h4 =>
          exact hstep (3 / 4) (5 / 8) (7 / 8) h3 h4
            (by have := e2m1ErrSq_le_3half (1 / 2) u; grind)
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h4 =>
          cases Rat.le_total (a := a) (b := (5 / 4 : Rat)) with
          | inl h5 =>
            exact hstep 1 (7 / 8) (5 / 4) h4 h5
              (by have := e2m1ErrSq_le_2 (1 / 2) u; grind)
              (by unfold sq; grind) (by unfold sq; grind)
          | inr h5 =>
            cases Rat.le_total (a := a) (b := (7 / 4 : Rat)) with
            | inl h6 =>
              exact hstep (3 / 2) (5 / 4) (7 / 4) h5 h6
                (by have := e2m1ErrSq_le_3 (1 / 2) u; grind)
                (by unfold sq; grind) (by unfold sq; grind)
            | inr h6 =>
              cases Rat.le_total (a := a) (b := (5 / 2 : Rat)) with
              | inl h7 =>
                exact hstep 2 (7 / 4) (5 / 2) h6 h7
                  (by have := e2m1ErrSq_le_4 (1 / 2) u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)
              | inr h7 =>
                exact hstep 3 (5 / 2) 3 h7 hu
                  (by have := e2m1ErrSq_le_6 (1 / 2) u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)

/-- Key Lagrangian coordinatewise bound: with `λ₀ = (3/4)*(1 - w)` and `w ∈ [1/10, 1]`,
    for EVERY `u` with `|u| ≤ 3`, `(1 - λ₀)*e₁(u) + λ₀*e_{1/2}(u) - w*u² ≤ (1 - w)/64`! -/
theorem lam0_bulk_le3 {w u : Rat} (hw_lo : (1 / 10 : Rat) ≤ w) (hw_hi : w ≤ 1)
    (hu : absRat u ≤ 3) :
    let lam := (3 / 4 : Rat) * (1 - w)
    (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (1 / 2) u - w * sq u ≤ (1 - w) / 64 := by
  intro lam
  rw [← sq_absRat u]
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  have hlam0 : (0 : Rat) ≤ lam := by grind
  have h1lam0 : (0 : Rat) ≤ 1 - lam := by grind
  have hstep : ∀ q1 q2 l r : Rat, l ≤ a → a ≤ r →
      (e2m1ErrSq 1 u ≤ sq (a - q1)) →
      (e2m1ErrSq (1 / 2) u ≤ sq (a - q2)) →
      (1 - lam) * sq (l - q1) + lam * sq (l - q2) - w * sq l ≤ (1 - w) / 64 →
      (1 - lam) * sq (r - q1) + lam * sq (r - q2) - w * sq r ≤ (1 - w) / 64 →
      (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (1 / 2) u - w * sq a ≤ (1 - w) / 64 := by
    intro q1 q2 l r hl hr hq1 hq2 hfl hfr
    have hmul1 := rat_mul_le_mul_of_nonneg_left hq1 h1lam0
    have hmul2 := rat_mul_le_mul_of_nonneg_left hq2 hlam0
    have hle : (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (1 / 2) u - w * sq a ≤
        (1 - lam) * sq (a - q1) + lam * sq (a - q2) - w * sq a := by grind
    have hquad_eq : ∀ t : Rat,
        (1 - w) * (t * t) + (-2 * ((1 - lam) * q1 + lam * q2)) * t +
          ((1 - lam) * (q1 * q1) + lam * (q2 * q2)) =
        (1 - lam) * sq (t - q1) + lam * sq (t - q2) - w * sq t := by
      intro t; unfold sq; grind
    have hc := convex_quad_le_of_endpoints (rat_sub_nonneg hw_hi) hl hr
      (by rw [hquad_eq]; exact hfl) (by rw [hquad_eq]; exact hfr)
    rw [hquad_eq] at hc
    exact Rat.le_trans hle hc
  -- Split on [0, 1/8], [1/8, 1/4], [1/4, 3/8], [3/8, 5/8], [5/8, 3/4], [3/4, 7/8], [7/8, 5/4], [5/4, 7/4], [7/4, 5/2], [5/2, 3]
  cases Rat.le_total (a := a) (b := (1 / 8 : Rat)) with
  | inl h1 =>
    exact hstep 0 0 0 (1 / 8) ha0 h1 (e2m1ErrSq_le_0 1 u) (e2m1ErrSq_le_0 (1 / 2) u)
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (1 / 4 : Rat)) with
    | inl h2 =>
      exact hstep 0 (1 / 4) (1 / 8) (1 / 4) h1 h2
        (e2m1ErrSq_le_0 1 u) (by have := e2m1ErrSq_le_half (1 / 2) u; grind)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (3 / 8 : Rat)) with
      | inl h3 =>
        exact hstep (1 / 2) (1 / 4) (1 / 4) (3 / 8) h2 h3
          (by have := e2m1ErrSq_le_half 1 u; grind) (by have := e2m1ErrSq_le_half (1 / 2) u; grind)
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h3 =>
        cases Rat.le_total (a := a) (b := (3 / 4 : Rat)) with
        | inl h4 =>
          exact hstep (1 / 2) (1 / 2) (3 / 8) (3 / 4) h3 h4
            (by have := e2m1ErrSq_le_half 1 u; grind) (by have := e2m1ErrSq_le_1 (1 / 2) u; grind)
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h4 =>
          cases Rat.le_total (a := a) (b := (5 / 4 : Rat)) with
          | inl h5 =>
            exact hstep 1 1 (3 / 4) (5 / 4) h4 h5
              (by have := e2m1ErrSq_le_1 1 u; grind) (by have := e2m1ErrSq_le_2 (1 / 2) u; grind)
              (by unfold sq; grind) (by unfold sq; grind)
          | inr h5 =>
            cases Rat.le_total (a := a) (b := (7 / 4 : Rat)) with
            | inl h6 =>
              exact hstep (3 / 2) (3 / 2) (5 / 4) (7 / 4) h5 h6
                (by have := e2m1ErrSq_le_3half 1 u; grind) (by have := e2m1ErrSq_le_3 (1 / 2) u; grind)
                (by unfold sq; grind) (by unfold sq; grind)
            | inr h6 =>
              cases Rat.le_total (a := a) (b := (5 / 2 : Rat)) with
              | inl h7 =>
                exact hstep 2 2 (7 / 4) (5 / 2) h6 h7
                  (by have := e2m1ErrSq_le_2 1 u; grind) (by have := e2m1ErrSq_le_4 (1 / 2) u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)
              | inr h7 =>
                exact hstep 3 3 (5 / 2) 3 h7 hu
                  (by have := e2m1ErrSq_le_3 1 u; grind) (by have := e2m1ErrSq_le_6 (1 / 2) u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)

/-- Block-sum helper: if `f(u) ≤ C` for all `u ∈ xs` and `f(M) ≤ D` for one `M ∈ xs`,
    then `∑_{u ∈ xs} f(u) ≤ D + (xs.length - 1) * C`. -/
theorem block_sum_bound_with_pivot (f : Rat → Rat) (C D : Rat)
    (x : List Rat) (hC : ∀ u ∈ x, f u ≤ C)
    (hpivot : ∃ M ∈ x, f M ≤ D) :
    (x.foldr (fun u acc => f u + acc) 0) ≤ D + ((x.length - 1 : Nat) : Rat) * C := by
  induction x with
  | nil =>
    rcases hpivot with ⟨M, hmem, _⟩
    cases hmem
  | cons a xs ih =>
    simp only [List.foldr, List.length_cons, Nat.add_sub_cancel]
    rcases hpivot with ⟨M, hmem, hM⟩
    cases hmem with
    | head =>
      have hrest : ∀ l : List Rat, (∀ u ∈ l, f u ≤ C) →
          l.foldr (fun u acc => f u + acc) 0 ≤ (l.length : Rat) * C := by
        intro l hl
        induction l with
        | nil => simp
        | cons b bs ihb =>
          simp only [List.foldr, List.length_cons, Rat.natCast_add]
          have hb := hl b (List.Mem.head _)
          have hbs := ihb (fun u hu => hl u (List.Mem.tail _ hu))
          have hadd := rat_add_le_add hb hbs
          grind
      have hxs := hrest xs (fun u hu => hC u (List.Mem.tail _ hu))
      exact rat_add_le_add hM hxs
    | tail _ hmem_xs =>
      cases xs with
      | nil => cases hmem_xs
      | cons b bs =>
        have ha := hC a (List.Mem.head _)
        have hih := ih (fun u hu => hC u (List.Mem.tail _ hu)) ⟨M, hmem_xs, hM⟩
        have hadd := rat_add_le_add ha hih
        simp only [List.length_cons, Nat.add_sub_cancel] at hih hadd ⊢
        rw [Rat.natCast_add]
        grind

theorem blockErrSq_sub_wEnergy_eq_foldr (s w : Rat) (x : List Rat) :
    blockErrSq s x - w * blockEnergy x =
      x.foldr (fun u acc => (e2m1ErrSq s u - w * sq u) + acc) 0 := by
  induction x with
  | nil => simp [blockErrSq, blockEnergy]; grind
  | cons u xs ih =>
    simp only [blockErrSq, blockEnergy, List.foldr]
    grind

theorem convex_blockErrSq_sub_wEnergy_eq_foldr (lam w : Rat) (x : List Rat) :
    (1 - lam) * blockErrSq 1 x + lam * blockErrSq (1 / 2) x - w * blockEnergy x =
      x.foldr (fun u acc => ((1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (1 / 2) u - w * sq u) + acc) 0 := by
  induction x with
  | nil => simp [blockErrSq, blockEnergy]; grind
  | cons u xs ih =>
    simp only [blockErrSq, blockEnergy, List.foldr]
    grind

/-- Parameterized Regime-1 theorem: if `M_cut ∈ [3, 5]` separates `s = 1/2` (`M ≤ M_cut`)
    from `s = 1` (`M_cut ≤ M`), then `min(E₁(x), E_{1/2}(x)) ≤ w * ‖x‖²` for all blocks of length `B`. -/
theorem opt_e8m0_bound_of_cut (B : Nat) (w M_cut : Rat)
    (hw_lo : (1 / 25 : Rat) ≤ w) (hw_hi : w ≤ 1)
    (hcut_lo : (3 : Rat) ≤ M_cut) (hcut_hi : M_cut ≤ 5)
    (h12_pt : sq (M_cut - 3) - w * sq M_cut ≤ (1 - w) / 64)
    (h12_sum : sq (M_cut - 3) - w * sq M_cut + ((B - 1 : Nat) : Rat) * ((1 - w) / 64) ≤ 0)
    (h1_cut : e2m1ErrSq 1 M_cut - w * sq M_cut + ((B - 1 : Nat) : Rat) * ((1 - w) / 16) ≤ 0)
    (h1_7half : M_cut ≤ 7 / 2 → (1 / 4 : Rat) - w * (49 / 4) + ((B - 1 : Nat) : Rat) * ((1 - w) / 16) ≤ 0)
    (_h1_4 : M_cut ≤ 4 → -w * 16 + ((B - 1 : Nat) : Rat) * ((1 - w) / 16) ≤ 0)
    (h1_5 : 1 - w * 25 + ((B - 1 : Nat) : Rat) * ((1 - w) / 16) ≤ 0)
    (x : List Rat) (hx_len : x.length = B)
    (hx_max : ∃ M ∈ x, 3 ≤ absRat M ∧ absRat M ≤ 6 ∧ ∀ u ∈ x, absRat u ≤ absRat M) :
    min (blockErrSq 1 x) (blockErrSq (1 / 2) x) ≤ w * blockEnergy x := by
  rcases hx_max with ⟨M, hM_mem, hM_lo, hM_hi, hM_all⟩
  cases Rat.le_total (a := absRat M) (b := M_cut) with
  | inl hle_cut =>
    -- Use s = 1/2!
    apply Rat.le_trans (rat_min_le_right _ _)
    apply rat_le_of_sub_nonneg
    have hsub : blockErrSq (1 / 2) x - w * blockEnergy x ≤ 0 := by
      rw [blockErrSq_sub_wEnergy_eq_foldr]
      have hpivot : e2m1ErrSq (1 / 2) M - w * sq M ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) := by
        rw [← sq_absRat M]
        have htop := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := M) (by grind)
          (by grind)
        have hid : (1 / 2 : Rat) * 6 = 3 := by grind
        rw [hid] at htop; rw [htop]
        have h3 : sq ((3 : Rat) - 3) - w * sq 3 ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) := by
          have hB0 : (0 : Rat) ≤ ((B - 1 : Nat) : Rat) := rat_natCast_nonneg (B - 1)
          have h12_3 : sq (M_cut - 3) - w * sq M_cut ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) := by grind
          -- Since h1_5 gives (B-1)*(1-w)/16 ≤ 25*w - 1, dividing by 4 gives
          -- (B-1)*(1-w)/64 ≤ (25*w - 1)/4 < 9*w (because 25w - 1 < 36w), which closes the bound.
          have hdiv4 : ((B - 1 : Nat) : Rat) * ((1 - w) / 64) ≤ (25 * w - 1) / 4 := by grind
          unfold sq; grind
        exact err_sub_wsq_le_on hw_hi hM_lo hle_cut h3 (by grind)
      have hall : ∀ u ∈ x, e2m1ErrSq (1 / 2) u - w * sq u ≤ (1 - w) / 64 := by
        intro u hu
        have hu_le : absRat u ≤ M_cut := Rat.le_trans (hM_all u hu) hle_cut
        cases Rat.le_total (a := absRat u) (b := (3 : Rat)) with
        | inl hle3 => exact ehalf_sub_wsq_le_on_le3 hw_lo hw_hi hle3
        | inr hge3 =>
          rw [← sq_absRat u]
          have htop := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := u) (by grind)
            (by grind)
          have hid : (1 / 2 : Rat) * 6 = 3 := by grind
          rw [hid] at htop; rw [htop]
          exact err_sub_wsq_le_on hw_hi hge3 hu_le (by unfold sq; grind) h12_pt
      have hsum := block_sum_bound_with_pivot (fun u => e2m1ErrSq (1 / 2) u - w * sq u)
        ((1 - w) / 64) (-(((B - 1 : Nat) : Rat) * ((1 - w) / 64))) x hall ⟨M, hM_mem, hpivot⟩
      rw [hx_len] at hsum
      grind
    grind
  | inr hge_cut =>
    -- Use s = 1!
    apply Rat.le_trans (rat_min_le_left _ _)
    apply rat_le_of_sub_nonneg
    have hsub : blockErrSq 1 x - w * blockEnergy x ≤ 0 := by
      rw [blockErrSq_sub_wEnergy_eq_foldr]
      have hall : ∀ u ∈ x, e2m1ErrSq 1 u - w * sq u ≤ (1 - w) / 16 := by
        intro u hu
        exact e1_sub_wsq_le hw_lo hw_hi (Rat.le_trans (hM_all u hu) hM_hi)
      have hpivot : e2m1ErrSq 1 M - w * sq M ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 16)) := by
        let a := absRat M
        rw [← e2m1ErrSq_abs, ← sq_absRat M]
        have h6 : sq ((6 : Rat) - 6) - w * sq 6 ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 16)) := by
          unfold sq; grind
        cases Rat.le_total (a := a) (b := (7 / 2 : Rat)) with
        | inl ha72 =>
          rw [e2m1ErrSq_1_on_3_7half hM_lo ha72]
          have hcut72 : M_cut ≤ 7 / 2 := Rat.le_trans hge_cut ha72
          have hcut_val : e2m1ErrSq 1 M_cut = sq (M_cut - 3) := e2m1ErrSq_1_on_3_7half hcut_lo hcut72
          rw [hcut_val] at h1_cut
          have h72_val := h1_7half hcut72
          exact err_sub_wsq_le_on hw_hi hge_cut ha72 (by grind) (by unfold sq; grind)
        | inr ha72 =>
          cases Rat.le_total (a := a) (b := (5 : Rat)) with
          | inl ha5 =>
            rw [e2m1ErrSq_1_on_7half_5 ha72 ha5]
            cases Rat.le_total (a := M_cut) (b := (7 / 2 : Rat)) with
            | inl hcut72 =>
              have h72_val := h1_7half hcut72
              exact err_sub_wsq_le_on hw_hi ha72 ha5 (by unfold sq; grind) (by unfold sq; grind)
            | inr hcut72 =>
              have hcut_val : e2m1ErrSq 1 M_cut = sq (M_cut - 4) := e2m1ErrSq_1_on_7half_5 hcut72 hcut_hi
              rw [hcut_val] at h1_cut
              exact err_sub_wsq_le_on hw_hi hge_cut ha5 (by grind) (by unfold sq; grind)
          | inr ha5 =>
            rw [e2m1ErrSq_1_on_ge_5 ha5]
            exact err_sub_wsq_le_on hw_hi ha5 hM_hi (by unfold sq; grind) h6
      have hsum := block_sum_bound_with_pivot (fun u => e2m1ErrSq 1 u - w * sq u)
        ((1 - w) / 16) (-(((B - 1 : Nat) : Rat) * ((1 - w) / 16))) x hall ⟨M, hM_mem, hpivot⟩
      rw [hx_len] at hsum
      grind
    grind

/-- Parameterized Lagrangian theorem (Regimes 2 and 3): with `λ₀ = (3/4)*(1 - w)` and `M_cut ∈ [5, 6]`,
    uses `λ₀` on `M ∈ [3, M_cut]` and `s = 1` on `M ∈ [M_cut, 6]`. -/
theorem opt_e8m0_bound_of_lam0 (B : Nat) (w M_cut : Rat)
    (hw_lo : (1 / 10 : Rat) ≤ w) (hw_hi : w ≤ 1)
    (hcut_lo : (5 : Rat) ≤ M_cut) (hcut_hi : M_cut ≤ 6)
    (hB_nonneg : (0 : Rat) ≤ ((B - 1 : Nat) : Rat))
    -- On [3, M_cut], f_{lam0}(M) <= - (B-1)*(1-w)/64 at breakpoints {3, 7/2, 5, M_cut}:
    (hlam_3 : -9 * w + ((B - 1 : Nat) : Rat) * ((1 - w) / 64) ≤ 0)
    (_hlam_72 : (1 / 4 : Rat) - (49 / 4) * w + ((B - 1 : Nat) : Rat) * ((1 - w) / 64) ≤ 0)
    (hlam_5 : (1 - (3 / 4 : Rat) * (1 - w)) * 1 + ((3 / 4 : Rat) * (1 - w)) * 4 - 25 * w +
        ((B - 1 : Nat) : Rat) * ((1 - w) / 64) ≤ 0)
    (hlam_cut : (1 - (3 / 4 : Rat) * (1 - w)) * sq (M_cut - 6) +
        ((3 / 4 : Rat) * (1 - w)) * sq (M_cut - 3) - w * sq M_cut +
        ((B - 1 : Nat) : Rat) * ((1 - w) / 64) ≤ 0)
    -- On [M_cut, 6], s = 1 works at M_cut:
    (h1_cut : sq (M_cut - 6) - w * sq M_cut + ((B - 1 : Nat) : Rat) * ((1 - w) / 16) ≤ 0)
    (x : List Rat) (hx_len : x.length = B)
    (hx_max : ∃ M ∈ x, 3 ≤ absRat M ∧ absRat M ≤ 6 ∧ ∀ u ∈ x, absRat u ≤ absRat M) :
    min (blockErrSq 1 x) (blockErrSq (1 / 2) x) ≤ w * blockEnergy x := by
  rcases hx_max with ⟨M, hM_mem, hM_lo, hM_hi, hM_all⟩
  cases Rat.le_total (a := absRat M) (b := M_cut) with
  | inl hle_cut =>
    let lam := (3 / 4 : Rat) * (1 - w)
    have hlam0 : (0 : Rat) ≤ lam := by grind
    have hlam1 : lam ≤ 1 := by grind
    apply rat_min_le_of_convex hlam0 hlam1
    apply rat_le_of_sub_nonneg
    have hsub : (1 - lam) * blockErrSq 1 x + lam * blockErrSq (1 / 2) x - w * blockEnergy x ≤ 0 := by
      rw [convex_blockErrSq_sub_wEnergy_eq_foldr]
      have hflam_on_3_cut : ∀ u : Rat, 3 ≤ absRat u → absRat u ≤ M_cut →
          (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (1 / 2) u - w * sq u ≤
            -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) := by
        intro u hu3 hucut
        let a := absRat u
        rw [← e2m1ErrSq_abs 1 u, ← e2m1ErrSq_abs (1 / 2) u, ← sq_absRat u]
        have hehalf : e2m1ErrSq (1 / 2) a = sq (a - 3) := by
          have htop := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := a) (by grind)
            (by rw [absRat_of_nonneg (Rat.le_trans (by grind) hu3)]; grind)
          rw [absRat_of_nonneg (Rat.le_trans (by grind) hu3)] at htop
          have hid : (1 / 2 : Rat) * 6 = 3 := by grind
          rw [hid] at htop; exact htop
        rw [hehalf]
        have hquad_le : ∀ q l r : Rat, l ≤ a → a ≤ r →
            (1 - lam) * sq (l - q) + lam * sq (l - 3) - w * sq l ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) →
            (1 - lam) * sq (r - q) + lam * sq (r - 3) - w * sq r ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) →
            (1 - lam) * sq (a - q) + lam * sq (a - 3) - w * sq a ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) := by
          intro q l r hl hr hfl hfr
          have hquad_eq : ∀ t : Rat,
              (1 - w) * (t * t) + (-2 * ((1 - lam) * q + lam * 3)) * t +
                ((1 - lam) * (q * q) + lam * 9) =
              (1 - lam) * sq (t - q) + lam * sq (t - 3) - w * sq t := by
            intro t; unfold sq; grind
          have hc := convex_quad_le_of_endpoints (rat_sub_nonneg hw_hi) hl hr
            (by rw [hquad_eq]; exact hfl) (by rw [hquad_eq]; exact hfr)
          rw [hquad_eq] at hc; exact hc
        cases Rat.le_total (a := a) (b := (7 / 2 : Rat)) with
        | inl ha72 =>
          rw [e2m1ErrSq_1_on_3_7half hu3 ha72]
          exact hquad_le 3 3 (7 / 2) hu3 ha72 (by unfold sq; grind) (by unfold sq; grind)
        | inr ha72 =>
          cases Rat.le_total (a := a) (b := (5 : Rat)) with
          | inl ha5 =>
            rw [e2m1ErrSq_1_on_7half_5 ha72 ha5]
            exact hquad_le 4 (7 / 2) 5 ha72 ha5 (by unfold sq; grind) (by unfold sq; grind)
          | inr ha5 =>
            rw [e2m1ErrSq_1_on_ge_5 ha5]
            exact hquad_le 6 5 M_cut ha5 hucut (by unfold sq; grind) (by grind)
      have hpivot := hflam_on_3_cut M hM_lo hle_cut
      have hall : ∀ u ∈ x, (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (1 / 2) u - w * sq u ≤ (1 - w) / 64 := by
        intro u hu
        cases Rat.le_total (a := absRat u) (b := (3 : Rat)) with
        | inl hle3 => exact lam0_bulk_le3 hw_lo hw_hi hle3
        | inr hge3 =>
          have h1 := hflam_on_3_cut u hge3 (Rat.le_trans (hM_all u hu) hle_cut)
          have h2 : -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) ≤ (1 - w) / 64 := by
            have : (0 : Rat) ≤ ((B - 1 : Nat) : Rat) * ((1 - w) / 64) :=
              Rat.mul_nonneg hB_nonneg (by grind)
            grind
          exact Rat.le_trans h1 h2
      have hsum := block_sum_bound_with_pivot
        (fun u => (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (1 / 2) u - w * sq u)
        ((1 - w) / 64) (-(((B - 1 : Nat) : Rat) * ((1 - w) / 64))) x hall ⟨M, hM_mem, hpivot⟩
      rw [hx_len] at hsum; grind
    grind
  | inr hge_cut =>
    -- Use s = 1!
    apply Rat.le_trans (rat_min_le_left _ _)
    apply rat_le_of_sub_nonneg
    have hsub : blockErrSq 1 x - w * blockEnergy x ≤ 0 := by
      rw [blockErrSq_sub_wEnergy_eq_foldr]
      have hall : ∀ u ∈ x, e2m1ErrSq 1 u - w * sq u ≤ (1 - w) / 16 := by
        intro u hu
        exact e1_sub_wsq_le (Rat.le_trans (by grind) hw_lo) hw_hi (Rat.le_trans (hM_all u hu) hM_hi)
      have hpivot : e2m1ErrSq 1 M - w * sq M ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 16)) := by
        rw [← e2m1ErrSq_abs, ← sq_absRat M]
        have ha5 : (5 : Rat) ≤ absRat M := Rat.le_trans hcut_lo hge_cut
        rw [e2m1ErrSq_1_on_ge_5 ha5]
        have h6 : sq ((6 : Rat) - 6) - w * sq 6 ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 16)) := by
          have hcut_sq : (0 : Rat) ≤ sq (M_cut - 6) := rat_sq_nonneg _
          have hM6 : sq M_cut ≤ sq 6 := sq_le_sq_of_abs_le (by grind) hcut_hi
          have hw0 : (0 : Rat) ≤ w := Rat.le_trans (by grind) hw_lo
          have hmul := rat_mul_le_mul_of_nonneg_left hM6 hw0
          unfold sq at *; grind
        exact err_sub_wsq_le_on hw_hi hge_cut hM_hi (by grind) h6
      have hsum := block_sum_bound_with_pivot (fun u => e2m1ErrSq 1 u - w * sq u)
        ((1 - w) / 16) (-(((B - 1 : Nat) : Rat) * ((1 - w) / 16))) x hall ⟨M, hM_mem, hpivot⟩
      rw [hx_len] at hsum; grind
    grind

/-- Exact evaluation helpers for the 3 attainment witnesses of Theorem 2. -/
theorem e2m1ErrSq_1_at_quarter : e2m1ErrSq 1 (1 / 4) = 1 / 16 := by
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_0 1 (1 / 4); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]
    unfold sq
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    grind

theorem e2m1ErrSq_half_at_quarter : e2m1ErrSq (1 / 2) (1 / 4) = 0 := by
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_half (1 / 2) (1 / 4); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · exact e2m1ErrSq_nonneg _ _

theorem e2m1ErrSq_1_at_eighth : e2m1ErrSq 1 (1 / 8) = 1 / 64 := by
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_0 1 (1 / 8); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]
    unfold sq
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    grind

theorem e2m1ErrSq_half_at_eighth : e2m1ErrSq (1 / 2) (1 / 8) = 1 / 64 := by
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_0 (1 / 2) (1 / 8); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]
    unfold sq
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    apply rat_le_min (by grind)
    grind

theorem e2m1ErrSq_1_at_5 : e2m1ErrSq 1 5 = 1 := by
  rw [e2m1ErrSq_1_on_ge_5 (by grind)]; unfold sq; grind

theorem e2m1ErrSq_half_at_5 : e2m1ErrSq (1 / 2) 5 = 4 := by
  have htop := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := 5) (by grind)
    (by rw [absRat_of_nonneg (by grind)]; grind)
  rw [absRat_of_nonneg (by grind)] at htop
  rw [htop]; unfold sq; grind

theorem e2m1ErrSq_1_at_3 : e2m1ErrSq 1 3 = 0 := by
  rw [e2m1ErrSq_1_on_3_7half (by grind) (by grind)]; unfold sq; grind

theorem e2m1ErrSq_half_at_3 : e2m1ErrSq (1 / 2) 3 = 0 := by
  have htop := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := 3) (by grind)
    (by rw [absRat_of_nonneg (by grind)]; grind)
  rw [absRat_of_nonneg (by grind)] at htop
  rw [htop]; unfold sq; grind

/-- Universal all-`B` upper bound for `opt-E8M0` MXFP4. -/
theorem opt_e8m0_universal_upper_bound (B : Nat) (hB : 1 ≤ B) (x : List Rat)
    (hx_len : x.length = B)
    (hx_max : ∃ M ∈ x, 3 ≤ absRat M ∧ absRat M ≤ 6 ∧ ∀ u ∈ x, absRat u ≤ absRat M) :
    min (blockErrSq 1 x) (blockErrSq (1 / 2) x) ≤ omegaOptE8M0 B * blockEnergy x := by
  have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
  by_cases h49 : B ≤ 49
  · -- Regime 1: 1 ≤ B ≤ 49, w = (B + 15)/(B + 399)
    have hw_eq : omegaOptE8M0 B = ((B : Rat) + 15) / ((B : Rat) + 399) := by
      unfold omegaOptE8M0; simp only [h49, ite_true]
    rw [hw_eq]
    let b : Rat := (B : Rat)
    have hb1 : (1 : Rat) ≤ b := rat_natCast_le hB
    have hb49 : b ≤ 49 := rat_natCast_le h49
    have hden : (0 : Rat) < b + 399 := by grind
    let w : Rat := (b + 15) / (b + 399)
    have hw_mul : w * (b + 399) = b + 15 := rat_div_mul_cancel (Rat.ne_of_gt hden)
    have hw_lo : (1 / 25 : Rat) ≤ w :=
      rat_le_div_of_mul_le hden (by grind)
    have hw_hi : w ≤ 1 :=
      rat_div_le_of_mul_le hden (by grind)
    have h1_5 : 1 - w * 25 + ((B - 1 : Nat) : Rat) * ((1 - w) / 16) ≤ 0 := by
      rw [hBcast]
      have hmul : (1 - w * 25 + (b - 1) * ((1 - w) / 16)) * (b + 399) = 0 := by grind
      have hpos : (0 : Rat) < b + 399 := hden
      have h0 : 1 - w * 25 + (b - 1) * ((1 - w) / 16) = 0 := by
        cases Rat.mul_eq_zero.mp hmul with
        | inl h => exact h
        | inr h => exact False.elim (Rat.ne_of_gt hpos h)
      rw [h0]; exact Rat.le_refl
    by_cases h9 : B ≤ 9
    · have hb9 : b ≤ 9 := rat_natCast_le h9
      exact opt_e8m0_bound_of_cut B w 3 hw_lo hw_hi (by grind) (by grind)
        (rat_le_of_clear hden (poly := -9 * (b + 15) - 6) (by unfold sq; grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -9 * (b + 15) + 6 * (b - 1)) (by unfold sq; grind) (by grind))
        (by rw [e2m1ErrSq_1_at_3, hBcast]; exact rat_le_zero_of_clear hden (poly := -9 * (b + 15) + 24 * (b - 1)) (by unfold sq; grind) (by grind))
        (fun _ => by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (1 / 4) * (b + 399) - (49 / 4) * (b + 15) + 24 * (b - 1)) (by grind) (by grind))
        (fun _ => by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -16 * (b + 15) + 24 * (b - 1)) (by grind) (by grind))
        h1_5 x hx_len hx_max
    · by_cases h16 : B ≤ 16
      · have hb10 : (10 : Rat) ≤ b := rat_natCast_le (by omega : 10 ≤ B)
        have hb16 : b ≤ 16 := rat_natCast_le h16
        have hecut : e2m1ErrSq 1 (15 / 4) = 1 / 16 := by
          rw [e2m1ErrSq_1_on_7half_5 (by grind) (by grind)]; unfold sq; grind
        exact opt_e8m0_bound_of_cut B w (15 / 4) hw_lo hw_hi (by grind) (by grind)
          (rat_le_of_clear hden (poly := (9 / 16) * (b + 399) - (225 / 16) * (b + 15) - 6) (by unfold sq; grind) (by grind))
          (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (9 / 16) * (b + 399) - (225 / 16) * (b + 15) + 6 * (b - 1)) (by unfold sq; grind) (by grind))
          (by rw [hecut, hBcast]; exact rat_le_zero_of_clear hden (poly := (1 / 16) * (b + 399) - (225 / 16) * (b + 15) + 24 * (b - 1)) (by unfold sq; grind) (by grind))
          (fun h => by grind)
          (fun _ => by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -16 * (b + 15) + 24 * (b - 1)) (by grind) (by grind))
          h1_5 x hx_len hx_max
      · by_cases h33 : B ≤ 33
        · have hb17 : (17 : Rat) ≤ b := rat_natCast_le (by omega : 17 ≤ B)
          have hb33 : b ≤ 33 := rat_natCast_le h33
          have hecut : e2m1ErrSq 1 4 = 0 := by
            rw [e2m1ErrSq_1_on_7half_5 (by grind) (by grind)]; unfold sq; grind
          exact opt_e8m0_bound_of_cut B w 4 hw_lo hw_hi (by grind) (by grind)
            (rat_le_of_clear hden (poly := (b + 399) - 16 * (b + 15) - 6) (by unfold sq; grind) (by grind))
            (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (b + 399) - 16 * (b + 15) + 6 * (b - 1)) (by unfold sq; grind) (by grind))
            (by rw [hecut, hBcast]; exact rat_le_zero_of_clear hden (poly := -16 * (b + 15) + 24 * (b - 1)) (by unfold sq; grind) (by grind))
            (fun h => by grind)
            (fun _ => by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -16 * (b + 15) + 24 * (b - 1)) (by grind) (by grind))
            h1_5 x hx_len hx_max
        · by_cases h45 : B ≤ 45
          · have hb34 : (34 : Rat) ≤ b := rat_natCast_le (by omega : 34 ≤ B)
            have hb45 : b ≤ 45 := rat_natCast_le h45
            have hecut : e2m1ErrSq 1 (17 / 4) = 1 / 16 := by
              rw [e2m1ErrSq_1_on_7half_5 (by grind) (by grind)]; unfold sq; grind
            exact opt_e8m0_bound_of_cut B w (17 / 4) hw_lo hw_hi (by grind) (by grind)
              (rat_le_of_clear hden (poly := (25 / 16) * (b + 399) - (289 / 16) * (b + 15) - 6) (by unfold sq; grind) (by grind))
              (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (25 / 16) * (b + 399) - (289 / 16) * (b + 15) + 6 * (b - 1)) (by unfold sq; grind) (by grind))
              (by rw [hecut, hBcast]; exact rat_le_zero_of_clear hden (poly := (1 / 16) * (b + 399) - (289 / 16) * (b + 15) + 24 * (b - 1)) (by unfold sq; grind) (by grind))
              (fun h => by grind)
              (fun h => by grind)
              h1_5 x hx_len hx_max
          · by_cases h48 : B ≤ 48
            · have hb46 : (46 : Rat) ≤ b := rat_natCast_le (by omega : 46 ≤ B)
              have hb48 : b ≤ 48 := rat_natCast_le h48
              have hecut : e2m1ErrSq 1 (35 / 8) = 9 / 64 := by
                rw [e2m1ErrSq_1_on_7half_5 (by grind) (by grind)]; unfold sq; grind
              exact opt_e8m0_bound_of_cut B w (35 / 8) hw_lo hw_hi (by grind) (by grind)
                (rat_le_of_clear hden (poly := (121 / 64) * (b + 399) - (1225 / 64) * (b + 15) - 6) (by unfold sq; grind) (by grind))
                (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (121 / 64) * (b + 399) - (1225 / 64) * (b + 15) + 6 * (b - 1)) (by unfold sq; grind) (by grind))
                (by rw [hecut, hBcast]; exact rat_le_zero_of_clear hden (poly := (9 / 64) * (b + 399) - (1225 / 64) * (b + 15) + 24 * (b - 1)) (by unfold sq; grind) (by grind))
                (fun h => by grind)
                (fun h => by grind)
                h1_5 x hx_len hx_max
            · have hb49_eq : B = 49 := by omega
              subst hb49_eq
              have hecut : e2m1ErrSq 1 (9 / 2) = 1 / 4 := by
                rw [e2m1ErrSq_1_on_7half_5 (by grind) (by grind)]; unfold sq; grind
              exact opt_e8m0_bound_of_cut 49 w (9 / 2) hw_lo hw_hi (by grind) (by grind)
                (rat_le_of_clear hden (poly := (9 / 4) * (b + 399) - (81 / 4) * (b + 15) - 6) (by unfold sq; grind) (by grind))
                (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (9 / 4) * (b + 399) - (81 / 4) * (b + 15) + 6 * (b - 1)) (by unfold sq; grind) (by grind))
                (by rw [hecut, hBcast]; exact rat_le_zero_of_clear hden (poly := (1 / 4) * (b + 399) - (81 / 4) * (b + 15) + 24 * (b - 1)) (by unfold sq; grind) (by grind))
                (fun h => by grind)
                (fun h => by grind)
                h1_5 x hx_len hx_max
  · by_cases h145 : B ≤ 145
    · -- Regime 2: 50 ≤ B ≤ 145
      have hw_eq : omegaOptE8M0 B =
          (((B : Rat) + 143) * ((B : Rat) + 143)) / ((B : Rat) * (B : Rat) + 1438 * (B : Rat) + 185185) := by
        unfold omegaOptE8M0; simp only [h49, h145, ite_false, ite_true]
      rw [hw_eq]
      let b : Rat := (B : Rat)
      have hb50 : (50 : Rat) ≤ b := rat_natCast_le (by omega : 50 ≤ B)
      have hb145 : b ≤ 145 := rat_natCast_le h145
      let D : Rat := b * b + 1438 * b + 185185
      have hD : (0 : Rat) < D := by
        have hb0 : (0 : Rat) ≤ b := Rat.le_trans (by grind) hb50
        have hb2 : (0 : Rat) ≤ b * b := Rat.mul_nonneg hb0 hb0
        grind
      let w : Rat := ((b + 143) * (b + 143)) / D
      have hw_mul : w * D = (b + 143) * (b + 143) := rat_div_mul_cancel (Rat.ne_of_gt hD)
      have hw_lo : (1 / 10 : Rat) ≤ w := by
        apply rat_le_div_of_mul_le hD
        have hb2 : (0 : Rat) ≤ b * b := rat_sq_nonneg b
        grind
      have hw_hi : w ≤ 1 := by
        apply rat_div_le_of_mul_le hD
        have hb0 : (0 : Rat) ≤ b := Rat.le_trans (by grind) hb50
        grind
      let M_cut : Rat := (b + 431) / 96
      have hcut_lo : (5 : Rat) ≤ M_cut := by grind
      have hcut_hi : M_cut ≤ 6 := by grind
      exact opt_e8m0_bound_of_lam0 B w M_cut hw_lo hw_hi hcut_lo hcut_hi
        (rat_natCast_nonneg (B - 1))
        (by rw [hBcast]
            apply rat_le_zero_of_clear hD (poly := 9 * (b - 145) * (b + 143)) (by grind)
            have h1 : (0 : Rat) ≤ (145 - b) * (b + 143) := Rat.mul_nonneg (by grind) (by grind)
            grind)
        (by rw [hBcast]
            apply rat_le_zero_of_clear hD (poly := 6 * (b - 241) * (b + 143)) (by grind)
            have h1 : (0 : Rat) ≤ (241 - b) * (b + 143) := Rat.mul_nonneg (by grind) (by grind)
            grind)
        (by rw [hBcast]
            apply rat_le_zero_of_clear hD (poly := -6 * (b - 49) * (b + 143)) (by grind)
            have h1 : (0 : Rat) ≤ (b - 49) * (b + 143) := Rat.mul_nonneg (by grind) (by grind)
            grind)
        (by rw [hBcast]; exact rat_le_zero_of_clear hD (poly := 0) (by unfold sq; grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hD (poly := 0) (by unfold sq; grind) (by grind))
        x hx_len hx_max
    · -- Regime 3: B ≥ 146, w = (B - 1)/(B + 575), M_cut = 6
      have hw_eq : omegaOptE8M0 B = ((B : Rat) - 1) / ((B : Rat) + 575) := by
        unfold omegaOptE8M0; simp only [h49, h145, ite_false]
      rw [hw_eq]
      let b : Rat := (B : Rat)
      have hb146 : (146 : Rat) ≤ b := rat_natCast_le (by omega : 146 ≤ B)
      have hden : (0 : Rat) < b + 575 := by grind
      let w : Rat := (b - 1) / (b + 575)
      have hw_mul : w * (b + 575) = b - 1 := rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw_lo : (1 / 10 : Rat) ≤ w := rat_le_div_of_mul_le hden (by grind)
      have hw_hi : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      exact opt_e8m0_bound_of_lam0 B w 6 hw_lo hw_hi (by grind) (by grind)
        (rat_natCast_nonneg (B - 1))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (1 / 4) * (b + 575) - (49 / 4) * (b - 1) + 9 * (b - 1)) (by grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (13 / 4) * (b + 575) - (109 / 4) * (b - 1) + 9 * (b - 1)) (by grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := (27 / 4) * (b + 575) - (171 / 4) * (b - 1) + 9 * (b - 1)) (by unfold sq; grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by unfold sq; grind) (by grind))
        x hx_len hx_max

/-- Theorem 2: Exact MXFP4 `opt-E8M0` All-`B` Three-Regime EF21 Minimax Law. -/
theorem mxfp4_opt_e8m0_all_b_ef21_three_regime_law :
    (∀ (B : Nat) (x : List Rat), 1 ≤ B → x.length = B →
      (∃ M ∈ x, 3 ≤ absRat M ∧ absRat M ≤ 6 ∧ ∀ u ∈ x, absRat u ≤ absRat M) →
      min (blockErrSq 1 x) (blockErrSq (1 / 2) x) ≤ omegaOptE8M0 B * blockEnergy x) ∧
    (∀ B : Nat, 1 ≤ B → B ≤ 49 →
      let x := mkSingleOutlierBlock B 5 (1 / 4)
      x.length = B ∧
      blockErrSq 1 x ≤ blockErrSq (1 / 2) x ∧
      min (blockErrSq 1 x) (blockErrSq (1 / 2) x) = omegaOptE8M0 B * blockEnergy x) ∧
    (∀ B : Nat, 49 < B → B ≤ 145 →
      let x := mkSingleOutlierBlock B (((B : Rat) + 431) / 96) (1 / 4)
      x.length = B ∧
      blockErrSq 1 x = blockErrSq (1 / 2) x ∧
      min (blockErrSq 1 x) (blockErrSq (1 / 2) x) = omegaOptE8M0 B * blockEnergy x) ∧
    (∀ B : Nat, 145 ≤ B →
      let x := mkSingleOutlierBlock B 3 (1 / 8)
      x.length = B ∧
      blockErrSq 1 x = blockErrSq (1 / 2) x ∧
      min (blockErrSq 1 x) (blockErrSq (1 / 2) x) = omegaOptE8M0 B * blockEnergy x) ∧
    (omegaOptE8M0 32 = 47 / 431 ∧
     omegaOptE8M0 64 = 23 / 151 ∧
     omegaOptE8M0 145 = 1 / 5 ∧
     (162 / 100 : Rat) * omegaOptE8M0 32 < 31 / 175 ∧
     (199 / 100 : Rat) * omegaOptE8M0 64 < 7 / 23 ∧
     (5 / 2 : Rat) * omegaOptE8M0 145 = 1 / 2) := by
  refine ⟨fun B x hB hlen hmax => opt_e8m0_universal_upper_bound B hB x hlen hmax, ?_, ?_, ?_, ?_⟩
  · intro B hB h49
    dsimp only [mkSingleOutlierBlock]
    have hlen : (5 :: List.replicate (B - 1) (1 / 4 : Rat)).length = B := by
      simp; omega
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    have he1 : blockErrSq 1 (5 :: List.replicate (B - 1) (1 / 4 : Rat)) = 1 + ((B : Rat) - 1) / 16 := by
      simp only [blockErrSq, blockErrSq_replicate, e2m1ErrSq_1_at_5, e2m1ErrSq_1_at_quarter, hBcast]; grind
    have he2 : blockErrSq (1 / 2) (5 :: List.replicate (B - 1) (1 / 4 : Rat)) = 4 := by
      simp only [blockErrSq, blockErrSq_replicate, e2m1ErrSq_half_at_5, e2m1ErrSq_half_at_quarter]; grind
    have hen : blockEnergy (5 :: List.replicate (B - 1) (1 / 4 : Rat)) = 25 + ((B : Rat) - 1) / 16 := by
      simp only [blockEnergy, blockEnergy_replicate, hBcast]; unfold sq; grind
    have hb49 : (B : Rat) ≤ 49 := rat_natCast_le h49
    have hle : blockErrSq 1 (5 :: List.replicate (B - 1) (1 / 4 : Rat)) ≤
        blockErrSq (1 / 2) (5 :: List.replicate (B - 1) (1 / 4 : Rat)) := by
      rw [he1, he2]; grind
    refine ⟨hlen, hle, ?_⟩
    rw [rat_min_eq_left hle, he1, hen]
    unfold omegaOptE8M0; simp only [h49, ite_true]
    have hden : ((B : Rat) + 399) ≠ 0 := by
      have : (0 : Rat) ≤ (B : Rat) := rat_natCast_nonneg B; grind
    have hmul := rat_div_mul_cancel (a := (B : Rat) + 15) hden
    grind
  · intro B h49 h145
    dsimp only [mkSingleOutlierBlock]
    have hB : 1 ≤ B := by omega
    have hlen : ((((B : Rat) + 431) / 96) :: List.replicate (B - 1) (1 / 4 : Rat)).length = B := by
      simp; omega
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    let M : Rat := (b + 431) / 96
    have hb50 : (50 : Rat) ≤ b := rat_natCast_le (by omega : 50 ≤ B)
    have hb145 : b ≤ 145 := rat_natCast_le h145
    have hM5 : (5 : Rat) ≤ M := by grind
    have hM6 : M ≤ 6 := by grind
    have he1M : e2m1ErrSq 1 M = sq (M - 6) := e2m1ErrSq_1_on_ge_5 hM5
    have he2M : e2m1ErrSq (1 / 2) M = sq (M - 3) := by
      have htop := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := M) (by grind)
        (by rw [absRat_of_nonneg (by grind)]; grind)
      rw [absRat_of_nonneg (by grind)] at htop
      have hid : (1 / 2 : Rat) * 6 = 3 := by grind
      rw [hid] at htop; exact htop
    have he1 : blockErrSq 1 (M :: List.replicate (B - 1) (1 / 4 : Rat)) = sq (M - 6) + (b - 1) / 16 := by
      simp only [blockErrSq, blockErrSq_replicate, he1M, e2m1ErrSq_1_at_quarter, hBcast]; grind
    have he2 : blockErrSq (1 / 2) (M :: List.replicate (B - 1) (1 / 4 : Rat)) = sq (M - 3) := by
      simp only [blockErrSq, blockErrSq_replicate, he2M, e2m1ErrSq_half_at_quarter]; grind
    have hen : blockEnergy (M :: List.replicate (B - 1) (1 / 4 : Rat)) = sq M + (b - 1) / 16 := by
      simp only [blockEnergy, blockEnergy_replicate, hBcast]; unfold sq; grind
    have htie : blockErrSq 1 (M :: List.replicate (B - 1) (1 / 4 : Rat)) =
        blockErrSq (1 / 2) (M :: List.replicate (B - 1) (1 / 4 : Rat)) := by
      rw [he1, he2]; unfold sq; grind
    refine ⟨hlen, htie, ?_⟩
    rw [rat_min_eq_left (by rw [htie]; exact Rat.le_refl), he1, hen]
    unfold omegaOptE8M0
    have hnot49 : ¬ B ≤ 49 := by omega
    simp only [hnot49, h145, ite_false, ite_true]
    have hD : b * b + 1438 * b + 185185 ≠ 0 := by
      have hb0 : (0 : Rat) ≤ b := Rat.le_trans (by grind) hb50
      have hb2 : (0 : Rat) ≤ b * b := Rat.mul_nonneg hb0 hb0
      grind
    have hmul := rat_div_mul_cancel (a := (b + 143) * (b + 143)) hD
    unfold sq; grind
  · intro B h145
    dsimp only [mkSingleOutlierBlock]
    have hB : 1 ≤ B := by omega
    have hlen : ((3 : Rat) :: List.replicate (B - 1) (1 / 8 : Rat)).length = B := by
      simp; omega
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have he1 : blockErrSq 1 ((3 : Rat) :: List.replicate (B - 1) (1 / 8 : Rat)) = (b - 1) / 64 := by
      simp only [blockErrSq, blockErrSq_replicate, e2m1ErrSq_1_at_3, e2m1ErrSq_1_at_eighth, hBcast]; grind
    have he2 : blockErrSq (1 / 2) ((3 : Rat) :: List.replicate (B - 1) (1 / 8 : Rat)) = (b - 1) / 64 := by
      simp only [blockErrSq, blockErrSq_replicate, e2m1ErrSq_half_at_3, e2m1ErrSq_half_at_eighth, hBcast]; grind
    have hen : blockEnergy ((3 : Rat) :: List.replicate (B - 1) (1 / 8 : Rat)) = 9 + (b - 1) / 64 := by
      simp only [blockEnergy, blockEnergy_replicate, hBcast]; unfold sq; grind
    have htie : blockErrSq 1 ((3 : Rat) :: List.replicate (B - 1) (1 / 8 : Rat)) =
        blockErrSq (1 / 2) ((3 : Rat) :: List.replicate (B - 1) (1 / 8 : Rat)) := by
      rw [he1, he2]
    refine ⟨hlen, htie, ?_⟩
    rw [rat_min_eq_left (by rw [htie]; exact Rat.le_refl), he1, hen]
    by_cases h145_eq : B = 145
    · subst h145_eq
      unfold omegaOptE8M0; simp; grind
    · have hnot49 : ¬ B ≤ 49 := by omega
      have hnot145 : ¬ B ≤ 145 := by omega
      unfold omegaOptE8M0; simp only [hnot49, hnot145, ite_false]
      have hden : b + 575 ≠ 0 := by
        have : (0 : Rat) ≤ b := rat_natCast_nonneg B; grind
      have hmul := rat_div_mul_cancel (a := b - 1) hden
      grind
  · have h32 : omegaOptE8M0 32 = 47 / 431 := by unfold omegaOptE8M0; simp; grind
    have h64 : omegaOptE8M0 64 = 23 / 151 := by unfold omegaOptE8M0; simp; grind
    have h145 : omegaOptE8M0 145 = 1 / 5 := by unfold omegaOptE8M0; simp; grind
    refine ⟨h32, h64, h145, ?_, ?_, ?_⟩
    · rw [h32]; grind
    · rw [h64]; grind
    · rw [h145]; grind

/-! ### Helper Lemmas and Proof for Theorem 5 (`opt-E8M0` never drops two exponents) -/

theorem e2m1ErrSq_half_le_1_64 {u : Rat} (hu : absRat u ≤ 1) :
    e2m1ErrSq (1 / 2) u ≤ 1 / 64 := by
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  have hbound : ∀ q : Rat, e2m1ErrSq (1 / 2) u ≤ sq (a - q) →
      -(1 / 8 : Rat) ≤ a - q → a - q ≤ 1 / 8 → e2m1ErrSq (1 / 2) u ≤ 1 / 64 := by
    intro q hle hlo hhi
    have hsq : sq (a - q) ≤ 1 / 64 := by
      have h1 : (0 : Rat) ≤ (1 / 8 - (a - q)) * (1 / 8 + (a - q)) :=
        Rat.mul_nonneg (by grind) (by grind)
      unfold sq; grind
    exact Rat.le_trans hle hsq
  cases Rat.le_total (a := a) (b := (1 / 8 : Rat)) with
  | inl h1 => exact hbound 0 (e2m1ErrSq_le_0 (1 / 2) u) (by grind) (by grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (3 / 8 : Rat)) with
    | inl h2 => exact hbound (1 / 4) (by have := e2m1ErrSq_le_half (1 / 2) u; grind) (by grind) (by grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (5 / 8 : Rat)) with
      | inl h3 => exact hbound (1 / 2) (by have := e2m1ErrSq_le_1 (1 / 2) u; grind) (by grind) (by grind)
      | inr h3 =>
        cases Rat.le_total (a := a) (b := (7 / 8 : Rat)) with
        | inl h4 => exact hbound (3 / 4) (by have := e2m1ErrSq_le_3half (1 / 2) u; grind) (by grind) (by grind)
        | inr h4 => exact hbound 1 (by have := e2m1ErrSq_le_2 (1 / 2) u; grind) (by grind) (by grind)

theorem e2m1ErrSq_half_le_1_16 {u : Rat} (hu : absRat u ≤ 2) :
    e2m1ErrSq (1 / 2) u ≤ 1 / 16 := by
  cases Rat.le_total (a := absRat u) (b := (1 : Rat)) with
  | inl h1 => exact Rat.le_trans (e2m1ErrSq_half_le_1_64 h1) (by grind)
  | inr h1 =>
    let a := absRat u
    have hbound : ∀ q : Rat, e2m1ErrSq (1 / 2) u ≤ sq (a - q) →
        -(1 / 4 : Rat) ≤ a - q → a - q ≤ 1 / 4 → e2m1ErrSq (1 / 2) u ≤ 1 / 16 := by
      intro q hle hlo hhi
      have hsq : sq (a - q) ≤ 1 / 16 := by
        have h1 : (0 : Rat) ≤ (1 / 4 - (a - q)) * (1 / 4 + (a - q)) :=
          Rat.mul_nonneg (by grind) (by grind)
        unfold sq; grind
      exact Rat.le_trans hle hsq
    cases Rat.le_total (a := a) (b := (5 / 4 : Rat)) with
    | inl h2 => exact hbound 1 (by have := e2m1ErrSq_le_2 (1 / 2) u; grind) (by grind) (by grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (7 / 4 : Rat)) with
      | inl h3 => exact hbound (3 / 2) (by have := e2m1ErrSq_le_3 (1 / 2) u; grind) (by grind) (by grind)
      | inr h3 => exact hbound 2 (by have := e2m1ErrSq_le_4 (1 / 2) u; grind) (by grind) (by grind)

theorem e2m1ErrSq_half_le_1_4 {u : Rat} (hu : absRat u ≤ 3) :
    e2m1ErrSq (1 / 2) u ≤ 1 / 4 := by
  cases Rat.le_total (a := absRat u) (b := (2 : Rat)) with
  | inl h2 => exact Rat.le_trans (e2m1ErrSq_half_le_1_16 h2) (by grind)
  | inr h2 =>
    let a := absRat u
    have hbound : ∀ q : Rat, e2m1ErrSq (1 / 2) u ≤ sq (a - q) →
        -(1 / 2 : Rat) ≤ a - q → a - q ≤ 1 / 2 → e2m1ErrSq (1 / 2) u ≤ 1 / 4 := by
      intro q hle hlo hhi
      have hsq : sq (a - q) ≤ 1 / 4 := by
        have h1 : (0 : Rat) ≤ (1 / 2 - (a - q)) * (1 / 2 + (a - q)) :=
          Rat.mul_nonneg (by grind) (by grind)
        unfold sq; grind
      exact Rat.le_trans hle hsq
    cases Rat.le_total (a := a) (b := (5 / 2 : Rat)) with
    | inl h3 => exact hbound 2 (by have := e2m1ErrSq_le_4 (1 / 2) u; grind) (by grind) (by grind)
    | inr h3 => exact hbound 3 (by have := e2m1ErrSq_le_6 (1 / 2) u; grind) (by grind) (by grind)

theorem blockErrSq_le_len_mul {s C : Rat} (l : List Rat) (h : ∀ u ∈ l, e2m1ErrSq s u ≤ C) :
    blockErrSq s l ≤ (l.length : Rat) * C := by
  induction l with
  | nil => simp [blockErrSq]
  | cons u xs ih =>
    simp only [blockErrSq, List.length_cons, Rat.natCast_add]
    have hu := h u (List.Mem.head _)
    have hxs := ih (fun v hv => h v (List.Mem.tail _ hv))
    have hadd := rat_add_le_add hu hxs
    grind

/-- Theorem 5: Exact Dominance Theorem — Why `opt-E8M0` Never Drops Two Exponents (`e ≤ e_ceil - 2`). -/
theorem mxfp4_opt_e8m0_never_drops_two_exponents :
    (∀ M s : Rat, 3 < M → 0 ≤ s → s ≤ 1 / 4 →
      e2m1ErrSq s M - e2m1ErrSq (1 / 2) M = (3 - 6 * s) * (2 * M - 3 - 6 * s) ∧
      3 * M - 27 / 4 ≤ e2m1ErrSq s M - e2m1ErrSq (1 / 2) M ∧
      9 / 4 < e2m1ErrSq s M - e2m1ErrSq (1 / 2) M) ∧
    (∀ (M s : Rat) (bulk : List Rat), 3 < absRat M → 0 ≤ s → s ≤ 1 / 4 →
      blockErrSq (1 / 2) bulk ≤ 3 * absRat M - 27 / 4 →
      blockErrSq (1 / 2) (M :: bulk) < blockErrSq s (M :: bulk) ∨
      (blockErrSq (1 / 2) (M :: bulk) ≤ blockErrSq s (M :: bulk) ∧
        (s < 1 / 4 ∨ 0 < blockErrSq s bulk → blockErrSq (1 / 2) (M :: bulk) < blockErrSq s (M :: bulk)))) ∧
    (∀ (M s : Rat) (bulk : List Rat), 3 < absRat M → 0 ≤ s → s ≤ 1 / 4 →
      bulk.length ≤ 144 → (∀ u ∈ bulk, absRat u ≤ 1) →
      blockErrSq (1 / 2) (M :: bulk) < blockErrSq s (M :: bulk)) ∧
    (∀ (M s : Rat) (bulk : List Rat), 3 < absRat M → 0 ≤ s → s ≤ 1 / 4 →
      bulk.length ≤ 36 → (∀ u ∈ bulk, absRat u ≤ 2) →
      blockErrSq (1 / 2) (M :: bulk) < blockErrSq s (M :: bulk)) ∧
    (∀ (s : Rat) (bulk : List Rat), 0 ≤ s → s ≤ 1 / 4 →
      bulk.length ≤ 44 → (∀ u ∈ bulk, absRat u ≤ 3) →
      blockErrSq (1 / 2) (6 :: bulk) < blockErrSq s (6 :: bulk)) := by
  have hdiff : ∀ M s : Rat, 3 < M → 0 ≤ s → s ≤ 1 / 4 →
      e2m1ErrSq s M - e2m1ErrSq (1 / 2) M = (3 - 6 * s) * (2 * M - 3 - 6 * s) ∧
      3 * M - 27 / 4 ≤ e2m1ErrSq s M - e2m1ErrSq (1 / 2) M ∧
      9 / 4 < e2m1ErrSq s M - e2m1ErrSq (1 / 2) M := by
    intro M s hM hs0 hs4
    have hM0 : (0 : Rat) ≤ M := by grind
    have hes : e2m1ErrSq s M = sq (M - s * 6) := by
      have h := e2m1ErrSq_eq_top hs0 (by rw [absRat_of_nonneg hM0]; grind)
      rw [absRat_of_nonneg hM0] at h; exact h
    have heh : e2m1ErrSq (1 / 2) M = sq (M - 3) := by
      have h := e2m1ErrSq_eq_top (s := (1 / 2 : Rat)) (u := M) (by grind)
        (by rw [absRat_of_nonneg hM0]; grind)
      rw [absRat_of_nonneg hM0] at h
      have hid : (1 / 2 : Rat) * 6 = 3 := by grind
      rw [hid] at h; exact h
    have heq : e2m1ErrSq s M - e2m1ErrSq (1 / 2) M = (3 - 6 * s) * (2 * M - 3 - 6 * s) := by
      rw [hes, heh]; unfold sq; grind
    have hge : 3 * M - 27 / 4 ≤ (3 - 6 * s) * (2 * M - 3 - 6 * s) := by
      have h1 : (0 : Rat) ≤ (1 / 4 - s) * (12 * M - 27 + 6 * (1 / 4 - s) * 6) := by
        have ha : (0 : Rat) ≤ 1 / 4 - s := rat_sub_nonneg hs4
        have hb : (0 : Rat) ≤ 12 * M - 27 + 6 * (1 / 4 - s) * 6 := by grind
        exact Rat.mul_nonneg ha hb
      grind
    refine ⟨heq, by rw [heq]; exact hge, ?_⟩
    rw [heq]
    have hlt : (9 / 4 : Rat) < 3 * M - 27 / 4 := by grind
    exact rat_lt_of_lt_of_le hlt hge
  refine ⟨hdiff, ?_, ?_, ?_, ?_⟩
  · intro M s bulk hM hs0 hs4 hbulk
    have hd := hdiff (absRat M) s hM hs0 hs4
    rw [e2m1ErrSq_abs s M, e2m1ErrSq_abs (1 / 2) M] at hd
    have hsb_nn : (0 : Rat) ≤ blockErrSq s bulk := blockErrSq_nonneg s bulk
    right
    refine ⟨by simp only [blockErrSq]; grind, ?_⟩
    intro hstrict
    simp only [blockErrSq]
    cases hstrict with
    | inl hslt =>
      have hstrict_gap : 3 * absRat M - 27 / 4 < e2m1ErrSq s M - e2m1ErrSq (1 / 2) M := by
        rw [hd.1]
        have ha : (0 : Rat) < 1 / 4 - s := rat_sub_pos hslt
        have hb : (0 : Rat) < 12 * absRat M - 27 + 36 * (1 / 4 - s) := by grind
        have hpos := rat_mul_pos ha hb
        grind
      grind
    | inr hbpos => grind
  · intro M s bulk hM hs0 hs4 hlen hall
    have hd := (hdiff (absRat M) s hM hs0 hs4).2.2
    rw [e2m1ErrSq_abs s M, e2m1ErrSq_abs (1 / 2) M] at hd
    have hb_le : blockErrSq (1 / 2) bulk ≤ (bulk.length : Rat) * (1 / 64) :=
      blockErrSq_le_len_mul bulk (fun u hu => e2m1ErrSq_half_le_1_64 (hall u hu))
    have hlen_le : (bulk.length : Rat) ≤ 144 := rat_natCast_le hlen
    have hsb_nn : (0 : Rat) ≤ blockErrSq s bulk := blockErrSq_nonneg s bulk
    simp only [blockErrSq]; grind
  · intro M s bulk hM hs0 hs4 hlen hall
    have hd := (hdiff (absRat M) s hM hs0 hs4).2.2
    rw [e2m1ErrSq_abs s M, e2m1ErrSq_abs (1 / 2) M] at hd
    have hb_le : blockErrSq (1 / 2) bulk ≤ (bulk.length : Rat) * (1 / 16) :=
      blockErrSq_le_len_mul bulk (fun u hu => e2m1ErrSq_half_le_1_16 (hall u hu))
    have hlen_le : (bulk.length : Rat) ≤ 36 := rat_natCast_le hlen
    have hsb_nn : (0 : Rat) ≤ blockErrSq s bulk := blockErrSq_nonneg s bulk
    simp only [blockErrSq]; grind
  · intro s bulk hs0 hs4 hlen hall
    have hd := (hdiff 6 s (by grind) hs0 hs4).2.1
    have hb_le : blockErrSq (1 / 2) bulk ≤ (bulk.length : Rat) * (1 / 4) :=
      blockErrSq_le_len_mul bulk (fun u hu => e2m1ErrSq_half_le_1_4 (hall u hu))
    have hlen_le : (bulk.length : Rat) ≤ 44 := rat_natCast_le hlen
    have hsb_nn : (0 : Rat) ≤ blockErrSq s bulk := blockErrSq_nonneg s bulk
    simp only [blockErrSq]; grind

end Mxfp4OptClipping
