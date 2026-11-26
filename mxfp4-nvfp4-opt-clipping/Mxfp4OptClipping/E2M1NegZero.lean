/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp4OptClipping.RatOrder

/-!
# E2M1 `-0` (`0b1000`) Repurposing Theorem (Theorem 6)

Proves `e2m1_neg_zero_repurposing_exact_gain`:
1. **`c = 8` (clean power-of-2 hardware level):** Universal all-`B` unrestricted MXFP4 `ceil-E8M0`
   contraction law `(B + 15)/(B + 399)` for `1 ≤ B ≤ 33` (`47/431` at `B = 32`, matching `opt-E8M0`'s
   `1.624x` improvement with ZERO scale search!) and `(B - 1)/(B + 255)` for `B ≥ 33` (`63/319` at
   `B = 64`), plus exact attainment witnesses for all `B ≥ 1`.
2. **`c = 1/4` (deadzone-halving champion):** Halves the subnormal deadzone from `1/4` to `1/8`
   (exact `4x` reduction in deadzone squared error `1/16 → 1/64`), yielding the universal all-`B`
   deadzone-bulk MXFP4 `ceil-E8M0` law `(B + 63)/(B + 1599)` for `1 ≤ B ≤ 42` (`95/1631` at `B = 32`,
   `> 3.04x` tighter than baseline `31/175`!) and `(B - 1)/(B + 575)` for `B ≥ 43`, plus exact
   NVFP4 `B = 16` deadzone-bulk reduction `199/4231 → 391/16519` (`> 1.98x` tighter).
3. **`c = 5` (Gaussian/Laplace `[4, 6]` gap-filler):** Universal `B = 1` MXFP4 `ceil-E8M0`
   worst-case relative MSE drops from `1/25` to `1/49` (`49/25 = 1.96x` tighter), and peak
   squared error on `[4, 6]` drops `4x` (`1 → 1/4`).
-/

namespace Mxfp4OptClipping

/-! ### Helpers for `e2m1PlusErrSq` -/

theorem e2m1PlusErrSq_le_base (c s u : Rat) : e2m1PlusErrSq c s u ≤ e2m1ErrSq s u :=
  rat_min_le_left _ _

theorem e2m1PlusErrSq_le_extra (c s u : Rat) : e2m1PlusErrSq c s u ≤ sq (absRat u - s * c) :=
  rat_min_le_right _ _

theorem e2m1PlusErrSq_nonneg (c s u : Rat) : (0 : Rat) ≤ e2m1PlusErrSq c s u :=
  rat_le_min (e2m1ErrSq_nonneg s u) (rat_sq_nonneg _)

theorem e2m1PlusErrSq_abs (c s u : Rat) : e2m1PlusErrSq c s (absRat u) = e2m1PlusErrSq c s u := by
  unfold e2m1PlusErrSq
  rw [e2m1ErrSq_abs, absRat_of_nonneg (absRat_nonneg u)]

/-! ### Part 1: `c = 8` Universal All-`B` Unrestricted MXFP4 `ceil-E8M0` Law -/

theorem e2m1Plus8_sub_wsq_le {w u : Rat} (hw_lo : (1 / 25 : Rat) ≤ w) (hw_hi : w ≤ 1)
    (hu : absRat u ≤ 8) :
    e2m1PlusErrSq 8 1 u - w * sq u ≤ (1 - w) / 16 := by
  rw [← sq_absRat u]
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
      (e2m1PlusErrSq 8 1 u ≤ sq (a - q)) →
      sq (l - q) - w * sq l ≤ (1 - w) / 16 →
      sq (r - q) - w * sq r ≤ (1 - w) / 16 →
      e2m1PlusErrSq 8 1 u - w * sq a ≤ (1 - w) / 16 := by
    intro q l r hl hr hle hfl hfr
    have hq := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * q) (C := q * q)
      (rat_sub_nonneg hw_hi) hl hr
      (by have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by unfold sq; grind
          rw [hid]; exact hfl)
      (by have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by unfold sq; grind
          rw [hid]; exact hfr)
    have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by unfold sq; grind
    rw [hid] at hq
    have hsub : e2m1PlusErrSq 8 1 u - w * sq a ≤ sq (a - q) - w * sq a := by grind
    exact Rat.le_trans hsub hq
  cases Rat.le_total (a := a) (b := (1 / 4 : Rat)) with
  | inl h1 =>
    exact hstep 0 0 (1 / 4) ha0 h1
      (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (e2m1ErrSq_le_0 1 u))
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (3 / 4 : Rat)) with
    | inl h2 =>
      exact hstep (1 / 2) (1 / 4) (3 / 4) h1 h2
        (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (by have := e2m1ErrSq_le_half 1 u; grind))
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (5 / 4 : Rat)) with
      | inl h3 =>
        exact hstep 1 (3 / 4) (5 / 4) h2 h3
          (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (by have := e2m1ErrSq_le_1 1 u; grind))
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h3 =>
        cases Rat.le_total (a := a) (b := (7 / 4 : Rat)) with
        | inl h4 =>
          exact hstep (3 / 2) (5 / 4) (7 / 4) h3 h4
            (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (by have := e2m1ErrSq_le_3half 1 u; grind))
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h4 =>
          cases Rat.le_total (a := a) (b := (5 / 2 : Rat)) with
          | inl h5 =>
            exact hstep 2 (7 / 4) (5 / 2) h4 h5
              (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (by have := e2m1ErrSq_le_2 1 u; grind))
              (by unfold sq; grind) (by unfold sq; grind)
          | inr h5 =>
            cases Rat.le_total (a := a) (b := (7 / 2 : Rat)) with
            | inl h6 =>
              exact hstep 3 (5 / 2) (7 / 2) h5 h6
                (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (by have := e2m1ErrSq_le_3 1 u; grind))
                (by unfold sq; grind) (by unfold sq; grind)
            | inr h6 =>
              cases Rat.le_total (a := a) (b := (5 : Rat)) with
              | inl h7 =>
                exact hstep 4 (7 / 2) 5 h6 h7
                  (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (by have := e2m1ErrSq_le_4 1 u; grind))
                  (by unfold sq; grind) (by unfold sq; grind)
              | inr h7 =>
                cases Rat.le_total (a := a) (b := (7 : Rat)) with
                | inl h8 =>
                  exact hstep 6 5 7 h7 h8
                    (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 u) (by have := e2m1ErrSq_le_6 1 u; grind))
                    (by unfold sq; grind) (by unfold sq; grind)
                | inr h8 =>
                  exact hstep 8 7 8 h8 hu
                    (by have := e2m1PlusErrSq_le_extra 8 1 u; grind)
                    (by unfold sq; grind) (by unfold sq; grind)

theorem e2m1Plus8_pivot_le {w K M : Rat} (_hw_lo : (1 / 25 : Rat) ≤ w) (hw_hi : w ≤ 1)
    (hM_lo : (4 : Rat) ≤ absRat M) (hM_hi : absRat M ≤ 8)
    (h4 : -16 * w ≤ K) (h5 : 1 - 25 * w ≤ K) (h7 : 1 - 49 * w ≤ K) (h8 : -64 * w ≤ K) :
    e2m1PlusErrSq 8 1 M - w * sq M ≤ K := by
  rw [← sq_absRat M]
  let a := absRat M
  have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
      (e2m1PlusErrSq 8 1 M ≤ sq (a - q)) →
      sq (l - q) - w * sq l ≤ K →
      sq (r - q) - w * sq r ≤ K →
      e2m1PlusErrSq 8 1 M - w * sq a ≤ K := by
    intro q l r hl hr hle hfl hfr
    have hq := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * q) (C := q * q)
      (rat_sub_nonneg hw_hi) hl hr
      (by have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by unfold sq; grind
          rw [hid]; exact hfl)
      (by have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by unfold sq; grind
          rw [hid]; exact hfr)
    have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by unfold sq; grind
    rw [hid] at hq
    have hsub : e2m1PlusErrSq 8 1 M - w * sq a ≤ sq (a - q) - w * sq a := by grind
    exact Rat.le_trans hsub hq
  cases Rat.le_total (a := a) (b := (5 : Rat)) with
  | inl h1 =>
    exact hstep 4 4 5 hM_lo h1
      (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 M) (by have := e2m1ErrSq_le_4 1 M; grind))
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (7 : Rat)) with
    | inl h2 =>
      exact hstep 6 5 7 h1 h2
        (Rat.le_trans (e2m1PlusErrSq_le_base 8 1 M) (by have := e2m1ErrSq_le_6 1 M; grind))
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      exact hstep 8 7 8 h2 hM_hi
        (by have := e2m1PlusErrSq_le_extra 8 1 M; grind)
        (by unfold sq; grind) (by unfold sq; grind)

theorem e2m1Plus8_at_5 : e2m1PlusErrSq 8 1 5 = 1 := by
  unfold e2m1PlusErrSq
  rw [e2m1ErrSq_1_on_ge_5 (by grind), absRat_of_nonneg (by grind)]
  unfold sq
  rw [rat_min_eq_left (by grind)]
  grind

theorem e2m1Plus8_at_4 : e2m1PlusErrSq 8 1 4 = 0 := by
  apply Rat.le_antisymm
  · have h := Rat.le_trans (e2m1PlusErrSq_le_base 8 1 4) (e2m1ErrSq_le_4 1 4)
    rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · exact e2m1PlusErrSq_nonneg _ _ _

theorem e2m1Plus8_at_qtr : e2m1PlusErrSq 8 1 (1 / 4) = 1 / 16 := by
  unfold e2m1PlusErrSq
  have hbase : e2m1ErrSq 1 (1 / 4) = 1 / 16 := by
    apply Rat.le_antisymm
    · have h := e2m1ErrSq_le_0 1 (1 / 4); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
    · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]; unfold sq
      apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
      apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
      apply rat_le_min (by grind); grind
  rw [hbase, absRat_of_nonneg (by grind)]
  unfold sq
  exact rat_min_eq_left (by grind)

/-! ### Part 2: `c = 1/4` Deadzone-Halving Helpers -/

theorem e2m1PlusQtr_le_deadzone {w u : Rat} (hw0 : (0 : Rat) ≤ w) (hw1 : w ≤ 1)
    (hu : absRat u ≤ 1 / 2) :
    e2m1PlusErrSq (1 / 4) 1 u - w * sq u ≤ (1 - w) / 64 := by
  rw [← sq_absRat u]
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
      (e2m1PlusErrSq (1 / 4) 1 u ≤ sq (a - q)) →
      sq (l - q) - w * sq l ≤ (1 - w) / 64 →
      sq (r - q) - w * sq r ≤ (1 - w) / 64 →
      e2m1PlusErrSq (1 / 4) 1 u - w * sq a ≤ (1 - w) / 64 := by
    intro q l r hl hr hle hfl hfr
    have hq := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * q) (C := q * q)
      (rat_sub_nonneg hw1) hl hr
      (by have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by unfold sq; grind
          rw [hid]; exact hfl)
      (by have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by unfold sq; grind
          rw [hid]; exact hfr)
    have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by unfold sq; grind
    rw [hid] at hq
    have hsub : e2m1PlusErrSq (1 / 4) 1 u - w * sq a ≤ sq (a - q) - w * sq a := by grind
    exact Rat.le_trans hsub hq
  cases Rat.le_total (a := a) (b := (1 / 8 : Rat)) with
  | inl h1 =>
    exact hstep 0 0 (1 / 8) ha0 h1
      (Rat.le_trans (e2m1PlusErrSq_le_base (1 / 4) 1 u) (e2m1ErrSq_le_0 1 u))
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (3 / 8 : Rat)) with
    | inl h2 =>
      exact hstep (1 / 4) (1 / 8) (3 / 8) h1 h2
        (by have := e2m1PlusErrSq_le_extra (1 / 4) 1 u; grind)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      exact hstep (1 / 2) (3 / 8) (1 / 2) h2 hu
        (Rat.le_trans (e2m1PlusErrSq_le_base (1 / 4) 1 u) (by have := e2m1ErrSq_le_half 1 u; grind))
        (by unfold sq; grind) (by unfold sq; grind)

theorem e2m1PlusQtr_at_eighth : e2m1PlusErrSq (1 / 4) 1 (1 / 8) = 1 / 64 := by
  unfold e2m1PlusErrSq
  have hbase : e2m1ErrSq 1 (1 / 8) = 1 / 64 := by
    apply Rat.le_antisymm
    · have h := e2m1ErrSq_le_0 1 (1 / 8); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
    · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]; unfold sq
      apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
      apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
      apply rat_le_min (by grind); grind
  rw [hbase, absRat_of_nonneg (by grind)]
  unfold sq
  exact rat_min_eq_left (by grind)

theorem e2m1PlusQtr_at_5 : e2m1PlusErrSq (1 / 4) 1 5 = 1 := by
  unfold e2m1PlusErrSq
  rw [e2m1ErrSq_1_on_ge_5 (by grind), absRat_of_nonneg (by grind)]
  unfold sq
  rw [rat_min_eq_left (by grind)]
  grind

theorem e2m1PlusQtr_at_3 : e2m1PlusErrSq (1 / 4) 1 3 = 0 := by
  apply Rat.le_antisymm
  · have h := Rat.le_trans (e2m1PlusErrSq_le_base (1 / 4) 1 3) (e2m1ErrSq_le_3 1 3)
    rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · exact e2m1PlusErrSq_nonneg _ _ _

/-! ### Part 3: `c = 5` `[4, 6]` Gap-Filler Helpers -/

theorem e2m1Plus5_le_1_4_on_4_6 {u : Rat} (hlo : (4 : Rat) ≤ u) (hhi : u ≤ 6) :
    e2m1PlusErrSq 5 1 u ≤ 1 / 4 := by
  have hu0 : (0 : Rat) ≤ u := by grind
  have habs : absRat u = u := absRat_of_nonneg hu0
  cases Rat.le_total (a := u) (b := (9 / 2 : Rat)) with
  | inl h1 =>
    have h := Rat.le_trans (e2m1PlusErrSq_le_base 5 1 u) (e2m1ErrSq_le_4 1 u)
    rw [habs] at h
    have hsq : sq (u - 1 * 4) ≤ 1 / 4 := by
      have : (0 : Rat) ≤ (1 / 2 - (u - 4)) * (1 / 2 + (u - 4)) := Rat.mul_nonneg (by grind) (by grind)
      unfold sq; grind
    exact Rat.le_trans h hsq
  | inr h1 =>
    cases Rat.le_total (a := u) (b := (11 / 2 : Rat)) with
    | inl h2 =>
      have h := e2m1PlusErrSq_le_extra 5 1 u
      rw [habs] at h
      have hsq : sq (u - 1 * 5) ≤ 1 / 4 := by
        have : (0 : Rat) ≤ (1 / 2 - (u - 5)) * (1 / 2 + (u - 5)) := Rat.mul_nonneg (by grind) (by grind)
        unfold sq; grind
      exact Rat.le_trans h hsq
    | inr h2 =>
      have h := Rat.le_trans (e2m1PlusErrSq_le_base 5 1 u) (e2m1ErrSq_le_6 1 u)
      rw [habs] at h
      have hsq : sq (u - 1 * 6) ≤ 1 / 4 := by
        have : (0 : Rat) ≤ (1 / 2 - (6 - u)) * (1 / 2 + (6 - u)) := Rat.mul_nonneg (by grind) (by grind)
        unfold sq; grind
      exact Rat.le_trans h hsq

theorem e2m1Plus5_b1_bound {M : Rat} (hlo : (3 : Rat) ≤ M) (hhi : M ≤ 6) :
    e2m1PlusErrSq 5 1 M ≤ (1 / 49 : Rat) * sq M := by
  have hM0 : (0 : Rat) ≤ M := by grind
  have habs : absRat M = M := absRat_of_nonneg hM0
  have hstep : ∀ q l r : Rat, l ≤ M → M ≤ r →
      (e2m1PlusErrSq 5 1 M ≤ sq (M - q)) →
      sq (l - q) - (1 / 49) * sq l ≤ 0 →
      sq (r - q) - (1 / 49) * sq r ≤ 0 →
      e2m1PlusErrSq 5 1 M ≤ (1 / 49 : Rat) * sq M := by
    intro q l r hl hr hle hfl hfr
    have hq := convex_quad_le_of_endpoints (A := 1 - 1 / 49) (B := -2 * q) (C := q * q)
      (by grind) hl hr
      (by have hid : (1 - (1 / 49 : Rat)) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - (1 / 49) * sq l := by unfold sq; grind
          rw [hid]; exact hfl)
      (by have hid : (1 - (1 / 49 : Rat)) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - (1 / 49) * sq r := by unfold sq; grind
          rw [hid]; exact hfr)
    have hid : (1 - (1 / 49 : Rat)) * (M * M) + (-2 * q) * M + q * q = sq (M - q) - (1 / 49) * sq M := by
      unfold sq; grind
    rw [hid] at hq; grind
  cases Rat.le_total (a := M) (b := (7 / 2 : Rat)) with
  | inl h1 =>
    exact hstep 3 3 (7 / 2) hlo h1
      (by have := Rat.le_trans (e2m1PlusErrSq_le_base 5 1 M) (e2m1ErrSq_le_3 1 M); rw [habs] at this; grind)
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := M) (b := (9 / 2 : Rat)) with
    | inl h2 =>
      exact hstep 4 (7 / 2) (9 / 2) h1 h2
        (by have := Rat.le_trans (e2m1PlusErrSq_le_base 5 1 M) (e2m1ErrSq_le_4 1 M); rw [habs] at this; grind)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      cases Rat.le_total (a := M) (b := (11 / 2 : Rat)) with
      | inl h3 =>
        exact hstep 5 (9 / 2) (11 / 2) h2 h3
          (by have := e2m1PlusErrSq_le_extra 5 1 M; rw [habs] at this; grind)
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h3 =>
        exact hstep 6 (11 / 2) 6 h3 hhi
          (by have := Rat.le_trans (e2m1PlusErrSq_le_base 5 1 M) (e2m1ErrSq_le_6 1 M); rw [habs] at this; grind)
          (by unfold sq; grind) (by unfold sq; grind)

theorem e2m1Plus5_at_7_2 : e2m1PlusErrSq 5 1 (7 / 2) = 1 / 4 := by
  unfold e2m1PlusErrSq
  rw [e2m1ErrSq_1_on_3_7half (by grind) (by grind), absRat_of_nonneg (by grind)]
  unfold sq
  rw [rat_min_eq_left (by grind)]
  grind

/-- Theorem 6: Exact E2M1 `-0` (`0b1000`) Repurposing Gains (`c = 8`, `c = 1/4`, `c = 5`). -/
theorem e2m1_neg_zero_repurposing_exact_gain :
    -- 1. c = 8: Universal all-B unrestricted MXFP4 ceil-E8M0 bound + exact witnesses:
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      4 ≤ absRat M → absRat M ≤ 8 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 8) →
      blockPlusErrSq 8 1 (M :: bulk) ≤ omegaE2M1Plus8 B * blockEnergy (M :: bulk)) ∧
    (∀ B : Nat, 1 ≤ B → B ≤ 33 →
      let x := mkSingleOutlierBlock B 5 (1 / 4)
      blockPlusErrSq 8 1 x = omegaE2M1Plus8 B * blockEnergy x) ∧
    (∀ B : Nat, 33 ≤ B →
      let x := mkSingleOutlierBlock B 4 (1 / 4)
      blockPlusErrSq 8 1 x = omegaE2M1Plus8 B * blockEnergy x) ∧
    (omegaE2M1Plus8 32 = 47 / 431 ∧ omegaE2M1Plus8 64 = 63 / 319 ∧
     (162 / 100 : Rat) * omegaE2M1Plus8 32 < 31 / 175) ∧
    -- 2. c = 1/4: Universal all-B deadzone-bulk MXFP4 ceil-E8M0 bound + exact witnesses (95/1631 at B = 32, > 3.04x!):
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 1 / 2) →
      blockPlusErrSq (1 / 4) 1 (M :: bulk) ≤ omegaE2M1PlusQtr B * blockEnergy (M :: bulk)) ∧
    (∀ B : Nat, 1 ≤ B → B ≤ 33 →
      let x := mkSingleOutlierBlock B 5 (1 / 8)
      blockPlusErrSq (1 / 4) 1 x = omegaE2M1PlusQtr B * blockEnergy x) ∧
    (∀ B : Nat, 49 ≤ B →
      let x := mkSingleOutlierBlock B 3 (1 / 8)
      blockPlusErrSq (1 / 4) 1 x = omegaE2M1PlusQtr B * blockEnergy x) ∧
    (omegaE2M1PlusQtr 32 = 95 / 1631 ∧
     (304 / 100 : Rat) * omegaE2M1PlusQtr 32 < 31 / 175) ∧
    -- 3. c = 5: B = 1 MXFP4 ceil-E8M0 drops from 1/25 to 1/49 (1.96x) and [4, 6] peak error drops 4x:
    (∀ M : Rat, 3 ≤ M → M ≤ 6 → e2m1PlusErrSq 5 1 M ≤ (1 / 49 : Rat) * sq M) ∧
    (e2m1PlusErrSq 5 1 (7 / 2) = (1 / 49 : Rat) * sq (7 / 2) ∧
     (∀ u : Rat, 4 ≤ u → u ≤ 6 → e2m1PlusErrSq 5 1 u ≤ 1 / 4)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- c = 8 universal bound
    intro B M bulk hB hMlo hMhi hlen hbulk
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have hb1 : (1 : Rat) ≤ b := rat_natCast_le hB
    have hsum_gen : ∀ w : Rat, (1 / 25 : Rat) ≤ w → w ≤ 1 →
        e2m1PlusErrSq 8 1 M - w * sq M ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 16)) →
        blockPlusErrSq 8 1 (M :: bulk) ≤ w * blockEnergy (M :: bulk) := by
      intro w hw_lo hw_hi hM_err
      have hsum_bulk : blockPlusErrSq 8 1 bulk - w * blockEnergy bulk ≤
          (bulk.length : Rat) * ((1 - w) / 16) :=
        blockPlusErrSq_sub_wEnergy_le_len bulk (fun u hu => e2m1Plus8_sub_wsq_le hw_lo hw_hi (hbulk u hu))
      rw [hlen] at hsum_bulk
      simp only [blockPlusErrSq, blockEnergy]; grind
    by_cases h33 : B ≤ 33
    · have hw_eq : omegaE2M1Plus8 B = (b + 15) / (b + 399) := by
        unfold omegaE2M1Plus8; simp only [h33, ite_true]; rfl
      rw [hw_eq]
      have hb33 : b ≤ 33 := rat_natCast_le h33
      have hden : (0 : Rat) < b + 399 := by grind
      let w : Rat := (b + 15) / (b + 399)
      have hw_mul : w * (b + 399) = b + 15 := rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw_lo : (1 / 25 : Rat) ≤ w := rat_le_div_of_mul_le hden (by grind)
      have hw_hi : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      apply hsum_gen w hw_lo hw_hi
      apply e2m1Plus8_pivot_le hw_lo hw_hi hMlo hMhi
      · rw [hBcast]; exact rat_le_of_clear hden (poly := -16 * (b + 15) + 24 * (b - 1)) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := (b + 399) - 25 * (b + 15) + 24 * (b - 1)) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := (b + 399) - 49 * (b + 15) + 24 * (b - 1)) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := -64 * (b + 15) + 24 * (b - 1)) (by grind) (by grind)
    · have hw_eq : omegaE2M1Plus8 B = (b - 1) / (b + 255) := by
        unfold omegaE2M1Plus8; simp only [h33, ite_false]; rfl
      rw [hw_eq]
      have hb34 : (34 : Rat) ≤ b := rat_natCast_le (by omega : 34 ≤ B)
      have hden : (0 : Rat) < b + 255 := by grind
      let w : Rat := (b - 1) / (b + 255)
      have hw_mul : w * (b + 255) = b - 1 := rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw_lo : (1 / 25 : Rat) ≤ w := rat_le_div_of_mul_le hden (by grind)
      have hw_hi : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      apply hsum_gen w hw_lo hw_hi
      apply e2m1Plus8_pivot_le hw_lo hw_hi hMlo hMhi
      · rw [hBcast]; exact rat_le_of_clear hden (poly := 0) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := (b + 255) - 25 * (b - 1) + 16 * (b - 1)) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := (b + 255) - 49 * (b - 1) + 16 * (b - 1)) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := -64 * (b - 1) + 16 * (b - 1)) (by grind) (by grind)
  · -- c = 8 witness for B ≤ 33
    intro B hB h33
    dsimp only [mkSingleOutlierBlock]
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    simp only [blockPlusErrSq, blockPlusErrSq_replicate, blockEnergy, blockEnergy_replicate,
      e2m1Plus8_at_5, e2m1Plus8_at_qtr, hBcast]
    unfold omegaE2M1Plus8 sq
    simp only [h33, ite_true]
    have hden : (B : Rat) + 399 ≠ 0 := by have := rat_natCast_nonneg B; grind
    have hmul := rat_div_mul_cancel (a := (B : Rat) + 15) hden
    grind
  · -- c = 8 witness for B ≥ 33
    intro B h33
    dsimp only [mkSingleOutlierBlock]
    have hB : 1 ≤ B := by omega
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    simp only [blockPlusErrSq, blockPlusErrSq_replicate, blockEnergy, blockEnergy_replicate,
      e2m1Plus8_at_4, e2m1Plus8_at_qtr, hBcast]
    by_cases h33eq : B = 33
    · subst h33eq; unfold omegaE2M1Plus8 sq; simp; grind
    · have hnot : ¬ B ≤ 33 := by omega
      unfold omegaE2M1Plus8 sq
      simp only [hnot, ite_false]
      have hden : (B : Rat) + 255 ≠ 0 := by have := rat_natCast_nonneg B; grind
      have hmul := rat_div_mul_cancel (a := (B : Rat) - 1) hden
      grind
  · -- c = 8 benchmarks
    have h32 : omegaE2M1Plus8 32 = 47 / 431 := by unfold omegaE2M1Plus8; simp; grind
    have h64 : omegaE2M1Plus8 64 = 63 / 319 := by unfold omegaE2M1Plus8; simp; grind
    refine ⟨h32, h64, ?_⟩
    rw [h32]; grind
  · -- c = 1/4 universal deadzone-bulk bound
    intro B M bulk hB hMlo hMhi hlen hbulk
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have hb1 : (1 : Rat) ≤ b := rat_natCast_le hB
    have hsum_gen : ∀ w : Rat, (1 / 25 : Rat) ≤ w → w ≤ 1 →
        -9 * w ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) →
        (1 / 4 : Rat) - (49 / 4) * w ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) →
        1 - 25 * w ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) →
        -36 * w ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) →
        blockPlusErrSq (1 / 4) 1 (M :: bulk) ≤ w * blockEnergy (M :: bulk) := by
      intro w hw_lo hw_hi h3 h72 h5 h6
      have hM_err : e2m1PlusErrSq (1 / 4) 1 M - w * sq M ≤ -(((B - 1 : Nat) : Rat) * ((1 - w) / 64)) := by
        have hbase_le : e2m1PlusErrSq (1 / 4) 1 M ≤ e2m1ErrSq 1 M := e2m1PlusErrSq_le_base (1 / 4) 1 M
        rw [← e2m1ErrSq_abs] at hbase_le
        rw [← sq_absRat M]
        let a := absRat M
        let K := -(((B - 1 : Nat) : Rat) * ((1 - w) / 64))
        have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
            (e2m1ErrSq 1 a ≤ sq (a - q)) →
            sq (l - q) - w * sq l ≤ K →
            sq (r - q) - w * sq r ≤ K →
            e2m1PlusErrSq (1 / 4) 1 M - w * sq a ≤ K := by
          intro q l r hl hr hq hfl hfr
          have hc := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * q) (C := q * q)
            (rat_sub_nonneg hw_hi) hl hr
            (by have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by unfold sq; grind
                rw [hid]; exact hfl)
            (by have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by unfold sq; grind
                rw [hid]; exact hfr)
          have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by unfold sq; grind
          rw [hid] at hc; grind
        cases Rat.le_total (a := a) (b := (7 / 2 : Rat)) with
        | inl h1 =>
          exact hstep 3 3 (7 / 2) hMlo h1 (by rw [e2m1ErrSq_1_on_3_7half hMlo h1]; exact Rat.le_refl)
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h1 =>
          cases Rat.le_total (a := a) (b := (5 : Rat)) with
          | inl h2 =>
            exact hstep 4 (7 / 2) 5 h1 h2 (by rw [e2m1ErrSq_1_on_7half_5 h1 h2]; exact Rat.le_refl)
              (by unfold sq; grind) (by unfold sq; grind)
          | inr h2 =>
            exact hstep 6 5 6 h2 hMhi (by rw [e2m1ErrSq_1_on_ge_5 h2]; exact Rat.le_refl)
              (by unfold sq; grind) (by unfold sq; grind)
      have hsum_bulk : blockPlusErrSq (1 / 4) 1 bulk - w * blockEnergy bulk ≤
          (bulk.length : Rat) * ((1 - w) / 64) :=
        blockPlusErrSq_sub_wEnergy_le_len bulk (fun u hu => e2m1PlusQtr_le_deadzone (Rat.le_trans (by grind) hw_lo) hw_hi (hbulk u hu))
      rw [hlen] at hsum_bulk
      simp only [blockPlusErrSq, blockEnergy]; grind
    by_cases h33 : B ≤ 33
    · have hw_eq : omegaE2M1PlusQtr B = (b + 63) / (b + 1599) := by
        unfold omegaE2M1PlusQtr; simp only [h33, ite_true]; rfl
      rw [hw_eq]
      have hb33 : b ≤ 33 := rat_natCast_le h33
      have hden : (0 : Rat) < b + 1599 := by grind
      let w : Rat := (b + 63) / (b + 1599)
      have hw_mul : w * (b + 1599) = b + 63 := rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw_lo : (1 / 25 : Rat) ≤ w := rat_le_div_of_mul_le hden (by grind)
      have hw_hi : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      apply hsum_gen w hw_lo hw_hi
      · rw [hBcast]; exact rat_le_of_clear hden (poly := -9 * (b + 63) + 24 * (b - 1)) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := (1 / 4) * (b + 1599) - (49 / 4) * (b + 63) + 24 * (b - 1)) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := 0) (by grind) (by grind)
      · rw [hBcast]; exact rat_le_of_clear hden (poly := -36 * (b + 63) + 24 * (b - 1)) (by grind) (by grind)
    · by_cases h49 : B ≤ 49
      · have hw_eq : omegaE2M1PlusQtr B = (b + 15) / (b + 783) := by
          unfold omegaE2M1PlusQtr; simp only [h33, h49, ite_false, ite_true]; rfl
        rw [hw_eq]
        have hb34 : (34 : Rat) ≤ b := rat_natCast_le (by omega : 34 ≤ B)
        have hb49 : b ≤ 49 := rat_natCast_le h49
        have hden : (0 : Rat) < b + 783 := by grind
        let w : Rat := (b + 15) / (b + 783)
        have hw_mul : w * (b + 783) = b + 15 := rat_div_mul_cancel (Rat.ne_of_gt hden)
        have hw_lo : (1 / 25 : Rat) ≤ w := rat_le_div_of_mul_le hden (by grind)
        have hw_hi : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
        apply hsum_gen w hw_lo hw_hi
        · rw [hBcast]; exact rat_le_of_clear hden (poly := -9 * (b + 15) + 12 * (b - 1)) (by grind) (by grind)
        · rw [hBcast]; exact rat_le_of_clear hden (poly := 0) (by grind) (by grind)
        · rw [hBcast]; exact rat_le_of_clear hden (poly := (b + 783) - 25 * (b + 15) + 12 * (b - 1)) (by grind) (by grind)
        · rw [hBcast]; exact rat_le_of_clear hden (poly := -36 * (b + 15) + 12 * (b - 1)) (by grind) (by grind)
      · have hw_eq : omegaE2M1PlusQtr B = (b - 1) / (b + 575) := by
          unfold omegaE2M1PlusQtr; simp only [h33, h49, ite_false]; rfl
        rw [hw_eq]
        have hb50 : (50 : Rat) ≤ b := rat_natCast_le (by omega : 50 ≤ B)
        have hden : (0 : Rat) < b + 575 := by grind
        let w : Rat := (b - 1) / (b + 575)
        have hw_mul : w * (b + 575) = b - 1 := rat_div_mul_cancel (Rat.ne_of_gt hden)
        have hw_lo : (1 / 25 : Rat) ≤ w := rat_le_div_of_mul_le hden (by grind)
        have hw_hi : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
        apply hsum_gen w hw_lo hw_hi
        · rw [hBcast]; exact rat_le_of_clear hden (poly := 0) (by grind) (by grind)
        · rw [hBcast]; exact rat_le_of_clear hden (poly := (1 / 4) * (b + 575) - (49 / 4) * (b - 1) + 9 * (b - 1)) (by grind) (by grind)
        · rw [hBcast]; exact rat_le_of_clear hden (poly := (b + 575) - 25 * (b - 1) + 9 * (b - 1)) (by grind) (by grind)
        · rw [hBcast]; exact rat_le_of_clear hden (poly := -36 * (b - 1) + 9 * (b - 1)) (by grind) (by grind)
  · -- c = 1/4 witness for B ≤ 33
    intro B hB h33
    dsimp only [mkSingleOutlierBlock]
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    simp only [blockPlusErrSq, blockPlusErrSq_replicate, blockEnergy, blockEnergy_replicate,
      e2m1PlusQtr_at_5, e2m1PlusQtr_at_eighth, hBcast]
    unfold omegaE2M1PlusQtr sq
    simp only [h33, ite_true]
    have hden : (B : Rat) + 1599 ≠ 0 := by have := rat_natCast_nonneg B; grind
    have hmul := rat_div_mul_cancel (a := (B : Rat) + 63) hden
    grind
  · -- c = 1/4 witness for B ≥ 49
    intro B h49
    dsimp only [mkSingleOutlierBlock]
    have hB : 1 ≤ B := by omega
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    simp only [blockPlusErrSq, blockPlusErrSq_replicate, blockEnergy, blockEnergy_replicate,
      e2m1PlusQtr_at_3, e2m1PlusQtr_at_eighth, hBcast]
    by_cases h49eq : B = 49
    · subst h49eq; unfold omegaE2M1PlusQtr sq; simp; grind
    · have hnot33 : ¬ B ≤ 33 := by omega
      have hnot49 : ¬ B ≤ 49 := by omega
      unfold omegaE2M1PlusQtr sq
      simp only [hnot33, hnot49, ite_false]
      have hden : (B : Rat) + 575 ≠ 0 := by have := rat_natCast_nonneg B; grind
      have hmul := rat_div_mul_cancel (a := (B : Rat) - 1) hden
      grind
  · -- c = 1/4 benchmark
    have h32 : omegaE2M1PlusQtr 32 = 95 / 1631 := by unfold omegaE2M1PlusQtr; simp; grind
    refine ⟨h32, ?_⟩
    rw [h32]; grind
  · -- c = 5 B = 1 bound
    intro M hlo hhi
    exact e2m1Plus5_b1_bound hlo hhi
  · -- c = 5 witness + [4, 6] peak error bound
    refine ⟨?_, fun u h1 h2 => e2m1Plus5_le_1_4_on_4_6 h1 h2⟩
    rw [e2m1Plus5_at_7_2]; unfold sq; grind

end Mxfp4OptClipping
