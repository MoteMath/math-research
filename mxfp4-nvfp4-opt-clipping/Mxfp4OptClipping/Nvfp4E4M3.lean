/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp4OptClipping.RatOrder

/-!
# NVFP4 (`E2M1 + E4M3`) Scale-Rounding & Optimal Clipping Theorems (Theorems 3 and 4)

Proves:
3. `nvfp4_ceil_vs_nearest_e4m3_all_b_ef21_exact`
4. `nvfp4_opt_e4m3_b16_and_b1_synergy_exact`
-/

namespace Mxfp4OptClipping

/-! ### Helper Lemmas for Theorem 3 (`ceil-E4M3` vs `nearest-E4M3`) -/

/-- For any `w ∈ [0, 1]` and any `u` with `|u| ≤ 2`, `e₁(u) - w*u² ≤ (1 - w) / 16`. -/
theorem e1_sub_wsq_le_core {w u : Rat} (hw0 : (0 : Rat) ≤ w) (hw1 : w ≤ 1)
    (hu : absRat u ≤ 2) :
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
    have hq := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * q) (C := q * q)
      (rat_sub_nonneg hw1) hl hr
      (by have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by unfold sq; grind
          rw [hid]; exact hfl)
      (by have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by unfold sq; grind
          rw [hid]; exact hfr)
    have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by unfold sq; grind
    rw [hid] at hq
    have hsub : e2m1ErrSq 1 u - w * sq a ≤ sq (a - q) - w * sq a := by grind
    exact Rat.le_trans hsub hq
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
          exact hstep 2 (7 / 4) 2 h4 hu
            (by have := e2m1ErrSq_le_2 1 u; grind)
            (by unfold sq; grind) (by unfold sq; grind)

/-- For any `w ∈ [0, 1]` and any `u` with `|u| ≤ 6`, `e₁(u) - w*u² ≤ max ((1 - w)/16) (1 - 25*w)`. -/
theorem e1_sub_wsq_le_all {w u : Rat} (hw0 : (0 : Rat) ≤ w) (hw1 : w ≤ 1)
    (hu : absRat u ≤ 6) :
    e2m1ErrSq 1 u - w * sq u ≤ max ((1 - w) / 16) (1 - 25 * w) := by
  let K := max ((1 - w) / 16) (1 - 25 * w)
  have hK1 : (1 - w) / 16 ≤ K := by
    show (1 - w) / 16 ≤ (if (1 - w) / 16 ≤ 1 - 25 * w then 1 - 25 * w else (1 - w) / 16)
    split
    · assumption
    · exact Rat.le_refl
  have hK2 : 1 - 25 * w ≤ K := by
    show 1 - 25 * w ≤ (if (1 - w) / 16 ≤ 1 - 25 * w then 1 - 25 * w else (1 - w) / 16)
    split
    · exact Rat.le_refl
    · rename_i h; exact Rat.le_of_lt (Rat.not_le.mp h)
  cases Rat.le_total (a := absRat u) (b := (2 : Rat)) with
  | inl hle2 => exact Rat.le_trans (e1_sub_wsq_le_core hw0 hw1 hle2) hK1
  | inr hge2 =>
    rw [← sq_absRat u]
    let a := absRat u
    have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
        (e2m1ErrSq 1 u ≤ sq (a - q)) →
        sq (l - q) - w * sq l ≤ K →
        sq (r - q) - w * sq r ≤ K →
        e2m1ErrSq 1 u - w * sq a ≤ K := by
      intro q l r hl hr hle hfl hfr
      have hq := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * q) (C := q * q)
        (rat_sub_nonneg hw1) hl hr
        (by have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by unfold sq; grind
            rw [hid]; exact hfl)
        (by have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by unfold sq; grind
            rw [hid]; exact hfr)
      have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by unfold sq; grind
      rw [hid] at hq
      have hsub : e2m1ErrSq 1 u - w * sq a ≤ sq (a - q) - w * sq a := by grind
      exact Rat.le_trans hsub hq
    cases Rat.le_total (a := a) (b := (5 / 2 : Rat)) with
    | inl h1 =>
      exact hstep 2 2 (5 / 2) hge2 h1
        (by have := e2m1ErrSq_le_2 1 u; grind)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h1 =>
      cases Rat.le_total (a := a) (b := (7 / 2 : Rat)) with
      | inl h2 =>
        exact hstep 3 (5 / 2) (7 / 2) h1 h2
          (by have := e2m1ErrSq_le_3 1 u; grind)
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h2 =>
        cases Rat.le_total (a := a) (b := (5 : Rat)) with
        | inl h3 =>
          exact hstep 4 (7 / 2) 5 h2 h3
            (by have := e2m1ErrSq_le_4 1 u; grind)
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h3 =>
          exact hstep 6 5 6 h3 hu
            (by have := e2m1ErrSq_le_6 1 u; grind)
            (by unfold sq; grind) (by unfold sq; grind)

theorem e2m1ErrSq_1_at_16_3 : e2m1ErrSq 1 (16 / 3) = 4 / 9 := by
  rw [e2m1ErrSq_1_on_ge_5 (by grind)]; unfold sq; grind

theorem e2m1ErrSq_1_at_17_3 : e2m1ErrSq 1 (17 / 3) = 1 / 9 := by
  rw [e2m1ErrSq_1_on_ge_5 (by grind)]; unfold sq; grind

theorem blockErrSq_1_le_of_M_and_bulk (B : Nat) (_hB : 1 ≤ B) (M_lo w K : Rat)
    (hM_lo5 : (5 : Rat) ≤ M_lo) (_hM_lo6 : M_lo ≤ 6)
    (_hw0 : (0 : Rat) ≤ w) (hw1 : w ≤ 1)
    (hM_bound : sq (M_lo - 6) - w * sq M_lo + ((B - 1 : Nat) : Rat) * K ≤ 0)
    (h6_bound : -w * 36 + ((B - 1 : Nat) : Rat) * K ≤ 0)
    (M : Rat) (bulk : List Rat)
    (hM_lo : M_lo ≤ absRat M) (hM_hi : absRat M ≤ 6)
    (hlen : bulk.length = B - 1)
    (hbulk : ∀ u ∈ bulk, e2m1ErrSq 1 u - w * sq u ≤ K) :
    blockErrSq 1 (M :: bulk) ≤ w * blockEnergy (M :: bulk) := by
  have hM_err : e2m1ErrSq 1 M - w * sq M ≤ -(((B - 1 : Nat) : Rat) * K) := by
    rw [← e2m1ErrSq_abs, ← sq_absRat M]
    rw [e2m1ErrSq_1_on_ge_5 (Rat.le_trans hM_lo5 hM_lo)]
    have hc := convex_quad_le_of_endpoints (A := 1 - w) (B := -12) (C := 36)
      (K := -(((B - 1 : Nat) : Rat) * K))
      (rat_sub_nonneg hw1) hM_lo hM_hi
      (by have hid : (1 - w) * (M_lo * M_lo) + (-12) * M_lo + 36 = sq (M_lo - 6) - w * sq M_lo := by unfold sq; grind
          rw [hid]; grind)
      (by unfold sq at *; grind)
    have hid : (1 - w) * (absRat M * absRat M) + (-12) * absRat M + 36 = sq (absRat M - 6) - w * sq (absRat M) := by
      unfold sq; grind
    rw [← hid]; exact hc
  have hsum_bulk : blockErrSq 1 bulk - w * blockEnergy bulk ≤ (bulk.length : Rat) * K :=
    blockErrSq_sub_wEnergy_le_len bulk hbulk
  rw [hlen] at hsum_bulk
  simp only [blockErrSq, blockEnergy]
  have htot : (e2m1ErrSq 1 M - w * sq M) + (blockErrSq 1 bulk - w * blockEnergy bulk) ≤ 0 := by grind
  grind

/-- Theorem 3: Exact NVFP4 (`E2M1 + E4M3`) `ceil-E4M3` vs Zero-Search `nearest-E4M3` All-`B` EF21 Law. -/
theorem nvfp4_ceil_vs_nearest_e4m3_all_b_ef21_exact :
    -- 1. Universal all-B upper bounds on core/deadzone bulk (|u| ≤ 2):
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      16 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 2) →
      blockErrSq 1 (M :: bulk) ≤ omegaCeilE4M3 B * blockEnergy (M :: bulk)) ∧
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      17 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 2) →
      blockErrSq 1 (M :: bulk) ≤ omegaNearestE4M3 B * blockEnergy (M :: bulk)) ∧
    -- 2. Universal all-B unrestricted bounds (|u| ≤ 6):
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      16 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 6) →
      blockErrSq 1 (M :: bulk) ≤ omegaCeilE4M3Full B * blockEnergy (M :: bulk)) ∧
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      17 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 6) →
      blockErrSq 1 (M :: bulk) ≤ omegaNearestE4M3Full B * blockEnergy (M :: bulk)) ∧
    -- 3. Exact attainment witnesses for all B ≥ 1:
    (∀ B : Nat, 1 ≤ B →
      let xc := mkSingleOutlierBlock B (16 / 3) (1 / 4)
      let xn := mkSingleOutlierBlock B (17 / 3) (1 / 4)
      blockErrSq 1 xc = omegaCeilE4M3 B * blockEnergy xc ∧
      blockErrSq 1 xn = omegaNearestE4M3 B * blockEnergy xn) ∧
    -- 4. Exact linear clipping margin where nearest-E4M3 beats ceil-E4M3 on the max entry:
    (∀ s_prev s_ceil M : Rat, s_prev < s_ceil →
      6 * s_prev < M → M < 3 * (s_prev + s_ceil) →
      sq (6 * s_ceil - M) - sq (M - 6 * s_prev) =
        12 * (s_ceil - s_prev) * (3 * (s_prev + s_ceil) - M) ∧
      0 < sq (6 * s_ceil - M) - sq (M - 6 * s_prev)) ∧
    -- 5. Exact NVFP4 B = 16 & B = 1 rational values and strict improvement ratios:
    (omegaCeilE4M3 16 = 199 / 4231 ∧
     omegaCeilE4M3Full 16 = 199 / 4231 ∧
     omegaNearestE4M3 16 = 151 / 4759 ∧
     omegaNearestE4M3Full 16 = 17 / 458 ∧
     (148 / 100 : Rat) * omegaNearestE4M3 16 < omegaCeilE4M3 16 ∧
     omegaNearestE4M3Full 16 < omegaCeilE4M3Full 16 ∧
     omegaCeilE4M3 1 = 1 / 64 ∧
     omegaNearestE4M3 1 = 1 / 289) := by
  have he1_qtr : e2m1ErrSq 1 (1 / 4) = 1 / 16 := by
    apply Rat.le_antisymm
    · have h := e2m1ErrSq_le_0 1 (1 / 4); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
    · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]; unfold sq
      apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
      apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
      apply rat_le_min (by grind); grind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ceil-E4M3 core bulk
    intro B M bulk hB hMlo hMhi hlen hbulk
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have hb1 : (1 : Rat) ≤ b := rat_natCast_le hB
    have hden : (0 : Rat) < 9 * b + 4087 := by grind
    have hw_mul : omegaCeilE4M3 B * (9 * b + 4087) = 9 * b + 55 := by
      unfold omegaCeilE4M3; exact rat_div_mul_cancel (Rat.ne_of_gt hden)
    have hw0 : (0 : Rat) ≤ omegaCeilE4M3 B := rat_div_nonneg (by grind) hden
    have hw1 : omegaCeilE4M3 B ≤ 1 := rat_div_le_of_mul_le hden (by grind)
    exact blockErrSq_1_le_of_M_and_bulk B hB (16 / 3) (omegaCeilE4M3 B) ((1 - omegaCeilE4M3 B) / 16)
      (by grind) (by grind) hw0 hw1
      (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by unfold sq; grind) (by grind))
      (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -36 * (9 * b + 55) + 252 * (b - 1)) (by grind) (by grind))
      M bulk hMlo hMhi hlen (fun u hu => e1_sub_wsq_le_core hw0 hw1 (hbulk u hu))
  · -- nearest-E4M3 core bulk
    intro B M bulk hB hMlo hMhi hlen hbulk
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have hb1 : (1 : Rat) ≤ b := rat_natCast_le hB
    have hden : (0 : Rat) < 9 * b + 4615 := by grind
    have hw_mul : omegaNearestE4M3 B * (9 * b + 4615) = 9 * b + 7 := by
      unfold omegaNearestE4M3; exact rat_div_mul_cancel (Rat.ne_of_gt hden)
    have hw0 : (0 : Rat) ≤ omegaNearestE4M3 B := rat_div_nonneg (by grind) hden
    have hw1 : omegaNearestE4M3 B ≤ 1 := rat_div_le_of_mul_le hden (by grind)
    exact blockErrSq_1_le_of_M_and_bulk B hB (17 / 3) (omegaNearestE4M3 B) ((1 - omegaNearestE4M3 B) / 16)
      (by grind) (by grind) hw0 hw1
      (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by unfold sq; grind) (by grind))
      (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -36 * (9 * b + 7) + 288 * (b - 1)) (by grind) (by grind))
      M bulk hMlo hMhi hlen (fun u hu => e1_sub_wsq_le_core hw0 hw1 (hbulk u hu))
  · -- ceil-E4M3 unrestricted
    intro B M bulk hB hMlo hMhi hlen hbulk
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have hb1 : (1 : Rat) ≤ b := rat_natCast_le hB
    by_cases h11 : B ≤ 11
    · have hw_eq : omegaCeilE4M3Full B = (9 * b - 5) / (225 * b + 31) := by
        unfold omegaCeilE4M3Full; simp only [h11, ite_true]; rfl
      rw [hw_eq]
      have hb11 : b ≤ 11 := rat_natCast_le h11
      have hden : (0 : Rat) < 225 * b + 31 := by grind
      let w : Rat := (9 * b - 5) / (225 * b + 31)
      have hw_mul : w * (225 * b + 31) = 9 * b - 5 := rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw0 : (0 : Rat) ≤ w := rat_div_nonneg (by grind) hden
      have hw1 : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      have hmax : max ((1 - w) / 16) (1 - 25 * w) = 1 - 25 * w := by
        show (if (1 - w) / 16 ≤ 1 - 25 * w then 1 - 25 * w else (1 - w) / 16) = 1 - 25 * w
        have hle : (1 - w) / 16 ≤ 1 - 25 * w :=
          rat_le_of_clear hden (poly := (1 / 16) * (216 * b + 36) - 156 - (216 * b + 36) + (216 * b + 36))
            (by grind) (by grind)
        simp only [hle, ite_true]
      exact blockErrSq_1_le_of_M_and_bulk B hB (16 / 3) w (1 - 25 * w)
        (by grind) (by grind) hw0 hw1
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by unfold sq; grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -36 * (9 * b - 5) + 156 * (b - 1)) (by grind) (by grind))
        M bulk hMlo hMhi hlen (fun u hu => by
          have := e1_sub_wsq_le_all hw0 hw1 (hbulk u hu); rw [hmax] at this; exact this)
    · have hw_eq : omegaCeilE4M3Full B = omegaCeilE4M3 B := by
        unfold omegaCeilE4M3Full; simp only [h11, ite_false]
      rw [hw_eq]
      have hb12 : (12 : Rat) ≤ b := rat_natCast_le (by omega : 12 ≤ B)
      have hden : (0 : Rat) < 9 * b + 4087 := by grind
      let w : Rat := omegaCeilE4M3 B
      have hw_mul : w * (9 * b + 4087) = 9 * b + 55 := by
        unfold w omegaCeilE4M3; exact rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw0 : (0 : Rat) ≤ w := rat_div_nonneg (by grind) hden
      have hw1 : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      have hmax : max ((1 - w) / 16) (1 - 25 * w) = (1 - w) / 16 := by
        show (if (1 - w) / 16 ≤ 1 - 25 * w then 1 - 25 * w else (1 - w) / 16) = (1 - w) / 16
        have hlt : 1 - 25 * w ≤ (1 - w) / 16 :=
          rat_le_of_clear hden (poly := (15 / 16) * (9 * b + 4087) - (399 / 16) * (9 * b + 55))
            (by grind) (by grind)
        split
        · rename_i hge; exact Rat.le_antisymm hlt hge
        · rfl
      exact blockErrSq_1_le_of_M_and_bulk B hB (16 / 3) w ((1 - w) / 16)
        (by grind) (by grind) hw0 hw1
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by unfold sq; grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -36 * (9 * b + 55) + 252 * (b - 1)) (by grind) (by grind))
        M bulk hMlo hMhi hlen (fun u hu => by
          have := e1_sub_wsq_le_all hw0 hw1 (hbulk u hu); rw [hmax] at this; exact this)
  · -- nearest-E4M3 unrestricted
    intro B M bulk hB hMlo hMhi hlen hbulk
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have hb1 : (1 : Rat) ≤ b := rat_natCast_le hB
    by_cases h19 : B ≤ 19
    · have hw_eq : omegaNearestE4M3Full B = (9 * b - 8) / (225 * b + 64) := by
        unfold omegaNearestE4M3Full; simp only [h19, ite_true]; rfl
      rw [hw_eq]
      have hb19 : b ≤ 19 := rat_natCast_le h19
      have hden : (0 : Rat) < 225 * b + 64 := by grind
      let w : Rat := (9 * b - 8) / (225 * b + 64)
      have hw_mul : w * (225 * b + 64) = 9 * b - 8 := rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw0 : (0 : Rat) ≤ w := rat_div_nonneg (by grind) hden
      have hw1 : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      have hmax : max ((1 - w) / 16) (1 - 25 * w) = 1 - 25 * w := by
        show (if (1 - w) / 16 ≤ 1 - 25 * w then 1 - 25 * w else (1 - w) / 16) = 1 - 25 * w
        have hle : (1 - w) / 16 ≤ 1 - 25 * w :=
          rat_le_of_clear hden (poly := (1 / 16) * (216 * b + 72) - 264)
            (by grind) (by grind)
        simp only [hle, ite_true]
      exact blockErrSq_1_le_of_M_and_bulk B hB (17 / 3) w (1 - 25 * w)
        (by grind) (by grind) hw0 hw1
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by unfold sq; grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -36 * (9 * b - 8) + 264 * (b - 1)) (by grind) (by grind))
        M bulk hMlo hMhi hlen (fun u hu => by
          have := e1_sub_wsq_le_all hw0 hw1 (hbulk u hu); rw [hmax] at this; exact this)
    · have hw_eq : omegaNearestE4M3Full B = omegaNearestE4M3 B := by
        unfold omegaNearestE4M3Full; simp only [h19, ite_false]
      rw [hw_eq]
      have hb20 : (20 : Rat) ≤ b := rat_natCast_le (by omega : 20 ≤ B)
      have hden : (0 : Rat) < 9 * b + 4615 := by grind
      let w : Rat := omegaNearestE4M3 B
      have hw_mul : w * (9 * b + 4615) = 9 * b + 7 := by
        unfold w omegaNearestE4M3; exact rat_div_mul_cancel (Rat.ne_of_gt hden)
      have hw0 : (0 : Rat) ≤ w := rat_div_nonneg (by grind) hden
      have hw1 : w ≤ 1 := rat_div_le_of_mul_le hden (by grind)
      have hmax : max ((1 - w) / 16) (1 - 25 * w) = (1 - w) / 16 := by
        show (if (1 - w) / 16 ≤ 1 - 25 * w then 1 - 25 * w else (1 - w) / 16) = (1 - w) / 16
        have hlt : 1 - 25 * w ≤ (1 - w) / 16 :=
          rat_le_of_clear hden (poly := (15 / 16) * (9 * b + 4615) - (399 / 16) * (9 * b + 7))
            (by grind) (by grind)
        split
        · rename_i hge; exact Rat.le_antisymm hlt hge
        · rfl
      exact blockErrSq_1_le_of_M_and_bulk B hB (17 / 3) w ((1 - w) / 16)
        (by grind) (by grind) hw0 hw1
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := 0) (by unfold sq; grind) (by grind))
        (by rw [hBcast]; exact rat_le_zero_of_clear hden (poly := -36 * (9 * b + 7) + 288 * (b - 1)) (by grind) (by grind))
        M bulk hMlo hMhi hlen (fun u hu => by
          have := e1_sub_wsq_le_all hw0 hw1 (hbulk u hu); rw [hmax] at this; exact this)
  · -- exact attainment witnesses
    intro B hB
    have hBcast : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := rat_natCast_sub hB
    let b : Rat := (B : Rat)
    have hb0 : (0 : Rat) ≤ b := rat_natCast_nonneg B
    constructor
    · dsimp only [mkSingleOutlierBlock]
      simp only [blockErrSq, blockErrSq_replicate, blockEnergy, blockEnergy_replicate,
        e2m1ErrSq_1_at_16_3, he1_qtr, hBcast]
      unfold omegaCeilE4M3 sq
      have hden : 9 * b + 4087 ≠ 0 := by grind
      have hmul := rat_div_mul_cancel (a := 9 * b + 55) hden
      grind
    · dsimp only [mkSingleOutlierBlock]
      simp only [blockErrSq, blockErrSq_replicate, blockEnergy, blockEnergy_replicate,
        e2m1ErrSq_1_at_17_3, he1_qtr, hBcast]
      unfold omegaNearestE4M3 sq
      have hden : 9 * b + 4615 ≠ 0 := by grind
      have hmul := rat_div_mul_cancel (a := 9 * b + 7) hden
      grind
  · -- exact linear clipping margin
    intro s_prev s_ceil M hlt hM1 hM2
    have hid : sq (6 * s_ceil - M) - sq (M - 6 * s_prev) =
        12 * (s_ceil - s_prev) * (3 * (s_prev + s_ceil) - M) := by unfold sq; grind
    refine ⟨hid, ?_⟩
    rw [hid]
    exact rat_mul_pos (rat_mul_pos (by grind) (rat_sub_pos hlt)) (rat_sub_pos hM2)
  · -- benchmark values
    have hc16 : omegaCeilE4M3 16 = 199 / 4231 := by unfold omegaCeilE4M3; grind
    have hcf16 : omegaCeilE4M3Full 16 = 199 / 4231 := by unfold omegaCeilE4M3Full; simp [hc16]
    have hn16 : omegaNearestE4M3 16 = 151 / 4759 := by unfold omegaNearestE4M3; grind
    have hnf16 : omegaNearestE4M3Full 16 = 17 / 458 := by unfold omegaNearestE4M3Full; simp; grind
    have hc1 : omegaCeilE4M3 1 = 1 / 64 := by unfold omegaCeilE4M3; grind
    have hn1 : omegaNearestE4M3 1 = 1 / 289 := by unfold omegaNearestE4M3; grind
    refine ⟨hc16, hcf16, hn16, hnf16, ?_, ?_, hc1, hn1⟩
    · rw [hn16, hc16]; grind
    · rw [hnf16, hcf16]; grind

/-! ### Helper Lemmas and Proof for Theorem 4 (`opt-E4M3` at `B = 16` and `B = 1` Synergy) -/

/-- Exact evaluation of `e2m1ErrSq (9/8) u` on `[6, 27/4]`: `e_{9/8}(u) = (27/4 - u)²`. -/
theorem e2m1ErrSq_9_8_on_6_27_4 {u : Rat} (hlo : (6 : Rat) ≤ u) (_hhi : u ≤ 27 / 4) :
    e2m1ErrSq (9 / 8) u = sq (u - 27 / 4) := by
  have hu0 : (0 : Rat) ≤ u := Rat.le_trans (by grind) hlo
  have habs : absRat u = u := absRat_of_nonneg hu0
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_6 (9 / 8) u; rw [habs] at h
    have hid : (9 / 8 : Rat) * 6 = 27 / 4 := by grind
    rw [hid] at h; exact h
  · unfold e2m1ErrSq; rw [habs]
    have hle : ∀ q : Rat, q ≤ 4 → sq (u - 27 / 4) ≤ sq (u - (9 / 8) * q) := by
      intro q hq
      have hpq : (9 / 8 : Rat) * q ≤ 27 / 4 := by grind
      have hmid : (9 / 8 : Rat) * q + 27 / 4 ≤ 2 * u := by grind
      exact sq_sub_le_of_mid_le hpq hmid
    apply rat_le_min
    · have h0 := hle 0 (by grind); grind
    apply rat_le_min (hle (1 / 2) (by grind))
    apply rat_le_min (hle 1 (by grind))
    apply rat_le_min (hle (3 / 2) (by grind))
    apply rat_le_min (hle 2 (by grind))
    apply rat_le_min (hle 3 (by grind))
    apply rat_le_min (hle 4 (by grind))
    have hid : (9 / 8 : Rat) * 6 = 27 / 4 := by grind
    rw [hid]; exact Rat.le_refl

/-- Coordinatewise bound for `s = 9/8` at `w = 23/887` on `|u| ≤ 2`: `e_{9/8}(u) - (23/887)*u² ≤ (81/1024)*(864/887)`. -/
theorem e9_8_sub_wsq_le_core {u : Rat} (hu : absRat u ≤ 2) :
    e2m1ErrSq (9 / 8) u - (23 / 887 : Rat) * sq u ≤ (81 / 1024 : Rat) * (864 / 887) := by
  rw [← sq_absRat u]
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  let w : Rat := 23 / 887
  let K : Rat := (81 / 1024 : Rat) * (864 / 887)
  have hstep : ∀ q l r : Rat, l ≤ a → a ≤ r →
      (e2m1ErrSq (9 / 8) u ≤ sq (a - q)) →
      sq (l - q) - w * sq l ≤ K →
      sq (r - q) - w * sq r ≤ K →
      e2m1ErrSq (9 / 8) u - w * sq a ≤ K := by
    intro q l r hl hr hle hfl hfr
    have hq := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * q) (C := q * q)
      (by grind) hl hr
      (by have hid : (1 - w) * (l * l) + (-2 * q) * l + q * q = sq (l - q) - w * sq l := by unfold sq; grind
          rw [hid]; exact hfl)
      (by have hid : (1 - w) * (r * r) + (-2 * q) * r + q * q = sq (r - q) - w * sq r := by unfold sq; grind
          rw [hid]; exact hfr)
    have hid : (1 - w) * (a * a) + (-2 * q) * a + q * q = sq (a - q) - w * sq a := by unfold sq; grind
    rw [hid] at hq
    have hsub : e2m1ErrSq (9 / 8) u - w * sq a ≤ sq (a - q) - w * sq a := by grind
    exact Rat.le_trans hsub hq
  cases Rat.le_total (a := a) (b := (9 / 32 : Rat)) with
  | inl h1 =>
    exact hstep 0 0 (9 / 32) ha0 h1 (e2m1ErrSq_le_0 (9 / 8) u)
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (27 / 32 : Rat)) with
    | inl h2 =>
      exact hstep (9 / 16) (9 / 32) (27 / 32) h1 h2
        (by have := e2m1ErrSq_le_half (9 / 8) u; grind)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (45 / 32 : Rat)) with
      | inl h3 =>
        exact hstep (9 / 8) (27 / 32) (45 / 32) h2 h3
          (by have := e2m1ErrSq_le_1 (9 / 8) u; grind)
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h3 =>
        cases Rat.le_total (a := a) (b := (63 / 32 : Rat)) with
        | inl h4 =>
          exact hstep (27 / 16) (45 / 32) (63 / 32) h3 h4
            (by have := e2m1ErrSq_le_3half (9 / 8) u; grind)
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h4 =>
          exact hstep (9 / 4) (63 / 32) 2 h4 hu
            (by have := e2m1ErrSq_le_2 (9 / 8) u; grind)
            (by unfold sq; grind) (by unfold sq; grind)

/-- Coordinatewise Lagrangian bound for `λ = 428/887`, `w = 23/887` on `|u| ≤ 2`. -/
theorem lam428_sub_wsq_le_core {u : Rat} (hu : absRat u ≤ 2) :
    let lam : Rat := 428 / 887
    let w : Rat := 23 / 887
    (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (9 / 8) u - w * sq u ≤ (1 - w) / 16 := by
  intro lam w
  rw [← sq_absRat u]
  let a := absRat u
  have ha0 : (0 : Rat) ≤ a := absRat_nonneg u
  let K : Rat := (1 - w) / 16
  have hstep : ∀ q1 q2 l r : Rat, l ≤ a → a ≤ r →
      (e2m1ErrSq 1 u ≤ sq (a - q1)) →
      (e2m1ErrSq (9 / 8) u ≤ sq (a - q2)) →
      (1 - lam) * sq (l - q1) + lam * sq (l - q2) - w * sq l ≤ K →
      (1 - lam) * sq (r - q1) + lam * sq (r - q2) - w * sq r ≤ K →
      (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (9 / 8) u - w * sq a ≤ K := by
    intro q1 q2 l r hl hr hq1 hq2 hfl hfr
    have h1 := rat_mul_le_mul_of_nonneg_left hq1 (by grind : (0 : Rat) ≤ 1 - lam)
    have h2 := rat_mul_le_mul_of_nonneg_left hq2 (by grind : (0 : Rat) ≤ lam)
    have hle : (1 - lam) * e2m1ErrSq 1 u + lam * e2m1ErrSq (9 / 8) u - w * sq a ≤
        (1 - lam) * sq (a - q1) + lam * sq (a - q2) - w * sq a := by grind
    have hquad_eq : ∀ t : Rat,
        (1 - w) * (t * t) + (-2 * ((1 - lam) * q1 + lam * q2)) * t +
          ((1 - lam) * (q1 * q1) + lam * (q2 * q2)) =
        (1 - lam) * sq (t - q1) + lam * sq (t - q2) - w * sq t := by
      intro t; unfold sq; grind
    have hc := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * ((1 - lam) * q1 + lam * q2))
      (C := (1 - lam) * (q1 * q1) + lam * (q2 * q2)) (by grind) hl hr
      (by rw [hquad_eq]; exact hfl) (by rw [hquad_eq]; exact hfr)
    rw [hquad_eq] at hc
    exact Rat.le_trans hle hc
  cases Rat.le_total (a := a) (b := (1 / 4 : Rat)) with
  | inl h1 =>
    exact hstep 0 0 0 (1 / 4) ha0 h1 (e2m1ErrSq_le_0 1 u) (e2m1ErrSq_le_0 (9 / 8) u)
      (by unfold sq; grind) (by unfold sq; grind)
  | inr h1 =>
    cases Rat.le_total (a := a) (b := (9 / 32 : Rat)) with
    | inl h2 =>
      exact hstep (1 / 2) 0 (1 / 4) (9 / 32) h1 h2
        (by have := e2m1ErrSq_le_half 1 u; grind) (e2m1ErrSq_le_0 (9 / 8) u)
        (by unfold sq; grind) (by unfold sq; grind)
    | inr h2 =>
      cases Rat.le_total (a := a) (b := (3 / 4 : Rat)) with
      | inl h3 =>
        exact hstep (1 / 2) (9 / 16) (9 / 32) (3 / 4) h2 h3
          (by have := e2m1ErrSq_le_half 1 u; grind) (by have := e2m1ErrSq_le_half (9 / 8) u; grind)
          (by unfold sq; grind) (by unfold sq; grind)
      | inr h3 =>
        cases Rat.le_total (a := a) (b := (27 / 32 : Rat)) with
        | inl h4 =>
          exact hstep 1 (9 / 16) (3 / 4) (27 / 32) h3 h4
            (by have := e2m1ErrSq_le_1 1 u; grind) (by have := e2m1ErrSq_le_half (9 / 8) u; grind)
            (by unfold sq; grind) (by unfold sq; grind)
        | inr h4 =>
          cases Rat.le_total (a := a) (b := (5 / 4 : Rat)) with
          | inl h5 =>
            exact hstep 1 (9 / 8) (27 / 32) (5 / 4) h4 h5
              (by have := e2m1ErrSq_le_1 1 u; grind) (by have := e2m1ErrSq_le_1 (9 / 8) u; grind)
              (by unfold sq; grind) (by unfold sq; grind)
          | inr h5 =>
            cases Rat.le_total (a := a) (b := (45 / 32 : Rat)) with
            | inl h6 =>
              exact hstep (3 / 2) (9 / 8) (5 / 4) (45 / 32) h5 h6
                (by have := e2m1ErrSq_le_3half 1 u; grind) (by have := e2m1ErrSq_le_1 (9 / 8) u; grind)
                (by unfold sq; grind) (by unfold sq; grind)
            | inr h6 =>
              cases Rat.le_total (a := a) (b := (7 / 4 : Rat)) with
              | inl h7 =>
                exact hstep (3 / 2) (27 / 16) (45 / 32) (7 / 4) h6 h7
                  (by have := e2m1ErrSq_le_3half 1 u; grind) (by have := e2m1ErrSq_le_3half (9 / 8) u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)
              | inr h7 =>
                exact hstep 2 (27 / 16) (7 / 4) 2 h7 hu
                  (by have := e2m1ErrSq_le_2 1 u; grind) (by have := e2m1ErrSq_le_3half (9 / 8) u; grind)
                  (by unfold sq; grind) (by unfold sq; grind)

theorem e2m1ErrSq_1_at_9_32 : e2m1ErrSq 1 (9 / 32) = 49 / 1024 := by
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_half 1 (9 / 32); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]; unfold sq
    apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
    apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
    apply rat_le_min (by grind); grind

theorem e2m1ErrSq_9_8_at_9_32 : e2m1ErrSq (9 / 8) (9 / 32) = 81 / 1024 := by
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_0 (9 / 8) (9 / 32); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
  · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]; unfold sq
    apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
    apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
    apply rat_le_min (by grind); grind

/-- Theorem 4: Exact NVFP4 `opt-E4M3` at `B = 16` (`23/887`) and `B = 1` Non-Top-Level Scale Synergy (`1/625`). -/
theorem nvfp4_opt_e4m3_b16_and_b1_synergy_exact :
    -- 1. Universal B = 16 opt-E4M3 upper bound 23/887 for all M ∈ [6, 27/4] and core bulk |u| ≤ 2:
    (∀ (M : Rat) (bulk : List Rat),
      6 ≤ absRat M → absRat M ≤ 27 / 4 → bulk.length = 15 → (∀ u ∈ bulk, absRat u ≤ 2) →
      min (blockErrSq 1 (M :: bulk)) (blockErrSq (9 / 8) (M :: bulk)) ≤
        (23 / 887 : Rat) * blockEnergy (M :: bulk)) ∧
    -- 2. Exact B = 16 attainment witness at (M = 107/16, u = 9/32):
    (let x := mkSingleOutlierBlock 16 (107 / 16) (9 / 32)
     x.length = 16 ∧
     blockErrSq 1 x = 1219 / 1024 ∧
     blockErrSq (9 / 8) x = 1219 / 1024 ∧
     blockEnergy x = 47011 / 1024 ∧
     min (blockErrSq 1 x) (blockErrSq (9 / 8) x) = (23 / 887 : Rat) * blockEnergy x ∧
     (181 / 100 : Rat) * (23 / 887 : Rat) < omegaCeilE4M3 16) ∧
    -- 3. Exact B = 1 non-top-level scale synergy on [6, 27/4]: s = 13/8 maps M to 4 * (13/8) = 13/2!
    (∀ M : Rat, 6 ≤ M → M ≤ 27 / 4 →
      min (e2m1ErrSq 1 M) (min (e2m1ErrSq (9 / 8) M) (e2m1ErrSq (13 / 8) M)) ≤
        (1 / 625 : Rat) * sq M) ∧
    -- 4. Exact B = 1 attainment at M = 25/4 (1/625 vs nearest 1/289 vs ceil 1/64):
    (e2m1ErrSq 1 (25 / 4) = 1 / 16 ∧
     e2m1ErrSq (13 / 8) (25 / 4) = 1 / 16 ∧
     e2m1ErrSq (9 / 8) (25 / 4) = 1 / 4 ∧
     min (e2m1ErrSq 1 (25 / 4)) (min (e2m1ErrSq (9 / 8) (25 / 4)) (e2m1ErrSq (13 / 8) (25 / 4))) =
       (1 / 625 : Rat) * sq (25 / 4) ∧
     (976 / 100 : Rat) * (1 / 625 : Rat) < (1 / 64 : Rat) ∧
     (216 / 100 : Rat) * (1 / 625 : Rat) < (1 / 289 : Rat)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Universal B = 16 bound 23/887
    intro M bulk hMlo hMhi hlen hbulk
    let w : Rat := 23 / 887
    let a := absRat M
    have he1M : e2m1ErrSq 1 M = sq (a - 6) := by
      rw [← e2m1ErrSq_abs]; exact e2m1ErrSq_1_on_ge_5 (Rat.le_trans (by grind) hMlo)
    have he98M : e2m1ErrSq (9 / 8) M = sq (a - 27 / 4) := by
      rw [← e2m1ErrSq_abs]; exact e2m1ErrSq_9_8_on_6_27_4 hMlo hMhi
    cases Rat.le_total (a := a) (b := (51 / 8 : Rat)) with
    | inl h51 =>
      -- Pure s = 1
      apply Rat.le_trans (rat_min_le_left _ _)
      have hM_bound : e2m1ErrSq 1 M - w * sq M ≤ -15 * ((1 - w) / 16) := by
        rw [he1M, ← sq_absRat M]
        have hc := convex_quad_le_of_endpoints (A := 1 - w) (B := -12) (C := 36)
          (K := -15 * ((1 - w) / 16)) (by grind) hMlo h51 (by grind) (by grind)
        have hid : (1 - w) * (a * a) + (-12) * a + 36 = sq (a - 6) - w * sq a := by unfold sq; grind
        rw [← hid]; exact hc
      have hsum : blockErrSq 1 bulk - w * blockEnergy bulk ≤ (bulk.length : Rat) * ((1 - w) / 16) :=
        blockErrSq_sub_wEnergy_le_len bulk (fun u hu => e1_sub_wsq_le_core (w := w) (by grind) (by grind) (hbulk u hu))
      rw [hlen] at hsum
      simp only [blockErrSq, blockEnergy]
      grind
    | inr h51 =>
      cases Rat.le_total (a := a) (b := (107 / 16 : Rat)) with
      | inl h107 =>
        -- Lagrangian lam = 428/887
        let lam : Rat := 428 / 887
        apply rat_min_le_of_convex (lam := lam) (by grind) (by grind)
        have hM_bound : (1 - lam) * e2m1ErrSq 1 M + lam * e2m1ErrSq (9 / 8) M - w * sq M ≤
            -15 * ((1 - w) / 16) := by
          rw [he1M, he98M, ← sq_absRat M]
          have hquad_eq : ∀ t : Rat,
              (1 - w) * (t * t) + (-2 * ((1 - lam) * 6 + lam * (27 / 4))) * t +
                ((1 - lam) * 36 + lam * ((27 / 4) * (27 / 4))) =
              (1 - lam) * sq (t - 6) + lam * sq (t - 27 / 4) - w * sq t := by
            intro t; unfold sq; grind
          have hc := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * ((1 - lam) * 6 + lam * (27 / 4)))
            (C := (1 - lam) * 36 + lam * ((27 / 4) * (27 / 4))) (K := -15 * ((1 - w) / 16))
            (by grind) h51 h107
            (by rw [hquad_eq]; unfold sq; grind) (by rw [hquad_eq]; unfold sq; grind)
          rw [hquad_eq] at hc; exact hc
        have hsum : (1 - lam) * blockErrSq 1 bulk + lam * blockErrSq (9 / 8) bulk - w * blockEnergy bulk ≤
            (bulk.length : Rat) * ((1 - w) / 16) :=
          convex_blockErrSq_sub_wEnergy_le_len bulk (fun u hu => lam428_sub_wsq_le_core (hbulk u hu))
        rw [hlen] at hsum
        simp only [blockErrSq, blockEnergy]
        grind
      | inr h107 =>
        -- Pure s = 9/8
        apply Rat.le_trans (rat_min_le_right _ _)
        let K : Rat := (81 / 1024 : Rat) * (864 / 887)
        have hM_bound : e2m1ErrSq (9 / 8) M - w * sq M ≤ -15 * K := by
          rw [he98M, ← sq_absRat M]
          have hquad_eq : ∀ t : Rat,
              (1 - w) * (t * t) + (-2 * (27 / 4)) * t + (27 / 4) * (27 / 4) =
              sq (t - 27 / 4) - w * sq t := by intro t; unfold sq; grind
          have hc := convex_quad_le_of_endpoints (A := 1 - w) (B := -2 * (27 / 4))
            (C := (27 / 4) * (27 / 4)) (K := -15 * K) (by grind) h107 hMhi
            (by rw [hquad_eq]; unfold sq; grind) (by rw [hquad_eq]; unfold sq; grind)
          rw [hquad_eq] at hc; exact hc
        have hsum : blockErrSq (9 / 8) bulk - w * blockEnergy bulk ≤ (bulk.length : Rat) * K :=
          blockErrSq_sub_wEnergy_le_len bulk (fun u hu => e9_8_sub_wsq_le_core (hbulk u hu))
        rw [hlen] at hsum
        simp only [blockErrSq, blockEnergy]
        grind
  · -- Exact B = 16 witness
    dsimp only [mkSingleOutlierBlock]
    have hlen : ((107 / 16 : Rat) :: List.replicate 15 (9 / 32 : Rat)).length = 16 := by simp
    have he1M : e2m1ErrSq 1 (107 / 16) = 121 / 256 := by
      rw [e2m1ErrSq_1_on_ge_5 (by grind)]; unfold sq; grind
    have he98M : e2m1ErrSq (9 / 8) (107 / 16) = 1 / 256 := by
      rw [e2m1ErrSq_9_8_on_6_27_4 (by grind) (by grind)]; unfold sq; grind
    have he1 : blockErrSq 1 ((107 / 16 : Rat) :: List.replicate 15 (9 / 32 : Rat)) = 1219 / 1024 := by
      simp only [blockErrSq, blockErrSq_replicate, he1M, e2m1ErrSq_1_at_9_32]; grind
    have he98 : blockErrSq (9 / 8) ((107 / 16 : Rat) :: List.replicate 15 (9 / 32 : Rat)) = 1219 / 1024 := by
      simp only [blockErrSq, blockErrSq_replicate, he98M, e2m1ErrSq_9_8_at_9_32]; grind
    have hen : blockEnergy ((107 / 16 : Rat) :: List.replicate 15 (9 / 32 : Rat)) = 47011 / 1024 := by
      simp only [blockEnergy, blockEnergy_replicate]; unfold sq; grind
    refine ⟨hlen, he1, he98, hen, ?_, ?_⟩
    · rw [he1, he98, hen, rat_min_eq_left Rat.le_refl]; grind
    · unfold omegaCeilE4M3; grind
  · -- Exact B = 1 non-top-level scale synergy on [6, 27/4]
    intro M hlo hhi
    have hM0 : (0 : Rat) ≤ M := by grind
    have habs : absRat M = M := absRat_of_nonneg hM0
    cases Rat.le_total (a := M) (b := (25 / 4 : Rat)) with
    | inl h25 =>
      apply Rat.le_trans (rat_min_le_left _ _)
      have h1 : e2m1ErrSq 1 M ≤ sq (M - 6) := by
        have := e2m1ErrSq_le_6 1 M; rw [habs] at this; grind
      have hc := convex_quad_le_of_endpoints (A := 1 - 1 / 625) (B := -12) (C := 36) (K := 0)
        (by grind) hlo h25 (by grind) (by grind)
      have hid : (1 - (1 / 625 : Rat)) * (M * M) + (-12) * M + 36 = sq (M - 6) - (1 / 625) * sq M := by
        unfold sq; grind
      rw [hid] at hc; grind
    | inr h25 =>
      cases Rat.le_total (a := M) (b := (53 / 8 : Rat)) with
      | inl h53 =>
        apply Rat.le_trans (rat_min_le_right _ _)
        apply Rat.le_trans (rat_min_le_right _ _)
        have h4 : e2m1ErrSq (13 / 8) M ≤ sq (M - 13 / 2) := by
          have := e2m1ErrSq_le_4 (13 / 8) M; rw [habs] at this; grind
        have hc := convex_quad_le_of_endpoints (A := 1 - 1 / 625) (B := -13) (C := (13 / 2) * (13 / 2)) (K := 0)
          (by grind) h25 h53 (by grind) (by grind)
        have hid : (1 - (1 / 625 : Rat)) * (M * M) + (-13) * M + (13 / 2) * (13 / 2) =
            sq (M - 13 / 2) - (1 / 625) * sq M := by unfold sq; grind
        rw [hid] at hc; grind
      | inr h53 =>
        apply Rat.le_trans (rat_min_le_right _ _)
        apply Rat.le_trans (rat_min_le_left _ _)
        have h6 : e2m1ErrSq (9 / 8) M ≤ sq (M - 27 / 4) := by
          have := e2m1ErrSq_le_6 (9 / 8) M; rw [habs] at this; grind
        have hc := convex_quad_le_of_endpoints (A := 1 - 1 / 625) (B := -(27 / 2)) (C := (27 / 4) * (27 / 4)) (K := 0)
          (by grind) h53 hhi (by grind) (by grind)
        have hid : (1 - (1 / 625 : Rat)) * (M * M) + (-(27 / 2)) * M + (27 / 4) * (27 / 4) =
            sq (M - 27 / 4) - (1 / 625) * sq M := by unfold sq; grind
        rw [hid] at hc; grind
  · -- Exact B = 1 attainment at M = 25/4
    have h1 : e2m1ErrSq 1 (25 / 4) = 1 / 16 := by
      rw [e2m1ErrSq_1_on_ge_5 (by grind)]; unfold sq; grind
    have h98 : e2m1ErrSq (9 / 8) (25 / 4) = 1 / 4 := by
      rw [e2m1ErrSq_9_8_on_6_27_4 (by grind) (by grind)]; unfold sq; grind
    have h138 : e2m1ErrSq (13 / 8) (25 / 4) = 1 / 16 := by
      apply Rat.le_antisymm
      · have h := e2m1ErrSq_le_4 (13 / 8) (25 / 4); rw [absRat_of_nonneg (by grind)] at h; unfold sq at h; grind
      · unfold e2m1ErrSq; rw [absRat_of_nonneg (by grind)]; unfold sq
        apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
        apply rat_le_min (by grind); apply rat_le_min (by grind); apply rat_le_min (by grind)
        apply rat_le_min (by grind); grind
    refine ⟨h1, h138, h98, ?_, by grind, by grind⟩
    rw [h1, h98, h138]
    rw [rat_min_eq_right (by grind : (1 / 16 : Rat) ≤ 1 / 4), rat_min_eq_left Rat.le_refl]
    unfold sq; grind

end Mxfp4OptClipping
