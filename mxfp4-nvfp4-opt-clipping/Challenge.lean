/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp4OptClipping.Defs

/-!
# Trusted Challenge Statements (`mxfp4-nvfp4-opt-clipping`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. MXFP4 (`E2M1 + E8M0`) exact piecewise-linear scale-down crossover law `Φ(M)`.
2. MXFP4 `opt-E8M0` universal all-`B` 3-regime EF21 minimax contraction law (`47/431` at `B = 32`,
   `23/151` at `B = 64`, `1/5` at `B = 145`).
3. NVFP4 (`E2M1 + E4M3`) `ceil-E4M3` vs zero-search `nearest-E4M3` universal all-`B` EF21 contraction
   laws (`199/4231` vs `151/4759` at `B = 16`, plus unrestricted `u = 5` phase transitions and exact
   linear clipping margin).
4. NVFP4 `opt-E4M3` exact `B = 16` minimax bound (`23/887`) and `B = 1` non-top-level scale synergy
   (`1/625` vs `1/289` vs `1/64`).
5. MXFP4 `opt-E8M0` exact dominance theorem explaining why `e ≤ e_ceil - 2` never wins (`9/4`
   clipping-loss floor and exact `B = 32` dominance corollaries).
6. OCP E2M1 `-0` (`0b1000`) repurposing exact EF21 / MSE gains (`c = 8`, `c = 1/4`, `c = 5`).
-/

namespace Mxfp4OptClippingChallenge

open Mxfp4OptClipping

/-- Theorem 1 (Exact MXFP4 `E2M1 + E8M0` Piecewise-Linear Scale-Down Crossover Law):
    Proves that for a normalized outlier `M ∈ (3, 6]` (`e_ceil = 0`), the clipping-minus-rounding
    cost `Φ(M) = (M - 3)² - e₁(M)` collapses identically to piecewise-linear form (`0` on `[3, 7/2]`,
    `2M - 7` on `[7/2, 5]`, `6M - 27` on `[5, 6]`), proves the exact block-level necessary & sufficient
    condition `blockErrSq (1/2) x < blockErrSq 1 x ↔ clipCost x < bulkGain x` for all blocks `x`,
    and proves the exact single-outlier threshold corollaries. -/
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
  sorry

/-- Theorem 2 (Exact MXFP4 `opt-E8M0` All-`B` Three-Regime EF21 Minimax Law):
    For every block size `B ≥ 1` and every block `x` of length `B` with normalized max `M ∈ [3, 6]`,
    proves `min(E₁(x), E_{1/2}(x)) ≤ omegaOptE8M0 B * ‖x‖₂²`, where `omegaOptE8M0 B` is
    `(B + 15)/(B + 399)` for `1 ≤ B ≤ 49`, `(B + 143)²/(B² + 1438 B + 185185)` for `49 < B ≤ 145`,
    and `(B - 1)/(B + 575)` for `B ≥ 145`, together with exact attainment witnesses for all `B ≥ 1`
    and exact `B ∈ {32, 64, 145}` comparisons (`47/431` vs `31/175`, `23/151` vs `7/23`, `1/5` vs `1/2`). -/
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
  sorry

/-- Theorem 3 (Exact NVFP4 `ceil-E4M3` vs Zero-Search `nearest-E4M3` All-`B` EF21 Law):
    For every `B ≥ 1`, proves the exact core-bulk (`|u| ≤ 2`) and unrestricted (`|u| ≤ 6`) universal
    upper bounds for `ceil-E4M3` (`(9B + 55)/(9B + 4087)`, `199/4231` at `B = 16`) and `nearest-E4M3`
    (`(9B + 7)/(9B + 4615)`, `151/4759` at `B = 16`, `> 1.48x` tighter with zero search overhead),
    exact attainment witnesses for all `B ≥ 1`, and the exact linear clipping margin identity. -/
theorem nvfp4_ceil_vs_nearest_e4m3_all_b_ef21_exact :
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      16 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 2) →
      blockErrSq 1 (M :: bulk) ≤ omegaCeilE4M3 B * blockEnergy (M :: bulk)) ∧
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      17 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 2) →
      blockErrSq 1 (M :: bulk) ≤ omegaNearestE4M3 B * blockEnergy (M :: bulk)) ∧
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      16 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 6) →
      blockErrSq 1 (M :: bulk) ≤ omegaCeilE4M3Full B * blockEnergy (M :: bulk)) ∧
    (∀ (B : Nat) (M : Rat) (bulk : List Rat), 1 ≤ B →
      17 / 3 ≤ absRat M → absRat M ≤ 6 → bulk.length = B - 1 → (∀ u ∈ bulk, absRat u ≤ 6) →
      blockErrSq 1 (M :: bulk) ≤ omegaNearestE4M3Full B * blockEnergy (M :: bulk)) ∧
    (∀ B : Nat, 1 ≤ B →
      let xc := mkSingleOutlierBlock B (16 / 3) (1 / 4)
      let xn := mkSingleOutlierBlock B (17 / 3) (1 / 4)
      blockErrSq 1 xc = omegaCeilE4M3 B * blockEnergy xc ∧
      blockErrSq 1 xn = omegaNearestE4M3 B * blockEnergy xn) ∧
    (∀ s_prev s_ceil M : Rat, s_prev < s_ceil →
      6 * s_prev < M → M < 3 * (s_prev + s_ceil) →
      sq (6 * s_ceil - M) - sq (M - 6 * s_prev) =
        12 * (s_ceil - s_prev) * (3 * (s_prev + s_ceil) - M) ∧
      0 < sq (6 * s_ceil - M) - sq (M - 6 * s_prev)) ∧
    (omegaCeilE4M3 16 = 199 / 4231 ∧
     omegaCeilE4M3Full 16 = 199 / 4231 ∧
     omegaNearestE4M3 16 = 151 / 4759 ∧
     omegaNearestE4M3Full 16 = 17 / 458 ∧
     (148 / 100 : Rat) * omegaNearestE4M3 16 < omegaCeilE4M3 16 ∧
     omegaNearestE4M3Full 16 < omegaCeilE4M3Full 16 ∧
     omegaCeilE4M3 1 = 1 / 64 ∧
     omegaNearestE4M3 1 = 1 / 289) := by
  sorry

/-- Theorem 4 (Exact NVFP4 `opt-E4M3` at `B = 16` (`23/887`) and `B = 1` Non-Top-Level Scale Synergy (`1/625`)):
    Proves the universal `B = 16` `opt-E4M3` minimax bound `23/887` (`> 1.81x` tighter than `ceil-E4M3`)
    with exact attainment at `(M = 107/16, u = 9/32)`, and proves `B = 1` non-top-level scale synergy
    (`s = 13/8 > s_ceil = 9/8` mapping `M` to `4s = 13/2`) achieves exact worst-case `1/625` vs
    `1/289` (`nearest`) and `1/64` (`ceil`), attained at `M = 25/4`. -/
theorem nvfp4_opt_e4m3_b16_and_b1_synergy_exact :
    (∀ (M : Rat) (bulk : List Rat),
      6 ≤ absRat M → absRat M ≤ 27 / 4 → bulk.length = 15 → (∀ u ∈ bulk, absRat u ≤ 2) →
      min (blockErrSq 1 (M :: bulk)) (blockErrSq (9 / 8) (M :: bulk)) ≤
        (23 / 887 : Rat) * blockEnergy (M :: bulk)) ∧
    (let x := mkSingleOutlierBlock 16 (107 / 16) (9 / 32)
     x.length = 16 ∧
     blockErrSq 1 x = 1219 / 1024 ∧
     blockErrSq (9 / 8) x = 1219 / 1024 ∧
     blockEnergy x = 47011 / 1024 ∧
     min (blockErrSq 1 x) (blockErrSq (9 / 8) x) = (23 / 887 : Rat) * blockEnergy x ∧
     (181 / 100 : Rat) * (23 / 887 : Rat) < omegaCeilE4M3 16) ∧
    (∀ M : Rat, 6 ≤ M → M ≤ 27 / 4 →
      min (e2m1ErrSq 1 M) (min (e2m1ErrSq (9 / 8) M) (e2m1ErrSq (13 / 8) M)) ≤
        (1 / 625 : Rat) * sq M) ∧
    (e2m1ErrSq 1 (25 / 4) = 1 / 16 ∧
     e2m1ErrSq (13 / 8) (25 / 4) = 1 / 16 ∧
     e2m1ErrSq (9 / 8) (25 / 4) = 1 / 4 ∧
     min (e2m1ErrSq 1 (25 / 4)) (min (e2m1ErrSq (9 / 8) (25 / 4)) (e2m1ErrSq (13 / 8) (25 / 4))) =
       (1 / 625 : Rat) * sq (25 / 4) ∧
     (976 / 100 : Rat) * (1 / 625 : Rat) < (1 / 64 : Rat) ∧
     (216 / 100 : Rat) * (1 / 625 : Rat) < (1 / 289 : Rat)) := by
  sorry

/-- Theorem 5 (Exact Dominance Theorem — Why `opt-E8M0` Never Drops Two Exponents `e ≤ e_ceil - 2`):
    Proves that for any `M > 3` and any scale `0 ≤ s ≤ 1/4`, the extra clipping loss over `s = 1/2`
    equals `(3 - 6s)(2M - 3 - 6s) ≥ 3M - 27/4 > 9/4`, strictly dominating `s ≤ 1/4` whenever bulk
    MSE at `s = 1/2` is below `3M - 27/4` — in particular for ALL blocks with `B ≤ 145` (fine core
    `|u| ≤ 1`), ALL blocks with `B ≤ 37` (wide core `|u| ≤ 2`, covering OCP MXFP4 `B = 32`), and
    ALL unrestricted blocks with `B ≤ 45` at `M = 6`. -/
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
  sorry

/-- Theorem 6 (Exact E2M1 `-0` (`0b1000`) Repurposing Gains for `c ∈ {8, 1/4, 5}`):
    Proves universal all-`B` exact EF21 worst-case bounds and attainment witnesses for repurposing
    the redundant OCP E2M1 `-0` code to `c = 8` (`47/431` at `B = 32`, matching `opt-E8M0` with zero
    search!), `c = 1/4` (`95/1631` at `B = 32`, `> 3.04x` tighter than baseline `31/175` on deadzone
    bulk!), and `c = 5` (`B = 1` worst-case drops from `1/25` to `1/49`, `4x` peak error reduction
    on `[4, 6]`). -/
theorem e2m1_neg_zero_repurposing_exact_gain :
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
    (∀ M : Rat, 3 ≤ M → M ≤ 6 → e2m1PlusErrSq 5 1 M ≤ (1 / 49 : Rat) * sq M) ∧
    (e2m1PlusErrSq 5 1 (7 / 2) = (1 / 49 : Rat) * sq (7 / 2) ∧
     (∀ u : Rat, 4 ≤ u → u ≤ 6 → e2m1PlusErrSq 5 1 u ≤ 1 / 4)) := by
  sorry

end Mxfp4OptClippingChallenge
