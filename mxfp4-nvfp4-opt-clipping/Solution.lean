/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp4OptClipping

/-!
# Verified Solutions (`mxfp4-nvfp4-opt-clipping`)
-/

namespace Mxfp4OptClippingChallenge

open Mxfp4OptClipping

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
    (∀ M Δ : Rat, 3 ≤ M → M ≤ 6 → 9 < Δ → clipPenalty M < Δ) :=
  Mxfp4OptClipping.mxfp4_e8m0_scale_down_piecewise_linear_crossover

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
     (5 / 2 : Rat) * omegaOptE8M0 145 = 1 / 2) :=
  Mxfp4OptClipping.mxfp4_opt_e8m0_all_b_ef21_three_regime_law

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
     omegaNearestE4M3 1 = 1 / 289) :=
  Mxfp4OptClipping.nvfp4_ceil_vs_nearest_e4m3_all_b_ef21_exact

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
     (216 / 100 : Rat) * (1 / 625 : Rat) < (1 / 289 : Rat)) :=
  Mxfp4OptClipping.nvfp4_opt_e4m3_b16_and_b1_synergy_exact

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
      blockErrSq (1 / 2) (6 :: bulk) < blockErrSq s (6 :: bulk)) :=
  Mxfp4OptClipping.mxfp4_opt_e8m0_never_drops_two_exponents

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
     (∀ u : Rat, 4 ≤ u → u ≤ 6 → e2m1PlusErrSq 5 1 u ≤ 1 / 4)) :=
  Mxfp4OptClipping.e2m1_neg_zero_repurposing_exact_gain

end Mxfp4OptClippingChallenge
