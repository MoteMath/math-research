/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relu2TealDeadzone

/-!
# Verified Solutions (`relu2-teal-deadzone-bounds`)
-/

namespace Relu2TealDeadzoneChallenge

open Relu2TealDeadzone

theorem relu2_exact_kurtosis_seventy_thirds_and_outlier_amplification :
    (∀ (n : Nat) (w x : Fin n → Rat),
      (∀ i, (0 : Rat) ≤ x i) →
      symExpect w x sq = 1 →
      symExpect w x pow4 = 3 →
      symExpect w x pow8 = 105 →
      kurtosis (symExpect w x sq) (symExpect w x pow4) = 3 ∧
      kurtosis (symExpect w x (fun t => sq (relu t)))
               (symExpect w x (fun t => pow4 (relu t))) = 6 ∧
      kurtosis (symExpect w x (fun t => sq (relu2 t)))
               (symExpect w x (fun t => pow4 (relu2 t))) = 70 / 3) ∧
    (∀ (n : Nat) (p c : Rat) (w x : Fin n → Rat),
      (0 : Rat) ≤ c →
      (∀ i, (0 : Rat) ≤ x i) →
      mixSymExpect p c w x (fun t => sq (relu t)) =
        ((1 - p) + p * sq c) * (symExpect w x sq / 2) ∧
      mixSymExpect p c w x (fun t => pow4 (relu t)) =
        ((1 - p) + p * pow4 c) * (symExpect w x pow4 / 2) ∧
      mixSymExpect p c w x (fun t => sq (relu2 t)) =
        ((1 - p) + p * pow4 c) * (symExpect w x pow4 / 2) ∧
      mixSymExpect p c w x (fun t => pow4 (relu2 t)) =
        ((1 - p) + p * pow8 c) * (symExpect w x pow8 / 2)) ∧
    (∀ (p c : Rat), (0 : Rat) < p → (1 : Rat) < c →
      p * pow4 c < p * pow8 c ∧
      (p * pow8 c) / (p * pow4 c) = pow4 c) ∧
    (kurtosis (((1 - 1 / 100 : Rat) + (1 / 100) * sq 4) * (1 / 2))
              (((1 - 1 / 100 : Rat) + (1 / 100) * pow4 4) * (3 / 2)) = 8520 / 529 ∧
     kurtosis (((1 - 1 / 100 : Rat) + (1 / 100) * pow4 4) * (3 / 2))
              (((1 - 1 / 100 : Rat) + (1 / 100) * pow8 4) * (105 / 2)) = 18377800 / 15123 ∧
     (1215 : Rat) < 18377800 / 15123 ∧
     (75 : Rat) * (8520 / 529) < 18377800 / 15123) :=
  Relu2TealDeadzone.relu2_exact_kurtosis_seventy_thirds_and_outlier_amplification

theorem relu2_quantization_order_uniform_pre_beats_post :
    (∀ M N : Rat, (0 : Rat) < M → (0 : Rat) < N →
      postZeroCutoffSq M N / sq (preZeroCutoff M N) = 2 * N) ∧
    ((2 * (15 : Rat) = 30 ∧ sq 5 < 30) ∧
     (2 * (7 : Rat) = 14 ∧ sq 3 < 14)) ∧
    (∀ M N x uhat : Rat, (0 : Rat) < M → (0 : Rat) < N → (0 : Rat) ≤ x →
      ratAbs (uhat - x) ≤ preZeroCutoff M N →
      ratAbs (sq uhat - sq x) ≤ preMaxErr M N x) ∧
    (∀ M N x : Rat, (0 : Rat) < M → (0 : Rat) < N →
      (preMaxErr M N x < postMaxErr M N ↔ x < M * (1 / 2 - 1 / (4 * N)))) ∧
    ((1 / 2 - 1 / (4 * 15) : Rat) = 29 / 60) ∧
    (∀ M N c : Rat, (0 : Rat) < M → (0 : Rat) < N → (0 : Rat) < c →
      preMaxErr M N (M / c) / postMaxErr M N = 2 / c + 1 / (2 * N)) ∧
    (((2 / 4 + 1 / (2 * 15) : Rat) = 8 / 15) ∧
     sq (8 / 15 : Rat) = 64 / 225 ∧
     (64 / 225 : Rat) < 1 / 3) :=
  Relu2TealDeadzone.relu2_quantization_order_uniform_pre_beats_post

theorem relu2_quantization_order_fp_post_beats_pre_exact_4x :
    (∀ u delta : Rat,
      sq (u * (1 + delta)) - sq u = sq u * (2 * delta + sq delta) ∧
      sq (u * (1 + delta)) - sq u = sq u * delta * (2 + delta)) ∧
    (∀ u delta : Rat, u ≠ 0 → delta ≠ 0 →
      sq (sq (u * (1 + delta)) - sq u) / sq (sq u * delta) = sq (2 + delta)) ∧
    (∀ delta eps : Rat, eps < 2 → ratAbs delta ≤ eps →
      sq (2 - eps) ≤ sq (2 + delta) ∧ sq (2 + delta) ≤ sq (2 + eps)) ∧
    (∀ (n : Nat) (u delta : Fin n → Rat) (eps : Rat),
      eps < 2 → (∀ i, ratAbs (delta i) ≤ eps) →
      sq (2 - eps) * finSum (fun i => sq (sq (u i) * delta i)) ≤
        finSum (fun i => sq (sq (u i * (1 + delta i)) - sq (u i))) ∧
      finSum (fun i => sq (sq (u i * (1 + delta i)) - sq (u i))) ≤
        sq (2 + eps) * finSum (fun i => sq (sq (u i) * delta i))) ∧
    (sq (2 - (0 : Rat)) = 4 ∧ sq (2 + (0 : Rat)) = 4 ∧
     sq (2 - (1 / 16 : Rat)) = 961 / 256 ∧
     sq (2 + (1 / 16 : Rat)) = 1089 / 256 ∧
     (961 / 256 : Rat) < 391 / 100 ∧
     (391 / 100 : Rat) < 1089 / 256) :=
  Relu2TealDeadzone.relu2_quantization_order_fp_post_beats_pre_exact_4x

theorem teal_cats_shifted_deadzone_reclamation_uniform_exact :
    (∀ M tau N : Rat, (0 : Rat) < M → (0 : Rat) < tau → tau < M → (0 : Rat) < N →
      shiftedStep M tau N = (1 - tau / M) * uniformStep M N ∧
      shiftedHalfStep M tau N = (1 - tau / M) * stdHalfStep M N ∧
      shiftedStep M tau N < uniformStep M N ∧
      sq (shiftedHalfStep M tau N) < sq (stdHalfStep M N) ∧
      sq (stdHalfStep M N) / sq (shiftedHalfStep M tau N) = 1 / sq (1 - tau / M)) ∧
    (∀ tau x q : Rat,
      ratAbs (tealShiftedRecon tau x q - x) = ratAbs (q - (ratAbs x - tau))) ∧
    ((1 / sq (1 - (1 / 2 : Rat)) : Rat) = 4 ∧
     (1 / sq (1 - (3 / 4 : Rat)) : Rat) = 16 ∧
     (1 / sq (1 - (7 / 8 : Rat)) : Rat) = 64) :=
  Relu2TealDeadzone.teal_cats_shifted_deadzone_reclamation_uniform_exact

theorem teal_cats_fp_superquadratic_logarithmic_density_bonus :
    (∀ M tau x : Rat, (0 : Rat) < M → (0 : Rat) < x →
      (1 - tau / M) - (x - tau) / x = (tau * (M - x)) / (M * x)) ∧
    (∀ M tau x : Rat, (0 : Rat) < tau → tau < x → x < M →
      ((x - tau) / x) * (M / (M - tau)) < 1 ∧
      (x - tau) / x < 1 - tau / M) ∧
    (∀ u M tau x : Rat, (0 : Rat) < u → (0 : Rat) < tau → tau < x → x < M →
      1 / sq (1 - tau / M) < sq (fpLocalStep u x) / sq (fpLocalStep u (x - tau))) ∧
    (∀ u M tau : Rat, (0 : Rat) < u → (0 : Rat) < tau → tau < M →
      sq (fpLocalStep u M) / sq (fpLocalStep u (M - tau)) = 1 / sq (1 - tau / M)) ∧
    (∀ (n : Nat) (x : Fin n → Rat) (u M tau : Rat),
      (0 : Rat) < u → (0 : Rat) < tau →
      (∀ i, tau < x i ∧ x i ≤ M) →
      (∃ j, x j < M) →
      finSum (fun i => sq (fpLocalStep u (x i - tau))) <
        sq (1 - tau / M) * finSum (fun i => sq (fpLocalStep u (x i)))) :=
  Relu2TealDeadzone.teal_cats_fp_superquadratic_logarithmic_density_bonus

theorem prune_before_quantize_mask_flip_and_bitmask_crossover :
    (∀ delta g tau x : Rat, (0 : Rat) < delta → g < tau → tau < g + delta / 2 →
      tau ≤ x → x < g + delta / 2 →
      pruneMask tau x = true ∧
      pruneMask tau (uniformGridRound delta g x) = false ∧
      tau - delta / 2 ≤ x ∧ x < tau + delta / 2) ∧
    (∀ delta g tau x : Rat, (0 : Rat) < delta → tau ≤ g + delta → g + delta / 2 ≤ tau →
      g + delta / 2 ≤ x → x < tau →
      pruneMask tau x = false ∧
      pruneMask tau (uniformGridRound delta g x) = true ∧
      tau - delta / 2 ≤ x ∧ x < tau + delta / 2) ∧
    (∀ delta g x : Rat, (0 : Rat) < delta →
      (g + delta) - delta / 2 ≤ x → x < g + delta →
      pruneMask (g + delta) x = false ∧
      pruneMask (g + delta) (uniformGridRound delta g x) = true) ∧
    (∀ ov : Rat, (0 : Rat) < ov →
      sparsityCrossover ov = ov / (1 + ov) ∧
      (0 : Rat) < sparsityCrossover ov ∧ sparsityCrossover ov < 1 ∧
      sparseTrafficRatio (sparsityCrossover ov) ov = 1 ∧
      sparseSpeedup (sparsityCrossover ov) ov = 1) ∧
    (∀ s ov : Rat, s < 1 → (0 : Rat) < ov →
      (sparseTrafficRatio s ov < 1 ↔ sparsityCrossover ov < s) ∧
      ((1 : Rat) < sparseSpeedup s ov ↔ sparsityCrossover ov < s)) ∧
    (sparsityCrossover (1 / 64 : Rat) = 1 / 65 ∧
     (1 / 65 : Rat) < 1 / 5 ∧
     sparsityCrossover (3 / 16 : Rat) = 3 / 19 ∧
     (3 / 19 : Rat) < 1 / 5 ∧
     sparseSpeedup (3 / 4 : Rat) (3 / 16 : Rat) = 64 / 19 ∧
     (23 / 10 : Rat) < 64 / 19 ∧ (64 / 19 : Rat) < 34 / 10) :=
  Relu2TealDeadzone.prune_before_quantize_mask_flip_and_bitmask_crossover

end Relu2TealDeadzoneChallenge
