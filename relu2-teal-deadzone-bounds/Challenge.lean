/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relu2TealDeadzone.Defs

/-!
# Trusted Challenge Statements (`relu2-teal-deadzone-bounds`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Exact `ReLU` (`6`) and `ReLU^2` (`70/3`) kurtosis under Gaussian moments and `p * c^8`
   outlier-mixture amplification.
2. Exact uniform quantization-order law (`PRE` beats `POST` on `INT4`, with `2N` squared
   zero-underflow deadzone ratio and lower-dynamic-range / outlier-mixture MSE win).
3. Exact floating-point quantization-order dichotomy (`POST` beats `PRE` by exact asymptotic
   `4×` / `+6.02 dB`, with finite-dataset two-sided bounds `(2 - ε)^2` to `(2 + ε)^2`).
4. Exact `TEAL` / `CATS` shifted deadzone reclamation law `(1 - τ/M)^(-2)` at zero extra
   bits for uniform quantizers (`4×` at `τ = M/2`, `16×` at `τ = 3M/4`, `64×` at `τ = 7M/8`).
5. Exact floating-point super-quadratic logarithmic density bonus under shifted deadzone
   reclamation across the entire active interior `(τ, M)`.
6. Exact quantize-before-prune mask-flip zone `[τ - Δ/2, τ + Δ/2)` vs zero-flip
   prune-before-quantize, and exact `uint64_t` bitmask sparsity crossover `s* = 1 - 1/(1 + ov)`.
-/

namespace Relu2TealDeadzoneChallenge

open Relu2TealDeadzone

/-- Theorem 1 (`relu2_exact_kurtosis_seventy_thirds_and_outlier_amplification`):
    For any symmetric finite rational distribution matching standard normal moments
    `m2 = 1, m4 = 3, m8 = 105`, `ReLU` doubles kurtosis to `6` while `ReLU^2` jumps kurtosis
    to exact `70/3`, and for any `(1 - p)` bulk + `p` `c`-scaled outlier mixture, squaring
    elevates the outlier weight from `p * c^4` to `p * c^8` (ratio `c^4`, exploding 1% `4×`
    OutlierMix kurtosis past `1215`). -/
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
     (75 : Rat) * (8520 / 529) < 18377800 / 15123) := by
  sorry

/-- Theorem 2 (`relu2_quantization_order_uniform_pre_beats_post`):
    For uniform integer quantization on `[0, M]` with `N > 0` levels, `POST`-square widens
    the squared zero-underflow deadzone by exact `2N` (`30 > 5^2` for `INT4-u4`, `14 > 3^2`
    for `INT4-s4`), and `PRE`-square strictly beats `POST`-square on worst-case error iff
    `x < M * (1/2 - 1/(4N))` (`29/60 * M` for `INT4-u4`), achieving worst-case ratio `8/15`
    (squared ratio `64/225 < 1/3`) at `x = M / 4`. -/
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
     (64 / 225 : Rat) < 1 / 3) := by
  sorry

/-- Theorem 3 (`relu2_quantization_order_fp_post_beats_pre_exact_4x`):
    For floating-point formats (`FP8-E4M3`, `MXFP4`, `NVFP4`) with relative error
    `û = u (1 + δ)`, `|δ| ≤ ε < 2`, squaring doubles first-order relative error
    `û^2 - u^2 = u^2 (2δ + δ^2)`, proving exact two-sided MSE inflation bounds
    `(2 - ε)^2` to `(2 + ε)^2` pointwise and across arbitrary finite datasets `Fin n`
    (exact `4×` asymptote as `ε → 0`; `961/256 < 3.91 < 1089/256` at `FP8-E4M3` `ε = 1/16`). -/
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
     (391 / 100 : Rat) < 1089 / 256) := by
  sorry

/-- Theorem 4 (`teal_cats_shifted_deadzone_reclamation_uniform_exact`):
    For `TEAL` / `CATS` activation sparsity with pruning threshold `τ ∈ (0, M)`, reclaiming
    the deadzone `[0, τ)` via shifted uniform quantization shrinks the step size by exact
    `(1 - τ/M)` and cuts worst-case squared quantization error by exact `(1 - τ/M)^(-2)` at
    zero extra bits (`4×` at `τ = M/2`, `16×` at `τ = 3M/4`, `64×` at `τ = 7M/8`). -/
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
     (1 / sq (1 - (7 / 8 : Rat)) : Rat) = 64) := by
  sorry

/-- Theorem 5 (`teal_cats_fp_superquadratic_logarithmic_density_bonus`):
    For floating-point formats (`MXFP4`, `NVFP4`, `FP8-E4M3`) with local step `u * y`,
    shifting `x ∈ (τ, M]` to `y = x - τ` beats the uniform `(1 - τ/M)` factor by exact
    `τ * (M - x) / (M * x) > 0` for every `x ∈ (τ, M)`, proving strictly super-quadratic
    MSE reduction `> (1 - τ/M)^(-2)` pointwise and across any finite active dataset with
    an interior sample. -/
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
        sq (1 - tau / M) * finSum (fun i => sq (fpLocalStep u (x i)))) := by
  sorry

/-- Theorem 6 (`prune_before_quantize_mask_flip_and_bitmask_crossover`):
    (a) Quantizing before `TEAL` / `CATS` pruning creates an exact boundary flip zone inside
    `[τ - Δ/2, τ + Δ/2)` where mask bits invert (`0` flips when pruning precedes quantization);
    (b) Exact `uint64_t` bitmask sparse `W4` `down_proj` crossover `s* = 1 - 1 / (1 + ov)`
    (`1/65 < 20%` for `1/64` metadata, `3/19 < 20%` for `3/16` overhead with `64/19 ≈ 3.37×`
    at `75%` sparsity). -/
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
     (23 / 10 : Rat) < 64 / 19 ∧ (64 / 19 : Rat) < 34 / 10) := by
  sorry

end Relu2TealDeadzoneChallenge
