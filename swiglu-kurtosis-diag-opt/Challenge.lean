/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SwiGluKurtosis.Defs

/-!
# Trusted Challenge Statements (`swiglu-kurtosis-diag-opt`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Exact `2x` gating-sparsity kurtosis multiplication law `Kurt(ReLU(G) * U) = 2 * Kurt(G) * Kurt(U)`.
2. Exact correlated bilinear kurtosis amplification (`70/3` and `76/3` vs `18` for Gaussian moments).
3. Exact zero-FLOP SwiGLU diagonal channel-scaling invariance `W_down S^{-1} (φ(g) ⊙ (S u)) = W_down (φ(g) ⊙ u)`.
4. Exact AM-GM / SOS optimal diagonal scaling MSE law with `W4A4`, `W8A4`, `W16A4` rational certificates.
5. Exact asymmetric gate-up-down bit-allocation dominance (`(4,5,3)` and `(5,4,3)` vs `(4,4,4)`).
6. Exact `MXFP4` (`B=32, E8M0`, `< M/24` flush) vs `NVFP4` (`B=16`, `100%` clean sub-block) underflow gap.
-/

namespace SwiGluKurtosisChallenge

open SwiGluKurtosis

/-- Theorem 1 (`reglu_exact_two_x_kurtosis_multiplication_law`):
    For any two independent symmetric finite rational distributions `G` and `U`
    (`P(G > 0) = P(G < 0) = 1/2, P(G = 0) = 0`), proves exact zero mean,
    `Kurt(G * U) = Kurt(G) * Kurt(U)`, and the exact `2x` gating-sparsity law
    `Kurt(ReLU(G) * U) = 2 * Kurt(G) * Kurt(U) = 2 * Kurt(G * U)`, plus exact rational
    witnesses achieving `2 * 3 * 3 = 18` (Gaussian moments) and `2 * 6 * 6 = 72` (Laplace moments). -/
theorem reglu_exact_two_x_kurtosis_multiplication_law :
    (∀ (n m : Nat) (G : SymHalfDist n) (U : SymHalfDist m),
      prodSymExpect G U (fun g u => relu g * u) = 0 ∧
      bilinearRawKurt G U = symKurtosis G * symKurtosis U ∧
      regluIndepRawKurt G U = 2 * symKurtosis G * symKurtosis U ∧
      regluIndepRawKurt G U = 2 * bilinearRawKurt G U) ∧
    (symKurtosis gaussMoment3Dist = 3 ∧
     regluIndepRawKurt gaussMoment3Dist gaussMoment3Dist = 18) ∧
    (symKurtosis laplaceMoment3Dist = 6 ∧
     regluIndepRawKurt laplaceMoment3Dist laplaceMoment3Dist = 72) := by
  sorry

/-- Theorem 2 (`correlated_bilinear_kurtosis_amplification_exact`):
    Proves that identical gate-up correlation (`G = U`) satisfies the exact identity
    `RawKurt(ReLU(G) * G) = 2 * E[G^8] / (E[G^4])^2`, strictly exceeding the independent `2x` law
    whenever `E[G^4]^4 < E[G^8] * E[G^2]^4`, proves the exact linear-mixture 2nd and 4th moments
    for `ReLU(G) * (a G + b Z)`, and proves the exact Gaussian-moment law
    `gaussCorrReGLUKurt(t) = 18 + 24 t (3 - t) / (2 t + 1)^2 > 18` for all `0 < t ≤ 1`
    (reaching exact `70/3` at `ρ = 1` and `76/3` at `ρ = 1/2` vs `18` independent),
    plus a concrete finite symmetric rational witness `heavyTail3Dist`. -/
theorem correlated_bilinear_kurtosis_amplification_exact :
    (∀ (n : Nat) (G : SymHalfDist n),
      regluSelfRawKurt G = 2 * symMoment8 G / sq (symMoment4 G)) ∧
    (∀ (n : Nat) (G : SymHalfDist n),
      pow4 (symMoment4 G) < symMoment8 G * pow4 (symMoment2 G) →
      regluIndepRawKurt G G < regluSelfRawKurt G) ∧
    (∀ (n : Nat) (D : SymHalfDist n) (a b : Rat),
      prodSymExpect D D (fun g z => sq (relu g * (a * g + b * z))) =
        (1 / 2) * (sq a * symMoment4 D + sq b * sq (symMoment2 D)) ∧
      prodSymExpect D D (fun g z => pow4 (relu g * (a * g + b * z))) =
        (1 / 2) * (pow4 a * symMoment8 D + 6 * sq a * sq b * symMoment6 D * symMoment2 D +
          pow4 b * sq (symMoment4 D))) ∧
    (∀ t : Rat, (0 : Rat) < t → t ≤ 1 →
      gaussCorrReGLUKurt t = 18 + (24 * t * (3 - t)) / sq (2 * t + 1) ∧
      (18 : Rat) < gaussCorrReGLUKurt t) ∧
    (gaussCorrReGLUKurt 0 = 18 ∧
     gaussCorrReGLUKurt (1 / 4) = 76 / 3 ∧
     gaussCorrReGLUKurt 1 = 70 / 3 ∧
     (18 : Rat) < 70 / 3 ∧
     (70 / 3 : Rat) < 76 / 3) ∧
    (regluIndepRawKurt heavyTail3Dist heavyTail3Dist < regluSelfRawKurt heavyTail3Dist) := by
  sorry

/-- Theorem 3 (`swiglu_zero_flop_diagonal_equivalence_identity`):
    Proves exact algebraic invariance of any gated FFN `W_down (φ(g) ⊙ u)` (for arbitrary
    gate nonlinearity `φ`, including `SiLU`, `GELU`, `ReLU`) under any invertible diagonal
    channel scaling `S = diag(s_1, ..., s_m)` absorbed into `W_up' = S W_up` and
    `W_down' = W_down S^{-1}`, leaving `W_gate` completely untouched at ZERO extra inference FLOPs. -/
theorem swiglu_zero_flop_diagonal_equivalence_identity :
    (∀ (d_out m : Nat) (φ : Rat → Rat) (W_down : Fin d_out → Fin m → Rat)
       (g u s : Fin m → Rat),
      (∀ j : Fin m, s j ≠ 0) →
      gatedFFN φ (invScaleCols s W_down) g (fun j => s j * u j) =
        gatedFFN φ W_down g u) ∧
    (∀ (d_out m d_in : Nat) (φ : Rat → Rat)
       (W_down : Fin d_out → Fin m → Rat)
       (W_gate W_up : Fin m → Fin d_in → Rat)
       (x : Fin d_in → Rat) (s : Fin m → Rat),
      (∀ j : Fin m, s j ≠ 0) →
      gatedFFN φ (invScaleCols s W_down) (matVec W_gate x) (matVec (scaleRows s W_up) x) =
        gatedFFN φ W_down (matVec W_gate x) (matVec W_up x)) ∧
    (∀ (φ : Rat → Rat) (w g u lam : Rat),
      lam ≠ 0 → (w * lam) * (φ g * (u / lam)) = w * (φ g * u)) := by
  sorry

/-- Theorem 4 (`swiglu_optimal_diagonal_scale_amgm_law`):
    Proves via exact SOS / AM-GM over `Rat` that `E(λ) = εa (K / λ)^2 + εw λ^2` satisfies
    `E(λ)^2 ≥ 4 K^2 εa εw`, is uniquely minimized at `λ^{*2} = K r` (where `r^2 = εa / εw`)
    with exact minimum `2 K εw r` strictly beating unscaled `λ = 1` whenever `K r ≠ 1`,
    is uniquely minimized on `(0, K]` at the clamp `λ = K` whenever `K^2 εw ≤ εa`,
    and provides exact rational certificates for `W4A4`, `W8A4`, and `W16A4`. -/
theorem swiglu_optimal_diagonal_scale_amgm_law :
    (∀ (εa εw K lam : Rat), lam ≠ 0 →
      sq (diagQuantMSE εa εw K lam) - 4 * sq K * εa * εw =
        sq (εa * sq (K / lam) - εw * sq lam) ∧
      4 * sq K * εa * εw ≤ sq (diagQuantMSE εa εw K lam)) ∧
    (∀ (εa εw K r lam : Rat), (0 : Rat) < εw → lam ≠ 0 → εa = εw * sq r →
      diagQuantMSE εa εw K lam - 2 * K * εw * r =
        εw * sq (sq lam - K * r) / sq lam ∧
      2 * K * εw * r ≤ diagQuantMSE εa εw K lam ∧
      (diagQuantMSE εa εw K lam = 2 * K * εw * r ↔ sq lam = K * r)) ∧
    (∀ (εa εw K r lamStar : Rat), (0 : Rat) < εw → lamStar ≠ 0 →
      εa = εw * sq r → sq lamStar = K * r → K * r ≠ 1 →
      diagQuantMSE εa εw K 1 - diagQuantMSE εa εw K lamStar = εw * sq (K * r - 1) ∧
      diagQuantMSE εa εw K lamStar < diagQuantMSE εa εw K 1) ∧
    (∀ (εa εw K lam : Rat), (0 : Rat) < εw → (0 : Rat) < lam → lam < K →
      sq K * εw ≤ εa →
      diagQuantMSE εa εw K K < diagQuantMSE εa εw K lam) ∧
    (diagQuantMSE (1 / 16) (1 / 16) 4 2 = 1 / 2 ∧
     diagQuantMSE (1 / 16) (1 / 16) 4 1 = 17 / 16 ∧
     diagQuantMSE (1 / 16) (1 / 16) 4 2 < diagQuantMSE (1 / 16) (1 / 16) 4 1 ∧
     diagQuantMSE (1 / 16) (1 / 4096) 16 16 = 1 / 8 ∧
     diagQuantMSE (1 / 16) (1 / 4096) 16 1 = 65537 / 4096 ∧
     diagQuantMSE (1 / 16) (1 / 4096) 16 16 < diagQuantMSE (1 / 16) (1 / 4096) 16 1 ∧
     diagQuantMSE (1 / 16) (1 / 16777216) 16 16 = 4097 / 65536 ∧
     diagQuantMSE (1 / 16) (1 / 16777216) 16 16 < diagQuantMSE (1 / 16) (1 / 16777216) 16 1) := by
  sorry

/-- Theorem 5 (`gated_ffn_asymmetric_bit_allocation_dominance`):
    Proves the universal 3-term AM-GM lower bound `27 Sg Su Sd * 4^{-B} ≤ MSE^3` and
    exact integer-bit dominance iff laws for any `b ≥ 1` (including `b = 4`, `B_tot = 12`):
    `(4, 5, 3)` beats `(4, 4, 4)` iff `Su > 4 * Sd`, `(5, 4, 3)` beats `(4, 4, 4)` iff
    `Sg > 4 * Sd`, and `(5, 3, 4)` beats `(3, 5, 4)` iff `Sg > Su` (capturing the
    negative-biased Llama-3/Qwen-3 regime where `S_gate ≈ 3 * S_up`). -/
theorem gated_ffn_asymmetric_bit_allocation_dominance :
    (∀ (Sg Su Sd : Rat) (bg bu bd : Nat), (0 : Rat) ≤ Sg → (0 : Rat) ≤ Su → (0 : Rat) ≤ Sd →
      27 * Sg * Su * Sd * invPow2Rat (2 * (bg + bu + bd)) ≤
        bitAllocMSE Sg Su Sd bg bu bd * bitAllocMSE Sg Su Sd bg bu bd * bitAllocMSE Sg Su Sd bg bu bd) ∧
    (∀ (Sg Su Sd : Rat) (b : Nat), 1 ≤ b →
      (bitAllocMSE Sg Su Sd b (b + 1) (b - 1) < bitAllocMSE Sg Su Sd b b b ↔ 4 * Sd < Su) ∧
      (bitAllocMSE Sg Su Sd (b + 1) b (b - 1) < bitAllocMSE Sg Su Sd b b b ↔ 4 * Sd < Sg) ∧
      (bitAllocMSE Sg Su Sd (b + 1) (b - 1) b < bitAllocMSE Sg Su Sd (b - 1) (b + 1) b ↔ Su < Sg)) ∧
    (∀ (Sg Su Sd : Rat),
      (bitAllocMSE Sg Su Sd 4 5 3 < bitAllocMSE Sg Su Sd 4 4 4 ↔ 4 * Sd < Su) ∧
      (bitAllocMSE Sg Su Sd 5 4 3 < bitAllocMSE Sg Su Sd 4 4 4 ↔ 4 * Sd < Sg) ∧
      (bitAllocMSE Sg Su Sd 5 3 4 < bitAllocMSE Sg Su Sd 3 5 4 ↔ Su < Sg)) ∧
    (bitAllocMSE 3 1 1 5 3 4 < bitAllocMSE 3 1 1 3 5 4 ∧
     bitAllocMSE 1 5 1 4 5 3 < bitAllocMSE 1 5 1 4 4 4 ∧
     bitAllocMSE 5 1 1 5 4 3 < bitAllocMSE 5 1 1 4 4 4) := by
  sorry

/-- Theorem 6 (`mxfp4_block32_vs_nvfp4_block16_kurtosis_underflow_gap`):
    Proves that for any 32-element block with a single extreme SwiGLU outlier `M` at any
    index `idx : Fin 32` and 31 background entries in `[m/12, m]` with `m < M/24`,
    `MXFP4` (`B=32`, any valid `E2M1` scale `s32 ≥ M/6`) flushes ALL 31 background entries
    to exact zero, whereas `NVFP4` (`B=16`) isolates the outlier to one half and preserves
    100% (all 16 entries) of the clean 16-element sub-block strictly nonzero. -/
theorem mxfp4_block32_vs_nvfp4_block16_kurtosis_underflow_gap :
    (maxE2M1 = 6 ∧ minSubE2M1 = 1 / 2 ∧ underflowMidE2M1 = 1 / 4 ∧
     maxE2M1 / underflowMidE2M1 = 24) ∧
    (∀ (v : Fin 32 → Rat) (idx : Fin 32) (M m s32 : Rat),
      (0 : Rat) < M → (0 : Rat) < m → m < M / 24 →
      ratAbs (v idx) = M →
      (∀ j : Fin 32, j ≠ idx → m / 12 ≤ ratAbs (v j) ∧ ratAbs (v j) ≤ m) →
      validE2M1Scale s32 M →
      (∀ j : Fin 32, j ≠ idx → fp4Underflows s32 (v j)) ∧
      (let sClean := m / 6
       validE2M1Scale sClean m ∧
       (∀ k : Fin 16, ratAbs (cleanHalf16 v idx k) ≤ m) ∧
       (∀ k : Fin 16, fp4PreservedNonzero sClean (cleanHalf16 v idx k)) ∧
       (∀ k : Fin 16, ¬ fp4Underflows sClean (cleanHalf16 v idx k)))) ∧
    (∀ (M : Rat), (0 : Rat) < M →
      (31 : Nat) + 1 = 32 ∧ (16 : Nat) + 16 = 32 ∧ (15 : Nat) + 16 = 31 ∧
      (16 : Rat) / 32 = 1 / 2) := by
  sorry

end SwiGluKurtosisChallenge
