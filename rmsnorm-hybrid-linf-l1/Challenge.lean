/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RmsnormHybridLinfL1.Defs

/-!
# Trusted Challenge Statements (`rmsnorm-hybrid-linf-l1`)

Universal and exact pure-`Init` (zero Mathlib, zero `native_decide`) Lean 4 statements for:
1. Universal sharp upper and lower rational envelopes (and exact attainment) for the `L∞ + L1`
   hybrid norm `H_{α,β}(x) = α ‖x‖_∞ + (β / d) ‖x‖_1` relative to `RMS(x)`.
2. Universal minimax optimality theorem (`κ^*(d) = √((√d + 1) / 2) = Θ(d^(1/4))`), exact
   square-dimension unique optimum (`β = s α` for `d = s^2`), and no-`O(1)`-distortion lower bound.
3. Exact pure-bitshift dyadic instantiations for Llama-3 8B (`d = 4096`, `κ^2 = 65/2`),
   Llama-3 70B (`d = 8192`, `κ^2 = 97/2`), and the power-of-4 dyadic scaling table.
4. Universal IEEE-754 RNE `sum(x_i^2)` swamping horizon `S_swamp(p) = 2^p` and bit-exact minimal
   outlier thresholds across BF16 (`16`), FP16 (`181/4`), FP8-E4M3 (`4`), FP8-E5M2 (`3`), and
   MXFP4-E2M1 (`2`).
5. Bit-exact 1-pass LayerNorm negative-variance (`NaN`) and zero-collapse witnesses across BF16
   (`243/16 → Var = -1`), FP16 (`1047/16 → Var = -4`), FP8-E4M3 (`13 → Var = -16`), and
   FP8-E5M2 (`8 → Var = -8`).
6. Universal unconditional non-negativity of 2-pass shifted-mean variance in exact rational
   arithmetic and every monotonic non-negative rounding arithmetic.
-/

namespace RmsnormHybridLinfL1Challenge

open RmsnormHybridLinfL1

/-- Theorem 1 (Exact `L∞ + L1` Hybrid Norm Upper and Lower Envelopes & Attainment):
    For all `d ≥ 1`, `α > 0`, `β > 0`, and `x : Fin d → Rat`, proves both sharp squared bounds
    `4 α β * MS(x) ≤ H_{α,β}(x)^2 ≤ (α^2 d + 2 α β + β^2) * MS(x)`, together with exact
    attainment of the upper bound by the spike-plus-uniform vector `upperExtremalVec d α β` and
    exact attainment of the lower bound by the `s`-sparse binary vector `kSparseVec (s * s) s`
    at `β = s α`. -/
theorem hybrid_linf_l1_exact_upper_and_lower_envelopes :
    (∀ (d : Nat) (α β : Rat) (x : Fin d → Rat), 1 ≤ d → 0 < α → 0 < β →
      hybridNorm α β x * hybridNorm α β x ≤ hybridUpperConstSq d α β * meanSq x) ∧
    (∀ (d : Nat) (α β : Rat), 1 ≤ d → 0 < α → 0 < β →
      0 < meanSq (upperExtremalVec d α β) ∧
      hybridNorm α β (upperExtremalVec d α β) * hybridNorm α β (upperExtremalVec d α β) =
        hybridUpperConstSq d α β * meanSq (upperExtremalVec d α β)) ∧
    (∀ (d : Nat) (α β : Rat) (x : Fin d → Rat), 1 ≤ d → 0 < α → 0 < β →
      hybridLowerConstSq α β * meanSq x ≤ hybridNorm α β x * hybridNorm α β x) ∧
    (∀ (s : Nat) (α : Rat), 1 ≤ s → 0 < α →
      0 < meanSq (kSparseVec (s * s) s) ∧
      hybridNorm α ((s : Rat) * α) (kSparseVec (s * s) s) *
        hybridNorm α ((s : Rat) * α) (kSparseVec (s * s) s) =
        hybridLowerConstSq α ((s : Rat) * α) * meanSq (kSparseVec (s * s) s)) := by
  sorry

/-- Theorem 2 (Universal Minimax `Θ(d^(1/4))` Law & Impossibility of `O(1)` Distortion):
    Proves the universal rational sum-of-squares identity `(2 κ^2 - 1)^2 - d = (α^2 d - β^2)^2 / (4 α^2 β^2)`
    implying `4 κ^4 - 4 κ^2 + 1 ≥ d` for all `d ≥ 1`, `α > 0`, `β > 0`; proves for every square
    dimension `d = s^2` that `κ(s^2, α, β)^2 ≥ (s + 1) / 2` with unique equality iff `β = s α`;
    and proves that no `d`-independent constant `C ≥ 1` can bound `κ(d, α, β)^2`. -/
theorem hybrid_linf_l1_minimax_d_quarter_law :
    (∀ (d : Nat) (α β : Rat), 1 ≤ d → 0 < α → 0 < β →
      (2 * hybridKappaSq d α β - 1) * (2 * hybridKappaSq d α β - 1) - (d : Rat) =
        ((α * α * (d : Rat) - β * β) * (α * α * (d : Rat) - β * β)) / (4 * α * α * β * β) ∧
      (d : Rat) ≤ 4 * hybridKappaSq d α β * hybridKappaSq d α β - 4 * hybridKappaSq d α β + 1) ∧
    (∀ (s : Nat) (α β : Rat), 1 ≤ s → 0 < α → 0 < β →
      hybridKappaSq (s * s) α β - ((s : Rat) + 1) / 2 =
        ((α * (s : Rat) - β) * (α * (s : Rat) - β)) / (4 * α * β) ∧
      ((s : Rat) + 1) / 2 ≤ hybridKappaSq (s * s) α β ∧
      (hybridKappaSq (s * s) α β = ((s : Rat) + 1) / 2 ↔ β = (s : Rat) * α)) ∧
    (∀ C : Rat, 1 ≤ C → ∃ d : Nat, 1 ≤ d ∧ ∀ α β : Rat, 0 < α → 0 < β → C < hybridKappaSq d α β) := by
  sorry

/-- Theorem 3 (Exact Pure-Bitshift Dyadic Hybrid Norm for Llama-3 8B `d = 4096` and 70B `d = 8192`):
    Proves that `2^(-6) ‖x‖_∞ + 2^(-12) ‖x‖_1` attains exact `κ^2 = 65/2` (`> 126x` tighter than
    pure `L1`'s `4096`) with universal envelopes `1/16 * MS(x) ≤ H(x)^2 ≤ 65/32 * MS(x)` at `d = 4096`,
    proves the `d = 8192` dyadic witness (`κ^2 = 97/2`, `> 168x` tighter than `8192`), and certifies
    the power-of-4 dyadic scaling table `d ∈ {64, 256, 1024, 4096, 16384}`. -/
theorem dyadic_llama3_d4096_hybrid_norm_exact :
    (hybridLowerConstSq (invPow2Rat 6) 1 = 1 / 16 ∧
     hybridUpperConstSq 4096 (invPow2Rat 6) 1 = 65 / 32 ∧
     hybridKappaSq 4096 (invPow2Rat 6) 1 = 65 / 2 ∧
     (4096 : Rat) / hybridKappaSq 4096 (invPow2Rat 6) 1 = 8192 / 65 ∧
     (126 : Rat) < 8192 / 65 ∧
     (∀ x : Fin 4096 → Rat,
       hybridNorm (invPow2Rat 6) 1 x = invPow2Rat 6 * linfNorm x + invPow2Rat 12 * l1Norm x ∧
       (1 / 16 : Rat) * meanSq x ≤ hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ∧
       hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ≤ (65 / 32 : Rat) * meanSq x)) ∧
    (hybridLowerConstSq (invPow2Rat 6) 1 = 1 / 16 ∧
     hybridUpperConstSq 8192 (invPow2Rat 6) 1 = 97 / 32 ∧
     hybridKappaSq 8192 (invPow2Rat 6) 1 = 97 / 2 ∧
     (8192 : Rat) / hybridKappaSq 8192 (invPow2Rat 6) 1 = 16384 / 97 ∧
     (168 : Rat) < 16384 / 97 ∧
     (∀ x : Fin 8192 → Rat,
       hybridNorm (invPow2Rat 6) 1 x = invPow2Rat 6 * linfNorm x + invPow2Rat 13 * l1Norm x ∧
       (1 / 16 : Rat) * meanSq x ≤ hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ∧
       hybridNorm (invPow2Rat 6) 1 x * hybridNorm (invPow2Rat 6) 1 x ≤ (97 / 32 : Rat) * meanSq x)) ∧
    (hybridKappaSq 64 (invPow2Rat 3) 1 = 9 / 2 ∧
     hybridKappaSq 256 (invPow2Rat 4) 1 = 17 / 2 ∧
     hybridKappaSq 1024 (invPow2Rat 5) 1 = 33 / 2 ∧
     hybridKappaSq 4096 (invPow2Rat 6) 1 = 65 / 2 ∧
     hybridKappaSq 16384 (invPow2Rat 7) 1 = 129 / 2) := by
  sorry

/-- Theorem 4 (Exact IEEE-754 RNE `sum(x_i^2)` Swamping Horizon `S_swamp(p) = 2^p`):
    Proves universal tie-to-even swamping `fl_p(2^p + 1) = 2^p` for all precisions `p ≥ 2`, and
    certifies the exact minimal outlier thresholds `M_swamp` (dropping ALL `n` unit bulk squares,
    while `M_swamp - 1 ulp` does not swamp) across BF16 (`0x4180` = `16`), FP16 (`0x51a8` = `181/4`),
    FP8-E4M3 (`0x48` = `4`), FP8-E5M2 (`0x42` = `3`), and MXFP4-E2M1 (`0x4` = `2`). -/
theorem bf16_fp16_fp8_sumsq_swamping_horizon_exact :
    (∀ p : Nat, 2 ≤ p → rneDivNat (2 ^ p + 1) 2 * 2 = 2 ^ p) ∧
    (fmtBF16.precision = 8 ∧
     fmtBF16.decode 0x4180 = FloatVal.finite 16 ∧
     fmtBF16.decode (fmtBF16.flMul 0x4180 0x4180) = FloatVal.finite 256 ∧
     (∀ n : Nat, fmtBF16.seqAddOnes (fmtBF16.flMul 0x4180 0x4180) n = fmtBF16.flMul 0x4180 0x4180) ∧
     fmtBF16.flAdd (fmtBF16.flMul 0x417f 0x417f) (fmtBF16.encodeDyadic 1 0) ≠
       fmtBF16.flMul 0x417f 0x417f) ∧
    (fmtFP16.precision = 11 ∧
     fmtFP16.decode 0x51a8 = FloatVal.finite (181 / 4) ∧
     fmtFP16.decode (fmtFP16.flMul 0x51a8 0x51a8) = FloatVal.finite 2048 ∧
     (∀ n : Nat, fmtFP16.seqAddOnes (fmtFP16.flMul 0x51a8 0x51a8) n = fmtFP16.flMul 0x51a8 0x51a8) ∧
     fmtFP16.flAdd (fmtFP16.flMul 0x51a7 0x51a7) (fmtFP16.encodeDyadic 1 0) ≠
       fmtFP16.flMul 0x51a7 0x51a7) ∧
    (fmtFP8E4M3.precision = 4 ∧
     fmtFP8E4M3.decode 0x48 = FloatVal.finite 4 ∧
     fmtFP8E4M3.decode (fmtFP8E4M3.flMul 0x48 0x48) = FloatVal.finite 16 ∧
     (∀ n : Nat, fmtFP8E4M3.seqAddOnes (fmtFP8E4M3.flMul 0x48 0x48) n = fmtFP8E4M3.flMul 0x48 0x48) ∧
     fmtFP8E4M3.flAdd (fmtFP8E4M3.flMul 0x47 0x47) (fmtFP8E4M3.encodeDyadic 1 0) ≠
       fmtFP8E4M3.flMul 0x47 0x47) ∧
    (fmtFP8E5M2.precision = 3 ∧
     fmtFP8E5M2.decode 0x42 = FloatVal.finite 3 ∧
     fmtFP8E5M2.decode (fmtFP8E5M2.flMul 0x42 0x42) = FloatVal.finite 8 ∧
     (∀ n : Nat, fmtFP8E5M2.seqAddOnes (fmtFP8E5M2.flMul 0x42 0x42) n = fmtFP8E5M2.flMul 0x42 0x42) ∧
     fmtFP8E5M2.flAdd (fmtFP8E5M2.flMul 0x41 0x41) (fmtFP8E5M2.encodeDyadic 1 0) ≠
       fmtFP8E5M2.flMul 0x41 0x41) ∧
    (fmtMXFP4.precision = 2 ∧
     fmtMXFP4.decode 0x4 = FloatVal.finite 2 ∧
     fmtMXFP4.decode (fmtMXFP4.flMul 0x4 0x4) = FloatVal.finite 4 ∧
     (∀ n : Nat, fmtMXFP4.seqAddOnes (fmtMXFP4.flMul 0x4 0x4) n = fmtMXFP4.flMul 0x4 0x4) ∧
     fmtMXFP4.flAdd (fmtMXFP4.flMul 0x3 0x3) (fmtMXFP4.encodeDyadic 1 0) ≠
       fmtMXFP4.flMul 0x3 0x3) := by
  sorry

/-- Theorem 5 (Bit-Exact 1-Pass LayerNorm Negative-Variance Witnesses):
    Verifies bit-exact IEEE-754 RNE 1-pass variance collapse and strictly negative variance
    (`Var < 0 => NaN`) on symmetric unit-std pairs in BF16 (`0x4173` = `243/16`, `m2 = 232`,
    `mu2 = 233`, `Var = -1`), FP16 (`0x5417` = `1047/16`, `m2 = 4280`, `mu2 = 4284`, `Var = -4`),
    FP8-E4M3 (`0x55` = `13`, `Var = -16`), and FP8-E5M2 (`0x48` = `8`, `Var = -8`). -/
theorem bf16_fp16_onepass_layernorm_negative_variance_exact :
    (fmtBF16.decode 0x4173 = FloatVal.finite (243 / 16) ∧
     (let r := fmtBF16.onePassVarPairBits 0x4173
      fmtBF16.decode r.1 = FloatVal.finite 232 ∧
      fmtBF16.decode r.2.1 = FloatVal.finite 233 ∧
      fmtBF16.decode r.2.2 = FloatVal.finite (-1)) ∧
     fmtBF16.decode 0x413d = FloatVal.finite (189 / 16) ∧
     (let r := fmtBF16.onePassVarPairBits 0x413d
      fmtBF16.decode r.1 = FloatVal.finite 140 ∧
      fmtBF16.decode r.2.1 = FloatVal.finite 140 ∧
      fmtBF16.decode r.2.2 = FloatVal.finite 0)) ∧
    (fmtFP16.decode 0x5417 = FloatVal.finite (1047 / 16) ∧
     (let r := fmtFP16.onePassVarPairBits 0x5417
      fmtFP16.decode r.1 = FloatVal.finite 4280 ∧
      fmtFP16.decode r.2.1 = FloatVal.finite 4284 ∧
      fmtFP16.decode r.2.2 = FloatVal.finite (-4)) ∧
     fmtFP16.decode 0x4fc7 = FloatVal.finite (1991 / 64) ∧
     (let r := fmtFP16.onePassVarPairBits 0x4fc7
      fmtFP16.decode r.1 = FloatVal.finite 969 ∧
      fmtFP16.decode r.2.1 = FloatVal.finite 969 ∧
      fmtFP16.decode r.2.2 = FloatVal.finite 0)) ∧
    (fmtFP8E4M3.decode 0x55 = FloatVal.finite 13 ∧
     (let r := fmtFP8E4M3.onePassVarPairBits 0x55
      fmtFP8E4M3.decode r.1 = FloatVal.finite 160 ∧
      fmtFP8E4M3.decode r.2.1 = FloatVal.finite 176 ∧
      fmtFP8E4M3.decode r.2.2 = FloatVal.finite (-16))) ∧
    (fmtFP8E5M2.decode 0x48 = FloatVal.finite 8 ∧
     (let r := fmtFP8E5M2.onePassVarPairBits 0x48
      fmtFP8E5M2.decode r.1 = FloatVal.finite 56 ∧
      fmtFP8E5M2.decode r.2.1 = FloatVal.finite 64 ∧
      fmtFP8E5M2.decode r.2.2 = FloatVal.finite (-8))) := by
  sorry

/-- Theorem 6 (Universal 2-Pass Shifted-Mean Variance Non-Negativity):
    Proves that 2-pass shifted-mean variance `(1/d) ∑ (x_i - μ)^2` is unconditionally `≥ 0`
    in exact rational arithmetic (together with the exact parallel-axis and 1-pass/2-pass
    identities) AND in every monotonic or non-negativity-preserving rounding arithmetic,
    eliminating negative-variance `NaN` identically. -/
theorem twopass_shifted_mean_variance_nonneg_universal :
    (∀ (d : Nat) (x : Fin d → Rat) (μ : Rat), 1 ≤ d →
      (0 : Rat) ≤ twoPassVar x μ ∧
      twoPassVar x μ = twoPassVar x (vecMean x) + (vecMean x - μ) * (vecMean x - μ) ∧
      twoPassVar x (vecMean x) ≤ twoPassVar x μ) ∧
    (∀ (d : Nat) (x : Fin d → Rat), 1 ≤ d →
      twoPassVar x (vecMean x) = meanSq x - vecMean x * vecMean x) ∧
    (∀ (fl : Rat → Rat), fl 0 = 0 → (∀ a b : Rat, a ≤ b → fl a ≤ fl b) →
      ∀ (d : Nat) (x : Fin d → Rat) (μHat : Rat), 1 ≤ d →
        (0 : Rat) ≤ twoPassVarRounded fl x μHat) ∧
    (∀ (fl : Rat → Rat), (∀ q : Rat, (0 : Rat) ≤ q → (0 : Rat) ≤ fl q) →
      ∀ (d : Nat) (x : Fin d → Rat) (μHat : Rat), 1 ≤ d →
        (0 : Rat) ≤ twoPassVarRounded fl x μHat) := by
  sorry

end RmsnormHybridLinfL1Challenge
