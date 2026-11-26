/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RmsnormHybridLinfL1

/-!
# Verified Solutions (`rmsnorm-hybrid-linf-l1`)
-/

namespace RmsnormHybridLinfL1Challenge

open RmsnormHybridLinfL1

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
        hybridLowerConstSq α ((s : Rat) * α) * meanSq (kSparseVec (s * s) s)) :=
  RmsnormHybridLinfL1.hybrid_linf_l1_exact_upper_and_lower_envelopes

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
    (∀ C : Rat, 1 ≤ C → ∃ d : Nat, 1 ≤ d ∧ ∀ α β : Rat, 0 < α → 0 < β → C < hybridKappaSq d α β) :=
  RmsnormHybridLinfL1.hybrid_linf_l1_minimax_d_quarter_law

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
     hybridKappaSq 16384 (invPow2Rat 7) 1 = 129 / 2) :=
  RmsnormHybridLinfL1.dyadic_llama3_d4096_hybrid_norm_exact

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
       fmtMXFP4.flMul 0x3 0x3) :=
  RmsnormHybridLinfL1.bf16_fp16_fp8_sumsq_swamping_horizon_exact

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
      fmtFP8E5M2.decode r.2.2 = FloatVal.finite (-8))) :=
  RmsnormHybridLinfL1.bf16_fp16_onepass_layernorm_negative_variance_exact

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
        (0 : Rat) ≤ twoPassVarRounded fl x μHat) :=
  RmsnormHybridLinfL1.twopass_shifted_mean_variance_nonneg_universal

end RmsnormHybridLinfL1Challenge
