/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RmsnormHybridLinfL1.RatOrder

/-!
# Exact IEEE-754 RNE `sum(x_i^2)` Swamping Horizon Theorem (Theorem 4)

Proves:
1. Universal IEEE-754 RNE tie-to-even swamping at `S_swamp(p) = 2^p` for every precision `p ≥ 2`
   and exact fixed-point persistence across arbitrarily many sequential `+ 1` additions.
2. Bit-exact certification of minimal outlier swamping thresholds `M_swamp` (together with
   non-swamping of their immediate predecessor `M_swamp - 1 ulp`) across all 5 formats:
   - BF16 (`p = 8`, `0x4180` = `16`, `fl(M^2) = 256`)
   - FP16 (`p = 11`, `0x51a8` = `181/4`, `fl(M^2) = 2048`)
   - FP8-E4M3 (`p = 4`, `0x48` = `4`, `fl(M^2) = 16`)
   - FP8-E5M2 (`p = 3`, `0x42` = `3`, `fl(M^2) = 8`)
   - MXFP4-E2M1 (`p = 2`, `0x4` = `2`, `fl(M^2) = 4`)
-/

namespace RmsnormHybridLinfL1

/-- Universal RNE tie-to-even swamping at `S_swamp(p) = 2^p`:
    For every precision `p ≥ 2`, `ulp(2^p) = 2`, `2^p` has even significand `2^(p-1)`,
    so RNE rounds `2^p + 1` back to `2^p`. -/
theorem rne_swamp_horizon_universal (p : Nat) (hp : 2 ≤ p) :
    rneDivNat (2 ^ p + 1) 2 * 2 = 2 ^ p := by
  have hp1 : p = (p - 1) + 1 := by omega
  have hp2 : p - 1 = (p - 2) + 1 := by omega
  have hpow1 : 2 ^ p = 2 * 2 ^ (p - 1) := by
    conv => lhs; rw [hp1]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hpow2 : 2 ^ (p - 1) = 2 * 2 ^ (p - 2) := by
    conv => lhs; rw [hp2]
    rw [Nat.pow_succ, Nat.mul_comm]
  unfold rneDivNat
  have hq : (2 ^ p + 1) / 2 = 2 ^ (p - 1) := by omega
  have hr : (2 ^ p + 1) % 2 = 1 := by omega
  rw [hq, hr]
  have hnotgt : ¬ (2 * 1 > 2) := by omega
  simp only [hnotgt, ↓reduceIte]
  have heven : (2 ^ (p - 1) &&& 1) = 0 := by
    rw [hpow2]
    have hmod : (2 * 2 ^ (p - 2)) % 2 = 0 := by omega
    rw [Nat.and_one_is_mod]
    exact hmod
  rw [heven, Nat.add_zero]
  omega

/-- Universal fixed-point persistence: if `fl(acc + 1) = acc`, then sequential accumulation
    drops ALL `n` unit bulk squares for every `n : Nat`. -/
theorem seqAddOnes_fixed_point (fmt : FloatFormat) (acc : Nat)
    (hfix : fmt.flAdd acc (fmt.encodeDyadic 1 0) = acc) :
    ∀ n : Nat, fmt.seqAddOnes acc n = acc := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [FloatFormat.seqAddOnes, hfix]
    exact ih

/-- Helper: decode a bit pattern to its exact `Rat` value via pure-integer `decodeDyadic`. -/
theorem decode_eq_finite_of_dyadic (fmt : FloatFormat) (bits : Nat) (m e : Int) (v : Rat)
    (hd : fmt.decodeDyadic bits = DyadicVal.finite m e)
    (hv : (m : Rat) * pow2Int e = v) :
    fmt.decode bits = FloatVal.finite v := by
  unfold FloatFormat.decode
  rw [hd]
  dsimp only
  rw [hv]

/-- Headline Theorem 4: Exact `sum(x_i^2)` Swamping Horizon across Universal Precision `p ≥ 2`
    and Bit-Exact Certification for BF16, FP16, FP8-E4M3, FP8-E5M2, and MXFP4-E2M1. -/
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
  refine ⟨rne_swamp_horizon_universal, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, seqAddOnes_fixed_point fmtBF16 _ (by decide), by decide⟩
    · exact decode_eq_finite_of_dyadic fmtBF16 0x4180 128 (-3) 16 (by decide)
        (by unfold pow2Int invPow2Rat pow2Rat; grind)
    · exact decode_eq_finite_of_dyadic fmtBF16 _ 128 1 256 (by decide)
        (by unfold pow2Int pow2Rat; grind)
  · refine ⟨rfl, ?_, ?_, seqAddOnes_fixed_point fmtFP16 _ (by decide), by decide⟩
    · exact decode_eq_finite_of_dyadic fmtFP16 0x51a8 1448 (-5) (181 / 4) (by decide)
        (by unfold pow2Int invPow2Rat pow2Rat; grind)
    · exact decode_eq_finite_of_dyadic fmtFP16 _ 1024 1 2048 (by decide)
        (by unfold pow2Int pow2Rat; grind)
  · refine ⟨rfl, ?_, ?_, seqAddOnes_fixed_point fmtFP8E4M3 _ (by decide), by decide⟩
    · exact decode_eq_finite_of_dyadic fmtFP8E4M3 0x48 8 (-1) 4 (by decide)
        (by unfold pow2Int invPow2Rat pow2Rat; grind)
    · exact decode_eq_finite_of_dyadic fmtFP8E4M3 _ 8 1 16 (by decide)
        (by unfold pow2Int pow2Rat; grind)
  · refine ⟨rfl, ?_, ?_, seqAddOnes_fixed_point fmtFP8E5M2 _ (by decide), by decide⟩
    · exact decode_eq_finite_of_dyadic fmtFP8E5M2 0x42 6 (-1) 3 (by decide)
        (by unfold pow2Int invPow2Rat pow2Rat; grind)
    · exact decode_eq_finite_of_dyadic fmtFP8E5M2 _ 4 1 8 (by decide)
        (by unfold pow2Int pow2Rat; grind)
  · refine ⟨rfl, ?_, ?_, seqAddOnes_fixed_point fmtMXFP4 _ (by decide), by decide⟩
    · exact decode_eq_finite_of_dyadic fmtMXFP4 0x4 2 0 2 (by decide)
        (by unfold pow2Int pow2Rat; grind)
    · exact decode_eq_finite_of_dyadic fmtMXFP4 _ 2 1 4 (by decide)
        (by unfold pow2Int pow2Rat; grind)

end RmsnormHybridLinfL1
