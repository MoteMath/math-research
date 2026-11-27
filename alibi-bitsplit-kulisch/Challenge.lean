/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlibiBitsplitKulisch.Defs

/-!
# Trusted Challenge Statements (`alibi-bitsplit-kulisch`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. `ALiBi` content-swamping threshold for the hand-written RNE predicate `rneSwampsAtNegB`, power-of-2 binade asymmetry, format
   overflows (`FP8-E4M3` at `d = 465`, `FP16` at `d = 65520 < 128K`), and zero-error dyadic slopes.
2. Exact finite-level symmetric `INT_b` bilinear bit-split crossover thresholds
   (`W4A4 -> W3A5` at `125/22`, `W3A5 -> W2A6` at `24025/92`, `W6A6 -> W5A7` at `10143/2350`).
3. Absmax-pinned super-outlier bit-split reversal (`W5A3` beats `W4A4`, `W4A2` beats `W3A3`).
4. Microscaling `MXFP5-E2M2 × MXFP7-E3M3` (`W5A7`) mantissa-parity dominance over `MXFP6-E3M2 × MXFP6-E3M2` (`W6A6`).
5. Exact single-bit tight signed two's-complement Kulisch accumulator widths across 4 mixed formats.
6. Exact `int64_t` Kulisch associativity and permutation invariance vs explicit `K = 32` `INT4 × FP8-E4M3` FP32 RNE drift.
-/

namespace AlibiBitsplitKulischChallenge

open AlibiBitsplitKulisch

/-- Theorem 1 (`alibi_content_swamping_and_dyadic_slope_exact`):
    Universal content-swamping threshold `B ≥ 2^{p+1} |x|` for the hand-written RNE predicate
    `rneSwampsAtNegB` (a model of IEEE-754 round-to-nearest-even), exact power-of-2
    binade asymmetry for `+x` vs `-x`, concrete `BF16`, `FP8-E4M3` (`d = 19..23` swamping &
    `d = 465` overflow), and `FP16` (`d = 65520 < 131072` overflow) horizons, and exact zero
    multiplication rounding error for dyadic slopes `m = 2^{-k}`. -/
theorem alibi_content_swamping_and_dyadic_slope_exact :
    (∀ (p : Nat) (e : Int) (M : Nat) (x : Rat),
      2 ≤ p → 2 ^ (p - 1) ≤ M → M < 2 ^ p →
      pow2Rat (p + 1) * ratAbs x ≤ alibiBias p e M →
      rneSwampsAtNegB p e M x) ∧
    (∀ (p : Nat) (e : Int), 2 ≤ p →
      let x := zpow2Rat (e - (p : Int))
      alibiBias p e (2 ^ (p - 1)) = zpow2Rat e ∧
      rneSwampsAtNegB p e (2 ^ (p - 1)) (-x) ∧
      ¬ rneSwampsAtNegB p e (2 ^ (p - 1)) x) ∧
    (alibiBias 8 8 128 = 256 ∧
      rneSwampsAtNegB 8 8 128 (-1) ∧
      ¬ rneSwampsAtNegB 8 8 128 1 ∧
      alibiBias 8 8 130 = 260 ∧
      rneSwampsAtNegB 8 8 130 1) ∧
    (alibiBias 4 4 8 = 16 ∧
      rneSwampsAtNegB 4 4 8 (-1) ∧
      ¬ rneSwampsAtNegB 4 4 8 1 ∧
      alibiBias 4 4 10 = 20 ∧
      rneSwampsAtNegB 4 4 10 1 ∧
      fp8E4M3Overflows 465 ∧
      ¬ fp8E4M3Overflows 464) ∧
    (fp16Overflows 65520 ∧
      (65520 : Nat) < 131072 ∧
      ¬ fp16Overflows 65519) ∧
    (∀ (p : Nat) (v : Rat) (k : Nat),
      isExactPBitFloat p v → isExactPBitFloat p (v * invPow2Rat k)) ∧
    (∀ (p d k : Nat), 2 ≤ p → d ≤ 2 ^ p →
      isExactPBitFloat p (d : Rat) ∧ isExactPBitFloat p ((d : Rat) * invPow2Rat k)) ∧
    (∀ (p d k : Nat), 2 ≤ p → d % 2 = 0 → d ≤ 2 ^ (p + 1) →
      isExactPBitFloat p (d : Rat) ∧ isExactPBitFloat p ((d : Rat) * invPow2Rat k)) := by
  sorry

/-- Theorem 2 (`bilinear_int_asymmetric_bitsplit_crossovers_exact`):
    Universal exact finite-level symmetric `INT_b` bit-split crossover equivalence and exact
    rational thresholds (`125/22`, `24025/92`, `10143/2350`, `49/5`, `10571/2254`). -/
theorem bilinear_int_asymmetric_bitsplit_crossovers_exact :
    (∀ (bW bX : Nat) (cW cX : Rat), 3 ≤ bW → 2 ≤ bX → (0 : Rat) < cW →
      (bilinearIntMSE (bW - 1) (bX + 1) cW cX < bilinearIntMSE bW bX cW cX ↔
        bilinearCrossoverR bW bX < cX / cW)) ∧
    (bilinearCrossoverR 4 4 = 125 / 22 ∧
      (142 / 100 : Rat) < bilinearCrossoverR 4 4 / 4) ∧
    (bilinearCrossoverR 3 5 = 24025 / 92 ∧
      (408 / 100 : Rat) < bilinearCrossoverR 3 5 / 64) ∧
    (bilinearCrossoverR 6 6 = 10143 / 2350 ∧
      (1079 / 1000 : Rat) < bilinearCrossoverR 6 6 / 4) ∧
    (bilinearCrossoverR 3 3 = 49 / 5 ∧
      bilinearCrossoverR 5 5 = 10571 / 2254) := by
  sorry

/-- Theorem 3 (`absmax_pinned_superoutlier_bitsplit_reversal`):
    Exact absmax pinning identity (`e_X = 0` on spike `S`), universal super-outlier bit-split
    reversal threshold, and concrete reversals (`W5A3` beats `W4A4` iff `S^2 > 125/22`,
    `W4A2` beats `W3A3` iff `S^2 > 49/5`). -/
theorem absmax_pinned_superoutlier_bitsplit_reversal :
    (∀ (bX : Nat) (S w wHat : Rat), 2 ≤ bX →
      absmaxPinnedQuant S bX = S ∧
      wHat * absmaxPinnedQuant S bX - w * S = (wHat - w) * S) ∧
    (∀ (bW bX : Nat) (S cW cX bulkX : Rat), 2 ≤ bW → 3 ≤ bX → (0 : Rat) < cW →
      (pinnedSuperOutlierMSE (bW + 1) (bX - 1) S cW cX bulkX <
        pinnedSuperOutlierMSE bW bX S cW cX bulkX ↔
        (cX / cW) * bilinearCrossoverR bX bW < S * S + bulkX)) ∧
    (∀ S : Rat,
      (pinnedSuperOutlierMSE 5 3 S 1 1 0 < pinnedSuperOutlierMSE 4 4 S 1 1 0 ↔
        (125 / 22 : Rat) < S * S) ∧
      ((3 : Rat) ≤ S → pinnedSuperOutlierMSE 5 3 S 1 1 0 < pinnedSuperOutlierMSE 4 4 S 1 1 0)) ∧
    (∀ S : Rat,
      (pinnedSuperOutlierMSE 4 2 S 1 1 0 < pinnedSuperOutlierMSE 3 3 S 1 1 0 ↔
        (49 / 5 : Rat) < S * S) ∧
      ((4 : Rat) ≤ S → pinnedSuperOutlierMSE 4 2 S 1 1 0 < pinnedSuperOutlierMSE 3 3 S 1 1 0)) := by
  sorry

/-- Theorem 4 (`mxfp_w5a7_beats_w6a6_mantissa_parity_exact`):
    At identical 12-bit budget `B_tot = 12`, asymmetric `W5A7` (`MXFP5-E2M2 × MXFP7-E3M3`,
    5 total mantissa bits) strictly beats symmetric `W6A6` (`MXFP6-E3M2 × MXFP6-E3M2`,
    4 total mantissa bits) by an exact factor of `8/5` (`1.6x`) for symmetric weighting and
    unconditionally for all positive `(cW, cX)`. -/
theorem mxfp_w5a7_beats_w6a6_mantissa_parity_exact :
    (mxfp5E2M2.totalBits + mxfp7E3M3.totalBits = 12 ∧
      mxfp6E3M2.totalBits + mxfp6E3M2.totalBits = 12 ∧
      mxfp5E2M2.mbits + mxfp7E3M3.mbits = 5 ∧
      mxfp6E3M2.mbits + mxfp6E3M2.mbits = 4) ∧
    (mxfpRelMSE mxfp5E2M2 = 1 / 192 ∧
      mxfpRelMSE mxfp6E3M2 = 1 / 192 ∧
      mxfpRelMSE mxfp7E3M3 = 1 / 768 ∧
      mxfpRelMSE mxfp6E3M2 / mxfpRelMSE mxfp7E3M3 = 4) ∧
    (∀ c : Rat, (0 : Rat) < c →
      mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 c c / mxfpProdRelMSE mxfp5E2M2 mxfp7E3M3 c c = 8 / 5 ∧
      mxfpProdRelMSE mxfp5E2M2 mxfp7E3M3 c c < mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 c c) ∧
    (∀ cW cX : Rat, (0 : Rat) < cW → (0 : Rat) < cX →
      mxfpProdRelMSE mxfp5E2M2 mxfp7E3M3 cW cX < mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 cW cX ∧
      mxfpProdRelMSE mxfp7E3M3 mxfp5E2M2 cW cX < mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 cW cX) := by
  sorry

/-- Theorem 5 (`mixed_format_signed_kulisch_width_exact`):
    Universal single-bit tight signed two's-complement Kulisch accumulator width theorem across
    all 4 mixed formats (`FP4×INT4`, `FP4×INT8`, `INT4×FP8-E4M3`, `FP4×FP8-E4M3`) at
    `K ∈ {32, 128, 4096, 16384}`, proving `INT4×FP8-E4M3` needs `27b` at `K = 32` (`> 24b` FP32)
    and `34b` at `K = 4096` (`> 32b` `int32_t`), while `int64_t` retains `≥ 27` bits headroom. -/
theorem mixed_format_signed_kulisch_width_exact :
    (∀ (Mmax K W : Nat), isExactMinSignedWidth Mmax K W →
      (∀ xs : List Int, xs.length ≤ K →
        (∀ x ∈ xs, -(Mmax : Int) ≤ x ∧ x ≤ (Mmax : Int)) →
        fitsSignedWidth W (intSum xs)) ∧
      ¬ fitsSignedWidth (W - 1) (intSum (List.replicate K (Mmax : Int)))) ∧
    (isExactMinSignedWidth mMaxFP4xINT4 32 13 ∧
      isExactMinSignedWidth mMaxFP4xINT4 128 15 ∧
      isExactMinSignedWidth mMaxFP4xINT4 4096 20 ∧
      isExactMinSignedWidth mMaxFP4xINT4 16384 22) ∧
    (isExactMinSignedWidth mMaxFP4xINT8 32 17 ∧
      isExactMinSignedWidth mMaxFP4xINT8 128 19 ∧
      isExactMinSignedWidth mMaxFP4xINT8 4096 24 ∧
      isExactMinSignedWidth mMaxFP4xINT8 16384 26) ∧
    (isExactMinSignedWidth mMaxINT4xFP8E4M3 32 27 ∧
      isExactMinSignedWidth mMaxINT4xFP8E4M3 128 29 ∧
      isExactMinSignedWidth mMaxINT4xFP8E4M3 4096 34 ∧
      isExactMinSignedWidth mMaxINT4xFP8E4M3 16384 36 ∧
      (24 : Nat) < 27 ∧ (32 : Nat) < 34) ∧
    (isExactMinSignedWidth mMaxFP4xFP8E4M3 32 28 ∧
      isExactMinSignedWidth mMaxFP4xFP8E4M3 128 30 ∧
      isExactMinSignedWidth mMaxFP4xFP8E4M3 4096 35 ∧
      isExactMinSignedWidth mMaxFP4xFP8E4M3 16384 37 ∧
      (37 : Nat) + 27 = 64) := by
  sorry

/-- Theorem 6 (`kulisch_int64_exact_associativity_vs_fp32_drift`):
    Exact associativity, split-merge, reversal, and `List.Perm` permutation invariance of exact
    `int64_t` Kulisch accumulation (`0` order diffs), alongside an explicit `K = 32`
    `INT4 × FP8-E4M3` witness where FP32 RNE fails exact associativity (`16777216 ≠ 16777232`). -/
theorem kulisch_int64_exact_associativity_vs_fp32_drift :
    (∀ xs ys : List Int, intSum (xs ++ ys) = intSum xs + intSum ys) ∧
    (∀ xs ys zs : List Int, intSum ((xs ++ ys) ++ zs) = intSum (xs ++ (ys ++ zs))) ∧
    (∀ xs : List Int, intSum xs = intSumR xs) ∧
    (∀ xs : List Int, intSum xs.reverse = intSum xs) ∧
    (∀ xs ys : List Int, List.Perm xs ys → intSum xs = intSum ys) ∧
    (fp32DriftWitnessK32.length = 32 ∧
      (∀ x ∈ fp32DriftWitnessK32, x ≤ mMaxINT4xFP8E4M3) ∧
      intSum (fp32DriftWitnessK32.map Int.ofNat) = 16777232 ∧
      intSum (fp32DriftWitnessK32.reverse.map Int.ofNat) = 16777232 ∧
      fitsSignedWidth 64 (intSum (fp32DriftWitnessK32.map Int.ofNat)) ∧
      fp32SumNat fp32DriftWitnessK32 = 16777216 ∧
      fp32SumNat fp32DriftWitnessK32.reverse = 16777232 ∧
      fp32SumNat fp32DriftWitnessK32 ≠ fp32SumNat fp32DriftWitnessK32.reverse) := by
  sorry

end AlibiBitsplitKulischChallenge
