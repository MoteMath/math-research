/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnDyadicSlack.Defs

/-!
# Trusted Challenge Statements (`flashattn-dyadic-slack-bounds`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Exact zero mantissa rounding error of dyadic power-of-two rescaling (`2^-k`) vs eager
   half-ULP rounding drift at non-dyadic midpoints.
2. Universal inductive IEEE-754 RNE one-ULP-per-step collapse under eager rescaling near
   the 1-ULP boundary (`seqPow(p, m * 2^p) = 2^-m`, strictly below true exponential decay).
3. Exact `FP8-E4M3` (`max = 448`, `τ ≤ 8`) and `FP16` (`max = 65504`, `B_c = 64`, `τ ≤ 9`)
   lazy-slack overflow boundaries with the integer windows `τ* ∈ [4, 6]` (`FP16`)
   and `[6, 8]` (`BF16 + FP8`) satisfying the stated inequalities.
4. `FP16` flat-attention overflow cliff at `L = 65520 = 65504 + 16` for one rounding of the exact count `L`
   (exact accumulation assumed; not a sequential `FP16` sum)
   (`Inf / Inf = NaN` or `finite / Inf = 0` collapse at `65520`, `65536`, `131072`).
5. Unconditional boundedness (`l < 2^14 < 65504`) and exact ratio cancellation of dyadic
   exponent normalization (`scale = 2^-1` when `l ≥ 2^14`) for arbitrary sequence length `L`.
6. Exact signed `int32` (`Q8.20`) Kulisch tile accumulator width, zero-drift exactness,
   and unconditional associativity/permutation invariance for `64`-element `FP8`/`UE3M1` tiles.
-/

namespace FlashAttnDyadicSlackChallenge

open FlashAttnDyadicSlack

/-- Theorem 1 (`dyadic_power_of_two_rescale_zero_mantissa_error`):
    Multiplying any normal `p`-mantissa-bit IEEE-754 binary float `(s, e, m)` by an exact
    power of two `2^-k` shifts ONLY the exponent (`e ↦ e - k`), preserves sign and mantissa
    identically, composes additively (`k1 + k2`), preserves normal exponent bounds, and incurs
    exact `0` mantissa rounding error — in contrast to eager non-dyadic RNE midpoints which
    inject exact half-ULP error `1 / 2^(p+1) > 0`. -/
theorem dyadic_power_of_two_rescale_zero_mantissa_error :
    (∀ (p k : Nat) (x : NormalFloat p),
      (x.scaleNegPow2 k).neg = x.neg ∧
      (x.scaleNegPow2 k).mant = x.mant ∧
      (x.scaleNegPow2 k).exp = x.exp - (k : Int) ∧
      (x.scaleNegPow2 k).toRat = x.toRat * invPow2Rat k ∧
      (x.scaleNegPow2 k).toRat - x.toRat * invPow2Rat k = 0) ∧
    (∀ (p k1 k2 : Nat) (x : NormalFloat p),
      (x.scaleNegPow2 k1).scaleNegPow2 k2 = x.scaleNegPow2 (k1 + k2) ∧
      ((x.scaleNegPow2 k1).scaleNegPow2 k2).toRat = x.toRat * invPow2Rat (k1 + k2)) ∧
    (∀ (p k : Nat) (eMin eMax : Int) (x : NormalFloat p),
      eMin + (k : Int) ≤ x.exp → x.exp ≤ eMax →
      eMin ≤ (x.scaleNegPow2 k).exp ∧ (x.scaleNegPow2 k).exp ≤ eMax) ∧
    (∀ (p : Nat), 1 ≤ p →
      rneNatDiv (2 ^ (p + 1) + 1) 2 = 2 ^ p ∧
      (((2 ^ (p + 1) + 1 : Nat) : Rat) / pow2Rat (p + 1)) -
        ((rneNatDiv (2 ^ (p + 1) + 1) 2 : Rat) / pow2Rat p) = invPow2Rat (p + 1) ∧
      (0 : Rat) < invPow2Rat (p + 1)) := by
  sorry

/-- Theorem 2 (`eager_online_softmax_one_ulp_per_step_collapse`):
    Universal inductive IEEE-754 RNE theorem proving that under eager rescaling (`τ = 0`)
    with small monotonic tile jumps near the 1-ULP boundary `α = 1 - 2^{-(p+1)}`, sequential
    multiplication loses exact `1` ULP per tile (`seqPow p (m * 2^p) = 2^-m`, e.g., `1/16`
    at `T = 512` in `BF16` and `1/4` at `T = 2048` in `FP16`), strictly underestimating true
    exponential decay `(1 - 2^{-(p+1)})^(m * 2^p)` for all `p ≥ 1, m ≥ 1`, whereas deferring
    rescale and applying a single exact dyadic shift `2^-k` eliminates intermediate drift. -/
theorem eager_online_softmax_one_ulp_per_step_collapse :
    (∀ (p : Nat) (e : Int) (s : Nat), 2 ^ p < s → s < 2 ^ (p + 1) →
      rneMulOneMinusHalfUlpStep p (e, s) = (e, s - 1)) ∧
    (∀ (p : Nat) (e : Int),
      rneMulOneMinusHalfUlpStep p (e, 2 ^ p) = (e - 1, 2 ^ (p + 1) - 1) ∧
      seqPowState p (2 ^ p) (e, 2 ^ p) = (e - 1, 2 ^ p)) ∧
    (∀ (p m : Nat), seqPow p (m * 2 ^ p) = invPow2Rat m) ∧
    (seqPow 7 512 = (1 / 16 : Rat) ∧ seqPow 10 2048 = (1 / 4 : Rat)) ∧
    (∀ (p m : Nat), 1 ≤ p → 1 ≤ m →
      seqPow p (m * 2 ^ p) < ratPow (1 - invPow2Rat (p + 1)) (m * 2 ^ p)) ∧
    (∀ (p k : Nat) (x : NormalFloat p),
      (x.scaleNegPow2 k).toRat = x.toRat * invPow2Rat k) := by
  sorry

/-- Theorem 3 (`slack_threshold_fp16_fp8_overflow_boundary_exact`):
    Exact integer overflow boundaries for lazy slack `τ` (base-2 units, weight amplification
    `2^τ`): proves `FP8-E4M3` (`max = 448`) safety iff `τ ≤ 8` (`2^8 = 256 ≤ 448`, overflowing
    at `τ ≥ 9` and `τ = 12`), general power-of-two tile width `2^b * 2^τ ≤ 65504 ↔ b + τ ≤ 15`,
    `FP16` (`max = 65504`) tile-sum safety for `B_c = 64` iff `τ ≤ 9` (overflowing at `τ ≥ 10`),
    and exact certification of the Pareto-safe windows `τ* ∈ [4, 6]` (`FP16`) and
    `τ* ∈ [6, 8]` (`BF16 + FP8`). -/
theorem slack_threshold_fp16_fp8_overflow_boundary_exact :
    (fp8E4M3Max = 448 ∧ fp16MaxNormal = 65504 ∧ tileWidthBc = 64) ∧
    (∀ τ : Nat, 2 ^ τ ≤ fp8E4M3Max ↔ τ ≤ 8) ∧
    (2 ^ 8 = 256 ∧ 2 ^ 8 ≤ fp8E4M3Max ∧
     2 ^ 9 = 512 ∧ fp8E4M3Max < 2 ^ 9 ∧
     2 ^ 12 = 4096 ∧ fp8E4M3Max < 2 ^ 12) ∧
    (∀ b τ : Nat, 2 ^ b * 2 ^ τ ≤ fp16MaxNormal ↔ b + τ ≤ 15) ∧
    (∀ τ : Nat, tileWidthBc * 2 ^ τ ≤ fp16MaxNormal ↔ τ ≤ 9) ∧
    (tileWidthBc * 2 ^ 9 = 32768 ∧ tileWidthBc * 2 ^ 9 ≤ fp16MaxNormal ∧
     tileWidthBc * 2 ^ 10 = 65536 ∧ fp16MaxNormal < tileWidthBc * 2 ^ 10 ∧
     tileWidthBc * 2 ^ 12 = 262144 ∧ fp16MaxNormal < tileWidthBc * 2 ^ 12) ∧
    (∀ τ : Nat, 4 ≤ τ → τ ≤ 6 →
      2 ^ τ ≤ fp8E4M3Max ∧ tileWidthBc * 2 ^ τ ≤ 4096 ∧
      15 * (tileWidthBc * 2 ^ τ) ≤ fp16MaxNormal) ∧
    (∀ τ : Nat, 6 ≤ τ → τ ≤ 8 →
      2 ^ τ ≤ fp8E4M3Max ∧ tileWidthBc * 2 ^ τ ≤ 16384 ∧
      tileWidthBc * 2 ^ τ ≤ fp16MaxNormal) := by
  sorry

/-- Theorem 4 (`fp16_flat_attention_65520_overflow_cliff_exact`):
    Theorem about one `FP16` RNE rounding of the exact integer `L` (exact accumulation assumed;
    a sequential `FP16` sum is not modelled) proving `FP16_MAX = 65504`, `ulp = 32`, and overflow
    midpoint `65520 = 65504 + 16`: flat uniform attention (`exp(0) = 1` per token,
    even after subtracting `m = max(s)`) stays finite at `L = 65504` and `L = 65519`,
    overflows `l` to `+Inf` at exact `L = 65520` (and for all `L ≥ 65520`, including `65536`
    and `131072`), triggering `Inf / Inf = NaN` or `finite / Inf = 0` silent collapse. -/
theorem fp16_flat_attention_65520_overflow_cliff_exact :
    (fp16MaxNormal = 65504 ∧ fp16TopUlp = 32 ∧ fp16OverflowThreshold = 65520) ∧
    (∀ L : Nat, 2 ^ 15 ≤ L → L < 2 ^ 16 →
      (binadeRneNat 10 15 L = 2 ^ 16 ↔ fp16OverflowThreshold ≤ L)) ∧
    (∀ L : Nat, fp16RneNatToExt L = .posInf ↔ fp16OverflowThreshold ≤ L) ∧
    (fp16RneNatToExt 65504 = .finite 65504 ∧
     fp16RneNatToExt 65519 = .finite 65504 ∧
     fp16RneNatToExt 65520 = .posInf ∧
     fp16RneNatToExt 65536 = .posInf ∧
     fp16RneNatToExt 131072 = .posInf) ∧
    (fpDiv .posInf .posInf = .nan ∧
     (∀ x : Rat, fpDiv (.finite x) .posInf = .finite 0)) ∧
    (∀ L : Nat,
      exactAttentionL (List.replicate L ((1 : Rat), (1 : Rat))) = (L : Rat)) := by
  sorry

/-- Theorem 5 (`dyadic_exponent_normalization_cancels_identically`):
    Exact algebraic and bit-exact IEEE-754 theorem proving that whenever `l ≥ 2^14 = 16384`,
    scaling both `(O, l)` by exact `2^-1` (`0.5`) incurs zero mantissa rounding error in
    normal `FP16`, keeps `0 ≤ l < 2^14 < 65504` unconditionally for arbitrary sequence length
    `L` (any finite list of bounded weights `0 ≤ w ≤ 16384`), and cancels identically in the
    final ratio `(2^-k O) / (2^-k l) = O / l` with ZERO division/reconstruction cost. -/
theorem dyadic_exponent_normalization_cancels_identically :
    (∀ (x : NormalFloat 10), (-13 : Int) ≤ x.exp →
      (-14 : Int) ≤ (x.scaleNegPow2 1).exp ∧
      (x.scaleNegPow2 1).neg = x.neg ∧
      (x.scaleNegPow2 1).mant = x.mant ∧
      (x.scaleNegPow2 1).toRat = x.toRat * invPow2Rat 1) ∧
    (∀ (O l : Rat) (k : Nat), l ≠ 0 →
      (O * invPow2Rat k) / (l * invPow2Rat k) = O / l) ∧
    (∀ (p k : Nat) (xO xl : NormalFloat p), xl.toRat ≠ 0 →
      (xO.scaleNegPow2 k).toRat / (xl.scaleNegPow2 k).toRat = xO.toRat / xl.toRat) ∧
    (∀ (xs : List (Rat × Rat)),
      (∀ wv ∈ xs, (0 : Rat) ≤ wv.1 ∧ wv.1 ≤ fp16NormThreshold) →
      let (O, l, k) := dyadicNormRun xs
      (0 : Rat) ≤ l ∧
      l < fp16NormThreshold ∧
      l < (fp16MaxNormal : Rat) ∧
      O = exactAttentionO xs * invPow2Rat k ∧
      l = exactAttentionL xs * invPow2Rat k ∧
      (exactAttentionL xs ≠ 0 → O / l = exactAttentionO xs / exactAttentionL xs)) := by
  sorry

/-- Theorem 6 (`flash_tile_int32_kulisch_associativity_and_exactness`):
    Exact signed `int32` (`Q8.20`) Kulisch accumulator width and unconditional associativity,
    split-merge, and `List.Perm` permutation-invariance proof for `64`-element `P * V` tiles
    under quantized `FP8-E4M3` and `UE3M1` attention weights, certifying exact zero-drift
    tile accumulation with zero signed 32-bit overflow. -/
theorem flash_tile_int32_kulisch_associativity_and_exactness :
    (∀ (pInt vInt : Int),
      ((fp8ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
        ((pInt : Rat) / pow2Rat 9) * ((vInt : Rat) / pow2Rat 9) ∧
      ((ue3m1ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
        ((pInt : Rat) / pow2Rat 7) * ((vInt : Rat) / pow2Rat 9)) ∧
    (∀ (xs : List Int) (M : Int),
      xs.length ≤ tileWidthBc → 0 ≤ M → (tileWidthBc : Int) * M ≤ int32Max →
      (∀ x ∈ xs, -M ≤ x ∧ x ≤ M) →
      inInt32Range (kulischSum xs)) ∧
    (∀ (xs : List Int),
      xs.length ≤ tileWidthBc →
      (∀ x ∈ xs, -(4 * (kulischScale : Int)) ≤ x ∧ x ≤ 4 * (kulischScale : Int)) →
      inInt32Range (kulischSum xs) ∧
      -(2 ^ 28 : Int) ≤ kulischSum xs ∧ kulischSum xs ≤ (2 ^ 28 : Int)) ∧
    (∀ (xs : List Int),
      (kulischSum xs : Rat) / (kulischScale : Rat) =
        ratSum (xs.map (fun (t : Int) => (t : Rat) / (kulischScale : Rat))) ∧
      kulischFoldl xs = kulischSum xs) ∧
    (∀ (xs ys : List Int),
      kulischSum (xs ++ ys) = kulischSum xs + kulischSum ys ∧
      kulischSum xs.reverse = kulischSum xs ∧
      (xs.Perm ys → kulischSum xs = kulischSum ys)) := by
  sorry

end FlashAttnDyadicSlackChallenge
