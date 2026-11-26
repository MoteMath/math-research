/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`alibi-bitsplit-kulisch`)

Pure-`Init` (zero Mathlib) definitions for:
1. IEEE-754 RNE `ALiBi` content swamping, power-of-2 binade asymmetry, format overflow, and exact dyadic slopes.
2. Symmetric uniform `INT_b` bilinear bit-split MSE and exact rational crossover thresholds.
3. Absmax-pinned super-outlier quantization and bit-split reversal.
4. Microscaling `MXFP_b` normal-range relative MSE and exponent-vs-mantissa parity (`W5A7` vs `W6A6`).
5. Mixed-format signed two's-complement Kulisch accumulator widths (`FP4`, `INT4`, `INT8`, `FP8-E4M3`).
6. Exact `Int` Kulisch accumulation vs IEEE-754 FP32 RNE integer accumulation.
-/

namespace AlibiBitsplitKulisch

/-! ### Exact Dyadic Powers and Absolute Value over `Rat` -/

/-- Exact rational power of two `2^k` for `k : Nat`. -/
def pow2Rat (k : Nat) : Rat := ((2 ^ k : Nat) : Rat)

/-- Exact rational inverse power of two `2^{-k}` for `k : Nat`. -/
def invPow2Rat (k : Nat) : Rat := 1 / pow2Rat k

/-- Exact rational integer power of two `2^e` for `e : Int`. -/
def zpow2Rat (e : Int) : Rat :=
  if 0 ≤ e then pow2Rat e.toNat else invPow2Rat (-e).toNat

/-- Exact absolute value on `Rat`. -/
def ratAbs (x : Rat) : Rat := if (0 : Rat) ≤ x then x else -x

/-! ### Pillar 1: Quantized `ALiBi` IEEE-754 RNE Swamping & Dyadic Slopes -/

/-- Exact positive normal `p`-bit floating-point bias `B = M * 2^{e - (p - 1)}`
    in binade `[2^e, 2^{e+1})` with integer significand `M ∈ [2^{p-1}, 2^p - 1]`. -/
def alibiBias (p : Nat) (e : Int) (M : Nat) : Rat :=
  (M : Rat) * zpow2Rat (e - ((p - 1 : Nat) : Int))

/-- Outward half-ULP `2^{e - p}` at binade `[2^e, 2^{e+1})` (moving away from 0, `x ≤ 0`). -/
def alibiHalfUlpOut (p : Nat) (e : Int) : Rat :=
  zpow2Rat (e - (p : Int))

/-- Inward half-ULP at `B = M * 2^{e - (p - 1)}` (moving toward 0, `x > 0`):
    drops by a factor of `2` to `2^{e - p - 1}` at an exact power-of-2 binade boundary `M = 2^{p-1}`. -/
def alibiHalfUlpIn (p : Nat) (e : Int) (M : Nat) : Rat :=
  if M = 2 ^ (p - 1) then zpow2Rat (e - (p : Int) - 1) else zpow2Rat (e - (p : Int))

/-- Exact IEEE-754 Round-to-Nearest-Even (RNE) swamping predicate:
    `fl_p(x - B) = -B` where `B = M * 2^{e - (p - 1)} > 0` is a normal `p`-bit float.
    - For `x ≤ 0` (outward): `|x| = -x` compared against `alibiHalfUlpOut p e` (inclusive iff `M` is even).
    - For `0 < x` (inward): `|x| = x` compared against `alibiHalfUlpIn p e M` (inclusive iff `M` is even). -/
def rneSwampsAtNegB (p : Nat) (e : Int) (M : Nat) (x : Rat) : Prop :=
  if x ≤ 0 then
    if M % 2 = 0 then -x ≤ alibiHalfUlpOut p e else -x < alibiHalfUlpOut p e
  else
    if M % 2 = 0 then x ≤ alibiHalfUlpIn p e M else x < alibiHalfUlpIn p e M

/-- A rational value `v` is exactly representable as a `p`-bit normal float (or `0`). -/
def isExactPBitFloat (p : Nat) (v : Rat) : Prop :=
  v = 0 ∨ ∃ (e : Int) (M : Nat), 2 ^ (p - 1) ≤ M ∧ M < 2 ^ p ∧ ratAbs v = alibiBias p e M

/-- FP8-E4M3 max finite value (`448 = 14 * 2^5`, even significand `14`, ULP `32`, midpoint `464`). -/
def fp8E4M3MaxFinite : Rat := 448

/-- Under RNE, FP8-E4M3 overflows strictly above the tie-to-even midpoint `464 = 448 + 16`. -/
def fp8E4M3Overflows (d : Rat) : Prop := (464 : Rat) < d

/-- FP16 max finite value (`65504 = 2047 * 2^5`, odd significand `2047`, ULP `32`, midpoint `65520`). -/
def fp16MaxFinite : Rat := 65504

/-- Under RNE, FP16 overflows at and above the tie-to-even midpoint `65520 = 65504 + 16`. -/
def fp16Overflows (d : Rat) : Prop := (65520 : Rat) ≤ d

/-! ### Pillar 2A: Symmetric Uniform `INT_b` Bilinear Bit-Split Crossovers -/

/-- Maximum symmetric quantization level `Q_b = 2^{b-1} - 1` for signed `INT_b` (`b ≥ 2`). -/
def intQ (b : Nat) : Nat := 2 ^ (b - 1) - 1

/-- Inverse squared quantization level `Q_b^{-2} = 1 / (2^{b-1} - 1)^2`. -/
def intInvQ2 (b : Nat) : Rat := 1 / ((intQ b * intQ b : Nat) : Rat)

/-- Bilinear uniform `INT` quantization MSE proportional to `cW / Q_{bW}^2 + cX / Q_{bX}^2`. -/
def bilinearIntMSE (bW bX : Nat) (cW cX : Rat) : Rat :=
  cW * intInvQ2 bW + cX * intInvQ2 bX

/-- Exact finite-level rational crossover ratio `R^*(bW, bX)` separating `(bW, bX)` from `(bW - 1, bX + 1)`. -/
def bilinearCrossoverR (bW bX : Nat) : Rat :=
  (intInvQ2 (bW - 1) - intInvQ2 bW) / (intInvQ2 bX - intInvQ2 (bX + 1))

/-! ### Pillar 2A: Absmax-Pinned Super-Outlier Reversal -/

/-- Blockwise absmax quantization step `Δ_X = S / Q_{bX}` when `S > 0` is the block maximum. -/
def absmaxStep (S : Rat) (bX : Nat) : Rat := S / (intQ bX : Rat)

/-- Reconstructed value of the pinned absmax coordinate `Δ_X * Q_{bX}`. -/
def absmaxPinnedQuant (S : Rat) (bX : Nat) : Rat := absmaxStep S bX * (intQ bX : Rat)

/-- Pinned super-outlier dot-product MSE: the absmax spike `S` has `e_X = 0`, contributing
    pure weight error `cW * S^2 / Q_{bW}^2`, while the bulk contributes `cW * bulkX / Q_{bW}^2 + cX / Q_{bX}^2`. -/
def pinnedSuperOutlierMSE (bW bX : Nat) (S cW cX bulkX : Rat) : Rat :=
  cW * (S * S + bulkX) * intInvQ2 bW + cX * intInvQ2 bX

/-! ### Pillar 2B: Microscaling `MXFP_b` Mantissa-Parity Dominance -/

/-- Microscaling floating-point format specification `(totalBits, ebits, mbits)`. -/
structure MxfpFormat where
  totalBits : Nat
  ebits : Nat
  mbits : Nat
  deriving DecidableEq, Repr

/-- `MXFP5-E2M2`: 1 sign + 2 exponent + 2 mantissa = 5 bits. -/
def mxfp5E2M2 : MxfpFormat := ⟨5, 2, 2⟩

/-- `MXFP6-E3M2`: 1 sign + 3 exponent + 2 mantissa = 6 bits. -/
def mxfp6E3M2 : MxfpFormat := ⟨6, 3, 2⟩

/-- `MXFP7-E3M3`: 1 sign + 3 exponent + 3 mantissa = 7 bits. -/
def mxfp7E3M3 : MxfpFormat := ⟨7, 3, 3⟩

/-- Normal-range uniform relative quantization MSE `(1/12) * 4^{-m}` for `m` mantissa bits. -/
def mxfpRelMSE (f : MxfpFormat) : Rat :=
  (1 / 12 : Rat) * invPow2Rat (2 * f.mbits)

/-- Bilinear normal-range relative MSE `cW * mxfpRelMSE fW + cX * mxfpRelMSE fX`. -/
def mxfpProdRelMSE (fW fX : MxfpFormat) (cW cX : Rat) : Rat :=
  cW * mxfpRelMSE fW + cX * mxfpRelMSE fX

/-! ### Pillar 3: Mixed-Format Signed Kulisch Accumulator Widths & FP32 Drift -/

/-- Exact signed two's-complement `W`-bit range predicate: `-2^{W-1} ≤ s ≤ 2^{W-1} - 1`. -/
def fitsSignedWidth (W : Nat) (s : Int) : Prop :=
  -((2 ^ (W - 1) : Nat) : Int) ≤ s ∧ s ≤ ((2 ^ (W - 1) : Nat) : Int) - 1

/-- Exact single-bit tight minimum signed two's-complement accumulator width `W`:
    `2^{W-2} < Mmax * K + 1 ≤ 2^{W-1}` (equivalently `W = ceil(log2(Mmax * K + 1)) + 1`). -/
def isExactMinSignedWidth (Mmax K W : Nat) : Prop :=
  2 ≤ W ∧ 2 ^ (W - 2) < Mmax * K + 1 ∧ Mmax * K + 1 ≤ 2 ^ (W - 1)

/-- Exact maximum scaled integer product `M_max` for `FP4-E2M1 × INT4` (unit `2^{-1}`, `12 × 8 = 96`). -/
def mMaxFP4xINT4 : Nat := 96

/-- Exact maximum scaled integer product `M_max` for `FP4-E2M1 × INT8` (unit `2^{-1}`, `12 × 128 = 1536`). -/
def mMaxFP4xINT8 : Nat := 1536

/-- Exact maximum scaled integer product `M_max` for `INT4 × FP8-E4M3` (unit `2^{-9}`, `8 × 229376 = 1835008`). -/
def mMaxINT4xFP8E4M3 : Nat := 1835008

/-- Exact maximum scaled integer product `M_max` for `FP4-E2M1 × FP8-E4M3` (unit `2^{-10}`, `12 × 229376 = 2752512`). -/
def mMaxFP4xFP8E4M3 : Nat := 2752512

/-- Exact left-to-right Kulisch integer sum. -/
def intSum (xs : List Int) : Int := xs.foldl (· + ·) 0

/-- Exact right-to-left Kulisch integer sum. -/
def intSumR (xs : List Int) : Int := xs.foldr (· + ·) 0

/-- Exact IEEE-754 FP32 (24-bit significand) Round-to-Nearest-Even rounding of a nonnegative integer. -/
def fp32RneNat (n : Nat) : Nat :=
  if n ≤ 2 ^ 24 then n
  else
    let s := Nat.log2 n - 23
    let u := 2 ^ s
    let h := 2 ^ (s - 1)
    let q := n / u
    let r := n % u
    if r < h then q * u
    else if h < r then (q + 1) * u
    else if q % 2 = 0 then q * u else (q + 1) * u

/-- Single IEEE-754 FP32 RNE addition of nonnegative integers. -/
def fp32RneAddNat (a b : Nat) : Nat := fp32RneNat (a + b)

/-- Sequential left-to-right IEEE-754 FP32 RNE accumulation of nonnegative integers. -/
def fp32SumNat (xs : List Nat) : Nat := xs.foldl fp32RneAddNat 0

/-- Explicit `K = 32` `INT4 × FP8-E4M3` scaled-product witness (in units of `2^{-9}`):
    16 terms of `(-8) × (-256) = 2^{20}` followed by 16 terms of `1 × 2^{-9} = 1`. -/
def fp32DriftWitnessK32 : List Nat :=
  List.replicate 16 (2 ^ 20) ++ List.replicate 16 1

end AlibiBitsplitKulisch
