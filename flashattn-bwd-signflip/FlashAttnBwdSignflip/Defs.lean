/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Definitions for FlashAttention Backward-Pass Low-Precision Stability Laws

Pure `Init` (zero Mathlib) exact rational and IEEE-754 RNE definitions for:
1. Finite sums over `Fin n`, dot products, L1/L2 norms, and Softmax backward-pass operators.
2. Exact IEEE-754 Round-to-Nearest-Even (RNE) predicates for `1 - ε` snapping to `1`
   and midpoint rounding `s * (1 + 2^{-(m+1)}) ↦ s`.
3. Direct `P · dP` midpoint DC-leakage ratio `1 / (2^{m+1} + 1)` and FlashAttention
   `D_i = dO · fl(O)` orthogonal divergence condition numbers.
4. Key-centering `dQ = dS (K - 1 K_bar^T)` operator.
5. Bit-exact OCP/IEEE floating-point format specifications (`U-E3M1`, `MXFP4-E2M1`,
   `MXFP4-E2M1-BLK`, `FP8-E4M3`, `FP8-E5M2`, `BF16`, `FP16`).
-/

namespace FlashAttnBwdSignflip

/-- Exact power of two as a rational number: `2^k : Rat`. -/
def pow2Rat (k : Nat) : Rat := ((2 ^ k : Nat) : Rat)

/-- Exact reciprocal power of two as a rational number: `2^{-k} : Rat`. -/
def invPow2Rat (k : Nat) : Rat := (1 : Rat) / pow2Rat k

/-- Exact absolute value on `Rat`. -/
def ratAbs (x : Rat) : Rat := if (0 : Rat) ≤ x then x else -x

/-- Recursive finite sum over `Fin k → Rat`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f =>
    finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat := finSumAux n f

/-- Exact finite sum excluding index `i`: `∑_{j ≠ i} f j`. -/
def finSumExcept {n : Nat} (i : Fin n) (f : Fin n → Rat) : Rat :=
  finSum (fun j : Fin n => if j = i then (0 : Rat) else f j)

/-- Exact dot product `∑_{j : Fin n} a j * b j`. -/
def dotProd {n : Nat} (a b : Fin n → Rat) : Rat :=
  finSum (fun j => a j * b j)

/-- Exact squared Euclidean norm `∑_{j : Fin n} (a j)^2`. -/
def l2NormSq {n : Nat} (a : Fin n → Rat) : Rat :=
  finSum (fun j => a j * a j)

/-- Exact Hadamard L1 norm `∑_{j : Fin n} |a j * b j|`. -/
def hadamardL1 {n : Nat} (a b : Fin n → Rat) : Rat :=
  finSum (fun j => ratAbs (a j * b j))

/-- Softmax backward scalar `D_i = ∑_j p_j dP_j`. -/
def softmaxD {n : Nat} (p dP : Fin n → Rat) : Rat :=
  dotProd p dP

/-- Standard FlashAttention Softmax backward entry `dS_i = p_i (dP_i - D)` where `D = ∑_j p_j dP_j`. -/
def softmaxGradStd {n : Nat} (p dP : Fin n → Rat) (i : Fin n) : Rat :=
  p i * (dP i - softmaxD p dP)

/-- Softmax backward entry using an externally supplied scalar `D_hat`: `p_i (dP_i - D_hat)`. -/
def softmaxGradWithD {n : Nat} (p dP : Fin n → Rat) (dHat : Rat) (i : Fin n) : Rat :=
  p i * (dP i - dHat)

/-- Cancellation-free Softmax backward entry `dS_i^{cf} = p_i ∑_{j ≠ i} p_j (dP_i - dP_j)`. -/
def softmaxGradCF {n : Nat} (p dP : Fin n → Rat) (i : Fin n) : Rat :=
  p i * finSumExcept i (fun j => p j * (dP i - dP j))

/-- IEEE-754 RNE snap-to-one predicate for an `m`-bit mantissa binary format (`e_min_normal ≤ -1`):
    on `[1 - 2^{-(m+1)}, 1]`, the lower neighbor `1 - 2^{-(m+1)}` has odd significand `2^{m+1} - 1`
    and `1` has even significand `2^m`, so RNE maps `x` to `1` iff
    `1 - 2^{-(m+1)} ≤ x ≤ 1` and `1 - x ≤ x - (1 - 2^{-(m+1)})`. -/
def rneSnapsToOne (m : Nat) (x : Rat) : Prop :=
  (1 - invPow2Rat (m + 1) ≤ x ∧ x ≤ 1) ∧
  1 - x ≤ x - (1 - invPow2Rat (m + 1))

/-- Exact tail-mass snap threshold `ε_snap(m) = 2^{-(m+2)}`. -/
def epsSnap (m : Nat) : Rat := invPow2Rat (m + 2)

/-- IEEE-754 RNE predicate on `[s, s (1 + 2^{-m})]` (where `s` has even significand `2^m` and
    `s (1 + 2^{-m})` has odd significand `2^m + 1`): `x` rounds (or ties-to-even) to `s` iff
    `s ≤ x` and `x - s ≤ s (1 + 2^{-m}) - x`. -/
def rneRoundsToLowerEven (m : Nat) (s x : Rat) : Prop :=
  s ≤ x ∧ x - s ≤ s * (1 + invPow2Rat m) - x

/-- Exact direct `P · dP` midpoint zero-sum DC-leakage ratio `Z_direct^* = 1 / (2^{m+1} + 1)`. -/
def directMidpointLeakage (m : Nat) : Rat :=
  (1 : Rat) / (pow2Rat (m + 1) + 1)

/-- Constant-offset upstream gradient `dP_0 = c`, `dP_{j ≠ 0} = c - δ`. -/
def offsetGrad {n : Nat} (hn : 0 < n) (c δ : Rat) : Fin n → Rat :=
  fun j => if j = ⟨0, hn⟩ then c else c - δ

/-- Matrix-vector product entry `(dS K)_c = ∑_{j : Fin n} dS_j K_{j, c}`. -/
def dqEntry {n d : Nat} (dS : Fin n → Rat) (K : Fin n → Fin d → Rat) (c : Fin d) : Rat :=
  finSum (fun j => dS j * K j c)

/-- Key-centered matrix `(K - 1 K_bar^T)_{j, c} = K_{j, c} - K_bar_c`. -/
def centeredKey {n d : Nat} (K : Fin n → Fin d → Rat) (kBar : Fin d → Rat) :
    Fin n → Fin d → Rat :=
  fun j c => K j c - kBar c

/-- Bit-exact specification of a binary floating-point format. -/
structure FloatFormatSpec where
  ebits : Nat
  mbits : Nat
  isUnsigned : Bool
  minSubnormal : Rat
  minNormal : Rat
  maxFinite : Rat
  unitRoundoff : Rat

/-- Total bit width of a binary floating-point format: `(sign bit if signed) + ebits + mbits`. -/
def FloatFormatSpec.totalBits (fmt : FloatFormatSpec) : Nat :=
  (if fmt.isUnsigned then 0 else 1) + fmt.ebits + fmt.mbits

/-- Full dynamic range `maxFinite / minSubnormal`. -/
def FloatFormatSpec.dynRangeFull (fmt : FloatFormatSpec) : Rat :=
  fmt.maxFinite / fmt.minSubnormal

/-- Normal dynamic range `maxFinite / minNormal`. -/
def FloatFormatSpec.dynRangeNormal (fmt : FloatFormatSpec) : Rat :=
  fmt.maxFinite / fmt.minNormal

/-- Unsigned 4-bit `U-E3M1` format for nonnegative probabilities `P ∈ [0, 1]`:
    `ebits = 3, mbits = 1, bias = 7`, covering `[2^{-7}, 3/2]`. -/
def fmtUE3M1 : FloatFormatSpec :=
  { ebits := 3
    mbits := 1
    isUnsigned := true
    minSubnormal := 1 / 128
    minNormal := 1 / 64
    maxFinite := 3 / 2
    unitRoundoff := 1 / 4 }

/-- Signed 4-bit OCP `MXFP4-E2M1` element format:
    `ebits = 2, mbits = 1, bias = 1`, covering `[1/2, 6]`. -/
def fmtMXFP4 : FloatFormatSpec :=
  { ebits := 2
    mbits := 1
    isUnsigned := false
    minSubnormal := 1 / 2
    minNormal := 1
    maxFinite := 6
    unitRoundoff := 1 / 4 }

/-- Block-scaled 4-bit OCP `MXFP4-E2M1` on `P ∈ [0, 1]` (E8M0 shared scale `2^{-2}`):
    covering `[1/8, 3/2]`. -/
def fmtMXFP4Prob : FloatFormatSpec :=
  { ebits := 2
    mbits := 1
    isUnsigned := false
    minSubnormal := 1 / 8
    minNormal := 1 / 4
    maxFinite := 3 / 2
    unitRoundoff := 1 / 4 }

/-- Signed 8-bit OCP `FP8-E4M3FN` format (`ebits = 4, mbits = 3`, `[2^{-9}, 448]`). -/
def fmtE4M3 : FloatFormatSpec :=
  { ebits := 4
    mbits := 3
    isUnsigned := false
    minSubnormal := 1 / 512
    minNormal := 1 / 64
    maxFinite := 448
    unitRoundoff := 1 / 16 }

/-- Signed 8-bit OCP `FP8-E5M2` format (`ebits = 5, mbits = 2`, `[2^{-16}, 57344]`). -/
def fmtE5M2 : FloatFormatSpec :=
  { ebits := 5
    mbits := 2
    isUnsigned := false
    minSubnormal := 1 / 65536
    minNormal := 1 / 16384
    maxFinite := 57344
    unitRoundoff := 1 / 8 }

end FlashAttnBwdSignflip
