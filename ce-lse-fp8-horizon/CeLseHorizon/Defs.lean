/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions for `ce-lse-fp8-horizon`

Zero Mathlib, zero `native_decide`, zero floating-point approximations.
All definitions operate purely over `Nat`, `Int`, and `Rat` in Lean 4's `Init` prelude.
-/

namespace CeLseHorizon

/-- Exact rational power of two `2^k` for `k : Nat`. -/
def pow2Rat (k : Nat) : Rat :=
  ((2 ^ k : Nat) : Rat)

/-- Exact rational inverse power of two `2^{-k} = 1 / 2^k` for `k : Nat`. -/
def invPow2Rat (k : Nat) : Rat :=
  (1 : Rat) / pow2Rat k

/-- Exact rational power of two `2^k` for any signed integer exponent `k : Int`. -/
def pow2IntRat (k : Int) : Rat :=
  match k with
  | Int.ofNat n => pow2Rat n
  | Int.negSucc n => invPow2Rat (n + 1)

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

/-- Exact finite sum over `Fin k → Rat`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
      f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{v : Fin n} f v`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-- Exact finite sum over all indices `v ≠ y`. -/
def finSumExcept {n : Nat} (y : Fin n) (f : Fin n → Rat) : Rat :=
  finSum (fun v => if v = y then 0 else f v)

/-! ### Cross-Entropy Gradient Definitions -/

/-- Exact Cross-Entropy logit gradient `g_v = p_v - δ_{v, y}`. -/
def ceGrad {V : Nat} (p : Fin V → Rat) (y : Fin V) (v : Fin V) : Rat :=
  p v - (if v = y then (1 : Rat) else 0)

/-- Uniform probability distribution `p_v = 1 / V` over `Fin V`. -/
def uniformProb (V : Nat) : Fin V → Rat :=
  fun _ => (1 : Rat) / (V : Rat)

/-! ### Exact FP8-E4M3 & FP8-E5M2 Subnormal and Near-`-1` Rounding Models -/

/-- OCP FP8-E4M3 minimum positive subnormal `2^{-9} = 1 / 512`. -/
def e4m3MinSub : Rat := invPow2Rat 9

/-- OCP FP8-E4M3 RNE tie-to-zero midpoint `2^{-10} = 1 / 1024`. -/
def e4m3RneMid : Rat := invPow2Rat 10

/-- OCP FP8-E4M3 largest representable value strictly above `-1` (RTZ target image):
    `-(1 - 2^{-4}) = -15 / 16`. -/
def e4m3PredNegOne : Rat := -(15 / 16 : Rat)

/-- IEEE FP8-E5M2 minimum positive subnormal `2^{-16} = 1 / 65536`. -/
def e5m2MinSub : Rat := invPow2Rat 16

/-- IEEE FP8-E5M2 RNE tie-to-zero midpoint `2^{-17} = 1 / 131072`. -/
def e5m2RneMid : Rat := invPow2Rat 17

/-- IEEE FP8-E5M2 largest representable value strictly above `-1` (RTZ target image):
    `-(1 - 2^{-3}) = -7 / 8`. -/
def e5m2PredNegOne : Rat := -(7 / 8 : Rat)

/-- Exact Round-Toward-Zero (RTZ) quantization in the lowest subnormal interval `[0, minSub]`:
    any `0 ≤ x < minSub` flushes to `0`, while `x = minSub` is preserved. -/
def subnormalQuantRTZ (minSub x : Rat) : Rat :=
  if x < minSub then 0 else minSub

/-- Exact Round-to-Nearest-Even (RNE) quantization in the lowest subnormal interval `[0, minSub]`:
    `0` has even significand `0`, `minSub` has odd significand `1`, and their midpoint is
    `minSub / 2`. Hence `x ≤ minSub / 2` ties-to-even to `0`, while `minSub / 2 < x` rounds UP
    to `minSub`. -/
def subnormalQuantRNE (minSub x : Rat) : Rat :=
  if x ≤ minSub / 2 then 0 else minSub

/-- Predicate that a negative gradient `g ∈ (-1, 0)` truncates toward zero (RTZ) to the
    predecessor of `-1` in an `m`-bit mantissa format (`-(1 - 2^{-(m+1)})`). -/
def negGradRoundsToPredRTZ (m : Nat) (g : Rat) : Prop :=
  (-1 : Rat) < g ∧ g < -(1 - invPow2Rat (m + 1))

/-- Predicate that a negative gradient `g ∈ (-1, 0)` rounds to `-1` under RNE in an `m`-bit
    mantissa format (strictly past the midpoint `-(1 - 2^{-(m+2)})`). -/
def negGradRoundsToNegOneRNE (m : Nat) (g : Rat) : Prop :=
  (-1 : Rat) < g ∧ g < -(1 - invPow2Rat (m + 2))

/-- Uniform quantized CE gradient vector under RTZ in the subnormal-flush / target-truncation regime. -/
def uniformQuantGradRTZ (minSub predNegOne : Rat) (V : Nat) (y : Fin V) (v : Fin V) : Rat :=
  if v = y then predNegOne else subnormalQuantRTZ minSub ((1 : Rat) / (V : Rat))

/-- Uniform quantized CE gradient vector under RNE in the subnormal / target-`-1` regime. -/
def uniformQuantGradRNE (minSub : Rat) (V : Nat) (y : Fin V) (v : Fin V) : Rat :=
  if v = y then (-1 : Rat) else subnormalQuantRNE minSub ((1 : Rat) / (V : Rat))

/-! ### FP16 Dynamic Loss-Scaling Constants & Safe Window Predicates -/

/-- IEEE-754 FP16 overflow threshold `65520 = 65504 + 16` (RNE rounds `≥ 65520` to `∞`). -/
def fp16OverflowThresh : Rat := 65520

/-- IEEE-754 FP16 minimum positive normal number `2^{-14}`. -/
def fp16MinNorm : Rat := invPow2Rat 14

/-- IEEE-754 FP16 RNE subnormal flush midpoint `2^{-25}` (half of `min_sub = 2^{-24}`). -/
def fp16MinSubRneThresh : Rat := invPow2Rat 25

/-- A loss scale `S` is FP16 normal-precision safe for `(gMax, pMin)` iff it simultaneously
    avoids overflow (`S * gMax < 65520`) and keeps `pMin` in normal precision (`S * pMin ≥ 2^{-14}`). -/
def fp16NormalSafe (S gMax pMin : Rat) : Prop :=
  S * gMax < fp16OverflowThresh ∧ fp16MinNorm ≤ S * pMin

/-- A loss scale `S` is FP16 subnormal-rescue safe for `(gMax, pMin)` iff it simultaneously
    avoids overflow (`S * gMax < 65520`) and avoids RNE subnormal flush (`S * pMin > 2^{-25}`). -/
def fp16SubnormalSafe (S gMax pMin : Rat) : Prop :=
  S * gMax < fp16OverflowThresh ∧ fp16MinSubRneThresh < S * pMin

/-! ### LogSumExp Swamping & Pairwise Binary Tree Split-Accumulation Models -/

/-- Exact IEEE-754 RNE swamping condition for adding a nonnegative term `t` to a binade-even
    accumulator `acc > 0` in binary floating-point with `p` significand bits (`BF16: p = 8`,
    `FP16: p = 11`, `FP8-E5M2: p = 3`): when `acc` is a power of two, `ulp(acc) = acc * 2^{-(p-1)}`
    and `acc` has even significand, so every `0 ≤ t ≤ acc * 2^{-p}` rounds `fl_p(acc + t) = acc`.
    For an accumulator that is not a power of two this predicate is only a model, not exact RNE
    (its ulp is larger than `acc * 2^{-(p-1)}`, so the real swamping threshold is higher). -/
def rneAddSwamps (p : Nat) (acc t : Rat) : Prop :=
  (0 : Rat) < acc ∧ (0 : Rat) ≤ t ∧ t ≤ acc * invPow2Rat p

/-- Naive `1 + sum` accumulation of `n` equal nonnegative off-peak terms `t` in `p`-bit
    significand RNE arithmetic: starting from `1`, each step swamps `t` whenever `t ≤ a * 2^{-p}`. -/
def naiveAccum (p : Nat) (t : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 =>
    let a := naiveAccum p t n
    if t ≤ a * invPow2Rat p then a else a + t

/-- Sequential split-accumulation (`T_seq`) starting from `0` adding `n` equal positive terms `t`
    in the `rneAddSwamps` model of `p`-bit significand RNE arithmetic: stalls permanently once
    `t ≤ a * 2^{-p}` (`a = 2^p * t`). This agrees with exact round-to-nearest-even only when `t` is
    a power of two (for `p = 3`, `t = 3` real RNE stalls at `32`, the model at `24`). -/
def seqSplitAccum (p : Nat) (t : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 =>
    let a := seqSplitAccum p t n
    if (0 : Rat) < a ∧ t ≤ a * invPow2Rat p then a else a + t

/-- Pairwise Binary Tree Split-Accumulation on `2^k` equal terms `t`:
    every merge adds two identical operands (`x + x = 2x`), which increments only the binary
    exponent by `+1` with ZERO significand rounding error. -/
def treeSum : Nat → Rat → Rat
  | 0, t => t
  | k + 1, t => treeSum k t + treeSum k t

/-! ### Label Smoothing -/

/-- Off-target label-smoothing probability mass `ε / V`. -/
def labelSmoothOffTarget (ε : Rat) (V : Nat) : Rat :=
  ε / (V : Rat)

end CeLseHorizon
