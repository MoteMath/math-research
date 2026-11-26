/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions for `ssm-decay-collapse-bounds`

Self-contained definitions over `Rat`, `Int`, and `Nat` (zero Mathlib) for:
1. Exact integer powers of two `zpow2`, rational absolute value `ratAbs`, exact
   Round-to-Nearest-Even integer rounding `rneInt`, exact binade index `binadeOf`,
   and IEEE-754 binary floating-point RNE rounding `ieeeRne p`.
2. Normal IEEE-754 binary floating-point grid values `floatVal p k m`, largest decay
   below one `aMax p`, RNE stall midpoint `aStall p`, sequential power iteration
   `seqPow p`, and sequential vs exact additive accumulation `seqAccum` / `exactAccum`.
3. Zero-multiplier signed integer shift-subtract recurrence `shiftSubStep` (using
   floor division `Int.fdiv`, identical to signed arithmetic right shift `>>> r`),
   zero-input iteration `shiftSubIter`, and tight invariant endpoints `shiftSubMin`
   and `shiftSubMax`.
4. 1-tap dyadic decay `oneTapDecay` and 2-tap Canonical Signed Digit (CSD) decay
   `twoTapCsdDecay`.
-/

namespace SsmDecayCollapse

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Exact integer power of two `2^k` in `Rat`. -/
def zpow2 (k : Int) : Rat :=
  if 0 ≤ k then
    ((2 ^ k.toNat : Nat) : Rat)
  else
    (1 : Rat) / ((2 ^ (-k).toNat : Nat) : Rat)

/-- Exact Round-to-Nearest-Even (RNE) rounding of a rational `q` to `Int`.
    Uses Euclidean floor division `q.num.ediv q.den` (with positive denominator `q.den > 0`),
    so `q = fl + rem / q.den` with `0 ≤ rem < q.den`. -/
def rneInt (q : Rat) : Int :=
  let d : Int := (q.den : Int)
  let fl : Int := q.num.ediv d
  let rem : Int := q.num.emod d
  if 2 * rem < d then
    fl
  else if d < 2 * rem then
    fl + 1
  else
    if fl % 2 == 0 then fl else fl + 1

/-- Exact binade exponent `k : Int` such that `2^k ≤ x < 2^(k + 1)` for every `x > 0`. -/
def binadeOf (x : Rat) : Int :=
  let k0 : Int := (Nat.log2 x.num.toNat : Int) - (Nat.log2 x.den : Int)
  if x < zpow2 k0 then k0 - 1 else k0

/-- Exact IEEE-754 binary floating-point Round-to-Nearest-Even (RNE) rounding
    with `p` explicit mantissa bits on positive rationals (unbounded normal exponent range). -/
def ieeeRne (p : Nat) (x : Rat) : Rat :=
  if 0 < x then
    let k := binadeOf x
    (rneInt (x * zpow2 ((p : Int) - k)) : Rat) * zpow2 (k - (p : Int))
  else
    0

/-- Exact value of a normal IEEE-754 binary floating-point number with `p` explicit
    mantissa bits in binade `k` (`[2^k, 2^(k+1))`) and explicit mantissa `m < 2^p`:
    `(2^p + m) * 2^(k - p)`. -/
def floatVal (p : Nat) (k : Int) (m : Nat) : Rat :=
  (((2 ^ p + m : Nat) : Rat)) * zpow2 (k - (p : Int))

/-- Predicate asserting that `x` is a positive normal IEEE-754 binary floating-point
    number with `p` explicit mantissa bits. -/
def IsIeeeNormal (p : Nat) (x : Rat) : Prop :=
  ∃ (k : Int) (m : Nat), m < 2 ^ p ∧ x = floatVal p k m

/-- Largest IEEE-754 representable decay strictly below `1` for `p` explicit mantissa bits:
    `a_max(p) = 1 - 2^(-(p + 1))`. -/
def aMax (p : Nat) : Rat :=
  1 - zpow2 (-((p + 1 : Nat) : Int))

/-- Exact RNE decay-stall midpoint for `p` explicit mantissa bits:
    `a_stall(p) = 1 - 2^(-(p + 2))`. -/
def aStall (p : Nat) : Rat :=
  1 - zpow2 (-((p + 2 : Nat) : Int))

/-- Sequential IEEE-754 RNE power iteration of `aMax p` starting from `1.0`. -/
def seqPow (p : Nat) : Nat → Rat
  | 0 => 1
  | n + 1 => ieeeRne p (seqPow p n * aMax p)

/-- Sequential IEEE-754 RNE additive accumulation starting from `h_0 = 1` with `a_t = 1`
    and constant input `b`. -/
def seqAccum (p : Nat) (b : Rat) : Nat → Rat
  | 0 => 1
  | t + 1 => ieeeRne p (seqAccum p b t + b)

/-- Exact (or binary-tree / Blelloch) additive accumulation starting from `h_0 = 1`
    with `a_t = 1` and constant input `b`. -/
def exactAccum (b : Rat) (t : Nat) : Rat :=
  1 + (t : Rat) * b

/-- Zero-multiplier 1-tap signed integer shift-subtract recurrence:
    `h' = h - floor(h / 2^r) + b`, where floor division `Int.fdiv` coincides with
    signed arithmetic right shift `>>> r` for positive divisor `2^r`. -/
def shiftSubStep (r : Nat) (h b : Int) : Int :=
  h - Int.fdiv h ((2 ^ r : Nat) : Int) + b

/-- Zero-input (`b_t = 0`) iteration of `shiftSubStep r`. -/
def shiftSubIter (r : Nat) (h : Int) : Nat → Int
  | 0 => h
  | n + 1 => shiftSubStep r (shiftSubIter r h n) 0

/-- Tight negative lower invariant bound `-2^R * B_max` for signed shift-subtract. -/
def shiftSubMin (R : Nat) (Bmax : Int) : Int :=
  -((2 ^ R : Nat) : Int) * Bmax

/-- Tight positive upper invariant bound `2^R * B_max + (2^R - 1)` for signed shift-subtract. -/
def shiftSubMax (R : Nat) (Bmax : Int) : Int :=
  ((2 ^ R : Nat) : Int) * Bmax + (((2 ^ R : Nat) : Int) - 1)

/-- 1-tap zero-multiplier dyadic decay `a_1(r) = 1 - 2^(-r)`. -/
def oneTapDecay (r : Nat) : Rat :=
  1 - zpow2 (-(r : Int))

/-- 2-tap zero-multiplier CSD dyadic decay `a_2(r, c) = 1 - 2^(-r) - c * 2^(-(r + 1))`
    where `c = false` denotes `0` and `c = true` denotes `1`. -/
def twoTapCsdDecay (r : Nat) (c : Bool) : Rat :=
  if c then
    1 - zpow2 (-(r : Int)) - zpow2 (-((r + 1 : Nat) : Int))
  else
    1 - zpow2 (-(r : Int))

end SsmDecayCollapse
