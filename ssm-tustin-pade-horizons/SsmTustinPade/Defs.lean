/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions (`ssm-tustin-pade-horizons`)

Pure-`Init` (zero Mathlib) definitions for low-precision IEEE-754 RNE SSM discretization
horizons across `FP8-E5M2` (`p = 3`), `FP8-E4M3` (`p = 4`), `BF16` (`p = 8`), and
`FP16` (`p = 11`), where `p = f + 1` is the total significand precision (`f` explicit
fraction bits plus 1 implicit leading bit).
-/

namespace SsmTustinPade

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

/-- Exact power of two as a rational: `2 ^ n`. -/
def pow2Rat (n : Nat) : Rat := ((2 ^ n : Nat) : Rat)

/-- Exact negative power of two as a rational: `2 ^ (-n) = 1 / 2 ^ n`. -/
def invPow2Rat (n : Nat) : Rat := (1 : Rat) / pow2Rat n

/-- Exact integer binade ULP in `[2^k, 2^(k+1))` for `p`-significand-bit binary floats
    (`p = f + 1`, `k ≥ p`): `ulp(p, k) = 2^(k + 1 - p)`. -/
def binadeUlp (p k : Nat) : Nat := 2 ^ (k + 1 - p)

/-- Exact IEEE-754 Round-to-Nearest-Even (RNE) rounding of a natural number `m` in binade
    `[2^k, 2^(k+1))` for `p`-significand-bit binary floats (`p = f + 1`). -/
def binadeRneNat (p k m : Nat) : Nat :=
  if k < p then m
  else
    let u := 2 ^ (k + 1 - p)
    let half := 2 ^ (k - p)
    let q := m / u
    let r := m % u
    if r < half then q * u
    else if r > half then (q + 1) * u
    else if q % 2 = 0 then q * u
    else (q + 1) * u

/-- Exact first positive Tustin Nyquist snap-to-`-1.0` horizon in two-step IEEE-754 RNE
    `fl(fl(2 - z) / fl(2 + z))`: `z_osc(p) = 2^(p + 1) + 8`
    (`24` E5M2, `40` E4M3, `520` BF16, `4104` FP16). -/
def tustinOscHorizon (p : Nat) : Nat := 2 ^ (p + 1) + 8

/-- Exact unconditional two-step Tustin snap-to-`-1.0` threshold: `2^(p + 2)`
    (`32` E5M2, `64` E4M3, `1024` BF16, `8192` FP16). -/
def tustinUncondOscThreshold (p : Nat) : Nat := 2 ^ (p + 2)

/-- Exact single-rounding Tustin snap-to-`-1.0` threshold: `2^(p + 3) - 2`. -/
def tustinSingleRoundOscThreshold (p : Nat) : Nat := 2 ^ (p + 3) - 2

/-- Exact Tustin / bilinear state pole `A_tustin(z) = (1 - z/2) / (1 + z/2) = (2 - z) / (2 + z)`. -/
def tustinA (z : Rat) : Rat := (1 - z / 2) / (1 + z / 2)

/-- IEEE-754 RNE snap-to-`-1.0` region from above: `-1 ≤ y ≤ -1 + 2^(-(p+1))`.
    Since `-1.0` has even significand `2^(p-1)` and `-1 + 2^(-p)` has odd significand
    `2^p - 1`, ties at `-1 + 2^(-(p+1))` round to `-1.0`. -/
def rneSnapsToNegOne (p : Nat) (y : Rat) : Prop :=
  (-1 : Rat) ≤ y ∧ y ≤ -1 + invPow2Rat (p + 1)

/-- IEEE-754 RNE snap-to-`+1.0` region from below: `1 - 2^(-(p+1)) ≤ y ≤ 1`. -/
def rneSnapsToPosOneBelow (p : Nat) (y : Rat) : Prop :=
  1 - invPow2Rat (p + 1) ≤ y ∧ y ≤ 1

/-- IEEE-754 RNE snap-to-`+1.0` region from above: `1 ≤ y ≤ 1 + 2^(-p)`. -/
def rneSnapsToPosOneAbove (p : Nat) (y : Rat) : Prop :=
  1 ≤ y ∧ y ≤ 1 + invPow2Rat p

/-- IEEE-754 RNE snap-to-`2.0` region from below: `2 - 2^(-p) ≤ y ≤ 2`. -/
def rneSnapsToTwoBelow (p : Nat) (y : Rat) : Prop :=
  2 - invPow2Rat p ≤ y ∧ y ≤ 2

/-- IEEE-754 RNE snap-to-`2.0` region from above: `2 ≤ y ≤ 2 + 2^(-(p-1))`. -/
def rneSnapsToTwoAbove (p : Nat) (y : Rat) : Prop :=
  2 ≤ y ∧ y ≤ 2 + invPow2Rat (p - 1)

/-- Exact Tustin / Padé-(0,2) infinite-memory stall horizon: `2^(-p)`. -/
def tustinStallHorizon (p : Nat) : Rat := invPow2Rat p

/-- Exact ZOH (`exp(-z)`) infinite-memory stall and naive `B_bar` blackout horizon: `2^(-(p+1))`. -/
def zohStallHorizon (p : Nat) : Rat := invPow2Rat (p + 1)

/-- IEEE-754 RNE rounding of a value `y ∈ (0, 1]` near `+1.0` (snaps to `1` on `[1 - 2^(-(p+1)), 1]`). -/
def flNearOneBelow (p : Nat) (y : Rat) : Rat :=
  if 1 - invPow2Rat (p + 1) ≤ y ∧ y ≤ 1 then 1 else y

/-- Naive ZOH input discretizer `B_naive(z) = (1 - fl(exp(-z))) / z` given `ez ≈ exp(-z)`. -/
def naiveZohBBar (p : Nat) (ez z : Rat) : Rat :=
  (1 - flNearOneBelow p ez) / z

/-- Count of positive finite IEEE-754 representables in `(0, 1]` for exponent bias `B`
    and `f = p - 1` explicit fraction bits: subnormals + normals `< 1` + exact `1.0`. -/
def countUnitInterval (B f : Nat) : Nat :=
  (2 ^ f - 1) + (B - 1) * 2 ^ f + 1

/-- Count of positive finite IEEE-754 representables in `(0, 2^(-(f+2))] = (0, 2^(-(p+1))]`
    where naive ZOH `B_bar` suffers 100% catastrophic cancellation blackout. -/
def countBlackoutInterval (B f : Nat) : Nat :=
  (2 ^ f - 1) + (B - f - 3) * 2 ^ f + 1

/-- Subtraction-free Padé-(0,2) state pole: `A_pade02(z) = 1 / (1 + z + z^2 / 2)`. -/
def pade02A (z : Rat) : Rat := 1 / (1 + z + z * z / 2)

/-- Degree-2 Taylor polynomial of `exp(-z)`: `1 - z + z^2 / 2`. -/
def expTaylor2 (z : Rat) : Rat := 1 - z + z * z / 2

/-- Degree-3 Taylor polynomial of `exp(-z)`: `1 - z + z^2 / 2 - z^3 / 6`. -/
def expTaylor3 (z : Rat) : Rat := 1 - z + z * z / 2 - z * z * z / 6

/-- Maximum finite representable in `FP8-E4M3FN` (no `Inf`): `448`. -/
def fp8E4M3MaxFinite : Rat := 448

/-- Subtraction-free 4th-order Padé-(0,2) input gain: `B_pade02(z) = 1 / (1 + z/2 + z^2/12)`. -/
def pade02B (z : Rat) : Rat := 1 / (1 + z / 2 + z * z / 12)

/-- Tustin / Padé-(0,1) input gain: `B_tustin(z) = 1 / (1 + z/2)`. -/
def tustinB (z : Rat) : Rat := 1 / (1 + z / 2)

/-- Degree-3 Taylor polynomial of `phi_1(-z) = (1 - exp(-z)) / z`: `1 - z/2 + z^2/6 - z^3/24`. -/
def phi1Taylor3 (z : Rat) : Rat := 1 - z / 2 + z * z / 6 - z * z * z / 24

/-- Degree-4 Taylor polynomial of `phi_1(-z)`: `1 - z/2 + z^2/6 - z^3/24 + z^4/120`. -/
def phi1Taylor4 (z : Rat) : Rat := 1 - z / 2 + z * z / 6 - z * z * z / 24 + z * z * z * z / 120

/-- Alternating Nyquist sign sequence `altSign t = (-1)^t`. -/
def altSign : Nat → Rat
  | 0 => 1
  | t + 1 => -altSign t

/-- Exact scalar linear SSM state recurrence `h_{t+1} = a * h_t + b * u_t`, `h_0 = 0`. -/
def ssmState (a b : Rat) (u : Nat → Rat) : Nat → Rat
  | 0 => 0
  | t + 1 => a * ssmState a b u t + b * u t

end SsmTustinPade
