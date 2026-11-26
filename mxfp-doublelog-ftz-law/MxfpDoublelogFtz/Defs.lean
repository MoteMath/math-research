/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`mxfp-doublelog-ftz-law`)

Pure-`Init` (zero Mathlib) exact integer and rational definitions for:
1. Full-finite gradual-underflow (`GU`) and flush-to-zero (`FTZ`) microscaling grids `E_a M_b`
   (both signed `w`-bit and unsigned `w`-bit, plus `OCP E4M3`),
2. Exact rational EF21 worst-case relative MSE envelopes under Continuous max-abs scaling
   and OCP E8M0 power-of-2 scaling,
3. Exact closed-form double-log crossover functions `B*_cont(a, b)` and `B*_e8m0(a, b)`,
4. Exact `FTZ` vs `GU` underflow error amplification ratios.
-/

namespace MxfpDoublelogFtz

/-! ## 1. Bit-Level Quantization Grids (`E_a M_b`) -/

/-- Exact integer grid value (in units of the smallest positive gradual-underflow subnormal `u_min = 1`)
for nonnegative code `code < 2 ^ (a + b)` in full-finite gradual-underflow format `E_a M_b`. -/
def mxfpCodeValue (a b code : Nat) : Nat :=
  if a = 0 then
    code
  else
    let e := code / (2 ^ b)
    let m := code % (2 ^ b)
    if e = 0 then
      m
    else
      (2 ^ b + m) * 2 ^ (e - 1)

/-- Maximum representable integer value (in units of `u_min = 1`) for full-finite `E_a M_b`. -/
def mxfpMaxInt (a b : Nat) : Nat :=
  if a = 0 then
    2 ^ b - 1
  else
    (2 ^ (b + 1) - 1) * 2 ^ (2 ^ a - 2)

/-- Smallest positive representable integer value for `E_a M_b` under gradual underflow (`ftz = false`)
or flush-to-zero (`ftz = true`, `a ≥ 1`). -/
def mxfpMinPosInt (a b : Nat) (ftz : Bool) : Nat :=
  if a = 0 || !ftz then 1 else 2 ^ b

/-- Nonnegative integer quantization grid for signed `w`-bit full-finite `E_a M_{w - 1 - a}`. -/
def mxfpSignedGrid (w a : Nat) : List Nat :=
  (List.range (2 ^ (w - 1))).map (mxfpCodeValue a (w - 1 - a))

/-- Nonnegative integer quantization grid for unsigned `w`-bit full-finite `U-E_a M_{w - a}`. -/
def mxfpUnsignedGrid (w a : Nat) : List Nat :=
  (List.range (2 ^ w)).map (mxfpCodeValue a (w - a))

/-- Normalized rational quantization grid (scaled by `1 / M`) for signed `w`-bit `E_a M_{w - 1 - a}`. -/
def mxfpSignedNormGrid (w a : Nat) : List Rat :=
  let M : Rat := (mxfpMaxInt a (w - 1 - a) : Rat)
  (mxfpSignedGrid w a).map (fun g : Nat => (g : Rat) / M)

/-- Normalized rational quantization grid (scaled by `1 / M`) for unsigned `w`-bit `U-E_a M_{w - a}`. -/
def mxfpUnsignedNormGrid (w a : Nat) : List Rat :=
  let M : Rat := (mxfpMaxInt a (w - a) : Rat)
  (mxfpUnsignedGrid w a).map (fun g : Nat => (g : Rat) / M)

/-! ## 2. Exact Rational EF21 Worst-Case Relative MSE Envelopes -/

/-- Exact normal-precision plateau `1 / (2^(b+1) + 1)^2` of format `E_a M_b` (`a ≥ 2, b ≥ 1`). -/
def mxfpNormPlateau (b : Nat) : Rat :=
  let q : Rat := ((2 ^ (b + 1) + 1 : Nat) : Rat)
  1 / (q * q)

/-- Continuous max-abs normal-precision branch for full-finite `E_a M_b` (`a ≥ 2, b ≥ 1`, `B ≥ 1`):
`k / (4 * (2^(b+1) - 1)^2 + k * (2^(b+1) + 1)^2)` where `k = B - 1`. -/
def deltaContNorm (b B : Nat) : Rat :=
  let k : Rat := ((B - 1 : Nat) : Rat)
  let top : Rat := ((2 ^ (b + 1) - 1 : Nat) : Rat)
  let q : Rat := ((2 ^ (b + 1) + 1 : Nat) : Rat)
  k / (4 * top * top + k * q * q)

/-- Continuous max-abs subnormal-underflow ramp with max value `M` and smallest positive value `u`:
`u^2 * k / (4 * M^2 + u^2 * k)` where `k = B - 1`. -/
def deltaContUf (M u B : Nat) : Rat :=
  let k : Rat := ((B - 1 : Nat) : Rat)
  let u2 : Rat := ((u * u : Nat) : Rat)
  let m2 : Rat := ((M * M : Nat) : Rat)
  (u2 * k) / (4 * m2 + u2 * k)

/-- Exact Continuous max-abs EF21 worst-case relative MSE for full-finite `E_a M_b` (`a ≥ 2, b ≥ 1`):
maximum of the normal-precision branch and the underflow ramp (`ftz = false` uses `u = 1`,
`ftz = true` uses `u = 2^b`). -/
def deltaCont (a b : Nat) (ftz : Bool) (B : Nat) : Rat :=
  max (deltaContNorm b B) (deltaContUf (mxfpMaxInt a b) (mxfpMinPosInt a b ftz) B)

/-- Continuous max-abs EF21 worst-case relative MSE for `INT_w` (`E0 M_b`, `M = 2^b - 1`). -/
def deltaContInt (b B : Nat) : Rat :=
  deltaContUf (2 ^ b - 1) 1 B

/-- OCP E8M0 power-of-2 scaling: top-binade lowest normal midpoint anchor + underflow midpoints. -/
def deltaE8m0Branch1 (a b u B : Nat) : Rat :=
  let s : Rat := ((2 ^ (2 ^ a - 2) : Nat) : Rat)
  let q : Rat := ((2 ^ (b + 1) + 1 : Nat) : Rat)
  let u2 : Rat := ((u * u : Nat) : Rat)
  let k : Rat := ((B - 1 : Nat) : Rat)
  (s * s + u2 * k) / (q * q * s * s + u2 * k)

/-- OCP E8M0 power-of-2 scaling: second-highest binade top midpoint anchor + underflow midpoints. -/
def deltaE8m0Branch2 (a b u B : Nat) : Rat :=
  let s2 : Rat := ((2 ^ (2 ^ a - 3) : Nat) : Rat)
  let p : Rat := ((2 ^ (b + 2) - 1 : Nat) : Rat)
  let u2 : Rat := ((u * u : Nat) : Rat)
  let k : Rat := ((B - 1 : Nat) : Rat)
  (s2 * s2 + u2 * k) / (p * p * s2 * s2 + u2 * k)

/-- OCP E8M0 power-of-2 scaling: exact `M / 2` grid-point anchor + underflow midpoints. -/
def deltaE8m0Uf (M u B : Nat) : Rat :=
  let u2 : Rat := ((u * u : Nat) : Rat)
  let m2 : Rat := ((M * M : Nat) : Rat)
  let k : Rat := ((B - 1 : Nat) : Rat)
  (u2 * k) / (m2 + u2 * k)

/-- Exact OCP E8M0 worst-case EF21 relative MSE for full-finite `E_a M_b` (`a ≥ 2, b ≥ 1`). -/
def deltaE8m0 (a b : Nat) (ftz : Bool) (B : Nat) : Rat :=
  let u := mxfpMinPosInt a b ftz
  max (deltaE8m0Branch1 a b u B)
    (max (deltaE8m0Branch2 a b u B) (deltaE8m0Uf (mxfpMaxInt a b) u B))

/-- OCP E8M0 worst-case EF21 relative MSE for `INT_w` (`E0 M_b`, `M = 2^b - 1`). -/
def deltaE8m0Int (b B : Nat) : Rat :=
  let m : Rat := ((2 ^ b - 1 : Nat) : Rat)
  let k : Rat := ((B - 1 : Nat) : Rat)
  (1 + k) / (m * m + k)

/-! ## 3. Exact `OCP E4M3` (`W8_E4M3_OCP`) Continuous & E8M0 Envelopes -/

/-- Maximum representable integer value of `W8_E4M3_OCP` (`14 * 2^14 = 229376`, since top code is NaN). -/
def ocpE4m3MaxInt : Nat := 14 * 2 ^ 14

/-- Continuous max-abs normal-precision branch for `W8_E4M3_OCP` (`top = 14`, `q = 17`). -/
def deltaContNormOcpE4m3 (B : Nat) : Rat :=
  let k : Rat := ((B - 1 : Nat) : Rat)
  k / (4 * 14 * 14 + k * 17 * 17)

/-- Exact Continuous max-abs EF21 worst-case relative MSE for `W8_E4M3_OCP` (`GU` or `FTZ`). -/
def deltaContOcpE4m3 (ftz : Bool) (B : Nat) : Rat :=
  let u := if ftz then 8 else 1
  max (deltaContNormOcpE4m3 B) (deltaContUf ocpE4m3MaxInt u B)

/-! ## 4. Universal Double-Log Crossover & E8M0 Shift Prefactors -/

/-- Universal Continuous-scaling crossover prefactor `(2^(b+1) - 1)^2 / (4 * ((2^b + 1)^2 - 1))`. -/
def contCrossoverPref (b : Nat) : Rat :=
  let num : Rat := ((2 ^ (b + 1) - 1 : Nat) : Rat)
  let d1 : Rat := ((2 ^ b + 1 : Nat) : Rat)
  (num * num) / (4 * (d1 * d1 - 1))

/-- Exact rational Continuous-scaling crossover `B*_cont(a, b)` where `E_a M_b`'s underflow ramp
equals `E_{a+1} M_{b-1}`'s normal-precision plateau `1 / (2^b + 1)^2`. -/
def contCrossover (a b : Nat) : Rat :=
  contCrossoverPref b * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)

/-- E8M0 underflow-regime crossover prefactor `(2^(b+1) - 1)^2 / (16 * ((2^b + 1)^2 - 1))`
(exactly `1/4` of `contCrossoverPref b`). -/
def e8m0UfCrossoverPref (b : Nat) : Rat :=
  contCrossoverPref b / 4

/-- E8M0 top-binade-anchor crossover prefactor `(3 * 2^b + 2) / (16 * (2^b + 2))`. -/
def e8m0NormCrossoverPref (b : Nat) : Rat :=
  let t : Rat := ((2 ^ b : Nat) : Rat)
  (3 * t + 2) / (16 * (t + 2))

/-- Exact E8M0 envelope crossover prefactor `min(e8m0UfCrossoverPref b, e8m0NormCrossoverPref b)`. -/
def e8m0CrossoverPref (b : Nat) : Rat :=
  min (e8m0UfCrossoverPref b) (e8m0NormCrossoverPref b)

/-- Exact E8M0 envelope crossover `B*_e8m0(a, b)`. -/
def e8m0Crossover (a b : Nat) : Rat :=
  e8m0CrossoverPref b * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)

/-! ## 5. Exact FTZ Underflow Penalty Ratio -/

/-- Exact ratio `deltaContUf(M, 2^b, B) / deltaContUf(M, 1, B)` of FTZ vs GU underflow MSE. -/
def ftzContUfRatio (M b B : Nat) : Rat :=
  deltaContUf M (2 ^ b) B / deltaContUf M 1 B

/-- Exact ratio `deltaE8m0Uf(M, 2^b, B) / deltaE8m0Uf(M, 1, B)` of FTZ vs GU underflow MSE. -/
def ftzE8m0UfRatio (M b B : Nat) : Rat :=
  deltaE8m0Uf M (2 ^ b) B / deltaE8m0Uf M 1 B

end MxfpDoublelogFtz
