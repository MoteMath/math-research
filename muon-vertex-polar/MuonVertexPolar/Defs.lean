/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions for Shifted-Square (Vertex) Polar Polynomials (`muon-vertex-polar`)

Defines the exact 6-rounding-point adversarial noisy shifted-square step `NoisyShiftedStep`,
5-step adversarial trajectories `NoisyShiftedTraj5`, the pointwise degree-5 upper/lower
envelopes, and the exact BF16 and FP8 E4M3FN hardware-grid schedules from Hunt 7.
-/

namespace MuonVertexPolar

/-- Parameters `(α, β, μ)` of a shifted-square odd quintic `x * (α + β * (x^2 - μ)^2)`. -/
abbrev ShiftedParams := Rat × Rat × Rat

/-- Exact 6-rounding-point adversarial noisy shifted-square step at unit roundoff `u`.
Matches `hunt-07-muon-polar/dyadic_iv.py` (`FORM_SHIFTED`) and `baselines_and_model.py`:
1. `a  = x^2 * (1 + δ1)`       (Gram matrix `X^T X`)
2. `d  = (a - μ) * (1 + δ2)`   (diagonal shift `A - μ I`)
3. `d2 = d^2 * (1 + δ3)`       (square `D^2`)
4. `t  = β * d2 * (1 + δ4)`    (scalar scale `β D^2`)
5. `b  = (α + t) * (1 + δ5)`   (positive sum `α I + β D^2`, zero cancellation)
6. `y  = x * b * (1 + δ6)`     (final product `X B`) -/
def NoisyShiftedStep (α β μ u : Rat) (x y : Rat) : Prop :=
  ∃ δ1 δ2 δ3 δ4 δ5 δ6 : Rat,
    (-u ≤ δ1 ∧ δ1 ≤ u) ∧
    (-u ≤ δ2 ∧ δ2 ≤ u) ∧
    (-u ≤ δ3 ∧ δ3 ≤ u) ∧
    (-u ≤ δ4 ∧ δ4 ≤ u) ∧
    (-u ≤ δ5 ∧ δ5 ≤ u) ∧
    (-u ≤ δ6 ∧ δ6 ≤ u) ∧
    let a  := x * x * (1 + δ1)
    let d  := (a - μ) * (1 + δ2)
    let d2 := d * d * (1 + δ3)
    let t  := β * d2 * (1 + δ4)
    let b  := (α + t) * (1 + δ5)
    y = x * b * (1 + δ6)

/-- Five-step adversarial noisy shifted-square trajectory from `σ0` to `σ5`. -/
def NoisyShiftedTraj5 (s1 s2 s3 s4 s5 : ShiftedParams) (u : Rat) (σ0 σ5 : Rat) : Prop :=
  ∃ σ1 σ2 σ3 σ4 : Rat,
    NoisyShiftedStep s1.1 s1.2.1 s1.2.2 u σ0 σ1 ∧
    NoisyShiftedStep s2.1 s2.2.1 s2.2.2 u σ1 σ2 ∧
    NoisyShiftedStep s3.1 s3.2.1 s3.2.2 u σ2 σ3 ∧
    NoisyShiftedStep s4.1 s4.2.1 s4.2.2 u σ3 σ4 ∧
    NoisyShiftedStep s5.1 s5.2.1 s5.2.2 u σ4 σ5

/-- Pointwise upper envelope branch using `x^2 * (1 - u) - μ`. -/
def shiftedUpperMinus (α β μ u x : Rat) : Rat :=
  let up := 1 + u
  let up2 := up * up
  let up4 := up2 * up2
  let dm := x * x * (1 - u) - μ
  up2 * x * (α + up4 * β * (dm * dm))

/-- Pointwise upper envelope branch using `x^2 * (1 + u) - μ`. -/
def shiftedUpperPlus (α β μ u x : Rat) : Rat :=
  let up := 1 + u
  let up2 := up * up
  let up4 := up2 * up2
  let dp := x * x * (1 + u) - μ
  up2 * x * (α + up4 * β * (dp * dp))

/-- Pointwise lower envelope branch valid when `x^2 * (1 + u) ≤ μ`. -/
def shiftedLowerLeft (α β μ u x : Rat) : Rat :=
  let lo := 1 - u
  let lo2 := lo * lo
  let lo4 := lo2 * lo2
  let dl := μ - x * x * (1 + u)
  lo2 * x * (α + lo4 * β * (dl * dl))

/-- Pointwise lower envelope branch valid when `x^2 * (1 - u) ≥ μ`. -/
def shiftedLowerRight (α β μ u x : Rat) : Rat :=
  let lo := 1 - u
  let lo2 := lo * lo
  let lo4 := lo2 * lo2
  let dr := x * x * (1 - u) - μ
  lo2 * x * (α + lo4 * β * (dr * dr))

/-- Universal lower envelope floor `(1 - u)^2 * α * x`, valid for all `x ≥ 0`. -/
def shiftedLowerBase (α u x : Rat) : Rat :=
  (1 - u) * (1 - u) * α * x

/-- BF16 unit roundoff `u = 2^-8 = 1/256`. -/
def uBF16 : Rat := 1 / 256

/-- Pure FP8 E4M3 unit roundoff `u = 2^-4 = 1/16`. -/
def uFP8Pure : Rat := 1 / 16

/-- Hybrid FP8 unit roundoff `u = 2^-5 = 1/32`. -/
def uFP8Hybrid : Rat := 1 / 32

/-- Drop-in BF16 stationary shifted-square quintic `(31/32, 199/128, 135/128)`. -/
def bf16StationaryParams : ShiftedParams := (31 / 32, 199 / 128, 135 / 128)

/-- 5-step BF16 Shifted-Square DP winning schedule (`ε = 1/100`, `u = 1/256`). -/
def bf16DP5Step1 : ShiftedParams := (73 / 1024, 51 / 4, 173 / 256)
def bf16DP5Step2 : ShiftedParams := (59 / 512, 65 / 64, 195 / 128)
def bf16DP5Step3 : ShiftedParams := (11 / 16, 8, 171 / 256)
def bf16DP5Step4 : ShiftedParams := (25 / 32, 13 / 16, 163 / 128)
def bf16DP5Step5 : ShiftedParams := (1, 31 / 32, 147 / 128)

/-- 5-step Pure FP8 E4M3 Shifted-Square DP winning schedule (`ε = 1/100`, `u = 1/16`). -/
def fp8PureDP5Step1 : ShiftedParams := (13 / 32, 11 / 2, 3 / 4)
def fp8PureDP5Step2 : ShiftedParams := (1 / 8, 11 / 16, 11 / 8)
def fp8PureDP5Step3 : ShiftedParams := (9 / 64, 18, 13 / 32)
def fp8PureDP5Step4 : ShiftedParams := (9 / 32, 14, 9 / 16)
def fp8PureDP5Step5 : ShiftedParams := (5 / 16, 11 / 16, 15 / 8)

/-- 5-step Hybrid FP8 Shifted-Square DP winning schedule (`ε = 1/100`, `u = 1/32`). -/
def fp8HybridDP5Step1 : ShiftedParams := (1 / 8, 6, 3 / 4)
def fp8HybridDP5Step2 : ShiftedParams := (9 / 64, 6, 7 / 8)
def fp8HybridDP5Step3 : ShiftedParams := (7 / 32, 3 / 4, 15 / 8)
def fp8HybridDP5Step4 : ShiftedParams := (9 / 16, 15 / 16, 13 / 8)
def fp8HybridDP5Step5 : ShiftedParams := (11 / 16, 5 / 16, 2)

end MuonVertexPolar
