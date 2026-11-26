/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions for Vertex-Form Matrix Inverse-Fourth-Root (`soap-vertex-fourth-root`)

Defines:
- The exact 7-rounding-point adversarial noisy vertex-form coupled `G^{-1/4}` step
  `NoisyVertexStep4` and 5-step trajectory `NoisyVertexTraj5`,
- The exact 5-rounding-point adversarial noisy linear coupled `G^{-1/4}` step
  `NoisyLinearStep4` and 5-step trajectory `NoisyLinearTraj5`,
- Pointwise exact upper/lower polynomial envelopes for both vertex and linear steps,
- The exact degree-6 cubic-convergence residual polynomial `taylor2ResidualPoly`,
- The exact BF16 and FP8 E4M3FN hardware-grid schedules from Cluster 04 (`I031` + `I032`).
-/

namespace SoapVertexFourthRoot

/-- Parameters `(α, β, μ)` of a vertex-form quadratic `P(m) = α + β * (m - μ)^2`. -/
abbrev VertexParams := Rat × Rat × Rat

/-- Parameters `(p0, p1)` of a linear coupled step `P(m) = p0 + p1 * m`. -/
abbrev LinearParams := Rat × Rat

/-- Fourth power helper on `Rat`. -/
def ratPow4 (x : Rat) : Rat :=
  let x2 := x * x
  x2 * x2

/-- Eighth power helper on `Rat`. -/
def ratPow8 (x : Rat) : Rat :=
  let x4 := ratPow4 x
  x4 * x4

/-- Exact degree-6 residual polynomial in `x = m - 1` such that
`m * (9/10 + (5/32) * (m - 9/5)^2)^4 - 1 = (m - 1)^3 * taylor2ResidualPoly m`. -/
def taylor2ResidualPoly (m : Rat) : Rat :=
  let x := m - 1
  (15 / 32 : Rat) + x * ((-135 / 512 : Rat) + x * ((189 / 1024 : Rat) +
    x * ((-15 / 256 : Rat) + x * ((675 / 32768 : Rat) +
      x * ((-3375 / 1048576 : Rat) + x * (625 / 1048576 : Rat))))))

/-- Exact 7-rounding-point adversarial noisy vertex-form coupled `G^{-1/4}` step at unit
roundoff `u`, matching `exp_031_032_inv_roots.py` (`MODE_INV4_VERTEX`):
1. `d  = (m - μ) * (1 + δ1)`
2. `d2 = d * d * (1 + δ2)`
3. `t  = β * d2 * (1 + δ3)`
4. `p  = (α + t) * (1 + δ4)`
5. `p2 = p * p * (1 + δ5)`
6. `p4 = p2 * p2 * (1 + δ6)`
7. `y  = m * p4 * (1 + δ7)`
with `-u ≤ δi ≤ u` for each `i = 1..7`. -/
def NoisyVertexStep4 (α β μ u : Rat) (m y : Rat) : Prop :=
  ∃ δ1 δ2 δ3 δ4 δ5 δ6 δ7 : Rat,
    (-u ≤ δ1 ∧ δ1 ≤ u) ∧
    (-u ≤ δ2 ∧ δ2 ≤ u) ∧
    (-u ≤ δ3 ∧ δ3 ≤ u) ∧
    (-u ≤ δ4 ∧ δ4 ≤ u) ∧
    (-u ≤ δ5 ∧ δ5 ≤ u) ∧
    (-u ≤ δ6 ∧ δ6 ≤ u) ∧
    (-u ≤ δ7 ∧ δ7 ≤ u) ∧
    let d  := (m - μ) * (1 + δ1)
    let d2 := d * d * (1 + δ2)
    let t  := β * d2 * (1 + δ3)
    let p  := (α + t) * (1 + δ4)
    let p2 := p * p * (1 + δ5)
    let p4 := p2 * p2 * (1 + δ6)
    y = m * p4 * (1 + δ7)

/-- Five-step adversarial noisy vertex-form `G^{-1/4}` trajectory from `m0` to `m5`. -/
def NoisyVertexTraj5 (s1 s2 s3 s4 s5 : VertexParams) (u : Rat) (m0 m5 : Rat) : Prop :=
  ∃ m1 m2 m3 m4 : Rat,
    NoisyVertexStep4 s1.1 s1.2.1 s1.2.2 u m0 m1 ∧
    NoisyVertexStep4 s2.1 s2.2.1 s2.2.2 u m1 m2 ∧
    NoisyVertexStep4 s3.1 s3.2.1 s3.2.2 u m2 m3 ∧
    NoisyVertexStep4 s4.1 s4.2.1 s4.2.2 u m3 m4 ∧
    NoisyVertexStep4 s5.1 s5.2.1 s5.2.2 u m4 m5

/-- Exact 5-rounding-point adversarial noisy linear coupled `G^{-1/4}` step at unit
roundoff `u`, matching `exp_031_032_inv_roots.py` (`MODE_INV4_LINEAR`):
1. `t  = p1 * m * (1 + δ1)`
2. `p  = (p0 + t) * (1 + δ2)`
3. `p2 = p * p * (1 + δ3)`
4. `p4 = p2 * p2 * (1 + δ4)`
5. `y  = m * p4 * (1 + δ5)`
with `-u ≤ δi ≤ u` for each `i = 1..5`. -/
def NoisyLinearStep4 (p0 p1 u : Rat) (m y : Rat) : Prop :=
  ∃ δ1 δ2 δ3 δ4 δ5 : Rat,
    (-u ≤ δ1 ∧ δ1 ≤ u) ∧
    (-u ≤ δ2 ∧ δ2 ≤ u) ∧
    (-u ≤ δ3 ∧ δ3 ≤ u) ∧
    (-u ≤ δ4 ∧ δ4 ≤ u) ∧
    (-u ≤ δ5 ∧ δ5 ≤ u) ∧
    let t  := p1 * m * (1 + δ1)
    let p  := (p0 + t) * (1 + δ2)
    let p2 := p * p * (1 + δ3)
    let p4 := p2 * p2 * (1 + δ4)
    y = m * p4 * (1 + δ5)

/-- Five-step adversarial noisy linear coupled `G^{-1/4}` trajectory from `m0` to `m5`. -/
def NoisyLinearTraj5 (s1 s2 s3 s4 s5 : LinearParams) (u : Rat) (m0 m5 : Rat) : Prop :=
  ∃ m1 m2 m3 m4 : Rat,
    NoisyLinearStep4 s1.1 s1.2 u m0 m1 ∧
    NoisyLinearStep4 s2.1 s2.2 u m1 m2 ∧
    NoisyLinearStep4 s3.1 s3.2 u m2 m3 ∧
    NoisyLinearStep4 s4.1 s4.2 u m3 m4 ∧
    NoisyLinearStep4 s5.1 s5.2 u m4 m5

/-- Pointwise inner lower polynomial `qLoVertex` for a vertex step. -/
def qLoVertex (α β μ u m : Rat) : Rat :=
  α + ratPow4 (1 - u) * β * ((m - μ) * (m - μ))

/-- Pointwise inner upper polynomial `qHiVertex` for a vertex step. -/
def qHiVertex (α β μ u m : Rat) : Rat :=
  α + ratPow4 (1 + u) * β * ((m - μ) * (m - μ))

/-- Pointwise exact lower envelope for `NoisyVertexStep4`. -/
def vertexLowerEnv4 (α β μ u m : Rat) : Rat :=
  ratPow8 (1 - u) * m * ratPow4 (qLoVertex α β μ u m)

/-- Pointwise exact upper envelope for `NoisyVertexStep4`. -/
def vertexUpperEnv4 (α β μ u m : Rat) : Rat :=
  ratPow8 (1 + u) * m * ratPow4 (qHiVertex α β μ u m)

/-- Pointwise inner lower affine polynomial `qLoLinear` for a linear step (`p1 ≤ 0`). -/
def qLoLinear (p0 p1 u m : Rat) : Rat :=
  p0 + p1 * (1 + u) * m

/-- Pointwise inner upper affine polynomial `qHiLinear` for a linear step (`p1 ≤ 0`). -/
def qHiLinear (p0 p1 u m : Rat) : Rat :=
  p0 + p1 * (1 - u) * m

/-- Pointwise exact lower envelope for `NoisyLinearStep4` (`p1 ≤ 0`, `0 < qLoLinear`). -/
def linearLowerEnv4 (p0 p1 u m : Rat) : Rat :=
  ratPow8 (1 - u) * m * ratPow4 (qLoLinear p0 p1 u m)

/-- Pointwise exact upper envelope for `NoisyLinearStep4` (`p1 ≤ 0`, `0 < qLoLinear`). -/
def linearUpperEnv4 (p0 p1 u m : Rat) : Rat :=
  ratPow8 (1 + u) * m * ratPow4 (qHiLinear p0 p1 u m)

/-- BF16 unit roundoff `u = 2^-8 = 1/256`. -/
def uBF16 : Rat := 1 / 256

/-- Hybrid FP8 unit roundoff `u = 2^-5 = 1/32`. -/
def uFP8Hybrid : Rat := 1 / 32

/-- Pure FP8 E4M3 unit roundoff `u = 2^-4 = 1/16`. -/
def uFP8Pure : Rat := 1 / 16

/-- 5-step BF16 Vertex-Form `G^{-1/4}` DP schedule (`ε = 1/100`, `u = 1/256`),
exact `inv4_vertex_bf16_e2` from `exp_031_032_results.json`. -/
def bf16E2Step1 : VertexParams := (27 / 32, 133 / 64, 243 / 256)
def bf16E2Step2 : VertexParams := (185 / 256, 87 / 1024, 83 / 32)
def bf16E2Step3 : VertexParams := (207 / 256, 87 / 1024, 81 / 32)
def bf16E2Step4 : VertexParams := (227 / 256, 37 / 256, 241 / 128)
def bf16E2Step5 : VertexParams := (251 / 256, 183 / 256, 149 / 128)

/-- 5-step BF16 Vertex-Form `G^{-1/4}` DP schedule (`ε = 1/10000`, `u = 1/256`),
exact `inv4_vertex_bf16_e4` from `exp_031_032_results.json`. -/
def bf16E4Step1 : VertexParams := (1 / 4, 133 / 64, 243 / 256)
def bf16E4Step2 : VertexParams := (1 / 4, 9 / 8, 243 / 256)
def bf16E4Step3 : VertexParams := (1 / 4, 133 / 64, 243 / 256)
def bf16E4Step4 : VertexParams := (209 / 256, 33 / 32, 243 / 256)
def bf16E4Step5 : VertexParams := (131 / 128, 153 / 256, 131 / 128)

/-- 5-step Hybrid FP8 Vertex-Form `G^{-1/4}` DP schedule (`ε = 1/100`, `u = 1/32`),
exact `inv4_vertex_fp8hyb_e2` from `exp_031_032_results.json`. -/
def fp8HybE2Step1 : VertexParams := (7 / 8, 15 / 4, 11 / 16)
def fp8HybE2Step2 : VertexParams := (5 / 8, 11 / 128, 3)
def fp8HybE2Step3 : VertexParams := (13 / 16, 1 / 8, 9 / 4)
def fp8HybE2Step4 : VertexParams := (7 / 8, 7 / 32, 13 / 8)
def fp8HybE2Step5 : VertexParams := (15 / 16, 7 / 16, 5 / 4)

/-- 5-step Pure FP8 E4M3 Linear Coupled `G^{-1/4}` DP schedule (`ε = 1/100`, `u = 1/16`),
exact `inv4_linear_fp8_e2` from `exp_031_032_results.json`. -/
def fp8LinE2Step1 : LinearParams := (7 / 4, -9 / 8)
def fp8LinE2Step2 : LinearParams := (15 / 8, -1 / 2)
def fp8LinE2Step3 : LinearParams := (11 / 8, -13 / 128)
def fp8LinE2Step4 : LinearParams := (1, -1 / 16)
def fp8LinE2Step5 : LinearParams := (9 / 8, -5 / 32)

end SoapVertexFourthRoot
