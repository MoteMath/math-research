/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions for Universal All-`p` Coupled `G^{-1/p}` Vertex Law (`universal-vertex-invroot`)

Defines:
- Universal all-`p` 2nd-order Taylor polynomial `taylor2InvRoot p m`, completed-square vertex
  polynomial `vertexInvRoot p m`, and exact monomial expansion coefficients `monoC0`, `monoC1`,
  `monoC2`;
- Exact recursive power `ratPow`, polynomial remainder `polyPowRem`, and universal all-`p`
  cubic convergence quotient `invRootCubicQuot p x`;
- Exact adversarial noisy vertex-form coupled steps `NoisyVertexStep2`, `NoisyVertexStep3`,
  `NoisyVertexStep8` (matching `dyadic_exact.py` / `polar_higher_roots.hip`) and 6-step
  stationary trajectories `NoisyVertexTraj6_2`, `NoisyVertexTraj6_3`, `NoisyVertexTraj6_8`;
- Pointwise exact upper/lower polynomial envelopes for `p ∈ {2, 3, 8}`;
- Exact BF16 (`u = 1/256`), Hybrid FP8 (`u = 1/32`), Pure FP8 (`u = 1/16`) unit roundoffs and
  the exact Q32.32 `quad_vertex` BF16 schedules from `w1-polar-higher-roots/results.json`.
-/

namespace UniversalVertexInvroot

/-- Parameters `(α, β, μ)` of a vertex-form quadratic `P(m) = α + β * (m - μ)^2`. -/
abbrev VertexParams := Rat × Rat × Rat

/-- Absolute value on `Rat` (pure `Init`). -/
def ratAbs (x : Rat) : Rat :=
  if x < 0 then -x else x

/-- Natural-number power on `Rat` (pure `Init`). -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPow x n * x

/-- 2nd-order Taylor/Halley polynomial of `m^(-1/p)` at `m = 1`. -/
def taylor2InvRoot (p : Nat) (m : Rat) : Rat :=
  1 - (m - 1) / (p : Rat) +
    ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) * (m - 1) * (m - 1)

/-- Completed-square (vertex) form of `taylor2InvRoot p m` for all `p ≥ 1`. -/
def vertexInvRoot (p : Nat) (m : Rat) : Rat :=
  (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) +
    ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) *
      (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
      (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1))

/-- Constant monomial coefficient `c0` of `taylor2InvRoot p m = c0 + c1 * m + c2 * m^2`. -/
def monoC0 (p : Nat) : Rat :=
  1 + 1 / (p : Rat) + ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat))

/-- Linear monomial coefficient `c1` of `taylor2InvRoot p m = c0 + c1 * m + c2 * m^2`. -/
def monoC1 (p : Nat) : Rat :=
  -(1 / (p : Rat)) - ((p : Rat) + 1) / ((p : Rat) * (p : Rat))

/-- Quadratic monomial coefficient `c2` of `taylor2InvRoot p m = c0 + c1 * m + c2 * m^2`. -/
def monoC2 (p : Nat) : Rat :=
  ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat))

/-- Explicit degree-`2k - 3` polynomial remainder `R_k(x)` such that
`(1 + a * x + b * x^2)^k = 1 + k * a * x + (k * b + k * (k - 1) / 2 * a^2) * x^2 + x^3 * R_k(x)`. -/
def polyPowRem (a b x : Rat) : Nat → Rat
  | 0 => 0
  | k + 1 =>
    let ak := (k : Rat) * a
    let bk := (k : Rat) * b + ((k : Rat) * ((k : Rat) - 1) / 2) * (a * a)
    ak * b + bk * a + bk * b * x + polyPowRem a b x k * (1 + a * x + b * x * x)

/-- Explicit universal cubic-convergence quotient `R_p(x)` in `x = m - 1` such that
`m * (vertexInvRoot p m)^p - 1 = (m - 1)^3 * invRootCubicQuot p (m - 1)` for all `p ≥ 1`,
with exact leading constant `invRootCubicQuot p 0 = (p + 1) * (2 * p + 1) / (6 * p^2)`. -/
def invRootCubicQuot (p : Nat) (x : Rat) : Rat :=
  1 + (1 + x) * polyPowRem (-1 / (p : Rat)) (((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat))) x p

/-- Exact 6-rounding-point adversarial noisy vertex-form coupled `G^{-1/2}` step at unit
roundoff `u`, matching `dyadic_exact.py` (`PROOT_QUAD_VERTEX`, `p_root = 2`):
1. `d  = (m - μ) * (1 + δ1)`
2. `d2 = d * d * (1 + δ2)`
3. `t  = β * d2 * (1 + δ3)`
4. `p  = (α + t) * (1 + δ4)`
5. `p2 = p * p * (1 + δ5)`
6. `y  = m * p2 * (1 + δ6)`
with `-u ≤ δi ≤ u` for `i = 1..6`. -/
def NoisyVertexStep2 (α β μ u : Rat) (m y : Rat) : Prop :=
  ∃ δ1 δ2 δ3 δ4 δ5 δ6 : Rat,
    (-u ≤ δ1 ∧ δ1 ≤ u) ∧
    (-u ≤ δ2 ∧ δ2 ≤ u) ∧
    (-u ≤ δ3 ∧ δ3 ≤ u) ∧
    (-u ≤ δ4 ∧ δ4 ≤ u) ∧
    (-u ≤ δ5 ∧ δ5 ≤ u) ∧
    (-u ≤ δ6 ∧ δ6 ≤ u) ∧
    let d  := (m - μ) * (1 + δ1)
    let d2 := d * d * (1 + δ2)
    let t  := β * d2 * (1 + δ3)
    let p  := (α + t) * (1 + δ4)
    let p2 := p * p * (1 + δ5)
    y = m * p2 * (1 + δ6)

/-- Exact 7-rounding-point adversarial noisy vertex-form coupled `G^{-1/3}` step at unit
roundoff `u`, matching `dyadic_exact.py` (`PROOT_QUAD_VERTEX`, `p_root = 3`):
1. `d  = (m - μ) * (1 + δ1)`
2. `d2 = d * d * (1 + δ2)`
3. `t  = β * d2 * (1 + δ3)`
4. `p  = (α + t) * (1 + δ4)`
5. `p2 = p * p * (1 + δ5)`
6. `p3 = p2 * p * (1 + δ6)`
7. `y  = m * p3 * (1 + δ7)`
with `-u ≤ δi ≤ u` for `i = 1..7`. -/
def NoisyVertexStep3 (α β μ u : Rat) (m y : Rat) : Prop :=
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
    let p3 := p2 * p * (1 + δ6)
    y = m * p3 * (1 + δ7)

/-- Exact 8-rounding-point adversarial noisy vertex-form coupled `G^{-1/8}` step at unit
roundoff `u`, matching `dyadic_exact.py` (`PROOT_QUAD_VERTEX`, `p_root = 8`):
1. `d  = (m - μ) * (1 + δ1)`
2. `d2 = d * d * (1 + δ2)`
3. `t  = β * d2 * (1 + δ3)`
4. `p  = (α + t) * (1 + δ4)`
5. `p2 = p * p * (1 + δ5)`
6. `p4 = p2 * p2 * (1 + δ6)`
7. `p8 = p4 * p4 * (1 + δ7)`
8. `y  = m * p8 * (1 + δ8)`
with `-u ≤ δi ≤ u` for `i = 1..8`. -/
def NoisyVertexStep8 (α β μ u : Rat) (m y : Rat) : Prop :=
  ∃ δ1 δ2 δ3 δ4 δ5 δ6 δ7 δ8 : Rat,
    (-u ≤ δ1 ∧ δ1 ≤ u) ∧
    (-u ≤ δ2 ∧ δ2 ≤ u) ∧
    (-u ≤ δ3 ∧ δ3 ≤ u) ∧
    (-u ≤ δ4 ∧ δ4 ≤ u) ∧
    (-u ≤ δ5 ∧ δ5 ≤ u) ∧
    (-u ≤ δ6 ∧ δ6 ≤ u) ∧
    (-u ≤ δ7 ∧ δ7 ≤ u) ∧
    (-u ≤ δ8 ∧ δ8 ≤ u) ∧
    let d  := (m - μ) * (1 + δ1)
    let d2 := d * d * (1 + δ2)
    let t  := β * d2 * (1 + δ3)
    let p  := (α + t) * (1 + δ4)
    let p2 := p * p * (1 + δ5)
    let p4 := p2 * p2 * (1 + δ6)
    let p8 := p4 * p4 * (1 + δ7)
    y = m * p8 * (1 + δ8)

/-- Six-step stationary adversarial noisy vertex-form `G^{-1/2}` trajectory from `m0` to `m6`. -/
def NoisyVertexTraj6_2 (s : VertexParams) (u : Rat) (m0 m6 : Rat) : Prop :=
  ∃ m1 m2 m3 m4 m5 : Rat,
    NoisyVertexStep2 s.1 s.2.1 s.2.2 u m0 m1 ∧
    NoisyVertexStep2 s.1 s.2.1 s.2.2 u m1 m2 ∧
    NoisyVertexStep2 s.1 s.2.1 s.2.2 u m2 m3 ∧
    NoisyVertexStep2 s.1 s.2.1 s.2.2 u m3 m4 ∧
    NoisyVertexStep2 s.1 s.2.1 s.2.2 u m4 m5 ∧
    NoisyVertexStep2 s.1 s.2.1 s.2.2 u m5 m6

/-- Six-step stationary adversarial noisy vertex-form `G^{-1/3}` trajectory from `m0` to `m6`. -/
def NoisyVertexTraj6_3 (s : VertexParams) (u : Rat) (m0 m6 : Rat) : Prop :=
  ∃ m1 m2 m3 m4 m5 : Rat,
    NoisyVertexStep3 s.1 s.2.1 s.2.2 u m0 m1 ∧
    NoisyVertexStep3 s.1 s.2.1 s.2.2 u m1 m2 ∧
    NoisyVertexStep3 s.1 s.2.1 s.2.2 u m2 m3 ∧
    NoisyVertexStep3 s.1 s.2.1 s.2.2 u m3 m4 ∧
    NoisyVertexStep3 s.1 s.2.1 s.2.2 u m4 m5 ∧
    NoisyVertexStep3 s.1 s.2.1 s.2.2 u m5 m6

/-- Six-step stationary adversarial noisy vertex-form `G^{-1/8}` trajectory from `m0` to `m6`. -/
def NoisyVertexTraj6_8 (s : VertexParams) (u : Rat) (m0 m6 : Rat) : Prop :=
  ∃ m1 m2 m3 m4 m5 : Rat,
    NoisyVertexStep8 s.1 s.2.1 s.2.2 u m0 m1 ∧
    NoisyVertexStep8 s.1 s.2.1 s.2.2 u m1 m2 ∧
    NoisyVertexStep8 s.1 s.2.1 s.2.2 u m2 m3 ∧
    NoisyVertexStep8 s.1 s.2.1 s.2.2 u m3 m4 ∧
    NoisyVertexStep8 s.1 s.2.1 s.2.2 u m4 m5 ∧
    NoisyVertexStep8 s.1 s.2.1 s.2.2 u m5 m6

/-- Pointwise inner lower polynomial `qLoVertex` for a vertex step. -/
def qLoVertex (α β μ u m : Rat) : Rat :=
  α + ratPow (1 - u) 4 * β * ((m - μ) * (m - μ))

/-- Pointwise inner upper polynomial `qHiVertex` for a vertex step. -/
def qHiVertex (α β μ u m : Rat) : Rat :=
  α + ratPow (1 + u) 4 * β * ((m - μ) * (m - μ))

/-- Pointwise exact lower envelope for a coupled `G^{-1/p}` vertex step (`p ∈ {2, 3, 8}`). -/
def vertexLowerEnv (p : Nat) (α β μ u m : Rat) : Rat :=
  ratPow (1 - u) (2 * p) * m * ratPow (qLoVertex α β μ u m) p

/-- Pointwise exact upper envelope for a coupled `G^{-1/p}` vertex step (`p ∈ {2, 3, 8}`). -/
def vertexUpperEnv (p : Nat) (α β μ u m : Rat) : Rat :=
  ratPow (1 + u) (2 * p) * m * ratPow (qHiVertex α β μ u m) p

/-- BF16 unit roundoff `u = 2^-8 = 1/256`. -/
def uBF16 : Rat := 1 / 256

/-- Hybrid FP8 unit roundoff `u = 2^-5 = 1/32`. -/
def uFP8Hybrid : Rat := 1 / 32

/-- Pure FP8 E4M3 unit roundoff `u = 2^-4 = 1/16`. -/
def uFP8Pure : Rat := 1 / 16

/-- Exact Q32.32 BF16 `quad_vertex` stationary parameters for `p = 2` (`p2_bf16` in `results.json`). -/
def bf16InvSqrtParams : VertexParams :=
  (4115409943 / 4294967296, 6258468564 / 4294967296, 5020662387 / 4294967296)

/-- Exact Q32.32 BF16 `quad_vertex` stationary parameters for `p = 3` (`p3_bf16` in `results.json`). -/
def bf16InvCbrtParams : VertexParams :=
  (4185630849 / 4294967296, 4605301221 / 4294967296, 4951892153 / 4294967296)

/-- Exact Q32.32 BF16 `quad_vertex` stationary parameters for `p = 8` (`p8_bf16` in `results.json`). -/
def bf16InvEighthParams : VertexParams :=
  (4193173389 / 4294967296, 701570769 / 4294967296, 5914773772 / 4294967296)

end UniversalVertexInvroot
