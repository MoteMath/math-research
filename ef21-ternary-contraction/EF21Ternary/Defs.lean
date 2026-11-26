/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Definitions for Exact EF21 Contraction & Quantization Laws

Public definitions shared by `Challenge.lean` and `Solution.lean` for the exact worst-case
EF21 contraction laws of optimal ternary compression, OCP E2M1 block-scaled formats
(MXFP4 / NVFP4), zero-omitting symmetric 2-bit quantizers, and floating-point mantissa
stochastic rounding.
-/

namespace EF21Ternary

open scoped BigOperators

/-- The exact ternary extremal vector `w_i = √(i + 1) - √i` on `Fin d`. -/
noncomputable def ternaryExtremal (d : ℕ) (i : Fin d) : ℝ :=
  Real.sqrt ((i.1 : ℝ) + 1) - Real.sqrt (i.1 : ℝ)

/-- Exact worst-case EF21 contraction factor for optimal ternary compression in dimension `d`:
`α_tern(d) = (∑_{i=0}^{d-1} (√(i + 1) - √i)^2)⁻¹`. -/
noncomputable def alphaTern (d : ℕ) : ℝ :=
  (∑ i : Fin d, (Real.sqrt ((i.1 : ℝ) + 1) - Real.sqrt (i.1 : ℝ)) ^ 2)⁻¹

/-- The `n`-th harmonic number `H_n = ∑_{i=0}^{n-1} 1 / (i + 1)` as a real number. -/
noncomputable def harmonicR (n : ℕ) : ℝ :=
  ∑ i : Fin n, (1 : ℝ) / ((i.1 : ℝ) + 1)

/-- Nonnegative half of the exact nearest-neighbor OCP E2M1 quantizer onto
`{0, 1/2, 1, 3/2, 2, 3, 4, 6}`. -/
noncomputable def e2m1QuantNonneg (y : ℝ) : ℝ :=
  if y < 1 / 4 then 0
  else if y < 3 / 4 then 1 / 2
  else if y < 5 / 4 then 1
  else if y < 7 / 4 then 3 / 2
  else if y < 5 / 2 then 2
  else if y < 7 / 2 then 3
  else if y < 5 then 4
  else 6

/-- Exact symmetric nearest-neighbor OCP E2M1 quantizer onto
`{0, ±1/2, ±1, ±3/2, ±2, ±3, ±4, ±6}`. -/
noncomputable def e2m1Quant (y : ℝ) : ℝ :=
  if 0 ≤ y then e2m1QuantNonneg y else -e2m1QuantNonneg (-y)

/-- Exact universal EF21 contraction factor for MXFP4 (OCP E2M1 with E8M0 power-of-2 block scaling,
block size `B ≥ 1`): three exact phase regimes (`1 ≤ B ≤ 8`, `9 ≤ B ≤ 12`, `B ≥ 13`),
matching `48/53` at `B = 16` and `144/175` at `B = 32`. -/
noncomputable def alphaMXFP4 (B : ℕ) : ℝ :=
  min (384 / ((B : ℝ) + 399)) (min (192 / ((B : ℝ) + 195)) (144 / ((B : ℝ) + 143)))

/-- Exact universal EF21 contraction factor for NVFP4 (OCP E2M1 with continuous/FP8 block scaling,
block size `B ≥ 1`): two exact phase regimes (`1 ≤ B ≤ 23`, `B ≥ 24`),
matching `132/137` at `B = 16` and `576/607` at `B = 32`. -/
noncomputable def alphaNVFP4 (B : ℕ) : ℝ :=
  min ((24 * (B : ℝ) + 12) / (25 * (B : ℝ) + 11)) (576 / ((B : ℝ) + 575))

end EF21Ternary
