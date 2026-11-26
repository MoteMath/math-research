/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonVertexPolar

/-!
# Verified Solutions (`muon-vertex-polar`)
-/

namespace MuonVertexPolarChallenge

open MuonVertexPolar

theorem shifted_square_equiv_monomial (a b c x : Rat) (hc : c ≠ 0) :
    let μ := -b / (2 * c)
    let α := a - (b * b) / (4 * c)
    a * x + b * (x * x * x) + c * (x * x * x * x * x) =
      x * (α + c * ((x * x - μ) * (x * x - μ))) :=
  MuonVertexPolar.shifted_square_equiv_monomial a b c x hc

theorem shifted_square_quadratic_error_at_one (α β b c u δ1 : Rat)
    (hβ : (0 : Rat) ≤ β) (hlo : -u ≤ δ1) (hhi : δ1 ≤ u) :
    let a := (1 : Rat) * (1 + δ1)
    (α + β * ((a - 1) * (a - 1)) - α = β * (δ1 * δ1)) ∧
    (β * ((a - 1) * (a - 1)) ≤ β * (u * u)) ∧
    (b * a + c * (a * a) - (b + c) = (b + 2 * c) * δ1 + c * (δ1 * δ1)) :=
  MuonVertexPolar.shifted_square_quadratic_error_at_one α β b c u δ1 hβ hlo hhi

theorem noisyShiftedStep_envelope (α β μ u x y : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) < β)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1) (hx : (0 : Rat) ≤ x)
    (hstep : NoisyShiftedStep α β μ u x y) :
    y ≤ max (shiftedUpperMinus α β μ u x) (shiftedUpperPlus α β μ u x) ∧
    (shiftedLowerBase α u x ≤ y) ∧
    (x * x * (1 + u) ≤ μ → shiftedLowerLeft α β μ u x ≤ y) ∧
    (μ ≤ x * x * (1 - u) → shiftedLowerRight α β μ u x ≤ y) :=
  MuonVertexPolar.noisyShiftedStep_envelope α β μ u x y hα hβ hu0 hu1 hx hstep

theorem bf16_stationary_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5
      bf16StationaryParams bf16StationaryParams bf16StationaryParams
      bf16StationaryParams bf16StationaryParams uBF16 σ0 σ5) :
    (942 / 1000 : Rat) ≤ σ5 ∧ σ5 ≤ (1052 / 1000 : Rat) :=
  MuonVertexPolar.bf16_stationary_shifted_certified σ0 σ5 hlo hhi htraj

theorem bf16_dp5_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5
      bf16DP5Step1 bf16DP5Step2 bf16DP5Step3 bf16DP5Step4 bf16DP5Step5 uBF16 σ0 σ5) :
    (987 / 1000 : Rat) ≤ σ5 ∧ σ5 ≤ (1013 / 1000 : Rat) :=
  MuonVertexPolar.bf16_dp5_shifted_certified σ0 σ5 hlo hhi htraj

theorem fp8_pure_dp5_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5
      fp8PureDP5Step1 fp8PureDP5Step2 fp8PureDP5Step3 fp8PureDP5Step4 fp8PureDP5Step5 uFP8Pure σ0 σ5) :
    (31 / 100 : Rat) ≤ σ5 ∧ σ5 ≤ (165 / 100 : Rat) :=
  MuonVertexPolar.fp8_pure_dp5_shifted_certified σ0 σ5 hlo hhi htraj

theorem fp8_hybrid_dp5_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5
      fp8HybridDP5Step1 fp8HybridDP5Step2 fp8HybridDP5Step3 fp8HybridDP5Step4 fp8HybridDP5Step5 uFP8Hybrid σ0 σ5) :
    (824 / 1000 : Rat) ≤ σ5 ∧ σ5 ≤ (1163 / 1000 : Rat) :=
  MuonVertexPolar.fp8_hybrid_dp5_shifted_certified σ0 σ5 hlo hhi htraj

end MuonVertexPolarChallenge
