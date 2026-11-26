/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SoapVertexFourthRoot

/-!
# Verified Solutions (`soap-vertex-fourth-root`)
-/

namespace SoapVertexFourthRootChallenge

open SoapVertexFourthRoot

theorem vertex_fourth_root_equiv_monomial (a b c α β μ m : Rat) (hc : c ≠ 0) :
    a + b * m + c * m * m =
      (a - (b * b) / (4 * c)) + c * (m + b / (2 * c)) * (m + b / (2 * c)) ∧
    ((0 : Rat) ≤ β → α ≤ α + β * (m - μ) * (m - μ)) :=
  SoapVertexFourthRoot.vertex_fourth_root_equiv_monomial a b c α β μ m hc

theorem taylor2_fourth_root_vertex_exact (m : Rat) :
    ((1 : Rat) - (m - 1) / 4 + (5 / 32 : Rat) * (m - 1) * (m - 1) =
      (9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5)) ∧
    ((9 / 10 : Rat) ≤ (9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5)) ∧
    (m * ratPow4 ((9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5)) - 1 =
      (m - 1) * (m - 1) * (m - 1) * taylor2ResidualPoly m) :=
  SoapVertexFourthRoot.taylor2_fourth_root_vertex_exact m

theorem noisyFourthRootStep_envelope (α β μ p0 p1 u m yv yl : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) ≤ β)
    (hp1 : p1 ≤ (0 : Rat))
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1) (hm : (0 : Rat) < m)
    (hqLoLin : (0 : Rat) < qLoLinear p0 p1 u m)
    (hv : NoisyVertexStep4 α β μ u m yv)
    (hl : NoisyLinearStep4 p0 p1 u m yl) :
    (vertexLowerEnv4 α β μ u m ≤ yv ∧ yv ≤ vertexUpperEnv4 α β μ u m) ∧
    (linearLowerEnv4 p0 p1 u m ≤ yl ∧ yl ≤ linearUpperEnv4 p0 p1 u m) :=
  SoapVertexFourthRoot.noisyFourthRootStep_envelope α β μ p0 p1 u m yv yl
    hα hβ hp1 hu0 hu1 hm hqLoLin hv hl

theorem bf16_fourth_root_dp5_certified (m0 m5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyVertexTraj5
      bf16E2Step1 bf16E2Step2 bf16E2Step3 bf16E2Step4 bf16E2Step5 uBF16 m0 m5) :
    (965 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1039 / 1000 : Rat) :=
  SoapVertexFourthRoot.bf16_fourth_root_dp5_certified m0 m5 hlo hhi htraj

theorem bf16_fourth_root_eps1e4_certified (m0 m5 : Rat)
    (hlo : (1 / 10000 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyVertexTraj5
      bf16E4Step1 bf16E4Step2 bf16E4Step3 bf16E4Step4 bf16E4Step5 uBF16 m0 m5) :
    (935 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1049 / 1000 : Rat) :=
  SoapVertexFourthRoot.bf16_fourth_root_eps1e4_certified m0 m5 hlo hhi htraj

theorem fp8_hybrid_fourth_root_dp5_certified (m0 m5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyVertexTraj5
      fp8HybE2Step1 fp8HybE2Step2 fp8HybE2Step3 fp8HybE2Step4 fp8HybE2Step5 uFP8Hybrid m0 m5) :
    (652 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1329 / 1000 : Rat) :=
  SoapVertexFourthRoot.fp8_hybrid_fourth_root_dp5_certified m0 m5 hlo hhi htraj

theorem fp8_pure_fourth_root_linear_dp5_certified (m0 m5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyLinearTraj5
      fp8LinE2Step1 fp8LinE2Step2 fp8LinE2Step3 fp8LinE2Step4 fp8LinE2Step5 uFP8Pure m0 m5) :
    (257 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1654 / 1000 : Rat) :=
  SoapVertexFourthRoot.fp8_pure_fourth_root_linear_dp5_certified m0 m5 hlo hhi htraj

end SoapVertexFourthRootChallenge
