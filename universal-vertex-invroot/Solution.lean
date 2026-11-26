/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UniversalVertexInvroot

/-!
# Verified Solutions (`universal-vertex-invroot`)
-/

namespace UniversalVertexInvrootChallenge

open UniversalVertexInvroot

theorem universal_invroot_vertex_identity_and_positivity (p : Nat) (hp : 1 ≤ p) (m : Rat) :
    (taylor2InvRoot p m = vertexInvRoot p m) ∧
    ((3 / 4 : Rat) ≤ (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) ∧
      (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) ≤ vertexInvRoot p m) ∧
    (taylor2InvRoot p m = monoC0 p + monoC1 p * m + monoC2 p * m * m) ∧
    (ratAbs (monoC0 p) + ratAbs (monoC1 p) + ratAbs (monoC2 p) =
      1 + 4 / (p : Rat) + 2 / ((p : Rat) * (p : Rat)) ∧
     ratAbs ((2 * (p : Rat) + 1) / (2 * (p : Rat) + 2)) +
      ratAbs (((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) *
        (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
        (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1))) = 1) :=
  UniversalVertexInvroot.universal_invroot_vertex_identity_and_positivity p hp m

theorem universal_invroot_cubic_convergence (p : Nat) (hp : 1 ≤ p) (m : Rat) :
    (m * ratPow (vertexInvRoot p m) p - 1 =
      (m - 1) * (m - 1) * (m - 1) * invRootCubicQuot p (m - 1)) ∧
    (invRootCubicQuot p 0 =
      ((p : Rat) + 1) * (2 * (p : Rat) + 1) / (6 * (p : Rat) * (p : Rat))) :=
  UniversalVertexInvroot.universal_invroot_cubic_convergence p hp m

theorem deg9_shared_square_and_rounding_floor_dominance
    (a c d μ1 μ2 u : Rat) (hu : (0 : Rat) < u) :
    (c + d * (a - μ2) * (a - μ2) =
      (c + d * (μ1 - μ2) * (μ1 - μ2)) +
        d * ((a - μ1) * (a - μ1)) +
        2 * d * (μ1 - μ2) * (a - μ1)) ∧
    ((5 : Nat) ^ 4 < (9 : Nat) ^ 3) ∧
    (ratPow (1 + u) 6 < ratPow (1 + u) 10) ∧
    ((165 / 100 : Rat) * (ratPow (1 + uBF16) 6 - 1) < ratPow (1 + uBF16) 10 - 1 ∧
     (165 / 100 : Rat) * (ratPow (1 + uFP8Hybrid) 6 - 1) < ratPow (1 + uFP8Hybrid) 10 - 1 ∧
     (165 / 100 : Rat) * (ratPow (1 + uFP8Pure) 6 - 1) < ratPow (1 + uFP8Pure) 10 - 1) :=
  UniversalVertexInvroot.deg9_shared_square_and_rounding_floor_dominance a c d μ1 μ2 u hu

theorem bf16_inv_sqrt_vertex_certified (m0 m6 : Rat)
    (hlo : (85 / 100 : Rat) ≤ m0) (hhi : m0 ≤ (115 / 100 : Rat))
    (htraj : NoisyVertexTraj6_2 bf16InvSqrtParams uBF16 m0 m6) :
    (982 / 1000 : Rat) ≤ m6 ∧ m6 ≤ (1018 / 1000 : Rat) :=
  UniversalVertexInvroot.bf16_inv_sqrt_vertex_certified m0 m6 hlo hhi htraj

theorem bf16_inv_cbrt_vertex_certified (m0 m6 : Rat)
    (hlo : (85 / 100 : Rat) ≤ m0) (hhi : m0 ≤ (115 / 100 : Rat))
    (htraj : NoisyVertexTraj6_3 bf16InvCbrtParams uBF16 m0 m6) :
    (974 / 1000 : Rat) ≤ m6 ∧ m6 ≤ (1026 / 1000 : Rat) :=
  UniversalVertexInvroot.bf16_inv_cbrt_vertex_certified m0 m6 hlo hhi htraj

theorem bf16_inv_eighth_vertex_certified (m0 m6 : Rat)
    (hlo : (85 / 100 : Rat) ≤ m0) (hhi : m0 ≤ (115 / 100 : Rat))
    (htraj : NoisyVertexTraj6_8 bf16InvEighthParams uBF16 m0 m6) :
    (932 / 1000 : Rat) ≤ m6 ∧ m6 ≤ (1068 / 1000 : Rat) :=
  UniversalVertexInvroot.bf16_inv_eighth_vertex_certified m0 m6 hlo hhi htraj

end UniversalVertexInvrootChallenge
