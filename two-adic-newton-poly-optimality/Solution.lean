/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoAdicNewtonPolyOptimality

/-!
# Verified Solutions (`two-adic-newton-poly-optimality`)
-/

namespace TwoAdicNewtonPolyOptimalityChallenge

open AdicNewtonOptimality

theorem fact_exactVal2 (n : Nat) : ExactVal2 (fact n : Int) (n - popcount n) :=
  AdicNewtonOptimality.fact_exactVal2 n

theorem exact_2adic_poly_reciprocal_optimality (D N : Nat) :
    (∃ p : List Int, p.length ≤ D + 1 ∧ ∀ a : Int, OddInt a → DivPow2 (1 - a * evalPoly p a) N) ↔
      N ≤ 2 * (D + 1) - popcount (D + 1) :=
  AdicNewtonOptimality.exact_2adic_poly_reciprocal_optimality D N

theorem exact_2adic_poly_optimality_pow2_sub_one (k N : Nat) :
    (∃ p : List Int, p.length ≤ 2 ^ k ∧ ∀ a : Int, OddInt a → DivPow2 (1 - a * evalPoly p a) N) ↔
      N ≤ 2 ^ (k + 1) - 1 :=
  AdicNewtonOptimality.exact_2adic_poly_optimality_pow2_sub_one k N

theorem circuit_mulDepth_optimality_pos {C : PolyCircuit} {N : Nat}
    (hk : 1 ≤ mulDepth C)
    (hmod : ∀ a : Int, OddInt a → DivPow2 (1 - a * evalCircuit C a) N) :
    N ≤ 2 ^ (mulDepth C + 1) :=
  AdicNewtonOptimality.circuit_mulDepth_optimality_pos hk hmod

theorem cert_minimal_step_optimality_closed (C : AffineContractionCert)
    (seed : Int → Int) (m0 : Nat) (hm0 : C.mCrit ≤ m0)
    (hseed_all : ∀ a, C.valid a → DivPow2 (C.res a (seed a)) m0)
    (aStar : Int) (haStar : C.valid aStar) (hsharp : ExactVal2 (C.res aStar (seed aStar)) m0)
    (k N : Nat) :
    (∀ a, C.valid a → DivPow2 (C.res a (iterateStep C.step a (seed a) k)) N) ↔
      (C.d - 1) * N ≤ C.d ^ k * ((C.d - 1) * m0 - C.s) + C.s :=
  AdicNewtonOptimality.cert_minimal_step_optimality_closed C seed m0 hm0 hseed_all aStar haStar hsharp k N

theorem recip_minimal_step_dumas {d : Nat} (hd : 2 ≤ d) (k N : Nat) :
    (∀ a : Nat, a % 2 = 1 →
      DivPow2 (1 - (a : Int) * iterateStep (recipStep d) (a : Int) (dumasSeedNat a : Int) k) N) ↔
      N ≤ 5 * d ^ k :=
  AdicNewtonOptimality.recip_minimal_step_dumas hd k N

theorem invSqrtS3_popcount_supergain {a x0 : Int} {m0 : Nat}
    (hm0 : 4 ≤ m0) (h0 : ExactVal2 (1 - a * x0 * x0) m0) (k : Nat) :
    ExactVal2 (1 - a * iterateStep invSqrtS3 a x0 k * iterateStep invSqrtS3 a x0 k)
      (orbitVal 3 3 m0 k) ∧
    2 * orbitVal 3 3 m0 k = 3 ^ k * (2 * m0 - 3) + 3 ∧
    2 * orbitVal 3 3 m0 k = 2 * (3 ^ k * (m0 - 2) + 2) + (3 ^ k - 1) :=
  AdicNewtonOptimality.invSqrtS3_popcount_supergain hm0 h0 k

theorem invSqrtS4_eq_S2_double_valuation {a x0 : Int} {m0 : Nat}
    (hm0 : 3 ≤ m0) (h0 : ExactVal2 (1 - a * x0 * x0) m0) (k : Nat) :
    ExactVal2 (1 - a * iterateStep invSqrtS4 a x0 k * iterateStep invSqrtS4 a x0 k)
      (4 ^ k * (m0 - 2) + 2) ∧
    ExactVal2 (1 - a * iterateStep invSqrtS2 a x0 (2 * k) * iterateStep invSqrtS2 a x0 (2 * k))
      (4 ^ k * (m0 - 2) + 2) :=
  AdicNewtonOptimality.invSqrtS4_eq_S2_double_valuation hm0 h0 k

end TwoAdicNewtonPolyOptimalityChallenge
