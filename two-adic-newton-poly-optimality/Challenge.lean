/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoAdicNewtonPolyOptimality.Defs

/-!
# Trusted Challenge Statements (`two-adic-newton-poly-optimality`)
-/

namespace TwoAdicNewtonPolyOptimalityChallenge

open AdicNewtonOptimality

/-- Legendre: `v_2(n!) = n - popcount n` exactly. -/
theorem fact_exactVal2 (n : Nat) : ExactVal2 (fact n : Int) (n - popcount n) := by
  sorry

/-- A degree `<= D` integer polynomial inverts every odd `a` modulo `2^N` iff `N <= 2(D+1) - popcount(D+1)`. -/
theorem exact_2adic_poly_reciprocal_optimality (D N : Nat) :
    (∃ p : List Int, p.length ≤ D + 1 ∧ ∀ a : Int, OddInt a → DivPow2 (1 - a * evalPoly p a) N) ↔
      N ≤ 2 * (D + 1) - popcount (D + 1) := by
  sorry

/-- The case `D + 1 = 2^k`: optimal precision is exactly `2^(k+1) - 1` bits. -/
theorem exact_2adic_poly_optimality_pow2_sub_one (k N : Nat) :
    (∃ p : List Int, p.length ≤ 2 ^ k ∧ ∀ a : Int, OddInt a → DivPow2 (1 - a * evalPoly p a) N) ↔
      N ≤ 2 ^ (k + 1) - 1 := by
  sorry

/-- Every integer straight-line circuit of multiplicative depth `k >= 1` computing an inverse mod `2^N` has `N <= 2^(k+1)`. -/
theorem circuit_mulDepth_optimality_pos {C : PolyCircuit} {N : Nat}
    (hk : 1 ≤ mulDepth C)
    (hmod : ∀ a : Int, OddInt a → DivPow2 (1 - a * evalCircuit C a) N) :
    N ≤ 2 ^ (mulDepth C + 1) := by
  sorry

/-- Closed-form two-sided minimal-step optimality for any affine contraction certificate. -/
theorem cert_minimal_step_optimality_closed (C : AffineContractionCert)
    (seed : Int → Int) (m0 : Nat) (hm0 : C.mCrit ≤ m0)
    (hseed_all : ∀ a, C.valid a → DivPow2 (C.res a (seed a)) m0)
    (aStar : Int) (haStar : C.valid aStar) (hsharp : ExactVal2 (C.res aStar (seed aStar)) m0)
    (k N : Nat) :
    (∀ a, C.valid a → DivPow2 (C.res a (iterateStep C.step a (seed a) k)) N) ↔
      (C.d - 1) * N ≤ C.d ^ k * ((C.d - 1) * m0 - C.s) + C.s := by
  sorry

/-- Exact iff precision law for the order-`d` reciprocal iteration seeded by the Dumas seed: `N <= 5 d^k`. -/
theorem recip_minimal_step_dumas {d : Nat} (hd : 2 ≤ d) (k N : Nat) :
    (∀ a : Nat, a % 2 = 1 →
      DivPow2 (1 - (a : Int) * iterateStep (recipStep d) (a : Int) (dumasSeedNat a : Int) k) N) ↔
      N ≤ 5 * d ^ k := by
  sorry

/-- Cubic inverse-square-root step gain `(3^k - 1)/2` bits beyond the quadratic baseline. -/
theorem invSqrtS3_popcount_supergain {a x0 : Int} {m0 : Nat}
    (hm0 : 4 ≤ m0) (h0 : ExactVal2 (1 - a * x0 * x0) m0) (k : Nat) :
    ExactVal2 (1 - a * iterateStep invSqrtS3 a x0 k * iterateStep invSqrtS3 a x0 k)
      (orbitVal 3 3 m0 k) ∧
    2 * orbitVal 3 3 m0 k = 3 ^ k * (2 * m0 - 3) + 3 ∧
    2 * orbitVal 3 3 m0 k = 2 * (3 ^ k * (m0 - 2) + 2) + (3 ^ k - 1) := by
  sorry

/-- The quartic inverse-square-root step equals two quadratic steps in valuation. -/
theorem invSqrtS4_eq_S2_double_valuation {a x0 : Int} {m0 : Nat}
    (hm0 : 3 ≤ m0) (h0 : ExactVal2 (1 - a * x0 * x0) m0) (k : Nat) :
    ExactVal2 (1 - a * iterateStep invSqrtS4 a x0 k * iterateStep invSqrtS4 a x0 k)
      (4 ^ k * (m0 - 2) + 2) ∧
    ExactVal2 (1 - a * iterateStep invSqrtS2 a x0 (2 * k) * iterateStep invSqrtS2 a x0 (2 * k))
      (4 ^ k * (m0 - 2) + 2) := by
  sorry

end TwoAdicNewtonPolyOptimalityChallenge
