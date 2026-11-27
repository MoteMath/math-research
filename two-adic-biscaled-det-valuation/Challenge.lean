/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoAdicBiscaledDetValuation.Defs

/-!
# Trusted Challenge Statements (`two-adic-biscaled-det-valuation`)

Statements of the biscaled elimination theorem for the exact 2-adic valuation of a determinant, its perturbation stability, the Mobius transform of popcount-AND matrices, the supercritical and two critical exact valuation formulas for the full hybrid matrix family, the n = 1 jump, and the infinite breakdown line.
-/

namespace TwoAdicBiscaledDetValuationChallenge

open SpecMat12 in
/-- Theorem 1 (Biscaled elimination engine): if unimodular U, V factor M into biscaled form 2^(a i + b j) times an odd-outside matrix Omega with invertible mod-2 leading block, then v2(det M) = sum (a i + b i). -/
theorem v2_det_biscaled_elimination_engine
    {n k : Nat} (hk : k ≤ n) (M U V Ω : Mat n) (a b : Fin n → Nat)
    (hU : det U = 1) (hV : det V = 1)
    (hfac : matMul (matMul U M) V = biScale a b Ω)
    (houtside : ∀ (i j : Fin n), k ≤ i.val → Ω i j % 2 = if i = j then 1 else 0)
    (R : Mat k)
    (hinv : ∀ (i j : Fin k),
      matMul R (fun r c => Ω ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) i j % 2 = idMat k i j) :
    HasV2 (det M) (sumNat (fun i => a i + b i)) := by
  sorry

open SpecMat12 in
/-- Theorem 2 (Perturbation stability): adding a perturbation divisible by one extra power of 2 in the biscaled frame leaves v2(det) unchanged. -/
theorem v2_det_perturbation_stability
    {n k : Nat} (hk : k ≤ n) (M Δ U V Ω E : Mat n) (a b : Fin n → Nat)
    (hU : det U = 1) (hV : det V = 1)
    (hfacM : matMul (matMul U M) V = biScale a b Ω)
    (hfacΔ : matMul (matMul U Δ) V = fun i j => (2 : Int) ^ (a i + b j + 1) * E i j)
    (houtside : ∀ (i j : Fin n), k ≤ i.val → Ω i j % 2 = if i = j then 1 else 0)
    (R : Mat k)
    (hinv : ∀ (i j : Fin k),
      matMul R (fun r c => Ω ⟨r.val, by omega⟩ ⟨c.val, by omega⟩) i j % 2 = idMat k i j) :
    HasV2 (det (matAdd M Δ)) (sumNat (fun i => a i + b i)) := by
  sorry

open SpecMat12 in
/-- Theorem 3 (Mobius of popcount-AND): the Mobius transform of q^popcount(u AND v) is diagonal with entries (q - 1)^popcount(i). -/
theorem mob2_pop_and (q : Int) (i j : Nat) :
    mob2 (fun u v => q ^ pop (u &&& v)) i j = if i = j then (q - 1) ^ pop i else 0 := by
  sorry

open SpecMat12 in
/-- Theorem 4 (Supercritical regime): for parameters 2^r u_a, 1 + 2^e u_q with r >= 2e - 1, v2(det) = e * popSum(n) - e for every n >= 2. -/
theorem theorem_1A_supercritical (e r n : Nat) (he : 1 ≤ e) (hr2 : 2 ≤ r) (hr : 2 * e - 1 ≤ r)
    (hn : 2 ≤ n) (u_a u_q lam tc td : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    HasV2 (det (fullHybridMat ((2 : Int) ^ r * u_a) (1 + (2 : Int) ^ e * u_q)
      lam (1 + (2 : Int) ^ e * tc) (1 + (2 : Int) ^ e * td) n)) (e * popSum n - e) := by
  sorry

open SpecMat12 in
/-- Theorem 5 (Critical regime I): at e = 1, v2(det) = popSum(n) - 1 for every n >= 2. -/
theorem theorem_1B_critical_I (n : Nat) (hn : 2 ≤ n)
    (u_a u_q lam tc td : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    HasV2 (det (fullHybridMat (2 * u_a) (1 + 2 * u_q) lam (1 + 2 * tc) (1 + 2 * td) n))
      (popSum n - 1) := by
  sorry

open SpecMat12 in
/-- Theorem 6 (Critical regime II): at e = 2 with 4 u_a, v2(det) = 2 * popSum(n) - 2 for every n >= 2. -/
theorem theorem_1C_critical_II (n : Nat) (hn : 2 ≤ n)
    (u_a u_q lam tc td : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    HasV2 (det (fullHybridMat (4 * u_a) (1 + 4 * u_q) lam (1 + 4 * tc) (1 + 4 * td) n))
      (2 * popSum n - 2) := by
  sorry

open SpecMat12 in
/-- Theorem 7 (n = 1 jump): for the 1 x 1 hybrid matrix, v2(det) = 1 for all a, q. -/
theorem theorem_n1_jump (a q : Int) : HasV2 (det (hybridMat a q 1)) 1 := by
  sorry

open SpecMat12 in
/-- Theorem 8 (Infinite breakdown line): for every e >= 3 the subcritical parameter 2^(2e - 2) u_a at n = 4 does not have valuation e * popSum(4) - e. -/
theorem sharpness_S3_infinite_breakdown_line (e : Nat) (he : 3 ≤ e)
    (u_a u_q : Int) (hua : u_a % 2 = 1) (huq : u_q % 2 = 1) :
    ¬ HasV2 (det (hybridMat ((2 : Int) ^ (2 * e - 2) * u_a) (1 + (2 : Int) ^ e * u_q) 4))
      (e * popSum 4 - e) := by
  sorry

end TwoAdicBiscaledDetValuationChallenge
