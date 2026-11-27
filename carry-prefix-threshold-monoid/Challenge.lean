/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryPrefixThresholdMonoid.Defs

/-!
# Trusted Challenge Statements (`carry-prefix-threshold-monoid`)

Statements of the super-critical collapse of multi-input carry maps into the finite aperiodic threshold-step semigroup, its exact cardinality, exact carry-absorption law, exact resonant digit-string counts, and the odd-modulus non-absorption law.
-/

namespace CarryPrefixThresholdMonoidChallenge

open SiliconCarryMonoid in
/-- Theorem 1 (Collapse tree universality): for every prefix tree of super-critical blocks preserving the carry window, the collapsed threshold-step evaluation agrees with the exact floor-division carry action on every in-window carry. -/
theorem collapse_tree_universality (L U : Int) (hLU : L ≤ U) (t : PrefixTree DivElem)
    (hleaves : ∀ d ∈ t.fringe, U - L ≤ (d.mod : Int) ∧ d.Preserves L U)
    (c : Int) (hcL : L ≤ c) (hcU : c ≤ U) :
    (t.eval (collapse L U)).eval c = (t.eval id).act c := by
  sorry

open SiliconCarryMonoid in
/-- Theorem 2 (Collapse sharpness): below the critical modulus there is a block admitting no threshold-step representative. -/
theorem collapse_sharpness_obstruction (L U : Int) (M : Nat) (hMpos : 0 < M)
    (hsub : (M : Int) < U - L) :
    ∃ d : DivElem, d.mod = M ∧
      ¬ ∃ e : ThreshElem, ∀ c : Int, L ≤ c → c ≤ U → e.eval c = d.act c := by
  sorry

open SiliconCarryMonoid SiliconCarryMonoid.ThreshElem in
/-- Theorem 3 (Aperiodicity): every threshold-step element satisfies e^3 = e^2. -/
theorem aperiodic (e : ThreshElem) : e.comp (e.comp e) = e.comp e := by
  sorry

open SiliconCarryMonoid SiliconCarryMonoid.ThreshElem in
/-- Theorem 4 (length of the enumeration list): the hand-built list `enumBounded L N` (N constants followed by (N-1)^2 step elements) has length N^2 - N + 1. This is a statement about the list length only; that the list is duplicate-free and complete for the bounded semigroup is proved in the library, not in this statement. -/
theorem enumBounded_length (L : Int) (N : Nat) (hN : 1 ≤ N) :
    (enumBounded L N).length = N * N - N + 1 := by
  sorry

open SiliconCarryMonoid in
/-- Theorem 5 (Exact carry absorption): a prefix tree of threshold-step elements absorbs the incoming carry iff its fringe is not a resonant chain. -/
theorem tree_exact_carry_absorption (t : PrefixTree ThreshElem) :
    (∃ q, t.eval id = .const q) ↔ ¬ ResonantChain t.fringe := by
  sorry

open SiliconCarryMonoid in
/-- Theorem 6 (Three-input absorption): exact absorption criterion for every prefix tree of three-operand digit sums, unsigned and signed. -/
theorem three_input_exact_absorption (t : PrefixTree Nat) (hds : ∀ s ∈ t.fringe, s ≤ 3) :
    ((∃ q, t.eval enc3Bit = .const q) ↔ BitResonant3 t.fringe = false) ∧
    ((∃ q, t.eval encSigned3Bit = .const q) ↔ BitResonant3 t.fringe = false) := by
  sorry

open SiliconCarryMonoid in
/-- Theorem 7 (Resonant triple count): exact weighted count of resonant three-input digit strings at every width. -/
theorem three_input_resonant_triple_count (w : Nat) (hw : 1 ≤ w) :
    sumWeights3 ((allDigits3 w).filter BitResonant3) = 2 * 4 ^ w := by
  sorry

open SiliconCarryMonoid SiliconCarryMonoid.AffMod in
/-- Theorem 8 (Odd modulus never absorbs): no binary block over an odd modulus is carry-absorbing. -/
theorem odd_modulus_never_absorbs (m : Nat) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (w r : Nat) (hr : r < m) :
    ¬ (∀ c₁ c₂ : Nat, c₁ < m → c₂ < m →
      (baseBlock m (by omega) 2 w r hr).act c₁ = (baseBlock m (by omega) 2 w r hr).act c₂) := by
  sorry

end CarryPrefixThresholdMonoidChallenge
