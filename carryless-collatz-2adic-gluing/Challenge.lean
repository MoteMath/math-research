/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarrylessCollatz2adicGluing.Defs

/-!
# Trusted Challenge Statements (`carryless-collatz-2adic-gluing`)

Headline infinite theorems; proofs are supplied in `Solution.lean`.
-/

namespace CarrylessCollatz2adicGluingChallenge

open Dynsil9
open Dynsil9.ShiftFaithful

/-- **Theorem 8 (Exact Syracuse 2-Adic Valuation Preservation & Conjugacy):** -/
theorem Syracuse_conjugacy {T1 T2 : Nat → Nat}
    (h2 : ShiftFaithful T2)
    (hE1 : ∀ n, T1 (2 * n) = n) (hE2 : ∀ n, T2 (2 * n) = n)
    (x v k : Nat) (hk : v + 2 ≤ k)
    (hdvd : 2 ^ v ∣ T1 x) (hndvd : ¬ 2 ^ (v + 1) ∣ T1 x) :
    let y := Phi T1 T2 k x
    (2 ^ v ∣ T2 y) ∧ (¬ 2 ^ (v + 1) ∣ T2 y) ∧
    Phi T1 T2 (k - 1 - v) (T1 x / 2 ^ v) = (T2 y / 2 ^ v) % 2 ^ (k - 1 - v) := by
  sorry

/--
  **Theorem 10 (Exact Finite-to-Infinite Ultrametric Gluing Characterization — Carried Tables):**
  For EVERY `r >= 1` and EVERY `2^r`-branch carried table `tab`:
    `checkAffTable r tab = true ↔ ShiftFaithful (evalAffTable r tab)`.
-/
theorem checkAffTable_iff_shiftFaithful (r : Nat) (hr : 1 ≤ r) (tab : Nat → Nat × Nat) :
    checkAffTable r tab = true ↔ ShiftFaithful (evalAffTable r tab) := by
  sorry

/--
  **Corollary (Carried Collatz `3x+1` and Carryless Collatz `3x ^ 1` are Constructively
  2-Adically Conjugate, Including Exact Syracuse `v_2` Preservation!):**
-/
theorem carried_carryless_3x1_syracuse_conjugate
    (x v k : Nat) (hk : v + 2 ≤ k)
    (hdvd : 2 ^ v ∣ TCarried 3 1 x) (hndvd : ¬ 2 ^ (v + 1) ∣ TCarried 3 1 x) :
    let y := Phi (TCarried 3 1) (TCarryless 3 1) k x
    (2 ^ v ∣ TCarryless 3 1 y) ∧ (¬ 2 ^ (v + 1) ∣ TCarryless 3 1 y) ∧
    Phi (TCarried 3 1) (TCarryless 3 1) (k - 1 - v) (TCarried 3 1 x / 2 ^ v) =
      (TCarryless 3 1 y / 2 ^ v) % 2 ^ (k - 1 - v) := by
  sorry

/--
  **Theorem 13 (Universal Carryless Self-Coding Exact Formula — ALL odd `p > 1`, ALL `k >= 1`):**
  For EVERY odd `p > 1` (let `v = v2 (p - 1) >= 1`) and EVERY width `k`:
    1. For `k <= v`: `Q (TCarryless p 1) k` is the IDENTITY on `Z / 2^k Z`.
    2. Exact closed-form count for ALL `k`:
         `fixedCount (TCarryless p 1) k = 2 ^ (min k (v2 (p - 1)))`.
    3. `0` is the UNIQUE 2-adic fixed point of `Q (TCarryless p 1)` in `Z_2`!
-/
theorem carryless_selfCoding_exact (p : Nat) (hp_odd : p % 2 = 1) (hp_gt : 1 < p) :
    let v := v2 (p - 1)
    (1 ≤ v) ∧
    (∀ k, k ≤ v → ∀ x, Q (TCarryless p 1) k x = x % 2 ^ k) ∧
    (∀ k, fixedCount (TCarryless p 1) k = 2 ^ (min k v)) ∧
    (∀ z : Nat → Nat, (∀ k, z k < 2 ^ k) → (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, Q (TCarryless p 1) k (z k) = z k) → ∀ k, z k = 0) := by
  sorry

/--
  **Theorem 14A (Single-Carry Collapse for Carried Collatz `a ≡ 1 (mod 4)`):**
  For EVERY `a` with `a % 4 = 1` and EVERY `k >= 1`:
    `fixedCount (TCarried a 1) k = 2`,
  and `0` is the UNIQUE 2-adic fixed point of `Q (TCarried a 1)` in `Z_2`!
-/
theorem carried_mod4_eq1_collapse (a : Nat) (ha : a % 4 = 1) :
    (∀ k, 1 ≤ k → fixedCount (TCarried a 1) k = 2) ∧
    (∀ z : Nat → Nat, (∀ k, z k < 2 ^ k) → (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, Q (TCarried a 1) k (z k) = z k) → ∀ k, z k = 0) := by
  sorry

theorem carryless_3x1_unique_nonzero_cycle {L x : Nat} (hL : 1 ≤ L) (hx : 0 < x)
    (hcyc : iter (TCarryless 3 1) L x = x) : x = 1 := by
  sorry

/-- **Theorem 9 (Universal 2-Adic Periodic-Orbit Classification):** -/
theorem periodic_orbit_classification {T : Nat → Nat} (hT : ShiftFaithful T)
    (p : Nat) (hp : 1 ≤ p) :
    (∀ w, w < 2 ^ p →
      (∀ k, perOrbit T p w k < 2 ^ k) ∧
      (∀ k, perOrbit T p w (k + 1) % 2 ^ k = perOrbit T p w k) ∧
      (∀ k, iter T p (perOrbit T p w (k + p)) % 2 ^ k = perOrbit T p w k) ∧
      Q T p (perOrbit T p w p) = w) ∧
    (∀ z : Nat → Nat,
      (∀ k, z k < 2 ^ k) →
      (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, iter T p (z (k + p)) % 2 ^ k = z k) →
      ∀ k, z k = perOrbit T p (Q T p (z p)) k) := by
  sorry

end CarrylessCollatz2adicGluingChallenge
