/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MersenneFermatBitfoldCrt.Defs

/-!
# Trusted Challenge Statements (`mersenne-fermat-bitfold-crt`)
-/

namespace MersenneFermatBitfoldCrtChallenge

open BitFoldEngine

/-- Exact Mersenne carry-absorption threshold `2^(rk) + 2^k - 1`. -/
theorem mersenne_exact_threshold (k r n : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hn : n < 2 ^ (r * k) + 2 ^ k - 1) :
    iterFoldM k r n < 2 ^ k ∧ iterFoldM k r n = canonM k n := by
  sorry

/-- Exact signed Fermat envelope for folding modulo `2^k + 1`. -/
theorem fermat_exact_envelope (k r : Nat) (x : Int)
    (hxL : -((2 : Int) ^ (r * k)) ≤ x)
    (hxU : x ≤ (2 : Int) ^ (r * k) + (2 : Int) ^ k - 1) :
    -1 ≤ iterFoldF k r x ∧ iterFoldF k r x ≤ (2 : Int) ^ k := by
  sorry

/-- Schedule-invariant total carry conservation law. -/
theorem total_carry_conservation {k : Nat} (hk : 1 ≤ k) {strides : List Nat}
    (hpos : strides.all (fun m => decide (1 ≤ m)) = true) {n : Nat}
    (habsorb : evalNatMersenne k strides n < 2 ^ k) :
    evalNatMersenne k strides n = canonM k n ∧
    carryNatMersenne k strides n = popcount n - popcount (canonM k n) := by
  sorry

/-- Tower factorization `(2^k - 1) * fermatProd d k = towerMod d k`. -/
theorem tower_factorization (d k : Nat) :
    (2 ^ k - 1) * fermatProd d k = towerMod d k := by
  sorry

/-- The Mersenne Rademacher idempotent has popcount `2^d`. -/
theorem idemM_popcount (d k : Nat) (hk : 1 ≤ k) :
    popcount (idemM d k) = 2 ^ d := by
  sorry

/-- Mersenne and Fermat idempotents form a partition of unity modulo `2^(2^d k) - 1`. -/
theorem idem_partition_of_unity (d k : Nat) (hk : 1 ≤ k) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ ((idemM d k : Int) + sumIdemF d k d - 1) := by
  sorry

/-- The dyadic bit-folding butterfly reconstructs `x` modulo `2^(2^d k) - 1` exactly. -/
theorem dyadic_butterfly_exact (d k : Nat) (hk : 1 ≤ k) (x : Int) :
    dyadicButterflyRecon d k (dyadicFoldTree d k x) % ((2 : Int) ^ (2 ^ d * k) - 1) =
    x % ((2 : Int) ^ (2 ^ d * k) - 1) := by
  sorry

/-- Exact minimal folding depth: `d + 2` rounds suffice and `d + 1` never do. -/
theorem mersenne_exact_min_depth_dichotomy (d k : Nat) (hd : 2 ≤ d) (hk : 2 ≤ k) (hdB : d ≤ 2 ^ k) :
    (∃ sched, sched.length = d + 2 ∧ sched.all (fun m => decide (1 ≤ m)) = true ∧
      ∀ n, n < 2 ^ (2 ^ d * k) → evalNatMersenne k sched n < 2 ^ k) ∧
    (∀ sched, sched.all (fun m => decide (1 ≤ m)) = true → sched.length ≤ d + 1 →
      ∃ n, n < 2 ^ (2 ^ d * k) ∧ 2 ^ k ≤ evalNatMersenne k sched n) := by
  sorry

end MersenneFermatBitfoldCrtChallenge
