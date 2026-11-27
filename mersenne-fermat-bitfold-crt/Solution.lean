/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MersenneFermatBitfoldCrt

/-!
# Verified Solutions (`mersenne-fermat-bitfold-crt`)
-/

namespace MersenneFermatBitfoldCrtChallenge

open BitFoldEngine

theorem mersenne_exact_threshold (k r n : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hn : n < 2 ^ (r * k) + 2 ^ k - 1) :
    iterFoldM k r n < 2 ^ k ∧ iterFoldM k r n = canonM k n :=
  BitFoldEngine.mersenne_exact_threshold k r n hk hr hn

theorem fermat_exact_envelope (k r : Nat) (x : Int)
    (hxL : -((2 : Int) ^ (r * k)) ≤ x)
    (hxU : x ≤ (2 : Int) ^ (r * k) + (2 : Int) ^ k - 1) :
    -1 ≤ iterFoldF k r x ∧ iterFoldF k r x ≤ (2 : Int) ^ k :=
  BitFoldEngine.fermat_exact_envelope k r x hxL hxU

theorem total_carry_conservation {k : Nat} (hk : 1 ≤ k) {strides : List Nat}
    (hpos : strides.all (fun m => decide (1 ≤ m)) = true) {n : Nat}
    (habsorb : evalNatMersenne k strides n < 2 ^ k) :
    evalNatMersenne k strides n = canonM k n ∧
    carryNatMersenne k strides n = popcount n - popcount (canonM k n) :=
  BitFoldEngine.total_carry_conservation hk hpos habsorb

theorem tower_factorization (d k : Nat) :
    (2 ^ k - 1) * fermatProd d k = towerMod d k :=
  BitFoldEngine.tower_factorization d k

theorem idemM_popcount (d k : Nat) (hk : 1 ≤ k) :
    popcount (idemM d k) = 2 ^ d :=
  BitFoldEngine.idemM_popcount d k hk

theorem idem_partition_of_unity (d k : Nat) (hk : 1 ≤ k) :
    ((2 : Int) ^ (2 ^ d * k) - 1) ∣ ((idemM d k : Int) + sumIdemF d k d - 1) :=
  BitFoldEngine.idem_partition_of_unity d k hk

theorem dyadic_butterfly_exact (d k : Nat) (hk : 1 ≤ k) (x : Int) :
    dyadicButterflyRecon d k (dyadicFoldTree d k x) % ((2 : Int) ^ (2 ^ d * k) - 1) =
    x % ((2 : Int) ^ (2 ^ d * k) - 1) :=
  BitFoldEngine.dyadic_butterfly_exact d k hk x

theorem mersenne_exact_min_depth_dichotomy (d k : Nat) (hd : 2 ≤ d) (hk : 2 ≤ k) (hdB : d ≤ 2 ^ k) :
    (∃ sched, sched.length = d + 2 ∧ sched.all (fun m => decide (1 ≤ m)) = true ∧
      ∀ n, n < 2 ^ (2 ^ d * k) → evalNatMersenne k sched n < 2 ^ k) ∧
    (∀ sched, sched.all (fun m => decide (1 ≤ m)) = true → sched.length ≤ d + 1 →
      ∃ n, n < 2 ^ (2 ^ d * k) ∧ 2 ^ k ≤ evalNatMersenne k sched n) :=
  BitFoldEngine.mersenne_exact_min_depth_dichotomy d k hd hk hdB

end MersenneFermatBitfoldCrtChallenge
