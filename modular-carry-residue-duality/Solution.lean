/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ModularCarryResidueDuality

/-!
# Verified Solutions (`modular-carry-residue-duality`)
-/

namespace ModularCarryResidueDualityChallenge

open ModularCarryResidueDuality

theorem master_dual_carry_residue_law {m : Nat} (hodd : m % 2 = 1) (L n : Nat) (hn : n < 2 ^ L) :
    (m : Int) * dualInvariant m hodd L n =
      2 * (((n % m : Nat) : Int) + (carryAt m hodd n L : Int)) - (halvingOrbitSum m (n % m) L : Int) :=
  ModularCarryResidueDuality.master_dual_carry_residue_law hodd L n hn

theorem synchronized_trace_divisibility_iff {m : Nat} (hodd : m % 2 = 1) (L n : Nat)
    (hn : n < 2 ^ L) :
    (m ∣ n ↔ carryAt m hodd n L = 0) ∧
    (m ∣ n ↔ ∀ i, i ≤ L → remAt m (by omega) L n i = carryAt m hodd n i) ∧
    (m ∣ n ↔ twoAdicQuot m hodd L n = n / m) :=
  ModularCarryResidueDuality.synchronized_trace_divisibility_iff hodd L n hn

theorem carry_complementarity_law {m : Nat} (hodd : m % 2 = 1) (L n : Nat)
    (hn : n < 2 ^ L) (hndvd : ¬ (m ∣ n)) :
    carriesAdd (n / m) (twoAdicQuot m hodd L (n % m)) + carryDomCount m hodd L n =
      L - 1 - v2 (n % m) :=
  ModularCarryResidueDuality.carry_complementarity_law hodd L n hn hndvd

theorem mersenne_dual_invariant_law {k t n : Nat} (hk : 2 ≤ k) (_ht : 1 ≤ t)
    (hn : n < 2 ^ (t * k)) :
    dualInvariant (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) n =
      if (2 ^ k - 1) ∣ n then 0
      else 2 - (t : Int) * (popcount (n % (2 ^ k - 1)) : Int) :=
  ModularCarryResidueDuality.mersenne_dual_invariant_law hk _ht hn

theorem mersenne_divisibility_threshold_iff {k t n : Nat} (hk : 2 ≤ k) (ht : 3 ≤ t)
    (hn : n < 2 ^ (t * k)) :
    (2 ^ k - 1) ∣ n ↔
      (popcount (twoAdicQuot (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) n) : Int) -
      (popcount (n / (2 ^ k - 1)) : Int) =
      (carryDomCount (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) n : Int) :=
  ModularCarryResidueDuality.mersenne_divisibility_threshold_iff hk ht hn

theorem mersenne_reciprocal_popcount_law {k t r : Nat} (hk : 2 ≤ k) (ht : 1 ≤ t)
    (hr_pos : 0 < r) (hr_lt : r < 2 ^ k - 1) :
    popcount (twoAdicQuot (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) r) =
      t * (k - popcount r) + 1 - v2 r :=
  ModularCarryResidueDuality.mersenne_reciprocal_popcount_law hk ht hr_pos hr_lt

theorem negacyclic_reciprocal_popcount_law {m d t r : Nat} (hodd : m % 2 = 1) (hm3 : 3 ≤ m)
    (hd : 1 ≤ d) (hdvd_m : m ∣ 2 ^ d + 1) (ht : 1 ≤ t) (hr_pos : 0 < r) (hr_lt : r < m) :
    popcount (twoAdicQuot m hodd (2 * t * d) r) = t * d + 1 - v2 r :=
  ModularCarryResidueDuality.negacyclic_reciprocal_popcount_law hodd hm3 hd hdvd_m ht hr_pos hr_lt

theorem fermat_reciprocal_popcount_law {k t r : Nat} (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hr_pos : 0 < r) (hr_lt : r < 2 ^ k + 1) :
    popcount (twoAdicQuot (2 ^ k + 1) (fermat_odd hk) (2 * t * k) r) = t * k + 1 - v2 r :=
  ModularCarryResidueDuality.fermat_reciprocal_popcount_law hk ht hr_pos hr_lt

end ModularCarryResidueDualityChallenge
