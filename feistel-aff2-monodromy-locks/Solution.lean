/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FeistelAff2MonodromyLocks

/-!
# Verified Solutions (`feistel-aff2-monodromy-locks`)
-/

namespace FeistelAff2MonodromyLocksChallenge

open FeistelMonodromy

theorem feistel_universal_2_3_period (f : TriangularRoundFn) :
    ∀ (w : Nat) (s : BitVec w × BitVec w),
      ∃ a b, a ≤ 2 * w ∧ b ≤ w ∧ ExactPeriod f w s (2 ^ a * 3 ^ b) :=
  FeistelMonodromy.feistel_universal_2_3_period f

theorem theorem_I_universal_period12_lock (τ : Nat → Bool) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      (ExactPeriod (fP12 τ) w s 4 ∨ ExactPeriod (fP12 τ) w s 12) ∧
      feistelIter (fP12 τ) w 12 s = s :=
  FeistelMonodromy.theorem_I_universal_period12_lock τ

theorem theorem_IIa_add_one_period6_lock :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      (ExactPeriod fAdd1 w s 1 ∨ ExactPeriod fAdd1 w s 3 ∨ ExactPeriod fAdd1 w s 6) ∧
      hwFeistelIter (fun w R => R + 1#w) w 6 s = s :=
  FeistelMonodromy.theorem_IIa_add_one_period6_lock 

theorem theorem_IIb_sub_one_exponential_escape :
    ∀ (w : Nat), 1 ≤ w →
      hwFeistelIter (fun w R => R - 1#w) w (3 * 2 ^ (w - 1)) (0#w, 0#w) = (0#w, 0#w) ∧
      ∀ q, 0 < q → q < 3 * 2 ^ (w - 1) →
        hwFeistelIter (fun w R => R - 1#w) w q (0#w, 0#w) ≠ (0#w, 0#w) :=
  FeistelMonodromy.theorem_IIb_sub_one_exponential_escape 

theorem theorem_IIIa_lsb_binomial_spectrum :
    (∀ (w : Nat) (s : BitVec w × BitVec w),
      (∃ e, e ≤ w ∧ ExactPeriod fLsb w s (3 ^ e)) ∧
      hwFeistelIter (fun _ R => R &&& (-R)) w (3 ^ w) s = s) ∧
    (∀ (w j : Nat),
      ((allPairs w).filter (isPeriod3Pow w j)).length = binom w j * 3 ^ j) ∧
    (∀ (w : Nat),
      ExactPeriod fLsb w (BitVec.allOnes w, 0#w) (3 ^ w)) :=
  FeistelMonodromy.theorem_IIIa_lsb_binomial_spectrum 

theorem theorem_IIIb_ctz_period_lock (τ : Nat → Bool) (m : Nat)
    (hpre : ∀ j, j < m → τ j = false) (hm : τ m = true) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      feistelIter (fLsbGen τ) w (2 * 3 ^ (m + 1)) s = s :=
  FeistelMonodromy.theorem_IIIb_ctz_period_lock τ m hpre hm

theorem theorem_IV_universal_isoperiodic (τ : Nat → Bool) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      ExactPeriod (fIso τ) w s (2 ^ (w + 1)) :=
  FeistelMonodromy.theorem_IV_universal_isoperiodic τ

end FeistelAff2MonodromyLocksChallenge
