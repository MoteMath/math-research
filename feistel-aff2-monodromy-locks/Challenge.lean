/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FeistelAff2MonodromyLocks.Defs

/-!
# Trusted Challenge Statements (`feistel-aff2-monodromy-locks`)

Headline infinite theorems; proofs are supplied in `Solution.lean`.
-/

namespace FeistelAff2MonodromyLocksChallenge

open FeistelMonodromy

/-- Universal `2^a * 3^b` Period Law: for EVERY triangular round function `f`,
    EVERY bit-width `w`, and EVERY state `s`, its exact minimal period has the form `2^a * 3^b`
    with `a ≤ 2 * w` and `b ≤ w`. -/
theorem feistel_universal_2_3_period (f : TriangularRoundFn) :
    ∀ (w : Nat) (s : BitVec w × BitVec w),
      ∃ a b, a ≤ 2 * w ∧ b ≤ w ∧ ExactPeriod f w s (2 ^ a * 3 ^ b) := by
  sorry

/-- **THEOREM I (Universal Trigger-Independent Period-12 Lock):**
    For EVERY 2-adic trigger `τ : Nat → Bool`, EVERY bit-width `w ≥ 1`, and EVERY state
    `s ∈ (BitVec w)^2`, the Feistel network `(L, R) ↦ (R, L ^^^ fP12(τ)(R))` locks to
    exact period dividing 12: every state has exact minimal period EITHER 4 or 12,
    hence `F^{12}(s) = s` universally for all `w ≥ 1`. -/
theorem theorem_I_universal_period12_lock (τ : Nat → Bool) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      (ExactPeriod (fP12 τ) w s 4 ∨ ExactPeriod (fP12 τ) w s 12) ∧
      feistelIter (fP12 τ) w 12 s = s := by
  sorry

/-- **THEOREM IIa (Exact Period-6 Lock for `R + 1`):**
    For EVERY bit-width `w ≥ 1` and EVERY state `(L, R) ∈ (BitVec w)^2`, the mixed
    XOR/ADD Feistel map `(L, R) ↦ (R, L ^^^ (R + 1))` has exact minimal period in `{1, 3, 6}`,
    and universally satisfies `F^6(L, R) = (L, R)`. -/
theorem theorem_IIa_add_one_period6_lock :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      (ExactPeriod fAdd1 w s 1 ∨ ExactPeriod fAdd1 w s 3 ∨ ExactPeriod fAdd1 w s 6) ∧
      hwFeistelIter (fun w R => R + 1#w) w 6 s = s := by
  sorry

/-- **THEOREM IIb (Sharp Infinite Exponential Escape for `R - 1`):**
    Flipping ONLY `+ 1` to `- 1` in Theorem IIa shatters the constant period-6 lock into
    unbounded exponential growth: for EVERY bit-width `w ≥ 1`, the state `(0#w, 0#w)` under
    `(L, R) ↦ (R, L ^^^ (R - 1))` has EXACT minimal period `3 * 2^(w-1)`. -/
theorem theorem_IIb_sub_one_exponential_escape :
    ∀ (w : Nat), 1 ≤ w →
      hwFeistelIter (fun w R => R - 1#w) w (3 * 2 ^ (w - 1)) (0#w, 0#w) = (0#w, 0#w) ∧
      ∀ q, 0 < q → q < 3 * 2 ^ (w - 1) →
        hwFeistelIter (fun w R => R - 1#w) w q (0#w, 0#w) ≠ (0#w, 0#w) := by
  sorry

/-- **THEOREM IIIa (Exact Binomial Power-of-3 Spectrum for `R &&& (-R)`):**
    For EVERY bit-width `w : Nat` and EVERY exponent `j : Nat`:
    1. Every state `s ∈ (BitVec w)^2` under `(L, R) ↦ (R, L ^^^ (R &&& (-R)))` has exact
       minimal period `3^e` for some `e ≤ w`, hence `F^{3^w}(s) = s` universally.
    2. The EXACT number of states in `(BitVec w)^2` having exact minimal period `3^j` is
       `Nat.choose w j * 3^j` (equivalently, EXACTLY `Nat.choose w j` disjoint cycles of
       length `3^j`, summing to `2^w` cycles in total).
    3. The maximum period `3^w` is attained constructively by `(BitVec.allOnes w, 0#w)`. -/
theorem theorem_IIIa_lsb_binomial_spectrum :
    (∀ (w : Nat) (s : BitVec w × BitVec w),
      (∃ e, e ≤ w ∧ ExactPeriod fLsb w s (3 ^ e)) ∧
      hwFeistelIter (fun _ R => R &&& (-R)) w (3 ^ w) s = s) ∧
    (∀ (w j : Nat),
      ((allPairs w).filter (isPeriod3Pow w j)).length = binom w j * 3 ^ j) ∧
    (∀ (w : Nat),
      ExactPeriod fLsb w (BitVec.allOnes w, 0#w) (3 ^ w)) := by
  sorry

/-- **THEOREM IIIb (Sharp `ctz(τ)` Period-Lock Phase Transition):**
    For EVERY 2-adic trigger `τ : Nat → Bool` with first `true` bit at index `m`
    (`∀ j < m, τ j = false` and `τ m = true`), the exponential `3^w` growth of Theorem IIIa
    SHARPLY COLLAPSES into a constant global period lock at `2 * 3^(m+1)`:
    for EVERY bit-width `w ≥ 1` and EVERY state `s ∈ (BitVec w)^2`,
    `feistelIter (fLsbGen τ) w (2 * 3^(m+1)) s = s`. -/
theorem theorem_IIIb_ctz_period_lock (τ : Nat → Bool) (m : Nat)
    (hpre : ∀ j, j < m → τ j = false) (hm : τ m = true) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      feistelIter (fLsbGen τ) w (2 * 3 ^ (m + 1)) s = s := by
  sorry

/-- **THEOREM IV (Universal Trigger-Independent Isoperiodic `2^(w+1)` Law):**
    For EVERY 2-adic trigger `τ : Nat → Bool`, EVERY bit-width `w ≥ 1`, and EVERY state
    `s ∈ (BitVec w)^2`, the Feistel map `(L, R) ↦ (R, L ^^^ fIso(τ)(R))` has EXACT minimal
    period `2^(w+1)` (partitioning all `4^w` states into `2^(w-1)` equal cycles). -/
theorem theorem_IV_universal_isoperiodic (τ : Nat → Bool) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      ExactPeriod (fIso τ) w s (2 ^ (w + 1)) := by
  sorry

end FeistelAff2MonodromyLocksChallenge
