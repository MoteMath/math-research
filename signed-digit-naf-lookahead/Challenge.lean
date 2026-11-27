/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SignedDigitNafLookahead.Defs

/-!
# Trusted Challenge Statements (`signed-digit-naf-lookahead`)
-/

namespace SignedDigitNafLookaheadChallenge

open SDTransducerEngine

/-- **Theorem 1h (Exact Binary-to-NAF Carry-Absorption Law, `∀ n : Nat`)**:
    For every natural number `n`, `nafRecode (natToSD n)` is the canonical NAF of `n`
    and `popcount n = sdWt (nafRecode (natToSD n)) + nafTotalDefect (natToSD n)`. -/
theorem nat_naf_conservation (n : Nat) :
    sdVal (nafRecode (natToSD n)) = (n : Int) ∧
    IsNAF (nafRecode (natToSD n)) ∧
    popcount n = sdWt (nafRecode (natToSD n)) + nafTotalDefect (natToSD n) := by
  sorry

/-- **Theorem 1d (Exact Zero-Defect Regular Characterization, `∀ D`)**:
    `D` achieves minimal NAF weight iff every step of the 5-state transducer has defect 0. -/
theorem nafRecode_minimal_iff (D : List SD) :
    sdWt (nafRecode D) = sdWt (D.map SD.toInt) ↔ nafTotalDefect D = 0 := by
  sorry

/-- **Theorem 1g (Global Minimality Across ALL Signed-Digit Representations)**:
    For ANY two signed-digit representations `A, D : List SD` of the same integer,
    `sdWt (nafRecode A) ≤ sdWt D`. -/
theorem naf_global_minimal (A D : List SD)
    (hEq : sdVal (A.map SD.toInt) = sdVal (D.map SD.toInt)) :
    sdWt (nafRecode A) ≤ sdWt (D.map SD.toInt) := by
  sorry

/-- **Theorem 2a (Exact Heptagonal Cubic Recurrence for Unsigned Binary Zero-Defect Count, `∀ w`)**:
    `Z(w + 3) + Z(w) = Z(w + 2) + 2 * Z(w + 1)` where `Z(w) = #{x ∈ {0,1}^w : popcount(x) = wt_NAF(x)}`. -/
theorem countZeroDefectBin_recurrence (w : Nat) :
    countZeroDefectBin (w + 3) + countZeroDefectBin w =
      countZeroDefectBin (w + 2) + 2 * countZeroDefectBin (w + 1) := by
  sorry

/-- **Theorem 2b (Exact Cubic Recurrence for Minimal-Weight Signed-Digit Words, `∀ w`)**:
    `M(w + 3) + M(w) = M(w + 2) + 3 * M(w + 1)` where `M(w) = #{D ∈ {-1,0,1}^w : wt(D) = wt_NAF(val(D))}`. -/
theorem countZeroDefectSD_recurrence (w : Nat) :
    countZeroDefectSD (w + 3) + countZeroDefectSD w =
      countZeroDefectSD (w + 2) + 3 * countZeroDefectSD (w + 1) := by
  sorry

/-- **Theorem 3b (Exact Value Preservation & Global Weight Subadditivity of `OL-CFPA`, `∀ A B`)**:
    For ALL balanced signed-digit numbers `A, B : List SD`, the strictly local `O(1)`-depth
    parallel adder `olAdd A B` satisfies:
    1. `sdVal (olAdd A B) = sdVal A + sdVal B`,
    2. `sdWt (olAdd A B) ≤ sdWt A + sdWt B`. -/
theorem olAdd_sound_and_subadditive (A B : List SD) :
    sdVal ((olAdd A B).map SD.toInt) = sdVal (A.map SD.toInt) + sdVal (B.map SD.toInt) ∧
    sdWt ((olAdd A B).map SD.toInt) ≤ sdWt (A.map SD.toInt) + sdWt (B.map SD.toInt) := by
  sorry

/-- **Theorem 4a (Universal Zero-Lookahead Impossibility, `∀ r : Nat`)**:
    For EVERY finite lookback radius `r` and EVERY valid causal carry-free parallel signed-digit
    adder `A : CausalAdder r`, there exists `k` (`1 ≤ k ≤ r + 1`) such that on `1^k + 0`:
    `causalOutWt A.C (List.replicate k 1) ≥ k + 1 > k`.
    Hence NO causal carry-free parallel adder of ANY finite radius can be weight-subadditive! -/
theorem causal_adder_not_subadditive (r : Nat) (A : CausalAdder r) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ r + 1 ∧ k < causalOutWt A.C (List.replicate k 1) := by
  sorry

/-- **Theorem 4b (Explicit Periodic `3/2` Weight-Blowup Family for Chow-Robertson, `∀ m : Nat`)**:
    On `A_m = (1, 1, 0)^m` (weight `2m`) added to `0`, classical radius-1 Chow-Robertson outputs
    `(1, -1, 1)^m` of weight `3m` — an unbounded linear `3/2` weight inflation! -/
theorem chowRobertson_periodic_blowup (m : Nat) :
    causalOutWt crCarry (repeatBlock110 m) = 3 * m ∧
    sdWt (repeatBlock110 m) = 2 * m := by
  sorry

end SignedDigitNafLookaheadChallenge
