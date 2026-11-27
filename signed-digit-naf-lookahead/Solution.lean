/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SignedDigitNafLookahead

/-!
# Verified Solutions (`signed-digit-naf-lookahead`)
-/

namespace SignedDigitNafLookaheadChallenge

open SDTransducerEngine

theorem nat_naf_conservation (n : Nat) :
    sdVal (nafRecode (natToSD n)) = (n : Int) ∧
    IsNAF (nafRecode (natToSD n)) ∧
    popcount n = sdWt (nafRecode (natToSD n)) + nafTotalDefect (natToSD n) :=
  SDTransducerEngine.nat_naf_conservation n

theorem nafRecode_minimal_iff (D : List SD) :
    sdWt (nafRecode D) = sdWt (D.map SD.toInt) ↔ nafTotalDefect D = 0 :=
  SDTransducerEngine.nafRecode_minimal_iff D

theorem naf_global_minimal (A D : List SD)
    (hEq : sdVal (A.map SD.toInt) = sdVal (D.map SD.toInt)) :
    sdWt (nafRecode A) ≤ sdWt (D.map SD.toInt) :=
  SDTransducerEngine.naf_global_minimal A D hEq

theorem countZeroDefectBin_recurrence (w : Nat) :
    countZeroDefectBin (w + 3) + countZeroDefectBin w =
      countZeroDefectBin (w + 2) + 2 * countZeroDefectBin (w + 1) :=
  SDTransducerEngine.countZeroDefectBin_recurrence w

theorem countZeroDefectSD_recurrence (w : Nat) :
    countZeroDefectSD (w + 3) + countZeroDefectSD w =
      countZeroDefectSD (w + 2) + 3 * countZeroDefectSD (w + 1) :=
  SDTransducerEngine.countZeroDefectSD_recurrence w

theorem olAdd_sound_and_subadditive (A B : List SD) :
    sdVal ((olAdd A B).map SD.toInt) = sdVal (A.map SD.toInt) + sdVal (B.map SD.toInt) ∧
    sdWt ((olAdd A B).map SD.toInt) ≤ sdWt (A.map SD.toInt) + sdWt (B.map SD.toInt) :=
  SDTransducerEngine.olAdd_sound_and_subadditive A B

theorem causal_adder_not_subadditive (r : Nat) (A : CausalAdder r) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ r + 1 ∧ k < causalOutWt A.C (List.replicate k 1) :=
  SDTransducerEngine.causal_adder_not_subadditive r A

theorem chowRobertson_periodic_blowup (m : Nat) :
    causalOutWt crCarry (repeatBlock110 m) = 3 * m ∧
    sdWt (repeatBlock110 m) = 2 * m :=
  SDTransducerEngine.chowRobertson_periodic_blowup m

end SignedDigitNafLookaheadChallenge
