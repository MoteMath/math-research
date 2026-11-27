/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryDefectWeightSpectra

/-!
# Verified Solutions (`carry-defect-weight-spectra`)
-/

namespace CarryDefectWeightSpectraChallenge

open CarryDefectEngine in
/-- Theorem 1 (Complete spectrum): for every multiplier c at least 5 with c mod 4 = 1, every defect weight w is attained. -/
theorem spectrum_one_mod_four (c : Nat) (hc : 5 ≤ c) (hmod : c % 4 = 1) :
    ∀ w : Nat, ∃ x : Nat, defectWeight c x = w :=
  CarryDefectEngine.spectrum_one_mod_four c hc hmod

open CarryDefectEngine in
/-- Theorem 2 (Mersenne zero-defect law): the carry defect for multiplier 2^m - 1 vanishes iff x is m-sparse. -/
theorem mersenne_zero_defect_iff (m : Nat) (hm : 1 ≤ m) (x : Nat) :
    defect (2 ^ m - 1) x = 0 ↔ isMSparse m 0 x = true :=
  CarryDefectEngine.mersenne_zero_defect_iff m hm x

open CarryDefectEngine in
/-- Theorem 3 (Mersenne spectrum): for m at least 2, the attained defect weights are exactly all w different from 1. -/
theorem mersenne_spectrum_classify (m : Nat) (hm : 2 ≤ m) :
    ∀ w : Nat, (∃ x : Nat, defectWeight (2 ^ m - 1) x = w) ↔ w ≠ 1 :=
  CarryDefectEngine.mersenne_spectrum_classify m hm

open CarryDefectEngine in
/-- Theorem 4 (Block additivity): defect weights add across sufficiently separated blocks. -/
theorem defectWeight_shift_add (c x y K : Nat) (hx : x < 2 ^ K) (hcx : c * x < 2 ^ K) :
    defectWeight c (x + 2 ^ K * y) = defectWeight c x + defectWeight c y :=
  CarryDefectEngine.defectWeight_shift_add c x y K hx hcx

open CarryDefectEngine in
/-- Theorem 5 (Certificate soundness): a finite state-table certificate lower-bounds the nonzero defect weight for every input of every width. -/
theorem potentialCert_sound (c depth root : Nat) (tree : BinTree StateEntry)
    (e0 : StateEntry)
    (hTree : checkTree c depth tree tree = true)
    (hRoot : BinTree.lookup depth tree root = some e0)
    (hu0 : e0.u = 0) (hv0 : e0.v = 0) :
    ∀ x : Nat, defect c x ≠ 0 → e0.bVal ≤ defectWeight c x :=
  CarryDefectEngine.PotentialCert.sound c depth root tree e0 hTree hRoot hu0 hv0

open CarryDefectEngine in
/-- Theorem 6 (Multiplier 23): the attained defect weights are exactly all w different from 1. -/
theorem spectrum_23 : ∀ w : Nat, (∃ x : Nat, defectWeight 23 x = w) ↔ w ≠ 1 :=
  CarryDefectEngine.spectrum_23

open CarryDefectEngine in
/-- Theorem 7 (Multiplier 175): the attained defect weights are exactly 0 and all w at least 3. -/
theorem spectrum_175 :
    ∀ w : Nat, (∃ x : Nat, defectWeight 175 x = w) ↔ (w = 0 ∨ 3 ≤ w) :=
  CarryDefectEngine.spectrum_175

open CarryDefectEngine in
/-- Theorem 8 (Multiplier 211, stealth weight one): every defect weight is attained. -/
theorem spectrum_211 : ∀ w : Nat, ∃ x : Nat, defectWeight 211 x = w :=
  CarryDefectEngine.spectrum_211

end CarryDefectWeightSpectraChallenge
