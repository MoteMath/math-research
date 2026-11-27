/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryDefectWeightSpectra.Defs

/-!
# Trusted Challenge Statements (`carry-defect-weight-spectra`)

Statements of exact Hamming-weight spectra of the carry defect (c * x) xor clmul(c, x) between carried integer multiplication and carry-less polynomial multiplication over F_2[x], for all inputs x in Nat: the Mersenne gap law, mod-4 completeness, block additivity, the certificate compiler, and certified multipliers 23, 175 and 211.
-/

namespace CarryDefectWeightSpectraChallenge

open CarryDefectEngine in
/-- Theorem 1 (Complete spectrum): for every multiplier c at least 5 with c mod 4 = 1, every defect weight w is attained. -/
theorem spectrum_one_mod_four (c : Nat) (hc : 5 ≤ c) (hmod : c % 4 = 1) :
    ∀ w : Nat, ∃ x : Nat, defectWeight c x = w := by
  sorry

open CarryDefectEngine in
/-- Theorem 2 (Mersenne zero-defect law): the carry defect for multiplier 2^m - 1 vanishes iff x is m-sparse. -/
theorem mersenne_zero_defect_iff (m : Nat) (hm : 1 ≤ m) (x : Nat) :
    defect (2 ^ m - 1) x = 0 ↔ isMSparse m 0 x = true := by
  sorry

open CarryDefectEngine in
/-- Theorem 3 (Mersenne spectrum): for m at least 2, the attained defect weights are exactly all w different from 1. -/
theorem mersenne_spectrum_classify (m : Nat) (hm : 2 ≤ m) :
    ∀ w : Nat, (∃ x : Nat, defectWeight (2 ^ m - 1) x = w) ↔ w ≠ 1 := by
  sorry

open CarryDefectEngine in
/-- Theorem 4 (Block additivity): defect weights add across sufficiently separated blocks. -/
theorem defectWeight_shift_add (c x y K : Nat) (hx : x < 2 ^ K) (hcx : c * x < 2 ^ K) :
    defectWeight c (x + 2 ^ K * y) = defectWeight c x + defectWeight c y := by
  sorry

open CarryDefectEngine in
/-- Theorem 5 (Certificate soundness): a finite state-table certificate lower-bounds the nonzero defect weight for every input of every width. -/
theorem potentialCert_sound (c depth root : Nat) (tree : BinTree StateEntry)
    (e0 : StateEntry)
    (hTree : checkTree c depth tree tree = true)
    (hRoot : BinTree.lookup depth tree root = some e0)
    (hu0 : e0.u = 0) (hv0 : e0.v = 0) :
    ∀ x : Nat, defect c x ≠ 0 → e0.bVal ≤ defectWeight c x := by
  sorry

open CarryDefectEngine in
/-- Theorem 6 (Multiplier 23): the attained defect weights are exactly all w different from 1. -/
theorem spectrum_23 : ∀ w : Nat, (∃ x : Nat, defectWeight 23 x = w) ↔ w ≠ 1 := by
  sorry

open CarryDefectEngine in
/-- Theorem 7 (Multiplier 175): the attained defect weights are exactly 0 and all w at least 3. -/
theorem spectrum_175 :
    ∀ w : Nat, (∃ x : Nat, defectWeight 175 x = w) ↔ (w = 0 ∨ 3 ≤ w) := by
  sorry

open CarryDefectEngine in
/-- Theorem 8 (Multiplier 211, stealth weight one): every defect weight is attained. -/
theorem spectrum_211 : ∀ w : Nat, ∃ x : Nat, defectWeight 211 x = w := by
  sorry

end CarryDefectWeightSpectraChallenge
