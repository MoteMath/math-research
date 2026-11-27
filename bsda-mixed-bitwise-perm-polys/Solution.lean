/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BsdaMixedBitwisePermPolys

/-!
# Verified Solutions (`bsda-mixed-bitwise-perm-polys`)
-/

namespace BsdaMixedBitwisePermPolysChallenge

open MixedPermEngine

theorem bijective_iff_forall_bitDeriv {f : ∀ w, BitVec w → BitVec w} (hf : Coherent f) (w : Nat) :
    Bijective (f w) ↔ ∀ (i : Nat), i < w → ∀ x : BitVec i, bitDeriv f i x = true :=
  MixedPermEngine.bijective_iff_forall_bitDeriv hf w

-- ----------------------------------------------------------------------------
-- 4C. Crown-Jewel Three-Way BSDA Engine Theorems (Exact ↔ Lifting ∀ w ≥ 2)
-- ----------------------------------------------------------------------------

/-- **Engine Theorem 1 (Exact Necessary & Sufficient BSDA Decision Theorem):**
    For any `MixedExpr` compiling to `D`, `e` is bijective on `BitVec w` for ALL `w ≥ 2`
    IF AND ONLY IF the pure-data finite-state checker `D.checkBijective = true`. -/
theorem bsda_bijective_iff (e : MixedExpr) (D : DerivAuto) (h : compileBSDA e = some D) :
    (∀ w, 2 ≤ w → Bijective (e.eval w)) ↔ D.checkBijective = true :=
  MixedPermEngine.bsda_bijective_iff e D h

theorem bsda_finite_slice_iff (e : MixedExpr) (D : DerivAuto) (h : compileBSDA e = some D) :
    (∀ w, 2 ≤ w → Bijective (e.eval w)) ↔ Bijective (e.eval D.horizonW) :=
  MixedPermEngine.bsda_finite_slice_iff e D h

theorem maskedPoly_bijective_iff (a0 : Int) (ts : List MaskedTerm) :
    (∀ w, 2 ≤ w → Bijective (evalMaskedPoly w a0 ts)) ↔
      (xorFold termBit0Deriv ts = true ∧
       (∀ i, 1 ≤ i → xorFold (fun t => termLinDeriv t i) ts = true) ∧
       (∀ i, 1 ≤ i → xorFold (fun t => termOddDeriv t i) ts = false)) :=
  MixedPermEngine.maskedPoly_bijective_iff a0 ts

theorem rivest_classical_mod4_iff (a0 : Int) (cs : List Int) :
    (∀ w, 2 ≤ w → Bijective (evalMaskedPoly w a0 (classicalTerms cs 1))) ↔
      Bijective (evalMaskedPoly 2 a0 (classicalTerms cs 1)) :=
  MixedPermEngine.rivest_classical_mod4_iff a0 cs

theorem carryPair_bijective_iff (c d : Int) (w : Nat) :
    Bijective ((carryPairExpr c d).eval w) ↔ BitVec.ofInt w c = BitVec.ofInt w d :=
  MixedPermEngine.carryPair_bijective_iff c d w

theorem addXorCancel_bijective_iff {f g : ∀ w, BitVec w → BitVec w}
    (hf : Coherent f) (hg : Coherent g) (w : Nat) :
    Bijective (fun x : BitVec w => (f w x + g w x) ^^^ g w x) ↔ Bijective (f w) :=
  MixedPermEngine.addXorCancel_bijective_iff hf hg w

theorem klimovShamir_general_iff {g : ∀ w, BitVec w → BitVec w} (hg : Coherent g) (c : Int) :
    (∀ w, 2 ≤ w → Bijective (fun x : BitVec w => x + ((g w x * g w x) ||| BitVec.ofInt w c))) ↔
      (intBit c 0 = true ∨ bit0Val g false = bit0Val g true) :=
  MixedPermEngine.klimovShamir_general_iff hg c

end BsdaMixedBitwisePermPolysChallenge
