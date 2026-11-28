import Defs

namespace SiliconNativeCert

theorem quadForm_pos_of_strictDiagDom {n : Nat}
    (G : Fin n → Fin n → Int) (S : Int)
    (hsym : ∀ i j, G i j = G j i)
    (hdom : IsStrictlyScaledDiagDom G S)
    (v : Fin n → Int) (i0 : Fin n) (hv0 : v i0 ≠ 0) :
    0 < quadForm G v := by
  sorry

theorem psync4_sound (t1 t2 : Transducer4) (invMask : UInt32)
    (hchk : checkPsyncInv4 t1 t2 invMask = true) :
    ∀ inp : List (Bool × Bool), t1.eval inp = t2.eval inp := by
  sorry

theorem universal_carry_decomp :
    ∀ inp : List (Bool × Bool), tAdd.eval inp = tXorPlusTwiceAnd.eval inp := by
  sorry

theorem universal_step_envelope_implies_target
    (f E : Nat → Nat) (C B : Nat)
    (hbound : ∀ w : Nat, 1 ≤ w → f w ≤ E w)
    (henv : ∀ w : Nat, 1 ≤ w → E w ≤ C * sqrtBit w + B) :
    SqrtScaleTarget f := by
  sorry

theorem finite_window_blindness (f : Nat → Nat) (W0 : Nat) :
    ∃ g : Nat → Nat,
      (∀ w : Nat, w ≤ W0 → g w = f w) ∧ ¬ SqrtScaleTarget g := by
  sorry

theorem bounded_envelope_obstruction (f E : Nat → Nat) (B : Nat)
    (hunb : ∀ M : Nat, ∃ w : Nat, 1 ≤ w ∧ M < f w)
    (hbnd : ∀ w : Nat, 1 ≤ w → E w ≤ B) :
    ¬ (∀ w : Nat, 1 ≤ w → f w ≤ E w) := by
  sorry

theorem carryMove_flips_parity {xs ys : List Nat} (h : isCarryMove xs ys) :
    listParity ys = !listParity xs := by
  sorry

theorem oneStepSplit_preserves_valid {N : Nat} {xs ys : List Nat}
    (hvalid : validFactorList N xs = true) (hsplit : isOneStepSplit xs ys) :
    validFactorList N ys = true := by
  sorry

end SiliconNativeCert
