import MbaHenselBlockJetLifting

namespace MbaHenselBlockJetLiftingChallenge

open MBAHensel

theorem evalMod_coherent (e : MBAExpr) : IsWidthCoherent (fun w x => evalMod w e x) :=
  _root_.MBAHensel.evalMod_coherent e

theorem symDeriv0_sound {w0 s r : Nat} {e : MBAExpr} {d : Bool}
    (h : symDeriv0 w0 s r e = some d) : HasExactDeriv0 e w0 s r d :=
  _root_.MBAHensel.symDeriv0_sound h

theorem quadLiftFromJet_sound {F : Nat → Nat → Nat} {w x : Nat} {J : BlockJet}
    (hw : 1 ≤ w) (hjet : IsAffineBlockJet F w x J) (hr0 : J.r = 0) (hodd : J.a % 2 = 1) :
    let x' := quadLiftFromJet w x J
    x' < 2 ^ (2 * w) ∧
    x' % 2 ^ w = x % 2 ^ w ∧
    F (2 * w) x' = 0 ∧
    (∀ y < 2 ^ (2 * w), y % 2 ^ w = x % 2 ^ w → F (2 * w) y = 0 → y = x') :=
  _root_.MBAHensel.quadLiftFromJet_sound hw hjet hr0 hodd

theorem thm1_constructive_lifts (a b c d : Nat) (hd : d % 2 = 0) :
    ∀ k : Nat,
      let F := fun w' x => evalMod w' (fam1 a b c d) x
      let y0 := liftCore F 0 1 0 k
      let y1 := liftCore F 0 1 1 k
      y0 < 2 ^ (1 + k) ∧ y1 < 2 ^ (1 + k) ∧
      F (1 + k) y0 = 0 ∧ F (1 + k) y1 = 0 ∧ y0 ≠ y1 :=
  _root_.MBAHensel.thm1_constructive_lifts a b c d hd

theorem witness2_one_root {w : Nat} (hw : 3 ≤ w) :
    rootCount (fun w' x => evalMod w' (fam2 H_one) x) w = 1 :=
  _root_.MBAHensel.witness2_one_root hw

theorem witness3_quad_lift_concrete :
    evalMod 4 (fam3 3 11 7) 8 = 0 ∧
    mbaQuadLift (fam3 3 11 7) 4 8 1 = 24 ∧
    evalMod 8 (fam3 3 11 7) 24 = 0 ∧
    mbaQuadLift (fam3 3 11 7) 4 8 2 = 49944 ∧
    evalMod 16 (fam3 3 11 7) 49944 = 0 :=
  _root_.MBAHensel.witness3_quad_lift_concrete

theorem sharpness1_even_mask :
    rootCount (fun w x => evalMod w fam1SharpEvenMask x) 5 = 8 :=
  _root_.MBAHensel.sharpness1_even_mask

theorem sharpness3_below_mask_threshold :
    evalBlockJet 2 (fam3 3 11 7) 0 = none :=
  _root_.MBAHensel.sharpness3_below_mask_threshold

end MbaHenselBlockJetLiftingChallenge
