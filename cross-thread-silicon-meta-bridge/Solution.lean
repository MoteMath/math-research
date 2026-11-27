import CrossThreadSiliconMetaBridge

namespace CrossThreadSiliconMetaBridgeChallenge

open SiliconMetaBridge

theorem sumPow2_eq_sumRange (w : Nat) (f : Nat → Int) :
    sumPow2 w f = sumRange (2 ^ w) f :=
  _root_.SiliconMetaBridge.sumPow2_eq_sumRange w f

theorem xorConv_quadForm_eq_wht (w : Nat) (f v : Nat → Int) :
    (2 ^ w : Int) * sumPow2 w (fun x => sumPow2 w (fun y => v x * f (x ^^^ y) * v y)) =
    sumPow2 w (fun xi => whtVec w f xi * (whtVec w v xi * whtVec w v xi)) :=
  _root_.SiliconMetaBridge.xorConv_quadForm_eq_wht w f v

theorem prefixTree_walsh_bandlimited (t : PrefixTree) :
    ∀ w xi : Nat, t.depth ≤ w → 2 ^ t.depth ≤ xi → xi < 2 ^ w →
      whtVec w t.eval xi = 0 :=
  _root_.SiliconMetaBridge.prefixTree_walsh_bandlimited t

theorem transferRec2_sound {D : Nat} (l : Vec D) (E : Mat D D) (r : Vec D)
    (cert : TransferRec2Cert) (hc : checkTransferRec2 E cert = true) :
    ∀ w : Nat,
      dot (vecMat l (matPow E (w + 2))) r =
      cert.c1 * dot (vecMat l (matPow E (w + 1))) r + cert.c0 * dot (vecMat l (matPow E w)) r :=
  _root_.SiliconMetaBridge.transferRec2_sound l E r cert hc

theorem rawCarry_c1_indefinite_all_w (w : Nat) (hw : 1 ≤ w) :
    let v : Nat → Int := fun x => sgn (x % 2 == 1)
    sumPow2 w (fun x => sumPow2 w (fun y => v x * rawCarryFiber true w (x ^^^ y) * v y)) =
    -(8 ^ w : Int) :=
  _root_.SiliconMetaBridge.rawCarry_c1_indefinite_all_w w hw

theorem thueMorse_inc_mod4_all_w (w : Nat) (hw : 2 ≤ w) :
    (4 : Int) ∣ sumPow2 w (fun x => thueMorseW w x * thueMorseW w ((x + 1) % 2 ^ w)) :=
  _root_.SiliconMetaBridge.thueMorse_inc_mod4_all_w w hw

theorem demoAdicTree_sharp_at_freq4 :
    whtVec 3 demoAdicTree.eval 4 = 12 :=
  _root_.SiliconMetaBridge.demoAdicTree_sharp_at_freq4

theorem mutation_reject_modSubspace :
    checkModSubspace
      (kronVec (kronVec thueMorseMPS.left (ofSliceTFunc incTFunc).left) thueMorseMPS.left)
      (corrTransfer thueMorseMPS (ofSliceTFunc incTFunc) thueMorseMPS)
      (kronVec (kronVec thueMorseMPS.right (ofSliceTFunc incTFunc).right) thueMorseMPS.right)
      badTmMod8Cert = false :=
  _root_.SiliconMetaBridge.mutation_reject_modSubspace

end CrossThreadSiliconMetaBridgeChallenge
