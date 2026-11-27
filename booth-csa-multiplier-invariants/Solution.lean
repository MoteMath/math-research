import BoothCsaMultiplierInvariants

namespace BoothCsaMultiplierInvariantsChallenge

open SiliconBoothCSA

theorem csa3to2_exact_mod (W a b c : Nat) :
    (csaSum W a b c + csaCarry W a b c) % 2 ^ W = (a + b + c) % 2 ^ W :=
  _root_.SiliconBoothCSA.csa3to2_exact_mod W a b c

theorem lift_all_widths {g : Nat} (G : GuardNormalizerSpec g)
    {W : Nat} (hWg : g ≤ W) (S C : Nat) {V : Int}
    (hV_lo : -p2 (W - 1) ≤ V) (hV_hi : V < p2 (W - 1))
    (hsum : (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W)
    (hallow : G.allowed (((S + C) % 2 ^ W) / 2 ^ (W - g))) :
    let (S', C') := applyTopGuard g W G.norm S C
    signedVal W S' + signedVal W C' = V :=
  _root_.SiliconBoothCSA.GuardNormalizerSpec.lift_all_widths G hWg S C hV_lo hV_hi hsum hallow

theorem zeroCarryTop_exact {g W : Nat} (hg : 2 ≤ g) (hWg : g ≤ W) (S C : Nat) {V : Int}
    (hV_lo : -p2 (W - 1) + p2 (W - g) ≤ V)
    (hV_hi : V < p2 (W - 1))
    (hsum : (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W) :
    let (S', C') := applyTopGuard g W (zeroCarryTopNorm g) S C
    signedVal W S' + signedVal W C' = V ∧ C' < 2 ^ (W - g) :=
  _root_.SiliconBoothCSA.zeroCarryTop_exact hg hWg S C hV_lo hV_hi hsum

theorem unnormalized_csa_rshift_fails {W : Nat} (hW : 3 ≤ W) :
    let S := 2 ^ (W - 1)
    let C := 2 ^ (W - 1)
    signedVal W (S + C) = 0 ∧
    (signedVal W S / 2) + (signedVal W C / 2) + (((S % 2 + C % 2) / 2 : Nat) : Int) =
      -p2 (W - 1) :=
  _root_.SiliconBoothCSA.unnormalized_csa_rshift_fails hW

theorem sec_cancellation_exact {k m : Nat} (hk : 1 ≤ k) (hm : 1 ≤ m) (W : Nat) (s : Nat → Fin 2) :
    p2 W * radixSum (2 ^ k) (fun j => secTerm k (decide (0 < j)) (s j).val) m +
    p2 W * radixSum (2 ^ k) (fun j => ((s j).val : Int)) m =
      p2 (W + k * m) :=
  _root_.SiliconBoothCSA.sec_cancellation_exact hk hm W s

theorem radix4_booth_tree_exact {w m : Nat} (hw : 1 ≤ w) (hm : 1 ≤ m) (x_u y_u : Nat) :
    boothTreeSum w m x_u y_u =
      signedVal w x_u * signedVal (2 * m) y_u + p2 (w + 1 + 2 * m) ∧
    boothTreeSum w m x_u y_u % p2 (w + 2 * m) =
      (signedVal w x_u * signedVal (2 * m) y_u) % p2 (w + 2 * m) :=
  _root_.SiliconBoothCSA.radix4_booth_tree_exact hw hm x_u y_u

theorem booth_acc_endpoints_tight {k w : Nat} (hk : 1 ≤ k) (hw : 1 ≤ w) :
    (signedVal w (2 ^ (w - 1)) * signedVal (k * 1) (2 ^ (k - 1))) / p2 (k * 0) = p2 (w + k - 2) ∧
    (signedVal w (2 ^ (w - 1)) * signedVal (k * (w + 1)) (2 ^ (k * (w + 1) - 1) - 1)) /
      p2 (k * w) = -p2 (w + k - 2) :=
  _root_.SiliconBoothCSA.booth_acc_endpoints_tight hk hw

theorem badGuardCert_g2_rejected : badGuardCert_g2_cutArc.check = false :=
  _root_.SiliconBoothCSA.badGuardCert_g2_rejected

end BoothCsaMultiplierInvariantsChallenge
