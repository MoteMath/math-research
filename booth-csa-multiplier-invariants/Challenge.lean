import BoothCsaMultiplierInvariants.Defs

namespace BoothCsaMultiplierInvariantsChallenge

open SiliconBoothCSA

theorem csa3to2_exact_mod (W a b c : Nat) :
    (csaSum W a b c + csaCarry W a b c) % 2 ^ W = (a + b + c) % 2 ^ W := by
  sorry

/-- INFINITE-WIDTH LIFTING THEOREM (Mechanism II): Any finite top-`g`-bit guard specification lifts to EXACT unwrapped integer conservation `signedVal W S' + signedVal W C' = V` for ALL bit-widths `W ≥ g` and ALL pairs `(S, C)` whose modular sum lies in the allowed slabs! -/
theorem lift_all_widths {g : Nat} (G : GuardNormalizerSpec g)
    {W : Nat} (hWg : g ≤ W) (S C : Nat) {V : Int}
    (hV_lo : -p2 (W - 1) ≤ V) (hV_hi : V < p2 (W - 1))
    (hsum : (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W)
    (hallow : G.allowed (((S + C) % 2 ^ W) / 2 ^ (W - g))) :
    let (S', C') := applyTopGuard g W G.norm S C
    signedVal W S' + signedVal W C' = V := by
  sorry

/-- THEOREM 1 (Exact g-Bit Zero-Carry-Top Normalizer, ∀ g ≥ 2, ∀ W ≥ g): For ANY `g ≥ 2`, ANY width `W ≥ g`, and ANY Carry-Save pair `(S, C)` whose modular sum `V` lies in the asymmetric range `[-2^(W-1) + 2^(W-g), 2^(W-1) - 1]`: 1. `signedVal W S' + signedVal W C' = V` EXACTLY IN `Int` (zero wraparound!) 2. `C' < 2^(W - g)` (top `g` bits of `C'` are identically zero, so `C'` is non-negative!). -/
theorem zeroCarryTop_exact {g W : Nat} (hg : 2 ≤ g) (hWg : g ≤ W) (S C : Nat) {V : Int}
    (hV_lo : -p2 (W - 1) + p2 (W - g) ≤ V)
    (hV_hi : V < p2 (W - 1))
    (hsum : (((S + C) % 2 ^ W : Nat) : Int) = V % p2 W) :
    let (S', C') := applyTopGuard g W (zeroCarryTopNorm g) S C
    signedVal W S' + signedVal W C' = V ∧ C' < 2 ^ (W - g) := by
  sorry

/-- Sharpness Corollary: Naive unnormalized CSA right-shift fails with error `-2^(W-1)` at `V = 0` ∀ W ≥ 3. -/
theorem unnormalized_csa_rshift_fails {W : Nat} (hW : 3 ≤ W) :
    let S := 2 ^ (W - 1)
    let C := 2 ^ (W - 1)
    signedVal W (S + C) = 0 ∧
    (signedVal W S / 2) + (signedVal W C / 2) + (((S % 2 + C % 2) / 2 : Nat) : Int) =
      -p2 (W - 1) := by
  sorry

/-- THEOREM 6 (Universal 2-State Radix-`2^k` Sign-Extension Cancellation Law, ∀ k ≥ 1, ∀ W, ∀ m ≥ 1): Directly discharged by Mechanism I (`RadixTransducer.lift_sum`) on `secTransducer`: `∑_{j=0}^{m-1} secTerm_k(j > 0, s_j) * 2^(W + k*j) + ∑_{j=0}^{m-1} s_j * 2^(W + k*j) = 2^(W + k*m)`. -/
theorem sec_cancellation_exact {k m : Nat} (hk : 1 ≤ k) (hm : 1 ≤ m) (W : Nat) (s : Nat → Fin 2) :
    p2 W * radixSum (2 ^ k) (fun j => secTerm k (decide (0 < j)) (s j).val) m +
    p2 W * radixSum (2 ^ k) (fun j => ((s j).val : Int)) m =
      p2 (W + k * m) := by
  sorry

/-- THEOREM 8 (Complete Pure-Silicon Radix-4 Booth Tree + SEC Theorem, ∀ w ≥ 1, ∀ m ≥ 1): Combines Booth Transducer (Theorem 5) + Silicon PP (Theorem 7) + 2-State SEC (Theorem 6): 1. `boothTreeSum w m x_u y_u = signedVal w x_u * signedVal (2*m) y_u + 2^(w + 1 + 2*m)` EXACTLY IN `Int`! 2. Modulo `2^(w + 2*m)`, `boothTreeSum` equals the exact `(w + 2*m)`-bit signed product! -/
theorem radix4_booth_tree_exact {w m : Nat} (hw : 1 ≤ w) (hm : 1 ≤ m) (x_u y_u : Nat) :
    boothTreeSum w m x_u y_u =
      signedVal w x_u * signedVal (2 * m) y_u + p2 (w + 1 + 2 * m) ∧
    boothTreeSum w m x_u y_u % p2 (w + 2 * m) =
      (signedVal w x_u * signedVal (2 * m) y_u) % p2 (w + 2 * m) := by
  sorry

/-- Sharpness / Tightness: BOTH `+2^(w+k-2)` and `-2^(w+k-2)` are attained by `A_j'`! -/
theorem booth_acc_endpoints_tight {k w : Nat} (hk : 1 ≤ k) (hw : 1 ≤ w) :
    (signedVal w (2 ^ (w - 1)) * signedVal (k * 1) (2 ^ (k - 1))) / p2 (k * 0) = p2 (w + k - 2) ∧
    (signedVal w (2 ^ (w - 1)) * signedVal (k * (w + 1)) (2 ^ (k * (w + 1) - 1) - 1)) /
      p2 (k * w) = -p2 (w + k - 2) := by
  sorry

theorem badGuardCert_g2_rejected : badGuardCert_g2_cutArc.check = false := by
  sorry

end BoothCsaMultiplierInvariantsChallenge
