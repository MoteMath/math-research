/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecodingOt

/-!
# Verified Solutions (`spec-decoding-ot-bounds`)
-/

namespace SpecDecodingOtChallenge

open SpecDecodingOt

theorem multidraft_corr_vs_iid_exact_gaps (K : Nat) (hK : 1 ≤ K) :
    (∀ (V : Nat) (p q : Fin V → Rat), isProbDist p → isProbDist q →
      ∀ (S : Fin V → Bool),
        alphaCorr K p q - strassenObj K p q S ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
        (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q ≤
          ((K ^ K : Nat) : Rat) * strassenObj K p q S) ∧
    (∃ p q : Fin 2 → Rat,
      isProbDist p ∧ isProbDist q ∧
      alphaCorr K p q = 1 ∧
      alphaIID K p q = 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      alphaCorr K p q - alphaIID K p q = ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q =
        ((K ^ K : Nat) : Rat) * alphaIID K p q) :=
  SpecDecodingOt.multidraft_corr_vs_iid_exact_gaps K hK

theorem cyclic_madow_optimality_refutation_exact :
    (isProbDist madowCE1P ∧ isProbDist madowCE1Q ∧
      alphaMadow2 madowCE1P madowCE1Q = (1 : Rat) / 2 ∧
      alphaIID 2 madowCE1P madowCE1Q = (3 : Rat) / 4 ∧
      alphaCorr 2 madowCE1P madowCE1Q = 1 ∧
      alphaMadow2 madowCE1P madowCE1Q < alphaIID 2 madowCE1P madowCE1Q ∧
      alphaIID 2 madowCE1P madowCE1Q < alphaCorr 2 madowCE1P madowCE1Q) ∧
    (isProbDist madowCE2P ∧ isProbDist madowCE2Q ∧
      (∀ i j : Fin 4, i.val ≤ j.val → madowCE2P j / madowCE2Q j ≤ madowCE2P i / madowCE2Q i) ∧
      alphaMadow2 madowCE2P madowCE2Q = (17 : Rat) / 20 ∧
      alphaIID 2 madowCE2P madowCE2Q = (91 : Rat) / 100 ∧
      alphaCorr 2 madowCE2P madowCE2Q = 1 ∧
      alphaMadow2 madowCE2P madowCE2Q < alphaIID 2 madowCE2P madowCE2Q ∧
      alphaIID 2 madowCE2P madowCE2Q < alphaCorr 2 madowCE2P madowCE2Q) :=
  SpecDecodingOt.cyclic_madow_optimality_refutation_exact

theorem quantized_draft_loss_k1_exact (V : Nat) (hV : 2 ≤ V) (R : Rat) (hR : 1 ≤ R) :
    (∀ (p w w' : Fin V → Rat), isProbDist p → (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      (alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w')).abs ≤ (R - 1) / (R + 1)) ∧
    (∃ (p w w' : Fin V → Rat), isProbDist p ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w') = (R - 1) / (R + 1)) :=
  SpecDecodingOt.quantized_draft_loss_k1_exact V hV R hR

theorem quantized_draft_loss_multidraft_exact (K : Nat) (hK : 2 ≤ K) (V : Nat) (hV : 2 ≤ V)
    (R : Rat) (hR : 1 ≤ R) :
    (∀ (p w w' : Fin V → Rat), isProbDist p → (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') ≤
        (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R))) ∧
    (∃ (p w w' : Fin V → Rat), isProbDist p ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') =
        (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R))) :=
  SpecDecodingOt.quantized_draft_loss_multidraft_exact K hK V hV R hR

theorem modular_bitvec_reversible_exact_inverse (b L : Nat)
    (F G : Fin L → BitVec b → BitVec b) (s : BitVec b × BitVec b) :
    revPass L F G (fwdPass L F G s) = s ∧ fwdPass L F G (revPass L F G s) = s :=
  SpecDecodingOt.modular_bitvec_reversible_exact_inverse b L F G s

theorem symplectic_float_reversible_unimodular (γ : Rat) (n : Nat) :
    mat2Det (symplecticM γ) = 1 ∧
    mat2Det (mat2Pow (symplecticM γ) n) = 1 ∧
    mat2Trace (symplecticM γ) = 2 + γ * γ ∧
    (γ ≠ 0 → 2 < mat2Trace (symplecticM γ)) ∧
    1 + (n : Rat) * (γ * γ) ≤ (mat2Pow (symplecticM γ) n).a00 ∧
    (0 ≤ γ → ratPow (1 + γ) n ≤ (mat2Pow (symplecticM γ) n).a00 + (mat2Pow (symplecticM γ) n).a01) :=
  SpecDecodingOt.symplectic_float_reversible_unimodular γ n

end SpecDecodingOtChallenge
