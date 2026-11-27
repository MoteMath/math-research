/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrayBasisFeistelCarryOrbits

/-!
# Verified Solutions (`gray-basis-feistel-carry-orbits`)
-/

namespace GrayBasisFeistelCarryOrbitsChallenge

open SiliconOrbitEngine

theorem phi_singleCycle_iff_even (n : Nat) (hn : 1 ≤ n) (γ : BitVec n) :
    IsSingleCycle n (phi n γ) ↔ γ.toNat % 2 = 0 :=
  SiliconOrbitEngine.phi_singleCycle_iff_even n hn γ

theorem grayInvMap_singleCycle_iff {n : Nat} (hn : 1 ≤ n)
    {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) :
    IsSingleCycle (n + 1) (grayInvMap P δ) ↔ (compiledDefect δ m).toNat % 2 = 0 :=
  SiliconOrbitEngine.grayInvMap_singleCycle_iff hn spec

theorem grayBitPermInvolution_plusOne_universal {n : Nat} (hn : 1 ≤ n)
    (π : Fin (n + 1) → Fin (n + 1)) (hinv : ∀ i, π (π i) = i) :
    let F : BitVec (n + 1) → BitVec (n + 1) := fun x => invGray (applyBitPerm (n + 1) π (gray x)) + 1#(n + 1)
    let j : Nat := (π ⟨0, by omega⟩).val
    HasMinPeriod F 0#(n + 1) (2 ^ (n + 1 - j)) ∧
    (IsSingleCycle (n + 1) F ↔ j = 0) ∧
    ∀ x : BitVec (n + 1),
      HasMinPeriod F x (2 ^ (n + 1 - j)) ∨ HasMinPeriod F x 2 ∨ HasMinPeriod F x 4 :=
  SiliconOrbitEngine.grayBitPermInvolution_plusOne_universal hn π hinv

theorem grayBitrev_plusOne_order4 {w : Nat} (hw : 2 ≤ w) :
    let F : BitVec w → BitVec w := fun x => invGray (applyBitPerm w (bitrevFin w) (gray x)) + 1#w
    HasMinPeriod F 0#w 2 ∧ ∀ x : BitVec w, iter F 4 x = x :=
  SiliconOrbitEngine.grayBitrev_plusOne_order4 hw

theorem grayBitPermInvolution_msbKick_singleCycle_iff {w : Nat} (hw : 3 ≤ w)
    (π : Fin w → Fin w) (hinv : ∀ i, π (π i) = i) :
    IsSingleCycle w (fun x => invGray (applyBitPerm w π (gray x)) + ((1#w <<< (w - 1)) + 1#w)) ↔
      (π ⟨0, by omega⟩).val = 0 ∨
      (π ⟨0, by omega⟩).val = w - 2 ∨
      (π ⟨0, by omega⟩).val = w - 1 :=
  SiliconOrbitEngine.grayBitPermInvolution_msbKick_singleCycle_iff hw π hinv

theorem grayBitrev_msbKick_singleCycle {w : Nat} (hw : 3 ≤ w) :
    IsSingleCycle w (fun x => invGray (applyBitPerm w (bitrevFin w) (gray x)) + ((1#w <<< (w - 1)) + 1#w)) :=
  SiliconOrbitEngine.grayBitrev_msbKick_singleCycle hw

theorem feistelCarry_singleCycle_iff {m k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (h : BitVec m → BitVec k) :
    IsSingleCycle (m + k) (feistelCarry m k h) ↔ ∀ a : BitVec m, (h a).toNat % 2 = 0 :=
  SiliconOrbitEngine.feistelCarry_singleCycle_iff hm hk h

theorem feistelCarry_bijection_jacobsthal {k : Nat} (hk : 1 ≤ k)
    (h hInv : BitVec k → BitVec k)
    (hleft : ∀ a, hInv (h a) = a) (hright : ∀ a, h (hInv a) = a) :
    3 * feistelZeroLen k k h = 2 ^ (2 * k + 1) + 1 ∧
    HasMinPeriod (feistelCarry k k h) 0#(k + k) (feistelZeroLen k k h) ∧
    ∀ x : BitVec (k + k),
      HasMinPeriod (feistelCarry k k h) x (feistelZeroLen k k h) ∨
      HasMinPeriod (feistelCarry k k h) x 1 ∨
      HasMinPeriod (feistelCarry k k h) x 2 :=
  SiliconOrbitEngine.feistelCarry_bijection_jacobsthal hk h hInv hleft hright

end GrayBasisFeistelCarryOrbitsChallenge
