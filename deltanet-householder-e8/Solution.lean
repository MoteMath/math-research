/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltaNetHouseholderE8

/-!
# Verified Solutions (`deltanet-householder-e8`)
-/

namespace DeltaNetHouseholderE8Challenge

open DeltaNetHouseholderE8

theorem householder_spectral_stability_iff_exact :
    (∀ (d : Nat) (β : Rat) (k v : Fin d → Rat),
      l2NormSq (householderApply β k v) =
        l2NormSq v - β * (2 - β * l2NormSq k) * (dotProd k v * dotProd k v)) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      householderApply β k k = (fun i => (1 - β * l2NormSq k) * k i) ∧
      l2NormSq (householderApply β k k) =
        (1 - β * l2NormSq k) * (1 - β * l2NormSq k) * l2NormSq k) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      (∀ v : Fin d → Rat, l2NormSq (householderApply β k v) ≤ l2NormSq v) ↔
        ((0 : Rat) ≤ β * l2NormSq k ∧ β * l2NormSq k ≤ 2)) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      (0 : Rat) < l2NormSq k → (2 : Rat) < β * l2NormSq k →
        l2NormSq k < l2NormSq (householderApply β k k) ∧
        (1 : Rat) < ratAbs (1 - β * l2NormSq k)) :=
  DeltaNetHouseholderE8.householder_spectral_stability_iff_exact

theorem quantized_unit_norm_supremum_exact :
    (∀ m : Nat, rneBinadeBottomRatio m = (pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) ∧
    (∀ m : Nat, sMax1 m = rneBinadeBottomRatio m * rneBinadeBottomRatio m) ∧
    (∀ m : Nat, sMax1 m =
      1 + (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) ∧
    (∀ m : Nat, 1 ≤ m → (1 : Rat) < sMax1 m) ∧
    (∀ (d m : Nat) (u uHat : Fin d → Rat),
      l2NormSq u = 1 →
      (∀ i : Fin d, ratAbs (uHat i) ≤ rneBinadeBottomRatio m * ratAbs (u i)) →
      l2NormSq uHat ≤ sMax1 m) ∧
    (sMax1 7 = 66564 / 66049 ∧
     sMax1 10 = 4202500 / 4198401 ∧
     sMax1 3 = 324 / 289) ∧
    (l2NormSq fp8WitnessVec = 287 / 256 ∧
     (1 : Rat) < l2NormSq fp8WitnessVec ∧
     l2NormSq fp8WitnessVec < sMax1 3 ∧
     (2 : Rat) < betaOneUlp 3 * l2NormSq fp8WitnessVec ∧
     betaTwoUlp 3 * l2NormSq fp8WitnessVec < 2) :=
  DeltaNetHouseholderE8.quantized_unit_norm_supremum_exact

theorem universal_two_ulp_safe_ceiling_theorem :
    (∀ m : Nat, 2 ≤ m → (2 : Rat) < betaOneUlp m * sMax1 m) ∧
    (∀ m : Nat, 2 ≤ m →
      (0 : Rat) < betaTwoUlp m ∧
      betaTwoUlp m * sMax1 m < 2 ∧
      betaTwoUlp m * sMax1 m ≤ 2) ∧
    (∀ m : Nat, 1 ≤ m → betaTwoUlp m = 2 - invPow2Rat (m - 1)) ∧
    (betaTwoUlp 7 = 127 / 64 ∧
     betaTwoUlp 10 = 1023 / 512 ∧
     betaTwoUlp 3 = 7 / 4) ∧
    (∀ (d m : Nat) (k : Fin d → Rat),
      2 ≤ m → l2NormSq k ≤ sMax1 m →
      ∀ v : Fin d → Rat, l2NormSq (householderApply (betaTwoUlp m) k v) ≤ l2NormSq v) ∧
    (∀ m : Nat, 2 ≤ m →
      let r := rneBinadeBottomRatio m
      let k : Fin 1 → Rat := fun _ => r
      l2NormSq k = sMax1 m ∧
      l2NormSq k < l2NormSq (householderApply (betaOneUlp m) k k) ∧
      (1 : Rat) < ratAbs (1 - betaOneUlp m * l2NormSq k)) :=
  DeltaNetHouseholderE8.universal_two_ulp_safe_ceiling_theorem

theorem wy_triangular_inverse_norm_growth_exact :
    (∀ (C : Nat) (i j : Fin C),
      matMul (wyAlignedMat C) (wyAlignedInv C) i j = identityMat C i j ∧
      matMul (wyAlignedInv C) (wyAlignedMat C) i j = identityMat C i j) ∧
    (∀ (C : Nat) (i j : Fin C), j.val < i.val →
      wyAlignedInv C i j = if (i.val - j.val) % 2 = 0 then 2 else -2) ∧
    (∀ (C : Nat) (i : Fin C),
      rowL1Norm (wyAlignedInv C) i = 2 * (i.val : Rat) + 1) ∧
    (∀ (C : Nat) (hC : 0 < C),
      (∀ i : Fin C, rowL1Norm (wyAlignedInv C) i ≤ 2 * (C : Rat) - 1) ∧
      rowL1Norm (wyAlignedInv C) ⟨C - 1, Nat.sub_lt hC (by decide)⟩ = 2 * (C : Rat) - 1) ∧
    (rowL1Norm (wyAlignedInv 64) ⟨63, by decide⟩ = 127) :=
  DeltaNetHouseholderE8.wy_triangular_inverse_norm_growth_exact

theorem d8_and_e8_weyl_root_zero_ulp_orthogonality :
    (∀ (v x : Fin 8 → Int), IsD8Root v →
      (2 * intDot8 v x) % 2 = 0 ∧
      intNormSq8 (reflectD8 v x) = intNormSq8 x ∧
      reflectD8 v (reflectD8 v x) = x ∧
      (InD8Lattice x → InD8Lattice (reflectD8 v x))) ∧
    (∀ w : Fin 8 → Int, IsTwoE8Root w ↔ (IsTwoE8IntRoot w ∨ IsTwoE8HalfIntRoot w)) ∧
    ((8 * 7 / 2) * 4 = 112 ∧ 2 ^ 7 = 128 ∧ 112 + 128 = 240) ∧
    (∀ (w x : Fin 8 → Int), IsTwoE8Root w → InTwoE8Lattice x →
      (2 * intDot8 w x) % 8 = 0 ∧
      intDot8 w x % 4 = 0 ∧
      InTwoE8Lattice (reflectTwoE8 w x) ∧
      intNormSq8 (reflectTwoE8 w x) = intNormSq8 x ∧
      reflectTwoE8 w (reflectTwoE8 w x) = x) :=
  DeltaNetHouseholderE8.d8_and_e8_weyl_root_zero_ulp_orthogonality

theorem non_weyl_hamming_closure_obstruction :
    intNormSq8 hammingV = 4 ∧
    intDot8 hammingV hammingX = 1 ∧
    2 * intDot8 hammingV hammingX = 2 ∧
    (2 * intDot8 hammingV hammingX) % 4 = 2 ∧
    (2 * intDot8 hammingV hammingX) % 4 ≠ 0 ∧
    householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingX) ⟨0, by decide⟩ = 1 / 2 ∧
    (∀ z : Int, (z : Rat) ≠
      householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingX) ⟨0, by decide⟩) ∧
    InD8Lattice hammingXEven ∧
    (2 * intDot8 hammingV hammingXEven) % 4 = 2 ∧
    (∀ z : Int, (z : Rat) ≠
      householderApply (2 / (4 : Rat)) (ratOfIntVec8 hammingV) (ratOfIntVec8 hammingXEven) ⟨0, by decide⟩) :=
  DeltaNetHouseholderE8.non_weyl_hamming_closure_obstruction

end DeltaNetHouseholderE8Challenge
