/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Paley32Mxfp4

/-!
# Verified Solutions (`paley32-mxfp4-outliers`)
-/

namespace Paley32Mxfp4Challenge

open Paley32Mxfp4

theorem universal_orthogonal_k_sparse_papr_lower_bound
    (n k : Nat) (hk1 : 1 ≤ k) (hkn : k ≤ n) (U : RatMat n n)
    (hUtU : isOrthogonalRat U (n : Rat))
    (hUUt : isOrthogonalRat (transposeRat U) (n : Rat)) :
    (∃ (i : Fin n) (S : Fin k → Fin n),
      isInjective S ∧
      (k : Rat) ≤ sumFinRat k (fun t => U i (S t) * U i (S t)) ∧
      ∃ x : Fin n → Rat,
        (∀ j : Fin n, (∀ t : Fin k, S t ≠ j) → x j = 0) ∧
        (0 : Rat) < sumSqRat x ∧
        (k : Rat) * sumSqRat x ≤ matVecRat U x i * matVecRat U x i) ∧
    (k < n →
      ((∀ (i : Fin n) (S : Fin k → Fin n), isInjective S →
          sumFinRat k (fun t => U i (S t) * U i (S t)) ≤ (k : Rat)) ↔
       (∀ i j : Fin n, U i j * U i j = 1))) :=
  Paley32Mxfp4.universal_orthogonal_k_sparse_papr_lower_bound n k hk1 hkn U hUtU hUUt

theorem paley32_orthogonality_and_zero_k4_collapse :
    isOrthogonal paley32 32 ∧
    isOrthogonal sylvester32 32 ∧
    (let y := matVec sylvester32 (supportVec [0, 1, 2, 3])
     countAbsEq y 4 = 8 ∧ countAbsEq y 0 = 24 ∧ sumFourthInt y = 2048) ∧
    countAffinePlanes32 = 1240 ∧
    (∀ c0 c1 c2 c3 : Fin 32, c0 < c1 → c1 < c2 → c2 < c3 →
      (c0.val ^^^ c1.val ^^^ c2.val ^^^ c3.val = 0) →
      maxC4 sylvester32 c0 c1 c2 c3 = 8) ∧
    (∀ c0 c1 c2 c3 : Fin 32, c0 < c1 → c1 < c2 → c2 < c3 →
      maxC4 paley32 c0 c1 c2 c3 ≤ 5) ∧
    (∃ c0 c1 c2 c3 : Fin 32, c0 < c1 ∧ c1 < c2 ∧ c2 < c3 ∧
      maxC4 paley32 c0 c1 c2 c3 = 5) :=
  Paley32Mxfp4.paley32_orthogonality_and_zero_k4_collapse

theorem paley32_vs_sylvester32_k8_l4_reduction :
    (let yS := matVec sylvester32 (supportVec [0, 1, 2, 3, 4, 5, 6, 7])
     countAbsEq yS 8 = 4 ∧ countAbsEq yS 0 = 28 ∧ sumFourthInt yS = 16384) ∧
    (∀ x : Fin 32 → Int, isSignedSparse 8 x →
      countAbsEq (matVec paley32 x) 8 ≤ 3 ∧
      sumFourthInt (matVec paley32 x) ≤ 12544) ∧
    (let yP := matVec paley32 (supportVec [0, 1, 2, 3, 8, 19, 22, 30])
     countAbsEq yP 8 = 3 ∧ sumFourthInt yP = 12544) ∧
    ((12544 : Rat) / 16384 = 49 / 64) :=
  Paley32Mxfp4.paley32_vs_sylvester32_k8_l4_reduction

theorem hall16_five_classes_orthogonality_and_k4_k8_duality :
    (isOrthogonal hall16_I 16 ∧ isOrthogonal hall16_II 16 ∧ isOrthogonal hall16_III 16 ∧
     isOrthogonal hall16_IV 16 ∧ isOrthogonal hall16_V 16) ∧
    (countClosedQuads16 hall16_I = 140 ∧
     countClosedQuads16 hall16_II = 76 ∧
     countClosedQuads16 hall16_III = 44 ∧
     countClosedQuads16 hall16_IV = 28 ∧
     countClosedQuads16 hall16_V = 28) ∧
    (∀ H : IntMat 16 16,
      (∀ r c : Fin 16, H r c = 1 ∨ H r c = -1) →
      isOrthogonal (transpose H) 16 →
      ∀ m : Nat, hasDoublePeak8Mask16 H m ↔ m ∈ rowPairMasks16 H) ∧
    (countDoublePeak8Subsets16 hall16_I = 30 ∧
     countDoublePeak8Subsets16 hall16_II = 54 ∧
     countDoublePeak8Subsets16 hall16_III = 90 ∧
     countDoublePeak8Subsets16 hall16_V = 114 ∧
     countDoublePeak8Subsets16 hall16_IV = 156) :=
  Paley32Mxfp4.hall16_five_classes_orthogonality_and_k4_k8_duality

theorem bent_diagonal_n16_anti_resonance_exact :
    isOrthogonal (diagTwist sylvester16 bentDiag16) 16 ∧
    affinePlanes16.length = 140 ∧
    countFlatAffinePlanes16 sylvester16 = 0 ∧
    countFlatAffinePlanes16 (diagTwist sylvester16 bentDiag16) = 80 :=
  Paley32Mxfp4.bent_diagonal_n16_anti_resonance_exact

theorem mxfp4_e8m0_bulk_crush_threshold_exact :
    (∀ (B k : Nat) (M S : Rat), 1 ≤ k → k < B → (0 : Rat) ≤ M →
      ((k : Rat) * M) / 6 ≤ S →
      (576 * ((B - k : Nat) : Rat) < ((k : Rat) * (k : Rat)) * (M * M) →
        ((B - k : Nat) : Rat) < (S / 4) * (S / 4)) ∧
      (((k : Rat) * (k : Rat)) * (M * M) = 576 * ((B - k : Nat) : Rat) →
        S = ((k : Rat) * M) / 6 →
        (S / 4) * (S / 4) = ((B - k : Nat) : Rat))) ∧
    ((576 * ((32 - 4 : Nat) : Rat)) / (4 * 4) = 1008 ∧
     (31 : Rat) * 31 < 1008 ∧ (1008 : Rat) < 32 * 32) ∧
    (∀ k : Nat, mxfp4HybridBits 32 k 5 < mxfp6BlockBits 32 ↔ k ≤ 3) ∧
    (∀ k : Nat, mxfp4HybridBits 64 k 6 < mxfp6BlockBits 64 ↔ k ≤ 5) ∧
    (∀ k : Nat, mxfp4HybridBits 16 k 4 < mxfp6BlockBits 16 ↔ k ≤ 1) :=
  Paley32Mxfp4.mxfp4_e8m0_bulk_crush_threshold_exact

end Paley32Mxfp4Challenge
