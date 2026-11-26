/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp6Ef21Rotations

/-!
# Verified Solutions (`mxfp6-ef21-rotations`)
-/

namespace Mxfp6Ef21RotationsChallenge

open Mxfp6Ef21Rotations

theorem mxfp6_e3m2_nvfp6_ef21_universal (B : Nat) (hB : 0 < B) :
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 28) → (∃ i0, (14 : Rat) < absRat (y i0)) →
      sumSqErr e3m2Quant y ≤ (1 - alphaMXFP6E3M2 B) * sumSq y) ∧
    (∀ ε : Rat, (0 : Rat) < ε → ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 28) ∧ (∃ i0, (14 : Rat) < absRat (y i0)) ∧
      (1 - alphaMXFP6E3M2 B - ε) * sumSq y < sumSqErr e3m2Quant y) ∧
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 28) → (∃ i0, absRat (y i0) = 28) →
      sumSqErr e3m2Quant y ≤ (1 - alphaNVFP6E3M2 B) * sumSq y) ∧
    (∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 28) ∧ (∃ i0, absRat (y i0) = 28) ∧
      sumSqErr e3m2Quant y = (1 - alphaNVFP6E3M2 B) * sumSq y) :=
  Mxfp6Ef21Rotations.mxfp6_e3m2_nvfp6_ef21_universal B hB

theorem mxfp6_e2m3_nvfp6_ef21_universal (B : Nat) (hB : 0 < B) :
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 15/2) → (∃ i0, (15/4 : Rat) < absRat (y i0)) →
      sumSqErr e2m3Quant y ≤ (1 - alphaMXFP6E2M3 B) * sumSq y) ∧
    (∀ ε : Rat, (0 : Rat) < ε → ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 15/2) ∧ (∃ i0, (15/4 : Rat) < absRat (y i0)) ∧
      (1 - alphaMXFP6E2M3 B - ε) * sumSq y < sumSqErr e2m3Quant y) ∧
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 15/2) → (∃ i0, absRat (y i0) = 15/2) →
      sumSqErr e2m3Quant y ≤ (1 - alphaNVFP6E2M3 B) * sumSq y) ∧
    (∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 15/2) ∧ (∃ i0, absRat (y i0) = 15/2) ∧
      sumSqErr e2m3Quant y = (1 - alphaNVFP6E2M3 B) * sumSq y) :=
  Mxfp6Ef21Rotations.mxfp6_e2m3_nvfp6_ef21_universal B hB

theorem mxfp6_e2m3_vs_e3m2_exact_crossover (B : Nat) (hB : 0 < B) :
    ((1 ≤ B ∧ B ≤ 43) → alphaMXFP6E3M2 B < alphaMXFP6E2M3 B) ∧
    (44 ≤ B → alphaMXFP6E2M3 B < alphaMXFP6E3M2 B) ∧
    (alphaMXFP6E2M3 32 = 4608 / 4655 ∧ alphaMXFP6E3M2 32 = 327680 / 331807 ∧
     (327680 / 331807 : Rat) < 4608 / 4655) ∧
    (alphaNVFP6E3M2 1 = 1 ∧ alphaNVFP6E2M3 1 = 1) ∧
    ((2 ≤ B ∧ B ≤ 178) → alphaNVFP6E3M2 B < alphaNVFP6E2M3 B) ∧
    (179 ≤ B → alphaNVFP6E2M3 B < alphaNVFP6E3M2 B) :=
  Mxfp6Ef21Rotations.mxfp6_e2m3_vs_e3m2_exact_crossover B hB

theorem hadamard_weight_quantization_defect_and_min_dyadic_coherence :
    (8 * ((3/8 : Rat) * (3/8)) = 9/8) ∧
    (8 * ((11/32 : Rat) * (11/32)) = 121/128) ∧
    (32 * ((3/16 : Rat) * (3/16)) = 9/8) ∧
    (32 * ((11/64 : Rat) * (11/64)) = 121/128) ∧
    (∀ k : Int, (1/8 : Rat) ≤ ((k : Rat) / 32) * ((k : Rat) / 32) → 12 ≤ k.natAbs) ∧
    (∀ k : Int, (1/32 : Rat) ≤ ((k : Rat) / 64) * ((k : Rat) / 64) → 12 ≤ k.natAbs) :=
  Mxfp6Ef21Rotations.hadamard_weight_quantization_defect_and_min_dyadic_coherence

theorem goethals_seidel_native_e2m1_orthonormal_exact :
    isOrthogonal GS_n16_E2M1_low 64 ∧
    (∀ i j : Fin 16, inAllThreeOCPGrids ((GS_n16_E2M1_low i j : Rat) / 8)) ∧
    isOrthogonal GS_n32_E2M1_pm13 64 ∧
    (∀ i j : Fin 32, inAllThreeOCPGrids ((GS_n32_E2M1_pm13 i j : Rat) / 8)) ∧
    (∀ i j : Fin 32, GS_n32_E2M1_pm13 i j ≠ 0) :=
  Mxfp6Ef21Rotations.goethals_seidel_native_e2m1_orthonormal_exact

theorem quaternion_4of8_sparse_orthogonality_universal :
    (∀ a b c d : Int, isOrthogonal (quatMat a b c d) (a * a + b * b + c * c + d * d)) ∧
    (∀ (m : Nat) (params : Fin m → Int × Int × Int × Int) (σ : Fin (4 * m) → Fin (4 * m)) (c : Int),
      isBijection σ →
      (∀ b : Fin m, let (a, b1, c1, d) := params b; a * a + b1 * b1 + c1 * c1 + d * d = c) →
      isOrthogonal (quatStage m params σ) c ∧ isRow4Sparse (quatStage m params σ)) ∧
    (∀ (n : Nat) (stages : List (IntMat n n × Int)),
      (∀ s ∈ stages, isOrthogonal s.1 s.2) →
      isOrthogonal (matProd n (stages.map Prod.fst)) (prodInt (stages.map Prod.snd))) :=
  Mxfp6Ef21Rotations.quaternion_4of8_sparse_orthogonality_universal

end Mxfp6Ef21RotationsChallenge
