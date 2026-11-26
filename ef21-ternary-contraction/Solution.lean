/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EF21Ternary

/-!
# Verified Solutions (`ef21-ternary-contraction`)
-/

namespace EF21TernaryChallenge

open scoped BigOperators
open EF21Ternary

theorem ternary_ef21_contraction_exact (d : ℕ) (hd : 0 < d) :
    (∀ x : Fin d → ℝ, ∃ (γ : ℝ) (t : Fin d → ℤ),
      (∀ i, t i = -1 ∨ t i = 0 ∨ t i = 1) ∧
      ∑ i : Fin d, (x i - γ * (t i : ℝ)) ^ 2 ≤
        (1 - alphaTern d) * ∑ i : Fin d, (x i) ^ 2) ∧
    (∀ (γ : ℝ) (t : Fin d → ℤ),
      (∀ i, t i = -1 ∨ t i = 0 ∨ t i = 1) →
      (1 - alphaTern d) * ∑ i : Fin d, (ternaryExtremal d i) ^ 2 ≤
        ∑ i : Fin d, (ternaryExtremal d i - γ * (t i : ℝ)) ^ 2) :=
  EF21Ternary.ternary_ef21_contraction_exact d hd

theorem alphaTern_harmonic_sandwich (d : ℕ) (hd : 0 < d) :
    4 / (4 + harmonicR (d - 1)) ≤ alphaTern d ∧
      alphaTern d ≤ 4 / (3 + harmonicR d) :=
  EF21Ternary.alphaTern_harmonic_sandwich d hd

theorem mxfp4_nvfp4_ef21_contraction_universal (B : ℕ) (hB : 0 < B) :
    ((∀ y : Fin B → ℝ, (∀ i, |y i| ≤ 6) → (∃ i0, 3 < |y i0|) →
        ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2 ≤
          (1 - alphaMXFP4 B) * ∑ i : Fin B, (y i) ^ 2) ∧
     (∀ ε : ℝ, 0 < ε → ∃ y : Fin B → ℝ, (∀ i, |y i| ≤ 6) ∧ (∃ i0, 3 < |y i0|) ∧
        (1 - alphaMXFP4 B - ε) * ∑ i : Fin B, (y i) ^ 2 <
          ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2)) ∧
    ((∀ y : Fin B → ℝ, (∀ i, |y i| ≤ 6) → (∃ i0, |y i0| = 6) →
        ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2 ≤
          (1 - alphaNVFP4 B) * ∑ i : Fin B, (y i) ^ 2) ∧
     (∃ y : Fin B → ℝ, (∀ i, |y i| ≤ 6) ∧ (∃ i0, |y i0| = 6) ∧
        ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2 =
          (1 - alphaNVFP4 B) * ∑ i : Fin B, (y i) ^ 2)) :=
  EF21Ternary.mxfp4_nvfp4_ef21_contraction_universal B hB

theorem symmetric_2bit_no_zero_collapse (d : ℕ) (hd : 0 < d) :
    let e0 : Fin d → ℝ := fun i => if i.1 = 0 then 1 else 0
    (∀ (γ : ℝ) (q : Fin d → ℤ),
      (∀ i, q i = -3 ∨ q i = -1 ∨ q i = 1 ∨ q i = 3) →
      (1 - 9 / ((d : ℝ) + 8)) * (∑ i : Fin d, (e0 i) ^ 2) ≤
        ∑ i : Fin d, (e0 i - γ * (q i : ℝ)) ^ 2) ∧
    (∃ q : Fin d → ℤ,
      (∀ i, q i = -3 ∨ q i = -1 ∨ q i = 1 ∨ q i = 3) ∧
      ∑ i : Fin d, (e0 i - (3 / ((d : ℝ) + 8)) * (q i : ℝ)) ^ 2 =
        (1 - 9 / ((d : ℝ) + 8)) * (∑ i : Fin d, (e0 i) ^ 2)) :=
  EF21Ternary.symmetric_2bit_no_zero_collapse d hd

theorem mantissa_sr_variance_law (m : ℕ) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * (1 - t) / ((2 : ℝ) ^ m + t) ^ 2 ≤
        1 / (4 * (2 : ℝ) ^ m * ((2 : ℝ) ^ m + 1))) ∧
    (let tStar : ℝ := (2 : ℝ) ^ m / (2 * (2 : ℝ) ^ m + 1)
     0 ≤ tStar ∧ tStar ≤ 1 ∧
     tStar * (1 - tStar) / ((2 : ℝ) ^ m + tStar) ^ 2 =
       1 / (4 * (2 : ℝ) ^ m * ((2 : ℝ) ^ m + 1))) :=
  EF21Ternary.mantissa_sr_variance_law m

end EF21TernaryChallenge
