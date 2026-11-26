/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonNsDyadic.Defs

/-!
# Globally Optimal Dyadic Quintics in FP8-E4M3FN and BF16 (Theorems 3–4)

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
3. `fp8_e4m3fn_optimal_quintic_exact_zero_error`:
   GPU-discovered FP8-E4M3FN optimal quintic `(2, -9/8, 1/8)` satisfies `a + b + c = 1`,
   `p(1) = 1`, `p'(1) = -3/4` (`|p'(1)| < 1`), and achieves EXACT ZERO (`0`) 5-step error
   across all 28 representable FP8-E4M3FN values in `[0.05, 1]` (`0x1D..0x38`) in both
   Muon matrix-form and Monomial modes, with zero NaN/overflow across all 56 unit values.
4. `bf16_optimal_dyadic_quintic_one_ulp_confinement`:
   GPU-discovered BF16 optimal quintic `(35/16, -31/16, 3/4)` satisfies `a + b + c = 1`,
   `p(1) = 1`, `p'(1) = 1/8`, exact period-1 fixed point at `1`, and confines all 564
   representable BF16 values in `[0.05, 1]` (`0x3D4D..0x3F80`) within `1/128` (1 BF16 ULP),
   `44x` tighter than Jordan's `[0.05, 1]` error (`11/32`) and `46x` tighter than Jordan's
   `[0.01, 1]` Muon matrix-form error (`23/64`).
-/

namespace MuonNsDyadic

private def fp8OptExactOne (x : Nat) : Bool :=
  (quinticIter fp8E4M3FNSpec .muonMatForm fp8OptA fp8OptB fp8OptC 5 x == fp8One) &&
  (quinticIter fp8E4M3FNSpec .monomial fp8OptA fp8OptB fp8OptC 5 x == fp8One)

private theorem fp8Opt_all_05 :
    checkRange fp8OptExactOne 0x1D (0x38 - 0x1D + 1) = true := by
  decide +kernel

private def fp8OptUnitFinite (x : Nat) : Bool :=
  fpIsFinite fp8E4M3FNSpec (quinticIter fp8E4M3FNSpec .muonMatForm fp8OptA fp8OptB fp8OptC 5 x) &&
  fpIsFinite fp8E4M3FNSpec (quinticIter fp8E4M3FNSpec .monomial fp8OptA fp8OptB fp8OptC 5 x)

private theorem fp8Opt_all_unit_finite :
    checkRange fp8OptUnitFinite 0x01 (0x38 - 0x01 + 1) = true := by
  decide +kernel

private def bf16ErrLe1_128 (y : Nat) : Bool :=
  fpIsFinite bf16Spec y && decide (ratAbs (fpToRat bf16Spec y - 1) ≤ (1 / 128 : Rat))

private theorem bf16ErrLe1_128_range :
    checkRange bf16ErrLe1_128 0x3F7E (0x3F81 - 0x3F7E + 1) = true := by
  decide +kernel

private theorem bf16_of_range_1_128 {y : Nat} (hlo : 0x3F7E ≤ y) (hhi : y ≤ 0x3F81) :
    fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (1 / 128 : Rat) := by
  have h := checkRange_spec bf16ErrLe1_128 0x3F7E (0x3F81 - 0x3F7E + 1) bf16ErrLe1_128_range y hlo (by omega)
  simp only [bf16ErrLe1_128, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

private def bf16OptInRange (x : Nat) : Bool :=
  strictNat (quinticIter bf16Spec .monomial bf16OptA bf16OptB bf16OptC 5 x) fun y =>
    Nat.ble 0x3F7E y && Nat.ble y 0x3F81

private theorem bf16Opt_all_05 :
    checkRange bf16OptInRange 0x3D4D (0x3F80 - 0x3D4D + 1) = true := rfl

/-- Theorem 3 (`fp8_e4m3fn_optimal_quintic_exact_zero_error`). -/
theorem fp8_e4m3fn_optimal_quintic_exact_zero_error :
    (fpToRat fp8E4M3FNSpec fp8OptA = (2 : Rat) ∧
     fpToRat fp8E4M3FNSpec fp8OptB = (-9 / 8 : Rat) ∧
     fpToRat fp8E4M3FNSpec fp8OptC = (1 / 8 : Rat)) ∧
    ((2 : Rat) + (-9 / 8 : Rat) + (1 / 8 : Rat) = 1 ∧
     quinticEval 2 (-9 / 8) (1 / 8) 1 = 1 ∧
     quinticDeriv 2 (-9 / 8) (1 / 8) 1 = (-3 / 4 : Rat) ∧
     ratAbs (quinticDeriv 2 (-9 / 8) (1 / 8) 1) = (3 / 4 : Rat) ∧
     ratAbs (quinticDeriv 2 (-9 / 8) (1 / 8) 1) < 1) ∧
    (quinticStep fp8E4M3FNSpec .muonMatForm fp8OptA fp8OptB fp8OptC fp8One = fp8One ∧
     quinticStep fp8E4M3FNSpec .monomial fp8OptA fp8OptB fp8OptC fp8One = fp8One ∧
     fpToRat fp8E4M3FNSpec fp8One = 1) ∧
    (∀ x : Nat, 0x1D ≤ x → x ≤ 0x38 →
      let yM := quinticIter fp8E4M3FNSpec .muonMatForm fp8OptA fp8OptB fp8OptC 5 x
      let yP := quinticIter fp8E4M3FNSpec .monomial fp8OptA fp8OptB fp8OptC 5 x
      yM = fp8One ∧ fpIsFinite fp8E4M3FNSpec yM = true ∧ ratAbs (fpToRat fp8E4M3FNSpec yM - 1) = 0 ∧
      yP = fp8One ∧ fpIsFinite fp8E4M3FNSpec yP = true ∧ ratAbs (fpToRat fp8E4M3FNSpec yP - 1) = 0) ∧
    (∀ x : Nat, 0x01 ≤ x → x ≤ 0x38 →
      fpIsFinite fp8E4M3FNSpec (quinticIter fp8E4M3FNSpec .muonMatForm fp8OptA fp8OptB fp8OptC 5 x) = true ∧
      fpIsFinite fp8E4M3FNSpec (quinticIter fp8E4M3FNSpec .monomial fp8OptA fp8OptB fp8OptC 5 x) = true) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · intro x hlo hhi
    have h := checkRange_spec fp8OptExactOne 0x1D (0x38 - 0x1D + 1) fp8Opt_all_05 x hlo (by omega)
    simp only [fp8OptExactOne, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨hM, hP⟩
    refine ⟨hM, ?_, ?_, hP, ?_, ?_⟩
    · rw [hM]; decide +kernel
    · rw [hM]; decide +kernel
    · rw [hP]; decide +kernel
    · rw [hP]; decide +kernel
  · intro x hlo hhi
    have h := checkRange_spec fp8OptUnitFinite 0x01 (0x38 - 0x01 + 1) fp8Opt_all_unit_finite x hlo (by omega)
    simp only [fp8OptUnitFinite, Bool.and_eq_true] at h
    exact h

/-- Theorem 4 (`bf16_optimal_dyadic_quintic_one_ulp_confinement`). -/
theorem bf16_optimal_dyadic_quintic_one_ulp_confinement :
    (fpToRat bf16Spec bf16OptA = (35 / 16 : Rat) ∧
     fpToRat bf16Spec bf16OptB = (-31 / 16 : Rat) ∧
     fpToRat bf16Spec bf16OptC = (3 / 4 : Rat)) ∧
    ((35 / 16 : Rat) + (-31 / 16 : Rat) + (3 / 4 : Rat) = 1 ∧
     quinticEval (35 / 16) (-31 / 16) (3 / 4) 1 = 1 ∧
     quinticDeriv (35 / 16) (-31 / 16) (3 / 4) 1 = (1 / 8 : Rat) ∧
     ratAbs (quinticDeriv (35 / 16) (-31 / 16) (3 / 4) 1) < 1) ∧
    (quinticStep bf16Spec .monomial bf16OptA bf16OptB bf16OptC bf16One = bf16One ∧
     fpToRat bf16Spec bf16One = 1) ∧
    ((11 / 32 : Rat) / (1 / 128 : Rat) = 44 ∧
     (23 / 64 : Rat) / (1 / 128 : Rat) = 46) ∧
    (∀ x : Nat, 0x3D4D ≤ x → x ≤ 0x3F80 →
      let y := quinticIter bf16Spec .monomial bf16OptA bf16OptB bf16OptC 5 x
      fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (1 / 128 : Rat)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro x hlo hhi
  have h := checkRange_spec bf16OptInRange 0x3D4D (0x3F80 - 0x3D4D + 1) bf16Opt_all_05 x hlo (by omega)
  have hst : ∀ (n : Nat) (f : Nat → Bool), strictNat n f = f n := fun n f => by cases n <;> rfl
  simp only [bf16OptInRange, hst, Bool.and_eq_true, Nat.ble_eq] at h
  exact bf16_of_range_1_128 h.1 h.2

end MuonNsDyadic
