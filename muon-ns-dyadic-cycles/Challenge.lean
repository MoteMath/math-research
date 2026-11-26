/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonNsDyadic.Defs

/-!
# Trusted Challenge Statements (`muon-ns-dyadic-cycles`)

Universal and bit-exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Jordan BF16 non-unit coefficient sum `11/16 ≠ 1`, exact period-2 limit cycle `{11/16, 71/64}`,
   and exact `23/64` worst-case `[0.01, 1]` deviation (unfixable by FP32 inner accumulation).
2. Exact BF16 parenthesization bifurcation of Jordan's quintic:
   Muon matrix-form (period 2, err `23/64`), Monomial (period 4, err `11/32`),
   and Horner (period 8, err `87/256`).
3. GPU-discovered FP8-E4M3FN globally optimal dyadic quintic `(2, -9/8, 1/8)`:
   `a + b + c = 1`, `p'(1) = -3/4`, exact zero (`0`) 5-step error across all 28
   representable values in `[0.05, 1]` with zero NaN/overflow across all 56 unit values.
4. GPU-discovered BF16 globally optimal dyadic quintic `(35/16, -31/16, 3/4)`:
   `a + b + c = 1`, `p'(1) = 1/8`, exact period-1 fixed point, and `≤ 1/128` (1 BF16 ULP,
   `44x` tighter than Jordan) confinement across all 564 BF16 values in `[0.05, 1]`.
5. Exact 1-ULP overshoot instability cliffs of Polar-Express 5-step in BF16 (`129/128 → +Inf`)
   and FP8-E4M3FN (`9/8 → NaN`), Jordan FP8 cliff (`11/8 → NaN`), and MXFP4-E2M1 saturation
   of Jordan `(3, -4, 2)` to `6` across all non-unit positive values.
6. Universal stationary quintic slope-vs-fixed-point Pareto law over `Rat`, formally explaining
   the 2-phase high-slope + unit-fixed-point hybrid architecture.
-/

namespace MuonNsDyadicChallenge

open MuonNsDyadic

/-- Theorem 1 (`jordan_bf16_nonunit_sum_and_period2_limit_cycle`). -/
theorem jordan_bf16_nonunit_sum_and_period2_limit_cycle :
    (fpToRat bf16Spec jordanBf16A = (55 / 16 : Rat) ∧
     fpToRat bf16Spec jordanBf16B = (-153 / 32 : Rat) ∧
     fpToRat bf16Spec jordanBf16C = (65 / 32 : Rat)) ∧
    ((55 / 16 : Rat) + (-153 / 32 : Rat) + (65 / 32 : Rat) = (11 / 16 : Rat) ∧
     (11 / 16 : Rat) ≠ 1 ∧
     quinticEval (55 / 16) (-153 / 32) (65 / 32) 1 = (11 / 16 : Rat) ∧
     ratAbs (quinticEval (55 / 16) (-153 / 32) (65 / 32) 1 - 1) = (5 / 16 : Rat) ∧
     quinticEval (55 / 16) (-153 / 32) (65 / 32) (11 / 16) = (37634267 / 33554432 : Rat) ∧
     (1 : Rat) < quinticEval (55 / 16) (-153 / 32) (65 / 32) (11 / 16)) ∧
    (quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C bf16One = 0x3F30 ∧
     quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 0x3F30 = 0x3F8E ∧
     quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 0x3F8E = 0x3F30 ∧
     fpToRat bf16Spec 0x3F30 = (11 / 16 : Rat) ∧
     fpToRat bf16Spec 0x3F8E = (71 / 64 : Rat) ∧
     (0x3F30 : Nat) ≠ 0x3F8E) ∧
    (quinticIter bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 5 0x3CA6 = 0x3F24 ∧
     fpToRat bf16Spec 0x3CA6 = (83 / 4096 : Rat) ∧
     fpToRat bf16Spec 0x3F24 = (41 / 64 : Rat) ∧
     ratAbs (fpToRat bf16Spec 0x3F24 - 1) = (23 / 64 : Rat)) ∧
    (∀ x : Nat, 0x3C24 ≤ x → x ≤ 0x3F80 →
      let y := quinticIter bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 5 x
      fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (23 / 64 : Rat)) := by
  sorry

/-- Theorem 2 (`jordan_bf16_parenthesization_bifurcation`). -/
theorem jordan_bf16_parenthesization_bifurcation :
    (quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C bf16One = 0x3F30 ∧
     quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 0x3F30 = 0x3F8E ∧
     quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 0x3F8E = 0x3F30 ∧
     quinticIter bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 2 0x3F30 = 0x3F30 ∧
     (0x3F30 : Nat) ≠ 0x3F8E) ∧
    (quinticIter bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 5 bf16One = 0x3F2C ∧
     quinticStep bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 0x3F2C = 0x3F92 ∧
     quinticStep bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 0x3F92 = 0x3F44 ∧
     quinticStep bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 0x3F44 = 0x3F82 ∧
     quinticStep bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 0x3F82 = 0x3F2C ∧
     fpToRat bf16Spec 0x3F2C = (43 / 64 : Rat) ∧
     fpToRat bf16Spec 0x3F92 = (73 / 64 : Rat) ∧
     fpToRat bf16Spec 0x3F44 = (49 / 64 : Rat) ∧
     fpToRat bf16Spec 0x3F82 = (65 / 64 : Rat) ∧
     ([0x3F2C, 0x3F92, 0x3F44, 0x3F82] : List Nat).Nodup ∧
     quinticIter bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 5 0x3CA2 = 0x3F28 ∧
     ratAbs (fpToRat bf16Spec 0x3F28 - 1) = (11 / 32 : Rat)) ∧
    (∀ x : Nat, 0x3C24 ≤ x → x ≤ 0x3F80 →
      let y := quinticIter bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 5 x
      fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (11 / 32 : Rat)) ∧
    (quinticIter bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 2 bf16One = 0x3F90 ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F90 = 0x3F3D ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F3D = 0x3F86 ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F86 = 0x3F2C ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F2C = 0x3F92 ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F92 = 0x3F44 ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F44 = 0x3F82 ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F82 = 0x3F2F ∧
     quinticStep bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 0x3F2F = 0x3F90 ∧
     ([0x3F90, 0x3F3D, 0x3F86, 0x3F2C, 0x3F92, 0x3F44, 0x3F82, 0x3F2F] : List Nat).Nodup ∧
     quinticIter bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 5 0x3CA2 = 0x3F29 ∧
     ratAbs (fpToRat bf16Spec 0x3F29 - 1) = (87 / 256 : Rat)) ∧
    (∀ x : Nat, 0x3C24 ≤ x → x ≤ 0x3F80 →
      let y := quinticIter bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 5 x
      fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (87 / 256 : Rat)) := by
  sorry

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
  sorry

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
  sorry

/-- Theorem 5 (`polar_express_bf16_fp8_one_ulp_overshoot_cliff`). -/
theorem polar_express_bf16_fp8_one_ulp_overshoot_cliff :
    (fpToRat bf16Spec 0x3F81 = (129 / 128 : Rat) ∧
     quinticScheduleIter bf16Spec .horner polarExpressBf16 0x3F81 = bf16PosInf ∧
     fpIsInf bf16Spec (quinticScheduleIter bf16Spec .horner polarExpressBf16 0x3F81) = true ∧
     quinticScheduleIter bf16Spec .monomial polarExpressBf16 0x3F81 = bf16PosInf ∧
     fpIsInf bf16Spec (quinticScheduleIter bf16Spec .monomial polarExpressBf16 0x3F81) = true ∧
     fpIsFinite bf16Spec (quinticScheduleIter bf16Spec .horner polarExpressBf16 bf16One) = true) ∧
    (fpToRat fp8E4M3FNSpec 0x39 = (9 / 8 : Rat) ∧
     quinticScheduleIter fp8E4M3FNSpec .horner polarExpressFp8 0x39 = fp8NaN ∧
     fpIsNaN fp8E4M3FNSpec (quinticScheduleIter fp8E4M3FNSpec .horner polarExpressFp8 0x39) = true ∧
     fpIsFinite fp8E4M3FNSpec (quinticScheduleIter fp8E4M3FNSpec .horner polarExpressFp8 fp8One) = true ∧
     fpToRat fp8E4M3FNSpec 0x3B = (11 / 8 : Rat) ∧
     quinticIter fp8E4M3FNSpec .muonMatForm jordanFp8A jordanFp8B jordanFp8C 5 0x3B = fp8NaN ∧
     fpIsNaN fp8E4M3FNSpec (quinticIter fp8E4M3FNSpec .muonMatForm jordanFp8A jordanFp8B jordanFp8C 5 0x3B) = true) ∧
    (fpToRat mxfp4E2M1Spec jordanMxfp4A = (3 : Rat) ∧
     fpToRat mxfp4E2M1Spec jordanMxfp4B = (-4 : Rat) ∧
     fpToRat mxfp4E2M1Spec jordanMxfp4C = (2 : Rat) ∧
     fpToRat mxfp4E2M1Spec mxfp4Six = (6 : Rat)) ∧
    (∀ x : Nat, 1 ≤ x → x ≤ 7 → x ≠ mxfp4One →
      quinticIter mxfp4E2M1Spec .monomial jordanMxfp4A jordanMxfp4B jordanMxfp4C 5 x = mxfp4Six ∧
      quinticIter mxfp4E2M1Spec .horner jordanMxfp4A jordanMxfp4B jordanMxfp4C 5 x = mxfp4Six) ∧
    (∀ x : Nat, 1 ≤ x → x ≤ 3 →
      quinticIter mxfp4E2M1Spec .horner classicNsMxfp4A classicNsMxfp4B classicNsMxfp4C 5 x = mxfp4One) := by
  sorry

/-- Theorem 6 (`stationary_quintic_slope_vs_fixedpoint_pareto`). -/
theorem stationary_quintic_slope_vs_fixedpoint_pareto :
    (∀ a b c : Rat,
      quinticDeriv a b c 0 = a ∧
      quinticEval a b c 1 = a + b + c ∧
      quinticDeriv a b c 1 = a + 3 * b + 5 * c) ∧
    (∀ a b c : Rat, a + b + c = 1 →
      quinticDeriv a b c 1 = 3 - 2 * a + 2 * c ∧
      quinticEval a b c (1 / 2) = (12 * a + 4 - 3 * c) / 32 ∧
      quinticSecondDeriv a b c 1 = 6 - 6 * a + 14 * c ∧
      (ratAbs (quinticDeriv a b c 1) < 1 ↔ (a - 2 < c ∧ c < a - 1)) ∧
      (quinticDeriv a b c 1 = 0 ↔ (c = a - 3 / 2 ∧ b = 5 / 2 - 2 * a))) ∧
    (∀ a b c : Rat, a + b + c = 1 → quinticDeriv a b c 1 < 1 →
      (9 * a + 7) / 32 < quinticEval a b c (1 / 2) ∧
      ((25 / 9 : Rat) ≤ a → (1 : Rat) < quinticEval a b c (1 / 2)) ∧
      ((3 : Rat) ≤ a → (17 / 16 : Rat) < quinticEval a b c (1 / 2))) ∧
    (∀ a b c : Rat, a + b + c = 1 → quinticEval a b c (1 / 2) ≤ 1 → (3 : Rat) < a →
      (7 / 3 : Rat) < quinticDeriv a b c 1) ∧
    (∀ a b c : Rat, a + b + c = 1 → (-1 : Rat) < quinticDeriv a b c 1 → (3 : Rat) < a →
      (2 : Rat) < quinticSecondDeriv a b c 1) ∧
    ((35 / 16 : Rat) < 25 / 9 ∧
     (35 / 16 : Rat) + (-31 / 16 : Rat) + (3 / 4 : Rat) = 1 ∧
     ratAbs (quinticDeriv (35 / 16) (-31 / 16) (3 / 4) 1) < 1 ∧
     quinticEval (35 / 16) (-31 / 16) (3 / 4) (1 / 2) < 1 ∧
     (2 : Rat) < 25 / 9 ∧
     (2 : Rat) + (-9 / 8 : Rat) + (1 / 8 : Rat) = 1 ∧
     ratAbs (quinticDeriv 2 (-9 / 8) (1 / 8) 1) < 1 ∧
     quinticEval 2 (-9 / 8) (1 / 8) (1 / 2) < 1) := by
  sorry

end MuonNsDyadicChallenge
