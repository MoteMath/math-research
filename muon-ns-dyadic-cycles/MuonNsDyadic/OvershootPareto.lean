/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonNsDyadic.Defs
import MuonNsDyadic.RatOrder

/-!
# Polar-Express 1-ULP Overshoot Cliffs, MXFP4 Saturation, and Stationary Quintic Pareto Law (Theorems 5–6)

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
5. `polar_express_bf16_fp8_one_ulp_overshoot_cliff`:
   Exact 1-ULP overshoot divergence of Polar-Express 5-step at `129/128` (`0x3F81`) in BF16
   (`→ +Inf`) and `9/8` (`0x39`) in FP8-E4M3FN (`→ NaN`), Jordan's FP8 cliff at `11/8` (`0x3B`),
   and exact MXFP4-E2M1 saturation of Jordan `(3, -4, 2)` to `6` across all non-unit positive values.
6. `stationary_quintic_slope_vs_fixedpoint_pareto`:
   Universal exact algebraic tradeoff over `Rat` between small-singular-value slope `p'(0) = a`,
   unit fixed-point condition `a + b + c = 1`, stability `|p'(1)| < 1`, and interior overshoot
   `p(1/2) > (9a + 7)/32`, formally explaining the 2-phase high-slope + unit-fixed-point hybrid.
-/

namespace MuonNsDyadic

private def mxfp4JordanSaturates (x : Nat) : Bool :=
  (x == mxfp4One) ||
  ((quinticIter mxfp4E2M1Spec .monomial jordanMxfp4A jordanMxfp4B jordanMxfp4C 5 x == mxfp4Six) &&
   (quinticIter mxfp4E2M1Spec .horner jordanMxfp4A jordanMxfp4B jordanMxfp4C 5 x == mxfp4Six))

private theorem mxfp4Jordan_all_sat :
    checkRange mxfp4JordanSaturates 1 7 = true := by
  decide +kernel

private def mxfp4ClassicConverges (x : Nat) : Bool :=
  quinticIter mxfp4E2M1Spec .horner classicNsMxfp4A classicNsMxfp4B classicNsMxfp4C 5 x == mxfp4One

private theorem mxfp4Classic_1_to_3 :
    checkRange mxfp4ClassicConverges 1 3 = true := by
  decide +kernel

/-- Theorem 5 (`polar_express_bf16_fp8_one_ulp_overshoot_cliff`). -/
theorem polar_express_bf16_fp8_one_ulp_overshoot_cliff :
    -- 1. BF16 1-ULP overshoot cliff of Polar-Express at 129/128 (0x3F81) -> +Inf
    (fpToRat bf16Spec 0x3F81 = (129 / 128 : Rat) ∧
     quinticScheduleIter bf16Spec .horner polarExpressBf16 0x3F81 = bf16PosInf ∧
     fpIsInf bf16Spec (quinticScheduleIter bf16Spec .horner polarExpressBf16 0x3F81) = true ∧
     quinticScheduleIter bf16Spec .monomial polarExpressBf16 0x3F81 = bf16PosInf ∧
     fpIsInf bf16Spec (quinticScheduleIter bf16Spec .monomial polarExpressBf16 0x3F81) = true ∧
     fpIsFinite bf16Spec (quinticScheduleIter bf16Spec .horner polarExpressBf16 bf16One) = true) ∧
    -- 2. FP8-E4M3FN 1-ULP overshoot cliff of Polar-Express at 9/8 (0x39) -> NaN, plus Jordan cliff at 11/8 (0x3B)
    (fpToRat fp8E4M3FNSpec 0x39 = (9 / 8 : Rat) ∧
     quinticScheduleIter fp8E4M3FNSpec .horner polarExpressFp8 0x39 = fp8NaN ∧
     fpIsNaN fp8E4M3FNSpec (quinticScheduleIter fp8E4M3FNSpec .horner polarExpressFp8 0x39) = true ∧
     fpIsFinite fp8E4M3FNSpec (quinticScheduleIter fp8E4M3FNSpec .horner polarExpressFp8 fp8One) = true ∧
     fpToRat fp8E4M3FNSpec 0x3B = (11 / 8 : Rat) ∧
     quinticIter fp8E4M3FNSpec .muonMatForm jordanFp8A jordanFp8B jordanFp8C 5 0x3B = fp8NaN ∧
     fpIsNaN fp8E4M3FNSpec (quinticIter fp8E4M3FNSpec .muonMatForm jordanFp8A jordanFp8B jordanFp8C 5 0x3B) = true) ∧
    -- 3. MXFP4-E2M1 saturation of Jordan (3, -4, 2) to 6 on every non-unit positive value, vs Classic NS convergence
    (fpToRat mxfp4E2M1Spec jordanMxfp4A = (3 : Rat) ∧
     fpToRat mxfp4E2M1Spec jordanMxfp4B = (-4 : Rat) ∧
     fpToRat mxfp4E2M1Spec jordanMxfp4C = (2 : Rat) ∧
     fpToRat mxfp4E2M1Spec mxfp4Six = (6 : Rat)) ∧
    (∀ x : Nat, 1 ≤ x → x ≤ 7 → x ≠ mxfp4One →
      quinticIter mxfp4E2M1Spec .monomial jordanMxfp4A jordanMxfp4B jordanMxfp4C 5 x = mxfp4Six ∧
      quinticIter mxfp4E2M1Spec .horner jordanMxfp4A jordanMxfp4B jordanMxfp4C 5 x = mxfp4Six) ∧
    (∀ x : Nat, 1 ≤ x → x ≤ 3 →
      quinticIter mxfp4E2M1Spec .horner classicNsMxfp4A classicNsMxfp4B classicNsMxfp4C 5 x = mxfp4One) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · intro x hlo hhi hne
    have h := checkRange_spec mxfp4JordanSaturates 1 7 mxfp4Jordan_all_sat x hlo (by omega)
    simp only [mxfp4JordanSaturates, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    cases h with
    | inl heq => exact False.elim (hne heq)
    | inr hsat => exact hsat
  · intro x hlo hhi
    have h := checkRange_spec mxfp4ClassicConverges 1 3 mxfp4Classic_1_to_3 x hlo (by omega)
    simp only [mxfp4ClassicConverges, beq_iff_eq] at h
    exact h

/-- Theorem 6 (`stationary_quintic_slope_vs_fixedpoint_pareto`). -/
theorem stationary_quintic_slope_vs_fixedpoint_pareto :
    -- 1. Universal odd-quintic derivative and unit identities
    (∀ a b c : Rat,
      quinticDeriv a b c 0 = a ∧
      quinticEval a b c 1 = a + b + c ∧
      quinticDeriv a b c 1 = a + 3 * b + 5 * c) ∧
    -- 2. Exact algebraic elimination under unit fixed point a + b + c = 1
    (∀ a b c : Rat, a + b + c = 1 →
      quinticDeriv a b c 1 = 3 - 2 * a + 2 * c ∧
      quinticEval a b c (1 / 2) = (12 * a + 4 - 3 * c) / 32 ∧
      quinticSecondDeriv a b c 1 = 6 - 6 * a + 14 * c ∧
      (ratAbs (quinticDeriv a b c 1) < 1 ↔ (a - 2 < c ∧ c < a - 1)) ∧
      (quinticDeriv a b c 1 = 0 ↔ (c = a - 3 / 2 ∧ b = 5 / 2 - 2 * a))) ∧
    -- 3. High-slope overshoot & instability Pareto tradeoff under a + b + c = 1
    (∀ a b c : Rat, a + b + c = 1 → quinticDeriv a b c 1 < 1 →
      (9 * a + 7) / 32 < quinticEval a b c (1 / 2) ∧
      ((25 / 9 : Rat) ≤ a → (1 : Rat) < quinticEval a b c (1 / 2)) ∧
      ((3 : Rat) ≤ a → (17 / 16 : Rat) < quinticEval a b c (1 / 2))) ∧
    (∀ a b c : Rat, a + b + c = 1 → quinticEval a b c (1 / 2) ≤ 1 → (3 : Rat) < a →
      (7 / 3 : Rat) < quinticDeriv a b c 1) ∧
    (∀ a b c : Rat, a + b + c = 1 → (-1 : Rat) < quinticDeriv a b c 1 → (3 : Rat) < a →
      (2 : Rat) < quinticSecondDeriv a b c 1) ∧
    -- 4. Phase-2 optimal dyadic schemes sit strictly in the stable non-overshooting regime
    ((35 / 16 : Rat) < 25 / 9 ∧
     (35 / 16 : Rat) + (-31 / 16 : Rat) + (3 / 4 : Rat) = 1 ∧
     ratAbs (quinticDeriv (35 / 16) (-31 / 16) (3 / 4) 1) < 1 ∧
     quinticEval (35 / 16) (-31 / 16) (3 / 4) (1 / 2) < 1 ∧
     (2 : Rat) < 25 / 9 ∧
     (2 : Rat) + (-9 / 8 : Rat) + (1 / 8 : Rat) = 1 ∧
     ratAbs (quinticDeriv 2 (-9 / 8) (1 / 8) 1) < 1 ∧
     quinticEval 2 (-9 / 8) (1 / 8) (1 / 2) < 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide +kernel⟩
  · intro a b c
    unfold quinticDeriv quinticEval
    refine ⟨by grind, by grind, by grind⟩
  · intro a b c hsum
    have hb : b = 1 - a - c := by grind
    have hd1 : quinticDeriv a b c 1 = 3 - 2 * a + 2 * c := by
      unfold quinticDeriv; grind
    have hhalf : quinticEval a b c (1 / 2) = (12 * a + 4 - 3 * c) / 32 := by
      unfold quinticEval; grind
    have hd2 : quinticSecondDeriv a b c 1 = 6 - 6 * a + 14 * c := by
      unfold quinticSecondDeriv; grind
    refine ⟨hd1, hhalf, hd2, ?_, ?_⟩
    · rw [ratAbs_lt_iff, hd1]
      constructor
      · intro ⟨hlo, hhi⟩
        refine ⟨?_, ?_⟩
        · apply rat_lt_of_sub_pos
          have hp := rat_sub_pos hlo
          have eq : c - (a - 2) = (1 / 2 : Rat) * ((3 - 2 * a + 2 * c) - (-1)) := by grind
          rw [eq]
          exact rat_mul_pos (by decide +kernel) hp
        · apply rat_lt_of_sub_pos
          have hp := rat_sub_pos hhi
          have eq : (a - 1) - c = (1 / 2 : Rat) * (1 - (3 - 2 * a + 2 * c)) := by grind
          rw [eq]
          exact rat_mul_pos (by decide +kernel) hp
      · intro ⟨hlo, hhi⟩
        refine ⟨?_, ?_⟩
        · apply rat_lt_of_sub_pos
          have hp := rat_sub_pos hlo
          have eq : (3 - 2 * a + 2 * c) - (-1) = 2 * (c - (a - 2)) := by grind
          rw [eq]
          exact rat_mul_pos (by decide +kernel) hp
        · apply rat_lt_of_sub_pos
          have hp := rat_sub_pos hhi
          have eq : 1 - (3 - 2 * a + 2 * c) = 2 * ((a - 1) - c) := by grind
          rw [eq]
          exact rat_mul_pos (by decide +kernel) hp
    · rw [hd1]
      constructor
      · intro h0
        refine ⟨by grind, by grind⟩
      · intro ⟨hc, _⟩
        grind
  · intro a b c hsum hd1
    have hd1_eq : quinticDeriv a b c 1 = 3 - 2 * a + 2 * c := by
      unfold quinticDeriv; grind
    have hhalf : quinticEval a b c (1 / 2) = (12 * a + 4 - 3 * c) / 32 := by
      unfold quinticEval; grind
    have hc_lt : c < a - 1 := by
      rw [hd1_eq] at hd1
      apply rat_lt_of_sub_pos
      have hp := rat_sub_pos hd1
      have eq : (a - 1) - c = (1 / 2 : Rat) * (1 - (3 - 2 * a + 2 * c)) := by grind
      rw [eq]
      exact rat_mul_pos (by decide +kernel) hp
    have hmain : (9 * a + 7) / 32 < quinticEval a b c (1 / 2) := by
      rw [hhalf]
      apply rat_lt_of_sub_pos
      have hp := rat_sub_pos hc_lt
      have eq : (12 * a + 4 - 3 * c) / 32 - (9 * a + 7) / 32 = (3 / 32 : Rat) * ((a - 1) - c) := by grind
      rw [eq]
      exact rat_mul_pos (by decide +kernel) hp
    refine ⟨hmain, ?_, ?_⟩
    · intro ha
      have h1 : (1 : Rat) ≤ (9 * a + 7) / 32 := by
        apply rat_le_of_sub_nonneg
        have hnn := rat_sub_nonneg ha
        have eq : (9 * a + 7) / 32 - 1 = (9 / 32 : Rat) * (a - 25 / 9) := by grind
        rw [eq]
        exact Rat.mul_nonneg (by decide +kernel) hnn
      exact rat_lt_of_le_of_lt h1 hmain
    · intro ha
      have h1 : (17 / 16 : Rat) ≤ (9 * a + 7) / 32 := by
        apply rat_le_of_sub_nonneg
        have hnn := rat_sub_nonneg ha
        have eq : (9 * a + 7) / 32 - 17 / 16 = (9 / 32 : Rat) * (a - 3) := by grind
        rw [eq]
        exact Rat.mul_nonneg (by decide +kernel) hnn
      exact rat_lt_of_le_of_lt h1 hmain
  · intro a b c hsum hhalf ha
    have hhalf_eq : quinticEval a b c (1 / 2) = (12 * a + 4 - 3 * c) / 32 := by
      unfold quinticEval; grind
    have hd1_eq : quinticDeriv a b c 1 = 3 - 2 * a + 2 * c := by
      unfold quinticDeriv; grind
    rw [hhalf_eq] at hhalf
    rw [hd1_eq]
    apply rat_lt_of_sub_pos
    have hnn1 : (0 : Rat) ≤ 1 - (12 * a + 4 - 3 * c) / 32 := rat_sub_nonneg hhalf
    have hp2 : (0 : Rat) < a - 3 := rat_sub_pos ha
    have h1 : (0 : Rat) ≤ (64 / 3 : Rat) * (1 - (12 * a + 4 - 3 * c) / 32) :=
      Rat.mul_nonneg (by decide +kernel) hnn1
    have h2 : (0 : Rat) < 6 * (a - 3) := rat_mul_pos (by decide +kernel) hp2
    have hsum_pos : (0 : Rat) < (64 / 3 : Rat) * (1 - (12 * a + 4 - 3 * c) / 32) + 6 * (a - 3) := by
      have hle : (0 : Rat) + 6 * (a - 3) ≤ (64 / 3 : Rat) * (1 - (12 * a + 4 - 3 * c) / 32) + 6 * (a - 3) :=
        (Rat.add_le_add_right (c := 6 * (a - 3))).mpr h1
      have h0 : (0 : Rat) + 6 * (a - 3) = 6 * (a - 3) := by grind
      rw [h0] at hle
      exact rat_lt_of_lt_of_le h2 hle
    have eq : (3 - 2 * a + 2 * c) - 7 / 3 =
        (64 / 3 : Rat) * (1 - (12 * a + 4 - 3 * c) / 32) + 6 * (a - 3) := by grind
    rw [eq]
    exact hsum_pos
  · intro a b c hsum hd1 ha
    have hd1_eq : quinticDeriv a b c 1 = 3 - 2 * a + 2 * c := by
      unfold quinticDeriv; grind
    have hd2_eq : quinticSecondDeriv a b c 1 = 6 - 6 * a + 14 * c := by
      unfold quinticSecondDeriv; grind
    rw [hd1_eq] at hd1
    rw [hd2_eq]
    apply rat_lt_of_sub_pos
    have hp1 : (0 : Rat) < (3 - 2 * a + 2 * c) - (-1) := rat_sub_pos hd1
    have hp2 : (0 : Rat) < a - 3 := rat_sub_pos ha
    have h1 : (0 : Rat) < 7 * ((3 - 2 * a + 2 * c) - (-1)) := rat_mul_pos (by decide +kernel) hp1
    have h2 : (0 : Rat) < 8 * (a - 3) := rat_mul_pos (by decide +kernel) hp2
    have hsum_pos : (0 : Rat) < 7 * ((3 - 2 * a + 2 * c) - (-1)) + 8 * (a - 3) := by
      have hle : (0 : Rat) + 8 * (a - 3) ≤ 7 * ((3 - 2 * a + 2 * c) - (-1)) + 8 * (a - 3) :=
        (Rat.add_le_add_right (c := 8 * (a - 3))).mpr (Rat.le_of_lt h1)
      have h0 : (0 : Rat) + 8 * (a - 3) = 8 * (a - 3) := by grind
      rw [h0] at hle
      exact rat_lt_of_lt_of_le h2 hle
    have eq : (6 - 6 * a + 14 * c) - 2 =
        7 * ((3 - 2 * a + 2 * c) - (-1)) + 8 * (a - 3) := by grind
    rw [eq]
    exact hsum_pos

end MuonNsDyadic
