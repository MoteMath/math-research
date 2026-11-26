/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonNsDyadic.Defs

/-!
# Jordan BF16 Limit Cycles & Parenthesization Bifurcation (Theorems 1–2)

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `jordan_bf16_nonunit_sum_and_period2_limit_cycle`:
   Jordan's BF16 coefficients `(55/16, -153/32, 65/32)` satisfy `a + b + c = 11/16 ≠ 1`,
   preventing `x = 1` from being a fixed point even under exact / FP32 inner accumulation,
   and produce the exact period-2 limit cycle `{11/16, 71/64}` under bit-exact BF16 RNE
   Muon matrix-form evaluation with exact worst-case `[0.01, 1]` error `23/64`.
2. `jordan_bf16_parenthesization_bifurcation`:
   Exact period-doubling bifurcation of BF16 Jordan across evaluation orders:
   Muon matrix-form (period 2, err `23/64`), Monomial (period 4, err `11/32`),
   and Horner (period 8, err `87/256`).
-/

namespace MuonNsDyadic

/-- Helper: every BF16 bit-pattern in `[0x3F24, 0x3FAE]` is finite with `|val - 1| ≤ 23/64`. -/
private def bf16ErrLe23_64 (y : Nat) : Bool :=
  fpIsFinite bf16Spec y && decide (ratAbs (fpToRat bf16Spec y - 1) ≤ (23 / 64 : Rat))

private theorem bf16ErrLe23_64_range :
    checkRange bf16ErrLe23_64 0x3F24 (0x3FAE - 0x3F24 + 1) = true := by
  decide +kernel

private theorem bf16_of_range_23_64 {y : Nat} (hlo : 0x3F24 ≤ y) (hhi : y ≤ 0x3FAE) :
    fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (23 / 64 : Rat) := by
  have h := checkRange_spec bf16ErrLe23_64 0x3F24 (0x3FAE - 0x3F24 + 1) bf16ErrLe23_64_range y hlo (by omega)
  simp only [bf16ErrLe23_64, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- Helper: every BF16 bit-pattern in `[0x3F28, 0x3FAC]` is finite with `|val - 1| ≤ 11/32`. -/
private def bf16ErrLe11_32 (y : Nat) : Bool :=
  fpIsFinite bf16Spec y && decide (ratAbs (fpToRat bf16Spec y - 1) ≤ (11 / 32 : Rat))

private theorem bf16ErrLe11_32_range :
    checkRange bf16ErrLe11_32 0x3F28 (0x3FAC - 0x3F28 + 1) = true := by
  decide +kernel

private theorem bf16_of_range_11_32 {y : Nat} (hlo : 0x3F28 ≤ y) (hhi : y ≤ 0x3FAC) :
    fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (11 / 32 : Rat) := by
  have h := checkRange_spec bf16ErrLe11_32 0x3F28 (0x3FAC - 0x3F28 + 1) bf16ErrLe11_32_range y hlo (by omega)
  simp only [bf16ErrLe11_32, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- Helper: every BF16 bit-pattern in `[0x3F29, 0x3FAB]` is finite with `|val - 1| ≤ 87/256`. -/
private def bf16ErrLe87_256 (y : Nat) : Bool :=
  fpIsFinite bf16Spec y && decide (ratAbs (fpToRat bf16Spec y - 1) ≤ (87 / 256 : Rat))

private theorem bf16ErrLe87_256_range :
    checkRange bf16ErrLe87_256 0x3F29 (0x3FAB - 0x3F29 + 1) = true := by
  decide +kernel

private theorem bf16_of_range_87_256 {y : Nat} (hlo : 0x3F29 ≤ y) (hhi : y ≤ 0x3FAB) :
    fpIsFinite bf16Spec y = true ∧ ratAbs (fpToRat bf16Spec y - 1) ≤ (87 / 256 : Rat) := by
  have h := checkRange_spec bf16ErrLe87_256 0x3F29 (0x3FAB - 0x3F29 + 1) bf16ErrLe87_256_range y hlo (by omega)
  simp only [bf16ErrLe87_256, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

private theorem strictNat_eq {α : Type} (n : Nat) (f : Nat → α) : strictNat n f = f n := by
  cases n <;> rfl

private def jordanMuonInRange (x : Nat) : Bool :=
  strictNat (quinticIter bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 5 x) fun y =>
    Nat.ble 0x3F24 y && Nat.ble y 0x3FAE

private theorem jordanMuon_all_01 :
    checkRange jordanMuonInRange 0x3C24 (0x3F80 - 0x3C24 + 1) = true := rfl

private def jordanMonoInRange (x : Nat) : Bool :=
  strictNat (quinticIter bf16Spec .monomial jordanBf16A jordanBf16B jordanBf16C 5 x) fun y =>
    Nat.ble 0x3F28 y && Nat.ble y 0x3FAC

private theorem jordanMono_all_01 :
    checkRange jordanMonoInRange 0x3C24 (0x3F80 - 0x3C24 + 1) = true := rfl

private def jordanHornerInRange (x : Nat) : Bool :=
  strictNat (quinticIter bf16Spec .horner jordanBf16A jordanBf16B jordanBf16C 5 x) fun y =>
    Nat.ble 0x3F29 y && Nat.ble y 0x3FAB

private theorem jordanHorner_all_01 :
    checkRange jordanHornerInRange 0x3C24 (0x3F80 - 0x3C24 + 1) = true := rfl

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
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro x hlo hhi
  have h := checkRange_spec jordanMuonInRange 0x3C24 (0x3F80 - 0x3C24 + 1) jordanMuon_all_01 x hlo (by omega)
  simp only [jordanMuonInRange, strictNat_eq, Bool.and_eq_true, Nat.ble_eq] at h
  exact bf16_of_range_23_64 h.1 h.2

/-- Theorem 2 (`jordan_bf16_parenthesization_bifurcation`). -/
theorem jordan_bf16_parenthesization_bifurcation :
    -- 1. Muon matrix-form: exact period-2 cycle {11/16, 71/64}, worst-case err 23/64
    (quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C bf16One = 0x3F30 ∧
     quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 0x3F30 = 0x3F8E ∧
     quinticStep bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 0x3F8E = 0x3F30 ∧
     quinticIter bf16Spec .muonMatForm jordanBf16A jordanBf16B jordanBf16C 2 0x3F30 = 0x3F30 ∧
     (0x3F30 : Nat) ≠ 0x3F8E) ∧
    -- 2. Monomial: exact period-4 cycle {43/64, 73/64, 49/64, 65/64}, worst-case err 11/32
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
    -- 3. Horner: exact period-8 cycle, worst-case err 87/256
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
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, ?_⟩
  · intro x hlo hhi
    have h := checkRange_spec jordanMonoInRange 0x3C24 (0x3F80 - 0x3C24 + 1) jordanMono_all_01 x hlo (by omega)
    simp only [jordanMonoInRange, strictNat_eq, Bool.and_eq_true, Nat.ble_eq] at h
    exact bf16_of_range_11_32 h.1 h.2
  · intro x hlo hhi
    have h := checkRange_spec jordanHornerInRange 0x3C24 (0x3F80 - 0x3C24 + 1) jordanHorner_all_01 x hlo (by omega)
    simp only [jordanHornerInRange, strictNat_eq, Bool.and_eq_true, Nat.ble_eq] at h
    exact bf16_of_range_87_256 h.1 h.2

end MuonNsDyadic
