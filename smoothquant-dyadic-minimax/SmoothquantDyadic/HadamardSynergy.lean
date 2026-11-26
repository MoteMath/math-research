/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SmoothquantDyadic.RatOrder

/-!
# Exact `SmoothQuant -> Hadamard` Non-Commutation & Parametric `Ω(M^2)` Separation

Proves Headline Theorem 5 (`smoothquant_hadamard_noncommutation_separation`):
1. Exact non-commutation `diag(M, 1) H_2 ≠ H_2 diag(M, 1)` for all `M ≠ 1`.
2. Exact matrix-product preservation for `SQ -> Hadamard`, `Pure Hadamard`, and `Hadamard -> SQ`.
3. `SQ -> Hadamard` achieves `O(1)` error `8 (1/q_W^2 + 1/q_X^2)` independent of `M`.
4. `Pure Hadamard` suffers exact error `(M + 1)^2 (1 + 1/M^2) (1/q_W^2 + 1/q_X^2)`.
5. Every `Hadamard -> diag(s0, s1)` (`s0, s1 > 0`) is at least as bad as `Pure Hadamard`,
   so `SQ -> Hadamard` beats BOTH `Pure Hadamard` and every `Hadamard -> SQ` by strictly more
   than `M^2 / 8` for all `M ≥ 1` (and strictly `> 1` for all `M > 1`)!
-/

namespace SmoothquantDyadic

theorem hadamard_diag_noncommute (M : Rat) (hM : M ≠ 1) :
    mat2Mul (mat2Diag M 1) hadamard2 ≠ mat2Mul hadamard2 (mat2Diag M 1) := by
  intro heq
  have h01 : (mat2Mul (mat2Diag M 1) hadamard2).a01 = (mat2Mul hadamard2 (mat2Diag M 1)).a01 :=
    congrArg Mat2.a01 heq
  simp [mat2Mul, mat2Diag, hadamard2] at h01
  apply hM
  grind

theorem sq_hadamard_exact_product (M : Rat) (hM : M ≠ 0) :
    mat2Scale (1 / 2)
      (mat2Mul (mat2Mul (mat2Mul (antiOutlierW M) (mat2Diag M 1)) hadamard2)
               (mat2Mul hadamard2 (mat2Mul (mat2Diag (1 / M) 1) (antiOutlierX M)))) =
    mat2Mul (antiOutlierW M) (antiOutlierX M) := by
  have h1 : (1 / M) * M = 1 := rat_div_mul_cancel hM
  simp only [mat2Scale, mat2Mul, mat2Diag, hadamard2, antiOutlierW, antiOutlierX]
  congr 1 <;> grind

theorem pure_hadamard_exact_product (M : Rat) :
    mat2Scale (1 / 2)
      (mat2Mul (mat2Mul (antiOutlierW M) hadamard2)
               (mat2Mul hadamard2 (antiOutlierX M))) =
    mat2Mul (antiOutlierW M) (antiOutlierX M) := by
  simp only [mat2Scale, mat2Mul, hadamard2, antiOutlierW, antiOutlierX]
  congr 1 <;> grind

theorem hadamard_sq_exact_product (M s0 s1 : Rat) (hs0 : s0 ≠ 0) (hs1 : s1 ≠ 0) :
    mat2Scale (1 / 2)
      (mat2Mul (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1))
               (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M)))) =
    mat2Mul (antiOutlierW M) (antiOutlierX M) := by
  have h0 : (1 / s0) * s0 = 1 := rat_div_mul_cancel hs0
  have h1 : (1 / s1) * s1 = 1 := rat_div_mul_cancel hs1
  simp only [mat2Scale, mat2Mul, mat2Diag, hadamard2, antiOutlierW, antiOutlierX]
  congr 1 <;> grind

theorem sq_then_hadamard_err_exact (qW qX M : Rat) (hM : M ≠ 0) :
    mat2QuantErrProxy qW qX 2
      (mat2Mul (mat2Mul (antiOutlierW M) (mat2Diag M 1)) hadamard2)
      (mat2Mul hadamard2 (mat2Mul (mat2Diag (1 / M) 1) (antiOutlierX M))) =
    8 * (1 / (qW * qW) + 1 / (qX * qX)) := by
  have h1 : (1 / M) * M = 1 := rat_div_mul_cancel hM
  have hW : mat2Mul (mat2Mul (antiOutlierW M) (mat2Diag M 1)) hadamard2 =
      { a00 := 2, a01 := 0, a10 := 0, a11 := 2 } := by
    simp only [mat2Mul, mat2Diag, hadamard2, antiOutlierW]
    congr 1 <;> grind
  have hX : mat2Mul hadamard2 (mat2Mul (mat2Diag (1 / M) 1) (antiOutlierX M)) =
      { a00 := 2, a01 := 0, a10 := 0, a11 := 2 } := by
    simp only [mat2Mul, mat2Diag, hadamard2, antiOutlierX]
    congr 1 <;> grind
  rw [hW, hX]
  unfold mat2QuantErrProxy mat2MaxSq mat2FrobSq ratMax
  simp only []
  grind

theorem pure_hadamard_err_exact (qW qX M : Rat) (hM : 1 ≤ M) :
    mat2QuantErrProxy qW qX 2
      (mat2Mul (antiOutlierW M) hadamard2)
      (mat2Mul hadamard2 (antiOutlierX M)) =
    (M + 1) * (M + 1) * (1 + 1 / (M * M)) * (1 / (qW * qW) + 1 / (qX * qX)) := by
  have hMpos : 0 < M := rat_lt_of_lt_of_le (by decide) hM
  have hMne : M ≠ 0 := Rat.ne_of_gt hMpos
  have hM2ne : M * M ≠ 0 := Rat.ne_of_gt (rat_mul_pos hMpos hMpos)
  have hWmax : mat2MaxSq (mat2Mul (antiOutlierW M) hadamard2) = (1 / M + 1) * (1 / M + 1) := by
    unfold mat2MaxSq mat2Mul antiOutlierW hadamard2
    have ha : (1 / M) * 1 + 1 * 1 = 1 / M + 1 := by grind
    have hb : (1 / M) * 1 + 1 * -1 = 1 / M - 1 := by grind
    have hc : (1 / M) * 1 + -1 * 1 = 1 / M - 1 := by grind
    have hd : (1 / M) * 1 + -1 * -1 = 1 / M + 1 := by grind
    rw [ha, hb, hc, hd]
    have hle : (1 / M - 1) * (1 / M - 1) ≤ (1 / M + 1) * (1 / M + 1) := by
      apply rat_le_of_sub_nonneg
      have hdiff : (1 / M + 1) * (1 / M + 1) - (1 / M - 1) * (1 / M - 1) = 4 * (1 / M) := by grind
      rw [hdiff]
      exact Rat.mul_nonneg (by decide : (0 : Rat) ≤ 4) (Rat.le_of_lt (rat_div_pos (by decide : (0 : Rat) < 1) hMpos))
    rw [ratMax_eq_left hle, ratMax_eq_right hle, ratMax_eq_left Rat.le_refl]
  have hXmax : mat2MaxSq (mat2Mul hadamard2 (antiOutlierX M)) = (M + 1) * (M + 1) := by
    unfold mat2MaxSq mat2Mul antiOutlierX hadamard2
    have ha : (1 : Rat) * M + 1 * 1 = M + 1 := by grind
    have hb : (1 : Rat) * M + 1 * -1 = M - 1 := by grind
    have hc : (1 : Rat) * M + -1 * 1 = M - 1 := by grind
    have hd : (1 : Rat) * M + -1 * -1 = M + 1 := by grind
    rw [ha, hb, hc, hd]
    have hle : (M - 1) * (M - 1) ≤ (M + 1) * (M + 1) := by
      apply rat_le_of_sub_nonneg
      have hdiff : (M + 1) * (M + 1) - (M - 1) * (M - 1) = 4 * M := by grind
      rw [hdiff]
      exact Rat.mul_nonneg (by decide) (Rat.le_of_lt hMpos)
    rw [ratMax_eq_left hle, ratMax_eq_right hle, ratMax_eq_left Rat.le_refl]
  have hWfrob : mat2FrobSq (mat2Mul (antiOutlierW M) hadamard2) = 4 * (1 + 1 / (M * M)) := by
    unfold mat2FrobSq mat2Mul antiOutlierW hadamard2
    have hinv2 : (1 / M) * (1 / M) = 1 / (M * M) := by
      rw [eq_comm, rat_div_eq_iff hM2ne]
      calc (1 : Rat) = 1 * 1 := by grind
        _ = ((1 / M) * M) * ((1 / M) * M) := by rw [rat_div_mul_cancel hMne]
        _ = (1 / M) * (1 / M) * (M * M) := by grind
    grind
  have hXfrob : mat2FrobSq (mat2Mul hadamard2 (antiOutlierX M)) = 4 * (M * M + 1) := by
    unfold mat2FrobSq mat2Mul antiOutlierX hadamard2
    grind
  unfold mat2QuantErrProxy
  rw [hWmax, hXmax, hWfrob, hXfrob]
  have hcross : (1 / M + 1) * (1 / M + 1) * (M * M + 1) =
      (M + 1) * (M + 1) * (1 + 1 / (M * M)) := by
    have hmul : ((1 / M + 1) * (1 / M + 1) * (M * M + 1) -
        (M + 1) * (M + 1) * (1 + 1 / (M * M))) * (M * M) = 0 := by
      have ha : (1 / M + 1) * M = 1 + M := by
        calc (1 / M + 1) * M = (1 / M) * M + M := by grind
          _ = 1 + M := by rw [rat_div_mul_cancel hMne]
      have hb : (1 + 1 / (M * M)) * (M * M) = M * M + 1 := by
        calc (1 + 1 / (M * M)) * (M * M) = M * M + (1 / (M * M)) * (M * M) := by grind
          _ = M * M + 1 := by rw [rat_div_mul_cancel hM2ne]
      have hc : (1 / M + 1) * (1 / M + 1) * (M * M) = (1 + M) * (1 + M) := by
        calc (1 / M + 1) * (1 / M + 1) * (M * M)
            = ((1 / M + 1) * M) * ((1 / M + 1) * M) := by grind
          _ = (1 + M) * (1 + M) := by rw [ha]
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h => grind
    | inr h => exact False.elim (hM2ne h)
  grind

theorem hadamard_then_sq_ge_pure_hadamard (qW qX M s0 s1 : Rat)
    (hqW : 0 < qW) (hqX : 0 < qX) (hM : 1 ≤ M) (hs0 : 0 < s0) (hs1 : 0 < s1) :
    mat2QuantErrProxy qW qX 2
      (mat2Mul (antiOutlierW M) hadamard2)
      (mat2Mul hadamard2 (antiOutlierX M)) ≤
    mat2QuantErrProxy qW qX 2
      (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1))
      (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M))) := by
  have hMpos : 0 < M := rat_lt_of_lt_of_le (by decide) hM
  have hMne : M ≠ 0 := Rat.ne_of_gt hMpos
  have hM2ne : M * M ≠ 0 := Rat.ne_of_gt (rat_mul_pos hMpos hMpos)
  have hs0ne : s0 ≠ 0 := Rat.ne_of_gt hs0
  have hs1ne : s1 ≠ 0 := Rat.ne_of_gt hs1
  have hs02 : 0 < s0 * s0 := rat_mul_pos hs0 hs0
  have hs12 : 0 < s1 * s1 := rat_mul_pos hs1 hs1
  have hs0inv_sq : (1 / s0) * (1 / s0) = 1 / (s0 * s0) := by
    rw [eq_comm, rat_div_eq_iff (Rat.ne_of_gt hs02)]
    calc (1 : Rat) = 1 * 1 := by grind
      _ = ((1 / s0) * s0) * ((1 / s0) * s0) := by rw [rat_div_mul_cancel hs0ne]
      _ = (1 / s0) * (1 / s0) * (s0 * s0) := by grind
  have hs1inv_sq : (1 / s1) * (1 / s1) = 1 / (s1 * s1) := by
    rw [eq_comm, rat_div_eq_iff (Rat.ne_of_gt hs12)]
    calc (1 : Rat) = 1 * 1 := by grind
      _ = ((1 / s1) * s1) * ((1 / s1) * s1) := by rw [rat_div_mul_cancel hs1ne]
      _ = (1 / s1) * (1 / s1) * (s1 * s1) := by grind
  let a : Rat := 1 / M + 1
  let c : Rat := M + 1
  have hWhs_max_ge : a * a * ratMax (s0 * s0) (s1 * s1) ≤
      mat2MaxSq (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1)) := by
    unfold mat2MaxSq mat2Mul mat2Diag antiOutlierW hadamard2
    have he00 : (((1 / M) * 1 + 1 * 1) * s0 + ((1 / M) * 1 + 1 * -1) * 0) *
        (((1 / M) * 1 + 1 * 1) * s0 + ((1 / M) * 1 + 1 * -1) * 0) = a * a * (s0 * s0) := by grind
    have he11 : (((1 / M) * 1 + -1 * 1) * 0 + ((1 / M) * 1 + -1 * -1) * s1) *
        (((1 / M) * 1 + -1 * 1) * 0 + ((1 / M) * 1 + -1 * -1) * s1) = a * a * (s1 * s1) := by grind
    rw [he00, he11]
    unfold ratMax
    split
    · exact Rat.le_trans (rat_le_ratMax_right _ _) (rat_le_ratMax_right _ _)
    · exact Rat.le_trans (rat_le_ratMax_left _ _) (rat_le_ratMax_left _ _)
  have hXhs_max_ge : c * c * ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) ≤
      mat2MaxSq (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M))) := by
    unfold mat2MaxSq mat2Mul mat2Diag antiOutlierX hadamard2
    have he00 : (1 / s0 * (1 * M + 1 * 1) + 0 * (1 * M + -1 * 1)) *
        (1 / s0 * (1 * M + 1 * 1) + 0 * (1 * M + -1 * 1)) = c * c * (1 / (s0 * s0)) := by
      calc (1 / s0 * (1 * M + 1 * 1) + 0 * (1 * M + -1 * 1)) *
            (1 / s0 * (1 * M + 1 * 1) + 0 * (1 * M + -1 * 1))
          = c * c * ((1 / s0) * (1 / s0)) := by grind
        _ = c * c * (1 / (s0 * s0)) := by rw [hs0inv_sq]
    have he11 : (0 * (1 * M + 1 * -1) + 1 / s1 * (1 * M + -1 * -1)) *
        (0 * (1 * M + 1 * -1) + 1 / s1 * (1 * M + -1 * -1)) = c * c * (1 / (s1 * s1)) := by
      calc (0 * (1 * M + 1 * -1) + 1 / s1 * (1 * M + -1 * -1)) *
            (0 * (1 * M + 1 * -1) + 1 / s1 * (1 * M + -1 * -1))
          = c * c * ((1 / s1) * (1 / s1)) := by grind
        _ = c * c * (1 / (s1 * s1)) := by rw [hs1inv_sq]
    rw [he00, he11]
    unfold ratMax
    split
    · exact Rat.le_trans (rat_le_ratMax_right _ _) (rat_le_ratMax_right _ _)
    · exact Rat.le_trans (rat_le_ratMax_left _ _) (rat_le_ratMax_left _ _)
  have hWhs_frob : mat2FrobSq (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1)) =
      2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1) := by
    unfold mat2FrobSq mat2Mul mat2Diag antiOutlierW hadamard2
    have hinv2 : (1 / M) * (1 / M) = 1 / (M * M) := by
      rw [eq_comm, rat_div_eq_iff hM2ne]
      calc (1 : Rat) = 1 * 1 := by grind
        _ = ((1 / M) * M) * ((1 / M) * M) := by rw [rat_div_mul_cancel hMne]
        _ = (1 / M) * (1 / M) * (M * M) := by grind
    grind
  have hXhs_frob : mat2FrobSq (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M))) =
      2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1)) := by
    unfold mat2FrobSq mat2Mul mat2Diag antiOutlierX hadamard2
    have h0 : (1 / s0 * (1 * M + 1 * 1) + 0 * (1 * M + -1 * 1)) *
        (1 / s0 * (1 * M + 1 * 1) + 0 * (1 * M + -1 * 1)) +
        (1 / s0 * (1 * M + 1 * -1) + 0 * (1 * M + -1 * -1)) *
        (1 / s0 * (1 * M + 1 * -1) + 0 * (1 * M + -1 * -1)) =
        2 * (M * M + 1) * (1 / (s0 * s0)) := by
      calc _ = 2 * (M * M + 1) * ((1 / s0) * (1 / s0)) := by grind
        _ = 2 * (M * M + 1) * (1 / (s0 * s0)) := by rw [hs0inv_sq]
    have h1 : (0 * (1 * M + 1 * 1) + 1 / s1 * (1 * M + -1 * 1)) *
        (0 * (1 * M + 1 * 1) + 1 / s1 * (1 * M + -1 * 1)) +
        (0 * (1 * M + 1 * -1) + 1 / s1 * (1 * M + -1 * -1)) *
        (0 * (1 * M + 1 * -1) + 1 / s1 * (1 * M + -1 * -1)) =
        2 * (M * M + 1) * (1 / (s1 * s1)) := by
      calc _ = 2 * (M * M + 1) * ((1 / s1) * (1 / s1)) := by grind
        _ = 2 * (M * M + 1) * (1 / (s1 * s1)) := by rw [hs1inv_sq]
    grind
  -- Key AM/max inequality: max(p, q) * (1/p + 1/q) ≥ 2 and max(1/p, 1/q) * (p + q) ≥ 2
  have hmax_prod1 : (2 : Rat) ≤ ratMax (s0 * s0) (s1 * s1) * (1 / (s0 * s0) + 1 / (s1 * s1)) := by
    have h1 : 1 ≤ ratMax (s0 * s0) (s1 * s1) * (1 / (s0 * s0)) := by
      have hm := rat_mul_le_mul_of_nonneg_right (rat_le_ratMax_left (s0 * s0) (s1 * s1))
        (Rat.le_of_lt (rat_div_pos (by decide : (0 : Rat) < 1) hs02))
      rw [rat_mul_div_cancel (Rat.ne_of_gt hs02)] at hm
      exact hm
    have h2 : 1 ≤ ratMax (s0 * s0) (s1 * s1) * (1 / (s1 * s1)) := by
      have hm := rat_mul_le_mul_of_nonneg_right (rat_le_ratMax_right (s0 * s0) (s1 * s1))
        (Rat.le_of_lt (rat_div_pos (by decide : (0 : Rat) < 1) hs12))
      rw [rat_mul_div_cancel (Rat.ne_of_gt hs12)] at hm
      exact hm
    have hsum := rat_add_le_add h1 h2
    have heq : ratMax (s0 * s0) (s1 * s1) * (1 / (s0 * s0)) +
        ratMax (s0 * s0) (s1 * s1) * (1 / (s1 * s1)) =
        ratMax (s0 * s0) (s1 * s1) * (1 / (s0 * s0) + 1 / (s1 * s1)) := by grind
    rw [heq] at hsum
    have h2eq : (1 : Rat) + 1 = 2 := by grind
    rw [h2eq] at hsum
    exact hsum
  have hmax_prod2 : (2 : Rat) ≤ ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) * (s0 * s0 + s1 * s1) := by
    have h1 : 1 ≤ ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) * (s0 * s0) := by
      have hm := rat_mul_le_mul_of_nonneg_right
        (rat_le_ratMax_left (1 / (s0 * s0)) (1 / (s1 * s1))) (Rat.le_of_lt hs02)
      rw [rat_div_mul_cancel (Rat.ne_of_gt hs02)] at hm
      exact hm
    have h2 : 1 ≤ ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) * (s1 * s1) := by
      have hm := rat_mul_le_mul_of_nonneg_right
        (rat_le_ratMax_right (1 / (s0 * s0)) (1 / (s1 * s1))) (Rat.le_of_lt hs12)
      rw [rat_div_mul_cancel (Rat.ne_of_gt hs12)] at hm
      exact hm
    have hsum := rat_add_le_add h1 h2
    have heq : ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) * (s0 * s0) +
        ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) * (s1 * s1) =
        ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) * (s0 * s0 + s1 * s1) := by grind
    rw [heq] at hsum
    have h2eq : (1 : Rat) + 1 = 2 := by grind
    rw [h2eq] at hsum
    exact hsum
  rw [pure_hadamard_err_exact qW qX M hM]
  unfold mat2QuantErrProxy
  rw [hWhs_frob, hXhs_frob]
  have hqW2 : 0 < qW * qW := rat_mul_pos hqW hqW
  have hqX2 : 0 < qX * qX := rat_mul_pos hqX hqX
  have hM2p1 : 0 < M * M + 1 := rat_add_pos (rat_mul_pos hMpos hMpos) (by decide)
  have h1pM2 : 0 < 1 + 1 / (M * M) := rat_add_pos (by decide) (rat_div_pos (by decide) (rat_mul_pos hMpos hMpos))
  have hcross : a * a * (M * M + 1) = c * c * (1 + 1 / (M * M)) := by
    have hmul : (a * a * (M * M + 1) - c * c * (1 + 1 / (M * M))) * (M * M) = 0 := by
      have ha : a * M = c := by
        change (1 / M + 1) * M = M + 1
        calc (1 / M + 1) * M = (1 / M) * M + M := by grind
          _ = 1 + M := by rw [rat_div_mul_cancel hMne]
          _ = M + 1 := by grind
      have hb : (1 + 1 / (M * M)) * (M * M) = M * M + 1 := by
        calc (1 + 1 / (M * M)) * (M * M) = M * M + (1 / (M * M)) * (M * M) := by grind
          _ = M * M + 1 := by rw [rat_div_mul_cancel hM2ne]
      have hc : a * a * (M * M) = c * c := by
        calc a * a * (M * M) = (a * M) * (a * M) := by grind
          _ = c * c := by rw [ha]
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h => grind
    | inr h => exact False.elim (hM2ne h)
  -- Bound Term 1
  have hterm1 : 4 * (c * c * (1 + 1 / (M * M))) / (qW * qW) ≤
      mat2MaxSq (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1)) / (qW * qW) *
        (2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1))) := by
    have hstep1 : (a * a * ratMax (s0 * s0) (s1 * s1)) / (qW * qW) *
        (2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1))) ≤
        mat2MaxSq (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1)) / (qW * qW) *
        (2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1))) := by
      have hpos : 0 ≤ 2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1)) :=
        Rat.le_of_lt (rat_mul_pos (rat_mul_pos (by decide) hM2p1)
          (rat_add_pos (rat_div_pos (by decide) hs02) (rat_div_pos (by decide) hs12)))
      have hdiv : (a * a * ratMax (s0 * s0) (s1 * s1)) / (qW * qW) ≤
          mat2MaxSq (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1)) / (qW * qW) := by
        rw [Rat.div_def, Rat.div_def]
        exact rat_mul_le_mul_of_nonneg_right hWhs_max_ge (Rat.le_of_lt (rat_inv_pos hqW2))
      exact rat_mul_le_mul_of_nonneg_right hdiv hpos
    have hstep2 : 4 * (c * c * (1 + 1 / (M * M))) / (qW * qW) ≤
        (a * a * ratMax (s0 * s0) (s1 * s1)) / (qW * qW) *
        (2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1))) := by
      rw [← hcross]
      have hfac_nonneg : 0 ≤ 2 * (a * a * (M * M + 1)) / (qW * qW) :=
        rat_div_nonneg (Rat.mul_nonneg (by decide) (Rat.mul_nonneg (rat_sq_nonneg a) (Rat.le_of_lt hM2p1))) hqW2
      have hm := rat_mul_le_mul_of_nonneg_left hmax_prod1 hfac_nonneg
      have hL : 2 * (a * a * (M * M + 1)) / (qW * qW) * 2 =
          4 * (a * a * (M * M + 1)) / (qW * qW) := by
        rw [Rat.div_def, Rat.div_def]; grind
      have hR : 2 * (a * a * (M * M + 1)) / (qW * qW) *
          (ratMax (s0 * s0) (s1 * s1) * (1 / (s0 * s0) + 1 / (s1 * s1))) =
          (a * a * ratMax (s0 * s0) (s1 * s1)) / (qW * qW) *
          (2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1))) := by
        rw [Rat.div_def, Rat.div_def]; grind
      rw [hL, hR] at hm
      exact hm
    exact Rat.le_trans hstep2 hstep1
  -- Bound Term 2
  have hterm2 : 4 * (c * c * (1 + 1 / (M * M))) / (qX * qX) ≤
      mat2MaxSq (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M))) / (qX * qX) *
        (2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1)) := by
    have hstep1 : (c * c * ratMax (1 / (s0 * s0)) (1 / (s1 * s1))) / (qX * qX) *
        (2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1)) ≤
        mat2MaxSq (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M))) / (qX * qX) *
        (2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1)) := by
      have hpos : 0 ≤ 2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1) :=
        Rat.le_of_lt (rat_mul_pos (rat_mul_pos (by decide) h1pM2) (rat_add_pos hs02 hs12))
      have hdiv : (c * c * ratMax (1 / (s0 * s0)) (1 / (s1 * s1))) / (qX * qX) ≤
          mat2MaxSq (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M))) / (qX * qX) := by
        rw [Rat.div_def, Rat.div_def]
        exact rat_mul_le_mul_of_nonneg_right hXhs_max_ge (Rat.le_of_lt (rat_inv_pos hqX2))
      exact rat_mul_le_mul_of_nonneg_right hdiv hpos
    have hstep2 : 4 * (c * c * (1 + 1 / (M * M))) / (qX * qX) ≤
        (c * c * ratMax (1 / (s0 * s0)) (1 / (s1 * s1))) / (qX * qX) *
        (2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1)) := by
      have hfac_nonneg : 0 ≤ 2 * (c * c * (1 + 1 / (M * M))) / (qX * qX) :=
        rat_div_nonneg (Rat.mul_nonneg (by decide) (Rat.mul_nonneg (rat_sq_nonneg c) (Rat.le_of_lt h1pM2))) hqX2
      have hm := rat_mul_le_mul_of_nonneg_left hmax_prod2 hfac_nonneg
      have hL : 2 * (c * c * (1 + 1 / (M * M))) / (qX * qX) * 2 =
          4 * (c * c * (1 + 1 / (M * M))) / (qX * qX) := by
        rw [Rat.div_def, Rat.div_def]; grind
      have hR : 2 * (c * c * (1 + 1 / (M * M))) / (qX * qX) *
          (ratMax (1 / (s0 * s0)) (1 / (s1 * s1)) * (s0 * s0 + s1 * s1)) =
          (c * c * ratMax (1 / (s0 * s0)) (1 / (s1 * s1))) / (qX * qX) *
          (2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1)) := by
        rw [Rat.div_def, Rat.div_def]; grind
      rw [hL, hR] at hm
      exact hm
    exact Rat.le_trans hstep2 hstep1
  have hsum := rat_add_le_add hterm1 hterm2
  have hdiv : (4 * (c * c * (1 + 1 / (M * M))) / (qW * qW) +
      4 * (c * c * (1 + 1 / (M * M))) / (qX * qX)) / (2 * 2) ≤
      (mat2MaxSq (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1)) / (qW * qW) *
        (2 * (M * M + 1) * (1 / (s0 * s0) + 1 / (s1 * s1))) +
       mat2MaxSq (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M))) / (qX * qX) *
        (2 * (1 + 1 / (M * M)) * (s0 * s0 + s1 * s1))) / (2 * 2) := by
    rw [Rat.div_def, Rat.div_def]
    exact rat_mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt (rat_inv_pos (rat_mul_pos (by decide) (by decide))))
  have hLeq : (4 * (c * c * (1 + 1 / (M * M))) / (qW * qW) +
      4 * (c * c * (1 + 1 / (M * M))) / (qX * qX)) / (2 * 2) =
      c * c * (1 + 1 / (M * M)) * (1 / (qW * qW) + 1 / (qX * qX)) := by
    grind
  rw [hLeq] at hdiv
  exact hdiv

/-! ### Headline Theorem 5 -/

theorem smoothquant_hadamard_noncommutation_separation :
    (∀ M : Rat, M ≠ 1 →
      mat2Mul (mat2Diag M 1) hadamard2 ≠ mat2Mul hadamard2 (mat2Diag M 1)) ∧
    (∀ M : Rat, M ≠ 0 →
      mat2Scale (1 / 2)
        (mat2Mul (mat2Mul (mat2Mul (antiOutlierW M) (mat2Diag M 1)) hadamard2)
                 (mat2Mul hadamard2 (mat2Mul (mat2Diag (1 / M) 1) (antiOutlierX M)))) =
      mat2Mul (antiOutlierW M) (antiOutlierX M) ∧
      mat2Scale (1 / 2)
        (mat2Mul (mat2Mul (antiOutlierW M) hadamard2)
                 (mat2Mul hadamard2 (antiOutlierX M))) =
      mat2Mul (antiOutlierW M) (antiOutlierX M)) ∧
    (∀ M s0 s1 : Rat, s0 ≠ 0 → s1 ≠ 0 →
      mat2Scale (1 / 2)
        (mat2Mul (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1))
                 (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M)))) =
      mat2Mul (antiOutlierW M) (antiOutlierX M)) ∧
    (∀ qW qX M s0 s1 : Rat, 0 < qW → 0 < qX → 1 ≤ M → 0 < s0 → 0 < s1 →
      let Wsh := mat2Mul (mat2Mul (antiOutlierW M) (mat2Diag M 1)) hadamard2
      let Xsh := mat2Mul hadamard2 (mat2Mul (mat2Diag (1 / M) 1) (antiOutlierX M))
      let Wh  := mat2Mul (antiOutlierW M) hadamard2
      let Xh  := mat2Mul hadamard2 (antiOutlierX M)
      let Whs := mat2Mul Wh (mat2Diag s0 s1)
      let Xhs := mat2Mul (mat2Diag (1 / s0) (1 / s1)) Xh
      mat2QuantErrProxy qW qX 2 Wsh Xsh = 8 * (1 / (qW * qW) + 1 / (qX * qX)) ∧
      mat2QuantErrProxy qW qX 2 Wh Xh =
        (M + 1) * (M + 1) * (1 + 1 / (M * M)) * (1 / (qW * qW) + 1 / (qX * qX)) ∧
      mat2QuantErrProxy qW qX 2 Wh Xh / mat2QuantErrProxy qW qX 2 Wsh Xsh =
        (M + 1) * (M + 1) * (1 + 1 / (M * M)) / 8 ∧
      (M * M) / 8 < mat2QuantErrProxy qW qX 2 Wh Xh / mat2QuantErrProxy qW qX 2 Wsh Xsh ∧
      mat2QuantErrProxy qW qX 2 Wh Xh ≤ mat2QuantErrProxy qW qX 2 Whs Xhs ∧
      (M * M) / 8 < mat2QuantErrProxy qW qX 2 Whs Xhs / mat2QuantErrProxy qW qX 2 Wsh Xsh ∧
      (1 < M →
        mat2QuantErrProxy qW qX 2 Wsh Xsh < mat2QuantErrProxy qW qX 2 Wh Xh ∧
        mat2QuantErrProxy qW qX 2 Wsh Xsh < mat2QuantErrProxy qW qX 2 Whs Xhs)) := by
  refine ⟨hadamard_diag_noncommute, ?_, hadamard_sq_exact_product, ?_⟩
  · intro M hM
    exact ⟨sq_hadamard_exact_product M hM, pure_hadamard_exact_product M⟩
  · intro qW qX M s0 s1 hqW hqX hM hs0 hs1
    intro Wsh Xsh Wh Xh Whs Xhs
    have hMpos : 0 < M := rat_lt_of_lt_of_le (by decide) hM
    have hMne : M ≠ 0 := Rat.ne_of_gt hMpos
    have hsqh := sq_then_hadamard_err_exact qW qX M hMne
    have hph := pure_hadamard_err_exact qW qX M hM
    have hge := hadamard_then_sq_ge_pure_hadamard qW qX M s0 s1 hqW hqX hM hs0 hs1
    have hqsum_pos : 0 < 1 / (qW * qW) + 1 / (qX * qX) :=
      rat_add_pos (rat_div_pos (by decide) (rat_mul_pos hqW hqW))
                  (rat_div_pos (by decide) (rat_mul_pos hqX hqX))
    have hWsh_pos : 0 < mat2QuantErrProxy qW qX 2 Wsh Xsh := by
      rw [hsqh]
      exact rat_mul_pos (by decide) hqsum_pos
    have hrat : mat2QuantErrProxy qW qX 2 Wh Xh / mat2QuantErrProxy qW qX 2 Wsh Xsh =
        (M + 1) * (M + 1) * (1 + 1 / (M * M)) / 8 := by
      rw [hph, hsqh]
      apply rat_div_eq_of_cross (Rat.ne_of_gt (rat_mul_pos (by decide) hqsum_pos)) (by decide)
      grind
    have hgt_M2 : (M * M) / 8 < (M + 1) * (M + 1) * (1 + 1 / (M * M)) / 8 := by
      apply rat_div_lt_div_of_cross (by decide) (by decide)
      have hsub : (M + 1) * (M + 1) * (1 + 1 / (M * M)) - M * M =
          (2 * M + 1) + (M + 1) * (M + 1) / (M * M) := by
        rw [Rat.div_def, Rat.div_def]; grind
      have hpos : 0 < (M + 1) * (M + 1) * (1 + 1 / (M * M)) - M * M := by
        rw [hsub]
        exact rat_add_pos (rat_add_pos (rat_mul_pos (by decide) hMpos) (by decide))
          (rat_div_pos (rat_mul_pos (rat_add_pos hMpos (by decide)) (rat_add_pos hMpos (by decide)))
                       (rat_mul_pos hMpos hMpos))
      have hlt := rat_lt_of_sub_pos hpos
      exact rat_mul_lt_mul_of_pos_right hlt (by decide)
    have hgt_ph : (M * M) / 8 < mat2QuantErrProxy qW qX 2 Wh Xh / mat2QuantErrProxy qW qX 2 Wsh Xsh := by
      rw [hrat]; exact hgt_M2
    have hgt_hs : (M * M) / 8 < mat2QuantErrProxy qW qX 2 Whs Xhs / mat2QuantErrProxy qW qX 2 Wsh Xsh := by
      have hdiv_le : mat2QuantErrProxy qW qX 2 Wh Xh / mat2QuantErrProxy qW qX 2 Wsh Xsh ≤
          mat2QuantErrProxy qW qX 2 Whs Xhs / mat2QuantErrProxy qW qX 2 Wsh Xsh := by
        rw [Rat.div_def, Rat.div_def]
        exact rat_mul_le_mul_of_nonneg_right hge (Rat.le_of_lt (rat_inv_pos hWsh_pos))
      exact rat_lt_of_lt_of_le hgt_ph hdiv_le
    refine ⟨hsqh, hph, hrat, hgt_ph, hge, hgt_hs, ?_⟩
    intro hMgt1
    have hstrict_fac : (8 : Rat) < (M + 1) * (M + 1) * (1 + 1 / (M * M)) := by
      apply rat_lt_of_sub_pos
      have hM2 : 0 < M * M := rat_mul_pos hMpos hMpos
      have hM2ne : M * M ≠ 0 := Rat.ne_of_gt hM2
      have hfac : (M + 1) * (M + 1) * (1 + 1 / (M * M)) - 8 =
          (M - 1) * (M - 1) * (M * M + 4 * M + 1) / (M * M) := by
        rw [eq_comm, rat_div_eq_iff hM2ne]
        have hb : (1 + 1 / (M * M)) * (M * M) = M * M + 1 := by
          calc (1 + 1 / (M * M)) * (M * M) = M * M + (1 / (M * M)) * (M * M) := by grind
            _ = M * M + 1 := by rw [rat_div_mul_cancel hM2ne]
        have h1 : (M + 1) * (M + 1) * (1 + 1 / (M * M)) * (M * M) =
            (M + 1) * (M + 1) * (M * M + 1) := by
          calc (M + 1) * (M + 1) * (1 + 1 / (M * M)) * (M * M)
              = (M + 1) * (M + 1) * ((1 + 1 / (M * M)) * (M * M)) := by grind
            _ = (M + 1) * (M + 1) * (M * M + 1) := by rw [hb]
        grind
      rw [hfac]
      have hMm1 : 0 < M - 1 := rat_sub_pos hMgt1
      have hpoly : 0 < M * M + 4 * M + 1 :=
        rat_add_pos (rat_add_pos hM2 (rat_mul_pos (by decide) hMpos)) (by decide)
      exact rat_div_pos (rat_mul_pos (rat_mul_pos hMm1 hMm1) hpoly) hM2
    have hlt_ph : mat2QuantErrProxy qW qX 2 Wsh Xsh < mat2QuantErrProxy qW qX 2 Wh Xh := by
      rw [hsqh, hph]
      exact rat_mul_lt_mul_of_pos_right hstrict_fac hqsum_pos
    exact ⟨hlt_ph, rat_lt_of_lt_of_le hlt_ph hge⟩

end SmoothquantDyadic
