/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltaNetHouseholderE8.HouseholderSpectral

/-!
# Theorems 2 & 3: Quantized Unit-Norm Supremum & Universal 2-ULP Safe Ceiling

Proves:
- Theorem 2 (`quantized_unit_norm_supremum_exact`):
  Squared-norm bound `S_max^(1)(m) = ((2^{m+1} + 2) / (2^{m+1} + 1))^2 > 1` for all `m ≥ 1`
  (valid for vectors whose coordinates satisfy the hypothesised ratio `r_m`; not shown attained),
  exact evaluations for `BF16` (`m = 7`), `FP16` (`m = 10`), `FP8-E4M3` (`m = 3`),
  and the exact `287 / 256` `FP8-E4M3` witness vector.
- Theorem 3 (`universal_two_ulp_safe_ceiling_theorem`):
  For ALL `m ≥ 2`:
  - `1` ULP below `2` (`β_1(m) = 2 - 2^{-m}`) satisfies `β_1(m) * S_max^(1)(m) > 2`.
  - `2` ULPs below `2` (`β_2(m) = 2 - 2^{1-m}`) satisfies `β_2(m) * S_max^(1)(m) < 2`,
    yielding exact dyadic ceilings `127/64` (`BF16`), `1023/512` (`FP16`), `7/4` (`FP8-E4M3`),
    and Householder spectral contraction for every `k` with `‖k‖² ≤ S_max^(1)(m)`.
-/

namespace DeltaNetHouseholderE8

theorem pow2Rat_succ_add_one_pos (m : Nat) : (0 : Rat) < pow2Rat (m + 1) + 1 :=
  rat_add_pos (pow2Rat_pos (m + 1)) (by decide)

theorem pow2Rat_succ_add_one_ne_zero (m : Nat) : pow2Rat (m + 1) + 1 ≠ 0 :=
  Rat.ne_of_gt (pow2Rat_succ_add_one_pos m)

theorem rneBinadeBottomRatio_eq (m : Nat) :
    rneBinadeBottomRatio m = (pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1) := by
  unfold rneBinadeBottomRatio invPow2Rat
  have hp : pow2Rat (m + 1) ≠ 0 := pow2Rat_ne_zero (m + 1)
  have hpm : pow2Rat m ≠ 0 := pow2Rat_ne_zero m
  have hden1 : (1 : Rat) + 1 / pow2Rat (m + 1) ≠ 0 := by
    have hpos : (0 : Rat) < 1 + 1 / pow2Rat (m + 1) :=
      rat_add_pos (by decide) (rat_div_pos (by decide) (pow2Rat_pos (m + 1)))
    exact Rat.ne_of_gt hpos
  have hden2 : pow2Rat (m + 1) + 1 ≠ 0 := pow2Rat_succ_add_one_ne_zero m
  apply (rat_div_eq_iff hden1).mpr
  apply Eq.symm
  have hmul : (pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1) * (1 + 1 / pow2Rat (m + 1)) =
      ((pow2Rat (m + 1) + 2) * (1 + 1 / pow2Rat (m + 1))) / (pow2Rat (m + 1) + 1) := by
    rw [Rat.div_def, Rat.div_def]; grind
  rw [hmul]
  apply (rat_div_eq_iff hden2).mpr
  have h1 : (1 + 1 / pow2Rat (m + 1)) * pow2Rat (m + 1) = pow2Rat (m + 1) + 1 := by
    have hcancel := rat_div_mul_cancel (a := (1 : Rat)) hp
    grind
  have h2 : (1 + 1 / pow2Rat m) * pow2Rat (m + 1) = pow2Rat (m + 1) + 2 := by
    rw [pow2Rat_succ m]
    have hcancel := rat_div_mul_cancel (a := (1 : Rat)) hpm
    grind
  have h3 : ((pow2Rat (m + 1) + 2) * (1 + 1 / pow2Rat (m + 1))) * pow2Rat (m + 1) =
      ((1 + 1 / pow2Rat m) * (pow2Rat (m + 1) + 1)) * pow2Rat (m + 1) := by
    have hl : (pow2Rat (m + 1) + 2) * (1 + 1 / pow2Rat (m + 1)) * pow2Rat (m + 1) =
        (pow2Rat (m + 1) + 2) * ((1 + 1 / pow2Rat (m + 1)) * pow2Rat (m + 1)) := by grind
    have hr : (1 + 1 / pow2Rat m) * (pow2Rat (m + 1) + 1) * pow2Rat (m + 1) =
        ((1 + 1 / pow2Rat m) * pow2Rat (m + 1)) * (pow2Rat (m + 1) + 1) := by grind
    rw [hl, hr, h1, h2]
  have h4 := congrArg (fun x => x * (pow2Rat (m + 1))⁻¹) h3
  have hcancelL : ((pow2Rat (m + 1) + 2) * (1 + 1 / pow2Rat (m + 1))) * pow2Rat (m + 1) *
      (pow2Rat (m + 1))⁻¹ = (pow2Rat (m + 1) + 2) * (1 + 1 / pow2Rat (m + 1)) := by
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hp, Rat.mul_one]
  have hcancelR : ((1 + 1 / pow2Rat m) * (pow2Rat (m + 1) + 1)) * pow2Rat (m + 1) *
      (pow2Rat (m + 1))⁻¹ = (1 + 1 / pow2Rat m) * (pow2Rat (m + 1) + 1) := by
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hp, Rat.mul_one]
  rw [hcancelL, hcancelR] at h4
  exact h4

theorem sMax1_eq_ratio_sq (m : Nat) :
    sMax1 m = rneBinadeBottomRatio m * rneBinadeBottomRatio m := by
  unfold sMax1
  rw [rneBinadeBottomRatio_eq]

theorem sMax1_decomp (m : Nat) :
    sMax1 m = 1 + (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) := by
  unfold sMax1
  have hden : pow2Rat (m + 1) + 1 ≠ 0 := pow2Rat_succ_add_one_ne_zero m
  have hden2 : (pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hden h
    | inr h => exact hden h
  have hdiv : ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) *
      ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) =
      ((pow2Rat (m + 1) + 2) * (pow2Rat (m + 1) + 2)) /
      ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) := by
    rw [Rat.div_def, Rat.div_def]
    have hinv : ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))⁻¹ =
        (pow2Rat (m + 1) + 1)⁻¹ * (pow2Rat (m + 1) + 1)⁻¹ := by
      have h1 : ((pow2Rat (m + 1) + 1)⁻¹ * (pow2Rat (m + 1) + 1)⁻¹) *
          ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) = 1 := by
        have hre : ((pow2Rat (m + 1) + 1)⁻¹ * (pow2Rat (m + 1) + 1)⁻¹) *
            ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) =
            ((pow2Rat (m + 1) + 1)⁻¹ * (pow2Rat (m + 1) + 1)) *
            ((pow2Rat (m + 1) + 1)⁻¹ * (pow2Rat (m + 1) + 1)) := by grind
        rw [hre, Rat.inv_mul_cancel _ hden, Rat.mul_one]
      have h2 := congrArg (fun x => x * ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))⁻¹) h1
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hden2, Rat.mul_one, Rat.one_mul] at h2
      exact h2.symm
    rw [hinv]; grind
  rw [hdiv]
  apply (rat_div_eq_iff hden2).mpr
  have hcancel := rat_div_mul_cancel (a := pow2Rat (m + 2) + 3) hden2
  have hsucc : pow2Rat (m + 2) = 2 * pow2Rat (m + 1) := pow2Rat_succ (m + 1)
  have hexp : (1 + (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) *
      ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) =
      (pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1) + (pow2Rat (m + 2) + 3) := by
    have hdist : (1 + (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) *
        ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) =
        (pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1) +
        ((pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) *
        ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) := by grind
    rw [hdist, hcancel]
  rw [hexp, hsucc]
  grind

theorem one_lt_sMax1 (m : Nat) : (1 : Rat) < sMax1 m := by
  rw [sMax1_decomp]
  have hnum : (0 : Rat) < pow2Rat (m + 2) + 3 :=
    rat_add_pos (pow2Rat_pos (m + 2)) (by decide)
  have hden : (0 : Rat) < (pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1) :=
    rat_mul_pos (pow2Rat_succ_add_one_pos m) (pow2Rat_succ_add_one_pos m)
  have hfrac : (0 : Rat) < (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) :=
    rat_div_pos hnum hden
  apply rat_lt_of_sub_pos
  have heq : 1 + (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) - 1 =
      (pow2Rat (m + 2) + 3) / ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) := by grind
  rw [heq]; exact hfrac

theorem quantized_unit_norm_le_sMax1 {d m : Nat} (u uHat : Fin d → Rat)
    (hu : l2NormSq u = 1)
    (hbound : ∀ i : Fin d, ratAbs (uHat i) ≤ rneBinadeBottomRatio m * ratAbs (u i)) :
    l2NormSq uHat ≤ sMax1 m := by
  rw [sMax1_eq_ratio_sq]
  have hr_nn : (0 : Rat) ≤ rneBinadeBottomRatio m := by
    rw [rneBinadeBottomRatio_eq]
    exact Rat.le_of_lt (rat_div_pos (rat_add_pos (pow2Rat_pos (m + 1)) (by decide))
      (pow2Rat_succ_add_one_pos m))
  have hcoord : ∀ i : Fin d,
      uHat i * uHat i ≤ (rneBinadeBottomRatio m * rneBinadeBottomRatio m) * (u i * u i) := by
    intro i
    rw [← ratAbs_sq (uHat i), ← ratAbs_sq (u i)]
    have h1 := hbound i
    have hnn1 : (0 : Rat) ≤ ratAbs (uHat i) := ratAbs_nonneg (uHat i)
    have hnn2 : (0 : Rat) ≤ rneBinadeBottomRatio m * ratAbs (u i) :=
      Rat.mul_nonneg hr_nn (ratAbs_nonneg (u i))
    have hsq := Rat.le_trans (rat_mul_le_mul_of_nonneg_right h1 hnn1)
      (rat_mul_le_mul_of_nonneg_left h1 hnn2)
    have heq : (rneBinadeBottomRatio m * ratAbs (u i)) * (rneBinadeBottomRatio m * ratAbs (u i)) =
        (rneBinadeBottomRatio m * rneBinadeBottomRatio m) * (ratAbs (u i) * ratAbs (u i)) := by grind
    rw [heq] at hsq
    exact hsq
  unfold l2NormSq dotProd at hu ⊢
  have hsum := finSum_le_finSum hcoord
  rw [finSum_mul_left, hu, Rat.mul_one] at hsum
  exact hsum

/-- Headline Theorem 2 (`quantized_unit_norm_supremum_exact`). -/
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
     betaTwoUlp 3 * l2NormSq fp8WitnessVec < 2) := by
  refine ⟨rneBinadeBottomRatio_eq, sMax1_eq_ratio_sq, sMax1_decomp,
    fun m _ => one_lt_sMax1 m, fun d m u uHat hu hb => quantized_unit_norm_le_sMax1 u uHat hu hb,
    ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp only [sMax1, pow2Rat]; grind
    · simp only [sMax1, pow2Rat]; grind
    · simp only [sMax1, pow2Rat]; grind
  · have hw : l2NormSq fp8WitnessVec = 287 / 256 := by
      simp only [l2NormSq, dotProd, finSum, finSumAux, fp8WitnessVec]; grind
    have hs3 : sMax1 3 = 324 / 289 := by simp only [sMax1, pow2Rat]; grind
    have hb1 : betaOneUlp 3 * (287 / 256 : Rat) = 4305 / 2048 := by
      simp only [betaOneUlp, invPow2Rat, pow2Rat]; grind
    have hb2 : betaTwoUlp 3 * (287 / 256 : Rat) = 2009 / 1024 := by
      simp only [betaTwoUlp, invPow2Rat, pow2Rat]; grind
    refine ⟨hw, ?_, ?_, ?_, ?_⟩
    · rw [hw]
      apply rat_lt_of_mul_pos_right (c := (256 : Rat)) (rat_natCast_pos (by decide))
      have h1 : (1 : Rat) * 256 = (256 : Nat) := by grind
      have h2 : (287 / 256 : Rat) * 256 = (287 : Nat) := by grind
      rw [h1, h2]; exact rat_natCast_lt (by decide)
    · rw [hw, hs3]
      apply rat_lt_of_mul_pos_right (c := (73984 : Rat)) (rat_natCast_pos (by decide))
      have h1 : (287 / 256 : Rat) * 73984 = (82943 : Nat) := by grind
      have h2 : (324 / 289 : Rat) * 73984 = (82944 : Nat) := by grind
      rw [h1, h2]; exact rat_natCast_lt (by decide)
    · rw [hw, hb1]
      apply rat_lt_of_mul_pos_right (c := (2048 : Rat)) (rat_natCast_pos (by decide))
      have h1 : (2 : Rat) * 2048 = (4096 : Nat) := by grind
      have h2 : (4305 / 2048 : Rat) * 2048 = (4305 : Nat) := by grind
      rw [h1, h2]; exact rat_natCast_lt (by decide)
    · rw [hw, hb2]
      apply rat_lt_of_mul_pos_right (c := (1024 : Rat)) (rat_natCast_pos (by decide))
      have h1 : (2009 / 1024 : Rat) * 1024 = (2009 : Nat) := by grind
      have h2 : (2 : Rat) * 1024 = (2048 : Nat) := by grind
      rw [h1, h2]; exact rat_natCast_lt (by decide)

/-! ### Theorem 3: Universal 2-ULP Safe Ceiling Theorem -/

theorem pow2Rat_ge_four {m : Nat} (hm : 2 ≤ m) : (4 : Rat) ≤ pow2Rat m := by
  unfold pow2Rat
  have h4 : (4 : Nat) ≤ 2 ^ m := by
    have hpow : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
    exact hpow
  exact rat_natCast_le h4

theorem betaOneUlp_mul_sMax1_gt_two {m : Nat} (hm : 2 ≤ m) :
    (2 : Rat) < betaOneUlp m * sMax1 m := by
  unfold betaOneUlp invPow2Rat sMax1
  have hN_pos : (0 : Rat) < pow2Rat m := pow2Rat_pos m
  have hN_ne : pow2Rat m ≠ 0 := Rat.ne_of_gt hN_pos
  have hN_ge4 : (4 : Rat) ≤ pow2Rat m := pow2Rat_ge_four hm
  have hD_pos : (0 : Rat) < pow2Rat (m + 1) + 1 := pow2Rat_succ_add_one_pos m
  have hD_ne : pow2Rat (m + 1) + 1 ≠ 0 := Rat.ne_of_gt hD_pos
  have hQ_pos : (0 : Rat) < pow2Rat m * ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) :=
    rat_mul_pos hN_pos (rat_mul_pos hD_pos hD_pos)
  apply rat_lt_of_mul_pos_right hQ_pos
  have hLHS : ((2 - 1 / pow2Rat m) *
      (((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) *
       ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)))) *
      (pow2Rat m * ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) =
      (2 * pow2Rat m - 1) * ((pow2Rat (m + 1) + 2) * (pow2Rat (m + 1) + 2)) := by
    have hc1 : (2 - 1 / pow2Rat m) * pow2Rat m = 2 * pow2Rat m - 1 := by
      have hc := rat_div_mul_cancel (a := (1 : Rat)) hN_ne
      grind
    have hc2 : ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) * (pow2Rat (m + 1) + 1) =
        pow2Rat (m + 1) + 2 := rat_div_mul_cancel hD_ne
    have hre : ((2 - 1 / pow2Rat m) *
        (((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) *
         ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)))) *
        (pow2Rat m * ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) =
        ((2 - 1 / pow2Rat m) * pow2Rat m) *
        ((((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) * (pow2Rat (m + 1) + 1)) *
         (((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) * (pow2Rat (m + 1) + 1))) := by grind
    rw [hre, hc1, hc2]
  rw [hLHS, pow2Rat_succ m]
  apply rat_lt_of_sub_pos
  have hdiff : (2 * pow2Rat m - 1) * ((2 * pow2Rat m + 2) * (2 * pow2Rat m + 2)) -
      2 * (pow2Rat m * ((2 * pow2Rat m + 1) * (2 * pow2Rat m + 1))) =
      4 * pow2Rat m * (pow2Rat m - 1) + (2 * pow2Rat m - 4) := by grind
  rw [hdiff]
  have h1 : (0 : Rat) < pow2Rat m - 1 := rat_sub_pos (rat_lt_of_lt_of_le (by decide : (1 : Rat) < 4) hN_ge4)
  have h2 : (0 : Rat) < 4 * pow2Rat m * (pow2Rat m - 1) :=
    rat_mul_pos (rat_mul_pos (by decide) hN_pos) h1
  have h3 : (0 : Rat) ≤ 2 * pow2Rat m - 4 := by
    apply rat_sub_nonneg
    have hmul := rat_mul_le_mul_of_nonneg_left hN_ge4 (by decide : (0 : Rat) ≤ 2)
    have h48 : (4 : Rat) ≤ 2 * 4 := by
      have : (2 : Rat) * 4 = (8 : Nat) := by grind
      rw [this]; exact rat_natCast_le (by decide)
    exact Rat.le_trans h48 hmul
  exact rat_add_pos_of_pos_of_nonneg h2 h3

theorem betaTwoUlp_pos {m : Nat} (hm : 2 ≤ m) : (0 : Rat) < betaTwoUlp m := by
  unfold betaTwoUlp invPow2Rat
  have hN_pos : (0 : Rat) < pow2Rat m := pow2Rat_pos m
  have hN_ge4 : (4 : Rat) ≤ pow2Rat m := pow2Rat_ge_four hm
  apply rat_lt_of_mul_pos_right hN_pos
  rw [Rat.zero_mul]
  have hc := rat_div_mul_cancel (a := (1 : Rat)) (Rat.ne_of_gt hN_pos)
  have hre : (2 - 2 * (1 / pow2Rat m)) * pow2Rat m = 2 * pow2Rat m - 2 := by grind
  rw [hre]
  apply rat_lt_of_sub_pos
  have : (2 : Rat) * pow2Rat m - 2 - 0 = 2 * (pow2Rat m - 1) := by grind
  rw [this]
  exact rat_mul_pos (by decide)
    (rat_sub_pos (rat_lt_of_lt_of_le (by decide : (1 : Rat) < 4) hN_ge4))

theorem betaTwoUlp_mul_sMax1_lt_two {m : Nat} :
    betaTwoUlp m * sMax1 m < 2 := by
  unfold betaTwoUlp invPow2Rat sMax1
  have hN_pos : (0 : Rat) < pow2Rat m := pow2Rat_pos m
  have hN_ne : pow2Rat m ≠ 0 := Rat.ne_of_gt hN_pos
  have hD_pos : (0 : Rat) < pow2Rat (m + 1) + 1 := pow2Rat_succ_add_one_pos m
  have hD_ne : pow2Rat (m + 1) + 1 ≠ 0 := Rat.ne_of_gt hD_pos
  have hQ_pos : (0 : Rat) < pow2Rat m * ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1)) :=
    rat_mul_pos hN_pos (rat_mul_pos hD_pos hD_pos)
  apply rat_lt_of_mul_pos_right hQ_pos
  have hLHS : ((2 - 2 * (1 / pow2Rat m)) *
      (((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) *
       ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)))) *
      (pow2Rat m * ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) =
      (2 * pow2Rat m - 2) * ((pow2Rat (m + 1) + 2) * (pow2Rat (m + 1) + 2)) := by
    have hc1 : (2 - 2 * (1 / pow2Rat m)) * pow2Rat m = 2 * pow2Rat m - 2 := by
      have hc := rat_div_mul_cancel (a := (1 : Rat)) hN_ne
      grind
    have hc2 : ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) * (pow2Rat (m + 1) + 1) =
        pow2Rat (m + 1) + 2 := rat_div_mul_cancel hD_ne
    have hre : ((2 - 2 * (1 / pow2Rat m)) *
        (((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) *
         ((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)))) *
        (pow2Rat m * ((pow2Rat (m + 1) + 1) * (pow2Rat (m + 1) + 1))) =
        ((2 - 2 * (1 / pow2Rat m)) * pow2Rat m) *
        ((((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) * (pow2Rat (m + 1) + 1)) *
         (((pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)) * (pow2Rat (m + 1) + 1))) := by grind
    rw [hre, hc1, hc2]
  rw [hLHS, pow2Rat_succ m]
  apply rat_lt_of_sub_pos
  have hdiff : 2 * (pow2Rat m * ((2 * pow2Rat m + 1) * (2 * pow2Rat m + 1))) -
      (2 * pow2Rat m - 2) * ((2 * pow2Rat m + 2) * (2 * pow2Rat m + 2)) =
      10 * pow2Rat m + 8 := by grind
  rw [hdiff]
  exact rat_add_pos (rat_mul_pos (by decide) hN_pos) (by decide)

theorem betaTwoUlp_eq_sub_invPow2Pred {m : Nat} (hm : 1 ≤ m) :
    betaTwoUlp m = 2 - invPow2Rat (m - 1) := by
  unfold betaTwoUlp
  have hsucc : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  have hinv : (2 : Rat) * invPow2Rat ((m - 1) + 1) = invPow2Rat (m - 1) := invPow2Rat_succ (m - 1)
  rw [← hsucc] at hinv
  rw [hinv]

/-- Headline Theorem 3 (`universal_two_ulp_safe_ceiling_theorem`). -/
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
      (1 : Rat) < ratAbs (1 - betaOneUlp m * l2NormSq k)) := by
  refine ⟨fun m hm => betaOneUlp_mul_sMax1_gt_two hm,
    fun m hm => ⟨betaTwoUlp_pos hm, betaTwoUlp_mul_sMax1_lt_two,
      Rat.le_of_lt betaTwoUlp_mul_sMax1_lt_two⟩,
    fun m hm => betaTwoUlp_eq_sub_invPow2Pred hm,
    ⟨by simp only [betaTwoUlp, invPow2Rat, pow2Rat]; grind,
     by simp only [betaTwoUlp, invPow2Rat, pow2Rat]; grind,
     by simp only [betaTwoUlp, invPow2Rat, pow2Rat]; grind⟩,
    ?_, ?_⟩
  · intro d m k hm hk v
    have hβ_pos : (0 : Rat) < betaTwoUlp m := betaTwoUlp_pos hm
    have hlo : (0 : Rat) ≤ betaTwoUlp m * l2NormSq k :=
      Rat.mul_nonneg (Rat.le_of_lt hβ_pos) (l2NormSq_nonneg k)
    have hhi : betaTwoUlp m * l2NormSq k ≤ 2 :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_left hk (Rat.le_of_lt hβ_pos))
        (Rat.le_of_lt betaTwoUlp_mul_sMax1_lt_two)
    exact (householder_contraction_iff (betaTwoUlp m) k).mpr ⟨hlo, hhi⟩ v
  · intro m hm
    let r := rneBinadeBottomRatio m
    let k : Fin 1 → Rat := fun _ => r
    have hk_norm : l2NormSq k = sMax1 m := by
      simp only [l2NormSq, dotProd, finSum, finSumAux, k, r, Rat.zero_add, ← sMax1_eq_ratio_sq]
    have hk_pos : (0 : Rat) < l2NormSq k := by
      rw [hk_norm]
      exact rat_lt_of_lt_of_le (by decide : (0 : Rat) < 1) (Rat.le_of_lt (one_lt_sMax1 m))
    have hgt : (2 : Rat) < betaOneUlp m * l2NormSq k := by
      rw [hk_norm]
      exact betaOneUlp_mul_sMax1_gt_two hm
    have hexp := householder_strict_explosion (betaOneUlp m) k hk_pos hgt
    exact ⟨hk_norm, hexp.1, hexp.2⟩

end DeltaNetHouseholderE8
