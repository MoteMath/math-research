/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrpoK3Kl.RatOrder

/-!
# GRPO Binary-Reward Extreme-Difficulty Over-Weighting, `BF16` One-Pass Negative Variance & `FP8-E4M3` Mean Stall

Proves Headline Theorems 5 and 6 purely over `Rat` and `Nat` inside `Init` (zero Mathlib):
5. `grpo_binary_reward_extreme_overweighting_exact`
6. `grpo_bf16_onepass_negvar_and_fp8_mean_stall`
-/

namespace GrpoK3Kl

theorem rat_natCast_lt {a b : Nat} (h : a < b) : (a : Rat) < (b : Rat) := by
  have hle : a + 1 ≤ b := h
  have h1 : ((a + 1 : Nat) : Rat) ≤ (b : Rat) := rat_natCast_le hle
  have h2 : (a : Rat) < ((a + 1 : Nat) : Rat) := by
    rw [Rat.natCast_add]
    apply rat_lt_of_sub_pos
    have eq : ((a : Rat) + (1 : Nat)) - (a : Rat) = 1 := by grind
    rw [eq]; decide
  exact rat_lt_of_lt_of_le h2 h1

theorem binVar_pos {k G : Nat} (hk : 0 < k) (hkg : k < G) : (0 : Rat) < binVar k G := by
  unfold binVar
  have hk' : (0 : Rat) < (k : Rat) := rat_natCast_pos hk
  have hG' : (0 : Rat) < (G : Rat) := rat_natCast_pos (Nat.lt_trans hk hkg)
  have hGk : (0 : Rat) < (G : Rat) - (k : Rat) := rat_sub_pos (rat_natCast_lt hkg)
  exact rat_div_pos (rat_mul_pos hk' hGk) (rat_mul_pos hG' hG')

theorem binVar_eq_sum {k G : Nat} (hk : 0 < k) (hkg : k < G) :
    ((k : Rat) * (1 - binMean k G) * (1 - binMean k G) +
     ((G : Rat) - (k : Rat)) * (0 - binMean k G) * (0 - binMean k G)) / (G : Rat) =
    binVar k G := by
  unfold binMean binVar
  have hG : (G : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (Nat.lt_trans hk hkg))
  have hG2 : (G : Rat) * (G : Rat) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hG h
    | inr h => exact hG h
  have h1 : (1 : Rat) - (k : Rat) / (G : Rat) = ((G : Rat) - (k : Rat)) / (G : Rat) := by
    rw [Rat.div_def, Rat.div_def]
    have hGG : (G : Rat) * (G : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hG
    grind
  rw [h1]
  have hnum :
      (k : Rat) * (((G : Rat) - (k : Rat)) / (G : Rat)) * (((G : Rat) - (k : Rat)) / (G : Rat)) +
      ((G : Rat) - (k : Rat)) * (0 - (k : Rat) / (G : Rat)) * (0 - (k : Rat) / (G : Rat)) =
      ((k : Rat) * ((G : Rat) - (k : Rat)) * (G : Rat)) * ((G : Rat) * (G : Rat))⁻¹ := by
    rw [Rat.div_def, Rat.div_def, rat_mul_inv hG hG]
    grind
  rw [hnum, Rat.div_def, Rat.div_def]
  calc
    ((k : Rat) * ((G : Rat) - (k : Rat)) * (G : Rat)) * ((G : Rat) * (G : Rat))⁻¹ * (G : Rat)⁻¹
        = (k : Rat) * ((G : Rat) - (k : Rat)) * ((G : Rat) * (G : Rat)⁻¹) *
            ((G : Rat) * (G : Rat))⁻¹ := by grind
    _ = (k : Rat) * ((G : Rat) - (k : Rat)) * 1 * ((G : Rat) * (G : Rat))⁻¹ := by
      rw [Rat.mul_inv_cancel _ hG]
    _ = (k : Rat) * ((G : Rat) - (k : Rat)) * ((G : Rat) * (G : Rat))⁻¹ := by grind

theorem binAdvPosSq_eq {k G : Nat} (hk : 0 < k) (hkg : k < G) :
    binAdvPosSq k G = ((G : Rat) - (k : Rat)) / (k : Rat) := by
  unfold binAdvPosSq binMean binVar
  have hk_ne : (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hk)
  have hG_ne : (G : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (Nat.lt_trans hk hkg))
  have hGk_ne : (G : Rat) - (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_sub_pos (rat_natCast_lt hkg))
  have h1 : (1 : Rat) - (k : Rat) / (G : Rat) = ((G : Rat) - (k : Rat)) * (G : Rat)⁻¹ := by
    rw [Rat.div_def]
    have hGG : (G : Rat) * (G : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hG_ne
    grind
  have hkGk_ne : (k : Rat) * ((G : Rat) - (k : Rat)) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hk_ne h
    | inr h => exact hGk_ne h
  have hG2_ne : (G : Rat) * (G : Rat) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hG_ne h
    | inr h => exact hG_ne h
  have hG2_inv_ne : ((G : Rat) * (G : Rat))⁻¹ ≠ 0 := by
    intro h0
    have h1 := Rat.mul_inv_cancel ((G : Rat) * (G : Rat)) hG2_ne
    rw [h0, Rat.mul_zero] at h1
    exact absurd h1 (by decide)
  rw [h1, Rat.div_def, Rat.div_def, Rat.div_def, rat_mul_inv hkGk_ne hG2_inv_ne,
      Rat.inv_inv, rat_mul_inv hk_ne hGk_ne]
  calc
    (((G : Rat) - (k : Rat)) * (G : Rat)⁻¹) * (((G : Rat) - (k : Rat)) * (G : Rat)⁻¹) *
      (((G : Rat) * (G : Rat)) * (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹))
        = ((G : Rat) - (k : Rat)) * (((G : Rat) - (k : Rat)) * ((G : Rat) - (k : Rat))⁻¹) *
          ((G : Rat) * (G : Rat)⁻¹) * ((G : Rat) * (G : Rat)⁻¹) * (k : Rat)⁻¹ := by grind
    _ = ((G : Rat) - (k : Rat)) * 1 * 1 * 1 * (k : Rat)⁻¹ := by
      rw [Rat.mul_inv_cancel _ hGk_ne, Rat.mul_inv_cancel _ hG_ne]
    _ = ((G : Rat) - (k : Rat)) * (k : Rat)⁻¹ := by grind

theorem binAdvNegSq_eq {k G : Nat} (hk : 0 < k) (hkg : k < G) :
    binAdvNegSq k G = (k : Rat) / ((G : Rat) - (k : Rat)) := by
  unfold binAdvNegSq binMean binVar
  have hk_ne : (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hk)
  have hG_ne : (G : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (Nat.lt_trans hk hkg))
  have hGk_ne : (G : Rat) - (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_sub_pos (rat_natCast_lt hkg))
  have hkGk_ne : (k : Rat) * ((G : Rat) - (k : Rat)) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hk_ne h
    | inr h => exact hGk_ne h
  have hG2_ne : (G : Rat) * (G : Rat) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hG_ne h
    | inr h => exact hG_ne h
  have hG2_inv_ne : ((G : Rat) * (G : Rat))⁻¹ ≠ 0 := by
    intro h0
    have h1 := Rat.mul_inv_cancel ((G : Rat) * (G : Rat)) hG2_ne
    rw [h0, Rat.mul_zero] at h1
    exact absurd h1 (by decide)
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, rat_mul_inv hkGk_ne hG2_inv_ne,
      Rat.inv_inv, rat_mul_inv hk_ne hGk_ne]
  calc
    ((k : Rat) * (G : Rat)⁻¹ * ((k : Rat) * (G : Rat)⁻¹)) *
      (((G : Rat) * (G : Rat)) * (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹))
        = (k : Rat) * ((k : Rat) * (k : Rat)⁻¹) *
          ((G : Rat) * (G : Rat)⁻¹) * ((G : Rat) * (G : Rat)⁻¹) * ((G : Rat) - (k : Rat))⁻¹ := by
      grind
    _ = (k : Rat) * 1 * 1 * 1 * ((G : Rat) - (k : Rat))⁻¹ := by
      rw [Rat.mul_inv_cancel _ hk_ne, Rat.mul_inv_cancel _ hG_ne]
    _ = (k : Rat) * ((G : Rat) - (k : Rat))⁻¹ := by grind

theorem binL1SumSq_eq {k G : Nat} (hk : 0 < k) (hkg : k < G) :
    binL1SumSq k G = ((G : Rat) * (G : Rat)) / ((k : Rat) * ((G : Rat) - (k : Rat))) := by
  unfold binL1SumSq
  rw [binAdvPosSq_eq hk hkg, binAdvNegSq_eq hk hkg]
  have hk_ne : (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hk)
  have hGk_ne : (G : Rat) - (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_sub_pos (rat_natCast_lt hkg))
  rw [Rat.div_def, Rat.div_def, Rat.div_def, rat_mul_inv hk_ne hGk_ne]
  have hkk : (k : Rat) * (k : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hk_ne
  have hGG : ((G : Rat) - (k : Rat)) * ((G : Rat) - (k : Rat))⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hGk_ne
  have h1 : ((G : Rat) - (k : Rat)) * (k : Rat)⁻¹ =
      (((G : Rat) - (k : Rat)) * ((G : Rat) - (k : Rat))) *
        (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹) := by
    calc
      ((G : Rat) - (k : Rat)) * (k : Rat)⁻¹
          = ((G : Rat) - (k : Rat)) * 1 * (k : Rat)⁻¹ := by grind
      _ = ((G : Rat) - (k : Rat)) * (((G : Rat) - (k : Rat)) * ((G : Rat) - (k : Rat))⁻¹) *
            (k : Rat)⁻¹ := by rw [hGG]
      _ = (((G : Rat) - (k : Rat)) * ((G : Rat) - (k : Rat))) *
            (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹) := by grind
  have h2 : (k : Rat) * ((G : Rat) - (k : Rat))⁻¹ =
      ((k : Rat) * (k : Rat)) * (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹) := by
    calc
      (k : Rat) * ((G : Rat) - (k : Rat))⁻¹
          = (k : Rat) * 1 * ((G : Rat) - (k : Rat))⁻¹ := by grind
      _ = (k : Rat) * ((k : Rat) * (k : Rat)⁻¹) * ((G : Rat) - (k : Rat))⁻¹ := by rw [hkk]
      _ = ((k : Rat) * (k : Rat)) * (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹) := by grind
  have h3 : (2 : Rat) =
      (2 * (k : Rat) * ((G : Rat) - (k : Rat))) * (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹) := by
    calc
      (2 : Rat) = 2 * 1 * 1 := by grind
      _ = 2 * ((k : Rat) * (k : Rat)⁻¹) * (((G : Rat) - (k : Rat)) * ((G : Rat) - (k : Rat))⁻¹) := by
        rw [hkk, hGG]
      _ = (2 * (k : Rat) * ((G : Rat) - (k : Rat))) *
            (((G : Rat) - (k : Rat))⁻¹ * (k : Rat)⁻¹) := by grind
  rw [h1, h2, h3]
  grind

theorem binMean_bounds {k G : Nat} (hkG : k ≤ G) (hG : 0 < G) :
    (0 : Rat) ≤ binMean k G ∧ binMean k G ≤ 1 := by
  unfold binMean
  have hGpos : (0 : Rat) < (G : Rat) := rat_natCast_pos hG
  constructor
  · exact rat_div_nonneg (rat_natCast_nonneg k) hGpos
  · have hle : (k : Rat) ≤ (G : Rat) := rat_natCast_le hkG
    have hdiv := rat_div_le_div_of_pos hle hGpos
    have hGG : (G : Rat) / (G : Rat) = 1 := by
      rw [Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt hGpos)]
    rw [hGG] at hdiv
    exact hdiv

/-- Headline Theorem 5 (`grpo_binary_reward_extreme_overweighting_exact`). -/
theorem grpo_binary_reward_extreme_overweighting_exact :
    (∀ (k G : Nat), 0 < k → k < G →
      ((k : Rat) * (1 - binMean k G) * (1 - binMean k G) +
       ((G : Rat) - (k : Rat)) * (0 - binMean k G) * (0 - binMean k G)) / (G : Rat) = binVar k G ∧
      (0 : Rat) < binVar k G ∧
      binAdvPosSq k G = ((G : Rat) - (k : Rat)) / (k : Rat) ∧
      binAdvNegSq k G = (k : Rat) / ((G : Rat) - (k : Rat)) ∧
      binAdvPosSq k G * binAdvNegSq k G = 1 ∧
      binL1SumSq k G = ((G : Rat) * (G : Rat)) / ((k : Rat) * ((G : Rat) - (k : Rat)))) ∧
    (∀ h : Nat, 2 ≤ h →
      let G := 2 * h
      binAdvPosSq h G = 1 ∧
      binAdvNegSq h G = 1 ∧
      binL1SumSq h G = 4 ∧
      binAdvPosSq 1 G = (G : Rat) - 1 ∧
      binAdvPosSq 1 G / binAdvPosSq h G = (G : Rat) - 1 ∧
      binL1SumSq 1 G / binL1SumSq h G = ((G : Rat) * (G : Rat)) / (4 * ((G : Rat) - 1))) ∧
    (binL1SumSq 1 4 / binL1SumSq 2 4 = 4 / 3 ∧
     binL1SumSq 1 8 / binL1SumSq 4 8 = 16 / 7 ∧
     binL1SumSq 1 16 / binL1SumSq 8 16 = 64 / 15 ∧
     binL1SumSq 1 64 / binL1SumSq 32 64 = 1024 / 63 ∧
     (16 : Rat) < binL1SumSq 1 64 / binL1SumSq 32 64) ∧
    (∀ (k G : Nat) (r : Rat), k ≤ G → 0 < G → (r = 0 ∨ r = 1) →
      ratAbs (drGrpoAdv r (binMean k G)) ≤ 1) ∧
    (∀ (k G : Nat), k ≤ G → 0 < G →
      ratAbs (drGrpoAdv 1 (binMean k G)) + ratAbs (drGrpoAdv 0 (binMean k G)) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k G hk hkg
    refine ⟨binVar_eq_sum hk hkg, binVar_pos hk hkg,
            binAdvPosSq_eq hk hkg, binAdvNegSq_eq hk hkg, ?_, binL1SumSq_eq hk hkg⟩
    rw [binAdvPosSq_eq hk hkg, binAdvNegSq_eq hk hkg]
    have hk_ne : (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hk)
    have hGk_ne : (G : Rat) - (k : Rat) ≠ 0 := Rat.ne_of_gt (rat_sub_pos (rat_natCast_lt hkg))
    rw [Rat.div_def, Rat.div_def]
    calc
      ((G : Rat) - (k : Rat)) * (k : Rat)⁻¹ * ((k : Rat) * ((G : Rat) - (k : Rat))⁻¹)
          = (((G : Rat) - (k : Rat)) * ((G : Rat) - (k : Rat))⁻¹) * ((k : Rat) * (k : Rat)⁻¹) := by
        grind
      _ = 1 * 1 := by rw [Rat.mul_inv_cancel _ hGk_ne, Rat.mul_inv_cancel _ hk_ne]
      _ = 1 := by grind
  · intro h hh
    have hh0 : 0 < h := by omega
    have hlt : h < 2 * h := by omega
    have h1lt : 1 < 2 * h := by omega
    have hh_ne : (h : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hh0)
    have h2h : ((2 * h : Nat) : Rat) = 2 * (h : Rat) := by
      rw [Rat.natCast_mul]; rfl
    have hPos_bal : binAdvPosSq h (2 * h) = 1 := by
      rw [binAdvPosSq_eq hh0 hlt, h2h]
      have eq : 2 * (h : Rat) - (h : Rat) = (h : Rat) := by grind
      rw [eq, Rat.div_def, Rat.mul_inv_cancel _ hh_ne]
    have hNeg_bal : binAdvNegSq h (2 * h) = 1 := by
      rw [binAdvNegSq_eq hh0 hlt, h2h]
      have eq : 2 * (h : Rat) - (h : Rat) = (h : Rat) := by grind
      rw [eq, Rat.div_def, Rat.mul_inv_cancel _ hh_ne]
    have hL1_bal : binL1SumSq h (2 * h) = 4 := by
      unfold binL1SumSq
      rw [hPos_bal, hNeg_bal]; grind
    have hPos_ext : binAdvPosSq 1 (2 * h) = ((2 * h : Nat) : Rat) - 1 := by
      rw [binAdvPosSq_eq (by decide) h1lt]
      have h1 : ((1 : Nat) : Rat) = 1 := rfl
      rw [h1, Rat.div_def]
      grind
    have hL1_ext : binL1SumSq 1 (2 * h) =
        (((2 * h : Nat) : Rat) * ((2 * h : Nat) : Rat)) / (((2 * h : Nat) : Rat) - 1) := by
      rw [binL1SumSq_eq (by decide) h1lt]
      have h1 : ((1 : Nat) : Rat) = 1 := rfl
      rw [h1, Rat.one_mul]
    refine ⟨hPos_bal, hNeg_bal, hL1_bal, hPos_ext, ?_, ?_⟩
    · rw [hPos_ext, hPos_bal, Rat.div_def]
      grind
    · have hG1_ne : ((2 * h : Nat) : Rat) - 1 ≠ 0 :=
        Rat.ne_of_gt (rat_sub_pos (rat_natCast_lt h1lt))
      have h4_ne : (4 : Rat) ≠ 0 := by decide
      rw [hL1_ext, hL1_bal, Rat.div_def, Rat.div_def, Rat.div_def, rat_mul_inv h4_ne hG1_ne]
      grind
  · unfold binL1SumSq binAdvPosSq binAdvNegSq binMean binVar
    grind
  · intro k G r hkG hG hr
    have ⟨h0, h1⟩ := binMean_bounds hkG hG
    unfold drGrpoAdv
    cases hr with
    | inl hr0 =>
      rw [hr0]
      have hneg : 0 - binMean k G ≤ 0 := by
        apply rat_le_of_sub_nonneg
        have eq : (0 : Rat) - (0 - binMean k G) = binMean k G := by grind
        rw [eq]; exact h0
      rw [ratAbs_of_nonpos hneg]
      have eq : -(0 - binMean k G) = binMean k G := by grind
      rw [eq]; exact h1
    | inr hr1 =>
      rw [hr1]
      have hnn : (0 : Rat) ≤ 1 - binMean k G := rat_sub_nonneg h1
      rw [ratAbs_of_nonneg hnn]
      apply rat_le_of_sub_nonneg
      have eq : 1 - (1 - binMean k G) = binMean k G := by grind
      rw [eq]; exact h0
  · intro k G hkG hG
    have ⟨h0, h1⟩ := binMean_bounds hkG hG
    unfold drGrpoAdv
    have hnn : (0 : Rat) ≤ 1 - binMean k G := rat_sub_nonneg h1
    have hnp : 0 - binMean k G ≤ 0 := by
      apply rat_le_of_sub_nonneg
      have eq : (0 : Rat) - (0 - binMean k G) = binMean k G := by grind
      rw [eq]; exact h0
    rw [ratAbs_of_nonneg hnn, ratAbs_of_nonpos hnp]
    grind

/-! ## Theorem 6: `BF16` One-Pass Negative Variance & `FP8-E4M3` Mean-Saturation Stall -/

theorem fp8E4M3SeqSumFour_le_16 :
    ∀ n : Nat, n ≤ 16 → fp8E4M3SeqSumFour n = ((4 * n : Nat) : Rat) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro hle
    have hk : k ≤ 16 := Nat.le_of_succ_le hle
    have hk16 : 4 * k < 64 := by omega
    have hstep : fp8E4M3SeqSumFour (k + 1) = fp8E4M3AddFour (fp8E4M3SeqSumFour k) := rfl
    rw [hstep, ih hk]
    unfold fp8E4M3AddFour
    have hlt : ((4 * k : Nat) : Rat) < (64 : Rat) := rat_natCast_lt hk16
    simp only [hlt, ↓reduceIte]
    have hnat : 4 * (k + 1) = 4 * k + 4 := by omega
    rw [hnat, Rat.natCast_add]
    rfl

theorem fp8E4M3SeqSumFour_eq_64_of_ge_16 :
    ∀ n : Nat, 16 ≤ n → fp8E4M3SeqSumFour n = 64 := by
  intro n hn
  have h16 : fp8E4M3SeqSumFour 16 = 64 := by
    rw [fp8E4M3SeqSumFour_le_16 16 (Nat.le_refl 16)]
    rfl
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => exact h16
  | succ k ih =>
    have hstep : fp8E4M3SeqSumFour (16 + (k + 1)) =
        fp8E4M3AddFour (fp8E4M3SeqSumFour (16 + k)) := rfl
    rw [hstep, ih (Nat.le_add_right 16 k)]
    unfold fp8E4M3AddFour
    simp only [show ¬ ((64 : Rat) < 64) by grind, ↓reduceIte]

theorem bf16_0x4081_val : bf16DecodePosNormal 0x4081 = 129 / 32 := by
  unfold bf16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x4081 / 128) % 256 = 129 by decide, show 0x4081 % 128 = 1 by decide,
             show (129 < 134) = true by decide, ↓reduceIte,
             show 134 - 129 = 5 by decide, show 128 + 1 = 129 by decide,
             show 2 ^ 5 = 32 by decide]
  grind

theorem bf16_0x4082_val : bf16DecodePosNormal 0x4082 = 65 / 16 := by
  unfold bf16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x4082 / 128) % 256 = 129 by decide, show 0x4082 % 128 = 2 by decide,
             show (129 < 134) = true by decide, ↓reduceIte,
             show 134 - 129 = 5 by decide, show 128 + 2 = 130 by decide,
             show 2 ^ 5 = 32 by decide]
  grind

theorem bf16_0x4083_val : bf16DecodePosNormal 0x4083 = 131 / 32 := by
  unfold bf16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x4083 / 128) % 256 = 129 by decide, show 0x4083 % 128 = 3 by decide,
             show (129 < 134) = true by decide, ↓reduceIte,
             show 134 - 129 = 5 by decide, show 128 + 3 = 131 by decide,
             show 2 ^ 5 = 32 by decide]
  grind

theorem bf16_0x4183_val : bf16DecodePosNormal 0x4183 = 131 / 8 := by
  unfold bf16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x4183 / 128) % 256 = 131 by decide, show 0x4183 % 128 = 3 by decide,
             show (131 < 134) = true by decide, ↓reduceIte,
             show 134 - 131 = 3 by decide, show 128 + 3 = 131 by decide,
             show 2 ^ 3 = 8 by decide]
  grind

theorem bf16_0x4184_val : bf16DecodePosNormal 0x4184 = 33 / 2 := by
  unfold bf16DecodePosNormal invPow2Rat pow2Rat
  simp only [show (0x4184 / 128) % 256 = 131 by decide, show 0x4184 % 128 = 4 by decide,
             show (131 < 134) = true by decide, ↓reduceIte,
             show 134 - 131 = 3 by decide, show 128 + 4 = 132 by decide,
             show 2 ^ 3 = 8 by decide]
  grind

/-- Headline Theorem 6 (`grpo_bf16_onepass_negvar_and_fp8_mean_stall`). -/
theorem grpo_bf16_onepass_negvar_and_fp8_mean_stall :
    (let r0 := bf16DecodePosNormal 0x4081
     let r3 := bf16DecodePosNormal 0x4083
     let μTrue := (3 * r0 + r3) / 4
     let μHat := bf16DecodePosNormal 0x4082
     let meanSqTrue := (3 * (r0 * r0) + r3 * r3) / 4
     let flMeanSq := bf16DecodePosNormal 0x4183
     let flMuSq := bf16DecodePosNormal 0x4184
     r0 = 129 / 32 ∧ r3 = 131 / 32 ∧ μHat = 65 / 16 ∧
     flMeanSq = 131 / 8 ∧ flMuSq = 33 / 2 ∧
     meanSqTrue - μTrue * μTrue = 3 / 4096 ∧
     (0 : Rat) < meanSqTrue - μTrue * μTrue ∧
     rneRoundsToUpperEven r0 (binadeUlp 2 7) μTrue ∧
     r0 + binadeUlp 2 7 = μHat ∧
     rneRoundsStrictlyLower flMuSq (binadeUlp 4 7) (μHat * μHat) ∧
     rneRoundsStrictlyLower flMeanSq (binadeUlp 4 7) meanSqTrue ∧
     flMeanSq - flMuSq = -(1 / 8 : Rat) ∧
     flMeanSq - flMuSq < 0) ∧
    (binadeUlp 6 3 = 8 ∧
     rneRoundsToLowerEven 64 (binadeUlp 6 3) (64 + 4) ∧
     (∀ n : Nat, 16 ≤ n → fp8E4M3SeqSumFour n = 64) ∧
     fp8E4M3SeqSumFour 64 = 64 ∧
     fp8E4M3SeqSumFour 64 / 64 = 1 ∧
     (4 : Rat) - fp8E4M3SeqSumFour 64 / 64 = 3 ∧
     (0 : Rat) < (4 : Rat) - fp8E4M3SeqSumFour 64 / 64) := by
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [bf16_0x4081_val, bf16_0x4082_val, bf16_0x4083_val, bf16_0x4183_val, bf16_0x4184_val]
    unfold rneRoundsToUpperEven rneRoundsStrictlyLower binadeUlp invPow2Rat pow2Rat
    simp only [show 2 ^ 2 = 4 by decide, show 2 ^ 4 = 16 by decide, show 2 ^ 7 = 128 by decide]
    grind
  · have h64 : fp8E4M3SeqSumFour 64 = 64 := fp8E4M3SeqSumFour_eq_64_of_ge_16 64 (by decide)
    have hulp : binadeUlp 6 3 = 8 := by
      unfold binadeUlp invPow2Rat pow2Rat
      simp only [show 2 ^ 6 = 64 by decide, show 2 ^ 3 = 8 by decide]
      grind
    refine ⟨hulp, ?_, fp8E4M3SeqSumFour_eq_64_of_ge_16, h64, ?_, ?_, ?_⟩
    · unfold rneRoundsToLowerEven; rw [hulp]; grind
    · rw [h64]; grind
    · rw [h64]; grind
    · rw [h64]; grind

end GrpoK3Kl
