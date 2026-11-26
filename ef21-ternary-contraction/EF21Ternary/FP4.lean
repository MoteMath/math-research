/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EF21Ternary.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact Universal EF21 Contraction Laws for MXFP4 and NVFP4

Proves `mxfp4_nvfp4_ef21_contraction_universal` for ALL block sizes `B ≥ 1`:
- **MXFP4** (`|y_i| ≤ 6`, `∃ i_0, 3 < |y_{i_0}|`):
  exact 3-phase law `α_MXFP4(B) = min(384/(B+399), 192/(B+195), 144/(B+143))`,
  with tight extremal configurations `(5, 1/4)` for `1 ≤ B ≤ 8`, `(7/2, 1/4)` for `9 ≤ B ≤ 12`,
  and `(3+, 1/4)` for `B ≥ 13` (matching `48/53` at `B = 16` and `144/175` at `B = 32`).
- **NVFP4** (`|y_i| ≤ 6`, `∃ i_0, |y_{i_0}| = 6`):
  exact 2-phase law `α_NVFP4(B) = min((24B+12)/(25B+11), 576/(B+575))`,
  with exact attainment at `(6, 5)` for `1 ≤ B ≤ 23` and `(6, 1/4)` for `B ≥ 24`
  (matching `132/137` at `B = 16` and `576/607` at `B = 32`).
-/

namespace EF21Ternary

open scoped BigOperators

private lemma e2m1QuantNonneg_zero : e2m1QuantNonneg 0 = 0 := by
  unfold e2m1QuantNonneg
  norm_num

private lemma e2m1Quant_neg (y : ℝ) : e2m1Quant (-y) = -e2m1Quant y := by
  unfold e2m1Quant
  by_cases hy : 0 ≤ y
  · by_cases hy0 : y = 0
    · subst hy0; simp [e2m1QuantNonneg_zero]
    · have hlt : ¬ (0 ≤ -y) := by linarith [lt_of_le_of_ne hy (Ne.symm hy0)]
      simp [hy, hlt]
  · have hpos : 0 ≤ -y := by linarith
    simp [hy, hpos]

private lemma e2m1_err_sq_abs (y : ℝ) :
    (y - e2m1Quant y) ^ 2 = (|y| - e2m1QuantNonneg |y|) ^ 2 := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    simp [e2m1Quant, hy]
  · rw [abs_of_neg (lt_of_not_ge hy)]
    simp [e2m1Quant, hy]
    ring

/-- Convexity of `(y - q)^2 - c * y^2` on `[a, b]` whenever `c ≤ 1`:
bounded above by the endpoint values at `a` and `b`. -/
private lemma quad_le_of_endpoints {a b q c M y : ℝ} (hc : c ≤ 1) (ha : a ≤ y) (hb : y ≤ b)
    (hfa : (a - q) ^ 2 - c * a ^ 2 ≤ M) (hfb : (b - q) ^ 2 - c * b ^ 2 ≤ M) :
    (y - q) ^ 2 - c * y ^ 2 ≤ M := by
  by_cases hab : a = b
  · have hya : y = a := le_antisymm (hab ▸ hb) ha
    simpa [hya] using hfa
  · have hlt : a < b := lt_of_le_of_ne (ha.trans hb) hab
    have hdiff : 0 ≤ (b - a) * (1 - c) * (y - a) * (b - y) := by
      have h1 : 0 ≤ b - a := by linarith
      have h2 : 0 ≤ 1 - c := by linarith
      have h3 : 0 ≤ y - a := by linarith
      have h4 : 0 ≤ b - y := by linarith
      positivity
    have hcomb : (b - y) * ((a - q) ^ 2 - c * a ^ 2) + (y - a) * ((b - q) ^ 2 - c * b ^ 2) ≤
        (b - a) * M := by
      nlinarith
    have hident : (b - a) * ((y - q) ^ 2 - c * y ^ 2) =
        (b - y) * ((a - q) ^ 2 - c * a ^ 2) + (y - a) * ((b - q) ^ 2 - c * b ^ 2) -
          (b - a) * (1 - c) * (y - a) * (b - y) := by
      ring
    nlinarith

/-- Uniform 1D upper bound on `(y - e2m1QuantNonneg y)^2 - c * y^2` for `y ∈ [0, 6]`. -/
private lemma e2m1_1d_bound_all {c M y : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hy0 : 0 ≤ y) (hy6 : y ≤ 6)
    (h0 : 0 ≤ M)
    (h14 : (1 - c) / 16 ≤ M)
    (h5 : 1 - 25 * c ≤ M) :
    (y - e2m1QuantNonneg y) ^ 2 - c * y ^ 2 ≤ M := by
  have h52 : (1 : ℝ) / 4 - 25 / 4 * c ≤ M := by linarith
  have h72 : (1 : ℝ) / 4 - 49 / 4 * c ≤ M := by linarith
  unfold e2m1QuantNonneg
  split_ifs with h1 h2 h3 h4 h5' h6 h7
  · exact quad_le_of_endpoints hc1 hy0 h1.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h1) h2.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h2) h3.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h3) h4.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h4) h5'.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h5') h6.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h6) h7.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h7) hy6 (by linarith) (by linarith)

/-- Anchor 1D upper bound on `(y - e2m1QuantNonneg y)^2 - c * y^2` for `y ∈ [3, 6]`. -/
private lemma e2m1_1d_bound_anchor {c A y : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hy3 : 3 ≤ y) (hy6 : y ≤ 6)
    (h3 : -9 * c ≤ A)
    (h72 : (1 : ℝ) / 4 - 49 / 4 * c ≤ A)
    (h5 : 1 - 25 * c ≤ A) :
    (y - e2m1QuantNonneg y) ^ 2 - c * y ^ 2 ≤ A := by
  unfold e2m1QuantNonneg
  have hn1 : ¬ (y < 1 / 4) := by linarith
  have hn2 : ¬ (y < 3 / 4) := by linarith
  have hn3 : ¬ (y < 5 / 4) := by linarith
  have hn4 : ¬ (y < 7 / 4) := by linarith
  have hn5 : ¬ (y < 5 / 2) := by linarith
  simp only [hn1, hn2, hn3, hn4, hn5, ↓reduceIte]
  split_ifs with h6 h7
  · exact quad_le_of_endpoints hc1 hy3 h6.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h6) h7.le (by linarith) (by linarith)
  · exact quad_le_of_endpoints hc1 (not_lt.mp h7) hy6 (by linarith) (by linarith)

private lemma e2m1Quant_eval_quarter : e2m1Quant (1 / 4) = 1 / 2 := by
  unfold e2m1Quant e2m1QuantNonneg; norm_num

private lemma e2m1Quant_eval_seven_halves : e2m1Quant (7 / 2) = 4 := by
  unfold e2m1Quant e2m1QuantNonneg; norm_num

private lemma e2m1Quant_eval_five : e2m1Quant 5 = 6 := by
  unfold e2m1Quant e2m1QuantNonneg; norm_num

private lemma e2m1Quant_eval_six : e2m1Quant 6 = 6 := by
  unfold e2m1Quant e2m1QuantNonneg; norm_num

private lemma e2m1Quant_eval_three_plus {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    e2m1Quant (3 + δ) = 3 := by
  unfold e2m1Quant e2m1QuantNonneg
  have h0 : 0 ≤ 3 + δ := by linarith
  have hn1 : ¬ (3 + δ < 1 / 4) := by linarith
  have hn2 : ¬ (3 + δ < 3 / 4) := by linarith
  have hn3 : ¬ (3 + δ < 5 / 4) := by linarith
  have hn4 : ¬ (3 + δ < 7 / 4) := by linarith
  have hn5 : ¬ (3 + δ < 5 / 2) := by linarith
  have h6 : 3 + δ < 7 / 2 := by linarith
  simp only [h0, hn1, hn2, hn3, hn4, hn5, h6, ↓reduceIte]

/-- Universal MXFP4 upper bound for all `B ≥ 1`. -/
lemma mxfp4_upper_bound (B : ℕ) (hB : 0 < B) (y : Fin B → ℝ)
    (hmax : ∀ i, |y i| ≤ 6) (hanchor : ∃ i0, 3 < |y i0|) :
    ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2 ≤
      (1 - alphaMXFP4 B) * ∑ i : Fin B, (y i) ^ 2 := by
  rcases hanchor with ⟨i0, hi0⟩
  set c : ℝ := 1 - alphaMXFP4 B with hc_def
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hα_le1 : alphaMXFP4 B ≤ 384 / ((B : ℝ) + 399) := min_le_left _ _
  have hα_le2 : alphaMXFP4 B ≤ 192 / ((B : ℝ) + 195) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hα_le3 : alphaMXFP4 B ≤ 144 / ((B : ℝ) + 143) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hα_pos : 0 < alphaMXFP4 B := by
    unfold alphaMXFP4
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hc1 : c ≤ 1 := by linarith
  have hc_ge1 : ((B : ℝ) + 15) / ((B : ℝ) + 399) ≤ c := by
    have hd : (0 : ℝ) < (B : ℝ) + 399 := by positivity
    have : 1 - 384 / ((B : ℝ) + 399) = ((B : ℝ) + 15) / ((B : ℝ) + 399) := by
      field_simp; ring
    linarith
  have hc_ge2 : ((B : ℝ) + 3) / ((B : ℝ) + 195) ≤ c := by
    have hd : (0 : ℝ) < (B : ℝ) + 195 := by positivity
    have : 1 - 192 / ((B : ℝ) + 195) = ((B : ℝ) + 3) / ((B : ℝ) + 195) := by
      field_simp; ring
    linarith
  have hc_ge3 : ((B : ℝ) - 1) / ((B : ℝ) + 143) ≤ c := by
    have hd : (0 : ℝ) < (B : ℝ) + 143 := by positivity
    have : 1 - 144 / ((B : ℝ) + 143) = ((B : ℝ) - 1) / ((B : ℝ) + 143) := by
      field_simp; ring
    linarith
  have hc_ge_1_25 : (1 : ℝ) / 25 ≤ c := by
    have hd : (0 : ℝ) < (B : ℝ) + 399 := by positivity
    have h1 : (1 : ℝ) / 25 ≤ ((B : ℝ) + 15) / ((B : ℝ) + 399) := by
      rw [div_le_div_iff₀ (by norm_num) hd]
      linarith
    linarith
  have hc0 : 0 ≤ c := by linarith
  have hprod1 : (B : ℝ) + 15 ≤ c * ((B : ℝ) + 399) := by
    rwa [div_le_iff₀ (by positivity)] at hc_ge1
  have hprod2 : (B : ℝ) + 3 ≤ c * ((B : ℝ) + 195) := by
    rwa [div_le_iff₀ (by positivity)] at hc_ge2
  have hprod3 : (B : ℝ) - 1 ≤ c * ((B : ℝ) + 143) := by
    rwa [div_le_iff₀ (by positivity)] at hc_ge3
  -- Reduce to summing `e(y_i)^2 - c * y_i^2 ≤ 0`
  suffices hsum : ∑ i : Fin B, ((y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2) ≤ 0 by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    linarith
  rw [(Finset.add_sum_erase Finset.univ
    (fun i : Fin B => (y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2)
    (Finset.mem_univ i0)).symm]
  have hanchor_le : (y i0 - e2m1Quant (y i0)) ^ 2 - c * (y i0) ^ 2 ≤
      -((B : ℝ) - 1) * ((1 - c) / 16) := by
    rw [e2m1_err_sq_abs, ← sq_abs (y i0)]
    exact e2m1_1d_bound_anchor hc0 hc1 hi0.le (hmax i0)
      (by linarith) (by linarith) (by linarith)
  have hother_le : ∀ i ∈ Finset.univ.erase i0,
      (y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2 ≤ (1 - c) / 16 := by
    intro i _
    rw [e2m1_err_sq_abs, ← sq_abs (y i)]
    exact e2m1_1d_bound_all hc0 hc1 (abs_nonneg (y i)) (hmax i)
      (by linarith) le_rfl (by linarith)
  have hsum_other : ∑ i ∈ Finset.univ.erase i0,
      ((y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2) ≤ ((B : ℝ) - 1) * ((1 - c) / 16) := by
    calc ∑ i ∈ Finset.univ.erase i0, ((y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2)
        ≤ ∑ _i ∈ Finset.univ.erase i0, ((1 - c) / 16) := Finset.sum_le_sum hother_le
      _ = ((B - 1 : ℕ) : ℝ) * ((1 - c) / 16) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i0),
            Finset.card_fin, nsmul_eq_mul]
      _ = ((B : ℝ) - 1) * ((1 - c) / 16) := by
          rw [Nat.cast_sub hB, Nat.cast_one]
  linarith

/-- Universal NVFP4 upper bound for all `B ≥ 1`. -/
lemma nvfp4_upper_bound (B : ℕ) (hB : 0 < B) (y : Fin B → ℝ)
    (hmax : ∀ i, |y i| ≤ 6) (hanchor : ∃ i0, |y i0| = 6) :
    ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2 ≤
      (1 - alphaNVFP4 B) * ∑ i : Fin B, (y i) ^ 2 := by
  rcases hanchor with ⟨i0, hi0⟩
  by_cases hB1 : B = 1
  · subst hB1
    have hα : alphaNVFP4 1 = 1 := by
      unfold alphaNVFP4; norm_num
    rw [hα, sub_self, zero_mul]
    have hsum0 : ∑ i : Fin 1, (y i - e2m1Quant (y i)) ^ 2 = 0 := by
      rw [Finset.sum_eq_single i0]
      · rw [e2m1_err_sq_abs, hi0]
        unfold e2m1QuantNonneg; norm_num
      · intro i _ hi
        exact absurd (Subsingleton.elim i i0) hi
      · intro h
        exact absurd (Finset.mem_univ i0) h
    rw [hsum0]
  · have hB2 : 2 ≤ B := by omega
    have hBm1_pos : (0 : ℝ) < (B : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
      linarith
    set c : ℝ := 1 - alphaNVFP4 B with hc_def
    have hα_le1 : alphaNVFP4 B ≤ (24 * (B : ℝ) + 12) / (25 * (B : ℝ) + 11) := min_le_left _ _
    have hα_le2 : alphaNVFP4 B ≤ 576 / ((B : ℝ) + 575) := min_le_right _ _
    have hα_pos : 0 < alphaNVFP4 B := by
      unfold alphaNVFP4
      exact lt_min (by positivity) (by positivity)
    have hc1 : c ≤ 1 := by linarith
    have hc_ge1 : ((B : ℝ) - 1) / (25 * (B : ℝ) + 11) ≤ c := by
      have hd : (0 : ℝ) < 25 * (B : ℝ) + 11 := by positivity
      have : 1 - (24 * (B : ℝ) + 12) / (25 * (B : ℝ) + 11) =
          ((B : ℝ) - 1) / (25 * (B : ℝ) + 11) := by field_simp; ring
      linarith
    have hc_ge2 : ((B : ℝ) - 1) / ((B : ℝ) + 575) ≤ c := by
      have hd : (0 : ℝ) < (B : ℝ) + 575 := by positivity
      have : 1 - 576 / ((B : ℝ) + 575) = ((B : ℝ) - 1) / ((B : ℝ) + 575) := by field_simp; ring
      linarith
    have hc0 : 0 ≤ c := le_trans (by positivity) hc_ge2
    have hprod1 : (B : ℝ) - 1 ≤ c * (25 * (B : ℝ) + 11) := by
      rwa [div_le_iff₀ (by positivity)] at hc_ge1
    have hprod2 : (B : ℝ) - 1 ≤ c * ((B : ℝ) + 575) := by
      rwa [div_le_iff₀ (by positivity)] at hc_ge2
    set M : ℝ := 36 * c / ((B : ℝ) - 1)
    have hM0 : 0 ≤ M := by positivity
    have hM14 : (1 - c) / 16 ≤ M := by
      rw [div_le_div_iff₀ (by norm_num) hBm1_pos]
      linarith
    have hM5 : 1 - 25 * c ≤ M := by
      rw [le_div_iff₀ hBm1_pos]
      linarith
    suffices hsum : ∑ i : Fin B, ((y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2) ≤ 0 by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
      linarith
    rw [(Finset.add_sum_erase Finset.univ
      (fun i : Fin B => (y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2)
      (Finset.mem_univ i0)).symm]
    have hanchor_eq : (y i0 - e2m1Quant (y i0)) ^ 2 - c * (y i0) ^ 2 = -36 * c := by
      rw [e2m1_err_sq_abs, ← sq_abs (y i0), hi0]
      unfold e2m1QuantNonneg; norm_num; ring
    have hother_le : ∀ i ∈ Finset.univ.erase i0,
        (y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2 ≤ M := by
      intro i _
      rw [e2m1_err_sq_abs, ← sq_abs (y i)]
      exact e2m1_1d_bound_all hc0 hc1 (abs_nonneg (y i)) (hmax i) hM0 hM14 hM5
    have hsum_other : ∑ i ∈ Finset.univ.erase i0,
        ((y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2) ≤ 36 * c := by
      calc ∑ i ∈ Finset.univ.erase i0, ((y i - e2m1Quant (y i)) ^ 2 - c * (y i) ^ 2)
          ≤ ∑ _i ∈ Finset.univ.erase i0, M := Finset.sum_le_sum hother_le
        _ = ((B - 1 : ℕ) : ℝ) * M := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i0),
              Finset.card_fin, nsmul_eq_mul]
        _ = ((B : ℝ) - 1) * (36 * c / ((B : ℝ) - 1)) := by
            rw [Nat.cast_sub hB, Nat.cast_one]
        _ = 36 * c := mul_div_cancel₀ _ hBm1_pos.ne'
    linarith

/-- Helper to evaluate sums on 2-valued vectors `i = 0 ↦ a`, `i ≠ 0 ↦ b`. -/
private lemma sum_two_val {B : ℕ} (hB : 0 < B) (f : ℝ → ℝ) (a b : ℝ) :
    ∑ i : Fin B, f (if i.1 = 0 then a else b) = f a + ((B : ℝ) - 1) * f b := by
  let i0 : Fin B := ⟨0, hB⟩
  rw [(Finset.add_sum_erase Finset.univ (fun i : Fin B => f (if i.1 = 0 then a else b))
    (Finset.mem_univ i0)).symm]
  have h0 : f (if i0.1 = 0 then a else b) = f a := by simp [i0]
  have hrest : ∑ i ∈ Finset.univ.erase i0, f (if i.1 = 0 then a else b) =
      ((B : ℝ) - 1) * f b := by
    have hcongr : ∀ i ∈ Finset.univ.erase i0, f (if i.1 = 0 then a else b) = f b := by
      intro i hi
      have hne : i.1 ≠ 0 := fun h0 => (Finset.mem_erase.mp hi).1 (Fin.ext h0)
      simp [hne]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_fin, nsmul_eq_mul,
      Nat.cast_sub hB, Nat.cast_one]
  rw [h0, hrest]

/-- Tightness of `alphaMXFP4 B` for all `B ≥ 1`: for every `ε > 0`, there exists a valid
MXFP4 block vector whose relative quantization error exceeds `1 - alphaMXFP4 B - ε`. -/
lemma mxfp4_tightness (B : ℕ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Fin B → ℝ, (∀ i, |y i| ≤ 6) ∧ (∃ i0, 3 < |y i0|) ∧
      (1 - alphaMXFP4 B - ε) * (∑ i : Fin B, (y i) ^ 2) <
        ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2 := by
  let i0 : Fin B := ⟨0, hB⟩
  by_cases hB8 : B ≤ 8
  · -- Regime 1 (`1 ≤ B ≤ 8`): exact attainment at `(5, 1/4)`
    have hB_le : (B : ℝ) ≤ 8 := by exact_mod_cast hB8
    have hα : alphaMXFP4 B = 384 / ((B : ℝ) + 399) := by
      unfold alphaMXFP4
      have h1 : 384 / ((B : ℝ) + 399) ≤ 192 / ((B : ℝ) + 195) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have h2 : 192 / ((B : ℝ) + 195) ≤ 144 / ((B : ℝ) + 143) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      rw [min_eq_left h2, min_eq_left h1]
    refine ⟨fun i => if i.1 = 0 then 5 else 1 / 4, ?_, ⟨i0, by simp [i0]; norm_num⟩, ?_⟩
    · intro i; dsimp only; split_ifs <;> norm_num
    · have hnum : ∑ i : Fin B, ((if i.1 = 0 then (5 : ℝ) else 1 / 4) -
          e2m1Quant (if i.1 = 0 then (5 : ℝ) else 1 / 4)) ^ 2 =
          1 + ((B : ℝ) - 1) / 16 := by
        simpa [e2m1Quant_eval_five, e2m1Quant_eval_quarter, div_eq_mul_inv] using
          (by
            have := sum_two_val hB (fun z => (z - e2m1Quant z) ^ 2) 5 (1 / 4)
            rw [e2m1Quant_eval_five, e2m1Quant_eval_quarter] at this
            linarith)
      have hden : ∑ i : Fin B, (if i.1 = 0 then (5 : ℝ) else 1 / 4) ^ 2 =
          25 + ((B : ℝ) - 1) / 16 := by
        have := sum_two_val hB (fun z => z ^ 2) 5 (1 / 4)
        linarith
      have hden_pos : 0 < 25 + ((B : ℝ) - 1) / 16 := by
        have : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
        linarith
      rw [hnum, hden, hα]
      have heq : (1 - 384 / ((B : ℝ) + 399)) * (25 + ((B : ℝ) - 1) / 16) =
          1 + ((B : ℝ) - 1) / 16 := by
        field_simp; ring
      nlinarith
  · by_cases hB12 : B ≤ 12
    · -- Regime 2 (`9 ≤ B ≤ 12`): exact attainment at `(7/2, 1/4)`
      have hB_ge : (9 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show 9 ≤ B by omega)
      have hB_le : (B : ℝ) ≤ 12 := by exact_mod_cast hB12
      have hα : alphaMXFP4 B = 192 / ((B : ℝ) + 195) := by
        unfold alphaMXFP4
        have h1 : 192 / ((B : ℝ) + 195) ≤ 384 / ((B : ℝ) + 399) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        have h2 : 192 / ((B : ℝ) + 195) ≤ 144 / ((B : ℝ) + 143) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        rw [min_eq_left h2, min_eq_right h1]
      refine ⟨fun i => if i.1 = 0 then 7 / 2 else 1 / 4, ?_, ⟨i0, by simp [i0]; norm_num⟩, ?_⟩
      · intro i; dsimp only; split_ifs <;> norm_num
      · have hnum : ∑ i : Fin B, ((if i.1 = 0 then (7 / 2 : ℝ) else 1 / 4) -
            e2m1Quant (if i.1 = 0 then (7 / 2 : ℝ) else 1 / 4)) ^ 2 =
            1 / 4 + ((B : ℝ) - 1) / 16 := by
          have := sum_two_val hB (fun z => (z - e2m1Quant z) ^ 2) (7 / 2) (1 / 4)
          rw [e2m1Quant_eval_seven_halves, e2m1Quant_eval_quarter] at this
          linarith
        have hden : ∑ i : Fin B, (if i.1 = 0 then (7 / 2 : ℝ) else 1 / 4) ^ 2 =
            49 / 4 + ((B : ℝ) - 1) / 16 := by
          have := sum_two_val hB (fun z => z ^ 2) (7 / 2) (1 / 4)
          linarith
        have hden_pos : 0 < 49 / 4 + ((B : ℝ) - 1) / 16 := by linarith
        rw [hnum, hden, hα]
        have heq : (1 - 192 / ((B : ℝ) + 195)) * (49 / 4 + ((B : ℝ) - 1) / 16) =
            1 / 4 + ((B : ℝ) - 1) / 16 := by
          field_simp; ring
        nlinarith
    · -- Regime 3 (`B ≥ 13`): supremum at `(3 + δ, 1/4)` as `δ → 0⁺`
      have hB_ge : (13 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show 13 ≤ B by omega)
      have hα : alphaMXFP4 B = 144 / ((B : ℝ) + 143) := by
        unfold alphaMXFP4
        have h1 : 144 / ((B : ℝ) + 143) ≤ 192 / ((B : ℝ) + 195) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        have h2 : 144 / ((B : ℝ) + 143) ≤ 384 / ((B : ℝ) + 399) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        rw [min_eq_right h1, min_eq_right h2]
      -- Choose `δ > 0` small enough that `(6 δ + δ^2) < ε * 9`
      set δ : ℝ := min (1 / 4) (ε / 2) with hδ_def
      have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
      have hδ_le1 : δ ≤ 1 / 4 := min_le_left _ _
      have hδ_le2 : δ ≤ ε / 2 := min_le_right _ _
      have hδ_lt : δ < 1 / 2 := by linarith
      refine ⟨fun i => if i.1 = 0 then 3 + δ else 1 / 4, ?_, ?_, ?_⟩
      · intro i
        dsimp only
        split_ifs
        · rw [abs_of_nonneg (by linarith)]; linarith
        · norm_num
      · refine ⟨i0, ?_⟩
        simp only [i0, ↓reduceIte]
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have hnum : ∑ i : Fin B, ((if i.1 = 0 then (3 + δ : ℝ) else 1 / 4) -
            e2m1Quant (if i.1 = 0 then (3 + δ : ℝ) else 1 / 4)) ^ 2 =
            δ ^ 2 + ((B : ℝ) - 1) / 16 := by
          have := sum_two_val hB (fun z => (z - e2m1Quant z) ^ 2) (3 + δ) (1 / 4)
          rw [e2m1Quant_eval_three_plus hδ0 hδ_lt, e2m1Quant_eval_quarter] at this
          linarith
        have hden : ∑ i : Fin B, (if i.1 = 0 then (3 + δ : ℝ) else 1 / 4) ^ 2 =
            (3 + δ) ^ 2 + ((B : ℝ) - 1) / 16 := by
          have := sum_two_val hB (fun z => z ^ 2) (3 + δ) (1 / 4)
          linarith
        rw [hnum, hden, hα]
        set c : ℝ := 1 - 144 / ((B : ℝ) + 143)
        have hc_eq : c = ((B : ℝ) - 1) / ((B : ℝ) + 143) := by
          dsimp [c]; field_simp; ring
        have hc_lt1 : c < 1 := by
          rw [hc_eq, div_lt_one (by positivity)]; linarith
        have hc_base : c * (9 + ((B : ℝ) - 1) / 16) = ((B : ℝ) - 1) / 16 := by
          rw [hc_eq]; field_simp; ring
        have hden_gt : 9 < (3 + δ) ^ 2 + ((B : ℝ) - 1) / 16 := by nlinarith
        have hstep : c * (6 * δ + δ ^ 2) < 9 * ε := by
          have h6 : 6 * δ + δ ^ 2 ≤ 7 * δ := by nlinarith
          have h7 : 7 * δ < 9 * ε := by linarith
          have hpos : 0 < 6 * δ + δ ^ 2 := by positivity
          nlinarith
        nlinarith

/-- Exact attainment of `alphaNVFP4 B` for all `B ≥ 1`. -/
lemma nvfp4_attainment (B : ℕ) (hB : 0 < B) :
    ∃ y : Fin B → ℝ, (∀ i, |y i| ≤ 6) ∧ (∃ i0, |y i0| = 6) ∧
      ∑ i : Fin B, (y i - e2m1Quant (y i)) ^ 2 =
        (1 - alphaNVFP4 B) * ∑ i : Fin B, (y i) ^ 2 := by
  let i0 : Fin B := ⟨0, hB⟩
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  by_cases hB23 : B ≤ 23
  · -- Regime 1 (`1 ≤ B ≤ 23`): exact attainment at `(6, 5)`
    have hB_le : (B : ℝ) ≤ 23 := by exact_mod_cast hB23
    have hα : alphaNVFP4 B = (24 * (B : ℝ) + 12) / (25 * (B : ℝ) + 11) := by
      unfold alphaNVFP4
      apply min_eq_left
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine ⟨fun i => if i.1 = 0 then 6 else 5, ?_, ⟨i0, by simp [i0]⟩, ?_⟩
    · intro i; dsimp only; split_ifs <;> norm_num
    · have hnum : ∑ i : Fin B, ((if i.1 = 0 then (6 : ℝ) else 5) -
          e2m1Quant (if i.1 = 0 then (6 : ℝ) else 5)) ^ 2 = (B : ℝ) - 1 := by
        have := sum_two_val hB (fun z => (z - e2m1Quant z) ^ 2) 6 5
        rw [e2m1Quant_eval_six, e2m1Quant_eval_five] at this
        linarith
      have hden : ∑ i : Fin B, (if i.1 = 0 then (6 : ℝ) else 5) ^ 2 =
          36 + 25 * ((B : ℝ) - 1) := by
        have := sum_two_val hB (fun z => z ^ 2) 6 5
        linarith
      rw [hnum, hden, hα]
      field_simp; ring
  · -- Regime 2 (`B ≥ 24`): exact attainment at `(6, 1/4)`
    have hB_ge : (24 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show 24 ≤ B by omega)
    have hα : alphaNVFP4 B = 576 / ((B : ℝ) + 575) := by
      unfold alphaNVFP4
      apply min_eq_right
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine ⟨fun i => if i.1 = 0 then 6 else 1 / 4, ?_, ⟨i0, by simp [i0]⟩, ?_⟩
    · intro i; dsimp only; split_ifs <;> norm_num
    · have hnum : ∑ i : Fin B, ((if i.1 = 0 then (6 : ℝ) else 1 / 4) -
          e2m1Quant (if i.1 = 0 then (6 : ℝ) else 1 / 4)) ^ 2 = ((B : ℝ) - 1) / 16 := by
        have := sum_two_val hB (fun z => (z - e2m1Quant z) ^ 2) 6 (1 / 4)
        rw [e2m1Quant_eval_six, e2m1Quant_eval_quarter] at this
        linarith
      have hden : ∑ i : Fin B, (if i.1 = 0 then (6 : ℝ) else 1 / 4) ^ 2 =
          36 + ((B : ℝ) - 1) / 16 := by
        have := sum_two_val hB (fun z => z ^ 2) 6 (1 / 4)
        linarith
      rw [hnum, hden, hα]
      field_simp; ring

/-- Theorem 3 (`I082`): Exact universal EF21 contraction law for both MXFP4 and NVFP4
across ALL block sizes `B ≥ 1`, with exact tightness/attainment in every phase regime. -/
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
  ⟨⟨mxfp4_upper_bound B hB, mxfp4_tightness B hB⟩,
   ⟨nvfp4_upper_bound B hB, nvfp4_attainment B hB⟩⟩

end EF21Ternary
