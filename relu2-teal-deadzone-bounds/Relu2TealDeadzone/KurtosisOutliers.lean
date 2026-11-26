/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relu2TealDeadzone.RatOrder

/-!
# Theorem 1: Exact `ReLU^2` Kurtosis (`70/3`) and Outlier Amplification (`p * c^8`)

Proves that for any symmetric finite rational distribution `(w, x)` with `x i ≥ 0`:
1. Half-rectification halves every even positive moment of `ReLU` and `ReLU^2`:
   - `E[ReLU(X)^2] = m2 / 2`, `E[ReLU(X)^4] = m4 / 2`,
   - `E[ReLU^2(X)^2] = m4 / 2`, `E[ReLU^2(X)^4] = m8 / 2`.
2. Consequently, for any standard-normal-moment-matching distribution (`m2 = 1, m4 = 3, m8 = 105`):
   - `Linear` kurtosis = `3`,
   - `ReLU` kurtosis = `6`,
   - `ReLU^2` kurtosis = `70 / 3` (`2 * 105 / 3^2 = 70 / 3`).
3. For any `(1 - p)` bulk + `p` `c`-scaled outlier mixture (`c ≥ 0`):
   - `ReLU` 4th-moment outlier weight scales as `p * c^4`,
   - `ReLU^2` 4th-moment (8th raw moment) outlier weight scales as `p * c^8`,
   - For `0 < p` and `1 < c`, `p * c^8 > p * c^4` (exact ratio `c^4`),
   - Concrete 1% `4×` OutlierMix (`p = 1/100, c = 4`) on Gaussian moments certifies
     `ReLU` kurtosis `= 8520 / 529` (`< 17`) vs `ReLU^2` kurtosis `= 18377800 / 15123` (`> 1215`,
     a `> 75×` kurtosis explosion over `ReLU`).
-/

namespace Relu2TealDeadzone

theorem relu_of_nonneg {t : Rat} (ht : (0 : Rat) ≤ t) : relu t = t := by
  unfold relu
  simp [ht]

theorem relu_neg_of_nonneg {t : Rat} (ht : (0 : Rat) ≤ t) : relu (-t) = 0 := by
  unfold relu
  by_cases h0 : t = 0
  · subst h0; decide
  · have hpos : (0 : Rat) < t := Rat.lt_of_le_of_ne ht (Ne.symm h0)
    have hneg : ¬ (0 : Rat) ≤ -t := by
      intro h
      have hle : t ≤ 0 := by
        have := (Rat.add_le_add_right (c := t)).mpr h
        grind
      exact Rat.not_le.mpr hpos hle
    simp [hneg]

theorem symExpect_even_sq {n : Nat} (w x : Fin n → Rat) :
    symExpect w x sq = 2 * finSum (fun i => w i * sq (x i)) := by
  unfold symExpect
  rw [← finSum_mul_left]
  apply finSum_congr
  intro i
  unfold sq
  grind

theorem symExpect_even_pow4 {n : Nat} (w x : Fin n → Rat) :
    symExpect w x pow4 = 2 * finSum (fun i => w i * pow4 (x i)) := by
  unfold symExpect
  rw [← finSum_mul_left]
  apply finSum_congr
  intro i
  unfold pow4 sq
  grind

theorem symExpect_even_pow8 {n : Nat} (w x : Fin n → Rat) :
    symExpect w x pow8 = 2 * finSum (fun i => w i * pow8 (x i)) := by
  unfold symExpect
  rw [← finSum_mul_left]
  apply finSum_congr
  intro i
  unfold pow8 pow4 sq
  grind

theorem symExpect_relu_sq {n : Nat} (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    symExpect w x (fun t => sq (relu t)) = symExpect w x sq / 2 := by
  rw [symExpect_even_sq]
  have h1 : symExpect w x (fun t => sq (relu t)) = finSum (fun i => w i * sq (x i)) := by
    unfold symExpect
    apply finSum_congr
    intro i
    dsimp only
    rw [relu_of_nonneg (hx i), relu_neg_of_nonneg (hx i)]
    unfold sq
    grind
  rw [h1]
  have h2 : (2 : Rat) ≠ 0 := by decide
  symm
  rw [rat_div_eq_iff h2]
  grind

theorem symExpect_relu_pow4 {n : Nat} (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    symExpect w x (fun t => pow4 (relu t)) = symExpect w x pow4 / 2 := by
  rw [symExpect_even_pow4]
  have h1 : symExpect w x (fun t => pow4 (relu t)) = finSum (fun i => w i * pow4 (x i)) := by
    unfold symExpect
    apply finSum_congr
    intro i
    dsimp only
    rw [relu_of_nonneg (hx i), relu_neg_of_nonneg (hx i)]
    unfold pow4 sq
    grind
  rw [h1]
  have h2 : (2 : Rat) ≠ 0 := by decide
  symm
  rw [rat_div_eq_iff h2]
  grind

theorem symExpect_relu2_sq {n : Nat} (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    symExpect w x (fun t => sq (relu2 t)) = symExpect w x pow4 / 2 := by
  have h : symExpect w x (fun t => sq (relu2 t)) = symExpect w x (fun t => pow4 (relu t)) := by
    unfold symExpect relu2 pow4
    rfl
  rw [h]
  exact symExpect_relu_pow4 w x hx

theorem symExpect_relu2_pow4 {n : Nat} (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    symExpect w x (fun t => pow4 (relu2 t)) = symExpect w x pow8 / 2 := by
  rw [symExpect_even_pow8]
  have h1 : symExpect w x (fun t => pow4 (relu2 t)) = finSum (fun i => w i * pow8 (x i)) := by
    unfold symExpect relu2
    apply finSum_congr
    intro i
    dsimp only
    rw [relu_of_nonneg (hx i), relu_neg_of_nonneg (hx i)]
    unfold pow8 pow4 sq
    grind
  rw [h1]
  have h2 : (2 : Rat) ≠ 0 := by decide
  symm
  rw [rat_div_eq_iff h2]
  grind

theorem symExpect_scale_sq {n : Nat} (c : Rat) (w x : Fin n → Rat) :
    symExpect w (fun i => c * x i) sq = sq c * symExpect w x sq := by
  unfold symExpect
  rw [← finSum_mul_left]
  apply finSum_congr
  intro i
  unfold sq
  grind

theorem symExpect_scale_pow4 {n : Nat} (c : Rat) (w x : Fin n → Rat) :
    symExpect w (fun i => c * x i) pow4 = pow4 c * symExpect w x pow4 := by
  unfold symExpect
  rw [← finSum_mul_left]
  apply finSum_congr
  intro i
  unfold pow4 sq
  grind

theorem symExpect_scale_pow8 {n : Nat} (c : Rat) (w x : Fin n → Rat) :
    symExpect w (fun i => c * x i) pow8 = pow8 c * symExpect w x pow8 := by
  unfold symExpect
  rw [← finSum_mul_left]
  apply finSum_congr
  intro i
  unfold pow8 pow4 sq
  grind

theorem mixSymExpect_relu_sq {n : Nat} (p c : Rat) (hc : (0 : Rat) ≤ c)
    (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    mixSymExpect p c w x (fun t => sq (relu t)) =
      ((1 - p) + p * sq c) * (symExpect w x sq / 2) := by
  unfold mixSymExpect
  have hcx : ∀ i, (0 : Rat) ≤ c * x i := fun i => Rat.mul_nonneg hc (hx i)
  rw [symExpect_relu_sq w x hx, symExpect_relu_sq w (fun i => c * x i) hcx,
      symExpect_scale_sq c w x]
  have h2 : (2 : Rat) ≠ 0 := by decide
  have eq1 : sq c * symExpect w x sq / 2 = sq c * (symExpect w x sq / 2) := by
    rw [rat_div_eq_iff h2]
    have := rat_div_mul_cancel (a := symExpect w x sq) h2
    grind
  rw [eq1]
  grind

theorem mixSymExpect_relu_pow4 {n : Nat} (p c : Rat) (hc : (0 : Rat) ≤ c)
    (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    mixSymExpect p c w x (fun t => pow4 (relu t)) =
      ((1 - p) + p * pow4 c) * (symExpect w x pow4 / 2) := by
  unfold mixSymExpect
  have hcx : ∀ i, (0 : Rat) ≤ c * x i := fun i => Rat.mul_nonneg hc (hx i)
  rw [symExpect_relu_pow4 w x hx, symExpect_relu_pow4 w (fun i => c * x i) hcx,
      symExpect_scale_pow4 c w x]
  have h2 : (2 : Rat) ≠ 0 := by decide
  have eq1 : pow4 c * symExpect w x pow4 / 2 = pow4 c * (symExpect w x pow4 / 2) := by
    rw [rat_div_eq_iff h2]
    have := rat_div_mul_cancel (a := symExpect w x pow4) h2
    grind
  rw [eq1]
  grind

theorem mixSymExpect_relu2_sq {n : Nat} (p c : Rat) (hc : (0 : Rat) ≤ c)
    (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    mixSymExpect p c w x (fun t => sq (relu2 t)) =
      ((1 - p) + p * pow4 c) * (symExpect w x pow4 / 2) := by
  have h : mixSymExpect p c w x (fun t => sq (relu2 t)) =
           mixSymExpect p c w x (fun t => pow4 (relu t)) := by
    unfold mixSymExpect symExpect relu2 pow4
    rfl
  rw [h]
  exact mixSymExpect_relu_pow4 p c hc w x hx

theorem mixSymExpect_relu2_pow4 {n : Nat} (p c : Rat) (hc : (0 : Rat) ≤ c)
    (w x : Fin n → Rat) (hx : ∀ i, (0 : Rat) ≤ x i) :
    mixSymExpect p c w x (fun t => pow4 (relu2 t)) =
      ((1 - p) + p * pow8 c) * (symExpect w x pow8 / 2) := by
  unfold mixSymExpect
  have hcx : ∀ i, (0 : Rat) ≤ c * x i := fun i => Rat.mul_nonneg hc (hx i)
  rw [symExpect_relu2_pow4 w x hx, symExpect_relu2_pow4 w (fun i => c * x i) hcx,
      symExpect_scale_pow8 c w x]
  have h2 : (2 : Rat) ≠ 0 := by decide
  have eq1 : pow8 c * symExpect w x pow8 / 2 = pow8 c * (symExpect w x pow8 / 2) := by
    rw [rat_div_eq_iff h2]
    have := rat_div_mul_cancel (a := symExpect w x pow8) h2
    grind
  rw [eq1]
  grind

theorem relu2_exact_kurtosis_seventy_thirds_and_outlier_amplification :
    (∀ (n : Nat) (w x : Fin n → Rat),
      (∀ i, (0 : Rat) ≤ x i) →
      symExpect w x sq = 1 →
      symExpect w x pow4 = 3 →
      symExpect w x pow8 = 105 →
      kurtosis (symExpect w x sq) (symExpect w x pow4) = 3 ∧
      kurtosis (symExpect w x (fun t => sq (relu t)))
               (symExpect w x (fun t => pow4 (relu t))) = 6 ∧
      kurtosis (symExpect w x (fun t => sq (relu2 t)))
               (symExpect w x (fun t => pow4 (relu2 t))) = 70 / 3) ∧
    (∀ (n : Nat) (p c : Rat) (w x : Fin n → Rat),
      (0 : Rat) ≤ c →
      (∀ i, (0 : Rat) ≤ x i) →
      mixSymExpect p c w x (fun t => sq (relu t)) =
        ((1 - p) + p * sq c) * (symExpect w x sq / 2) ∧
      mixSymExpect p c w x (fun t => pow4 (relu t)) =
        ((1 - p) + p * pow4 c) * (symExpect w x pow4 / 2) ∧
      mixSymExpect p c w x (fun t => sq (relu2 t)) =
        ((1 - p) + p * pow4 c) * (symExpect w x pow4 / 2) ∧
      mixSymExpect p c w x (fun t => pow4 (relu2 t)) =
        ((1 - p) + p * pow8 c) * (symExpect w x pow8 / 2)) ∧
    (∀ (p c : Rat), (0 : Rat) < p → (1 : Rat) < c →
      p * pow4 c < p * pow8 c ∧
      (p * pow8 c) / (p * pow4 c) = pow4 c) ∧
    (kurtosis (((1 - 1 / 100 : Rat) + (1 / 100) * sq 4) * (1 / 2))
              (((1 - 1 / 100 : Rat) + (1 / 100) * pow4 4) * (3 / 2)) = 8520 / 529 ∧
     kurtosis (((1 - 1 / 100 : Rat) + (1 / 100) * pow4 4) * (3 / 2))
              (((1 - 1 / 100 : Rat) + (1 / 100) * pow8 4) * (105 / 2)) = 18377800 / 15123 ∧
     (1215 : Rat) < 18377800 / 15123 ∧
     (75 : Rat) * (8520 / 529) < 18377800 / 15123) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n w x hx hm2 hm4 hm8
    rw [symExpect_relu_sq w x hx, symExpect_relu_pow4 w x hx,
        symExpect_relu2_sq w x hx, symExpect_relu2_pow4 w x hx,
        hm2, hm4, hm8]
    unfold kurtosis sq
    refine ⟨by grind, by grind, by grind⟩
  · intro n p c w x hc hx
    exact ⟨mixSymExpect_relu_sq p c hc w x hx,
           mixSymExpect_relu_pow4 p c hc w x hx,
           mixSymExpect_relu2_sq p c hc w x hx,
           mixSymExpect_relu2_pow4 p c hc w x hx⟩
  · intro p c hp hc
    have hc_pos : (0 : Rat) < c := rat_lt_trans (by decide) hc
    have hc2_gt : (1 : Rat) < sq c := by
      have h1 : (1 : Rat) * 1 < c * c := by
        have := rat_sq_lt_sq_of_nonneg (by decide : (0 : Rat) ≤ 1) hc
        simpa [sq] using this
      simpa [sq] using h1
    have hc4_gt : (1 : Rat) < pow4 c := by
      have := rat_sq_lt_sq_of_nonneg (by decide : (0 : Rat) ≤ 1) hc2_gt
      have h1 : sq (1 : Rat) = 1 := by unfold sq; grind
      rw [h1] at this
      exact this
    have hc4_pos : (0 : Rat) < pow4 c := rat_lt_trans (by decide) hc4_gt
    have hpc4_pos : (0 : Rat) < p * pow4 c := rat_mul_pos hp hc4_pos
    have hpow8_eq : pow8 c = pow4 c * pow4 c := rfl
    constructor
    · have hlt : (p * pow4 c) * 1 < (p * pow4 c) * pow4 c :=
        rat_mul_lt_mul_of_pos_left hc4_gt hpc4_pos
      have eqL : (p * pow4 c) * 1 = p * pow4 c := by grind
      have eqR : (p * pow4 c) * pow4 c = p * pow8 c := by rw [hpow8_eq]; grind
      rw [eqL, eqR] at hlt
      exact hlt
    · rw [rat_div_eq_iff (Rat.ne_of_gt hpc4_pos), hpow8_eq]
      grind
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold kurtosis pow4 sq; grind
    · unfold kurtosis pow8 pow4 sq; grind
    · apply rat_lt_div_of_mul_lt (by decide : (0 : Rat) < 15123)
      have eq : (1215 : Rat) * 15123 = 18374445 := by grind
      rw [eq]; decide
    · have eqL : (75 : Rat) * (8520 / 529) = 639000 / 529 := by grind
      rw [eqL]
      apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 529) (by decide : (0 : Rat) < 15123)
      have h1 : (639000 : Rat) * 15123 = 9663597000 := by grind
      have h2 : (18377800 : Rat) * 529 = 9721856200 := by grind
      rw [h1, h2]; decide

end Relu2TealDeadzone
