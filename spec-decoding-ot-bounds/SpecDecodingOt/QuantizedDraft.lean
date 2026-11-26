/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecodingOt.RatHelpers

/-!
# Theorems 3 & 4: Exact Quantized-Draft Speculative Decoding Acceptance Loss Laws

Pure-`Init` Lean 4 proofs over `Rat` (zero Mathlib):
1. `quantized_draft_loss_k1_exact`:
   For all `V ≥ 2`, `R ≥ 1`, probability distribution `p`, and positive draft weights `w, w'`
   satisfying `w i ≤ R * w' i` and `w' i ≤ R * w i`:
   `|alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w')| ≤ (R - 1) / (R + 1)` (= `tanh(ε / 2)`),
   attained with exact equality for every `V ≥ 2`.
2. `quantized_draft_loss_multidraft_exact`:
   For all `K ≥ 2`, `V ≥ 2`, `R ≥ 1`, probability distribution `p`, and positive `w, w'` with
   `R`-bounded weight ratios:
   `alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') ≤ (K - 1) * (R^2 - 1) / (1 + (K - 1) * R^2)`,
   attained with exact equality for every `K ≥ 2`, `V ≥ 2`, `R ≥ 1`.
-/

namespace SpecDecodingOt

/-! ## Shared Ratio-Partition Lemma for Softmax Subsets -/

private theorem softmax_subset_ratio_bound {V : Nat} (hV : 0 < V) {R : Rat} (hR : 1 ≤ R)
    (w w' : Fin V → Rat) (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    (hbound : ∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i)
    (P : Fin V → Prop) [DecidablePred P] :
    let A := sumRat (fun i => if P i then softmaxRat w i else 0)
    let A' := sumRat (fun i => if P i then softmaxRat w' i else 0)
    0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ A' ∧ A' ≤ 1 ∧
    A * (1 - A') ≤ (R * R) * A' * (1 - A) := by
  have hWpos : 0 < sumRat w := sumRat_pos hV w hw
  have hW'pos : 0 < sumRat w' := sumRat_pos hV w' hw'
  have hR0 : 0 ≤ R := Rat.le_trans (by decide) hR
  let Wp := sumRat (fun i => if P i then w i else 0)
  let Wq := sumRat (fun i => if P i then 0 else w i)
  let W'p := sumRat (fun i => if P i then w' i else 0)
  let W'q := sumRat (fun i => if P i then 0 else w' i)
  have hWp0 : 0 ≤ Wp := sumRat_nonneg _ (fun i => by by_cases hp : P i <;> simp [hp]; exact Rat.le_of_lt (hw i))
  have hWq0 : 0 ≤ Wq := sumRat_nonneg _ (fun i => by by_cases hp : P i <;> simp [hp]; exact Rat.le_of_lt (hw i))
  have hW'p0 : 0 ≤ W'p := sumRat_nonneg _ (fun i => by by_cases hp : P i <;> simp [hp]; exact Rat.le_of_lt (hw' i))
  have hW'q0 : 0 ≤ W'q := sumRat_nonneg _ (fun i => by by_cases hp : P i <;> simp [hp]; exact Rat.le_of_lt (hw' i))
  have hWsplit : Wp + Wq = sumRat w := sumRat_split_prop w P
  have hW'split : W'p + W'q = sumRat w' := sumRat_split_prop w' P
  have hA_eq : sumRat (fun i => if P i then softmaxRat w i else 0) = Wp / sumRat w := by
    rw [← sumRat_div_right]
    apply sumRat_congr
    intro i
    by_cases hp : P i
    · simp [hp, softmaxRat]
    · simp [hp, Rat.div_def]
  have hA'_eq : sumRat (fun i => if P i then softmaxRat w' i else 0) = W'p / sumRat w' := by
    rw [← sumRat_div_right]
    apply sumRat_congr
    intro i
    by_cases hp : P i
    · simp [hp, softmaxRat]
    · simp [hp, Rat.div_def]
  have h1A_eq : 1 - Wp / sumRat w = Wq / sumRat w := by
    have hself := rat_div_self (rat_ne_zero_of_pos hWpos)
    rw [← hWsplit] at hself
    rw [Rat.div_def] at hself ⊢
    grind
  have h1A'_eq : 1 - W'p / sumRat w' = W'q / sumRat w' := by
    have hself := rat_div_self (rat_ne_zero_of_pos hW'pos)
    rw [← hW'split] at hself
    rw [Rat.div_def] at hself ⊢
    grind
  have hA0 : 0 ≤ Wp / sumRat w := rat_div_nonneg hWp0 hWpos
  have hA1 : Wp / sumRat w ≤ 1 := by
    apply rat_le_of_sub_nonneg
    rw [h1A_eq]
    exact rat_div_nonneg hWq0 hWpos
  have hA'0 : 0 ≤ W'p / sumRat w' := rat_div_nonneg hW'p0 hW'pos
  have hA'1 : W'p / sumRat w' ≤ 1 := by
    apply rat_le_of_sub_nonneg
    rw [h1A'_eq]
    exact rat_div_nonneg hW'q0 hW'pos
  have hWp_le : Wp ≤ R * W'p := by
    change sumRat (fun i => if P i then w i else 0) ≤ R * sumRat (fun i => if P i then w' i else 0)
    rw [← sumRat_mul_left]
    apply sumRat_le_sumRat
    intro i
    by_cases hp : P i
    · simp [hp]; exact (hbound i).1
    · simp [hp]
  have hW'q_le : W'q ≤ R * Wq := by
    change sumRat (fun i => if P i then 0 else w' i) ≤ R * sumRat (fun i => if P i then 0 else w i)
    rw [← sumRat_mul_left]
    apply sumRat_le_sumRat
    intro i
    by_cases hp : P i
    · simp [hp]
    · simp [hp]; exact (hbound i).2
  have hprod : Wp * W'q ≤ (R * R) * W'p * Wq := by
    have h1 : Wp * W'q ≤ (R * W'p) * W'q := Rat.mul_le_mul_of_nonneg_right hWp_le hW'q0
    have h2 : (R * W'p) * W'q ≤ (R * W'p) * (R * Wq) :=
      Rat.mul_le_mul_of_nonneg_left hW'q_le (rat_mul_nonneg hR0 hW'p0)
    have h3 : (R * W'p) * (R * Wq) = (R * R) * W'p * Wq := by grind
    rw [h3] at h2
    exact Rat.le_trans h1 h2
  have hmain : (Wp / sumRat w) * (1 - W'p / sumRat w') ≤
      (R * R) * (W'p / sumRat w') * (1 - Wp / sumRat w) := by
    rw [h1A'_eq, h1A_eq]
    have hWW'pos : 0 < sumRat w * sumRat w' := rat_mul_pos hWpos hW'pos
    have hinv_nonneg : 0 ≤ (sumRat w)⁻¹ * (sumRat w')⁻¹ :=
      rat_mul_nonneg (Rat.le_of_lt (rat_inv_pos hWpos)) (Rat.le_of_lt (rat_inv_pos hW'pos))
    have hmul := Rat.mul_le_mul_of_nonneg_right hprod hinv_nonneg
    have hL : Wp * W'q * ((sumRat w)⁻¹ * (sumRat w')⁻¹) = (Wp / sumRat w) * (W'q / sumRat w') := by
      simp only [Rat.div_def]; grind
    have hR' : (R * R) * W'p * Wq * ((sumRat w)⁻¹ * (sumRat w')⁻¹) =
        (R * R) * (W'p / sumRat w') * (Wq / sumRat w) := by
      simp only [Rat.div_def]; grind
    rw [hL, hR'] at hmul
    exact hmul
  rw [hA_eq, hA'_eq]
  exact ⟨hA0, hA1, hA'0, hA'1, hmain⟩

private theorem denom_R2_pos {A R : Rat} (_hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hR : 1 ≤ R) :
    0 < A + (R * R) * (1 - A) := by
  have h1A : 0 ≤ 1 - A := rat_sub_nonneg_of_le hA1
  have hR2 : 1 ≤ R * R := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hR (Rat.le_trans (by decide) hR)
    have h2 : R * 1 = R := by grind
    rw [h2] at h1
    exact Rat.le_trans hR h1
  have hge1 : 1 ≤ A + (R * R) * (1 - A) := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hR2 h1A
    have h2 : 1 * (1 - A) = 1 - A := by grind
    rw [h2] at h1
    have h3 : A + (1 - A) ≤ A + (R * R) * (1 - A) := Rat.add_le_add_left.mpr h1
    have h4 : A + (1 - A) = 1 := by grind
    rw [h4] at h3
    exact h3
  exact rat_lt_of_lt_of_le (by decide) hge1

/-! ## Theorem 3: Exact Single-Draft (`K = 1`) Quantized-Draft Acceptance Loss -/

private theorem min_sub_min_le_pos_part (p q q' : Rat) :
    min p q - min p q' ≤ if q' ≤ q then q - q' else 0 := by
  by_cases hqq' : q' ≤ q
  · simp only [hqq', ↓reduceIte]
    by_cases hpq' : p ≤ q'
    · have hpq : p ≤ q := Rat.le_trans hpq' hqq'
      rw [rat_min_eq_left hpq, rat_min_eq_left hpq']
      have : p - p = 0 := by grind
      rw [this]
      exact rat_sub_nonneg_of_le hqq'
    · have hq'p : q' ≤ p := Rat.le_of_lt (Rat.not_le.mp hpq')
      rw [rat_min_eq_right hq'p]
      have hle : min p q ≤ q := rat_min_le_right p q
      apply rat_le_of_sub_nonneg
      have : (q - q') - (min p q - q') = q - min p q := by grind
      rw [this]
      exact rat_sub_nonneg_of_le hle
  · simp only [hqq', ↓reduceIte]
    have hqq'_lt : q ≤ q' := Rat.le_of_lt (Rat.not_le.mp hqq')
    have hle : min p q ≤ min p q' :=
      rat_le_min (rat_min_le_left p q) (Rat.le_trans (rat_min_le_right p q) hqq'_lt)
    apply rat_le_of_sub_nonneg
    have : 0 - (min p q - min p q') = min p q' - min p q := by grind
    rw [this]
    exact rat_sub_nonneg_of_le hle

private theorem quantized_draft_loss_k1_one_side {V : Nat} (hV : 0 < V) {R : Rat} (hR : 1 ≤ R)
    (p w w' : Fin V → Rat) (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    (hbound : ∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) :
    alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w') ≤ (R - 1) / (R + 1) := by
  let q := softmaxRat w
  let q' := softmaxRat w'
  let P : Fin V → Prop := fun i => q' i ≤ q i
  have hdiff : alpha1 p q - alpha1 p q' ≤
      sumRat (fun i => if P i then q i else 0) - sumRat (fun i => if P i then q' i else 0) := by
    unfold alpha1
    rw [← sumRat_sub, ← sumRat_sub]
    apply sumRat_le_sumRat
    intro i
    by_cases hp : P i
    · simp only [hp, ↓reduceIte]
      have h := min_sub_min_le_pos_part (p i) (q i) (q' i)
      simp only [P] at hp
      simp only [hp, ↓reduceIte] at h
      exact h
    · simp only [hp, ↓reduceIte]
      have hz : (0 : Rat) - 0 = 0 := by grind
      rw [hz]
      have h := min_sub_min_le_pos_part (p i) (q i) (q' i)
      simp only [P] at hp
      simp only [hp, ↓reduceIte] at h
      exact h
  have ⟨hA0, hA1, hA'0, _, hratio⟩ := softmax_subset_ratio_bound hV hR w w' hw hw' hbound P
  let A := sumRat (fun i => if P i then q i else 0)
  let A' := sumRat (fun i => if P i then q' i else 0)
  have hden_pos : 0 < A + (R * R) * (1 - A) := denom_R2_pos hA0 hA1 hR
  have hRp1_pos : 0 < R + 1 := by
    have h0R : (0 : Rat) ≤ R := Rat.le_trans (by decide) hR
    have h01 : (0 : Rat) < 1 := by decide
    have h := rat_add_lt_add_of_le_of_lt h0R h01
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at h; exact h
  have hRsub : 0 ≤ R - 1 := rat_sub_nonneg_of_le hR
  -- From A * (1 - A') ≤ R^2 * A' * (1 - A), we get A ≤ A' * (A + R^2 * (1 - A))
  have hA_le_A'den : A ≤ A' * (A + (R * R) * (1 - A)) := by
    apply rat_le_of_sub_nonneg
    have hEq : A' * (A + (R * R) * (1 - A)) - A = (R * R) * A' * (1 - A) - A * (1 - A') := by grind
    rw [hEq]
    exact rat_sub_nonneg_of_le hratio
  -- Therefore (A - A') * (A + R^2 * (1 - A)) ≤ (R^2 - 1) * A * (1 - A)
  have hmul_bound : (A - A') * (A + (R * R) * (1 - A)) ≤ (R * R - 1) * A * (1 - A) := by
    apply rat_le_of_sub_nonneg
    have hEq : (R * R - 1) * A * (1 - A) - (A - A') * (A + (R * R) * (1 - A)) =
        A' * (A + (R * R) * (1 - A)) - A := by grind
    rw [hEq]
    exact rat_sub_nonneg_of_le hA_le_A'den
  -- Exact SOS identity: (R - 1) * (A + R^2 * (1 - A)) - (R + 1) * (R^2 - 1) * A * (1 - A) = (R - 1) * (R*(1-A) - A)^2 ≥ 0
  have hsos : (R + 1) * ((R * R - 1) * A * (1 - A)) ≤ (R - 1) * (A + (R * R) * (1 - A)) := by
    apply rat_le_of_sub_nonneg
    have hEq : (R - 1) * (A + (R * R) * (1 - A)) - (R + 1) * ((R * R - 1) * A * (1 - A)) =
        (R - 1) * ((R * (1 - A) - A) * (R * (1 - A) - A)) := by grind
    rw [hEq]
    exact rat_mul_nonneg hRsub (rat_sq_nonneg _)
  have hcomb : ((A - A') * (R + 1)) * (A + (R * R) * (1 - A)) ≤
      (R - 1) * (A + (R * R) * (1 - A)) := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hmul_bound (Rat.le_of_lt hRp1_pos)
    have hL : (R + 1) * ((A - A') * (A + (R * R) * (1 - A))) =
        ((A - A') * (R + 1)) * (A + (R * R) * (1 - A)) := by grind
    rw [hL] at h1
    exact Rat.le_trans h1 hsos
  have hcancel : (A - A') * (R + 1) ≤ R - 1 := by
    have hinv := rat_inv_pos hden_pos
    have h1 := Rat.mul_le_mul_of_nonneg_right hcomb (Rat.le_of_lt hinv)
    have hne := rat_ne_zero_of_pos hden_pos
    have hL : ((A - A') * (R + 1)) * (A + (R * R) * (1 - A)) * (A + (R * R) * (1 - A))⁻¹ =
        (A - A') * (R + 1) := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne]; grind
    have hR' : (R - 1) * (A + (R * R) * (1 - A)) * (A + (R * R) * (1 - A))⁻¹ = R - 1 := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne]; grind
    rw [hL, hR'] at h1
    exact h1
  have hAA' : A - A' ≤ (R - 1) / (R + 1) := (rat_le_div_iff hRp1_pos).mpr hcancel
  exact Rat.le_trans hdiff hAA'

theorem quantized_draft_loss_k1_exact (V : Nat) (hV : 2 ≤ V) (R : Rat) (hR : 1 ≤ R) :
    (∀ (p w w' : Fin V → Rat), isProbDist p → (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      (alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w')).abs ≤ (R - 1) / (R + 1)) ∧
    (∃ (p w w' : Fin V → Rat), isProbDist p ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w') = (R - 1) / (R + 1)) := by
  have hVpos : 0 < V := by omega
  have hVm1pos : (0 : Rat) < ((V - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
  have hRpos : 0 < R := rat_lt_of_lt_of_le (by decide) hR
  have hRp1_pos : 0 < R + 1 := by
    have h01 : (0 : Rat) < 1 := by decide
    have h := rat_add_lt_add_of_le_of_lt (Rat.le_of_lt hRpos) h01
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at h; exact h
  constructor
  · intro p w w' _ hw hw' hbound
    rw [rat_abs_le_iff]
    refine ⟨quantized_draft_loss_k1_one_side hVpos hR p w w' hw hw' hbound, ?_⟩
    have hsym : -(alpha1 p (softmaxRat w) - alpha1 p (softmaxRat w')) =
        alpha1 p (softmaxRat w') - alpha1 p (softmaxRat w) := by grind
    rw [hsym]
    exact quantized_draft_loss_k1_one_side hVpos hR p w' w hw' hw (fun i => ⟨(hbound i).2, (hbound i).1⟩)
  · -- Sharpness witness: w = (R, 1/(V-1), ...), w' = (1, R/(V-1), ...), p = softmaxRat w
    let w : Fin V → Rat := fun i => if i.val = 0 then R else (1 : Rat) / ((V - 1 : Nat) : Rat)
    let w' : Fin V → Rat := fun i => if i.val = 0 then 1 else R / ((V - 1 : Nat) : Rat)
    have hw : ∀ i, 0 < w i := by
      intro i; dsimp only [w]
      by_cases h0 : i.val = 0
      · simp [h0]; exact hRpos
      · simp [h0]; exact rat_div_pos (by decide) hVm1pos
    have hw' : ∀ i, 0 < w' i := by
      intro i; dsimp only [w']
      by_cases h0 : i.val = 0
      · simp [h0]; decide
      · simp [h0]; exact rat_div_pos hRpos hVm1pos
    have hbound : ∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i := by
      intro i; dsimp only [w, w']
      have hR2 : 1 ≤ R * R := by
        have h1 := Rat.mul_le_mul_of_nonneg_left hR (Rat.le_of_lt hRpos)
        have h2 : R * 1 = R := by grind
        rw [h2] at h1; exact Rat.le_trans hR h1
      by_cases h0 : i.val = 0
      · simp only [h0, ↓reduceIte]
        refine ⟨?_, hR2⟩
        have hR1 : R * 1 = R := by grind
        rw [hR1]; exact Rat.le_refl
      · simp only [h0, ↓reduceIte]
        have hEq : R * ((1 : Rat) / ((V - 1 : Nat) : Rat)) = R / ((V - 1 : Nat) : Rat) := by
          simp only [Rat.div_def]; grind
        refine ⟨?_, ?_⟩
        · have hmul : R * (R / ((V - 1 : Nat) : Rat)) = (R * R) / ((V - 1 : Nat) : Rat) := by
            simp only [Rat.div_def]; grind
          rw [hmul, rat_div_le_div_iff hVm1pos hVm1pos]
          exact Rat.mul_le_mul_of_nonneg_right hR2 (Rat.le_of_lt hVm1pos)
        · rw [hEq]; exact Rat.le_refl
    have hsumW : sumRat w = R + 1 := by
      dsimp only [w]
      rw [sumRat_ite_eq_zero hVpos, Rat.div_def]
      have hcancel : ((V - 1 : Nat) : Rat) * (1 * ((V - 1 : Nat) : Rat)⁻¹) = 1 := by
        have h1 : ((V - 1 : Nat) : Rat) * (1 * ((V - 1 : Nat) : Rat)⁻¹) =
            ((V - 1 : Nat) : Rat) * ((V - 1 : Nat) : Rat)⁻¹ := by grind
        rw [h1, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hVm1pos)]
      rw [hcancel]
    have hsumW' : sumRat w' = R + 1 := by
      dsimp only [w']
      rw [sumRat_ite_eq_zero hVpos, Rat.div_def]
      have hcancel : ((V - 1 : Nat) : Rat) * (R * ((V - 1 : Nat) : Rat)⁻¹) = R := by
        have h1 : ((V - 1 : Nat) : Rat) * (R * ((V - 1 : Nat) : Rat)⁻¹) =
            R * (((V - 1 : Nat) : Rat) * ((V - 1 : Nat) : Rat)⁻¹) := by grind
        rw [h1, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hVm1pos)]; grind
      rw [hcancel]; grind
    refine ⟨softmaxRat w, w, w', softmaxRat_isProbDist hVpos w hw, hw, hw', hbound, ?_⟩
    have ha1 : alpha1 (softmaxRat w) (softmaxRat w) = 1 := by
      unfold alpha1
      have hcongr : sumRat (fun i => min (softmaxRat w i) (softmaxRat w i)) = sumRat (softmaxRat w) := by
        apply sumRat_congr; intro i; exact rat_min_eq_left Rat.le_refl
      rw [hcongr, softmaxRat_sum hVpos w hw]
    have ha2 : alpha1 (softmaxRat w) (softmaxRat w') = 2 / (R + 1) := by
      unfold alpha1
      have hcongr : sumRat (fun i => min (softmaxRat w i) (softmaxRat w' i)) =
          sumRat (fun i : Fin V => if i.val = 0 then (1 : Rat) / (R + 1)
            else ((1 : Rat) / ((V - 1 : Nat) : Rat)) / (R + 1)) := by
        apply sumRat_congr
        intro i
        unfold softmaxRat
        rw [hsumW, hsumW']
        dsimp only [w, w']
        by_cases h0 : i.val = 0
        · simp only [h0, ↓reduceIte]
          have hle : (1 : Rat) / (R + 1) ≤ R / (R + 1) := by
            rw [rat_div_le_div_iff hRp1_pos hRp1_pos]
            exact Rat.mul_le_mul_of_nonneg_right hR (Rat.le_of_lt hRp1_pos)
          exact rat_min_eq_right hle
        · simp only [h0, ↓reduceIte]
          have hle : ((1 : Rat) / ((V - 1 : Nat) : Rat)) / (R + 1) ≤
              (R / ((V - 1 : Nat) : Rat)) / (R + 1) := by
            rw [rat_div_le_div_iff hRp1_pos hRp1_pos]
            have h1 : (1 : Rat) / ((V - 1 : Nat) : Rat) ≤ R / ((V - 1 : Nat) : Rat) := by
              rw [rat_div_le_div_iff hVm1pos hVm1pos]
              exact Rat.mul_le_mul_of_nonneg_right hR (Rat.le_of_lt hVm1pos)
            exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hRp1_pos)
          exact rat_min_eq_left hle
      rw [hcongr, sumRat_ite_eq_zero hVpos]
      have hcancel : ((V - 1 : Nat) : Rat) * (((1 : Rat) / ((V - 1 : Nat) : Rat)) / (R + 1)) =
          (1 : Rat) / (R + 1) := by
        simp only [Rat.div_def]
        have h1 : ((V - 1 : Nat) : Rat) * (1 * ((V - 1 : Nat) : Rat)⁻¹ * (R + 1)⁻¹) =
            (((V - 1 : Nat) : Rat) * ((V - 1 : Nat) : Rat)⁻¹) * (R + 1)⁻¹ := by grind
        rw [h1, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hVm1pos)]
      rw [hcancel]; grind
    rw [ha1, ha2]
    have hcancel : (R + 1) * (R + 1)⁻¹ = 1 := Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hRp1_pos)
    simp only [Rat.div_def]
    grind

/-! ## Theorem 4: Exact Correlated Multi-Draft (`K ≥ 2`) Quantized-Draft Acceptance Loss -/

theorem quantized_draft_loss_multidraft_exact (K : Nat) (hK : 2 ≤ K) (V : Nat) (hV : 2 ≤ V)
    (R : Rat) (hR : 1 ≤ R) :
    (∀ (p w w' : Fin V → Rat), isProbDist p → (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') ≤
        (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R))) ∧
    (∃ (p w w' : Fin V → Rat), isProbDist p ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      alphaCorr K p (softmaxRat w) - alphaCorr K p (softmaxRat w') =
        (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R))) := by
  have hVpos : 0 < V := by omega
  have hVm1pos : (0 : Rat) < ((V - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have hKm1_ge1 : (1 : Rat) ≤ (K : Rat) - 1 := by
    have h2 : (2 : Rat) ≤ (K : Rat) := rat_natCast_le_natCast hK
    apply rat_le_of_sub_nonneg
    have : ((K : Rat) - 1) - 1 = (K : Rat) - 2 := by grind
    rw [this]; exact rat_sub_nonneg_of_le h2
  have hKm1_pos : (0 : Rat) < (K : Rat) - 1 := rat_lt_of_lt_of_le (by decide) hKm1_ge1
  have hRpos : 0 < R := rat_lt_of_lt_of_le (by decide) hR
  have hR2_ge1 : 1 ≤ R * R := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hR (Rat.le_of_lt hRpos)
    have h2 : R * 1 = R := by grind
    rw [h2] at h1; exact Rat.le_trans hR h1
  have hR2_sub : 0 ≤ R * R - 1 := rat_sub_nonneg_of_le hR2_ge1
  have hDpos : 0 < 1 + ((K : Rat) - 1) * (R * R) := by
    have h01 : (0 : Rat) < 1 := by decide
    have h := rat_add_lt_add_of_lt_of_le h01
      (rat_mul_nonneg (Rat.le_of_lt hKm1_pos) (Rat.le_trans (by decide) hR2_ge1))
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at h; exact h
  constructor
  · intro p w w' hp hw hw' hbound
    let q := softmaxRat w
    let q' := softmaxRat w'
    let P : Fin V → Prop := fun i => (K : Rat) * q' i < min (p i) ((K : Rat) * q i)
    have hdiff_le : alphaCorr K p q - alphaCorr K p q' ≤
        sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) -
        (K : Rat) * sumRat (fun i => if P i then q' i else 0) := by
      unfold alphaCorr
      rw [← sumRat_mul_left, ← sumRat_sub, ← sumRat_sub]
      apply sumRat_le_sumRat
      intro i
      by_cases hPi : P i
      · simp only [hPi, ↓reduceIte]
        have hlt : (K : Rat) * q' i < p i := rat_lt_of_lt_of_le hPi (rat_min_le_left _ _)
        rw [rat_min_eq_right (Rat.le_of_lt hlt)]
        exact Rat.le_refl
      · simp only [hPi, ↓reduceIte]
        have hz : (0 : Rat) - (K : Rat) * 0 = 0 := by grind
        rw [hz]
        have hle_q' : min (p i) ((K : Rat) * q i) ≤ (K : Rat) * q' i := Rat.not_lt.mp hPi
        have hle : min (p i) ((K : Rat) * q i) ≤ min (p i) ((K : Rat) * q' i) :=
          rat_le_min (rat_min_le_left _ _) hle_q'
        apply rat_le_of_sub_nonneg
        have : 0 - (min (p i) ((K : Rat) * q i) - min (p i) ((K : Rat) * q' i)) =
            min (p i) ((K : Rat) * q' i) - min (p i) ((K : Rat) * q i) := by grind
        rw [this]; exact rat_sub_nonneg_of_le hle
    have ⟨hA0, hA1, hA'0, _, hratio⟩ := softmax_subset_ratio_bound hVpos hR w w' hw hw' hbound P
    let A := sumRat (fun i => if P i then q i else 0)
    let A' := sumRat (fun i => if P i then q' i else 0)
    have hden_pos : 0 < A + (R * R) * (1 - A) := denom_R2_pos hA0 hA1 hR
    have hA_le_A'den : A ≤ A' * (A + (R * R) * (1 - A)) := by
      apply rat_le_of_sub_nonneg
      have hEq : A' * (A + (R * R) * (1 - A)) - A = (R * R) * A' * (1 - A) - A * (1 - A') := by grind
      rw [hEq]; exact rat_sub_nonneg_of_le hratio
    have hA'_ge : A / (A + (R * R) * (1 - A)) ≤ A' := (rat_div_le_iff hden_pos).mpr hA_le_A'den
    cases @Rat.le_total ((K : Rat) * A) 1 with
    | inl hKA_le1 =>
      -- Case K * A ≤ 1: bound by K * (A - A')
      have hsum_le_KA : sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) ≤ (K : Rat) * A := by
        change sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) ≤
          (K : Rat) * sumRat (fun i => if P i then q i else 0)
        rw [← sumRat_mul_left]
        apply sumRat_le_sumRat
        intro i
        by_cases hPi : P i
        · simp only [hPi, ↓reduceIte]; exact rat_min_le_right _ _
        · simp only [hPi, ↓reduceIte]
          have hz : (K : Rat) * 0 = 0 := by grind
          rw [hz]; exact Rat.le_refl
      have h1 : alphaCorr K p q - alphaCorr K p q' ≤ (K : Rat) * (A - A') := by
        have hstep : sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) - (K : Rat) * A' ≤
            (K : Rat) * A - (K : Rat) * A' := by
          apply rat_le_of_sub_nonneg
          have hEq : ((K : Rat) * A - (K : Rat) * A') -
              (sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) - (K : Rat) * A') =
              (K : Rat) * A - sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) := by grind
          rw [hEq]; exact rat_sub_nonneg_of_le hsum_le_KA
        have hfactor : (K : Rat) * A - (K : Rat) * A' = (K : Rat) * (A - A') := by grind
        rw [hfactor] at hstep
        exact Rat.le_trans hdiff_le hstep
      -- Show K * (A - A') ≤ K * A * (1 - A) * (R^2 - 1) / (A + R^2*(1 - A)) ≤ (K - 1)*(R^2 - 1) / (1 + (K - 1)*R^2)
      have hAA'_bound : (A - A') * (A + (R * R) * (1 - A)) ≤ (R * R - 1) * A * (1 - A) := by
        apply rat_le_of_sub_nonneg
        have hEq : (R * R - 1) * A * (1 - A) - (A - A') * (A + (R * R) * (1 - A)) =
            A' * (A + (R * R) * (1 - A)) - A := by grind
        rw [hEq]; exact rat_sub_nonneg_of_le hA_le_A'den
      have hKAA' : (K : Rat) * (A - A') ≤ ((K : Rat) * A * (1 - A) * (R * R - 1)) / (A + (R * R) * (1 - A)) := by
        rw [rat_le_div_iff hden_pos]
        have hmul := Rat.mul_le_mul_of_nonneg_left hAA'_bound (Rat.le_of_lt hKpos)
        have hL : (K : Rat) * ((A - A') * (A + (R * R) * (1 - A))) =
            (K : Rat) * (A - A') * (A + (R * R) * (1 - A)) := by grind
        have hR' : (K : Rat) * ((R * R - 1) * A * (1 - A)) =
            (K : Rat) * A * (1 - A) * (R * R - 1) := by grind
        rw [hL, hR'] at hmul
        exact hmul
      -- Exact factorization: (K - 1)*(A + R^2*(1-A)) - K*A*(1-A)*(1 + (K-1)*R^2) = (1 - K*A) * (R^2*(K-1)*(1-A) - A) ≥ 0
      have hfrac : ((K : Rat) * A * (1 - A) * (R * R - 1)) / (A + (R * R) * (1 - A)) ≤
          (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R)) := by
        rw [rat_div_le_div_iff hden_pos hDpos]
        apply rat_le_of_sub_nonneg
        have hEq : (((K : Rat) - 1) * (R * R - 1)) * (A + (R * R) * (1 - A)) -
            ((K : Rat) * A * (1 - A) * (R * R - 1)) * (1 + ((K : Rat) - 1) * (R * R)) =
            (R * R - 1) * ((1 - (K : Rat) * A) * ((R * R) * ((K : Rat) - 1) * (1 - A) - A)) := by
          grind
        rw [hEq]
        have h1KA : 0 ≤ 1 - (K : Rat) * A := rat_sub_nonneg_of_le hKA_le1
        have h2A : (2 : Rat) * A ≤ (K : Rat) * A :=
          Rat.mul_le_mul_of_nonneg_right (rat_natCast_le_natCast hK) hA0
        have hA_le_1A : A ≤ 1 - A := by
          apply rat_le_of_sub_nonneg
          have : (1 - A) - A = 1 - (2 : Rat) * A := by grind
          rw [this]; exact rat_sub_nonneg_of_le (Rat.le_trans h2A hKA_le1)
        have hcoef : (1 : Rat) ≤ (R * R) * ((K : Rat) - 1) := by
          have hm := Rat.mul_le_mul_of_nonneg_left hKm1_ge1 (Rat.le_trans (by decide) hR2_ge1)
          have h1 : (R * R) * 1 = R * R := by grind
          rw [h1] at hm; exact Rat.le_trans hR2_ge1 hm
        have hinner : 0 ≤ (R * R) * ((K : Rat) - 1) * (1 - A) - A := by
          have hm := Rat.mul_le_mul_of_nonneg_right hcoef (rat_sub_nonneg_of_le hA1)
          have h1 : 1 * (1 - A) = 1 - A := by grind
          rw [h1] at hm
          exact rat_sub_nonneg_of_le (Rat.le_trans hA_le_1A hm)
        exact rat_mul_nonneg hR2_sub (rat_mul_nonneg h1KA hinner)
      exact Rat.le_trans h1 (Rat.le_trans hKAA' hfrac)
    | inr hKA_ge1 =>
      -- Case 1 ≤ K * A: bound by 1 - K * A' ≤ 1 - K / (1 + (K - 1) * R^2) = (K - 1)*(R^2 - 1) / (1 + (K - 1)*R^2)
      have hsum_le_1 : sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) ≤ 1 := by
        have hle : sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) ≤ sumRat p := by
          apply sumRat_le_sumRat
          intro i
          by_cases hPi : P i
          · simp only [hPi, ↓reduceIte]; exact rat_min_le_left _ _
          · simp only [hPi, ↓reduceIte]; exact hp.1 i
        rw [hp.2] at hle; exact hle
      have h1 : alphaCorr K p q - alphaCorr K p q' ≤ 1 - (K : Rat) * A' := by
        have hstep : sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) - (K : Rat) * A' ≤
            1 - (K : Rat) * A' := by
          apply rat_le_of_sub_nonneg
          have hEq : (1 - (K : Rat) * A') -
              (sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) - (K : Rat) * A') =
              1 - sumRat (fun i => if P i then min (p i) ((K : Rat) * q i) else 0) := by grind
          rw [hEq]; exact rat_sub_nonneg_of_le hsum_le_1
        exact Rat.le_trans hdiff_le hstep
      have hA'_ge_inv : (1 : Rat) / (1 + ((K : Rat) - 1) * (R * R)) ≤ A' := by
        have hstep : (1 : Rat) / (1 + ((K : Rat) - 1) * (R * R)) ≤ A / (A + (R * R) * (1 - A)) := by
          rw [rat_div_le_div_iff hDpos hden_pos]
          apply rat_le_of_sub_nonneg
          have hEq : A * (1 + ((K : Rat) - 1) * (R * R)) - 1 * (A + (R * R) * (1 - A)) =
              (R * R) * ((K : Rat) * A - 1) := by grind
          rw [hEq]
          exact rat_mul_nonneg (Rat.le_trans (by decide) hR2_ge1) (rat_sub_nonneg_of_le hKA_ge1)
        exact Rat.le_trans hstep hA'_ge
      have hKA'_ge : (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) ≤ (K : Rat) * A' := by
        have hm := Rat.mul_le_mul_of_nonneg_left hA'_ge_inv (Rat.le_of_lt hKpos)
        have hL : (K : Rat) * ((1 : Rat) / (1 + ((K : Rat) - 1) * (R * R))) =
            (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) := by simp only [Rat.div_def]; grind
        rw [hL] at hm; exact hm
      have h2 : 1 - (K : Rat) * A' ≤ (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R)) := by
        have hEq : 1 - (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) =
            (((K : Rat) - 1) * (R * R - 1)) / (1 + ((K : Rat) - 1) * (R * R)) := by
          have hcancel := Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hDpos)
          simp only [Rat.div_def]; grind
        rw [← hEq]
        apply rat_le_of_sub_nonneg
        have hsub : (1 - (K : Rat) / (1 + ((K : Rat) - 1) * (R * R))) - (1 - (K : Rat) * A') =
            (K : Rat) * A' - (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) := by grind
        rw [hsub]; exact rat_sub_nonneg_of_le hKA'_ge
      exact Rat.le_trans h1 h2
  · -- Sharpness witness: p = (1, 0, ...), w = (R, (K-1)*R/(V-1), ...), w' = (1, (K-1)*R^2/(V-1), ...)
    let p : Fin V → Rat := fun i => if i.val = 0 then 1 else 0
    let w : Fin V → Rat := fun i =>
      if i.val = 0 then R else ((K : Rat) - 1) * R / ((V - 1 : Nat) : Rat)
    let w' : Fin V → Rat := fun i =>
      if i.val = 0 then 1 else ((K : Rat) - 1) * (R * R) / ((V - 1 : Nat) : Rat)
    have hp : isProbDist p := by
      refine ⟨?_, ?_⟩
      · intro i; dsimp only [p]; by_cases h0 : i.val = 0 <;> simp [h0]; decide
      · dsimp only [p]; rw [sumRat_ite_eq_zero hVpos]; grind
    have hw : ∀ i, 0 < w i := by
      intro i; dsimp only [w]
      by_cases h0 : i.val = 0
      · simp [h0]; exact hRpos
      · simp [h0]; exact rat_div_pos (rat_mul_pos hKm1_pos hRpos) hVm1pos
    have hw' : ∀ i, 0 < w' i := by
      intro i; dsimp only [w']
      by_cases h0 : i.val = 0
      · simp [h0]; decide
      · simp [h0]; exact rat_div_pos (rat_mul_pos hKm1_pos (rat_mul_pos hRpos hRpos)) hVm1pos
    have hbound : ∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i := by
      intro i; dsimp only [w, w']
      by_cases h0 : i.val = 0
      · simp only [h0, ↓reduceIte]
        refine ⟨?_, hR2_ge1⟩
        have hR1 : R * 1 = R := by grind
        rw [hR1]; exact Rat.le_refl
      · simp only [h0, ↓reduceIte]
        have hEq2 : R * (((K : Rat) - 1) * R / ((V - 1 : Nat) : Rat)) =
            ((K : Rat) - 1) * (R * R) / ((V - 1 : Nat) : Rat) := by
          simp only [Rat.div_def]; grind
        refine ⟨?_, by rw [hEq2]; exact Rat.le_refl⟩
        have hmul : R * (((K : Rat) - 1) * (R * R) / ((V - 1 : Nat) : Rat)) =
            (((K : Rat) - 1) * R * (R * R)) / ((V - 1 : Nat) : Rat) := by
          simp only [Rat.div_def]; grind
        rw [hmul, rat_div_le_div_iff hVm1pos hVm1pos]
        have h1 : ((K : Rat) - 1) * R ≤ ((K : Rat) - 1) * R * (R * R) := by
          have hm := Rat.mul_le_mul_of_nonneg_left hR2_ge1 (Rat.le_of_lt (rat_mul_pos hKm1_pos hRpos))
          have h1' : ((K : Rat) - 1) * R * 1 = ((K : Rat) - 1) * R := by grind
          rw [h1'] at hm; exact hm
        exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hVm1pos)
    have hsumW : sumRat w = (K : Rat) * R := by
      dsimp only [w]
      rw [sumRat_ite_eq_zero hVpos, Rat.div_def]
      have hcancel : ((V - 1 : Nat) : Rat) * (((K : Rat) - 1) * R * ((V - 1 : Nat) : Rat)⁻¹) =
          ((K : Rat) - 1) * R := by
        have h1 : ((V - 1 : Nat) : Rat) * (((K : Rat) - 1) * R * ((V - 1 : Nat) : Rat)⁻¹) =
            ((K : Rat) - 1) * R * (((V - 1 : Nat) : Rat) * ((V - 1 : Nat) : Rat)⁻¹) := by grind
        rw [h1, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hVm1pos)]; grind
      rw [hcancel]; grind
    have hsumW' : sumRat w' = 1 + ((K : Rat) - 1) * (R * R) := by
      dsimp only [w']
      rw [sumRat_ite_eq_zero hVpos, Rat.div_def]
      have hcancel : ((V - 1 : Nat) : Rat) * (((K : Rat) - 1) * (R * R) * ((V - 1 : Nat) : Rat)⁻¹) =
          ((K : Rat) - 1) * (R * R) := by
        have h1 : ((V - 1 : Nat) : Rat) * (((K : Rat) - 1) * (R * R) * ((V - 1 : Nat) : Rat)⁻¹) =
            ((K : Rat) - 1) * (R * R) * (((V - 1 : Nat) : Rat) * ((V - 1 : Nat) : Rat)⁻¹) := by grind
        rw [h1, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hVm1pos)]; grind
      rw [hcancel]
    refine ⟨p, w, w', hp, hw, hw', hbound, ?_⟩
    have ha1 : alphaCorr K p (softmaxRat w) = 1 := by
      unfold alphaCorr
      have hcongr : sumRat (fun i => min (p i) ((K : Rat) * softmaxRat w i)) =
          sumRat (fun i : Fin V => if i.val = 0 then (1 : Rat) else 0) := by
        apply sumRat_congr
        intro i
        unfold softmaxRat
        rw [hsumW]
        dsimp only [p, w]
        by_cases h0 : i.val = 0
        · simp only [h0, ↓reduceIte]
          have hKR : (K : Rat) * (R / ((K : Rat) * R)) = 1 := by
            rw [Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hKpos) (rat_ne_zero_of_pos hRpos)]
            have h1 : (K : Rat) * (R * (R⁻¹ * (K : Rat)⁻¹)) =
                ((K : Rat) * (K : Rat)⁻¹) * (R * R⁻¹) := by grind
            rw [h1, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hKpos),
                Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hRpos)]; grind
          rw [hKR]; exact rat_min_eq_left Rat.le_refl
        · simp only [h0, ↓reduceIte]
          have hnn : 0 ≤ (K : Rat) * (((K : Rat) - 1) * R / ((V - 1 : Nat) : Rat) / ((K : Rat) * R)) :=
            rat_mul_nonneg (Rat.le_of_lt hKpos)
              (rat_div_nonneg (rat_div_nonneg (rat_mul_nonneg (Rat.le_of_lt hKm1_pos) (Rat.le_of_lt hRpos)) hVm1pos)
                (rat_mul_pos hKpos hRpos))
          exact rat_min_eq_left hnn
      rw [hcongr, sumRat_ite_eq_zero hVpos]; grind
    have ha2 : alphaCorr K p (softmaxRat w') = (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) := by
      unfold alphaCorr
      have hcongr : sumRat (fun i => min (p i) ((K : Rat) * softmaxRat w' i)) =
          sumRat (fun i : Fin V => if i.val = 0 then (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) else 0) := by
        apply sumRat_congr
        intro i
        unfold softmaxRat
        rw [hsumW']
        dsimp only [p, w']
        by_cases h0 : i.val = 0
        · simp only [h0, ↓reduceIte]
          have hEq : (K : Rat) * ((1 : Rat) / (1 + ((K : Rat) - 1) * (R * R))) =
              (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) := by simp only [Rat.div_def]; grind
          rw [hEq]
          have hle : (K : Rat) / (1 + ((K : Rat) - 1) * (R * R)) ≤ 1 := by
            rw [rat_div_le_iff hDpos]
            apply rat_le_of_sub_nonneg
            have hsub : 1 * (1 + ((K : Rat) - 1) * (R * R)) - (K : Rat) =
                ((K : Rat) - 1) * (R * R - 1) := by grind
            rw [hsub]; exact rat_mul_nonneg (Rat.le_of_lt hKm1_pos) hR2_sub
          exact rat_min_eq_right hle
        · simp only [h0, ↓reduceIte]
          have hnn : 0 ≤ (K : Rat) * (((K : Rat) - 1) * (R * R) / ((V - 1 : Nat) : Rat) /
              (1 + ((K : Rat) - 1) * (R * R))) :=
            rat_mul_nonneg (Rat.le_of_lt hKpos)
              (rat_div_nonneg (rat_div_nonneg (rat_mul_nonneg (Rat.le_of_lt hKm1_pos)
                (Rat.le_trans (by decide) hR2_ge1)) hVm1pos) hDpos)
          exact rat_min_eq_left hnn
      rw [hcongr, sumRat_ite_eq_zero hVpos]; grind
    rw [ha1, ha2]
    have hcancel := Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hDpos)
    simp only [Rat.div_def]; grind

end SpecDecodingOt
