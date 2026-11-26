/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltaNetHouseholderE8.RatOrder

/-!
# Theorem 1: Exact Rational Householder Spectral-Stability `iff` Law

Proves that for any vector `k : Fin d → Rat` and scalar `β : Rat`,
`∀ v, ‖(I - β k k^T) v‖_2^2 ≤ ‖v‖_2^2 ↔ 0 ≤ β ‖k‖_2^2 ≤ 2`,
together with the exact eigenvalue `1 - β ‖k‖_2^2` along `k` and strict spectral
amplification whenever `β ‖k‖_2^2 > 2` and `‖k‖_2^2 > 0`.
-/

namespace DeltaNetHouseholderE8

theorem householderApply_normSq {d : Nat} (β : Rat) (k v : Fin d → Rat) :
    l2NormSq (householderApply β k v) =
      l2NormSq v - β * (2 - β * l2NormSq k) * (dotProd k v * dotProd k v) := by
  unfold l2NormSq householderApply dotProd
  have hterm : ∀ i : Fin d,
      (v i - β * finSum (fun j => k j * v j) * k i) *
      (v i - β * finSum (fun j => k j * v j) * k i) =
      (v i * v i) - (2 * β * finSum (fun j => k j * v j)) * (k i * v i) +
      (β * β * (finSum (fun j => k j * v j) * finSum (fun j => k j * v j))) * (k i * k i) := by
    intro i; grind
  rw [finSum_congr hterm, finSum_add, finSum_sub, finSum_mul_left, finSum_mul_left]
  grind

theorem householderApply_eigen_k {d : Nat} (β : Rat) (k : Fin d → Rat) :
    householderApply β k k = (fun i => (1 - β * l2NormSq k) * k i) ∧
    l2NormSq (householderApply β k k) =
      (1 - β * l2NormSq k) * (1 - β * l2NormSq k) * l2NormSq k := by
  constructor
  · funext i
    unfold householderApply l2NormSq
    grind
  · rw [householderApply_normSq]
    unfold l2NormSq
    grind

theorem rat_mul_two_sub_nonneg_iff (x : Rat) :
    (0 : Rat) ≤ x * (2 - x) ↔ ((0 : Rat) ≤ x ∧ x ≤ 2) := by
  constructor
  · intro h
    constructor
    · cases Rat.le_total (a := (0 : Rat)) (b := x) with
      | inl hx => exact hx
      | inr hx =>
        by_cases h0 : x = 0
        · rw [h0]; exact Rat.le_refl
        · have hneg : x < 0 := Rat.lt_of_le_of_ne hx h0
          have hpos2 : (0 : Rat) < 2 - x := by
            have : (0 : Rat) < -x := rat_neg_pos_of_neg hneg
            have h2 : (0 : Rat) < (2 : Rat) := by decide
            have heq : (2 : Rat) - x = 2 + (-x) := by grind
            rw [heq]; exact rat_add_pos h2 this
          have hprod : x * (2 - x) < 0 := by
            have h1 := rat_mul_pos (rat_neg_pos_of_neg hneg) hpos2
            have h2 := rat_neg_of_pos h1
            have heq : -((-x) * (2 - x)) = x * (2 - x) := by grind
            rw [← heq]; exact h2
          exact False.elim (Rat.not_le.mpr hprod h)
    · cases Rat.le_total (a := x) (b := (2 : Rat)) with
      | inl hx => exact hx
      | inr hx =>
        by_cases h2 : x = 2
        · rw [h2]; exact Rat.le_refl
        · have hgt : (2 : Rat) < x := Rat.lt_of_le_of_ne hx (Ne.symm h2)
          have hpos : (0 : Rat) < x := rat_lt_of_lt_of_le (by decide : (0 : Rat) < 2) (Rat.le_of_lt hgt)
          have hneg2 : 2 - x < 0 := by
            have h1 : (0 : Rat) < x - 2 := rat_sub_pos hgt
            have h2 := rat_neg_of_pos h1
            have heq : -(x - 2) = 2 - x := by grind
            rw [← heq]; exact h2
          have hprod : x * (2 - x) < 0 := by
            have h1 := rat_mul_pos hpos (rat_neg_pos_of_neg hneg2)
            have h2 := rat_neg_of_pos h1
            have heq : -(x * (-(2 - x))) = x * (2 - x) := by grind
            rw [← heq]; exact h2
          exact False.elim (Rat.not_le.mpr hprod h)
  · intro ⟨h0, h2⟩
    exact Rat.mul_nonneg h0 (rat_sub_nonneg h2)

theorem householder_contraction_iff {d : Nat} (β : Rat) (k : Fin d → Rat) :
    (∀ v : Fin d → Rat, l2NormSq (householderApply β k v) ≤ l2NormSq v) ↔
      ((0 : Rat) ≤ β * l2NormSq k ∧ β * l2NormSq k ≤ 2) := by
  have hk_nn : (0 : Rat) ≤ l2NormSq k := l2NormSq_nonneg k
  by_cases hk0 : l2NormSq k = 0
  · constructor
    · intro _
      rw [hk0, Rat.mul_zero]
      exact ⟨Rat.le_refl, by decide⟩
    · intro _ v
      rw [householderApply_normSq]
      have hk_all : ∀ i : Fin d, k i = 0 := (l2NormSq_eq_zero_iff k).mp hk0
      have hdot : dotProd k v = 0 := by
        unfold dotProd
        have hz : finSum (fun i => k i * v i) = finSum (fun _ : Fin d => (0 : Rat)) := by
          apply finSum_congr
          intro i; rw [hk_all i, Rat.zero_mul]
        rw [hz, finSum_zero]
      rw [hdot]
      have heq : l2NormSq v - β * (2 - β * l2NormSq k) * (0 * 0) = l2NormSq v := by grind
      rw [heq]; exact Rat.le_refl
  · have hk_pos : (0 : Rat) < l2NormSq k := Rat.lt_of_le_of_ne hk_nn (Ne.symm hk0)
    constructor
    · intro hall
      have hk := hall k
      rw [householderApply_normSq] at hk
      have hsub : (0 : Rat) ≤ β * (2 - β * l2NormSq k) * (l2NormSq k * l2NormSq k) := by
        have h1 := rat_sub_nonneg hk
        unfold l2NormSq at h1 ⊢
        grind
      have hfact : β * (2 - β * l2NormSq k) * (l2NormSq k * l2NormSq k) =
          (β * l2NormSq k * (2 - β * l2NormSq k)) * l2NormSq k := by grind
      rw [hfact] at hsub
      have h0 : (0 : Rat) * l2NormSq k ≤ (β * l2NormSq k * (2 - β * l2NormSq k)) * l2NormSq k := by
        rw [Rat.zero_mul]; exact hsub
      have hprod := rat_le_of_mul_pos_right hk_pos h0
      exact (rat_mul_two_sub_nonneg_iff (β * l2NormSq k)).mp hprod
    · intro ⟨hlo, hhi⟩ v
      rw [householderApply_normSq]
      have hβ_nn : (0 : Rat) ≤ β := by
        apply rat_le_of_mul_pos_right hk_pos
        rw [Rat.zero_mul]; exact hlo
      have hrem_nn : (0 : Rat) ≤ 2 - β * l2NormSq k := rat_sub_nonneg hhi
      have hterm_nn : (0 : Rat) ≤ β * (2 - β * l2NormSq k) * (dotProd k v * dotProd k v) :=
        Rat.mul_nonneg (Rat.mul_nonneg hβ_nn hrem_nn) (rat_sq_nonneg (dotProd k v))
      apply rat_le_of_sub_nonneg
      have heq : l2NormSq v - (l2NormSq v - β * (2 - β * l2NormSq k) * (dotProd k v * dotProd k v)) =
          β * (2 - β * l2NormSq k) * (dotProd k v * dotProd k v) := by grind
      rw [heq]; exact hterm_nn

theorem householder_strict_explosion {d : Nat} (β : Rat) (k : Fin d → Rat)
    (hk : (0 : Rat) < l2NormSq k) (hgt : (2 : Rat) < β * l2NormSq k) :
    l2NormSq k < l2NormSq (householderApply β k k) ∧
    (1 : Rat) < ratAbs (1 - β * l2NormSq k) := by
  have heig := (householderApply_eigen_k β k).2
  have hlt_neg1 : 1 - β * l2NormSq k < -1 := by
    apply rat_lt_of_sub_pos
    have h1 := rat_sub_pos hgt
    have heq : (-1 : Rat) - (1 - β * l2NormSq k) = β * l2NormSq k - 2 := by grind
    rw [heq]; exact h1
  have hneg : 1 - β * l2NormSq k ≤ 0 :=
    Rat.le_trans (Rat.le_of_lt hlt_neg1) (by decide)
  have habs : (1 : Rat) < ratAbs (1 - β * l2NormSq k) := by
    rw [ratAbs_of_nonpos hneg]
    apply rat_lt_of_sub_pos
    have h1 := rat_sub_pos hgt
    have heq : -(1 - β * l2NormSq k) - 1 = β * l2NormSq k - 2 := by grind
    rw [heq]; exact h1
  have hsq : (1 : Rat) < (1 - β * l2NormSq k) * (1 - β * l2NormSq k) := by
    rw [← ratAbs_sq]
    have hpos : (0 : Rat) < ratAbs (1 - β * l2NormSq k) :=
      rat_lt_of_lt_of_le (by decide : (0 : Rat) < 1) (Rat.le_of_lt habs)
    have h1 := rat_mul_lt_mul_of_pos_right habs hpos
    rw [Rat.one_mul] at h1
    exact rat_lt_of_lt_of_le habs (Rat.le_of_lt h1)
  refine ⟨?_, habs⟩
  rw [heig]
  have hmul := rat_mul_lt_mul_of_pos_right hsq hk
  rw [Rat.one_mul] at hmul
  exact hmul

/-- Headline Theorem 1 (`householder_spectral_stability_iff_exact`). -/
theorem householder_spectral_stability_iff_exact :
    (∀ (d : Nat) (β : Rat) (k v : Fin d → Rat),
      l2NormSq (householderApply β k v) =
        l2NormSq v - β * (2 - β * l2NormSq k) * (dotProd k v * dotProd k v)) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      householderApply β k k = (fun i => (1 - β * l2NormSq k) * k i) ∧
      l2NormSq (householderApply β k k) =
        (1 - β * l2NormSq k) * (1 - β * l2NormSq k) * l2NormSq k) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      (∀ v : Fin d → Rat, l2NormSq (householderApply β k v) ≤ l2NormSq v) ↔
        ((0 : Rat) ≤ β * l2NormSq k ∧ β * l2NormSq k ≤ 2)) ∧
    (∀ (d : Nat) (β : Rat) (k : Fin d → Rat),
      (0 : Rat) < l2NormSq k → (2 : Rat) < β * l2NormSq k →
        l2NormSq k < l2NormSq (householderApply β k k) ∧
        (1 : Rat) < ratAbs (1 - β * l2NormSq k)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d β k v; exact householderApply_normSq β k v
  · intro d β k; exact householderApply_eigen_k β k
  · intro d β k; exact householder_contraction_iff β k
  · intro d β k hk hgt; exact householder_strict_explosion β k hk hgt

end DeltaNetHouseholderE8
