/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonclipAdamwSr.RatOrder

/-!
# MuonClip Pitchfork Symmetry Breaking, RTN Overshoot vs RTZ Safety, and Asymmetric Ratio Laws

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
- Theorem 1 (`muonclip_pitchfork_symmetry_breaking_exact`)
- Theorem 2 (`muonclip_rtn_overshoot_vs_rtz_safety`)
- Theorem 6 (`asymmetric_muonclip_ratio_limit_exact`)
-/

namespace MuonclipAdamwSr

/-! ### Helper Identities for Theorem 1 -/

theorem muonclipQuartic_sym_factor (γ x : Rat) :
    muonclipQuartic 1 γ x = (x * x - γ) * (x * x - x + γ) := by
  unfold muonclipQuartic
  grind

theorem muonclipObj_sym_sos (A γ x : Rat) (hx : x ≠ 0) :
    muonclipObj A A γ x =
      A * (1 - 2 * γ) + A * ((x * x - x + γ) / x) * ((x * x - x + γ) / x) := by
  unfold muonclipObj
  have h1 : (γ / x) * x = γ := rat_div_mul_cancel hx
  have h2 : ((x * x - x + γ) / x) * x = x * x - x + γ := rat_div_mul_cancel hx
  have hxx : x * x ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hx h
    | inr h => exact hx h
  have hmul :
      (A * (1 - x) * (1 - x) + A * (1 - γ / x) * (1 - γ / x) -
        (A * (1 - 2 * γ) + A * ((x * x - x + γ) / x) * ((x * x - x + γ) / x))) *
      (x * x) = 0 := by
    have ha : (1 - γ / x) * x = x - γ := by grind
    have hb : ((x * x - x + γ) / x) * ((x * x - x + γ) / x) * (x * x) =
        (x * x - x + γ) * (x * x - x + γ) := by grind
    have hc : (1 - γ / x) * (1 - γ / x) * (x * x) = (x - γ) * (x - γ) := by grind
    grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h0 => grind
  | inr h0 => exact False.elim (hxx h0)

theorem muonclipObj_sym_diff_sq (A s x : Rat) (hs : s ≠ 0) (hx : x ≠ 0) :
    muonclipObj A A (s * s) x - muonclipObj A A (s * s) s =
      A * (((x - s) * (x - s)) / x) * ((((x - s) * (x - s)) / x) + (4 * s - 2)) := by
  have hL : muonclipObj A A (s * s) x =
      A * (1 - 2 * (s * s)) + A * ((x * x - x + s * s) / x) * ((x * x - x + s * s) / x) :=
    muonclipObj_sym_sos A (s * s) x hx
  have hR : muonclipObj A A (s * s) s =
      A * (1 - 2 * (s * s)) + A * ((s * s - s + s * s) / s) * ((s * s - s + s * s) / s) :=
    muonclipObj_sym_sos A (s * s) s hs
  have hs_simp : (s * s - s + s * s) / s = 2 * s - 1 := by
    rw [rat_div_eq_iff hs]; grind
  rw [hL, hR, hs_simp]
  have hxx : x * x ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hx h
    | inr h => exact hx h
  have hmul :
      ((A * (1 - 2 * (s * s)) + A * ((x * x - x + s * s) / x) * ((x * x - x + s * s) / x)) -
       (A * (1 - 2 * (s * s)) + A * (2 * s - 1) * (2 * s - 1)) -
       A * (((x - s) * (x - s)) / x) * ((((x - s) * (x - s)) / x) + (4 * s - 2))) *
      (x * x) = 0 := by
    have h1 : ((x * x - x + s * s) / x) * x = x * x - x + s * s := rat_div_mul_cancel hx
    have h2 : (((x - s) * (x - s)) / x) * x = (x - s) * (x - s) := rat_div_mul_cancel hx
    grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h0 => grind
  | inr h0 => exact False.elim (hxx h0)

theorem muonclipObj_sym_at_s (A s : Rat) (hs : s ≠ 0) :
    muonclipObj A A (s * s) s = 2 * A * (1 - s) * (1 - s) := by
  unfold muonclipObj
  have hdiv : (s * s) / s = s := by
    rw [rat_div_eq_iff hs]
  rw [hdiv]
  grind

/-! ### Theorem 1: `muonclip_pitchfork_symmetry_breaking_exact` -/

theorem muonclip_pitchfork_symmetry_breaking_exact :
    (∀ γ x : Rat, muonclipQuartic 1 γ x = (x * x - γ) * (x * x - x + γ)) ∧
    (∀ A γ x : Rat, x ≠ 0 →
      muonclipObj A A γ x =
        A * (1 - 2 * γ) + A * ((x * x - x + γ) / x) * ((x * x - x + γ) / x)) ∧
    (∀ A γ x : Rat, 0 < A → x ≠ 0 →
      A * (1 - 2 * γ) ≤ muonclipObj A A γ x ∧
      (x * x - x + γ = 0 → muonclipObj A A γ x = A * (1 - 2 * γ))) ∧
    (∀ A s x : Rat, 0 < A → (1 / 2 : Rat) ≤ s → 0 < x →
      muonclipObj A A (s * s) s ≤ muonclipObj A A (s * s) x ∧
      (x ≠ s → muonclipObj A A (s * s) s < muonclipObj A A (s * s) x)) ∧
    (∀ A s : Rat, 0 < A → 0 < s → s < (1 / 2 : Rat) →
      muonclipSecondDerivSym A s < 0 ∧
      (∀ x : Rat, 0 < x → x ≠ s → x + (s * s) / x < 2 - 2 * s →
        muonclipObj A A (s * s) x < muonclipObj A A (s * s) s) ∧
      muonclipObj A A (s * s) s - A * (1 - 2 * (s * s)) = A * (1 - 2 * s) * (1 - 2 * s) ∧
      0 < A * (1 - 2 * s) * (1 - 2 * s)) ∧
    (∀ A : Rat,
      ((1 / 4 : Rat) * (1 / 4) - 1 / 4 + 3 / 16 = 0 ∧
       (3 / 4 : Rat) * (3 / 4) - 3 / 4 + 3 / 16 = 0 ∧
       muonclipObj A A (3 / 16) (1 / 4) = A * (5 / 8) ∧
       muonclipObj A A (3 / 16) (3 / 4) = A * (5 / 8)) ∧
      ((1 / 8 : Rat) * (1 / 8) - 1 / 8 + 7 / 64 = 0 ∧
       (7 / 8 : Rat) * (7 / 8) - 7 / 8 + 7 / 64 = 0 ∧
       muonclipObj A A (7 / 64) (1 / 8) = A * (25 / 32) ∧
       muonclipObj A A (7 / 64) (7 / 8) = A * (25 / 32)) ∧
      (muonclipObj A A (1 / 9) (1 / 3) = A * (8 / 9) ∧
       A * (1 - 2 * (1 / 9)) = A * (7 / 9) ∧
       muonclipObj A A (1 / 9) (1 / 3) - A * (1 - 2 * (1 / 9)) = A * (1 / 9)) ∧
      (muonclipObj A A (1 / 16) (1 / 4) = A * (9 / 8) ∧
       A * (1 - 2 * (1 / 16)) = A * (7 / 8) ∧
       muonclipObj A A (1 / 16) (1 / 4) - A * (1 - 2 * (1 / 16)) = A * (1 / 4))) := by
  refine ⟨muonclipQuartic_sym_factor, muonclipObj_sym_sos, ?_, ?_, ?_, ?_⟩
  · intro A γ x hA hx
    rw [muonclipObj_sym_sos A γ x hx]
    constructor
    · apply rat_le_of_sub_nonneg
      have hsq : (0 : Rat) ≤ ((x * x - x + γ) / x) * ((x * x - x + γ) / x) :=
        rat_sq_nonneg _
      have hprod : (0 : Rat) ≤ A * (((x * x - x + γ) / x) * ((x * x - x + γ) / x)) :=
        Rat.mul_nonneg (Rat.le_of_lt hA) hsq
      have heq : A * (1 - 2 * γ) + A * ((x * x - x + γ) / x) * ((x * x - x + γ) / x) -
          A * (1 - 2 * γ) =
          A * (((x * x - x + γ) / x) * ((x * x - x + γ) / x)) := by grind
      rw [heq]; exact hprod
    · intro hroot
      rw [hroot]
      have h0 : (0 : Rat) / x = 0 := by rw [Rat.div_def, Rat.zero_mul]
      rw [h0]; grind
  · intro A s x hA hs hx
    have hspos : (0 : Rat) < s := rat_lt_of_lt_of_le (rat_div_pos (by decide) (by decide)) hs
    have hdiff := muonclipObj_sym_diff_sq A s x (Rat.ne_of_gt hspos) (Rat.ne_of_gt hx)
    have h4s : (0 : Rat) ≤ 4 * s - 2 := by
      apply rat_sub_nonneg
      have h := rat_mul_le_mul_of_nonneg_left hs (by decide : (0 : Rat) ≤ 4)
      have h2 : (4 : Rat) * (1 / 2) = 2 := by grind
      rw [h2] at h; exact h
    have hq_nonneg : (0 : Rat) ≤ ((x - s) * (x - s)) / x :=
      rat_div_nonneg (rat_sq_nonneg (x - s)) hx
    constructor
    · apply rat_le_of_sub_nonneg
      rw [hdiff]
      have h1 : (0 : Rat) ≤ A * (((x - s) * (x - s)) / x) :=
        Rat.mul_nonneg (Rat.le_of_lt hA) hq_nonneg
      have h2 : (0 : Rat) ≤ ((x - s) * (x - s)) / x + (4 * s - 2) :=
        rat_add_nonneg hq_nonneg h4s
      exact Rat.mul_nonneg h1 h2
    · intro hne
      apply rat_lt_of_sub_pos
      rw [hdiff]
      have hxms : x - s ≠ 0 := by intro h0; apply hne; grind
      have hq_pos : (0 : Rat) < ((x - s) * (x - s)) / x :=
        rat_div_pos (rat_sq_pos_of_ne_zero hxms) hx
      have h1 : (0 : Rat) < A * (((x - s) * (x - s)) / x) := rat_mul_pos hA hq_pos
      have h2 : (0 : Rat) < ((x - s) * (x - s)) / x + (4 * s - 2) :=
        rat_add_pos_of_pos_of_nonneg hq_pos h4s
      exact rat_mul_pos h1 h2
  · intro A s hA hs hs_half
    have hsne : s ≠ 0 := Rat.ne_of_gt hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold muonclipSecondDerivSym
      have h2s : 2 * s < 1 := by
        have h := rat_mul_lt_mul_of_pos_left hs_half (by decide : (0 : Rat) < 2)
        have h1 : (2 : Rat) * (1 / 2) = 1 := by grind
        rw [h1] at h; exact h
      have h2_lt : (2 : Rat) < 1 / s := rat_lt_div_of_mul_lt hs h2s
      have hneg : (0 : Rat) < 1 / s - 2 := rat_sub_pos h2_lt
      have h4A : (0 : Rat) < 4 * A := rat_mul_pos (by decide) hA
      have hprod : (0 : Rat) < (4 * A) * (1 / s - 2) := rat_mul_pos h4A hneg
      apply rat_lt_of_sub_pos
      have heq : 0 - 4 * A * (2 - 1 / s) = (4 * A) * (1 / s - 2) := by grind
      rw [heq]; exact hprod
    · intro x hx hne hnbhd
      have hxne : x ≠ 0 := Rat.ne_of_gt hx
      have hdiff := muonclipObj_sym_diff_sq A s x hsne hxne
      have hxms : x - s ≠ 0 := by intro h0; apply hne; grind
      have hq_pos : (0 : Rat) < ((x - s) * (x - s)) / x :=
        rat_div_pos (rat_sq_pos_of_ne_zero hxms) hx
      have hfac_eq : ((x - s) * (x - s)) / x + (4 * s - 2) =
          (x + (s * s) / x) - (2 - 2 * s) := by
        have h1 : (((x - s) * (x - s)) / x) * x = (x - s) * (x - s) := rat_div_mul_cancel hxne
        have h2 : ((s * s) / x) * x = s * s := rat_div_mul_cancel hxne
        have hmul : (((x - s) * (x - s)) / x + (4 * s - 2) -
            ((x + (s * s) / x) - (2 - 2 * s))) * x = 0 := by grind
        cases Rat.mul_eq_zero.mp hmul with
        | inl h0 => grind
        | inr h0 => exact False.elim (hxne h0)
      have hfac_neg : (0 : Rat) < -(((x - s) * (x - s)) / x + (4 * s - 2)) := by
        rw [hfac_eq]
        have h := rat_sub_pos hnbhd
        have heq : -((x + s * s / x) - (2 - 2 * s)) = (2 - 2 * s) - (x + s * s / x) := by grind
        rw [heq]; exact h
      apply rat_lt_of_sub_pos
      have heq : muonclipObj A A (s * s) s - muonclipObj A A (s * s) x =
          (A * (((x - s) * (x - s)) / x)) * (-(((x - s) * (x - s)) / x + (4 * s - 2))) := by
        grind
      rw [heq]
      exact rat_mul_pos (rat_mul_pos hA hq_pos) hfac_neg
    · rw [muonclipObj_sym_at_s A s hsne]
      grind
    · have h2s : 2 * s < 1 := by
        have h := rat_mul_lt_mul_of_pos_left hs_half (by decide : (0 : Rat) < 2)
        have h1 : (2 : Rat) * (1 / 2) = 1 := by grind
        rw [h1] at h; exact h
      have h1m2s : (0 : Rat) < 1 - 2 * s := rat_sub_pos h2s
      have hsq : (0 : Rat) < (1 - 2 * s) * (1 - 2 * s) := rat_mul_pos h1m2s h1m2s
      have heq : A * (1 - 2 * s) * (1 - 2 * s) = A * ((1 - 2 * s) * (1 - 2 * s)) := by grind
      rw [heq]
      exact rat_mul_pos hA hsq
  · intro A
    refine ⟨⟨by grind, by grind, ?_, ?_⟩, ⟨by grind, by grind, ?_, ?_⟩,
            ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · unfold muonclipObj; grind
    · unfold muonclipObj; grind
    · unfold muonclipObj; grind
    · unfold muonclipObj; grind
    · unfold muonclipObj; grind
    · grind
    · unfold muonclipObj; grind
    · unfold muonclipObj; grind
    · grind
    · unfold muonclipObj; grind

/-! ### Theorem 2: `muonclip_rtn_overshoot_vs_rtz_safety` -/

theorem muonclip_rtn_overshoot_vs_rtz_safety :
    (rtnOvershootFactor 3 = 289 / 256 ∧
     rtnOvershootFactor 7 = 66049 / 65536 ∧
     rtnOvershootFactor 10 = 4198401 / 4194304 ∧
     rtzUndershootFactor 3 = 49 / 64 ∧
     rtzUndershootFactor 7 = 16129 / 16384) ∧
    (∀ (m : Nat) (γ S_max τ sQ sK sQ' sK' : Rat),
      0 < S_max → 0 < τ → γ = τ / S_max →
      0 ≤ sQ → 0 ≤ sK → sQ * sK = γ →
      0 ≤ sQ' → 0 ≤ sK' →
      sQ' ≤ (1 + invPow2Rat (m + 1)) * sQ →
      sK' ≤ (1 + invPow2Rat (m + 1)) * sK →
      sQ' * sK' * S_max ≤ rtnOvershootFactor m * τ) ∧
    (∀ τ : Rat, 0 < τ →
      ((9 / 8 : Rat) * (9 / 8)) / ((35 / 32 : Rat) * (35 / 32)) * τ = (1296 / 1225 : Rat) * τ ∧
      τ < (1296 / 1225 : Rat) * τ ∧
      ((129 / 128 : Rat) * (129 / 128)) / ((515 / 512 : Rat) * (515 / 512)) * τ =
        (266256 / 265225 : Rat) * τ ∧
      τ < (266256 / 265225 : Rat) * τ) ∧
    (∀ (γ S_max τ sQ sK sQ' sK' : Rat),
      0 < S_max → 0 < τ → γ = τ / S_max →
      0 ≤ sQ' → sQ' ≤ sQ → 0 ≤ sK' → sK' ≤ sK → sQ * sK = γ →
      sQ' * sK' * S_max ≤ τ) ∧
    (∀ (m : Nat) (γ S_max τ sQ sK sQ' sK' : Rat),
      1 ≤ m → 0 < S_max → 0 < τ → γ = τ / S_max →
      0 ≤ sQ → 0 ≤ sK → sQ * sK = γ →
      (1 - invPow2Rat m) * sQ ≤ sQ' →
      (1 - invPow2Rat m) * sK ≤ sK' →
      rtzUndershootFactor m * τ ≤ sQ' * sK' * S_max) := by
  refine ⟨⟨by unfold rtnOvershootFactor invPow2Rat pow2Rat; grind,
           by unfold rtnOvershootFactor invPow2Rat pow2Rat; grind,
           by unfold rtnOvershootFactor invPow2Rat pow2Rat; grind,
           by unfold rtzUndershootFactor invPow2Rat pow2Rat; grind,
           by unfold rtzUndershootFactor invPow2Rat pow2Rat; grind⟩, ?_, ?_, ?_, ?_⟩
  · intro m γ S_max τ sQ sK sQ' sK' hS hτ hγ hsQ hsK hprod hsQ' hsK' hQ hK
    have hfac_nonneg : (0 : Rat) ≤ 1 + invPow2Rat (m + 1) :=
      rat_add_nonneg (by decide) (Rat.le_of_lt (invPow2Rat_pos (m + 1)))
    have h1 : sQ' * sK' ≤ ((1 + invPow2Rat (m + 1)) * sQ) * sK' :=
      rat_mul_le_mul_of_nonneg_right hQ hsK'
    have h2 : ((1 + invPow2Rat (m + 1)) * sQ) * sK' ≤
        ((1 + invPow2Rat (m + 1)) * sQ) * ((1 + invPow2Rat (m + 1)) * sK) :=
      rat_mul_le_mul_of_nonneg_left hK (Rat.mul_nonneg hfac_nonneg hsQ)
    have h3 : sQ' * sK' ≤ rtnOvershootFactor m * γ := by
      have h := Rat.le_trans h1 h2
      unfold rtnOvershootFactor
      have heq : ((1 + invPow2Rat (m + 1)) * sQ) * ((1 + invPow2Rat (m + 1)) * sK) =
          (1 + invPow2Rat (m + 1)) * (1 + invPow2Rat (m + 1)) * (sQ * sK) := by grind
      rw [heq, hprod] at h
      exact h
    have h4 := rat_mul_le_mul_of_nonneg_right h3 (Rat.le_of_lt hS)
    have hγS : γ * S_max = τ := by rw [hγ, rat_div_mul_cancel (Rat.ne_of_gt hS)]
    have heq : rtnOvershootFactor m * γ * S_max = rtnOvershootFactor m * τ := by
      rw [Rat.mul_assoc, hγS]
    rw [heq] at h4
    exact h4
  · intro τ hτ
    have hlt1 : (1 : Rat) < 1296 / 1225 :=
      rat_lt_div_of_mul_lt (by decide) (by rw [Rat.one_mul]; decide)
    have hlt2 : (1 : Rat) < 266256 / 265225 :=
      rat_lt_div_of_mul_lt (by decide) (by rw [Rat.one_mul]; decide)
    refine ⟨by grind, ?_, by grind, ?_⟩
    · have h := rat_mul_lt_mul_of_pos_right hlt1 hτ
      rw [Rat.one_mul] at h; exact h
    · have h := rat_mul_lt_mul_of_pos_right hlt2 hτ
      rw [Rat.one_mul] at h; exact h
  · intro γ S_max τ sQ sK sQ' sK' hS hτ hγ hsQ' hQ hsK' hK hprod
    have hsQ : (0 : Rat) ≤ sQ := Rat.le_trans hsQ' hQ
    have h1 : sQ' * sK' ≤ sQ * sK' := rat_mul_le_mul_of_nonneg_right hQ hsK'
    have h2 : sQ * sK' ≤ sQ * sK := rat_mul_le_mul_of_nonneg_left hK hsQ
    have h3 : sQ' * sK' ≤ γ := by rw [← hprod]; exact Rat.le_trans h1 h2
    have h4 := rat_mul_le_mul_of_nonneg_right h3 (Rat.le_of_lt hS)
    have hγS : γ * S_max = τ := by rw [hγ, rat_div_mul_cancel (Rat.ne_of_gt hS)]
    rw [hγS] at h4
    exact h4
  · intro m γ S_max τ sQ sK sQ' sK' hm hS hτ hγ hsQ hsK hprod hQ hK
    have h2m_ge : (1 : Rat) ≤ pow2Rat m := by
      unfold pow2Rat
      exact rat_natCast_le (Nat.pow_pos (by decide))
    have hinv_le : invPow2Rat m ≤ 1 := by
      unfold invPow2Rat
      apply rat_div_le_of_mul_le (pow2Rat_pos m)
      rw [Rat.one_mul]; exact h2m_ge
    have hfac_nonneg : (0 : Rat) ≤ 1 - invPow2Rat m := rat_sub_nonneg hinv_le
    have hsQ'_nonneg : (0 : Rat) ≤ sQ' := Rat.le_trans (Rat.mul_nonneg hfac_nonneg hsQ) hQ
    have h1 : ((1 - invPow2Rat m) * sQ) * ((1 - invPow2Rat m) * sK) ≤
        sQ' * ((1 - invPow2Rat m) * sK) :=
      rat_mul_le_mul_of_nonneg_right hQ (Rat.mul_nonneg hfac_nonneg hsK)
    have h2 : sQ' * ((1 - invPow2Rat m) * sK) ≤ sQ' * sK' :=
      rat_mul_le_mul_of_nonneg_left hK hsQ'_nonneg
    have h3 : rtzUndershootFactor m * γ ≤ sQ' * sK' := by
      have h := Rat.le_trans h1 h2
      unfold rtzUndershootFactor
      have heq : ((1 - invPow2Rat m) * sQ) * ((1 - invPow2Rat m) * sK) =
          (1 - invPow2Rat m) * (1 - invPow2Rat m) * (sQ * sK) := by grind
      rw [heq, hprod] at h
      exact h
    have h4 := rat_mul_le_mul_of_nonneg_right h3 (Rat.le_of_lt hS)
    have hγS : γ * S_max = τ := by rw [hγ, rat_div_mul_cancel (Rat.ne_of_gt hS)]
    have heq : rtzUndershootFactor m * γ * S_max = rtzUndershootFactor m * τ := by
      rw [Rat.mul_assoc, hγS]
    rw [heq] at h4
    exact h4

/-! ### Theorem 6: `asymmetric_muonclip_ratio_limit_exact` -/

theorem asymmetric_muonclip_ratio_limit_exact :
    (∀ A B α : Rat, 0 < A → 0 < B →
      muonclipQuadApprox A B α - muonclipQuadApprox A B (B / (A + B)) =
        (A + B) * (α - B / (A + B)) * (α - B / (A + B)) ∧
      muonclipQuadApprox A B (B / (A + B)) ≤ muonclipQuadApprox A B α) ∧
    (∀ A B : Rat, 0 < A → 0 < B →
      let r := A / B
      muonclipQuadApprox A B (B / (A + B)) / muonclipQuadApprox A B (1 / 2) =
        4 * r / ((1 + r) * (1 + r)) ∧
      1 - 4 * r / ((1 + r) * (1 + r)) = ((r - 1) / (r + 1)) * ((r - 1) / (r + 1))) ∧
    ((1 - 4 * (4 : Rat) / ((1 + 4) * (1 + 4)) = 9 / 25) ∧
     (1 - 4 * (9 : Rat) / ((1 + 9) * (1 + 9)) = 16 / 25) ∧
     (1 - 4 * (16 : Rat) / ((1 + 16) * (1 + 16)) = 225 / 289)) ∧
    (∀ A B s : Rat, 0 < A → 0 < B → 0 < s → s < 1 →
      let r := A / B
      muonclipObj A B (s * s) 1 / muonclipObj A B (s * s) s =
        ((1 + s) * (1 + s)) / (r + 1) ∧
      1 - muonclipObj A B (s * s) 1 / muonclipObj A B (s * s) s =
        (r - s * s - 2 * s) / (r + 1)) := by
  refine ⟨?_, ?_, ⟨by grind, by grind, by grind⟩, ?_⟩
  · intro A B α hA hB
    have hAB : (0 : Rat) < A + B := rat_add_pos hA hB
    have hABne : A + B ≠ 0 := Rat.ne_of_gt hAB
    have heq : muonclipQuadApprox A B α - muonclipQuadApprox A B (B / (A + B)) =
        (A + B) * (α - B / (A + B)) * (α - B / (A + B)) := by
      unfold muonclipQuadApprox
      have hdiv : (B / (A + B)) * (A + B) = B := rat_div_mul_cancel hABne
      have hmul : (A * α * α + B * (1 - α) * (1 - α) -
          (A * (B / (A + B)) * (B / (A + B)) + B * (1 - B / (A + B)) * (1 - B / (A + B))) -
          (A + B) * (α - B / (A + B)) * (α - B / (A + B))) * (A + B) = 0 := by grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (hABne h0)
    refine ⟨heq, ?_⟩
    apply rat_le_of_sub_nonneg
    rw [heq]
    have hsq : (0 : Rat) ≤ (α - B / (A + B)) * (α - B / (A + B)) := rat_sq_nonneg _
    have hprod : (0 : Rat) ≤ (A + B) * ((α - B / (A + B)) * (α - B / (A + B))) :=
      Rat.mul_nonneg (Rat.le_of_lt hAB) hsq
    have hrw : (A + B) * (α - B / (A + B)) * (α - B / (A + B)) =
        (A + B) * ((α - B / (A + B)) * (α - B / (A + B))) := by grind
    rw [hrw]; exact hprod
  · intro A B hA hB
    dsimp only
    have hBne : B ≠ 0 := Rat.ne_of_gt hB
    have hAB : (0 : Rat) < A + B := rat_add_pos hA hB
    have hABne : A + B ≠ 0 := Rat.ne_of_gt hAB
    have hr : (0 : Rat) < A / B := rat_div_pos hA hB
    have h1pr : (0 : Rat) < 1 + A / B := rat_add_pos (by decide) hr
    have h1pr_ne : 1 + A / B ≠ 0 := Rat.ne_of_gt h1pr
    have h1pr_sq_ne : (1 + A / B) * (1 + A / B) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos h1pr h1pr)
    have hquad_opt : muonclipQuadApprox A B (B / (A + B)) = (A * B) / (A + B) := by
      unfold muonclipQuadApprox
      rw [Eq.comm, rat_div_eq_iff hABne]
      have hdiv : (B / (A + B)) * (A + B) = B := rat_div_mul_cancel hABne
      have hmul : (A * B - (A * (B / (A + B)) * (B / (A + B)) +
          B * (1 - B / (A + B)) * (1 - B / (A + B))) * (A + B)) * (A + B) = 0 := by grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (hABne h0)
    have hquad_half : muonclipQuadApprox A B (1 / 2) = (A + B) / 4 := by
      unfold muonclipQuadApprox; grind
    have hquad_half_ne : muonclipQuadApprox A B (1 / 2) ≠ 0 := by
      rw [hquad_half]
      exact Rat.ne_of_gt (rat_div_pos hAB (by decide))
    constructor
    · rw [hquad_opt, hquad_half]
      apply rat_div_eq_of_cross (Rat.ne_of_gt (rat_div_pos hAB (by decide))) h1pr_sq_ne
      have h1 : (A / B) * B = A := rat_div_mul_cancel hBne
      have h2 : ((A * B) / (A + B)) * (A + B) = A * B := rat_div_mul_cancel hABne
      have hden_ne : (A + B) * (B * B) ≠ 0 :=
        Rat.ne_of_gt (rat_mul_pos hAB (rat_mul_pos hB hB))
      have hmul : ((A * B) / (A + B) * ((1 + A / B) * (1 + A / B)) -
          4 * (A / B) * ((A + B) / 4)) * ((A + B) * (B * B)) = 0 := by grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (hden_ne h0)
    · have hrp1_ne : A / B + 1 ≠ 0 := by
        have : A / B + 1 = 1 + A / B := by grind
        rw [this]; exact h1pr_ne
      have hmul : (1 - 4 * (A / B) / ((1 + A / B) * (1 + A / B)) -
          ((A / B - 1) / (A / B + 1)) * ((A / B - 1) / (A / B + 1))) *
          ((1 + A / B) * (1 + A / B)) = 0 := by
        have h1 : (4 * (A / B) / ((1 + A / B) * (1 + A / B))) * ((1 + A / B) * (1 + A / B)) =
            4 * (A / B) := rat_div_mul_cancel h1pr_sq_ne
        have h2 : ((A / B - 1) / (A / B + 1)) * (1 + A / B) = A / B - 1 := by
          have : 1 + A / B = A / B + 1 := by grind
          rw [this]; exact rat_div_mul_cancel hrp1_ne
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (h1pr_sq_ne h0)
  · intro A B s hA hB hs hs1
    dsimp only
    have hBne : B ≠ 0 := Rat.ne_of_gt hB
    have hsne : s ≠ 0 := Rat.ne_of_gt hs
    have h1ms : (0 : Rat) < 1 - s := rat_sub_pos hs1
    have hAB : (0 : Rat) < A + B := rat_add_pos hA hB
    have hr : (0 : Rat) < A / B := rat_div_pos hA hB
    have hrp1 : (0 : Rat) < A / B + 1 := rat_add_pos hr (by decide)
    have hrp1_ne : A / B + 1 ≠ 0 := Rat.ne_of_gt hrp1
    have hobj1 : muonclipObj A B (s * s) 1 = B * (1 - s * s) * (1 - s * s) := by
      unfold muonclipObj
      have hdiv : (s * s) / 1 = s * s := (rat_div_eq_iff (by decide)).mpr (by grind)
      rw [hdiv]; grind
    have hobjs : muonclipObj A B (s * s) s = (A + B) * (1 - s) * (1 - s) := by
      unfold muonclipObj
      have hdiv : (s * s) / s = s := by rw [rat_div_eq_iff hsne]
      rw [hdiv]; grind
    have hobjs_pos : (0 : Rat) < muonclipObj A B (s * s) s := by
      rw [hobjs]
      have heq : (A + B) * (1 - s) * (1 - s) = (A + B) * ((1 - s) * (1 - s)) := by grind
      rw [heq]; exact rat_mul_pos hAB (rat_mul_pos h1ms h1ms)
    have hratio : muonclipObj A B (s * s) 1 / muonclipObj A B (s * s) s =
        ((1 + s) * (1 + s)) / (A / B + 1) := by
      rw [hobj1, hobjs]
      apply rat_div_eq_of_cross (by rw [← hobjs]; exact Rat.ne_of_gt hobjs_pos) hrp1_ne
      have h1 : (A / B) * B = A := rat_div_mul_cancel hBne
      grind
    refine ⟨hratio, ?_⟩
    rw [hratio]
    have hmul : (1 - ((1 + s) * (1 + s)) / (A / B + 1) - (A / B - s * s - 2 * s) / (A / B + 1)) *
        (A / B + 1) = 0 := by
      have h1 : (((1 + s) * (1 + s)) / (A / B + 1)) * (A / B + 1) = (1 + s) * (1 + s) :=
        rat_div_mul_cancel hrp1_ne
      have h2 : ((A / B - s * s - 2 * s) / (A / B + 1)) * (A / B + 1) = A / B - s * s - 2 * s :=
        rat_div_mul_cancel hrp1_ne
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 => exact False.elim (hrp1_ne h0)

end MuonclipAdamwSr
