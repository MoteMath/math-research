/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UniversalVertexInvroot.Defs

/-!
# Universal All-`p` Vertex Law, Cubic Convergence, Degree-9 Dominance, and Pointwise Envelopes

All proofs are pure Lean 4 `Init` (zero Mathlib, zero `native_decide`, zero `sorry`).
-/

namespace UniversalVertexInvroot

/-! ## Elementary `Rat` Order, Division, and Power Helpers -/

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := Rat.add_le_add_right (c := -b) |>.mpr h
  grind

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := Rat.add_le_add_right (c := b) |>.mpr h
  grind

theorem rat_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a * b := by
  have h1 : (0 : Rat) ≤ a * b := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  have hne : a * b ≠ 0 := by
    intro h0
    have ha0 : a ≠ 0 := Rat.ne_of_gt ha
    have hb0 : b ≠ 0 := Rat.ne_of_gt hb
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha0 h
    | inr h => exact hb0 h
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    c * a ≤ c * b := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ b - a := rat_sub_nonneg h
  have h2 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]
  exact h2

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

theorem rat_mul_le_mul {a b c d : Rat}
    (hab : a ≤ b) (hcd : c ≤ d) (ha : (0 : Rat) ≤ a) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * d := by
  have hb : (0 : Rat) ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hab hc)
    (rat_mul_le_mul_of_nonneg_left hcd hb)

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  have hle : c * a ≤ c * b := rat_mul_le_mul_of_nonneg_left (Rat.le_of_lt h) (Rat.le_of_lt hc)
  have hne : c * a ≠ c * b := by
    intro heq
    have h0 : c * (b - a) = 0 := by grind
    cases Rat.mul_eq_zero.mp h0 with
    | inl hc0 => exact Rat.ne_of_gt hc hc0
    | inr hba =>
      have hab : a = b := by grind
      rw [hab] at h
      exact Rat.lt_irrefl h
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_mul_lt_mul_of_pos_right {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    a * c < b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_lt_mul_of_pos_left h hc

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := by
      have := rat_sub_nonneg h
      grind
    have eq : x * x = (-x) * (-x) := by grind
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_le_sq_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  rat_mul_le_mul hab hab ha ha

theorem rat_sub_pos_of_lt {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by
  have hle : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt h)
  have hne : a - b ≠ 0 := by
    intro h0
    have hab : a = b := by grind
    rw [hab] at h
    exact Rat.lt_irrefl h
  exact Rat.lt_of_le_of_ne hle (Ne.symm hne)

theorem rat_lt_of_lt_of_le {a b c : Rat} (hab : a < b) (hbc : b ≤ c) : a < c := by
  have hac : a ≤ c := Rat.le_trans (Rat.le_of_lt hab) hbc
  have hne : a ≠ c := by
    intro h
    rw [h] at hab
    exact Rat.not_le.mpr hab hbc
  exact Rat.lt_of_le_of_ne hac hne

theorem rat_lt_of_le_of_lt {a b c : Rat} (hab : a ≤ b) (hbc : b < c) : a < c := by
  have hac : a ≤ c := Rat.le_trans hab (Rat.le_of_lt hbc)
  have hne : a ≠ c := by
    intro h
    rw [h] at hab
    exact Rat.not_le.mpr hbc hab
  exact Rat.lt_of_le_of_ne hac hne

theorem rat_add_pos_of_pos_nonneg {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) < a + b := by
  have h1 : a ≤ a + b := by
    have := Rat.add_le_add_left (c := a) |>.mpr hb
    grind
  exact rat_lt_of_lt_of_le ha h1

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < a⁻¹ := by
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  have hinv : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hne
  cases Rat.le_total (a := (0 : Rat)) (b := a⁻¹) with
  | inl h =>
    have hne' : a⁻¹ ≠ 0 := by
      intro h0
      rw [h0] at hinv
      have : (0 : Rat) = 1 := by grind
      exact (by decide : (0 : Rat) ≠ 1) this
    exact Rat.lt_of_le_of_ne h (Ne.symm hne')
  | inr h =>
    have hprod := rat_mul_le_mul_of_nonneg_left h (Rat.le_of_lt ha)
    rw [hinv] at hprod
    have : (1 : Rat) ≤ 0 := by grind
    exact False.elim (Rat.not_le.mpr (by decide : (0 : Rat) < 1) this)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_mul_cancel_left {a b c : Rat} (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  have hdiff : c * (a - b) = 0 := by grind
  cases Rat.mul_eq_zero.mp hdiff with
  | inl h0 => exact False.elim (hc h0)
  | inr h0 => grind

theorem rat_inv_mul_eq {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  have hab : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact hb h
  apply rat_mul_cancel_left hab
  have h1 : (a * b) * (a * b)⁻¹ = 1 := Rat.mul_inv_cancel (a * b) hab
  have h2 : a * a⁻¹ = 1 := Rat.mul_inv_cancel a ha
  have h3 : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hb
  calc
    (a * b) * (a * b)⁻¹ = 1 := h1
    _ = 1 * 1 := by grind
    _ = (a * a⁻¹) * (b * b⁻¹) := by rw [h2, h3]
    _ = (a * b) * (a⁻¹ * b⁻¹) := by grind

theorem rat_natCast_pos {p : Nat} (hp : 1 ≤ p) : (0 : Rat) < (p : Rat) := by
  have h1 : (1 : Rat) ≤ (p : Rat) := by
    have hle : ((1 : Nat) : Int) ≤ ((p : Nat) : Int) := by omega
    have hR := Rat.intCast_le_intCast.mpr hle
    have h1eq : ((1 : Nat) : Rat) = (1 : Rat) := rfl
    rw [Rat.intCast_natCast, Rat.intCast_natCast, h1eq] at hR
    exact hR
  exact rat_lt_of_lt_of_le (by decide : (0 : Rat) < 1) h1

theorem rat_natCast_ne_zero {p : Nat} (hp : 1 ≤ p) : (p : Rat) ≠ 0 :=
  Rat.ne_of_gt (rat_natCast_pos hp)

theorem ratAbs_of_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) : ratAbs x = x := by
  unfold ratAbs
  have hnot : ¬(x < 0) := Rat.not_lt.mpr hx
  simp [hnot]

theorem ratAbs_of_neg {x : Rat} (hx : x < (0 : Rat)) : ratAbs x = -x := by
  unfold ratAbs
  simp [hx]

theorem ratPow_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) : ∀ n : Nat, (0 : Rat) ≤ ratPow x n
  | 0 => by unfold ratPow; decide
  | n + 1 => by
    unfold ratPow
    exact Rat.mul_nonneg (ratPow_nonneg hx n) hx

theorem ratPow_pos {x : Rat} (hx : (0 : Rat) < x) : ∀ n : Nat, (0 : Rat) < ratPow x n
  | 0 => by unfold ratPow; decide
  | n + 1 => by
    unfold ratPow
    exact rat_mul_pos (ratPow_pos hx n) hx

theorem ratPow_le_pow_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, ratPow a n ≤ ratPow b n
  | 0 => by unfold ratPow; exact Rat.le_refl
  | n + 1 => by
    unfold ratPow
    exact rat_mul_le_mul (ratPow_le_pow_of_nonneg ha hab n) hab (ratPow_nonneg ha n) ha

theorem rat_max_eq_right {a b : Rat} (h : a ≤ b) : max a b = b := by
  change (if a ≤ b then b else a) = b
  simp [h]

theorem rat_max_eq_left {a b : Rat} (h : b ≤ a) : max a b = a := by
  change (if a ≤ b then b else a) = a
  split
  · rename_i h'
    exact Rat.le_antisymm h h'
  · rfl

theorem rat_le_max_left (a b : Rat) : a ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact h
  | inr h => rw [rat_max_eq_left h]; exact Rat.le_refl

theorem rat_le_max_right (a b : Rat) : b ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact Rat.le_refl
  | inr h => rw [rat_max_eq_left h]; exact h

theorem rat_sq_le_max_sq {L v R : Rat} (hL : L ≤ v) (hR : v ≤ R) :
    v * v ≤ max (L * L) (R * R) := by
  cases Rat.le_total (a := (0 : Rat)) (b := v) with
  | inl hv =>
    have h1 : v * v ≤ R * R := rat_sq_le_sq_of_nonneg hv hR
    exact Rat.le_trans h1 (rat_le_max_right _ _)
  | inr hv =>
    have hneg_v : (0 : Rat) ≤ -v := by
      have := rat_sub_nonneg hv
      grind
    have hneg_L : -v ≤ -L := by
      have := rat_sub_nonneg hL
      exact rat_le_of_sub_nonneg (a := -L) (b := -v) (by grind)
    have h1 : (-v) * (-v) ≤ (-L) * (-L) := rat_sq_le_sq_of_nonneg hneg_v hneg_L
    have eq1 : (-v) * (-v) = v * v := by grind
    have eq2 : (-L) * (-L) = L * L := by grind
    rw [eq1, eq2] at h1
    exact Rat.le_trans h1 (rat_le_max_left _ _)

/-! ## Theorem 1: Universal All-`p` Coupled `G^{-1/p}` Vertex Law -/

private theorem inv_p_pos {p : Nat} (hp : 1 ≤ p) :
    (0 : Rat) < (p : Rat) ∧ (0 : Rat) < (p : Rat) + 1 ∧ (0 : Rat) < 2 * (p : Rat) + 2 := by
  have hpPos : (0 : Rat) < (p : Rat) := rat_natCast_pos hp
  have hp1Pos : (0 : Rat) < (p : Rat) + 1 :=
    rat_add_pos_of_pos_nonneg hpPos (by decide : (0 : Rat) ≤ 1)
  have h2p2Pos : (0 : Rat) < 2 * (p : Rat) + 2 := by
    have : (2 : Rat) * ((p : Rat) + 1) = 2 * (p : Rat) + 2 := by grind
    rw [← this]
    exact rat_mul_pos (by decide : (0 : Rat) < 2) hp1Pos
  exact ⟨hpPos, hp1Pos, h2p2Pos⟩

theorem taylor2InvRoot_eq_vertexInvRoot (p : Nat) (hp : 1 ≤ p) (m : Rat) :
    taylor2InvRoot p m = vertexInvRoot p m := by
  unfold taylor2InvRoot vertexInvRoot
  have ⟨hpPos, hp1Pos, h2p2Pos⟩ := inv_p_pos hp
  have hpNe : (p : Rat) ≠ 0 := Rat.ne_of_gt hpPos
  have hp1Ne : (p : Rat) + 1 ≠ 0 := Rat.ne_of_gt hp1Pos
  have h2Ne : (2 : Rat) ≠ 0 := by decide
  have h2p2Ne : 2 * (p : Rat) + 2 ≠ 0 := Rat.ne_of_gt h2p2Pos
  have h2ppNe : 2 * (p : Rat) * (p : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 2) hpPos) hpPos)
  have hD : (2 * (p : Rat) * (p : Rat)) * ((p : Rat) + 1) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 2) hpPos) hpPos) hp1Pos)
  -- Clear denominators by multiplying both sides by 2 * p^2 * (p + 1)
  apply rat_mul_cancel_left hD
  have hip : (p : Rat) * (p : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hpNe
  have hip1 : ((p : Rat) + 1) * ((p : Rat) + 1)⁻¹ = 1 := Rat.mul_inv_cancel _ hp1Ne
  have hi2p2 : (2 * (p : Rat) + 2) * (2 * (p : Rat) + 2)⁻¹ = 1 := Rat.mul_inv_cancel _ h2p2Ne
  have hi2pp : (2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹ = 1 :=
    Rat.mul_inv_cancel _ h2ppNe
  have h2p2_eq : 2 * (p : Rat) + 2 = 2 * ((p : Rat) + 1) := by grind
  have hinv_2p2 : (2 * (p : Rat) + 2)⁻¹ = (2 : Rat)⁻¹ * ((p : Rat) + 1)⁻¹ := by
    rw [h2p2_eq]; exact rat_inv_mul_eq h2Ne hp1Ne
  have hi2 : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ h2Ne
  simp only [Rat.div_def]
  rw [hinv_2p2]
  -- Reduce each product with inverses
  have hl1 : (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) * ((m - 1) * (p : Rat)⁻¹) =
      2 * (p : Rat) * ((p : Rat) + 1) * (m - 1) := by
    calc
      (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) * ((m - 1) * (p : Rat)⁻¹)
          = 2 * (p : Rat) * ((p : Rat) + 1) * (m - 1) * ((p : Rat) * (p : Rat)⁻¹) := by grind
      _ = 2 * (p : Rat) * ((p : Rat) + 1) * (m - 1) * 1 := by rw [hip]
      _ = 2 * (p : Rat) * ((p : Rat) + 1) * (m - 1) := by grind
  have hl2 : (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
      (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ * (m - 1) * (m - 1)) =
      ((p : Rat) + 1) * ((p : Rat) + 1) * (m - 1) * (m - 1) := by
    calc
      (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
          (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ * (m - 1) * (m - 1))
          = ((p : Rat) + 1) * ((p : Rat) + 1) * (m - 1) * (m - 1) *
              ((2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹) := by grind
      _ = ((p : Rat) + 1) * ((p : Rat) + 1) * (m - 1) * (m - 1) * 1 := by rw [hi2pp]
      _ = ((p : Rat) + 1) * ((p : Rat) + 1) * (m - 1) * (m - 1) := by grind
  have hr1 : (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
      ((2 * (p : Rat) + 1) * ((2 : Rat)⁻¹ * ((p : Rat) + 1)⁻¹)) =
      (p : Rat) * (p : Rat) * (2 * (p : Rat) + 1) := by
    calc
      (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
          ((2 * (p : Rat) + 1) * ((2 : Rat)⁻¹ * ((p : Rat) + 1)⁻¹))
          = (p : Rat) * (p : Rat) * (2 * (p : Rat) + 1) *
              (((2 : Rat) * (2 : Rat)⁻¹) * (((p : Rat) + 1) * ((p : Rat) + 1)⁻¹)) := by grind
      _ = (p : Rat) * (p : Rat) * (2 * (p : Rat) + 1) * (1 * 1) := by rw [hi2, hip1]
      _ = (p : Rat) * (p : Rat) * (2 * (p : Rat) + 1) := by grind
  have hr2 : (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
      (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ *
        (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹) *
        (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹)) =
      (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) *
        (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) := by
    have hsub : ((p : Rat) + 1) * (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹) =
        ((p : Rat) + 1) * m - (2 * (p : Rat) + 1) := by
      calc
        ((p : Rat) + 1) * (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹)
            = ((p : Rat) + 1) * m - (2 * (p : Rat) + 1) * (((p : Rat) + 1) * ((p : Rat) + 1)⁻¹) := by grind
        _ = ((p : Rat) + 1) * m - (2 * (p : Rat) + 1) * 1 := by rw [hip1]
        _ = ((p : Rat) + 1) * m - (2 * (p : Rat) + 1) := by grind
    calc
      (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
          (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ *
            (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹) *
            (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹))
          = ((2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹) *
            ((((p : Rat) + 1) * (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹)) *
             (((p : Rat) + 1) * (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹))) := by grind
      _ = 1 * ((((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) *
               (((p : Rat) + 1) * m - (2 * (p : Rat) + 1))) := by rw [hi2pp, hsub]
      _ = (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) *
          (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) := by grind
  have hLHS : (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
      (1 - (m - 1) * (p : Rat)⁻¹ +
        ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ * (m - 1) * (m - 1)) =
      2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1) -
        2 * (p : Rat) * ((p : Rat) + 1) * (m - 1) +
        ((p : Rat) + 1) * ((p : Rat) + 1) * (m - 1) * (m - 1) := by
    calc
      (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
          (1 - (m - 1) * (p : Rat)⁻¹ +
            ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ * (m - 1) * (m - 1))
          = 2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1) -
            (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) * ((m - 1) * (p : Rat)⁻¹) +
            (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
              (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ * (m - 1) * (m - 1)) := by grind
      _ = 2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1) -
            2 * (p : Rat) * ((p : Rat) + 1) * (m - 1) +
            ((p : Rat) + 1) * ((p : Rat) + 1) * (m - 1) * (m - 1) := by rw [hl1, hl2]
  have hRHS : (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
      ((2 * (p : Rat) + 1) * ((2 : Rat)⁻¹ * ((p : Rat) + 1)⁻¹) +
        ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ *
          (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹) *
          (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹)) =
      (p : Rat) * (p : Rat) * (2 * (p : Rat) + 1) +
        (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) *
          (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) := by
    calc
      (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
          ((2 * (p : Rat) + 1) * ((2 : Rat)⁻¹ * ((p : Rat) + 1)⁻¹) +
            ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ *
              (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹) *
              (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹))
          = (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
              ((2 * (p : Rat) + 1) * ((2 : Rat)⁻¹ * ((p : Rat) + 1)⁻¹)) +
            (2 * (p : Rat) * (p : Rat) * ((p : Rat) + 1)) *
              (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ *
                (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹) *
                (m - (2 * (p : Rat) + 1) * ((p : Rat) + 1)⁻¹)) := by grind
      _ = (p : Rat) * (p : Rat) * (2 * (p : Rat) + 1) +
            (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) *
              (((p : Rat) + 1) * m - (2 * (p : Rat) + 1)) := by rw [hr1, hr2]
  rw [hLHS, hRHS]
  grind

theorem universal_invroot_vertex_identity_and_positivity (p : Nat) (hp : 1 ≤ p) (m : Rat) :
    (taylor2InvRoot p m = vertexInvRoot p m) ∧
    ((3 / 4 : Rat) ≤ (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) ∧
      (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) ≤ vertexInvRoot p m) ∧
    (taylor2InvRoot p m = monoC0 p + monoC1 p * m + monoC2 p * m * m) ∧
    (ratAbs (monoC0 p) + ratAbs (monoC1 p) + ratAbs (monoC2 p) =
      1 + 4 / (p : Rat) + 2 / ((p : Rat) * (p : Rat)) ∧
     ratAbs ((2 * (p : Rat) + 1) / (2 * (p : Rat) + 2)) +
      ratAbs (((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) *
        (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
        (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1))) = 1) := by
  have ⟨hpPos, hp1Pos, h2p2Pos⟩ := inv_p_pos hp
  have hpNe : (p : Rat) ≠ 0 := Rat.ne_of_gt hpPos
  have hp1Ne : (p : Rat) + 1 ≠ 0 := Rat.ne_of_gt hp1Pos
  have h2Ne : (2 : Rat) ≠ 0 := by decide
  have h2ppPos : (0 : Rat) < 2 * (p : Rat) * (p : Rat) :=
    rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 2) hpPos) hpPos
  have hppPos : (0 : Rat) < (p : Rat) * (p : Rat) := rat_mul_pos hpPos hpPos
  have h2ppNe : 2 * (p : Rat) * (p : Rat) ≠ 0 := Rat.ne_of_gt h2ppPos
  have hppNe : (p : Rat) * (p : Rat) ≠ 0 := Rat.ne_of_gt hppPos
  have h1leP : (1 : Rat) ≤ (p : Rat) := by
    have hle : ((1 : Nat) : Int) ≤ ((p : Nat) : Int) := by omega
    have hR := Rat.intCast_le_intCast.mpr hle
    have h1eq : ((1 : Nat) : Rat) = (1 : Rat) := rfl
    rw [Rat.intCast_natCast, Rat.intCast_natCast, h1eq] at hR
    exact hR
  refine ⟨taylor2InvRoot_eq_vertexInvRoot p hp m, ?_, ?_, ?_⟩
  · constructor
    · -- 3/4 ≤ (2p + 1) / (2p + 2)
      apply rat_le_of_sub_nonneg
      have hdiff : (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) - (3 / 4 : Rat) =
          ((p : Rat) - 1) / (4 * ((p : Rat) + 1)) := by
        have h4p1Pos : (0 : Rat) < 4 * ((p : Rat) + 1) :=
          rat_mul_pos (by decide : (0 : Rat) < 4) hp1Pos
        apply rat_mul_cancel_left (Rat.ne_of_gt h4p1Pos)
        have hi2p2 : (2 * (p : Rat) + 2) * (2 * (p : Rat) + 2)⁻¹ = 1 :=
          Rat.mul_inv_cancel _ (Rat.ne_of_gt h2p2Pos)
        have hi4p1 : (4 * ((p : Rat) + 1)) * (4 * ((p : Rat) + 1))⁻¹ = 1 :=
          Rat.mul_inv_cancel _ (Rat.ne_of_gt h4p1Pos)
        simp only [Rat.div_def]
        have h1 : (4 * ((p : Rat) + 1)) * ((2 * (p : Rat) + 1) * (2 * (p : Rat) + 2)⁻¹) =
            2 * (2 * (p : Rat) + 1) := by
          calc
            (4 * ((p : Rat) + 1)) * ((2 * (p : Rat) + 1) * (2 * (p : Rat) + 2)⁻¹)
                = 2 * (2 * (p : Rat) + 1) * ((2 * (p : Rat) + 2) * (2 * (p : Rat) + 2)⁻¹) := by grind
            _ = 2 * (2 * (p : Rat) + 1) * 1 := by rw [hi2p2]
            _ = 2 * (2 * (p : Rat) + 1) := by grind
        have h2 : (4 * ((p : Rat) + 1)) * (((p : Rat) - 1) * (4 * ((p : Rat) + 1))⁻¹) =
            (p : Rat) - 1 := by
          calc
            (4 * ((p : Rat) + 1)) * (((p : Rat) - 1) * (4 * ((p : Rat) + 1))⁻¹)
                = ((p : Rat) - 1) * ((4 * ((p : Rat) + 1)) * (4 * ((p : Rat) + 1))⁻¹) := by grind
            _ = ((p : Rat) - 1) * 1 := by rw [hi4p1]
            _ = (p : Rat) - 1 := by grind
        calc
          (4 * ((p : Rat) + 1)) * ((2 * (p : Rat) + 1) * (2 * (p : Rat) + 2)⁻¹ - 3 * (4 : Rat)⁻¹)
              = (4 * ((p : Rat) + 1)) * ((2 * (p : Rat) + 1) * (2 * (p : Rat) + 2)⁻¹) -
                  (4 * ((p : Rat) + 1)) * (3 * (4 : Rat)⁻¹) := by grind
          _ = 2 * (2 * (p : Rat) + 1) - 3 * ((p : Rat) + 1) := by rw [h1]; grind
          _ = (p : Rat) - 1 := by grind
          _ = (4 * ((p : Rat) + 1)) * (((p : Rat) - 1) * (4 * ((p : Rat) + 1))⁻¹) := h2.symm
      rw [hdiff]
      exact rat_div_nonneg (rat_sub_nonneg h1leP) (rat_mul_pos (by decide : (0 : Rat) < 4) hp1Pos)
    · -- (2p + 1) / (2p + 2) ≤ vertexInvRoot p m
      unfold vertexInvRoot
      have hβ : (0 : Rat) ≤ ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) :=
        rat_div_nonneg (Rat.le_of_lt hp1Pos) h2ppPos
      have hsq : (0 : Rat) ≤ (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
          (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) := rat_sq_nonneg _
      have hprod : (0 : Rat) ≤ (((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat))) *
          ((m - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
           (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1))) := Rat.mul_nonneg hβ hsq
      have hadd := Rat.add_le_add_left (c := (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2)) |>.mpr hprod
      have heq : (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) +
          ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) *
            (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
            (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) =
          (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) +
          (((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat))) *
            ((m - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
             (m - (2 * (p : Rat) + 1) / ((p : Rat) + 1))) := by grind
      rw [heq]
      grind
  · -- Monomial expansion identity
    unfold taylor2InvRoot monoC0 monoC1 monoC2
    apply rat_mul_cancel_left h2ppNe
    have hip : (p : Rat) * (p : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hpNe
    have hipp : ((p : Rat) * (p : Rat)) * ((p : Rat) * (p : Rat))⁻¹ = 1 := Rat.mul_inv_cancel _ hppNe
    have hi2pp : (2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹ = 1 :=
      Rat.mul_inv_cancel _ h2ppNe
    simp only [Rat.div_def]
    have h1 : (2 * (p : Rat) * (p : Rat)) * ((m - 1) * (p : Rat)⁻¹) = 2 * (p : Rat) * (m - 1) := by
      calc (2 * (p : Rat) * (p : Rat)) * ((m - 1) * (p : Rat)⁻¹)
          = 2 * (p : Rat) * (m - 1) * ((p : Rat) * (p : Rat)⁻¹) := by grind
        _ = 2 * (p : Rat) * (m - 1) := by rw [hip]; grind
    have h2 : (2 * (p : Rat) * (p : Rat)) * ((1 : Rat) * (p : Rat)⁻¹) = 2 * (p : Rat) := by
      calc (2 * (p : Rat) * (p : Rat)) * ((1 : Rat) * (p : Rat)⁻¹)
          = 2 * (p : Rat) * ((p : Rat) * (p : Rat)⁻¹) := by grind
        _ = 2 * (p : Rat) := by rw [hip]; grind
    have h3 : (2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹) =
        2 * ((p : Rat) + 1) := by
      calc (2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹)
          = 2 * ((p : Rat) + 1) * (((p : Rat) * (p : Rat)) * ((p : Rat) * (p : Rat))⁻¹) := by grind
        _ = 2 * ((p : Rat) + 1) := by rw [hipp]; grind
    have h4 : (2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹) =
        (p : Rat) + 1 := by
      calc (2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)
          = ((p : Rat) + 1) * ((2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹) := by grind
        _ = (p : Rat) + 1 := by rw [hi2pp]; grind
    calc
      (2 * (p : Rat) * (p : Rat)) *
          (1 - (m - 1) * (p : Rat)⁻¹ +
            ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ * (m - 1) * (m - 1))
          = 2 * (p : Rat) * (p : Rat) -
            (2 * (p : Rat) * (p : Rat)) * ((m - 1) * (p : Rat)⁻¹) +
            ((2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) *
              ((m - 1) * (m - 1)) := by grind
      _ = 2 * (p : Rat) * (p : Rat) - 2 * (p : Rat) * (m - 1) +
            ((p : Rat) + 1) * ((m - 1) * (m - 1)) := by rw [h1, h4]
      _ = (2 * (p : Rat) * (p : Rat) + 2 * (p : Rat) + ((p : Rat) + 1)) +
            (-(2 * (p : Rat)) - 2 * ((p : Rat) + 1)) * m +
            ((p : Rat) + 1) * (m * m) := by grind
      _ = (2 * (p : Rat) * (p : Rat) + (2 * (p : Rat) * (p : Rat)) * ((1 : Rat) * (p : Rat)⁻¹) +
            (2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) +
            (-((2 * (p : Rat) * (p : Rat)) * ((1 : Rat) * (p : Rat)⁻¹)) -
              (2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹)) * m +
            ((2 * (p : Rat) * (p : Rat)) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) *
              (m * m) := by rw [h2, h3, h4]
      _ = (2 * (p : Rat) * (p : Rat)) *
            (1 + 1 * (p : Rat)⁻¹ + ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ +
              (-(1 * (p : Rat)⁻¹) - ((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹) * m +
              ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ * m * m) := by grind
  · -- Condition numbers: monomial vs vertex
    constructor
    · -- |c0| + |c1| + |c2| = 1 + 4/p + 2/p^2
      have hc0_nn : (0 : Rat) ≤ monoC0 p := by
        unfold monoC0
        have h1 : (0 : Rat) ≤ 1 / (p : Rat) := rat_div_nonneg (by decide) hpPos
        have h2 : (0 : Rat) ≤ ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) :=
          rat_div_nonneg (Rat.le_of_lt hp1Pos) h2ppPos
        have h12 : (0 : Rat) ≤ 1 + 1 / (p : Rat) :=
          Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by decide : (0 : Rat) < 1) h1)
        exact Rat.le_trans h12 (by have := Rat.add_le_add_left (c := 1 + 1 / (p : Rat)) |>.mpr h2; grind)
      have hc1_neg : monoC1 p < (0 : Rat) := by
        unfold monoC1
        have h1 : (0 : Rat) < 1 / (p : Rat) := rat_div_pos (by decide) hpPos
        have h2 : (0 : Rat) < ((p : Rat) + 1) / ((p : Rat) * (p : Rat)) := rat_div_pos hp1Pos hppPos
        have hsum : (0 : Rat) < 1 / (p : Rat) + ((p : Rat) + 1) / ((p : Rat) * (p : Rat)) :=
          rat_add_pos_of_pos_nonneg h1 (Rat.le_of_lt h2)
        have hlt := rat_sub_pos_of_lt hsum
        have heq : -(1 / (p : Rat)) - ((p : Rat) + 1) / ((p : Rat) * (p : Rat)) =
            -(1 / (p : Rat) + ((p : Rat) + 1) / ((p : Rat) * (p : Rat))) := by grind
        rw [heq]
        have hle : -(1 / (p : Rat) + ((p : Rat) + 1) / ((p : Rat) * (p : Rat))) ≤ 0 := by
          have := Rat.add_le_add_right (c := -(1 / (p : Rat) + ((p : Rat) + 1) / ((p : Rat) * (p : Rat)))) |>.mpr (Rat.le_of_lt hsum)
          grind
        have hne : -(1 / (p : Rat) + ((p : Rat) + 1) / ((p : Rat) * (p : Rat))) ≠ 0 := by
          intro h0
          have : 1 / (p : Rat) + ((p : Rat) + 1) / ((p : Rat) * (p : Rat)) = 0 := by grind
          exact Rat.ne_of_gt hsum this
        exact Rat.lt_of_le_of_ne hle hne
      have hc2_nn : (0 : Rat) ≤ monoC2 p := by
        unfold monoC2
        exact rat_div_nonneg (Rat.le_of_lt hp1Pos) h2ppPos
      rw [ratAbs_of_nonneg hc0_nn, ratAbs_of_neg hc1_neg, ratAbs_of_nonneg hc2_nn]
      unfold monoC0 monoC1 monoC2
      apply rat_mul_cancel_left hppNe
      have hip : (p : Rat) * (p : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hpNe
      have hipp : ((p : Rat) * (p : Rat)) * ((p : Rat) * (p : Rat))⁻¹ = 1 := Rat.mul_inv_cancel _ hppNe
      have hi2pp : (2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹ = 1 :=
        Rat.mul_inv_cancel _ h2ppNe
      simp only [Rat.div_def]
      have h1 : ((p : Rat) * (p : Rat)) * ((1 : Rat) * (p : Rat)⁻¹) = (p : Rat) := by
        calc ((p : Rat) * (p : Rat)) * ((1 : Rat) * (p : Rat)⁻¹)
            = (p : Rat) * ((p : Rat) * (p : Rat)⁻¹) := by grind
          _ = (p : Rat) := by rw [hip]; grind
      have h2 : ((p : Rat) * (p : Rat)) * (((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹) = (p : Rat) + 1 := by
        calc ((p : Rat) * (p : Rat)) * (((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹)
            = ((p : Rat) + 1) * (((p : Rat) * (p : Rat)) * ((p : Rat) * (p : Rat))⁻¹) := by grind
          _ = (p : Rat) + 1 := by rw [hipp]; grind
      have h3 : ((p : Rat) * (p : Rat)) * (2 * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) =
          (p : Rat) + 1 := by
        calc ((p : Rat) * (p : Rat)) * (2 * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹))
            = ((p : Rat) + 1) * ((2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹) := by grind
          _ = (p : Rat) + 1 := by rw [hi2pp]; grind
      have h4 : ((p : Rat) * (p : Rat)) * ((4 : Rat) * (p : Rat)⁻¹) = 4 * (p : Rat) := by
        calc ((p : Rat) * (p : Rat)) * ((4 : Rat) * (p : Rat)⁻¹)
            = 4 * (p : Rat) * ((p : Rat) * (p : Rat)⁻¹) := by grind
          _ = 4 * (p : Rat) := by rw [hip]; grind
      have h5 : ((p : Rat) * (p : Rat)) * ((2 : Rat) * ((p : Rat) * (p : Rat))⁻¹) = 2 := by
        calc ((p : Rat) * (p : Rat)) * ((2 : Rat) * ((p : Rat) * (p : Rat))⁻¹)
            = 2 * (((p : Rat) * (p : Rat)) * ((p : Rat) * (p : Rat))⁻¹) := by grind
          _ = 2 := by rw [hipp]; grind
      calc
        ((p : Rat) * (p : Rat)) *
            (1 + 1 * (p : Rat)⁻¹ + ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹ +
              -(-(1 * (p : Rat)⁻¹) - ((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹) +
              ((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)
            = (p : Rat) * (p : Rat) +
              2 * (((p : Rat) * (p : Rat)) * ((1 : Rat) * (p : Rat)⁻¹)) +
              ((p : Rat) * (p : Rat)) * (((p : Rat) + 1) * ((p : Rat) * (p : Rat))⁻¹) +
              ((p : Rat) * (p : Rat)) * (2 * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) := by grind
        _ = (p : Rat) * (p : Rat) + 2 * (p : Rat) + ((p : Rat) + 1) + ((p : Rat) + 1) := by rw [h1, h2, h3]
        _ = (p : Rat) * (p : Rat) + 4 * (p : Rat) + 2 := by grind
        _ = (p : Rat) * (p : Rat) +
              ((p : Rat) * (p : Rat)) * ((4 : Rat) * (p : Rat)⁻¹) +
              ((p : Rat) * (p : Rat)) * ((2 : Rat) * ((p : Rat) * (p : Rat))⁻¹) := by rw [h4, h5]
        _ = ((p : Rat) * (p : Rat)) *
              (1 + 4 * (p : Rat)⁻¹ + 2 * ((p : Rat) * (p : Rat))⁻¹) := by grind
    · -- Vertex sum condition number = 1 (both terms nonnegative, sum = vertexInvRoot p 1 = 1)
      have ht1_nn : (0 : Rat) ≤ (2 * (p : Rat) + 1) / (2 * (p : Rat) + 2) :=
        rat_div_nonneg (Rat.le_of_lt (rat_add_pos_of_pos_nonneg
          (rat_mul_pos (by decide : (0 : Rat) < 2) hpPos) (by decide : (0 : Rat) ≤ 1))) h2p2Pos
      have ht2_nn : (0 : Rat) ≤ ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) *
          (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
          (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) := by
        have hβ : (0 : Rat) ≤ ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) :=
          rat_div_nonneg (Rat.le_of_lt hp1Pos) h2ppPos
        have hsq : (0 : Rat) ≤ (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
            (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) := rat_sq_nonneg _
        have hmul := Rat.mul_nonneg hβ hsq
        have heq : ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat)) *
            (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
            (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) =
            (((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat))) *
            ((1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1)) *
             (1 - (2 * (p : Rat) + 1) / ((p : Rat) + 1))) := by grind
        rw [heq]; exact hmul
      rw [ratAbs_of_nonneg ht1_nn, ratAbs_of_nonneg ht2_nn]
      have h1 : vertexInvRoot p 1 = taylor2InvRoot p 1 :=
        (taylor2InvRoot_eq_vertexInvRoot p hp 1).symm
      have h2 : taylor2InvRoot p 1 = 1 := by
        unfold taylor2InvRoot
        have h0 : ((1 : Rat) - 1) / (p : Rat) = 0 := by rw [Rat.div_def]; grind
        rw [h0]; grind
      unfold vertexInvRoot at h1
      rw [h1, h2]

/-! ## Theorem 2: Universal All-`p` Cubic Convergence -/

private theorem polyPowRem_spec (a b x : Rat) :
    ∀ k : Nat,
      ratPow (1 + a * x + b * x * x) k =
        1 + (k : Rat) * a * x +
          ((k : Rat) * b + ((k : Rat) * ((k : Rat) - 1) / 2) * (a * a)) * (x * x) +
          (x * x * x) * polyPowRem a b x k
  | 0 => by
    unfold ratPow polyPowRem
    grind
  | k + 1 => by
    have ih := polyPowRem_spec a b x k
    unfold ratPow polyPowRem
    rw [ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      have h1 : ((1 : Nat) : Rat) = (1 : Rat) := rfl
      rw [Rat.natCast_add, h1]
    rw [hcast]
    grind

private theorem polyPowRem_zero (a b : Rat) :
    ∀ k : Nat,
      polyPowRem a b 0 k =
        (k : Rat) * ((k : Rat) - 1) * a * b +
          (k : Rat) * ((k : Rat) - 1) * ((k : Rat) - 2) / 6 * (a * a * a)
  | 0 => by
    unfold polyPowRem
    grind
  | k + 1 => by
    have ih := polyPowRem_zero a b k
    unfold polyPowRem
    rw [ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      have h1 : ((1 : Nat) : Rat) = (1 : Rat) := rfl
      rw [Rat.natCast_add, h1]
    rw [hcast]
    grind

theorem universal_invroot_cubic_convergence (p : Nat) (hp : 1 ≤ p) (m : Rat) :
    (m * ratPow (vertexInvRoot p m) p - 1 =
      (m - 1) * (m - 1) * (m - 1) * invRootCubicQuot p (m - 1)) ∧
    (invRootCubicQuot p 0 =
      ((p : Rat) + 1) * (2 * (p : Rat) + 1) / (6 * (p : Rat) * (p : Rat))) := by
  have hpPos : (0 : Rat) < (p : Rat) := rat_natCast_pos hp
  have hpNe : (p : Rat) ≠ 0 := Rat.ne_of_gt hpPos
  have h2ppNe : 2 * (p : Rat) * (p : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 2) hpPos) hpPos)
  have h6ppNe : 6 * (p : Rat) * (p : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 6) hpPos) hpPos)
  have hip : (p : Rat) * (p : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hpNe
  have hi2pp : (2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹ = 1 :=
    Rat.mul_inv_cancel _ h2ppNe
  have hi6pp : (6 * (p : Rat) * (p : Rat)) * (6 * (p : Rat) * (p : Rat))⁻¹ = 1 :=
    Rat.mul_inv_cancel _ h6ppNe
  let a : Rat := -1 / (p : Rat)
  let b : Rat := ((p : Rat) + 1) / (2 * (p : Rat) * (p : Rat))
  constructor
  · rw [← taylor2InvRoot_eq_vertexInvRoot p hp m]
    let x := m - 1
    have htaylor : taylor2InvRoot p m = 1 + a * x + b * x * x := by
      unfold taylor2InvRoot
      dsimp [a, b, x]
      simp only [Rat.div_def]
      grind
    rw [htaylor]
    have hpow := polyPowRem_spec a b x p
    have hAp : (p : Rat) * a = -1 := by
      dsimp [a]; rw [Rat.div_def]
      calc (p : Rat) * ((-1 : Rat) * (p : Rat)⁻¹) = -((p : Rat) * (p : Rat)⁻¹) := by grind
        _ = -1 := by rw [hip]
    have hBp : (p : Rat) * b + ((p : Rat) * ((p : Rat) - 1) / 2) * (a * a) = 1 := by
      apply rat_mul_cancel_left h2ppNe
      dsimp [a, b]; simp only [Rat.div_def]
      have h1 : (2 * (p : Rat) * (p : Rat)) * ((p : Rat) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) =
          (p : Rat) * ((p : Rat) + 1) := by
        calc (2 * (p : Rat) * (p : Rat)) * ((p : Rat) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹))
            = (p : Rat) * ((p : Rat) + 1) * ((2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹) := by grind
          _ = (p : Rat) * ((p : Rat) + 1) := by rw [hi2pp]; grind
      have h2 : (2 * (p : Rat) * (p : Rat)) *
          ((p : Rat) * ((p : Rat) - 1) * (2 : Rat)⁻¹ * ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹))) =
          (p : Rat) * ((p : Rat) - 1) := by
        have hi2 : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (by decide : (2 : Rat) ≠ 0)
        calc (2 * (p : Rat) * (p : Rat)) *
              ((p : Rat) * ((p : Rat) - 1) * (2 : Rat)⁻¹ * ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹)))
            = (p : Rat) * ((p : Rat) - 1) * ((2 : Rat) * (2 : Rat)⁻¹) *
                (((p : Rat) * (p : Rat)⁻¹) * ((p : Rat) * (p : Rat)⁻¹)) := by grind
          _ = (p : Rat) * ((p : Rat) - 1) * 1 * (1 * 1) := by rw [hi2, hip]
          _ = (p : Rat) * ((p : Rat) - 1) := by grind
      calc
        (2 * (p : Rat) * (p : Rat)) *
            ((p : Rat) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹) +
              (p : Rat) * ((p : Rat) - 1) * (2 : Rat)⁻¹ * ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹)))
            = (2 * (p : Rat) * (p : Rat)) * ((p : Rat) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) +
              (2 * (p : Rat) * (p : Rat)) *
                ((p : Rat) * ((p : Rat) - 1) * (2 : Rat)⁻¹ * ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹))) := by grind
        _ = (p : Rat) * ((p : Rat) + 1) + (p : Rat) * ((p : Rat) - 1) := by rw [h1, h2]
        _ = (2 * (p : Rat) * (p : Rat)) * 1 := by grind
    rw [hAp, hBp] at hpow
    rw [hpow]
    unfold invRootCubicQuot
    dsimp [a, b, x]
    grind
  · -- Exact leading constant at x = 0: (p + 1) * (2p + 1) / (6 * p^2)
    unfold invRootCubicQuot
    rw [polyPowRem_zero]
    apply rat_mul_cancel_left h6ppNe
    simp only [Rat.div_def]
    have hi6 : (6 : Rat) * (6 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (by decide : (6 : Rat) ≠ 0)
    have h1 : (6 * (p : Rat) * (p : Rat)) *
        ((p : Rat) * ((p : Rat) - 1) * (-1 * (p : Rat)⁻¹) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) =
        -3 * (((p : Rat) - 1) * ((p : Rat) + 1)) := by
      calc (6 * (p : Rat) * (p : Rat)) *
            ((p : Rat) * ((p : Rat) - 1) * (-1 * (p : Rat)⁻¹) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹))
          = -3 * (((p : Rat) - 1) * ((p : Rat) + 1)) *
              (((p : Rat) * (p : Rat)⁻¹) * ((2 * (p : Rat) * (p : Rat)) * (2 * (p : Rat) * (p : Rat))⁻¹)) := by grind
        _ = -3 * (((p : Rat) - 1) * ((p : Rat) + 1)) * (1 * 1) := by rw [hip, hi2pp]
        _ = -3 * (((p : Rat) - 1) * ((p : Rat) + 1)) := by grind
    have h2 : (6 * (p : Rat) * (p : Rat)) *
        ((p : Rat) * ((p : Rat) - 1) * ((p : Rat) - 2) * (6 : Rat)⁻¹ *
          ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹))) =
        -(((p : Rat) - 1) * ((p : Rat) - 2)) := by
      calc (6 * (p : Rat) * (p : Rat)) *
            ((p : Rat) * ((p : Rat) - 1) * ((p : Rat) - 2) * (6 : Rat)⁻¹ *
              ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹)))
          = -(((p : Rat) - 1) * ((p : Rat) - 2)) *
              ((6 : Rat) * (6 : Rat)⁻¹) *
              (((p : Rat) * (p : Rat)⁻¹) * ((p : Rat) * (p : Rat)⁻¹) * ((p : Rat) * (p : Rat)⁻¹)) := by grind
        _ = -(((p : Rat) - 1) * ((p : Rat) - 2)) * 1 * (1 * 1 * 1) := by rw [hi6, hip]
        _ = -(((p : Rat) - 1) * ((p : Rat) - 2)) := by grind
    have h3 : (6 * (p : Rat) * (p : Rat)) *
        (((p : Rat) + 1) * (2 * (p : Rat) + 1) * (6 * (p : Rat) * (p : Rat))⁻¹) =
        ((p : Rat) + 1) * (2 * (p : Rat) + 1) := by
      calc (6 * (p : Rat) * (p : Rat)) *
            (((p : Rat) + 1) * (2 * (p : Rat) + 1) * (6 * (p : Rat) * (p : Rat))⁻¹)
          = ((p : Rat) + 1) * (2 * (p : Rat) + 1) *
              ((6 * (p : Rat) * (p : Rat)) * (6 * (p : Rat) * (p : Rat))⁻¹) := by grind
        _ = ((p : Rat) + 1) * (2 * (p : Rat) + 1) := by rw [hi6pp]; grind
    calc
      (6 * (p : Rat) * (p : Rat)) *
          (1 + (1 + 0) *
            ((p : Rat) * ((p : Rat) - 1) * (-1 * (p : Rat)⁻¹) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹) +
              (p : Rat) * ((p : Rat) - 1) * ((p : Rat) - 2) * (6 : Rat)⁻¹ *
                ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹))))
          = 6 * (p : Rat) * (p : Rat) +
            (6 * (p : Rat) * (p : Rat)) *
              ((p : Rat) * ((p : Rat) - 1) * (-1 * (p : Rat)⁻¹) * (((p : Rat) + 1) * (2 * (p : Rat) * (p : Rat))⁻¹)) +
            (6 * (p : Rat) * (p : Rat)) *
              ((p : Rat) * ((p : Rat) - 1) * ((p : Rat) - 2) * (6 : Rat)⁻¹ *
                ((-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹) * (-1 * (p : Rat)⁻¹))) := by grind
      _ = 6 * (p : Rat) * (p : Rat) + -3 * (((p : Rat) - 1) * ((p : Rat) + 1)) +
            -(((p : Rat) - 1) * ((p : Rat) - 2)) := by rw [h1, h2]
      _ = ((p : Rat) + 1) * (2 * (p : Rat) + 1) := by grind
      _ = (6 * (p : Rat) * (p : Rat)) *
            (((p : Rat) + 1) * (2 * (p : Rat) + 1) * (6 * (p : Rat) * (p : Rat))⁻¹) := h3.symm

/-! ## Theorem 3: Degree-9 Shared-Square Identity & Rounding-Floor Dominance -/

private theorem deg9_ratio_gt_165 (u : Rat) (hu : (0 : Rat) < u) :
    (165 / 100 : Rat) * (ratPow (1 + u) 6 - 1) < ratPow (1 + u) 10 - 1 := by
  have huNN : (0 : Rat) ≤ u := Rat.le_of_lt hu
  have hdiff : ratPow (1 + u) 10 - 1 - (165 / 100 : Rat) * (ratPow (1 + u) 6 - 1) =
      u * ((1 / 10 : Rat) + u * ((81 / 4 : Rat) + u * ((87 : Rat) +
        u * ((741 / 4 : Rat) + u * ((2421 / 10 : Rat) + u * ((4167 / 20 : Rat) +
          u * ((120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u))))))))) := by
    simp only [ratPow]
    grind
  have hpos : (0 : Rat) < ratPow (1 + u) 10 - 1 - (165 / 100 : Rat) * (ratPow (1 + u) 6 - 1) := by
    rw [hdiff]
    have h9 : (0 : Rat) ≤ (10 : Rat) + u := Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) huNN)
    have h8 : (0 : Rat) ≤ (45 : Rat) + u * ((10 : Rat) + u) :=
      Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h9))
    have h7 : (0 : Rat) ≤ (120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u)) :=
      Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h8))
    have h6 : (0 : Rat) ≤ (4167 / 20 : Rat) + u * ((120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u))) :=
      Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h7))
    have h5 : (0 : Rat) ≤ (2421 / 10 : Rat) + u * ((4167 / 20 : Rat) + u * ((120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u)))) :=
      Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h6))
    have h4 : (0 : Rat) ≤ (741 / 4 : Rat) + u * ((2421 / 10 : Rat) + u * ((4167 / 20 : Rat) + u * ((120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u))))) :=
      Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h5))
    have h3 : (0 : Rat) ≤ (87 : Rat) + u * ((741 / 4 : Rat) + u * ((2421 / 10 : Rat) + u * ((4167 / 20 : Rat) + u * ((120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u)))))) :=
      Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h4))
    have h2 : (0 : Rat) ≤ (81 / 4 : Rat) + u * ((87 : Rat) + u * ((741 / 4 : Rat) + u * ((2421 / 10 : Rat) + u * ((4167 / 20 : Rat) + u * ((120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u))))))) :=
      Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h3))
    have h1 : (0 : Rat) < (1 / 10 : Rat) + u * ((81 / 4 : Rat) + u * ((87 : Rat) + u * ((741 / 4 : Rat) + u * ((2421 / 10 : Rat) + u * ((4167 / 20 : Rat) + u * ((120 : Rat) + u * ((45 : Rat) + u * ((10 : Rat) + u)))))))) :=
      rat_add_pos_of_pos_nonneg (by grind) (Rat.mul_nonneg huNN h2)
    exact rat_mul_pos hu h1
  have hle : (165 / 100 : Rat) * (ratPow (1 + u) 6 - 1) ≤ ratPow (1 + u) 10 - 1 :=
    rat_le_of_sub_nonneg (Rat.le_of_lt hpos)
  have hne : (165 / 100 : Rat) * (ratPow (1 + u) 6 - 1) ≠ ratPow (1 + u) 10 - 1 := by
    intro heq
    have : ratPow (1 + u) 10 - 1 - (165 / 100 : Rat) * (ratPow (1 + u) 6 - 1) = 0 := by grind
    exact Rat.ne_of_gt hpos this
  exact Rat.lt_of_le_of_ne hle hne

theorem deg9_shared_square_and_rounding_floor_dominance
    (a c d μ1 μ2 u : Rat) (hu : (0 : Rat) < u) :
    (c + d * (a - μ2) * (a - μ2) =
      (c + d * (μ1 - μ2) * (μ1 - μ2)) +
        d * ((a - μ1) * (a - μ1)) +
        2 * d * (μ1 - μ2) * (a - μ1)) ∧
    ((5 : Nat) ^ 4 < (9 : Nat) ^ 3) ∧
    (ratPow (1 + u) 6 < ratPow (1 + u) 10) ∧
    ((165 / 100 : Rat) * (ratPow (1 + uBF16) 6 - 1) < ratPow (1 + uBF16) 10 - 1 ∧
     (165 / 100 : Rat) * (ratPow (1 + uFP8Hybrid) 6 - 1) < ratPow (1 + uFP8Hybrid) 10 - 1 ∧
     (165 / 100 : Rat) * (ratPow (1 + uFP8Pure) 6 - 1) < ratPow (1 + uFP8Pure) 10 - 1) := by
  refine ⟨by grind, by decide, ?_, ?_, ?_, ?_⟩
  · -- (1 + u)^6 < (1 + u)^10 for every 0 < u
    have h1u_gt1 : (1 : Rat) < 1 + u := by
      have h := Rat.add_lt_add_left (c := (1 : Rat)) |>.mpr hu
      grind
    have h1u_pos : (0 : Rat) < 1 + u := rat_lt_of_lt_of_le (by decide : (0 : Rat) < 1) (Rat.le_of_lt h1u_gt1)
    have hp6_pos : (0 : Rat) < ratPow (1 + u) 6 := ratPow_pos h1u_pos 6
    have hp2_gt1 : (1 : Rat) < (1 + u) * (1 + u) := by
      have h1 := rat_mul_lt_mul_of_pos_left h1u_gt1 h1u_pos
      have h2 : (1 + u) * 1 = 1 + u := by grind
      rw [h2] at h1
      exact rat_lt_of_lt_of_le h1u_gt1 (Rat.le_of_lt h1)
    have hp4_gt1 : (1 : Rat) < ((1 + u) * (1 + u)) * ((1 + u) * (1 + u)) := by
      have h2pos : (0 : Rat) < (1 + u) * (1 + u) := rat_mul_pos h1u_pos h1u_pos
      have h1 := rat_mul_lt_mul_of_pos_left hp2_gt1 h2pos
      have h2 : ((1 + u) * (1 + u)) * 1 = (1 + u) * (1 + u) := by grind
      rw [h2] at h1
      exact rat_lt_of_lt_of_le hp2_gt1 (Rat.le_of_lt h1)
    have hmul := rat_mul_lt_mul_of_pos_left hp4_gt1 hp6_pos
    have h10 : ratPow (1 + u) 10 = ratPow (1 + u) 6 * (((1 + u) * (1 + u)) * ((1 + u) * (1 + u))) := by
      simp only [ratPow]
      grind
    rw [h10]
    have h6_1 : ratPow (1 + u) 6 * 1 = ratPow (1 + u) 6 := by grind
    rw [h6_1] at hmul
    exact hmul
  · exact deg9_ratio_gt_165 uBF16 (by unfold uBF16; grind)
  · exact deg9_ratio_gt_165 uFP8Hybrid (by unfold uFP8Hybrid; grind)
  · exact deg9_ratio_gt_165 uFP8Pure (by unfold uFP8Pure; grind)

/-! ## Pointwise Exact Adversarial Envelopes for `p ∈ {2, 3, 8}` -/

private theorem factor_bounds {u δ : Rat} (hu1 : u < 1) (hlo : -u ≤ δ) (hhi : δ ≤ u) :
    (0 : Rat) < 1 - u ∧ 1 - u ≤ 1 + δ ∧ 1 + δ ≤ 1 + u := by
  have hpos : (0 : Rat) < 1 - u := rat_sub_pos_of_lt hu1
  have h1 : 1 - u ≤ 1 + δ := by
    have := Rat.add_le_add_left (c := (1 : Rat)) |>.mpr hlo
    grind
  have h2 : 1 + δ ≤ 1 + u := Rat.add_le_add_left (c := (1 : Rat)) |>.mpr hhi
  exact ⟨hpos, h1, h2⟩

private theorem inner_vertex_bounds {α β μ u m δ1 δ2 δ3 : Rat}
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) ≤ β)
    (hu1 : u < 1)
    (h1l : -u ≤ δ1) (h1r : δ1 ≤ u)
    (h2l : -u ≤ δ2) (h2r : δ2 ≤ u)
    (h3l : -u ≤ δ3) (h3r : δ3 ≤ u) :
    let d  := (m - μ) * (1 + δ1)
    let d2 := d * d * (1 + δ2)
    let t  := β * d2 * (1 + δ3)
    let q  := α + t
    (0 : Rat) < qLoVertex α β μ u m ∧ qLoVertex α β μ u m ≤ q ∧ q ≤ qHiVertex α β μ u m := by
  have ⟨hloPos, h1lo, h1hi⟩ := factor_bounds hu1 h1l h1r
  have ⟨_, h2lo, h2hi⟩ := factor_bounds hu1 h2l h2r
  have ⟨_, h3lo, h3hi⟩ := factor_bounds hu1 h3l h3r
  have hloNN : (0 : Rat) ≤ 1 - u := Rat.le_of_lt hloPos
  have h1sq_lo : (1 - u) * (1 - u) ≤ (1 + δ1) * (1 + δ1) := rat_sq_le_sq_of_nonneg hloNN h1lo
  have h1sq_hi : (1 + δ1) * (1 + δ1) ≤ (1 + u) * (1 + u) :=
    rat_sq_le_sq_of_nonneg (Rat.le_trans hloNN h1lo) h1hi
  have h23_lo : (1 - u) * (1 - u) ≤ (1 + δ2) * (1 + δ3) :=
    rat_mul_le_mul h2lo h3lo hloNN hloNN
  have h23_hi : (1 + δ2) * (1 + δ3) ≤ (1 + u) * (1 + u) :=
    rat_mul_le_mul h2hi h3hi (Rat.le_trans hloNN h2lo) (Rat.le_trans hloNN h3lo)
  have hf4_lo : ratPow (1 - u) 4 ≤ ((1 + δ1) * (1 + δ1)) * ((1 + δ2) * (1 + δ3)) := by
    have h4 : ratPow (1 - u) 4 = ((1 - u) * (1 - u)) * ((1 - u) * (1 - u)) := by simp only [ratPow]; grind
    rw [h4]
    exact rat_mul_le_mul h1sq_lo h23_lo (rat_sq_nonneg _) (rat_sq_nonneg _)
  have hf4_hi : ((1 + δ1) * (1 + δ1)) * ((1 + δ2) * (1 + δ3)) ≤ ratPow (1 + u) 4 := by
    have h4 : ratPow (1 + u) 4 = ((1 + u) * (1 + u)) * ((1 + u) * (1 + u)) := by simp only [ratPow]; grind
    rw [h4]
    exact rat_mul_le_mul h1sq_hi h23_hi (rat_sq_nonneg _)
      (Rat.mul_nonneg (Rat.le_trans hloNN h2lo) (Rat.le_trans hloNN h3lo))
  dsimp only
  let d  := (m - μ) * (1 + δ1)
  let d2 := d * d * (1 + δ2)
  let t  := β * d2 * (1 + δ3)
  let q  := α + t
  have ht_eq : t = (((1 + δ1) * (1 + δ1)) * ((1 + δ2) * (1 + δ3))) * (β * ((m - μ) * (m - μ))) := by
    dsimp [t, d2, d]; grind
  have hβsq_nn : (0 : Rat) ≤ β * ((m - μ) * (m - μ)) := Rat.mul_nonneg hβ (rat_sq_nonneg _)
  have ht_lo : ratPow (1 - u) 4 * β * ((m - μ) * (m - μ)) ≤ t := by
    rw [ht_eq]
    have h := rat_mul_le_mul_of_nonneg_right hf4_lo hβsq_nn
    have eq1 : ratPow (1 - u) 4 * β * ((m - μ) * (m - μ)) =
        ratPow (1 - u) 4 * (β * ((m - μ) * (m - μ))) := by grind
    rw [eq1]; exact h
  have ht_hi : t ≤ ratPow (1 + u) 4 * β * ((m - μ) * (m - μ)) := by
    rw [ht_eq]
    have h := rat_mul_le_mul_of_nonneg_right hf4_hi hβsq_nn
    have eq1 : ratPow (1 + u) 4 * β * ((m - μ) * (m - μ)) =
        ratPow (1 + u) 4 * (β * ((m - μ) * (m - μ))) := by grind
    rw [eq1]; exact h
  have hqLo_pos : (0 : Rat) < qLoVertex α β μ u m := by
    unfold qLoVertex
    exact rat_add_pos_of_pos_nonneg hα
      (Rat.mul_nonneg (Rat.mul_nonneg (ratPow_nonneg hloNN 4) hβ) (rat_sq_nonneg _))
  exact ⟨hqLo_pos,
    by unfold qLoVertex; exact Rat.add_le_add_left.mpr ht_lo,
    by unfold qHiVertex; exact Rat.add_le_add_left.mpr ht_hi⟩

private theorem step2_factor (m q a b c : Rat) :
    let p  := q * a
    let p2 := p * p * b
    m * p2 * c =
      ((a * a) * (b * c)) * (m * ratPow q 2) := by
  dsimp only
  simp only [ratPow]
  grind

/-- Pointwise exact envelope for the 6-rounding-point vertex `G^{-1/2}` step `NoisyVertexStep2`. -/
theorem noisyVertexStep2_envelope (α β μ u m y : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) ≤ β)
    (hu1 : u < 1) (hm : (0 : Rat) < m)
    (hstep : NoisyVertexStep2 α β μ u m y) :
    vertexLowerEnv 2 α β μ u m ≤ y ∧ y ≤ vertexUpperEnv 2 α β μ u m := by
  rcases hstep with ⟨δ1, δ2, δ3, δ4, δ5, δ6,
    ⟨h1l, h1r⟩, ⟨h2l, h2r⟩, ⟨h3l, h3r⟩, ⟨h4l, h4r⟩, ⟨h5l, h5r⟩, ⟨h6l, h6r⟩, hy⟩
  have ⟨hqLoPos, hq_lo, hq_hi⟩ := inner_vertex_bounds (μ := μ) (m := m) hα hβ hu1 h1l h1r h2l h2r h3l h3r
  have ⟨hloPos, h4lo, h4hi⟩ := factor_bounds hu1 h4l h4r
  have ⟨_, h5lo, h5hi⟩ := factor_bounds hu1 h5l h5r
  have ⟨_, h6lo, h6hi⟩ := factor_bounds hu1 h6l h6r
  have hloNN : (0 : Rat) ≤ 1 - u := Rat.le_of_lt hloPos
  have h4sq_lo : (1 - u) * (1 - u) ≤ (1 + δ4) * (1 + δ4) := rat_sq_le_sq_of_nonneg hloNN h4lo
  have h4sq_hi : (1 + δ4) * (1 + δ4) ≤ (1 + u) * (1 + u) :=
    rat_sq_le_sq_of_nonneg (Rat.le_trans hloNN h4lo) h4hi
  have h56_lo : (1 - u) * (1 - u) ≤ (1 + δ5) * (1 + δ6) := rat_mul_le_mul h5lo h6lo hloNN hloNN
  have h56_hi : (1 + δ5) * (1 + δ6) ≤ (1 + u) * (1 + u) :=
    rat_mul_le_mul h5hi h6hi (Rat.le_trans hloNN h5lo) (Rat.le_trans hloNN h6lo)
  have hf4_lo : ratPow (1 - u) 4 ≤ ((1 + δ4) * (1 + δ4)) * ((1 + δ5) * (1 + δ6)) := by
    have h4 : ratPow (1 - u) 4 = ((1 - u) * (1 - u)) * ((1 - u) * (1 - u)) := by simp only [ratPow]; grind
    rw [h4]; exact rat_mul_le_mul h4sq_lo h56_lo (rat_sq_nonneg _) (rat_sq_nonneg _)
  have hf4_hi : ((1 + δ4) * (1 + δ4)) * ((1 + δ5) * (1 + δ6)) ≤ ratPow (1 + u) 4 := by
    have h4 : ratPow (1 + u) 4 = ((1 + u) * (1 + u)) * ((1 + u) * (1 + u)) := by simp only [ratPow]; grind
    rw [h4]; exact rat_mul_le_mul h4sq_hi h56_hi (rat_sq_nonneg _)
      (Rat.mul_nonneg (Rat.le_trans hloNN h5lo) (Rat.le_trans hloNN h6lo))
  let q := α + β * (((m - μ) * (1 + δ1)) * ((m - μ) * (1 + δ1)) * (1 + δ2)) * (1 + δ3)
  have hy_eq : y = (((1 + δ4) * (1 + δ4)) * ((1 + δ5) * (1 + δ6))) * (m * ratPow q 2) := by
    rw [hy]
    exact step2_factor m q (1 + δ4) (1 + δ5) (1 + δ6)
  have hqLoNN : (0 : Rat) ≤ qLoVertex α β μ u m := Rat.le_of_lt hqLoPos
  have hqNN : (0 : Rat) ≤ q := Rat.le_trans hqLoNN hq_lo
  have hmNN : (0 : Rat) ≤ m := Rat.le_of_lt hm
  have hmq_lo : m * ratPow (qLoVertex α β μ u m) 2 ≤ m * ratPow q 2 :=
    rat_mul_le_mul_of_nonneg_left (ratPow_le_pow_of_nonneg hqLoNN hq_lo 2) hmNN
  have hmq_hi : m * ratPow q 2 ≤ m * ratPow (qHiVertex α β μ u m) 2 :=
    rat_mul_le_mul_of_nonneg_left (ratPow_le_pow_of_nonneg hqNN hq_hi 2) hmNN
  have hf4_nn : (0 : Rat) ≤ ratPow (1 - u) 4 := ratPow_nonneg hloNN 4
  constructor
  · rw [hy_eq]; unfold vertexLowerEnv
    have h := rat_mul_le_mul hf4_lo hmq_lo hf4_nn (Rat.mul_nonneg hmNN (ratPow_nonneg hqLoNN 2))
    rw [Rat.mul_assoc (ratPow (1 - u) 4)]; exact h
  · rw [hy_eq]; unfold vertexUpperEnv
    have h := rat_mul_le_mul hf4_hi hmq_hi (Rat.le_trans hf4_nn hf4_lo)
      (Rat.mul_nonneg hmNN (ratPow_nonneg hqNN 2))
    rw [Rat.mul_assoc (ratPow (1 + u) 4)]; exact h

private theorem step3_factor (m q a b c d : Rat) :
    let p  := q * a
    let p2 := p * p * b
    let p3 := p2 * p * c
    m * p3 * d =
      (ratPow a 3 * ((b * c) * d)) * (m * ratPow q 3) := by
  dsimp only
  simp only [ratPow]
  grind

/-- Pointwise exact envelope for the 7-rounding-point vertex `G^{-1/3}` step `NoisyVertexStep3`. -/
theorem noisyVertexStep3_envelope (α β μ u m y : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) ≤ β)
    (hu1 : u < 1) (hm : (0 : Rat) < m)
    (hstep : NoisyVertexStep3 α β μ u m y) :
    vertexLowerEnv 3 α β μ u m ≤ y ∧ y ≤ vertexUpperEnv 3 α β μ u m := by
  rcases hstep with ⟨δ1, δ2, δ3, δ4, δ5, δ6, δ7,
    ⟨h1l, h1r⟩, ⟨h2l, h2r⟩, ⟨h3l, h3r⟩, ⟨h4l, h4r⟩, ⟨h5l, h5r⟩, ⟨h6l, h6r⟩, ⟨h7l, h7r⟩, hy⟩
  have ⟨hqLoPos, hq_lo, hq_hi⟩ := inner_vertex_bounds (μ := μ) (m := m) hα hβ hu1 h1l h1r h2l h2r h3l h3r
  have ⟨hloPos, h4lo, h4hi⟩ := factor_bounds hu1 h4l h4r
  have ⟨_, h5lo, h5hi⟩ := factor_bounds hu1 h5l h5r
  have ⟨_, h6lo, h6hi⟩ := factor_bounds hu1 h6l h6r
  have ⟨_, h7lo, h7hi⟩ := factor_bounds hu1 h7l h7r
  have hloNN : (0 : Rat) ≤ 1 - u := Rat.le_of_lt hloPos
  have h4p3_lo : ratPow (1 - u) 3 ≤ ratPow (1 + δ4) 3 := ratPow_le_pow_of_nonneg hloNN h4lo 3
  have h4p3_hi : ratPow (1 + δ4) 3 ≤ ratPow (1 + u) 3 :=
    ratPow_le_pow_of_nonneg (Rat.le_trans hloNN h4lo) h4hi 3
  have h56_lo : (1 - u) * (1 - u) ≤ (1 + δ5) * (1 + δ6) := rat_mul_le_mul h5lo h6lo hloNN hloNN
  have h56_hi : (1 + δ5) * (1 + δ6) ≤ (1 + u) * (1 + u) :=
    rat_mul_le_mul h5hi h6hi (Rat.le_trans hloNN h5lo) (Rat.le_trans hloNN h6lo)
  have h567_lo : ratPow (1 - u) 3 ≤ ((1 + δ5) * (1 + δ6)) * (1 + δ7) := by
    have h3 : ratPow (1 - u) 3 = ((1 - u) * (1 - u)) * (1 - u) := by simp only [ratPow]; grind
    rw [h3]; exact rat_mul_le_mul h56_lo h7lo (rat_sq_nonneg _) hloNN
  have h567_hi : ((1 + δ5) * (1 + δ6)) * (1 + δ7) ≤ ratPow (1 + u) 3 := by
    have h3 : ratPow (1 + u) 3 = ((1 + u) * (1 + u)) * (1 + u) := by simp only [ratPow]; grind
    rw [h3]; exact rat_mul_le_mul h56_hi h7hi
      (Rat.mul_nonneg (Rat.le_trans hloNN h5lo) (Rat.le_trans hloNN h6lo))
      (Rat.le_trans hloNN h7lo)
  have hf6_lo : ratPow (1 - u) 6 ≤ ratPow (1 + δ4) 3 * (((1 + δ5) * (1 + δ6)) * (1 + δ7)) := by
    have h6 : ratPow (1 - u) 6 = ratPow (1 - u) 3 * ratPow (1 - u) 3 := by simp only [ratPow]; grind
    rw [h6]; exact rat_mul_le_mul h4p3_lo h567_lo (ratPow_nonneg hloNN 3) (ratPow_nonneg hloNN 3)
  have hf6_hi : ratPow (1 + δ4) 3 * (((1 + δ5) * (1 + δ6)) * (1 + δ7)) ≤ ratPow (1 + u) 6 := by
    have h6 : ratPow (1 + u) 6 = ratPow (1 + u) 3 * ratPow (1 + u) 3 := by simp only [ratPow]; grind
    rw [h6]; exact rat_mul_le_mul h4p3_hi h567_hi
      (ratPow_nonneg (Rat.le_trans hloNN h4lo) 3)
      (Rat.le_trans (ratPow_nonneg hloNN 3) h567_lo)
  let q := α + β * (((m - μ) * (1 + δ1)) * ((m - μ) * (1 + δ1)) * (1 + δ2)) * (1 + δ3)
  have hy_eq : y = (ratPow (1 + δ4) 3 * (((1 + δ5) * (1 + δ6)) * (1 + δ7))) * (m * ratPow q 3) := by
    rw [hy]
    exact step3_factor m q (1 + δ4) (1 + δ5) (1 + δ6) (1 + δ7)
  have hqLoNN : (0 : Rat) ≤ qLoVertex α β μ u m := Rat.le_of_lt hqLoPos
  have hqNN : (0 : Rat) ≤ q := Rat.le_trans hqLoNN hq_lo
  have hmNN : (0 : Rat) ≤ m := Rat.le_of_lt hm
  have hmq_lo : m * ratPow (qLoVertex α β μ u m) 3 ≤ m * ratPow q 3 :=
    rat_mul_le_mul_of_nonneg_left (ratPow_le_pow_of_nonneg hqLoNN hq_lo 3) hmNN
  have hmq_hi : m * ratPow q 3 ≤ m * ratPow (qHiVertex α β μ u m) 3 :=
    rat_mul_le_mul_of_nonneg_left (ratPow_le_pow_of_nonneg hqNN hq_hi 3) hmNN
  have hf6_nn : (0 : Rat) ≤ ratPow (1 - u) 6 := ratPow_nonneg hloNN 6
  constructor
  · rw [hy_eq]; unfold vertexLowerEnv
    have h := rat_mul_le_mul hf6_lo hmq_lo hf6_nn (Rat.mul_nonneg hmNN (ratPow_nonneg hqLoNN 3))
    rw [Rat.mul_assoc (ratPow (1 - u) 6)]; exact h
  · rw [hy_eq]; unfold vertexUpperEnv
    have h := rat_mul_le_mul hf6_hi hmq_hi (Rat.le_trans hf6_nn hf6_lo)
      (Rat.mul_nonneg hmNN (ratPow_nonneg hqNN 3))
    rw [Rat.mul_assoc (ratPow (1 + u) 6)]; exact h

private theorem step8_factor (m q a b c d e : Rat) :
    let p  := q * a
    let p2 := p * p * b
    let p4 := p2 * p2 * c
    let p8 := p4 * p4 * d
    m * p8 * e =
      (ratPow a 8 * (ratPow b 4 * (ratPow c 2 * (d * e)))) * (m * ratPow q 8) := by
  dsimp only
  simp only [ratPow]
  grind

/-- Pointwise exact envelope for the 8-rounding-point vertex `G^{-1/8}` step `NoisyVertexStep8`. -/
theorem noisyVertexStep8_envelope (α β μ u m y : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) ≤ β)
    (hu1 : u < 1) (hm : (0 : Rat) < m)
    (hstep : NoisyVertexStep8 α β μ u m y) :
    vertexLowerEnv 8 α β μ u m ≤ y ∧ y ≤ vertexUpperEnv 8 α β μ u m := by
  rcases hstep with ⟨δ1, δ2, δ3, δ4, δ5, δ6, δ7, δ8,
    ⟨h1l, h1r⟩, ⟨h2l, h2r⟩, ⟨h3l, h3r⟩, ⟨h4l, h4r⟩, ⟨h5l, h5r⟩, ⟨h6l, h6r⟩, ⟨h7l, h7r⟩, ⟨h8l, h8r⟩, hy⟩
  have ⟨hqLoPos, hq_lo, hq_hi⟩ := inner_vertex_bounds (μ := μ) (m := m) hα hβ hu1 h1l h1r h2l h2r h3l h3r
  have ⟨hloPos, h4lo, h4hi⟩ := factor_bounds hu1 h4l h4r
  have ⟨_, h5lo, h5hi⟩ := factor_bounds hu1 h5l h5r
  have ⟨_, h6lo, h6hi⟩ := factor_bounds hu1 h6l h6r
  have ⟨_, h7lo, h7hi⟩ := factor_bounds hu1 h7l h7r
  have ⟨_, h8lo, h8hi⟩ := factor_bounds hu1 h8l h8r
  have hloNN : (0 : Rat) ≤ 1 - u := Rat.le_of_lt hloPos
  have h4p8_lo : ratPow (1 - u) 8 ≤ ratPow (1 + δ4) 8 := ratPow_le_pow_of_nonneg hloNN h4lo 8
  have h4p8_hi : ratPow (1 + δ4) 8 ≤ ratPow (1 + u) 8 :=
    ratPow_le_pow_of_nonneg (Rat.le_trans hloNN h4lo) h4hi 8
  have h5p4_lo : ratPow (1 - u) 4 ≤ ratPow (1 + δ5) 4 := ratPow_le_pow_of_nonneg hloNN h5lo 4
  have h5p4_hi : ratPow (1 + δ5) 4 ≤ ratPow (1 + u) 4 :=
    ratPow_le_pow_of_nonneg (Rat.le_trans hloNN h5lo) h5hi 4
  have h6p2_lo : ratPow (1 - u) 2 ≤ ratPow (1 + δ6) 2 := ratPow_le_pow_of_nonneg hloNN h6lo 2
  have h6p2_hi : ratPow (1 + δ6) 2 ≤ ratPow (1 + u) 2 :=
    ratPow_le_pow_of_nonneg (Rat.le_trans hloNN h6lo) h6hi 2
  have h78_lo : ratPow (1 - u) 2 ≤ (1 + δ7) * (1 + δ8) := by
    have h2 : ratPow (1 - u) 2 = (1 - u) * (1 - u) := by simp only [ratPow]; grind
    rw [h2]; exact rat_mul_le_mul h7lo h8lo hloNN hloNN
  have h78_hi : (1 + δ7) * (1 + δ8) ≤ ratPow (1 + u) 2 := by
    have h2 : ratPow (1 + u) 2 = (1 + u) * (1 + u) := by simp only [ratPow]; grind
    rw [h2]; exact rat_mul_le_mul h7hi h8hi (Rat.le_trans hloNN h7lo) (Rat.le_trans hloNN h8lo)
  have h678_lo : ratPow (1 - u) 4 ≤ ratPow (1 + δ6) 2 * ((1 + δ7) * (1 + δ8)) := by
    have h4 : ratPow (1 - u) 4 = ratPow (1 - u) 2 * ratPow (1 - u) 2 := by simp only [ratPow]; grind
    rw [h4]; exact rat_mul_le_mul h6p2_lo h78_lo (ratPow_nonneg hloNN 2) (ratPow_nonneg hloNN 2)
  have h678_hi : ratPow (1 + δ6) 2 * ((1 + δ7) * (1 + δ8)) ≤ ratPow (1 + u) 4 := by
    have h4 : ratPow (1 + u) 4 = ratPow (1 + u) 2 * ratPow (1 + u) 2 := by simp only [ratPow]; grind
    rw [h4]; exact rat_mul_le_mul h6p2_hi h78_hi
      (ratPow_nonneg (Rat.le_trans hloNN h6lo) 2) (Rat.le_trans (ratPow_nonneg hloNN 2) h78_lo)
  have h5678_lo : ratPow (1 - u) 8 ≤ ratPow (1 + δ5) 4 * (ratPow (1 + δ6) 2 * ((1 + δ7) * (1 + δ8))) := by
    have h8 : ratPow (1 - u) 8 = ratPow (1 - u) 4 * ratPow (1 - u) 4 := by simp only [ratPow]; grind
    rw [h8]; exact rat_mul_le_mul h5p4_lo h678_lo (ratPow_nonneg hloNN 4) (ratPow_nonneg hloNN 4)
  have h5678_hi : ratPow (1 + δ5) 4 * (ratPow (1 + δ6) 2 * ((1 + δ7) * (1 + δ8))) ≤ ratPow (1 + u) 8 := by
    have h8 : ratPow (1 + u) 8 = ratPow (1 + u) 4 * ratPow (1 + u) 4 := by simp only [ratPow]; grind
    rw [h8]; exact rat_mul_le_mul h5p4_hi h678_hi
      (ratPow_nonneg (Rat.le_trans hloNN h5lo) 4) (Rat.le_trans (ratPow_nonneg hloNN 4) h678_lo)
  let f16 := ratPow (1 + δ4) 8 * (ratPow (1 + δ5) 4 * (ratPow (1 + δ6) 2 * ((1 + δ7) * (1 + δ8))))
  have hf16_lo : ratPow (1 - u) 16 ≤ f16 := by
    have h16 : ratPow (1 - u) 16 = ratPow (1 - u) 8 * ratPow (1 - u) 8 := by simp only [ratPow]; grind
    rw [h16]; exact rat_mul_le_mul h4p8_lo h5678_lo (ratPow_nonneg hloNN 8) (ratPow_nonneg hloNN 8)
  have hf16_hi : f16 ≤ ratPow (1 + u) 16 := by
    have h16 : ratPow (1 + u) 16 = ratPow (1 + u) 8 * ratPow (1 + u) 8 := by simp only [ratPow]; grind
    rw [h16]; exact rat_mul_le_mul h4p8_hi h5678_hi
      (ratPow_nonneg (Rat.le_trans hloNN h4lo) 8) (Rat.le_trans (ratPow_nonneg hloNN 8) h5678_lo)
  let q := α + β * (((m - μ) * (1 + δ1)) * ((m - μ) * (1 + δ1)) * (1 + δ2)) * (1 + δ3)
  have hy_eq : y = f16 * (m * ratPow q 8) := by
    rw [hy]
    exact step8_factor m q (1 + δ4) (1 + δ5) (1 + δ6) (1 + δ7) (1 + δ8)
  have hqLoNN : (0 : Rat) ≤ qLoVertex α β μ u m := Rat.le_of_lt hqLoPos
  have hqNN : (0 : Rat) ≤ q := Rat.le_trans hqLoNN hq_lo
  have hmNN : (0 : Rat) ≤ m := Rat.le_of_lt hm
  have hmq_lo : m * ratPow (qLoVertex α β μ u m) 8 ≤ m * ratPow q 8 :=
    rat_mul_le_mul_of_nonneg_left (ratPow_le_pow_of_nonneg hqLoNN hq_lo 8) hmNN
  have hmq_hi : m * ratPow q 8 ≤ m * ratPow (qHiVertex α β μ u m) 8 :=
    rat_mul_le_mul_of_nonneg_left (ratPow_le_pow_of_nonneg hqNN hq_hi 8) hmNN
  have hf16_nn : (0 : Rat) ≤ ratPow (1 - u) 16 := ratPow_nonneg hloNN 16
  constructor
  · rw [hy_eq]; unfold vertexLowerEnv
    have h := rat_mul_le_mul hf16_lo hmq_lo hf16_nn (Rat.mul_nonneg hmNN (ratPow_nonneg hqLoNN 8))
    rw [Rat.mul_assoc (ratPow (1 - u) 16)]; exact h
  · rw [hy_eq]; unfold vertexUpperEnv
    have h := rat_mul_le_mul hf16_hi hmq_hi (Rat.le_trans hf16_nn hf16_lo)
      (Rat.mul_nonneg hmNN (ratPow_nonneg hqNN 8))
    rw [Rat.mul_assoc (ratPow (1 + u) 16)]; exact h

end UniversalVertexInvroot
