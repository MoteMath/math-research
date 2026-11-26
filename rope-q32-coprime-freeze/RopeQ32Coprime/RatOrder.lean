/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RopeQ32Coprime.Defs

/-!
# Pure-`Init` `Rat` Order, Absolute Value, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace RopeQ32Coprime

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := Rat.add_le_add_right (c := -b) |>.mpr h
  grind

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := Rat.add_le_add_right (c := b) |>.mpr h
  grind

theorem rat_sub_pos {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by
  have h1 : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt h)
  have hne : a - b ≠ 0 := by
    intro h0
    have heq : a = b := by grind
    exact Rat.ne_of_gt h heq
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_lt_of_sub_pos {a b : Rat} (h : (0 : Rat) < a - b) : b < a := by
  have h1 : b ≤ a := rat_le_of_sub_nonneg (Rat.le_of_lt h)
  have hne : b ≠ a := by
    intro h0
    have : a - b = 0 := by grind
    exact Rat.ne_of_gt h this
  exact Rat.lt_of_le_of_ne h1 hne

theorem rat_neg_nonneg_of_nonpos {a : Rat} (h : a ≤ 0) : (0 : Rat) ≤ -a := by
  have := rat_sub_nonneg h
  grind

theorem rat_neg_pos_of_neg {a : Rat} (h : a < 0) : (0 : Rat) < -a := by
  have := rat_sub_pos h
  grind

theorem rat_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a * b := by
  have h1 : (0 : Rat) ≤ a * b := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  have hne : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact Rat.ne_of_gt ha h
    | inr h => exact Rat.ne_of_gt hb h
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    c * a ≤ c * b := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ b - a := rat_sub_nonneg h
  have h2 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]; exact h2

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  apply rat_lt_of_sub_pos
  have h1 : (0 : Rat) < b - a := rat_sub_pos h
  have h2 : (0 : Rat) < c * (b - a) := rat_mul_pos hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]; exact h2

theorem rat_mul_lt_mul_of_pos_right {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    a * c < b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_lt_mul_of_pos_left h hc

theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  have h3 : a + c ≤ b + c := (Rat.add_le_add_right (c := c)).mpr h1
  have h4 : b + c ≤ b + d := by
    rw [Rat.add_comm b c, Rat.add_comm b d]
    exact (Rat.add_le_add_right (c := b)).mpr h2
  exact Rat.le_trans h3 h4

theorem rat_add_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) ≤ a + b := by
  have h := rat_add_le_add ha hb
  have h0 : (0 : Rat) + 0 = 0 := by grind
  rw [h0] at h
  exact h

theorem rat_add_pos_of_pos_of_nonneg {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) < a + b := by
  have h1 : (0 : Rat) ≤ a + b := rat_add_nonneg (Rat.le_of_lt ha) hb
  have hne : a + b ≠ 0 := by
    intro h0
    have ha_le : a ≤ 0 := by
      have : -b ≤ 0 := by
        have := rat_sub_nonneg hb
        grind
      have heq : a = -b := by grind
      rw [heq]; exact this
    exact Rat.not_le.mpr ha ha_le
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
    have eq : x * x = (-x) * (-x) := by grind
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_one_add_sq_pos (t : Rat) : (0 : Rat) < 1 + t * t :=
  rat_add_pos_of_pos_of_nonneg (by decide) (rat_sq_nonneg t)

theorem rat_one_add_sq_ne_zero (t : Rat) : 1 + t * t ≠ 0 :=
  Rat.ne_of_gt (rat_one_add_sq_pos t)

theorem rat_le_of_mul_pos_right {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c ≤ b * c) :
    a ≤ b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl hab => exact hab
  | inr hba =>
    by_cases heq : a = b
    · rw [heq]; exact Rat.le_refl
    · have hlt : b < a := Rat.lt_of_le_of_ne hba (Ne.symm heq)
      have hmul : b * c < a * c := rat_mul_lt_mul_of_pos_right hlt hc
      exact False.elim (Rat.not_le.mpr hmul h)

theorem rat_div_mul_cancel {a b : Rat} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.mul_one]

theorem rat_mul_div_cancel {a b : Rat} (hb : b ≠ 0) : b * (a / b) = a := by
  rw [Rat.mul_comm, rat_div_mul_cancel hb]

theorem rat_div_eq_iff {a b c : Rat} (hb : b ≠ 0) : a / b = c ↔ a = c * b := by
  constructor
  · intro h
    rw [← h, rat_div_mul_cancel hb]
  · intro h
    rw [h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel b hb, Rat.mul_one]

theorem rat_div_le_of_mul_le {a b c : Rat} (hc : (0 : Rat) < c) (h : a ≤ b * c) :
    a / c ≤ b := by
  apply rat_le_of_mul_pos_right hc
  rw [rat_div_mul_cancel (Rat.ne_of_gt hc)]
  exact h

theorem rat_le_div_of_mul_le {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c ≤ b) :
    a ≤ b / c := by
  apply rat_le_of_mul_pos_right hc
  rw [rat_div_mul_cancel (Rat.ne_of_gt hc)]
  exact h

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have hle : a ≤ c := Rat.le_trans (Rat.le_of_lt h1) h2
  have hne : a ≠ c := by
    intro heq
    rw [heq] at h1
    exact Rat.not_le.mpr h1 h2
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  have hle : a ≤ c := Rat.le_trans h1 (Rat.le_of_lt h2)
  have hne : a ≠ c := by
    intro heq
    rw [← heq] at h2
    exact Rat.not_le.mpr h2 h1
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  rat_lt_of_lt_of_le h1 (Rat.le_of_lt h2)

theorem rat_sq_le_sq_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b := by
  have hb : (0 : Rat) ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (rat_mul_le_mul_of_nonneg_left hab ha)
    (rat_mul_le_mul_of_nonneg_right hab hb)

/-! ### `ratAbs` Lemmas -/

theorem ratAbs_nonneg (x : Rat) : (0 : Rat) ≤ ratAbs x := by
  unfold ratAbs
  split
  · assumption
  · rename_i h
    have hlt : x < 0 := Rat.not_le.mp h
    exact rat_neg_nonneg_of_nonpos (Rat.le_of_lt hlt)

theorem ratAbs_of_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) : ratAbs x = x := by
  unfold ratAbs
  simp [hx]

theorem ratAbs_of_nonpos {x : Rat} (hx : x ≤ 0) : ratAbs x = -x := by
  unfold ratAbs
  split
  · rename_i hge
    have h0 : x = 0 := Rat.le_antisymm hx hge
    rw [h0]; decide
  · rfl

theorem ratAbs_neg (x : Rat) : ratAbs (-x) = ratAbs x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h =>
    rw [ratAbs_of_nonneg h]
    have hneg : -x ≤ 0 := by
      have := rat_sub_nonneg h
      grind
    rw [ratAbs_of_nonpos hneg]
    grind
  | inr h =>
    rw [ratAbs_of_nonpos h]
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
    rw [ratAbs_of_nonneg hneg]

theorem ratAbs_le_self_and_neg (x : Rat) : x ≤ ratAbs x ∧ -x ≤ ratAbs x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h =>
    rw [ratAbs_of_nonneg h]
    refine ⟨Rat.le_refl, ?_⟩
    have h1 : -x ≤ 0 := by
      have := rat_sub_nonneg h
      grind
    exact Rat.le_trans h1 h
  | inr h =>
    rw [ratAbs_of_nonpos h]
    refine ⟨Rat.le_trans h (rat_neg_nonneg_of_nonpos h), Rat.le_refl⟩

theorem ratAbs_add_le (a b : Rat) : ratAbs (a + b) ≤ ratAbs a + ratAbs b := by
  have ha := ratAbs_le_self_and_neg a
  have hb := ratAbs_le_self_and_neg b
  unfold ratAbs
  split
  · exact rat_add_le_add ha.1 hb.1
  · have hsum : -(a + b) = -a + -b := by grind
    rw [hsum]
    exact rat_add_le_add ha.2 hb.2

theorem ratAbs_sub_le (a b : Rat) : ratAbs (a - b) ≤ ratAbs a + ratAbs b := by
  have h : a - b = a + (-b) := by grind
  rw [h, ← ratAbs_neg b]
  exact ratAbs_add_le a (-b)

theorem ratAbs_mul (a b : Rat) : ratAbs (a * b) = ratAbs a * ratAbs b := by
  cases Rat.le_total (a := (0 : Rat)) (b := a) with
  | inl ha =>
    cases Rat.le_total (a := (0 : Rat)) (b := b) with
    | inl hb =>
      rw [ratAbs_of_nonneg ha, ratAbs_of_nonneg hb, ratAbs_of_nonneg (Rat.mul_nonneg ha hb)]
    | inr hb =>
      have hnb : (0 : Rat) ≤ -b := rat_neg_nonneg_of_nonpos hb
      have hab : a * b ≤ 0 := by
        have h1 : (0 : Rat) ≤ a * (-b) := Rat.mul_nonneg ha hnb
        have h2 : a * (-b) = -(a * b) := by grind
        rw [h2] at h1
        have := rat_le_of_sub_nonneg (a := (0 : Rat)) (b := a * b)
        grind
      rw [ratAbs_of_nonneg ha, ratAbs_of_nonpos hb, ratAbs_of_nonpos hab]
      grind
  | inr ha =>
    have hna : (0 : Rat) ≤ -a := rat_neg_nonneg_of_nonpos ha
    cases Rat.le_total (a := (0 : Rat)) (b := b) with
    | inl hb =>
      have hab : a * b ≤ 0 := by
        have h1 : (0 : Rat) ≤ (-a) * b := Rat.mul_nonneg hna hb
        have h2 : (-a) * b = -(a * b) := by grind
        rw [h2] at h1
        have := rat_le_of_sub_nonneg (a := (0 : Rat)) (b := a * b)
        grind
      rw [ratAbs_of_nonpos ha, ratAbs_of_nonneg hb, ratAbs_of_nonpos hab]
      grind
    | inr hb =>
      have hnb : (0 : Rat) ≤ -b := rat_neg_nonneg_of_nonpos hb
      have hab : (0 : Rat) ≤ a * b := by
        have h1 : (0 : Rat) ≤ (-a) * (-b) := Rat.mul_nonneg hna hnb
        have h2 : (-a) * (-b) = a * b := by grind
        rw [← h2]; exact h1
      rw [ratAbs_of_nonpos ha, ratAbs_of_nonpos hb, ratAbs_of_nonneg hab]
      grind

theorem ratAbs_sq (x : Rat) : ratAbs x * ratAbs x = x * x := by
  unfold ratAbs
  split
  · rfl
  · grind

theorem ratAbs_le_of_bounds {x b : Rat} (hlo : -b ≤ x) (hhi : x ≤ b) : ratAbs x ≤ b := by
  unfold ratAbs
  split
  · exact hhi
  · have := rat_sub_nonneg hlo
    have hneg : (0 : Rat) ≤ b - (-x) := by grind
    exact rat_le_of_sub_nonneg hneg

/-! ### `finSum` Lemmas -/

theorem finSumAux_congr {k : Nat} {f g : Fin k → Rat} (h : ∀ j, f j = g j) :
    finSumAux k f = finSumAux k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [finSumAux]
    rw [ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem finSum_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ j, f j = g j) :
    finSum f = finSum g :=
  finSumAux_congr h

theorem finSum_zero (n : Nat) : finSum (fun _ : Fin n => (0 : Rat)) = 0 := by
  unfold finSum
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumAux]
    rw [ih, Rat.add_zero]

theorem finSum_add {n : Nat} (f g : Fin n → Rat) :
    finSum (fun j => f j + g j) = finSum f + finSum g := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]; grind
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_sub {n : Nat} (f g : Fin n → Rat) :
    finSum (fun j => f j - g j) = finSum f - finSum g := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]; grind
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Rat} (h : ∀ j, f j ≤ g j) :
    finSum f ≤ finSum g := by
  unfold finSum
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [finSumAux]
    exact rat_add_le_add (ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem ratAbs_finSum_le {n : Nat} (f : Fin n → Rat) :
    ratAbs (finSum f) ≤ finSum (fun j => ratAbs (f j)) := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux, ratAbs]
  | succ k ih =>
    simp only [finSumAux]
    exact Rat.le_trans (ratAbs_add_le _ _)
      (rat_add_le_add (ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)) Rat.le_refl)

end RopeQ32Coprime
