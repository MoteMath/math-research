/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relu2TealDeadzone.Defs

/-!
# Pure-`Init` `Rat` Order, Absolute Value, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`, zero `grind` — compiles in `< 1s`.
-/

namespace Relu2TealDeadzone

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have h1 := (Rat.add_le_add_right (c := -b)).mpr h
  rw [Rat.add_neg_cancel, ← Rat.sub_eq_add_neg] at h1
  exact h1

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have h1 := (Rat.add_le_add_right (c := b)).mpr h
  rw [Rat.zero_add, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero] at h1
  exact h1

theorem rat_sub_pos {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by
  have h1 : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt h)
  have hne : a - b ≠ 0 := by
    intro h0
    have heq : a = b := by
      have h2 := congrArg (· + b) h0
      rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero, Rat.zero_add] at h2
      exact h2
    exact Rat.ne_of_gt h heq
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_lt_of_sub_pos {a b : Rat} (h : (0 : Rat) < a - b) : b < a := by
  have h1 : b ≤ a := rat_le_of_sub_nonneg (Rat.le_of_lt h)
  have hne : b ≠ a := by
    intro h0
    have : a - b = 0 := by rw [h0, Rat.sub_self]
    exact Rat.ne_of_gt h this
  exact Rat.lt_of_le_of_ne h1 hne

theorem rat_neg_nonneg_of_nonpos {a : Rat} (h : a ≤ 0) : (0 : Rat) ≤ -a := by
  have h1 := rat_sub_nonneg h
  rw [Rat.sub_eq_add_neg, Rat.zero_add] at h1
  exact h1

theorem rat_neg_nonpos_of_nonneg {a : Rat} (h : (0 : Rat) ≤ a) : -a ≤ 0 := by
  have h1 := (Rat.add_le_add_right (c := -a)).mpr h
  rw [Rat.zero_add, Rat.add_neg_cancel] at h1
  exact h1

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
  rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, ← Rat.sub_eq_add_neg] at h2
  exact h2

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  apply rat_lt_of_sub_pos
  have h1 : (0 : Rat) < b - a := rat_sub_pos h
  have h2 : (0 : Rat) < c * (b - a) := rat_mul_pos hc h1
  rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, ← Rat.sub_eq_add_neg] at h2
  exact h2

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
  rw [Rat.add_zero] at h
  exact h

theorem rat_add_pos_of_pos_of_nonneg {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) < a + b := by
  have h1 : (0 : Rat) ≤ a + b := rat_add_nonneg (Rat.le_of_lt ha) hb
  have hne : a + b ≠ 0 := by
    intro h0
    have heq : a = -b := by
      have h2 := congrArg (· + -b) h0
      rw [Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.zero_add] at h2
      exact h2
    have hle : a ≤ 0 := by rw [heq]; exact rat_neg_nonpos_of_nonneg hb
    exact Rat.not_le.mpr ha hle
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) :
    a + c < b + d := by
  apply rat_lt_of_sub_pos
  have hba : (0 : Rat) ≤ b - a := rat_sub_nonneg h1
  have hdc : (0 : Rat) < d - c := rat_sub_pos h2
  have eq : (b + d) - (a + c) = (d - c) + (b - a) := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add]
    rw [Rat.add_assoc, ← Rat.add_assoc d (-a) (-c), Rat.add_comm d (-a),
        Rat.add_assoc (-a) d (-c), ← Rat.add_assoc b (-a) (d + -c),
        Rat.add_comm (b + -a) (d + -c)]
  rw [eq]
  exact rat_add_pos_of_pos_of_nonneg hdc hba

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

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ sq x := by
  unfold sq
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
    have eq : x * x = (-x) * (-x) := by rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_pos {x : Rat} (hx : (0 : Rat) < x) : (0 : Rat) < sq x :=
  rat_mul_pos hx hx

theorem rat_sq_le_sq_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    sq a ≤ sq b := by
  unfold sq
  have hb : (0 : Rat) ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (rat_mul_le_mul_of_nonneg_left hab ha)
    (rat_mul_le_mul_of_nonneg_right hab hb)

theorem rat_sq_lt_sq_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (h : a < b) :
    sq a < sq b := by
  unfold sq
  have hb : (0 : Rat) < b := rat_lt_of_le_of_lt ha h
  have h1 : a * a ≤ a * b := rat_mul_le_mul_of_nonneg_left (Rat.le_of_lt h) ha
  have h2 : a * b < b * b := rat_mul_lt_mul_of_pos_right h hb
  exact rat_lt_of_le_of_lt h1 h2

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

theorem rat_lt_of_mul_pos_right {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c < b * c) :
    a < b := by
  have hle : a ≤ b := rat_le_of_mul_pos_right hc (Rat.le_of_lt h)
  have hne : a ≠ b := by
    intro heq
    rw [heq] at h
    exact Rat.lt_irrefl h
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_eq_of_mul_pos_right {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c = b * c) :
    a = b :=
  Rat.le_antisymm
    (rat_le_of_mul_pos_right hc (h ▸ Rat.le_refl))
    (rat_le_of_mul_pos_right hc (h.symm ▸ Rat.le_refl))

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

theorem rat_div_lt_div_of_cross {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d)
    (h : a * d < c * b) : a / b < c / d := by
  apply rat_lt_of_mul_pos_right (rat_mul_pos hb hd)
  have hL : (a / b) * (b * d) = a * d := by
    rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
  have hR : (c / d) * (b * d) = c * b := by
    rw [Rat.mul_comm b d, ← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hd)]
  rw [hL, hR]
  exact h

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  apply rat_lt_of_mul_pos_right hb
  rw [rat_div_mul_cancel (Rat.ne_of_gt hb), Rat.zero_mul]
  exact ha

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  apply rat_le_of_mul_pos_right hb
  rw [rat_div_mul_cancel (Rat.ne_of_gt hb), Rat.zero_mul]
  exact ha

theorem rat_div_lt_of_mul_lt {a b c : Rat} (hc : (0 : Rat) < c) (h : a < b * c) :
    a / c < b := by
  apply rat_lt_of_mul_pos_right hc
  rw [rat_div_mul_cancel (Rat.ne_of_gt hc)]
  exact h

theorem rat_lt_div_of_mul_lt {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c < b) :
    a < b / c := by
  apply rat_lt_of_mul_pos_right hc
  rw [rat_div_mul_cancel (Rat.ne_of_gt hc)]
  exact h

theorem rat_div_lt_div_of_pos_right {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    a / c < b / c := by
  apply rat_lt_of_mul_pos_right hc
  rw [rat_div_mul_cancel (Rat.ne_of_gt hc), rat_div_mul_cancel (Rat.ne_of_gt hc)]
  exact h

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
    rw [ratAbs_of_nonneg h, ratAbs_of_nonpos (rat_neg_nonpos_of_nonneg h), Rat.neg_neg]
  | inr h =>
    rw [ratAbs_of_nonpos h, ratAbs_of_nonneg (rat_neg_nonneg_of_nonpos h)]

theorem ratAbs_le_self_and_neg (x : Rat) : x ≤ ratAbs x ∧ -x ≤ ratAbs x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h =>
    rw [ratAbs_of_nonneg h]
    exact ⟨Rat.le_refl, Rat.le_trans (rat_neg_nonpos_of_nonneg h) h⟩
  | inr h =>
    rw [ratAbs_of_nonpos h]
    exact ⟨Rat.le_trans h (rat_neg_nonneg_of_nonpos h), Rat.le_refl⟩

theorem ratAbs_le_iff {x b : Rat} : ratAbs x ≤ b ↔ (-b ≤ x ∧ x ≤ b) := by
  constructor
  · intro h
    have hsn := ratAbs_le_self_and_neg x
    refine ⟨?_, Rat.le_trans hsn.1 h⟩
    have hneg : -x ≤ b := Rat.le_trans hsn.2 h
    have hsub : (0 : Rat) ≤ b - (-x) := rat_sub_nonneg hneg
    have eq : x - (-b) = b - (-x) := by
      rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_neg, Rat.neg_neg, Rat.add_comm]
    exact rat_le_of_sub_nonneg (by rw [eq]; exact hsub)
  · intro h
    unfold ratAbs
    split
    · exact h.2
    · have hsub : (0 : Rat) ≤ x - (-b) := rat_sub_nonneg h.1
      have eq : b - (-x) = x - (-b) := by
        rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_neg, Rat.neg_neg, Rat.add_comm]
      exact rat_le_of_sub_nonneg (by rw [eq]; exact hsub)

theorem ratAbs_add_le (a b : Rat) : ratAbs (a + b) ≤ ratAbs a + ratAbs b := by
  have ha := ratAbs_le_self_and_neg a
  have hb := ratAbs_le_self_and_neg b
  unfold ratAbs
  split
  · exact rat_add_le_add ha.1 hb.1
  · rw [Rat.neg_add]
    exact rat_add_le_add ha.2 hb.2

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
        rw [Rat.mul_neg] at h1
        have h2 := rat_neg_nonpos_of_nonneg h1
        rw [Rat.neg_neg] at h2
        exact h2
      rw [ratAbs_of_nonneg ha, ratAbs_of_nonpos hb, ratAbs_of_nonpos hab, Rat.mul_neg]
  | inr ha =>
    have hna : (0 : Rat) ≤ -a := rat_neg_nonneg_of_nonpos ha
    cases Rat.le_total (a := (0 : Rat)) (b := b) with
    | inl hb =>
      have hab : a * b ≤ 0 := by
        have h1 : (0 : Rat) ≤ (-a) * b := Rat.mul_nonneg hna hb
        rw [Rat.neg_mul] at h1
        have h2 := rat_neg_nonpos_of_nonneg h1
        rw [Rat.neg_neg] at h2
        exact h2
      rw [ratAbs_of_nonpos ha, ratAbs_of_nonneg hb, ratAbs_of_nonpos hab, Rat.neg_mul]
    | inr hb =>
      have hnb : (0 : Rat) ≤ -b := rat_neg_nonneg_of_nonpos hb
      have hab : (0 : Rat) ≤ a * b := by
        have h1 : (0 : Rat) ≤ (-a) * (-b) := Rat.mul_nonneg hna hnb
        rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at h1
        exact h1
      rw [ratAbs_of_nonpos ha, ratAbs_of_nonpos hb, ratAbs_of_nonneg hab,
          Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

/-! ### `finSum` Lemmas -/

theorem finSum_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem finSum_add {n : Nat} (f g : Fin n → Rat) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => simp [finSum, Rat.add_zero]
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
           (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    rw [Rat.add_assoc, ← Rat.add_assoc (finSum (fun i : Fin k => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)),
        Rat.add_comm (finSum (fun i : Fin k => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)),
        Rat.add_assoc, ← Rat.add_assoc]

theorem finSum_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    finSum (fun i => c * f i) = c * finSum f := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩), ← Rat.mul_add]

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [finSum]
    exact rat_add_le_add (ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem finSum_lt_finSum {n : Nat} {f g : Fin n → Rat}
    (hle : ∀ i, f i ≤ g i) (hlt : ∃ j, f j < g j) :
    finSum f < finSum g := by
  induction n with
  | zero =>
    rcases hlt with ⟨j, _⟩
    exact False.elim (Nat.not_lt_zero j.val j.isLt)
  | succ k ih =>
    simp only [finSum]
    rcases hlt with ⟨j, hj⟩
    by_cases hjk : j.val = k
    · have hjeq : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hjk
      rw [hjeq] at hj
      exact rat_add_lt_add_of_le_of_lt
        (finSum_le_finSum (fun i => hle ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) hj
    · have hjlt : j.val < k := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt) hjk
      have h1 : finSum (fun i : Fin k => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) <
                finSum (fun i : Fin k => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
        ih (fun i => hle ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ⟨⟨j.val, hjlt⟩, hj⟩
      rw [Rat.add_comm (finSum _), Rat.add_comm (finSum _)]
      exact rat_add_lt_add_of_le_of_lt (hle ⟨k, Nat.lt_succ_self k⟩) h1

end Relu2TealDeadzone
