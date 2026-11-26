/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VlmTomeCumulant.Defs

/-!
# Pure-`Init` `Rat`, `Int`, and `Nat` Order & Finite-Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace VlmTomeCumulant

/-! ### `Rat` Order and Arithmetic Helpers -/

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

theorem rat_add_pos_of_nonneg_of_pos {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a + b := by
  rw [Rat.add_comm]
  exact rat_add_pos_of_pos_of_nonneg hb ha

theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) :
    a + c < b + d := by
  apply rat_lt_of_sub_pos
  have h3 : (0 : Rat) ≤ b - a := rat_sub_nonneg h1
  have h4 : (0 : Rat) < d - c := rat_sub_pos h2
  have eq : b + d - (a + c) = (b - a) + (d - c) := by grind
  rw [eq]
  exact rat_add_pos_of_nonneg_of_pos h3 h4

theorem rat_add_lt_add_of_lt_of_le {a b c d : Rat} (h1 : a < b) (h2 : c ≤ d) :
    a + c < b + d := by
  rw [Rat.add_comm a c, Rat.add_comm b d]
  exact rat_add_lt_add_of_le_of_lt h2 h1

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
    have eq : x * x = (-x) * (-x) := by grind
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) : (0 : Rat) < x * x := by
  have hle := rat_sq_nonneg x
  have hne : x * x ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hx h
    | inr h => exact hx h
  exact Rat.lt_of_le_of_ne hle (Ne.symm hne)

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

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  apply rat_le_div_of_mul_le hb
  have : (0 : Rat) * b = 0 := by grind
  rw [this]; exact ha

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  apply rat_lt_div_of_mul_lt hb
  have : (0 : Rat) * b = 0 := by grind
  rw [this]; exact ha

theorem rat_div_div_eq_mul_div {a b c d : Rat} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - c * b) / (b * d) := by
  have hbd : b * d ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hb h
    | inr h => exact hd h
  symm
  rw [rat_div_eq_iff hbd]
  have h1 : (a / b) * (b * d) = a * d := by
    calc (a / b) * (b * d) = ((a / b) * b) * d := by rw [Rat.mul_assoc]
    _ = a * d := by rw [rat_div_mul_cancel hb]
  have h2 : (c / d) * (b * d) = c * b := by
    calc (c / d) * (b * d) = ((c / d) * d) * b := by grind
    _ = c * b := by rw [rat_div_mul_cancel hd]
  grind

theorem rat_natCast_add (a b : Nat) : ((a + b : Nat) : Rat) = (a : Rat) + (b : Rat) := by
  grind

theorem rat_natCast_mul (a b : Nat) : ((a * b : Nat) : Rat) = (a : Rat) * (b : Rat) := by
  grind

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := rat_natCast_add k 1
    rw [h1]
    exact rat_add_nonneg ih (by decide)

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  cases n with
  | zero => omega
  | succ k =>
    have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := rat_natCast_add k 1
    rw [h1]
    exact rat_add_pos_of_nonneg_of_pos (rat_natCast_nonneg k) (by decide)

theorem rat_natCast_le {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have hdiff : b = a + (b - a) := by omega
  rw [hdiff, rat_natCast_add]
  have hnn : (0 : Rat) ≤ ((b - a : Nat) : Rat) := rat_natCast_nonneg (b - a)
  have := (Rat.add_le_add_right (c := (a : Rat))).mpr hnn
  grind

theorem rat_natCast_lt {a b : Nat} (h : a < b) : (a : Rat) < (b : Rat) := by
  have hdiff : b = a + (b - a) := by omega
  have hpos : 0 < b - a := by omega
  rw [hdiff, rat_natCast_add]
  have hnn : (0 : Rat) < ((b - a : Nat) : Rat) := rat_natCast_pos hpos
  have := rat_add_lt_add_of_le_of_lt (Rat.le_refl (a := (a : Rat))) hnn
  grind

theorem rat_div_le_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := by
  have hb' : (0 : Rat) < (b : Rat) := rat_natCast_pos hb
  have hd' : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  apply rat_div_le_of_mul_le hb'
  apply rat_le_of_mul_pos_right hd'
  have hmul : ((c : Rat) / (d : Rat)) * (b : Rat) * (d : Rat) = (c : Rat) * (b : Rat) := by
    calc ((c : Rat) / (d : Rat)) * (b : Rat) * (d : Rat)
        = (((c : Rat) / (d : Rat)) * (d : Rat)) * (b : Rat) := by grind
      _ = (c : Rat) * (b : Rat) := by rw [rat_div_mul_cancel (Rat.ne_of_gt hd')]
  rw [hmul, ← rat_natCast_mul, ← rat_natCast_mul]
  exact rat_natCast_le h

theorem rat_div_lt_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) :
    (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  have hb' : (0 : Rat) < (b : Rat) := rat_natCast_pos hb
  have hd' : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  apply rat_div_lt_of_mul_lt hb'
  apply rat_lt_of_mul_pos_right hd'
  have hmul : ((c : Rat) / (d : Rat)) * (b : Rat) * (d : Rat) = (c : Rat) * (b : Rat) := by
    calc ((c : Rat) / (d : Rat)) * (b : Rat) * (d : Rat)
        = (((c : Rat) / (d : Rat)) * (d : Rat)) * (b : Rat) := by grind
      _ = (c : Rat) * (b : Rat) := by rw [rat_div_mul_cancel (Rat.ne_of_gt hd')]
  rw [hmul, ← rat_natCast_mul, ← rat_natCast_mul]
  exact rat_natCast_lt h

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

/-! ### `ratAbs` Lemmas -/

theorem ratAbs_zero : ratAbs 0 = 0 := by decide

theorem ratAbs_of_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) : ratAbs x = x := by
  unfold ratAbs
  simp [hx]

/-! ### `finSum` (`Rat`) Lemmas -/

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

theorem finSum_const (n : Nat) (c : Rat) : finSum (fun _ : Fin n => c) = (n : Rat) * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih, rat_natCast_add]
    grind

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

theorem finSum_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    finSum (fun j => c * f j) = c * finSum f := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_div_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    finSum (fun j => f j / c) = finSum f / c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]; grind
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    simp only [Rat.div_def]
    grind

theorem finSum_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ j, (0 : Rat) ≤ f j) :
    (0 : Rat) ≤ finSum f := by
  unfold finSum
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [finSumAux]
    exact rat_add_nonneg (ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem finSum_pos_of_nonneg_of_exists_pos {n : Nat} {f : Fin n → Rat}
    (hnn : ∀ j, (0 : Rat) ≤ f j) (hex : ∃ j, (0 : Rat) < f j) :
    (0 : Rat) < finSum f := by
  unfold finSum
  induction n with
  | zero =>
    obtain ⟨j, _⟩ := hex
    exact Fin.elim0 j
  | succ k ih =>
    simp only [finSumAux]
    obtain ⟨j, hj⟩ := hex
    by_cases hlast : j.val = k
    · have hj' : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      rw [hj'] at hj
      exact rat_add_pos_of_nonneg_of_pos
        (finSum_nonneg (fun i => hnn ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) hj
    · have hlt : j.val < k := by omega
      have hprev := ih (fun i => hnn ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        ⟨⟨j.val, hlt⟩, by simpa using hj⟩
      exact rat_add_pos_of_pos_of_nonneg hprev (hnn ⟨k, Nat.lt_succ_self k⟩)

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Rat} (h : ∀ j, f j ≤ g j) :
    finSum f ≤ finSum g := by
  unfold finSum
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [finSumAux]
    exact rat_add_le_add (ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem finSum_lt_finSum_of_le_of_exists_lt {n : Nat} {f g : Fin n → Rat}
    (hle : ∀ j, f j ≤ g j) (hex : ∃ j, f j < g j) :
    finSum f < finSum g := by
  apply rat_lt_of_sub_pos
  rw [← finSum_sub]
  apply finSum_pos_of_nonneg_of_exists_pos
  · intro j; exact rat_sub_nonneg (hle j)
  · obtain ⟨j, hj⟩ := hex
    exact ⟨j, rat_sub_pos hj⟩

/-! ### `finSumInt` (`Int`) Lemmas -/

theorem finSumIntAux_congr {k : Nat} {f g : Fin k → Int} (h : ∀ j, f j = g j) :
    finSumIntAux k f = finSumIntAux k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [finSumIntAux]
    rw [ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem finSumInt_congr {n : Nat} {f g : Fin n → Int} (h : ∀ j, f j = g j) :
    finSumInt f = finSumInt g :=
  finSumIntAux_congr h

theorem finSumInt_add {n : Nat} (f g : Fin n → Int) :
    finSumInt (fun j => f j + g j) = finSumInt f + finSumInt g := by
  unfold finSumInt
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumIntAux]
    rw [ih]
    omega

theorem finSumInt_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    finSumInt (fun j => c * f j) = c * finSumInt f := by
  unfold finSumInt
  induction n with
  | zero => simp [finSumIntAux]
  | succ k ih =>
    simp only [finSumIntAux]
    rw [ih]
    grind

theorem finSumInt_split {a b : Nat} (f : Fin (a + b) → Int) :
    finSumInt f =
      finSumInt (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩) +
      finSumInt (fun j : Fin b => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  unfold finSumInt
  induction b with
  | zero =>
    simp only [finSumIntAux, Int.add_zero]
    exact finSumIntAux_congr (fun _ => rfl)
  | succ b ih =>
    change finSumIntAux (a + b) (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
        f ⟨a + b, Nat.lt_succ_self (a + b)⟩ =
      finSumIntAux a (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (b + 1))⟩) +
      (finSumIntAux b (fun j => f ⟨a + j.val, Nat.add_lt_add_left (Nat.lt_succ_of_lt j.isLt) a⟩) +
       f ⟨a + b, Nat.add_lt_add_left (Nat.lt_succ_self b) a⟩)
    have hih := ih (fun i : Fin (a + b) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    rw [hih]
    dsimp only
    omega

/-! ### `finSumNat` (`Nat`) Lemmas -/

theorem finSumNatAux_congr {k : Nat} {f g : Fin k → Nat} (h : ∀ j, f j = g j) :
    finSumNatAux k f = finSumNatAux k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [finSumNatAux]
    rw [ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem finSumNat_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ j, f j = g j) :
    finSumNat f = finSumNat g :=
  finSumNatAux_congr h

theorem finSumNat_zero (n : Nat) : finSumNat (fun _ : Fin n => 0) = 0 := by
  unfold finSumNat
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumNatAux]
    rw [ih]

theorem finSumNat_const (n c : Nat) : finSumNat (fun _ : Fin n => c) = n * c := by
  unfold finSumNat
  induction n with
  | zero => simp [finSumNatAux]
  | succ k ih =>
    simp only [finSumNatAux]
    rw [ih, Nat.succ_mul]

theorem finSumNat_add {n : Nat} (f g : Fin n → Nat) :
    finSumNat (fun j => f j + g j) = finSumNat f + finSumNat g := by
  unfold finSumNat
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumNatAux]
    rw [ih]
    omega

theorem finSumNat_le_finSumNat {n : Nat} {f g : Fin n → Nat} (h : ∀ j, f j ≤ g j) :
    finSumNat f ≤ finSumNat g := by
  unfold finSumNat
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [finSumNatAux]
    exact Nat.add_le_add (ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem finSumNat_lt_finSumNat_of_le_of_exists_lt {n : Nat} {f g : Fin n → Nat}
    (hle : ∀ j, f j ≤ g j) (hex : ∃ j, f j < g j) :
    finSumNat f < finSumNat g := by
  unfold finSumNat
  induction n with
  | zero =>
    obtain ⟨j, _⟩ := hex
    exact Fin.elim0 j
  | succ k ih =>
    simp only [finSumNatAux]
    obtain ⟨j, hj⟩ := hex
    by_cases hlast : j.val = k
    · have hj' : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      rw [hj'] at hj
      have hprev := finSumNat_le_finSumNat (fun i : Fin k => hle ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      unfold finSumNat at hprev
      omega
    · have hlt : j.val < k := by omega
      have hprev := ih (fun i => hle ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        ⟨⟨j.val, hlt⟩, by simpa using hj⟩
      have hlastle := hle ⟨k, Nat.lt_succ_self k⟩
      omega

theorem finSumNat_split {a b : Nat} (f : Fin (a + b) → Nat) :
    finSumNat f =
      finSumNat (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩) +
      finSumNat (fun j : Fin b => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  unfold finSumNat
  induction b with
  | zero =>
    simp only [finSumNatAux, Nat.add_zero]
    exact finSumNatAux_congr (fun _ => rfl)
  | succ b ih =>
    change finSumNatAux (a + b) (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
        f ⟨a + b, Nat.lt_succ_self (a + b)⟩ =
      finSumNatAux a (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (b + 1))⟩) +
      (finSumNatAux b (fun j => f ⟨a + j.val, Nat.add_lt_add_left (Nat.lt_succ_of_lt j.isLt) a⟩) +
       f ⟨a + b, Nat.add_lt_add_left (Nat.lt_succ_self b) a⟩)
    have hih := ih (fun i : Fin (a + b) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    rw [hih]
    dsimp only
    omega

theorem finSumNat_single {n : Nat} (j : Fin n) (c : Nat) :
    finSumNat (fun i : Fin n => if i = j then c else 0) = c := by
  unfold finSumNat
  induction n with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    simp only [finSumNatAux]
    by_cases hlast : j.val = k
    · have hj : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      subst hj
      have hzero : finSumNatAux k (fun i : Fin k =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ then c else 0) = 0 := by
        rw [finSumNatAux_congr (g := fun _ => 0)]
        · exact finSumNat_zero k
        · intro i
          have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) ≠ ⟨k, Nat.lt_succ_self k⟩ := by
            intro heq
            have : i.val = k := congrArg Fin.val heq
            omega
          simp [hne]
      rw [hzero]
      simp
    · have hlt : j.val < k := by omega
      have hne : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ j := by
        intro heq
        have : k = j.val := congrArg Fin.val heq
        omega
      simp only [hne, ite_false, Nat.add_zero]
      have hcongr : finSumNatAux k (fun i : Fin k =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) = j then c else 0) =
          finSumNatAux k (fun i : Fin k => if i = ⟨j.val, hlt⟩ then c else 0) := by
        apply finSumNatAux_congr
        intro i
        have hiff : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) = j) ↔ (i = ⟨j.val, hlt⟩) := by
          constructor
          · intro h
            exact Fin.ext (congrArg (fun x : Fin (k + 1) => x.val) h)
          · intro h
            exact Fin.ext (congrArg (fun x : Fin k => x.val) h)
        by_cases hi : i = ⟨j.val, hlt⟩
        · simp [hi]
        · have hi' : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) ≠ j := fun h => hi (hiff.mp h)
          simp only [hi, hi', ite_false]
      rw [hcongr]
      exact ih ⟨j.val, hlt⟩

end VlmTomeCumulant
