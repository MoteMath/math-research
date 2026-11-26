/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SwiGluKurtosis.Defs

/-!
# Pure-`Init` `Rat` Order, Absolute Value, Dyadic Power, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace SwiGluKurtosis

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

theorem rat_neg_of_pos {a : Rat} (h : (0 : Rat) < a) : -a < 0 := by
  apply rat_lt_of_sub_pos
  have : (0 : Rat) - (-a) = a := by grind
  rw [this]; exact h

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

theorem rat_add_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a + b :=
  rat_add_pos_of_pos_of_nonneg ha (Rat.le_of_lt hb)

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
    have eq : x * x = (-x) * (-x) := by grind
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) : (0 : Rat) < x * x := by
  have hle : (0 : Rat) ≤ x * x := rat_sq_nonneg x
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
    exact Rat.not_le.mpr h Rat.le_refl
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_inv_pos {c : Rat} (hc : (0 : Rat) < c) : (0 : Rat) < c⁻¹ := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  have h1 : (0 : Rat) < c⁻¹ * c := by
    rw [Rat.inv_mul_cancel c hne]
    decide
  cases Rat.le_total (a := (0 : Rat)) (b := c⁻¹) with
  | inl hle =>
    have hinv_ne : c⁻¹ ≠ 0 := by
      intro h0
      rw [h0, Rat.zero_mul] at h1
      exact Rat.not_le.mpr h1 Rat.le_refl
    exact Rat.lt_of_le_of_ne hle (Ne.symm hinv_ne)
  | inr hge =>
    have hle0 : c⁻¹ * c ≤ 0 := by
      have h := rat_mul_le_mul_of_nonneg_right hge (Rat.le_of_lt hc)
      rw [Rat.zero_mul] at h
      exact h
    exact False.elim (Rat.not_le.mpr h1 hle0)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

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

theorem rat_div_lt_div_iff {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d) :
    a / b < c / d ↔ a * d < c * b := by
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h (rat_mul_pos hb hd)
    have hl : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hr : (c / d) * (b * d) = c * b := by
      have : (c / d) * (b * d) = (c / d) * d * b := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hl, hr] at h1
    exact h1
  · intro h
    apply rat_lt_of_mul_pos_right (rat_mul_pos hb hd)
    have hl : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hr : (c / d) * (b * d) = c * b := by
      have : (c / d) * (b * d) = (c / d) * d * b := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hl, hr]
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

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    rw [Rat.natCast_add]
    exact rat_add_nonneg ih (by decide)

theorem rat_natCast_le {m n : Nat} (h : m ≤ n) : (m : Rat) ≤ (n : Rat) := by
  have hk : n = m + (n - m) := (Nat.add_sub_of_le h).symm
  rw [hk, Rat.natCast_add]
  have h0 : (0 : Rat) ≤ ((n - m : Nat) : Rat) := rat_natCast_nonneg (n - m)
  have h1 := rat_add_le_add (Rat.le_refl (a := (m : Rat))) h0
  rw [Rat.add_zero] at h1
  exact h1

theorem rat_natCast_lt {m n : Nat} (h : m < n) : (m : Rat) < (n : Rat) := by
  have h1 : ((m + 1 : Nat) : Rat) ≤ (n : Rat) := rat_natCast_le h
  rw [Rat.natCast_add] at h1
  have h2 : (m : Rat) < (m : Rat) + 1 := by
    apply rat_lt_of_sub_pos
    have : (m : Rat) + 1 - (m : Rat) = 1 := by grind
    rw [this]; decide
  exact rat_lt_of_lt_of_le h2 h1

theorem rat_natCast_pos {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) :=
  rat_natCast_lt h

theorem pow2Rat_pos (k : Nat) : (0 : Rat) < pow2Rat k := by
  unfold pow2Rat
  exact rat_natCast_pos (Nat.pow_pos (by decide))

theorem pow2Rat_ne_zero (k : Nat) : pow2Rat k ≠ 0 :=
  Rat.ne_of_gt (pow2Rat_pos k)

theorem pow2Rat_add (a b : Nat) : pow2Rat (a + b) = pow2Rat a * pow2Rat b := by
  unfold pow2Rat
  rw [Nat.pow_add, Rat.natCast_mul]

theorem invPow2Rat_pos (k : Nat) : (0 : Rat) < invPow2Rat k :=
  rat_div_pos (by decide) (pow2Rat_pos k)

theorem invPow2Rat_add (a b : Nat) : invPow2Rat (a + b) = invPow2Rat a * invPow2Rat b := by
  unfold invPow2Rat
  rw [pow2Rat_add]
  have ha := pow2Rat_ne_zero a
  have hb := pow2Rat_ne_zero b
  have hab : pow2Rat a * pow2Rat b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact hb h
  apply (rat_div_eq_iff hab).mpr
  have heq : (1 / pow2Rat a) * (1 / pow2Rat b) * (pow2Rat a * pow2Rat b) =
      ((1 / pow2Rat a) * pow2Rat a) * ((1 / pow2Rat b) * pow2Rat b) := by grind
  rw [heq, rat_div_mul_cancel ha, rat_div_mul_cancel hb]
  grind

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

theorem finSum_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    finSum (fun j => c * f j) = c * finSum f := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    finSum (fun j => f j * c) = finSum f * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
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

theorem finSum_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ j, (0 : Rat) ≤ f j) :
    (0 : Rat) ≤ finSum f := by
  have h1 := finSum_le_finSum h
  rw [finSum_zero] at h1
  exact h1

/-- If `f j ≥ 0` everywhere and `∑ j, f j > 0`, and `g j > 0` everywhere, then `∑ j, f j * g j > 0`. -/
theorem finSum_mul_pos_of_sum_pos {n : Nat} {f g : Fin n → Rat}
    (hf_nn : ∀ j, (0 : Rat) ≤ f j)
    (hf_pos : (0 : Rat) < finSum f)
    (hg_pos : ∀ j, (0 : Rat) < g j) :
    (0 : Rat) < finSum (fun j => f j * g j) := by
  unfold finSum at hf_pos ⊢
  induction n with
  | zero =>
    simp only [finSumAux] at hf_pos
    exact False.elim (Rat.not_le.mpr hf_pos Rat.le_refl)
  | succ k ih =>
    simp only [finSumAux] at hf_pos ⊢
    have hprev_nn : (0 : Rat) ≤ finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) :=
      finSum_nonneg (fun j => hf_nn ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have hprev_mul_nn : (0 : Rat) ≤
        finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ * g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) :=
      finSum_nonneg (fun j => Rat.mul_nonneg (hf_nn _) (Rat.le_of_lt (hg_pos _)))
    have hlast_nn : (0 : Rat) ≤ f ⟨k, Nat.lt_succ_self k⟩ := hf_nn ⟨k, Nat.lt_succ_self k⟩
    have hlast_mul_nn : (0 : Rat) ≤ f ⟨k, Nat.lt_succ_self k⟩ * g ⟨k, Nat.lt_succ_self k⟩ :=
      Rat.mul_nonneg hlast_nn (Rat.le_of_lt (hg_pos _))
    by_cases hlast0 : f ⟨k, Nat.lt_succ_self k⟩ = 0
    · rw [hlast0, Rat.add_zero] at hf_pos
      have hih := ih (fun j => hf_nn ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) hf_pos
        (fun j => hg_pos ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
      exact rat_add_pos_of_pos_of_nonneg hih hlast_mul_nn
    · have hlast_pos : (0 : Rat) < f ⟨k, Nat.lt_succ_self k⟩ :=
        Rat.lt_of_le_of_ne hlast_nn (Ne.symm hlast0)
      have hmul_pos : (0 : Rat) < f ⟨k, Nat.lt_succ_self k⟩ * g ⟨k, Nat.lt_succ_self k⟩ :=
        rat_mul_pos hlast_pos (hg_pos ⟨k, Nat.lt_succ_self k⟩)
      rw [Rat.add_comm]
      exact rat_add_pos_of_pos_of_nonneg hmul_pos hprev_mul_nn

end SwiGluKurtosis
