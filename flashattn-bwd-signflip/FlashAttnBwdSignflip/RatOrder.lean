/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnBwdSignflip.Defs

/-!
# Pure-`Init` `Rat` Order, Absolute Value, Dyadic Power, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace FlashAttnBwdSignflip

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

theorem rat_mul_neg_of_pos_of_neg {a b : Rat} (ha : (0 : Rat) < a) (hb : b < 0) :
    a * b < 0 := by
  have hpos : (0 : Rat) < a * (-b) := rat_mul_pos ha (rat_neg_pos_of_neg hb)
  have hneg : -(a * (-b)) < 0 := rat_neg_of_pos hpos
  have heq : -(a * (-b)) = a * b := by grind
  rw [← heq]; exact hneg

theorem rat_mul_neg_of_neg_of_pos {a b : Rat} (ha : a < 0) (hb : (0 : Rat) < b) :
    a * b < 0 := by
  rw [Rat.mul_comm]
  exact rat_mul_neg_of_pos_of_neg hb ha

theorem rat_mul_pos_of_neg_of_neg {a b : Rat} (ha : a < 0) (hb : b < 0) :
    (0 : Rat) < a * b := by
  have h := rat_mul_pos (rat_neg_pos_of_neg ha) (rat_neg_pos_of_neg hb)
  have heq : (-a) * (-b) = a * b := by grind
  rw [← heq]; exact h

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

theorem rat_div_eq_iff {a b c : Rat} (hb : b ≠ 0) : a / b = c ↔ a = c * b := by
  constructor
  · intro h
    rw [← h, rat_div_mul_cancel hb]
  · intro h
    rw [h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel b hb, Rat.mul_one]

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

theorem pow2Rat_succ (k : Nat) : pow2Rat (k + 1) = 2 * pow2Rat k := by
  unfold pow2Rat
  have h : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [h, Rat.natCast_mul]
  rfl

theorem invPow2Rat_pos (k : Nat) : (0 : Rat) < invPow2Rat k :=
  rat_div_pos (by decide) (pow2Rat_pos k)

theorem invPow2Rat_succ (k : Nat) : (2 : Rat) * invPow2Rat (k + 1) = invPow2Rat k := by
  unfold invPow2Rat
  rw [pow2Rat_succ]
  have hp : pow2Rat k ≠ 0 := pow2Rat_ne_zero k
  have h2 : (2 : Rat) * pow2Rat k ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact absurd h (by decide)
    | inr h => exact hp h
  apply Eq.symm
  apply (rat_div_eq_iff hp).mpr
  have hmul : (2 : Rat) * (1 / (2 * pow2Rat k)) * pow2Rat k =
      ((1 : Rat) / (2 * pow2Rat k)) * (2 * pow2Rat k) := by grind
  rw [hmul, rat_div_mul_cancel h2]

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

theorem finSum_neg {n : Nat} (f : Fin n → Rat) :
    finSum (fun j => -f j) = -finSum f := by
  have h : (fun j : Fin n => -f j) = (fun j => (-1 : Rat) * f j) := by
    funext j; grind
  rw [h, finSum_mul_left]
  grind

theorem finSum_single {n : Nat} (i : Fin n) (v : Rat) :
    finSum (fun j : Fin n => if j = i then v else (0 : Rat)) = v := by
  unfold finSum
  induction n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    simp only [finSumAux]
    by_cases hi : i.val = k
    · have hiEq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hi
      simp only [hiEq.symm, ite_true]
      have hzero : finSumAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = i then v else 0) =
          finSumAux k (fun _ => (0 : Rat)) := by
        apply finSumAux_congr
        intro j
        have hne : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ i := by
          intro h
          have : j.val = i.val := congrArg Fin.val h
          omega
        simp [hne]
      rw [hzero]
      have hz := finSum_zero k
      unfold finSum at hz
      rw [hz, Rat.zero_add]
    · have hlt : i.val < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi
      have hneLast : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ i := by
        intro h
        exact hi (congrArg Fin.val h).symm
      simp only [hneLast, ite_false, Rat.add_zero]
      have hcongr : finSumAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = i then v else 0) =
          finSumAux k (fun j => if j = ⟨i.val, hlt⟩ then v else 0) := by
        apply finSumAux_congr
        intro j
        by_cases hj : j.val = i.val
        · have h2 : j = ⟨i.val, hlt⟩ := Fin.ext hj
          have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = i := Fin.ext hj
          rw [h1, h2]
          simp only [ite_true]
        · have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ i :=
            fun h => hj (congrArg Fin.val h)
          have h2 : j ≠ ⟨i.val, hlt⟩ := fun h => hj (congrArg Fin.val h)
          simp [h1, h2]
      rw [hcongr]
      exact ih ⟨i.val, hlt⟩

theorem finSum_split_at {n : Nat} (i : Fin n) (f : Fin n → Rat) :
    finSum f = f i + finSumExcept i f := by
  unfold finSumExcept
  have hdecomp : finSum f =
      finSum (fun j : Fin n => (if j = i then f i else 0) + (if j = i then 0 else f j)) := by
    apply finSum_congr
    intro j
    by_cases hji : j = i
    · simp [hji, Rat.add_zero]
    · simp [hji, Rat.zero_add]
  rw [hdecomp, finSum_add, finSum_single]

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

theorem ratAbs_finSum_le {n : Nat} (f : Fin n → Rat) :
    ratAbs (finSum f) ≤ finSum (fun j => ratAbs (f j)) := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux, ratAbs]
  | succ k ih =>
    simp only [finSumAux]
    exact Rat.le_trans (ratAbs_add_le _ _)
      (rat_add_le_add (ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)) Rat.le_refl)

/-- Exact finite-dimensional Cauchy-Schwarz inequality over `Rat`:
    `(∑_j a_j b_j)^2 ≤ (∑_j a_j^2) * (∑_j b_j^2)`. -/
theorem cauchy_schwarz_finSum {n : Nat} (a b : Fin n → Rat) :
    dotProd a b * dotProd a b ≤ l2NormSq a * l2NormSq b := by
  have hnonneg : (0 : Rat) ≤
      finSum (fun i : Fin n => finSum (fun j : Fin n =>
        (a i * b j - a j * b i) * (a i * b j - a j * b i))) := by
    apply finSum_nonneg
    intro i
    apply finSum_nonneg
    intro j
    exact rat_sq_nonneg _
  have hexpand :
      finSum (fun i : Fin n => finSum (fun j : Fin n =>
        (a i * b j - a j * b i) * (a i * b j - a j * b i))) =
      2 * (l2NormSq a * l2NormSq b - dotProd a b * dotProd a b) := by
    have hinner : ∀ i : Fin n,
        finSum (fun j : Fin n => (a i * b j - a j * b i) * (a i * b j - a j * b i)) =
        (a i * a i) * l2NormSq b - 2 * (a i * b i) * dotProd a b + (b i * b i) * l2NormSq a := by
      intro i
      have hterm : ∀ j : Fin n,
          (a i * b j - a j * b i) * (a i * b j - a j * b i) =
          (a i * a i) * (b j * b j) - (2 * (a i * b i)) * (a j * b j) + (b i * b i) * (a j * a j) := by
        intro j; grind
      rw [finSum_congr hterm, finSum_add, finSum_sub,
          finSum_mul_left, finSum_mul_left, finSum_mul_left]
      rfl
    rw [finSum_congr hinner, finSum_add, finSum_sub,
        finSum_mul_right, finSum_mul_right, finSum_mul_right]
    have hmid : finSum (fun i : Fin n => 2 * (a i * b i)) = 2 * dotProd a b := by
      rw [finSum_mul_left]; rfl
    rw [hmid]
    unfold l2NormSq dotProd
    grind
  rw [hexpand] at hnonneg
  have hsub : (0 : Rat) ≤ l2NormSq a * l2NormSq b - dotProd a b * dotProd a b := by
    apply rat_le_of_mul_pos_right (c := (2 : Rat)) (by decide)
    have h0 : (0 : Rat) * 2 = 0 := by grind
    rw [h0, Rat.mul_comm]
    exact hnonneg
  exact rat_le_of_sub_nonneg hsub

theorem finSum_two (f : Fin 2 → Rat) : finSum f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := by
  simp [finSum, finSumAux, Rat.zero_add]

end FlashAttnBwdSignflip
