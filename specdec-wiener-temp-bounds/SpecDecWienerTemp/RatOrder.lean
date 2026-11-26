/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecWienerTemp.Defs

/-!
# Pure-`Init` `Rat` Order, Power, `ratMin`, `ratAbs`, and `finSum` Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace SpecDecWienerTemp

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
  have h1 : (0 : Rat) ≤ x * x := rat_sq_nonneg x
  have hne : x * x ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hx h
    | inr h => exact hx h
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

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

theorem rat_eq_of_mul_eq_mul_right {a b c : Rat} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have h1 : (a * c) * c⁻¹ = (b * c) * c⁻¹ := by rw [h]
  rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_inv_cancel c hc, Rat.mul_one, Rat.mul_one] at h1
  exact h1

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

theorem rat_div_le_div_iff {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  have hbd : (0 : Rat) < b * d := rat_mul_pos hb hd
  constructor
  · intro h
    have hmul := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hbd)
    have hL : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hR : (c / d) * (b * d) = c * b := by
      rw [Rat.mul_comm b d, ← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hL, hR] at hmul
    exact hmul
  · intro h
    apply rat_le_of_mul_pos_right hbd
    have hL : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hR : (c / d) * (b * d) = c * b := by
      rw [Rat.mul_comm b d, ← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hL, hR]
    exact h

theorem rat_div_lt_div_iff {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d) :
    a / b < c / d ↔ a * d < c * b := by
  have hbd : (0 : Rat) < b * d := rat_mul_pos hb hd
  constructor
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h hbd
    have hL : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hR : (c / d) * (b * d) = c * b := by
      rw [Rat.mul_comm b d, ← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hL, hR] at hmul
    exact hmul
  · intro h
    apply rat_lt_of_mul_pos_right hbd
    have hL : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hR : (c / d) * (b * d) = c * b := by
      rw [Rat.mul_comm b d, ← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hL, hR]
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

theorem rat_natCast_succ (k : Nat) : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
  grind

theorem rat_intCast_lt {a b : Int} (h : a < b) : (a : Rat) < (b : Rat) := by
  rw [Rat.lt_iff]
  change a * (1 : Nat) < b * (1 : Nat)
  omega

theorem rat_intCast_le {a b : Int} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  rw [Rat.le_iff]
  change a * (1 : Nat) ≤ b * (1 : Nat)
  omega

theorem rat_div_lt_div_of_int {a b c d : Int} (hb : (0 : Int) < b) (hd : (0 : Int) < d)
    (h : a * d < c * b) : (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  have hb' : (0 : Rat) < (b : Rat) := rat_intCast_lt hb
  have hd' : (0 : Rat) < (d : Rat) := rat_intCast_lt hd
  rw [rat_div_lt_div_iff hb' hd', ← Rat.intCast_mul, ← Rat.intCast_mul]
  exact rat_intCast_lt h

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    rw [rat_natCast_succ]
    exact rat_add_nonneg ih (by decide)

/-! ### `ratPow` Lemmas -/

theorem ratPow_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) (n : Nat) : (0 : Rat) ≤ ratPow x n := by
  induction n with
  | zero => simp only [ratPow]; decide
  | succ k ih => exact Rat.mul_nonneg ih hx

theorem ratPow_pos {x : Rat} (hx : (0 : Rat) < x) (n : Nat) : (0 : Rat) < ratPow x n := by
  induction n with
  | zero => simp only [ratPow]; decide
  | succ k ih => exact rat_mul_pos ih hx

theorem ratPow_le_one {x : Rat} (h0 : (0 : Rat) ≤ x) (h1 : x ≤ 1) (n : Nat) :
    ratPow x n ≤ 1 := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [ratPow]
    have hmul : ratPow x k * x ≤ 1 * 1 := by
      have ha : ratPow x k * x ≤ 1 * x := rat_mul_le_mul_of_nonneg_right ih h0
      have hb : 1 * x ≤ 1 * 1 := rat_mul_le_mul_of_nonneg_left h1 (by decide)
      exact Rat.le_trans ha hb
    rw [Rat.mul_one] at hmul
    exact hmul

theorem ratPow_one (n : Nat) : ratPow 1 n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [ratPow, ih]

theorem ratPow_div (a b : Int) (hb : (b : Rat) ≠ 0) (n : Nat) :
    ratPow ((a : Rat) / (b : Rat)) n = ((a ^ n : Int) : Rat) / ((b ^ n : Int) : Rat) := by
  induction n with
  | zero =>
    simp only [ratPow, Int.pow_zero, Rat.intCast_one]
    grind
  | succ k ih =>
    simp only [ratPow]
    rw [ih]
    have hbk : ((b ^ k : Int) : Rat) ≠ 0 := by
      have : ((b ^ k : Int) : Rat) = ratPow (b : Rat) k := by
        clear ih
        induction k with
        | zero => simp [ratPow]
        | succ m ihm =>
          rw [Int.pow_succ, Rat.intCast_mul, ihm]; rfl
      rw [this]
      clear ih this
      induction k with
      | zero => simp [ratPow]
      | succ m ihm =>
        simp only [ratPow]
        intro h0
        cases Rat.mul_eq_zero.mp h0 with
        | inl h => exact ihm h
        | inr h => exact hb h
    have hbk1 : ((b ^ (k + 1) : Int) : Rat) ≠ 0 := by
      rw [Int.pow_succ, Rat.intCast_mul]
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact hbk h
      | inr h => exact hb h
    symm
    rw [rat_div_eq_iff hbk1, Int.pow_succ, Int.pow_succ, Rat.intCast_mul, Rat.intCast_mul]
    symm
    calc (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat)) * ((a : Rat) / (b : Rat)) *
          (((b ^ k : Int) : Rat) * (b : Rat))
        = ((((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat)) * ((b ^ k : Int) : Rat)) *
          (((a : Rat) / (b : Rat)) * (b : Rat)) := by grind
      _ = ((a ^ k : Int) : Rat) * (a : Rat) := by
          rw [rat_div_mul_cancel hbk, rat_div_mul_cancel hb]

/-! ### `ratAbs` and `ratMin` Lemmas -/

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

theorem ratMin_eq_half_sub_abs (a b : Rat) :
    ratMin a b = (a + b - ratAbs (a - b)) / 2 := by
  unfold ratMin
  split
  · rename_i hab
    have hsub : a - b ≤ 0 := by
      have := rat_sub_nonneg hab
      grind
    rw [ratAbs_of_nonpos hsub]
    grind
  · rename_i hnot
    have hlt : b < a := Rat.not_le.mp hnot
    have hsub : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt hlt)
    rw [ratAbs_of_nonneg hsub]
    grind

theorem ratMin_self (a : Rat) : ratMin a a = a := by
  unfold ratMin
  simp

theorem ratMin_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) ≤ ratMin a b := by
  unfold ratMin
  split
  · exact ha
  · exact hb

theorem ratMin_le_left (a b : Rat) : ratMin a b ≤ a := by
  unfold ratMin
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem ratMin_le_right (a b : Rat) : ratMin a b ≤ b := by
  unfold ratMin
  split
  · assumption
  · exact Rat.le_refl

theorem le_ratMin {a b c : Rat} (ha : c ≤ a) (hb : c ≤ b) : c ≤ ratMin a b := by
  unfold ratMin
  split
  · exact ha
  · exact hb

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

theorem finSum_div {n : Nat} (f : Fin n → Rat) (c : Rat) :
    finSum (fun j => f j / c) = finSum f / c := by
  have h1 : (fun j => f j / c) = (fun j => f j * c⁻¹) := by
    funext j; exact Rat.div_def (f j) c
  rw [h1, finSum_mul_right, ← Rat.div_def]

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
  rw [← finSum_zero n]
  exact finSum_le_finSum h

theorem finSum_const (n : Nat) (c : Rat) : finSum (fun _ : Fin n => c) = (n : Rat) * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih, rat_natCast_succ]
    grind

theorem finSum_elem_le_finSum {n : Nat} {f : Fin n → Rat} (h : ∀ j, (0 : Rat) ≤ f j) (i : Fin n) :
    f i ≤ finSum f := by
  unfold finSum
  induction n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    simp only [finSumAux]
    by_cases heq : i.val = k
    · have hi : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext heq
      rw [hi]
      have hsum : (0 : Rat) ≤ finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) :=
        finSum_nonneg (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
      have hadd := rat_add_le_add hsum (Rat.le_refl (a := f ⟨k, Nat.lt_succ_self k⟩))
      rw [Rat.zero_add] at hadd
      exact hadd
    · have hlt : i.val < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) heq
      have hrec := ih (f := fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
        (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) ⟨i.val, hlt⟩
      have hfk : (0 : Rat) ≤ f ⟨k, Nat.lt_succ_self k⟩ := h ⟨k, Nat.lt_succ_self k⟩
      have hadd := rat_add_le_add hrec hfk
      rw [Rat.add_zero] at hadd
      exact hadd

end SpecDecWienerTemp
