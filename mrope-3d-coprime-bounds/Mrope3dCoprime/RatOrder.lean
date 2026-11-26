/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mrope3dCoprime.Defs

/-!
# Pure-`Init` `Rat` Order, Power, Absolute Value, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace Mrope3dCoprime

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

theorem rat_div_le_div_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) < c) :
    a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))

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

theorem invPow2Rat_pos (k : Nat) : (0 : Rat) < invPow2Rat k :=
  rat_div_pos (by decide) (pow2Rat_pos k)

/-! ### `ratPow` Lemmas -/

theorem ratPow_pos {x : Rat} (hx : (0 : Rat) < x) (k : Nat) : (0 : Rat) < ratPow x k := by
  induction k with
  | zero => simp only [ratPow]; decide
  | succ k ih => exact rat_mul_pos ih hx

theorem ratPow_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) (k : Nat) : (0 : Rat) ≤ ratPow x k := by
  induction k with
  | zero => simp only [ratPow]; decide
  | succ k ih => exact Rat.mul_nonneg ih hx

theorem ratPow_ne_zero {x : Rat} (hx : (0 : Rat) < x) (k : Nat) : ratPow x k ≠ 0 :=
  Rat.ne_of_gt (ratPow_pos hx k)

theorem ratPow_add (x : Rat) (a b : Nat) : ratPow x (a + b) = ratPow x a * ratPow x b := by
  induction b with
  | zero => simp [ratPow, Rat.mul_one]
  | succ b ih =>
    rw [Nat.add_succ, ratPow, ih, ratPow, Rat.mul_assoc]

theorem ratPow_mul (x : Rat) (a b : Nat) : ratPow x (a * b) = ratPow (ratPow x a) b := by
  induction b with
  | zero => simp [ratPow]
  | succ b ih =>
    rw [Nat.mul_succ, ratPow_add, ih, ratPow]

theorem ratPow_mul_distrib (x y : Rat) (k : Nat) :
    ratPow (x * y) k = ratPow x k * ratPow y k := by
  induction k with
  | zero => simp [ratPow]
  | succ k ih =>
    simp only [ratPow, ih]
    grind

theorem ratPow_le_ratPow {x y : Rat} (hx : (0 : Rat) ≤ x) (hxy : x ≤ y) (k : Nat) :
    ratPow x k ≤ ratPow y k := by
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [ratPow]
    have hy : (0 : Rat) ≤ y := Rat.le_trans hx hxy
    have h1 := rat_mul_le_mul_of_nonneg_right ih hx
    have h2 := rat_mul_le_mul_of_nonneg_left hxy (ratPow_nonneg hy k)
    exact Rat.le_trans h1 h2

theorem ratPow_lt_ratPow {x y : Rat} (hx : (0 : Rat) ≤ x) (hxy : x < y) {k : Nat} (hk : 0 < k) :
    ratPow x k < ratPow y k := by
  cases k with
  | zero => exact absurd hk (by decide)
  | succ k =>
    clear hk
    induction k with
    | zero =>
      simp only [ratPow, Rat.one_mul]
      exact hxy
    | succ k ih =>
      simp only [ratPow]
      have hy : (0 : Rat) < y := rat_lt_of_le_of_lt hx hxy
      have h1 : ratPow x (k + 1) * x ≤ ratPow x (k + 1) * y :=
        rat_mul_le_mul_of_nonneg_left (Rat.le_of_lt hxy) (ratPow_nonneg hx (k + 1))
      have h2 : ratPow x (k + 1) * y < ratPow y (k + 1) * y :=
        rat_mul_lt_mul_of_pos_right ih hy
      exact rat_lt_of_le_of_lt h1 h2

theorem rat_lt_of_ratPow_lt {x y : Rat} (_hx : (0 : Rat) ≤ x) (hy : (0 : Rat) ≤ y)
    {k : Nat} (_hk : 0 < k) (h : ratPow x k < ratPow y k) : x < y := by
  cases Rat.le_total (a := y) (b := x) with
  | inl hyx =>
    have hpow : ratPow y k ≤ ratPow x k := ratPow_le_ratPow hy hyx k
    exact False.elim (Rat.not_le.mpr h hpow)
  | inr hxy =>
    by_cases heq : x = y
    · rw [heq] at h
      exact False.elim (Rat.not_le.mpr h Rat.le_refl)
    · exact Rat.lt_of_le_of_ne hxy heq

theorem ratPow_natCast (a k : Nat) : ratPow (a : Rat) k = ((a ^ k : Nat) : Rat) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ratPow, ih, Nat.pow_succ, Rat.natCast_mul]

theorem ratPow_div_one {x : Rat} (hx : x ≠ 0) (k : Nat) :
    ratPow (1 / x) k * ratPow x k = 1 := by
  rw [← ratPow_mul_distrib, rat_div_mul_cancel hx]
  induction k with
  | zero => rfl
  | succ k ih => rw [ratPow, ih, Rat.mul_one]

theorem ratPow_one (k : Nat) : ratPow (1 : Rat) k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ratPow, ih, Rat.mul_one]

theorem ratPow_one_lt_of_lt_one {x : Rat} (hx0 : (0 : Rat) < x) (hx1 : x < 1) {k : Nat} (hk : 0 < k) :
    ratPow x k < 1 := by
  have h := ratPow_lt_ratPow (Rat.le_of_lt hx0) hx1 hk
  rw [ratPow_one] at h
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

theorem ratAbs_le_iff {x b : Rat} : ratAbs x ≤ b ↔ (-b ≤ x ∧ x ≤ b) := by
  unfold ratAbs
  split
  · rename_i hx
    constructor
    · intro h
      refine ⟨?_, h⟩
      have hb : (0 : Rat) ≤ b := Rat.le_trans hx h
      have hnb : -b ≤ 0 := by
        have := rat_sub_nonneg hb; grind
      exact Rat.le_trans hnb hx
    · intro h; exact h.2
  · rename_i hx
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := rat_sub_nonneg h; grind
      · have hlt : x < 0 := Rat.not_le.mp hx
        have hnx : (0 : Rat) < -x := rat_neg_pos_of_neg hlt
        have hb : (0 : Rat) ≤ b := Rat.le_trans (Rat.le_of_lt hnx) h
        exact Rat.le_trans (Rat.le_of_lt hlt) hb
    · intro h
      have := rat_sub_nonneg h.1; grind

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

theorem finSum_const (n : Nat) (c : Rat) : finSum (fun _ : Fin n => c) = (n : Rat) * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih, Rat.natCast_add]
    grind

theorem finSum_ones (n : Nat) : finSum (fun _ : Fin n => (1 : Rat)) = (n : Rat) := by
  rw [finSum_const, Rat.mul_one]

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

/-- Pigeonhole principle for finite sums over `Rat`: if `c * n ≤ ∑_{j : Fin n} f j` with `n > 0`,
    then there exists `j : Fin n` with `c ≤ f j`. -/
theorem exists_ge_of_finSum_ge {n : Nat} (hn : 0 < n) (f : Fin n → Rat) (c : Rat)
    (hsum : (n : Rat) * c ≤ finSum f) : ∃ j : Fin n, c ≤ f j := by
  apply Classical.byContradiction
  intro hnone
  have hall : ∀ j : Fin n, f j < c := by
    intro j
    have hnot : ¬ (c ≤ f j) := fun hj => hnone ⟨j, hj⟩
    exact Rat.not_le.mp hnot
  have hstrict : finSum f < (n : Rat) * c := by
    have haux : ∀ (k : Nat) (hk : 0 < k) (g : Fin k → Rat),
        (∀ j : Fin k, g j < c) → finSum g < (k : Rat) * c := by
      intro k
      induction k with
      | zero => intro hk; exact absurd hk (by decide)
      | succ k ih =>
        intro _ g hg
        unfold finSum
        simp only [finSumAux]
        cases k with
        | zero =>
          simp only [finSumAux, Rat.zero_add]
          have h1 : ((1 : Nat) : Rat) * c = c := by grind
          rw [h1]
          exact hg ⟨0, by decide⟩
        | succ k' =>
          have ih' := ih (Nat.succ_pos k') (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
            (fun j => hg ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
          unfold finSum at ih'
          have hlast := hg ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩
          have hsum_lt : finSumAux (k' + 1) (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
              g ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩ < ((k' + 1 : Nat) : Rat) * c + c := by
            have h1 := rat_add_le_add (Rat.le_of_lt ih') (Rat.le_of_lt hlast)
            have hne : finSumAux (k' + 1) (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
                g ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩ ≠ ((k' + 1 : Nat) : Rat) * c + c := by
              intro heq
              have hsub1 : (0 : Rat) < ((k' + 1 : Nat) : Rat) * c -
                  finSumAux (k' + 1) (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) := rat_sub_pos ih'
              have hsub2 : (0 : Rat) < c - g ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩ := rat_sub_pos hlast
              have htot := rat_add_pos hsub1 hsub2
              have hz : (((k' + 1 : Nat) : Rat) * c -
                  finSumAux (k' + 1) (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)) +
                  (c - g ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩) = 0 := by grind
              rw [hz] at htot
              exact Rat.not_le.mpr htot Rat.le_refl
            exact Rat.lt_of_le_of_ne h1 hne
          have hcast : (((k' + 1) + 1 : Nat) : Rat) * c = ((k' + 1 : Nat) : Rat) * c + c := by
            rw [Rat.natCast_add]; grind
          rw [hcast]
          exact hsum_lt
    exact haux n hn f hall
  exact Rat.not_le.mpr hstrict hsum

/-- Sum of geometric series `(1 - q) * ∑_{j=0}^{n-1} q^j = 1 - q^n`. -/
theorem finSum_geom_mul (q : Rat) (n : Nat) :
    finSum (fun j : Fin n => ratPow q j.val) * (1 - q) = 1 - ratPow q n := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux, ratPow]; grind
  | succ k ih =>
    simp only [finSumAux]
    have h : (finSumAux k (fun j => ratPow q j.val) + ratPow q k) * (1 - q) =
        finSumAux k (fun j => ratPow q j.val) * (1 - q) + ratPow q k * (1 - q) := by grind
    rw [h, ih, ratPow]
    grind

/-- Double sum swap over `Fin m × Fin n`. -/
theorem finSum_swap {m n : Nat} (f : Fin m → Fin n → Rat) :
    finSum (fun i : Fin m => finSum (fun j : Fin n => f i j)) =
      finSum (fun j : Fin n => finSum (fun i : Fin m => f i j)) := by
  unfold finSum
  induction m with
  | zero =>
    simp only [finSumAux]
    have hz : finSumAux n (fun _ : Fin n => (0 : Rat)) = 0 := finSum_zero n
    exact hz.symm
  | succ k ih =>
    simp only [finSumAux]
    rw [ih (fun i j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j)]
    have hadd := finSum_add
      (fun j : Fin n => finSumAux k (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j))
      (fun j : Fin n => f ⟨k, Nat.lt_succ_self k⟩ j)
    unfold finSum at hadd
    exact hadd.symm

end Mrope3dCoprime
