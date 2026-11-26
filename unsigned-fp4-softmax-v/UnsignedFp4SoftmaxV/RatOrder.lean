/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnsignedFp4SoftmaxV.Defs

/-!
# Pure-`Init` `Rat` Order, Field, and Finite-Sum Helpers

Zero Mathlib, zero `native_decide`. Elementary `Rat` arithmetic, order, absolute-value,
`max`, and `sumFin` linearity lemmas used across all six headline theorems.
-/

namespace UnsignedFp4SoftmaxV

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
  rw [eq]
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
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]
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
    have hneg : (0 : Rat) ≤ -x := by
      have := rat_sub_nonneg h
      grind
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

theorem rat_div_eq_of_cross {a b c d : Rat} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : a / b = c / d := by
  have h1 : (a / b) * (b * d) = a * d := by
    rw [Rat.div_def, Rat.mul_assoc a b⁻¹, ← Rat.mul_assoc b⁻¹ b d,
        Rat.inv_mul_cancel b hb, Rat.one_mul]
  have h2 : (c / d) * (b * d) = c * b := by
    rw [Rat.div_def, Rat.mul_comm b d, Rat.mul_assoc c d⁻¹, ← Rat.mul_assoc d⁻¹ d b,
        Rat.inv_mul_cancel d hd, Rat.one_mul]
  have hmul : ((a / b) - (c / d)) * (b * d) = 0 := by grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h0 => grind
  | inr hbd =>
    cases Rat.mul_eq_zero.mp hbd with
    | inl hb0 => exact False.elim (hb hb0)
    | inr hd0 => exact False.elim (hd hd0)

theorem rat_div_le_div_of_cross {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  have hbd : (0 : Rat) < b * d := rat_mul_pos hb hd
  apply rat_le_of_mul_pos_right hbd
  have h1 : (a / b) * (b * d) = a * d := by
    rw [Rat.div_def, Rat.mul_assoc a b⁻¹, ← Rat.mul_assoc b⁻¹ b d,
        Rat.inv_mul_cancel b hbne, Rat.one_mul]
  have h2 : (c / d) * (b * d) = c * b := by
    rw [Rat.div_def, Rat.mul_comm b d, Rat.mul_assoc c d⁻¹, ← Rat.mul_assoc d⁻¹ d b,
        Rat.inv_mul_cancel d hdne, Rat.one_mul]
  rw [h1, h2]
  exact h

theorem rat_div_lt_div_of_cross {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d)
    (h : a * d < c * b) : a / b < c / d := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  have hbd : (0 : Rat) < b * d := rat_mul_pos hb hd
  apply rat_lt_of_mul_pos_right hbd
  have h1 : (a / b) * (b * d) = a * d := by
    rw [Rat.div_def, Rat.mul_assoc a b⁻¹, ← Rat.mul_assoc b⁻¹ b d,
        Rat.inv_mul_cancel b hbne, Rat.one_mul]
  have h2 : (c / d) * (b * d) = c * b := by
    rw [Rat.div_def, Rat.mul_comm b d, Rat.mul_assoc c d⁻¹, ← Rat.mul_assoc d⁻¹ d b,
        Rat.inv_mul_cancel d hdne, Rat.one_mul]
  rw [h1, h2]
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

theorem rat_max_eq_left {a b : Rat} (h : b ≤ a) : max a b = a := by
  simp only [max, Max.max]
  split
  · rename_i hle
    exact Rat.le_antisymm h hle
  · rfl

theorem rat_max_eq_right {a b : Rat} (h : a ≤ b) : max a b = b := by
  simp only [max, Max.max]
  split
  · rfl
  · rename_i hnot
    exact False.elim (hnot h)

theorem rat_le_max_left (a b : Rat) : a ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact h
  | inr h => rw [rat_max_eq_left h]; exact Rat.le_refl

theorem rat_le_max_right (a b : Rat) : b ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact Rat.le_refl
  | inr h => rw [rat_max_eq_left h]; exact h

theorem rat_max_le {a b c : Rat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact hb
  | inr h => rw [rat_max_eq_left h]; exact ha

theorem ratAbs_nonneg (x : Rat) : (0 : Rat) ≤ ratAbs x := by
  unfold ratAbs
  split
  · assumption
  · rename_i hnot
    have hlt : x < 0 := Rat.not_le.mp hnot
    have hsub : (0 : Rat) < 0 - x := rat_sub_pos hlt
    have eq : -x = 0 - x := by grind
    rw [eq]; exact Rat.le_of_lt hsub

theorem ratAbs_of_nonneg {x : Rat} (h : (0 : Rat) ≤ x) : ratAbs x = x := by
  unfold ratAbs; simp [h]

theorem ratAbs_neg (x : Rat) : ratAbs (-x) = ratAbs x := by
  unfold ratAbs
  by_cases h : (0 : Rat) ≤ x
  · by_cases h0 : x = 0
    · subst h0; decide
    · have hpos : (0 : Rat) < x := Rat.lt_of_le_of_ne h (Ne.symm h0)
      have hneg : ¬((0 : Rat) ≤ -x) := by
        intro hle
        have : (0 : Rat) ≤ -x + x := rat_add_nonneg hle (Rat.le_of_lt hpos)
        have hlt : -x < 0 := by
          apply rat_lt_of_sub_pos
          have eq : (0 : Rat) - (-x) = x := by grind
          rw [eq]; exact hpos
        exact Rat.not_le.mpr hlt hle
      simp [h, hneg]
  · have hlt : x < 0 := Rat.not_le.mp h
    have hpos : (0 : Rat) ≤ -x := by
      have hsub : (0 : Rat) < 0 - x := rat_sub_pos hlt
      have eq : -x = 0 - x := by grind
      rw [eq]; exact Rat.le_of_lt hsub
    simp [h, hpos]

theorem ratAbs_le_of_bounds {x b : Rat} (h1 : -b ≤ x) (h2 : x ≤ b) : ratAbs x ≤ b := by
  unfold ratAbs
  split
  · exact h2
  · have h3 : (0 : Rat) ≤ x - (-b) := rat_sub_nonneg h1
    apply rat_le_of_sub_nonneg
    have eq : b - (-x) = x - (-b) := by grind
    rw [eq]; exact h3

theorem rat_le_ratAbs (x : Rat) : x ≤ ratAbs x := by
  unfold ratAbs
  split
  · exact Rat.le_refl
  · rename_i hnot
    have hlt : x < 0 := Rat.not_le.mp hnot
    have hpos : (0 : Rat) < -x := by
      have hsub := rat_sub_pos hlt
      have eq : -x = 0 - x := by grind
      rw [eq]; exact hsub
    exact Rat.le_of_lt (rat_lt_of_lt_of_le hlt (Rat.le_of_lt hpos))

theorem rat_neg_le_ratAbs (x : Rat) : -x ≤ ratAbs x := by
  rw [← ratAbs_neg x]
  exact rat_le_ratAbs (-x)

theorem ratAbs_add_le (x y : Rat) : ratAbs (x + y) ≤ ratAbs x + ratAbs y := by
  apply ratAbs_le_of_bounds
  · have h1 : -ratAbs x ≤ x := by
      have := rat_neg_le_ratAbs x
      have hsub := rat_sub_nonneg this
      apply rat_le_of_sub_nonneg
      have eq : x - (-ratAbs x) = ratAbs x - (-x) := by grind
      rw [eq]; exact hsub
    have h2 : -ratAbs y ≤ y := by
      have := rat_neg_le_ratAbs y
      have hsub := rat_sub_nonneg this
      apply rat_le_of_sub_nonneg
      have eq : y - (-ratAbs y) = ratAbs y - (-y) := by grind
      rw [eq]; exact hsub
    have h3 := rat_add_le_add h1 h2
    have eq : -(ratAbs x + ratAbs y) = -ratAbs x + -ratAbs y := by grind
    rw [eq]; exact h3
  · exact rat_add_le_add (rat_le_ratAbs x) (rat_le_ratAbs y)

theorem ratAbs_mul_nonneg {c x : Rat} (hc : (0 : Rat) ≤ c) :
    ratAbs (c * x) = c * ratAbs x := by
  by_cases hx : (0 : Rat) ≤ x
  · rw [ratAbs_of_nonneg (Rat.mul_nonneg hc hx), ratAbs_of_nonneg hx]
  · have hlt : x < 0 := Rat.not_le.mp hx
    have hnegx : (0 : Rat) ≤ -x := by
      have hsub := rat_sub_pos hlt
      have eq : -x = 0 - x := by grind
      rw [eq]; exact Rat.le_of_lt hsub
    have hprod : (0 : Rat) ≤ c * (-x) := Rat.mul_nonneg hc hnegx
    have h1 : ratAbs (c * x) = ratAbs (-(c * x)) := (ratAbs_neg (c * x)).symm
    have eq1 : -(c * x) = c * (-x) := by grind
    rw [h1, eq1, ratAbs_of_nonneg hprod]
    unfold ratAbs
    simp [hx]

/-! ### Finite-Sum (`sumFin`) Linearity and Order Lemmas -/

theorem sumFin_add {n : Nat} (f g : Fin n → Rat) :
    sumFin (fun j => f j + g j) = sumFin f + sumFin g := by
  induction n with
  | zero => simp [sumFin]; grind
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem sumFin_sub {n : Nat} (f g : Fin n → Rat) :
    sumFin (fun j => f j - g j) = sumFin f - sumFin g := by
  induction n with
  | zero => simp [sumFin]; grind
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem sumFin_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumFin (fun j => f j * c) = sumFin f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem sumFin_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumFin (fun j => c * f j) = c * sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem sumFin_const {n : Nat} (c : Rat) :
    sumFin (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin]
    rw [ih, Rat.natCast_add]
    grind

theorem sumFin_le_sumFin {n : Nat} {f g : Fin n → Rat} (h : ∀ j : Fin n, f j ≤ g j) :
    sumFin f ≤ sumFin g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [sumFin]
    exact rat_add_le_add (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem ratAbs_sumFin_le {n : Nat} (f : Fin n → Rat) :
    ratAbs (sumFin f) ≤ sumFin (fun j => ratAbs (f j)) := by
  induction n with
  | zero =>
    simp only [sumFin]
    rw [ratAbs_of_nonneg Rat.le_refl]
    exact Rat.le_refl
  | succ n ih =>
    simp only [sumFin]
    have h1 := ratAbs_add_le (sumFin (fun i : Fin n => f i.castSucc)) (f (Fin.last n))
    have h2 := ih (fun i : Fin n => f i.castSucc)
    exact Rat.le_trans h1 (rat_add_le_add h2 Rat.le_refl)

theorem sumFinNat_cast {n : Nat} (f : Fin n → Nat) :
    ((sumFinNat f : Nat) : Rat) = sumFin (fun j => (f j : Rat)) := by
  induction n with
  | zero => simp [sumFinNat, sumFin]
  | succ n ih =>
    simp only [sumFinNat, sumFin, Rat.natCast_add]
    rw [ih (fun i => f i.castSucc)]

end UnsignedFp4SoftmaxV
