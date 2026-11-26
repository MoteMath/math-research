/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrpoK3Kl.Defs

/-!
# Pure-`Init` `Rat` Order, Absolute Value, Dyadic Power, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace GrpoK3Kl

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

theorem rat_mul_nonneg_sq (a : Rat) : (0 : Rat) ≤ a * a := by
  cases Rat.le_total (a := (0 : Rat)) (b := a) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hn : (0 : Rat) ≤ -a := rat_neg_nonneg_of_nonpos h
    have hmul : (0 : Rat) ≤ (-a) * (-a) := Rat.mul_nonneg hn hn
    have heq : (-a) * (-a) = a * a := by grind
    rw [← heq]; exact hmul

theorem rat_mul_pos_sq {a : Rat} (ha : a ≠ 0) : (0 : Rat) < a * a := by
  have h1 : (0 : Rat) ≤ a * a := rat_mul_nonneg_sq a
  have hne : a * a ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact ha h
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
  have h2 : a ≤ a + b := by
    have := rat_add_le_add (Rat.le_refl (a := a)) hb
    have h0 : a + 0 = a := by grind
    rw [h0] at this; exact this
  exact rat_lt_of_lt_of_le ha h2

theorem rat_add_pos_of_nonneg_of_pos {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a + b := by
  rw [Rat.add_comm]
  exact rat_add_pos_of_pos_of_nonneg hb ha

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < a⁻¹ := by
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  have h1 : (0 : Rat) < a⁻¹ * a := by
    rw [Rat.inv_mul_cancel a hne]
    decide
  cases Rat.le_total (a := (0 : Rat)) (b := a⁻¹) with
  | inl hle =>
    have hinv_ne : a⁻¹ ≠ 0 := by
      intro h0
      rw [h0, Rat.zero_mul] at h1
      exact Rat.not_le.mpr h1 Rat.le_refl
    exact Rat.lt_of_le_of_ne hle (Ne.symm hinv_ne)
  | inr hge =>
    have hle0 : a⁻¹ * a ≤ 0 := by
      have h := rat_mul_le_mul_of_nonneg_right hge (Rat.le_of_lt ha)
      rw [Rat.zero_mul] at h
      exact h
    exact False.elim (Rat.not_le.mpr h1 hle0)

theorem rat_mul_inv {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have hab : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact hb h
  calc
    (a * b)⁻¹ = (a * b)⁻¹ * 1 := by rw [Rat.mul_one]
    _ = (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) := by
      have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
        calc
          (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by grind
          _ = a * 1 * a⁻¹ := by rw [Rat.mul_inv_cancel b hb]
          _ = a * a⁻¹ := by grind
          _ = 1 := Rat.mul_inv_cancel a ha
      rw [h1]
    _ = ((a * b)⁻¹ * (a * b)) * (b⁻¹ * a⁻¹) := by grind
    _ = 1 * (b⁻¹ * a⁻¹) := by rw [Rat.inv_mul_cancel _ hab]
    _ = b⁻¹ * a⁻¹ := by rw [Rat.one_mul]

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_le_div_of_pos {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) < c) :
    a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))

theorem rat_div_le_div {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  have hbd : (0 : Rat) < b * d := rat_mul_pos hb hd
  have hdiv := rat_div_le_div_of_pos h hbd
  have hb_ne : b ≠ 0 := Rat.ne_of_gt hb
  have hd_ne : d ≠ 0 := Rat.ne_of_gt hd
  rw [Rat.div_def, Rat.div_def, rat_mul_inv hb_ne hd_ne] at hdiv
  have hL : a * d * (d⁻¹ * b⁻¹) = a / b := by
    rw [Rat.div_def]
    calc
      a * d * (d⁻¹ * b⁻¹) = a * (d * d⁻¹) * b⁻¹ := by grind
      _ = a * 1 * b⁻¹ := by rw [Rat.mul_inv_cancel d hd_ne]
      _ = a * b⁻¹ := by grind
  have hR : c * b * (d⁻¹ * b⁻¹) = c / d := by
    rw [Rat.div_def]
    calc
      c * b * (d⁻¹ * b⁻¹) = c * (b * b⁻¹) * d⁻¹ := by grind
      _ = c * 1 * d⁻¹ := by rw [Rat.mul_inv_cancel b hb_ne]
      _ = c * d⁻¹ := by grind
  rw [hL, hR] at hdiv
  exact hdiv

theorem rat_div_lt_div {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d)
    (h : a * d < c * b) : a / b < c / d := by
  have hbd : (0 : Rat) < b * d := rat_mul_pos hb hd
  have hdiv : (a * d) / (b * d) < (c * b) / (b * d) := by
    rw [Rat.div_def, Rat.div_def]
    exact rat_mul_lt_mul_of_pos_right h (rat_inv_pos hbd)
  have hb_ne : b ≠ 0 := Rat.ne_of_gt hb
  have hd_ne : d ≠ 0 := Rat.ne_of_gt hd
  rw [Rat.div_def, Rat.div_def, rat_mul_inv hb_ne hd_ne] at hdiv
  have hL : a * d * (d⁻¹ * b⁻¹) = a / b := by
    rw [Rat.div_def]
    calc
      a * d * (d⁻¹ * b⁻¹) = a * (d * d⁻¹) * b⁻¹ := by grind
      _ = a * 1 * b⁻¹ := by rw [Rat.mul_inv_cancel d hd_ne]
      _ = a * b⁻¹ := by grind
  have hR : c * b * (d⁻¹ * b⁻¹) = c / d := by
    rw [Rat.div_def]
    calc
      c * b * (d⁻¹ * b⁻¹) = c * (b * b⁻¹) * d⁻¹ := by grind
      _ = c * 1 * d⁻¹ := by rw [Rat.mul_inv_cancel b hb_ne]
      _ = c * d⁻¹ := by grind
  rw [hL, hR] at hdiv
  exact hdiv

theorem rat_inv_le_inv_of_pos {a b : Rat} (ha : (0 : Rat) < a) (hab : a ≤ b) :
    b⁻¹ ≤ a⁻¹ := by
  have hb : (0 : Rat) < b := rat_lt_of_lt_of_le ha hab
  have hne_a : a ≠ 0 := Rat.ne_of_gt ha
  have hne_b : b ≠ 0 := Rat.ne_of_gt hb
  have h1 : a * (a⁻¹ * b⁻¹) ≤ b * (a⁻¹ * b⁻¹) :=
    rat_mul_le_mul_of_nonneg_right hab (Rat.le_of_lt (rat_mul_pos (rat_inv_pos ha) (rat_inv_pos hb)))
  have hl : a * (a⁻¹ * b⁻¹) = b⁻¹ := by
    rw [← Rat.mul_assoc, Rat.mul_inv_cancel a hne_a, Rat.one_mul]
  have hr : b * (a⁻¹ * b⁻¹) = a⁻¹ := by
    rw [Rat.mul_comm a⁻¹ b⁻¹, ← Rat.mul_assoc, Rat.mul_inv_cancel b hne_b, Rat.one_mul]
  rw [hl, hr] at h1
  exact h1

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by simp [Rat.natCast_add]
    rw [h1]
    exact rat_add_nonneg ih (by decide)

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  cases n with
  | zero => exact absurd hn (by decide)
  | succ k =>
    have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by simp [Rat.natCast_add]
    rw [h1]
    exact rat_add_pos_of_nonneg_of_pos (rat_natCast_nonneg k) (by decide)

theorem rat_natCast_le {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have hdiff : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  rw [hdiff, Rat.natCast_add]
  have this := rat_add_le_add (Rat.le_refl (a := (a : Rat))) (rat_natCast_nonneg (b - a))
  have h0' : (a : Rat) + 0 = (a : Rat) := by grind
  rw [h0'] at this
  exact this

theorem pow2Rat_pos (k : Nat) : (0 : Rat) < pow2Rat k := by
  unfold pow2Rat
  exact rat_natCast_pos (Nat.two_pow_pos k)

theorem pow2Rat_ne_zero (k : Nat) : pow2Rat k ≠ 0 :=
  Rat.ne_of_gt (pow2Rat_pos k)

theorem pow2Rat_succ (k : Nat) : pow2Rat (k + 1) = 2 * pow2Rat k := by
  unfold pow2Rat
  have h : (2 ^ (k + 1) : Nat) = 2 * 2 ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [h, Rat.natCast_mul]
  rfl

theorem pow2Rat_mono {a b : Nat} (h : a ≤ b) : pow2Rat a ≤ pow2Rat b := by
  unfold pow2Rat
  exact rat_natCast_le (Nat.pow_le_pow_right (by decide) h)

theorem invPow2Rat_pos (k : Nat) : (0 : Rat) < invPow2Rat k := by
  unfold invPow2Rat
  exact rat_div_pos (by decide) (pow2Rat_pos k)

theorem invPow2Rat_succ (k : Nat) : invPow2Rat (k + 1) * 2 = invPow2Rat k := by
  unfold invPow2Rat
  rw [pow2Rat_succ]
  have hp : pow2Rat k ≠ 0 := pow2Rat_ne_zero k
  have h2 : (2 : Rat) ≠ 0 := by decide
  rw [Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul, rat_mul_inv h2 hp]
  calc
    ((pow2Rat k)⁻¹ * (2 : Rat)⁻¹) * 2 = (pow2Rat k)⁻¹ * ((2 : Rat)⁻¹ * 2) := by
      rw [Rat.mul_assoc]
    _ = (pow2Rat k)⁻¹ * 1 := by rw [Rat.inv_mul_cancel _ h2]
    _ = (pow2Rat k)⁻¹ := by rw [Rat.mul_one]

theorem invPow2Rat_succ_eq (k : Nat) : invPow2Rat (k + 1) = invPow2Rat k / 2 := by
  have h := invPow2Rat_succ k
  rw [Rat.div_def]
  have h2 : (2 : Rat) ≠ 0 := by decide
  calc
    invPow2Rat (k + 1) = (invPow2Rat (k + 1) * 2) * (2 : Rat)⁻¹ := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ h2, Rat.mul_one]
    _ = invPow2Rat k * (2 : Rat)⁻¹ := by rw [h]

theorem ratAbs_nonneg (x : Rat) : (0 : Rat) ≤ ratAbs x := by
  unfold ratAbs
  split
  · assumption
  · rename_i h
    have hlt : x < 0 := Rat.not_le.mp h
    exact rat_neg_nonneg_of_nonpos (Rat.le_of_lt hlt)

theorem ratAbs_of_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) : ratAbs x = x := by
  unfold ratAbs; simp [hx]

theorem ratAbs_of_nonpos {x : Rat} (hx : x ≤ 0) : ratAbs x = -x := by
  unfold ratAbs
  split
  · rename_i h
    have hx0 : x = 0 := Rat.le_antisymm hx h
    rw [hx0]; decide
  · rfl

theorem ratAbs_neg (x : Rat) : ratAbs (-x) = ratAbs x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h =>
    have hnx : -x ≤ 0 := by
      apply rat_le_of_sub_nonneg
      have eq : (0 : Rat) - (-x) = x := by grind
      rw [eq]; exact h
    rw [ratAbs_of_nonneg h, ratAbs_of_nonpos hnx]
    grind
  | inr h =>
    have hnx : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
    rw [ratAbs_of_nonpos h, ratAbs_of_nonneg hnx]

theorem ratAbs_le_iff {x b : Rat} : ratAbs x ≤ b ↔ (-b ≤ x ∧ x ≤ b) := by
  constructor
  · intro h
    cases Rat.le_total (a := (0 : Rat)) (b := x) with
    | inl hx =>
      rw [ratAbs_of_nonneg hx] at h
      have hb : (0 : Rat) ≤ b := Rat.le_trans hx h
      have hnb : -b ≤ 0 := by
        apply rat_le_of_sub_nonneg
        have eq : (0 : Rat) - (-b) = b := by grind
        rw [eq]; exact hb
      exact ⟨Rat.le_trans hnb hx, h⟩
    | inr hx =>
      rw [ratAbs_of_nonpos hx] at h
      have hnb : -b ≤ x := by
        apply rat_le_of_sub_nonneg
        have h1 := rat_sub_nonneg h
        have eq : x - (-b) = b - (-x) := by grind
        rw [eq]; exact h1
      have hb : (0 : Rat) ≤ b := Rat.le_trans (rat_neg_nonneg_of_nonpos hx) h
      exact ⟨hnb, Rat.le_trans hx hb⟩
  · rintro ⟨h1, h2⟩
    cases Rat.le_total (a := (0 : Rat)) (b := x) with
    | inl hx =>
      rw [ratAbs_of_nonneg hx]; exact h2
    | inr hx =>
      rw [ratAbs_of_nonpos hx]
      apply rat_le_of_sub_nonneg
      have hsub := rat_sub_nonneg h1
      have eq : b - (-x) = x - (-b) := by grind
      rw [eq]; exact hsub

theorem ratAbs_add_le (a b : Rat) : ratAbs (a + b) ≤ ratAbs a + ratAbs b := by
  rw [ratAbs_le_iff]
  have ha := ratAbs_le_iff.mp (Rat.le_refl (a := ratAbs a))
  have hb := ratAbs_le_iff.mp (Rat.le_refl (a := ratAbs b))
  constructor
  · have h := rat_add_le_add ha.1 hb.1
    have eq : -(ratAbs a + ratAbs b) = -ratAbs a + -ratAbs b := by grind
    rw [eq]; exact h
  · exact rat_add_le_add ha.2 hb.2

theorem ratAbs_mul (a b : Rat) : ratAbs (a * b) = ratAbs a * ratAbs b := by
  cases Rat.le_total (a := (0 : Rat)) (b := a) with
  | inl ha =>
    cases Rat.le_total (a := (0 : Rat)) (b := b) with
    | inl hb =>
      rw [ratAbs_of_nonneg ha, ratAbs_of_nonneg hb, ratAbs_of_nonneg (Rat.mul_nonneg ha hb)]
    | inr hb =>
      have hnb : (0 : Rat) ≤ -b := rat_neg_nonneg_of_nonpos hb
      have hab : a * b ≤ 0 := by
        apply rat_le_of_sub_nonneg
        have eq : (0 : Rat) - a * b = a * (-b) := by grind
        rw [eq]; exact Rat.mul_nonneg ha hnb
      rw [ratAbs_of_nonneg ha, ratAbs_of_nonpos hb, ratAbs_of_nonpos hab]
      grind
  | inr ha =>
    have hna : (0 : Rat) ≤ -a := rat_neg_nonneg_of_nonpos ha
    cases Rat.le_total (a := (0 : Rat)) (b := b) with
    | inl hb =>
      have hab : a * b ≤ 0 := by
        apply rat_le_of_sub_nonneg
        have eq : (0 : Rat) - a * b = (-a) * b := by grind
        rw [eq]; exact Rat.mul_nonneg hna hb
      rw [ratAbs_of_nonpos ha, ratAbs_of_nonneg hb, ratAbs_of_nonpos hab]
      grind
    | inr hb =>
      have hnb : (0 : Rat) ≤ -b := rat_neg_nonneg_of_nonpos hb
      have hab : (0 : Rat) ≤ a * b := by
        have eq : a * b = (-a) * (-b) := by grind
        rw [eq]; exact Rat.mul_nonneg hna hnb
      rw [ratAbs_of_nonpos ha, ratAbs_of_nonpos hb, ratAbs_of_nonneg hab]
      grind

end GrpoK3Kl
