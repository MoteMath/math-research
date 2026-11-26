/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RingAttnKulisch.Defs

/-!
# Pure-`Init` `Rat` Order, Dyadic Power, and Exact RNE Rounding Lemmas

Zero Mathlib, zero `native_decide`. Provides elementary `Rat` order/field helpers,
exact power-of-two rational identities, and exact characterization lemmas for `rneInt`
and `rneGrid`.
-/

namespace RingAttnKulisch

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have hle : a ≤ c := Rat.le_trans (Rat.le_of_lt h1) h2
  have hne : a ≠ c := by
    intro heq
    rw [heq] at h1
    exact Rat.not_le.mpr h1 h2
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := (Rat.add_le_add_right (c := -b)).mpr h
  grind

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := (Rat.add_le_add_right (c := b)).mpr h
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

theorem rat_add_lt_add_left {a b c : Rat} (h : a < b) : c + a < c + b := by
  apply rat_lt_of_sub_pos
  have eq : (c + b) - (c + a) = b - a := by grind
  rw [eq]
  exact rat_sub_pos h

theorem rat_add_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a + b := by
  have h1 : (0 : Rat) ≤ a + b := by
    have := rat_add_le_add (Rat.le_of_lt ha) (Rat.le_of_lt hb)
    have h0 : (0 : Rat) + 0 = 0 := by grind
    rw [h0] at this
    exact this
  have hne : a + b ≠ 0 := by
    intro h0
    have hlt : a + 0 < a + b := rat_add_lt_add_left hb
    have ha0 : a + 0 = a := by grind
    rw [ha0, h0] at hlt
    exact Rat.not_lt.mpr (Rat.le_of_lt ha) hlt
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < 1 / a := by
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  cases Rat.le_total (a := (1 / a : Rat)) (b := (0 : Rat)) with
  | inl hle =>
    have hmul : (1 / a) * a ≤ 0 * a := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt ha)
    have h1 : (1 / a) * a = 1 := by
      rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel a hne]
    have h0 : (0 : Rat) * a = 0 := by grind
    rw [h1, h0] at hmul
    exact absurd hmul (by decide)
  | inr hge =>
    have hne1 : 1 / a ≠ 0 := by
      intro h0
      have h1 : (1 / a) * a = 1 := by
        rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel a hne]
      rw [h0] at h1
      have h0a : (0 : Rat) * a = 0 := by grind
      rw [h0a] at h1
      exact absurd h1 (by decide)
    exact Rat.lt_of_le_of_ne hge (Ne.symm hne1)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  have h : a / b = a * (1 / b) := by
    rw [Rat.div_def, Rat.div_def, Rat.one_mul]
  rw [h]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  have : (0 : Int) < (n : Int) := by omega
  exact Rat.intCast_lt_intCast.mpr this

theorem rat_natCast_le {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have : (a : Int) ≤ (b : Int) := by omega
  exact Rat.intCast_le_intCast.mpr this

theorem rat_natCast_lt {a b : Nat} (h : a < b) : (a : Rat) < (b : Rat) := by
  have : (a : Int) < (b : Int) := by omega
  exact Rat.intCast_lt_intCast.mpr this

theorem rat_intCast_le {a b : Int} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) :=
  Rat.intCast_le_intCast.mpr h

theorem rat_intCast_lt {a b : Int} (h : a < b) : (a : Rat) < (b : Rat) :=
  Rat.intCast_lt_intCast.mpr h

/-! ### Dyadic Power-of-Two Identities -/

theorem pow2_pos_nat (n : Nat) : 0 < 2 ^ n :=
  Nat.pow_pos (by omega)

theorem pow2Rat_pos (n : Nat) : (0 : Rat) < pow2Rat n := by
  unfold pow2Rat
  exact rat_natCast_pos (pow2_pos_nat n)

theorem pow2Rat_ne_zero (n : Nat) : pow2Rat n ≠ 0 :=
  Rat.ne_of_gt (pow2Rat_pos n)

theorem invPow2Rat_pos (n : Nat) : (0 : Rat) < invPow2Rat n := by
  unfold invPow2Rat
  exact rat_inv_pos (rat_natCast_pos (pow2_pos_nat n))

theorem invPow2Rat_eq_div (n : Nat) : invPow2Rat n = 1 / pow2Rat n := rfl

theorem pow2Rat_mul_invPow2Rat (n : Nat) : pow2Rat n * invPow2Rat n = 1 := by
  rw [invPow2Rat_eq_div, Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (pow2Rat_ne_zero n)]

theorem invPow2Rat_mul_pow2Rat (n : Nat) : invPow2Rat n * pow2Rat n = 1 := by
  rw [Rat.mul_comm, pow2Rat_mul_invPow2Rat]

theorem pow2Rat_add (a b : Nat) : pow2Rat (a + b) = pow2Rat a * pow2Rat b := by
  unfold pow2Rat
  rw [Nat.pow_add, Rat.natCast_mul]

theorem pow2Rat_succ (n : Nat) : pow2Rat (n + 1) = 2 * pow2Rat n := by
  have h : pow2Rat (n + 1) = pow2Rat n * pow2Rat 1 := pow2Rat_add n 1
  rw [h]
  unfold pow2Rat
  grind

theorem invPow2Rat_add (a b : Nat) : invPow2Rat (a + b) = invPow2Rat a * invPow2Rat b := by
  rw [invPow2Rat_eq_div, invPow2Rat_eq_div, invPow2Rat_eq_div, pow2Rat_add]
  have ha : pow2Rat a ≠ 0 := pow2Rat_ne_zero a
  have hb : pow2Rat b ≠ 0 := pow2Rat_ne_zero b
  have hab : pow2Rat a * pow2Rat b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact hb h
  have hmul : (1 / (pow2Rat a * pow2Rat b)) * (pow2Rat a * pow2Rat b) =
      ((1 / pow2Rat a) * (1 / pow2Rat b)) * (pow2Rat a * pow2Rat b) := by
    rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel _ hab]
    have h1 : (1 / pow2Rat a) * pow2Rat a = 1 := by
      rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel _ ha]
    have h2 : (1 / pow2Rat b) * pow2Rat b = 1 := by
      rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel _ hb]
    have rearr : ((1 / pow2Rat a) * (1 / pow2Rat b)) * (pow2Rat a * pow2Rat b) =
        ((1 / pow2Rat a) * pow2Rat a) * ((1 / pow2Rat b) * pow2Rat b) := by grind
    rw [rearr, h1, h2]
    grind
  have hcancel : ∀ x y z : Rat, z ≠ 0 → x * z = y * z → x = y := by
    intro x y z hz hxy
    have := congrArg (· * z⁻¹) hxy
    simp only [Rat.mul_assoc, Rat.mul_inv_cancel z hz, Rat.mul_one] at this
    exact this
  exact hcancel _ _ _ hab hmul

theorem invPow2Rat_mul_pow2Rat_of_le {a b : Nat} (h : a ≤ b) :
    invPow2Rat a * pow2Rat b = pow2Rat (b - a) := by
  have hb : b = a + (b - a) := by omega
  have h1 : invPow2Rat a * pow2Rat b = invPow2Rat a * (pow2Rat a * pow2Rat (b - a)) := by
    rw [← pow2Rat_add, ← hb]
  rw [h1, ← Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.one_mul]

theorem invPow2Rat_mul_pow2Rat_of_ge {a b : Nat} (h : b ≤ a) :
    invPow2Rat a * pow2Rat b = invPow2Rat (a - b) := by
  have ha : a = b + (a - b) := by omega
  have h1 : invPow2Rat a * pow2Rat b = (invPow2Rat b * invPow2Rat (a - b)) * pow2Rat b := by
    rw [← invPow2Rat_add, ← ha]
  rw [h1]
  have rearr : invPow2Rat b * invPow2Rat (a - b) * pow2Rat b =
      (invPow2Rat b * pow2Rat b) * invPow2Rat (a - b) := by grind
  rw [rearr, invPow2Rat_mul_pow2Rat, Rat.one_mul]

theorem pow2Rat_mul_invPow2Rat_of_le {a b : Nat} (h : a ≤ b) :
    pow2Rat a * invPow2Rat b = invPow2Rat (b - a) := by
  rw [Rat.mul_comm]
  exact invPow2Rat_mul_pow2Rat_of_ge h

theorem pow2Rat_mul_invPow2Rat_of_ge {a b : Nat} (h : b ≤ a) :
    pow2Rat a * invPow2Rat b = pow2Rat (a - b) := by
  rw [Rat.mul_comm]
  exact invPow2Rat_mul_pow2Rat_of_le h

theorem invPow2Rat_le_invPow2Rat {a b : Nat} (h : a ≤ b) :
    invPow2Rat b ≤ invPow2Rat a := by
  have hpow : pow2Rat a ≤ pow2Rat b := by
    unfold pow2Rat
    exact rat_natCast_le (Nat.pow_le_pow_right (by omega) h)
  have hmul : pow2Rat a * (invPow2Rat a * invPow2Rat b) ≤
      pow2Rat b * (invPow2Rat a * invPow2Rat b) :=
    rat_mul_le_mul_of_nonneg_right hpow (Rat.le_of_lt (rat_mul_pos (invPow2Rat_pos a) (invPow2Rat_pos b)))
  have lhs : pow2Rat a * (invPow2Rat a * invPow2Rat b) = invPow2Rat b := by
    rw [← Rat.mul_assoc, pow2Rat_mul_invPow2Rat, Rat.one_mul]
  have rhs : pow2Rat b * (invPow2Rat a * invPow2Rat b) = invPow2Rat a := by
    have : pow2Rat b * (invPow2Rat a * invPow2Rat b) = (pow2Rat b * invPow2Rat b) * invPow2Rat a := by grind
    rw [this, pow2Rat_mul_invPow2Rat, Rat.one_mul]
  rw [lhs, rhs] at hmul
  exact hmul

theorem invPow2Rat_lt_invPow2Rat {a b : Nat} (h : a < b) :
    invPow2Rat b < invPow2Rat a := by
  have hpow : pow2Rat a < pow2Rat b := by
    unfold pow2Rat
    exact rat_natCast_lt (Nat.pow_lt_pow_right (by omega) h)
  have hmul : pow2Rat a * (invPow2Rat a * invPow2Rat b) <
      pow2Rat b * (invPow2Rat a * invPow2Rat b) :=
    rat_mul_lt_mul_of_pos_right hpow (rat_mul_pos (invPow2Rat_pos a) (invPow2Rat_pos b))
  have lhs : pow2Rat a * (invPow2Rat a * invPow2Rat b) = invPow2Rat b := by
    rw [← Rat.mul_assoc, pow2Rat_mul_invPow2Rat, Rat.one_mul]
  have rhs : pow2Rat b * (invPow2Rat a * invPow2Rat b) = invPow2Rat a := by
    have : pow2Rat b * (invPow2Rat a * invPow2Rat b) = (pow2Rat b * invPow2Rat b) * invPow2Rat a := by grind
    rw [this, pow2Rat_mul_invPow2Rat, Rat.one_mul]
  rw [lhs, rhs] at hmul
  exact hmul

/-! ### Exact `Rat.le_iff` and Integer Division Bridge for `rneInt` -/

theorem rat_int_le_iff (n : Int) (y : Rat) :
    (n : Rat) ≤ y ↔ n * (y.den : Int) ≤ y.num := by
  rw [Rat.le_iff]
  have hnum : ((n : Rat)).num = n := rfl
  have hden : ((n : Rat)).den = 1 := rfl
  rw [hnum, hden]
  omega

theorem rat_le_int_iff (y : Rat) (n : Int) :
    y ≤ (n : Rat) ↔ y.num ≤ n * (y.den : Int) := by
  rw [Rat.le_iff]
  have hnum : ((n : Rat)).num = n := rfl
  have hden : ((n : Rat)).den = 1 := rfl
  rw [hnum, hden]
  omega

theorem rat_lt_int_iff (y : Rat) (n : Int) :
    y < (n : Rat) ↔ y.num < n * (y.den : Int) := by
  constructor
  · intro h
    have hnot : ¬ ((n : Rat) ≤ y) := Rat.not_le.mpr h
    rw [rat_int_le_iff] at hnot
    omega
  · intro h
    apply Rat.not_le.mp
    rw [rat_int_le_iff]
    omega

theorem rat_mul_den (y : Rat) : y * (y.den : Rat) = (y.num : Rat) := by
  have hdiv : y = (y.num : Rat) / ((y.den : Int) : Rat) := by
    rw [← Rat.divInt_eq_div]
    have h1 : Rat.divInt y.num (y.den : Int) = mkRat y.num y.den := by
      unfold Rat.divInt mkRat
      simp [y.den_nz]
    rw [h1, Rat.mkRat_self]
  have hd_ne : ((y.den : Int) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos (Nat.pos_of_ne_zero y.den_nz))
  have hcast : ((y.den : Nat) : Rat) = ((y.den : Int) : Rat) := rfl
  rw [hcast]
  have h2 : y * ((y.den : Int) : Rat) = ((y.num : Rat) / ((y.den : Int) : Rat)) * ((y.den : Int) : Rat) :=
    congrArg (· * ((y.den : Int) : Rat)) hdiv
  rw [h2, Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hd_ne, Rat.mul_one]

theorem rat_lt_int_add_half_iff (y : Rat) (n : Int) :
    y < (n : Rat) + 1 / 2 ↔ 2 * y.num < (2 * n + 1) * (y.den : Int) := by
  have hd_pos : (0 : Rat) < (y.den : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero y.den_nz)
  have h2d_pos : (0 : Rat) < 2 * (y.den : Rat) := rat_mul_pos (by decide) hd_pos
  have hlhs : y * (2 * (y.den : Rat)) = ((2 * y.num : Int) : Rat) := by
    have : y * (2 * (y.den : Rat)) = 2 * (y * (y.den : Rat)) := by grind
    rw [this, rat_mul_den, Rat.intCast_mul]; rfl
  have hrhs : ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) =
      (((2 * n + 1) * (y.den : Int) : Int) : Rat) := by
    have : ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) = (2 * (n : Rat) + 1) * (y.den : Rat) := by grind
    rw [this, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_mul]; rfl
  constructor
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h h2d_pos
    rw [hlhs, hrhs] at hmul
    exact Rat.intCast_lt_intCast.mp hmul
  · intro h
    have hcast : y * (2 * (y.den : Rat)) < ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) := by
      rw [hlhs, hrhs]
      exact Rat.intCast_lt_intCast.mpr h
    have hinv := rat_mul_lt_mul_of_pos_right hcast (rat_inv_pos h2d_pos)
    have hne : 2 * (y.den : Rat) ≠ 0 := Rat.ne_of_gt h2d_pos
    have h1 : ∀ x : Rat, x * (2 * (y.den : Rat)) * (1 / (2 * (y.den : Rat))) = x := by
      intro x
      rw [Rat.mul_assoc, Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ hne, Rat.mul_one]
    rw [h1 y, h1 ((n : Rat) + 1 / 2)] at hinv
    exact hinv

theorem rat_int_add_half_lt_iff (n : Int) (y : Rat) :
    (n : Rat) + 1 / 2 < y ↔ (2 * n + 1) * (y.den : Int) < 2 * y.num := by
  have hd_pos : (0 : Rat) < (y.den : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero y.den_nz)
  have h2d_pos : (0 : Rat) < 2 * (y.den : Rat) := rat_mul_pos (by decide) hd_pos
  have hlhs : ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) =
      (((2 * n + 1) * (y.den : Int) : Int) : Rat) := by
    have : ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) = (2 * (n : Rat) + 1) * (y.den : Rat) := by grind
    rw [this, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_mul]; rfl
  have hrhs : y * (2 * (y.den : Rat)) = ((2 * y.num : Int) : Rat) := by
    have : y * (2 * (y.den : Rat)) = 2 * (y * (y.den : Rat)) := by grind
    rw [this, rat_mul_den, Rat.intCast_mul]; rfl
  constructor
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h h2d_pos
    rw [hlhs, hrhs] at hmul
    exact Rat.intCast_lt_intCast.mp hmul
  · intro h
    have hcast : ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) < y * (2 * (y.den : Rat)) := by
      rw [hlhs, hrhs]
      exact Rat.intCast_lt_intCast.mpr h
    have hinv := rat_mul_lt_mul_of_pos_right hcast (rat_inv_pos h2d_pos)
    have hne : 2 * (y.den : Rat) ≠ 0 := Rat.ne_of_gt h2d_pos
    have h1 : ∀ x : Rat, x * (2 * (y.den : Rat)) * (1 / (2 * (y.den : Rat))) = x := by
      intro x
      rw [Rat.mul_assoc, Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ hne, Rat.mul_one]
    rw [h1 ((n : Rat) + 1 / 2), h1 y] at hinv
    exact hinv

theorem rat_eq_int_add_half_iff (y : Rat) (n : Int) :
    y = (n : Rat) + 1 / 2 ↔ 2 * y.num = (2 * n + 1) * (y.den : Int) := by
  have hd_pos : (0 : Rat) < (y.den : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero y.den_nz)
  have h2d_ne : 2 * (y.den : Rat) ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) hd_pos)
  have hlhs : y * (2 * (y.den : Rat)) = ((2 * y.num : Int) : Rat) := by
    have : y * (2 * (y.den : Rat)) = 2 * (y * (y.den : Rat)) := by grind
    rw [this, rat_mul_den, Rat.intCast_mul]; rfl
  have hrhs : ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) =
      (((2 * n + 1) * (y.den : Int) : Int) : Rat) := by
    have : ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) = (2 * (n : Rat) + 1) * (y.den : Rat) := by grind
    rw [this, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_mul]; rfl
  constructor
  · intro h
    have hmul := congrArg (· * (2 * (y.den : Rat))) h
    rw [hlhs, hrhs] at hmul
    exact Rat.intCast_inj.mp hmul
  · intro h
    have hcast : y * (2 * (y.den : Rat)) = ((n : Rat) + 1 / 2) * (2 * (y.den : Rat)) := by
      rw [hlhs, hrhs]
      exact congrArg (fun z : Int => (z : Rat)) h
    have h1 := congrArg (· * (2 * (y.den : Rat))⁻¹) hcast
    simp only [Rat.mul_assoc, Rat.mul_inv_cancel _ h2d_ne, Rat.mul_one] at h1
    exact h1

/-! ### Exact Integer Division Uniqueness & `rneInt` Lemmas -/

theorem int_ediv_eq_of_bounds {a d n : Int} (hd : 0 < d)
    (hlo : n * d ≤ a) (hhi : a < (n + 1) * d) :
    a.ediv d = n := by
  have hdiv : d * (a.ediv d) + a.emod d = a := Int.mul_ediv_add_emod a d
  have hrm0 : 0 ≤ a.emod d := Int.emod_nonneg a (by omega)
  have hrm1 : a.emod d < d := Int.emod_lt_of_pos a hd
  by_cases h1 : a.ediv d < n
  · have hle : a.ediv d + 1 ≤ n := by omega
    have hmul : (a.ediv d + 1) * d ≤ n * d := Int.mul_le_mul_of_nonneg_right hle (by omega)
    have hexp : (a.ediv d + 1) * d = d * (a.ediv d) + d := by grind
    omega
  · by_cases h2 : n < a.ediv d
    · have hle : n + 1 ≤ a.ediv d := by omega
      have hmul : (n + 1) * d ≤ (a.ediv d) * d := Int.mul_le_mul_of_nonneg_right hle (by omega)
      have hcomm : (a.ediv d) * d = d * (a.ediv d) := Int.mul_comm _ _
      omega
    · omega

theorem rneInt_of_lt_half {y : Rat} {n : Int}
    (hlo : (n : Rat) ≤ y) (hhi : y < (n : Rat) + 1 / 2) :
    rneInt y = n := by
  have hd : 0 < (y.den : Int) := by have := Nat.pos_of_ne_zero y.den_nz; omega
  have h1 : n * (y.den : Int) ≤ y.num := (rat_int_le_iff n y).mp hlo
  have h2 : 2 * y.num < (2 * n + 1) * (y.den : Int) := (rat_lt_int_add_half_iff y n).mp hhi
  have hhi_int : y.num < (n + 1) * (y.den : Int) := by
    have hexp1 : (2 * n + 1) * (y.den : Int) = 2 * (n * (y.den : Int)) + (y.den : Int) := by grind
    have hexp2 : (n + 1) * (y.den : Int) = n * (y.den : Int) + (y.den : Int) := by grind
    omega
  have hq : y.num.ediv (y.den : Int) = n := int_ediv_eq_of_bounds hd h1 hhi_int
  have hdiv : (y.den : Int) * (y.num.ediv (y.den : Int)) + y.num.emod (y.den : Int) = y.num :=
    Int.mul_ediv_add_emod y.num (y.den : Int)
  rw [hq] at hdiv
  have hr : 2 * y.num.emod (y.den : Int) < (y.den : Int) := by
    have hexp : (2 * n + 1) * (y.den : Int) = 2 * ((y.den : Int) * n) + (y.den : Int) := by grind
    omega
  unfold rneInt
  simp [hq, hr]

theorem rneInt_of_gt_half {y : Rat} {n : Int}
    (hlo : (n : Rat) + 1 / 2 < y) (hhi : y < ((n + 1 : Int) : Rat)) :
    rneInt y = n + 1 := by
  have hd : 0 < (y.den : Int) := by have := Nat.pos_of_ne_zero y.den_nz; omega
  have h1 : (2 * n + 1) * (y.den : Int) < 2 * y.num := (rat_int_add_half_lt_iff n y).mp hlo
  have h2 : y.num < (n + 1) * (y.den : Int) := (rat_lt_int_iff y (n + 1)).mp hhi
  have hlo_int : n * (y.den : Int) ≤ y.num := by
    have hexp : (2 * n + 1) * (y.den : Int) = 2 * (n * (y.den : Int)) + (y.den : Int) := by grind
    omega
  have hq : y.num.ediv (y.den : Int) = n := int_ediv_eq_of_bounds hd hlo_int h2
  have hdiv : (y.den : Int) * (y.num.ediv (y.den : Int)) + y.num.emod (y.den : Int) = y.num :=
    Int.mul_ediv_add_emod y.num (y.den : Int)
  rw [hq] at hdiv
  have hr2 : (y.den : Int) < 2 * y.num.emod (y.den : Int) := by
    have hexp : (2 * n + 1) * (y.den : Int) = 2 * ((y.den : Int) * n) + (y.den : Int) := by grind
    omega
  have hr1 : ¬ (2 * y.num.emod (y.den : Int) < (y.den : Int)) := by omega
  unfold rneInt
  simp [hq, hr1, hr2]

theorem rneInt_of_eq_half_even {y : Rat} {n : Int}
    (heq : y = (n : Rat) + 1 / 2) (heven : n % 2 = 0) :
    rneInt y = n := by
  have hd : 0 < (y.den : Int) := by have := Nat.pos_of_ne_zero y.den_nz; omega
  have h1 : 2 * y.num = (2 * n + 1) * (y.den : Int) := (rat_eq_int_add_half_iff y n).mp heq
  have hlo_int : n * (y.den : Int) ≤ y.num := by
    have hexp : (2 * n + 1) * (y.den : Int) = 2 * (n * (y.den : Int)) + (y.den : Int) := by grind
    omega
  have hhi_int : y.num < (n + 1) * (y.den : Int) := by
    have hexp1 : (2 * n + 1) * (y.den : Int) = 2 * (n * (y.den : Int)) + (y.den : Int) := by grind
    have hexp2 : (n + 1) * (y.den : Int) = n * (y.den : Int) + (y.den : Int) := by grind
    omega
  have hq : y.num.ediv (y.den : Int) = n := int_ediv_eq_of_bounds hd hlo_int hhi_int
  have hdiv : (y.den : Int) * (y.num.ediv (y.den : Int)) + y.num.emod (y.den : Int) = y.num :=
    Int.mul_ediv_add_emod y.num (y.den : Int)
  rw [hq] at hdiv
  have hr_eq : 2 * y.num.emod (y.den : Int) = (y.den : Int) := by
    have hexp : (2 * n + 1) * (y.den : Int) = 2 * ((y.den : Int) * n) + (y.den : Int) := by grind
    omega
  have hr1 : ¬ (2 * y.num.emod (y.den : Int) < (y.den : Int)) := by omega
  have hr2 : ¬ ((y.den : Int) < 2 * y.num.emod (y.den : Int)) := by omega
  unfold rneInt
  simp [hq, hr1, hr2, heven]

theorem rneInt_int (n : Int) : rneInt (n : Rat) = n := by
  apply rneInt_of_lt_half
  · exact Rat.le_refl
  · have : (0 : Rat) < 1 / 2 := rat_div_pos (by decide) (by decide)
    have h := rat_add_lt_add_left (c := (n : Rat)) this
    have h0 : (n : Rat) + 0 = (n : Rat) := by grind
    rw [h0] at h
    exact h

theorem rneInt_le_of_le_int {x : Rat} {n : Int} (h : (n : Rat) ≤ x) :
    n ≤ rneInt x := by
  have hd : 0 < (x.den : Int) := by have := Nat.pos_of_ne_zero x.den_nz; omega
  have h1 : n * (x.den : Int) ≤ x.num := (rat_int_le_iff n x).mp h
  have hdiv : (x.den : Int) * (x.num.ediv (x.den : Int)) + x.num.emod (x.den : Int) = x.num :=
    Int.mul_ediv_add_emod x.num (x.den : Int)
  have hrm1 : x.num.emod (x.den : Int) < (x.den : Int) := Int.emod_lt_of_pos x.num hd
  have hq : n ≤ x.num.ediv (x.den : Int) := by
    by_cases hlt : x.num.ediv (x.den : Int) < n
    · have hle : x.num.ediv (x.den : Int) + 1 ≤ n := by omega
      have hmul : (x.num.ediv (x.den : Int) + 1) * (x.den : Int) ≤ n * (x.den : Int) :=
        Int.mul_le_mul_of_nonneg_right hle (by omega)
      have hexp : (x.num.ediv (x.den : Int) + 1) * (x.den : Int) =
          (x.den : Int) * (x.num.ediv (x.den : Int)) + (x.den : Int) := by grind
      omega
    · omega
  unfold rneInt
  dsimp only
  split
  · exact hq
  · split
    · omega
    · split <;> omega

theorem rneGrid_ge_of_int_le {p : Nat} {x : Rat} {n : Int}
    (h : (n : Rat) ≤ x * pow2Rat (p - 1)) :
    (n : Rat) * invPow2Rat (p - 1) ≤ rneGrid p x := by
  unfold rneGrid
  exact rat_mul_le_mul_of_nonneg_right (rat_intCast_le (rneInt_le_of_le_int h))
    (Rat.le_of_lt (invPow2Rat_pos (p - 1)))

theorem rneGrid_of_int_mul {p : Nat} {x : Rat} {n : Int}
    (h : x * pow2Rat (p - 1) = (n : Rat)) :
    rneGrid p x = (n : Rat) * invPow2Rat (p - 1) := by
  unfold rneGrid
  rw [h, rneInt_int]

end RingAttnKulisch
