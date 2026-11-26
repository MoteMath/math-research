/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlibiBitsplitKulisch.Defs

/-!
# Pure-`Init` `Rat` Order, Absolute Value, and Dyadic Power Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace AlibiBitsplitKulisch

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

theorem rat_div_mul_cancel {a b : Rat} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.mul_one]

theorem rat_mul_div_cancel {a b : Rat} (hb : b ≠ 0) : b * (a / b) = a := by
  rw [Rat.mul_comm, rat_div_mul_cancel hb]

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

theorem invPow2Rat_ne_zero (k : Nat) : invPow2Rat k ≠ 0 :=
  Rat.ne_of_gt (invPow2Rat_pos k)

theorem pow2Rat_mul_invPow2Rat (k : Nat) : pow2Rat k * invPow2Rat k = 1 := by
  unfold invPow2Rat
  exact rat_mul_div_cancel (pow2Rat_ne_zero k)

theorem invPow2Rat_add (a b : Nat) : invPow2Rat (a + b) = invPow2Rat a * invPow2Rat b := by
  unfold invPow2Rat
  rw [pow2Rat_add]
  have ha : pow2Rat a ≠ 0 := pow2Rat_ne_zero a
  have hb : pow2Rat b ≠ 0 := pow2Rat_ne_zero b
  have hab : pow2Rat a * pow2Rat b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact hb h
  have h1 : (1 / (pow2Rat a * pow2Rat b)) * (pow2Rat a * pow2Rat b) = 1 :=
    rat_div_mul_cancel hab
  have h2 : ((1 / pow2Rat a) * (1 / pow2Rat b)) * (pow2Rat a * pow2Rat b) = 1 := by
    have hrw : ((1 / pow2Rat a) * (1 / pow2Rat b)) * (pow2Rat a * pow2Rat b) =
        ((1 / pow2Rat a) * pow2Rat a) * ((1 / pow2Rat b) * pow2Rat b) := by grind
    rw [hrw, rat_div_mul_cancel ha, rat_div_mul_cancel hb, Rat.mul_one]
  have h3 : (1 / (pow2Rat a * pow2Rat b) - (1 / pow2Rat a) * (1 / pow2Rat b)) *
      (pow2Rat a * pow2Rat b) = 0 := by
    have hrw : (1 / (pow2Rat a * pow2Rat b) - (1 / pow2Rat a) * (1 / pow2Rat b)) *
        (pow2Rat a * pow2Rat b) =
        (1 / (pow2Rat a * pow2Rat b)) * (pow2Rat a * pow2Rat b) -
        ((1 / pow2Rat a) * (1 / pow2Rat b)) * (pow2Rat a * pow2Rat b) := by grind
    rw [hrw, h1, h2]
    grind
  cases Rat.mul_eq_zero.mp h3 with
  | inl h => grind
  | inr h => exact False.elim (hab h)

theorem zpow2Rat_pos (e : Int) : (0 : Rat) < zpow2Rat e := by
  unfold zpow2Rat
  split
  · exact pow2Rat_pos _
  · exact invPow2Rat_pos _

theorem zpow2Rat_ne_zero (e : Int) : zpow2Rat e ≠ 0 :=
  Rat.ne_of_gt (zpow2Rat_pos e)

theorem zpow2Rat_add (a b : Int) : zpow2Rat (a + b) = zpow2Rat a * zpow2Rat b := by
  have hcancel_pos_neg : ∀ (m n : Nat),
      pow2Rat m * invPow2Rat n = zpow2Rat ((m : Int) - (n : Int)) := by
    intro m n
    by_cases hmn : n ≤ m
    · have hsub : (0 : Int) ≤ (m : Int) - (n : Int) := by omega
      have htoNat : ((m : Int) - (n : Int)).toNat = m - n := by omega
      unfold zpow2Rat
      simp only [hsub, ite_true, htoNat]
      have hmul : pow2Rat m = pow2Rat (m - n) * pow2Rat n := by
        rw [← pow2Rat_add, Nat.sub_add_cancel hmn]
      rw [hmul, Rat.mul_assoc, pow2Rat_mul_invPow2Rat, Rat.mul_one]
    · have hlt : m < n := Nat.lt_of_not_le hmn
      have hsub : ¬ ((0 : Int) ≤ (m : Int) - (n : Int)) := by omega
      have htoNat : (-((m : Int) - (n : Int))).toNat = n - m := by omega
      unfold zpow2Rat
      simp only [hsub, ite_false, htoNat]
      have hmul : invPow2Rat n = invPow2Rat m * invPow2Rat (n - m) := by
        rw [← invPow2Rat_add, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
      rw [hmul, ← Rat.mul_assoc, pow2Rat_mul_invPow2Rat, Rat.one_mul]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · have hab : 0 ≤ a + b := by omega
      have hto : (a + b).toNat = a.toNat + b.toNat := by omega
      unfold zpow2Rat
      simp only [hab, ha, hb, ite_true, hto, pow2Rat_add]
    · have hsum : a + b = (a.toNat : Int) - ((-b).toNat : Int) := by omega
      rw [hsum, ← hcancel_pos_neg]
      unfold zpow2Rat
      simp only [ha, hb, ite_true, ite_false]
  · by_cases hb : 0 ≤ b
    · have hsum : a + b = (b.toNat : Int) - ((-a).toNat : Int) := by omega
      rw [hsum, ← hcancel_pos_neg, Rat.mul_comm]
      unfold zpow2Rat
      simp only [ha, hb, ite_true, ite_false]
    · have hab : ¬ (0 ≤ a + b) := by omega
      have hto : (-(a + b)).toNat = (-a).toNat + (-b).toNat := by omega
      unfold zpow2Rat
      simp only [hab, ha, hb, ite_false, hto, invPow2Rat_add]

theorem zpow2Rat_ofNat (n : Nat) : zpow2Rat (n : Int) = pow2Rat n := by
  unfold zpow2Rat
  have h : (0 : Int) ≤ (n : Int) := by omega
  simp only [h, ite_true]
  rfl

theorem zpow2Rat_neg_ofNat (n : Nat) : zpow2Rat (-(n : Int)) = invPow2Rat n := by
  by_cases hn : n = 0
  · subst hn
    unfold zpow2Rat invPow2Rat pow2Rat
    have h0 : (0 : Int) ≤ -(0 : Nat) := by omega
    simp only [h0, ite_true]
    have h1 : (-(0 : Nat) : Int).toNat = 0 := rfl
    rw [h1]
    grind
  · unfold zpow2Rat
    have hneg : ¬ ((0 : Int) ≤ -(n : Int)) := by omega
    have hto : (- -(n : Int)).toNat = n := by omega
    simp only [hneg, ite_false, hto]

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

end AlibiBitsplitKulisch
