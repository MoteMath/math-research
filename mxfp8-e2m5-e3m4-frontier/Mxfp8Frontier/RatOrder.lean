/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp8Frontier.Defs

/-!
# Pure-`Init` `Rat` Order, Field, and Linear-Fractional Helpers

Zero Mathlib, zero `native_decide`. Provides elementary `Rat` order/field lemmas,
dyadic power-of-two identities, and exact cross-multiplication lemmas for `linFrac`.
-/

namespace Mxfp8Frontier

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

/-- Exact `Nat`-level cross-multiplication criterion for `linFrac n1 n0 d1 d0 B < linFrac m1 m0 e1 e0 B`. -/
theorem linFrac_lt_of_nat {n1 n0 d1 d0 m1 m0 e1 e0 B : Nat}
    (hd : 0 < d1 * B + d0) (he : 0 < e1 * B + e0)
    (h : (n1 * B + n0) * (e1 * B + e0) < (m1 * B + m0) * (d1 * B + d0)) :
    linFrac n1 n0 d1 d0 B < linFrac m1 m0 e1 e0 B := by
  unfold linFrac
  apply rat_div_lt_div_of_cross (rat_natCast_pos hd) (rat_natCast_pos he)
  rw [← Rat.natCast_mul, ← Rat.natCast_mul]
  exact rat_natCast_lt h

/-- Exact `Nat`-level cross-multiplication criterion for `linFrac n1 n0 d1 d0 B ≤ linFrac m1 m0 e1 e0 B`. -/
theorem linFrac_le_of_nat {n1 n0 d1 d0 m1 m0 e1 e0 B : Nat}
    (hd : 0 < d1 * B + d0) (he : 0 < e1 * B + e0)
    (h : (n1 * B + n0) * (e1 * B + e0) ≤ (m1 * B + m0) * (d1 * B + d0)) :
    linFrac n1 n0 d1 d0 B ≤ linFrac m1 m0 e1 e0 B := by
  unfold linFrac
  apply rat_div_le_div_of_cross (rat_natCast_pos hd) (rat_natCast_pos he)
  rw [← Rat.natCast_mul, ← Rat.natCast_mul]
  exact rat_natCast_le h

/-- Exact `Nat`-level equality between `ef21AlphaCand ay ae my me B` and `linFrac n1 n0 d1 d0 B`
    when `ae ≤ ay`, `me ≤ my`, `0 < ay`, and `1 ≤ B`. -/
theorem ef21AlphaCand_eq_linFrac {ay ae my me n1 n0 d1 d0 B : Nat}
    (_hB : 1 ≤ B) (hay : 0 < ay) (hae : ae ≤ ay) (hme : me ≤ my)
    (hd : 0 < d1 * B + d0)
    (hcross :
      ((ay * ay - ae * ae) + (B - 1) * (my * my - me * me)) * (d1 * B + d0) =
        (n1 * B + n0) * (ay * ay + (B - 1) * (my * my))) :
    ef21AlphaCand ay ae my me B = linFrac n1 n0 d1 d0 B := by
  unfold ef21AlphaCand linFrac
  have hden_pos : 0 < ay * ay + (B - 1) * (my * my) := by
    have : 0 < ay * ay := Nat.mul_pos hay hay
    omega
  have hden_rat_pos : (0 : Rat) < ((ay * ay + (B - 1) * (my * my) : Nat) : Rat) :=
    rat_natCast_pos hden_pos
  have hden_ne : ((ay * ay + (B - 1) * (my * my) : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt hden_rat_pos
  have hd_ne : ((d1 * B + d0 : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos hd)
  have hnum_le : ae * ae + (B - 1) * (me * me) ≤ ay * ay + (B - 1) * (my * my) := by
    have h1 : ae * ae ≤ ay * ay := Nat.mul_le_mul hae hae
    have h2 : me * me ≤ my * my := Nat.mul_le_mul hme hme
    have h3 : (B - 1) * (me * me) ≤ (B - 1) * (my * my) := Nat.mul_le_mul_left (B - 1) h2
    omega
  have hsub_eq :
      (ay * ay + (B - 1) * (my * my)) - (ae * ae + (B - 1) * (me * me)) =
        (ay * ay - ae * ae) + (B - 1) * (my * my - me * me) := by
    have h1 : ae * ae ≤ ay * ay := Nat.mul_le_mul hae hae
    have h2 : me * me ≤ my * my := Nat.mul_le_mul hme hme
    have h3 : (B - 1) * (my * my - me * me) + (B - 1) * (me * me) = (B - 1) * (my * my) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel h2]
    omega
  have h1sub :
      (1 : Rat) - (((ae * ae + (B - 1) * (me * me) : Nat) : Rat) /
                   ((ay * ay + (B - 1) * (my * my) : Nat) : Rat)) =
      (((ay * ay - ae * ae) + (B - 1) * (my * my - me * me) : Nat) : Rat) /
        ((ay * ay + (B - 1) * (my * my) : Nat) : Rat) := by
    have hadd :
        ((ay * ay - ae * ae) + (B - 1) * (my * my - me * me)) +
          (ae * ae + (B - 1) * (me * me)) =
        ay * ay + (B - 1) * (my * my) := by
      rw [← hsub_eq, Nat.sub_add_cancel hnum_le]
    have hadd_rat :
        (((ay * ay - ae * ae) + (B - 1) * (my * my - me * me) : Nat) : Rat) +
          ((ae * ae + (B - 1) * (me * me) : Nat) : Rat) =
        ((ay * ay + (B - 1) * (my * my) : Nat) : Rat) := by
      rw [← Rat.natCast_add, hadd]
    have hstep :
        (((ay * ay - ae * ae) + (B - 1) * (my * my - me * me) : Nat) : Rat) /
          ((ay * ay + (B - 1) * (my * my) : Nat) : Rat) +
        ((ae * ae + (B - 1) * (me * me) : Nat) : Rat) /
          ((ay * ay + (B - 1) * (my * my) : Nat) : Rat) = 1 := by
      rw [Rat.div_def, Rat.div_def, ← Rat.add_mul, hadd_rat, Rat.mul_inv_cancel _ hden_ne]
    grind
  rw [h1sub]
  apply rat_div_eq_of_cross hden_ne hd_ne
  rw [← Rat.natCast_mul, ← Rat.natCast_mul]
  exact congrArg (fun k : Nat => (k : Rat)) hcross

/-- Exact `Nat`-level criterion for `linFrac n1 n0 d1 d0 B = 1`. -/
theorem linFrac_eq_one {n1 n0 d1 d0 B : Nat}
    (hd : 0 < d1 * B + d0) (h : n1 * B + n0 = d1 * B + d0) :
    linFrac n1 n0 d1 d0 B = 1 := by
  unfold linFrac
  rw [h, Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt (rat_natCast_pos hd))]

/-- Exact `Nat`-level criterion for `(1 - linFrac n1 n0 d1 d0 B) * (p / q) < 1 - linFrac m1 m0 e1 e0 B`. -/
theorem one_sub_linFrac_mul_lt {n1 n0 d1 d0 m1 m0 e1 e0 B p q : Nat}
    (hd : 0 < d1 * B + d0) (he : 0 < e1 * B + e0) (hq : 0 < q)
    (hn : n1 * B + n0 ≤ d1 * B + d0) (hm : m1 * B + m0 ≤ e1 * B + e0)
    (h : ((d1 * B + d0) - (n1 * B + n0)) * p * (e1 * B + e0) <
         ((e1 * B + e0) - (m1 * B + m0)) * (q * (d1 * B + d0))) :
    (1 - linFrac n1 n0 d1 d0 B) * ((p : Rat) / (q : Rat)) < 1 - linFrac m1 m0 e1 e0 B := by
  unfold linFrac
  have hd_pos : (0 : Rat) < ((d1 * B + d0 : Nat) : Rat) := rat_natCast_pos hd
  have he_pos : (0 : Rat) < ((e1 * B + e0 : Nat) : Rat) := rat_natCast_pos he
  have hq_pos : (0 : Rat) < (q : Rat) := rat_natCast_pos hq
  have hd_ne : ((d1 * B + d0 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hd_pos
  have he_ne : ((e1 * B + e0 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt he_pos
  have hq_ne : (q : Rat) ≠ 0 := Rat.ne_of_gt hq_pos
  have hsub1 : (1 : Rat) - ((n1 * B + n0 : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat) =
      (((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat) := by
    have ha : ((d1 * B + d0) - (n1 * B + n0)) + (n1 * B + n0) = d1 * B + d0 :=
      Nat.sub_add_cancel hn
    have hr : (((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) + ((n1 * B + n0 : Nat) : Rat) =
        ((d1 * B + d0 : Nat) : Rat) := by rw [← Rat.natCast_add, ha]
    have hs : (((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat) +
        ((n1 * B + n0 : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat) = 1 := by
      rw [Rat.div_def, Rat.div_def, ← Rat.add_mul, hr, Rat.mul_inv_cancel _ hd_ne]
    grind
  have hsub2 : (1 : Rat) - ((m1 * B + m0 : Nat) : Rat) / ((e1 * B + e0 : Nat) : Rat) =
      (((e1 * B + e0) - (m1 * B + m0) : Nat) : Rat) / ((e1 * B + e0 : Nat) : Rat) := by
    have ha : ((e1 * B + e0) - (m1 * B + m0)) + (m1 * B + m0) = e1 * B + e0 :=
      Nat.sub_add_cancel hm
    have hr : (((e1 * B + e0) - (m1 * B + m0) : Nat) : Rat) + ((m1 * B + m0 : Nat) : Rat) =
        ((e1 * B + e0 : Nat) : Rat) := by rw [← Rat.natCast_add, ha]
    have hs : (((e1 * B + e0) - (m1 * B + m0) : Nat) : Rat) / ((e1 * B + e0 : Nat) : Rat) +
        ((m1 * B + m0 : Nat) : Rat) / ((e1 * B + e0 : Nat) : Rat) = 1 := by
      rw [Rat.div_def, Rat.div_def, ← Rat.add_mul, hr, Rat.mul_inv_cancel _ he_ne]
    grind
  rw [hsub1, hsub2]
  have hmul : ((((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat)) *
      ((p : Rat) / (q : Rat)) =
      ((((d1 * B + d0) - (n1 * B + n0)) * p : Nat) : Rat) /
        ((q * (d1 * B + d0) : Nat) : Rat) := by
    have hqd_ne : ((q * (d1 * B + d0) : Nat) : Rat) ≠ 0 :=
      Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos hq hd))
    have hL : ((((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat)) *
        ((p : Rat) / (q : Rat)) * ((q * (d1 * B + d0) : Nat) : Rat) =
        ((((d1 * B + d0) - (n1 * B + n0)) * p : Nat) : Rat) := by
      rw [Rat.natCast_mul, Rat.natCast_mul]
      have c1 := rat_div_mul_cancel (a := (((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat)) hd_ne
      have c2 := rat_div_mul_cancel (a := (p : Rat)) hq_ne
      calc
        ((((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat)) *
            ((p : Rat) / (q : Rat)) * ((q : Rat) * ((d1 * B + d0 : Nat) : Rat))
            = ((((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat) *
                ((d1 * B + d0 : Nat) : Rat)) * (((p : Rat) / (q : Rat)) * (q : Rat)) := by grind
        _ = (((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) * (p : Rat) := by rw [c1, c2]
    have hR := rat_div_mul_cancel (a := ((((d1 * B + d0) - (n1 * B + n0)) * p : Nat) : Rat)) hqd_ne
    have hdiff : (((((d1 * B + d0) - (n1 * B + n0) : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat)) *
        ((p : Rat) / (q : Rat)) -
        ((((d1 * B + d0) - (n1 * B + n0)) * p : Nat) : Rat) / ((q * (d1 * B + d0) : Nat) : Rat)) *
        ((q * (d1 * B + d0) : Nat) : Rat) = 0 := by grind
    cases Rat.mul_eq_zero.mp hdiff with
    | inl hz => grind
    | inr h0 => exact False.elim (hqd_ne h0)
  rw [hmul]
  apply rat_div_lt_div_of_cross (rat_natCast_pos (Nat.mul_pos hq hd)) he_pos
  rw [← Rat.natCast_mul, ← Rat.natCast_mul]
  exact rat_natCast_lt h

end Mxfp8Frontier
