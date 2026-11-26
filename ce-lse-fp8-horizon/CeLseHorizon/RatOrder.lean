/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CeLseHorizon.Defs

/-!
# Pure-`Init` `Rat` Order, Dyadic Power, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace CeLseHorizon

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

theorem rat_neg_lt_neg {a b : Rat} (h : a < b) : -b < -a := by
  apply rat_lt_of_sub_pos
  have heq : -a - (-b) = b - a := by grind
  rw [heq]
  exact rat_sub_pos h

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

theorem rat_natCast_le_iff {m n : Nat} : ((m : Rat) ≤ (n : Rat)) ↔ m ≤ n := by
  constructor
  · intro h
    by_cases hle : m ≤ n
    · exact hle
    · have hgt : n < m := by omega
      exact False.elim (Rat.not_le.mpr (rat_natCast_lt hgt) h)
  · exact rat_natCast_le

theorem rat_natCast_lt_iff {m n : Nat} : ((m : Rat) < (n : Rat)) ↔ m < n := by
  constructor
  · intro h
    by_cases hlt : m < n
    · exact hlt
    · have hge : n ≤ m := by omega
      exact False.elim (Rat.not_le.mpr h (rat_natCast_le hge))
  · exact rat_natCast_lt

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

theorem pow2Rat_add (a b : Nat) : pow2Rat (a + b) = pow2Rat a * pow2Rat b := by
  unfold pow2Rat
  rw [Nat.pow_add, Rat.natCast_mul]

theorem invPow2Rat_pos (k : Nat) : (0 : Rat) < invPow2Rat k :=
  rat_div_pos (by decide) (pow2Rat_pos k)

theorem pow2IntRat_pos (k : Int) : (0 : Rat) < pow2IntRat k := by
  cases k with
  | ofNat n => exact pow2Rat_pos n
  | negSucc n => exact invPow2Rat_pos (n + 1)

theorem pow2Rat_mul_invPow2Rat (k : Nat) : pow2Rat k * invPow2Rat k = 1 := by
  unfold invPow2Rat
  exact rat_mul_div_cancel (pow2Rat_ne_zero k)

theorem invPow2Rat_mul_pow2Rat (k : Nat) : invPow2Rat k * pow2Rat k = 1 := by
  rw [Rat.mul_comm]
  exact pow2Rat_mul_invPow2Rat k

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

theorem finSum_ite_const {n : Nat} (y : Fin n) (a b : Rat) :
    finSum (fun v : Fin n => if v = y then a else b) = a + ((n - 1 : Nat) : Rat) * b := by
  have hdecomp : (fun v : Fin n => if v = y then a else b) =
      (fun v : Fin n => b + (if v = y then a - b else 0)) := by
    funext v
    by_cases hv : v = y
    · simp [hv]; grind
    · simp [hv, Rat.add_zero]
  rw [hdecomp, finSum_add, finSum_const, finSum_single]
  have hn1 : n = (n - 1) + 1 := by
    have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le y.val) y.isLt
    omega
  have hcast : (n : Rat) = ((n - 1 : Nat) : Rat) + 1 := by
    have h1 : (n : Rat) = (((n - 1) + 1 : Nat) : Rat) := congrArg (fun k : Nat => (k : Rat)) hn1
    rw [h1, Rat.natCast_add]
    rfl
  rw [hcast]
  grind

end CeLseHorizon
