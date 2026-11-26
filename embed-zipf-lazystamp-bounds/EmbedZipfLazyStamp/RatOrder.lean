/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp.Defs

/-!
# Pure-`Init` `Rat` Order, Sums, Products, and Power Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace EmbedZipfLazyStamp

/-! ### Basic `Rat` Order Lemmas -/

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
    exact Rat.ne_of_lt h rfl
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

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  have h1 : (1 : Rat) ≤ (n : Rat) := by
    have : (1 : Int) ≤ (n : Int) := by omega
    exact Rat.intCast_le_intCast.mpr this
  exact rat_lt_of_lt_of_le (by decide : (0 : Rat) < 1) h1

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  have : (0 : Int) ≤ (n : Int) := by omega
  exact Rat.intCast_le_intCast.mpr this

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

theorem ratAbs_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) : (0 : Rat) < ratAbs x := by
  unfold ratAbs
  split
  · rename_i hge
    exact Rat.lt_of_le_of_ne hge (Ne.symm hx)
  · rename_i hlt
    exact rat_neg_pos_of_neg (Rat.not_le.mp hlt)

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

theorem ratAbs_le_iff {x b : Rat} : ratAbs x ≤ b ↔ (-b ≤ x ∧ x ≤ b) := by
  constructor
  · intro h
    unfold ratAbs at h
    split at h
    · rename_i hx
      have hnb : -b ≤ 0 := by
        have h0b : (0 : Rat) ≤ b := Rat.le_trans hx h
        have := rat_sub_nonneg h0b
        grind
      exact ⟨Rat.le_trans hnb hx, h⟩
    · rename_i hnx
      have hlt : x < 0 := Rat.not_le.mp hnx
      have hlo : -b ≤ x := by
        have := rat_sub_nonneg h
        have : (0 : Rat) ≤ x - (-b) := by grind
        exact rat_le_of_sub_nonneg this
      have hb0 : (0 : Rat) ≤ b := Rat.le_trans (rat_neg_nonneg_of_nonpos (Rat.le_of_lt hlt)) h
      exact ⟨hlo, Rat.le_trans (Rat.le_of_lt hlt) hb0⟩
  · rintro ⟨hlo, hhi⟩
    unfold ratAbs
    split
    · exact hhi
    · have := rat_sub_nonneg hlo
      have hneg : (0 : Rat) ≤ b - (-x) := by grind
      exact rat_le_of_sub_nonneg hneg

theorem ratAbs_lt_iff {x b : Rat} : ratAbs x < b ↔ (-b < x ∧ x < b) := by
  constructor
  · intro h
    unfold ratAbs at h
    split at h
    · rename_i hx
      have hb0 : (0 : Rat) < b := rat_lt_of_le_of_lt hx h
      have hnb : -b < 0 := by
        have := rat_sub_pos hb0
        have : (0 : Rat) < 0 - (-b) := by grind
        exact rat_lt_of_sub_pos this
      exact ⟨rat_lt_of_lt_of_le hnb hx, h⟩
    · rename_i hnx
      have hlt : x < 0 := Rat.not_le.mp hnx
      have hlo : -b < x := by
        have := rat_sub_pos h
        have : (0 : Rat) < x - (-b) := by grind
        exact rat_lt_of_sub_pos this
      have hb0 : (0 : Rat) < b := rat_lt_of_le_of_lt (rat_neg_nonneg_of_nonpos (Rat.le_of_lt hlt)) h
      exact ⟨hlo, rat_lt_trans hlt hb0⟩
  · rintro ⟨hlo, hhi⟩
    unfold ratAbs
    split
    · exact hhi
    · have := rat_sub_pos hlo
      have hneg : (0 : Rat) < b - (-x) := by grind
      exact rat_lt_of_sub_pos hneg

/-! ### `finSum`, `finSumInt`, `finProd` Lemmas -/

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

theorem finSum_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    finSum (fun j => f j * c) = finSum f * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
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

theorem finSum_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ j, (0 : Rat) ≤ f j) :
    (0 : Rat) ≤ finSum f := by
  unfold finSum
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [finSumAux]
    exact rat_add_nonneg (ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem finSum_pos {n : Nat} (hn : 0 < n) {f : Fin n → Rat} (h : ∀ j, (0 : Rat) < f j) :
    (0 : Rat) < finSum f := by
  cases n with
  | zero => omega
  | succ k =>
    unfold finSum
    simp only [finSumAux]
    have h1 : (0 : Rat) ≤ finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) :=
      finSum_nonneg (fun j => Rat.le_of_lt (h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
    have h2 : (0 : Rat) < f ⟨k, Nat.lt_succ_self k⟩ := h ⟨k, Nat.lt_succ_self k⟩
    rw [Rat.add_comm]
    exact rat_add_pos_of_pos_of_nonneg h2 h1

theorem finSum_const (n : Nat) (c : Rat) :
    finSum (fun _ : Fin n => c) = (n : Rat) * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    rw [hcast]
    grind

theorem finSum_ite_eq {n : Nat} (y : Fin n) :
    finSum (fun v : Fin n => if v = y then (1 : Rat) else 0) = 1 := by
  unfold finSum
  induction n with
  | zero => exact Fin.elim0 y
  | succ k ih =>
    simp only [finSumAux]
    by_cases hy : y.val = k
    · have hy_eq : y = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hy
      have hzero : finSumAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = y then (1 : Rat) else 0) = 0 := by
        have hcongr := finSumAux_congr (k := k)
          (f := fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = y then (1 : Rat) else 0)
          (g := fun _ => (0 : Rat))
          (fun j => by
            have hne : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ y := by
              intro heq
              have hv : j.val = y.val := congrArg Fin.val heq
              omega
            simp [hne])
        rw [hcongr]
        exact finSum_zero k
      rw [hzero, hy_eq]
      simp only [↓reduceIte]
      grind
    · have hy_lt : y.val < k := by omega
      let y' : Fin k := ⟨y.val, hy_lt⟩
      have hne_last : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ y := by
        intro heq
        have hv : k = y.val := congrArg Fin.val heq
        omega
      have hcongr := finSumAux_congr (k := k)
        (f := fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = y then (1 : Rat) else 0)
        (g := fun j => if j = y' then (1 : Rat) else 0)
        (fun j => by
          by_cases h : j.val = y.val
          · have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = y := Fin.ext h
            have h2 : j = y' := Fin.ext h
            split <;> (try split) <;> first | rfl | contradiction
          · have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ y := by
              intro heq; exact h (congrArg Fin.val heq)
            have h2 : j ≠ y' := by
              intro heq; exact h (congrArg Fin.val heq)
            split <;> (try split) <;> first | rfl | contradiction)
      rw [hcongr, ih y']
      simp only [hne_last, ↓reduceIte]
      grind

theorem finSum_swap {m n : Nat} (f : Fin m → Fin n → Rat) :
    finSum (fun i => finSum (fun j => f i j)) =
      finSum (fun j => finSum (fun i => f i j)) := by
  induction m with
  | zero =>
    unfold finSum
    simp only [finSumAux]
    have h := finSum_zero n
    unfold finSum at h
    rw [h]
  | succ k ih =>
    have hsplit : finSum (fun i : Fin (k + 1) => finSum (fun j => f i j)) =
        finSum (fun i : Fin k => finSum (fun j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j)) +
        finSum (fun j => f ⟨k, Nat.lt_succ_self k⟩ j) := rfl
    rw [hsplit, ih (fun i j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j), ← finSum_add]
    exact finSum_congr (fun _ => rfl)

theorem finProd_pos {n : Nat} {f : Fin n → Rat} (h : ∀ j, (0 : Rat) < f j) :
    (0 : Rat) < finProd f := by
  unfold finProd
  induction n with
  | zero => simp only [finProdAux]; decide
  | succ k ih =>
    simp only [finProdAux]
    exact rat_mul_pos (ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      (h ⟨k, Nat.lt_succ_self k⟩)

theorem finProd_mul {n : Nat} (f g : Fin n → Rat) :
    finProd (fun j => f j * g j) = finProd f * finProd g := by
  unfold finProd
  induction n with
  | zero => simp [finProdAux]
  | succ k ih =>
    simp only [finProdAux]
    rw [ih]
    grind

theorem finProd_const (n : Nat) (c : Rat) :
    finProd (fun _ : Fin n => c) = ratPow c n := by
  unfold finProd
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finProdAux, ratPow]
    rw [ih, Rat.mul_comm]

/-! ### `ratPow`, `pow2Int`, `pow4Int` Lemmas -/

theorem ratPow_add (x : Rat) (a b : Nat) :
    ratPow x (a + b) = ratPow x a * ratPow x b := by
  induction a with
  | zero => simp [ratPow]
  | succ k ih =>
    rw [Nat.succ_add, ratPow, ratPow, ih, Rat.mul_assoc]

theorem ratPow_mul_comm (x y : Rat) (n : Nat) :
    ratPow (x * y) n = ratPow x n * ratPow y n := by
  induction n with
  | zero => simp [ratPow]
  | succ k ih =>
    simp only [ratPow]
    rw [ih]
    grind

theorem ratPow_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) (n : Nat) :
    (0 : Rat) ≤ ratPow x n := by
  induction n with
  | zero => simp only [ratPow]; decide
  | succ k ih =>
    simp only [ratPow]
    exact Rat.mul_nonneg hx ih

theorem ratPow_pos {x : Rat} (hx : (0 : Rat) < x) (n : Nat) :
    (0 : Rat) < ratPow x n := by
  induction n with
  | zero => simp only [ratPow]; decide
  | succ k ih =>
    simp only [ratPow]
    exact rat_mul_pos hx ih

theorem ratPow_le_ratPow {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) (n : Nat) :
    ratPow a n ≤ ratPow b n := by
  have hb : (0 : Rat) ≤ b := Rat.le_trans ha hab
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [ratPow]
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_left ih ha)
      (rat_mul_le_mul_of_nonneg_right hab (ratPow_nonneg hb k))

theorem ratPow_lt_ratPow {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a < b) {n : Nat} (hn : 0 < n) :
    ratPow a n < ratPow b n := by
  cases n with
  | zero => omega
  | succ k =>
    have hb : (0 : Rat) < b := rat_lt_of_le_of_lt ha hab
    simp only [ratPow]
    have h1 : a * ratPow a k ≤ a * ratPow b k :=
      rat_mul_le_mul_of_nonneg_left (ratPow_le_ratPow ha (Rat.le_of_lt hab) k) ha
    have h2 : a * ratPow b k < b * ratPow b k :=
      rat_mul_lt_mul_of_pos_right hab (ratPow_pos hb k)
    exact rat_lt_of_le_of_lt h1 h2

theorem rat_le_of_ratPow_le {a b : Rat} (_ha : (0 : Rat) ≤ a) (hb : (0 : Rat) ≤ b)
    {n : Nat} (hn : 0 < n) (h : ratPow a n ≤ ratPow b n) : a ≤ b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl hab => exact hab
  | inr hba =>
    by_cases heq : a = b
    · rw [heq]; exact Rat.le_refl
    · have hlt : b < a := Rat.lt_of_le_of_ne hba (Ne.symm heq)
      have hpow : ratPow b n < ratPow a n := ratPow_lt_ratPow hb hlt hn
      exact False.elim (Rat.not_le.mpr hpow h)

theorem pow2_nat_pos (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) :=
  rat_natCast_pos (Nat.pow_pos (by omega))

theorem pow2Int_pos (e : Int) : (0 : Rat) < pow2Int e := by
  unfold pow2Int
  split
  · exact pow2_nat_pos e.toNat
  · exact rat_div_pos (by decide) (pow2_nat_pos (-e).toNat)

theorem pow2Int_ne_zero (e : Int) : pow2Int e ≠ 0 :=
  Rat.ne_of_gt (pow2Int_pos e)

theorem pow2Int_ofNat (n : Nat) : pow2Int (n : Int) = ((2 ^ n : Nat) : Rat) := by
  unfold pow2Int
  have h : (0 : Int) ≤ (n : Int) := by omega
  simp [h]

theorem pow2Int_neg (e : Int) : pow2Int (-e) = (1 : Rat) / pow2Int e := by
  unfold pow2Int
  by_cases he0 : e = 0
  · subst he0
    simp only [Int.neg_zero, Int.le_refl, ↓reduceIte, Int.toNat_zero, Nat.pow_zero]
    have h1 : ((1 : Nat) : Rat) = 1 := rfl
    rw [h1]; grind
  · by_cases hge : (0 : Int) ≤ e
    · have hlt : ¬ ((0 : Int) ≤ -e) := by omega
      simp only [hge, hlt, ↓reduceIte, Int.neg_neg]
    · have hpos : (0 : Int) ≤ -e := by omega
      simp only [hge, hpos, ↓reduceIte]
      have hne : ((2 ^ (-e).toNat : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (pow2_nat_pos _)
      have hne_inv : (1 : Rat) / ((2 ^ (-e).toNat : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt (rat_div_pos (by decide) (pow2_nat_pos _))
      symm
      rw [rat_div_eq_iff hne_inv, rat_mul_div_cancel hne]

theorem pow2Int_add_one (e : Int) : pow2Int (e + 1) = 2 * pow2Int e := by
  unfold pow2Int
  by_cases hge : (0 : Int) ≤ e
  · have hge1 : (0 : Int) ≤ e + 1 := by omega
    simp only [hge, hge1, ↓reduceIte]
    have hto : (e + 1).toNat = e.toNat + 1 := by omega
    rw [hto, Nat.pow_succ, Rat.natCast_mul, Rat.mul_comm]
    rfl
  · by_cases he1 : e = -1
    · subst he1
      have h0 : (-1 : Int) + 1 = 0 := rfl
      have hneg : ¬ ((0 : Int) ≤ -1) := by omega
      simp only [h0, Int.le_refl, hneg, ↓reduceIte]
      have h1 : ((2 ^ Int.toNat 0 : Nat) : Rat) = 1 := rfl
      have h2 : ((2 ^ (- (-1 : Int)).toNat : Nat) : Rat) = 2 := rfl
      rw [h1, h2]; grind
    · have hlt1 : ¬ ((0 : Int) ≤ e + 1) := by omega
      simp only [hge, hlt1, ↓reduceIte]
      have hto : (-e).toNat = (-(e + 1)).toNat + 1 := by omega
      rw [hto, Nat.pow_succ, Rat.natCast_mul]
      have h1 : ((2 ^ (-(e + 1)).toNat : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (pow2_nat_pos _)
      have h2 : ((2 ^ (-(e + 1)).toNat : Nat) : Rat) * (2 : Rat) ≠ 0 :=
        Rat.ne_of_gt (rat_mul_pos (pow2_nat_pos _) (by decide))
      rw [rat_div_eq_iff h1]
      have hmul : 2 * (1 / (((2 ^ (-(e + 1)).toNat : Nat) : Rat) * 2)) *
          ((2 ^ (-(e + 1)).toNat : Nat) : Rat) =
          (1 / (((2 ^ (-(e + 1)).toNat : Nat) : Rat) * 2)) *
          (((2 ^ (-(e + 1)).toNat : Nat) : Rat) * 2) := by grind
      have hcast : ((2 : Nat) : Rat) = 2 := rfl
      rw [hcast, hmul, rat_div_mul_cancel h2]

theorem pow2Int_sub_one (e : Int) : pow2Int (e - 1) = pow2Int e / 2 := by
  have h := pow2Int_add_one (e - 1)
  have he : e - 1 + 1 = e := by omega
  rw [he] at h
  symm
  rw [rat_div_eq_iff (by decide : (2 : Rat) ≠ 0)]
  grind

theorem pow2Int_add_nat (a : Int) (n : Nat) :
    pow2Int (a + (n : Int)) = pow2Int a * pow2Int (n : Int) := by
  induction n with
  | zero =>
    have h0 : pow2Int 0 = 1 := by decide
    rw [Int.ofNat_zero, Int.add_zero, h0, Rat.mul_one]
  | succ k ih =>
    have h1 : a + ((k + 1 : Nat) : Int) = (a + (k : Int)) + 1 := by omega
    have h2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [h1, h2, pow2Int_add_one, pow2Int_add_one, ih]
    grind

theorem pow2Int_sub_nat (a : Int) (n : Nat) :
    pow2Int (a - (n : Int)) = pow2Int a * pow2Int (-(n : Int)) := by
  induction n with
  | zero =>
    have h0 : pow2Int 0 = 1 := by decide
    simp only [Int.ofNat_zero, Int.sub_zero, Int.neg_zero, h0, Rat.mul_one]
  | succ k ih =>
    have h1 : a - ((k + 1 : Nat) : Int) = (a - (k : Int)) - 1 := by omega
    have h2 : -((k + 1 : Nat) : Int) = -(k : Int) - 1 := by omega
    rw [h1, h2, pow2Int_sub_one, pow2Int_sub_one, ih]
    grind

theorem pow2Int_add (a b : Int) : pow2Int (a + b) = pow2Int a * pow2Int b := by
  cases b with
  | ofNat n => exact pow2Int_add_nat a n
  | negSucc n =>
    have h1 : a + Int.negSucc n = a - ((n + 1 : Nat) : Int) := by omega
    have h2 : Int.negSucc n = -((n + 1 : Nat) : Int) := by omega
    rw [h1, h2]
    exact pow2Int_sub_nat a (n + 1)

theorem pow2Int_sub (a b : Int) : pow2Int (a - b) = pow2Int a / pow2Int b := by
  have h : a - b = a + (-b) := by omega
  rw [h, pow2Int_add, pow2Int_neg]
  rw [Rat.div_def, Rat.div_def, Rat.one_mul]

theorem pow4Int_pos (e : Int) : (0 : Rat) < pow4Int e :=
  pow2Int_pos (2 * e)

theorem pow4Int_ne_zero (e : Int) : pow4Int e ≠ 0 :=
  Rat.ne_of_gt (pow4Int_pos e)

theorem pow4Int_add (a b : Int) : pow4Int (a + b) = pow4Int a * pow4Int b := by
  unfold pow4Int
  have h : 2 * (a + b) = 2 * a + 2 * b := by omega
  rw [h, pow2Int_add]

theorem pow4Int_sub (a b : Int) : pow4Int (a - b) = pow4Int a / pow4Int b := by
  unfold pow4Int
  have h : 2 * (a - b) = 2 * a - 2 * b := by omega
  rw [h, pow2Int_sub]

theorem pow4Int_neg (e : Int) : pow4Int (-e) = 1 / pow4Int e := by
  unfold pow4Int
  have h : 2 * (-e) = -(2 * e) := by omega
  rw [h, pow2Int_neg]

theorem finProd_pow4Int {n : Nat} (b : Fin n → Int) :
    finProd (fun j => pow4Int (b j)) = pow4Int (finSumInt b) := by
  unfold finProd finSumInt
  induction n with
  | zero =>
    simp [finProdAux, finSumIntAux, pow4Int, pow2Int]
  | succ k ih =>
    simp only [finProdAux, finSumIntAux]
    rw [ih (fun j => b ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), ← pow4Int_add]

end EmbedZipfLazyStamp
