/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp4OptClipping.Defs

/-!
# Pure-`Init` `Rat` Order, Field, Convexity, and E2M1 Piecewise Helpers

Zero Mathlib, zero `native_decide`. Provides elementary `Rat` order/field lemmas,
piecewise-convex quadratic endpoint bounds, and exact piecewise evaluations of `e2m1ErrSq`.
-/

namespace Mxfp4OptClipping

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

theorem rat_le_zero_of_mul_pos {a c : Rat} (hc : (0 : Rat) < c) (h : a * c ≤ 0) : a ≤ 0 := by
  apply rat_le_of_mul_pos_right hc
  rw [Rat.zero_mul]
  exact h

/-- Clear a single denominator `w = N / D` (`w * D = N`, `0 < D`) from a linear inequality `a + c * w ≤ 0`. -/
theorem rat_lin_w_le_zero {w N D a c : Rat} (hD : (0 : Rat) < D) (hw : w * D = N)
    (h : a * D + c * N ≤ 0) : a + c * w ≤ 0 := by
  apply rat_le_zero_of_mul_pos hD
  have hid : (a + c * w) * D = a * D + c * (w * D) := by grind
  rw [hid, hw]
  exact h

/-- Clear a single denominator `w = N / D` from an arbitrary expression `expr ≤ 0` given `expr * D = poly`. -/
theorem rat_le_zero_of_clear {expr poly D : Rat} (hD : (0 : Rat) < D)
    (heq : expr * D = poly) (hpoly : poly ≤ 0) : expr ≤ 0 := by
  apply rat_le_zero_of_mul_pos hD
  rw [heq]
  exact hpoly

/-- Clear a single denominator `D > 0` from `lhs ≤ rhs` given `(lhs - rhs) * D = poly ≤ 0`. -/
theorem rat_le_of_clear {lhs rhs poly D : Rat} (hD : (0 : Rat) < D)
    (heq : (lhs - rhs) * D = poly) (hpoly : poly ≤ 0) : lhs ≤ rhs := by
  have h0 : lhs - rhs ≤ 0 := rat_le_zero_of_clear hD heq hpoly
  apply rat_le_of_sub_nonneg
  grind

/-- Sum a coordinatewise upper bound `e_s(u) - w * u^2 ≤ K` over any list `l`. -/
theorem blockErrSq_sub_wEnergy_le_len {s w K : Rat} (l : List Rat)
    (h : ∀ u ∈ l, e2m1ErrSq s u - w * sq u ≤ K) :
    blockErrSq s l - w * blockEnergy l ≤ (l.length : Rat) * K := by
  induction l with
  | nil => simp [blockErrSq, blockEnergy]; grind
  | cons u xs ih =>
    simp only [blockErrSq, blockEnergy, List.length_cons, Rat.natCast_add]
    have hu := h u (List.Mem.head _)
    have hxs := ih (fun v hv => h v (List.Mem.tail _ hv))
    have hadd := rat_add_le_add hu hxs
    grind

/-- Sum a convex-combination coordinatewise upper bound over any list `l`. -/
theorem convex_blockErrSq_sub_wEnergy_le_len {s1 s2 lam w K : Rat} (l : List Rat)
    (h : ∀ u ∈ l, (1 - lam) * e2m1ErrSq s1 u + lam * e2m1ErrSq s2 u - w * sq u ≤ K) :
    (1 - lam) * blockErrSq s1 l + lam * blockErrSq s2 l - w * blockEnergy l ≤ (l.length : Rat) * K := by
  induction l with
  | nil => simp [blockErrSq, blockEnergy]; grind
  | cons u xs ih =>
    simp only [blockErrSq, blockEnergy, List.length_cons, Rat.natCast_add]
    have hu := h u (List.Mem.head _)
    have hxs := ih (fun v hv => h v (List.Mem.tail _ hv))
    have hadd := rat_add_le_add hu hxs
    grind

/-- Sum a coordinatewise upper bound `e_{c,s}(u) - w * u^2 ≤ K` over any list `l`. -/
theorem blockPlusErrSq_sub_wEnergy_le_len {c s w K : Rat} (l : List Rat)
    (h : ∀ u ∈ l, e2m1PlusErrSq c s u - w * sq u ≤ K) :
    blockPlusErrSq c s l - w * blockEnergy l ≤ (l.length : Rat) * K := by
  induction l with
  | nil => simp [blockPlusErrSq, blockEnergy]; grind
  | cons u xs ih =>
    simp only [blockPlusErrSq, blockEnergy, List.length_cons, Rat.natCast_add]
    have hu := h u (List.Mem.head _)
    have hxs := ih (fun v hv => h v (List.Mem.tail _ hv))
    have hadd := rat_add_le_add hu hxs
    grind

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

theorem rat_natCast_sub {m n : Nat} (h : n ≤ m) :
    ((m - n : Nat) : Rat) = (m : Rat) - (n : Rat) := by
  have hk : m = (m - n) + n := (Nat.sub_add_cancel h).symm
  have hcast : (m : Rat) = ((m - n : Nat) : Rat) + (n : Rat) := by
    rw [← Rat.natCast_add, ← hk]
  grind

/-! ### `min`, `absRat`, and Convex Quadratic Helpers -/

theorem rat_min_le_left (a b : Rat) : min a b ≤ a := by
  show (if a ≤ b then a else b) ≤ a
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem rat_min_le_right (a b : Rat) : min a b ≤ b := by
  show (if a ≤ b then a else b) ≤ b
  split
  · assumption
  · exact Rat.le_refl

theorem rat_le_min {a b c : Rat} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ min a b := by
  show c ≤ (if a ≤ b then a else b)
  split <;> assumption

theorem rat_min_eq_left {a b : Rat} (h : a ≤ b) : min a b = a := by
  show (if a ≤ b then a else b) = a
  split
  · rfl
  · rename_i hna; exact False.elim (hna h)

theorem rat_min_eq_right {a b : Rat} (h : b ≤ a) : min a b = b := by
  show (if a ≤ b then a else b) = b
  split
  · rename_i hab
    exact Rat.le_antisymm hab h
  · rfl

theorem rat_min_le_of_convex {a b c lam : Rat} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (h : (1 - lam) * a + lam * b ≤ c) : min a b ≤ c := by
  have h1 : (1 - lam) * min a b ≤ (1 - lam) * a :=
    rat_mul_le_mul_of_nonneg_left (rat_min_le_left a b) (rat_sub_nonneg hlam1)
  have h2 : lam * min a b ≤ lam * b :=
    rat_mul_le_mul_of_nonneg_left (rat_min_le_right a b) hlam0
  have hsum := rat_add_le_add h1 h2
  have hid : (1 - lam) * min a b + lam * min a b = min a b := by grind
  rw [hid] at hsum
  exact Rat.le_trans hsum h

theorem absRat_nonneg (u : Rat) : (0 : Rat) ≤ absRat u := by
  unfold absRat
  split
  · rename_i h
    have := rat_sub_nonneg (Rat.le_of_lt h)
    grind
  · rename_i h
    exact Rat.not_lt.mp h

theorem absRat_of_nonneg {u : Rat} (h : (0 : Rat) ≤ u) : absRat u = u := by
  unfold absRat
  split
  · rename_i hlt; exact False.elim (Rat.not_lt.mpr h hlt)
  · rfl

theorem sq_absRat (u : Rat) : sq (absRat u) = sq u := by
  unfold absRat sq
  split <;> grind

theorem sq_le_sq_of_abs_le {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) : sq a ≤ sq b := by
  unfold sq
  have hb : 0 ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (rat_mul_le_mul_of_nonneg_left hab ha) (rat_mul_le_mul_of_nonneg_right hab hb)

/-- Key convexity lemma: for any convex quadratic `f(u) = A*u^2 + B*u + C` with `A ≥ 0`,
    if `f(l) ≤ K` and `f(r) ≤ K` and `l ≤ u ≤ r`, then `f(u) ≤ K`. -/
theorem convex_quad_le_of_endpoints {A B C K l r u : Rat}
    (hA : 0 ≤ A) (hl : l ≤ u) (hr : u ≤ r)
    (hfl : A * (l * l) + B * l + C ≤ K)
    (hfr : A * (r * r) + B * r + C ≤ K) :
    A * (u * u) + B * u + C ≤ K := by
  by_cases hlr : l = r
  · have hu : u = l := Rat.le_antisymm (by rw [hlr]; exact hr) hl
    rw [hu]; exact hfl
  · have hpos : (0 : Rat) < r - l :=
      rat_sub_pos (Rat.lt_of_le_of_ne (Rat.le_trans hl hr) hlr)
    have ht1 : (0 : Rat) ≤ r - u := rat_sub_nonneg hr
    have ht2 : (0 : Rat) ≤ u - l := rat_sub_nonneg hl
    have hmul1 := rat_mul_le_mul_of_nonneg_left hfl ht1
    have hmul2 := rat_mul_le_mul_of_nonneg_left hfr ht2
    have hsum := rat_add_le_add hmul1 hmul2
    have hquad : (0 : Rat) ≤ A * (r - u) * (u - l) * (r - l) :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hA ht1) ht2) (Rat.le_of_lt hpos)
    have hstep : (A * (u * u) + B * u + C) * (r - l) + A * (r - u) * (u - l) * (r - l) =
        (r - u) * (A * (l * l) + B * l + C) + (u - l) * (A * (r * r) + B * r + C) := by
      grind
    have hbound : (A * (u * u) + B * u + C) * (r - l) ≤ K * (r - l) := by
      have h1 : (A * (u * u) + B * u + C) * (r - l) ≤
          (A * (u * u) + B * u + C) * (r - l) + A * (r - u) * (u - l) * (r - l) := by
        have := rat_add_le_add (Rat.le_refl (a := (A * (u * u) + B * u + C) * (r - l))) hquad
        rw [Rat.add_zero] at this
        exact this
      have h2 : (r - u) * K + (u - l) * K = K * (r - l) := by grind
      rw [hstep] at h1
      rw [h2] at hsum
      exact Rat.le_trans h1 hsum
    exact rat_le_of_mul_pos_right hpos hbound

/-! ### Exact `e2m1ErrSq` Bounds and Piecewise Evaluations -/

theorem e2m1ErrSq_le_0 (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - 0) :=
  rat_min_le_left _ _

theorem e2m1ErrSq_le_half (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - s * (1 / 2)) :=
  Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _)

theorem e2m1ErrSq_le_1 (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - s * 1) :=
  Rat.le_trans (rat_min_le_right _ _) (Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _))

theorem e2m1ErrSq_le_3half (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - s * (3 / 2)) :=
  Rat.le_trans (rat_min_le_right _ _)
    (Rat.le_trans (rat_min_le_right _ _)
      (Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _)))

theorem e2m1ErrSq_le_2 (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - s * 2) :=
  Rat.le_trans (rat_min_le_right _ _)
    (Rat.le_trans (rat_min_le_right _ _)
      (Rat.le_trans (rat_min_le_right _ _)
        (Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _))))

theorem e2m1ErrSq_le_3 (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - s * 3) :=
  Rat.le_trans (rat_min_le_right _ _)
    (Rat.le_trans (rat_min_le_right _ _)
      (Rat.le_trans (rat_min_le_right _ _)
        (Rat.le_trans (rat_min_le_right _ _)
          (Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _)))))

theorem e2m1ErrSq_le_4 (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - s * 4) :=
  Rat.le_trans (rat_min_le_right _ _)
    (Rat.le_trans (rat_min_le_right _ _)
      (Rat.le_trans (rat_min_le_right _ _)
        (Rat.le_trans (rat_min_le_right _ _)
          (Rat.le_trans (rat_min_le_right _ _)
            (Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _))))))

theorem e2m1ErrSq_le_6 (s u : Rat) : e2m1ErrSq s u ≤ sq (absRat u - s * 6) :=
  Rat.le_trans (rat_min_le_right _ _)
    (Rat.le_trans (rat_min_le_right _ _)
      (Rat.le_trans (rat_min_le_right _ _)
        (Rat.le_trans (rat_min_le_right _ _)
          (Rat.le_trans (rat_min_le_right _ _)
            (Rat.le_trans (rat_min_le_right _ _) (rat_min_le_right _ _))))))

theorem e2m1ErrSq_nonneg (s u : Rat) : (0 : Rat) ≤ e2m1ErrSq s u := by
  unfold e2m1ErrSq
  apply rat_le_min (rat_sq_nonneg _)
  apply rat_le_min (rat_sq_nonneg _)
  apply rat_le_min (rat_sq_nonneg _)
  apply rat_le_min (rat_sq_nonneg _)
  apply rat_le_min (rat_sq_nonneg _)
  apply rat_le_min (rat_sq_nonneg _)
  apply rat_le_min (rat_sq_nonneg _)
  exact rat_sq_nonneg _

theorem e2m1ErrSq_abs (s u : Rat) : e2m1ErrSq s (absRat u) = e2m1ErrSq s u := by
  unfold e2m1ErrSq
  rw [absRat_of_nonneg (absRat_nonneg u)]

theorem blockErrSq_nonneg (s : Rat) (x : List Rat) : (0 : Rat) ≤ blockErrSq s x := by
  induction x with
  | nil => exact Rat.le_refl
  | cons u xs ih => exact rat_add_nonneg (e2m1ErrSq_nonneg s u) ih

theorem blockEnergy_nonneg (x : List Rat) : (0 : Rat) ≤ blockEnergy x := by
  induction x with
  | nil => exact Rat.le_refl
  | cons u xs ih => exact rat_add_nonneg (rat_sq_nonneg u) ih

theorem blockEnergy_replicate (n : Nat) (u : Rat) :
    blockEnergy (List.replicate n u) = (n : Rat) * sq u := by
  induction n with
  | zero => simp [blockEnergy]
  | succ n ih =>
    simp [List.replicate_succ, blockEnergy, ih, Rat.natCast_add]
    grind

theorem blockErrSq_replicate (s : Rat) (n : Nat) (u : Rat) :
    blockErrSq s (List.replicate n u) = (n : Rat) * e2m1ErrSq s u := by
  induction n with
  | zero => simp [blockErrSq]
  | succ n ih =>
    simp [List.replicate_succ, blockErrSq, ih, Rat.natCast_add]
    grind

theorem blockPlusErrSq_replicate (c s : Rat) (n : Nat) (u : Rat) :
    blockPlusErrSq c s (List.replicate n u) = (n : Rat) * e2m1PlusErrSq c s u := by
  induction n with
  | zero => simp [blockPlusErrSq]
  | succ n ih =>
    simp [List.replicate_succ, blockPlusErrSq, ih, Rat.natCast_add]
    grind

/-- Helper: `(a - p)^2 ≤ (a - q)^2` when `2a ≤ p + q` and `p ≤ q`. -/
theorem sq_sub_le_of_le_mid {a p q : Rat} (hpq : p ≤ q) (hmid : 2 * a ≤ p + q) :
    sq (a - p) ≤ sq (a - q) := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ q - p := rat_sub_nonneg hpq
  have h2 : (0 : Rat) ≤ p + q - 2 * a := rat_sub_nonneg hmid
  have hmul := Rat.mul_nonneg h1 h2
  have hid : sq (a - q) - sq (a - p) = (q - p) * (p + q - 2 * a) := by unfold sq; grind
  rw [hid]; exact hmul

/-- Helper: `(a - q)^2 ≤ (a - p)^2` when `p + q ≤ 2a` and `p ≤ q`. -/
theorem sq_sub_le_of_mid_le {a p q : Rat} (hpq : p ≤ q) (hmid : p + q ≤ 2 * a) :
    sq (a - q) ≤ sq (a - p) := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ q - p := rat_sub_nonneg hpq
  have h2 : (0 : Rat) ≤ 2 * a - (p + q) := rat_sub_nonneg hmid
  have hmul := Rat.mul_nonneg h1 h2
  have hid : sq (a - p) - sq (a - q) = (q - p) * (2 * a - (p + q)) := by unfold sq; grind
  rw [hid]; exact hmul

/-- Exact saturation of `e2m1ErrSq s u` when `6 * s ≤ absRat u` and `0 ≤ s`. -/
theorem e2m1ErrSq_eq_top {s u : Rat} (hs : 0 ≤ s) (hu : s * 6 ≤ absRat u) :
    e2m1ErrSq s u = sq (absRat u - s * 6) := by
  apply Rat.le_antisymm (e2m1ErrSq_le_6 s u)
  unfold e2m1ErrSq
  have hle : ∀ q : Rat, q ≤ 6 → sq (absRat u - s * 6) ≤ sq (absRat u - s * q) := by
    intro q hq
    have hpq : s * q ≤ s * 6 := rat_mul_le_mul_of_nonneg_left hq hs
    have hmid : s * q + s * 6 ≤ 2 * absRat u := by
      have h2 := rat_add_le_add hpq (Rat.le_refl (a := s * 6))
      have h3 := rat_add_le_add hu hu
      have hid : s * 6 + s * 6 = 2 * (s * 6) := by grind
      have hid2 : absRat u + absRat u = 2 * absRat u := by grind
      rw [hid2] at h3
      exact Rat.le_trans h2 h3
    exact sq_sub_le_of_mid_le hpq hmid
  apply rat_le_min
  · have h0 := hle 0 (by grind)
    have hid : s * 0 = 0 := by grind
    rw [hid] at h0; exact h0
  apply rat_le_min (hle (1 / 2) (by grind))
  apply rat_le_min (hle 1 (by grind))
  apply rat_le_min (hle (3 / 2) (by grind))
  apply rat_le_min (hle 2 (by grind))
  apply rat_le_min (hle 3 (by grind))
  apply rat_le_min (hle 4 (by grind))
  exact Rat.le_refl

/-- Exact evaluation of `e2m1ErrSq 1 u` on `[3, 7/2]`. -/
theorem e2m1ErrSq_1_on_3_7half {u : Rat} (hlo : (3 : Rat) ≤ u) (hhi : u ≤ 7 / 2) :
    e2m1ErrSq 1 u = sq (u - 3) := by
  have hu0 : (0 : Rat) ≤ u := Rat.le_trans (by grind) hlo
  have habs : absRat u = u := absRat_of_nonneg hu0
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_3 1 u; rw [habs] at h; have hid : (1 : Rat) * 3 = 3 := by grind
    rw [hid] at h; exact h
  · unfold e2m1ErrSq; rw [habs]
    have hle_below : ∀ q : Rat, q ≤ 3 → sq (u - 3) ≤ sq (u - 1 * q) := by
      intro q hq
      have hmid : 1 * q + 3 ≤ 2 * u := by
        have h1 : (1 : Rat) * q ≤ 3 := by rw [Rat.one_mul]; exact hq
        have h2 := rat_add_le_add h1 (Rat.le_refl (a := (3 : Rat)))
        have h3 := rat_add_le_add hlo hlo
        have hid : u + u = 2 * u := by grind
        rw [hid] at h3
        exact Rat.le_trans h2 h3
      exact sq_sub_le_of_mid_le (by rw [Rat.one_mul]; exact hq) hmid
    have hle_above : ∀ q : Rat, 4 ≤ q → sq (u - 3) ≤ sq (u - 1 * q) := by
      intro q hq
      have hmid : 2 * u ≤ 3 + 1 * q := by
        have h1 : 2 * u ≤ 7 := by
          have := rat_mul_le_mul_of_nonneg_left hhi (by grind : (0 : Rat) ≤ 2)
          grind
        have h2 : (7 : Rat) ≤ 3 + 1 * q := by
          have := rat_add_le_add (Rat.le_refl (a := (3 : Rat))) hq
          grind
        exact Rat.le_trans h1 h2
      exact sq_sub_le_of_le_mid (by rw [Rat.one_mul]; exact Rat.le_trans (by grind) hq) hmid
    apply rat_le_min
    · have h0 := hle_below 0 (by grind); grind
    apply rat_le_min (hle_below (1 / 2) (by grind))
    apply rat_le_min (hle_below 1 (by grind))
    apply rat_le_min (hle_below (3 / 2) (by grind))
    apply rat_le_min (hle_below 2 (by grind))
    apply rat_le_min (by rw [Rat.one_mul]; exact Rat.le_refl)
    apply rat_le_min (hle_above 4 (by grind))
    exact hle_above 6 (by grind)

/-- Exact evaluation of `e2m1ErrSq 1 u` on `[7/2, 5]`. -/
theorem e2m1ErrSq_1_on_7half_5 {u : Rat} (hlo : (7 / 2 : Rat) ≤ u) (hhi : u ≤ 5) :
    e2m1ErrSq 1 u = sq (u - 4) := by
  have hu0 : (0 : Rat) ≤ u := Rat.le_trans (by grind) hlo
  have habs : absRat u = u := absRat_of_nonneg hu0
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_4 1 u; rw [habs] at h; have hid : (1 : Rat) * 4 = 4 := by grind
    rw [hid] at h; exact h
  · unfold e2m1ErrSq; rw [habs]
    have hle_below : ∀ q : Rat, q ≤ 3 → sq (u - 4) ≤ sq (u - 1 * q) := by
      intro q hq
      have hmid : 1 * q + 4 ≤ 2 * u := by
        have h1 : 1 * q + 4 ≤ 7 := by
          have := rat_add_le_add hq (Rat.le_refl (a := (4 : Rat))); grind
        have h2 : (7 : Rat) ≤ 2 * u := by
          have := rat_mul_le_mul_of_nonneg_left hlo (by grind : (0 : Rat) ≤ 2); grind
        exact Rat.le_trans h1 h2
      exact sq_sub_le_of_mid_le (by rw [Rat.one_mul]; exact Rat.le_trans hq (by grind)) hmid
    have hle_6 : sq (u - 4) ≤ sq (u - 1 * 6) := by
      have hmid : 2 * u ≤ 4 + 1 * 6 := by
        have := rat_mul_le_mul_of_nonneg_left hhi (by grind : (0 : Rat) ≤ 2); grind
      exact sq_sub_le_of_le_mid (by grind) hmid
    apply rat_le_min
    · have h0 := hle_below 0 (by grind); grind
    apply rat_le_min (hle_below (1 / 2) (by grind))
    apply rat_le_min (hle_below 1 (by grind))
    apply rat_le_min (hle_below (3 / 2) (by grind))
    apply rat_le_min (hle_below 2 (by grind))
    apply rat_le_min (hle_below 3 (by grind))
    apply rat_le_min (by rw [Rat.one_mul]; exact Rat.le_refl)
    exact hle_6

/-- Exact evaluation of `e2m1ErrSq 1 u` on `[5, ∞)`. -/
theorem e2m1ErrSq_1_on_ge_5 {u : Rat} (hlo : (5 : Rat) ≤ u) :
    e2m1ErrSq 1 u = sq (u - 6) := by
  have hu0 : (0 : Rat) ≤ u := Rat.le_trans (by grind) hlo
  have habs : absRat u = u := absRat_of_nonneg hu0
  apply Rat.le_antisymm
  · have h := e2m1ErrSq_le_6 1 u; rw [habs] at h; have hid : (1 : Rat) * 6 = 6 := by grind
    rw [hid] at h; exact h
  · unfold e2m1ErrSq; rw [habs]
    have hle_below : ∀ q : Rat, q ≤ 4 → sq (u - 6) ≤ sq (u - 1 * q) := by
      intro q hq
      have hmid : 1 * q + 6 ≤ 2 * u := by
        have h1 : 1 * q + 6 ≤ 10 := by
          have := rat_add_le_add hq (Rat.le_refl (a := (6 : Rat))); grind
        have h2 : (10 : Rat) ≤ 2 * u := by
          have := rat_mul_le_mul_of_nonneg_left hlo (by grind : (0 : Rat) ≤ 2); grind
        exact Rat.le_trans h1 h2
      exact sq_sub_le_of_mid_le (by rw [Rat.one_mul]; exact Rat.le_trans hq (by grind)) hmid
    apply rat_le_min
    · have h0 := hle_below 0 (by grind); grind
    apply rat_le_min (hle_below (1 / 2) (by grind))
    apply rat_le_min (hle_below 1 (by grind))
    apply rat_le_min (hle_below (3 / 2) (by grind))
    apply rat_le_min (hle_below 2 (by grind))
    apply rat_le_min (hle_below 3 (by grind))
    apply rat_le_min (hle_below 4 (by grind))
    have hid : (1 : Rat) * 6 = 6 := by grind
    rw [hid]; exact Rat.le_refl

end Mxfp4OptClipping
