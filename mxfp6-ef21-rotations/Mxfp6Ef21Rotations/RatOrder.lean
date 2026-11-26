/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp6Ef21Rotations.Defs

/-!
# Pure-`Init` `Rat` Order, Convexity, Finite Sums, and Generic Nearest-Grid Interval Bounds

Zero Mathlib, zero `native_decide`. Provides:
1. Elementary `Rat` order/algebra helpers (`rat_mul_le_mul_of_nonneg_*`, `rat_div_le_*`, `min`/`max`).
2. `absRat` and `symQuant` symmetry (`symQuant_sq_err_abs`).
3. `sumFinRat` monotonicity, additivity, scaling, and anchor-splitting (`sumFinRat_split_anchor`).
4. Convex quadratic endpoint maximum (`convex_quad_le_endpoints`) and generic recursive
   nearest-grid interval bound (`nearestNonneg_quad_le`).
-/

namespace Mxfp6Ef21Rotations

/-! ### 1. Elementary `Rat` Order and Field Helpers -/

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

theorem rat_div_le_of_mul_le {a b c : Rat} (hc : (0 : Rat) < c) (h : a ≤ b * c) :
    a / c ≤ b := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  apply rat_le_of_mul_pos_right hc
  have hdiv : (a / c) * c = a := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne, Rat.mul_one]
  rw [hdiv]
  exact h

theorem rat_le_div_of_mul_le {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c ≤ b) :
    a ≤ b / c := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  apply rat_le_of_mul_pos_right hc
  have hdiv : (b / c) * c = b := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne, Rat.mul_one]
  rw [hdiv]
  exact h

theorem rat_div_lt_div_of_cross {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d)
    (h : a * d < c * b) : a / b < c / d := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  have hbd : (0 : Rat) < b * d := rat_mul_pos hb hd
  have h1 : (a / b) * (b * d) = a * d := by
    rw [Rat.div_def, Rat.mul_assoc a b⁻¹, ← Rat.mul_assoc b⁻¹ b d,
        Rat.inv_mul_cancel b hbne, Rat.one_mul]
  have h2 : (c / d) * (b * d) = c * b := by
    rw [Rat.div_def, Rat.mul_comm b d, Rat.mul_assoc c d⁻¹, ← Rat.mul_assoc d⁻¹ d b,
        Rat.inv_mul_cancel d hdne, Rat.one_mul]
  cases Rat.le_total (a := c / d) (b := a / b) with
  | inl hge =>
    have hmul := rat_mul_le_mul_of_nonneg_right hge (Rat.le_of_lt hbd)
    rw [h1, h2] at hmul
    exact False.elim (Rat.not_le.mpr h hmul)
  | inr hle =>
    by_cases heq : a / b = c / d
    · have : (a / b) * (b * d) = (c / d) * (b * d) := by rw [heq]
      rw [h1, h2] at this
      exact False.elim (Rat.ne_of_lt h this)
    · exact Rat.lt_of_le_of_ne hle heq

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

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_min_le_left (a b : Rat) : min a b ≤ a := by
  change (if a ≤ b then a else b) ≤ a
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem rat_min_le_right (a b : Rat) : min a b ≤ b := by
  change (if a ≤ b then a else b) ≤ b
  split
  · rename_i h; exact h
  · exact Rat.le_refl

theorem rat_le_min {a b c : Rat} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ min a b := by
  change c ≤ (if a ≤ b then a else b)
  split
  · exact h1
  · exact h2

theorem rat_min_eq_left {a b : Rat} (h : a ≤ b) : min a b = a := by
  change (if a ≤ b then a else b) = a
  simp [h]

theorem rat_min_eq_right {a b : Rat} (h : b ≤ a) : min a b = b := by
  change (if a ≤ b then a else b) = b
  split
  · rename_i h'; exact Rat.le_antisymm h' h
  · rfl

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have h1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
      exact Rat.natCast_add n 1
    rw [h1]
    exact rat_add_nonneg ih (by decide)

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

theorem rat_div_eq_int {a b c : Rat} (hb : b ≠ 0) (h : a = c * b) : a / b = c := by
  rw [Rat.div_def, h, Rat.mul_assoc, Rat.mul_inv_cancel b hb, Rat.mul_one]

theorem rat_natCast_le {m n : Nat} (h : m ≤ n) : (m : Rat) ≤ (n : Rat) := by
  have hk : n = m + (n - m) := (Nat.add_sub_of_le h).symm
  rw [hk, Rat.natCast_add]
  have h0 : (0 : Rat) ≤ ((n - m : Nat) : Rat) := rat_natCast_nonneg (n - m)
  have h1 := rat_add_le_add (Rat.le_refl (a := (m : Rat))) h0
  rw [Rat.add_zero] at h1
  exact h1

theorem rat_natCast_pos {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) := by
  have h1 : (1 : Rat) ≤ (n : Rat) := rat_natCast_le h
  exact rat_lt_of_lt_of_le (by decide) h1

/-! ### 2. `absRat` and `symQuant` Symmetry -/

theorem absRat_nonneg (x : Rat) : (0 : Rat) ≤ absRat x := by
  unfold absRat
  split
  · rename_i h
    have := rat_sub_nonneg (Rat.le_of_lt h)
    grind
  · rename_i h
    exact Rat.not_lt.mp h

theorem absRat_sq (x : Rat) : absRat x * absRat x = x * x := by
  unfold absRat
  split <;> grind

theorem absRat_of_nonneg {x : Rat} (h : (0 : Rat) ≤ x) : absRat x = x := by
  unfold absRat
  have hn : ¬(x < 0) := Rat.not_lt.mpr h
  simp [hn]

theorem symQuant_sq_err_abs (levels : List Rat) (y : Rat) :
    (symQuant levels y - y) * (symQuant levels y - y) =
    (nearestNonneg levels (absRat y) - absRat y) *
    (nearestNonneg levels (absRat y) - absRat y) := by
  unfold symQuant absRat
  split <;> grind

/-! ### 3. `sumFinRat` Lemmas -/

theorem sumFinRat_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    sumFinRat n f = sumFinRat n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFinRat]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFinRat_add {n : Nat} (f g : Fin n → Rat) :
    sumFinRat n (fun i => f i + g i) = sumFinRat n f + sumFinRat n g := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ n ih =>
    simp only [sumFinRat]
    rw [ih]
    grind

theorem sumFinRat_sub {n : Nat} (f g : Fin n → Rat) :
    sumFinRat n (fun i => f i - g i) = sumFinRat n f - sumFinRat n g := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ n ih =>
    simp only [sumFinRat]
    rw [ih]
    grind

theorem sumFinRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumFinRat n (fun i => c * f i) = c * sumFinRat n f := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih =>
    simp only [sumFinRat]
    rw [ih]
    grind

theorem sumFinRat_const (n : Nat) (c : Rat) :
    sumFinRat n (fun _ => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih =>
    simp only [sumFinRat]
    rw [ih, Rat.natCast_add]
    grind

theorem sumFinRat_le {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    sumFinRat n f ≤ sumFinRat n g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [sumFinRat]
    exact rat_add_le_add (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem sumFinRat_single (n : Nat) (i0 : Fin n) (a b : Rat) :
    sumFinRat n (fun i => if i = i0 then a else b) = a + ((n - 1 : Nat) : Rat) * b := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ n ih =>
    simp only [sumFinRat]
    by_cases h : i0 = Fin.last n
    · subst h
      have hne : ∀ i : Fin n, i.castSucc ≠ Fin.last n := by
        intro i heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
      have hleft : sumFinRat n (fun i => if i.castSucc = Fin.last n then a else b) =
          sumFinRat n (fun _ => b) := by
        apply sumFinRat_congr
        intro i
        simp [hne i]
      rw [hleft, sumFinRat_const]
      simp only [ite_true]
      have hsub : n + 1 - 1 = n := by omega
      rw [hsub]
      grind
    · have hlt : i0.val < n := by
        have hlt1 := i0.isLt
        have hne_val : i0.val ≠ n := by
          intro hv
          apply h
          exact Fin.ext hv
        omega
      let j0 : Fin n := ⟨i0.val, hlt⟩
      have hleft : sumFinRat n (fun i => if i.castSucc = i0 then a else b) =
          sumFinRat n (fun i => if i = j0 then a else b) := by
        apply sumFinRat_congr
        intro i
        have hiff : (i.castSucc = i0) ↔ (i = j0) := by
          constructor
          · intro heq
            apply Fin.ext
            have hv := congrArg Fin.val heq
            simpa [Fin.val_castSucc, j0] using hv
          · intro heq
            apply Fin.ext
            have hv := congrArg Fin.val heq
            simpa [Fin.val_castSucc, j0] using hv
        simp only [hiff]
      have hlast : (if Fin.last n = i0 then a else b) = b := by
        have : Fin.last n ≠ i0 := Ne.symm h
        simp [this]
      rw [hleft, hlast, ih j0]
      have hn1 : 1 ≤ n := by omega
      have hcast : ((n : Nat) : Rat) = ((n - 1 : Nat) : Rat) + 1 := by
        have : n = (n - 1) + 1 := by omega
        conv => lhs; rw [this]
        rw [Rat.natCast_add]
        rfl
      have hsub : n + 1 - 1 = n := by omega
      rw [hsub, hcast]
      grind

/-- Anchor-splitting bound: if `f i0 ≤ A` and `f i ≤ C` for all `i ≠ i0`,
    then `sumFinRat B f ≤ A + (B - 1) * C`. -/
theorem sumFinRat_le_anchor {B : Nat} (i0 : Fin B) (f : Fin B → Rat) (A C : Rat)
    (hA : f i0 ≤ A) (hC : ∀ i, i ≠ i0 → f i ≤ C) :
    sumFinRat B f ≤ A + ((B - 1 : Nat) : Rat) * C := by
  have hle : sumFinRat B f ≤ sumFinRat B (fun i => if i = i0 then A else C) := by
    apply sumFinRat_le
    intro i
    by_cases h : i = i0
    · subst h; simpa using hA
    · simpa [h] using hC i h
  rw [sumFinRat_single B i0 A C] at hle
  exact hle

/-! ### 4. Convex Quadratic Endpoint Maximum & Generic Nearest-Grid Interval Bound -/

/-- For any `α ≥ 0` (`δ = 1 - α`) and `g : Rat`, the convex quadratic
    `φ(y) = (g - y)^2 - (1 - α) * y^2` on `[a, b]` attains its maximum at an endpoint `a` or `b`. -/
theorem convex_quad_le_endpoints {α g a b y C : Rat}
    (hα : (0 : Rat) ≤ α) (hay : a ≤ y) (hyb : y ≤ b)
    (ha : (g - a) * (g - a) - (1 - α) * (a * a) ≤ C)
    (hb : (g - b) * (g - b) - (1 - α) * (b * b) ≤ C) :
    (g - y) * (g - y) - (1 - α) * (y * y) ≤ C := by
  by_cases hab : a = b
  · have hy : y = a := Rat.le_antisymm (hab ▸ hyb) hay
    rw [hy]; exact ha
  · have hlt : a < b := Rat.lt_of_le_of_ne (Rat.le_trans hay hyb) hab
    have hba : (0 : Rat) < b - a := rat_sub_pos hlt
    have hya : (0 : Rat) ≤ y - a := rat_sub_nonneg hay
    have hby : (0 : Rat) ≤ b - y := rat_sub_nonneg hyb
    let φ : Rat → Rat := fun t => (g - t) * (g - t) - (1 - α) * (t * t)
    have hdiff : (b - a) * φ y - ((b - y) * φ a + (y - a) * φ b) =
        -(α * (b - a) * (y - a) * (b - y)) := by
      dsimp only [φ]
      grind
    have hprod_nonneg : (0 : Rat) ≤ α * (b - a) * (y - a) * (b - y) := by
      have h1 : (0 : Rat) ≤ α * (b - a) := Rat.mul_nonneg hα (Rat.le_of_lt hba)
      have h2 : (0 : Rat) ≤ α * (b - a) * (y - a) := Rat.mul_nonneg h1 hya
      exact Rat.mul_nonneg h2 hby
    have hle1 : (b - a) * φ y ≤ (b - y) * φ a + (y - a) * φ b := by
      apply rat_le_of_sub_nonneg
      have heq : (b - y) * φ a + (y - a) * φ b - (b - a) * φ y =
          α * (b - a) * (y - a) * (b - y) := by grind
      rw [heq]
      exact hprod_nonneg
    have hle2 : (b - y) * φ a + (y - a) * φ b ≤ (b - a) * C := by
      have h1 : (b - y) * φ a ≤ (b - y) * C := rat_mul_le_mul_of_nonneg_left ha hby
      have h2 : (y - a) * φ b ≤ (y - a) * C := rat_mul_le_mul_of_nonneg_left hb hya
      have h3 := rat_add_le_add h1 h2
      have heq : (b - y) * C + (y - a) * C = (b - a) * C := by grind
      rw [heq] at h3
      exact h3
    have hle3 : φ y * (b - a) ≤ C * (b - a) := by
      have h := Rat.le_trans hle1 hle2
      grind
    exact rat_le_of_mul_pos_right hba hle3

/-- Sortedness predicate for a list of grid levels. -/
def isSorted : List Rat → Prop
  | [] => True
  | [_] => True
  | g1 :: g2 :: rest => g1 ≤ g2 ∧ isSorted (g2 :: rest)

/-- Last element of a list of grid levels (0 if empty). -/
def lastLevel : List Rat → Rat
  | [] => 0
  | [g] => g
  | _ :: g2 :: rest => lastLevel (g2 :: rest)

/-- Recursive endpoint + midpoint quadratic bound on every interval of `levels`. -/
def gridQuadBound (α C : Rat) : List Rat → Prop
  | [] => True
  | [g] => -(1 - α) * (g * g) ≤ C
  | g1 :: g2 :: rest =>
    (-(1 - α) * (g1 * g1) ≤ C) ∧
    (((g2 - g1) / 2) * ((g2 - g1) / 2) - (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2)) ≤ C) ∧
    gridQuadBound α C (g2 :: rest)

theorem nearestNonneg_eq_head_of_le {g : Rat} {rest : List Rat} {y : Rat}
    (hs : isSorted (g :: rest)) (hy : y ≤ g) :
    nearestNonneg (g :: rest) y = g := by
  cases rest with
  | nil => rfl
  | cons g2 rest' =>
    simp only [nearestNonneg]
    have hle : g ≤ g2 := hs.1
    have hmid : y ≤ (g + g2) / 2 := by
      have h1 : g ≤ (g + g2) / 2 := by
        apply rat_le_div_of_mul_le (by decide)
        have := rat_add_le_add (Rat.le_refl (a := g)) hle
        grind
      exact Rat.le_trans hy h1
    simp [hmid]

/-- Generic universal 1D nearest-grid quadratic bound:
    if `0 ≤ α`, `levels = g0 :: rest` is sorted, `g0 ≤ y ≤ lastLevel (g0 :: rest)`,
    and `gridQuadBound α C (g0 :: rest)` holds, then
    `(nearestNonneg (g0 :: rest) y - y)^2 - (1 - α) * y^2 ≤ C`. -/
theorem nearestNonneg_quad_le {α C : Rat} (hα : (0 : Rat) ≤ α) :
    ∀ (levels : List Rat),
      isSorted levels →
      gridQuadBound α C levels →
      ∀ (g0 : Rat) (rest : List Rat), levels = g0 :: rest →
        ∀ (y : Rat), g0 ≤ y → y ≤ lastLevel (g0 :: rest) →
          (nearestNonneg (g0 :: rest) y - y) * (nearestNonneg (g0 :: rest) y - y) -
            (1 - α) * (y * y) ≤ C := by
  intro levels
  induction levels with
  | nil =>
    intro _ _ _ _ heq
    cases heq
  | cons g1 tl ih =>
    intro hsort hbound g0 rest heq y hy_lo hy_hi
    cases heq
    cases tl with
    | nil =>
      simp only [lastLevel] at hy_hi
      have hy : y = g1 := Rat.le_antisymm hy_hi hy_lo
      rw [hy]
      simp only [nearestNonneg]
      have h0 : (g1 - g1) * (g1 - g1) - (1 - α) * (g1 * g1) = -(1 - α) * (g1 * g1) := by grind
      rw [h0]
      exact hbound
    | cons g2 rest' =>
      have h12 : g1 ≤ g2 := hsort.1
      have hsort2 : isSorted (g2 :: rest') := hsort.2
      have hg1_bd : -(1 - α) * (g1 * g1) ≤ C := hbound.1
      have hmid_bd : ((g2 - g1) / 2) * ((g2 - g1) / 2) -
          (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2)) ≤ C := hbound.2.1
      have hbound2 : gridQuadBound α C (g2 :: rest') := hbound.2.2
      let m : Rat := (g1 + g2) / 2
      have hg1_m : g1 ≤ m := by
        apply rat_le_div_of_mul_le (by decide)
        have := rat_add_le_add (Rat.le_refl (a := g1)) h12
        grind
      have hm_g2 : m ≤ g2 := by
        apply rat_div_le_of_mul_le (by decide)
        have := rat_add_le_add h12 (Rat.le_refl (a := g2))
        grind
      by_cases hym : y ≤ m
      · have hq : nearestNonneg (g1 :: g2 :: rest') y = g1 := by
          simp only [nearestNonneg]
          simp [m] at hym
          simp [hym]
        rw [hq]
        apply convex_quad_le_endpoints hα hy_lo hym
        · have heq0 : (g1 - g1) * (g1 - g1) - (1 - α) * (g1 * g1) = -(1 - α) * (g1 * g1) := by grind
          rw [heq0]; exact hg1_bd
        · have heqm : (g1 - m) * (g1 - m) - (1 - α) * (m * m) =
              ((g2 - g1) / 2) * ((g2 - g1) / 2) -
              (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2)) := by
            dsimp only [m]; grind
          rw [heqm]; exact hmid_bd
      · have hq_step : nearestNonneg (g1 :: g2 :: rest') y = nearestNonneg (g2 :: rest') y := by
          simp only [nearestNonneg]
          simp [m] at hym
          simp [hym]
        rw [hq_step]
        have hmy : m ≤ y := Rat.le_of_lt (Rat.not_le.mp hym)
        by_cases hyg2 : y ≤ g2
        · have hq2 : nearestNonneg (g2 :: rest') y = g2 :=
            nearestNonneg_eq_head_of_le hsort2 hyg2
          rw [hq2]
          have hg2_bd : -(1 - α) * (g2 * g2) ≤ C := by
            cases rest' with
            | nil => exact hbound2
            | cons _ _ => exact hbound2.1
          apply convex_quad_le_endpoints hα hmy hyg2
          · have heqm : (g2 - m) * (g2 - m) - (1 - α) * (m * m) =
                ((g2 - g1) / 2) * ((g2 - g1) / 2) -
                (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2)) := by
              dsimp only [m]; grind
            rw [heqm]; exact hmid_bd
          · have heq2 : (g2 - g2) * (g2 - g2) - (1 - α) * (g2 * g2) = -(1 - α) * (g2 * g2) := by grind
            rw [heq2]; exact hg2_bd
        · have hg2y : g2 ≤ y := Rat.le_of_lt (Rat.not_le.mp hyg2)
          have hlast_eq : lastLevel (g1 :: g2 :: rest') = lastLevel (g2 :: rest') := rfl
          rw [hlast_eq] at hy_hi
          exact ih hsort2 hbound2 g2 rest' rfl y hg2y hy_hi

/-- Dropping a prefix of `nearestNonneg` when `y` exceeds all dropped midpoints. -/
theorem nearestNonneg_drop_cons {g1 g2 : Rat} {rest : List Rat} {y : Rat}
    (h : (g1 + g2) / 2 < y) :
    nearestNonneg (g1 :: g2 :: rest) y = nearestNonneg (g2 :: rest) y := by
  simp only [nearestNonneg]
  have hn : ¬(y ≤ (g1 + g2) / 2) := Rat.not_le.mpr h
  simp [hn]

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

/-- Pure-`Nat` mirror of `nearestNonneg` on `ns.map (fun k => k / D)` at `y = p / q`. -/
def nearestNonnegNat (D : Nat) : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | [g], _, _ => g
  | g1 :: g2 :: rest, p, q =>
    if 2 * D * p ≤ q * (g1 + g2) then g1 else nearestNonnegNat D (g2 :: rest) p q

theorem nearestNonneg_map_div (D p q : Nat) (hD : 0 < D) (hq : 0 < q) (ns : List Nat) :
    nearestNonneg (ns.map (fun (k : Nat) => (k : Rat) / (D : Rat))) ((p : Rat) / (q : Rat)) =
    ((nearestNonnegNat D ns p q : Nat) : Rat) / (D : Rat) := by
  have hDpos : (0 : Rat) < (D : Rat) := rat_natCast_pos hD
  have hDne : (D : Rat) ≠ 0 := Rat.ne_of_gt hDpos
  have hqpos : (0 : Rat) < (q : Rat) := rat_natCast_pos hq
  have h2D : (0 : Rat) < 2 * (D : Rat) := rat_mul_pos (by decide) hDpos
  induction ns with
  | nil =>
    simp only [List.map, nearestNonneg, nearestNonnegNat]
    have h0 : ((0 : Nat) : Rat) / (D : Rat) = 0 := by rw [Rat.div_def]; simp
    exact h0.symm
  | cons g1 tl ih =>
    cases tl with
    | nil => rfl
    | cons g2 rest =>
      simp only [List.map, nearestNonneg, nearestNonnegNat]
      have hmid_eq : ((g1 : Rat) / (D : Rat) + (g2 : Rat) / (D : Rat)) / 2 =
          ((g1 : Rat) + (g2 : Rat)) / (2 * (D : Rat)) := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
        have h2D_inv : (2 * (D : Rat))⁻¹ = (2 : Rat)⁻¹ * (D : Rat)⁻¹ := by
          have hmul : ((2 * (D : Rat))⁻¹ - (2 : Rat)⁻¹ * (D : Rat)⁻¹) * (2 * (D : Rat)) = 0 := by
            have h2inv : (2 : Rat)⁻¹ * 2 = 1 := Rat.inv_mul_cancel 2 (by decide)
            have hDinv : (D : Rat)⁻¹ * (D : Rat) = 1 := Rat.inv_mul_cancel _ hDne
            have h2Dinv : (2 * (D : Rat))⁻¹ * (2 * (D : Rat)) = 1 :=
              Rat.inv_mul_cancel _ (Rat.ne_of_gt h2D)
            grind
          cases Rat.mul_eq_zero.mp hmul with
          | inl h0 => grind
          | inr h0 => exact False.elim (Rat.ne_of_gt h2D h0)
        rw [h2D_inv]; grind
      rw [hmid_eq]
      have hiff : ((p : Rat) / (q : Rat) ≤ ((g1 : Rat) + (g2 : Rat)) / (2 * (D : Rat))) ↔
          (2 * D * p ≤ q * (g1 + g2)) := by
        constructor
        · intro hle
          have hmul := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt (rat_mul_pos hqpos h2D))
          have hL : (p : Rat) / (q : Rat) * ((q : Rat) * (2 * (D : Rat))) =
              (2 * (D : Rat)) * (p : Rat) := by
            rw [Rat.div_def, Rat.mul_assoc (p : Rat) (q : Rat)⁻¹, ← Rat.mul_assoc (q : Rat)⁻¹ (q : Rat),
                Rat.inv_mul_cancel _ (Rat.ne_of_gt hqpos), Rat.one_mul, Rat.mul_comm]
          have hR : ((g1 : Rat) + (g2 : Rat)) / (2 * (D : Rat)) * ((q : Rat) * (2 * (D : Rat))) =
              (q : Rat) * ((g1 : Rat) + (g2 : Rat)) := by
            rw [Rat.div_def, Rat.mul_comm (q : Rat) (2 * (D : Rat)),
                Rat.mul_assoc _ (2 * (D : Rat))⁻¹, ← Rat.mul_assoc (2 * (D : Rat))⁻¹,
                Rat.inv_mul_cancel _ (Rat.ne_of_gt h2D), Rat.one_mul, Rat.mul_comm]
          rw [hL, hR] at hmul
          have hcastL : (2 * (D : Rat)) * (p : Rat) = (((2 * D * p : Nat) : Int) : Rat) := by
            rw [Rat.intCast_natCast, Rat.natCast_mul, Rat.natCast_mul]; rfl
          have hcastR : (q : Rat) * ((g1 : Rat) + (g2 : Rat)) = (((q * (g1 + g2) : Nat) : Int) : Rat) := by
            rw [Rat.intCast_natCast, Rat.natCast_mul, Rat.natCast_add]
          rw [hcastL, hcastR] at hmul
          have hint := Rat.intCast_le_intCast.mp hmul
          omega
        · intro hnat
          apply rat_div_le_div_of_cross hqpos h2D
          have hc := rat_natCast_le hnat
          rw [Rat.natCast_mul, Rat.natCast_mul, Rat.natCast_mul, Rat.natCast_add] at hc
          have heqL : (p : Rat) * (2 * (D : Rat)) = ((2 : Nat) : Rat) * (D : Rat) * (p : Rat) := by grind
          have heqR : ((g1 : Rat) + (g2 : Rat)) * (q : Rat) = (q : Rat) * ((g1 : Rat) + (g2 : Rat)) := by grind
          rw [heqL, heqR]; exact hc
      by_cases h : 2 * D * p ≤ q * (g1 + g2)
      · have h' : (p : Rat) / (q : Rat) ≤ ((g1 : Rat) + (g2 : Rat)) / (2 * (D : Rat)) := hiff.mpr h
        simp only [h, h', ↓reduceIte]
      · have h' : ¬((p : Rat) / (q : Rat) ≤ ((g1 : Rat) + (g2 : Rat)) / (2 * (D : Rat))) :=
          fun hx => h (hiff.mp hx)
        simp only [h, h', ↓reduceIte]
        exact ih

theorem rat_div_nonneg_nat (p q : Nat) (hq : 0 < q) : (0 : Rat) ≤ (p : Rat) / (q : Rat) :=
  rat_div_nonneg (rat_natCast_nonneg p) (rat_natCast_pos hq)

theorem rat_div_pos_nat (p q : Nat) (hp : 0 < p) (hq : 0 < q) : (0 : Rat) < (p : Rat) / (q : Rat) :=
  rat_div_pos (rat_natCast_pos hp) (rat_natCast_pos hq)

theorem rat_div_le_div_nat (a b c d : Nat) (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := by
  apply rat_div_le_div_of_cross (rat_natCast_pos hb) (rat_natCast_pos hd)
  have hc := rat_natCast_le h
  rw [Rat.natCast_mul, Rat.natCast_mul] at hc
  exact hc

theorem rat_div_lt_div_nat (a b c d : Nat) (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) :
    (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  apply rat_div_lt_div_of_cross (rat_natCast_pos hb) (rat_natCast_pos hd)
  have hle : ((a * d : Nat) : Rat) ≤ ((c * b : Nat) : Rat) := rat_natCast_le (Nat.le_of_lt h)
  have hne : ((a * d : Nat) : Rat) ≠ ((c * b : Nat) : Rat) := by
    intro heq
    have hint : (((a * d : Nat) : Int) : Rat) = (((c * b : Nat) : Int) : Rat) := by
      simpa [Rat.intCast_natCast] using heq
    have := Rat.intCast_inj.mp hint
    omega
  rw [Rat.natCast_mul, Rat.natCast_mul] at hle hne
  exact Rat.lt_of_le_of_ne hle hne

def e2m1Nums : List Nat := [0, 1, 2, 3, 4, 6, 8, 12]

def e3m2Nums : List Nat :=
  [ 0, 1, 2, 3,
    4, 5, 6, 7,
    8, 10, 12, 14,
    16, 20, 24, 28,
    32, 40, 48, 56,
    64, 80, 96, 112,
    128, 160, 192, 224,
    256, 320, 384, 448 ]

def e2m3Nums : List Nat :=
  [ 0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14, 15,
    16, 18, 20, 22, 24, 26, 28, 30,
    32, 36, 40, 44, 48, 52, 56, 60 ]

theorem e2m1Levels_eq_map :
    e2m1Levels = e2m1Nums.map (fun (k : Nat) => (k : Rat) / 2) := by
  simp only [e2m1Levels, e2m1Nums, List.map, List.cons.injEq, and_true]
  repeat (first
    | exact rat_div_eq_of_cross (by decide) (by decide) (by grind)
    | exact (rat_div_eq_int (by decide) (by grind)).symm
    | constructor)

theorem e3m2Levels_eq_map :
    e3m2Levels = e3m2Nums.map (fun (k : Nat) => (k : Rat) / 16) := by
  simp only [e3m2Levels, e3m2Nums, List.map, List.cons.injEq, and_true]
  repeat (first
    | exact rat_div_eq_of_cross (by decide) (by decide) (by grind)
    | exact (rat_div_eq_int (by decide) (by grind)).symm
    | constructor)

theorem e2m3Levels_eq_map :
    e2m3Levels = e2m3Nums.map (fun (k : Nat) => (k : Rat) / 8) := by
  simp only [e2m3Levels, e2m3Nums, List.map, List.cons.injEq, and_true]
  repeat (first
    | exact rat_div_eq_of_cross (by decide) (by decide) (by grind)
    | exact (rat_div_eq_int (by decide) (by grind)).symm
    | constructor)

end Mxfp6Ef21Rotations
