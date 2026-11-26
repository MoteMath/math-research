/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NsaBallBoundMoba.Defs

/-!
# Pure-`Init` `Int` / `Rat` Finite-Sum, Order, and Cauchy–Schwarz Helpers

Zero Mathlib, zero `native_decide`. Provides exact algebraic linearity for
`intFinSum` / `finSum`, `Rat` order helpers, and universal Cauchy–Schwarz
inequalities over both `Int` and `Rat` for arbitrary dimension `d : Nat`.
-/

namespace NsaBallBoundMoba

/-! ### `intFinSum` Algebraic Lemmas -/

theorem intFinSumAux_congr {k : Nat} {f g : Fin k → Int} (h : ∀ j, f j = g j) :
    intFinSumAux k f = intFinSumAux k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [intFinSumAux]
    rw [ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem intFinSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ j, f j = g j) :
    intFinSum f = intFinSum g :=
  intFinSumAux_congr h

theorem intFinSum_zero (n : Nat) : intFinSum (fun _ : Fin n => (0 : Int)) = 0 := by
  unfold intFinSum
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [intFinSumAux]
    rw [ih]
    omega

theorem intFinSum_const (n : Nat) (c : Int) :
    intFinSum (fun _ : Fin n => c) = (n : Int) * c := by
  unfold intFinSum
  induction n with
  | zero => simp [intFinSumAux]
  | succ k ih =>
    simp only [intFinSumAux]
    rw [ih]
    grind

theorem intFinSum_add {n : Nat} (f g : Fin n → Int) :
    intFinSum (fun j => f j + g j) = intFinSum f + intFinSum g := by
  unfold intFinSum
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [intFinSumAux]
    rw [ih]
    omega

theorem intFinSum_sub {n : Nat} (f g : Fin n → Int) :
    intFinSum (fun j => f j - g j) = intFinSum f - intFinSum g := by
  unfold intFinSum
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [intFinSumAux]
    rw [ih]
    omega

theorem intFinSum_mul_left {n : Nat} (a : Int) (f : Fin n → Int) :
    intFinSum (fun j => a * f j) = a * intFinSum f := by
  unfold intFinSum
  induction n with
  | zero => simp [intFinSumAux]
  | succ k ih =>
    simp only [intFinSumAux]
    rw [ih]
    grind

theorem intFinSum_mul_right {n : Nat} (f : Fin n → Int) (a : Int) :
    intFinSum (fun j => f j * a) = intFinSum f * a := by
  unfold intFinSum
  induction n with
  | zero => simp [intFinSumAux]
  | succ k ih =>
    simp only [intFinSumAux]
    rw [ih]
    grind

theorem intFinSum_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ j, 0 ≤ f j) :
    0 ≤ intFinSum f := by
  unfold intFinSum
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [intFinSumAux]
    have h1 := ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

theorem intFinSum_le_intFinSum {n : Nat} {f g : Fin n → Int} (h : ∀ j, f j ≤ g j) :
    intFinSum f ≤ intFinSum g := by
  unfold intFinSum
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [intFinSumAux]
    have h1 := ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

theorem intFinSum_single {n : Nat} (i : Fin n) (v : Int) :
    intFinSum (fun j : Fin n => if j.val = i.val then v else 0) = v := by
  unfold intFinSum
  induction n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    simp only [intFinSumAux]
    by_cases hi : i.val = k
    · have hzero : intFinSumAux k (fun j => if j.val = i.val then v else 0) = 0 := by
        have hcongr : intFinSumAux k (fun j => if j.val = i.val then v else 0) =
            intFinSumAux k (fun _ => (0 : Int)) := by
          apply intFinSumAux_congr
          intro j
          have hj : j.val ≠ i.val := by omega
          simp [hj]
        rw [hcongr]
        exact intFinSum_zero k
      rw [hzero]
      simp [hi]
    · have hik : i.val < k := by omega
      have hih := ih ⟨i.val, hik⟩
      simp only [hih]
      have hne : k ≠ i.val := by omega
      simp [hne]

theorem intFinSum_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    intFinSum (fun i => intFinSum (fun j => f i j)) =
    intFinSum (fun j => intFinSum (fun i => f i j)) := by
  induction m with
  | zero =>
    unfold intFinSum
    simp only [intFinSumAux]
    exact (intFinSum_zero n).symm
  | succ k ih =>
    change intFinSumAux (k + 1) (fun i => intFinSum (fun j => f i j)) =
           intFinSum (fun j => intFinSumAux (k + 1) (fun i => f i j))
    simp only [intFinSumAux]
    rw [intFinSum_add]
    have hih := ih (fun i j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j)
    exact congrArg (· + intFinSum (fun j => f ⟨k, Nat.lt_succ_self k⟩ j)) hih

/-! ### `intFinMaxNonneg` Lemmas -/

theorem intFinMaxNonnegAux_nonneg {k : Nat} (f : Fin k → Int) :
    0 ≤ intFinMaxNonnegAux k f := by
  induction k with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [intFinMaxNonnegAux]
    have h := ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    omega

theorem intFinMaxNonneg_nonneg {n : Nat} (f : Fin n → Int) :
    0 ≤ intFinMaxNonneg f :=
  intFinMaxNonnegAux_nonneg f

theorem le_intFinMaxNonnegAux {k : Nat} (f : Fin k → Int) (j : Fin k) :
    f j ≤ intFinMaxNonnegAux k f := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    simp only [intFinMaxNonnegAux]
    by_cases hj : j.val = k
    · have heq : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hj
      rw [heq]
      omega
    · have hlt : j.val < k := by omega
      have h1 := ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ⟨j.val, hlt⟩
      have heq : (⟨j.val, Nat.lt_succ_of_lt hlt⟩ : Fin (k + 1)) = j := Fin.ext rfl
      rw [heq] at h1
      omega

theorem le_intFinMaxNonneg {n : Nat} (f : Fin n → Int) (j : Fin n) :
    f j ≤ intFinMaxNonneg f :=
  le_intFinMaxNonnegAux f j

theorem intFinMaxNonnegAux_le {k : Nat} {f : Fin k → Int} {M : Int}
    (h0 : 0 ≤ M) (h : ∀ j, f j ≤ M) : intFinMaxNonnegAux k f ≤ M := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    simp only [intFinMaxNonnegAux]
    have h1 := ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

theorem intFinMaxNonneg_le {n : Nat} {f : Fin n → Int} {M : Int}
    (h0 : 0 ≤ M) (h : ∀ j, f j ≤ M) : intFinMaxNonneg f ≤ M :=
  intFinMaxNonnegAux_le h0 h

/-! ### Exact `Int` Inner Product & Universal Cauchy–Schwarz Inequality -/

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have hneg : 0 ≤ -x := by omega
    have heq : x * x = (-x) * (-x) := by grind
    rw [heq]
    exact Int.mul_nonneg hneg hneg

theorem normSqInt_nonneg {d : Nat} (v : Fin d → Int) : 0 ≤ normSqInt v := by
  unfold normSqInt dotInt
  exact intFinSum_nonneg (fun c => int_sq_nonneg (v c))

theorem dotInt_add_right {d : Nat} (u v w : Fin d → Int) :
    dotInt u (fun c => v c + w c) = dotInt u v + dotInt u w := by
  unfold dotInt
  have h : intFinSum (fun c => u c * (v c + w c)) =
      intFinSum (fun c => u c * v c + u c * w c) := by
    apply intFinSum_congr
    intro c
    grind
  rw [h, intFinSum_add]

theorem dotInt_sub_right {d : Nat} (u v w : Fin d → Int) :
    dotInt u (fun c => v c - w c) = dotInt u v - dotInt u w := by
  unfold dotInt
  have h : intFinSum (fun c => u c * (v c - w c)) =
      intFinSum (fun c => u c * v c - u c * w c) := by
    apply intFinSum_congr
    intro c
    grind
  rw [h, intFinSum_sub]

theorem dotInt_smul_right {d : Nat} (a : Int) (u v : Fin d → Int) :
    dotInt u (fun c => a * v c) = a * dotInt u v := by
  unfold dotInt
  have h : intFinSum (fun c => u c * (a * v c)) =
      intFinSum (fun c => a * (u c * v c)) := by
    apply intFinSum_congr
    intro c
    grind
  rw [h, intFinSum_mul_left]

theorem dotInt_zero_right {d : Nat} (u : Fin d → Int) :
    dotInt u (fun _ => 0) = 0 := by
  unfold dotInt
  have h : intFinSum (fun c => u c * (0 : Int)) = intFinSum (fun _ : Fin d => (0 : Int)) := by
    apply intFinSum_congr
    intro c
    grind
  rw [h, intFinSum_zero]

theorem dotInt_blockSum {d B : Nat} (q : Fin d → Int) (ks : Fin B → Fin d → Int) :
    dotInt q (blockSum ks) = intFinSum (fun j => dotInt q (ks j)) := by
  unfold dotInt blockSum
  have h1 : intFinSum (fun c => q c * intFinSum (fun j => ks j c)) =
      intFinSum (fun c => intFinSum (fun j => q c * ks j c)) := by
    apply intFinSum_congr
    intro c
    exact (intFinSum_mul_left (q c) (fun j => ks j c)).symm
  rw [h1, intFinSum_swap]

/-- Helper step for Cauchy–Schwarz induction over `Int`. -/
theorem cauchy_schwarz_int_step {U V S a b : Int}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hCS : S * S ≤ U * V) :
    (S + a * b) * (S + a * b) ≤ (U + a * a) * (V + b * b) := by
  have hcross : 0 ≤ U * (b * b) + V * (a * a) - 2 * S * a * b := by
    by_cases hU0 : U = 0
    · subst hU0
      have hS0 : S * S ≤ 0 := by grind
      have hSge : 0 ≤ S * S := int_sq_nonneg S
      have hSS : S * S = 0 := by omega
      have hS : S = 0 := by
        cases Int.mul_eq_zero.mp hSS with
        | inl h => exact h
        | inr h => exact h
      subst hS
      have ha2 : 0 ≤ a * a := int_sq_nonneg a
      have hVa2 : 0 ≤ V * (a * a) := Int.mul_nonneg hV ha2
      grind
    · have hUpos : 0 < U := by omega
      have h1 : 0 ≤ (U * b - S * a) * (U * b - S * a) := int_sq_nonneg (U * b - S * a)
      have h2 : 0 ≤ (U * V - S * S) * (a * a) :=
        Int.mul_nonneg (by omega) (int_sq_nonneg a)
      have hprod : 0 ≤ U * (U * (b * b) + V * (a * a) - 2 * S * a * b) := by
        have hid : U * (U * (b * b) + V * (a * a) - 2 * S * a * b) =
            (U * b - S * a) * (U * b - S * a) + (U * V - S * S) * (a * a) := by grind
        rw [hid]
        omega
      by_cases hneg : U * (b * b) + V * (a * a) - 2 * S * a * b < 0
      · have hlt : U * (U * (b * b) + V * (a * a) - 2 * S * a * b) < 0 := by
          have hpos_neg : 0 < -(U * (b * b) + V * (a * a) - 2 * S * a * b) := by omega
          have hmul_pos : 0 < U * (-(U * (b * b) + V * (a * a) - 2 * S * a * b)) :=
            Int.mul_pos hUpos hpos_neg
          grind
        omega
      · omega
  have hdiff : (U + a * a) * (V + b * b) - (S + a * b) * (S + a * b) =
      (U * V - S * S) + (U * (b * b) + V * (a * a) - 2 * S * a * b) := by grind
  omega

/-- Universal Cauchy–Schwarz inequality over `ℤ^d` for ALL dimensions `d : Nat`. -/
theorem cauchy_schwarz_int {d : Nat} (u v : Fin d → Int) :
    dotInt u v * dotInt u v ≤ normSqInt u * normSqInt v := by
  unfold dotInt normSqInt dotInt intFinSum
  induction d with
  | zero => simp [intFinSumAux]
  | succ k ih =>
    simp only [intFinSumAux]
    have hU : 0 ≤ intFinSumAux k (fun c => u ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩ *
                                           u ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩) :=
      intFinSum_nonneg (fun c => int_sq_nonneg _)
    have hV : 0 ≤ intFinSumAux k (fun c => v ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩ *
                                           v ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩) :=
      intFinSum_nonneg (fun c => int_sq_nonneg _)
    have hCS := ih (fun c => u ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩)
                   (fun c => v ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩)
    exact cauchy_schwarz_int_step hU hV hCS

/-- Exact parallelogram upper bound `‖u + v‖_2^2 ≤ 2(‖u‖_2^2 + ‖v‖_2^2)` over `ℤ^d`. -/
theorem normSqInt_add_le_two_mul {d : Nat} (u v : Fin d → Int) :
    normSqInt (fun c => u c + v c) ≤ 2 * (normSqInt u + normSqInt v) := by
  have hdiff : 2 * (normSqInt u + normSqInt v) - normSqInt (fun c => u c + v c) =
      normSqInt (fun c => u c - v c) := by
    unfold normSqInt dotInt
    rw [← intFinSum_add, ← intFinSum_mul_left, ← intFinSum_sub]
    apply intFinSum_congr
    intro c
    grind
  have hnn : 0 ≤ normSqInt (fun c => u c - v c) := normSqInt_nonneg _
  omega

/-- Exact squared-norm expansion `‖u + v‖_2^2 = ‖u‖_2^2 + 2 u^T v + ‖v‖_2^2`. -/
theorem normSqInt_add_eq {d : Nat} (u v : Fin d → Int) :
    normSqInt (fun c => u c + v c) = normSqInt u + 2 * dotInt u v + normSqInt v := by
  unfold normSqInt dotInt
  have h1 : intFinSum (fun c => (u c + v c) * (u c + v c)) =
      intFinSum (fun c => (u c * u c + 2 * (u c * v c)) + v c * v c) := by
    apply intFinSum_congr
    intro c
    grind
  rw [h1, intFinSum_add, intFinSum_add, intFinSum_mul_left]

/-- If `x^2 ≤ y^2` and `0 ≤ y`, then `x ≤ y`. -/
theorem int_le_of_sq_le_sq {x y : Int} (hy : 0 ≤ y) (h : x * x ≤ y * y) : x ≤ y := by
  by_cases hgt : y < x
  · have h1 : 0 < x - y := by omega
    have h2 : 0 < x + y := by omega
    have hmul : 0 < (x - y) * (x + y) := Int.mul_pos h1 h2
    have hid : (x - y) * (x + y) = x * x - y * y := by grind
    omega
  · omega

/-! ### Pure-`Init` `Rat` Order, Finite Sum, and Cauchy–Schwarz Helpers -/

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

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
    have eq : x * x = (-x) * (-x) := by grind
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_le_sq_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b := by
  have hb : (0 : Rat) ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (rat_mul_le_mul_of_nonneg_left hab ha)
    (rat_mul_le_mul_of_nonneg_right hab hb)

theorem rat_div_mul_cancel {a b : Rat} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.mul_one]

theorem rat_le_of_mul_pos_right {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c ≤ b * c) :
    a ≤ b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl hab => exact hab
  | inr hba =>
    by_cases heq : a = b
    · rw [heq]; exact Rat.le_refl
    · have hlt : b < a := Rat.lt_of_le_of_ne hba (Ne.symm heq)
      have hpos : (0 : Rat) < (a - b) * c := rat_mul_pos (rat_sub_pos hlt) hc
      have hsub : (0 : Rat) ≤ b * c - a * c := rat_sub_nonneg h
      have hneg : b * c - a * c = -((a - b) * c) := by grind
      rw [hneg] at hsub
      have hle0 : (a - b) * c ≤ 0 := by
        have := rat_le_of_sub_nonneg (a := (0 : Rat)) (b := (a - b) * c)
        grind
      exact False.elim (Rat.not_le.mpr hpos hle0)

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

theorem finSum_mul_left {n : Nat} (a : Rat) (f : Fin n → Rat) :
    finSum (fun j => a * f j) = a * finSum f := by
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

theorem cauchy_schwarz_rat_step {U V S a b : Rat}
    (hU : (0 : Rat) ≤ U) (hV : (0 : Rat) ≤ V) (hCS : S * S ≤ U * V) :
    (S + a * b) * (S + a * b) ≤ (U + a * a) * (V + b * b) := by
  have hcross : (0 : Rat) ≤ U * (b * b) + V * (a * a) - 2 * S * a * b := by
    by_cases hU0 : U = 0
    · subst hU0
      have hS0 : S * S ≤ 0 := by grind
      have hSge : (0 : Rat) ≤ S * S := rat_sq_nonneg S
      have hSS : S * S = 0 := Rat.le_antisymm hS0 hSge
      have hS : S = 0 := by
        cases Rat.mul_eq_zero.mp hSS with
        | inl h => exact h
        | inr h => exact h
      subst hS
      have hVa2 : (0 : Rat) ≤ V * (a * a) := Rat.mul_nonneg hV (rat_sq_nonneg a)
      have heq : (0 : Rat) * (b * b) + V * (a * a) - 2 * 0 * a * b = V * (a * a) := by grind
      rw [heq]; exact hVa2
    · have hUpos : (0 : Rat) < U := Rat.lt_of_le_of_ne hU (Ne.symm hU0)
      have h1 : (0 : Rat) ≤ (U * b - S * a) * (U * b - S * a) := rat_sq_nonneg (U * b - S * a)
      have h2 : (0 : Rat) ≤ (U * V - S * S) * (a * a) :=
        Rat.mul_nonneg (rat_sub_nonneg hCS) (rat_sq_nonneg a)
      have hprod : (0 : Rat) ≤ (U * (b * b) + V * (a * a) - 2 * S * a * b) * U := by
        have hid : (U * (b * b) + V * (a * a) - 2 * S * a * b) * U =
            (U * b - S * a) * (U * b - S * a) + (U * V - S * S) * (a * a) := by grind
        rw [hid]
        exact rat_add_nonneg h1 h2
      have h0 : (0 : Rat) * U ≤ (U * (b * b) + V * (a * a) - 2 * S * a * b) * U := by
        have hz : (0 : Rat) * U = 0 := by grind
        rw [hz]; exact hprod
      exact rat_le_of_mul_pos_right hUpos h0
  apply rat_le_of_sub_nonneg
  have hdiff : (U + a * a) * (V + b * b) - (S + a * b) * (S + a * b) =
      (U * V - S * S) + (U * (b * b) + V * (a * a) - 2 * S * a * b) := by grind
  rw [hdiff]
  exact rat_add_nonneg (rat_sub_nonneg hCS) hcross

/-- Universal Cauchy–Schwarz inequality over `ℚ^d` for ALL dimensions `d : Nat`. -/
theorem cauchy_schwarz_rat {d : Nat} (u v : Fin d → Rat) :
    dotRat u v * dotRat u v ≤ normSqRat u * normSqRat v := by
  unfold dotRat normSqRat dotRat finSum
  induction d with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    have hU : (0 : Rat) ≤ finSumAux k (fun c => u ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩ *
                                                u ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩) :=
      finSum_nonneg (fun c => rat_sq_nonneg _)
    have hV : (0 : Rat) ≤ finSumAux k (fun c => v ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩ *
                                                v ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩) :=
      finSum_nonneg (fun c => rat_sq_nonneg _)
    have hCS := ih (fun c => u ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩)
                   (fun c => v ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩)
    exact cauchy_schwarz_rat_step hU hV hCS

end NsaBallBoundMoba
