/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecodingOt.Defs

/-!
# Shared Pure-`Init` Rational, Power, and Finite-Sum Helpers
-/

namespace SpecDecodingOt

theorem rat_le_of_sub_nonneg {a b : Rat} (h : 0 ≤ b - a) : a ≤ b := by
  have h1 : 0 + a ≤ (b - a) + a := Rat.add_le_add_right.mpr h
  have h2 : 0 + a = a := by grind
  have h3 : (b - a) + a = b := by grind
  rw [h2, h3] at h1
  exact h1

theorem rat_sub_nonneg_of_le {a b : Rat} (h : a ≤ b) : 0 ≤ b - a := by
  have h1 : a + -a ≤ b + -a := Rat.add_le_add_right.mpr h
  have h2 : a + -a = 0 := by grind
  have h3 : b + -a = b - a := by grind
  rw [h2, h3] at h1
  exact h1

theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at h1 ⊢
  refine ⟨Rat.le_trans h1.1 h2, ?_⟩
  intro heq
  subst heq
  exact h1.2 (Rat.le_antisymm h1.1 h2)

theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at h2 ⊢
  refine ⟨Rat.le_trans h1 h2.1, ?_⟩
  intro heq
  subst heq
  exact h2.2 (Rat.le_antisymm h2.1 h1)

theorem rat_add_lt_add_of_lt_of_le {a b c d : Rat} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d := by
  have hle : a + c ≤ b + d := rat_add_le_add (Rat.le_of_lt h1) h2
  rw [Rat.lt_iff_le_and_ne] at h1 ⊢
  refine ⟨hle, ?_⟩
  intro heq
  have hbc : b + c ≤ b + d := Rat.add_le_add_left.mpr h2
  have hac : a + c ≤ b + c := Rat.add_le_add_right.mpr h1.1
  have hab : b + c ≤ a + c := by rw [heq]; exact hbc
  have heqc : a + c = b + c := Rat.le_antisymm hac hab
  have hab' : a = b := by grind
  exact h1.2 hab'

theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  have h := rat_add_lt_add_of_lt_of_le h2 h1
  have hL : c + a = a + c := by grind
  have hR : d + b = b + d := by grind
  rw [hL, hR] at h
  exact h

theorem rat_lt_or_ge (a b : Rat) : a < b ∨ b ≤ a := by
  by_cases h : b ≤ a
  · exact Or.inr h
  · exact Or.inl (Rat.not_le.mp h)

theorem rat_mul_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h := Rat.mul_le_mul_of_nonneg_left hb ha
  have hz : a * 0 = 0 := by grind
  rw [hz] at h
  exact h

theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  cases @Rat.le_total 0 x with
  | inl h => exact rat_mul_nonneg h h
  | inr h =>
    have hn : 0 ≤ -x := by
      have h1 := rat_sub_nonneg_of_le h
      have h2 : 0 - x = -x := by grind
      rw [h2] at h1
      exact h1
    have hmul := rat_mul_nonneg hn hn
    have heq : (-x) * (-x) = x * x := by grind
    rw [heq] at hmul
    exact hmul

theorem rat_mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h := Rat.mul_lt_mul_of_pos_left hb ha
  have hz : a * 0 = 0 := by grind
  rw [hz] at h
  exact h

theorem rat_ne_zero_of_pos {a : Rat} (ha : 0 < a) : a ≠ 0 := by
  intro h
  subst h
  exact Rat.lt_irrefl ha

theorem rat_inv_pos {a : Rat} (ha : 0 < a) : 0 < a⁻¹ := by
  cases rat_lt_or_ge 0 a⁻¹ with
  | inl h => exact h
  | inr h =>
    have hmul : a * a⁻¹ ≤ a * 0 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt ha)
    rw [Rat.mul_inv_cancel a (rat_ne_zero_of_pos ha), Rat.mul_zero] at hmul
    exact absurd hmul (by decide)

theorem rat_div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  exact rat_mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_self {a : Rat} (ha : a ≠ 0) : a / a = 1 := by
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel a ha

theorem rat_inv_mul_inv {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have hab : a * b ≠ 0 := by
    intro h
    rcases Rat.mul_eq_zero.mp h with h1 | h1
    · exact ha h1
    · exact hb h1
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    have : (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by grind
    rw [this, Rat.mul_inv_cancel b hb, Rat.mul_one, Rat.mul_inv_cancel a ha]
  have h2 := congrArg (fun z => (a * b)⁻¹ * z) h1
  have hL : (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) = b⁻¹ * a⁻¹ := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel (a * b) hab, Rat.one_mul]
  rw [hL, Rat.mul_one] at h2
  exact h2.symm

theorem rat_div_le_div_iff {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  constructor
  · intro h
    have hbd : 0 < b * d := rat_mul_pos hb hd
    have h1 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hbd)
    have hL : a / b * (b * d) = a * d := by
      rw [Rat.div_def]
      have : a * b⁻¹ * (b * d) = a * (b⁻¹ * b) * d := by grind
      rw [this, Rat.inv_mul_cancel b (rat_ne_zero_of_pos hb)]
      grind
    have hR : c / d * (b * d) = c * b := by
      rw [Rat.div_def]
      have : c * d⁻¹ * (b * d) = c * (d⁻¹ * d) * b := by grind
      rw [this, Rat.inv_mul_cancel d (rat_ne_zero_of_pos hd)]
      grind
    rw [hL, hR] at h1
    exact h1
  · intro h
    have hinv : 0 < (b * d)⁻¹ := rat_inv_pos (rat_mul_pos hb hd)
    have h1 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hinv)
    have hL : a * d * (b * d)⁻¹ = a / b := by
      rw [Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hb) (rat_ne_zero_of_pos hd)]
      have : a * d * (d⁻¹ * b⁻¹) = a * (d * d⁻¹) * b⁻¹ := by grind
      rw [this, Rat.mul_inv_cancel d (rat_ne_zero_of_pos hd)]
      grind
    have hR : c * b * (b * d)⁻¹ = c / d := by
      rw [Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hb) (rat_ne_zero_of_pos hd)]
      have : c * b * (d⁻¹ * b⁻¹) = c * (b * b⁻¹) * d⁻¹ := by grind
      rw [this, Rat.mul_inv_cancel b (rat_ne_zero_of_pos hb)]
      grind
    rw [hL, hR] at h1
    exact h1

theorem rat_inv_one : (1 : Rat)⁻¹ = 1 := by
  have h : (1 : Rat) * (1 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1 (by decide)
  rw [Rat.one_mul] at h
  exact h

theorem rat_div_one (a : Rat) : a / 1 = a := by
  rw [Rat.div_def, rat_inv_one]
  grind

theorem rat_le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  have h := @rat_div_le_div_iff a 1 b c (by decide) hc
  have ha : a / 1 = a := rat_div_one a
  have hb : b * 1 = b := by grind
  rw [ha, hb] at h
  exact h

theorem rat_div_le_iff {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  have h := @rat_div_le_div_iff a b c 1 hb (by decide)
  have hc : c / 1 = c := rat_div_one c
  have ha : a * 1 = a := by grind
  rw [hc, ha] at h
  exact h

theorem rat_abs_le_iff {x b : Rat} : x.abs ≤ b ↔ x ≤ b ∧ -x ≤ b := by
  by_cases h : 0 ≤ x
  · have habs : x.abs = x := by simp [Rat.abs, h]
    rw [habs]
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      have hneg : -x ≤ 0 := by
        apply rat_le_of_sub_nonneg
        have hEq : (0 : Rat) - -x = x := by grind
        rw [hEq]; exact h
      exact Rat.le_trans hneg (Rat.le_trans h hx)
    · exact fun hp => hp.1
  · have habs : x.abs = -x := by simp [Rat.abs, h]
    rw [habs]
    have hxlt : x < 0 := Rat.not_le.mp h
    have hxle : x ≤ 0 := Rat.le_of_lt hxlt
    have hnx : 0 ≤ -x := by
      apply rat_le_of_sub_nonneg
      have hEq : -x - (0 : Rat) = 0 - x := by grind
      rw [hEq]; exact rat_sub_nonneg_of_le hxle
    constructor
    · intro hnxle
      exact ⟨Rat.le_trans hxle (Rat.le_trans hnx hnxle), hnxle⟩
    · exact fun hp => hp.2

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    rw [hcast]
    have h01 : (0 : Rat) ≤ 1 := by decide
    have h := rat_add_le_add ih h01
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at h
    exact h

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  cases n with
  | zero => omega
  | succ k =>
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    rw [hcast]
    have h01 : (0 : Rat) < 1 := by decide
    have h := rat_add_lt_add_of_le_of_lt (rat_natCast_nonneg k) h01
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at h
    exact h

theorem rat_natCast_le_natCast {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have hd : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  rw [hd, Rat.natCast_add]
  have h0 : (a : Rat) + 0 ≤ (a : Rat) + ((b - a : Nat) : Rat) :=
    Rat.add_le_add_left.mpr (rat_natCast_nonneg (b - a))
  have ha : (a : Rat) + 0 = (a : Rat) := by grind
  rw [ha] at h0
  exact h0

/-! ## `ratPow` Lemmas -/

theorem rat_min_le_left (a b : Rat) : min a b ≤ a := by
  by_cases h : a ≤ b
  · simp [min, h]
  · simp [min, h]; exact Rat.le_of_lt (Rat.not_le.mp h)

theorem rat_min_le_right (a b : Rat) : min a b ≤ b := by
  by_cases h : a ≤ b
  · simp [min, h]
  · simp [min, h]

theorem rat_le_min {a b c : Rat} (h1 : a ≤ b) (h2 : a ≤ c) : a ≤ min b c := by
  by_cases h : b ≤ c
  · simp [min, h]; exact h1
  · simp [min, h]; exact h2

theorem rat_min_eq_left {a b : Rat} (h : a ≤ b) : min a b = a := by
  simp [min, h]

theorem rat_min_eq_right {a b : Rat} (h : b ≤ a) : min a b = b := by
  by_cases h' : a ≤ b
  · simp [min, h']; exact Rat.le_antisymm h' h
  · simp [min, h']

theorem ratPow_one (n : Nat) : ratPow 1 n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [ratPow]; rw [ih]; grind

theorem ratPow_zero_of_pos {n : Nat} (hn : 1 ≤ n) : ratPow 0 n = 0 := by
  cases n with
  | zero => omega
  | succ k => simp only [ratPow]; grind

theorem ratPow_nonneg {x : Rat} (hx : 0 ≤ x) (n : Nat) : 0 ≤ ratPow x n := by
  induction n with
  | zero => simp [ratPow]; decide
  | succ k ih => exact rat_mul_nonneg ih hx

theorem ratPow_pos {x : Rat} (hx : 0 < x) (n : Nat) : 0 < ratPow x n := by
  induction n with
  | zero => simp [ratPow]; decide
  | succ k ih => exact rat_mul_pos ih hx

theorem ratPow_le_one {x : Rat} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : Nat) : ratPow x n ≤ 1 := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have h1 := Rat.mul_le_mul_of_nonneg_right ih hx0
    have h2 : 1 * x = x := by grind
    rw [h2] at h1
    exact Rat.le_trans h1 hx1

theorem ratPow_mono {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) (n : Nat) :
    ratPow x n ≤ ratPow y n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have hy : 0 ≤ y := Rat.le_trans hx hxy
    have h1 := Rat.mul_le_mul_of_nonneg_right ih hx
    have h2 := Rat.mul_le_mul_of_nonneg_left hxy (ratPow_nonneg hy k)
    exact Rat.le_trans h1 h2

theorem ratPow_mul (x y : Rat) (n : Nat) :
    ratPow (x * y) n = ratPow x n * ratPow y n := by
  induction n with
  | zero => simp [ratPow]
  | succ k ih =>
    simp only [ratPow]
    rw [ih]
    grind

theorem ratPow_div {x y : Rat} (hy : y ≠ 0) (n : Nat) :
    ratPow (x / y) n = ratPow x n / ratPow y n := by
  induction n with
  | zero => simp [ratPow, rat_div_one]
  | succ k ih =>
    simp only [ratPow]
    rw [ih, Rat.div_def, Rat.div_def, Rat.div_def]
    have hyk : ratPow y k ≠ 0 := by
      clear ih
      induction k with
      | zero => simp [ratPow]
      | succ m ihm =>
        simp only [ratPow]
        intro h
        rcases Rat.mul_eq_zero.mp h with h1 | h1
        · exact ihm h1
        · exact hy h1
    rw [rat_inv_mul_inv hyk hy]
    grind

theorem ratPow_natCast (a n : Nat) : ratPow (a : Rat) n = ((a ^ n : Nat) : Rat) := by
  induction n with
  | zero => simp [ratPow]
  | succ k ih =>
    simp only [ratPow, Nat.pow_succ, Rat.natCast_mul]
    rw [ih]

/-- Exact finite-difference identity `x^n - y^n` for convexity / monotonicity of `t ↦ (1 - t)^K`. -/
theorem ratPow_sub_le_mul_sub {x y : Rat} (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx1 : x ≤ 1) (n : Nat) :
    ratPow x n - ratPow y n ≤ (n : Rat) * (x - y) := by
  induction n with
  | zero =>
    simp only [ratPow]
    have h0 : (1 : Rat) - 1 = 0 := by grind
    have h1 : ((0 : Nat) : Rat) * (x - y) = 0 := by
      have : ((0 : Nat) : Rat) = 0 := rfl
      rw [this]; grind
    rw [h0, h1]
    exact Rat.le_refl
  | succ k ih =>
    simp only [ratPow]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    have hsplit : ratPow x k * x - ratPow y k * y =
        (ratPow x k - ratPow y k) * x + ratPow y k * (x - y) := by grind
    rw [hsplit, hcast]
    have hx0 : 0 ≤ x := Rat.le_trans hy0 hyx
    have hdiff : 0 ≤ x - y := rat_sub_nonneg_of_le hyx
    have h1 : (ratPow x k - ratPow y k) * x ≤ ((k : Rat) * (x - y)) * x :=
      Rat.mul_le_mul_of_nonneg_right ih hx0
    have h2 : ((k : Rat) * (x - y)) * x ≤ ((k : Rat) * (x - y)) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hx1 (rat_mul_nonneg (rat_natCast_nonneg k) hdiff)
    have h3 : ratPow y k * (x - y) ≤ 1 * (x - y) :=
      Rat.mul_le_mul_of_nonneg_right (ratPow_le_one hy0 (Rat.le_trans hyx hx1) k) hdiff
    have hsum := rat_add_le_add (Rat.le_trans h1 h2) h3
    have hR : ((k : Rat) * (x - y)) * 1 + 1 * (x - y) = ((k : Rat) + 1) * (x - y) := by grind
    rw [hR] at hsum
    exact hsum

/-- Bernoulli / concavity inequality for `1 - (1 - x)^K`:
    for `0 ≤ x ≤ y ≤ 1`, `(1 - x)^K - (1 - y)^K ≤ K * (y - x)`, i.e.,
    `K * x + (1 - x)^K ≤ K * y + (1 - y)^K`. -/
theorem bernoulli_linear_plus_pow_mono {x y : Rat} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) (K : Nat) :
    (K : Rat) * x + ratPow (1 - x) K ≤ (K : Rat) * y + ratPow (1 - y) K := by
  have h1y : 0 ≤ 1 - y := rat_sub_nonneg_of_le hy1
  have h1yx : 1 - y ≤ 1 - x := rat_le_of_sub_nonneg (by
    have : (1 - x) - (1 - y) = y - x := by grind
    rw [this]; exact rat_sub_nonneg_of_le hxy)
  have h1x1 : 1 - x ≤ 1 := rat_le_of_sub_nonneg (by
    have : 1 - (1 - x) = x := by grind
    rw [this]; exact hx0)
  have hpow := ratPow_sub_le_mul_sub h1y h1yx h1x1 K
  have hsub : (1 - x) - (1 - y) = y - x := by grind
  rw [hsub] at hpow
  exact rat_le_of_sub_nonneg (by
    have hEq : ((K : Rat) * y + ratPow (1 - y) K) - ((K : Rat) * x + ratPow (1 - x) K) =
        (K : Rat) * (y - x) - (ratPow (1 - x) K - ratPow (1 - y) K) := by grind
    rw [hEq]
    exact rat_sub_nonneg_of_le hpow)

/-! ## `sumRat` Lemmas -/

theorem sumRat_add {n : Nat} (f g : Fin n → Rat) :
    sumRat (fun i => f i + g i) = sumRat f + sumRat g := by
  induction n with
  | zero => simp only [sumRat]; grind
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem sumRat_sub {n : Nat} (f g : Fin n → Rat) :
    sumRat (fun i => f i - g i) = sumRat f - sumRat g := by
  induction n with
  | zero => simp only [sumRat]; grind
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem sumRat_const (n : Nat) (c : Rat) :
    sumRat (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    rw [hcast]
    grind

theorem sumRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumRat (fun i => c * f i) = c * sumRat f := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc), Rat.mul_add]

theorem sumRat_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumRat (fun i => f i * c) = sumRat f * c := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc), Rat.add_mul]

theorem sumRat_div_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumRat (fun i => f i / c) = sumRat f / c := by
  simp only [Rat.div_def]
  exact sumRat_mul_right f c⁻¹

theorem sumRat_nonneg {n : Nat} (f : Fin n → Rat) (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumRat f := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [sumRat]
    have h1 := rat_add_le_add (ih (fun i => f i.castSucc) (fun i => h i.castSucc)) (h (Fin.last k))
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at h1
    exact h1

theorem sumRat_pos {n : Nat} (hn : 0 < n) (f : Fin n → Rat) (h : ∀ i, 0 < f i) :
    0 < sumRat f := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [sumRat]
    have h1 := rat_add_lt_add_of_le_of_lt
      (sumRat_nonneg (fun i => f i.castSucc) (fun i => Rat.le_of_lt (h i.castSucc)))
      (h (Fin.last k))
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at h1
    exact h1

theorem sumRat_le_sumRat {n : Nat} (f g : Fin n → Rat) (h : ∀ i, f i ≤ g i) :
    sumRat f ≤ sumRat g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [sumRat]
    exact rat_add_le_add
      (ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => h i.castSucc))
      (h (Fin.last k))

theorem sumRat_congr {n : Nat} (f g : Fin n → Rat) (h : ∀ i, f i = g i) :
    sumRat f = sumRat g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => h i.castSucc), h (Fin.last k)]

theorem sumRat_split_bool {n : Nat} (f : Fin n → Rat) (S : Fin n → Bool) :
    sumRat (fun i => if S i then f i else 0) + sumRat (fun i => if S i then 0 else f i) =
      sumRat f := by
  rw [← sumRat_add]
  apply sumRat_congr
  intro i
  cases S i <;> simp <;> grind

theorem sumRat_split_prop {n : Nat} (f : Fin n → Rat) (P : Fin n → Prop) [DecidablePred P] :
    sumRat (fun i => if P i then f i else 0) + sumRat (fun i => if P i then 0 else f i) =
      sumRat f := by
  rw [← sumRat_add]
  apply sumRat_congr
  intro i
  by_cases hp : P i <;> simp [hp] <;> grind

theorem sumRat_ite_eq_zero {n : Nat} (hn : 0 < n) (a b : Rat) :
    sumRat (fun i : Fin n => if i.val = 0 then a else b) =
      a + ((n - 1 : Nat) : Rat) * b := by
  cases n with
  | zero => omega
  | succ k =>
    induction k with
    | zero =>
      simp only [sumRat]
      have h0 : ((0 : Nat) : Rat) = 0 := rfl
      simp [h0]
      grind
    | succ m ih =>
      have hstep : sumRat (fun i : Fin (m + 1 + 1) => if i.val = 0 then a else b) =
          sumRat (fun i : Fin (m + 1) => if i.castSucc.val = 0 then a else b) +
            (if (Fin.last (m + 1)).val = 0 then a else b) := rfl
      rw [hstep]
      have hlast : (Fin.last (m + 1)).val ≠ 0 := by simp [Fin.last]
      simp only [hlast, ↓reduceIte]
      have hsub : sumRat (fun i : Fin (m + 1) => if i.castSucc.val = 0 then a else b) =
          sumRat (fun i : Fin (m + 1) => if i.val = 0 then a else b) := by
        apply sumRat_congr
        intro i
        rfl
      rw [hsub, ih (Nat.zero_lt_succ m)]
      have hcast : ((m + 1 : Nat) : Rat) = (m : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      simp only [Nat.add_sub_cancel]
      rw [hcast]
      grind

theorem softmaxRat_nonneg {V : Nat} (hV : 0 < V) (w : Fin V → Rat) (hw : ∀ i, 0 < w i) (i : Fin V) :
    0 ≤ softmaxRat w i :=
  rat_div_nonneg (Rat.le_of_lt (hw i)) (sumRat_pos hV w hw)

theorem softmaxRat_sum {V : Nat} (hV : 0 < V) (w : Fin V → Rat) (hw : ∀ i, 0 < w i) :
    sumRat (softmaxRat w) = 1 := by
  unfold softmaxRat
  rw [sumRat_div_right]
  exact rat_div_self (rat_ne_zero_of_pos (sumRat_pos hV w hw))

theorem softmaxRat_isProbDist {V : Nat} (hV : 0 < V) (w : Fin V → Rat) (hw : ∀ i, 0 < w i) :
    isProbDist (softmaxRat w) :=
  ⟨softmaxRat_nonneg hV w hw, softmaxRat_sum hV w hw⟩

end SpecDecodingOt
