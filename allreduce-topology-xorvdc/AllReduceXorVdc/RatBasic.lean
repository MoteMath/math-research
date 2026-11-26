/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AllReduceXorVdc.Defs

/-!
# Pure-`Init` `Rat` Order, Finite Sums, RNE Characterization, and Bitwise Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace AllReduceXorVdc

/-! ### 1. Elementary `Rat` Order and Field Helpers -/

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

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < a⁻¹ := by
  by_cases h : (0 : Rat) < a⁻¹
  · exact h
  · have hle : a⁻¹ ≤ 0 := Rat.not_lt.mp h
    have h1 : a * a⁻¹ ≤ a * 0 := rat_mul_le_mul_of_nonneg_left hle (Rat.le_of_lt ha)
    have ha_ne : a ≠ 0 := Rat.ne_of_gt ha
    have hmul : a * a⁻¹ = 1 := Rat.mul_inv_cancel a ha_ne
    have h0 : a * 0 = 0 := by grind
    rw [hmul, h0] at h1
    exact absurd h1 (by decide)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_le_div_of_pos_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) < c) :
    a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))

theorem rat_div_lt_div_of_pos_right {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    a / c < b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact rat_mul_lt_mul_of_pos_right h (rat_inv_pos hc)

theorem rat_add_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) ≤ a + b := by
  have h1 : (0 : Rat) + b ≤ a + b := (Rat.add_le_add_right (c := b)).mpr ha
  have h0 : (0 : Rat) + b = b := by grind
  rw [h0] at h1
  exact Rat.le_trans hb h1

theorem rat_add_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a + b := by
  have h1 : (0 : Rat) + b < a + b := (Rat.add_lt_add_right (c := b)).mpr ha
  have h0 : (0 : Rat) + b = b := by grind
  rw [h0] at h1
  exact rat_lt_trans hb h1

theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) :
    a + c ≤ b + d := by
  have h3 : a + c ≤ b + c := (Rat.add_le_add_right (c := c)).mpr h1
  have h4 : c + b ≤ d + b := (Rat.add_le_add_right (c := b)).mpr h2
  rw [Rat.add_comm c b, Rat.add_comm d b] at h4
  exact Rat.le_trans h3 h4

theorem absRat_of_nonneg {x : Rat} (h : (0 : Rat) ≤ x) : absRat x = x := by
  unfold absRat
  have hnot : ¬ (x < 0) := Rat.not_lt.mpr h
  simp [hnot]

theorem absRat_of_nonpos {x : Rat} (h : x ≤ 0) : absRat x = -x := by
  unfold absRat
  by_cases hlt : x < 0
  · simp [hlt]
  · have hge : (0 : Rat) ≤ x := Rat.not_lt.mp hlt
    have hx : x = 0 := Rat.le_antisymm h hge
    simp [hx]

theorem absRat_nonneg (x : Rat) : (0 : Rat) ≤ absRat x := by
  unfold absRat
  by_cases hlt : x < 0
  · simp only [hlt, ↓reduceIte]
    have := rat_sub_pos hlt
    grind
  · simp only [hlt, ↓reduceIte]
    exact Rat.not_lt.mp hlt

theorem absRat_neg (x : Rat) : absRat (-x) = absRat x := by
  unfold absRat
  by_cases hlt : x < 0
  · have hpos : (0 : Rat) < -x := by
      have := rat_sub_pos hlt
      grind
    have hnot : ¬ (-x < 0) := Rat.not_lt.mpr (Rat.le_of_lt hpos)
    simp [hlt, hnot]
  · have hge : (0 : Rat) ≤ x := Rat.not_lt.mp hlt
    by_cases h0 : x = 0
    · subst h0; decide
    · have hpos : (0 : Rat) < x := Rat.lt_of_le_of_ne hge (Ne.symm h0)
      have hneg : -x < 0 := by
        have := (Rat.add_lt_add_right (c := -x)).mpr hpos
        grind
      simp [hlt, hneg]

theorem absRat_le_iff {x c : Rat} : absRat x ≤ c ↔ -c ≤ x ∧ x ≤ c := by
  unfold absRat
  by_cases hlt : x < 0
  · simp only [hlt, ↓reduceIte]
    constructor
    · intro h
      have h1 : -c ≤ x := by
        have := (Rat.add_le_add_right (c := x - c)).mpr h
        grind
      have h2 : (0 : Rat) ≤ c := by
        have hxpos : (0 : Rat) < -x := by
          have := rat_sub_pos hlt
          grind
        exact Rat.le_trans (Rat.le_of_lt hxpos) h
      exact ⟨h1, Rat.le_trans (Rat.le_of_lt hlt) h2⟩
    · intro ⟨h1, _⟩
      have := (Rat.add_le_add_right (c := c - x)).mpr h1
      grind
  · simp only [hlt, ↓reduceIte]
    have hge : (0 : Rat) ≤ x := Rat.not_lt.mp hlt
    constructor
    · intro h
      have hc : (0 : Rat) ≤ c := Rat.le_trans hge h
      have hnegc : -c ≤ 0 := by
        have := (Rat.add_le_add_right (c := -c)).mpr hc
        grind
      exact ⟨Rat.le_trans hnegc hge, h⟩
    · intro ⟨_, h2⟩
      exact h2

theorem absRat_lt_iff {x c : Rat} : absRat x < c ↔ -c < x ∧ x < c := by
  unfold absRat
  by_cases hlt : x < 0
  · simp only [hlt, ↓reduceIte]
    constructor
    · intro h
      have h1 : -c < x := by
        have := (Rat.add_lt_add_right (c := x - c)).mpr h
        grind
      have h2 : (0 : Rat) < c := by
        have hxpos : (0 : Rat) < -x := by
          have := rat_sub_pos hlt
          grind
        exact rat_lt_trans hxpos h
      exact ⟨h1, rat_lt_trans hlt h2⟩
    · intro ⟨h1, _⟩
      have := (Rat.add_lt_add_right (c := c - x)).mpr h1
      grind
  · simp only [hlt, ↓reduceIte]
    have hge : (0 : Rat) ≤ x := Rat.not_lt.mp hlt
    constructor
    · intro h
      have hc : (0 : Rat) < c := rat_lt_of_le_of_lt hge h
      have hnegc : -c < 0 := by
        have := (Rat.add_lt_add_right (c := -c)).mpr hc
        grind
      exact ⟨rat_lt_of_lt_of_le hnegc hge, h⟩
    · intro ⟨_, h2⟩
      exact h2

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  have h : (0 : Int) < (n : Int) := by omega
  exact Rat.intCast_lt_intCast.mpr h

theorem rat_natCast_ne_zero {n : Nat} (hn : 0 < n) : (n : Rat) ≠ 0 :=
  Rat.ne_of_gt (rat_natCast_pos hn)

theorem rat_natCast_le_natCast {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have h1 : (a : Int) ≤ (b : Int) := by omega
  exact Rat.intCast_le_intCast.mpr h1

theorem rat_natCast_lt_natCast {a b : Nat} (h : a < b) : (a : Rat) < (b : Rat) := by
  have h1 : (a : Int) < (b : Int) := by omega
  exact Rat.intCast_lt_intCast.mpr h1

theorem rat_natCast_add (a b : Nat) : ((a + b : Nat) : Rat) = (a : Rat) + (b : Rat) := by
  grind

theorem rat_natCast_mul (a b : Nat) : ((a * b : Nat) : Rat) = (a : Rat) * (b : Rat) := by
  grind

theorem rat_pow2_pos (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) :=
  rat_natCast_pos (Nat.two_pow_pos n)

theorem rat_pow2_ne_zero (n : Nat) : ((2 ^ n : Nat) : Rat) ≠ 0 :=
  Rat.ne_of_gt (rat_pow2_pos n)

theorem dyadicUlp_pos (p : Nat) : (0 : Rat) < dyadicUlp p :=
  rat_div_pos (by decide) (rat_pow2_pos p)

theorem dyadicUlp_ne_zero (p : Nat) : dyadicUlp p ≠ 0 :=
  Rat.ne_of_gt (dyadicUlp_pos p)

theorem rat_mul_inv (a b : Rat) (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have hab : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact hb h
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    have : (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by grind
    rw [this, Rat.mul_inv_cancel _ hb, Rat.mul_one, Rat.mul_inv_cancel _ ha]
  have h2 := congrArg ((a * b)⁻¹ * ·) h1
  rw [← Rat.mul_assoc, Rat.inv_mul_cancel _ hab, Rat.one_mul, Rat.mul_one] at h2
  exact h2.symm

/-! ### 2. Exact Integer Division Bridge and `rneInt` / `rneGrid` Characterizations -/

theorem rat_int_le_iff (n : Int) (y : Rat) :
    (n : Rat) ≤ y ↔ n * (y.den : Int) ≤ y.num := by
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
    y < (n : Rat) + (1 : Rat) / 2 ↔ 2 * y.num < (2 * n + 1) * (y.den : Int) := by
  have hd_pos : (0 : Rat) < (y.den : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero y.den_nz)
  have h2d_pos : (0 : Rat) < 2 * (y.den : Rat) := rat_mul_pos (by decide) hd_pos
  have hlhs : y * (2 * (y.den : Rat)) = ((2 * y.num : Int) : Rat) := by
    have : y * (2 * (y.den : Rat)) = 2 * (y * (y.den : Rat)) := by grind
    rw [this, rat_mul_den, Rat.intCast_mul]; rfl
  have hrhs : ((n : Rat) + (1 : Rat) / 2) * (2 * (y.den : Rat)) =
      (((2 * n + 1) * (y.den : Int) : Int) : Rat) := by
    have : ((n : Rat) + (1 : Rat) / 2) * (2 * (y.den : Rat)) = (2 * (n : Rat) + 1) * (y.den : Rat) := by grind
    rw [this, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_mul]; rfl
  constructor
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h h2d_pos
    rw [hlhs, hrhs] at hmul
    exact Rat.intCast_lt_intCast.mp hmul
  · intro h
    have hcast : y * (2 * (y.den : Rat)) < ((n : Rat) + (1 : Rat) / 2) * (2 * (y.den : Rat)) := by
      rw [hlhs, hrhs]
      exact Rat.intCast_lt_intCast.mpr h
    have hinv := rat_mul_lt_mul_of_pos_right hcast (rat_inv_pos h2d_pos)
    have hne : 2 * (y.den : Rat) ≠ 0 := Rat.ne_of_gt h2d_pos
    have h1 : ∀ x : Rat, x * (2 * (y.den : Rat)) * (2 * (y.den : Rat))⁻¹ = x := by
      intro x
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne, Rat.mul_one]
    rw [h1 y, h1 ((n : Rat) + (1 : Rat) / 2)] at hinv
    exact hinv

theorem rat_eq_int_add_half_iff (y : Rat) (n : Int) :
    y = (n : Rat) + (1 : Rat) / 2 ↔ 2 * y.num = (2 * n + 1) * (y.den : Int) := by
  have hd_pos : (0 : Rat) < (y.den : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero y.den_nz)
  have h2d_ne : 2 * (y.den : Rat) ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) hd_pos)
  have hlhs : y * (2 * (y.den : Rat)) = ((2 * y.num : Int) : Rat) := by
    have : y * (2 * (y.den : Rat)) = 2 * (y * (y.den : Rat)) := by grind
    rw [this, rat_mul_den, Rat.intCast_mul]; rfl
  have hrhs : ((n : Rat) + (1 : Rat) / 2) * (2 * (y.den : Rat)) =
      (((2 * n + 1) * (y.den : Int) : Int) : Rat) := by
    have : ((n : Rat) + (1 : Rat) / 2) * (2 * (y.den : Rat)) = (2 * (n : Rat) + 1) * (y.den : Rat) := by grind
    rw [this, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_mul]; rfl
  constructor
  · intro h
    have hmul := congrArg (· * (2 * (y.den : Rat))) h
    rw [hlhs, hrhs] at hmul
    exact Rat.intCast_inj.mp hmul
  · intro h
    have hcast : y * (2 * (y.den : Rat)) = ((n : Rat) + (1 : Rat) / 2) * (2 * (y.den : Rat)) := by
      rw [hlhs, hrhs, h]
    have hinv := congrArg (· * (2 * (y.den : Rat))⁻¹) hcast
    simp only [Rat.mul_assoc, Rat.mul_inv_cancel _ h2d_ne, Rat.mul_one] at hinv
    exact hinv

theorem rneInt_int (n : Int) : rneInt (n : Rat) = n := by
  unfold rneInt
  dsimp only
  have hnum : ((n : Rat)).num = n := rfl
  have hden : ((n : Rat)).den = 1 := rfl
  rw [hnum, hden]
  have h1 : ((1 : Nat) : Int) = 1 := rfl
  rw [h1, Int.ediv_one, Int.emod_one]
  simp

theorem int_div_eq_of_bounds {a d n : Int} (hd : 0 < d) (hlo : n * d ≤ a) (hhi : a < (n + 1) * d) :
    a / d = n := by
  have hdiv : d * (a / d) + a % d = a := by
    have h := Int.emod_add_mul_ediv a d; omega
  have hr0 : 0 ≤ a % d := Int.emod_nonneg a (by omega)
  have hrd : a % d < d := Int.emod_lt_of_pos a hd
  have h1 : n ≤ a / d := by
    by_cases h : n ≤ a / d
    · exact h
    · have hle : a / d + 1 ≤ n := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right hle (show (0 : Int) ≤ d by omega)
      have : d * (a / d) + d ≤ n * d := by grind
      omega
  have h2 : a / d ≤ n := by
    by_cases h : a / d ≤ n
    · exact h
    · have hge : n + 1 ≤ a / d := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right hge (show (0 : Int) ≤ d by omega)
      have : (n + 1) * d ≤ d * (a / d) := by grind
      omega
  omega

theorem rneInt_int_add_small {n : Int} {r : Rat} (hr0 : (0 : Rat) ≤ r) (hrhalf : r < (1 : Rat) / 2) :
    rneInt ((n : Rat) + r) = n := by
  unfold rneInt
  dsimp only
  let y : Rat := (n : Rat) + r
  change (if 2 * (y.num % (y.den : Int)) < (y.den : Int) then y.num / (y.den : Int)
    else if (y.den : Int) < 2 * (y.num % (y.den : Int)) then y.num / (y.den : Int) + 1
    else if (y.num / (y.den : Int) % 2 == 0) = true then y.num / (y.den : Int)
    else y.num / (y.den : Int) + 1) = n
  have hd_pos : (0 : Int) < (y.den : Int) := by
    have := Nat.pos_of_ne_zero y.den_nz; omega
  have hge : n * (y.den : Int) ≤ y.num := by
    apply (rat_int_le_iff n y).mp
    have := (Rat.add_le_add_right (c := (n : Rat))).mpr hr0
    grind
  have hlt : 2 * y.num < (2 * n + 1) * (y.den : Int) := by
    apply (rat_lt_int_add_half_iff y n).mp
    have := (Rat.add_lt_add_right (c := (n : Rat))).mpr hrhalf
    grind
  have hlt1 : y.num < (n + 1) * (y.den : Int) := by
    have h2 : 2 * ((n + 1) * (y.den : Int)) = (2 * n + 1) * (y.den : Int) + (y.den : Int) := by grind
    omega
  have hq : y.num / (y.den : Int) = n := int_div_eq_of_bounds hd_pos hge hlt1
  have hdiv : (y.den : Int) * (y.num / (y.den : Int)) + y.num % (y.den : Int) = y.num := by
    have h := Int.emod_add_mul_ediv y.num (y.den : Int); omega
  have hrem : 2 * (y.num % (y.den : Int)) < (y.den : Int) := by
    rw [hq] at hdiv
    have h3 : (2 * n + 1) * (y.den : Int) = 2 * ((y.den : Int) * n) + (y.den : Int) := by grind
    omega
  simp only [hq, hrem, ↓reduceIte]

theorem rneInt_int_add_half_even {n : Int} (heven : n % 2 = 0) :
    rneInt ((n : Rat) + (1 : Rat) / 2) = n := by
  unfold rneInt
  dsimp only
  let y : Rat := (n : Rat) + (1 : Rat) / 2
  change (if 2 * (y.num % (y.den : Int)) < (y.den : Int) then y.num / (y.den : Int)
    else if (y.den : Int) < 2 * (y.num % (y.den : Int)) then y.num / (y.den : Int) + 1
    else if (y.num / (y.den : Int) % 2 == 0) = true then y.num / (y.den : Int)
    else y.num / (y.den : Int) + 1) = n
  have hd_pos : (0 : Int) < (y.den : Int) := by
    have := Nat.pos_of_ne_zero y.den_nz; omega
  have heq : 2 * y.num = (2 * n + 1) * (y.den : Int) :=
    (rat_eq_int_add_half_iff y n).mp rfl
  have hlo : n * (y.den : Int) ≤ y.num := by
    have : (2 * n + 1) * (y.den : Int) = 2 * (n * (y.den : Int)) + (y.den : Int) := by grind
    omega
  have hhi : y.num < (n + 1) * (y.den : Int) := by
    have : 2 * ((n + 1) * (y.den : Int)) = (2 * n + 1) * (y.den : Int) + (y.den : Int) := by grind
    omega
  have hq : y.num / (y.den : Int) = n := int_div_eq_of_bounds hd_pos hlo hhi
  have hdiv : (y.den : Int) * (y.num / (y.den : Int)) + y.num % (y.den : Int) = y.num := by
    have h := Int.emod_add_mul_ediv y.num (y.den : Int); omega
  have hrem : 2 * (y.num % (y.den : Int)) = (y.den : Int) := by
    rw [hq] at hdiv
    have h3 : (2 * n + 1) * (y.den : Int) = 2 * ((y.den : Int) * n) + (y.den : Int) := by grind
    omega
  have h1 : ¬ (2 * (y.num % (y.den : Int)) < (y.den : Int)) := by omega
  have h2 : ¬ ((y.den : Int) < 2 * (y.num % (y.den : Int))) := by omega
  simp only [h1, h2, hq, heven, beq_self_eq_true, ↓reduceIte]

theorem rneInt_int_add_half_odd {n : Int} (hodd : n % 2 ≠ 0) :
    rneInt ((n : Rat) + (1 : Rat) / 2) = n + 1 := by
  unfold rneInt
  dsimp only
  let y : Rat := (n : Rat) + (1 : Rat) / 2
  change (if 2 * (y.num % (y.den : Int)) < (y.den : Int) then y.num / (y.den : Int)
    else if (y.den : Int) < 2 * (y.num % (y.den : Int)) then y.num / (y.den : Int) + 1
    else if (y.num / (y.den : Int) % 2 == 0) = true then y.num / (y.den : Int)
    else y.num / (y.den : Int) + 1) = n + 1
  have hd_pos : (0 : Int) < (y.den : Int) := by
    have := Nat.pos_of_ne_zero y.den_nz; omega
  have heq : 2 * y.num = (2 * n + 1) * (y.den : Int) :=
    (rat_eq_int_add_half_iff y n).mp rfl
  have hlo : n * (y.den : Int) ≤ y.num := by
    have : (2 * n + 1) * (y.den : Int) = 2 * (n * (y.den : Int)) + (y.den : Int) := by grind
    omega
  have hhi : y.num < (n + 1) * (y.den : Int) := by
    have : 2 * ((n + 1) * (y.den : Int)) = (2 * n + 1) * (y.den : Int) + (y.den : Int) := by grind
    omega
  have hq : y.num / (y.den : Int) = n := int_div_eq_of_bounds hd_pos hlo hhi
  have hdiv : (y.den : Int) * (y.num / (y.den : Int)) + y.num % (y.den : Int) = y.num := by
    have h := Int.emod_add_mul_ediv y.num (y.den : Int); omega
  have hrem : 2 * (y.num % (y.den : Int)) = (y.den : Int) := by
    rw [hq] at hdiv
    have h3 : (2 * n + 1) * (y.den : Int) = 2 * ((y.den : Int) * n) + (y.den : Int) := by grind
    omega
  have h1 : ¬ (2 * (y.num % (y.den : Int)) < (y.den : Int)) := by omega
  have h2 : ¬ ((y.den : Int) < 2 * (y.num % (y.den : Int))) := by omega
  have h3 : (n % 2 == 0) = false := by
    cases h : (n % 2 == 0)
    · rfl
    · exact absurd (beq_iff_eq.mp h) hodd
  simp only [h1, h2, hq, h3, Bool.false_eq_true, ↓reduceIte]

/-- Universal half-ULP error bound for `rneInt`: `|y - rneInt y| ≤ 1/2`. -/
theorem absRat_sub_rneInt_le_half (y : Rat) :
    absRat (y - (rneInt y : Rat)) ≤ (1 : Rat) / 2 := by
  have hd_pos : (0 : Int) < (y.den : Int) := by
    have := Nat.pos_of_ne_zero y.den_nz; omega
  have h2d_pos : (0 : Rat) < 2 * (y.den : Rat) :=
    rat_mul_pos (by decide) (rat_natCast_pos (Nat.pos_of_ne_zero y.den_nz))
  have hdiv : y.num = (y.num / (y.den : Int)) * (y.den : Int) + y.num % (y.den : Int) := by
    have h := Int.emod_add_mul_ediv y.num (y.den : Int)
    have hcomm : (y.den : Int) * (y.num / (y.den : Int)) = (y.num / (y.den : Int)) * (y.den : Int) :=
      Int.mul_comm _ _
    omega
  have hr0 : 0 ≤ y.num % (y.den : Int) := Int.emod_nonneg y.num (by omega)
  have hrd : y.num % (y.den : Int) < (y.den : Int) := Int.emod_lt_of_pos y.num hd_pos
  have hbound : ∀ k : Int,
      -(y.den : Int) ≤ 2 * (y.num - k * (y.den : Int)) ∧
      2 * (y.num - k * (y.den : Int)) ≤ (y.den : Int) →
      absRat (y - (k : Rat)) ≤ (1 : Rat) / 2 := by
    intro k ⟨hlo, hhi⟩
    rw [absRat_le_iff]
    have hmul_eq : (y - (k : Rat)) * (2 * (y.den : Rat)) =
        ((2 * (y.num - k * (y.den : Int)) : Int) : Rat) := by
      have h1 : (y - (k : Rat)) * (2 * (y.den : Rat)) =
          2 * (y * (y.den : Rat) - (k : Rat) * (y.den : Rat)) := by grind
      rw [h1, rat_mul_den]
      have h2 : ((y.den : Nat) : Rat) = ((y.den : Int) : Rat) := rfl
      rw [h2, Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_mul]; rfl
    have hne : 2 * (y.den : Rat) ≠ 0 := Rat.ne_of_gt h2d_pos
    have hcancel : ∀ a b : Rat, a * (2 * (y.den : Rat)) ≤ b * (2 * (y.den : Rat)) → a ≤ b := by
      intro a b hab
      have hinv := rat_mul_le_mul_of_nonneg_right hab (Rat.le_of_lt (rat_inv_pos h2d_pos))
      simp only [Rat.mul_assoc, Rat.mul_inv_cancel _ hne, Rat.mul_one] at hinv
      exact hinv
    constructor
    · apply hcancel
      rw [hmul_eq]
      have hl : -((1 : Rat) / 2) * (2 * (y.den : Rat)) = ((-(y.den : Int) : Int) : Rat) := by
        have : -((1 : Rat) / 2) * (2 * (y.den : Rat)) = -((y.den : Rat)) := by grind
        rw [this, Rat.intCast_neg]; rfl
      rw [hl]
      exact Rat.intCast_le_intCast.mpr hlo
    · apply hcancel
      rw [hmul_eq]
      have hr : ((1 : Rat) / 2) * (2 * (y.den : Rat)) = (((y.den : Int) : Int) : Rat) := by
        have : ((1 : Rat) / 2) * (2 * (y.den : Rat)) = (y.den : Rat) := by grind
        rw [this]; rfl
      rw [hr]
      exact Rat.intCast_le_intCast.mpr hhi
  apply hbound
  unfold rneInt
  dsimp only
  have hsubq : y.num - (y.num / (y.den : Int)) * (y.den : Int) = y.num % (y.den : Int) := by omega
  have hsubq1 : y.num - (y.num / (y.den : Int) + 1) * (y.den : Int) =
      y.num % (y.den : Int) - (y.den : Int) := by grind
  by_cases h1 : 2 * (y.num % (y.den : Int)) < (y.den : Int)
  · simp only [h1, ↓reduceIte, hsubq]
    omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (y.den : Int) < 2 * (y.num % (y.den : Int))
    · simp only [h2, ↓reduceIte, hsubq1]
      omega
    · simp only [h2, ↓reduceIte]
      by_cases h3 : ((y.num / (y.den : Int)) % 2 == 0) = true
      · simp only [h3, ↓reduceIte, hsubq]
        omega
      · simp only [h3, Bool.false_eq_true, ↓reduceIte, hsubq1]
        omega

/-- Universal half-ULP error bound for `rneGrid`: `|x - rneGrid u x| ≤ u / 2` for `u > 0`. -/
theorem absRat_sub_rneGrid_le_half {u : Rat} (hu : (0 : Rat) < u) (x : Rat) :
    absRat (x - rneGrid u x) ≤ u / 2 := by
  unfold rneGrid
  have hu_ne : u ≠ 0 := Rat.ne_of_gt hu
  have hfactor : x - (rneInt (x / u) : Rat) * u = (x / u - (rneInt (x / u) : Rat)) * u := by
    have hdiv : (x / u) * u = x := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hu_ne, Rat.mul_one]
    have hsub : (x / u - (rneInt (x / u) : Rat)) * u = (x / u) * u - (rneInt (x / u) : Rat) * u := by grind
    rw [hsub, hdiv]
  rw [hfactor]
  have hbound : absRat (x / u - (rneInt (x / u) : Rat)) ≤ (1 : Rat) / 2 :=
    absRat_sub_rneInt_le_half (x / u)
  rw [absRat_le_iff] at hbound ⊢
  constructor
  · have h1 := rat_mul_le_mul_of_nonneg_right hbound.1 (Rat.le_of_lt hu)
    have hl : -((1 : Rat) / 2) * u = -(u / 2) := by grind
    rw [hl] at h1
    exact h1
  · have h2 := rat_mul_le_mul_of_nonneg_right hbound.2 (Rat.le_of_lt hu)
    have hr : (1 : Rat) / 2 * u = u / 2 := by grind
    rw [hr] at h2
    exact h2

/-- `rneGrid u (n * u) = n * u` for any integer `n` and `u > 0`. -/
theorem rneGrid_int_mul {u : Rat} (hu : (0 : Rat) < u) (n : Int) :
    rneGrid u ((n : Rat) * u) = (n : Rat) * u := by
  unfold rneGrid
  have hu_ne : u ≠ 0 := Rat.ne_of_gt hu
  have hdiv : (n : Rat) * u / u = (n : Rat) := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hu_ne, Rat.mul_one]
  rw [hdiv, rneInt_int]

/-! ### 3. `sumRange` and `sumNatRange` Algebra -/

theorem sumRange_congr {n : Nat} {f g : Nat → Rat} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumRange_add (n : Nat) (f g : Nat → Rat) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]; grind
  | succ n ih =>
    simp only [sumRange, ih]
    grind

theorem sumRange_sub (n : Nat) (f g : Nat → Rat) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]; grind
  | succ n ih =>
    simp only [sumRange, ih]
    grind

theorem sumRange_const (n : Nat) (c : Rat) :
    sumRange n (fun _ => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    grind

theorem sumRange_mul_left (n : Nat) (c : Rat) (f : Nat → Rat) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    grind

theorem sumRange_div_const (n : Nat) (f : Nat → Rat) (c : Rat) :
    sumRange n (fun i => f i / c) = sumRange n f / c := by
  induction n with
  | zero => simp [sumRange]; grind
  | succ n ih =>
    simp only [sumRange, ih]
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind

theorem sumRange_append (a b : Nat) (f : Nat → Rat) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun j => f (a + j)) := by
  induction b with
  | zero => simp [sumRange]; grind
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [sumRange]
    rw [ih]
    grind

theorem sumRange_mul_split (A B : Nat) (hB : 0 < B) (f : Nat → Nat → Rat) :
    sumRange (A * B) (fun w => f (w / B) (w % B)) =
    sumRange A (fun q => sumRange B (fun r => f q r)) := by
  induction A with
  | zero => simp [sumRange]
  | succ A ih =>
    rw [Nat.succ_mul, sumRange_append, ih]
    simp only [sumRange]
    congr 1
    apply sumRange_congr
    intro r hr
    have hdiv : (A * B + r) / B = A := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hr, Nat.add_zero]
    have hmod : (A * B + r) % B = r := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rw [hdiv, hmod]

theorem sumRange_lt_indicator (M p : Nat) (hp : p ≤ M) :
    sumRange M (fun u => if u < p then (1 : Rat) else 0) = (p : Rat) := by
  induction M generalizing p with
  | zero =>
    have hp0 : p = 0 := by omega
    subst hp0; rfl
  | succ M ih =>
    simp only [sumRange]
    by_cases hlt : M < p
    · have hpEq : p = M + 1 := by omega
      subst hpEq
      have h1 : sumRange M (fun u => if u < M + 1 then (1 : Rat) else 0) =
          sumRange M (fun u => if u < M then (1 : Rat) else 0) := by
        apply sumRange_congr
        intro u hu
        have h2 : u < M + 1 := by omega
        simp [hu, h2]
      rw [h1, ih M (Nat.le_refl M)]
      simp only [hlt, ↓reduceIte]
      grind
    · have hpLe : p ≤ M := by omega
      rw [ih p hpLe]
      simp only [hlt, ↓reduceIte]
      grind

theorem sumRange_nat_id (n : Nat) :
    sumRange n (fun u => (u : Rat)) = ((n : Rat) * ((n : Rat) - 1)) / 2 := by
  induction n with
  | zero => simp [sumRange]; grind
  | succ n ih =>
    simp only [sumRange, ih]
    rw [rat_natCast_add]
    have h1 : ((1 : Nat) : Rat) = 1 := rfl
    rw [h1]
    grind

theorem sumRange_nat_sq (n : Nat) :
    sumRange n (fun u => (u : Rat) * (u : Rat)) =
    ((n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1)) / 6 := by
  induction n with
  | zero => simp [sumRange]; grind
  | succ n ih =>
    simp only [sumRange, ih]
    rw [rat_natCast_add]
    have h1 : ((1 : Nat) : Rat) = 1 := rfl
    rw [h1]
    grind

theorem sumNatRange_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumNatRange n f = sumNatRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNatRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumNatRange_const (n c : Nat) :
    sumNatRange n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumNatRange]
  | succ n ih =>
    simp only [sumNatRange, ih]
    rw [Nat.succ_mul]

theorem sumNatRange_append (a b : Nat) (f : Nat → Nat) :
    sumNatRange (a + b) f = sumNatRange a f + sumNatRange b (fun j => f (a + j)) := by
  induction b with
  | zero => simp [sumNatRange]
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [sumNatRange, ih]
    omega

theorem countRange_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i, i < n → p i = q i) :
    countRange n p = countRange n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem countRange_true (n : Nat) : countRange n (fun _ => true) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countRange, ih]

theorem countRange_false (n : Nat) : countRange n (fun _ => false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countRange, ih]

theorem countRange_append (a b : Nat) (p : Nat → Bool) :
    countRange (a + b) p = countRange a p + countRange b (fun j => p (a + j)) := by
  induction b with
  | zero => simp [countRange]
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [countRange, ih]
    omega

theorem countRange_ne (n i : Nat) (hi : i < n) :
    countRange n (fun j => decide (i ≠ j)) = n - 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [countRange]
    by_cases heq : i = n
    · subst heq
      have h1 : countRange i (fun j => decide (i ≠ j)) = countRange i (fun _ => true) := by
        apply countRange_congr
        intro j hj
        have hne : i ≠ j := by omega
        simp [hne]
      rw [h1, countRange_true]
      simp
    · have hi' : i < n := by omega
      rw [ih hi']
      have hne : i ≠ n := heq
      simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      omega

theorem countRange_eq_single (n i : Nat) (hi : i < n) :
    countRange n (fun j => decide (j = i)) = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [countRange]
    by_cases heq : n = i
    · subst heq
      have h0 : countRange n (fun j => decide (j = n)) = countRange n (fun _ => false) := by
        apply countRange_congr
        intro j hj
        have hne : j ≠ n := by omega
        simp [hne]
      rw [h0, countRange_false]
      simp
    · have hi' : i < n := by omega
      rw [ih hi']
      simp [heq]

/-! ### 4. Bitwise XOR & `bitrev` Invariance on `{0, ..., 2^m - 1}` -/

theorem testBit_eq_false_of_lt_pow {m x i : Nat} (hx : x < 2 ^ m) (hi : m ≤ i) :
    x.testBit i = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hpow : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
  have hlt : x < 2 ^ i := Nat.lt_of_lt_of_le hx hpow
  rw [Nat.div_eq_of_lt hlt]
  decide

theorem testBit_add_two_pow {m u i : Nat} (hu : u < 2 ^ m) :
    (2 ^ m + u).testBit i = (decide (i = m) || u.testBit i) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hlt : i < m
  · have hne : ¬ (i = m) := by omega
    simp only [hne, decide_false, Bool.false_or]
    have hpow : 2 ^ m = 2 ^ i * 2 ^ (m - i) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
    have heven : 2 ^ (m - i) % 2 = 0 := by
      have h1 : m - i = (m - i - 1) + 1 := by omega
      rw [h1, Nat.pow_succ]
      omega
    rw [hpow, Nat.mul_add_div (Nat.two_pow_pos i)]
    have hmod : (2 ^ (m - i) + u / 2 ^ i) % 2 = (u / 2 ^ i) % 2 := by omega
    rw [hmod]
  · by_cases heq : i = m
    · subst heq
      simp only [decide_true, Bool.true_or]
      have hdiv : (2 ^ i + u) / 2 ^ i = 1 := by
        have h1 : 2 ^ i + u = 2 ^ i * 1 + u := by omega
        rw [h1, Nat.mul_add_div (Nat.two_pow_pos i), Nat.div_eq_of_lt hu]
      rw [hdiv]
      decide
    · have hgt : m + 1 ≤ i := by omega
      have hne : ¬ (i = m) := heq
      simp only [hne, decide_false, Bool.false_or]
      have hpow1 : 2 ^ (m + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
      have hsumlt : 2 ^ m + u < 2 ^ i := by
        have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
        omega
      have hult : u < 2 ^ i := by omega
      rw [Nat.div_eq_of_lt hsumlt, Nat.div_eq_of_lt hult]

theorem nat_xor_add_two_pow_left {m u d : Nat} (hu : u < 2 ^ m) (hd : d < 2 ^ m) :
    (2 ^ m + u) ^^^ d = 2 ^ m + (u ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_add_two_pow hu, testBit_add_two_pow (Nat.xor_lt_two_pow hu hd),
      Nat.testBit_xor]
  by_cases hi : i = m
  · subst hi
    have hdm : d.testBit i = false := testBit_eq_false_of_lt_pow hd (Nat.le_refl i)
    simp [hdm]
  · simp [hi]

theorem nat_xor_add_two_pow_right {m u d : Nat} (hu : u < 2 ^ m) (hd : d < 2 ^ m) :
    u ^^^ (2 ^ m + d) = 2 ^ m + (u ^^^ d) := by
  rw [Nat.xor_comm, nat_xor_add_two_pow_left hd hu, Nat.xor_comm]

theorem nat_xor_add_two_pow_both {m u d : Nat} (hu : u < 2 ^ m) (hd : d < 2 ^ m) :
    (2 ^ m + u) ^^^ (2 ^ m + d) = u ^^^ d := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_add_two_pow hu, testBit_add_two_pow hd, Nat.testBit_xor]
  by_cases hi : i = m
  · subst hi
    have hum : u.testBit i = false := testBit_eq_false_of_lt_pow hu (Nat.le_refl i)
    have hdm : d.testBit i = false := testBit_eq_false_of_lt_pow hd (Nat.le_refl i)
    simp [hum, hdm]
  · simp [hi]

/-- XOR with any `d < 2^m` is a bijection on `{0, ..., 2^m - 1}`, preserving `sumRange (2^m)`. -/
theorem sumRange_xor (m d : Nat) (hd : d < 2 ^ m) (f : Nat → Rat) :
    sumRange (2 ^ m) (fun u => f (u ^^^ d)) = sumRange (2 ^ m) f := by
  induction m generalizing d f with
  | zero =>
    have hd0 : d = 0 := by omega
    subst hd0
    simp [sumRange]
  | succ m ih =>
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by
      rw [Nat.pow_succ]; omega
    rw [hpow, sumRange_append, sumRange_append]
    by_cases hdm : d < 2 ^ m
    · have hleft : sumRange (2 ^ m) (fun u => f (u ^^^ d)) = sumRange (2 ^ m) f :=
        ih d hdm f
      have hright : sumRange (2 ^ m) (fun u => f ((2 ^ m + u) ^^^ d)) =
          sumRange (2 ^ m) (fun u => f (2 ^ m + u)) := by
        have hcongr : sumRange (2 ^ m) (fun u => f ((2 ^ m + u) ^^^ d)) =
            sumRange (2 ^ m) (fun u => f (2 ^ m + (u ^^^ d))) := by
          apply sumRange_congr
          intro u hu
          rw [nat_xor_add_two_pow_left hu hdm]
        rw [hcongr]
        exact ih d hdm (fun u => f (2 ^ m + u))
      rw [hleft, hright]
    · let d' := d - 2 ^ m
      have hdEq : d = 2 ^ m + d' := by omega
      have hd'lt : d' < 2 ^ m := by omega
      rw [hdEq]
      have hleft : sumRange (2 ^ m) (fun u => f (u ^^^ (2 ^ m + d'))) =
          sumRange (2 ^ m) (fun u => f (2 ^ m + u)) := by
        have hcongr : sumRange (2 ^ m) (fun u => f (u ^^^ (2 ^ m + d'))) =
            sumRange (2 ^ m) (fun u => f (2 ^ m + (u ^^^ d'))) := by
          apply sumRange_congr
          intro u hu
          rw [nat_xor_add_two_pow_right hu hd'lt]
        rw [hcongr]
        exact ih d' hd'lt (fun u => f (2 ^ m + u))
      have hright : sumRange (2 ^ m) (fun u => f ((2 ^ m + u) ^^^ (2 ^ m + d'))) =
          sumRange (2 ^ m) f := by
        have hcongr : sumRange (2 ^ m) (fun u => f ((2 ^ m + u) ^^^ (2 ^ m + d'))) =
            sumRange (2 ^ m) (fun u => f (u ^^^ d')) := by
          apply sumRange_congr
          intro u hu
          rw [nat_xor_add_two_pow_both hu hd'lt]
        rw [hcongr]
        exact ih d' hd'lt f
      rw [hleft, hright, Rat.add_comm]

theorem bitrev_lt (k x : Nat) : bitrev k x < 2 ^ k := by
  induction k generalizing x with
  | zero => simp [bitrev]
  | succ k ih =>
    simp only [bitrev]
    have hlt := ih (x / 2)
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rcases hmod with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega

/-- `bitrev k` preserves `sumRange (2^k)` (bijection on `{0, ..., 2^k - 1}`). -/
theorem sumRange_bitrev (k : Nat) (f : Nat → Rat) :
    sumRange (2 ^ k) (fun r => f (bitrev k r)) = sumRange (2 ^ k) f := by
  induction k generalizing f with
  | zero => simp [sumRange, bitrev]
  | succ k ih =>
    have hsplit : sumRange (2 ^ (k + 1)) (fun r => f (bitrev (k + 1) r)) =
        sumRange (2 ^ k) (fun q =>
          f (bitrev (k + 1) (2 * q)) + f (bitrev (k + 1) (2 * q + 1))) := by
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
      rw [hpow]
      have hms := sumRange_mul_split (2 ^ k) 2 (by omega)
        (fun q b => f (bitrev (k + 1) (2 * q + b)))
      have hcongr : sumRange (2 ^ k * 2) (fun r => f (bitrev (k + 1) r)) =
          sumRange (2 ^ k * 2) (fun w => f (bitrev (k + 1) (2 * (w / 2) + w % 2))) := by
        apply sumRange_congr
        intro w _
        have hdm : 2 * (w / 2) + w % 2 = w := by omega
        rw [hdm]
      rw [hcongr, hms]
      apply sumRange_congr
      intro q _
      simp [sumRange, Rat.zero_add]
    rw [hsplit, sumRange_add]
    have heven : sumRange (2 ^ k) (fun q => f (bitrev (k + 1) (2 * q))) =
        sumRange (2 ^ k) (fun q => f (bitrev k q)) := by
      apply sumRange_congr
      intro q _
      simp [bitrev]
    have hodd : sumRange (2 ^ k) (fun q => f (bitrev (k + 1) (2 * q + 1))) =
        sumRange (2 ^ k) (fun q => f (2 ^ k + bitrev k q)) := by
      apply sumRange_congr
      intro q _
      have hmod : (2 * q + 1) % 2 = 1 := by omega
      have hdiv : (2 * q + 1) / 2 = q := by omega
      simp [bitrev, hmod, hdiv]
    rw [heven, hodd, ih f, ih (fun u => f (2 ^ k + u))]
    have hpow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow2, sumRange_append]

end AllReduceXorVdc
