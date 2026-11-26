/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XorVdcFp4Dither.Defs

/-!
# Pure-`Init` `Rat` Order, Finite Sums, Product Decomposition, and Bitwise XOR Invariance

Zero Mathlib, zero `native_decide`.
-/

namespace XorVdcFp4Dither

/-! ### 1. Elementary `Rat` Order and Field Helpers -/

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

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_le_div_of_pos_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) < c) :
    a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))

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
  have hle : (0 : Rat) ≤ a + b := Rat.le_trans (Rat.le_of_lt hb) (Rat.le_of_lt h1)
  have hne : (0 : Rat) ≠ a + b := by
    intro heq
    have : a + b < b := by rw [← heq]; exact hb
    exact Rat.not_lt.mpr (Rat.le_of_lt h1) this
  exact Rat.lt_of_le_of_ne hle hne

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

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  have h : (0 : Int) < (n : Int) := by omega
  exact Rat.intCast_lt_intCast.mpr h

theorem rat_natCast_ne_zero {n : Nat} (hn : 0 < n) : (n : Rat) ≠ 0 :=
  Rat.ne_of_gt (rat_natCast_pos hn)

theorem rat_natCast_le_natCast {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have h1 : (a : Int) ≤ (b : Int) := by omega
  exact Rat.intCast_le_intCast.mpr h1

theorem rat_natCast_add (a b : Nat) : ((a + b : Nat) : Rat) = (a : Rat) + (b : Rat) := by
  grind

theorem rat_natCast_mul (a b : Nat) : ((a * b : Nat) : Rat) = (a : Rat) * (b : Rat) := by
  grind

theorem rat_pow2_pos (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) :=
  rat_natCast_pos (Nat.two_pow_pos n)

theorem rat_pow2_ne_zero (n : Nat) : ((2 ^ n : Nat) : Rat) ≠ 0 :=
  Rat.ne_of_gt (rat_pow2_pos n)

/-! ### 2. `sumRange` Algebra -/

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

theorem sumRange_mul_right (n : Nat) (f : Nat → Rat) (c : Rat) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
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

theorem sumRange_swap (m n : Nat) (f : Nat → Nat → Rat) :
    sumRange m (fun i => sumRange n (fun j => f i j)) =
    sumRange n (fun j => sumRange m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumRange]
    have h0 : sumRange n (fun _ => (0 : Rat)) = 0 := by
      rw [sumRange_const]; grind
    exact h0.symm
  | succ m ih =>
    simp only [sumRange]
    rw [ih, ← sumRange_add]

theorem sumRange_append (a b : Nat) (f : Nat → Rat) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun j => f (a + j)) := by
  induction b with
  | zero => simp [sumRange]; grind
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [sumRange]
    rw [ih]
    grind

/-- Product decomposition: `∑_{w < A * B} f(w / B, w % B) = ∑_{q < A} ∑_{r < B} f(q, r)`. -/
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

/-- Indicator sum `∑_{u < M} (if u < p then 1 else 0) = p` for `p ≤ M`. -/
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

/-- Sum of `u` over `0..n-1` equals `n * (n - 1) / 2`. -/
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

/-- Sum of squared centered indices `∑_{r < R} (2r - (R - 1))^2 = R (R^2 - 1) / 3`. -/
theorem sumRange_centered_sq (R : Nat) :
    sumRange R (fun r => (2 * (r : Rat) - ((R : Rat) - 1)) * (2 * (r : Rat) - ((R : Rat) - 1))) =
    ((R : Rat) * ((R : Rat) * (R : Rat) - 1)) / 3 := by
  induction R with
  | zero => simp [sumRange]; grind
  | succ R ih =>
    simp only [sumRange]
    have hsplit :
        sumRange R (fun r =>
          (2 * (r : Rat) - (((R + 1 : Nat) : Rat) - 1)) *
          (2 * (r : Rat) - (((R + 1 : Nat) : Rat) - 1))) =
        sumRange R (fun r =>
          (2 * (r : Rat) - ((R : Rat) - 1)) * (2 * (r : Rat) - ((R : Rat) - 1))) -
        2 * sumRange R (fun r => 2 * (r : Rat) - ((R : Rat) - 1)) +
        sumRange R (fun _ => (1 : Rat)) := by
      have hcongr :
          sumRange R (fun r =>
            (2 * (r : Rat) - (((R + 1 : Nat) : Rat) - 1)) *
            (2 * (r : Rat) - (((R + 1 : Nat) : Rat) - 1))) =
          sumRange R (fun r =>
            ((2 * (r : Rat) - ((R : Rat) - 1)) * (2 * (r : Rat) - ((R : Rat) - 1)) -
              2 * (2 * (r : Rat) - ((R : Rat) - 1))) + 1) := by
        apply sumRange_congr
        intro r _
        rw [rat_natCast_add]
        have h1 : ((1 : Nat) : Rat) = 1 := rfl
        rw [h1]
        grind
      rw [hcongr, sumRange_add, sumRange_sub, sumRange_mul_left]
    have hmean0 : sumRange R (fun r => 2 * (r : Rat) - ((R : Rat) - 1)) = 0 := by
      rw [sumRange_sub, sumRange_mul_left, sumRange_nat_id, sumRange_const]
      grind
    rw [hsplit, ih, hmean0, sumRange_const, rat_natCast_add]
    have h1 : ((1 : Nat) : Rat) = 1 := rfl
    rw [h1]
    grind

/-- Geometric sum `∑_{s < b} 4^s = (4^b - 1) / 3`. -/
theorem sumRange_geom4 (b : Nat) :
    sumRange b (fun s => ((4 ^ s : Nat) : Rat)) = (((4 ^ b : Nat) : Rat) - 1) / 3 := by
  induction b with
  | zero => simp [sumRange]; grind
  | succ b ih =>
    simp only [sumRange, ih]
    have hpow : (4 ^ (b + 1) : Nat) = 4 * 4 ^ b := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, rat_natCast_mul]
    have h4 : ((4 : Nat) : Rat) = 4 := rfl
    rw [h4]
    grind

/-! ### 3. Bitwise XOR Invariance on `{0, ..., 2^m - 1}` -/

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
    have hge1 : 1 ≤ m - i := by omega
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
    · have hge : 2 ^ m ≤ d := by omega
      let d' := d - 2 ^ m
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

theorem bitrev_lt (b x : Nat) : bitrev b x < 2 ^ b := by
  induction b generalizing x with
  | zero => simp [bitrev]
  | succ b ih =>
    simp only [bitrev]
    have hlt := ih (x / 2)
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hpow : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
    rcases hmod with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega

theorem xorVdcOffset_lt (m b i : Nat) (hbm : b ≤ m) :
    xorVdcOffset m b i < 2 ^ m := by
  unfold xorVdcOffset
  rw [Nat.shiftLeft_eq]
  have hbr : bitrev b i < 2 ^ b := bitrev_lt b i
  have hmul : bitrev b i * 2 ^ (m - b) < 2 ^ b * 2 ^ (m - b) :=
    Nat.mul_lt_mul_of_pos_right hbr (Nat.two_pow_pos (m - b))
  have hpow : 2 ^ b * 2 ^ (m - b) = 2 ^ m := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hbm]
  omega

end XorVdcFp4Dither
