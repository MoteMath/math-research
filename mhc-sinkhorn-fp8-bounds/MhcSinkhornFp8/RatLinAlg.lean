/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MhcSinkhornFp8.Defs

/-!
# Pure-`Init` `Rat` Order, Finite Sums, Double Sums, Cauchy–Schwarz, and Matrix Iteration

Zero Mathlib, zero `native_decide`. Provides the reusable algebraic backbone for all six
headline theorems.
-/

namespace MhcSinkhornFp8

/-! ### 1. Elementary `Rat` Order & Field Helpers -/

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

theorem rat_add_pos_of_nonneg_of_pos {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a + b := by
  rw [Rat.add_comm]
  exact rat_add_pos_of_pos_of_nonneg hb ha

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

theorem rat_mul_div_mul_left {c a b : Rat} (hc : c ≠ 0) (hb : b ≠ 0) :
    (c * a) / (c * b) = a / b := by
  have hcb : c * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hc h
    | inr h => exact hb h
  have hmul : ((c * a) / (c * b) - a / b) * (c * b) = 0 := by
    have h1 : (c * a) / (c * b) * (c * b) = c * a := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hcb, Rat.mul_one]
    have h2 : (a / b) * (c * b) = c * a := by
      rw [Rat.div_def, Rat.mul_comm c b, Rat.mul_assoc a b⁻¹, ← Rat.mul_assoc b⁻¹ b c,
          Rat.inv_mul_cancel b hb, Rat.one_mul, Rat.mul_comm]
    grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h => grind
  | inr h => exact False.elim (hcb h)

theorem rat_mul_div_mul_right {a b c : Rat} (hc : c ≠ 0) (hb : b ≠ 0) :
    (a * c) / (b * c) = a / b := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_div_mul_left hc hb

theorem rat_div_mul_cancel {a b : Rat} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.mul_one]

theorem rat_div_self {a : Rat} (ha : a ≠ 0) : a / a = 1 := by
  rw [Rat.div_def, Rat.mul_inv_cancel a ha]

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

theorem rat_natCast_pos {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) := by
  have h1 : (1 : Rat) ≤ (n : Rat) := rat_natCast_le h
  have hne : (0 : Rat) ≠ (n : Rat) := by
    intro heq
    rw [← heq] at h1
    exact Rat.not_le.mpr (by decide : (0 : Rat) < 1) h1
  exact Rat.lt_of_le_of_ne (Rat.le_trans (by decide : (0 : Rat) ≤ 1) h1) hne

theorem ratPow_nonneg {a : Rat} (ha : (0 : Rat) ≤ a) (k : Nat) : (0 : Rat) ≤ ratPow a k := by
  induction k with
  | zero => simp only [ratPow]; decide
  | succ k ih =>
    simp only [ratPow]
    exact Rat.mul_nonneg ha ih

theorem ratPow_mul (a b : Rat) (k : Nat) : ratPow (a * b) k = ratPow a k * ratPow b k := by
  induction k with
  | zero => simp [ratPow]
  | succ k ih =>
    simp only [ratPow, ih]
    grind

/-! ### 2. `sumFinRat` Algebra, Double Sums, and Lagrange's Cauchy–Schwarz -/

theorem sumFinRat_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    sumFinRat n f = sumFinRat n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFinRat]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem sumFinRat_zero (n : Nat) : sumFinRat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumFinRat, ih]; grind

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

theorem sumFinRat_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumFinRat n (fun i => f i * c) = sumFinRat n f * c := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih =>
    simp only [sumFinRat]
    rw [ih]
    grind

theorem sumFinRat_div_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumFinRat n (fun i => f i / c) = sumFinRat n f / c := by
  have h1 : sumFinRat n (fun i => f i / c) = sumFinRat n (fun i => f i * c⁻¹) := by
    apply sumFinRat_congr
    intro i
    exact Rat.div_def (f i) c
  rw [h1, sumFinRat_mul_right, ← Rat.div_def]

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

theorem sumFinRat_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ i, (0 : Rat) ≤ f i) :
    (0 : Rat) ≤ sumFinRat n f := by
  have hle := sumFinRat_le (f := fun _ => (0 : Rat)) (g := f) h
  rw [sumFinRat_zero] at hle
  exact hle

theorem sumFinRat_pos_of_all_pos {n : Nat} (hn : 0 < n) {f : Fin n → Rat}
    (h : ∀ i, (0 : Rat) < f i) : (0 : Rat) < sumFinRat n f := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [sumFinRat]
    have hge : (0 : Rat) ≤ sumFinRat m (fun i => f i.castSucc) :=
      sumFinRat_nonneg (fun i => Rat.le_of_lt (h i.castSucc))
    exact rat_add_pos_of_nonneg_of_pos hge (h (Fin.last m))

theorem sumFinRat_eq_zero_of_nonneg {n : Nat} {f : Fin n → Rat}
    (hnn : ∀ i, (0 : Rat) ≤ f i) (hsum : sumFinRat n f = 0) : ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih =>
    simp only [sumFinRat] at hsum
    have h1 : (0 : Rat) ≤ sumFinRat m (fun i => f i.castSucc) :=
      sumFinRat_nonneg (fun i => hnn i.castSucc)
    have h2 : (0 : Rat) ≤ f (Fin.last m) := hnn (Fin.last m)
    have hlast0 : f (Fin.last m) = 0 := by
      cases Rat.le_total (a := f (Fin.last m)) (b := 0) with
      | inl hle => exact Rat.le_antisymm hle h2
      | inr _ =>
        by_cases hz : f (Fin.last m) = 0
        · exact hz
        · have hpos : (0 : Rat) < f (Fin.last m) := Rat.lt_of_le_of_ne h2 (Ne.symm hz)
          have htot := rat_add_pos_of_nonneg_of_pos h1 hpos
          rw [hsum] at htot
          exact False.elim (Rat.not_le.mpr htot Rat.le_refl)
    have hrest0 : sumFinRat m (fun i => f i.castSucc) = 0 := by
      rw [hlast0, Rat.add_zero] at hsum
      exact hsum
    have hih := ih (fun i => hnn i.castSucc) hrest0
    intro i
    by_cases hl : i = Fin.last m
    · rw [hl]; exact hlast0
    · have hlt : i.val < m := by
        have hlt1 := i.isLt
        have hne : i.val ≠ m := fun hv => hl (Fin.ext hv)
        omega
      have heq : i = (⟨i.val, hlt⟩ : Fin m).castSucc := Fin.ext rfl
      rw [heq]
      exact hih ⟨i.val, hlt⟩

/-- Fubini / swap of two finite rational sums. -/
theorem sumFinRat_swap {m n : Nat} (f : Fin m → Fin n → Rat) :
    sumFinRat m (fun i => sumFinRat n (fun j => f i j)) =
    sumFinRat n (fun j => sumFinRat m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFinRat]
    exact (sumFinRat_zero n).symm
  | succ m ih =>
    simp only [sumFinRat]
    rw [ih (fun i j => f i.castSucc j), ← sumFinRat_add]

/-- Weighted Cauchy–Schwarz via Lagrange's identity in pure `Rat` (zero square roots):
    `(∑_j p_j v_j)^2 ≤ (∑_j p_j) * (∑_j p_j v_j^2)` whenever `∀ j, 0 ≤ p_j`. -/
theorem weighted_cauchy_schwarz {n : Nat} (p v : Fin n → Rat)
    (hp : ∀ j, (0 : Rat) ≤ p j) :
    sumFinRat n (fun j => p j * v j) * sumFinRat n (fun j => p j * v j) ≤
    sumFinRat n p * sumFinRat n (fun j => p j * (v j * v j)) := by
  have hlag : (0 : Rat) ≤
      sumFinRat n (fun i => sumFinRat n (fun j => p i * p j * ((v i - v j) * (v i - v j)))) := by
    apply sumFinRat_nonneg
    intro i
    apply sumFinRat_nonneg
    intro j
    exact Rat.mul_nonneg (Rat.mul_nonneg (hp i) (hp j)) (rat_sq_nonneg (v i - v j))
  have hexpand :
      sumFinRat n (fun i => sumFinRat n (fun j => p i * p j * ((v i - v j) * (v i - v j)))) =
      2 * (sumFinRat n p * sumFinRat n (fun j => p j * (v j * v j)) -
           sumFinRat n (fun j => p j * v j) * sumFinRat n (fun j => p j * v j)) := by
    have hinner : ∀ i : Fin n,
        sumFinRat n (fun j => p i * p j * ((v i - v j) * (v i - v j))) =
        (p i * (v i * v i)) * sumFinRat n p -
        2 * (p i * v i) * sumFinRat n (fun j => p j * v j) +
        p i * sumFinRat n (fun j => p j * (v j * v j)) := by
      intro i
      have hterm : ∀ j : Fin n,
          p i * p j * ((v i - v j) * (v i - v j)) =
          ((p i * (v i * v i)) * p j - (2 * (p i * v i)) * (p j * v j)) +
          p i * (p j * (v j * v j)) := by
        intro j; grind
      rw [sumFinRat_congr hterm, sumFinRat_add, sumFinRat_sub,
          sumFinRat_mul_left, sumFinRat_mul_left, sumFinRat_mul_left]
    rw [sumFinRat_congr hinner, sumFinRat_add, sumFinRat_sub,
        sumFinRat_mul_right, sumFinRat_mul_right, sumFinRat_mul_right,
        sumFinRat_mul_left]
    grind
  rw [hexpand] at hlag
  have hdiff : (0 : Rat) ≤
      sumFinRat n p * sumFinRat n (fun j => p j * (v j * v j)) -
      sumFinRat n (fun j => p j * v j) * sumFinRat n (fun j => p j * v j) := by
    have hhalf := rat_mul_le_mul_of_nonneg_left hlag (rat_div_nonneg (by decide) (by decide) : (0 : Rat) ≤ (1 / 2 : Rat))
    have h0 : (1 / 2 : Rat) * 0 = 0 := by grind
    have h1 : (1 / 2 : Rat) * (2 * (sumFinRat n p * sumFinRat n (fun j => p j * (v j * v j)) -
        sumFinRat n (fun j => p j * v j) * sumFinRat n (fun j => p j * v j))) =
        sumFinRat n p * sumFinRat n (fun j => p j * (v j * v j)) -
        sumFinRat n (fun j => p j * v j) * sumFinRat n (fun j => p j * v j) := by grind
    rw [h0, h1] at hhalf
    exact hhalf
  exact rat_le_of_sub_nonneg hdiff

/-- Unweighted Cauchy–Schwarz: `(∑_j v_j)^2 ≤ n * ∑_j v_j^2`. -/
theorem cauchy_schwarz_ones {n : Nat} (v : Fin n → Rat) :
    sumFinRat n v * sumFinRat n v ≤ (n : Rat) * sumFinRat n (fun j => v j * v j) := by
  have h := weighted_cauchy_schwarz (fun _ : Fin n => (1 : Rat)) v (fun _ => by decide)
  have h1 : sumFinRat n (fun j : Fin n => (1 : Rat) * v j) = sumFinRat n v :=
    sumFinRat_congr (fun j => by grind)
  have h2 : sumFinRat n (fun j : Fin n => (1 : Rat) * (v j * v j)) = sumFinRat n (fun j => v j * v j) :=
    sumFinRat_congr (fun j => by grind)
  have h3 : sumFinRat n (fun _ : Fin n => (1 : Rat)) = (n : Rat) := by
    rw [sumFinRat_const]; grind
  rw [h1, h2, h3] at h
  exact h

/-! ### 3. Matrix Iteration & Collatz–Wielandt Lower-Bound Machinery -/

/-- Entrywise monotonicity of `matVecMul` for nonnegative matrices. -/
theorem matVecMul_mono {n : Nat} {A : RatMat n} (hA : ∀ i j, (0 : Rat) ≤ A i j)
    {u v : RatVec n} (huv : ∀ j, u j ≤ v j) :
    ∀ i, matVecMul A u i ≤ matVecMul A v i := by
  intro i
  simp only [matVecMul]
  apply sumFinRat_le
  intro j
  exact rat_mul_le_mul_of_nonneg_left (huv j) (hA i j)

/-- Scaling of `matVecMul`: `A (c • v) = c • (A v)`. -/
theorem matVecMul_scale {n : Nat} (A : RatMat n) (c : Rat) (v : RatVec n) (i : Fin n) :
    matVecMul A (fun j => c * v j) i = c * matVecMul A v i := by
  simp only [matVecMul]
  have h1 : ∀ j, A i j * (c * v j) = c * (A i j * v j) := fun j => by grind
  rw [sumFinRat_congr h1, sumFinRat_mul_left]

/-- Exact eigenvector iteration: if `A v = λ • v`, then `A^L v = λ^L • v` for all `L`. -/
theorem vecApplyIter_eigenvector {n : Nat} (A : RatMat n) (v : RatVec n) (lam : Rat)
    (heig : ∀ i, matVecMul A v i = lam * v i) :
    ∀ (L : Nat) (i : Fin n), vecApplyIter A L v i = ratPow lam L * v i := by
  intro L
  induction L with
  | zero =>
    intro i; simp [vecApplyIter, ratPow]
  | succ L ih =>
    intro i
    simp only [vecApplyIter, ratPow]
    have hcongr : matVecMul A (vecApplyIter A L v) i =
        matVecMul A (fun j => ratPow lam L * v j) i := by
      simp only [matVecMul]
      apply sumFinRat_congr
      intro j
      rw [ih j]
    rw [hcongr, matVecMul_scale, heig i]
    grind

/-- Exact norm-squared of an eigenvector iterate: `‖A^L v‖_2^2 = (λ^L)^2 ‖v‖_2^2`. -/
theorem normSq_vecApplyIter_eigenvector {n : Nat} (A : RatMat n) (v : RatVec n) (lam : Rat)
    (heig : ∀ i, matVecMul A v i = lam * v i) (L : Nat) :
    normSq (vecApplyIter A L v) = ratPow lam L * ratPow lam L * normSq v := by
  simp only [normSq]
  have hterm : ∀ i : Fin n,
      vecApplyIter A L v i * vecApplyIter A L v i =
      (ratPow lam L * ratPow lam L) * (v i * v i) := by
    intro i
    rw [vecApplyIter_eigenvector A v lam heig L i]
    grind
  rw [sumFinRat_congr hterm, sumFinRat_mul_left]

/-- Collatz–Wielandt exponential lower bound for nonnegative matrices:
    if `A ≥ 0`, `v ≥ 0`, `λ ≥ 0`, and `λ v ≤ A v` entrywise, then
    `λ^L v ≤ A^L v` entrywise and `(λ^L)^2 ‖v‖_2^2 ≤ ‖A^L v‖_2^2` for ALL `L : Nat`. -/
theorem vecApplyIter_collatz_wielandt {n : Nat} {A : RatMat n}
    (hA : ∀ i j, (0 : Rat) ≤ A i j)
    {v : RatVec n} (hv : ∀ i, (0 : Rat) ≤ v i)
    {lam : Rat} (hlam : (0 : Rat) ≤ lam)
    (hstep : ∀ i, lam * v i ≤ matVecMul A v i) :
    ∀ (L : Nat),
      (∀ i, ratPow lam L * v i ≤ vecApplyIter A L v i) ∧
      ratPow lam L * ratPow lam L * normSq v ≤ normSq (vecApplyIter A L v) := by
  have hentry : ∀ (L : Nat) (i : Fin n), ratPow lam L * v i ≤ vecApplyIter A L v i := by
    intro L
    induction L with
    | zero =>
      intro i
      simp only [vecApplyIter, ratPow]
      have : (1 : Rat) * v i = v i := by grind
      rw [this]; exact Rat.le_refl
    | succ L ih =>
      intro i
      simp only [vecApplyIter, ratPow]
      have h1 : ratPow lam L * (lam * v i) ≤ ratPow lam L * matVecMul A v i :=
        rat_mul_le_mul_of_nonneg_left (hstep i) (ratPow_nonneg hlam L)
      have h2 : ratPow lam L * matVecMul A v i = matVecMul A (fun j => ratPow lam L * v j) i :=
        (matVecMul_scale A (ratPow lam L) v i).symm
      have h3 : matVecMul A (fun j => ratPow lam L * v j) i ≤ matVecMul A (vecApplyIter A L v) i :=
        matVecMul_mono hA ih i
      have hcomm : lam * ratPow lam L * v i = ratPow lam L * (lam * v i) := by grind
      rw [hcomm]
      exact Rat.le_trans h1 (h2 ▸ h3)
  intro L
  refine ⟨hentry L, ?_⟩
  simp only [normSq]
  rw [← sumFinRat_mul_left]
  apply sumFinRat_le
  intro i
  have hnn : (0 : Rat) ≤ ratPow lam L * v i := Rat.mul_nonneg (ratPow_nonneg hlam L) (hv i)
  have hle : ratPow lam L * v i ≤ vecApplyIter A L v i := hentry L i
  have hsq : (ratPow lam L * v i) * (ratPow lam L * v i) ≤
      vecApplyIter A L v i * vecApplyIter A L v i := by
    have h1 := rat_mul_le_mul_of_nonneg_left hle hnn
    have h2 := rat_mul_le_mul_of_nonneg_right hle (Rat.le_trans hnn hle)
    exact Rat.le_trans h1 h2
  have heq : ratPow lam L * ratPow lam L * (v i * v i) =
      (ratPow lam L * v i) * (ratPow lam L * v i) := by grind
  rw [heq]
  exact hsq

end MhcSinkhornFp8
