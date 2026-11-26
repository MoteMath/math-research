/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MlaKantorovichRope.Defs

/-!
# Pure-`Init` `Rat` Order, Field, `finSum`, and Cauchy-Schwarz Helpers

Zero Mathlib, zero `native_decide`. Provides elementary `Rat` order/field lemmas,
finite-sum linearity and Fubini swap over `Fin n`, and exact algebraic Cauchy-Schwarz.
-/

namespace MlaKantorovichRope

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
  | inr hle =>
    have hneg : c⁻¹ * c ≤ 0 := by
      have := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hc)
      rw [Rat.zero_mul] at this
      exact this
    exact False.elim (Rat.not_le.mpr h1 hneg)

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

theorem rat_div_mul_cancel {a b : Rat} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.mul_one]

theorem rat_mul_div_cancel {a b : Rat} (hb : b ≠ 0) : (a * b) / b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel b hb, Rat.mul_one]

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have hle : a ≤ c := Rat.le_trans (Rat.le_of_lt h1) h2
  have hne : a ≠ c := by
    intro heq
    rw [heq] at h1
    exact Rat.not_le.mpr h1 h2
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_mul_inv {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  have hab : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha h
    | inr h => exact hb h
  have h1 : (a * b) * (a⁻¹ * b⁻¹) = 1 := by
    have hre : (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by grind
    rw [hre, Rat.mul_inv_cancel a ha, Rat.mul_inv_cancel b hb]
    grind
  have h2 : (a * b)⁻¹ = (a * b)⁻¹ * ((a * b) * (a⁻¹ * b⁻¹)) := by
    rw [h1, Rat.mul_one]
  rw [h2, ← Rat.mul_assoc, Rat.inv_mul_cancel (a * b) hab, Rat.one_mul]

theorem rat_div_inv {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : (a / b)⁻¹ = b / a := by
  have hbi : b⁻¹ ≠ 0 := by
    intro h0
    have h1 := Rat.mul_inv_cancel b hb
    rw [h0, Rat.mul_zero] at h1
    exact (by decide : (0 : Rat) ≠ 1) h1
  rw [Rat.div_def, rat_mul_inv ha hbi, Rat.inv_inv, Rat.mul_comm, ← Rat.div_def]

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  have h1 : ((0 : Nat) : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr hn
  exact h1

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  exact Rat.natCast_le_natCast.mpr (Nat.zero_le n)

theorem rat_pow4_pos (b : Nat) : (0 : Rat) < ((4 ^ b : Nat) : Rat) := by
  apply rat_natCast_pos
  exact Nat.pow_pos (by decide : 0 < 4)

theorem rat_invPow4_pos (b : Nat) : (0 : Rat) < invPow4Rat b := by
  unfold invPow4Rat
  exact rat_div_pos (by decide) (rat_pow4_pos b)

theorem rat_invPow4_strict_anti {a b : Nat} (h : a < b) : invPow4Rat b < invPow4Rat a := by
  unfold invPow4Rat
  have hpow : 4 ^ a < 4 ^ b := Nat.pow_lt_pow_right (by decide : 1 < 4) h
  have hrat : ((4 ^ a : Nat) : Rat) < ((4 ^ b : Nat) : Rat) := Rat.natCast_lt_natCast.mpr hpow
  have hpa : (0 : Rat) < ((4 ^ a : Nat) : Rat) := rat_pow4_pos a
  have hpb : (0 : Rat) < ((4 ^ b : Nat) : Rat) := rat_pow4_pos b
  have hmul : (0 : Rat) < ((4 ^ a : Nat) : Rat) * ((4 ^ b : Nat) : Rat) := rat_mul_pos hpa hpb
  apply rat_lt_of_mul_pos_right hmul
  have h1 : (1 / ((4 ^ b : Nat) : Rat)) * (((4 ^ a : Nat) : Rat) * ((4 ^ b : Nat) : Rat)) =
      ((4 ^ a : Nat) : Rat) := by
    have hnb : ((4 ^ b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hpb
    rw [Rat.mul_comm ((4 ^ a : Nat) : Rat), ← Rat.mul_assoc, rat_div_mul_cancel hnb, Rat.one_mul]
  have h2 : (1 / ((4 ^ a : Nat) : Rat)) * (((4 ^ a : Nat) : Rat) * ((4 ^ b : Nat) : Rat)) =
      ((4 ^ b : Nat) : Rat) := by
    have hna : ((4 ^ a : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hpa
    rw [← Rat.mul_assoc, rat_div_mul_cancel hna, Rat.one_mul]
  rw [h1, h2]
  exact hrat

/-! ### `finSum` algebraic laws -/

theorem finSum_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem finSum_zero (n : Nat) : finSum n (fun _ => (0 : Rat)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSum, ih]
    grind

theorem finSum_add {n : Nat} (f g : Fin n → Rat) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => simp [finSum]; grind
  | succ k ih =>
    simp only [finSum]
    rw [ih]
    grind

theorem finSum_sub {n : Nat} (f g : Fin n → Rat) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  induction n with
  | zero => simp [finSum]; grind
  | succ k ih =>
    simp only [finSum]
    rw [ih]
    grind

theorem finSum_const_mul {n : Nat} (c : Rat) (f : Fin n → Rat) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    rw [ih]
    grind

theorem finSum_mul_const {n : Nat} (f : Fin n → Rat) (c : Rat) :
    finSum n (fun i => f i * c) = finSum n f * c := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    rw [ih]
    grind

theorem finSum_swap {m n : Nat} (f : Fin m → Fin n → Rat) :
    finSum m (fun i => finSum n (fun j => f i j)) =
      finSum n (fun j => finSum m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [finSum]
    exact (finSum_zero n).symm
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j)]
    rw [← finSum_add]

theorem finSum_const (n : Nat) (c : Rat) :
    finSum n (fun _ => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum, ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    rw [hcast]
    grind

theorem finSum_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ i, (0 : Rat) ≤ f i) :
    (0 : Rat) ≤ finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    exact rat_add_nonneg (ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) (h ⟨k, Nat.lt_succ_self k⟩)

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    exact rat_add_le_add (ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) (h ⟨k, Nat.lt_succ_self k⟩)

theorem finSum_ite_eq {n : Nat} (k : Fin n) (f : Fin n → Rat) :
    finSum n (fun i => if i = k then f i else 0) = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    simp only [finSum]
    by_cases hk : k.val = m
    · have hk_eq : k = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hk
      subst hk_eq
      have hleft : finSum m (fun i => if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ then
          f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) = 0 := by
        rw [finSum_congr (g := fun _ => (0 : Rat))]
        · exact finSum_zero m
        · intro i
          have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) ≠ ⟨m, Nat.lt_succ_self m⟩ := by
            intro heq
            have : i.val = m := congrArg Fin.val heq
            exact Nat.ne_of_lt i.isLt this
          simp [hne]
      rw [hleft]
      simp only [↓reduceIte]
      grind
    · have hk_lt : k.val < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp k.isLt) hk
      let k' : Fin m := ⟨k.val, hk_lt⟩
      have hleft : finSum m (fun i => if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = k then
          f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) = f k := by
        have hstep := ih k' (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        have hcongr : finSum m (fun i => if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = k then
            f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) =
            finSum m (fun i => if i = k' then f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) := by
          apply finSum_congr
          intro i
          by_cases h1 : i = k'
          · have h2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = k := by
              apply Fin.ext
              exact congrArg (fun x : Fin m => x.val) h1
            simp only [h2, ↓reduceIte]
            simp only [h1, ↓reduceIte]
          · have h2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) ≠ k := by
              intro heq
              apply h1
              apply Fin.ext
              exact congrArg (fun x : Fin (m + 1) => x.val) heq
            simp only [h2, ↓reduceIte]
            simp only [h1, ↓reduceIte]
        rw [hcongr, hstep]
      have hne : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ≠ k := by
        intro heq
        exact hk (congrArg Fin.val heq).symm
      rw [hleft]
      simp only [hne, ↓reduceIte]
      grind

theorem finSum_ite_eq_right {n : Nat} (k : Fin n) (f : Fin n → Rat) :
    finSum n (fun i => if k = i then f i else 0) = f k := by
  rw [finSum_congr (g := fun i => if i = k then f i else 0)]
  · exact finSum_ite_eq k f
  · intro i
    by_cases h : i = k
    · subst h; simp
    · have h' : k ≠ i := Ne.symm h
      simp [h, h']

/-- Exact Lagrange identity over `Fin n`:
    `∑_i ∑_j (a_i b_j - a_j b_i)^2 = 2 (∑ a_i^2)(∑ b_j^2) - 2 (∑ a_i b_i)^2`. -/
theorem finSum_lagrange_identity {n : Nat} (a b : Fin n → Rat) :
    finSum n (fun i => finSum n (fun j => (a i * b j - a j * b i) * (a i * b j - a j * b i))) =
      2 * (finSum n (fun i => a i * a i) * finSum n (fun j => b j * b j) -
        finSum n (fun i => a i * b i) * finSum n (fun i => a i * b i)) := by
  have hexpand : ∀ i j : Fin n,
      (a i * b j - a j * b i) * (a i * b j - a j * b i) =
        ((a i * a i) * (b j * b j) + (b i * b i) * (a j * a j)) -
          2 * ((a i * b i) * (a j * b j)) := by
    intro i j; grind
  have h1 : finSum n (fun i => finSum n (fun j => (a i * b j - a j * b i) * (a i * b j - a j * b i))) =
      finSum n (fun i => finSum n (fun j =>
        ((a i * a i) * (b j * b j) + (b i * b i) * (a j * a j)) -
          2 * ((a i * b i) * (a j * b j)))) := by
    apply finSum_congr; intro i; apply finSum_congr; intro j; exact hexpand i j
  rw [h1]
  have hinner : ∀ i : Fin n,
      finSum n (fun j => ((a i * a i) * (b j * b j) + (b i * b i) * (a j * a j)) -
          2 * ((a i * b i) * (a j * b j))) =
        (a i * a i) * finSum n (fun j => b j * b j) +
        (b i * b i) * finSum n (fun j => a j * a j) -
        2 * ((a i * b i) * finSum n (fun j => a j * b j)) := by
    intro i
    rw [finSum_sub, finSum_add, finSum_const_mul, finSum_const_mul, finSum_const_mul, finSum_const_mul]
  rw [finSum_congr hinner]
  rw [finSum_sub, finSum_add, finSum_mul_const, finSum_mul_const, finSum_const_mul, finSum_mul_const]
  grind

/-- Exact Cauchy-Schwarz inequality over `Fin n` in `Rat`. -/
theorem finSum_cauchy_schwarz {n : Nat} (a b : Fin n → Rat) :
    finSum n (fun i => a i * b i) * finSum n (fun i => a i * b i) ≤
      finSum n (fun i => a i * a i) * finSum n (fun i => b i * b i) := by
  have hnonneg : (0 : Rat) ≤
      finSum n (fun i => finSum n (fun j => (a i * b j - a j * b i) * (a i * b j - a j * b i))) := by
    apply finSum_nonneg; intro i
    apply finSum_nonneg; intro j
    exact rat_sq_nonneg _
  rw [finSum_lagrange_identity] at hnonneg
  have hdiff : (0 : Rat) ≤
      finSum n (fun i => a i * a i) * finSum n (fun j => b j * b j) -
        finSum n (fun i => a i * b i) * finSum n (fun i => a i * b i) := by
    have h2 : (0 : Rat) < 2 := by decide
    have hmul := rat_div_nonneg hnonneg h2
    have hsimp : (2 * (finSum n (fun i => a i * a i) * finSum n (fun j => b j * b j) -
        finSum n (fun i => a i * b i) * finSum n (fun i => a i * b i))) / 2 =
        finSum n (fun i => a i * a i) * finSum n (fun j => b j * b j) -
        finSum n (fun i => a i * b i) * finSum n (fun i => a i * b i) := by
      rw [Rat.mul_comm, rat_mul_div_cancel (by decide)]
    rw [hsimp] at hmul
    exact hmul
  exact rat_le_of_sub_nonneg hdiff

theorem normSq_nonneg {n : Nat} (v : Fin n → Rat) : (0 : Rat) ≤ normSq v := by
  unfold normSq dot
  apply finSum_nonneg
  intro i
  exact rat_sq_nonneg (v i)

end MlaKantorovichRope
