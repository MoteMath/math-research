/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitnetContraction.Defs

/-!
# Pure-`Init` Rational & Finite-Sum Helper Theorems

Basic order, algebraic, `Rat.abs`, and `sumRat` lemmas in pure Lean 4 `Init` (zero Mathlib).
-/

namespace BitnetContraction

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

theorem rat_mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have hle : 0 ≤ a * b := rat_mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  rw [Rat.lt_iff_le_and_ne]
  refine ⟨hle, ?_⟩
  intro heq
  have ha0 : a ≠ 0 := (Rat.lt_iff_le_and_ne.mp ha).2.symm
  have hb0 : b ≠ 0 := (Rat.lt_iff_le_and_ne.mp hb).2.symm
  have : a * b ≠ 0 := by grind
  exact this heq.symm

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

theorem rat_neg_le_neg {a b : Rat} (h : a ≤ b) : -b ≤ -a := by
  have h1 := rat_sub_nonneg_of_le h
  apply rat_le_of_sub_nonneg
  have heq : -a - -b = b - a := by grind
  rw [heq]
  exact h1

theorem rat_inv_pos {a : Rat} (ha : 0 < a) : 0 < a⁻¹ := by
  have ha0 : a ≠ 0 := (Rat.lt_iff_le_and_ne.mp ha).2.symm
  cases @Rat.le_total 0 a⁻¹ with
  | inl h =>
    rw [Rat.lt_iff_le_and_ne]
    refine ⟨h, ?_⟩
    intro heq
    have hmul : a * a⁻¹ = 1 := by grind
    rw [← heq] at hmul
    have : a * 0 = 0 := by grind
    rw [this] at hmul
    exact absurd hmul (by decide)
  | inr h =>
    have hmul : a * a⁻¹ ≤ a * 0 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt ha)
    have h1 : a * a⁻¹ = 1 := by grind
    have h2 : a * 0 = 0 := by grind
    rw [h1, h2] at hmul
    exact absurd hmul (by decide)

theorem rat_div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  have heq : a / b = a * b⁻¹ := by grind
  rw [heq]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  have heq : a / b = a * b⁻¹ := by grind
  rw [heq]
  exact rat_mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_le_div_of_nonneg {a b c : Rat} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  have h1 : a * c⁻¹ ≤ b * c⁻¹ :=
    Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))
  have e1 : a / c = a * c⁻¹ := by grind
  have e2 : b / c = b * c⁻¹ := by grind
  rw [e1, e2]
  exact h1

theorem rat_mul_le_mul_of_nonneg {a b c d : Rat}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a ≤ c) (h2 : b ≤ d) : a * b ≤ c * d := by
  have hc : 0 ≤ c := Rat.le_trans ha h1
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right h1 hb)
    (Rat.mul_le_mul_of_nonneg_left h2 hc)

theorem rat_le_of_mul_le_mul_left {a b c : Rat} (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b := by
  have h1 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt (rat_inv_pos hc))
  have hc0 : c ≠ 0 := (Rat.lt_iff_le_and_ne.mp hc).2.symm
  have e1 : c⁻¹ * (c * a) = a := by grind
  have e2 : c⁻¹ * (c * b) = b := by grind
  rw [e1, e2] at h1
  exact h1

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have hstep : (0 : Rat) + 0 ≤ (k : Rat) + 1 :=
      rat_add_le_add ih (by decide : (0 : Rat) ≤ 1)
    have h0 : (0 : Rat) + 0 = 0 := by grind
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [h0] at hstep
    rw [hcast]
    exact hstep

theorem rat_natCast_pos {n : Nat} (hn : 1 ≤ n) : (0 : Rat) < (n : Rat) := by
  cases n with
  | zero => omega
  | succ k =>
    have hk : (0 : Rat) ≤ (k : Rat) := rat_natCast_nonneg k
    have h1 : (0 : Rat) < 1 := by decide
    have hsum : (0 : Rat) + 0 < (k : Rat) + 1 := rat_add_lt_add_of_le_of_lt hk h1
    have h0 : (0 : Rat) + 0 = 0 := by grind
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [h0] at hsum
    rw [hcast]
    exact hsum

theorem rat_natCast_le {m n : Nat} (h : m ≤ n) : (m : Rat) ≤ (n : Rat) := by
  have hd : n = m + (n - m) := by omega
  rw [hd]
  have hcast : ((m + (n - m) : Nat) : Rat) = (m : Rat) + ((n - m : Nat) : Rat) := by grind
  rw [hcast]
  have hnn := rat_natCast_nonneg (n - m)
  have h1 : (m : Rat) + 0 ≤ (m : Rat) + ((n - m : Nat) : Rat) := Rat.add_le_add_left.mpr hnn
  have h2 : (m : Rat) + 0 = (m : Rat) := by grind
  rw [h2] at h1
  exact h1

/-! ## `Rat.abs` Lemmas -/

theorem rat_abs_eq_of_nonneg {x : Rat} (hx : 0 ≤ x) : x.abs = x := by
  simp [Rat.abs, hx]

theorem rat_abs_eq_neg_of_nonpos {x : Rat} (hx : x ≤ 0) : x.abs = -x := by
  by_cases h0 : 0 ≤ x
  · have hx0 : x = 0 := Rat.le_antisymm hx h0
    subst hx0
    decide
  · simp [Rat.abs, h0]

theorem rat_abs_nonneg (x : Rat) : 0 ≤ x.abs := by
  cases @Rat.le_total 0 x with
  | inl h => rw [rat_abs_eq_of_nonneg h]; exact h
  | inr h =>
    rw [rat_abs_eq_neg_of_nonpos h]
    have h1 := rat_sub_nonneg_of_le h
    have h2 : 0 - x = -x := by grind
    rw [h2] at h1
    exact h1

theorem rat_abs_sq (x : Rat) : x.abs * x.abs = x * x := by
  cases @Rat.le_total 0 x with
  | inl h => rw [rat_abs_eq_of_nonneg h]
  | inr h =>
    rw [rat_abs_eq_neg_of_nonpos h]
    grind

theorem rat_abs_eq_zero_iff (x : Rat) : x.abs = 0 ↔ x = 0 := by
  constructor
  · intro h
    cases @Rat.le_total 0 x with
    | inl hx => rw [rat_abs_eq_of_nonneg hx] at h; exact h
    | inr hx =>
      rw [rat_abs_eq_neg_of_nonpos hx] at h
      grind
  · intro h; subst h; decide

/-! ## `sumRat` Lemmas -/

theorem sumRat_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    sumRat f = sumRat g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => h i.castSucc), h ⟨k, Nat.lt_succ_self k⟩]

theorem sumRat_zero {n : Nat} : sumRat (fun _ : Fin n => (0 : Rat)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRat, ih]
    grind

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

theorem sumRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumRat (fun i => c * f i) = c * sumRat f := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem sumRat_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumRat (fun i => f i * c) = sumRat f * c := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem sumRat_div_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumRat (fun i => f i / c) = sumRat f / c := by
  have h1 : sumRat (fun i => f i / c) = sumRat (fun i => f i * c⁻¹) :=
    sumRat_congr (fun i => by grind)
  rw [h1, sumRat_mul_right]
  grind

theorem sumRat_const {n : Nat} (c : Rat) :
    sumRat (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [hcast]
    grind

theorem sumRat_le_sumRat {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    sumRat f ≤ sumRat g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [sumRat]
    exact rat_add_le_add (ih (fun i => h i.castSucc)) (h ⟨k, Nat.lt_succ_self k⟩)

theorem sumRat_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumRat f := by
  have h1 := sumRat_le_sumRat (f := fun _ : Fin n => (0 : Rat)) (g := f) h
  rw [sumRat_zero] at h1
  exact h1

theorem sumRat_lt_sumRat_of_le_of_lt {n : Nat} {f g : Fin n → Rat}
    (hle : ∀ i, f i ≤ g i) (hlt : ∃ i, f i < g i) :
    sumRat f < sumRat g := by
  induction n with
  | zero =>
    obtain ⟨i, _⟩ := hlt
    exact Fin.elim0 i
  | succ k ih =>
    simp only [sumRat]
    obtain ⟨i0, hi0⟩ := hlt
    by_cases hlast : i0.val = k
    · have heq : i0 = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      rw [heq] at hi0
      exact rat_add_lt_add_of_le_of_lt
        (sumRat_le_sumRat (fun i => hle i.castSucc)) hi0
    · have hlt_k : i0.val < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i0.isLt) hlast
      have hrec : sumRat (fun i : Fin k => f i.castSucc) < sumRat (fun i : Fin k => g i.castSucc) :=
        ih (fun i => hle i.castSucc) ⟨⟨i0.val, hlt_k⟩, by
          have : (⟨i0.val, hlt_k⟩ : Fin k).castSucc = i0 := Fin.ext rfl
          rw [this]; exact hi0⟩
      exact rat_add_lt_add_of_lt_of_le hrec (hle ⟨k, Nat.lt_succ_self k⟩)

theorem sumRat_sq_le_sq_sumRat {n : Nat} (f : Fin n → Rat) (hf : ∀ i, 0 ≤ f i) :
    sumRat (fun i => f i * f i) ≤ sumRat f * sumRat f := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    let S := sumRat (fun i : Fin k => f i.castSucc)
    let a := f ⟨k, Nat.lt_succ_self k⟩
    have hS : 0 ≤ S := sumRat_nonneg (fun i => hf i.castSucc)
    have ha : 0 ≤ a := hf ⟨k, Nat.lt_succ_self k⟩
    have hrec : sumRat (fun i : Fin k => f i.castSucc * f i.castSucc) ≤ S * S :=
      ih (fun i => f i.castSucc) (fun i => hf i.castSucc)
    have h2 : 0 ≤ 2 * (S * a) := rat_mul_nonneg (by decide) (rat_mul_nonneg hS ha)
    have hstep : sumRat (fun i : Fin k => f i.castSucc * f i.castSucc) + a * a ≤ S * S + a * a :=
      Rat.add_le_add_right.mpr hrec
    have hstep2 : S * S + a * a ≤ (S + a) * (S + a) := by
      apply rat_le_of_sub_nonneg
      have heq : (S + a) * (S + a) - (S * S + a * a) = 2 * (S * a) := by grind
      rw [heq]
      exact h2
    exact Rat.le_trans hstep hstep2

/-- Sum of a function that equals `v0` at index `i0` and `v1` elsewhere. -/
theorem sumRat_ite_eq {n : Nat} (i0 : Fin n) (v0 v1 : Rat) :
    sumRat (fun i : Fin n => if i = i0 then v0 else v1) = v0 + (((n : Rat) - 1) * v1) := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ k ih =>
    simp only [sumRat]
    by_cases hlast : i0.val = k
    · have hi0 : i0 = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      subst hi0
      have h1 : sumRat (fun i : Fin k =>
          if i.castSucc = (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) then v0 else v1) =
          sumRat (fun _ : Fin k => v1) := by
        apply sumRat_congr
        intro i
        have hne : i.castSucc ≠ (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
          intro h
          have hv : i.val = k := congrArg Fin.val h
          exact Nat.ne_of_lt i.isLt hv
        simp [hne]
      rw [h1, sumRat_const]
      simp only [ite_true]
      have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
      rw [hcast]
      grind
    · have hlt : i0.val < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i0.isLt) hlast
      let j0 : Fin k := ⟨i0.val, hlt⟩
      have hj0 : j0.castSucc = i0 := Fin.ext rfl
      have hne_last : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ i0 := by
        intro h
        exact hlast (congrArg Fin.val h).symm
      have h1 : sumRat (fun i : Fin k => if i.castSucc = i0 then v0 else v1) =
          sumRat (fun i : Fin k => if i = j0 then v0 else v1) := by
        apply sumRat_congr
        intro i
        by_cases hi : i = j0
        · subst hi
          simp only [hj0, ite_true]
        · have hcast_ne : i.castSucc ≠ i0 := by
            intro hc
            apply hi
            apply Fin.ext
            have hv : i.castSucc.val = i0.val := congrArg Fin.val hc
            exact hv
          simp only [hcast_ne, hi, ite_false]
      rw [h1, ih j0]
      simp only [hne_last, ite_false]
      have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
      rw [hcast]
      grind

/-- Sum of a function that equals `v0` at index `0` and `v1` at indices `> 0`, for `1 ≤ n`. -/
theorem sumRat_zero_override {n : Nat} (hn : 1 ≤ n) (v0 v1 : Rat) :
    sumRat (fun i : Fin n => if i.val = 0 then v0 else v1) = v0 + (((n : Rat) - 1) * v1) := by
  let i0 : Fin n := ⟨0, hn⟩
  have h1 : sumRat (fun i : Fin n => if i.val = 0 then v0 else v1) =
      sumRat (fun i : Fin n => if i = i0 then v0 else v1) := by
    apply sumRat_congr
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [i0, ite_true]
    · have hv : i.val ≠ 0 := by
        intro h
        exact hi (Fin.ext h)
      simp only [hv, hi, ite_false]
  rw [h1, sumRat_ite_eq i0 v0 v1]

/-- Lower bound a sum by extracting a distinguished index `i0` with value `≥ a0`
    and bounding all other indices by `≥ a1`. -/
theorem sumRat_ge_of_point_and_rest {n : Nat} (f : Fin n → Rat) (i0 : Fin n) (a0 a1 : Rat)
    (h0 : a0 ≤ f i0) (hrest : ∀ i, i ≠ i0 → a1 ≤ f i) :
    a0 + (((n : Rat) - 1) * a1) ≤ sumRat f := by
  rw [← sumRat_ite_eq i0 a0 a1]
  apply sumRat_le_sumRat
  intro i
  by_cases hi : i = i0
  · subst hi; simp [h0]
  · simp [hi, hrest i hi]

end BitnetContraction
