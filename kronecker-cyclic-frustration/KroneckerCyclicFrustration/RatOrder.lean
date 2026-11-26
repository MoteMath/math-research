/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KroneckerCyclicFrustration.Defs

/-!
# Pure-`Init` `Rat` Order, Field, Power, and Finite Product Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace KroneckerCyclicFrustration

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

theorem rat_mul_le_mul {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d)
    (hc : (0 : Rat) ≤ c) (hb : (0 : Rat) ≤ b) : a * c ≤ b * d :=
  Rat.le_trans (rat_mul_le_mul_of_nonneg_right hab hc) (rat_mul_le_mul_of_nonneg_left hcd hb)

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

theorem rat_div_one (a : Rat) : a / 1 = a := by
  have h := rat_div_mul_cancel (a := a) (b := 1) (by decide)
  rw [Rat.mul_one] at h
  exact h

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

theorem rat_div_mul_div {a b c d : Rat} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a / b) * (c / d) = (a * c) / (b * d) := by
  have hbd : b * d ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hb h
    | inr h => exact hd h
  have h1 : ((a / b) * (c / d)) * (b * d) = a * c := by
    have eq1 : ((a / b) * (c / d)) * (b * d) = ((a / b) * b) * ((c / d) * d) := by grind
    rw [eq1, rat_div_mul_cancel hb, rat_div_mul_cancel hd]
  have h2 : ((a * c) / (b * d)) * (b * d) = a * c := rat_div_mul_cancel hbd
  have hmul : ((a / b) * (c / d) - (a * c) / (b * d)) * (b * d) = 0 := by grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h0 => grind
  | inr h0 => exact False.elim (hbd h0)

theorem rat_div_div_eq {a b c d : Rat} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (a / b) / (c / d) = (a * d) / (b * c) := by
  have hcd : c / d ≠ 0 := by
    intro h0
    have : c = 0 := by
      have := rat_div_mul_cancel (a := c) hd
      rw [h0, Rat.zero_mul] at this
      exact this.symm
    exact hc this
  have hbc : b * c ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hb h
    | inr h => exact hc h
  apply rat_div_eq_of_cross hcd hbc
  have eq1 : (a / b) * (b * c) = ((a / b) * b) * c := by grind
  have eq2 : (a * d) * (c / d) = a * ((c / d) * d) := by grind
  rw [eq1, rat_div_mul_cancel hb, eq2, rat_div_mul_cancel hd]

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

/-! ## `ratPow` and `finProdRat` Helpers -/

theorem ratPow_pos {x : Rat} (hx : (0 : Rat) < x) : ∀ n : Nat, (0 : Rat) < ratPow x n
  | 0 => by simp only [ratPow]; decide
  | n + 1 => rat_mul_pos (ratPow_pos hx n) hx

theorem ratPow_nonneg {x : Rat} (hx : (0 : Rat) ≤ x) : ∀ n : Nat, (0 : Rat) ≤ ratPow x n
  | 0 => by simp only [ratPow]; decide
  | n + 1 => Rat.mul_nonneg (ratPow_nonneg hx n) hx

theorem ratPow_ne_zero {x : Rat} (hx : (0 : Rat) < x) (n : Nat) : ratPow x n ≠ 0 :=
  Rat.ne_of_gt (ratPow_pos hx n)

theorem ratPow_add (x : Rat) (a : Nat) : ∀ b : Nat, ratPow x (a + b) = ratPow x a * ratPow x b
  | 0 => by simp [ratPow]
  | b + 1 => by
    rw [Nat.add_succ, ratPow, ratPow, ratPow_add x a b, Rat.mul_assoc]

theorem ratPow_mul (x : Rat) (a : Nat) : ∀ b : Nat, ratPow x (a * b) = ratPow (ratPow x a) b
  | 0 => by simp [ratPow]
  | b + 1 => by
    rw [Nat.mul_succ, ratPow_add, ratPow, ratPow_mul x a b]

theorem ratPow_mono_exp {x : Rat} (hx : (1 : Rat) ≤ x) :
    ∀ {a b : Nat}, a ≤ b → ratPow x a ≤ ratPow x b := by
  intro a b hab
  have hdiff : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
  rw [hdiff, ratPow_add]
  have hx0 : (0 : Rat) ≤ x := Rat.le_trans (by decide) hx
  have h1 : ∀ k : Nat, (1 : Rat) ≤ ratPow x k := by
    intro k
    induction k with
    | zero => exact Rat.le_refl
    | succ k ih =>
      rw [ratPow]
      have := rat_mul_le_mul ih hx (by decide) (Rat.le_trans (by decide) ih)
      rw [Rat.one_mul] at this
      exact this
  have hmul := rat_mul_le_mul_of_nonneg_left (h1 (b - a)) (ratPow_nonneg hx0 a)
  rw [Rat.mul_one] at hmul
  exact hmul

theorem finProdRat_nonneg : ∀ {n : Nat} (f : Fin n → Rat),
    (∀ i, (0 : Rat) ≤ f i) → (0 : Rat) ≤ finProdRat f
  | 0, _, _ => by simp only [finProdRat]; decide
  | _ + 1, f, hf =>
    Rat.mul_nonneg (finProdRat_nonneg (fun i => f i.castSucc) (fun i => hf i.castSucc)) (hf _)

theorem finProdRat_pos : ∀ {n : Nat} (f : Fin n → Rat),
    (∀ i, (0 : Rat) < f i) → (0 : Rat) < finProdRat f
  | 0, _, _ => by simp only [finProdRat]; decide
  | _ + 1, f, hf =>
    rat_mul_pos (finProdRat_pos (fun i => f i.castSucc) (fun i => hf i.castSucc)) (hf _)

theorem finProdRat_congr : ∀ {n : Nat} {f g : Fin n → Rat},
    (∀ i, f i = g i) → finProdRat f = finProdRat g
  | 0, _, _, _ => rfl
  | _ + 1, f, g, h => by
    simp only [finProdRat]
    rw [finProdRat_congr (fun i => h i.castSucc), h]

theorem finProdRat_const : ∀ (n : Nat) (c : Rat), finProdRat (fun _ : Fin n => c) = ratPow c n
  | 0, _ => rfl
  | n + 1, c => by
    simp only [finProdRat, ratPow]
    rw [finProdRat_const n c]

theorem finProdRat_mul : ∀ {n : Nat} (f g : Fin n → Rat),
    finProdRat (fun i => f i * g i) = finProdRat f * finProdRat g
  | 0, _, _ => by simp [finProdRat]
  | _ + 1, f, g => by
    simp only [finProdRat]
    rw [finProdRat_mul (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem finProdRat_div : ∀ {n : Nat} (f g : Fin n → Rat),
    (∀ i, g i ≠ 0) →
    finProdRat (fun i => f i / g i) = finProdRat f / finProdRat g
  | 0, _, _, _ => by simp only [finProdRat, rat_div_one]
  | _ + 1, f, g, hg => by
    simp only [finProdRat]
    rw [finProdRat_div (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => hg i.castSucc)]
    have hprod_ne : finProdRat (fun i => g i.castSucc) ≠ 0 := by
      have hne : ∀ {m : Nat} (u : Fin m → Rat), (∀ i, u i ≠ 0) → finProdRat u ≠ 0 := by
        intro m
        induction m with
        | zero => intro _ _; simp only [finProdRat]; decide
        | succ m ih =>
          intro u hu
          simp only [finProdRat]
          intro h0
          cases Rat.mul_eq_zero.mp h0 with
          | inl h1 => exact ih (fun i => u i.castSucc) (fun i => hu i.castSucc) h1
          | inr h2 => exact hu _ h2
      exact hne _ (fun i => hg i.castSucc)
    exact rat_div_mul_div hprod_ne (hg _)

theorem finProdRat_le_finProdRat : ∀ {n : Nat} (f g : Fin n → Rat),
    (∀ i, (0 : Rat) ≤ f i) → (∀ i, f i ≤ g i) →
    finProdRat f ≤ finProdRat g
  | 0, _, _, _, _ => Rat.le_refl
  | _ + 1, f, g, hf, hfg => by
    simp only [finProdRat]
    have h1 := finProdRat_le_finProdRat (fun i => f i.castSucc) (fun i => g i.castSucc)
      (fun i => hf i.castSucc) (fun i => hfg i.castSucc)
    have h2 := hfg ⟨_, Nat.lt_succ_self _⟩
    have h0g : (0 : Rat) ≤ finProdRat (fun i => g i.castSucc) :=
      finProdRat_nonneg _ (fun i => Rat.le_trans (hf i.castSucc) (hfg i.castSucc))
    exact rat_mul_le_mul h1 h2 (hf _) h0g

/-- Cyclic shift invariance of `finProdRat`: `∏_{t : Fin L} f ((t + 1) mod L) = ∏_{t : Fin L} f t`. -/
theorem finProdRat_shift {L : Nat} (hL : 0 < L) (f : Fin L → Rat) :
    finProdRat (fun t : Fin L => f (finNext hL t)) = finProdRat f := by
  cases L with
  | zero => exact False.elim (Nat.lt_irrefl 0 hL)
  | succ m =>
    -- Prove by induction on `k ≤ m` that prefix product of shifted equals prefix product * f(k) / f(0),
    -- or directly prove for any `k ≤ m`:
    -- `finProdRat (fun i : Fin (k + 1) => f ⟨i.val + 1, _⟩)` * f ⟨0, _⟩ =
    -- `finProdRat (fun i : Fin (k + 1) => f ⟨i.val, _⟩)` * f ⟨k + 1, _⟩`
    -- Wait: let's do an even simpler auxiliary identity on `k ≤ m`!
    have aux : ∀ (k : Nat) (hk : k ≤ m),
        f ⟨0, Nat.succ_pos m⟩ * finProdRat (fun i : Fin k => f ⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.succ_lt_succ i.isLt) (Nat.succ_le_succ hk)⟩) =
        finProdRat (fun i : Fin k => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ_of_le hk)⟩) * f ⟨k, Nat.lt_succ_of_le hk⟩ := by
      intro k
      induction k with
      | zero =>
        intro _
        simp [finProdRat, Rat.mul_one, Rat.one_mul]
      | succ k ih =>
        intro hk
        have hk' : k ≤ m := Nat.le_of_succ_le hk
        simp only [finProdRat, Fin.val_castSucc]
        rw [← Rat.mul_assoc, ih hk']
    -- Now unfold the top step of `finProdRat` on `m + 1`:
    -- Last term `t = m` has `finNext hL ⟨m, _⟩ = ⟨0, _⟩`.
    -- Earlier terms `i : Fin m` have `finNext hL i.castSucc = ⟨i.val + 1, _⟩`.
    simp only [finProdRat]
    have hlast : finNext (Nat.succ_pos m) ⟨m, Nat.lt_succ_self m⟩ = ⟨0, Nat.succ_pos m⟩ := by
      apply Fin.ext
      simp [finNext, Nat.mod_self]
    have hearly : (fun i : Fin m => f (finNext (Nat.succ_pos m) i.castSucc)) =
        (fun i : Fin m => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) := by
      funext i
      congr 1
      apply Fin.ext
      simp [finNext, Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)]
    rw [hlast, hearly, Rat.mul_comm]
    exact aux m (Nat.le_refl m)

end KroneckerCyclicFrustration
