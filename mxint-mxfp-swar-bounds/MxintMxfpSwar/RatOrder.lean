/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxintMxfpSwar.Defs

/-!
# Pure-`Init` `Rat` Order, `Fin n` Sum, and `Int` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace MxintMxfpSwar

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

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  apply rat_lt_of_sub_pos
  have h1 : (0 : Rat) < b - a := rat_sub_pos h
  have h2 : (0 : Rat) < c * (b - a) := rat_mul_pos hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]; exact h2

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
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos h
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

theorem rat_div_mul_cancel {a b : Rat} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.mul_one]

theorem rat_div_le_div_iff {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_mul_pos hb hd))
    have hl : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hr : (c / d) * (b * d) = c * b := by
      have : (c / d) * (b * d) = ((c / d) * d) * b := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hl, hr] at h1
    exact h1
  · intro h
    apply rat_le_of_mul_pos_right (rat_mul_pos hb hd)
    have hl : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hr : (c / d) * (b * d) = c * b := by
      have : (c / d) * (b * d) = ((c / d) * d) * b := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hl, hr]
    exact h

theorem rat_div_lt_div_iff {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d) :
    a / b < c / d ↔ a * d < c * b := by
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h (rat_mul_pos hb hd)
    have hl : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hr : (c / d) * (b * d) = c * b := by
      have : (c / d) * (b * d) = ((c / d) * d) * b := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hl, hr] at h1
    exact h1
  · intro h
    apply rat_lt_of_mul_pos_right (rat_mul_pos hb hd)
    have hl : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hb)]
    have hr : (c / d) * (b * d) = c * b := by
      have : (c / d) * (b * d) = ((c / d) * d) * b := by grind
      rw [this, rat_div_mul_cancel (Rat.ne_of_gt hd)]
    rw [hl, hr]
    exact h

theorem rat_div_eq_div_iff {a b c d : Rat} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b := by
  constructor
  · intro h
    have h1 : (a / b) * (b * d) = (c / d) * (b * d) := by rw [h]
    have hl : (a / b) * (b * d) = a * d := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel hb]
    have hr : (c / d) * (b * d) = c * b := by
      have : (c / d) * (b * d) = ((c / d) * d) * b := by grind
      rw [this, rat_div_mul_cancel hd]
    rw [hl, hr] at h1
    exact h1
  · intro h
    have hbd : b * d ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h1 => exact hb h1
      | inr h2 => exact hd h2
    have hmul : (a / b) * (b * d) = (c / d) * (b * d) := by
      have hl : (a / b) * (b * d) = a * d := by
        rw [← Rat.mul_assoc, rat_div_mul_cancel hb]
      have hr : (c / d) * (b * d) = c * b := by
        have : (c / d) * (b * d) = ((c / d) * d) * b := by grind
        rw [this, rat_div_mul_cancel hd]
      rw [hl, hr, h]
    have hdiff : ((a / b) - (c / d)) * (b * d) = 0 := by grind
    cases Rat.mul_eq_zero.mp hdiff with
    | inl h0 => grind
    | inr h0 => exact absurd h0 hbd

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

theorem rat_div_lt_of_mul_lt {a b c : Rat} (hc : (0 : Rat) < c) (h : a < b * c) :
    a / c < b := by
  apply rat_lt_of_mul_pos_right hc
  rw [rat_div_mul_cancel (Rat.ne_of_gt hc)]
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

theorem rat_intCast_nonneg {z : Int} (h : 0 ≤ z) : (0 : Rat) ≤ (z : Rat) := by
  have hz : z = (z.toNat : Int) := by omega
  rw [hz, Rat.intCast_natCast]
  exact rat_natCast_nonneg z.toNat

theorem rat_intCast_pos {z : Int} (h : 0 < z) : (0 : Rat) < (z : Rat) := by
  have hz : z = (z.toNat : Int) := by omega
  rw [hz, Rat.intCast_natCast]
  exact rat_natCast_pos (by omega)

theorem rat_intCast_le {a b : Int} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  apply rat_le_of_sub_nonneg
  have hsub : (b : Rat) - (a : Rat) = ((b - a : Int) : Rat) := by
    rw [Rat.intCast_sub]
  rw [hsub]
  exact rat_intCast_nonneg (by omega)

theorem rat_intCast_lt {a b : Int} (h : a < b) : (a : Rat) < (b : Rat) := by
  apply rat_lt_of_sub_pos
  have hsub : (b : Rat) - (a : Rat) = ((b - a : Int) : Rat) := by
    rw [Rat.intCast_sub]
  rw [hsub]
  exact rat_intCast_pos (by omega)

theorem rat_inv_pos {c : Rat} (hc : (0 : Rat) < c) : (0 : Rat) < c⁻¹ := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  have h1 : (0 : Rat) < c⁻¹ * c := by
    rw [Rat.inv_mul_cancel c hne]
    exact rat_natCast_pos (by decide : 0 < 1)
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

theorem rat_div_eq_iff {a b c : Rat} (hb : b ≠ 0) : a / b = c ↔ a = c * b := by
  constructor
  · intro h
    rw [← h, rat_div_mul_cancel hb]
  · intro h
    rw [h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel b hb, Rat.mul_one]

theorem ratAbs_sq (x : Rat) : ratAbs x * ratAbs x = x * x := by
  unfold ratAbs
  split <;> grind

theorem ratMax_le_iff {a b c : Rat} : ratMax a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  unfold ratMax
  split
  · rename_i h
    constructor
    · intro hbc; exact ⟨Rat.le_trans h hbc, hbc⟩
    · intro ⟨_, hbc⟩; exact hbc
  · rename_i h
    have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp h)
    constructor
    · intro hac; exact ⟨hac, Rat.le_trans hba hac⟩
    · intro ⟨hac, _⟩; exact hac

theorem ratMax_lt_iff {a b c : Rat} : ratMax a b < c ↔ a < c ∧ b < c := by
  unfold ratMax
  split
  · rename_i h
    constructor
    · intro hbc; exact ⟨rat_lt_of_le_of_lt h hbc, hbc⟩
    · intro ⟨_, hbc⟩; exact hbc
  · rename_i h
    have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp h)
    constructor
    · intro hac; exact ⟨hac, rat_lt_of_le_of_lt hba hac⟩
    · intro ⟨hac, _⟩; exact hac

theorem le_ratMax_left (a b : Rat) : a ≤ ratMax a b := by
  unfold ratMax
  split
  · assumption
  · exact Rat.le_refl

theorem le_ratMax_right (a b : Rat) : b ≤ ratMax a b := by
  unfold ratMax
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

/-! ### `finSum` Lemmas -/

theorem finSum_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem finSum_add {n : Nat} (f g : Fin n → Rat) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => simp [finSum]; grind
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem finSum_sub {n : Nat} (f g : Fin n → Rat) :
    finSum (fun i => f i - g i) = finSum f - finSum g := by
  induction n with
  | zero => simp [finSum]; grind
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem finSum_const {n : Nat} (c : Rat) :
    finSum (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    rw [ih, Rat.natCast_add]
    grind

theorem finSum_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    finSum (fun i => c * f i) = c * finSum f := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [finSum]
    exact rat_add_le_add (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem finSum_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ i, (0 : Rat) ≤ f i) :
    (0 : Rat) ≤ finSum f := by
  have h0 : finSum (fun _ : Fin n => (0 : Rat)) = 0 := by
    rw [finSum_const, Rat.mul_zero]
  rw [← h0]
  exact finSum_le_finSum h

theorem finSum_single {n : Nat} (i0 : Fin n) (c : Rat) :
    finSum (fun j : Fin n => if j = i0 then c else 0) = c := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ n ih =>
    simp only [finSum]
    by_cases hlast : i0 = Fin.last n
    · subst hlast
      have h1 : finSum (fun i : Fin n => if i.castSucc = Fin.last n then c else 0) = 0 := by
        have hcongr : finSum (fun i : Fin n => if i.castSucc = Fin.last n then c else 0) =
            finSum (fun _ : Fin n => (0 : Rat)) := by
          apply finSum_congr
          intro i
          have hne : i.castSucc ≠ Fin.last n := by
            intro heq
            have hv : i.val = n := by simpa [Fin.val_castSucc, Fin.val_last] using congrArg Fin.val heq
            omega
          simp [hne]
        rw [hcongr, finSum_const, Rat.mul_zero]
      rw [h1]
      simp [Rat.zero_add]
    · have hlt : i0.val < n := by
        have hval : i0.val ≠ n := by
          intro h0; apply hlast; exact Fin.ext (by simpa [Fin.val_last] using h0)
        have := i0.isLt; omega
      let i0' : Fin n := ⟨i0.val, hlt⟩
      have hi0eq : i0 = i0'.castSucc := Fin.ext rfl
      have h1 : finSum (fun i : Fin n => if i.castSucc = i0 then c else 0) = c := by
        have hcongr : finSum (fun i : Fin n => if i.castSucc = i0 then c else 0) =
            finSum (fun i : Fin n => if i = i0' then c else 0) := by
          apply finSum_congr
          intro i
          rw [hi0eq]
          by_cases h : i = i0'
          · subst h; simp
          · have h2 : i.castSucc ≠ i0'.castSucc := by
              intro heq; apply h; exact Fin.ext (by simpa [Fin.val_castSucc] using congrArg Fin.val heq)
            simp [h, h2]
        rw [hcongr]
        exact ih i0'
      have h2 : (if Fin.last n = i0 then c else 0) = 0 := by
        have hne : Fin.last n ≠ i0 := Ne.symm hlast
        simp [hne]
      rw [h1, h2, Rat.add_zero]

theorem finSum_split_at {n : Nat} (i0 : Fin n) (f : Fin n → Rat) :
    finSum f = f i0 + finSumExcept i0 f := by
  unfold finSumExcept
  have hdecomp : finSum f =
      finSum (fun j => (if j = i0 then f i0 else 0) + (if j = i0 then 0 else f j)) := by
    apply finSum_congr
    intro j
    by_cases h : j = i0
    · subst h; simp [Rat.add_zero]
    · simp [h, Rat.zero_add]
  rw [hdecomp, finSum_add, finSum_single]

theorem finSumExcept_const {n : Nat} (i0 : Fin n) (c : Rat) :
    finSumExcept i0 (fun _ => c) = ((n - 1 : Nat) : Rat) * c := by
  have h1 := finSum_split_at i0 (fun _ : Fin n => c)
  rw [finSum_const] at h1
  have hn : 1 ≤ n := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
  have hcast : (n : Rat) = ((n - 1 : Nat) : Rat) + 1 := by
    have : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    conv => lhs; rw [this]
    rw [Rat.natCast_add]
    rfl
  rw [hcast] at h1
  grind

theorem finSumExcept_le {n : Nat} (i0 : Fin n) {f g : Fin n → Rat}
    (h : ∀ j, j ≠ i0 → f j ≤ g j) :
    finSumExcept i0 f ≤ finSumExcept i0 g := by
  unfold finSumExcept
  apply finSum_le_finSum
  intro j
  by_cases hj : j = i0
  · simp [hj]
  · simp [hj]; exact h j hj

theorem finSumExcept_nonneg {n : Nat} (i0 : Fin n) {f : Fin n → Rat}
    (h : ∀ j, j ≠ i0 → (0 : Rat) ≤ f j) :
    (0 : Rat) ≤ finSumExcept i0 f := by
  unfold finSumExcept
  apply finSum_nonneg
  intro j
  by_cases hj : j = i0
  · simp [hj]
  · simp [hj]; exact h j hj

theorem l2NormSq_split_at {n : Nat} (i0 : Fin n) (u : Fin n → Rat) :
    l2NormSq u = u i0 * u i0 + finSumExcept i0 (fun j => u j * u j) :=
  finSum_split_at i0 (fun j => u j * u j)

end MxintMxfpSwar
