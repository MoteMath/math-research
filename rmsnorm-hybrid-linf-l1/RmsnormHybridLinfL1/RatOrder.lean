/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RmsnormHybridLinfL1.Defs

/-!
# Pure-`Init` `Rat` Order, Field, and Finite-Sum Helpers

Zero Mathlib, zero `native_decide`. Provides elementary `Rat` order/field lemmas,
`ratAbs`/`ratMax` properties, and `finSum` / Cauchy-Schwarz inequalities over `Fin d → Rat`.
-/

namespace RmsnormHybridLinfL1

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

theorem rat_add_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a + b :=
  rat_add_pos_of_pos_of_nonneg ha (Rat.le_of_lt hb)

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

theorem rat_sq_pos_of_ne_zero {x : Rat} (hx : x ≠ 0) : (0 : Rat) < x * x := by
  have hle : (0 : Rat) ≤ x * x := rat_sq_nonneg x
  have hne : x * x ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hx h
    | inr h => exact hx h
  exact Rat.lt_of_le_of_ne hle (Ne.symm hne)

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

theorem rat_div_lt_of_mul_lt {a b c : Rat} (hc : (0 : Rat) < c) (h : a < b * c) :
    a / c < b := by
  apply rat_lt_of_mul_pos_right hc
  rw [rat_div_mul_cancel (Rat.ne_of_gt hc)]
  exact h

theorem rat_lt_div_of_mul_lt {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c < b) :
    a < b / c := by
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

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  rat_lt_of_lt_of_le h1 (Rat.le_of_lt h2)

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

theorem pow2Rat_pos (k : Nat) : (0 : Rat) < pow2Rat k := by
  unfold pow2Rat
  exact rat_natCast_pos (Nat.pow_pos (by decide))

theorem invPow2Rat_pos (k : Nat) : (0 : Rat) < invPow2Rat k :=
  rat_div_pos (by decide) (pow2Rat_pos k)

theorem pow2Int_pos (e : Int) : (0 : Rat) < pow2Int e := by
  unfold pow2Int
  split
  · exact pow2Rat_pos _
  · exact invPow2Rat_pos _

/-! ## `ratAbs` and `ratMax` properties -/

theorem ratAbs_nonneg (q : Rat) : (0 : Rat) ≤ ratAbs q := by
  unfold ratAbs
  split
  · rename_i h
    have := rat_sub_pos h
    grind
  · rename_i h
    exact Rat.not_lt.mp h

theorem ratAbs_sq (q : Rat) : ratAbs q * ratAbs q = q * q := by
  unfold ratAbs
  split <;> grind

theorem ratAbs_of_nonneg {q : Rat} (h : (0 : Rat) ≤ q) : ratAbs q = q := by
  unfold ratAbs
  split
  · rename_i hlt
    exact False.elim (Rat.not_le.mpr hlt h)
  · rfl

theorem ratMax_le_left (a b : Rat) : a ≤ ratMax a b := by
  unfold ratMax
  split
  · assumption
  · exact Rat.le_refl

theorem ratMax_le_right (a b : Rat) : b ≤ ratMax a b := by
  unfold ratMax
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem ratMax_le_iff {a b c : Rat} : ratMax a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  unfold ratMax
  split
  · rename_i hab
    constructor
    · intro hbc; exact ⟨Rat.le_trans hab hbc, hbc⟩
    · intro ⟨_, hbc⟩; exact hbc
  · rename_i hnab
    have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp hnab)
    constructor
    · intro hac; exact ⟨hac, Rat.le_trans hba hac⟩
    · intro ⟨hac, _⟩; exact hac

theorem ratMax_eq_or (a b : Rat) : ratMax a b = a ∨ ratMax a b = b := by
  unfold ratMax
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## `finSum` algebraic and order properties -/

theorem finSum_congr {d : Nat} {f g : Fin d → Rat} (h : ∀ i, f i = g i) :
    finSum d f = finSum d g := by
  induction d with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => h i.castSucc), h ⟨n, Nat.lt_succ_self n⟩]

theorem finSum_nonneg {d : Nat} {f : Fin d → Rat} (h : ∀ i, (0 : Rat) ≤ f i) :
    (0 : Rat) ≤ finSum d f := by
  induction d with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [finSum]
    exact rat_add_nonneg (ih (fun i => h i.castSucc)) (h ⟨n, Nat.lt_succ_self n⟩)

theorem finSum_le_finSum {d : Nat} {f g : Fin d → Rat} (h : ∀ i, f i ≤ g i) :
    finSum d f ≤ finSum d g := by
  induction d with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [finSum]
    exact rat_add_le_add (ih (fun i => h i.castSucc)) (h ⟨n, Nat.lt_succ_self n⟩)

theorem finSum_add {d : Nat} (f g : Fin d → Rat) :
    finSum d (fun i => f i + g i) = finSum d f + finSum d g := by
  induction d with
  | zero => simp [finSum]; grind
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem finSum_sub {d : Nat} (f g : Fin d → Rat) :
    finSum d (fun i => f i - g i) = finSum d f - finSum d g := by
  induction d with
  | zero => simp [finSum]; grind
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem finSum_mul_left {d : Nat} (c : Rat) (f : Fin d → Rat) :
    finSum d (fun i => c * f i) = c * finSum d f := by
  induction d with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem finSum_const {d : Nat} (c : Rat) :
    finSum d (fun _ => c) = (d : Rat) * c := by
  induction d with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    rw [ih, Rat.natCast_add]
    grind

/-- Split out a single index `i0 : Fin d` from `finSum d f` by zeroing it out. -/
theorem finSum_split_at {d : Nat} (f : Fin d → Rat) (i0 : Fin d) :
    finSum d f = f i0 + finSum d (fun i => if i = i0 then 0 else f i) := by
  induction d with
  | zero => exact Fin.elim0 i0
  | succ n ih =>
    simp only [finSum]
    by_cases hlast : i0 = ⟨n, Nat.lt_succ_self n⟩
    · subst hlast
      have hcongr :
          finSum n (fun i => if i.castSucc = ⟨n, Nat.lt_succ_self n⟩ then 0 else f i.castSucc) =
          finSum n (fun i => f i.castSucc) := by
        apply finSum_congr
        intro i
        have hne : i.castSucc ≠ ⟨n, Nat.lt_succ_self n⟩ := by
          intro heq
          have hv : i.val = n := congrArg Fin.val heq
          omega
        simp [hne]
      rw [hcongr]
      simp
      grind
    · have hlt : i0.val < n := by
        have hle := i0.isLt
        have hne : i0.val ≠ n := by
          intro hv
          apply hlast
          exact Fin.ext hv
        omega
      let j0 : Fin n := ⟨i0.val, hlt⟩
      have hj0 : j0.castSucc = i0 := Fin.ext rfl
      have hih := ih (fun i => f i.castSucc) j0
      have hcongr :
          finSum n (fun i => if i = j0 then 0 else f i.castSucc) =
          finSum n (fun i => if i.castSucc = i0 then 0 else f i.castSucc) := by
        apply finSum_congr
        intro i
        have hiff : (i = j0) ↔ (i.castSucc = i0) := by
          constructor
          · intro h; subst h; exact hj0
          · intro h
            apply Fin.ext
            have hv : i.castSucc.val = i0.val := congrArg Fin.val h
            exact hv
        by_cases h : i = j0
        · simp [h, hj0]
        · simp [h, mt hiff.mpr h]
      have hneLast : ¬ (⟨n, Nat.lt_succ_self n⟩ = i0) := fun h => hlast h.symm
      rw [hih, hcongr, hj0]
      simp [hneLast]
      grind

/-- Cauchy-Schwarz inequality over `Fin n → Rat`: `(∑ f i)^2 ≤ n * ∑ (f i)^2`. -/
theorem finSum_sq_le_mul_sumSq {n : Nat} (f : Fin n → Rat) :
    finSum n f * finSum n f ≤ (n : Rat) * finSum n (fun i => f i * f i) := by
  induction n with
  | zero =>
    simp [finSum]
  | succ k ih =>
    simp only [finSum]
    let S := finSum k (fun i => f i.castSucc)
    let Q := finSum k (fun i => f i.castSucc * f i.castSucc)
    let y := f ⟨k, Nat.lt_succ_self k⟩
    change (S + y) * (S + y) ≤ ((k + 1 : Nat) : Rat) * (Q + y * y)
    have hih : S * S ≤ (k : Rat) * Q := ih (fun i => f i.castSucc)
    cases k with
    | zero =>
      have hS : S = 0 := rfl
      have hQ : Q = 0 := rfl
      rw [hS, hQ]
      have h1 : ((0 + 1 : Nat) : Rat) = 1 := by decide
      rw [h1]
      have heq : (0 + y) * (0 + y) = 1 * (0 + y * y) := by grind
      rw [heq]
      exact Rat.le_refl
    | succ m =>
      have hkpos : (0 : Rat) < ((m + 1 : Nat) : Rat) := rat_natCast_pos (Nat.succ_pos m)
      apply rat_le_of_mul_pos_right hkpos
      apply rat_le_of_sub_nonneg
      have hdiff : (0 : Rat) ≤ ((m + 1 : Nat) : Rat) * Q - S * S := rat_sub_nonneg hih
      have hsq : (0 : Rat) ≤ (S - ((m + 1 : Nat) : Rat) * y) * (S - ((m + 1 : Nat) : Rat) * y) :=
        rat_sq_nonneg _
      have hcast : ((m + 1 + 1 : Nat) : Rat) = ((m + 1 : Nat) : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      have hident :
          ((m + 1 + 1 : Nat) : Rat) * (Q + y * y) * ((m + 1 : Nat) : Rat) -
            (S + y) * (S + y) * ((m + 1 : Nat) : Rat) =
          (((m + 1 : Nat) : Rat) + 1) * (((m + 1 : Nat) : Rat) * Q - S * S) +
            (S - ((m + 1 : Nat) : Rat) * y) * (S - ((m + 1 : Nat) : Rat) * y) := by
        rw [hcast]
        grind
      rw [hident]
      have hk1pos : (0 : Rat) ≤ ((m + 1 : Nat) : Rat) + 1 :=
        rat_add_nonneg (Rat.le_of_lt hkpos) (by decide)
      exact rat_add_nonneg (Rat.mul_nonneg hk1pos hdiff) hsq

/-- Cauchy-Schwarz on the `d - 1` entries excluding a chosen index `i0 : Fin d`. -/
theorem finSum_excl_sq_le {d : Nat} (f : Fin d → Rat) (i0 : Fin d) :
    let g := fun i => if i = i0 then 0 else f i
    finSum d g * finSum d g ≤ ((d - 1 : Nat) : Rat) * finSum d (fun i => g i * g i) := by
  induction d with
  | zero => exact Fin.elim0 i0
  | succ n ih =>
    intro g
    by_cases hlast : i0 = ⟨n, Nat.lt_succ_self n⟩
    · subst hlast
      have h1 : finSum (n + 1) g = finSum n (fun i => f i.castSucc) := by
        simp only [finSum, g]
        have hcongr :
            finSum n (fun i => if i.castSucc = ⟨n, Nat.lt_succ_self n⟩ then 0 else f i.castSucc) =
            finSum n (fun i => f i.castSucc) := by
          apply finSum_congr
          intro i
          have hne : i.castSucc ≠ ⟨n, Nat.lt_succ_self n⟩ := by
            intro heq
            have hv : i.val = n := congrArg Fin.val heq
            omega
          simp [hne]
        rw [hcongr]
        simp [Rat.add_zero]
      have h2 : finSum (n + 1) (fun i => g i * g i) =
          finSum n (fun i => f i.castSucc * f i.castSucc) := by
        simp only [finSum, g]
        have hcongr :
            finSum n (fun i => (if i.castSucc = ⟨n, Nat.lt_succ_self n⟩ then 0 else f i.castSucc) *
              (if i.castSucc = ⟨n, Nat.lt_succ_self n⟩ then 0 else f i.castSucc)) =
            finSum n (fun i => f i.castSucc * f i.castSucc) := by
          apply finSum_congr
          intro i
          have hne : i.castSucc ≠ ⟨n, Nat.lt_succ_self n⟩ := by
            intro heq
            have hv : i.val = n := congrArg Fin.val heq
            omega
          simp [hne]
        rw [hcongr]
        simp [Rat.mul_zero, Rat.add_zero]
      rw [h1, h2]
      exact finSum_sq_le_mul_sumSq (fun i => f i.castSucc)
    · have hlt : i0.val < n := by
        have hle := i0.isLt
        have hne : i0.val ≠ n := by
          intro hv; apply hlast; exact Fin.ext hv
        omega
      let j0 : Fin n := ⟨i0.val, hlt⟩
      have hj0 : j0.castSucc = i0 := Fin.ext rfl
      have hih := ih (fun i => f i.castSucc) j0
      dsimp only at hih
      let g' : Fin n → Rat := fun i => if i = j0 then 0 else f i.castSucc
      let S := finSum n g'
      let Q := finSum n (fun i => g' i * g' i)
      let y := f ⟨n, Nat.lt_succ_self n⟩
      have hneLast : ¬ (⟨n, Nat.lt_succ_self n⟩ = i0) := fun h => hlast h.symm
      have h1 : finSum (n + 1) g = S + y := by
        simp only [finSum, g, hneLast, ite_false]
        have hcongr :
            finSum n (fun i => if i.castSucc = i0 then 0 else f i.castSucc) = S := by
          apply finSum_congr
          intro i
          have hiff : (i.castSucc = i0) ↔ (i = j0) := by
            constructor
            · intro h; apply Fin.ext; have hv : i.castSucc.val = i0.val := congrArg Fin.val h; exact hv
            · intro h; subst h; exact hj0
          by_cases h : i = j0
          · simp [g', h, hj0]
          · simp [g', h, mt hiff.mp h]
        rw [hcongr]
      have h2 : finSum (n + 1) (fun i => g i * g i) = Q + y * y := by
        simp only [finSum, g, hneLast, ite_false]
        have hcongr :
            finSum n (fun i => (if i.castSucc = i0 then 0 else f i.castSucc) *
              (if i.castSucc = i0 then 0 else f i.castSucc)) = Q := by
          apply finSum_congr
          intro i
          have hiff : (i.castSucc = i0) ↔ (i = j0) := by
            constructor
            · intro h; apply Fin.ext; have hv : i.castSucc.val = i0.val := congrArg Fin.val h; exact hv
            · intro h; subst h; exact hj0
          by_cases h : i = j0
          · simp [g', h, hj0]
          · simp [g', h, mt hiff.mp h]
        rw [hcongr]
      rw [h1, h2]
      cases n with
      | zero => omega
      | succ m =>
        cases m with
        | zero =>
          have hS0 : S = 0 := by
            simp only [S, finSum, g']
            have hj00 : (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = j0 := Fin.ext (by omega)
            simp [hj00]; grind
          have hQ0 : Q = 0 := by
            simp only [Q, finSum, g']
            have hj00 : (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = j0 := Fin.ext (by omega)
            simp [hj00]; grind
          rw [hS0, hQ0]
          have h1' : ((1 + 1 - 1 : Nat) : Rat) = 1 := by decide
          rw [h1']
          have heq : (0 + y) * (0 + y) = 1 * (0 + y * y) := by grind
          rw [heq]
          exact Rat.le_refl
        | succ k =>
          have hkpos : (0 : Rat) < ((k + 1 : Nat) : Rat) := rat_natCast_pos (Nat.succ_pos k)
          apply rat_le_of_mul_pos_right hkpos
          apply rat_le_of_sub_nonneg
          have hdiff : (0 : Rat) ≤ ((k + 1 : Nat) : Rat) * Q - S * S := rat_sub_nonneg hih
          have hsq : (0 : Rat) ≤ (S - ((k + 1 : Nat) : Rat) * y) * (S - ((k + 1 : Nat) : Rat) * y) :=
            rat_sq_nonneg _
          have hcast : ((k + 1 + 1 + 1 - 1 : Nat) : Rat) = ((k + 1 : Nat) : Rat) + 1 := by
            have hnat : k + 1 + 1 + 1 - 1 = (k + 1) + 1 := by omega
            rw [hnat, Rat.natCast_add]; rfl
          have hident :
              ((k + 1 + 1 + 1 - 1 : Nat) : Rat) * (Q + y * y) * ((k + 1 : Nat) : Rat) -
                (S + y) * (S + y) * ((k + 1 : Nat) : Rat) =
              (((k + 1 : Nat) : Rat) + 1) * (((k + 1 : Nat) : Rat) * Q - S * S) +
                (S - ((k + 1 : Nat) : Rat) * y) * (S - ((k + 1 : Nat) : Rat) * y) := by
            rw [hcast]
            grind
          rw [hident]
          have hk1pos : (0 : Rat) ≤ ((k + 1 : Nat) : Rat) + 1 :=
            rat_add_nonneg (Rat.le_of_lt hkpos) (by decide)
          exact rat_add_nonneg (Rat.mul_nonneg hk1pos hdiff) hsq

/-! ## `linfNorm` properties -/

theorem linfNorm_nonneg {d : Nat} (x : Fin d → Rat) : (0 : Rat) ≤ linfNorm x := by
  induction d with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [linfNorm]
    exact Rat.le_trans (ih (fun i => x i.castSucc)) (ratMax_le_left _ _)

theorem ratAbs_le_linfNorm {d : Nat} (x : Fin d → Rat) (i : Fin d) :
    ratAbs (x i) ≤ linfNorm x := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [linfNorm]
    by_cases hlast : i = ⟨n, Nat.lt_succ_self n⟩
    · subst hlast
      exact ratMax_le_right _ _
    · have hlt : i.val < n := by
        have hle := i.isLt
        have hne : i.val ≠ n := fun hv => hlast (Fin.ext hv)
        omega
      let j : Fin n := ⟨i.val, hlt⟩
      have hj : j.castSucc = i := Fin.ext rfl
      rw [← hj]
      exact Rat.le_trans (ih (fun k => x k.castSucc) j) (ratMax_le_left _ _)

theorem exists_eq_linfNorm {d : Nat} (hd : 1 ≤ d) (x : Fin d → Rat) :
    ∃ i : Fin d, ratAbs (x i) = linfNorm x := by
  induction d with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      refine ⟨⟨0, Nat.lt_succ_self 0⟩, ?_⟩
      change ratAbs (x ⟨0, Nat.lt_succ_self 0⟩) = ratMax 0 (ratAbs (x ⟨0, Nat.lt_succ_self 0⟩))
      unfold ratMax
      split
      · rfl
      · rename_i h; exact False.elim (h (ratAbs_nonneg _))
    | succ m =>
      have hdef : linfNorm x =
          ratMax (linfNorm (fun i => x i.castSucc)) (ratAbs (x ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) :=
        rfl
      rw [hdef]
      cases ratMax_eq_or (linfNorm (fun i => x i.castSucc)) (ratAbs (x ⟨m + 1, Nat.lt_succ_self (m + 1)⟩)) with
      | inl h =>
        rw [h]
        obtain ⟨j, hj⟩ := ih (Nat.succ_pos m) (fun i => x i.castSucc)
        exact ⟨j.castSucc, hj⟩
      | inr h =>
        rw [h]
        exact ⟨⟨m + 1, Nat.lt_succ_self (m + 1)⟩, rfl⟩

end RmsnormHybridLinfL1
