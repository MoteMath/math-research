/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxfpDoublelogFtz.Defs

/-!
# Pure-`Init` `Rat` Order, Division, and `Nat` Power Helpers

Zero Mathlib, zero `native_decide`. Elementary order/field lemmas over `Rat` and `Nat`
powers of two used across all six theorems.
-/

namespace MxfpDoublelogFtz

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

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < a⁻¹ := by
  by_cases h : (0 : Rat) < a⁻¹
  · exact h
  · have hle : a⁻¹ ≤ 0 := Rat.not_lt.mp h
    have hneg : (0 : Rat) ≤ -a⁻¹ := by
      have := rat_sub_nonneg hle; grind
    have hmul : (0 : Rat) ≤ a * (-a⁻¹) := Rat.mul_nonneg (Rat.le_of_lt ha) hneg
    have hne : a ≠ 0 := Rat.ne_of_gt ha
    have heq : a * (-a⁻¹) = -1 := by
      have h1 : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hne
      grind
    rw [heq] at hmul
    exact False.elim (Rat.not_le.mpr (by decide : (-1 : Rat) < 0) hmul)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_le_div_iff {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_mul_pos hb hd))
    have hl : a / b * (b * d) = a * d := by
      rw [Rat.div_def]
      have hbi : b⁻¹ * b = 1 := Rat.inv_mul_cancel b hbne
      grind
    have hr : c / d * (b * d) = c * b := by
      rw [Rat.div_def]
      have hdi : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
      grind
    rw [hl, hr] at h1
    exact h1
  · intro h
    have hinv : (0 : Rat) < (b * d)⁻¹ := rat_inv_pos (rat_mul_pos hb hd)
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hinv)
    have hl : a * d * (b * d)⁻¹ = a / b := by
      rw [Rat.div_def]
      have hbd : (b * d) * (b * d)⁻¹ = 1 := Rat.mul_inv_cancel (b * d) (Rat.ne_of_gt (rat_mul_pos hb hd))
      have hbi : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
      have hdi : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
      have hmul : (b * d)⁻¹ = b⁻¹ * d⁻¹ := by
        have : (b * d) * (b⁻¹ * d⁻¹) = 1 := by grind
        grind
      rw [hmul]; grind
    have hr : c * b * (b * d)⁻¹ = c / d := by
      rw [Rat.div_def]
      have hbd : (b * d) * (b * d)⁻¹ = 1 := Rat.mul_inv_cancel (b * d) (Rat.ne_of_gt (rat_mul_pos hb hd))
      have hbi : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
      have hdi : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
      have hmul : (b * d)⁻¹ = b⁻¹ * d⁻¹ := by
        have : (b * d) * (b⁻¹ * d⁻¹) = 1 := by grind
        grind
      rw [hmul]; grind
    rw [hl, hr] at h1
    exact h1

theorem rat_div_lt_div_iff {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d) :
    a / b < c / d ↔ a * d < c * b := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h (rat_mul_pos hb hd)
    have hl : a / b * (b * d) = a * d := by
      rw [Rat.div_def]
      have hbi : b⁻¹ * b = 1 := Rat.inv_mul_cancel b hbne
      grind
    have hr : c / d * (b * d) = c * b := by
      rw [Rat.div_def]
      have hdi : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
      grind
    rw [hl, hr] at h1
    exact h1
  · intro h
    have hinv : (0 : Rat) < (b * d)⁻¹ := rat_inv_pos (rat_mul_pos hb hd)
    have h1 := rat_mul_lt_mul_of_pos_right h hinv
    have hmul : (b * d)⁻¹ = b⁻¹ * d⁻¹ := by
      have hbd : (b * d) * (b * d)⁻¹ = 1 := Rat.mul_inv_cancel (b * d) (Rat.ne_of_gt (rat_mul_pos hb hd))
      have hbi : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
      have hdi : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
      have : (b * d) * (b⁻¹ * d⁻¹) = 1 := by grind
      grind
    have hl : a * d * (b * d)⁻¹ = a / b := by
      rw [Rat.div_def, hmul]
      have hdi : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
      grind
    have hr : c * b * (b * d)⁻¹ = c / d := by
      rw [Rat.div_def, hmul]
      have hbi : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
      grind
    rw [hl, hr] at h1
    exact h1

theorem rat_div_eq_div_iff {a b c d : Rat} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b := by
  constructor
  · intro h
    have hbi : b⁻¹ * b = 1 := Rat.inv_mul_cancel b hb
    have hdi : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hd
    have h' : a * b⁻¹ = c * d⁻¹ := by simpa [Rat.div_def] using h
    have hmul : (a * b⁻¹) * (b * d) = (c * d⁻¹) * (b * d) := congrArg (· * (b * d)) h'
    grind
  · intro h
    have hbi : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hb
    have hdi : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hd
    rw [Rat.div_def, Rat.div_def]
    have hmul : (a * d) * (b⁻¹ * d⁻¹) = (c * b) * (b⁻¹ * d⁻¹) := congrArg (· * (b⁻¹ * d⁻¹)) h
    grind

theorem natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have h1 : (0 : Rat) ≤ (1 : Rat) := by decide
    have eq : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [eq]
    exact rat_add_nonneg ih h1

theorem natCast_inj {m n : Nat} (h : (m : Rat) = (n : Rat)) : m = n := by
  have hnum : ((m : Rat)).num = ((n : Rat)).num := congrArg Rat.num h
  simp [Rat.num_natCast] at hnum
  exact Int.ofNat.inj hnum

theorem natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  have h1 : (0 : Rat) ≤ (n : Rat) := natCast_nonneg n
  have hne : (n : Rat) ≠ 0 := by
    intro h0
    have h0' : (n : Rat) = ((0 : Nat) : Rat) := by simpa using h0
    have : n = 0 := natCast_inj h0'
    omega
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem natCast_le_iff (m n : Nat) : ((m : Rat) ≤ (n : Rat)) ↔ m ≤ n := by
  constructor
  · intro h
    by_cases hle : m ≤ n
    · exact hle
    · exfalso
      have hdiff : 0 < m - n := by omega
      have hpos : (0 : Rat) < ((m - n : Nat) : Rat) := natCast_pos hdiff
      have heq : ((m - n : Nat) : Rat) = (m : Rat) - (n : Rat) := by
        have hadd : (m - n) + n = m := by omega
        have : (((m - n) + n : Nat) : Rat) = (m : Rat) := congrArg (fun x : Nat => (x : Rat)) hadd
        grind
      rw [heq] at hpos
      have hlt : (n : Rat) < (m : Rat) := rat_lt_of_sub_pos hpos
      exact Rat.not_le.mpr hlt h
  · intro h
    have hadd : m + (n - m) = n := by omega
    have heq : (n : Rat) = (m : Rat) + ((n - m : Nat) : Rat) := by
      have : ((m + (n - m) : Nat) : Rat) = (n : Rat) := congrArg (fun x : Nat => (x : Rat)) hadd
      grind
    rw [heq]
    have hnn : (0 : Rat) ≤ ((n - m : Nat) : Rat) := natCast_nonneg (n - m)
    have := (Rat.add_le_add_right (c := (m : Rat))).mpr hnn
    grind

theorem natCast_lt_iff (m n : Nat) : ((m : Rat) < (n : Rat)) ↔ m < n := by
  constructor
  · intro h
    have hle : m ≤ n := (natCast_le_iff m n).mp (Rat.le_of_lt h)
    have hne : m ≠ n := by
      intro heq
      rw [heq] at h
      exact Rat.lt_irrefl h
    omega
  · intro h
    have hle : (m : Rat) ≤ (n : Rat) := (natCast_le_iff m n).mpr (Nat.le_of_lt h)
    have hne : (m : Rat) ≠ (n : Rat) := by
      intro heq
      have : m = n := natCast_inj heq
      omega
    exact Rat.lt_of_le_of_ne hle hne

theorem nat_pow2_pos (n : Nat) : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)

theorem rat_pow2_pos (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) :=
  natCast_pos (nat_pow2_pos n)

theorem rat_pow2_ge_one (n : Nat) : (1 : Rat) ≤ ((2 ^ n : Nat) : Rat) :=
  (natCast_le_iff 1 (2 ^ n)).mpr (nat_pow2_pos n)

theorem nat_pow2_ge_four {b : Nat} (hb : 2 ≤ b) : 4 ≤ 2 ^ b := by
  have h : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide : 0 < 2) hb
  simpa using h

theorem rat_pow2_ge_four {b : Nat} (hb : 2 ≤ b) : (4 : Rat) ≤ ((2 ^ b : Nat) : Rat) :=
  (natCast_le_iff 4 (2 ^ b)).mpr (nat_pow2_ge_four hb)

theorem nat_pow2_ge_two {b : Nat} (hb : 1 ≤ b) : 2 ≤ 2 ^ b := by
  have h : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide : 0 < 2) hb
  simpa using h

theorem rat_pow2_ge_two {b : Nat} (hb : 1 ≤ b) : (2 : Rat) ≤ ((2 ^ b : Nat) : Rat) :=
  (natCast_le_iff 2 (2 ^ b)).mpr (nat_pow2_ge_two hb)

theorem rat_max_eq_left_of_le {a b : Rat} (h : b ≤ a) : max a b = a := by
  simp only [max]
  split
  · rename_i hle
    exact Rat.le_antisymm h hle
  · rfl

theorem rat_max_eq_right_of_le {a b : Rat} (h : a ≤ b) : max a b = b := by
  simp only [max]
  simp [h]

theorem rat_min_eq_left_of_le {a b : Rat} (h : a ≤ b) : min a b = a := by
  simp only [min]
  simp [h]

theorem rat_min_eq_right_of_le {a b : Rat} (h : b ≤ a) : min a b = b := by
  simp only [min]
  split
  · rename_i hle
    exact Rat.le_antisymm hle h
  · rfl

theorem rat_le_max_left (a b : Rat) : a ≤ max a b := by
  simp only [max]
  split
  · assumption
  · exact Rat.le_refl

theorem rat_le_max_right (a b : Rat) : b ≤ max a b := by
  simp only [max]
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem rat_max_le {a b c : Rat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  simp only [max]
  split
  · exact hb
  · exact ha

theorem rat_min_le_left (a b : Rat) : min a b ≤ a := by
  simp only [min]
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem rat_min_le_right (a b : Rat) : min a b ≤ b := by
  simp only [min]
  split
  · assumption
  · exact Rat.le_refl

theorem rat_le_min {a b c : Rat} (ha : c ≤ a) (hb : c ≤ b) : c ≤ min a b := by
  simp only [min]
  split
  · exact ha
  · exact hb

theorem mxfpMinPosInt_false (a b : Nat) : mxfpMinPosInt a b false = 1 := by
  unfold mxfpMinPosInt
  simp

theorem mxfpMinPosInt_true {a b : Nat} (ha : 1 ≤ a) : mxfpMinPosInt a b true = 2 ^ b := by
  unfold mxfpMinPosInt
  have hne : a ≠ 0 := by omega
  simp [hne]

/-- Fast kernel-friendly rational inequality via `Nat` cross-multiplication (zero `Rat.normalize`). -/
theorem rat_div_le_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := by
  rw [rat_div_le_div_iff (natCast_pos hb) (natCast_pos hd)]
  have hl : (a : Rat) * (d : Rat) = ((a * d : Nat) : Rat) := by grind
  have hr : (c : Rat) * (b : Rat) = ((c * b : Nat) : Rat) := by grind
  rw [hl, hr]
  exact (natCast_le_iff _ _).mpr h

theorem rat_div_lt_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) :
    (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  rw [rat_div_lt_div_iff (natCast_pos hb) (natCast_pos hd)]
  have hl : (a : Rat) * (d : Rat) = ((a * d : Nat) : Rat) := by grind
  have hr : (c : Rat) * (b : Rat) = ((c * b : Nat) : Rat) := by grind
  rw [hl, hr]
  exact (natCast_lt_iff _ _).mpr h

theorem rat_div_eq_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d = c * b) :
    (a : Rat) / (b : Rat) = (c : Rat) / (d : Rat) := by
  rw [rat_div_eq_div_iff (Rat.ne_of_gt (natCast_pos hb)) (Rat.ne_of_gt (natCast_pos hd))]
  have hl : (a : Rat) * (d : Rat) = ((a * d : Nat) : Rat) := by grind
  have hr : (c : Rat) * (b : Rat) = ((c * b : Nat) : Rat) := by grind
  rw [hl, hr]
  exact congrArg (fun x : Nat => (x : Rat)) h

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
    rw [heq] at h1
    exact Rat.not_le.mpr h2 h1
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  rat_lt_of_lt_of_le h1 (Rat.le_of_lt h2)

/-- Pure-`Nat` fraction maximum for fast kernel-checked evaluation without `Rat.normalize`. -/
def natFracMax (p q : Nat × Nat) : Nat × Nat :=
  if p.1 * q.2 ≤ q.1 * p.2 then q else p

theorem natFracMax_den_pos {p q : Nat × Nat} (hp : 0 < p.2) (hq : 0 < q.2) :
    0 < (natFracMax p q).2 := by
  unfold natFracMax
  split <;> assumption

theorem natFracMax_val (p q : Nat × Nat) (hp : 0 < p.2) (hq : 0 < q.2) :
    max ((p.1 : Rat) / (p.2 : Rat)) ((q.1 : Rat) / (q.2 : Rat)) =
      ((natFracMax p q).1 : Rat) / ((natFracMax p q).2 : Rat) := by
  unfold natFracMax
  split
  · rename_i hle
    exact rat_max_eq_right_of_le (rat_div_le_div_of_nat hp hq hle)
  · rename_i hnot
    have hge : q.1 * p.2 ≤ p.1 * q.2 := by omega
    exact rat_max_eq_left_of_le (rat_div_le_div_of_nat hq hp hge)

def deltaContNormNat (b B : Nat) : Nat × Nat :=
  let k := B - 1
  let top := 2 ^ (b + 1) - 1
  let q := 2 ^ (b + 1) + 1
  (k, 4 * top * top + k * q * q)

def deltaContUfNat (M u B : Nat) : Nat × Nat :=
  let k := B - 1
  (u * u * k, 4 * (M * M) + u * u * k)

def deltaContNat (a b : Nat) (ftz : Bool) (B : Nat) : Nat × Nat :=
  natFracMax (deltaContNormNat b B) (deltaContUfNat (mxfpMaxInt a b) (mxfpMinPosInt a b ftz) B)

def deltaContIntNat (b B : Nat) : Nat × Nat :=
  deltaContUfNat (2 ^ b - 1) 1 B

def deltaE8m0Branch1Nat (a b u B : Nat) : Nat × Nat :=
  let s := 2 ^ (2 ^ a - 2)
  let q := 2 ^ (b + 1) + 1
  let k := B - 1
  (s * s + u * u * k, q * q * s * s + u * u * k)

def deltaE8m0Branch2Nat (a b u B : Nat) : Nat × Nat :=
  let s2 := 2 ^ (2 ^ a - 3)
  let p := 2 ^ (b + 2) - 1
  let k := B - 1
  (s2 * s2 + u * u * k, p * p * s2 * s2 + u * u * k)

def deltaE8m0UfNat (M u B : Nat) : Nat × Nat :=
  let k := B - 1
  (u * u * k, M * M + u * u * k)

def deltaE8m0Nat (a b : Nat) (ftz : Bool) (B : Nat) : Nat × Nat :=
  let u := mxfpMinPosInt a b ftz
  natFracMax (deltaE8m0Branch1Nat a b u B)
    (natFracMax (deltaE8m0Branch2Nat a b u B) (deltaE8m0UfNat (mxfpMaxInt a b) u B))

def deltaE8m0IntNat (b B : Nat) : Nat × Nat :=
  let m := 2 ^ b - 1
  let k := B - 1
  (1 + k, m * m + k)

theorem deltaContNorm_eq_nat (b B : Nat) :
    deltaContNorm b B = ((deltaContNormNat b B).1 : Rat) / ((deltaContNormNat b B).2 : Rat) := by
  unfold deltaContNorm deltaContNormNat
  congr 1; grind

theorem deltaContUf_eq_nat (M u B : Nat) :
    deltaContUf M u B = ((deltaContUfNat M u B).1 : Rat) / ((deltaContUfNat M u B).2 : Rat) := by
  unfold deltaContUf deltaContUfNat
  congr 1 <;> grind

theorem deltaCont_eq_nat {a b : Nat} (ftz : Bool) (B : Nat)
    (h1 : 0 < (deltaContNormNat b B).2)
    (h2 : 0 < (deltaContUfNat (mxfpMaxInt a b) (mxfpMinPosInt a b ftz) B).2) :
    deltaCont a b ftz B = ((deltaContNat a b ftz B).1 : Rat) / ((deltaContNat a b ftz B).2 : Rat) := by
  unfold deltaCont deltaContNat
  rw [deltaContNorm_eq_nat, deltaContUf_eq_nat, natFracMax_val _ _ h1 h2]

theorem deltaContInt_eq_nat (b B : Nat) :
    deltaContInt b B = ((deltaContIntNat b B).1 : Rat) / ((deltaContIntNat b B).2 : Rat) :=
  deltaContUf_eq_nat _ _ _

theorem deltaE8m0Branch1_eq_nat (a b u B : Nat) :
    deltaE8m0Branch1 a b u B =
      ((deltaE8m0Branch1Nat a b u B).1 : Rat) / ((deltaE8m0Branch1Nat a b u B).2 : Rat) := by
  unfold deltaE8m0Branch1 deltaE8m0Branch1Nat
  congr 1 <;> grind

theorem deltaE8m0Branch2_eq_nat (a b u B : Nat) :
    deltaE8m0Branch2 a b u B =
      ((deltaE8m0Branch2Nat a b u B).1 : Rat) / ((deltaE8m0Branch2Nat a b u B).2 : Rat) := by
  unfold deltaE8m0Branch2 deltaE8m0Branch2Nat
  congr 1 <;> grind

theorem deltaE8m0Uf_eq_nat (M u B : Nat) :
    deltaE8m0Uf M u B = ((deltaE8m0UfNat M u B).1 : Rat) / ((deltaE8m0UfNat M u B).2 : Rat) := by
  unfold deltaE8m0Uf deltaE8m0UfNat
  congr 1 <;> grind

theorem deltaE8m0_eq_nat {a b : Nat} (ftz : Bool) (B : Nat)
    (h1 : 0 < (deltaE8m0Branch1Nat a b (mxfpMinPosInt a b ftz) B).2)
    (h2 : 0 < (deltaE8m0Branch2Nat a b (mxfpMinPosInt a b ftz) B).2)
    (h3 : 0 < (deltaE8m0UfNat (mxfpMaxInt a b) (mxfpMinPosInt a b ftz) B).2) :
    deltaE8m0 a b ftz B = ((deltaE8m0Nat a b ftz B).1 : Rat) / ((deltaE8m0Nat a b ftz B).2 : Rat) := by
  unfold deltaE8m0 deltaE8m0Nat
  dsimp only
  rw [deltaE8m0Branch1_eq_nat, deltaE8m0Branch2_eq_nat, deltaE8m0Uf_eq_nat,
    natFracMax_val _ _ h2 h3, natFracMax_val _ _ h1 (natFracMax_den_pos h2 h3)]

theorem deltaE8m0Int_eq_nat (b B : Nat) :
    deltaE8m0Int b B = ((deltaE8m0IntNat b B).1 : Rat) / ((deltaE8m0IntNat b B).2 : Rat) := by
  unfold deltaE8m0Int deltaE8m0IntNat
  congr 1 <;> grind

end MxfpDoublelogFtz
