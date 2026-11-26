/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VcacheIprXorvdc.Defs

/-!
# Pure-`Init` `Rat` Order, `finSum`, and Bijection-Invariance Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace VcacheIprXorvdc

/-! ### Basic `Rat` Order & Arithmetic Helpers -/

theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind
theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind
theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c := by grind
theorem rat_le_trans {a b c : Rat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by grind
theorem rat_lt_of_not_le {a b : Rat} (h : ¬ a ≤ b) : b < a := by grind
theorem rat_le_of_not_lt {a b : Rat} (h : ¬ a < b) : b ≤ a := by grind

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by grind
theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by grind
theorem rat_sub_pos {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by grind
theorem rat_lt_of_sub_pos {a b : Rat} (h : (0 : Rat) < a - b) : b < a := by grind

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
  have h1 : (0 : Rat) ≤ b - a := by grind
  have h2 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc h1
  grind

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  have h1 : (0 : Rat) < b - a := by grind
  have h2 : (0 : Rat) < c * (b - a) := rat_mul_pos hc h1
  grind

theorem rat_mul_lt_mul_of_pos_right {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    a * c < b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_lt_mul_of_pos_left h hc

theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by grind
theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by grind
theorem rat_add_lt_add_of_lt_of_le {a b c d : Rat} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d := by grind

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  by_cases h : (0 : Rat) ≤ x
  · exact Rat.mul_nonneg h h
  · have hneg : (0 : Rat) ≤ -x := by grind
    have hsq : (-x) * (-x) = x * x := by grind
    rw [← hsq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_pos {x : Rat} (hx : x ≠ 0) : (0 : Rat) < x * x := by
  have hge := rat_sq_nonneg x
  have hne : x * x ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hx h
    | inr h => exact hx h
  exact Rat.lt_of_le_of_ne hge (Ne.symm hne)

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < 1 / a := by
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  by_cases h : (0 : Rat) < 1 / a
  · exact h
  · have hle : 1 / a ≤ 0 := by grind
    have hmul : (1 / a) * a ≤ 0 * a := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt ha)
    have h1 : (1 / a) * a = 1 := by grind
    grind

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  have eq : a / b = a * (1 / b) := by grind
  rw [eq]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  have eq : a / b = a * (1 / b) := by grind
  rw [eq]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_lt_iff {a b c : Rat} (hb : (0 : Rat) < b) :
    a / b < c ↔ a < c * b := by
  have hne : b ≠ 0 := Rat.ne_of_gt hb
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hb
    have eq : a / b * b = a := by grind
    rw [eq] at h1
    exact h1
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h (rat_inv_pos hb)
    have eq1 : a * (1 / b) = a / b := by grind
    have eq2 : c * b * (1 / b) = c := by grind
    rw [eq1, eq2] at h1
    exact h1

theorem rat_lt_div_iff {a b c : Rat} (hc : (0 : Rat) < c) :
    a < b / c ↔ a * c < b := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hc
    have eq : b / c * c = b := by grind
    rw [eq] at h1
    exact h1
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h (rat_inv_pos hc)
    have eq1 : a * c * (1 / c) = a := by grind
    have eq2 : b * (1 / c) = b / c := by grind
    rw [eq1, eq2] at h1
    exact h1

theorem rat_le_div_iff {a b c : Rat} (hc : (0 : Rat) < c) :
    a ≤ b / c ↔ a * c ≤ b := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hc)
    have eq : b / c * c = b := by grind
    rw [eq] at h1
    exact h1
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))
    have eq1 : a * c * (1 / c) = a := by grind
    have eq2 : b * (1 / c) = b / c := by grind
    rw [eq1, eq2] at h1
    exact h1

theorem rat_div_le_iff {a b c : Rat} (hb : (0 : Rat) < b) :
    a / b ≤ c ↔ a ≤ c * b := by
  have hne : b ≠ 0 := Rat.ne_of_gt hb
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hb)
    have eq : a / b * b = a := by grind
    rw [eq] at h1
    exact h1
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hb))
    have eq1 : a * (1 / b) = a / b := by grind
    have eq2 : c * b * (1 / b) = c := by grind
    rw [eq1, eq2] at h1
    exact h1

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => grind
    | succ m =>
      have hk : (0 : Rat) < ((m + 1 : Nat) : Rat) := ih (by omega)
      have eq : ((m + 2 : Nat) : Rat) = ((m + 1 : Nat) : Rat) + 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, Rat.natCast_add]
        simp
      rw [eq]
      grind

theorem rat_natCast_ne_zero {n : Nat} (hn : 0 < n) : (n : Rat) ≠ 0 :=
  Rat.ne_of_gt (rat_natCast_pos hn)

theorem rat_natCast_le {m n : Nat} (h : m ≤ n) : (m : Rat) ≤ (n : Rat) := by
  induction h with
  | refl => grind
  | @step k _ ih =>
    have eq : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by simp [Rat.natCast_add]
    rw [eq]
    grind

theorem rat_natCast_lt {m n : Nat} (h : m < n) : (m : Rat) < (n : Rat) := by
  have h1 : (m : Rat) ≤ ((n - 1 : Nat) : Rat) := rat_natCast_le (by omega)
  have h2 : ((n - 1 : Nat) : Rat) + 1 = (n : Rat) := by
    have : n - 1 + 1 = n := by omega
    rw [← this, Rat.natCast_add]
    simp
  grind

theorem ratAbs_nonneg (x : Rat) : (0 : Rat) ≤ ratAbs x := by
  unfold ratAbs
  split <;> grind

theorem ratAbs_le_iff {x b : Rat} : ratAbs x ≤ b ↔ -b ≤ x ∧ x ≤ b := by
  unfold ratAbs
  split <;> constructor <;> grind

theorem ratAbs_lt_iff {x b : Rat} : ratAbs x < b ↔ -b < x ∧ x < b := by
  unfold ratAbs
  split <;> constructor <;> grind

/-! ### `finSum` Algebraic & Order Lemmas -/

theorem finSum_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ j, f j = g j) :
    finSum f = finSum g := by
  unfold finSum
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumAux]
    rw [ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem finSum_zero {n : Nat} : finSum (fun _ : Fin n => (0 : Rat)) = 0 := by
  unfold finSum
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_add {n : Nat} (f g : Fin n → Rat) :
    finSum (fun j => f j + g j) = finSum f + finSum g := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
            grind
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_sub {n : Nat} (f g : Fin n → Rat) :
    finSum (fun j => f j - g j) = finSum f - finSum g := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
            grind
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    finSum (fun j => c * f j) = c * finSum f := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    finSum (fun j => f j * c) = finSum f * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih]
    grind

theorem finSum_const {n : Nat} (c : Rat) :
    finSum (fun _ : Fin n => c) = (n : Rat) * c := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    rw [ih, Rat.natCast_add]
    simp
    grind

theorem finSum_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ j, (0 : Rat) ≤ f j) :
    (0 : Rat) ≤ finSum f := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    have h1 := ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    grind

theorem finSum_le {n : Nat} {f g : Fin n → Rat} (h : ∀ j, f j ≤ g j) :
    finSum f ≤ finSum g := by
  unfold finSum
  induction n with
  | zero => simp [finSumAux]
  | succ k ih =>
    simp only [finSumAux]
    have h1 := ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    grind

theorem finSum_single {n : Nat} (j0 : Fin n) (c : Rat) :
    finSum (fun j : Fin n => if j = j0 then c else 0) = c := by
  unfold finSum
  induction n with
  | zero => exact Fin.elim0 j0
  | succ k ih =>
    simp only [finSumAux]
    by_cases h : j0.val = k
    · have hzero : finSumAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = j0 then c else 0) = 0 := by
        have hcongr : finSum (fun j : Fin k => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = j0 then c else 0) =
            finSum (fun _ : Fin k => (0 : Rat)) := by
          apply finSum_congr
          intro j
          have hne : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ j0 := by
            intro heq
            have : j.val = j0.val := congrArg Fin.val heq
            omega
          simp [hne]
        rw [finSum_zero] at hcongr
        exact hcongr
      have heq : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = j0 := Fin.ext h.symm
      rw [hzero]
      simp [heq]
      grind
    · have hlt : j0.val < k := by omega
      let j0' : Fin k := ⟨j0.val, hlt⟩
      have hne : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ j0 := by
        intro heq
        exact h (congrArg Fin.val heq).symm
      simp only [hne, ↓reduceIte]
      have hcongr : finSumAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = j0 then c else 0) =
          finSumAux k (fun j => if j = j0' then c else 0) := by
        apply @finSum_congr k
        intro j
        by_cases hj : j = j0'
        · subst hj
          have : (⟨j0'.val, Nat.lt_succ_of_lt j0'.isLt⟩ : Fin (k + 1)) = j0 := Fin.ext rfl
          simp [this]
        · have : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ j0 := by
            intro heq
            have hv : j.val = j0.val := congrArg Fin.val heq
            exact hj (Fin.ext hv)
          simp [hj, this]
      rw [hcongr, ih j0']
      grind

theorem finSum_comm {m n : Nat} (f : Fin m → Fin n → Rat) :
    finSum (fun i => finSum (fun j => f i j)) = finSum (fun j => finSum (fun i => f i j)) := by
  induction m with
  | zero =>
    change (0 : Rat) = finSum (fun _ : Fin n => (0 : Rat))
    rw [finSum_zero]
  | succ k ih =>
    have hL : finSum (fun i : Fin (k + 1) => finSum (fun j => f i j)) =
        finSum (fun i : Fin k => finSum (fun j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j)) +
        finSum (fun j => f ⟨k, Nat.lt_succ_self k⟩ j) := rfl
    rw [hL, ih, ← finSum_add]
    apply finSum_congr
    intro j
    rfl

/-- Cauchy–Schwarz on `Fin L` specialized to `(∑_j p_j)^2 ≤ L * ∑_j p_j^2`. -/
theorem finSum_sq_le_mul_ipr {L : Nat} (p : Fin L → Rat) :
    finSum p * finSum p ≤ (L : Rat) * ipr p := by
  have hnonneg : (0 : Rat) ≤ finSum (fun i => finSum (fun j => (p i - p j) * (p i - p j))) := by
    apply finSum_nonneg
    intro i
    apply finSum_nonneg
    intro j
    exact rat_sq_nonneg (p i - p j)
  have hexpand : finSum (fun i => finSum (fun j => (p i - p j) * (p i - p j))) =
      2 * ((L : Rat) * ipr p - finSum p * finSum p) := by
    have h1 : ∀ i : Fin L,
        finSum (fun j => (p i - p j) * (p i - p j)) =
        (L : Rat) * (p i * p i) - 2 * p i * finSum p + ipr p := by
      intro i
      have hcongr : finSum (fun j => (p i - p j) * (p i - p j)) =
          finSum (fun j => (p i * p i - 2 * p i * p j) + p j * p j) := by
        apply finSum_congr
        intro j
        grind
      rw [hcongr, finSum_add, finSum_sub, finSum_const, finSum_mul_left]
      rfl
    rw [finSum_congr h1, finSum_add, finSum_sub, finSum_mul_left, finSum_const]
    have hmid : finSum (fun i => 2 * p i * finSum p) = 2 * (finSum p * finSum p) := by
      have hc : finSum (fun i => 2 * p i * finSum p) = finSum (fun i => p i * (2 * finSum p)) := by
        apply finSum_congr; intro i; grind
      rw [hc, finSum_mul_right]
      grind
    rw [hmid]
    unfold ipr
    grind
  rw [hexpand] at hnonneg
  grind

/-- Splitting `finSum` on `Fin (n + 1)` at index `0`. -/
theorem finSum_split_zero {n : Nat} (f : Fin (n + 1) → Rat) :
    finSum f = f ⟨0, Nat.zero_lt_succ n⟩ + finSum (fun j : Fin n => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) := by
  induction n with
  | zero =>
    simp [finSum, finSumAux]
    grind
  | succ k ih =>
    have hL : finSum f = finSum (fun j : Fin (k + 1) => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
        f ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := rfl
    rw [hL, ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)]
    have hR : finSum (fun j : Fin (k + 1) => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) =
        finSum (fun j : Fin k => f ⟨j.val + 1, Nat.lt_succ_of_lt (Nat.succ_lt_succ j.isLt)⟩) +
        f ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := rfl
    rw [hR]
    grind

/-- Splitting `finSum` on `Fin (a + b)` into lower `Fin a` and upper `Fin b`. -/
theorem finSum_append {a b : Nat} (f : Fin (a + b) → Rat) :
    finSum f = finSum (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩) +
      finSum (fun j : Fin b => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  induction b with
  | zero =>
    simp [finSum, finSumAux]
    grind
  | succ k ih =>
    have hL : finSum f =
        finSum (fun i : Fin (a + k) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
        f ⟨a + k, Nat.lt_succ_self (a + k)⟩ := rfl
    rw [hL, ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    have hR : finSum (fun j : Fin (k + 1) => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) =
        finSum (fun j : Fin k => f ⟨a + j.val, Nat.lt_succ_of_lt (Nat.add_lt_add_left j.isLt a)⟩) +
        f ⟨a + k, Nat.lt_succ_self (a + k)⟩ := rfl
    rw [hR]
    grind

/-! ### `finSumNat` & `finSumInt` Helpers -/

theorem finSumNat_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ j, f j = g j) :
    finSumNat f = finSumNat g := by
  unfold finSumNat
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSumNatAux]
    rw [ih (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem finSumNat_add {n : Nat} (f g : Fin n → Nat) :
    finSumNat (fun j => f j + g j) = finSumNat f + finSumNat g := by
  unfold finSumNat
  induction n with
  | zero => simp [finSumNatAux]
  | succ k ih =>
    simp only [finSumNatAux]
    rw [ih]
    omega

theorem finSumNat_const {n : Nat} (c : Nat) :
    finSumNat (fun _ : Fin n => c) = n * c := by
  unfold finSumNat
  induction n with
  | zero => simp [finSumNatAux]
  | succ k ih =>
    simp only [finSumNatAux]
    rw [ih, Nat.succ_mul]

theorem finSumNat_cast_rat {n : Nat} (f : Fin n → Nat) :
    ((finSumNat f : Nat) : Rat) = finSum (fun j => (f j : Rat)) := by
  unfold finSumNat finSum
  induction n with
  | zero => simp [finSumNatAux, finSumAux]
  | succ k ih =>
    simp only [finSumNatAux, finSumAux, Rat.natCast_add]
    rw [ih]

theorem finSumNat_single {n : Nat} (j0 : Fin n) (c : Nat) :
    finSumNat (fun j : Fin n => if j = j0 then c else 0) = c := by
  unfold finSumNat
  induction n with
  | zero => exact Fin.elim0 j0
  | succ k ih =>
    simp only [finSumNatAux]
    by_cases h : j0.val = k
    · have hzero : finSumNatAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = j0 then c else 0) = 0 := by
        have hcongr : finSumNat (fun j : Fin k => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = j0 then c else 0) =
            finSumNat (fun _ : Fin k => 0) := by
          apply finSumNat_congr
          intro j
          have hne : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ j0 := by
            intro heq
            have : j.val = j0.val := congrArg Fin.val heq
            omega
          simp [hne]
        rw [finSumNat_const, Nat.mul_zero] at hcongr
        exact hcongr
      have heq : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = j0 := Fin.ext h.symm
      rw [hzero]
      simp [heq]
    · have hlt : j0.val < k := by omega
      let j0' : Fin k := ⟨j0.val, hlt⟩
      have hne : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ j0 := by
        intro heq
        exact h (congrArg Fin.val heq).symm
      simp only [hne, ↓reduceIte]
      have hcongr : finSumNatAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = j0 then c else 0) =
          finSumNatAux k (fun j => if j = j0' then c else 0) := by
        apply @finSumNat_congr k
        intro j
        by_cases hj : j = j0'
        · subst hj
          have : (⟨j0'.val, Nat.lt_succ_of_lt j0'.isLt⟩ : Fin (k + 1)) = j0 := Fin.ext rfl
          simp [this]
        · have : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ j0 := by
            intro heq
            have hv : j.val = j0.val := congrArg Fin.val heq
            exact hj (Fin.ext hv)
          simp [hj, this]
      rw [hcongr, ih j0']
      omega

theorem finSumNat_comm {m n : Nat} (f : Fin m → Fin n → Nat) :
    finSumNat (fun i => finSumNat (fun j => f i j)) =
    finSumNat (fun j => finSumNat (fun i => f i j)) := by
  induction m with
  | zero =>
    change 0 = finSumNat (fun _ : Fin n => 0)
    rw [finSumNat_const]
    omega
  | succ k ih =>
    have hL : finSumNat (fun i : Fin (k + 1) => finSumNat (fun j => f i j)) =
        finSumNat (fun i : Fin k => finSumNat (fun j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j)) +
        finSumNat (fun j => f ⟨k, Nat.lt_succ_self k⟩ j) := rfl
    rw [hL, ih, ← finSumNat_add]
    apply finSumNat_congr
    intro j
    rfl

/-- Bijection invariance of `finSumNat`: for any bijection `π : Fin n → Fin n` with inverse `πInv`,
    `∑_j f (π j) = ∑_i f i`. -/
theorem finSumNat_bij {n : Nat} (π πInv : Fin n → Fin n)
    (hL : ∀ x, πInv (π x) = x) (hR : ∀ y, π (πInv y) = y) (f : Fin n → Nat) :
    finSumNat (fun j => f (π j)) = finSumNat f := by
  have h1 : finSumNat (fun j => f (π j)) =
      finSumNat (fun j => finSumNat (fun i => if i = π j then f i else 0)) := by
    apply finSumNat_congr
    intro j
    have hcongr : finSumNat (fun i => if i = π j then f i else 0) =
        finSumNat (fun i => if i = π j then f (π j) else 0) := by
      apply finSumNat_congr
      intro i
      by_cases hi : i = π j
      · subst hi; simp
      · simp [hi]
    rw [hcongr, finSumNat_single]
  rw [h1, finSumNat_comm]
  apply finSumNat_congr
  intro i
  have h2 : finSumNat (fun j => if i = π j then f i else 0) =
      finSumNat (fun j => if j = πInv i then f i else 0) := by
    apply finSumNat_congr
    intro j
    by_cases hj : j = πInv i
    · subst hj
      simp [hR i]
    · have hne : i ≠ π j := by
        intro heq
        apply hj
        rw [heq, hL j]
      simp [hj, hne]
  rw [h2, finSumNat_single]

theorem finSumInt_le_bound {n : Nat} (f : Fin n → Int) (B : Fin n → Int)
    (h : ∀ j, -(B j) ≤ f j ∧ f j ≤ B j) :
    -(finSumInt B) ≤ finSumInt f ∧ finSumInt f ≤ finSumInt B := by
  unfold finSumInt
  induction n with
  | zero =>
    simp [finSumIntAux]
  | succ k ih =>
    simp only [finSumIntAux]
    have h1 := ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
      (fun j => B ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
      (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    omega

theorem finSumInt_const {n : Nat} (c : Int) :
    finSumInt (fun _ : Fin n => c) = (n : Int) * c := by
  unfold finSumInt
  induction n with
  | zero => simp [finSumIntAux]
  | succ k ih =>
    simp only [finSumIntAux]
    rw [ih]
    grind

theorem finSumInt_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    finSumInt (fun j => f j * c) = finSumInt f * c := by
  unfold finSumInt
  induction n with
  | zero => simp [finSumIntAux]
  | succ k ih =>
    simp only [finSumIntAux]
    rw [ih]
    grind

end VcacheIprXorvdc
