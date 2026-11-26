/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MoeBiasPlacement.Defs

/-!
# Pure-`Init` Arithmetic & Finite-Sum Helpers (`Nat`, `Int`, `Rat`)
-/

namespace MoeBiasPlacement

/-! ## `Rat` Order, Absolute Value, and Division Helpers -/

theorem rat_le_refl (a : Rat) : a ≤ a := Rat.le_refl

theorem rat_le_total (a b : Rat) : a ≤ b ∨ b ≤ a := Rat.le_total

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [Rat.lt_iff] at h1 ⊢
  rw [Rat.le_iff] at h2
  have hb : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hc : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have ha : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hm1 : a.num * (b.den : Int) * (c.den : Int) < b.num * (a.den : Int) * (c.den : Int) :=
    Int.mul_lt_mul_of_pos_right h1 hc
  have hm2 : b.num * (c.den : Int) * (a.den : Int) ≤ c.num * (b.den : Int) * (a.den : Int) :=
    Int.mul_le_mul_of_nonneg_right h2 (Int.le_of_lt ha)
  have heq : b.num * (a.den : Int) * (c.den : Int) = b.num * (c.den : Int) * (a.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (a.den : Int), ← Int.mul_assoc]
  have hlt : a.num * (c.den : Int) * (b.den : Int) < c.num * (a.den : Int) * (b.den : Int) := by
    have hl : a.num * (c.den : Int) * (b.den : Int) = a.num * (b.den : Int) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (c.den : Int), ← Int.mul_assoc]
    have hr : c.num * (a.den : Int) * (b.den : Int) = c.num * (b.den : Int) * (a.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (a.den : Int), ← Int.mul_assoc]
    rw [hl, hr]
    exact Int.lt_of_lt_of_le hm1 (heq ▸ hm2)
  exact Int.lt_of_mul_lt_mul_right hlt (Int.le_of_lt hb)

theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rw [Rat.le_iff] at h1
  rw [Rat.lt_iff] at h2 ⊢
  have hb : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hc : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have ha : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hm1 : a.num * (b.den : Int) * (c.den : Int) ≤ b.num * (a.den : Int) * (c.den : Int) :=
    Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hc)
  have hm2 : b.num * (c.den : Int) * (a.den : Int) < c.num * (b.den : Int) * (a.den : Int) :=
    Int.mul_lt_mul_of_pos_right h2 ha
  have heq : b.num * (a.den : Int) * (c.den : Int) = b.num * (c.den : Int) * (a.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (a.den : Int), ← Int.mul_assoc]
  have hlt : a.num * (c.den : Int) * (b.den : Int) < c.num * (a.den : Int) * (b.den : Int) := by
    have hl : a.num * (c.den : Int) * (b.den : Int) = a.num * (b.den : Int) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (c.den : Int), ← Int.mul_assoc]
    have hr : c.num * (a.den : Int) * (b.den : Int) = c.num * (b.den : Int) * (a.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (a.den : Int), ← Int.mul_assoc]
    rw [hl, hr]
    exact Int.lt_of_le_of_lt (heq ▸ hm1) hm2
  exact Int.lt_of_mul_lt_mul_right hlt (Int.le_of_lt hb)

theorem rat_neg_le_neg_iff (a b : Rat) : -a ≤ -b ↔ b ≤ a := by
  rw [Rat.le_iff, Rat.le_iff]
  simp only [Rat.neg_num, Rat.neg_den, Int.neg_mul]
  omega

theorem rat_neg_le_iff (a b : Rat) : -a ≤ b ↔ -b ≤ a := by
  rw [Rat.le_iff, Rat.le_iff]
  simp only [Rat.neg_num, Rat.neg_den, Int.neg_mul]
  omega

theorem rat_le_neg_iff (a b : Rat) : a ≤ -b ↔ b ≤ -a := by
  rw [Rat.le_iff, Rat.le_iff]
  simp only [Rat.neg_num, Rat.neg_den, Int.neg_mul]
  omega

theorem rat_neg_nonneg_of_nonpos {a : Rat} (h : a ≤ 0) : 0 ≤ -a := by
  have := (rat_neg_le_neg_iff 0 a).mpr h
  simpa using this

theorem rat_neg_nonpos_of_nonneg {a : Rat} (h : 0 ≤ a) : -a ≤ 0 := by
  have := (rat_neg_le_neg_iff a 0).mpr h
  simpa using this

theorem rat_le_of_not_lt {a b : Rat} (h : ¬ b < a) : a ≤ b := by
  rcases rat_le_total a b with hab | hba
  · exact hab
  · rcases Rat.le_iff_lt_or_eq.mp hba with hlt | heq
    · exact absurd hlt h
    · rw [heq]; exact rat_le_refl _

theorem rat_lt_of_not_le {a b : Rat} (h : ¬ b ≤ a) : a < b := by
  rcases rat_le_total a b with hab | hba
  · rcases Rat.le_iff_lt_or_eq.mp hab with hlt | heq
    · exact hlt
    · exfalso; apply h; rw [heq]; exact rat_le_refl _
  · exact absurd hba h

theorem rat_not_lt_of_le {a b : Rat} (h : a ≤ b) : ¬ b < a := fun hlt =>
  Rat.lt_irrefl (rat_lt_of_lt_of_le hlt h)

theorem rat_abs_eq_ite (x : Rat) : x.abs = if 0 ≤ x then x else -x := by
  rfl

theorem rat_le_abs_self (x : Rat) : x ≤ x.abs := by
  rw [rat_abs_eq_ite]
  by_cases h : 0 ≤ x
  · simp [h]
  · simp [h]
    have hx : x ≤ 0 := Rat.le_of_lt (rat_lt_of_not_le h)
    exact Rat.le_trans hx (rat_neg_nonneg_of_nonpos hx)

theorem rat_neg_le_abs_self (x : Rat) : -x ≤ x.abs := by
  rw [rat_abs_eq_ite]
  by_cases h : 0 ≤ x
  · simp [h]
    exact Rat.le_trans (rat_neg_nonpos_of_nonneg h) h
  · simp [h]

theorem rat_abs_le_iff (x c : Rat) : x.abs ≤ c ↔ -c ≤ x ∧ x ≤ c := by
  constructor
  · intro h
    exact ⟨(rat_neg_le_iff c x).mpr (Rat.le_trans (rat_neg_le_abs_self x) h),
           Rat.le_trans (rat_le_abs_self x) h⟩
  · rintro ⟨h1, h2⟩
    rw [rat_abs_eq_ite]
    by_cases h : 0 ≤ x
    · simp [h]; exact h2
    · simp [h]; exact (rat_neg_le_iff x c).mpr h1

theorem rat_abs_nonneg (x : Rat) : 0 ≤ x.abs := by
  rw [rat_abs_eq_ite]
  by_cases h : 0 ≤ x
  · simp [h]
  · simp [h]; exact rat_neg_nonneg_of_nonpos (Rat.le_of_lt (rat_lt_of_not_le h))

theorem rat_abs_of_nonneg {x : Rat} (hx : 0 ≤ x) : x.abs = x := by
  rw [rat_abs_eq_ite]; simp [hx]

theorem rat_abs_neg (x : Rat) : (-x).abs = x.abs := by
  rw [rat_abs_eq_ite, rat_abs_eq_ite]
  by_cases h : 0 ≤ x
  · by_cases h' : 0 ≤ -x
    · have hxle : x ≤ 0 := (rat_neg_le_neg_iff 0 x).mp (by simpa using h')
      have hx0 : x = 0 := Rat.le_antisymm hxle h
      simp [hx0]
    · simp [h, h']
  · have hx : x ≤ 0 := Rat.le_of_lt (rat_lt_of_not_le h)
    have h' : 0 ≤ -x := rat_neg_nonneg_of_nonpos hx
    simp [h, h']

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  rw [Rat.lt_iff]; simp; omega

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  rw [Rat.le_iff]; simp

theorem rat_natCast_ne_zero {n : Nat} (hn : 0 < n) : (n : Rat) ≠ 0 := by
  intro h
  have hlt := rat_natCast_pos hn
  rw [h] at hlt
  exact Rat.lt_irrefl hlt

theorem rat_natCast_add (a b : Nat) : ((a + b : Nat) : Rat) = (a : Rat) + (b : Rat) := by
  exact Rat.natCast_add a b

theorem rat_natCast_mul (a b : Nat) : ((a * b : Nat) : Rat) = (a : Rat) * (b : Rat) := by
  exact Rat.natCast_mul a b

theorem rat_natCast_le {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  rw [Rat.le_iff]; simp; omega

theorem rat_natCast_lt {a b : Nat} (h : a < b) : (a : Rat) < (b : Rat) := by
  rw [Rat.lt_iff]; simp; omega

theorem rat_mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [Rat.lt_iff] at ha hb ⊢
  simp at ha hb ⊢
  have hprod : 0 < a.num * b.num := Int.mul_pos ha hb
  have hden : 0 < a.den * b.den := Nat.mul_pos a.den_pos b.den_pos
  have hgcd : 0 < Nat.gcd (a.num * b.num).natAbs (a.den * b.den) :=
    Nat.gcd_pos_of_pos_right _ hden
  have hdvd := Nat.gcd_dvd_left (a.num * b.num).natAbs (a.den * b.den)
  have hnum : (a * b).num = (a.num * b.num) / ((Nat.gcd (a.num * b.num).natAbs (a.den * b.den) : Nat) : Int) := by
    rw [Rat.mul_def]
    simp [Rat.normalize]
  rw [hnum]
  generalize Nat.gcd (a.num * b.num).natAbs (a.den * b.den) = g at hgcd hdvd ⊢
  rcases hdvd with ⟨m, hm⟩
  have hprod_eq : a.num * b.num = (g : Int) * (m : Int) := by
    have h1 : ((a.num * b.num).natAbs : Int) = a.num * b.num := by omega
    rw [← h1, hm, Int.natCast_mul]
  have hmpos : 0 < m := by
    cases m with
    | zero => simp at hprod_eq; omega
    | succ k => omega
  rw [hprod_eq, Int.mul_ediv_cancel_left _ (by omega)]
  omega

theorem rat_inv_pos {a : Rat} (ha : 0 < a) : 0 < a⁻¹ := by
  have hne : a ≠ 0 := fun h => by rw [h] at ha; exact Rat.lt_irrefl ha
  have hprod : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hne
  by_cases hpos : 0 < a⁻¹
  · exact hpos
  · exfalso
    have h0 : a⁻¹ ≤ 0 := rat_le_of_not_lt hpos
    have hneg : 0 ≤ -a⁻¹ := rat_neg_nonneg_of_nonpos h0
    rcases Rat.le_iff_lt_or_eq.mp hneg with hlt | heq
    · have hp : 0 < a * (-a⁻¹) := rat_mul_pos ha hlt
      rw [Rat.mul_neg, hprod] at hp
      exact absurd hp (by decide)
    · have : a⁻¹ = 0 := by
        have h1 : -(-a⁻¹) = -(0 : Rat) := congrArg Neg.neg heq.symm
        simpa using h1
      rw [this, Rat.mul_zero] at hprod
      exact absurd hprod (by decide)

theorem rat_mul_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rcases Rat.le_iff_lt_or_eq.mp ha with ha' | ha'
  · rcases Rat.le_iff_lt_or_eq.mp hb with hb' | hb'
    · exact Rat.le_of_lt (rat_mul_pos ha' hb')
    · rw [← hb', Rat.mul_zero]; exact rat_le_refl 0
  · rw [← ha', Rat.zero_mul]; exact rat_le_refl 0

theorem rat_sub_nonneg_iff (a b : Rat) : 0 ≤ a - b ↔ b ≤ a := by
  constructor
  · intro h
    have h1 := (Rat.add_le_add_right (c := b)).mpr h
    simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add, Rat.add_zero] using h1
  · intro h
    have h1 := (Rat.add_le_add_right (c := -b)).mpr h
    simpa [Rat.sub_eq_add_neg, Rat.add_neg_cancel] using h1

theorem rat_sub_pos_iff (a b : Rat) : 0 < a - b ↔ b < a := by
  constructor
  · intro h
    have h1 := (Rat.add_lt_add_right (c := b)).mpr h
    simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add, Rat.add_zero] using h1
  · intro h
    have h1 := (Rat.add_lt_add_right (c := -b)).mpr h
    simpa [Rat.sub_eq_add_neg, Rat.add_neg_cancel] using h1

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  rw [← rat_sub_nonneg_iff] at hab ⊢
  have : b * c - a * c = (b - a) * c := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]
  rw [this]
  exact rat_mul_nonneg hab hc

theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  rw [Rat.mul_comm c a, Rat.mul_comm c b]
  exact rat_mul_le_mul_of_nonneg_right hab hc

theorem rat_mul_lt_mul_of_pos_right {a b c : Rat} (hab : a < b) (hc : 0 < c) :
    a * c < b * c := by
  rw [← rat_sub_pos_iff] at hab ⊢
  have : b * c - a * c = (b - a) * c := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]
  rw [this]
  exact rat_mul_pos hab hc

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (hab : a < b) (hc : 0 < c) :
    c * a < c * b := by
  rw [Rat.mul_comm c a, Rat.mul_comm c b]
  exact rat_mul_lt_mul_of_pos_right hab hc

theorem rat_div_le_div_of_nonneg_right {a b c : Rat} (hab : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact rat_mul_le_mul_of_nonneg_right hab (Rat.le_of_lt (rat_inv_pos hc))

theorem rat_div_le_iff {a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  have hne : c ≠ 0 := fun h => by rw [h] at hc; exact Rat.lt_irrefl hc
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hc)
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hne, Rat.mul_one] at h1
    exact h1
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne, Rat.mul_one] at h1
    rw [Rat.div_def]
    exact h1

theorem rat_le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  have hne : c ≠ 0 := fun h => by rw [h] at hc; exact Rat.lt_irrefl hc
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hc)
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hne, Rat.mul_one] at h1
    exact h1
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt (rat_inv_pos hc))
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne, Rat.mul_one] at h1
    rw [Rat.div_def]
    exact h1

theorem rat_div_lt_iff {a b c : Rat} (hc : 0 < c) : a / c < b ↔ a < b * c := by
  have hne : c ≠ 0 := fun h => by rw [h] at hc; exact Rat.lt_irrefl hc
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hc
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hne, Rat.mul_one] at h1
    exact h1
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h (rat_inv_pos hc)
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne, Rat.mul_one] at h1
    rw [Rat.div_def]
    exact h1

theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans ((Rat.add_le_add_right (c := c)).mpr h1) ((Rat.add_le_add_left (c := b)).mpr h2)

theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d :=
  rat_lt_of_le_of_lt ((Rat.add_le_add_right (c := c)).mpr h1) ((Rat.add_lt_add_left (c := b)).mpr h2)

theorem rat_add_lt_add_of_lt_of_le {a b c d : Rat} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d :=
  rat_lt_of_lt_of_le ((Rat.add_lt_add_right (c := c)).mpr h1) ((Rat.add_le_add_left (c := b)).mpr h2)

/-! ## Finite Sum Lemmas (`sumFinNat` and `sumFinRat`) -/

theorem sumFinNat_const (n c : Nat) : sumFinNat (fun _ : Fin n => c) = n * c := by
  induction n with
  | zero => simp [sumFinNat]
  | succ n ih =>
    simp [sumFinNat, ih, Nat.succ_mul]

theorem sumFinNat_add {n : Nat} (f g : Fin n → Nat) :
    sumFinNat (fun i => f i + g i) = sumFinNat f + sumFinNat g := by
  induction n with
  | zero => simp [sumFinNat]
  | succ n ih =>
    simp only [sumFinNat]
    rw [ih]
    omega

theorem sumFinNat_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    sumFinNat f ≤ sumFinNat g := by
  induction n with
  | zero => simp [sumFinNat]
  | succ n ih =>
    simp only [sumFinNat]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem sumFinNat_split_bool {n : Nat} (S : Fin n → Bool) (f : Fin n → Nat) :
    sumFinNat f = sumFinNatSubset S f + sumFinNatSubset (fun i => !S i) f := by
  induction n with
  | zero => simp [sumFinNat, sumFinNatSubset]
  | succ n ih =>
    simp only [sumFinNat, sumFinNatSubset]
    have hih := ih (fun i => S i.castSucc) (fun i => f i.castSucc)
    simp only [sumFinNatSubset] at hih
    have hlast :
        (if S (Fin.last n) = true then f (Fin.last n) else 0) +
        (if (!S (Fin.last n)) = true then f (Fin.last n) else 0) = f (Fin.last n) := by
      cases S (Fin.last n) <;> simp
    omega

theorem countBool_add_not {n : Nat} (S : Fin n → Bool) :
    countBool S + countBool (fun i => !S i) = n := by
  unfold countBool
  have h := sumFinNat_split_bool S (fun _ : Fin n => 1)
  simp only [sumFinNat_const, Nat.mul_one, sumFinNatSubset] at h
  exact h.symm

theorem sumFinNat_ite_lt (n r a b : Nat) (hr : r ≤ n) :
    sumFinNat (fun i : Fin n => if i.val < r then a else b) = r * a + (n - r) * b := by
  induction n with
  | zero =>
    have : r = 0 := by omega
    subst this; simp [sumFinNat]
  | succ n ih =>
    simp only [sumFinNat, Fin.val_castSucc, Fin.val_last]
    by_cases h : r ≤ n
    · have hih := ih h
      have hnot : ¬ (n < r) := by omega
      simp [hnot, hih]
      have : n + 1 - r = (n - r) + 1 := by omega
      rw [this, Nat.succ_mul]
      omega
    · have hrn : r = n + 1 := by omega
      subst hrn
      have hlt : n < n + 1 := by omega
      have hconst : (fun i : Fin n => if i.val < n + 1 then a else b) = (fun _ : Fin n => a) := by
        funext i
        have hi : i.val < n + 1 := by omega
        simp [hi]
      simp [hlt, hconst, sumFinNat_const, Nat.succ_mul]

theorem sumFinRat_const (n : Nat) (c : Rat) : sumFinRat (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih =>
    simp only [sumFinRat, ih]
    rw [rat_natCast_add, Rat.add_mul]
    simp

theorem sumFinRat_add {n : Nat} (f g : Fin n → Rat) :
    sumFinRat (fun i => f i + g i) = sumFinRat f + sumFinRat g := by
  induction n with
  | zero => simp [sumFinRat, Rat.add_zero]
  | succ n ih =>
    simp only [sumFinRat, ih]
    rw [Rat.add_assoc, ← Rat.add_assoc (sumFinRat fun i => g i.castSucc),
        Rat.add_comm (sumFinRat fun i => g i.castSucc) (f (Fin.last n)),
        Rat.add_assoc, Rat.add_assoc]

theorem sumFinRat_sub {n : Nat} (f g : Fin n → Rat) :
    sumFinRat (fun i => f i - g i) = sumFinRat f - sumFinRat g := by
  induction n with
  | zero => simp [sumFinRat, Rat.sub_eq_add_neg, Rat.add_zero]
  | succ n ih =>
    simp only [sumFinRat, ih]
    simp only [Rat.sub_eq_add_neg, Rat.neg_add]
    rw [Rat.add_assoc, ← Rat.add_assoc (-sumFinRat fun i => g i.castSucc),
        Rat.add_comm (-sumFinRat fun i => g i.castSucc) (f (Fin.last n)),
        Rat.add_assoc, Rat.add_assoc]

theorem sumFinRat_neg {n : Nat} (f : Fin n → Rat) :
    sumFinRat (fun i => -f i) = -sumFinRat f := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih => simp only [sumFinRat, ih, Rat.neg_add]

theorem sumFinRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumFinRat (fun i => c * f i) = c * sumFinRat f := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih =>
    simp only [sumFinRat, ih, Rat.mul_add]

theorem sumFinRat_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumFinRat (fun i => f i * c) = sumFinRat f * c := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih =>
    simp only [sumFinRat, ih, Rat.add_mul]

theorem sumFinRat_natCast {n : Nat} (f : Fin n → Nat) :
    sumFinRat (fun i => (f i : Rat)) = (sumFinNat f : Rat) := by
  induction n with
  | zero => simp [sumFinRat, sumFinNat]
  | succ n ih =>
    simp only [sumFinRat, sumFinNat, ih, rat_natCast_add]

theorem sumFinRat_le {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    sumFinRat f ≤ sumFinRat g := by
  induction n with
  | zero => simp [sumFinRat]
  | succ n ih =>
    simp only [sumFinRat]
    exact rat_add_le_add (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem sumFinRat_lt_of_le_of_exists_lt {n : Nat} {f g : Fin n → Rat}
    (hle : ∀ i, f i ≤ g i) (hlt : ∃ i, f i < g i) :
    sumFinRat f < sumFinRat g := by
  induction n with
  | zero =>
    rcases hlt with ⟨i, _⟩
    exact Fin.elim0 i
  | succ n ih =>
    simp only [sumFinRat]
    rcases hlt with ⟨i, hi⟩
    refine Fin.lastCases (motive := fun k => f k < g k → _) ?_ ?_ i hi
    · intro hlast
      exact rat_add_lt_add_of_le_of_lt (sumFinRat_le (fun j => hle j.castSucc)) hlast
    · intro j hj
      exact rat_add_lt_add_of_lt_of_le (ih (fun k => hle k.castSucc) ⟨j, hj⟩) (hle (Fin.last n))

theorem sumFinRat_le_with_one_small {n : Nat} {f : Fin n → Rat} {u v : Rat}
    (hle : ∀ i, f i ≤ u) (hex : ∃ j, f j ≤ v) :
    sumFinRat f + u ≤ (n : Rat) * u + v := by
  induction n with
  | zero =>
    rcases hex with ⟨j, _⟩
    exact Fin.elim0 j
  | succ n ih =>
    simp only [sumFinRat]
    rw [rat_natCast_add, Rat.add_mul]
    have h1u : ((1 : Nat) : Rat) * u = u := by simp
    rw [h1u]
    rcases hex with ⟨j, hj⟩
    refine Fin.lastCases (motive := fun k => f k ≤ v → _) ?_ ?_ j hj
    · intro hlast
      have h1 : sumFinRat (fun i : Fin n => f i.castSucc) ≤ (n : Rat) * u := by
        rw [← sumFinRat_const n u]
        exact sumFinRat_le (fun i => hle i.castSucc)
      have h2 := rat_add_le_add (rat_add_le_add h1 hlast) (rat_le_refl u)
      simpa [Rat.add_assoc, Rat.add_comm u v] using h2
    · intro k hk
      have h1 := ih (fun i => hle i.castSucc) ⟨k, hk⟩
      have h2 := hle (Fin.last n)
      have h3 := rat_add_le_add h1 h2
      have hl : (sumFinRat (fun i : Fin n => f i.castSucc) + f (Fin.last n)) + u =
          (sumFinRat (fun i : Fin n => f i.castSucc) + u) + f (Fin.last n) := by
        rw [Rat.add_assoc, Rat.add_comm (f (Fin.last n)) u, ← Rat.add_assoc]
      have hr : ((n : Rat) * u + u) + v = ((n : Rat) * u + v) + u := by
        rw [Rat.add_assoc, Rat.add_comm u v, ← Rat.add_assoc]
      rw [hl, hr]
      exact h3

theorem sumFinRat_ge_with_one_large {n : Nat} {f : Fin n → Rat} {l v : Rat}
    (hge : ∀ i, l ≤ f i) (hex : ∃ j, v ≤ f j) :
    (n : Rat) * l + v ≤ sumFinRat f + l := by
  have h1 := sumFinRat_le_with_one_small (f := fun i => -f i) (u := -l) (v := -v)
    (fun i => (rat_neg_le_neg_iff (f i) l).mpr (hge i))
    (by
      rcases hex with ⟨j, hj⟩
      exact ⟨j, (rat_neg_le_neg_iff (f j) v).mpr hj⟩)
  rw [sumFinRat_neg, Rat.mul_neg] at h1
  rw [← Rat.neg_add, ← Rat.neg_add] at h1
  exact (rat_neg_le_neg_iff _ _).mp h1

end MoeBiasPlacement
