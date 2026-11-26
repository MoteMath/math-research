/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RagPopcntMatryoshka.Defs

/-!
# Pure-`Init` `Rat`, `Int`, and `Fin n` Sum Helpers

Zero Mathlib, zero `native_decide`.
-/

namespace RagPopcntMatryoshka

/-! ## Basic `Rat` order and algebra helpers -/

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

theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  have hle : a ≤ c := Rat.le_trans h1 (Rat.le_of_lt h2)
  have hne : a ≠ c := by
    intro heq
    subst heq
    exact Rat.not_le.mpr h2 h1
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have hle : a ≤ c := Rat.le_trans (Rat.le_of_lt h1) h2
  have hne : a ≠ c := by
    intro heq
    subst heq
    exact Rat.not_le.mpr h1 h2
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  rat_lt_of_lt_of_le h1 (Rat.le_of_lt h2)

theorem rat_mul_right_cancel {a b c : Rat} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have h1 : (a * c) * c⁻¹ = (b * c) * c⁻¹ := congrArg (· * c⁻¹) h
  rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_inv_cancel c hc, Rat.mul_one, Rat.mul_one] at h1
  exact h1

theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) :
    a + c < b + d := by
  have h3 : a + c ≤ b + c := (Rat.add_le_add_right (c := c)).mpr h1
  have h4 : b + c < b + d := by
    apply rat_lt_of_sub_pos
    have eq : (b + d) - (b + c) = d - c := by grind
    rw [eq]; exact rat_sub_pos h2
  exact rat_lt_of_le_of_lt h3 h4

theorem rat_add_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) ≤ a + b := by
  have h := rat_add_le_add ha hb
  have h0 : (0 : Rat) + 0 = 0 := by grind
  rw [h0] at h
  exact h

theorem rat_add_pos_of_pos_of_nonneg {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) < a + b := by
  have h := rat_add_lt_add_of_le_of_lt hb ha
  have h0 : (0 : Rat) + 0 = 0 := by grind
  rw [h0, Rat.add_comm b a] at h
  exact h

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

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < a⁻¹ := by
  by_cases h : (0 : Rat) < a⁻¹
  · exact h
  · have hle0 : a⁻¹ ≤ 0 := Rat.not_lt.mp h
    have hle : a * a⁻¹ ≤ 0 := by
      have h1 := rat_mul_le_mul_of_nonneg_left hle0 (Rat.le_of_lt ha)
      have h0 : a * 0 = 0 := by grind
      rw [h0] at h1
      exact h1
    have hne : a ≠ 0 := Rat.ne_of_gt ha
    have h1 : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hne
    rw [h1] at hle
    exact False.elim (Rat.not_le.mpr (by decide : (0 : Rat) < 1) hle)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_div_lt_iff {a b c : Rat} (hb : (0 : Rat) < b) :
    a / b < c ↔ a < c * b := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hb
    have eq : (a / b) * b = a := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hbne, Rat.mul_one]
    rw [eq] at h1
    exact h1
  · intro h
    have hinv : (0 : Rat) < b⁻¹ := rat_inv_pos hb
    have h1 := rat_mul_lt_mul_of_pos_right h hinv
    have eq : (c * b) * b⁻¹ = c := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel b hbne, Rat.mul_one]
    rw [eq, ← Rat.div_def] at h1
    exact h1

theorem rat_lt_div_iff {a b c : Rat} (hb : (0 : Rat) < b) :
    c < a / b ↔ c * b < a := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  constructor
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hb
    have eq : (a / b) * b = a := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hbne, Rat.mul_one]
    rw [eq] at h1
    exact h1
  · intro h
    have hinv : (0 : Rat) < b⁻¹ := rat_inv_pos hb
    have h1 := rat_mul_lt_mul_of_pos_right h hinv
    have eq : (c * b) * b⁻¹ = c := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel b hbne, Rat.mul_one]
    rw [eq, ← Rat.div_def] at h1
    exact h1

theorem rat_div_le_iff {a b c : Rat} (hb : (0 : Rat) < b) :
    a / b ≤ c ↔ a ≤ c * b := by
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hb)
    have eq : (a / b) * b = a := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hbne, Rat.mul_one]
    rw [eq] at h1
    exact h1
  · intro h
    have hinv : (0 : Rat) ≤ b⁻¹ := Rat.le_of_lt (rat_inv_pos hb)
    have h1 := rat_mul_le_mul_of_nonneg_right h hinv
    have eq : (c * b) * b⁻¹ = c := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel b hbne, Rat.mul_one]
    rw [eq, ← Rat.div_def] at h1
    exact h1

theorem rat_div_lt_div_of_cross {a b c d : Rat} (hb : (0 : Rat) < b) (hd : (0 : Rat) < d)
    (h : a * d < c * b) : a / b < c / d := by
  rw [rat_div_lt_iff hb]
  have h1 := rat_mul_lt_mul_of_pos_right h (rat_inv_pos hd)
  have h2 : (a * d) * d⁻¹ = a := by
    rw [Rat.mul_assoc, Rat.mul_inv_cancel d (Rat.ne_of_gt hd), Rat.mul_one]
  have h3 : (c * b) * d⁻¹ = (c / d) * b := by
    rw [Rat.div_def]; grind
  rw [h2, h3] at h1
  exact h1

/-! ## `ratAbs` helpers -/

theorem ratAbs_nonneg (x : Rat) : (0 : Rat) ≤ ratAbs x := by
  unfold ratAbs
  split
  · assumption
  · rename_i h
    exact rat_neg_nonneg_of_nonpos (Rat.le_of_lt (Rat.not_le.mp h))

theorem le_ratAbs (x : Rat) : x ≤ ratAbs x := by
  unfold ratAbs
  split
  · exact Rat.le_refl
  · rename_i h
    have hlt : x < 0 := Rat.not_le.mp h
    have hneg : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos (Rat.le_of_lt hlt)
    exact Rat.le_trans (Rat.le_of_lt hlt) hneg

theorem neg_le_ratAbs (x : Rat) : -x ≤ ratAbs x := by
  unfold ratAbs
  split
  · rename_i h
    have hneg : -x ≤ 0 := by
      have := rat_sub_nonneg h
      grind
    exact Rat.le_trans hneg h
  · exact Rat.le_refl

theorem ratAbs_le_iff {x b : Rat} : ratAbs x ≤ b ↔ -b ≤ x ∧ x ≤ b := by
  unfold ratAbs
  split
  · rename_i hx
    constructor
    · intro h
      refine ⟨?_, h⟩
      have hb : (0 : Rat) ≤ b := Rat.le_trans hx h
      have hnb : -b ≤ 0 := by
        have := rat_sub_nonneg hb
        grind
      exact Rat.le_trans hnb hx
    · intro ⟨_, h⟩; exact h
  · rename_i hx
    have hlt : x < 0 := Rat.not_le.mp hx
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := rat_sub_nonneg h
        grind
      · have hb : (0 : Rat) ≤ b := Rat.le_trans (rat_neg_nonneg_of_nonpos (Rat.le_of_lt hlt)) h
        exact Rat.le_trans (Rat.le_of_lt hlt) hb
    · intro ⟨h1, _⟩
      have := rat_sub_nonneg h1
      grind

theorem ratAbs_add_le (x y : Rat) : ratAbs (x + y) ≤ ratAbs x + ratAbs y := by
  rw [ratAbs_le_iff]
  have hx1 := le_ratAbs x
  have hx2 := neg_le_ratAbs x
  have hy1 := le_ratAbs y
  have hy2 := neg_le_ratAbs y
  constructor
  · have h := rat_add_le_add hx2 hy2
    have eq1 : -(ratAbs x + ratAbs y) ≤ x + y := by
      have := rat_sub_nonneg h
      apply rat_le_of_sub_nonneg
      have e : (x + y) - (-(ratAbs x + ratAbs y)) = (ratAbs x + ratAbs y) - (-x + -y) := by grind
      rw [e]; exact this
    exact eq1
  · exact rat_add_le_add hx1 hy1

theorem ratAbs_mul (x y : Rat) : ratAbs (x * y) = ratAbs x * ratAbs y := by
  unfold ratAbs
  by_cases hx : (0 : Rat) ≤ x <;> by_cases hy : (0 : Rat) ≤ y
  · have hxy : (0 : Rat) ≤ x * y := Rat.mul_nonneg hx hy
    simp [hx, hy, hxy]
  · have hyn : y < 0 := Rat.not_le.mp hy
    have hny : (0 : Rat) ≤ -y := rat_neg_nonneg_of_nonpos (Rat.le_of_lt hyn)
    by_cases hx0 : x = 0
    · subst hx0; simp
    · have hxp : (0 : Rat) < x := Rat.lt_of_le_of_ne hx (Ne.symm hx0)
      have hneg : (0 : Rat) < x * (-y) := rat_mul_pos hxp (rat_sub_pos hyn |> fun h => by
        have e : (0 : Rat) - y = -y := by grind
        rw [← e]; exact h)
      have hxy_neg : ¬((0 : Rat) ≤ x * y) := by
        intro hle
        have hsum := rat_add_pos_of_pos_of_nonneg hneg hle
        have e : x * (-y) + x * y = 0 := by grind
        rw [e] at hsum
        exact Rat.lt_irrefl hsum
      simp only [hx, hy, hxy_neg, ↓reduceIte]
      grind
  · have hxn : x < 0 := Rat.not_le.mp hx
    by_cases hy0 : y = 0
    · subst hy0; simp
    · have hyp : (0 : Rat) < y := Rat.lt_of_le_of_ne hy (Ne.symm hy0)
      have hneg : (0 : Rat) < (-x) * y := rat_mul_pos (rat_sub_pos hxn |> fun h => by
        have e : (0 : Rat) - x = -x := by grind
        rw [← e]; exact h) hyp
      have hxy_neg : ¬((0 : Rat) ≤ x * y) := by
        intro hle
        have hsum := rat_add_pos_of_pos_of_nonneg hneg hle
        have e : (-x) * y + x * y = 0 := by grind
        rw [e] at hsum
        exact Rat.lt_irrefl hsum
      simp only [hx, hy, hxy_neg, ↓reduceIte]
      grind
  · have hxn : x < 0 := Rat.not_le.mp hx
    have hyn : y < 0 := Rat.not_le.mp hy
    have hnx : (0 : Rat) ≤ -x := rat_neg_nonneg_of_nonpos (Rat.le_of_lt hxn)
    have hny : (0 : Rat) ≤ -y := rat_neg_nonneg_of_nonpos (Rat.le_of_lt hyn)
    have hxy : (0 : Rat) ≤ x * y := by
      have eq : x * y = (-x) * (-y) := by grind
      rw [eq]; exact Rat.mul_nonneg hnx hny
    simp only [hx, hy, hxy, ↓reduceIte]
    grind

/-! ## `finSumNat`, `finSumInt`, and `finSumRat` lemmas -/

theorem finSumNat_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    finSumNat f = finSumNat g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSumNat, h (Fin.last n)]
    rw [ih (fun i => h i.castSucc)]

theorem finSumInt_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSumInt f = finSumInt g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSumInt, h (Fin.last n)]
    rw [ih (fun i => h i.castSucc)]

theorem finSumRat_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    finSumRat f = finSumRat g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSumRat, h (Fin.last n)]
    rw [ih (fun i => h i.castSucc)]

theorem finSumInt_add {n : Nat} (f g : Fin n → Int) :
    finSumInt (fun i => f i + g i) = finSumInt f + finSumInt g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSumInt]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem finSumInt_sub {n : Nat} (f g : Fin n → Int) :
    finSumInt (fun i => f i - g i) = finSumInt f - finSumInt g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSumInt]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem finSumInt_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    finSumInt (fun i => c * f i) = c * finSumInt f := by
  induction n with
  | zero => simp [finSumInt]
  | succ n ih =>
    simp only [finSumInt]
    rw [ih (fun i => f i.castSucc), Int.mul_add]

theorem finSumInt_const {n : Nat} (c : Int) :
    finSumInt (fun _ : Fin n => c) = (n : Int) * c := by
  induction n with
  | zero => simp [finSumInt]
  | succ n ih =>
    simp only [finSumInt]
    rw [ih]
    grind

theorem finSumInt_ofNat {n : Nat} (f : Fin n → Nat) :
    (finSumNat f : Int) = finSumInt (fun i => (f i : Int)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSumNat, finSumInt, Int.natCast_add]
    rw [ih (fun i => f i.castSucc)]

theorem finSumInt_le_finSumInt {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    finSumInt f ≤ finSumInt g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [finSumInt]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem finSumInt_split {a b : Nat} (f : Fin (a + b) → Int) :
    finSumInt f = finSumInt (leftBlock f) + finSumInt (rightBlock f) := by
  induction b with
  | zero =>
    simp only [finSumInt, Int.add_zero]
    exact finSumInt_congr (fun i => by simp [leftBlock])
  | succ b ih =>
    change finSumInt (fun i : Fin (a + b) => f i.castSucc) + f (Fin.last (a + b)) =
      finSumInt (leftBlock f) + (finSumInt (fun i : Fin b => rightBlock f i.castSucc) + rightBlock f (Fin.last b))
    have hleft : leftBlock (fun i : Fin (a + b) => f i.castSucc) = leftBlock f := by
      funext i; rfl
    have hright : rightBlock (fun i : Fin (a + b) => f i.castSucc) =
        fun i : Fin b => rightBlock f i.castSucc := by
      funext i; rfl
    have hlast : f (Fin.last (a + b)) = rightBlock f (Fin.last b) := rfl
    rw [ih (fun i : Fin (a + b) => f i.castSucc), hleft, hright, hlast, Int.add_assoc]

theorem finSumRat_add {n : Nat} (f g : Fin n → Rat) :
    finSumRat (fun i => f i + g i) = finSumRat f + finSumRat g := by
  induction n with
  | zero => simp [finSumRat]; grind
  | succ n ih =>
    simp only [finSumRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem finSumRat_sub {n : Nat} (f g : Fin n → Rat) :
    finSumRat (fun i => f i - g i) = finSumRat f - finSumRat g := by
  induction n with
  | zero => simp [finSumRat]; grind
  | succ n ih =>
    simp only [finSumRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem finSumRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    finSumRat (fun i => c * f i) = c * finSumRat f := by
  induction n with
  | zero => simp [finSumRat]
  | succ n ih =>
    simp only [finSumRat]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem finSumRat_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    finSumRat (fun i => f i * c) = finSumRat f * c := by
  induction n with
  | zero => simp [finSumRat]
  | succ n ih =>
    simp only [finSumRat]
    rw [ih (fun i => f i.castSucc)]
    grind

theorem finSumRat_const {n : Nat} (c : Rat) :
    finSumRat (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [finSumRat]
  | succ n ih =>
    simp only [finSumRat]
    rw [ih]
    grind

theorem finSumRat_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ i, (0 : Rat) ≤ f i) :
    (0 : Rat) ≤ finSumRat f := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [finSumRat]
    exact rat_add_nonneg (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem finSumRat_pos {n : Nat} {f : Fin n → Rat} (hn : 0 < n) (h : ∀ i, (0 : Rat) < f i) :
    (0 : Rat) < finSumRat f := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [finSumRat]
    have h1 : (0 : Rat) ≤ finSumRat (fun i : Fin m => f i.castSucc) :=
      finSumRat_nonneg (fun i => Rat.le_of_lt (h i.castSucc))
    have h2 : (0 : Rat) < f (Fin.last m) := h (Fin.last m)
    rw [Rat.add_comm]
    exact rat_add_pos_of_pos_of_nonneg h2 h1

theorem finSumRat_le_finSumRat {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    finSumRat f ≤ finSumRat g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    simp only [finSumRat]
    exact rat_add_le_add (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem finSumRat_lt_finSumRat {n : Nat} {f g : Fin n → Rat} (hn : 0 < n)
    (h : ∀ i, f i < g i) : finSumRat f < finSumRat g := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [finSumRat]
    exact rat_add_lt_add_of_le_of_lt
      (finSumRat_le_finSumRat (fun i => Rat.le_of_lt (h i.castSucc)))
      (h (Fin.last m))

theorem ratAbs_finSumRat_le {n : Nat} (f : Fin n → Rat) :
    ratAbs (finSumRat f) ≤ finSumRat (fun i => ratAbs (f i)) := by
  induction n with
  | zero =>
    simp only [finSumRat, ratAbs]
    exact Rat.le_refl
  | succ n ih =>
    simp only [finSumRat]
    exact Rat.le_trans (ratAbs_add_le _ _)
      (rat_add_le_add (ih (fun i => f i.castSucc)) Rat.le_refl)

theorem finSumRat_split {a b : Nat} (f : Fin (a + b) → Rat) :
    finSumRat f = finSumRat (leftBlock f) + finSumRat (rightBlock f) := by
  induction b with
  | zero =>
    simp only [finSumRat, Rat.add_zero]
    exact finSumRat_congr (fun i => by simp [leftBlock])
  | succ b ih =>
    change finSumRat (fun i : Fin (a + b) => f i.castSucc) + f (Fin.last (a + b)) =
      finSumRat (leftBlock f) + (finSumRat (fun i : Fin b => rightBlock f i.castSucc) + rightBlock f (Fin.last b))
    have hleft : leftBlock (fun i : Fin (a + b) => f i.castSucc) = leftBlock f := by
      funext i; rfl
    have hright : rightBlock (fun i : Fin (a + b) => f i.castSucc) =
        fun i : Fin b => rightBlock f i.castSucc := by
      funext i; rfl
    have hlast : f (Fin.last (a + b)) = rightBlock f (Fin.last b) := rfl
    rw [ih (fun i : Fin (a + b) => f i.castSucc), hleft, hright, hlast, Rat.add_assoc]

theorem finSumRat_cast {m n : Nat} (heq : m = n) (f : Fin n → Rat) :
    finSumRat f = finSumRat (fun i : Fin m => f ⟨i.val, heq ▸ i.isLt⟩) := by
  subst heq
  rfl

theorem finSumRat_split_le {D dM : Nat} (h : dM ≤ D) (f : Fin D → Rat) :
    finSumRat f =
      finSumRat (fun i : Fin dM => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩) +
      finSumRat (fun i : Fin (D - dM) => f ⟨dM + i.val, by omega⟩) := by
  have heq : dM + (D - dM) = D := Nat.add_sub_of_le h
  rw [finSumRat_cast heq f, finSumRat_split]
  rfl

theorem finSumRat_mul_finSumRat {m n : Nat} (f : Fin m → Rat) (g : Fin n → Rat) :
    finSumRat f * finSumRat g = finSumRat (fun i : Fin m => finSumRat (fun j : Fin n => f i * g j)) := by
  have h1 : ∀ i : Fin m, finSumRat (fun j : Fin n => f i * g j) = f i * finSumRat g :=
    fun i => finSumRat_mul_left (f i) g
  rw [finSumRat_congr h1, finSumRat_mul_right]

end RagPopcntMatryoshka
