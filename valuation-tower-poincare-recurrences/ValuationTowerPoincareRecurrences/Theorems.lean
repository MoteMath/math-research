/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ValuationTowerPoincareRecurrences.Defs

/-!
# Theorems (`ValuationTowerPoincareRecurrences`)

# 2-Adic Valuation-Tower Poincaré Reduction (VTPR)
## A Pure-Silicon Infinite Proof Mechanism for Multi-Dimensional Bitwise Periodic Recurrences

Standalone Lean 4.34.1 formalization (zero Mathlib, zero `sorry`, standard axioms only).
-/


namespace VTPR
/-- Halving projection `BitVec (w + 1) → BitVec w` (`x ↦ x / 2`). -/
def halfBV {w : Nat} (x : BitVec (w + 1)) : BitVec w :=
  BitVec.ofNat w (x.toNat / 2)

/-- Low-`w`-bit truncation `BitVec (w + 1) → BitVec w`. -/
def trunc1 {w : Nat} (x : BitVec (w + 1)) : BitVec w :=
  BitVec.ofNat w x.toNat

theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

theorem iter_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = iter f n (f x) := rfl

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f b (iter f a x) := by
  induction a generalizing x with
  | zero => simp [iter]
  | succ a ih =>
    rw [Nat.succ_add, iter_succ, ih]
    rfl

theorem iter_succ_right {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = f (iter f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih]; rfl

theorem iter_mul {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a * b) x = iter (iter f a) b x := by
  induction b generalizing x with
  | zero => simp [iter]
  | succ b ih =>
    rw [Nat.mul_succ, Nat.add_comm, iter_add, iter_succ, ih]

theorem iter_fixed_mul {α : Type} (f : α → α) {p : Nat} {x : α}
    (h : iter f p x = x) (k : Nat) : iter f (p * k) x = x := by
  rw [iter_mul]
  induction k with
  | zero => rfl
  | succ k ih => rw [iter_succ, h, ih]

theorem iter_fixed_of_dvd {α : Type} (f : α → α) {p q : Nat} {x : α}
    (h : iter f p x = x) (hdvd : p ∣ q) : iter f q x = x := by
  rcases hdvd with ⟨k, rfl⟩
  exact iter_fixed_mul f h k

theorem iter_conj {α β : Type} (f : α → α) (g : β → β) (φ : α → β)
    (h : ∀ x, φ (f x) = g (φ x)) (n : Nat) (x : α) :
    φ (iter f n x) = iter g n (φ x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iter_succ, iter_succ, ih, h]

theorem iter_comm {α : Type} (f : α → α) (n k : Nat) (x : α) :
    iter f n (iter f k x) = iter f k (iter f n x) := by
  rw [← iter_add, Nat.add_comm, iter_add]

theorem iter_injective {α : Type} {f : α → α} (hinj : ∀ x y, f x = f y → x = y)
    (n : Nat) : ∀ x y, iter f n x = iter f n y → x = y := by
  induction n with
  | zero => intro x y h; exact h
  | succ n ih =>
    intro x y h
    rw [iter_succ, iter_succ] at h
    exact hinj x y (ih _ _ h)

/-! ### Bit-level `BitVec` Arithmetic Lemmas -/

theorem toNat_shift2 {w : Nat} (x : BitVec w) : (shift2 x).toNat = 2 * x.toNat := by
  simp only [shift2, BitVec.toNat_ofNat]
  have hx : x.toNat < 2 ^ w := x.isLt
  have h2 : 2 * x.toNat < 2 ^ (w + 1) := by
    rw [Nat.pow_succ]; omega
  exact Nat.mod_eq_of_lt h2

theorem toNat_halfBV {w : Nat} (x : BitVec (w + 1)) : (halfBV x).toNat = x.toNat / 2 := by
  simp only [halfBV, BitVec.toNat_ofNat]
  have hx : x.toNat < 2 ^ (w + 1) := x.isLt
  have h2 : x.toNat / 2 < 2 ^ w := by
    rw [Nat.pow_succ] at hx; omega
  exact Nat.mod_eq_of_lt h2

theorem toNat_trunc1 {w : Nat} (x : BitVec (w + 1)) : (trunc1 x).toNat = x.toNat % 2 ^ w := by
  simp [trunc1]

theorem shift2_injective {w : Nat} {x y : BitVec w} (h : shift2 x = shift2 y) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  rw [toNat_shift2, toNat_shift2] at this
  omega

theorem getLsbD_zero_iff_mod2 {w : Nat} (x : BitVec w) :
    x.getLsbD 0 = true ↔ x.toNat % 2 = 1 := by
  simp [BitVec.getLsbD, Nat.testBit_zero]

theorem getLsbD_zero_false_iff_mod2 {w : Nat} (x : BitVec w) :
    x.getLsbD 0 = false ↔ x.toNat % 2 = 0 := by
  have h := getLsbD_zero_iff_mod2 x
  cases hb : x.getLsbD 0
  · simp only [hb, Bool.false_eq_true, false_iff] at h
    simp only [true_iff]; omega
  · simp only [hb, true_iff] at h
    simp only [Bool.true_eq_false, false_iff]; omega

theorem getLsbD_ge_width {w : Nat} (x : BitVec w) (k : Nat) (hk : w ≤ k) :
    x.getLsbD k = false := by
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hlt : x.toNat < 2 ^ k := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hk)
  rw [Nat.div_eq_of_lt hlt]
  rfl

theorem shift2_halfBV {w : Nat} {x : BitVec (w + 1)} (h0 : x.getLsbD 0 = false) :
    shift2 (halfBV x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shift2, toNat_halfBV]
  have hm : x.toNat % 2 = 0 := (getLsbD_zero_false_iff_mod2 x).mp h0
  omega

theorem getLsbD_shift2_zero {w : Nat} (x : BitVec w) : (shift2 x).getLsbD 0 = false := by
  rw [getLsbD_zero_false_iff_mod2, toNat_shift2]
  omega

theorem getLsbD_shift2_succ {w : Nat} (x : BitVec w) (k : Nat) :
    (shift2 x).getLsbD (k + 1) = x.getLsbD k := by
  simp only [BitVec.getLsbD, toNat_shift2, Nat.testBit_succ]
  congr 1
  omega

theorem shift2_zero {w : Nat} : shift2 (0#w) = 0#(w + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [toNat_shift2]

theorem shift2_add {w : Nat} (x y : BitVec w) :
    shift2 (x + y) = shift2 x + shift2 y := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shift2, BitVec.toNat_add, BitVec.toNat_add, toNat_shift2, toNat_shift2]
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, ← Nat.mul_add, Nat.mul_mod_mul_left]

theorem shift2_neg {w : Nat} (x : BitVec w) :
    shift2 (-x) = -(shift2 x) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shift2, BitVec.toNat_neg, BitVec.toNat_neg, toNat_shift2]
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2]
  have hx : x.toNat < 2 ^ w := x.isLt
  have h1 : 2 * (2 ^ w - x.toNat) = 2 * 2 ^ w - 2 * x.toNat := by omega
  rw [← h1, Nat.mul_mod_mul_left]

theorem shift2_sub {w : Nat} (x y : BitVec w) :
    shift2 (x - y) = shift2 x - shift2 y := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, shift2_add, shift2_neg]

theorem shift2_and {w : Nat} (x y : BitVec w) :
    shift2 (x &&& y) = shift2 x &&& shift2 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  cases k with
  | zero =>
    rw [BitVec.getLsbD_and, getLsbD_shift2_zero, getLsbD_shift2_zero, getLsbD_shift2_zero]
    rfl
  | succ k =>
    rw [BitVec.getLsbD_and, getLsbD_shift2_succ, getLsbD_shift2_succ, getLsbD_shift2_succ,
        BitVec.getLsbD_and]

theorem shift2_or {w : Nat} (x y : BitVec w) :
    shift2 (x ||| y) = shift2 x ||| shift2 y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  cases k with
  | zero =>
    rw [BitVec.getLsbD_or, getLsbD_shift2_zero, getLsbD_shift2_zero, getLsbD_shift2_zero]
    rfl
  | succ k =>
    rw [BitVec.getLsbD_or, getLsbD_shift2_succ, getLsbD_shift2_succ, getLsbD_shift2_succ,
        BitVec.getLsbD_or]

theorem shift2_lsb {w : Nat} (x : BitVec w) :
    shift2 (lsb x) = lsb (shift2 x) := by
  simp only [lsb, shift2_and, shift2_neg]

theorem shift2_mul_left {w : Nat} (c : BitVec (w + 1)) (x : BitVec w) :
    c * shift2 x = shift2 (trunc1 c * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, toNat_shift2, toNat_shift2, BitVec.toNat_mul, toNat_trunc1]
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2]
  have h1 : c.toNat * (2 * x.toNat) = 2 * (c.toNat * x.toNat) := by
    rw [Nat.mul_left_comm]
  rw [h1, Nat.mul_mod_mul_left, Nat.mod_mul_mod]

theorem getLsbD_trunc1_zero {w : Nat} (c : BitVec (w + 1)) (hw : 1 ≤ w) :
    (trunc1 c).getLsbD 0 = c.getLsbD 0 := by
  rw [Bool.eq_iff_iff, getLsbD_zero_iff_mod2, getLsbD_zero_iff_mod2, toNat_trunc1]
  have h2dvd : 2 ∣ 2 ^ w := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 (2 ^ w')
  rw [Nat.mod_mod_of_dvd c.toNat h2dvd]

theorem getLsbD_orVec {w n : Nat} (v : Fin n → BitVec w) (k : Nat) :
    (orVec v).getLsbD k = true ↔ ∃ i : Fin n, (v i).getLsbD k = true := by
  induction n with
  | zero =>
    simp [orVec]
  | succ n ih =>
    simp only [orVec, BitVec.getLsbD_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h0 | ⟨i, hi⟩)
      · exact ⟨0, h0⟩
      · exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact Or.inl hi
      | succ j => exact Or.inr ⟨j, hi⟩

theorem getLsbD_orVec_false {w n : Nat} (v : Fin n → BitVec w) (k : Nat) :
    (orVec v).getLsbD k = false ↔ ∀ i : Fin n, (v i).getLsbD k = false := by
  have h := getLsbD_orVec v k
  constructor
  · intro hf i
    cases hb : (v i).getLsbD k
    · rfl
    · have : (orVec v).getLsbD k = true := h.mpr ⟨i, hb⟩
      rw [hf] at this; cases this
  · intro hall
    cases hb : (orVec v).getLsbD k
    · rfl
    · rcases h.mp hb with ⟨i, hi⟩
      rw [hall i] at hi; cases hi

theorem shift2_orVec {w n : Nat} (v : Fin n → BitVec w) :
    shift2 (orVec v) = orVec (fun i => shift2 (v i)) := by
  induction n with
  | zero => simp [orVec, shift2_zero]
  | succ n ih =>
    simp only [orVec, shift2_or]
    rw [ih]

/-! ### Core `lsb` Identities (All Bit-Widths `w`) -/

theorem lsb_zero {w : Nat} : lsb (0#w) = 0#w := by
  simp [lsb]

theorem lsb_neg {w : Nat} (u : BitVec w) : lsb (-u) = lsb u := by
  simp only [lsb, BitVec.neg_neg, BitVec.and_comm]

theorem neg_getLsbD_zero {w : Nat} (x : BitVec w) :
    (-x).getLsbD 0 = x.getLsbD 0 := by
  cases w with
  | zero => simp
  | succ w =>
    rw [Bool.eq_iff_iff]
    simp only [getLsbD_zero_iff_mod2, BitVec.toNat_neg]
    have hx : x.toNat < 2 ^ (w + 1) := x.isLt
    have hpow : 2 ^ (w + 1) % 2 = 0 := by
      rw [Nat.pow_succ]; omega
    by_cases hx0 : x.toNat = 0
    · simp [hx0]
    · have hlt : 2 ^ (w + 1) - x.toNat < 2 ^ (w + 1) := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega

theorem add_getLsbD_zero {w : Nat} (x y : BitVec w) :
    (x + y).getLsbD 0 = (x.getLsbD 0 != y.getLsbD 0) := by
  cases w with
  | zero => simp
  | succ w =>
    rw [Bool.eq_iff_iff]
    have hpow : 2 ^ (w + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
    have h1 := getLsbD_zero_iff_mod2 x
    have h2 := getLsbD_zero_iff_mod2 y
    have h3 := getLsbD_zero_iff_mod2 (x + y)
    rw [BitVec.toNat_add] at h3
    cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;> simp_all <;> omega

theorem sub_getLsbD_zero {w : Nat} (x y : BitVec w) :
    (x - y).getLsbD 0 = (x.getLsbD 0 != y.getLsbD 0) := by
  rw [BitVec.sub_eq_add_neg, add_getLsbD_zero, neg_getLsbD_zero]

theorem neg_getLsbD_one_of_even {w : Nat} {x : BitVec w} (h0 : x.getLsbD 0 = false) :
    (-x).getLsbD 1 = x.getLsbD 1 := by
  cases w with
  | zero => simp
  | succ w =>
    rw [← shift2_halfBV h0, ← shift2_neg, getLsbD_shift2_succ, getLsbD_shift2_succ]
    exact neg_getLsbD_zero (halfBV x)

theorem add_getLsbD_one_of_even {w : Nat} {x y : BitVec w}
    (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false) :
    (x + y).getLsbD 1 = (x.getLsbD 1 != y.getLsbD 1) := by
  cases w with
  | zero => simp
  | succ w =>
    rw [← shift2_halfBV hx, ← shift2_halfBV hy, ← shift2_add]
    simp only [getLsbD_shift2_succ]
    exact add_getLsbD_zero (halfBV x) (halfBV y)

theorem sub_getLsbD_one_of_even {w : Nat} {x y : BitVec w}
    (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false) :
    (x - y).getLsbD 1 = (x.getLsbD 1 != y.getLsbD 1) := by
  rw [BitVec.sub_eq_add_neg, add_getLsbD_one_of_even hx (by rw [neg_getLsbD_zero]; exact hy),
      neg_getLsbD_one_of_even hy]

theorem two_mul_eq_shift2_trunc1 {w : Nat} (c : BitVec (w + 1)) :
    2#(w + 1) * c = shift2 (trunc1 c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, toNat_shift2, toNat_trunc1, BitVec.toNat_ofNat]
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2]
  cases w with
  | zero => simp [Nat.mod_one]
  | succ w =>
    have hp : 2 ≤ 2 ^ (w + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    have h2 : 2 % (2 * 2 ^ (w + 1)) = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h2, Nat.mul_mod_mul_left]

theorem two_mul_getLsbD_zero {w : Nat} (c : BitVec w) :
    (2#w * c).getLsbD 0 = false := by
  cases w with
  | zero => simp
  | succ w => rw [two_mul_eq_shift2_trunc1, getLsbD_shift2_zero]

theorem two_mul_getLsbD_one_of_odd {w : Nat} {c : BitVec w} (hc : c.getLsbD 0 = true)
    (hw : 2 ≤ w) : (2#w * c).getLsbD 1 = true := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rw [two_mul_eq_shift2_trunc1, getLsbD_shift2_succ]
  rw [getLsbD_trunc1_zero c (by omega), hc]

theorem lsb_eq_one_of_odd {w : Nat} {u : BitVec w} (h : u.getLsbD 0 = true) :
    lsb u = 1#w := by
  cases w with
  | zero => exact Subsingleton.elim _ _
  | succ w =>
    have hmod : u.toNat % 2 = 1 := (getLsbD_zero_iff_mod2 u).mp h
    have hne : u.toNat ≠ 0 := by omega
    have hneg_toNat : (-u).toNat = 2 ^ (w + 1) - u.toNat := by
      rw [BitVec.toNat_neg]
      exact Nat.mod_eq_of_lt (by omega)
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    cases k with
    | zero =>
      rw [lsb, BitVec.getLsbD_and, neg_getLsbD_zero, h]
      simp
    | succ k =>
      rw [lsb, BitVec.getLsbD_and]
      have h1_bit : (1#(w + 1)).getLsbD (k + 1) = false := by
        simp [BitVec.getLsbD, Nat.testBit_succ]
      rw [h1_bit]
      have hcomp : (-u).toNat = (~~~u).toNat + 1 := by
        rw [hneg_toNat, BitVec.toNat_not]
        have := u.isLt; omega
      have hnot_even : (~~~u).toNat % 2 = 0 := by
        have := u.isLt
        rw [BitVec.toNat_not]
        have hpow : 2 ^ (w + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
        omega
      have hdiv : (-u).toNat / 2 ^ (k + 1) = (~~~u).toNat / 2 ^ (k + 1) := by
        rw [hcomp, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
            ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        have hdiv2 : ((~~~u).toNat + 1) / 2 = (~~~u).toNat / 2 := by omega
        rw [hdiv2]
      have hneg_eq_not : (-u).getLsbD (k + 1) = (~~~u).getLsbD (k + 1) := by
        simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
      rw [hneg_eq_not, BitVec.getLsbD_not]
      simp only [hk, decide_true, Bool.true_and]
      cases u.getLsbD (k + 1) <;> rfl

theorem lsb_eq_two_of_val1 {w : Nat} {u : BitVec w}
    (h0 : u.getLsbD 0 = false) (h1 : u.getLsbD 1 = true) :
    lsb u = 2#w := by
  cases w with
  | zero => exact Subsingleton.elim _ _
  | succ w =>
    rw [← shift2_halfBV h0, ← shift2_lsb]
    have hv : (halfBV u).getLsbD 0 = true := by
      have := getLsbD_shift2_succ (halfBV u) 0
      rw [shift2_halfBV h0] at this
      rw [← this, h1]
    rw [lsb_eq_one_of_odd hv]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shift2]
    cases w with
    | zero =>
      have : u.getLsbD 1 = false := getLsbD_ge_width u 1 (by omega)
      rw [this] at h1; cases h1
    | succ w =>
      have hlt : 2 < 2 ^ (w + 2) := by
        have : 2 ^ 2 ≤ 2 ^ (w + 2) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hlt1 : 1 < 2 ^ (w + 1) := by
        have : 2 ^ 1 ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt1]

theorem lsb_div4 {w : Nat} {u : BitVec w}
    (h0 : u.getLsbD 0 = false) (h1 : u.getLsbD 1 = false) :
    (lsb u).getLsbD 0 = false ∧ (lsb u).getLsbD 1 = false := by
  simp only [lsb, BitVec.getLsbD_and, h0, h1, Bool.false_and, and_self]

theorem lsb_orVec_neg {w n : Nat} (v : Fin n → BitVec w) :
    lsb (orVec (fun i => -v i)) = lsb (orVec v) := by
  induction w with
  | zero => exact Subsingleton.elim _ _
  | succ w ih =>
    by_cases hodd : (orVec v).getLsbD 0 = true
    · rcases (getLsbD_orVec v 0).mp hodd with ⟨i, hi⟩
      have hodd' : (orVec (fun j => -v j)).getLsbD 0 = true :=
        (getLsbD_orVec (fun j => -v j) 0).mpr ⟨i, by rw [neg_getLsbD_zero]; exact hi⟩
      rw [lsb_eq_one_of_odd hodd, lsb_eq_one_of_odd hodd']
    · have hev : (orVec v).getLsbD 0 = false := by
        cases hb : (orVec v).getLsbD 0 <;> simp_all
      have hall : ∀ i, (v i).getLsbD 0 = false := (getLsbD_orVec_false v 0).mp hev
      let u : Fin n → BitVec w := fun i => halfBV (v i)
      have hv_eq : v = fun i => shift2 (u i) := by
        funext i; exact (shift2_halfBV (hall i)).symm
      have hneg_eq : (fun i => -v i) = fun i => shift2 (-u i) := by
        funext i; rw [hv_eq]; exact (shift2_neg (u i)).symm
      rw [hneg_eq, ← shift2_orVec, ← shift2_lsb, ih u]
      rw [hv_eq, ← shift2_orVec, ← shift2_lsb]

/-! ## Section 2: General `d`-Dimensional Subtraction Recurrence & Period Arithmetic -/

theorem fin_mk_eq {n a b : Nat} {ha : a < n} {hb : b < n} (h : a = b) :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := Fin.ext h

theorem bv_sub_sub_cancel {w : Nat} (a b : BitVec w) : a - (a - b) = b := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_sub, BitVec.add_comm, BitVec.add_comm (-a) b,
      BitVec.add_assoc, BitVec.add_comm (-a) a, BitVec.add_neg_eq_sub,
      BitVec.sub_self, BitVec.add_zero]

theorem bv_two_mul {w : Nat} (c : BitVec w) : 2#w * c = c + c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  cases w with
  | zero => simp [Nat.mod_one]
  | succ w =>
    cases w with
    | zero => simp; omega
    | succ w =>
      have hp : 2 < 2 ^ (w + 2) := by
        have : 2 ^ 2 ≤ 2 ^ (w + 2) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [Nat.mod_eq_of_lt hp, Nat.two_mul]

theorem bv_poincare_alg {w : Nat} (a b d : BitVec w) :
    a - (b - (a - d)) = ((2#w * a) - b) - d := by
  rw [bv_two_mul, BitVec.sub_eq_add_neg, BitVec.neg_sub, BitVec.sub_eq_add_neg,
      BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  ac_rfl

/-- Explicit inverse of `stepMap Φ` (proving bijectivity for ANY operator `Φ`). -/
def stepMapInv {m w : Nat} (Φ : (Fin (m + 1) → BitVec w) → BitVec w) (y : State m w) : State m w :=
  fun i =>
    if i.val = 0 then Φ (fun j => y ⟨j.val, by omega⟩) - y ⟨m + 1, by omega⟩
    else y ⟨i.val - 1, by omega⟩

theorem stepMap_left_inv {m w : Nat} (Φ : (Fin (m + 1) → BitVec w) → BitVec w) (x : State m w) :
    stepMapInv Φ (stepMap Φ x) = x := by
  funext i
  simp only [stepMapInv]
  split
  · rename_i hi0
    have htail : (fun j : Fin (m + 1) => stepMap Φ x ⟨j.val, by omega⟩) = tail x := by
      funext j
      simp only [stepMap, tail]
      have hj : j.val + 1 < m + 2 := by omega
      simp [hj, Fin.succ]
    have hlast : stepMap Φ x ⟨m + 1, by omega⟩ = Φ (tail x) - x 0 := by
      simp [stepMap]
    rw [htail, hlast]
    have hi : i = 0 := Fin.ext hi0
    rw [hi]
    exact bv_sub_sub_cancel (Φ (tail x)) (x 0)
  · rename_i hi0
    simp only [stepMap]
    have hlt : i.val - 1 + 1 < m + 2 := by omega
    simp only [hlt, dite_true]
    congr 1
    apply Fin.ext; dsimp only; omega

theorem stepMap_injective {m w : Nat} (Φ : (Fin (m + 1) → BitVec w) → BitVec w) :
    ∀ x y : State m w, stepMap Φ x = stepMap Φ y → x = y := by
  intro x y h
  have := congrArg (stepMapInv Φ) h
  rwa [stepMap_left_inv, stepMap_left_inv] at this

theorem QFactor_eq_lcm (d : Nat) : QFactor d = Nat.lcm (2 * d) (d + 1) := by
  have hgcd_dvd2 : Nat.gcd (2 * d) (d + 1) ∣ 2 := by
    have h1 : Nat.gcd (2 * d) (d + 1) ∣ 2 * d := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (2 * d) (d + 1) ∣ 2 * (d + 1) :=
      Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.dvd_mul_left (d + 1) 2)
    have hsub : 2 * (d + 1) - 2 * d = 2 := by omega
    have hd := Nat.dvd_sub h2 h1
    rwa [hsub] at hd
  unfold QFactor Nat.lcm
  by_cases hev : d % 2 = 0
  · simp only [hev, ite_true]
    have hodd : ¬ (2 ∣ d + 1) := by omega
    have hgcd1 : Nat.gcd (2 * d) (d + 1) = 1 := by
      have hle : Nat.gcd (2 * d) (d + 1) ≤ 2 := Nat.le_of_dvd (by decide) hgcd_dvd2
      have hpos : 0 < Nat.gcd (2 * d) (d + 1) := Nat.gcd_pos_of_pos_right _ (by omega)
      have hne2 : Nat.gcd (2 * d) (d + 1) ≠ 2 := by
        intro h2
        have := Nat.gcd_dvd_right (2 * d) (d + 1)
        rw [h2] at this
        exact hodd this
      omega
    rw [hgcd1, Nat.div_one]
  · simp only [hev, ite_false]
    have hdvd2 : 2 ∣ Nat.gcd (2 * d) (d + 1) :=
      Nat.dvd_gcd (Nat.dvd_mul_right 2 d) (by omega)
    have hgcd2 : Nat.gcd (2 * d) (d + 1) = 2 :=
      Nat.dvd_antisymm hgcd_dvd2 hdvd2
    rw [hgcd2]
    have hmul : 2 * d * (d + 1) = (d * (d + 1)) * 2 := by
      rw [Nat.mul_assoc, Nat.mul_comm 2 (d * (d + 1))]
    rw [hmul, Nat.mul_div_cancel _ (by decide)]

theorem QPeriod_eq_lcm (d : Nat) : QPeriod d = Nat.lcm (2 * d) (d + 1) * (2 * d - 1) := by
  rw [QPeriod, QFactor_eq_lcm]

theorem two_mul_dvd_QFactor (d : Nat) : 2 * d ∣ QFactor d := by
  unfold QFactor
  by_cases hev : d % 2 = 0
  · simp only [hev, ite_true]
    exact Nat.dvd_mul_right (2 * d) (d + 1)
  · simp only [hev, ite_false]
    refine ⟨(d + 1) / 2, ?_⟩
    have h2 : d + 1 = 2 * ((d + 1) / 2) := by omega
    calc d * (d + 1) = d * (2 * ((d + 1) / 2)) := by rw [← h2]
      _ = 2 * d * ((d + 1) / 2) := by rw [← Nat.mul_assoc, Nat.mul_comm d 2]

theorem two_mul_dvd_QPeriod (d : Nat) : 2 * d ∣ QPeriod d :=
  Nat.dvd_trans (two_mul_dvd_QFactor d) (Nat.dvd_mul_right _ _)

/-- A state vector is primitive if at least one coordinate is odd. -/
def isPrimitive {m w : Nat} (x : State m w) : Prop :=
  ∃ i : Fin (m + 2), (x i).getLsbD 0 = true

/-- Even-window Poincaré section `𝒮`: `x 0` is odd and `x 1, ..., x_{d-1}` are all even. -/
def inSection {m w : Nat} (x : State m w) : Prop :=
  (x 0).getLsbD 0 = true ∧ ∀ j : Fin (m + 1), (x j.succ).getLsbD 0 = false

/-- Linear signed cyclic shift `negShift` (Level-1 active regime). -/
def negShift {m w : Nat} (e : State m w) : State m w :=
  fun i =>
    if i.val = 0 then e ⟨m + 1, by omega⟩
    else if i.val = 1 then -e 0
    else e ⟨i.val - 1, by omega⟩

/-- Auxiliary helper: `Φ v` is even whenever all coordinates of `v` are even. -/
theorem ValuationTowerSpec.even_of_all_even {m w : Nat} {Φ c}
    (S : ValuationTowerSpec m w Φ c) {v : Fin (m + 1) → BitVec w}
    (hev : ∀ j : Fin (m + 1), (v j).getLsbD 0 = false) :
    (Φ v).getLsbD 0 = false := by
  by_cases h1 : ∃ j : Fin (m + 1), (v j).getLsbD 1 = true
  · rw [S.level1_val1 v hev h1]
    exact two_mul_getLsbD_zero c
  · have hdiv4 : ∀ j : Fin (m + 1), (v j).getLsbD 0 = false ∧ (v j).getLsbD 1 = false := by
      intro j
      refine ⟨hev j, ?_⟩
      cases hb : (v j).getLsbD 1
      · rfl
      · exfalso; exact h1 ⟨j, hb⟩
    exact (S.level2_div4 v hdiv4).1

/-- Primitivity is strictly conserved by `stepMap Φ`. -/
theorem ValuationTowerSpec.preserve_primitive {m w : Nat} {Φ c}
    (S : ValuationTowerSpec m w Φ c) {x : State m w}
    (hprim : isPrimitive x) : isPrimitive (stepMap Φ x) := by
  by_cases htail : ∃ j : Fin (m + 1), (x j.succ).getLsbD 0 = true
  · rcases htail with ⟨j, hj⟩
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    simp only [stepMap]
    have hlt : j.val + 1 < m + 2 := by omega
    simp only [hlt, dite_true]
    exact hj
  · have hev : ∀ j : Fin (m + 1), (x j.succ).getLsbD 0 = false := by
      intro j
      cases hb : (x j.succ).getLsbD 0
      · rfl
      · exfalso; exact htail ⟨j, hb⟩
    have hx0 : (x 0).getLsbD 0 = true := by
      rcases hprim with ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact hi
      | succ j => rw [hev j] at hi; cases hi
    have hΦev : (Φ (tail x)).getLsbD 0 = false := S.even_of_all_even hev
    refine ⟨⟨m + 1, by omega⟩, ?_⟩
    simp only [stepMap, Nat.lt_irrefl, dite_false]
    rw [sub_getLsbD_zero, hΦev, hx0]
    rfl

theorem ValuationTowerSpec.preserve_primitive_iter {m w : Nat} {Φ c}
    (S : ValuationTowerSpec m w Φ c) {x : State m w}
    (hprim : isPrimitive x) (n : Nat) : isPrimitive (iter (stepMap Φ) n x) := by
  induction n generalizing x with
  | zero => exact hprim
  | succ n ih => exact ih (S.preserve_primitive hprim)

/-! ### Step 3A: Dense-Odd Regime (`2d` Period) -/

/-- Constant-reflection step `(x_0, ..., x_{d-1}) ↦ (x_1, ..., x_{d-1}, c - x_0)`. -/
def reflectStep {m w : Nat} (c : BitVec w) (x : State m w) : State m w :=
  fun i =>
    if h : i.val + 1 < m + 2 then x ⟨i.val + 1, h⟩
    else c - x 0

theorem iter_reflectStep_le {m w : Nat} (c : BitVec w) (x : State m w) :
    ∀ t : Nat, (ht : t ≤ m + 2) →
      iter (reflectStep c) t x = fun i =>
        if h : i.val + t < m + 2 then x ⟨i.val + t, h⟩
        else c - x ⟨i.val + t - (m + 2), by have := i.isLt; omega⟩ := by
  intro t ht
  induction t with
  | zero =>
    funext i
    simp [iter]
  | succ t ih =>
    rw [iter_succ_right, ih (by omega)]
    funext i
    simp only [reflectStep]
    split
    · split <;> split
      · exact congrArg x (fin_mk_eq (by omega))
      · omega
      · omega
      · exact congrArg (c - ·) (congrArg x (fin_mk_eq (by omega)))
    · simp only [Fin.val_zero]
      have h0 : t < m + 2 := by omega
      have h2 : ¬ (i.val + (t + 1) < m + 2) := by omega
      simp [h0, h2]
      exact congrArg x (fin_mk_eq (by omega))

theorem iter_reflectStep_d {m w : Nat} (c : BitVec w) (x : State m w) :
    iter (reflectStep c) (m + 2) x = fun i => c - x i := by
  rw [iter_reflectStep_le c x (m + 2) (Nat.le_refl _)]
  funext i
  split
  · omega
  · exact congrArg (c - ·) (congrArg x (Fin.ext (by dsimp only; omega)))

theorem iter_reflectStep_2d {m w : Nat} (c : BitVec w) (x : State m w) :
    iter (reflectStep c) (2 * (m + 2)) x = x := by
  have h2d : 2 * (m + 2) = (m + 2) + (m + 2) := by omega
  rw [h2d, iter_add, iter_reflectStep_d, iter_reflectStep_d]
  funext i
  exact bv_sub_sub_cancel c (x i)

theorem dense_odd_period {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    {x : State m w}
    (hdense : ∀ n : Nat, ∃ j : Fin (m + 1), (iter (stepMap Φ) n x j.succ).getLsbD 0 = true) :
    iter (stepMap Φ) (2 * (m + 2)) x = x := by
  have heq : ∀ n, iter (stepMap Φ) n x = iter (reflectStep c) n x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iter_succ_right, iter_succ_right, ← ih]
      funext i
      simp only [stepMap, reflectStep]
      split
      · rfl
      · rw [S.level0_odd (tail (iter (stepMap Φ) n x)) (hdense n)]
  rw [heq, iter_reflectStep_2d]

/-! ### Step 3B: Exact `(2d - 1)`-Step Poincaré Return Conjugacy on `inSection` -/

theorem toEven_invol {m w : Nat} (c : BitVec w) (y : State m w) :
    toEven c (toEven c y) = y := by
  funext i
  simp only [toEven]
  split
  · rename_i hi0
    simp only [Fin.val_zero, ite_true]
    have hi : i = 0 := Fin.ext hi0
    rw [hi]
    exact bv_sub_sub_cancel c (y 0)
  · rfl

theorem toEven_allEven_of_inSection {m w : Nat} {c : BitVec w}
    (hc : c.getLsbD 0 = true) {y : State m w} (hy : inSection y) :
    allEven (toEven c y) := by
  intro i
  simp only [toEven]
  split
  · rw [sub_getLsbD_zero, hc, hy.1]; rfl
  · rename_i hi0
    have hsucc : i = Fin.succ ⟨i.val - 1, by omega⟩ := by
      apply Fin.ext; simp [Fin.succ]; omega
    rw [hsucc]
    exact hy.2 ⟨i.val - 1, by omega⟩

theorem poincare_phase1 {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (_hw : 1 ≤ w) {y : State m w} (hy : inSection y) :
    ∀ t : Nat, (ht : t ≤ m + 1) →
      iter (stepMap Φ) (1 + t) y = fun i =>
        if h1 : i.val + 1 + t < m + 2 then y ⟨i.val + 1 + t, h1⟩
        else if i.val + 1 + t = m + 2 then Φ (tail y) - y 0
        else c - y ⟨i.val + 1 + t - (m + 2), by have := i.isLt; omega⟩ := by
  have hL_ev : (Φ (tail y)).getLsbD 0 = false := S.even_of_all_even hy.2
  have hLy_odd : (Φ (tail y) - y 0).getLsbD 0 = true := by
    rw [sub_getLsbD_zero, hL_ev, hy.1]; rfl
  intro t ht
  induction t with
  | zero =>
    rw [Nat.add_zero]
    funext i
    simp only [iter, stepMap]
    split
    · rfl
    · split
      · rfl
      · omega
  | succ t ih =>
    rw [show 1 + (t + 1) = (1 + t) + 1 by omega, iter_succ_right, ih (by omega)]
    have htail_odd : ∃ j : Fin (m + 1),
        (tail (fun i : Fin (m + 2) =>
          if h1 : i.val + 1 + t < m + 2 then y ⟨i.val + 1 + t, h1⟩
          else if i.val + 1 + t = m + 2 then Φ (tail y) - y 0
          else c - y ⟨i.val + 1 + t - (m + 2), by have := i.isLt; omega⟩) j).getLsbD 0 = true := by
      refine ⟨⟨m - t, by omega⟩, ?_⟩
      dsimp only [tail]
      simp only [Fin.val_succ]
      split
      · omega
      · split
        · exact hLy_odd
        · omega
    funext i
    simp only [stepMap, Fin.val_zero]
    split
    · by_cases h1 : i.val + 1 + (t + 1) < m + 2
      · have h1' : (i.val + 1) + 1 + t < m + 2 := by omega
        simp [h1, h1']
        exact congrArg y (fin_mk_eq (by omega))
      · by_cases h2 : i.val + 1 + (t + 1) = m + 2
        · have h2' : (i.val + 1) + 1 + t = m + 2 := by omega
          simp [h2, h2']
        · have h1' : ¬ ((i.val + 1) + 1 + t < m + 2) := by omega
          have h2' : ¬ ((i.val + 1) + 1 + t = m + 2) := by omega
          simp [h1, h1', h2, h2']
          exact congrArg y (fin_mk_eq (by omega))
    · rw [S.level0_odd _ htail_odd]
      have h0 : 0 + 1 + t < m + 2 := by omega
      have h1 : ¬ (i.val + 1 + (t + 1) < m + 2) := by omega
      have h2 : ¬ (i.val + 1 + (t + 1) = m + 2) := by omega
      simp [h0, h1, h2]
      exact congrArg y (fin_mk_eq (by omega))

theorem poincare_mid {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 1 ≤ w) {y : State m w} (hy : inSection y) :
    iter (stepMap Φ) (m + 2) y = fun i =>
      if i.val = 0 then Φ (tail y) - y 0 else c - y i := by
  have h := poincare_phase1 S hw hy (m + 1) (Nat.le_refl _)
  rw [show 1 + (m + 1) = m + 2 by omega] at h
  rw [h]
  funext i
  split
  · omega
  · split <;> split
    · rfl
    · omega
    · omega
    · exact congrArg (c - ·) (congrArg y (Fin.ext (by dsimp only; omega)))

theorem poincare_phase2 {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 1 ≤ w) {y : State m w} (hy : inSection y) :
    ∀ t : Nat, (ht : t ≤ m + 1) →
      iter (stepMap Φ) ((m + 2) + t) y = fun i =>
        if h1 : i.val + t < m + 2 then
          if i.val + t = 0 then Φ (tail y) - y 0 else c - y ⟨i.val + t, h1⟩
        else if i.val + t = m + 2 then c - (Φ (tail y) - y 0)
        else y ⟨i.val + t - (m + 2), by have := i.isLt; omega⟩ := by
  have hc : c.getLsbD 0 = true := S.c_odd hw
  have hcy_odd : ∀ j : Fin (m + 1), (c - y j.succ).getLsbD 0 = true := by
    intro j; rw [sub_getLsbD_zero, hc, hy.2 j]; rfl
  intro t ht
  induction t with
  | zero =>
    have h0 : iter (stepMap Φ) (m + 2 + 0) y = iter (stepMap Φ) (m + 2) y := rfl
    rw [h0, poincare_mid S hw hy]
    funext i
    simp
  | succ t ih =>
    rw [← Nat.add_assoc, iter_succ_right, ih (by omega)]
    have htail_odd : ∃ j : Fin (m + 1),
        (tail (fun i : Fin (m + 2) =>
          if h1 : i.val + t < m + 2 then
            if i.val + t = 0 then Φ (tail y) - y 0 else c - y ⟨i.val + t, h1⟩
          else if i.val + t = m + 2 then c - (Φ (tail y) - y 0)
          else y ⟨i.val + t - (m + 2), by have := i.isLt; omega⟩) j).getLsbD 0 = true := by
      refine ⟨⟨m - t, by omega⟩, ?_⟩
      dsimp only [tail]
      simp only [Fin.val_succ]
      have hlt : m - t + 1 + t < m + 2 := by omega
      simp [hlt]
      have hidx : (⟨m - t + 1 + t, hlt⟩ : Fin (m + 2)) = Fin.succ ⟨m, by omega⟩ := by
        apply Fin.ext; simp [Fin.succ]; omega
      rw [hidx]; exact hcy_odd ⟨m, by omega⟩
    funext i
    simp only [stepMap, Fin.val_zero]
    split
    · by_cases h1 : i.val + (t + 1) < m + 2
      · have h1' : (i.val + 1) + t < m + 2 := by omega
        simp [h1, h1']
        exact congrArg y (fin_mk_eq (by omega))
      · by_cases h2 : i.val + (t + 1) = m + 2
        · have h2' : (i.val + 1) + t = m + 2 := by omega
          simp [h2, h2']
        · have h1' : ¬ ((i.val + 1) + t < m + 2) := by omega
          have h2' : ¬ ((i.val + 1) + t = m + 2) := by omega
          simp [h1, h1', h2, h2']
          exact congrArg y (fin_mk_eq (by omega))
    · rw [S.level0_odd _ htail_odd]
      have h0 : t < m + 2 := by omega
      have h1 : ¬ (i.val + (t + 1) < m + 2) := by omega
      simp [h0, h1]
      by_cases ht0 : t = 0
      · subst ht0
        have h2 : i.val + 1 = m + 2 := by omega
        simp [h2]
      · have h2 : ¬ (i.val + (t + 1) = m + 2) := by omega
        simp [ht0, h2, bv_sub_sub_cancel]
        exact congrArg y (fin_mk_eq (by omega))

/-- **Exact `(2d - 1)`-Step Poincaré Return Theorem:**
    On the even-window section `inSection`, `F^{2d-1}` conjugates via `toEven c` to `poincareR Φ c`. -/
theorem poincare_return {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 1 ≤ w) {e : State m w} (he : allEven e) :
    iter (stepMap Φ) (2 * (m + 2) - 1) (toEven c e) = toEven c (poincareR Φ c e) := by
  have hc : c.getLsbD 0 = true := S.c_odd hw
  have hy : inSection (toEven c e) := by
    refine ⟨?_, ?_⟩
    · simp only [toEven, Fin.val_zero, ite_true]
      rw [sub_getLsbD_zero, hc, he 0]; rfl
    · intro j
      simp only [toEven, Fin.val_succ, Nat.succ_ne_zero, ite_false]
      exact he j.succ
  have htail : tail (toEven c e) = tail e := by
    funext j
    simp [tail, toEven, Fin.val_succ]
  have hstep := poincare_phase2 S hw hy (m + 1) (Nat.le_refl _)
  rw [show (m + 2) + (m + 1) = 2 * (m + 2) - 1 by omega] at hstep
  rw [hstep]
  funext i
  by_cases hi0 : i.val = 0
  · simp [toEven, poincareR, hi0]
  · by_cases hi1 : i.val = 1
    · have heq : 1 + (m + 1) = m + 2 := by omega
      simp [hi1, heq, htail, toEven, poincareR]
      exact bv_poincare_alg c (Φ (tail e)) (e 0)
    · have h1 : ¬ (i.val + (m + 1) < m + 2) := by omega
      have h2 : ¬ (i.val + (m + 1) = m + 2) := by omega
      have hne : i.val + (m + 1) - (m + 2) ≠ 0 := by omega
      simp [h1, h2, toEven, poincareR, hi0, hi1, hne]
      exact congrArg e (fin_mk_eq (by omega))

/-! ### Step 3C: Linear Shift Algebra (`negShift` & `monodromyM`) -/

theorem poincareR_preserve_allEven {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    {e : State m w} (he : allEven e) : allEven (poincareR Φ c e) := by
  intro i
  simp only [poincareR]
  split
  · exact he ⟨m + 1, by omega⟩
  · split
    · have hΦ : (Φ (tail e)).getLsbD 0 = false := S.even_of_all_even (fun j => he j.succ)
      rw [sub_getLsbD_zero, sub_getLsbD_zero, two_mul_getLsbD_zero, hΦ, he 0]
      rfl
    · exact he ⟨i.val - 1, by omega⟩

theorem poincareR_eq_negShift_of_val1 {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    {e : State m w} (he : allEven e)
    (h1 : ∃ j : Fin (m + 1), (e j.succ).getLsbD 1 = true) :
    poincareR Φ c e = negShift e := by
  funext i
  simp only [poincareR, negShift]
  split
  · rfl
  · split
    · rw [S.level1_val1 (tail e) (fun j => he j.succ) h1, BitVec.sub_self, BitVec.zero_sub]
    · rfl

theorem negShift_neg {m w : Nat} (e : State m w) :
    negShift (fun i => -e i) = fun i => -(negShift e i) := by
  funext i
  simp only [negShift]
  split
  · rfl
  · split <;> rfl

theorem monodromyM_eq_neg_negShift {m w : Nat} (e : State m w) :
    monodromyM e = fun i => -(negShift e i) := by
  funext i
  simp only [monodromyM, negShift]
  split
  · rfl
  · split
    · exact BitVec.neg_neg.symm
    · rfl

theorem monodromyM_preserve_allDiv4 {m w : Nat} {e : State m w} (h : allDiv4 e) :
    allDiv4 (monodromyM e) := by
  intro i
  simp only [monodromyM]
  split
  · have ⟨h0, h1⟩ := h ⟨m + 1, by omega⟩
    exact ⟨by rw [neg_getLsbD_zero]; exact h0, by rw [neg_getLsbD_one_of_even h0]; exact h1⟩
  · split
    · exact h 0
    · have ⟨h0, h1⟩ := h ⟨i.val - 1, by omega⟩
      exact ⟨by rw [neg_getLsbD_zero]; exact h0, by rw [neg_getLsbD_one_of_even h0]; exact h1⟩

theorem iter_negShift_le {m w : Nat} (e : State m w) :
    ∀ t : Nat, (ht : 1 ≤ t ∧ t ≤ m + 1) →
      iter negShift t e = fun i =>
        if _h0 : i.val = 0 then e ⟨m + 2 - t, by omega⟩
        else if _hlt : i.val < t then -e ⟨m + 2 + i.val - t, by omega⟩
        else if _heq : i.val = t then -e 0
        else e ⟨i.val - t, by omega⟩ := by
  intro t ht
  rcases ht with ⟨ht1, htm⟩
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht0 : t = 0
    · subst ht0
      funext i
      simp only [iter, negShift]
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · by_cases hi1 : i.val = 1
        · simp [hi1]
        · have hnotlt : ¬ (i.val < 1) := by omega
          simp [hi0, hi1, hnotlt]
    · rw [iter_succ_right, ih (by omega) (by omega)]
      funext i
      simp only [negShift, Fin.val_zero]
      by_cases hi0 : i.val = 0
      · have h1 : ¬ (m + 1 < t) := by omega
        have h2 : m + 1 ≠ t := by omega
        simp [hi0, h1, h2]
      · by_cases hi1 : i.val = 1
        · have hlt : 1 < t + 1 := by omega
          simp [hi1, hlt]
        · by_cases hlt : i.val < t + 1
          · have h1 : i.val - 1 ≠ 0 := by omega
            have h2 : i.val - 1 < t := by omega
            simp [hi0, hi1, hlt, h1, h2]
            exact congrArg e (fin_mk_eq (by omega))
          · by_cases heq : i.val = t + 1
            · simp [heq, ht0]
            · have h1 : i.val - 1 ≠ 0 := by omega
              have h2 : ¬ (i.val - 1 < t) := by omega
              have h3 : i.val - 1 ≠ t := by omega
              simp [hi0, hi1, hlt, heq, h1, h2, h3]
              exact congrArg e (fin_mk_eq (by omega))

theorem iter_negShift_d {m w : Nat} (e : State m w) :
    iter negShift (m + 2) e = fun i => -e i := by
  rw [iter_succ_right, iter_negShift_le e (m + 1) ⟨by omega, Nat.le_refl _⟩]
  funext i
  simp only [negShift, Fin.val_zero]
  by_cases hi0 : i.val = 0
  · simp [hi0]
    exact congrArg e (Fin.ext (by simp [hi0]))
  · by_cases hi1 : i.val = 1
    · simp [hi1]
      exact congrArg e (Fin.ext (by simp [hi1]))
    · have h1 : i.val - 1 ≠ 0 := by omega
      have h2 : i.val - 1 < m + 1 := by omega
      simp [hi0, hi1, h1, h2]
      exact congrArg e (Fin.ext (by dsimp only; omega))

theorem iter_negShift_2d {m w : Nat} (e : State m w) :
    iter negShift (2 * (m + 2)) e = e := by
  rw [show 2 * (m + 2) = (m + 2) + (m + 2) by omega, iter_add, iter_negShift_d, iter_negShift_d]
  funext i; exact BitVec.neg_neg

theorem iter_monodromyM_eq {m w : Nat} (n : Nat) (e : State m w) :
    iter monodromyM n e =
      if n % 2 = 0 then iter negShift n e else fun i => -(iter negShift n e i) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    rw [iter_succ_right, ih, monodromyM_eq_neg_negShift]
    by_cases hev : n % 2 = 0
    · have hodd : ¬ ((n + 1) % 2 = 0) := by omega
      simp only [hev, hodd, ite_true, ite_false]
      rw [iter_succ_right]
    · have hev' : (n + 1) % 2 = 0 := by omega
      simp only [hev, hev', ite_false, ite_true]
      rw [negShift_neg, iter_succ_right]
      funext i; exact BitVec.neg_neg

/-- **Dimension-Parity Monodromy Order Theorem:**
    `M^d = +id` when `d = m + 2` is ODD, and `M^d = -id` (so `M^{2d} = +id`) when `d` is EVEN! -/
theorem iter_monodromyM_d_odd {m w : Nat} (hodd : (m + 2) % 2 ≠ 0) (e : State m w) :
    iter monodromyM (m + 2) e = e := by
  rw [iter_monodromyM_eq]
  simp only [hodd, ite_false, iter_negShift_d]
  funext i; exact BitVec.neg_neg

theorem iter_monodromyM_d_even {m w : Nat} (hev : (m + 2) % 2 = 0) (e : State m w) :
    iter monodromyM (m + 2) e = fun i => -e i := by
  rw [iter_monodromyM_eq]
  simp only [hev, ite_true, iter_negShift_d]

theorem iter_monodromyM_2d_even {m w : Nat} (hev : (m + 2) % 2 = 0) (e : State m w) :
    iter monodromyM (2 * (m + 2)) e = e := by
  rw [show 2 * (m + 2) = (m + 2) + (m + 2) by omega, iter_add,
      iter_monodromyM_d_even hev, iter_monodromyM_d_even hev]
  funext i; exact BitVec.neg_neg

/-! ### Step 3D: Exact `(d + 1)`-Step Nonlinear Cancellation & Primitive Periodicity Theorem -/

/-- **Exact Nonlinear Cancellation Theorem (`ℛ^{d+1} = M` on 4-divisible states):**
    For ANY `ValuationTowerSpec` operator `Φ` and ANY 4-divisible state `z`,
    after `d + 1` Poincaré return steps the arbitrary level-≥2 nonlinearity `Φ(tail z)`
    cancels identically and collapses to the linear monodromy `monodromyM z`! -/
theorem poincareR_linearization {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 2 ≤ w) {z : State m w} (hz : allDiv4 z) :
    iter (poincareR Φ c) (m + 3) z = monodromyM z := by
  have hc : c.getLsbD 0 = true := S.c_odd (by omega)
  have h2c0 : (2#w * c).getLsbD 0 = false := two_mul_getLsbD_zero c
  have h2c1 : (2#w * c).getLsbD 1 = true := two_mul_getLsbD_one_of_odd hc hw
  have htail_div4 : ∀ j : Fin (m + 1), (tail z j).getLsbD 0 = false ∧ (tail z j).getLsbD 1 = false :=
    fun j => hz j.succ
  have ⟨hL0, hL1⟩ := S.level2_div4 (tail z) htail_div4
  let L : BitVec w := Φ (tail z)
  let u : BitVec w := (2#w * c - L) - z 0
  have hu0 : u.getLsbD 0 = false := by
    simp only [u, L, sub_getLsbD_zero, h2c0, hL0, (hz 0).1]; rfl
  have hu1 : u.getLsbD 1 = true := by
    have hsub0 : (2#w * c - L).getLsbD 0 = false := by simp only [L, sub_getLsbD_zero, h2c0, hL0]; rfl
    have hsub1 : (2#w * c - L).getLsbD 1 = true := by
      simp only [L]
      rw [sub_getLsbD_one_of_even h2c0 hL0, h2c1, hL1]; rfl
    simp only [u]
    rw [sub_getLsbD_one_of_even hsub0 (hz 0).1, hsub1, (hz 0).2]; rfl
  let z' : State m w := fun i => if i.val = 0 then -u else z i
  have hz'_ev : allEven z' := by
    intro i; simp only [z']; split
    · rw [neg_getLsbD_zero]; exact hu0
    · exact (hz i).1
  have hstep1 : poincareR Φ c z = negShift z' := by
    funext i
    simp only [poincareR, negShift, z']
    split
    · simp only [Nat.succ_ne_zero, ite_false]
    · split
      · simp only [Fin.val_zero, ite_true, BitVec.neg_neg]; rfl
      · rename_i hi0 hi1
        have hne : i.val - 1 ≠ 0 := by omega
        simp only [hne, ite_false]
  -- For 1 ≤ t ≤ m + 2, iter (poincareR Φ c) t z = iter negShift t z'
  have hsteps : ∀ t : Nat, (ht : 1 ≤ t ∧ t ≤ m + 2) →
      iter (poincareR Φ c) t z = iter negShift t z' := by
    intro t ht
    rcases ht with ⟨ht1, htm⟩
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht0 : t = 0
      · subst ht0; exact hstep1
      · rw [iter_succ_right, iter_succ_right, ih (by omega) (by omega)]
        -- At step t (1 ≤ t ≤ m + 1), iter negShift t z' is allEven and has -z' 0 = u at index t ≥ 1!
        have hev_t : allEven (iter negShift t z') := by
          rw [iter_negShift_le z' t ⟨by omega, by omega⟩]
          intro i
          dsimp only
          split
          · exact hz'_ev _
          · split
            · rw [neg_getLsbD_zero]; exact hz'_ev _
            · split
              · rw [neg_getLsbD_zero]; exact hz'_ev 0
              · exact hz'_ev _
        have hval1_t : ∃ j : Fin (m + 1), (iter negShift t z' j.succ).getLsbD 1 = true := by
          refine ⟨⟨t - 1, by omega⟩, ?_⟩
          rw [iter_negShift_le z' t ⟨by omega, by omega⟩]
          dsimp only
          simp only [Fin.val_succ]
          split
          · omega
          · split
            · omega
            · split
              · simp only [z', Fin.val_zero, ite_true, BitVec.neg_neg]
                exact hu1
              · omega
        exact poincareR_eq_negShift_of_val1 S hev_t hval1_t
  -- Plug in t = m + 2, then apply one final poincareR step!
  rw [show m + 3 = (m + 2) + 1 by omega, iter_succ_right,
      hsteps (m + 2) ⟨by omega, Nat.le_refl _⟩, iter_negShift_d]
  -- Now compute poincareR Φ c (fun i => -z' i)!
  have htail_neg : tail (fun i => -z' i) = fun j => -(tail z j) := by
    funext j
    simp only [tail, z', Fin.val_succ, Nat.succ_ne_zero, ite_false]
  funext i
  simp only [poincareR, monodromyM]
  split
  · simp only [z', Nat.succ_ne_zero, ite_false]
  · split
    · rw [htail_neg, S.level2_sign_inv (tail z) htail_div4]
      simp only [z', Fin.val_zero, ite_true, BitVec.neg_neg]
      exact bv_sub_sub_cancel (2#w * c - L) (z 0)
    · rename_i hi0 hi1
      have hne : i.val - 1 ≠ 0 := by omega
      simp only [z', hne, ite_false]

theorem poincareR_iter_monodromyM {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 2 ≤ w) {z : State m w} (hz : allDiv4 z) (r : Nat) :
    iter (poincareR Φ c) ((m + 3) * r) z = iter monodromyM r z := by
  induction r generalizing z with
  | zero => simp [iter]
  | succ r ih =>
    rw [Nat.mul_succ, Nat.add_comm, iter_add, poincareR_linearization S hw hz,
        iter_succ, ih (monodromyM_preserve_allDiv4 hz)]

theorem poincareR_period_allDiv4 {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 2 ≤ w) {z : State m w} (hz : allDiv4 z) :
    iter (poincareR Φ c) (QFactor (m + 2)) z = z := by
  unfold QFactor
  by_cases hev : (m + 2) % 2 = 0
  · simp only [hev, ite_true]
    rw [show 2 * (m + 2) * (m + 2 + 1) = (m + 3) * (2 * (m + 2)) by
          rw [Nat.mul_comm (2 * (m + 2)) (m + 2 + 1)]]
    rw [poincareR_iter_monodromyM S hw hz, iter_monodromyM_2d_even hev]
  · simp only [hev, ite_false]
    rw [show (m + 2) * (m + 2 + 1) = (m + 3) * (m + 2) by
          rw [Nat.mul_comm (m + 2) (m + 2 + 1)]]
    rw [poincareR_iter_monodromyM S hw hz, iter_monodromyM_d_odd hev]

theorem poincareR_injective {m w : Nat} (Φ : (Fin (m + 1) → BitVec w) → BitVec w) (c : BitVec w) :
    ∀ e₁ e₂ : State m w, poincareR Φ c e₁ = poincareR Φ c e₂ → e₁ = e₂ := by
  intro e₁ e₂ h
  have htail_eq : tail e₁ = tail e₂ := by
    funext j
    have hidx : j.val + 1 < m + 2 := by omega
    by_cases hj : j.val = m
    · have h0 := congrFun h 0
      simp only [poincareR, Fin.val_zero, ite_true] at h0
      have hj_eq : j.succ = ⟨m + 1, by omega⟩ := by apply Fin.ext; simp [Fin.succ]; omega
      simp only [tail, hj_eq]; exact h0
    · have hk := congrFun h ⟨j.val + 2, by omega⟩
      have hne0 : j.val + 2 ≠ 0 := by omega
      have hne1 : j.val + 2 ≠ 1 := by omega
      simp only [poincareR, hne0, hne1, ite_false] at hk
      have hj_eq : j.succ = ⟨j.val + 2 - 1, by omega⟩ := by apply Fin.ext; simp [Fin.succ]
      simp only [tail, hj_eq]; exact hk
  funext i
  cases i using Fin.cases with
  | zero =>
    have h1 := congrFun h ⟨1, by omega⟩
    simp only [poincareR, Nat.one_ne_zero, ite_false, ite_true, htail_eq] at h1
    have hcan := congrArg (fun t => (2#w * c - Φ (tail e₂)) - t) h1
    simpa only [bv_sub_sub_cancel] using hcan
  | succ j => exact congrFun htail_eq j

theorem poincareR_period_allEven {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 2 ≤ w) {e : State m w} (he : allEven e) :
    iter (poincareR Φ c) (QFactor (m + 2)) e = e := by
  have hev_iter : ∀ n, allEven (iter (poincareR Φ c) n e) := by
    intro n
    induction n with
    | zero => exact he
    | succ n ih => rw [iter_succ_right]; exact poincareR_preserve_allEven S ih
  by_cases hact : ∀ n : Nat, ∃ j : Fin (m + 1), (iter (poincareR Φ c) n e j.succ).getLsbD 1 = true
  · -- Level-1 Always Active: `poincareR = negShift`, period divides `2d ∣ QFactor d`
    have heq : ∀ n, iter (poincareR Φ c) n e = iter negShift n e := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [iter_succ_right, iter_succ_right, ← ih]
        exact poincareR_eq_negShift_of_val1 S (hev_iter n) (hact n)
    have h2d : iter (poincareR Φ c) (2 * (m + 2)) e = e := by
      rw [heq, iter_negShift_2d]
    exact iter_fixed_of_dvd (poincareR Φ c) h2d (two_mul_dvd_QFactor (m + 2))
  · -- Hits a 4-divisible tail at some step `k`: at `k` or `k+1`, state is `allDiv4`!
    have hex : ∃ k : Nat, ∀ j : Fin (m + 1), (iter (poincareR Φ c) k e j.succ).getLsbD 1 = false := by
      apply Classical.byContradiction
      intro hno
      apply hact
      intro n
      apply Classical.byContradiction
      intro hno_j
      apply hno
      refine ⟨n, fun j => ?_⟩
      cases hb : (iter (poincareR Φ c) n e j.succ).getLsbD 1
      · rfl
      · exfalso; exact hno_j ⟨j, hb⟩
    rcases hex with ⟨k, hk⟩
    let z := iter (poincareR Φ c) k e
    have hz_ev : allEven z := hev_iter k
    have hdiv4_reach : ∃ k', allDiv4 (iter (poincareR Φ c) k' e) := by
      by_cases hz0 : (z 0).getLsbD 1 = false
      · refine ⟨k, fun i => ⟨hz_ev i, ?_⟩⟩
        cases i using Fin.cases with
        | zero => exact hz0
        | succ j => exact hk j
      · have hz0_t : (z 0).getLsbD 1 = true := by
          cases hb : (z 0).getLsbD 1 <;> simp_all
        refine ⟨k + 1, ?_⟩
        rw [iter_succ_right]
        intro i
        refine ⟨poincareR_preserve_allEven S hz_ev i, ?_⟩
        simp only [poincareR]
        split
        · exact hk ⟨m, by omega⟩
        · split
          · have htd : ∀ j : Fin (m + 1), (tail z j).getLsbD 0 = false ∧ (tail z j).getLsbD 1 = false :=
              fun j => ⟨hz_ev j.succ, hk j⟩
            have ⟨hL0, hL1⟩ := S.level2_div4 (tail z) htd
            have h2c0 : (2#w * c).getLsbD 0 = false := two_mul_getLsbD_zero c
            have h2c1 : (2#w * c).getLsbD 1 = true := two_mul_getLsbD_one_of_odd (S.c_odd (by omega)) hw
            have hsub0 : (2#w * c - Φ (tail z)).getLsbD 0 = false := by
              rw [sub_getLsbD_zero, h2c0, hL0]; rfl
            have hsub1 : (2#w * c - Φ (tail z)).getLsbD 1 = true := by
              rw [sub_getLsbD_one_of_even h2c0 hL0, h2c1, hL1]; rfl
            rw [sub_getLsbD_one_of_even hsub0 (hz_ev 0), hsub1, hz0_t]; rfl
          · rename_i hi0 hi1
            have hsucc : (⟨i.val - 1, by omega⟩ : Fin (m + 2)) = Fin.succ ⟨i.val - 2, by omega⟩ := by
              apply Fin.ext; simp [Fin.succ]; omega
            rw [hsucc]
            exact hk ⟨i.val - 2, by omega⟩
    rcases hdiv4_reach with ⟨k', hk'⟩
    have hper_k' : iter (poincareR Φ c) (QFactor (m + 2)) (iter (poincareR Φ c) k' e) =
        iter (poincareR Φ c) k' e := poincareR_period_allDiv4 S hw hk'
    rw [iter_comm] at hper_k'
    exact iter_injective (poincareR_injective Φ c) k' _ _ hper_k'

/--
**MAIN ENGINE THEOREM 1 (VTPR Primitive Periodicity Theorem):**
For ANY dimension `d = m + 2 ≥ 2`, ANY bit-width `w : Nat`, ANY odd constant `c : BitVec w`,
and ANY nonlinear operator `Φ` satisfying `ValuationTowerSpec m w Φ c`, EVERY primitive
state `x : State m w` returns to itself after exactly `QPeriod (m + 2) = lcm(2d, d+1) * (2d - 1)` steps!
-/
theorem vtpr_primitive_period {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    {x : State m w} (hprim : isPrimitive x) :
    iter (stepMap Φ) (QPeriod (m + 2)) x = x := by
  by_cases hw0 : w = 0
  · subst hw0; funext i; exact Subsingleton.elim _ _
  have hw1 : 1 ≤ w := by omega
  by_cases hdense : ∀ n : Nat, ∃ j : Fin (m + 1), (iter (stepMap Φ) n x j.succ).getLsbD 0 = true
  · -- Regime 1 (Dense-Odd): period divides `2d ∣ Q(d)`
    have h2d := dense_odd_period S hdense
    exact iter_fixed_of_dvd (stepMap Φ) h2d (two_mul_dvd_QPeriod (m + 2))
  · -- Regime 2 (Sparse-Odd): hits even-window section `inSection` at some step `k`
    have hex : ∃ k : Nat, ∀ j : Fin (m + 1), (iter (stepMap Φ) k x j.succ).getLsbD 0 = false := by
      apply Classical.byContradiction
      intro hno
      apply hdense
      intro n
      apply Classical.byContradiction
      intro hno_j
      apply hno
      refine ⟨n, fun j => ?_⟩
      cases hb : (iter (stepMap Φ) n x j.succ).getLsbD 0
      · rfl
      · exfalso; exact hno_j ⟨j, hb⟩
    rcases hex with ⟨k, hk⟩
    let y := iter (stepMap Φ) k x
    have hy_prim : isPrimitive y := S.preserve_primitive_iter hprim k
    have hy0 : (y 0).getLsbD 0 = true := by
      rcases hy_prim with ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact hi
      | succ j => rw [hk j] at hi; cases hi
    have hy_sec : inSection y := ⟨hy0, hk⟩
    let e := toEven c y
    have he_ev : allEven e := toEven_allEven_of_inSection (S.c_odd hw1) hy_sec
    have hy_eq : y = toEven c e := (toEven_invol c y).symm
    -- Iterating the (2d - 1)-step Poincaré return map `r` times!
    have hret_iter : ∀ (r : Nat) (e0 : State m w), allEven e0 →
        iter (stepMap Φ) ((2 * (m + 2) - 1) * r) (toEven c e0) =
          toEven c (iter (poincareR Φ c) r e0) := by
      intro r
      induction r with
      | zero => intro e0 _; simp [iter]
      | succ r ih =>
        intro e0 he0
        rw [Nat.mul_succ, Nat.add_comm, iter_add, poincare_return S hw1 he0,
            iter_succ, ih (poincareR Φ c e0) (poincareR_preserve_allEven S he0)]
    have hper_y : iter (stepMap Φ) (QPeriod (m + 2)) y = y := by
      rw [hy_eq, QPeriod, Nat.mul_comm, hret_iter (QFactor (m + 2)) e he_ev]
      by_cases hw2 : 2 ≤ w
      · rw [poincareR_period_allEven S hw2 he_ev]
      · -- Edge case `w = 1`: all even vectors are identically `0#1`!
        have hw_eq1 : w = 1 := by omega
        subst hw_eq1
        have hzero : ∀ v : State m 1, allEven v → v = fun _ => 0#1 := by
          intro v hv
          funext i
          apply BitVec.eq_of_getLsbD_eq
          intro b hb
          have hb0 : b = 0 := by omega
          subst hb0
          exact hv i
        have he0 : e = fun _ => 0#1 := hzero e he_ev
        have hr0 : iter (poincareR Φ c) (QFactor (m + 2)) e = fun _ => 0#1 := by
          apply hzero
          clear he0 hy_eq hret_iter
          induction (QFactor (m + 2)) with
          | zero => exact he_ev
          | succ n ih => rw [iter_succ_right]; exact poincareR_preserve_allEven S ih
        rw [hr0, ← he0]
    change iter (stepMap Φ) (QPeriod (m + 2)) (iter (stepMap Φ) k x) = iter (stepMap Φ) k x at hper_y
    rw [iter_comm] at hper_y
    exact iter_injective (stepMap_injective Φ) k _ _ hper_y

theorem ValuationHomogeneousSpec.step_shift2 {m : Nat} {Φ c}
    (H : ValuationHomogeneousSpec m Φ c) (w : Nat) (x : State m w) :
    stepMap (Φ (w + 1)) (fun i => shift2 (x i)) = fun i => shift2 (stepMap (Φ w) x i) := by
  funext i
  simp only [stepMap]
  split
  · rfl
  · have htail : tail (fun i => shift2 (x i)) = fun j => shift2 (tail x j) := rfl
    rw [htail, H.shift2_hom w (tail x), ← shift2_sub]

/--
**MAIN ENGINE THEOREM 2 (Exact Infinite-Width Valuation Conservation):**
For EVERY `ValuationHomogeneousSpec` family, EVERY bit-width `w`, and EVERY state `x`,
the joint lowest-set-bit `lsb (orVec x)` is strictly conserved by `stepMap (Φ w)`.
-/
theorem vtpr_conserved_joint_lsb {m : Nat} {Φ c} (H : ValuationHomogeneousSpec m Φ c) :
    ∀ (w : Nat) (x : State m w),
      lsb (orVec (stepMap (Φ w) x)) = lsb (orVec x) := by
  intro w
  induction w with
  | zero => intro x; exact Subsingleton.elim _ _
  | succ w ih =>
    intro x
    by_cases hprim : isPrimitive x
    · have hodd1 : (orVec x).getLsbD 0 = true := (getLsbD_orVec x 0).mpr hprim
      have hodd2 : (orVec (stepMap (Φ (w + 1)) x)).getLsbD 0 = true :=
        (getLsbD_orVec _ 0).mpr ((H.tower (w + 1)).preserve_primitive hprim)
      rw [lsb_eq_one_of_odd hodd1, lsb_eq_one_of_odd hodd2]
    · have hall : ∀ i : Fin (m + 2), (x i).getLsbD 0 = false := by
        intro i
        cases hb : (x i).getLsbD 0
        · rfl
        · exfalso; exact hprim ⟨i, hb⟩
      let y : State m w := fun i => halfBV (x i)
      have hx_eq : x = fun i => shift2 (y i) := by
        funext i; exact (shift2_halfBV (hall i)).symm
      rw [hx_eq, H.step_shift2 w y, ← shift2_orVec, ← shift2_orVec, ← shift2_lsb, ← shift2_lsb,
          ih y]

/--
**MAIN ENGINE THEOREM 3 (Full-Space Infinite-Width Tower-Lifting Periodicity):**
For EVERY `ValuationHomogeneousSpec` family, EVERY bit-width `w : Nat`, and EVERY state
`x : State m w` (across ALL valuation strata `0 ≤ ν₂(x) ≤ w`),
`iter (stepMap (Φ w)) (QPeriod (m + 2)) x = x`!
-/
theorem vtpr_full_period {m : Nat} {Φ c} (H : ValuationHomogeneousSpec m Φ c) :
    ∀ (w : Nat) (x : State m w),
      iter (stepMap (Φ w)) (QPeriod (m + 2)) x = x := by
  intro w
  induction w with
  | zero => intro x; funext i; exact Subsingleton.elim _ _
  | succ w ih =>
    intro x
    by_cases hprim : isPrimitive x
    · exact vtpr_primitive_period (H.tower (w + 1)) hprim
    · have hall : ∀ i : Fin (m + 2), (x i).getLsbD 0 = false := by
        intro i
        cases hb : (x i).getLsbD 0
        · rfl
        · exfalso; exact hprim ⟨i, hb⟩
      let y : State m w := fun i => halfBV (x i)
      have hx_eq : x = fun i => shift2 (y i) := by
        funext i; exact (shift2_halfBV (hall i)).symm
      rw [hx_eq]
      have hconj := iter_conj (stepMap (Φ w)) (stepMap (Φ (w + 1)))
        (fun (z : State m w) => (fun i => shift2 (z i)))
        (fun z => (H.step_shift2 w z).symm) (QPeriod (m + 2)) y
      rw [← hconj, ih y]

/-! ## Section 4: Concrete Infinite Families, Universal Minimal Period & Sharpness -/

/-! ### 4A: Family 1 — `d`-Dimensional Twisted Joint-LSB Subtraction Recurrence -/

theorem mul_div4_right {w : Nat} (c x : BitVec w)
    (hx : x.getLsbD 0 = false ∧ x.getLsbD 1 = false) :
    (c * x).getLsbD 0 = false ∧ (c * x).getLsbD 1 = false := by
  cases w with
  | zero => simp
  | succ w =>
    rw [← shift2_halfBV hx.1, shift2_mul_left]
    refine ⟨getLsbD_shift2_zero _, ?_⟩
    rw [getLsbD_shift2_succ]
    have hx1 : (halfBV x).getLsbD 0 = false := by
      have := getLsbD_shift2_succ (halfBV x) 0
      rw [shift2_halfBV hx.1] at this
      rw [← this, hx.2]
    cases w with
    | zero => simp
    | succ w =>
      rw [← shift2_halfBV hx1, shift2_mul_left]
      exact getLsbD_shift2_zero _

theorem four_mul_div4 {w : Nat} (x : BitVec w) :
    (4#w * x).getLsbD 0 = false ∧ (4#w * x).getLsbD 1 = false := by
  rw [BitVec.mul_comm]
  apply mul_div4_right
  refine ⟨?_, ?_⟩
  · cases w with
    | zero => simp
    | succ w =>
      rw [getLsbD_zero_false_iff_mod2, BitVec.toNat_ofNat]
      have h2 : 2 ∣ 2 ^ (w + 1) := by rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 (2 ^ w)
      rw [Nat.mod_mod_of_dvd 4 h2]
  · cases w with
    | zero => simp
    | succ w =>
      cases w with
      | zero => exact getLsbD_ge_width _ 1 (by omega)
      | succ w =>
        cases w with
        | zero => decide
        | succ w =>
          have h4lt : 4 < 2 ^ (w + 3) := by
            have : 2 ^ 3 ≤ 2 ^ (w + 3) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          simp only [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4lt]
          decide

/-- Instantiation of Layer 1 (`ValuationTowerSpec`) for `twistedLSBPhi c`. -/
theorem twistedLSB_towerSpec (m w : Nat) (c : BitVec w) (hc : 1 ≤ w → c.getLsbD 0 = true) :
    ValuationTowerSpec m w (twistedLSBPhi c) c where
  c_odd := hc
  level0_odd := by
    intro v hv
    simp only [twistedLSBPhi]
    have hodd : (orVec v).getLsbD 0 = true := (getLsbD_orVec v 0).mpr hv
    rw [lsb_eq_one_of_odd hodd, BitVec.mul_one]
  level1_val1 := by
    intro v hev h1
    simp only [twistedLSBPhi]
    have h0 : (orVec v).getLsbD 0 = false := (getLsbD_orVec_false v 0).mpr hev
    have h1' : (orVec v).getLsbD 1 = true := (getLsbD_orVec v 1).mpr h1
    rw [lsb_eq_two_of_val1 h0 h1', BitVec.mul_comm]
  level2_div4 := by
    intro v hv
    simp only [twistedLSBPhi]
    have h0 : (orVec v).getLsbD 0 = false := (getLsbD_orVec_false v 0).mpr (fun j => (hv j).1)
    have h1 : (orVec v).getLsbD 1 = false := (getLsbD_orVec_false v 1).mpr (fun j => (hv j).2)
    exact mul_div4_right c (lsb (orVec v)) (lsb_div4 h0 h1)
  level2_sign_inv := by
    intro v _
    simp only [twistedLSBPhi]
    rw [lsb_orVec_neg]

/-- Instantiation of Layer 2 (`ValuationHomogeneousSpec`) for any odd multiplier `k : Nat`. -/
theorem twistedLSB_homSpec (m k : Nat) (hk : k % 2 = 1) :
    ValuationHomogeneousSpec m
      (fun w => twistedLSBPhi (BitVec.ofNat w k))
      (fun w => BitVec.ofNat w k) where
  tower := fun w => twistedLSB_towerSpec m w (BitVec.ofNat w k) (fun hw => by
    rw [getLsbD_zero_iff_mod2, BitVec.toNat_ofNat]
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    have h2 : 2 ∣ 2 ^ (w' + 1) := by rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 (2 ^ w')
    rw [Nat.mod_mod_of_dvd k h2, hk])
  shift2_hom := by
    intro w v
    simp only [twistedLSBPhi]
    rw [← shift2_orVec, ← shift2_lsb, shift2_mul_left]
    congr 1
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_trunc1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := by rw [Nat.pow_succ]; exact Nat.dvd_mul_right (2 ^ w) 2
    exact Nat.mod_mod_of_dvd k hdvd

/--
**HEADLINE THEOREM A1 (Infinite-Dimension, Infinite-Width Exact Conserved Invariant):**
For EVERY dimension `d = m + 2 ≥ 2`, EVERY bit-width `w : Nat`, EVERY odd multiplier `c : BitVec w`,
and EVERY state `x : (BitVec w)^d`, the joint lowest-set-bit `lsb (orVec x)` is strictly conserved.
-/
theorem twistedLSB_conserved_joint_lsb (m w : Nat) (c : BitVec w)
    (hc : 1 ≤ w → c.getLsbD 0 = true) (x : State m w) :
    lsb (orVec (twistedLSBStep c x)) = lsb (orVec x) := by
  cases w with
  | zero => exact Subsingleton.elim _ _
  | succ w =>
    have hodd : c.toNat % 2 = 1 := (getLsbD_zero_iff_mod2 c).mp (hc (by omega))
    have hc_eq : BitVec.ofNat (w + 1) c.toNat = c :=
      BitVec.eq_of_toNat_eq (by simp)
    have h := vtpr_conserved_joint_lsb (twistedLSB_homSpec m c.toNat hodd) (w + 1) x
    simpa only [twistedLSBStep, hc_eq] using h

/--
**HEADLINE THEOREM A2 (Infinite-Dimension, Infinite-Width Exact Periodicity):**
For EVERY dimension `d = m + 2 ≥ 2`, EVERY bit-width `w : Nat`, EVERY odd multiplier `c : BitVec w`,
and EVERY state `x : (BitVec w)^d`, `twistedLSBStep c` has exact global period
`Q(d) = lcm(2d, d + 1) * (2d - 1)`.
-/
theorem twistedLSB_period (m w : Nat) (c : BitVec w)
    (hc : 1 ≤ w → c.getLsbD 0 = true) (x : State m w) :
    iter (twistedLSBStep c) (QPeriod (m + 2)) x = x := by
  cases w with
  | zero => funext i; exact Subsingleton.elim _ _
  | succ w =>
    have hodd : c.toNat % 2 = 1 := (getLsbD_zero_iff_mod2 c).mp (hc (by omega))
    have hc_eq : BitVec.ofNat (w + 1) c.toNat = c :=
      BitVec.eq_of_toNat_eq (by simp)
    have h := vtpr_full_period (twistedLSB_homSpec m c.toNat hodd) (w + 1) x
    simpa only [twistedLSBStep, hc_eq] using h

/-- Explicit dimension specializations illustrating the non-monotone dimension-parity bifurcation:
    `Q(2)=36, Q(3)=60, Q(4)=280 > Q(5)=270, Q(6)=924 > Q(7)=728`. -/
theorem twistedLSB_period_2D (w : Nat) (c : BitVec w) (hc : 1 ≤ w → c.getLsbD 0 = true)
    (x : State 0 w) : iter (twistedLSBStep c) 36 x = x :=
  twistedLSB_period 0 w c hc x

theorem twistedLSB_period_3D (w : Nat) (c : BitVec w) (hc : 1 ≤ w → c.getLsbD 0 = true)
    (x : State 1 w) : iter (twistedLSBStep c) 60 x = x :=
  twistedLSB_period 1 w c hc x

theorem twistedLSB_period_4D (w : Nat) (c : BitVec w) (hc : 1 ≤ w → c.getLsbD 0 = true)
    (x : State 2 w) : iter (twistedLSBStep c) 280 x = x :=
  twistedLSB_period 2 w c hc x

theorem twistedLSB_period_5D (w : Nat) (c : BitVec w) (hc : 1 ≤ w → c.getLsbD 0 = true)
    (x : State 3 w) : iter (twistedLSBStep c) 270 x = x :=
  twistedLSB_period 3 w c hc x

theorem period_bifurcation_drop :
    QPeriod 2 = 36 ∧ QPeriod 3 = 60 ∧ QPeriod 4 = 280 ∧ QPeriod 5 = 270 ∧
    QPeriod 6 = 924 ∧ QPeriod 7 = 728 ∧ QPeriod 5 < QPeriod 4 ∧ QPeriod 7 < QPeriod 6 := by
  decide

theorem sumSq_neg {w n : Nat} (v : Fin n → BitVec w) :
    sumSq (fun i => -v i) = sumSq v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumSq]
    have hsq : (-v 0) * (-v 0) = v 0 * v 0 := by
      rw [BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg]
    rw [hsq, ih (fun i => v i.succ)]

/-- Instantiation of Layer 1 (`ValuationTowerSpec`) for `wildQuadPhi c`. -/
theorem wildQuad_towerSpec (m w : Nat) (c : BitVec w) (hc : 1 ≤ w → c.getLsbD 0 = true) :
    ValuationTowerSpec m w (wildQuadPhi c) c where
  c_odd := hc
  level0_odd := by
    intro v hv
    have hodd : (orVec v).getLsbD 0 = true := (getLsbD_orVec v 0).mpr hv
    simp [wildQuadPhi, hodd]
  level1_val1 := by
    intro v hev h1
    have h0 : (orVec v).getLsbD 0 = false := (getLsbD_orVec_false v 0).mpr hev
    have h1' : (orVec v).getLsbD 1 = true := (getLsbD_orVec v 1).mpr h1
    simp [wildQuadPhi, h0, h1']
  level2_div4 := by
    intro v hv
    have h0 : (orVec v).getLsbD 0 = false := (getLsbD_orVec_false v 0).mpr (fun j => (hv j).1)
    have h1 : (orVec v).getLsbD 1 = false := (getLsbD_orVec_false v 1).mpr (fun j => (hv j).2)
    simp only [wildQuadPhi, h0, h1, Bool.false_eq_true, ite_false]
    exact four_mul_div4 (sumSq v)
  level2_sign_inv := by
    intro v hv
    have h0 : (orVec v).getLsbD 0 = false := (getLsbD_orVec_false v 0).mpr (fun j => (hv j).1)
    have h1 : (orVec v).getLsbD 1 = false := (getLsbD_orVec_false v 1).mpr (fun j => (hv j).2)
    have h0' : (orVec (fun j => -v j)).getLsbD 0 = false :=
      (getLsbD_orVec_false _ 0).mpr (fun j => by rw [neg_getLsbD_zero]; exact (hv j).1)
    have h1' : (orVec (fun j => -v j)).getLsbD 1 = false :=
      (getLsbD_orVec_false _ 1).mpr (fun j => by rw [neg_getLsbD_one_of_even (hv j).1]; exact (hv j).2)
    simp only [wildQuadPhi, h0, h1, h0', h1', Bool.false_eq_true, ite_false]
    rw [sumSq_neg]

/--
**HEADLINE THEOREM B (Non-Transducer Wild Quadratic Periodicity):**
Even though `4 * ∑ y_j^2` is nonlinear quadratic arithmetic (not a finite-state Mealy transducer
and not 2-adic homogeneous), EVERY primitive orbit in EVERY dimension `d = m + 2 ≥ 2` and EVERY
bit-width `w : Nat` still locks to exact global period `Q(d) = lcm(2d, d + 1) * (2d - 1)`.
-/
theorem wildQuad_primitive_period (m w : Nat) (c : BitVec w)
    (hc : 1 ≤ w → c.getLsbD 0 = true) (x : State m w) (hprim : isPrimitive x) :
    iter (stepMap (wildQuadPhi c)) (QPeriod (m + 2)) x = x :=
  vtpr_primitive_period (wildQuad_towerSpec m w c hc) hprim

/-- Even-coordinate image of `v*_d` under `toEven 1#w`: `(0, ..., 0, 4)`. -/
def witnessEven (m w : Nat) : State m w :=
  fun i => if i.val = m + 1 then 4#w else 0#w

theorem not_inSection_step_pos_lt {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 1 ≤ w) {y : State m w} (hy : inSection y) {r : Nat}
    (hr1 : 0 < r) (hr2 : r < 2 * (m + 2) - 1) :
    ¬ inSection (iter (stepMap Φ) r y) := by
  intro hsec
  have hc : c.getLsbD 0 = true := S.c_odd hw
  have hL_ev : (Φ (tail y)).getLsbD 0 = false := S.even_of_all_even hy.2
  have hLy_odd : (Φ (tail y) - y 0).getLsbD 0 = true := by
    rw [sub_getLsbD_zero, hL_ev, hy.1]; rfl
  by_cases hle : r ≤ m + 1
  · -- Phase 1 (`r = 1 + t`, `t ≤ m`): `Φ (tail y) - y 0` (odd!) sits at tail index `m + 1 - t ≥ 1`
    have hph := poincare_phase1 S hw hy (r - 1) (by omega)
    rw [show 1 + (r - 1) = r by omega] at hph
    have hev := hsec.2 ⟨m + 1 - r, by omega⟩
    rw [hph] at hev
    dsimp only at hev
    simp only [Fin.val_succ] at hev
    have heq : m + 1 - r + 1 + 1 + (r - 1) = m + 2 := by omega
    simp [heq] at hev
    rw [hLy_odd] at hev; cases hev
  · -- Phase 2 (`r = (m + 2) + t`, `0 ≤ t ≤ m`): `c - y (m + 1)` (odd!) sits at tail index `m + 1 - t ≥ 1`
    have hph := poincare_phase2 S hw hy (r - (m + 2)) (by omega)
    rw [show (m + 2) + (r - (m + 2)) = r by omega] at hph
    have hev := hsec.2 ⟨m - (r - (m + 2)), by omega⟩
    rw [hph] at hev
    dsimp only at hev
    simp only [Fin.val_succ] at hev
    have hlt : m - (r - (m + 2)) + 1 + (r - (m + 2)) < m + 2 := by omega
    have hne0 : m - (r - (m + 2)) + 1 + (r - (m + 2)) ≠ 0 := by omega
    simp only [hlt, hne0, dite_true, ite_false] at hev
    have hidx : (⟨m - (r - (m + 2)) + 1 + (r - (m + 2)), hlt⟩ : Fin (m + 2)) = Fin.succ ⟨m, by omega⟩ := by
      apply Fin.ext; simp [Fin.succ]; omega
    rw [hidx, sub_getLsbD_zero, hc, hy.2 ⟨m, by omega⟩] at hev
    cases hev

theorem not_allDiv4_poincareR_pos_lt {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 2 ≤ w) {z : State m w} (hz : allDiv4 z) {r : Nat}
    (hr1 : 0 < r) (hr2 : r < m + 3) :
    ¬ allDiv4 (iter (poincareR Φ c) r z) := by
  intro hdiv
  have hc : c.getLsbD 0 = true := S.c_odd (by omega)
  have h2c0 : (2#w * c).getLsbD 0 = false := two_mul_getLsbD_zero c
  have h2c1 : (2#w * c).getLsbD 1 = true := two_mul_getLsbD_one_of_odd hc hw
  have ⟨hL0, hL1⟩ := S.level2_div4 (tail z) (fun j => hz j.succ)
  let u : BitVec w := (2#w * c - Φ (tail z)) - z 0
  have hu0 : u.getLsbD 0 = false := by
    simp only [u, sub_getLsbD_zero, h2c0, hL0, (hz 0).1]; rfl
  have hu1 : u.getLsbD 1 = true := by
    have hsub0 : (2#w * c - Φ (tail z)).getLsbD 0 = false := by rw [sub_getLsbD_zero, h2c0, hL0]; rfl
    have hsub1 : (2#w * c - Φ (tail z)).getLsbD 1 = true := by
      rw [sub_getLsbD_one_of_even h2c0 hL0, h2c1, hL1]; rfl
    simp only [u]
    rw [sub_getLsbD_one_of_even hsub0 (hz 0).1, hsub1, (hz 0).2]; rfl
  let z' : State m w := fun i => if i.val = 0 then -u else z i
  have hz'_ev : allEven z' := by
    intro i; simp only [z']; split
    · rw [neg_getLsbD_zero]; exact hu0
    · exact (hz i).1
  have hstep1 : poincareR Φ c z = negShift z' := by
    funext i; simp only [poincareR, negShift, z']
    split
    · simp only [Nat.succ_ne_zero, ite_false]
    · split
      · simp only [Fin.val_zero, ite_true, BitVec.neg_neg]; rfl
      · rename_i hi0 hi1
        have hne : i.val - 1 ≠ 0 := by omega
        simp only [hne, ite_false]
  have hsteps : ∀ t : Nat, (ht : 1 ≤ t ∧ t ≤ m + 2) →
      iter (poincareR Φ c) t z = iter negShift t z' := by
    intro t ⟨ht1, htm⟩
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht0 : t = 0
      · subst ht0; exact hstep1
      · rw [iter_succ_right, iter_succ_right, ih (by omega) (by omega)]
        have hev_t : allEven (iter negShift t z') := by
          rw [iter_negShift_le z' t ⟨by omega, by omega⟩]
          intro i; dsimp only
          split
          · exact hz'_ev _
          · split
            · rw [neg_getLsbD_zero]; exact hz'_ev _
            · split
              · rw [neg_getLsbD_zero]; exact hz'_ev 0
              · exact hz'_ev _
        have hval1_t : ∃ j : Fin (m + 1), (iter negShift t z' j.succ).getLsbD 1 = true := by
          refine ⟨⟨t - 1, by omega⟩, ?_⟩
          rw [iter_negShift_le z' t ⟨by omega, by omega⟩]
          dsimp only; simp only [Fin.val_succ]
          split
          · omega
          · split
            · omega
            · split
              · simp only [z', Fin.val_zero, ite_true, BitVec.neg_neg]; exact hu1
              · omega
        exact poincareR_eq_negShift_of_val1 S hev_t hval1_t
  rw [hsteps r ⟨hr1, by omega⟩] at hdiv
  by_cases hrm : r ≤ m + 1
  · have hbit := (hdiv ⟨r, by omega⟩).2
    rw [iter_negShift_le z' r ⟨hr1, hrm⟩] at hbit
    dsimp only at hbit
    have hr0 : r ≠ 0 := by omega
    have hnotlt : ¬ (r < r) := Nat.lt_irrefl r
    simp only [hr0, hnotlt, dite_false, dite_true, z', Fin.val_zero, ite_true, BitVec.neg_neg] at hbit
    rw [hu1] at hbit; cases hbit
  · have hreq : r = m + 2 := by omega
    subst hreq
    have hbit := (hdiv 0).2
    rw [iter_negShift_d] at hbit
    simp only [z', Fin.val_zero, ite_true, BitVec.neg_neg] at hbit
    rw [hu1] at hbit; cases hbit

theorem four_ne_zero_of_ge4 {w : Nat} (hw : 4 ≤ w) : (4#w) ≠ 0#w := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
  have hlt : 4 < 2 ^ w := by
    have : 16 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
    omega
  rw [Nat.mod_eq_of_lt hlt] at this
  omega

theorem four_ne_neg_four_of_ge4 {w : Nat} (hw : 4 ≤ w) : (-4#w) ≠ 4#w := by
  intro h
  have h16 : 16 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have htoNat := congrArg BitVec.toNat h
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat] at htoNat
  have h4mod : 4 % 2 ^ w = 4 := Nat.mod_eq_of_lt (by omega)
  have hsubmod : (2 ^ w - 4) % 2 ^ w = 2 ^ w - 4 := Nat.mod_eq_of_lt (by omega)
  rw [h4mod, hsubmod] at htoNat
  omega

/--
**HEADLINE THEOREM C (Universal Exact Minimal Period Theorem):**
For EVERY dimension `d = m + 2 ≥ 2`, EVERY bit-width `w ≥ 4`, and EVERY operator `Φ` satisfying
`ValuationTowerSpec m w Φ 1#w`, the single explicit state `v*_d = (1, 0, ..., 0, 4)` has
**EXACT MINIMAL PERIOD** `Q(d) = lcm(2d, d + 1) * (2d - 1)`:
`iter (stepMap Φ) (QPeriod (m + 2)) v*_d = v*_d` AND `∀ 0 < t < Q(d), iter (stepMap Φ) t v*_d ≠ v*_d`.
-/
theorem vtpr_universal_exact_minimal_period {m w : Nat} {Φ}
    (S : ValuationTowerSpec m w Φ 1#w) (hw : 4 ≤ w) :
    iter (stepMap Φ) (QPeriod (m + 2)) (universalWitness m w) = universalWitness m w ∧
    ∀ t : Nat, 0 < t → t < QPeriod (m + 2) →
      iter (stepMap Φ) t (universalWitness m w) ≠ universalWitness m w := by
  have hw1 : 1 ≤ w := by omega
  have hw2 : 2 ≤ w := by omega
  have h1_odd : (1#w).getLsbD 0 = true := S.c_odd hw1
  have h4_div4 : (4#w).getLsbD 0 = false ∧ (4#w).getLsbD 1 = false := by
    have := four_mul_div4 (1#w)
    simpa only [BitVec.mul_one] using this
  have h0_div4 : (0#w).getLsbD 0 = false ∧ (0#w).getLsbD 1 = false := by simp
  have he0_div4 : allDiv4 (witnessEven m w) := by
    intro i; simp only [witnessEven]; split
    · exact h4_div4
    · exact h0_div4
  have he0_ev : allEven (witnessEven m w) := fun i => (he0_div4 i).1
  have hv_eq : universalWitness m w = toEven 1#w (witnessEven m w) := by
    funext i
    simp only [universalWitness, toEven, witnessEven]
    split
    · simp
    · rfl
  have hv_prim : isPrimitive (universalWitness m w) := ⟨0, by simp [universalWitness, h1_odd]⟩
  have hv_sec : inSection (universalWitness m w) := by
    refine ⟨by simp [universalWitness, h1_odd], fun j => ?_⟩
    simp only [universalWitness, Fin.val_succ, Nat.succ_ne_zero, ite_false]
    split
    · exact h4_div4.1
    · exact h0_div4.1
  refine ⟨vtpr_primitive_period S hv_prim, ?_⟩
  intro t ht0 htlt hfix
  -- Step 1: Show `(2*(m+2) - 1) ∣ t`
  let P0 := 2 * (m + 2) - 1
  have hP0_pos : 0 < P0 := by omega
  have hret_iter : ∀ (r : Nat) (e : State m w), allEven e →
      iter (stepMap Φ) (P0 * r) (toEven 1#w e) = toEven 1#w (iter (poincareR Φ 1#w) r e) := by
    intro r
    induction r with
    | zero => intro e _; simp [iter]
    | succ r ih =>
      intro e he
      rw [Nat.mul_succ, Nat.add_comm, iter_add, poincare_return S hw1 he,
          iter_succ, ih (poincareR Φ 1#w e) (poincareR_preserve_allEven S he)]
  let q := t / P0
  let r := t % P0
  have ht_eq : t = P0 * q + r := (Nat.div_add_mod t P0).symm
  have hr_lt : r < P0 := Nat.mod_lt t hP0_pos
  have heq_ev_q : allEven (iter (poincareR Φ 1#w) q (witnessEven m w)) := by
    clear hfix
    induction q with
    | zero => exact he0_ev
    | succ n ih => rw [iter_succ_right]; exact poincareR_preserve_allEven S ih
  have hsec_q : inSection (toEven 1#w (iter (poincareR Φ 1#w) q (witnessEven m w))) := by
    refine ⟨?_, ?_⟩
    · simp only [toEven, Fin.val_zero, ite_true]
      rw [sub_getLsbD_zero, h1_odd, heq_ev_q 0]; rfl
    · intro j
      simp only [toEven, Fin.val_succ, Nat.succ_ne_zero, ite_false]
      exact heq_ev_q j.succ
  have hstep_r : iter (stepMap Φ) r (toEven 1#w (iter (poincareR Φ 1#w) q (witnessEven m w))) =
      universalWitness m w := by
    rw [← hret_iter q (witnessEven m w) he0_ev, ← hv_eq, ← iter_add, ← ht_eq, hfix]
  have hr0 : r = 0 := by
    by_cases hrz : r = 0
    · exact hrz
    · exfalso
      have hnot := not_inSection_step_pos_lt S hw1 hsec_q (by omega) hr_lt
      rw [hstep_r] at hnot
      exact hnot hv_sec
  have hq_pos : 0 < q := by
    apply Classical.byContradiction
    intro h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0, hr0, Nat.mul_zero, Nat.add_zero] at ht_eq
    omega
  have hq_fix : iter (poincareR Φ 1#w) q (witnessEven m w) = witnessEven m w := by
    rw [hr0, iter_zero, hv_eq] at hstep_r
    have := congrArg (toEven 1#w) hstep_r
    rwa [toEven_invol, toEven_invol] at this
  -- Step 2: Show `(m + 3) ∣ q`
  let s := q / (m + 3)
  let r' := q % (m + 3)
  have hq_eq : q = (m + 3) * s + r' := (Nat.div_add_mod q (m + 3)).symm
  have hr'_lt : r' < m + 3 := Nat.mod_lt q (by omega)
  have hdiv4_s : allDiv4 (iter monodromyM s (witnessEven m w)) := by
    clear hq_fix
    induction s with
    | zero => exact he0_div4
    | succ n ih => rw [iter_succ_right]; exact monodromyM_preserve_allDiv4 ih
  have hstep_r' : iter (poincareR Φ 1#w) r' (iter monodromyM s (witnessEven m w)) = witnessEven m w := by
    rw [← poincareR_iter_monodromyM S hw2 he0_div4 s, ← iter_add, ← hq_eq, hq_fix]
  have hr'0 : r' = 0 := by
    by_cases hrz : r' = 0
    · exact hrz
    · exfalso
      have hnot := not_allDiv4_poincareR_pos_lt S hw2 hdiv4_s (by omega) hr'_lt
      rw [hstep_r'] at hnot
      exact hnot he0_div4
  have hs_pos : 0 < s := by
    apply Classical.byContradiction
    intro h
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
    rw [hs0, hr'0, Nat.mul_zero, Nat.add_zero] at hq_eq
    omega
  have hs_fix : iter monodromyM s (witnessEven m w) = witnessEven m w := by
    rwa [hr'0, iter_zero] at hstep_r'
  -- Step 3: Show `(m + 2) ∣ s`, and `2 * (m + 2) ∣ s` if `(m + 2) % 2 = 0`!
  let p := s / (m + 2)
  let r'' := s % (m + 2)
  have hs_eq : s = (m + 2) * p + r'' := (Nat.div_add_mod s (m + 2)).symm
  have hr''_lt : r'' < m + 2 := Nat.mod_lt s (by omega)
  have hM_mul : ∀ (k : Nat),
      iter monodromyM ((m + 2) * k) (witnessEven m w) = witnessEven m w ∨
      iter monodromyM ((m + 2) * k) (witnessEven m w) = fun i => -(witnessEven m w i) := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Nat.mul_succ, iter_add]
      by_cases hev : (m + 2) % 2 = 0
      · rcases ih with h | h
        · rw [h, iter_monodromyM_d_even hev]; exact Or.inr rfl
        · rw [h, iter_monodromyM_d_even hev]; left; funext i; exact BitVec.neg_neg
      · rcases ih with h | h
        · rw [h, iter_monodromyM_d_odd hev]; exact Or.inl rfl
        · rw [h, iter_monodromyM_d_odd hev]; exact Or.inr rfl
  -- If `1 ≤ r'' ≤ m + 1`, then index `m + 1` of `iter monodromyM r'' (±e0)` is `0#w ≠ 4#w`!
  have hr''0 : r'' = 0 := by
    by_cases hrz : r'' = 0
    · exact hrz
    · exfalso
      have hpos : 1 ≤ r'' := by omega
      have hle : r'' ≤ m + 1 := by omega
      have h4_eq : iter monodromyM r'' (iter monodromyM ((m + 2) * p) (witnessEven m w)) ⟨m + 1, by omega⟩ = 4#w := by
        rw [← iter_add, ← hs_eq, hs_fix]
        simp [witnessEven]
      have hzero_shift : ∀ (v : State m w), (∀ i : Fin (m + 2), i.val < m + 1 → v i = 0#w) →
          iter negShift r'' v ⟨m + 1, by omega⟩ = 0#w := by
        intro v hv
        rw [iter_negShift_le v r'' ⟨hpos, hle⟩]
        dsimp only
        have hnotlt : ¬ (m + 1 < r'') := by omega
        by_cases heq : m + 1 = r''
        · simp [heq, hrz, hv 0 (by simp)]
        · simp [hnotlt, heq]
          exact hv ⟨m + 1 - r'', by omega⟩ (by dsimp only; omega)
      have hzero_M : ∀ (v : State m w), (∀ i : Fin (m + 2), i.val < m + 1 → v i = 0#w) →
          iter monodromyM r'' v ⟨m + 1, by omega⟩ = 0#w := by
        intro v hv
        rw [iter_monodromyM_eq]
        split
        · exact hzero_shift v hv
        · dsimp only; rw [hzero_shift v hv, BitVec.neg_zero]
      have h0_eq : iter monodromyM r'' (iter monodromyM ((m + 2) * p) (witnessEven m w)) ⟨m + 1, by omega⟩ = 0#w := by
        rcases hM_mul p with h | h
        · rw [h]; apply hzero_M; intro i hi; simp [witnessEven, show i.val ≠ m + 1 by omega]
        · rw [h]; apply hzero_M; intro i hi; simp [witnessEven, show i.val ≠ m + 1 by omega]
      rw [h0_eq] at h4_eq
      exact four_ne_zero_of_ge4 hw h4_eq.symm
  have hp_pos : 0 < p := by
    apply Classical.byContradiction
    intro h
    have hp0 : p = 0 := Nat.eq_zero_of_not_pos h
    rw [hp0, hr''0, Nat.mul_zero, Nat.add_zero] at hs_eq
    omega
  have ht_prod : t = P0 * ((m + 3) * ((m + 2) * p)) := by
    rw [ht_eq, hr0, hq_eq, hr'0, hs_eq, hr''0]
    simp only [Nat.add_zero]
  by_cases hev : (m + 2) % 2 = 0
  · -- When `d = m + 2` is even, `p` must be even (else `M^{dp}(e0) = -e0` gives `-4#w = 4#w`)!
    have hp_even : p % 2 = 0 := by
      by_cases hpe : p % 2 = 0
      · exact hpe
      · exfalso
        have hM_par : ∀ k : Nat,
            iter monodromyM ((m + 2) * k) (witnessEven m w) =
              if k % 2 = 0 then witnessEven m w else fun i => -(witnessEven m w i) := by
          intro k
          induction k with
          | zero => simp [iter]
          | succ k ih =>
            rw [Nat.mul_succ, iter_add, ih]
            by_cases hk : k % 2 = 0
            · have hk1 : ¬ ((k + 1) % 2 = 0) := by omega
              simp only [hk, hk1, ite_true, ite_false]
              exact iter_monodromyM_d_even hev _
            · have hk1 : (k + 1) % 2 = 0 := by omega
              simp only [hk, hk1, ite_false, ite_true]
              rw [iter_monodromyM_d_even hev]
              funext i; exact BitVec.neg_neg
        have hneg : iter monodromyM ((m + 2) * p) (witnessEven m w) = fun i => -(witnessEven m w i) := by
          rw [hM_par p]; simp only [hpe, ite_false]
        rw [hs_eq, hr''0, Nat.add_zero, hneg] at hs_fix
        have h4 := congrFun hs_fix ⟨m + 1, by omega⟩
        simp only [witnessEven, ite_true] at h4
        exact four_ne_neg_four_of_ge4 hw h4
    have hp_ge2 : 2 ≤ p := by omega
    have hQ_eq : QPeriod (m + 2) = P0 * ((m + 3) * ((m + 2) * 2)) := by
      simp only [QPeriod, QFactor, hev, ite_true, P0]
      have : 2 * (m + 2) * (m + 2 + 1) * (2 * (m + 2) - 1) =
             (2 * (m + 2) - 1) * ((m + 3) * ((m + 2) * 2)) := by
        rw [Nat.mul_comm (2 * (m + 2) * (m + 2 + 1)) (2 * (m + 2) - 1)]
        congr 1
        rw [show m + 2 + 1 = m + 3 by omega, Nat.mul_comm (2 * (m + 2)) (m + 3),
            Nat.mul_comm 2 (m + 2)]
      exact this
    have hle : QPeriod (m + 2) ≤ t := by
      rw [hQ_eq, ht_prod]
      exact Nat.mul_le_mul_left P0 (Nat.mul_le_mul_left (m + 3) (Nat.mul_le_mul_left (m + 2) hp_ge2))
    omega
  · -- When `d = m + 2` is odd, `p ≥ 1` immediately gives `Q(d) ≤ t`!
    have hQ_eq : QPeriod (m + 2) = P0 * ((m + 3) * ((m + 2) * 1)) := by
      simp only [QPeriod, QFactor, hev, ite_false, P0, Nat.mul_one]
      rw [Nat.mul_comm ((m + 2) * (m + 2 + 1)) (2 * (m + 2) - 1)]
      congr 1
      rw [show m + 2 + 1 = m + 3 by omega, Nat.mul_comm (m + 2) (m + 3)]
    have hle : QPeriod (m + 2) ≤ t := by
      rw [hQ_eq, ht_prod]
      exact Nat.mul_le_mul_left P0 (Nat.mul_le_mul_left (m + 3) (Nat.mul_le_mul_left (m + 2) hp_pos))
    omega

/-- Corollary: `v*_d` attains exact minimal period `Q(d)` for `twistedLSBStep 1#w` (`∀ d ≥ 2, ∀ w ≥ 4`). -/
theorem twistedLSB_exact_minimal_period (m w : Nat) (hw : 4 ≤ w) :
    iter (twistedLSBStep 1#w) (QPeriod (m + 2)) (universalWitness m w) = universalWitness m w ∧
    ∀ t : Nat, 0 < t → t < QPeriod (m + 2) →
      iter (twistedLSBStep 1#w) t (universalWitness m w) ≠ universalWitness m w :=
  vtpr_universal_exact_minimal_period
    (twistedLSB_towerSpec m w 1#w (fun hw1 => by
      rw [getLsbD_zero_iff_mod2, BitVec.toNat_ofNat]
      have h1lt : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
      rw [Nat.mod_eq_of_lt h1lt]))
    hw

/-- Corollary: `v*_d` attains exact minimal period `Q(d)` for `wildQuadPhi 1#w` (`∀ d ≥ 2, ∀ w ≥ 4`). -/
theorem wildQuad_exact_minimal_period (m w : Nat) (hw : 4 ≤ w) :
    iter (stepMap (wildQuadPhi 1#w)) (QPeriod (m + 2)) (universalWitness m w) = universalWitness m w ∧
    ∀ t : Nat, 0 < t → t < QPeriod (m + 2) →
      iter (stepMap (wildQuadPhi 1#w)) t (universalWitness m w) ≠ universalWitness m w :=
  vtpr_universal_exact_minimal_period
    (wildQuad_towerSpec m w 1#w (fun hw1 => by
      rw [getLsbD_zero_iff_mod2, BitVec.toNat_ofNat]
      have h1lt : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
      rw [Nat.mod_eq_of_lt h1lt]))
    hw

/-! ## Section 5: Kernel-Checked Non-Vacuity Witnesses & 6 Sharpness Counterexamples -/

/-- Non-vacuity witness 1: `ValuationTowerSpec` is inhabited by two genuinely distinct operators
    (one homogeneous LSB, one non-homogeneous quadratic `4 * ∑ y_j^2`)! -/
theorem nonvacuity_specs_distinct :
    Nonempty (ValuationTowerSpec 0 8 (twistedLSBPhi 3#8) 3#8) ∧
    Nonempty (ValuationTowerSpec 0 8 (wildQuadPhi 3#8) 3#8) ∧
    @twistedLSBPhi 0 8 3#8 (fun _ => 4#8) ≠ @wildQuadPhi 0 8 3#8 (fun _ => 4#8) := by
  refine ⟨⟨twistedLSB_towerSpec 0 8 3#8 (fun _ => by decide)⟩,
          ⟨wildQuad_towerSpec 0 8 3#8 (fun _ => by decide)⟩, ?_⟩
  decide

/-- Non-vacuity witness 2: `ValuationHomogeneousSpec` is constructively inhabited for all `m`. -/
theorem nonvacuity_homSpec (m : Nat) :
    Nonempty (ValuationHomogeneousSpec m
      (fun w => twistedLSBPhi (BitVec.ofNat w 3))
      (fun w => BitVec.ofNat w 3)) :=
  ⟨twistedLSB_homSpec m 3 (by decide)⟩

/-- Non-vacuity witness 3: Cross-bit carry propagation is genuinely active (not bit-parallel):
    changing bit 0 of `y` in `twistedLSBStep 1#8` flips bit 2 of the next state (`4#8` vs `1#8`)! -/
theorem nonvacuity_genuine_carry_coupling :
    let s1 : State 0 8 := fun i => if i.val = 0 then 0#8 else 4#8
    let s2 : State 0 8 := fun i => if i.val = 0 then 0#8 else 5#8
    (twistedLSBStep 1#8 s1 1).getLsbD 2 ≠ (twistedLSBStep 1#8 s2 1).getLsbD 2 := by
  decide

/-- Sharpness 1 (XOR instead of subtraction): `x_{n+2} = x_n ^^^ lsb(x_{n+1})` breaks `Q(2) = 36`!
    At `w = 3`, `(0, 7)` has period `27 = 3^3 ∤ 36`. -/
def xorPerturbStep {w : Nat} (p : BitVec w × BitVec w) : BitVec w × BitVec w :=
  (p.2, p.1 ^^^ lsb p.2)

theorem sharpness_xor_breaks_period36 :
    iter xorPerturbStep 36 (0#3, 7#3) ≠ (0#3, 7#3) ∧
    iter xorPerturbStep 27 (0#3, 7#3) = (0#3, 7#3) := by
  decide

/-- Sharpness 2 (Reversed sign `x_n - lsb(x_{n+1})`): breaks `Q(2) = 36` at `w = 4` (period `24 ∤ 36`)! -/
def revSignStep {w : Nat} (p : BitVec w × BitVec w) : BitVec w × BitVec w :=
  (p.2, p.1 - lsb p.2)

theorem sharpness_reversed_sign_breaks_period36 :
    iter revSignStep 36 (1#4, 2#4) ≠ (1#4, 2#4) ∧
    iter revSignStep 24 (1#4, 2#4) = (1#4, 2#4) := by
  have h12 : iter revSignStep 12 (1#4, 2#4) = (9#4, 10#4) := by decide
  have h12' : iter revSignStep 12 (9#4, 10#4) = (1#4, 2#4) := by decide
  have h24 : iter revSignStep 24 (1#4, 2#4) = (1#4, 2#4) := by
    rw [show 24 = 12 + 12 by rfl, iter_add, h12, h12']
  refine ⟨?_, h24⟩
  rw [show 36 = 24 + 12 by rfl, iter_add, h24, h12]
  decide

/-- Sharpness 3 (Even multiplier `c = 2`): breaks `Q(2) = 36` at `w = 6` (period `64 = 2^6`)! -/
def evenMultStep {w : Nat} (p : BitVec w × BitVec w) : BitVec w × BitVec w :=
  (p.2, 2#w * lsb p.2 - p.1)

theorem sharpness_even_multiplier_breaks_period36 :
    iter evenMultStep 36 (1#6, 2#6) ≠ (1#6, 2#6) ∧
    iter evenMultStep 64 (1#6, 2#6) = (1#6, 2#6) := by
  decide

/-- Sharpness 4 (AND instead of OR in 3D): `x_{n+3} = lsb(x_{n+1} &&& x_{n+2}) - x_n`
    breaks `Q(3) = 60` at `w = 3` (seed `(0, 3, 3)` has period `36 ∤ 60`)! -/
def andPerturbStep3D {w : Nat} (t : BitVec w × BitVec w × BitVec w) : BitVec w × BitVec w × BitVec w :=
  (t.2.1, t.2.2, lsb (t.2.1 &&& t.2.2) - t.1)

theorem sharpness_and_instead_of_or_breaks_period60 :
    iter andPerturbStep3D 60 (0#3, 3#3, 3#3) ≠ (0#3, 3#3, 3#3) ∧
    iter andPerturbStep3D 36 (0#3, 3#3, 3#3) = (0#3, 3#3, 3#3) := by
  decide

/-- Sharpness 5 (Breaking Level-≥2 sign-invariance): an operator satisfying Level-0 and Level-1
    pinning + Level-≥2 4-divisibility, but failing `Φ(-v) = Φ(v)`, breaks `Q(2) = 36` at `w = 5`! -/
def brokenSignStep {w : Nat} (p : BitVec w × BitVec w) : BitVec w × BitVec w :=
  let phi := if p.2.getLsbD 0 then 1#w else if p.2.getLsbD 1 then 2#w else p.2
  (p.2, phi - p.1)

theorem sharpness_broken_sign_invariance_breaks_period36 :
    iter brokenSignStep 36 (1#5, 4#5) ≠ (1#5, 4#5) ∧
    iter brokenSignStep 72 (1#5, 4#5) = (1#5, 4#5) := by
  decide

/-- Sharpness 6 (Width threshold `w ≥ 4` for even `d` is sharp): at `d = 2, w = 3`,
    the witness `(1, 4)` drops from period `36` to period `18` (because `4 ≡ -4 mod 8`)! -/
theorem sharpness_width_threshold_even_d :
    iter (twistedLSBStep 1#3) 18 (universalWitness 0 3) = universalWitness 0 3 := by
  funext i
  cases i using Fin.cases with
  | zero => decide
  | succ j =>
    cases j using Fin.cases with
    | zero => decide
    | succ k => exact Fin.elim0 k

end VTPR

/-! ## Section 6: Axiom Audit (`#print axioms` on all main theorems) -/




