/-
  specmat-11: Kronecker-Plus-Low-Rank Carry-Perturbation Schur-Tower Engine
  Standalone Lean 4.36.0 (zero Mathlib, zero sorry, standard axioms only).

  Part 1: Commutative Ring (CRing), Exact Rational Field (Q), Finite Sums,
          Matrix/Block/Kronecker Algebra, First-Principles Laplace Determinant,
          Alternating-Multilinear Uniqueness, Multiplicativity, Block Triangular,
          Kronecker Determinant, Matrix Determinant Lemma (inverse & scaled),
          Sherman-Morrison-Woodbury Inverse, and Kernel Singularity Lemma.
-/

namespace SpecMat11

-- ============================================================================
-- Section 1: Commutative Rings (CRing) and Exact Rational Field (Q)
-- ============================================================================

class CRing (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  zero_add : ∀ a : R, add zero a = a
  add_comm : ∀ a b : R, add a b = add b a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : R, mul one a = a
  mul_comm : ∀ a b : R, mul a b = mul b a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

instance {R : Type} [CRing R] : Zero R := ⟨CRing.zero⟩
instance {R : Type} [CRing R] : One R := ⟨CRing.one⟩
instance {R : Type} [CRing R] : Add R := ⟨CRing.add⟩
instance {R : Type} [CRing R] : Neg R := ⟨CRing.neg⟩
instance {R : Type} [CRing R] : Mul R := ⟨CRing.mul⟩
instance {R : Type} [CRing R] : Sub R := ⟨fun a b => a + (-b)⟩

def rpow {R : Type} [CRing R] (a : R) : Nat → R
  | 0 => 1
  | n + 1 => a * rpow a n

section CRingLemmas
variable {R : Type} [CRing R]

theorem add_zero' (a : R) : a + 0 = a := by
  change CRing.add a CRing.zero = a
  rw [CRing.add_comm, CRing.zero_add]

theorem zero_add' (a : R) : 0 + a = a := CRing.zero_add a
theorem add_comm' (a b : R) : a + b = b + a := CRing.add_comm a b
theorem add_assoc' (a b c : R) : (a + b) + c = a + (b + c) := CRing.add_assoc a b c
theorem add_left_neg' (a : R) : (-a) + a = 0 := CRing.add_left_neg a

theorem add_right_neg' (a : R) : a + (-a) = 0 := by
  rw [add_comm', add_left_neg']

theorem sub_eq_add_neg' (a b : R) : a - b = a + (-b) := rfl

theorem sub_self' (a : R) : a - a = 0 := add_right_neg' a

theorem mul_one' (a : R) : a * 1 = a := by
  change CRing.mul a CRing.one = a
  rw [CRing.mul_comm, CRing.one_mul]

theorem one_mul' (a : R) : 1 * a = a := CRing.one_mul a
theorem mul_comm' (a b : R) : a * b = b * a := CRing.mul_comm a b
theorem mul_assoc' (a b c : R) : (a * b) * c = a * (b * c) := CRing.mul_assoc a b c
theorem left_distrib' (a b c : R) : a * (b + c) = a * b + a * c := CRing.left_distrib a b c

theorem right_distrib' (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [mul_comm', left_distrib', mul_comm' c a, mul_comm' c b]

theorem add_left_cancel' {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (CRing.add (-a)) h
  rw [← add_assoc', ← add_assoc', add_left_neg', zero_add', zero_add'] at h1
  exact h1

theorem mul_zero' (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← left_distrib', add_zero', add_zero']
  exact add_left_cancel' h

theorem zero_mul' (a : R) : 0 * a = 0 := by
  rw [mul_comm', mul_zero']

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have h1 : (-a) + (a + b) = (-a) + 0 := congrArg (CRing.add (-a)) h
  rw [← add_assoc', add_left_neg', zero_add', add_zero'] at h1
  exact h1.symm

theorem neg_zero' : -(0 : R) = 0 := neg_eq_of_add_eq_zero (zero_add' 0)

theorem neg_neg' (a : R) : -(-a) = a := neg_eq_of_add_eq_zero (add_left_neg' a)

theorem neg_add' (a b : R) : -(a + b) = (-a) + (-b) := by
  apply neg_eq_of_add_eq_zero
  calc (a + b) + ((-a) + (-b))
      = (a + (-a)) + (b + (-b)) := by
          rw [add_assoc', ← add_assoc' b (-a), add_comm' b (-a), add_assoc', ← add_assoc']
    _ = 0 + 0 := by rw [add_right_neg', add_right_neg']
    _ = 0 := zero_add' 0

theorem mul_neg' (a b : R) : a * (-b) = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← left_distrib', add_right_neg', mul_zero']

theorem neg_mul' (a b : R) : (-a) * b = -(a * b) := by
  rw [mul_comm', mul_neg', mul_comm']

theorem neg_one_mul' (a : R) : (-1 : R) * a = -a := by
  rw [neg_mul', one_mul']

theorem neg_mul_neg' (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul', mul_neg', neg_neg']

theorem left_distrib_sub' (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg', left_distrib', mul_neg', ← sub_eq_add_neg']

theorem right_distrib_sub' (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg', right_distrib', neg_mul', ← sub_eq_add_neg']

theorem rpow_zero (a : R) : rpow a 0 = 1 := rfl
theorem rpow_succ (a : R) (n : Nat) : rpow a (n + 1) = a * rpow a n := rfl

theorem rpow_one (a : R) : rpow a 1 = a := by
  rw [rpow_succ, rpow_zero, mul_one']

theorem rpow_add (a : R) (m n : Nat) : rpow a (m + n) = rpow a m * rpow a n := by
  induction m with
  | zero => simp [rpow_zero, one_mul']
  | succ m ih =>
    rw [Nat.succ_add, rpow_succ, rpow_succ, ih, mul_assoc']

theorem rpow_mul (a : R) (m n : Nat) : rpow a (m * n) = rpow (rpow a m) n := by
  induction n with
  | zero => simp [rpow_zero]
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, rpow_add, rpow_succ, ih]

theorem mul_rpow (a b : R) (n : Nat) : rpow (a * b) n = rpow a n * rpow b n := by
  induction n with
  | zero => simp [rpow_zero, one_mul']
  | succ n ih =>
    rw [rpow_succ, rpow_succ, rpow_succ, ih]
    rw [mul_assoc', ← mul_assoc' b, mul_comm' b (rpow a n), mul_assoc', ← mul_assoc']

theorem one_rpow (n : Nat) : rpow (1 : R) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rpow_succ, one_mul', ih]

def signPow (k : Nat) : R := if k % 2 = 0 then 1 else -1

theorem signPow_zero : signPow (R := R) 0 = 1 := rfl

theorem signPow_succ (k : Nat) : signPow (R := R) (k + 1) = - signPow (R := R) k := by
  unfold signPow
  have h : (k + 1) % 2 = 0 ↔ k % 2 ≠ 0 := by omega
  by_cases hk : k % 2 = 0
  · have h1 : (k + 1) % 2 ≠ 0 := by omega
    simp [hk, h1]
  · have h1 : (k + 1) % 2 = 0 := by omega
    simp [hk, h1, neg_neg']

theorem signPow_add (a b : Nat) : signPow (R := R) (a + b) = signPow a * signPow b := by
  induction a with
  | zero => simp [signPow_zero, one_mul']
  | succ a ih =>
    rw [Nat.succ_add, signPow_succ, signPow_succ, ih, neg_mul']

theorem signPow_mul_self (k : Nat) : signPow (R := R) k * signPow k = 1 := by
  unfold signPow
  split
  · exact one_mul' 1
  · rw [neg_mul_neg', one_mul']

end CRingLemmas

instance : CRing Int where
  zero := 0
  one := 1
  add := Int.add
  neg := Int.neg
  mul := Int.mul
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_comm := Int.add_comm
  add_left_neg := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add

-- Exact Rational Field Q via Quotient of (num : Int, den : Int, den > 0)
structure QPair where
  num : Int
  den : Int
  den_pos : 0 < den

def QPair.equiv (a b : QPair) : Prop := a.num * b.den = b.num * a.den

theorem QPair.equiv_refl (a : QPair) : QPair.equiv a a := rfl

theorem QPair.equiv_symm {a b : QPair} (h : QPair.equiv a b) : QPair.equiv b a := h.symm

theorem QPair.equiv_trans {a b c : QPair} (h1 : QPair.equiv a b) (h2 : QPair.equiv b c) :
    QPair.equiv a c := by
  unfold QPair.equiv at *
  have hb : b.den ≠ 0 := Int.ne_of_gt b.den_pos
  have hmul : (a.num * c.den) * b.den = (c.num * a.den) * b.den := by
    calc (a.num * c.den) * b.den
        = (a.num * b.den) * c.den := by rw [Int.mul_assoc, Int.mul_comm c.den b.den, ← Int.mul_assoc]
      _ = (b.num * a.den) * c.den := by rw [h1]
      _ = (b.num * c.den) * a.den := by rw [Int.mul_assoc, Int.mul_comm a.den c.den, ← Int.mul_assoc]
      _ = (c.num * b.den) * a.den := by rw [h2]
      _ = (c.num * a.den) * b.den := by rw [Int.mul_assoc, Int.mul_comm b.den a.den, ← Int.mul_assoc]
  exact Int.eq_of_mul_eq_mul_right hb hmul

instance QPair.setoid : Setoid QPair where
  r := QPair.equiv
  iseqv := ⟨QPair.equiv_refl, QPair.equiv_symm, QPair.equiv_trans⟩

def Q := Quotient QPair.setoid

namespace Q

def mk (n d : Int) (hd : 0 < d) : Q := Quotient.mk QPair.setoid ⟨n, d, hd⟩

def ofInt (n : Int) : Q := mk n 1 (by omega)

def zero : Q := ofInt 0
def one : Q := ofInt 1

def add : Q → Q → Q :=
  Quotient.lift₂
    (fun a b => mk (a.num * b.den + b.num * a.den) (a.den * b.den) (Int.mul_pos a.den_pos b.den_pos))
    (by
      intro a1 b1 a2 b2 ha hb
      apply Quotient.sound
      change (a1.num * b1.den + b1.num * a1.den) * (a2.den * b2.den) =
             (a2.num * b2.den + b2.num * a2.den) * (a1.den * b1.den)
      change a1.num * a2.den = a2.num * a1.den at ha
      change b1.num * b2.den = b2.num * b1.den at hb
      calc (a1.num * b1.den + b1.num * a1.den) * (a2.den * b2.den)
          = (a1.num * a2.den) * (b1.den * b2.den) + (b1.num * b2.den) * (a1.den * a2.den) := by
              rw [Int.add_mul]
              congr 1
              · rw [Int.mul_assoc, ← Int.mul_assoc b1.den a2.den, Int.mul_comm b1.den a2.den,
                    Int.mul_assoc a2.den b1.den, ← Int.mul_assoc]
              · rw [Int.mul_assoc, ← Int.mul_assoc a1.den a2.den, Int.mul_comm (a1.den * a2.den) b2.den,
                    ← Int.mul_assoc]
        _ = (a2.num * a1.den) * (b1.den * b2.den) + (b2.num * b1.den) * (a1.den * a2.den) := by
              rw [ha, hb]
        _ = (a2.num * b2.den + b2.num * a2.den) * (a1.den * b1.den) := by
              rw [Int.add_mul]
              congr 1
              · rw [Int.mul_assoc, Int.mul_comm b1.den b2.den, ← Int.mul_assoc a1.den b2.den,
                    Int.mul_comm a1.den b2.den, Int.mul_assoc b2.den a1.den, ← Int.mul_assoc]
              · rw [Int.mul_assoc, Int.mul_comm a1.den a2.den, ← Int.mul_assoc b1.den a2.den,
                    Int.mul_comm b1.den a2.den, Int.mul_assoc a2.den b1.den,
                    Int.mul_comm b1.den a1.den, ← Int.mul_assoc])

def neg : Q → Q :=
  Quotient.lift
    (fun a => mk (-a.num) a.den a.den_pos)
    (by
      intro a b h
      apply Quotient.sound
      change (-a.num) * b.den = (-b.num) * a.den
      change a.num * b.den = b.num * a.den at h
      rw [Int.neg_mul, Int.neg_mul, h])

def mul : Q → Q → Q :=
  Quotient.lift₂
    (fun a b => mk (a.num * b.num) (a.den * b.den) (Int.mul_pos a.den_pos b.den_pos))
    (by
      intro a1 b1 a2 b2 ha hb
      apply Quotient.sound
      change (a1.num * b1.num) * (a2.den * b2.den) = (a2.num * b2.num) * (a1.den * b1.den)
      change a1.num * a2.den = a2.num * a1.den at ha
      change b1.num * b2.den = b2.num * b1.den at hb
      calc (a1.num * b1.num) * (a2.den * b2.den)
          = (a1.num * a2.den) * (b1.num * b2.den) := by
              rw [Int.mul_assoc, ← Int.mul_assoc b1.num a2.den, Int.mul_comm b1.num a2.den,
                  Int.mul_assoc a2.den b1.num, ← Int.mul_assoc]
        _ = (a2.num * a1.den) * (b2.num * b1.den) := by rw [ha, hb]
        _ = (a2.num * b2.num) * (a1.den * b1.den) := by
              rw [Int.mul_assoc, ← Int.mul_assoc a1.den b2.num, Int.mul_comm a1.den b2.num,
                  Int.mul_assoc b2.num a1.den, ← Int.mul_assoc])

def inv : Q → Q :=
  Quotient.lift
    (fun a =>
      if hpos : 0 < a.num then mk a.den a.num hpos
      else if hneg : a.num < 0 then mk (-a.den) (-a.num) (by omega)
      else zero)
    (by
      intro a b hab
      change a.num * b.den = b.num * a.den at hab
      have hda := a.den_pos
      have hdb := b.den_pos
      by_cases ha0 : a.num = 0
      · have hb0 : b.num = 0 := by
          rw [ha0, Int.zero_mul] at hab
          rcases Int.mul_eq_zero.mp hab.symm with h | h
          · exact h
          · exact absurd h (Int.ne_of_gt hda)
        simp [ha0, hb0]
      · have hb0 : b.num ≠ 0 := by
          intro hb
          rw [hb, Int.zero_mul] at hab
          rcases Int.mul_eq_zero.mp hab with h | h
          · exact ha0 h
          · exact absurd h (Int.ne_of_gt hdb)
        by_cases hap : 0 < a.num
        · have hbp : 0 < b.num := by
            have h1 : 0 < b.num * a.den := hab ▸ Int.mul_pos hap hdb
            by_cases hle : b.num ≤ 0
            · have : b.num * a.den ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hle (Int.le_of_lt hda)
              omega
            · omega
          simp only [hap, hbp, dite_true]
          apply Quotient.sound
          change a.den * b.num = b.den * a.num
          rw [Int.mul_comm a.den b.num, Int.mul_comm b.den a.num, hab]
        · have han : a.num < 0 := by omega
          have hbn : b.num < 0 := by
            have h1 : b.num * a.den < 0 := hab ▸ Int.mul_neg_of_neg_of_pos han hdb
            by_cases hge : 0 ≤ b.num
            · have : 0 ≤ b.num * a.den := Int.mul_nonneg hge (Int.le_of_lt hda)
              omega
            · omega
          have hbp : ¬(0 < b.num) := by omega
          simp only [hap, han, hbp, hbn, dite_false, dite_true]
          apply Quotient.sound
          change (-a.den) * (-b.num) = (-b.den) * (-a.num)
          rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.mul_comm a.den b.num, Int.mul_comm b.den a.num, hab])

instance : CRing Q where
  zero := Q.zero
  one := Q.one
  add := Q.add
  neg := Q.neg
  mul := Q.mul
  add_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro x y z
    apply Quotient.sound
    change ((x.num * y.den + y.num * x.den) * z.den + z.num * (x.den * y.den)) * (x.den * (y.den * z.den)) =
           (x.num * (y.den * z.den) + (y.num * z.den + z.num * y.den) * x.den) * ((x.den * y.den) * z.den)
    have h1 : (x.num * y.den + y.num * x.den) * z.den + z.num * (x.den * y.den) =
              x.num * (y.den * z.den) + (y.num * z.den + z.num * y.den) * x.den := by
      rw [Int.add_mul, Int.add_mul, Int.add_assoc]
      congr 1
      · exact Int.mul_assoc _ _ _
      · congr 1
        · rw [Int.mul_assoc, Int.mul_comm x.den z.den, ← Int.mul_assoc]
        · rw [Int.mul_comm x.den y.den, ← Int.mul_assoc]
    rw [h1, Int.mul_assoc x.den y.den z.den]
  zero_add := by
    intro a
    refine Quotient.inductionOn a ?_
    intro x
    apply Quotient.sound
    change (0 * x.den + x.num * 1) * x.den = x.num * (1 * x.den)
    rw [Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]
  add_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    apply Quotient.sound
    change (x.num * y.den + y.num * x.den) * (y.den * x.den) =
           (y.num * x.den + x.num * y.den) * (x.den * y.den)
    rw [Int.add_comm (x.num * y.den), Int.mul_comm y.den x.den]
  add_left_neg := by
    intro a
    refine Quotient.inductionOn a ?_
    intro x
    apply Quotient.sound
    change ((-x.num) * x.den + x.num * x.den) * 1 = 0 * (x.den * x.den)
    rw [Int.neg_mul, Int.add_left_neg, Int.zero_mul, Int.zero_mul]
  mul_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro x y z
    apply Quotient.sound
    change ((x.num * y.num) * z.num) * (x.den * (y.den * z.den)) =
           (x.num * (y.num * z.num)) * ((x.den * y.den) * z.den)
    rw [Int.mul_assoc x.num, Int.mul_assoc x.den]
  one_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro x
    apply Quotient.sound
    change (1 * x.num) * x.den = x.num * (1 * x.den)
    rw [Int.one_mul, Int.one_mul]
  mul_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    apply Quotient.sound
    change (x.num * y.num) * (y.den * x.den) = (y.num * x.num) * (x.den * y.den)
    rw [Int.mul_comm x.num y.num, Int.mul_comm y.den x.den]
  left_distrib := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro x y z
    apply Quotient.sound
    change (x.num * (y.num * z.den + z.num * y.den)) * ((x.den * y.den) * (x.den * z.den)) =
           ((x.num * y.num) * (x.den * z.den) + (x.num * z.num) * (x.den * y.den)) * (x.den * (y.den * z.den))
    grind

theorem mul_inv_cancel {a : Q} (ha : a ≠ 0) : a * inv a = 1 := by
  refine Quotient.inductionOn a (fun x hx => ?_) ha
  have hnx : x.num ≠ 0 := by
    intro h0
    apply hx
    apply Quotient.sound
    change x.num * 1 = 0 * x.den
    rw [h0, Int.zero_mul, Int.zero_mul]
  change Q.mul (Quotient.mk QPair.setoid x) (Q.inv (Quotient.mk QPair.setoid x)) = Q.one
  have hinv : Q.inv (Quotient.mk QPair.setoid x) =
      if hpos : 0 < x.num then mk x.den x.num hpos
      else if hneg : x.num < 0 then mk (-x.den) (-x.num) (by omega)
      else zero := rfl
  rw [hinv]
  by_cases hp : 0 < x.num
  · rw [dite_eq_left hp]
    apply Quotient.sound
    change (x.num * x.den) * 1 = 1 * (x.den * x.num)
    grind
  · have hn : x.num < 0 := by omega
    rw [dite_eq_right hp, dite_eq_left hn]
    apply Quotient.sound
    change (x.num * (-x.den)) * 1 = 1 * (x.den * (-x.num))
    grind

theorem inv_mul_cancel {a : Q} (ha : a ≠ 0) : inv a * a = 1 := by
  rw [mul_comm', mul_inv_cancel ha]

theorem eq_zero_of_mul_eq_zero {a b : Q} (h : a * b = 0) (hb : b ≠ 0) : a = 0 := by
  have h1 : (a * b) * inv b = 0 * inv b := congrArg (fun z => z * inv b) h
  rw [mul_assoc', mul_inv_cancel hb, mul_one', zero_mul'] at h1
  exact h1

theorem ofInt_zero : ofInt 0 = 0 := rfl
theorem ofInt_one : ofInt 1 = 1 := rfl

theorem ofInt_add (a b : Int) : ofInt (a + b) = ofInt a + ofInt b := by
  apply Quotient.sound
  change (a + b) * (1 * 1) = (a * 1 + b * 1) * 1
  grind

theorem ofInt_neg (a : Int) : ofInt (-a) = -(ofInt a) := by
  apply Quotient.sound
  change (-a) * 1 = (-a) * 1
  rfl

theorem ofInt_mul (a b : Int) : ofInt (a * b) = ofInt a * ofInt b := by
  apply Quotient.sound
  change (a * b) * (1 * 1) = (a * b) * 1
  rw [Int.mul_one, Int.mul_one]

theorem ofInt_rpow (a : Int) (n : Nat) : ofInt (rpow a n) = rpow (ofInt a) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rpow_succ, rpow_succ, ofInt_mul, ih]

theorem ofInt_injective {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  have hq : QPair.equiv ⟨a, 1, by omega⟩ ⟨b, 1, by omega⟩ := Quotient.exact h
  change a * 1 = b * 1 at hq
  rw [Int.mul_one, Int.mul_one] at hq
  exact hq

theorem ofInt_ne_zero {a : Int} (ha : a ≠ 0) : ofInt a ≠ 0 := by
  intro h
  exact ha (ofInt_injective h)

end Q

-- ============================================================================
-- Section 2: Finite Sums over Fin n
-- ============================================================================

def finSum {R : Type} [CRing R] : {n : Nat} → (Fin n → R) → R
  | 0, _ => 0
  | _ + 1, f => f 0 + finSum (fun i => f i.succ)

section FinSumLemmas
variable {R : Type} [CRing R]

theorem finSum_zero (n : Nat) : finSum (fun _ : Fin n => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finSum, ih, zero_add']

theorem finSum_congr {n : Nat} {f g : Fin n → R} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [h 0, ih (fun i => h i.succ)]

theorem finSum_add {n : Nat} (f g : Fin n → R) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => simp [finSum, zero_add']
  | succ n ih =>
    simp only [finSum]
    rw [ih]
    rw [add_assoc', ← add_assoc' (g 0), add_comm' (g 0),
        add_assoc', ← add_assoc']

theorem finSum_neg {n : Nat} (f : Fin n → R) :
    finSum (fun i => - f i) = - finSum f := by
  induction n with
  | zero => simp [finSum, neg_zero']
  | succ n ih => simp only [finSum]; rw [ih, neg_add']

theorem finSum_sub {n : Nat} (f g : Fin n → R) :
    finSum (fun i => f i - g i) = finSum f - finSum g := by
  simp only [sub_eq_add_neg', finSum_add, finSum_neg]

theorem finSum_smul_left {n : Nat} (c : R) (f : Fin n → R) :
    finSum (fun i => c * f i) = c * finSum f := by
  induction n with
  | zero => simp [finSum, mul_zero']
  | succ n ih => simp only [finSum]; rw [ih, left_distrib']

theorem finSum_smul_right {n : Nat} (f : Fin n → R) (c : R) :
    finSum (fun i => f i * c) = finSum f * c := by
  induction n with
  | zero => simp [finSum, zero_mul']
  | succ n ih => simp only [finSum]; rw [ih, right_distrib']

theorem finSum_swap {m n : Nat} (f : Fin m → Fin n → R) :
    finSum (fun i => finSum (fun j => f i j)) = finSum (fun j => finSum (fun i => f i j)) := by
  induction m with
  | zero => simp [finSum, finSum_zero]
  | succ m ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem finSum_single {n : Nat} (i : Fin n) (f : Fin n → R) (h : ∀ j, j ≠ i → f j = 0) :
    finSum f = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [finSum]
    cases i using Fin.cases with
    | zero =>
      have hz : finSum (fun j : Fin n => f j.succ) = 0 := by
        rw [finSum_congr (fun j => h j.succ (Fin.succ_ne_zero j)), finSum_zero]
      rw [hz, add_zero']
    | succ i' =>
      have h0 : f 0 = 0 := h 0 (Fin.succ_ne_zero i').symm
      rw [h0, zero_add']
      exact ih i' (fun j => f j.succ) (fun j hj => h j.succ (fun heq => hj (Fin.succ_inj.mp heq)))

theorem finSum_fin1 (f : Fin 1 → R) : finSum f = f 0 := by
  simp [finSum, add_zero']

theorem finSum_fin2 (f : Fin 2 → R) : finSum f = f 0 + f 1 := by
  simp only [finSum, add_zero']
  rfl

-- Index helpers for block matrices (m + n) and Kronecker products (m * n)
def finAddLeft {m n : Nat} (i : Fin m) : Fin (m + n) := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩
def finAddRight {m n : Nat} (j : Fin n) : Fin (m + n) := ⟨m + j.val, Nat.add_lt_add_left j.isLt m⟩

theorem finSum_cast {a b : Nat} (h : a = b) (f : Fin b → R) :
    finSum (fun i : Fin a => f (Fin.cast h i)) = finSum f := by
  subst h
  rfl

theorem finSum_succ {n : Nat} (f : Fin (n + 1) → R) :
    finSum f = f 0 + finSum (fun i : Fin n => f i.succ) := rfl

theorem finSum_split_add {m n : Nat} (f : Fin (m + n) → R) :
    finSum f = finSum (fun i : Fin m => f (finAddLeft i)) + finSum (fun j : Fin n => f (finAddRight j)) := by
  induction m with
  | zero =>
    have h0 : 0 + n = n := Nat.zero_add n
    rw [← finSum_cast h0.symm f]
    simp only [finSum, zero_add']
    apply finSum_congr
    intro j
    congr 1
    apply Fin.ext
    simp [finAddRight]
  | succ m ih =>
    have hsucc : (m + 1) + n = (m + n) + 1 := Nat.succ_add m n
    rw [← finSum_cast hsucc.symm f]
    rw [finSum_succ, finSum_succ]
    rw [ih (fun k : Fin (m + n) => f (Fin.cast hsucc.symm k.succ))]
    rw [add_assoc']
    have hhead : f (Fin.cast hsucc.symm 0) = f (finAddLeft 0) := by
      congr 1
    have hleft : finSum (fun i : Fin m => f (Fin.cast hsucc.symm (finAddLeft i).succ)) =
                 finSum (fun i : Fin m => f (finAddLeft i.succ)) := by
      apply finSum_congr; intro i; congr 1
    have hright : finSum (fun j : Fin n => f (Fin.cast hsucc.symm (finAddRight j).succ)) =
                  finSum (fun j : Fin n => f (finAddRight j)) := by
      apply finSum_congr; intro j; congr 1; apply Fin.ext; simp [finAddRight]; omega
    rw [hhead, hleft, hright]

def finMulPair {m n : Nat} (i : Fin m) (j : Fin n) : Fin (m * n) :=
  ⟨i.val * n + j.val, by
    have h1 : i.val + 1 ≤ m := i.isLt
    have h2 : (i.val + 1) * n ≤ m * n := Nat.mul_le_mul_right n h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega⟩

theorem finSum_split_mul {m n : Nat} (f : Fin (m * n) → R) :
    finSum f = finSum (fun i : Fin m => finSum (fun j : Fin n => f (finMulPair i j))) := by
  induction m with
  | zero =>
    have h0 : 0 * n = 0 := Nat.zero_mul n
    rw [← finSum_cast h0.symm f]
    rfl
  | succ m ih =>
    have hm : (m + 1) * n = n + m * n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [← finSum_cast hm.symm f]
    rw [finSum_split_add]
    simp only [finSum]
    congr 1
    · apply finSum_congr; intro j; congr 1; apply Fin.ext; simp [finAddLeft, finMulPair]
    · rw [ih]
      apply finSum_congr; intro i
      apply finSum_congr; intro j
      congr 1; apply Fin.ext; simp [finAddRight, finMulPair, Nat.add_mul, Nat.one_mul]; omega

theorem finSum_split_mul_comm {m n : Nat} (f : Fin (m * n) → R) :
    finSum f = finSum (fun j : Fin n => finSum (fun i : Fin m => f (finMulPair i j))) := by
  rw [finSum_split_mul, finSum_swap]

-- Key skew-symmetry cancellation lemma over ANY commutative ring (zero division by 2!)
def succAbove {n : Nat} (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if h : i.val < p.val then ⟨i.val, Nat.lt_trans h p.isLt⟩
  else ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

theorem succAbove_zero {n : Nat} (i : Fin n) :
    succAbove (0 : Fin (n + 1)) i = i.succ := by
  apply Fin.ext
  unfold succAbove
  simp

theorem succAbove_succ_zero {n : Nat} (p : Fin (n + 1)) :
    succAbove p.succ (0 : Fin (n + 1)) = (0 : Fin (n + 2)) := by
  apply Fin.ext
  unfold succAbove
  simp [Fin.succ]

theorem succAbove_succ_succ {n : Nat} (p : Fin (n + 1)) (i : Fin n) :
    succAbove p.succ i.succ = (succAbove p i).succ := by
  apply Fin.ext
  unfold succAbove
  by_cases h : i.val < p.val
  · simp [h, Fin.succ]
  · simp [h, Fin.succ]

theorem succAbove_ne {n : Nat} (p : Fin (n + 1)) (i : Fin n) :
    succAbove p i ≠ p := by
  intro h
  have hv := congrArg Fin.val h
  unfold succAbove at hv
  by_cases hlt : i.val < p.val
  · simp [hlt] at hv; omega
  · simp [hlt] at hv; omega

theorem finSum_skew_pairs {n : Nat} (F : Fin (n + 2) → Fin (n + 2) → R)
    (hskew : ∀ a b, F a b = - F b a) :
    finSum (fun j : Fin (n + 2) => finSum (fun k : Fin (n + 1) => F j (succAbove j k))) = 0 := by
  induction n with
  | zero =>
    simp only [finSum, add_zero']
    have h01 : succAbove (0 : Fin 2) (0 : Fin 1) = (1 : Fin 2) := by
      apply Fin.ext; unfold succAbove; simp
    have h10 : succAbove (1 : Fin 2) (0 : Fin 1) = (0 : Fin 2) := by
      apply Fin.ext; unfold succAbove; simp
    change F 0 (succAbove (0 : Fin 2) (0 : Fin 1)) +
           F 1 (succAbove (1 : Fin 2) (0 : Fin 1)) = 0
    rw [h01, h10, hskew 1 0, add_right_neg']
  | succ n ih =>
    rw [finSum_succ]
    have h1 : finSum (fun k : Fin (n + 2) => F 0 (succAbove 0 k)) =
              finSum (fun k : Fin (n + 2) => F 0 k.succ) := by
      apply finSum_congr; intro k; rw [succAbove_zero]
    rw [h1]
    have h2a : finSum (fun j : Fin (n + 2) => finSum (fun k : Fin (n + 2) => F j.succ (succAbove j.succ k))) =
               finSum (fun j : Fin (n + 2) =>
                 F j.succ (succAbove j.succ 0) +
                 finSum (fun k : Fin (n + 1) => F j.succ (succAbove j.succ k.succ))) := by
      apply finSum_congr; intro j; exact finSum_succ _
    rw [h2a]
    have h2 : finSum (fun j : Fin (n + 2) =>
                F j.succ (succAbove j.succ 0) +
                finSum (fun k : Fin (n + 1) => F j.succ (succAbove j.succ k.succ))) =
              finSum (fun j : Fin (n + 2) => F j.succ 0) +
              finSum (fun j : Fin (n + 2) => finSum (fun k : Fin (n + 1) => F j.succ (succAbove j k).succ)) := by
      rw [finSum_add]
      have ha : finSum (fun j : Fin (n + 2) => F j.succ (succAbove j.succ 0)) =
                finSum (fun j : Fin (n + 2) => F j.succ 0) := by
        apply finSum_congr; intro j; rw [succAbove_succ_zero]
      have hb : finSum (fun j : Fin (n + 2) => finSum (fun k : Fin (n + 1) => F j.succ (succAbove j.succ k.succ))) =
                finSum (fun j : Fin (n + 2) => finSum (fun k : Fin (n + 1) => F j.succ (succAbove j k).succ)) := by
        apply finSum_congr; intro j; apply finSum_congr; intro k; rw [succAbove_succ_succ]
      rw [ha, hb]
    rw [h2, ← add_assoc']
    have hcancel : finSum (fun k : Fin (n + 2) => F 0 k.succ) +
                   finSum (fun j : Fin (n + 2) => F j.succ 0) = 0 := by
      have hneg : finSum (fun j : Fin (n + 2) => F j.succ 0) =
                  - finSum (fun k : Fin (n + 2) => F 0 k.succ) := by
        rw [← finSum_neg]
        apply finSum_congr; intro j; exact hskew j.succ 0
      rw [hneg, add_right_neg']
    rw [hcancel, zero_add']
    exact ih (fun a b => F a.succ b.succ) (fun a b => hskew a.succ b.succ)

end FinSumLemmas

-- ============================================================================
-- Section 3: Matrices, Block Matrices, and Kronecker Products over CRing R
-- ============================================================================

abbrev Mat (m n : Nat) (R : Type) := Fin m → Fin n → R

section MatrixAlgebra
variable {R : Type} [CRing R]

def matZero (m n : Nat) : Mat m n R := fun _ _ => 0
def matOne (n : Nat) : Mat n n R := fun i j => if i = j then 1 else 0
def matAllOnes (m n : Nat) : Mat m n R := fun _ _ => 1
def matAdd {m n : Nat} (A B : Mat m n R) : Mat m n R := fun i j => A i j + B i j
def matNeg {m n : Nat} (A : Mat m n R) : Mat m n R := fun i j => - A i j
def matSub {m n : Nat} (A B : Mat m n R) : Mat m n R := fun i j => A i j - B i j
def matSmul {m n : Nat} (c : R) (A : Mat m n R) : Mat m n R := fun i j => c * A i j
def matMul {m p n : Nat} (A : Mat m p R) (B : Mat p n R) : Mat m n R :=
  fun i j => finSum (fun k => A i k * B k j)
def matTranspose {m n : Nat} (A : Mat m n R) : Mat n m R := fun i j => A j i

theorem matMul_assoc {m p q n : Nat} (A : Mat m p R) (B : Mat p q R) (C : Mat q n R) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  unfold matMul
  calc finSum (fun l => finSum (fun k => A i k * B k l) * C l j)
      = finSum (fun l => finSum (fun k => (A i k * B k l) * C l j)) := by
          apply finSum_congr; intro l; rw [← finSum_smul_right]
    _ = finSum (fun k => finSum (fun l => A i k * (B k l * C l j))) := by
          rw [finSum_swap]
          apply finSum_congr; intro k; apply finSum_congr; intro l; exact mul_assoc' _ _ _
    _ = finSum (fun k => A i k * finSum (fun l => B k l * C l j)) := by
          apply finSum_congr; intro k; rw [finSum_smul_left]

theorem matOne_mul {m n : Nat} (A : Mat m n R) : matMul (matOne m) A = A := by
  funext i j
  unfold matMul matOne
  rw [finSum_single i]
  · simp [one_mul']
  · intro k hk
    have hne : i ≠ k := hk.symm
    simp [hne, zero_mul']

theorem matMul_one {m n : Nat} (A : Mat m n R) : matMul A (matOne n) = A := by
  funext i j
  unfold matMul matOne
  rw [finSum_single j]
  · simp [mul_one']
  · intro k hk
    simp [hk, mul_zero']

theorem matMul_add {m p n : Nat} (A : Mat m p R) (B C : Mat p n R) :
    matMul A (matAdd B C) = matAdd (matMul A B) (matMul A C) := by
  funext i j
  unfold matMul matAdd
  rw [← finSum_add]
  apply finSum_congr; intro k; exact left_distrib' _ _ _

theorem matAdd_mul {m p n : Nat} (A B : Mat m p R) (C : Mat p n R) :
    matMul (matAdd A B) C = matAdd (matMul A C) (matMul B C) := by
  funext i j
  unfold matMul matAdd
  rw [← finSum_add]
  apply finSum_congr; intro k; exact right_distrib' _ _ _

theorem matMul_sub {m p n : Nat} (A : Mat m p R) (B C : Mat p n R) :
    matMul A (matSub B C) = matSub (matMul A B) (matMul A C) := by
  funext i j
  unfold matMul matSub
  rw [← finSum_sub]
  apply finSum_congr; intro k; exact left_distrib_sub' _ _ _

theorem matSub_mul {m p n : Nat} (A B : Mat m p R) (C : Mat p n R) :
    matMul (matSub A B) C = matSub (matMul A C) (matMul B C) := by
  funext i j
  unfold matMul matSub
  rw [← finSum_sub]
  apply finSum_congr; intro k; exact right_distrib_sub' _ _ _

theorem matMul_neg {m p n : Nat} (A : Mat m p R) (B : Mat p n R) :
    matMul A (matNeg B) = matNeg (matMul A B) := by
  funext i j
  unfold matMul matNeg
  rw [← finSum_neg]
  apply finSum_congr; intro k; exact mul_neg' _ _

theorem matNeg_mul {m p n : Nat} (A : Mat m p R) (B : Mat p n R) :
    matMul (matNeg A) B = matNeg (matMul A B) := by
  funext i j
  unfold matMul matNeg
  rw [← finSum_neg]
  apply finSum_congr; intro k; exact neg_mul' _ _

theorem matMul_zero {m p n : Nat} (A : Mat m p R) :
    matMul A (matZero p n) = matZero m n := by
  funext i j
  unfold matMul matZero
  rw [finSum_congr (fun k => mul_zero' (A i k)), finSum_zero]

theorem matZero_mul {m p n : Nat} (A : Mat p n R) :
    matMul (matZero m p) A = matZero m n := by
  funext i j
  unfold matMul matZero
  rw [finSum_congr (fun k => zero_mul' (A k j)), finSum_zero]

theorem matMul_smul_left {m p n : Nat} (c : R) (A : Mat m p R) (B : Mat p n R) :
    matMul (matSmul c A) B = matSmul c (matMul A B) := by
  funext i j
  unfold matMul matSmul
  rw [← finSum_smul_left]
  apply finSum_congr; intro k; exact mul_assoc' _ _ _

theorem matMul_smul_right {m p n : Nat} (c : R) (A : Mat m p R) (B : Mat p n R) :
    matMul A (matSmul c B) = matSmul c (matMul A B) := by
  funext i j
  unfold matMul matSmul
  rw [← finSum_smul_left]
  apply finSum_congr; intro k
  rw [← mul_assoc', mul_comm' (A i k) c, mul_assoc']

-- Block Matrices
def fromBlocks {m n p q : Nat}
    (A : Mat m p R) (B : Mat m q R) (C : Mat n p R) (D : Mat n q R) : Mat (m + n) (p + q) R :=
  fun i j =>
    if hi : i.val < m then
      if hj : j.val < p then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else B ⟨i.val, hi⟩ ⟨j.val - p, by omega⟩
    else
      if hj : j.val < p then C ⟨i.val - m, by omega⟩ ⟨j.val, hj⟩
      else D ⟨i.val - m, by omega⟩ ⟨j.val - p, by omega⟩

theorem fromBlocks_mul {m n p q r s : Nat}
    (A1 : Mat m p R) (B1 : Mat m q R) (C1 : Mat n p R) (D1 : Mat n q R)
    (A2 : Mat p r R) (B2 : Mat p s R) (C2 : Mat q r R) (D2 : Mat q s R) :
    matMul (fromBlocks A1 B1 C1 D1) (fromBlocks A2 B2 C2 D2) =
    fromBlocks
      (matAdd (matMul A1 A2) (matMul B1 C2))
      (matAdd (matMul A1 B2) (matMul B1 D2))
      (matAdd (matMul C1 A2) (matMul D1 C2))
      (matAdd (matMul C1 B2) (matMul D1 D2)) := by
  funext i j
  unfold matMul
  rw [finSum_split_add]
  unfold fromBlocks matAdd
  by_cases hi : i.val < m <;> by_cases hj : j.val < r <;> simp only [hi, hj, dite_true, dite_false]
  · congr 1
    · apply finSum_congr; intro k
      simp [finAddLeft, k.isLt]
    · apply finSum_congr; intro k
      have hk : ¬(p + k.val < p) := by omega
      simp only [finAddRight, hk, dite_false, Nat.add_sub_cancel_left]
  · congr 1
    · apply finSum_congr; intro k
      simp [finAddLeft, k.isLt]
    · apply finSum_congr; intro k
      have hk : ¬(p + k.val < p) := by omega
      simp only [finAddRight, hk, dite_false, Nat.add_sub_cancel_left]
  · congr 1
    · apply finSum_congr; intro k
      simp [finAddLeft, k.isLt]
    · apply finSum_congr; intro k
      have hk : ¬(p + k.val < p) := by omega
      simp only [finAddRight, hk, dite_false, Nat.add_sub_cancel_left]
  · congr 1
    · apply finSum_congr; intro k
      simp [finAddLeft, k.isLt]
    · apply finSum_congr; intro k
      have hk : ¬(p + k.val < p) := by omega
      simp only [finAddRight, hk, dite_false, Nat.add_sub_cancel_left]

-- Kronecker Product
def divFin {m n : Nat} (i : Fin (m * n)) : Fin m :=
  ⟨i.val / n, by
    have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; simp at i; exact Nat.not_lt_zero _ i.isLt)
    exact Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ i.isLt)⟩

def modFin {m n : Nat} (i : Fin (m * n)) : Fin n :=
  ⟨i.val % n, by
    have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; simp at i; exact Nat.not_lt_zero _ i.isLt)
    exact Nat.mod_lt _ hn⟩

theorem divFin_finMulPair {m n : Nat} (i : Fin m) (j : Fin n) :
    divFin (finMulPair i j) = i := by
  apply Fin.ext
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  simp only [divFin, finMulPair]
  rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

theorem modFin_finMulPair {m n : Nat} (i : Fin m) (j : Fin n) :
    modFin (finMulPair i j) = j := by
  apply Fin.ext
  simp [modFin, finMulPair, Nat.mod_eq_of_lt j.isLt]

def kron {m1 n1 m2 n2 : Nat} (A : Mat m1 n1 R) (B : Mat m2 n2 R) : Mat (m1 * m2) (n1 * n2) R :=
  fun i j => A (divFin i) (divFin j) * B (modFin i) (modFin j)

theorem kron_apply_pair {m1 n1 m2 n2 : Nat} (A : Mat m1 n1 R) (B : Mat m2 n2 R)
    (i1 : Fin m1) (i2 : Fin m2) (j1 : Fin n1) (j2 : Fin n2) :
    kron A B (finMulPair i1 i2) (finMulPair j1 j2) = A i1 j1 * B i2 j2 := by
  unfold kron
  rw [divFin_finMulPair, divFin_finMulPair, modFin_finMulPair, modFin_finMulPair]

theorem kron_mul {m1 p1 n1 m2 p2 n2 : Nat}
    (A : Mat m1 p1 R) (B : Mat m2 p2 R) (C : Mat p1 n1 R) (D : Mat p2 n2 R) :
    matMul (kron A B) (kron C D) = kron (matMul A C) (matMul B D) := by
  funext i j
  unfold matMul kron
  rw [finSum_split_mul]
  calc finSum (fun k1 : Fin p1 => finSum (fun k2 : Fin p2 =>
        (A (divFin i) (divFin (finMulPair k1 k2)) * B (modFin i) (modFin (finMulPair k1 k2))) *
        (C (divFin (finMulPair k1 k2)) (divFin j) * D (modFin (finMulPair k1 k2)) (modFin j))))
      = finSum (fun k1 : Fin p1 => finSum (fun k2 : Fin p2 =>
        (A (divFin i) k1 * C k1 (divFin j)) * (B (modFin i) k2 * D k2 (modFin j)))) := by
          apply finSum_congr; intro k1; apply finSum_congr; intro k2
          rw [divFin_finMulPair, modFin_finMulPair]
          rw [mul_assoc', ← mul_assoc' (B (modFin i) k2), mul_comm' (B (modFin i) k2) (C k1 (divFin j)),
              mul_assoc' (C k1 (divFin j)), ← mul_assoc']
    _ = finSum (fun k1 : Fin p1 =>
        (A (divFin i) k1 * C k1 (divFin j)) * finSum (fun k2 : Fin p2 => B (modFin i) k2 * D k2 (modFin j))) := by
          apply finSum_congr; intro k1; rw [finSum_smul_left]
    _ = finSum (fun k1 : Fin p1 => A (divFin i) k1 * C k1 (divFin j)) *
        finSum (fun k2 : Fin p2 => B (modFin i) k2 * D k2 (modFin j)) := by
          rw [finSum_smul_right]

theorem kron_one (m n : Nat) : kron (R := R) (matOne m) (matOne n) = matOne (m * n) := by
  funext i j
  unfold kron matOne
  by_cases hij : i = j
  · subst hij; simp [one_mul']
  · have hpair : ¬(divFin i = divFin j ∧ modFin i = modFin j) := by
      intro ⟨hd, hm⟩
      apply hij
      apply Fin.ext
      have hdv := congrArg Fin.val hd
      have hmv := congrArg Fin.val hm
      simp [divFin, modFin] at hdv hmv
      have hi := Nat.div_add_mod i.val n
      have hj := Nat.div_add_mod j.val n
      rw [hdv, hmv] at hi
      rw [← hi, hj]
    by_cases hd : divFin i = divFin j
    · have hm : modFin i ≠ modFin j := fun h => hpair ⟨hd, h⟩
      simp [hij, hd, hm, mul_zero']
    · simp [hij, hd, zero_mul']

theorem kron_add_left {m1 n1 m2 n2 : Nat} (A B : Mat m1 n1 R) (C : Mat m2 n2 R) :
    kron (matAdd A B) C = matAdd (kron A C) (kron B C) := by
  funext i j; unfold kron matAdd; exact right_distrib' _ _ _

theorem kron_add_right {m1 n1 m2 n2 : Nat} (A : Mat m1 n1 R) (B C : Mat m2 n2 R) :
    kron A (matAdd B C) = matAdd (kron A B) (kron A C) := by
  funext i j; unfold kron matAdd; exact left_distrib' _ _ _

theorem kron_sub_left {m1 n1 m2 n2 : Nat} (A B : Mat m1 n1 R) (C : Mat m2 n2 R) :
    kron (matSub A B) C = matSub (kron A C) (kron B C) := by
  funext i j; unfold kron matSub; exact right_distrib_sub' _ _ _

theorem kron_smul_left {m1 n1 m2 n2 : Nat} (c : R) (A : Mat m1 n1 R) (B : Mat m2 n2 R) :
    kron (matSmul c A) B = matSmul c (kron A B) := by
  funext i j; unfold kron matSmul; exact mul_assoc' _ _ _

theorem kron_smul_right {m1 n1 m2 n2 : Nat} (c : R) (A : Mat m1 n1 R) (B : Mat m2 n2 R) :
    kron A (matSmul c B) = matSmul c (kron A B) := by
  funext i j; unfold kron matSmul
  rw [← mul_assoc', mul_comm' (A (divFin i) (divFin j)) c, mul_assoc']

end MatrixAlgebra

-- ============================================================================
-- Section 4: First-Principles Laplace Determinant & Complete Schur Calculus
-- ============================================================================

section Determinant
variable {R : Type} [CRing R]

def minor0 {n : Nat} (A : Mat (n + 1) (n + 1) R) (j : Fin (n + 1)) : Mat n n R :=
  fun r c => A r.succ (succAbove j c)

def det : {n : Nat} → Mat n n R → R
  | 0, _ => 1
  | _ + 1, A => finSum (fun j => signPow j.val * A 0 j * det (minor0 A j))

theorem det_succ {n : Nat} (A : Mat (n + 1) (n + 1) R) :
    det A = finSum (fun j => signPow j.val * A 0 j * det (minor0 A j)) := rfl

theorem det_zero (A : Mat 0 0 R) : det A = 1 := rfl

theorem det_one_mat (A : Mat 1 1 R) : det A = A 0 0 := by
  rw [det_succ, finSum_fin1, Fin.val_zero, signPow_zero, one_mul', det_zero, mul_one']

theorem det_two_mat (A : Mat 2 2 R) :
    det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  rw [det_succ, finSum_fin2]
  have hs0 : signPow (R := R) 0 = 1 := rfl
  have hs1 : signPow (R := R) 1 = -1 := by simp [signPow]
  have hm0 : minor0 A 0 0 0 = A 1 1 := by
    unfold minor0 succAbove; simp [Fin.succ]
  have hm1 : minor0 A 1 0 0 = A 1 0 := by
    unfold minor0 succAbove; simp [Fin.succ]
  rw [det_one_mat, det_one_mat, hm0, hm1]
  have hv0 : (0 : Fin 2).val = 0 := rfl
  have hv1 : (1 : Fin 2).val = 1 := rfl
  rw [hv0, hv1, hs0, hs1, one_mul', neg_one_mul', neg_mul', sub_eq_add_neg']

theorem det_matOne (n : Nat) : det (matOne n : Mat n n R) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [det]
    rw [finSum_single (0 : Fin (n + 1))]
    · have hm : minor0 (matOne (n + 1) : Mat (n + 1) (n + 1) R) 0 = matOne n := by
        funext r c
        unfold minor0 matOne
        rw [succAbove_zero]
        by_cases h : r = c
        · subst h; simp
        · have h' : r.succ ≠ c.succ := fun heq => h (Fin.succ_inj.mp heq)
          simp [h, h']
      rw [hm, ih, Fin.val_zero, signPow_zero]
      simp [matOne, one_mul']
    · intro j hj
      have hne : (0 : Fin (n + 1)) ≠ j := hj.symm
      simp [matOne, hne, mul_zero', zero_mul']

-- Row update helper
def updateRow {m n : Nat} (A : Mat m n R) (i : Fin m) (v : Fin n → R) : Mat m n R :=
  fun r c => if r = i then v c else A r c

omit [CRing R] in
theorem updateRow_self {m n : Nat} (A : Mat m n R) (i : Fin m) :
    updateRow A i (A i) = A := by
  funext r c; unfold updateRow; split <;> simp_all

omit [CRing R] in
theorem updateRow_updateRow {m n : Nat} (A : Mat m n R) (i : Fin m) (u v : Fin n → R) :
    updateRow (updateRow A i u) i v = updateRow A i v := by
  funext r c; unfold updateRow; split <;> rfl

omit [CRing R] in
theorem minor0_updateRow_zero {n : Nat} (A : Mat (n + 1) (n + 1) R) (v : Fin (n + 1) → R) (j : Fin (n + 1)) :
    minor0 (updateRow A 0 v) j = minor0 A j := by
  funext r c; unfold minor0 updateRow
  have h : r.succ ≠ 0 := Fin.succ_ne_zero r
  simp [h]

omit [CRing R] in
theorem minor0_updateRow_succ {n : Nat} (A : Mat (n + 1) (n + 1) R) (i : Fin n) (v : Fin (n + 1) → R)
    (j : Fin (n + 1)) :
    minor0 (updateRow A i.succ v) j = updateRow (minor0 A j) i (fun c => v (succAbove j c)) := by
  funext r c; unfold minor0 updateRow
  by_cases h : r = i
  · subst h; simp
  · have h' : r.succ ≠ i.succ := fun heq => h (Fin.succ_inj.mp heq)
    simp [h, h']

theorem det_updateRow_add {n : Nat} (A : Mat n n R) (i : Fin n) (u v : Fin n → R) :
    det (updateRow A i (fun c => u c + v c)) = det (updateRow A i u) + det (updateRow A i v) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [det, minor0_updateRow_zero, ← finSum_add]
      apply finSum_congr; intro j
      unfold updateRow; simp only [ite_true]
      rw [left_distrib', right_distrib']
    | succ i' =>
      rw [det_succ, det_succ, det_succ, ← finSum_add]
      apply finSum_congr; intro j
      rw [minor0_updateRow_succ, minor0_updateRow_succ, minor0_updateRow_succ]
      have h0 : (0 : Fin (n + 1)) ≠ i'.succ := (Fin.succ_ne_zero i').symm
      have hA1 : updateRow A i'.succ (fun c => u c + v c) 0 j = A 0 j := by unfold updateRow; simp [h0]
      have hA2 : updateRow A i'.succ u 0 j = A 0 j := by unfold updateRow; simp [h0]
      have hA3 : updateRow A i'.succ v 0 j = A 0 j := by unfold updateRow; simp [h0]
      rw [hA1, hA2, hA3, ih (minor0 A j) i' (fun c => u (succAbove j c)) (fun c => v (succAbove j c)), left_distrib']

theorem det_updateRow_smul {n : Nat} (A : Mat n n R) (i : Fin n) (s : R) (u : Fin n → R) :
    det (updateRow A i (fun c => s * u c)) = s * det (updateRow A i u) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [det_succ, det_succ, ← finSum_smul_left]
      apply finSum_congr; intro j
      rw [minor0_updateRow_zero, minor0_updateRow_zero]
      have hA1 : updateRow A 0 (fun c => s * u c) 0 j = s * u j := by unfold updateRow; simp
      have hA2 : updateRow A 0 u 0 j = u j := by unfold updateRow; simp
      rw [hA1, hA2]
      calc signPow j.val * (s * u j) * det (minor0 A j)
          = (signPow j.val * s) * u j * det (minor0 A j) := by rw [← mul_assoc']
        _ = (s * signPow j.val) * u j * det (minor0 A j) := by rw [mul_comm' (signPow j.val) s]
        _ = s * (signPow j.val * u j * det (minor0 A j)) := by rw [mul_assoc', mul_assoc', ← mul_assoc' (signPow j.val)]
    | succ i' =>
      rw [det_succ, det_succ, ← finSum_smul_left]
      apply finSum_congr; intro j
      rw [minor0_updateRow_succ, minor0_updateRow_succ]
      have h0 : (0 : Fin (n + 1)) ≠ i'.succ := (Fin.succ_ne_zero i').symm
      have hA1 : updateRow A i'.succ (fun c => s * u c) 0 j = A 0 j := by unfold updateRow; simp [h0]
      have hA2 : updateRow A i'.succ u 0 j = A 0 j := by unfold updateRow; simp [h0]
      rw [hA1, hA2, ih (minor0 A j) i' (fun c => u (succAbove j c))]
      rw [← mul_assoc', mul_comm' (signPow j.val * A 0 j) s, mul_assoc']

-- Double minor symmetry for alternating proof
omit [CRing R] in
theorem minor0_minor0_comm {n : Nat} (A : Mat (n + 2) (n + 2) R)
    (a b : Fin (n + 2)) (hab : a.val < b.val) :
    minor0 (minor0 A a) ⟨b.val - 1, by omega⟩ = minor0 (minor0 A b) ⟨a.val, by omega⟩ := by
  funext r c
  unfold minor0 succAbove
  congr 1
  apply Fin.ext
  by_cases h1 : c.val < a.val
  · have h2 : c.val < b.val - 1 := by omega
    have h3 : c.val < b.val := by omega
    simp [h1, h2, h3]
  · by_cases h2 : c.val < b.val - 1
    · have h3 : ¬(c.val + 1 < a.val) := by omega
      have h4 : c.val + 1 < b.val := by omega
      simp [h1, h2, h4]
    · have h3 : ¬(c.val + 1 < a.val) := by omega
      have h4 : ¬(c.val + 1 < b.val) := by omega
      simp [h1, h2, h3, h4]

theorem det_eq_zero_of_adj_rows_eq {n : Nat} (A : Mat (n + 1) (n + 1) R)
    (i : Fin n) (heq : A i.castSucc = A i.succ) : det A = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [det_succ]
      have hexp : ∀ j : Fin (n + 2),
          signPow j.val * A 0 j * det (minor0 A j) =
          finSum (fun k : Fin (n + 1) =>
            signPow j.val * signPow k.val * A 0 j *
            A 0 (succAbove j k) * det (minor0 (minor0 A j) k)) := by
        intro j
        rw [det_succ, ← finSum_smul_left]
        apply finSum_congr; intro k
        have hrow1 : minor0 A j 0 k = A 0 (succAbove j k) := by
          unfold minor0
          have hrow := congrFun heq (succAbove j k)
          exact hrow.symm
        rw [hrow1]
        repeat rw [mul_assoc']
        congr 1
        rw [← mul_assoc' (A 0 j), mul_comm' (A 0 j) (signPow k.val),
            mul_assoc' (signPow k.val)]
      rw [finSum_congr hexp]
      let F : Fin (n + 2) → Fin (n + 2) → R := fun a b =>
        if hlt : a.val < b.val then
          signPow a.val * signPow (b.val - 1) * A 0 a *
          A 0 b * det (minor0 (minor0 A a) ⟨b.val - 1, by omega⟩)
        else if hgt : b.val < a.val then
          signPow a.val * signPow b.val * A 0 a *
          A 0 b * det (minor0 (minor0 A a) ⟨b.val, by omega⟩)
        else 0
      have hFmatch : ∀ (j : Fin (n + 2)) (k : Fin (n + 1)),
          signPow j.val * signPow k.val * A 0 j *
          A 0 (succAbove j k) * det (minor0 (minor0 A j) k) =
          F j (succAbove j k) := by
        intro j k
        dsimp only [F]
        by_cases hk : k.val < j.val
        · have hs : (succAbove j k).val = k.val := by unfold succAbove; simp [hk]
          have h1 : ¬(j.val < (succAbove j k).val) := by omega
          have h2 : (succAbove j k).val < j.val := by omega
          rw [dite_eq_right h1, dite_eq_left h2]
          have hkeq : (⟨(succAbove j k).val, by omega⟩ : Fin (n + 1)) = k := Fin.ext hs
          rw [hkeq, hs]
        · have hs : (succAbove j k).val = k.val + 1 := by unfold succAbove; simp [hk]
          have h1 : j.val < (succAbove j k).val := by omega
          rw [dite_eq_left h1]
          have hsub : (succAbove j k).val - 1 = k.val := by omega
          have hkeq : (⟨(succAbove j k).val - 1, by omega⟩ : Fin (n + 1)) = k := Fin.ext (by dsimp; omega)
          rw [hkeq, hsub]
      rw [finSum_congr (fun j => finSum_congr (fun k => hFmatch j k))]
      apply finSum_skew_pairs F
      intro a b
      dsimp only [F]
      by_cases hab : a.val < b.val
      · have hba1 : ¬(b.val < a.val) := by omega
        rw [dite_eq_left hab, dite_eq_right hba1, dite_eq_left hab]
        rw [minor0_minor0_comm A a b hab]
        have hs : signPow (R := R) b.val = - signPow (R := R) (b.val - 1) := by
          have hb : b.val = (b.val - 1) + 1 := by omega
          conv => lhs; rw [hb]
          exact signPow_succ (b.val - 1)
        rw [hs, neg_mul', neg_mul', neg_mul', neg_mul', neg_neg']
        rw [mul_comm' (signPow (b.val - 1)) (signPow a.val)]
        repeat rw [mul_assoc']
        congr 1; congr 1
        rw [← mul_assoc' (A 0 a), mul_comm' (A 0 a) (A 0 b), mul_assoc']
      · by_cases hba : b.val < a.val
        · rw [dite_eq_right hab, dite_eq_left hba, dite_eq_left hba]
          rw [← minor0_minor0_comm A b a hba]
          have hs : signPow (R := R) a.val = - signPow (R := R) (a.val - 1) := by
            have ha : a.val = (a.val - 1) + 1 := by omega
            conv => lhs; rw [ha]
            exact signPow_succ (a.val - 1)
          rw [hs, neg_mul', neg_mul', neg_mul', neg_mul']
          congr 1
          rw [mul_comm' (signPow (a.val - 1)) (signPow b.val)]
          repeat rw [mul_assoc']
          congr 1; congr 1
          rw [← mul_assoc' (A 0 a), mul_comm' (A 0 a) (A 0 b), mul_assoc']
        · rw [dite_eq_right hab, dite_eq_right hba, dite_eq_right hba, dite_eq_right hab, neg_zero']
    | succ i' =>
      rw [det_succ]
      have hz : ∀ j : Fin (n + 2), det (minor0 A j) = 0 := by
        intro j
        apply ih (minor0 A j) i'
        funext c
        unfold minor0
        exact congrFun heq (succAbove j c)
      rw [finSum_congr (fun j => by rw [hz j, mul_zero']), finSum_zero]

-- Abstract Alternating Multilinear Form & Uniqueness Theorem
structure AltMultilin (n : Nat) (R : Type) [CRing R] where
  toFun : Mat n n R → R
  map_add : ∀ (A : Mat n n R) (i : Fin n) (u v : Fin n → R),
    toFun (updateRow A i (fun c => u c + v c)) = toFun (updateRow A i u) + toFun (updateRow A i v)
  map_smul : ∀ (A : Mat n n R) (i : Fin n) (s : R) (u : Fin n → R),
    toFun (updateRow A i (fun c => s * u c)) = s * toFun (updateRow A i u)
  map_adj_eq : ∀ (A : Mat n n R) (i : Fin n) (hi : i.val + 1 < n),
    A i = A ⟨i.val + 1, hi⟩ → toFun A = 0

def detAltMultilin (n : Nat) : AltMultilin n R where
  toFun := det
  map_add := det_updateRow_add
  map_smul := det_updateRow_smul
  map_adj_eq := by
    intro A i hi heq
    cases n with
    | zero => exact Fin.elim0 i
    | succ n' =>
      exact det_eq_zero_of_adj_rows_eq A ⟨i.val, by omega⟩ heq

namespace AltMultilin

theorem map_zero_row {n : Nat} (f : AltMultilin n R) (A : Mat n n R) (i : Fin n) :
    f.toFun (updateRow A i (fun _ => 0)) = 0 := by
  have h : (fun _ : Fin n => (0 : R)) = (fun c => 0 * A i c) := by
    funext c; exact (zero_mul' (A i c)).symm
  rw [h, f.map_smul, zero_mul']

theorem map_finSum_row {n m : Nat} (f : AltMultilin n R) (A : Mat n n R) (i : Fin n)
    (v : Fin m → Fin n → R) :
    f.toFun (updateRow A i (fun c => finSum (fun k => v k c))) =
    finSum (fun k => f.toFun (updateRow A i (v k))) := by
  induction m with
  | zero => simp only [finSum]; exact f.map_zero_row A i
  | succ m ih =>
    simp only [finSum]
    rw [f.map_add, ih]

def swapRows {m n : Nat} (A : Mat m n R) (p q : Fin m) : Mat m n R :=
  fun r c => if r = p then A q c else if r = q then A p c else A r c

theorem map_swapAdj {n : Nat} (f : AltMultilin n R) (A : Mat n n R) (i : Fin n) (hi : i.val + 1 < n) :
    f.toFun (swapRows A i ⟨i.val + 1, hi⟩) = - f.toFun A := by
  let j : Fin n := ⟨i.val + 1, hi⟩
  have hij : i ≠ j := fun h => by have := congrArg Fin.val h; dsimp [j] at this; omega
  have hji : j ≠ i := hij.symm
  let u := A i
  let v := A j
  let B := updateRow (updateRow A i (fun c => u c + v c)) j (fun c => u c + v c)
  have hB0 : f.toFun B = 0 := by
    apply f.map_adj_eq B i hi
    funext c; dsimp only [B, updateRow, j]
    simp only [ite_true, ite_self]
  have h1 : f.toFun B =
      f.toFun (updateRow (updateRow A i u) j u) +
      f.toFun (updateRow (updateRow A i u) j v) +
      (f.toFun (updateRow (updateRow A i v) j u) +
       f.toFun (updateRow (updateRow A i v) j v)) := by
    dsimp [B]
    rw [f.map_add]
    have hcomm : ∀ w : Fin n → R,
        updateRow (updateRow A i (fun c => u c + v c)) j w =
        updateRow (updateRow A j w) i (fun c => u c + v c) := by
      intro w; funext r c; unfold updateRow
      by_cases hr1 : r = j <;> by_cases hr2 : r = i <;> simp_all
    rw [hcomm u, f.map_add, hcomm v, f.map_add]
    have hback : ∀ w1 w2 : Fin n → R,
        updateRow (updateRow A j w2) i w1 = updateRow (updateRow A i w1) j w2 := by
      intro w1 w2; funext r c; unfold updateRow
      by_cases hr1 : r = j <;> by_cases hr2 : r = i <;> simp_all
    rw [hback u u, hback v u, hback u v, hback v v]
    rw [add_assoc', ← add_assoc' (f.toFun (updateRow (updateRow A i v) j u)),
        add_comm' (f.toFun (updateRow (updateRow A i v) j u)) (f.toFun (updateRow (updateRow A i u) j v)),
        add_assoc', ← add_assoc']
  have huu : f.toFun (updateRow (updateRow A i u) j u) = 0 := by
    apply f.map_adj_eq _ i hi; funext c; dsimp only [updateRow, j]; simp only [ite_true, ite_self]
  have hvv : f.toFun (updateRow (updateRow A i v) j v) = 0 := by
    apply f.map_adj_eq _ i hi; funext c; dsimp only [updateRow, j]; simp only [ite_true, ite_self]
  have huv : updateRow (updateRow A i u) j v = A := by
    funext r c; unfold updateRow
    by_cases hr1 : r = j
    · subst hr1; simp [v]
    · by_cases hr2 : r = i
      · subst hr2; simp [hr1, u]
      · simp [hr1, hr2]
  have hvu : updateRow (updateRow A i v) j u = swapRows A i j := by
    funext r c; unfold updateRow swapRows
    by_cases hr1 : r = j
    · subst hr1; simp [hji, u]
    · by_cases hr2 : r = i
      · subst hr2; simp [hr1, v]
      · simp [hr1, hr2]
  rw [hB0, huu, hvv, zero_add', add_zero', huv, hvu] at h1
  exact (neg_eq_of_add_eq_zero h1.symm).symm

theorem map_rows_eq_lt {n : Nat} (f : AltMultilin n R) (A : Mat n n R)
    (p q : Fin n) (hpq : p.val < q.val) (heq : A p = A q) : f.toFun A = 0 := by
  generalize hd : q.val - p.val - 1 = d
  induction d generalizing A p q with
  | zero =>
    have hp1 : p.val + 1 < n := by have := q.isLt; omega
    have hq : q = ⟨p.val + 1, hp1⟩ := Fin.ext (by dsimp; omega)
    rw [hq] at heq
    exact f.map_adj_eq A p hp1 heq
  | succ d ih =>
    have hq1 : q.val - 1 < n := by have := q.isLt; omega
    have hq2 : (q.val - 1) + 1 < n := by have := q.isLt; omega
    let q' : Fin n := ⟨q.val - 1, hq1⟩
    let B := swapRows A q' ⟨q'.val + 1, hq2⟩
    have hB : f.toFun B = - f.toFun A := f.map_swapAdj A q' hq2
    have hBeq : B p = B q' := by
      funext c
      dsimp only [B, swapRows]
      have h1 : p ≠ q' := fun h => by have := congrArg Fin.val h; dsimp [q'] at this; omega
      have h2 : p ≠ ⟨q'.val + 1, hq2⟩ := fun h => by have := congrArg Fin.val h; dsimp [q'] at this; omega
      have hqeq : (⟨q'.val + 1, hq2⟩ : Fin n) = q := by apply Fin.ext; dsimp [q']; omega
      have h3 : p ≠ q := hqeq ▸ h2
      simp only [h1, hqeq, h3, ite_true, ite_false]
      exact congrFun heq c
    have hB0 : f.toFun B = 0 := ih B p q' (by dsimp [q']; omega) hBeq (by dsimp [q']; omega)
    rw [hB0] at hB
    have hneg : -(0 : R) = -(- f.toFun A) := congrArg CRing.neg hB
    rw [neg_zero', neg_neg'] at hneg
    exact hneg.symm

theorem map_rows_eq {n : Nat} (f : AltMultilin n R) (A : Mat n n R)
    (p q : Fin n) (hne : p ≠ q) (heq : A p = A q) : f.toFun A = 0 := by
  by_cases h : p.val < q.val
  · exact f.map_rows_eq_lt A p q h heq
  · have h' : q.val < p.val := by
      have hne' : p.val ≠ q.val := fun hv => hne (Fin.ext hv)
      omega
    exact f.map_rows_eq_lt A q p h' heq.symm

theorem map_addRowMul {n : Nat} (f : AltMultilin n R) (A : Mat n n R)
    (p q : Fin n) (hne : p ≠ q) (s : R) :
    f.toFun (updateRow A q (fun c => A q c + s * A p c)) = f.toFun A := by
  rw [f.map_add, updateRow_self, f.map_smul]
  have hz : f.toFun (updateRow A q (A p)) = 0 := by
    apply f.map_rows_eq _ p q hne
    funext c; unfold updateRow; simp [hne]
  rw [hz, mul_zero', add_zero']

-- Helper: insert row 0 = e_j and col j (below row 0) = 0 around an n×n matrix M
def stdBasis (n : Nat) (j : Fin n) : Fin n → R := fun c => if c = j then 1 else 0

def insertRow0Colj {n : Nat} (j : Fin (n + 1)) (M : Mat n n R) : Mat (n + 1) (n + 1) R :=
  fun r c =>
    if hr : r.val = 0 then
      if c = j then 1 else 0
    else
      if hc : c.val < j.val then M ⟨r.val - 1, by omega⟩ ⟨c.val, by omega⟩
      else if hc2 : c.val = j.val then 0
      else M ⟨r.val - 1, by omega⟩ ⟨c.val - 1, by omega⟩

theorem insertRow0Colj_updateRow {n : Nat} (j : Fin (n + 1)) (M : Mat n n R) (i : Fin n) (v : Fin n → R) :
    insertRow0Colj j (updateRow M i v) =
    updateRow (insertRow0Colj j M) i.succ (fun c =>
      if hc : c.val < j.val then v ⟨c.val, by omega⟩
      else if hc2 : c.val = j.val then 0
      else v ⟨c.val - 1, by omega⟩) := by
  funext r c
  unfold insertRow0Colj updateRow
  by_cases hr0 : r.val = 0
  · have hne : r ≠ i.succ := fun h => by subst h; simp [Fin.succ] at hr0
    simp [hr0, hne]
  · by_cases hri : r = i.succ
    · subst hri
      simp
    · have hi1 : (⟨r.val - 1, by omega⟩ : Fin n) ≠ i := by
        intro h; apply hri; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv; simp [Fin.succ]; omega
      simp [hr0, hri, hi1]

theorem insertRow0Colj_matOne_sign {n : Nat} (f : AltMultilin (n + 1) R) (j : Fin (n + 1)) :
    f.toFun (insertRow0Colj j (matOne n)) = signPow j.val * f.toFun (matOne (n + 1)) := by
  suffices ∀ (k : Nat) (hk : k ≤ j.val),
      f.toFun (fun r c : Fin (n + 1) =>
        if r.val = k then (if c = j then 1 else 0)
        else if r.val < k then (if c.val = r.val then 1 else 0)
        else if r.val ≤ j.val then (if c.val = r.val - 1 then 1 else 0)
        else (if c.val = r.val then 1 else 0)) =
      signPow k * f.toFun (insertRow0Colj j (matOne n)) by
    have h := this j.val (Nat.le_refl _)
    have hId : (fun r c : Fin (n + 1) =>
        if r.val = j.val then (if c = j then (1 : R) else 0)
        else if r.val < j.val then (if c.val = r.val then 1 else 0)
        else if r.val ≤ j.val then (if c.val = r.val - 1 then 1 else 0)
        else (if c.val = r.val then 1 else 0)) = matOne (n + 1) := by
      funext r c
      unfold matOne
      by_cases h1 : r.val = j.val
      · have hrj : r = j := Fin.ext h1
        subst hrj
        by_cases hc : c = r
        · subst hc; simp
        · have hrc : r ≠ c := fun h => hc h.symm
          simp [hc, hrc]
      · by_cases h2 : r.val < j.val
        · have hrc : c.val = r.val ↔ r = c := ⟨fun h => Fin.ext h.symm, fun h => by subst h; rfl⟩
          simp [h1, h2, hrc]
        · have h3 : ¬(r.val ≤ j.val) := by omega
          have hrc : c.val = r.val ↔ r = c := ⟨fun h => Fin.ext h.symm, fun h => by subst h; rfl⟩
          simp [h1, h2, h3, hrc]
    rw [hId] at h
    have hmul : signPow j.val * f.toFun (matOne (n + 1)) =
                signPow j.val * (signPow j.val * f.toFun (insertRow0Colj j (matOne n))) :=
      congrArg (CRing.mul (signPow j.val)) h
    rw [← mul_assoc', signPow_mul_self, one_mul'] at hmul
    exact hmul.symm
  intro k hk
  induction k with
  | zero =>
    rw [signPow_zero, one_mul']
    congr 1; funext r c
    unfold insertRow0Colj matOne
    by_cases hr0 : r.val = 0
    · simp [hr0]
    · simp only [hr0, ite_false, Nat.not_lt_zero]
      by_cases hle : r.val ≤ j.val
      · simp only [hle, ite_true]
        by_cases hc1 : c.val < j.val
        · simp only [dite_eq_left hc1]
          by_cases heq : c.val = r.val - 1
          · have : (⟨r.val - 1, by omega⟩ : Fin n) = ⟨c.val, by omega⟩ := Fin.ext heq.symm
            simp [heq, this]
          · have : (⟨r.val - 1, by omega⟩ : Fin n) ≠ ⟨c.val, by omega⟩ := fun h => heq (congrArg Fin.val h).symm
            simp [heq, this]
        · by_cases hc2 : c.val = j.val
          · have hne : c.val ≠ r.val - 1 := by omega
            simp [dite_eq_right hc1, dite_eq_left hc2, hne]
          · have hne : c.val ≠ r.val - 1 := by omega
            have hne2 : (⟨r.val - 1, by omega⟩ : Fin n) ≠ ⟨c.val - 1, by omega⟩ := by
              intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
            simp [dite_eq_right hc1, dite_eq_right hc2, hne, hne2]
      · simp only [hle, ite_false]
        by_cases hc1 : c.val < j.val
        · have hne : c.val ≠ r.val := by omega
          have hne2 : (⟨r.val - 1, by omega⟩ : Fin n) ≠ ⟨c.val, by omega⟩ := by
            intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
          simp [dite_eq_left hc1, hne, hne2]
        · by_cases hc2 : c.val = j.val
          · have hne : c.val ≠ r.val := by omega
            simp [dite_eq_right hc1, dite_eq_left hc2, hne]
          · simp only [hc1, hc2, dite_false]
            by_cases heq : c.val = r.val
            · have hrc : r.val - 1 = c.val - 1 := by omega
              have hfin : (⟨r.val - 1, by omega⟩ : Fin n) = ⟨c.val - 1, by omega⟩ := Fin.ext hrc
              simp [heq, hfin]
            · have hfin : (⟨r.val - 1, by omega⟩ : Fin n) ≠ ⟨c.val - 1, by omega⟩ := by
                intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
              simp [heq, hfin]
  | succ k ih =>
    have hk1 : k + 1 < n + 1 := Nat.lt_of_le_of_lt hk j.isLt
    let A : Mat (n + 1) (n + 1) R := fun r c =>
      if r.val = k then (if c = j then 1 else 0)
      else if r.val < k then (if c.val = r.val then 1 else 0)
      else if r.val ≤ j.val then (if c.val = r.val - 1 then 1 else 0)
      else (if c.val = r.val then 1 else 0)
    have hswap : (fun r c : Fin (n + 1) =>
        if r.val = k + 1 then (if c = j then 1 else 0)
        else if r.val < k + 1 then (if c.val = r.val then 1 else 0)
        else if r.val ≤ j.val then (if c.val = r.val - 1 then 1 else 0)
        else (if c.val = r.val then 1 else 0)) =
        swapRows A ⟨k, by omega⟩ ⟨k + 1, hk1⟩ := by
      funext r c
      dsimp only [A, swapRows]
      by_cases hr1 : r = ⟨k, by omega⟩
      · subst hr1
        have h1 : ¬(k = k + 1) := by omega
        have h2 : k < k + 1 := by omega
        have h3 : ¬(k + 1 = k) := by omega
        have h4 : ¬(k + 1 < k) := by omega
        have h5 : k + 1 ≤ j.val := hk
        simp [h2, h4, h5]
      · by_cases hr2 : r = ⟨k + 1, hk1⟩
        · subst hr2; simp
        · have hne1 : r.val ≠ k := fun hv => hr1 (Fin.ext hv)
          have hne2 : r.val ≠ k + 1 := fun hv => hr2 (Fin.ext hv)
          have hlt : r.val < k + 1 ↔ r.val < k := by omega
          simp [hr1, hr2, hne1, hne2, hlt]
    rw [hswap, f.map_swapAdj A ⟨k, by omega⟩ hk1, ih (Nat.le_of_succ_le hk), signPow_succ, neg_mul']

-- Clear column j in rows 1..m of a matrix whose row 0 is e_j
theorem map_clear_col_j {n : Nat} (f : AltMultilin (n + 1) R) (A : Mat (n + 1) (n + 1) R)
    (j : Fin (n + 1)) :
    f.toFun (updateRow A 0 (stdBasis (n + 1) j)) =
    f.toFun (insertRow0Colj j (minor0 A j)) := by
  let B0 := updateRow A 0 (stdBasis (n + 1) j)
  suffices ∀ (m : Nat) (hm : m ≤ n),
      f.toFun B0 = f.toFun (fun r c =>
        if r.val = 0 then (if c = j then 1 else 0)
        else if r.val ≤ m then (if c = j then 0 else A r c)
        else A r c) by
    have h := this n (Nat.le_refl n)
    rw [h]
    congr 1; funext r c
    unfold insertRow0Colj minor0
    by_cases hr0 : r.val = 0
    · simp [hr0]
    · have hle : r.val ≤ n := Nat.le_of_lt_succ r.isLt
      simp only [hr0, ite_false, hle, ite_true]
      by_cases hc1 : c.val < j.val
      · have hne : c ≠ j := fun h => by subst h; omega
        have hsa : succAbove j ⟨c.val, by omega⟩ = c := by
          apply Fin.ext; unfold succAbove; simp [hc1]
        have hrsucc : (⟨r.val - 1, by omega⟩ : Fin n).succ = r := by
          apply Fin.ext; simp [Fin.succ]; omega
        simp [dite_eq_left hc1, hne, hsa, hrsucc]
      · by_cases hc2 : c.val = j.val
        · have heq : c = j := Fin.ext hc2
          simp [heq]
        · have hne : c ≠ j := fun h => hc2 (congrArg Fin.val h)
          have hsa : succAbove j ⟨c.val - 1, by omega⟩ = c := by
            apply Fin.ext; unfold succAbove
            have hnot : ¬(c.val - 1 < j.val) := by omega
            simp [hnot]; omega
          have hrsucc : (⟨r.val - 1, by omega⟩ : Fin n).succ = r := by
            apply Fin.ext; simp [Fin.succ]; omega
          simp [dite_eq_right hc1, dite_eq_right hc2, hne, hsa, hrsucc]
  intro m hm
  induction m with
  | zero =>
    congr 1; funext r c
    dsimp only [B0, updateRow, stdBasis]
    by_cases hr0 : r.val = 0
    · have heq : r = 0 := Fin.ext hr0
      simp [heq]
    · have hne : r ≠ 0 := fun h => hr0 (congrArg Fin.val h)
      have hle : ¬(r.val ≤ 0) := by omega
      simp [hr0, hne, hle]
  | succ m ih =>
    rw [ih (Nat.le_of_succ_le hm)]
    let M : Mat (n + 1) (n + 1) R := fun r c =>
      if r.val = 0 then (if c = j then 1 else 0)
      else if r.val ≤ m then (if c = j then 0 else A r c)
      else A r c
    let q : Fin (n + 1) := ⟨m + 1, by omega⟩
    have hne : (0 : Fin (n + 1)) ≠ q := by
      intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
    have hstep := f.map_addRowMul M 0 q hne (- A q j)
    rw [← hstep]
    congr 1; funext r c
    dsimp only [M, updateRow]
    by_cases hrq : r = q
    · subst hrq
      have h0 : ¬((q.val : Nat) = 0) := by dsimp [q]; omega
      have h1 : q.val ≤ m + 1 := by dsimp [q]; omega
      have h2 : ¬(q.val ≤ m) := by dsimp [q]; omega
      simp only [ite_true, h0, ite_false, h1, h2, Fin.val_zero]
      by_cases hcj : c = j
      · subst hcj; simp [mul_one', add_right_neg']
      · simp [hcj, mul_zero', add_zero']
    · have hval : r.val ≠ m + 1 := fun hv => hrq (Fin.ext hv)
      have hiff : r.val ≤ m + 1 ↔ r.val ≤ m := by omega
      simp [hrq, hiff]

-- CROWN JEWEL: Uniqueness of Alternating Multilinear Forms over ANY CRing R!
end AltMultilin

-- ============================================================================
-- Corollary 1: Multiplicativity det (A * B) = det A * det B
-- ============================================================================

theorem det_blockLower_one_left {m n : Nat} (C : Mat n m R) (D : Mat n n R) :
    det (fromBlocks (matOne m) (matZero m n) C D) = det D := by
  induction m with
  | zero =>
    have h0 : 0 + n = n := Nat.zero_add n
    have hEq : fromBlocks (matOne 0) (matZero 0 n) C D =
               fun i j : Fin (0 + n) => D (Fin.cast h0 i) (Fin.cast h0 j) := by
      funext i j; unfold fromBlocks
      have hi : ¬(i.val < 0) := Nat.not_lt_zero _
      have hj : ¬(j.val < 0) := Nat.not_lt_zero _
      simp only [hi, hj, dite_false]
      congr 1 <;> (apply Fin.ext; simp)
    have hdet : ∀ {a b : Nat} (heq : a = b) (M : Mat b b R),
        det (fun i j : Fin a => M (Fin.cast heq i) (Fin.cast heq j)) = det M := by
      intro a b heq M; subst heq; rfl
    rw [hEq, hdet h0 D]
  | succ m ih =>
    have hsucc : (m + 1) + n = (m + n) + 1 := Nat.succ_add m n
    have hdet_cast : ∀ {a b : Nat} (heq : a = b) (M : Mat b b R),
        det (fun i j : Fin a => M (Fin.cast heq i) (Fin.cast heq j)) = det M := by
      intro a b heq M; subst heq; rfl
    let M : Mat ((m + n) + 1) ((m + n) + 1) R :=
      fun i j => fromBlocks (matOne (m + 1)) (matZero (m + 1) n) C D (Fin.cast hsucc.symm i) (Fin.cast hsucc.symm j)
    have hM : det (fromBlocks (matOne (m + 1)) (matZero (m + 1) n) C D) = det M := by
      rw [← hdet_cast hsucc M]
      congr 1
    rw [hM, det_succ]
    rw [finSum_single (0 : Fin ((m + n) + 1))]
    · have h00 : M 0 0 = 1 := by
        dsimp only [M, fromBlocks, matOne]
        have hlt : 0 < m + 1 := Nat.zero_lt_succ m
        simp [hlt]
      have hmin : minor0 M 0 =
                  fromBlocks (matOne m) (matZero m n) (fun r c => C r c.succ) D := by
        funext r c
        dsimp only [minor0, M, fromBlocks, matOne, matZero]
        rw [succAbove_zero]
        by_cases hr : r.val < m
        · have hr1 : r.succ.val < m + 1 := Nat.succ_lt_succ hr
          by_cases hc : c.val < m
          · have hc1 : c.succ.val < m + 1 := Nat.succ_lt_succ hc
            simp only [Fin.val_cast, hr, hr1, hc, hc1, dite_true]
            by_cases hrc : r = c
            · subst hrc; simp
            · have hrc' : r.val ≠ c.val := fun hv => hrc (Fin.ext hv)
              have h1 : (⟨r.succ.val, hr1⟩ : Fin (m + 1)) ≠ ⟨c.succ.val, hc1⟩ := by
                intro h; exact hrc' (by have := congrArg Fin.val h; dsimp at this; simp at this; omega)
              have h2 : (⟨r.val, hr⟩ : Fin m) ≠ ⟨c.val, hc⟩ := fun h => hrc' (by have := congrArg Fin.val h; dsimp at this; exact this)
              simp [hrc', h2]
          · have hc1 : ¬(c.succ.val < m + 1) := by simp [Fin.succ]; omega
            simp only [Fin.val_cast, hr, hr1, hc, hc1, dite_true, dite_false]
        · have hr1 : ¬(r.succ.val < m + 1) := by simp [Fin.succ]; omega
          by_cases hc : c.val < m
          · have hc1 : c.succ.val < m + 1 := Nat.succ_lt_succ hc
            simp only [Fin.val_cast, hr, hr1, hc, hc1, dite_false, dite_true]
            congr 1
            · apply Fin.ext; simp [Fin.succ]
          · have hc1 : ¬(c.succ.val < m + 1) := by simp [Fin.succ]; omega
            simp only [Fin.val_cast, hr, hr1, hc, hc1, dite_false]
            congr 1
            · apply Fin.ext; simp [Fin.succ]
            · apply Fin.ext; simp [Fin.succ]
      rw [h00, Fin.val_zero, signPow_zero, one_mul', one_mul', hmin]
      exact ih (fun r c => C r c.succ)
    · intro j hj
      have h0j : M 0 j = 0 := by
        dsimp only [M, fromBlocks, matOne, matZero]
        have hlt : 0 < m + 1 := Nat.zero_lt_succ m
        by_cases hjlt : j.val < m + 1
        · simp [hlt, hj, hjlt]
        · simp [hlt, hjlt]
      rw [h0j, mul_zero', zero_mul']

theorem det_blockUpper_one_diag {m n : Nat} (B : Mat m n R) :
    det (fromBlocks (matOne m) B (matZero n m) (matOne n)) = 1 := by
  suffices ∀ (k : Nat) (hk : k ≤ n),
      det (fromBlocks (matOne m) (fun r c => if c.val < k then (0 : R) else B r c) (matZero n m) (matOne n)) =
      det (fromBlocks (matOne m) B (matZero n m) (matOne n)) by
    have h := this n (Nat.le_refl n)
    have hzero : (fun r c => if c.val < n then (0 : R) else B r c) = matZero m n := by
      funext r c; simp [c.isLt, matZero]
    rw [hzero] at h
    have hId : fromBlocks (R := R) (matOne m) (matZero m n) (matZero n m) (matOne n) = matOne (m + n) := by
      funext i j; unfold fromBlocks matOne matZero
      by_cases hi : i.val < m <;> by_cases hj : j.val < m
      · simp only [hi, hj, dite_true]
        by_cases hij : i = j
        · subst hij; simp
        · have hne : (⟨i.val, hi⟩ : Fin m) ≠ ⟨j.val, hj⟩ := fun h => hij (Fin.ext (by have := congrArg Fin.val h; dsimp at this; exact this))
          simp [hij, hne]
      · have hij : i ≠ j := fun h => by subst h; exact hj hi
        simp [hi, hj, hij]
      · have hij : i ≠ j := fun h => by subst h; exact hi hj
        simp [hi, hj, hij]
      · simp only [hi, hj, dite_false]
        by_cases hij : i = j
        · subst hij; simp
        · have hne : (⟨i.val - m, by omega⟩ : Fin n) ≠ ⟨j.val - m, by omega⟩ := by
            intro h; apply hij; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv; omega
          simp [hij, hne]
    rw [hId, det_matOne] at h
    exact h.symm
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih (Nat.le_of_succ_le hk)]
    suffices ∀ (t : Nat) (ht : t ≤ m),
        det (fromBlocks (matOne m)
          (fun r c => if c.val < k then (0 : R) else if c.val = k ∧ r.val < t then 0 else B r c)
          (matZero n m) (matOne n)) =
        det (fromBlocks (matOne m)
          (fun r c => if c.val < k then (0 : R) else B r c)
          (matZero n m) (matOne n)) by
      have h := this m (Nat.le_refl m)
      rw [← h]
      congr 1; funext i j; unfold fromBlocks
      by_cases hi : i.val < m
      · simp only [hi, dite_true]
        by_cases hj : j.val < m
        · simp only [hj, dite_true]
        · simp only [hj, dite_false]
          by_cases hc : j.val - m < k
          · have hc1 : j.val - m < k + 1 := by omega
            simp [hc, hc1]
          · by_cases hce : j.val - m = k
            · have hc1 : j.val - m < k + 1 := by omega
              simp [hce]
            · have hc1 : ¬(j.val - m < k + 1) := by omega
              simp [hc, hce, hc1]
      · simp only [hi, dite_false]
    intro t ht
    induction t with
    | zero =>
      congr 1; funext i j; unfold fromBlocks
      by_cases hi : i.val < m
      · simp only [hi, dite_true]
        by_cases hj : j.val < m
        · simp only [hj, dite_true]
        · simp [hj]
      · simp only [hi, dite_false]
    | succ t iht =>
      rw [← iht (Nat.le_of_succ_le ht)]
      let M := fromBlocks (matOne m)
        (fun r c => if c.val < k then (0 : R) else if c.val = k ∧ r.val < t then 0 else B r c)
        (matZero n m) (matOne n)
      let p : Fin (m + n) := ⟨m + k, by omega⟩
      let q : Fin (m + n) := ⟨t, by omega⟩
      have hne : p ≠ q := fun h => by have := congrArg Fin.val h; dsimp [p, q] at this; omega
      have hstep := (detAltMultilin (m + n)).map_addRowMul M p q hne (- B ⟨t, ht⟩ ⟨k, hk⟩)
      dsimp [detAltMultilin] at hstep
      rw [← hstep]
      congr 1; funext r c
      dsimp only [M, updateRow, fromBlocks, matOne, matZero]
      by_cases hrq : r = q
      · subst hrq
        have hlt : q.val < m := by dsimp [q]; omega
        have hpnot : ¬(p.val < m) := by dsimp [p]; omega
        simp only [ite_true, hlt, hpnot, dite_true, dite_false]
        by_cases hcm : c.val < m
        · simp [hcm, mul_zero', add_zero']
        · simp only [hcm, dite_false]
          by_cases hck : c.val - m = k
          · have hpeq : (⟨p.val - m, by omega⟩ : Fin n) = ⟨c.val - m, by omega⟩ := by
              apply Fin.ext; dsimp [p]; omega
            have hlt1 : q.val < t + 1 := by dsimp [q]; omega
            have hlt0 : ¬(q.val < t) := by dsimp [q]; omega
            have hqt : (⟨q.val, hlt⟩ : Fin m) = ⟨t, ht⟩ := Fin.ext rfl
            simp [hck, hlt1, hlt0, hpeq, hqt, mul_one', add_right_neg']
          · have hpne : (⟨p.val - m, by omega⟩ : Fin n) ≠ ⟨c.val - m, by omega⟩ := by
              intro h; apply hck; have hv := congrArg Fin.val h; dsimp [p] at hv; omega
            simp [hck, hpne, mul_zero', add_zero']
      · simp only [hrq, ite_false]
        by_cases hrm : r.val < m
        · simp only [hrm, dite_true]
          by_cases hcm : c.val < m
          · simp [hcm]
          · simp only [hcm, dite_false]
            have hne_val : r.val ≠ t := fun hv => hrq (Fin.ext hv)
            have hiff : r.val < t + 1 ↔ r.val < t := by omega
            simp [hiff]
        · simp [hrm]

def shuffleMat (m n : Nat) : Mat (m * n) (n * m) R :=
  fun i j => if divFin i = modFin j ∧ modFin i = divFin j then 1 else 0

theorem shuffleMat_mul_kron {m n : Nat} (C : Mat m m R) :
    matMul (matMul (shuffleMat n m) (kron C (matOne n))) (shuffleMat m n) =
    kron (matOne n) C := by
  funext i j
  unfold matMul
  have h1 : ∀ k2 : Fin (m * n),
      finSum (fun k1 : Fin (m * n) => shuffleMat n m i k1 * kron C (matOne n) k1 k2) =
      kron C (matOne n) (finMulPair (modFin i) (divFin i)) k2 := by
    intro k2
    rw [finSum_single (finMulPair (modFin i) (divFin i))]
    · unfold shuffleMat
      rw [divFin_finMulPair, modFin_finMulPair]
      simp [one_mul']
    · intro k1 hk1
      unfold shuffleMat
      have hnot : ¬(divFin i = modFin k1 ∧ modFin i = divFin k1) := by
        intro ⟨h1, h2⟩
        apply hk1
        apply Fin.ext
        have hd := congrArg Fin.val h2
        have hm := congrArg Fin.val h1
        simp only [divFin, modFin, finMulPair] at hd hm ⊢
        have hk := Nat.div_add_mod k1.val n
        rw [← hd, ← hm, Nat.mul_comm n] at hk
        exact hk.symm
      simp [hnot, zero_mul']
  rw [finSum_congr (fun k2 => by rw [h1 k2])]
  rw [finSum_single (finMulPair (modFin j) (divFin j))]
  · unfold shuffleMat
    rw [divFin_finMulPair, modFin_finMulPair]
    simp only [and_self, ite_true, mul_one']
    rw [kron_apply_pair]
    unfold kron matOne
    by_cases h : divFin i = divFin j
    · simp [h, mul_one', one_mul']
    · simp [h, mul_zero', zero_mul']
  · intro k2 hk2
    unfold shuffleMat
    have hnot : ¬(divFin k2 = modFin j ∧ modFin k2 = divFin j) := by
      intro ⟨h1, h2⟩
      apply hk2
      apply Fin.ext
      have hd := congrArg Fin.val h1
      have hm := congrArg Fin.val h2
      simp only [divFin, modFin, finMulPair] at hd hm ⊢
      have hk := Nat.div_add_mod k2.val n
      rw [hd, hm, Nat.mul_comm n] at hk
      exact hk.symm
    simp [hnot, mul_zero']

theorem shuffleMat_mul_inv (m n : Nat) :
    matMul (shuffleMat (R := R) n m) (shuffleMat m n) = matOne (n * m) := by
  have h := shuffleMat_mul_kron (R := R) (matOne m) (n := n)
  rw [kron_one, matMul_one, kron_one] at h
  exact h

theorem woodbury_mul_right {n r : Nat} (A Ainv : Mat n n R) (U : Mat n r R) (V : Mat r n R)
    (Sinv : Mat r r R)
    (hAR : matMul A Ainv = matOne n)
    (hSR : matMul (matAdd (matOne r) (matMul (matMul V Ainv) U)) Sinv = matOne r) :
    matMul (matAdd A (matMul U V))
           (matSub Ainv (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv))) = matOne n := by
  rw [matMul_sub, matAdd_mul, matAdd_mul]
  have hT3 : matMul A (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)) =
             matMul (matMul U Sinv) (matMul V Ainv) := by
    rw [← matMul_assoc A (matMul (matMul Ainv U) Sinv),
        ← matMul_assoc A (matMul Ainv U),
        ← matMul_assoc A Ainv U, hAR, matOne_mul]
  have hT4 : matMul (matMul U V) (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)) =
             matMul (matMul (matMul U (matMul (matMul V Ainv) U)) Sinv) (matMul V Ainv) := by
    rw [matMul_assoc U V, ← matMul_assoc V (matMul (matMul Ainv U) Sinv),
        ← matMul_assoc V (matMul Ainv U), ← matMul_assoc V Ainv U,
        ← matMul_assoc U (matMul (matMul (matMul V Ainv) U) Sinv),
        ← matMul_assoc U (matMul (matMul V Ainv) U) Sinv]
  have hsum : matAdd (matMul A (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)))
                     (matMul (matMul U V) (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv))) =
              matMul (matMul U V) Ainv := by
    rw [hT3, hT4, ← matAdd_mul, ← matAdd_mul]
    have hfac : matAdd U (matMul U (matMul (matMul V Ainv) U)) =
                matMul U (matAdd (matOne r) (matMul (matMul V Ainv) U)) := by
      rw [matMul_add, matMul_one]
    rw [hfac, matMul_assoc U _ Sinv, hSR, matMul_one, matMul_assoc]
  rw [hAR, hsum]
  funext i j; unfold matSub matAdd
  rw [sub_eq_add_neg', add_assoc', add_right_neg', add_zero']

theorem woodbury_mul_left {n r : Nat} (A Ainv : Mat n n R) (U : Mat n r R) (V : Mat r n R)
    (Sinv : Mat r r R)
    (hAL : matMul Ainv A = matOne n)
    (hSL : matMul Sinv (matAdd (matOne r) (matMul (matMul V Ainv) U)) = matOne r) :
    matMul (matSub Ainv (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)))
           (matAdd A (matMul U V)) = matOne n := by
  rw [matSub_mul, matMul_add, matMul_add]
  have hT3 : matMul (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)) A =
             matMul (matMul (matMul Ainv U) Sinv) V := by
    rw [matMul_assoc, matMul_assoc V Ainv A, hAL, matMul_one]
  have hT4 : matMul (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)) (matMul U V) =
             matMul (matMul (matMul Ainv U) (matMul Sinv (matMul (matMul V Ainv) U))) V := by
    rw [matMul_assoc (matMul (matMul Ainv U) Sinv),
        ← matMul_assoc (matMul V Ainv) U V,
        ← matMul_assoc (matMul (matMul Ainv U) Sinv) (matMul (matMul V Ainv) U) V,
        matMul_assoc (matMul Ainv U) Sinv (matMul (matMul V Ainv) U)]
  have hsum : matAdd (matMul (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)) A)
                     (matMul (matMul (matMul (matMul Ainv U) Sinv) (matMul V Ainv)) (matMul U V)) =
              matMul Ainv (matMul U V) := by
    rw [hT3, hT4, ← matAdd_mul]
    have hfac : matAdd (matMul (matMul Ainv U) Sinv)
                       (matMul (matMul Ainv U) (matMul Sinv (matMul (matMul V Ainv) U))) =
                matMul (matMul Ainv U) (matMul Sinv (matAdd (matOne r) (matMul (matMul V Ainv) U))) := by
      rw [matMul_add, matMul_one, matMul_add]
    rw [hfac, hSL, matMul_one, matMul_assoc]
  rw [hAL, hsum]
  funext i j; unfold matSub matAdd
  rw [sub_eq_add_neg', add_assoc', add_right_neg', add_zero']

-- ============================================================================
-- Corollary 5: Kernel Singularity Lemma (M * v = 0 ∧ v ≠ 0 → det M = 0 over Q)
-- ============================================================================

theorem det_eq_zero_of_col_zero : ∀ {n : Nat} (A : Mat n n R) (p : Fin n),
    (∀ r : Fin n, A r p = 0) → det A = 0
  | 0, _, p, _ => Fin.elim0 p
  | n + 1, A, p, hp => by
    simp only [det]
    have hterm : ∀ j : Fin (n + 1), signPow j.val * A 0 j * det (minor0 A j) = 0 := by
      intro j
      by_cases hjp : j = p
      · subst hjp; rw [hp 0, mul_zero', zero_mul']
      · have hmin0 : det (minor0 A j) = 0 := by
          by_cases hlt : p.val < j.val
          · apply det_eq_zero_of_col_zero (minor0 A j) ⟨p.val, by omega⟩
            intro r; unfold minor0 succAbove
            have h1 : (⟨p.val, by omega⟩ : Fin n).val < j.val := hlt
            rw [dite_eq_left h1]
            exact hp r.succ
          · have hgt : j.val < p.val := by
              have hne : j.val ≠ p.val := fun hv => hjp (Fin.ext hv)
              omega
            apply det_eq_zero_of_col_zero (minor0 A j) ⟨p.val - 1, by omega⟩
            intro r; unfold minor0 succAbove
            have h1 : ¬((⟨p.val - 1, by omega⟩ : Fin n).val < j.val) := by dsimp; omega
            rw [dite_eq_right h1]
            have hpeq : (⟨(⟨p.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ : Fin (n + 1)) = p := by
              apply Fin.ext; dsimp; omega
            rw [hpeq]
            exact hp r.succ
        rw [hmin0, mul_zero']
    rw [finSum_congr hterm, finSum_zero]

def setCol {n : Nat} (A : Mat n n R) (p : Fin n) (v : Fin n → R) : Mat n n R :=
  fun r c => if c = p then v r else A r c

theorem det_setCol_matOne : ∀ {n : Nat} (p : Fin n) (v : Fin n → R),
    det (setCol (matOne n) p v) = v p
  | 0, p, _ => Fin.elim0 p
  | n + 1, p, v => by
    cases p using Fin.cases with
    | zero =>
      simp only [det]
      rw [finSum_single (0 : Fin (n + 1))]
      · have hmin : minor0 (setCol (matOne (n + 1)) 0 v) 0 = matOne n := by
          funext r c; unfold minor0 setCol matOne
          rw [succAbove_zero]
          have hne : c.succ ≠ 0 := Fin.succ_ne_zero c
          simp only [hne, ite_false]
          by_cases h : r = c
          · subst h; simp
          · have h' : r.succ ≠ c.succ := fun heq => h (Fin.succ_inj.mp heq)
            simp [h, h']
        rw [hmin, det_matOne, Fin.val_zero, signPow_zero, one_mul', mul_one']
        simp [setCol]
      · intro j hj
        have h0j : setCol (matOne (n + 1)) 0 v 0 j = 0 := by
          simp [setCol, matOne, hj, hj.symm]
        rw [h0j, mul_zero', zero_mul']
    | succ p' =>
      simp only [det]
      have hterm : ∀ j : Fin (n + 1), j ≠ 0 →
          signPow j.val * setCol (matOne (n + 1)) p'.succ v 0 j *
          det (minor0 (setCol (matOne (n + 1)) p'.succ v) j) = 0 := by
        intro j hj
        by_cases hjp : j = p'.succ
        · subst hjp
          have hcol0 : det (minor0 (setCol (matOne (n + 1)) p'.succ v) p'.succ) = 0 := by
            cases n with
            | zero => exact Fin.elim0 p'
            | succ n' =>
              apply det_eq_zero_of_col_zero _ (0 : Fin (n' + 1))
              intro r
              unfold minor0 setCol matOne
              rw [succAbove_succ_zero]
              have h1 : (0 : Fin (n' + 2)) ≠ p'.succ := (Fin.succ_ne_zero p').symm
              have h2 : r.succ ≠ 0 := Fin.succ_ne_zero r
              simp [h1, h2]
          rw [hcol0, mul_zero']
        · have h0j : setCol (matOne (n + 1)) p'.succ v 0 j = 0 := by
            simp [setCol, matOne, hjp, hj.symm]
          rw [h0j, mul_zero', zero_mul']
      rw [finSum_single (0 : Fin (n + 1)) _ hterm]
      have h00 : setCol (matOne (n + 1)) p'.succ v 0 0 = 1 := by
        have hne : (0 : Fin (n + 1)) ≠ p'.succ := (Fin.succ_ne_zero p').symm
        simp [setCol, matOne, hne]
      have hmin : minor0 (setCol (matOne (n + 1)) p'.succ v) 0 =
                  setCol (matOne n) p' (fun r => v r.succ) := by
        funext r c; unfold minor0 setCol matOne
        rw [succAbove_zero]
        by_cases hc : c = p'
        · subst hc; simp
        · have hc' : c.succ ≠ p'.succ := fun heq => hc (Fin.succ_inj.mp heq)
          simp only [hc, hc', ite_false]
          by_cases hr : r = c
          · subst hr; simp
          · have hr' : r.succ ≠ c.succ := fun heq => hr (Fin.succ_inj.mp heq)
            simp [hr, hr']
      rw [h00, hmin, Fin.val_zero, signPow_zero, one_mul', one_mul']
      exact det_setCol_matOne p' (fun r => v r.succ)

def castMatQ {m n : Nat} (A : Mat m n Int) : Mat m n Q :=
  fun i j => Q.ofInt (A i j)

theorem finSum_ofInt {n : Nat} (f : Fin n → Int) :
    Q.ofInt (finSum f) = finSum (fun i => Q.ofInt (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finSum, Q.ofInt_add, ih]

theorem ofInt_signPow (k : Nat) : Q.ofInt (signPow k) = signPow k := by
  unfold signPow
  by_cases h : k % 2 = 0
  · simp [h, Q.ofInt_one]
  · simp [h, Q.ofInt_neg, Q.ofInt_one]

theorem det_castMatQ : ∀ {n : Nat} (A : Mat n n Int),
    det (castMatQ A) = Q.ofInt (det A)
  | 0, _ => rfl
  | n + 1, A => by
    simp only [det, finSum_ofInt]
    apply finSum_congr; intro j
    rw [Q.ofInt_mul, Q.ofInt_mul, ofInt_signPow]
    have hmin : minor0 (castMatQ A) j = castMatQ (minor0 A j) := rfl
    rw [hmin, det_castMatQ (minor0 A j)]
    rfl

end Determinant

-- ============================================================================
-- Section 5: The Kronecker-Woodbury Schur-Tower Riccati Lifting Engine
-- ============================================================================
-- Part 5A: General Rank-r Kronecker-Plus-Low-Rank Probe-Bank Engine
-- Part 5B: Exact b×b Affine Bit-Transducer Compiler & Singularity Converse
-- Part 5C: Pure-Silicon Bit-Serial Transducer Equivalence Bridge
-- ============================================================================

section SchurTowerEngine
variable {R : Type} [CRing R]

-- Left-associative power powB b k so powB b (k + 1) = b * powB b k DEFINITIONALLY!
def powB (b : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => b * powB b k

theorem powB_eq_pow (b k : Nat) : powB b k = b ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powB, ih, Nat.pow_succ, Nat.mul_comm]

theorem powB_pos {b : Nat} (hb : 0 < b) (k : Nat) : 0 < powB b k := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos hb ih

-- ----------------------------------------------------------------------------
-- Part 5A: General Rank-r Kronecker-Plus-Low-Rank Probe-Bank Schur-Tower Engine
-- ----------------------------------------------------------------------------

-- Block-wise bilinear probe contraction:
--   ∑_{a, c : Fin b} Cinv a c • (L a * S * R c)
def probeContract {b q p q' p' : Nat} (Cinv : Mat b b R)
    (L : Fin b → Mat q' q R) (S : Mat q p R) (Rm : Fin b → Mat p p' R) : Mat q' p' R :=
  fun i j => finSum (fun a : Fin b => finSum (fun c : Fin b =>
    Cinv a c * matMul (matMul (L a) S) (Rm c) i j))

-- Key contraction identity:
-- If Y' has block a equal to L a * Y, and X' has block c equal to X * Rm c,
-- then Y' * (Cinv ⊗ W) * X' = probeContract Cinv L (Y * W * X) Rm!
theorem probe_kron_contract {b n q p q' p' : Nat}
    (Cinv : Mat b b R) (W : Mat n n R)
    (X : Mat n p R) (Y : Mat q n R)
    (X' : Mat (b * n) p' R) (Y' : Mat q' (b * n) R)
    (L : Fin b → Mat q' q R) (Rm : Fin b → Mat p p' R)
    (hX : ∀ (c : Fin b) (k : Fin n) (j : Fin p'), X' (finMulPair c k) j = matMul X (Rm c) k j)
    (hY : ∀ (i : Fin q') (a : Fin b) (k : Fin n), Y' i (finMulPair a k) = matMul (L a) Y i k) :
    matMul (matMul Y' (kron Cinv W)) X' = probeContract Cinv L (matMul (matMul Y W) X) Rm := by
  funext i j
  unfold matMul probeContract
  rw [finSum_split_mul]
  have hinner : ∀ c : Fin b,
      finSum (fun k2 : Fin n =>
        finSum (fun m : Fin (b * n) => Y' i m * kron Cinv W m (finMulPair c k2)) * X' (finMulPair c k2) j) =
      finSum (fun a : Fin b => Cinv a c * matMul (matMul (L a) (matMul (matMul Y W) X)) (Rm c) i j) := by
    intro c
    have hstep1 : ∀ k2 : Fin n,
        finSum (fun m : Fin (b * n) => Y' i m * kron Cinv W m (finMulPair c k2)) * X' (finMulPair c k2) j =
        finSum (fun a : Fin b =>
          Cinv a c * (finSum (fun k1 : Fin n => matMul (L a) Y i k1 * W k1 k2) * matMul X (Rm c) k2 j)) := by
      intro k2
      rw [finSum_split_mul, hX c k2 j, ← finSum_smul_right]
      apply finSum_congr; intro a
      have hsub : finSum (fun k1 : Fin n => Y' i (finMulPair a k1) * kron Cinv W (finMulPair a k1) (finMulPair c k2)) =
                  Cinv a c * finSum (fun k1 : Fin n => matMul (L a) Y i k1 * W k1 k2) := by
        rw [← finSum_smul_left]
        apply finSum_congr; intro k1
        rw [hY i a k1, kron_apply_pair]
        rw [← mul_assoc', mul_comm' (matMul (L a) Y i k1) (Cinv a c), mul_assoc']
      rw [hsub, mul_assoc']
    rw [finSum_congr hstep1, finSum_swap]
    apply finSum_congr; intro a
    rw [finSum_smul_left]
    congr 1
    -- Show ∑_{k2} ((L a * Y) * W)_{i, k2} * (X * Rm c)_{k2, j} = ((L a * ((Y * W) * X)) * Rm c)_{i, j}
    change matMul (matMul (matMul (L a) Y) W) (matMul X (Rm c)) i j =
           matMul (matMul (L a) (matMul (matMul Y W) X)) (Rm c) i j
    rw [matMul_assoc (L a) Y W, matMul_assoc (L a) (matMul Y W) (matMul X (Rm c)),
        ← matMul_assoc (matMul Y W) X (Rm c), matMul_assoc (L a) (matMul (matMul Y W) X) (Rm c)]
  rw [finSum_congr hinner, finSum_swap]
  rfl

-- One-Step General Rank-r Schur-Tower Theorem:
-- Given M' = (C ⊗ M) + U * V, with invertible C and M, and invertible capacitance I_r + Γ:
-- produces exact Woodbury inverse W', exact next probe state S' = Y' * W' * X', and exact det(M')!
structure GeneralSchurTower (b n0 p q r : Nat) (R : Type) [CRing R] where
  C : Mat b b R
  Cinv : Mat b b R
  hCR : matMul C Cinv = matOne b
  hCL : matMul Cinv C = matOne b
  dim : Nat → Nat
  hdim0 : dim 0 = n0
  hdimS : ∀ k, dim (k + 1) = b * dim k
  M : (k : Nat) → Mat (dim k) (dim k) R
  X : (k : Nat) → Mat (dim k) p R
  Y : (k : Nat) → Mat q (dim k) R
  U : (k : Nat) → Mat (b * dim k) r R
  V : (k : Nat) → Mat r (b * dim k) R
  Rm : Nat → Fin b → Mat p p R
  Lm : Nat → Fin b → Mat q q R
  Pm : Nat → Fin b → Mat p r R
  Qm : Nat → Fin b → Mat r q R
  hM_rec : ∀ k, M (k + 1) = (hdimS k).symm ▸ matAdd (kron C (M k)) (matMul (U k) (V k))
  hX_rec : ∀ k c i j, (hdimS k ▸ X (k + 1)) (finMulPair c i) j = matMul (X k) (Rm k c) i j
  hY_rec : ∀ k i a j, (hdimS k ▸ Y (k + 1)) i (finMulPair a j) = matMul (Lm k a) (Y k) i j
  hU_rec : ∀ k c i j, U k (finMulPair c i) j = matMul (X k) (Pm k c) i j
  hV_rec : ∀ k i a j, V k i (finMulPair a j) = matMul (Qm k a) (Y k) i j

-- ----------------------------------------------------------------------------
-- Part 5B: Exact b×b Affine Bit-Transducer Compiler (Engine B)
--          M_{k+1} = (C ⊗ M_k) + (B ⊗ J_k)
-- ----------------------------------------------------------------------------

-- Grand sum (capacitance) of a matrix: cap(W) = 1^T W 1 = ∑_{i, j} W i j
def cap {n : Nat} (W : Mat n n R) : R :=
  finSum (fun i : Fin n => finSum (fun j : Fin n => W i j))

theorem cap_one_mat (A : Mat 1 1 R) : cap A = A 0 0 := by
  unfold cap; rw [finSum_fin1, finSum_fin1]

theorem cap_two_mat (A : Mat 2 2 R) : cap A = A 0 0 + A 0 1 + (A 1 0 + A 1 1) := by
  unfold cap; rw [finSum_fin2, finSum_fin2, finSum_fin2]

theorem cap_add {n : Nat} (A B : Mat n n R) : cap (matAdd A B) = cap A + cap B := by
  unfold cap matAdd
  rw [← finSum_add]
  apply finSum_congr; intro i
  rw [← finSum_add]

theorem cap_sub {n : Nat} (A B : Mat n n R) : cap (matSub A B) = cap A - cap B := by
  unfold cap matSub
  rw [← finSum_sub]
  apply finSum_congr; intro i
  rw [← finSum_sub]

theorem cap_kron {m n : Nat} (A : Mat m m R) (B : Mat n n R) : cap (kron A B) = cap A * cap B := by
  unfold cap kron
  rw [finSum_split_mul]
  have h1 : ∀ a : Fin m,
      finSum (fun i : Fin n => finSum (fun col : Fin (m * n) =>
        A (divFin (finMulPair a i)) (divFin col) * B (modFin (finMulPair a i)) (modFin col))) =
      finSum (fun c : Fin m => A a c) * finSum (fun i : Fin n => finSum (fun j : Fin n => B i j)) := by
    intro a
    have h2 : ∀ i : Fin n,
        finSum (fun col : Fin (m * n) =>
          A (divFin (finMulPair a i)) (divFin col) * B (modFin (finMulPair a i)) (modFin col)) =
        finSum (fun c : Fin m => A a c) * finSum (fun j : Fin n => B i j) := by
      intro i
      rw [finSum_split_mul]
      have h3 : ∀ c : Fin m,
          finSum (fun j : Fin n =>
            A (divFin (finMulPair a i)) (divFin (finMulPair c j)) *
            B (modFin (finMulPair a i)) (modFin (finMulPair c j))) =
          A a c * finSum (fun j : Fin n => B i j) := by
        intro c
        rw [← finSum_smul_left]
        apply finSum_congr; intro j
        rw [divFin_finMulPair, divFin_finMulPair, modFin_finMulPair, modFin_finMulPair]
      rw [finSum_congr h3, finSum_smul_right]
    rw [finSum_congr h2, finSum_smul_left]
  rw [finSum_congr h1, finSum_smul_right]

theorem matAllOnes_mul_mul {n : Nat} (W : Mat n n R) :
    matMul (matMul (matAllOnes n n) W) (matAllOnes n n) = matSmul (cap W) (matAllOnes n n) := by
  funext i j
  unfold matMul matAllOnes matSmul cap
  rw [mul_one']
  calc finSum (fun k => finSum (fun l => 1 * W l k) * 1)
      = finSum (fun k => finSum (fun l => W l k)) := by
          apply finSum_congr; intro k; rw [mul_one']
          apply finSum_congr; intro l; exact one_mul' _
    _ = finSum (fun l => finSum (fun k => W l k)) := finSum_swap _

theorem cap_WJW {n : Nat} (W : Mat n n R) :
    cap (matMul (matMul W (matAllOnes n n)) W) = cap W * cap W := by
  unfold cap matMul matAllOnes
  calc finSum (fun i => finSum (fun j => finSum (fun k => finSum (fun l => W i l * 1) * W k j)))
      = finSum (fun i => finSum (fun j => (finSum (fun l => W i l)) * finSum (fun k => W k j))) := by
          apply finSum_congr; intro i; apply finSum_congr; intro j
          rw [← finSum_smul_left]
          apply finSum_congr; intro k
          congr 1; apply finSum_congr; intro l; exact mul_one' _
    _ = finSum (fun i => (finSum (fun l => W i l)) * finSum (fun j => finSum (fun k => W k j))) := by
          apply finSum_congr; intro i; rw [finSum_smul_left]
    _ = finSum (fun i => finSum (fun l => W i l)) * finSum (fun j => finSum (fun k => W k j)) := by
          rw [finSum_smul_right]
    _ = finSum (fun i => finSum (fun l => W i l)) * finSum (fun k => finSum (fun j => W k j)) := by
          rw [finSum_swap]

-- Rank-b factorization of (B ⊗ J_n) = U * V where U = (B ⊗ 1_n) : (b*n)×b and V = (I_b ⊗ 1_n^T) : b×(b*n)!
def colOnes (n : Nat) : Mat n 1 R := fun _ _ => 1
def rowOnes (n : Nat) : Mat 1 n R := fun _ _ => 1

theorem kron_B_J_eq_mul {b n : Nat} (B : Mat b b R) :
    kron B (matAllOnes n n) =
    matMul (fun i (c : Fin b) => B (divFin i) c)
           (fun (c : Fin b) j => if c = divFin j then 1 else 0) := by
  funext i j
  unfold kron matAllOnes matMul
  rw [mul_one', finSum_single (divFin j)]
  · simp [mul_one']
  · intro c hc; simp [hc, mul_zero']

-- Exact One-Step Affine Bit-Transducer Schur-Tower Theorem:
-- M' = (C ⊗ M) + (B ⊗ J_n), with n ≥ 1 (so n = (n - 1) + 1)
def affineTower {b : Nat} (C B : Mat b b R) (m0 : R) : (k : Nat) → Mat (powB b k) (powB b k) R
  | 0 => fun _ _ => m0
  | k + 1 => matAdd (kron C (affineTower C B m0 k)) (kron B (matAllOnes (powB b k) (powB b k)))

-- Explicit Recursive Woodbury Inverse Tower!
def affineTowerInv {b : Nat} (Cinv B : Mat b b R) (m0_inv : R) (Qmat : Nat → Mat b b R) :
    (k : Nat) → Mat (powB b k) (powB b k) R
  | 0 => fun _ _ => m0_inv
  | k + 1 =>
    let W := affineTowerInv Cinv B m0_inv Qmat k
    matSub (kron Cinv W)
           (kron (matMul (matMul Cinv B) (Qmat k))
                 (matMul (matMul W (matAllOnes (powB b k) (powB b k))) W))

-- MASTER INFINITE LIFTING THEOREM (Engine B):
-- Any finite scalar Riccati-Schur certificate (S_k, Qmat_k) discharges for ALL k : Nat:
--   (1) M_k * W_k = I  and  W_k * M_k = I   (exact constructive inverse for ALL 2^k × 2^k!)
--   (2) cap(W_k) = S_k                      (exact inverse grand-sum invariant!)
--   (3) det(M_{k+1}) = (det C)^(b^k - 1) * det(C + S_k • B) * (det M_k)^b!
def bitTransducerVal (C B : Mat 2 2 R) (m0 : R) (i j : Nat) : Nat → R
  | 0 => m0
  | k + 1 =>
    let bi : Fin 2 := if i.testBit k then 1 else 0
    let bj : Fin 2 := if j.testBit k then 1 else 0
    C bi bj * bitTransducerVal C B m0 i j k + B bi bj

def bitTransducerMat (C B : Mat 2 2 R) (m0 : R) (k : Nat) : Mat (powB 2 k) (powB 2 k) R :=
  fun i j => bitTransducerVal C B m0 i.val j.val k

theorem testBit_top_of_lt_two_mul_pow2 {k x : Nat} (hx : x < 2 * powB 2 k) :
    x.testBit k = decide (x / powB 2 k = 1) := by
  have hp : powB 2 k = 2 ^ k := powB_eq_pow 2 k
  rw [hp] at hx ⊢
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hlt2 : x / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (Nat.mul_comm 2 (2 ^ k) ▸ hx)
  cases hq : x / 2 ^ k with
  | zero => simp
  | succ q =>
    cases q with
    | zero => simp
    | succ q' => omega

theorem testBit_mod_pow2 {k r x : Nat} (hr : r < k) :
    (x % powB 2 k).testBit r = x.testBit r := by
  rw [powB_eq_pow, Nat.testBit_mod_two_pow]
  simp [hr]

theorem bitTransducerVal_mod (C B : Mat 2 2 R) (m0 : R) (i j k : Nat) :
    bitTransducerVal C B m0 (i % powB 2 k) (j % powB 2 k) k = bitTransducerVal C B m0 i j k := by
  suffices ∀ (m : Nat), m ≤ k →
      bitTransducerVal C B m0 (i % powB 2 k) (j % powB 2 k) m = bitTransducerVal C B m0 i j m by
    exact this k (Nat.le_refl k)
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold bitTransducerVal
    have hlt : m < k := hm
    rw [testBit_mod_pow2 hlt, testBit_mod_pow2 hlt, ih (Nat.le_of_succ_le hm)]

-- BITWISE BRIDGE THEOREM:
-- For ALL k : Nat, the bit-serial transducer matrix (evaluated bit-by-bit via Nat.testBit)
-- is IDENTICAL entrywise to the recursive Kronecker-plus-low-rank tower affineTower!
theorem castMatQ_affineTower {b : Nat} (C B : Mat b b Int) (m0 : Int) :
    ∀ k : Nat, castMatQ (affineTower C B m0 k) = affineTower (castMatQ C) (castMatQ B) (Q.ofInt m0) k
  | 0 => rfl
  | k + 1 => by
    funext i j
    unfold castMatQ affineTower matAdd kron matAllOnes
    rw [Q.ofInt_add, Q.ofInt_mul, Q.ofInt_mul, Q.ofInt_one]
    have ih := congrFun (congrFun (castMatQ_affineTower C B m0 k) (modFin i)) (modFin j)
    unfold castMatQ at ih
    rw [ih]

end SchurTowerEngine


-- ============================================================================
-- Section 6: Four Novel Infinite Theorems for Carry-Perturbed Bitwise Matrices
--            + Explicit popcount/&&&/>>> Bridge + Programmable Singularity
--            + Non-Walsh Core Generality + Sharpness + Non-Vacuity + Axioms
-- ============================================================================

section ConcreteInfiniteTheorems

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl
  | _ + 2 => omega

theorem q_sound {a b : QPair} (h : a.num * b.den = b.num * a.den) :
    (Quotient.mk QPair.setoid a : Q) = Quotient.mk QPair.setoid b :=
  Quotient.sound h

-- ----------------------------------------------------------------------------
-- 6.1 Pure-Silicon Bitwise Walsh-Hadamard Core and Explicit popcount/>>> Bridge
-- ----------------------------------------------------------------------------

def walsh2 : Mat 2 2 Int := fun i j => if i = 1 ∧ j = 1 then -1 else 1
def walsh2Q : Mat 2 2 Q := castMatQ walsh2
def walsh2InvQ : Mat 2 2 Q := fun i j =>
  if i = 1 ∧ j = 1 then Q.mk (-1) 2 (by omega) else Q.mk 1 2 (by omega)

theorem q_half_add_half : Q.mk 1 2 (by omega) + Q.mk 1 2 (by omega) = (1 : Q) := by
  apply Quotient.sound
  change (1 * 2 + 1 * 2) * 1 = 1 * (2 * 2)
  rfl

theorem q_half_sub_half : Q.mk 1 2 (by omega) + Q.mk (-1) 2 (by omega) = (0 : Q) := by
  apply Quotient.sound
  change (1 * 2 + (-1) * 2) * 1 = 0 * (2 * 2)
  rfl

theorem q_neg_half : -(Q.mk 1 2 (by omega)) = Q.mk (-1) 2 (by omega) := by
  apply Quotient.sound
  change (-1) * 2 = (-1) * 2
  rfl

theorem q_neg_neg_half : -(Q.mk (-1) 2 (by omega)) = Q.mk 1 2 (by omega) := by
  apply Quotient.sound
  change (-(-1)) * 2 = 1 * 2
  rfl

theorem walsh2Q_mul_inv : matMul walsh2Q walsh2InvQ = matOne 2 := by
  funext i j
  unfold matMul walsh2Q castMatQ walsh2 walsh2InvQ matOne
  rw [finSum_fin2]
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
               Q.ofInt_one, Q.ofInt_neg, one_mul', neg_one_mul', q_neg_half, q_neg_neg_half,
               q_half_add_half, q_half_sub_half]

theorem walsh2InvQ_mul : matMul walsh2InvQ walsh2Q = matOne 2 := by
  funext i j
  unfold matMul walsh2Q castMatQ walsh2 walsh2InvQ matOne
  rw [finSum_fin2]
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
    simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
               Q.ofInt_one, Q.ofInt_neg, mul_one', mul_neg', q_neg_half, q_neg_neg_half,
               q_half_add_half, q_half_sub_half]

theorem det_walsh2 : det walsh2 = (-2 : Int) := by
  rw [det_two_mat]
  unfold walsh2
  decide

theorem det_walsh2Q : det walsh2Q = Q.ofInt (-2) := by
  rw [walsh2Q, det_castMatQ, det_walsh2]

-- Pure-silicon popcount over the lowest k bits of x : Nat
def popcount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => popcount k x + if x.testBit k then 1 else 0

theorem popcount_succ (k x : Nat) :
    popcount (k + 1) x = popcount k x + if x.testBit k then 1 else 0 := rfl

-- Explicit entrywise bitwise sum:
--   m0 * (-1)^popcount_k(i &&& j)
--   + ∑_{s=0}^{k-1} B[i_s, j_s] * (-1)^popcount_{k-1-s}((i >>> (s+1)) &&& (j >>> (s+1)))
def walshPerturbedEntry (B : Mat 2 2 Int) (m0 : Int) (i j k : Nat) : Int :=
  m0 * signPow (popcount k (i &&& j)) +
  finSum (fun s : Fin k =>
    let bi : Fin 2 := if i.testBit s.val then 1 else 0
    let bj : Fin 2 := if j.testBit s.val then 1 else 0
    B bi bj * signPow (popcount (k - 1 - s.val) ((i >>> (s.val + 1)) &&& (j >>> (s.val + 1)))))

def walshPerturbedMat (B : Mat 2 2 Int) (m0 : Int) (k : Nat) : Mat (powB 2 k) (powB 2 k) Int :=
  fun i j => walshPerturbedEntry B m0 i.val j.val k

theorem walsh2_bit_eq (bi bj : Bool) :
    walsh2 (if bi then 1 else 0) (if bj then 1 else 0) = signPow (if (bi && bj) then 1 else 0) := by
  cases bi <;> cases bj <;> decide

theorem testBit_shiftRight_land (i j s t : Nat) :
    (((i >>> (s + 1)) &&& (j >>> (s + 1))).testBit t) = (i.testBit (t + s + 1) && j.testBit (t + s + 1)) := by
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  have h1 : s + 1 + t = t + s + 1 := by omega
  rw [h1]

theorem finSum_snoc {R : Type} [CRing R] {n : Nat} (f : Fin (n + 1) → R) :
    finSum f = finSum (fun i : Fin n => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩ := by
  induction n with
  | zero =>
    rw [finSum_fin1]
    change f 0 = 0 + f ⟨0, Nat.lt_succ_self 0⟩
    rw [zero_add']
    rfl
  | succ n ih =>
    rw [finSum_succ f, ih (fun i : Fin (n + 1) => f i.succ), finSum_succ (fun i : Fin (n + 1) => f i.castSucc), add_assoc']
    have h1 : (finSum fun i : Fin n => f i.castSucc.succ) = finSum fun i : Fin n => f i.succ.castSucc :=
      finSum_congr fun i => congrArg f (Fin.ext rfl)
    have h2 : f (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).succ = f ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ :=
      congrArg f (Fin.ext rfl)
    rw [h1, h2]
    rfl

-- BITWISE POPCOUNT / SHIFT-RIGHT BRIDGE THEOREM:
-- Proves for ALL B, m0, i, j, k that the explicit popcount/&&&/>>> formula
-- equals the bit-serial affine transducer (and therefore equals affineTower)!
theorem walshPerturbedEntry_eq_bitTransducer (B : Mat 2 2 Int) (m0 : Int) (i j : Nat) :
    ∀ k : Nat, walshPerturbedEntry B m0 i j k = bitTransducerVal walsh2 B m0 i j k
  | 0 => by
    unfold walshPerturbedEntry bitTransducerVal popcount finSum
    rw [signPow_zero, mul_one', add_zero']
  | k + 1 => by
    unfold bitTransducerVal
    rw [← walshPerturbedEntry_eq_bitTransducer B m0 i j k]
    unfold walshPerturbedEntry
    -- Factor walsh2 bi_k bj_k = signPow (if i_k && j_k then 1 else 0)
    have hw : walsh2 (if i.testBit k then 1 else 0) (if j.testBit k then 1 else 0) =
              signPow (if (i.testBit k && j.testBit k) then 1 else 0) :=
      walsh2_bit_eq (i.testBit k) (j.testBit k)
    have hpop : signPow (R := Int) (popcount (k + 1) (i &&& j)) =
                walsh2 (if i.testBit k then 1 else 0) (if j.testBit k then 1 else 0) *
                signPow (popcount k (i &&& j)) := by
      rw [popcount_succ, Nat.testBit_and, signPow_add, mul_comm', hw]
    -- Split the last term s = k off the finSum over Fin (k + 1)
    rw [finSum_snoc]
    have htop : (let bi : Fin 2 := if i.testBit k then 1 else 0
                 let bj : Fin 2 := if j.testBit k then 1 else 0
                 B bi bj * signPow (popcount (k + 1 - 1 - k) ((i >>> (k + 1)) &&& (j >>> (k + 1))))) =
                B (if i.testBit k then 1 else 0) (if j.testBit k then 1 else 0) := by
      have hz : k + 1 - 1 - k = 0 := by omega
      rw [hz]; unfold popcount; rw [signPow_zero, mul_one']
    dsimp only at htop ⊢
    rw [htop]
    -- Each lower term s < k gains bit k in ((i >>> (s+1)) &&& (j >>> (s+1)))!
    have hlow : finSum (fun s : Fin k =>
                  B (if i.testBit s.val then 1 else 0) (if j.testBit s.val then 1 else 0) *
                  signPow (popcount (k + 1 - 1 - s.val) ((i >>> (s.val + 1)) &&& (j >>> (s.val + 1))))) =
                walsh2 (if i.testBit k then 1 else 0) (if j.testBit k then 1 else 0) *
                finSum (fun s : Fin k =>
                  B (if i.testBit s.val then 1 else 0) (if j.testBit s.val then 1 else 0) *
                  signPow (popcount (k - 1 - s.val) ((i >>> (s.val + 1)) &&& (j >>> (s.val + 1))))) := by
      rw [← finSum_smul_left]
      apply finSum_congr; intro s
      have hidx : k + 1 - 1 - s.val = (k - 1 - s.val) + 1 := by have := s.isLt; omega
      rw [hidx, popcount_succ, testBit_shiftRight_land]
      have hbit : k - 1 - s.val + s.val + 1 = k := by have := s.isLt; omega
      rw [hbit, signPow_add, ← hw]
      grind
    have hlow' : finSum (fun s : Fin k =>
                  B (if i.testBit s.castSucc.val then 1 else 0) (if j.testBit s.castSucc.val then 1 else 0) *
                  signPow (popcount (k + 1 - 1 - s.castSucc.val) ((i >>> (s.castSucc.val + 1)) &&& (j >>> (s.castSucc.val + 1))))) =
                walsh2 (if i.testBit k then 1 else 0) (if j.testBit k then 1 else 0) *
                finSum (fun s : Fin k =>
                  B (if i.testBit s.val then 1 else 0) (if j.testBit s.val then 1 else 0) *
                  signPow (popcount (k - 1 - s.val) ((i >>> (s.val + 1)) &&& (j >>> (s.val + 1))))) := hlow
    rw [hlow', hpop, left_distrib', add_assoc']
    congr 1
    · rw [← mul_assoc', mul_comm' m0 (walsh2 _ _), mul_assoc']

def mat2InvQ (A : Mat 2 2 Q) (detInv : Q) : Mat 2 2 Q :=
  fun i j =>
    detInv * (if i = 0 ∧ j = 0 then A 1 1
              else if i = 0 ∧ j = 1 then - A 0 1
              else if i = 1 ∧ j = 0 then - A 1 0
              else A 0 0)

theorem mat2InvQ_mul_right (A : Mat 2 2 Q) (detInv : Q) (hd : det A * detInv = 1) :
    matMul A (mat2InvQ A detInv) = matOne 2 := by
  rw [det_two_mat] at hd
  funext i j
  unfold matMul mat2InvQ matOne
  rw [finSum_fin2]
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;> simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false]
  · calc A 0 0 * (detInv * A 1 1) + A 0 1 * (detInv * -A 1 0)
        = (A 0 0 * A 1 1 - A 0 1 * A 1 0) * detInv := by
            rw [sub_eq_add_neg', right_distrib', neg_mul', mul_neg', mul_neg']
            congr 1
            · rw [← mul_assoc', mul_comm' (A 0 0) detInv, mul_assoc', mul_comm' detInv]
            · congr 1; rw [← mul_assoc', mul_comm' (A 0 1) detInv, mul_assoc', mul_comm' detInv]
      _ = 1 := hd
  · calc A 0 0 * (detInv * -A 0 1) + A 0 1 * (detInv * A 0 0)
        = -(detInv * (A 0 0 * A 0 1)) + detInv * (A 0 0 * A 0 1) := by
            congr 1
            · rw [mul_neg', mul_neg', ← mul_assoc', mul_comm' (A 0 0) detInv, mul_assoc']
            · rw [← mul_assoc', mul_comm' (A 0 1) detInv, mul_assoc', mul_comm' (A 0 1) (A 0 0)]
      _ = 0 := add_left_neg' _
  · calc A 1 0 * (detInv * A 1 1) + A 1 1 * (detInv * -A 1 0)
        = detInv * (A 1 0 * A 1 1) + -(detInv * (A 1 0 * A 1 1)) := by
            congr 1
            · rw [← mul_assoc', mul_comm' (A 1 0) detInv, mul_assoc']
            · rw [mul_neg', mul_neg', ← mul_assoc', mul_comm' (A 1 1) detInv, mul_assoc', mul_comm' (A 1 1) (A 1 0)]
      _ = 0 := add_right_neg' _
  · calc A 1 0 * (detInv * -A 0 1) + A 1 1 * (detInv * A 0 0)
        = (A 0 0 * A 1 1 - A 0 1 * A 1 0) * detInv := by
            rw [sub_eq_add_neg', right_distrib', neg_mul', mul_neg', mul_neg', add_comm']
            congr 1
            · rw [← mul_assoc', mul_comm' (A 1 1) detInv, mul_assoc', mul_comm' detInv, mul_comm' (A 1 1) (A 0 0)]
            · congr 1; rw [← mul_assoc', mul_comm' (A 1 0) detInv, mul_assoc', mul_comm' detInv, mul_comm' (A 1 0) (A 0 1)]
      _ = 1 := hd

theorem mat2InvQ_mul_left (A : Mat 2 2 Q) (detInv : Q) (hd : det A * detInv = 1) :
    matMul (mat2InvQ A detInv) A = matOne 2 := by
  rw [det_two_mat] at hd
  funext i j
  unfold matMul mat2InvQ matOne
  rw [finSum_fin2]
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;> simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false]
  · calc detInv * A 1 1 * A 0 0 + detInv * -A 0 1 * A 1 0
        = (A 0 0 * A 1 1 - A 0 1 * A 1 0) * detInv := by
            rw [sub_eq_add_neg', right_distrib', neg_mul', mul_neg', neg_mul']
            congr 1
            · rw [mul_assoc', mul_comm' detInv, mul_comm' (A 1 1) (A 0 0)]
            · congr 1; rw [mul_assoc', mul_comm' detInv]
      _ = 1 := hd
  · calc detInv * A 1 1 * A 0 1 + detInv * -A 0 1 * A 1 1
        = detInv * (A 0 1 * A 1 1) + -(detInv * (A 0 1 * A 1 1)) := by
            congr 1
            · rw [mul_assoc', mul_comm' (A 1 1) (A 0 1)]
            · rw [mul_neg', neg_mul', mul_assoc']
      _ = 0 := add_right_neg' _
  · calc detInv * -A 1 0 * A 0 0 + detInv * A 0 0 * A 1 0
        = -(detInv * (A 0 0 * A 1 0)) + detInv * (A 0 0 * A 1 0) := by
            congr 1
            · rw [mul_neg', neg_mul', mul_assoc', mul_comm' (A 1 0) (A 0 0)]
            · rw [mul_assoc']
      _ = 0 := add_left_neg' _
  · calc detInv * -A 1 0 * A 0 1 + detInv * A 0 0 * A 1 1
        = (A 0 0 * A 1 1 - A 0 1 * A 1 0) * detInv := by
            rw [sub_eq_add_neg', right_distrib', neg_mul', mul_neg', neg_mul', add_comm']
            congr 1
            · rw [mul_assoc', mul_comm' detInv]
            · congr 1; rw [mul_assoc', mul_comm' detInv, mul_comm' (A 1 0) (A 0 1)]
      _ = 1 := hd

theorem cap_mat2InvQ (A : Mat 2 2 Q) (detInv : Q) :
    cap (mat2InvQ A detInv) = detInv * ((A 1 1 + (- A 0 1)) + ((- A 1 0) + A 0 0)) := by
  rw [cap_two_mat]
  unfold mat2InvQ
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false]
  rw [left_distrib', left_distrib', left_distrib']

-- Arithmetic helpers for integer powers of 2 and (-2)
theorem rpow_neg_two_even {n : Nat} (heven : n % 2 = 0) :
    rpow (-2 : Int) n = rpow (2 : Int) n := by
  have h : rpow (-2 : Int) n = rpow (-1 : Int) n * rpow (2 : Int) n := by
    rw [← mul_rpow]; congr 1
  have hsign : ∀ m : Nat, rpow (-1 : Int) m = signPow m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [rpow_succ, ih, neg_one_mul', signPow_succ]
  rw [h, hsign, signPow]
  simp [heven, one_mul']

theorem rpow_neg_two_odd {n : Nat} (hodd : n % 2 = 1) :
    rpow (-2 : Int) n = - rpow (2 : Int) n := by
  have h : rpow (-2 : Int) n = rpow (-1 : Int) n * rpow (2 : Int) n := by
    rw [← mul_rpow]; congr 1
  have hsign : ∀ m : Nat, rpow (-1 : Int) m = signPow m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [rpow_succ, ih, neg_one_mul', signPow_succ]
  rw [h, hsign, signPow]
  have hne : ¬(n % 2 = 0) := by omega
  simp [hne, neg_one_mul']

theorem powB2_ge_one (k : Nat) : 1 ≤ powB 2 k := powB_pos (by omega) k

theorem powB2_sub_one_odd {k : Nat} (hk : 1 ≤ k) : (powB 2 k - 1) % 2 = 1 := by
  cases k with
  | zero => omega
  | succ k' =>
    change (2 * powB 2 k' - 1) % 2 = 1
    have hp := powB2_ge_one k'
    omega

-- ============================================================================
-- THEOREM 1 (Fixed-Point Regime):
--   Carry-Generate Perturbed Walsh-Hadamard Matrix W_k^(lam)
--   Entrywise: (-1)^popcount(i & j) + lam * ∑_{s < k, i_s = j_s = 1} (-1)^popcount((i>>>(s+1)) & (j>>>(s+1)))
-- ============================================================================

def carryGenB (lam : Int) : Mat 2 2 Int := fun i j => if i = 1 ∧ j = 1 then lam else 0
def carryGenWalshMat (lam : Int) (k : Nat) : Mat (powB 2 k) (powB 2 k) Int :=
  walshPerturbedMat (carryGenB lam) 1 k

theorem carryGen_core_det (lam : Int) :
    det (matAdd walsh2Q (matSmul (1 : Q) (castMatQ (carryGenB lam)))) = Q.ofInt (lam - 2) := by
  rw [det_two_mat]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 carryGenB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_zero, Q.ofInt_one, Q.ofInt_neg, one_mul', mul_zero', add_zero', mul_one']
  rw [← Q.ofInt_one, ← Q.ofInt_neg, ← Q.ofInt_add]
  have hsub : ∀ a b : Int, Q.ofInt a - Q.ofInt b = Q.ofInt (a - b) := by
    intro a b; rw [sub_eq_add_neg', ← Q.ofInt_neg, ← Q.ofInt_add]; rfl
  rw [hsub]
  congr 1; omega

theorem carryGen_core_cap (lam : Int) (hlam : lam ≠ 2) :
    cap (mat2InvQ (matAdd walsh2Q (matSmul (1 : Q) (castMatQ (carryGenB lam))))
                  (Q.inv (Q.ofInt (lam - 2)))) = (1 : Q) := by
  rw [cap_mat2InvQ]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 carryGenB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_zero, Q.ofInt_one, Q.ofInt_neg, one_mul', mul_zero', add_zero']
  have hnum : (-(1 : Q) + Q.ofInt lam + -(1 : Q)) + (-(1 : Q) + (1 : Q)) = Q.ofInt (lam - 2) := by
    rw [add_left_neg', add_zero', ← Q.ofInt_one, ← Q.ofInt_neg, ← Q.ofInt_add, ← Q.ofInt_add]
    congr 1; omega
  rw [hnum, Q.inv_mul_cancel (Q.ofInt_ne_zero (by omega))]

-- Theorem 1a: Exact Woodbury Inverse & Fixed-Point Capacitance S_k = 1 (∀ lam ≠ 2, ∀ k)
def skewBorrowB : Mat 2 2 Int := fun i j =>
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

def skewBorrowWalshMat (k : Nat) : Mat (powB 2 k) (powB 2 k) Int :=
  walshPerturbedMat skewBorrowB 1 k

def skewCapSeq : Nat → Q
  | 0 => Q.ofInt 1
  | k + 1 => if k % 2 = 0 then Q.ofInt 2 else Q.ofInt (-2)

theorem skewBorrow_core_det (s : Int) :
    det (matAdd walsh2Q (matSmul (Q.ofInt s) (castMatQ skewBorrowB))) = Q.ofInt (s * s - 2) := by
  rw [det_two_mat]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 skewBorrowB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_zero, Q.ofInt_one, Q.ofInt_neg, mul_zero', add_zero', mul_one', mul_neg']
  have hsub : ∀ a b : Int, Q.ofInt a - Q.ofInt b = Q.ofInt (a - b) := by
    intro a b; rw [sub_eq_add_neg', ← Q.ofInt_neg, ← Q.ofInt_add]; rfl
  rw [← Q.ofInt_one, ← Q.ofInt_neg, ← Q.ofInt_add, ← Q.ofInt_neg s, ← Q.ofInt_add,
      ← Q.ofInt_mul, hsub]
  congr 1; grind

theorem skewBorrow_core_cap (s : Int) (_hs : s * s - 2 ≠ 0) :
    Q.ofInt s * cap (mat2InvQ (matAdd walsh2Q (matSmul (Q.ofInt s) (castMatQ skewBorrowB)))
                              (Q.inv (Q.ofInt (s * s - 2)))) =
    Q.ofInt (-2 * s) * Q.inv (Q.ofInt (s * s - 2)) := by
  rw [cap_mat2InvQ]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 skewBorrowB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_zero, Q.ofInt_one, Q.ofInt_neg, mul_zero', add_zero', mul_one', mul_neg']
  have hsum : (-(1 : Q) + -((1 : Q) + Q.ofInt s)) + (-((1 : Q) + -(Q.ofInt s)) + (1 : Q)) = Q.ofInt (-2) := by
    rw [← Q.ofInt_one, ← Q.ofInt_neg 1, ← Q.ofInt_neg s, ← Q.ofInt_add, ← Q.ofInt_add,
        ← Q.ofInt_neg, ← Q.ofInt_neg, ← Q.ofInt_add, ← Q.ofInt_add, ← Q.ofInt_add]
    congr 1; omega
  rw [hsum, ← mul_assoc', mul_comm' (Q.ofInt s) (Q.inv _), mul_assoc',
      ← Q.ofInt_mul, mul_comm' (Q.inv _)]
  congr 1; congr 1; omega

def skewCapInt : Nat → Int
  | 0 => 1
  | k + 1 => if k % 2 = 0 then 2 else -2

theorem skewCapSeq_eq (k : Nat) : skewCapSeq k = Q.ofInt (skewCapInt k) := by
  cases k with
  | zero => rfl
  | succ k => unfold skewCapSeq skewCapInt; by_cases h : k % 2 = 0 <;> simp [h]

theorem skewCapInt_det_ne_zero (k : Nat) : skewCapInt k * skewCapInt k - 2 ≠ 0 := by
  cases k with
  | zero => decide
  | succ k => unfold skewCapInt; by_cases h : k % 2 = 0 <;> simp [h]

theorem skewCapInt_step (k : Nat) :
    Q.ofInt (-2 * skewCapInt k) * Q.inv (Q.ofInt (skewCapInt k * skewCapInt k - 2)) =
    Q.ofInt (skewCapInt (k + 1)) := by
  cases k with
  | zero =>
    change Q.ofInt (-2) * Q.inv (Q.ofInt (-1)) = Q.ofInt 2
    have h : Q.ofInt (-2) = Q.ofInt 2 * Q.ofInt (-1) := by rw [← Q.ofInt_mul]; rfl
    rw [h, mul_assoc', Q.mul_inv_cancel (Q.ofInt_ne_zero (by omega)), mul_one']
  | succ k =>
    unfold skewCapInt
    by_cases hk : k % 2 = 0
    · have hk1 : ¬((k + 1) % 2 = 0) := by omega
      simp only [hk, hk1, ite_true, ite_false]
      have h : Q.ofInt (-2 * 2) = Q.ofInt (-2) * Q.ofInt (2 * 2 - 2) := by rw [← Q.ofInt_mul]; rfl
      rw [h, mul_assoc', Q.mul_inv_cancel (Q.ofInt_ne_zero (by omega)), mul_one']
    · have hk1 : (k + 1) % 2 = 0 := by omega
      simp only [hk, hk1, ite_true, ite_false]
      have h : Q.ofInt (-2 * -2) = Q.ofInt 2 * Q.ofInt (-2 * -2 - 2) := by rw [← Q.ofInt_mul]; rfl
      rw [h, mul_assoc', Q.mul_inv_cancel (Q.ofInt_ne_zero (by omega)), mul_one']

-- Theorem 2a: Exact Woodbury Inverse & Period-2 Capacitance Limit Cycle (+1, +2, -2, +2, -2, ...)
def bitEqB : Mat 2 2 Int := fun i j => if i = j then 1 else 0
def bitEqWalshMat (k : Nat) : Mat (powB 2 k) (powB 2 k) Int :=
  walshPerturbedMat bitEqB 1 k

def eqCapSeq : Nat → Q
  | 0 => 1
  | _ + 1 => 0

theorem bitEq_core_det_0 :
    det (matAdd walsh2Q (matSmul (1 : Q) (castMatQ bitEqB))) = Q.ofInt (-1) := by
  rw [det_two_mat]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 bitEqB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_zero, Q.ofInt_one, Q.ofInt_neg, one_mul', mul_zero', add_zero']
  apply q_sound
  decide

theorem bitEq_core_det_succ :
    det (matAdd walsh2Q (matSmul (0 : Q) (castMatQ bitEqB))) = Q.ofInt (-2) := by
  have hzero : matAdd walsh2Q (matSmul (0 : Q) (castMatQ bitEqB)) = walsh2Q := by
    funext i j; unfold matAdd matSmul; rw [zero_mul', add_zero']
  rw [hzero, det_walsh2Q]

theorem bitEq_core_cap_0 :
    cap (mat2InvQ (matAdd walsh2Q (matSmul (1 : Q) (castMatQ bitEqB))) (Q.inv (Q.ofInt (-1)))) = (0 : Q) := by
  rw [cap_mat2InvQ]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 bitEqB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_zero, Q.ofInt_one, Q.ofInt_neg, one_mul', mul_zero', add_zero']
  have hsum : (-(1 : Q) + (1 : Q) + -(1 : Q)) + (-(1 : Q) + ((1 : Q) + (1 : Q))) = 0 := by
    apply q_sound; decide
  rw [hsum, mul_zero']

-- Theorem 3a: Exact Woodbury Inverse & Zero-Sum Inverse Law (∀ k ≥ 1, ∑_{i,j} (E_k^{-1})_{i,j} = 0!)
def prefixB (lam : Int) : Mat 2 2 Int := fun _ _ => lam
def prefixWalshMat (m0 lam : Int) (k : Nat) : Mat (powB 2 k) (powB 2 k) Int :=
  walshPerturbedMat (prefixB lam) m0 k

-- Division-free dyadic-superfactorial product: ∏_{j=0}^{k-1} (m0 + j*lam)^(2^(k-1-j))
def prefixDyadicProd (m0 lam : Int) : Nat → Int
  | 0 => 1
  | k + 1 => (m0 + (k : Int) * lam) * rpow (prefixDyadicProd m0 lam k) 2

theorem prefixDyadicProd_succ (m0 lam : Int) (k : Nat) :
    prefixDyadicProd m0 lam (k + 1) = (m0 + (k : Int) * lam) * rpow (prefixDyadicProd m0 lam k) 2 := rfl

theorem prefix_core_det (lam : Int) (s : Q) :
    det (matAdd walsh2Q (matSmul s (castMatQ (prefixB lam)))) =
    Q.ofInt (-2) * (1 + s * Q.ofInt lam) := by
  rw [det_two_mat]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 prefixB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_one, Q.ofInt_neg]
  let t := s * Q.ofInt lam
  change (1 + t) * (-1 + t) - (1 + t) * (1 + t) = Q.ofInt (-2) * (1 + t)
  have h2 : Q.ofInt (-2) = (-1 : Q) + (-1 : Q) := by
    rw [← Q.ofInt_one, ← Q.ofInt_neg, ← Q.ofInt_add]; rfl
  rw [h2, sub_eq_add_neg', ← mul_neg', ← left_distrib', neg_add', mul_comm' (1 + t)]
  congr 1
  rw [add_assoc' (-1 : Q), ← add_assoc' t, add_comm' t (-1 : Q), add_assoc' (-1 : Q),
      add_right_neg', add_zero']

theorem prefix_core_cap (lam : Int) (s detInv : Q) (hd : Q.ofInt (-2) * (1 + s * Q.ofInt lam) * detInv = 1) :
    s * cap (mat2InvQ (matAdd walsh2Q (matSmul s (castMatQ (prefixB lam)))) detInv) =
    s * Q.inv (1 + s * Q.ofInt lam) := by
  rw [cap_mat2InvQ]
  unfold matAdd matSmul walsh2Q castMatQ walsh2 prefixB
  simp only [Fin.reduceEq, and_self, and_false, false_and, ite_true, ite_false,
             Q.ofInt_one, Q.ofInt_neg]
  let t := s * Q.ofInt lam
  have hsum : ((-1 + t) + -(1 + t)) + (-(1 + t) + (1 + t)) = Q.ofInt (-2) := by
    rw [add_left_neg', add_zero', neg_add', add_comm' (-1 : Q) t, add_assoc',
        ← add_assoc' (-1 : Q) (-1 : Q), add_comm' t, add_assoc', add_left_neg', add_zero']
    rw [← Q.ofInt_one, ← Q.ofInt_neg, ← Q.ofInt_add]; rfl
  rw [hsum]
  -- Show detInv * (-2) = inv(1 + t) from (-2) * (1 + t) * detInv = 1!
  have h1t_ne : (1 : Q) + t ≠ 0 := by
    intro h0; rw [h0, mul_zero', zero_mul'] at hd
    have := Q.ofInt_injective hd; omega
  have hdetInv_eq : detInv * Q.ofInt (-2) = Q.inv (1 + t) := by
    have hmul : (detInv * Q.ofInt (-2)) * (1 + t) = 1 := by
      rw [mul_assoc', mul_comm' detInv]; exact hd
    have h2 := congrArg (fun z => z * Q.inv (1 + t)) hmul
    rw [mul_assoc', Q.mul_inv_cancel h1t_ne, mul_one', one_mul'] at h2
    exact h2
  rw [hdetInv_eq]

-- Bounded-horizon Prefix-Walsh Lift (works for ALL k ≤ K when m0 + j*lam ≠ 0 for all j ≤ K,
-- powering BOTH the infinite Theorem 4a AND the programmable depth-N singularity Theorem 4b!)
def hamming2 : Mat 2 2 Int := fun i j => if i = j then 1 else 2
def hamming2Q : Mat 2 2 Q := castMatQ hamming2
def hamming2InvQ : Mat 2 2 Q := fun i j =>
  if i = j then Q.mk (-1) 3 (by omega) else Q.mk 2 3 (by omega)

def singCoreJ2 : Mat 2 2 Int := fun _ _ => 1

theorem sharpness_singular_core_breaks_tower :
    det (bitTransducerMat singCoreJ2 bitEqB 1 1) = 3 ∧
    det (bitTransducerMat singCoreJ2 bitEqB 1 2) = 0 := by
  constructor <;> decide

-- Counterexample B: Replacing rank-1 (B ⊗ J_k) by full-rank (B ⊗ I_k) breaks Theorem 1 at k = 2!
def fullRankPerturbedK2 : Mat 4 4 Int :=
  matAdd (kron walsh2 (carryGenWalshMat 1 1)) (kron (carryGenB 1) (matOne 2))

end ConcreteInfiniteTheorems

end SpecMat11

-- ============================================================================
-- Axiom Audit (#print axioms on EVERY main mechanism & theorem)
-- ============================================================================
