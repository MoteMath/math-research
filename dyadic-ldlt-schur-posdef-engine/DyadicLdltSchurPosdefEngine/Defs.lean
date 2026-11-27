/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`dyadic-ldlt-schur-posdef-engine`)

Exact Dyadic LDL-Transpose Positive-Definiteness Infinite Certificate Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace DyadicLDLT


-- ============================================================================
-- LAYER 1: EXACT DYADIC RING Z[1/2]
-- ============================================================================

/-- Exact dyadic rational `mant * 2^(-shift)` in `Z[1/2]`. Pure silicon binary math. -/
structure Dyad where
  mant  : Int
  shift : Nat
  deriving Repr, DecidableEq

namespace Dyad


def zero : Dyad := ⟨0, 0⟩

def one  : Dyad := ⟨1, 0⟩

def ofInt (z : Int) : Dyad := ⟨z, 0⟩

def pow2Neg (s : Nat) : Dyad := ⟨1, s⟩

def add (a b : Dyad) : Dyad :=
  ⟨a.mant * (2 ^ b.shift : Int) + b.mant * (2 ^ a.shift : Int), a.shift + b.shift⟩

def neg (a : Dyad) : Dyad :=
  ⟨-a.mant, a.shift⟩

def sub (a b : Dyad) : Dyad :=
  add a (neg b)

def mul (a b : Dyad) : Dyad :=
  ⟨a.mant * b.mant, a.shift + b.shift⟩

def shr (a : Dyad) (s : Nat) : Dyad :=
  ⟨a.mant, a.shift + s⟩

def pow (a : Dyad) : Nat → Dyad
  | 0     => one
  | k + 1 => mul a (pow a k)

instance : Add Dyad := ⟨add⟩

instance : Sub Dyad := ⟨sub⟩

instance : Mul Dyad := ⟨mul⟩

instance : Neg Dyad := ⟨neg⟩

/-- Exact equality in `Z[1/2]`: `a.mant * 2^b.shift = b.mant * 2^a.shift`. -/
def deq (a b : Dyad) : Prop :=
  a.mant * (2 ^ b.shift : Int) = b.mant * (2 ^ a.shift : Int)

/-- Exact non-strict order in `Z[1/2]`. -/
def dle (a b : Dyad) : Prop :=
  a.mant * (2 ^ b.shift : Int) ≤ b.mant * (2 ^ a.shift : Int)

/-- Exact strict order in `Z[1/2]`. -/
def dlt (a b : Dyad) : Prop :=
  a.mant * (2 ^ b.shift : Int) < b.mant * (2 ^ a.shift : Int)

infix:50 " ≈ " => deq

infix:50 " ≤ᵈ " => dle

infix:50 " <ᵈ " => dlt

instance (a b : Dyad) : Decidable (a ≈ b) := inferInstanceAs (Decidable (_ = _))

instance (a b : Dyad) : Decidable (a ≤ᵈ b) := inferInstanceAs (Decidable (_ ≤ _))

instance (a b : Dyad) : Decidable (a <ᵈ b) := inferInstanceAs (Decidable (_ < _))

theorem two_pow_pos (s : Nat) : (0 : Int) < (2 ^ s : Int) := by
  induction s with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    omega

theorem two_pow_ne_zero (s : Nat) : (2 ^ s : Int) ≠ 0 := by
  have h := two_pow_pos s
  omega

theorem two_pow_add (s t : Nat) : (2 ^ (s + t) : Int) = (2 ^ s : Int) * (2 ^ t : Int) :=
  Int.pow_add 2 s t

theorem mul_cancel_two_pow {x y : Int} {s : Nat}
    (h : x * (2 ^ s : Int) = y * (2 ^ s : Int)) : x = y :=
  Int.eq_of_mul_eq_mul_right (two_pow_ne_zero s) h

theorem le_cancel_two_pow {x y : Int} {s : Nat}
    (h : x * (2 ^ s : Int) ≤ y * (2 ^ s : Int)) : x ≤ y := by
  by_cases hle : x ≤ y
  · exact hle
  · have hgt : y < x := by omega
    have hmul : y * (2 ^ s : Int) < x * (2 ^ s : Int) :=
      Int.mul_lt_mul_of_pos_right hgt (two_pow_pos s)
    omega

theorem lt_cancel_two_pow {x y : Int} {s : Nat}
    (h : x * (2 ^ s : Int) < y * (2 ^ s : Int)) : x < y := by
  by_cases hlt : x < y
  · exact hlt
  · have hle : y ≤ x := by omega
    have hmul : y * (2 ^ s : Int) ≤ x * (2 ^ s : Int) :=
      Int.mul_le_mul_of_nonneg_right hle (Int.le_of_lt (two_pow_pos s))
    omega

-- Equivalence relation & Trans instances for calc

theorem deq_refl (a : Dyad) : a ≈ a := rfl

theorem deq_symm {a b : Dyad} (h : a ≈ b) : b ≈ a := h.symm

theorem deq_trans {a b c : Dyad} (h1 : a ≈ b) (h2 : b ≈ c) : a ≈ c := by
  unfold deq at *
  apply mul_cancel_two_pow (s := b.shift)
  calc
    a.mant * (2 ^ c.shift : Int) * (2 ^ b.shift : Int)
        = (a.mant * (2 ^ b.shift : Int)) * (2 ^ c.shift : Int) := by
          rw [Int.mul_assoc, Int.mul_comm (2 ^ c.shift : Int), ← Int.mul_assoc]
    _ = (b.mant * (2 ^ a.shift : Int)) * (2 ^ c.shift : Int) := by rw [h1]
    _ = (b.mant * (2 ^ c.shift : Int)) * (2 ^ a.shift : Int) := by
          rw [Int.mul_assoc, Int.mul_comm (2 ^ a.shift : Int), ← Int.mul_assoc]
    _ = (c.mant * (2 ^ b.shift : Int)) * (2 ^ a.shift : Int) := by rw [h2]
    _ = c.mant * (2 ^ a.shift : Int) * (2 ^ b.shift : Int) := by
          rw [Int.mul_assoc, Int.mul_comm (2 ^ b.shift : Int), ← Int.mul_assoc]

instance : Trans deq deq deq where trans := deq_trans

-- Congruences

theorem add_congr {a b c d : Dyad} (h1 : a ≈ b) (h2 : c ≈ d) : a + c ≈ b + d := by
  show (a.mant * (2 ^ c.shift : Int) + c.mant * (2 ^ a.shift : Int)) * (2 ^ (b.shift + d.shift) : Int) =
       (b.mant * (2 ^ d.shift : Int) + d.mant * (2 ^ b.shift : Int)) * (2 ^ (a.shift + c.shift) : Int)
  unfold deq at h1 h2
  rw [two_pow_add, two_pow_add, Int.add_mul, Int.add_mul]
  have t1 : a.mant * (2 ^ c.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int)) =
            b.mant * (2 ^ d.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by
    calc
      a.mant * (2 ^ c.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int))
          = (a.mant * (2 ^ b.shift : Int)) * ((2 ^ c.shift : Int) * (2 ^ d.shift : Int)) := by ac_rfl
      _ = (b.mant * (2 ^ a.shift : Int)) * ((2 ^ c.shift : Int) * (2 ^ d.shift : Int)) := by rw [h1]
      _ = b.mant * (2 ^ d.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by ac_rfl
  have t2 : c.mant * (2 ^ a.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int)) =
            d.mant * (2 ^ b.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by
    calc
      c.mant * (2 ^ a.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int))
          = (c.mant * (2 ^ d.shift : Int)) * ((2 ^ a.shift : Int) * (2 ^ b.shift : Int)) := by ac_rfl
      _ = (d.mant * (2 ^ c.shift : Int)) * ((2 ^ a.shift : Int) * (2 ^ b.shift : Int)) := by rw [h2]
      _ = d.mant * (2 ^ b.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by ac_rfl
  rw [t1, t2]

theorem neg_congr {a b : Dyad} (h : a ≈ b) : -a ≈ -b := by
  show (-a.mant) * (2 ^ b.shift : Int) = (-b.mant) * (2 ^ a.shift : Int)
  unfold deq at h
  rw [Int.neg_mul, Int.neg_mul, h]

theorem sub_congr {a b c d : Dyad} (h1 : a ≈ b) (h2 : c ≈ d) : a - c ≈ b - d :=
  add_congr h1 (neg_congr h2)

theorem mul_congr {a b c d : Dyad} (h1 : a ≈ b) (h2 : c ≈ d) : a * c ≈ b * d := by
  show (a.mant * c.mant) * (2 ^ (b.shift + d.shift) : Int) =
       (b.mant * d.mant) * (2 ^ (a.shift + c.shift) : Int)
  unfold deq at h1 h2
  rw [two_pow_add, two_pow_add]
  calc
    a.mant * c.mant * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int))
        = (a.mant * (2 ^ b.shift : Int)) * (c.mant * (2 ^ d.shift : Int)) := by
          simp only [Int.mul_assoc, Int.mul_left_comm]
    _ = (b.mant * (2 ^ a.shift : Int)) * (d.mant * (2 ^ c.shift : Int)) := by rw [h1, h2]
    _ = b.mant * d.mant * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by
          simp only [Int.mul_assoc, Int.mul_left_comm]

theorem add_comm (a b : Dyad) : a + b ≈ b + a := by
  show (a.mant * (2 ^ b.shift : Int) + b.mant * (2 ^ a.shift : Int)) * (2 ^ (b.shift + a.shift) : Int) =
       (b.mant * (2 ^ a.shift : Int) + a.mant * (2 ^ b.shift : Int)) * (2 ^ (a.shift + b.shift) : Int)
  rw [Int.add_comm (a.mant * _), Nat.add_comm b.shift a.shift]

theorem add_assoc (a b c : Dyad) : (a + b) + c ≈ a + (b + c) := by
  show ((a.mant * (2 ^ b.shift : Int) + b.mant * (2 ^ a.shift : Int)) * (2 ^ c.shift : Int) +
        c.mant * (2 ^ (a.shift + b.shift) : Int)) * (2 ^ (a.shift + (b.shift + c.shift)) : Int) =
       (a.mant * (2 ^ (b.shift + c.shift) : Int) +
        (b.mant * (2 ^ c.shift : Int) + c.mant * (2 ^ b.shift : Int)) * (2 ^ a.shift : Int)) *
       (2 ^ ((a.shift + b.shift) + c.shift) : Int)
  rw [Nat.add_assoc a.shift b.shift c.shift]
  congr 1
  rw [two_pow_add, two_pow_add, Int.add_mul, Int.add_mul, Int.add_assoc]
  congr 1
  · ac_rfl
  · congr 1 <;> ac_rfl

theorem add_zero (a : Dyad) : a + zero ≈ a := by
  show (a.mant * (2 ^ 0 : Int) + 0 * (2 ^ a.shift : Int)) * (2 ^ a.shift : Int) =
       a.mant * (2 ^ (a.shift + 0) : Int)
  simp

theorem zero_add (a : Dyad) : zero + a ≈ a :=
  deq_trans (add_comm zero a) (add_zero a)

theorem add_neg (a : Dyad) : a + (-a) ≈ zero := by
  show (a.mant * (2 ^ a.shift : Int) + (-a.mant) * (2 ^ a.shift : Int)) * (2 ^ 0 : Int) =
       0 * (2 ^ (a.shift + a.shift) : Int)
  rw [Int.neg_mul]
  omega

theorem neg_add (a b : Dyad) : -(a + b) ≈ (-a) + (-b) := by
  show (-(a.mant * (2 ^ b.shift : Int) + b.mant * (2 ^ a.shift : Int))) * (2 ^ (a.shift + b.shift) : Int) =
       ((-a.mant) * (2 ^ b.shift : Int) + (-b.mant) * (2 ^ a.shift : Int)) * (2 ^ (a.shift + b.shift) : Int)
  congr 1
  rw [Int.neg_mul, Int.neg_mul]
  omega

theorem sub_add_cancel (a b : Dyad) : (a - b) + b ≈ a := by
  calc
    (a - b) + b = (a + (-b)) + b := rfl
    _ ≈ a + ((-b) + b) := add_assoc a (-b) b
    _ ≈ a + (b + (-b)) := add_congr (deq_refl a) (add_comm (-b) b)
    _ ≈ a + zero := add_congr (deq_refl a) (add_neg b)
    _ ≈ a := add_zero a

theorem mul_comm (a b : Dyad) : a * b ≈ b * a := by
  show (a.mant * b.mant) * (2 ^ (b.shift + a.shift) : Int) =
       (b.mant * a.mant) * (2 ^ (a.shift + b.shift) : Int)
  rw [Int.mul_comm a.mant b.mant, Nat.add_comm b.shift a.shift]

theorem mul_assoc (a b c : Dyad) : (a * b) * c ≈ a * (b * c) := by
  show (a.mant * b.mant * c.mant) * (2 ^ (a.shift + (b.shift + c.shift)) : Int) =
       (a.mant * (b.mant * c.mant)) * (2 ^ ((a.shift + b.shift) + c.shift) : Int)
  rw [Int.mul_assoc a.mant b.mant c.mant, Nat.add_assoc a.shift b.shift c.shift]

theorem mul_one (a : Dyad) : a * one ≈ a := by
  show (a.mant * 1) * (2 ^ a.shift : Int) = a.mant * (2 ^ (a.shift + 0) : Int)
  simp

theorem one_mul (a : Dyad) : one * a ≈ a :=
  deq_trans (mul_comm one a) (mul_one a)

theorem mul_zero (a : Dyad) : a * zero ≈ zero := by
  show (a.mant * 0) * (2 ^ 0 : Int) = 0 * (2 ^ (a.shift + 0) : Int)
  simp

theorem zero_mul (a : Dyad) : zero * a ≈ zero :=
  deq_trans (mul_comm zero a) (mul_zero a)

theorem mul_add (a b c : Dyad) : a * (b + c) ≈ a * b + a * c := by
  show (a.mant * (b.mant * (2 ^ c.shift : Int) + c.mant * (2 ^ b.shift : Int))) *
       (2 ^ ((a.shift + b.shift) + (a.shift + c.shift)) : Int) =
       (a.mant * b.mant * (2 ^ (a.shift + c.shift) : Int) +
        a.mant * c.mant * (2 ^ (a.shift + b.shift) : Int)) *
       (2 ^ (a.shift + (b.shift + c.shift)) : Int)
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  congr 1
  · rw [two_pow_add, two_pow_add, two_pow_add, two_pow_add, two_pow_add]
    simp only [Int.mul_assoc, Int.mul_left_comm]
  · rw [two_pow_add, two_pow_add, two_pow_add, two_pow_add, two_pow_add]
    simp only [Int.mul_assoc, Int.mul_left_comm]

theorem add_mul (a b c : Dyad) : (a + b) * c ≈ a * c + b * c :=
  deq_trans (mul_comm (a + b) c)
    (deq_trans (mul_add c a b) (add_congr (mul_comm c a) (mul_comm c b)))

theorem neg_mul (a b : Dyad) : (-a) * b ≈ -(a * b) := by
  show ((-a.mant) * b.mant) * (2 ^ (a.shift + b.shift) : Int) =
       (-(a.mant * b.mant)) * (2 ^ (a.shift + b.shift) : Int)
  rw [Int.neg_mul]

theorem mul_neg (a b : Dyad) : a * (-b) ≈ -(a * b) :=
  deq_trans (mul_comm a (-b)) (deq_trans (neg_mul b a) (neg_congr (mul_comm b a)))

theorem mul_sub (a b c : Dyad) : a * (b - c) ≈ a * b - a * c :=
  deq_trans (mul_add a b (-c)) (add_congr (deq_refl _) (mul_neg a c))

theorem sub_mul (a b c : Dyad) : (a - b) * c ≈ a * c - b * c :=
  deq_trans (add_mul a (-b) c) (add_congr (deq_refl _) (neg_mul b c))

theorem pow2Neg_zero : pow2Neg 0 ≈ one := rfl

theorem pow2Neg_mul (s t : Nat) : pow2Neg s * pow2Neg t ≈ pow2Neg (s + t) := by
  show (1 * 1 : Int) * (2 ^ (s + t) : Int) = 1 * (2 ^ (s + t) : Int)
  simp

theorem add_sub_comm (a b c : Dyad) : (a - b) + c ≈ (a + c) - b := by
  calc
    (a + (-b)) + c ≈ a + ((-b) + c) := add_assoc a (-b) c
    _ ≈ a + (c + (-b)) := add_congr (deq_refl a) (add_comm (-b) c)
    _ ≈ (a + c) + (-b) := deq_symm (add_assoc a c (-b))

theorem sub_sub_eq_sub_add (a b c : Dyad) : (a - b) - c ≈ a - (b + c) := by
  calc
    (a + (-b)) + (-c) ≈ a + ((-b) + (-c)) := add_assoc a (-b) (-c)
    _ ≈ a + (-(b + c)) := add_congr (deq_refl a) (deq_symm (neg_add b c))

theorem sub_sub_comm (a b c : Dyad) : (a - b) - c ≈ (a - c) - b :=
  add_sub_comm a b (-c)

theorem dle_of_deq {a b : Dyad} (h : a ≈ b) : a ≤ᵈ b := Int.le_of_eq h

theorem dle_of_dlt {a b : Dyad} (h : a <ᵈ b) : a ≤ᵈ b := Int.le_of_lt h

theorem dle_trans {a b c : Dyad} (h1 : a ≤ᵈ b) (h2 : b ≤ᵈ c) : a ≤ᵈ c := by
  unfold dle at *
  apply le_cancel_two_pow (s := b.shift)
  have hc := Int.le_of_lt (two_pow_pos c.shift)
  have ha := Int.le_of_lt (two_pow_pos a.shift)
  calc
    a.mant * (2 ^ c.shift : Int) * (2 ^ b.shift : Int)
        = (a.mant * (2 ^ b.shift : Int)) * (2 ^ c.shift : Int) := by ac_rfl
    _ ≤ (b.mant * (2 ^ a.shift : Int)) * (2 ^ c.shift : Int) :=
          Int.mul_le_mul_of_nonneg_right h1 hc
    _ = (b.mant * (2 ^ c.shift : Int)) * (2 ^ a.shift : Int) := by ac_rfl
    _ ≤ (c.mant * (2 ^ b.shift : Int)) * (2 ^ a.shift : Int) :=
          Int.mul_le_mul_of_nonneg_right h2 ha
    _ = c.mant * (2 ^ a.shift : Int) * (2 ^ b.shift : Int) := by ac_rfl

theorem dlt_of_dlt_of_dle {a b c : Dyad} (h1 : a <ᵈ b) (h2 : b ≤ᵈ c) : a <ᵈ c := by
  unfold dlt dle at *
  apply lt_cancel_two_pow (s := b.shift)
  have hc := two_pow_pos c.shift
  have ha := Int.le_of_lt (two_pow_pos a.shift)
  calc
    a.mant * (2 ^ c.shift : Int) * (2 ^ b.shift : Int)
        = (a.mant * (2 ^ b.shift : Int)) * (2 ^ c.shift : Int) := by ac_rfl
    _ < (b.mant * (2 ^ a.shift : Int)) * (2 ^ c.shift : Int) :=
          Int.mul_lt_mul_of_pos_right h1 hc
    _ = (b.mant * (2 ^ c.shift : Int)) * (2 ^ a.shift : Int) := by ac_rfl
    _ ≤ (c.mant * (2 ^ b.shift : Int)) * (2 ^ a.shift : Int) :=
          Int.mul_le_mul_of_nonneg_right h2 ha
    _ = c.mant * (2 ^ a.shift : Int) * (2 ^ b.shift : Int) := by ac_rfl

theorem dlt_of_dle_of_dlt {a b c : Dyad} (h1 : a ≤ᵈ b) (h2 : b <ᵈ c) : a <ᵈ c := by
  unfold dlt dle at *
  apply lt_cancel_two_pow (s := b.shift)
  have hc := Int.le_of_lt (two_pow_pos c.shift)
  have ha := two_pow_pos a.shift
  calc
    a.mant * (2 ^ c.shift : Int) * (2 ^ b.shift : Int)
        = (a.mant * (2 ^ b.shift : Int)) * (2 ^ c.shift : Int) := by ac_rfl
    _ ≤ (b.mant * (2 ^ a.shift : Int)) * (2 ^ c.shift : Int) :=
          Int.mul_le_mul_of_nonneg_right h1 hc
    _ = (b.mant * (2 ^ c.shift : Int)) * (2 ^ a.shift : Int) := by ac_rfl
    _ < (c.mant * (2 ^ b.shift : Int)) * (2 ^ a.shift : Int) :=
          Int.mul_lt_mul_of_pos_right h2 ha
    _ = c.mant * (2 ^ a.shift : Int) * (2 ^ b.shift : Int) := by ac_rfl

theorem dlt_trans {a b c : Dyad} (h1 : a <ᵈ b) (h2 : b <ᵈ c) : a <ᵈ c :=
  dlt_of_dlt_of_dle h1 (dle_of_dlt h2)

instance : Trans dle dle dle where trans := dle_trans

instance : Trans dlt dle dlt where trans := dlt_of_dlt_of_dle

instance : Trans dle dlt dlt where trans := dlt_of_dle_of_dlt

instance : Trans dlt dlt dlt where trans := dlt_trans

instance : Trans deq dle dle where trans h1 h2 := dle_trans (dle_of_deq h1) h2

instance : Trans dle deq dle where trans h1 h2 := dle_trans h1 (dle_of_deq h2)

instance : Trans deq dlt dlt where trans h1 h2 := dlt_of_dle_of_dlt (dle_of_deq h1) h2

instance : Trans dlt deq dlt where trans h1 h2 := dlt_of_dlt_of_dle h1 (dle_of_deq h2)

end Dyad

open Dyad

-- ============================================================================
-- LAYER 2: EXACT DYADIC SUMS, MATRICES, AND GENERAL LDL^T ENGINE (EXACT IFF!)
-- ============================================================================

/-- Finite dyadic sum `∑_{i=0}^{n-1} f i`. -/
def dsum : Nat → (Nat → Dyad) → Dyad
  | 0, _     => zero
  | n + 1, f => dsum n f + f n

theorem dsum_congr {n : Nat} {f g : Nat → Dyad}
    (h : ∀ i, i < n → f i ≈ g i) : dsum n f ≈ dsum n g := by
  induction n with
  | zero => exact deq_refl _
  | succ k ih =>
    exact add_congr (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

theorem dsum_zero (n : Nat) : dsum n (fun _ => zero) ≈ zero := by
  induction n with
  | zero => exact deq_refl _
  | succ k ih => exact deq_trans (add_congr ih (deq_refl _)) (add_zero zero)

theorem dsum_eq_zero {n : Nat} {f : Nat → Dyad}
    (h : ∀ i, i < n → f i ≈ zero) : dsum n f ≈ zero :=
  deq_trans (dsum_congr h) (dsum_zero n)

theorem dsum_single {n r : Nat} (hr : r < n) (f : Nat → Dyad)
    (hz : ∀ i, i < n → i ≠ r → f i ≈ zero) :
    dsum n f ≈ f r := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hkr : k = r
    · subst hkr
      have hpre : dsum k f ≈ zero :=
        dsum_eq_zero (fun i hi => hz i (Nat.lt_succ_of_lt hi) (by omega))
      exact deq_trans (add_congr hpre (deq_refl _)) (zero_add _)
    · have hrk : r < k := by omega
      have hpre := ih hrk (fun i hi hne => hz i (Nat.lt_succ_of_lt hi) hne)
      have hlast : f k ≈ zero := hz k (Nat.lt_succ_self k) hkr
      exact deq_trans (add_congr hpre hlast) (add_zero _)

abbrev Vec := Nat → Dyad

abbrev Mat := Nat → Nat → Dyad

def matMul (N : Nat) (A B : Mat) : Mat :=
  fun i j => dsum N (fun r => A i r * B r j)

def matMulT (N : Nat) (A B : Mat) : Mat :=
  fun i j => dsum N (fun r => A i r * B j r)

def matTVec (N : Nat) (L : Mat) (v : Vec) : Vec :=
  fun r => dsum N (fun i => L i r * v i)

def quadForm (N : Nat) (M : Mat) (v : Vec) : Dyad :=
  dsum N (fun i => dsum N (fun j => v i * M i j * v j))

def StrictlyPosDef (N : Nat) (M : Mat) : Prop :=
  ∀ v : Vec, (∃ i, i < N ∧ ¬ (v i ≈ zero)) → zero <ᵈ quadForm N M v

def IsUnitLowerTri (N : Nat) (L : Mat) : Prop :=
  (∀ i, i < N → L i i ≈ one) ∧
  (∀ i j, i < N → j < N → i < j → L i j ≈ zero)

/-- Exact dyadic algebraic `LDL^T` factorization on `[0, N)` (pivots unrestricted in sign). -/
structure IsLDLTAlg (N : Nat) (M L : Mat) (D : Vec) : Prop where
  unitLower : IsUnitLowerTri N L
  factor : ∀ i j, i < N → j < N →
    M i j ≈ dsum N (fun r => L i r * D r * L j r)

/-- Exact dyadic positive-definite `LDL^T` certificate on `[0, N)`. -/
structure IsLDLTPos (N : Nat) (M L : Mat) (D : Vec) : Prop extends IsLDLTAlg N M L D where
  pivotsPos : ∀ r, r < N → zero <ᵈ D r

/-- Exact back-substitution in `Z[1/2]` solving `L^T w ≈ e_{r*}` (zero division!). -/
def backSubAux (N : Nat) (L : Mat) (rStar : Nat) : Nat → Vec
  | 0     => fun _ => zero
  | m + 1 =>
    let prev := backSubAux N L rStar m
    let idx := N - 1 - m
    let rhs := if idx = rStar then one else zero
    let tail := dsum m (fun t => L (N - 1 - t) idx * prev (N - 1 - t))
    let val := rhs - tail
    fun i => if i = idx then val else prev i

/-- Exact back-substitution vector `w` in `Z[1/2]` satisfying `L^T w ≈ e_{r*}`. -/
def backSubVec (N : Nat) (L : Mat) (rStar : Nat) : Vec :=
  backSubAux N L rStar N

/-- Block-combined lower-triangular factor `[[L_A, 0], [E * L_A, L_S]]`. -/
def blockL (N : Nat) (E L_A L_S : Mat) : Mat :=
  fun i j =>
    if i < N then
      if j < N then L_A i j else zero
    else
      if j < N then matMul N E L_A (i - N) j else L_S (i - N) (j - N)

/-- Block-concatenated pivot vector `D_A || D_S`. -/
def blockD (N : Nat) (D_A D_S : Vec) : Vec :=
  fun r => if r < N then D_A r else D_S (r - N)

/-- **REUSABLE INFINITE PROOF MECHANISM**:
    A `SchurSystem State` specifies a finite/parametric state-machine block-Schur recurrence
    over exact `Z[1/2]` matrices with arbitrary dyadic coupling operator `coupling σ k`.
    The engine automatically lifts it to an exact `LDL^T` factorization for ALL `k : Nat`! -/
structure SchurSystem (State : Type) where
  mat        : State → Nat → Mat
  leftState  : State → Nat → State
  rightState : State → Nat → State
  coupling   : State → Nat → Mat
  tl_eq : ∀ σ k i j, i < 2 ^ k → j < 2 ^ k →
    mat σ (k + 1) i j ≈ mat (leftState σ k) k i j
  bl_eq : ∀ σ k i j, i < 2 ^ k → j < 2 ^ k →
    mat σ (k + 1) (2 ^ k + i) j ≈ matMul (2 ^ k) (coupling σ k) (mat (leftState σ k) k) i j
  tr_eq : ∀ σ k i j, i < 2 ^ k → j < 2 ^ k →
    mat σ (k + 1) i (2 ^ k + j) ≈ matMul (2 ^ k) (coupling σ k) (mat (leftState σ k) k) j i
  br_eq : ∀ σ k i j, i < 2 ^ k → j < 2 ^ k →
    mat σ (k + 1) (2 ^ k + i) (2 ^ k + j) ≈
      mat (rightState σ k) k i j +
      matMulT (2 ^ k) (matMul (2 ^ k) (coupling σ k) (mat (leftState σ k) k)) (coupling σ k) i j

/-- Computable recursive exact dyadic unit lower-triangular factor `L` generated by `S`. -/
def schurL {State : Type} (S : SchurSystem State) : State → Nat → Mat
  | _, 0     => fun i j => if i = j then one else zero
  | σ, k + 1 => blockL (2 ^ k) (S.coupling σ k) (schurL S (S.leftState σ k) k)
                  (schurL S (S.rightState σ k) k)

/-- Computable recursive exact dyadic pivot vector `D` generated by `S`:
    traverses the binary bits of `r` (MSB-first) through `(leftState, rightState)`. -/
def schurD {State : Type} (S : SchurSystem State) : State → Nat → Vec
  | σ, 0     => fun _ => S.mat σ 0 0 0
  | σ, k + 1 => blockD (2 ^ k) (schurD S (S.leftState σ k) k) (schurD S (S.rightState σ k) k)

/-- Scalar coupling `E = q * I`: `matMul N (scalarMat q) A i j ≈ q * A i j`. -/
def scalarMat (q : Dyad) : Mat :=
  fun i j => if i = j then q else zero

theorem matMul_scalarMat {N : Nat} (q : Dyad) (A : Mat) {i j : Nat} (hi : i < N) :
    matMul N (scalarMat q) A i j ≈ q * A i j := by
  unfold matMul scalarMat
  have h := dsum_single hi (fun r => (if i = r then q else zero) * A r j) (fun r _ hne => by
    have hne' : i ≠ r := Ne.symm hne
    simp only [hne', ↓reduceIte]
    exact zero_mul _)
  simpa using h

theorem matMulT_scalarMat {N : Nat} (q : Dyad) (A : Mat) {i j : Nat} (hj : j < N) :
    matMulT N A (scalarMat q) i j ≈ A i j * q := by
  unfold matMulT scalarMat
  have h := dsum_single hj (fun r => A i r * (if j = r then q else zero)) (fun r _ hne => by
    have hne' : j ≠ r := Ne.symm hne
    simp only [hne', ↓reduceIte]
    exact mul_zero _)
  simpa using h

/-- Antidiagonal bit-reflection coupling `E = q * J_N`: `(E)_{i,r} = q` iff `r = N - 1 - i`. -/
def reflectMat (N : Nat) (q : Dyad) : Mat :=
  fun i r => if r = N - 1 - i then q else zero

theorem matMul_reflectMat {N : Nat} (q : Dyad) (A : Mat) {i j : Nat} (hi : i < N) :
    matMul N (reflectMat N q) A i j ≈ q * A (N - 1 - i) j := by
  unfold matMul reflectMat
  have hr : N - 1 - i < N := by omega
  have h := dsum_single hr (fun r => (if r = N - 1 - i then q else zero) * A r j) (fun r _ hne => by
    simp only [hne, ↓reduceIte]
    exact zero_mul _)
  simpa using h

theorem matMulT_reflectMat {N : Nat} (q : Dyad) (A : Mat) {i j : Nat} (hj : j < N) :
    matMulT N A (reflectMat N q) i j ≈ A i (N - 1 - j) * q := by
  unfold matMulT reflectMat
  have hr : N - 1 - j < N := by omega
  have h := dsum_single hr (fun r => A i r * (if r = N - 1 - j then q else zero)) (fun r _ hne => by
    simp only [hne, ↓reduceIte]
    exact mul_zero _)
  simpa using h

/-- Rank-1 boundary coupling `E = v * e_{N-1}^T`: nonzero ONLY in column `N - 1`. -/
def boundaryMat (N : Nat) (v : Vec) : Mat :=
  fun i r => if r = N - 1 then v i else zero

theorem matMul_boundaryMat {N : Nat} (hN : 0 < N) (v : Vec) (A : Mat) (i j : Nat) :
    matMul N (boundaryMat N v) A i j ≈ v i * A (N - 1) j := by
  unfold matMul boundaryMat
  have hr : N - 1 < N := by omega
  have h := dsum_single hr (fun r => (if r = N - 1 then v i else zero) * A r j) (fun r _ hne => by
    simp only [hne, ↓reduceIte]
    exact zero_mul _)
  simpa using h

theorem matMulT_boundaryMat {N : Nat} (hN : 0 < N) (v : Vec) (A : Mat) (i j : Nat) :
    matMulT N A (boundaryMat N v) i j ≈ A i (N - 1) * v j := by
  unfold matMulT boundaryMat
  have hr : N - 1 < N := by omega
  have h := dsum_single hr (fun r => A i r * (if r = N - 1 then v j else zero)) (fun r _ hne => by
    simp only [hne, ↓reduceIte]
    exact mul_zero _)
  simpa using h

-- ============================================================================
-- LAYER 4A: PURE SILICON BITWISE PRIMITIVES ON `Nat`
-- ============================================================================

theorem testBit_two_pow_add {k x j : Nat} (hx : x < 2 ^ k) :
    (2 ^ k + x).testBit j = if j = k then true else x.testBit j := by
  induction k generalizing x j with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    cases j with
    | zero => decide
    | succ m =>
      have hne : m + 1 ≠ 0 := by omega
      have hlt : 1 < 2 ^ (m + 1) := by
        rw [Nat.pow_succ]
        have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
        omega
      simp only [hne, ↓reduceIte, Nat.pow_zero, Nat.add_zero, Nat.zero_testBit]
      exact Nat.testBit_lt_two_pow hlt
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    cases j with
    | zero =>
      have hne : (0 : Nat) ≠ k + 1 := by omega
      simp only [hne, ↓reduceIte, Nat.testBit_zero]
      rw [hpow]
      have hmod : (2 * 2 ^ k + x) % 2 = x % 2 := by omega
      rw [hmod]
    | succ m =>
      have hdiv : (2 ^ (k + 1) + x) / 2 = 2 ^ k + x / 2 := by rw [hpow]; omega
      have hx' : x / 2 < 2 ^ k := by rw [hpow] at hx; omega
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv, ih hx']
      by_cases hmk : m = k
      · subst hmk; simp
      · simp [hmk]

theorem xor_lt_two_pow {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x ^^^ y < 2 ^ k :=
  Nat.xor_lt_two_pow hx hy

theorem and_lt_two_pow {k x y : Nat} (hx : x < 2 ^ k) :
    x &&& y < 2 ^ k := by
  have hle : x &&& y ≤ x := Nat.and_le_left
  omega

theorem xor_add_two_pow_left {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (2 ^ k + x) ^^^ y = 2 ^ k + (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_two_pow_add hx, testBit_two_pow_add (xor_lt_two_pow hx hy), Nat.testBit_xor]
  by_cases hjk : j = k
  · subst hjk
    have hyk : y.testBit j = false := Nat.testBit_lt_two_pow hy
    simp [hyk]
  · simp [hjk]

theorem xor_add_two_pow_right {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x ^^^ (2 ^ k + y) = 2 ^ k + (x ^^^ y) := by
  rw [Nat.xor_comm, xor_add_two_pow_left hy hx, Nat.xor_comm]

theorem xor_add_two_pow_both {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (2 ^ k + x) ^^^ (2 ^ k + y) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_two_pow_add hx, testBit_two_pow_add hy, Nat.testBit_xor]
  by_cases hjk : j = k
  · subst hjk
    have hxk : x.testBit j = false := Nat.testBit_lt_two_pow hx
    have hyk : y.testBit j = false := Nat.testBit_lt_two_pow hy
    simp [hxk, hyk]
  · simp [hjk]

theorem and_add_two_pow_left {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (2 ^ k + x) &&& y = x &&& y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, testBit_two_pow_add hx, Nat.testBit_and]
  by_cases hjk : j = k
  · subst hjk
    have hyk : y.testBit j = false := Nat.testBit_lt_two_pow hy
    simp [hyk]
  · simp [hjk]

theorem and_add_two_pow_right {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x &&& (2 ^ k + y) = x &&& y := by
  rw [Nat.and_comm, and_add_two_pow_left hy hx, Nat.and_comm]

theorem and_add_two_pow_both {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    (2 ^ k + x) &&& (2 ^ k + y) = 2 ^ k + (x &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, testBit_two_pow_add hx, testBit_two_pow_add hy,
      testBit_two_pow_add (and_lt_two_pow hx), Nat.testBit_and]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-- Structurally recursive population count (Hamming weight) on `Nat` for instant kernel reduction. -/
def popcountAux : Nat → Nat → Nat
  | 0, _     => 0
  | f + 1, n => if n = 0 then 0 else n % 2 + popcountAux f (n / 2)

def popcount (n : Nat) : Nat := popcountAux n n

theorem popcountAux_eq_of_le : ∀ f g n, n ≤ f → n ≤ g → popcountAux f n = popcountAux g n := by
  intro f
  induction f with
  | zero =>
    intro g n hnf _
    have hn0 : n = 0 := by omega
    subst hn0
    cases g <;> simp [popcountAux]
  | succ f ih =>
    intro g n hnf hng
    cases g with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0; simp [popcountAux]
    | succ g =>
      unfold popcountAux
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        congr 1
        exact ih g (n / 2) (by omega) (by omega)

theorem popcount_eq_mod_add_div (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => rfl
  | succ m =>
    show (if m + 1 = 0 then 0 else (m + 1) % 2 + popcountAux m ((m + 1) / 2)) =
         (m + 1) % 2 + popcountAux ((m + 1) / 2) ((m + 1) / 2)
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    congr 1
    exact popcountAux_eq_of_le m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)

theorem popcount_add_two_pow {k x : Nat} (hx : x < 2 ^ k) :
    popcount (2 ^ k + x) = 1 + popcount x := by
  induction k generalizing x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0; decide
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, popcount_eq_mod_add_div (2 * 2 ^ k + x), popcount_eq_mod_add_div x]
    have hmod : (2 * 2 ^ k + x) % 2 = x % 2 := by omega
    have hdiv : (2 * 2 ^ k + x) / 2 = 2 ^ k + x / 2 := by omega
    have hx' : x / 2 < 2 ^ k := by omega
    rw [hmod, hdiv, ih hx']
    omega

/-- Structurally recursive bit-position weight `W(n) = ∑_{b ∈ bits(n)} (b + 1)`. -/
def bitWeightAux : Nat → Nat → Nat → Nat
  | 0, _, _     => 0
  | f + 1, b, n => if n = 0 then 0 else (if n % 2 = 1 then b + 1 else 0) + bitWeightAux f (b + 1) (n / 2)

def bitWeightFrom (b n : Nat) : Nat := bitWeightAux n b n

def bitWeight (n : Nat) : Nat := bitWeightFrom 0 n

theorem bitWeightAux_eq_of_le : ∀ f g b n, n ≤ f → n ≤ g →
    bitWeightAux f b n = bitWeightAux g b n := by
  intro f
  induction f with
  | zero =>
    intro g b n hnf _
    have hn0 : n = 0 := by omega
    subst hn0
    cases g <;> simp [bitWeightAux]
  | succ f ih =>
    intro g b n hnf hng
    cases g with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0; simp [bitWeightAux]
    | succ g =>
      unfold bitWeightAux
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        congr 1
        exact ih g (b + 1) (n / 2) (by omega) (by omega)

theorem bitWeightFrom_zero (b : Nat) : bitWeightFrom b 0 = 0 := rfl

theorem bitWeightFrom_unfold (b n : Nat) :
    bitWeightFrom b n = (if n % 2 = 1 then b + 1 else 0) + bitWeightFrom (b + 1) (n / 2) := by
  cases n with
  | zero => rfl
  | succ m =>
    show (if m + 1 = 0 then 0 else (if (m + 1) % 2 = 1 then b + 1 else 0) + bitWeightAux m (b + 1) ((m + 1) / 2)) =
         (if (m + 1) % 2 = 1 then b + 1 else 0) + bitWeightAux ((m + 1) / 2) (b + 1) ((m + 1) / 2)
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    congr 1
    exact bitWeightAux_eq_of_le m ((m + 1) / 2) (b + 1) ((m + 1) / 2) (by omega) (Nat.le_refl _)

theorem bitWeightFrom_add_two_pow {k b x : Nat} (hx : x < 2 ^ k) :
    bitWeightFrom b (2 ^ k + x) = (b + k + 1) + bitWeightFrom b x := by
  induction k generalizing b x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    rw [Nat.pow_zero, Nat.add_zero, bitWeightFrom_unfold, bitWeightFrom_zero, bitWeightFrom_zero]
    simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, bitWeightFrom_unfold b (2 * 2 ^ k + x), bitWeightFrom_unfold b x]
    have hmod : (2 * 2 ^ k + x) % 2 = x % 2 := by omega
    have hdiv : (2 * 2 ^ k + x) / 2 = 2 ^ k + x / 2 := by omega
    have hx' : x / 2 < 2 ^ k := by omega
    rw [hmod, hdiv, ih hx']
    omega

theorem bitWeight_add_two_pow {k x : Nat} (hx : x < 2 ^ k) :
    bitWeight (2 ^ k + x) = (k + 1) + bitWeight x := by
  simpa [bitWeight] using bitWeightFrom_add_two_pow (b := 0) hx

/-- Structurally recursive exact dyadic van der Corput radical inverse `φ_2(n) ∈ Z[1/2]`. -/
def phi2Aux : Nat → Nat → Nat → Dyad
  | 0, _, _     => zero
  | f + 1, b, n =>
    if n = 0 then zero else
      (if n % 2 = 1 then pow2Neg (b + 1) else zero) + phi2Aux f (b + 1) (n / 2)

def phi2From (b n : Nat) : Dyad := phi2Aux n b n

def phi2 (n : Nat) : Dyad := phi2From 0 n

theorem phi2Aux_eq_of_le : ∀ f g b n, n ≤ f → n ≤ g →
    phi2Aux f b n = phi2Aux g b n := by
  intro f
  induction f with
  | zero =>
    intro g b n hnf _
    have hn0 : n = 0 := by omega
    subst hn0
    cases g <;> simp [phi2Aux]
  | succ f ih =>
    intro g b n hnf hng
    cases g with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0; simp [phi2Aux]
    | succ g =>
      unfold phi2Aux
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        congr 1
        exact ih g (b + 1) (n / 2) (by omega) (by omega)

theorem phi2From_zero (b : Nat) : phi2From b 0 = zero := rfl

theorem phi2From_unfold (b n : Nat) :
    phi2From b n ≈ (if n % 2 = 1 then pow2Neg (b + 1) else zero) + phi2From (b + 1) (n / 2) := by
  cases n with
  | zero =>
    show zero ≈ zero + zero
    exact deq_symm (add_zero zero)
  | succ m =>
    show (if m + 1 = 0 then zero else
            (if (m + 1) % 2 = 1 then pow2Neg (b + 1) else zero) + phi2Aux m (b + 1) ((m + 1) / 2)) ≈
         (if (m + 1) % 2 = 1 then pow2Neg (b + 1) else zero) + phi2Aux ((m + 1) / 2) (b + 1) ((m + 1) / 2)
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [phi2Aux_eq_of_le m ((m + 1) / 2) (b + 1) ((m + 1) / 2) (by omega) (Nat.le_refl _)]
    exact deq_refl _

theorem phi2From_add_two_pow {k b x : Nat} (hx : x < 2 ^ k) :
    phi2From b (2 ^ k + x) ≈ phi2From b x + pow2Neg (b + k + 1) := by
  induction k generalizing b x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    have h1 := phi2From_unfold b 1
    have h1' : phi2From b 1 ≈ pow2Neg (b + 1) + zero := by
      simpa [phi2From_zero] using h1
    rw [Nat.pow_zero, Nat.add_zero, phi2From_zero]
    calc
      phi2From b 1 ≈ pow2Neg (b + 1) + zero := h1'
      _ ≈ pow2Neg (b + 1) := add_zero _
      _ ≈ zero + pow2Neg (b + 1) := deq_symm (zero_add _)
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    have hmod : (2 * 2 ^ k + x) % 2 = x % 2 := by omega
    have hdiv : (2 * 2 ^ k + x) / 2 = 2 ^ k + x / 2 := by omega
    have hx' : x / 2 < 2 ^ k := by omega
    have hstep := phi2From_unfold b (2 * 2 ^ k + x)
    rw [hmod, hdiv] at hstep
    have hrec : phi2From (b + 1) (2 ^ k + x / 2) ≈ phi2From (b + 1) (x / 2) + pow2Neg (b + 1 + k + 1) :=
      ih hx'
    have hidx : b + 1 + k + 1 = b + (k + 1) + 1 := by omega
    rw [hidx] at hrec
    let bitTerm := if x % 2 = 1 then pow2Neg (b + 1) else zero
    calc
      phi2From b (2 * 2 ^ k + x)
          ≈ bitTerm + phi2From (b + 1) (2 ^ k + x / 2) := hstep
      _ ≈ bitTerm + (phi2From (b + 1) (x / 2) + pow2Neg (b + (k + 1) + 1)) :=
            add_congr (deq_refl _) hrec
      _ ≈ (bitTerm + phi2From (b + 1) (x / 2)) + pow2Neg (b + (k + 1) + 1) :=
            deq_symm (add_assoc _ _ _)
      _ ≈ phi2From b x + pow2Neg (b + (k + 1) + 1) :=
            add_congr (deq_symm (phi2From_unfold b x)) (deq_refl _)

theorem phi2_add_two_pow {k x : Nat} (hx : x < 2 ^ k) :
    phi2 (2 ^ k + x) ≈ phi2 x + pow2Neg (k + 1) := by
  simpa [phi2] using phi2From_add_two_pow (b := 0) hx

def vdcHammingMat (c β : Dyad) : Mat :=
  fun x y => pow2Neg (popcount (x ^^^ y)) * (c - β * phi2 (x &&& y))

/-- Reusable algebraic identity for affine `c - β * φ_2` Schur complements. -/
theorem affine_schur_combine (f q2 c β ph t : Dyad) (hf : f + q2 ≈ one) :
    ((f * c - β * t) - (f * β) * ph) + q2 * (c - β * ph) ≈ c - β * (ph + t) := by
  have h1 : (f * c - β * t) - (f * β) * ph ≈ f * (c - β * ph) - β * t :=
    calc
      (f * c - β * t) - (f * β) * ph
          ≈ (f * c - (f * β) * ph) - β * t := sub_sub_comm _ _ _
      _ ≈ (f * c - f * (β * ph)) - β * t := sub_congr (sub_congr (deq_refl _) (mul_assoc _ _ _)) (deq_refl _)
      _ ≈ f * (c - β * ph) - β * t := sub_congr (deq_symm (mul_sub _ _ _)) (deq_refl _)
  calc
    ((f * c - β * t) - (f * β) * ph) + q2 * (c - β * ph)
        ≈ (f * (c - β * ph) - β * t) + q2 * (c - β * ph) := add_congr h1 (deq_refl _)
    _ ≈ (f * (c - β * ph) + q2 * (c - β * ph)) - β * t := add_sub_comm _ _ _
    _ ≈ ((f + q2) * (c - β * ph)) - β * t := sub_congr (deq_symm (add_mul _ _ _)) (deq_refl _)
    _ ≈ (one * (c - β * ph)) - β * t := sub_congr (mul_congr hf (deq_refl _)) (deq_refl _)
    _ ≈ (c - β * ph) - β * t := sub_congr (one_mul _) (deq_refl _)
    _ ≈ c - (β * ph + β * t) := sub_sub_eq_sub_add _ _ _
    _ ≈ c - β * (ph + t) := sub_congr (deq_refl _) (deq_symm (mul_add _ _ _))

/-- Parametric Schur state `(c, β)` for the van der Corput-Hamming kernel. -/
def vdcHammingSystem : SchurSystem (Dyad × Dyad) where
  mat := fun σ _ => vdcHammingMat σ.1 σ.2
  leftState := fun σ _ => σ
  rightState := fun σ k =>
    (⟨3, 2⟩ * σ.1 - σ.2 * pow2Neg (k + 1), ⟨3, 2⟩ * σ.2)
  coupling := fun _ _ => scalarMat (pow2Neg 1)
  tl_eq := fun _ _ _ _ _ _ => deq_refl _
  bl_eq := fun σ k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_scalarMat (pow2Neg 1) (vdcHammingMat σ.1 σ.2) hi))
    unfold vdcHammingMat
    rw [xor_add_two_pow_left hi hj, popcount_add_two_pow (xor_lt_two_pow hi hj),
        and_add_two_pow_left hi hj]
    calc
      pow2Neg (1 + popcount (i ^^^ j)) * (σ.1 - σ.2 * phi2 (i &&& j))
          ≈ (pow2Neg 1 * pow2Neg (popcount (i ^^^ j))) * (σ.1 - σ.2 * phi2 (i &&& j)) :=
            mul_congr (deq_symm (pow2Neg_mul 1 _)) (deq_refl _)
      _ ≈ pow2Neg 1 * (pow2Neg (popcount (i ^^^ j)) * (σ.1 - σ.2 * phi2 (i &&& j))) :=
            mul_assoc _ _ _
  tr_eq := fun σ k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_scalarMat (pow2Neg 1) (vdcHammingMat σ.1 σ.2) hj))
    unfold vdcHammingMat
    rw [xor_add_two_pow_right hi hj, popcount_add_two_pow (xor_lt_two_pow hi hj),
        and_add_two_pow_right hi hj, Nat.xor_comm i j, Nat.and_comm i j]
    calc
      pow2Neg (1 + popcount (j ^^^ i)) * (σ.1 - σ.2 * phi2 (j &&& i))
          ≈ (pow2Neg 1 * pow2Neg (popcount (j ^^^ i))) * (σ.1 - σ.2 * phi2 (j &&& i)) :=
            mul_congr (deq_symm (pow2Neg_mul 1 _)) (deq_refl _)
      _ ≈ pow2Neg 1 * (pow2Neg (popcount (j ^^^ i)) * (σ.1 - σ.2 * phi2 (j &&& i))) :=
            mul_assoc _ _ _
  br_eq := fun σ k i j hi hj => by
    have hquad : matMulT (2 ^ k) (matMul (2 ^ k) (scalarMat (pow2Neg 1)) (vdcHammingMat σ.1 σ.2))
                   (scalarMat (pow2Neg 1)) i j ≈
                 pow2Neg 2 * vdcHammingMat σ.1 σ.2 i j := by
      have h1 := matMulT_scalarMat (N := 2 ^ k) (i := i) (pow2Neg 1)
        (matMul (2 ^ k) (scalarMat (pow2Neg 1)) (vdcHammingMat σ.1 σ.2)) hj
      have h2 := mul_congr (matMul_scalarMat (N := 2 ^ k) (j := j) (pow2Neg 1) (vdcHammingMat σ.1 σ.2) hi)
        (deq_refl (pow2Neg 1))
      have h3 : (pow2Neg 1 * vdcHammingMat σ.1 σ.2 i j) * pow2Neg 1 ≈
                (pow2Neg 1 * pow2Neg 1) * vdcHammingMat σ.1 σ.2 i j :=
        deq_trans (mul_assoc _ _ _)
          (deq_trans (mul_congr (deq_refl _) (mul_comm _ _)) (deq_symm (mul_assoc _ _ _)))
      have h4 := mul_congr (pow2Neg_mul 1 1) (deq_refl (vdcHammingMat σ.1 σ.2 i j))
      exact deq_trans h1 (deq_trans h2 (deq_trans h3 h4))
    let p := pow2Neg (popcount (i ^^^ j))
    let ph := phi2 (i &&& j)
    let c' := ⟨3, 2⟩ * σ.1 - σ.2 * pow2Neg (k + 1)
    let β' := ⟨3, 2⟩ * σ.2
    have hcomb := affine_schur_combine ⟨3, 2⟩ (pow2Neg 2) σ.1 σ.2 ph (pow2Neg (k + 1)) (by decide)
    have hphi := phi2_add_two_pow (and_lt_two_pow (y := j) hi)
    have hstep1 : vdcHammingMat σ.1 σ.2 (2 ^ k + i) (2 ^ k + j) ≈
                  p * (σ.1 - σ.2 * (ph + pow2Neg (k + 1))) := by
      unfold vdcHammingMat
      rw [xor_add_two_pow_both hi hj, and_add_two_pow_both hi hj]
      exact mul_congr (deq_refl p) (sub_congr (deq_refl σ.1) (mul_congr (deq_refl σ.2) hphi))
    have hstep2 : p * (σ.1 - σ.2 * (ph + pow2Neg (k + 1))) ≈
                  p * (c' - β' * ph) + pow2Neg 2 * (p * (σ.1 - σ.2 * ph)) := by
      have ha := mul_congr (deq_refl p) (deq_symm hcomb)
      have hb := mul_add p (c' - β' * ph) (pow2Neg 2 * (σ.1 - σ.2 * ph))
      have hc : p * (pow2Neg 2 * (σ.1 - σ.2 * ph)) ≈ pow2Neg 2 * (p * (σ.1 - σ.2 * ph)) :=
        deq_trans (deq_symm (mul_assoc _ _ _))
          (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
      exact deq_trans ha (deq_trans hb (add_congr (deq_refl _) hc))
    exact deq_trans hstep1 (deq_trans hstep2 (add_congr (deq_refl _) (deq_symm hquad)))

/-- Exact closed-form pivot formula for Family I:
    `D(0) = c`, and for `r > 0`, `D(r) = (3/4)^(pop(r) - 1) * (3/4 * c - β * φ_2(r))`. -/
def vdcHammingPivot (c β : Dyad) (r : Nat) : Dyad :=
  if r = 0 then c
  else Dyad.pow ⟨3, 2⟩ (popcount r - 1) * (⟨3, 2⟩ * c - β * phi2 r)

def weightedVdcMat (c β : Dyad) : Mat :=
  fun x y => pow2Neg (bitWeight (x ^^^ y)) * (c - β * phi2 (x &&& y))

/-- Schur factor `f_k = 1 - 4^{-(k+1)}`. -/
def schurFactorW (k : Nat) : Dyad :=
  one - pow2Neg (2 * (k + 1))

def weightedVdcSystem : SchurSystem (Dyad × Dyad) where
  mat := fun σ _ => weightedVdcMat σ.1 σ.2
  leftState := fun σ _ => σ
  rightState := fun σ k =>
    (schurFactorW k * σ.1 - σ.2 * pow2Neg (k + 1), schurFactorW k * σ.2)
  coupling := fun _ k => scalarMat (pow2Neg (k + 1))
  tl_eq := fun _ _ _ _ _ _ => deq_refl _
  bl_eq := fun σ k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_scalarMat (pow2Neg (k + 1)) (weightedVdcMat σ.1 σ.2) hi))
    unfold weightedVdcMat
    rw [xor_add_two_pow_left hi hj, bitWeight_add_two_pow (xor_lt_two_pow hi hj),
        and_add_two_pow_left hi hj]
    calc
      pow2Neg ((k + 1) + bitWeight (i ^^^ j)) * (σ.1 - σ.2 * phi2 (i &&& j))
          ≈ (pow2Neg (k + 1) * pow2Neg (bitWeight (i ^^^ j))) * (σ.1 - σ.2 * phi2 (i &&& j)) :=
            mul_congr (deq_symm (pow2Neg_mul (k + 1) _)) (deq_refl _)
      _ ≈ pow2Neg (k + 1) * (pow2Neg (bitWeight (i ^^^ j)) * (σ.1 - σ.2 * phi2 (i &&& j))) :=
            mul_assoc _ _ _
  tr_eq := fun σ k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_scalarMat (pow2Neg (k + 1)) (weightedVdcMat σ.1 σ.2) hj))
    unfold weightedVdcMat
    rw [xor_add_two_pow_right hi hj, bitWeight_add_two_pow (xor_lt_two_pow hi hj),
        and_add_two_pow_right hi hj, Nat.xor_comm i j, Nat.and_comm i j]
    calc
      pow2Neg ((k + 1) + bitWeight (j ^^^ i)) * (σ.1 - σ.2 * phi2 (j &&& i))
          ≈ (pow2Neg (k + 1) * pow2Neg (bitWeight (j ^^^ i))) * (σ.1 - σ.2 * phi2 (j &&& i)) :=
            mul_congr (deq_symm (pow2Neg_mul (k + 1) _)) (deq_refl _)
      _ ≈ pow2Neg (k + 1) * (pow2Neg (bitWeight (j ^^^ i)) * (σ.1 - σ.2 * phi2 (j &&& i))) :=
            mul_assoc _ _ _
  br_eq := fun σ k i j hi hj => by
    have h2k : (k + 1) + (k + 1) = 2 * (k + 1) := by omega
    have hquad : matMulT (2 ^ k) (matMul (2 ^ k) (scalarMat (pow2Neg (k + 1))) (weightedVdcMat σ.1 σ.2))
                   (scalarMat (pow2Neg (k + 1))) i j ≈
                 pow2Neg (2 * (k + 1)) * weightedVdcMat σ.1 σ.2 i j := by
      have h1 := matMulT_scalarMat (N := 2 ^ k) (i := i) (pow2Neg (k + 1))
        (matMul (2 ^ k) (scalarMat (pow2Neg (k + 1))) (weightedVdcMat σ.1 σ.2)) hj
      have h2 := mul_congr (matMul_scalarMat (N := 2 ^ k) (j := j) (pow2Neg (k + 1)) (weightedVdcMat σ.1 σ.2) hi)
        (deq_refl (pow2Neg (k + 1)))
      have h3 : (pow2Neg (k + 1) * weightedVdcMat σ.1 σ.2 i j) * pow2Neg (k + 1) ≈
                (pow2Neg (k + 1) * pow2Neg (k + 1)) * weightedVdcMat σ.1 σ.2 i j :=
        deq_trans (mul_assoc _ _ _)
          (deq_trans (mul_congr (deq_refl _) (mul_comm _ _)) (deq_symm (mul_assoc _ _ _)))
      have h4 : (pow2Neg (k + 1) * pow2Neg (k + 1)) * weightedVdcMat σ.1 σ.2 i j ≈
                pow2Neg (2 * (k + 1)) * weightedVdcMat σ.1 σ.2 i j := by
        rw [← h2k]; exact mul_congr (pow2Neg_mul (k + 1) (k + 1)) (deq_refl _)
      exact deq_trans h1 (deq_trans h2 (deq_trans h3 h4))
    let p := pow2Neg (bitWeight (i ^^^ j))
    let ph := phi2 (i &&& j)
    let fk := schurFactorW k
    let c' := fk * σ.1 - σ.2 * pow2Neg (k + 1)
    let β' := fk * σ.2
    have hfk_add : fk + pow2Neg (2 * (k + 1)) ≈ one := sub_add_cancel one (pow2Neg (2 * (k + 1)))
    have hcomb := affine_schur_combine fk (pow2Neg (2 * (k + 1))) σ.1 σ.2 ph (pow2Neg (k + 1)) hfk_add
    have hphi := phi2_add_two_pow (and_lt_two_pow (y := j) hi)
    have hstep1 : weightedVdcMat σ.1 σ.2 (2 ^ k + i) (2 ^ k + j) ≈
                  p * (σ.1 - σ.2 * (ph + pow2Neg (k + 1))) := by
      unfold weightedVdcMat
      rw [xor_add_two_pow_both hi hj, and_add_two_pow_both hi hj]
      exact mul_congr (deq_refl p) (sub_congr (deq_refl σ.1) (mul_congr (deq_refl σ.2) hphi))
    have hstep2 : p * (σ.1 - σ.2 * (ph + pow2Neg (k + 1))) ≈
                  p * (c' - β' * ph) + pow2Neg (2 * (k + 1)) * (p * (σ.1 - σ.2 * ph)) := by
      have ha := mul_congr (deq_refl p) (deq_symm hcomb)
      have hb := mul_add p (c' - β' * ph) (pow2Neg (2 * (k + 1)) * (σ.1 - σ.2 * ph))
      have hc : p * (pow2Neg (2 * (k + 1)) * (σ.1 - σ.2 * ph)) ≈
                pow2Neg (2 * (k + 1)) * (p * (σ.1 - σ.2 * ph)) :=
        deq_trans (deq_symm (mul_assoc _ _ _))
          (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
      exact deq_trans ha (deq_trans hb (add_congr (deq_refl _) hc))
    exact deq_trans hstep1 (deq_trans hstep2 (add_congr (deq_refl _) (deq_symm hquad)))

/-- Pure dyadic upper-bound envelope `V(k)` for `∑_{b=0}^{k-1} 2^{-(b+1)} / (1 - 4^{-(b+1)})`:
    `V(0) = 0`, `V(k) = 79/64 - (9/8) * 2^{-k}` for `k ≥ 1`. -/
def envV : Nat → Dyad
  | 0     => zero
  | k + 1 => ⟨79, 6⟩ - ⟨9, 3⟩ * pow2Neg (k + 1)

/-- Pure dyadic product lower-bound `prodW k = ∏_{j=0}^{k-1} (1 - 4^{-(j+1)})`. -/
def prodW : Nat → Dyad
  | 0     => one
  | k + 1 => schurFactorW k * prodW k

def gray (n : Nat) : Nat := n ^^^ (n >>> 1)

theorem testBit_two_pow_sub_one_sub {k x j : Nat} (hx : x < 2 ^ k) :
    (2 ^ k - 1 - x).testBit j = (decide (j < k) && !(x.testBit j)) := by
  induction k generalizing x j with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0; simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    have hsplit : 2 ^ (k + 1) - 1 - x = 2 * (2 ^ k - 1 - x / 2) + (1 - x % 2) := by
      rw [hpow] at hx ⊢; omega
    cases j with
    | zero =>
      simp only [Nat.testBit_zero, Nat.zero_lt_succ, decide_true, Bool.true_and]
      rw [hsplit]
      have hmod : (2 * (2 ^ k - 1 - x / 2) + (1 - x % 2)) % 2 = 1 - x % 2 := by omega
      rw [hmod]
      by_cases hxm : x % 2 = 1
      · simp [hxm]
      · have hxm0 : x % 2 = 0 := by omega
        simp [hxm0]
    | succ m =>
      have hdiv : (2 ^ (k + 1) - 1 - x) / 2 = 2 ^ k - 1 - x / 2 := by rw [hsplit]; omega
      have hx' : x / 2 < 2 ^ k := by rw [hpow] at hx; omega
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv, ih hx']
      by_cases hmk : m < k
      · have hmk' : m + 1 < k + 1 := by omega
        simp [hmk, hmk']
      · have hmk' : ¬ (m + 1 < k + 1) := by omega
        simp [hmk, hmk']

theorem gray_lt_two_pow {k x : Nat} (hx : x < 2 ^ k) : gray x < 2 ^ k := by
  unfold gray
  have hsr : x >>> 1 < 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  exact Nat.xor_lt_two_pow hx hsr

theorem testBit_gray (n j : Nat) : (gray n).testBit j = xor (n.testBit j) (n.testBit (j + 1)) := by
  unfold gray
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_comm 1 j]

theorem gray_add_two_pow {k x : Nat} (hx : x < 2 ^ k) :
    gray (2 ^ k + x) = 2 ^ k + gray (2 ^ k - 1 - x) := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have hcomp_lt : 2 ^ k - 1 - x < 2 ^ k := by omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_gray, testBit_two_pow_add hx, testBit_two_pow_add hx,
      testBit_two_pow_add (gray_lt_two_pow hcomp_lt), testBit_gray,
      testBit_two_pow_sub_one_sub hx, testBit_two_pow_sub_one_sub hx]
  by_cases hjk : j = k
  · subst hjk
    have hxj1 : x.testBit (j + 1) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_trans hx (Nat.pow_lt_pow_right (by omega) (by omega)))
    simp [hxj1]
  · by_cases hlt : j < k
    · by_cases htop : j + 1 = k
      · simp [hjk, hlt, htop]
      · have hlt1 : j + 1 < k := by omega
        simp only [hjk, ↓reduceIte, hlt, decide_true, Bool.true_and, htop, hlt1]
        cases x.testBit j <;> cases x.testBit (j + 1) <;> rfl
    · have hnot1 : ¬ (j + 1 < k) := by omega
      have hne1 : j + 1 ≠ k := by omega
      have hxj : x.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      have hxj1 : x.testBit (j + 1) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hjk, hlt, hnot1, hne1, hxj, hxj1]

/-- Exact bit-reflection centrosymmetry of Gray-code XOR differences on `[0, 2^k)`. -/
theorem gray_reflect_xor {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    gray (2 ^ k - 1 - x) ^^^ gray (2 ^ k - 1 - y) = gray x ^^^ gray y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_gray, testBit_gray, testBit_gray, testBit_gray,
      testBit_two_pow_sub_one_sub hx, testBit_two_pow_sub_one_sub hx,
      testBit_two_pow_sub_one_sub hy, testBit_two_pow_sub_one_sub hy]
  by_cases hlt : j < k
  · by_cases hlt1 : j + 1 < k
    · simp only [hlt, hlt1, decide_true, Bool.true_and]
      cases x.testBit j <;> cases x.testBit (j + 1) <;> cases y.testBit j <;> cases y.testBit (j + 1) <;> rfl
    · have hxj1 : x.testBit (j + 1) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      have hyj1 : y.testBit (j + 1) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))
      simp only [hlt, hlt1, decide_true, decide_false, Bool.true_and, Bool.false_and, hxj1, hyj1]
      cases x.testBit j <;> cases y.testBit j <;> rfl
  · have hnot1 : ¬ (j + 1 < k) := by omega
    have hxj : x.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    have hxj1 : x.testBit (j + 1) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    have hyj : y.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))
    have hyj1 : y.testBit (j + 1) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hlt, hnot1, hxj, hxj1, hyj, hyj1]

def grayWeightedMat : Mat :=
  fun x y => pow2Neg (bitWeight (gray x ^^^ gray y))

def plainWeightedMat : Mat :=
  fun x y => pow2Neg (bitWeight (x ^^^ y))

/-- Antidiagonal reflection `SchurSystem` for `s * K^{Gray, W}`. -/
def grayWeightedSystem : SchurSystem Dyad where
  mat := fun s _ x y => s * grayWeightedMat x y
  leftState := fun s _ => s
  rightState := fun s k => schurFactorW k * s
  coupling := fun _ k => reflectMat (2 ^ k) (pow2Neg (k + 1))
  tl_eq := fun _ _ _ _ _ _ => deq_refl _
  bl_eq := fun s k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_reflectMat (N := 2 ^ k) (pow2Neg (k + 1))
      (fun x y => s * grayWeightedMat x y) hi))
    have hcomp : 2 ^ k - 1 - i < 2 ^ k := by
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); omega
    unfold grayWeightedMat
    rw [gray_add_two_pow hi, xor_add_two_pow_left (gray_lt_two_pow hcomp) (gray_lt_two_pow hj),
        bitWeight_add_two_pow (xor_lt_two_pow (gray_lt_two_pow hcomp) (gray_lt_two_pow hj))]
    have h1 := mul_congr (deq_refl s) (deq_symm (pow2Neg_mul (k + 1) (bitWeight (gray (2 ^ k - 1 - i) ^^^ gray j))))
    have h2 : s * (pow2Neg (k + 1) * pow2Neg (bitWeight (gray (2 ^ k - 1 - i) ^^^ gray j))) ≈
              pow2Neg (k + 1) * (s * pow2Neg (bitWeight (gray (2 ^ k - 1 - i) ^^^ gray j))) :=
      deq_trans (deq_symm (mul_assoc _ _ _))
        (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
    exact deq_trans h1 h2
  tr_eq := fun s k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_reflectMat (N := 2 ^ k) (pow2Neg (k + 1))
      (fun x y => s * grayWeightedMat x y) hj))
    have hcomp : 2 ^ k - 1 - j < 2 ^ k := by
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); omega
    unfold grayWeightedMat
    rw [gray_add_two_pow hj, xor_add_two_pow_right (gray_lt_two_pow hi) (gray_lt_two_pow hcomp),
        bitWeight_add_two_pow (xor_lt_two_pow (gray_lt_two_pow hi) (gray_lt_two_pow hcomp)),
        Nat.xor_comm (gray i) (gray (2 ^ k - 1 - j))]
    have h1 := mul_congr (deq_refl s) (deq_symm (pow2Neg_mul (k + 1) (bitWeight (gray (2 ^ k - 1 - j) ^^^ gray i))))
    have h2 : s * (pow2Neg (k + 1) * pow2Neg (bitWeight (gray (2 ^ k - 1 - j) ^^^ gray i))) ≈
              pow2Neg (k + 1) * (s * pow2Neg (bitWeight (gray (2 ^ k - 1 - j) ^^^ gray i))) :=
      deq_trans (deq_symm (mul_assoc _ _ _))
        (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
    exact deq_trans h1 h2
  br_eq := fun s k i j hi hj => by
    have h2k : (k + 1) + (k + 1) = 2 * (k + 1) := by omega
    have hquad : matMulT (2 ^ k) (matMul (2 ^ k) (reflectMat (2 ^ k) (pow2Neg (k + 1)))
                   (fun x y => s * grayWeightedMat x y))
                   (reflectMat (2 ^ k) (pow2Neg (k + 1))) i j ≈
                 pow2Neg (2 * (k + 1)) * (s * grayWeightedMat i j) := by
      have h1 := matMulT_reflectMat (N := 2 ^ k) (i := i) (pow2Neg (k + 1))
        (matMul (2 ^ k) (reflectMat (2 ^ k) (pow2Neg (k + 1))) (fun x y => s * grayWeightedMat x y)) hj
      have h2 := mul_congr (matMul_reflectMat (N := 2 ^ k) (j := 2 ^ k - 1 - j) (pow2Neg (k + 1))
        (fun x y => s * grayWeightedMat x y) hi) (deq_refl (pow2Neg (k + 1)))
      have hsym : grayWeightedMat (2 ^ k - 1 - i) (2 ^ k - 1 - j) = grayWeightedMat i j := by
        unfold grayWeightedMat; rw [gray_reflect_xor hi hj]
      have h3 : (pow2Neg (k + 1) * (s * grayWeightedMat (2 ^ k - 1 - i) (2 ^ k - 1 - j))) * pow2Neg (k + 1) ≈
                pow2Neg (2 * (k + 1)) * (s * grayWeightedMat i j) := by
        rw [hsym]
        have ha : (pow2Neg (k + 1) * (s * grayWeightedMat i j)) * pow2Neg (k + 1) ≈
                  (pow2Neg (k + 1) * pow2Neg (k + 1)) * (s * grayWeightedMat i j) :=
          deq_trans (mul_assoc _ _ _)
            (deq_trans (mul_congr (deq_refl _) (mul_comm _ _)) (deq_symm (mul_assoc _ _ _)))
        have hb : (pow2Neg (k + 1) * pow2Neg (k + 1)) * (s * grayWeightedMat i j) ≈
                  pow2Neg (2 * (k + 1)) * (s * grayWeightedMat i j) := by
          rw [← h2k]; exact mul_congr (pow2Neg_mul (k + 1) (k + 1)) (deq_refl _)
        exact deq_trans ha hb
      exact deq_trans h1 (deq_trans h2 h3)
    have hcomp_i : 2 ^ k - 1 - i < 2 ^ k := by
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); omega
    have hcomp_j : 2 ^ k - 1 - j < 2 ^ k := by
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); omega
    have hbr_eq : grayWeightedMat (2 ^ k + i) (2 ^ k + j) = grayWeightedMat i j := by
      unfold grayWeightedMat
      rw [gray_add_two_pow hi, gray_add_two_pow hj,
          xor_add_two_pow_both (gray_lt_two_pow hcomp_i) (gray_lt_two_pow hcomp_j),
          gray_reflect_xor hi hj]
    rw [hbr_eq]
    let A := s * grayWeightedMat i j
    have hsum1 : schurFactorW k * A + pow2Neg (2 * (k + 1)) * A ≈ A :=
      deq_trans (deq_symm (add_mul (schurFactorW k) (pow2Neg (2 * (k + 1))) A))
        (deq_trans (mul_congr (sub_add_cancel one (pow2Neg (2 * (k + 1)))) (deq_refl A)) (one_mul A))
    have hassoc : (schurFactorW k * s) * grayWeightedMat i j ≈ schurFactorW k * A :=
      mul_assoc (schurFactorW k) s (grayWeightedMat i j)
    exact deq_trans (deq_symm hsum1) (add_congr (deq_symm hassoc) (deq_symm hquad))

/-- Plain scalar-coupled `SchurSystem` for `s * K^{plain, W}` (for pivot-equality comparison). -/
def plainWeightedSystem : SchurSystem Dyad where
  mat := fun s _ x y => s * plainWeightedMat x y
  leftState := fun s _ => s
  rightState := fun s k => schurFactorW k * s
  coupling := fun _ k => scalarMat (pow2Neg (k + 1))
  tl_eq := fun _ _ _ _ _ _ => deq_refl _
  bl_eq := fun s k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_scalarMat (N := 2 ^ k) (pow2Neg (k + 1))
      (fun x y => s * plainWeightedMat x y) hi))
    unfold plainWeightedMat
    rw [xor_add_two_pow_left hi hj, bitWeight_add_two_pow (xor_lt_two_pow hi hj)]
    have h1 := mul_congr (deq_refl s) (deq_symm (pow2Neg_mul (k + 1) (bitWeight (i ^^^ j))))
    have h2 : s * (pow2Neg (k + 1) * pow2Neg (bitWeight (i ^^^ j))) ≈
              pow2Neg (k + 1) * (s * pow2Neg (bitWeight (i ^^^ j))) :=
      deq_trans (deq_symm (mul_assoc _ _ _))
        (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
    exact deq_trans h1 h2
  tr_eq := fun s k i j hi hj => by
    refine deq_trans ?_ (deq_symm (matMul_scalarMat (N := 2 ^ k) (pow2Neg (k + 1))
      (fun x y => s * plainWeightedMat x y) hj))
    unfold plainWeightedMat
    rw [xor_add_two_pow_right hi hj, bitWeight_add_two_pow (xor_lt_two_pow hi hj), Nat.xor_comm i j]
    have h1 := mul_congr (deq_refl s) (deq_symm (pow2Neg_mul (k + 1) (bitWeight (j ^^^ i))))
    have h2 : s * (pow2Neg (k + 1) * pow2Neg (bitWeight (j ^^^ i))) ≈
              pow2Neg (k + 1) * (s * pow2Neg (bitWeight (j ^^^ i))) :=
      deq_trans (deq_symm (mul_assoc _ _ _))
        (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
    exact deq_trans h1 h2
  br_eq := fun s k i j hi hj => by
    have h2k : (k + 1) + (k + 1) = 2 * (k + 1) := by omega
    have hquad : matMulT (2 ^ k) (matMul (2 ^ k) (scalarMat (pow2Neg (k + 1)))
                   (fun x y => s * plainWeightedMat x y))
                   (scalarMat (pow2Neg (k + 1))) i j ≈
                 pow2Neg (2 * (k + 1)) * (s * plainWeightedMat i j) := by
      have h1 := matMulT_scalarMat (N := 2 ^ k) (i := i) (pow2Neg (k + 1))
        (matMul (2 ^ k) (scalarMat (pow2Neg (k + 1))) (fun x y => s * plainWeightedMat x y)) hj
      have h2 := mul_congr (matMul_scalarMat (N := 2 ^ k) (j := j) (pow2Neg (k + 1))
        (fun x y => s * plainWeightedMat x y) hi) (deq_refl (pow2Neg (k + 1)))
      have ha : (pow2Neg (k + 1) * (s * plainWeightedMat i j)) * pow2Neg (k + 1) ≈
                (pow2Neg (k + 1) * pow2Neg (k + 1)) * (s * plainWeightedMat i j) :=
        deq_trans (mul_assoc _ _ _)
          (deq_trans (mul_congr (deq_refl _) (mul_comm _ _)) (deq_symm (mul_assoc _ _ _)))
      have hb : (pow2Neg (k + 1) * pow2Neg (k + 1)) * (s * plainWeightedMat i j) ≈
                pow2Neg (2 * (k + 1)) * (s * plainWeightedMat i j) := by
        rw [← h2k]; exact mul_congr (pow2Neg_mul (k + 1) (k + 1)) (deq_refl _)
      exact deq_trans h1 (deq_trans h2 (deq_trans ha hb))
    have hbr : plainWeightedMat (2 ^ k + i) (2 ^ k + j) = plainWeightedMat i j := by
      unfold plainWeightedMat; rw [xor_add_two_pow_both hi hj]
    rw [hbr]
    let A := s * plainWeightedMat i j
    have hsum1 : schurFactorW k * A + pow2Neg (2 * (k + 1)) * A ≈ A :=
      deq_trans (deq_symm (add_mul (schurFactorW k) (pow2Neg (2 * (k + 1))) A))
        (deq_trans (mul_congr (sub_add_cancel one (pow2Neg (2 * (k + 1)))) (deq_refl A)) (one_mul A))
    have hassoc : (schurFactorW k * s) * plainWeightedMat i j ≈ schurFactorW k * A :=
      mul_assoc (schurFactorW k) s (plainWeightedMat i j)
    exact deq_trans (deq_symm hsum1) (add_congr (deq_symm hassoc) (deq_symm hquad))

def absDiff (x y : Nat) : Nat := if x ≤ y then y - x else x - y

def expVdcMat (c β : Dyad) : Mat :=
  fun x y => pow2Neg (absDiff x y) * (c - β * phi2 (Nat.min x y))

/-- 2-parameter Schur state for the rank-1 boundary-coupled exponential kernel. -/
structure ExpState where
  c      : Dyad
  β      : Dyad
  offset : Nat
  prev   : Dyad

def expStateMat (σ : ExpState) : Mat :=
  fun x y =>
    pow2Neg (absDiff x y) * (σ.c - σ.β * phi2 (σ.offset + Nat.min x y)) -
    σ.prev * pow2Neg (x + y + 2)

/-- Rank-1 boundary-carry `SchurSystem` for `K^{exp}_{c,β}`. -/
def expVdcSystem : SchurSystem ExpState where
  mat := fun σ _ => expStateMat σ
  leftState := fun σ _ => σ
  rightState := fun σ k =>
    ⟨σ.c, σ.β, σ.offset + 2 ^ k, σ.c - σ.β * phi2 (σ.offset + (2 ^ k - 1))⟩
  coupling := fun _ k => boundaryMat (2 ^ k) (fun x => pow2Neg (x + 1))
  tl_eq := fun _ _ _ _ _ _ => deq_refl _
  bl_eq := fun σ k i j hi hj => by
    have hpos : 0 < 2 ^ k := Nat.one_le_pow k 2 (by omega)
    refine deq_trans ?_ (deq_symm (matMul_boundaryMat hpos (fun x => pow2Neg (x + 1)) (expStateMat σ) i j))
    unfold expStateMat
    have habs1 : absDiff (2 ^ k + i) j = (i + 1) + absDiff (2 ^ k - 1) j := by
      unfold absDiff; split <;> split <;> omega
    have hmin1 : Nat.min (2 ^ k + i) j = j := Nat.min_eq_right (by omega)
    have hmin2 : Nat.min (2 ^ k - 1) j = j := Nat.min_eq_right (by omega)
    have hsum1 : (2 ^ k + i) + j + 2 = (i + 1) + ((2 ^ k - 1) + j + 2) := by omega
    rw [habs1, hmin1, hmin2, hsum1]
    let t := σ.c - σ.β * phi2 (σ.offset + j)
    have ha : pow2Neg ((i + 1) + absDiff (2 ^ k - 1) j) * t ≈
              pow2Neg (i + 1) * (pow2Neg (absDiff (2 ^ k - 1) j) * t) :=
      deq_trans (mul_congr (deq_symm (pow2Neg_mul (i + 1) _)) (deq_refl t)) (mul_assoc _ _ _)
    have hb : σ.prev * pow2Neg ((i + 1) + ((2 ^ k - 1) + j + 2)) ≈
              pow2Neg (i + 1) * (σ.prev * pow2Neg ((2 ^ k - 1) + j + 2)) :=
      deq_trans (mul_congr (deq_refl σ.prev) (deq_symm (pow2Neg_mul (i + 1) _)))
        (deq_trans (deq_symm (mul_assoc _ _ _))
          (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _)))
    exact deq_trans (sub_congr ha hb) (deq_symm (mul_sub _ _ _))
  tr_eq := fun σ k i j hi hj => by
    have hpos : 0 < 2 ^ k := Nat.one_le_pow k 2 (by omega)
    refine deq_trans ?_ (deq_symm (matMul_boundaryMat hpos (fun x => pow2Neg (x + 1)) (expStateMat σ) j i))
    unfold expStateMat
    have habs1 : absDiff i (2 ^ k + j) = (j + 1) + absDiff (2 ^ k - 1) i := by
      unfold absDiff; split <;> split <;> omega
    have hmin1 : Nat.min i (2 ^ k + j) = i := Nat.min_eq_left (by omega)
    have hmin2 : Nat.min (2 ^ k - 1) i = i := Nat.min_eq_right (by omega)
    have hsum1 : i + (2 ^ k + j) + 2 = (j + 1) + ((2 ^ k - 1) + i + 2) := by omega
    rw [habs1, hmin1, hmin2, hsum1]
    let t := σ.c - σ.β * phi2 (σ.offset + i)
    have ha : pow2Neg ((j + 1) + absDiff (2 ^ k - 1) i) * t ≈
              pow2Neg (j + 1) * (pow2Neg (absDiff (2 ^ k - 1) i) * t) :=
      deq_trans (mul_congr (deq_symm (pow2Neg_mul (j + 1) _)) (deq_refl t)) (mul_assoc _ _ _)
    have hb : σ.prev * pow2Neg ((j + 1) + ((2 ^ k - 1) + i + 2)) ≈
              pow2Neg (j + 1) * (σ.prev * pow2Neg ((2 ^ k - 1) + i + 2)) :=
      deq_trans (mul_congr (deq_refl σ.prev) (deq_symm (pow2Neg_mul (j + 1) _)))
        (deq_trans (deq_symm (mul_assoc _ _ _))
          (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _)))
    exact deq_trans (sub_congr ha hb) (deq_symm (mul_sub _ _ _))
  br_eq := fun σ k i j hi hj => by
    have hpos : 0 < 2 ^ k := Nat.one_le_pow k 2 (by omega)
    let v : Vec := fun x => pow2Neg (x + 1)
    let pNew := σ.c - σ.β * phi2 (σ.offset + (2 ^ k - 1))
    -- Evaluate E * A * E^T at (i, j) = v(i) * A(2^k-1, 2^k-1) * v(j)
    have hquad : matMulT (2 ^ k) (matMul (2 ^ k) (boundaryMat (2 ^ k) v) (expStateMat σ))
                   (boundaryMat (2 ^ k) v) i j ≈
                 pNew * pow2Neg (i + j + 2) - σ.prev * pow2Neg ((2 ^ k + i) + (2 ^ k + j) + 2) := by
      have h1 := matMulT_boundaryMat hpos v (matMul (2 ^ k) (boundaryMat (2 ^ k) v) (expStateMat σ)) i j
      have h2 := mul_congr (matMul_boundaryMat hpos v (expStateMat σ) i (2 ^ k - 1)) (deq_refl (v j))
      have hA_diag : expStateMat σ (2 ^ k - 1) (2 ^ k - 1) ≈
                     pNew - σ.prev * pow2Neg ((2 ^ k - 1) + (2 ^ k - 1) + 2) := by
        unfold expStateMat
        have ha0 : absDiff (2 ^ k - 1) (2 ^ k - 1) = 0 := by unfold absDiff; simp
        have hm0 : Nat.min (2 ^ k - 1) (2 ^ k - 1) = 2 ^ k - 1 := Nat.min_self _
        rw [ha0, hm0]
        exact sub_congr (deq_trans (mul_congr pow2Neg_zero (deq_refl pNew)) (one_mul pNew)) (deq_refl _)
      have hv_mul : v i * v j ≈ pow2Neg (i + j + 2) := by
        have hidx : (i + 1) + (j + 1) = i + j + 2 := by omega
        rw [← hidx]; exact pow2Neg_mul (i + 1) (j + 1)
      have hre : (v i * expStateMat σ (2 ^ k - 1) (2 ^ k - 1)) * v j ≈
                 expStateMat σ (2 ^ k - 1) (2 ^ k - 1) * pow2Neg (i + j + 2) :=
        calc
          (v i * expStateMat σ (2 ^ k - 1) (2 ^ k - 1)) * v j
              ≈ (expStateMat σ (2 ^ k - 1) (2 ^ k - 1) * v i) * v j := mul_congr (mul_comm _ _) (deq_refl _)
          _ ≈ expStateMat σ (2 ^ k - 1) (2 ^ k - 1) * (v i * v j) := mul_assoc _ _ _
          _ ≈ expStateMat σ (2 ^ k - 1) (2 ^ k - 1) * pow2Neg (i + j + 2) := mul_congr (deq_refl _) hv_mul
      have hdist : (pNew - σ.prev * pow2Neg ((2 ^ k - 1) + (2 ^ k - 1) + 2)) * pow2Neg (i + j + 2) ≈
                   pNew * pow2Neg (i + j + 2) - σ.prev * pow2Neg ((2 ^ k + i) + (2 ^ k + j) + 2) := by
        have hexp : ((2 ^ k - 1) + (2 ^ k - 1) + 2) + (i + j + 2) = (2 ^ k + i) + (2 ^ k + j) + 2 := by omega
        have hs1 := sub_mul pNew (σ.prev * pow2Neg ((2 ^ k - 1) + (2 ^ k - 1) + 2)) (pow2Neg (i + j + 2))
        have hs2 : (σ.prev * pow2Neg ((2 ^ k - 1) + (2 ^ k - 1) + 2)) * pow2Neg (i + j + 2) ≈
                   σ.prev * pow2Neg ((2 ^ k + i) + (2 ^ k + j) + 2) := by
          rw [← hexp]
          exact deq_trans (mul_assoc _ _ _) (mul_congr (deq_refl σ.prev) (pow2Neg_mul _ _))
        exact deq_trans hs1 (sub_congr (deq_refl _) hs2)
      exact deq_trans h1 (deq_trans h2 (deq_trans hre
        (deq_trans (mul_congr hA_diag (deq_refl _)) hdist)))
    -- Now cancel pNew * pow2Neg (i + j + 2) between S and E*A*E^T!
    unfold expStateMat
    have habs : absDiff (2 ^ k + i) (2 ^ k + j) = absDiff i j := by
      unfold absDiff; split <;> split <;> omega
    have hmin : σ.offset + Nat.min (2 ^ k + i) (2 ^ k + j) = (σ.offset + 2 ^ k) + Nat.min i j := by
      have hm : Nat.min (2 ^ k + i) (2 ^ k + j) = 2 ^ k + Nat.min i j := by
        simp only [Nat.min_def]
        by_cases hij : i ≤ j
        · have hij' : 2 ^ k + i ≤ 2 ^ k + j := by omega
          simp [hij, hij']
        · have hij' : ¬ (2 ^ k + i ≤ 2 ^ k + j) := by omega
          simp [hij, hij']
      rw [hm]; omega
    rw [habs, hmin]
    let mainTerm := pow2Neg (absDiff i j) * (σ.c - σ.β * phi2 ((σ.offset + 2 ^ k) + Nat.min i j))
    let cancelTerm := pNew * pow2Neg (i + j + 2)
    let tailTerm := σ.prev * pow2Neg ((2 ^ k + i) + (2 ^ k + j) + 2)
    have hcancel : (mainTerm - cancelTerm) + (cancelTerm - tailTerm) ≈ mainTerm - tailTerm := by
      have h1 := deq_symm (add_assoc (mainTerm - cancelTerm) cancelTerm (-tailTerm))
      have h2 := add_congr (sub_add_cancel mainTerm cancelTerm) (deq_refl (-tailTerm))
      exact deq_trans h1 h2
    exact deq_trans (deq_symm hcancel) (add_congr (deq_refl _) (deq_symm hquad))

/-- Exact closed-form pivot formula for Family IV:
    `D(0) = c`, and `D(r + 1) = (c - β * φ_2(r + 1)) - 1/4 * (c - β * φ_2(r))`. -/
def expVdcPivot (c β : Dyad) : Nat → Dyad
  | 0     => c
  | r + 1 => (c - β * phi2 (r + 1)) - pow2Neg 2 * (c - β * phi2 r)

/-- Sharpness counterexample for Family IV: `c = 9/8, β = 1` (just `1/24` below `7/6`)
    FAILS strict PD at `n = 32` via an explicit 2-sparse integer vector `w = 2*e_31 - e_30`
    giving `w^T M_32 w = -1/32 < 0` (even though `M_31` IS strictly PD)! -/
def sparseNegVec : Vec :=
  fun i => if i = 31 then ofInt 2 else if i = 30 then ofInt (-1) else zero

end DyadicLDLT
