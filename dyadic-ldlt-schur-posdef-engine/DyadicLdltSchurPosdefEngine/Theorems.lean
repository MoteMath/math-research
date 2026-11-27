/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DyadicLdltSchurPosdefEngine.Defs

/-!
# Theorems (`dyadic-ldlt-schur-posdef-engine`)

Full proofs of the headline infinite theorems of Exact Dyadic LDL-Transpose Positive-Definiteness Infinite Certificate Engine.
-/

namespace DyadicLDLT

namespace Dyad

theorem pow_congr {a b : Dyad} (h : a ≈ b) (n : Nat) : a.pow n ≈ b.pow n := by
  induction n with
  | zero => exact deq_refl _
  | succ k ih => exact mul_congr h ih

-- Ring laws up to ≈

theorem sub_self (a : Dyad) : a - a ≈ zero := add_neg a

theorem neg_neg (a : Dyad) : -(-a) ≈ a := by
  show (-(-a.mant)) * (2 ^ a.shift : Int) = a.mant * (2 ^ a.shift : Int)
  rw [Int.neg_neg]

theorem neg_zero : -zero ≈ zero := by decide

theorem sub_eq_add_neg (a b : Dyad) : a - b = a + (-b) := rfl

theorem add_sub_cancel (a b : Dyad) : (a + b) - b ≈ a := by
  calc
    (a + b) - b = (a + b) + (-b) := rfl
    _ ≈ a + (b + (-b)) := add_assoc a b (-b)
    _ ≈ a + zero := add_congr (deq_refl a) (add_neg b)
    _ ≈ a := add_zero a

theorem pow2Neg_succ (s : Nat) : pow2Neg (s + 1) ≈ pow2Neg 1 * pow2Neg s := by
  rw [Nat.add_comm s 1]
  exact deq_symm (pow2Neg_mul 1 s)

theorem pow2Neg_half_add (k : Nat) : pow2Neg (k + 1) + pow2Neg (k + 1) ≈ pow2Neg k := by
  show ((1 : Int) * (2 ^ (k + 1) : Int) + 1 * (2 ^ (k + 1) : Int)) * (2 ^ k : Int) =
       1 * (2 ^ ((k + 1) + (k + 1)) : Int)
  rw [Int.one_mul, Int.one_mul]
  have hsucc : (2 ^ (k + 1) : Int) = (2 ^ k : Int) * 2 := Int.pow_succ 2 k
  calc
    ((2 ^ (k + 1) : Int) + (2 ^ (k + 1) : Int)) * (2 ^ k : Int)
        = (2 ^ (k + 1) : Int) * ((2 ^ k : Int) * 2) := by
          rw [Int.add_mul, Int.mul_comm (2 ^ (k + 1) : Int) (2 ^ k : Int)]
          have h2 : (2 ^ k : Int) * 2 = (2 ^ k : Int) + (2 ^ k : Int) := by omega
          rw [h2, Int.mul_add, Int.mul_comm (2 ^ k : Int) (2 ^ (k + 1) : Int)]
    _ = (2 ^ (k + 1) : Int) * (2 ^ (k + 1) : Int) := by rw [← hsucc]
    _ = (2 ^ ((k + 1) + (k + 1)) : Int) := (two_pow_add (k + 1) (k + 1)).symm

theorem pow2Neg_sub_half (k : Nat) : pow2Neg k - pow2Neg (k + 1) ≈ pow2Neg (k + 1) := by
  calc
    pow2Neg k - pow2Neg (k + 1)
        ≈ (pow2Neg (k + 1) + pow2Neg (k + 1)) - pow2Neg (k + 1) :=
          sub_congr (deq_symm (pow2Neg_half_add k)) (deq_refl _)
    _ ≈ pow2Neg (k + 1) := add_sub_cancel _ _

theorem sub_sub_sub_cancel (a b c : Dyad) : (a - b) - (a - c) ≈ c - b := by
  calc
    (a - b) - (a - c)
        ≈ (a + (-b)) + ((-a) + (-(-c))) := add_congr (deq_refl _) (neg_add a (-c))
    _ ≈ (a + (-b)) + ((-a) + c) := add_congr (deq_refl _) (add_congr (deq_refl _) (neg_neg c))
    _ ≈ a + ((-b) + ((-a) + c)) := add_assoc _ _ _
    _ ≈ a + (((-b) + (-a)) + c) := add_congr (deq_refl _) (deq_symm (add_assoc _ _ _))
    _ ≈ a + (((-a) + (-b)) + c) := add_congr (deq_refl _) (add_congr (add_comm _ _) (deq_refl _))
    _ ≈ a + ((-a) + ((-b) + c)) := add_congr (deq_refl _) (add_assoc _ _ _)
    _ ≈ (a + (-a)) + ((-b) + c) := deq_symm (add_assoc _ _ _)
    _ ≈ zero + ((-b) + c) := add_congr (add_neg a) (deq_refl _)
    _ ≈ (-b) + c := zero_add _
    _ ≈ c + (-b) := add_comm _ _

theorem shr_eq_mul (a : Dyad) (s : Nat) : shr a s ≈ a * pow2Neg s := by
  show a.mant * (2 ^ (a.shift + s) : Int) = (a.mant * 1) * (2 ^ (a.shift + s) : Int)
  simp

theorem ofInt_add (x y : Int) : ofInt (x + y) ≈ ofInt x + ofInt y := by
  show (x + y) * (2 ^ 0 : Int) = (x * (2 ^ 0 : Int) + y * (2 ^ 0 : Int)) * (2 ^ 0 : Int)
  simp

theorem ofInt_mul (x y : Int) : ofInt (x * y) ≈ ofInt x * ofInt y := rfl

-- Order lemmas

theorem dle_refl (a : Dyad) : a ≤ᵈ a := Int.le_refl _

theorem dle_congr {a b c d : Dyad} (h1 : a ≈ b) (h2 : c ≈ d) (h : a ≤ᵈ c) : b ≤ᵈ d :=
  dle_trans (dle_of_deq (deq_symm h1)) (dle_trans h (dle_of_deq h2))

theorem dlt_congr {a b c d : Dyad} (h1 : a ≈ b) (h2 : c ≈ d) (h : a <ᵈ c) : b <ᵈ d :=
  dlt_of_dle_of_dlt (dle_of_deq (deq_symm h1)) (dlt_of_dlt_of_dle h (dle_of_deq h2))

theorem zero_dlt_iff (a : Dyad) : zero <ᵈ a ↔ 0 < a.mant := by
  show (0 : Int) * (2 ^ a.shift : Int) < a.mant * (2 ^ 0 : Int) ↔ 0 < a.mant
  simp

theorem zero_dle_iff (a : Dyad) : zero ≤ᵈ a ↔ 0 ≤ a.mant := by
  show (0 : Int) * (2 ^ a.shift : Int) ≤ a.mant * (2 ^ 0 : Int) ↔ 0 ≤ a.mant
  simp

theorem deq_zero_iff (a : Dyad) : a ≈ zero ↔ a.mant = 0 := by
  show a.mant * (2 ^ 0 : Int) = 0 * (2 ^ a.shift : Int) ↔ a.mant = 0
  simp

theorem not_dlt_of_dle {a b : Dyad} (h : a ≤ᵈ b) : ¬ (b <ᵈ a) := by
  unfold dle dlt at *
  omega

theorem dle_of_not_dlt {a b : Dyad} (h : ¬ (b <ᵈ a)) : a ≤ᵈ b := by
  unfold dle dlt at *
  omega

theorem add_dle_add {a b c d : Dyad} (h1 : a ≤ᵈ b) (h2 : c ≤ᵈ d) : a + c ≤ᵈ b + d := by
  show (a.mant * (2 ^ c.shift : Int) + c.mant * (2 ^ a.shift : Int)) * (2 ^ (b.shift + d.shift) : Int) ≤
       (b.mant * (2 ^ d.shift : Int) + d.mant * (2 ^ b.shift : Int)) * (2 ^ (a.shift + c.shift) : Int)
  unfold dle at h1 h2
  rw [two_pow_add, two_pow_add, Int.add_mul, Int.add_mul]
  have h1' : a.mant * (2 ^ c.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int)) ≤
             b.mant * (2 ^ d.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by
    have hpos : (0 : Int) ≤ (2 ^ c.shift : Int) * (2 ^ d.shift : Int) :=
      Int.mul_nonneg (Int.le_of_lt (two_pow_pos c.shift)) (Int.le_of_lt (two_pow_pos d.shift))
    have hm := Int.mul_le_mul_of_nonneg_right h1 hpos
    calc a.mant * (2 ^ c.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int))
        = (a.mant * (2 ^ b.shift : Int)) * ((2 ^ c.shift : Int) * (2 ^ d.shift : Int)) := by ac_rfl
      _ ≤ (b.mant * (2 ^ a.shift : Int)) * ((2 ^ c.shift : Int) * (2 ^ d.shift : Int)) := hm
      _ = b.mant * (2 ^ d.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by ac_rfl
  have h2' : c.mant * (2 ^ a.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int)) ≤
             d.mant * (2 ^ b.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by
    have hpos : (0 : Int) ≤ (2 ^ a.shift : Int) * (2 ^ b.shift : Int) :=
      Int.mul_nonneg (Int.le_of_lt (two_pow_pos a.shift)) (Int.le_of_lt (two_pow_pos b.shift))
    have hm := Int.mul_le_mul_of_nonneg_right h2 hpos
    calc c.mant * (2 ^ a.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int))
        = (c.mant * (2 ^ d.shift : Int)) * ((2 ^ a.shift : Int) * (2 ^ b.shift : Int)) := by ac_rfl
      _ ≤ (d.mant * (2 ^ c.shift : Int)) * ((2 ^ a.shift : Int) * (2 ^ b.shift : Int)) := hm
      _ = d.mant * (2 ^ b.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by ac_rfl
  exact Int.add_le_add h1' h2'

theorem add_dlt_add_of_dlt_of_dle {a b c d : Dyad} (h1 : a <ᵈ b) (h2 : c ≤ᵈ d) : a + c <ᵈ b + d := by
  show (a.mant * (2 ^ c.shift : Int) + c.mant * (2 ^ a.shift : Int)) * (2 ^ (b.shift + d.shift) : Int) <
       (b.mant * (2 ^ d.shift : Int) + d.mant * (2 ^ b.shift : Int)) * (2 ^ (a.shift + c.shift) : Int)
  unfold dlt at h1
  unfold dle at h2
  rw [two_pow_add, two_pow_add, Int.add_mul, Int.add_mul]
  have h1' : a.mant * (2 ^ c.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int)) <
             b.mant * (2 ^ d.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by
    have hpos : (0 : Int) < (2 ^ c.shift : Int) * (2 ^ d.shift : Int) :=
      Int.mul_pos (two_pow_pos c.shift) (two_pow_pos d.shift)
    have hm := Int.mul_lt_mul_of_pos_right h1 hpos
    calc a.mant * (2 ^ c.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int))
        = (a.mant * (2 ^ b.shift : Int)) * ((2 ^ c.shift : Int) * (2 ^ d.shift : Int)) := by ac_rfl
      _ < (b.mant * (2 ^ a.shift : Int)) * ((2 ^ c.shift : Int) * (2 ^ d.shift : Int)) := hm
      _ = b.mant * (2 ^ d.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by ac_rfl
  have h2' : c.mant * (2 ^ a.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int)) ≤
             d.mant * (2 ^ b.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by
    have hpos : (0 : Int) ≤ (2 ^ a.shift : Int) * (2 ^ b.shift : Int) :=
      Int.mul_nonneg (Int.le_of_lt (two_pow_pos a.shift)) (Int.le_of_lt (two_pow_pos b.shift))
    have hm := Int.mul_le_mul_of_nonneg_right h2 hpos
    calc c.mant * (2 ^ a.shift : Int) * ((2 ^ b.shift : Int) * (2 ^ d.shift : Int))
        = (c.mant * (2 ^ d.shift : Int)) * ((2 ^ a.shift : Int) * (2 ^ b.shift : Int)) := by ac_rfl
      _ ≤ (d.mant * (2 ^ c.shift : Int)) * ((2 ^ a.shift : Int) * (2 ^ b.shift : Int)) := hm
      _ = d.mant * (2 ^ b.shift : Int) * ((2 ^ a.shift : Int) * (2 ^ c.shift : Int)) := by ac_rfl
  omega

theorem add_dlt_add_of_dle_of_dlt {a b c d : Dyad} (h1 : a ≤ᵈ b) (h2 : c <ᵈ d) : a + c <ᵈ b + d :=
  dlt_congr (add_comm c a) (add_comm d b) (add_dlt_add_of_dlt_of_dle h2 h1)

theorem neg_dle_neg {a b : Dyad} (h : a ≤ᵈ b) : -b ≤ᵈ -a := by
  show (-b.mant) * (2 ^ a.shift : Int) ≤ (-a.mant) * (2 ^ b.shift : Int)
  unfold dle at h
  rw [Int.neg_mul, Int.neg_mul]
  omega

theorem sub_dle_sub_left (a : Dyad) {b c : Dyad} (h : b ≤ᵈ c) : a - c ≤ᵈ a - b :=
  add_dle_add (dle_refl a) (neg_dle_neg h)

theorem sub_le_self_of_nonneg (a : Dyad) {b : Dyad} (hb : zero ≤ᵈ b) : a - b ≤ᵈ a := by
  have hneg : -b ≤ᵈ zero := dle_congr (deq_refl _) neg_zero (neg_dle_neg hb)
  exact dle_trans (add_dle_add (dle_refl a) hneg) (dle_of_deq (add_zero a))

theorem dle_of_ofInt_mul_dle {z : Int} (hz : 0 < z) {a b : Dyad}
    (h : ofInt z * a ≤ᵈ ofInt z * b) : a ≤ᵈ b := by
  change (z * a.mant) * (2 ^ (0 + b.shift) : Int) ≤ (z * b.mant) * (2 ^ (0 + a.shift) : Int) at h
  simp only [Nat.zero_add] at h
  rw [Int.mul_assoc z, Int.mul_assoc z] at h
  show a.mant * (2 ^ b.shift : Int) ≤ b.mant * (2 ^ a.shift : Int)
  by_cases hle : a.mant * (2 ^ b.shift : Int) ≤ b.mant * (2 ^ a.shift : Int)
  · exact hle
  · have hgt : b.mant * (2 ^ a.shift : Int) < a.mant * (2 ^ b.shift : Int) := by omega
    have hm := Int.mul_lt_mul_of_pos_left hgt hz
    omega

theorem dle_zero_of_ofInt_mul_dle_zero {z : Int} (hz : 0 < z) {a : Dyad}
    (h : ofInt z * a ≤ᵈ zero) : a ≤ᵈ zero :=
  dle_of_ofInt_mul_dle hz (dle_congr (deq_refl _) (deq_symm (mul_zero (ofInt z))) h)

theorem mul_dle_mul_of_nonneg_left {a b c : Dyad} (hc : zero ≤ᵈ c) (h : a ≤ᵈ b) : c * a ≤ᵈ c * b := by
  show (c.mant * a.mant) * (2 ^ (c.shift + b.shift) : Int) ≤
       (c.mant * b.mant) * (2 ^ (c.shift + a.shift) : Int)
  rw [zero_dle_iff] at hc
  unfold dle at h
  rw [two_pow_add, two_pow_add]
  have hpos : (0 : Int) ≤ c.mant * (2 ^ c.shift : Int) :=
    Int.mul_nonneg hc (Int.le_of_lt (two_pow_pos c.shift))
  have hm := Int.mul_le_mul_of_nonneg_left h hpos
  simpa [Int.mul_assoc, Int.mul_left_comm] using hm

theorem mul_dle_mul_of_nonneg_right {a b c : Dyad} (hc : zero ≤ᵈ c) (h : a ≤ᵈ b) : a * c ≤ᵈ b * c :=
  dle_congr (mul_comm c a) (mul_comm c b) (mul_dle_mul_of_nonneg_left hc h)

theorem mul_dlt_mul_of_pos_left {a b c : Dyad} (hc : zero <ᵈ c) (h : a <ᵈ b) : c * a <ᵈ c * b := by
  show (c.mant * a.mant) * (2 ^ (c.shift + b.shift) : Int) <
       (c.mant * b.mant) * (2 ^ (c.shift + a.shift) : Int)
  rw [zero_dlt_iff] at hc
  unfold dlt at h
  rw [two_pow_add, two_pow_add]
  have hpos : (0 : Int) < c.mant * (2 ^ c.shift : Int) :=
    Int.mul_pos hc (two_pow_pos c.shift)
  have hm := Int.mul_lt_mul_of_pos_left h hpos
  simpa [Int.mul_assoc, Int.mul_left_comm] using hm

theorem mul_pos_of_pos {a b : Dyad} (ha : zero <ᵈ a) (hb : zero <ᵈ b) : zero <ᵈ a * b := by
  rw [zero_dlt_iff] at *
  exact Int.mul_pos ha hb

theorem mul_nonneg_of_nonneg {a b : Dyad} (ha : zero ≤ᵈ a) (hb : zero ≤ᵈ b) : zero ≤ᵈ a * b := by
  rw [zero_dle_iff] at *
  exact Int.mul_nonneg ha hb

theorem sq_nonneg (a : Dyad) : zero ≤ᵈ a * a := by
  rw [zero_dle_iff]
  change 0 ≤ a.mant * a.mant
  by_cases h : 0 ≤ a.mant
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -a.mant := by omega
    have hmul : 0 ≤ (-a.mant) * (-a.mant) := Int.mul_nonneg hneg hneg
    rw [Int.neg_mul_neg] at hmul
    exact hmul

theorem sq_pos_of_ne_zero {a : Dyad} (h : ¬ (a ≈ zero)) : zero <ᵈ a * a := by
  rw [deq_zero_iff] at h
  rw [zero_dlt_iff]
  change 0 < a.mant * a.mant
  by_cases hp : 0 < a.mant
  · exact Int.mul_pos hp hp
  · have hn : 0 < -a.mant := by omega
    have hmul : 0 < (-a.mant) * (-a.mant) := Int.mul_pos hn hn
    rw [Int.neg_mul_neg] at hmul
    exact hmul

theorem pow2Neg_pos (s : Nat) : zero <ᵈ pow2Neg s := by
  rw [zero_dlt_iff]; show (0 : Int) < 1; decide

theorem pow2Neg_nonneg (s : Nat) : zero ≤ᵈ pow2Neg s :=
  dle_of_dlt (pow2Neg_pos s)

theorem pow2Neg_antitone {s t : Nat} (h : s ≤ t) : pow2Neg t ≤ᵈ pow2Neg s := by
  show (1 : Int) * (2 ^ s : Int) ≤ 1 * (2 ^ t : Int)
  rw [Int.one_mul, Int.one_mul]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [two_pow_add]
  have hd : (1 : Int) ≤ (2 ^ d : Int) := by have hp := two_pow_pos d; omega
  have hs : (0 : Int) ≤ (2 ^ s : Int) := Int.le_of_lt (two_pow_pos s)
  calc (2 ^ s : Int) = (2 ^ s : Int) * 1 := (Int.mul_one _).symm
    _ ≤ (2 ^ s : Int) * (2 ^ d : Int) := Int.mul_le_mul_of_nonneg_left hd hs

theorem sub_nonneg_iff (a b : Dyad) : zero ≤ᵈ a - b ↔ b ≤ᵈ a := by
  rw [zero_dle_iff]
  change 0 ≤ a.mant * (2 ^ b.shift : Int) + (-b.mant) * (2 ^ a.shift : Int) ↔
         b.mant * (2 ^ a.shift : Int) ≤ a.mant * (2 ^ b.shift : Int)
  rw [Int.neg_mul]
  omega

theorem sub_pos_iff (a b : Dyad) : zero <ᵈ a - b ↔ b <ᵈ a := by
  rw [zero_dlt_iff]
  change 0 < a.mant * (2 ^ b.shift : Int) + (-b.mant) * (2 ^ a.shift : Int) ↔
         b.mant * (2 ^ a.shift : Int) < a.mant * (2 ^ b.shift : Int)
  rw [Int.neg_mul]
  omega

theorem dle_iff_sub_nonneg {a b : Dyad} : a ≤ᵈ b ↔ zero ≤ᵈ b - a :=
  (sub_nonneg_iff b a).symm

/-- Archimedean property in `Z[1/2]`: for `a > 0` and `b ≥ 0`, `∃ k, b * 2^(-k) ≤ a`. -/
theorem exists_pow2Neg_le {a b : Dyad} (ha : zero <ᵈ a) (hb : zero ≤ᵈ b) :
    ∃ k : Nat, b * pow2Neg k ≤ᵈ a := by
  rw [zero_dlt_iff] at ha
  rw [zero_dle_iff] at hb
  let M : Nat := (b.mant * (2 ^ a.shift : Int)).toNat
  refine ⟨M, ?_⟩
  show (b.mant * 1) * (2 ^ a.shift : Int) ≤ a.mant * (2 ^ (b.shift + M) : Int)
  rw [Int.mul_one, two_pow_add]
  have h1 : b.mant * (2 ^ a.shift : Int) ≤ (M : Int) := by
    have hnn : 0 ≤ b.mant * (2 ^ a.shift : Int) :=
      Int.mul_nonneg hb (Int.le_of_lt (two_pow_pos a.shift))
    omega
  have h2 : (M : Int) < (2 ^ M : Int) := by
    have hn : M < 2 ^ M := Nat.lt_two_pow_self
    exact_mod_cast hn
  have h3 : (1 : Int) ≤ a.mant := by omega
  have h4 : (1 : Int) ≤ (2 ^ b.shift : Int) := by
    have hp := two_pow_pos b.shift; omega
  have h5 : (2 ^ M : Int) ≤ (2 ^ b.shift : Int) * (2 ^ M : Int) := by
    have hp := Int.le_of_lt (two_pow_pos M)
    calc (2 ^ M : Int) = 1 * (2 ^ M : Int) := (Int.one_mul _).symm
      _ ≤ (2 ^ b.shift : Int) * (2 ^ M : Int) := Int.mul_le_mul_of_nonneg_right h4 hp
  have h6 : (2 ^ b.shift : Int) * (2 ^ M : Int) ≤ a.mant * ((2 ^ b.shift : Int) * (2 ^ M : Int)) := by
    have hp := Int.mul_nonneg (Int.le_of_lt (two_pow_pos b.shift)) (Int.le_of_lt (two_pow_pos M))
    calc (2 ^ b.shift : Int) * (2 ^ M : Int)
        = 1 * ((2 ^ b.shift : Int) * (2 ^ M : Int)) := (Int.one_mul _).symm
      _ ≤ a.mant * ((2 ^ b.shift : Int) * (2 ^ M : Int)) := Int.mul_le_mul_of_nonneg_right h3 hp
  omega

end Dyad

open Dyad

-- ============================================================================
-- LAYER 2: EXACT DYADIC SUMS, MATRICES, AND GENERAL LDL^T ENGINE (EXACT IFF!)
-- ============================================================================

theorem dsum_add (n : Nat) (f g : Nat → Dyad) :
    dsum n (fun i => f i + g i) ≈ dsum n f + dsum n g := by
  induction n with
  | zero => exact deq_symm (add_zero zero)
  | succ k ih =>
    show dsum k (fun i => f i + g i) + (f k + g k) ≈ (dsum k f + f k) + (dsum k g + g k)
    calc
      dsum k (fun i => f i + g i) + (f k + g k)
          ≈ (dsum k f + dsum k g) + (f k + g k) := add_congr ih (deq_refl _)
      _ ≈ dsum k f + (dsum k g + (f k + g k)) := add_assoc _ _ _
      _ ≈ dsum k f + ((dsum k g + f k) + g k) :=
            add_congr (deq_refl _) (deq_symm (add_assoc _ _ _))
      _ ≈ dsum k f + ((f k + dsum k g) + g k) :=
            add_congr (deq_refl _) (add_congr (add_comm _ _) (deq_refl _))
      _ ≈ dsum k f + (f k + (dsum k g + g k)) :=
            add_congr (deq_refl _) (add_assoc _ _ _)
      _ ≈ (dsum k f + f k) + (dsum k g + g k) := deq_symm (add_assoc _ _ _)

theorem dsum_mul_left (n : Nat) (c : Dyad) (f : Nat → Dyad) :
    dsum n (fun i => c * f i) ≈ c * dsum n f := by
  induction n with
  | zero => exact deq_symm (mul_zero c)
  | succ k ih =>
    show dsum k (fun i => c * f i) + c * f k ≈ c * (dsum k f + f k)
    exact deq_trans (add_congr ih (deq_refl _)) (deq_symm (mul_add c _ _))

theorem dsum_mul_right (n : Nat) (f : Nat → Dyad) (c : Dyad) :
    dsum n (fun i => f i * c) ≈ dsum n f * c := by
  induction n with
  | zero => exact deq_symm (zero_mul c)
  | succ k ih =>
    show dsum k (fun i => f i * c) + f k * c ≈ (dsum k f + f k) * c
    exact deq_trans (add_congr ih (deq_refl _)) (deq_symm (add_mul _ _ c))

theorem dsum_split (n m : Nat) (f : Nat → Dyad) :
    dsum (n + m) f ≈ dsum n f + dsum m (fun i => f (n + i)) := by
  induction m with
  | zero => exact deq_symm (add_zero _)
  | succ k ih =>
    show dsum (n + k) f + f (n + k) ≈ dsum n f + (dsum k (fun i => f (n + i)) + f (n + k))
    exact deq_trans (add_congr ih (deq_refl _)) (add_assoc _ _ _)

theorem dsum_swap (n m : Nat) (f : Nat → Nat → Dyad) :
    dsum n (fun i => dsum m (fun j => f i j)) ≈
    dsum m (fun j => dsum n (fun i => f i j)) := by
  induction n with
  | zero => exact deq_symm (dsum_zero m)
  | succ k ih =>
    show dsum k (fun i => dsum m (fun j => f i j)) + dsum m (fun j => f k j) ≈
         dsum m (fun j => dsum k (fun i => f i j) + f k j)
    exact deq_trans (add_congr ih (deq_refl _)) (deq_symm (dsum_add m _ _))

theorem dsum_prefix_of_zero_tail {n N : Nat} (hle : n ≤ N) {f : Nat → Dyad}
    (hz : ∀ r, n ≤ r → r < N → f r ≈ zero) :
    dsum N f ≈ dsum n f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
  have htail : dsum m (fun i => f (n + i)) ≈ zero :=
    dsum_eq_zero (fun i hi => hz (n + i) (Nat.le_add_right n i) (by omega))
  exact deq_trans (dsum_split n m f) (deq_trans (add_congr (deq_refl _) htail) (add_zero _))

theorem dsum_rev (n : Nat) (f : Nat → Dyad) :
    dsum n (fun i => f (n - 1 - i)) ≈ dsum n f := by
  induction n with
  | zero => exact deq_refl _
  | succ k ih =>
    have hsplit : dsum (k + 1) (fun i => f (k - i)) ≈
                  dsum 1 (fun i => f (k - i)) + dsum k (fun i => f (k - (1 + i))) := by
      simpa [Nat.add_comm] using dsum_split 1 k (fun i => f (k - i))
    have h1 : dsum 1 (fun i => f (k - i)) ≈ f k := by
      show zero + f (k - 0) ≈ f k
      simpa using zero_add (f k)
    have h2 : dsum k (fun i => f (k - (1 + i))) ≈ dsum k f := by
      have hcongr : dsum k (fun i => f (k - (1 + i))) ≈ dsum k (fun i => f (k - 1 - i)) :=
        dsum_congr (fun i _ => by
          have heq : k - (1 + i) = k - 1 - i := by omega
          rw [heq]; exact deq_refl _)
      exact deq_trans hcongr ih
    have hsub : dsum (k + 1) (fun i => f (k + 1 - 1 - i)) ≈ dsum (k + 1) (fun i => f (k - i)) :=
      dsum_congr (fun i _ => by simp; exact deq_refl _)
    exact deq_trans hsub
      (deq_trans hsplit (deq_trans (add_congr h1 h2) (add_comm (f k) (dsum k f))))

theorem dsum_nonneg {n : Nat} {f : Nat → Dyad}
    (h : ∀ i, i < n → zero ≤ᵈ f i) : zero ≤ᵈ dsum n f := by
  induction n with
  | zero => exact dle_refl _
  | succ k ih =>
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h k (Nat.lt_succ_self k)
    exact dle_congr (add_zero zero) (deq_refl _) (add_dle_add h1 h2)

theorem dsum_pos_of_exists_pos {n : Nat} {f : Nat → Dyad}
    (hnn : ∀ i, i < n → zero ≤ᵈ f i)
    (hex : ∃ r, r < n ∧ zero <ᵈ f r) : zero <ᵈ dsum n f := by
  induction n with
  | zero =>
    obtain ⟨r, hr, _⟩ := hex; omega
  | succ k ih =>
    obtain ⟨r, hr, hpos⟩ := hex
    by_cases hkr : r = k
    · subst hkr
      have hpre := dsum_nonneg (fun i hi => hnn i (Nat.lt_succ_of_lt hi))
      exact dlt_congr (add_zero zero) (deq_refl _) (add_dlt_add_of_dle_of_dlt hpre hpos)
    · have hpre := ih (fun i hi => hnn i (Nat.lt_succ_of_lt hi)) ⟨r, by omega, hpos⟩
      have hlast := hnn k (Nat.lt_succ_self k)
      exact dlt_congr (add_zero zero) (deq_refl _) (add_dlt_add_of_dlt_of_dle hpre hlast)

theorem dsum_dle_dsum {n : Nat} {f g : Nat → Dyad}
    (h : ∀ i, i < n → f i ≤ᵈ g i) : dsum n f ≤ᵈ dsum n g := by
  induction n with
  | zero => exact dle_refl _
  | succ k ih =>
    exact add_dle_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h k (Nat.lt_succ_self k))

-- Matrix and vector types

/-- Exact quadratic form identity: `v^T (L D L^T) v ≈ ∑_{r < N} D r * (L^T v)_r^2`. -/
theorem ldlt_quadForm_eq {N : Nat} {M L : Mat} {D : Vec}
    (h : IsLDLTAlg N M L D) (v : Vec) :
    quadForm N M v ≈ dsum N (fun r => D r * (matTVec N L v r * matTVec N L v r)) := by
  unfold quadForm
  have h1 : dsum N (fun i => dsum N (fun j => v i * M i j * v j)) ≈
            dsum N (fun i => dsum N (fun j => dsum N (fun r => D r * (L i r * v i) * (L j r * v j)))) := by
    refine dsum_congr (fun i hi => dsum_congr (fun j hj => ?_))
    have hfac := h.factor i j hi hj
    calc
      v i * M i j * v j
          ≈ v i * dsum N (fun r => L i r * D r * L j r) * v j :=
            mul_congr (mul_congr (deq_refl _) hfac) (deq_refl _)
      _ ≈ dsum N (fun r => v i * (L i r * D r * L j r)) * v j :=
            mul_congr (deq_symm (dsum_mul_left N (v i) _)) (deq_refl _)
      _ ≈ dsum N (fun r => v i * (L i r * D r * L j r) * v j) :=
            deq_symm (dsum_mul_right N _ (v j))
      _ ≈ dsum N (fun r => D r * (L i r * v i) * (L j r * v j)) := by
            refine dsum_congr (fun r _ => ?_)
            show (v i).mant * ((L i r).mant * (D r).mant * (L j r).mant) * (v j).mant *
                 (2 ^ ((D r).shift + ((L i r).shift + (v i).shift) + ((L j r).shift + (v j).shift)) : Int) =
                 (D r).mant * ((L i r).mant * (v i).mant) * ((L j r).mant * (v j).mant) *
                 (2 ^ ((v i).shift + ((L i r).shift + (D r).shift + (L j r).shift) + (v j).shift) : Int)
            have hs : (D r).shift + ((L i r).shift + (v i).shift) + ((L j r).shift + (v j).shift) =
                      (v i).shift + ((L i r).shift + (D r).shift + (L j r).shift) + (v j).shift := by omega
            rw [hs]
            congr 1
            simp only [Int.mul_assoc, Int.mul_left_comm]
  have h2 : dsum N (fun i => dsum N (fun j => dsum N (fun r => D r * (L i r * v i) * (L j r * v j)))) ≈
            dsum N (fun r => dsum N (fun i => dsum N (fun j => D r * (L i r * v i) * (L j r * v j)))) := by
    calc
      dsum N (fun i => dsum N (fun j => dsum N (fun r => D r * (L i r * v i) * (L j r * v j))))
          ≈ dsum N (fun i => dsum N (fun r => dsum N (fun j => D r * (L i r * v i) * (L j r * v j)))) :=
            dsum_congr (fun i _ => dsum_swap N N (fun j r => D r * (L i r * v i) * (L j r * v j)))
      _ ≈ dsum N (fun r => dsum N (fun i => dsum N (fun j => D r * (L i r * v i) * (L j r * v j)))) :=
            dsum_swap N N (fun i r => dsum N (fun j => D r * (L i r * v i) * (L j r * v j)))
  have h3 : dsum N (fun r => dsum N (fun i => dsum N (fun j => D r * (L i r * v i) * (L j r * v j)))) ≈
            dsum N (fun r => D r * (matTVec N L v r * matTVec N L v r)) := by
    refine dsum_congr (fun r _ => ?_)
    calc
      dsum N (fun i => dsum N (fun j => D r * (L i r * v i) * (L j r * v j)))
          ≈ dsum N (fun i => D r * (L i r * v i) * matTVec N L v r) :=
            dsum_congr (fun i _ => dsum_mul_left N (D r * (L i r * v i)) (fun j => L j r * v j))
      _ ≈ dsum N (fun i => D r * (L i r * v i)) * matTVec N L v r :=
            dsum_mul_right N (fun i => D r * (L i r * v i)) (matTVec N L v r)
      _ ≈ (D r * matTVec N L v r) * matTVec N L v r :=
            mul_congr (dsum_mul_left N (D r) (fun i => L i r * v i)) (deq_refl _)
      _ ≈ D r * (matTVec N L v r * matTVec N L v r) := mul_assoc _ _ _
  exact deq_trans h1 (deq_trans h2 h3)

/-- Unit lower-triangular matrices have injective transpose over `Z[1/2]` (no division!). -/
theorem unitLower_transpose_injective {N : Nat} {L : Mat}
    (hL : IsUnitLowerTri N L) {v : Vec}
    (hv : ∃ i, i < N ∧ ¬ (v i ≈ zero)) :
    ∃ r, r < N ∧ ¬ (matTVec N L v r ≈ zero) := by
  induction N with
  | zero =>
    obtain ⟨i, hi, _⟩ := hv; omega
  | succ k ih =>
    by_cases hlast : v k ≈ zero
    · have hv' : ∃ i, i < k ∧ ¬ (v i ≈ zero) := by
        obtain ⟨i, hi, hne⟩ := hv
        by_cases hik : i = k
        · subst hik; exact absurd hlast hne
        · exact ⟨i, by omega, hne⟩
      have hL' : IsUnitLowerTri k L :=
        ⟨fun i hi => hL.1 i (Nat.lt_succ_of_lt hi),
         fun i j hi hj hij => hL.2 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij⟩
      obtain ⟨r, hr, hne⟩ := ih hL' hv'
      refine ⟨r, Nat.lt_succ_of_lt hr, ?_⟩
      intro hz
      apply hne
      have hstep : matTVec (k + 1) L v r ≈ matTVec k L v r := by
        show matTVec k L v r + L k r * v k ≈ matTVec k L v r
        have hmul0 : L k r * v k ≈ zero := deq_trans (mul_congr (deq_refl _) hlast) (mul_zero _)
        exact deq_trans (add_congr (deq_refl _) hmul0) (add_zero _)
      exact deq_trans (deq_symm hstep) hz
    · refine ⟨k, Nat.lt_succ_self k, ?_⟩
      have heq : matTVec (k + 1) L v k ≈ v k := by
        have hsingle : matTVec (k + 1) L v k ≈ L k k * v k :=
          dsum_single (Nat.lt_succ_self k) (fun i => L i k * v i) (fun i hi hne => by
            have hik : i < k := by omega
            have h0 : L i k ≈ zero := hL.2 i k hi (Nat.lt_succ_self k) hik
            exact deq_trans (mul_congr h0 (deq_refl _)) (zero_mul _))
        exact deq_trans hsingle (deq_trans (mul_congr (hL.1 k (Nat.lt_succ_self k)) (deq_refl _)) (one_mul _))
      intro hz
      exact hlast (deq_trans (deq_symm heq) hz)

theorem backSubAux_spec {N : Nat} {L : Mat} (hL : IsUnitLowerTri N L) (rStar : Nat) :
    ∀ m, m ≤ N →
      (∀ i, i < N - m → backSubAux N L rStar m i ≈ zero) ∧
      (∀ r, N - m ≤ r → r < N →
        dsum m (fun t => L (N - 1 - t) r * backSubAux N L rStar m (N - 1 - t)) ≈
        if r = rStar then one else zero) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ _ => deq_refl _, fun r hr1 hr2 => by omega⟩
  | succ k ih =>
    intro hle
    obtain ⟨hzero, hsol⟩ := ih (by omega)
    let idx := N - 1 - k
    have hidx_lt : idx < N := by omega
    have hagree : ∀ t, t < k →
        backSubAux N L rStar (k + 1) (N - 1 - t) = backSubAux N L rStar k (N - 1 - t) := by
      intro t ht
      change (if N - 1 - t = idx then _ else backSubAux N L rStar k (N - 1 - t)) = _
      have hne : N - 1 - t ≠ idx := by omega
      simp [hne]
    constructor
    · intro i hi
      change (if i = idx then _ else backSubAux N L rStar k i) ≈ zero
      have hne : i ≠ idx := by omega
      simp only [hne, ↓reduceIte]
      exact hzero i (by omega)
    · intro r hr1 hr2
      show dsum k (fun t => L (N - 1 - t) r * backSubAux N L rStar (k + 1) (N - 1 - t)) +
           L idx r * backSubAux N L rStar (k + 1) idx ≈
           if r = rStar then one else zero
      have hpre_eq :
          dsum k (fun t => L (N - 1 - t) r * backSubAux N L rStar (k + 1) (N - 1 - t)) ≈
          dsum k (fun t => L (N - 1 - t) r * backSubAux N L rStar k (N - 1 - t)) :=
        dsum_congr (fun t ht => by rw [hagree t ht]; exact deq_refl _)
      by_cases hri : r = idx
      · subst hri
        have hval : backSubAux N L rStar (k + 1) idx =
            (if idx = rStar then one else zero) -
            dsum k (fun t => L (N - 1 - t) idx * backSubAux N L rStar k (N - 1 - t)) := by
          rw [show backSubAux N L rStar (k + 1) idx =
              (if idx = N - 1 - k then
                (if N - 1 - k = rStar then one else zero) -
                  dsum k (fun t => L (N - 1 - t) (N - 1 - k) * backSubAux N L rStar k (N - 1 - t))
              else backSubAux N L rStar k idx) from rfl]
          simp only [idx, ↓reduceIte]
        rw [hval]
        let tail := dsum k (fun t => L (N - 1 - t) idx * backSubAux N L rStar k (N - 1 - t))
        let rhs := if idx = rStar then one else zero
        calc
          dsum k (fun t => L (N - 1 - t) idx * backSubAux N L rStar (k + 1) (N - 1 - t)) +
            L idx idx * (rhs - tail)
              ≈ tail + one * (rhs - tail) :=
                add_congr hpre_eq (mul_congr (hL.1 idx hidx_lt) (deq_refl _))
          _ ≈ tail + (rhs - tail) := add_congr (deq_refl _) (one_mul _)
          _ ≈ (rhs - tail) + tail := add_comm _ _
          _ ≈ rhs := sub_add_cancel rhs tail
      · have hgt : idx < r := by omega
        have hL0 : L idx r ≈ zero := hL.2 idx r hidx_lt hr2 hgt
        have hlast0 : L idx r * backSubAux N L rStar (k + 1) idx ≈ zero :=
          deq_trans (mul_congr hL0 (deq_refl _)) (zero_mul _)
        exact deq_trans (add_congr (deq_trans hpre_eq (hsol r (by omega) hr2)) hlast0) (add_zero _)

theorem backSubVec_matTVec {N : Nat} {L : Mat} (hL : IsUnitLowerTri N L)
    {rStar r : Nat} (hr : r < N) :
    matTVec N L (backSubVec N L rStar) r ≈ (if r = rStar then one else zero) := by
  have hspec := (backSubAux_spec hL rStar N (Nat.le_refl N)).2 r (by omega) hr
  have hrev : matTVec N L (backSubVec N L rStar) r ≈
              dsum N (fun t => L (N - 1 - t) r * backSubVec N L rStar (N - 1 - t)) :=
    deq_symm (dsum_rev N (fun i => L i r * backSubVec N L rStar i))
  exact deq_trans hrev hspec

theorem backSubVec_nonzero {N : Nat} {L : Mat} (hL : IsUnitLowerTri N L)
    {rStar : Nat} (hr : rStar < N) :
    ∃ i, i < N ∧ ¬ (backSubVec N L rStar i ≈ zero) := by
  -- If backSubVec were identically zero on [0, N), then matTVec at rStar would be 0 ≠ 1!
  have htv : matTVec N L (backSubVec N L rStar) rStar ≈ one := by
    simpa using backSubVec_matTVec hL (rStar := rStar) hr
  -- Constructively find a nonzero index via decidable search on [0, N)
  have hex : ∀ m, m ≤ N →
      (∃ i, i < m ∧ ¬ (backSubVec N L rStar i ≈ zero)) ∨
      (∀ i, i < m → backSubVec N L rStar i ≈ zero) := by
    intro m
    induction m with
    | zero => intro _; exact Or.inr (fun i hi => by omega)
    | succ k ih =>
      intro hle
      cases ih (by omega) with
      | inl h =>
        obtain ⟨i, hi, hne⟩ := h
        exact Or.inl ⟨i, Nat.lt_succ_of_lt hi, hne⟩
      | inr hall =>
        by_cases hk : backSubVec N L rStar k ≈ zero
        · exact Or.inr (fun i hi => by
            by_cases hik : i = k
            · subst hik; exact hk
            · exact hall i (by omega))
        · exact Or.inl ⟨k, Nat.lt_succ_self k, hk⟩
  cases hex N (Nat.le_refl N) with
  | inl h => exact h
  | inr hall =>
    have h0 : matTVec N L (backSubVec N L rStar) rStar ≈ zero :=
      dsum_eq_zero (fun i hi => deq_trans (mul_congr (deq_refl _) (hall i hi)) (mul_zero _))
    have h10 : one ≈ zero := deq_trans (deq_symm htv) h0
    exact absurd h10 (by decide)

theorem backSubVec_quadForm {N : Nat} {M L : Mat} {D : Vec}
    (h : IsLDLTAlg N M L D) {rStar : Nat} (hr : rStar < N) :
    quadForm N M (backSubVec N L rStar) ≈ D rStar := by
  have hqf := ldlt_quadForm_eq h (backSubVec N L rStar)
  have hsingle : dsum N (fun r => D r * (matTVec N L (backSubVec N L rStar) r *
                                          matTVec N L (backSubVec N L rStar) r)) ≈
                 D rStar * (matTVec N L (backSubVec N L rStar) rStar *
                            matTVec N L (backSubVec N L rStar) rStar) := by
    refine dsum_single hr _ (fun r hrN hne => ?_)
    have htv0 : matTVec N L (backSubVec N L rStar) r ≈ zero := by
      simpa [hne] using backSubVec_matTVec h.unitLower (rStar := rStar) hrN
    calc
      D r * (matTVec N L (backSubVec N L rStar) r * matTVec N L (backSubVec N L rStar) r)
          ≈ D r * (zero * zero) := mul_congr (deq_refl _) (mul_congr htv0 htv0)
      _ ≈ D r * zero := mul_congr (deq_refl _) (mul_zero zero)
      _ ≈ zero := mul_zero _
  have htv1 : matTVec N L (backSubVec N L rStar) rStar ≈ one := by
    simpa using backSubVec_matTVec h.unitLower (rStar := rStar) hr
  calc
    quadForm N M (backSubVec N L rStar)
        ≈ dsum N (fun r => D r * (matTVec N L (backSubVec N L rStar) r *
                                  matTVec N L (backSubVec N L rStar) r)) := hqf
    _ ≈ D rStar * (matTVec N L (backSubVec N L rStar) rStar *
                   matTVec N L (backSubVec N L rStar) rStar) := hsingle
    _ ≈ D rStar * (one * one) := mul_congr (deq_refl _) (mul_congr htv1 htv1)
    _ ≈ D rStar * one := mul_congr (deq_refl _) (mul_one one)
    _ ≈ D rStar := mul_one _

/-- **EXACT IFF SOUNDNESS & NECESSITY THEOREM**:
    For any exact dyadic `LDL^T` factorization `M = L D L^T`,
    `M` is strictly positive definite over `Z[1/2]` IF AND ONLY IF every pivot `D r > 0`! -/
theorem ldlt_strictlyPosDef_iff {N : Nat} {M L : Mat} {D : Vec}
    (h : IsLDLTAlg N M L D) :
    StrictlyPosDef N M ↔ (∀ r, r < N → zero <ᵈ D r) := by
  constructor
  · intro hpd r hr
    have hnz := backSubVec_nonzero h.unitLower hr
    have hpos := hpd (backSubVec N L r) hnz
    exact dlt_congr (deq_refl _) (backSubVec_quadForm h hr) hpos
  · intro hD v hv
    obtain ⟨r0, hr0, hne⟩ := unitLower_transpose_injective h.unitLower hv
    have hsum_pos : zero <ᵈ dsum N (fun r => D r * (matTVec N L v r * matTVec N L v r)) := by
      refine dsum_pos_of_exists_pos
        (fun r hr => mul_nonneg_of_nonneg (dle_of_dlt (hD r hr)) (sq_nonneg _))
        ⟨r0, hr0, mul_pos_of_pos (hD r0 hr0) (sq_pos_of_ne_zero hne)⟩
    exact dlt_congr (deq_refl _) (deq_symm (ldlt_quadForm_eq h v)) hsum_pos

theorem ldltPos_strictlyPosDef {N : Nat} {M L : Mat} {D : Vec}
    (h : IsLDLTPos N M L D) : StrictlyPosDef N M :=
  (ldlt_strictlyPosDef_iff h.toIsLDLTAlg).mpr h.pivotsPos

/-- Quantitative quadratic-form lower bound from a uniform pivot lower bound `δ`. -/
theorem ldlt_quadForm_lower_bound {N : Nat} {M L : Mat} {D : Vec} {δ : Dyad}
    (h : IsLDLTAlg N M L D) (hδ : ∀ r, r < N → δ ≤ᵈ D r) (v : Vec) :
    δ * dsum N (fun r => matTVec N L v r * matTVec N L v r) ≤ᵈ quadForm N M v := by
  have h1 : dsum N (fun r => δ * (matTVec N L v r * matTVec N L v r)) ≤ᵈ
            dsum N (fun r => D r * (matTVec N L v r * matTVec N L v r)) :=
    dsum_dle_dsum (fun r hr => mul_dle_mul_of_nonneg_right (sq_nonneg _) (hδ r hr))
  exact dle_congr (dsum_mul_left N δ _) (deq_symm (ldlt_quadForm_eq h v)) h1

/-- **ARBITRARY `n x n` LEADING PRINCIPAL SUBMATRIX RESTRICTION THEOREM**:
    If `M` has an exact dyadic `LDL^T` on `[0, N)` and `n ≤ N`, the exact same `(L, D)`
    certifies `M` on `[0, n)` (lifting `2^k x 2^k` proofs to ALL `n : Nat`!). -/
theorem ldlt_prefix_restrict {N n : Nat} {M L : Mat} {D : Vec}
    (h : IsLDLTAlg N M L D) (hle : n ≤ N) : IsLDLTAlg n M L D := by
  refine ⟨⟨fun i hi => h.unitLower.1 i (Nat.lt_of_lt_of_le hi hle),
           fun i j hi hj hij => h.unitLower.2 i j (Nat.lt_of_lt_of_le hi hle)
             (Nat.lt_of_lt_of_le hj hle) hij⟩, ?_⟩
  intro i j hi hj
  have hfac := h.factor i j (Nat.lt_of_lt_of_le hi hle) (Nat.lt_of_lt_of_le hj hle)
  have htrunc : dsum N (fun r => L i r * D r * L j r) ≈ dsum n (fun r => L i r * D r * L j r) := by
    refine dsum_prefix_of_zero_tail hle (fun r hr1 hr2 => ?_)
    have hir : i < r := by omega
    have hL0 : L i r ≈ zero := h.unitLower.2 i r (Nat.lt_of_lt_of_le hi hle) hr2 hir
    calc
      L i r * D r * L j r
          ≈ zero * D r * L j r := mul_congr (mul_congr hL0 (deq_refl _)) (deq_refl _)
      _ ≈ zero * L j r := mul_congr (zero_mul _) (deq_refl _)
      _ ≈ zero := zero_mul _
  exact deq_trans hfac htrunc

-- ============================================================================
-- LAYER 3: REUSABLE RECURSIVE BLOCK-SCHUR LDL^T AUTOMATON ENGINE
-- ============================================================================

/-- **SINGLE-STEP BLOCK-SCHUR `LDL^T` LIFTING THEOREM** (arbitrary dyadic coupling `E`!). -/
theorem block_schur_ldlt_step {N : Nat} {M A S E L_A L_S : Mat} {D_A D_S : Vec}
    (hA : IsLDLTAlg N A L_A D_A)
    (hS : IsLDLTAlg N S L_S D_S)
    (hTL : ∀ i j, i < N → j < N → M i j ≈ A i j)
    (hBL : ∀ i j, i < N → j < N → M (N + i) j ≈ matMul N E A i j)
    (hTR : ∀ i j, i < N → j < N → M i (N + j) ≈ matMul N E A j i)
    (hBR : ∀ i j, i < N → j < N →
      M (N + i) (N + j) ≈ S i j + matMulT N (matMul N E A) E i j) :
    IsLDLTAlg (2 * N) M (blockL N E L_A L_S) (blockD N D_A D_S) := by
  have h2N : 2 * N = N + N := by omega
  constructor
  · -- Unit lower-triangularity of blockL
    refine ⟨fun i hi => ?_, fun i j hi hj hij => ?_⟩
    · by_cases hiN : i < N
      · unfold blockL; simp [hiN]; exact hA.unitLower.1 i hiN
      · unfold blockL; simp [hiN]; exact hS.unitLower.1 (i - N) (by omega)
    · by_cases hiN : i < N
      · by_cases hjN : j < N
        · unfold blockL; simp [hiN, hjN]; exact hA.unitLower.2 i j hiN hjN hij
        · unfold blockL; simp [hiN, hjN]; exact deq_refl _
      · have hjN : ¬ (j < N) := by omega
        unfold blockL; simp [hiN, hjN]
        exact hS.unitLower.2 (i - N) (j - N) (by omega) (by omega) (by omega)
  · -- Factorization across all 4 blocks
    intro i j hi hj
    rw [h2N]
    -- Helper: matMul N (E * L_A) * D_A * L_A^T = E * A
    have hELA_LA : ∀ u v, u < N → v < N →
        dsum N (fun r => matMul N E L_A u r * D_A r * L_A v r) ≈ matMul N E A u v := by
      intro u v hu hv
      calc
        dsum N (fun r => matMul N E L_A u r * D_A r * L_A v r)
            ≈ dsum N (fun r => dsum N (fun t => E u t * L_A t r * D_A r * L_A v r)) := by
              refine dsum_congr (fun r _ => ?_)
              calc
                dsum N (fun t => E u t * L_A t r) * D_A r * L_A v r
                    ≈ dsum N (fun t => E u t * L_A t r * D_A r) * L_A v r :=
                      mul_congr (deq_symm (dsum_mul_right N _ (D_A r))) (deq_refl _)
                _ ≈ dsum N (fun t => E u t * L_A t r * D_A r * L_A v r) :=
                      deq_symm (dsum_mul_right N _ (L_A v r))
        _ ≈ dsum N (fun t => dsum N (fun r => E u t * L_A t r * D_A r * L_A v r)) :=
              dsum_swap N N _
        _ ≈ dsum N (fun t => E u t * dsum N (fun r => L_A t r * D_A r * L_A v r)) := by
              refine dsum_congr (fun t _ => ?_)
              have hre : dsum N (fun r => E u t * L_A t r * D_A r * L_A v r) ≈
                         dsum N (fun r => E u t * (L_A t r * D_A r * L_A v r)) :=
                dsum_congr (fun r _ => by
                  calc
                    E u t * L_A t r * D_A r * L_A v r
                        ≈ E u t * (L_A t r * D_A r) * L_A v r :=
                          mul_congr (mul_assoc _ _ _) (deq_refl _)
                    _ ≈ E u t * (L_A t r * D_A r * L_A v r) := mul_assoc _ _ _)
              exact deq_trans hre (dsum_mul_left N (E u t) _)
        _ ≈ dsum N (fun t => E u t * A t v) :=
              dsum_congr (fun t ht => mul_congr (deq_refl _) (deq_symm (hA.factor t v ht hv)))
    -- Helper: (E * L_A) * D_A * (E * L_A)^T = (E * A) * E^T
    have hELA_ELA : ∀ u v, u < N → v < N →
        dsum N (fun r => matMul N E L_A u r * D_A r * matMul N E L_A v r) ≈
        matMulT N (matMul N E A) E u v := by
      intro u v hu hv
      calc
        dsum N (fun r => matMul N E L_A u r * D_A r * matMul N E L_A v r)
            ≈ dsum N (fun r => dsum N (fun s => (matMul N E L_A u r * D_A r) * (E v s * L_A s r))) :=
              dsum_congr (fun r _ => deq_symm (dsum_mul_left N _ _))
        _ ≈ dsum N (fun s => dsum N (fun r => (matMul N E L_A u r * D_A r) * (E v s * L_A s r))) :=
              dsum_swap N N _
        _ ≈ dsum N (fun s => dsum N (fun r => matMul N E L_A u r * D_A r * L_A s r) * E v s) := by
              refine dsum_congr (fun s _ => ?_)
              have hre : dsum N (fun r => (matMul N E L_A u r * D_A r) * (E v s * L_A s r)) ≈
                         dsum N (fun r => (matMul N E L_A u r * D_A r * L_A s r) * E v s) :=
                dsum_congr (fun r _ => by
                  calc
                    (matMul N E L_A u r * D_A r) * (E v s * L_A s r)
                        ≈ (matMul N E L_A u r * D_A r) * (L_A s r * E v s) :=
                          mul_congr (deq_refl _) (mul_comm _ _)
                    _ ≈ (matMul N E L_A u r * D_A r * L_A s r) * E v s :=
                          deq_symm (mul_assoc _ _ _))
              exact deq_trans hre (dsum_mul_right N _ (E v s))
        _ ≈ dsum N (fun s => matMul N E A u s * E v s) :=
              dsum_congr (fun s hs => mul_congr (hELA_LA u s hu hs) (deq_refl _))
    -- Now split dsum (N + N) into first N and second N
    refine deq_trans ?_ (deq_symm (dsum_split N N _))
    by_cases hiN : i < N
    · by_cases hjN : j < N
      · -- TL block: i < N, j < N
        have hfirst : dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) ≈
                      dsum N (fun r => L_A i r * D_A r * L_A j r) :=
          dsum_congr (fun r hr => by unfold blockL blockD; simp [hiN, hjN, hr]; exact deq_refl _)
        have hsecond : dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) ≈ zero :=
          dsum_eq_zero (fun r _ => by
            have hge : ¬ (N + r < N) := by omega
            unfold blockL blockD; simp [hiN, hjN, hge]
            exact deq_trans (mul_congr (zero_mul _) (deq_refl _)) (zero_mul _))
        calc
          M i j ≈ A i j := hTL i j hiN hjN
          _ ≈ dsum N (fun r => L_A i r * D_A r * L_A j r) := hA.factor i j hiN hjN
          _ ≈ dsum N (fun r => L_A i r * D_A r * L_A j r) + zero := deq_symm (add_zero _)
          _ ≈ dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) +
              dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) :=
              add_congr (deq_symm hfirst) (deq_symm hsecond)
      · -- TR block: i < N, j = N + j'
        let j' := j - N
        have hj'lt : j' < N := by omega
        have hj_eq : j = N + j' := by omega
        have hfirst : dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) ≈
                      dsum N (fun r => matMul N E L_A j' r * D_A r * L_A i r) :=
          dsum_congr (fun r hr => by
            unfold blockL blockD; simp [hiN, hjN, hr]
            show L_A i r * D_A r * matMul N E L_A j' r ≈ matMul N E L_A j' r * D_A r * L_A i r
            calc
              L_A i r * D_A r * matMul N E L_A j' r
                  ≈ matMul N E L_A j' r * (L_A i r * D_A r) := mul_comm _ _
              _ ≈ matMul N E L_A j' r * (D_A r * L_A i r) := mul_congr (deq_refl _) (mul_comm _ _)
              _ ≈ matMul N E L_A j' r * D_A r * L_A i r := deq_symm (mul_assoc _ _ _))
        have hsecond : dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) ≈ zero :=
          dsum_eq_zero (fun r _ => by
            have hge : ¬ (N + r < N) := by omega
            unfold blockL blockD; simp [hiN, hjN, hge]
            exact deq_trans (mul_congr (zero_mul _) (deq_refl _)) (zero_mul _))
        calc
          M i j = M i (N + j') := by rw [← hj_eq]
          _ ≈ matMul N E A j' i := hTR i j' hiN hj'lt
          _ ≈ dsum N (fun r => matMul N E L_A j' r * D_A r * L_A i r) := deq_symm (hELA_LA j' i hj'lt hiN)
          _ ≈ dsum N (fun r => matMul N E L_A j' r * D_A r * L_A i r) + zero := deq_symm (add_zero _)
          _ ≈ dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) +
              dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) :=
              add_congr (deq_symm hfirst) (deq_symm hsecond)
    · let i' := i - N
      have hi'lt : i' < N := by omega
      have hi_eq : i = N + i' := by omega
      by_cases hjN : j < N
      · -- BL block: i = N + i', j < N
        have hfirst : dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) ≈
                      dsum N (fun r => matMul N E L_A i' r * D_A r * L_A j r) :=
          dsum_congr (fun r hr => by unfold blockL blockD; simp [hiN, hjN, hr]; exact deq_refl _)
        have hsecond : dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) ≈ zero :=
          dsum_eq_zero (fun r _ => by
            have hge : ¬ (N + r < N) := by omega
            unfold blockL blockD; simp [hiN, hjN, hge]
            exact mul_zero _)
        calc
          M i j = M (N + i') j := by rw [← hi_eq]
          _ ≈ matMul N E A i' j := hBL i' j hi'lt hjN
          _ ≈ dsum N (fun r => matMul N E L_A i' r * D_A r * L_A j r) := deq_symm (hELA_LA i' j hi'lt hjN)
          _ ≈ dsum N (fun r => matMul N E L_A i' r * D_A r * L_A j r) + zero := deq_symm (add_zero _)
          _ ≈ dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) +
              dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) :=
              add_congr (deq_symm hfirst) (deq_symm hsecond)
      · -- BR block: i = N + i', j = N + j'
        let j' := j - N
        have hj'lt : j' < N := by omega
        have hj_eq : j = N + j' := by omega
        have hfirst : dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) ≈
                      dsum N (fun r => matMul N E L_A i' r * D_A r * matMul N E L_A j' r) :=
          dsum_congr (fun r hr => by unfold blockL blockD; simp [hiN, hjN, hr]; exact deq_refl _)
        have hsecond : dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) ≈
                       dsum N (fun r => L_S i' r * D_S r * L_S j' r) :=
          dsum_congr (fun r _ => by
            have hge : ¬ (N + r < N) := by omega
            have hsub : N + r - N = r := by omega
            unfold blockL blockD; simp [hiN, hjN, hge, hsub]; exact deq_refl _)
        calc
          M i j = M (N + i') (N + j') := by rw [← hi_eq, ← hj_eq]
          _ ≈ S i' j' + matMulT N (matMul N E A) E i' j' := hBR i' j' hi'lt hj'lt
          _ ≈ matMulT N (matMul N E A) E i' j' + S i' j' := add_comm _ _
          _ ≈ dsum N (fun r => matMul N E L_A i' r * D_A r * matMul N E L_A j' r) +
              dsum N (fun r => L_S i' r * D_S r * L_S j' r) :=
              add_congr (deq_symm (hELA_ELA i' j' hi'lt hj'lt)) (hS.factor i' j' hi'lt hj'lt)
          _ ≈ dsum N (fun r => blockL N E L_A L_S i r * blockD N D_A D_S r * blockL N E L_A L_S j r) +
              dsum N (fun r => blockL N E L_A L_S i (N + r) * blockD N D_A D_S (N + r) * blockL N E L_A L_S j (N + r)) :=
              add_congr (deq_symm hfirst) (deq_symm hsecond)

/-- **MASTER INFINITE LIFTING THEOREM**:
    Every `SchurSystem` produces a kernel-verified exact `Z[1/2]` `LDL^T` factorization
    at EVERY scale `k : Nat` (`2^k x 2^k`) and EVERY state `σ`! -/
theorem schurSystem_ldlt {State : Type} (S : SchurSystem State) :
    ∀ k σ, IsLDLTAlg (2 ^ k) (S.mat σ k) (schurL S σ k) (schurD S σ k) := by
  intro k
  induction k with
  | zero =>
    intro σ
    refine ⟨⟨fun i _ => by simp [schurL]; exact deq_refl _, fun i j hi hj hij => by omega⟩, ?_⟩
    intro i j hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    show S.mat σ 0 0 0 ≈ zero + (one * S.mat σ 0 0 0 * one)
    calc
      S.mat σ 0 0 0 ≈ S.mat σ 0 0 0 * one := deq_symm (mul_one _)
      _ ≈ one * S.mat σ 0 0 0 * one := mul_congr (deq_symm (one_mul _)) (deq_refl _)
      _ ≈ zero + (one * S.mat σ 0 0 0 * one) := deq_symm (zero_add _)
  | succ k ih =>
    intro σ
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    exact block_schur_ldlt_step (ih (S.leftState σ k)) (ih (S.rightState σ k))
      (S.tl_eq σ k) (S.bl_eq σ k) (S.tr_eq σ k) (S.br_eq σ k)

/-- **MASTER PIVOT-AUTOMATON LOWER BOUND LIFTER**:
    Any dyadic state-invariant lower bound `lb σ k` preserved by `(leftState, rightState)`
    lifts automatically to a lower bound on EVERY pivot `r < 2^k` for ALL `k : Nat`! -/
theorem schurSystem_pivot_lb {State : Type} (S : SchurSystem State)
    (lb : State → Nat → Dyad)
    (hbase : ∀ σ, lb σ 0 ≤ᵈ S.mat σ 0 0 0)
    (hleft : ∀ σ k, lb σ (k + 1) ≤ᵈ lb (S.leftState σ k) k)
    (hright : ∀ σ k, lb σ (k + 1) ≤ᵈ lb (S.rightState σ k) k) :
    ∀ k σ r, r < 2 ^ k → lb σ k ≤ᵈ schurD S σ k r := by
  intro k
  induction k with
  | zero =>
    intro σ r _
    exact hbase σ
  | succ k ih =>
    intro σ r hr
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    unfold schurD blockD
    by_cases hrk : r < 2 ^ k
    · simp only [hrk, ↓reduceIte]
      exact dle_trans (hleft σ k) (ih (S.leftState σ k) r hrk)
    · simp only [hrk, ↓reduceIte]
      exact dle_trans (hright σ k) (ih (S.rightState σ k) (r - 2 ^ k) (by omega))

/-- Strict-positivity specialization of the pivot-automaton lifter. -/
theorem schurSystem_strictlyPosDef_of_lb {State : Type} (S : SchurSystem State)
    (lb : State → Nat → Dyad)
    (hbase : ∀ σ, lb σ 0 ≤ᵈ S.mat σ 0 0 0)
    (hleft : ∀ σ k, lb σ (k + 1) ≤ᵈ lb (S.leftState σ k) k)
    (hright : ∀ σ k, lb σ (k + 1) ≤ᵈ lb (S.rightState σ k) k)
    {σ : State} {k : Nat} (hpos : zero <ᵈ lb σ k) :
    StrictlyPosDef (2 ^ k) (S.mat σ k) := by
  refine (ldlt_strictlyPosDef_iff (schurSystem_ldlt S k σ)).mpr (fun r hr => ?_)
  exact dlt_of_dlt_of_dle hpos (schurSystem_pivot_lb S lb hbase hleft hright k σ r hr)

/-- **NESTED ARBITRARY `n x n` INFINITE STREAM LIFTER**:
    If `M` agrees with `S.mat σ k` on `[0, 2^k)` for all `k`, then `M` has an exact `Z[1/2]` `LDL^T`
    at EVERY `n : Nat` (not just powers of 2!), with exact `↔` PD characterization! -/
theorem schurSystem_nested_ldlt {State : Type} (S : SchurSystem State) (σ : State) (M : Mat)
    (hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k → M i j ≈ S.mat σ k i j)
    (n : Nat) :
    IsLDLTAlg n M (schurL S σ n) (schurD S σ n) := by
  have hle : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  have hres := ldlt_prefix_restrict (schurSystem_ldlt S n σ) hle
  refine ⟨hres.unitLower, fun i j hi hj => ?_⟩
  exact deq_trans (hagree n i j (Nat.lt_of_lt_of_le hi hle) (Nat.lt_of_lt_of_le hj hle))
    (hres.factor i j hi hj)

theorem schurSystem_nested_iff {State : Type} (S : SchurSystem State) (σ : State) (M : Mat)
    (hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k → M i j ≈ S.mat σ k i j)
    (n : Nat) :
    StrictlyPosDef n M ↔ (∀ r, r < n → zero <ᵈ schurD S σ n r) :=
  ldlt_strictlyPosDef_iff (schurSystem_nested_ldlt S σ M hagree n)

-- Helpful coupling evaluation lemmas (reusable across scalar, reflection, and rank-1 families!)

theorem popcount_zero : popcount 0 = 0 := rfl

theorem phi2From_succ_shift (b n : Nat) :
    phi2From (b + 1) n ≈ pow2Neg 1 * phi2From b n := by
  induction n using Nat.strongRecOn generalizing b with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; rw [phi2From_zero, phi2From_zero]; exact deq_symm (mul_zero _)
    · have hdiv : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih (n / 2) hdiv (b + 1)
      have hterm : (if n % 2 = 1 then pow2Neg (b + 1 + 1) else zero) ≈
                   pow2Neg 1 * (if n % 2 = 1 then pow2Neg (b + 1) else zero) := by
        by_cases hm : n % 2 = 1
        · simp only [hm, ↓reduceIte]; exact pow2Neg_succ (b + 1)
        · simp only [hm, ↓reduceIte]; exact deq_symm (mul_zero _)
      calc
        phi2From (b + 1) n
            ≈ (if n % 2 = 1 then pow2Neg (b + 1 + 1) else zero) + phi2From (b + 1 + 1) (n / 2) :=
              phi2From_unfold (b + 1) n
        _ ≈ pow2Neg 1 * (if n % 2 = 1 then pow2Neg (b + 1) else zero) +
            pow2Neg 1 * phi2From (b + 1) (n / 2) := add_congr hterm hrec
        _ ≈ pow2Neg 1 * ((if n % 2 = 1 then pow2Neg (b + 1) else zero) + phi2From (b + 1) (n / 2)) :=
              deq_symm (mul_add _ _ _)
        _ ≈ pow2Neg 1 * phi2From b n := mul_congr (deq_refl _) (deq_symm (phi2From_unfold b n))

theorem phi2_nonneg (n : Nat) : zero ≤ᵈ phi2 n := by
  suffices ∀ b n, zero ≤ᵈ phi2From b n from this 0 n
  intro b n
  induction n using Nat.strongRecOn generalizing b with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; rw [phi2From_zero]; exact dle_refl _
    · have hdiv : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have hterm : zero ≤ᵈ (if n % 2 = 1 then pow2Neg (b + 1) else zero) := by
        by_cases hm : n % 2 = 1
        · simp only [hm, ↓reduceIte]; exact pow2Neg_nonneg _
        · simp only [hm, ↓reduceIte]; exact dle_refl _
      have hsum : zero ≤ᵈ (if n % 2 = 1 then pow2Neg (b + 1) else zero) + phi2From (b + 1) (n / 2) :=
        dle_congr (add_zero zero) (deq_refl _) (add_dle_add hterm (ih (n / 2) hdiv (b + 1)))
      exact dle_congr (deq_refl _) (deq_symm (phi2From_unfold b n)) hsum

theorem phi2_lt_one (n : Nat) : phi2 n <ᵈ one := by
  have hgen : ∀ k x, x < 2 ^ k → phi2 x + pow2Neg k ≤ᵈ one := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have hx0 : x = 0 := by omega
      subst hx0
      show phi2From 0 0 + pow2Neg 0 ≤ᵈ one
      rw [phi2From_zero]
      exact dle_of_deq (zero_add one)
    | succ k ih =>
      intro x hx
      by_cases hxk : x < 2 ^ k
      · have hle : pow2Neg (k + 1) ≤ᵈ pow2Neg k := pow2Neg_antitone (by omega)
        exact dle_trans (add_dle_add (dle_refl _) hle) (ih x hxk)
      · let y := x - 2 ^ k
        have hy : y < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
        have hxy : x = 2 ^ k + y := by omega
        rw [hxy]
        calc
          phi2 (2 ^ k + y) + pow2Neg (k + 1)
              ≈ (phi2 y + pow2Neg (k + 1)) + pow2Neg (k + 1) :=
                add_congr (phi2_add_two_pow hy) (deq_refl _)
          _ ≈ phi2 y + (pow2Neg (k + 1) + pow2Neg (k + 1)) := add_assoc _ _ _
          _ ≈ phi2 y + pow2Neg k := add_congr (deq_refl _) (pow2Neg_half_add k)
          _ ≤ᵈ one := ih y hy
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hle := hgen n n hlt
  have hpos : zero <ᵈ pow2Neg n := pow2Neg_pos n
  calc
    phi2 n ≈ phi2 n + zero := deq_symm (add_zero _)
    _ <ᵈ phi2 n + pow2Neg n := add_dlt_add_of_dle_of_dlt (dle_refl _) hpos
    _ ≤ᵈ one := hle

theorem phi2_two_pow_sub_one (k : Nat) : phi2 (2 ^ k - 1) ≈ one - pow2Neg k := by
  induction k with
  | zero =>
    show phi2From 0 0 ≈ one - pow2Neg 0
    rw [phi2From_zero]
    exact deq_symm (sub_self one)
  | succ k ih =>
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    have hpow : 2 ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by rw [Nat.pow_succ]; omega
    have hlt : 2 ^ k - 1 < 2 ^ k := by omega
    have h1 : (one - pow2Neg (k + 1)) - pow2Neg (k + 1) ≈ one - pow2Neg k :=
      deq_trans (sub_sub_eq_sub_add _ _ _) (sub_congr (deq_refl _) (pow2Neg_half_add k))
    have hdiff : (one - pow2Neg k) + pow2Neg (k + 1) ≈ one - pow2Neg (k + 1) :=
      deq_trans (add_congr (deq_symm h1) (deq_refl _)) (sub_add_cancel _ _)
    rw [hpow]
    exact deq_trans (phi2_add_two_pow hlt) (deq_trans (add_congr ih (deq_refl _)) hdiff)

-- ============================================================================
-- FAMILY I: BITWISE VAN DER CORPUT-HAMMING KERNEL (SCALAR COUPLING E_k = 1/2 I)
-- K(x, y) = 2^(-popcount(x ^^^ y)) * (c - beta * phi2(x &&& y))
-- EXACT IFF CRITICAL THRESHOLD: ∀ n, StrictlyPosDef n K ↔ 4*beta ≤ 3*c !
-- ============================================================================

theorem schurD_vdcHamming_eq :
    ∀ k c β r, r < 2 ^ k →
      schurD vdcHammingSystem (c, β) k r ≈ vdcHammingPivot c β r := by
  intro k
  induction k with
  | zero =>
    intro c β r hr
    have hr0 : r = 0 := by omega
    subst hr0
    show pow2Neg (popcount (0 ^^^ 0)) * (c - β * phi2 (0 &&& 0)) ≈ c
    have h0 : popcount (0 ^^^ 0) = 0 := by decide
    have ha : 0 &&& 0 = 0 := by decide
    rw [h0, ha, phi2, phi2From_zero]
    calc
      pow2Neg 0 * (c - β * zero)
          ≈ one * (c - zero) := mul_congr pow2Neg_zero (sub_congr (deq_refl _) (mul_zero β))
      _ ≈ c - zero := one_mul _
      _ ≈ c := deq_trans (add_congr (deq_refl c) neg_zero) (add_zero c)
  | succ k ih =>
    intro c β r hr
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    unfold schurD blockD
    by_cases hrk : r < 2 ^ k
    · simp only [hrk, ↓reduceIte]
      exact ih c β r hrk
    · simp only [hrk, ↓reduceIte]
      let u := r - 2 ^ k
      have hu : u < 2 ^ k := by omega
      have hru : r = 2 ^ k + u := by omega
      have hrec := ih (⟨3, 2⟩ * c - β * pow2Neg (k + 1)) (⟨3, 2⟩ * β) u hu
      have hr_ne : r ≠ 0 := by
        have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
        omega
      by_cases hu0 : u = 0
      · have hr_eq : r = 2 ^ k := by omega
        have hpop : popcount (2 ^ k) = 1 := by
          have h := popcount_add_two_pow (k := k) (x := 0) (Nat.one_le_pow k 2 (by omega))
          simpa [popcount_zero] using h
        have hphi : phi2 (2 ^ k) ≈ pow2Neg (k + 1) := by
          have h := phi2_add_two_pow (k := k) (x := 0) (Nat.one_le_pow k 2 (by omega))
          simpa [phi2, phi2From_zero] using deq_trans h (zero_add _)
        have h1 : vdcHammingPivot (⟨3, 2⟩ * c - β * pow2Neg (k + 1)) (⟨3, 2⟩ * β) u =
                  ⟨3, 2⟩ * c - β * pow2Neg (k + 1) := by rw [hu0]; rfl
        have h2 : vdcHammingPivot c β r ≈ ⟨3, 2⟩ * c - β * pow2Neg (k + 1) := by
          unfold vdcHammingPivot
          simp only [hr_ne, ↓reduceIte]
          rw [hr_eq, hpop]
          show one * (⟨3, 2⟩ * c - β * phi2 (2 ^ k)) ≈ ⟨3, 2⟩ * c - β * pow2Neg (k + 1)
          exact deq_trans (one_mul _) (sub_congr (deq_refl _) (mul_congr (deq_refl _) hphi))
        exact deq_trans hrec (deq_trans (by rw [h1]; exact deq_refl _) (deq_symm h2))
      · have hpop_pos : 1 ≤ popcount u := by
          by_cases hpu : popcount u = 0
          · exfalso
            have : ∀ n, popcount n = 0 → n = 0 := by
              intro n
              induction n using Nat.strongRecOn with
              | ind n ihn =>
                intro hp0
                by_cases hn0 : n = 0
                · exact hn0
                · rw [popcount_eq_mod_add_div] at hp0
                  have hm : n % 2 = 0 := by omega
                  have hd : n / 2 = 0 := ihn (n / 2) (Nat.div_lt_self (by omega) (by omega)) (by omega)
                  omega
            exact hu0 (this u hpu)
          · omega
        have hpop_r : popcount r = 1 + popcount u := by
          rw [hru]; exact popcount_add_two_pow hu
        have hsub : popcount r - 1 = (popcount u - 1) + 1 := by omega
        have hpow34 : Dyad.pow ⟨3, 2⟩ (popcount r - 1) ≈
                      Dyad.pow ⟨3, 2⟩ (popcount u - 1) * ⟨3, 2⟩ := by
          rw [hsub]
          have hstep : ∀ a m, Dyad.pow a (m + 1) ≈ Dyad.pow a m * a := by
            intro a m
            induction m with
            | zero => exact deq_trans (mul_one a) (deq_symm (one_mul a))
            | succ t iht =>
              show a * Dyad.pow a (t + 1) ≈ (a * Dyad.pow a t) * a
              exact deq_trans (mul_congr (deq_refl a) iht) (deq_symm (mul_assoc _ _ _))
          exact hstep ⟨3, 2⟩ (popcount u - 1)
        have hphi_r : phi2 r ≈ phi2 u + pow2Neg (k + 1) := by
          rw [hru]; exact phi2_add_two_pow hu
        have hinner : ⟨3, 2⟩ * (⟨3, 2⟩ * c - β * pow2Neg (k + 1)) - (⟨3, 2⟩ * β) * phi2 u ≈
                      ⟨3, 2⟩ * (⟨3, 2⟩ * c - β * phi2 r) := by
          let q34 : Dyad := ⟨3, 2⟩
          let a1 := q34 * c
          let b1 := β * pow2Neg (k + 1)
          let b2 := β * phi2 u
          have s1 := sub_congr (mul_sub q34 a1 b1) (mul_assoc q34 β (phi2 u))
          have s2 := sub_sub_eq_sub_add (q34 * a1) (q34 * b1) (q34 * b2)
          have s3 := sub_congr (deq_refl (q34 * a1)) (deq_symm (mul_add q34 b1 b2))
          have s4 := deq_symm (mul_sub q34 a1 (b1 + b2))
          have s5 : b1 + b2 ≈ β * phi2 r :=
            deq_trans (add_comm b1 b2)
              (deq_trans (deq_symm (mul_add β (phi2 u) (pow2Neg (k + 1))))
                (mul_congr (deq_refl β) (deq_symm hphi_r)))
          have s6 := mul_congr (deq_refl q34) (sub_congr (deq_refl a1) s5)
          exact deq_trans s1 (deq_trans s2 (deq_trans s3 (deq_trans s4 s6)))
        refine deq_trans hrec ?_
        unfold vdcHammingPivot
        simp only [hu0, hr_ne, ↓reduceIte]
        calc
          Dyad.pow ⟨3, 2⟩ (popcount u - 1) *
            (⟨3, 2⟩ * (⟨3, 2⟩ * c - β * pow2Neg (k + 1)) - (⟨3, 2⟩ * β) * phi2 u)
              ≈ Dyad.pow ⟨3, 2⟩ (popcount u - 1) * (⟨3, 2⟩ * (⟨3, 2⟩ * c - β * phi2 r)) :=
                mul_congr (deq_refl _) hinner
          _ ≈ (Dyad.pow ⟨3, 2⟩ (popcount u - 1) * ⟨3, 2⟩) * (⟨3, 2⟩ * c - β * phi2 r) :=
                deq_symm (mul_assoc _ _ _)
          _ ≈ Dyad.pow ⟨3, 2⟩ (popcount r - 1) * (⟨3, 2⟩ * c - β * phi2 r) :=
                mul_congr (deq_symm hpow34) (deq_refl _)

theorem dyad_pow_pos {a : Dyad} (ha : zero <ᵈ a) (m : Nat) : zero <ᵈ Dyad.pow a m := by
  induction m with
  | zero => show zero <ᵈ one; decide
  | succ k ih => exact mul_pos_of_pos ha ih

/-- **THEOREM 1 (EXACT SHARP CRITICAL THRESHOLD FOR FAMILY I, ALL `n : Nat`)**:
    For any `β > 0` and `c` in `Z[1/2]`, the Bitwise van der Corput-Hamming kernel
    `K_{c,β}(x, y) = 2^(-pop(x ^^^ y)) * (c - β * φ_2(x &&& y))`
    is strictly positive definite on `[0, n)` for ALL `n : Nat`
    **IF AND ONLY IF** `4 * β ≤ 3 * c`! -/
theorem vdcHamming_strictlyPosDef_all_n_iff {c β : Dyad} (hβ : zero <ᵈ β) :
    (∀ n : Nat, StrictlyPosDef n (vdcHammingMat c β)) ↔
    ofInt 4 * β ≤ᵈ ofInt 3 * c := by
  have hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k →
      vdcHammingMat c β i j ≈ vdcHammingSystem.mat (c, β) k i j :=
    fun _ _ _ _ _ => deq_refl _
  constructor
  · intro hall
    apply dle_of_not_dlt
    intro hlt
    let δ := ofInt 4 * β - ofInt 3 * c
    have hδ : zero <ᵈ δ := (sub_pos_iff _ _).mpr hlt
    have h4β : zero ≤ᵈ ofInt 4 * β :=
      dle_of_dlt (mul_pos_of_pos (by decide : zero <ᵈ ofInt 4) hβ)
    obtain ⟨k0, hk0⟩ := exists_pow2Neg_le hδ h4β
    let k := k0 + 1
    have hk : ofInt 4 * β * pow2Neg k ≤ᵈ δ :=
      dle_trans (mul_dle_mul_of_nonneg_left h4β (pow2Neg_antitone (by omega))) hk0
    let r := 2 ^ k - 1
    have hr_lt : r < 2 ^ k := by
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      omega
    have hr_ne : r ≠ 0 := by
      have hp : 2 ≤ 2 ^ k := by
        show 2 ≤ 2 ^ (k0 + 1)
        rw [Nat.pow_succ]
        have h1 : 1 ≤ 2 ^ k0 := Nat.one_le_pow k0 2 (by omega)
        omega
      omega
    have hpd := (schurSystem_nested_iff vdcHammingSystem (c, β) (vdcHammingMat c β) hagree (2 ^ k)).mp
      (hall (2 ^ k)) r hr_lt
    have h2k_le : 2 ^ k ≤ 2 ^ (2 ^ k) := Nat.le_of_lt Nat.lt_two_pow_self
    have hD_eq : schurD vdcHammingSystem (c, β) (2 ^ k) r ≈ vdcHammingPivot c β r :=
      schurD_vdcHamming_eq (2 ^ k) c β r (Nat.lt_of_lt_of_le hr_lt h2k_le)
    have hpiv_pos : zero <ᵈ vdcHammingPivot c β r :=
      dlt_congr (deq_refl _) hD_eq hpd
    unfold vdcHammingPivot at hpiv_pos
    simp only [hr_ne, ↓reduceIte] at hpiv_pos
    have hfactor_le : ⟨3, 2⟩ * c - β * phi2 r ≤ᵈ zero := by
      have h4eq : ofInt 4 * (⟨3, 2⟩ * c - β * phi2 r) ≈
                  ofInt 4 * β * pow2Neg k - δ := by
        have h43 : ofInt 4 * (⟨3, 2⟩ : Dyad) ≈ ofInt 3 := by decide
        have hphi := phi2_two_pow_sub_one k
        have hsub3 : ∀ x y z : Dyad, x - (y - z) ≈ z - (y - x) := by
          intro x y z
          calc
            x - (y - z)
                ≈ x + (-y + -(-z)) := add_congr (deq_refl _) (neg_add y (-z))
            _ ≈ x + (-y + z) := add_congr (deq_refl _) (add_congr (deq_refl _) (neg_neg z))
            _ ≈ x + (z + -y) := add_congr (deq_refl _) (add_comm _ _)
            _ ≈ (x + z) + -y := deq_symm (add_assoc _ _ _)
            _ ≈ (z + x) + -y := add_congr (add_comm _ _) (deq_refl _)
            _ ≈ z + (x + -y) := add_assoc _ _ _
            _ ≈ z + (-y + x) := add_congr (deq_refl _) (add_comm _ _)
            _ ≈ z + (-y + -(-x)) := add_congr (deq_refl _) (add_congr (deq_refl _) (deq_symm (neg_neg x)))
            _ ≈ z + -(y + -x) := add_congr (deq_refl _) (deq_symm (neg_add y (-x)))
        calc
          ofInt 4 * (⟨3, 2⟩ * c - β * phi2 r)
              ≈ ofInt 4 * (⟨3, 2⟩ * c) - ofInt 4 * (β * (one - pow2Neg k)) :=
                deq_trans (mul_sub _ _ _) (sub_congr (deq_refl _) (mul_congr (deq_refl _) (mul_congr (deq_refl _) hphi)))
          _ ≈ (ofInt 4 * ⟨3, 2⟩) * c - (ofInt 4 * β) * (one - pow2Neg k) :=
                sub_congr (deq_symm (mul_assoc _ _ _)) (deq_symm (mul_assoc _ _ _))
          _ ≈ ofInt 3 * c - (ofInt 4 * β * one - ofInt 4 * β * pow2Neg k) :=
                sub_congr (mul_congr h43 (deq_refl _)) (mul_sub _ _ _)
          _ ≈ ofInt 3 * c - (ofInt 4 * β - ofInt 4 * β * pow2Neg k) :=
                sub_congr (deq_refl _) (sub_congr (mul_one _) (deq_refl _))
          _ ≈ ofInt 4 * β * pow2Neg k - (ofInt 4 * β - ofInt 3 * c) := hsub3 _ _ _
      have h4le : ofInt 4 * (⟨3, 2⟩ * c - β * phi2 r) ≤ᵈ zero := by
        have hsub0 : ofInt 4 * β * pow2Neg k - δ ≤ᵈ zero :=
          dle_trans (add_dle_add hk (dle_refl (-δ))) (dle_of_deq (add_neg δ))
        exact dle_congr (deq_symm h4eq) (deq_refl _) hsub0
      exact dle_zero_of_ofInt_mul_dle_zero (by decide) h4le
    have hpow_pos : zero <ᵈ Dyad.pow ⟨3, 2⟩ (popcount r - 1) :=
      dyad_pow_pos (by decide : zero <ᵈ (⟨3, 2⟩ : Dyad)) _
    have hprod_le : Dyad.pow ⟨3, 2⟩ (popcount r - 1) * (⟨3, 2⟩ * c - β * phi2 r) ≤ᵈ zero :=
      dle_trans (mul_dle_mul_of_nonneg_left (dle_of_dlt hpow_pos) hfactor_le) (dle_of_deq (mul_zero _))
    exact not_dlt_of_dle hprod_le hpiv_pos
  · intro hcond n
    refine (schurSystem_nested_iff vdcHammingSystem (c, β) (vdcHammingMat c β) hagree n).mpr ?_
    intro r hr
    have hD_eq : schurD vdcHammingSystem (c, β) n r ≈ vdcHammingPivot c β r :=
      schurD_vdcHamming_eq n c β r (Nat.lt_trans hr Nat.lt_two_pow_self)
    refine dlt_congr (deq_refl _) (deq_symm hD_eq) ?_
    unfold vdcHammingPivot
    by_cases hr0 : r = 0
    · simp only [hr0, ↓reduceIte]
      have h3c : zero <ᵈ ofInt 3 * c :=
        dlt_of_dlt_of_dle (mul_pos_of_pos (by decide : zero <ᵈ ofInt 4) hβ) hcond
      rw [zero_dlt_iff] at h3c ⊢
      change 0 < 3 * c.mant at h3c
      omega
    · simp only [hr0, ↓reduceIte]
      have hpow_pos : zero <ᵈ Dyad.pow ⟨3, 2⟩ (popcount r - 1) :=
        dyad_pow_pos (by decide : zero <ᵈ (⟨3, 2⟩ : Dyad)) _
      have hphi_lt : phi2 r <ᵈ one := phi2_lt_one r
      have hβphi_lt : β * phi2 r <ᵈ β :=
        dlt_congr (deq_refl _) (mul_one β) (mul_dlt_mul_of_pos_left hβ hphi_lt)
      have hβ_le_34c : β ≤ᵈ ⟨3, 2⟩ * c := by
        have h4eq : ofInt 4 * (⟨3, 2⟩ * c) ≈ ofInt 3 * c := by
          have h43 : ofInt 4 * (⟨3, 2⟩ : Dyad) ≈ ofInt 3 := by decide
          exact deq_trans (deq_symm (mul_assoc _ _ _)) (mul_congr h43 (deq_refl _))
        have h4le : ofInt 4 * β ≤ᵈ ofInt 4 * (⟨3, 2⟩ * c) :=
          dle_congr (deq_refl _) (deq_symm h4eq) hcond
        exact dle_of_ofInt_mul_dle (by decide) h4le
      have hinner : zero <ᵈ ⟨3, 2⟩ * c - β * phi2 r :=
        (sub_pos_iff _ _).mpr (dlt_of_dlt_of_dle hβphi_lt hβ_le_34c)
      exact mul_pos_of_pos hpow_pos hinner

/-- Concrete critical pure-dyadic instantiation (`c = 4, β = 3`, exact ratio `4/3`). -/
theorem vdcHamming_critical_4_3_all_n (n : Nat) :
    StrictlyPosDef n (vdcHammingMat (ofInt 4) (ofInt 3)) :=
  (vdcHamming_strictlyPosDef_all_n_iff (by decide : zero <ᵈ ofInt 3)).mpr (by decide) n

/-- Sharpness counterexample for Family I: `c = 15/4, β = 3` (ratio `5/4 < 4/3`)
    is strictly PD at `n = 15` YET fails strict PD at `n = 16`! -/
theorem vdcHamming_sharp_15_4_passes_15 :
    StrictlyPosDef 15 (vdcHammingMat ⟨15, 2⟩ (ofInt 3)) := by
  have hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k →
      vdcHammingMat ⟨15, 2⟩ (ofInt 3) i j ≈ vdcHammingSystem.mat (⟨15, 2⟩, ofInt 3) k i j :=
    fun _ _ _ _ _ => deq_refl _
  refine (schurSystem_nested_iff vdcHammingSystem (⟨15, 2⟩, ofInt 3)
    (vdcHammingMat ⟨15, 2⟩ (ofInt 3)) hagree 15).mpr ?_
  intro r hr
  have hD := schurD_vdcHamming_eq 15 ⟨15, 2⟩ (ofInt 3) r (Nat.lt_trans hr Nat.lt_two_pow_self)
  refine dlt_congr (deq_refl _) (deq_symm hD) ?_
  match r with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => decide
  | n + 15 => omega

theorem vdcHamming_sharp_15_4_fails_16 :
    ¬ StrictlyPosDef 16 (vdcHammingMat ⟨15, 2⟩ (ofInt 3)) := by
  have hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k →
      vdcHammingMat ⟨15, 2⟩ (ofInt 3) i j ≈ vdcHammingSystem.mat (⟨15, 2⟩, ofInt 3) k i j :=
    fun _ _ _ _ _ => deq_refl _
  intro hpd
  have h15 := (schurSystem_nested_iff vdcHammingSystem (⟨15, 2⟩, ofInt 3)
    (vdcHammingMat ⟨15, 2⟩ (ofInt 3)) hagree 16).mp hpd 15 (by omega)
  have hD := schurD_vdcHamming_eq 16 ⟨15, 2⟩ (ofInt 3) 15 (Nat.lt_trans (by omega) Nat.lt_two_pow_self)
  have hpiv : zero <ᵈ vdcHammingPivot ⟨15, 2⟩ (ofInt 3) 15 := dlt_congr (deq_refl _) hD h15
  have hzero : ¬ (zero <ᵈ vdcHammingPivot ⟨15, 2⟩ (ofInt 3) 15) := by decide
  exact hzero hpiv

-- ============================================================================
-- FAMILY II: BIT-POSITION-WEIGHTED VAN DER CORPUT KERNEL
-- Scale-varying coupling E_k = 2^{-(k+1)} I, DIMENSION-FREE UNIFORM LOWER BOUND!
-- K^{(W)}_{c,β}(x, y) = 2^(-W(x ^^^ y)) * (c - β * φ_2(x &&& y))
-- At c = 5/4, β = 1 (where Family I FAILS at n=16!), EVERY pivot D(r) ≥ 1/128 ∀ n!
-- ============================================================================

theorem schurFactorW_nonneg (k : Nat) : zero ≤ᵈ schurFactorW k := by
  refine (sub_nonneg_iff _ _).mpr ?_
  exact dle_trans (pow2Neg_antitone (by omega : 0 ≤ 2 * (k + 1))) (dle_of_deq pow2Neg_zero)

theorem schurFactorW_le_one (k : Nat) : schurFactorW k ≤ᵈ one :=
  sub_le_self_of_nonneg one (pow2Neg_nonneg _)

/-- Key exact algebraic lower bound: `3 * prodW k ≥ 2 + 4^(-k)` for ALL `k : Nat`! -/
theorem three_mul_prodW_ge (k : Nat) : ofInt 2 + pow2Neg (2 * k) ≤ᵈ ofInt 3 * prodW k := by
  induction k with
  | zero =>
    show ofInt 2 + pow2Neg 0 ≤ᵈ ofInt 3 * one
    decide
  | succ k ih =>
    have hfk_nn : zero ≤ᵈ schurFactorW k := schurFactorW_nonneg k
    have hstep : schurFactorW k * (ofInt 2 + pow2Neg (2 * k)) ≤ᵈ
                 schurFactorW k * (ofInt 3 * prodW k) :=
      mul_dle_mul_of_nonneg_left hfk_nn ih
    have hrhs : schurFactorW k * (ofInt 3 * prodW k) ≈ ofInt 3 * prodW (k + 1) := by
      show schurFactorW k * (ofInt 3 * prodW k) ≈ ofInt 3 * (schurFactorW k * prodW k)
      exact deq_trans (deq_symm (mul_assoc _ _ _))
        (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
    have hlow : ofInt 2 + pow2Neg (2 * (k + 1)) ≤ᵈ
                schurFactorW k * (ofInt 2 + pow2Neg (2 * k)) := by
      show ((2 : Int) * (2 ^ (2 * (k + 1)) : Int) + 1 * (2 ^ 0 : Int)) *
           (2 ^ ((0 + 2 * (k + 1)) + (0 + 2 * k)) : Int) ≤
           ((1 * (2 ^ (2 * (k + 1)) : Int) + (-1) * (2 ^ 0 : Int)) *
            (2 * (2 ^ (2 * k) : Int) + 1 * (2 ^ 0 : Int))) *
           (2 ^ (0 + 2 * (k + 1)) : Int)
      simp only [Nat.zero_add, Int.one_mul, Int.mul_one, Int.pow_zero]
      have h2k_eq : (2 ^ (2 * (k + 1)) : Int) = 4 * (2 ^ (2 * k) : Int) := by
        have : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [this, two_pow_add]
        have h4 : (2 ^ 2 : Int) = 4 := by decide
        rw [h4, Int.mul_comm]
      have hq_ge : (1 : Int) ≤ (2 ^ (2 * k) : Int) := by
        have hp := two_pow_pos (2 * k); omega
      rw [two_pow_add, h2k_eq]
      generalize (2 ^ (2 * k) : Int) = q at hq_ge ⊢
      have hbase : (2 * (4 * q) + 1) * q ≤ (4 * q + -1) * (2 * q + 1) := by
        have hlin : (4 * q + -1) * (2 * q + 1) = (2 * (4 * q) + 1) * q + (q - 1) := by
          rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.add_mul]
          have h1 : 4 * q * (2 * q) = 2 * (4 * q) * q := by ac_rfl
          have h2 : (-1 : Int) * (2 * q) = -(2 * q) := by omega
          have h3 : (-1 : Int) * 1 = -1 := by decide
          omega
        omega
      have h4q_nn : 0 ≤ 4 * q := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right hbase h4q_nn
      calc
        (2 * (4 * q) + 1) * (4 * q * q)
            = (2 * (4 * q) + 1) * q * (4 * q) := by ac_rfl
        _ ≤ (4 * q + -1) * (2 * q + 1) * (4 * q) := hmul
    exact dle_trans hlow (dle_trans hstep (dle_of_deq hrhs))

theorem prodW_nonneg (k : Nat) : zero ≤ᵈ prodW k := by
  induction k with
  | zero => exact dle_of_dlt (by decide : zero <ᵈ one)
  | succ k ih => exact mul_nonneg_of_nonneg (schurFactorW_nonneg k) ih

theorem envV_one_eq : envV 1 ≈ ⟨43, 6⟩ := by
  have hm : (⟨9, 3⟩ : Dyad) * pow2Neg 1 ≈ ⟨9, 4⟩ := by decide
  have hv1a : envV 1 ≈ ⟨79, 6⟩ - ⟨9, 4⟩ := sub_congr (deq_refl ⟨79, 6⟩) hm
  have hv1b : (⟨79, 6⟩ : Dyad) - ⟨9, 4⟩ ≈ ⟨43, 6⟩ := by
    show (79 * (2 ^ 4 : Int) + (-9) * (2 ^ 6 : Int)) * (2 ^ 6 : Int) = 43 * (2 ^ (6 + 4) : Int)
    have h4 : (2 ^ 4 : Int) = 16 := rfl
    have h6 : (2 ^ 6 : Int) = 64 := rfl
    have h10 : (2 ^ (6 + 4) : Int) = 1024 := rfl
    rw [h4, h6, h10]; decide
  exact deq_trans hv1a hv1b

theorem envV_mono (k : Nat) : envV k ≤ᵈ envV (k + 1) := by
  cases k with
  | zero =>
    exact dle_congr (deq_refl zero) (deq_symm envV_one_eq) (by decide : zero ≤ᵈ (⟨43, 6⟩ : Dyad))
  | succ k =>
    show ⟨79, 6⟩ - ⟨9, 3⟩ * pow2Neg (k + 1) ≤ᵈ ⟨79, 6⟩ - ⟨9, 3⟩ * pow2Neg (k + 2)
    exact sub_dle_sub_left ⟨79, 6⟩
      (mul_dle_mul_of_nonneg_left (by decide : zero ≤ᵈ (⟨9, 3⟩ : Dyad)) (pow2Neg_antitone (by omega)))

theorem envV_step (k : Nat) :
    pow2Neg (k + 1) ≤ᵈ schurFactorW k * (envV (k + 1) - envV k) := by
  cases k with
  | zero =>
    have hf0 : schurFactorW 0 ≈ ⟨3, 2⟩ := by decide
    have hv1 : envV 1 - envV 0 ≈ ⟨43, 6⟩ :=
      deq_trans (deq_trans (add_congr (deq_refl _) neg_zero) (add_zero _)) envV_one_eq
    have hprod : pow2Neg 1 ≤ᵈ (⟨3, 2⟩ : Dyad) * ⟨43, 6⟩ := by
      show (1 : Int) * (2 ^ (2 + 6) : Int) ≤ (3 * 43) * (2 ^ 1 : Int)
      have h8 : (2 ^ (2 + 6) : Int) = 256 := rfl
      have h1 : (2 ^ 1 : Int) = 2 := rfl
      rw [h8, h1]; decide
    exact dle_congr (deq_refl _) (deq_symm (mul_congr hf0 hv1)) hprod
  | succ k =>
    let q98 : Dyad := ⟨9, 3⟩
    let p1 := pow2Neg (k + 1)
    let p2 := pow2Neg (k + 2)
    have ha : envV (k + 2) - envV (k + 1) ≈ q98 * p1 - q98 * p2 :=
      sub_sub_sub_cancel ⟨79, 6⟩ (q98 * p2) (q98 * p1)
    have hb : q98 * p1 - q98 * p2 ≈ q98 * (p1 - p2) := deq_symm (mul_sub q98 p1 p2)
    have hc : q98 * (p1 - p2) ≈ q98 * p2 := mul_congr (deq_refl q98) (pow2Neg_sub_half (k + 1))
    have hdiff : envV (k + 2) - envV (k + 1) ≈ q98 * p2 := deq_trans ha (deq_trans hb hc)
    have hfk_ge : (⟨15, 4⟩ : Dyad) ≤ᵈ schurFactorW (k + 1) := by
      have h15 : (⟨15, 4⟩ : Dyad) ≈ one - pow2Neg 4 := by decide
      exact dle_congr (deq_symm h15) (deq_refl _)
        (sub_dle_sub_left one (pow2Neg_antitone (by omega)))
    have hprod_ge : one ≤ᵈ schurFactorW (k + 1) * ⟨9, 3⟩ :=
      dle_trans (by decide : one ≤ᵈ (⟨15, 4⟩ : Dyad) * ⟨9, 3⟩)
        (mul_dle_mul_of_nonneg_right (by decide : zero ≤ᵈ (⟨9, 3⟩ : Dyad)) hfk_ge)
    calc
      pow2Neg (k + 2) ≈ one * pow2Neg (k + 2) := deq_symm (one_mul _)
      _ ≤ᵈ (schurFactorW (k + 1) * ⟨9, 3⟩) * pow2Neg (k + 2) :=
            mul_dle_mul_of_nonneg_right (pow2Neg_nonneg _) hprod_ge
      _ ≈ schurFactorW (k + 1) * (⟨9, 3⟩ * pow2Neg (k + 2)) := mul_assoc _ _ _
      _ ≈ schurFactorW (k + 1) * (envV (k + 2) - envV (k + 1)) :=
            mul_congr (deq_refl _) (deq_symm hdiff)

/-- **THEOREM 2 (DIMENSION-FREE UNIFORM EXACT DYADIC PIVOT LOWER BOUND FOR FAMILY II)**:
    For the Bit-Position-Weighted van der Corput Kernel `K^{(W)}_{5/4, 1}` (at `c = 5/4`, where
    the constant-coupling Family I FAILS at `n = 16`!), EVERY pivot `D(r)` satisfies the
    **dimension-free uniform exact dyadic lower bound** `1/128 ≤ D(r)` for ALL `k, r < 2^k`,
    and hence `K^{(W)}_{5/4, 1}` is strictly positive definite for **ALL `n : Nat`**! -/
theorem weightedVdc_pivot_lb_general :
    ∀ k (σ : Dyad × Dyad) r, r < 2 ^ k →
      zero ≤ᵈ σ.2 → envV k * σ.2 ≤ᵈ σ.1 →
      prodW k * (σ.1 - envV k * σ.2) ≤ᵈ schurD weightedVdcSystem σ k r := by
  intro k
  induction k with
  | zero =>
    intro σ r hr _ _
    have hr0 : r = 0 := by omega
    subst hr0
    show one * (σ.1 - zero * σ.2) ≤ᵈ
         pow2Neg (bitWeight (0 ^^^ 0)) * (σ.1 - σ.2 * phi2 (0 &&& 0))
    have hbw : bitWeight (0 ^^^ 0) = 0 := by decide
    have ha : 0 &&& 0 = 0 := by decide
    rw [hbw, ha, phi2, phi2From_zero]
    refine dle_of_deq ?_
    calc
      one * (σ.1 - zero * σ.2)
          ≈ σ.1 - zero := deq_trans (one_mul _) (sub_congr (deq_refl _) (zero_mul _))
      _ ≈ one * (σ.1 - σ.2 * zero) :=
            deq_symm (deq_trans (one_mul _) (sub_congr (deq_refl _) (mul_zero _)))
      _ ≈ pow2Neg 0 * (σ.1 - σ.2 * zero) := mul_congr (deq_symm pow2Neg_zero) (deq_refl _)
  | succ k ih =>
    intro σ r hr hβ hinv
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    unfold schurD blockD
    by_cases hrk : r < 2 ^ k
    · simp only [hrk, ↓reduceIte]
      have hVle : envV k * σ.2 ≤ᵈ envV (k + 1) * σ.2 :=
        mul_dle_mul_of_nonneg_right hβ (envV_mono k)
      have hinv' : envV k * σ.2 ≤ᵈ σ.1 := dle_trans hVle hinv
      have hdiff_le : σ.1 - envV (k + 1) * σ.2 ≤ᵈ σ.1 - envV k * σ.2 :=
        sub_dle_sub_left σ.1 hVle
      have hmargin_nn : zero ≤ᵈ σ.1 - envV (k + 1) * σ.2 := (sub_nonneg_iff _ _).mpr hinv
      have hprod_le : prodW (k + 1) ≤ᵈ prodW k := by
        show schurFactorW k * prodW k ≤ᵈ prodW k
        exact dle_trans (mul_dle_mul_of_nonneg_right (prodW_nonneg k) (schurFactorW_le_one k))
          (dle_of_deq (one_mul _))
      calc
        prodW (k + 1) * (σ.1 - envV (k + 1) * σ.2)
            ≤ᵈ prodW k * (σ.1 - envV (k + 1) * σ.2) :=
              mul_dle_mul_of_nonneg_right hmargin_nn hprod_le
        _ ≤ᵈ prodW k * (σ.1 - envV k * σ.2) :=
              mul_dle_mul_of_nonneg_left (prodW_nonneg k) hdiff_le
        _ ≤ᵈ schurD weightedVdcSystem σ k r := ih σ r hrk hβ hinv'
    · simp only [hrk, ↓reduceIte]
      let c' := schurFactorW k * σ.1 - σ.2 * pow2Neg (k + 1)
      let β' := schurFactorW k * σ.2
      have hfk_nn : zero ≤ᵈ schurFactorW k := schurFactorW_nonneg k
      have hβ' : zero ≤ᵈ β' := mul_nonneg_of_nonneg hfk_nn hβ
      have hmargin : schurFactorW k * (σ.1 - envV (k + 1) * σ.2) ≤ᵈ c' - envV k * β' := by
        have hstep := mul_dle_mul_of_nonneg_right hβ (envV_step k)
        have h1 : schurFactorW k * (envV (k + 1) - envV k) * σ.2 ≈
                  schurFactorW k * (envV (k + 1) * σ.2) - envV k * β' := by
          calc
            schurFactorW k * (envV (k + 1) - envV k) * σ.2
                ≈ (schurFactorW k * envV (k + 1) - schurFactorW k * envV k) * σ.2 :=
                  mul_congr (mul_sub _ _ _) (deq_refl _)
            _ ≈ (schurFactorW k * envV (k + 1)) * σ.2 - (schurFactorW k * envV k) * σ.2 :=
                  sub_mul _ _ _
            _ ≈ schurFactorW k * (envV (k + 1) * σ.2) - envV k * (schurFactorW k * σ.2) :=
                  sub_congr (mul_assoc _ _ _)
                    (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
        have h2 : schurFactorW k * (σ.1 - envV (k + 1) * σ.2) +
                  schurFactorW k * (envV (k + 1) * σ.2) ≈ schurFactorW k * σ.1 :=
          deq_trans (add_congr (mul_sub _ _ _) (deq_refl _)) (sub_add_cancel _ _)
        have h3 : schurFactorW k * (σ.1 - envV (k + 1) * σ.2) +
                  (schurFactorW k * (envV (k + 1) * σ.2) - envV k * β') ≈
                  schurFactorW k * σ.1 - envV k * β' :=
          deq_trans (deq_symm (add_assoc _ _ _)) (add_congr h2 (deq_refl _))
        have halg : c' - envV k * β' ≈
                    schurFactorW k * (σ.1 - envV (k + 1) * σ.2) +
                    (schurFactorW k * (envV (k + 1) - envV k) * σ.2 - pow2Neg (k + 1) * σ.2) := by
          calc
            c' - envV k * β'
                ≈ (schurFactorW k * σ.1 - envV k * β') - σ.2 * pow2Neg (k + 1) := sub_sub_comm _ _ _
            _ ≈ (schurFactorW k * σ.1 - envV k * β') - pow2Neg (k + 1) * σ.2 :=
                  sub_congr (deq_refl _) (mul_comm _ _)
            _ ≈ (schurFactorW k * (σ.1 - envV (k + 1) * σ.2) +
                 (schurFactorW k * (envV (k + 1) * σ.2) - envV k * β')) - pow2Neg (k + 1) * σ.2 :=
                  sub_congr (deq_symm h3) (deq_refl _)
            _ ≈ schurFactorW k * (σ.1 - envV (k + 1) * σ.2) +
                ((schurFactorW k * (envV (k + 1) * σ.2) - envV k * β') - pow2Neg (k + 1) * σ.2) :=
                  add_assoc _ _ _
            _ ≈ schurFactorW k * (σ.1 - envV (k + 1) * σ.2) +
                (schurFactorW k * (envV (k + 1) - envV k) * σ.2 - pow2Neg (k + 1) * σ.2) :=
                  add_congr (deq_refl _) (sub_congr (deq_symm h1) (deq_refl _))
        have hrem_nn : zero ≤ᵈ schurFactorW k * (envV (k + 1) - envV k) * σ.2 - pow2Neg (k + 1) * σ.2 :=
          (sub_nonneg_iff _ _).mpr hstep
        calc
          schurFactorW k * (σ.1 - envV (k + 1) * σ.2)
              ≈ schurFactorW k * (σ.1 - envV (k + 1) * σ.2) + zero := deq_symm (add_zero _)
          _ ≤ᵈ schurFactorW k * (σ.1 - envV (k + 1) * σ.2) +
               (schurFactorW k * (envV (k + 1) - envV k) * σ.2 - pow2Neg (k + 1) * σ.2) :=
                add_dle_add (dle_refl _) hrem_nn
          _ ≈ c' - envV k * β' := deq_symm halg
      have hinv' : envV k * β' ≤ᵈ c' := by
        refine (sub_nonneg_iff c' (envV k * β')).mp ?_
        exact dle_trans (mul_nonneg_of_nonneg hfk_nn ((sub_nonneg_iff _ _).mpr hinv)) hmargin
      have hrec := ih (c', β') (r - 2 ^ k) (by omega) hβ' hinv'
      calc
        prodW (k + 1) * (σ.1 - envV (k + 1) * σ.2)
            = (schurFactorW k * prodW k) * (σ.1 - envV (k + 1) * σ.2) := rfl
        _ ≈ prodW k * (schurFactorW k * (σ.1 - envV (k + 1) * σ.2)) :=
              deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _)
        _ ≤ᵈ prodW k * (c' - envV k * β') := mul_dle_mul_of_nonneg_left (prodW_nonneg k) hmargin
        _ ≤ᵈ schurD weightedVdcSystem (c', β') k (r - 2 ^ k) := hrec

theorem weightedVdc_5_4_uniform_pivot_lb (k r : Nat) (hr : r < 2 ^ k) :
    pow2Neg 7 ≤ᵈ schurD weightedVdcSystem (⟨5, 2⟩, one) k r := by
  have hVle : envV k ≤ᵈ ⟨79, 6⟩ := by
    cases k with
    | zero => show zero ≤ᵈ ⟨79, 6⟩; decide
    | succ k =>
      show ⟨79, 6⟩ - ⟨9, 3⟩ * pow2Neg (k + 1) ≤ᵈ ⟨79, 6⟩
      exact sub_le_self_of_nonneg ⟨79, 6⟩
        (mul_nonneg_of_nonneg (by decide : zero ≤ᵈ (⟨9, 3⟩ : Dyad)) (pow2Neg_nonneg _))
  have hVmul : envV k * one ≤ᵈ ⟨79, 6⟩ := dle_trans (dle_of_deq (mul_one _)) hVle
  have hinv : envV k * one ≤ᵈ ⟨5, 2⟩ := dle_trans hVmul (by decide : (⟨79, 6⟩ : Dyad) ≤ᵈ ⟨5, 2⟩)
  have hmargin : pow2Neg 6 ≤ᵈ ⟨5, 2⟩ - envV k * one :=
    dle_trans (by decide : pow2Neg 6 ≤ᵈ (⟨5, 2⟩ : Dyad) - ⟨79, 6⟩) (sub_dle_sub_left ⟨5, 2⟩ hVmul)
  have hprod_ge : pow2Neg 1 ≤ᵈ prodW k := by
    have h3 := three_mul_prodW_ge k
    have h2 : ofInt 2 ≤ᵈ ofInt 3 * prodW k :=
      dle_trans (dle_congr (add_zero _) (deq_refl _) (add_dle_add (dle_refl _) (pow2Neg_nonneg (2 * k)))) h3
    change (1 : Int) * (2 ^ (prodW k).shift : Int) ≤ (prodW k).mant * (2 ^ 1 : Int)
    change (2 : Int) * (2 ^ (0 + (prodW k).shift) : Int) ≤ (3 * (prodW k).mant) * (2 ^ 0 : Int) at h2
    simp only [Nat.zero_add, Int.one_mul, Int.pow_zero, Int.mul_one] at h2 ⊢
    have hp : (2 ^ 1 : Int) = 2 := by decide
    have hd : (0 : Int) < (2 ^ (prodW k).shift : Int) := two_pow_pos (prodW k).shift
    rw [hp]
    omega
  have hbase := weightedVdc_pivot_lb_general k (⟨5, 2⟩, one) r hr (by decide) hinv
  have hlow : pow2Neg 7 ≤ᵈ prodW k * (⟨5, 2⟩ - envV k * one) := by
    calc
      pow2Neg 7 ≈ pow2Neg 1 * pow2Neg 6 := deq_symm (pow2Neg_mul 1 6)
      _ ≤ᵈ prodW k * pow2Neg 6 := mul_dle_mul_of_nonneg_right (pow2Neg_nonneg 6) hprod_ge
      _ ≤ᵈ prodW k * (⟨5, 2⟩ - envV k * one) := mul_dle_mul_of_nonneg_left (prodW_nonneg k) hmargin
  exact dle_trans hlow hbase

theorem weightedVdc_5_4_strictlyPosDef_all_n (n : Nat) :
    StrictlyPosDef n (weightedVdcMat ⟨5, 2⟩ one) := by
  have hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k →
      weightedVdcMat ⟨5, 2⟩ one i j ≈ weightedVdcSystem.mat (⟨5, 2⟩, one) k i j :=
    fun _ _ _ _ _ => deq_refl _
  refine (schurSystem_nested_iff weightedVdcSystem (⟨5, 2⟩, one)
    (weightedVdcMat ⟨5, 2⟩ one) hagree n).mpr ?_
  intro r hr
  exact dlt_of_dlt_of_dle (pow2Neg_pos 7)
    (weightedVdc_5_4_uniform_pivot_lb n r (Nat.lt_trans hr Nat.lt_two_pow_self))

/-- Fast exact shift-aligned dyadic subtraction lemma (zero shift blowup!). -/
theorem dyad_sub_aligned {a b c : Int} {s d : Nat}
    (h : a - b * (2 ^ d : Int) = c) :
    (⟨a, s + d⟩ : Dyad) - ⟨b, s⟩ ≈ ⟨c, s + d⟩ := by
  show (a * (2 ^ s : Int) + (-b) * (2 ^ (s + d) : Int)) * (2 ^ (s + d) : Int) =
       c * (2 ^ ((s + d) + s) : Int)
  rw [two_pow_add (s + d) s, two_pow_add s d]
  rw [← h, Int.sub_eq_add_neg, Int.add_mul, Int.add_mul, Int.neg_mul, Int.neg_mul]
  congr 1
  · ac_rfl
  · rw [Int.neg_mul]; congr 1; ac_rfl

theorem schurD_right_step {State : Type} (S : SchurSystem State) (σ : State) (k u : Nat) :
    schurD S σ (k + 1) (2 ^ k + u) = schurD S (S.rightState σ k) k u := by
  have hnot : ¬ (2 ^ k + u < 2 ^ k) := by omega
  show (if 2 ^ k + u < 2 ^ k then schurD S (S.leftState σ k) k (2 ^ k + u)
        else schurD S (S.rightState σ k) k (2 ^ k + u - 2 ^ k)) =
       schurD S (S.rightState σ k) k u
  simp [hnot]

/-- Sharpness counterexample for Family II: `c = 17/16, β = 1` fails strict PD at `n = 16`! -/
theorem weightedVdc_sharp_17_16_fails_16 :
    ¬ StrictlyPosDef 16 (weightedVdcMat ⟨17, 4⟩ one) := by
  intro hpd
  have h15 := (ldlt_strictlyPosDef_iff (schurSystem_ldlt weightedVdcSystem 4 (⟨17, 4⟩, one))).mp
    hpd 15 (by decide)
  have hstep : ∀ (a1 a2 b1 b2 : Dyad) (k : Nat),
      a1 ≈ a2 → b1 ≈ b2 →
      schurFactorW k * a1 - b1 * pow2Neg (k + 1) ≈ schurFactorW k * a2 - b2 * pow2Neg (k + 1) := by
    intro a1 a2 b1 b2 k ha hb
    exact sub_congr (mul_congr (deq_refl _) ha) (mul_congr hb (deq_refl _))
  have hf3 : schurFactorW 3 ≈ ⟨255, 8⟩ := by
    show (1 * (2 ^ 8 : Int) + (-1) * (2 ^ 0 : Int)) * (2 ^ 8 : Int) = 255 * (2 ^ (0 + 8) : Int)
    have h8 : (2 ^ 8 : Int) = 256 := rfl
    have h0 : (2 ^ 0 : Int) = 1 := rfl
    rw [Nat.zero_add, h8, h0]; decide
  have hf2 : schurFactorW 2 ≈ ⟨63, 6⟩ := by
    show (1 * (2 ^ 6 : Int) + (-1) * (2 ^ 0 : Int)) * (2 ^ 6 : Int) = 63 * (2 ^ (0 + 6) : Int)
    have h6 : (2 ^ 6 : Int) = 64 := rfl
    have h0 : (2 ^ 0 : Int) = 1 := rfl
    rw [Nat.zero_add, h6, h0]; decide
  have hf1 : schurFactorW 1 ≈ ⟨15, 4⟩ := by decide
  have hf0 : schurFactorW 0 ≈ ⟨3, 2⟩ := by decide
  have hc3 : schurFactorW 3 * ⟨17, 4⟩ - one * pow2Neg 4 ≈ ⟨4079, 12⟩ := by
    have h1 := sub_congr (mul_congr hf3 (deq_refl ⟨17, 4⟩)) (one_mul (pow2Neg 4))
    have h2 : (⟨255, 8⟩ : Dyad) * ⟨17, 4⟩ - pow2Neg 4 ≈ ⟨4079, 12⟩ :=
      dyad_sub_aligned (s := 4) (d := 8) (by decide)
    exact deq_trans h1 h2
  have hβ3 : schurFactorW 3 * one ≈ ⟨255, 8⟩ := deq_trans (mul_one _) hf3
  have hc2 : schurFactorW 2 * ⟨4079, 12⟩ - ⟨255, 8⟩ * pow2Neg 3 ≈ ⟨224337, 18⟩ := by
    have h1 := sub_congr (mul_congr hf2 (deq_refl ⟨4079, 12⟩)) (deq_refl (⟨255, 8⟩ * pow2Neg 3))
    have h2 : (⟨63, 6⟩ : Dyad) * ⟨4079, 12⟩ - ⟨255, 8⟩ * pow2Neg 3 ≈ ⟨224337, 18⟩ :=
      dyad_sub_aligned (s := 11) (d := 7) (by decide)
    exact deq_trans h1 h2
  have hβ2 : schurFactorW 2 * ⟨255, 8⟩ ≈ ⟨16065, 14⟩ :=
    deq_trans (mul_congr hf2 (deq_refl ⟨255, 8⟩)) (by show (63 * 255 : Int) * _ = 16065 * _; rfl)
  have hc1 : schurFactorW 1 * ⟨224337, 18⟩ - ⟨16065, 14⟩ * pow2Neg 2 ≈ ⟨2336895, 22⟩ := by
    have h1 := sub_congr (mul_congr hf1 (deq_refl ⟨224337, 18⟩)) (deq_refl (⟨16065, 14⟩ * pow2Neg 2))
    have h2 : (⟨15, 4⟩ : Dyad) * ⟨224337, 18⟩ - ⟨16065, 14⟩ * pow2Neg 2 ≈ ⟨2336895, 22⟩ :=
      dyad_sub_aligned (s := 16) (d := 6) (by decide)
    exact deq_trans h1 h2
  have hβ1 : schurFactorW 1 * ⟨16065, 14⟩ ≈ ⟨240975, 18⟩ :=
    deq_trans (mul_congr hf1 (deq_refl ⟨16065, 14⟩)) (by show (15 * 16065 : Int) * _ = 240975 * _; rfl)
  have hc0 : schurFactorW 0 * ⟨2336895, 22⟩ - ⟨240975, 18⟩ * pow2Neg 1 ≈ ⟨-700515, 24⟩ := by
    have h1 := sub_congr (mul_congr hf0 (deq_refl ⟨2336895, 22⟩)) (deq_refl (⟨240975, 18⟩ * pow2Neg 1))
    have h2 : (⟨3, 2⟩ : Dyad) * ⟨2336895, 22⟩ - ⟨240975, 18⟩ * pow2Neg 1 ≈ ⟨-700515, 24⟩ :=
      dyad_sub_aligned (s := 19) (d := 5) (by decide)
    exact deq_trans h1 h2
  have hcongr_D : ∀ k (σ1 σ2 : Dyad × Dyad) r,
      σ1.1 ≈ σ2.1 → σ1.2 ≈ σ2.2 → schurD weightedVdcSystem σ1 k r ≈ schurD weightedVdcSystem σ2 k r := by
    intro k
    induction k with
    | zero =>
      intro σ1 σ2 _ h1 h2
      show pow2Neg (bitWeight (0 ^^^ 0)) * (σ1.1 - σ1.2 * phi2 (0 &&& 0)) ≈
           pow2Neg (bitWeight (0 ^^^ 0)) * (σ2.1 - σ2.2 * phi2 (0 &&& 0))
      exact mul_congr (deq_refl _) (sub_congr h1 (mul_congr h2 (deq_refl _)))
    | succ k ih =>
      intro σ1 σ2 r h1 h2
      unfold schurD blockD
      by_cases hr : r < 2 ^ k
      · simp only [hr, ↓reduceIte]; exact ih σ1 σ2 r h1 h2
      · simp only [hr, ↓reduceIte]
        exact ih _ _ (r - 2 ^ k) (hstep _ _ _ _ k h1 h2) (mul_congr (deq_refl _) h2)
  have hD15 : schurD weightedVdcSystem (⟨17, 4⟩, one) 4 15 ≈ ⟨-700515, 24⟩ := by
    have s4 := schurD_right_step weightedVdcSystem (⟨17, 4⟩, one) 3 7
    have e3 : schurD weightedVdcSystem (weightedVdcSystem.rightState (⟨17, 4⟩, one) 3) 3 7 ≈
              schurD weightedVdcSystem (⟨4079, 12⟩, ⟨255, 8⟩) 3 7 := hcongr_D 3 _ _ 7 hc3 hβ3
    have s3 := schurD_right_step weightedVdcSystem (⟨4079, 12⟩, ⟨255, 8⟩) 2 3
    have e2 : schurD weightedVdcSystem (weightedVdcSystem.rightState (⟨4079, 12⟩, ⟨255, 8⟩) 2) 2 3 ≈
              schurD weightedVdcSystem (⟨224337, 18⟩, ⟨16065, 14⟩) 2 3 := hcongr_D 2 _ _ 3 hc2 hβ2
    have s2 := schurD_right_step weightedVdcSystem (⟨224337, 18⟩, ⟨16065, 14⟩) 1 1
    have e1 : schurD weightedVdcSystem (weightedVdcSystem.rightState (⟨224337, 18⟩, ⟨16065, 14⟩) 1) 1 1 ≈
              schurD weightedVdcSystem (⟨2336895, 22⟩, ⟨240975, 18⟩) 1 1 := hcongr_D 1 _ _ 1 hc1 hβ1
    have s1 := schurD_right_step weightedVdcSystem (⟨2336895, 22⟩, ⟨240975, 18⟩) 0 0
    have e0 : schurD weightedVdcSystem (weightedVdcSystem.rightState (⟨2336895, 22⟩, ⟨240975, 18⟩) 0) 0 0 ≈
              schurD weightedVdcSystem (⟨-700515, 24⟩, schurFactorW 0 * ⟨240975, 18⟩) 0 0 :=
      hcongr_D 0 _ _ 0 hc0 (deq_refl _)
    have hbase : schurD weightedVdcSystem (⟨-700515, 24⟩, schurFactorW 0 * ⟨240975, 18⟩) 0 0 ≈ ⟨-700515, 24⟩ := by
      show pow2Neg 0 * (⟨-700515, 24⟩ - (schurFactorW 0 * ⟨240975, 18⟩) * zero) ≈ ⟨-700515, 24⟩
      exact deq_trans (one_mul _)
        (deq_trans (sub_congr (deq_refl _) (mul_zero _))
          (deq_trans (add_congr (deq_refl _) neg_zero) (add_zero _)))
    change schurD weightedVdcSystem (⟨17, 4⟩, one) 4 (2 ^ 3 + 7) ≈ _
    rw [s4]
    refine deq_trans e3 ?_
    change schurD weightedVdcSystem (⟨4079, 12⟩, ⟨255, 8⟩) 3 (2 ^ 2 + 3) ≈ _
    rw [s3]
    refine deq_trans e2 ?_
    change schurD weightedVdcSystem (⟨224337, 18⟩, ⟨16065, 14⟩) 2 (2 ^ 1 + 1) ≈ _
    rw [s2]
    refine deq_trans e1 ?_
    change schurD weightedVdcSystem (⟨2336895, 22⟩, ⟨240975, 18⟩) 1 (2 ^ 0 + 0) ≈ _
    rw [s1]
    exact deq_trans e0 hbase
  have hneg : zero <ᵈ (⟨-700515, 24⟩ : Dyad) := dlt_congr (deq_refl zero) hD15 h15
  rw [zero_dlt_iff] at hneg
  change (0 : Int) < -700515 at hneg
  omega

-- ============================================================================
-- FAMILY III: BIT-WEIGHTED GRAY-CODE HAMMING KERNEL
-- NON-SCALAR ANTIDIAGONAL BIT-REFLECTION COUPLING E_k = 2^{-(k+1)} * J_k!
-- K^{Gray, W}(x, y) = 2^(-W(G(x) ^^^ G(y))), G(x) = x ^^^ (x >>> 1)
-- Uniform dimension-free lower bound D(r) ≥ 2/3 (> 5/8) ∀ k, r!
-- Identical pivots to plain Hamming, YET strictly distinct fractal factor L!
-- ============================================================================

/-- **THEOREM 3A (UNIFORM DIMENSION-FREE LOWER BOUND FOR GRAY BIT-WEIGHTED HAMMING)**:
    For EVERY `k : Nat` and EVERY `r < 2^k`, the Gray-code bit-weighted Hamming kernel
    (with antidiagonal bit-reflection coupling `E_k = 2^{-(k+1)} J_k`) has exact dyadic pivot
    `D(r) ≥ 2/3` (`ofInt 2 ≤ ofInt 3 * D(r)`, and `5/8 ≤ D(r)` in `Z[1/2]`),
    hence is strictly positive definite for ALL `k : Nat` (and ALL `n : Nat` by nesting!). -/
theorem grayWeighted_pivot_ge_prodW (k r : Nat) (hr : r < 2 ^ k) :
    prodW k ≤ᵈ schurD grayWeightedSystem one k r := by
  have hgen : ∀ k s r, r < 2 ^ k → zero ≤ᵈ s → prodW k * s ≤ᵈ schurD grayWeightedSystem s k r := by
    intro k
    induction k with
    | zero =>
      intro s r hr _
      have hr0 : r = 0 := by omega
      subst hr0
      show one * s ≤ᵈ s * pow2Neg (bitWeight (gray 0 ^^^ gray 0))
      have h0 : bitWeight (gray 0 ^^^ gray 0) = 0 := by decide
      rw [h0]
      exact dle_of_deq (deq_trans (one_mul s)
        (deq_symm (deq_trans (mul_congr (deq_refl s) pow2Neg_zero) (mul_one s))))
    | succ k ih =>
      intro s r hr hs
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      unfold schurD blockD
      by_cases hrk : r < 2 ^ k
      · simp only [hrk, ↓reduceIte]
        have hple : prodW (k + 1) ≤ᵈ prodW k :=
          dle_trans (mul_dle_mul_of_nonneg_right (prodW_nonneg k) (schurFactorW_le_one k))
            (dle_of_deq (one_mul _))
        exact dle_trans (mul_dle_mul_of_nonneg_right hs hple) (ih s r hrk hs)
      · simp only [hrk, ↓reduceIte]
        have hs' : zero ≤ᵈ schurFactorW k * s := mul_nonneg_of_nonneg (schurFactorW_nonneg k) hs
        have hre : prodW (k + 1) * s ≈ prodW k * (schurFactorW k * s) :=
          deq_trans (mul_congr (mul_comm (schurFactorW k) (prodW k)) (deq_refl s))
            (mul_assoc (prodW k) (schurFactorW k) s)
        exact dle_congr (deq_symm hre) (deq_refl _) (ih (schurFactorW k * s) (r - 2 ^ k) (by omega) hs')
  exact dle_congr (mul_one (prodW k)) (deq_refl _) (hgen k one r hr (by decide))

theorem grayWeighted_uniform_pivot_lb_two_thirds (k r : Nat) (hr : r < 2 ^ k) :
    ofInt 2 ≤ᵈ ofInt 3 * schurD grayWeightedSystem one k r := by
  have h1 : ofInt 2 ≤ᵈ ofInt 3 * prodW k :=
    dle_trans (dle_congr (add_zero _) (deq_refl _) (add_dle_add (dle_refl _) (pow2Neg_nonneg (2 * k))))
      (three_mul_prodW_ge k)
  exact dle_trans h1 (mul_dle_mul_of_nonneg_left (by decide : zero ≤ᵈ ofInt 3) (grayWeighted_pivot_ge_prodW k r hr))

theorem grayWeighted_uniform_pivot_lb_five_eighths (k r : Nat) (hr : r < 2 ^ k) :
    ⟨5, 3⟩ ≤ᵈ schurD grayWeightedSystem one k r := by
  have h23 := grayWeighted_uniform_pivot_lb_two_thirds k r hr
  have h15 : ofInt 3 * (⟨5, 3⟩ : Dyad) ≤ᵈ ofInt 2 := by decide
  exact dle_of_ofInt_mul_dle (by decide : (0 : Int) < 3) (dle_trans h15 h23)

theorem grayWeighted_strictlyPosDef_all_n (n : Nat) :
    StrictlyPosDef n grayWeightedMat := by
  have hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k →
      grayWeightedMat i j ≈ grayWeightedSystem.mat one k i j :=
    fun _ _ _ _ _ => deq_symm (one_mul _)
  refine (schurSystem_nested_iff grayWeightedSystem one grayWeightedMat hagree n).mpr ?_
  intro r hr
  exact dlt_of_dlt_of_dle (by decide : zero <ᵈ (⟨5, 3⟩ : Dyad))
    (grayWeighted_uniform_pivot_lb_five_eighths n r (Nat.lt_trans hr Nat.lt_two_pow_self))

/-- **THEOREM 3B (EXACT PIVOT ISOSPECTRALITY WITH STRICTLY DISTINCT FRACTAL `L`)**:
    Gray-code and plain bit-weighted Hamming kernels have IDENTICAL exact dyadic pivots
    for ALL `k, r < 2^k`, YET strictly distinct lower-triangular factors `L` (witnessed at `k = 2`)! -/
theorem gray_plain_pivots_eq :
    ∀ k s r, r < 2 ^ k →
      schurD grayWeightedSystem s k r ≈ schurD plainWeightedSystem s k r := by
  intro k
  induction k with
  | zero =>
    intro s r _
    show s * pow2Neg (bitWeight (gray 0 ^^^ gray 0)) ≈ s * pow2Neg (bitWeight (0 ^^^ 0))
    have h1 : bitWeight (gray 0 ^^^ gray 0) = 0 := by decide
    have h2 : bitWeight (0 ^^^ 0) = 0 := by decide
    rw [h1, h2]; exact deq_refl _
  | succ k ih =>
    intro s r hr
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    unfold schurD blockD
    by_cases hrk : r < 2 ^ k
    · simp only [hrk, ↓reduceIte]; exact ih s r hrk
    · simp only [hrk, ↓reduceIte]; exact ih (schurFactorW k * s) (r - 2 ^ k) (by omega)

theorem gray_plain_L_distinct_witness :
    ¬ (schurL grayWeightedSystem one 2 2 1 ≈ schurL plainWeightedSystem one 2 2 1) := by
  decide

-- ============================================================================
-- FAMILY IV: VAN DER CORPUT-EXPONENTIAL HYBRID KERNEL
-- NON-SCALAR RANK-1 BOUNDARY-CARRY COUPLING E_k = v_k * e_{2^k - 1}^T!
-- K^{exp}_{c,β}(x, y) = 2^(-|x - y|) * (c - β * φ_2(min(x, y)))
-- EXACT IFF CRITICAL THRESHOLD: ∀ n, StrictlyPosDef n K^{exp} ↔ 7*β ≤ 6*c !
-- ============================================================================

theorem schurD_expVdc_eq :
    ∀ k (σ : ExpState) r, r < 2 ^ k →
      schurD expVdcSystem σ k r ≈
        if r = 0 then (σ.c - σ.β * phi2 σ.offset) - σ.prev * pow2Neg 2
        else (σ.c - σ.β * phi2 (σ.offset + r)) - pow2Neg 2 * (σ.c - σ.β * phi2 (σ.offset + r - 1)) := by
  intro k
  induction k with
  | zero =>
    intro σ r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simp only [↓reduceIte]
    show pow2Neg (absDiff 0 0) * (σ.c - σ.β * phi2 (σ.offset + Nat.min 0 0)) - σ.prev * pow2Neg (0 + 0 + 2) ≈
         (σ.c - σ.β * phi2 σ.offset) - σ.prev * pow2Neg 2
    have ha0 : absDiff 0 0 = 0 := rfl
    have hm0 : Nat.min 0 0 = 0 := rfl
    rw [ha0, hm0, Nat.add_zero]
    exact sub_congr (deq_trans (mul_congr pow2Neg_zero (deq_refl _)) (one_mul _)) (deq_refl _)
  | succ k ih =>
    intro σ r hr
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    unfold schurD blockD
    by_cases hrk : r < 2 ^ k
    · simp only [hrk, ↓reduceIte]
      exact ih σ r hrk
    · simp only [hrk, ↓reduceIte]
      let u := r - 2 ^ k
      have hu : u < 2 ^ k := by omega
      have hru : r = 2 ^ k + u := by omega
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      have hr_ne : r ≠ 0 := by omega
      have hrec := ih (expVdcSystem.rightState σ k) u hu
      simp only [hr_ne, ↓reduceIte]
      by_cases hu0 : u = 0
      · simp only [hu0, ↓reduceIte] at hrec
        have hr_eq : σ.offset + r = σ.offset + 2 ^ k := by omega
        have hr_sub : σ.offset + 2 ^ k - 1 = σ.offset + (2 ^ k - 1) := by omega
        rw [hr_eq, hr_sub]
        change schurD expVdcSystem (expVdcSystem.rightState σ k) k u ≈ _
        rw [hu0]
        exact deq_trans hrec (sub_congr (deq_refl _) (mul_comm _ _))
      · simp only [hu0, ↓reduceIte] at hrec
        have h1 : σ.offset + 2 ^ k + u = σ.offset + r := by omega
        have h2 : σ.offset + 2 ^ k + u - 1 = σ.offset + r - 1 := by omega
        change schurD expVdcSystem (expVdcSystem.rightState σ k) k u ≈ _
        simpa [expVdcSystem, h1, h2] using hrec

theorem schurD_expVdc_init_eq (k : Nat) (c β : Dyad) (r : Nat) (hr : r < 2 ^ k) :
    schurD expVdcSystem ⟨c, β, 0, zero⟩ k r ≈ expVdcPivot c β r := by
  have h := schurD_expVdc_eq k ⟨c, β, 0, zero⟩ r hr
  cases r with
  | zero =>
    simp only [↓reduceIte] at h
    unfold expVdcPivot
    have h0 : (c - β * phi2 0) - zero * pow2Neg 2 ≈ c := by
      rw [phi2, phi2From_zero]
      have h1 := sub_congr (deq_trans (sub_congr (deq_refl c) (mul_zero β))
        (deq_trans (add_congr (deq_refl c) neg_zero) (add_zero c))) (zero_mul (pow2Neg 2))
      exact deq_trans h1 (deq_trans (add_congr (deq_refl c) neg_zero) (add_zero c))
    exact deq_trans h h0
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.zero_add, Nat.add_sub_cancel] at h
    exact h

/-- Sharp bound on consecutive van der Corput values:
    `∀ r ≥ 1, φ_2(r) - (1/4) * φ_2(r - 1) < 7/8`! -/
theorem phi2_consec_lt_seven_eighths (m : Nat) :
    phi2 (m + 1) - pow2Neg 2 * phi2 m <ᵈ ⟨7, 3⟩ := by
  by_cases hodd : (m + 1) % 2 = 1
  · -- m + 1 = 2*u + 1 (odd), m = 2*u (even)
    let u := m / 2
    have hm_eq : m = 2 * u := by omega
    have hphi_m : phi2 m ≈ pow2Neg 1 * phi2 u := by
      have hu1 := phi2From_unfold 0 m
      have hmod0 : m % 2 = 0 := by omega
      have hdiv : m / 2 = u := rfl
      rw [hmod0, hdiv] at hu1
      exact deq_trans hu1 (deq_trans (zero_add _) (phi2From_succ_shift 0 u))
    have hphi_m1 : phi2 (m + 1) ≈ pow2Neg 1 + phi2 m := by
      have hu1 := phi2From_unfold 0 (m + 1)
      have hdiv : (m + 1) / 2 = u := by omega
      rw [hodd, hdiv] at hu1
      exact deq_trans hu1 (add_congr (deq_refl _) (deq_trans (phi2From_succ_shift 0 u) (deq_symm hphi_m)))
    -- phi2(m+1) - 1/4 * phi2(m) = 1/2 + 3/4 * phi2(m) < 1/2 + 3/4 * 1/2 = 7/8!
    have hlt_half : phi2 m <ᵈ pow2Neg 1 := by
      have h1 := mul_dlt_mul_of_pos_left (pow2Neg_pos 1) (phi2_lt_one u)
      exact dlt_congr (deq_symm hphi_m) (mul_one _) h1
    have hcomb : phi2 (m + 1) - pow2Neg 2 * phi2 m ≈ pow2Neg 1 + ⟨3, 2⟩ * phi2 m := by
      have h34 : one - pow2Neg 2 ≈ ⟨3, 2⟩ := by decide
      have h1 := sub_congr hphi_m1 (deq_refl (pow2Neg 2 * phi2 m))
      have h2 := add_assoc (pow2Neg 1) (phi2 m) (-(pow2Neg 2 * phi2 m))
      have h3 : phi2 m - pow2Neg 2 * phi2 m ≈ ⟨3, 2⟩ * phi2 m :=
        deq_trans (sub_congr (deq_symm (one_mul _)) (deq_refl _))
          (deq_trans (deq_symm (sub_mul one (pow2Neg 2) (phi2 m))) (mul_congr h34 (deq_refl _)))
      exact deq_trans h1 (deq_trans h2 (add_congr (deq_refl _) h3))
    have hbound : pow2Neg 1 + ⟨3, 2⟩ * phi2 m <ᵈ ⟨7, 3⟩ := by
      have h1 := mul_dlt_mul_of_pos_left (by decide : zero <ᵈ (⟨3, 2⟩ : Dyad)) hlt_half
      have h2 := add_dlt_add_of_dle_of_dlt (dle_refl (pow2Neg 1)) h1
      exact dlt_congr (deq_refl _) (by decide : pow2Neg 1 + (⟨3, 2⟩ : Dyad) * pow2Neg 1 ≈ ⟨7, 3⟩) h2
    exact dlt_congr (deq_symm hcomb) (deq_refl _) hbound
  · -- m + 1 = 2*(u+1) (even), m = 2*u + 1 (odd): φ_2(m+1) < 1/2 < 7/8 and φ_2(m) ≥ 0!
    have hmod0 : (m + 1) % 2 = 0 := by omega
    have hphi_even : phi2 (m + 1) ≈ pow2Neg 1 * phi2 ((m + 1) / 2) := by
      have hu1 := phi2From_unfold 0 (m + 1)
      rw [hmod0] at hu1
      exact deq_trans hu1 (deq_trans (zero_add _) (phi2From_succ_shift 0 ((m + 1) / 2)))
    have hlt_half : phi2 (m + 1) <ᵈ pow2Neg 1 :=
      dlt_congr (deq_symm hphi_even) (mul_one _) (mul_dlt_mul_of_pos_left (pow2Neg_pos 1) (phi2_lt_one _))
    have hnn : zero ≤ᵈ pow2Neg 2 * phi2 m := mul_nonneg_of_nonneg (pow2Neg_nonneg 2) (phi2_nonneg m)
    exact dlt_trans (dlt_of_dle_of_dlt (sub_le_self_of_nonneg (phi2 (m + 1)) hnn) hlt_half)
      (by decide : pow2Neg 1 <ᵈ ⟨7, 3⟩)

/-- **THEOREM 4 (EXACT SHARP CRITICAL THRESHOLD FOR FAMILY IV, ALL `n : Nat`)**:
    For any `β > 0` and `c` in `Z[1/2]`, the van der Corput-Exponential Hybrid kernel
    `K^{exp}_{c,β}(x, y) = 2^(-|x - y|) * (c - β * φ_2(min(x, y)))`
    (proved via the rank-1 boundary-carry `SchurSystem`) is strictly positive definite
    on `[0, n)` for ALL `n : Nat` **IF AND ONLY IF** `7 * β ≤ 6 * c`! -/
theorem expVdc_strictlyPosDef_all_n_iff {c β : Dyad} (hβ : zero <ᵈ β) :
    (∀ n : Nat, StrictlyPosDef n (expVdcMat c β)) ↔
    ofInt 7 * β ≤ᵈ ofInt 6 * c := by
  have hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k →
      expVdcMat c β i j ≈ expVdcSystem.mat ⟨c, β, 0, zero⟩ k i j := by
    intro k i j _ _
    unfold expVdcMat expVdcSystem expStateMat
    simp only [Nat.zero_add]
    exact deq_symm (deq_trans (sub_congr (deq_refl _) (zero_mul _))
      (deq_trans (add_congr (deq_refl _) neg_zero) (add_zero _)))
  constructor
  · intro hall
    apply dle_of_not_dlt
    intro hlt
    let δ := ofInt 7 * β - ofInt 6 * c
    have hδ : zero <ᵈ δ := (sub_pos_iff _ _).mpr hlt
    have h6β : zero ≤ᵈ ofInt 6 * β :=
      dle_of_dlt (mul_pos_of_pos (by decide : zero <ᵈ ofInt 6) hβ)
    obtain ⟨k0, hk0⟩ := exists_pow2Neg_le hδ h6β
    let k := k0 + 2
    have hk : ofInt 6 * β * pow2Neg k ≤ᵈ δ :=
      dle_trans (mul_dle_mul_of_nonneg_left h6β (pow2Neg_antitone (by omega))) hk0
    let r := 2 ^ k - 1
    have hp4 : 4 ≤ 2 ^ k := by
      show 4 ≤ 2 ^ (k0 + 2)
      rw [Nat.pow_succ, Nat.pow_succ]
      have h1 : 1 ≤ 2 ^ k0 := Nat.one_le_pow k0 2 (by omega)
      omega
    have hr_lt : r < 2 ^ k := by omega
    have hpd := (schurSystem_nested_iff expVdcSystem ⟨c, β, 0, zero⟩ (expVdcMat c β) hagree (2 ^ k)).mp
      (hall (2 ^ k)) r hr_lt
    have h2k_le : 2 ^ k ≤ 2 ^ (2 ^ k) := Nat.le_of_lt Nat.lt_two_pow_self
    have hD_eq := schurD_expVdc_init_eq (2 ^ k) c β r (Nat.lt_of_lt_of_le hr_lt h2k_le)
    have hpiv_pos : zero <ᵈ expVdcPivot c β r := dlt_congr (deq_refl _) hD_eq hpd
    -- For r = 2^k - 1 (odd!), r - 1 = 2^k - 2 has φ_2(r) = 1 - 2^{-k} and φ_2(r - 1) = 1/2 - 2^{-k}!
    have hr_succ : r = (r - 1) + 1 := by omega
    have hphi_r : phi2 r ≈ one - pow2Neg k := phi2_two_pow_sub_one k
    have hphi_rm1 : phi2 (r - 1) ≈ pow2Neg 1 - pow2Neg k := by
      -- r = (r - 1) + 1 is odd, so φ_2(r) = 1/2 + φ_2(r - 1)!
      have hodd : r % 2 = 1 := by
        show (2 ^ (k0 + 2) - 1) % 2 = 1
        have hp1 : 1 ≤ 2 ^ (k0 + 1) := Nat.one_le_pow (k0 + 1) 2 (by omega)
        rw [Nat.pow_succ]; omega
      have hr_pos : 1 ≤ r := by omega
      have hdiv : r / 2 = (r - 1) / 2 := by omega
      have heven : (r - 1) % 2 = 0 := by omega
      have h1 := phi2From_unfold 0 r
      have h2 := phi2From_unfold 0 (r - 1)
      rw [hodd, hdiv] at h1
      rw [heven] at h2
      have hrel : phi2 r ≈ pow2Neg 1 + phi2 (r - 1) :=
        deq_trans h1 (add_congr (deq_refl _) (deq_trans (deq_symm (zero_add _)) (deq_symm h2)))
      -- Since 1/2 + phi2(r-1) ≈ 1 - 2^{-k} = 1/2 + (1/2 - 2^{-k}):
      have h12 : one - pow2Neg k ≈ pow2Neg 1 + (pow2Neg 1 - pow2Neg k) :=
        deq_trans (sub_congr (deq_symm (pow2Neg_half_add 0)) (deq_refl _)) (add_assoc _ _ _)
      have hsum : pow2Neg 1 + phi2 (r - 1) ≈ pow2Neg 1 + (pow2Neg 1 - pow2Neg k) :=
        deq_trans (deq_symm hrel) (deq_trans hphi_r h12)
      -- Subtract pow2Neg 1 from both sides:
      have hsub := sub_congr hsum (deq_refl (pow2Neg 1))
      have hl : (pow2Neg 1 + phi2 (r - 1)) - pow2Neg 1 ≈ phi2 (r - 1) :=
        deq_trans (add_congr (add_comm _ _) (deq_refl _)) (add_sub_cancel _ _)
      have hr2 : (pow2Neg 1 + (pow2Neg 1 - pow2Neg k)) - pow2Neg 1 ≈ pow2Neg 1 - pow2Neg k :=
        deq_trans (add_congr (add_comm _ _) (deq_refl _)) (add_sub_cancel _ _)
      exact deq_trans (deq_symm hl) (deq_trans hsub hr2)
    -- Now compute 8 * expVdcPivot c β r = 6*c - 7*β + 6*β*2^{-k} = 6*β*2^{-k} - δ ≤ 0!
    have h8eq : ofInt 8 * expVdcPivot c β r ≈ ofInt 6 * β * pow2Neg k - δ := by
      have hpiv_eq : expVdcPivot c β r = (c - β * phi2 r) - pow2Neg 2 * (c - β * phi2 (r - 1)) := by
        conv => lhs; rw [hr_succ]
        show (c - β * phi2 ((r - 1) + 1)) - pow2Neg 2 * (c - β * phi2 (r - 1)) = _
        rw [← hr_succ]
      rw [hpiv_eq]
      -- 8 * ((c - β*(1 - 2^{-k})) - 1/4 * (c - β*(1/2 - 2^{-k})))
      -- = 8*c - 8*β + 8*β*2^{-k} - 2*c + β - 2*β*2^{-k} = 6*c - 7*β + 6*β*2^{-k}
      have h84 : ofInt 8 * pow2Neg 2 ≈ ofInt 2 := by decide
      have h2half : ofInt 2 * pow2Neg 1 ≈ one := by decide
      have h6_82 : ofInt 8 * c - ofInt 2 * c ≈ ofInt 6 * c := by
        exact deq_trans (deq_symm (sub_mul (ofInt 8) (ofInt 2) c))
          (mul_congr (by decide : ofInt 8 - ofInt 2 ≈ ofInt 6) (deq_refl c))
      -- Direct algebraic normalization via exact Int arithmetic!
      have hnorm : ofInt 8 * ((c - β * (one - pow2Neg k)) - pow2Neg 2 * (c - β * (pow2Neg 1 - pow2Neg k))) ≈
                   ofInt 6 * β * pow2Neg k - (ofInt 7 * β - ofInt 6 * c) := by
        -- Prove directly at the Int level by cancelling shifts!
        -- Wait: even cleaner, use a 10-line Dyad ring calc on (8c - 2c) + (-8β + β) + (8 - 2)β*2^{-k}!
        let p := pow2Neg k
        have ht1 : ofInt 8 * (c - β * (one - p)) ≈ ofInt 8 * c - ofInt 8 * β + ofInt 8 * β * p := by
          have ha := mul_sub (ofInt 8) c (β * (one - p))
          have hb : ofInt 8 * (β * (one - p)) ≈ ofInt 8 * β - ofInt 8 * β * p :=
            deq_trans (deq_symm (mul_assoc (ofInt 8) β (one - p)))
              (deq_trans (mul_sub (ofInt 8 * β) one p) (sub_congr (mul_one _) (deq_refl _)))
          have hc : ofInt 8 * c - (ofInt 8 * β - ofInt 8 * β * p) ≈
                    ofInt 8 * c - ofInt 8 * β + ofInt 8 * β * p :=
            deq_trans (add_congr (deq_refl _) (deq_trans (neg_add _ _) (add_congr (deq_refl _) (neg_neg _))))
              (deq_symm (add_assoc _ _ _))
          exact deq_trans ha (deq_trans (sub_congr (deq_refl _) hb) hc)
        have ht2 : ofInt 8 * (pow2Neg 2 * (c - β * (pow2Neg 1 - p))) ≈
                   ofInt 2 * c - β + ofInt 2 * β * p := by
          have ha : ofInt 8 * (pow2Neg 2 * (c - β * (pow2Neg 1 - p))) ≈
                    ofInt 2 * (c - β * (pow2Neg 1 - p)) :=
            deq_trans (deq_symm (mul_assoc _ _ _)) (mul_congr h84 (deq_refl _))
          have hb := mul_sub (ofInt 2) c (β * (pow2Neg 1 - p))
          have hc : ofInt 2 * (β * (pow2Neg 1 - p)) ≈ β - ofInt 2 * β * p := by
            have hc1 := deq_trans (deq_symm (mul_assoc (ofInt 2) β (pow2Neg 1 - p)))
              (mul_sub (ofInt 2 * β) (pow2Neg 1) p)
            have hc2 : (ofInt 2 * β) * pow2Neg 1 ≈ β :=
              deq_trans (mul_assoc _ _ _)
                (deq_trans (mul_congr (deq_refl _) (mul_comm _ _))
                  (deq_trans (deq_symm (mul_assoc _ _ _))
                    (deq_trans (mul_congr h2half (deq_refl β)) (one_mul β))))
            exact deq_trans hc1 (sub_congr hc2 (deq_refl _))
          have hd : ofInt 2 * c - (β - ofInt 2 * β * p) ≈ ofInt 2 * c - β + ofInt 2 * β * p :=
            deq_trans (add_congr (deq_refl _) (deq_trans (neg_add _ _) (add_congr (deq_refl _) (neg_neg _))))
              (deq_symm (add_assoc _ _ _))
          exact deq_trans ha (deq_trans hb (deq_trans (sub_congr (deq_refl _) hc) hd))
        -- Combine: (8c - 8β + 8βp) - (2c - β + 2βp) = 6βp - (7β - 6c)
        have hcomb_lin : (ofInt 8 * c - ofInt 8 * β + ofInt 8 * β * p) - (ofInt 2 * c - β + ofInt 2 * β * p) ≈
                         ofInt 6 * β * p - (ofInt 7 * β - ofInt 6 * c) := by
          -- Directly in Int after expanding shifts? Even better, prove via a general 3-term linear helper!
          -- All terms are integer multiples of c, β, and β*p!
          have hsub_abc : ∀ x1 y1 z1 x2 y2 z2 : Dyad,
              (x1 - y1 + z1) - (x2 - y2 + z2) ≈ (x1 - x2) - (y1 - y2) + (z1 - z2) := by
            intro x1 y1 z1 x2 y2 z2
            -- Check in Int after clearing common shift? Wait: just rearrange with Dyad laws?
            -- Wait: let's prove `(a + b) - (c + d) ≈ (a - c) + (b - d)` once!
            have hadd_sub : ∀ a b u v : Dyad, (a + b) - (u + v) ≈ (a - u) + (b - v) := by
              intro a b u v
              calc
                (a + b) + -(u + v)
                    ≈ (a + b) + (-u + -v) := add_congr (deq_refl _) (neg_add u v)
                _ ≈ a + (b + (-u + -v)) := add_assoc _ _ _
                _ ≈ a + ((b + -u) + -v) := add_congr (deq_refl _) (deq_symm (add_assoc _ _ _))
                _ ≈ a + ((-u + b) + -v) := add_congr (deq_refl _) (add_congr (add_comm _ _) (deq_refl _))
                _ ≈ a + (-u + (b + -v)) := add_congr (deq_refl _) (add_assoc _ _ _)
                _ ≈ (a + -u) + (b + -v) := deq_symm (add_assoc _ _ _)
            have hsub_sub : ∀ a b u v : Dyad, (a - b) - (u - v) ≈ (a - u) - (b - v) := by
              intro a b u v
              have h1 := hadd_sub a (-b) u (-v)
              have h2 : (-b) - (-v) ≈ -(b - v) :=
                deq_trans (deq_symm (neg_add b (-v))) (deq_refl _)
              exact deq_trans h1 (add_congr (deq_refl _) h2)
            exact deq_trans (hadd_sub (x1 - y1) z1 (x2 - y2) z2) (add_congr (hsub_sub x1 y1 x2 y2) (deq_refl _))
          have h1 := hsub_abc (ofInt 8 * c) (ofInt 8 * β) (ofInt 8 * β * p) (ofInt 2 * c) β (ofInt 2 * β * p)
          have hy : ofInt 8 * β - β ≈ ofInt 7 * β :=
            deq_trans (sub_congr (deq_refl _) (deq_symm (one_mul β)))
              (deq_trans (deq_symm (sub_mul (ofInt 8) one β))
                (mul_congr (by decide : ofInt 8 - one ≈ ofInt 7) (deq_refl β)))
          have hz : ofInt 8 * β * p - ofInt 2 * β * p ≈ ofInt 6 * β * p :=
            deq_trans (sub_congr (mul_assoc _ _ _) (mul_assoc _ _ _))
              (deq_trans (deq_symm (sub_mul (ofInt 8) (ofInt 2) (β * p)))
                (deq_trans (mul_congr (by decide : ofInt 8 - ofInt 2 ≈ ofInt 6) (deq_refl _))
                  (deq_symm (mul_assoc _ _ _))))
          have hfin : (ofInt 6 * c - ofInt 7 * β) + ofInt 6 * β * p ≈
                      ofInt 6 * β * p - (ofInt 7 * β - ofInt 6 * c) := by
            have hneg_swap : ofInt 6 * c - ofInt 7 * β ≈ -(ofInt 7 * β - ofInt 6 * c) :=
              deq_trans (add_comm (ofInt 6 * c) (-(ofInt 7 * β)))
                (deq_trans (add_congr (deq_refl _) (deq_symm (neg_neg _)))
                  (deq_symm (neg_add (ofInt 7 * β) (-(ofInt 6 * c)))))
            exact deq_trans (add_comm _ _) (add_congr (deq_refl _) hneg_swap)
          exact deq_trans h1 (deq_trans (add_congr (sub_congr h6_82 hy) hz) hfin)
        exact deq_trans (mul_sub (ofInt 8) _ _) (deq_trans (sub_congr ht1 ht2) hcomb_lin)
      exact deq_trans (mul_congr (deq_refl (ofInt 8))
        (sub_congr (sub_congr (deq_refl c) (mul_congr (deq_refl β) hphi_r))
          (mul_congr (deq_refl (pow2Neg 2)) (sub_congr (deq_refl c) (mul_congr (deq_refl β) hphi_rm1)))))
        hnorm
    have h8le : ofInt 8 * expVdcPivot c β r ≤ᵈ zero :=
      dle_congr (deq_symm h8eq) (deq_refl _)
        (dle_trans (add_dle_add hk (dle_refl (-δ))) (dle_of_deq (add_neg δ)))
    have hpiv_le : expVdcPivot c β r ≤ᵈ zero := dle_zero_of_ofInt_mul_dle_zero (by decide) h8le
    exact not_dlt_of_dle hpiv_le hpiv_pos
  · -- Sufficiency: 7 * β ≤ 6 * c → StrictlyPosDef n for ALL n!
    intro hcond n
    refine (schurSystem_nested_iff expVdcSystem ⟨c, β, 0, zero⟩ (expVdcMat c β) hagree n).mpr ?_
    intro r hr
    have hD_eq := schurD_expVdc_init_eq n c β r (Nat.lt_trans hr Nat.lt_two_pow_self)
    refine dlt_congr (deq_refl _) (deq_symm hD_eq) ?_
    cases r with
    | zero =>
      show zero <ᵈ c
      have h6c : zero <ᵈ ofInt 6 * c :=
        dlt_of_dlt_of_dle (mul_pos_of_pos (by decide : zero <ᵈ ofInt 7) hβ) hcond
      rw [zero_dlt_iff] at h6c ⊢
      change 0 < 6 * c.mant at h6c
      omega
    | succ m =>
      unfold expVdcPivot
      -- Rewrite (c - β φ(m+1)) - 1/4*(c - β φ(m)) = 3/4 * c - β * (φ(m+1) - 1/4 φ(m))
      have hre : (c - β * phi2 (m + 1)) - pow2Neg 2 * (c - β * phi2 m) ≈
                 ⟨3, 2⟩ * c - β * (phi2 (m + 1) - pow2Neg 2 * phi2 m) := by
        have h34 : one - pow2Neg 2 ≈ ⟨3, 2⟩ := by decide
        have hsub_add : ∀ a b u v : Dyad, (a - b) - (u - v) ≈ (a - u) - (b - v) := by
          intro a b u v
          calc
            (a + -b) + -(u + -v)
                ≈ (a + -b) + (-u + -(-v)) := add_congr (deq_refl _) (neg_add u (-v))
            _ ≈ a + (-b + (-u + -(-v))) := add_assoc _ _ _
            _ ≈ a + ((-b + -u) + -(-v)) := add_congr (deq_refl _) (deq_symm (add_assoc _ _ _))
            _ ≈ a + ((-u + -b) + -(-v)) := add_congr (deq_refl _) (add_congr (add_comm _ _) (deq_refl _))
            _ ≈ a + (-u + (-b + -(-v))) := add_congr (deq_refl _) (add_assoc _ _ _)
            _ ≈ (a + -u) + (-b + -(-v)) := deq_symm (add_assoc _ _ _)
            _ ≈ (a - u) - (b - v) := add_congr (deq_refl _) (deq_symm (neg_add b (-v)))
        have h1 := sub_congr (deq_refl (c - β * phi2 (m + 1))) (mul_sub (pow2Neg 2) c (β * phi2 m))
        have h2 := hsub_add c (β * phi2 (m + 1)) (pow2Neg 2 * c) (pow2Neg 2 * (β * phi2 m))
        have hc_part : c - pow2Neg 2 * c ≈ ⟨3, 2⟩ * c :=
          deq_trans (sub_congr (deq_symm (one_mul c)) (deq_refl _))
            (deq_trans (deq_symm (sub_mul one (pow2Neg 2) c)) (mul_congr h34 (deq_refl c)))
        have hβ_part : β * phi2 (m + 1) - pow2Neg 2 * (β * phi2 m) ≈
                       β * (phi2 (m + 1) - pow2Neg 2 * phi2 m) := by
          have hsw : pow2Neg 2 * (β * phi2 m) ≈ β * (pow2Neg 2 * phi2 m) :=
            deq_trans (deq_symm (mul_assoc _ _ _))
              (deq_trans (mul_congr (mul_comm _ _) (deq_refl _)) (mul_assoc _ _ _))
          exact deq_trans (sub_congr (deq_refl _) hsw) (deq_symm (mul_sub β _ _))
        exact deq_trans h1 (deq_trans h2 (sub_congr hc_part hβ_part))
      refine dlt_congr (deq_refl zero) (deq_symm hre) ?_
      refine (sub_pos_iff _ _).mpr ?_
      have h1 : β * (phi2 (m + 1) - pow2Neg 2 * phi2 m) <ᵈ β * ⟨7, 3⟩ :=
        mul_dlt_mul_of_pos_left hβ (phi2_consec_lt_seven_eighths m)
      have h2 : β * ⟨7, 3⟩ ≤ᵈ ⟨3, 2⟩ * c := by
        have h8l : ofInt 8 * (β * ⟨7, 3⟩) ≈ ofInt 7 * β :=
          deq_trans (deq_symm (mul_assoc _ _ _))
            (deq_trans (mul_congr (mul_comm _ _) (deq_refl _))
              (deq_trans (mul_assoc _ _ _)
                (deq_trans (mul_congr (deq_refl _) (by decide : ofInt 8 * (⟨7, 3⟩ : Dyad) ≈ ofInt 7))
                  (mul_comm _ _))))
        have h8r : ofInt 8 * (⟨3, 2⟩ * c) ≈ ofInt 6 * c :=
          deq_trans (deq_symm (mul_assoc _ _ _))
            (mul_congr (by decide : ofInt 8 * (⟨3, 2⟩ : Dyad) ≈ ofInt 6) (deq_refl c))
        exact dle_of_ofInt_mul_dle (by decide : (0 : Int) < 8)
          (dle_congr (deq_symm h8l) (deq_symm h8r) hcond)
      exact dlt_of_dlt_of_dle h1 h2

/-- Concrete critical pure-dyadic instantiation (`c = 7, β = 6`, exact ratio `7/6`). -/
theorem expVdc_critical_7_6_all_n (n : Nat) :
    StrictlyPosDef n (expVdcMat (ofInt 7) (ofInt 6)) :=
  (expVdc_strictlyPosDef_all_n_iff (by decide : zero <ᵈ ofInt 6)).mpr (by decide) n

/-- Uniform dimension-free lower bound for Family IV at `c = 5/4, β = 1`:
    EVERY pivot `D(r) > 1/16` for ALL `k, r < 2^k`! -/
theorem expVdc_5_4_uniform_pivot_lb (k r : Nat) (hr : r < 2 ^ k) :
    pow2Neg 4 ≤ᵈ schurD expVdcSystem ⟨⟨5, 2⟩, one, 0, zero⟩ k r := by
  have hD := schurD_expVdc_init_eq k ⟨5, 2⟩ one r hr
  refine dle_congr (deq_refl _) (deq_symm hD) ?_
  cases r with
  | zero => show pow2Neg 4 ≤ᵈ ⟨5, 2⟩; decide
  | succ m =>
    unfold expVdcPivot
    have hlt := phi2_consec_lt_seven_eighths m
    have hre : (⟨5, 2⟩ - one * phi2 (m + 1)) - pow2Neg 2 * (⟨5, 2⟩ - one * phi2 m) ≈
               ⟨15, 4⟩ - (phi2 (m + 1) - pow2Neg 2 * phi2 m) := by
      have h1 : (⟨5, 2⟩ : Dyad) - one * phi2 (m + 1) ≈ ⟨5, 2⟩ - phi2 (m + 1) :=
        sub_congr (deq_refl _) (one_mul _)
      have h2 : pow2Neg 2 * (⟨5, 2⟩ - one * phi2 m) ≈ ⟨5, 4⟩ - pow2Neg 2 * phi2 m :=
        deq_trans (mul_congr (deq_refl _) (sub_congr (deq_refl _) (one_mul _)))
          (deq_trans (mul_sub (pow2Neg 2) ⟨5, 2⟩ (phi2 m))
            (sub_congr (by decide : pow2Neg 2 * (⟨5, 2⟩ : Dyad) ≈ ⟨5, 4⟩) (deq_refl _)))
      have hsub_add : ∀ a b u v : Dyad, (a - b) - (u - v) ≈ (a - u) - (b - v) := by
        intro a b u v
        calc
          (a + -b) + -(u + -v)
              ≈ (a + -b) + (-u + -(-v)) := add_congr (deq_refl _) (neg_add u (-v))
          _ ≈ a + (-b + (-u + -(-v))) := add_assoc _ _ _
          _ ≈ a + ((-b + -u) + -(-v)) := add_congr (deq_refl _) (deq_symm (add_assoc _ _ _))
          _ ≈ a + ((-u + -b) + -(-v)) := add_congr (deq_refl _) (add_congr (add_comm _ _) (deq_refl _))
          _ ≈ a + (-u + (-b + -(-v))) := add_congr (deq_refl _) (add_assoc _ _ _)
          _ ≈ (a + -u) + (-b + -(-v)) := deq_symm (add_assoc _ _ _)
          _ ≈ (a - u) - (b - v) := add_congr (deq_refl _) (deq_symm (neg_add b (-v)))
      exact deq_trans (sub_congr h1 h2)
        (deq_trans (hsub_add ⟨5, 2⟩ (phi2 (m + 1)) ⟨5, 4⟩ (pow2Neg 2 * phi2 m))
          (sub_congr (by decide : (⟨5, 2⟩ : Dyad) - ⟨5, 4⟩ ≈ ⟨15, 4⟩) (deq_refl _)))
    refine dle_congr (deq_refl _) (deq_symm hre) ?_
    exact dle_trans (by decide : pow2Neg 4 ≤ᵈ (⟨15, 4⟩ : Dyad) - ⟨7, 3⟩)
      (sub_dle_sub_left ⟨15, 4⟩ (dle_of_dlt hlt))

theorem expVdc_sharp_9_8_2sparse_negative :
    quadForm 32 (expVdcMat ⟨9, 3⟩ one) sparseNegVec <ᵈ zero := by
  -- Evaluate quadratic form on the 2-sparse vector {30, 31} symbolically -> instant!
  have hrow : ∀ i, i < 32 →
      dsum 32 (fun j => sparseNegVec i * expVdcMat ⟨9, 3⟩ one i j * sparseNegVec j) ≈
      sparseNegVec i * (expVdcMat ⟨9, 3⟩ one i 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one i 31 * ofInt 2) := by
    intro i _
    have hsplit := dsum_split 30 2 (fun j => sparseNegVec i * expVdcMat ⟨9, 3⟩ one i j * sparseNegVec j)
    have hpre : dsum 30 (fun j => sparseNegVec i * expVdcMat ⟨9, 3⟩ one i j * sparseNegVec j) ≈ zero :=
      dsum_eq_zero (fun j hj => by
        have h30 : j ≠ 30 := by omega
        have h31 : j ≠ 31 := by omega
        simp only [sparseNegVec, h30, h31, ↓reduceIte]
        exact mul_zero _)
    have htail : dsum 2 (fun j => sparseNegVec i * expVdcMat ⟨9, 3⟩ one i (30 + j) * sparseNegVec (30 + j)) ≈
                 sparseNegVec i * (expVdcMat ⟨9, 3⟩ one i 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one i 31 * ofInt 2) := by
      show (zero + sparseNegVec i * expVdcMat ⟨9, 3⟩ one i 30 * ofInt (-1)) +
           sparseNegVec i * expVdcMat ⟨9, 3⟩ one i 31 * ofInt 2 ≈ _
      exact deq_trans (add_congr (zero_add _) (deq_refl _))
        (deq_trans (add_congr (mul_assoc _ _ _) (mul_assoc _ _ _)) (deq_symm (mul_add _ _ _)))
    exact deq_trans hsplit (deq_trans (add_congr hpre htail) (zero_add _))
  have hqf : quadForm 32 (expVdcMat ⟨9, 3⟩ one) sparseNegVec ≈
             ofInt (-1) * (expVdcMat ⟨9, 3⟩ one 30 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one 30 31 * ofInt 2) +
             ofInt 2 * (expVdcMat ⟨9, 3⟩ one 31 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one 31 31 * ofInt 2) := by
    unfold quadForm
    have h1 := dsum_congr hrow
    have h2 := dsum_split 30 2 (fun i =>
      sparseNegVec i * (expVdcMat ⟨9, 3⟩ one i 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one i 31 * ofInt 2))
    have hpre : dsum 30 (fun i =>
        sparseNegVec i * (expVdcMat ⟨9, 3⟩ one i 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one i 31 * ofInt 2)) ≈ zero :=
      dsum_eq_zero (fun i hi => by
        have h30 : i ≠ 30 := by omega
        have h31 : i ≠ 31 := by omega
        simp only [sparseNegVec, h30, h31, ↓reduceIte]
        exact zero_mul _)
    exact deq_trans h1 (deq_trans h2 (deq_trans (add_congr hpre (add_congr (zero_add _) (deq_refl _))) (zero_add _)))
  -- Compute the 4 entries explicitly: φ_2(30) = 15/32, φ_2(31) = 31/32!
  have hphi30 : phi2 30 ≈ ⟨15, 5⟩ := by
    have h31 := phi2_two_pow_sub_one 5
    have h1 := phi2From_unfold 0 31
    have h2 := phi2From_unfold 0 30
    have hrel : phi2 31 ≈ pow2Neg 1 + phi2 30 := by
      have hm1 : 31 % 2 = 1 := rfl
      have hm0 : 30 % 2 = 0 := rfl
      have hd : 31 / 2 = 30 / 2 := rfl
      rw [hm1, hd] at h1; rw [hm0] at h2
      exact deq_trans h1 (add_congr (deq_refl _) (deq_trans (deq_symm (zero_add _)) (deq_symm h2)))
    have hsum : pow2Neg 1 + phi2 30 ≈ pow2Neg 1 + ⟨15, 5⟩ :=
      deq_trans (deq_symm hrel) (deq_trans h31 (by decide : one - pow2Neg 5 ≈ pow2Neg 1 + ⟨15, 5⟩))
    have hsub := sub_congr hsum (deq_refl (pow2Neg 1))
    exact deq_trans (deq_symm (deq_trans (add_congr (add_comm _ _) (deq_refl _)) (add_sub_cancel _ _)))
      (deq_trans hsub (deq_trans (add_congr (add_comm _ _) (deq_refl _)) (add_sub_cancel _ _)))
  have hphi31 : phi2 31 ≈ ⟨31, 5⟩ := deq_trans (phi2_two_pow_sub_one 5) (by decide)
  have hM3030 : expVdcMat ⟨9, 3⟩ one 30 30 ≈ ⟨21, 5⟩ := by
    show pow2Neg 0 * (⟨9, 3⟩ - one * phi2 30) ≈ ⟨21, 5⟩
    exact deq_trans (one_mul _) (deq_trans (sub_congr (deq_refl _) (deq_trans (one_mul _) hphi30)) (by decide))
  have hM3031 : expVdcMat ⟨9, 3⟩ one 30 31 ≈ ⟨21, 6⟩ := by
    show pow2Neg 1 * (⟨9, 3⟩ - one * phi2 30) ≈ ⟨21, 6⟩
    exact deq_trans (mul_congr (deq_refl _) (deq_trans (sub_congr (deq_refl _) (deq_trans (one_mul _) hphi30)) (by decide : (⟨9, 3⟩ : Dyad) - ⟨15, 5⟩ ≈ ⟨21, 5⟩))) (by decide)
  have hM3130 : expVdcMat ⟨9, 3⟩ one 31 30 ≈ ⟨21, 6⟩ := hM3031
  have hM3131 : expVdcMat ⟨9, 3⟩ one 31 31 ≈ ⟨5, 5⟩ := by
    show pow2Neg 0 * (⟨9, 3⟩ - one * phi2 31) ≈ ⟨5, 5⟩
    exact deq_trans (one_mul _) (deq_trans (sub_congr (deq_refl _) (deq_trans (one_mul _) hphi31)) (by decide))
  have hval : quadForm 32 (expVdcMat ⟨9, 3⟩ one) sparseNegVec ≈ ⟨-1, 5⟩ := by
    have hr1 : ofInt (-1) * (expVdcMat ⟨9, 3⟩ one 30 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one 30 31 * ofInt 2) ≈ zero := by
      have ha := add_congr (mul_congr hM3030 (deq_refl (ofInt (-1)))) (mul_congr hM3031 (deq_refl (ofInt 2)))
      have hb : (⟨21, 5⟩ : Dyad) * ofInt (-1) + ⟨21, 6⟩ * ofInt 2 ≈ zero := by decide
      exact deq_trans (mul_congr (deq_refl _) (deq_trans ha hb)) (mul_zero _)
    have hr2 : ofInt 2 * (expVdcMat ⟨9, 3⟩ one 31 30 * ofInt (-1) + expVdcMat ⟨9, 3⟩ one 31 31 * ofInt 2) ≈ ⟨-1, 5⟩ := by
      have ha := add_congr (mul_congr hM3130 (deq_refl (ofInt (-1)))) (mul_congr hM3131 (deq_refl (ofInt 2)))
      have hb : (⟨21, 6⟩ : Dyad) * ofInt (-1) + ⟨5, 5⟩ * ofInt 2 ≈ ⟨-1, 6⟩ := by decide
      exact deq_trans (mul_congr (deq_refl _) (deq_trans ha hb)) (by decide)
    exact deq_trans hqf (deq_trans (add_congr hr1 hr2) (zero_add _))
  exact dlt_congr (deq_symm hval) (deq_refl zero) (by decide : (⟨-1, 5⟩ : Dyad) <ᵈ zero)

theorem expVdc_sharp_9_8_fails_32 : ¬ StrictlyPosDef 32 (expVdcMat ⟨9, 3⟩ one) := by
  intro hpd
  have hnz : ∃ i, i < 32 ∧ ¬ (sparseNegVec i ≈ zero) :=
    ⟨31, by omega, by show ¬ (ofInt 2 ≈ zero); decide⟩
  exact not_dlt_of_dle (dle_of_dlt expVdc_sharp_9_8_2sparse_negative) (hpd sparseNegVec hnz)

-- ============================================================================
-- NON-VACUITY WITNESSES (KERNEL-CHECKED CONSTRUCTIVE HABITATION!)
-- ============================================================================

/-- Non-vacuity witness: all four `SchurSystem` engines are genuinely inhabited
    and produce strictly positive-definite concrete matrices with explicit non-zero vectors. -/
theorem nonvacuity_all_four_families :
    Nonempty (SchurSystem (Dyad × Dyad)) ∧
    Nonempty (SchurSystem Dyad) ∧
    Nonempty (SchurSystem ExpState) ∧
    StrictlyPosDef 16 (vdcHammingMat (ofInt 4) (ofInt 3)) ∧
    StrictlyPosDef 16 (weightedVdcMat ⟨5, 2⟩ one) ∧
    StrictlyPosDef 16 grayWeightedMat ∧
    StrictlyPosDef 32 (expVdcMat (ofInt 7) (ofInt 6)) :=
  ⟨⟨vdcHammingSystem⟩,
   ⟨grayWeightedSystem⟩,
   ⟨expVdcSystem⟩,
   vdcHamming_critical_4_3_all_n 16,
   weightedVdc_5_4_strictlyPosDef_all_n 16,
   grayWeighted_strictlyPosDef_all_n 16,
   expVdc_critical_7_6_all_n 32⟩

end DyadicLDLT
