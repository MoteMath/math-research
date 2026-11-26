/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RagPopcntMatryoshka.RatOrder

/-!
# Theorem 1: Bit-Exact 1-Bit `XOR+POPCNT`, 1.58-Bit Ternary, and 2-Bit 2-Bitplane `POPCNT` Identities

Pure-`Init` (zero Mathlib) algebraic/inductive proofs over arbitrary dimension `d : Nat`.
-/

namespace RagPopcntMatryoshka

theorem popcnt_int {d : Nat} (p : Fin d → Bool) :
    (popcnt p : Int) = finSumInt (fun i => if p i then (1 : Int) else 0) := by
  unfold popcnt
  rw [finSumInt_ofNat]
  apply finSumInt_congr
  intro i
  cases p i <;> rfl

theorem bipolar_mul_eq_one_sub_two_xor (q x : Bool) :
    bipolar q * bipolar x = (1 : Int) - 2 * (if xor q x then (1 : Int) else 0) := by
  cases q <;> cases x <;> rfl

theorem bipolar_mul_bounds (q x : Bool) :
    (-1 : Int) ≤ bipolar q * bipolar x ∧ bipolar q * bipolar x ≤ (1 : Int) := by
  cases q <;> cases x <;> decide

theorem dotBool_eq_sub_two_hamming {d : Nat} (q x : Fin d → Bool) :
    dotBool q x = (d : Int) - 2 * (hamming q x : Int) := by
  unfold dotBool hamming
  rw [popcnt_int]
  have hpoint : ∀ i : Fin d,
      bipolar (q i) * bipolar (x i) =
        (1 : Int) - 2 * (if xor (q i) (x i) then (1 : Int) else 0) :=
    fun i => bipolar_mul_eq_one_sub_two_xor (q i) (x i)
  rw [finSumInt_congr hpoint, finSumInt_sub, finSumInt_const, finSumInt_mul_left]
  omega

theorem dotBool_comm {d : Nat} (q x : Fin d → Bool) :
    dotBool q x = dotBool x q := by
  unfold dotBool
  exact finSumInt_congr (fun i => Int.mul_comm (bipolar (q i)) (bipolar (x i)))

theorem dotBool_self {d : Nat} (q : Fin d → Bool) :
    dotBool q q = (d : Int) := by
  unfold dotBool
  have hpoint : ∀ i : Fin d, bipolar (q i) * bipolar (q i) = 1 := by
    intro i; cases q i <;> rfl
  rw [finSumInt_congr hpoint, finSumInt_const]
  omega

theorem dotBool_bounds {d : Nat} (q x : Fin d → Bool) :
    -(d : Int) ≤ dotBool q x ∧ dotBool q x ≤ (d : Int) := by
  unfold dotBool
  constructor
  · have h1 := finSumInt_le_finSumInt (fun i : Fin d => (bipolar_mul_bounds (q i) (x i)).1)
    rw [finSumInt_const] at h1
    omega
  · have h2 := finSumInt_le_finSumInt (fun i : Fin d => (bipolar_mul_bounds (q i) (x i)).2)
    rw [finSumInt_const] at h2
    omega

theorem ternaryVal_mul_eq (qp qn xp xn : Bool) :
    ternaryVal qp qn * ternaryVal xp xn =
      (if qp && xp then (1 : Int) else 0) +
      (if qn && xn then (1 : Int) else 0) -
      (if qp && xn then (1 : Int) else 0) -
      (if qn && xp then (1 : Int) else 0) := by
  cases qp <;> cases qn <;> cases xp <;> cases xn <;> rfl

theorem dotTernary_eq_popcntTernaryDot {d : Nat} (qp qn xp xn : Fin d → Bool) :
    dotTernary qp qn xp xn = popcntTernaryDot qp qn xp xn := by
  unfold dotTernary popcntTernaryDot
  rw [popcnt_int, popcnt_int, popcnt_int, popcnt_int]
  rw [finSumInt_congr (fun i => ternaryVal_mul_eq (qp i) (qn i) (xp i) (xn i))]
  rw [finSumInt_sub, finSumInt_sub, finSumInt_add]

theorem popcntTernaryDot_comm {d : Nat} (qp qn xp xn : Fin d → Bool) :
    popcntTernaryDot qp qn xp xn = popcntTernaryDot xp xn qp qn := by
  rw [← dotTernary_eq_popcntTernaryDot, ← dotTernary_eq_popcntTernaryDot]
  unfold dotTernary
  exact finSumInt_congr (fun i => Int.mul_comm _ _)

theorem twoBitVal_mul_eq (qs qh xs xh : Bool) :
    twoBitVal qs qh * twoBitVal xs xh =
      (2 * (if !(xor qs xs) then (1 : Int) else 0) - 1) +
      2 * (2 * (if xor qh xh && !(xor qs xs) then (1 : Int) else 0) -
           (if xor qh xh then (1 : Int) else 0)) +
      8 * (2 * (if (qh && xh) && !(xor qs xs) then (1 : Int) else 0) -
           (if qh && xh then (1 : Int) else 0)) := by
  cases qs <;> cases qh <;> cases xs <;> cases xh <;> rfl

theorem twoBitVal_mul_bounds (qs qh xs xh : Bool) :
    (-9 : Int) ≤ twoBitVal qs qh * twoBitVal xs xh ∧
    twoBitVal qs qh * twoBitVal xs xh ≤ (9 : Int) := by
  cases qs <;> cases qh <;> cases xs <;> cases xh <;> decide

theorem dotTwoBit_eq_popcntTwoBitDot {d : Nat} (qs qh xs xh : Fin d → Bool) :
    dotTwoBit qs qh xs xh = popcntTwoBitDot qs qh xs xh := by
  unfold dotTwoBit popcntTwoBitDot
  dsimp only
  rw [popcnt_int, popcnt_int, popcnt_int, popcnt_int, popcnt_int]
  rw [finSumInt_congr (fun i => twoBitVal_mul_eq (qs i) (qh i) (xs i) (xh i))]
  rw [finSumInt_add, finSumInt_add]
  rw [finSumInt_sub, finSumInt_mul_left, finSumInt_const]
  rw [finSumInt_mul_left, finSumInt_sub, finSumInt_mul_left]
  rw [finSumInt_mul_left, finSumInt_sub, finSumInt_mul_left]
  omega

theorem popcntTwoBitDot_comm {d : Nat} (qs qh xs xh : Fin d → Bool) :
    popcntTwoBitDot qs qh xs xh = popcntTwoBitDot xs xh qs qh := by
  rw [← dotTwoBit_eq_popcntTwoBitDot, ← dotTwoBit_eq_popcntTwoBitDot]
  unfold dotTwoBit
  exact finSumInt_congr (fun i => Int.mul_comm _ _)

theorem dotTwoBit_bounds {d : Nat} (qs qh xs xh : Fin d → Bool) :
    -(9 * (d : Int)) ≤ dotTwoBit qs qh xs xh ∧ dotTwoBit qs qh xs xh ≤ 9 * (d : Int) := by
  unfold dotTwoBit
  constructor
  · have h1 := finSumInt_le_finSumInt (fun i : Fin d => (twoBitVal_mul_bounds (qs i) (qh i) (xs i) (xh i)).1)
    rw [finSumInt_const] at h1
    omega
  · have h2 := finSumInt_le_finSumInt (fun i : Fin d => (twoBitVal_mul_bounds (qs i) (qh i) (xs i) (xh i)).2)
    rw [finSumInt_const] at h2
    omega

theorem dotBool_block_assoc {a b : Nat} (q x : Fin (a + b) → Bool) :
    dotBool q x = dotBool (leftBlock q) (leftBlock x) + dotBool (rightBlock q) (rightBlock x) := by
  unfold dotBool
  exact finSumInt_split (fun i => bipolar (q i) * bipolar (x i))

theorem dotTwoBit_block_assoc {a b : Nat} (qs qh xs xh : Fin (a + b) → Bool) :
    dotTwoBit qs qh xs xh =
      dotTwoBit (leftBlock qs) (leftBlock qh) (leftBlock xs) (leftBlock xh) +
      dotTwoBit (rightBlock qs) (rightBlock qh) (rightBlock xs) (rightBlock xh) := by
  unfold dotTwoBit
  exact finSumInt_split (fun i => twoBitVal (qs i) (qh i) * twoBitVal (xs i) (xh i))

/-- Headline Theorem 1 (`popcnt_binary_and_twoplane_exact_dot_identities`). -/
theorem popcnt_binary_and_twoplane_exact_dot_identities :
    (∀ (d : Nat) (q x : Fin d → Bool),
      dotBool q x = (d : Int) - 2 * (hamming q x : Int) ∧
      dotBool q x = dotBool x q ∧
      dotBool q q = (d : Int) ∧
      -(d : Int) ≤ dotBool q x ∧ dotBool q x ≤ (d : Int)) ∧
    (∀ (d : Nat) (qp qn xp xn : Fin d → Bool),
      dotTernary qp qn xp xn = popcntTernaryDot qp qn xp xn ∧
      popcntTernaryDot qp qn xp xn = popcntTernaryDot xp xn qp qn) ∧
    (∀ (d : Nat) (qs qh xs xh : Fin d → Bool),
      dotTwoBit qs qh xs xh = popcntTwoBitDot qs qh xs xh ∧
      popcntTwoBitDot qs qh xs xh = popcntTwoBitDot xs xh qs qh ∧
      -(9 * (d : Int)) ≤ dotTwoBit qs qh xs xh ∧ dotTwoBit qs qh xs xh ≤ 9 * (d : Int)) ∧
    (∀ (a b : Nat) (q x : Fin (a + b) → Bool),
      dotBool q x = dotBool (leftBlock q) (leftBlock x) + dotBool (rightBlock q) (rightBlock x)) ∧
    (∀ (a b : Nat) (qs qh xs xh : Fin (a + b) → Bool),
      dotTwoBit qs qh xs xh =
        dotTwoBit (leftBlock qs) (leftBlock qh) (leftBlock xs) (leftBlock xh) +
        dotTwoBit (rightBlock qs) (rightBlock qh) (rightBlock xs) (rightBlock xh)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d q x
    exact ⟨dotBool_eq_sub_two_hamming q x, dotBool_comm q x, dotBool_self q,
      (dotBool_bounds q x).1, (dotBool_bounds q x).2⟩
  · intro d qp qn xp xn
    exact ⟨dotTernary_eq_popcntTernaryDot qp qn xp xn, popcntTernaryDot_comm qp qn xp xn⟩
  · intro d qs qh xs xh
    exact ⟨dotTwoBit_eq_popcntTwoBitDot qs qh xs xh, popcntTwoBitDot_comm qs qh xs xh,
      (dotTwoBit_bounds qs qh xs xh).1, (dotTwoBit_bounds qs qh xs xh).2⟩
  · intro a b q x
    exact dotBool_block_assoc q x
  · intro a b qs qh xs xh
    exact dotTwoBit_block_assoc qs qh xs xh

end RagPopcntMatryoshka
