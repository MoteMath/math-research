/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryBlocksDeterminants.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Ultrametric XOR Bit-Length Determinants

Proves the exact closed-form determinant of `(bitlen (i ^^^ j) + t)_{0 ≤ i, j < 2^k}` over any
commutative ring `R`, using the division-free block-circulant identity
`det (fromBlocks A B B A) = det (A - B) * det (A + B)`.
-/

namespace CarryBlocksDeterminants

open Matrix Finset

section Helpers

/-- Division-free block-circulant determinant identity over any commutative ring `R`. -/
lemma det_fromBlocks_circulant {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) :
    (Matrix.fromBlocks A B B A).det = (A - B).det * (A + B).det := by
  let L : Matrix (n ⊕ n) (n ⊕ n) R := Matrix.fromBlocks 1 0 1 1
  let U : Matrix (n ⊕ n) (n ⊕ n) R := Matrix.fromBlocks 1 0 (-1) 1
  have hL : L.det = 1 := by
    simp [L]
  have hU : U.det = 1 := by
    simp [U]
  have hmul : L * Matrix.fromBlocks A B B A * U = Matrix.fromBlocks (A - B) B 0 (A + B) := by
    simp only [L, U, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add]
    congr 1 <;> abel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, hL, hU, one_mul, mul_one,
    Matrix.det_fromBlocks_zero₂₁] at hdet
  exact hdet

lemma bitlen_zero : bitlen 0 = 0 := by
  simp [bitlen]

lemma bitlen_of_pos {n : ℕ} (hn : 0 < n) : bitlen n = 1 + bitlen (n / 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [bitlen]

lemma bitlen_of_range : ∀ k n : ℕ, 2 ^ k ≤ n → n < 2 ^ (k + 1) → bitlen n = k + 1
  | 0, n, h1, h2 => by
      have hn : n = 1 := by omega
      subst hn
      simp [bitlen]
  | k + 1, n, h1, h2 => by
      have hpos : 0 < n := lt_of_lt_of_le (Nat.two_pow_pos (k + 1)) h1
      rw [bitlen_of_pos hpos]
      have h1' : 2 ^ k ≤ n / 2 := by
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        simpa [pow_succ] using h1
      have h2' : n / 2 < 2 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
        simpa [pow_succ] using h2
      rw [bitlen_of_range k (n / 2) h1' h2']
      omega

lemma xor_lt_pow_two {k u v : ℕ} (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    u ^^^ v < 2 ^ k := by
  exact Nat.xor_lt_two_pow hu hv

private lemma testBit_add_two_pow_of_lt {k u i : ℕ} (hi : i < k) :
    (2 ^ k + u).testBit i = u.testBit i := by
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hdvd : 2 ^ i ∣ 2 ^ k := Nat.pow_dvd_pow 2 (Nat.le_of_lt hi)
  obtain ⟨q, hq⟩ := hdvd
  have hqeven : 2 ∣ q := by
    have hpow : 2 ^ (i + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 hi
    obtain ⟨m, hm⟩ := hpow
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    have : 2 ^ i * q = 2 ^ i * (2 * m) := by
      calc 2 ^ i * q = 2 ^ k := hq.symm
        _ = 2 ^ (i + 1) * m := hm
        _ = 2 ^ i * (2 * m) := by rw [pow_succ]; ring
    exact ⟨m, Nat.eq_of_mul_eq_mul_left hpos this⟩
  obtain ⟨m, rfl⟩ := hqeven
  rw [hq, show 2 ^ i * (2 * m) + u = u + 2 ^ i * (2 * m) by ring,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), Nat.and_comm 1, Nat.and_comm 1,
    Nat.and_one_is_mod, Nat.and_one_is_mod]
  simp [Nat.add_mod]

private lemma testBit_add_two_pow_self {k u : ℕ} (hu : u < 2 ^ k) :
    (2 ^ k + u).testBit k = true := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hq : (2 ^ k + u) / 2 ^ k = 1 := by
    rw [show 2 ^ k + u = u + 2 ^ k * 1 by ring,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hu]
  rw [hq]
  rfl

lemma xor_add_two_pow_same {k u v : ℕ} (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    (2 ^ k + u) ^^^ (2 ^ k + v) = u ^^^ v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_xor]
  by_cases hi : i < k
  · rw [testBit_add_two_pow_of_lt hi, testBit_add_two_pow_of_lt hi]
  · push Not at hi
    have hu_bit : u.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) hi))
    have hv_bit : v.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hi))
    by_cases heq : i = k
    · subst heq
      rw [testBit_add_two_pow_self hu, testBit_add_two_pow_self hv, hu_bit, hv_bit]
      rfl
    · have hgt : k + 1 ≤ i := by omega
      have h1 : (2 ^ k + u).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have : 2 ^ k + u < 2 ^ (k + 1) := by rw [pow_succ]; omega
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) hgt)
      have h2 : (2 ^ k + v).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have : 2 ^ k + v < 2 ^ (k + 1) := by rw [pow_succ]; omega
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) hgt)
      rw [h1, h2, hu_bit, hv_bit]

lemma xor_add_two_pow_diff {k u v : ℕ} (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    2 ^ k ≤ u ^^^ (2 ^ k + v) ∧ u ^^^ (2 ^ k + v) < 2 ^ (k + 1) := by
  have hlt : u ^^^ (2 ^ k + v) < 2 ^ (k + 1) := by
    apply Nat.xor_lt_two_pow
    · exact lt_trans hu (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k))
    · rw [pow_succ]; omega
  refine ⟨?_, hlt⟩
  have hbit : (u ^^^ (2 ^ k + v)).testBit k = true := by
    rw [Nat.testBit_xor, Nat.testBit_lt_two_pow hu, testBit_add_two_pow_self hv]
    rfl
  exact Nat.ge_two_pow_of_testBit hbit

lemma bitlen_xor_add_two_pow_diff {k u v : ℕ} (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    bitlen (u ^^^ (2 ^ k + v)) = k + 1 := by
  obtain ⟨h1, h2⟩ := xor_add_two_pow_diff hu hv
  exact bitlen_of_range k _ h1 h2

lemma bitlen_xor_add_two_pow_diff_left {k u v : ℕ} (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    bitlen ((2 ^ k + u) ^^^ v) = k + 1 := by
  rw [Nat.xor_comm]
  exact bitlen_xor_add_two_pow_diff hv hu

/-- Equivalence `Fin (2^k) ⊕ Fin (2^k) ≃ Fin (2^(k+1))`. -/
def sumFinTwoPowEquiv (k : ℕ) : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) where
  toFun
    | Sum.inl u => ⟨u.val, lt_trans u.isLt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k))⟩
    | Sum.inr u => ⟨2 ^ k + u.val, by have := u.isLt; rw [pow_succ]; omega⟩
  invFun x :=
    if h : x.val < 2 ^ k then Sum.inl ⟨x.val, h⟩
    else Sum.inr ⟨x.val - 2 ^ k, by
      have hx : x.val < 2 ^ k * 2 := by simpa [pow_succ] using x.isLt
      omega⟩
  left_inv
    | Sum.inl u => by simp [u.isLt]
    | Sum.inr u => by
        have h : ¬ (2 ^ k + u.val < 2 ^ k) := by omega
        simp [h]
  right_inv x := by
    by_cases h : x.val < 2 ^ k
    · simp [h]
    · simp only [h, ↓reduceDIte]
      ext
      simp only
      omega

end Helpers

/-- Exact closed-form determinant of the shifted ultrametric XOR bit-length matrix
`(bitlen (i ^^^ j) + t)_{0 ≤ i, j < 2^k}` over any commutative ring `R`. -/
theorem det_bitlen_xor_add_const {R : Type*} [CommRing R] :
    ∀ (k : ℕ) (t : R),
      (bitlenXorMatrix k t).det =
        ((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) + t * (2 ^ k : R)) *
          ∏ r ∈ Finset.range k, (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - 1 - r))
  | 0, t => by
      simp [bitlenXorMatrix, bitlen_zero]
  | k + 1, t => by
      let e := sumFinTwoPowEquiv k
      have hreindex : (bitlenXorMatrix (k + 1) t).det =
          ((bitlenXorMatrix (k + 1) t).submatrix e e).det := by
        exact (Matrix.det_reindex_self e.symm (bitlenXorMatrix (k + 1) t)).symm
      rw [hreindex]
      let A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R := bitlenXorMatrix k t
      let B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R := Matrix.of fun _ _ => ((k + 1 : ℕ) : R) + t
      have hblock : (bitlenXorMatrix (k + 1) t).submatrix e e = Matrix.fromBlocks A B B A := by
        ext x y
        cases x with
        | inl u =>
          cases y with
          | inl v =>
            simp [e, sumFinTwoPowEquiv, bitlenXorMatrix, A]
          | inr v =>
            simp [e, sumFinTwoPowEquiv, bitlenXorMatrix, B,
              bitlen_xor_add_two_pow_diff u.isLt v.isLt]
        | inr u =>
          cases y with
          | inl v =>
            simp [e, sumFinTwoPowEquiv, bitlenXorMatrix, B,
              bitlen_xor_add_two_pow_diff_left u.isLt v.isLt]
          | inr v =>
            simp [e, sumFinTwoPowEquiv, bitlenXorMatrix, A,
              xor_add_two_pow_same u.isLt v.isLt]
      rw [hblock, det_fromBlocks_circulant]
      have hAB_sub : A - B = bitlenXorMatrix k (-((k + 1 : ℕ) : R)) := by
        ext u v
        simp [A, B, bitlenXorMatrix]
        ring
      have hAB_add : A + B = bitlenXorMatrix k (2 * t + ((k + 1 : ℕ) : R)) := by
        ext u v
        simp [A, B, bitlenXorMatrix]
        ring
      rw [hAB_sub, hAB_add, det_bitlen_xor_add_const k (-((k + 1 : ℕ) : R)),
        det_bitlen_xor_add_const k (2 * t + ((k + 1 : ℕ) : R))]
      set P : R := ∏ r ∈ Finset.range k, (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - 1 - r))
      have hL1 : (((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) : R) +
          (-((k + 1 : ℕ) : R)) * (2 ^ k : R)) = -(((2 ^ (k + 1) - 1 : ℕ) : R)) := by
        have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
        rw [Nat.cast_sub hpos]
        push_cast
        ring
      have hL2 : (((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) : R) +
          (2 * t + ((k + 1 : ℕ) : R)) * (2 ^ k : R)) =
          (((((k + 1 : ℕ) : ℤ) - 1) * (2 : ℤ) ^ (k + 1) + 1 : ℤ) : R) + t * (2 ^ (k + 1) : R) := by
        push_cast
        ring
      have hP : (-(((2 ^ (k + 1) - 1 : ℕ) : R))) * (P * P) =
          ∏ r ∈ Finset.range (k + 1), (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - r)) := by
        rw [Finset.prod_range_succ, Nat.sub_self, pow_zero, pow_one, mul_comm]
        congr 1
        dsimp [P]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro r hr
        rw [Finset.mem_range] at hr
        rw [← pow_add]
        congr 1
        have hsub : k - r = (k - 1 - r) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      rw [hL1, hL2]
      set Q : R := (((((k + 1 : ℕ) : ℤ) - 1) * (2 : ℤ) ^ (k + 1) + 1 : ℤ) : R) +
          t * (2 ^ (k + 1) : R)
      calc (-(((2 ^ (k + 1) - 1 : ℕ) : R))) * P * (Q * P)
          = Q * ((-(((2 ^ (k + 1) - 1 : ℕ) : R))) * (P * P)) := by ring
        _ = Q * ∏ r ∈ Finset.range (k + 1), (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k + 1 - 1 - r)) := by
            rw [hP]
            simp

/-- Exact unshifted ultrametric XOR bit-length determinant (`t = 0`). -/
theorem det_bitlen_xor {R : Type*} [CommRing R] (k : ℕ) :
    (bitlenXorMatrix k (0 : R)).det =
      ((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) : R) *
        ∏ r ∈ Finset.range k, (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - 1 - r)) := by
  simpa using det_bitlen_xor_add_const (R := R) k 0

end CarryBlocksDeterminants
