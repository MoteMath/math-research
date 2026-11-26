/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SkewThueMorsePfaffian.Defs
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Skew-Symmetric Thue-Morse Pfaffian Unimodularity (`skew-thue-morse-pfaffian`)

Proves all four headline theorems over arbitrary commutative rings `R`:
1. `det_skewThueMorse_even`: `det(A_{2m}^{(0)}) = 1` for all `m`.
2. `det_skewThueMorse_shift1_even`: `det(A_{2m}^{(1)}) = 1` for all `m`.
3. `det_skewThueMorse_shift2_even`: `det(A_{2m}^{(2)}) = 1` for all `m`.
4. `det_skewThueMorse_odd`: `det(A_{2m + 1}^{(s)}) = 0` for all `s, m`.
-/

namespace SkewThueMorsePfaffian

open scoped BigOperators
open Matrix Finset

/-! ## Section 1: Binary Popcount & Thue-Morse Sign Identities -/

theorem binPopcount_zero : binPopcount 0 = 0 := by
  unfold binPopcount; simp

theorem binPopcount_eq_of_pos {n : ℕ} (hn : n ≠ 0) :
    binPopcount n = n % 2 + binPopcount (n / 2) := by
  conv_lhs => unfold binPopcount
  simp [hn]

theorem binPopcount_two_pow_add : ∀ k x, x < 2 ^ k → binPopcount (2 ^ k + x) = 1 + binPopcount x
  | 0, x, hx => by
    have hx0 : x = 0 := by omega
    subst hx0
    rw [pow_zero, add_zero, binPopcount_zero, binPopcount_eq_of_pos (by omega)]
    simp [binPopcount_zero]
  | k + 1, x, hx => by
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    have hpos : 0 < 2 ^ k := by positivity
    have hne : 2 ^ (k + 1) + x ≠ 0 := by omega
    rw [binPopcount_eq_of_pos hne]
    have hmod : (2 ^ (k + 1) + x) % 2 = x % 2 := by rw [hpow, Nat.mul_add_mod]
    have hdiv : (2 ^ (k + 1) + x) / 2 = 2 ^ k + x / 2 := by
      rw [hpow, Nat.mul_add_div (by omega)]
    rw [hmod, hdiv, binPopcount_two_pow_add k (x / 2) (by omega)]
    by_cases hx0 : x = 0
    · subst hx0; simp [binPopcount_zero]
    · rw [binPopcount_eq_of_pos hx0]; omega

theorem thueMorseSign_zero {R : Type*} [CommRing R] :
    thueMorseSign (R := R) 0 = 1 := by
  simp [thueMorseSign, binPopcount_zero]

theorem thueMorseSign_sq {R : Type*} [CommRing R] (n : ℕ) :
    thueMorseSign (R := R) n * thueMorseSign (R := R) n = 1 := by
  unfold thueMorseSign
  rw [← mul_pow]
  simp

theorem thueMorseSign_two_pow_add {R : Type*} [CommRing R] {k x : ℕ} (hx : x < 2 ^ k) :
    thueMorseSign (R := R) (2 ^ k + x) = -thueMorseSign (R := R) x := by
  unfold thueMorseSign
  rw [binPopcount_two_pow_add k x hx, pow_add, pow_one]
  ring

theorem thueMorseSign_three_mul_two_pow_add {R : Type*} [CommRing R] {k x : ℕ}
    (hx : x < 2 ^ (k + 1)) :
    thueMorseSign (R := R) (3 * 2 ^ k + x) = thueMorseSign (R := R) x := by
  have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  have h2 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  by_cases hlt : x < 2 ^ k
  · have heq : 3 * 2 ^ k + x = 2 ^ (k + 1) + (2 ^ k + x) := by omega
    rw [heq, thueMorseSign_two_pow_add (by omega), thueMorseSign_two_pow_add hlt, neg_neg]
  · have hge : 2 ^ k ≤ x := Nat.not_lt.mp hlt
    have heq : 3 * 2 ^ k + x = 2 ^ (k + 2) + (x - 2 ^ k) := by omega
    have hx' : x = 2 ^ k + (x - 2 ^ k) := by omega
    rw [heq, thueMorseSign_two_pow_add (by omega)]
    conv_rhs => rw [hx', thueMorseSign_two_pow_add (by omega)]

theorem thueMorseSign_four_mul_two_pow_add {R : Type*} [CommRing R] {k x : ℕ}
    (hx : x < 2 ^ (k + 1)) :
    thueMorseSign (R := R) (4 * 2 ^ k + x) = -thueMorseSign (R := R) x := by
  have h2 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  have heq : 4 * 2 ^ k + x = 2 ^ (k + 2) + x := by omega
  rw [heq, thueMorseSign_two_pow_add (by omega)]

theorem sum_thueMorseSign_two_pow (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (2 ^ k), thueMorseSign (R := ℚ) i = 0 := by
  cases k with
  | zero => omega
  | succ k' =>
    have hpow : 2 ^ (k' + 1) = 2 ^ k' + 2 ^ k' := by rw [pow_succ]; ring
    rw [hpow, Finset.sum_range_add]
    have hneg : ∑ x ∈ Finset.range (2 ^ k'), thueMorseSign (R := ℚ) (2 ^ k' + x) =
        -∑ x ∈ Finset.range (2 ^ k'), thueMorseSign (R := ℚ) x := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      exact thueMorseSign_two_pow_add (Finset.mem_range.mp hx)
    rw [hneg]; ring

theorem sum_thueMorseSign_two_pow_shift (k j : ℕ) (hk : 1 ≤ k) (hj : j < 2 ^ k) :
    ∑ i ∈ Finset.range (2 ^ k), thueMorseSign (R := ℚ) (2 ^ k + i + j) = 0 := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  have hbij : ∑ i ∈ Finset.range (2 ^ k), thueMorseSign (R := ℚ) (2 ^ k + i + j) =
      ∑ u ∈ Finset.range (2 ^ k), -thueMorseSign (R := ℚ) u := by
    refine Finset.sum_bij (fun i _ => (i + j) % 2 ^ k) ?_ ?_ ?_ ?_
    · intro i _; exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
    · intro i1 hi1 i2 hi2 heq
      have h1 := Finset.mem_range.mp hi1
      have h2 := Finset.mem_range.mp hi2
      by_cases c1 : i1 + j < 2 ^ k <;> by_cases c2 : i2 + j < 2 ^ k
      · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at heq; omega
      · have h2' : (i2 + j) % 2 ^ k = i2 + j - 2 ^ k := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [Nat.mod_eq_of_lt c1, h2'] at heq; omega
      · have h1' : (i1 + j) % 2 ^ k = i1 + j - 2 ^ k := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1', Nat.mod_eq_of_lt c2] at heq; omega
      · have h1' : (i1 + j) % 2 ^ k = i1 + j - 2 ^ k := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        have h2' : (i2 + j) % 2 ^ k = i2 + j - 2 ^ k := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1', h2'] at heq; omega
    · intro u hu
      have hu' := Finset.mem_range.mp hu
      by_cases hju : j ≤ u
      · refine ⟨u - j, Finset.mem_range.mpr (by omega), ?_⟩
        have : u - j + j = u := by omega
        rw [this, Nat.mod_eq_of_lt hu']
      · refine ⟨2 ^ k + u - j, Finset.mem_range.mpr (by omega), ?_⟩
        have : 2 ^ k + u - j + j = u + 2 ^ k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hu']
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      by_cases hij : i + j < 2 ^ k
      · rw [Nat.mod_eq_of_lt hij]
        have heq : 2 ^ k + i + j = 2 ^ k + (i + j) := by omega
        rw [heq, thueMorseSign_two_pow_add hij]
      · have hmod : (i + j) % 2 ^ k = i + j - 2 ^ k := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have heq : 2 ^ k + i + j = 2 ^ (k + 1) + (i + j - 2 ^ k) := by omega
        rw [heq, thueMorseSign_two_pow_add (by omega)]
  rw [hbij, Finset.sum_neg_distrib, sum_thueMorseSign_two_pow k hk, neg_zero]

/-! ## Section 2: Half-Swap Involution & Schur Complement Annihilation over `ℚ` -/

/-- Half-swap involution on `Fin (2 * M)`: exchanges `i < M` with `i + M`. -/
def halfSwapEquiv (M : ℕ) : Fin (2 * M) ≃ Fin (2 * M) where
  toFun i := if h : i.1 < M then ⟨i.1 + M, by omega⟩ else ⟨i.1 - M, by omega⟩
  invFun i := if h : i.1 < M then ⟨i.1 + M, by omega⟩ else ⟨i.1 - M, by omega⟩
  left_inv i := by
    ext
    by_cases h : i.1 < M
    · have h2 : ¬(i.1 + M < M) := by omega
      simp [h, h2]
    · have h2 : i.1 - M < M := by omega
      simp [h, h2]; omega
  right_inv i := by
    ext
    by_cases h : i.1 < M
    · have h2 : ¬(i.1 + M < M) := by omega
      simp [h, h2]
    · have h2 : i.1 - M < M := by omega
      simp [h, h2]; omega

/-- Permutation matrix `J` of `halfSwapEquiv M` over `ℚ`. -/
def halfSwapMat (M : ℕ) : Matrix (Fin (2 * M)) (Fin (2 * M)) ℚ :=
  Matrix.of fun i j => if halfSwapEquiv M i = j then 1 else 0

theorem halfSwapEquiv_invol (M : ℕ) (i : Fin (2 * M)) :
    halfSwapEquiv M (halfSwapEquiv M i) = i :=
  (halfSwapEquiv M).left_inv i

theorem halfSwapMat_symm (M : ℕ) : (halfSwapMat M).transpose = halfSwapMat M := by
  ext i j
  simp only [Matrix.transpose_apply, halfSwapMat, Matrix.of_apply]
  have hiff : halfSwapEquiv M j = i ↔ halfSwapEquiv M i = j := by
    constructor <;> intro h
    · rw [← h, halfSwapEquiv_invol]
    · rw [← h, halfSwapEquiv_invol]
  simp only [hiff]

theorem halfSwapMat_mul_left {M n : ℕ} (X : Matrix (Fin (2 * M)) (Fin n) ℚ) (i : Fin (2 * M)) (j : Fin n) :
    (halfSwapMat M * X) i j = X (halfSwapEquiv M i) j := by
  simp only [Matrix.mul_apply, halfSwapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (halfSwapEquiv M i)]
  · simp
  · intro r _ hr; simp [Ne.symm hr]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem halfSwapMat_mul_right {M n : ℕ} (X : Matrix (Fin n) (Fin (2 * M)) ℚ) (i : Fin n) (j : Fin (2 * M)) :
    (X * halfSwapMat M) i j = X i (halfSwapEquiv M j) := by
  simp only [Matrix.mul_apply, halfSwapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (halfSwapEquiv M j)]
  · simp [halfSwapEquiv_invol]
  · intro r _ hr
    have hne : halfSwapEquiv M r ≠ j := fun h => hr (by rw [← h, halfSwapEquiv_invol])
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem halfSwapMat_sq (M : ℕ) : halfSwapMat M * halfSwapMat M = 1 := by
  ext i j
  rw [halfSwapMat_mul_left]
  simp only [halfSwapMat, Matrix.of_apply, Matrix.one_apply, halfSwapEquiv_invol]

/-- Anti-commutation `J * A_{2^k}^{(s)} * J = -A_{2^k}^{(s)}` for `s ≤ 1` and `k ≥ 1`. -/
theorem halfSwap_skewThueMorse (s m : ℕ) (hs : s ≤ 1) :
    halfSwapMat (2 ^ m) * skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m) * halfSwapMat (2 ^ m) =
      -skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m) := by
  ext i j
  rw [halfSwapMat_mul_right, halfSwapMat_mul_left]
  simp only [Matrix.neg_apply, skewThueMorseMatrix, Matrix.of_apply]
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
  by_cases hi : i.1 < 2 ^ m <;> by_cases hj : j.1 < 2 ^ m
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 + 2 ^ m := by simp [halfSwapEquiv, hi]
    have hsj : (halfSwapEquiv (2 ^ m) j).1 = j.1 + 2 ^ m := by simp [halfSwapEquiv, hj]
    rw [hsi, hsj]
    have hsum : i.1 + 2 ^ m + (j.1 + 2 ^ m) + s = 2 ^ (m + 1) + (i.1 + j.1 + s) := by omega
    rw [hsum, thueMorseSign_two_pow_add (by omega)]
    split_ifs <;> first | omega | ring
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 + 2 ^ m := by simp [halfSwapEquiv, hi]
    have hsj : (halfSwapEquiv (2 ^ m) j).1 = j.1 - 2 ^ m := by simp [halfSwapEquiv, hj]
    rw [hsi, hsj]
    have hsum : i.1 + 2 ^ m + (j.1 - 2 ^ m) + s = i.1 + j.1 + s := by omega
    rw [hsum]
    split_ifs <;> first | omega | ring
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 - 2 ^ m := by simp [halfSwapEquiv, hi]
    have hsj : (halfSwapEquiv (2 ^ m) j).1 = j.1 + 2 ^ m := by simp [halfSwapEquiv, hj]
    rw [hsi, hsj]
    have hsum : i.1 - 2 ^ m + (j.1 + 2 ^ m) + s = i.1 + j.1 + s := by omega
    rw [hsum]
    split_ifs <;> first | omega | ring
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 - 2 ^ m := by simp [halfSwapEquiv, hi]
    have hsj : (halfSwapEquiv (2 ^ m) j).1 = j.1 - 2 ^ m := by simp [halfSwapEquiv, hj]
    rw [hsi, hsj]
    have hsum : i.1 + j.1 + s = 2 ^ (m + 1) + (i.1 - 2 ^ m + (j.1 - 2 ^ m) + s) := by omega
    rw [hsum, thueMorseSign_two_pow_add (by omega)]
    split_ifs <;> first | omega | ring

/-- Cross-block `B_{N × r}` between indices `< N` and indices `N .. N + r - 1`. -/
def crossBlock (s N r : ℕ) : Matrix (Fin N) (Fin r) ℚ :=
  Matrix.of fun i j => thueMorseSign (R := ℚ) (N + i.1 + j.1 + s)

/-- Anti-eigenvector identity `J * B = -B` for `s ≤ 1`, `N = 2 * 2^m`, and `r ≤ N`. -/
theorem halfSwap_crossBlock (s m r : ℕ) (hs : s ≤ 1) (hr : r ≤ 2 * 2 ^ m) :
    halfSwapMat (2 ^ m) * crossBlock s (2 * 2 ^ m) r = -crossBlock s (2 * 2 ^ m) r := by
  ext i j
  rw [halfSwapMat_mul_left]
  simp only [Matrix.neg_apply, crossBlock, Matrix.of_apply]
  have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
  have h2 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_succ, pow_succ]; ring
  have hj_lt : j.1 < 2 * 2 ^ m := lt_of_lt_of_le j.2 hr
  by_cases hi : i.1 < 2 ^ m <;> by_cases hj : j.1 < 2 ^ m
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 + 2 ^ m := by simp [halfSwapEquiv, hi]
    rw [hsi]
    have hL : 2 * 2 ^ m + (i.1 + 2 ^ m) + j.1 + s = 3 * 2 ^ m + (i.1 + j.1 + s) := by omega
    have hR : 2 * 2 ^ m + i.1 + j.1 + s = 2 ^ (m + 1) + (i.1 + j.1 + s) := by omega
    rw [hL, hR, thueMorseSign_three_mul_two_pow_add (by omega), thueMorseSign_two_pow_add (by omega), neg_neg]
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 + 2 ^ m := by simp [halfSwapEquiv, hi]
    rw [hsi]
    have hL : 2 * 2 ^ m + (i.1 + 2 ^ m) + j.1 + s = 4 * 2 ^ m + (i.1 + (j.1 - 2 ^ m) + s) := by omega
    have hR : 2 * 2 ^ m + i.1 + j.1 + s = 3 * 2 ^ m + (i.1 + (j.1 - 2 ^ m) + s) := by omega
    rw [hL, hR, thueMorseSign_four_mul_two_pow_add (by omega), thueMorseSign_three_mul_two_pow_add (by omega)]
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 - 2 ^ m := by simp [halfSwapEquiv, hi]
    rw [hsi]
    have hL : 2 * 2 ^ m + (i.1 - 2 ^ m) + j.1 + s = 2 ^ (m + 1) + ((i.1 - 2 ^ m) + j.1 + s) := by omega
    have hR : 2 * 2 ^ m + i.1 + j.1 + s = 3 * 2 ^ m + ((i.1 - 2 ^ m) + j.1 + s) := by omega
    rw [hL, hR, thueMorseSign_two_pow_add (by omega), thueMorseSign_three_mul_two_pow_add (by omega)]
  · have hsi : (halfSwapEquiv (2 ^ m) i).1 = i.1 - 2 ^ m := by simp [halfSwapEquiv, hi]
    rw [hsi]
    have hL : 2 * 2 ^ m + (i.1 - 2 ^ m) + j.1 + s = 3 * 2 ^ m + ((i.1 - 2 ^ m) + (j.1 - 2 ^ m) + s) := by omega
    have hR : 2 * 2 ^ m + i.1 + j.1 + s = 4 * 2 ^ m + ((i.1 - 2 ^ m) + (j.1 - 2 ^ m) + s) := by omega
    rw [hL, hR, thueMorseSign_three_mul_two_pow_add (by omega), thueMorseSign_four_mul_two_pow_add (by omega), neg_neg]

/-- Core Schur annihilation miracle: whenever `A = A_{2 * 2^m}^{(s)}` (`s ≤ 1`) is invertible over `ℚ`,
`Bᵀ * A⁻¹ * B = 0` for every `r ≤ 2 * 2^m`! -/
theorem schur_annihilation (s m r : ℕ) (hs : s ≤ 1) (hr : r ≤ 2 * 2 ^ m)
    (hdet : (skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m)).det ≠ 0) :
    (crossBlock s (2 * 2 ^ m) r).transpose *
      (skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m))⁻¹ *
      crossBlock s (2 * 2 ^ m) r = 0 := by
  set A := skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m)
  set J := halfSwapMat (2 ^ m)
  set B := crossBlock s (2 * 2 ^ m) r
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hJsq : J * J = 1 := halfSwapMat_sq (2 ^ m)
  have hJAJ : J * A * J = -A := halfSwap_skewThueMorse s m hs
  have hJB : J * B = -B := halfSwap_crossBlock s m r hs hr
  have hJT : J.transpose = J := halfSwapMat_symm (2 ^ m)
  have hBTJ : B.transpose * J = -B.transpose := by
    have := congrArg Matrix.transpose hJB
    simpa [Matrix.transpose_mul, hJT] using this
  have hJAinvJ : J * A⁻¹ * J = -A⁻¹ := by
    have h1 : A * (-J * A⁻¹ * J) = 1 := by
      have hJA : J * A = -A * J := by
        calc J * A = (J * A * J) * J := by rw [Matrix.mul_assoc, hJsq, Matrix.mul_one]
          _ = -A * J := by rw [hJAJ]
      have hAJ : A * J = -J * A := by
        calc A * J = J * (J * A * J) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJsq, Matrix.one_mul]
          _ = J * (-A) := by rw [hJAJ]
          _ = -J * A := by simp
      calc A * (-J * A⁻¹ * J) = -(A * J) * A⁻¹ * J := by simp [Matrix.mul_assoc]
        _ = -(-J * A) * A⁻¹ * J := by rw [hAJ]
        _ = J * (A * A⁻¹) * J := by simp [Matrix.mul_assoc]
        _ = J * J := by rw [hAAinv, Matrix.mul_one]
        _ = 1 := hJsq
    have hinv : A⁻¹ = -J * A⁻¹ * J := by
      have h2 := congrArg (A⁻¹ * ·) h1
      rw [Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hunit, Matrix.one_mul] at h2
      exact h2.symm
    calc J * A⁻¹ * J = J * (-J * A⁻¹ * J) * J := by conv_lhs => rw [hinv]
      _ = -(J * J) * A⁻¹ * (J * J) := by simp [Matrix.mul_assoc]
      _ = -A⁻¹ := by rw [hJsq]; simp
  have hneg : B.transpose * A⁻¹ * B = -(B.transpose * A⁻¹ * B) := by
    have h1 : (-B.transpose) * J = B.transpose := by rw [Matrix.neg_mul, hBTJ, neg_neg]
    have h2 : (-J) * B = B := by rw [Matrix.neg_mul, hJB, neg_neg]
    calc B.transpose * A⁻¹ * B
        = ((-B.transpose) * J) * A⁻¹ * ((-J) * B) := by rw [h1, h2]
      _ = B.transpose * (J * A⁻¹ * J) * B := by simp [Matrix.mul_assoc]
      _ = B.transpose * (-A⁻¹) * B := by rw [hJAinvJ]
      _ = -(B.transpose * A⁻¹ * B) := by simp [Matrix.mul_assoc]
  ext i j
  have hij := congrArg (fun M => M i j) hneg
  simp only [Matrix.neg_apply] at hij
  simp only [Matrix.zero_apply]
  linarith

/-- Block decomposition of `A_{N + r}^{(s)}` for `s ≤ 1`, `N = 2 * 2^m`, `r ≤ N` via `finSumFinEquiv`. -/
theorem skewThueMorse_block_decomp (s m r : ℕ) (hs : s ≤ 1) (hr : r ≤ 2 * 2 ^ m) :
    (skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m + r)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks
        (skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m))
        (crossBlock s (2 * 2 ^ m) r)
        (-(crossBlock s (2 * 2 ^ m) r).transpose)
        (-skewThueMorseMatrix (R := ℚ) s r) := by
  have hN : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
  have h2N : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_succ, pow_succ]; ring
  ext a b
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      simp only [Matrix.submatrix_apply, skewThueMorseMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left, Fin.val_castAdd]
    | inr j =>
      simp only [Matrix.submatrix_apply, skewThueMorseMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, crossBlock, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
      have hlt : i.1 < 2 * 2 ^ m + j.1 := by omega
      simp only [hlt, ↓reduceIte]
      congr 1; omega
  | inr i =>
    cases b with
    | inl j =>
      simp only [Matrix.submatrix_apply, skewThueMorseMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.transpose_apply, crossBlock,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
      have hnotlt : ¬(2 * 2 ^ m + i.1 < j.1) := by omega
      have hgt : j.1 < 2 * 2 ^ m + i.1 := by omega
      simp only [hnotlt, hgt, ↓reduceIte]
      congr 2; omega
    | inr j =>
      simp only [Matrix.submatrix_apply, skewThueMorseMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, finSumFinEquiv_apply_right, Fin.val_natAdd]
      have hsum : 2 * 2 ^ m + i.1 + (2 * 2 ^ m + j.1) + s = 2 ^ (m + 2) + (i.1 + j.1 + s) := by omega
      have hlt_sum : i.1 + j.1 + s < 2 ^ (m + 2) := by omega
      rw [hsum, thueMorseSign_two_pow_add hlt_sum]
      split_ifs <;> first | omega | ring

/-- Inductive step over `ℚ`: for `s ≤ 1`, `N = 2 * 2^m`, `r ≤ N` even, if `det(A_N) = 1`
then `det(A_{N + r}) = det(A_r)`. -/
theorem det_skewThueMorse_add_even (s m k : ℕ) (hs : s ≤ 1) (hk : 2 * k ≤ 2 * 2 ^ m)
    (hdetN : (skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m)).det = 1) :
    (skewThueMorseMatrix (R := ℚ) s (2 * 2 ^ m + 2 * k)).det =
      (skewThueMorseMatrix (R := ℚ) s (2 * k)).det := by
  set N := 2 * 2 ^ m
  set r := 2 * k
  set A := skewThueMorseMatrix (R := ℚ) s N
  set B := crossBlock s N r
  set Ar := skewThueMorseMatrix (R := ℚ) s r
  have hA_ne : A.det ≠ 0 := by rw [hdetN]; norm_num
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA_ne
  have hschur : B.transpose * A⁻¹ * B = 0 := schur_annihilation s m r hs hk hA_ne
  have hsub := skewThueMorse_block_decomp s m r hs hk
  have hdet_sub : (skewThueMorseMatrix (R := ℚ) s (N + r)).det =
      (Matrix.fromBlocks A B (-B.transpose) (-Ar)).det := by
    rw [← hsub, Matrix.det_submatrix_equiv_self]
  rw [hdet_sub]
  let L : Matrix (Fin N ⊕ Fin r) (Fin N ⊕ Fin r) ℚ :=
    Matrix.fromBlocks 1 0 (B.transpose * A⁻¹) 1
  have hL_det : L.det = 1 := by
    simp [L]
  have hmul : L * Matrix.fromBlocks A B (-B.transpose) (-Ar) =
      Matrix.fromBlocks A B 0 (-Ar) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero]
    congr 1
    · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A hunit, Matrix.mul_one, add_neg_cancel]
    · rw [hschur, zero_add]
  have hdet_mul := congrArg Matrix.det hmul
  rw [Matrix.det_mul, hL_det, one_mul, Matrix.det_fromBlocks_zero₂₁, hdetN, one_mul] at hdet_mul
  rw [hdet_mul, Matrix.det_neg, Fintype.card_fin]
  simp [r]

/-- Theorems 1 & 2 over `ℚ`: `det(A_{2m}^{(s)}) = 1` for all `s ≤ 1` and all `m : ℕ`. -/
theorem det_skewThueMorse_le_one_rat (s : ℕ) (hs : s ≤ 1) :
    ∀ m : ℕ, (skewThueMorseMatrix (R := ℚ) s (2 * m)).det = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => simp [skewThueMorseMatrix]
    | 1 =>
      rw [Matrix.det_fin_two]
      simp only [skewThueMorseMatrix, Matrix.of_apply, Fin.val_zero, Fin.val_one]
      have hsq := thueMorseSign_sq (R := ℚ) (0 + 1 + s)
      have hcomm : thueMorseSign (R := ℚ) (1 + 0 + s) = thueMorseSign (R := ℚ) (0 + 1 + s) := by
        congr 1
      simp only [lt_self_iff_false, ↓reduceIte, zero_lt_one, Nat.not_lt_zero, mul_zero, zero_sub,
        hcomm, mul_neg, neg_neg, hsq]
    | m' + 2 =>
      set n := m' + 2
      have hn : 2 ≤ n := by omega
      -- Choose p = Nat.log 2 (n - 1), so 2^p ≤ n - 1 < 2^(p+1), hence 2^p < n ≤ 2 * 2^p
      set p := Nat.log 2 (n - 1)
      have hle : 2 ^ p ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
      have hlt : n - 1 < 2 ^ (p + 1) := Nat.lt_pow_succ_log_self (by omega) (n - 1)
      have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, mul_comm]
      have h2p_lt : 2 ^ p < n := by omega
      have hrem_pos : 1 ≤ n - 2 ^ p := by omega
      have hrem_le : n - 2 ^ p ≤ 2 ^ p := by omega
      have hrem_lt : n - 2 ^ p < n := by omega
      have hsplit : 2 * n = 2 * 2 ^ p + 2 * (n - 2 ^ p) := by omega
      rw [hsplit]
      have hdetN := ih (2 ^ p) h2p_lt
      have hdetR := ih (n - 2 ^ p) hrem_lt
      rw [det_skewThueMorse_add_even s p (n - 2 ^ p) hs (by omega) hdetN, hdetR]

/-! ## Section 3: Shift `s = 2` via Explicit Null Vector of `A_{2m+1}^{(0)}` -/

/-- Row `0` of `(A_{2^k}^{(0)})⁻¹` is `[0, 1, 1, ..., 1]`, i.e., `[0, 1, ..., 1] ᵥ* A_{2^k} = e_0`. -/
theorem rowZero_vecMul_skewThueMorse :
    ∀ m (j : Fin (2 * 2 ^ m)),
      (∑ i : Fin (2 * 2 ^ m), (if i.1 = 0 then (0 : ℚ) else 1) *
        skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ m) i j) =
      if j.1 = 0 then 1 else 0
  | 0, j => by
    fin_cases j
    · simp [skewThueMorseMatrix, Fin.sum_univ_two, thueMorseSign, binPopcount_eq_of_pos, binPopcount_zero]
    · simp [skewThueMorseMatrix, Fin.sum_univ_two]
  | m + 1, j => by
    have ih := rowZero_vecMul_skewThueMorse m
    set M := 2 * 2 ^ m
    have hM_eq : 2 ^ (m + 1) = M := by rw [pow_succ, mul_comm]
    have h2M : 2 * 2 ^ (m + 1) = M + M := by omega
    have hM_pos : 1 ≤ M := by
      have hpos : 0 < 2 ^ m := by positivity
      dsimp [M]; omega
    -- Split sum over Fin (2 * 2^(m+1)) into Fin M ⊕ Fin M via finCongr + finSumFinEquiv
    let e : Fin M ⊕ Fin M ≃ Fin (2 * 2 ^ (m + 1)) := finSumFinEquiv.trans (finCongr h2M.symm)
    have he_inl : ∀ x : Fin M, (e (Sum.inl x)).1 = x.1 := fun x => by simp [e]
    have he_inr : ∀ x : Fin M, (e (Sum.inr x)).1 = M + x.1 := fun x => by simp [e]; omega
    rw [Fintype.sum_equiv e.symm _ (fun x =>
      (if (e x).1 = 0 then (0 : ℚ) else 1) * skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e x) j)
      (fun i => by simp)]
    rw [Fintype.sum_sum_type]
    by_cases hj : j.1 < M
    · -- j is in the first half [0, M)
      let j1 : Fin M := ⟨j.1, hj⟩
      have hfirst :
          (∑ x : Fin M, (if (e (Sum.inl x)).1 = 0 then (0 : ℚ) else 1) *
            skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inl x)) j) =
          if j.1 = 0 then 1 else 0 := by
        have := ih j1
        convert this using 1
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [skewThueMorseMatrix, Matrix.of_apply, he_inl, j1]
      have hsecond :
          (∑ x : Fin M, (if (e (Sum.inr x)).1 = 0 then (0 : ℚ) else 1) *
            skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inr x)) j) = 0 := by
        have h1 : ∀ x : Fin M,
            (if (e (Sum.inr x)).1 = 0 then (0 : ℚ) else 1) *
              skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inr x)) j =
            -thueMorseSign (R := ℚ) (2 ^ (m + 1) + x.1 + j.1) := by
          intro x
          have hval := he_inr x
          have hne0 : M + x.1 ≠ 0 := by omega
          have hgt : j.1 < M + x.1 := by omega
          have hnotlt : ¬(M + x.1 < j.1) := by omega
          simp only [skewThueMorseMatrix, Matrix.of_apply, hval, hne0, ↓reduceIte, one_mul, hnotlt, hgt,
            add_zero]
          congr 2; omega
        simp_rw [h1]
        rw [Finset.sum_neg_distrib, Fin.sum_univ_eq_sum_range (fun x => thueMorseSign (R := ℚ) (2 ^ (m + 1) + x + j.1))]
        have hrange : Finset.range M = Finset.range (2 ^ (m + 1)) := by rw [hM_eq]
        rw [hrange, sum_thueMorseSign_two_pow_shift (m + 1) j.1 (by omega) (by omega), neg_zero]
      rw [hfirst, hsecond, add_zero]
    · -- j is in the second half [M, 2M): write j = M + j2
      have hj_ne0 : j.1 ≠ 0 := by omega
      simp only [hj_ne0, ↓reduceIte]
      let j2 : Fin M := ⟨j.1 - M, by omega⟩
      have hj_eq : j.1 = M + j2.1 := by dsimp [j2]; omega
      have hfirst :
          (∑ x : Fin M, (if (e (Sum.inl x)).1 = 0 then (0 : ℚ) else 1) *
            skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inl x)) j) =
          thueMorseSign (R := ℚ) j2.1 := by
        have htot : (∑ x : Fin M, thueMorseSign (R := ℚ) (2 ^ (m + 1) + x.1 + j2.1)) = 0 := by
          rw [Fin.sum_univ_eq_sum_range (fun x => thueMorseSign (R := ℚ) (2 ^ (m + 1) + x + j2.1))]
          have hrange : Finset.range M = Finset.range (2 ^ (m + 1)) := by rw [hM_eq]
          rw [hrange]
          exact sum_thueMorseSign_two_pow_shift (m + 1) j2.1 (by omega) (by have := j2.2; omega)
        let h0 : Fin M := ⟨0, by omega⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h0)] at htot ⊢
        have hterm0 : (if (e (Sum.inl h0)).1 = 0 then (0 : ℚ) else 1) *
            skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inl h0)) j = 0 := by
          simp [he_inl, h0]
        rw [hterm0, zero_add]
        have hrest :
            (∑ x ∈ Finset.univ.erase h0, (if (e (Sum.inl x)).1 = 0 then (0 : ℚ) else 1) *
              skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inl x)) j) =
            ∑ x ∈ Finset.univ.erase h0, thueMorseSign (R := ℚ) (2 ^ (m + 1) + x.1 + j2.1) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hx0 : x.1 ≠ 0 := fun hz => (Finset.ne_of_mem_erase hx) (Fin.ext hz)
          have hval := he_inl x
          have hlt : x.1 < j.1 := by have := x.2; omega
          simp only [skewThueMorseMatrix, Matrix.of_apply, hval, hx0, ↓reduceIte, one_mul, hlt, add_zero]
          congr 1; omega
        rw [hrest]
        have h0val : thueMorseSign (R := ℚ) (2 ^ (m + 1) + h0.1 + j2.1) = -thueMorseSign (R := ℚ) j2.1 := by
          simp only [h0, add_zero]
          exact thueMorseSign_two_pow_add (by have := j2.2; omega)
        linarith
      have hsecond :
          (∑ x : Fin M, (if (e (Sum.inr x)).1 = 0 then (0 : ℚ) else 1) *
            skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inr x)) j) =
          -thueMorseSign (R := ℚ) j2.1 := by
        have hrew : ∀ x : Fin M,
            (if (e (Sum.inr x)).1 = 0 then (0 : ℚ) else 1) *
              skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ (m + 1)) (e (Sum.inr x)) j =
            -skewThueMorseMatrix (R := ℚ) 0 M x j2 := by
          intro x
          have hval := he_inr x
          have hne0 : M + x.1 ≠ 0 := by omega
          simp only [skewThueMorseMatrix, Matrix.of_apply, hval, hne0, ↓reduceIte, one_mul, hj_eq, add_zero]
          have hsum : M + x.1 + (M + j2.1) = 2 ^ (m + 2) + (x.1 + j2.1) := by
            have : 2 ^ (m + 2) = 2 * M := by rw [pow_succ, hM_eq]; ring
            omega
          have hlt_sum : x.1 + j2.1 < 2 ^ (m + 2) := by
            have : 2 ^ (m + 2) = 2 * M := by rw [pow_succ, hM_eq]; ring
            have hx2 := x.2; have hj22 := j2.2; omega
          rw [hsum, thueMorseSign_two_pow_add hlt_sum]
          split_ifs <;> first | omega | ring
        simp_rw [hrew, Finset.sum_neg_distrib]
        let h0 : Fin M := ⟨0, by omega⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h0)]
        have hih := ih j2
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h0)] at hih
        simp only [h0, ↓reduceIte, zero_mul, zero_add] at hih
        have hrest :
            (∑ x ∈ Finset.univ.erase h0, skewThueMorseMatrix (R := ℚ) 0 M x j2) =
            if j2.1 = 0 then 1 else 0 := by
          rw [← hih]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hx0 : x.1 ≠ 0 := fun hz => (Finset.ne_of_mem_erase hx) (Fin.ext hz)
          simp [hx0]
        rw [hrest]
        by_cases hj2 : j2.1 = 0
        · simp only [skewThueMorseMatrix, Matrix.of_apply, h0, hj2, lt_self_iff_false, ↓reduceIte,
            zero_add, thueMorseSign_zero]
        · have hj2_pos : 0 < j2.1 := Nat.pos_of_ne_zero hj2
          simp only [skewThueMorseMatrix, Matrix.of_apply, h0, hj2, hj2_pos, ↓reduceIte,
            zero_add, add_zero]
      rw [hfirst, hsecond, add_neg_cancel]

/-- Entry `(0, j)` of `(A_{2 * 2^m}^{(0)})⁻¹ * B` equals `thueMorseSign j` for `r ≤ 2 * 2^m`. -/
theorem inv_mul_crossBlock_row0 (m r : ℕ) (hr : r ≤ 2 * 2 ^ m) (j : Fin r) :
    ((skewThueMorseMatrix (R := ℚ) 0 (2 * 2 ^ m))⁻¹ * crossBlock 0 (2 * 2 ^ m) r)
      ⟨0, by positivity⟩ j = thueMorseSign (R := ℚ) j.1 := by
  set N := 2 * 2 ^ m
  set A := skewThueMorseMatrix (R := ℚ) 0 N
  have hdet1 : A.det = 1 := det_skewThueMorse_le_one_rat 0 (by omega) (2 ^ m)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (by rw [hdet1]; norm_num)
  let r0 : Fin N → ℚ := fun i => if i.1 = 0 then 0 else 1
  have hr0_eq : ∀ c : Fin N, A⁻¹ ⟨0, by positivity⟩ c = r0 c := by
    -- r0 ᵥ* A = e_0, so multiplying on right by A⁻¹ gives r0 = row 0 of A⁻¹!
    have hmul : r0 ᵥ* A = fun c => if c.1 = 0 then (1 : ℚ) else 0 := by
      ext c
      exact rowZero_vecMul_skewThueMorse m c
    have h2 := congrArg (· ᵥ* A⁻¹) hmul
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hunit, Matrix.vecMul_one] at h2
    intro c
    have hc := congrFun h2 c
    simp only [Matrix.vecMul, dotProduct] at hc
    rw [Finset.sum_eq_single ⟨0, by positivity⟩] at hc
    · simpa using hc.symm
    · intro x _ hx; have : x.1 ≠ 0 := fun hz => hx (Fin.ext hz); simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [Matrix.mul_apply, hr0_eq, r0, crossBlock, Matrix.of_apply, add_zero]
  let h0 : Fin N := ⟨0, by positivity⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h0)]
  simp only [h0, ↓reduceIte, zero_mul, zero_add]
  have htot : ∑ i : Fin N, thueMorseSign (R := ℚ) (N + i.1 + j.1) = 0 := by
    have hN : N = 2 ^ (m + 1) := by rw [pow_succ, mul_comm]
    rw [Fin.sum_univ_eq_sum_range (fun i => thueMorseSign (R := ℚ) (N + i + j.1)), hN]
    exact sum_thueMorseSign_two_pow_shift (m + 1) j.1 (by omega) (by omega)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h0)] at htot
  have hrest :
      (∑ i ∈ Finset.univ.erase h0, (if i.1 = 0 then (0 : ℚ) else 1) * thueMorseSign (R := ℚ) (N + i.1 + j.1)) =
      ∑ i ∈ Finset.univ.erase h0, thueMorseSign (R := ℚ) (N + i.1 + j.1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi0 : i.1 ≠ 0 := fun hz => (Finset.ne_of_mem_erase hi) (Fin.ext hz)
    simp [hi0]
  rw [hrest]
  have hterm0 : thueMorseSign (R := ℚ) (N + h0.1 + j.1) = -thueMorseSign (R := ℚ) j.1 := by
    have hN : N = 2 ^ (m + 1) := by rw [pow_succ, mul_comm]
    simp only [h0, add_zero, hN]
    exact thueMorseSign_two_pow_add (by omega)
  linarith

/-- Explicit null vector `w` of `A_{2m + 1}^{(0)}` with `w 0 = thueMorseSign m` and `w (2m) = 1`. -/
theorem exists_nullvec_skewThueMorse_odd :
    ∀ m : ℕ, ∃ w : Fin (2 * m + 1) → ℚ,
      skewThueMorseMatrix (R := ℚ) 0 (2 * m + 1) *ᵥ w = 0 ∧
      w ⟨0, by omega⟩ = thueMorseSign (R := ℚ) m ∧
      w ⟨2 * m, by omega⟩ = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 =>
      refine ⟨fun _ => 1, ?_, by simp [thueMorseSign_zero], rfl⟩
      ext i; fin_cases i; simp [skewThueMorseMatrix, Matrix.mulVec, dotProduct]
    | m' + 1 =>
      set n := m' + 1
      set p := Nat.log 2 n
      have hp_le : 2 ^ p ≤ n := Nat.pow_log_le_self 2 (by omega)
      have hp_lt : n < 2 ^ (p + 1) := Nat.lt_pow_succ_log_self (by omega) n
      have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, mul_comm]
      set N := 2 * 2 ^ p
      set m0 := n - 2 ^ p
      have hm0_lt : m0 < n := by omega
      have hm0_le : 2 * m0 + 1 ≤ N := by omega
      have hsplit : 2 * n + 1 = N + (2 * m0 + 1) := by omega
      rcases ih m0 hm0_lt with ⟨u, hu_ker, hu0, hulast⟩
      set A := skewThueMorseMatrix (R := ℚ) 0 N
      set B := crossBlock 0 N (2 * m0 + 1)
      have hdetA : A.det = 1 := det_skewThueMorse_le_one_rat 0 (by omega) (2 ^ p)
      have hunitA : IsUnit A.det := isUnit_iff_ne_zero.mpr (by rw [hdetA]; norm_num)
      have hschur : B.transpose * A⁻¹ * B = 0 := schur_annihilation 0 p (2 * m0 + 1) (by omega) hm0_le (by rw [hdetA]; norm_num)
      -- Define w on Fin N ⊕ Fin (2 * m0 + 1) as (-A⁻¹ *ᵥ (B *ᵥ u), u) and transport via e!
      let e : Fin N ⊕ Fin (2 * m0 + 1) ≃ Fin (2 * n + 1) := finSumFinEquiv.trans (finCongr hsplit.symm)
      let wtop : Fin N → ℚ := -(A⁻¹ *ᵥ (B *ᵥ u))
      let wsum : Fin N ⊕ Fin (2 * m0 + 1) → ℚ := Sum.elim wtop u
      let w : Fin (2 * n + 1) → ℚ := wsum ∘ e.symm
      refine ⟨w, ?_, ?_, ?_⟩
      · -- Show A_{2n+1} *ᵥ w = 0 via block decomposition
        have hdecomp : (skewThueMorseMatrix (R := ℚ) 0 (2 * n + 1)).submatrix e e =
            Matrix.fromBlocks A B (-B.transpose) (-skewThueMorseMatrix (R := ℚ) 0 (2 * m0 + 1)) := by
          have h1 := skewThueMorse_block_decomp 0 p (2 * m0 + 1) (by omega) hm0_le
          ext a b
          have := congrArg (fun M => M a b) h1
          simpa [e, skewThueMorseMatrix, Matrix.fromBlocks, A, B] using this
        have hker_sum :
            ((skewThueMorseMatrix (R := ℚ) 0 (2 * n + 1)).submatrix e e) *ᵥ wsum = 0 := by
          rw [hdecomp, Matrix.fromBlocks_mulVec]
          ext x
          cases x with
          | inl i =>
            have htop : A *ᵥ wtop + B *ᵥ u = 0 := by
              dsimp only [wtop]
              rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunitA,
                  Matrix.one_mulVec, neg_add_cancel]
            exact congrFun htop i
          | inr j =>
            have hbot : (-B.transpose) *ᵥ wtop + (-skewThueMorseMatrix (R := ℚ) 0 (2 * m0 + 1)) *ᵥ u = 0 := by
              dsimp only [wtop]
              rw [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.mulVec_mulVec,
                  Matrix.mulVec_mulVec, hschur, Matrix.zero_mulVec, Matrix.neg_mulVec, hu_ker,
                  neg_zero, add_zero]
            exact congrFun hbot j
        ext i
        have hi := congrFun hker_sum (e.symm i)
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, e.apply_symm_apply,
          Pi.zero_apply] at hi ⊢
        rw [Fintype.sum_equiv e.symm _ (fun x =>
          skewThueMorseMatrix (R := ℚ) 0 (2 * n + 1) i (e x) * wsum x)
          (fun y => by simp [w])]
        exact hi
      · -- Show w 0 = thueMorseSign n
        have he0 : e.symm ⟨0, by omega⟩ = Sum.inl ⟨0, by positivity⟩ := by
          apply e.injective; ext; simp [e]
        have hw0 : w ⟨0, by omega⟩ = -((A⁻¹ * B) *ᵥ u) ⟨0, by positivity⟩ := by
          dsimp only [w, Function.comp_apply]
          rw [he0]
          dsimp only [wsum, Sum.elim_inl, wtop]
          rw [Pi.neg_apply, ← Matrix.mulVec_mulVec]
        rw [hw0]
        simp only [Matrix.mulVec, dotProduct]
        have hrow0 : ∀ j : Fin (2 * m0 + 1), (A⁻¹ * B) ⟨0, by positivity⟩ j = thueMorseSign (R := ℚ) j.1 :=
          inv_mul_crossBlock_row0 p (2 * m0 + 1) hm0_le
        simp_rw [hrow0]
        -- ∑ j, t(j) * u j = t(0) * u 0 + (A_{2m0+1} *ᵥ u) 0 = u 0 + 0 = t(m0)!
        let h0 : Fin (2 * m0 + 1) := ⟨0, by omega⟩
        have hker0 := congrFun hu_ker h0
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hker0
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h0)] at hker0 ⊢
        have hsum_eq :
            (∑ j ∈ Finset.univ.erase h0, thueMorseSign (R := ℚ) j.1 * u j) =
            ∑ j ∈ Finset.univ.erase h0, skewThueMorseMatrix (R := ℚ) 0 (2 * m0 + 1) h0 j * u j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjpos : 0 < j.1 := Nat.pos_of_ne_zero fun hz => (Finset.ne_of_mem_erase hj) (Fin.ext hz)
          simp only [skewThueMorseMatrix, Matrix.of_apply, h0, hjpos, ↓reduceIte, zero_add, add_zero]
        have hdiag0 : skewThueMorseMatrix (R := ℚ) 0 (2 * m0 + 1) h0 h0 = 0 := by
          simp [skewThueMorseMatrix]
        rw [hdiag0, zero_mul, zero_add] at hker0
        rw [hsum_eq, hker0, add_zero]
        dsimp only [h0]
        rw [thueMorseSign_zero, one_mul, hu0]
        have hn_eq : n = 2 ^ p + m0 := by omega
        rw [hn_eq, thueMorseSign_two_pow_add (by omega)]
      · -- Show w (2n) = 1
        have helast : e.symm ⟨2 * n, by omega⟩ = Sum.inr ⟨2 * m0, by omega⟩ := by
          apply e.injective
          ext; simp [e]; omega
        simp [w, helast, wsum, hulast]

/-- Theorem 3 over `ℚ`: `det(A_{2m}^{(2)}) = 1` for all `m : ℕ`. -/
theorem det_skewThueMorse_shift2_rat (m : ℕ) :
    (skewThueMorseMatrix (R := ℚ) 2 (2 * m)).det = 1 := by
  set K := skewThueMorseMatrix (R := ℚ) 0 (2 * m + 1)
  rcases exists_nullvec_skewThueMorse_odd m with ⟨w, hw_ker, hw0, hwlast⟩
  have hK_skew : K.transpose = -K := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, K, skewThueMorseMatrix, Matrix.of_apply]
    have hcomm : j.1 + i.1 + 0 = i.1 + j.1 + 0 := by omega
    rw [hcomm]
    split_ifs <;> first | omega | ring
  have hw_left : w ᵥ* K = 0 := by
    have := congrArg (· *ᵥ w) hK_skew
    rw [Matrix.neg_mulVec, hw_ker, neg_zero] at this
    ext j
    have hj := congrFun this j
    simpa [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm] using hj
  set i0 : Fin (2 * m + 1) := ⟨0, by omega⟩
  set ilast : Fin (2 * m + 1) := ⟨2 * m, by omega⟩
  have hw0_sq : w i0 * w i0 = 1 := by rw [hw0]; exact thueMorseSign_sq m
  have hw0_ne : w i0 ≠ 0 := fun h => by rw [h, zero_mul] at hw0_sq; norm_num at hw0_sq
  let M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℚ :=
    K + Matrix.of fun i j => if i = i0 ∧ j = i0 then 1 else 0
  -- Identity 1: det(M) = det(A_{2m}^{(2)}) via E1 (replaces col 0 of I by w, det = w0)
  let E1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℚ :=
    Matrix.of fun i j => if j = i0 then w i else if i = j then 1 else 0
  have hE1_det : E1.det = w i0 := by
    have htri : E1.BlockTriangular OrderDual.toDual := by
      intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hj0 : j ≠ i0 := by intro h; subst h; exact Nat.not_lt_zero _ hij
      simp [E1, hj0, hne]
    rw [Matrix.det_of_isLowerTriangular E1 htri]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    have hdiag0 : E1 i0 i0 = w i0 := by simp [E1]
    rw [hdiag0]
    have hprod1 : ∏ x ∈ Finset.univ.erase i0, E1 x x = 1 :=
      Finset.prod_eq_one fun x hx => by simp [E1, Finset.ne_of_mem_erase hx]
    rw [hprod1, mul_one]
  have hM_eq_s2 : M.det = (skewThueMorseMatrix (R := ℚ) 2 (2 * m)).det := by
    let P1 := E1.transpose * M * E1
    have hP1_entry : ∀ i j : Fin (2 * m + 1),
        P1 i j = if i = i0 then (if j = i0 then 1 else 0)
                 else if j = i0 then 0 else K i j := by
      intro i j
      have hME1 : ∀ r c, (M * E1) r c =
          if c = i0 then (if r = i0 then w i0 else 0) else M r c := by
        intro r c
        simp only [Matrix.mul_apply, E1, Matrix.of_apply]
        by_cases hc : c = i0
        · subst hc
          simp only [↓reduceIte, M, Matrix.add_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib]
          have h1 : ∑ x, K r x * w x = 0 := congrFun hw_ker r
          rw [h1, zero_add]
          rw [Finset.sum_eq_single i0]
          · by_cases hr : r = i0 <;> simp [hr]
          · intro x _ hx; simp [hx]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp only [hc, ↓reduceIte]
          rw [Finset.sum_eq_single c]
          · simp
          · intro x _ hx; simp [hx]
          · intro h; exact absurd (Finset.mem_univ _) h
      simp only [P1, Matrix.mul_assoc, Matrix.mul_apply, Matrix.transpose_apply, E1, Matrix.of_apply, hME1]
      by_cases hi : i = i0
      · subst hi
        simp only [↓reduceIte]
        by_cases hj : j = i0
        · subst hj
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single i0]
          · simp [hw0_sq]
          · intro x _ hx; simp [hx]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp only [hj, ↓reduceIte, M, Matrix.add_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
          have h1 : ∑ x, w x * K x j = 0 := congrFun hw_left j
          rw [h1, zero_add]
          simp
      · simp only [hi, ↓reduceIte]
        rw [Finset.sum_eq_single i]
        · simp only [↓reduceIte, one_mul]
          by_cases hj : j = i0
          · simp [hj, hi]
          · simp [hj, hi, M]
        · intro x _ hx; simp [hx]
        · intro h; exact absurd (Finset.mem_univ _) h
    have hdet_P1 : P1.det = (skewThueMorseMatrix (R := ℚ) 2 (2 * m)).det := by
      rw [Matrix.det_succ_row_zero P1]
      rw [Finset.sum_eq_single 0]
      · simp only [Fin.val_zero, pow_zero, one_mul]
        have h00 : P1 0 0 = 1 := by
          have := hP1_entry i0 i0; simpa [i0] using this
        rw [h00, one_mul]
        congr 1
        ext a b
        have ha : a.succ ≠ i0 := by intro h; have := congrArg Fin.val h; simp [i0] at this
        have hb : b.succ ≠ i0 := by intro h; have := congrArg Fin.val h; simp [i0] at this
        simp only [Matrix.submatrix_apply, Fin.succAbove_zero, hP1_entry, ha, hb, ↓reduceIte, K,
          skewThueMorseMatrix, Matrix.of_apply, Fin.val_succ, add_zero]
        have hsum : a.1 + 1 + (b.1 + 1) = a.1 + b.1 + 2 := by omega
        rw [hsum]
        split_ifs <;> first | omega | rfl
      · intro j _ hj0
        have hj : j ≠ i0 := hj0
        have h0j : P1 0 j = 0 := by
          have := hP1_entry i0 j
          simp only [↓reduceIte, hj] at this
          exact this
        simp [h0j]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hdet_mul : P1.det = w i0 * w i0 * M.det := by
      simp only [P1, Matrix.det_mul, Matrix.det_transpose, hE1_det]; ring
    rw [hw0_sq, one_mul] at hdet_mul
    rw [← hdet_mul, hdet_P1]
  -- Identity 2: det(M) = det(A_{2m}^{(0)}) via E2 (replaces col 2m by w, det = 1) and F (col 0 -= w0⁻¹ * col 2m, det = 1)
  let E2 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℚ :=
    Matrix.of fun i j => if j = ilast then w i else if i = j then 1 else 0
  let F : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℚ :=
    Matrix.of fun i j => if i = j then 1 else if i = ilast ∧ j = i0 then -(w i0)⁻¹ else 0
  have hE2_det : E2.det = 1 := by
    have htri : E2.BlockTriangular id := by
      intro i j hij
      have hne : i ≠ j := ne_of_gt hij
      have hjlast : j ≠ ilast := by
        intro h; subst h
        have hi := i.2; have hlt : 2 * m < i.1 := hij; omega
      simp [E2, hjlast, hne]
    rw [Matrix.det_of_isUpperTriangular htri]
    refine Finset.prod_eq_one fun x _ => ?_
    by_cases hx : x = ilast
    · subst hx; simp [E2, hwlast]
    · simp [E2, hx]
  have hF_det : F.det = 1 := by
    have htri : F.BlockTriangular OrderDual.toDual := by
      intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hilast : i ≠ ilast := by
        intro h; subst h
        have hj := j.2; have hlt : 2 * m < j.1 := hij; omega
      simp [F, hne, hilast]
    rw [Matrix.det_of_isLowerTriangular F htri]
    refine Finset.prod_eq_one fun x _ => by simp [F]
  have hM_eq_s0 : M.det = (skewThueMorseMatrix (R := ℚ) 0 (2 * m)).det := by
    let G := E2 * F
    let P2 := G.transpose * M * G
    have hG_det : G.det = 1 := by simp [G, Matrix.det_mul, hE2_det, hF_det]
    have hP2_entry : ∀ i j : Fin (2 * m + 1),
        P2 i j = if i = ilast then (if j = ilast then 1 else 0)
                 else if j = ilast then 0 else K i j := by
      -- First compute E2ᵀ * K * E2 (has row/col ilast = 0, rest = K) and E2ᵀ * e0
      have hE2KE2 : ∀ r c, (E2.transpose * K * E2) r c =
          if r = ilast ∨ c = ilast then 0 else K r c := by
        intro r c
        have hKE2 : ∀ a b, (K * E2) a b = if b = ilast then 0 else K a b := by
          intro a b
          simp only [Matrix.mul_apply, E2, Matrix.of_apply]
          by_cases hb : b = ilast
          · subst hb; simp only [↓reduceIte]; exact congrFun hw_ker a
          · simp only [hb, ↓reduceIte]
            rw [Finset.sum_eq_single b]
            · simp
            · intro x _ hx; simp [hx]
            · intro h; exact absurd (Finset.mem_univ _) h
        rw [Matrix.mul_assoc]
        simp only [Matrix.mul_apply, Matrix.transpose_apply, E2, Matrix.of_apply, hKE2]
        by_cases hc : c = ilast
        · simp [hc]
        · simp only [hc, or_false, ↓reduceIte]
          by_cases hr : r = ilast
          · subst hr; simp only [↓reduceIte]; exact congrFun hw_left c
          · simp only [hr, ↓reduceIte]
            rw [Finset.sum_eq_single r]
            · simp
            · intro x _ hx; simp [hx]
            · intro h; exact absurd (Finset.mem_univ _) h
      have hFT_E2KE2_F : ∀ i j, (F.transpose * (E2.transpose * K * E2) * F) i j =
          if i = ilast ∨ j = ilast then 0 else K i j := by
        intro i j
        have h1 : ∀ a b, ((E2.transpose * K * E2) * F) a b =
            if a = ilast ∨ b = ilast then 0 else K a b := by
          intro a b
          simp only [Matrix.mul_apply, hE2KE2, F, Matrix.of_apply]
          rw [Finset.sum_eq_single b]
          · simp
          · intro x _ hx
            by_cases hxl : x = ilast
            · simp [hxl]
            · simp [hx, hxl]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [Matrix.mul_assoc]
        simp only [Matrix.mul_apply, Matrix.transpose_apply, F, Matrix.of_apply, h1]
        rw [Finset.sum_eq_single i]
        · simp
        · intro x _ hx
          by_cases hxl : x = ilast
          · simp [hxl]
          · simp [hx, hxl]
        · intro h; exact absurd (Finset.mem_univ _) h
      -- Now compute Gᵀ * (e0 e0ᵀ) * G: row 0 of G is e_{ilast} * w0!
      have hG0 : ∀ c : Fin (2 * m + 1), G i0 c = if c = ilast then w i0 else 0 := by
        intro c
        simp only [G, Matrix.mul_apply, E2, F, Matrix.of_apply]
        by_cases hm0 : m = 0
        · subst hm0
          have hc : c = ilast := Fin.ext (by have := c.2; omega)
          subst hc
          have hi0l : i0 = ilast := Fin.ext rfl
          rw [Finset.sum_eq_single ilast]
          · simp [hi0l]
          · intro x _ hx
            exfalso; apply hx; apply Fin.ext
            have hx2 := x.2
            change x.1 = 2 * 0
            omega
          · intro h; exact absurd (Finset.mem_univ _) h
        · have hi0_ne_last : i0 ≠ ilast := by intro h; have := congrArg Fin.val h; simp [i0, ilast] at this; omega
          by_cases hc : c = ilast
          · subst hc
            rw [Finset.sum_eq_single ilast]
            · simp
            · intro x _ hx; simp [hx, hi0_ne_last.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
          · simp only [hc, ↓reduceIte]
            by_cases hc0 : c = i0
            · subst hc0
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
              rw [Finset.sum_eq_single ilast]
              · simp [hi0_ne_last, hi0_ne_last.symm, mul_inv_cancel₀ hw0_ne]
              · intro x hx hxl
                have hx0 : x ≠ i0 := Finset.ne_of_mem_erase hx
                simp [hx0, hxl, hx0.symm]
              · intro h
                exact absurd (Finset.mem_erase.mpr ⟨hi0_ne_last.symm, Finset.mem_univ _⟩) h
            · rw [Finset.sum_eq_single c]
              · simp [hc, Ne.symm hc0]
              · intro x _ hx; simp [hx, hc0]
              · intro h; exact absurd (Finset.mem_univ _) h
      have hrank1 : ∀ i j,
          (G.transpose * (Matrix.of fun r c => if r = i0 ∧ c = i0 then (1 : ℚ) else 0) * G) i j =
          if i = ilast ∧ j = ilast then 1 else 0 := by
        intro i j
        have hstep : ∀ a b,
            ((Matrix.of fun r c => if r = i0 ∧ c = i0 then (1 : ℚ) else 0) * G) a b =
            if a = i0 then G i0 b else 0 := by
          intro a b
          simp only [Matrix.mul_apply, Matrix.of_apply]
          rw [Finset.sum_eq_single i0]
          · by_cases ha : a = i0 <;> simp [ha]
          · intro x _ hx; simp [hx]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [Matrix.mul_assoc]
        simp only [Matrix.mul_apply, Matrix.transpose_apply, hstep]
        rw [Finset.sum_eq_single i0]
        · simp only [↓reduceIte, hG0]
          by_cases hi : i = ilast <;> by_cases hj : j = ilast <;> simp [hi, hj, hw0_sq]
        · intro x _ hx; simp [hx]
        · intro h; exact absurd (Finset.mem_univ _) h
      intro i j
      have hsplitM : P2 = F.transpose * (E2.transpose * K * E2) * F +
          G.transpose * (Matrix.of fun r c => if r = i0 ∧ c = i0 then (1 : ℚ) else 0) * G := by
        simp only [P2, M, G, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [hsplitM, Matrix.add_apply, hFT_E2KE2_F, hrank1]
      by_cases hi : i = ilast <;> by_cases hj : j = ilast <;> simp [hi, hj]
    have hdet_P2 : P2.det = (skewThueMorseMatrix (R := ℚ) 0 (2 * m)).det := by
      -- Reindex Fin (2m + 1) via finSumFinEquiv : Fin (2m) ⊕ Fin 1 ≃ Fin (2m + 1)
      have hsub : P2.submatrix finSumFinEquiv finSumFinEquiv =
          Matrix.fromBlocks (skewThueMorseMatrix (R := ℚ) 0 (2 * m)) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
        ext a b
        cases a with
        | inl i =>
          cases b with
          | inl j =>
            have hi : finSumFinEquiv (Sum.inl i) ≠ ilast := by
              intro h; have := congrArg Fin.val h; simp [ilast] at this; omega
            have hj : finSumFinEquiv (Sum.inl j) ≠ ilast := by
              intro h; have := congrArg Fin.val h; simp [ilast] at this; omega
            simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, hP2_entry, hi, hj, ↓reduceIte]
            simp only [K, skewThueMorseMatrix, Matrix.of_apply, finSumFinEquiv_apply_left, Fin.val_castAdd]
          | inr j =>
            have hj : finSumFinEquiv (Sum.inr j) = ilast := by ext; simp [ilast]
            have hi : finSumFinEquiv (Sum.inl i) ≠ ilast := by
              intro h; have := congrArg Fin.val h; simp [ilast] at this; omega
            simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, hP2_entry, hi, hj, ↓reduceIte,
              Matrix.zero_apply]
        | inr i =>
          have hi : finSumFinEquiv (Sum.inr i) = ilast := by ext; simp [ilast]
          cases b with
          | inl j =>
            have hj : finSumFinEquiv (Sum.inl j) ≠ ilast := by
              intro h; have := congrArg Fin.val h; simp [ilast] at this; omega
            simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, hP2_entry, hi, hj, ↓reduceIte,
              Matrix.zero_apply]
          | inr j =>
            have hj : finSumFinEquiv (Sum.inr j) = ilast := by ext; simp [ilast]
            simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, hP2_entry, hi, hj, ↓reduceIte]
            fin_cases i; fin_cases j
            simp only [Matrix.one_apply_eq]
      rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv P2, hsub, Matrix.det_fromBlocks_zero₂₁,
          Matrix.det_one, mul_one]
    have hdet_mul : P2.det = M.det := by
      simp [P2, Matrix.det_mul, Matrix.det_transpose, hG_det]
    rw [← hdet_mul, hdet_P2]
  rw [← hM_eq_s2, hM_eq_s0]
  exact det_skewThueMorse_le_one_rat 0 (by omega) m

/-! ## Section 4: Ring Transfer & Headline Theorems over Arbitrary Commutative Rings -/

theorem map_skewThueMorseMatrix {R : Type*} [CommRing R] (s n : ℕ) :
    (Int.castRingHom R).mapMatrix (skewThueMorseMatrix (R := ℤ) s n) =
      skewThueMorseMatrix (R := R) s n := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, skewThueMorseMatrix, Matrix.of_apply,
    thueMorseSign]
  split_ifs <;> simp

theorem det_skewThueMorse_int_of_rat {s n : ℕ} {v : ℤ}
    (h : (skewThueMorseMatrix (R := ℚ) s n).det = (v : ℚ)) :
    (skewThueMorseMatrix (R := ℤ) s n).det = v := by
  apply Int.cast_injective (α := ℚ)
  calc ((skewThueMorseMatrix (R := ℤ) s n).det : ℚ)
      = (Int.castRingHom ℚ) (skewThueMorseMatrix (R := ℤ) s n).det := rfl
    _ = ((Int.castRingHom ℚ).mapMatrix (skewThueMorseMatrix (R := ℤ) s n)).det :=
        RingHom.map_det (Int.castRingHom ℚ) _
    _ = (skewThueMorseMatrix (R := ℚ) s n).det := by rw [map_skewThueMorseMatrix]
    _ = (v : ℚ) := h

/-- Theorem 1 (Unimodularity of skew-symmetric Thue-Morse matrix at shift `s = 0`). -/
theorem det_skewThueMorse_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 0 (2 * m)).det = 1 := by
  have hint : (skewThueMorseMatrix (R := ℤ) 0 (2 * m)).det = 1 :=
    det_skewThueMorse_int_of_rat (v := 1) (by simpa using det_skewThueMorse_le_one_rat 0 (by omega) m)
  have h := congrArg (Int.castRingHom R) hint
  rw [RingHom.map_det, map_skewThueMorseMatrix, map_one] at h
  exact h

/-- Theorem 2 (Unimodularity at shift `s = 1`). -/
theorem det_skewThueMorse_shift1_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 1 (2 * m)).det = 1 := by
  have hint : (skewThueMorseMatrix (R := ℤ) 1 (2 * m)).det = 1 :=
    det_skewThueMorse_int_of_rat (v := 1) (by simpa using det_skewThueMorse_le_one_rat 1 (by omega) m)
  have h := congrArg (Int.castRingHom R) hint
  rw [RingHom.map_det, map_skewThueMorseMatrix, map_one] at h
  exact h

/-- Theorem 3 (Unimodularity at shift `s = 2`). -/
theorem det_skewThueMorse_shift2_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 2 (2 * m)).det = 1 := by
  have hint : (skewThueMorseMatrix (R := ℤ) 2 (2 * m)).det = 1 :=
    det_skewThueMorse_int_of_rat (v := 1) (by simpa using det_skewThueMorse_shift2_rat m)
  have h := congrArg (Int.castRingHom R) hint
  rw [RingHom.map_det, map_skewThueMorseMatrix, map_one] at h
  exact h

/-- Theorem 4 (Odd-size vanishing over any commutative ring `R`, including char 2). -/
theorem det_skewThueMorse_odd {R : Type*} [CommRing R] (s m : ℕ) :
    (skewThueMorseMatrix (R := R) s (2 * m + 1)).det = 0 := by
  have hskew : (skewThueMorseMatrix (R := ℤ) s (2 * m + 1)).transpose =
      -skewThueMorseMatrix (R := ℤ) s (2 * m + 1) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, skewThueMorseMatrix, Matrix.of_apply]
    have hcomm : j.1 + i.1 + s = i.1 + j.1 + s := by omega
    rw [hcomm]
    split_ifs <;> omega
  have hdet_eq := congrArg Matrix.det hskew
  rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hdet_eq
  have hpow : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  rw [hpow, neg_one_mul] at hdet_eq
  have hint : (skewThueMorseMatrix (R := ℤ) s (2 * m + 1)).det = 0 := by omega
  have h := congrArg (Int.castRingHom R) hint
  rw [RingHom.map_det, map_skewThueMorseMatrix, map_zero] at h
  exact h

end SkewThueMorsePfaffian
