/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryBlocksDeterminants.Defs

/-!
# Trusted Challenge Statements (`carry-blocks-determinants`)

Minimal trusted statements for the mixed-radix carry-blocks, binary Gray-code carry-transition,
plateau Hankel, mixed-radix digit-length, and ultrametric XOR bit-length determinant theorems
over an arbitrary commutative ring `R`.
-/

namespace CarryBlocksChallenge

open CarryBlocksDeterminants

/-- Exponential mixed-radix carry-blocks determinant theorem. -/
theorem det_mixedCarryBlocks_exp {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (x : R) :
    (mixedCarryBlocksExpMatrix b k x).det =
      (-1 : R) ^ ((place b k - 1).choose 2) * (x - 1) ^ (place b k - 1) := by
  sorry

/-- Unimodularity of the linear mixed-radix carry-blocks matrix on `1 ≤ i, j < P_k`. -/
theorem det_mixedCarryBlocks_linear {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) :
    (mixedCarryBlocksMatrix b k (R := R)).det = (-1 : R) ^ ((place b k - 1).choose 2) := by
  sorry

/-- Binary carry-blocks unimodularity (`b = fun _ => 2`). -/
theorem det_binaryCarryBlocks {R : Type*} [CommRing R] (k : ℕ) :
    (mixedCarryBlocksMatrix (fun _ => 2) k (R := R)).det =
      (-1 : R) ^ ((2 ^ k - 1).choose 2) := by
  sorry

/-- Exact binary Gray-code carry-transition determinant on `1 ≤ i, j < 2^k`. -/
theorem det_grayCarryTransitions {R : Type*} [CommRing R] (k : ℕ) :
    (grayCarryTransitionMatrix (R := R) k).det =
      (-1 : R) ^ ((2 ^ k - 1).choose 2) * (2 : R) ^ (2 ^ k - 1) := by
  sorry

/-- Universal 1-based plateau Hankel determinant (independent of `f(0)..f(N-2)`). -/
theorem det_plateauHankel_one {R : Type*} [CommRing R] {N : ℕ} (hN : 2 ≤ N)
    (f : ℕ → R) (a d : R)
    (hmid : f (N - 1) = a)
    (hhi : ∀ n, N ≤ n → n ≤ 2 * N - 2 → f n = a + d) :
    (hankelOneMatrix N f).det = (-1 : R) ^ ((N - 1).choose 2) * d ^ (N - 2) * (a + d) := by
  sorry

/-- Universal 0-based plateau Hankel determinant (independent of `f(1)..f(M-1)`). -/
theorem det_plateauHankel_zero {R : Type*} [CommRing R] {M N : ℕ}
    (hM : 1 ≤ M) (hMN : 2 * M ≤ N)
    (f : ℕ → R) (a d : R)
    (hmid : ∀ n, M ≤ n → n < N → f n = a)
    (hhi : ∀ n, N ≤ n → n ≤ 2 * N - 2 → f n = a + d) :
    (hankelZeroMatrix N f).det =
      (-1 : R) ^ ((N - 1).choose 2) * d ^ (N - 2) * (f 0 * (a + d) - a ^ 2) := by
  sorry

/-- Universal 1-based mixed-radix digit-length Hankel determinant. -/
theorem det_mixedDigitLen_one {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k : ℕ) (hk : 1 ≤ k) :
    (hankelOneMatrix (place b k) (fun n => (mlen b k n : R))).det =
      (-1 : R) ^ ((place b k - 1).choose 2) * ((k + 1 : ℕ) : R) := by
  sorry

/-- Universal 0-based mixed-radix digit-length Hankel determinant. -/
theorem det_mixedDigitLen_zero {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k : ℕ) (hk : 1 ≤ k) :
    (hankelZeroMatrix (place b k) (fun n => (mlen b k n : R))).det =
      (-1 : R) ^ ((place b k - 1).choose 2 + 1) * ((k : R) ^ 2) := by
  sorry

/-- Exact shifted ultrametric XOR bit-length determinant on `Fin (2^k)`. -/
theorem det_bitlen_xor_add_const {R : Type*} [CommRing R] (k : ℕ) (t : R) :
    (bitlenXorMatrix k t).det =
      ((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) + t * (2 ^ k : R)) *
        ∏ r ∈ Finset.range k, (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - 1 - r)) := by
  sorry

/-- Exact unshifted ultrametric XOR bit-length determinant on `Fin (2^k)`. -/
theorem det_bitlen_xor {R : Type*} [CommRing R] (k : ℕ) :
    (bitlenXorMatrix k (0 : R)).det =
      ((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) : R) *
        ∏ r ∈ Finset.range k, (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - 1 - r)) := by
  sorry

end CarryBlocksChallenge
