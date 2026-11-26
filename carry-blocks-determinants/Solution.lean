/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryBlocksDeterminants

/-!
# Verified Solutions (`carry-blocks-determinants`)

Provides sorry-free proofs for every theorem in `Challenge.lean`.
-/

namespace CarryBlocksChallenge

open CarryBlocksDeterminants

theorem det_mixedCarryBlocks_exp {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (x : R) :
    (mixedCarryBlocksExpMatrix b k x).det =
      (-1 : R) ^ ((place b k - 1).choose 2) * (x - 1) ^ (place b k - 1) :=
  CarryBlocksDeterminants.det_mixedCarryBlocks_exp b hb k x

theorem det_mixedCarryBlocks_linear {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) :
    (mixedCarryBlocksMatrix b k (R := R)).det = (-1 : R) ^ ((place b k - 1).choose 2) :=
  CarryBlocksDeterminants.det_mixedCarryBlocks_linear b hb k

theorem det_binaryCarryBlocks {R : Type*} [CommRing R] (k : ℕ) :
    (mixedCarryBlocksMatrix (fun _ => 2) k (R := R)).det =
      (-1 : R) ^ ((2 ^ k - 1).choose 2) :=
  CarryBlocksDeterminants.det_binaryCarryBlocks k

theorem det_grayCarryTransitions {R : Type*} [CommRing R] (k : ℕ) :
    (grayCarryTransitionMatrix (R := R) k).det =
      (-1 : R) ^ ((2 ^ k - 1).choose 2) * (2 : R) ^ (2 ^ k - 1) :=
  CarryBlocksDeterminants.det_grayCarryTransitions k

theorem det_plateauHankel_one {R : Type*} [CommRing R] {N : ℕ} (hN : 2 ≤ N)
    (f : ℕ → R) (a d : R)
    (hmid : f (N - 1) = a)
    (hhi : ∀ n, N ≤ n → n ≤ 2 * N - 2 → f n = a + d) :
    (hankelOneMatrix N f).det = (-1 : R) ^ ((N - 1).choose 2) * d ^ (N - 2) * (a + d) :=
  CarryBlocksDeterminants.det_plateauHankel_one hN f a d hmid hhi

theorem det_plateauHankel_zero {R : Type*} [CommRing R] {M N : ℕ}
    (hM : 1 ≤ M) (hMN : 2 * M ≤ N)
    (f : ℕ → R) (a d : R)
    (hmid : ∀ n, M ≤ n → n < N → f n = a)
    (hhi : ∀ n, N ≤ n → n ≤ 2 * N - 2 → f n = a + d) :
    (hankelZeroMatrix N f).det =
      (-1 : R) ^ ((N - 1).choose 2) * d ^ (N - 2) * (f 0 * (a + d) - a ^ 2) :=
  CarryBlocksDeterminants.det_plateauHankel_zero hM hMN f a d hmid hhi

theorem det_mixedDigitLen_one {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k : ℕ) (hk : 1 ≤ k) :
    (hankelOneMatrix (place b k) (fun n => (mlen b k n : R))).det =
      (-1 : R) ^ ((place b k - 1).choose 2) * ((k + 1 : ℕ) : R) :=
  CarryBlocksDeterminants.det_mixedDigitLen_one b hb k hk

theorem det_mixedDigitLen_zero {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k : ℕ) (hk : 1 ≤ k) :
    (hankelZeroMatrix (place b k) (fun n => (mlen b k n : R))).det =
      (-1 : R) ^ ((place b k - 1).choose 2 + 1) * ((k : R) ^ 2) :=
  CarryBlocksDeterminants.det_mixedDigitLen_zero b hb k hk

theorem det_bitlen_xor_add_const {R : Type*} [CommRing R] (k : ℕ) (t : R) :
    (bitlenXorMatrix k t).det =
      ((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) + t * (2 ^ k : R)) *
        ∏ r ∈ Finset.range k, (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - 1 - r)) :=
  CarryBlocksDeterminants.det_bitlen_xor_add_const k t

theorem det_bitlen_xor {R : Type*} [CommRing R] (k : ℕ) :
    (bitlenXorMatrix k (0 : R)).det =
      ((((k : ℤ) - 1) * (2 : ℤ) ^ k + 1 : ℤ) : R) *
        ∏ r ∈ Finset.range k, (-(((2 ^ (r + 1) - 1 : ℕ) : R))) ^ (2 ^ (k - 1 - r)) :=
  CarryBlocksDeterminants.det_bitlen_xor k

end CarryBlocksChallenge
