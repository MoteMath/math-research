/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Shared Definitions (`carry-blocks-determinants`)

Minimal trusted definitions for mixed-radix carry-block matrices, binary Gray-code carry
transitions, plateau Hankel matrices, and ultrametric XOR bit-length matrices.
-/

namespace CarryBlocksDeterminants

/-- Mixed-radix place value `P_0 = 1`, `P_{k+1} = P_k * b k`. -/
def place (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => place b k * b k

/-- Carry bit out of mixed-radix position `r` when adding `i` and `j`. -/
def carryBit (b : ℕ → ℕ) (r i j : ℕ) : ℕ :=
  if place b (r + 1) ≤ i % place b (r + 1) + j % place b (r + 1) then 1 else 0

/-- Number of maximal contiguous `1`-runs in the first `k` mixed-radix carry bits of `i + j`. -/
def carryBlocks (b : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, i, j =>
      carryBlocks b k i j +
        if carryBit b k i j = 1 ∧ (k = 0 ∨ carryBit b (k - 1) i j = 0) then 1 else 0

/-- Mixed-radix digit length of `n` (with `mlen b 0 = 0` and `mlen b n = k` for `P_{k-1} ≤ n < P_k`). -/
def mlen (b : ℕ → ℕ) (k n : ℕ) : ℕ :=
  match k with
  | 0 => if n = 0 then 0 else 1
  | k' + 1 => if n < place b (k' + 1) then mlen b k' n else k' + 2

/-- Standard binary bit-length: `bitlen 0 = 0`, `bitlen n = floor(log_2 n) + 1` for `n > 0`. -/
def bitlen : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + bitlen ((n + 1) / 2)
termination_by n => n

/-- Standard binary reflected Gray code `g(n) = n ^^^ (n / 2)`. -/
def gray (n : ℕ) : ℕ := n ^^^ (n / 2)

/-- Binary population count (Hamming weight). -/
def popcnt : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((n + 1) % 2) + popcnt ((n + 1) / 2)
termination_by n => n

/-- Exponential mixed-radix carry-blocks matrix `(x ^ carryBlocks b k i j)_{0 ≤ i, j < P_k}`. -/
def mixedCarryBlocksExpMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (k : ℕ) (x : R) :
    Matrix (Fin (place b k)) (Fin (place b k)) R :=
  Matrix.of fun i j => x ^ carryBlocks b k i.val j.val

/-- Linear mixed-radix carry-blocks matrix `(carryBlocks b k (i + 1) (j + 1))_{0 ≤ i, j < P_k - 1}`. -/
def mixedCarryBlocksMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (k : ℕ) :
    Matrix (Fin (place b k - 1)) (Fin (place b k - 1)) R :=
  Matrix.of fun i j => (carryBlocks b k (i.val + 1) (j.val + 1) : R)

/-- Binary Gray-code carry-transition matrix on `1 ≤ i, j < 2^k`. -/
def grayCarryTransitionMatrix {R : Type*} [CommRing R] (k : ℕ) :
    Matrix (Fin (2 ^ k - 1)) (Fin (2 ^ k - 1)) R :=
  Matrix.of fun i j =>
    (popcnt (gray ((i.val + 1) + (j.val + 1)) ^^^ gray (i.val + 1) ^^^ gray (j.val + 1)) : R)

/-- 0-based `N × N` Hankel matrix `(f (i + j))_{0 ≤ i, j < N}`. -/
def hankelZeroMatrix {R : Type*} (N : ℕ) (f : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => f (i.val + j.val)

/-- 1-based `(N - 1) × (N - 1)` Hankel matrix `(f (i + j + 2))_{0 ≤ i, j < N - 1}`. -/
def hankelOneMatrix {R : Type*} (N : ℕ) (f : ℕ → R) : Matrix (Fin (N - 1)) (Fin (N - 1)) R :=
  Matrix.of fun i j => f (i.val + j.val + 2)

/-- Ultrametric XOR bit-length matrix with additive constant shift `t` on `Fin (2^k)`. -/
def bitlenXorMatrix {R : Type*} [CommRing R] (k : ℕ) (t : R) :
    Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R :=
  Matrix.of fun i j => (bitlen (i.val ^^^ j.val) : R) + t

end CarryBlocksDeterminants
