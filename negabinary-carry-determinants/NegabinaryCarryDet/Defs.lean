/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Definitions for Negabinary (Base `-2`) Carry-Borrow Determinants

All definitions are pure Mathlib (no proofs) so `Challenge.lean` imports only this file.
-/

namespace NegabinaryCarryDet

open Matrix

/-- Binary Hamming weight (sum of binary digits `s_2(n)`). -/
def popcount : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

/-- Single-bit base-`(-2)` addition step on incoming carry `cin : ℤ` and bits `a, b ∈ {0, 1}`.
Returns `(outBit, nextCarry, posCarryInc, negBorrowInc)`:
- If `s = a + b + cin ≥ 2`, writes `s - 2`, emits borrow `-1`, increments `negBorrow`.
- If `s < 0`, writes `s + 2`, emits carry `+1`, increments `posCarry`.
- Otherwise writes `s`, emits carry `0`. -/
def negStep (cin : ℤ) (a b : ℕ) : ℕ × ℤ × ℕ × ℕ :=
  let s : ℤ := (a : ℤ) + (b : ℤ) + cin
  if 2 ≤ s then ((s - 2).toNat, -1, 0, 1)
  else if s < 0 then ((s + 2).toNat, 1, 1, 0)
  else (s.toNat, 0, 0, 0)

/-- Fuel-bounded base-`(-2)` addition returning `(sumBits, posCarries, negBorrows)`.
For `i, j < 2 ^ m` and `cin ∈ {-1, 0, 1}`, fuel `m + 3` always terminates with zero carry. -/
def negAddFullAux : ℕ → ℤ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, _, _ => (0, 0, 0)
  | fuel + 1, cin, i, j =>
    let (d, c', pc, nb) := negStep cin (i % 2) (j % 2)
    let (sRest, pcRest, nbRest) := negAddFullAux fuel c' (i / 2) (j / 2)
    (d + 2 * sRest, pc + pcRest, nb + nbRest)

/-- Canonical sufficient fuel for base-`(-2)` addition of `i` and `j`. -/
def negFuel (i j : ℕ) : ℕ := max i j + 4

/-- Exact base-`(-2)` bit-pattern of `i +_{-2} j` (with carry-in `cin`). -/
def negAdd (cin : ℤ) (i j : ℕ) : ℕ :=
  (negAddFullAux (negFuel i j) cin i j).1

/-- Exact number of positive carries (`s < 0 ↦ carry +1`) in base-`(-2)` addition `i +_{-2} j + cin`. -/
def negPosCarries (cin : ℤ) (i j : ℕ) : ℕ :=
  (negAddFullAux (negFuel i j) cin i j).2.1

/-- Exact number of negative borrows (`s ≥ 2 ↦ carry -1`) in base-`(-2)` addition `i +_{-2} j + cin`. -/
def negNegBorrows (cin : ℤ) (i j : ℕ) : ℕ :=
  (negAddFullAux (negFuel i j) cin i j).2.2

/-- Lower-unitriangular run-prefix predicate `L_Z(i, k)`:
`true` iff `k` is a submask of `i` that never drops a `1`-bit of `i` directly above a kept `1`-bit
of `k` (equivalently, `k` keeps a downward prefix of every contiguous `1`-run of `i`). -/
def runPrefix : ℕ → ℕ → Bool
  | _, 0 => true
  | i, k + 1 =>
    if (k + 1) % 2 = 0 then
      runPrefix (i / 2) ((k + 1) / 2)
    else
      decide (i % 2 = 1 ∧ (i / 2) % 2 = ((k + 1) / 2) % 2) &&
        runPrefix (i / 2) ((k + 1) / 2)

/-- Lower-unitriangular `{0, 1}` run-prefix matrix `L_Z` of size `n × n` over `R`. -/
def runPrefixMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i k => if runPrefix i.1 k.1 then 1 else 0

/-- Diagonal Thue-Morse matrix `diag((-1)^{s_2(0)}, ..., (-1)^{s_2(n-1)})` over `R`. -/
def thueMorseDiag (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun k : Fin n => (-1 : R) ^ popcount k.1

/-- The `n × n` base-`(-2)` zero-positive-carry matrix `Z_n(i, j) = 1[negPosCarries 0 i j = 0]`. -/
def negZeroPosCarryMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if negPosCarries 0 i.1 j.1 = 0 then 1 else 0

/-- The `n × n` base-`(-2)` zero-borrow matrix `B_n(i, j) = 1[negNegBorrows 0 i j = 0]`. -/
def negZeroBorrowMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if negNegBorrows 0 i.1 j.1 = 0 then 1 else 0

/-- The `n × n` Sierpinski disjoint-bit matrix `S_n(i, j) = 1[i &&& j = 0]`. -/
def disjointBitMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i.1 &&& j.1) = 0 then 1 else 0

/-- The `n × n` base-`(-2)` positive-carry parity matrix `H_n^{(cin)}(i, j) = (-1)^{negPosCarries cin i j}`. -/
def negParityMat (R : Type*) [CommRing R] (cin : ℤ) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (-1 : R) ^ negPosCarries cin i.1 j.1

/-- Difference matrix `K_n = H_n^{(-1)} - H_n^{(0)}`. -/
def negKMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  negParityMat R (-1) n - negParityMat R 0 n

/-- Sum matrix `J_n = H_n^{(+1)} + H_n^{(0)}`. -/
def negJMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  negParityMat R 1 n + negParityMat R 0 n

end NegabinaryCarryDet
