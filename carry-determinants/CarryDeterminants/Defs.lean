/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Core Definitions for Mixed-Radix Hankel and Carry Determinants

This file contains only definitions (no proofs) and imports Mathlib alone, so that
`Challenge.lean` can state every headline theorem transparently.
-/

namespace NovelCarry

/-- Mixed-radix place value `P_r = ∏_{j < r} b_j`. -/
def place (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => place b r * b r

/-- The `r`-th digit of `n` in mixed radix `b`. -/
def mdigit (b : ℕ → ℕ) (n r : ℕ) : ℕ :=
  (n / place b r) % b r

/-- Carry into position `r` when adding `i` and `j` in mixed radix `b`. -/
def carryIn (b : ℕ → ℕ) (i j r : ℕ) : ℕ :=
  (i % place b r + j % place b r) / place b r

/-- Carry out of position `r` (into position `r + 1`) when adding `i` and `j`. -/
def carryBit (b : ℕ → ℕ) (i j r : ℕ) : ℕ :=
  carryIn b i j (r + 1)

/-- Sum of the first `k` mixed-radix digits of `n`. -/
def mdigitSum (b : ℕ → ℕ) (k n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range k, mdigit b n r

/-- Total number of carries in the first `k` positions. -/
def carryCount (b : ℕ → ℕ) (k i j : ℕ) : ℕ :=
  ∑ r ∈ Finset.range k, carryBit b i j r

/-- Suffix product `Q_j = ∏_{t = j + 1}^{k - 1} b_t = place b k / place b (j + 1)`. -/
def suffixProd (b : ℕ → ℕ) (k j : ℕ) : ℕ :=
  place b k / place b (j + 1)

/-- The `n × n` multivariate mixed-radix carry matrix with weights `x : ℕ → R`. -/
def carryMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (k n : ℕ) (x : ℕ → R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ∏ r ∈ Finset.range k, (x r) ^ carryBit b i.1 j.1 r

/-- The weighted-exponent univariate polynomial carry matrix `x_r = X^(b_r - 1)`. -/
noncomputable def mixedCarryPolyMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (k n : ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial R) :=
  carryMatrix b k n (fun r => (Polynomial.X : Polynomial R) ^ (b r - 1))

/-- The uniform base-`B` univariate polynomial carry matrix `M_{i,j} = X^{c_B(i,j)}`. -/
noncomputable def baseCarryPolyMatrix {R : Type*} [CommRing R] (B k n : ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial R) :=
  Matrix.of fun i j => (Polynomial.X : Polynomial R) ^ carryCount (fun _ => B) k i.1 j.1

/-- Multiplicative mixed-radix digit function `f(n) = (∏_{r < k} y_r^{d_r(n)}) * y_k^{⌊n / N⌋}`. -/
def hankelDigitVal {R : Type*} [CommRing R] (b : ℕ → ℕ) (k : ℕ)
    (y : Fin (k + 1) → R) (n : ℕ) : R :=
  (∏ r : Fin k, (y r.castSucc) ^ mdigit b n r.1) * (y (Fin.last k)) ^ (n / place b k)

/-- The `N × N` multivariate mixed-radix multiplicative Hankel matrix (`N = place b k`). -/
def mixedHankelMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (k : ℕ)
    (y : Fin (k + 1) → R) : Matrix (Fin (place b k)) (Fin (place b k)) R :=
  Matrix.of fun i j => hankelDigitVal b k y (i.1 + j.1)

end NovelCarry
