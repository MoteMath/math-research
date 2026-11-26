/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Core Definitions for Mixed-Radix Zero-Carry Graph Spanning Trees

This file contains only definitions (no proofs) and imports Mathlib alone, so that
`Challenge.lean` can state every headline theorem transparently.
-/

namespace ZeroCarrySpanningTrees

/-- Mixed-radix place value `P_r = ∏_{j < r} b_j`. -/
def place (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => place b r * b r

/-- The `r`-th digit of `n` in mixed radix `b`. -/
def mdigit (b : ℕ → ℕ) (n r : ℕ) : ℕ :=
  (n / place b r) % b r

/-- Boolean adjacency predicate of the mixed-radix zero-carry graph on `{0, ..., P_k - 1}`:
distinct vertices `i ≠ j` are adjacent iff `i + j` produces zero carries across positions `< k`. -/
def zeroCarryAdjBool (b : ℕ → ℕ) (k i j : ℕ) : Bool :=
  decide (i ≠ j ∧ ∀ r ∈ Finset.range k, mdigit b i r + mdigit b j r < b r)

/-- Degree of vertex `i` in the mixed-radix zero-carry graph on `{0, ..., P_k - 1}`. -/
def zeroCarryDeg (b : ℕ → ℕ) (k i : ℕ) : ℕ :=
  ((Finset.range (place b k)).filter (fun j => zeroCarryAdjBool b k i j = true)).card

/-- Laplacian matrix `L = D - A` of the mixed-radix zero-carry graph on `Fin (place b k)`. -/
def zeroCarryLaplacian {R : Type*} [CommRing R] (b : ℕ → ℕ) (k : ℕ) :
    Matrix (Fin (place b k)) (Fin (place b k)) R :=
  Matrix.of fun i j =>
    if i = j then (zeroCarryDeg b k i.1 : R)
    else if zeroCarryAdjBool b k i.1 j.1 = true then (-1 : R)
    else 0

/-- Principal `(0, 0)`-cofactor of `zeroCarryLaplacian` on `Fin (place b k - 1)`,
whose determinant equals the Kirchhoff spanning-tree count `τ(G_b)`. -/
def zeroCarryCofactor {R : Type*} [CommRing R] (b : ℕ → ℕ) (k : ℕ) :
    Matrix (Fin (place b k - 1)) (Fin (place b k - 1)) R :=
  Matrix.of fun i j =>
    if i = j then (zeroCarryDeg b k (i.1 + 1) : R)
    else if zeroCarryAdjBool b k (i.1 + 1) (j.1 + 1) = true then (-1 : R)
    else 0

/-- Normalized mixed-radix zero-carry transition matrix `W = B^{-1} T` over `ℚ`, where
`B_{i,i} = ∏_{r < k} (b_r - d_r(i))` and `T_{i,j} = 1` iff `∀ r < k, d_r(i) + d_r(j) < b_r`. -/
def zeroCarryWalkMatrix (b : ℕ → ℕ) (k : ℕ) :
    Matrix (Fin (place b k)) (Fin (place b k)) ℚ :=
  Matrix.of fun i j =>
    if ∀ r ∈ Finset.range k, mdigit b i.1 r + mdigit b j.1 r < b r then
      (∏ r ∈ Finset.range k, ((b r - mdigit b i.1 r : ℕ) : ℚ))⁻¹
    else 0

/-- Degree of vertex `i` in the binary zero-carry (bitwise-disjoint) graph on `{0, ..., 2^k - 1}`
defined directly via native bitwise AND `i &&& j = 0`. -/
def binaryZeroCarryDeg (k i : ℕ) : ℕ :=
  ((Finset.range (2 ^ k)).filter (fun j => decide (i ≠ j ∧ (i &&& j) = 0))).card

/-- Principal `(0, 0)`-cofactor of the Laplacian of the binary zero-carry graph
`i ~ j ↔ i ≠ j ∧ (i &&& j) = 0` on `Fin (2^k)`. -/
def binaryZeroCarryCofactor {R : Type*} [CommRing R] (k : ℕ) :
    Matrix (Fin (2 ^ k - 1)) (Fin (2 ^ k - 1)) R :=
  Matrix.of fun i j =>
    if i = j then (binaryZeroCarryDeg k (i.1 + 1) : R)
    else if (i.1 + 1) &&& (j.1 + 1) = 0 then (-1 : R)
    else 0

end ZeroCarrySpanningTrees
