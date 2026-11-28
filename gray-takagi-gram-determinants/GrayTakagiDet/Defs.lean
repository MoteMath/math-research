import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GrayTakagiDet

/-- Reflected binary Gray code `gray n = n XOR (n / 2)`. -/
def gray (n : ℕ) : ℕ :=
  n ^^^ (n / 2)

/-- Binary Hamming weight (population count) of a natural number. -/
def popcount (n : ℕ) : ℕ :=
  if n = 0 then 0 else n % 2 + popcount (n / 2)
termination_by n

/-- Cumulative Hamming weight of the first `n` Gray-code words. -/
def grayPopSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, popcount (gray i)

/-- Discrete Takagi (Blancmange) fractal function:
`takagi 0 = takagi 1 = 0` and `takagi (2^m + k) = takagi k + min k (2^m - k)` for `0 ≤ k ≤ 2^m`. -/
def takagi (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0
  else
    let m := Nat.log 2 (n - 1)
    let k := n - 2 ^ m
    have hk : k < n := by
      have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
      omega
    takagi k + min k (2 ^ m - k)
termination_by n

/-- Symbolic `q`-deformed Gray-code bitwise-AND Gram matrix `q^(popcount(gray i &&& gray j))`. -/
def grayAndMat {R : Type*} [CommRing R] (q : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => q ^ popcount (gray i.val &&& gray j.val)

/-- Symbolic `q`-deformed Gray-code bitwise-OR Gram matrix `q^(popcount(gray i ||| gray j))`. -/
def grayOrMat {R : Type*} [CommRing R] (q : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => q ^ popcount (gray i.val ||| gray j.val)

/-- Symbolic `q`-deformed Gray-code Hamming-distance (`XOR`) matrix `q^(popcount(gray i ^^^ gray j))`. -/
def grayXorMat {R : Type*} [CommRing R] (q : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => q ^ popcount (gray i.val ^^^ gray j.val)

/-- Gray-code bitwise-disjointness `{0,1}` matrix `1[gray i &&& gray j = 0]`. -/
def grayDisjointMat {R : Type*} [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (gray i.val &&& gray j.val) = 0 then 1 else 0

end GrayTakagiDet
