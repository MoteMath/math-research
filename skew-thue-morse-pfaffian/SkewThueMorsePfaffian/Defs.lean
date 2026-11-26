/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Core Definitions for Skew-Symmetric Thue-Morse Pfaffian (`skew-thue-morse-pfaffian`)

Pure-Mathlib definitions (no proofs) of binary popcount `binPopcount`, the Thue-Morse sign
`thueMorseSign n = (-1)^{s_2(n)}`, and the shifted skew-symmetric Thue-Morse matrix
`(A_n^{(s)})_{i, j} = sgn(j - i) * (-1)^{s_2(i + j + s)}` over any commutative ring `R`.
-/

namespace SkewThueMorsePfaffian

/-- Binary popcount (sum of base-2 digits) `s_2(n)`. -/
def binPopcount (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n % 2) + binPopcount (n / 2)

/-- Thue-Morse sign `(-1)^{s_2(n)}` in any commutative ring `R`. -/
def thueMorseSign {R : Type*} [CommRing R] (n : ℕ) : R :=
  (-1 : R) ^ binPopcount n

/-- Shifted skew-symmetric Thue-Morse matrix `A_n^{(s)}` of size `n × n` over `R`:
`(A_n^{(s)})_{i, j} = sgn(j - i) * (-1)^{s_2(i + j + s)}`. -/
def skewThueMorseMatrix {R : Type*} [CommRing R] (s n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if i.1 < j.1 then thueMorseSign (R := R) (i.1 + j.1 + s)
    else if j.1 < i.1 then -thueMorseSign (R := R) (i.1 + j.1 + s)
    else 0

end SkewThueMorsePfaffian
