/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Core Definitions for Carry-Less `F_2[x]`-Lift Monomial Determinants (`clmul-lift-determinants`)

Pure-Mathlib definitions (no proofs) of binary carry-less multiplication `clmul`, binary `{0, 1}`-lift
polynomial evaluation `bitPolyEval`, and the odd carry-less-multiplication lift matrix
`(M_n(t))_{i, j} = bitPolyEval t (clmul (2i + 1) (2j + 1))` over any commutative ring `R`.
-/

namespace ClmulLiftDeterminants

/-- Carry-less multiplication of binary integers (`P_a * P_b` in `F_2[x]` packed into `ℕ`). -/
def clmul (a b : ℕ) : ℕ :=
  if b = 0 then 0 else (if b % 2 = 1 then a else 0) ^^^ (2 * clmul a (b / 2))

/-- Evaluates the `{0, 1}`-coefficient polynomial encoded by the binary bits of `n` at `t ∈ R`:
`bitPolyEval t n = ∑_{r : n.testBit r} t^r`. -/
def bitPolyEval {R : Type*} [CommRing R] (t : R) (n : ℕ) : R :=
  if n = 0 then 0 else (if n % 2 = 1 then 1 else 0) + t * bitPolyEval t (n / 2)

/-- The `n × n` odd carry-less-multiplication lift matrix over `R`:
`(M_n(t))_{i, j} = lift_Z(P_{2i + 1} *_{F_2[x]} P_{2j + 1})(t)`. -/
def oddClmulMatrix {R : Type*} [CommRing R] (t : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => bitPolyEval t (clmul (2 * i.1 + 1) (2 * j.1 + 1))

end ClmulLiftDeterminants
