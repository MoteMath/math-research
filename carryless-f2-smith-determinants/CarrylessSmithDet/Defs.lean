import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Log
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CarrylessSmithDet

open Polynomial

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Carry-less multiplication over `F_2[X]` encoded on natural numbers. -/
def clmul (a b : ℕ) : ℕ :=
  if a = 0 then 0
  else (if a % 2 = 1 then b else 0) ^^^ (clmul (a / 2) b <<< 1)
termination_by a

/-- Binary Hamming weight (population count) of a natural number. -/
def popcount (n : ℕ) : ℕ :=
  if n = 0 then 0 else n % 2 + popcount (n / 2)
termination_by n

/-- Canonical bijection from `ℕ` to `(ZMod 2)[X]` reading binary digits as coefficients. -/
noncomputable def natToPoly (n : ℕ) : Polynomial (ZMod 2) :=
  if n = 0 then 0
  else Polynomial.C ((n % 2 : ℕ) : ZMod 2) + Polynomial.X * natToPoly (n / 2)
termination_by n

/-- Inverse bijection from `(ZMod 2)[X]` to `ℕ`. -/
noncomputable def polyToNat (P : Polynomial (ZMod 2)) : ℕ :=
  ∑ k ∈ P.support, 2 ^ k

/-- Carry-less polynomial GCD over `F_2[X]` encoded back on `ℕ`. -/
noncomputable def clgcd (a b : ℕ) : ℕ :=
  polyToNat (EuclideanDomain.gcd (natToPoly a) (natToPoly b))

/-- Finite set of carry-less divisors of `m` in `{1, ..., m}`. -/
noncomputable def clDivisors (m : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun d : ℕ => natToPoly d ∣ natToPoly m)
  (Finset.Icc 1 m).filter (fun d => natToPoly d ∣ natToPoly m)

/-- Carry-less Möbius inversion `g = f *_cl μ_cl` defined recursively on the divisor poset. -/
noncomputable def clMobiusInv {R : Type*} [CommRing R] (f : ℕ → R) (m : ℕ) : R :=
  if m = 0 then 0
  else f m - ∑ d ∈ (clDivisors m).erase m,
    if d < m then clMobiusInv f d else 0
termination_by m

/-- Carry-less Euler totient `|((ZMod 2)[X] / (P_m))^\times|` for `m ≥ 1`. -/
noncomputable def clTotient (m : ℕ) : ℕ :=
  letI := Classical.decPred (fun a : ℕ => clgcd a m = 1)
  ((Finset.range (2 ^ Nat.log 2 m)).filter (fun a => clgcd a m = 1)).card

/-- `n × n` carry-less Smith GCD matrix `f(clgcd(i + 1, j + 1))`. -/
noncomputable def clgcdMat {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => f (clgcd (i.val + 1) (j.val + 1))

end CarrylessSmithDet
