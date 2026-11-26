/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Bitwise Carry Algebra

Pure-`Init` definitions (zero Mathlib) for binary carry words, Gray codes,
borrow words, popcount, maximal carry-block counts, and `2^k × 2^k` square sums.
-/

namespace BitwiseCarryAlgebra

/-- Binary carry word `(x + y) ^^^ x ^^^ y`: bit `r` is 1 iff adding `x` and `y` carries into bit `r`. -/
def carryWord (x y : Nat) : Nat :=
  (x + y) ^^^ x ^^^ y

/-- Binary reflected Gray code `x ^^^ (x >>> 1)`. -/
def gray (x : Nat) : Nat :=
  x ^^^ (x >>> 1)

/-- Symmetric unsigned borrow word `(max x y - min x y) ^^^ x ^^^ y`. -/
def borrowWord (x y : Nat) : Nat :=
  (max x y - min x y) ^^^ x ^^^ y

/-- Exact binary popcount (Hamming weight) of a natural number. -/
def popcnt (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 2 + popcnt (n / 2)
termination_by n
decreasing_by omega

/-- Number of maximal contiguous 1-bit runs (blocks) in the binary representation of `n`. -/
def blocks (n : Nat) : Nat :=
  if h : n = 0 then 0
  else blocks (n / 2) + if n % 2 = 1 ∧ (n / 2) % 2 = 0 then 1 else 0
termination_by n
decreasing_by omega

/-- Number of maximal carry chains generated when adding `x` and `y` in binary. -/
def carryBlocks (x y : Nat) : Nat :=
  blocks (carryWord x y)

/-- Sum of `f i` for `i = 0, 1, ..., n - 1`. -/
def sumRange (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => sumRange m f + f m

/-- Sum of `f i j` over `[0, 2^k) × [0, 2^k)`. -/
def sumSquare (k : Nat) (f : Nat → Nat → Nat) : Nat :=
  sumRange (2 ^ k) fun i => sumRange (2 ^ k) fun j => f i j

end BitwiseCarryAlgebra
