/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Bit-Reversal Increment Cycles (`bitrev-increment-cycles`)

Pure-`Init` (zero Mathlib) definitions of `k`-bit reversal, the bit-reversal increment map
`f_k(x) = (bitrev k x + 1) % 2^k`, and iteration `iter f n x`.
-/

namespace BitrevIncrementCycles

/-- `k`-bit reversal of a natural number `x`: reverses the lowest `k` bits of `x`. -/
def bitrev : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => (x % 2) * 2 ^ k + bitrev k (x / 2)

/-- The `k`-bit reversal-plus-one permutation `f_k(x) = (bitrev k x + 1) % 2^k`. -/
def bitrevInc (k x : Nat) : Nat :=
  (bitrev k x + 1) % 2 ^ k

/-- `n`-fold iteration of a function `f : Nat → Nat`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- Predicate stating that `bitrevInc k` acts as a single full-period cycle of length `2^k`
on `{0, ..., 2^k - 1}` (starting from `0`, it returns to `0` at step `2^k` and visits every
`x < 2^k` in strictly fewer than `2^k` steps). -/
def IsSingleCycle (k : Nat) : Prop :=
  iter (bitrevInc k) (2 ^ k) 0 = 0 ∧
  ∀ x : Nat, x < 2 ^ k → ∃ s : Nat, s < 2 ^ k ∧ iter (bitrevInc k) s 0 = x

end BitrevIncrementCycles
