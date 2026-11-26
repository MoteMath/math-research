/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BinaryLynessPeriods.Defs

/-!
# Trusted Challenge Statements (`binary-lyness-periods`)

Statements of the general even-carry (period 6) and odd-carry (period 12) XOR-Feistel
carry-renormalization laws, universal period 6 of `F_{2^r}(x, y) = (y, x ^^^ (y + 2^r))`,
the exact power-of-two periodicity dichotomy on unbounded `Nat × Nat`, and universal period 12
of the bitwise-OR twin `H_{2^r}(x, y) = (y, x ^^^ (y ||| (y + 2^r)))`.
-/

namespace BinaryLynessChallenge

open BinaryLynessPeriods

/-- Theorem 1 (General even-carry period-6 law):
for ANY functions `f h : Nat → Nat` with `f (2k) = 2k + 1` and `f (2k + 1) = 2 * h k`,
every pair `(x, y)` outside the odd-odd sector returns to itself in 6 steps. -/
theorem feistelStep_iter_six_of_even_parity (f h : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * h k)
    (x y : Nat) (hpar : x % 2 = 0 ∨ y % 2 = 0) :
    iter (feistelStep f) 6 (x, y) = (x, y) := by
  sorry

/-- Theorem 2 (General odd-carry period-12 law):
for ANY functions `f g : Nat → Nat` with `f (2k) = 2k + 1` and `f (2k + 1) = 2 * g k + 1`,
EVERY pair `(x, y) : Nat × Nat` returns to itself in 12 steps. -/
theorem feistelStep_iter_twelve_of_odd_parity (f g : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * g k + 1)
    (x y : Nat) :
    iter (feistelStep f) 12 (x, y) = (x, y) := by
  sorry

/-- Theorem 3 (Universal period 6 for Binary Lyness at every power of 2):
for every `r : Nat` and all `x y : Nat`, `F_{2^r}^6(x, y) = (x, y)` over unbounded `Nat × Nat`. -/
theorem lynessStep_pow_two_period_six (r x y : Nat) :
    iter (lynessStep (2 ^ r)) 6 (x, y) = (x, y) := by
  sorry

/-- Theorem 4 (Exact power-of-two period-6 dichotomy over unbounded `Nat × Nat`):
`F_c(x, y) = (y, x ^^^ (y + c))` satisfies `F_c^6 = id` on all of `Nat × Nat` if and only if
`c = 0` or `c = 2^r` for some `r : Nat`. -/
theorem lynessStep_period_six_iff (c : Nat) :
    (∀ x y : Nat, iter (lynessStep c) 6 (x, y) = (x, y)) ↔
    (c = 0 ∨ ∃ r : Nat, c = 2 ^ r) := by
  sorry

/-- Theorem 5 (Universal period 12 for the Bitwise-OR Binary Lyness twin at every power of 2):
for every `r : Nat` and all `x y : Nat`, `H_{2^r}^{12}(x, y) = (x, y)` over unbounded `Nat × Nat`. -/
theorem orLynessStep_pow_two_period_twelve (r x y : Nat) :
    iter (orLynessStep (2 ^ r)) 12 (x, y) = (x, y) := by
  sorry

end BinaryLynessChallenge
