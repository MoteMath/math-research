/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BinaryLynessPeriods

/-!
# Verified Solutions (`binary-lyness-periods`)
-/

namespace BinaryLynessChallenge

open BinaryLynessPeriods

theorem feistelStep_iter_six_of_even_parity (f h : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * h k)
    (x y : Nat) (hpar : x % 2 = 0 ∨ y % 2 = 0) :
    iter (feistelStep f) 6 (x, y) = (x, y) :=
  BinaryLynessPeriods.feistelStep_iter_six_of_even_parity f h heven hodd x y hpar

theorem feistelStep_iter_twelve_of_odd_parity (f g : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * g k + 1)
    (x y : Nat) :
    iter (feistelStep f) 12 (x, y) = (x, y) :=
  BinaryLynessPeriods.feistelStep_iter_twelve_of_odd_parity f g heven hodd x y

theorem lynessStep_pow_two_period_six (r x y : Nat) :
    iter (lynessStep (2 ^ r)) 6 (x, y) = (x, y) :=
  BinaryLynessPeriods.lynessStep_pow_two_period_six r x y

theorem lynessStep_period_six_iff (c : Nat) :
    (∀ x y : Nat, iter (lynessStep c) 6 (x, y) = (x, y)) ↔
    (c = 0 ∨ ∃ r : Nat, c = 2 ^ r) :=
  BinaryLynessPeriods.lynessStep_period_six_iff c

theorem orLynessStep_pow_two_period_twelve (r x y : Nat) :
    iter (orLynessStep (2 ^ r)) 12 (x, y) = (x, y) :=
  BinaryLynessPeriods.orLynessStep_pow_two_period_twelve r x y

end BinaryLynessChallenge
