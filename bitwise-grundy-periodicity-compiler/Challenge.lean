/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitwiseGrundyPeriodicityCompiler.Defs

/-!
# Trusted Challenge Statements (`bitwise-grundy-periodicity-compiler`)

Statements about subtraction games whose move legality depends on the binary borrow/carry
structure of `n - s`: the Kummer borrow-popcount identity, dyadic localization of borrow counts,
the full multi-heap Sprague-Grundy XOR theorem, the dyadic borrow-wall periodicity theorem for
every wall-guarded game, the soundness of the certificate compiler `checkCert` (exact Grundy
equivalence for all `n`), a coprime-period (period 5) showcase game, and the provably aperiodic
borrow-parity game together with its periodic 1-heap vs aperiodic 2-heap split.
-/

namespace BitwiseGrundyPeriodicityCompilerChallenge

open BitwiseGrundyCompiler

/-- Theorem 1 (Kummer borrow-popcount identity):
for all `s ≤ n`, `popcount (n - s) + popcount s = popcount n + borrowCount n s`. -/
theorem kummer_borrow_popcount (n s : Nat) (hsn : s ≤ n) :
    popcount (n - s) + popcount s = popcount n + borrowCount n s := by
  sorry

/-- Theorem 2 (Borrow-count dyadic localization):
for `s < 2^k` and `s ≤ n`, adding any multiple of `2^(k + B)` preserves `borrowCount n s ≤ B`. -/
theorem borrowCount_le_shift_inv (s k B n m : Nat) (hsk : s < 2 ^ k) (hsn : s ≤ n) :
    borrowCount (n + m * 2 ^ (k + B)) s ≤ B ↔ borrowCount n s ≤ B := by
  sorry

/-- Theorem 3 (Full multi-heap Sprague-Grundy XOR theorem):
for ANY bitwise/carry subtraction game `G` and ANY finite list of heaps `hs`,
`IsWinningMulti G hs ↔ nimSum (hs.map (grundy G)) ≠ 0`. -/
theorem isWinningMulti_iff_nimSum_ne_zero (G : BitGame) (hs : List Nat) :
    IsWinningMulti G hs ↔ nimSum (hs.map (grundy G)) ≠ 0 := by
  sorry

/-- Theorem 4 (Dyadic borrow-wall periodicity):
every game all of whose guards are wall guards is purely periodic from `n = 0`
with period `2 ^ gameShiftBits G`. -/
theorem dyadic_borrow_wall_periodicity (G : BitGame)
    (hwall : ∀ r ∈ G, isWallGuard r.guard = true) :
    ∀ n, grundy G (n + 2 ^ gameShiftBits G) = grundy G n := by
  sorry

/-- Theorem 5 (Soundness of the certificate compiler):
if the executable checker accepts a finite certificate `c`, then `grundy G n = evalPeriodic c n`
for ALL `n : Nat`. -/
theorem checkCert_sound_grundy (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, grundy G n = evalPeriodic c n := by
  sorry

/-- Theorem 6 (Odd period `5` coprime to the dyadic gate):
the game `{2 (borrowFree), 3 (always), 7 (always)}` has Grundy sequence of period `5` for all `n ≥ 15`. -/
theorem G_coprime_p5_period_5 :
    ∀ n, 15 ≤ n → grundy G_coprime_p5 (n + 5) = grundy G_coprime_p5 n := by
  sorry

/-- Theorem 7 (Borrow-parity aperiodicity):
for EVERY preperiod `n0` and EVERY candidate period `p > 0`, some `n ≥ n0` has
`grundyParity (n + p) ≠ grundyParity n`. -/
theorem grundyParity_not_eventually_periodic :
    ∀ n0 p, p > 0 → ∃ n, n0 ≤ n ∧ grundyParity (n + p) ≠ grundyParity n := by
  sorry

/-- Theorem 8 (Periodic 1-heap vs aperiodic 2-heap split in the borrow-parity game):
for `n ≥ 12` the 1-heap winning set has period `4`, yet the 2-heap Nim-sum `(4k, 4)` is losing
iff `ctz k` is even. -/
theorem grundyParity_oneHeap_periodic_vs_twoHeap_aperiodic :
    (∀ n, 12 ≤ n → (grundyParity n ≠ 0 ↔ n % 4 = 0 ∨ n % 4 = 3)) ∧
    (∀ k, 3 ≤ k → (grundyParity (4 * k) ^^^ grundyParity 4 = 0 ↔ ctz k % 2 = 0)) := by
  sorry

end BitwiseGrundyPeriodicityCompilerChallenge
