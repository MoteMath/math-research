/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitwiseGrundyPeriodicityCompiler

/-!
# Verified Solutions (`bitwise-grundy-periodicity-compiler`)
-/

namespace BitwiseGrundyPeriodicityCompilerChallenge

open BitwiseGrundyCompiler

theorem kummer_borrow_popcount (n s : Nat) (hsn : s ≤ n) :
    popcount (n - s) + popcount s = popcount n + borrowCount n s :=
  BitwiseGrundyCompiler.kummer_borrow_popcount n s hsn

theorem borrowCount_le_shift_inv (s k B n m : Nat) (hsk : s < 2 ^ k) (hsn : s ≤ n) :
    borrowCount (n + m * 2 ^ (k + B)) s ≤ B ↔ borrowCount n s ≤ B :=
  BitwiseGrundyCompiler.borrowCount_le_shift_inv s k B n m hsk hsn

theorem isWinningMulti_iff_nimSum_ne_zero (G : BitGame) (hs : List Nat) :
    IsWinningMulti G hs ↔ nimSum (hs.map (grundy G)) ≠ 0 :=
  BitwiseGrundyCompiler.isWinningMulti_iff_nimSum_ne_zero G hs

theorem dyadic_borrow_wall_periodicity (G : BitGame)
    (hwall : ∀ r ∈ G, isWallGuard r.guard = true) :
    ∀ n, grundy G (n + 2 ^ gameShiftBits G) = grundy G n :=
  BitwiseGrundyCompiler.dyadic_borrow_wall_periodicity G hwall

theorem checkCert_sound_grundy (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, grundy G n = evalPeriodic c n :=
  BitwiseGrundyCompiler.checkCert_sound_grundy G c h

theorem G_coprime_p5_period_5 :
    ∀ n, 15 ≤ n → grundy G_coprime_p5 (n + 5) = grundy G_coprime_p5 n :=
  BitwiseGrundyCompiler.G_coprime_p5_period_5

theorem grundyParity_not_eventually_periodic :
    ∀ n0 p, p > 0 → ∃ n, n0 ≤ n ∧ grundyParity (n + p) ≠ grundyParity n :=
  BitwiseGrundyCompiler.grundyParity_not_eventually_periodic

theorem grundyParity_oneHeap_periodic_vs_twoHeap_aperiodic :
    (∀ n, 12 ≤ n → (grundyParity n ≠ 0 ↔ n % 4 = 0 ∨ n % 4 = 3)) ∧
    (∀ k, 3 ≤ k → (grundyParity (4 * k) ^^^ grundyParity 4 = 0 ↔ ctz k % 2 = 0)) :=
  BitwiseGrundyCompiler.grundyParity_oneHeap_periodic_vs_twoHeap_aperiodic

end BitwiseGrundyPeriodicityCompilerChallenge
