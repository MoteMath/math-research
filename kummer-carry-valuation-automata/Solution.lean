/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KummerCarryValuationAutomata

/-!
# Verified Solutions (`kummer-carry-valuation-automata`)
-/

namespace KummerCarryValuationAutomataChallenge

open CVAEngine

theorem v2_binom_add_popcount (a b : Nat) :
    v2 (binom (a + b) a) + popcount (a + b) = popcount a + popcount b :=
  CVAEngine.v2_binom_add_popcount a b

theorem v2_trinom_add_popcount (a b c : Nat) :
    v2 (trinom a b c) + popcount (a + b + c) = popcount a + popcount b + popcount c :=
  CVAEngine.v2_trinom_add_popcount a b c

theorem shifted_xor_kummer_exact (n : Nat) :
    2 * v2 (binom (n + (n ^^^ (2 * n))) n) = 2 * popcount n + popcount (n ^^^ (2 * n)) :=
  CVAEngine.shifted_xor_kummer_exact n

theorem shifted_or_kummer_exact (n : Nat) :
    v2 (binom (n + (n ||| (2 * n))) n) = popcount (n ||| (2 * n)) :=
  CVAEngine.shifted_or_kummer_exact n

theorem gray_binom_even (n : Nat) (hn : 1 ≤ n) :
    2 ∣ binom (n + gray n) n :=
  CVAEngine.gray_binom_even n hn

theorem gray_strictly_below_shifted_xor (n : Nat) (hn : 1 ≤ n) :
    v2 (binom (n + gray n) n) + 1 ≤ v2 (binom (n + (n ^^^ (2 * n))) n) :=
  CVAEngine.gray_strictly_below_shifted_xor n hn

theorem binom_11n_sharp_slope (n : Nat) (hn : 1 ≤ n) :
    2 * v2 (binom (11 * n) n) + 2 ≤ 5 * popcount n :=
  CVAEngine.binom_11n_sharp_slope n hn

theorem binom_55n_sharp_infinite (m : Nat) :
    4 * v2 (binom (55 * fam55 m) (fam55 m)) + 8 = 13 * popcount (fam55 m) ∧
    popcount (fam55 m) = 4 * m + 8 :=
  CVAEngine.binom_55n_sharp_infinite m

end KummerCarryValuationAutomataChallenge
