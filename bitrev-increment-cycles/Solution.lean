/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitrevIncrementCycles

/-!
# Verified Solutions (`bitrev-increment-cycles`)

Provides exact, sorry-free, pure-`Init` proofs of every theorem in `Challenge.lean`.
-/

namespace BitrevIncrementChallenge

open BitrevIncrementCycles

theorem bitrevInc_odd_single_cycle (t : Nat) :
    IsSingleCycle (2 * t + 1) :=
  BitrevIncrementCycles.bitrevInc_odd_single_cycle t

theorem bitrevInc_even_zero_period (m : Nat) :
    iter (bitrevInc (2 * (m + 1))) (2 ^ (m + 2) - 1) 0 = 0 ∧
    ∀ s : Nat, 0 < s → s < 2 ^ (m + 2) - 1 → iter (bitrevInc (2 * (m + 1))) s 0 ≠ 0 :=
  BitrevIncrementCycles.bitrevInc_even_zero_period m

theorem bitrevInc_single_cycle_iff_odd (k : Nat) (hk : 1 ≤ k) :
    IsSingleCycle k ↔ k % 2 = 1 :=
  BitrevIncrementCycles.bitrevInc_single_cycle_iff_odd k hk

theorem bitrevInc_return_map (k m : Nat) (hk : 1 ≤ k) (hm : m < 2 ^ k) :
    (m = 2 ^ k - 1 → iter (bitrevInc (k + 2)) 3 (2 * m) = 0) ∧
    (m ≠ 2 ^ k - 1 → bitrevInc k m = 2 ^ k - 1 → iter (bitrevInc (k + 2)) 5 (2 * m) = 2) ∧
    (m ≠ 2 ^ k - 1 → bitrevInc k m ≠ 2 ^ k - 1 →
      iter (bitrevInc (k + 2)) 4 (2 * m) = 2 * bitrevInc k (bitrevInc k m)) :=
  BitrevIncrementCycles.bitrevInc_return_map k m hk hm

end BitrevIncrementChallenge
