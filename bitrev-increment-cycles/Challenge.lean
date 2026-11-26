/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitrevIncrementCycles.Defs

/-!
# Trusted Challenge Statements (`bitrev-increment-cycles`)

Pure-`Init` (zero Mathlib) statements of the bit-reversal increment (`f_k(x) = (bitrev_k(x) + 1) % 2^k`)
return-map identity, full-period Hamiltonian cycle theorem for all odd bit-widths, exact short
orbit length `2^{m+1} - 1` of `0` for all even bit-widths `2m`, and the parity iff characterization.
-/

namespace BitrevIncrementChallenge

open BitrevIncrementCycles

/-- Theorem 1 (Odd bit-width Hamiltonian cycle): for every odd bit-width `k = 2t + 1`,
`f_k(x) = (bitrev_k(x) + 1) % 2^k` is a single full-period cycle of length `2^(2t + 1)`. -/
theorem bitrevInc_odd_single_cycle (t : Nat) :
    IsSingleCycle (2 * t + 1) := by
  sorry

/-- Theorem 2 (Exact even-width orbit period of `0`): for every even bit-width `k = 2(m + 1)`,
the orbit of `0` under `f_{2(m+1)}` has exact minimal period `2^(m + 2) - 1`. -/
theorem bitrevInc_even_zero_period (m : Nat) :
    iter (bitrevInc (2 * (m + 1))) (2 ^ (m + 2) - 1) 0 = 0 ∧
    ∀ s : Nat, 0 < s → s < 2 ^ (m + 2) - 1 → iter (bitrevInc (2 * (m + 1))) s 0 ≠ 0 := by
  sorry

/-- Theorem 3 (Parity dichotomy): for every `k ≥ 1`, `f_k(x) = (bitrev_k(x) + 1) % 2^k`
acts as a single cycle on `{0, ..., 2^k - 1}` if and only if `k` is odd. -/
theorem bitrevInc_single_cycle_iff_odd (k : Nat) (hk : 1 ≤ k) :
    IsSingleCycle k ↔ k % 2 = 1 := by
  sorry

/-- Theorem 4 (Exact `k → k + 2` return-map law): on the embedded slice `2 * m` (`(a=0, mid=m, b=0)`),
`f_{k+2}` returns in 3 steps from `2^k - 1` to `0`, in 5 steps from `f_k^{-1}(2^k - 1)` to `2`,
and in 4 steps from every other `m < 2^k` to `2 * f_k^2(m)`. -/
theorem bitrevInc_return_map (k m : Nat) (hk : 1 ≤ k) (hm : m < 2 ^ k) :
    (m = 2 ^ k - 1 → iter (bitrevInc (k + 2)) 3 (2 * m) = 0) ∧
    (m ≠ 2 ^ k - 1 → bitrevInc k m = 2 ^ k - 1 → iter (bitrevInc (k + 2)) 5 (2 * m) = 2) ∧
    (m ≠ 2 ^ k - 1 → bitrevInc k m ≠ 2 ^ k - 1 →
      iter (bitrevInc (k + 2)) 4 (2 * m) = 2 * bitrevInc k (bitrevInc k m)) := by
  sorry

end BitrevIncrementChallenge
