/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse.Defs

/-!
# Trusted Challenge Statements (`ssm-decay-collapse-bounds`)

Universal and exact pure-`Init` Lean 4 statements for:
1. Exact IEEE-754 RNE decay-stall midpoint quantization law for all mantissa widths `p ≥ 1`,
   specialized to FP8-E5M2 (`p = 2`), FP8-E4M3 (`p = 3`), BF16 (`p = 7`), FP16 (`p = 10`),
   and FP32 (`p = 23`).
2. Universal one-ULP-per-step sequential decay collapse law `seqPow p (m * 2^p) = 2^(-m)`
   for all `p ≥ 1` and `m : Nat` (exact effective half-life `2^p` tokens: `128` in BF16,
   and `2^(-32)` at `T = 4096`).
3. Exact linear additive swamping divergence `|h_exact(T) - h_seq(T)| = T * 2^(-(p + 1))`
   under IEEE-754 RNE tie-to-even (`h_0 = 1, a_t = 1, b_t = 2^(-(p + 1))`).
4. Tight asymmetric signed-integer invariant bounds `[-2^R B_max, 2^R B_max + (2^R - 1)]`
   for the zero-multiplier 1-tap shift-subtract recurrence, with exact attainment of both
   endpoints.
5. Zero-input signed stall asymmetry: positive states `0 ≤ h < 2^r` stall permanently as
   fixed points, while every strictly negative state `h < 0` strictly increases and reaches
   `0` in finitely many steps.
6. Exact `2 → 3/2` worst-case adjacent decay-rate ratio reduction via 2-tap zero-multiplier
   CSD shift-subtract, alongside 5-bit `2^24` scale range vs BF16's `2^8` (`65,536×` wider).
-/

namespace SsmDecayCollapseChallenge

open SsmDecayCollapse

/-- Theorem 1 (Exact IEEE-754 RNE Decay-Stall & Midpoint Quantization Law):
    For every `p ≥ 1`, `aMax p = 1 - 2^(-(p + 1))` is the largest normal IEEE-754 value
    strictly below `1`, the exact RNE midpoint `aStall p = 1 - 2^(-(p + 2))` rounds to `1`,
    every `a ∈ [aStall p, 1]` rounds to `1`, every `a ∈ [aMax p, aStall p)` rounds to
    `aMax p`, with exact rational instantiations for FP8-E5M2, FP8-E4M3, BF16, FP16, FP32. -/
theorem ieee_decay_stall_midpoint_exact :
    (∀ p : Nat, 1 ≤ p →
      IsIeeeNormal p (aMax p) ∧
      aMax p < 1 ∧
      (∀ x : Rat, IsIeeeNormal p x → x < 1 → x ≤ aMax p) ∧
      ieeeRne p (aStall p) = 1 ∧
      (∀ a : Rat, aStall p ≤ a → a ≤ 1 → ieeeRne p a = 1) ∧
      (∀ a : Rat, aMax p ≤ a → a < aStall p → ieeeRne p a = aMax p)) ∧
    (aMax 2 = 7 / 8 ∧ aStall 2 = 15 / 16) ∧
    (aMax 3 = 15 / 16 ∧ aStall 3 = 31 / 32) ∧
    (aMax 7 = 255 / 256 ∧ aStall 7 = 511 / 512) ∧
    (aMax 10 = 2047 / 2048 ∧ aStall 10 = 4095 / 4096) ∧
    (aMax 23 = 16777215 / 16777216 ∧ aStall 23 = 33554431 / 33554432) := by
  sorry

/-- Theorem 2 (Universal One-ULP-Per-Step Sequential Decay Collapse Law):
    Under bit-exact IEEE-754 RNE sequential multiplication by `aMax p = 1 - 2^(-(p + 1))`,
    every step decrements the normal significand/binade representation by exactly 1 ULP,
    yielding the exact closed form `seqPow p (m * 2^p) = 2^(-m)` for all `p ≥ 1` and all
    `m : Nat`, exact effective half-life `2^p` tokens (`128` in BF16), and `2^(-32)` at
    `T = 4096` in BF16. -/
theorem one_ulp_per_step_sequential_collapse :
    (∀ (p : Nat) (k : Int) (m : Nat), 0 < m → m < 2 ^ p →
      ieeeRne p (floatVal p k m * aMax p) = floatVal p k (m - 1)) ∧
    (∀ (p : Nat) (k : Int),
      ieeeRne p (floatVal p k 0 * aMax p) = floatVal p (k - 1) (2 ^ p - 1)) ∧
    (∀ (p m : Nat), 1 ≤ p → seqPow p (m * 2 ^ p) = zpow2 (-(m : Int))) ∧
    (∀ p : Nat, 1 ≤ p → seqPow p (2 ^ p) = 1 / 2) ∧
    (seqPow 7 128 = 1 / 2 ∧ seqPow 7 4096 = zpow2 (-32)) := by
  sorry

/-- Theorem 3 (Exact Linear Additive Swamping Divergence):
    When `h_0 = 1, a_t = 1, b_t = 2^(-(p + 1))`, IEEE-754 RNE tie-to-even stalls sequential
    accumulation permanently at `1.0`, while exact/tree accumulation grows linearly, giving
    `|exactAccum - seqAccum| = T * 2^(-(p + 1))` for all `p ≥ 1` and `T : Nat` (explicitly
    `4` at `T = 1024` and `512` at `T = 131072` in BF16). -/
theorem additive_swamping_exact_divergence :
    (∀ (p : Nat), 1 ≤ p → ∀ (T : Nat),
      seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T = 1 ∧
      ratAbs (exactAccum (zpow2 (-((p + 1 : Nat) : Int))) T -
        seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T) =
        (T : Rat) * zpow2 (-((p + 1 : Nat) : Int))) ∧
    (exactAccum (zpow2 (-8)) 1024 = 5 ∧ seqAccum 7 (zpow2 (-8)) 1024 = 1 ∧
      ratAbs (exactAccum (zpow2 (-8)) 1024 - seqAccum 7 (zpow2 (-8)) 1024) = 4) ∧
    (exactAccum (zpow2 (-8)) 131072 = 513 ∧ seqAccum 7 (zpow2 (-8)) 131072 = 1 ∧
      ratAbs (exactAccum (zpow2 (-8)) 131072 - seqAccum 7 (zpow2 (-8)) 131072) = 512) := by
  sorry

/-- Theorem 4 (Tight Asymmetric Invariant Bounds for Zero-Multiplier Shift-Subtract):
    For `h_{t+1} = h_t - floor(h_t / 2^r) + b_t` with `|b_t| ≤ B_max` (`0 ≤ B_max`) and
    `1 ≤ r ≤ R`, the interval `[-2^R B_max, 2^R B_max + (2^R - 1)]` is invariant, BOTH
    endpoints are tightly attained as fixed points at `r = R`, and their sum is `2^R - 1`. -/
theorem dyadic_shift_subtract_tight_bounds :
    (∀ (r R : Nat) (Bmax h b : Int),
      1 ≤ r → r ≤ R → 0 ≤ Bmax →
      shiftSubMin R Bmax ≤ h → h ≤ shiftSubMax R Bmax →
      -Bmax ≤ b → b ≤ Bmax →
      shiftSubMin R Bmax ≤ shiftSubStep r h b ∧ shiftSubStep r h b ≤ shiftSubMax R Bmax) ∧
    (∀ (R : Nat) (Bmax : Int),
      shiftSubStep R (shiftSubMax R Bmax) Bmax = shiftSubMax R Bmax ∧
      shiftSubStep R (shiftSubMin R Bmax) (-Bmax) = shiftSubMin R Bmax) ∧
    (∀ (R : Nat) (Bmax : Int),
      shiftSubMax R Bmax + shiftSubMin R Bmax = ((2 ^ R : Nat) : Int) - 1) := by
  sorry

/-- Theorem 5 (Zero-Input Signed Stall Asymmetry):
    Under zero input (`b_t = 0`), every state `0 ≤ h < 2^r` is a permanent fixed point,
    whereas for every `r ≥ 1`, every strictly negative state `h < 0` strictly increases
    (`h < h' ≤ 0`) and reaches `0` in finitely many steps. -/
theorem dyadic_shift_subtract_zero_input_stall_asymmetry :
    (∀ (r : Nat) (h : Int), 0 ≤ h → h < ((2 ^ r : Nat) : Int) →
      shiftSubStep r h 0 = h ∧ ∀ n : Nat, shiftSubIter r h n = h) ∧
    (∀ (r : Nat) (h : Int), 1 ≤ r → h < 0 →
      h < shiftSubStep r h 0 ∧
      shiftSubStep r h 0 ≤ 0 ∧
      ∃ n : Nat, shiftSubIter r h n = 0) := by
  sorry

/-- Theorem 6 (2-Tap CSD Shift-Subtract Adjacent Decay-Rate Gap Reduction):
    Adding a second zero-multiplier CSD tap `1 - 2^(-r) - c * 2^(-(r + 1))` (`c ∈ {false, true}`)
    reduces the worst-case adjacent decay-rate ratio from `2` strictly down to `3 / 2`
    (exact alternating ratios `3 / 2` and `4 / 3`) for all `r ≥ 1`, while 5-bit `r ∈ {1..24}`
    spans `2^24` inverse decay-rate range vs BF16's `2^8` (`65,536×` wider). -/
theorem csd_two_tap_half_life_gap_reduction :
    (∀ r : Nat, 1 ≤ r →
      (1 - oneTapDecay r) / (1 - oneTapDecay (r + 1)) = 2) ∧
    (∀ r : Nat, 1 ≤ r →
      (1 - twoTapCsdDecay r true) / (1 - twoTapCsdDecay r false) = 3 / 2 ∧
      (1 - twoTapCsdDecay r false) / (1 - twoTapCsdDecay (r + 1) true) = 4 / 3 ∧
      (1 - twoTapCsdDecay r false) / (1 - twoTapCsdDecay (r + 1) true) < 3 / 2 ∧
      (3 / 2 : Rat) < 2) ∧
    ((1 : Rat) / (1 - oneTapDecay 24) = ((2 ^ 24 : Nat) : Rat) ∧
      (1 : Rat) / (1 - aMax 7) = ((2 ^ 8 : Nat) : Rat) ∧
      ((2 ^ 24 : Nat) : Rat) / ((2 ^ 8 : Nat) : Rat) = 65536) := by
  sorry

end SsmDecayCollapseChallenge
