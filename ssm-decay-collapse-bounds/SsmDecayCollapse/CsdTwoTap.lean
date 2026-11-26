/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse.RatZpow

/-!
# Theorem 6: 2-Tap CSD Shift-Subtract Adjacent Decay-Rate Gap Reduction (`2 → 3/2`)

Proves that adding a second zero-multiplier Canonical Signed Digit (CSD) tap
`twoTapCsdDecay r c = 1 - 2^(-r) - c * 2^(-(r + 1))` (`c ∈ {false, true}`)
reduces the worst-case adjacent decay-rate ratio `(1 - a_fast) / (1 - a_slow)`
universally across all `r ≥ 1` from `2` (1-tap) strictly down to `3 / 2` (exact
alternating ratios `3 / 2` and `4 / 3`), while 5-bit `r ∈ {1..24}` already spans
an inverse decay-rate range of `2^24` (vs BF16's `2^8`, `65,536x` wider, and far
exceeding BF16's `2^7` mantissa grid).
-/

namespace SsmDecayCollapse

theorem oneTap_decay_rate (r : Nat) :
    1 - oneTapDecay r = zpow2 (-(r : Int)) := by
  unfold oneTapDecay
  grind

theorem twoTap_decay_rate_false (r : Nat) :
    1 - twoTapCsdDecay r false = zpow2 (-(r : Int)) := by
  unfold twoTapCsdDecay
  simp only [Bool.false_eq_true, ↓reduceIte]
  grind

theorem twoTap_decay_rate_true (r : Nat) :
    1 - twoTapCsdDecay r true = 3 * zpow2 (-((r + 1 : Nat) : Int)) := by
  unfold twoTapCsdDecay
  simp only [↓reduceIte]
  have h1 : zpow2 (-(r : Int)) = 2 * zpow2 (-((r + 1 : Nat) : Int)) := by
    have heq : -(r : Int) = -((r + 1 : Nat) : Int) + 1 := by omega
    rw [heq, zpow2_add_one, Rat.mul_comm]
  rw [h1]
  grind

theorem oneTap_adjacent_ratio (r : Nat) :
    (1 - oneTapDecay r) / (1 - oneTapDecay (r + 1)) = 2 := by
  rw [oneTap_decay_rate, oneTap_decay_rate]
  have heq : -(r : Int) = -((r + 1 : Nat) : Int) + 1 := by omega
  rw [heq, zpow2_add_one, Rat.div_def, Rat.mul_comm (zpow2 _) 2, Rat.mul_assoc,
    Rat.mul_inv_cancel _ (zpow2_ne_zero _), Rat.mul_one]

theorem twoTap_adjacent_ratio_same_r (r : Nat) :
    (1 - twoTapCsdDecay r true) / (1 - twoTapCsdDecay r false) = 3 / 2 := by
  rw [twoTap_decay_rate_true, twoTap_decay_rate_false]
  have h1 : zpow2 (-(r : Int)) = 2 * zpow2 (-((r + 1 : Nat) : Int)) := by
    have heq : -(r : Int) = -((r + 1 : Nat) : Int) + 1 := by omega
    rw [heq, zpow2_add_one, Rat.mul_comm]
  rw [h1, Rat.div_def, rat_mul_inv_eq (by decide : (2 : Rat) ≠ 0) (zpow2_ne_zero _)]
  rw [Rat.mul_assoc, ← Rat.mul_assoc (zpow2 _) (zpow2 _)⁻¹,
    Rat.mul_inv_cancel _ (zpow2_ne_zero _), Rat.one_mul, ← Rat.div_def]

theorem twoTap_adjacent_ratio_cross_r (r : Nat) :
    (1 - twoTapCsdDecay r false) / (1 - twoTapCsdDecay (r + 1) true) = 4 / 3 := by
  rw [twoTap_decay_rate_false, twoTap_decay_rate_true]
  have h1 : zpow2 (-(r : Int)) = 4 * zpow2 (-((r + 2 : Nat) : Int)) := by
    have heq : -(r : Int) = -((r + 2 : Nat) : Int) + ((2 : Nat) : Int) := by omega
    rw [heq, zpow2_add, zpow2_ofNat, Rat.mul_comm]
    rfl
  rw [h1, Rat.div_def, rat_mul_inv_eq (by decide : (3 : Rat) ≠ 0) (zpow2_ne_zero _)]
  rw [Rat.mul_assoc, ← Rat.mul_assoc (zpow2 _) (zpow2 _)⁻¹,
    Rat.mul_inv_cancel _ (zpow2_ne_zero _), Rat.one_mul, ← Rat.div_def]

/-- Headline Theorem 6 (`csd_two_tap_half_life_gap_reduction`). -/
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
  refine ⟨fun r _ => oneTap_adjacent_ratio r, fun r _ => ?_, ?_⟩
  · refine ⟨twoTap_adjacent_ratio_same_r r, twoTap_adjacent_ratio_cross_r r, ?_, ?_⟩
    · rw [twoTap_adjacent_ratio_cross_r r]
      grind
    · grind
  · refine ⟨?_, ?_, ?_⟩
    · rw [oneTap_decay_rate, zpow2_neg_ofNat, Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul, Rat.inv_inv]
    · unfold aMax
      have hsub : 1 - (1 - zpow2 (-((7 + 1 : Nat) : Int))) = zpow2 (-((8 : Nat) : Int)) := by grind
      rw [hsub, zpow2_neg_ofNat, Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul, Rat.inv_inv]
    · grind

end SsmDecayCollapse
