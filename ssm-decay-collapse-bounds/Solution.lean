/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse

/-!
# Verified Solutions (`ssm-decay-collapse-bounds`)
-/

namespace SsmDecayCollapseChallenge

open SsmDecayCollapse

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
    (aMax 23 = 16777215 / 16777216 ∧ aStall 23 = 33554431 / 33554432) :=
  SsmDecayCollapse.ieee_decay_stall_midpoint_exact

theorem one_ulp_per_step_sequential_collapse :
    (∀ (p : Nat) (k : Int) (m : Nat), 0 < m → m < 2 ^ p →
      ieeeRne p (floatVal p k m * aMax p) = floatVal p k (m - 1)) ∧
    (∀ (p : Nat) (k : Int),
      ieeeRne p (floatVal p k 0 * aMax p) = floatVal p (k - 1) (2 ^ p - 1)) ∧
    (∀ (p m : Nat), 1 ≤ p → seqPow p (m * 2 ^ p) = zpow2 (-(m : Int))) ∧
    (∀ p : Nat, 1 ≤ p → seqPow p (2 ^ p) = 1 / 2) ∧
    (seqPow 7 128 = 1 / 2 ∧ seqPow 7 4096 = zpow2 (-32)) :=
  SsmDecayCollapse.one_ulp_per_step_sequential_collapse

theorem additive_swamping_exact_divergence :
    (∀ (p : Nat), 1 ≤ p → ∀ (T : Nat),
      seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T = 1 ∧
      ratAbs (exactAccum (zpow2 (-((p + 1 : Nat) : Int))) T -
        seqAccum p (zpow2 (-((p + 1 : Nat) : Int))) T) =
        (T : Rat) * zpow2 (-((p + 1 : Nat) : Int))) ∧
    (exactAccum (zpow2 (-8)) 1024 = 5 ∧ seqAccum 7 (zpow2 (-8)) 1024 = 1 ∧
      ratAbs (exactAccum (zpow2 (-8)) 1024 - seqAccum 7 (zpow2 (-8)) 1024) = 4) ∧
    (exactAccum (zpow2 (-8)) 131072 = 513 ∧ seqAccum 7 (zpow2 (-8)) 131072 = 1 ∧
      ratAbs (exactAccum (zpow2 (-8)) 131072 - seqAccum 7 (zpow2 (-8)) 131072) = 512) :=
  SsmDecayCollapse.additive_swamping_exact_divergence

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
      shiftSubMax R Bmax + shiftSubMin R Bmax = ((2 ^ R : Nat) : Int) - 1) :=
  SsmDecayCollapse.dyadic_shift_subtract_tight_bounds

theorem dyadic_shift_subtract_zero_input_stall_asymmetry :
    (∀ (r : Nat) (h : Int), 0 ≤ h → h < ((2 ^ r : Nat) : Int) →
      shiftSubStep r h 0 = h ∧ ∀ n : Nat, shiftSubIter r h n = h) ∧
    (∀ (r : Nat) (h : Int), 1 ≤ r → h < 0 →
      h < shiftSubStep r h 0 ∧
      shiftSubStep r h 0 ≤ 0 ∧
      ∃ n : Nat, shiftSubIter r h n = 0) :=
  SsmDecayCollapse.dyadic_shift_subtract_zero_input_stall_asymmetry

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
      ((2 ^ 24 : Nat) : Rat) / ((2 ^ 8 : Nat) : Rat) = 65536) :=
  SsmDecayCollapse.csd_two_tap_half_life_gap_reduction

end SsmDecayCollapseChallenge
