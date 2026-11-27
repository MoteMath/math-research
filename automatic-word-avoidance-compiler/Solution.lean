/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AutomaticWordAvoidanceCompiler

/-!
# Verified Solutions (`automatic-word-avoidance-compiler`)
-/

namespace AutomaticWordAvoidanceCompilerChallenge

open SiliconAvoidance

theorem windowCert_sound (M : DFAO) (W : Nat) (ok : List Nat → Bool) (cert : WindowCert)
    (h : checkWindowCert M W ok cert = true) :
    ∀ n : Nat, ok (outputWindow M W n) = true :=
  SiliconAvoidance.windowCert_sound M W ok cert h

theorem powerAvoidCert_sound (M : DFAO) (k : Nat) (cert : PowerAvoidCert)
    (h : checkPowerAvoidCert M k cert = true) :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < (k - 1) * p ∧ M.evalWord (n + j) ≠ M.evalWord (n + p + j) :=
  SiliconAvoidance.powerAvoidCert_sound M k cert h

theorem overlapAvoidCert_sound (M : DFAO) (cert : OverlapAvoidCert)
    (h : checkOverlapAvoidCert M cert = true) :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j ≤ p ∧ M.evalWord (n + j) ≠ M.evalWord (n + p + j) :=
  SiliconAvoidance.overlapAvoidCert_sound M cert h

-- ============================================================================
-- Section 10: Concrete Novel Infinite Pure-Silicon Theorems (T1..T8)
-- ============================================================================

/-- T1: Carry-XOR Parity `popcount((3*n) ^^^ n) % 2` avoids ALL 4th powers (∀ n, ∀ p ≥ 1). -/
theorem carryXor3_four_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 3 * p ∧ carryXor 3 (n + j) ≠ carryXor 3 (n + p + j) :=
  SiliconAvoidance.carryXor3_four_power_free

theorem carryAnd3_five_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 4 * p ∧ carryAnd 3 (n + j) ≠ carryAnd 3 (n + p + j) :=
  SiliconAvoidance.carryAnd3_five_power_free

theorem carryAnd5_four_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 3 * p ∧ carryAnd 5 (n + j) ≠ carryAnd 5 (n + p + j) :=
  SiliconAvoidance.carryAnd5_four_power_free

theorem carryXor5_six_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 5 * p ∧ carryXor 5 (n + j) ≠ carryXor 5 (n + p + j) :=
  SiliconAvoidance.carryXor5_six_power_free

theorem grayMod4_overlap_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j ≤ p ∧ grayMod4 (n + j) ≠ grayMod4 (n + p + j) :=
  SiliconAvoidance.grayMod4_overlap_free

end AutomaticWordAvoidanceCompilerChallenge
