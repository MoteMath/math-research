/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryRunCyclotomicTransfer

/-!
# Verified Solutions (`carry-run-cyclotomic-transfer`)
-/

namespace CarryRunCyclotomicTransferChallenge

open SiliconCarryTransfer

theorem evenRadix_carryRun_outputParity_collapse (m L : Nat) (hm : 1 ≤ m) (hL : 1 ≤ L) (w : Nat) :
    sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
      if maxCarryRunLe (2 * m) L w x y then paritySign (digitSum (2 * m) w ((x + y) % (2 * m) ^ w)) else 0)) =
    if w % (L + 2) = 0 then (m : Int) ^ w
    else if w % (L + 2) = L + 1 then -((m : Int) ^ w)
    else 0 :=
  SiliconCarryTransfer.evenRadix_carryRun_outputParity_collapse m L hm hL w

theorem binary_carryRun_fullPopcount_collapse (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
      if maxCarryRunLe 2 L w x y then paritySign (popcount (w + 1) (x + y)) else 0)) =
    if w % (L + 2) = 0 then 1
    else if w % (L + 2) = 1 then -2
    else if w % (L + 2) = L + 1 then 1
    else 0 :=
  SiliconCarryTransfer.binary_carryRun_fullPopcount_collapse L hL w

theorem evenRadix_rippleDepth_inputParity_collapse (m L : Nat) (hm : 1 ≤ m) (hL : 1 ≤ L) (w : Nat) :
    sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
      if maxRippleDepthLe (2 * m) L w x y then
        paritySign (digitSum (2 * m) w x + digitSum (2 * m) w y)
      else 0)) =
    if w % (L + 1) = 0 then
      (paritySign (L + 1) * (2 : Int) ^ L * (m : Int) ^ (L + 1)) ^ (w / (L + 1))
    else 0 :=
  SiliconCarryTransfer.evenRadix_rippleDepth_inputParity_collapse m L hm hL w

theorem binary_rippleDepth_plain_recurrence (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    let R := fun n => sumNat (2 ^ n) (fun x => sumNat (2 ^ n) (fun y =>
      if maxRippleDepthLe 2 L n x y then (1 : Int) else 0))
    R (w + L + 1) = 4 * R (w + L) - (2 : Int) ^ L * R w :=
  SiliconCarryTransfer.binary_rippleDepth_plain_recurrence L hL w

theorem binary_carryRun_absorption_recurrence (t : Int) (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    carryRunAbsSum t L (w + L + 2) =
      (1 - t) * carryRunAbsSum t L (w + L) + t * carryRunAbsSum t L w :=
  SiliconCarryTransfer.binary_carryRun_absorption_recurrence t L hL w

theorem binary_zeroAbsorption_dichotomy (L : Nat) (hL : 1 ≤ L) (w : Nat) (hw : L ≤ w) :
    carryRunAbsSum 0 L w = if L % 2 = 1 then 0 else paritySign w :=
  SiliconCarryTransfer.binary_zeroAbsorption_dichotomy L hL w hw

theorem rippleOp_annihilator (L : Nat) (hL : 1 ≤ L) (k p g : Int) (v : Nat → Int) :
    ∀ i, i < L + 1 →
      iterOp (rippleOp L k p g) (L + 1) v i -
        (k + p + g) * iterOp (rippleOp L k p g) L v i +
        g * p ^ L * v i = 0 :=
  SiliconCarryTransfer.rippleOp_annihilator L hL k p g v

theorem runOp_annihilator (L : Nat) (hL : 1 ≤ L) (a b c r : Int) (v : Nat → Int) :
    ∀ i, i < L + 1 →
      iterOp (runOp L a b c r) (L + 2) v i -
        (a + r) * iterOp (runOp L a b c r) (L + 1) v i +
        (a * r - b * c) * iterOp (runOp L a b c r) L v i +
        b * c * r ^ L * v i = 0 :=
  SiliconCarryTransfer.runOp_annihilator L hL a b c r v

end CarryRunCyclotomicTransferChallenge
