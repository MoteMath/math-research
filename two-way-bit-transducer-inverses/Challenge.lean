/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoWayBitTransducerInverses.Defs

/-!
# Trusted Challenge Statements (`two-way-bit-transducer-inverses`)

Statements of the pure-data finite tile-witness crossing-sequence certificate soundness on BitVec w, exact period-3 and period-6 laws for bidirectional skip-flip and run-trigger transducers across all widths and thresholds m >= 2, exponential 2^w forward period contrasting bidirectional period 3, and coupled parity-delay exact inversion.
-/

namespace TwoWayBitTransducerInversesChallenge

open BidirectionalTransducer in
/-- Theorem 1 (Tile-witness certificate soundness): any finite tile-witness certificate passing checkCert certifies that the sweep composition is the identity on BitVec w for every width w. -/
theorem checkCert_sound_bv {Q : Type} [DecidableEq Q] (cert : FiniteTileCert Q)
    (hCheck : checkCert cert = true) {w : Nat} (x : BitVec w) :
    sweepsBV cert.sws x = x := by
  sorry

open BidirectionalTransducer in
/-- Theorem 2 (Universal period-3 law): the bidirectional skip-flip transducer skipFlip2TwoWay satisfies iter T 3 x = x on BitVec w for every width w (period divides 3; least period is not stated). -/
theorem skipFlip2_period3_bv {w : Nat} (x : BitVec w) :
    iter skipFlip2TwoWay 3 x = x := by
  sorry

open BidirectionalTransducer in
/-- Theorem 3 (Shifted period-6 law): the shifted bidirectional skip-flip transducer satisfies iter T 6 x = x on BitVec w for every width w (least period is not stated). -/
theorem skipFlip2_shifted_period6_bv {w : Nat} (x : BitVec w) :
    iter skipFlip2Shifted 6 x = x := by
  sorry

open BidirectionalTransducer in
/-- Theorem 4 (Exponential forward period): the unidirectional forward sweep of skipFlip2 satisfies iter T (2^w) x = x on BitVec w (a divisibility statement; least period is not stated here). -/
theorem skipFlip2_fwd_period_pow2 {w : Nat} (x : BitVec w) :
    iter (fwdBV (skipFlip2 false)) (2 ^ w) x = x := by
  sorry

open BidirectionalTransducer in
/-- Theorem 5 (Parametric two-way inversion): for every threshold m and width w, runTriggerTwoWay m has an explicit two-way left inverse. -/
theorem runTriggerTwoWay_left_inv (m : Nat) {w : Nat} (x : BitVec w) :
    fwdBV (runTriggerS m) (bwdBV (runTriggerR m) (runTriggerTwoWay m x)) = x := by
  sorry

open BidirectionalTransducer in
/-- Theorem 6 (Coxeter-6 phase transition): for every threshold m >= 2 and every width w, runTriggerTwoWay m satisfies iter T 6 x = x on BitVec w (least period is not stated). -/
theorem runTrigger_period6_all_m_bv (m : Nat) (hm : 2 ≤ m) {w : Nat} (x : BitVec w) :
    iter (runTriggerTwoWay m) 6 x = x := by
  sorry

open BidirectionalTransducer in
/-- Theorem 7 (Parametric run-skip-flip period 6): for every m >= 2 and every width w, the symmetric two-way runSkipFlip m transducer satisfies iter T 6 x = x on BitVec w. -/
theorem runSkipFlip_period6_all_m_bv (m : Nat) (hm : 2 ≤ m) {w : Nat} (x : BitVec w) :
    iter (twoWayBV (runSkipFlip m) (runSkipFlip m)) 6 x = x := by
  sorry

open BidirectionalTransducer in
/-- Theorem 8 (Coupled parity-delay exact inverse): the coupled parity-delay forward transducer is exactly inverted on all bit lists by the Gray-difference backward transducer. -/
theorem coupled_parityDelay_exact_inv (xs : List Bool) :
    runCoupledTwoWay parityDelayF id grayDiffB xs = xs := by
  sorry

end TwoWayBitTransducerInversesChallenge
