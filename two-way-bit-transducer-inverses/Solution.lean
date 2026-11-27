/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoWayBitTransducerInverses

/-!
# Verified Solutions (`two-way-bit-transducer-inverses`)
-/

namespace TwoWayBitTransducerInversesChallenge

open BidirectionalTransducer in
/-- Theorem 1 (Tile-witness certificate soundness): any finite tile-witness certificate passing checkCert certifies that the sweep composition is the identity on BitVec w for every width w. -/
theorem checkCert_sound_bv {Q : Type} [DecidableEq Q] (cert : FiniteTileCert Q)
    (hCheck : checkCert cert = true) {w : Nat} (x : BitVec w) :
    sweepsBV cert.sws x = x :=
  BidirectionalTransducer.checkCert_sound_bv cert hCheck x

open BidirectionalTransducer in
/-- Theorem 2 (Universal period-3 law): the bidirectional skip-flip transducer skipFlip2TwoWay has exact period 3 on BitVec w for every width w. -/
theorem skipFlip2_period3_bv {w : Nat} (x : BitVec w) :
    iter skipFlip2TwoWay 3 x = x :=
  BidirectionalTransducer.skipFlip2_period3_bv x

open BidirectionalTransducer in
/-- Theorem 3 (Shifted period-6 law): the shifted bidirectional skip-flip transducer has exact period 6 on BitVec w for every width w. -/
theorem skipFlip2_shifted_period6_bv {w : Nat} (x : BitVec w) :
    iter skipFlip2Shifted 6 x = x :=
  BidirectionalTransducer.skipFlip2_shifted_period6_bv x

open BidirectionalTransducer in
/-- Theorem 4 (Exponential forward period): the unidirectional forward sweep of skipFlip2 has period 2^w on BitVec w, contrasting the bidirectional period 3. -/
theorem skipFlip2_fwd_period_pow2 {w : Nat} (x : BitVec w) :
    iter (fwdBV (skipFlip2 false)) (2 ^ w) x = x :=
  BidirectionalTransducer.skipFlip2_fwd_period_pow2 x

open BidirectionalTransducer in
/-- Theorem 5 (Parametric two-way inversion): for every threshold m and width w, runTriggerTwoWay m has an explicit two-way left inverse. -/
theorem runTriggerTwoWay_left_inv (m : Nat) {w : Nat} (x : BitVec w) :
    fwdBV (runTriggerS m) (bwdBV (runTriggerR m) (runTriggerTwoWay m x)) = x :=
  BidirectionalTransducer.runTriggerTwoWay_left_inv m x

open BidirectionalTransducer in
/-- Theorem 6 (Coxeter-6 phase transition): for every threshold m >= 2 and every width w, runTriggerTwoWay m has universal period 6 on BitVec w. -/
theorem runTrigger_period6_all_m_bv (m : Nat) (hm : 2 ≤ m) {w : Nat} (x : BitVec w) :
    iter (runTriggerTwoWay m) 6 x = x :=
  BidirectionalTransducer.runTrigger_period6_all_m_bv m hm x

open BidirectionalTransducer in
/-- Theorem 7 (Parametric run-skip-flip period 6): for every m >= 2 and every width w, the symmetric two-way runSkipFlip m transducer has period 6 on BitVec w. -/
theorem runSkipFlip_period6_all_m_bv (m : Nat) (hm : 2 ≤ m) {w : Nat} (x : BitVec w) :
    iter (twoWayBV (runSkipFlip m) (runSkipFlip m)) 6 x = x :=
  BidirectionalTransducer.runSkipFlip_period6_all_m_bv m hm x

open BidirectionalTransducer in
/-- Theorem 8 (Coupled parity-delay exact inverse): the coupled parity-delay forward transducer is exactly inverted on all bit lists by the Gray-difference backward transducer. -/
theorem coupled_parityDelay_exact_inv (xs : List Bool) :
    runCoupledTwoWay parityDelayF id grayDiffB xs = xs :=
  BidirectionalTransducer.coupled_parityDelay_exact_inv xs

end TwoWayBitTransducerInversesChallenge
