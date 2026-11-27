/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NlfsrHolonomyLassoDebruijn

/-!
# Verified Solutions (`nlfsr-holonomy-lasso-debruijn`)
-/

namespace NlfsrHolonomyLassoDebruijnChallenge

open DynSil12

theorem transducer_cert_period_doubling {S : Nat} {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta)
    (T : CarryTransducer S) (hV : T.Valid)
    (P : Nat → Bool) (w0 L0 x : Nat)
    (htrack : ∀ d y, y < 2 ^ (w0 + d) → P (y % 2 ^ w0) = true →
              delta (w0 + d) y = T.toggle (runTransducer T (w0 + d) y))
    (hP_inv : ∀ y, P (y % 2 ^ w0) = true → P (f y % 2 ^ w0) = true)
    (hP_cnt : ((List.range (2 ^ w0)).filter (fun y => P (y % 2 ^ w0))).length = L0)
    (hx_in : P (x % 2 ^ w0) = true)
    (hbase : ExactPeriod f w0 x L0)
    (cert : LassoCert)
    (hcert : checkLasso T (cylinderVec T P w0 w0) cert = true) :
    ∀ d, ExactPeriod f (w0 + d) x (L0 * 2 ^ d) :=
  DynSil12.transducer_cert_period_doubling hf T hV P w0 L0 x htrack hP_inv hP_cnt hx_in hbase cert hcert

theorem theorem1_H111_exact_two_cycles (w : Nat) (hw : w ≥ 3) :
    (∀ x, x.testBit 2 = false → ExactPeriod H111 w x (2 ^ (w - 1))) ∧
    (∀ x, x.testBit 2 = true  → ExactPeriod H111 w x (2 ^ (w - 1))) ∧
    (∀ x y t, x.testBit 2 = false → y.testBit 2 = true → iter H111 t x % 2 ^ w ≠ y % 2 ^ w) :=
  DynSil12.theorem1_H111_exact_two_cycles w hw

theorem theorem1b_H121_debruijn (w : Nat) (hw : w ≥ 1) : SingleCycle H121 w :=
  DynSil12.theorem1b_H121_debruijn w hw

theorem theorem2a_carry_pump_universal_giant_cycle {N : Nat → Nat} (hN : TwoDelayed N)
    (hgate : (N 0).testBit 2 = (N 1).testBit 2)
    {c : Nat} (hc : c % 4 = 1) :
    ∀ w ≥ 2, ∀ x, x.testBit 1 = false → ExactPeriod (hybridCarryNLFSR N c) w x (2 ^ (w - 1)) :=
  DynSil12.theorem2a_carry_pump_universal_giant_cycle hN hgate hc

theorem theorem2b_carry_barrier_hermetic {N : Nat → Nat} (hN : TwoDelayed N) (x : Nat)
    (hx : x.testBit 1 = true) :
    (hybridCarryNLFSR N 1 x).testBit 1 = true ∧
    hybridCarryNLFSR N 1 x / 4 = (x ^^^ (x <<< 1) ^^^ N x) / 4 :=
  DynSil12.theorem2b_carry_barrier_hermetic hN x hx

theorem theorem2c_linear_carry_barrier_exact_log_period (w k : Nat) (hw : w ≥ 3) (hk : k ≥ 1)
    (hhi : w - 1 ≤ 2 ^ k) (hlo : 2 ^ (k - 1) < w - 1)
    (x : Nat) (hx : x.testBit 1 = true) :
    ExactPeriod F0 w x (2 ^ k) :=
  DynSil12.theorem2c_linear_carry_barrier_exact_log_period w k hw hk hhi hlo x hx

theorem theorem3a_nonprefix_hybrid_nlfsr_debruijn {M : List (List Nat)} (hM : ∀ T ∈ M, NonPrefixTap T)
    {c : Nat} (hc : c % 2 = 1) (w : Nat) (hw : w ≥ 1) :
    SingleCycle (hybridTapNLFSR M c) w :=
  DynSil12.theorem3a_nonprefix_hybrid_nlfsr_debruijn hM hc w hw

theorem theorem3b_prefix_tap_exact_cycle_splitting (d : Nat) (hd : d ≥ 1) {c : Nat} (hc : c % 2 = 1) :
    (∀ w, 1 ≤ w → w ≤ d → SingleCycle (hybridTapNLFSR [prefixTap d] c) w) ∧
    (ExactPeriod (hybridTapNLFSR [prefixTap d] c) (d + 1) 0 (2 ^ d) ∧
     ExactPeriod (hybridTapNLFSR [prefixTap d] c) (d + 1) (2 ^ d) (2 ^ d) ∧
     ∀ t, iter (hybridTapNLFSR [prefixTap d] c) t 0 % 2 ^ (d + 1) ≠ 2 ^ d % 2 ^ (d + 1)) :=
  DynSil12.theorem3b_prefix_tap_exact_cycle_splitting d hd hc

end NlfsrHolonomyLassoDebruijnChallenge
