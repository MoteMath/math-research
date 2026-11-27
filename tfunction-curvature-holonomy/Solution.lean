/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TfunctionCurvatureHolonomy

/-!
# Verified Solutions (`tfunction-curvature-holonomy`)
-/

namespace TfunctionCurvatureHolonomyChallenge

open SiliconTFunc

theorem singleCycle_succ_iff {f : Nat → Nat} {w : Nat}
    (hf : IsOneLipschitz f) (hsc : IsSingleCycle f w) :
    IsSingleCycle f (w + 1) ↔ HasUnitSliceDeriv f w ∧ holonomy f w = true :=
  SiliconTFunc.singleCycle_succ_iff hf hsc

theorem holonomy_succ_iff_curvatureSum_zero {f : Nat → Nat} {w : Nat}
    (hf : IsOneLipschitz f) (hsc1 : IsSingleCycle f (w + 1)) :
    holonomy f (w + 1) = true ↔ curvatureSum f w % (2 ^ (w + 2) : Int) = 0 :=
  SiliconTFunc.holonomy_succ_iff_curvatureSum_zero hf hsc1

theorem lift_singleCycle_from_w4 {f : Nat → Nat}
    (hf : IsOneLipschitz f)
    (hbase : IsSingleCycle f 4)
    (hderiv : ∀ w, 3 ≤ w → HasUnitSliceDeriv f (w + 1))
    (hcurv : ∀ w, 3 ≤ w → curvatureSum f w % (2 ^ (w + 2) : Int) = 0) :
    ∀ w, 1 ≤ w → IsSingleCycle f w :=
  SiliconTFunc.lift_singleCycle_from_w4 hf hbase hderiv hcurv

theorem singleCycle_xor_carryMask_iff {g : Nat → Nat} (hg : IsOneLipschitz g) (k : Nat) :
    ∀ w, 1 ≤ w →
      (IsSingleCycle (fun x => g x ^^^ (2 * k * carryMask x)) w ↔ IsSingleCycle g w) :=
  SiliconTFunc.singleCycle_xor_carryMask_iff hg k

theorem hybridH_singleCycle_iff_bits (a b C k : Nat) :
    (∀ w, 1 ≤ w → IsSingleCycle (hybridH a b C k) w) ↔
      (C.testBit 0 = true ∧
       (a.testBit 1 = true → C.testBit 1 = true) ∧
       (a.testBit 0 = false → C.testBit 2 = true) ∧
       (b.testBit 0 = true → C.testBit 3 = true)) :=
  SiliconTFunc.hybridH_singleCycle_iff_bits a b C k

theorem runT_singleCycle_iff {d : Nat} (hd : 2 ≤ d) (C : Nat) :
    (∀ w, 1 ≤ w → IsSingleCycle (runT d C) w) ↔ (C.testBit 0 = true ∧ C.testBit d = true) :=
  SiliconTFunc.runT_singleCycle_iff hd C

theorem runT_sharp_threshold {d : Nat} (hd : 2 ≤ d) :
    (∀ w, 1 ≤ w → w ≤ d → IsSingleCycle (runT d 1) w) ∧ ¬ IsSingleCycle (runT d 1) (d + 1) :=
  SiliconTFunc.runT_sharp_threshold hd

theorem no_universal_finite_threshold :
    ∀ W, 1 ≤ W → ∃ f : Nat → Nat, IsOneLipschitz f ∧
      (∀ w, 1 ≤ w → w ≤ W → IsSingleCycle f w) ∧ ¬ IsSingleCycle f (W + 1) :=
  SiliconTFunc.no_universal_finite_threshold 

end TfunctionCurvatureHolonomyChallenge
