/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HenselSiliconBasinClassifier

/-!
# Verified Solutions (`hensel-silicon-basin-classifier`)
-/

namespace HenselSiliconBasinClassifierChallenge

open HenselSilicon in
/-- Theorem 1 (3-valued bit-derivative soundness): the static abstract bit-derivative of any BPoly (mixing +, *, clmul, &, |, ^, ~) soundly tracks bit-k sensitivity across all widths. -/
theorem bPoly_absDeriv_sound (m : Nat) (hm : 1 ≤ m) (e : BPoly)
    {w k : Nat} (hmk : m ≤ k) (hkw : k < w)
    (x y : BitVec w) (hxy : BitVec.setWidth k x = BitVec.setWidth k y) :
    (e.absDeriv m (x.getLsbD 0)).Satisfies
      (x.getLsbD k ^^ y.getLsbD k)
      ((e.eval x).getLsbD k ^^ (e.eval y).getLsbD k) :=
  HenselSilicon.BPoly.absDeriv_sound m hm e hmk hkw x y hxy

open HenselSilicon in
/-- Theorem 2 (Contraction-free universal fixed-point depth): for ANY T-function on BitVec w, every state that ever reaches a fixed point reaches it in at most w steps. -/
theorem tfunc_fixedPoint_depth_le_width {F : ∀ w, BitVec w → BitVec w} (hF : IsTFunc F)
    {w : Nat} (x xStar : BitVec w)
    (hfix : F w xStar = xStar) (hreach : ∃ t, iter (F w) t x = xStar) :
    iter (F w) w x = xStar :=
  HenselSilicon.tfunc_fixedPoint_depth_le_width hF x xStar hfix hreach

open HenselSilicon in
/-- Theorem 3 (Hensel periodic orbit lift): any locally contracting L-cycle at base width m lifts to an exact L-cycle at every width w >= m. -/
theorem henselLift_periodic {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hc : 1 ≤ cycleContractionCount F m P r L)
    {w : Nat} (hmw : m ≤ w) :
    iter (F w) L (henselLift F m L (cycleContractionCount F m P r L) w r) =
      henselLift F m L (cycleContractionCount F m P r L) w r :=
  HenselSilicon.henselLift_periodic hF hC r hper hc hmw

open HenselSilicon in
/-- Theorem 4 (Hensel basin convergence): every w-bit state whose m-bit truncation reaches a contracting L-cycle converges to its Hensel lift in explicit logarithmic rounds. -/
theorem henselLift_basin_convergence {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m L : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (r : BitVec m) (hper : iter (F m) L r = r)
    (hc : 1 ≤ cycleContractionCount F m P r L)
    {w : Nat} (hmw : m ≤ w) (x : BitVec w) (d : Nat)
    (hreach : iter (F m) d (BitVec.setWidth m x) = r) :
    iter (F w) (d + henselRounds w m (cycleContractionCount F m P r L) * L) x =
      henselLift F m L (cycleContractionCount F m P r L) w r :=
  HenselSilicon.henselLift_basin_convergence hF hC r hper hc hmw x d hreach

open HenselSilicon in
/-- Theorem 5 (Fixed-point count invariance): when every base fixed point is locally contracting, the total fixed-point count is constant across all widths w >= m. -/
theorem fixedPointCount_lift {F : ∀ w, BitVec w → BitVec w}
    (hF : IsTFunc F) {m : Nat} {P : BitVec m → Bool} (hC : IsContractingOn F m P)
    (hchk : checkPeriodicContracting F m 1 P = true)
    {w : Nat} (hmw : m ≤ w) :
    bvCount w (isFixedPointB F w) = bvCount m (isFixedPointB F m) :=
  HenselSilicon.fixedPointCount_lift hF hC hchk hmw

open HenselSilicon in
/-- Theorem 6 (Asymmetric non-power-of-two basin): mapAsym has exact attracting basin size 3 * 2^(w - 3) for every width w >= 3. -/
theorem mapAsym_basin_4_nonPowerOfTwo (w : Nat) (hw : 3 ≤ w) :
    bvCount w (inFixedBasinAt (fun _ => mapAsym.eval) w (1 + (w - 3))
      (henselLift (fun _ => mapAsym.eval) 3 1 1 w 4#3)) = 3 * 2 ^ (w - 3) :=
  HenselSilicon.mapAsym_basin_4_nonPowerOfTwo w hw

open HenselSilicon in
/-- Theorem 7 (Seven fixed points): the bitwise-quadratic map mapSeven has exactly 7 fixed points at every width w >= 3. -/
theorem mapSeven_fixedPointCount (w : Nat) (hw : 3 ≤ w) :
    bvCount w (isFixedPointB (fun _ => mapSeven.eval) w) = 7 :=
  HenselSilicon.mapSeven_fixedPointCount w hw

open HenselSilicon in
/-- Theorem 8 (Exact 2w - 2 cycle transient depth): mapHalfCycle achieves exact transient depth 2w - 2 at every width w >= 2, strictly separating cycle depth from fixed-point depth w. -/
theorem mapHalfCycle_depth_exact_sharp (w : Nat) (hw : 2 ≤ w) :
    iter mapHalfCycle.eval 2 (iter mapHalfCycle.eval (2 * w - 3) 3#w) ≠
      iter mapHalfCycle.eval (2 * w - 3) 3#w ∧
    iter mapHalfCycle.eval 2 (iter mapHalfCycle.eval (2 * w - 2) 3#w) =
      iter mapHalfCycle.eval (2 * w - 2) 3#w :=
  HenselSilicon.mapHalfCycle_depth_exact_sharp w hw

end HenselSiliconBasinClassifierChallenge
