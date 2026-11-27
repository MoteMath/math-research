/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CoupledS4TfunctionOrbits

/-!
# Verified Solutions (`coupled-s4-tfunction-orbits`)
-/

namespace CoupledS4TfunctionOrbitsChallenge

open CoupledS4TFunction in
/-- Theorem 1 (Orbit-lifting exact period): lifting a base state of exact period L with fiber monodromy period d yields exact period d * L at width w + 1. -/
theorem orbit_lift_exact_period (T : TFunc2) (w : Nat) (s : State w) (L : Nat)
    (p : Fiber) (d : Nat)
    (hBase : IsExactPeriod (T.eval w) s L)
    (hMon : IsExactPeriod (monodromy T w s L) p d) :
    IsExactPeriod (T.eval (w + 1)) (liftState p s) (d * L) :=
  CoupledS4TFunction.orbit_lift_exact_period T w s L p d hBase hMon

open CoupledS4TFunction in
/-- Theorem 2 (D4 4-cycle criterion): an element of the dihedral fiber group D4 acts as a single 4-cycle on Bool x Bool iff both shear and translation parity bits are true. -/
theorem d4Elem_is_4cycle_iff (e : D4Elem) :
    (∀ p : Fiber, IsExactPeriod e.apply p 4) ↔ e.lam = true ∧ e.beta = true :=
  CoupledS4TFunction.D4Elem.is_4cycle_iff e

open CoupledS4TFunction in
/-- Theorem 3 (D4 parity full-period lift): any D4-fibered coupled T-function with odd global shear and translation parities at every width has full period 4^w on every state. -/
theorem full_period_of_D4_parity (T : TFunc2)
    (lam alpha beta : ∀ w, State w → Bool)
    (hFiber : ∀ w s p, fiber T w s p = (D4Elem.mk (lam w s) (alpha w s) (beta w s)).apply p)
    (hLam : ∀ w, xorList (lam w) (allStates w) = true)
    (hBeta : ∀ w, xorList (beta w) (allStates w) = true) :
    ∀ w (s : State w), IsExactPeriod (T.eval w) s (4 ^ w) :=
  CoupledS4TFunction.full_period_of_D4_parity T lam alpha beta hFiber hLam hBeta

open CoupledS4TFunction in
/-- Theorem 4 (Universal no-shear obstruction): no coupled T-function whose fibers are pure translations can achieve full period 4^w at any width w >= 1. -/
theorem no_shear_never_full_period (T : TFunc2)
    (hNoShear : ∀ w (s : State w), IsPureTranslation (fiber T w s))
    (w : Nat) (hw : 1 ≤ w) (s : State w) :
    ¬ IsExactPeriod (T.eval w) s (4 ^ w) :=
  CoupledS4TFunction.no_shear_never_full_period T hNoShear w hw s

open CoupledS4TFunction in
/-- Theorem 5 (Infinite-dimensional full-period family): for arbitrary causal perturbations P, Q, R, family1 P Q R achieves full period 4^w at every width w. -/
theorem family1_full_period (P : TScalar2) (Q : TFunc1) (R : TScalar2) :
    ∀ w (s : State w), IsExactPeriod ((family1 P Q R).eval w) s (4 ^ w) :=
  CoupledS4TFunction.family1_full_period P Q R

open CoupledS4TFunction in
/-- Theorem 6 (Twisted ternary odometer cycle partition): for any positive shift list, ternPoly partitions all 4^w states into exact cycles of length 3^popcount(x). -/
theorem ternPoly_exact_cycle_partition (shifts : List Nat) (hShifts : ∀ d ∈ shifts, 1 ≤ d)
    (w : Nat) :
    let f := (ternPoly shifts).eval w
    ((allBitVecs w).flatMap (fun x => orbitList f (x, 0#w) (3 ^ popcount x))).Perm (allStates w) ∧
    (∀ x : BitVec w, IsExactPeriod f (x, 0#w) (3 ^ popcount x)) ∧
    (∀ k : Nat, (allBitVecs w).countP (fun x => decide (popcount x = k)) = choose w k) :=
  CoupledS4TFunction.ternPoly_exact_cycle_partition shifts hShifts w

open CoupledS4TFunction in
/-- Theorem 7 (OR-destroying twist partition): the twisted ternary odometer preserves the exact 3^popcount(x) cycle partition at every width. -/
theorem ternTwistY_exact_partition (w : Nat) :
    ((allBitVecs w).flatMap (fun x => orbitList ((ternPoly [1]).eval w) (x, 0#w) (3 ^ popcount x))).Perm
      (allStates w) ∧
    (∀ x : BitVec w, IsExactPeriod ((ternPoly [1]).eval w) (x, 0#w) (3 ^ popcount x)) :=
  CoupledS4TFunction.ternTwistY_exact_partition w

open CoupledS4TFunction in
/-- Theorem 8 (Hybrid two-cycle partition): at every width w = w' + 1, hybridTwoCycle splits all 4^w states into exactly two cycles of lengths 4^w' and 3 * 4^w'. -/
theorem hybridTwoCycle_exact_two_cycles (w' : Nat) :
    let f := hybridTwoCycle.eval (w' + 1)
    IsExactPeriod f (0#(w' + 1), 0#(w' + 1)) (4 ^ w') ∧
    IsExactPeriod f (1#(w' + 1), 0#(w' + 1)) (3 * 4 ^ w') ∧
    (orbitList f (0#(w' + 1), 0#(w' + 1)) (4 ^ w') ++
     orbitList f (1#(w' + 1), 0#(w' + 1)) (3 * 4 ^ w')).Perm (allStates (w' + 1)) :=
  CoupledS4TFunction.hybridTwoCycle_exact_two_cycles w'

end CoupledS4TfunctionOrbitsChallenge
