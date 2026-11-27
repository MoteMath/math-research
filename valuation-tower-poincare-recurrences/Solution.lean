/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ValuationTowerPoincareRecurrences

/-!
# Verified Solutions (`valuation-tower-poincare-recurrences`)
-/

namespace ValuationTowerPoincareRecurrencesChallenge

open VTPR

theorem poincare_return {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 1 ≤ w) {e : State m w} (he : allEven e) :
    iter (stepMap Φ) (2 * (m + 2) - 1) (toEven c e) = toEven c (poincareR Φ c e) :=
  VTPR.poincare_return S hw he

/-! ### Step 3D: Exact `(d + 1)`-Step Nonlinear Cancellation & Primitive Periodicity Theorem -/

/-- **Exact Nonlinear Cancellation Theorem (`ℛ^{d+1} = M` on 4-divisible states):**
    For ANY `ValuationTowerSpec` operator `Φ` and ANY 4-divisible state `z`,
    after `d + 1` Poincaré return steps the arbitrary level-≥2 nonlinearity `Φ(tail z)`
    cancels identically and collapses to the linear monodromy `monodromyM z`! -/
theorem poincareR_linearization {m w : Nat} {Φ c} (S : ValuationTowerSpec m w Φ c)
    (hw : 2 ≤ w) {z : State m w} (hz : allDiv4 z) :
    iter (poincareR Φ c) (m + 3) z = monodromyM z :=
  VTPR.poincareR_linearization S hw hz

theorem vtpr_full_period {m : Nat} {Φ c} (H : ValuationHomogeneousSpec m Φ c) :
    ∀ (w : Nat) (x : State m w),
      iter (stepMap (Φ w)) (QPeriod (m + 2)) x = x :=
  VTPR.vtpr_full_period H

theorem vtpr_universal_exact_minimal_period {m w : Nat} {Φ}
    (S : ValuationTowerSpec m w Φ 1#w) (hw : 4 ≤ w) :
    iter (stepMap Φ) (QPeriod (m + 2)) (universalWitness m w) = universalWitness m w ∧
    ∀ t : Nat, 0 < t → t < QPeriod (m + 2) →
      iter (stepMap Φ) t (universalWitness m w) ≠ universalWitness m w :=
  VTPR.vtpr_universal_exact_minimal_period S hw

theorem twistedLSB_exact_minimal_period (m w : Nat) (hw : 4 ≤ w) :
    iter (twistedLSBStep 1#w) (QPeriod (m + 2)) (universalWitness m w) = universalWitness m w ∧
    ∀ t : Nat, 0 < t → t < QPeriod (m + 2) →
      iter (twistedLSBStep 1#w) t (universalWitness m w) ≠ universalWitness m w :=
  VTPR.twistedLSB_exact_minimal_period m w hw

theorem wildQuad_exact_minimal_period (m w : Nat) (hw : 4 ≤ w) :
    iter (stepMap (wildQuadPhi 1#w)) (QPeriod (m + 2)) (universalWitness m w) = universalWitness m w ∧
    ∀ t : Nat, 0 < t → t < QPeriod (m + 2) →
      iter (stepMap (wildQuadPhi 1#w)) t (universalWitness m w) ≠ universalWitness m w :=
  VTPR.wildQuad_exact_minimal_period m w hw

end ValuationTowerPoincareRecurrencesChallenge
