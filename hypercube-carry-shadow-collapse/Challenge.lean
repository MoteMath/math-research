/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HypercubeCarryShadowCollapse.Defs

/-!
# Trusted Challenge Statements (`hypercube-carry-shadow-collapse`)
-/

namespace HypercubeCarryShadowCollapseChallenge

open HypercubeCarryShadowCollapse

/-- Headline theorem `checkGuardedBisimWitness_sound`. -/
theorem checkGuardedBisimWitness_sound {k : Nat}
    (G T1 T2 : Transducer k) (R : Nat)
    (hcheck : checkGuardedBisimWitness G T1 T2 R = true) :
    ∀ env : Fin k → Nat, G.eval env = 0 → T1.eval env = T2.eval env := by
  sorry

/-- Headline theorem `phi_carry_chain_collapse`. -/
theorem phi_carry_chain_collapse (x y : Nat) :
    carryMask (x + y) (x ^^^ y) = 2 * ((x + y) &&& (x ^^^ y)) := by
  sorry

/-- Headline theorem `carryMask_eigen_sandwich_iff`. -/
theorem carryMask_eigen_sandwich_iff (A v : Nat) :
    carryMask A v = 2 * v ↔
      bdiff (A &&& (2 * v)) v = 0 ∧ bdiff v (A ||| (2 * v)) = 0 := by
  sorry

/-- Headline theorem `carryMask_dominated_absorption`. -/
theorem carryMask_dominated_absorption {a b c d : Nat}
    (hba : bsub b a) (hca : bsub c a) (hdb : bsub d b) (hdc : bsub d c) :
    carryMask (carryMask a b) (carryMask c d) = 2 * carryMask a d := by
  sorry

/-- Headline theorem `baseB_carry_defect`. -/
theorem baseB_carry_defect (B : Int) (x y : Nat) :
    evalBase B x + evalBase B y - evalBase B (x + y) =
      (2 - B) * evalBase B (carryMask x y / 2) := by
  sorry

/-- Headline theorem `Q_closed_form_on_dom`. -/
theorem Q_closed_form_on_dom (m : Nat) (y : Cube m) (hy : DomCube m y) :
    Q m y (zeroVertex m) = 2 ^ m * y (zeroVertex m) ∧
    ∀ I : Fin m → Bool, I ≠ zeroVertex m →
      Q m y I = 2 ^ (m - 1) * carryMask (y (zeroVertex m)) (y I) := by
  sorry

/-- Headline theorem `Q_collapse_universal`. -/
theorem Q_collapse_universal (m : Nat) (hm : 1 ≤ m) (x : Cube m) (k : Nat) (hk : 2 ≤ k) :
    iter (k + 1) (Q m) x = scaleCube (2 ^ m) (iter k (Q m) x) := by
  sorry

/-- Headline theorem `Q_bitvec_nilpotent`. -/
theorem Q_bitvec_nilpotent (m w k : Nat) (hm : 1 ≤ m) (hmk : w ≤ m * k) (x : CubeBV m w) :
    iter (k + 2) (QBV m w) x = fun _ => BitVec.ofNat w 0 := by
  sorry

end HypercubeCarryShadowCollapseChallenge
