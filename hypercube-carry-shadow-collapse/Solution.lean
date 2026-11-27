/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HypercubeCarryShadowCollapse

/-!
# Verified Solutions (`hypercube-carry-shadow-collapse`)
-/

namespace HypercubeCarryShadowCollapseChallenge

open HypercubeCarryShadowCollapse

theorem checkGuardedBisimWitness_sound {k : Nat}
    (G T1 T2 : Transducer k) (R : Nat)
    (hcheck : checkGuardedBisimWitness G T1 T2 R = true) :
    ∀ env : Fin k → Nat, G.eval env = 0 → T1.eval env = T2.eval env :=
  HypercubeCarryShadowCollapse.checkGuardedBisimWitness_sound G T1 T2 R hcheck

theorem phi_carry_chain_collapse (x y : Nat) :
    carryMask (x + y) (x ^^^ y) = 2 * ((x + y) &&& (x ^^^ y)) :=
  HypercubeCarryShadowCollapse.phi_carry_chain_collapse x y

theorem carryMask_eigen_sandwich_iff (A v : Nat) :
    carryMask A v = 2 * v ↔
      bdiff (A &&& (2 * v)) v = 0 ∧ bdiff v (A ||| (2 * v)) = 0 :=
  HypercubeCarryShadowCollapse.carryMask_eigen_sandwich_iff A v

theorem carryMask_dominated_absorption {a b c d : Nat}
    (hba : bsub b a) (hca : bsub c a) (hdb : bsub d b) (hdc : bsub d c) :
    carryMask (carryMask a b) (carryMask c d) = 2 * carryMask a d :=
  HypercubeCarryShadowCollapse.carryMask_dominated_absorption hba hca hdb hdc

theorem baseB_carry_defect (B : Int) (x y : Nat) :
    evalBase B x + evalBase B y - evalBase B (x + y) =
      (2 - B) * evalBase B (carryMask x y / 2) :=
  HypercubeCarryShadowCollapse.baseB_carry_defect B x y

theorem Q_closed_form_on_dom (m : Nat) (y : Cube m) (hy : DomCube m y) :
    Q m y (zeroVertex m) = 2 ^ m * y (zeroVertex m) ∧
    ∀ I : Fin m → Bool, I ≠ zeroVertex m →
      Q m y I = 2 ^ (m - 1) * carryMask (y (zeroVertex m)) (y I) :=
  HypercubeCarryShadowCollapse.Q_closed_form_on_dom m y hy

theorem Q_collapse_universal (m : Nat) (hm : 1 ≤ m) (x : Cube m) (k : Nat) (hk : 2 ≤ k) :
    iter (k + 1) (Q m) x = scaleCube (2 ^ m) (iter k (Q m) x) :=
  HypercubeCarryShadowCollapse.Q_collapse_universal m hm x k hk

theorem Q_bitvec_nilpotent (m w k : Nat) (hm : 1 ≤ m) (hmk : w ≤ m * k) (x : CubeBV m w) :
    iter (k + 2) (QBV m w) x = fun _ => BitVec.ofNat w 0 :=
  HypercubeCarryShadowCollapse.Q_bitvec_nilpotent m w k hm hmk x

end HypercubeCarryShadowCollapseChallenge
