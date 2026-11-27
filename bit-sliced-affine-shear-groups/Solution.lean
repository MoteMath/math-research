/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSlicedAffineShearGroups

/-!
# Verified Solutions (`bit-sliced-affine-shear-groups`)
-/

namespace BitSlicedAffineShearGroupsChallenge

open BSASCE

theorem bsasce_master_order_bound {w r D : Nat} {M : Nat → GL2} {f : State w → State w}
    (hf : IsBitAffine r M f) (hrw : r ≤ w)
    (hbase : ∀ x, LowEq r (iter f D x) x)
    (hjac : ∀ k, r ≤ k → k < w → (M k).pow D = GL2.I) :
    ∀ x, iter f (D * 2 ^ (w - r)) x = x :=
  BSASCE.bsasce_master_order_bound hf hrw hbase hjac

theorem bsasce_derived_series_collapse {w : Nat} (hw : 1 ≤ w) (f : RevCircuit w)
    (hf : InDerivedSeries w (w + 1) f) :
    ∀ x, f.toFun x = x :=
  BSASCE.bsasce_derived_series_collapse hw f hf

theorem theorem1_circuitE_exact_order (w : Nat) (hw : 2 ≤ w) :
    HasExactOrder (circuitE w) (3 * 2 ^ w) :=
  BSASCE.theorem1_circuitE_exact_order w hw

theorem theorem2_circuitP_exact_order (w : Nat) (hw : 2 ≤ w) :
    HasExactOrder (circuitP w) (3 * 2 ^ (w - 1)) :=
  BSASCE.theorem2_circuitP_exact_order w hw

theorem theorem2_circuitFm_pairwise_non_conjugate (w : Nat) (m1 m2 : BitVec w) (hne : m1 ≠ m2)
    (h : RevCircuit w) (Mh : Nat → GL2) (hh : IsBitAffine 0 Mh h.toFun) :
    ¬ (∀ x, (circuitFm w m2).toFun x = (h.conj (circuitFm w m1)).toFun x) :=
  BSASCE.theorem2_circuitFm_pairwise_non_conjugate w m1 m2 hne h Mh hh

theorem theorem3_addXorShear_exact_order (w : Nat) (hw : 2 ≤ w) :
    HasExactOrder ((addShearR w 0).comp (xorShearR w 0)) (2 ^ (w - 1)) :=
  BSASCE.theorem3_addXorShear_exact_order w hw

theorem theorem3_fiber1_wreath_normal_form {w : Nat} (hw : 2 ≤ w) :
    (∀ f, InFiber1Group w f → ∃ ε u v, ∀ b, f b = wreathElem ε u v b) ∧
    (∀ ε u v, InFiber1Group w (wreathElem ε u v)) ∧
    (∀ (ε1 : Bool) (u1 v1 : BitVec (w - 1)) (ε2 : Bool) (u2 v2 : BitVec (w - 1)),
      (∀ b : BitVec w, wreathElem ε1 u1 v1 b = wreathElem ε2 u2 v2 b) →
      ε1 = ε2 ∧ u1 = u2 ∧ v1 = v2) :=
  BSASCE.theorem3_fiber1_wreath_normal_form hw

theorem theorem4_circuitH_prime5_obstruction (w : Nat) (hw : 2 ≤ w) :
    iter (circuitH w hw).toFun (3 * 2 ^ w) (0#w, 1#w) ≠ (0#w, 1#w) :=
  BSASCE.theorem4_circuitH_prime5_obstruction w hw

end BitSlicedAffineShearGroupsChallenge
