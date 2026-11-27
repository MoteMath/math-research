/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarriedCaCoboundaryRigidity

/-!
# Verified Solutions (\carried-ca-coboundary-rigidity\)
-/

namespace CarriedCaCoboundaryRigidityChallenge

open SiliconTransducerCA

theorem causal_bij_weight_rigidity {Q : Type} (w : Nat → Int) (T : Mealy Q)
    (hbij : ∀ q : Q, T.out q false ≠ T.out q true)
    (hconn : StronglyConnected T)
    (hw : ∀ i : Nat, w i ≠ 0)
    (hbound : ∃ M : Int, ∀ xs : List Bool, weightedDefect w T xs ≤ M) :
    ∀ xs : List Bool, T.run xs = xs :=
  SiliconTransducerCA.causal_bij_weight_rigidity w T hbij hconn hw hbound

theorem causal_bij_unbounded_both_sides {Q : Type} (w : Nat → Int) (T : Mealy Q)
    (hbij : ∀ q : Q, T.out q false ≠ T.out q true)
    (hconn : StronglyConnected T)
    (hw : ∀ i : Nat, w i ≠ 0)
    (hnotId : ∃ xs : List Bool, T.run xs ≠ xs) :
    (∀ M : Int, ∃ xs : List Bool, weightedDefect w T xs > M) ∧
    (∀ M : Int, ∃ xs : List Bool, weightedDefect w T xs < -M) :=
  SiliconTransducerCA.causal_bij_unbounded_both_sides w T hbij hconn hw hnotId

theorem carriedRule30_alt_bound (xs : List Bool) :
    -1 ≤ altSum (T30.run xs) - altSum xs ∧ altSum (T30.run xs) - altSum xs ≤ 1 :=
  SiliconTransducerCA.carriedRule30_alt_bound ..

theorem carriedRule30_iter_alt_exact (t : Nat) (xs : List Bool) :
    altSum (iterFn (T30.stepFlushed 2) t xs) = altSum xs :=
  SiliconTransducerCA.carriedRule30_iter_alt_exact ..

theorem altSemigroup_exact (ops : List Bool) (xs : List Bool) :
    altSum (runAltSemigroup ops xs) = altSum xs ∧
    bitsToNat (runAltSemigroup ops xs) % 3 = bitsToNat xs % 3 :=
  SiliconTransducerCA.altSemigroup_exact ..

theorem fredkinRouter_iter_popcount_exact (d t : Nat) (xs : List Bool) :
    popcount (iterFn ((fredkinRouter d).stepFlushed (d + 2)) t xs) = popcount xs :=
  SiliconTransducerCA.fredkinRouter_iter_popcount_exact ..

theorem walkInv_involutive (K : Nat) (xs : List Bool) :
    (walkInv K).run ((walkInv K).run xs) = xs :=
  SiliconTransducerCA.walkInv_involutive ..

theorem rule54_105_period4 (xs : List Bool) :
    iterFn T54_105.run 4 xs = xs :=
  SiliconTransducerCA.rule54_105_period4 ..

end CarriedCaCoboundaryRigidityChallenge
