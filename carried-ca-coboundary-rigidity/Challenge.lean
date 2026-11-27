/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarriedCaCoboundaryRigidity.Defs

/-!
# Trusted Challenge Statements (\carried-ca-coboundary-rigidity\)

Infinite conservation-law rigidity (no-go) theorem for strongly connected causal bijective bit transducers, and exact
all-width / all-iterate conservation laws for carried Wolfram Rule 30, the Fredkin router family, the bounded-walk
involution family and the carried period-4 hybrid automaton.
-/

namespace CarriedCaCoboundaryRigidityChallenge

open SiliconTransducerCA

/-- Theorem 1 (One-sided conservation-bijectivity rigidity): a strongly connected causal bijective transducer (any state type) with a nowhere-zero weight sequence and a one-sided bounded weighted defect is the identity on every finite bit word. -/
theorem causal_bij_weight_rigidity {Q : Type} (w : Nat → Int) (T : Mealy Q)
    (hbij : ∀ q : Q, T.out q false ≠ T.out q true)
    (hconn : StronglyConnected T)
    (hw : ∀ i : Nat, w i ≠ 0)
    (hbound : ∃ M : Int, ∀ xs : List Bool, weightedDefect w T xs ≤ M) :
    ∀ xs : List Bool, T.run xs = xs := by
  sorry

/-- Theorem 2 (Two-sided unbounded defect): a non-identity strongly connected causal bijective transducer has weighted defect unbounded above and unbounded below, for every nowhere-zero weight sequence. -/
theorem causal_bij_unbounded_both_sides {Q : Type} (w : Nat → Int) (T : Mealy Q)
    (hbij : ∀ q : Q, T.out q false ≠ T.out q true)
    (hconn : StronglyConnected T)
    (hw : ∀ i : Nat, w i ≠ 0)
    (hnotId : ∃ xs : List Bool, T.run xs ≠ xs) :
    (∀ M : Int, ∃ xs : List Bool, weightedDefect w T xs > M) ∧
    (∀ M : Int, ∃ xs : List Bool, weightedDefect w T xs < -M) := by
  sorry

/-- Theorem 3 (Carried Rule 30 alternating-weight coboundary): one pass of T30 changes the alternating sum of any bit word by at most 1. -/
theorem carriedRule30_alt_bound (xs : List Bool) :
    -1 ≤ altSum (T30.run xs) - altSum xs ∧ altSum (T30.run xs) - altSum xs ≤ 1 := by
  sorry

/-- Theorem 4 (Carried Rule 30 exact conservation for all iterates): the zero-flushed iterate conserves the alternating sum for every number of steps t and every word. -/
theorem carriedRule30_iter_alt_exact (t : Nat) (xs : List Bool) :
    altSum (iterFn (T30.stepFlushed 2) t xs) = altSum xs := by
  sorry

/-- Theorem 5 (Semigroup law): every finite composition of the carried Rule 30 and Rule 46 flushed passes conserves the alternating sum and the value modulo 3. -/
theorem altSemigroup_exact (ops : List Bool) (xs : List Bool) :
    altSum (runAltSemigroup ops xs) = altSum xs ∧
    bitsToNat (runAltSemigroup ops xs) % 3 = bitsToNat xs % 3 := by
  sorry

/-- Theorem 6 (Fredkin router family): for every delay d and every iterate count t, the zero-flushed carried Fredkin router conserves popcount exactly. -/
theorem fredkinRouter_iter_popcount_exact (d t : Nat) (xs : List Bool) :
    popcount (iterFn ((fredkinRouter d).stepFlushed (d + 2)) t xs) = popcount xs := by
  sorry

/-- Theorem 7 (Bounded-walk involution family): for every capacity K, the bounded-walk transducer is an involution on all finite bit words. -/
theorem walkInv_involutive (K : Nat) (xs : List Bool) :
    (walkInv K).run ((walkInv K).run xs) = xs := by
  sorry

/-- Theorem 8 (Deep nonlinear period 4): the carried hybrid automaton T54_105 satisfies T^4 = id on all finite bit words. -/
theorem rule54_105_period4 (xs : List Bool) :
    iterFn T54_105.run 4 xs = xs := by
  sorry

end CarriedCaCoboundaryRigidityChallenge
