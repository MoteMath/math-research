/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakBruhatCommutators

/-!
# Verified Solutions (`weak-bruhat-commutators`)

Provides sorry-free proofs for every theorem in `Challenge.lean`.
-/

namespace WeakBruhatCommutatorsChallenge

open WeakBruhatCommutators

theorem desBot_bubblePass_iff (xs : List Nat) (hnd : xs.Nodup) (b : Nat) :
    IsDesBot (bubblePass xs) b ↔ IsDesBot xs b ∧ 2 ≤ leftInv xs b :=
  WeakBruhatCommutators.desBot_bubblePass_iff hnd b

theorem bubbleOrder_bubblePass_mono (xs ys : List Nat)
    (hperm : xs.Perm ys) (hnd : xs.Nodup) (hle : BubbleLe xs ys) :
    BubbleLe (bubblePass xs) (bubblePass ys) :=
  WeakBruhatCommutators.bubbleOrder_bubblePass_mono hperm hnd hle

theorem iterBubble_west_commutator (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    BubbleLe (iterBubble k (westSort xs)) (westSort (iterBubble k xs)) :=
  WeakBruhatCommutators.iterBubble_west_commutator k hnd

theorem iterBubble_pop_commutator (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    BubbleLe (iterBubble k (popSort xs)) (popSort (iterBubble k xs)) :=
  WeakBruhatCommutators.iterBubble_pop_commutator k hnd

theorem invCnt_iterBubble_west_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (iterBubble k (westSort xs)) ≤ invCnt (westSort (iterBubble k xs)) :=
  WeakBruhatCommutators.invCnt_iterBubble_west_le k hnd

theorem desCnt_iterBubble_west_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    desCnt (iterBubble k (westSort xs)) ≤ desCnt (westSort (iterBubble k xs)) :=
  WeakBruhatCommutators.desCnt_iterBubble_west_le k hnd

theorem invCnt_iterBubble_pop_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (iterBubble k (popSort xs)) ≤ invCnt (popSort (iterBubble k xs)) :=
  WeakBruhatCommutators.invCnt_iterBubble_pop_le k hnd

theorem desCnt_iterBubble_pop_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    desCnt (iterBubble k (popSort xs)) ≤ desCnt (popSort (iterBubble k xs)) :=
  WeakBruhatCommutators.desCnt_iterBubble_pop_le k hnd

end WeakBruhatCommutatorsChallenge
