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

theorem invSet_bubblePass_iff (xs : List Nat) (hnd : xs.Nodup) (a b : Nat) :
    IsInv (bubblePass xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ IsInv xs c b :=
  WeakBruhatCommutators.invSet_bubblePass_iff hnd a b

theorem desBot_bubblePass_iff (xs : List Nat) (hnd : xs.Nodup) (b : Nat) :
    IsDesBot (bubblePass xs) b ↔ IsDesBot xs b ∧ 2 ≤ leftInv xs b :=
  WeakBruhatCommutators.desBot_bubblePass_iff hnd b

theorem bubbleOrder_bubblePass_mono (xs ys : List Nat)
    (hperm : xs.Perm ys) (hnd : xs.Nodup) (hle : BubbleLe xs ys) :
    BubbleLe (bubblePass xs) (bubblePass ys) :=
  WeakBruhatCommutators.bubbleOrder_bubblePass_mono hperm hnd hle

theorem westSort_weakBruhat_bubblePass (xs : List Nat) (hnd : xs.Nodup) :
    WeakBruhatLe (westSort xs) (bubblePass xs) :=
  WeakBruhatCommutators.westSort_weakBruhat_bubblePass hnd

theorem westSort_weakBruhat_popSort (xs : List Nat) (hnd : xs.Nodup) :
    WeakBruhatLe (westSort xs) (popSort xs) :=
  WeakBruhatCommutators.westSort_weakBruhat_popSort hnd

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

theorem exists_westSort_popSort_not_weakBruhat_mono :
    ∃ u v : List Nat,
      u.Perm v ∧ u.Nodup ∧ WeakBruhatLe u v ∧
      ¬ WeakBruhatLe (westSort u) (westSort v) ∧
      ¬ WeakBruhatLe (popSort u) (popSort v) :=
  WeakBruhatCommutators.exists_westSort_popSort_not_weakBruhat_mono

theorem exists_bubble_pop_incomparable :
    ∃ xs : List Nat, xs.Nodup ∧
      ¬ WeakBruhatLe (bubblePass xs) (popSort xs) ∧
      ¬ WeakBruhatLe (popSort xs) (bubblePass xs) :=
  WeakBruhatCommutators.exists_bubble_pop_incomparable

end WeakBruhatCommutatorsChallenge
