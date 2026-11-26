/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakBruhatCommutators.Defs

/-!
# Trusted Challenge Statements (`weak-bruhat-commutators`)

Pure-`Init` (zero Mathlib) statements of the Weak-Bruhat and Descent-Bottom commutator laws
for iterated bubble sort (`B^k`), West's stack-sorting operator (`S`), and pop-stack sorting (`P`)
on duplicate-free lists of natural numbers.
-/

namespace WeakBruhatCommutatorsChallenge

open WeakBruhatCommutators

/-- Exact Left Weak Bruhat characterization of a single bubble-sort pass. -/
theorem invSet_bubblePass_iff (xs : List Nat) (hnd : xs.Nodup) (a b : Nat) :
    IsInv (bubblePass xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ IsInv xs c b := by
  sorry

/-- Exact descent-bottom characterization of a single bubble-sort pass. -/
theorem desBot_bubblePass_iff (xs : List Nat) (hnd : xs.Nodup) (b : Nat) :
    IsDesBot (bubblePass xs) b ↔ IsDesBot xs b ∧ 2 ≤ leftInv xs b := by
  sorry

/-- Single-pass bubble sort is monotone in the Bubble-Refined Order `WeakBruhatLe ∧ DesBotSub`. -/
theorem bubbleOrder_bubblePass_mono (xs ys : List Nat)
    (hperm : xs.Perm ys) (hnd : xs.Nodup) (hle : BubbleLe xs ys) :
    BubbleLe (bubblePass xs) (bubblePass ys) := by
  sorry

/-- West stack-sorting is bounded above by single-pass bubble sort in Left Weak Bruhat Order. -/
theorem westSort_weakBruhat_bubblePass (xs : List Nat) (hnd : xs.Nodup) :
    WeakBruhatLe (westSort xs) (bubblePass xs) := by
  sorry

/-- West stack-sorting is bounded above by pop-stack sorting in Left Weak Bruhat Order. -/
theorem westSort_weakBruhat_popSort (xs : List Nat) (hnd : xs.Nodup) :
    WeakBruhatLe (westSort xs) (popSort xs) := by
  sorry

/-- Iterated Bubble–West commutator in Bubble-Refined Order: `B^k(S(xs)) ⪯_B S(B^k(xs))`. -/
theorem iterBubble_west_commutator (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    BubbleLe (iterBubble k (westSort xs)) (westSort (iterBubble k xs)) := by
  sorry

/-- Iterated Bubble–Pop commutator in Bubble-Refined Order: `B^k(P(xs)) ⪯_B P(B^k(xs))`. -/
theorem iterBubble_pop_commutator (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    BubbleLe (iterBubble k (popSort xs)) (popSort (iterBubble k xs)) := by
  sorry

/-- Inversion-count commutator inequality `invCnt(B^k(S(xs))) ≤ invCnt(S(B^k(xs)))`. -/
theorem invCnt_iterBubble_west_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (iterBubble k (westSort xs)) ≤ invCnt (westSort (iterBubble k xs)) := by
  sorry

/-- Descent-count commutator inequality `desCnt(B^k(S(xs))) ≤ desCnt(S(B^k(xs)))`. -/
theorem desCnt_iterBubble_west_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    desCnt (iterBubble k (westSort xs)) ≤ desCnt (westSort (iterBubble k xs)) := by
  sorry

/-- Inversion-count commutator inequality `invCnt(B^k(P(xs))) ≤ invCnt(P(B^k(xs)))`. -/
theorem invCnt_iterBubble_pop_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (iterBubble k (popSort xs)) ≤ invCnt (popSort (iterBubble k xs)) := by
  sorry

/-- Descent-count commutator inequality `desCnt(B^k(P(xs))) ≤ desCnt(P(B^k(xs)))`. -/
theorem desCnt_iterBubble_pop_le (k : Nat) (xs : List Nat) (hnd : xs.Nodup) :
    desCnt (iterBubble k (popSort xs)) ≤ desCnt (popSort (iterBubble k xs)) := by
  sorry

/-- Neither `westSort` nor `popSort` is monotone in Left Weak Bruhat Order. -/
theorem exists_westSort_popSort_not_weakBruhat_mono :
    ∃ u v : List Nat,
      u.Perm v ∧ u.Nodup ∧ WeakBruhatLe u v ∧
      ¬ WeakBruhatLe (westSort u) (westSort v) ∧
      ¬ WeakBruhatLe (popSort u) (popSort v) := by
  sorry

/-- Single-pass bubble sort and pop-stack sorting are incomparable in Left Weak Bruhat Order. -/
theorem exists_bubble_pop_incomparable :
    ∃ xs : List Nat, xs.Nodup ∧
      ¬ WeakBruhatLe (bubblePass xs) (popSort xs) ∧
      ¬ WeakBruhatLe (popSort xs) (bubblePass xs) := by
  sorry

end WeakBruhatCommutatorsChallenge
