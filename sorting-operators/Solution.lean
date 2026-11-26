/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SortingOperators

/-!
# Verified Solutions (`sorting-operators`)

Provides sorry-free proofs for every theorem in `Challenge.lean`.
-/

namespace SortingOperatorsChallenge

open SortingOperators

theorem inv_bubble_add_des_le_inv (xs : List Nat) :
    invCnt (bubblePass xs) + desCnt xs ≤ invCnt xs :=
  SortingOperators.inv_bubble_add_des_le_inv xs

theorem des_bubble_le_des (xs : List Nat) :
    desCnt (bubblePass xs) ≤ desCnt xs :=
  SortingOperators.des_bubble_le_des xs

theorem westSort_split_max (L R : List Nat) (m : Nat)
    (hL : ∀ a ∈ L, a < m) (hR : ∀ b ∈ R, b < m) :
    westSort (L ++ m :: R) = westSort L ++ westSort R ++ [m] :=
  SortingOperators.westSort_split_max L R m hL hR

theorem bubblePass_split_max (L R : List Nat) (m : Nat)
    (hL : ∀ a ∈ L, a < m) (hR : ∀ b ∈ R, b < m) :
    bubblePass (L ++ m :: R) = bubblePass L ++ R ++ [m] :=
  SortingOperators.bubblePass_split_max L R m hL hR

theorem inv_westSort_le_bubble (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (westSort xs) ≤ invCnt (bubblePass xs) :=
  SortingOperators.inv_westSort_le_bubble xs hnd

theorem des_westSort_le_bubble (xs : List Nat) (hnd : xs.Nodup) :
    desCnt (westSort xs) ≤ desCnt (bubblePass xs) :=
  SortingOperators.des_westSort_le_bubble xs hnd

theorem westSort_eq_bubble_of_avoids321 (xs : List Nat) (hnd : xs.Nodup) (hav : Avoids321 xs) :
    westSort xs = bubblePass xs :=
  SortingOperators.westSort_eq_bubble_of_avoids321 xs hnd hav

theorem exists_not_avoids321_westSort_eq_bubble :
    ∃ xs : List Nat, xs.Nodup ∧ ¬ Avoids321 xs ∧ westSort xs = bubblePass xs :=
  SortingOperators.exists_not_avoids321_westSort_eq_bubble

theorem inv_bubble_le_pat321_add_pat231 (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (bubblePass xs) ≤ pat321 xs + pat231 xs :=
  SortingOperators.inv_bubble_le_pat321_add_pat231 xs hnd

end SortingOperatorsChallenge
