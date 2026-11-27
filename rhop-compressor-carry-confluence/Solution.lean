/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RhopCompressorCarryConfluence

/-!
# Verified Solutions (`rhop-compressor-carry-confluence`)
-/

namespace RhopCompressorCarryConfluenceChallenge

open RhopCompressorCarryConfluence

theorem carry_free_capacity_dichotomy (p v M : Nat) (hp_pos : 1 ≤ p) :
    Nonempty (CarryFreeCell p v M) ↔ M ≤ 2 * v ∧ p ≤ M + 2 * v + 1 :=
  RhopCompressorCarryConfluence.carry_free_capacity_dichotomy p v M hp_pos

theorem rhop_capacity_dichotomy (p v r : Nat) (hp_pos : 1 ≤ p) :
    Nonempty (RHopCompressor p v r) ↔ p ≤ 2 * v * 2 ^ r + 1 :=
  RhopCompressorCarryConfluence.rhop_capacity_dichotomy p v r hp_pos

theorem no_carry_free_6_2 (M : Nat) : ¬ Nonempty (CarryFreeCell 6 1 M) :=
  RhopCompressorCarryConfluence.no_carry_free_6_2 M

theorem no_3hop_18_2 : ¬ Nonempty (RHopCompressor 18 1 3) :=
  RhopCompressorCarryConfluence.no_3hop_18_2

theorem cell42_bijection_right (h : (Fin 4 → Bool) → Nat) (hh : IsValid42H h) :
    ∃ m : Fin 64, ∀ x, h42OfMask m x = h x :=
  RhopCompressorCarryConfluence.cell42_bijection_right h hh

theorem netW_popcount_carry_conservation {w d : Nat} {X Y : List Nat} {K : Nat → Nat}
    (hnet : NetW w d X Y K) (hw : 1 ≤ w) :
    popListW Y w + sumRange K (w - 1) + 2 * K (w - 1) = popListW X w :=
  RhopCompressorCarryConfluence.netW_popcount_carry_conservation hnet hw

theorem confluence_csa_3state {w d1 d2 : Nat} {X Y1 Y2 : List Nat} {K1 K2 : Nat → Nat}
    (h1 : NetW w d1 X Y1 K1) (h2 : NetW w d2 X Y2 K2)
    (hb1 : ∀ k < w, colSum Y1 k ≤ 2) (hb2 : ∀ k < w, colSum Y2 k ≤ 2) :
    ∀ j ≤ w,
      runTransducer 2 Y1 Y2 j = some ((ledgerIn K2 j : Int) - (ledgerIn K1 j : Int)) ∧
      -1 ≤ (ledgerIn K2 j : Int) - (ledgerIn K1 j : Int) ∧
      (ledgerIn K2 j : Int) - (ledgerIn K1 j : Int) ≤ 1 :=
  RhopCompressorCarryConfluence.confluence_csa_3state h1 h2 hb1 hb2

theorem transducer_state_minimality (h : Nat) (hh : 1 ≤ h) (q : Int) (hq : inStateSpace h q) :
    ∃ (w : Nat) (Y1 Y2 : List Nat),
      (∀ k, colSum Y1 k ≤ h) ∧
      (∀ k, colSum Y2 k ≤ h) ∧
      sumList Y1 = sumList Y2 ∧
      runTransducer h Y1 Y2 w = some q :=
  RhopCompressorCarryConfluence.transducer_state_minimality h hh q hq

end RhopCompressorCarryConfluenceChallenge
