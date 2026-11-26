/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sparse24E2M1Lop3

/-!
# Verified Solutions (`sparse24-e2m1-lop3`)
-/

namespace Sparse24E2M1Lop3Challenge

open Sparse24E2M1Lop3

theorem unpack_5t8b_to_e2m1_ten_lop3_and_lower_bound :
    (∀ w0 w1 w2 w3 w4 : Int,
      IsTrit w0 → IsTrit w1 → IsTrit w2 → IsTrit w3 → IsTrit w4 →
      decode5E2M1 (unpack5t8b (encode5t8b w0 w1 w2 w3 w4)) =
        (2 * w0, 2 * w1, 2 * w2, 2 * w3, 2 * w4)) ∧
    (∀ (dec : BitVec 8 → BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4),
      (∀ w0 w1 w2 w3 w4 : Int,
        IsTrit w0 → IsTrit w1 → IsTrit w2 → IsTrit w3 → IsTrit w4 →
        ∃ x : BitVec 8, decode5E2M1 (dec x) = (2 * w0, 2 * w1, 2 * w2, 2 * w3, 2 * w4)) →
      (∀ i : Fin 5,
        let fi : BitVec 8 → Bool := fun x => e2m1TwiceVal (slot5 i (dec x)) != 0
        162 ≤ weight fi ∧ weight fi ≤ 175) ∧
      (∀ g : BitVec 8 → Bool, DependsOnAtMost4 g → weight g % 16 = 0) ∧
      (∀ i : Fin 5, ¬ DependsOnAtMost4 (fun x => e2m1TwiceVal (slot5 i (dec x)) != 0))) :=
  Sparse24E2M1Lop3.unpack_5t8b_to_e2m1_ten_lop3_and_lower_bound

theorem sparse24_3bit_single_lop3_tight :
    (∀ m : BitVec 4, isMask24 m = true →
      ∃ x : BitVec 3, unpackMask24_3b x = m ∧ ∀ y : BitVec 3, unpackMask24_3b y = m → y = x) ∧
    (∀ dec : BitVec 3 → BitVec 4,
      (∀ m : BitVec 4, isMask24 m = true → ∃ x : BitVec 3, dec x = m) →
      ¬ (∀ b : Fin 4, WireOrConst (fun x : BitVec 3 => (dec x).getLsbD b.val))) ∧
    (∀ x : BitVec 3, (unpackUnordered24_3b x).1 ≠ (unpackUnordered24_3b x).2) ∧
    (∀ a b : Fin 4, a < b →
      let (u, v) := unpackUnordered24_3b (encodeUnordered24_3b a b)
      u ≠ v ∧ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))) :=
  Sparse24E2M1Lop3.sparse24_3bit_single_lop3_tight

theorem sparse24_3bit_ordered_three_lop3_tight :
    (∀ a b : Fin 4, a < b →
      unpackOrdered24_3b (encodeOrdered24_3b a b) = (a, b) ∧
      ∀ y : BitVec 3, unpackOrdered24_3b y = (a, b) → y = encodeOrdered24_3b a b) ∧
    (∀ dec : BitVec 3 → Fin 4 × Fin 4,
      (∀ a b : Fin 4, a < b → ∃ x : BitVec 3, dec x = (a, b)) →
      ∀ k1 k2 : Fin 4, k1 ≠ k2 →
        ¬ (WireOrConst (fun x => idxPairBit (dec x) k1) ∧
           WireOrConst (fun x => idxPairBit (dec x) k2))) :=
  Sparse24E2M1Lop3.sparse24_3bit_ordered_three_lop3_tight

theorem sparse24_8bit_triple_twelve_lop3_and_wire_bound :
    (∀ m0 m1 m2 : BitVec 4,
      isMask24 m0 = true → isMask24 m1 = true → isMask24 m2 = true →
      unpackTripleMask24_8b (encodeTripleMask24_8b m0 m1 m2) = (m0, m1, m2)) ∧
    (∀ d0 d1 d2 : Nat, d0 ≤ 3 → d1 ≤ 3 → d2 ≤ 3 → d0 + d1 + d2 ≤ 8 →
      maxFiber d0 * maxFiber d1 * maxFiber d2 ≤ 2 ^ (8 - (d0 + d1 + d2)) →
      d0 + d1 + d2 ≥ 3 →
      d0 + d1 + d2 = 3 ∧ d0 = 1 ∧ d1 = 1 ∧ d2 = 1) :=
  Sparse24E2M1Lop3.sparse24_8bit_triple_twelve_lop3_and_wire_bound

theorem e2m1_mag_mul_25lop3_exact :
    ∀ a b : BitVec 3, (e2m1MagMul25 a b).toNat = e2m1MagVal a * e2m1MagVal b :=
  Sparse24E2M1Lop3.e2m1_mag_mul_25lop3_exact

theorem quinary_2w5b_to_e2m1_four_lop3_and_wire_bound :
    (∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
      let (n0, n1) := unpack2q5b (encode2q5b w0 w1)
      e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1) ∧
    (∀ dec : BitVec 5 → BitVec 4 × BitVec 4,
      (∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
        ∃ x : BitVec 5,
          e2m1TwiceVal (dec x).1 = 2 * w0 ∧ e2m1TwiceVal (dec x).2 = 2 * w1) →
      ∀ k0 k1 k2 k3 : Fin 6,
        k0 ≠ k1 → k0 ≠ k2 → k0 ≠ k3 → k1 ≠ k2 → k1 ≠ k3 → k2 ≠ k3 →
        ¬ (WireOrConst (fun x => quinaryOutBit (dec x) k0) ∧
           WireOrConst (fun x => quinaryOutBit (dec x) k1) ∧
           WireOrConst (fun x => quinaryOutBit (dec x) k2) ∧
           WireOrConst (fun x => quinaryOutBit (dec x) k3))) :=
  Sparse24E2M1Lop3.quinary_2w5b_to_e2m1_four_lop3_and_wire_bound

end Sparse24E2M1Lop3Challenge
