/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sparse24E2M1Lop3.Defs

/-!
# Trusted Challenge Statements (`sparse24-e2m1-lop3`)

Statements of the six headline theorems for Wave 1C (`w1-lop3-subbyte-synth`) GPU-synthesized
`LOP3` circuits and exact lower-bound theorems:
1. `unpack_5t8b_to_e2m1_ten_lop3_and_lower_bound`: 10-`LOP3` direct-sign 5t8b → 5×E2M1 unpacker
   (243/243 exact) and general ≥ 5-essential-variable (`LOP3` depth ≥ 2) lower bound.
2. `sparse24_3bit_single_lop3_tight`: Tight 1-`LOP3` 3b → 4b 2:4 mask (bijection + 0-`LOP3`
   impossibility) and 1-`LOP3` 3b → unordered `{idx0, idx1}` (3× reduction over ordered).
3. `sparse24_3bit_ordered_three_lop3_tight`: Tight 3-`LOP3` 3b → ordered `(idx0 < idx1)`
   bijection and general lower bound (at most 1 output bit can be a wire → ≥ 3 `LOP3`).
4. `sparse24_8bit_triple_twelve_lop3_and_wire_bound`: 12-`LOP3` 8b → 3×4b 2:4 masks (216/216
   exact) and unique `(1, 1, 1)` fiber-product pigeonhole direct-wire theorem (`≤ 3` wires).
5. `e2m1_mag_mul_25lop3_exact`: 25-`LOP3` zero-FP `E2M1 × E2M1` magnitude multiplier (64/64 exact).
6. `quinary_2w5b_to_e2m1_four_lop3_and_wire_bound`: 4-`LOP3` depth-2 2q5b → 2×E2M1 unpacker
   (25/25 exact) and general 4-wire impossibility theorem (≥ 3 `LOP3`).
-/

namespace Sparse24E2M1Lop3Challenge

open Sparse24E2M1Lop3

/-- Theorem 1 (Frontier 1): Exact 10-`LOP3` direct-sign `5t8b → 5 × E2M1` unpacker (`243/243`
    exact, `-60.0%` VRAM vs FP4) and general lower bound proving every nonzero indicator `f_i`
    of ANY surjective `5t8b → 5 × E2M1` decoder has `162 ≤ weight f_i ≤ 175`, while every
    `≤ 4`-variable Boolean function on `BitVec 8` has `weight g % 16 = 0` (`≥ 5` essential
    variables and `LOP3` depth `≥ 2` on every output). -/
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
      (∀ i : Fin 5, ¬ DependsOnAtMost4 (fun x => e2m1TwiceVal (slot5 i (dec x)) != 0))) := by
  sorry

/-- Theorem 2 (Frontier 2A, 1-`LOP3` tight):
    - `unpackMask24_3b` (`0x17`, `~MAJ3`) is an exact bijection onto all 6 valid 2-of-4 masks,
      and NO 0-`LOP3` (pure-wire / negated-wire / constant) decoder can cover all 6 masks.
    - `unpackUnordered24_3b` (`0x63`) produces distinct indices on all inputs and covers all 6
      unordered pairs `{a, b} ⊂ Fin 4` in 1 `LOP3` gate (3× fewer than ordered `idx0 < idx1`). -/
theorem sparse24_3bit_single_lop3_tight :
    (∀ m : BitVec 4, isMask24 m = true →
      ∃ x : BitVec 3, unpackMask24_3b x = m ∧ ∀ y : BitVec 3, unpackMask24_3b y = m → y = x) ∧
    (∀ dec : BitVec 3 → BitVec 4,
      (∀ m : BitVec 4, isMask24 m = true → ∃ x : BitVec 3, dec x = m) →
      ¬ (∀ b : Fin 4, WireOrConst (fun x : BitVec 3 => (dec x).getLsbD b.val))) ∧
    (∀ x : BitVec 3, (unpackUnordered24_3b x).1 ≠ (unpackUnordered24_3b x).2) ∧
    (∀ a b : Fin 4, a < b →
      let (u, v) := unpackUnordered24_3b (encodeUnordered24_3b a b)
      u ≠ v ∧ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))) := by
  sorry

/-- Theorem 3 (Frontier 2A, 3-`LOP3` tight):
    `unpackOrdered24_3b` (`i0_0 = c2`, `0x08`, `0x2D`, `0x3E`) is an exact bijection onto all 6
    ordered pairs `a < b` in `Fin 4`, and for ANY surjective ordered `3b → (idx0 < idx1)`
    decoder, no two distinct output bits can both be raw/inverted wires or constants (at most 1
    direct wire, forcing `≥ 3 LOP3`). -/
theorem sparse24_3bit_ordered_three_lop3_tight :
    (∀ a b : Fin 4, a < b →
      unpackOrdered24_3b (encodeOrdered24_3b a b) = (a, b) ∧
      ∀ y : BitVec 3, unpackOrdered24_3b y = (a, b) → y = encodeOrdered24_3b a b) ∧
    (∀ dec : BitVec 3 → Fin 4 × Fin 4,
      (∀ a b : Fin 4, a < b → ∃ x : BitVec 3, dec x = (a, b)) →
      ∀ k1 k2 : Fin 4, k1 ≠ k2 →
        ¬ (WireOrConst (fun x => idxPairBit (dec x) k1) ∧
           WireOrConst (fun x => idxPairBit (dec x) k2))) := by
  sorry

/-- Theorem 4 (Frontier 2B): Exact 12-`LOP3` `8b → 3 × 4b 2:4 masks` unpacker covering all
    `6^3 = 216` mask triples (`-33.3%` metadata), plus the exact fiber-product pigeonhole theorem
    proving `d0 + d1 + d2 ≤ 3` direct wires achieved uniquely at `(1, 1, 1)`. -/
theorem sparse24_8bit_triple_twelve_lop3_and_wire_bound :
    (∀ m0 m1 m2 : BitVec 4,
      isMask24 m0 = true → isMask24 m1 = true → isMask24 m2 = true →
      unpackTripleMask24_8b (encodeTripleMask24_8b m0 m1 m2) = (m0, m1, m2)) ∧
    (∀ d0 d1 d2 : Nat, d0 ≤ 3 → d1 ≤ 3 → d2 ≤ 3 → d0 + d1 + d2 ≤ 8 →
      maxFiber d0 * maxFiber d1 * maxFiber d2 ≤ 2 ^ (8 - (d0 + d1 + d2)) →
      d0 + d1 + d2 ≥ 3 →
      d0 + d1 + d2 = 3 ∧ d0 = 1 ∧ d1 = 1 ∧ d2 = 1) := by
  sorry

/-- Theorem 5 (Frontier 3): Exact 25-`LOP3` zero-FP `E2M1 × E2M1` magnitude multiplier
    (`64 / 64` exact products in `[0, 144]`). -/
theorem e2m1_mag_mul_25lop3_exact :
    ∀ a b : BitVec 3, (e2m1MagMul25 a b).toNat = e2m1MagVal a * e2m1MagVal b := by
  sorry

/-- Theorem 6 (Frontier 4): Exact 4-`LOP3` depth-2 `2q5b → 2 × E2M1` unpacker covering all 25
    quinary pairs in `{-2, -1, 0, +1, +2}^2`, plus the general 4-wire impossibility theorem
    proving no 4 of the 6 E2M1 output bits can be direct/inverted wires on `BitVec 5`
    (forcing `≥ 3 LOP3`). -/
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
           WireOrConst (fun x => quinaryOutBit (dec x) k3))) := by
  sorry

end Sparse24E2M1Lop3Challenge
