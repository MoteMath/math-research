/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrayCarryWhiteningTransducer.Defs

/-!
# Trusted Challenge Statements (`gray-carry-whitening-transducer`)

Statements of exact fiber counts for the Gray-coded carry word of binary addition, whitening in binary and Gray coordinates, the joint carry-borrow fiber law, carry-borrow Gray orthogonality, the radix-B whitening law, and the k-operand impossibility.
-/

namespace GrayCarryWhiteningTransducerChallenge

open GrayTransducerEngine in
/-- Theorem 1 (Whitening law): the number of operand pairs of width w whose Gray-coded carry word equals z modulo 2^w is 3^(w - popcount z). -/
theorem gray_carry_whitening_binary (w : Nat) (c0 : Bool) (z : Nat) (hz : z < 2 ^ w) :
    countPairs w (fun a b => decide (gray (carryWord a b c0) % 2 ^ w = z)) =
      3 ^ (w - popcount z) := by
  sorry

open GrayTransducerEngine in
/-- Theorem 2 (Whitening in Gray coordinates): the same count holds for the Gray-coordinate carry defect of Gray-code addition. -/
theorem gray_carry_whitening_gray_coords (w : Nat) (c0 : Bool) (z : Nat) (hz : z < 2 ^ w) :
    countPairs w (fun x y => decide ((grayAddWith x y c0 ^^^ x ^^^ y) % 2 ^ w = z)) =
      3 ^ (w - popcount z) := by
  sorry

open GrayTransducerEngine in
/-- Theorem 3 (Full fiber count): exact fiber size of the full Gray-coded carry word including the parity-forced top bit. -/
theorem gray_carry_full_fiber_count (w : Nat) (c0 : Bool) (z : Nat) (hz : z < 2 ^ (w + 1)) :
    countPairs w (fun a b => decide (gray (carryWord a b c0) = z)) =
      if parity z = c0 then 3 ^ (w - popcount (z % 2 ^ w)) else 0 := by
  sorry

open GrayTransducerEngine in
/-- Theorem 4 (Joint carry-borrow fibers): exact joint count of Gray carry and borrow words, supported on disjoint masks. -/
theorem gray_joint_carry_borrow_fiber_count (w : Nat) (c0 b0 : Bool) (u v : Nat)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w) :
    countPairs w (fun a b =>
      decide (gray (carryWord a b c0) % 2 ^ w = u ∧
              gray (borrowWordFull w a b b0) % 2 ^ w = v)) =
      if u &&& v = 0 then 2 ^ (w - popcount u - popcount v) else 0 := by
  sorry

open GrayTransducerEngine in
/-- Theorem 5 (Gray orthogonality): the Gray-coded carry and borrow words of an addition and subtraction pair are disjoint. -/
theorem gray_carry_borrow_orthogonal (a b : Nat) (c0 b0 : Bool) (h : b + b0.toNat ≤ a) :
    (gray (carryWord a b c0)) &&& (gray (borrowWord a b b0)) = 0 := by
  sorry

open GrayTransducerEngine in
/-- Theorem 6 (Radix-B whitening): exact fiber count of the carry-difference word in every base B at least 2. -/
theorem radix_carry_whitening_law (B : Nat) (hB : 2 ≤ B) (w : Nat) (c0 : Bool)
    (z : Nat) (hz : z < 2 ^ w) :
    countPairsBase B w (fun a b => decide (carryDiffWordBase B c0 a b w = z)) =
      (B * (B + 1) / 2) ^ (w - popcount z) * (B * (B - 1) / 2) ^ (popcount z) := by
  sorry

open GrayTransducerEngine in
/-- Theorem 7 (k-operand impossibility): for k at least 3 operands, the carry-sum slice counts of the multi-operand carry transducer are not all equal, so balanced whitening is impossible. -/
theorem k_operand_whitening_impossibility (k : Nat) (hk : 3 ≤ k) :
    multiCarrySlice1 k 0 ≠ multiCarrySlice1 k 2 ∨
    multiCarrySlice1 k 0 ≠ multiCarrySlice1 k 1 := by
  sorry

open GrayTransducerEngine in
/-- Theorem 8 (Binary uniqueness): in every base B at least 3 there are digits d1, d2 below B with a carry and a borrow at the same position, so B = 2 is the unique radix with carry-borrow orthogonality. -/
theorem radix_carry_borrow_orthogonality_binary_unique (B : Nat) (hB : 3 ≤ B) :
    ∃ d1 d2, d1 < B ∧ d2 < B ∧
      Bool.xor false (decide (B ≤ d1 + d2)) = true ∧
      Bool.xor false (decide (d1 < d2)) = true := by
  sorry

end GrayCarryWhiteningTransducerChallenge
