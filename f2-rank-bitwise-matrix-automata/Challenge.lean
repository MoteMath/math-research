/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import F2RankBitwiseMatrixAutomata.Defs

/-!
# Trusted Challenge Statements (`f2-rank-bitwise-matrix-automata`)

Statements of exact F2 rank and kernel-cardinality laws, isotropic rank-one decoupling of block matrices, the exact nullity of the carry-free XOR-sum parity matrix for every n, invertibility exactly at powers of two, and the base-4 automaton criterion for the Hamming-type matrix.
-/

namespace F2RankBitwiseMatrixAutomataChallenge

open F2RankAutomaton in
/-- Theorem 1 (Kernel-count law): if M has F2 rank r then its kernel has exactly 2^(n - r) vectors. -/
theorem hasRank_kerCount {m n r : Nat} {M : Mat m n} (h : HasRank M r) :
    kerCount M = 2 ^ (n - r) := by
  sorry

open F2RankAutomaton in
/-- Theorem 2 (Rank uniqueness): the F2 rank of a matrix is unique. -/
theorem hasRank_unique {m n r1 r2 : Nat} {M : Mat m n}
    (h1 : HasRank M r1) (h2 : HasRank M r2) : r1 = r2 := by
  sorry

open F2RankAutomaton in
/-- Theorem 3 (Isotropic rank-one decoupling): a symmetric block with an isotropic preimage decouples the coupled block matrix, whose rank is the sum rA + rB. -/
theorem hasRank_isotropic_rank1_decouple {a b rA rB : Nat}
    {A : Mat a a} {B : Mat b b} {u : Vec a} {v : Vec b}
    (hAsym : ∀ i j, A i j = A j i)
    (x : Vec a) (hAx : matVec A x = u) (hiso : vdot u x = false)
    (hA : HasRank A rA) (hB : HasRank B rB) :
    HasRank (blockMat A (outerMat u v) (outerMat v u) B) (rA + rB) := by
  sorry

open F2RankAutomaton in
/-- Theorem 4 (Parity-matrix nullity): for every n >= 2 the carry-free XOR-sum parity matrix M0(n) has nullity popcount(gray(n - 1)) - 1. -/
theorem M0_gray_nullity (n : Nat) (hn : n ≥ 2) :
    HasNullity (M0Mat n) (popcount (gray (n - 1)) - 1) := by
  sorry

open F2RankAutomaton in
/-- Theorem 5 (Parity-matrix kernel size): for every n >= 2, M0(n) has exactly 2^(popcount(gray(n - 1)) - 1) kernel vectors. -/
theorem M0_kerCount (n : Nat) (hn : n ≥ 2) :
    kerCount (M0Mat n) = 2 ^ (popcount (gray (n - 1)) - 1) := by
  sorry

open F2RankAutomaton in
/-- Theorem 6 (Invertibility at powers of two): M0(n) is invertible over F2 iff n = 2^k with k >= 1. -/
theorem M0_invertible_iff_pow2 (n : Nat) (hn : n ≥ 1) :
    HasRank (M0Mat n) n ↔ ∃ k : Nat, k ≥ 1 ∧ n = 2 ^ k := by
  sorry

open F2RankAutomaton in
/-- Theorem 7 (Hamming-type kernel size): the kernel of HMat d n has exactly 2^(hcNullity d n) vectors for every n. -/
theorem H_kerCount (d : Bool) (n : Nat) : kerCount (HMat d n) = 2 ^ (hcNullity d n) := by
  sorry

open F2RankAutomaton in
/-- Theorem 8 (Base-4 automaton criterion): HMat false n has full rank iff the base-4 DFA accepts n. -/
theorem H0_invertible_iff_base4 (n : Nat) :
    HasRank (HMat false n) n ↔ hc0Base4Accept n = true := by
  sorry

end F2RankBitwiseMatrixAutomataChallenge
