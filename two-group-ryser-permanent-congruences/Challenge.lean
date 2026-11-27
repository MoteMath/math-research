/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoGroupRyserPermanentCongruences.Defs

/-!
# Trusted Challenge Statements (`two-group-ryser-permanent-congruences`)

Statements of the bitmask Ryser formula for the permanent, 2-group orbit-collapse congruences of the permanent modulo 2^(k + 1) and 2^(k + 2) for equivariant matrices, and exact congruences for XOR-circulant and hypercube adjacency matrices.
-/

namespace TwoGroupRyserPermanentCongruencesChallenge

open SpecMat9 in
/-- Theorem 1 (Bitmask Ryser formula): the permanent of every n x n integer matrix equals its Ryser inclusion-exclusion bitmask sum. -/
theorem perm_eq_ryserSum (n : Nat) (A : Mat n) :
    perm n A = ryserSum n A := by
  sorry

open SpecMat9 in
/-- Theorem 2 (2-group orbit-collapse congruence): for a matrix equivariant under a free 2^k-group action, perm(A) is congruent to the number of odd solutions modulo 2^(k + 1). -/
theorem perm_mod_two_pow_succ {k n : Nat} (hk : 1 ≤ k) (Gr : Fin2Group k)
    (BA : FreeBiAction Gr n) (A : Mat n) (heq : IsEquivariant BA A) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm n A - (oddSolCount n A : Int)) := by
  sorry

open SpecMat9 in
/-- Theorem 3 (XOR-circulant congruence): for every k >= 1 and f, the permanent of the 2^k x 2^k XOR-circulant is congruent to its odd-solution count modulo 2^(k + 1). -/
theorem xorCirc_perm_mod_two_pow_succ {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm (2 ^ k) (xorCirc k f) - (oddSolCount (2 ^ k) (xorCirc k f) : Int)) := by
  sorry

open SpecMat9 in
/-- Theorem 4 (Even-row-sum divisibility): for k >= 3 and even total row sum, 2^(k + 1) divides the permanent of the XOR-circulant. -/
theorem xorCirc_even_rowSum_dvd {k : Nat} (hk : 3 ≤ k) (f : Fin (2 ^ k) → Int)
    (heven : rowSumAll k f % 2 = 0) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ perm (2 ^ k) (xorCirc k f) := by
  sorry

open SpecMat9 in
/-- Theorem 5 (Mod 2^(k + 2) refinement): for odd row sum, the XOR-circulant permanent is congruent modulo 2^(k + 2) to an explicit closed form in the odd and even counts. -/
theorem xorCirc_odd_mod_two_pow_add_two {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) :
    ((2 ^ (k + 2) : Nat) : Int) ∣
      (perm (2 ^ k) (xorCirc k f) -
        (1 + ((2 ^ k : Nat) : Int) * (((oddCount k f : Int) - 1) + evenSum k f))) := by
  sorry

open SpecMat9 in
/-- Theorem 6 (Hypercube adjacency, odd k): for odd k the permanent of the hypercube adjacency matrix is congruent to 1 + 2^k (k - 1) modulo 2^(k + 2). -/
theorem hypercubeAdj_odd_mod {k : Nat} (hk : 1 ≤ k) (hodd : k % 2 = 1) :
    ((2 ^ (k + 2) : Nat) : Int) ∣
      (perm (2 ^ k) (hypercubeAdj k) - (1 + ((2 ^ k : Nat) : Int) * ((k : Int) - 1))) := by
  sorry

open SpecMat9 in
/-- Theorem 7 (Hypercube adjacency, even k): for even k >= 4, 2^(k + 1) divides the permanent of the hypercube adjacency matrix. -/
theorem hypercubeAdj_even_dvd {k : Nat} (hk : 4 ≤ k) (heven : k % 2 = 0) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ perm (2 ^ k) (hypercubeAdj k) := by
  sorry

open SpecMat9 in
/-- Theorem 8 (Hypercube matchings): for odd m >= 3, 2^(m + 1) divides the permanent of the hypercube bipartite adjacency matrix. -/
theorem hypercubeMatching_even_dvd {m : Nat} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    ((2 ^ (m + 1) : Nat) : Int) ∣ perm (2 ^ m) (hypercubeBiadj m) := by
  sorry

end TwoGroupRyserPermanentCongruencesChallenge
