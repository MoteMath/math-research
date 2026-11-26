/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ZeroCarrySpanningTrees.Defs

/-!
# Trusted Challenge Statements (`zero-carry-spanning-trees`)

This file imports `ZeroCarrySpanningTrees.Defs` alone (which imports Mathlib alone) and states
all 5 headline theorems with `sorry` placeholders for `leanprover/comparator`.
-/

namespace ZeroCarrySpanningTreesChallenge

open ZeroCarrySpanningTrees

/-- Theorem 1 (Alternating-harmonic spectrum of the mixed-radix zero-carry walk matrix):
for every mixed radix `b_r ≥ 1` and every `x : ℚ`, `det (x • 1 - W_{b,k})` splits completely
into factors with roots `∏_{r < k} (-1)^{d_r(j)} / (d_r(j) + 1)`. -/
theorem det_zeroCarryWalk_charpoly (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) (x : ℚ) :
    (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - zeroCarryWalkMatrix b k).det =
      ∏ j : Fin (place b k),
        (x - ∏ r ∈ Finset.range k,
          ((-1 : ℚ) ^ mdigit b j.1 r / ((mdigit b j.1 r + 1 : ℕ) : ℚ))) := by
  sorry

/-- Theorem 2 (Exact mixed-radix zero-carry graph Kirchhoff spanning-tree formula):
over any commutative ring `R`, for any mixed radix `b_r ≥ 1`, the `(0, 0)`-cofactor determinant
of the zero-carry graph Laplacian satisfies the cleared-denominator product identity. -/
theorem det_zeroCarryCofactor_mixed {R : Type*} [CommRing R]
    (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (∏ r ∈ Finset.range k, ((b r * (b r + 1) / 2 : ℕ) : R)) *
      (zeroCarryCofactor (R := R) b k).det =
      ∏ j : Fin (place b k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : R)) -
          ∏ r ∈ Finset.range k, (-1 : R) ^ mdigit b (j.1 + 1) r) := by
  sorry

/-- Corollary 2.1 (Uniform base-`B` zero-carry graph spanning-tree formula). -/
theorem det_zeroCarryCofactor_base {R : Type*} [CommRing R]
    (B : ℕ) (hB : 1 ≤ B) (k : ℕ) :
    (((B * (B + 1) / 2 : ℕ) : R) ^ k) *
      (zeroCarryCofactor (R := R) (fun _ => B) k).det =
      ∏ j : Fin (place (fun _ => B) k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit (fun _ => B) (j.1 + 1) r + 1 : ℕ) : R)) -
          ∏ r ∈ Finset.range k, (-1 : R) ^ mdigit (fun _ => B) (j.1 + 1) r) := by
  sorry

/-- Corollary 2.2 (Binary zero-carry / bitwise-disjoint graph spanning-tree formula):
over any commutative ring `R`, the Kirchhoff spanning-tree count of the graph
`i ~ j ↔ i ≠ j ∧ (i &&& j) = 0` on `{0, ..., 2^k - 1}` is
`∏_{m = 2}^{k} (2^m - (-1)^m)^{C(k, m)}`. -/
theorem det_binaryZeroCarryCofactor {R : Type*} [CommRing R] (k : ℕ) :
    (binaryZeroCarryCofactor (R := R) k).det =
      ∏ m ∈ Finset.Ico 2 (k + 1),
        ((2 : R) ^ m - (-1 : R) ^ m) ^ (k.choose m) := by
  sorry

/-- Corollary 2.3 (Single-radix `k = 1` threshold half-graph spanning-tree formula). -/
theorem det_singleRadixZeroCarryCofactor {R : Type*} [CommRing R] (B : ℕ) (hB : 1 ≤ B) :
    ((B * (B + 1) / 2 : ℕ) : R) *
      (zeroCarryCofactor (R := R) (fun _ => B) 1).det =
      ∏ j ∈ Finset.Ico 1 B, (((j + 1 : ℕ) : R) - (-1 : R) ^ j) := by
  sorry

end ZeroCarrySpanningTreesChallenge
