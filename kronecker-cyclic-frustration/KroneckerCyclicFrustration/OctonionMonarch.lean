/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KroneckerCyclicFrustration.MonarchCoherence

/-!
# Universal Quaternion (`4×4`) & Octonion (`8×8`) Orthogonality and Zero-Error `E2M1` Sparse Monarch Blocks

Proves Headline Theorem 5 (`octonion_sparse_e2m1_monarch_blocks_exact`) in pure `Init`
(zero Mathlib, zero `native_decide`).
-/

namespace KroneckerCyclicFrustration

/-- Universal `4 × 4` Quaternion orthogonality: `Q(a, b, c, d)^T Q(a, b, c, d) = (a^2+b^2+c^2+d^2) I_4`. -/
theorem quat4_scaled_ortho (a b c d : Int) :
    IsScaledOrtho (quat4 a b c d) (a * a + b * b + c * c + d * d) := by
  intro i j
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨0, _⟩, ⟨3, _⟩
  | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩ | ⟨1, _⟩, ⟨3, _⟩
  | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨3, _⟩
  | ⟨3, _⟩, ⟨0, _⟩ | ⟨3, _⟩, ⟨1, _⟩ | ⟨3, _⟩, ⟨2, _⟩ | ⟨3, _⟩, ⟨3, _⟩ =>
    simp [matColDot, finSumInt, quat4] <;> grind

/-- Explicit 8-term unfolding of `finSumInt` on `Fin 8`. -/
theorem finSumInt_eight (f : Fin 8 → Int) :
    finSumInt f =
      f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ + f ⟨7, by decide⟩ := by
  simp only [finSumInt, Fin.castSucc, Fin.castAdd, Fin.castLE, Int.zero_add]

theorem matColDot_symm {n : Nat} (M : Fin n → Fin n → Int) (i j : Fin n) :
    matColDot M i j = matColDot M j i := by
  unfold matColDot
  apply finSumInt_congr
  intro k
  exact Int.mul_comm _ _

private theorem oct8_col_01 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (i j : Fin 8)
    (hi : i.val = 0 ∨ i.val = 1) (hij : i.val ≤ j.val) :
    matColDot (oct8 c0 c1 c2 c3 c4 c5 c6 c7) i j =
      if i = j then
        c0 * c0 + c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 + c5 * c5 + c6 * c6 + c7 * c7
      else 0 := by
  rcases i with ⟨iv, hiv⟩
  rcases j with ⟨jv, hjv⟩
  dsimp only at hi hij
  have hj : jv = 0 ∨ jv = 1 ∨ jv = 2 ∨ jv = 3 ∨ jv = 4 ∨ jv = 5 ∨ jv = 6 ∨ jv = 7 := by omega
  rcases hi with rfl | rfl <;>
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | omega | (unfold matColDot; rw [finSumInt_eight]; dsimp only [oct8]; simp only [Fin.mk.injEq]; grind)

private theorem oct8_col_23 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (i j : Fin 8)
    (hi : i.val = 2 ∨ i.val = 3) (hij : i.val ≤ j.val) :
    matColDot (oct8 c0 c1 c2 c3 c4 c5 c6 c7) i j =
      if i = j then
        c0 * c0 + c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 + c5 * c5 + c6 * c6 + c7 * c7
      else 0 := by
  rcases i with ⟨iv, hiv⟩
  rcases j with ⟨jv, hjv⟩
  dsimp only at hi hij
  have hj : jv = 2 ∨ jv = 3 ∨ jv = 4 ∨ jv = 5 ∨ jv = 6 ∨ jv = 7 := by omega
  rcases hi with rfl | rfl <;>
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | omega | (unfold matColDot; rw [finSumInt_eight]; dsimp only [oct8]; simp only [Fin.mk.injEq]; grind)

private theorem oct8_col_4567 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (i j : Fin 8)
    (hi : i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7) (hij : i.val ≤ j.val) :
    matColDot (oct8 c0 c1 c2 c3 c4 c5 c6 c7) i j =
      if i = j then
        c0 * c0 + c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 + c5 * c5 + c6 * c6 + c7 * c7
      else 0 := by
  rcases i with ⟨iv, hiv⟩
  rcases j with ⟨jv, hjv⟩
  dsimp only at hi hij
  have hj : jv = 4 ∨ jv = 5 ∨ jv = 6 ∨ jv = 7 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
  rcases hj with rfl | rfl | rfl | rfl
  all_goals first | omega | (unfold matColDot; rw [finSumInt_eight]; dsimp only [oct8]; simp only [Fin.mk.injEq]; grind)

/-- Universal `8 × 8` Octonion orthogonality (Fano-plane):
    `O(c0..c7)^T O(c0..c7) = (∑ c_i^2) I_8` for ALL `c0..c7 : Int`. -/
theorem oct8_scaled_ortho (c0 c1 c2 c3 c4 c5 c6 c7 : Int) :
    IsScaledOrtho (oct8 c0 c1 c2 c3 c4 c5 c6 c7)
      (c0 * c0 + c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 + c5 * c5 + c6 * c6 + c7 * c7) := by
  have hle : ∀ i j : Fin 8, i.val ≤ j.val →
      matColDot (oct8 c0 c1 c2 c3 c4 c5 c6 c7) i j =
        if i = j then
          c0 * c0 + c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 + c5 * c5 + c6 * c6 + c7 * c7
        else 0 := by
    intro i j hij
    have hi : (i.val = 0 ∨ i.val = 1) ∨ (i.val = 2 ∨ i.val = 3) ∨
              (i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7) := by omega
    rcases hi with h01 | h23 | h4567
    · exact oct8_col_01 c0 c1 c2 c3 c4 c5 c6 c7 i j h01 hij
    · exact oct8_col_23 c0 c1 c2 c3 c4 c5 c6 c7 i j h23 hij
    · exact oct8_col_4567 c0 c1 c2 c3 c4 c5 c6 c7 i j h4567 hij
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact hle i j hij
  · rw [matColDot_symm, hle j i (by omega)]
    by_cases heq : i = j
    · subst heq; simp
    · have hne : j ≠ i := Ne.symm heq
      simp [heq, hne]

/-- Helper: concrete `IsOptimalSparseE2M1Block` check for `sparseQuat4 s` (`1 ≤ s ≤ 4`). -/
theorem sparseQuat4_optimal (s : Nat) (hs1 : 1 ≤ s) (hs4 : s ≤ 4) :
    IsOptimalSparseE2M1Block (sparseQuat4 s) s := by
  have hs : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j; revert i j; decide
    · intro i j; revert i j; decide
    · intro i j; revert i j; decide
    · intro i; revert i; decide
    · intro i; revert i; decide

/-- Helper: concrete `IsOptimalSparseE2M1Block` check for `sparseOct8 s` (`1 ≤ s ≤ 8`). -/
theorem sparseOct8_optimal (s : Nat) (hs1 : 1 ≤ s) (hs8 : s ≤ 8) :
    IsOptimalSparseE2M1Block (sparseOct8 s) s := by
  have hs : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j; revert i j; decide
    · intro i j; revert i j; decide
    · intro i j; revert i j; decide
    · intro i; revert i; decide
    · intro i; revert i; decide

/-- Headline Theorem 5 (`octonion_sparse_e2m1_monarch_blocks_exact`):
    Proves universal `4×4` Quaternion and `8×8` Octonion orthogonality over `Int`,
    exact zero-error OCP `E2M1` membership, uniform row sparsity `s`, and optimal coherence `1/s`
    for all sparse Quaternion blocks (`s ∈ {1..4}`) and all sparse Octonion blocks (`s ∈ {1..8}`),
    and certifies the exact MAC-reduction & coherence certificates for `Q4_1110`, `O8_4nnz`, and `O8_7nnz`. -/
theorem octonion_sparse_e2m1_monarch_blocks_exact :
    (∀ a b c d : Int, IsScaledOrtho (quat4 a b c d) (a * a + b * b + c * c + d * d)) ∧
    (∀ c0 c1 c2 c3 c4 c5 c6 c7 : Int,
      IsScaledOrtho (oct8 c0 c1 c2 c3 c4 c5 c6 c7)
        (c0 * c0 + c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 + c5 * c5 + c6 * c6 + c7 * c7)) ∧
    (∀ s : Nat, 1 ≤ s → s ≤ 4 → IsOptimalSparseE2M1Block (sparseQuat4 s) s) ∧
    (∀ s : Nat, 1 ≤ s → s ≤ 8 → IsOptimalSparseE2M1Block (sparseOct8 s) s) ∧
    (IsOptimalSparseE2M1Block (sparseQuat4 3) 3 ∧
     IsOptimalSparseE2M1Block (sparseOct8 4) 4 ∧
     IsOptimalSparseE2M1Block (sparseOct8 7) 7 ∧
     ((4 + 4 : Nat) = 8 ∧ (8 : Rat) / 16 = 1 / 2) ∧
     ((7 + 4 : Nat) = 11 ∧ (16 - 11 : Rat) / 16 = 5 / 16) ∧
     (((1 : Rat) / 4) * ((1 : Rat) / 4) = 1 / 16) ∧
     (((1 : Rat) / 7) * ((1 : Rat) / 4) = 1 / 28)) := by
  refine ⟨quat4_scaled_ortho, oct8_scaled_ortho, sparseQuat4_optimal, sparseOct8_optimal,
          sparseQuat4_optimal 3 (by decide) (by decide),
          sparseOct8_optimal 4 (by decide) (by decide),
          sparseOct8_optimal 7 (by decide) (by decide),
          ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ?_, ?_⟩
  · apply rat_div_eq_of_cross (by decide) (by decide); grind
  · apply rat_div_eq_of_cross (by decide) (by decide); grind
  · rw [rat_div_mul_div (by decide) (by decide)]
    apply rat_div_eq_of_cross (by grind) (by decide); grind
  · rw [rat_div_mul_div (by decide) (by decide)]
    apply rat_div_eq_of_cross (by grind) (by decide); grind

end KroneckerCyclicFrustration
