/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SparseE2M1Rotations.Defs

/-!
# Trusted Challenge Statements (`sparse-e2m1-rotations`)

Universal and exact pure-`Init` Lean 4 statements for:
1. Doubly-2:4-sparse exact orthogonal factorization of all `2^(k+2) × 2^(k+2)` Walsh–Hadamard matrices.
2. Sharp single-2:4 coherence lower bound `(4m) * M^2 ≥ 2c` and exact attainment by `H_{2^k} ⊗ B1`.
3. Universal skew-conference orthogonality `(a I + C)^T (a I + C) = (a^2 + n - 1) I` and E2M1 membership.
4. Exact power-of-2 norm `Q32 = H_4 ⊗ (I_8 + 3 C_8)` (`c = 16^2 = 256`) and NVFP4 winner `Q16 = 4 I_16 + C_16` (`c = 31`).
5. Universal doubly-2:4-sparse E2M1-native Givens–Hadamard family `G_{4 * 2^k}(1, 2) = H_{2^k} ⊗ G_4(1, 2)`.
-/

namespace SparseE2M1Challenge

open SparseE2M1Rotations

/-- Theorem 1 (Universal Doubly-2:4-Sparse Walsh–Hadamard Factorization):
    For every `k : Nat`, `H_{2^(k+2)} = (H_{2^k} ⊗ B1)(I_{2^k} ⊗ B2)`, where both factors
    are doubly-2:4-sparse, ternary (`{-1, 0, 1}`), and exact integer orthogonal. -/
theorem walshHadamard_doubly24_factorization (k : Nat) :
    let Q1 := kron (walshHadamard k) B1
    let Q2 := kron (idMat (2 ^ k)) B2
    matMul Q1 Q2 = walshHadamardOf (2 ^ k * 4) ∧
    isDoubly24Sparse Q1 ∧
    isDoubly24Sparse Q2 ∧
    matEntriesIn isTernary Q1 ∧
    matEntriesIn isTernary Q2 ∧
    isOrthogonal Q1 (2 * ((2 ^ k : Nat) : Int)) ∧
    isOrthogonal Q2 2 := by
  sorry

/-- Theorem 2a (Universal Single-2:4 Coherence Lower Bound):
    For every `m ≥ 1`, `c M : Int` (`0 ≤ M`), and `(4m) × (4m)` row-2:4-sparse row-orthogonal
    integer matrix `Q` with `Q Q^T = c I` and `|Q_{ij}| ≤ M`, we have `2 c ≤ (4m) M^2`. -/
theorem single24_coherence_lower_bound (m : Nat) (hm : 1 ≤ m)
    (c M : Int) (hM : 0 ≤ M) (Q : IntMat (m * 4) (m * 4))
    (hsp : is24SparseRows Q)
    (horth : isRowOrthogonal Q c)
    (hbound : ∀ i j, -M ≤ Q i j ∧ Q i j ≤ M) :
    2 * c ≤ ((m * 4 : Nat) : Int) * (M * M) := by
  sorry

/-- Theorem 2b (Exact Attainment by Walsh Weighing Matrices):
    For every `k : Nat`, `W_{4 * 2^k} = H_{2^k} ⊗ B1` is doubly-2:4-sparse, orthogonal with
    `c = 2 * 2^k`, has entries in `[-1, 1]`, and attains exact equality `(4 * 2^k) * 1^2 = 2c`. -/
theorem walsh_weighing_attains_coherence_bound (k : Nat) :
    let W := kron (walshHadamard k) B1
    let c : Int := 2 * ((2 ^ k : Nat) : Int)
    isDoubly24Sparse W ∧
    isOrthogonal W c ∧
    isRowOrthogonal W c ∧
    (∀ i j, -1 ≤ W i j ∧ W i j ≤ 1) ∧
    ((2 ^ k * 4 : Nat) : Int) * (1 * 1) = 2 * c := by
  sorry

/-- Theorem 3 (Universal Skew-Conference E2M1 Orthogonality):
    For every `n : Nat`, skew-conference matrix `C` (`C^T = -C`, `C^T C = (n - 1) I`), and `a : Int`,
    `(a I + C)^T (a I + C) = (a^2 + n - 1) I`, and if `a ∈ 2*E2M1`, `diag(C) = 0`, and `C` is
    ternary, then `a I + C` has all entries in `2*E2M1`. -/
theorem skewConference_e2m1_orthogonal (n : Nat) (C : IntMat n n) (a : Int)
    (hskew : transpose C = negMat C)
    (hconf : matMul (transpose C) C = scaleMat ((n : Int) - 1) (idMat n)) :
    isOrthogonal (addMat (scaleMat a (idMat n)) C) (a * a + (n : Int) - 1) ∧
    (isDoubledE2M1 a → (∀ i, C i i = 0) → matEntriesIn isTernary C →
      matEntriesIn isDoubledE2M1 (addMat (scaleMat a (idMat n)) C)) := by
  sorry

/-- Theorem 4a (Exact Power-of-2 Dense E2M1-Native `32 × 32` Rotation):
    `Q32 = H_4 ⊗ (I_8 + 3 C_8)` satisfies `Q32^T Q32 = 16^2 I_32` with all entries in
    `{-3, -1, 1, 3} ⊂ 2*E2M1`. -/
theorem q32_pow2_e2m1_exact :
    isOrthogonal Q32 (16 * 16) ∧
    matEntriesIn (fun x => x = -3 ∨ x = -1 ∨ x = 1 ∨ x = 3) Q32 ∧
    matEntriesIn isDoubledE2M1 Q32 := by
  sorry

/-- Theorem 4b (Exact NVFP4 Winner `Q16 = 4 I_16 + C_16`):
    `Q16^T Q16 = 31 I_16` with all entries in `{-1, 1, 4} ⊂ 2*E2M1`. -/
theorem q16_skew41_e2m1_exact :
    isOrthogonal Q16 31 ∧
    matEntriesIn (fun x => x = -1 ∨ x = 1 ∨ x = 4) Q16 ∧
    matEntriesIn isDoubledE2M1 Q16 := by
  sorry

/-- Theorem 5 (Universal Doubly-2:4-Sparse E2M1-Native Givens–Hadamard Family):
    For every `k : Nat`, `G_{4 * 2^k}(1, 2) = H_{2^k} ⊗ G_4(1, 2)` is doubly-2:4-sparse,
    E2M1-native, and exact orthogonal with `G^T G = (5 * 2^k) I`. -/
theorem g4k_doubly24_e2m1_orthogonal (k : Nat) :
    let G := kron (walshHadamard k) G4_1_2
    isDoubly24Sparse G ∧
    matEntriesIn isDoubledE2M1 G ∧
    isOrthogonal G (5 * ((2 ^ k : Nat) : Int)) := by
  sorry

end SparseE2M1Challenge
