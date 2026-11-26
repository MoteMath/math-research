/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Paley32Mxfp4.Defs

/-!
# Trusted Challenge Statements (`paley32-mxfp4-outliers`)

Pure-`Init` (zero Mathlib) Lean 4 formalization of the six headline theorems from Wave 5A
(`w5-fp4-block-outliers`):
1. Universal real-orthogonal `k`-sparse PAPR lower bound (`≥ k/n`) and Hadamard flatness equality.
2. Paley-32 vs Sylvester-32 orthogonality, explicit Sylvester-32 8-spike collapse witness,
   and exhaustive `k = 4` zero-subgroup-collapse theorem (`maxC4 paley32 ≤ 5`, `1,240` Sylvester affine 2-planes).
3. Universal `k = 8` zero-collapse (`c_8 ≤ 3`) and exact `49/64` (`-23.4375%`) fourth-moment reduction
   (`12,544` vs `16,384`) for Paley-32 vs Sylvester-32.
4. Hall-16 Classes I–V orthogonality, exhaustive `k = 4` closed-quadruple counts (`140, 76, 44, 28, 28`),
   and exhaustive `k = 8` double-peak-8 duality separation (`30, 54, 90, 114, 156`).
5. 4-variable bent diagonal (`0x356`) anti-resonance flattening `80` of `140` Sylvester-16 affine 2-planes
   to exact PAPR = 1 (`|y_r| = 2` everywhere).
6. Exact OCP MXFP4 E8M0 bulk-crush threshold (`k^2 M^2 ≥ 576 (B - k)`, `B = 32, k = 4` witness `M^2 = 1008`)
   and Hybrid `k`-Split bit-budget dominance over MXFP6 (`k ≤ 3` at `B = 32`, `k ≤ 5` at `B = 64`).
-/

namespace Paley32Mxfp4Challenge

open Paley32Mxfp4

/-- Theorem 1 (Universal Orthogonal `k`-Sparse PAPR Lower Bound & Hadamard Flatness Equality):
    For every `n ≥ 1`, `1 ≤ k ≤ n`, and every scaled orthogonal matrix `U` (`U^T U = n I`, `U U^T = n I`):
    (a) There exists a row `i` and an injective `k`-support `S` with `∑_{t} U_{i, S(t)}^2 ≥ k`,
        giving a nonzero `k`-sparse vector `x` with `(U x)_i^2 ≥ k · ‖x‖_2^2` (i.e. PAPR `≥ k/n`
        for the orthonormal matrix `U / √n`).
    (b) For every `1 ≤ k < n`, `U` attains the universal lower bound `∑_{t} U_{i, S(t)}^2 ≤ k`
        on all rows and all injective `k`-supports if and only if `U` is flat (`U_{i, j}^2 = 1`
        for all `i, j`, i.e., a Hadamard matrix). -/
theorem universal_orthogonal_k_sparse_papr_lower_bound
    (n k : Nat) (hk1 : 1 ≤ k) (hkn : k ≤ n) (U : RatMat n n)
    (hUtU : isOrthogonalRat U (n : Rat))
    (hUUt : isOrthogonalRat (transposeRat U) (n : Rat)) :
    (∃ (i : Fin n) (S : Fin k → Fin n),
      isInjective S ∧
      (k : Rat) ≤ sumFinRat k (fun t => U i (S t) * U i (S t)) ∧
      ∃ x : Fin n → Rat,
        (∀ j : Fin n, (∀ t : Fin k, S t ≠ j) → x j = 0) ∧
        (0 : Rat) < sumSqRat x ∧
        (k : Rat) * sumSqRat x ≤ matVecRat U x i * matVecRat U x i) ∧
    (k < n →
      ((∀ (i : Fin n) (S : Fin k → Fin n), isInjective S →
          sumFinRat k (fun t => U i (S t) * U i (S t)) ≤ (k : Rat)) ↔
       (∀ i j : Fin n, U i j * U i j = 1))) := by
  sorry

/-- Theorem 2 (Paley-32 Orthogonality & Exhaustive `k = 4` Zero-Subgroup-Collapse):
    Both `paley32` and `sylvester32` satisfy exact orthogonality `H^T H = 32 I`.
    Sylvester-32 hits an explicit 8-spike collapse (`c_4 = 8`, `24` zeros, `ℓ_4^4 = 2,048`) on the
    affine 2-plane `{0, 1, 2, 3}`, and has exactly `1,240` affine 2-planes (`c_0 ⊕ c_1 ⊕ c_2 ⊕ c_3 = 0`),
    every one of which achieves `maxC4 sylvester32 = 8`.
    In contrast, over ALL `C(32, 4) = 35,960` 4-subsets, Paley-32 has ZERO `c_4 ≥ 6` collapses
    (`∀ c0 < c1 < c2 < c3, maxC4 paley32 c0 c1 c2 c3 ≤ 5`) and attains `maxC4 = 5`. -/
theorem paley32_orthogonality_and_zero_k4_collapse :
    isOrthogonal paley32 32 ∧
    isOrthogonal sylvester32 32 ∧
    (let y := matVec sylvester32 (supportVec [0, 1, 2, 3])
     countAbsEq y 4 = 8 ∧ countAbsEq y 0 = 24 ∧ sumFourthInt y = 2048) ∧
    countAffinePlanes32 = 1240 ∧
    (∀ c0 c1 c2 c3 : Fin 32, c0 < c1 → c1 < c2 → c2 < c3 →
      (c0.val ^^^ c1.val ^^^ c2.val ^^^ c3.val = 0) →
      maxC4 sylvester32 c0 c1 c2 c3 = 8) ∧
    (∀ c0 c1 c2 c3 : Fin 32, c0 < c1 → c1 < c2 → c2 < c3 →
      maxC4 paley32 c0 c1 c2 c3 ≤ 5) ∧
    (∃ c0 c1 c2 c3 : Fin 32, c0 < c1 ∧ c1 < c2 ∧ c2 < c3 ∧
      maxC4 paley32 c0 c1 c2 c3 = 5) := by
  sorry

/-- Theorem 3 (Paley-32 vs Sylvester-32 Universal `k = 8` Zero-Collapse & Exact `49/64` `ℓ_4^4` Reduction):
    On the affine 3-space `{0..7}`, Sylvester-32 suffers 4-spike collapse (`c_8 = 4`, `28` zeros,
    `ℓ_4^4 = 16,384`). For EVERY signed 8-sparse vector `x ∈ {-1, 0, 1}^{32}` (`|supp(x)| = 8`),
    Paley-32 has ZERO `c_8 ≥ 4` collapses (`countAbsEq (matVec paley32 x) 8 ≤ 3`) and satisfies
    the universal fourth-moment bound `sumFourthInt (matVec paley32 x) ≤ 12,544`, attained
    tightly on `{0, 1, 2, 3, 8, 19, 22, 30}` with exact reduction ratio `12544 / 16384 = 49 / 64`. -/
theorem paley32_vs_sylvester32_k8_l4_reduction :
    (let yS := matVec sylvester32 (supportVec [0, 1, 2, 3, 4, 5, 6, 7])
     countAbsEq yS 8 = 4 ∧ countAbsEq yS 0 = 28 ∧ sumFourthInt yS = 16384) ∧
    (∀ x : Fin 32 → Int, isSignedSparse 8 x →
      countAbsEq (matVec paley32 x) 8 ≤ 3 ∧
      sumFourthInt (matVec paley32 x) ≤ 12544) ∧
    (let yP := matVec paley32 (supportVec [0, 1, 2, 3, 8, 19, 22, 30])
     countAbsEq yP 8 = 3 ∧ sumFourthInt yP = 12544) ∧
    ((12544 : Rat) / 16384 = 49 / 64) := by
  sorry

/-- Theorem 4 (Hall-16 Five Equivalence Classes: Orthogonality & `k = 4` vs `k = 8` Duality Paradox):
    All five Hall (1961) equivalence classes satisfy `H^T H = 16 I`, have exact exhaustive `k = 4`
    closed-quadruple counts `140, 76, 44, 28, 28`, and exact exhaustive `k = 8` double-peak-8
    collapse subset counts `30, 54, 90, 114, 156` (characterizing `hasDoublePeak8Mask16` exactly
    via `rowPairMasks16`), strictly separating all five classes and exhibiting the `k = 4` vs `k = 8`
    duality inversion (`Hall_I` minimizes `k = 8` collapses while maximizing `k = 4` collapses, and
    `k = 8` separates `Hall_V` (`114`) from `Hall_IV` (`156`)). -/
theorem hall16_five_classes_orthogonality_and_k4_k8_duality :
    (isOrthogonal hall16_I 16 ∧ isOrthogonal hall16_II 16 ∧ isOrthogonal hall16_III 16 ∧
     isOrthogonal hall16_IV 16 ∧ isOrthogonal hall16_V 16) ∧
    (countClosedQuads16 hall16_I = 140 ∧
     countClosedQuads16 hall16_II = 76 ∧
     countClosedQuads16 hall16_III = 44 ∧
     countClosedQuads16 hall16_IV = 28 ∧
     countClosedQuads16 hall16_V = 28) ∧
    (∀ H : IntMat 16 16,
      (∀ r c : Fin 16, H r c = 1 ∨ H r c = -1) →
      isOrthogonal (transpose H) 16 →
      ∀ m : Nat, hasDoublePeak8Mask16 H m ↔ m ∈ rowPairMasks16 H) ∧
    (countDoublePeak8Subsets16 hall16_I = 30 ∧
     countDoublePeak8Subsets16 hall16_II = 54 ∧
     countDoublePeak8Subsets16 hall16_III = 90 ∧
     countDoublePeak8Subsets16 hall16_V = 114 ∧
     countDoublePeak8Subsets16 hall16_IV = 156) := by
  sorry

/-- Theorem 5 (4-Variable Bent Diagonal Anti-Resonance on Sylvester-16):
    Right-multiplying `sylvester16` by the 4-variable Boolean bent diagonal `bentDiag16` (`0x356`)
    preserves exact Hadamard orthogonality (`(H D)^T (H D) = 16 I`) while flattening exactly `80`
    of the `140` affine 2-planes in `𝔽_2^4` to exact PAPR = 1 (`|y_r| = 2` for all `r : Fin 16`),
    compared to `0` of `140` flattened for untwisted `sylvester16`. -/
theorem bent_diagonal_n16_anti_resonance_exact :
    isOrthogonal (diagTwist sylvester16 bentDiag16) 16 ∧
    affinePlanes16.length = 140 ∧
    countFlatAffinePlanes16 sylvester16 = 0 ∧
    countFlatAffinePlanes16 (diagTwist sylvester16 bentDiag16) = 80 := by
  sorry

/-- Theorem 6 (Exact OCP MXFP4 E8M0 Bulk-Crush Threshold & Hybrid `k`-Split Bit-Budget Dominance):
    (a) Universal bulk-crush threshold: for all `1 ≤ k < B`, `M ≥ 0`, and E8M0 scale `S ≥ (k : Rat) * M / 6`,
        `((k : Rat) * (k : Rat)) * (M * M) > 576 * ((B - k : Nat) : Rat)` forces the unit-RMS bulk energy
        `(B - k : Rat)` strictly below the E2M1 subnormal round-to-zero squared threshold `(S / 4)^2`,
        and at exact equality `k^2 M^2 = 576 (B - k)` with `S = k M / 6`, `(S / 4)^2 = B - k`.
    (b) Exact `B = 32, k = 4` witness: `576 * (32 - 4) / (4 * 4) = 1008` (`31^2 < 1008 < 32^2`).
    (c) Exact MXFP4 Hybrid `k`-Split bit-budget dominance over MXFP6 (`mxfp4HybridBits < mxfp6BlockBits`):
        holds iff `k ≤ 3` at `B = 32` (`b = 5`), iff `k ≤ 5` at `B = 64` (`b = 6`), and iff `k ≤ 1` at `B = 16` (`b = 4`). -/
theorem mxfp4_e8m0_bulk_crush_threshold_exact :
    (∀ (B k : Nat) (M S : Rat), 1 ≤ k → k < B → (0 : Rat) ≤ M →
      ((k : Rat) * M) / 6 ≤ S →
      (576 * ((B - k : Nat) : Rat) < ((k : Rat) * (k : Rat)) * (M * M) →
        ((B - k : Nat) : Rat) < (S / 4) * (S / 4)) ∧
      (((k : Rat) * (k : Rat)) * (M * M) = 576 * ((B - k : Nat) : Rat) →
        S = ((k : Rat) * M) / 6 →
        (S / 4) * (S / 4) = ((B - k : Nat) : Rat))) ∧
    ((576 * ((32 - 4 : Nat) : Rat)) / (4 * 4) = 1008 ∧
     (31 : Rat) * 31 < 1008 ∧ (1008 : Rat) < 32 * 32) ∧
    (∀ k : Nat, mxfp4HybridBits 32 k 5 < mxfp6BlockBits 32 ↔ k ≤ 3) ∧
    (∀ k : Nat, mxfp4HybridBits 64 k 6 < mxfp6BlockBits 64 ↔ k ≤ 5) ∧
    (∀ k : Nat, mxfp4HybridBits 16 k 4 < mxfp6BlockBits 16 ↔ k ≤ 1) := by
  sorry

end Paley32Mxfp4Challenge
