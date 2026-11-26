/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FanoSparse24Perm.Defs

/-!
# Trusted Challenge Statements (`fano-sparse24-perm`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Universal structured Top-`k` EF21 contraction `α(k:m) = k / m` (`1/2` for `2:4`, `4:8`, `8:16`;
   `1/4` for `1:4`, `2:8`) with multi-block lift and exact flat-block tightness.
2. Joint `k:m + MXFP4` (`B = 32`, E8M0 `M_eff = 3`) exact worst-case EF21 contraction proving
   `4:8 + MXFP4` (`18/37`) strictly beats `2:4 + MXFP4` (`72/151`) via anchor-group dilution
   (`8/32` vs `4/32`), plus the exact closed-form dense Ternary contraction law `4 / (B + 3)`.
3. Universal first-moment lower bound `R_crit(C, 3) ≥ ⌈(4C - 1)(4C - 2) / 6⌉` and exact Fano plane
   `PG(2, 2)` `2:4` column-permutation obstruction (`R_crit(2, 3) = 7`, `7 × 5 = 35` pairwise-disjoint kills).
4. Exact 3-column sunflower `2:4` obstruction (`R_crit(2, 4) = 4`): every `≤ 3` weight-4 rows on
   `8` columns admit a `2:4`-feasible `(4, 4)`-bipartition, while `4` sunflower rows kill all `35`.
5. Exact rational Uniform and Laplace `k:2k` order-statistic NMSE gain laws (`4:8` vs `2:4` = `-1/6`
   Uniform, `-33489/112700 ≈ -29.72%` Laplace; `8:16` vs `4:8` = `-2/17` Uniform,
   `-12099837073/58312286604 ≈ -20.75%` Laplace).
-/

namespace FanoSparse24PermChallenge

open FanoSparse24Perm

/-- Theorem 1 (Universal Structured Top-`k` EF21 Contraction `α(k:m) = k / m`):
    For all `1 ≤ k ≤ m`, proves exact energy decomposition and contraction
    `blockPrunedErr k m a ≤ (1 - k / m) * blockEnergy m a` per block and across `g` disjoint blocks,
    exact tightness via flat blocks `a i = c > 0`, and exact instantiations for
    `2:4`, `4:8`, `8:16` (`1/2`) and `1:4`, `2:8` (`1/4`). -/
theorem structured_topk_ef21_contraction_exact :
    (∀ (k m : Nat) (a : Nat → Rat), 1 ≤ k → k ≤ m → NonIncreasingMags m a →
      blockEnergy m a = blockKeptEnergy k a + blockPrunedErr k m a ∧
      blockPrunedErr k m a ≤ (1 - ef21Alpha k m) * blockEnergy m a) ∧
    (∀ (g k m : Nat) (x : Nat → Nat → Rat), 1 ≤ k → k ≤ m →
      (∀ r : Nat, r < g → NonIncreasingMags m (x r)) →
      sumRange g (fun r => blockPrunedErr k m (x r)) ≤
        (1 - ef21Alpha k m) * sumRange g (fun r => blockEnergy m (x r))) ∧
    (∀ (k m : Nat) (c : Rat), 1 ≤ k → k ≤ m → (0 : Rat) < c →
      NonIncreasingMags m (fun _ => c) ∧
      (0 : Rat) < blockEnergy m (fun _ => c) ∧
      1 - blockPrunedErr k m (fun _ => c) / blockEnergy m (fun _ => c) = ef21Alpha k m) ∧
    (ef21Alpha 2 4 = 1 / 2 ∧ ef21Alpha 4 8 = 1 / 2 ∧ ef21Alpha 8 16 = 1 / 2 ∧
     ef21Alpha 1 4 = 1 / 4 ∧ ef21Alpha 2 8 = 1 / 4) := by
  sorry

/-- Theorem 2 (Joint `k:m + MXFP4` (`B = 32`) Worst-Case EF21 Contraction & Anchor-Group Dilution):
    Proves universally over all rational blocks `x ∈ [0, 3]^{32}` with anchor `x 0 0 = 3` that
    `4:8 + MXFP4` achieves exact contraction `18/37`, `2:4 + MXFP4` achieves exact contraction `72/151`,
    both attained by explicit witnesses, with strict anchor-group dilution advantage
    `72/151 < 18/37` (gap `54/5587`), plus the exact closed-form dense Ternary law `4 / (B + 3)`
    for all `B ≥ 1` (`4/35` at `B = 32`). -/
theorem mxfp4_anchor_dilution_48_beats_24_exact :
    (∀ x : Nat → Nat → Rat, ValidMxfp4Block 4 8 x →
      blockMxfp4ErrSq 4 4 8 x ≤ (1 - 18 / 37) * blockMxfp4Energy 4 8 x) ∧
    (∃ x : Nat → Nat → Rat, ValidMxfp4Block 4 8 x ∧
      blockMxfp4ErrSq 4 4 8 x = 114 ∧ blockMxfp4Energy 4 8 x = 222 ∧
      1 - blockMxfp4ErrSq 4 4 8 x / blockMxfp4Energy 4 8 x = 18 / 37) ∧
    (∀ x : Nat → Nat → Rat, ValidMxfp4Block 8 4 x →
      blockMxfp4ErrSq 8 2 4 x ≤ (1 - 72 / 151) * blockMxfp4Energy 8 4 x) ∧
    (∃ x : Nat → Nat → Rat, ValidMxfp4Block 8 4 x ∧
      blockMxfp4ErrSq 8 2 4 x = 79 / 4 ∧ blockMxfp4Energy 8 4 x = 151 / 4 ∧
      1 - blockMxfp4ErrSq 8 2 4 x / blockMxfp4Energy 8 4 x = 72 / 151) ∧
    ((72 / 151 : Rat) < 18 / 37 ∧ (18 / 37 : Rat) - 72 / 151 = 54 / 5587) ∧
    (∀ (B : Nat) (x : Nat → Rat), 1 ≤ B → x 0 = 1 →
      (∀ i : Nat, i < B → (0 : Rat) ≤ x i ∧ x i ≤ 1) →
      sumRange B (fun i => ternaryErrSq (x i)) ≤
        (1 - ternaryDenseAlpha B) * sumRange B (fun i => x i * x i)) ∧
    (∀ B : Nat, 1 ≤ B →
      ∃ x : Nat → Rat, x 0 = 1 ∧
        (∀ i : Nat, i < B → (0 : Rat) ≤ x i ∧ x i ≤ 1) ∧
        sumRange B (fun i => ternaryErrSq (x i)) =
          (1 - ternaryDenseAlpha B) * sumRange B (fun i => x i * x i)) ∧
    ternaryDenseAlpha 32 = 4 / 35 := by
  sorry

/-- Theorem 3 (Exact Fano Plane `2:4` Column-Permutation Obstruction `R_crit(2, 3) = 7`):
    Proves the universal first-moment ceiling lower bound `⌈(4C - 1)(4C - 2) / 6⌉` for all `C ≥ 1`,
    that every weight-3 row on `8` columns kills exactly `5` of the `35` `(4, 4)`-bipartitions so
    every `≤ 6` weight-3 rows admit a `2:4`-feasible bipartition, and that the `7` lines of the
    Fano plane `PG(2, 2)` intersect pairwise in `1` column and kill `7 × 5 = 35` pairwise-disjoint
    bipartitions simultaneously. -/
theorem fano_plane_sparse24_obstruction_exact :
    (∀ C : Nat, 1 ≤ C →
      (4 * C - 1) * (4 * C - 2) ≤ 6 * rCritLowerBound3 C ∧
      ∀ R : Nat, R < rCritLowerBound3 C → 6 * R < (4 * C - 1) * (4 * C - 2)) ∧
    (rCritLowerBound3 1 = 1 ∧ rCritLowerBound3 2 = 7 ∧ rCritLowerBound3 3 = 19 ∧
     rCritLowerBound3 4 = 35 ∧ rCritLowerBound3 8 = 155 ∧
     rCritLowerBound3 16 = 651 ∧ rCritLowerBound3 32 = 2667) ∧
    (allBipartitions8.length = 35 ∧ allTriples8.length = 56 ∧
     ∀ r : Nat, r ∈ allTriples8 →
       (allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 5) ∧
    (∀ rows : List Nat, (∀ r : Nat, r ∈ rows → r ∈ allTriples8) →
      rows.length ≤ 6 → rowsFeasible8 rows) ∧
    (fanoLines8.length = 7 ∧
     (∀ r : Nat, r ∈ fanoLines8 → r ∈ allTriples8) ∧
     (∀ i j : Nat, i < 7 → j < 7 → i ≠ j →
       interCount8 (fanoLines8.getD i 0) (fanoLines8.getD j 0) = 1 ∧
       ∀ p : Nat, p ∈ allBipartitions8 →
         (!(bipartitionKilled p (fanoLines8.getD i 0) &&
            bipartitionKilled p (fanoLines8.getD j 0))) = true) ∧
     ¬ rowsFeasible8 fanoLines8) := by
  sorry

/-- Theorem 4 (Exact 3-Column Sunflower `2:4` Obstruction `R_crit(2, 4) = 4`):
    Proves that every weight-4 row on `8` columns kills exactly `17` of the `35` bipartitions,
    that every `≤ 3` weight-4 rows on `8` columns still admit a `2:4`-feasible `(4, 4)`-bipartition,
    and that the `4` sunflower rows sharing core `{0, 1, 2}` kill all `35` bipartitions simultaneously. -/
theorem sunflower_sparse24_obstruction_exact :
    (allQuads8.length = 70 ∧
     ∀ r : Nat, r ∈ allQuads8 →
       (allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 17) ∧
    (∀ rows : List Nat, (∀ r : Nat, r ∈ rows → r ∈ allQuads8) →
      rows.length ≤ 3 → rowsFeasible8 rows) ∧
    (sunflowerRows8.length = 4 ∧
     (∀ r : Nat, r ∈ sunflowerRows8 → r ∈ allQuads8) ∧
     ¬ rowsFeasible8 sunflowerRows8) := by
  sorry

/-- Theorem 5 (Exact Order-Statistic `k:2k` Gain Laws: Uniform & Laplace):
    Proves the universal closed-form Uniform `k:2k` NMSE `(k + 2) / (4 (2k + 1))` directly from
    the order-statistic sum for all `k ≥ 1`, its strict monotonicity, asymptotic floor `1/8`,
    and exact doubling gain `3k / ((k + 2)(4k + 1))` (`-1/6` for `4:8` vs `2:4`, `-2/17` for
    `8:16` vs `4:8`), together with exact Rényi Laplace `k:2k` NMSE values (`23/288` for `2:4`,
    `79211/1411200` for `4:8`, exact `-33489/112700 ≈ -29.72%` gain; `8:16` vs `4:8` =
    `-12099837073/58312286604 ≈ -20.75%`). -/
theorem order_statistic_k2k_nmse_laws_exact :
    (∀ k : Nat, 1 ≤ k →
      unifNMSEFromOrderStats k = unifNMSE k ∧
      unifNMSE (k + 1) < unifNMSE k ∧
      (1 / 8 : Rat) < unifNMSE k ∧
      1 - unifNMSE (2 * k) / unifNMSE k =
        ((3 * k : Nat) : Rat) / (((k + 2) * (4 * k + 1) : Nat) : Rat)) ∧
    (unifNMSE 1 = 1 / 4 ∧ unifNMSE 2 = 1 / 5 ∧ unifNMSE 4 = 1 / 6 ∧
     unifNMSE 8 = 5 / 34 ∧ unifNMSE 16 = 3 / 22 ∧
     1 - unifNMSE 4 / unifNMSE 2 = 1 / 6 ∧
     1 - unifNMSE 8 / unifNMSE 4 = 2 / 17) ∧
    (laplaceNMSE 1 = 1 / 8 ∧
     laplaceNMSE 2 = 23 / 288 ∧
     laplaceNMSE 4 = 79211 / 1411200 ∧
     laplaceNMSE 8 = 46212449531 / 1038874636800 ∧
     1 - laplaceNMSE 4 / laplaceNMSE 2 = 33489 / 112700 ∧
     (2971 / 10000 : Rat) < 33489 / 112700 ∧ (33489 / 112700 : Rat) < 2972 / 10000 ∧
     1 - laplaceNMSE 8 / laplaceNMSE 4 = 12099837073 / 58312286604 ∧
     (2075 / 10000 : Rat) < 12099837073 / 58312286604 ∧
       (12099837073 / 58312286604 : Rat) < 2076 / 10000) := by
  sorry

end FanoSparse24PermChallenge
