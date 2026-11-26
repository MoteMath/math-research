/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FanoSparse24Perm

/-!
# Verified Solutions (`fano-sparse24-perm`)
-/

namespace FanoSparse24PermChallenge

open FanoSparse24Perm

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
     ef21Alpha 1 4 = 1 / 4 ∧ ef21Alpha 2 8 = 1 / 4) :=
  FanoSparse24Perm.structured_topk_ef21_contraction_exact

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
    ternaryDenseAlpha 32 = 4 / 35 :=
  FanoSparse24Perm.mxfp4_anchor_dilution_48_beats_24_exact

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
     ¬ rowsFeasible8 fanoLines8) :=
  FanoSparse24Perm.fano_plane_sparse24_obstruction_exact

theorem sunflower_sparse24_obstruction_exact :
    (allQuads8.length = 70 ∧
     ∀ r : Nat, r ∈ allQuads8 →
       (allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 17) ∧
    (∀ rows : List Nat, (∀ r : Nat, r ∈ rows → r ∈ allQuads8) →
      rows.length ≤ 3 → rowsFeasible8 rows) ∧
    (sunflowerRows8.length = 4 ∧
     (∀ r : Nat, r ∈ sunflowerRows8 → r ∈ allQuads8) ∧
     ¬ rowsFeasible8 sunflowerRows8) :=
  FanoSparse24Perm.sunflower_sparse24_obstruction_exact

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
       (12099837073 / 58312286604 : Rat) < 2076 / 10000) :=
  FanoSparse24Perm.order_statistic_k2k_nmse_laws_exact

end FanoSparse24PermChallenge
