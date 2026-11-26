/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MhcSinkhornFp8

/-!
# Verified Solutions (`mhc-sinkhorn-fp8-bounds`)
-/

namespace MhcSinkhornFp8Challenge

open MhcSinkhornFp8

theorem sinkhorn_diagonal_scaling_invariance (n : Nat) (A : RatMat n) (d e : RatVec n)
    (hA : ∀ i j, (0 : Rat) < A i j) (hd : ∀ i, (0 : Rat) < d i) (he : ∀ j, (0 : Rat) < e j) :
    rowNorm (diagScaleLeft d (diagScaleRight A e)) = rowNorm (diagScaleRight A e) ∧
    rowNorm (diagScaleLeft d A) = rowNorm A ∧
    colNorm (diagScaleRight A e) = colNorm A :=
  MhcSinkhornFp8.sinkhorn_diagonal_scaling_invariance n A d e hA hd he

theorem antidiagonal_swamping_bf16_fp8_fixed_point :
    (∀ n : Nat, 2 ≤ n → n ≤ 16 →
      (∀ i : Fin n, hwRowSum bf16Format (bf16AntiDiag n) i = 0x3F80) ∧
      (∀ j : Fin n, hwColSum bf16Format (bf16AntiDiag n) j = 0x3F80) ∧
      (∀ T : Nat, sinkhornModeAIter bf16Format T (bf16AntiDiag n) = bf16AntiDiag n) ∧
      normSq (onesVec n) < normSq (matVecMul (bitsMatToRat bf16Format (bf16AntiDiag n)) (onesVec n)) ∧
      (∀ L : Nat,
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 16384)) L *
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 16384)) L * normSq (onesVec n) ≤
        normSq (vecApplyIter (bitsMatToRat bf16Format (bf16AntiDiag n)) L (onesVec n)))) ∧
    (rowSum (bitsMatToRat bf16Format (bf16AntiDiag 4)) ⟨3, by omega⟩ = 259 / 256 ∧
     colSum (bitsMatToRat bf16Format (bf16AntiDiag 4)) ⟨3, by omega⟩ = 259 / 256 ∧
     rowSum (bitsMatToRat bf16Format (bf16AntiDiag 8)) ⟨7, by omega⟩ = 263 / 256 ∧
     colSum (bitsMatToRat bf16Format (bf16AntiDiag 8)) ⟨7, by omega⟩ = 263 / 256 ∧
     rowSum (bitsMatToRat bf16Format (bf16AntiDiag 16)) ⟨15, by omega⟩ = 271 / 256 ∧
     colSum (bitsMatToRat bf16Format (bf16AntiDiag 16)) ⟨15, by omega⟩ = 271 / 256) ∧
    (∀ n : Nat, 2 ≤ n → n ≤ 16 →
      (∀ i : Fin n, hwRowSum fp8Format (fp8AntiDiag n) i = 0x38) ∧
      (∀ j : Fin n, hwColSum fp8Format (fp8AntiDiag n) j = 0x38) ∧
      (∀ T : Nat, sinkhornModeAIter fp8Format T (fp8AntiDiag n) = fp8AntiDiag n) ∧
      normSq (onesVec n) < normSq (matVecMul (bitsMatToRat fp8Format (fp8AntiDiag n)) (onesVec n)) ∧
      (∀ L : Nat,
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 512)) L *
        ratPow (1 + ((n - 1 : Nat) : Rat) * ((1 : Rat) / 512)) L * normSq (onesVec n) ≤
        normSq (vecApplyIter (bitsMatToRat fp8Format (fp8AntiDiag n)) L (onesVec n)))) ∧
    (rowSum (bitsMatToRat fp8Format (fp8AntiDiag 4)) ⟨3, by omega⟩ = 19 / 16 ∧
     colSum (bitsMatToRat fp8Format (fp8AntiDiag 4)) ⟨3, by omega⟩ = 19 / 16 ∧
     rowSum (bitsMatToRat fp8Format (fp8AntiDiag 8)) ⟨7, by omega⟩ = 23 / 16 ∧
     colSum (bitsMatToRat fp8Format (fp8AntiDiag 8)) ⟨7, by omega⟩ = 23 / 16 ∧
     rowSum (bitsMatToRat fp8Format (fp8AntiDiag 16)) ⟨15, by omega⟩ = 31 / 16 ∧
     colSum (bitsMatToRat fp8Format (fp8AntiDiag 16)) ⟨15, by omega⟩ = 31 / 16) :=
  MhcSinkhornFp8.antidiagonal_swamping_bf16_fp8_fixed_point

theorem fp8_support_collapse_sqrt_n_minus_1_fixed_point :
    let v4 : RatVec 4 := fun i => if i.val = 0 ∨ i.val = 2 then 1 else 0
    sinkhornStep collapseMat4 = collapseMat4 ∧
    (normSq v4 = 2 ∧ normSq (matVecMul collapseMat4 v4) = 2 * normSq v4) ∧
    (∀ u : RatVec 4, normSq (matVecMul collapseMat4 u) ≤ 2 * normSq u) ∧
    (normSq (vecApplyIter (matMul (matTranspose collapseMat4) collapseMat4) 64 v4) =
      ratPow 2 128 * normSq v4) ∧
    (∀ n : Nat, 3 ≤ n →
      sinkhornStep (collapseMatGen n) = collapseMatGen n ∧
      (∀ u : RatVec n, normSq (matVecMul (collapseMatGen n) u) ≤ ((n - 1 : Nat) : Rat) * normSq u) ∧
      (∃ v : RatVec n, (0 : Rat) < normSq v ∧
        normSq (matVecMul (collapseMatGen n) v) = ((n - 1 : Nat) : Rat) * normSq v)) :=
  MhcSinkhornFp8.fp8_support_collapse_sqrt_n_minus_1_fixed_point

theorem mode_b_exact_sum_symmetric_overshoot_fixed_point :
    let H_fp8 := bitsMatToRat fp8Format fp8ModeBFixed4
    let H_bf16 := bitsMatToRat bf16Format bf16ModeBFixed4
    (∀ T : Nat, sinkhornModeBIter fp8Format T fp8ModeBFixed4 = fp8ModeBFixed4) ∧
    (∀ L : Nat, normSq (vecApplyIter H_fp8 L (onesVec 4)) =
      ratPow (527 / 512) L * ratPow (527 / 512) L * normSq (onesVec 4)) ∧
    (∀ u : RatVec 4, normSq (matVecMul H_fp8 u) ≤ (527 / 512) * (527 / 512) * normSq u) ∧
    ((40 : Rat) < ratPow (527 / 512) 128) ∧
    (∀ T : Nat, sinkhornModeBIter bf16Format T bf16ModeBFixed4 = bf16ModeBFixed4) ∧
    (∀ L : Nat, normSq (vecApplyIter H_bf16 L (onesVec 4)) =
      ratPow (131327 / 131072) L * ratPow (131327 / 131072) L * normSq (onesVec 4)) ∧
    (∀ u : RatVec 4, normSq (matVecMul H_bf16 u) ≤ (131327 / 131072) * (131327 / 131072) * normSq u) ∧
    ((32 / 25 : Rat) < ratPow (131327 / 131072) 128) :=
  MhcSinkhornFp8.mode_b_exact_sum_symmetric_overshoot_fixed_point

theorem sinkhorn_interstream_contraction_bound (n : Nat) (H : RatMat n) (ε : Rat)
    (hH : isDoublyStochastic H) (hmin : ∀ i j, ε ≤ H i j)
    (v : RatVec n) (hv : sumFinRat n v = 0) :
    normSq (matVecMul H v) ≤ (1 - (n : Rat) * ε) * (1 - (n : Rat) * ε) * normSq v ∧
    ∀ (L : Nat),
      normSq (vecApplyIter H L v) ≤
        ratPow (1 - (n : Rat) * ε) L * ratPow (1 - (n : Rat) * ε) L * normSq v :=
  MhcSinkhornFp8.sinkhorn_interstream_contraction_bound n H ε hH hmin v hv

theorem dyadic_orthogonal_zero_division_mixers_exact :
    (∀ a b c d : Rat, a * a + b * b + c * c + d * d = 4 → isOrthogonalRat (quatMixer4 a b c d)) ∧
    isOrthogonalRat hadamardMixer4 ∧
    (∀ s : Fin 4 → Rat, (∀ j, s j * s j = 1) → isOrthogonalRat (signedHadamard4 s)) ∧
    (∀ v : RatVec 8, normSq v = 16 → isOrthogonalRat (householder8 v)) ∧
    (let v8 : RatVec 8 := fun i => if i.val = 0 then 3 else 1
     normSq v8 = 16 ∧ isOrthogonalRat (householder8 v8)) ∧
    (∀ (n : Nat) (Q : RatMat n), isOrthogonalRat Q →
      (∀ v : RatVec n, normSq (matVecMul Q v) = normSq v) ∧
      (∀ (L : Nat) (v : RatVec n), normSq (vecApplyIter Q L v) = normSq v)) ∧
    (∀ (n : Nat) (Qs : List (RatMat n)), (∀ Q ∈ Qs, isOrthogonalRat Q) →
      ∀ v : RatVec n, normSq (applyLayerList Qs v) = normSq v) :=
  MhcSinkhornFp8.dyadic_orthogonal_zero_division_mixers_exact

end MhcSinkhornFp8Challenge
