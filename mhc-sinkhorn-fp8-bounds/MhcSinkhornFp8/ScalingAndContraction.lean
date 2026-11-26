/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MhcSinkhornFp8.RatLinAlg

/-!
# Theorems 1 & 5: Exact Rational Diagonal Scaling Invariance & Inter-Stream Contraction

1. `sinkhorn_diagonal_scaling_invariance`:
   For all `n : Nat`, positive `A : RatMat n`, and positive diagonal scales `d e : RatVec n`:
   - `rowNorm (diagScaleLeft d (diagScaleRight A e)) = rowNorm (diagScaleRight A e)`
   - `rowNorm (diagScaleLeft d A) = rowNorm A`
   - `colNorm (diagScaleRight A e) = colNorm A`

5. `sinkhorn_interstream_contraction_bound`:
   For all `n : Nat`, doubly-stochastic `H : RatMat n`, and `ε ≥ 0` with `∀ i j, ε ≤ H i j`:
   - `∀ v : RatVec n`, `sumFinRat n v = 0 → normSq (matVecMul H v) ≤ (1 - n * ε)^2 * normSq v`
   - And for ALL depths `L : Nat`:
     `normSq (vecApplyIter H L v) ≤ ((1 - n * ε)^L)^2 * normSq v`.
-/

namespace MhcSinkhornFp8

/-! ### Theorem 1: Exact Rational Diagonal Scaling Invariance -/

theorem rowNorm_diagScaleLeft {n : Nat} (A : RatMat n) (d : RatVec n)
    (hA : ∀ i j, (0 : Rat) < A i j) (hd : ∀ i, (0 : Rat) < d i) :
    rowNorm (diagScaleLeft d A) = rowNorm A := by
  funext i j
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hn : 0 < m + 1 := Nat.succ_pos m
    have hsA : (0 : Rat) < rowSum A i := sumFinRat_pos_of_all_pos hn (fun k => hA i k)
    have hsA_ne : rowSum A i ≠ 0 := Rat.ne_of_gt hsA
    have hdi_ne : d i ≠ 0 := Rat.ne_of_gt (hd i)
    have hsL : rowSum (diagScaleLeft d A) i = d i * rowSum A i := by
      simp only [rowSum, diagScaleLeft]
      exact sumFinRat_mul_left (d i) (fun k => A i k)
    have hsL_ne : rowSum (diagScaleLeft d A) i ≠ 0 := by
      rw [hsL]
      exact Rat.ne_of_gt (rat_mul_pos (hd i) hsA)
    simp only [rowNorm, diagScaleLeft, hsL_ne, hsA_ne, ↓reduceIte]
    rw [hsL]
    exact rat_mul_div_mul_left hdi_ne hsA_ne

theorem colNorm_diagScaleRight {n : Nat} (A : RatMat n) (e : RatVec n)
    (hA : ∀ i j, (0 : Rat) < A i j) (he : ∀ j, (0 : Rat) < e j) :
    colNorm (diagScaleRight A e) = colNorm A := by
  funext i j
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hn : 0 < m + 1 := Nat.succ_pos m
    have hsA : (0 : Rat) < colSum A j := sumFinRat_pos_of_all_pos hn (fun k => hA k j)
    have hsA_ne : colSum A j ≠ 0 := Rat.ne_of_gt hsA
    have hej_ne : e j ≠ 0 := Rat.ne_of_gt (he j)
    have hsR : colSum (diagScaleRight A e) j = colSum A j * e j := by
      simp only [colSum, diagScaleRight]
      exact sumFinRat_mul_right (fun k => A k j) (e j)
    have hsR_ne : colSum (diagScaleRight A e) j ≠ 0 := by
      rw [hsR]
      exact Rat.ne_of_gt (rat_mul_pos hsA (he j))
    simp only [colNorm, diagScaleRight, hsR_ne, hsA_ne, ↓reduceIte]
    rw [hsR]
    exact rat_mul_div_mul_right hej_ne hsA_ne

theorem sinkhorn_diagonal_scaling_invariance (n : Nat) (A : RatMat n) (d e : RatVec n)
    (hA : ∀ i j, (0 : Rat) < A i j) (hd : ∀ i, (0 : Rat) < d i) (he : ∀ j, (0 : Rat) < e j) :
    rowNorm (diagScaleLeft d (diagScaleRight A e)) = rowNorm (diagScaleRight A e) ∧
    rowNorm (diagScaleLeft d A) = rowNorm A ∧
    colNorm (diagScaleRight A e) = colNorm A := by
  have hAe : ∀ i j, (0 : Rat) < diagScaleRight A e i j := fun i j => rat_mul_pos (hA i j) (he j)
  exact ⟨rowNorm_diagScaleLeft (diagScaleRight A e) d hAe hd,
         rowNorm_diagScaleLeft A d hA hd,
         colNorm_diagScaleRight A e hA he⟩

/-! ### Theorem 5: Universal Doubly-Stochastic Inter-Stream Contraction -/

/-- Any doubly-stochastic matrix is non-expansive in Euclidean norm: `‖M v‖_2^2 ≤ ‖v‖_2^2`. -/
theorem doubly_stochastic_normSq_le {n : Nat} (M : RatMat n)
    (hM : isDoublyStochastic M) (v : RatVec n) :
    normSq (matVecMul M v) ≤ normSq v := by
  rcases hM with ⟨hnn, hrow, hcol⟩
  have hrow_sq : ∀ i : Fin n,
      matVecMul M v i * matVecMul M v i ≤ sumFinRat n (fun j => M i j * (v j * v j)) := by
    intro i
    have hcs := weighted_cauchy_schwarz (fun j => M i j) v (fun j => hnn i j)
    have hr : sumFinRat n (fun j => M i j) = 1 := hrow i
    rw [hr, Rat.one_mul] at hcs
    exact hcs
  have hsum_le : normSq (matVecMul M v) ≤
      sumFinRat n (fun i => sumFinRat n (fun j => M i j * (v j * v j))) :=
    sumFinRat_le hrow_sq
  have hswap : sumFinRat n (fun i => sumFinRat n (fun j => M i j * (v j * v j))) = normSq v := by
    rw [sumFinRat_swap]
    simp only [normSq]
    apply sumFinRat_congr
    intro j
    rw [sumFinRat_mul_right (fun i => M i j) (v j * v j)]
    have hc : sumFinRat n (fun i => M i j) = 1 := hcol j
    rw [hc, Rat.one_mul]
  rw [hswap] at hsum_le
  exact hsum_le

/-- Doubly-stochastic matrices preserve the zero-sum inter-stream subspace `V_⊥`. -/
theorem doubly_stochastic_preserves_zero_sum {n : Nat} (H : RatMat n)
    (hH : isDoublyStochastic H) (v : RatVec n) (hv : sumFinRat n v = 0) :
    sumFinRat n (matVecMul H v) = 0 := by
  rcases hH with ⟨_, _, hcol⟩
  unfold matVecMul
  rw [sumFinRat_swap]
  have hterm : ∀ j : Fin n, sumFinRat n (fun i => H i j * v j) = v j := by
    intro j
    rw [sumFinRat_mul_right (fun i => H i j) (v j)]
    have hc : sumFinRat n (fun i => H i j) = 1 := hcol j
    rw [hc, Rat.one_mul]
  rw [sumFinRat_congr hterm]
  exact hv

/-- Single-layer inter-stream contraction:
    for any doubly-stochastic `H` with `∀ i j, ε ≤ H i j` and any `v ∈ V_⊥`,
    `‖H v‖_2^2 ≤ (1 - n ε)^2 ‖v‖_2^2`. -/
theorem interstream_contraction_one_step {n : Nat} (H : RatMat n) (ε : Rat)
    (hH : isDoublyStochastic H) (hmin : ∀ i j, ε ≤ H i j)
    (v : RatVec n) (hv : sumFinRat n v = 0) :
    normSq (matVecMul H v) ≤ (1 - (n : Rat) * ε) * (1 - (n : Rat) * ε) * normSq v := by
  cases n with
  | zero =>
    change (0 : Rat) ≤ (1 - ((0 : Nat) : Rat) * ε) * (1 - ((0 : Nat) : Rat) * ε) * 0
    have : (1 - ((0 : Nat) : Rat) * ε) * (1 - ((0 : Nat) : Rat) * ε) * 0 = 0 := by grind
    rw [this]; exact Rat.le_refl
  | succ m =>
    rcases hH with ⟨hnn, hrow, hcol⟩
    let c : Rat := 1 - ((m + 1 : Nat) : Rat) * ε
    have hc_nonneg : (0 : Rat) ≤ c := by
      have i0 : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
      have hle : sumFinRat (m + 1) (fun _ => ε) ≤ sumFinRat (m + 1) (fun j => H i0 j) :=
        sumFinRat_le (fun j => hmin i0 j)
      rw [sumFinRat_const] at hle
      have hr : sumFinRat (m + 1) (fun j => H i0 j) = 1 := hrow i0
      rw [hr] at hle
      exact rat_sub_nonneg hle
    by_cases hc0 : c = 0
    · have hH_eq : ∀ i j : Fin (m + 1), H i j = ε := by
        intro i
        have hdiff_nn : ∀ j : Fin (m + 1), (0 : Rat) ≤ H i j - ε :=
          fun j => rat_sub_nonneg (hmin i j)
        have hdiff_sum : sumFinRat (m + 1) (fun j => H i j - ε) = 0 := by
          rw [sumFinRat_sub, sumFinRat_const]
          have hr : sumFinRat (m + 1) (fun j => H i j) = 1 := hrow i
          rw [hr]; exact hc0
        intro j
        have hz := sumFinRat_eq_zero_of_nonneg hdiff_nn hdiff_sum j
        grind
      have hHv0 : ∀ i : Fin (m + 1), matVecMul H v i = 0 := by
        intro i
        simp only [matVecMul]
        have hcongr : ∀ j, H i j * v j = ε * v j := fun j => by rw [hH_eq i j]
        rw [sumFinRat_congr hcongr, sumFinRat_mul_left, hv]
        grind
      have hns0 : normSq (matVecMul H v) = 0 := by
        simp only [normSq]
        have h0 : ∀ i, matVecMul H v i * matVecMul H v i = 0 := fun i => by rw [hHv0 i]; grind
        rw [sumFinRat_congr h0, sumFinRat_zero]
      rw [hns0]
      change (0 : Rat) ≤ c * c * normSq v
      rw [hc0]; grind
    · have hc_pos : (0 : Rat) < c := Rat.lt_of_le_of_ne hc_nonneg (Ne.symm hc0)
      let M : RatMat (m + 1) := fun i j => (H i j - ε) / c
      have hM_ds : isDoublyStochastic M := by
        refine ⟨?_, ?_, ?_⟩
        · intro i j
          exact rat_div_nonneg (rat_sub_nonneg (hmin i j)) hc_pos
        · intro i
          simp only [rowSum, M]
          rw [sumFinRat_div_right, sumFinRat_sub, sumFinRat_const]
          have hr : sumFinRat (m + 1) (fun j => H i j) = 1 := hrow i
          rw [hr]
          exact rat_div_self hc0
        · intro j
          simp only [colSum, M]
          rw [sumFinRat_div_right, sumFinRat_sub, sumFinRat_const]
          have hc_col : sumFinRat (m + 1) (fun i => H i j) = 1 := hcol j
          rw [hc_col]
          exact rat_div_self hc0
      have hHv_eq : ∀ i : Fin (m + 1), matVecMul H v i = c * matVecMul M v i := by
        intro i
        simp only [matVecMul, M]
        have hdecomp : ∀ j : Fin (m + 1), H i j * v j = c * (((H i j - ε) / c) * v j) + ε * v j := by
          intro j
          have hmul : c * ((H i j - ε) / c) = H i j - ε := by
            rw [Rat.mul_comm]
            exact rat_div_mul_cancel hc0
          have hmul2 : c * (((H i j - ε) / c) * v j) = (c * ((H i j - ε) / c)) * v j := by grind
          rw [hmul2, hmul]; grind
        rw [sumFinRat_congr hdecomp, sumFinRat_add, sumFinRat_mul_left, sumFinRat_mul_left, hv]
        grind
      have hns_eq : normSq (matVecMul H v) = c * c * normSq (matVecMul M v) := by
        simp only [normSq]
        have hterm : ∀ i, matVecMul H v i * matVecMul H v i =
            (c * c) * (matVecMul M v i * matVecMul M v i) := by
          intro i; rw [hHv_eq i]; grind
        rw [sumFinRat_congr hterm, sumFinRat_mul_left]
      rw [hns_eq]
      exact rat_mul_le_mul_of_nonneg_left (doubly_stochastic_normSq_le M hM_ds v)
        (Rat.mul_nonneg hc_nonneg hc_nonneg)

/-- Theorem 5 (Universal Inter-Stream Contraction Bound, 1-step and arbitrary depth `L`):
    For any `n : Nat`, doubly-stochastic `H : RatMat n`, `ε : Rat` with `∀ i j, ε ≤ H i j`,
    and any `v : RatVec n` in `V_⊥ = {v : ∑_i v_i = 0}`:
    1. Single layer: `‖H v‖_2^2 ≤ (1 - n ε)^2 ‖v‖_2^2`.
    2. All depths `L`: `‖H^L v‖_2^2 ≤ ((1 - n ε)^L)^2 ‖v‖_2^2`. -/
theorem sinkhorn_interstream_contraction_bound (n : Nat) (H : RatMat n) (ε : Rat)
    (hH : isDoublyStochastic H) (hmin : ∀ i j, ε ≤ H i j)
    (v : RatVec n) (hv : sumFinRat n v = 0) :
    normSq (matVecMul H v) ≤ (1 - (n : Rat) * ε) * (1 - (n : Rat) * ε) * normSq v ∧
    ∀ (L : Nat),
      normSq (vecApplyIter H L v) ≤
        ratPow (1 - (n : Rat) * ε) L * ratPow (1 - (n : Rat) * ε) L * normSq v := by
  refine ⟨interstream_contraction_one_step H ε hH hmin v hv, ?_⟩
  have hiter : ∀ (L : Nat),
      sumFinRat n (vecApplyIter H L v) = 0 ∧
      normSq (vecApplyIter H L v) ≤
        ratPow (1 - (n : Rat) * ε) L * ratPow (1 - (n : Rat) * ε) L * normSq v := by
    intro L
    induction L with
    | zero =>
      simp only [vecApplyIter, ratPow]
      refine ⟨hv, ?_⟩
      have : (1 : Rat) * 1 * normSq v = normSq v := by grind
      rw [this]; exact Rat.le_refl
    | succ L ih =>
      rcases ih with ⟨hsumL, hnormL⟩
      simp only [vecApplyIter, ratPow]
      refine ⟨doubly_stochastic_preserves_zero_sum H hH _ hsumL, ?_⟩
      have hstep := interstream_contraction_one_step H ε hH hmin (vecApplyIter H L v) hsumL
      have hsq_nn : (0 : Rat) ≤ (1 - (n : Rat) * ε) * (1 - (n : Rat) * ε) :=
        rat_sq_nonneg (1 - (n : Rat) * ε)
      have hmul := rat_mul_le_mul_of_nonneg_left hnormL hsq_nn
      have hcomb := Rat.le_trans hstep hmul
      have hrew : (1 - (n : Rat) * ε) * (1 - (n : Rat) * ε) *
          (ratPow (1 - (n : Rat) * ε) L * ratPow (1 - (n : Rat) * ε) L * normSq v) =
          (1 - (n : Rat) * ε) * ratPow (1 - (n : Rat) * ε) L *
          ((1 - (n : Rat) * ε) * ratPow (1 - (n : Rat) * ε) L) * normSq v := by grind
      rw [hrew] at hcomb
      exact hcomb
  intro L
  exact (hiter L).2

end MhcSinkhornFp8
