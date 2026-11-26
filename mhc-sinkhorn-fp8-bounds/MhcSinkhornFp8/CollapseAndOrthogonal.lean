/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MhcSinkhornFp8.RatLinAlg

/-!
# Theorems 3 & 6: Support-Collapse `√(n-1)` Fixed Points & Zero-Division Dyadic-Orthogonal Mixers

3. `fp8_support_collapse_sqrt_n_minus_1_fixed_point`:
   - GPU-discovered `n = 4` witness `collapseMat4`: exact rational fixed point of `sinkhornStep`,
     exact spectral norm squared `= 2` (both attainment and universal upper bound), and exact
     `L = 128` (`64` steps of `H^T H`) blowup `2^128 * ‖v‖_2^2` (`2^64×` norm amplification).
   - Universal `n ≥ 3` family `collapseMatGen n`: exact rational fixed point of `sinkhornStep`
     attaining exact spectral norm squared `= n - 1` (both attainment and universal upper bound).

6. `dyadic_orthogonal_zero_division_mixers_exact`:
   - Universal orthogonality-to-isometry lifting: `Q^T Q = I` implies `‖Q v‖_2^2 = ‖v‖_2^2`,
     `‖Q^L v‖_2^2 = ‖v‖_2^2` for all `L`, and `‖applyLayerList Qs v‖_2^2 = ‖v‖_2^2` for any list
     of orthogonal layer matrices.
   - `n = 4` Hamilton-Quaternion / Signed Hadamard mixers (`entries ±1/2`, exact `>> 1`).
   - `n = 8` dyadic Householder mixer `I_8 - (1/8) v v^T` for ANY `v` with `‖v‖_2^2 = 16`
     (exact `>> 3`, zero division).
-/

namespace MhcSinkhornFp8

/-! ### 1. Theorem 3: GPU-Discovered `n = 4` Witness & General `n ≥ 3` Support-Collapse Family -/

theorem collapseMat4_rowSum :
    rowSum collapseMat4 ⟨0, by omega⟩ = 1 ∧
    rowSum collapseMat4 ⟨1, by omega⟩ = (1 : Rat) / 2 ∧
    rowSum collapseMat4 ⟨2, by omega⟩ = (1 : Rat) / 2 ∧
    rowSum collapseMat4 ⟨3, by omega⟩ = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [rowSum, sumFinRat, collapseMat4, Fin.castSucc, Fin.last]; grind)

theorem rowNorm_collapseMat4 (i j : Fin 4) :
    rowNorm collapseMat4 i j =
    match i.val, j.val with
    | 0, 3 => 1
    | 1, 1 => 1
    | 2, 1 => 1
    | 3, 0 => (1 : Rat) / 2
    | 3, 2 => (1 : Rat) / 2
    | _, _ => 0 := by
  rcases collapseMat4_rowSum with ⟨hr0, hr1, hr2, hr3⟩
  have h1ne : (1 : Rat) ≠ 0 := by decide
  have h2ne : (2 : Rat) ≠ 0 := by decide
  have hhalf_ne : ((1 : Rat) / 2) ≠ 0 := Rat.ne_of_gt (rat_div_pos (by decide) (by decide))
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => simp only [rowNorm, hr0, h1ne, ↓reduceIte, collapseMat4]; grind
  | ⟨0, _⟩, ⟨1, _⟩ => simp only [rowNorm, hr0, h1ne, ↓reduceIte, collapseMat4]; grind
  | ⟨0, _⟩, ⟨2, _⟩ => simp only [rowNorm, hr0, h1ne, ↓reduceIte, collapseMat4]; grind
  | ⟨0, _⟩, ⟨3, _⟩ => simp only [rowNorm, hr0, h1ne, ↓reduceIte, collapseMat4]; grind
  | ⟨1, _⟩, ⟨0, _⟩ => simp only [rowNorm, hr1, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨1, _⟩, ⟨1, _⟩ => simp only [rowNorm, hr1, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨1, _⟩, ⟨2, _⟩ => simp only [rowNorm, hr1, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨1, _⟩, ⟨3, _⟩ => simp only [rowNorm, hr1, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨2, _⟩, ⟨0, _⟩ => simp only [rowNorm, hr2, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨2, _⟩, ⟨1, _⟩ => simp only [rowNorm, hr2, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨2, _⟩, ⟨2, _⟩ => simp only [rowNorm, hr2, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨2, _⟩, ⟨3, _⟩ => simp only [rowNorm, hr2, hhalf_ne, ↓reduceIte, collapseMat4]; grind
  | ⟨3, _⟩, ⟨0, _⟩ => simp only [rowNorm, hr3, h2ne, ↓reduceIte, collapseMat4]
  | ⟨3, _⟩, ⟨1, _⟩ => simp only [rowNorm, hr3, h2ne, ↓reduceIte, collapseMat4]; grind
  | ⟨3, _⟩, ⟨2, _⟩ => simp only [rowNorm, hr3, h2ne, ↓reduceIte, collapseMat4]
  | ⟨3, _⟩, ⟨3, _⟩ => simp only [rowNorm, hr3, h2ne, ↓reduceIte, collapseMat4]; grind

theorem collapseMat4_sinkhorn_fixed : sinkhornStep collapseMat4 = collapseMat4 := by
  have hc0 : colSum (rowNorm collapseMat4) ⟨0, by omega⟩ = (1 : Rat) / 2 := by
    simp only [colSum, sumFinRat, Fin.castSucc, Fin.last, rowNorm_collapseMat4]; grind
  have hc1 : colSum (rowNorm collapseMat4) ⟨1, by omega⟩ = 2 := by
    simp only [colSum, sumFinRat, Fin.castSucc, Fin.last, rowNorm_collapseMat4]; grind
  have hc2 : colSum (rowNorm collapseMat4) ⟨2, by omega⟩ = (1 : Rat) / 2 := by
    simp only [colSum, sumFinRat, Fin.castSucc, Fin.last, rowNorm_collapseMat4]; grind
  have hc3 : colSum (rowNorm collapseMat4) ⟨3, by omega⟩ = 1 := by
    simp only [colSum, sumFinRat, Fin.castSucc, Fin.last, rowNorm_collapseMat4]; grind
  have h1ne : (1 : Rat) ≠ 0 := by decide
  have h2ne : (2 : Rat) ≠ 0 := by decide
  have hhalf_ne : ((1 : Rat) / 2) ≠ 0 := Rat.ne_of_gt (rat_div_pos (by decide) (by decide))
  funext i j
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => simp only [sinkhornStep, colNorm, hc0, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨0, _⟩, ⟨1, _⟩ => simp only [sinkhornStep, colNorm, hc1, h2ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨0, _⟩, ⟨2, _⟩ => simp only [sinkhornStep, colNorm, hc2, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨0, _⟩, ⟨3, _⟩ => simp only [sinkhornStep, colNorm, hc3, h1ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨1, _⟩, ⟨0, _⟩ => simp only [sinkhornStep, colNorm, hc0, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨1, _⟩, ⟨1, _⟩ => simp only [sinkhornStep, colNorm, hc1, h2ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]
  | ⟨1, _⟩, ⟨2, _⟩ => simp only [sinkhornStep, colNorm, hc2, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨1, _⟩, ⟨3, _⟩ => simp only [sinkhornStep, colNorm, hc3, h1ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨2, _⟩, ⟨0, _⟩ => simp only [sinkhornStep, colNorm, hc0, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨2, _⟩, ⟨1, _⟩ => simp only [sinkhornStep, colNorm, hc1, h2ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]
  | ⟨2, _⟩, ⟨2, _⟩ => simp only [sinkhornStep, colNorm, hc2, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨2, _⟩, ⟨3, _⟩ => simp only [sinkhornStep, colNorm, hc3, h1ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨3, _⟩, ⟨0, _⟩ => simp only [sinkhornStep, colNorm, hc0, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨3, _⟩, ⟨1, _⟩ => simp only [sinkhornStep, colNorm, hc1, h2ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨3, _⟩, ⟨2, _⟩ => simp only [sinkhornStep, colNorm, hc2, hhalf_ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind
  | ⟨3, _⟩, ⟨3, _⟩ => simp only [sinkhornStep, colNorm, hc3, h1ne, ↓reduceIte, rowNorm_collapseMat4, collapseMat4]; grind

theorem collapseMat4_spectral_upper (u : RatVec 4) :
    normSq (matVecMul collapseMat4 u) ≤ 2 * normSq u := by
  apply rat_le_of_sub_nonneg
  have hexpand : 2 * normSq u - normSq (matVecMul collapseMat4 u) =
      (u ⟨0, by omega⟩ - u ⟨2, by omega⟩) * (u ⟨0, by omega⟩ - u ⟨2, by omega⟩) +
      ((3 : Rat) / 2) * (u ⟨1, by omega⟩ * u ⟨1, by omega⟩) +
      (u ⟨3, by omega⟩ * u ⟨3, by omega⟩) := by
    simp only [normSq, matVecMul, sumFinRat, collapseMat4, Fin.castSucc, Fin.last]
    grind
  rw [hexpand]
  exact rat_add_nonneg
    (rat_add_nonneg (rat_sq_nonneg _) (Rat.mul_nonneg (rat_div_nonneg (by decide) (by decide)) (rat_sq_nonneg _)))
    (rat_sq_nonneg _)

/-- Helper: sum over `0..n-1` of a function that is `c` on `0..n-2` and `0` at `n-1`. -/
theorem sumFinRat_init_const (m : Nat) (c : Rat) :
    sumFinRat (m + 1) (fun j : Fin (m + 1) => if j.val = m then (0 : Rat) else c) = (m : Rat) * c := by
  simp only [sumFinRat, Fin.val_last, ↓reduceIte, Rat.add_zero]
  have hcongr : ∀ j : Fin m, (if j.castSucc.val = m then (0 : Rat) else c) = c := by
    intro j
    have hlt := j.isLt
    have hne : j.val ≠ m := by omega
    simp only [Fin.val_castSucc, hne, ↓reduceIte]
  rw [sumFinRat_congr hcongr, sumFinRat_const]

/-- Helper: sum over `0..n-1` of a function that is `c` at `n-1` and `0` elsewhere. -/
theorem sumFinRat_last_only (m : Nat) (c : Rat) :
    sumFinRat (m + 1) (fun j : Fin (m + 1) => if j.val = m then c else (0 : Rat)) = c := by
  simp only [sumFinRat, Fin.val_last, ↓reduceIte]
  have hcongr : ∀ j : Fin m, (if j.castSucc.val = m then c else (0 : Rat)) = 0 := by
    intro j
    have hlt := j.isLt
    have hne : j.val ≠ m := by omega
    simp only [Fin.val_castSucc, hne, ↓reduceIte]
  rw [sumFinRat_congr hcongr, sumFinRat_zero, Rat.zero_add]

theorem collapseMatGen_sinkhorn_fixed (n : Nat) (hn : 3 ≤ n) :
    sinkhornStep (collapseMatGen n) = collapseMatGen n := by
  cases n with
  | zero => omega
  | succ m =>
    have hm_pos : 0 < m := by omega
    have hm_ne : (m : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hm_pos)
    have hinv_ne : ((1 : Rat) / (m : Rat)) ≠ 0 :=
      Rat.ne_of_gt (rat_div_pos (by decide) (rat_natCast_pos hm_pos))
    have hsub : m + 1 - 1 = m := by omega
    have hrow_sum : ∀ i : Fin (m + 1),
        rowSum (collapseMatGen (m + 1)) i =
        if i.val = m then (m : Rat) else (1 : Rat) / (m : Rat) := by
      intro i
      simp only [rowSum, collapseMatGen, hsub]
      by_cases hi : i.val = m
      · simp only [hi, ↓reduceIte]
        have := sumFinRat_init_const m 1
        rw [this]; grind
      · simp only [hi, ↓reduceIte]
        exact sumFinRat_last_only m ((1 : Rat) / (m : Rat))
    have hrowNorm : ∀ i j : Fin (m + 1),
        rowNorm (collapseMatGen (m + 1)) i j =
        if i.val = m then (if j.val = m then 0 else (1 : Rat) / (m : Rat))
        else (if j.val = m then 1 else 0) := by
      intro i j
      simp only [rowNorm, hrow_sum i, collapseMatGen, hsub]
      by_cases hi : i.val = m
      · simp only [hi, ↓reduceIte, hm_ne]
        by_cases hj : j.val = m
        · simp only [hj, ↓reduceIte]; grind
        · simp only [hj, ↓reduceIte]
      · simp only [hi, ↓reduceIte, hinv_ne]
        by_cases hj : j.val = m
        · simp only [hj, ↓reduceIte]; exact rat_div_self hinv_ne
        · simp only [hj, ↓reduceIte]; grind
    have hcol_sum : ∀ j : Fin (m + 1),
        colSum (rowNorm (collapseMatGen (m + 1))) j =
        if j.val = m then (m : Rat) else (1 : Rat) / (m : Rat) := by
      intro j
      simp only [colSum]
      rw [sumFinRat_congr (fun i => hrowNorm i j)]
      by_cases hj : j.val = m
      · simp only [hj, ↓reduceIte]
        have := sumFinRat_init_const m 1
        rw [this]; grind
      · simp only [hj, ↓reduceIte]
        exact sumFinRat_last_only m ((1 : Rat) / (m : Rat))
    funext i j
    simp only [sinkhornStep, colNorm, hcol_sum j, hrowNorm i j, collapseMatGen, hsub]
    by_cases hj : j.val = m
    · simp only [hj, ↓reduceIte, hm_ne]
      by_cases hi : i.val = m
      · simp only [hi, ↓reduceIte]; grind
      · simp only [hi, ↓reduceIte]
    · simp only [hj, ↓reduceIte, hinv_ne]
      by_cases hi : i.val = m
      · simp only [hi, ↓reduceIte]; exact rat_div_self hinv_ne
      · simp only [hi, ↓reduceIte]; grind

theorem collapseMatGen_spectral_exact (n : Nat) (hn : 3 ≤ n) :
    (∀ u : RatVec n, normSq (matVecMul (collapseMatGen n) u) ≤ ((n - 1 : Nat) : Rat) * normSq u) ∧
    (∃ v : RatVec n, (0 : Rat) < normSq v ∧
      normSq (matVecMul (collapseMatGen n) v) = ((n - 1 : Nat) : Rat) * normSq v) := by
  cases n with
  | zero => omega
  | succ m =>
    have hm_pos : 0 < m := by omega
    have hm_rat_pos : (0 : Rat) < (m : Rat) := rat_natCast_pos hm_pos
    have hm_ne : (m : Rat) ≠ 0 := Rat.ne_of_gt hm_rat_pos
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    constructor
    · intro u
      let u_init : Fin m → Rat := fun j => u j.castSucc
      have hlast_row : matVecMul (collapseMatGen (m + 1)) u (Fin.last m) = sumFinRat m u_init := by
        simp only [matVecMul, collapseMatGen, hsub, Fin.val_last, ↓reduceIte, sumFinRat]
        have h0 : (0 : Rat) * u (Fin.last m) = 0 := by grind
        rw [h0, Rat.add_zero]
        apply sumFinRat_congr
        intro j
        have hlt := j.isLt
        have hne : j.castSucc.val ≠ m := by simp only [Fin.val_castSucc]; omega
        simp only [hne, ↓reduceIte, u_init]; grind
      have hinit_row : ∀ i : Fin m,
          matVecMul (collapseMatGen (m + 1)) u i.castSucc = u (Fin.last m) / (m : Rat) := by
        intro i
        have hi_ne : i.castSucc.val ≠ m := by simp only [Fin.val_castSucc]; have := i.isLt; omega
        simp only [matVecMul, collapseMatGen, hsub, hi_ne, ↓reduceIte, sumFinRat, Fin.val_last]
        have hleft : sumFinRat m (fun j : Fin m =>
            (if j.castSucc.val = m then (1 : Rat) / (m : Rat) else 0) * u j.castSucc) = 0 := by
          have h0 : ∀ j : Fin m,
              (if j.castSucc.val = m then (1 : Rat) / (m : Rat) else 0) * u j.castSucc = 0 := by
            intro j
            have hne : j.castSucc.val ≠ m := by simp only [Fin.val_castSucc]; have := j.isLt; omega
            simp only [hne, ↓reduceIte]; grind
          rw [sumFinRat_congr h0, sumFinRat_zero]
        rw [hleft, Rat.zero_add]; grind
      have hns_Hu : normSq (matVecMul (collapseMatGen (m + 1)) u) =
          (u (Fin.last m) * u (Fin.last m)) / (m : Rat) + sumFinRat m u_init * sumFinRat m u_init := by
        simp only [normSq, sumFinRat, hlast_row]
        have hcongr : ∀ i : Fin m,
            matVecMul (collapseMatGen (m + 1)) u i.castSucc *
            matVecMul (collapseMatGen (m + 1)) u i.castSucc =
            (u (Fin.last m) / (m : Rat)) * (u (Fin.last m) / (m : Rat)) := by
          intro i; rw [hinit_row i]
        rw [sumFinRat_congr hcongr, sumFinRat_const]
        have hmul_cancel : (m : Rat) * ((u (Fin.last m) / (m : Rat)) * (u (Fin.last m) / (m : Rat))) =
            (u (Fin.last m) * u (Fin.last m)) / (m : Rat) := by
          have h1 : (m : Rat) * (u (Fin.last m) / (m : Rat)) = u (Fin.last m) := by
            rw [Rat.mul_comm]; exact rat_div_mul_cancel hm_ne
          have h2 : (m : Rat) * ((u (Fin.last m) / (m : Rat)) * (u (Fin.last m) / (m : Rat))) =
              ((m : Rat) * (u (Fin.last m) / (m : Rat))) * (u (Fin.last m) / (m : Rat)) := by grind
          rw [h2, h1]; grind
        rw [hmul_cancel]
      have hns_u : normSq u = sumFinRat m (fun j => u_init j * u_init j) +
          u (Fin.last m) * u (Fin.last m) := by
        simp only [normSq, sumFinRat, u_init]
      rw [hns_Hu, hns_u]
      have hcs : sumFinRat m u_init * sumFinRat m u_init ≤
          (m : Rat) * sumFinRat m (fun j => u_init j * u_init j) := cauchy_schwarz_ones u_init
      have hlast_le : (u (Fin.last m) * u (Fin.last m)) / (m : Rat) ≤
          (m : Rat) * (u (Fin.last m) * u (Fin.last m)) := by
        have hm1 : (1 : Rat) ≤ (m : Rat) := rat_natCast_le hm_pos
        have hm2 : (1 : Rat) ≤ (m : Rat) * (m : Rat) := by
          have h1 := rat_mul_le_mul_of_nonneg_left hm1 (Rat.le_of_lt hm_rat_pos)
          exact Rat.le_trans hm1 (by simpa using h1)
        have hinv_le : (1 : Rat) / (m : Rat) ≤ (m : Rat) := by
          apply rat_le_of_sub_nonneg
          have heq : (m : Rat) - (1 : Rat) / (m : Rat) = ((m : Rat) * (m : Rat) - 1) / (m : Rat) := by
            have h1 : (m : Rat) = ((m : Rat) * (m : Rat)) / (m : Rat) := by
              have := rat_div_mul_cancel (a := (m : Rat) * (m : Rat)) hm_ne
              have hdiff : ((m : Rat) - ((m : Rat) * (m : Rat)) / (m : Rat)) * (m : Rat) = 0 := by grind
              cases Rat.mul_eq_zero.mp hdiff with
              | inl h0 => grind
              | inr h0 => exact False.elim (hm_ne h0)
            grind
          rw [heq]
          exact rat_div_nonneg (rat_sub_nonneg hm2) hm_rat_pos
        have hmul := rat_mul_le_mul_of_nonneg_right hinv_le (rat_sq_nonneg (u (Fin.last m)))
        have heq1 : (1 : Rat) / (m : Rat) * (u (Fin.last m) * u (Fin.last m)) =
            (u (Fin.last m) * u (Fin.last m)) / (m : Rat) := by grind
        rw [heq1] at hmul
        exact hmul
      have htot := rat_add_le_add hlast_le hcs
      have hrew : (m : Rat) * (u (Fin.last m) * u (Fin.last m)) +
          (m : Rat) * sumFinRat m (fun j => u_init j * u_init j) =
          (m : Rat) * (sumFinRat m (fun j => u_init j * u_init j) +
            u (Fin.last m) * u (Fin.last m)) := by grind
      rw [hrew] at htot
      exact htot
    · let v : RatVec (m + 1) := fun j => if j.val = m then 0 else 1
      refine ⟨v, ?_, ?_⟩
      · have hns_v : normSq v = (m : Rat) := by
          simp only [normSq, v]
          have hcongr : ∀ j : Fin (m + 1), (if j.val = m then (0 : Rat) else 1) *
              (if j.val = m then (0 : Rat) else 1) = if j.val = m then 0 else 1 := by
            intro j; split <;> grind
          rw [sumFinRat_congr hcongr, sumFinRat_init_const m 1]; grind
        rw [hns_v]; exact hm_rat_pos
      · have hns_v : normSq v = (m : Rat) := by
          simp only [normSq, v]
          have hcongr : ∀ j : Fin (m + 1), (if j.val = m then (0 : Rat) else 1) *
              (if j.val = m then (0 : Rat) else 1) = if j.val = m then 0 else 1 := by
            intro j; split <;> grind
          rw [sumFinRat_congr hcongr, sumFinRat_init_const m 1]; grind
        have hHv : ∀ i : Fin (m + 1),
            matVecMul (collapseMatGen (m + 1)) v i = if i.val = m then (m : Rat) else 0 := by
          intro i
          simp only [matVecMul, collapseMatGen, hsub, v]
          by_cases hi : i.val = m
          · simp only [hi, ↓reduceIte]
            have hcongr : ∀ j : Fin (m + 1), (if j.val = m then (0 : Rat) else 1) *
                (if j.val = m then (0 : Rat) else 1) = if j.val = m then 0 else 1 := by
              intro j; split <;> grind
            rw [sumFinRat_congr hcongr, sumFinRat_init_const m 1]; grind
          · simp only [hi, ↓reduceIte]
            have hcongr : ∀ j : Fin (m + 1),
                (if j.val = m then (1 : Rat) / (m : Rat) else 0) *
                (if j.val = m then (0 : Rat) else 1) = 0 := by
              intro j; split <;> grind
            rw [sumFinRat_congr hcongr, sumFinRat_zero]
        have hns_Hv : normSq (matVecMul (collapseMatGen (m + 1)) v) = (m : Rat) * (m : Rat) := by
          simp only [normSq]
          have hcongr : ∀ i : Fin (m + 1),
              matVecMul (collapseMatGen (m + 1)) v i * matVecMul (collapseMatGen (m + 1)) v i =
              if i.val = m then (m : Rat) * (m : Rat) else 0 := by
            intro i; rw [hHv i]; split <;> grind
          rw [sumFinRat_congr hcongr, sumFinRat_last_only m ((m : Rat) * (m : Rat))]
        rw [hns_Hv, hns_v]

/-- Theorem 3 (Support-Collapse `√(n - 1)` Exact Rational Fixed Points):
    1. GPU-discovered `n = 4` witness `collapseMat4`: exact rational fixed point of `sinkhornStep`,
       exact spectral norm squared `= 2` (attainment at `v4 = (1, 0, 1, 0)` and universal upper
       bound), and exact `L = 128` (`64` applications of `H^T H`) amplification `2^128 * ‖v4‖_2^2`.
    2. Universal `n ≥ 3` family `collapseMatGen n`: exact rational fixed point of `sinkhornStep`
       attaining exact spectral norm squared `= n - 1`. -/
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
        normSq (matVecMul (collapseMatGen n) v) = ((n - 1 : Nat) : Rat) * normSq v)) := by
  intro v4
  have hns_v4 : normSq v4 = 2 := by
    simp only [normSq, sumFinRat, v4, Fin.castSucc, Fin.last]; grind
  have hns_Hv4 : normSq (matVecMul collapseMat4 v4) = 2 * normSq v4 := by
    rw [hns_v4]
    simp only [normSq, matVecMul, sumFinRat, collapseMat4, v4, Fin.castSucc, Fin.last]; grind
  have hHTH_eig : ∀ i : Fin 4,
      matVecMul (matMul (matTranspose collapseMat4) collapseMat4) v4 i = 2 * v4 i := by
    intro i
    match i with
    | ⟨0, _⟩ => simp only [matVecMul, matMul, matTranspose, sumFinRat, collapseMat4, v4, Fin.castSucc, Fin.last]; grind
    | ⟨1, _⟩ => simp only [matVecMul, matMul, matTranspose, sumFinRat, collapseMat4, v4, Fin.castSucc, Fin.last]; grind
    | ⟨2, _⟩ => simp only [matVecMul, matMul, matTranspose, sumFinRat, collapseMat4, v4, Fin.castSucc, Fin.last]; grind
    | ⟨3, _⟩ => simp only [matVecMul, matMul, matTranspose, sumFinRat, collapseMat4, v4, Fin.castSucc, Fin.last]; grind
  have hpow64 : ratPow 2 64 * ratPow 2 64 = ratPow 2 128 := by
    have hadd : ∀ a b : Nat, ratPow 2 a * ratPow 2 b = ratPow 2 (a + b) := by
      intro a
      induction a with
      | zero => intro b; simp only [ratPow, Nat.zero_add]; grind
      | succ k ih =>
        intro b
        simp only [ratPow]
        have h1 : k + 1 + b = (k + b) + 1 := by omega
        rw [h1, ratPow, ← ih b]; grind
    exact hadd 64 64
  have hL128 : normSq (vecApplyIter (matMul (matTranspose collapseMat4) collapseMat4) 64 v4) =
      ratPow 2 128 * normSq v4 := by
    rw [normSq_vecApplyIter_eigenvector _ v4 2 hHTH_eig 64, hpow64]
  refine ⟨collapseMat4_sinkhorn_fixed, ⟨hns_v4, hns_Hv4⟩, collapseMat4_spectral_upper, hL128, ?_⟩
  intro n hn
  have hspec := collapseMatGen_spectral_exact n hn
  exact ⟨collapseMatGen_sinkhorn_fixed n hn, hspec.1, hspec.2⟩

/-! ### 2. Theorem 6: Zero-Division Dyadic-Orthogonal Residual Stream Mixers -/

theorem sumFinRat_delta_right {n : Nat} (j : Fin n) (f : Fin n → Rat) :
    sumFinRat n (fun k => (if k = j then (1 : Rat) else 0) * f k) = f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    simp only [sumFinRat]
    by_cases hl : j = Fin.last m
    · subst hl
      have h0 : sumFinRat m (fun k : Fin m =>
          (if k.castSucc = Fin.last m then (1 : Rat) else 0) * f k.castSucc) = 0 := by
        have hcongr : ∀ k : Fin m,
            (if k.castSucc = Fin.last m then (1 : Rat) else 0) * f k.castSucc = 0 := by
          intro k
          have hne : k.castSucc ≠ Fin.last m := by
            intro heq
            have hv := congrArg Fin.val heq
            simp only [Fin.val_castSucc, Fin.val_last] at hv
            omega
          simp only [hne, ↓reduceIte]; grind
        rw [sumFinRat_congr hcongr, sumFinRat_zero]
      rw [h0]; simp; grind
    · have hlt : j.val < m := by
        have := j.isLt
        have hne : j.val ≠ m := fun hv => hl (Fin.ext hv)
        omega
      let j' : Fin m := ⟨j.val, hlt⟩
      have hleft : sumFinRat m (fun k : Fin m =>
          (if k.castSucc = j then (1 : Rat) else 0) * f k.castSucc) =
          sumFinRat m (fun k : Fin m => (if k = j' then (1 : Rat) else 0) * f k.castSucc) := by
        apply sumFinRat_congr
        intro k
        have hiff : (k.castSucc = j) ↔ (k = j') := by
          constructor
          · intro heq; apply Fin.ext; have hv := congrArg Fin.val heq; simpa [j'] using hv
          · intro heq; apply Fin.ext; have hv := congrArg Fin.val heq; simpa [j'] using hv
        simp only [hiff]
      have hne_last : Fin.last m ≠ j := Ne.symm hl
      have hlast : (if Fin.last m = j then (1 : Rat) else 0) * f (Fin.last m) = 0 := by
        simp only [hne_last, ↓reduceIte]; grind
      rw [hleft, hlast, Rat.add_zero, ih j' (fun k => f k.castSucc)]
      exact congrArg f (Fin.ext rfl)

/-- Universal orthogonality → exact Euclidean energy preservation (`‖Q v‖_2^2 = ‖v‖_2^2`). -/
theorem orthogonal_preserves_normSq {n : Nat} (Q : RatMat n) (hQ : isOrthogonalRat Q) (v : RatVec n) :
    normSq (matVecMul Q v) = normSq v := by
  simp only [normSq, matVecMul]
  have hexp1 : ∀ i : Fin n,
      sumFinRat n (fun j => Q i j * v j) * sumFinRat n (fun k => Q i k * v k) =
      sumFinRat n (fun j => sumFinRat n (fun k => (Q i j * Q i k) * (v j * v k))) := by
    intro i
    rw [← sumFinRat_mul_right]
    apply sumFinRat_congr
    intro j
    rw [← sumFinRat_mul_left]
    apply sumFinRat_congr
    intro k; grind
  rw [sumFinRat_congr hexp1, sumFinRat_swap]
  have hinner : ∀ j : Fin n,
      sumFinRat n (fun i => sumFinRat n (fun k => (Q i j * Q i k) * (v j * v k))) =
      v j * v j := by
    intro j
    rw [sumFinRat_swap]
    have hfactor : ∀ k : Fin n,
        sumFinRat n (fun i => (Q i j * Q i k) * (v j * v k)) =
        (matMul (matTranspose Q) Q j k) * (v j * v k) := by
      intro k
      rw [sumFinRat_mul_right]
      rfl
    rw [sumFinRat_congr hfactor, hQ]
    have hdelta : ∀ k : Fin n, matId n j k * (v j * v k) =
        (if k = j then (1 : Rat) else 0) * (v j * v k) := by
      intro k
      simp only [matId]
      by_cases h : j = k
      · subst h; simp
      · have h' : k ≠ j := Ne.symm h
        simp [h, h']
    rw [sumFinRat_congr hdelta, sumFinRat_delta_right j (fun k => v j * v k)]
  rw [sumFinRat_congr hinner]

theorem orthogonal_preserves_normSq_iter {n : Nat} (Q : RatMat n) (hQ : isOrthogonalRat Q)
    (L : Nat) (v : RatVec n) :
    normSq (vecApplyIter Q L v) = normSq v := by
  induction L with
  | zero => rfl
  | succ k ih =>
    simp only [vecApplyIter]
    rw [orthogonal_preserves_normSq Q hQ, ih]

theorem orthogonal_preserves_normSq_list {n : Nat} (Qs : List (RatMat n))
    (hQs : ∀ Q ∈ Qs, isOrthogonalRat Q) (v : RatVec n) :
    normSq (applyLayerList Qs v) = normSq v := by
  induction Qs generalizing v with
  | nil => rfl
  | cons Q rest ih =>
    simp only [applyLayerList]
    have hQ : isOrthogonalRat Q := hQs Q (List.Mem.head rest)
    have hrest : ∀ R ∈ rest, isOrthogonalRat R := fun R hR => hQs R (List.Mem.tail Q hR)
    rw [ih hrest (matVecMul Q v), orthogonal_preserves_normSq Q hQ v]

/-- Universal exact orthogonality of the `n = 4` Hamilton-Quaternion mixer `(1/2) L(a,b,c,d)`
    whenever `a^2 + b^2 + c^2 + d^2 = 4`. -/
theorem quatMixer4_orthogonal (a b c d : Rat) (hnorm : a * a + b * b + c * c + d * d = 4) :
    isOrthogonalRat (quatMixer4 a b c d) := by
  funext i j
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨0, _⟩, ⟨1, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨0, _⟩, ⟨2, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨0, _⟩, ⟨3, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨1, _⟩, ⟨0, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨1, _⟩, ⟨1, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨1, _⟩, ⟨2, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨1, _⟩, ⟨3, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨2, _⟩, ⟨0, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨2, _⟩, ⟨1, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨2, _⟩, ⟨2, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨2, _⟩, ⟨3, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨3, _⟩, ⟨0, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨3, _⟩, ⟨1, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨3, _⟩, ⟨2, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind
  | ⟨3, _⟩, ⟨3, _⟩ => simp only [matMul, matTranspose, matId, sumFinRat, quatMixer4, Fin.castSucc, Fin.last]; grind

theorem hadamardMixer4_orthogonal : isOrthogonalRat hadamardMixer4 :=
  quatMixer4_orthogonal 1 1 1 1 (by grind)

theorem signedHadamard4_orthogonal (s : Fin 4 → Rat) (hs : ∀ j, s j * s j = 1) :
    isOrthogonalRat (signedHadamard4 s) := by
  funext i j
  have hH := congrFun (congrFun hadamardMixer4_orthogonal i) j
  simp only [matMul, matTranspose, signedHadamard4]
  have hfactor : ∀ k : Fin 4,
      (hadamardMixer4 k i * s i) * (hadamardMixer4 k j * s j) =
      (s i * s j) * (matTranspose hadamardMixer4 i k * hadamardMixer4 k j) := by
    intro k; simp only [matTranspose]; grind
  rw [sumFinRat_congr hfactor, sumFinRat_mul_left]
  change (s i * s j) * matMul (matTranspose hadamardMixer4) hadamardMixer4 i j = matId 4 i j
  rw [hH]
  simp only [matId]
  by_cases h : i = j
  · subst h; simp only [↓reduceIte, hs i]; grind
  · simp only [h, ↓reduceIte]; grind

/-- Universal exact orthogonality of the `n = 8` dyadic Householder mixer `I_8 - (1/8) v v^T`
    for EVERY `v : RatVec 8` with `‖v‖_2^2 = 16` (exact `>> 3` bit-shift, zero division!). -/
theorem householder8_orthogonal (v : RatVec 8) (hv : normSq v = 16) :
    isOrthogonalRat (householder8 v) := by
  funext i j
  simp only [matMul, matTranspose, householder8]
  have hexpand : ∀ k : Fin 8,
      ((if k = i then (1 : Rat) else 0) - ((1 : Rat) / 8) * (v k * v i)) *
      ((if k = j then (1 : Rat) else 0) - ((1 : Rat) / 8) * (v k * v j)) =
      ((if k = i then (1 : Rat) else 0) * (if k = j then (1 : Rat) else 0) -
       (if k = i then (1 : Rat) else 0) * (((1 : Rat) / 8) * (v k * v j))) -
      (if k = j then (1 : Rat) else 0) * (((1 : Rat) / 8) * (v k * v i)) +
      (((1 : Rat) / 64) * (v i * v j)) * (v k * v k) := by
    intro k; grind
  rw [sumFinRat_congr hexpand, sumFinRat_add, sumFinRat_sub, sumFinRat_sub,
      sumFinRat_delta_right i (fun k => if k = j then (1 : Rat) else 0),
      sumFinRat_delta_right i (fun k => ((1 : Rat) / 8) * (v k * v j)),
      sumFinRat_delta_right j (fun k => ((1 : Rat) / 8) * (v k * v i)),
      sumFinRat_mul_left]
  have hns : sumFinRat 8 (fun k => v k * v k) = 16 := hv
  rw [hns]
  simp only [matId]
  grind

/-- Theorem 6 (Zero-Division Dyadic-Orthogonal Residual Stream Mixers):
    1. Universal exact orthogonality of the `n = 4` Hamilton-Quaternion family `(1/2) L(a,b,c,d)`
       whenever `a^2 + b^2 + c^2 + d^2 = 4`, concrete `hadamardMixer4` (`±1/2`), and all
       column-signed `signedHadamard4 s`.
    2. Universal exact orthogonality of the `n = 8` dyadic Householder mixer `I_8 - (1/8) v v^T`
       for EVERY `v` with `‖v‖_2^2 = 16` (including `(3, 1, 1, 1, 1, 1, 1, 1)`).
    3. Exact energy preservation `‖Q v‖_2^2 = ‖v‖_2^2`, `‖Q^L v‖_2^2 = ‖v‖_2^2` for ALL depths `L`,
       and `‖applyLayerList Qs v‖_2^2 = ‖v‖_2^2` for ANY sequence of orthogonal mixers. -/
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
      ∀ v : RatVec n, normSq (applyLayerList Qs v) = normSq v) := by
  refine ⟨quatMixer4_orthogonal, hadamardMixer4_orthogonal, signedHadamard4_orthogonal,
          householder8_orthogonal, ?_, ?_, fun n => orthogonal_preserves_normSq_list (n := n)⟩
  · let v8 : RatVec 8 := fun i => if i.val = 0 then 3 else 1
    have hv8 : normSq v8 = 16 := by
      simp only [normSq, sumFinRat, v8, Fin.castSucc, Fin.last]; grind
    exact ⟨hv8, householder8_orthogonal v8 hv8⟩
  · intro n Q hQ
    exact ⟨orthogonal_preserves_normSq Q hQ, orthogonal_preserves_normSq_iter Q hQ⟩

end MhcSinkhornFp8
