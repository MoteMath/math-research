/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp.RatOrder

/-!
# Theorem 1: Tied-Embedding Dense Push-Down Zero-Sum Conservation & Asymmetry

Pure-`Init` exact algebraic proofs for tied weights `W_emb = W_lm^T ∈ Q^{V × d}`:
1. Exact column-sum conservation `∑_v g_out[v, j] = 0` for every hidden coordinate `j`
   (both single-step and batch-averaged across `B` positions).
2. Sparse-input vs dense-output asymmetry on every absent token `v ≠ y`:
   `g_in[v, j] = 0`, `g_out[v, j] = p_v * h_j`, and `g_out[y, j] = -(1 - p_y) * h_j`.
3. Exact `p_y⁻¹ · p_v` and `p_v / (1 - p_y)` magnitude ratios between absent and active rows.
-/

namespace EmbedZipfLazyStamp

theorem gOutDense_col_sum_zero {V d : Nat} (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat)
    (hp : finSum p = 1) (j : Fin d) :
    finSum (fun v : Fin V => gOutDense p y h v j) = 0 := by
  have h1 : finSum (fun v : Fin V => gOutDense p y h v j) =
      finSum (fun v : Fin V => p v - if v = y then (1 : Rat) else 0) * h j := by
    rw [← finSum_mul_right]
    rfl
  rw [h1, finSum_sub, hp, finSum_ite_eq y]
  grind

theorem gOutBatch_col_sum_zero {B V d : Nat}
    (pB : Fin B → Fin V → Rat) (yB : Fin B → Fin V) (hB : Fin B → Fin d → Rat)
    (hpB : ∀ b : Fin B, finSum (pB b) = 1) (j : Fin d) :
    finSum (fun v : Fin V => gOutBatch pB yB hB v j) = 0 := by
  unfold gOutBatch
  rw [finSum_mul_left, finSum_swap]
  have hzero : finSum (fun b : Fin B => finSum (fun v : Fin V => gOutDense (pB b) (yB b) (hB b) v j)) = 0 := by
    rw [finSum_congr (fun b => gOutDense_col_sum_zero (pB b) (yB b) (hB b) (hpB b) j)]
    exact finSum_zero B
  rw [hzero, Rat.mul_zero]

theorem gInSparse_absent {V d : Nat} (y : Fin V) (g_x : Fin d → Rat)
    (v : Fin V) (hv : v ≠ y) (j : Fin d) :
    gInSparse y g_x v j = 0 := by
  unfold gInSparse
  simp [hv]

theorem gOutDense_absent {V d : Nat} (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat)
    (v : Fin V) (hv : v ≠ y) (j : Fin d) :
    gOutDense p y h v j = p v * h j := by
  unfold gOutDense
  simp only [hv, ↓reduceIte]
  grind

theorem gOutDense_active {V d : Nat} (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat)
    (j : Fin d) :
    gOutDense p y h y j = -(1 - p y) * h j := by
  unfold gOutDense
  simp only [↓reduceIte]
  grind

theorem gOutDense_absent_active_ratio {V d : Nat} (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat)
    (v : Fin V) (hv : v ≠ y) (j : Fin d)
    (hpv : (0 : Rat) < p v) (hpy_pos : (0 : Rat) < p y) (hpy_lt : p y < 1) (hh : h j ≠ 0) :
    ratAbs (gOutDense p y h v j) / ratAbs (gOutDense p y h y j) = p v / (1 - p y) ∧
    ratAbs (gOutDense p y h v j) / ratAbs (p y * h j) = (1 / p y) * p v ∧
    ratAbs (gOutDense p y h v j) / ratAbs (gOutDense p y h y j) =
      ((1 / p y) * p v) * (p y / (1 - p y)) := by
  rw [gOutDense_absent p y h v hv j, gOutDense_active p y h j]
  have h1mp : (0 : Rat) < 1 - p y := rat_sub_pos hpy_lt
  have habs_h : (0 : Rat) < ratAbs (h j) := ratAbs_pos_of_ne_zero hh
  have habs_v : ratAbs (p v * h j) = p v * ratAbs (h j) := by
    rw [ratAbs_mul, ratAbs_of_nonneg (Rat.le_of_lt hpv)]
  have habs_y : ratAbs (-(1 - p y) * h j) = (1 - p y) * ratAbs (h j) := by
    rw [ratAbs_mul, ratAbs_neg, ratAbs_of_nonneg (Rat.le_of_lt h1mp)]
  have habs_pyh : ratAbs (p y * h j) = p y * ratAbs (h j) := by
    rw [ratAbs_mul, ratAbs_of_nonneg (Rat.le_of_lt hpy_pos)]
  rw [habs_v, habs_y, habs_pyh]
  have hden1 : (1 - p y) * ratAbs (h j) ≠ 0 := Rat.ne_of_gt (rat_mul_pos h1mp habs_h)
  have hden2 : p y * ratAbs (h j) ≠ 0 := Rat.ne_of_gt (rat_mul_pos hpy_pos habs_h)
  have h1mp_ne : 1 - p y ≠ 0 := Rat.ne_of_gt h1mp
  have hpy_ne : p y ≠ 0 := Rat.ne_of_gt hpy_pos
  have hr1 : (p v * ratAbs (h j)) / ((1 - p y) * ratAbs (h j)) = p v / (1 - p y) := by
    rw [rat_div_eq_iff hden1]
    have hmul : p v / (1 - p y) * ((1 - p y) * ratAbs (h j)) =
        (p v / (1 - p y) * (1 - p y)) * ratAbs (h j) := by grind
    rw [hmul, rat_div_mul_cancel h1mp_ne]
  have hr2 : (p v * ratAbs (h j)) / (p y * ratAbs (h j)) = (1 / p y) * p v := by
    rw [rat_div_eq_iff hden2]
    have hmul : (1 / p y) * p v * (p y * ratAbs (h j)) =
        ((1 / p y) * p y) * (p v * ratAbs (h j)) := by grind
    rw [hmul, rat_div_mul_cancel hpy_ne, Rat.one_mul]
  refine ⟨hr1, hr2, ?_⟩
  rw [hr1]
  have hmul : (1 / p y) * p v * (p y / (1 - p y)) =
      ((1 / p y) * p y) * (p v / (1 - p y)) := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind
  rw [hmul, rat_div_mul_cancel hpy_ne, Rat.one_mul]

/-- Headline Theorem 1 (`tied_embedding_dense_pushdown_zero_sum_and_asymmetry`):
    Exact algebraic law for tied weights `W_emb = W_lm^T ∈ Q^{V × d}` proving
    single-step and batch-averaged column-sum conservation `∑_v g_out[v, j] = 0`,
    sparse-input vs dense-output asymmetry on every absent token `v ≠ y`, and
    the exact `p_y⁻¹ · p_v` and `p_v / (1 - p_y)` magnitude ratios. -/
theorem tied_embedding_dense_pushdown_zero_sum_and_asymmetry :
    (∀ (V d : Nat) (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat),
      finSum p = 1 → ∀ j : Fin d, finSum (fun v : Fin V => gOutDense p y h v j) = 0) ∧
    (∀ (B V d : Nat) (pB : Fin B → Fin V → Rat) (yB : Fin B → Fin V) (hB : Fin B → Fin d → Rat),
      (∀ b : Fin B, finSum (pB b) = 1) →
      ∀ j : Fin d, finSum (fun v : Fin V => gOutBatch pB yB hB v j) = 0) ∧
    (∀ (V d : Nat) (p : Fin V → Rat) (y : Fin V) (h g_x : Fin d → Rat) (v : Fin V),
      v ≠ y → ∀ j : Fin d,
        gInSparse y g_x v j = 0 ∧
        gOutDense p y h v j = p v * h j ∧
        gOutDense p y h y j = -(1 - p y) * h j) ∧
    (∀ (V d : Nat) (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat) (v : Fin V) (j : Fin d),
      v ≠ y → (0 : Rat) < p v → (0 : Rat) < p y → p y < 1 → h j ≠ 0 →
        ratAbs (gOutDense p y h v j) / ratAbs (gOutDense p y h y j) = p v / (1 - p y) ∧
        ratAbs (gOutDense p y h v j) / ratAbs (p y * h j) = (1 / p y) * p v ∧
        ratAbs (gOutDense p y h v j) / ratAbs (gOutDense p y h y j) =
          ((1 / p y) * p v) * (p y / (1 - p y))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V d p y h hp j
    exact gOutDense_col_sum_zero p y h hp j
  · intro B V d pB yB hB hpB j
    exact gOutBatch_col_sum_zero pB yB hB hpB j
  · intro V d p y h g_x v hv j
    exact ⟨gInSparse_absent y g_x v hv j,
           gOutDense_absent p y h v hv j,
           gOutDense_active p y h j⟩
  · intro V d p y h v j hv hpv hpy_pos hpy_lt hh
    exact gOutDense_absent_active_ratio p y h v hv j hpv hpy_pos hpy_lt hh

end EmbedZipfLazyStamp
