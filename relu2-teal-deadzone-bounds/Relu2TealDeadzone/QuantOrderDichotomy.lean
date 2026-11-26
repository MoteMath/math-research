/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relu2TealDeadzone.RatOrder

/-!
# Theorems 2 & 3: Uniform vs Floating-Point Squared-ReLU Quantization-Order Dichotomy

- **Theorem 2 (`relu2_quantization_order_uniform_pre_beats_post`)**:
  For uniform integer quantization (`INT4-u4` with `N = 15`, `INT4-s4` with `N = 7`, or general
  `N > 0`) on `[0, M]`:
  1. The squared zero-underflow threshold ratio `postZeroCutoffSq M N / sq (preZeroCutoff M N)`
     equals exact `2 * N` (`30 > 5^2` for `INT4-u4`, proving a `> 5×` wider linear deadzone in
     `POST`; `14 > 3^2` for `INT4-s4`).
  2. For any `x ∈ [0, M]` and `û` with `|û - x| ≤ M / (2N)`, the `PRE`-square error satisfies
     `|û^2 - x^2| ≤ preMaxErr M N x = (M * x) / N + M^2 / (4N^2)`.
  3. `PRE` strictly beats `POST` (`preMaxErr M N x < postMaxErr M N`) iff
     `x < M * (1/2 - 1/(4N))` (for `INT4-u4`, every `x < (29/60) * M`).
  4. On outlier-dominated blocks (`x ≤ M / c`), `preMaxErr M N (M / c) / postMaxErr M N =
     2 / c + 1 / (2N)`. For `c = 4, N = 15` (`INT4-u4` OutlierMix), this ratio is `8 / 15`,
     yielding squared worst-case error ratio `64 / 225 < 1 / 3` (`> 3.5×` MSE reduction).

- **Theorem 3 (`relu2_quantization_order_fp_post_beats_pre_exact_4x`)**:
  For floating-point formats (`FP8-E4M3`, `MXFP4`, `NVFP4`) with relative error `û = u (1 + δ)`,
  `|δ| ≤ ε < 2`:
  1. Exact algebraic squaring identity: `û^2 - u^2 = u^2 * (2 * δ + δ^2) = u^2 * δ * (2 + δ)`.
  2. Exact two-sided squared-error ratio bounds:
     `(2 - ε)^2 ≤ (2 + δ)^2 ≤ (2 + ε)^2`, and when `u ≠ 0, δ ≠ 0`,
     `sq (û^2 - u^2) / sq (u^2 * δ) = sq (2 + δ)`.
  3. Finite-dataset (`Fin n`) MSE inflation law:
     `(2 - ε)^2 * ∑ (u_i^2 * δ_i)^2 ≤ ∑ ((u_i (1 + δ_i))^2 - u_i^2)^2 ≤ (2 + ε)^2 * ∑ (u_i^2 * δ_i)^2`.
  4. Exact asymptotic limit `4×` at `ε = 0` and exact `FP8-E4M3` (`ε = 1/16`) bracket
     `961 / 256 ≤ ratio ≤ 1089 / 256` (bracketing the GPU-certified `3.91×` / `5.92 dB`).
-/

namespace Relu2TealDeadzone

theorem pre_post_zero_cutoff_sq_ratio {M N : Rat} (hM : (0 : Rat) < M) (hN : (0 : Rat) < N) :
    postZeroCutoffSq M N / sq (preZeroCutoff M N) = 2 * N := by
  unfold postZeroCutoffSq preZeroCutoff sq
  have hMne : M ≠ 0 := Rat.ne_of_gt hM
  have hNne : N ≠ 0 := Rat.ne_of_gt hN
  have h2N : 2 * N ≠ 0 := by
    have : (0 : Rat) < 2 * N := rat_mul_pos (by decide) hN
    exact Rat.ne_of_gt this
  have hpre_pos : (0 : Rat) < M / (2 * N) := rat_div_pos hM (rat_mul_pos (by decide) hN)
  have hden_ne : (M / (2 * N)) * (M / (2 * N)) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos hpre_pos hpre_pos)
  rw [rat_div_eq_iff hden_ne]
  have h1 : (M / (2 * N)) * (2 * N) = M := rat_div_mul_cancel h2N
  have h2 : (M * M / (2 * N)) * (2 * N) = M * M := rat_div_mul_cancel h2N
  have h2Npos : (0 : Rat) < 2 * N := rat_mul_pos (by decide) hN
  have hmul : (M * M / (2 * N)) * (2 * N) = (2 * N * ((M / (2 * N)) * (M / (2 * N)))) * (2 * N) := by
    rw [h2]
    have hassoc : (2 * N * ((M / (2 * N)) * (M / (2 * N)))) * (2 * N) =
        ((M / (2 * N)) * (2 * N)) * ((M / (2 * N)) * (2 * N)) := by grind
    rw [hassoc, h1]
  exact rat_eq_of_mul_pos_right h2Npos hmul

theorem pre_sq_err_bound {M N x uhat : Rat} (hM : (0 : Rat) < M) (hN : (0 : Rat) < N)
    (hx : (0 : Rat) ≤ x) (herr : ratAbs (uhat - x) ≤ preZeroCutoff M N) :
    ratAbs (sq uhat - sq x) ≤ preMaxErr M N x := by
  have hdiff : sq uhat - sq x = (uhat - x) * (uhat + x) := by unfold sq; grind
  rw [hdiff, ratAbs_mul]
  have hsum_eq : uhat + x = (uhat - x) + 2 * x := by grind
  have hsum_le : ratAbs (uhat + x) ≤ preZeroCutoff M N + 2 * x := by
    rw [hsum_eq]
    have htri := ratAbs_add_le (uhat - x) (2 * x)
    have h2x : ratAbs (2 * x) = 2 * x := ratAbs_of_nonneg (Rat.mul_nonneg (by decide) hx)
    rw [h2x] at htri
    exact Rat.le_trans htri ((Rat.add_le_add_right (c := 2 * x)).mpr herr)
  have hpre_nonneg : (0 : Rat) ≤ preZeroCutoff M N := by
    unfold preZeroCutoff
    exact rat_div_nonneg (Rat.le_of_lt hM) (rat_mul_pos (by decide) hN)
  have hprod : ratAbs (uhat - x) * ratAbs (uhat + x) ≤
      preZeroCutoff M N * (preZeroCutoff M N + 2 * x) := by
    have h1 := rat_mul_le_mul_of_nonneg_left hsum_le (ratAbs_nonneg (uhat - x))
    have h2 := rat_mul_le_mul_of_nonneg_right herr
      (rat_add_nonneg hpre_nonneg (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 2) hx))
    exact Rat.le_trans h1 h2
  have hident : preZeroCutoff M N * (preZeroCutoff M N + 2 * x) = preMaxErr M N x := by
    unfold preZeroCutoff preMaxErr sq
    have hNne : N ≠ 0 := Rat.ne_of_gt hN
    have h2N : 2 * N ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) hN)
    have h4N2 : 4 * (N * N) ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (rat_mul_pos hN hN))
    have hpos : (0 : Rat) < 4 * (N * N) := rat_mul_pos (by decide) (rat_mul_pos hN hN)
    have hc1 : (M / (2 * N)) * (2 * N) = M := rat_div_mul_cancel h2N
    have hc2 : (M * x / N) * N = M * x := rat_div_mul_cancel hNne
    have hc3 : (M * M / (4 * (N * N))) * (4 * (N * N)) = M * M := rat_div_mul_cancel h4N2
    have hmul : (M / (2 * N) * (M / (2 * N) + 2 * x)) * (4 * (N * N)) =
        (M * x / N + M * M / (4 * (N * N))) * (4 * (N * N)) := by
      have hL : (M / (2 * N) * (M / (2 * N) + 2 * x)) * (4 * (N * N)) =
          ((M / (2 * N)) * (2 * N)) * ((M / (2 * N)) * (2 * N)) +
          2 * x * ((M / (2 * N)) * (2 * N)) * (2 * N) := by grind
      have hR : (M * x / N + M * M / (4 * (N * N))) * (4 * (N * N)) =
          ((M * x / N) * N) * (4 * N) + (M * M / (4 * (N * N))) * (4 * (N * N)) := by grind
      rw [hL, hR, hc1, hc2, hc3]
      grind
    exact rat_eq_of_mul_pos_right hpos hmul
  rw [← hident]
  exact hprod

theorem pre_beats_post_iff {M N x : Rat} (hM : (0 : Rat) < M) (hN : (0 : Rat) < N) :
    preMaxErr M N x < postMaxErr M N ↔ x < M * (1 / 2 - 1 / (4 * N)) := by
  unfold preMaxErr postMaxErr sq
  have hNne : N ≠ 0 := Rat.ne_of_gt hN
  have h2Nne : 2 * N ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) hN)
  have h4Nne : 4 * N ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) hN)
  have h4N2pos : (0 : Rat) < 4 * (N * N) := rat_mul_pos (by decide) (rat_mul_pos hN hN)
  have h4N2ne : 4 * (N * N) ≠ 0 := Rat.ne_of_gt h4N2pos
  have hc1 : (M * x / N) * N = M * x := rat_div_mul_cancel hNne
  have hc2 : (M * M / (4 * (N * N))) * (4 * (N * N)) = M * M := rat_div_mul_cancel h4N2ne
  have hc3 : (M * M / (2 * N)) * (2 * N) = M * M := rat_div_mul_cancel h2Nne
  have hc4 : ((1 : Rat) / (4 * N)) * (4 * N) = 1 := rat_div_mul_cancel h4Nne
  have hL : (M * x / N + M * M / (4 * (N * N))) * (4 * (N * N)) =
      4 * N * M * x + M * M := by
    have eq : (M * x / N + M * M / (4 * (N * N))) * (4 * (N * N)) =
        ((M * x / N) * N) * (4 * N) + (M * M / (4 * (N * N))) * (4 * (N * N)) := by grind
    rw [eq, hc1, hc2]; grind
  have hR : (M * M / (2 * N)) * (4 * (N * N)) = 2 * N * (M * M) := by
    have eq : (M * M / (2 * N)) * (4 * (N * N)) = ((M * M / (2 * N)) * (2 * N)) * (2 * N) := by
      grind
    rw [eq, hc3]; grind
  have hM4Npos : (0 : Rat) < 4 * N * M := rat_mul_pos (rat_mul_pos (by decide) hN) hM
  have hRHS : (M * (1 / 2 - 1 / (4 * N))) * (4 * N * M) = (2 * N - 1) * (M * M) := by
    have eq : (M * (1 / 2 - 1 / (4 * N))) * (4 * N * M) =
        M * M * (2 * N - ((1 : Rat) / (4 * N)) * (4 * N)) := by grind
    rw [eq, hc4]; grind
  constructor
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h h4N2pos
    rw [hL, hR] at hmul
    apply rat_lt_of_mul_pos_right hM4Npos
    rw [hRHS]
    have hsub := rat_sub_pos hmul
    apply rat_lt_of_sub_pos
    have eq : (2 * N - 1) * (M * M) - x * (4 * N * M) =
        2 * N * (M * M) - (4 * N * M * x + M * M) := by grind
    rw [eq]; exact hsub
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h hM4Npos
    rw [hRHS] at hmul
    apply rat_lt_of_mul_pos_right h4N2pos
    rw [hL, hR]
    have hsub := rat_sub_pos hmul
    apply rat_lt_of_sub_pos
    have eq : 2 * N * (M * M) - (4 * N * M * x + M * M) =
        (2 * N - 1) * (M * M) - x * (4 * N * M) := by grind
    rw [eq]; exact hsub

theorem pre_post_outlier_ratio {M N c : Rat} (hM : (0 : Rat) < M) (hN : (0 : Rat) < N)
    (hc : (0 : Rat) < c) :
    preMaxErr M N (M / c) / postMaxErr M N = 2 / c + 1 / (2 * N) := by
  unfold preMaxErr postMaxErr sq
  have hMne : M ≠ 0 := Rat.ne_of_gt hM
  have hNne : N ≠ 0 := Rat.ne_of_gt hN
  have hcne : c ≠ 0 := Rat.ne_of_gt hc
  have h2Npos : (0 : Rat) < 2 * N := rat_mul_pos (by decide) hN
  have h2Nne : 2 * N ≠ 0 := Rat.ne_of_gt h2Npos
  have hpost_pos : (0 : Rat) < M * M / (2 * N) := rat_div_pos (rat_mul_pos hM hM) h2Npos
  have hpost_ne : M * M / (2 * N) ≠ 0 := Rat.ne_of_gt hpost_pos
  rw [rat_div_eq_iff hpost_ne]
  have h4N2cpos : (0 : Rat) < 4 * (N * N) * c :=
    rat_mul_pos (rat_mul_pos (by decide) (rat_mul_pos hN hN)) hc
  have h4N2ne : 4 * (N * N) ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (rat_mul_pos hN hN))
  have hc1 : (M / c) * c = M := rat_div_mul_cancel hcne
  have hc2 : (M * (M / c) / N) * N = M * (M / c) := rat_div_mul_cancel hNne
  have hc3 : (M * M / (4 * (N * N))) * (4 * (N * N)) = M * M := rat_div_mul_cancel h4N2ne
  have hc4 : (M * M / (2 * N)) * (2 * N) = M * M := rat_div_mul_cancel h2Nne
  have hc5 : ((2 : Rat) / c) * c = 2 := rat_div_mul_cancel hcne
  have hc6 : ((1 : Rat) / (2 * N)) * (2 * N) = 1 := rat_div_mul_cancel h2Nne
  have hmul : (M * (M / c) / N + M * M / (4 * (N * N))) * (4 * (N * N) * c) =
      ((2 / c + 1 / (2 * N)) * (M * M / (2 * N))) * (4 * (N * N) * c) := by
    have hL : (M * (M / c) / N + M * M / (4 * (N * N))) * (4 * (N * N) * c) =
        ((M * (M / c) / N) * N) * (4 * N * c) +
        ((M * M / (4 * (N * N))) * (4 * (N * N))) * c := by grind
    rw [hL, hc2, hc3]
    have hL2 : M * (M / c) * (4 * N * c) + M * M * c =
        M * ((M / c) * c) * (4 * N) + M * M * c := by grind
    rw [hL2, hc1]
    have hR : ((2 / c + 1 / (2 * N)) * (M * M / (2 * N))) * (4 * (N * N) * c) =
        (((2 : Rat) / c) * c) * ((M * M / (2 * N)) * (2 * N)) * (2 * N) +
        (((1 : Rat) / (2 * N)) * (2 * N)) * ((M * M / (2 * N)) * (2 * N)) * c := by grind
    rw [hR, hc4, hc5, hc6]
    grind
  exact rat_eq_of_mul_pos_right h4N2cpos hmul

theorem relu2_quantization_order_uniform_pre_beats_post :
    (∀ M N : Rat, (0 : Rat) < M → (0 : Rat) < N →
      postZeroCutoffSq M N / sq (preZeroCutoff M N) = 2 * N) ∧
    ((2 * (15 : Rat) = 30 ∧ sq 5 < 30) ∧
     (2 * (7 : Rat) = 14 ∧ sq 3 < 14)) ∧
    (∀ M N x uhat : Rat, (0 : Rat) < M → (0 : Rat) < N → (0 : Rat) ≤ x →
      ratAbs (uhat - x) ≤ preZeroCutoff M N →
      ratAbs (sq uhat - sq x) ≤ preMaxErr M N x) ∧
    (∀ M N x : Rat, (0 : Rat) < M → (0 : Rat) < N →
      (preMaxErr M N x < postMaxErr M N ↔ x < M * (1 / 2 - 1 / (4 * N)))) ∧
    ((1 / 2 - 1 / (4 * 15) : Rat) = 29 / 60) ∧
    (∀ M N c : Rat, (0 : Rat) < M → (0 : Rat) < N → (0 : Rat) < c →
      preMaxErr M N (M / c) / postMaxErr M N = 2 / c + 1 / (2 * N)) ∧
    (((2 / 4 + 1 / (2 * 15) : Rat) = 8 / 15) ∧
     sq (8 / 15 : Rat) = 64 / 225 ∧
     (64 / 225 : Rat) < 1 / 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M N hM hN; exact pre_post_zero_cutoff_sq_ratio hM hN
  · refine ⟨⟨by grind, ?_⟩, ⟨by grind, ?_⟩⟩
    · have h : sq (5 : Rat) = 25 := by unfold sq; grind
      rw [h]; decide
    · have h : sq (3 : Rat) = 9 := by unfold sq; grind
      rw [h]; decide
  · intro M N x uhat hM hN hx herr; exact pre_sq_err_bound hM hN hx herr
  · intro M N x hM hN; exact pre_beats_post_iff hM hN
  · grind
  · intro M N c hM hN hc; exact pre_post_outlier_ratio hM hN hc
  · refine ⟨by grind, by unfold sq; grind, ?_⟩
    apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 225) (by decide : (0 : Rat) < 3)
    have h1 : (64 : Rat) * 3 = 192 := by grind
    have h2 : (1 : Rat) * 225 = 225 := by grind
    rw [h1, h2]; decide

theorem fp_sq_err_identity (u delta : Rat) :
    sq (u * (1 + delta)) - sq u = sq u * (2 * delta + sq delta) ∧
    sq (u * (1 + delta)) - sq u = sq u * delta * (2 + delta) := by
  unfold sq
  constructor <;> grind

theorem fp_sq_err_ratio_bounds {delta eps : Rat}
    (heps_lt : eps < 2) (hdelta : ratAbs delta ≤ eps) :
    sq (2 - eps) ≤ sq (2 + delta) ∧ sq (2 + delta) ≤ sq (2 + eps) := by
  have hb := ratAbs_le_iff.mp hdelta
  have h2me_nonneg : (0 : Rat) ≤ 2 - eps := rat_sub_nonneg (Rat.le_of_lt heps_lt)
  have h1 : 2 - eps ≤ 2 + delta := by
    have := (Rat.add_le_add_right (c := (2 : Rat))).mpr hb.1
    grind
  have h2 : 2 + delta ≤ 2 + eps := by
    have := (Rat.add_le_add_right (c := (2 : Rat))).mpr hb.2
    grind
  have h2pd_nonneg : (0 : Rat) ≤ 2 + delta := Rat.le_trans h2me_nonneg h1
  exact ⟨rat_sq_le_sq_of_nonneg h2me_nonneg h1, rat_sq_le_sq_of_nonneg h2pd_nonneg h2⟩

theorem fp_sq_err_pointwise_mse {u delta eps : Rat}
    (heps_lt : eps < 2) (hdelta : ratAbs delta ≤ eps) :
    sq (2 - eps) * sq (sq u * delta) ≤ sq (sq (u * (1 + delta)) - sq u) ∧
    sq (sq (u * (1 + delta)) - sq u) ≤ sq (2 + eps) * sq (sq u * delta) := by
  have hb := fp_sq_err_ratio_bounds heps_lt hdelta
  have hid : sq (sq (u * (1 + delta)) - sq u) = sq (2 + delta) * sq (sq u * delta) := by
    unfold sq; grind
  rw [hid]
  have hnonneg : (0 : Rat) ≤ sq (sq u * delta) := rat_sq_nonneg _
  exact ⟨rat_mul_le_mul_of_nonneg_right hb.1 hnonneg,
         rat_mul_le_mul_of_nonneg_right hb.2 hnonneg⟩

theorem fp_sq_err_dataset_mse {n : Nat} (u delta : Fin n → Rat) {eps : Rat}
    (heps_lt : eps < 2) (hdelta : ∀ i, ratAbs (delta i) ≤ eps) :
    sq (2 - eps) * finSum (fun i => sq (sq (u i) * delta i)) ≤
      finSum (fun i => sq (sq (u i * (1 + delta i)) - sq (u i))) ∧
    finSum (fun i => sq (sq (u i * (1 + delta i)) - sq (u i))) ≤
      sq (2 + eps) * finSum (fun i => sq (sq (u i) * delta i)) := by
  rw [← finSum_mul_left, ← finSum_mul_left]
  constructor
  · exact finSum_le_finSum (fun i => (fp_sq_err_pointwise_mse heps_lt (hdelta i)).1)
  · exact finSum_le_finSum (fun i => (fp_sq_err_pointwise_mse heps_lt (hdelta i)).2)

theorem relu2_quantization_order_fp_post_beats_pre_exact_4x :
    (∀ u delta : Rat,
      sq (u * (1 + delta)) - sq u = sq u * (2 * delta + sq delta) ∧
      sq (u * (1 + delta)) - sq u = sq u * delta * (2 + delta)) ∧
    (∀ u delta : Rat, u ≠ 0 → delta ≠ 0 →
      sq (sq (u * (1 + delta)) - sq u) / sq (sq u * delta) = sq (2 + delta)) ∧
    (∀ delta eps : Rat, eps < 2 → ratAbs delta ≤ eps →
      sq (2 - eps) ≤ sq (2 + delta) ∧ sq (2 + delta) ≤ sq (2 + eps)) ∧
    (∀ (n : Nat) (u delta : Fin n → Rat) (eps : Rat),
      eps < 2 → (∀ i, ratAbs (delta i) ≤ eps) →
      sq (2 - eps) * finSum (fun i => sq (sq (u i) * delta i)) ≤
        finSum (fun i => sq (sq (u i * (1 + delta i)) - sq (u i))) ∧
      finSum (fun i => sq (sq (u i * (1 + delta i)) - sq (u i))) ≤
        sq (2 + eps) * finSum (fun i => sq (sq (u i) * delta i))) ∧
    (sq (2 - (0 : Rat)) = 4 ∧ sq (2 + (0 : Rat)) = 4 ∧
     sq (2 - (1 / 16 : Rat)) = 961 / 256 ∧
     sq (2 + (1 / 16 : Rat)) = 1089 / 256 ∧
     (961 / 256 : Rat) < 391 / 100 ∧
     (391 / 100 : Rat) < 1089 / 256) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u delta; exact fp_sq_err_identity u delta
  · intro u delta hu hd
    have hsq_u_ne : sq u ≠ 0 := by
      unfold sq; intro h; cases Rat.mul_eq_zero.mp h <;> exact hu ‹_›
    have hden_ne : sq (sq u * delta) ≠ 0 := by
      unfold sq
      intro h
      cases Rat.mul_eq_zero.mp h with
      | inl h1 | inr h1 =>
        cases Rat.mul_eq_zero.mp h1 with
        | inl h2 => exact hsq_u_ne h2
        | inr h2 => exact hd h2
    rw [rat_div_eq_iff hden_ne]
    unfold sq; grind
  · intro delta eps heps hdelta; exact fp_sq_err_ratio_bounds heps hdelta
  · intro n u delta eps heps hdelta; exact fp_sq_err_dataset_mse u delta heps hdelta
  · refine ⟨by unfold sq; grind, by unfold sq; grind,
            by unfold sq; grind, by unfold sq; grind, ?_, ?_⟩
    · apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 256) (by decide : (0 : Rat) < 100)
      have h1 : (961 : Rat) * 100 = 96100 := by grind
      have h2 : (391 : Rat) * 256 = 100096 := by grind
      rw [h1, h2]; decide
    · apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 100) (by decide : (0 : Rat) < 256)
      have h1 : (391 : Rat) * 256 = 100096 := by grind
      have h2 : (1089 : Rat) * 100 = 108900 := by grind
      rw [h1, h2]; decide

end Relu2TealDeadzone
