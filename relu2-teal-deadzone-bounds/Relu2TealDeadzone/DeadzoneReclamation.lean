/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relu2TealDeadzone.RatOrder

/-!
# Theorems 4 & 5: `TEAL` / `CATS` Shifted Deadzone Reclamation (Uniform & Floating-Point)

- **Theorem 4 (`teal_cats_shifted_deadzone_reclamation_uniform_exact`)**:
  For `TEAL` / `CATS` activation sparsity with pruning threshold `τ ∈ (0, M)` and `N > 0`
  uniform levels:
  1. Reclaiming the pruned deadzone `[0, τ)` shrinks the uniform step size by exact
     `(1 - τ / M)`: `shiftedStep M tau N = (1 - tau / M) * uniformStep M N`.
  2. Worst-case half-step error shrinks by `(1 - τ / M)` and worst-case squared quantization
     error shrinks by exact `(1 - τ / M)^(-2)`:
     `sq (stdHalfStep M N) / sq (shiftedHalfStep M tau N) = 1 / sq (1 - tau / M)`
     and `sq (shiftedHalfStep M tau N) < sq (stdHalfStep M N)`.
  3. Sign-preserving reconstruction `tealShiftedRecon tau x q = sign(x) * (τ + q)` has exact
     error `|tealShiftedRecon tau x q - x| = |q - (|x| - τ)|` for all `|x| ≥ τ` (using `0`
     extra bits).
  4. Concrete certified checkpoints: `4×` at `τ = M / 2`, `16×` at `τ = 3M / 4`, `64×` at
     `τ = 7M / 8`.

- **Theorem 5 (`teal_cats_fp_superquadratic_logarithmic_density_bonus`)**:
  For floating-point formats (`MXFP4`, `NVFP4`, `FP8-E4M3`) with relative bin spacing `u > 0`,
  shifting `x ∈ (τ, M]` to `y = x - τ`:
  1. Cuts local FP step width by exact `(x - τ) / x`, and its ratio to the uniform factor
     `(1 - τ / M)` is `((x - τ) / x) / (1 - τ / M) = ((x - τ) * M) / (x * (M - τ))`.
  2. Exact gap identity: `(1 - τ / M) - (x - τ) / x = τ * (M - x) / (M * x) > 0` for EVERY
     `x ∈ (τ, M)`.
  3. Therefore, for EVERY `x ∈ (τ, M)`:
     `((x - τ) / x) * (M / (M - τ)) < 1` and
     `sq (fpLocalStep u x) / sq (fpLocalStep u (x - τ)) > 1 / sq (1 - τ / M)` (strictly
     super-quadratic MSE reduction across the entire active interior!).
  4. Finite-dataset lift: for any `n` active samples `x_i ∈ (τ, M]` with at least one
     interior sample `x_j < M`,
     `finSum (fun i => sq (fpLocalStep u (x i - tau))) < sq (1 - tau / M) * finSum (fun i => sq (fpLocalStep u (x i)))`.
-/

namespace Relu2TealDeadzone

theorem one_sub_div_eq {M tau : Rat} (hM : M ≠ 0) :
    1 - tau / M = (M - tau) / M := by
  symm
  rw [rat_div_eq_iff hM]
  have hc : (tau / M) * M = tau := rat_div_mul_cancel hM
  grind

theorem shiftedStep_eq_factor {M tau N : Rat} (hM : (0 : Rat) < M) (hN : (0 : Rat) < N) :
    shiftedStep M tau N = (1 - tau / M) * uniformStep M N := by
  unfold shiftedStep uniformStep
  have hMne : M ≠ 0 := Rat.ne_of_gt hM
  have hNne : N ≠ 0 := Rat.ne_of_gt hN
  rw [one_sub_div_eq hMne]
  have hMNpos : (0 : Rat) < M * N := rat_mul_pos hM hN
  have hc1 : ((M - tau) / N) * N = M - tau := rat_div_mul_cancel hNne
  have hc2 : ((M - tau) / M) * M = M - tau := rat_div_mul_cancel hMne
  have hc3 : (M / N) * N = M := rat_div_mul_cancel hNne
  have hmul : ((M - tau) / N) * (M * N) = (((M - tau) / M) * (M / N)) * (M * N) := by
    have hL : ((M - tau) / N) * (M * N) = (((M - tau) / N) * N) * M := by grind
    have hR : (((M - tau) / M) * (M / N)) * (M * N) =
        (((M - tau) / M) * M) * ((M / N) * N) := by grind
    rw [hL, hR, hc1, hc2, hc3]
  exact Rat.le_antisymm
    (rat_le_of_mul_pos_right hMNpos (by rw [hmul]; exact Rat.le_refl))
    (rat_le_of_mul_pos_right hMNpos (by rw [← hmul]; exact Rat.le_refl))

theorem shiftedHalfStep_eq_factor {M tau N : Rat} (hM : (0 : Rat) < M) (hN : (0 : Rat) < N) :
    shiftedHalfStep M tau N = (1 - tau / M) * stdHalfStep M N := by
  unfold shiftedHalfStep stdHalfStep
  have h2N : (0 : Rat) < 2 * N := rat_mul_pos (by decide) hN
  exact shiftedStep_eq_factor hM h2N

theorem std_over_shifted_sq_exact {M tau N : Rat}
    (hM : (0 : Rat) < M) (htau_lt : tau < M) (hN : (0 : Rat) < N) :
    sq (stdHalfStep M N) / sq (shiftedHalfStep M tau N) = 1 / sq (1 - tau / M) := by
  have hMne : M ≠ 0 := Rat.ne_of_gt hM
  have hMmt : (0 : Rat) < M - tau := rat_sub_pos htau_lt
  have hfac_pos : (0 : Rat) < 1 - tau / M := by
    rw [one_sub_div_eq hMne]
    exact rat_div_pos hMmt hM
  have hstd_pos : (0 : Rat) < stdHalfStep M N := by
    unfold stdHalfStep
    exact rat_div_pos hM (rat_mul_pos (by decide) hN)
  have hsh_eq : shiftedHalfStep M tau N = (1 - tau / M) * stdHalfStep M N :=
    shiftedHalfStep_eq_factor hM hN
  have hsh_pos : (0 : Rat) < shiftedHalfStep M tau N := by
    rw [hsh_eq]; exact rat_mul_pos hfac_pos hstd_pos
  have hden1 : sq (shiftedHalfStep M tau N) ≠ 0 := Rat.ne_of_gt (rat_sq_pos hsh_pos)
  have hden2 : sq (1 - tau / M) ≠ 0 := Rat.ne_of_gt (rat_sq_pos hfac_pos)
  rw [rat_div_eq_iff hden1]
  rw [hsh_eq]
  have hsq_mul : sq ((1 - tau / M) * stdHalfStep M N) =
      sq (1 - tau / M) * sq (stdHalfStep M N) := by unfold sq; grind
  rw [hsq_mul]
  have hc : (1 / sq (1 - tau / M)) * sq (1 - tau / M) = 1 := rat_div_mul_cancel hden2
  have eq : 1 / sq (1 - tau / M) * (sq (1 - tau / M) * sq (stdHalfStep M N)) =
      (1 / sq (1 - tau / M) * sq (1 - tau / M)) * sq (stdHalfStep M N) := by grind
  rw [eq, hc]
  grind

theorem teal_shifted_recon_err_exact (tau x q : Rat) :
    ratAbs (tealShiftedRecon tau x q - x) = ratAbs (q - (ratAbs x - tau)) := by
  unfold tealShiftedRecon ratAbs
  split
  · rename_i hx
    have eq : tau + q - x = q - (x - tau) := by grind
    rw [eq]
  · rename_i hx
    have eq : -(tau + q) - x = -(q - (-x - tau)) := by grind
    rw [eq]
    exact ratAbs_neg (q - (-x - tau))

theorem teal_cats_shifted_deadzone_reclamation_uniform_exact :
    (∀ M tau N : Rat, (0 : Rat) < M → (0 : Rat) < tau → tau < M → (0 : Rat) < N →
      shiftedStep M tau N = (1 - tau / M) * uniformStep M N ∧
      shiftedHalfStep M tau N = (1 - tau / M) * stdHalfStep M N ∧
      shiftedStep M tau N < uniformStep M N ∧
      sq (shiftedHalfStep M tau N) < sq (stdHalfStep M N) ∧
      sq (stdHalfStep M N) / sq (shiftedHalfStep M tau N) = 1 / sq (1 - tau / M)) ∧
    (∀ tau x q : Rat,
      ratAbs (tealShiftedRecon tau x q - x) = ratAbs (q - (ratAbs x - tau))) ∧
    ((1 / sq (1 - (1 / 2 : Rat)) : Rat) = 4 ∧
     (1 / sq (1 - (3 / 4 : Rat)) : Rat) = 16 ∧
     (1 / sq (1 - (7 / 8 : Rat)) : Rat) = 64) := by
  refine ⟨?_, ?_, ?_⟩
  · intro M tau N hM htau htau_lt hN
    have hstep := shiftedStep_eq_factor (tau := tau) hM hN
    have hhalf := shiftedHalfStep_eq_factor (tau := tau) hM hN
    have hratio := std_over_shifted_sq_exact hM htau_lt hN
    have hMmt_lt : M - tau < M := by
      apply rat_lt_of_sub_pos
      have eq : M - (M - tau) = tau := by grind
      rw [eq]; exact htau
    have hstep_lt : shiftedStep M tau N < uniformStep M N := by
      unfold shiftedStep uniformStep
      exact rat_div_lt_div_of_pos_right hMmt_lt hN
    have hhalf_lt : shiftedHalfStep M tau N < stdHalfStep M N := by
      unfold shiftedHalfStep stdHalfStep
      exact rat_div_lt_div_of_pos_right hMmt_lt (rat_mul_pos (by decide) hN)
    have hhalf_nonneg : (0 : Rat) ≤ shiftedHalfStep M tau N := by
      unfold shiftedHalfStep
      exact rat_div_nonneg (Rat.le_of_lt (rat_sub_pos htau_lt)) (rat_mul_pos (by decide) hN)
    have hsq_lt : sq (shiftedHalfStep M tau N) < sq (stdHalfStep M N) :=
      rat_sq_lt_sq_of_nonneg hhalf_nonneg hhalf_lt
    exact ⟨hstep, hhalf, hstep_lt, hsq_lt, hratio⟩
  · intro tau x q; exact teal_shifted_recon_err_exact tau x q
  · unfold sq; refine ⟨by grind, by grind, by grind⟩

theorem fp_shift_gap_identity {M tau x : Rat} (hM : (0 : Rat) < M) (hx : (0 : Rat) < x) :
    (1 - tau / M) - (x - tau) / x = (tau * (M - x)) / (M * x) := by
  have hMne : M ≠ 0 := Rat.ne_of_gt hM
  have hxne : x ≠ 0 := Rat.ne_of_gt hx
  have hMxpos : (0 : Rat) < M * x := rat_mul_pos hM hx
  have hMxne : M * x ≠ 0 := Rat.ne_of_gt hMxpos
  symm
  rw [rat_div_eq_iff hMxne]
  have hc1 : (tau / M) * M = tau := rat_div_mul_cancel hMne
  have hc2 : ((x - tau) / x) * x = x - tau := rat_div_mul_cancel hxne
  have eq : ((1 - tau / M) - (x - tau) / x) * (M * x) =
      M * x - ((tau / M) * M) * x - (((x - tau) / x) * x) * M := by grind
  rw [eq, hc1, hc2]
  grind

theorem fp_shift_ratio_lt_one {M tau x : Rat}
    (htau : (0 : Rat) < tau) (htau_x : tau < x) (hx_M : x < M) :
    ((x - tau) / x) * (M / (M - tau)) < 1 := by
  have hx : (0 : Rat) < x := rat_lt_trans htau htau_x
  have hM : (0 : Rat) < M := rat_lt_trans hx hx_M
  have hMmt : (0 : Rat) < M - tau := rat_sub_pos (rat_lt_trans htau_x hx_M)
  have hxne : x ≠ 0 := Rat.ne_of_gt hx
  have hMmtne : M - tau ≠ 0 := Rat.ne_of_gt hMmt
  have hden : (0 : Rat) < x * (M - tau) := rat_mul_pos hx hMmt
  apply rat_lt_of_mul_pos_right hden
  have hc1 : ((x - tau) / x) * x = x - tau := rat_div_mul_cancel hxne
  have hc2 : (M / (M - tau)) * (M - tau) = M := rat_div_mul_cancel hMmtne
  have hL : (((x - tau) / x) * (M / (M - tau))) * (x * (M - tau)) =
      (((x - tau) / x) * x) * ((M / (M - tau)) * (M - tau)) := by grind
  rw [hL, hc1, hc2]
  apply rat_lt_of_sub_pos
  have eq : 1 * (x * (M - tau)) - (x - tau) * M = tau * (M - x) := by grind
  rw [eq]
  exact rat_mul_pos htau (rat_sub_pos hx_M)

theorem fp_shift_pointwise_le {u M tau x : Rat}
    (htau : (0 : Rat) < tau) (htau_x : tau < x) (hx_M : x ≤ M) :
    sq (fpLocalStep u (x - tau)) ≤ sq (1 - tau / M) * sq (fpLocalStep u x) := by
  have hx : (0 : Rat) < x := rat_lt_trans htau htau_x
  have hM : (0 : Rat) < M := rat_lt_of_lt_of_le hx hx_M
  have hgap := fp_shift_gap_identity (tau := tau) hM hx
  have hgap_nonneg : (0 : Rat) ≤ (1 - tau / M) - (x - tau) / x := by
    rw [hgap]
    exact rat_div_nonneg (Rat.mul_nonneg (Rat.le_of_lt htau) (rat_sub_nonneg hx_M))
      (rat_mul_pos hM hx)
  have hle : (x - tau) / x ≤ 1 - tau / M := rat_le_of_sub_nonneg hgap_nonneg
  have hnonneg : (0 : Rat) ≤ (x - tau) / x :=
    rat_div_nonneg (Rat.le_of_lt (rat_sub_pos htau_x)) hx
  have hsq_le : sq ((x - tau) / x) ≤ sq (1 - tau / M) := rat_sq_le_sq_of_nonneg hnonneg hle
  have hprod := rat_mul_le_mul_of_nonneg_right hsq_le (rat_sq_nonneg (fpLocalStep u x))
  have hident : sq ((x - tau) / x) * sq (fpLocalStep u x) = sq (fpLocalStep u (x - tau)) := by
    unfold fpLocalStep sq
    have hxne : x ≠ 0 := Rat.ne_of_gt hx
    have hc : ((x - tau) / x) * x = x - tau := rat_div_mul_cancel hxne
    have eq : ((x - tau) / x * ((x - tau) / x)) * (u * x * (u * x)) =
        u * (((x - tau) / x) * x) * (u * (((x - tau) / x) * x)) := by grind
    rw [eq, hc]
  rw [hident] at hprod
  exact hprod

theorem fp_shift_pointwise_lt {u M tau x : Rat}
    (hu : (0 : Rat) < u) (htau : (0 : Rat) < tau) (htau_x : tau < x) (hx_M : x < M) :
    sq (fpLocalStep u (x - tau)) < sq (1 - tau / M) * sq (fpLocalStep u x) := by
  have hx : (0 : Rat) < x := rat_lt_trans htau htau_x
  have hM : (0 : Rat) < M := rat_lt_trans hx hx_M
  have hgap := fp_shift_gap_identity (tau := tau) hM hx
  have hgap_pos : (0 : Rat) < (1 - tau / M) - (x - tau) / x := by
    rw [hgap]
    exact rat_div_pos (rat_mul_pos htau (rat_sub_pos hx_M)) (rat_mul_pos hM hx)
  have hlt : (x - tau) / x < 1 - tau / M := rat_lt_of_sub_pos hgap_pos
  have hnonneg : (0 : Rat) ≤ (x - tau) / x :=
    rat_div_nonneg (Rat.le_of_lt (rat_sub_pos htau_x)) hx
  have hsq_lt : sq ((x - tau) / x) < sq (1 - tau / M) := rat_sq_lt_sq_of_nonneg hnonneg hlt
  have hux_pos : (0 : Rat) < sq (fpLocalStep u x) := by
    unfold fpLocalStep
    exact rat_sq_pos (rat_mul_pos hu hx)
  have hprod := rat_mul_lt_mul_of_pos_right hsq_lt hux_pos
  have hident : sq ((x - tau) / x) * sq (fpLocalStep u x) = sq (fpLocalStep u (x - tau)) := by
    unfold fpLocalStep sq
    have hxne : x ≠ 0 := Rat.ne_of_gt hx
    have hc : ((x - tau) / x) * x = x - tau := rat_div_mul_cancel hxne
    have eq : ((x - tau) / x * ((x - tau) / x)) * (u * x * (u * x)) =
        u * (((x - tau) / x) * x) * (u * (((x - tau) / x) * x)) := by grind
    rw [eq, hc]
  rw [hident] at hprod
  exact hprod

theorem teal_cats_fp_superquadratic_logarithmic_density_bonus :
    (∀ M tau x : Rat, (0 : Rat) < M → (0 : Rat) < x →
      (1 - tau / M) - (x - tau) / x = (tau * (M - x)) / (M * x)) ∧
    (∀ M tau x : Rat, (0 : Rat) < tau → tau < x → x < M →
      ((x - tau) / x) * (M / (M - tau)) < 1 ∧
      (x - tau) / x < 1 - tau / M) ∧
    (∀ u M tau x : Rat, (0 : Rat) < u → (0 : Rat) < tau → tau < x → x < M →
      1 / sq (1 - tau / M) < sq (fpLocalStep u x) / sq (fpLocalStep u (x - tau))) ∧
    (∀ u M tau : Rat, (0 : Rat) < u → (0 : Rat) < tau → tau < M →
      sq (fpLocalStep u M) / sq (fpLocalStep u (M - tau)) = 1 / sq (1 - tau / M)) ∧
    (∀ (n : Nat) (x : Fin n → Rat) (u M tau : Rat),
      (0 : Rat) < u → (0 : Rat) < tau →
      (∀ i, tau < x i ∧ x i ≤ M) →
      (∃ j, x j < M) →
      finSum (fun i => sq (fpLocalStep u (x i - tau))) <
        sq (1 - tau / M) * finSum (fun i => sq (fpLocalStep u (x i)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M tau x hM hx; exact fp_shift_gap_identity hM hx
  · intro M tau x htau htau_x hx_M
    have hx : (0 : Rat) < x := rat_lt_trans htau htau_x
    have hM : (0 : Rat) < M := rat_lt_trans hx hx_M
    refine ⟨fp_shift_ratio_lt_one htau htau_x hx_M, ?_⟩
    apply rat_lt_of_sub_pos
    rw [fp_shift_gap_identity hM hx]
    exact rat_div_pos (rat_mul_pos htau (rat_sub_pos hx_M)) (rat_mul_pos hM hx)
  · intro u M tau x hu htau htau_x hx_M
    have hx : (0 : Rat) < x := rat_lt_trans htau htau_x
    have hM : (0 : Rat) < M := rat_lt_trans hx hx_M
    have hMmt : (0 : Rat) < M - tau := rat_sub_pos (rat_lt_trans htau_x hx_M)
    have hfac_pos : (0 : Rat) < 1 - tau / M := by
      rw [one_sub_div_eq (Rat.ne_of_gt hM)]
      exact rat_div_pos hMmt hM
    have hsh_pos : (0 : Rat) < sq (fpLocalStep u (x - tau)) := by
      unfold fpLocalStep
      exact rat_sq_pos (rat_mul_pos hu (rat_sub_pos htau_x))
    have hfac_sq_pos : (0 : Rat) < sq (1 - tau / M) := rat_sq_pos hfac_pos
    have hpt := fp_shift_pointwise_lt hu htau htau_x hx_M
    apply rat_lt_of_mul_pos_right (rat_mul_pos hfac_sq_pos hsh_pos)
    have hc1 : (1 / sq (1 - tau / M)) * sq (1 - tau / M) = 1 :=
      rat_div_mul_cancel (Rat.ne_of_gt hfac_sq_pos)
    have hc2 : (sq (fpLocalStep u x) / sq (fpLocalStep u (x - tau))) *
        sq (fpLocalStep u (x - tau)) = sq (fpLocalStep u x) :=
      rat_div_mul_cancel (Rat.ne_of_gt hsh_pos)
    have hL : (1 / sq (1 - tau / M)) * (sq (1 - tau / M) * sq (fpLocalStep u (x - tau))) =
        ((1 / sq (1 - tau / M)) * sq (1 - tau / M)) * sq (fpLocalStep u (x - tau)) := by grind
    have hR : (sq (fpLocalStep u x) / sq (fpLocalStep u (x - tau))) *
        (sq (1 - tau / M) * sq (fpLocalStep u (x - tau))) =
        sq (1 - tau / M) *
          ((sq (fpLocalStep u x) / sq (fpLocalStep u (x - tau))) * sq (fpLocalStep u (x - tau))) := by
      grind
    rw [hL, hR, hc1, hc2, Rat.one_mul]
    exact hpt
  · intro u M tau hu htau htau_lt
    have hM : (0 : Rat) < M := rat_lt_trans htau htau_lt
    have hMne : M ≠ 0 := Rat.ne_of_gt hM
    have hMmt : (0 : Rat) < M - tau := rat_sub_pos htau_lt
    have hsh_pos : (0 : Rat) < sq (fpLocalStep u (M - tau)) := by
      unfold fpLocalStep; exact rat_sq_pos (rat_mul_pos hu hMmt)
    have hfac_pos : (0 : Rat) < 1 - tau / M := by
      rw [one_sub_div_eq hMne]; exact rat_div_pos hMmt hM
    have hfac_sq_pos : (0 : Rat) < sq (1 - tau / M) := rat_sq_pos hfac_pos
    rw [rat_div_eq_iff (Rat.ne_of_gt hsh_pos)]
    have hc : (1 / sq (1 - tau / M)) * sq (1 - tau / M) = 1 :=
      rat_div_mul_cancel (Rat.ne_of_gt hfac_sq_pos)
    have hfac_mul : (1 - tau / M) * M = M - tau := by
      rw [one_sub_div_eq hMne]; exact rat_div_mul_cancel hMne
    have hsq_eq : sq (fpLocalStep u (M - tau)) = sq (1 - tau / M) * sq (fpLocalStep u M) := by
      unfold fpLocalStep sq
      have eq : u * (M - tau) * (u * (M - tau)) =
          u * ((1 - tau / M) * M) * (u * ((1 - tau / M) * M)) := by rw [hfac_mul]
      rw [eq]; grind
    rw [hsq_eq]
    have eq : 1 / sq (1 - tau / M) * (sq (1 - tau / M) * sq (fpLocalStep u M)) =
        (1 / sq (1 - tau / M) * sq (1 - tau / M)) * sq (fpLocalStep u M) := by grind
    rw [eq, hc]; grind
  · intro n x u M tau hu htau hbounds hj
    rw [← finSum_mul_left]
    apply finSum_lt_finSum
    · intro i
      exact fp_shift_pointwise_le htau (hbounds i).1 (hbounds i).2
    · rcases hj with ⟨j, hjM⟩
      exact ⟨j, fp_shift_pointwise_lt hu htau (hbounds j).1 hjM⟩

end Relu2TealDeadzone
