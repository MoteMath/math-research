/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relu2TealDeadzone.RatOrder

/-!
# Theorem 6: Prune-Before-Quantize Mask-Flip Zone & `uint64_t` Bitmask Sparsity Crossover

Proves:
1. **Threshold-Tie Mask-Flip Zone (Quantize-Before-Prune vs Prune-Before-Quantize):**
   - For any uniform grid step `Δ > 0`, lower grid level `g : Rat`, and threshold
     `τ ∈ [g, g + Δ]` with bin midpoint `mid = g + Δ / 2`:
     - If `τ < mid`, EVERY `x ∈ [τ, mid)` is kept by prune-before-quantize (`pruneMask τ x = true`)
       yet pruned by quantize-before-prune (`pruneMask τ (uniformGridRound Δ g x) = false`),
       and lies inside `[τ - Δ/2, τ + Δ/2)`.
     - If `mid ≤ τ`, EVERY `x ∈ [mid, τ)` is pruned by prune-before-quantize (`pruneMask τ x = false`)
       yet kept by quantize-before-prune (`pruneMask τ (uniformGridRound Δ g x) = true`),
       and lies inside `[τ - Δ/2, τ + Δ/2)`.
   - In particular, for any grid-aligned threshold `τ = g + Δ`, every `x ∈ [τ - Δ/2, τ)`
     flips from pruned to kept (`width = Δ / 2`).
   - Conversely, prune-before-quantize evaluates `pruneMask τ x` on exact `x` identically (`0` flips).
2. **Exact `uint64_t` Bitmask Sparse `W4` `down_proj` Crossover Formula:**
   - For any `ov > 0` and `s < 1`:
     - `sparsityCrossover ov = 1 - 1 / (1 + ov) = ov / (1 + ov) ∈ (0, 1)`.
     - Exact break-even: `sparseTrafficRatio (sparsityCrossover ov) ov = 1` and
       `sparseSpeedup (sparsityCrossover ov) ov = 1`.
     - Strict speedup iff `s > sparsityCrossover ov`:
       `sparseTrafficRatio s ov < 1 ↔ sparsityCrossover ov < s` and
       `1 < sparseSpeedup s ov ↔ sparsityCrossover ov < s`.
   - Concrete `uint64_t` bitmask metadata checkpoints:
     - Pure `1/64` bitmask metadata overhead: `s* = 1/65 < 1/5` (`1.54% < 20%`).
     - Empirical `gfx1100` `INT4` overhead `ov = 3/16`: `s* = 3/19 < 1/5` (`15.79% < 20%`),
       and at `s = 3/4` (`75%`), `sparseSpeedup (3/4) (3/16) = 64/19` (`≈ 3.37×`, inside
       `2.3×–3.4×`!).
-/

namespace Relu2TealDeadzone

theorem pruneMask_eq_true {tau x : Rat} (h : tau ≤ x) : pruneMask tau x = true := by
  unfold pruneMask
  exact decide_eq_true h

theorem pruneMask_eq_false {tau x : Rat} (h : x < tau) : pruneMask tau x = false := by
  unfold pruneMask
  exact decide_eq_false (Rat.not_le.mpr h)

theorem flip_zone_lower_branch {delta g tau x : Rat}
    (hdelta : (0 : Rat) < delta) (hg_le : g < tau) (_htau_mid : tau < g + delta / 2)
    (hx_lo : tau ≤ x) (hx_hi : x < g + delta / 2) :
    pruneMask tau x = true ∧
    pruneMask tau (uniformGridRound delta g x) = false ∧
    tau - delta / 2 ≤ x ∧ x < tau + delta / 2 := by
  have hround : uniformGridRound delta g x = g := by
    unfold uniformGridRound
    simp [hx_hi]
  refine ⟨pruneMask_eq_true hx_lo, ?_, ?_, ?_⟩
  · rw [hround]
    exact pruneMask_eq_false hg_le
  · have hhalf : (0 : Rat) < delta / 2 := rat_div_pos hdelta (by decide)
    have h1 : tau - delta / 2 ≤ tau := by
      apply rat_le_of_sub_nonneg
      have eq : tau - (tau - delta / 2) = delta / 2 := by grind
      rw [eq]; exact Rat.le_of_lt hhalf
    exact Rat.le_trans h1 hx_lo
  · have h2 : g + delta / 2 < tau + delta / 2 := by
      apply rat_lt_of_sub_pos
      have eq : (tau + delta / 2) - (g + delta / 2) = tau - g := by grind
      rw [eq]; exact rat_sub_pos hg_le
    exact rat_lt_trans hx_hi h2

theorem flip_zone_upper_branch {delta g tau x : Rat}
    (hdelta : (0 : Rat) < delta) (htau_hi : tau ≤ g + delta) (_hmid_le : g + delta / 2 ≤ tau)
    (hx_lo : g + delta / 2 ≤ x) (hx_hi : x < tau) :
    pruneMask tau x = false ∧
    pruneMask tau (uniformGridRound delta g x) = true ∧
    tau - delta / 2 ≤ x ∧ x < tau + delta / 2 := by
  have hnot : ¬ (x < g + delta / 2) := Rat.not_lt.mpr hx_lo
  have hround : uniformGridRound delta g x = g + delta := by
    unfold uniformGridRound
    simp [hnot]
  refine ⟨pruneMask_eq_false hx_hi, ?_, ?_, ?_⟩
  · rw [hround]
    exact pruneMask_eq_true htau_hi
  · have h1 : tau - delta / 2 ≤ g + delta / 2 := by
      apply rat_le_of_sub_nonneg
      have hsub := rat_sub_nonneg htau_hi
      have eq : (g + delta / 2) - (tau - delta / 2) = (g + delta) - tau := by grind
      rw [eq]; exact hsub
    exact Rat.le_trans h1 hx_lo
  · have hhalf : (0 : Rat) < delta / 2 := rat_div_pos hdelta (by decide)
    have h2 : tau < tau + delta / 2 := by
      apply rat_lt_of_sub_pos
      have eq : (tau + delta / 2) - tau = delta / 2 := by grind
      rw [eq]; exact hhalf
    exact rat_lt_trans hx_hi h2

theorem sparsityCrossover_eq_div {ov : Rat} (hov : (0 : Rat) < ov) :
    sparsityCrossover ov = ov / (1 + ov) := by
  unfold sparsityCrossover
  have h1ov_pos : (0 : Rat) < 1 + ov := rat_add_pos_of_pos_of_nonneg (by decide) (Rat.le_of_lt hov)
  have h1ov_ne : 1 + ov ≠ 0 := Rat.ne_of_gt h1ov_pos
  symm
  rw [rat_div_eq_iff h1ov_ne]
  have hc : (1 / (1 + ov)) * (1 + ov) = 1 := rat_div_mul_cancel h1ov_ne
  have eq : (1 - 1 / (1 + ov)) * (1 + ov) = (1 + ov) - (1 / (1 + ov)) * (1 + ov) := by grind
  rw [eq, hc]
  grind

theorem sparsityCrossover_bounds {ov : Rat} (hov : (0 : Rat) < ov) :
    (0 : Rat) < sparsityCrossover ov ∧ sparsityCrossover ov < 1 := by
  rw [sparsityCrossover_eq_div hov]
  have h1ov_pos : (0 : Rat) < 1 + ov := rat_add_pos_of_pos_of_nonneg (by decide) (Rat.le_of_lt hov)
  refine ⟨rat_div_pos hov h1ov_pos, ?_⟩
  apply rat_div_lt_of_mul_lt h1ov_pos
  apply rat_lt_of_sub_pos
  have eq : 1 * (1 + ov) - ov = 1 := by grind
  rw [eq]; decide

theorem sparseTrafficRatio_at_crossover {ov : Rat} (hov : (0 : Rat) < ov) :
    sparseTrafficRatio (sparsityCrossover ov) ov = 1 ∧
    sparseSpeedup (sparsityCrossover ov) ov = 1 := by
  have h1ov_pos : (0 : Rat) < 1 + ov := rat_add_pos_of_pos_of_nonneg (by decide) (Rat.le_of_lt hov)
  have h1ov_ne : 1 + ov ≠ 0 := Rat.ne_of_gt h1ov_pos
  have htr : sparseTrafficRatio (sparsityCrossover ov) ov = 1 := by
    unfold sparseTrafficRatio sparsityCrossover
    have eq : (1 - (1 - 1 / (1 + ov))) * (1 + ov) = (1 / (1 + ov)) * (1 + ov) := by grind
    rw [eq, rat_div_mul_cancel h1ov_ne]
  refine ⟨htr, ?_⟩
  unfold sparseSpeedup
  rw [htr]
  grind

theorem sparseTrafficRatio_lt_one_iff {s ov : Rat} (hov : (0 : Rat) < ov) :
    sparseTrafficRatio s ov < 1 ↔ sparsityCrossover ov < s := by
  unfold sparseTrafficRatio sparsityCrossover
  have h1ov_pos : (0 : Rat) < 1 + ov := rat_add_pos_of_pos_of_nonneg (by decide) (Rat.le_of_lt hov)
  have h1ov_ne : 1 + ov ≠ 0 := Rat.ne_of_gt h1ov_pos
  have hc : (1 / (1 + ov)) * (1 + ov) = 1 := rat_div_mul_cancel h1ov_ne
  constructor
  · intro h
    apply rat_lt_of_mul_pos_right h1ov_pos
    have hL : (1 - 1 / (1 + ov)) * (1 + ov) = ov := by
      have eq : (1 - 1 / (1 + ov)) * (1 + ov) = (1 + ov) - (1 / (1 + ov)) * (1 + ov) := by grind
      rw [eq, hc]; grind
    rw [hL]
    apply rat_lt_of_sub_pos
    have hsub := rat_sub_pos h
    have eq : s * (1 + ov) - ov = 1 - (1 - s) * (1 + ov) := by grind
    rw [eq]; exact hsub
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h h1ov_pos
    have hL : (1 - 1 / (1 + ov)) * (1 + ov) = ov := by
      have eq : (1 - 1 / (1 + ov)) * (1 + ov) = (1 + ov) - (1 / (1 + ov)) * (1 + ov) := by grind
      rw [eq, hc]; grind
    rw [hL] at hmul
    apply rat_lt_of_sub_pos
    have hsub := rat_sub_pos hmul
    have eq : 1 - (1 - s) * (1 + ov) = s * (1 + ov) - ov := by grind
    rw [eq]; exact hsub

theorem sparseSpeedup_gt_one_iff {s ov : Rat} (hs : s < 1) (hov : (0 : Rat) < ov) :
    (1 : Rat) < sparseSpeedup s ov ↔ sparsityCrossover ov < s := by
  rw [← sparseTrafficRatio_lt_one_iff hov]
  unfold sparseSpeedup
  have h1ms : (0 : Rat) < 1 - s := rat_sub_pos hs
  have h1ov : (0 : Rat) < 1 + ov := rat_add_pos_of_pos_of_nonneg (by decide) (Rat.le_of_lt hov)
  have htr_pos : (0 : Rat) < sparseTrafficRatio s ov := by
    unfold sparseTrafficRatio
    exact rat_mul_pos h1ms h1ov
  have htr_ne : sparseTrafficRatio s ov ≠ 0 := Rat.ne_of_gt htr_pos
  constructor
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h htr_pos
    rw [Rat.one_mul, rat_div_mul_cancel htr_ne] at hmul
    exact hmul
  · intro h
    apply rat_lt_div_of_mul_lt htr_pos
    rw [Rat.one_mul]
    exact h

theorem prune_before_quantize_mask_flip_and_bitmask_crossover :
    (∀ delta g tau x : Rat, (0 : Rat) < delta → g < tau → tau < g + delta / 2 →
      tau ≤ x → x < g + delta / 2 →
      pruneMask tau x = true ∧
      pruneMask tau (uniformGridRound delta g x) = false ∧
      tau - delta / 2 ≤ x ∧ x < tau + delta / 2) ∧
    (∀ delta g tau x : Rat, (0 : Rat) < delta → tau ≤ g + delta → g + delta / 2 ≤ tau →
      g + delta / 2 ≤ x → x < tau →
      pruneMask tau x = false ∧
      pruneMask tau (uniformGridRound delta g x) = true ∧
      tau - delta / 2 ≤ x ∧ x < tau + delta / 2) ∧
    (∀ delta g x : Rat, (0 : Rat) < delta →
      (g + delta) - delta / 2 ≤ x → x < g + delta →
      pruneMask (g + delta) x = false ∧
      pruneMask (g + delta) (uniformGridRound delta g x) = true) ∧
    (∀ ov : Rat, (0 : Rat) < ov →
      sparsityCrossover ov = ov / (1 + ov) ∧
      (0 : Rat) < sparsityCrossover ov ∧ sparsityCrossover ov < 1 ∧
      sparseTrafficRatio (sparsityCrossover ov) ov = 1 ∧
      sparseSpeedup (sparsityCrossover ov) ov = 1) ∧
    (∀ s ov : Rat, s < 1 → (0 : Rat) < ov →
      (sparseTrafficRatio s ov < 1 ↔ sparsityCrossover ov < s) ∧
      ((1 : Rat) < sparseSpeedup s ov ↔ sparsityCrossover ov < s)) ∧
    (sparsityCrossover (1 / 64 : Rat) = 1 / 65 ∧
     (1 / 65 : Rat) < 1 / 5 ∧
     sparsityCrossover (3 / 16 : Rat) = 3 / 19 ∧
     (3 / 19 : Rat) < 1 / 5 ∧
     sparseSpeedup (3 / 4 : Rat) (3 / 16 : Rat) = 64 / 19 ∧
     (23 / 10 : Rat) < 64 / 19 ∧ (64 / 19 : Rat) < 34 / 10) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro delta g tau x hdelta hg htm hx1 hx2
    exact flip_zone_lower_branch hdelta hg htm hx1 hx2
  · intro delta g tau x hdelta hth hml hx1 hx2
    exact flip_zone_upper_branch hdelta hth hml hx1 hx2
  · intro delta g x hdelta hx1 hx2
    have hmid_le : g + delta / 2 ≤ g + delta := by
      apply rat_le_of_sub_nonneg
      have eq : (g + delta) - (g + delta / 2) = delta / 2 := by grind
      rw [eq]; exact Rat.le_of_lt (rat_div_pos hdelta (by decide))
    have hx_lo : g + delta / 2 ≤ x := by
      have eq : g + delta / 2 = (g + delta) - delta / 2 := by grind
      rw [eq]; exact hx1
    have h := flip_zone_upper_branch hdelta Rat.le_refl hmid_le hx_lo hx2
    exact ⟨h.1, h.2.1⟩
  · intro ov hov
    have hb := sparsityCrossover_bounds hov
    have hc := sparseTrafficRatio_at_crossover hov
    exact ⟨sparsityCrossover_eq_div hov, hb.1, hb.2, hc.1, hc.2⟩
  · intro s ov hs hov
    exact ⟨sparseTrafficRatio_lt_one_iff hov, sparseSpeedup_gt_one_iff hs hov⟩
  · refine ⟨by unfold sparsityCrossover; grind, ?_,
            by unfold sparsityCrossover; grind, ?_,
            by unfold sparseSpeedup sparseTrafficRatio; grind, ?_, ?_⟩
    · apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 65) (by decide : (0 : Rat) < 5)
      have h1 : (1 : Rat) * 5 = 5 := by grind
      have h2 : (1 : Rat) * 65 = 65 := by grind
      rw [h1, h2]; decide
    · apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 19) (by decide : (0 : Rat) < 5)
      have h1 : (3 : Rat) * 5 = 15 := by grind
      have h2 : (1 : Rat) * 19 = 19 := by grind
      rw [h1, h2]; decide
    · apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 10) (by decide : (0 : Rat) < 19)
      have h1 : (23 : Rat) * 19 = 437 := by grind
      have h2 : (64 : Rat) * 10 = 640 := by grind
      rw [h1, h2]; decide
    · apply rat_div_lt_div_of_cross (by decide : (0 : Rat) < 19) (by decide : (0 : Rat) < 10)
      have h1 : (64 : Rat) * 10 = 640 := by grind
      have h2 : (34 : Rat) * 19 = 646 := by grind
      rw [h1, h2]; decide

end Relu2TealDeadzone
