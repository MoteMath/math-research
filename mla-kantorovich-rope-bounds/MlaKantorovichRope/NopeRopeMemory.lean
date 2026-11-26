/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MlaKantorovichRope.RatOrder

/-!
# Theorems 3 & 6: Decoupled NoPE+RoPE `256/85` Crossover & Sub-Byte MLA Memory Compression

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
- Theorem 3 (`decoupled_nope_rope_256_85_crossover_exact`): exact DeepSeek bit budgets (`2048` vs
  `2304`, exact `1/9` = `-11.1%` cache reduction), exact `256/85` sensitivity crossover for
  `(3, 8)` beating `(4, 4)` (plus `16/5` for `(3, 6)` beating `(4, 4)`), and the universal
  closed-form rational crossover and budget-reduction laws for arbitrary `(d_c, d_R, b_c, b_R, b_c', b_R')`.
- Theorem 6 (`subbyte_mla_memory_compression_ratios_exact`): exact byte footprints (`192 B/tok`
  fused `Tern512 + RoPE64_INT8`, `128 B/tok` `Tern512`, `256 B/tok` `INT4-512`, `1152 B/tok` BF16 MLA,
  `65536 B/tok` BF16 MHA-128), exact compression ratios `1024/3` (`341.33x` vs BF16 MHA-128) and `6`
  (`6x` vs BF16 MLA), and general parametric compression formulas.
-/

namespace MlaKantorovichRope

/-- Universal rational distortion crossover law:
    For `b_c < b_c'`, `b_R' < b_R`, and `α_c, α_R > 0`,
    `mlaDistortion α_c α_R b_c b_R < mlaDistortion α_c α_R b_c' b_R'`
    iff `crossoverThreshold b_c b_R b_c' b_R' < α_R / α_c`. -/
theorem general_nope_rope_crossover (α_c α_R : Rat) (b_c b_R b_c' b_R' : Nat)
    (hαc : 0 < α_c) (_hbc : b_c < b_c') (hbR : b_R' < b_R) :
    mlaDistortion α_c α_R b_c b_R < mlaDistortion α_c α_R b_c' b_R' ↔
      crossoverThreshold b_c b_R b_c' b_R' < α_R / α_c := by
  unfold mlaDistortion crossoverThreshold
  have hdiffR : (0 : Rat) < invPow4Rat b_R' - invPow4Rat b_R :=
    rat_sub_pos (rat_invPow4_strict_anti hbR)
  have hdiffR_ne : invPow4Rat b_R' - invPow4Rat b_R ≠ 0 := Rat.ne_of_gt hdiffR
  have hαc_ne : α_c ≠ 0 := Rat.ne_of_gt hαc
  constructor
  · intro hlt
    have hsub : (0 : Rat) <
        (α_c * invPow4Rat b_c' + α_R * invPow4Rat b_R') -
        (α_c * invPow4Rat b_c + α_R * invPow4Rat b_R) := rat_sub_pos hlt
    have hre : (α_c * invPow4Rat b_c' + α_R * invPow4Rat b_R') -
        (α_c * invPow4Rat b_c + α_R * invPow4Rat b_R) =
        α_R * (invPow4Rat b_R' - invPow4Rat b_R) - α_c * (invPow4Rat b_c - invPow4Rat b_c') := by grind
    rw [hre] at hsub
    have hineq : α_c * (invPow4Rat b_c - invPow4Rat b_c') < α_R * (invPow4Rat b_R' - invPow4Rat b_R) :=
      rat_lt_of_sub_pos hsub
    have hdiv1 := rat_div_lt_div_of_pos_right hineq (rat_mul_pos hαc hdiffR)
    have hl : (α_c * (invPow4Rat b_c - invPow4Rat b_c')) / (α_c * (invPow4Rat b_R' - invPow4Rat b_R)) =
        (invPow4Rat b_c - invPow4Rat b_c') / (invPow4Rat b_R' - invPow4Rat b_R) := by
      have hmul : ((invPow4Rat b_c - invPow4Rat b_c') / (invPow4Rat b_R' - invPow4Rat b_R)) *
          (α_c * (invPow4Rat b_R' - invPow4Rat b_R)) =
          α_c * (invPow4Rat b_c - invPow4Rat b_c') := by
        rw [Rat.mul_comm α_c, ← Rat.mul_assoc, rat_div_mul_cancel hdiffR_ne, Rat.mul_comm]
      rw [← hmul, rat_mul_div_cancel (Rat.ne_of_gt (rat_mul_pos hαc hdiffR))]
    have hr : (α_R * (invPow4Rat b_R' - invPow4Rat b_R)) / (α_c * (invPow4Rat b_R' - invPow4Rat b_R)) =
        α_R / α_c := by
      have hmul : (α_R / α_c) * (α_c * (invPow4Rat b_R' - invPow4Rat b_R)) =
          α_R * (invPow4Rat b_R' - invPow4Rat b_R) := by
        rw [← Rat.mul_assoc, rat_div_mul_cancel hαc_ne]
      rw [← hmul, rat_mul_div_cancel (Rat.ne_of_gt (rat_mul_pos hαc hdiffR))]
    rw [hl, hr] at hdiv1
    exact hdiv1
  · intro hlt
    have hmul := rat_mul_lt_mul_of_pos_right hlt (rat_mul_pos hαc hdiffR)
    have hl : ((invPow4Rat b_c - invPow4Rat b_c') / (invPow4Rat b_R' - invPow4Rat b_R)) *
        (α_c * (invPow4Rat b_R' - invPow4Rat b_R)) =
        α_c * (invPow4Rat b_c - invPow4Rat b_c') := by
      rw [Rat.mul_comm α_c, ← Rat.mul_assoc, rat_div_mul_cancel hdiffR_ne, Rat.mul_comm]
    have hr : (α_R / α_c) * (α_c * (invPow4Rat b_R' - invPow4Rat b_R)) =
        α_R * (invPow4Rat b_R' - invPow4Rat b_R) := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel hαc_ne]
    rw [hl, hr] at hmul
    apply rat_lt_of_sub_pos
    have hsub := rat_sub_pos hmul
    have hre : (α_c * invPow4Rat b_c' + α_R * invPow4Rat b_R') -
        (α_c * invPow4Rat b_c + α_R * invPow4Rat b_R) =
        α_R * (invPow4Rat b_R' - invPow4Rat b_R) - α_c * (invPow4Rat b_c - invPow4Rat b_c') := by grind
    rw [hre]
    exact hsub

/-- Theorem 3 (Exact Decoupled NoPE + RoPE `256/85` Mixed-Precision Crossover Law):
    Proves DeepSeek-V2/V3 exact bit budgets (`2048` for `(3,8)` vs `2304` for `(4,4)`, exact `1/9`
    smaller KV cache), exact crossover thresholds `256/85` for `(3,8)` vs `(4,4)` and `16/5` for
    `(3,6)` vs `(4,4)`, and the universal closed-form rational crossover and budget-reduction laws
    for arbitrary `(d_c, d_R, b_c, b_R, b_c', b_R')`. -/
theorem decoupled_nope_rope_256_85_crossover_exact :
    (mlaBitBudget 512 64 3 8 = 2048 ∧
     mlaBitBudget 512 64 4 4 = 2304 ∧
     mlaBitBudget 512 64 4 8 = 2560 ∧
     mlaBitBudget 512 64 3 6 = 1920 ∧
     ((2304 - 2048 : Rat) / 2304 = 1 / 9)) ∧
    (crossoverThreshold 3 8 4 4 = 256 / 85 ∧
     crossoverThreshold 3 6 4 4 = 16 / 5) ∧
    (∀ α_c α_R : Rat, 0 < α_c →
      (mlaDistortion α_c α_R 3 8 < mlaDistortion α_c α_R 4 4 ↔ (256 / 85 : Rat) < α_R / α_c) ∧
      (mlaDistortion α_c α_R 3 6 < mlaDistortion α_c α_R 4 4 ↔ (16 / 5 : Rat) < α_R / α_c)) ∧
    (∀ (α_c α_R : Rat) (b_c b_R b_c' b_R' : Nat),
      0 < α_c → b_c < b_c' → b_R' < b_R →
      (mlaDistortion α_c α_R b_c b_R < mlaDistortion α_c α_R b_c' b_R' ↔
        crossoverThreshold b_c b_R b_c' b_R' < α_R / α_c)) ∧
    (∀ (d_c d_R b_c b_R b_c' b_R' : Nat),
      b_c ≤ b_c' → b_R' ≤ b_R →
      (mlaBitBudget d_c d_R b_c b_R < mlaBitBudget d_c d_R b_c' b_R' ↔
        d_R * (b_R - b_R') < d_c * (b_c' - b_c))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold mlaBitBudget; grind
  · unfold crossoverThreshold invPow4Rat; grind
  · intro α_c α_R hαc
    have h1 := general_nope_rope_crossover α_c α_R 3 8 4 4 hαc (by decide) (by decide)
    have h2 := general_nope_rope_crossover α_c α_R 3 6 4 4 hαc (by decide) (by decide)
    have hc1 : crossoverThreshold 3 8 4 4 = 256 / 85 := by
      unfold crossoverThreshold invPow4Rat; grind
    have hc2 : crossoverThreshold 3 6 4 4 = 16 / 5 := by
      unfold crossoverThreshold invPow4Rat; grind
    rw [hc1] at h1
    rw [hc2] at h2
    exact ⟨h1, h2⟩
  · intro α_c α_R b_c b_R b_c' b_R' hαc hbc hbR
    exact general_nope_rope_crossover α_c α_R b_c b_R b_c' b_R' hαc hbc hbR
  · intro d_c d_R b_c b_R b_c' b_R' hbc hbR
    unfold mlaBitBudget
    have h1 : d_c * b_c' = d_c * b_c + d_c * (b_c' - b_c) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hbc]
    have h2 : d_R * b_R = d_R * b_R' + d_R * (b_R - b_R') := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hbR]
    omega

/-- Theorem 6 (Exact Sub-Byte MLA Memory Compression Ratios):
    Certifies DeepSeek fused `Tern512 + RoPE64_INT8` (`192 B/tok`) achieves exact `1024/3`
    (`341.333...x`) reduction vs BF16 MHA-128 (`65,536 B/tok`) and exact `6x` reduction vs
    BF16 MLA (`1,152 B/tok`), alongside `Tern512` (`128 B/tok`, `512x` vs MHA / `9x` vs MLA),
    `INT4-512` (`256 B/tok`, `256x` vs MHA), and the general parametric rational compression laws. -/
theorem subbyte_mla_memory_compression_ratios_exact :
    (mlaBytesPerToken 512 64 2 8 = 192 ∧
     mlaBytesPerToken 512 0 2 0 = 128 ∧
     mlaBytesPerToken 512 0 4 0 = 256 ∧
     bf16MlaBytesPerToken 512 64 = 1152 ∧
     bf16MhaBytesPerToken 128 128 = 65536) ∧
    (bf16MhaBytesPerToken 128 128 / mlaBytesPerToken 512 64 2 8 = 1024 / 3 ∧
     bf16MlaBytesPerToken 512 64 / mlaBytesPerToken 512 64 2 8 = 6 ∧
     bf16MhaBytesPerToken 128 128 / mlaBytesPerToken 512 0 2 0 = 512 ∧
     bf16MlaBytesPerToken 512 64 / mlaBytesPerToken 512 0 2 0 = 9 ∧
     bf16MhaBytesPerToken 128 128 / mlaBytesPerToken 512 0 4 0 = 256) ∧
    (∀ (H d_h d_c d_R b_c b_R : Nat), 0 < mlaBitBudget d_c d_R b_c b_R →
      bf16MhaBytesPerToken H d_h / mlaBytesPerToken d_c d_R b_c b_R =
        ((32 * H * d_h : Nat) : Rat) / ((mlaBitBudget d_c d_R b_c b_R : Nat) : Rat) ∧
      bf16MlaBytesPerToken d_c d_R / mlaBytesPerToken d_c d_R b_c b_R =
        ((16 * (d_c + d_R) : Nat) : Rat) / ((mlaBitBudget d_c d_R b_c b_R : Nat) : Rat)) := by
  refine ⟨by unfold mlaBytesPerToken bf16MlaBytesPerToken bf16MhaBytesPerToken; grind,
          by unfold mlaBytesPerToken bf16MlaBytesPerToken bf16MhaBytesPerToken; grind, ?_⟩
  intro H d_h d_c d_R b_c b_R hpos
  unfold bf16MhaBytesPerToken bf16MlaBytesPerToken mlaBytesPerToken mlaBitBudget at *
  have hBne : ((d_c * b_c + d_R * b_R : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos hpos)
  have h8ne : (8 : Rat) ≠ 0 := by decide
  have hdiv_inv : (((d_c * b_c + d_R * b_R : Nat) : Rat) / 8)⁻¹ =
      8 / ((d_c * b_c + d_R * b_R : Nat) : Rat) := rat_div_inv hBne h8ne
  constructor
  · rw [Rat.div_def, hdiv_inv]
    have hnat : ((32 * H * d_h : Nat) : Rat) = ((H * d_h * 4 : Nat) : Rat) * 8 := by
      have h1 : 32 * H * d_h = H * d_h * 4 * 8 := by grind
      rw [h1, Rat.natCast_mul]
      rfl
    rw [hnat, Rat.div_def, Rat.div_def]
    grind
  · rw [Rat.div_def, hdiv_inv]
    have hnat : ((16 * (d_c + d_R) : Nat) : Rat) = (((d_c + d_R) * 2 : Nat) : Rat) * 8 := by
      have h1 : 16 * (d_c + d_R) = (d_c + d_R) * 2 * 8 := by grind
      rw [h1, Rat.natCast_mul]
      rfl
    rw [hnat, Rat.div_def, Rat.div_def]
    grind

end MlaKantorovichRope
