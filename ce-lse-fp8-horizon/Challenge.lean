/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CeLseHorizon.Defs

/-!
# Trusted Challenge Statements (`ce-lse-fp8-horizon`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Exact Cross-Entropy gradient zero-sum conservation.
2. OCP FP8-E4M3 dual RTZ/RNE horizons (`V > 512` RTZ flush, `V ∈ [513, 1023]` RNE overshoot
   peaking at `+255/256`, `V = 1024` discontinuous cliff to `-1`).
3. IEEE FP8-E5M2 128K-vocabulary conservation collapse (`V > 65536` RTZ flush,
   `V ∈ [65537, 131071]` RNE overshoot peaking at `+32767/32768`, `V = 131072 = 2^17` cliff to `-1`).
4. FP16 dynamic power-of-two loss-scaling empty-window collapse (`2^30 - 2^18` normal,
   `2^41 - 2^29` subnormal).
5. LogSumExp naive `1 + sum` swamping and sequential split-accumulator stall vs exact zero-error
   pairwise binary tree split-accumulation.
6. Total FP8 erasure of standard label smoothing (`ε ∈ (0, 1/8]`) at `V ≥ 131,072`.
-/

namespace CeLseHorizonChallenge

open CeLseHorizon

/-- Theorem 1 (`ce_gradient_zero_sum_conservation_exact`):
    For any discrete probability distribution `p : Fin V → Rat` with `∑_v p_v = 1` and target
    `y : Fin V`, proves exact zero-sum conservation `∑_v (p_v - δ_{v,y}) = 0`, non-target mass
    `∑_{v ≠ y} p_v = 1 - p_y`, exact target cancellation, and the uniform distribution witness. -/
theorem ce_gradient_zero_sum_conservation_exact :
    (∀ (V : Nat) (p : Fin V → Rat) (y : Fin V), finSum p = 1 →
      finSum (ceGrad p y) = 0) ∧
    (∀ (V : Nat) (p : Fin V → Rat) (y : Fin V), finSum p = 1 →
      finSumExcept y p = 1 - p y) ∧
    (∀ (V : Nat) (p : Fin V → Rat) (y : Fin V), finSum p = 1 →
      finSumExcept y (ceGrad p y) = -ceGrad p y y) ∧
    (∀ (V : Nat) (y : Fin V),
      finSum (uniformProb V) = 1 ∧
      finSum (ceGrad (uniformProb V) y) = 0 ∧
      finSumExcept y (uniformProb V) = ((V - 1 : Nat) : Rat) / (V : Rat) ∧
      ceGrad (uniformProb V) y y = -(((V - 1 : Nat) : Rat) / (V : Rat))) := by
  sorry

/-- Theorem 2 (`fp8_e4m3_dual_horizon_and_rne_overshoot_cliff`):
    Exact OCP FP8-E4M3 (`min_sub = 2^{-9} = 1/512`, RNE tie-to-zero midpoint `2^{-10} = 1/1024`)
    dual horizon on uniform non-target gradients `1/V`:
    - RTZ flushes 100% of non-target gradients to `0` iff `V > 512` (exact defect `-15/16` for
      all `V > 512`, including `V = 513`).
    - RNE rounds every non-target gradient UP to `2^{-9}` across `V ∈ [513, 1023]`, producing a
      positive DC bias overshoot peaking at `V = 1023` (`+255/256 ≈ +0.996094`), then hits the
      RNE tie-to-even midpoint at `V = 1024` for a discontinuous drop of `511/256` to 100% flush
      and exact `-1` pure DC bias for all `V ≥ 1024`. -/
theorem fp8_e4m3_dual_horizon_and_rne_overshoot_cliff :
    (e4m3MinSub = 1 / 512 ∧ e4m3RneMid = 1 / 1024 ∧ e4m3MinSub / 2 = e4m3RneMid) ∧
    (∀ (V : Nat), 0 < V →
      (subnormalQuantRTZ e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 ↔ 512 < V)) ∧
    (∀ (V : Nat) (y : Fin V), 512 < V →
      negGradRoundsToPredRTZ 3 (ceGrad (uniformProb V) y y) ∧
      finSum (uniformQuantGradRTZ e4m3MinSub e4m3PredNegOne V y) = -(15 / 16 : Rat)) ∧
    (∀ (y : Fin 513),
      finSum (uniformQuantGradRTZ e4m3MinSub e4m3PredNegOne 513 y) = -(15 / 16 : Rat)) ∧
    (∀ (V : Nat) (y : Fin V), 513 ≤ V → V ≤ 1023 →
      negGradRoundsToNegOneRNE 3 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = e4m3MinSub ∧
      finSum (uniformQuantGradRNE e4m3MinSub V y) = ((V - 1 : Nat) : Rat) / 512 - 1) ∧
    (∀ (y : Fin 1023),
      finSum (uniformQuantGradRNE e4m3MinSub 1023 y) = 255 / 256) ∧
    (∀ (V : Nat) (y : Fin V), 1024 ≤ V →
      negGradRoundsToNegOneRNE 3 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 ∧
      finSum (uniformQuantGradRNE e4m3MinSub V y) = -1) ∧
    ((1 : Rat) / (1024 : Rat) = e4m3RneMid ∧
     (∀ (y1 : Fin 1023) (y2 : Fin 1024),
       finSum (uniformQuantGradRNE e4m3MinSub 1023 y1) -
         finSum (uniformQuantGradRNE e4m3MinSub 1024 y2) = 511 / 256)) := by
  sorry

/-- Theorem 3 (`fp8_e5m2_128k_vocab_conservation_collapse`):
    Exact IEEE FP8-E5M2 (`min_sub = 2^{-16} = 1/65536`, RNE midpoint `2^{-17} = 1/131072`)
    dual horizon on uniform non-target gradients `1/V`:
    - RTZ flushes 100% of non-target gradients to `0` iff `V > 65536` (exact defect `-7/8` for
      all `V > 65536`, including `V = 65537`).
    - RNE overshoots across `V ∈ [65537, 131071]`, peaking at `V = 131071` (`+32767/32768 ≈
      +0.999969`), then discontinuously collapses at `V = 131,072 = 2^17` (exact 128K LLM
      vocabulary size) with a drop of `65535/32768` to 100% flush and exact `-1` pure DC bias
      for all `V ≥ 131072`. -/
theorem fp8_e5m2_128k_vocab_conservation_collapse :
    (e5m2MinSub = 1 / 65536 ∧ e5m2RneMid = 1 / 131072 ∧
     e5m2MinSub / 2 = e5m2RneMid ∧ (2 ^ 17 : Nat) = 131072) ∧
    (∀ (V : Nat), 0 < V →
      (subnormalQuantRTZ e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 ↔ 65536 < V)) ∧
    (∀ (V : Nat) (y : Fin V), 65536 < V →
      negGradRoundsToPredRTZ 2 (ceGrad (uniformProb V) y y) ∧
      finSum (uniformQuantGradRTZ e5m2MinSub e5m2PredNegOne V y) = -(7 / 8 : Rat)) ∧
    (∀ (y : Fin 65537),
      finSum (uniformQuantGradRTZ e5m2MinSub e5m2PredNegOne 65537 y) = -(7 / 8 : Rat)) ∧
    (∀ (V : Nat) (y : Fin V), 65537 ≤ V → V ≤ 131071 →
      negGradRoundsToNegOneRNE 2 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = e5m2MinSub ∧
      finSum (uniformQuantGradRNE e5m2MinSub V y) = ((V - 1 : Nat) : Rat) / 65536 - 1) ∧
    (∀ (y : Fin 131071),
      finSum (uniformQuantGradRNE e5m2MinSub 131071 y) = 32767 / 32768) ∧
    (∀ (V : Nat) (y : Fin V), 131072 ≤ V →
      negGradRoundsToNegOneRNE 2 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 ∧
      finSum (uniformQuantGradRNE e5m2MinSub V y) = -1) ∧
    ((1 : Rat) / (131072 : Rat) = e5m2RneMid ∧
     (∀ (y1 : Fin 131071) (y2 : Fin 131072),
       finSum (uniformQuantGradRNE e5m2MinSub 131071 y1) -
         finSum (uniformQuantGradRNE e5m2MinSub 131072 y2) = 65535 / 32768)) := by
  sorry

/-- Theorem 4 (`fp16_loss_scale_empty_window_collapse_exact`):
    For IEEE-754 FP16 (`overflow_threshold = 65520`, `min_norm = 2^{-14}`, `min_sub_rne_thresh =
    2^{-25}`), proves NO positive loss scale `S` (and in particular NO power-of-two `S = 2^k`)
    simultaneously avoids overflow and normal underflow whenever `G_max / p_min ≥ 65520 * 2^14 =
    2^30 - 2^18 = 1,073,479,680`, and NO `S` avoids overflow and subnormal flush whenever
    `G_max / p_min ≥ 65520 * 2^25 = 2^41 - 2^29 = 2,198,486,384,640`. -/
theorem fp16_loss_scale_empty_window_collapse_exact :
    ((65520 : Rat) * pow2Rat 14 = (1073479680 : Rat) ∧
     (65520 : Nat) * 2 ^ 14 = 2 ^ 30 - 2 ^ 18 ∧
     (65520 : Nat) * 2 ^ 14 = 1073479680) ∧
    ((65520 : Rat) * pow2Rat 25 = (2198486384640 : Rat) ∧
     (65520 : Nat) * 2 ^ 25 = 2 ^ 41 - 2 ^ 29 ∧
     (65520 : Nat) * 2 ^ 25 = 2198486384640) ∧
    (∀ (gMax pMin : Rat), (0 : Rat) < gMax → (0 : Rat) < pMin →
      (1073479680 : Rat) ≤ gMax / pMin →
      (∀ S : Rat, (0 : Rat) < S → ¬fp16NormalSafe S gMax pMin) ∧
      (∀ k : Int, ¬fp16NormalSafe (pow2IntRat k) gMax pMin)) ∧
    (∀ (gMax pMin : Rat), (0 : Rat) < gMax → (0 : Rat) < pMin →
      (2198486384640 : Rat) ≤ gMax / pMin →
      (∀ S : Rat, (0 : Rat) < S → ¬fp16SubnormalSafe S gMax pMin) ∧
      (∀ k : Int, ¬fp16SubnormalSafe (pow2IntRat k) gMax pMin)) := by
  sorry

/-- Theorem 5 (`lse_naive_swamping_vs_pairwise_tree_exact`):
    For binary floating-point with `p` significand bits (`BF16: p = 8`, `FP16: p = 11`,
    `FP8-E5M2: p = 3`):
    - Naive `1 + sum` completely swamps every `0 ≤ t ≤ 2^{-p}` across all `n` terms (`naiveAccum = 1`).
    - Sequential split-accumulation, for terms `t` that are a power of two (`t = 2^j`, `j : Int`),
      stalls permanently at `2^p * t` for all `n ≥ 2^p`, losing all remaining `n - 2^p` terms.
      The power-of-two hypothesis is needed: in real round-to-nearest-even with `p = 3` and `t = 3`
      the running sum stalls at `32`, whereas the model `seqSplitAccum` gives `24`.
    - Pairwise Binary Tree Split-Accumulation on `2^k` equal terms `t` doubles exactly with ZERO
      rounding error (`treeSum k t = 2^k * t` for all `k : Nat`), strictly beating sequential
      accumulation (for power-of-two `t`) by `2^{k - p}` whenever `p < k`. -/
theorem lse_naive_swamping_vs_pairwise_tree_exact :
    (invPow2Rat 8 = 1 / 256 ∧ invPow2Rat 11 = 1 / 2048 ∧ invPow2Rat 3 = 1 / 8) ∧
    (∀ (p n : Nat) (t : Rat), (0 : Rat) ≤ t → t ≤ invPow2Rat p →
      rneAddSwamps p 1 t ∧ naiveAccum p t n = 1) ∧
    (∀ (p n : Nat) (t : Rat), (0 : Rat) < t → (∃ j : Int, t = pow2IntRat j) →
      rneAddSwamps p (pow2Rat p * t) t ∧
      (n ≤ 2 ^ p → seqSplitAccum p t n = (n : Rat) * t) ∧
      (2 ^ p ≤ n →
        seqSplitAccum p t n = pow2Rat p * t ∧
        (n : Rat) * t - seqSplitAccum p t n = ((n - 2 ^ p : Nat) : Rat) * t)) ∧
    (∀ (k : Nat) (t : Rat), treeSum k t = pow2Rat k * t) ∧
    (∀ (p k : Nat) (t : Rat), p < k → (0 : Rat) < t → (∃ j : Int, t = pow2IntRat j) →
      seqSplitAccum p t (2 ^ k) < treeSum k t ∧
      treeSum k t / seqSplitAccum p t (2 ^ k) = pow2Rat (k - p)) := by
  sorry

/-- Theorem 6 (`label_smoothing_fp8_total_erasure_exact`):
    For any standard label-smoothing weight `ε ∈ (0, 1/8]` (including `1/100`, `1/20`, `1/10`)
    at modern LLM vocabulary sizes `V ≥ 131,072 = 2^17`, proves `0 < ε / V < 2^{-17}`, so BOTH
    OCP FP8-E4M3 and IEEE FP8-E5M2 (under both RNE and RTZ) flush `ε / V` to exact `0`
    (100% erasure of label smoothing). -/
theorem label_smoothing_fp8_total_erasure_exact :
    (∀ (ε : Rat) (V : Nat), (0 : Rat) < ε → ε ≤ 1 / 8 → 131072 ≤ V →
      (0 : Rat) < labelSmoothOffTarget ε V ∧
      labelSmoothOffTarget ε V < e5m2RneMid ∧
      subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRTZ e4m3MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRTZ e5m2MinSub (labelSmoothOffTarget ε V) = 0) ∧
    (subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 100) 131072) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 100) 131072) = 0 ∧
     subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 20) 131072) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 20) 131072) = 0 ∧
     subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 10) 131072) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 10) 131072) = 0 ∧
     subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 10) 262144) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 10) 262144) = 0) := by
  sorry

end CeLseHorizonChallenge
