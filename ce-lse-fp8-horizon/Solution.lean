/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CeLseHorizon

/-!
# Verified Solutions (`ce-lse-fp8-horizon`)
-/

namespace CeLseHorizonChallenge

open CeLseHorizon

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
      ceGrad (uniformProb V) y y = -(((V - 1 : Nat) : Rat) / (V : Rat))) :=
  CeLseHorizon.ce_gradient_zero_sum_conservation_exact

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
         finSum (uniformQuantGradRNE e4m3MinSub 1024 y2) = 511 / 256)) :=
  CeLseHorizon.fp8_e4m3_dual_horizon_and_rne_overshoot_cliff

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
         finSum (uniformQuantGradRNE e5m2MinSub 131072 y2) = 65535 / 32768)) :=
  CeLseHorizon.fp8_e5m2_128k_vocab_conservation_collapse

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
      (∀ k : Int, ¬fp16SubnormalSafe (pow2IntRat k) gMax pMin)) :=
  CeLseHorizon.fp16_loss_scale_empty_window_collapse_exact

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
      treeSum k t / seqSplitAccum p t (2 ^ k) = pow2Rat (k - p)) :=
  CeLseHorizon.lse_naive_swamping_vs_pairwise_tree_exact

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
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 10) 262144) = 0) :=
  CeLseHorizon.label_smoothing_fp8_total_erasure_exact

end CeLseHorizonChallenge
