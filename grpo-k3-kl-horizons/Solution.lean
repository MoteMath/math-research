/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrpoK3Kl

/-!
# Verified Solutions (`grpo-k3-kl-horizons`)
-/

namespace GrpoK3KlChallenge

open GrpoK3Kl

theorem schulman_k3_exact_nonnegativity_and_quadratic_bound :
    (∀ (d e_d : Rat), 1 + d ≤ e_d → (0 : Rat) ≤ e_d - 1 - d) ∧
    (∀ (d e_d : Rat), 1 + d < e_d → (0 : Rat) < e_d - 1 - d) ∧
    (∀ (d e_d : Rat), (0 : Rat) ≤ d → d ≤ 1 →
      expTaylor4 d ≤ e_d → e_d ≤ expTaylor3 d + d * d * d * d / 12 →
      k3QuadLower d ≤ k3Stab d ∧ k3Stab d ≤ e_d - 1 - d ∧ e_d - 1 - d ≤ k3QuadUpper d) ∧
    (∀ d : Rat,
      k3Stab d = (d * d / 24) * ((d + 2) * (d + 2) + 8) ∧
      (d * d) / 3 ≤ k3Stab d ∧
      (0 : Rat) ≤ k3Stab d ∧
      (d ≠ 0 → (0 : Rat) < k3Stab d)) ∧
    (∀ d : Rat,
      (1 / 4 : Rat) ≤ pade22Den d ∧
      (0 : Rat) < pade22Den d ∧
      pade22 d - 1 - d = (d * d * (6 - d)) / (12 * pade22Den d) ∧
      (d < 6 → (0 : Rat) ≤ pade22 d - 1 - d ∧ (d ≠ 0 → (0 : Rat) < pade22 d - 1 - d))) :=
  GrpoK3Kl.schulman_k3_exact_nonnegativity_and_quadratic_bound

theorem bf16_k3_negative_kl_and_deadzone_exact :
    (∀ (m : Nat) (x : Rat), rneRoundsToOneAbove m x ↔ (1 ≤ x ∧ x ≤ 1 + invPow2Rat (m + 1))) ∧
    (∀ (m : Nat) (d : Rat), rneRoundsToPredOfOne m (1 - d) ↔
      (invPow2Rat (m + 2) < d ∧ d ≤ invPow2Rat (m + 1))) ∧
    (∀ (m : Nat) (d : Rat), rneSnapsToOneBelow m (1 - d) ↔
      ((0 : Rat) ≤ d ∧ d ≤ invPow2Rat (m + 2))) ∧
    (∀ (m : Nat) (d e_d : Rat),
      invPow2Rat (m + 2) < d → d ≤ invPow2Rat (m + 1) →
      1 ≤ e_d → e_d ≤ 1 + invPow2Rat (m + 1) →
      rneRoundsToOneAbove m e_d ∧
      rneRoundsToPredOfOne m (1 - d) ∧
      (1 - invPow2Rat (m + 1)) - 1 = -invPow2Rat (m + 1) ∧
      (1 - invPow2Rat (m + 1)) - 1 < 0) ∧
    (∀ (m : Nat) (d e_d : Rat),
      (0 : Rat) < d → d ≤ invPow2Rat (m + 2) →
      1 ≤ e_d → e_d ≤ 1 + invPow2Rat (m + 1) →
      rneRoundsToOneAbove m e_d ∧
      rneSnapsToOneBelow m (1 - d) ∧
      (1 : Rat) - 1 = 0 ∧
      (0 : Rat) < k3Stab d) ∧
    (∀ d : Rat, ((1 + d) - d) - 1 = 0) ∧
    (let d := bf16DecodePosNormal 0x3b01
     d = 129 / 65536 ∧
     rneRoundsToOneAbove 7 (expTaylor4 d) ∧
     rneRoundsToPredOfOne 7 (1 - d) ∧
     (1 - invPow2Rat 8) - 1 = -(1 / 256 : Rat) ∧
     (1 - invPow2Rat 8) - 1 < 0) ∧
    (let d := fp16DecodePosNormal 0x0c01
     d = 1025 / 4194304 ∧
     rneRoundsToOneAbove 10 (expTaylor4 d) ∧
     rneRoundsToPredOfOne 10 (1 - d) ∧
     (1 - invPow2Rat 11) - 1 = -(1 / 2048 : Rat) ∧
     (1 - invPow2Rat 11) - 1 < 0) ∧
    (∀ (m : Nat) (d e_d : Rat),
      (0 : Rat) < d → 1 ≤ e_d → e_d ≤ 1 + invPow2Rat (m + 1) →
      rneRoundsToOneAbove m e_d ∧ ((1 : Rat) - 1) - d = -d ∧ ((1 : Rat) - 1) - d < 0) ∧
    (let d := bf16DecodePosNormal 0x3b7f
     d = 255 / 65536 ∧
     rneRoundsToOneAbove 7 (expTaylor4 d) ∧
     ((1 : Rat) - 1) - d = -(255 / 65536 : Rat) ∧
     ((1 : Rat) - 1) - d < 0) :=
  GrpoK3Kl.bf16_k3_negative_kl_and_deadzone_exact

theorem fp8_bf16_logprob_cancellation_clip_collapse :
    (∀ (k m : Nat) (q1 q2 : Int),
      (q1 : Rat) * binadeUlp k m - (q2 : Rat) * binadeUlp k m =
        ((q1 - q2 : Int) : Rat) * binadeUlp k m ∧
      (q1 ≠ q2 → binadeUlp k m ≤
        ratAbs ((q1 : Rat) * binadeUlp k m - (q2 : Rat) * binadeUlp k m))) ∧
    (∀ (Δ r : Rat), (1 / 4 : Rat) ≤ Δ → 1 + Δ + Δ * Δ / 2 ≤ r →
      (6 / 5 : Rat) < r ∧ ¬ inClipWindow r) ∧
    (∀ (Δ r : Rat), Δ ≤ -(1 / 4 : Rat) → (0 : Rat) < r →
      1 + (-Δ) + (-Δ) * (-Δ) / 2 ≤ r⁻¹ →
      r < (4 / 5 : Rat) ∧ ¬ inClipWindow r) ∧
    (∀ (k m : Nat), m ≤ k + 2 → (1 / 4 : Rat) ≤ binadeUlp k m) ∧
    (∀ k : Nat, 1 ≤ k → (1 / 4 : Rat) ≤ binadeUlp k 3) ∧
    (∀ k : Nat, 5 ≤ k → (1 / 4 : Rat) ≤ binadeUlp k 7) ∧
    (∀ k : Nat, 8 ≤ k → (1 / 4 : Rat) ≤ binadeUlp k 10) ∧
    (binadeUlp 1 3 = 1 / 4 ∧ binadeUlp 3 7 = 1 / 16 ∧ binadeUlp 4 7 = 1 / 8 ∧
     binadeUlp 5 7 = 1 / 4 ∧ binadeUlp 8 10 = 1 / 4) :=
  GrpoK3Kl.fp8_bf16_logprob_cancellation_clip_collapse

theorem direct_logit_diff_binade_invariance :
    (∀ (zNew zOld lseNew lseOld : Rat),
      logProb zNew lseNew - logProb zOld lseOld = directLogitDiff zNew zOld lseNew lseOld) ∧
    (∀ (zNew zOld lseNew lseOld c : Rat),
      directLogitDiff (zNew - c) (zOld - c) lseNew lseOld =
        directLogitDiff zNew zOld lseNew lseOld) ∧
    (∀ (zNew zOld lseNew lseOld c : Rat),
      directLogitDiff zNew zOld (lseNew + c) (lseOld + c) =
        directLogitDiff zNew zOld lseNew lseOld) ∧
    (∀ (k m : Nat) (lpNew lpOld flNew flOld : Rat),
      ratAbs (flNew - lpNew) ≤ binadeUlp k m / 2 →
      ratAbs (flOld - lpOld) ≤ binadeUlp k m / 2 →
      ratAbs ((flNew - flOld) - (lpNew - lpOld)) ≤ binadeUlp k m) ∧
    (∀ (m : Nat) (Δ ΔHat B : Rat),
      ratAbs Δ ≤ B →
      ratAbs (ΔHat - Δ) ≤ invPow2Rat (m + 1) * ratAbs Δ →
      ratAbs (ΔHat - Δ) ≤ invPow2Rat (m + 1) * B) ∧
    (invPow2Rat 8 * (1 / 4 : Rat) = 1 / 1024 ∧
     binadeUlp 4 7 / (1 / 1024 : Rat) = 128 ∧
     binadeUlp 5 7 / (1 / 1024 : Rat) = 256) :=
  GrpoK3Kl.direct_logit_diff_binade_invariance

theorem grpo_binary_reward_extreme_overweighting_exact :
    (∀ (k G : Nat), 0 < k → k < G →
      ((k : Rat) * (1 - binMean k G) * (1 - binMean k G) +
       ((G : Rat) - (k : Rat)) * (0 - binMean k G) * (0 - binMean k G)) / (G : Rat) = binVar k G ∧
      (0 : Rat) < binVar k G ∧
      binAdvPosSq k G = ((G : Rat) - (k : Rat)) / (k : Rat) ∧
      binAdvNegSq k G = (k : Rat) / ((G : Rat) - (k : Rat)) ∧
      binAdvPosSq k G * binAdvNegSq k G = 1 ∧
      binL1SumSq k G = ((G : Rat) * (G : Rat)) / ((k : Rat) * ((G : Rat) - (k : Rat)))) ∧
    (∀ h : Nat, 2 ≤ h →
      let G := 2 * h
      binAdvPosSq h G = 1 ∧
      binAdvNegSq h G = 1 ∧
      binL1SumSq h G = 4 ∧
      binAdvPosSq 1 G = (G : Rat) - 1 ∧
      binAdvPosSq 1 G / binAdvPosSq h G = (G : Rat) - 1 ∧
      binL1SumSq 1 G / binL1SumSq h G = ((G : Rat) * (G : Rat)) / (4 * ((G : Rat) - 1))) ∧
    (binL1SumSq 1 4 / binL1SumSq 2 4 = 4 / 3 ∧
     binL1SumSq 1 8 / binL1SumSq 4 8 = 16 / 7 ∧
     binL1SumSq 1 16 / binL1SumSq 8 16 = 64 / 15 ∧
     binL1SumSq 1 64 / binL1SumSq 32 64 = 1024 / 63 ∧
     (16 : Rat) < binL1SumSq 1 64 / binL1SumSq 32 64) ∧
    (∀ (k G : Nat) (r : Rat), k ≤ G → 0 < G → (r = 0 ∨ r = 1) →
      ratAbs (drGrpoAdv r (binMean k G)) ≤ 1) ∧
    (∀ (k G : Nat), k ≤ G → 0 < G →
      ratAbs (drGrpoAdv 1 (binMean k G)) + ratAbs (drGrpoAdv 0 (binMean k G)) = 1) :=
  GrpoK3Kl.grpo_binary_reward_extreme_overweighting_exact

theorem grpo_bf16_onepass_negvar_and_fp8_mean_stall :
    (let r0 := bf16DecodePosNormal 0x4081
     let r3 := bf16DecodePosNormal 0x4083
     let μTrue := (3 * r0 + r3) / 4
     let μHat := bf16DecodePosNormal 0x4082
     let meanSqTrue := (3 * (r0 * r0) + r3 * r3) / 4
     let flMeanSq := bf16DecodePosNormal 0x4183
     let flMuSq := bf16DecodePosNormal 0x4184
     r0 = 129 / 32 ∧ r3 = 131 / 32 ∧ μHat = 65 / 16 ∧
     flMeanSq = 131 / 8 ∧ flMuSq = 33 / 2 ∧
     meanSqTrue - μTrue * μTrue = 3 / 4096 ∧
     (0 : Rat) < meanSqTrue - μTrue * μTrue ∧
     rneRoundsToUpperEven r0 (binadeUlp 2 7) μTrue ∧
     r0 + binadeUlp 2 7 = μHat ∧
     rneRoundsStrictlyLower flMuSq (binadeUlp 4 7) (μHat * μHat) ∧
     rneRoundsStrictlyLower flMeanSq (binadeUlp 4 7) meanSqTrue ∧
     flMeanSq - flMuSq = -(1 / 8 : Rat) ∧
     flMeanSq - flMuSq < 0) ∧
    (binadeUlp 6 3 = 8 ∧
     rneRoundsToLowerEven 64 (binadeUlp 6 3) (64 + 4) ∧
     (∀ n : Nat, 16 ≤ n → fp8E4M3SeqSumFour n = 64) ∧
     fp8E4M3SeqSumFour 64 = 64 ∧
     fp8E4M3SeqSumFour 64 / 64 = 1 ∧
     (4 : Rat) - fp8E4M3SeqSumFour 64 / 64 = 3 ∧
     (0 : Rat) < (4 : Rat) - fp8E4M3SeqSumFour 64 / 64) :=
  GrpoK3Kl.grpo_bf16_onepass_negvar_and_fp8_mean_stall

end GrpoK3KlChallenge
