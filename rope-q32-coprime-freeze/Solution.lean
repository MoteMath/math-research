/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RopeQ32Coprime

/-!
# Verified Solutions (`rope-q32-coprime-freeze`)
-/

namespace RopeQ32CoprimeChallenge

open RopeQ32Coprime

theorem rope_bf16_fp16_consecutive_freeze_run_exact :
    (∀ p k : Nat, p ≤ k →
      binadeUlp p k * 2 ^ (p + 1) = 2 ^ (k + 1) ∧
      2 ^ (k + 1) / 2 ^ (p + 1) = binadeUlp p k ∧
      2 ^ k / 2 ^ p = binadeUlp p k) ∧
    (∀ p k q : Nat, p < k → 0 < q → q % 2 = 0 →
      (∀ m : Nat, q * binadeUlp p k - 2 ^ (k - p - 1) ≤ m →
        m ≤ q * binadeUlp p k + 2 ^ (k - p - 1) →
        binadeRneNat p k m = q * binadeUlp p k) ∧
      (q * binadeUlp p k + 2 ^ (k - p - 1)) - (q * binadeUlp p k - 2 ^ (k - p - 1)) + 1 =
        binadeUlp p k + 1) ∧
    (∀ p k q : Nat, p < k → q % 2 = 1 →
      (∀ m : Nat, q * binadeUlp p k - 2 ^ (k - p - 1) + 1 ≤ m →
        m ≤ q * binadeUlp p k + 2 ^ (k - p - 1) - 1 →
        binadeRneNat p k m = q * binadeUlp p k) ∧
      (q * binadeUlp p k + 2 ^ (k - p - 1) - 1) - (q * binadeUlp p k - 2 ^ (k - p - 1) + 1) + 1 =
        binadeUlp p k - 1) ∧
    (∀ p k : Nat, p < k → (binadeUlp p k + 1) + (binadeUlp p k - 1) = 2 * binadeUlp p k) ∧
    (binadeUlp 7 12 = 32 ∧ binadeUlp 7 15 = 256 ∧
     binadeUlp 7 17 = 1024 ∧ binadeUlp 7 20 = 8192 ∧
     binadeUlp 10 12 = 4 ∧ binadeUlp 10 15 = 32 ∧
     binadeUlp 23 29 = 64) ∧
    (∀ k m : Nat, k ≤ 23 → binadeRneNat 23 k m = m) ∧
    (fp16MaxNormal = 65504 ∧ fp16TopUlp = 32 ∧ fp16OverflowThreshold = 65520 ∧
     (∀ m : Nat, 2 ^ 15 ≤ m → m < 2 ^ 16 →
       (binadeRneNat 10 15 m = 2 ^ 16 ↔ fp16OverflowThreshold ≤ m)) ∧
     131072 - fp16OverflowThreshold = 65552 ∧
     1048576 - fp16OverflowThreshold = 983056) :=
  RopeQ32Coprime.rope_bf16_fp16_consecutive_freeze_run_exact

theorem rope_high_freq_random_phase_horizon_exact :
    (∀ p k m : Nat, k ≤ p → binadeRneNat p k m = m) ∧
    (highFreqRandomPhasePos 7 = 257 ∧
     highFreqRandomPhasePos 10 = 2049 ∧
     highFreqRandomPhasePos 23 = 16777217) ∧
    (∀ p k : Nat, p + 1 ≤ k → 2 ≤ binadeUlp p k ∧ 1 ≤ 2 ^ (k - p - 1)) ∧
    (∀ p : Nat, 1 ≤ p →
      binadeUlp p (p + 1) = 2 ∧
      binadeRneNat p (p + 1) (highFreqRandomPhasePos p) = 2 ^ (p + 1) ∧
      highFreqRandomPhasePos p - binadeRneNat p (p + 1) (highFreqRandomPhasePos p) = 1) ∧
    (∀ piRat : Rat, piRat ≤ 22 / 7 →
      piRat / 4 < (1 : Rat) ∧ piRat / 2 < (2 : Rat)) ∧
    ((1 : Rat) - 2 * (1 / 8 : Rat) = 3 / 4) :=
  RopeQ32Coprime.rope_high_freq_random_phase_horizon_exact

theorem q32_modular_odd_dyadic_zero_drift_exact :
    (∀ (omega : Nat), omega % 2 = 1 →
      Function.Injective (q32PhaseFin omega) ∧
      Function.Surjective (q32PhaseFin omega) ∧
      (∀ m : Nat, q32Phase omega (m + q32Mod) = q32Phase omega m) ∧
      (∀ m d : Nat, 0 < d → d < q32Mod → q32Phase omega (m + d) ≠ q32Phase omega m) ∧
      (∀ m : Nat, q32Phase omega (m + 1) ≠ q32Phase omega m) ∧
      (∀ m n : Nat, m ≤ n →
        (q32Phase omega m + q32Phase omega (n - m)) % q32Mod = q32Phase omega n ∧
        (q32Phase omega n + q32Mod - q32Phase omega m) % q32Mod = q32Phase omega (n - m))) ∧
    (∀ (b omega : Nat), 1 ≤ b → omega % 2 = 1 →
      (∃ u : Nat, u < 2 ^ b ∧ (omega * u) % (2 ^ b) = 1) ∧
      (∀ m : Nat, modPhase b omega (m + 1) ≠ modPhase b omega m)) :=
  RopeQ32Coprime.q32_modular_odd_dyadic_zero_drift_exact

theorem quantized_rotation_norm_drift_exact :
    (∀ c s : Rat, c * c + s * s = 1 →
      ratAbs (quantMXFP4 c * quantMXFP4 c + quantMXFP4 s * quantMXFP4 s - 1) ≤ 1 / 4) ∧
    ((15 / 17 : Rat) * (15 / 17) + (8 / 17) * (8 / 17) = 1 ∧
     quantMXFP4 (15 / 17) = 1 ∧ quantMXFP4 (8 / 17) = 1 / 2 ∧
     ratAbs (quantMXFP4 (15 / 17) * quantMXFP4 (15 / 17) +
             quantMXFP4 (8 / 17) * quantMXFP4 (8 / 17) - 1) = 1 / 4) ∧
    (∀ c s : Rat, c * c + s * s = 1 →
      ratAbs (quantFP8E4M3 c * quantFP8E4M3 c + quantFP8E4M3 s * quantFP8E4M3 s - 1) ≤ 21 / 256) ∧
    ((1323 / 1565 : Rat) * (1323 / 1565) + (836 / 1565) * (836 / 1565) = 1 ∧
     quantFP8E4M3 (1323 / 1565) = 7 / 8 ∧ quantFP8E4M3 (836 / 1565) = 9 / 16 ∧
     ratAbs (quantFP8E4M3 (1323 / 1565) * quantFP8E4M3 (1323 / 1565) +
             quantFP8E4M3 (836 / 1565) * quantFP8E4M3 (836 / 1565) - 1) = 21 / 256) ∧
    (∀ t : Rat, cayleyCos t * cayleyCos t + cayleySin t * cayleySin t - 1 = 0) ∧
    (∀ (B k : Nat),
      ((2 ^ (2 * B) : Int) - (k : Int) * (k : Int)) * ((2 ^ (2 * B) : Int) - (k : Int) * (k : Int)) +
      (2 * (2 ^ B : Int) * (k : Int)) * (2 * (2 ^ B : Int) * (k : Int)) =
      ((2 ^ (2 * B) : Int) + (k : Int) * (k : Int)) * ((2 ^ (2 * B) : Int) + (k : Int) * (k : Int))) :=
  RopeQ32Coprime.quantized_rotation_norm_drift_exact

theorem relative_position_factorization_error_decomposition :
    (∀ (q k : Rat × Rat) (Rm Rn : Rot2),
      rotScore q k Rm Rn = relScore q k (Rm.transpose.mul Rn)) ∧
    (∀ (q k : Rat × Rat) (RphM RphN Rm Rn Rrel : Rot2),
      let Em := Rm.sub RphM
      let En := Rn.sub RphN
      rotScore q k Rm Rn - relScore q k Rrel =
        (rotScore q k RphM RphN - relScore q k Rrel) +
        (relScore q k (Em.transpose.mul RphN) +
         relScore q k (RphM.transpose.mul En) +
         relScore q k (Em.transpose.mul En))) ∧
    (∀ (h : Nat) (q k : Fin h → Rat × Rat) (RphM RphN Rm Rn Rrel : Fin h → Rot2),
      finSum (fun i => rotScore (q i) (k i) (Rm i) (Rn i) - relScore (q i) (k i) (Rrel i)) =
        finSum (fun i => rotScore (q i) (k i) (RphM i) (RphN i) - relScore (q i) (k i) (Rrel i)) +
        finSum (fun i =>
          relScore (q i) (k i) ((Rm i).sub (RphM i) |>.transpose.mul (RphN i)) +
          relScore (q i) (k i) ((RphM i).transpose.mul ((Rn i).sub (RphN i))) +
          relScore (q i) (k i) ((Rm i).sub (RphM i) |>.transpose.mul ((Rn i).sub (RphN i))))) ∧
    (∀ (q k : Rat × Rat) (RphM RphN Rm Rn Rrel : Rot2) (ε : Rat),
      RphM.transpose.mul RphN = Rrel →
      ratAbs RphM.c ≤ 1 → ratAbs RphM.s ≤ 1 →
      ratAbs RphN.c ≤ 1 → ratAbs RphN.s ≤ 1 →
      ratAbs (Rm.sub RphM).c ≤ ε → ratAbs (Rm.sub RphM).s ≤ ε →
      ratAbs (Rn.sub RphN).c ≤ ε → ratAbs (Rn.sub RphN).s ≤ ε →
      ratAbs (rotScore q k Rm Rn - relScore q k Rrel) ≤
        (4 * ε + 2 * ε * ε) * l1Norm2 q * l1Norm2 k) ∧
    (∀ (Rfreeze : Rot2), Rfreeze.c * Rfreeze.c + Rfreeze.s * Rfreeze.s = 1 →
      ratAbs (rotScore (1, 0) (1, 0) Rfreeze Rfreeze - relScore (1, 0) (1, 0) ⟨0, 1⟩) = 1 ∧
      ratAbs (rotScore (1, 0) (1, 0) Rfreeze Rfreeze - relScore (1, 0) (1, 0) ⟨-1, 0⟩) = 2 ∧
      (4 * (1 / 32 : Rat) + 2 * (1 / 32) * (1 / 32) = 65 / 512) ∧
      (65 / 512 : Rat) < 1 ∧
      (4 * (1 / 8 : Rat) + 2 * (1 / 8) * (1 / 8) = 17 / 32) ∧
      (17 / 32 : Rat) < 1) :=
  RopeQ32Coprime.relative_position_factorization_error_decomposition

theorem dyadic_cayley_relative_composition_exact :
    (cayleyRot 0 = Rot2.id) ∧
    (∀ t : Rat, (cayleyRot t).transpose = cayleyRot (-t)) ∧
    (∀ t : Rat,
      (cayleyRot t).transpose.mul (cayleyRot t) = Rot2.id ∧
      (cayleyRot t).mul (cayleyRot t).transpose = Rot2.id) ∧
    (∀ (t : Rat) (v : Rat × Rat),
      normSq2 ((cayleyRot t).apply v) = normSq2 v) ∧
    (∀ t1 t2 : Rat, t1 * t2 ≠ 1 →
      (cayleyRot t1).mul (cayleyRot t2) = cayleyRot ((t1 + t2) / (1 - t1 * t2))) ∧
    (∀ t1 t2 : Rat, t1 * t2 ≠ -1 →
      (cayleyRot t1).transpose.mul (cayleyRot t2) = cayleyRot ((t2 - t1) / (1 + t1 * t2))) :=
  RopeQ32Coprime.dyadic_cayley_relative_composition_exact

end RopeQ32CoprimeChallenge
