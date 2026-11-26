/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnsignedFp4SoftmaxV

/-!
# Verified Solutions (`unsigned-fp4-softmax-v`)
-/

namespace UnsignedFp4SoftmaxVChallenge

open UnsignedFp4SoftmaxV

theorem unsigned_fp4_e1m3_collapse_to_uint4 :
    (∀ c : Nat, c < 16 →
      decodeUnsignedIEEE 1 3 c = decodeUnsignedIEEE 0 4 c ∧
      decodeUnsignedIEEE 1 3 c = c) ∧
    unsignedFp4IntLevels 1 3 = unsignedFp4IntLevels 0 4 ∧
    unsignedFp4IntLevels 1 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] ∧
    uE1M3Levels = uE0M4Levels ∧
    (∀ B : Nat, ef21OneMinusAlpha uE1M3Levels B = ef21OneMinusAlpha uE0M4Levels B) ∧
    (∀ N : Nat, simplexRtnDrift uE1M3Levels N = simplexRtnDrift uE0M4Levels N) ∧
    unsignedFp4IntLevels 2 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28] ∧
    unsignedFp4IntLevels 3 1 = [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192] ∧
    unsignedFp4IntLevels 4 0 =
      [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384] :=
  UnsignedFp4SoftmaxV.unsigned_fp4_e1m3_collapse_to_uint4

theorem unsigned_fp4_all_b_ef21_regime_classification :
    (∀ (B : Nat) (_ : 2 ≤ B) (C : Rat) (x e : Fin (B - 1) → Rat),
      (∀ j : Fin (B - 1), ∃ u0 u1 : Rat,
        (0 : Rat) ≤ u0 ∧ u0 ≤ x j ∧ x j ≤ u1 ∧
        e j = rtnDist u0 u1 (x j) ∧ ef21Bin u0 u1 B ≤ C) →
      sumFin (fun j => e j * e j) / (1 + sumFin (fun j => x j * x j)) ≤ C) ∧
    (∀ (B : Nat) (u0 u1 : Rat),
      let h := (u1 - u0) / 2
      let m := (u0 + u1) / 2
      sumFin (fun _ : Fin (B - 1) => h * h) / (1 + sumFin (fun _ : Fin (B - 1) => m * m)) =
        ef21Bin u0 u1 B) ∧
    (∀ B : Nat, 2 ≤ B → B ≤ 9 →
      ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
      ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE3M1Levels B ∧
      ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE4M0Levels B) ∧
    (∀ B : Nat, 10 ≤ B → B ≤ 130 →
      ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
      ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE3M1Levels B ∧
      ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE4M0Levels B) ∧
    (∀ B : Nat, 131 ≤ B → B ≤ 18431 →
      ef21OneMinusAlpha uE3M1Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
      ef21OneMinusAlpha uE3M1Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
      ef21OneMinusAlpha uE3M1Levels B ≤ ef21OneMinusAlpha uE4M0Levels B) ∧
    (ef21OneMinusAlpha uE3M1Levels 18431 = ef21OneMinusAlpha uE4M0Levels 18431) ∧
    (∀ B : Nat, 18432 ≤ B →
      ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
      ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
      ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE3M1Levels B) ∧
    ((ef21OneMinusAlpha sE2M1Levels 64 = 7 / 71 ∧
      ef21OneMinusAlpha uE2M2Levels 64 = 9 / 457 ∧
      (5 : Rat) < ef21OneMinusAlpha sE2M1Levels 64 / ef21OneMinusAlpha uE2M2Levels 64) ∧
     (ef21OneMinusAlpha sE2M1Levels 256 = 85 / 277 ∧
      ef21OneMinusAlpha uE3M1Levels 256 = 85 / 2137 ∧
      (77 / 10 : Rat) < ef21OneMinusAlpha sE2M1Levels 256 / ef21OneMinusAlpha uE3M1Levels 256) ∧
     (ef21OneMinusAlpha sE2M1Levels 1024 = 341 / 533 ∧
      ef21OneMinusAlpha uE3M1Levels 1024 = 341 / 8537 ∧
      (16 : Rat) < ef21OneMinusAlpha sE2M1Levels 1024 / ef21OneMinusAlpha uE3M1Levels 1024)) :=
  UnsignedFp4SoftmaxV.unsigned_fp4_all_b_ef21_regime_classification

theorem softmax_simplex_rtn_drift_exact :
    (∀ (N : Nat) (_ : 2 ≤ N) (D s : Rat) (_ : (0 : Rat) < s) (p q : Fin (N - 1) → Rat),
      s + sumFin p = 1 →
      (∀ j : Fin (N - 1), ∃ u0 u1 : Rat,
        (0 : Rat) ≤ u0 ∧ u0 ≤ p j / s ∧ p j / s ≤ u1 ∧
        q j - p j = s * rtnSignedErr u0 u1 (p j / s) ∧
        driftBin u0 u1 N ≤ D) →
      ratAbs (1 - (s + sumFin q)) ≤ D) ∧
    (∀ (N : Nat) (u0 u1 : Rat), (0 : Rat) ≤ u0 → u0 ≤ u1 →
      let m := (u0 + u1) / 2
      let s := 1 / (1 + ((N - 1 : Nat) : Rat) * m)
      (s + sumFin (fun _ : Fin (N - 1) => s * m) = 1) ∧
      (1 - (s + sumFin (fun _ : Fin (N - 1) => s * u0)) = driftBin u0 u1 N) ∧
      ((s + sumFin (fun _ : Fin (N - 1) => s * u1)) - 1 = driftBin u0 u1 N)) ∧
    ((simplexRtnDrift sE2M1Levels 128 = 127 / 151 ∧ (84 / 100 : Rat) < simplexRtnDrift sE2M1Levels 128) ∧
     (simplexRtnDrift uE0M4Levels 128 = 127 / 157 ∧ (80 / 100 : Rat) < simplexRtnDrift uE0M4Levels 128) ∧
     (simplexRtnDrift uE3M1Levels 128 = 127 / 511 ∧ simplexRtnDrift uE3M1Levels 128 < (25 / 100 : Rat)) ∧
     (driftBin ((fp8E4M3IntLevel 15 0 : Rat) / (fp8E4M3MaxInt : Rat))
               ((fp8E4M3IntLevel 15 1 : Rat) / (fp8E4M3MaxInt : Rat)) 128 = 127 / 2187 ∧
      (127 / 2187 : Rat) < (6 / 100 : Rat) ∧
      (∀ e m : Nat, e < 16 → m < 8 → ¬(e = 15 ∧ 6 ≤ m) →
        let a := fp8E4M3IntLevel e m
        let b := if m < 7 then fp8E4M3IntLevel e (m + 1) else fp8E4M3IntLevel (e + 1) 0
        driftBin ((a : Rat) / (fp8E4M3MaxInt : Rat)) ((b : Rat) / (fp8E4M3MaxInt : Rat)) 128 ≤
          127 / 2187))) :=
  UnsignedFp4SoftmaxV.softmax_simplex_rtn_drift_exact

theorem stratified_xor_vdc_simplex_zero_drift :
    (∀ b u : Nat, 1 ≤ b → u < 2 ^ b →
      srBit (2 ^ (b - 1)) u + srBit (2 ^ (b - 1)) ((2 ^ b - 1) - u) = 1) ∧
    (∀ (b m : Nat) (s u0 Δ : Rat) (u : Fin m → Nat),
      1 ≤ b → (∀ i, u i < 2 ^ b) →
      s + sumFin (fun _ : Fin m => 2 * (s * (u0 + (1 / 2 : Rat) * Δ))) = 1 →
      let qPair : Fin m → Rat := fun i =>
        s * (u0 + ((srBit (2 ^ (b - 1)) (u i) : Nat) : Rat) * Δ) +
        s * (u0 + ((srBit (2 ^ (b - 1)) ((2 ^ b - 1) - u i) : Nat) : Rat) * Δ)
      ratAbs (1 - (s + sumFin qPair)) = 0) ∧
    (∀ b mask k : Nat, mask < 2 ^ b → k ≤ 2 ^ b →
      sumFinNat (fun j : Fin (2 ^ b) => srBit k (xorVdcThreshold b mask j.val)) = k) ∧
    (∀ (b mask k : Nat) (s u0 Δ : Rat),
      mask < 2 ^ b → k ≤ 2 ^ b →
      let f : Rat := (k : Rat) / ((2 ^ b : Nat) : Rat)
      s + sumFin (fun _ : Fin (2 ^ b) => s * (u0 + f * Δ)) = 1 →
      let qVdc : Fin (2 ^ b) → Rat := fun j =>
        s * (u0 + ((srBit k (xorVdcThreshold b mask j.val) : Nat) : Rat) * Δ)
      ratAbs (1 - (s + sumFin qVdc)) = 0) :=
  UnsignedFp4SoftmaxV.stratified_xor_vdc_simplex_zero_drift

theorem attention_v_centering_simplex_drift_annihilation :
    ∀ (n : Nat) (p pHat v qV qVc : Fin n → Rat) (μV : Rat),
      sumFin p = 1 →
      let δP := sumFin pHat - 1
      let vc : Fin n → Rat := fun j => v j - μV
      (dotFin p v = dotFin p vc + μV) ∧
      (dotFin pHat qV - dotFin p v =
        δP * μV +
        dotFin (fun j => pHat j - p j) vc +
        dotFin pHat (fun j => qV j - v j)) ∧
      ((dotFin pHat qVc + μV) - dotFin p v = dotFin pHat qVc - dotFin p vc) ∧
      ((dotFin pHat qVc + μV) - dotFin p v =
        dotFin (fun j => pHat j - p j) vc +
        dotFin pHat (fun j => qVc j - vc j)) :=
  UnsignedFp4SoftmaxV.attention_v_centering_simplex_drift_annihilation

theorem raw_v_e2m1_level_collapse_vs_centered_invariance :
    e2m1SignedLevels.length = 15 ∧
    (∀ μ R : Rat, (0 : Rat) < R → (4 : Rat) ≤ ratAbs μ / R →
      countLevelsInInterval e2m1SignedLevels ((ratAbs μ - R) / (ratAbs μ + R)) 1 ≤ 2) ∧
    (∀ μ R : Rat, (0 : Rat) < R → (8 : Rat) ≤ ratAbs μ / R →
      countLevelsInInterval e2m1SignedLevels ((ratAbs μ - R) / (ratAbs μ + R)) 1 ≤ 1) ∧
    (∀ μ R : Rat, (0 : Rat) < R →
      let S_raw := ratAbs μ + R
      let S_c := R
      S_raw / S_c = 1 + ratAbs μ / R ∧
      ((μ + R) - μ) / S_c = 1 ∧
      ((μ - R) - μ) / S_c = -1 ∧
      countLevelsInInterval e2m1SignedLevels (((μ - R) - μ) / S_c) (((μ + R) - μ) / S_c) = 15) ∧
    (countLevelsInInterval e2m1SignedLevels (-1) 1 = 15 ∧
     countLevelsInInterval e2m1SignedLevels (-1 / 3) 1 = 12 ∧
     countLevelsInInterval e2m1SignedLevels 0 1 = 8 ∧
     countLevelsInInterval e2m1SignedLevels (1 / 3) 1 = 4 ∧
     countLevelsInInterval e2m1SignedLevels (3 / 5) 1 = 2 ∧
     countLevelsInInterval e2m1SignedLevels (7 / 9) 1 = 1) :=
  UnsignedFp4SoftmaxV.raw_v_e2m1_level_collapse_vs_centered_invariance

end UnsignedFp4SoftmaxVChallenge
