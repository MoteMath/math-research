/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnsignedFp4SoftmaxV.Defs

/-!
# Trusted Challenge Statements (`unsigned-fp4-softmax-v`)

Universal and exact pure-`Init` (zero Mathlib, zero `native_decide`) Lean 4 statements for:
1. IEEE `U-E1M3 == UINT4` exact bit-level collapse (`decodeUnsignedIEEE 1 3 c = c`).
2. Universal all-`B ≥ 2` unsigned 4-bit EF21 contraction law and complete regime classification
   (`U-E0M4` `[2..9]` → `U-E2M2` `[10..130]` → `U-E3M1` `[131..18431]` → `U-E4M0` `[≥ 18432]`),
   plus exact `> 5x`, `> 7.7x`, `> 16x` gains over signed `S-E2M1`.
3. Universal exact Softmax RTN simplex-sum conservation drift bound across all `N ≥ 2` and
   exact `N = 128` instantiations (`S-E2M1 > 84%`, `UINT4 > 80%`, `U-E3M1 < 25%`, `FP8-E4M3 < 6%`).
4. Exact discrete zero-drift pair-antithetic SR (midpoint rows) and zero-carry stratified
   XOR-VDC SR across all dyadic fractional residues `f = k / 2^b`.
5. Universal exact algebraic `V`-centering identity completely annihilating first-order
   simplex-drift bias `δ_P * μ_V ≡ 0`.
6. Raw `V` signed `FP4-E2M1` codebook collapse (`≤ 2` levels at `|μ|/R ≥ 4`, `≤ 1` at `|μ|/R ≥ 8`)
   vs centered `V_c` invariance preserving all `15 / 15` levels with scale compression `1 + |μ|/R`.
-/

namespace UnsignedFp4SoftmaxVChallenge

open UnsignedFp4SoftmaxV

/-- Theorem 1 (Exact IEEE `U-E1M3 == UINT4` Bit-Level Collapse):
    Proves standard IEEE/OCP subnormal `U-E1M3` decodes identically to `U-E0M4` (`UINT4`)
    with integer levels `{0, ..., 15}`, identical normalized rational levels, identical EF21
    contraction `1 - α` for all `B`, and identical Softmax simplex drift for all `N`, alongside
    the exact 16-level integer codebooks of `U-E2M2`, `U-E3M1`, and `U-E4M0`. -/
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
      [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384] := by
  sorry

/-- Theorem 2 (Universal All-`B` Unsigned 4-Bit EF21 Contraction & Regime Classification):
    Proves the universal EF21 contraction upper bound and midpoint attainment
    `1 - α(U, B) = max_k ((B-1) h_k^2) / (1 + (B-1) m_k^2)` for all `B ≥ 2`, proves the
    complete all-`B` optimal unsigned 4-bit regimes (`U-E0M4` on `[2..9]`, `U-E2M2` on `[10..130]`,
    `U-E3M1` on `[131..18431]` with exact tie at `18431`, `U-E4M0` on `[≥ 18432]`), and proves
    exact improvement ratios over signed `S-E2M1` (`> 5x` at `B = 64`, `> 7.7x` at `B = 256`,
    `> 16x` at `B = 1024`). -/
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
      (16 : Rat) < ef21OneMinusAlpha sE2M1Levels 1024 / ef21OneMinusAlpha uE3M1Levels 1024)) := by
  sorry

/-- Theorem 3 (Universal Softmax Simplex RTN Conservation Drift Exact Law):
    Proves the universal worst-case RTN simplex-sum drift bound
    `|1 - ∑ Q(p_j)| ≤ max_k ((N-1) h_k) / (1 + (N-1) m_k)` for all simplex sizes `N ≥ 2`,
    exact downward and upward midpoint attainment, and exact `N = 128` instantiations
    (`S-E2M1 = 127/151 > 84%`, `UINT4 = 127/157 > 80%`, `U-E3M1 = 127/511 < 25%`,
    and universal OCP `FP8-E4M3` bound `127/2187 < 6%` over all 126 adjacent bins). -/
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
          127 / 2187))) := by
  sorry

/-- Theorem 4 (Exact Zero-Drift Pair-Antithetic & Stratified XOR-VDC Stochastic Rounding):
    Proves pair-antithetic SR achieves exact `0` simplex-sum drift on midpoint uniform rows
    (`f = 1/2`), and zero-carry stratified XOR-VDC SR (`(bitRev b j) ^^^ mask`) achieves exact
    `0` simplex-sum drift across ALL dyadic fractional residues `f = k / 2^b` (`0 ≤ k ≤ 2^b`)
    and ALL `b`-bit scrambles `mask < 2^b`. -/
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
      ratAbs (1 - (s + sumFin qVdc)) = 0) := by
  sorry

/-- Theorem 5 (Exact Attention `V`-Centering Simplex-Drift Annihilation):
    For any probability vector `p` (`∑ p_j = 1`), quantized probability `pHat`
    (`∑ pHat_j = 1 + δ_P`), value vector `v`, constant shift `μ_V`, and centered `v_c = v - μ_V`,
    proves exact centering invariance, the raw dual-quantization error decomposition carrying
    first-order simplex-drift bias `δ_P * μ_V`, and the centered identity
    `(pHat^T Q(v_c) + μ_V) - p^T v = pHat^T Q(v_c) - p^T v_c` annihilating `δ_P * μ_V ≡ 0`. -/
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
        dotFin pHat (fun j => qVc j - vc j)) := by
  sorry

/-- Theorem 6 (Raw `V` Signed `FP4-E2M1` Level Collapse vs Centered Invariance):
    Proves raw `V ∈ [μ - R, μ + R]` with bias ratio `|μ| / R ≥ 4` collapses to `≤ 2` active
    signed `FP4-E2M1` levels (and `≤ 1` level for `|μ| / R ≥ 8`), with exact active counts
    `15, 12, 8, 4, 2, 1` at `|μ|/R ∈ {0, 1/2, 1, 2, 4, 8}`, whereas centered `V_c = V - μ`
    is identically invariant to `μ`, compresses scale by exact factor `1 + |μ|/R`, and
    preserves all `15 / 15` signed `FP4-E2M1` levels. -/
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
     countLevelsInInterval e2m1SignedLevels (7 / 9) 1 = 1) := by
  sorry

end UnsignedFp4SoftmaxVChallenge
