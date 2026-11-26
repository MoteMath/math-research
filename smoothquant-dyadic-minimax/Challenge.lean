/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SmoothquantDyadic.Defs

/-!
# Trusted Challenge Statements (`smoothquant-dyadic-minimax`)

Universal and exact pure-`Init` (zero Mathlib, zero `native_decide`) Lean 4 statements for:
1. Asymmetric-Bitwidth SmoothQuant AM-GM optimal scale, classical `SQ(0.5)` suboptimality
   (`8089/889` W4A8, `8069/381` W3A8, `8065/127` W2A8), and critical clamping threshold
   `M_crit = q_X / q_W`.
2. Zero-FLOP dyadic power-of-2 SmoothQuant per-channel `L_2^2` sharp worst-case bound `5/4`.
3. Zero-FLOP dyadic power-of-2 SmoothQuant per-channel squared `L_1` sharp worst-case bound `9/8`.
4. Per-tensor coupled dyadic rounding sharp worst-case `5/2` vs global phase-shifted `3/2`.
5. `SmoothQuant -> Hadamard` non-commutation and parametric `Ω(M^2)` separation over both
   `Pure Hadamard` and every `Hadamard -> SQ` diagonal scaling.
6. Channel-outlier coupling paradox under asymmetric bitwidths (`M < M_crit^2`).
-/

namespace SmoothquantDyadicChallenge

open SmoothquantDyadic

/-- Theorem 1 (Asymmetric-Bitwidth SmoothQuant AM-GM Optimal Scale & Critical Clamp):
    Proves universal AM-GM optimality of `s^4 = B / A` for `E(A, B, s) = A s^2 + B / s^2`,
    exact rational suboptimality `(q_X^2 + q_W^2) / (2 q_W q_X)` of classical `SQ(0.5)`
    (`8089/889` W4A8, `8069/381` W3A8, `8065/127` W2A8, `505/217` W4A6, `25/7` W2A4),
    and the exact critical clamping threshold `M_crit = q_X / q_W` (`127/7`, `127/3`, `127`). -/
theorem smoothquant_asymmetric_amgm_optimal_scale :
    (∀ A B s : Rat, s ≠ 0 →
      bilinearErr A B s * bilinearErr A B s - 4 * A * B =
        (A * (s * s) - B / (s * s)) * (A * (s * s) - B / (s * s)) ∧
      4 * A * B ≤ bilinearErr A B s * bilinearErr A B s) ∧
    (∀ A B c s : Rat, 0 < A → 0 < B → 0 < c → c * c = A * B → 0 < s →
      bilinearErr A B s - 2 * c =
        (A * (s * s) - c) * (A * (s * s) - c) / (A * (s * s)) ∧
      2 * c ≤ bilinearErr A B s ∧
      (bilinearErr A B s = 2 * c ↔ s * s * s * s = B / A)) ∧
    (∀ qW qX u : Rat, 0 < qW → 0 < qX → 0 < u →
      interiorChannelErr qW qX (qX / qW) = 2 / (qW * qX) ∧
      interiorChannelErr qW qX u - interiorChannelErr qW qX (qX / qW) =
        (qW * u - qX) * (qW * u - qX) / (qW * qW * qX * qX * u) ∧
      interiorChannelErr qW qX (qX / qW) ≤ interiorChannelErr qW qX u ∧
      interiorChannelErr qW qX 1 / interiorChannelErr qW qX (qX / qW) =
        sqHalfPenaltyRatio qW qX ∧
      sqHalfPenaltyRatio qW qX = 1 + (qX - qW) * (qX - qW) / (2 * qW * qX) ∧
      1 ≤ sqHalfPenaltyRatio qW qX ∧
      (qW ≠ qX → 1 < sqHalfPenaltyRatio qW qX)) ∧
    ((sqHalfPenaltyRatio 7 7 = 1 ∧ criticalClampThreshold 7 7 = 1) ∧
     (sqHalfPenaltyRatio 7 31 = 505 / 217 ∧ criticalClampThreshold 7 31 = 31 / 7) ∧
     (sqHalfPenaltyRatio 1 7 = 25 / 7 ∧ criticalClampThreshold 1 7 = 7) ∧
     (sqHalfPenaltyRatio 7 127 = 8089 / 889 ∧ criticalClampThreshold 7 127 = 127 / 7) ∧
     (sqHalfPenaltyRatio 3 127 = 8069 / 381 ∧ criticalClampThreshold 3 127 = 127 / 3) ∧
     (sqHalfPenaltyRatio 1 127 = 8065 / 127 ∧ criticalClampThreshold 1 127 = 127)) ∧
    (∀ qW qX M u : Rat, 0 < qW → 0 < qX → 1 ≤ M → 1 < u →
      M ≤ criticalClampThreshold qW qX →
      bulkChannelErr qW qX M 1 < bulkChannelErr qW qX M u) ∧
    (∀ qW qX M : Rat, 0 < qW → 0 < qX → criticalClampThreshold qW qX < M →
      1 < M * qW / qX ∧
      bulkChannelErr qW qX M (M * qW / qX) < bulkChannelErr qW qX M 1) := by
  sorry

/-- Theorem 2 (Dyadic Power-of-2 SmoothQuant Per-Channel `L_2^2` Sharp Bound `5/4`):
    Proves that rounding any positive optimal scale `s*` to its nearest power of 2
    (`1/2 ≤ (s_dyad / s*)^2 ≤ 2`) increases per-channel `L_2^2` error by at most `5/4`,
    strictly `< 5/4` on `(1/2, 2)`, and attained exactly at `u = 2` and `u = 1/2`. -/
theorem dyadic_smoothquant_perchannel_l2_5_over_4_sharp :
    (∀ u : Rat, u ≠ 0 →
      (5 / 4 : Rat) - dyadicL2SqPenalty u = (2 - u) * (2 * u - 1) / (4 * u)) ∧
    (∀ u : Rat, (1 / 2 : Rat) ≤ u → u ≤ 2 → dyadicL2SqPenalty u ≤ 5 / 4) ∧
    (∀ u : Rat, (1 / 2 : Rat) < u → u < 2 → dyadicL2SqPenalty u < 5 / 4) ∧
    (∀ A B s_opt s_dyad : Rat,
      0 < A → 0 < B → 0 < s_opt → 0 < s_dyad →
      A * (s_opt * s_opt) = B / (s_opt * s_opt) →
      (1 / 2 : Rat) ≤ (s_dyad / s_opt) * (s_dyad / s_opt) →
      (s_dyad / s_opt) * (s_dyad / s_opt) ≤ 2 →
      bilinearErr A B s_dyad ≤ (5 / 4 : Rat) * bilinearErr A B s_opt) ∧
    (dyadicL2SqPenalty 2 = 5 / 4 ∧ dyadicL2SqPenalty (1 / 2) = 5 / 4) := by
  sorry

/-- Theorem 3 (Dyadic Power-of-2 SmoothQuant Per-Channel Squared `L_1` Sharp Bound `9/8`):
    Proves that rounding any positive optimal scale `s*` to its nearest power of 2
    increases per-channel `L_1` error `A s + B / s` by at most `3 / (2√2)` (squared: `9/8`),
    attained exactly at `u = 2` and `u = 1/2`. -/
theorem dyadic_smoothquant_perchannel_l1_9_over_8_sharp :
    (∀ u : Rat, u ≠ 0 →
      (9 / 8 : Rat) - dyadicL1SqPenalty u = (2 - u) * (2 * u - 1) / (8 * u)) ∧
    (∀ u : Rat, (1 / 2 : Rat) ≤ u → u ≤ 2 → dyadicL1SqPenalty u ≤ 9 / 8) ∧
    (∀ r : Rat, 0 < r → (1 / 2 : Rat) ≤ r * r → r * r ≤ 2 →
      ((r + 1 / r) / 2) * ((r + 1 / r) / 2) ≤ 9 / 8) ∧
    (∀ A B s_opt s_dyad : Rat,
      0 < A → 0 < B → 0 < s_opt → 0 < s_dyad →
      A * s_opt = B / s_opt →
      (1 / 2 : Rat) ≤ (s_dyad / s_opt) * (s_dyad / s_opt) →
      (s_dyad / s_opt) * (s_dyad / s_opt) ≤ 2 →
      bilinearL1Err A B s_dyad * bilinearL1Err A B s_dyad ≤
        (9 / 8 : Rat) * (bilinearL1Err A B s_opt * bilinearL1Err A B s_opt)) ∧
    (dyadicL1SqPenalty 2 = 9 / 8 ∧ dyadicL1SqPenalty (1 / 2) = 9 / 8) := by
  sorry

/-- Theorem 4 (Per-Tensor Coupled Dyadic Rounding: Naive `5/2` vs Phase-Shifted `3/2`):
    Proves naive per-tensor coupled power-of-2 rounding suffers exact sharp worst-case `5/2`,
    whereas a single zero-FLOP global dyadic phase shift slashes the `d = 2` worst-case bound
    to exact sharp `3/2`, with universal upper bounds, exact attainment witnesses, and an
    all-exponents impossibility lower bound `≥ 3/2`. -/
theorem dyadic_smoothquant_pertensor_5_2_vs_phase_shift_3_2 :
    (∀ mwSq mxSq u : Rat, (1 / 2 : Rat) ≤ u → u ≤ 2 → mwSq ≤ 2 → mxSq ≤ 2 →
      perTensorCoupledChannelPenalty mwSq mxSq u ≤ 5 / 2) ∧
    (∀ u1 u2 : Rat, (1 / 2 : Rat) ≤ u1 → u1 ≤ 2 → (1 / 2 : Rat) ≤ u2 → u2 ≤ 2 →
      perTensorCoupledD2Penalty u1 u2 ≤ 5 / 2) ∧
    (perTensorCoupledD2Penalty 2 (1 / 2) = 5 / 2 ∧
     perTensorCoupledChannelPenalty 2 2 2 = 5 / 2 ∧
     perTensorCoupledChannelPenalty 2 2 (1 / 2) = 5 / 2) ∧
    (∀ u1 u2 : Rat, 0 < u1 → 0 < u2 →
      perTensorCoupledD2Penalty u1 u2 = (1 + ratMax (u2 / u1) (u1 / u2)) / 2) ∧
    (∀ u2 : Rat, (1 / 2 : Rat) ≤ u2 → u2 ≤ 2 →
      perTensorCoupledD2Penalty 1 u2 ≤ 3 / 2) ∧
    (perTensorCoupledD2Penalty 1 2 = 3 / 2 ∧
     perTensorCoupledD2Penalty 1 (1 / 2) = 3 / 2 ∧
     (3 / 2 : Rat) < 5 / 2) ∧
    (∀ (e1 e2 : Int) (lamSq : Rat), 0 < lamSq →
      (3 / 2 : Rat) ≤ perTensorCoupledD2Penalty
        (pow2IntRat (2 * e1) / lamSq) (pow2IntRat (2 * e2 - 1) / lamSq)) := by
  sorry

/-- Theorem 5 (`SmoothQuant -> Hadamard` Non-Commutation & Parametric `Ω(M^2)` Separation):
    Exhibits an explicit parametric family `(W(M), X(M))` (`M ≥ 1`) where `diag(M, 1)` and `H_2`
    do not commute, all three factorizations preserve `W X` identically, `SQ -> Hadamard`
    achieves `O(1)` error `8 (1/q_W^2 + 1/q_X^2)`, while both `Pure Hadamard` and EVERY
    `Hadamard -> diag(s0, s1)` (`s0, s1 > 0`) incur error strictly exceeding `(M^2 / 8)` times
    `SQ -> Hadamard` for all `M ≥ 1` (and strictly worse for every `M > 1`). -/
theorem smoothquant_hadamard_noncommutation_separation :
    (∀ M : Rat, M ≠ 1 →
      mat2Mul (mat2Diag M 1) hadamard2 ≠ mat2Mul hadamard2 (mat2Diag M 1)) ∧
    (∀ M : Rat, M ≠ 0 →
      mat2Scale (1 / 2)
        (mat2Mul (mat2Mul (mat2Mul (antiOutlierW M) (mat2Diag M 1)) hadamard2)
                 (mat2Mul hadamard2 (mat2Mul (mat2Diag (1 / M) 1) (antiOutlierX M)))) =
      mat2Mul (antiOutlierW M) (antiOutlierX M) ∧
      mat2Scale (1 / 2)
        (mat2Mul (mat2Mul (antiOutlierW M) hadamard2)
                 (mat2Mul hadamard2 (antiOutlierX M))) =
      mat2Mul (antiOutlierW M) (antiOutlierX M)) ∧
    (∀ M s0 s1 : Rat, s0 ≠ 0 → s1 ≠ 0 →
      mat2Scale (1 / 2)
        (mat2Mul (mat2Mul (mat2Mul (antiOutlierW M) hadamard2) (mat2Diag s0 s1))
                 (mat2Mul (mat2Diag (1 / s0) (1 / s1)) (mat2Mul hadamard2 (antiOutlierX M)))) =
      mat2Mul (antiOutlierW M) (antiOutlierX M)) ∧
    (∀ qW qX M s0 s1 : Rat, 0 < qW → 0 < qX → 1 ≤ M → 0 < s0 → 0 < s1 →
      let Wsh := mat2Mul (mat2Mul (antiOutlierW M) (mat2Diag M 1)) hadamard2
      let Xsh := mat2Mul hadamard2 (mat2Mul (mat2Diag (1 / M) 1) (antiOutlierX M))
      let Wh  := mat2Mul (antiOutlierW M) hadamard2
      let Xh  := mat2Mul hadamard2 (antiOutlierX M)
      let Whs := mat2Mul Wh (mat2Diag s0 s1)
      let Xhs := mat2Mul (mat2Diag (1 / s0) (1 / s1)) Xh
      mat2QuantErrProxy qW qX 2 Wsh Xsh = 8 * (1 / (qW * qW) + 1 / (qX * qX)) ∧
      mat2QuantErrProxy qW qX 2 Wh Xh =
        (M + 1) * (M + 1) * (1 + 1 / (M * M)) * (1 / (qW * qW) + 1 / (qX * qX)) ∧
      mat2QuantErrProxy qW qX 2 Wh Xh / mat2QuantErrProxy qW qX 2 Wsh Xsh =
        (M + 1) * (M + 1) * (1 + 1 / (M * M)) / 8 ∧
      (M * M) / 8 < mat2QuantErrProxy qW qX 2 Wh Xh / mat2QuantErrProxy qW qX 2 Wsh Xsh ∧
      mat2QuantErrProxy qW qX 2 Wh Xh ≤ mat2QuantErrProxy qW qX 2 Whs Xhs ∧
      (M * M) / 8 < mat2QuantErrProxy qW qX 2 Whs Xhs / mat2QuantErrProxy qW qX 2 Wsh Xsh ∧
      (1 < M →
        mat2QuantErrProxy qW qX 2 Wsh Xsh < mat2QuantErrProxy qW qX 2 Wh Xh ∧
        mat2QuantErrProxy qW qX 2 Wsh Xsh < mat2QuantErrProxy qW qX 2 Whs Xhs)) := by
  sorry

/-- Theorem 6 (Exact Channel-Outlier Coupling Paradox under Asymmetric Bitwidths):
    Proves that with activation outlier `M > 1` only (no weight outliers), classical `SQ(0.5)`
    strictly worsens bilinear quantization error compared to unscaled quantization iff
    `M < M_crit^2 = (q_X / q_W)^2`, with exact W4A8 (`q_W = 7, q_X = 127`) witnesses at
    `M = 32` (`517696/66305 > 7x` worse), `M = 16` (`258848/28673 > 9x` worse), and sign flip
    at `M = 330 > 16129/49`. -/
theorem channel_outlier_coupling_paradox_exact :
    (∀ qW qX M : Rat, 0 < qW → 0 < qX → 0 < M →
      bulkChannelErr qW qX M M - bulkChannelErr qW qX M 1 =
        (M - 1) * (qX * qX - M * qW * qW) / (M * M * qW * qW * qX * qX)) ∧
    (∀ qW qX M : Rat, 0 < qW → 0 < qX → 1 < M →
      (bulkChannelErr qW qX M 1 < bulkChannelErr qW qX M M ↔
        M < criticalClampThreshold qW qX * criticalClampThreshold qW qX)) ∧
    (∀ (qW qX M : Rat) (k b : Nat), 0 < qW → 0 < qX → 1 < M → 1 ≤ b →
      (totalCoupledErr qW qX M 1 k b < totalCoupledErr qW qX M M k b ↔
        M < criticalClampThreshold qW qX * criticalClampThreshold qW qX)) ∧
    ((criticalClampThreshold 7 127 * criticalClampThreshold 7 127 = 16129 / 49) ∧
     (bulkChannelErr 7 127 32 1 < bulkChannelErr 7 127 32 32 ∧
      bulkChannelErr 7 127 32 32 / bulkChannelErr 7 127 32 1 = 517696 / 66305 ∧
      (7 : Rat) < 517696 / 66305) ∧
     (bulkChannelErr 7 127 16 1 < bulkChannelErr 7 127 16 16 ∧
      bulkChannelErr 7 127 16 16 / bulkChannelErr 7 127 16 1 = 258848 / 28673 ∧
      (9 : Rat) < 258848 / 28673) ∧
     (bulkChannelErr 7 127 330 330 < bulkChannelErr 7 127 330 1)) := by
  sorry

end SmoothquantDyadicChallenge
