/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnBwdSignflip.Defs

/-!
# Trusted Challenge Statements (`flashattn-bwd-signflip`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Softmax-Jacobian zero-sum conservation and exact cancellation-free identity.
2. Peaked-Softmax spurious sign-flip threshold at `ε ≤ 2^{-(m+2)}` (exactly one of `±c` flips the sign).
3. Direct `P · dP` midpoint DC-leakage law `Z_direct^* = 1 / (2^{m+1} + 1)`.
4. FlashAttention `D_i = dO · fl(O)` orthogonal divergence amplification (`u_fwd · κ_orth`).
5. Key-centering `dQ = dS (K - 1 K_bar^T)` zero-bias invariance and spurious-bias elimination.
6. Ratio `16` between the dynamic ranges of the hand-written records of unsigned 4-bit `U-E3M1` and signed `MXFP4-E2M1`.
-/

namespace FlashAttnBwdSignflipChallenge

open FlashAttnBwdSignflip

/-- Theorem 1 (`softmax_jacobian_zero_sum_and_cancellation_free_identity`):
    Universal exact algebraic theorem over `Rat` for any `p, dP : Fin n → Rat`:
    proves exact zero-sum conservation `∑_j p_j (dP_j - D) = 0`, exact algebraic equivalence
    `softmaxGradStd p dP i = softmaxGradCF p dP i` for all `i` (and `i = 0`), unconditional
    shift-invariance of `softmaxGradCF`, and exact off-simplex shift leakage of `softmaxGradStd`. -/
theorem softmax_jacobian_zero_sum_and_cancellation_free_identity :
    (∀ (n : Nat) (p dP : Fin n → Rat), finSum p = 1 →
      finSum (fun j => softmaxGradStd p dP j) = 0) ∧
    (∀ (n : Nat) (p dP : Fin n → Rat) (i : Fin n), finSum p = 1 →
      softmaxGradStd p dP i = softmaxGradCF p dP i) ∧
    (∀ (n : Nat) (hn : 0 < n) (p dP : Fin n → Rat), finSum p = 1 →
      softmaxGradStd p dP ⟨0, hn⟩ = softmaxGradCF p dP ⟨0, hn⟩) ∧
    (∀ (n : Nat) (pHat dP : Fin n → Rat) (c : Rat) (i : Fin n),
      softmaxGradCF pHat (fun j => dP j + c) i = softmaxGradCF pHat dP i) ∧
    (∀ (n : Nat) (pHat dP : Fin n → Rat) (c : Rat) (i : Fin n),
      softmaxGradStd pHat (fun j => dP j + c) i =
        softmaxGradStd pHat dP i + pHat i * (1 - finSum pHat) * c) := by
  sorry

/-- Theorem 2 (`peaked_softmax_half_spurious_signflip_threshold`):
    Theorem about the hand-written predicate `rneSnapsToOne` (defined on `[1 - 2^{-(m+1)}, 1]`)
    proving `fl_m(1 - ε) = 1 ↔ 0 ≤ ε ≤ 2^{-(m+2)}`
    (`1/8` U-E3M1, `1/16` FP8-E5M2, `1/32` FP8-E4M3, `1/512` BF16, `1/4096` FP16),
    strict sign flip of `softmaxGradStd` for all same-sign `|c| > |δ|` (exactly one of `+c`, `-c`
    flips it; a symmetry statement, not a measure over inputs), invariance and zero sign flips for
    `softmaxGradCF`, and
    the universal `m`-bit 2-token witness at `ε = 2^{-(m+2)}, dP = (1, 1/2)`. -/
theorem peaked_softmax_half_spurious_signflip_threshold :
    (∀ (m : Nat) (ε : Rat), rneSnapsToOne m (1 - ε) ↔ ((0 : Rat) ≤ ε ∧ ε ≤ epsSnap m)) ∧
    (epsSnap 1 = 1 / 8 ∧ epsSnap 2 = 1 / 16 ∧ epsSnap 3 = 1 / 32 ∧
     epsSnap 7 = 1 / 512 ∧ epsSnap 10 = 1 / 4096) ∧
    (∀ (n : Nat) (hn : 0 < n) (pHat : Fin n → Rat) (ε c δ : Rat),
      0 < ε → ε < 1 → pHat ⟨0, hn⟩ = 1 →
      0 < finSumExcept ⟨0, hn⟩ pHat → δ ≠ 0 →
      let i0 : Fin n := ⟨0, hn⟩
      let εHat := finSumExcept i0 pHat
      let dS_true := (1 - ε) * ε * δ
      (finSum pHat = 1 + εHat ∧ 1 < finSum pHat) ∧
      (softmaxGradStd pHat (offsetGrad hn c δ) i0 = εHat * (δ - c)) ∧
      (softmaxGradCF pHat (offsetGrad hn c δ) i0 = εHat * δ) ∧
      (0 < softmaxGradCF pHat (offsetGrad hn c δ) i0 * dS_true) ∧
      (((0 < δ ∧ δ < c) ∨ (c < δ ∧ δ < 0)) →
        softmaxGradStd pHat (offsetGrad hn c δ) i0 * dS_true < 0) ∧
      (ratAbs δ < ratAbs c →
        (softmaxGradStd pHat (offsetGrad hn c δ) i0 * dS_true < 0 ∧
         0 < softmaxGradStd pHat (offsetGrad hn (-c) δ) i0 * dS_true) ∨
        (0 < softmaxGradStd pHat (offsetGrad hn c δ) i0 * dS_true ∧
         softmaxGradStd pHat (offsetGrad hn (-c) δ) i0 * dS_true < 0))) ∧
    (∀ m : Nat, 1 ≤ m →
      let ε := epsSnap m
      let pHat2 : Fin 2 → Rat := fun j => if j.val = 0 then 1 else ε
      let dP2 : Fin 2 → Rat := fun j => if j.val = 0 then 1 else 1 / 2
      rneSnapsToOne m (1 - ε) ∧
      0 < (1 - ε) * ε * (1 / 2 : Rat) ∧
      softmaxGradStd pHat2 dP2 ⟨0, by decide⟩ = -invPow2Rat (m + 3) ∧
      softmaxGradStd pHat2 dP2 ⟨0, by decide⟩ < 0 ∧
      softmaxGradCF pHat2 dP2 ⟨0, by decide⟩ = invPow2Rat (m + 3) ∧
      0 < softmaxGradCF pHat2 dP2 ⟨0, by decide⟩) := by
  sorry

/-- Theorem 3 (`direct_p_dp_midpoint_dc_leakage_exact`):
    Universal exact rational theorem proving the midpoint zero-sum drift bound
    `Z_direct^* = 1 / (2^{m+1} + 1)` (`1/5` MXFP4, `1/9` FP8-E5M2, `1/17` FP8-E4M3,
    `1/257` BF16, `1/2049` FP16) and `Z_jac^* = 1` (100% of true Jacobian L1 norm),
    plus the universal relative-error upper bound `Z_direct ≤ 2^{-(m+1)}`. -/
theorem direct_p_dp_midpoint_dc_leakage_exact :
    (directMidpointLeakage 1 = 1 / 5 ∧
     directMidpointLeakage 2 = 1 / 9 ∧
     directMidpointLeakage 3 = 1 / 17 ∧
     directMidpointLeakage 7 = 1 / 257 ∧
     directMidpointLeakage 10 = 1 / 2049) ∧
    (∀ (m : Nat) (s : Rat), 0 < s →
      let p : Fin 2 → Rat := fun _ => 1 / 2
      let dP : Fin 2 → Rat := fun j => if j.val = 0 then s * (1 + invPow2Rat m) else s
      let dTrue := softmaxD p dP
      finSum p = 1 ∧
      dTrue = s * (1 + invPow2Rat (m + 1)) ∧
      rneRoundsToLowerEven m s dTrue ∧
      finSum (fun j => softmaxGradWithD p dP s j) = s * invPow2Rat (m + 1) ∧
      hadamardL1 p dP = s * (1 + invPow2Rat (m + 1)) ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP s j)) / hadamardL1 p dP =
        directMidpointLeakage m ∧
      finSum (fun j => ratAbs (softmaxGradStd p dP j)) = s * invPow2Rat (m + 1) ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP s j)) /
        finSum (fun j => ratAbs (softmaxGradStd p dP j)) = 1) ∧
    (∀ (n m : Nat) (p dP : Fin n → Rat) (dHat : Rat),
      finSum p = 1 →
      ratAbs (dHat - softmaxD p dP) ≤ invPow2Rat (m + 1) * ratAbs (softmaxD p dP) →
      ratAbs (finSum (fun j => softmaxGradWithD p dP dHat j)) ≤
        invPow2Rat (m + 1) * hadamardL1 p dP) := by
  sorry

/-- Theorem 4 (`flashattn_do_o_orthogonal_divergence_amplification`):
    Exact algebraic law proving `D_i^{FA} = dO · fl(O)` introduces DC-leakage `-⟨dO, δO⟩`
    governed by `u_fwd · κ_orth` (both L1 Hadamard and L2 Cauchy-Schwarz forms), with
    an explicit parametric rational family achieving arbitrarily large blowup (`> 1000×`
    worse than direct `P · dP` at `ε_v = 1/1001`) and exact witnesses at `ε_v = 1/256`. -/
theorem flashattn_do_o_orthogonal_divergence_amplification :
    (∀ (n d : Nat) (p dP : Fin n → Rat) (dO O oHat : Fin d → Rat) (uFwd : Rat),
      finSum p = 1 →
      dotProd dO O = softmaxD p dP →
      0 ≤ uFwd →
      (∀ k : Fin d, ratAbs (oHat k - O k) ≤ uFwd * ratAbs (O k)) →
      let δO : Fin d → Rat := fun k => oHat k - O k
      let dFA := dotProd dO oHat
      finSum (fun j => softmaxGradWithD p dP dFA j) = -dotProd dO δO ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP dFA j)) ≤ uFwd * hadamardL1 dO O ∧
      (0 < hadamardL1 p dP →
        ratAbs (finSum (fun j => softmaxGradWithD p dP dFA j)) / hadamardL1 p dP ≤
          uFwd * (hadamardL1 dO O / hadamardL1 p dP)) ∧
      dotProd dO δO * dotProd dO δO ≤ (uFwd * uFwd) * l2NormSq dO * l2NormSq O) ∧
    (∀ (m : Nat) (ε_v : Rat), 0 < ε_v →
      let u := invPow2Rat (m + 1)
      let p : Fin 2 → Rat := fun _ => 1 / 2
      let O : Fin 2 → Rat := fun k => if k.val = 0 then 1 + u else 1
      let oHat : Fin 2 → Rat := fun _ => 1
      let dO : Fin 2 → Rat := fun k => if k.val = 0 then 1 else -(1 + u)
      let V0 : Fin 2 → Rat := fun k => if k.val = 0 then 1 + u else 1 + ε_v
      let V1 : Fin 2 → Rat := fun k => if k.val = 0 then 1 + u else 1 - ε_v
      let dP : Fin 2 → Rat := fun j => if j.val = 0 then dotProd dO V0 else dotProd dO V1
      rneRoundsToLowerEven m 1 (O ⟨0, by decide⟩) ∧
      (∀ k : Fin 2, (1 / 2 : Rat) * V0 k + (1 / 2 : Rat) * V1 k = O k) ∧
      dotProd dO O = 0 ∧
      softmaxD p dP = 0 ∧
      dotProd dO oHat = -u ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP (dotProd dO oHat) j)) / hadamardL1 p dP =
        directMidpointLeakage m / ε_v) ∧
    (∀ (m : Nat) (M : Rat), 0 < M →
      directMidpointLeakage m / (directMidpointLeakage m / M) = M) ∧
    (∀ m : Nat,
      directMidpointLeakage m / (1 / 1001 : Rat) = 1001 * directMidpointLeakage m ∧
      1000 * directMidpointLeakage m < directMidpointLeakage m / (1 / 1001 : Rat)) ∧
    (directMidpointLeakage 7 / (1 / 256 : Rat) = 256 / 257 ∧
     directMidpointLeakage 3 / (1 / 256 : Rat) = 256 / 17 ∧
     directMidpointLeakage 2 / (1 / 256 : Rat) = 256 / 9 ∧
     directMidpointLeakage 1 / (1 / 256 : Rat) = 256 / 5) := by
  sorry

/-- Theorem 5 (`key_centering_dq_invariance_exact`):
    Universal exact algebraic theorem proving exact zero-bias invariance `dS (K - 1 K_bar^T) = dS K`
    whenever `∑_j dS_j = 0`, exact elimination of spurious bias `δ_S K_bar^T` under drift
    `∑_j dSHat_j = δ_S`, and the exact cosine-similarity collapse law `cos^2 → 0` under
    uncentered orthogonal key bias. -/
theorem key_centering_dq_invariance_exact :
    (∀ (n d : Nat) (dS : Fin n → Rat) (K : Fin n → Fin d → Rat) (kBar : Fin d → Rat) (c : Fin d),
      dqEntry dS K c - dqEntry dS (centeredKey K kBar) c = finSum dS * kBar c) ∧
    (∀ (n d : Nat) (dS : Fin n → Rat) (K : Fin n → Fin d → Rat) (kBar : Fin d → Rat) (c : Fin d),
      finSum dS = 0 → dqEntry dS (centeredKey K kBar) c = dqEntry dS K c) ∧
    (∀ (n d : Nat) (dSHat : Fin n → Rat) (K0 : Fin n → Fin d → Rat) (kBar : Fin d → Rat) (δS : Rat),
      finSum dSHat = δS →
      let K : Fin n → Fin d → Rat := fun j c => K0 j c + kBar c
      (∀ c : Fin d, dqEntry dSHat (centeredKey K kBar) c = dqEntry dSHat K0 c) ∧
      (∀ c : Fin d, dqEntry dSHat K c = dqEntry dSHat K0 c + δS * kBar c)) ∧
    (∀ (d : Nat) (dQ0 kBar : Fin d → Rat) (δS : Rat),
      dotProd dQ0 kBar = 0 →
      0 < l2NormSq dQ0 →
      δS ≠ 0 →
      0 < l2NormSq kBar →
      let dQ_biased : Fin d → Rat := fun c => dQ0 c + δS * kBar c
      dotProd dQ0 dQ_biased = l2NormSq dQ0 ∧
      l2NormSq dQ_biased = l2NormSq dQ0 + (δS * δS) * l2NormSq kBar ∧
      (dotProd dQ0 dQ_biased * dotProd dQ0 dQ_biased) / (l2NormSq dQ0 * l2NormSq dQ_biased) =
        l2NormSq dQ0 / (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar) ∧
      (∀ (ε s : Rat), 0 < ε →
        l2NormSq dQ0 < ε * ((δS * δS) * (s * s) * l2NormSq kBar) →
        let dQ_s : Fin d → Rat := fun c => dQ0 c + δS * (s * kBar c)
        (dotProd dQ0 dQ_s * dotProd dQ0 dQ_s) / (l2NormSq dQ0 * l2NormSq dQ_s) < ε)) := by
  sorry

/-- Theorem 6 (`unsigned_ue3m1_vs_mxfp4_dynamic_range_16x_exact`):
    Constant-level theorem: the hand-written record `fmtUE3M1` has `16×` the dynamic range
    (`192` vs `12` full, `96` vs `6` normal) of the unscaled record `fmtMXFP4` and a `16×` lower
    subnormal floor (`1/128` vs `1/8`, the latter taken from the block-scaled record `fmtMXFP4Prob`)
    than the signed `MXFP4-E2M1` records, at identical 4-bit width and 1-bit mantissa; the ratios
    follow from the constants chosen in the records,
    together with companion 8-bit `FP8-E5M2` vs `FP8-E4M3` ratios (`16384×` full, `32768×` normal,
    `2×` roundoff) and the universal sign-bit-to-exponent reallocation identity. -/
theorem unsigned_ue3m1_vs_mxfp4_dynamic_range_16x_exact :
    (fmtUE3M1.totalBits = 4 ∧ fmtMXFP4.totalBits = 4 ∧ fmtMXFP4Prob.totalBits = 4 ∧
     fmtUE3M1.mbits = 1 ∧ fmtMXFP4.mbits = 1 ∧
     fmtUE3M1.unitRoundoff = 1 / 4 ∧ fmtMXFP4.unitRoundoff = 1 / 4) ∧
    (fmtUE3M1.dynRangeFull = 192 ∧ fmtMXFP4.dynRangeFull = 12 ∧
     fmtUE3M1.dynRangeFull / fmtMXFP4.dynRangeFull = 16 ∧
     fmtUE3M1.dynRangeNormal = 96 ∧ fmtMXFP4.dynRangeNormal = 6 ∧
     fmtUE3M1.dynRangeNormal / fmtMXFP4.dynRangeNormal = 16) ∧
    (fmtMXFP4Prob.minSubnormal / fmtUE3M1.minSubnormal = 16 ∧
     (∀ p : Rat, fmtUE3M1.minSubnormal ≤ p → p < fmtMXFP4Prob.minSubnormal / 2 →
       (1 / 128 : Rat) ≤ p ∧ p < (1 / 16 : Rat)) ∧
     (fmtUE3M1.minSubnormal ≤ (1 / 32 : Rat) ∧ (1 / 32 : Rat) < fmtMXFP4Prob.minSubnormal / 2)) ∧
    (fmtE5M2.totalBits = 8 ∧ fmtE4M3.totalBits = 8 ∧
     fmtE5M2.dynRangeFull = 3758096384 ∧ fmtE4M3.dynRangeFull = 229376 ∧
     fmtE5M2.dynRangeFull / fmtE4M3.dynRangeFull = 16384 ∧
     fmtE5M2.dynRangeNormal = 939524096 ∧ fmtE4M3.dynRangeNormal = 28672 ∧
     fmtE5M2.dynRangeNormal / fmtE4M3.dynRangeNormal = 32768 ∧
     fmtE5M2.unitRoundoff / fmtE4M3.unitRoundoff = 2) ∧
    ((∀ e_s : Nat, 2 ^ (2 ^ (e_s + 1) - 2 ^ e_s) = 2 ^ (2 ^ e_s)) ∧
     2 ^ (2 ^ 2) = 16) := by
  sorry

end FlashAttnBwdSignflipChallenge
