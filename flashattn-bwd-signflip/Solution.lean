/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnBwdSignflip

/-!
# Verified Solutions (`flashattn-bwd-signflip`)
-/

namespace FlashAttnBwdSignflipChallenge

open FlashAttnBwdSignflip

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
        softmaxGradStd pHat dP i + pHat i * (1 - finSum pHat) * c) :=
  FlashAttnBwdSignflip.softmax_jacobian_zero_sum_and_cancellation_free_identity

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
      0 < softmaxGradCF pHat2 dP2 ⟨0, by decide⟩) :=
  FlashAttnBwdSignflip.peaked_softmax_half_spurious_signflip_threshold

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
        invPow2Rat (m + 1) * hadamardL1 p dP) :=
  FlashAttnBwdSignflip.direct_p_dp_midpoint_dc_leakage_exact

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
     directMidpointLeakage 1 / (1 / 256 : Rat) = 256 / 5) :=
  FlashAttnBwdSignflip.flashattn_do_o_orthogonal_divergence_amplification

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
        (dotProd dQ0 dQ_s * dotProd dQ0 dQ_s) / (l2NormSq dQ0 * l2NormSq dQ_s) < ε)) :=
  FlashAttnBwdSignflip.key_centering_dq_invariance_exact

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
     2 ^ (2 ^ 2) = 16) :=
  FlashAttnBwdSignflip.unsigned_ue3m1_vs_mxfp4_dynamic_range_16x_exact

end FlashAttnBwdSignflipChallenge
