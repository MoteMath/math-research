/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VcacheIprXorvdc

/-!
# Verified Solutions (`vcache-ipr-xorvdc-bounds`)
-/

namespace VcacheIprXorvdcChallenge

open VcacheIprXorvdc

theorem ipr_attention_averaging_sr_vs_rne_exact :
    (∀ (L : Nat) (p : Fin L → Rat), 0 < L → (∀ j, (0 : Rat) ≤ p j) → finSum p = 1 →
      1 / (L : Rat) ≤ ipr p ∧ ipr p ≤ 1 ∧ (0 : Rat) < ipr p ∧
      (1 : Rat) ≤ neff p ∧ neff p ≤ (L : Rat)) ∧
    (∀ (L : Nat), 0 < L →
      finSum (uniformWeights L) = 1 ∧
      ipr (uniformWeights L) = 1 / (L : Rat) ∧
      neff (uniformWeights L) = (L : Rat)) ∧
    (∀ (L : Nat) (j0 : Fin L),
      finSum (peakedWeights L j0) = 1 ∧
      ipr (peakedWeights L j0) = 1 ∧
      neff (peakedWeights L j0) = 1) ∧
    (∀ (L : Nat) (p : Fin L → Rat) (sigmaSrSq sigmaRneSq muBias : Rat),
      finSum p = 1 → (0 : Rat) < ipr p →
      srOutputMse p sigmaSrSq = ipr p * sigmaSrSq ∧
      srOutputMse p sigmaSrSq = sigmaSrSq / neff p ∧
      rneOutputMse p muBias sigmaRneSq = muBias * muBias + ipr p * sigmaRneSq ∧
      rneOutputMse p muBias sigmaRneSq = muBias * muBias + sigmaRneSq / neff p) ∧
    (∀ (L : Nat) (p : Fin L → Rat) (sigmaSrSq sigmaRneSq muBias : Rat),
      finSum p = 1 → (0 : Rat) < ipr p → muBias ≠ 0 →
      (srOutputMse p sigmaSrSq < rneOutputMse p muBias sigmaRneSq ↔
        neffThreshold sigmaSrSq sigmaRneSq muBias < neff p) ∧
      (srOutputMse p sigmaSrSq = rneOutputMse p muBias sigmaRneSq ↔
        neff p = neffThreshold sigmaSrSq sigmaRneSq muBias) ∧
      (rneOutputMse p muBias sigmaRneSq < srOutputMse p sigmaSrSq ↔
        neff p < neffThreshold sigmaSrSq sigmaRneSq muBias)) ∧
    (∀ (L : Nat) (j0 : Fin L) (delta : Rat), delta ≠ 0 →
      srUniformVar delta / rneUniformVar delta = 2 ∧
      srOutputMse (peakedWeights L j0) (srUniformVar delta) =
        2 * rneOutputMse (peakedWeights L j0) 0 (rneUniformVar delta)) :=
  VcacheIprXorvdc.ipr_attention_averaging_sr_vs_rne_exact

theorem cross_format_int2_sr_beats_int4_mxfp4_rne :
    (∀ (L : Nat) (p : Fin L → Rat) (sigmaSrLowSq muBiasHigh sigmaRneHighSq : Rat),
      finSum p = 1 → (0 : Rat) < ipr p → muBiasHigh ≠ 0 → (0 : Rat) ≤ sigmaRneHighSq →
      sigmaSrLowSq / (muBiasHigh * muBiasHigh) < neff p →
      srOutputMse p sigmaSrLowSq < rneOutputMse p muBiasHigh sigmaRneHighSq) ∧
    (∀ (L : Nat) (p : Fin L → Rat) (sigmaSrLowSq muBiasHigh sigmaRneHighSq : Rat),
      finSum p = 1 → (0 : Rat) < ipr p → muBiasHigh ≠ 0 →
      (srOutputMse p sigmaSrLowSq < rneOutputMse p muBiasHigh sigmaRneHighSq ↔
        neffThreshold sigmaSrLowSq sigmaRneHighSq muBiasHigh < neff p)) ∧
    ((396 / 100000000 : Rat) < (100 / 10000000 : Rat) ∧
     (100 / 10000000 : Rat) < (266 / 10000000 : Rat) ∧
     (266 / 10000000 : Rat) < (699 / 10000000 : Rat) ∧
     (6 : Rat) < (266 / 10000000 : Rat) / (396 / 100000000 : Rat) ∧
     (17 : Rat) < (699 / 10000000 : Rat) / (396 / 100000000 : Rat) ∧
     (5 / 2 : Rat) < (266 / 10000000 : Rat) / (100 / 10000000 : Rat) ∧
     (69 / 10 : Rat) < (699 / 10000000 : Rat) / (100 / 10000000 : Rat)) ∧
    ((652 / 10000 : Rat) / (266 / 10000000 : Rat) < 2452 ∧
     (652 / 10000 : Rat) / (699 / 10000000 : Rat) < 933 ∧
     (167 / 1000 : Rat) / (266 / 10000000 : Rat) < 6279 ∧
     (167 / 1000 : Rat) / (699 / 10000000 : Rat) < 2390 ∧
     ∀ (L : Nat) (mu4 muMx : Rat), 16384 ≤ L →
       mu4 * mu4 = 266 / 10000000 → muMx * muMx = 699 / 10000000 →
       srOutputMse (uniformWeights L) (652 / 10000) <
         rneOutputMse (uniformWeights L) mu4 (170 / 100000) ∧
       srOutputMse (uniformWeights L) (652 / 10000) <
         rneOutputMse (uniformWeights L) muMx (116 / 100000) ∧
       srOutputMse (uniformWeights L) (167 / 1000) <
         rneOutputMse (uniformWeights L) mu4 (170 / 100000) ∧
       srOutputMse (uniformWeights L) (167 / 1000) <
         rneOutputMse (uniformWeights L) muMx (116 / 100000)) :=
  VcacheIprXorvdc.cross_format_int2_sr_beats_int4_mxfp4_rne

theorem xor_vdc_stratified_sr_superconvergence_and_iid_halving :
    (∀ (K : Nat) (u0 : Fin (2 ^ K)),
      Function.Injective (xorVdcFin K u0) ∧ Function.Surjective (xorVdcFin K u0)) ∧
    (∀ (K : Nat) (j : Fin (2 ^ K)) (r : Nat), r ≤ 2 ^ K →
      finSumNat (fun u0 : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) = r ∧
      ((finSumNat (fun u0 : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) : Nat) : Rat) /
        ((2 ^ K : Nat) : Rat) = (r : Rat) / ((2 ^ K : Nat) : Rat)) ∧
    (∀ (K : Nat) (u0 : Fin (2 ^ K)) (r : Nat) (f : Rat),
      r < 2 ^ K →
      (r : Rat) / ((2 ^ K : Nat) : Rat) ≤ f →
      f < ((r + 1 : Nat) : Rat) / ((2 ^ K : Nat) : Rat) →
      let sumErr := finSum (fun j : Fin (2 ^ K) => ((srRoundUpBit r (xorVdcFin K u0 j).val : Nat) : Rat) - f)
      let avgErr := sumErr / ((2 ^ K : Nat) : Rat)
      ratAbs sumErr < 1 ∧
      ratAbs avgErr < 1 / ((2 ^ K : Nat) : Rat) ∧
      avgErr * avgErr < 1 / (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat))) ∧
    (∀ (K u0 m : Nat),
      xorVdcNat (K + 1) u0 (2 * m + 1) = xorVdcNat (K + 1) u0 (2 * m) ^^^ 2 ^ K) ∧
    (∀ (u : Rat), condVar u = 1 / 12 ∧ condMean u + condMean (1 - u) = 0) ∧
    (∀ (K : Nat) (u0 : Fin (2 ^ K)),
      finSum (fun j : Fin (2 ^ K) => condMean (xorVdcCenteredThresh K u0 j)) = 0 ∧
      (1 / ((2 ^ K : Nat) : Rat)) * (1 / ((2 ^ K : Nat) : Rat)) *
        finSum (fun j : Fin (2 ^ K) => condVar (xorVdcCenteredThresh K u0 j)) =
        (1 / 12 : Rat) / ((2 ^ K : Nat) : Rat) ∧
      (1 / 6 : Rat) / ((2 ^ K : Nat) : Rat) = 2 * ((1 / 12 : Rat) / ((2 ^ K : Nat) : Rat))) :=
  VcacheIprXorvdc.xor_vdc_stratified_sr_superconvergence_and_iid_halving

theorem rank1_attention_sink_ipr_crossover_exact :
    (∀ (L : Nat) (alpha : Rat), 2 ≤ L → (0 : Rat) ≤ alpha → alpha ≤ 1 →
      (∀ j : Fin L, (0 : Rat) ≤ sinkWeights L alpha j) ∧
      finSum (sinkWeights L alpha) = 1 ∧
      ipr (sinkWeights L alpha) =
        alpha * alpha + (1 - alpha) * (1 - alpha) / ((L - 1 : Nat) : Rat)) ∧
    (∀ (L : Nat) (alpha : Rat), 2 ≤ L → (3 / 4 : Rat) ≤ alpha → alpha ≤ 1 →
      (9 / 16 : Rat) < ipr (sinkWeights L alpha) ∧
      neff (sinkWeights L alpha) < 16 / 9 ∧
      neff (sinkWeights L alpha) < 2) ∧
    (∀ (L : Nat) (alpha : Rat) (e : Fin L → Rat) (hL : 2 ≤ L),
      e ⟨0, by omega⟩ = 0 →
      finSum (fun j : Fin L => sinkWeights L alpha j * e j) =
        (1 - alpha) * finSum (fun k : Fin (L - 1) =>
          uniformWeights (L - 1) k * e ⟨k.val + 1, by omega⟩) ∧
      finSum (uniformWeights (L - 1)) = 1 ∧
      ipr (uniformWeights (L - 1)) = 1 / ((L - 1 : Nat) : Rat) ∧
      neff (uniformWeights (L - 1)) = ((L - 1 : Nat) : Rat)) :=
  VcacheIprXorvdc.rank1_attention_sink_ipr_crossover_exact

theorem rank1_split_wht_orthogonality_and_output_inversion :
    (∀ m : Nat, isScaledOrthogonal (whtMat m)) ∧
    (∀ (L d : Nat) (p : Fin L → Rat) (r : Fin L → Fin d → Rat) (H : Fin d → Fin d → Rat) (i : Fin d),
      attnOut p (fun j => matVecMul H (r j)) i = matVecMul H (attnOut p r) i) ∧
    (∀ (L d : Nat) (p : Fin L → Rat) (r : Fin L → Fin d → Rat) (H : Fin d → Fin d → Rat) (c : Fin d),
      0 < d → isScaledOrthogonal H →
      (1 / (d : Rat)) * matVecMul (matTranspose H) (attnOut p (fun j => matVecMul H (r j))) c =
        attnOut p r c) ∧
    (∀ (L d : Nat) (p : Fin L → Rat) (mu : Fin d → Rat) (r : Fin L → Fin d → Rat)
      (H : Fin d → Fin d → Rat) (c : Fin d),
      0 < d → finSum p = 1 → isScaledOrthogonal H →
      attnOut p (fun j k => mu k + r j k) c =
        mu c + (1 / (d : Rat)) * matVecMul (matTranspose H) (attnOut p (fun j => matVecMul H (r j))) c) ∧
    (∀ (mu r rho K : Rat), (0 : Rat) < rho → (0 : Rat) ≤ K →
      (ratAbs r ≤ rho → ratAbs ((mu + r) - mu) ≤ rho) ∧
      (mu = K * rho → r = rho → ratAbs (mu + r) = (K + 1) * rho ∧ ratAbs r = rho)) :=
  VcacheIprXorvdc.rank1_split_wht_orthogonality_and_output_inversion

theorem sub4bit_vcache_packing_density_and_exact_int64_bounds :
    (vcacheMiB vcacheBytesPerTokenInt16 = 1024 ∧
     vcacheMiB vcacheBytesPerTokenInt4 = 256 ∧
     vcacheMiB vcacheBytesPerTokenInt2 = 128 ∧
     vcacheMiB vcacheBytesPerTokenTernary = 112 ∧
     ((vcacheMiB vcacheBytesPerTokenInt16 : Rat) / (vcacheMiB vcacheBytesPerTokenInt4 : Rat) = 4) ∧
     ((vcacheMiB vcacheBytesPerTokenInt16 : Rat) / (vcacheMiB vcacheBytesPerTokenInt2 : Rat) = 8) ∧
     ((vcacheMiB vcacheBytesPerTokenInt16 : Rat) / (vcacheMiB vcacheBytesPerTokenTernary : Rat) = 64 / 7) ∧
     (914 / 100 : Rat) < (64 / 7 : Rat)) ∧
    ((3 ^ 5 : Nat) = 243 ∧ 243 < 256 ∧ 26 * 5 = 130 ∧ vcacheHeadDim ≤ 26 * 5 ∧
     7 * 4 = vcacheBytesPerTokenTernary ∧
     ∀ t0 t1 t2 t3 t4 : Fin 3,
       pack5Trits t0 t1 t2 t3 t4 < 243 ∧
       unpack5Trits (pack5Trits t0 t1 t2 t3 t4) = (t0, t1, t2, t3, t4)) ∧
    (∀ (L : Nat) (P V : Fin L → Int) (SP Vmax : Int),
      (∀ j, 0 ≤ P j) → finSumInt P = SP →
      (∀ j, -Vmax ≤ V j ∧ V j ≤ Vmax) →
      -(SP * Vmax) ≤ finSumInt (fun j => P j * V j) ∧
      finSumInt (fun j => P j * V j) ≤ SP * Vmax) ∧
    (∀ (L : Nat) (P V : Fin L → Int) (Pmax Vmax : Int),
      (∀ j, -Pmax ≤ P j ∧ P j ≤ Pmax) →
      (∀ j, -Vmax ≤ V j ∧ V j ≤ Vmax) →
      -((L : Int) * (Pmax * Vmax)) ≤ finSumInt (fun j => P j * V j) ∧
      finSumInt (fun j => P j * V j) ≤ (L : Int) * (Pmax * Vmax)) ∧
    (∀ (P V : Fin vcacheCtx128K → Int),
      (∀ j, -(2 ^ 20 : Int) ≤ P j ∧ P j ≤ (2 ^ 20 : Int)) →
      (∀ j, -(7 * (2 ^ 20 : Int)) ≤ V j ∧ V j ≤ 7 * (2 ^ 20 : Int)) →
      int64Min < finSumInt (fun j => P j * V j) ∧
      finSumInt (fun j => P j * V j) < int64Max) ∧
    (((2 ^ 20 : Int) * (2 ^ 15 : Int) < int64Max) ∧
     ((vcacheCtx128K : Int) * ((2 ^ 20 : Int) * (2 ^ 15 : Int)) < int64Max) ∧
     ((vcacheCtx128K : Int) * ((2 ^ 20 : Int) * (7 * (2 ^ 20 : Int))) < int64Max)) :=
  VcacheIprXorvdc.sub4bit_vcache_packing_density_and_exact_int64_bounds

end VcacheIprXorvdcChallenge
