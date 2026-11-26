/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VcacheIprXorvdc.RatHelpers

/-!
# Theorems 1 & 2: Exact Attention-Weight Averaging IPR Law, Phase Transition & Cross-Format Inversion

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `ipr_attention_averaging_sr_vs_rne_exact`:
   - Exact simplex bounds `1 / L ≤ IPR(p) ≤ 1` and `1 ≤ N_eff(p) ≤ L` (with exact uniform `IPR = 1/L, N_eff = L`
     and peaked `IPR = 1, N_eff = 1`).
   - Exact SR output MSE `IPR(p) * σ_SR^2 = σ_SR^2 / N_eff(p)`.
   - Exact RNE output MSE `μ_bias^2 + IPR(p) * σ_RNE^2 = μ_bias^2 + σ_RNE^2 / N_eff(p)`.
   - Exact RNE-vs-SR phase transition threshold `N_eff* = (σ_SR^2 - σ_RNE^2) / μ_bias^2`.
   - Exact `2.000×` RNE advantage at peaked `N_eff = 1` on zero-mean IID uniform quantization (`Δ^2/6 = 2 * (Δ^2/12)`).
2. `cross_format_int2_sr_beats_int4_mxfp4_rne`:
   - General cross-format inversion theorem: whenever `N_eff(p) > σ_SR,low^2 / μ_bias,high^2` (sufficient)
     or sharply `N_eff(p) > (σ_SR,low^2 - σ_RNE,high^2) / μ_bias,high^2`, lower-bit SR strictly beats higher-bit RNE.
   - Exact rational witness inequalities matching the GPU-certified `INT2-SR < Ternary-SR < INT4-RNE < MXFP4-RNE`
     inversion at `L = 16384` and exact crossover thresholds (`L ≥ 2452` for `INT2-SR < INT4-RNE`,
     `L ≥ 933` for `INT2-SR < MXFP4-RNE`).
-/

namespace VcacheIprXorvdc

/-! ### Simplex IPR & Effective Support Bounds -/

theorem simplex_entry_le_one {L : Nat} (p : Fin L → Rat)
    (hnonneg : ∀ j, (0 : Rat) ≤ p j) (hsum : finSum p = 1) (j0 : Fin L) :
    p j0 ≤ 1 := by
  have hle : finSum (fun j : Fin L => if j = j0 then p j0 else 0) ≤ finSum p := by
    apply finSum_le
    intro j
    by_cases h : j = j0
    · subst h; simp
    · simp [h, hnonneg j]
  rw [finSum_single, hsum] at hle
  exact hle

theorem simplex_ipr_bounds {L : Nat} (hL : 0 < L) (p : Fin L → Rat)
    (hnonneg : ∀ j, (0 : Rat) ≤ p j) (hsum : finSum p = 1) :
    1 / (L : Rat) ≤ ipr p ∧ ipr p ≤ 1 ∧ (0 : Rat) < ipr p ∧
    (1 : Rat) ≤ neff p ∧ neff p ≤ (L : Rat) := by
  have hLpos : (0 : Rat) < (L : Rat) := rat_natCast_pos hL
  have hcs := finSum_sq_le_mul_ipr p
  rw [hsum] at hcs
  have h1 : (1 : Rat) ≤ (L : Rat) * ipr p := by grind
  have hlow : 1 / (L : Rat) ≤ ipr p := by
    rw [rat_div_le_iff hLpos]
    grind
  have hpos : (0 : Rat) < ipr p := rat_lt_of_lt_of_le (rat_inv_pos hLpos) hlow
  have hhigh : ipr p ≤ 1 := by
    have hle : ipr p ≤ finSum p := by
      unfold ipr
      apply finSum_le
      intro j
      have hj0 : (0 : Rat) ≤ p j := hnonneg j
      have hj1 : p j ≤ 1 := simplex_entry_le_one p hnonneg hsum j
      have hmul := rat_mul_le_mul_of_nonneg_left hj1 hj0
      grind
    rw [hsum] at hle
    exact hle
  have hneff_low : (1 : Rat) ≤ neff p := by
    unfold neff
    rw [rat_le_div_iff hpos]
    grind
  have hneff_high : neff p ≤ (L : Rat) := by
    unfold neff
    rw [rat_div_le_iff hpos]
    grind
  exact ⟨hlow, hhigh, hpos, hneff_low, hneff_high⟩

theorem uniformWeights_ipr_neff {L : Nat} (hL : 0 < L) :
    finSum (uniformWeights L) = 1 ∧
    ipr (uniformWeights L) = 1 / (L : Rat) ∧
    neff (uniformWeights L) = (L : Rat) := by
  have hLne : (L : Rat) ≠ 0 := rat_natCast_ne_zero hL
  have hsum : finSum (uniformWeights L) = 1 := by
    unfold uniformWeights
    rw [finSum_const]
    grind
  have hipr : ipr (uniformWeights L) = 1 / (L : Rat) := by
    unfold ipr uniformWeights
    rw [finSum_const]
    grind
  have hneff : neff (uniformWeights L) = (L : Rat) := by
    unfold neff
    rw [hipr]
    grind
  exact ⟨hsum, hipr, hneff⟩

theorem peakedWeights_ipr_neff {L : Nat} (j0 : Fin L) :
    finSum (peakedWeights L j0) = 1 ∧
    ipr (peakedWeights L j0) = 1 ∧
    neff (peakedWeights L j0) = 1 := by
  have hsum : finSum (peakedWeights L j0) = 1 := by
    unfold peakedWeights
    exact finSum_single j0 1
  have hipr : ipr (peakedWeights L j0) = 1 := by
    unfold ipr peakedWeights
    have hc : finSum (fun j : Fin L => (if j = j0 then (1 : Rat) else 0) *
        (if j = j0 then (1 : Rat) else 0)) =
        finSum (fun j : Fin L => if j = j0 then (1 : Rat) else 0) := by
      apply finSum_congr
      intro j
      by_cases h : j = j0 <;> simp [h]
    rw [hc, finSum_single]
  have hneff : neff (peakedWeights L j0) = 1 := by
    unfold neff
    rw [hipr]
    grind
  exact ⟨hsum, hipr, hneff⟩

/-! ### Exact SR & RNE Output MSE Forms and Phase Transition -/

theorem srOutputMse_eq {L : Nat} (p : Fin L → Rat) (sigmaSrSq : Rat) :
    srOutputMse p sigmaSrSq = ipr p * sigmaSrSq := by
  unfold srOutputMse ipr
  exact finSum_mul_right (fun j => p j * p j) sigmaSrSq

theorem srOutputMse_div_neff {L : Nat} (p : Fin L → Rat) (sigmaSrSq : Rat)
    (hipr : (0 : Rat) < ipr p) :
    srOutputMse p sigmaSrSq = sigmaSrSq / neff p := by
  rw [srOutputMse_eq]
  unfold neff
  have hne : ipr p ≠ 0 := Rat.ne_of_gt hipr
  grind

theorem rneOutputMse_simplex_eq {L : Nat} (p : Fin L → Rat) (muBias sigmaRneSq : Rat)
    (hsum : finSum p = 1) :
    rneOutputMse p muBias sigmaRneSq = muBias * muBias + ipr p * sigmaRneSq := by
  unfold rneOutputMse ipr
  rw [finSum_mul_right p muBias, hsum, finSum_mul_right (fun j => p j * p j) sigmaRneSq]
  grind

theorem rneOutputMse_div_neff {L : Nat} (p : Fin L → Rat) (muBias sigmaRneSq : Rat)
    (hsum : finSum p = 1) (hipr : (0 : Rat) < ipr p) :
    rneOutputMse p muBias sigmaRneSq = muBias * muBias + sigmaRneSq / neff p := by
  rw [rneOutputMse_simplex_eq p muBias sigmaRneSq hsum]
  unfold neff
  have hne : ipr p ≠ 0 := Rat.ne_of_gt hipr
  grind

theorem sr_lt_rne_iff {L : Nat} (p : Fin L → Rat) (sigmaSrSq sigmaRneSq muBias : Rat)
    (hsum : finSum p = 1) (hipr : (0 : Rat) < ipr p) (hmu : muBias ≠ 0) :
    srOutputMse p sigmaSrSq < rneOutputMse p muBias sigmaRneSq ↔
    neffThreshold sigmaSrSq sigmaRneSq muBias < neff p := by
  rw [srOutputMse_eq, rneOutputMse_simplex_eq p muBias sigmaRneSq hsum]
  unfold neffThreshold neff
  have hmu2 : (0 : Rat) < muBias * muBias := rat_sq_pos hmu
  have hne_ipr : ipr p ≠ 0 := Rat.ne_of_gt hipr
  have hne_mu2 : muBias * muBias ≠ 0 := Rat.ne_of_gt hmu2
  constructor
  · intro h
    have h1 : ipr p * (sigmaSrSq - sigmaRneSq) < muBias * muBias := by
      have hs := rat_sub_pos h
      apply rat_lt_of_sub_pos
      have eq : muBias * muBias - ipr p * (sigmaSrSq - sigmaRneSq) =
          muBias * muBias + ipr p * sigmaRneSq - ipr p * sigmaSrSq := by grind
      rw [eq]; exact hs
    rw [rat_div_lt_iff hmu2]
    have h2 := rat_mul_lt_mul_of_pos_left h1 (rat_inv_pos hipr)
    have eq1 : 1 / ipr p * (ipr p * (sigmaSrSq - sigmaRneSq)) = sigmaSrSq - sigmaRneSq := by grind
    have eq2 : 1 / ipr p * (muBias * muBias) = (1 / ipr p) * (muBias * muBias) := rfl
    rw [eq1, eq2] at h2
    exact h2
  · intro h
    rw [rat_div_lt_iff hmu2] at h
    have h1 := rat_mul_lt_mul_of_pos_left h hipr
    have eq1 : ipr p * (1 / ipr p * (muBias * muBias)) = muBias * muBias := by grind
    rw [eq1] at h1
    apply rat_lt_of_sub_pos
    have hs := rat_sub_pos h1
    have eq2 : muBias * muBias + ipr p * sigmaRneSq - ipr p * sigmaSrSq =
        muBias * muBias - ipr p * (sigmaSrSq - sigmaRneSq) := by grind
    rw [eq2]; exact hs

theorem sr_eq_rne_iff {L : Nat} (p : Fin L → Rat) (sigmaSrSq sigmaRneSq muBias : Rat)
    (hsum : finSum p = 1) (hipr : (0 : Rat) < ipr p) (hmu : muBias ≠ 0) :
    srOutputMse p sigmaSrSq = rneOutputMse p muBias sigmaRneSq ↔
    neff p = neffThreshold sigmaSrSq sigmaRneSq muBias := by
  rw [srOutputMse_eq, rneOutputMse_simplex_eq p muBias sigmaRneSq hsum]
  unfold neffThreshold neff
  have hne_ipr : ipr p ≠ 0 := Rat.ne_of_gt hipr
  have hne_mu2 : muBias * muBias ≠ 0 := Rat.ne_of_gt (rat_sq_pos hmu)
  constructor <;> intro h <;> grind

theorem rne_lt_sr_iff {L : Nat} (p : Fin L → Rat) (sigmaSrSq sigmaRneSq muBias : Rat)
    (hsum : finSum p = 1) (hipr : (0 : Rat) < ipr p) (hmu : muBias ≠ 0) :
    rneOutputMse p muBias sigmaRneSq < srOutputMse p sigmaSrSq ↔
    neff p < neffThreshold sigmaSrSq sigmaRneSq muBias := by
  rw [srOutputMse_eq, rneOutputMse_simplex_eq p muBias sigmaRneSq hsum]
  unfold neffThreshold neff
  have hmu2 : (0 : Rat) < muBias * muBias := rat_sq_pos hmu
  have hne_ipr : ipr p ≠ 0 := Rat.ne_of_gt hipr
  constructor
  · intro h
    have h1 : muBias * muBias < ipr p * (sigmaSrSq - sigmaRneSq) := by
      have hs := rat_sub_pos h
      apply rat_lt_of_sub_pos
      have eq : ipr p * (sigmaSrSq - sigmaRneSq) - muBias * muBias =
          ipr p * sigmaSrSq - (muBias * muBias + ipr p * sigmaRneSq) := by grind
      rw [eq]; exact hs
    rw [rat_lt_div_iff hmu2]
    have h2 := rat_mul_lt_mul_of_pos_left h1 (rat_inv_pos hipr)
    have eq1 : 1 / ipr p * (ipr p * (sigmaSrSq - sigmaRneSq)) = sigmaSrSq - sigmaRneSq := by grind
    rw [eq1] at h2
    exact h2
  · intro h
    rw [rat_lt_div_iff hmu2] at h
    have h1 := rat_mul_lt_mul_of_pos_left h hipr
    have eq1 : ipr p * (1 / ipr p * (muBias * muBias)) = muBias * muBias := by grind
    rw [eq1] at h1
    apply rat_lt_of_sub_pos
    have hs := rat_sub_pos h1
    have eq2 : ipr p * sigmaSrSq - (muBias * muBias + ipr p * sigmaRneSq) =
        ipr p * (sigmaSrSq - sigmaRneSq) - muBias * muBias := by grind
    rw [eq2]; exact hs

/-! ### Headline Theorem 1 (`ipr_attention_averaging_sr_vs_rne_exact`) -/

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
        2 * rneOutputMse (peakedWeights L j0) 0 (rneUniformVar delta)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L p hL hnn hsum
    exact simplex_ipr_bounds hL p hnn hsum
  · intro L hL
    exact uniformWeights_ipr_neff hL
  · intro L j0
    exact peakedWeights_ipr_neff j0
  · intro L p sSr sRne mu hsum hipr
    exact ⟨srOutputMse_eq p sSr,
           srOutputMse_div_neff p sSr hipr,
           rneOutputMse_simplex_eq p mu sRne hsum,
           rneOutputMse_div_neff p mu sRne hsum hipr⟩
  · intro L p sSr sRne mu hsum hipr hmu
    exact ⟨sr_lt_rne_iff p sSr sRne mu hsum hipr hmu,
           sr_eq_rne_iff p sSr sRne mu hsum hipr hmu,
           rne_lt_sr_iff p sSr sRne mu hsum hipr hmu⟩
  · intro L j0 delta hdelta
    have hpk := peakedWeights_ipr_neff j0
    have h1 : srUniformVar delta / rneUniformVar delta = 2 := by
      unfold srUniformVar rneUniformVar
      have hd2 : delta * delta ≠ 0 := Rat.ne_of_gt (rat_sq_pos hdelta)
      grind
    have h2 : srOutputMse (peakedWeights L j0) (srUniformVar delta) =
        2 * rneOutputMse (peakedWeights L j0) 0 (rneUniformVar delta) := by
      rw [srOutputMse_eq, rneOutputMse_simplex_eq _ 0 _ hpk.1, hpk.2.1]
      unfold srUniformVar rneUniformVar
      grind
    exact ⟨h1, h2⟩

/-! ### Headline Theorem 2 (`cross_format_int2_sr_beats_int4_mxfp4_rne`) -/

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
         rneOutputMse (uniformWeights L) muMx (116 / 100000)) := by
  have hSuff : ∀ (L : Nat) (p : Fin L → Rat) (sigmaSrLowSq muBiasHigh sigmaRneHighSq : Rat),
      finSum p = 1 → (0 : Rat) < ipr p → muBiasHigh ≠ 0 → (0 : Rat) ≤ sigmaRneHighSq →
      sigmaSrLowSq / (muBiasHigh * muBiasHigh) < neff p →
      srOutputMse p sigmaSrLowSq < rneOutputMse p muBiasHigh sigmaRneHighSq := by
    intro L p sLow muH sHigh hsum hipr hmu hsHigh hneff
    rw [sr_lt_rne_iff p sLow sHigh muH hsum hipr hmu]
    unfold neffThreshold
    have hmu2 : (0 : Rat) < muH * muH := rat_sq_pos hmu
    have hle : (sLow - sHigh) / (muH * muH) ≤ sLow / (muH * muH) := by
      rw [rat_div_le_iff hmu2]
      have hne : muH * muH ≠ 0 := Rat.ne_of_gt hmu2
      have eq : sLow / (muH * muH) * (muH * muH) = sLow := by grind
      rw [eq]
      apply rat_le_of_sub_nonneg
      have eq2 : sLow - (sLow - sHigh) = sHigh := by grind
      rw [eq2]; exact hsHigh
    exact rat_lt_of_le_of_lt hle hneff
  refine ⟨hSuff, ?_, ?_, ?_⟩
  · intro L p sLow muH sHigh hsum hipr hmu
    exact sr_lt_rne_iff p sLow sHigh muH hsum hipr hmu
  · refine ⟨by grind, by grind, by grind, by grind, by grind, by grind, by grind⟩
  · refine ⟨by grind, by grind, by grind, by grind, ?_⟩
    intro L mu4 muMx hL hmu4 hmuMx
    have hLpos : 0 < L := by omega
    have hu := uniformWeights_ipr_neff hLpos
    have hipr_pos : (0 : Rat) < ipr (uniformWeights L) := by
      rw [hu.2.1]; exact rat_inv_pos (rat_natCast_pos hLpos)
    have hmu4_ne : mu4 ≠ 0 := by
      intro h0; rw [h0] at hmu4; grind
    have hmuMx_ne : muMx ≠ 0 := by
      intro h0; rw [h0] at hmuMx; grind
    have hLrat : (16384 : Rat) ≤ (L : Rat) := rat_natCast_le hL
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply hSuff L (uniformWeights L) (652 / 10000) mu4 (170 / 100000) hu.1 hipr_pos hmu4_ne (by grind)
      rw [hu.2.2, hmu4]
      exact rat_lt_of_lt_of_le (by grind) hLrat
    · apply hSuff L (uniformWeights L) (652 / 10000) muMx (116 / 100000) hu.1 hipr_pos hmuMx_ne (by grind)
      rw [hu.2.2, hmuMx]
      exact rat_lt_of_lt_of_le (by grind) hLrat
    · apply hSuff L (uniformWeights L) (167 / 1000) mu4 (170 / 100000) hu.1 hipr_pos hmu4_ne (by grind)
      rw [hu.2.2, hmu4]
      exact rat_lt_of_lt_of_le (by grind) hLrat
    · apply hSuff L (uniformWeights L) (167 / 1000) muMx (116 / 100000) hu.1 hipr_pos hmuMx_ne (by grind)
      rw [hu.2.2, hmuMx]
      exact rat_lt_of_lt_of_le (by grind) hLrat

end VcacheIprXorvdc
