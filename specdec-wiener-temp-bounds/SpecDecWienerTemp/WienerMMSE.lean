/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecWienerTemp.RatOrder

/-!
# Wiener-MMSE Temperature Optimality & Strict Dominance over Variance Matching

Proves Theorems 1 and 2 of `SpecDecWienerTempChallenge`:
1. `wiener_mmse_temperature_uniquely_minimizes_logit_mse`
2. `wiener_mmse_strictly_beats_variance_matching_and_uncalibrated`
-/

namespace SpecDecWienerTemp

/-! ### Theorem 1: Completed-Square SOS Optimality of `T_MMSE^*` -/

theorem wienerTemp_gt_one {sz2 sq2 : Rat} (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) :
    (1 : Rat) < wienerTemp sz2 sq2 := by
  unfold wienerTemp
  have hpos : (0 : Rat) < sq2 / sz2 := rat_div_pos hsq hsz
  apply rat_lt_of_sub_pos
  have heq : 1 + sq2 / sz2 - 1 = sq2 / sz2 := by grind
  rw [heq]; exact hpos

theorem wienerTemp_pos {sz2 sq2 : Rat} (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) :
    (0 : Rat) < wienerTemp sz2 sq2 :=
  rat_lt_trans (by decide : (0 : Rat) < 1) (wienerTemp_gt_one hsz hsq)

theorem wienerTemp_eq_div {sz2 sq2 : Rat} (hsz : (0 : Rat) < sz2) :
    wienerTemp sz2 sq2 = (sz2 + sq2) / sz2 := by
  unfold wienerTemp
  symm
  rw [rat_div_eq_iff (Rat.ne_of_gt hsz)]
  have hmul : (1 + sq2 / sz2) * sz2 = sz2 + (sq2 / sz2) * sz2 := by grind
  rw [hmul, rat_div_mul_cancel (Rat.ne_of_gt hsz)]

theorem inv_wienerTemp_eq {sz2 sq2 : Rat} (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) :
    (1 : Rat) / wienerTemp sz2 sq2 = sz2 / (sz2 + sq2) := by
  have hsum : (0 : Rat) < sz2 + sq2 := rat_add_pos hsz hsq
  have hTpos : (0 : Rat) < wienerTemp sz2 sq2 := wienerTemp_pos hsz hsq
  have hT_eq : wienerTemp sz2 sq2 = (sz2 + sq2) / sz2 := wienerTemp_eq_div hsz
  rw [rat_div_eq_iff (Rat.ne_of_gt hTpos), hT_eq]
  have h1 : sz2 + sq2 ≠ 0 := Rat.ne_of_gt hsum
  have h2 : sz2 ≠ 0 := Rat.ne_of_gt hsz
  have hprod : (sz2 / (sz2 + sq2)) * ((sz2 + sq2) / sz2) = 1 := by
    rw [Rat.div_def, Rat.div_def]
    calc sz2 * (sz2 + sq2)⁻¹ * ((sz2 + sq2) * sz2⁻¹)
        = sz2 * ((sz2 + sq2)⁻¹ * (sz2 + sq2)) * sz2⁻¹ := by grind
      _ = sz2 * 1 * sz2⁻¹ := by rw [Rat.inv_mul_cancel (sz2 + sq2) h1]
      _ = sz2 * sz2⁻¹ := by grind
      _ = 1 := Rat.mul_inv_cancel sz2 h2
  exact hprod.symm

theorem logitMSE_sos_decomp {sz2 sq2 T : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) (hT : T ≠ 0) :
    logitMSE sz2 sq2 T - wienerOptMSE sz2 sq2 =
      (sz2 + sq2) * (1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2)) := by
  have hsum : (0 : Rat) < sz2 + sq2 := rat_add_pos hsz hsq
  have hsum_ne : sz2 + sq2 ≠ 0 := Rat.ne_of_gt hsum
  have hT2_ne : T * T ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero hT)
  have hden : (T * T) * (sz2 + sq2) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hT2_ne h
    | inr h => exact hsum_ne h
  apply rat_eq_of_mul_eq_mul_right hden
  unfold logitMSE wienerOptMSE
  have hTinv : (1 / T) * T = 1 := rat_div_mul_cancel hT
  have hsqT : (sq2 / (T * T)) * (T * T) = sq2 := rat_div_mul_cancel hT2_ne
  have hopt : ((sz2 * sq2) / (sz2 + sq2)) * (sz2 + sq2) = sz2 * sq2 := rat_div_mul_cancel hsum_ne
  have hs1 : (sz2 / (sz2 + sq2)) * (sz2 + sq2) = sz2 := rat_div_mul_cancel hsum_ne
  -- Simplify LHS * (T*T)*(sz2+sq2)
  have hLHS :
      (((1 - 1 / T) * (1 - 1 / T) * sz2 + sq2 / (T * T)) - (sz2 * sq2) / (sz2 + sq2)) *
        ((T * T) * (sz2 + sq2)) =
      ((T - 1) * (T - 1) * sz2 + sq2) * (sz2 + sq2) - (T * T) * (sz2 * sq2) := by
    have ha : (1 - 1 / T) * T = T - 1 := by
      have : (1 - 1 / T) * T = T - (1 / T) * T := by grind
      rw [this, hTinv]
    have hb : (1 - 1 / T) * (1 - 1 / T) * (T * T) = (T - 1) * (T - 1) := by
      calc (1 - 1 / T) * (1 - 1 / T) * (T * T)
          = ((1 - 1 / T) * T) * ((1 - 1 / T) * T) := by grind
        _ = (T - 1) * (T - 1) := by rw [ha]
    calc (((1 - 1 / T) * (1 - 1 / T) * sz2 + sq2 / (T * T)) - (sz2 * sq2) / (sz2 + sq2)) *
          ((T * T) * (sz2 + sq2))
        = ((1 - 1 / T) * (1 - 1 / T) * (T * T) * sz2 + (sq2 / (T * T)) * (T * T)) * (sz2 + sq2) -
          (T * T) * (((sz2 * sq2) / (sz2 + sq2)) * (sz2 + sq2)) := by grind
      _ = ((T - 1) * (T - 1) * sz2 + sq2) * (sz2 + sq2) - (T * T) * (sz2 * sq2) := by
          rw [hb, hsqT, hopt]
  -- Simplify RHS * (T*T)*(sz2+sq2)
  have hRHS :
      ((sz2 + sq2) * (1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2))) *
        ((T * T) * (sz2 + sq2)) =
      ((sz2 + sq2) - T * sz2) * ((sz2 + sq2) - T * sz2) := by
    have hc : (1 / T - sz2 / (sz2 + sq2)) * (T * (sz2 + sq2)) = (sz2 + sq2) - T * sz2 := by
      calc (1 / T - sz2 / (sz2 + sq2)) * (T * (sz2 + sq2))
          = ((1 / T) * T) * (sz2 + sq2) - T * ((sz2 / (sz2 + sq2)) * (sz2 + sq2)) := by grind
        _ = 1 * (sz2 + sq2) - T * sz2 := by rw [hTinv, hs1]
        _ = (sz2 + sq2) - T * sz2 := by grind
    calc ((sz2 + sq2) * (1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2))) *
          ((T * T) * (sz2 + sq2))
        = ((1 / T - sz2 / (sz2 + sq2)) * (T * (sz2 + sq2))) *
          ((1 / T - sz2 / (sz2 + sq2)) * (T * (sz2 + sq2))) := by grind
      _ = ((sz2 + sq2) - T * sz2) * ((sz2 + sq2) - T * sz2) := by rw [hc]
  rw [hLHS, hRHS]
  grind

theorem logitMSE_at_wienerTemp {sz2 sq2 : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) :
    logitMSE sz2 sq2 (wienerTemp sz2 sq2) = wienerOptMSE sz2 sq2 := by
  have hTne : wienerTemp sz2 sq2 ≠ 0 := Rat.ne_of_gt (wienerTemp_pos hsz hsq)
  have hdecomp := logitMSE_sos_decomp hsz hsq hTne
  rw [inv_wienerTemp_eq hsz hsq] at hdecomp
  grind

theorem logitMSE_ge_wienerOptMSE {sz2 sq2 T : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) (hT : T ≠ 0) :
    wienerOptMSE sz2 sq2 ≤ logitMSE sz2 sq2 T := by
  apply rat_le_of_sub_nonneg
  rw [logitMSE_sos_decomp hsz hsq hT]
  have hsum : (0 : Rat) ≤ sz2 + sq2 := Rat.le_of_lt (rat_add_pos hsz hsq)
  have hsq_nn : (0 : Rat) ≤ (1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2)) :=
    rat_sq_nonneg _
  have hmul : (0 : Rat) ≤ (sz2 + sq2) * ((1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2))) :=
    Rat.mul_nonneg hsum hsq_nn
  grind

theorem logitMSE_gt_wienerOptMSE_of_ne {sz2 sq2 T : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) (hT : T ≠ 0)
    (hne : T ≠ wienerTemp sz2 sq2) :
    wienerOptMSE sz2 sq2 < logitMSE sz2 sq2 T := by
  apply rat_lt_of_sub_pos
  rw [logitMSE_sos_decomp hsz hsq hT]
  have hsum : (0 : Rat) < sz2 + sq2 := rat_add_pos hsz hsq
  have hdiff_ne : 1 / T - sz2 / (sz2 + sq2) ≠ 0 := by
    intro h0
    have heq : 1 / T = sz2 / (sz2 + sq2) := by grind
    rw [← inv_wienerTemp_eq hsz hsq] at heq
    have hTstar_ne : wienerTemp sz2 sq2 ≠ 0 := Rat.ne_of_gt (wienerTemp_pos hsz hsq)
    have h1 : (1 / T) * (T * wienerTemp sz2 sq2) = (1 / wienerTemp sz2 sq2) * (T * wienerTemp sz2 sq2) := by
      rw [heq]
    have hL : (1 / T) * (T * wienerTemp sz2 sq2) = wienerTemp sz2 sq2 := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel hT, Rat.one_mul]
    have hR : (1 / wienerTemp sz2 sq2) * (T * wienerTemp sz2 sq2) = T := by
      rw [Rat.mul_comm T _, ← Rat.mul_assoc, rat_div_mul_cancel hTstar_ne, Rat.one_mul]
    rw [hL, hR] at h1
    exact hne h1.symm
  have hsq_pos : (0 : Rat) < (1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2)) :=
    rat_sq_pos_of_ne_zero hdiff_ne
  have hmul : (0 : Rat) < (sz2 + sq2) * ((1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2))) :=
    rat_mul_pos hsum hsq_pos
  grind

theorem logitMSE_eq_opt_iff {sz2 sq2 T : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) (hT : T ≠ 0) :
    logitMSE sz2 sq2 T = wienerOptMSE sz2 sq2 ↔ T = wienerTemp sz2 sq2 := by
  constructor
  · intro heq
    by_cases h : T = wienerTemp sz2 sq2
    · exact h
    · have hgt := logitMSE_gt_wienerOptMSE_of_ne hsz hsq hT h
      rw [heq] at hgt
      exact False.elim (Rat.lt_irrefl hgt)
  · intro h
    rw [h]
    exact logitMSE_at_wienerTemp hsz hsq

theorem generalProjMSE_sos_decomp {sz2 szt2 cov beta : Rat} (hszt : (0 : Rat) < szt2) :
    generalProjMSE sz2 szt2 cov beta - wienerProjOptMSE sz2 szt2 cov =
      szt2 * (beta - wienerProjGain szt2 cov) * (beta - wienerProjGain szt2 cov) := by
  have hne : szt2 ≠ 0 := Rat.ne_of_gt hszt
  apply rat_eq_of_mul_eq_mul_right hne
  unfold generalProjMSE wienerProjOptMSE wienerProjGain
  have h1 : (cov / szt2) * szt2 = cov := rat_div_mul_cancel hne
  have h2 : ((cov * cov) / szt2) * szt2 = cov * cov := rat_div_mul_cancel hne
  have hLHS :
      ((beta * beta * szt2 - 2 * beta * cov + sz2) - (sz2 - (cov * cov) / szt2)) * szt2 =
      beta * beta * szt2 * szt2 - 2 * beta * cov * szt2 + cov * cov := by
    calc ((beta * beta * szt2 - 2 * beta * cov + sz2) - (sz2 - (cov * cov) / szt2)) * szt2
        = (beta * beta * szt2 - 2 * beta * cov) * szt2 + ((cov * cov) / szt2) * szt2 := by grind
      _ = beta * beta * szt2 * szt2 - 2 * beta * cov * szt2 + cov * cov := by rw [h2]; grind
  have hRHS :
      (szt2 * (beta - cov / szt2) * (beta - cov / szt2)) * szt2 =
      (beta * szt2 - cov) * (beta * szt2 - cov) := by
    have hc : (beta - cov / szt2) * szt2 = beta * szt2 - cov := by
      calc (beta - cov / szt2) * szt2
          = beta * szt2 - (cov / szt2) * szt2 := by grind
        _ = beta * szt2 - cov := by rw [h1]
    calc (szt2 * (beta - cov / szt2) * (beta - cov / szt2)) * szt2
        = ((beta - cov / szt2) * szt2) * ((beta - cov / szt2) * szt2) := by grind
      _ = (beta * szt2 - cov) * (beta * szt2 - cov) := by rw [hc]
  rw [hLHS, hRHS]
  grind

/-- Headline Theorem 1 (`wiener_mmse_temperature_uniquely_minimizes_logit_mse`). -/
theorem wiener_mmse_temperature_uniquely_minimizes_logit_mse :
    (∀ sz2 sq2 T : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 → T ≠ 0 →
      logitMSE sz2 sq2 T - wienerOptMSE sz2 sq2 =
        (sz2 + sq2) * (1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2))) ∧
    (∀ sz2 sq2 : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 →
      (1 : Rat) < wienerTemp sz2 sq2 ∧
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) = wienerOptMSE sz2 sq2) ∧
    (∀ sz2 sq2 T : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 → T ≠ 0 →
      wienerOptMSE sz2 sq2 ≤ logitMSE sz2 sq2 T ∧
      (logitMSE sz2 sq2 T = wienerOptMSE sz2 sq2 ↔ T = wienerTemp sz2 sq2) ∧
      (T ≠ wienerTemp sz2 sq2 → wienerOptMSE sz2 sq2 < logitMSE sz2 sq2 T)) ∧
    (∀ sz2 szt2 cov beta : Rat, (0 : Rat) < szt2 →
      generalProjMSE sz2 szt2 cov beta - wienerProjOptMSE sz2 szt2 cov =
        szt2 * (beta - wienerProjGain szt2 cov) * (beta - wienerProjGain szt2 cov) ∧
      wienerProjOptMSE sz2 szt2 cov ≤ generalProjMSE sz2 szt2 cov beta) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sz2 sq2 T hsz hsq hT
    exact logitMSE_sos_decomp hsz hsq hT
  · intro sz2 sq2 hsz hsq
    exact ⟨wienerTemp_gt_one hsz hsq, logitMSE_at_wienerTemp hsz hsq⟩
  · intro sz2 sq2 T hsz hsq hT
    exact ⟨logitMSE_ge_wienerOptMSE hsz hsq hT,
           logitMSE_eq_opt_iff hsz hsq hT,
           logitMSE_gt_wienerOptMSE_of_ne hsz hsq hT⟩
  · intro sz2 szt2 cov beta hszt
    have hdecomp := generalProjMSE_sos_decomp (sz2 := sz2) (cov := cov) (beta := beta) hszt
    refine ⟨hdecomp, ?_⟩
    apply rat_le_of_sub_nonneg
    rw [hdecomp]
    have hnn := Rat.mul_nonneg (Rat.le_of_lt hszt) (rat_sq_nonneg (beta - wienerProjGain szt2 cov))
    grind

/-! ### Theorem 2: Strict Dominance over Uncalibrated `T = 1` and Variance-Matching `T_var` -/

theorem logitMSE_at_one (sz2 sq2 : Rat) : logitMSE sz2 sq2 1 = sq2 := by
  unfold logitMSE
  have h1 : (1 : Rat) / 1 = 1 := by grind
  have h2 : (1 : Rat) * 1 = 1 := by grind
  rw [h1, h2]
  have h3 : sq2 / 1 = sq2 := by
    rw [rat_div_eq_iff (by decide : (1 : Rat) ≠ 0)]
    grind
  rw [h3]
  grind

theorem logitMSE_saving_over_one {sz2 sq2 : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2) :
    logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2) =
      (sq2 * sq2) / (sz2 + sq2) ∧
    (0 : Rat) < (sq2 * sq2) / (sz2 + sq2) ∧
    logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 1 := by
  have hsum : (0 : Rat) < sz2 + sq2 := rat_add_pos hsz hsq
  have hsum_ne : sz2 + sq2 ≠ 0 := Rat.ne_of_gt hsum
  rw [logitMSE_at_one, logitMSE_at_wienerTemp hsz hsq]
  have hdiff : sq2 - wienerOptMSE sz2 sq2 = (sq2 * sq2) / (sz2 + sq2) := by
    apply rat_eq_of_mul_eq_mul_right hsum_ne
    unfold wienerOptMSE
    have h1 : ((sz2 * sq2) / (sz2 + sq2)) * (sz2 + sq2) = sz2 * sq2 := rat_div_mul_cancel hsum_ne
    have h2 : ((sq2 * sq2) / (sz2 + sq2)) * (sz2 + sq2) = sq2 * sq2 := rat_div_mul_cancel hsum_ne
    calc (sq2 - (sz2 * sq2) / (sz2 + sq2)) * (sz2 + sq2)
        = sq2 * (sz2 + sq2) - ((sz2 * sq2) / (sz2 + sq2)) * (sz2 + sq2) := by grind
      _ = sq2 * (sz2 + sq2) - sz2 * sq2 := by rw [h1]
      _ = sq2 * sq2 := by grind
      _ = ((sq2 * sq2) / (sz2 + sq2)) * (sz2 + sq2) := h2.symm
  have hpos : (0 : Rat) < (sq2 * sq2) / (sz2 + sq2) :=
    rat_div_pos (rat_mul_pos hsq hsq) hsum
  refine ⟨hdiff, hpos, ?_⟩
  apply rat_lt_of_sub_pos
  rw [hdiff]
  exact hpos

theorem tvar_bounds {sz2 sq2 Tvar : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2)
    (hTpos : (0 : Rat) < Tvar) (hTsq : Tvar * Tvar = wienerTemp sz2 sq2) :
    (1 : Rat) < Tvar ∧ Tvar < wienerTemp sz2 sq2 := by
  have hgt1 : (1 : Rat) < Tvar * Tvar := by
    rw [hTsq]; exact wienerTemp_gt_one hsz hsq
  have hTgt1 : (1 : Rat) < Tvar := by
    cases Rat.le_total (a := Tvar) (b := 1) with
    | inr hge =>
      by_cases heq : Tvar = 1
      · rw [heq] at hgt1
        have : (1 : Rat) * 1 = 1 := by grind
        rw [this] at hgt1
        exact False.elim (Rat.lt_irrefl hgt1)
      · exact Rat.lt_of_le_of_ne hge (Ne.symm heq)
    | inl hle =>
      have hsq_le : Tvar * Tvar ≤ 1 := by
        have ha : Tvar * Tvar ≤ 1 * Tvar := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hTpos)
        have hb : 1 * Tvar ≤ 1 * 1 := rat_mul_le_mul_of_nonneg_left hle (by decide)
        have h11 : (1 : Rat) * 1 = 1 := by grind
        rw [h11] at hb
        exact Rat.le_trans ha hb
      exact False.elim (Rat.not_le.mpr hgt1 hsq_le)
  have hTlt : Tvar < wienerTemp sz2 sq2 := by
    rw [← hTsq]
    have hmul := rat_mul_lt_mul_of_pos_left hTgt1 hTpos
    rw [Rat.mul_one] at hmul
    exact hmul
  exact ⟨hTgt1, hTlt⟩

theorem logitMSE_at_tvar {sz2 sq2 Tvar : Rat}
    (hsz : (0 : Rat) < sz2) (hTpos : (0 : Rat) < Tvar)
    (hTsq : Tvar * Tvar = wienerTemp sz2 sq2) :
    logitMSE sz2 sq2 Tvar = 2 * sz2 * (1 - 1 / Tvar) := by
  have hTne : Tvar ≠ 0 := Rat.ne_of_gt hTpos
  have hT2ne : Tvar * Tvar ≠ 0 := Rat.ne_of_gt (rat_mul_pos hTpos hTpos)
  have hsq2 : sq2 = sz2 * (Tvar * Tvar - 1) := by
    unfold wienerTemp at hTsq
    have hdiv : sq2 / sz2 = Tvar * Tvar - 1 := by grind
    have hmul := (rat_div_eq_iff (Rat.ne_of_gt hsz)).mp hdiv
    grind
  apply rat_eq_of_mul_eq_mul_right hT2ne
  unfold logitMSE
  have hTinv : (1 / Tvar) * Tvar = 1 := rat_div_mul_cancel hTne
  have hsqdiv : (sq2 / (Tvar * Tvar)) * (Tvar * Tvar) = sq2 := rat_div_mul_cancel hT2ne
  have ha : (1 - 1 / Tvar) * Tvar = Tvar - 1 := by
    have : (1 - 1 / Tvar) * Tvar = Tvar - (1 / Tvar) * Tvar := by grind
    rw [this, hTinv]
  have hb : (1 - 1 / Tvar) * (1 - 1 / Tvar) * (Tvar * Tvar) = (Tvar - 1) * (Tvar - 1) := by
    calc (1 - 1 / Tvar) * (1 - 1 / Tvar) * (Tvar * Tvar)
        = ((1 - 1 / Tvar) * Tvar) * ((1 - 1 / Tvar) * Tvar) := by grind
      _ = (Tvar - 1) * (Tvar - 1) := by rw [ha]
  calc ((1 - 1 / Tvar) * (1 - 1 / Tvar) * sz2 + sq2 / (Tvar * Tvar)) * (Tvar * Tvar)
      = (1 - 1 / Tvar) * (1 - 1 / Tvar) * (Tvar * Tvar) * sz2 +
        (sq2 / (Tvar * Tvar)) * (Tvar * Tvar) := by grind
    _ = (Tvar - 1) * (Tvar - 1) * sz2 + sq2 := by rw [hb, hsqdiv]
    _ = (Tvar - 1) * (Tvar - 1) * sz2 + sz2 * (Tvar * Tvar - 1) := by rw [hsq2]
    _ = 2 * sz2 * ((Tvar - 1) * Tvar) := by grind
    _ = 2 * sz2 * (((1 - 1 / Tvar) * Tvar) * Tvar) := by rw [ha]
    _ = (2 * sz2 * (1 - 1 / Tvar)) * (Tvar * Tvar) := by grind

theorem tvar_gap_and_recovery {sz2 sq2 Tvar : Rat}
    (hsz : (0 : Rat) < sz2) (hsq : (0 : Rat) < sq2)
    (hTpos : (0 : Rat) < Tvar) (hTsq : Tvar * Tvar = wienerTemp sz2 sq2) :
    logitMSE sz2 sq2 Tvar - logitMSE sz2 sq2 (wienerTemp sz2 sq2) =
      sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar) ∧
    (0 : Rat) < sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar) ∧
    logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 Tvar ∧
    logitMSE sz2 sq2 Tvar < logitMSE sz2 sq2 1 ∧
    (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 Tvar) /
      (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2)) =
      1 - 1 / ((Tvar + 1) * (Tvar + 1)) ∧
    (3 / 4 : Rat) < 1 - 1 / ((Tvar + 1) * (Tvar + 1)) ∧
    1 - 1 / ((Tvar + 1) * (Tvar + 1)) < 1 := by
  have ⟨hTgt1, _⟩ := tvar_bounds hsz hsq hTpos hTsq
  have hTne : Tvar ≠ 0 := Rat.ne_of_gt hTpos
  have hT2pos : (0 : Rat) < Tvar * Tvar := rat_mul_pos hTpos hTpos
  have hT2ne : Tvar * Tvar ≠ 0 := Rat.ne_of_gt hT2pos
  have hsum : (0 : Rat) < sz2 + sq2 := rat_add_pos hsz hsq
  have hsum_ne : sz2 + sq2 ≠ 0 := Rat.ne_of_gt hsum
  have hsq2 : sq2 = sz2 * (Tvar * Tvar - 1) := by
    unfold wienerTemp at hTsq
    have hdiv : sq2 / sz2 = Tvar * Tvar - 1 := by grind
    have hmul := (rat_div_eq_iff (Rat.ne_of_gt hsz)).mp hdiv
    grind
  have hsz_add_sq : sz2 + sq2 = sz2 * (Tvar * Tvar) := by rw [hsq2]; grind
  have hopt_tvar : wienerOptMSE sz2 sq2 = sz2 * (Tvar * Tvar - 1) / (Tvar * Tvar) := by
    unfold wienerOptMSE
    rw [hsz_add_sq, hsq2]
    apply rat_eq_of_mul_eq_mul_right hT2ne
    have h1 : (sz2 * (Tvar * Tvar - 1) / (Tvar * Tvar)) * (Tvar * Tvar) = sz2 * (Tvar * Tvar - 1) :=
      rat_div_mul_cancel hT2ne
    rw [h1]
    have hszT2_ne : sz2 * (Tvar * Tvar) ≠ 0 := Rat.ne_of_gt (rat_mul_pos hsz hT2pos)
    have h2 : (sz2 * (sz2 * (Tvar * Tvar - 1)) / (sz2 * (Tvar * Tvar))) * (sz2 * (Tvar * Tvar)) =
        sz2 * (sz2 * (Tvar * Tvar - 1)) := rat_div_mul_cancel hszT2_ne
    apply rat_eq_of_mul_eq_mul_right (Rat.ne_of_gt hsz)
    calc (sz2 * (sz2 * (Tvar * Tvar - 1)) / (sz2 * (Tvar * Tvar))) * (Tvar * Tvar) * sz2
        = (sz2 * (sz2 * (Tvar * Tvar - 1)) / (sz2 * (Tvar * Tvar))) * (sz2 * (Tvar * Tvar)) := by grind
      _ = sz2 * (sz2 * (Tvar * Tvar - 1)) := h2
      _ = sz2 * (Tvar * Tvar - 1) * sz2 := by grind
  have hgap : logitMSE sz2 sq2 Tvar - logitMSE sz2 sq2 (wienerTemp sz2 sq2) =
      sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar) := by
    rw [logitMSE_at_tvar hsz hTpos hTsq, logitMSE_at_wienerTemp hsz hsq, hopt_tvar]
    apply rat_eq_of_mul_eq_mul_right hT2ne
    have hTinv : (1 / Tvar) * Tvar = 1 := rat_div_mul_cancel hTne
    have ha : (1 - 1 / Tvar) * (Tvar * Tvar) = (Tvar - 1) * Tvar := by
      calc (1 - 1 / Tvar) * (Tvar * Tvar)
          = Tvar * Tvar - ((1 / Tvar) * Tvar) * Tvar := by grind
        _ = Tvar * Tvar - 1 * Tvar := by rw [hTinv]
        _ = (Tvar - 1) * Tvar := by grind
    have hb : (sz2 * (Tvar * Tvar - 1) / (Tvar * Tvar)) * (Tvar * Tvar) = sz2 * (Tvar * Tvar - 1) :=
      rat_div_mul_cancel hT2ne
    have hc : (sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar)) * (Tvar * Tvar) =
        sz2 * ((Tvar - 1) * (Tvar - 1)) := rat_div_mul_cancel hT2ne
    calc (2 * sz2 * (1 - 1 / Tvar) - sz2 * (Tvar * Tvar - 1) / (Tvar * Tvar)) * (Tvar * Tvar)
        = 2 * sz2 * ((1 - 1 / Tvar) * (Tvar * Tvar)) -
          (sz2 * (Tvar * Tvar - 1) / (Tvar * Tvar)) * (Tvar * Tvar) := by grind
      _ = 2 * sz2 * ((Tvar - 1) * Tvar) - sz2 * (Tvar * Tvar - 1) := by rw [ha, hb]
      _ = sz2 * ((Tvar - 1) * (Tvar - 1)) := by grind
      _ = (sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar)) * (Tvar * Tvar) := hc.symm
  have hTm1_pos : (0 : Rat) < Tvar - 1 := rat_sub_pos hTgt1
  have hgap_pos : (0 : Rat) < sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar) :=
    rat_div_pos (rat_mul_pos hsz (rat_mul_pos hTm1_pos hTm1_pos)) hT2pos
  have hlt1 : logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 Tvar := by
    apply rat_lt_of_sub_pos; rw [hgap]; exact hgap_pos
  have hdiff_1_tvar : logitMSE sz2 sq2 1 - logitMSE sz2 sq2 Tvar =
      sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) / Tvar := by
    rw [logitMSE_at_one, logitMSE_at_tvar hsz hTpos hTsq, hsq2]
    apply rat_eq_of_mul_eq_mul_right hTne
    have hTinv : (1 / Tvar) * Tvar = 1 := rat_div_mul_cancel hTne
    have hd : (sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) / Tvar) * Tvar =
        sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) := rat_div_mul_cancel hTne
    calc (sz2 * (Tvar * Tvar - 1) - 2 * sz2 * (1 - 1 / Tvar)) * Tvar
        = sz2 * (Tvar * Tvar - 1) * Tvar - 2 * sz2 * (Tvar - (1 / Tvar) * Tvar) := by grind
      _ = sz2 * (Tvar * Tvar - 1) * Tvar - 2 * sz2 * (Tvar - 1) := by rw [hTinv]
      _ = sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) := by grind
      _ = (sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) / Tvar) * Tvar := hd.symm
  have hTp2_pos : (0 : Rat) < Tvar + 2 := rat_add_pos hTpos (by decide)
  have hlt2 : logitMSE sz2 sq2 Tvar < logitMSE sz2 sq2 1 := by
    apply rat_lt_of_sub_pos
    rw [hdiff_1_tvar]
    exact rat_div_pos (rat_mul_pos hsz (rat_mul_pos (rat_mul_pos hTm1_pos hTm1_pos) hTp2_pos)) hTpos
  have hdiff_1_opt : logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2) =
      sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) / (Tvar * Tvar) := by
    have ⟨hsave, _, _⟩ := logitMSE_saving_over_one hsz hsq
    rw [hsave, hsz_add_sq, hsq2]
    apply rat_eq_of_mul_eq_mul_right hT2ne
    have h1 : (sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) / (Tvar * Tvar)) *
        (Tvar * Tvar) = sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) :=
      rat_div_mul_cancel hT2ne
    rw [h1]
    have hszT2_ne : sz2 * (Tvar * Tvar) ≠ 0 := Rat.ne_of_gt (rat_mul_pos hsz hT2pos)
    have h2 : (sz2 * (Tvar * Tvar - 1) * (sz2 * (Tvar * Tvar - 1)) / (sz2 * (Tvar * Tvar))) *
        (sz2 * (Tvar * Tvar)) = sz2 * (Tvar * Tvar - 1) * (sz2 * (Tvar * Tvar - 1)) :=
      rat_div_mul_cancel hszT2_ne
    apply rat_eq_of_mul_eq_mul_right (Rat.ne_of_gt hsz)
    calc (sz2 * (Tvar * Tvar - 1) * (sz2 * (Tvar * Tvar - 1)) / (sz2 * (Tvar * Tvar))) *
          (Tvar * Tvar) * sz2
        = (sz2 * (Tvar * Tvar - 1) * (sz2 * (Tvar * Tvar - 1)) / (sz2 * (Tvar * Tvar))) *
          (sz2 * (Tvar * Tvar)) := by grind
      _ = sz2 * (Tvar * Tvar - 1) * (sz2 * (Tvar * Tvar - 1)) := h2
      _ = sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) * sz2 := by grind
  have hTp1_pos : (0 : Rat) < Tvar + 1 := rat_add_pos hTpos (by decide)
  have hTp1_sq_pos : (0 : Rat) < (Tvar + 1) * (Tvar + 1) := rat_mul_pos hTp1_pos hTp1_pos
  have hTp1_sq_ne : (Tvar + 1) * (Tvar + 1) ≠ 0 := Rat.ne_of_gt hTp1_sq_pos
  have hdenom_pos : (0 : Rat) < logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2) := by
    have ⟨hsave, hpos, _⟩ := logitMSE_saving_over_one hsz hsq
    rw [hsave]; exact hpos
  have hrec_eq :
      (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 Tvar) /
        (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2)) =
      1 - 1 / ((Tvar + 1) * (Tvar + 1)) := by
    rw [rat_div_eq_iff (Rat.ne_of_gt hdenom_pos), hdiff_1_tvar, hdiff_1_opt]
    apply rat_eq_of_mul_eq_mul_right hT2ne
    have h1 : (sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) / Tvar) * (Tvar * Tvar) =
        sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) * Tvar := by
      calc (sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) / Tvar) * (Tvar * Tvar)
          = ((sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) / Tvar) * Tvar) * Tvar := by grind
        _ = sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) * Tvar := by rw [rat_div_mul_cancel hTne]
    have h2 : (sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) / (Tvar * Tvar)) *
        (Tvar * Tvar) = sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) :=
      rat_div_mul_cancel hT2ne
    have h3 : (1 - 1 / ((Tvar + 1) * (Tvar + 1))) * ((Tvar + 1) * (Tvar + 1)) =
        (Tvar + 1) * (Tvar + 1) - 1 := by
      calc (1 - 1 / ((Tvar + 1) * (Tvar + 1))) * ((Tvar + 1) * (Tvar + 1))
          = (Tvar + 1) * (Tvar + 1) - (1 / ((Tvar + 1) * (Tvar + 1))) * ((Tvar + 1) * (Tvar + 1)) := by grind
        _ = (Tvar + 1) * (Tvar + 1) - 1 := by rw [rat_div_mul_cancel hTp1_sq_ne]
    rw [h1]
    calc sz2 * ((Tvar - 1) * (Tvar - 1) * (Tvar + 2)) * Tvar
        = sz2 * ((Tvar - 1) * (Tvar - 1)) * ((Tvar + 1) * (Tvar + 1) - 1) := by grind
      _ = sz2 * ((Tvar - 1) * (Tvar - 1)) *
          ((1 - 1 / ((Tvar + 1) * (Tvar + 1))) * ((Tvar + 1) * (Tvar + 1))) := by rw [← h3]
      _ = (1 - 1 / ((Tvar + 1) * (Tvar + 1))) *
          (sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1)))) := by grind
      _ = (1 - 1 / ((Tvar + 1) * (Tvar + 1))) *
          (sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) / (Tvar * Tvar)) *
          (Tvar * Tvar) := by
            have hassoc : (1 - 1 / ((Tvar + 1) * (Tvar + 1))) *
                (sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) / (Tvar * Tvar)) *
                (Tvar * Tvar) =
                (1 - 1 / ((Tvar + 1) * (Tvar + 1))) *
                ((sz2 * ((Tvar - 1) * (Tvar - 1) * ((Tvar + 1) * (Tvar + 1))) / (Tvar * Tvar)) *
                  (Tvar * Tvar)) := by grind
            rw [hassoc, h2]
  have hTp1_gt2 : (2 : Rat) < Tvar + 1 := by
    apply rat_lt_of_sub_pos
    have : Tvar + 1 - 2 = Tvar - 1 := by grind
    rw [this]; exact hTm1_pos
  have hTp1_sq_gt4 : (4 : Rat) < (Tvar + 1) * (Tvar + 1) := by
    have ha : (2 : Rat) * 2 < 2 * (Tvar + 1) := rat_mul_lt_mul_of_pos_left hTp1_gt2 (by decide)
    have hb : 2 * (Tvar + 1) < (Tvar + 1) * (Tvar + 1) := rat_mul_lt_mul_of_pos_right hTp1_gt2 hTp1_pos
    have h22 : (2 : Rat) * 2 = 4 := by grind
    rw [h22] at ha
    exact rat_lt_trans ha hb
  have hinv_lt : (1 : Rat) / ((Tvar + 1) * (Tvar + 1)) < 1 / 4 := by
    rw [rat_div_lt_div_iff hTp1_sq_pos (by decide : (0 : Rat) < 4)]
    grind
  have hrec_gt : (3 / 4 : Rat) < 1 - 1 / ((Tvar + 1) * (Tvar + 1)) := by
    apply rat_lt_of_sub_pos
    have hsub : (1 - 1 / ((Tvar + 1) * (Tvar + 1))) - 3 / 4 =
        1 / 4 - 1 / ((Tvar + 1) * (Tvar + 1)) := by grind
    rw [hsub]
    exact rat_sub_pos hinv_lt
  have hrec_lt : 1 - 1 / ((Tvar + 1) * (Tvar + 1)) < 1 := by
    apply rat_lt_of_sub_pos
    have hsub : 1 - (1 - 1 / ((Tvar + 1) * (Tvar + 1))) = 1 / ((Tvar + 1) * (Tvar + 1)) := by grind
    rw [hsub]
    exact rat_div_pos (by decide) hTp1_sq_pos
  exact ⟨hgap, hgap_pos, hlt1, hlt2, hrec_eq, hrec_gt, hrec_lt⟩

/-- Headline Theorem 2 (`wiener_mmse_strictly_beats_variance_matching_and_uncalibrated`). -/
theorem wiener_mmse_strictly_beats_variance_matching_and_uncalibrated :
    (∀ sz2 sq2 : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 →
      logitMSE sz2 sq2 1 = sq2 ∧
      logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2) = (sq2 * sq2) / (sz2 + sq2) ∧
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 1) ∧
    (∀ sz2 sq2 Tvar : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 → (0 : Rat) < Tvar →
      Tvar * Tvar = wienerTemp sz2 sq2 →
      (1 : Rat) < Tvar ∧
      Tvar < wienerTemp sz2 sq2 ∧
      logitMSE sz2 sq2 Tvar = 2 * sz2 * (1 - 1 / Tvar) ∧
      logitMSE sz2 sq2 Tvar - logitMSE sz2 sq2 (wienerTemp sz2 sq2) =
        sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar) ∧
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 Tvar ∧
      logitMSE sz2 sq2 Tvar < logitMSE sz2 sq2 1 ∧
      (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 Tvar) /
        (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2)) =
        1 - 1 / ((Tvar + 1) * (Tvar + 1)) ∧
      (3 / 4 : Rat) < 1 - 1 / ((Tvar + 1) * (Tvar + 1)) ∧
      1 - 1 / ((Tvar + 1) * (Tvar + 1)) < 1) ∧
    (∀ sz2 sq2 T : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 →
      (1 : Rat) ≤ T → T < wienerTemp sz2 sq2 →
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sz2 sq2 hsz hsq
    have ⟨hdiff, _, hlt⟩ := logitMSE_saving_over_one hsz hsq
    exact ⟨logitMSE_at_one sz2 sq2, hdiff, hlt⟩
  · intro sz2 sq2 Tvar hsz hsq hTpos hTsq
    have ⟨h1, h2⟩ := tvar_bounds hsz hsq hTpos hTsq
    have h3 := logitMSE_at_tvar hsz hTpos hTsq
    have ⟨h4, _, h5, h6, h7, h8, h9⟩ := tvar_gap_and_recovery hsz hsq hTpos hTsq
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · intro sz2 sq2 T hsz hsq hge1 hlt
    have hTpos : (0 : Rat) < T := rat_lt_of_lt_of_le (by decide : (0 : Rat) < 1) hge1
    rw [logitMSE_at_wienerTemp hsz hsq]
    exact logitMSE_gt_wienerOptMSE_of_ne hsz hsq (Rat.ne_of_gt hTpos) (Rat.ne_of_lt hlt)

end SpecDecWienerTemp
