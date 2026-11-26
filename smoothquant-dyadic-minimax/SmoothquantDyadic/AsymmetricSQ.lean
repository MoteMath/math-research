/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SmoothquantDyadic.RatOrder

/-!
# Asymmetric-Bitwidth SmoothQuant AM-GM Law & Channel-Outlier Coupling Paradox

Proves:
- Theorem 1 (`smoothquant_asymmetric_amgm_optimal_scale`)
- Theorem 6 (`channel_outlier_coupling_paradox_exact`)
-/

namespace SmoothquantDyadic

/-! ### Part 1: Universal Bilinear AM-GM Identity & Optimality -/

theorem bilinearErr_sq_sub_four_mul (A B s : Rat) (hs : s ≠ 0) :
    bilinearErr A B s * bilinearErr A B s - 4 * A * B =
      (A * (s * s) - B / (s * s)) * (A * (s * s) - B / (s * s)) := by
  unfold bilinearErr
  have hs2 : s * s ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero hs)
  have hmul : (B / (s * s)) * (s * s) = B := rat_div_mul_cancel hs2
  have hcross : A * (s * s) * (B / (s * s)) = A * B := by
    calc A * (s * s) * (B / (s * s))
        = A * ((B / (s * s)) * (s * s)) := by grind
      _ = A * B := by rw [hmul]
  grind

theorem bilinearErr_sub_two_c (A B c s : Rat)
    (hA : 0 < A) (hc2 : c * c = A * B) (hs : 0 < s) :
    bilinearErr A B s - 2 * c =
      (A * (s * s) - c) * (A * (s * s) - c) / (A * (s * s)) := by
  unfold bilinearErr
  have hs2 : 0 < s * s := rat_mul_pos hs hs
  have hs2ne : s * s ≠ 0 := Rat.ne_of_gt hs2
  have hAs2 : 0 < A * (s * s) := rat_mul_pos hA hs2
  have hAs2ne : A * (s * s) ≠ 0 := Rat.ne_of_gt hAs2
  rw [eq_comm, rat_div_eq_iff hAs2ne]
  have hmul : (B / (s * s)) * (A * (s * s)) = A * B := by
    calc (B / (s * s)) * (A * (s * s))
        = A * ((B / (s * s)) * (s * s)) := by grind
      _ = A * B := by rw [rat_div_mul_cancel hs2ne]
  grind

theorem bilinearErr_eq_two_c_iff (A B c s : Rat)
    (hA : 0 < A) (hc : 0 < c) (hc2 : c * c = A * B) (hs : 0 < s) :
    bilinearErr A B s = 2 * c ↔ s * s * s * s = B / A := by
  have hAne : A ≠ 0 := Rat.ne_of_gt hA
  have hs2 : 0 < s * s := rat_mul_pos hs hs
  have hAs2 : 0 < A * (s * s) := rat_mul_pos hA hs2
  have hAs2ne : A * (s * s) ≠ 0 := Rat.ne_of_gt hAs2
  have hdiff := bilinearErr_sub_two_c A B c s hA hc2 hs
  constructor
  · intro heq
    have h0 : (A * (s * s) - c) * (A * (s * s) - c) / (A * (s * s)) = 0 := by
      rw [← hdiff, heq]; grind
    have hnum : (A * (s * s) - c) * (A * (s * s) - c) = 0 := by
      have := (rat_div_eq_iff hAs2ne).mp h0
      grind
    have hlin : A * (s * s) = c := by
      cases Rat.mul_eq_zero.mp hnum with
      | inl h => grind
      | inr h => grind
    rw [eq_comm, rat_div_eq_iff hAne]
    have hsq : (A * (s * s)) * (A * (s * s)) = c * c := by rw [hlin]
    rw [hc2] at hsq
    have hfac : A * (s * s * s * s * A - B) = 0 := by grind
    cases Rat.mul_eq_zero.mp hfac with
    | inl h => exact False.elim (hAne h)
    | inr h => grind
  · intro hs4
    have hs4A : s * s * s * s * A = B := by
      have := (rat_div_eq_iff hAne).mp hs4.symm
      grind
    have hsq : (A * (s * s) - c) * (A * (s * s) + c) = 0 := by
      have : (A * (s * s)) * (A * (s * s)) = c * c := by
        rw [hc2]
        calc (A * (s * s)) * (A * (s * s))
            = A * (s * s * s * s * A) := by grind
          _ = A * B := by rw [hs4A]
      grind
    have hpos_sum : 0 < A * (s * s) + c := rat_add_pos hAs2 hc
    have hlin : A * (s * s) - c = 0 := by
      cases Rat.mul_eq_zero.mp hsq with
      | inl h => exact h
      | inr h => exact False.elim (Rat.ne_of_gt hpos_sum h)
    rw [hlin] at hdiff
    have h0 : (0 : Rat) * 0 / (A * (s * s)) = 0 := by
      rw [Rat.zero_mul, Rat.div_def, Rat.zero_mul]
    rw [h0] at hdiff
    grind

/-! ### Part 2: Interior-Channel Asymmetric-Bitwidth SmoothQuant Law -/

theorem interiorChannelErr_opt (qW qX : Rat) (hqW : 0 < qW) (hqX : 0 < qX) :
    interiorChannelErr qW qX (qX / qW) = 2 / (qW * qX) := by
  unfold interiorChannelErr
  have hqWne : qW ≠ 0 := Rat.ne_of_gt hqW
  have hqXne : qX ≠ 0 := Rat.ne_of_gt hqX
  have hqWqXne : qW * qX ≠ 0 := Rat.ne_of_gt (rat_mul_pos hqW hqX)
  have h1 : qW * qW * (qX / qW) = qW * qX := by
    calc qW * qW * (qX / qW)
        = qW * (qW * (qX / qW)) := by grind
      _ = qW * qX := by rw [rat_mul_div_cancel hqWne]
  have h2 : (qX / qW) / (qX * qX) = 1 / (qW * qX) := by
    apply rat_div_eq_of_cross (Rat.ne_of_gt (rat_mul_pos hqX hqX)) hqWqXne
    calc (qX / qW) * (qW * qX)
        = ((qX / qW) * qW) * qX := by grind
      _ = qX * qX := by rw [rat_div_mul_cancel hqWne]
      _ = 1 * (qX * qX) := by grind
  rw [h1, h2]
  rw [Rat.div_def, Rat.div_def]
  grind

theorem interiorChannelErr_sub_opt (qW qX u : Rat)
    (hqW : 0 < qW) (hqX : 0 < qX) (hu : 0 < u) :
    interiorChannelErr qW qX u - interiorChannelErr qW qX (qX / qW) =
      (qW * u - qX) * (qW * u - qX) / (qW * qW * qX * qX * u) := by
  rw [interiorChannelErr_opt qW qX hqW hqX]
  unfold interiorChannelErr
  have hqW2 : 0 < qW * qW := rat_mul_pos hqW hqW
  have hqX2 : 0 < qX * qX := rat_mul_pos hqX hqX
  have hden : 0 < qW * qW * qX * qX * u :=
    rat_mul_pos (rat_mul_pos (rat_mul_pos hqW2 hqX) hqX) hu
  have hden_ne : qW * qW * qX * qX * u ≠ 0 := Rat.ne_of_gt hden
  have hqW2u_ne : qW * qW * u ≠ 0 := Rat.ne_of_gt (rat_mul_pos hqW2 hu)
  have hqX2_ne : qX * qX ≠ 0 := Rat.ne_of_gt hqX2
  have hqWqX_ne : qW * qX ≠ 0 := Rat.ne_of_gt (rat_mul_pos hqW hqX)
  rw [eq_comm, rat_div_eq_iff hden_ne]
  have ht1 : (1 / (qW * qW * u)) * (qW * qW * qX * qX * u) = qX * qX := by
    calc (1 / (qW * qW * u)) * (qW * qW * qX * qX * u)
        = ((1 / (qW * qW * u)) * (qW * qW * u)) * (qX * qX) := by grind
      _ = 1 * (qX * qX) := by rw [rat_div_mul_cancel hqW2u_ne]
      _ = qX * qX := by grind
  have ht2 : (u / (qX * qX)) * (qW * qW * qX * qX * u) = qW * qW * u * u := by
    calc (u / (qX * qX)) * (qW * qW * qX * qX * u)
        = ((u / (qX * qX)) * (qX * qX)) * (qW * qW * u) := by grind
      _ = u * (qW * qW * u) := by rw [rat_div_mul_cancel hqX2_ne]
      _ = qW * qW * u * u := by grind
  have ht3 : (2 / (qW * qX)) * (qW * qW * qX * qX * u) = 2 * qW * qX * u := by
    calc (2 / (qW * qX)) * (qW * qW * qX * qX * u)
        = ((2 / (qW * qX)) * (qW * qX)) * (qW * qX * u) := by grind
      _ = 2 * (qW * qX * u) := by rw [rat_div_mul_cancel hqWqX_ne]
      _ = 2 * qW * qX * u := by grind
  grind

theorem interiorChannelErr_half_ratio (qW qX : Rat) (hqW : 0 < qW) (hqX : 0 < qX) :
    interiorChannelErr qW qX 1 / interiorChannelErr qW qX (qX / qW) =
      sqHalfPenaltyRatio qW qX := by
  rw [interiorChannelErr_opt qW qX hqW hqX]
  unfold interiorChannelErr sqHalfPenaltyRatio
  have hqW2 : qW * qW ≠ 0 := Rat.ne_of_gt (rat_mul_pos hqW hqW)
  have hqX2 : qX * qX ≠ 0 := Rat.ne_of_gt (rat_mul_pos hqX hqX)
  have hqWqX : qW * qX ≠ 0 := Rat.ne_of_gt (rat_mul_pos hqW hqX)
  have h2qWqX : 2 * qW * qX ≠ 0 := Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide) hqW) hqX)
  have hden : 2 / (qW * qX) ≠ 0 := Rat.ne_of_gt (rat_div_pos (by decide) (rat_mul_pos hqW hqX))
  apply rat_div_eq_of_cross hden h2qWqX
  have hL1 : (1 / (qW * qW * 1)) * (2 * qW * qX) = 2 * qX / qW := by
    have hqWne : qW ≠ 0 := Rat.ne_of_gt hqW
    rw [Rat.mul_one, eq_comm, rat_div_eq_iff hqWne]
    calc 2 * qX = 1 * (2 * qX) := by grind
      _ = ((1 / (qW * qW)) * (qW * qW)) * (2 * qX) := by rw [rat_div_mul_cancel hqW2]
      _ = (1 / (qW * qW)) * (2 * qW * qX) * qW := by grind
  have hL2 : (1 / (qX * qX)) * (2 * qW * qX) = 2 * qW / qX := by
    have hqXne : qX ≠ 0 := Rat.ne_of_gt hqX
    rw [eq_comm, rat_div_eq_iff hqXne]
    calc 2 * qW = 1 * (2 * qW) := by grind
      _ = ((1 / (qX * qX)) * (qX * qX)) * (2 * qW) := by rw [rat_div_mul_cancel hqX2]
      _ = (1 / (qX * qX)) * (2 * qW * qX) * qX := by grind
  have hR : (qX * qX + qW * qW) * (2 / (qW * qX)) = 2 * qX / qW + 2 * qW / qX := by
    have hqWne : qW ≠ 0 := Rat.ne_of_gt hqW
    have hqXne : qX ≠ 0 := Rat.ne_of_gt hqX
    have hmul : ((qX * qX + qW * qW) * (2 / (qW * qX)) - (2 * qX / qW + 2 * qW / qX)) * (qW * qX) = 0 := by
      have ha : (qX * qX + qW * qW) * (2 / (qW * qX)) * (qW * qX) = (qX * qX + qW * qW) * 2 := by
        calc (qX * qX + qW * qW) * (2 / (qW * qX)) * (qW * qX)
            = (qX * qX + qW * qW) * ((2 / (qW * qX)) * (qW * qX)) := by grind
          _ = (qX * qX + qW * qW) * 2 := by rw [rat_div_mul_cancel hqWqX]
      have hb : (2 * qX / qW) * (qW * qX) = 2 * qX * qX := by
        calc (2 * qX / qW) * (qW * qX)
            = ((2 * qX / qW) * qW) * qX := by grind
          _ = 2 * qX * qX := by rw [rat_div_mul_cancel hqWne]
      have hc : (2 * qW / qX) * (qW * qX) = 2 * qW * qW := by
        calc (2 * qW / qX) * (qW * qX)
            = ((2 * qW / qX) * qX) * qW := by grind
          _ = 2 * qW * qW := by rw [rat_div_mul_cancel hqXne]
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h => grind
    | inr h => exact False.elim (hqWqX h)
  grind

theorem sqHalfPenaltyRatio_decomp (qW qX : Rat) (hqW : 0 < qW) (hqX : 0 < qX) :
    sqHalfPenaltyRatio qW qX = 1 + (qX - qW) * (qX - qW) / (2 * qW * qX) := by
  unfold sqHalfPenaltyRatio
  have h2 : 2 * qW * qX ≠ 0 := Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (by decide) hqW) hqX)
  rw [rat_div_eq_iff h2]
  have hc : ((qX - qW) * (qX - qW) / (2 * qW * qX)) * (2 * qW * qX) = (qX - qW) * (qX - qW) :=
    rat_div_mul_cancel h2
  grind

/-! ### Part 3: Bulk-Channel Critical Clamping Threshold `M_crit = q_X / q_W` -/

theorem bulkChannelErr_sub_unscaled (qW qX M u : Rat)
    (hqW : 0 < qW) (hqX : 0 < qX) (hM : 0 < M) (hu : 0 < u) :
    bulkChannelErr qW qX M u - bulkChannelErr qW qX M 1 =
      (u - 1) * (qX * qX * u - M * M * qW * qW) / (M * M * qW * qW * qX * qX * u) := by
  unfold bulkChannelErr
  have hM2 : 0 < M * M := rat_mul_pos hM hM
  have hqW2 : 0 < qW * qW := rat_mul_pos hqW hqW
  have hqX2 : 0 < qX * qX := rat_mul_pos hqX hqX
  have hM2qW2_pos : 0 < M * M * qW * qW := rat_mul_pos (rat_mul_pos hM2 hqW) hqW
  have hM2qW2 : M * M * qW * qW ≠ 0 := Rat.ne_of_gt hM2qW2_pos
  have hqX2u : qX * qX * u ≠ 0 := Rat.ne_of_gt (rat_mul_pos hqX2 hu)
  have hqX2_ne : qX * qX ≠ 0 := Rat.ne_of_gt hqX2
  have hden : M * M * qW * qW * qX * qX * u ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (rat_mul_pos (rat_mul_pos hM2qW2_pos hqX) hqX) hu)
  rw [eq_comm, rat_div_eq_iff hden]
  have ht1 : (u / (M * M * qW * qW)) * (M * M * qW * qW * qX * qX * u) = u * qX * qX * u := by
    calc (u / (M * M * qW * qW)) * (M * M * qW * qW * qX * qX * u)
        = ((u / (M * M * qW * qW)) * (M * M * qW * qW)) * (qX * qX * u) := by grind
      _ = u * (qX * qX * u) := by rw [rat_div_mul_cancel hM2qW2]
      _ = u * qX * qX * u := by grind
  have ht2 : (1 / (qX * qX * u)) * (M * M * qW * qW * qX * qX * u) = M * M * qW * qW := by
    calc (1 / (qX * qX * u)) * (M * M * qW * qW * qX * qX * u)
        = ((1 / (qX * qX * u)) * (qX * qX * u)) * (M * M * qW * qW) := by grind
      _ = 1 * (M * M * qW * qW) := by rw [rat_div_mul_cancel hqX2u]
      _ = M * M * qW * qW := by grind
  have ht3 : (1 / (M * M * qW * qW)) * (M * M * qW * qW * qX * qX * u) = qX * qX * u := by
    calc (1 / (M * M * qW * qW)) * (M * M * qW * qW * qX * qX * u)
        = ((1 / (M * M * qW * qW)) * (M * M * qW * qW)) * (qX * qX * u) := by grind
      _ = 1 * (qX * qX * u) := by rw [rat_div_mul_cancel hM2qW2]
      _ = qX * qX * u := by grind
  have ht4 : (1 / (qX * qX * 1)) * (M * M * qW * qW * qX * qX * u) = M * M * qW * qW * u := by
    rw [Rat.mul_one]
    calc (1 / (qX * qX)) * (M * M * qW * qW * qX * qX * u)
        = ((1 / (qX * qX)) * (qX * qX)) * (M * M * qW * qW * u) := by grind
      _ = 1 * (M * M * qW * qW * u) := by rw [rat_div_mul_cancel hqX2_ne]
      _ = M * M * qW * qW * u := by grind
  grind

theorem bulkChannelErr_clamps_below_Mcrit (qW qX M u : Rat)
    (hqW : 0 < qW) (hqX : 0 < qX) (hM : 1 ≤ M) (hu : 1 < u)
    (hMc : M ≤ criticalClampThreshold qW qX) :
    bulkChannelErr qW qX M 1 < bulkChannelErr qW qX M u := by
  have hMpos : 0 < M := rat_lt_of_lt_of_le (by decide) hM
  have hupos : 0 < u := rat_lt_trans (by decide) hu
  apply rat_lt_of_sub_pos
  rw [bulkChannelErr_sub_unscaled qW qX M u hqW hqX hMpos hupos]
  have hMqW : M * qW ≤ qX := by
    unfold criticalClampThreshold at hMc
    have h := rat_mul_le_mul_of_nonneg_right hMc (Rat.le_of_lt hqW)
    rw [rat_div_mul_cancel (Rat.ne_of_gt hqW)] at h
    exact h
  have hMqW_sq : M * M * qW * qW ≤ qX * qX := by
    have hpos : 0 ≤ M * qW := Rat.le_of_lt (rat_mul_pos hMpos hqW)
    have h1 := rat_mul_le_mul_of_nonneg_left hMqW hpos
    have h2 := rat_mul_le_mul_of_nonneg_right hMqW (Rat.le_of_lt hqX)
    have h3 := Rat.le_trans h1 h2
    have heq : M * qW * (M * qW) = M * M * qW * qW := by grind
    rw [heq] at h3
    exact h3
  have hqX2 : 0 < qX * qX := rat_mul_pos hqX hqX
  have hqX2u : qX * qX < qX * qX * u := by
    have h := rat_mul_lt_mul_of_pos_left hu hqX2
    rw [Rat.mul_one] at h
    exact h
  have hfac2 : 0 < qX * qX * u - M * M * qW * qW :=
    rat_sub_pos (rat_lt_of_le_of_lt hMqW_sq hqX2u)
  have hfac1 : 0 < u - 1 := rat_sub_pos hu
  have hden : 0 < M * M * qW * qW * qX * qX * u :=
    rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hMpos hMpos) hqW) hqW) hqX) hqX) hupos
  exact rat_div_pos (rat_mul_pos hfac1 hfac2) hden

theorem bulkChannelErr_improves_above_Mcrit (qW qX M : Rat)
    (hqW : 0 < qW) (hqX : 0 < qX) (hMc : criticalClampThreshold qW qX < M) :
    1 < M * qW / qX ∧
    bulkChannelErr qW qX M (M * qW / qX) < bulkChannelErr qW qX M 1 := by
  unfold criticalClampThreshold at hMc
  have hqXne : qX ≠ 0 := Rat.ne_of_gt hqX
  have hqWne : qW ≠ 0 := Rat.ne_of_gt hqW
  have hMqW : qX < M * qW := by
    have h := rat_mul_lt_mul_of_pos_right hMc hqW
    rw [rat_div_mul_cancel hqWne] at h
    exact h
  have hu_gt1 : 1 < M * qW / qX := by
    apply rat_lt_div_of_mul_lt hqX
    rw [Rat.one_mul]
    exact hMqW
  refine ⟨hu_gt1, ?_⟩
  have hMpos : 0 < M := rat_lt_trans (rat_div_pos hqX hqW) hMc
  have hupos : 0 < M * qW / qX := rat_lt_trans (by decide) hu_gt1
  apply rat_lt_of_sub_pos
  have hsub := bulkChannelErr_sub_unscaled qW qX M (M * qW / qX) hqW hqX hMpos hupos
  have hden_pos : 0 < M * M * qW * qW * qX * qX * (M * qW / qX) :=
    rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hMpos hMpos) hqW) hqW) hqX) hqX) hupos
  have hneg : bulkChannelErr qW qX M 1 - bulkChannelErr qW qX M (M * qW / qX) =
      (M * qW / qX - 1) * (M * M * qW * qW - qX * qX * (M * qW / qX)) /
        (M * M * qW * qW * qX * qX * (M * qW / qX)) := by
    have hden_ne : M * M * qW * qW * qX * qX * (M * qW / qX) ≠ 0 := Rat.ne_of_gt hden_pos
    rw [eq_comm, rat_div_eq_iff hden_ne]
    have h1 := (rat_div_eq_iff hden_ne).mp hsub.symm
    grind
  rw [hneg]
  have hnum2 : M * M * qW * qW - qX * qX * (M * qW / qX) = M * qW * (M * qW - qX) := by
    have hc : qX * qX * (M * qW / qX) = qX * (M * qW) := by
      calc qX * qX * (M * qW / qX)
          = qX * (qX * (M * qW / qX)) := by grind
        _ = qX * (M * qW) := by rw [rat_mul_div_cancel hqXne]
    grind
  rw [hnum2]
  have hpos1 : 0 < M * qW / qX - 1 := rat_sub_pos hu_gt1
  have hpos2 : 0 < M * qW * (M * qW - qX) := rat_mul_pos (rat_mul_pos hMpos hqW) (rat_sub_pos hMqW)
  exact rat_div_pos (rat_mul_pos hpos1 hpos2) hden_pos

/-! ### Headline Theorem 1 -/

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B s hs
    have h := bilinearErr_sq_sub_four_mul A B s hs
    refine ⟨h, ?_⟩
    apply rat_le_of_sub_nonneg
    rw [h]
    exact rat_sq_nonneg _
  · intro A B c s hA _hB hc hc2 hs
    have hdiff := bilinearErr_sub_two_c A B c s hA hc2 hs
    refine ⟨hdiff, ?_, bilinearErr_eq_two_c_iff A B c s hA hc hc2 hs⟩
    apply rat_le_of_sub_nonneg
    rw [hdiff]
    exact rat_div_nonneg (rat_sq_nonneg _) (rat_mul_pos hA (rat_mul_pos hs hs))
  · intro qW qX u hqW hqX hu
    have hopt := interiorChannelErr_opt qW qX hqW hqX
    have hsub := interiorChannelErr_sub_opt qW qX u hqW hqX hu
    have hrat := interiorChannelErr_half_ratio qW qX hqW hqX
    have hdec := sqHalfPenaltyRatio_decomp qW qX hqW hqX
    have hden : 0 < qW * qW * qX * qX * u :=
      rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hqW hqW) hqX) hqX) hu
    have h2 : 0 < 2 * qW * qX := rat_mul_pos (rat_mul_pos (by decide) hqW) hqX
    refine ⟨hopt, hsub, ?_, hrat, hdec, ?_, ?_⟩
    · apply rat_le_of_sub_nonneg
      rw [hsub]
      exact rat_div_nonneg (rat_sq_nonneg _) hden
    · rw [hdec]
      have h0 : (0 : Rat) ≤ (qX - qW) * (qX - qW) / (2 * qW * qX) :=
        rat_div_nonneg (rat_sq_nonneg _) h2
      have h1 := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) h0
      rw [Rat.add_zero] at h1
      exact h1
    · intro hne
      rw [hdec]
      apply rat_lt_of_sub_pos
      have hdiff : 1 + (qX - qW) * (qX - qW) / (2 * qW * qX) - 1 =
          (qX - qW) * (qX - qW) / (2 * qW * qX) := by grind
      rw [hdiff]
      have hne0 : qX - qW ≠ 0 := by
        intro h0
        apply hne
        grind
      exact rat_div_pos (rat_sq_pos_of_ne_zero hne0) h2
  · unfold sqHalfPenaltyRatio criticalClampThreshold
    grind
  · exact bulkChannelErr_clamps_below_Mcrit
  · exact bulkChannelErr_improves_above_Mcrit

/-! ### Part 4: Headline Theorem 6 (Channel-Outlier Coupling Paradox) -/

theorem bulkChannelErr_sqHalf_sub_unscaled (qW qX M : Rat)
    (hqW : 0 < qW) (hqX : 0 < qX) (hM : 0 < M) :
    bulkChannelErr qW qX M M - bulkChannelErr qW qX M 1 =
      (M - 1) * (qX * qX - M * qW * qW) / (M * M * qW * qW * qX * qX) := by
  have h := bulkChannelErr_sub_unscaled qW qX M M hqW hqX hM hM
  rw [h]
  have hMne : M ≠ 0 := Rat.ne_of_gt hM
  have hden2_pos : 0 < M * M * qW * qW * qX * qX :=
    rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hM hM) hqW) hqW) hqX) hqX
  have hden1 : M * M * qW * qW * qX * qX * M ≠ 0 := Rat.ne_of_gt (rat_mul_pos hden2_pos hM)
  have hden2 : M * M * qW * qW * qX * qX ≠ 0 := Rat.ne_of_gt hden2_pos
  apply rat_div_eq_of_cross hden1 hden2
  grind

theorem bulkChannelErr_sqHalf_worse_iff (qW qX M : Rat)
    (hqW : 0 < qW) (hqX : 0 < qX) (hM : 1 < M) :
    bulkChannelErr qW qX M 1 < bulkChannelErr qW qX M M ↔
      M < criticalClampThreshold qW qX * criticalClampThreshold qW qX := by
  have hMpos : 0 < M := rat_lt_trans (by decide) hM
  have hMsub : 0 < M - 1 := rat_sub_pos hM
  have hqW2 : 0 < qW * qW := rat_mul_pos hqW hqW
  have hqX2 : 0 < qX * qX := rat_mul_pos hqX hqX
  have hden : 0 < M * M * qW * qW * qX * qX :=
    rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hMpos hMpos) hqW) hqW) hqX) hqX
  have hdiff := bulkChannelErr_sqHalf_sub_unscaled qW qX M hqW hqX hMpos
  have hmcrit_sq : criticalClampThreshold qW qX * criticalClampThreshold qW qX =
      (qX * qX) / (qW * qW) := by
    unfold criticalClampThreshold
    have hqWne : qW ≠ 0 := Rat.ne_of_gt hqW
    rw [eq_comm, rat_div_eq_iff (Rat.ne_of_gt hqW2)]
    calc qX * qX = ((qX / qW) * qW) * ((qX / qW) * qW) := by rw [rat_div_mul_cancel hqWne]
      _ = (qX / qW) * (qX / qW) * (qW * qW) := by grind
  rw [hmcrit_sq]
  constructor
  · intro hlt
    have hpos : 0 < (M - 1) * (qX * qX - M * qW * qW) / (M * M * qW * qW * qX * qX) := by
      rw [← hdiff]
      exact rat_sub_pos hlt
    have hnum_pos : 0 < (M - 1) * (qX * qX - M * qW * qW) := by
      have h1 := rat_mul_lt_mul_of_pos_right hpos hden
      rw [Rat.zero_mul, rat_div_mul_cancel (Rat.ne_of_gt hden)] at h1
      exact h1
    have hfac_pos : 0 < qX * qX - M * qW * qW := by
      apply rat_lt_of_mul_pos_right hMsub
      rw [Rat.zero_mul, Rat.mul_comm]
      exact hnum_pos
    apply rat_lt_div_of_mul_lt hqW2
    have h1 := rat_lt_of_sub_pos hfac_pos
    have heq : M * (qW * qW) = M * qW * qW := by grind
    rw [heq]
    exact h1
  · intro hlt
    have hMqW2 : M * qW * qW < qX * qX := by
      have h1 := rat_mul_lt_mul_of_pos_right hlt hqW2
      rw [rat_div_mul_cancel (Rat.ne_of_gt hqW2)] at h1
      have heq : M * (qW * qW) = M * qW * qW := by grind
      rw [← heq]
      exact h1
    apply rat_lt_of_sub_pos
    rw [hdiff]
    exact rat_div_pos (rat_mul_pos hMsub (rat_sub_pos hMqW2)) hden

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
  refine ⟨bulkChannelErr_sqHalf_sub_unscaled, bulkChannelErr_sqHalf_worse_iff, ?_, ?_⟩
  · intro qW qX M k b hqW hqX hM hb
    have hbpos : (0 : Rat) < (b : Rat) := rat_natCast_pos hb
    have hiff := bulkChannelErr_sqHalf_worse_iff qW qX M hqW hqX hM
    rw [← hiff]
    unfold totalCoupledErr
    constructor
    · intro hlt
      have hsub : 0 < (b : Rat) * (bulkChannelErr qW qX M M - bulkChannelErr qW qX M 1) := by
        have h := rat_sub_pos hlt
        have heq : (k : Rat) * outlierChannelErr qW qX + (b : Rat) * bulkChannelErr qW qX M M -
            ((k : Rat) * outlierChannelErr qW qX + (b : Rat) * bulkChannelErr qW qX M 1) =
            (b : Rat) * (bulkChannelErr qW qX M M - bulkChannelErr qW qX M 1) := by grind
        rw [← heq]
        exact h
      apply rat_lt_of_sub_pos
      apply rat_lt_of_mul_pos_right hbpos
      rw [Rat.zero_mul, Rat.mul_comm]
      exact hsub
    · intro hlt
      apply rat_lt_of_sub_pos
      have heq : (k : Rat) * outlierChannelErr qW qX + (b : Rat) * bulkChannelErr qW qX M M -
          ((k : Rat) * outlierChannelErr qW qX + (b : Rat) * bulkChannelErr qW qX M 1) =
          (b : Rat) * (bulkChannelErr qW qX M M - bulkChannelErr qW qX M 1) := by grind
      rw [heq]
      exact rat_mul_pos hbpos (rat_sub_pos hlt)
  · unfold criticalClampThreshold bulkChannelErr
    grind

end SmoothquantDyadic
