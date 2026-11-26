/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SmoothquantDyadic.RatOrder

/-!
# Zero-FLOP Dyadic Power-of-2 SmoothQuant Sharp Minimax Bounds

Proves:
- Theorem 2 (`dyadic_smoothquant_perchannel_l2_5_over_4_sharp`)
- Theorem 3 (`dyadic_smoothquant_perchannel_l1_9_over_8_sharp`)
- Theorem 4 (`dyadic_smoothquant_pertensor_5_2_vs_phase_shift_3_2`)
-/

namespace SmoothquantDyadic

/-! ### Part 1: Per-Channel `L_2^2` Sharp Bound (`5/4`) -/

theorem dyadicL2SqPenalty_gap (u : Rat) (hu : u ≠ 0) :
    (5 / 4 : Rat) - dyadicL2SqPenalty u = (2 - u) * (2 * u - 1) / (4 * u) := by
  unfold dyadicL2SqPenalty
  have h4u : 4 * u ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact (by decide : (4 : Rat) ≠ 0) h
    | inr h => exact hu h
  rw [eq_comm, rat_div_eq_iff h4u]
  have h1 : ((u + 1 / u) / 2) * (4 * u) = 2 * (u * u + 1) := by
    have hinv : (1 / u) * u = 1 := rat_div_mul_cancel hu
    have h2ne : (2 : Rat) ≠ 0 := by decide
    calc ((u + 1 / u) / 2) * (4 * u)
        = (((u + 1 / u) / 2) * 2) * (2 * u) := by grind
      _ = (u + 1 / u) * (2 * u) := by rw [rat_div_mul_cancel h2ne]
      _ = 2 * (u * u + (1 / u) * u) := by grind
      _ = 2 * (u * u + 1) := by rw [hinv]
  grind

theorem dyadicL2SqPenalty_le (u : Rat) (hlo : (1 / 2 : Rat) ≤ u) (hhi : u ≤ 2) :
    dyadicL2SqPenalty u ≤ 5 / 4 := by
  have hupos : 0 < u := rat_lt_of_lt_of_le (by grind) hlo
  apply rat_le_of_sub_nonneg
  rw [dyadicL2SqPenalty_gap u (Rat.ne_of_gt hupos)]
  have h1 : 0 ≤ 2 - u := rat_sub_nonneg hhi
  have h2 : 0 ≤ 2 * u - 1 := by
    have hm := rat_mul_le_mul_of_nonneg_left hlo (by decide : (0 : Rat) ≤ 2)
    have heq : (2 : Rat) * (1 / 2) = 1 := by grind
    rw [heq] at hm
    exact rat_sub_nonneg hm
  exact rat_div_nonneg (Rat.mul_nonneg h1 h2) (rat_mul_pos (by decide) hupos)

theorem bilinearErr_dyadic_ratio (A B s_opt s_dyad : Rat)
    (_hA : 0 < A) (hs_opt : 0 < s_opt) (hs_dyad : 0 < s_dyad)
    (hbal : A * (s_opt * s_opt) = B / (s_opt * s_opt)) :
    bilinearErr A B s_dyad =
      dyadicL2SqPenalty ((s_dyad / s_opt) * (s_dyad / s_opt)) * bilinearErr A B s_opt := by
  unfold bilinearErr dyadicL2SqPenalty
  have hs_opt_ne : s_opt ≠ 0 := Rat.ne_of_gt hs_opt
  have hs_opt2_ne : s_opt * s_opt ≠ 0 := Rat.ne_of_gt (rat_mul_pos hs_opt hs_opt)
  have hB : B = A * (s_opt * s_opt) * (s_opt * s_opt) := by
    have := (rat_div_eq_iff hs_opt2_ne).mp hbal.symm
    exact this
  have hopt_sum : A * (s_opt * s_opt) + B / (s_opt * s_opt) = 2 * (A * (s_opt * s_opt)) := by
    rw [← hbal]; grind
  rw [hopt_sum]
  let r : Rat := s_dyad / s_opt
  have hr_pos : 0 < r := rat_div_pos hs_dyad hs_opt
  have hu_ne : r * r ≠ 0 := Rat.ne_of_gt (rat_mul_pos hr_pos hr_pos)
  have hs_dyad_eq : s_dyad = r * s_opt := (rat_div_mul_cancel hs_opt_ne).symm
  have hs_dyad2_eq : s_dyad * s_dyad = (r * r) * (s_opt * s_opt) := by
    rw [hs_dyad_eq]; grind
  have hterm1 : A * (s_dyad * s_dyad) = (r * r) * (A * (s_opt * s_opt)) := by
    rw [hs_dyad2_eq]; grind
  have hterm2 : B / (s_dyad * s_dyad) = (1 / (r * r)) * (A * (s_opt * s_opt)) := by
    rw [hB, hs_dyad2_eq]
    have hden_ne : (r * r) * (s_opt * s_opt) ≠ 0 :=
      Rat.ne_of_gt (rat_mul_pos (rat_mul_pos hr_pos hr_pos) (rat_mul_pos hs_opt hs_opt))
    rw [rat_div_eq_iff hden_ne]
    calc A * (s_opt * s_opt) * (s_opt * s_opt)
        = 1 * (A * (s_opt * s_opt) * (s_opt * s_opt)) := by grind
      _ = ((1 / (r * r)) * (r * r)) * (A * (s_opt * s_opt) * (s_opt * s_opt)) := by
            rw [rat_div_mul_cancel hu_ne]
      _ = (1 / (r * r)) * (A * (s_opt * s_opt)) * (r * r * (s_opt * s_opt)) := by grind
  rw [hterm1, hterm2]
  have h2ne : (2 : Rat) ≠ 0 := by decide
  change (r * r) * (A * (s_opt * s_opt)) + (1 / (r * r)) * (A * (s_opt * s_opt)) =
    (r * r + 1 / (r * r)) / 2 * (2 * (A * (s_opt * s_opt)))
  calc (r * r) * (A * (s_opt * s_opt)) + (1 / (r * r)) * (A * (s_opt * s_opt))
      = (r * r + 1 / (r * r)) * (A * (s_opt * s_opt)) := by grind
    _ = (((r * r + 1 / (r * r)) / 2) * 2) * (A * (s_opt * s_opt)) := by
          rw [rat_div_mul_cancel h2ne]
    _ = (r * r + 1 / (r * r)) / 2 * (2 * (A * (s_opt * s_opt))) := by grind

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
  refine ⟨dyadicL2SqPenalty_gap, dyadicL2SqPenalty_le, ?_, ?_, ?_⟩
  · intro u hlo hhi
    have hupos : 0 < u := rat_lt_trans (by grind) hlo
    apply rat_lt_of_sub_pos
    rw [dyadicL2SqPenalty_gap u (Rat.ne_of_gt hupos)]
    have h1 : 0 < 2 - u := rat_sub_pos hhi
    have h2 : 0 < 2 * u - 1 := by
      have hm := rat_mul_lt_mul_of_pos_left hlo (by decide : (0 : Rat) < 2)
      have heq : (2 : Rat) * (1 / 2) = 1 := by grind
      rw [heq] at hm
      exact rat_sub_pos hm
    exact rat_div_pos (rat_mul_pos h1 h2) (rat_mul_pos (by decide) hupos)
  · intro A B s_opt s_dyad hA hB hs_opt hs_dyad hbal hlo hhi
    rw [bilinearErr_dyadic_ratio A B s_opt s_dyad hA hs_opt hs_dyad hbal]
    have hpen := dyadicL2SqPenalty_le ((s_dyad / s_opt) * (s_dyad / s_opt)) hlo hhi
    have hopt_nonneg : 0 ≤ bilinearErr A B s_opt := by
      unfold bilinearErr
      have hs2 : 0 < s_opt * s_opt := rat_mul_pos hs_opt hs_opt
      exact rat_add_nonneg (Rat.le_of_lt (rat_mul_pos hA hs2)) (Rat.le_of_lt (rat_div_pos hB hs2))
    exact rat_mul_le_mul_of_nonneg_right hpen hopt_nonneg
  · unfold dyadicL2SqPenalty
    grind

/-! ### Part 2: Per-Channel Squared `L_1` Sharp Bound (`9/8`) -/

theorem dyadicL1SqPenalty_gap (u : Rat) (hu : u ≠ 0) :
    (9 / 8 : Rat) - dyadicL1SqPenalty u = (2 - u) * (2 * u - 1) / (8 * u) := by
  unfold dyadicL1SqPenalty
  have h8u : 8 * u ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact (by decide : (8 : Rat) ≠ 0) h
    | inr h => exact hu h
  rw [eq_comm, rat_div_eq_iff h8u]
  have h1 : ((u + 2 + 1 / u) / 4) * (8 * u) = 2 * (u * u + 2 * u + 1) := by
    have hinv : (1 / u) * u = 1 := rat_div_mul_cancel hu
    have h4ne : (4 : Rat) ≠ 0 := by decide
    calc ((u + 2 + 1 / u) / 4) * (8 * u)
        = (((u + 2 + 1 / u) / 4) * 4) * (2 * u) := by grind
      _ = (u + 2 + 1 / u) * (2 * u) := by rw [rat_div_mul_cancel h4ne]
      _ = 2 * (u * u + 2 * u + (1 / u) * u) := by grind
      _ = 2 * (u * u + 2 * u + 1) := by rw [hinv]
  grind

theorem dyadicL1SqPenalty_le (u : Rat) (hlo : (1 / 2 : Rat) ≤ u) (hhi : u ≤ 2) :
    dyadicL1SqPenalty u ≤ 9 / 8 := by
  have hupos : 0 < u := rat_lt_of_lt_of_le (by grind) hlo
  apply rat_le_of_sub_nonneg
  rw [dyadicL1SqPenalty_gap u (Rat.ne_of_gt hupos)]
  have h1 : 0 ≤ 2 - u := rat_sub_nonneg hhi
  have h2 : 0 ≤ 2 * u - 1 := by
    have hm := rat_mul_le_mul_of_nonneg_left hlo (by decide : (0 : Rat) ≤ 2)
    have heq : (2 : Rat) * (1 / 2) = 1 := by grind
    rw [heq] at hm
    exact rat_sub_nonneg hm
  exact rat_div_nonneg (Rat.mul_nonneg h1 h2) (rat_mul_pos (by decide) hupos)

theorem dyadicL1Sq_eq_sq (r : Rat) (hr : r ≠ 0) :
    ((r + 1 / r) / 2) * ((r + 1 / r) / 2) = dyadicL1SqPenalty (r * r) := by
  unfold dyadicL1SqPenalty
  have hr2 : r * r ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero hr)
  have h1 : r * (1 / r) = 1 := rat_mul_div_cancel hr
  have h2 : (1 / r) * (1 / r) = 1 / (r * r) := by
    rw [eq_comm, rat_div_eq_iff hr2]
    calc (1 : Rat) = 1 * 1 := by grind
      _ = ((1 / r) * r) * ((1 / r) * r) := by rw [rat_div_mul_cancel hr]
      _ = (1 / r) * (1 / r) * (r * r) := by grind
  have h4ne : (4 : Rat) ≠ 0 := by decide
  have h2ne : (2 : Rat) ≠ 0 := by decide
  rw [eq_comm, rat_div_eq_iff h4ne]
  calc r * r + 2 + 1 / (r * r)
      = r * r + 2 * (r * (1 / r)) + (1 / r) * (1 / r) := by rw [h1, h2]; grind
    _ = (r + 1 / r) * (r + 1 / r) := by grind
    _ = (((r + 1 / r) / 2) * 2) * (((r + 1 / r) / 2) * 2) := by rw [rat_div_mul_cancel h2ne]
    _ = ((r + 1 / r) / 2) * ((r + 1 / r) / 2) * 4 := by grind

theorem bilinearL1Err_dyadic_sq_ratio (A B s_opt s_dyad : Rat)
    (hs_opt : 0 < s_opt) (hs_dyad : 0 < s_dyad)
    (hbal : A * s_opt = B / s_opt) :
    bilinearL1Err A B s_dyad * bilinearL1Err A B s_dyad =
      dyadicL1SqPenalty ((s_dyad / s_opt) * (s_dyad / s_opt)) *
        (bilinearL1Err A B s_opt * bilinearL1Err A B s_opt) := by
  unfold bilinearL1Err
  have hs_opt_ne : s_opt ≠ 0 := Rat.ne_of_gt hs_opt
  let r : Rat := s_dyad / s_opt
  have hr_ne : r ≠ 0 := Rat.ne_of_gt (rat_div_pos hs_dyad hs_opt)
  have hs_dyad_eq : s_dyad = r * s_opt := (rat_div_mul_cancel hs_opt_ne).symm
  have hB : B = A * s_opt * s_opt := (rat_div_eq_iff hs_opt_ne).mp hbal.symm
  have hlin : A * s_dyad + B / s_dyad = ((r + 1 / r) / 2) * (A * s_opt + B / s_opt) := by
    have hopt_sum : A * s_opt + B / s_opt = 2 * (A * s_opt) := by rw [← hbal]; grind
    rw [hopt_sum, hs_dyad_eq, hB]
    have hterm2 : A * s_opt * s_opt / (r * s_opt) = (1 / r) * (A * s_opt) := by
      have hrs_ne : r * s_opt ≠ 0 := Rat.ne_of_gt (rat_mul_pos (rat_div_pos hs_dyad hs_opt) hs_opt)
      rw [rat_div_eq_iff hrs_ne]
      calc A * s_opt * s_opt = 1 * (A * s_opt * s_opt) := by grind
        _ = ((1 / r) * r) * (A * s_opt * s_opt) := by rw [rat_div_mul_cancel hr_ne]
        _ = (1 / r) * (A * s_opt) * (r * s_opt) := by grind
    rw [hterm2]
    have h2ne : (2 : Rat) ≠ 0 := by decide
    calc A * (r * s_opt) + (1 / r) * (A * s_opt)
        = (r + 1 / r) * (A * s_opt) := by grind
      _ = (((r + 1 / r) / 2) * 2) * (A * s_opt) := by rw [rat_div_mul_cancel h2ne]
      _ = (r + 1 / r) / 2 * (2 * (A * s_opt)) := by grind
  rw [hlin]
  change ((r + 1 / r) / 2 * (A * s_opt + B / s_opt)) * ((r + 1 / r) / 2 * (A * s_opt + B / s_opt)) =
    dyadicL1SqPenalty (r * r) * ((A * s_opt + B / s_opt) * (A * s_opt + B / s_opt))
  rw [← dyadicL1Sq_eq_sq r hr_ne]
  grind

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
  refine ⟨dyadicL1SqPenalty_gap, dyadicL1SqPenalty_le, ?_, ?_, ?_⟩
  · intro r hr hlo hhi
    rw [dyadicL1Sq_eq_sq r (Rat.ne_of_gt hr)]
    exact dyadicL1SqPenalty_le (r * r) hlo hhi
  · intro A B s_opt s_dyad _hA _hB hs_opt hs_dyad hbal hlo hhi
    rw [bilinearL1Err_dyadic_sq_ratio A B s_opt s_dyad hs_opt hs_dyad hbal]
    have hpen := dyadicL1SqPenalty_le ((s_dyad / s_opt) * (s_dyad / s_opt)) hlo hhi
    exact rat_mul_le_mul_of_nonneg_right hpen (rat_sq_nonneg _)
  · unfold dyadicL1SqPenalty
    grind

/-! ### Part 3: Per-Tensor Coupled `5/2` vs Global Phase-Shifted `3/2` Sharp Bounds -/

theorem perTensorCoupledChannelPenalty_le_naive (mwSq mxSq u : Rat)
    (hlo : (1 / 2 : Rat) ≤ u) (hhi : u ≤ 2) (hmw : mwSq ≤ 2) (hmx : mxSq ≤ 2) :
    perTensorCoupledChannelPenalty mwSq mxSq u ≤ 5 / 2 := by
  unfold perTensorCoupledChannelPenalty
  have hupos : 0 < u := rat_lt_of_lt_of_le (by grind) hlo
  have h1 : mwSq / u ≤ 2 / u := by
    rw [Rat.div_def, Rat.div_def]
    exact rat_mul_le_mul_of_nonneg_right hmw (Rat.le_of_lt (rat_inv_pos hupos))
  have h2 : mxSq * u ≤ 2 * u := rat_mul_le_mul_of_nonneg_right hmx (Rat.le_of_lt hupos)
  have hsum : mwSq / u + mxSq * u ≤ 2 / u + 2 * u := rat_add_le_add h1 h2
  have havg : (mwSq / u + mxSq * u) / 2 ≤ (2 / u + 2 * u) / 2 := by
    rw [Rat.div_def, Rat.div_def]
    exact rat_mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt (rat_inv_pos (by decide)))
  have hpen : (2 / u + 2 * u) / 2 = 2 * dyadicL2SqPenalty u := by
    unfold dyadicL2SqPenalty
    have h2u : 2 / u = 2 * (1 / u) := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [h2u]
    rw [Rat.div_def, Rat.div_def]
    grind
  rw [hpen] at havg
  have h54 := dyadicL2SqPenalty_le u hlo hhi
  have h52 := rat_mul_le_mul_of_nonneg_left h54 (by decide : (0 : Rat) ≤ 2)
  have heq : (2 : Rat) * (5 / 4) = 5 / 2 := by grind
  rw [heq] at h52
  exact Rat.le_trans havg h52

theorem perTensorCoupledD2Penalty_closed_form (u1 u2 : Rat)
    (hu1 : 0 < u1) (hu2 : 0 < u2) :
    perTensorCoupledD2Penalty u1 u2 = (1 + ratMax (u2 / u1) (u1 / u2)) / 2 := by
  unfold perTensorCoupledD2Penalty perTensorCoupledChannelPenalty
  have hu1ne : u1 ≠ 0 := Rat.ne_of_gt hu1
  have hu2ne : u2 ≠ 0 := Rat.ne_of_gt hu2
  cases Rat.le_total (a := u1) (b := u2) with
  | inl h12 =>
    have hmw : ratMax u1 u2 = u2 := ratMax_eq_right h12
    have hinv : 1 / u2 ≤ 1 / u1 := by
      apply rat_div_le_div_of_cross hu2 hu1
      rw [Rat.one_mul, Rat.one_mul]
      exact h12
    have hmx : ratMax (1 / u1) (1 / u2) = 1 / u1 := ratMax_eq_left hinv
    have hrat : u1 / u2 ≤ u2 / u1 := by
      apply rat_div_le_div_of_cross hu2 hu1
      have h1 := rat_mul_le_mul_of_nonneg_left h12 (Rat.le_of_lt hu1)
      have h2 := rat_mul_le_mul_of_nonneg_right h12 (Rat.le_of_lt hu2)
      exact Rat.le_trans h1 h2
    have hrmax : ratMax (u2 / u1) (u1 / u2) = u2 / u1 := ratMax_eq_left hrat
    rw [hmw, hmx, hrmax]
    dsimp only []
    have ha : (1 / u1) * u1 = 1 := rat_div_mul_cancel hu1ne
    have hb : u2 / u2 = 1 := by rw [rat_div_eq_iff hu2ne, Rat.one_mul]
    have hc : (1 / u1) * u2 = u2 / u1 := by rw [Rat.div_def, Rat.div_def]; grind
    rw [ha, hb, hc]
    grind
  | inr h21 =>
    have hmw : ratMax u1 u2 = u1 := ratMax_eq_left h21
    have hinv : 1 / u1 ≤ 1 / u2 := by
      apply rat_div_le_div_of_cross hu1 hu2
      rw [Rat.one_mul, Rat.one_mul]
      exact h21
    have hmx : ratMax (1 / u1) (1 / u2) = 1 / u2 := ratMax_eq_right hinv
    have hrat : u2 / u1 ≤ u1 / u2 := by
      apply rat_div_le_div_of_cross hu1 hu2
      have h1 := rat_mul_le_mul_of_nonneg_left h21 (Rat.le_of_lt hu2)
      have h2 := rat_mul_le_mul_of_nonneg_right h21 (Rat.le_of_lt hu1)
      exact Rat.le_trans h1 h2
    have hrmax : ratMax (u2 / u1) (u1 / u2) = u1 / u2 := ratMax_eq_right hrat
    rw [hmw, hmx, hrmax]
    dsimp only []
    have ha : u1 / u1 = 1 := by rw [rat_div_eq_iff hu1ne, Rat.one_mul]
    have hb : (1 / u2) * u2 = 1 := rat_div_mul_cancel hu2ne
    have hc : (1 / u2) * u1 = u1 / u2 := by rw [Rat.div_def, Rat.div_def]; grind
    rw [ha, hb, hc]
    grind

theorem perTensorCoupledD2Penalty_naive_le (u1 u2 : Rat)
    (h1lo : (1 / 2 : Rat) ≤ u1) (h1hi : u1 ≤ 2)
    (h2lo : (1 / 2 : Rat) ≤ u2) (h2hi : u2 ≤ 2) :
    perTensorCoupledD2Penalty u1 u2 ≤ 5 / 2 := by
  have hu1 : 0 < u1 := rat_lt_of_lt_of_le (by grind) h1lo
  have hu2 : 0 < u2 := rat_lt_of_lt_of_le (by grind) h2lo
  rw [perTensorCoupledD2Penalty_closed_form u1 u2 hu1 hu2]
  have hr1 : u2 / u1 ≤ 4 := by
    apply rat_div_le_of_mul_le hu1
    have hm := rat_mul_le_mul_of_nonneg_left h1lo (by decide : (0 : Rat) ≤ 4)
    have heq : (4 : Rat) * (1 / 2) = 2 := by grind
    rw [heq] at hm
    exact Rat.le_trans h2hi hm
  have hr2 : u1 / u2 ≤ 4 := by
    apply rat_div_le_of_mul_le hu2
    have hm := rat_mul_le_mul_of_nonneg_left h2lo (by decide : (0 : Rat) ≤ 4)
    have heq : (4 : Rat) * (1 / 2) = 2 := by grind
    rw [heq] at hm
    exact Rat.le_trans h1hi hm
  have hmax : ratMax (u2 / u1) (u1 / u2) ≤ 4 := by
    unfold ratMax
    split
    · exact hr2
    · exact hr1
  have hsum := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hmax
  have hdiv : (1 + ratMax (u2 / u1) (u1 / u2)) / 2 ≤ (1 + 4) / 2 := by
    rw [Rat.div_def, Rat.div_def]
    exact rat_mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt (rat_inv_pos (by decide)))
  have heq : ((1 : Rat) + 4) / 2 = 5 / 2 := by grind
  rw [heq] at hdiv
  exact hdiv

theorem perTensorCoupledD2Penalty_phase_shifted_le (u2 : Rat)
    (hlo : (1 / 2 : Rat) ≤ u2) (hhi : u2 ≤ 2) :
    perTensorCoupledD2Penalty 1 u2 ≤ 3 / 2 := by
  have hu2 : 0 < u2 := rat_lt_of_lt_of_le (by grind) hlo
  rw [perTensorCoupledD2Penalty_closed_form 1 u2 (by decide) hu2]
  have h1 : u2 / 1 = u2 := by rw [rat_div_eq_iff (by decide), Rat.mul_one]
  rw [h1]
  have hinv : 1 / u2 ≤ 2 := by
    apply rat_div_le_of_mul_le hu2
    have hm := rat_mul_le_mul_of_nonneg_left hlo (by decide : (0 : Rat) ≤ 2)
    have heq : (2 : Rat) * (1 / 2) = 1 := by grind
    rw [heq] at hm
    exact hm
  have hmax : ratMax u2 (1 / u2) ≤ 2 := by
    unfold ratMax
    split
    · exact hinv
    · exact hhi
  have hsum := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hmax
  have hdiv : (1 + ratMax u2 (1 / u2)) / 2 ≤ (1 + 2) / 2 := by
    rw [Rat.div_def, Rat.div_def]
    exact rat_mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt (rat_inv_pos (by decide)))
  have heq : ((1 : Rat) + 2) / 2 = 3 / 2 := by grind
  rw [heq] at hdiv
  exact hdiv

theorem perTensorCoupledD2Penalty_phase_shifted_lower_bound (e1 e2 : Int) (lamSq : Rat)
    (hlam : 0 < lamSq) :
    let u1 := pow2IntRat (2 * e1) / lamSq
    let u2 := pow2IntRat (2 * e2 - 1) / lamSq
    (3 / 2 : Rat) ≤ perTensorCoupledD2Penalty u1 u2 := by
  intro u1 u2
  have hu1 : 0 < u1 := rat_div_pos (pow2IntRat_pos _) hlam
  have hu2 : 0 < u2 := rat_div_pos (pow2IntRat_pos _) hlam
  rw [perTensorCoupledD2Penalty_closed_form u1 u2 hu1 hu2]
  have hlam_ne : lamSq ≠ 0 := Rat.ne_of_gt hlam
  have hrat_eq : u2 / u1 = pow2IntRat (2 * e2 - 1) / pow2IntRat (2 * e1) := by
    apply rat_div_eq_of_cross (Rat.ne_of_gt hu1) (Rat.ne_of_gt (pow2IntRat_pos _))
    have hmul : (pow2IntRat (2 * e2 - 1) / lamSq * pow2IntRat (2 * e1) -
        pow2IntRat (2 * e2 - 1) * (pow2IntRat (2 * e1) / lamSq)) * lamSq = 0 := by
      have ha : (pow2IntRat (2 * e2 - 1) / lamSq) * lamSq = pow2IntRat (2 * e2 - 1) :=
        rat_div_mul_cancel hlam_ne
      have hb : (pow2IntRat (2 * e1) / lamSq) * lamSq = pow2IntRat (2 * e1) :=
        rat_div_mul_cancel hlam_ne
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h => grind
    | inr h => exact False.elim (hlam_ne h)
  have hpow_div : ∀ a b : Int, pow2IntRat a / pow2IntRat b = pow2IntRat (a - b) := by
    intro a b
    -- Prove via pow2IntRat_add: pow2IntRat (a - b) * pow2IntRat b = pow2IntRat a
    have hadd : ∀ x y : Int, pow2IntRat x * pow2IntRat y = pow2IntRat (x + y) := by
      intro x y
      cases x with
      | ofNat m =>
        cases y with
        | ofNat n =>
          have hxy : Int.ofNat m + Int.ofNat n = Int.ofNat (m + n) := rfl
          rw [hxy]
          simp only [pow2IntRat]
          rw [Nat.pow_add, Rat.natCast_mul]
        | negSucc n =>
          by_cases hmn : m ≥ n + 1
          · have hsub : Int.ofNat m + Int.negSucc n = Int.ofNat (m - (n + 1)) := by
              change (m : Int) + (-(n + 1 : Int)) = ((m - (n + 1) : Nat) : Int)
              omega
            rw [hsub]
            simp only [pow2IntRat]
            have hpow : (2 ^ m : Nat) = 2 ^ (m - (n + 1)) * 2 ^ (n + 1) := by
              rw [← Nat.pow_add, Nat.sub_add_cancel hmn]
            have hp : ((2 ^ (n + 1) : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
            calc ((2 ^ m : Nat) : Rat) * (1 / ((2 ^ (n + 1) : Nat) : Rat))
                = (((2 ^ (m - (n + 1)) : Nat) : Rat) * ((2 ^ (n + 1) : Nat) : Rat)) *
                    (1 / ((2 ^ (n + 1) : Nat) : Rat)) := by rw [hpow, Rat.natCast_mul]
              _ = ((2 ^ (m - (n + 1)) : Nat) : Rat) *
                    (((2 ^ (n + 1) : Nat) : Rat) * (1 / ((2 ^ (n + 1) : Nat) : Rat))) := by grind
              _ = ((2 ^ (m - (n + 1)) : Nat) : Rat) * 1 := by rw [rat_mul_div_cancel hp]
              _ = ((2 ^ (m - (n + 1)) : Nat) : Rat) := Rat.mul_one _
          · have hsub : Int.ofNat m + Int.negSucc n = Int.negSucc (n - m) := by
              change (m : Int) + (-(n + 1 : Int)) = -(((n - m : Nat) + 1 : Int))
              omega
            rw [hsub]
            simp only [pow2IntRat]
            have hpow : (2 ^ (n + 1) : Nat) = 2 ^ m * 2 ^ (n - m + 1) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            have hp1 : ((2 ^ (n + 1) : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
            have hp2 : ((2 ^ (n - m + 1) : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
            have hmul_eq : ((2 ^ m : Nat) : Rat) * (1 / ((2 ^ (n + 1) : Nat) : Rat)) =
                ((2 ^ m : Nat) : Rat) / ((2 ^ (n + 1) : Nat) : Rat) := by
              rw [Rat.div_def, Rat.div_def]; grind
            rw [hmul_eq]
            apply rat_div_eq_of_cross hp1 hp2
            rw [hpow, Rat.natCast_mul]; grind
      | negSucc m =>
        cases y with
        | ofNat n =>
          have hcomm : Int.negSucc m + Int.ofNat n = Int.ofNat n + Int.negSucc m := Int.add_comm _ _
          rw [hcomm, Rat.mul_comm]
          by_cases hnm : n ≥ m + 1
          · have hsub : Int.ofNat n + Int.negSucc m = Int.ofNat (n - (m + 1)) := by
              change (n : Int) + (-(m + 1 : Int)) = ((n - (m + 1) : Nat) : Int)
              omega
            rw [hsub]
            simp only [pow2IntRat]
            have hpow : (2 ^ n : Nat) = 2 ^ (n - (m + 1)) * 2 ^ (m + 1) := by
              rw [← Nat.pow_add, Nat.sub_add_cancel hnm]
            have hp : ((2 ^ (m + 1) : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
            calc ((2 ^ n : Nat) : Rat) * (1 / ((2 ^ (m + 1) : Nat) : Rat))
                = (((2 ^ (n - (m + 1)) : Nat) : Rat) * ((2 ^ (m + 1) : Nat) : Rat)) *
                    (1 / ((2 ^ (m + 1) : Nat) : Rat)) := by rw [hpow, Rat.natCast_mul]
              _ = ((2 ^ (n - (m + 1)) : Nat) : Rat) *
                    (((2 ^ (m + 1) : Nat) : Rat) * (1 / ((2 ^ (m + 1) : Nat) : Rat))) := by grind
              _ = ((2 ^ (n - (m + 1)) : Nat) : Rat) * 1 := by rw [rat_mul_div_cancel hp]
              _ = ((2 ^ (n - (m + 1)) : Nat) : Rat) := Rat.mul_one _
          · have hsub : Int.ofNat n + Int.negSucc m = Int.negSucc (m - n) := by
              change (n : Int) + (-(m + 1 : Int)) = -(((m - n : Nat) + 1 : Int))
              omega
            rw [hsub]
            simp only [pow2IntRat]
            have hpow : (2 ^ (m + 1) : Nat) = 2 ^ n * 2 ^ (m - n + 1) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            have hp1 : ((2 ^ (m + 1) : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
            have hp2 : ((2 ^ (m - n + 1) : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
            have hmul_eq : ((2 ^ n : Nat) : Rat) * (1 / ((2 ^ (m + 1) : Nat) : Rat)) =
                ((2 ^ n : Nat) : Rat) / ((2 ^ (m + 1) : Nat) : Rat) := by
              rw [Rat.div_def, Rat.div_def]; grind
            rw [hmul_eq]
            apply rat_div_eq_of_cross hp1 hp2
            rw [hpow, Rat.natCast_mul]; grind
        | negSucc n =>
          have hsub : Int.negSucc m + Int.negSucc n = Int.negSucc (m + n + 1) := by
            change (-(m + 1 : Int)) + (-(n + 1 : Int)) = -(((m + n + 1 : Nat) + 1 : Int))
            omega
          rw [hsub]
          simp only [pow2IntRat]
          have hpow : (2 ^ (m + n + 1 + 1) : Nat) = 2 ^ (m + 1) * 2 ^ (n + 1) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          have hp1 : ((2 ^ (m + 1) : Nat) : Rat) ≠ 0 :=
            Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
          have hp2 : ((2 ^ (n + 1) : Nat) : Rat) ≠ 0 :=
            Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
          have hp12 : ((2 ^ (m + n + 1 + 1) : Nat) : Rat) ≠ 0 :=
            Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
          rw [eq_comm, rat_div_eq_iff hp12]
          rw [hpow, Rat.natCast_mul]
          calc (1 : Rat) = 1 * 1 := by grind
            _ = ((1 / ((2 ^ (m + 1) : Nat) : Rat)) * ((2 ^ (m + 1) : Nat) : Rat)) *
                ((1 / ((2 ^ (n + 1) : Nat) : Rat)) * ((2 ^ (n + 1) : Nat) : Rat)) := by
                  rw [rat_div_mul_cancel hp1, rat_div_mul_cancel hp2]
            _ = (1 / ((2 ^ (m + 1) : Nat) : Rat)) * (1 / ((2 ^ (n + 1) : Nat) : Rat)) *
                (((2 ^ (m + 1) : Nat) : Rat) * ((2 ^ (n + 1) : Nat) : Rat)) := by grind
    rw [rat_div_eq_iff (Rat.ne_of_gt (pow2IntRat_pos b))]
    rw [hadd (a - b) b]
    have hab : a - b + b = a := by omega
    rw [hab]
  have hu2u1 : u2 / u1 = pow2IntRat (2 * (e2 - e1) - 1) := by
    rw [hrat_eq, hpow_div]
    congr 1
    omega
  have hu1u2 : u1 / u2 = pow2IntRat (1 - 2 * (e2 - e1)) := by
    have hinv : u1 / u2 = 1 / (u2 / u1) := by
      apply rat_div_eq_of_cross (Rat.ne_of_gt hu2) (Rat.ne_of_gt (rat_div_pos hu2 hu1))
      rw [Rat.one_mul, rat_mul_div_cancel (Rat.ne_of_gt hu1)]
    rw [hinv, hu2u1, pow2IntRat_inv]
    congr 1
    omega
  have hmax_ge_2 : (2 : Rat) ≤ ratMax (u2 / u1) (u1 / u2) := by
    rw [hu2u1, hu1u2]
    by_cases hpos : 1 ≤ 2 * (e2 - e1) - 1
    · exact Rat.le_trans (pow2IntRat_ge_two_of_pos hpos) (rat_le_ratMax_left _ _)
    · have hneg : 1 ≤ 1 - 2 * (e2 - e1) := by omega
      exact Rat.le_trans (pow2IntRat_ge_two_of_pos hneg) (rat_le_ratMax_right _ _)
  have hsum := rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hmax_ge_2
  have hdiv : ((1 : Rat) + 2) / 2 ≤ (1 + ratMax (u2 / u1) (u1 / u2)) / 2 := by
    rw [Rat.div_def, Rat.div_def]
    exact rat_mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt (rat_inv_pos (by decide)))
  have heq : ((1 : Rat) + 2) / 2 = 3 / 2 := by grind
  rw [heq] at hdiv
  exact hdiv

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
  refine ⟨perTensorCoupledChannelPenalty_le_naive,
          perTensorCoupledD2Penalty_naive_le,
          ?_,
          perTensorCoupledD2Penalty_closed_form,
          perTensorCoupledD2Penalty_phase_shifted_le,
          ?_,
          perTensorCoupledD2Penalty_phase_shifted_lower_bound⟩
  · unfold perTensorCoupledD2Penalty perTensorCoupledChannelPenalty ratMax
    grind
  · unfold perTensorCoupledD2Penalty perTensorCoupledChannelPenalty ratMax
    grind

end SmoothquantDyadic
