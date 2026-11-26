/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CeLseHorizon.RatOrder

/-!
# Cross-Entropy Conservation & FP8-E4M3 / FP8-E5M2 Dual-Horizon Collapse Laws

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `ce_gradient_zero_sum_conservation_exact`
2. `fp8_e4m3_dual_horizon_and_rne_overshoot_cliff`
3. `fp8_e5m2_128k_vocab_conservation_collapse`
-/

namespace CeLseHorizon

/-! ### Helper Lemmas for Cross-Entropy Conservation -/

theorem ceGrad_sum_zero {V : Nat} (p : Fin V → Rat) (y : Fin V) (hp : finSum p = 1) :
    finSum (ceGrad p y) = 0 := by
  unfold ceGrad
  rw [finSum_sub, finSum_single, hp]
  grind

theorem ceGrad_nonTarget_sum {V : Nat} (p : Fin V → Rat) (y : Fin V) (hp : finSum p = 1) :
    finSumExcept y p = 1 - p y := by
  have hsplit := finSum_split_at y p
  rw [hp] at hsplit
  grind

theorem ceGrad_nonTarget_cancels_target {V : Nat} (p : Fin V → Rat) (y : Fin V) (hp : finSum p = 1) :
    finSumExcept y (ceGrad p y) = -ceGrad p y y := by
  have hsplit := finSum_split_at y (ceGrad p y)
  rw [ceGrad_sum_zero p y hp] at hsplit
  grind

theorem uniformProb_sum {V : Nat} (y : Fin V) : finSum (uniformProb V) = 1 := by
  unfold uniformProb
  rw [finSum_const]
  have hVpos : 0 < V := Nat.lt_of_le_of_lt (Nat.zero_le y.val) y.isLt
  have hVne : (V : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hVpos)
  exact rat_mul_div_cancel hVne

theorem uniformProb_target_grad {V : Nat} (y : Fin V) :
    ceGrad (uniformProb V) y y = -(((V - 1 : Nat) : Rat) / (V : Rat)) := by
  unfold ceGrad uniformProb
  simp only [ite_true]
  have hVpos : 0 < V := Nat.lt_of_le_of_lt (Nat.zero_le y.val) y.isLt
  have hVne : (V : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hVpos)
  have hn : V = (V - 1) + 1 := by omega
  have hcast : (V : Rat) = ((V - 1 : Nat) : Rat) + 1 := by
    have h1 : (V : Rat) = (((V - 1) + 1 : Nat) : Rat) := congrArg (fun k : Nat => (k : Rat)) hn
    rw [h1, Rat.natCast_add]
    rfl
  have hmul : ((1 : Rat) / (V : Rat) - 1) * (V : Rat) =
      (-(((V - 1 : Nat) : Rat) / (V : Rat))) * (V : Rat) := by
    have h1 : ((1 : Rat) / (V : Rat) - 1) * (V : Rat) =
        ((1 : Rat) / (V : Rat)) * (V : Rat) - (V : Rat) := by grind
    have h2 : (-(((V - 1 : Nat) : Rat) / (V : Rat))) * (V : Rat) =
        -((((V - 1 : Nat) : Rat) / (V : Rat)) * (V : Rat)) := by grind
    rw [h1, h2, rat_div_mul_cancel hVne, rat_div_mul_cancel hVne, hcast]
    grind
  have hdiff : (((1 : Rat) / (V : Rat) - 1) - (-(((V - 1 : Nat) : Rat) / (V : Rat)))) * (V : Rat) = 0 := by
    grind
  cases Rat.mul_eq_zero.mp hdiff with
  | inl h => grind
  | inr h => exact absurd h hVne

theorem uniformProb_nonTarget_sum {V : Nat} (y : Fin V) :
    finSumExcept y (uniformProb V) = ((V - 1 : Nat) : Rat) / (V : Rat) := by
  rw [ceGrad_nonTarget_sum (uniformProb V) y (uniformProb_sum y)]
  have ht := uniformProb_target_grad y
  unfold ceGrad at ht
  simp only [ite_true] at ht
  grind

/-! ### Theorem 1 -/

theorem ce_gradient_zero_sum_conservation_exact :
    (∀ (V : Nat) (p : Fin V → Rat) (y : Fin V), finSum p = 1 →
      finSum (ceGrad p y) = 0) ∧
    (∀ (V : Nat) (p : Fin V → Rat) (y : Fin V), finSum p = 1 →
      finSumExcept y p = 1 - p y) ∧
    (∀ (V : Nat) (p : Fin V → Rat) (y : Fin V), finSum p = 1 →
      finSumExcept y (ceGrad p y) = -ceGrad p y y) ∧
    (∀ (V : Nat) (y : Fin V),
      finSum (uniformProb V) = 1 ∧
      finSum (ceGrad (uniformProb V) y) = 0 ∧
      finSumExcept y (uniformProb V) = ((V - 1 : Nat) : Rat) / (V : Rat) ∧
      ceGrad (uniformProb V) y y = -(((V - 1 : Nat) : Rat) / (V : Rat))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V p y hp; exact ceGrad_sum_zero p y hp
  · intro V p y hp; exact ceGrad_nonTarget_sum p y hp
  · intro V p y hp; exact ceGrad_nonTarget_cancels_target p y hp
  · intro V y
    exact ⟨uniformProb_sum y, ceGrad_sum_zero _ y (uniformProb_sum y),
      uniformProb_nonTarget_sum y, uniformProb_target_grad y⟩

/-! ### Generic Exact Reciprocal Comparisons & Target Rounding Helpers -/

theorem inv_nat_lt_inv_nat_iff {V N : Nat} (hV : 0 < V) (hN : 0 < N) :
    ((1 : Rat) / (V : Rat) < (1 : Rat) / (N : Rat)) ↔ N < V := by
  have hVp : (0 : Rat) < (V : Rat) := rat_natCast_pos hV
  have hNp : (0 : Rat) < (N : Rat) := rat_natCast_pos hN
  have hVne : (V : Rat) ≠ 0 := Rat.ne_of_gt hVp
  have hNne : (N : Rat) ≠ 0 := Rat.ne_of_gt hNp
  constructor
  · intro h
    have h1 : ((1 : Rat) / (V : Rat)) * ((V : Rat) * (N : Rat)) <
        ((1 : Rat) / (N : Rat)) * ((V : Rat) * (N : Rat)) :=
      rat_mul_lt_mul_of_pos_right h (rat_mul_pos hVp hNp)
    have lhs : ((1 : Rat) / (V : Rat)) * ((V : Rat) * (N : Rat)) = (N : Rat) := by
      have eq1 : ((1 : Rat) / (V : Rat)) * ((V : Rat) * (N : Rat)) =
          (((1 : Rat) / (V : Rat)) * (V : Rat)) * (N : Rat) := by grind
      rw [eq1, rat_div_mul_cancel hVne, Rat.one_mul]
    have rhs : ((1 : Rat) / (N : Rat)) * ((V : Rat) * (N : Rat)) = (V : Rat) := by
      have eq2 : ((1 : Rat) / (N : Rat)) * ((V : Rat) * (N : Rat)) =
          (((1 : Rat) / (N : Rat)) * (N : Rat)) * (V : Rat) := by grind
      rw [eq2, rat_div_mul_cancel hNne, Rat.one_mul]
    rw [lhs, rhs] at h1
    exact rat_natCast_lt_iff.mp h1
  · intro h
    have hlt : (N : Rat) < (V : Rat) := rat_natCast_lt h
    apply rat_lt_of_mul_pos_right (rat_mul_pos hVp hNp)
    have lhs : ((1 : Rat) / (V : Rat)) * ((V : Rat) * (N : Rat)) = (N : Rat) := by
      have eq1 : ((1 : Rat) / (V : Rat)) * ((V : Rat) * (N : Rat)) =
          (((1 : Rat) / (V : Rat)) * (V : Rat)) * (N : Rat) := by grind
      rw [eq1, rat_div_mul_cancel hVne, Rat.one_mul]
    have rhs : ((1 : Rat) / (N : Rat)) * ((V : Rat) * (N : Rat)) = (V : Rat) := by
      have eq2 : ((1 : Rat) / (N : Rat)) * ((V : Rat) * (N : Rat)) =
          (((1 : Rat) / (N : Rat)) * (N : Rat)) * (V : Rat) := by grind
      rw [eq2, rat_div_mul_cancel hNne, Rat.one_mul]
    rw [lhs, rhs]
    exact hlt

theorem inv_nat_le_inv_nat_iff {V N : Nat} (hV : 0 < V) (hN : 0 < N) :
    ((1 : Rat) / (V : Rat) ≤ (1 : Rat) / (N : Rat)) ↔ N ≤ V := by
  constructor
  · intro h
    by_cases hle : N ≤ V
    · exact hle
    · have hgt : V < N := by omega
      have hlt : (1 : Rat) / (N : Rat) < (1 : Rat) / (V : Rat) :=
        (inv_nat_lt_inv_nat_iff hN hV).mpr hgt
      exact False.elim (Rat.not_le.mpr hlt h)
  · intro h
    by_cases heq : N = V
    · rw [heq]; exact Rat.le_refl
    · exact Rat.le_of_lt ((inv_nat_lt_inv_nat_iff hV hN).mpr (Nat.lt_of_le_of_ne h heq))

theorem uniform_target_rounds_rtz {V m : Nat} (y : Fin V) (hV : 2 ^ (m + 1) < V) :
    negGradRoundsToPredRTZ m (ceGrad (uniformProb V) y y) := by
  unfold negGradRoundsToPredRTZ
  rw [uniformProb_target_grad y]
  have hVpos : 0 < V := Nat.lt_of_le_of_lt (Nat.zero_le y.val) y.isLt
  have hVp : (0 : Rat) < (V : Rat) := rat_natCast_pos hVpos
  have hVne : (V : Rat) ≠ 0 := Rat.ne_of_gt hVp
  have hsub : ((V - 1 : Nat) : Rat) / (V : Rat) = 1 - (1 : Rat) / (V : Rat) := by
    have hn : V = (V - 1) + 1 := by omega
    have hcast : (V : Rat) = ((V - 1 : Nat) : Rat) + 1 := by
      have h1 : (V : Rat) = (((V - 1) + 1 : Nat) : Rat) := congrArg (fun k : Nat => (k : Rat)) hn
      rw [h1, Rat.natCast_add]; rfl
    apply (rat_div_eq_iff hVne).mpr
    have eq1 : (1 - (1 : Rat) / (V : Rat)) * (V : Rat) =
        (V : Rat) - ((1 : Rat) / (V : Rat)) * (V : Rat) := by grind
    rw [eq1, rat_div_mul_cancel hVne, hcast]
    grind
  rw [hsub]
  constructor
  · have hpos : (0 : Rat) < (1 : Rat) / (V : Rat) := rat_div_pos (by decide) hVp
    apply rat_lt_of_sub_pos
    have eq1 : -(1 - (1 : Rat) / (V : Rat)) - (-1) = (1 : Rat) / (V : Rat) := by grind
    rw [eq1]; exact hpos
  · have hinv : (1 : Rat) / (V : Rat) < invPow2Rat (m + 1) := by
      unfold invPow2Rat pow2Rat
      exact (inv_nat_lt_inv_nat_iff hVpos (Nat.pow_pos (by decide))).mpr hV
    apply rat_lt_of_sub_pos
    have eq1 : -(1 - invPow2Rat (m + 1)) - -(1 - (1 : Rat) / (V : Rat)) =
        invPow2Rat (m + 1) - (1 : Rat) / (V : Rat) := by grind
    rw [eq1]
    exact rat_sub_pos hinv

theorem uniform_target_rounds_rne {V m : Nat} (y : Fin V) (hV : 2 ^ (m + 2) < V) :
    negGradRoundsToNegOneRNE m (ceGrad (uniformProb V) y y) := by
  unfold negGradRoundsToNegOneRNE
  exact uniform_target_rounds_rtz (m := m + 1) y hV

/-! ### Theorem 2: OCP FP8-E4M3 Dual Horizon & RNE Overshoot Cliff -/

theorem e4m3_rtz_flush_iff {V : Nat} (hV : 0 < V) :
    subnormalQuantRTZ e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 ↔ 512 < V := by
  unfold subnormalQuantRTZ e4m3MinSub invPow2Rat pow2Rat
  have h512 : (2 ^ 9 : Nat) = 512 := by decide
  rw [h512]
  constructor
  · intro h
    by_cases hlt : (1 : Rat) / (V : Rat) < (1 : Rat) / ((512 : Nat) : Rat)
    · exact (inv_nat_lt_inv_nat_iff hV (by decide)).mp hlt
    · simp only [hlt, ite_false] at h
      have hne : (1 : Rat) / ((512 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt (rat_div_pos (by decide) (rat_natCast_pos (by decide)))
      exact absurd h hne
  · intro h
    have hlt : (1 : Rat) / (V : Rat) < (1 : Rat) / ((512 : Nat) : Rat) :=
      (inv_nat_lt_inv_nat_iff hV (by decide)).mpr h
    simp only [hlt, ite_true]

theorem e4m3_rne_overshoot_val {V : Nat} (hlo : 513 ≤ V) (hhi : V ≤ 1023) :
    subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = e4m3MinSub := by
  unfold subnormalQuantRNE
  have hmid : e4m3MinSub / 2 = (1 : Rat) / ((1024 : Nat) : Rat) := by
    unfold e4m3MinSub invPow2Rat pow2Rat
    have h1 : (2 ^ 9 : Nat) = 512 := by decide
    rw [h1]
    grind
  rw [hmid]
  have hVpos : 0 < V := by omega
  have hlt : (1 : Rat) / ((1024 : Nat) : Rat) < (1 : Rat) / (V : Rat) :=
    (inv_nat_lt_inv_nat_iff (by decide) hVpos).mpr (by omega)
  have hnotle : ¬((1 : Rat) / (V : Rat) ≤ (1 : Rat) / ((1024 : Nat) : Rat)) :=
    Rat.not_le.mpr hlt
  simp only [hnotle, ite_false]

theorem e4m3_rne_flush_val {V : Nat} (hlo : 1024 ≤ V) :
    subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 := by
  unfold subnormalQuantRNE
  have hmid : e4m3MinSub / 2 = (1 : Rat) / ((1024 : Nat) : Rat) := by
    unfold e4m3MinSub invPow2Rat pow2Rat
    have h1 : (2 ^ 9 : Nat) = 512 := by decide
    rw [h1]
    grind
  rw [hmid]
  have hVpos : 0 < V := by omega
  have hle : (1 : Rat) / (V : Rat) ≤ (1 : Rat) / ((1024 : Nat) : Rat) :=
    (inv_nat_le_inv_nat_iff hVpos (by decide)).mpr hlo
  simp only [hle, ite_true]

theorem fp8_e4m3_dual_horizon_and_rne_overshoot_cliff :
    (e4m3MinSub = 1 / 512 ∧ e4m3RneMid = 1 / 1024 ∧ e4m3MinSub / 2 = e4m3RneMid) ∧
    (∀ (V : Nat), 0 < V →
      (subnormalQuantRTZ e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 ↔ 512 < V)) ∧
    (∀ (V : Nat) (y : Fin V), 512 < V →
      negGradRoundsToPredRTZ 3 (ceGrad (uniformProb V) y y) ∧
      finSum (uniformQuantGradRTZ e4m3MinSub e4m3PredNegOne V y) = -(15 / 16 : Rat)) ∧
    (∀ (y : Fin 513),
      finSum (uniformQuantGradRTZ e4m3MinSub e4m3PredNegOne 513 y) = -(15 / 16 : Rat)) ∧
    (∀ (V : Nat) (y : Fin V), 513 ≤ V → V ≤ 1023 →
      negGradRoundsToNegOneRNE 3 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = e4m3MinSub ∧
      finSum (uniformQuantGradRNE e4m3MinSub V y) = ((V - 1 : Nat) : Rat) / 512 - 1) ∧
    (∀ (y : Fin 1023),
      finSum (uniformQuantGradRNE e4m3MinSub 1023 y) = 255 / 256) ∧
    (∀ (V : Nat) (y : Fin V), 1024 ≤ V →
      negGradRoundsToNegOneRNE 3 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 ∧
      finSum (uniformQuantGradRNE e4m3MinSub V y) = -1) ∧
    ((1 : Rat) / (1024 : Rat) = e4m3RneMid ∧
     (∀ (y1 : Fin 1023) (y2 : Fin 1024),
       finSum (uniformQuantGradRNE e4m3MinSub 1023 y1) -
         finSum (uniformQuantGradRNE e4m3MinSub 1024 y2) = 511 / 256)) := by
  have hConst : e4m3MinSub = 1 / 512 ∧ e4m3RneMid = 1 / 1024 ∧ e4m3MinSub / 2 = e4m3RneMid := by
    unfold e4m3MinSub e4m3RneMid invPow2Rat pow2Rat
    have h1 : (2 ^ 9 : Nat) = 512 := by decide
    have h2 : (2 ^ 10 : Nat) = 1024 := by decide
    rw [h1, h2]
    grind
  have hRtzAll : ∀ (V : Nat) (y : Fin V), 512 < V →
      negGradRoundsToPredRTZ 3 (ceGrad (uniformProb V) y y) ∧
      finSum (uniformQuantGradRTZ e4m3MinSub e4m3PredNegOne V y) = -(15 / 16 : Rat) := by
    intro V y hV
    refine ⟨uniform_target_rounds_rtz y (by omega), ?_⟩
    unfold uniformQuantGradRTZ
    rw [finSum_ite_const]
    have hflush : subnormalQuantRTZ e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 :=
      (e4m3_rtz_flush_iff (by omega)).mpr hV
    rw [hflush]
    unfold e4m3PredNegOne
    grind
  have hRneBand : ∀ (V : Nat) (y : Fin V), 513 ≤ V → V ≤ 1023 →
      negGradRoundsToNegOneRNE 3 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = e4m3MinSub ∧
      finSum (uniformQuantGradRNE e4m3MinSub V y) = ((V - 1 : Nat) : Rat) / 512 - 1 := by
    intro V y hlo hhi
    have hq := e4m3_rne_overshoot_val hlo hhi
    refine ⟨uniform_target_rounds_rne y (by omega), hq, ?_⟩
    unfold uniformQuantGradRNE
    rw [finSum_ite_const, hq, hConst.1]
    grind
  have hPeak : ∀ (y : Fin 1023),
      finSum (uniformQuantGradRNE e4m3MinSub 1023 y) = 255 / 256 := by
    intro y
    rw [(hRneBand 1023 y (by omega) (by omega)).2.2]
    grind
  have hCliff : ∀ (V : Nat) (y : Fin V), 1024 ≤ V →
      negGradRoundsToNegOneRNE 3 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e4m3MinSub ((1 : Rat) / (V : Rat)) = 0 ∧
      finSum (uniformQuantGradRNE e4m3MinSub V y) = -1 := by
    intro V y hlo
    have hq := e4m3_rne_flush_val hlo
    refine ⟨uniform_target_rounds_rne y (by omega), hq, ?_⟩
    unfold uniformQuantGradRNE
    rw [finSum_ite_const, hq]
    grind
  refine ⟨hConst, fun V hV => e4m3_rtz_flush_iff hV, hRtzAll,
    fun y => (hRtzAll 513 y (by omega)).2, hRneBand, hPeak, hCliff, ?_⟩
  refine ⟨by rw [hConst.2.1], ?_⟩
  intro y1 y2
  rw [hPeak y1, (hCliff 1024 y2 (by omega)).2.2]
  grind

/-! ### Theorem 3: IEEE FP8-E5M2 128K-Vocab Conservation Collapse -/

theorem e5m2_rtz_flush_iff {V : Nat} (hV : 0 < V) :
    subnormalQuantRTZ e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 ↔ 65536 < V := by
  unfold subnormalQuantRTZ e5m2MinSub invPow2Rat pow2Rat
  have h65536 : (2 ^ 16 : Nat) = 65536 := by decide
  rw [h65536]
  constructor
  · intro h
    by_cases hlt : (1 : Rat) / (V : Rat) < (1 : Rat) / ((65536 : Nat) : Rat)
    · exact (inv_nat_lt_inv_nat_iff hV (by decide)).mp hlt
    · simp only [hlt, ite_false] at h
      have hne : (1 : Rat) / ((65536 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt (rat_div_pos (by decide) (rat_natCast_pos (by decide)))
      exact absurd h hne
  · intro h
    have hlt : (1 : Rat) / (V : Rat) < (1 : Rat) / ((65536 : Nat) : Rat) :=
      (inv_nat_lt_inv_nat_iff hV (by decide)).mpr h
    simp only [hlt, ite_true]

theorem e5m2_rne_overshoot_val {V : Nat} (hlo : 65537 ≤ V) (hhi : V ≤ 131071) :
    subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = e5m2MinSub := by
  unfold subnormalQuantRNE
  have hmid : e5m2MinSub / 2 = (1 : Rat) / ((131072 : Nat) : Rat) := by
    unfold e5m2MinSub invPow2Rat pow2Rat
    have h1 : (2 ^ 16 : Nat) = 65536 := by decide
    rw [h1]
    grind
  rw [hmid]
  have hVpos : 0 < V := by omega
  have hlt : (1 : Rat) / ((131072 : Nat) : Rat) < (1 : Rat) / (V : Rat) :=
    (inv_nat_lt_inv_nat_iff (by decide) hVpos).mpr (by omega)
  have hnotle : ¬((1 : Rat) / (V : Rat) ≤ (1 : Rat) / ((131072 : Nat) : Rat)) :=
    Rat.not_le.mpr hlt
  simp only [hnotle, ite_false]

theorem e5m2_rne_flush_val {V : Nat} (hlo : 131072 ≤ V) :
    subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 := by
  unfold subnormalQuantRNE
  have hmid : e5m2MinSub / 2 = (1 : Rat) / ((131072 : Nat) : Rat) := by
    unfold e5m2MinSub invPow2Rat pow2Rat
    have h1 : (2 ^ 16 : Nat) = 65536 := by decide
    rw [h1]
    grind
  rw [hmid]
  have hVpos : 0 < V := by omega
  have hle : (1 : Rat) / (V : Rat) ≤ (1 : Rat) / ((131072 : Nat) : Rat) :=
    (inv_nat_le_inv_nat_iff hVpos (by decide)).mpr hlo
  simp only [hle, ite_true]

theorem fp8_e5m2_128k_vocab_conservation_collapse :
    (e5m2MinSub = 1 / 65536 ∧ e5m2RneMid = 1 / 131072 ∧
     e5m2MinSub / 2 = e5m2RneMid ∧ (2 ^ 17 : Nat) = 131072) ∧
    (∀ (V : Nat), 0 < V →
      (subnormalQuantRTZ e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 ↔ 65536 < V)) ∧
    (∀ (V : Nat) (y : Fin V), 65536 < V →
      negGradRoundsToPredRTZ 2 (ceGrad (uniformProb V) y y) ∧
      finSum (uniformQuantGradRTZ e5m2MinSub e5m2PredNegOne V y) = -(7 / 8 : Rat)) ∧
    (∀ (y : Fin 65537),
      finSum (uniformQuantGradRTZ e5m2MinSub e5m2PredNegOne 65537 y) = -(7 / 8 : Rat)) ∧
    (∀ (V : Nat) (y : Fin V), 65537 ≤ V → V ≤ 131071 →
      negGradRoundsToNegOneRNE 2 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = e5m2MinSub ∧
      finSum (uniformQuantGradRNE e5m2MinSub V y) = ((V - 1 : Nat) : Rat) / 65536 - 1) ∧
    (∀ (y : Fin 131071),
      finSum (uniformQuantGradRNE e5m2MinSub 131071 y) = 32767 / 32768) ∧
    (∀ (V : Nat) (y : Fin V), 131072 ≤ V →
      negGradRoundsToNegOneRNE 2 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 ∧
      finSum (uniformQuantGradRNE e5m2MinSub V y) = -1) ∧
    ((1 : Rat) / (131072 : Rat) = e5m2RneMid ∧
     (∀ (y1 : Fin 131071) (y2 : Fin 131072),
       finSum (uniformQuantGradRNE e5m2MinSub 131071 y1) -
         finSum (uniformQuantGradRNE e5m2MinSub 131072 y2) = 65535 / 32768)) := by
  have hConst : e5m2MinSub = 1 / 65536 ∧ e5m2RneMid = 1 / 131072 ∧
      e5m2MinSub / 2 = e5m2RneMid ∧ (2 ^ 17 : Nat) = 131072 := by
    unfold e5m2MinSub e5m2RneMid invPow2Rat pow2Rat
    have h1 : (2 ^ 16 : Nat) = 65536 := by decide
    have h2 : (2 ^ 17 : Nat) = 131072 := by decide
    rw [h1, h2]
    grind
  have hRtzAll : ∀ (V : Nat) (y : Fin V), 65536 < V →
      negGradRoundsToPredRTZ 2 (ceGrad (uniformProb V) y y) ∧
      finSum (uniformQuantGradRTZ e5m2MinSub e5m2PredNegOne V y) = -(7 / 8 : Rat) := by
    intro V y hV
    refine ⟨uniform_target_rounds_rtz y (by omega), ?_⟩
    unfold uniformQuantGradRTZ
    rw [finSum_ite_const]
    have hflush : subnormalQuantRTZ e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 :=
      (e5m2_rtz_flush_iff (by omega)).mpr hV
    rw [hflush]
    unfold e5m2PredNegOne
    grind
  have hRneBand : ∀ (V : Nat) (y : Fin V), 65537 ≤ V → V ≤ 131071 →
      negGradRoundsToNegOneRNE 2 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = e5m2MinSub ∧
      finSum (uniformQuantGradRNE e5m2MinSub V y) = ((V - 1 : Nat) : Rat) / 65536 - 1 := by
    intro V y hlo hhi
    have hq := e5m2_rne_overshoot_val hlo hhi
    refine ⟨uniform_target_rounds_rne y (by omega), hq, ?_⟩
    unfold uniformQuantGradRNE
    rw [finSum_ite_const, hq, hConst.1]
    grind
  have hPeak : ∀ (y : Fin 131071),
      finSum (uniformQuantGradRNE e5m2MinSub 131071 y) = 32767 / 32768 := by
    intro y
    rw [(hRneBand 131071 y (by omega) (by omega)).2.2]
    grind
  have hCliff : ∀ (V : Nat) (y : Fin V), 131072 ≤ V →
      negGradRoundsToNegOneRNE 2 (ceGrad (uniformProb V) y y) ∧
      subnormalQuantRNE e5m2MinSub ((1 : Rat) / (V : Rat)) = 0 ∧
      finSum (uniformQuantGradRNE e5m2MinSub V y) = -1 := by
    intro V y hlo
    have hq := e5m2_rne_flush_val hlo
    refine ⟨uniform_target_rounds_rne y (by omega), hq, ?_⟩
    unfold uniformQuantGradRNE
    rw [finSum_ite_const, hq]
    grind
  refine ⟨hConst, fun V hV => e5m2_rtz_flush_iff hV, hRtzAll,
    fun y => (hRtzAll 65537 y (by omega)).2, hRneBand, hPeak, hCliff, ?_⟩
  refine ⟨by rw [hConst.2.1], ?_⟩
  intro y1 y2
  rw [hPeak y1, (hCliff 131072 y2 (by omega)).2.2]
  grind

end CeLseHorizon
