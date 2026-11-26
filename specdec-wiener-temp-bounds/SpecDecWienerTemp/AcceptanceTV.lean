/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecWienerTemp.RatOrder

/-!
# Quantized Draft Speculative Acceptance, TV Distance, and Rényi-2 Sensitivity

Proves Theorem 3 (`quantized_draft_tv_acceptance_lower_bound_exact`):
1. Exact acceptance–TV identity `α(p, q) = ∑_v min(p_v, q_v) = 1 - TV(p, q)`, with `0 ≤ α(p, q) ≤ 1`
   and `α(p, p) = 1`.
2. Exact ratio-perturbation and multiplicative weight-perturbation lower bounds on acceptance
   (`q_v ≥ r · p_v → α(p, q) ≥ r`, and `(1 - δ) w_v ≤ w̃_v ≤ (1 + δ) w_v → α(p, q) ≥ (1 - δ)/(1 + δ)`),
   plus additive `L_1` lower bound `α(p, q) ≥ 1 - (1/2) ∑_v η_v`.
3. Exact Rényi-2 collision sensitivity factor identity and Cauchy–Schwarz bound:
   pointwise `0 ≤ 1 - 2 p_v + ‖p‖_2^2`, exact weighted identity
   `∑_v p_v (1 - 2 p_v + ‖p‖_2^2) = 1 - ‖p‖_2^2`, and for any `s_v` with
   `s_v^2 ≤ 1 - 2 p_v + ‖p‖_2^2`, `(∑_v p_v s_v)^2 ≤ 1 - ‖p‖_2^2`.
-/

namespace SpecDecWienerTemp

theorem acceptRate_eq_one_sub_tvDist {n : Nat} {p q : Fin n → Rat}
    (hp : isProbDist p) (hq : isProbDist q) :
    acceptRate p q = 1 - tvDist p q := by
  unfold acceptRate tvDist
  have hcongr : finSum (fun i => ratMin (p i) (q i)) =
      finSum (fun i => (p i + q i - ratAbs (p i - q i)) / 2) :=
    finSum_congr (fun i => ratMin_eq_half_sub_abs (p i) (q i))
  rw [hcongr, finSum_div, finSum_sub, finSum_add, hp.2, hq.2]
  grind

theorem acceptRate_bounds {n : Nat} {p q : Fin n → Rat}
    (hp : isProbDist p) (hq : isProbDist q) :
    (0 : Rat) ≤ acceptRate p q ∧ acceptRate p q ≤ 1 ∧ acceptRate p p = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold acceptRate
    exact finSum_nonneg (fun i => ratMin_nonneg (hp.1 i) (hq.1 i))
  · unfold acceptRate
    have hle : finSum (fun i => ratMin (p i) (q i)) ≤ finSum p :=
      finSum_le_finSum (fun i => ratMin_le_left (p i) (q i))
    rw [hp.2] at hle
    exact hle
  · unfold acceptRate
    rw [finSum_congr (fun i => ratMin_self (p i)), hp.2]

theorem acceptRate_ge_of_ratio_lower {n : Nat} {p q : Fin n → Rat} {r : Rat}
    (hp : isProbDist p) (hr1 : r ≤ 1) (hratio : ∀ i : Fin n, r * p i ≤ q i) :
    r ≤ acceptRate p q := by
  unfold acceptRate
  have hle : finSum (fun i => r * p i) ≤ finSum (fun i => ratMin (p i) (q i)) := by
    apply finSum_le_finSum
    intro i
    have h1 : r * p i ≤ 1 * p i := rat_mul_le_mul_of_nonneg_right hr1 (hp.1 i)
    rw [Rat.one_mul] at h1
    exact le_ratMin h1 (hratio i)
  rw [finSum_mul_left, hp.2, Rat.mul_one] at hle
  exact hle

theorem normProb_isProbDist {n : Nat} {w : Fin n → Rat}
    (hw : ∀ i : Fin n, (0 : Rat) ≤ w i) (hsum : (0 : Rat) < finSum w) :
    isProbDist (normProb w) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact rat_div_nonneg (hw i) hsum
  · unfold normProb
    rw [finSum_div]
    rw [rat_div_eq_iff (Rat.ne_of_gt hsum), Rat.one_mul]

theorem acceptRate_ge_of_mult_perturbation {n : Nat} {w wt : Fin n → Rat} {δ : Rat}
    (hw : ∀ i : Fin n, (0 : Rat) ≤ w i) (hsum : (0 : Rat) < finSum w)
    (hδ0 : (0 : Rat) ≤ δ) (hδ1 : δ < 1)
    (hlo : ∀ i : Fin n, (1 - δ) * w i ≤ wt i)
    (hhi : ∀ i : Fin n, wt i ≤ (1 + δ) * w i) :
    (1 - δ) / (1 + δ) ≤ acceptRate (normProb w) (normProb wt) ∧
    tvDist (normProb w) (normProb wt) ≤ (2 * δ) / (1 + δ) := by
  have h1m_pos : (0 : Rat) < 1 - δ := rat_sub_pos hδ1
  have h1p_pos : (0 : Rat) < 1 + δ := rat_add_pos_of_pos_of_nonneg (by decide) hδ0
  have hwt_nn : ∀ i : Fin n, (0 : Rat) ≤ wt i := fun i =>
    Rat.le_trans (Rat.mul_nonneg (Rat.le_of_lt h1m_pos) (hw i)) (hlo i)
  have hsum_lo : (1 - δ) * finSum w ≤ finSum wt := by
    rw [← finSum_mul_left]
    exact finSum_le_finSum hlo
  have hsum_hi : finSum wt ≤ (1 + δ) * finSum w := by
    rw [← finSum_mul_left]
    exact finSum_le_finSum hhi
  have hsum_wt_pos : (0 : Rat) < finSum wt :=
    rat_lt_of_lt_of_le (rat_mul_pos h1m_pos hsum) hsum_lo
  have hp : isProbDist (normProb w) := normProb_isProbDist hw hsum
  have hq : isProbDist (normProb wt) := normProb_isProbDist hwt_nn hsum_wt_pos
  have hr_le1 : (1 - δ) / (1 + δ) ≤ 1 := by
    apply rat_div_le_of_mul_le h1p_pos
    rw [Rat.one_mul]
    apply rat_le_of_sub_nonneg
    have : 1 + δ - (1 - δ) = 2 * δ := by grind
    rw [this]
    exact Rat.mul_nonneg (by decide) hδ0
  have hratio : ∀ i : Fin n, ((1 - δ) / (1 + δ)) * normProb w i ≤ normProb wt i := by
    intro i
    unfold normProb
    have hmul_eq : ((1 - δ) / (1 + δ)) * (w i / finSum w) =
        ((1 - δ) * w i) / ((1 + δ) * finSum w) := by
      have ha : 1 + δ ≠ 0 := Rat.ne_of_gt h1p_pos
      have hb : finSum w ≠ 0 := Rat.ne_of_gt hsum
      have hab : (1 + δ) * finSum w ≠ 0 := Rat.ne_of_gt (rat_mul_pos h1p_pos hsum)
      symm
      rw [rat_div_eq_iff hab]
      symm
      calc ((1 - δ) / (1 + δ)) * (w i / finSum w) * ((1 + δ) * finSum w)
          = (((1 - δ) / (1 + δ)) * (1 + δ)) * ((w i / finSum w) * finSum w) := by grind
        _ = (1 - δ) * w i := by rw [rat_div_mul_cancel ha, rat_div_mul_cancel hb]
    rw [hmul_eq, rat_div_le_div_iff (rat_mul_pos h1p_pos hsum) hsum_wt_pos]
    have h1 : (1 - δ) * w i * finSum wt ≤ wt i * finSum wt :=
      rat_mul_le_mul_of_nonneg_right (hlo i) (Rat.le_of_lt hsum_wt_pos)
    have h2 : wt i * finSum wt ≤ wt i * ((1 + δ) * finSum w) :=
      rat_mul_le_mul_of_nonneg_left hsum_hi (hwt_nn i)
    exact Rat.le_trans h1 h2
  have hacc : (1 - δ) / (1 + δ) ≤ acceptRate (normProb w) (normProb wt) :=
    acceptRate_ge_of_ratio_lower hp hr_le1 hratio
  have htv : tvDist (normProb w) (normProb wt) ≤ (2 * δ) / (1 + δ) := by
    have heq := acceptRate_eq_one_sub_tvDist hp hq
    rw [heq] at hacc
    have h1sub : 1 - (1 - δ) / (1 + δ) = (2 * δ) / (1 + δ) := by
      apply rat_eq_of_mul_eq_mul_right (Rat.ne_of_gt h1p_pos)
      have ha : ((1 - δ) / (1 + δ)) * (1 + δ) = 1 - δ := rat_div_mul_cancel (Rat.ne_of_gt h1p_pos)
      have hb : ((2 * δ) / (1 + δ)) * (1 + δ) = 2 * δ := rat_div_mul_cancel (Rat.ne_of_gt h1p_pos)
      calc (1 - (1 - δ) / (1 + δ)) * (1 + δ)
          = (1 + δ) - ((1 - δ) / (1 + δ)) * (1 + δ) := by grind
        _ = (1 + δ) - (1 - δ) := by rw [ha]
        _ = 2 * δ := by grind
        _ = ((2 * δ) / (1 + δ)) * (1 + δ) := hb.symm
    rw [← h1sub]
    have hle := rat_sub_nonneg hacc
    apply rat_le_of_sub_nonneg
    grind
  exact ⟨hacc, htv⟩

theorem renyi2_pointwise_nonneg {n : Nat} {p : Fin n → Rat}
    (_hp : isProbDist p) (i : Fin n) :
    (0 : Rat) ≤ 1 - 2 * p i + renyi2Collision p := by
  have hsq_le : p i * p i ≤ renyi2Collision p :=
    finSum_elem_le_finSum (f := fun j => p j * p j) (fun j => rat_sq_nonneg (p j)) i
  have hdiff_nn : (0 : Rat) ≤ renyi2Collision p - p i * p i := rat_sub_nonneg hsq_le
  have h1m_sq : (0 : Rat) ≤ (1 - p i) * (1 - p i) := rat_sq_nonneg (1 - p i)
  have hdecomp : 1 - 2 * p i + renyi2Collision p =
      (1 - p i) * (1 - p i) + (renyi2Collision p - p i * p i) := by grind
  rw [hdecomp]
  exact rat_add_nonneg h1m_sq hdiff_nn

theorem renyi2_sensitivity_exact {n : Nat} {p : Fin n → Rat} (hp : isProbDist p) :
    finSum (fun i => p i * (1 - 2 * p i + renyi2Collision p)) = 1 - renyi2Collision p := by
  have hsplit : (fun i : Fin n => p i * (1 - 2 * p i + renyi2Collision p)) =
      (fun i => (p i - 2 * (p i * p i)) + renyi2Collision p * p i) := by
    funext i; grind
  rw [hsplit, finSum_add, finSum_sub, finSum_mul_left, finSum_mul_left, hp.2]
  unfold renyi2Collision
  grind

theorem weighted_jensen_sq {n : Nat} {p s : Fin n → Rat} (hp : isProbDist p) :
    finSum (fun i => p i * s i) * finSum (fun i => p i * s i) ≤
      finSum (fun i => p i * (s i * s i)) := by
  let μ := finSum (fun i => p i * s i)
  have hvar_nn : (0 : Rat) ≤ finSum (fun i => p i * ((s i - μ) * (s i - μ))) :=
    finSum_nonneg (fun i => Rat.mul_nonneg (hp.1 i) (rat_sq_nonneg (s i - μ)))
  have hexpand : finSum (fun i => p i * ((s i - μ) * (s i - μ))) =
      finSum (fun i => p i * (s i * s i)) - μ * μ := by
    have hpt : (fun i : Fin n => p i * ((s i - μ) * (s i - μ))) =
        (fun i => (p i * (s i * s i) - (2 * μ) * (p i * s i)) + (μ * μ) * p i) := by
      funext i; grind
    rw [hpt, finSum_add, finSum_sub, finSum_mul_left, finSum_mul_left, hp.2]
    change finSum (fun i => p i * (s i * s i)) - (2 * μ) * μ + (μ * μ) * 1 =
      finSum (fun i => p i * (s i * s i)) - μ * μ
    grind
  rw [hexpand] at hvar_nn
  exact rat_le_of_sub_nonneg hvar_nn

/-- Headline Theorem 3 (`quantized_draft_tv_acceptance_lower_bound_exact`). -/
theorem quantized_draft_tv_acceptance_lower_bound_exact :
    (∀ {n : Nat} (p q : Fin n → Rat), isProbDist p → isProbDist q →
      acceptRate p q = 1 - tvDist p q ∧
      (0 : Rat) ≤ acceptRate p q ∧ acceptRate p q ≤ 1 ∧ acceptRate p p = 1) ∧
    (∀ {n : Nat} (p q : Fin n → Rat) (r : Rat),
      isProbDist p → r ≤ 1 → (∀ i : Fin n, r * p i ≤ q i) →
      r ≤ acceptRate p q) ∧
    (∀ {n : Nat} (w wt : Fin n → Rat) (δ : Rat),
      (∀ i : Fin n, (0 : Rat) ≤ w i) → (0 : Rat) < finSum w →
      (0 : Rat) ≤ δ → δ < 1 →
      (∀ i : Fin n, (1 - δ) * w i ≤ wt i) →
      (∀ i : Fin n, wt i ≤ (1 + δ) * w i) →
      (1 - δ) / (1 + δ) ≤ acceptRate (normProb w) (normProb wt) ∧
      tvDist (normProb w) (normProb wt) ≤ (2 * δ) / (1 + δ)) ∧
    (∀ {n : Nat} (p q η : Fin n → Rat),
      isProbDist p → isProbDist q →
      (∀ i : Fin n, ratAbs (p i - q i) ≤ η i) →
      1 - finSum η / 2 ≤ acceptRate p q) ∧
    (∀ {n : Nat} (p : Fin n → Rat), isProbDist p →
      (∀ i : Fin n, (0 : Rat) ≤ 1 - 2 * p i + renyi2Collision p) ∧
      finSum (fun i => p i * (1 - 2 * p i + renyi2Collision p)) = 1 - renyi2Collision p ∧
      finSum (fun i => p i * (1 - 2 * p i + renyi2Collision p)) ≤ 1 - renyi2Collision p ∧
      (∀ s : Fin n → Rat, (∀ i : Fin n, s i * s i ≤ 1 - 2 * p i + renyi2Collision p) →
        finSum (fun i => p i * s i) * finSum (fun i => p i * s i) ≤ 1 - renyi2Collision p)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n p q hp hq
    have ⟨h0, h1, hself⟩ := acceptRate_bounds hp hq
    exact ⟨acceptRate_eq_one_sub_tvDist hp hq, h0, h1, hself⟩
  · intro n p q r hp hr1 hratio
    exact acceptRate_ge_of_ratio_lower hp hr1 hratio
  · intro n w wt δ hw hsum hδ0 hδ1 hlo hhi
    exact acceptRate_ge_of_mult_perturbation hw hsum hδ0 hδ1 hlo hhi
  · intro n p q η hp hq hη
    rw [acceptRate_eq_one_sub_tvDist hp hq]
    unfold tvDist
    have hsum_le : finSum (fun i => ratAbs (p i - q i)) ≤ finSum η := finSum_le_finSum hη
    have hdiv_le : finSum (fun i => ratAbs (p i - q i)) / 2 ≤ finSum η / 2 := by
      rw [rat_div_le_div_iff (by decide : (0 : Rat) < 2) (by decide : (0 : Rat) < 2)]
      exact rat_mul_le_mul_of_nonneg_right hsum_le (by decide)
    have hsub := rat_sub_nonneg hdiv_le
    apply rat_le_of_sub_nonneg
    grind
  · intro n p hp
    refine ⟨renyi2_pointwise_nonneg hp, renyi2_sensitivity_exact hp,
      by rw [renyi2_sensitivity_exact hp]; exact Rat.le_refl, ?_⟩
    intro s hs
    have hj := weighted_jensen_sq (s := s) hp
    have hle : finSum (fun i => p i * (s i * s i)) ≤
        finSum (fun i => p i * (1 - 2 * p i + renyi2Collision p)) :=
      finSum_le_finSum (fun i => rat_mul_le_mul_of_nonneg_left (hs i) (hp.1 i))
    rw [renyi2_sensitivity_exact hp] at hle
    exact Rat.le_trans hj hle

end SpecDecWienerTemp
