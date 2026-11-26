/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp8Frontier.RatOrder

/-!
# Theorems 5 & 6: Delayed-Scaling Spike-Clipping Crossover & Block-Scaled Bias Invariance

Proves:
- **Theorem 5 (`delayed_scaling_spike_clipping_crossover_exact`):**
  Universal exact rational spike-factor phase transition `ρ*(M, m) = ((2^{m+1} + 1) / 2^{m+1}) * 2^M`
  where delayed-scaling clipping error `(1 - 2^M / ρ)^2` crosses wide-format normal quantization error
  `1 / (2^{m+1} + 1)^2`, specializing for `E4M3` vs `E5M2` (`m = 2`) to exact `ρ*(M) = (9/8) * 2^M`
  (`+12.5%` headroom threshold), plus partial-spike strict dominance at `ρ = (9/8) * 2^M`.
- **Theorem 6 (`fp8_block_scaling_bias_invariance_exact`):**
  Exact block-scaled exponent-bias invariance over arbitrary coordinate lists `xs, qs : List Rat`
  (any positive scale shift `c = 2^{b₁} / 2^{b₂}` is absorbed identically into the shared block scale),
  contrasted with the exact `4x` per-bit (`4^M` total) delayed-scaling headroom underflow capacity tax.
-/

namespace Mxfp8Frontier

/-! ### Helper Lemmas for Theorem 5 -/

theorem rat_sq_lt_sq_iff {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    a * a < b * b ↔ a < b := by
  have hab : (0 : Rat) < a + b := rat_add_pos ha hb
  have hdiff : b * b - a * a = (b - a) * (a + b) := by grind
  constructor
  · intro h
    have hpos : (0 : Rat) < (b - a) * (a + b) := by
      rw [← hdiff]
      exact rat_sub_pos h
    have hba : (0 : Rat) < b - a := by
      apply rat_lt_of_mul_pos_right hab
      rw [Rat.zero_mul]
      exact hpos
    exact rat_lt_of_sub_pos hba
  · intro h
    have hba : (0 : Rat) < b - a := rat_sub_pos h
    have hpos : (0 : Rat) < b * b - a * a := by
      rw [hdiff]
      exact rat_mul_pos hba hab
    exact rat_lt_of_sub_pos hpos

theorem rat_div_mul_div (a b c d : Rat) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a / b) * (c / d) = (a * c) / (b * d) := by
  have hbd : b * d ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hb h
    | inr h => exact hd h
  have h1 : ((a / b) * (c / d)) * (b * d) = a * c := by
    have hL : (a / b) * b = a := rat_div_mul_cancel hb
    have hR : (c / d) * d = c := rat_div_mul_cancel hd
    calc
      ((a / b) * (c / d)) * (b * d) = ((a / b) * b) * ((c / d) * d) := by grind
      _ = a * c := by rw [hL, hR]
  have h2 : ((a * c) / (b * d)) * (b * d) = a * c := rat_div_mul_cancel hbd
  have hmul : ((a / b) * (c / d) - (a * c) / (b * d)) * (b * d) = 0 := by grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h => grind
  | inr h => exact False.elim (hbd h)

theorem delayedClip_base_eq (M m : Nat) :
    1 - pow2Rat M / spikeCrossover M m = 1 / ((2 ^ (m + 1) + 1 : Nat) : Rat) := by
  unfold spikeCrossover
  have hpM_pos : (0 : Rat) < pow2Rat M := pow2Rat_pos M
  have hpm_pos : (0 : Rat) < pow2Rat (m + 1) := pow2Rat_pos (m + 1)
  have hpm_ne : pow2Rat (m + 1) ≠ 0 := Rat.ne_of_gt hpm_pos
  have hden_pos : (0 : Rat) < ((2 ^ (m + 1) + 1 : Nat) : Rat) := rat_natCast_pos (Nat.succ_pos _)
  have hden_ne : ((2 ^ (m + 1) + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hden_pos
  have hsc_pos : (0 : Rat) < (((2 ^ (m + 1) + 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat M :=
    rat_mul_pos (rat_div_pos hden_pos hpm_pos) hpM_pos
  have hsc_ne : (((2 ^ (m + 1) + 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat M ≠ 0 :=
    Rat.ne_of_gt hsc_pos
  have hdiv : pow2Rat M / ((((2 ^ (m + 1) + 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat M) =
      pow2Rat (m + 1) / ((2 ^ (m + 1) + 1 : Nat) : Rat) := by
    apply rat_div_eq_of_cross hsc_ne hden_ne
    have h1 : (((2 ^ (m + 1) + 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat (m + 1) =
        ((2 ^ (m + 1) + 1 : Nat) : Rat) := rat_div_mul_cancel hpm_ne
    calc
      pow2Rat M * ((2 ^ (m + 1) + 1 : Nat) : Rat)
          = pow2Rat M * ((((2 ^ (m + 1) + 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat (m + 1)) := by
              rw [h1]
      _ = pow2Rat (m + 1) * ((((2 ^ (m + 1) + 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat M) := by
              grind
  rw [hdiv]
  have hcast : ((2 ^ (m + 1) + 1 : Nat) : Rat) = pow2Rat (m + 1) + 1 := by
    unfold pow2Rat
    rw [Rat.natCast_add]
    rfl
  have hsum : pow2Rat (m + 1) / ((2 ^ (m + 1) + 1 : Nat) : Rat) +
      1 / ((2 ^ (m + 1) + 1 : Nat) : Rat) = 1 := by
    rw [Rat.div_def, Rat.div_def, ← Rat.add_mul, ← hcast, Rat.mul_inv_cancel _ hden_ne]
  grind

theorem delayedClipDelta_at_crossover (M m : Nat) :
    delayedClipDelta (spikeCrossover M m) M = wideNormalDelta m := by
  unfold delayedClipDelta wideNormalDelta
  rw [delayedClip_base_eq M m]
  have hden_ne : ((2 ^ (m + 1) + 1 : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos (Nat.succ_pos _))
  rw [rat_div_mul_div 1 _ 1 _ hden_ne hden_ne, Rat.mul_one]

theorem spikeCrossover_pos (M m : Nat) : (0 : Rat) < spikeCrossover M m := by
  unfold spikeCrossover
  exact rat_mul_pos (rat_div_pos (rat_natCast_pos (Nat.succ_pos _)) (pow2Rat_pos (m + 1))) (pow2Rat_pos M)

theorem delayedClip_base_pos {ρ : Rat} {M : Nat} (hρ : pow2Rat M < ρ) :
    (0 : Rat) < 1 - pow2Rat M / ρ := by
  have hpM_pos : (0 : Rat) < pow2Rat M := pow2Rat_pos M
  have hρ_pos : (0 : Rat) < ρ := rat_lt_trans hpM_pos hρ
  have hlt1 : pow2Rat M / ρ < 1 := by
    have h1 : (1 : Rat) = ρ / ρ := (Rat.mul_inv_cancel ρ (Rat.ne_of_gt hρ_pos)).symm
    rw [h1]
    apply rat_div_lt_div_of_cross hρ_pos hρ_pos
    exact rat_mul_lt_mul_of_pos_right hρ hρ_pos
  exact rat_sub_pos hlt1

theorem delayedClip_base_lt_iff {ρ₁ ρ₂ : Rat} {M : Nat}
    (h1 : (0 : Rat) < ρ₁) (h2 : (0 : Rat) < ρ₂) :
    1 - pow2Rat M / ρ₁ < 1 - pow2Rat M / ρ₂ ↔ ρ₁ < ρ₂ := by
  have hpM_pos : (0 : Rat) < pow2Rat M := pow2Rat_pos M
  constructor
  · intro h
    have hdiv : pow2Rat M / ρ₂ < pow2Rat M / ρ₁ := by
      apply rat_lt_of_sub_pos
      have eq : pow2Rat M / ρ₁ - pow2Rat M / ρ₂ = (1 - pow2Rat M / ρ₂) - (1 - pow2Rat M / ρ₁) := by
        grind
      rw [eq]
      exact rat_sub_pos h
    have hmul : (pow2Rat M / ρ₂) * (ρ₁ * ρ₂) < (pow2Rat M / ρ₁) * (ρ₁ * ρ₂) :=
      rat_mul_lt_mul_of_pos_right hdiv (rat_mul_pos h1 h2)
    have hL : (pow2Rat M / ρ₂) * (ρ₁ * ρ₂) = pow2Rat M * ρ₁ := by
      have hc : (pow2Rat M / ρ₂) * ρ₂ = pow2Rat M := rat_div_mul_cancel (Rat.ne_of_gt h2)
      calc
        (pow2Rat M / ρ₂) * (ρ₁ * ρ₂) = ((pow2Rat M / ρ₂) * ρ₂) * ρ₁ := by grind
        _ = pow2Rat M * ρ₁ := by rw [hc]
    have hR : (pow2Rat M / ρ₁) * (ρ₁ * ρ₂) = pow2Rat M * ρ₂ := by
      have hc : (pow2Rat M / ρ₁) * ρ₁ = pow2Rat M := rat_div_mul_cancel (Rat.ne_of_gt h1)
      calc
        (pow2Rat M / ρ₁) * (ρ₁ * ρ₂) = ((pow2Rat M / ρ₁) * ρ₁) * ρ₂ := by grind
        _ = pow2Rat M * ρ₂ := by rw [hc]
    rw [hL, hR, Rat.mul_comm (pow2Rat M) ρ₁, Rat.mul_comm (pow2Rat M) ρ₂] at hmul
    exact rat_lt_of_mul_pos_right hpM_pos hmul
  · intro h
    have hdiv : pow2Rat M / ρ₂ < pow2Rat M / ρ₁ := by
      apply rat_div_lt_div_of_cross h2 h1
      exact rat_mul_lt_mul_of_pos_left h hpM_pos
    apply rat_lt_of_sub_pos
    have eq : (1 - pow2Rat M / ρ₂) - (1 - pow2Rat M / ρ₁) = pow2Rat M / ρ₁ - pow2Rat M / ρ₂ := by
      grind
    rw [eq]
    exact rat_sub_pos hdiv

/-- Headline Theorem 5 (`delayed_scaling_spike_clipping_crossover_exact`). -/
theorem delayed_scaling_spike_clipping_crossover_exact :
    (∀ (M m : Nat), delayedClipDelta (spikeCrossover M m) M = wideNormalDelta m) ∧
    (∀ (M m : Nat) (ρ : Rat), pow2Rat M < ρ →
      (wideNormalDelta m < delayedClipDelta ρ M ↔ spikeCrossover M m < ρ) ∧
      (delayedClipDelta ρ M < wideNormalDelta m ↔ ρ < spikeCrossover M m)) ∧
    (wideNormalDelta 2 = 1 / 81 ∧
     (∀ M : Nat, spikeCrossover M 2 = (9 / 8 : Rat) * pow2Rat M) ∧
     (spikeCrossover 0 2 = 9 / 8 ∧ spikeCrossover 1 2 = 9 / 4 ∧
      spikeCrossover 2 2 = 9 / 2 ∧ spikeCrossover 3 2 = 9 ∧
      spikeCrossover 4 2 = 18)) ∧
    (∀ (M : Nat) (k_norm ns_norm e_ns e_e5m2 : Rat),
      0 < k_norm → 0 ≤ ns_norm → 0 < e_ns →
      e_e5m2 ≤ (1 / 81 : Rat) * k_norm →
      e_e5m2 / (k_norm + ns_norm) <
        (delayedClipDelta (spikeCrossover M 2) M * k_norm + e_ns) / (k_norm + ns_norm)) := by
  refine ⟨delayedClipDelta_at_crossover, ?_, ?_, ?_⟩
  · intro M m ρ hρ
    have hρ_pos : (0 : Rat) < ρ := rat_lt_trans (pow2Rat_pos M) hρ
    have hsc_pos : (0 : Rat) < spikeCrossover M m := spikeCrossover_pos M m
    have hbase_ρ : (0 : Rat) < 1 - pow2Rat M / ρ := delayedClip_base_pos hρ
    have hbase_sc : (0 : Rat) < 1 - pow2Rat M / spikeCrossover M m := by
      rw [delayedClip_base_eq M m]
      exact rat_div_pos (by decide) (rat_natCast_pos (Nat.succ_pos _))
    rw [← delayedClipDelta_at_crossover M m]
    unfold delayedClipDelta
    constructor
    · rw [rat_sq_lt_sq_iff hbase_sc hbase_ρ, delayedClip_base_lt_iff hsc_pos hρ_pos]
    · rw [rat_sq_lt_sq_iff hbase_ρ hbase_sc, delayedClip_base_lt_iff hρ_pos hsc_pos]
  · have h98 : (((2 ^ (2 + 1) + 1 : Nat) : Rat) / pow2Rat (2 + 1)) = (9 / 8 : Rat) := by
      unfold pow2Rat; rfl
    have hw2 : wideNormalDelta 2 = 1 / 81 := by
      unfold wideNormalDelta
      change (1 : Rat) / (9 * 9) = 1 / 81
      grind
    refine ⟨hw2, ?_,
            ⟨by unfold spikeCrossover; rw [h98]; change (9 / 8 : Rat) * 1 = 9 / 8; grind,
             by unfold spikeCrossover; rw [h98]; change (9 / 8 : Rat) * 2 = 9 / 4; grind,
             by unfold spikeCrossover; rw [h98]; change (9 / 8 : Rat) * 4 = 9 / 2; grind,
             by unfold spikeCrossover; rw [h98]; change (9 / 8 : Rat) * 8 = 9; grind,
             by unfold spikeCrossover; rw [h98]; change (9 / 8 : Rat) * 16 = 18; grind⟩⟩
    intro M
    unfold spikeCrossover
    rw [h98]
  · intro M k_norm ns_norm e_ns e_e5m2 hk hns hens he5
    have htot : (0 : Rat) < k_norm + ns_norm := rat_add_pos_of_pos_of_nonneg hk hns
    have hclip : delayedClipDelta (spikeCrossover M 2) M = 1 / 81 := by
      rw [delayedClipDelta_at_crossover M 2]
      unfold wideNormalDelta
      change (1 : Rat) / (9 * 9) = 1 / 81
      grind
    rw [hclip]
    have hnum : e_e5m2 < (1 / 81 : Rat) * k_norm + e_ns := by
      have h1 : (1 / 81 : Rat) * k_norm < (1 / 81 : Rat) * k_norm + e_ns := by
        apply rat_lt_of_sub_pos
        have eq : ((1 / 81 : Rat) * k_norm + e_ns) - (1 / 81 : Rat) * k_norm = e_ns := by grind
        rw [eq]; exact hens
      exact rat_lt_of_le_of_lt he5 h1
    apply rat_div_lt_div_of_cross htot htot
    exact rat_mul_lt_mul_of_pos_right hnum htot

/-! ### Theorem 6: Block-Scaled Exponent-Bias Invariance & `4x` Per-Bit Headroom Tax -/

theorem sqErrList_scale_invariance (s c : Rat) (hc : c ≠ 0) :
    ∀ (xs qs : List Rat), sqErrList (s / c) xs (qs.map (c * ·)) = sqErrList s xs qs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, q :: qs => by
      simp only [List.map_cons, sqErrList]
      have hterm : (s / c) * (c * q) = s * q := by
        have hsc : (s / c) * c = s := rat_div_mul_cancel hc
        calc
          (s / c) * (c * q) = ((s / c) * c) * q := by grind
          _ = s * q := by rw [hsc]
      rw [hterm, sqErrList_scale_invariance s c hc xs qs]

theorem underflowCap_step (Y : Rat) (M : Nat) :
    underflowCap Y M = 4 * underflowCap Y (M + 1) := by
  unfold underflowCap effAnchor
  rw [pow2Rat_succ M]
  have hp : pow2Rat M ≠ 0 := pow2Rat_ne_zero M
  have h2p : 2 * pow2Rat M ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact (by decide : (2 : Rat) ≠ 0) h
    | inr h => exact hp h
  have hdiv : Y / (2 * pow2Rat M) = (Y / pow2Rat M) / 2 := by
    apply rat_div_eq_of_cross h2p (by decide)
    have h1 : (Y / pow2Rat M) * pow2Rat M = Y := rat_div_mul_cancel hp
    calc
      Y * 2 = ((Y / pow2Rat M) * pow2Rat M) * 2 := by rw [h1]
      _ = (Y / pow2Rat M) * (2 * pow2Rat M) := by grind
  rw [hdiv]
  have hhalf : ((Y / pow2Rat M) / 2) * ((Y / pow2Rat M) / 2) * 4 =
      (Y / pow2Rat M) * (Y / pow2Rat M) := by
    have h2 : ((Y / pow2Rat M) / 2) * 2 = Y / pow2Rat M := rat_div_mul_cancel (by decide)
    calc
      ((Y / pow2Rat M) / 2) * ((Y / pow2Rat M) / 2) * 4
          = (((Y / pow2Rat M) / 2) * 2) * (((Y / pow2Rat M) / 2) * 2) := by grind
      _ = (Y / pow2Rat M) * (Y / pow2Rat M) := by rw [h2]
  grind

theorem underflowCap_closed_form (Y : Rat) (M : Nat) :
    underflowCap Y M = (Y * Y) / ((4 ^ M : Nat) : Rat) := by
  unfold underflowCap effAnchor
  have hp : pow2Rat M ≠ 0 := pow2Rat_ne_zero M
  rw [rat_div_mul_div Y (pow2Rat M) Y (pow2Rat M) hp hp]
  have hpow : pow2Rat M * pow2Rat M = ((4 ^ M : Nat) : Rat) := by
    unfold pow2Rat
    rw [← Rat.natCast_mul]
    have hnat : 2 ^ M * 2 ^ M = 4 ^ M := by
      rw [← Nat.mul_pow]
    rw [hnat]
  rw [hpow]

/-- Headline Theorem 6 (`fp8_block_scaling_bias_invariance_exact`). -/
theorem fp8_block_scaling_bias_invariance_exact :
    (∀ (s c : Rat) (xs qs : List Rat), c ≠ 0 →
      sqErrList (s / c) xs (qs.map (c * ·)) = sqErrList s xs qs ∧
      1 - sqErrList (s / c) xs (qs.map (c * ·)) / normSqList xs =
        1 - sqErrList s xs qs / normSqList xs) ∧
    (∀ (s : Rat) (b₁ b₂ : Nat) (xs qs : List Rat),
      let c := pow2Rat b₁ / pow2Rat b₂
      sqErrList (s / c) xs (qs.map (c * ·)) = sqErrList s xs qs) ∧
    (∀ (Y : Rat) (M : Nat),
      underflowCap Y M = 4 * underflowCap Y (M + 1) ∧
      underflowCap Y M = (Y * Y) / ((4 ^ M : Nat) : Rat)) ∧
    (underflowCap 458752 0 = 210453397504 ∧
     underflowCap 458752 1 = 52613349376 ∧
     underflowCap 458752 2 = 13153337344) := by
  refine ⟨?_, ?_, ?_,
          ⟨by rw [underflowCap_closed_form]; change (458752 : Rat) * 458752 / 1 = 210453397504; grind,
           by rw [underflowCap_closed_form]; change (458752 : Rat) * 458752 / 4 = 52613349376; grind,
           by rw [underflowCap_closed_form]; change (458752 : Rat) * 458752 / 16 = 13153337344; grind⟩⟩
  · intro s c xs qs hc
    have h := sqErrList_scale_invariance s c hc xs qs
    exact ⟨h, by rw [h]⟩
  · intro s b₁ b₂ xs qs
    have hc : pow2Rat b₁ / pow2Rat b₂ ≠ 0 :=
      Rat.ne_of_gt (rat_div_pos (pow2Rat_pos b₁) (pow2Rat_pos b₂))
    exact sqErrList_scale_invariance s (pow2Rat b₁ / pow2Rat b₂) hc xs qs
  · intro Y M
    exact ⟨underflowCap_step Y M, underflowCap_closed_form Y M⟩

end Mxfp8Frontier
