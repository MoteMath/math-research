/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecWienerTemp.RatOrder

/-!
# Speculative Decoding Expected Yield, Net Speedup, and Discrete Unimodality

Proves Theorem 4 (`expected_specdec_yield_and_speedup_exact`):
1. Exact geometric yield identity `(1 - α) · Y(α, γ) = 1 - α^{γ+1}`, closed form
   `Y(α, γ) = (1 - α^{γ+1}) / (1 - α)` for `α ≠ 1`, and `Y(1, γ) = γ + 1`.
2. Exact closed-form net speedup `S(α, γ, c) = (1 - α^{γ+1}) / ((1 - α)(1 + γ c))` for `α ≠ 1, c ≥ 0`.
3. Exact discrete marginal-benefit optimality condition:
   `S(α, γ + 1, c) ≥ S(α, γ, c) ↔ α^{γ+1}(1 + γ c) ≥ c · Y(α, γ)`
   (and strict version).
4. Exact discrete unimodality identity:
   `M(α, γ + 1, c) - M(α, γ, c) = (α - 1) · α^{γ+1} · (1 + (γ + 1) c) ≤ 0` for `0 ≤ α ≤ 1, c ≥ 0`,
   implying that once `M(α, γ*, c) ≤ 0`, `S(α, γ, c)` is non-increasing for all `γ ≥ γ*`.
-/

namespace SpecDecWienerTemp

theorem specYieldSum_zero (α : Rat) : specYieldSum α 0 = 1 := by
  unfold specYieldSum finSum
  simp [finSumAux, ratPow]
  exact Rat.zero_add 1

theorem specYieldSum_succ (α : Rat) (γ : Nat) :
    specYieldSum α (γ + 1) = specYieldSum α γ + ratPow α (γ + 1) := by
  unfold specYieldSum finSum finSumAux
  rfl

theorem specYieldSum_mul_one_sub (α : Rat) (γ : Nat) :
    (1 - α) * specYieldSum α γ = 1 - ratPow α (γ + 1) := by
  induction γ with
  | zero =>
    rw [specYieldSum_zero]
    simp [ratPow]
  | succ k ih =>
    rw [specYieldSum_succ]
    have hpow : ratPow α (k + 2) = ratPow α (k + 1) * α := rfl
    rw [hpow]
    calc (1 - α) * (specYieldSum α k + ratPow α (k + 1))
        = (1 - α) * specYieldSum α k + (1 - α) * ratPow α (k + 1) := by grind
      _ = (1 - ratPow α (k + 1)) + (1 - α) * ratPow α (k + 1) := by rw [ih]
      _ = 1 - ratPow α (k + 1) * α := by grind

theorem specYieldSum_eq_closed {α : Rat} (hα : α ≠ 1) (γ : Nat) :
    specYieldSum α γ = specYieldClosed α γ := by
  have h1m : 1 - α ≠ 0 := by
    intro h0; exact hα (by grind)
  unfold specYieldClosed
  symm
  rw [rat_div_eq_iff h1m]
  have h := specYieldSum_mul_one_sub α γ
  grind

theorem specYieldSum_at_one (γ : Nat) : specYieldSum 1 γ = (γ : Rat) + 1 := by
  induction γ with
  | zero =>
    rw [specYieldSum_zero]
    grind
  | succ k ih =>
    rw [specYieldSum_succ, ih, ratPow_one, rat_natCast_succ]

theorem one_add_gamma_mul_pos {c : Rat} (hc : (0 : Rat) ≤ c) (γ : Nat) :
    (0 : Rat) < 1 + (γ : Rat) * c :=
  rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (rat_natCast_nonneg γ) hc)

theorem specSpeedup_eq_closed {α c : Rat} (hα : α ≠ 1) (hc : (0 : Rat) ≤ c) (γ : Nat) :
    specSpeedup α γ c = specSpeedupClosed α γ c := by
  have h1m : 1 - α ≠ 0 := by intro h0; exact hα (by grind)
  have hden : 1 + (γ : Rat) * c ≠ 0 := Rat.ne_of_gt (one_add_gamma_mul_pos hc γ)
  have hprod_ne : (1 - α) * (1 + (γ : Rat) * c) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact h1m h
    | inr h => exact hden h
  unfold specSpeedup specSpeedupClosed
  symm
  rw [rat_div_eq_iff hprod_ne]
  have h1 : (specYieldSum α γ / (1 + (γ : Rat) * c)) * ((1 - α) * (1 + (γ : Rat) * c)) =
      (1 - α) * ((specYieldSum α γ / (1 + (γ : Rat) * c)) * (1 + (γ : Rat) * c)) := by grind
  rw [h1, rat_div_mul_cancel hden, specYieldSum_mul_one_sub]

theorem specSpeedup_step_iff {α c : Rat} (hc : (0 : Rat) ≤ c) (γ : Nat) :
    (specSpeedup α γ c ≤ specSpeedup α (γ + 1) c ↔
      c * specYieldSum α γ ≤ ratPow α (γ + 1) * (1 + (γ : Rat) * c)) ∧
    (specSpeedup α γ c < specSpeedup α (γ + 1) c ↔
      c * specYieldSum α γ < ratPow α (γ + 1) * (1 + (γ : Rat) * c)) := by
  have hd0 : (0 : Rat) < 1 + (γ : Rat) * c := one_add_gamma_mul_pos hc γ
  have hd1 : (0 : Rat) < 1 + ((γ + 1 : Nat) : Rat) * c := one_add_gamma_mul_pos hc (γ + 1)
  unfold specSpeedup
  rw [rat_div_le_div_iff hd0 hd1, rat_div_lt_div_iff hd0 hd1, specYieldSum_succ, rat_natCast_succ]
  constructor
  · constructor
    · intro h
      have hsub := rat_sub_nonneg h
      apply rat_le_of_sub_nonneg
      grind
    · intro h
      have hsub := rat_sub_nonneg h
      apply rat_le_of_sub_nonneg
      grind
  · constructor
    · intro h
      have hsub := rat_sub_pos h
      apply rat_lt_of_sub_pos
      grind
    · intro h
      have hsub := rat_sub_pos h
      apply rat_lt_of_sub_pos
      grind

theorem specMargin_step_diff (α c : Rat) (γ : Nat) :
    specMargin α (γ + 1) c - specMargin α γ c =
      (α - 1) * ratPow α (γ + 1) * (1 + ((γ + 1 : Nat) : Rat) * c) := by
  unfold specMargin
  rw [specYieldSum_succ]
  have hpow : ratPow α (γ + 2) = ratPow α (γ + 1) * α := rfl
  rw [hpow, rat_natCast_succ]
  grind

theorem specMargin_antitone {α c : Rat} (hα0 : (0 : Rat) ≤ α) (hα1 : α ≤ 1)
    (hc : (0 : Rat) ≤ c) (γ : Nat) :
    specMargin α (γ + 1) c ≤ specMargin α γ c := by
  apply rat_le_of_sub_nonneg
  have hdiff := specMargin_step_diff α c γ
  have hneg : specMargin α γ c - specMargin α (γ + 1) c =
      (1 - α) * ratPow α (γ + 1) * (1 + ((γ + 1 : Nat) : Rat) * c) := by grind
  rw [hneg]
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (rat_sub_nonneg hα1) (ratPow_nonneg hα0 (γ + 1)))
    (Rat.le_of_lt (one_add_gamma_mul_pos hc (γ + 1)))

theorem specMargin_nonpos_of_ge {α c : Rat} (hα0 : (0 : Rat) ≤ α) (hα1 : α ≤ 1)
    (hc : (0 : Rat) ≤ c) {γ0 : Nat} (h0 : specMargin α γ0 c ≤ 0) :
    ∀ k : Nat, specMargin α (γ0 + k) c ≤ 0 := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ m ih =>
    have hstep := specMargin_antitone hα0 hα1 hc (γ0 + m)
    have heq : γ0 + (m + 1) = (γ0 + m) + 1 := by omega
    rw [heq]
    exact Rat.le_trans hstep ih

theorem specSpeedup_tail_noninc {α c : Rat} (hα0 : (0 : Rat) ≤ α) (hα1 : α ≤ 1)
    (hc : (0 : Rat) ≤ c) {γ0 : Nat} (h0 : specMargin α γ0 c ≤ 0) :
    ∀ k : Nat, specSpeedup α (γ0 + k) c ≤ specSpeedup α γ0 c := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    have hm : specMargin α (γ0 + m) c ≤ 0 := specMargin_nonpos_of_ge hα0 hα1 hc h0 m
    have hstep_le : specSpeedup α ((γ0 + m) + 1) c ≤ specSpeedup α (γ0 + m) c := by
      cases Rat.le_total (a := specSpeedup α ((γ0 + m) + 1) c) (b := specSpeedup α (γ0 + m) c) with
      | inl h => exact h
      | inr h =>
        by_cases heq : specSpeedup α ((γ0 + m) + 1) c = specSpeedup α (γ0 + m) c
        · rw [heq]; exact Rat.le_refl
        · have hlt : specSpeedup α (γ0 + m) c < specSpeedup α ((γ0 + m) + 1) c :=
            Rat.lt_of_le_of_ne h (Ne.symm heq)
          have hpos_m : c * specYieldSum α (γ0 + m) <
              ratPow α ((γ0 + m) + 1) * (1 + ((γ0 + m : Nat) : Rat) * c) :=
            (specSpeedup_step_iff hc (γ0 + m)).2.mp hlt
          have hgt0 : (0 : Rat) < specMargin α (γ0 + m) c := rat_sub_pos hpos_m
          exact False.elim (Rat.not_le.mpr hgt0 hm)
    have heq : γ0 + (m + 1) = (γ0 + m) + 1 := by omega
    rw [heq]
    exact Rat.le_trans hstep_le ih

/-- Headline Theorem 4 (`expected_specdec_yield_and_speedup_exact`). -/
theorem expected_specdec_yield_and_speedup_exact :
    (∀ (α : Rat) (γ : Nat),
      (1 - α) * specYieldSum α γ = 1 - ratPow α (γ + 1) ∧
      (α ≠ 1 → specYieldSum α γ = specYieldClosed α γ) ∧
      specYieldSum 1 γ = (γ : Rat) + 1) ∧
    (∀ (α c : Rat) (γ : Nat), α ≠ 1 → (0 : Rat) ≤ c →
      specSpeedup α γ c = specSpeedupClosed α γ c) ∧
    (∀ (α c : Rat) (γ : Nat), (0 : Rat) ≤ c →
      (specSpeedup α γ c ≤ specSpeedup α (γ + 1) c ↔
        c * specYieldSum α γ ≤ ratPow α (γ + 1) * (1 + (γ : Rat) * c)) ∧
      (specSpeedup α γ c < specSpeedup α (γ + 1) c ↔
        c * specYieldSum α γ < ratPow α (γ + 1) * (1 + (γ : Rat) * c))) ∧
    (∀ (α c : Rat) (γ : Nat),
      specMargin α (γ + 1) c - specMargin α γ c =
        (α - 1) * ratPow α (γ + 1) * (1 + ((γ + 1 : Nat) : Rat) * c)) ∧
    (∀ (α c : Rat) (γ0 : Nat),
      (0 : Rat) ≤ α → α ≤ 1 → (0 : Rat) ≤ c → specMargin α γ0 c ≤ 0 →
      ∀ k : Nat, specSpeedup α (γ0 + k) c ≤ specSpeedup α γ0 c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α γ
    exact ⟨specYieldSum_mul_one_sub α γ, fun h => specYieldSum_eq_closed h γ, specYieldSum_at_one γ⟩
  · intro α c γ hα hc
    exact specSpeedup_eq_closed hα hc γ
  · intro α c γ hc
    exact specSpeedup_step_iff hc γ
  · intro α c γ
    exact specMargin_step_diff α c γ
  · intro α c γ0 hα0 hα1 hc h0
    exact specSpeedup_tail_noninc hα0 hα1 hc h0

end SpecDecWienerTemp
