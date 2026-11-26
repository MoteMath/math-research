/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecWienerTemp.SpecDecYield

/-!
# Sub-4-Bit Self-Speculative Dominance over `FP8` and `BF16`

Proves Theorem 5 (`sub4bit_self_speculative_dominance_over_fp8_bf16`):
1. Universal bandwidth-cost ceilings:
   - `Y(α, γ) ≤ γ + 1` for all `0 ≤ α ≤ 1` and `γ : Nat`.
   - For `BF16` self-speculation (`c ≥ 1`), `S(α, γ, c) ≤ 1` for ALL `0 ≤ α ≤ 1, γ : Nat`.
   - For any draft with `0 < c < 1`, `S(α, γ, c) < 1 / c` for ALL `0 ≤ α ≤ 1, γ : Nat`.
   - In particular, self-speculative `FP8` (`b = 8, c_0 = 1, c = 1/2`) satisfies
     `S(α, γ, 1/2) < 2` universally for ALL `0 ≤ α ≤ 1` and ALL `γ : Nat`.
2. Universal algebraic dominance criterion under `c(b) = c_0 · b / 16`:
   `S(α_1, γ_1, c(b_1)) > S(α_2, γ_2, c(b_2)) ↔ Y_1 (16 + γ_2 c_0 b_2) > Y_2 (16 + γ_1 c_0 b_1)`.
3. Concrete certified self-speculative (`c_0 = 1`) and `c_0 = 1/4` rational dominance bounds
   matching Wave 32A `REPORT.md`.
-/

namespace SpecDecWienerTemp

theorem specYieldSum_le_succ {α : Rat} (hα0 : (0 : Rat) ≤ α) (hα1 : α ≤ 1) (γ : Nat) :
    specYieldSum α γ ≤ (γ : Rat) + 1 := by
  induction γ with
  | zero =>
    rw [specYieldSum_zero]
    have h0 : ((0 : Nat) : Rat) + 1 = 1 := by grind
    rw [h0]
    exact Rat.le_refl
  | succ k ih =>
    rw [specYieldSum_succ]
    have hpow : ratPow α (k + 1) ≤ 1 := ratPow_le_one hα0 hα1 (k + 1)
    rw [rat_natCast_succ]
    exact rat_add_le_add ih hpow

theorem specSpeedup_le_one_of_cost_ge_one {α c : Rat}
    (hα0 : (0 : Rat) ≤ α) (hα1 : α ≤ 1) (hc1 : (1 : Rat) ≤ c) (γ : Nat) :
    specSpeedup α γ c ≤ 1 := by
  have hc0 : (0 : Rat) ≤ c := Rat.le_trans (by decide : (0 : Rat) ≤ 1) hc1
  have hden : (0 : Rat) < 1 + (γ : Rat) * c := one_add_gamma_mul_pos hc0 γ
  unfold specSpeedup
  apply rat_div_le_of_mul_le hden
  rw [Rat.one_mul]
  have hy := specYieldSum_le_succ hα0 hα1 γ
  have hgc : (γ : Rat) ≤ (γ : Rat) * c := by
    have h := rat_mul_le_mul_of_nonneg_left hc1 (rat_natCast_nonneg γ)
    rw [Rat.mul_one] at h
    exact h
  have hle : (γ : Rat) + 1 ≤ 1 + (γ : Rat) * c := by
    have h := rat_add_le_add hgc (Rat.le_refl (a := (1 : Rat)))
    grind
  exact Rat.le_trans hy hle

theorem specSpeedup_lt_inv_cost {α c : Rat}
    (hα0 : (0 : Rat) ≤ α) (hα1 : α ≤ 1) (hc0 : (0 : Rat) < c) (hc1 : c < 1) (γ : Nat) :
    specSpeedup α γ c < 1 / c := by
  have hden : (0 : Rat) < 1 + (γ : Rat) * c := one_add_gamma_mul_pos (Rat.le_of_lt hc0) γ
  unfold specSpeedup
  rw [rat_div_lt_div_iff hden hc0, Rat.one_mul]
  have hy : specYieldSum α γ * c ≤ ((γ : Rat) + 1) * c :=
    rat_mul_le_mul_of_nonneg_right (specYieldSum_le_succ hα0 hα1 γ) (Rat.le_of_lt hc0)
  have hlt : ((γ : Rat) + 1) * c < 1 + (γ : Rat) * c := by
    apply rat_lt_of_sub_pos
    have : (1 + (γ : Rat) * c) - ((γ : Rat) + 1) * c = 1 - c := by grind
    rw [this]
    exact rat_sub_pos hc1
  exact rat_lt_of_le_of_lt hy hlt

theorem draftCost_dominance_iff {α1 α2 b1 b2 c0 : Rat} {γ1 γ2 : Nat}
    (hc0 : (0 : Rat) ≤ c0) (hb1 : (0 : Rat) ≤ b1) (hb2 : (0 : Rat) ≤ b2) :
    specSpeedup α2 γ2 (draftCost c0 b2) < specSpeedup α1 γ1 (draftCost c0 b1) ↔
      specYieldSum α2 γ2 * (16 + (γ1 : Rat) * c0 * b1) <
      specYieldSum α1 γ1 * (16 + (γ2 : Rat) * c0 * b2) := by
  have hc1 : (0 : Rat) ≤ draftCost c0 b1 :=
    rat_div_nonneg (Rat.mul_nonneg hc0 hb1) (by decide)
  have hc2 : (0 : Rat) ≤ draftCost c0 b2 :=
    rat_div_nonneg (Rat.mul_nonneg hc0 hb2) (by decide)
  have hd1 : (0 : Rat) < 1 + (γ1 : Rat) * draftCost c0 b1 := one_add_gamma_mul_pos hc1 γ1
  have hd2 : (0 : Rat) < 1 + (γ2 : Rat) * draftCost c0 b2 := one_add_gamma_mul_pos hc2 γ2
  unfold specSpeedup
  rw [rat_div_lt_div_iff hd2 hd1]
  have h16_pos : (0 : Rat) < 16 := by decide
  have h16_ne : (16 : Rat) ≠ 0 := by decide
  have hm1 : (1 + (γ1 : Rat) * draftCost c0 b1) * 16 = 16 + (γ1 : Rat) * c0 * b1 := by
    unfold draftCost
    have hd : ((c0 * b1) / 16) * 16 = c0 * b1 := rat_div_mul_cancel h16_ne
    calc (1 + (γ1 : Rat) * ((c0 * b1) / 16)) * 16
        = 16 + (γ1 : Rat) * (((c0 * b1) / 16) * 16) := by grind
      _ = 16 + (γ1 : Rat) * (c0 * b1) := by rw [hd]
      _ = 16 + (γ1 : Rat) * c0 * b1 := by grind
  have hm2 : (1 + (γ2 : Rat) * draftCost c0 b2) * 16 = 16 + (γ2 : Rat) * c0 * b2 := by
    unfold draftCost
    have hd : ((c0 * b2) / 16) * 16 = c0 * b2 := rat_div_mul_cancel h16_ne
    calc (1 + (γ2 : Rat) * ((c0 * b2) / 16)) * 16
        = 16 + (γ2 : Rat) * (((c0 * b2) / 16) * 16) := by grind
      _ = 16 + (γ2 : Rat) * (c0 * b2) := by rw [hd]
      _ = 16 + (γ2 : Rat) * c0 * b2 := by grind
  constructor
  · intro h
    have hmul := rat_mul_lt_mul_of_pos_right h h16_pos
    have hL : specYieldSum α2 γ2 * (1 + (γ1 : Rat) * draftCost c0 b1) * 16 =
        specYieldSum α2 γ2 * (16 + (γ1 : Rat) * c0 * b1) := by rw [Rat.mul_assoc, hm1]
    have hR : specYieldSum α1 γ1 * (1 + (γ2 : Rat) * draftCost c0 b2) * 16 =
        specYieldSum α1 γ1 * (16 + (γ2 : Rat) * c0 * b2) := by rw [Rat.mul_assoc, hm2]
    rw [hL, hR] at hmul
    exact hmul
  · intro h
    apply rat_lt_of_mul_pos_right h16_pos
    have hL : specYieldSum α2 γ2 * (1 + (γ1 : Rat) * draftCost c0 b1) * 16 =
        specYieldSum α2 γ2 * (16 + (γ1 : Rat) * c0 * b1) := by rw [Rat.mul_assoc, hm1]
    have hR : specYieldSum α1 γ1 * (1 + (γ2 : Rat) * draftCost c0 b2) * 16 =
        specYieldSum α1 γ1 * (16 + (γ2 : Rat) * c0 * b2) := by rw [Rat.mul_assoc, hm2]
    rw [hL, hR]
    exact h

/-! ### Exact Integer-Fraction Reduction for Closed-Form Speedup -/

theorem rat_intCast_natCast (n : Nat) : ((n : Int) : Rat) = (n : Rat) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Int.natCast_add, Rat.intCast_add, ih, rat_natCast_succ]
    rfl

/-- Exact integer-fraction formula for `specSpeedup (a / b) γ (cn / cd)`:
    `specSpeedup (a/b) γ (cn/cd) = ((b^(γ+1) - a^(γ+1)) * b * cd) / (b^(γ+1) * (b - a) * (cd + γ * cn))`. -/
theorem specSpeedup_int_frac (a b cn cd : Int) (γ : Nat)
    (hb : (0 : Int) < b) (hab : a < b) (hcn : (0 : Int) ≤ cn) (hcd : (0 : Int) < cd) :
    specSpeedup ((a : Rat) / (b : Rat)) γ ((cn : Rat) / (cd : Rat)) =
      (((b ^ (γ + 1) - a ^ (γ + 1)) * b * cd : Int) : Rat) /
      (((b ^ (γ + 1) * (b - a) * (cd + (γ : Int) * cn) : Int) : Rat)) := by
  have hb_r : (0 : Rat) < (b : Rat) := rat_intCast_lt hb
  have hcd_r : (0 : Rat) < (cd : Rat) := rat_intCast_lt hcd
  have hc_nn : (0 : Rat) ≤ (cn : Rat) / (cd : Rat) :=
    rat_div_nonneg (rat_intCast_le hcn) hcd_r
  have hα_ne1 : (a : Rat) / (b : Rat) ≠ 1 := by
    intro heq
    have h1 := (rat_div_eq_iff (Rat.ne_of_gt hb_r)).mp heq
    rw [Rat.one_mul] at h1
    have hlt : (a : Rat) < (b : Rat) := rat_intCast_lt hab
    rw [h1] at hlt
    exact Rat.lt_irrefl hlt
  rw [specSpeedup_eq_closed hα_ne1 hc_nn γ]
  unfold specSpeedupClosed
  rw [ratPow_div a b (Rat.ne_of_gt hb_r) (γ + 1)]
  have hbn_pos : (0 : Int) < b ^ (γ + 1) := Int.pow_pos hb
  have hbn_r : (0 : Rat) < ((b ^ (γ + 1) : Int) : Rat) := rat_intCast_lt hbn_pos
  have hbn_ne : ((b ^ (γ + 1) : Int) : Rat) ≠ 0 := Rat.ne_of_gt hbn_r
  have hbma_pos : (0 : Int) < b - a := by omega
  have hcdg_pos : (0 : Int) < cd + (γ : Int) * cn := by
    have hmul : (0 : Int) ≤ (γ : Int) * cn := Int.mul_nonneg (Int.natCast_nonneg γ) hcn
    omega
  have hden_int_pos : (0 : Int) < b ^ (γ + 1) * (b - a) * (cd + (γ : Int) * cn) :=
    Int.mul_pos (Int.mul_pos hbn_pos hbma_pos) hcdg_pos
  have hden_r_ne : (((b ^ (γ + 1) * (b - a) * (cd + (γ : Int) * cn) : Int) : Rat)) ≠ 0 :=
    Rat.ne_of_gt (rat_intCast_lt hden_int_pos)
  have h1mα : (1 : Rat) - (a : Rat) / (b : Rat) = ((b - a : Int) : Rat) / (b : Rat) := by
    symm
    rw [rat_div_eq_iff (Rat.ne_of_gt hb_r), Rat.intCast_sub]
    have h1 : (1 - (a : Rat) / (b : Rat)) * (b : Rat) = (b : Rat) - ((a : Rat) / (b : Rat)) * (b : Rat) := by grind
    rw [h1, rat_div_mul_cancel (Rat.ne_of_gt hb_r)]
  have h1pγc : (1 : Rat) + (γ : Rat) * ((cn : Rat) / (cd : Rat)) =
      ((cd + (γ : Int) * cn : Int) : Rat) / (cd : Rat) := by
    symm
    rw [rat_div_eq_iff (Rat.ne_of_gt hcd_r), Rat.intCast_add, Rat.intCast_mul, rat_intCast_natCast]
    have h1 : (1 + (γ : Rat) * ((cn : Rat) / (cd : Rat))) * (cd : Rat) =
        (cd : Rat) + (γ : Rat) * (((cn : Rat) / (cd : Rat)) * (cd : Rat)) := by grind
    rw [h1, rat_div_mul_cancel (Rat.ne_of_gt hcd_r)]
  have hnum : (1 : Rat) - ((a ^ (γ + 1) : Int) : Rat) / ((b ^ (γ + 1) : Int) : Rat) =
      ((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) / ((b ^ (γ + 1) : Int) : Rat) := by
    symm
    rw [rat_div_eq_iff hbn_ne, Rat.intCast_sub]
    have h1 : (1 - ((a ^ (γ + 1) : Int) : Rat) / ((b ^ (γ + 1) : Int) : Rat)) * ((b ^ (γ + 1) : Int) : Rat) =
        ((b ^ (γ + 1) : Int) : Rat) -
          (((a ^ (γ + 1) : Int) : Rat) / ((b ^ (γ + 1) : Int) : Rat)) * ((b ^ (γ + 1) : Int) : Rat) := by grind
    rw [h1, rat_div_mul_cancel hbn_ne]
  rw [hnum, h1mα, h1pγc]
  have hbma_ne : ((b - a : Int) : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt hbma_pos)
  have hcdg_ne : ((cd + (γ : Int) * cn : Int) : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt hcdg_pos)
  have hprod_ne : (((b - a : Int) : Rat) / (b : Rat)) *
      (((cd + (γ : Int) * cn : Int) : Rat) / (cd : Rat)) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h =>
      have := (rat_div_eq_iff (Rat.ne_of_gt hb_r)).mp h
      rw [Rat.zero_mul] at this
      exact hbma_ne this
    | inr h =>
      have := (rat_div_eq_iff (Rat.ne_of_gt hcd_r)).mp h
      rw [Rat.zero_mul] at this
      exact hcdg_ne this
  rw [rat_div_eq_iff hprod_ne]
  apply rat_eq_of_mul_eq_mul_right hden_r_ne
  rw [Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_mul]
  have hL : (((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) / ((b ^ (γ + 1) : Int) : Rat)) *
      (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat)) =
      ((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat) := by
    calc (((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) / ((b ^ (γ + 1) : Int) : Rat)) *
          (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat))
        = ((((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) / ((b ^ (γ + 1) : Int) : Rat)) * ((b ^ (γ + 1) : Int) : Rat)) *
          (((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat)) := by grind
      _ = ((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat) := by
          rw [rat_div_mul_cancel hbn_ne]; grind
  have hden_eq : (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat)) =
      (((b ^ (γ + 1) * (b - a) * (cd + (γ : Int) * cn) : Int) : Rat)) := by
    rw [Rat.intCast_mul, Rat.intCast_mul]
  have hR1 :
      ((((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * (b : Rat) * (cd : Rat)) /
        (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat))) *
      ((((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat))) =
      ((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * (b : Rat) * (cd : Rat) := by
    rw [hden_eq]
    exact rat_div_mul_cancel hden_r_ne
  rw [hL]
  have hRHS_simp :
      ((((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * (b : Rat) * (cd : Rat)) /
        (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat))) *
      ((((b - a : Int) : Rat) / (b : Rat)) * (((cd + (γ : Int) * cn : Int) : Rat) / (cd : Rat))) *
      (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat)) =
      ((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat) := by
    calc ((((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * (b : Rat) * (cd : Rat)) /
            (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat))) *
          ((((b - a : Int) : Rat) / (b : Rat)) * (((cd + (γ : Int) * cn : Int) : Rat) / (cd : Rat))) *
          (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat))
        = ((((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * (b : Rat) * (cd : Rat)) /
            (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat)) *
           (((b ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat))) *
          ((((b - a : Int) : Rat) / (b : Rat)) * (((cd + (γ : Int) * cn : Int) : Rat) / (cd : Rat))) := by grind
      _ = (((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * (b : Rat) * (cd : Rat)) *
          ((((b - a : Int) : Rat) / (b : Rat)) * (((cd + (γ : Int) * cn : Int) : Rat) / (cd : Rat))) := by rw [hR1]
      _ = ((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) *
          ((((b - a : Int) : Rat) / (b : Rat)) * (b : Rat)) *
          ((((cd + (γ : Int) * cn : Int) : Rat) / (cd : Rat)) * (cd : Rat)) := by grind
      _ = ((b ^ (γ + 1) - a ^ (γ + 1) : Int) : Rat) * ((b - a : Int) : Rat) * ((cd + (γ : Int) * cn : Int) : Rat) := by
          rw [rat_div_mul_cancel (Rat.ne_of_gt hb_r), rat_div_mul_cancel (Rat.ne_of_gt hcd_r)]
  exact hRHS_simp.symm

/-! ### Concrete Certified Self-Speculative (`c_0 = 1`) and `c_0 = 1/4` Dominance Bounds -/

theorem int2_self_spec_speedup_bounds :
    (2976 / 1000 : Rat) < specSpeedup (89214 / 100000) 8 (draftCost 1 2) ∧
    specSpeedup (89214 / 100000) 8 (draftCost 1 2) < 2977 / 1000 := by
  have hc : draftCost 1 2 = (1 : Rat) / 8 := by unfold draftCost; grind
  rw [hc]
  have h := specSpeedup_int_frac 89214 100000 1 8 8 (by decide) (by decide) (by decide) (by decide)
  change (2976 / 1000 : Rat) < specSpeedup ((89214 : Int) / (100000 : Int)) 8 ((1 : Int) / (8 : Int)) ∧
    specSpeedup ((89214 : Int) / (100000 : Int)) 8 ((1 : Int) / (8 : Int)) < (2977 / 1000 : Rat)
  rw [h]
  exact ⟨rat_div_lt_div_of_int (by decide) (by decide) (by decide),
         rat_div_lt_div_of_int (by decide) (by decide) (by decide)⟩

theorem int3_self_spec_speedup_bounds :
    (2520 / 1000 : Rat) < specSpeedup (90707 / 100000) 7 (draftCost 1 3) ∧
    specSpeedup (90707 / 100000) 7 (draftCost 1 3) < 2521 / 1000 := by
  have hc : draftCost 1 3 = (3 : Rat) / 16 := by unfold draftCost; grind
  rw [hc]
  have h := specSpeedup_int_frac 90707 100000 3 16 7 (by decide) (by decide) (by decide) (by decide)
  change (2520 / 1000 : Rat) < specSpeedup ((90707 : Int) / (100000 : Int)) 7 ((3 : Int) / (16 : Int)) ∧
    specSpeedup ((90707 : Int) / (100000 : Int)) 7 ((3 : Int) / (16 : Int)) < (2521 / 1000 : Rat)
  rw [h]
  exact ⟨rat_div_lt_div_of_int (by decide) (by decide) (by decide),
         rat_div_lt_div_of_int (by decide) (by decide) (by decide)⟩

theorem int4_self_spec_speedup_bounds :
    (2508 / 1000 : Rat) < specSpeedup (95375 / 100000) 10 (draftCost 1 4) ∧
    specSpeedup (95375 / 100000) 10 (draftCost 1 4) < 2509 / 1000 := by
  have hc : draftCost 1 4 = (1 : Rat) / 4 := by unfold draftCost; grind
  rw [hc]
  have h := specSpeedup_int_frac 95375 100000 1 4 10 (by decide) (by decide) (by decide) (by decide)
  change (2508 / 1000 : Rat) < specSpeedup ((95375 : Int) / (100000 : Int)) 10 ((1 : Int) / (4 : Int)) ∧
    specSpeedup ((95375 : Int) / (100000 : Int)) 10 ((1 : Int) / (4 : Int)) < (2509 / 1000 : Rat)
  rw [h]
  exact ⟨rat_div_lt_div_of_int (by decide) (by decide) (by decide),
         rat_div_lt_div_of_int (by decide) (by decide) (by decide)⟩

theorem fp8_self_spec_speedup_upper :
    specSpeedup (98628 / 100000) 14 (draftCost 1 8) < 176 / 100 := by
  have hc : draftCost 1 8 = (1 : Rat) / 2 := by unfold draftCost; grind
  rw [hc]
  have h := specSpeedup_int_frac 98628 100000 1 2 14 (by decide) (by decide) (by decide) (by decide)
  change specSpeedup ((98628 : Int) / (100000 : Int)) 14 ((1 : Int) / (2 : Int)) < (176 / 100 : Rat)
  rw [h]
  exact rat_div_lt_div_of_int (by decide) (by decide) (by decide)

theorem int4_quarter_cost_beats_fp8 :
    (6 : Rat) < specSpeedup (95375 / 100000) 20 (draftCost (1 / 4) 4) ∧
    specSpeedup (98628 / 100000) 26 (draftCost (1 / 4) 8) < 54 / 10 := by
  have hc4 : draftCost (1 / 4) 4 = (1 : Rat) / 16 := by unfold draftCost; grind
  have hc8 : draftCost (1 / 4) 8 = (1 : Rat) / 8 := by unfold draftCost; grind
  rw [hc4, hc8]
  have h4 := specSpeedup_int_frac 95375 100000 1 16 20 (by decide) (by decide) (by decide) (by decide)
  have h8 := specSpeedup_int_frac 98628 100000 1 8 26 (by decide) (by decide) (by decide) (by decide)
  have h6 : (6 : Rat) = ((6 : Int) : Rat) / ((1 : Int) : Rat) := by grind
  rw [h6]
  change ((6 : Int) : Rat) / ((1 : Int) : Rat) <
      specSpeedup ((95375 : Int) / (100000 : Int)) 20 ((1 : Int) / (16 : Int)) ∧
    specSpeedup ((98628 : Int) / (100000 : Int)) 26 ((1 : Int) / (8 : Int)) <
      ((54 : Int) : Rat) / ((10 : Int) : Rat)
  rw [h4, h8]
  exact ⟨rat_div_lt_div_of_int (by decide) (by decide) (by decide),
         rat_div_lt_div_of_int (by decide) (by decide) (by decide)⟩

/-- Headline Theorem 5 (`sub4bit_self_speculative_dominance_over_fp8_bf16`). -/
theorem sub4bit_self_speculative_dominance_over_fp8_bf16 :
    (∀ (α : Rat) (γ : Nat), (0 : Rat) ≤ α → α ≤ 1 →
      specSpeedup α γ (draftCost 1 16) ≤ 1 ∧
      specSpeedup α γ (draftCost 1 8) < 2) ∧
    (∀ (α c : Rat) (γ : Nat), (0 : Rat) ≤ α → α ≤ 1 → (0 : Rat) < c → c < 1 →
      specSpeedup α γ c < 1 / c) ∧
    (∀ (α1 α2 b1 b2 c0 : Rat) (γ1 γ2 : Nat),
      (0 : Rat) ≤ c0 → (0 : Rat) ≤ b1 → (0 : Rat) ≤ b2 →
      (specSpeedup α2 γ2 (draftCost c0 b2) < specSpeedup α1 γ1 (draftCost c0 b1) ↔
        specYieldSum α2 γ2 * (16 + (γ1 : Rat) * c0 * b1) <
        specYieldSum α1 γ1 * (16 + (γ2 : Rat) * c0 * b2))) ∧
    ((2976 / 1000 : Rat) < specSpeedup (89214 / 100000) 8 (draftCost 1 2) ∧
     specSpeedup (89214 / 100000) 8 (draftCost 1 2) < 2977 / 1000 ∧
     (2520 / 1000 : Rat) < specSpeedup (90707 / 100000) 7 (draftCost 1 3) ∧
     specSpeedup (90707 / 100000) 7 (draftCost 1 3) < 2521 / 1000 ∧
     (2508 / 1000 : Rat) < specSpeedup (95375 / 100000) 10 (draftCost 1 4) ∧
     specSpeedup (95375 / 100000) 10 (draftCost 1 4) < 2509 / 1000 ∧
     specSpeedup (98628 / 100000) 14 (draftCost 1 8) < 176 / 100 ∧
     (∀ (α : Rat) (γ : Nat), (0 : Rat) ≤ α → α ≤ 1 →
       specSpeedup α γ (draftCost 1 8) < specSpeedup (89214 / 100000) 8 (draftCost 1 2) ∧
       specSpeedup α γ (draftCost 1 8) < specSpeedup (90707 / 100000) 7 (draftCost 1 3) ∧
       specSpeedup α γ (draftCost 1 8) < specSpeedup (95375 / 100000) 10 (draftCost 1 4))) ∧
    ((6 : Rat) < specSpeedup (95375 / 100000) 20 (draftCost (1 / 4) 4) ∧
     specSpeedup (98628 / 100000) 26 (draftCost (1 / 4) 8) < 54 / 10) := by
  have h16 : draftCost 1 16 = 1 := by unfold draftCost; grind
  have h8 : draftCost 1 8 = 1 / 2 := by unfold draftCost; grind
  have hinv2 : (1 : Rat) / (1 / 2) = 2 := by grind
  have ⟨hi2lo, hi2hi⟩ := int2_self_spec_speedup_bounds
  have ⟨hi3lo, hi3hi⟩ := int3_self_spec_speedup_bounds
  have ⟨hi4lo, hi4hi⟩ := int4_self_spec_speedup_bounds
  have hfp8 := fp8_self_spec_speedup_upper
  have ⟨hq1, hq2⟩ := int4_quarter_cost_beats_fp8
  refine ⟨?_, ?_, ?_, ?_, ⟨hq1, hq2⟩⟩
  · intro α γ hα0 hα1
    rw [h16, h8]
    refine ⟨specSpeedup_le_one_of_cost_ge_one hα0 hα1 Rat.le_refl γ, ?_⟩
    have hlt := specSpeedup_lt_inv_cost (c := (1 / 2 : Rat)) hα0 hα1 (by grind) (by grind) γ
    rw [hinv2] at hlt
    exact hlt
  · intro α c γ hα0 hα1 hc0 hc1
    exact specSpeedup_lt_inv_cost hα0 hα1 hc0 hc1 γ
  · intro α1 α2 b1 b2 c0 γ1 γ2 hc0 hb1 hb2
    exact draftCost_dominance_iff hc0 hb1 hb2
  · refine ⟨hi2lo, hi2hi, hi3lo, hi3hi, hi4lo, hi4hi, hfp8, ?_⟩
    intro α γ hα0 hα1
    have hfp8_lt2 : specSpeedup α γ (draftCost 1 8) < 2 := by
      rw [h8]
      have hlt := specSpeedup_lt_inv_cost (c := (1 / 2 : Rat)) hα0 hα1 (by grind) (by grind) γ
      rw [hinv2] at hlt
      exact hlt
    exact ⟨rat_lt_trans hfp8_lt2 (rat_lt_trans (by grind : (2 : Rat) < 2976 / 1000) hi2lo),
           rat_lt_trans hfp8_lt2 (rat_lt_trans (by grind : (2 : Rat) < 2520 / 1000) hi3lo),
           rat_lt_trans hfp8_lt2 (rat_lt_trans (by grind : (2 : Rat) < 2508 / 1000) hi4lo)⟩

end SpecDecWienerTemp
