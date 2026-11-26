/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp.Bf16Freeze

/-!
# Theorem 4: Exact Equivalence of Lazy-Stamp AdamW to Dense Absent-Step Updates

Pure-`Init` exact rational inductive proofs that for any absent interval of `Δ` steps
(`g_{t+1} = ... = g_{t+Δ} = 0`):
1. `denseAbsentSteps β1 β2 η lam Δ s = lazyStampJump β1 β2 η lam Δ s`
   for all `β1, β2, η, lam : Rat`, `s : AdamWState`, and `Δ : Nat`.
2. Semigroup composition across consecutive absent intervals `Δ1, Δ2`.
3. Exact equivalence of `O(log Δ)` binary exponentiation `lazyStampJumpFast` to `lazyStampJump`.
4. Elimination of intermediate per-step `BF16` decay freeze: at `β2 = 999/1000`, a single
   lazy jump of just `Δ = 4` steps clears the `BF16` half-ULP for **100% of all normal BF16
   values** (`rneFloatBelow 7 e m (ratPow (999/1000) 4 * normalFloat 7 e m) ≠ normalFloat 7 e m`).
-/

namespace EmbedZipfLazyStamp

theorem denseAbsentSteps_eq_lazyStampJump (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState) :
    denseAbsentSteps β1 β2 η lam Δ s = lazyStampJump β1 β2 η lam Δ s := by
  induction Δ generalizing s with
  | zero =>
    unfold denseAbsentSteps lazyStampJump ratPow
    cases s with
    | mk w m v =>
      simp only [Rat.one_mul]
  | succ k ih =>
    simp only [denseAbsentSteps, ih, lazyStampJump, denseAbsentStep, ratPow]
    cases s with
    | mk w m v =>
      simp only [AdamWState.mk.injEq]
      exact ⟨by grind, by grind, by grind⟩

theorem lazyStampJump_add (β1 β2 η lam : Rat) (Δ1 Δ2 : Nat) (s : AdamWState) :
    lazyStampJump β1 β2 η lam Δ2 (lazyStampJump β1 β2 η lam Δ1 s) =
      lazyStampJump β1 β2 η lam (Δ1 + Δ2) s := by
  unfold lazyStampJump
  rw [ratPow_add, ratPow_add, ratPow_add]
  cases s with
  | mk w m v =>
    simp only [AdamWState.mk.injEq]
    exact ⟨by grind, by grind, by grind⟩

theorem ratPowFast_eq_ratPow (x : Rat) (n : Nat) : ratPowFast x n = ratPow x n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold ratPowFast
    by_cases hn0 : n = 0
    · subst hn0; simp [ratPow]
    · simp only [hn0, ↓reduceIte]
      have hhalf_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
      rw [ih (n / 2) hhalf_lt]
      by_cases heven : n % 2 = 0
      · simp only [heven, ↓reduceIte]
        rw [← ratPow_add]
        have hsum : n / 2 + n / 2 = n := by omega
        rw [hsum]
      · simp only [heven, ↓reduceIte]
        have hassoc : x * ratPow x (n / 2) * ratPow x (n / 2) =
            x * (ratPow x (n / 2) * ratPow x (n / 2)) := by grind
        rw [hassoc, ← ratPow_add]
        have hsum : n = (n / 2 + n / 2) + 1 := by omega
        conv => rhs; rw [hsum]
        rfl

theorem lazyStampJumpFast_eq_lazyStampJump (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState) :
    lazyStampJumpFast β1 β2 η lam Δ s = lazyStampJump β1 β2 η lam Δ s := by
  unfold lazyStampJumpFast lazyStampJump
  rw [ratPowFast_eq_ratPow, ratPowFast_eq_ratPow, ratPowFast_eq_ratPow]

theorem bf16_lazy_jump_4_breaks_freeze (e : Int) (m : Nat) (hm : m < 128) :
    rneFloatBelow 7 e m (ratPow (999 / 1000 : Rat) 4 * normalFloat 7 e m) ≠
      normalFloat 7 e m := by
  let β4 : Rat := ratPow (999 / 1000 : Rat) 4
  have h1mβ4_eq : (1 : Rat) - β4 = 3994003999 / 1000000000000 := by
    change (1 : Rat) - (999 / 1000 : Rat) * ((999 / 1000) * ((999 / 1000) * ((999 / 1000) * 1))) =
      3994003999 / 1000000000000
    grind
  have hlo_256 : (1 / 256 : Rat) < 1 - β4 := by
    rw [h1mβ4_eq]
    apply rat_lt_of_mul_pos_right (c := (256000000000000 : Rat)) (by decide)
    have ha : (1 / 256 : Rat) * 256000000000000 = 1000000000000 := by grind
    have hb : (3994003999 / 1000000000000 : Rat) * 256000000000000 = 1022465023744 := by grind
    rw [ha, hb]; decide
  have hhi_128 : 1 - β4 < 1 / 128 := by
    rw [h1mβ4_eq]
    apply rat_lt_of_mul_pos_right (c := (128000000000000 : Rat)) (by decide)
    have ha : (3994003999 / 1000000000000 : Rat) * 128000000000000 = 511232511872 := by grind
    have hb : (1 / 128 : Rat) * 128000000000000 = 1000000000000 := by grind
    rw [ha, hb]; decide
  unfold rneFloatBelow
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte]
    let u : Rat := pow2Int (e - 1 - ((7 : Nat) : Int))
    have hu_pos : (0 : Rat) < u := pow2Int_pos _
    have hv_eq : normalFloat 7 e 0 = ((256 : Nat) : Rat) * u := by
      unfold normalFloat
      have hpow : pow2Int (e - ((7 : Nat) : Int)) = 2 * u := by
        have : e - ((7 : Nat) : Int) = (e - 1 - ((7 : Nat) : Int)) + 1 := by omega
        rw [this, pow2Int_add_one]
      rw [hpow]
      have h128 : ((2 ^ 7 + 0 : Nat) : Rat) = 128 := rfl
      have h256 : ((256 : Nat) : Rat) = 256 := rfl
      rw [h128, h256]; grind
    have hlo_u : u < (1 - β4) * normalFloat 7 e 0 := by
      rw [hv_eq]
      have h256 : ((256 : Nat) : Rat) = 256 := rfl
      rw [h256]
      have hmul := rat_mul_lt_mul_of_pos_right hlo_256 (rat_mul_pos (by decide : (0 : Rat) < 256) hu_pos)
      have hlhs : (1 / 256 : Rat) * (256 * u) = u := by grind
      rw [hlhs] at hmul
      exact hmul
    have hhi_2u : (1 - β4) * normalFloat 7 e 0 < 2 * u := by
      rw [hv_eq]
      have h256 : ((256 : Nat) : Rat) = 256 := rfl
      rw [h256]
      have hmul := rat_mul_lt_mul_of_pos_right hhi_128 (rat_mul_pos (by decide : (0 : Rat) < 256) hu_pos)
      have hrhs : (1 / 128 : Rat) * (256 * u) = 2 * u := by grind
      rw [hrhs] at hmul
      exact hmul
    have hmid : (1 - β4) * normalFloat 7 e 0 < (3 / 2 : Rat) * u := by
      rw [hv_eq]
      have h256 : ((256 : Nat) : Rat) = 256 := rfl
      rw [h256]
      have hlt : 1 - β4 < 3 / 512 := by
        rw [h1mβ4_eq]
        apply rat_lt_of_mul_pos_right (c := (512000000000000 : Rat)) (by decide)
        have ha : (3994003999 / 1000000000000 : Rat) * 512000000000000 = 2044930047488 := by grind
        have hb : (3 / 512 : Rat) * 512000000000000 = 3000000000000 := by grind
        rw [ha, hb]; decide
      have hmul := rat_mul_lt_mul_of_pos_right hlt (rat_mul_pos (by decide : (0 : Rat) < 256) hu_pos)
      have hrhs : (3 / 512 : Rat) * (256 * u) = (3 / 2 : Rat) * u := by grind
      rw [hrhs] at hmul
      exact hmul
    have hsplit : β4 * normalFloat 7 e 0 = ((255 : Int) : Rat) * u + (u - (1 - β4) * normalFloat 7 e 0) := by
      have h255 : ((255 : Int) : Rat) = 255 := rfl
      have h256 : ((256 : Nat) : Rat) = 256 := rfl
      rw [h255]
      have hv2 : normalFloat 7 e 0 = 256 * u := by rw [hv_eq, h256]
      grind
    have hdw : ratAbs (u - (1 - β4) * normalFloat 7 e 0) < u / 2 := by
      rw [ratAbs_lt_iff]
      constructor
      · have := rat_sub_pos hmid
        have : (0 : Rat) < (u - (1 - β4) * normalFloat 7 e 0) - (-(u / 2)) := by grind
        exact rat_lt_of_sub_pos this
      · have := rat_sub_pos hlo_u
        have hneg : u - (1 - β4) * normalFloat 7 e 0 < 0 := by
          have : (0 : Rat) < 0 - (u - (1 - β4) * normalFloat 7 e 0) := by grind
          exact rat_lt_of_sub_pos this
        exact rat_lt_trans hneg (rat_div_pos hu_pos (by decide))
    rw [hsplit, rneGrid_flush_strict 255 u _ hu_pos hdw, hv_eq]
    intro heq
    have h255 : ((255 : Int) : Rat) = 255 := rfl
    have h256 : ((256 : Nat) : Rat) = 256 := rfl
    rw [h255, h256] at heq
    have hu0 : u = 0 := by grind
    exact Rat.ne_of_gt hu_pos hu0
  · simp only [hm0, ↓reduceIte]
    let u : Rat := pow2Int (e - ((7 : Nat) : Int))
    have hu_pos : (0 : Rat) < u := pow2Int_pos _
    have hv_eq : normalFloat 7 e m = (((128 + m : Nat) : Int) : Rat) * u := rfl
    have hge128 : (128 : Rat) * u ≤ normalFloat 7 e m := by
      rw [hv_eq]
      apply rat_mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hu_pos)
      have h128 : (128 : Rat) = ((128 : Int) : Rat) := rfl
      rw [h128]
      exact Rat.intCast_le_intCast.mpr (by omega)
    have hlt256 : normalFloat 7 e m < (256 : Rat) * u := by
      rw [hv_eq]
      apply rat_mul_lt_mul_of_pos_right _ hu_pos
      have h256 : (256 : Rat) = ((256 : Int) : Rat) := rfl
      rw [h256]
      exact Rat.intCast_lt_intCast.mpr (by omega)
    have h256_pos : (0 : Rat) < 1 / 256 := rat_div_pos (by decide) (by decide)
    have hlo_dw : u / 2 < (1 - β4) * normalFloat 7 e m := by
      have h1 : (1 / 256 : Rat) * ((128 : Rat) * u) < (1 - β4) * ((128 : Rat) * u) :=
        rat_mul_lt_mul_of_pos_right hlo_256 (rat_mul_pos (by decide) hu_pos)
      have h2 : (1 - β4) * ((128 : Rat) * u) ≤ (1 - β4) * normalFloat 7 e m :=
        rat_mul_le_mul_of_nonneg_left hge128 (Rat.le_of_lt (rat_lt_trans h256_pos hlo_256))
      have hlhs : (1 / 256 : Rat) * ((128 : Rat) * u) = u / 2 := by grind
      rw [hlhs] at h1
      exact rat_lt_of_lt_of_le h1 h2
    have hhi_dw : (1 - β4) * normalFloat 7 e m < (3 / 2 : Rat) * u := by
      have hlt : 1 - β4 < 3 / 512 := by
        rw [h1mβ4_eq]
        apply rat_lt_of_mul_pos_right (c := (512000000000000 : Rat)) (by decide)
        have ha : (3994003999 / 1000000000000 : Rat) * 512000000000000 = 2044930047488 := by grind
        have hb : (3 / 512 : Rat) * 512000000000000 = 3000000000000 := by grind
        rw [ha, hb]; decide
      have h1 : (1 - β4) * normalFloat 7 e m < (1 - β4) * ((256 : Rat) * u) :=
        rat_mul_lt_mul_of_pos_left hlt256 (rat_lt_trans h256_pos hlo_256)
      have h2 : (1 - β4) * ((256 : Rat) * u) < (3 / 512 : Rat) * ((256 : Rat) * u) :=
        rat_mul_lt_mul_of_pos_right hlt (rat_mul_pos (by decide) hu_pos)
      have hrhs : (3 / 512 : Rat) * ((256 : Rat) * u) = (3 / 2 : Rat) * u := by grind
      rw [hrhs] at h2
      exact rat_lt_trans h1 h2
    let q1 : Int := ((128 + m : Nat) : Int) - 1
    have hq1 : (q1 : Rat) = (((128 + m : Nat) : Int) : Rat) - 1 := by
      change ((((128 + m : Nat) : Int) - 1 : Int) : Rat) = _
      rw [Rat.intCast_sub]; rfl
    have hsplit : β4 * normalFloat 7 e m = (q1 : Rat) * u + (u - (1 - β4) * normalFloat 7 e m) := by
      rw [hq1]
      have : ((((128 + m : Nat) : Int) : Rat) - 1) * u + (u - (1 - β4) * normalFloat 7 e m) =
          (((128 + m : Nat) : Int) : Rat) * u - (1 - β4) * normalFloat 7 e m := by grind
      rw [this, ← hv_eq]; grind
    have hdw : ratAbs (u - (1 - β4) * normalFloat 7 e m) < u / 2 := by
      rw [ratAbs_lt_iff]
      constructor
      · have := rat_sub_pos hhi_dw
        have : (0 : Rat) < (u - (1 - β4) * normalFloat 7 e m) - (-(u / 2)) := by grind
        exact rat_lt_of_sub_pos this
      · have := rat_sub_pos hlo_dw
        have : (0 : Rat) < u / 2 - (u - (1 - β4) * normalFloat 7 e m) := by grind
        exact rat_lt_of_sub_pos this
    rw [hsplit, rneGrid_flush_strict q1 u _ hu_pos hdw, hv_eq, hq1]
    intro heq
    have hu0 : u = 0 := by grind
    exact Rat.ne_of_gt hu_pos hu0

/-- Headline Theorem 4 (`lazy_stamp_adamw_exact_equivalence_to_dense_updates`):
    Exact rational inductive theorem proving that Lazy-Stamp AdamW (`O(1)` closed-form
    or `O(log Δ)` binary-exponentiation jump across `Δ` absent steps) is 100% mathematically
    identical to `Δ` dense per-step AdamW updates, satisfies semigroup composition across
    consecutive gaps, and breaks the `BF16` `β_2 = 0.999` decay freeze across 100% of
    normal `BF16` states in just `Δ = 4` steps. -/
theorem lazy_stamp_adamw_exact_equivalence_to_dense_updates :
    (∀ (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState),
      denseAbsentSteps β1 β2 η lam Δ s = lazyStampJump β1 β2 η lam Δ s) ∧
    (∀ (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState),
      lazyStampJumpFast β1 β2 η lam Δ s = denseAbsentSteps β1 β2 η lam Δ s) ∧
    (∀ (β1 β2 η lam : Rat) (Δ1 Δ2 : Nat) (s : AdamWState),
      lazyStampJump β1 β2 η lam Δ2 (lazyStampJump β1 β2 η lam Δ1 s) =
        lazyStampJump β1 β2 η lam (Δ1 + Δ2) s) ∧
    (∀ (e : Int) (m : Nat), m < 128 →
      rneFloatBelow 7 e m (ratPow (999 / 1000 : Rat) 4 * normalFloat 7 e m) ≠
        normalFloat 7 e m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact denseAbsentSteps_eq_lazyStampJump
  · intro β1 β2 η lam Δ s
    rw [lazyStampJumpFast_eq_lazyStampJump, denseAbsentSteps_eq_lazyStampJump]
  · exact lazyStampJump_add
  · exact bf16_lazy_jump_4_breaks_freeze

end EmbedZipfLazyStamp
