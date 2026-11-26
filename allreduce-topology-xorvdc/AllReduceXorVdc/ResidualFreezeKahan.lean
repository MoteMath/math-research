/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AllReduceXorVdc.RatBasic

/-!
# Pillar 3: Exact BF16 Residual-Stream Freeze Depth & Kahan Compensated Recovery

Proves:
- Theorem 4 (`bf16_residual_stream_freeze_depth_exact`):
  - Exact integer-squared freeze threshold `2^(16 - 2p) < 2 * L ↔ bf16FreezeDepth p < L`
    (with `bf16FreezeDepth 5 = 32`, `bf16FreezeDepth 4 = 128`, `bf16FreezeDepth 3 = 512`).
  - Complete RNE freeze (`bf16ResidualAccum x δ L = x`) for every BF16 representable `x = m / 128`
    and every `0 ≤ δ < 1 / 256` across arbitrary depth `L`.
  - Exact boundary tie-to-even stall at `L = 2^(15 - 2p)` (`δ = 1 / 256`): every even-mantissa
    `x = (2k) / 128` freezes for all `L` steps, and every odd-mantissa `x = (2k + 1) / 128`
    steps once to the even neighbor `(2k + 2) / 128` and freezes for all remaining `L - 1` steps!
- Theorem 5 (`kahan_compensated_residual_exact_recovery`):
  - Exact conservation invariant `(kahanAccum u s0 xs).1 + (kahanAccum u s0 xs).2 = s0 + sumListRat xs`
    for arbitrary grid `u > 0` and arbitrary update list `xs` (arbitrary depth `L`, arbitrary signs).
  - Bounded compensation register `|(kahanAccum u s0 xs).2| ≤ u / 2` (so the primary accumulator
    stays within `u / 2` of the exact sum for all `L`, eliminating sub-ULP freeze completely).
-/

namespace AllReduceXorVdc

/-! ### Part A: Theorem 4 — Exact BF16 Residual-Stream Freeze Depth -/

theorem bf16_freeze_ineq_iff (p L : Nat) (hp : p ≤ 7) :
    2 ^ (16 - 2 * p) < 2 * L ↔ bf16FreezeDepth p < L := by
  unfold bf16FreezeDepth
  have h16 : 16 - 2 * p = (15 - 2 * p) + 1 := by omega
  rw [h16, Nat.pow_succ]
  omega

theorem bf16_freeze_eq_iff (p L : Nat) (hp : p ≤ 7) :
    2 ^ (16 - 2 * p) = 2 * L ↔ L = bf16FreezeDepth p := by
  unfold bf16FreezeDepth
  have h16 : 16 - 2 * p = (15 - 2 * p) + 1 := by omega
  rw [h16, Nat.pow_succ]
  omega

theorem bf16_rneAdd_sub_half_ulp (m : Int) (δ : Rat) (hδ0 : (0 : Rat) ≤ δ) (hδ : δ < bf16HalfUlp) :
    rneAdd bf16Ulp ((m : Rat) * bf16Ulp) δ = (m : Rat) * bf16Ulp := by
  unfold rneAdd rneGrid bf16Ulp bf16HalfUlp at *
  have hdiv : ((m : Rat) * ((1 : Rat) / 128) + δ) / ((1 : Rat) / 128) = (m : Rat) + 128 * δ := by
    grind
  rw [hdiv]
  have h128_nn : (0 : Rat) ≤ 128 * δ := Rat.mul_nonneg (by decide) hδ0
  have h128_lt : 128 * δ < (1 : Rat) / 2 := by
    have hmul := rat_mul_lt_mul_of_pos_left hδ (show (0 : Rat) < 128 by decide)
    have h1 : (128 : Rat) * ((1 : Rat) / 256) = (1 : Rat) / 2 := by grind
    rw [h1] at hmul
    exact hmul
  rw [rneInt_int_add_small h128_nn h128_lt]

theorem bf16ResidualAccum_freeze (m : Int) (δ : Rat) (hδ0 : (0 : Rat) ≤ δ) (hδ : δ < bf16HalfUlp)
    (L : Nat) :
    bf16ResidualAccum ((m : Rat) * bf16Ulp) δ L = (m : Rat) * bf16Ulp := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [bf16ResidualAccum, ih]
    exact bf16_rneAdd_sub_half_ulp m δ hδ0 hδ

theorem bf16_rneAdd_half_ulp_even (m : Int) (heven : m % 2 = 0) :
    rneAdd bf16Ulp ((m : Rat) * bf16Ulp) bf16HalfUlp = (m : Rat) * bf16Ulp := by
  unfold rneAdd rneGrid bf16Ulp bf16HalfUlp
  have hdiv : ((m : Rat) * ((1 : Rat) / 128) + (1 : Rat) / 256) / ((1 : Rat) / 128) =
      (m : Rat) + (1 : Rat) / 2 := by grind
  rw [hdiv, rneInt_int_add_half_even heven]

theorem bf16_rneAdd_half_ulp_odd (m : Int) (hodd : m % 2 ≠ 0) :
    rneAdd bf16Ulp ((m : Rat) * bf16Ulp) bf16HalfUlp = ((m + 1 : Int) : Rat) * bf16Ulp := by
  unfold rneAdd rneGrid bf16Ulp bf16HalfUlp
  have hdiv : ((m : Rat) * ((1 : Rat) / 128) + (1 : Rat) / 256) / ((1 : Rat) / 128) =
      (m : Rat) + (1 : Rat) / 2 := by grind
  rw [hdiv, rneInt_int_add_half_odd hodd]

theorem bf16ResidualAccum_boundary_even (m : Int) (heven : m % 2 = 0) (L : Nat) :
    bf16ResidualAccum ((m : Rat) * bf16Ulp) bf16HalfUlp L = (m : Rat) * bf16Ulp := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [bf16ResidualAccum, ih]
    exact bf16_rneAdd_half_ulp_even m heven

theorem bf16ResidualAccum_boundary_odd (m : Int) (hodd : m % 2 ≠ 0) (L : Nat) (hL : 1 ≤ L) :
    bf16ResidualAccum ((m : Rat) * bf16Ulp) bf16HalfUlp L = ((m + 1 : Int) : Rat) * bf16Ulp := by
  induction L with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp only [bf16ResidualAccum]
      exact bf16_rneAdd_half_ulp_odd m hodd
    | succ r =>
      change rneAdd bf16Ulp (bf16ResidualAccum ((m : Rat) * bf16Ulp) bf16HalfUlp (r + 1)) bf16HalfUlp = _
      rw [ih (by omega)]
      have hev : (m + 1) % 2 = 0 := by omega
      exact bf16_rneAdd_half_ulp_even (m + 1) hev

/-- **Headline Theorem 4 (Exact BF16 Residual-Stream Freeze Depth & Boundary Stall):** -/
theorem bf16_residual_stream_freeze_depth_exact :
    (∀ (p L : Nat), p ≤ 7 →
      (2 ^ (16 - 2 * p) < 2 * L ↔ bf16FreezeDepth p < L) ∧
      (2 ^ (16 - 2 * p) = 2 * L ↔ L = bf16FreezeDepth p)) ∧
    (bf16FreezeDepth 5 = 32 ∧ bf16FreezeDepth 4 = 128 ∧ bf16FreezeDepth 3 = 512) ∧
    (∀ (m : Int) (δ : Rat) (L : Nat), (0 : Rat) ≤ δ → δ < bf16HalfUlp →
      bf16ResidualAccum ((m : Rat) * bf16Ulp) δ L = (m : Rat) * bf16Ulp ∧
      absRat (bf16ResidualAccum ((m : Rat) * bf16Ulp) δ L -
        ((m : Rat) * bf16Ulp + (L : Rat) * δ)) = (L : Rat) * δ) ∧
    (∀ (m : Int) (L : Nat), m % 2 = 0 →
      bf16ResidualAccum ((m : Rat) * bf16Ulp) bf16HalfUlp L = (m : Rat) * bf16Ulp) ∧
    (∀ (m : Int) (L : Nat), m % 2 ≠ 0 → 1 ≤ L →
      bf16ResidualAccum ((m : Rat) * bf16Ulp) bf16HalfUlp L = ((m + 1 : Int) : Rat) * bf16Ulp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p L hp
    exact ⟨bf16_freeze_ineq_iff p L hp, bf16_freeze_eq_iff p L hp⟩
  · exact ⟨by decide, by decide, by decide⟩
  · intro m δ L hδ0 hδ
    have hfr := bf16ResidualAccum_freeze m δ hδ0 hδ L
    refine ⟨hfr, ?_⟩
    rw [hfr]
    have hsub : (m : Rat) * bf16Ulp - ((m : Rat) * bf16Ulp + (L : Rat) * δ) = -((L : Rat) * δ) := by grind
    rw [hsub, absRat_neg]
    exact absRat_of_nonneg (Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le L)) hδ0)
  · intro m L hev
    exact bf16ResidualAccum_boundary_even m hev L
  · intro m L hodd hL
    exact bf16ResidualAccum_boundary_odd m hodd L hL

/-! ### Part B: Theorem 5 — 2-Word Compensated Kahan Residual Exact Recovery -/

theorem kahanStep_invariant (u : Rat) (st : Rat × Rat) (x : Rat) :
    (kahanStep u st x).1 + (kahanStep u st x).2 = st.1 + st.2 + x := by
  unfold kahanStep
  dsimp only
  grind

theorem kahanStep_comp_bound {u : Rat} (hu : (0 : Rat) < u) (st : Rat × Rat) (x : Rat) :
    absRat (kahanStep u st x).2 ≤ u / 2 := by
  unfold kahanStep
  dsimp only
  have heq : x + st.2 - (rneGrid u (st.1 + (x + st.2)) - st.1) =
      (st.1 + (x + st.2)) - rneGrid u (st.1 + (x + st.2)) := by grind
  rw [heq]
  exact absRat_sub_rneGrid_le_half hu (st.1 + (x + st.2))

theorem kahanFold_invariant (u : Rat) (st : Rat × Rat) (xs : List Rat) :
    (xs.foldl (kahanStep u) st).1 + (xs.foldl (kahanStep u) st).2 =
    st.1 + st.2 + sumListRat xs := by
  induction xs generalizing st with
  | nil => simp [sumListRat, Rat.add_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, sumListRat]
    rw [ih (kahanStep u st x), kahanStep_invariant]
    grind

theorem kahanFold_comp_bound {u : Rat} (hu : (0 : Rat) < u) (st : Rat × Rat)
    (hst : absRat st.2 ≤ u / 2) (xs : List Rat) :
    absRat (xs.foldl (kahanStep u) st).2 ≤ u / 2 := by
  induction xs generalizing st with
  | nil => exact hst
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (kahanStep u st x) (kahanStep_comp_bound hu st x)

/-- **Headline Theorem 5 (2-Word Compensated Kahan Residual Exact Recovery):** -/
theorem kahan_compensated_residual_exact_recovery :
    (∀ (u s0 : Rat) (xs : List Rat), (0 : Rat) < u →
      let res := kahanAccum u s0 xs
      res.1 + res.2 = s0 + sumListRat xs ∧
      absRat res.2 ≤ u / 2 ∧
      absRat (res.1 - (s0 + sumListRat xs)) ≤ u / 2) ∧
    (∀ (m : Int) (δ : Rat) (L : Nat),
      let res := kahanAccum bf16Ulp ((m : Rat) * bf16Ulp) (List.replicate L δ)
      res.1 + res.2 = (m : Rat) * bf16Ulp + (L : Rat) * δ ∧
      absRat (res.1 - ((m : Rat) * bf16Ulp + (L : Rat) * δ)) ≤ bf16HalfUlp) := by
  have hrep : ∀ (L : Nat) (δ : Rat), sumListRat (List.replicate L δ) = (L : Rat) * δ := by
    intro L δ
    induction L with
    | zero => simp [List.replicate, sumListRat]
    | succ L ih =>
      simp only [List.replicate_succ, sumListRat, ih]
      rw [rat_natCast_add]
      have h1 : ((1 : Nat) : Rat) = 1 := rfl
      rw [h1]; grind
  refine ⟨?_, ?_⟩
  · intro u s0 xs hu
    unfold kahanAccum
    dsimp only
    have hinv := kahanFold_invariant u (s0, 0) xs
    have h0 : s0 + 0 + sumListRat xs = s0 + sumListRat xs := by grind
    rw [h0] at hinv
    have hc0 : absRat (0 : Rat) ≤ u / 2 := by
      have : absRat (0 : Rat) = 0 := by decide
      rw [this]
      exact Rat.le_of_lt (rat_div_pos hu (by decide))
    have hcb := kahanFold_comp_bound hu (s0, 0) hc0 xs
    refine ⟨hinv, hcb, ?_⟩
    have hdiff : (xs.foldl (kahanStep u) (s0, 0)).1 - (s0 + sumListRat xs) =
        -(xs.foldl (kahanStep u) (s0, 0)).2 := by grind
    rw [hdiff, absRat_neg]
    exact hcb
  · intro m δ L
    unfold kahanAccum
    dsimp only
    have hinv := kahanFold_invariant bf16Ulp ((m : Rat) * bf16Ulp, 0) (List.replicate L δ)
    rw [hrep L δ] at hinv
    have h0 : (m : Rat) * bf16Ulp + 0 + (L : Rat) * δ = (m : Rat) * bf16Ulp + (L : Rat) * δ := by grind
    rw [h0] at hinv
    have hu : (0 : Rat) < bf16Ulp := rat_div_pos (by decide) (by decide)
    have hc0 : absRat (0 : Rat) ≤ bf16Ulp / 2 := by
      have h0 : absRat (0 : Rat) = 0 := by decide
      rw [h0]
      exact Rat.le_of_lt (rat_div_pos hu (by decide))
    have hcb := kahanFold_comp_bound hu ((m : Rat) * bf16Ulp, 0) hc0 (List.replicate L δ)
    have hhalf : bf16Ulp / 2 = bf16HalfUlp := by unfold bf16Ulp bf16HalfUlp; grind
    rw [hhalf] at hcb
    refine ⟨hinv, ?_⟩
    have hdiff : ((List.replicate L δ).foldl (kahanStep bf16Ulp) ((m : Rat) * bf16Ulp, 0)).1 -
        ((m : Rat) * bf16Ulp + (L : Rat) * δ) =
        -((List.replicate L δ).foldl (kahanStep bf16Ulp) ((m : Rat) * bf16Ulp, 0)).2 := by grind
    rw [hdiff, absRat_neg]
    exact hcb

end AllReduceXorVdc
