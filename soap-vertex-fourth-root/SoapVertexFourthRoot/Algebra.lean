/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SoapVertexFourthRoot.Defs

/-!
# Algebraic Equivalence, Taylor-2 Exactness, and Pointwise Envelopes (`soap-vertex-fourth-root`)

All proofs are pure Lean 4 `Init` (zero Mathlib, zero `native_decide`).
-/

namespace SoapVertexFourthRoot

/-! ## Elementary `Rat` Order Helpers -/

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := Rat.add_le_add_right (c := -b) |>.mpr h
  grind

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := Rat.add_le_add_right (c := b) |>.mpr h
  grind

theorem rat_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a * b := by
  have h1 : (0 : Rat) ≤ a * b := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  have hne : a * b ≠ 0 := by
    intro h0
    have ha0 : a ≠ 0 := Rat.ne_of_gt ha
    have hb0 : b ≠ 0 := Rat.ne_of_gt hb
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact ha0 h
    | inr h => exact hb0 h
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    c * a ≤ c * b := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ b - a := rat_sub_nonneg h
  have h2 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]
  exact h2

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

theorem rat_mul_le_mul_of_nonpos_left {a b c : Rat} (h : a ≤ b) (hc : c ≤ (0 : Rat)) :
    c * b ≤ c * a := by
  have hneg : (0 : Rat) ≤ -c := by
    have := rat_sub_nonneg hc
    grind
  have h1 : (-c) * a ≤ (-c) * b := rat_mul_le_mul_of_nonneg_left h hneg
  apply rat_le_of_sub_nonneg
  have h2 : (0 : Rat) ≤ (-c) * b - (-c) * a := rat_sub_nonneg h1
  have eq : c * a - c * b = (-c) * b - (-c) * a := by grind
  rw [eq]
  exact h2

theorem rat_mul_le_mul {a b c d : Rat}
    (hab : a ≤ b) (hcd : c ≤ d) (ha : (0 : Rat) ≤ a) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * d := by
  have hb : (0 : Rat) ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hab hc)
    (rat_mul_le_mul_of_nonneg_left hcd hb)

theorem rat_add_le_add {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr hab) (Rat.add_le_add_left.mpr hcd)

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := by
      have := rat_sub_nonneg h
      grind
    have eq : x * x = (-x) * (-x) := by grind
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

theorem rat_sq_le_sq_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  rat_mul_le_mul hab hab ha ha

theorem rat_pow4_nonneg (x : Rat) : (0 : Rat) ≤ ratPow4 x := by
  unfold ratPow4
  exact rat_sq_nonneg (x * x)

theorem rat_pow4_pos {x : Rat} (hx : (0 : Rat) < x) : (0 : Rat) < ratPow4 x := by
  unfold ratPow4
  have hx2 : (0 : Rat) < x * x := rat_mul_pos hx hx
  exact rat_mul_pos hx2 hx2

theorem rat_pow4_le_pow4_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    ratPow4 a ≤ ratPow4 b := by
  unfold ratPow4
  have h2 : a * a ≤ b * b := rat_sq_le_sq_of_nonneg ha hab
  have ha2 : (0 : Rat) ≤ a * a := rat_sq_nonneg a
  exact rat_sq_le_sq_of_nonneg ha2 h2

theorem rat_max_eq_right {a b : Rat} (h : a ≤ b) : max a b = b := by
  change (if a ≤ b then b else a) = b
  simp [h]

theorem rat_max_eq_left {a b : Rat} (h : b ≤ a) : max a b = a := by
  change (if a ≤ b then b else a) = a
  split
  · rename_i h'
    exact Rat.le_antisymm h h'
  · rfl

theorem rat_le_max_left (a b : Rat) : a ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact h
  | inr h => rw [rat_max_eq_left h]; exact Rat.le_refl

theorem rat_le_max_right (a b : Rat) : b ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact Rat.le_refl
  | inr h => rw [rat_max_eq_left h]; exact h

theorem rat_sq_le_max_sq {L v R : Rat} (hL : L ≤ v) (hR : v ≤ R) :
    v * v ≤ max (L * L) (R * R) := by
  cases Rat.le_total (a := (0 : Rat)) (b := v) with
  | inl hv =>
    have h1 : v * v ≤ R * R := rat_sq_le_sq_of_nonneg hv hR
    exact Rat.le_trans h1 (rat_le_max_right _ _)
  | inr hv =>
    have hneg_v : (0 : Rat) ≤ -v := by
      have := rat_sub_nonneg hv
      grind
    have hneg_L : -v ≤ -L := by
      have := rat_sub_nonneg hL
      exact rat_le_of_sub_nonneg (a := -L) (b := -v) (by grind)
    have h1 : (-v) * (-v) ≤ (-L) * (-L) := rat_sq_le_sq_of_nonneg hneg_v hneg_L
    have eq1 : (-v) * (-v) = v * v := by grind
    have eq2 : (-L) * (-L) = L * L := by grind
    rw [eq1, eq2] at h1
    exact Rat.le_trans h1 (rat_le_max_left _ _)

theorem rat_sub_pos_of_lt {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by
  have hle : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt h)
  have hne : a - b ≠ 0 := by
    intro h0
    have hab : a = b := by grind
    rw [hab] at h
    exact Rat.lt_irrefl h
  exact Rat.lt_of_le_of_ne hle (Ne.symm hne)

theorem rat_lt_of_lt_of_le {a b c : Rat} (hab : a < b) (hbc : b ≤ c) : a < c := by
  have hac : a ≤ c := Rat.le_trans (Rat.le_of_lt hab) hbc
  have hne : a ≠ c := by
    intro h
    rw [h] at hab
    exact Rat.not_le.mpr hab hbc
  exact Rat.lt_of_le_of_ne hac hne

theorem rat_add_pos_of_pos_nonneg {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) < a + b := by
  have h1 : a ≤ a + b := by
    have := Rat.add_le_add_left (c := a) |>.mpr hb
    grind
  exact rat_lt_of_lt_of_le ha h1

/-! ## Theorem 1: Exact Vertex Equivalence & Global Positivity -/

theorem vertex_fourth_root_equiv_monomial (a b c α β μ m : Rat) (hc : c ≠ 0) :
    a + b * m + c * m * m =
      (a - (b * b) / (4 * c)) + c * (m + b / (2 * c)) * (m + b / (2 * c)) ∧
    ((0 : Rat) ≤ β → α ≤ α + β * (m - μ) * (m - μ)) := by
  constructor
  · have h2c : (2 : Rat) * c ≠ 0 := by
      intro h
      apply hc
      grind
    have h4c : (4 : Rat) * c ≠ 0 := by
      intro h
      apply hc
      grind
    have hinv2 : ((2 : Rat) * c) * ((2 * c)⁻¹) = 1 := Rat.mul_inv_cancel (2 * c) h2c
    have hinv4 : ((4 : Rat) * c) * ((4 * c)⁻¹) = 1 := Rat.mul_inv_cancel (4 * c) h4c
    have hdiv2 : b / (2 * c) = b * (2 * c)⁻¹ := Rat.div_def b (2 * c)
    have hdiv4 : (b * b) / (4 * c) = (b * b) * (4 * c)⁻¹ := Rat.div_def (b * b) (4 * c)
    rw [hdiv2, hdiv4]
    have hrel : (2 * c)⁻¹ * (2 * c)⁻¹ = (4 * c)⁻¹ * c⁻¹ := by
      have hmul : ((4 : Rat) * c * c) * ((2 * c)⁻¹ * (2 * c)⁻¹) = 1 := by
        calc
          ((4 : Rat) * c * c) * ((2 * c)⁻¹ * (2 * c)⁻¹)
              = (((2 : Rat) * c) * (2 * c)⁻¹) * (((2 : Rat) * c) * (2 * c)⁻¹) := by grind
          _ = 1 * 1 := by rw [hinv2]
          _ = 1 := by grind
      have hmul2 : ((4 : Rat) * c * c) * ((4 * c)⁻¹ * c⁻¹) = 1 := by
        have hcinv : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
        calc
          ((4 : Rat) * c * c) * ((4 * c)⁻¹ * c⁻¹)
              = (((4 : Rat) * c) * (4 * c)⁻¹) * (c * c⁻¹) := by grind
          _ = 1 * 1 := by rw [hinv4, hcinv]
          _ = 1 := by grind
      have h4cc : (4 : Rat) * c * c ≠ 0 := by
        intro h0
        cases Rat.mul_eq_zero.mp h0 with
        | inl h => exact h4c h
        | inr h => exact hc h
      have hdiff : ((4 : Rat) * c * c) * ((2 * c)⁻¹ * (2 * c)⁻¹ - (4 * c)⁻¹ * c⁻¹) = 0 := by
        calc
          ((4 : Rat) * c * c) * ((2 * c)⁻¹ * (2 * c)⁻¹ - (4 * c)⁻¹ * c⁻¹)
              = ((4 : Rat) * c * c) * ((2 * c)⁻¹ * (2 * c)⁻¹) -
                  ((4 : Rat) * c * c) * ((4 * c)⁻¹ * c⁻¹) := by grind
          _ = 1 - 1 := by rw [hmul, hmul2]
          _ = 0 := by grind
      cases Rat.mul_eq_zero.mp hdiff with
      | inl h => exact False.elim (h4cc h)
      | inr h => grind
    have hcinv : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
    have hterm1 : c * (2 * (m * (b * (2 * c)⁻¹))) = b * m := by
      calc
        c * (2 * (m * (b * (2 * c)⁻¹)))
            = b * m * (((2 : Rat) * c) * (2 * c)⁻¹) := by grind
        _ = b * m * 1 := by rw [hinv2]
        _ = b * m := by grind
    have hterm2 : c * ((b * (2 * c)⁻¹) * (b * (2 * c)⁻¹)) = (b * b) * (4 * c)⁻¹ := by
      calc
        c * ((b * (2 * c)⁻¹) * (b * (2 * c)⁻¹))
            = (b * b) * (c * ((2 * c)⁻¹ * (2 * c)⁻¹)) := by grind
        _ = (b * b) * (c * ((4 * c)⁻¹ * c⁻¹)) := by rw [hrel]
        _ = (b * b) * ((4 * c)⁻¹ * (c * c⁻¹)) := by grind
        _ = (b * b) * ((4 * c)⁻¹ * 1) := by rw [hcinv]
        _ = (b * b) * (4 * c)⁻¹ := by grind
    calc
      a + b * m + c * m * m
          = (a - (b * b) * (4 * c)⁻¹) + c * m * m + b * m + (b * b) * (4 * c)⁻¹ := by grind
      _ = (a - (b * b) * (4 * c)⁻¹) + c * m * m +
            c * (2 * (m * (b * (2 * c)⁻¹))) +
            c * ((b * (2 * c)⁻¹) * (b * (2 * c)⁻¹)) := by rw [hterm1, hterm2]
      _ = (a - (b * b) * (4 * c)⁻¹) +
            c * (m + b * (2 * c)⁻¹) * (m + b * (2 * c)⁻¹) := by grind
  · intro hβ
    have hsq : (0 : Rat) ≤ (m - μ) * (m - μ) := rat_sq_nonneg (m - μ)
    have hprod : (0 : Rat) ≤ β * ((m - μ) * (m - μ)) := Rat.mul_nonneg hβ hsq
    have hadd : α + 0 ≤ α + β * ((m - μ) * (m - μ)) :=
      Rat.add_le_add_left.mpr hprod
    have eq1 : α + β * (m - μ) * (m - μ) = α + β * ((m - μ) * (m - μ)) := by grind
    rw [eq1]
    grind

/-! ## Theorem 2: Exact Taylor-2 Vertex Form & Cubic Convergence Residual -/

theorem taylor2_fourth_root_vertex_exact (m : Rat) :
    ((1 : Rat) - (m - 1) / 4 + (5 / 32 : Rat) * (m - 1) * (m - 1) =
      (9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5)) ∧
    ((9 / 10 : Rat) ≤ (9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5)) ∧
    (m * ratPow4 ((9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5)) - 1 =
      (m - 1) * (m - 1) * (m - 1) * taylor2ResidualPoly m) := by
  have heq : (1 : Rat) - (m - 1) / 4 + (5 / 32 : Rat) * (m - 1) * (m - 1) =
      (9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5) := by
    grind
  refine ⟨heq, ?_, ?_⟩
  · have hβ : (0 : Rat) ≤ (5 / 32 : Rat) := by grind
    have hsq : (0 : Rat) ≤ (m - 9 / 5) * (m - 9 / 5) := rat_sq_nonneg (m - 9 / 5)
    have hprod : (0 : Rat) ≤ (5 / 32 : Rat) * ((m - 9 / 5) * (m - 9 / 5)) :=
      Rat.mul_nonneg hβ hsq
    have hadd : (9 / 10 : Rat) + 0 ≤ (9 / 10 : Rat) + (5 / 32 : Rat) * ((m - 9 / 5) * (m - 9 / 5)) :=
      Rat.add_le_add_left.mpr hprod
    have eq1 : (9 / 10 : Rat) + (5 / 32 : Rat) * (m - 9 / 5) * (m - 9 / 5) =
        (9 / 10 : Rat) + (5 / 32 : Rat) * ((m - 9 / 5) * (m - 9 / 5)) := by grind
    rw [eq1]
    grind
  · rw [← heq]
    unfold ratPow4 taylor2ResidualPoly
    grind

/-! ## Theorem 3: Pointwise Exact Envelopes for Vertex & Linear Coupled `G^{-1/4}` Steps -/

private theorem step4_factor (m q a b c e : Rat) :
    m * ((((q * a) * (q * a) * b) * ((q * a) * (q * a) * b)) * c) * e =
    (ratPow4 a * ((b * b) * (c * e))) * (m * ratPow4 q) := by
  unfold ratPow4
  grind

private theorem one_sub_u_pos {u : Rat} (hu1 : u < 1) : (0 : Rat) < 1 - u :=
  rat_sub_pos_of_lt hu1

private theorem one_add_u_pos {u : Rat} (hu0 : (0 : Rat) ≤ u) : (0 : Rat) < 1 + u := by
  have h1 : (0 : Rat) < 1 := by grind
  exact rat_add_pos_of_pos_nonneg h1 hu0

private theorem factor_bounds {u δ : Rat} (hu1 : u < 1) (hlo : -u ≤ δ) (hhi : δ ≤ u) :
    (0 : Rat) < 1 - u ∧ 1 - u ≤ 1 + δ ∧ 1 + δ ≤ 1 + u := by
  have hpos : (0 : Rat) < 1 - u := one_sub_u_pos hu1
  have h1 : 1 - u ≤ 1 + δ := by
    have := Rat.add_le_add_left (c := (1 : Rat)) |>.mpr hlo
    grind
  have h2 : 1 + δ ≤ 1 + u := Rat.add_le_add_left (c := (1 : Rat)) |>.mpr hhi
  exact ⟨hpos, h1, h2⟩

/-- Pointwise exact envelope for the 7-rounding-point vertex step `NoisyVertexStep4`. -/
theorem noisyVertexStep4_envelope (α β μ u m y : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) ≤ β)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1) (hm : (0 : Rat) < m)
    (hstep : NoisyVertexStep4 α β μ u m y) :
    vertexLowerEnv4 α β μ u m ≤ y ∧ y ≤ vertexUpperEnv4 α β μ u m := by
  rcases hstep with ⟨δ1, δ2, δ3, δ4, δ5, δ6, δ7,
    ⟨h1l, h1r⟩, ⟨h2l, h2r⟩, ⟨h3l, h3r⟩, ⟨h4l, h4r⟩, ⟨h5l, h5r⟩, ⟨h6l, h6r⟩, ⟨h7l, h7r⟩, hy⟩
  have ⟨hloPos, h1lo, h1hi⟩ := factor_bounds hu1 h1l h1r
  have ⟨_, h2lo, h2hi⟩ := factor_bounds hu1 h2l h2r
  have ⟨_, h3lo, h3hi⟩ := factor_bounds hu1 h3l h3r
  have ⟨_, h4lo, h4hi⟩ := factor_bounds hu1 h4l h4r
  have ⟨_, h5lo, h5hi⟩ := factor_bounds hu1 h5l h5r
  have ⟨_, h6lo, h6hi⟩ := factor_bounds hu1 h6l h6r
  have ⟨_, h7lo, h7hi⟩ := factor_bounds hu1 h7l h7r
  have hloNN : (0 : Rat) ≤ 1 - u := Rat.le_of_lt hloPos
  have hhiPos : (0 : Rat) < 1 + u := one_add_u_pos hu0
  have hhiNN : (0 : Rat) ≤ 1 + u := Rat.le_of_lt hhiPos
  -- Bound (1 + δ1)^2 * (1 + δ2) * (1 + δ3) ∈ [(1 - u)^4, (1 + u)^4]
  have h1sq_lo : (1 - u) * (1 - u) ≤ (1 + δ1) * (1 + δ1) := rat_sq_le_sq_of_nonneg hloNN h1lo
  have h1sq_hi : (1 + δ1) * (1 + δ1) ≤ (1 + u) * (1 + u) :=
    rat_sq_le_sq_of_nonneg (Rat.le_trans hloNN h1lo) h1hi
  have h23_lo : (1 - u) * (1 - u) ≤ (1 + δ2) * (1 + δ3) :=
    rat_mul_le_mul h2lo h3lo hloNN hloNN
  have h23_hi : (1 + δ2) * (1 + δ3) ≤ (1 + u) * (1 + u) :=
    rat_mul_le_mul h2hi h3hi (Rat.le_trans hloNN h2lo) (Rat.le_trans hloNN h3lo)
  have hf4_lo : ratPow4 (1 - u) ≤ ((1 + δ1) * (1 + δ1)) * ((1 + δ2) * (1 + δ3)) := by
    unfold ratPow4
    exact rat_mul_le_mul h1sq_lo h23_lo (rat_sq_nonneg _) (rat_sq_nonneg _)
  have hf4_hi : ((1 + δ1) * (1 + δ1)) * ((1 + δ2) * (1 + δ3)) ≤ ratPow4 (1 + u) := by
    unfold ratPow4
    exact rat_mul_le_mul h1sq_hi h23_hi (rat_sq_nonneg _)
      (Rat.mul_nonneg (Rat.le_trans hloNN h2lo) (Rat.le_trans hloNN h3lo))
  -- Inner sum q = α + t
  let d  := (m - μ) * (1 + δ1)
  let d2 := d * d * (1 + δ2)
  let t  := β * d2 * (1 + δ3)
  let q  := α + t
  have ht_eq : t = (((1 + δ1) * (1 + δ1)) * ((1 + δ2) * (1 + δ3))) * (β * ((m - μ) * (m - μ))) := by
    dsimp [t, d2, d]
    grind
  have hβsq_nn : (0 : Rat) ≤ β * ((m - μ) * (m - μ)) :=
    Rat.mul_nonneg hβ (rat_sq_nonneg (m - μ))
  have ht_lo : ratPow4 (1 - u) * β * ((m - μ) * (m - μ)) ≤ t := by
    rw [ht_eq]
    have h := rat_mul_le_mul_of_nonneg_right hf4_lo hβsq_nn
    have eq1 : ratPow4 (1 - u) * β * ((m - μ) * (m - μ)) =
        ratPow4 (1 - u) * (β * ((m - μ) * (m - μ))) := by grind
    rw [eq1]; exact h
  have ht_hi : t ≤ ratPow4 (1 + u) * β * ((m - μ) * (m - μ)) := by
    rw [ht_eq]
    have h := rat_mul_le_mul_of_nonneg_right hf4_hi hβsq_nn
    have eq1 : ratPow4 (1 + u) * β * ((m - μ) * (m - μ)) =
        ratPow4 (1 + u) * (β * ((m - μ) * (m - μ))) := by grind
    rw [eq1]; exact h
  have hq_lo : qLoVertex α β μ u m ≤ q := by
    unfold qLoVertex
    exact Rat.add_le_add_left.mpr ht_lo
  have hq_hi : q ≤ qHiVertex α β μ u m := by
    unfold qHiVertex
    exact Rat.add_le_add_left.mpr ht_hi
  have hqLo_pos : (0 : Rat) < qLoVertex α β μ u m := by
    unfold qLoVertex
    have h1 : (0 : Rat) ≤ ratPow4 (1 - u) * β * ((m - μ) * (m - μ)) :=
      Rat.mul_nonneg (Rat.mul_nonneg (rat_pow4_nonneg _) hβ) (rat_sq_nonneg _)
    exact rat_add_pos_of_pos_nonneg hα h1
  have hqLo_nn : (0 : Rat) ≤ qLoVertex α β μ u m := Rat.le_of_lt hqLo_pos
  have hq_nn : (0 : Rat) ≤ q := Rat.le_trans hqLo_nn hq_lo
  -- Outer rounding factor (1+δ4)^4 * (1+δ5)^2 * (1+δ6) * (1+δ7) ∈ [(1-u)^8, (1+u)^8]
  have h4p4_lo : ratPow4 (1 - u) ≤ ratPow4 (1 + δ4) := rat_pow4_le_pow4_of_nonneg hloNN h4lo
  have h4p4_hi : ratPow4 (1 + δ4) ≤ ratPow4 (1 + u) :=
    rat_pow4_le_pow4_of_nonneg (Rat.le_trans hloNN h4lo) h4hi
  have h5sq_lo : (1 - u) * (1 - u) ≤ (1 + δ5) * (1 + δ5) := rat_sq_le_sq_of_nonneg hloNN h5lo
  have h5sq_hi : (1 + δ5) * (1 + δ5) ≤ (1 + u) * (1 + u) :=
    rat_sq_le_sq_of_nonneg (Rat.le_trans hloNN h5lo) h5hi
  have h67_lo : (1 - u) * (1 - u) ≤ (1 + δ6) * (1 + δ7) :=
    rat_mul_le_mul h6lo h7lo hloNN hloNN
  have h67_hi : (1 + δ6) * (1 + δ7) ≤ (1 + u) * (1 + u) :=
    rat_mul_le_mul h6hi h7hi (Rat.le_trans hloNN h6lo) (Rat.le_trans hloNN h7lo)
  have h567_lo : ratPow4 (1 - u) ≤ ((1 + δ5) * (1 + δ5)) * ((1 + δ6) * (1 + δ7)) := by
    unfold ratPow4
    exact rat_mul_le_mul h5sq_lo h67_lo (rat_sq_nonneg _) (rat_sq_nonneg _)
  have h567_hi : ((1 + δ5) * (1 + δ5)) * ((1 + δ6) * (1 + δ7)) ≤ ratPow4 (1 + u) := by
    unfold ratPow4
    exact rat_mul_le_mul h5sq_hi h67_hi (rat_sq_nonneg _)
      (Rat.mul_nonneg (Rat.le_trans hloNN h6lo) (Rat.le_trans hloNN h7lo))
  have hf8_lo : ratPow8 (1 - u) ≤ ratPow4 (1 + δ4) * (((1 + δ5) * (1 + δ5)) * ((1 + δ6) * (1 + δ7))) := by
    unfold ratPow8
    exact rat_mul_le_mul h4p4_lo h567_lo (rat_pow4_nonneg _) (rat_pow4_nonneg _)
  have hf8_hi : ratPow4 (1 + δ4) * (((1 + δ5) * (1 + δ5)) * ((1 + δ6) * (1 + δ7))) ≤ ratPow8 (1 + u) := by
    unfold ratPow8
    exact rat_mul_le_mul h4p4_hi h567_hi (rat_pow4_nonneg _)
      (Rat.mul_nonneg (rat_sq_nonneg _)
        (Rat.mul_nonneg (Rat.le_trans hloNN h6lo) (Rat.le_trans hloNN h7lo)))
  -- Assemble y = factor8 * m * q^4
  have hy_eq : y = (ratPow4 (1 + δ4) * (((1 + δ5) * (1 + δ5)) * ((1 + δ6) * (1 + δ7)))) *
      (m * ratPow4 q) := by
    rw [hy]
    exact step4_factor m q (1 + δ4) (1 + δ5) (1 + δ6) (1 + δ7)
  have hq4_lo : ratPow4 (qLoVertex α β μ u m) ≤ ratPow4 q :=
    rat_pow4_le_pow4_of_nonneg hqLo_nn hq_lo
  have hq4_hi : ratPow4 q ≤ ratPow4 (qHiVertex α β μ u m) :=
    rat_pow4_le_pow4_of_nonneg hq_nn hq_hi
  have hm_nn : (0 : Rat) ≤ m := Rat.le_of_lt hm
  have hmq4_lo : m * ratPow4 (qLoVertex α β μ u m) ≤ m * ratPow4 q :=
    rat_mul_le_mul_of_nonneg_left hq4_lo hm_nn
  have hmq4_hi : m * ratPow4 q ≤ m * ratPow4 (qHiVertex α β μ u m) :=
    rat_mul_le_mul_of_nonneg_left hq4_hi hm_nn
  have hmq4_lo_nn : (0 : Rat) ≤ m * ratPow4 (qLoVertex α β μ u m) :=
    Rat.mul_nonneg hm_nn (rat_pow4_nonneg _)
  have hmq4_nn : (0 : Rat) ≤ m * ratPow4 q := Rat.le_trans hmq4_lo_nn hmq4_lo
  have hf8_nn : (0 : Rat) ≤ ratPow8 (1 - u) := by
    unfold ratPow8
    exact rat_sq_nonneg _
  have hf8_mid_nn : (0 : Rat) ≤ ratPow4 (1 + δ4) * (((1 + δ5) * (1 + δ5)) * ((1 + δ6) * (1 + δ7))) :=
    Rat.le_trans hf8_nn hf8_lo
  constructor
  · rw [hy_eq]
    unfold vertexLowerEnv4
    have h := rat_mul_le_mul hf8_lo hmq4_lo hf8_nn hmq4_lo_nn
    rw [Rat.mul_assoc]
    exact h
  · rw [hy_eq]
    unfold vertexUpperEnv4
    have h := rat_mul_le_mul hf8_hi hmq4_hi hf8_mid_nn hmq4_nn
    rw [Rat.mul_assoc (ratPow8 (1 + u))]
    exact h

/-- Pointwise exact envelope for the 5-rounding-point linear step `NoisyLinearStep4`. -/
theorem noisyLinearStep4_envelope (p0 p1 u m y : Rat)
    (hp1 : p1 ≤ (0 : Rat))
    (_hu0 : (0 : Rat) ≤ u) (hu1 : u < 1) (hm : (0 : Rat) < m)
    (hqLoPos : (0 : Rat) < qLoLinear p0 p1 u m)
    (hstep : NoisyLinearStep4 p0 p1 u m y) :
    linearLowerEnv4 p0 p1 u m ≤ y ∧ y ≤ linearUpperEnv4 p0 p1 u m := by
  rcases hstep with ⟨δ1, δ2, δ3, δ4, δ5,
    ⟨h1l, h1r⟩, ⟨h2l, h2r⟩, ⟨h3l, h3r⟩, ⟨h4l, h4r⟩, ⟨h5l, h5r⟩, hy⟩
  have ⟨hloPos, h1lo, h1hi⟩ := factor_bounds hu1 h1l h1r
  have ⟨_, h2lo, h2hi⟩ := factor_bounds hu1 h2l h2r
  have ⟨_, h3lo, h3hi⟩ := factor_bounds hu1 h3l h3r
  have ⟨_, h4lo, h4hi⟩ := factor_bounds hu1 h4l h4r
  have ⟨_, h5lo, h5hi⟩ := factor_bounds hu1 h5l h5r
  have hloNN : (0 : Rat) ≤ 1 - u := Rat.le_of_lt hloPos
  have hm_nn : (0 : Rat) ≤ m := Rat.le_of_lt hm
  -- Since p1 ≤ 0 and m ≥ 0, p1 * m ≤ 0, so multiplying by (1 + δ1) reverses order
  have hp1m_np : p1 * m ≤ 0 := by
    have h := rat_mul_le_mul_of_nonneg_right hp1 hm_nn
    grind
  let t := p1 * m * (1 + δ1)
  let q := p0 + t
  have ht_lo : p1 * (1 + u) * m ≤ t := by
    have h := rat_mul_le_mul_of_nonpos_left h1hi hp1m_np
    have eq1 : p1 * (1 + u) * m = (p1 * m) * (1 + u) := by grind
    rw [eq1]; exact h
  have ht_hi : t ≤ p1 * (1 - u) * m := by
    have h := rat_mul_le_mul_of_nonpos_left h1lo hp1m_np
    have eq1 : p1 * (1 - u) * m = (p1 * m) * (1 - u) := by grind
    rw [eq1]; exact h
  have hq_lo : qLoLinear p0 p1 u m ≤ q := by
    unfold qLoLinear
    exact Rat.add_le_add_left.mpr ht_lo
  have hq_hi : q ≤ qHiLinear p0 p1 u m := by
    unfold qHiLinear
    exact Rat.add_le_add_left.mpr ht_hi
  have hqLo_nn : (0 : Rat) ≤ qLoLinear p0 p1 u m := Rat.le_of_lt hqLoPos
  have hq_nn : (0 : Rat) ≤ q := Rat.le_trans hqLo_nn hq_lo
  -- Outer rounding factor (1+δ2)^4 * (1+δ3)^2 * (1+δ4) * (1+δ5) ∈ [(1-u)^8, (1+u)^8]
  have h2p4_lo : ratPow4 (1 - u) ≤ ratPow4 (1 + δ2) := rat_pow4_le_pow4_of_nonneg hloNN h2lo
  have h2p4_hi : ratPow4 (1 + δ2) ≤ ratPow4 (1 + u) :=
    rat_pow4_le_pow4_of_nonneg (Rat.le_trans hloNN h2lo) h2hi
  have h3sq_lo : (1 - u) * (1 - u) ≤ (1 + δ3) * (1 + δ3) := rat_sq_le_sq_of_nonneg hloNN h3lo
  have h3sq_hi : (1 + δ3) * (1 + δ3) ≤ (1 + u) * (1 + u) :=
    rat_sq_le_sq_of_nonneg (Rat.le_trans hloNN h3lo) h3hi
  have h45_lo : (1 - u) * (1 - u) ≤ (1 + δ4) * (1 + δ5) :=
    rat_mul_le_mul h4lo h5lo hloNN hloNN
  have h45_hi : (1 + δ4) * (1 + δ5) ≤ (1 + u) * (1 + u) :=
    rat_mul_le_mul h4hi h5hi (Rat.le_trans hloNN h4lo) (Rat.le_trans hloNN h5lo)
  have h345_lo : ratPow4 (1 - u) ≤ ((1 + δ3) * (1 + δ3)) * ((1 + δ4) * (1 + δ5)) := by
    unfold ratPow4
    exact rat_mul_le_mul h3sq_lo h45_lo (rat_sq_nonneg _) (rat_sq_nonneg _)
  have h345_hi : ((1 + δ3) * (1 + δ3)) * ((1 + δ4) * (1 + δ5)) ≤ ratPow4 (1 + u) := by
    unfold ratPow4
    exact rat_mul_le_mul h3sq_hi h45_hi (rat_sq_nonneg _)
      (Rat.mul_nonneg (Rat.le_trans hloNN h4lo) (Rat.le_trans hloNN h5lo))
  have hf8_lo : ratPow8 (1 - u) ≤ ratPow4 (1 + δ2) * (((1 + δ3) * (1 + δ3)) * ((1 + δ4) * (1 + δ5))) := by
    unfold ratPow8
    exact rat_mul_le_mul h2p4_lo h345_lo (rat_pow4_nonneg _) (rat_pow4_nonneg _)
  have hf8_hi : ratPow4 (1 + δ2) * (((1 + δ3) * (1 + δ3)) * ((1 + δ4) * (1 + δ5))) ≤ ratPow8 (1 + u) := by
    unfold ratPow8
    exact rat_mul_le_mul h2p4_hi h345_hi (rat_pow4_nonneg _)
      (Rat.mul_nonneg (rat_sq_nonneg _)
        (Rat.mul_nonneg (Rat.le_trans hloNN h4lo) (Rat.le_trans hloNN h5lo)))
  have hy_eq : y = (ratPow4 (1 + δ2) * (((1 + δ3) * (1 + δ3)) * ((1 + δ4) * (1 + δ5)))) *
      (m * ratPow4 q) := by
    rw [hy]
    exact step4_factor m q (1 + δ2) (1 + δ3) (1 + δ4) (1 + δ5)
  have hq4_lo : ratPow4 (qLoLinear p0 p1 u m) ≤ ratPow4 q :=
    rat_pow4_le_pow4_of_nonneg hqLo_nn hq_lo
  have hq4_hi : ratPow4 q ≤ ratPow4 (qHiLinear p0 p1 u m) :=
    rat_pow4_le_pow4_of_nonneg hq_nn hq_hi
  have hmq4_lo : m * ratPow4 (qLoLinear p0 p1 u m) ≤ m * ratPow4 q :=
    rat_mul_le_mul_of_nonneg_left hq4_lo hm_nn
  have hmq4_hi : m * ratPow4 q ≤ m * ratPow4 (qHiLinear p0 p1 u m) :=
    rat_mul_le_mul_of_nonneg_left hq4_hi hm_nn
  have hmq4_lo_nn : (0 : Rat) ≤ m * ratPow4 (qLoLinear p0 p1 u m) :=
    Rat.mul_nonneg hm_nn (rat_pow4_nonneg _)
  have hmq4_nn : (0 : Rat) ≤ m * ratPow4 q := Rat.le_trans hmq4_lo_nn hmq4_lo
  have hf8_nn : (0 : Rat) ≤ ratPow8 (1 - u) := by
    unfold ratPow8
    exact rat_sq_nonneg _
  have hf8_mid_nn : (0 : Rat) ≤ ratPow4 (1 + δ2) * (((1 + δ3) * (1 + δ3)) * ((1 + δ4) * (1 + δ5))) :=
    Rat.le_trans hf8_nn hf8_lo
  constructor
  · rw [hy_eq]
    unfold linearLowerEnv4
    have h := rat_mul_le_mul hf8_lo hmq4_lo hf8_nn hmq4_lo_nn
    rw [Rat.mul_assoc]
    exact h
  · rw [hy_eq]
    unfold linearUpperEnv4
    have h := rat_mul_le_mul hf8_hi hmq4_hi hf8_mid_nn hmq4_nn
    rw [Rat.mul_assoc (ratPow8 (1 + u))]
    exact h

/-- Combined Theorem 3: exact pointwise upper and lower envelopes for BOTH
`NoisyVertexStep4` and `NoisyLinearStep4`. -/
theorem noisyFourthRootStep_envelope (α β μ p0 p1 u m yv yl : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) ≤ β)
    (hp1 : p1 ≤ (0 : Rat))
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1) (hm : (0 : Rat) < m)
    (hqLoLin : (0 : Rat) < qLoLinear p0 p1 u m)
    (hv : NoisyVertexStep4 α β μ u m yv)
    (hl : NoisyLinearStep4 p0 p1 u m yl) :
    (vertexLowerEnv4 α β μ u m ≤ yv ∧ yv ≤ vertexUpperEnv4 α β μ u m) ∧
    (linearLowerEnv4 p0 p1 u m ≤ yl ∧ yl ≤ linearUpperEnv4 p0 p1 u m) :=
  ⟨noisyVertexStep4_envelope α β μ u m yv hα hβ hu0 hu1 hm hv,
   noisyLinearStep4_envelope p0 p1 u m yl hp1 hu0 hu1 hm hqLoLin hl⟩

end SoapVertexFourthRoot
