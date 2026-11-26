/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonVertexPolar.Defs

/-!
# Algebraic Equivalence, Quadratic Rounding-Error Annihilation, Pointwise Envelope,
and Bernstein Degree-5 Certificate Engine (`muon-vertex-polar`)

All proofs are pure Lean 4 `Init` (zero Mathlib, zero `native_decide`).
-/

namespace MuonVertexPolar

/-! ## Elementary `Rat` Order Helpers -/

private theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := Rat.add_le_add_right (c := -b) |>.mpr h
  grind

private theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := Rat.add_le_add_right (c := b) |>.mpr h
  grind

private theorem rat_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
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

private theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    c * a ≤ c * b := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ b - a := rat_sub_nonneg h
  have h2 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]
  exact h2

private theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

private theorem rat_mul_le_mul {a b c d : Rat}
    (hab : a ≤ b) (hcd : c ≤ d) (ha : (0 : Rat) ≤ a) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * d := by
  have hb : (0 : Rat) ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hab hc)
    (rat_mul_le_mul_of_nonneg_left hcd hb)

private theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  cases Rat.le_total (a := (0 : Rat)) (b := x) with
  | inl h => exact Rat.mul_nonneg h h
  | inr h =>
    have hneg : (0 : Rat) ≤ -x := by
      have := rat_sub_nonneg h
      grind
    have eq : x * x = (-x) * (-x) := by grind
    rw [eq]
    exact Rat.mul_nonneg hneg hneg

private theorem rat_sq_le_sq_of_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  rat_mul_le_mul hab hab ha ha

private theorem rat_max_eq_right {a b : Rat} (h : a ≤ b) : max a b = b := by
  change (if a ≤ b then b else a) = b
  simp [h]

private theorem rat_max_eq_left {a b : Rat} (h : b ≤ a) : max a b = a := by
  change (if a ≤ b then b else a) = a
  split
  · rename_i h'
    exact Rat.le_antisymm h h'
  · rfl

private theorem rat_le_max_left (a b : Rat) : a ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact h
  | inr h => rw [rat_max_eq_left h]; exact Rat.le_refl

private theorem rat_le_max_right (a b : Rat) : b ≤ max a b := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h => rw [rat_max_eq_right h]; exact Rat.le_refl
  | inr h => rw [rat_max_eq_left h]; exact h

private theorem rat_sq_le_max_sq {L v R : Rat} (hL : L ≤ v) (hR : v ≤ R) :
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

private theorem rat_nonneg_of_mul_pos_nonneg {k y : Rat} (hk : (0 : Rat) < k)
    (hky : (0 : Rat) ≤ k * y) : (0 : Rat) ≤ y := by
  cases Rat.le_total (a := (0 : Rat)) (b := y) with
  | inl h => exact h
  | inr hy =>
    by_cases hy0 : y = 0
    · rw [hy0]; exact Rat.le_refl
    · have hneg_y : (0 : Rat) < -y := by
        have h1 : (0 : Rat) ≤ -y := by
          have := rat_sub_nonneg hy
          grind
        have hne : -y ≠ 0 := by intro h; apply hy0; grind
        exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)
      have hpos : (0 : Rat) < k * (-y) := rat_mul_pos hk hneg_y
      have hneg_ky : k * y < 0 := by
        have eq : k * (-y) = -(k * y) := by grind
        rw [eq] at hpos
        have hle : k * y ≤ 0 := by
          have h1 : (0 : Rat) ≤ -(k * y) := Rat.le_of_lt hpos
          exact rat_le_of_sub_nonneg (by grind)
        have hne : k * y ≠ 0 := by
          intro h0
          rw [h0] at hpos
          exact Rat.lt_irrefl hpos
        exact Rat.lt_of_le_of_ne hle hne
      exact False.elim (Rat.not_le.mpr hneg_ky hky)

private theorem rat_add_le_add {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr hab) (Rat.add_le_add_left.mpr hcd)

private theorem rat_max_mul_nonneg_left {a b c : Rat} (hc : (0 : Rat) ≤ c) :
    c * max a b = max (c * a) (c * b) := by
  cases Rat.le_total (a := a) (b := b) with
  | inl h =>
    have h1 : max a b = b := rat_max_eq_right h
    have h2 : c * a ≤ c * b := rat_mul_le_mul_of_nonneg_left h hc
    have h3 : max (c * a) (c * b) = c * b := rat_max_eq_right h2
    rw [h1, h3]
  | inr h =>
    have h1 : max a b = a := rat_max_eq_left h
    have h2 : c * b ≤ c * a := rat_mul_le_mul_of_nonneg_left h hc
    have h3 : max (c * a) (c * b) = c * a := rat_max_eq_left h2
    rw [h1, h3]

private theorem rat_add_max_left (a b c : Rat) :
    a + max b c = max (a + b) (a + c) := by
  cases Rat.le_total (a := b) (b := c) with
  | inl h =>
    rw [rat_max_eq_right h, rat_max_eq_right (Rat.add_le_add_left.mpr h)]
  | inr h =>
    rw [rat_max_eq_left h, rat_max_eq_left (Rat.add_le_add_left.mpr h)]

/-! ## Theorem 1: Exact Algebraic Equivalence (Monomial ↔ Shifted-Square) -/

/-- Every odd quintic `a * x + b * x^3 + c * x^5` with `c ≠ 0` is identically equal
to the 3-parameter shifted-square (vertex) form `x * (α + c * (x^2 - μ)^2)` with
`μ = -b / (2 * c)` and `α = a - b^2 / (4 * c)`. -/
theorem shifted_square_equiv_monomial (a b c x : Rat) (hc : c ≠ 0) :
    let μ := -b / (2 * c)
    let α := a - (b * b) / (4 * c)
    a * x + b * (x * x * x) + c * (x * x * x * x * x) =
      x * (α + c * ((x * x - μ) * (x * x - μ))) := by
  dsimp only
  have hc2 : (2 * c) ≠ 0 := by
    intro h
    cases Rat.mul_eq_zero.mp h with
    | inl h2 => exact absurd h2 (by decide)
    | inr h0 => exact hc h0
  have hc4 : (4 * c) ≠ 0 := by
    intro h
    cases Rat.mul_eq_zero.mp h with
    | inl h4 => exact absurd h4 (by decide)
    | inr h0 => exact hc h0
  have hμ : 2 * c * (-b / (2 * c)) = -b := by
    rw [Rat.mul_comm, Rat.div_mul_cancel hc2]
  have hα : 4 * c * ((b * b) / (4 * c)) = b * b := by
    rw [Rat.mul_comm, Rat.div_mul_cancel hc4]
  have hdiff : (4 * c) * ((a * x + b * (x * x * x) + c * (x * x * x * x * x)) -
      x * ((a - (b * b) / (4 * c)) + c * ((x * x - (-b / (2 * c))) * (x * x - (-b / (2 * c)))))) = 0 := by
    let μ := -b / (2 * c)
    let q := (b * b) / (4 * c)
    have hμ2 : 4 * c * (c * (μ * μ)) = b * b := by
      have : 4 * c * (c * (μ * μ)) = (2 * c * μ) * (2 * c * μ) := by grind
      rw [this, hμ]
      grind
    have hμ1 : 4 * c * (c * (x * x * μ)) = -2 * c * b * (x * x) := by
      have : 4 * c * (c * (x * x * μ)) = 2 * c * (x * x) * (2 * c * μ) := by grind
      rw [this, hμ]
      grind
    have hexp : (4 * c) * ((a * x + b * (x * x * x) + c * (x * x * x * x * x)) -
        x * ((a - q) + c * ((x * x - μ) * (x * x - μ)))) =
        x * (4 * c * q - 4 * c * (c * (μ * μ))) +
        2 * x * (4 * c * (c * (x * x * μ)) + 2 * c * b * (x * x)) := by
      grind
    change (4 * c) * ((a * x + b * (x * x * x) + c * (x * x * x * x * x)) -
        x * ((a - q) + c * ((x * x - μ) * (x * x - μ)))) = 0
    rw [hexp, hα, hμ2, hμ1]
    grind
  cases Rat.mul_eq_zero.mp hdiff with
  | inl h => exact False.elim (hc4 h)
  | inr h => grind

/-! ## Theorem 2: Quadratic Rounding-Error Annihilation at `x = 1` -/

/-- At `x = 1` and `μ = 1`, a relative Gram-matrix rounding perturbation `a = 1 * (1 + δ1)`
with `|δ1| ≤ u` enters `β * (a - 1)^2` purely quadratically as `β * δ1^2 ≤ β * u^2`,
whereas in monomial form `b * a + c * a^2` the error has a first-order linear term
`(b + 2 * c) * δ1`. -/
theorem shifted_square_quadratic_error_at_one (α β b c u δ1 : Rat)
    (hβ : (0 : Rat) ≤ β) (hlo : -u ≤ δ1) (hhi : δ1 ≤ u) :
    let a := (1 : Rat) * (1 + δ1)
    (α + β * ((a - 1) * (a - 1)) - α = β * (δ1 * δ1)) ∧
    (β * ((a - 1) * (a - 1)) ≤ β * (u * u)) ∧
    (b * a + c * (a * a) - (b + c) = (b + 2 * c) * δ1 + c * (δ1 * δ1)) := by
  dsimp only
  refine ⟨by grind, ?_, by grind⟩
  have h1 : (1 * (1 + δ1) - 1) * (1 * (1 + δ1) - 1) = δ1 * δ1 := by grind
  rw [h1]
  have hsq : δ1 * δ1 ≤ max ((-u) * (-u)) (u * u) := rat_sq_le_max_sq hlo hhi
  have hmax : max ((-u) * (-u)) (u * u) = u * u := by
    have heq : (-u) * (-u) = u * u := by grind
    rw [heq, rat_max_eq_right Rat.le_refl]
  rw [hmax] at hsq
  exact rat_mul_le_mul_of_nonneg_left hsq hβ

/-! ## Pointwise Exact Degree-5 Envelope Lemma -/

/-- Every adversarial output `y` of `NoisyShiftedStep α β μ u x y` (with `α, β > 0`,
`0 ≤ u < 1`, `x ≥ 0`) is sandwiched between the exact degree-5 lower and upper envelopes. -/
theorem noisyShiftedStep_envelope (α β μ u x y : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) < β)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1) (hx : (0 : Rat) ≤ x)
    (hstep : NoisyShiftedStep α β μ u x y) :
    y ≤ max (shiftedUpperMinus α β μ u x) (shiftedUpperPlus α β μ u x) ∧
    (shiftedLowerBase α u x ≤ y) ∧
    (x * x * (1 + u) ≤ μ → shiftedLowerLeft α β μ u x ≤ y) ∧
    (μ ≤ x * x * (1 - u) → shiftedLowerRight α β μ u x ≤ y) := by
  rcases hstep with ⟨δ1, δ2, δ3, δ4, δ5, δ6,
    ⟨h1l, h1r⟩, ⟨h2l, h2r⟩, ⟨h3l, h3r⟩, ⟨h4l, h4r⟩, ⟨h5l, h5r⟩, ⟨h6l, h6r⟩, hy⟩
  have hlo_pos : (0 : Rat) ≤ 1 - u := rat_sub_nonneg (Rat.le_of_lt hu1)
  have hup_pos : (0 : Rat) ≤ 1 + u := Rat.le_trans hlo_pos (by
    apply rat_le_of_sub_nonneg
    have : (1 + u) - (1 - u) = u + u := by grind
    rw [this]
    have := rat_add_le_add hu0 hu0; grind)
  have h_bounds : ∀ δ : Rat, -u ≤ δ → δ ≤ u → 1 - u ≤ 1 + δ ∧ 1 + δ ≤ 1 + u := by
    intro δ hl hr
    constructor
    · apply rat_le_of_sub_nonneg; have := rat_sub_nonneg hl; grind
    · apply rat_le_of_sub_nonneg; have := rat_sub_nonneg hr; grind
  have ⟨h1_lo, h1_hi⟩ := h_bounds δ1 h1l h1r
  have ⟨h2_lo, h2_hi⟩ := h_bounds δ2 h2l h2r
  have ⟨h3_lo, h3_hi⟩ := h_bounds δ3 h3l h3r
  have ⟨h4_lo, h4_hi⟩ := h_bounds δ4 h4l h4r
  have ⟨h5_lo, h5_hi⟩ := h_bounds δ5 h5l h5r
  have ⟨h6_lo, h6_hi⟩ := h_bounds δ6 h6l h6r
  have h2_nn : (0 : Rat) ≤ 1 + δ2 := Rat.le_trans hlo_pos h2_lo
  have h3_nn : (0 : Rat) ≤ 1 + δ3 := Rat.le_trans hlo_pos h3_lo
  have h4_nn : (0 : Rat) ≤ 1 + δ4 := Rat.le_trans hlo_pos h4_lo
  have h5_nn : (0 : Rat) ≤ 1 + δ5 := Rat.le_trans hlo_pos h5_lo
  have h6_nn : (0 : Rat) ≤ 1 + δ6 := Rat.le_trans hlo_pos h6_lo
  let lo := 1 - u
  let up := 1 + u
  let f2 := (1 + δ2) * (1 + δ2)
  let f4 := f2 * (1 + δ3) * (1 + δ4)
  let f56 := (1 + δ5) * (1 + δ6)
  have hf2_lo : lo * lo ≤ f2 := rat_mul_le_mul h2_lo h2_lo hlo_pos hlo_pos
  have hf2_hi : f2 ≤ up * up := rat_mul_le_mul h2_hi h2_hi h2_nn h2_nn
  have hf4_lo : (lo * lo) * (lo * lo) ≤ f4 := by
    have hlo2 : (0 : Rat) ≤ lo * lo := Rat.mul_nonneg hlo_pos hlo_pos
    have h34_lo : lo * lo ≤ (1 + δ3) * (1 + δ4) := rat_mul_le_mul h3_lo h4_lo hlo_pos hlo_pos
    have eq : f4 = f2 * ((1 + δ3) * (1 + δ4)) := by grind
    rw [eq]
    exact rat_mul_le_mul hf2_lo h34_lo hlo2 hlo2
  have hf4_hi : f4 ≤ (up * up) * (up * up) := by
    have hf2_nn : (0 : Rat) ≤ f2 := Rat.mul_nonneg h2_nn h2_nn
    have h34_nn : (0 : Rat) ≤ (1 + δ3) * (1 + δ4) := Rat.mul_nonneg h3_nn h4_nn
    have h34_hi : (1 + δ3) * (1 + δ4) ≤ up * up := rat_mul_le_mul h3_hi h4_hi h3_nn h4_nn
    have eq : f4 = f2 * ((1 + δ3) * (1 + δ4)) := by grind
    rw [eq]
    exact rat_mul_le_mul hf2_hi h34_hi hf2_nn h34_nn
  have hf4_nn : (0 : Rat) ≤ f4 :=
    Rat.le_trans (Rat.mul_nonneg (Rat.mul_nonneg hlo_pos hlo_pos) (Rat.mul_nonneg hlo_pos hlo_pos)) hf4_lo
  have hf56_lo : lo * lo ≤ f56 := rat_mul_le_mul h5_lo h6_lo hlo_pos hlo_pos
  have hf56_hi : f56 ≤ up * up := rat_mul_le_mul h5_hi h6_hi h5_nn h6_nn
  have hf56_nn : (0 : Rat) ≤ f56 := Rat.mul_nonneg h5_nn h6_nn
  let a := x * x * (1 + δ1)
  have hy_eq : y = f56 * x * (α + f4 * β * ((a - μ) * (a - μ))) := by
    rw [hy]; grind
  have hβ_nn : (0 : Rat) ≤ β := Rat.le_of_lt hβ
  have hα_nn : (0 : Rat) ≤ α := Rat.le_of_lt hα
  have hsq_nn : (0 : Rat) ≤ (a - μ) * (a - μ) := rat_sq_nonneg (a - μ)
  have ht_nn : (0 : Rat) ≤ f4 * β * ((a - μ) * (a - μ)) :=
    Rat.mul_nonneg (Rat.mul_nonneg hf4_nn hβ_nn) hsq_nn
  have hαt_nn : (0 : Rat) ≤ α + f4 * β * ((a - μ) * (a - μ)) := by
    have := rat_add_le_add hα_nn ht_nn; grind
  have hx2_nn : (0 : Rat) ≤ x * x := rat_sq_nonneg x
  have ha_lo : x * x * lo - μ ≤ a - μ := by
    have h := rat_mul_le_mul_of_nonneg_left h1_lo hx2_nn
    apply rat_le_of_sub_nonneg; have := rat_sub_nonneg h; grind
  have ha_hi : a - μ ≤ x * x * up - μ := by
    have h := rat_mul_le_mul_of_nonneg_left h1_hi hx2_nn
    apply rat_le_of_sub_nonneg; have := rat_sub_nonneg h; grind
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Upper bound
    let dm := x * x * lo - μ
    let dp := x * x * up - μ
    have hsq_up : (a - μ) * (a - μ) ≤ max (dm * dm) (dp * dp) :=
      rat_sq_le_max_sq ha_lo ha_hi
    have ht_up : f4 * β * ((a - μ) * (a - μ)) ≤
        (up * up) * (up * up) * β * max (dm * dm) (dp * dp) := by
      have hf4β_lo : f4 * β ≤ (up * up) * (up * up) * β :=
        rat_mul_le_mul_of_nonneg_right hf4_hi hβ_nn
      exact rat_mul_le_mul hf4β_lo hsq_up (Rat.mul_nonneg hf4_nn hβ_nn) hsq_nn
    have hinner : α + f4 * β * ((a - μ) * (a - μ)) ≤
        α + (up * up) * (up * up) * β * max (dm * dm) (dp * dp) :=
      rat_add_le_add Rat.le_refl ht_up
    have houter : f56 * x * (α + f4 * β * ((a - μ) * (a - μ))) ≤
        (up * up) * x * (α + (up * up) * (up * up) * β * max (dm * dm) (dp * dp)) :=
      rat_mul_le_mul (rat_mul_le_mul_of_nonneg_right hf56_hi hx) hinner
        (Rat.mul_nonneg hf56_nn hx) hαt_nn
    rw [hy_eq]
    have hup4β_nn : (0 : Rat) ≤ (up * up) * (up * up) * β :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hup_pos hup_pos) (Rat.mul_nonneg hup_pos hup_pos)) hβ_nn
    have hup2x_nn : (0 : Rat) ≤ (up * up) * x :=
      Rat.mul_nonneg (Rat.mul_nonneg hup_pos hup_pos) hx
    rw [rat_max_mul_nonneg_left hup4β_nn, rat_add_max_left, rat_max_mul_nonneg_left hup2x_nn] at houter
    exact houter
  · -- Universal base lower bound
    rw [hy_eq]
    have hinner : α ≤ α + f4 * β * ((a - μ) * (a - μ)) := by
      have := rat_add_le_add (Rat.le_refl (a := α)) ht_nn; grind
    have h1 : (lo * lo) * x * α ≤ f56 * x * (α + f4 * β * ((a - μ) * (a - μ))) :=
      rat_mul_le_mul (rat_mul_le_mul_of_nonneg_right hf56_lo hx) hinner
        (Rat.mul_nonneg (Rat.mul_nonneg hlo_pos hlo_pos) hx) hα_nn
    have eq : shiftedLowerBase α u x = (lo * lo) * x * α := by
      unfold shiftedLowerBase; grind
    rw [eq]
    exact h1
  · -- Left lower bound when x^2*(1+u) ≤ μ
    intro hleft
    rw [hy_eq]
    let dl := μ - x * x * up
    have hdl_nn : (0 : Rat) ≤ dl := rat_sub_nonneg hleft
    have hdl_le : dl ≤ μ - a := by
      apply rat_le_of_sub_nonneg; have := rat_sub_nonneg ha_hi; grind
    have hsq_lo : dl * dl ≤ (a - μ) * (a - μ) := by
      have h1 := rat_sq_le_sq_of_nonneg hdl_nn hdl_le
      have eq : (μ - a) * (μ - a) = (a - μ) * (a - μ) := by grind
      rw [eq] at h1
      exact h1
    have hlo2_nn : (0 : Rat) ≤ lo * lo := Rat.mul_nonneg hlo_pos hlo_pos
    have hlo4_nn : (0 : Rat) ≤ (lo * lo) * (lo * lo) := Rat.mul_nonneg hlo2_nn hlo2_nn
    have ht_lo : (lo * lo) * (lo * lo) * β * (dl * dl) ≤ f4 * β * ((a - μ) * (a - μ)) :=
      rat_mul_le_mul (rat_mul_le_mul_of_nonneg_right hf4_lo hβ_nn) hsq_lo
        (Rat.mul_nonneg hlo4_nn hβ_nn) (Rat.mul_nonneg hdl_nn hdl_nn)
    have hinner : α + (lo * lo) * (lo * lo) * β * (dl * dl) ≤
        α + f4 * β * ((a - μ) * (a - μ)) :=
      rat_add_le_add Rat.le_refl ht_lo
    exact rat_mul_le_mul (rat_mul_le_mul_of_nonneg_right hf56_lo hx) hinner
      (Rat.mul_nonneg hlo2_nn hx)
      (Rat.le_trans hα_nn (by
        have hterm : (0 : Rat) ≤ (lo * lo) * (lo * lo) * β * (dl * dl) :=
          Rat.mul_nonneg (Rat.mul_nonneg hlo4_nn hβ_nn) (Rat.mul_nonneg hdl_nn hdl_nn)
        have := rat_add_le_add (Rat.le_refl (a := α)) hterm
        grind))
  · -- Right lower bound when μ ≤ x^2*(1-u)
    intro hright
    rw [hy_eq]
    let dr := x * x * lo - μ
    have hdr_nn : (0 : Rat) ≤ dr := rat_sub_nonneg hright
    have hsq_lo : dr * dr ≤ (a - μ) * (a - μ) := rat_sq_le_sq_of_nonneg hdr_nn ha_lo
    have hlo2_nn : (0 : Rat) ≤ lo * lo := Rat.mul_nonneg hlo_pos hlo_pos
    have hlo4_nn : (0 : Rat) ≤ (lo * lo) * (lo * lo) := Rat.mul_nonneg hlo2_nn hlo2_nn
    have ht_lo : (lo * lo) * (lo * lo) * β * (dr * dr) ≤ f4 * β * ((a - μ) * (a - μ)) :=
      rat_mul_le_mul (rat_mul_le_mul_of_nonneg_right hf4_lo hβ_nn) hsq_lo
        (Rat.mul_nonneg hlo4_nn hβ_nn) (Rat.mul_nonneg hdr_nn hdr_nn)
    have hinner : α + (lo * lo) * (lo * lo) * β * (dr * dr) ≤
        α + f4 * β * ((a - μ) * (a - μ)) :=
      rat_add_le_add Rat.le_refl ht_lo
    exact rat_mul_le_mul (rat_mul_le_mul_of_nonneg_right hf56_lo hx) hinner
      (Rat.mul_nonneg hlo2_nn hx)
      (Rat.le_trans hα_nn (by
        have hterm : (0 : Rat) ≤ (lo * lo) * (lo * lo) * β * (dr * dr) :=
          Rat.mul_nonneg (Rat.mul_nonneg hlo4_nn hβ_nn) (Rat.mul_nonneg hdr_nn hdr_nn)
        have := rat_add_le_add (Rat.le_refl (a := α)) hterm
        grind))

/-! ## Bernstein Degree-5 Nonnegativity Engine (Exact `Int`-Cleared Certificates) -/

/-- Odd-plus-constant degree-5 polynomial `c0 + c1*x + c3*x^3 + c5*x^5`. -/
def evalOdd5 (c0 c1 c3 c5 x : Rat) : Rat :=
  c0 + c1 * x + c3 * (x * x * x) + c5 * (x * x * x * x * x)

/-- Homogeneous Bernstein basis coefficients `(B0, B1, B2, B3, B4, B5)` for
`(hi - lo)^5 * evalOdd5 c0 c1 c3 c5 x` expanded in `s^(5-k) * t^k` where
`s = hi - x` and `t = x - lo`. -/
def bernsteinOdd5 (c0 c1 c3 c5 lo hi : Rat) : Rat × Rat × Rat × Rat × Rat × Rat :=
  let lo2 := lo * lo
  let lo3 := lo2 * lo
  let lo4 := lo3 * lo
  let lo5 := lo4 * lo
  let hi2 := hi * hi
  let hi3 := hi2 * hi
  let hi4 := hi3 * hi
  let hi5 := hi4 * hi
  ( c0 + c1 * lo + c3 * lo3 + c5 * lo5
  , 5 * c0 + c1 * (4 * lo + hi) + c3 * (2 * lo3 + 3 * lo2 * hi) + c5 * (5 * lo4 * hi)
  , 10 * c0 + c1 * (6 * lo + 4 * hi) + c3 * (lo3 + 6 * lo2 * hi + 3 * lo * hi2) + c5 * (10 * lo3 * hi2)
  , 10 * c0 + c1 * (4 * lo + 6 * hi) + c3 * (3 * lo2 * hi + 6 * lo * hi2 + hi3) + c5 * (10 * lo2 * hi3)
  , 5 * c0 + c1 * (lo + 4 * hi) + c3 * (3 * lo * hi2 + 2 * hi3) + c5 * (5 * lo * hi4)
  , c0 + c1 * hi + c3 * hi3 + c5 * hi5 )

/-- Exact polynomial identity expanding `(hi - lo)^5 * evalOdd5 c0 c1 c3 c5 x`
in the nonnegative Bernstein basis `s^(5-k) * t^k` (`s = hi - x`, `t = x - lo`). -/
theorem bernsteinOdd5_identity (c0 c1 c3 c5 lo hi x : Rat) :
    let w := hi - lo
    let s := hi - x
    let t := x - lo
    let (b0, b1, b2, b3, b4, b5) := bernsteinOdd5 c0 c1 c3 c5 lo hi
    (w * w * w * w * w) * evalOdd5 c0 c1 c3 c5 x =
      b0 * (s * s * s * s * s) +
      b1 * (s * s * s * s * t) +
      b2 * (s * s * s * t * t) +
      b3 * (s * s * t * t * t) +
      b4 * (s * t * t * t * t) +
      b5 * (t * t * t * t * t) := by
  unfold evalOdd5 bernsteinOdd5
  dsimp only
  grind

/-- Bernstein Degree-5 Nonnegativity Theorem: if `lo < hi` and all 6 Bernstein
coefficients of `evalOdd5 c0 c1 c3 c5` on `[lo, hi]` are nonnegative, then
`evalOdd5 c0 c1 c3 c5 x ≥ 0` for every `x ∈ [lo, hi]`. -/
theorem bernsteinOdd5_nonneg_on (c0 c1 c3 c5 lo hi : Rat) (hlo_lt : lo < hi)
    (hb : let (b0, b1, b2, b3, b4, b5) := bernsteinOdd5 c0 c1 c3 c5 lo hi
          (0 : Rat) ≤ b0 ∧ (0 : Rat) ≤ b1 ∧ (0 : Rat) ≤ b2 ∧
          (0 : Rat) ≤ b3 ∧ (0 : Rat) ≤ b4 ∧ (0 : Rat) ≤ b5)
    {x : Rat} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    (0 : Rat) ≤ evalOdd5 c0 c1 c3 c5 x := by
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩
  let w := hi - lo
  let s := hi - x
  let t := x - lo
  have hw_pos : (0 : Rat) < w := by
    have h1 : (0 : Rat) ≤ w := rat_sub_nonneg (Rat.le_of_lt hlo_lt)
    have hne : w ≠ 0 := by intro h; exact Rat.ne_of_lt hlo_lt (by grind)
    exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)
  have hw5_pos : (0 : Rat) < w * w * w * w * w :=
    rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hw_pos hw_pos) hw_pos) hw_pos) hw_pos
  have hs : (0 : Rat) ≤ s := rat_sub_nonneg hhi
  have ht : (0 : Rat) ≤ t := rat_sub_nonneg hlo
  have hsum : (0 : Rat) ≤ (w * w * w * w * w) * evalOdd5 c0 c1 c3 c5 x := by
    rw [bernsteinOdd5_identity c0 c1 c3 c5 lo hi x]
    have t0 : (0 : Rat) ≤ (bernsteinOdd5 c0 c1 c3 c5 lo hi).1 * (s * s * s * s * s) :=
      Rat.mul_nonneg hb0 (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hs hs) hs) hs) hs)
    have t1 : (0 : Rat) ≤ (bernsteinOdd5 c0 c1 c3 c5 lo hi).2.1 * (s * s * s * s * t) :=
      Rat.mul_nonneg hb1 (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hs hs) hs) hs) ht)
    have t2 : (0 : Rat) ≤ (bernsteinOdd5 c0 c1 c3 c5 lo hi).2.2.1 * (s * s * s * t * t) :=
      Rat.mul_nonneg hb2 (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hs hs) hs) ht) ht)
    have t3 : (0 : Rat) ≤ (bernsteinOdd5 c0 c1 c3 c5 lo hi).2.2.2.1 * (s * s * t * t * t) :=
      Rat.mul_nonneg hb3 (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hs hs) ht) ht) ht)
    have t4 : (0 : Rat) ≤ (bernsteinOdd5 c0 c1 c3 c5 lo hi).2.2.2.2.1 * (s * t * t * t * t) :=
      Rat.mul_nonneg hb4 (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hs ht) ht) ht) ht)
    have t5 : (0 : Rat) ≤ (bernsteinOdd5 c0 c1 c3 c5 lo hi).2.2.2.2.2 * (t * t * t * t * t) :=
      Rat.mul_nonneg hb5 (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg ht ht) ht) ht) ht)
    have hadd_nn : ∀ {a b : Rat}, (0 : Rat) ≤ a → (0 : Rat) ≤ b → (0 : Rat) ≤ a + b := by
      intro a b ha hb; have := rat_add_le_add ha hb; grind
    exact hadd_nn (hadd_nn (hadd_nn (hadd_nn (hadd_nn t0 t1) t2) t3) t4) t5
  exact rat_nonneg_of_mul_pos_nonneg hw5_pos hsum

/-! ### Cleared-Denominator `Int` Bernstein Partition Checker (Zero `Rat.normalize` in Kernel!) -/

/-- Pure-integer check that all 6 cleared-denominator Bernstein coefficients of
`(c0N/C) + (c1N/C)*x + (c3N/C)*x^3 + (c5N/C)*x^5` on `[loN/D, hiN/D]` are `≥ 0`
(for `C > 0, D > 0`). Runs in microseconds in both Lean's kernel and `nanoda`. -/
def checkBernsteinSegInt (c0N c1N c3N c5N D loN hiN : Int) : Bool :=
  let d2 := D * D
  let d4 := d2 * d2
  let d5 := d4 * D
  let lo2 := loN * loN
  let lo3 := lo2 * loN
  let lo4 := lo3 * loN
  let lo5 := lo4 * loN
  let hi2 := hiN * hiN
  let hi3 := hi2 * hiN
  let hi4 := hi3 * hiN
  let hi5 := hi4 * hiN
  let b0 := c0N * d5 + c1N * loN * d4 + c3N * lo3 * d2 + c5N * lo5
  let b1 := 5 * c0N * d5 + c1N * (4 * loN + hiN) * d4 + c3N * (2 * lo3 + 3 * lo2 * hiN) * d2 + c5N * (5 * lo4 * hiN)
  let b2 := 10 * c0N * d5 + c1N * (6 * loN + 4 * hiN) * d4 + c3N * (lo3 + 6 * lo2 * hiN + 3 * loN * hi2) * d2 + c5N * (10 * lo3 * hi2)
  let b3 := 10 * c0N * d5 + c1N * (4 * loN + 6 * hiN) * d4 + c3N * (3 * lo2 * hiN + 6 * loN * hi2 + hi3) * d2 + c5N * (10 * lo2 * hi3)
  let b4 := 5 * c0N * d5 + c1N * (loN + 4 * hiN) * d4 + c3N * (3 * loN * hi2 + 2 * hi3) * d2 + c5N * (5 * loN * hi4)
  let b5 := c0N * d5 + c1N * hiN * d4 + c3N * hi3 * d2 + c5N * hi5
  decide (loN < hiN) && decide (0 ≤ b0) && decide (0 ≤ b1) && decide (0 ≤ b2) &&
    decide (0 ≤ b3) && decide (0 ≤ b4) && decide (0 ≤ b5)

/-- Check an entire contiguous breakpoint list `[p0, p1, ..., pk]` (representing `p_i / D`). -/
def checkBernsteinPartitionInt (c0N c1N c3N c5N D : Int) : List Int → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest =>
    checkBernsteinSegInt c0N c1N c3N c5N D p q && checkBernsteinPartitionInt c0N c1N c3N c5N D (q :: rest)

private theorem rat_ofNat_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have h1 : (0 : Rat) ≤ (1 : Rat) := by decide
    have h2 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := Rat.natCast_add k 1
    rw [h2]
    have := rat_add_le_add ih h1; grind

private theorem rat_ofInt_nonneg {a : Int} (h : (0 : Int) ≤ a) : (0 : Rat) ≤ (a : Rat) := by
  cases a with
  | ofNat n => exact rat_ofNat_nonneg n
  | negSucc n => omega

private theorem rat_ofInt_pos {a : Int} (h : (0 : Int) < a) : (0 : Rat) < (a : Rat) := by
  have hnn : (0 : Rat) ≤ (a : Rat) := rat_ofInt_nonneg (by omega)
  have hne : (a : Rat) ≠ 0 := by
    intro h0
    have h1 : (a : Rat).num = 0 := by rw [h0]; rfl
    have h2 : (a : Rat).num = a := rfl
    omega
  exact Rat.lt_of_le_of_ne hnn (Ne.symm hne)

theorem rat_ofInt_div_nonneg {a b : Int} (ha : (0 : Int) ≤ a) (hb : (0 : Int) < b) :
    (0 : Rat) ≤ (a : Rat) / (b : Rat) := by
  have hb_pos : (0 : Rat) < (b : Rat) := rat_ofInt_pos hb
  have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt hb_pos
  have hmul : (b : Rat) * ((a : Rat) / (b : Rat)) = (a : Rat) := by
    rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
  exact rat_nonneg_of_mul_pos_nonneg hb_pos (by rw [hmul]; exact rat_ofInt_nonneg ha)

theorem rat_ofInt_div_pos {a b : Int} (ha : (0 : Int) < a) (hb : (0 : Int) < b) :
    (0 : Rat) < (a : Rat) / (b : Rat) := by
  have hnn : (0 : Rat) ≤ (a : Rat) / (b : Rat) := rat_ofInt_div_nonneg (by omega) hb
  have hne : (a : Rat) / (b : Rat) ≠ 0 := by
    intro h0
    have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hb)
    have hmul : (b : Rat) * ((a : Rat) / (b : Rat)) = (a : Rat) := by
      rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
    rw [h0] at hmul
    have ha0 : (a : Rat) = 0 := by grind
    have ha_pos : (0 : Rat) < (a : Rat) := rat_ofInt_pos ha
    rw [ha0] at ha_pos
    exact Rat.lt_irrefl ha_pos
  exact Rat.lt_of_le_of_ne hnn (Ne.symm hne)

theorem rat_div_one_eq (a : Int) : (a : Rat) / (1 : Rat) = (a : Rat) := by
  have h1 : (1 : Rat) ≠ 0 := by decide
  have h2 : (1 : Rat) * ((a : Rat) / (1 : Rat)) = (a : Rat) := by
    rw [Rat.mul_comm, Rat.div_mul_cancel h1]
  grind

theorem rat_ofInt_div_lt_one {a b : Int} (hab : a < b) (hb : (0 : Int) < b) :
    (a : Rat) / (b : Rat) < 1 := by
  have h1 : (a : Rat) / (b : Rat) < (b : Rat) / (b : Rat) := by
    have hb_pos : (0 : Rat) < (b : Rat) := rat_ofInt_pos hb
    have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt hb_pos
    have hsub : (0 : Rat) < ((b - a : Int) : Rat) / (b : Rat) := rat_ofInt_div_pos (by omega) hb
    have heq : (b : Rat) / (b : Rat) - (a : Rat) / (b : Rat) = ((b - a : Int) : Rat) / (b : Rat) := by
      have hm1 : (b : Rat) * ((b : Rat) / (b : Rat)) = (b : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
      have hm2 : (b : Rat) * ((a : Rat) / (b : Rat)) = (a : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
      have hm3 : (b : Rat) * (((b - a : Int) : Rat) / (b : Rat)) = ((b - a : Int) : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
      have hba : ((b - a : Int) : Rat) = (b : Rat) - (a : Rat) := Rat.intCast_sub b a
      have hm : (b : Rat) * ((b : Rat) / (b : Rat) - (a : Rat) / (b : Rat) - ((b - a : Int) : Rat) / (b : Rat)) = 0 := by grind
      cases Rat.mul_eq_zero.mp hm with | inl h => exact False.elim (hb_ne h) | inr h => grind
    have hle : (a : Rat) / (b : Rat) ≤ (b : Rat) / (b : Rat) :=
      rat_le_of_sub_nonneg (by rw [heq]; exact Rat.le_of_lt hsub)
    have hne : (a : Rat) / (b : Rat) ≠ (b : Rat) / (b : Rat) := by
      intro h; rw [h] at heq
      have : ((b - a : Int) : Rat) / (b : Rat) = 0 := by grind
      rw [this] at hsub; exact Rat.lt_irrefl hsub
    exact Rat.lt_of_le_of_ne hle hne
  have hbb : (b : Rat) / (b : Rat) = 1 := by
    have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hb)
    have hm : (b : Rat) * ((b : Rat) / (b : Rat) - 1) = 0 := by
      have : (b : Rat) * ((b : Rat) / (b : Rat)) = (b : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
      grind
    cases Rat.mul_eq_zero.mp hm with | inl h => exact False.elim (hb_ne h) | inr h => grind
  rw [hbb] at h1
  exact h1

private theorem rat_div_lt_div_of_pos {a b d : Int} (hab : a < b) (hd : (0 : Int) < d) :
    (a : Rat) / (d : Rat) < (b : Rat) / (d : Rat) := by
  have hd_pos : (0 : Rat) < (d : Rat) := rat_ofInt_pos hd
  have hd_ne : (d : Rat) ≠ 0 := Rat.ne_of_gt hd_pos
  have hsub : (0 : Rat) < ((b - a : Int) : Rat) := rat_ofInt_pos (by omega)
  have hdiv : (0 : Rat) < ((b - a : Int) : Rat) / (d : Rat) := by
    have hnn := rat_ofInt_div_nonneg (a := b - a) (b := d) (by omega) hd
    have hne : ((b - a : Int) : Rat) / (d : Rat) ≠ 0 := by
      intro h0
      have : (d : Rat) * (((b - a : Int) : Rat) / (d : Rat)) = ((b - a : Int) : Rat) := by
        rw [Rat.mul_comm, Rat.div_mul_cancel hd_ne]
      rw [h0] at this
      have h0' : ((b - a : Int) : Rat) = 0 := by grind
      rw [h0'] at hsub
      exact Rat.lt_irrefl hsub
    exact Rat.lt_of_le_of_ne hnn (Ne.symm hne)
  have heq : (b : Rat) / (d : Rat) - (a : Rat) / (d : Rat) = ((b - a : Int) : Rat) / (d : Rat) := by
    have h1 : (d : Rat) * ((b : Rat) / (d : Rat) - (a : Rat) / (d : Rat)) = ((b - a : Int) : Rat) := by
      have hb : (d : Rat) * ((b : Rat) / (d : Rat)) = (b : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hd_ne]
      have ha : (d : Rat) * ((a : Rat) / (d : Rat)) = (a : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hd_ne]
      have hba : ((b - a : Int) : Rat) = (b : Rat) - (a : Rat) := Rat.intCast_sub b a
      grind
    have h2 : (d : Rat) * (((b - a : Int) : Rat) / (d : Rat)) = ((b - a : Int) : Rat) := by
      rw [Rat.mul_comm, Rat.div_mul_cancel hd_ne]
    have h3 : (d : Rat) * (((b : Rat) / (d : Rat) - (a : Rat) / (d : Rat)) - ((b - a : Int) : Rat) / (d : Rat)) = 0 := by
      grind
    cases Rat.mul_eq_zero.mp h3 with
    | inl h => exact False.elim (hd_ne h)
    | inr h => grind
  have hle : (a : Rat) / (d : Rat) ≤ (b : Rat) / (d : Rat) :=
    rat_le_of_sub_nonneg (by rw [heq]; exact Rat.le_of_lt hdiv)
  have hne : (a : Rat) / (d : Rat) ≠ (b : Rat) / (d : Rat) := by
    intro h
    rw [h] at heq
    have : ((b - a : Int) : Rat) / (d : Rat) = 0 := by grind
    rw [this] at hdiv
    exact Rat.lt_irrefl hdiv
  exact Rat.lt_of_le_of_ne hle hne

private theorem rat_scaled_nonneg {C D : Int} (hC : (0 : Int) < C) (hD : (0 : Int) < D)
    {b : Rat} {bInt : Int}
    (heq : (C : Rat) * ((D : Rat) * (D : Rat) * (D : Rat) * (D : Rat) * (D : Rat)) * b = (bInt : Rat))
    (hnn : (0 : Int) ≤ bInt) : (0 : Rat) ≤ b := by
  have hC_pos : (0 : Rat) < (C : Rat) := rat_ofInt_pos hC
  have hD_pos : (0 : Rat) < (D : Rat) := rat_ofInt_pos hD
  have hCD5_pos : (0 : Rat) < (C : Rat) * ((D : Rat) * (D : Rat) * (D : Rat) * (D : Rat) * (D : Rat)) :=
    rat_mul_pos hC_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hD_pos hD_pos) hD_pos) hD_pos) hD_pos)
  exact rat_nonneg_of_mul_pos_nonneg hCD5_pos (by rw [heq]; exact rat_ofInt_nonneg hnn)

/-- Soundness of a single cleared-denominator integer Bernstein segment check. -/
theorem bernsteinSegInt_sound (c0N c1N c3N c5N C D loN hiN : Int)
    (hC : (0 : Int) < C) (hD : (0 : Int) < D)
    (hchk : checkBernsteinSegInt c0N c1N c3N c5N D loN hiN = true)
    {x : Rat} (hlo : (loN : Rat) / (D : Rat) ≤ x) (hhi : x ≤ (hiN : Rat) / (D : Rat)) :
    (0 : Rat) ≤ evalOdd5 ((c0N : Rat) / C) ((c1N : Rat) / C) ((c3N : Rat) / C) ((c5N : Rat) / C) x := by
  unfold checkBernsteinSegInt at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨hlt, hb0⟩, hb1⟩, hb2⟩, hb3⟩, hb4⟩, hb5⟩
  have hC_ne : (C : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hC)
  have hD_ne : (D : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hD)
  have hCD_c0 : (C : Rat) * ((c0N : Rat) / (C : Rat)) = (c0N : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hC_ne]
  have hCD_c1 : (C : Rat) * ((c1N : Rat) / (C : Rat)) = (c1N : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hC_ne]
  have hCD_c3 : (C : Rat) * ((c3N : Rat) / (C : Rat)) = (c3N : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hC_ne]
  have hCD_c5 : (C : Rat) * ((c5N : Rat) / (C : Rat)) = (c5N : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hC_ne]
  have hD_lo : (D : Rat) * ((loN : Rat) / (D : Rat)) = (loN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hD_ne]
  have hD_hi : (D : Rat) * ((hiN : Rat) / (D : Rat)) = (hiN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hD_ne]
  apply bernsteinOdd5_nonneg_on _ _ _ _ ((loN : Rat) / D) ((hiN : Rat) / D)
    (rat_div_lt_div_of_pos hlt hD) _ hlo hhi
  unfold bernsteinOdd5
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rat_scaled_nonneg hC hD (by simp only [Rat.intCast_add, Rat.intCast_mul]; grind) hb0
  · exact rat_scaled_nonneg hC hD (by simp only [Rat.intCast_add, Rat.intCast_mul]; grind) hb1
  · exact rat_scaled_nonneg hC hD (by simp only [Rat.intCast_add, Rat.intCast_mul]; grind) hb2
  · exact rat_scaled_nonneg hC hD (by simp only [Rat.intCast_add, Rat.intCast_mul]; grind) hb3
  · exact rat_scaled_nonneg hC hD (by simp only [Rat.intCast_add, Rat.intCast_mul]; grind) hb4
  · exact rat_scaled_nonneg hC hD (by simp only [Rat.intCast_add, Rat.intCast_mul]; grind) hb5

/-- Soundness of a contiguous breakpoint list `p :: q :: more` ending at `last`. -/
theorem bernsteinPartitionInt_sound (c0N c1N c3N c5N C D : Int)
    (hC : (0 : Int) < C) (hD : (0 : Int) < D) :
    ∀ (more : List Int) (p q last : Int),
      (p :: q :: more).getLast (List.cons_ne_nil p (q :: more)) = last →
      checkBernsteinPartitionInt c0N c1N c3N c5N D (p :: q :: more) = true →
      ∀ {x : Rat}, (p : Rat) / (D : Rat) ≤ x → x ≤ (last : Rat) / (D : Rat) →
        (0 : Rat) ≤ evalOdd5 ((c0N : Rat) / C) ((c1N : Rat) / C) ((c3N : Rat) / C) ((c5N : Rat) / C) x
  | [], p, q, last, hlast, hchk, x, hlo, hhi => by
    simp only [checkBernsteinPartitionInt, Bool.and_eq_true] at hchk
    simp only [List.getLast_cons_cons, List.getLast_singleton] at hlast
    subst hlast
    exact bernsteinSegInt_sound c0N c1N c3N c5N C D p q hC hD hchk.1 hlo hhi
  | r :: more', p, q, last, hlast, hchk, x, hlo, hhi => by
    simp only [checkBernsteinPartitionInt, Bool.and_eq_true] at hchk
    cases Rat.le_total (a := x) (b := (q : Rat) / (D : Rat)) with
    | inl hx_le =>
      exact bernsteinSegInt_sound c0N c1N c3N c5N C D p q hC hD hchk.1 hlo hx_le
    | inr hq_le =>
      have hlast' : (q :: r :: more').getLast (List.cons_ne_nil q (r :: more')) = last := by
        simpa using hlast
      have hchk' : checkBernsteinPartitionInt c0N c1N c3N c5N D (q :: r :: more') = true := by
        simp only [checkBernsteinPartitionInt, Bool.and_eq_true]
        exact hchk.2
      exact bernsteinPartitionInt_sound c0N c1N c3N c5N C D hC hD more' q r last hlast' hchk' hq_le hhi

/-! ### Step-Envelope Bridge Lemmas -/

/-- Exact degree-5 polynomial expansion for `hi_out - shiftedUpperMinus α β μ u x`. -/
theorem shiftedUpperMinus_as_evalOdd5 (α β μ u hi_out x : Rat) :
    let up := 1 + u
    let up2 := up * up
    let up6 := up2 * up2 * up2
    let lo := 1 - u
    hi_out - shiftedUpperMinus α β μ u x =
      evalOdd5 hi_out
        (-(up2 * (α + up2 * up2 * β * (μ * μ))))
        (2 * up6 * lo * β * μ)
        (-(up6 * (lo * lo) * β))
        x := by
  unfold shiftedUpperMinus evalOdd5; dsimp only; grind

/-- Exact degree-5 polynomial expansion for `hi_out - shiftedUpperPlus α β μ u x`. -/
theorem shiftedUpperPlus_as_evalOdd5 (α β μ u hi_out x : Rat) :
    let up := 1 + u
    let up2 := up * up
    let up6 := up2 * up2 * up2
    hi_out - shiftedUpperPlus α β μ u x =
      evalOdd5 hi_out
        (-(up2 * (α + up2 * up2 * β * (μ * μ))))
        (2 * up6 * up * β * μ)
        (-(up6 * up2 * β))
        x := by
  unfold shiftedUpperPlus evalOdd5; dsimp only; grind

/-- Exact degree-5 polynomial expansion for `shiftedLowerLeft α β μ u x - lo_out`. -/
theorem shiftedLowerLeft_as_evalOdd5 (α β μ u lo_out x : Rat) :
    let lo := 1 - u
    let lo2 := lo * lo
    let lo6 := lo2 * lo2 * lo2
    let up := 1 + u
    shiftedLowerLeft α β μ u x - lo_out =
      evalOdd5 (-lo_out)
        (lo2 * (α + lo2 * lo2 * β * (μ * μ)))
        (-(2 * lo6 * up * β * μ))
        (lo6 * (up * up) * β)
        x := by
  unfold shiftedLowerLeft evalOdd5; dsimp only; grind

/-- Exact degree-5 polynomial expansion for `shiftedLowerRight α β μ u x - lo_out`. -/
theorem shiftedLowerRight_as_evalOdd5 (α β μ u lo_out x : Rat) :
    let lo := 1 - u
    let lo2 := lo * lo
    let lo6 := lo2 * lo2 * lo2
    shiftedLowerRight α β μ u x - lo_out =
      evalOdd5 (-lo_out)
        (lo2 * (α + lo2 * lo2 * β * (μ * μ)))
        (-(2 * lo6 * lo * β * μ))
        (lo6 * lo2 * β)
        x := by
  unfold shiftedLowerRight evalOdd5; dsimp only; grind

/-- Helper: combine upper and lower step bounds into `lo_out ≤ y ∧ y ≤ hi_out`. -/
theorem noisyShiftedStep_step_certified
    (α β μ u lo_in hi_in lo_out hi_out : Rat)
    (hα : (0 : Rat) < α) (hβ : (0 : Rat) < β)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1) (hlo_in : (0 : Rat) ≤ lo_in)
    (h_upM : ∀ x, lo_in ≤ x → x ≤ hi_in → (0 : Rat) ≤ hi_out - shiftedUpperMinus α β μ u x)
    (h_upP : ∀ x, lo_in ≤ x → x ≤ hi_in → (0 : Rat) ≤ hi_out - shiftedUpperPlus α β μ u x)
    (h_lo : ∀ x, lo_in ≤ x → x ≤ hi_in →
      lo_out ≤ shiftedLowerBase α u x ∨
      (x * x * (1 + u) ≤ μ ∧ lo_out ≤ shiftedLowerLeft α β μ u x) ∨
      (μ ≤ x * x * (1 - u) ∧ lo_out ≤ shiftedLowerRight α β μ u x))
    {x y : Rat} (hxlo : lo_in ≤ x) (hxhi : x ≤ hi_in)
    (hstep : NoisyShiftedStep α β μ u x y) :
    lo_out ≤ y ∧ y ≤ hi_out := by
  have hx : (0 : Rat) ≤ x := Rat.le_trans hlo_in hxlo
  have ⟨hup, hbase, hleft, hright⟩ := noisyShiftedStep_envelope α β μ u x y hα hβ hu0 hu1 hx hstep
  constructor
  · rcases h_lo x hxlo hxhi with h1 | ⟨hc, h2⟩ | ⟨hc, h3⟩
    · exact Rat.le_trans h1 hbase
    · exact Rat.le_trans h2 (hleft hc)
    · exact Rat.le_trans h3 (hright hc)
  · have hm : shiftedUpperMinus α β μ u x ≤ hi_out := rat_le_of_sub_nonneg (h_upM x hxlo hxhi)
    have hp : shiftedUpperPlus α β μ u x ≤ hi_out := rat_le_of_sub_nonneg (h_upP x hxlo hxhi)
    have hmax : max (shiftedUpperMinus α β μ u x) (shiftedUpperPlus α β μ u x) ≤ hi_out := by
      cases Rat.le_total (a := shiftedUpperMinus α β μ u x) (b := shiftedUpperPlus α β μ u x) with
      | inl h => rw [rat_max_eq_right h]; exact hp
      | inr h => rw [rat_max_eq_left h]; exact hm
    exact Rat.le_trans hup hmax

/-! ### Pure-`Int` Cleared-Denominator Step Certificate Drivers (Zero `Rat` Normalization!) -/

theorem rat_div_eq_of_cross {a b c d : Int} (hb : (0 : Int) < b) (hd : (0 : Int) < d)
    (h : a * d = c * b) : (a : Rat) / (b : Rat) = (c : Rat) / (d : Rat) := by
  have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hb)
  have hd_ne : (d : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hd)
  have h1 : (b : Rat) * (d : Rat) * ((a : Rat) / (b : Rat)) = ((a * d : Int) : Rat) := by
    have hba : (b : Rat) * ((a : Rat) / (b : Rat)) = (a : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
    rw [Rat.intCast_mul]; grind
  have h2 : (b : Rat) * (d : Rat) * ((c : Rat) / (d : Rat)) = ((c * b : Int) : Rat) := by
    have hdc : (d : Rat) * ((c : Rat) / (d : Rat)) = (c : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hd_ne]
    rw [Rat.intCast_mul]; grind
  have hbd_ne : (b : Rat) * (d : Rat) ≠ 0 := by
    intro h0; cases Rat.mul_eq_zero.mp h0 with | inl h => exact hb_ne h | inr h => exact hd_ne h
  have h3 : (b : Rat) * (d : Rat) * ((a : Rat) / (b : Rat) - (c : Rat) / (d : Rat)) = 0 := by
    have : ((a * d : Int) : Rat) = ((c * b : Int) : Rat) := congrArg (fun z : Int => (z : Rat)) h
    grind
  cases Rat.mul_eq_zero.mp h3 with
  | inl h0 => exact False.elim (hbd_ne h0)
  | inr h0 => grind

private theorem rat_div_le_of_cross {a b c d : Int} (hb : (0 : Int) < b) (hd : (0 : Int) < d)
    (h : a * d ≤ c * b) : (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := by
  have hb_pos : (0 : Rat) < (b : Rat) := rat_ofInt_pos hb
  have hd_pos : (0 : Rat) < (d : Rat) := rat_ofInt_pos hd
  have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt hb_pos
  have hd_ne : (d : Rat) ≠ 0 := Rat.ne_of_gt hd_pos
  have hbd_pos : (0 : Rat) < (b : Rat) * (d : Rat) := rat_mul_pos hb_pos hd_pos
  apply rat_le_of_sub_nonneg
  apply rat_nonneg_of_mul_pos_nonneg hbd_pos
  have h1 : (b : Rat) * (d : Rat) * ((c : Rat) / (d : Rat) - (a : Rat) / (b : Rat)) =
      ((c * b - a * d : Int) : Rat) := by
    have hba : (b : Rat) * ((a : Rat) / (b : Rat)) = (a : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hb_ne]
    have hdc : (d : Rat) * ((c : Rat) / (d : Rat)) = (c : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hd_ne]
    rw [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_mul]
    grind
  rw [h1]
  exact rat_ofInt_nonneg (by omega)

private theorem rat_c1_eq_div (αN αD βN βD μN μD uS uD : Rat)
    (hαD : αD ≠ 0) (hβD : βD ≠ 0) (hμD : μD ≠ 0) (huD : uD ≠ 0) :
    (uS / uD) * (uS / uD) *
      (αN / αD + (uS / uD) * (uS / uD) * ((uS / uD) * (uS / uD)) * (βN / βD) * ((μN / μD) * (μN / μD))) =
    (uS * uS * (αN * βD * μD * μD * (uD * uD * uD * uD) + (uS * uS) * (uS * uS) * βN * μN * μN * αD)) /
      (αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD) := by
  have ha : αD * (αN / αD) = αN := by rw [Rat.mul_comm, Rat.div_mul_cancel hαD]
  have hb : βD * (βN / βD) = βN := by rw [Rat.mul_comm, Rat.div_mul_cancel hβD]
  have hm : μD * (μN / μD) = μN := by rw [Rat.mul_comm, Rat.div_mul_cancel hμD]
  have hu : uD * (uS / uD) = uS := by rw [Rat.mul_comm, Rat.div_mul_cancel huD]
  have hden_ne : αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD ≠ 0 := by
    intro h0; grind
  have hd : (αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD) *
      ((uS * uS * (αN * βD * μD * μD * (uD * uD * uD * uD) + (uS * uS) * (uS * uS) * βN * μN * μN * αD)) /
       (αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD)) =
      uS * uS * (αN * βD * μD * μD * (uD * uD * uD * uD) + (uS * uS) * (uS * uS) * βN * μN * μN * αD) := by
    rw [Rat.mul_comm, Rat.div_mul_cancel hden_ne]
  have hmul : (αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD) *
      ((uS / uD) * (uS / uD) *
        (αN / αD + (uS / uD) * (uS / uD) * ((uS / uD) * (uS / uD)) * (βN / βD) * ((μN / μD) * (μN / μD))) -
       (uS * uS * (αN * βD * μD * μD * (uD * uD * uD * uD) + (uS * uS) * (uS * uS) * βN * μN * μN * αD)) /
         (αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD)) = 0 := by
    grind
  cases Rat.mul_eq_zero.mp hmul with | inl h => exact False.elim (hden_ne h) | inr h => grind

private theorem rat_c3_eq_div (βN βD μN μD uS uT uD : Rat)
    (hβD : βD ≠ 0) (hμD : μD ≠ 0) (huD : uD ≠ 0) :
    2 * ((uS / uD) * (uS / uD) * ((uS / uD) * (uS / uD)) * ((uS / uD) * (uS / uD))) *
      (uT / uD) * (βN / βD) * (μN / μD) =
    (2 * ((uS * uS) * (uS * uS) * (uS * uS)) * uT * βN * μN) /
      (βD * μD * (uD * uD * uD * uD * uD * uD * uD)) := by
  have hb : βD * (βN / βD) = βN := by rw [Rat.mul_comm, Rat.div_mul_cancel hβD]
  have hm : μD * (μN / μD) = μN := by rw [Rat.mul_comm, Rat.div_mul_cancel hμD]
  have hus : uD * (uS / uD) = uS := by rw [Rat.mul_comm, Rat.div_mul_cancel huD]
  have hut : uD * (uT / uD) = uT := by rw [Rat.mul_comm, Rat.div_mul_cancel huD]
  have hden_ne : βD * μD * (uD * uD * uD * uD * uD * uD * uD) ≠ 0 := by
    intro h0; grind
  have hd : (βD * μD * (uD * uD * uD * uD * uD * uD * uD)) *
      ((2 * ((uS * uS) * (uS * uS) * (uS * uS)) * uT * βN * μN) /
       (βD * μD * (uD * uD * uD * uD * uD * uD * uD))) =
      2 * ((uS * uS) * (uS * uS) * (uS * uS)) * uT * βN * μN := by
    rw [Rat.mul_comm, Rat.div_mul_cancel hden_ne]
  have hmul : (βD * μD * (uD * uD * uD * uD * uD * uD * uD)) *
      (2 * ((uS / uD) * (uS / uD) * ((uS / uD) * (uS / uD)) * ((uS / uD) * (uS / uD))) *
        (uT / uD) * (βN / βD) * (μN / μD) -
       (2 * ((uS * uS) * (uS * uS) * (uS * uS)) * uT * βN * μN) /
         (βD * μD * (uD * uD * uD * uD * uD * uD * uD))) = 0 := by
    grind
  cases Rat.mul_eq_zero.mp hmul with | inl h => exact False.elim (hden_ne h) | inr h => grind

private theorem rat_c5_eq_div (βN βD uS uT uD : Rat)
    (hβD : βD ≠ 0) (huD : uD ≠ 0) :
    (uS / uD) * (uS / uD) * ((uS / uD) * (uS / uD)) * ((uS / uD) * (uS / uD)) *
      ((uT / uD) * (uT / uD)) * (βN / βD) =
    (((uS * uS) * (uS * uS) * (uS * uS)) * uT * uT * βN) /
      (βD * (uD * uD * uD * uD * uD * uD * uD * uD)) := by
  have hb : βD * (βN / βD) = βN := by rw [Rat.mul_comm, Rat.div_mul_cancel hβD]
  have hus : uD * (uS / uD) = uS := by rw [Rat.mul_comm, Rat.div_mul_cancel huD]
  have hut : uD * (uT / uD) = uT := by rw [Rat.mul_comm, Rat.div_mul_cancel huD]
  have hden_ne : βD * (uD * uD * uD * uD * uD * uD * uD * uD) ≠ 0 := by
    intro h0; grind
  have hd : (βD * (uD * uD * uD * uD * uD * uD * uD * uD)) *
      ((((uS * uS) * (uS * uS) * (uS * uS)) * uT * uT * βN) /
       (βD * (uD * uD * uD * uD * uD * uD * uD * uD))) =
      ((uS * uS) * (uS * uS) * (uS * uS)) * uT * uT * βN := by
    rw [Rat.mul_comm, Rat.div_mul_cancel hden_ne]
  have hmul : (βD * (uD * uD * uD * uD * uD * uD * uD * uD)) *
      ((uS / uD) * (uS / uD) * ((uS / uD) * (uS / uD)) * ((uS / uD) * (uS / uD)) *
        ((uT / uD) * (uT / uD)) * (βN / βD) -
       (((uS * uS) * (uS * uS) * (uS * uS)) * uT * uT * βN) /
         (βD * (uD * uD * uD * uD * uD * uD * uD * uD))) = 0 := by
    grind
  cases Rat.mul_eq_zero.mp hmul with | inl h => exact False.elim (hden_ne h) | inr h => grind

private theorem rat_neg_div_eq (a b : Rat) (hb : b ≠ 0) : -(a / b) = (-a) / b := by
  have h1 : b * (a / b) = a := by rw [Rat.mul_comm, Rat.div_mul_cancel hb]
  have h2 : b * ((-a) / b) = -a := by rw [Rat.mul_comm, Rat.div_mul_cancel hb]
  have h3 : b * (-(a / b) - (-a) / b) = 0 := by grind
  cases Rat.mul_eq_zero.mp h3 with | inl h => exact False.elim (hb h) | inr h => grind

/-- Pure-`Int` certificate for `0 ≤ hi_out - shiftedUpperMinus α β μ u x` on `[loN/D, hiN/D]`. -/
theorem upperMinus_cert_int
    (αN αD βN βD μN μD uN uD outN outD C D : Int)
    (hαD : (0 : Int) < αD) (hβD : (0 : Int) < βD) (hμD : (0 : Int) < μD)
    (huD : (0 : Int) < uD) (houtD : (0 : Int) < outD) (hC : (0 : Int) < C) (hD : (0 : Int) < D)
    (c0N c1N c3N c5N : Int)
    (hc0 : c0N * outD = outN * C)
    (hc1 : let up := uD + uN; let up2 := up * up; let up4 := up2 * up2; let uD4 := uD * uD * uD * uD
           let den1 := αD * βD * μD * μD * uD4 * uD * uD
           c1N * den1 = (-(up2 * (αN * βD * μD * μD * uD4 + up4 * βN * μN * μN * αD))) * C)
    (hc3 : let up := uD + uN; let up2 := up * up; let up6 := up2 * up2 * up2; let lo := uD - uN
           let den3 := βD * μD * (uD * uD * uD * uD * uD * uD * uD)
           c3N * den3 = (2 * up6 * lo * βN * μN) * C)
    (hc5 : let up := uD + uN; let up2 := up * up; let up6 := up2 * up2 * up2; let lo := uD - uN
           let den5 := βD * (uD * uD * uD * uD * uD * uD * uD * uD)
           c5N * den5 = (-(up6 * lo * lo * βN)) * C)
    (p q last : Int) (more : List Int)
    (hlast : (p :: q :: more).getLast (List.cons_ne_nil p (q :: more)) = last)
    (hchk : checkBernsteinPartitionInt c0N c1N c3N c5N D (p :: q :: more) = true)
    {x : Rat} (hxlo : (p : Rat) / (D : Rat) ≤ x) (hxhi : x ≤ (last : Rat) / (D : Rat)) :
    (0 : Rat) ≤ (outN : Rat) / outD - shiftedUpperMinus ((αN : Rat) / αD) ((βN : Rat) / βD) ((μN : Rat) / μD) ((uN : Rat) / uD) x := by
  rw [shiftedUpperMinus_as_evalOdd5]
  have h0 : (outN : Rat) / outD = (c0N : Rat) / C := (rat_div_eq_of_cross hC houtD hc0).symm
  have huD_ne : (uD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos huD)
  have hαD_ne : (αD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hαD)
  have hβD_ne : (βD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hβD)
  have hμD_ne : (μD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hμD)
  have hup : (1 : Rat) + (uN : Rat) / uD = ((uD + uN : Int) : Rat) / uD := by
    rw [Rat.intCast_add]
    have h1 : (uD : Rat) * ((1 : Rat) + (uN : Rat) / uD - ((uD : Rat) + (uN : Rat)) / uD) = 0 := by
      have ha : (uD : Rat) * ((uN : Rat) / uD) = (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hb : (uD : Rat) * (((uD : Rat) + (uN : Rat)) / uD) = (uD : Rat) + (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      grind
    cases Rat.mul_eq_zero.mp h1 with | inl h => exact False.elim (huD_ne h) | inr h => grind
  have hlo : (1 : Rat) - (uN : Rat) / uD = ((uD - uN : Int) : Rat) / uD := by
    rw [Rat.intCast_sub]
    have h1 : (uD : Rat) * ((1 : Rat) - (uN : Rat) / uD - ((uD : Rat) - (uN : Rat)) / uD) = 0 := by
      have ha : (uD : Rat) * ((uN : Rat) / uD) = (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hb : (uD : Rat) * (((uD : Rat) - (uN : Rat)) / uD) = (uD : Rat) - (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      grind
    cases Rat.mul_eq_zero.mp h1 with | inl h => exact False.elim (huD_ne h) | inr h => grind
  have hden1 : (0 : Int) < αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD :=
    Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos hαD hβD) hμD) hμD)
      (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD)) huD) huD
  have hden3 : (0 : Int) < βD * μD * (uD * uD * uD * uD * uD * uD * uD) :=
    Int.mul_pos (Int.mul_pos hβD hμD)
      (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD) huD) huD) huD)
  have hden5 : (0 : Int) < βD * (uD * uD * uD * uD * uD * uD * uD * uD) :=
    Int.mul_pos hβD
      (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD) huD) huD) huD) huD)
  have h1 : -(((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
      ((αN : Rat) / αD + ((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
        (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
        ((βN : Rat) / βD) * (((μN : Rat) / μD) * ((μN : Rat) / μD)))) = (c1N : Rat) / C := by
    rw [hup, rat_c1_eq_div _ _ _ _ _ _ _ _ hαD_ne hβD_ne hμD_ne huD_ne]
    rw [rat_neg_div_eq _ _ (by
      have := Rat.ne_of_gt (rat_ofInt_pos hden1); simp only [Rat.intCast_mul] at this; exact this)]
    have hrat := (rat_div_eq_of_cross hC hden1 hc1).symm
    simp only [Rat.intCast_neg, Rat.intCast_add, Rat.intCast_mul] at hrat ⊢
    exact hrat
  have h3 : 2 * (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD))) *
      ((1 : Rat) - (uN : Rat) / uD) * ((βN : Rat) / βD) * ((μN : Rat) / μD) = (c3N : Rat) / C := by
    rw [hup, hlo, rat_c3_eq_div _ _ _ _ _ _ _ hβD_ne hμD_ne huD_ne]
    have hrat := (rat_div_eq_of_cross hC hden3 hc3).symm
    simp only [Rat.intCast_mul] at hrat ⊢
    exact hrat
  have h5 : -(((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      (((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD)) *
      ((βN : Rat) / βD)) = (c5N : Rat) / C := by
    rw [hup, hlo, rat_c5_eq_div _ _ _ _ _ hβD_ne huD_ne]
    rw [rat_neg_div_eq _ _ (by
      have := Rat.ne_of_gt (rat_ofInt_pos hden5); simp only [Rat.intCast_mul] at this; exact this)]
    have hrat := (rat_div_eq_of_cross hC hden5 hc5).symm
    simp only [Rat.intCast_neg, Rat.intCast_mul] at hrat ⊢
    exact hrat
  rw [h0, h1, h3, h5]
  exact bernsteinPartitionInt_sound c0N c1N c3N c5N C D hC hD more p q last hlast hchk hxlo hxhi

/-- Pure-`Int` certificate for `0 ≤ hi_out - shiftedUpperPlus α β μ u x` on `[loN/D, hiN/D]`. -/
theorem upperPlus_cert_int
    (αN αD βN βD μN μD uN uD outN outD C D : Int)
    (hαD : (0 : Int) < αD) (hβD : (0 : Int) < βD) (hμD : (0 : Int) < μD)
    (huD : (0 : Int) < uD) (houtD : (0 : Int) < outD) (hC : (0 : Int) < C) (hD : (0 : Int) < D)
    (c0N c1N c3N c5N : Int)
    (hc0 : c0N * outD = outN * C)
    (hc1 : let up := uD + uN; let up2 := up * up; let up4 := up2 * up2; let uD4 := uD * uD * uD * uD
           let den1 := αD * βD * μD * μD * uD4 * uD * uD
           c1N * den1 = (-(up2 * (αN * βD * μD * μD * uD4 + up4 * βN * μN * μN * αD))) * C)
    (hc3 : let up := uD + uN; let up2 := up * up; let up6 := up2 * up2 * up2
           let den3 := βD * μD * (uD * uD * uD * uD * uD * uD * uD)
           c3N * den3 = (2 * up6 * up * βN * μN) * C)
    (hc5 : let up := uD + uN; let up2 := up * up; let up6 := up2 * up2 * up2
           let den5 := βD * (uD * uD * uD * uD * uD * uD * uD * uD)
           c5N * den5 = (-(up6 * up * up * βN)) * C)
    (p q last : Int) (more : List Int)
    (hlast : (p :: q :: more).getLast (List.cons_ne_nil p (q :: more)) = last)
    (hchk : checkBernsteinPartitionInt c0N c1N c3N c5N D (p :: q :: more) = true)
    {x : Rat} (hxlo : (p : Rat) / (D : Rat) ≤ x) (hxhi : x ≤ (last : Rat) / (D : Rat)) :
    (0 : Rat) ≤ (outN : Rat) / outD - shiftedUpperPlus ((αN : Rat) / αD) ((βN : Rat) / βD) ((μN : Rat) / μD) ((uN : Rat) / uD) x := by
  rw [shiftedUpperPlus_as_evalOdd5]
  have h0 : (outN : Rat) / outD = (c0N : Rat) / C := (rat_div_eq_of_cross hC houtD hc0).symm
  have huD_ne : (uD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos huD)
  have hαD_ne : (αD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hαD)
  have hβD_ne : (βD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hβD)
  have hμD_ne : (μD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hμD)
  have hup : (1 : Rat) + (uN : Rat) / uD = ((uD + uN : Int) : Rat) / uD := by
    rw [Rat.intCast_add]
    have h1 : (uD : Rat) * ((1 : Rat) + (uN : Rat) / uD - ((uD : Rat) + (uN : Rat)) / uD) = 0 := by
      have ha : (uD : Rat) * ((uN : Rat) / uD) = (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hb : (uD : Rat) * (((uD : Rat) + (uN : Rat)) / uD) = (uD : Rat) + (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      grind
    cases Rat.mul_eq_zero.mp h1 with | inl h => exact False.elim (huD_ne h) | inr h => grind
  have hden1 : (0 : Int) < αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD :=
    Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos hαD hβD) hμD) hμD)
      (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD)) huD) huD
  have hden3 : (0 : Int) < βD * μD * (uD * uD * uD * uD * uD * uD * uD) :=
    Int.mul_pos (Int.mul_pos hβD hμD)
      (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD) huD) huD) huD)
  have hden5 : (0 : Int) < βD * (uD * uD * uD * uD * uD * uD * uD * uD) :=
    Int.mul_pos hβD
      (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD) huD) huD) huD) huD)
  have h1 : -(((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
      ((αN : Rat) / αD + ((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
        (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
        ((βN : Rat) / βD) * (((μN : Rat) / μD) * ((μN : Rat) / μD)))) = (c1N : Rat) / C := by
    rw [hup, rat_c1_eq_div _ _ _ _ _ _ _ _ hαD_ne hβD_ne hμD_ne huD_ne]
    rw [rat_neg_div_eq _ _ (by
      have := Rat.ne_of_gt (rat_ofInt_pos hden1); simp only [Rat.intCast_mul] at this; exact this)]
    have hrat := (rat_div_eq_of_cross hC hden1 hc1).symm
    simp only [Rat.intCast_neg, Rat.intCast_add, Rat.intCast_mul] at hrat ⊢
    exact hrat
  have h3 : 2 * (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD))) *
      ((1 : Rat) + (uN : Rat) / uD) * ((βN : Rat) / βD) * ((μN : Rat) / μD) = (c3N : Rat) / C := by
    rw [hup, rat_c3_eq_div _ _ _ _ _ _ _ hβD_ne hμD_ne huD_ne]
    have hrat := (rat_div_eq_of_cross hC hden3 hc3).symm
    simp only [Rat.intCast_mul] at hrat ⊢
    exact hrat
  have h5 : -(((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      ((βN : Rat) / βD)) = (c5N : Rat) / C := by
    rw [hup, rat_c5_eq_div _ _ _ _ _ hβD_ne huD_ne]
    rw [rat_neg_div_eq _ _ (by
      have := Rat.ne_of_gt (rat_ofInt_pos hden5); simp only [Rat.intCast_mul] at this; exact this)]
    have hrat := (rat_div_eq_of_cross hC hden5 hc5).symm
    simp only [Rat.intCast_neg, Rat.intCast_mul] at hrat ⊢
    exact hrat
  rw [h0, h1, h3, h5]
  exact bernsteinPartitionInt_sound c0N c1N c3N c5N C D hC hD more p q last hlast hchk hxlo hxhi

/-- Pure-`Int` certificate for `lo_out ≤ shiftedLowerLeft α β μ u x` on `[loN/D, hiN/D]`. -/
theorem lowerLeft_cert_int
    (αN αD βN βD μN μD uN uD lN lD C D : Int)
    (hαD : (0 : Int) < αD) (hβD : (0 : Int) < βD) (hμD : (0 : Int) < μD)
    (huD : (0 : Int) < uD) (hlD : (0 : Int) < lD) (hC : (0 : Int) < C) (hD : (0 : Int) < D)
    (c0N c1N c3N c5N : Int)
    (hc0 : c0N * lD = (-lN) * C)
    (hc1 : let lo := uD - uN; let lo2 := lo * lo; let lo4 := lo2 * lo2; let uD4 := uD * uD * uD * uD
           let den1 := αD * βD * μD * μD * uD4 * uD * uD
           c1N * den1 = (lo2 * (αN * βD * μD * μD * uD4 + lo4 * βN * μN * μN * αD)) * C)
    (hc3 : let lo := uD - uN; let lo2 := lo * lo; let lo6 := lo2 * lo2 * lo2; let up := uD + uN
           let den3 := βD * μD * (uD * uD * uD * uD * uD * uD * uD)
           c3N * den3 = (-(2 * lo6 * up * βN * μN)) * C)
    (hc5 : let lo := uD - uN; let lo2 := lo * lo; let lo6 := lo2 * lo2 * lo2; let up := uD + uN
           let den5 := βD * (uD * uD * uD * uD * uD * uD * uD * uD)
           c5N * den5 = (lo6 * up * up * βN) * C)
    (p q last : Int) (more : List Int)
    (hlast : (p :: q :: more).getLast (List.cons_ne_nil p (q :: more)) = last)
    (hchk : checkBernsteinPartitionInt c0N c1N c3N c5N D (p :: q :: more) = true)
    {x : Rat} (hxlo : (p : Rat) / (D : Rat) ≤ x) (hxhi : x ≤ (last : Rat) / (D : Rat)) :
    (lN : Rat) / lD ≤ shiftedLowerLeft ((αN : Rat) / αD) ((βN : Rat) / βD) ((μN : Rat) / μD) ((uN : Rat) / uD) x := by
  apply rat_le_of_sub_nonneg
  rw [shiftedLowerLeft_as_evalOdd5]
  have h0 : -((lN : Rat) / lD) = (c0N : Rat) / C := by
    rw [rat_neg_div_eq _ _ (Rat.ne_of_gt (rat_ofInt_pos hlD))]
    have h1 := (rat_div_eq_of_cross hC hlD hc0).symm
    rw [Rat.intCast_neg] at h1
    exact h1
  have huD_ne : (uD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos huD)
  have hαD_ne : (αD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hαD)
  have hβD_ne : (βD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hβD)
  have hμD_ne : (μD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hμD)
  have hup : (1 : Rat) + (uN : Rat) / uD = ((uD + uN : Int) : Rat) / uD := by
    rw [Rat.intCast_add]
    have h1 : (uD : Rat) * ((1 : Rat) + (uN : Rat) / uD - ((uD : Rat) + (uN : Rat)) / uD) = 0 := by
      have ha : (uD : Rat) * ((uN : Rat) / uD) = (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hb : (uD : Rat) * (((uD : Rat) + (uN : Rat)) / uD) = (uD : Rat) + (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      grind
    cases Rat.mul_eq_zero.mp h1 with | inl h => exact False.elim (huD_ne h) | inr h => grind
  have hlo : (1 : Rat) - (uN : Rat) / uD = ((uD - uN : Int) : Rat) / uD := by
    rw [Rat.intCast_sub]
    have h1 : (uD : Rat) * ((1 : Rat) - (uN : Rat) / uD - ((uD : Rat) - (uN : Rat)) / uD) = 0 := by
      have ha : (uD : Rat) * ((uN : Rat) / uD) = (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hb : (uD : Rat) * (((uD : Rat) - (uN : Rat)) / uD) = (uD : Rat) - (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      grind
    cases Rat.mul_eq_zero.mp h1 with | inl h => exact False.elim (huD_ne h) | inr h => grind
  have hden1 : (0 : Int) < αD * βD * μD * μD * (uD * uD * uD * uD) * uD * uD :=
    Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos hαD hβD) hμD) hμD)
      (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD)) huD) huD
  have hden3 : (0 : Int) < βD * μD * (uD * uD * uD * uD * uD * uD * uD) :=
    Int.mul_pos (Int.mul_pos hβD hμD)
      (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD) huD) huD) huD)
  have hden5 : (0 : Int) < βD * (uD * uD * uD * uD * uD * uD * uD * uD) :=
    Int.mul_pos hβD
      (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) huD) huD) huD) huD) huD) huD)
  have h1 : ((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD) *
      ((αN : Rat) / αD + ((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD) *
        (((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD)) *
        ((βN : Rat) / βD) * (((μN : Rat) / μD) * ((μN : Rat) / μD))) = (c1N : Rat) / C := by
    rw [hlo, rat_c1_eq_div _ _ _ _ _ _ _ _ hαD_ne hβD_ne hμD_ne huD_ne]
    have hrat := (rat_div_eq_of_cross hC hden1 hc1).symm
    simp only [Rat.intCast_add, Rat.intCast_mul] at hrat ⊢
    exact hrat
  have h3 : -(2 * (((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD) *
      (((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD)) *
      (((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD))) *
      ((1 : Rat) + (uN : Rat) / uD) * ((βN : Rat) / βD) * ((μN : Rat) / μD)) = (c3N : Rat) / C := by
    rw [hup, hlo, rat_c3_eq_div _ _ _ _ _ _ _ hβD_ne hμD_ne huD_ne]
    rw [rat_neg_div_eq _ _ (by
      have := Rat.ne_of_gt (rat_ofInt_pos hden3); simp only [Rat.intCast_mul] at this; exact this)]
    have hrat := (rat_div_eq_of_cross hC hden3 hc3).symm
    simp only [Rat.intCast_neg, Rat.intCast_mul] at hrat ⊢
    exact hrat
  have h5 : ((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD) *
      (((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD)) *
      (((1 : Rat) - (uN : Rat) / uD) * ((1 : Rat) - (uN : Rat) / uD)) *
      (((1 : Rat) + (uN : Rat) / uD) * ((1 : Rat) + (uN : Rat) / uD)) *
      ((βN : Rat) / βD) = (c5N : Rat) / C := by
    rw [hup, hlo, rat_c5_eq_div _ _ _ _ _ hβD_ne huD_ne]
    have hrat := (rat_div_eq_of_cross hC hden5 hc5).symm
    simp only [Rat.intCast_mul] at hrat ⊢
    exact hrat
  rw [h0, h1, h3, h5]
  exact bernsteinPartitionInt_sound c0N c1N c3N c5N C D hC hD more p q last hlast hchk hxlo hxhi

/-- Pure-`Int` check that `x^2 * (1 + u) ≤ μ` whenever `0 ≤ x ≤ qN / qD` and
`qN^2 * (uD + uN) * μD ≤ μN * qD^2 * uD`. -/
theorem sq_mul_up_le_mu_of_int {qN qD uN uD μN μD : Int}
    (hqD : (0 : Int) < qD) (huD : (0 : Int) < uD) (hμD : (0 : Int) < μD)
    (hu_nn : (0 : Int) ≤ uD + uN)
    (hcheck : qN * qN * (uD + uN) * μD ≤ μN * (qD * qD) * uD)
    {x : Rat} (hx0 : (0 : Rat) ≤ x) (hxq : x ≤ (qN : Rat) / qD) :
    x * x * (1 + (uN : Rat) / uD) ≤ (μN : Rat) / μD := by
  have huD_ne : (uD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos huD)
  have hup : (1 : Rat) + (uN : Rat) / uD = ((uD + uN : Int) : Rat) / uD := by
    rw [Rat.intCast_add]
    have h1 : (uD : Rat) * ((1 : Rat) + (uN : Rat) / uD - ((uD : Rat) + (uN : Rat)) / uD) = 0 := by
      have ha : (uD : Rat) * ((uN : Rat) / uD) = (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hb : (uD : Rat) * (((uD : Rat) + (uN : Rat)) / uD) = (uD : Rat) + (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      grind
    cases Rat.mul_eq_zero.mp h1 with | inl h => exact False.elim (huD_ne h) | inr h => grind
  rw [hup]
  have hup_nn : (0 : Rat) ≤ ((uD + uN : Int) : Rat) / uD := rat_ofInt_div_nonneg hu_nn huD
  have hsq : x * x ≤ ((qN : Rat) / qD) * ((qN : Rat) / qD) := rat_sq_le_sq_of_nonneg hx0 hxq
  have h1 : x * x * (((uD + uN : Int) : Rat) / uD) ≤
      (((qN : Rat) / qD) * ((qN : Rat) / qD)) * (((uD + uN : Int) : Rat) / uD) :=
    rat_mul_le_mul_of_nonneg_right hsq hup_nn
  have hden : (0 : Int) < (qD * qD) * uD := Int.mul_pos (Int.mul_pos hqD hqD) huD
  have h2 : (((qN : Rat) / qD) * ((qN : Rat) / qD)) * (((uD + uN : Int) : Rat) / uD) =
      ((qN * qN * (uD + uN) : Int) : Rat) / ((qD * qD * uD : Int) : Rat) := by
    have hqD_ne : (qD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hqD)
    have hden_ne : ((qD * qD * uD : Int) : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hden)
    have hmul : ((qD * qD * uD : Int) : Rat) *
        ((((qN : Rat) / qD) * ((qN : Rat) / qD)) * (((uD + uN : Int) : Rat) / uD) -
         ((qN * qN * (uD + uN) : Int) : Rat) / ((qD * qD * uD : Int) : Rat)) = 0 := by
      have hq : (qD : Rat) * ((qN : Rat) / qD) = (qN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hqD_ne]
      have hu : (uD : Rat) * (((uD + uN : Int) : Rat) / uD) = ((uD + uN : Int) : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hd : ((qD * qD * uD : Int) : Rat) * (((qN * qN * (uD + uN) : Int) : Rat) / ((qD * qD * uD : Int) : Rat)) =
          ((qN * qN * (uD + uN) : Int) : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hden_ne]
      have hcast1 : ((qN * qN * (uD + uN) : Int) : Rat) = (qN : Rat) * (qN : Rat) * ((uD + uN : Int) : Rat) := by
        simp only [Rat.intCast_mul]
      have hcast2 : ((qD * qD * uD : Int) : Rat) = (qD : Rat) * (qD : Rat) * (uD : Rat) := by
        simp only [Rat.intCast_mul]
      grind
    cases Rat.mul_eq_zero.mp hmul with | inl h => exact False.elim (hden_ne h) | inr h => grind
  rw [h2] at h1
  have hcheck' : qN * qN * (uD + uN) * μD ≤ μN * (qD * qD * uD) := by
    have : μN * (qD * qD * uD) = μN * (qD * qD) * uD := by grind
    rw [this]; exact hcheck
  exact Rat.le_trans h1 (rat_div_le_of_cross hden hμD hcheck')

/-- Pure-`Int` check that `lo_out ≤ shiftedLowerBase α u x` whenever `qN / qD ≤ x` and
`lN * (uD^2 * αD * qD) ≤ (uD - uN)^2 * αN * qN * lD`. -/
theorem lowerBase_ge_of_int {lN lD αN αD uN uD qN qD : Int}
    (hlD : (0 : Int) < lD) (hαD : (0 : Int) < αD) (huD : (0 : Int) < uD) (hqD : (0 : Int) < qD)
    (hα_nn : (0 : Int) ≤ αN) (hu_nn : (0 : Int) ≤ uD - uN)
    (hcheck : lN * (uD * uD * αD * qD) ≤ (uD - uN) * (uD - uN) * αN * qN * lD)
    {x : Rat} (hx : (qN : Rat) / qD ≤ x) :
    (lN : Rat) / lD ≤ shiftedLowerBase ((αN : Rat) / αD) ((uN : Rat) / uD) x := by
  unfold shiftedLowerBase
  have huD_ne : (uD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos huD)
  have hlo : (1 : Rat) - (uN : Rat) / uD = ((uD - uN : Int) : Rat) / uD := by
    rw [Rat.intCast_sub]
    have h1 : (uD : Rat) * ((1 : Rat) - (uN : Rat) / uD - ((uD : Rat) - (uN : Rat)) / uD) = 0 := by
      have ha : (uD : Rat) * ((uN : Rat) / uD) = (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hb : (uD : Rat) * (((uD : Rat) - (uN : Rat)) / uD) = (uD : Rat) - (uN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      grind
    cases Rat.mul_eq_zero.mp h1 with | inl h => exact False.elim (huD_ne h) | inr h => grind
  rw [hlo]
  have hcoeff_nn : (0 : Rat) ≤ (((uD - uN : Int) : Rat) / uD) * (((uD - uN : Int) : Rat) / uD) * ((αN : Rat) / αD) :=
    Rat.mul_nonneg (Rat.mul_nonneg (rat_ofInt_div_nonneg hu_nn huD) (rat_ofInt_div_nonneg hu_nn huD))
      (rat_ofInt_div_nonneg hα_nn hαD)
  have h1 : (((uD - uN : Int) : Rat) / uD) * (((uD - uN : Int) : Rat) / uD) * ((αN : Rat) / αD) * ((qN : Rat) / qD) ≤
      (((uD - uN : Int) : Rat) / uD) * (((uD - uN : Int) : Rat) / uD) * ((αN : Rat) / αD) * x :=
    rat_mul_le_mul_of_nonneg_left hx hcoeff_nn
  have hden : (0 : Int) < uD * uD * αD * qD :=
    Int.mul_pos (Int.mul_pos (Int.mul_pos huD huD) hαD) hqD
  have h2 : (((uD - uN : Int) : Rat) / uD) * (((uD - uN : Int) : Rat) / uD) * ((αN : Rat) / αD) * ((qN : Rat) / qD) =
      (((uD - uN) * (uD - uN) * αN * qN : Int) : Rat) / ((uD * uD * αD * qD : Int) : Rat) := by
    have hαD_ne : (αD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hαD)
    have hqD_ne : (qD : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hqD)
    have hden_ne : ((uD * uD * αD * qD : Int) : Rat) ≠ 0 := Rat.ne_of_gt (rat_ofInt_pos hden)
    have hmul : ((uD * uD * αD * qD : Int) : Rat) *
        ((((uD - uN : Int) : Rat) / uD) * (((uD - uN : Int) : Rat) / uD) * ((αN : Rat) / αD) * ((qN : Rat) / qD) -
         (((uD - uN) * (uD - uN) * αN * qN : Int) : Rat) / ((uD * uD * αD * qD : Int) : Rat)) = 0 := by
      have ha : (αD : Rat) * ((αN : Rat) / αD) = (αN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hαD_ne]
      have hq : (qD : Rat) * ((qN : Rat) / qD) = (qN : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hqD_ne]
      have hu : (uD : Rat) * (((uD - uN : Int) : Rat) / uD) = ((uD - uN : Int) : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel huD_ne]
      have hd : ((uD * uD * αD * qD : Int) : Rat) *
          ((((uD - uN) * (uD - uN) * αN * qN : Int) : Rat) / ((uD * uD * αD * qD : Int) : Rat)) =
          (((uD - uN) * (uD - uN) * αN * qN : Int) : Rat) := by rw [Rat.mul_comm, Rat.div_mul_cancel hden_ne]
      have hcast1 : (((uD - uN) * (uD - uN) * αN * qN : Int) : Rat) =
          ((uD - uN : Int) : Rat) * ((uD - uN : Int) : Rat) * (αN : Rat) * (qN : Rat) := by
        simp only [Rat.intCast_mul]
      have hcast2 : ((uD * uD * αD * qD : Int) : Rat) = (uD : Rat) * (uD : Rat) * (αD : Rat) * (qD : Rat) := by
        simp only [Rat.intCast_mul]
      grind
    cases Rat.mul_eq_zero.mp hmul with | inl h => exact False.elim (hden_ne h) | inr h => grind
  rw [h2] at h1
  exact Rat.le_trans (rat_div_le_of_cross hlD hden hcheck) h1

end MuonVertexPolar
