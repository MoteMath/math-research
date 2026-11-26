/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp6Ef21Rotations.RatOrder

/-!
# Universal All-`B` EF21 Contraction Phase Diagrams & Exact `E2M3` vs `E3M2` Crossover

Pure Lean 4 `Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `mxfp6_e3m2_nvfp6_ef21_universal` (for ALL `B ≥ 1`, upper bound + exact tightness/attainment).
2. `mxfp6_e2m3_nvfp6_ef21_universal` (for ALL `B ≥ 1`, upper bound + exact tightness/attainment).
3. `mxfp6_e2m3_vs_e3m2_exact_crossover` (`B ≤ 43` vs `B ≥ 44` for MXFP6; `B = 1` tie, `2 ≤ B ≤ 178` vs `B ≥ 179` for NVFP6).
-/

namespace Mxfp6Ef21Rotations

/-! ### 1. Integer-Numerator Grid Representation & Generic Lifting -/

/-- Boolean checker on integer numerators: every adjacent pair `(a, b)` satisfies `a < b` and
    either is a unit-step subnormal/low-normal interval (`b - a = 1`, `1 ≤ a + b`) or has
    `b - a ≤ maxGap` and `ratio * (b - a) ≤ a + b`. -/
private def checkGridNums (maxGap ratio : Nat) : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    (decide (a < b)) &&
    (decide (b - a = 1 ∧ 1 ≤ a + b) || decide (b - a ≤ maxGap ∧ ratio * (b - a) ≤ a + b)) &&
    checkGridNums maxGap ratio (b :: rest)

private theorem check_e3m2Nums : checkGridNums 64 9 e3m2Nums = true := by decide
private theorem check_e2m3Nums : checkGridNums 4 17 e2m3Nums = true := by decide

private theorem isSorted_map_div {D : Nat} (hD : 0 < D) (maxGap ratio : Nat) :
    ∀ ns : List Nat, checkGridNums maxGap ratio ns = true →
      isSorted (ns.map (fun (k : Nat) => (k : Rat) / (D : Rat))) := by
  intro ns
  induction ns with
  | nil => intro _; trivial
  | cons a tl ih =>
    cases tl with
    | nil => intro _; trivial
    | cons b rest =>
      intro hchk
      simp only [checkGridNums, Bool.and_eq_true, decide_eq_true_eq] at hchk
      have hab : a < b := hchk.1.1
      have hrest : checkGridNums maxGap ratio (b :: rest) = true := hchk.2
      refine ⟨?_, ih hrest⟩
      have hDpos : (0 : Rat) < (D : Rat) := rat_natCast_pos hD
      apply rat_div_le_div_of_cross hDpos hDpos
      have hle : (a : Rat) ≤ (b : Rat) := rat_natCast_le (Nat.le_of_lt hab)
      exact rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hDpos)

private theorem rat_natCast_sub {a b : Nat} (h : a ≤ b) :
    ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) := by
  have heq : b = (b - a) + a := (Nat.sub_add_cancel h).symm
  have h1 : (b : Rat) = ((b - a : Nat) : Rat) + (a : Rat) := by
    conv => lhs; rw [heq]
    exact Rat.natCast_add (b - a) a
  grind

private theorem rat_2D_inv {D : Nat} (hD : 0 < D) :
    (2 * (D : Rat))⁻¹ = (2 : Rat)⁻¹ * (D : Rat)⁻¹ := by
  have hDpos : (0 : Rat) < (D : Rat) := rat_natCast_pos hD
  have hDne : (D : Rat) ≠ 0 := Rat.ne_of_gt hDpos
  have h2D : (0 : Rat) < 2 * (D : Rat) := rat_mul_pos (by decide) hDpos
  have hmul : ((2 * (D : Rat))⁻¹ - (2 : Rat)⁻¹ * (D : Rat)⁻¹) * (2 * (D : Rat)) = 0 := by
    have h2inv : (2 : Rat)⁻¹ * 2 = 1 := Rat.inv_mul_cancel 2 (by decide)
    have hDinv : (D : Rat)⁻¹ * (D : Rat) = 1 := Rat.inv_mul_cancel _ hDne
    have h2Dinv : (2 * (D : Rat))⁻¹ * (2 * (D : Rat)) = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt h2D)
    grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h0 => grind
  | inr h0 => exact False.elim (Rat.ne_of_gt h2D h0)

/-- Lift `checkGridNums` to `gridQuadBound α C` given a unit-step bound and a ratio-step bound. -/
private theorem gridQuadBound_of_check {D maxGap ratio : Nat}
    {α C : Rat} (hδ : (0 : Rat) ≤ 1 - α) (hC : (0 : Rat) ≤ C)
    (hUnit : ∀ a b : Nat, a < b → b - a = 1 → 1 ≤ a + b →
      (((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
      (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2)) ≤ C)
    (hRatio : ∀ a b : Nat, a < b → b - a ≤ maxGap → ratio * (b - a) ≤ a + b →
      (((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
      (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2)) ≤ C) :
    ∀ ns : List Nat, checkGridNums maxGap ratio ns = true →
      gridQuadBound α C (ns.map (fun (k : Nat) => (k : Rat) / (D : Rat))) := by
  intro ns
  induction ns with
  | nil => intro _; trivial
  | cons a tl ih =>
    have hpt : -(1 - α) * (((a : Rat) / D) * ((a : Rat) / D)) ≤ C := by
      have hsq : (0 : Rat) ≤ ((a : Rat) / D) * ((a : Rat) / D) := rat_sq_nonneg _
      have hprod : (0 : Rat) ≤ (1 - α) * (((a : Rat) / D) * ((a : Rat) / D)) :=
        Rat.mul_nonneg hδ hsq
      have hle0 : -(1 - α) * (((a : Rat) / D) * ((a : Rat) / D)) ≤ 0 := by
        apply rat_le_of_sub_nonneg
        have heq : (0 : Rat) - -(1 - α) * (((a : Rat) / D) * ((a : Rat) / D)) =
            (1 - α) * (((a : Rat) / D) * ((a : Rat) / D)) := by grind
        rw [heq]; exact hprod
      exact Rat.le_trans hle0 hC
    cases tl with
    | nil =>
      intro _
      exact hpt
    | cons b rest =>
      intro hchk
      simp only [checkGridNums, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
      have hab : a < b := hchk.1.1
      have hmid : (((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
          (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2)) ≤ C := by
        cases hchk.1.2 with
        | inl hu => exact hUnit a b hab hu.1 hu.2
        | inr hr => exact hRatio a b hab hr.1 hr.2
      exact ⟨hpt, hmid, ih hchk.2⟩

/-- Unit-step midpoint bound: when `b - a = 1` and `1 ≤ a + b`,
    `h^2 - (1 - α) m^2 ≤ α / (4 D^2)`. -/
private theorem unit_step_mxfp {D : Nat} (hD : 0 < D) {α : Rat} (hδ : (0 : Rat) ≤ 1 - α)
    (a b : Nat) (hab : a < b) (hba : b - a = 1) (hs : 1 ≤ a + b) :
    (((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
    (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2)) ≤
    α / (4 * (D : Rat) * (D : Rat)) := by
  have hDne : (D : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hD)
  have hdiff : (b : Rat) - (a : Rat) = 1 := by
    have := rat_natCast_sub (Nat.le_of_lt hab)
    rw [hba] at this
    exact this.symm
  have hsum : (1 : Rat) ≤ (a : Rat) + (b : Rat) := by
    have h1 := rat_natCast_le hs
    rw [Rat.natCast_add] at h1
    exact h1
  have hsq_ge : (1 : Rat) ≤ ((a : Rat) + (b : Rat)) * ((a : Rat) + (b : Rat)) := by
    have h0 : (0 : Rat) ≤ (a : Rat) + (b : Rat) := Rat.le_trans (by decide) hsum
    have h1 := rat_mul_le_mul_of_nonneg_left hsum h0
    have h2 : (1 : Rat) ≤ ((a : Rat) + (b : Rat)) * 1 := by grind
    exact Rat.le_trans h2 h1
  have h4D2 : (0 : Rat) < 4 * (D : Rat) * (D : Rat) := by
    have hDp := rat_natCast_pos hD
    exact rat_mul_pos (rat_mul_pos (by decide) hDp) hDp
  have h4D2ne : 4 * (D : Rat) * (D : Rat) ≠ 0 := Rat.ne_of_gt h4D2
  apply rat_le_of_sub_nonneg
  have heq : α / (4 * (D : Rat) * (D : Rat)) -
      ((((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
       (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2))) =
      (1 - α) * (((a : Rat) + (b : Rat)) * ((a : Rat) + (b : Rat)) - 1) / (4 * (D : Rat) * (D : Rat)) := by
    have hsub : (b : Rat) / D - (a : Rat) / D = 1 / D := by
      have : ((b : Rat) - (a : Rat)) / D = (b : Rat) / D - (a : Rat) / D := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
      rw [← this, hdiff]
    have hadd : (a : Rat) / D + (b : Rat) / D = ((a : Rat) + (b : Rat)) / D := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
    rw [hsub, hadd]
    have hinv : ((D : Rat)⁻¹) * (D : Rat) = 1 := Rat.inv_mul_cancel (D : Rat) hDne
    have h2inv : ((2 : Rat)⁻¹) * (2 : Rat) = 1 := Rat.inv_mul_cancel 2 (by decide)
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
    have h4D2_inv : (4 * (D : Rat) * (D : Rat))⁻¹ = (4 : Rat)⁻¹ * (D : Rat)⁻¹ * (D : Rat)⁻¹ := by
      have hmul : ((4 * (D : Rat) * (D : Rat))⁻¹ - (4 : Rat)⁻¹ * (D : Rat)⁻¹ * (D : Rat)⁻¹) *
          (4 * (D : Rat) * (D : Rat)) = 0 := by
        have h1 : (4 * (D : Rat) * (D : Rat))⁻¹ * (4 * (D : Rat) * (D : Rat)) = 1 :=
          Rat.inv_mul_cancel _ h4D2ne
        have h4 : (4 : Rat)⁻¹ * 4 = 1 := Rat.inv_mul_cancel 4 (by decide)
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (h4D2ne h0)
    rw [h4D2_inv]
    have h2sq : (2 : Rat)⁻¹ * (2 : Rat)⁻¹ = (4 : Rat)⁻¹ := by
      have h4 : (4 : Rat)⁻¹ * 4 = 1 := Rat.inv_mul_cancel 4 (by decide)
      have hmul : ((2 : Rat)⁻¹ * (2 : Rat)⁻¹ - (4 : Rat)⁻¹) * 4 = 0 := by grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim ((by decide : (4 : Rat) ≠ 0) h0)
    grind
  rw [heq]
  exact rat_div_nonneg (Rat.mul_nonneg hδ (rat_sub_nonneg hsq_ge)) h4D2

/-- Ratio-step midpoint bound for MXFP: when `ratio * (b - a) ≤ a + b` and
    `1 ≤ (ratio^2) * (1 - α)` and `0 ≤ C`, then `h^2 - (1 - α) m^2 ≤ C`. -/
private theorem ratio_step_mxfp {D ratio : Nat} (hD : 0 < D) (hr : 0 < ratio)
    {α C : Rat} (hC : (0 : Rat) ≤ C)
    (hδr : (1 : Rat) ≤ ((ratio : Rat) * (ratio : Rat)) * (1 - α))
    (a b : Nat) (hab : a < b) (hbr : ratio * (b - a) ≤ a + b) :
    (((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
    (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2)) ≤ C := by
  have hDpos : (0 : Rat) < (D : Rat) := rat_natCast_pos hD
  have hrpos : (0 : Rat) < (ratio : Rat) := rat_natCast_pos hr
  have hr2pos : (0 : Rat) < (ratio : Rat) * (ratio : Rat) := rat_mul_pos hrpos hrpos
  let h : Rat := ((b : Rat) / D - (a : Rat) / D) / 2
  let m : Rat := ((a : Rat) / D + (b : Rat) / D) / 2
  have hh_nonneg : (0 : Rat) ≤ h := by
    have h1 : (0 : Rat) ≤ (b : Rat) - (a : Rat) := rat_sub_nonneg (rat_natCast_le (Nat.le_of_lt hab))
    have h2 : (b : Rat) / D - (a : Rat) / D = ((b : Rat) - (a : Rat)) / D := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
    change (0 : Rat) ≤ ((b : Rat) / D - (a : Rat) / D) / 2
    rw [h2]
    exact rat_div_nonneg (rat_div_nonneg h1 hDpos) (by decide)
  have hrh_le_m : (ratio : Rat) * h ≤ m := by
    have h1 : (ratio : Rat) * ((b : Rat) - (a : Rat)) ≤ (a : Rat) + (b : Rat) := by
      have hc := rat_natCast_le hbr
      rw [Rat.natCast_mul, Rat.natCast_add, rat_natCast_sub (Nat.le_of_lt hab)] at hc
      exact hc
    have h2D : (0 : Rat) < 2 * (D : Rat) := rat_mul_pos (by decide) hDpos
    have hdiv := rat_div_le_div_of_cross h2D h2D
      (rat_mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt h2D))
    have hlhs : (ratio : Rat) * h = (ratio : Rat) * ((b : Rat) - (a : Rat)) / (2 * (D : Rat)) := by
      dsimp only [h]
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, rat_2D_inv hD]; grind
    have hrhs : m = ((a : Rat) + (b : Rat)) / (2 * (D : Rat)) := by
      dsimp only [m]
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, rat_2D_inv hD]; grind
    rw [hlhs, hrhs]
    exact hdiv
  have hsq : ((ratio : Rat) * h) * ((ratio : Rat) * h) ≤ m * m := by
    have hrh0 : (0 : Rat) ≤ (ratio : Rat) * h := Rat.mul_nonneg (Rat.le_of_lt hrpos) hh_nonneg
    have hm0 : (0 : Rat) ≤ m := Rat.le_trans hrh0 hrh_le_m
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hrh_le_m hrh0)
      (rat_mul_le_mul_of_nonneg_left hrh_le_m hm0)
  have hle0 : h * h - (1 - α) * (m * m) ≤ 0 := by
    apply rat_le_of_mul_pos_right hr2pos
    rw [Rat.zero_mul]
    have h1 : (m * m) ≤ ((ratio : Rat) * (ratio : Rat) * (1 - α)) * (m * m) := by
      have := rat_mul_le_mul_of_nonneg_right hδr (rat_sq_nonneg m)
      simpa [Rat.one_mul] using this
    have h2 : ((ratio : Rat) * h) * ((ratio : Rat) * h) ≤
        ((ratio : Rat) * (ratio : Rat) * (1 - α)) * (m * m) := Rat.le_trans hsq h1
    have hsub := rat_sub_nonneg h2
    apply rat_le_of_sub_nonneg
    have heq : (0 : Rat) - (h * h - (1 - α) * (m * m)) * ((ratio : Rat) * (ratio : Rat)) =
        ((ratio : Rat) * (ratio : Rat) * (1 - α)) * (m * m) -
        ((ratio : Rat) * h) * ((ratio : Rat) * h) := by grind
    rw [heq]; exact hsub
  exact Rat.le_trans hle0 hC

/-! ### 2. Generic NVFP Step Bounds (Unit-Step & Ratio-Step) -/

private theorem unit_step_nvfp {D : Nat} (hD : 0 < D) {B : Nat} (hB2 : 2 ≤ B)
    {α M : Rat} (hδ : (0 : Rat) ≤ 1 - α)
    (hα_bd : α * (4 * (D : Rat) * (D : Rat) * (M * M) + ((B - 1 : Nat) : Rat)) ≤
             4 * (D : Rat) * (D : Rat) * (M * M))
    (a b : Nat) (hab : a < b) (hba : b - a = 1) (hs : 1 ≤ a + b) :
    (((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
    (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2)) ≤
    (1 - α) * (M * M) / ((B - 1 : Nat) : Rat) := by
  have hstep1 := unit_step_mxfp hD hδ a b hab hba hs
  have hBm1 : (0 : Rat) < ((B - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
  have h4D2 : (0 : Rat) < 4 * (D : Rat) * (D : Rat) := by
    have hDp := rat_natCast_pos hD
    exact rat_mul_pos (rat_mul_pos (by decide) hDp) hDp
  have hstep2 : α / (4 * (D : Rat) * (D : Rat)) ≤ (1 - α) * (M * M) / ((B - 1 : Nat) : Rat) := by
    apply rat_div_le_div_of_cross h4D2 hBm1
    have h1 := rat_sub_nonneg hα_bd
    apply rat_le_of_sub_nonneg
    have heq : (1 - α) * (M * M) * (4 * (D : Rat) * (D : Rat)) - α * ((B - 1 : Nat) : Rat) =
        4 * (D : Rat) * (D : Rat) * (M * M) -
        α * (4 * (D : Rat) * (D : Rat) * (M * M) + ((B - 1 : Nat) : Rat)) := by grind
    rw [heq]; exact h1
  exact Rat.le_trans hstep1 hstep2

private theorem ratio_step_nvfp {D maxGap ratio : Nat} (hD : 0 < D) (hG : 0 < maxGap)
    {B : Nat} (hB2 : 2 ≤ B) {α M : Rat}
    (hα_bd : ((B - 1 : Nat) : Rat) * (((maxGap : Rat) / (2 * (D : Rat))) * ((maxGap : Rat) / (2 * (D : Rat)))) ≤
             (1 - α) * (M * M + ((B - 1 : Nat) : Rat) *
               (((ratio : Rat) * ((maxGap : Rat) / (2 * (D : Rat)))) *
                ((ratio : Rat) * ((maxGap : Rat) / (2 * (D : Rat)))))))
    (a b : Nat) (hab : a < b) (hgap : b - a ≤ maxGap) (hbr : ratio * (b - a) ≤ a + b) :
    (((b : Rat) / D - (a : Rat) / D) / 2) * (((b : Rat) / D - (a : Rat) / D) / 2) -
    (1 - α) * ((((a : Rat) / D + (b : Rat) / D) / 2) * (((a : Rat) / D + (b : Rat) / D) / 2)) ≤
    (1 - α) * (M * M) / ((B - 1 : Nat) : Rat) := by
  have hDpos : (0 : Rat) < (D : Rat) := rat_natCast_pos hD
  have hBm1 : (0 : Rat) < ((B - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
  have h2D : (0 : Rat) < 2 * (D : Rat) := rat_mul_pos (by decide) hDpos
  let h : Rat := ((b : Rat) / D - (a : Rat) / D) / 2
  let m : Rat := ((a : Rat) / D + (b : Rat) / D) / 2
  let hmax : Rat := (maxGap : Rat) / (2 * (D : Rat))
  have hhmax_pos : (0 : Rat) < hmax := rat_div_pos (rat_natCast_pos hG) h2D
  have hh_eq : h = ((b - a : Nat) : Rat) / (2 * (D : Rat)) := by
    dsimp only [h]
    rw [rat_natCast_sub (Nat.le_of_lt hab)]
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, rat_2D_inv hD]; grind
  have hm_eq : m = ((a : Rat) + (b : Rat)) / (2 * (D : Rat)) := by
    dsimp only [m]
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, rat_2D_inv hD]; grind
  have hh_nonneg : (0 : Rat) ≤ h := by
    rw [hh_eq]; exact rat_div_nonneg (rat_natCast_nonneg _) h2D
  have hh_le_hmax : h ≤ hmax := by
    rw [hh_eq]
    apply rat_div_le_div_of_cross h2D h2D
    exact rat_mul_le_mul_of_nonneg_right (rat_natCast_le hgap) (Rat.le_of_lt h2D)
  have hrh_le_m : (ratio : Rat) * h ≤ m := by
    rw [hh_eq, hm_eq]
    have h1 : (ratio : Rat) * ((b - a : Nat) : Rat) ≤ (a : Rat) + (b : Rat) := by
      have hc := rat_natCast_le hbr
      rw [Rat.natCast_mul, Rat.natCast_add] at hc
      exact hc
    have hdiv := rat_div_le_div_of_cross h2D h2D
      (rat_mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt h2D))
    have hlhs : (ratio : Rat) * (((b - a : Nat) : Rat) / (2 * (D : Rat))) =
        (ratio : Rat) * ((b - a : Nat) : Rat) / (2 * (D : Rat)) := by
      rw [Rat.div_def, Rat.div_def]; grind
    rw [hlhs]; exact hdiv
  have hh2_le : h * h ≤ hmax * hmax :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_right hh_le_hmax hh_nonneg)
      (rat_mul_le_mul_of_nonneg_left hh_le_hmax (Rat.le_of_lt hhmax_pos))
  have hrh2_le : ((ratio : Rat) * h) * ((ratio : Rat) * h) ≤ m * m := by
    have hrh0 : (0 : Rat) ≤ (ratio : Rat) * h :=
      Rat.mul_nonneg (rat_natCast_nonneg ratio) hh_nonneg
    have hm0 : (0 : Rat) ≤ m := Rat.le_trans hrh0 hrh_le_m
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hrh_le_m hrh0)
      (rat_mul_le_mul_of_nonneg_left hrh_le_m hm0)
  have hkey : h * h * (M * M + ((B - 1 : Nat) : Rat) *
      (((ratio : Rat) * hmax) * ((ratio : Rat) * hmax))) ≤
      (hmax * hmax) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) := by
    have h1 : h * h * (M * M) ≤ (hmax * hmax) * (M * M) :=
      rat_mul_le_mul_of_nonneg_right hh2_le (rat_sq_nonneg M)
    have h2 : ((B - 1 : Nat) : Rat) * (hmax * hmax) * (((ratio : Rat) * h) * ((ratio : Rat) * h)) ≤
        ((B - 1 : Nat) : Rat) * (hmax * hmax) * (m * m) :=
      rat_mul_le_mul_of_nonneg_left hrh2_le (Rat.mul_nonneg (Rat.le_of_lt hBm1) (rat_sq_nonneg hmax))
    have hsum := rat_add_le_add h1 h2
    have hlhs : h * h * (M * M + ((B - 1 : Nat) : Rat) *
        (((ratio : Rat) * hmax) * ((ratio : Rat) * hmax))) =
        h * h * (M * M) + ((B - 1 : Nat) : Rat) * (hmax * hmax) *
          (((ratio : Rat) * h) * ((ratio : Rat) * h)) := by grind
    have hrhs : (hmax * hmax) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) =
        (hmax * hmax) * (M * M) + ((B - 1 : Nat) : Rat) * (hmax * hmax) * (m * m) := by grind
    rw [hlhs, hrhs]; exact hsum
  let Q : Rat := M * M + ((B - 1 : Nat) : Rat) * (((ratio : Rat) * hmax) * ((ratio : Rat) * hmax))
  have hQ_nonneg : (0 : Rat) ≤ Q :=
    rat_add_nonneg (rat_sq_nonneg M)
      (Rat.mul_nonneg (Rat.le_of_lt hBm1) (rat_sq_nonneg ((ratio : Rat) * hmax)))
  have hδQ_pos : (0 : Rat) < (1 - α) * Q := by
    have hpos : (0 : Rat) < ((B - 1 : Nat) : Rat) * (hmax * hmax) :=
      rat_mul_pos hBm1 (rat_mul_pos hhmax_pos hhmax_pos)
    exact rat_lt_of_lt_of_le hpos hα_bd
  have hQ_pos : (0 : Rat) < Q := by
    have hne : Q ≠ 0 := by
      intro h0
      rw [h0, Rat.mul_zero] at hδQ_pos
      exact Rat.not_le.mpr hδQ_pos Rat.le_refl
    exact Rat.lt_of_le_of_ne hQ_nonneg (Ne.symm hne)
  apply rat_le_div_of_mul_le hBm1
  have hgoal_iff : (h * h - (1 - α) * (m * m)) * ((B - 1 : Nat) : Rat) ≤ (1 - α) * (M * M) ↔
      ((B - 1 : Nat) : Rat) * (h * h) ≤ (1 - α) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) := by
    constructor <;> intro hx
    · apply rat_le_of_sub_nonneg
      have hsub := rat_sub_nonneg hx
      have heq : (1 - α) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) - ((B - 1 : Nat) : Rat) * (h * h) =
          (1 - α) * (M * M) - (h * h - (1 - α) * (m * m)) * ((B - 1 : Nat) : Rat) := by grind
      rw [heq]; exact hsub
    · apply rat_le_of_sub_nonneg
      have hsub := rat_sub_nonneg hx
      have heq : (1 - α) * (M * M) - (h * h - (1 - α) * (m * m)) * ((B - 1 : Nat) : Rat) =
          (1 - α) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) - ((B - 1 : Nat) : Rat) * (h * h) := by grind
      rw [heq]; exact hsub
  rw [hgoal_iff]
  apply rat_le_of_mul_pos_right hQ_pos
  have hstepA : ((B - 1 : Nat) : Rat) * (h * h) * Q ≤
      ((B - 1 : Nat) : Rat) * (hmax * hmax) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) := by
    have h1 := rat_mul_le_mul_of_nonneg_left hkey (Rat.le_of_lt hBm1)
    have hlhs : ((B - 1 : Nat) : Rat) * (h * h) * Q =
        ((B - 1 : Nat) : Rat) * (h * h * Q) := by grind
    have hrhs : ((B - 1 : Nat) : Rat) * (hmax * hmax) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) =
        ((B - 1 : Nat) : Rat) * ((hmax * hmax) * (M * M + ((B - 1 : Nat) : Rat) * (m * m))) := by grind
    rw [hlhs, hrhs]; exact h1
  have hstepB : ((B - 1 : Nat) : Rat) * (hmax * hmax) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) ≤
      (1 - α) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) * Q := by
    have hMm_nonneg : (0 : Rat) ≤ M * M + ((B - 1 : Nat) : Rat) * (m * m) :=
      rat_add_nonneg (rat_sq_nonneg M) (Rat.mul_nonneg (Rat.le_of_lt hBm1) (rat_sq_nonneg m))
    have h1 := rat_mul_le_mul_of_nonneg_right hα_bd hMm_nonneg
    have hrhs : (1 - α) * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) * Q =
        (1 - α) * Q * (M * M + ((B - 1 : Nat) : Rat) * (m * m)) := by grind
    rw [hrhs]; exact h1
  exact Rat.le_trans hstepA hstepB

/-! ### 3. Dropping Prefixes via Pure-`Nat` Numerator Bounds -/

private theorem nearestNonneg_drop_prefix_nat (D M : Nat) (hD : 0 < D) :
    ∀ (pref tail : List Nat),
      tail ≠ [] →
      (∀ g ∈ pref, g ≤ M) →
      (match tail with | [] => True | h :: _ => h ≤ M) →
      ∀ (y : Rat), (M : Rat) / (D : Rat) < y →
        nearestNonneg ((pref ++ tail).map (fun (k : Nat) => (k : Rat) / (D : Rat))) y =
        nearestNonneg (tail.map (fun (k : Nat) => (k : Rat) / (D : Rat))) y := by
  intro pref
  induction pref with
  | nil => intro _ _ _ _ _ _; rfl
  | cons a pref' ih =>
    intro tail htail_ne hpref htail y hy
    have ha : a ≤ M := hpref a (by simp)
    have hpref' : ∀ g ∈ pref', g ≤ M := fun g hg => hpref g (by simp [hg])
    cases hpt : pref' ++ tail with
    | nil =>
      exfalso
      cases pref' with
      | nil => simp at hpt; exact htail_ne hpt
      | cons _ _ => simp at hpt
    | cons b rest =>
      have hb : b ≤ M := by
        cases pref' with
        | nil => simp at hpt; subst hpt; exact htail
        | cons p ps =>
          simp only [List.cons_append, List.cons.injEq] at hpt
          rcases hpt with ⟨hp, _⟩
          rw [← hp]
          exact hpref' p (by simp)
      have hmid_le : ((a : Rat) / (D : Rat) + (b : Rat) / (D : Rat)) / 2 ≤ (M : Rat) / (D : Rat) := by
        have hDpos : (0 : Rat) < (D : Rat) := rat_natCast_pos hD
        have h2D : (0 : Rat) < 2 * (D : Rat) := rat_mul_pos (by decide) hDpos
        have hsum : a + b ≤ 2 * M := by omega
        have hlhs : ((a : Rat) / (D : Rat) + (b : Rat) / (D : Rat)) / 2 =
            ((a : Rat) + (b : Rat)) / (2 * (D : Rat)) := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, rat_2D_inv hD]; grind
        rw [hlhs]
        apply rat_div_le_div_of_cross h2D hDpos
        have hcast := rat_natCast_le hsum
        rw [Rat.natCast_add, Rat.natCast_mul] at hcast
        have h1 := rat_mul_le_mul_of_nonneg_right hcast (Rat.le_of_lt hDpos)
        have heqR : ((2 : Nat) : Rat) * (M : Rat) * (D : Rat) = (M : Rat) * (2 * (D : Rat)) := by grind
        rw [heqR] at h1; exact h1
      have hlt : ((a : Rat) / (D : Rat) + (b : Rat) / (D : Rat)) / 2 < y :=
        rat_lt_of_le_of_lt hmid_le hy
      simp only [List.cons_append, List.map_cons, hpt]
      rw [nearestNonneg_drop_cons hlt]
      have := ih tail htail_ne hpref' htail y hy
      rw [hpt] at this
      exact this

private def e3m2UpperLevels : List Rat := [14, 16, 20, 24, 28]
private def e2m3UpperLevels : List Rat := [15/4, 4, 9/2, 5, 11/2, 6, 13/2, 7, 15/2]

private theorem nearestNonneg_e3m2_upper {y : Rat} (hy : (14 : Rat) < y) :
    nearestNonneg e3m2Levels y = nearestNonneg e3m2UpperLevels y := by
  rw [e3m2Levels_eq_map]
  let pref : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28,
    32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192]
  let tail : List Nat := [224, 256, 320, 384, 448]
  have hsplit : e3m2Nums = pref ++ tail := rfl
  have hpref_le : ∀ g ∈ pref, g ≤ 224 := by decide
  have hy' : ((224 : Nat) : Rat) / ((16 : Nat) : Rat) < y := by
    have heq : ((224 : Nat) : Rat) / ((16 : Nat) : Rat) = 14 :=
      rat_div_eq_int (by decide) (by grind)
    rw [heq]; exact hy
  have hdrop := nearestNonneg_drop_prefix_nat 16 224 (by decide) pref tail (by decide) hpref_le (by decide) y hy'
  have htail_eq : tail.map (fun (k : Nat) => (k : Rat) / 16) = e3m2UpperLevels := by
    simp only [tail, e3m2UpperLevels, List.map, List.cons.injEq, and_true]
    repeat (first
      | exact rat_div_eq_int (by decide) (by grind)
      | constructor)
  rw [hsplit]
  exact Eq.trans hdrop (congrArg (fun l => nearestNonneg l y) htail_eq)

private theorem nearestNonneg_e2m3_upper {y : Rat} (hy : (15/4 : Rat) < y) :
    nearestNonneg e2m3Levels y = nearestNonneg e2m3UpperLevels y := by
  rw [e2m3Levels_eq_map]
  let pref : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 18, 20, 22, 24, 26, 28]
  let tail : List Nat := [30, 32, 36, 40, 44, 48, 52, 56, 60]
  have hsplit : e2m3Nums = pref ++ tail := rfl
  have hpref_le : ∀ g ∈ pref, g ≤ 30 := by decide
  have hy' : ((30 : Nat) : Rat) / ((8 : Nat) : Rat) < y := by
    have heq : ((30 : Nat) : Rat) / ((8 : Nat) : Rat) = 15 / 4 :=
      rat_div_eq_of_cross (by decide) (by decide) (by grind)
    rw [heq]; exact hy
  have hdrop := nearestNonneg_drop_prefix_nat 8 30 (by decide) pref tail (by decide) hpref_le (by decide) y hy'
  have htail_eq : tail.map (fun (k : Nat) => (k : Rat) / 8) = e2m3UpperLevels := by
    simp only [tail, e2m3UpperLevels, List.map, List.cons.injEq, and_true]
    repeat (first
      | exact rat_div_eq_of_cross (by decide) (by decide) (by grind)
      | exact rat_div_eq_int (by decide) (by grind)
      | constructor)
  rw [hsplit]
  exact Eq.trans hdrop (congrArg (fun l => nearestNonneg l y) htail_eq)

/-! ### 4. Theorem 1: Universal All-`B` EF21 Contraction for `MXFP6-E3M2` and `NVFP6-E3M2` -/

private theorem alphaMXFP6E3M2_pos {B : Nat} (hB : 0 < B) : (0 : Rat) < alphaMXFP6E3M2 B := by
  unfold alphaMXFP6E3M2
  have hd1 : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have hd2 : (0 : Rat) < (B : Rat) + 230399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have hd3 : (0 : Rat) < (B : Rat) + 200703 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have h1 : (0 : Rat) < 327680 / ((B : Rat) + 331775) := rat_div_pos (by decide) hd1
  have h2 : (0 : Rat) < 229376 / ((B : Rat) + 230399) := rat_div_pos (by decide) hd2
  have h3 : (0 : Rat) < 200704 / ((B : Rat) + 200703) := rat_div_pos (by decide) hd3
  have hmin2 : (0 : Rat) < min (229376 / ((B : Rat) + 230399)) (200704 / ((B : Rat) + 200703)) := by
    change (0 : Rat) < if _ ≤ _ then _ else _
    split <;> assumption
  change (0 : Rat) < if _ ≤ _ then _ else _
  split <;> assumption

private theorem alphaMXFP6E3M2_le_80_81 {B : Nat} (hB : 0 < B) :
    alphaMXFP6E3M2 B ≤ (80 : Rat) / 81 := by
  have h1 : alphaMXFP6E3M2 B ≤ 327680 / ((B : Rat) + 331775) := rat_min_le_left _ _
  have hd : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have h2 : 327680 / ((B : Rat) + 331775) ≤ (80 : Rat) / 81 := by
    apply rat_div_le_div_of_cross hd (by decide)
    have hB1 : (1 : Rat) ≤ (B : Rat) := rat_natCast_le hB
    have hsub := rat_sub_nonneg hB1
    apply rat_le_of_sub_nonneg
    have heq : (80 : Rat) * ((B : Rat) + 331775) - 327680 * 81 = 80 * ((B : Rat) - 1) := by grind
    rw [heq]
    exact Rat.mul_nonneg (by decide) hsub
  exact Rat.le_trans h1 h2

private theorem mxfp6_e3m2_upper_bound (B : Nat) (hB : 0 < B) (y : Fin B → Rat)
    (hmax : ∀ i, absRat (y i) ≤ 28)
    (hanc : ∃ i0, (14 : Rat) < absRat (y i0)) :
    sumSqErr e3m2Quant y ≤ (1 - alphaMXFP6E3M2 B) * sumSq y := by
  let α := alphaMXFP6E3M2 B
  have hα_pos : (0 : Rat) < α := alphaMXFP6E3M2_pos hB
  have hα_nonneg : (0 : Rat) ≤ α := Rat.le_of_lt hα_pos
  have hα_8081 : α ≤ (80 : Rat) / 81 := alphaMXFP6E3M2_le_80_81 hB
  have hδ_ge : (1 : Rat) ≤ (9 : Rat) * 9 * (1 - α) := by
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hα_8081
    have heq : (9 : Rat) * 9 * (1 - α) - 1 = 81 * ((80 : Rat) / 81 - α) := by
      have h81 : (81 : Rat) * (81 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 81 (by decide)
      rw [Rat.div_def]; grind
    rw [heq]; exact Rat.mul_nonneg (by decide) hsub
  have hδ_nonneg : (0 : Rat) ≤ 1 - α := by
    have h1 : (80 : Rat) / 81 ≤ 1 := by
      have h := rat_div_le_div_nat 80 81 1 1 (by decide) (by decide) (by decide)
      have h1' : ((1 : Nat) : Rat) / ((1 : Nat) : Rat) = 1 := rat_div_eq_int (by decide) (by grind)
      rw [h1'] at h; exact h
    exact rat_sub_nonneg (Rat.le_trans hα_8081 h1)
  let C : Rat := α / 1024
  have hC_nonneg : (0 : Rat) ≤ C := rat_div_nonneg hα_nonneg (by decide)
  have hnonanc : ∀ i : Fin B,
      (e3m2Quant (y i) - y i) * (e3m2Quant (y i) - y i) - (1 - α) * (y i * y i) ≤ C := by
    intro i
    rw [← absRat_sq (y i)]
    unfold e3m2Quant
    rw [symQuant_sq_err_abs]
    have hsort : isSorted e3m2Levels := by
      rw [e3m2Levels_eq_map]
      exact isSorted_map_div (by decide) 64 9 e3m2Nums check_e3m2Nums
    have hgb : gridQuadBound α C e3m2Levels := by
      rw [e3m2Levels_eq_map]
      apply gridQuadBound_of_check (D := 16) (maxGap := 64) (ratio := 9) hδ_nonneg hC_nonneg
      · intro a b hab hba hs
        have hu := unit_step_mxfp (D := 16) (by decide) hδ_nonneg a b hab hba hs
        have h1024 : (4 : Rat) * ((16 : Nat) : Rat) * ((16 : Nat) : Rat) = 1024 := by grind
        rw [h1024] at hu; exact hu
      · intro a b hab _ hbr
        exact ratio_step_mxfp (D := 16) (ratio := 9) (by decide) (by decide) hC_nonneg hδ_ge a b hab hbr
      · exact check_e3m2Nums
    have hy0 : (0 : Rat) ≤ absRat (y i) := absRat_nonneg (y i)
    have hy28 : absRat (y i) ≤ lastLevel e3m2Levels := by
      have hlast : lastLevel e3m2Levels = 28 := rfl
      rw [hlast]; exact hmax i
    exact nearestNonneg_quad_le hα_nonneg e3m2Levels hsort hgb 0 e3m2Levels.tail rfl (absRat (y i)) hy0 hy28
  rcases hanc with ⟨i0, hi0⟩
  let A : Rat := -(((B - 1 : Nat) : Rat) * C)
  have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
    have := rat_natCast_sub hB; simpa using this
  have hα1 : α ≤ 327680 / ((B : Rat) + 331775) := rat_min_le_left _ _
  have hα2 : α ≤ 229376 / ((B : Rat) + 230399) :=
    Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _)
  have hα3 : α ≤ 200704 / ((B : Rat) + 200703) :=
    Rat.le_trans (rat_min_le_right _ _) (rat_min_le_right _ _)
  have hpt14 : -(1 - α) * (14 * 14) ≤ A := by
    have hd : (0 : Rat) < (B : Rat) + 200703 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
    have hmul := rat_mul_le_mul_of_nonneg_right hα3 (Rat.le_of_lt hd)
    have hcancel : 200704 / ((B : Rat) + 200703) * ((B : Rat) + 200703) = 200704 := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
    rw [hcancel] at hmul
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hmul
    have heq : A - -(1 - α) * (14 * 14) = (200704 - α * ((B : Rat) + 200703)) / 1024 := by
      dsimp only [A, C]; rw [hBm1_eq, Rat.div_def, Rat.div_def]
      have h1024 : (1024 : Rat) * (1024 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1024 (by decide)
      grind
    rw [heq]; exact rat_div_nonneg hsub (by decide)
  have hmid15 : ((16 - 14 : Rat) / 2) * ((16 - 14 : Rat) / 2) -
      (1 - α) * (((14 + 16 : Rat) / 2) * ((14 + 16 : Rat) / 2)) ≤ A := by
    have hd : (0 : Rat) < (B : Rat) + 230399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
    have hmul := rat_mul_le_mul_of_nonneg_right hα2 (Rat.le_of_lt hd)
    have hcancel : 229376 / ((B : Rat) + 230399) * ((B : Rat) + 230399) = 229376 := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
    rw [hcancel] at hmul
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hmul
    have heq : A - (((16 - 14 : Rat) / 2) * ((16 - 14 : Rat) / 2) -
        (1 - α) * (((14 + 16 : Rat) / 2) * ((14 + 16 : Rat) / 2))) =
        (229376 - α * ((B : Rat) + 230399)) / 1024 := by
      dsimp only [A, C]; rw [hBm1_eq]
      have h1 : (16 - 14 : Rat) / 2 = 1 := rat_div_eq_int (by decide) (by grind)
      have h2 : (14 + 16 : Rat) / 2 = 15 := rat_div_eq_int (by decide) (by grind)
      rw [h1, h2, Rat.div_def, Rat.div_def]
      have h1024 : (1024 : Rat) * (1024 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1024 (by decide)
      grind
    rw [heq]; exact rat_div_nonneg hsub (by decide)
  have hmid18 : ((20 - 16 : Rat) / 2) * ((20 - 16 : Rat) / 2) -
      (1 - α) * (((16 + 20 : Rat) / 2) * ((16 + 20 : Rat) / 2)) ≤ A := by
    have hd : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
    have hmul := rat_mul_le_mul_of_nonneg_right hα1 (Rat.le_of_lt hd)
    have hcancel : 327680 / ((B : Rat) + 331775) * ((B : Rat) + 331775) = 327680 := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
    rw [hcancel] at hmul
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hmul
    have heq : A - (((20 - 16 : Rat) / 2) * ((20 - 16 : Rat) / 2) -
        (1 - α) * (((16 + 20 : Rat) / 2) * ((16 + 20 : Rat) / 2))) =
        (327680 - α * ((B : Rat) + 331775)) / 1024 := by
      dsimp only [A, C]; rw [hBm1_eq]
      have h1 : (20 - 16 : Rat) / 2 = 2 := rat_div_eq_int (by decide) (by grind)
      have h2 : (16 + 20 : Rat) / 2 = 18 := rat_div_eq_int (by decide) (by grind)
      rw [h1, h2, Rat.div_def, Rat.div_def]
      have h1024 : (1024 : Rat) * (1024 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1024 (by decide)
      grind
    rw [heq]; exact rat_div_nonneg hsub (by decide)
  have hpt_ge14 : ∀ g : Rat, (14 : Rat) ≤ g → -(1 - α) * (g * g) ≤ A := by
    intro g hg
    have hg2 : (14 : Rat) * 14 ≤ g * g := by
      have hg0 : (0 : Rat) ≤ g := Rat.le_trans (by decide) hg
      exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hg (by decide))
        (rat_mul_le_mul_of_nonneg_left hg hg0)
    have hle : -(1 - α) * (g * g) ≤ -(1 - α) * (14 * 14) := by
      apply rat_le_of_sub_nonneg
      have heq : -(1 - α) * (14 * 14) - -(1 - α) * (g * g) = (1 - α) * (g * g - 14 * 14) := by grind
      rw [heq]; exact Rat.mul_nonneg hδ_nonneg (rat_sub_nonneg hg2)
    exact Rat.le_trans hle hpt14
  have hmid22 : ((24 - 20 : Rat) / 2) * ((24 - 20 : Rat) / 2) -
      (1 - α) * (((20 + 24 : Rat) / 2) * ((20 + 24 : Rat) / 2)) ≤ A := by
    have hle : ((24 - 20 : Rat) / 2) * ((24 - 20 : Rat) / 2) -
        (1 - α) * (((20 + 24 : Rat) / 2) * ((20 + 24 : Rat) / 2)) ≤
        ((20 - 16 : Rat) / 2) * ((20 - 16 : Rat) / 2) -
        (1 - α) * (((16 + 20 : Rat) / 2) * ((16 + 20 : Rat) / 2)) := by
      apply rat_le_of_sub_nonneg
      have h1 : (24 - 20 : Rat) / 2 = 2 := rat_div_eq_int (by decide) (by grind)
      have h2 : (20 + 24 : Rat) / 2 = 22 := rat_div_eq_int (by decide) (by grind)
      have h3 : (20 - 16 : Rat) / 2 = 2 := rat_div_eq_int (by decide) (by grind)
      have h4 : (16 + 20 : Rat) / 2 = 18 := rat_div_eq_int (by decide) (by grind)
      rw [h1, h2, h3, h4]
      have heq : (2 * 2 - (1 - α) * (18 * 18)) - (2 * 2 - (1 - α) * (22 * 22)) = 160 * (1 - α) := by grind
      rw [heq]; exact Rat.mul_nonneg (by decide) hδ_nonneg
    exact Rat.le_trans hle hmid18
  have hmid26 : ((28 - 24 : Rat) / 2) * ((28 - 24 : Rat) / 2) -
      (1 - α) * (((24 + 28 : Rat) / 2) * ((24 + 28 : Rat) / 2)) ≤ A := by
    have hle : ((28 - 24 : Rat) / 2) * ((28 - 24 : Rat) / 2) -
        (1 - α) * (((24 + 28 : Rat) / 2) * ((24 + 28 : Rat) / 2)) ≤
        ((20 - 16 : Rat) / 2) * ((20 - 16 : Rat) / 2) -
        (1 - α) * (((16 + 20 : Rat) / 2) * ((16 + 20 : Rat) / 2)) := by
      apply rat_le_of_sub_nonneg
      have h1 : (28 - 24 : Rat) / 2 = 2 := rat_div_eq_int (by decide) (by grind)
      have h2 : (24 + 28 : Rat) / 2 = 26 := rat_div_eq_int (by decide) (by grind)
      have h3 : (20 - 16 : Rat) / 2 = 2 := rat_div_eq_int (by decide) (by grind)
      have h4 : (16 + 20 : Rat) / 2 = 18 := rat_div_eq_int (by decide) (by grind)
      rw [h1, h2, h3, h4]
      have heq : (2 * 2 - (1 - α) * (18 * 18)) - (2 * 2 - (1 - α) * (26 * 26)) = 352 * (1 - α) := by grind
      rw [heq]; exact Rat.mul_nonneg (by decide) hδ_nonneg
    exact Rat.le_trans hle hmid18
  have hanc_bd :
      (e3m2Quant (y i0) - y i0) * (e3m2Quant (y i0) - y i0) - (1 - α) * (y i0 * y i0) ≤ A := by
    rw [← absRat_sq (y i0)]
    unfold e3m2Quant
    rw [symQuant_sq_err_abs, nearestNonneg_e3m2_upper hi0]
    have hsort : isSorted e3m2UpperLevels := by
      refine ⟨by decide, by decide, by decide, by decide, trivial⟩
    have hgb : gridQuadBound α A e3m2UpperLevels :=
      ⟨hpt14, hmid15, hpt_ge14 16 (by decide), hmid18, hpt_ge14 20 (by decide),
       hmid22, hpt_ge14 24 (by decide), hmid26, hpt_ge14 28 (by decide)⟩
    exact nearestNonneg_quad_le hα_nonneg e3m2UpperLevels hsort hgb 14 [16, 20, 24, 28] rfl
      (absRat (y i0)) (Rat.le_of_lt hi0) (hmax i0)
  have hsum := sumFinRat_le_anchor i0
    (fun i => (e3m2Quant (y i) - y i) * (e3m2Quant (y i) - y i) - (1 - α) * (y i * y i))
    A C hanc_bd (fun i _ => hnonanc i)
  have hzero : A + ((B - 1 : Nat) : Rat) * C = 0 := by dsimp only [A]; grind
  rw [hzero, sumFinRat_sub, sumFinRat_mul_left] at hsum
  exact rat_le_of_sub_nonneg (by
    have h := rat_sub_nonneg hsum
    have heq : (1 - α) * sumSq y - sumSqErr e3m2Quant y =
        0 - (sumFinRat B (fun i => (e3m2Quant (y i) - y i) * (e3m2Quant (y i) - y i)) -
             (1 - α) * sumFinRat B (fun i => y i * y i)) := by
      unfold sumSq sumSqErr; grind
    rw [heq]; exact h)

/-! #### Exact Quantizer Evaluations at Witness Points (via `nearestNonneg_map_div`) -/

private theorem e3m2Quant_div_nat (p q : Nat) (hq : 0 < q) :
    e3m2Quant ((p : Rat) / (q : Rat)) = ((nearestNonnegNat 16 e3m2Nums p q : Nat) : Rat) / 16 := by
  unfold e3m2Quant symQuant
  have hnn : (0 : Rat) ≤ (p : Rat) / (q : Rat) := rat_div_nonneg_nat p q hq
  have hn : ¬((p : Rat) / (q : Rat) < 0) := Rat.not_lt.mpr hnn
  simp only [hn, ↓reduceIte]
  rw [e3m2Levels_eq_map]
  exact nearestNonneg_map_div 16 p q (by decide) hq e3m2Nums

private theorem e3m2Quant_18 : e3m2Quant 18 = 16 := by
  have h18 : (18 : Rat) = ((18 : Nat) : Rat) / ((1 : Nat) : Rat) :=
    (rat_div_eq_int (by decide) (by grind)).symm
  rw [h18, e3m2Quant_div_nat 18 1 (by decide)]
  have hnat : nearestNonnegNat 16 e3m2Nums 18 1 = 256 := by decide
  rw [hnat]
  exact rat_div_eq_int (by decide) (by grind)

private theorem e3m2Quant_15 : e3m2Quant 15 = 14 := by
  have h15 : (15 : Rat) = ((15 : Nat) : Rat) / ((1 : Nat) : Rat) :=
    (rat_div_eq_int (by decide) (by grind)).symm
  rw [h15, e3m2Quant_div_nat 15 1 (by decide)]
  have hnat : nearestNonnegNat 16 e3m2Nums 15 1 = 224 := by decide
  rw [hnat]
  exact rat_div_eq_int (by decide) (by grind)

private theorem e3m2Quant_28 : e3m2Quant 28 = 28 := by
  have h28 : (28 : Rat) = ((28 : Nat) : Rat) / ((1 : Nat) : Rat) :=
    (rat_div_eq_int (by decide) (by grind)).symm
  rw [h28, e3m2Quant_div_nat 28 1 (by decide)]
  have hnat : nearestNonnegNat 16 e3m2Nums 28 1 = 448 := by decide
  rw [hnat]
  exact rat_div_eq_int (by decide) (by grind)

private theorem e3m2Quant_1_32 : e3m2Quant (1/32) = 0 := by
  have h := e3m2Quant_div_nat 1 32 (by decide)
  have hnat : nearestNonnegNat 16 e3m2Nums 1 32 = 0 := by decide
  rw [hnat] at h
  have h0 : ((0 : Nat) : Rat) / 16 = 0 := rat_div_eq_int (by decide) (by grind)
  rw [h0] at h
  exact h

private theorem e3m2Quant_14_plus {t : Rat} (ht0 : (0 : Rat) < t) (ht1 : t < 1) :
    e3m2Quant (14 + t) = 14 := by
  unfold e3m2Quant symQuant
  have hpos : (14 : Rat) < 14 + t := by apply rat_lt_of_sub_pos; grind
  have hn : ¬((14 + t : Rat) < 0) := Rat.not_lt.mpr (Rat.le_trans (by decide) (Rat.le_of_lt hpos))
  simp only [hn, ↓reduceIte]
  rw [nearestNonneg_e3m2_upper hpos]
  unfold e3m2UpperLevels
  simp only [nearestNonneg]
  have hle15 : 14 + t ≤ (14 + 16) / 2 := by
    have h1 := Rat.le_of_lt ht1
    have h2 := rat_add_le_add (Rat.le_refl (a := (14 : Rat))) h1
    have heq : (14 + 16 : Rat) / 2 = 14 + 1 := rat_div_eq_int (by decide) (by grind)
    rw [heq]; exact h2
  simp only [hle15, ↓reduceIte]

private theorem mxfp6_e3m2_tight (B : Nat) (hB : 0 < B) (ε : Rat) (hε : (0 : Rat) < ε) :
    ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 28) ∧
      (∃ i0, (14 : Rat) < absRat (y i0)) ∧
      (1 - alphaMXFP6E3M2 B - ε) * sumSq y < sumSqErr e3m2Quant y := by
  let i0 : Fin B := ⟨0, hB⟩
  have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
    have := rat_natCast_sub hB; simpa using this
  have h1_32_nn : (0 : Rat) ≤ (1 : Rat) / 32 := rat_div_nonneg_nat 1 32 (by decide)
  have h1_32_le28 : (1 : Rat) / 32 ≤ 28 := by
    have h := rat_div_le_div_nat 1 32 28 1 (by decide) (by decide) (by decide)
    have h28 : ((28 : Nat) : Rat) / ((1 : Nat) : Rat) = 28 := rat_div_eq_int (by decide) (by grind)
    rw [h28] at h; exact h
  have h1_32_sq : (1 / 32 : Rat) * (1 / 32) = 1 / 1024 := by
    have h32ne : (32 : Rat) * 32 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
    have h1 : (1 / 32 : Rat) * (1 / 32) = 1 / (32 * 32) := by
      rw [Rat.div_def]
      have hmul : ((32 * 32 : Rat)⁻¹ - (32 : Rat)⁻¹ * (32 : Rat)⁻¹) * (32 * 32) = 0 := by
        have h32 : (32 : Rat)⁻¹ * 32 = 1 := Rat.inv_mul_cancel 32 (by decide)
        have h1024 : (32 * 32 : Rat)⁻¹ * (32 * 32) = 1 := Rat.inv_mul_cancel _ h32ne
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (h32ne h0)
    rw [h1]; exact rat_div_eq_of_cross h32ne (by decide) (by grind)
  by_cases h1 : B ≤ 6145
  · refine ⟨fun i => if i = i0 then 18 else 1/32, ?_, ⟨i0, by simp [absRat]; decide⟩, ?_⟩
    · intro i
      by_cases h : i = i0
      · simp only [h, ↓reduceIte, absRat_of_nonneg (by decide : (0 : Rat) ≤ 18)]; decide
      · simp only [h, ↓reduceIte, absRat_of_nonneg h1_32_nn]; exact h1_32_le28
    · have hα_eq : alphaMXFP6E3M2 B = 327680 / ((B : Rat) + 331775) := by
        unfold alphaMXFP6E3M2
        have hd1 : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
        have hd2 : (0 : Rat) < (B : Rat) + 230399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
        have hd3 : (0 : Rat) < (B : Rat) + 200703 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
        have hB_le : (B : Rat) ≤ 6145 := rat_natCast_le h1
        have h12 : 327680 / ((B : Rat) + 331775) ≤ 229376 / ((B : Rat) + 230399) := by
          apply rat_div_le_div_of_cross hd1 hd2
          apply rat_le_of_sub_nonneg
          have heq : 229376 * ((B : Rat) + 331775) - 327680 * ((B : Rat) + 230399) =
              98304 * (6145 - (B : Rat)) := by grind
          rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hB_le)
        have h13 : 327680 / ((B : Rat) + 331775) ≤ 200704 / ((B : Rat) + 200703) := by
          apply rat_div_le_div_of_cross hd1 hd3
          apply rat_le_of_sub_nonneg
          have hsub := rat_sub_nonneg hB_le
          have heq : 200704 * ((B : Rat) + 331775) - 327680 * ((B : Rat) + 200703) =
              126976 * (6145 - (B : Rat)) + 41943040 := by grind
          rw [heq]
          exact rat_add_nonneg (Rat.mul_nonneg (by decide) hsub) (by decide)
        exact rat_min_eq_left (rat_le_min h12 h13)
      have hsq : sumSq (fun i => if i = i0 then (18 : Rat) else 1/32) =
          324 + ((B - 1 : Nat) : Rat) / 1024 := by
        unfold sumSq
        have hcongr : (fun i => (if i = i0 then (18 : Rat) else 1/32) *
            (if i = i0 then (18 : Rat) else 1/32)) =
            (fun i => if i = i0 then (324 : Rat) else 1/1024) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte]; grind
          · simp only [h, ↓reduceIte]; exact h1_32_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      have herr : sumSqErr e3m2Quant (fun i => if i = i0 then (18 : Rat) else 1/32) =
          4 + ((B - 1 : Nat) : Rat) / 1024 := by
        unfold sumSqErr
        have hcongr : (fun i => (e3m2Quant (if i = i0 then (18 : Rat) else 1/32) -
            (if i = i0 then (18 : Rat) else 1/32)) *
            (e3m2Quant (if i = i0 then (18 : Rat) else 1/32) -
            (if i = i0 then (18 : Rat) else 1/32))) =
            (fun i => if i = i0 then (4 : Rat) else 1/1024) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, e3m2Quant_18]; grind
          · simp only [h, ↓reduceIte, e3m2Quant_1_32]
            have : (0 - 1 / 32 : Rat) * (0 - 1 / 32) = (1 / 32 : Rat) * (1 / 32) := by grind
            rw [this]; exact h1_32_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      rw [hα_eq, hsq, herr]
      have hsum_pos : (0 : Rat) < 324 + ((B - 1 : Nat) : Rat) / 1024 :=
        rat_add_pos_of_pos_of_nonneg (by decide) (rat_div_nonneg (rat_natCast_nonneg _) (by decide))
      have hd1 : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
      have heq_exact : (1 - 327680 / ((B : Rat) + 331775)) * (324 + ((B - 1 : Nat) : Rat) / 1024) =
          4 + ((B - 1 : Nat) : Rat) / 1024 := by
        rw [hBm1_eq]
        have hinv : ((B : Rat) + 331775)⁻¹ * ((B : Rat) + 331775) = 1 :=
          Rat.inv_mul_cancel _ (Rat.ne_of_gt hd1)
        have h1024 : (1024 : Rat) * (1024 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1024 (by decide)
        rw [Rat.div_def, Rat.div_def]; grind
      apply rat_lt_of_sub_pos
      have hdiff : (4 + ((B - 1 : Nat) : Rat) / 1024) -
          (1 - 327680 / ((B : Rat) + 331775) - ε) * (324 + ((B - 1 : Nat) : Rat) / 1024) =
          ε * (324 + ((B - 1 : Nat) : Rat) / 1024) := by
        rw [← heq_exact]; grind
      rw [hdiff]
      exact rat_mul_pos hε hsum_pos
  · by_cases h2 : B ≤ 7169
    · refine ⟨fun i => if i = i0 then 15 else 1/32, ?_, ⟨i0, by simp [absRat]; decide⟩, ?_⟩
      · intro i
        by_cases h : i = i0
        · simp only [h, ↓reduceIte, absRat_of_nonneg (by decide : (0 : Rat) ≤ 15)]; decide
        · simp only [h, ↓reduceIte, absRat_of_nonneg h1_32_nn]; exact h1_32_le28
      · have hα_eq : alphaMXFP6E3M2 B = 229376 / ((B : Rat) + 230399) := by
          unfold alphaMXFP6E3M2
          have hd1 : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
          have hd2 : (0 : Rat) < (B : Rat) + 230399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
          have hd3 : (0 : Rat) < (B : Rat) + 200703 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
          have hB_ge : (6145 : Rat) ≤ (B : Rat) := rat_natCast_le (m := 6145) (by omega)
          have hB_le : (B : Rat) ≤ 7169 := rat_natCast_le h2
          have h21 : 229376 / ((B : Rat) + 230399) ≤ 327680 / ((B : Rat) + 331775) := by
            apply rat_div_le_div_of_cross hd2 hd1
            apply rat_le_of_sub_nonneg
            have heq : 327680 * ((B : Rat) + 230399) - 229376 * ((B : Rat) + 331775) =
                98304 * ((B : Rat) - 6145) := by grind
            rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hB_ge)
          have h23 : 229376 / ((B : Rat) + 230399) ≤ 200704 / ((B : Rat) + 200703) := by
            apply rat_div_le_div_of_cross hd2 hd3
            apply rat_le_of_sub_nonneg
            have heq : 200704 * ((B : Rat) + 230399) - 229376 * ((B : Rat) + 200703) =
                28672 * (7169 - (B : Rat)) := by grind
            rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hB_le)
          rw [rat_min_eq_left h23, rat_min_eq_right h21]
        have hsq : sumSq (fun i => if i = i0 then (15 : Rat) else 1/32) =
            225 + ((B - 1 : Nat) : Rat) / 1024 := by
          unfold sumSq
          have hcongr : (fun i => (if i = i0 then (15 : Rat) else 1/32) *
              (if i = i0 then (15 : Rat) else 1/32)) =
              (fun i => if i = i0 then (225 : Rat) else 1/1024) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte]; grind
            · simp only [h, ↓reduceIte]; exact h1_32_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        have herr : sumSqErr e3m2Quant (fun i => if i = i0 then (15 : Rat) else 1/32) =
            1 + ((B - 1 : Nat) : Rat) / 1024 := by
          unfold sumSqErr
          have hcongr : (fun i => (e3m2Quant (if i = i0 then (15 : Rat) else 1/32) -
              (if i = i0 then (15 : Rat) else 1/32)) *
              (e3m2Quant (if i = i0 then (15 : Rat) else 1/32) -
              (if i = i0 then (15 : Rat) else 1/32))) =
              (fun i => if i = i0 then (1 : Rat) else 1/1024) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte, e3m2Quant_15]; grind
            · simp only [h, ↓reduceIte, e3m2Quant_1_32]
              have : (0 - 1 / 32 : Rat) * (0 - 1 / 32) = (1 / 32 : Rat) * (1 / 32) := by grind
              rw [this]; exact h1_32_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        rw [hα_eq, hsq, herr]
        have hsum_pos : (0 : Rat) < 225 + ((B - 1 : Nat) : Rat) / 1024 :=
          rat_add_pos_of_pos_of_nonneg (by decide) (rat_div_nonneg (rat_natCast_nonneg _) (by decide))
        have hd2 : (0 : Rat) < (B : Rat) + 230399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
        have heq_exact : (1 - 229376 / ((B : Rat) + 230399)) * (225 + ((B - 1 : Nat) : Rat) / 1024) =
            1 + ((B - 1 : Nat) : Rat) / 1024 := by
          rw [hBm1_eq]
          have hinv : ((B : Rat) + 230399)⁻¹ * ((B : Rat) + 230399) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hd2)
          have h1024 : (1024 : Rat) * (1024 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1024 (by decide)
          rw [Rat.div_def, Rat.div_def]; grind
        apply rat_lt_of_sub_pos
        have hdiff : (1 + ((B - 1 : Nat) : Rat) / 1024) -
            (1 - 229376 / ((B : Rat) + 230399) - ε) * (225 + ((B - 1 : Nat) : Rat) / 1024) =
            ε * (225 + ((B - 1 : Nat) : Rat) / 1024) := by
          rw [← heq_exact]; grind
        rw [hdiff]
        exact rat_mul_pos hε hsum_pos
    · let t : Rat := min (1/2) (ε * 196 / 29)
      have ht_pos : (0 : Rat) < t := by
        dsimp only [t]
        have h1' : (0 : Rat) < 1 / 2 := rat_div_pos_nat 1 2 (by decide) (by decide)
        have h2' : (0 : Rat) < ε * 196 / 29 := rat_div_pos (rat_mul_pos hε (by decide)) (by decide)
        change (0 : Rat) < if _ ≤ _ then _ else _
        split
        · exact h1'
        · exact h2'
      have ht_le_half : t ≤ 1/2 := rat_min_le_left _ _
      have ht_lt_1 : t < 1 := by
        have h := rat_div_lt_div_nat 1 2 1 1 (by decide) (by decide) (by decide)
        have h1' : ((1 : Nat) : Rat) / ((1 : Nat) : Rat) = 1 := rat_div_eq_int (by decide) (by grind)
        rw [h1'] at h
        exact rat_lt_of_le_of_lt ht_le_half h
      have ht_le_eps : t ≤ ε * 196 / 29 := rat_min_le_right _ _
      refine ⟨fun i => if i = i0 then 14 + t else 1/32, ?_, ?_, ?_⟩
      · intro i
        by_cases h : i = i0
        · simp only [h, ↓reduceIte]
          have hpos : (0 : Rat) ≤ 14 + t := rat_add_nonneg (by decide) (Rat.le_of_lt ht_pos)
          rw [absRat_of_nonneg hpos]
          have h15 : (14 : Rat) + 1 = 15 := by grind
          exact Rat.le_trans (rat_add_le_add (Rat.le_refl (a := (14 : Rat))) (Rat.le_of_lt ht_lt_1)) (by rw [h15]; decide)
        · simp only [h, ↓reduceIte, absRat_of_nonneg h1_32_nn]; exact h1_32_le28
      · refine ⟨i0, ?_⟩
        simp only [↓reduceIte]
        have hpos : (0 : Rat) ≤ 14 + t := rat_add_nonneg (by decide) (Rat.le_of_lt ht_pos)
        rw [absRat_of_nonneg hpos]
        apply rat_lt_of_sub_pos; grind
      · have hd1 : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
        have hd2 : (0 : Rat) < (B : Rat) + 230399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
        have hd3 : (0 : Rat) < (B : Rat) + 200703 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
        have hα_eq : alphaMXFP6E3M2 B = 200704 / ((B : Rat) + 200703) := by
          unfold alphaMXFP6E3M2
          have hB_ge : (7169 : Rat) ≤ (B : Rat) := rat_natCast_le (m := 7169) (by omega)
          have h32 : 200704 / ((B : Rat) + 200703) ≤ 229376 / ((B : Rat) + 230399) := by
            apply rat_div_le_div_of_cross hd3 hd2; apply rat_le_of_sub_nonneg
            have heq : 229376 * ((B : Rat) + 200703) - 200704 * ((B : Rat) + 230399) =
                28672 * ((B : Rat) - 7169) := by grind
            rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hB_ge)
          have h31 : 200704 / ((B : Rat) + 200703) ≤ 327680 / ((B : Rat) + 331775) := by
            apply rat_div_le_div_of_cross hd3 hd1; apply rat_le_of_sub_nonneg
            have heq : 327680 * ((B : Rat) + 200703) - 200704 * ((B : Rat) + 331775) =
                126976 * ((B : Rat) - 7169) + 88080384 := by grind
            rw [heq]; exact rat_add_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB_ge)) (by decide)
          rw [rat_min_eq_right h32, rat_min_eq_right h31]
        let δ3 : Rat := 1 - 200704 / ((B : Rat) + 200703)
        have hsq : sumSq (fun i => if i = i0 then (14 + t : Rat) else 1/32) =
            (14 + t) * (14 + t) + ((B - 1 : Nat) : Rat) / 1024 := by
          unfold sumSq
          have hcongr : (fun i => (if i = i0 then (14 + t : Rat) else 1/32) *
              (if i = i0 then (14 + t : Rat) else 1/32)) =
              (fun i => if i = i0 then (14 + t) * (14 + t) else 1/1024) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte]
            · simp only [h, ↓reduceIte]; exact h1_32_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        have herr : sumSqErr e3m2Quant (fun i => if i = i0 then (14 + t : Rat) else 1/32) =
            t * t + ((B - 1 : Nat) : Rat) / 1024 := by
          unfold sumSqErr
          have hcongr : (fun i => (e3m2Quant (if i = i0 then (14 + t : Rat) else 1/32) -
              (if i = i0 then (14 + t : Rat) else 1/32)) *
              (e3m2Quant (if i = i0 then (14 + t : Rat) else 1/32) -
              (if i = i0 then (14 + t : Rat) else 1/32))) =
              (fun i => if i = i0 then t * t else 1/1024) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte, e3m2Quant_14_plus ht_pos ht_lt_1]; grind
            · simp only [h, ↓reduceIte, e3m2Quant_1_32]
              have : (0 - 1 / 32 : Rat) * (0 - 1 / 32) = (1 / 32 : Rat) * (1 / 32) := by grind
              rw [this]; exact h1_32_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        rw [hα_eq, hsq, herr]
        have hδ3_exact : δ3 * (196 + ((B - 1 : Nat) : Rat) / 1024) = ((B - 1 : Nat) : Rat) / 1024 := by
          dsimp only [δ3]; rw [hBm1_eq]
          have hinv : ((B : Rat) + 200703)⁻¹ * ((B : Rat) + 200703) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hd3)
          have h1024 : (1024 : Rat) * (1024 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1024 (by decide)
          rw [Rat.div_def, Rat.div_def]; grind
        have hδ3_lt1 : δ3 < 1 := by
          dsimp only [δ3]
          apply rat_lt_of_sub_pos
          have heq : (1 : Rat) - (1 - 200704 / ((B : Rat) + 200703)) = 200704 / ((B : Rat) + 200703) := by grind
          rw [heq]; exact rat_div_pos (by decide) hd3
        have h28t : (28 * t + t * t) < 29 * t := by
          apply rat_lt_of_sub_pos
          have heq : 29 * t - (28 * t + t * t) = t * (1 - t) := by grind
          rw [heq]; exact rat_mul_pos ht_pos (rat_sub_pos ht_lt_1)
        have h29t_le : 29 * t ≤ ε * 196 := by
          have hmul := rat_mul_le_mul_of_nonneg_left ht_le_eps (by decide : (0 : Rat) ≤ 29)
          have hcancel : (29 : Rat) * (ε * 196 / 29) = ε * 196 := by
            rw [Rat.div_def, Rat.mul_comm (ε * 196), ← Rat.mul_assoc]
            have h29 : (29 : Rat) * (29 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 29 (by decide)
            rw [h29, Rat.one_mul]
          rw [hcancel] at hmul; exact hmul
        have hstep1 : δ3 * (28 * t + t * t) < ε * ((14 + t) * (14 + t) + ((B - 1 : Nat) : Rat) / 1024) := by
          have hpos_dt : (0 : Rat) < 28 * t + t * t :=
            rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) ht_pos) (rat_sq_nonneg t)
          have ha : δ3 * (28 * t + t * t) < 1 * (28 * t + t * t) :=
            rat_mul_lt_mul_of_pos_right hδ3_lt1 hpos_dt
          have hb : 1 * (28 * t + t * t) < 29 * t := by rw [Rat.one_mul]; exact h28t
          have hc : ε * 196 ≤ ε * ((14 + t) * (14 + t) + ((B - 1 : Nat) : Rat) / 1024) := by
            apply rat_mul_le_mul_of_nonneg_left _ (Rat.le_of_lt hε)
            apply rat_le_of_sub_nonneg
            have heq : (14 + t) * (14 + t) + ((B - 1 : Nat) : Rat) / 1024 - 196 =
                (28 * t + t * t) + ((B - 1 : Nat) : Rat) / 1024 := by grind
            rw [heq]
            exact rat_add_nonneg (Rat.le_of_lt hpos_dt) (rat_div_nonneg (rat_natCast_nonneg _) (by decide))
          exact rat_lt_of_lt_of_le (rat_lt_trans ha hb) (Rat.le_trans h29t_le hc)
        apply rat_lt_of_sub_pos
        have hsub := rat_sub_pos hstep1
        have heq : (t * t + ((B - 1 : Nat) : Rat) / 1024) -
            (1 - 200704 / ((B : Rat) + 200703) - ε) * ((14 + t) * (14 + t) + ((B - 1 : Nat) : Rat) / 1024) =
            t * t + (ε * ((14 + t) * (14 + t) + ((B - 1 : Nat) : Rat) / 1024) - δ3 * (28 * t + t * t)) := by
          dsimp only [δ3] at hδ3_exact ⊢
          rw [← hδ3_exact]; grind
        rw [heq]
        exact rat_add_pos_of_pos_of_nonneg (rat_mul_pos ht_pos ht_pos) (Rat.le_of_lt hsub)

/-! #### NVFP6-E3M2 Upper Bound & Exact Attainment -/

private theorem nvfp6_e3m2_upper_bound (B : Nat) (hB : 0 < B) (y : Fin B → Rat)
    (hmax : ∀ i, absRat (y i) ≤ 28)
    (hanc : ∃ i0, absRat (y i0) = 28) :
    sumSqErr e3m2Quant y ≤ (1 - alphaNVFP6E3M2 B) * sumSq y := by
  let α := alphaNVFP6E3M2 B
  rcases hanc with ⟨i0, hi0⟩
  by_cases hB1 : B = 1
  · subst hB1
    have h0 : i0 = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst h0
    have herr0 : sumSqErr e3m2Quant y = 0 := by
      unfold sumSqErr sumFinRat sumFinRat
      have he : (e3m2Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) *
          (e3m2Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) = 0 := by
        unfold e3m2Quant; rw [symQuant_sq_err_abs, hi0]
        have hq : nearestNonneg e3m2Levels 28 = 28 := by
          have := e3m2Quant_28
          unfold e3m2Quant symQuant at this
          have hn : ¬((28 : Rat) < 0) := by decide
          simp only [hn, ↓reduceIte] at this; exact this
        rw [hq]; grind
      change (0 : Rat) + (e3m2Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) *
          (e3m2Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) = 0
      rw [he]; grind
    have hα_le1 : α ≤ 1 := by
      have h1 : α ≤ (80 * ((1 : Nat) : Rat) + 116) / (81 * ((1 : Nat) : Rat) + 115) :=
        rat_min_le_left _ _
      have heq : (80 * ((1 : Nat) : Rat) + 116) / (81 * ((1 : Nat) : Rat) + 115) = 1 :=
        rat_div_eq_int (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (by decide)) (by decide))) (by grind)
      rw [heq] at h1; exact h1
    have hsum_nonneg : (0 : Rat) ≤ sumSq y := by
      unfold sumSq sumFinRat sumFinRat
      have hsq := rat_sq_nonneg (y ⟨0, by omega⟩)
      change (0 : Rat) ≤ 0 + _
      rw [Rat.zero_add]; exact hsq
    rw [herr0]
    exact Rat.mul_nonneg (rat_sub_nonneg hα_le1) hsum_nonneg
  · have hB2 : 2 ≤ B := by omega
    have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
      have := rat_natCast_sub hB; simpa using this
    have hBm1_pos : (0 : Rat) < ((B - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
    have hα_pos : (0 : Rat) < α := by
      dsimp only [α]
      unfold alphaNVFP6E3M2
      have h1 : (0 : Rat) < (80 * (B : Rat) + 116) / (81 * (B : Rat) + 115) :=
        rat_div_pos (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide))
          (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide))
      have h2 : (0 : Rat) < 802816 / ((B : Rat) + 802815) :=
        rat_div_pos (by decide) (rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide))
      change (0 : Rat) < if _ ≤ _ then _ else _
      split <;> assumption
    have hα1 : α ≤ (80 * (B : Rat) + 116) / (81 * (B : Rat) + 115) := rat_min_le_left _ _
    have hα2 : α ≤ 802816 / ((B : Rat) + 802815) := rat_min_le_right _ _
    have hδ_nonneg : (0 : Rat) ≤ 1 - α := by
      have hd : (0 : Rat) < (B : Rat) + 802815 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
      have hle1 : 802816 / ((B : Rat) + 802815) ≤ 1 := by
        apply rat_div_le_of_mul_le hd
        have hB1 : (1 : Rat) ≤ (B : Rat) := rat_natCast_le hB
        have hsub := rat_sub_nonneg hB1
        apply rat_le_of_sub_nonneg; grind
      exact rat_sub_nonneg (Rat.le_trans hα2 hle1)
    let C : Rat := (1 - α) * (28 * 28) / ((B - 1 : Nat) : Rat)
    have hC_nonneg : (0 : Rat) ≤ C :=
      rat_div_nonneg (Rat.mul_nonneg hδ_nonneg (rat_sq_nonneg 28)) hBm1_pos
    have hα_unit : α * (4 * ((16 : Nat) : Rat) * ((16 : Nat) : Rat) * (28 * 28) + ((B - 1 : Nat) : Rat)) ≤
        4 * ((16 : Nat) : Rat) * ((16 : Nat) : Rat) * (28 * 28) := by
      have hd : (0 : Rat) < (B : Rat) + 802815 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
      have hmul := rat_mul_le_mul_of_nonneg_right hα2 (Rat.le_of_lt hd)
      have hcancel : 802816 / ((B : Rat) + 802815) * ((B : Rat) + 802815) = 802816 := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
      rw [hcancel] at hmul
      rw [hBm1_eq]
      have heq1 : (4 : Rat) * ((16 : Nat) : Rat) * ((16 : Nat) : Rat) * (28 * 28) = 802816 := by grind
      rw [heq1]
      have heq2 : (802816 : Rat) + ((B : Rat) - 1) = (B : Rat) + 802815 := by grind
      rw [heq2]; exact hmul
    have hα_ratio : ((B - 1 : Nat) : Rat) *
        ((((64 : Nat) : Rat) / (2 * ((16 : Nat) : Rat))) * (((64 : Nat) : Rat) / (2 * ((16 : Nat) : Rat)))) ≤
        (1 - α) * (28 * 28 + ((B - 1 : Nat) : Rat) *
          ((((9 : Nat) : Rat) * (((64 : Nat) : Rat) / (2 * ((16 : Nat) : Rat)))) *
           (((9 : Nat) : Rat) * (((64 : Nat) : Rat) / (2 * ((16 : Nat) : Rat)))))) := by
      have hd : (0 : Rat) < 81 * (B : Rat) + 115 :=
        rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide)
      have hmul := rat_mul_le_mul_of_nonneg_right hα1 (Rat.le_of_lt hd)
      have hcancel : (80 * (B : Rat) + 116) / (81 * (B : Rat) + 115) * (81 * (B : Rat) + 115) =
          80 * (B : Rat) + 116 := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
      rw [hcancel] at hmul
      have hsub := rat_sub_nonneg hmul
      apply rat_le_of_sub_nonneg
      rw [hBm1_eq]
      have hsimp1 : ((64 : Nat) : Rat) / (2 * ((16 : Nat) : Rat)) = 2 :=
        rat_div_eq_int (Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))) (by grind)
      have hsimp2 : ((9 : Nat) : Rat) = 9 := rfl
      rw [hsimp1, hsimp2]
      have heq : (1 - α) * (28 * 28 + ((B : Rat) - 1) * (9 * 2 * (9 * 2))) - ((B : Rat) - 1) * (2 * 2) =
          4 * ((80 * (B : Rat) + 116) - α * (81 * (B : Rat) + 115)) := by grind
      rw [heq]; exact Rat.mul_nonneg (by decide) hsub
    have hnonanc : ∀ i : Fin B,
        (e3m2Quant (y i) - y i) * (e3m2Quant (y i) - y i) - (1 - α) * (y i * y i) ≤ C := by
      intro i
      rw [← absRat_sq (y i)]
      unfold e3m2Quant
      rw [symQuant_sq_err_abs]
      have hsort : isSorted e3m2Levels := by
        rw [e3m2Levels_eq_map]
        exact isSorted_map_div (by decide) 64 9 e3m2Nums check_e3m2Nums
      have hgb : gridQuadBound α C e3m2Levels := by
        rw [e3m2Levels_eq_map]
        apply gridQuadBound_of_check (D := 16) (maxGap := 64) (ratio := 9) hδ_nonneg hC_nonneg
        · intro a b hab hba hs
          exact unit_step_nvfp (D := 16) (by decide) hB2 hδ_nonneg hα_unit a b hab hba hs
        · intro a b hab hgap hbr
          exact ratio_step_nvfp (D := 16) (maxGap := 64) (ratio := 9) (by decide) (by decide) hB2 hα_ratio a b hab hgap hbr
        · exact check_e3m2Nums
      have hy0 : (0 : Rat) ≤ absRat (y i) := absRat_nonneg (y i)
      have hy28 : absRat (y i) ≤ lastLevel e3m2Levels := by
        have hlast : lastLevel e3m2Levels = 28 := rfl
        rw [hlast]; exact hmax i
      exact nearestNonneg_quad_le (Rat.le_of_lt hα_pos) e3m2Levels hsort hgb 0 e3m2Levels.tail rfl (absRat (y i)) hy0 hy28
    have hanc_bd : (e3m2Quant (y i0) - y i0) * (e3m2Quant (y i0) - y i0) - (1 - α) * (y i0 * y i0) ≤
        -(1 - α) * (28 * 28) := by
      rw [← absRat_sq (y i0)]
      unfold e3m2Quant; rw [symQuant_sq_err_abs, hi0]
      have hq : nearestNonneg e3m2Levels 28 = 28 := by
        have := e3m2Quant_28
        unfold e3m2Quant symQuant at this
        have hn : ¬((28 : Rat) < 0) := by decide
        simp only [hn, ↓reduceIte] at this; exact this
      rw [hq]
      have heq : (28 - 28 : Rat) * (28 - 28) - (1 - α) * (28 * 28) = -(1 - α) * (28 * 28) := by grind
      rw [heq]; exact Rat.le_refl
    have hsum := sumFinRat_le_anchor i0
      (fun i => (e3m2Quant (y i) - y i) * (e3m2Quant (y i) - y i) - (1 - α) * (y i * y i))
      (-(1 - α) * (28 * 28)) C hanc_bd (fun i _ => hnonanc i)
    have hzero : -(1 - α) * (28 * 28) + ((B - 1 : Nat) : Rat) * C = 0 := by
      dsimp only [C]
      have hne : ((B - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hBm1_pos
      have hmul : ((B - 1 : Nat) : Rat) * ((1 - α) * (28 * 28) / ((B - 1 : Nat) : Rat)) =
          (1 - α) * (28 * 28) := by
        rw [Rat.div_def, Rat.mul_comm ((1 - α) * (28 * 28)), ← Rat.mul_assoc,
            Rat.mul_comm ((B - 1 : Nat) : Rat), Rat.inv_mul_cancel _ hne, Rat.one_mul]
      rw [hmul]; grind
    rw [hzero, sumFinRat_sub, sumFinRat_mul_left] at hsum
    exact rat_le_of_sub_nonneg (by
      have h := rat_sub_nonneg hsum
      have heq : (1 - α) * sumSq y - sumSqErr e3m2Quant y =
          0 - (sumFinRat B (fun i => (e3m2Quant (y i) - y i) * (e3m2Quant (y i) - y i)) -
               (1 - α) * sumFinRat B (fun i => y i * y i)) := by
        unfold sumSq sumSqErr; grind
      rw [heq]; exact h)

private theorem nvfp6_e3m2_attained (B : Nat) (hB : 0 < B) :
    ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 28) ∧
      (∃ i0, absRat (y i0) = 28) ∧
      sumSqErr e3m2Quant y = (1 - alphaNVFP6E3M2 B) * sumSq y := by
  let i0 : Fin B := ⟨0, hB⟩
  have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
    have := rat_natCast_sub hB; simpa using this
  have hd1 : (0 : Rat) < 81 * (B : Rat) + 115 :=
    rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide)
  have hd2 : (0 : Rat) < (B : Rat) + 802815 :=
    rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have h1_32_nn : (0 : Rat) ≤ (1 : Rat) / 32 := rat_div_nonneg_nat 1 32 (by decide)
  have h1_32_le28 : (1 : Rat) / 32 ≤ 28 := by
    have h := rat_div_le_div_nat 1 32 28 1 (by decide) (by decide) (by decide)
    have h28 : ((28 : Nat) : Rat) / ((1 : Nat) : Rat) = 28 := rat_div_eq_int (by decide) (by grind)
    rw [h28] at h; exact h
  have h1_32_sq : (1 / 32 : Rat) * (1 / 32) = 1 / 1024 := by
    have h32ne : (32 : Rat) * 32 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
    have h1 : (1 / 32 : Rat) * (1 / 32) = 1 / (32 * 32) := by
      rw [Rat.div_def]
      have hmul : ((32 * 32 : Rat)⁻¹ - (32 : Rat)⁻¹ * (32 : Rat)⁻¹) * (32 * 32) = 0 := by
        have h32 : (32 : Rat)⁻¹ * 32 = 1 := Rat.inv_mul_cancel 32 (by decide)
        have h1024 : (32 * 32 : Rat)⁻¹ * (32 * 32) = 1 := Rat.inv_mul_cancel _ h32ne
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim (h32ne h0)
    rw [h1]; exact rat_div_eq_of_cross h32ne (by decide) (by grind)
  by_cases h1 : B ≤ 10033
  · refine ⟨fun i => if i = i0 then 28 else 18, ?_, ⟨i0, by simp [absRat]; decide⟩, ?_⟩
    · intro i
      by_cases h : i = i0
      · simp only [h, ↓reduceIte, absRat_of_nonneg (by decide : (0 : Rat) ≤ 28)]; decide
      · simp only [h, ↓reduceIte, absRat_of_nonneg (by decide : (0 : Rat) ≤ 18)]; decide
    · have hα_eq : alphaNVFP6E3M2 B = (80 * (B : Rat) + 116) / (81 * (B : Rat) + 115) := by
        unfold alphaNVFP6E3M2
        apply rat_min_eq_left
        apply rat_div_le_div_of_cross hd1 hd2
        apply rat_le_of_sub_nonneg
        have hB1 : (1 : Rat) ≤ (B : Rat) := rat_natCast_le hB
        have hBle : (B : Rat) ≤ 10033 := rat_natCast_le h1
        have heq : 802816 * (81 * (B : Rat) + 115) - (80 * (B : Rat) + 116) * ((B : Rat) + 802815) =
            80 * ((B : Rat) - 1) * (10033 - (B : Rat)) + 60 * ((B : Rat) - 1) := by grind
        rw [heq]
        exact rat_add_nonneg
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB1)) (rat_sub_nonneg hBle))
          (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB1))
      have hsq : sumSq (fun i => if i = i0 then (28 : Rat) else 18) =
          784 + ((B - 1 : Nat) : Rat) * 324 := by
        unfold sumSq
        have hcongr : (fun i => (if i = i0 then (28 : Rat) else 18) *
            (if i = i0 then (28 : Rat) else 18)) =
            (fun i => if i = i0 then (784 : Rat) else 324) := by
          funext i; by_cases h : i = i0 <;> simp only [h, ↓reduceIte] <;> grind
        rw [hcongr, sumFinRat_single]
      have herr : sumSqErr e3m2Quant (fun i => if i = i0 then (28 : Rat) else 18) =
          0 + ((B - 1 : Nat) : Rat) * 4 := by
        unfold sumSqErr
        have hcongr : (fun i => (e3m2Quant (if i = i0 then (28 : Rat) else 18) -
            (if i = i0 then (28 : Rat) else 18)) *
            (e3m2Quant (if i = i0 then (28 : Rat) else 18) -
            (if i = i0 then (28 : Rat) else 18))) =
            (fun i => if i = i0 then (0 : Rat) else 4) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, e3m2Quant_28]; grind
          · simp only [h, ↓reduceIte, e3m2Quant_18]; grind
        rw [hcongr, sumFinRat_single]
      rw [hα_eq, hsq, herr, hBm1_eq]
      have hinv : (81 * (B : Rat) + 115)⁻¹ * (81 * (B : Rat) + 115) = 1 :=
        Rat.inv_mul_cancel _ (Rat.ne_of_gt hd1)
      rw [Rat.div_def]; grind
  · refine ⟨fun i => if i = i0 then 28 else 1/32, ?_, ⟨i0, by simp [absRat]; decide⟩, ?_⟩
    · intro i
      by_cases h : i = i0
      · simp only [h, ↓reduceIte, absRat_of_nonneg (by decide : (0 : Rat) ≤ 28)]; decide
      · simp only [h, ↓reduceIte, absRat_of_nonneg h1_32_nn]; exact h1_32_le28
    · have hα_eq : alphaNVFP6E3M2 B = 802816 / ((B : Rat) + 802815) := by
        unfold alphaNVFP6E3M2
        apply rat_min_eq_right
        apply rat_div_le_div_of_cross hd2 hd1
        apply rat_le_of_sub_nonneg
        have hBge : (10034 : Rat) ≤ (B : Rat) := rat_natCast_le (m := 10034) (by omega)
        have heq : (80 * (B : Rat) + 116) * ((B : Rat) + 802815) - 802816 * (81 * (B : Rat) + 115) =
            80 * ((B : Rat) - 10034) * ((B : Rat) - 10034) + 802660 * ((B : Rat) - 10034) + 200660 := by grind
        rw [heq]
        exact rat_add_nonneg
          (rat_add_nonneg
            (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge)) (rat_sub_nonneg hBge))
            (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge)))
          (by decide)
      have hsq : sumSq (fun i => if i = i0 then (28 : Rat) else 1/32) =
          784 + ((B - 1 : Nat) : Rat) / 1024 := by
        unfold sumSq
        have hcongr : (fun i => (if i = i0 then (28 : Rat) else 1/32) *
            (if i = i0 then (28 : Rat) else 1/32)) =
            (fun i => if i = i0 then (784 : Rat) else 1/1024) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte]; grind
          · simp only [h, ↓reduceIte]; exact h1_32_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      have herr : sumSqErr e3m2Quant (fun i => if i = i0 then (28 : Rat) else 1/32) =
          0 + ((B - 1 : Nat) : Rat) / 1024 := by
        unfold sumSqErr
        have hcongr : (fun i => (e3m2Quant (if i = i0 then (28 : Rat) else 1/32) -
            (if i = i0 then (28 : Rat) else 1/32)) *
            (e3m2Quant (if i = i0 then (28 : Rat) else 1/32) -
            (if i = i0 then (28 : Rat) else 1/32))) =
            (fun i => if i = i0 then (0 : Rat) else 1/1024) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, e3m2Quant_28]; grind
          · simp only [h, ↓reduceIte, e3m2Quant_1_32]
            have : (0 - 1 / 32 : Rat) * (0 - 1 / 32) = (1 / 32 : Rat) * (1 / 32) := by grind
            rw [this]; exact h1_32_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      rw [hα_eq, hsq, herr, hBm1_eq]
      have hinv : ((B : Rat) + 802815)⁻¹ * ((B : Rat) + 802815) = 1 :=
        Rat.inv_mul_cancel _ (Rat.ne_of_gt hd2)
      have h1024 : (1024 : Rat) * (1024 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 1024 (by decide)
      rw [Rat.div_def, Rat.div_def]; grind

/-- Theorem 1: Universal all-`B` EF21 contraction law for `MXFP6-E3M2` and `NVFP6-E3M2`. -/
theorem mxfp6_e3m2_nvfp6_ef21_universal (B : Nat) (hB : 0 < B) :
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 28) → (∃ i0, (14 : Rat) < absRat (y i0)) →
      sumSqErr e3m2Quant y ≤ (1 - alphaMXFP6E3M2 B) * sumSq y) ∧
    (∀ ε : Rat, (0 : Rat) < ε → ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 28) ∧ (∃ i0, (14 : Rat) < absRat (y i0)) ∧
      (1 - alphaMXFP6E3M2 B - ε) * sumSq y < sumSqErr e3m2Quant y) ∧
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 28) → (∃ i0, absRat (y i0) = 28) →
      sumSqErr e3m2Quant y ≤ (1 - alphaNVFP6E3M2 B) * sumSq y) ∧
    (∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 28) ∧ (∃ i0, absRat (y i0) = 28) ∧
      sumSqErr e3m2Quant y = (1 - alphaNVFP6E3M2 B) * sumSq y) :=
  ⟨mxfp6_e3m2_upper_bound B hB, mxfp6_e3m2_tight B hB,
   nvfp6_e3m2_upper_bound B hB, nvfp6_e3m2_attained B hB⟩

/-! ### 5. Theorem 2: Universal All-`B` EF21 Contraction for `MXFP6-E2M3` and `NVFP6-E2M3` -/

private theorem alphaMXFP6E2M3_pos {B : Nat} (hB : 0 < B) : (0 : Rat) < alphaMXFP6E2M3 B := by
  unfold alphaMXFP6E2M3
  have hd1 : (0 : Rat) < (B : Rat) + 4623 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have hd2 : (0 : Rat) < (B : Rat) + 3843 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have hd3 : (0 : Rat) < (B : Rat) + 3599 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have h1 : (0 : Rat) < 4608 / ((B : Rat) + 4623) := rat_div_pos (by decide) hd1
  have h2 : (0 : Rat) < 3840 / ((B : Rat) + 3843) := rat_div_pos (by decide) hd2
  have h3 : (0 : Rat) < 3600 / ((B : Rat) + 3599) := rat_div_pos (by decide) hd3
  have hmin2 : (0 : Rat) < min (3840 / ((B : Rat) + 3843)) (3600 / ((B : Rat) + 3599)) := by
    change (0 : Rat) < if _ ≤ _ then _ else _
    split <;> assumption
  change (0 : Rat) < if _ ≤ _ then _ else _
  split <;> assumption

private theorem alphaMXFP6E2M3_le_288_289 {B : Nat} (hB : 0 < B) :
    alphaMXFP6E2M3 B ≤ (288 : Rat) / 289 := by
  have h1 : alphaMXFP6E2M3 B ≤ 4608 / ((B : Rat) + 4623) := rat_min_le_left _ _
  have hd : (0 : Rat) < (B : Rat) + 4623 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have h2 : 4608 / ((B : Rat) + 4623) ≤ (288 : Rat) / 289 := by
    apply rat_div_le_div_of_cross hd (by decide)
    have hB1 : (1 : Rat) ≤ (B : Rat) := rat_natCast_le hB
    have hsub := rat_sub_nonneg hB1
    apply rat_le_of_sub_nonneg
    have heq : (288 : Rat) * ((B : Rat) + 4623) - 4608 * 289 = 288 * ((B : Rat) - 1) := by grind
    rw [heq]; exact Rat.mul_nonneg (by decide) hsub
  exact Rat.le_trans h1 h2

private theorem rat_div_sq (a b : Rat) (hb : b ≠ 0) :
    (a / b) * (a / b) = (a * a) / (b * b) := by
  have hb2 : b * b ≠ 0 := fun h => by
    cases Rat.mul_eq_zero.mp h with | inl h0 => exact hb h0 | inr h0 => exact hb h0
  rw [Rat.div_def, Rat.div_def]
  have hinv : (b * b)⁻¹ = b⁻¹ * b⁻¹ := by
    have hmul : ((b * b)⁻¹ - b⁻¹ * b⁻¹) * (b * b) = 0 := by
      have h1 : b⁻¹ * b = 1 := Rat.inv_mul_cancel b hb
      have h2 : (b * b)⁻¹ * (b * b) = 1 := Rat.inv_mul_cancel (b * b) hb2
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr h0 => exact False.elim (hb2 h0)
  rw [hinv]; grind

private theorem mxfp6_e2m3_upper_bound (B : Nat) (hB : 0 < B) (y : Fin B → Rat)
    (hmax : ∀ i, absRat (y i) ≤ 15/2)
    (hanc : ∃ i0, (15/4 : Rat) < absRat (y i0)) :
    sumSqErr e2m3Quant y ≤ (1 - alphaMXFP6E2M3 B) * sumSq y := by
  let α := alphaMXFP6E2M3 B
  have hα_pos : (0 : Rat) < α := alphaMXFP6E2M3_pos hB
  have hα_nonneg : (0 : Rat) ≤ α := Rat.le_of_lt hα_pos
  have hα_bd : α ≤ (288 : Rat) / 289 := alphaMXFP6E2M3_le_288_289 hB
  have hδ_ge : (1 : Rat) ≤ (17 : Rat) * 17 * (1 - α) := by
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hα_bd
    have heq : (17 : Rat) * 17 * (1 - α) - 1 = 289 * ((288 : Rat) / 289 - α) := by
      have h289 : (289 : Rat) * (289 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 289 (by decide)
      rw [Rat.div_def]; grind
    rw [heq]; exact Rat.mul_nonneg (by decide) hsub
  have hδ_nonneg : (0 : Rat) ≤ 1 - α := by
    have h1 : (288 : Rat) / 289 ≤ 1 := by
      have h := rat_div_le_div_nat 288 289 1 1 (by decide) (by decide) (by decide)
      have h1' : ((1 : Nat) : Rat) / ((1 : Nat) : Rat) = 1 := rat_div_eq_int (by decide) (by grind)
      rw [h1'] at h; exact h
    exact rat_sub_nonneg (Rat.le_trans hα_bd h1)
  let C : Rat := α / 256
  have hC_nonneg : (0 : Rat) ≤ C := rat_div_nonneg hα_nonneg (by decide)
  have hnonanc : ∀ i : Fin B,
      (e2m3Quant (y i) - y i) * (e2m3Quant (y i) - y i) - (1 - α) * (y i * y i) ≤ C := by
    intro i
    rw [← absRat_sq (y i)]
    unfold e2m3Quant
    rw [symQuant_sq_err_abs]
    have hsort : isSorted e2m3Levels := by
      rw [e2m3Levels_eq_map]
      exact isSorted_map_div (by decide) 4 17 e2m3Nums check_e2m3Nums
    have hgb : gridQuadBound α C e2m3Levels := by
      rw [e2m3Levels_eq_map]
      apply gridQuadBound_of_check (D := 8) (maxGap := 4) (ratio := 17) hδ_nonneg hC_nonneg
      · intro a b hab hba hs
        have hu := unit_step_mxfp (D := 8) (by decide) hδ_nonneg a b hab hba hs
        have h256 : (4 : Rat) * ((8 : Nat) : Rat) * ((8 : Nat) : Rat) = 256 := by grind
        rw [h256] at hu; exact hu
      · intro a b hab _ hbr
        exact ratio_step_mxfp (D := 8) (ratio := 17) (by decide) (by decide) hC_nonneg hδ_ge a b hab hbr
      · exact check_e2m3Nums
    have hy0 : (0 : Rat) ≤ absRat (y i) := absRat_nonneg (y i)
    have hy152 : absRat (y i) ≤ lastLevel e2m3Levels := by
      have hlast : lastLevel e2m3Levels = 15/2 := rfl
      rw [hlast]; exact hmax i
    exact nearestNonneg_quad_le hα_nonneg e2m3Levels hsort hgb 0 e2m3Levels.tail rfl (absRat (y i)) hy0 hy152
  rcases hanc with ⟨i0, hi0⟩
  let A : Rat := -(((B - 1 : Nat) : Rat) * C)
  have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
    have := rat_natCast_sub hB; simpa using this
  have hα1 : α ≤ 4608 / ((B : Rat) + 4623) := rat_min_le_left _ _
  have hα2 : α ≤ 3840 / ((B : Rat) + 3843) :=
    Rat.le_trans (rat_min_le_right _ _) (rat_min_le_left _ _)
  have hα3 : α ≤ 3600 / ((B : Rat) + 3599) :=
    Rat.le_trans (rat_min_le_right _ _) (rat_min_le_right _ _)
  have h256 : (256 : Rat) * (256 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 256 (by decide)
  have h44 : (4 : Rat) * 4 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h88 : (8 : Rat) * 8 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have hpt154 : -(1 - α) * ((15/4 : Rat) * (15/4)) ≤ A := by
    have hd : (0 : Rat) < (B : Rat) + 3599 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
    have hmul := rat_mul_le_mul_of_nonneg_right hα3 (Rat.le_of_lt hd)
    have hcancel : 3600 / ((B : Rat) + 3599) * ((B : Rat) + 3599) = 3600 := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
    rw [hcancel] at hmul
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hmul
    have heq : A - -(1 - α) * ((15/4 : Rat) * (15/4)) = (3600 - α * ((B : Rat) + 3599)) / 256 := by
      dsimp only [A, C]; rw [hBm1_eq, rat_div_sq 15 4 (by decide)]
      have h16_256 : ((15 : Rat) * 15) / (4 * 4) = 3600 / 256 :=
        rat_div_eq_of_cross h44 (by decide) (by grind)
      rw [h16_256, Rat.div_def, Rat.div_def, Rat.div_def]; grind
    rw [heq]; exact rat_div_nonneg hsub (by decide)
  have hmid318 : ((4 - 15/4 : Rat) / 2) * ((4 - 15/4 : Rat) / 2) -
      (1 - α) * (((15/4 + 4 : Rat) / 2) * ((15/4 + 4 : Rat) / 2)) ≤ A := by
    have hd : (0 : Rat) < (B : Rat) + 3843 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
    have hmul := rat_mul_le_mul_of_nonneg_right hα2 (Rat.le_of_lt hd)
    have hcancel : 3840 / ((B : Rat) + 3843) * ((B : Rat) + 3843) = 3840 := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
    rw [hcancel] at hmul
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hmul
    have h1 : (4 - 15/4 : Rat) / 2 = 1 / 8 := by
      have h4 : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
      apply rat_div_eq_of_cross (by decide) (by decide); rw [Rat.div_def]; grind
    have h2 : (15/4 + 4 : Rat) / 2 = 31 / 8 := by
      have h4 : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
      apply rat_div_eq_of_cross (by decide) (by decide); rw [Rat.div_def]; grind
    rw [h1, h2, rat_div_sq 1 8 (by decide), rat_div_sq 31 8 (by decide)]
    have h1_64 : (1 * 1 : Rat) / (8 * 8) = 4 / 256 := rat_div_eq_of_cross h88 (by decide) (by grind)
    have h31_64 : (31 * 31 : Rat) / (8 * 8) = 3844 / 256 := rat_div_eq_of_cross h88 (by decide) (by grind)
    rw [h1_64, h31_64]
    have heq : A - (4 / 256 - (1 - α) * (3844 / 256)) = (3840 - α * ((B : Rat) + 3843)) / 256 := by
      dsimp only [A, C]; rw [hBm1_eq, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]; grind
    rw [heq]; exact rat_div_nonneg hsub (by decide)
  have hmid174 : ((9/2 - 4 : Rat) / 2) * ((9/2 - 4 : Rat) / 2) -
      (1 - α) * (((4 + 9/2 : Rat) / 2) * ((4 + 9/2 : Rat) / 2)) ≤ A := by
    have hd : (0 : Rat) < (B : Rat) + 4623 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
    have hmul := rat_mul_le_mul_of_nonneg_right hα1 (Rat.le_of_lt hd)
    have hcancel : 4608 / ((B : Rat) + 4623) * ((B : Rat) + 4623) = 4608 := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
    rw [hcancel] at hmul
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg hmul
    have h1 : (9/2 - 4 : Rat) / 2 = 1 / 4 := by
      have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
      apply rat_div_eq_of_cross (by decide) (by decide); rw [Rat.div_def]; grind
    have h2 : (4 + 9/2 : Rat) / 2 = 17 / 4 := by
      have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
      apply rat_div_eq_of_cross (by decide) (by decide); rw [Rat.div_def]; grind
    rw [h1, h2, rat_div_sq 1 4 (by decide), rat_div_sq 17 4 (by decide)]
    have h1_16 : (1 * 1 : Rat) / (4 * 4) = 16 / 256 := rat_div_eq_of_cross h44 (by decide) (by grind)
    have h17_16 : (17 * 17 : Rat) / (4 * 4) = 4624 / 256 := rat_div_eq_of_cross h44 (by decide) (by grind)
    rw [h1_16, h17_16]
    have heq : A - (16 / 256 - (1 - α) * (4624 / 256)) = (4608 - α * ((B : Rat) + 4623)) / 256 := by
      dsimp only [A, C]; rw [hBm1_eq, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]; grind
    rw [heq]; exact rat_div_nonneg hsub (by decide)
  have hpt_ge : ∀ g : Rat, (15/4 : Rat) ≤ g → -(1 - α) * (g * g) ≤ A := by
    intro g hg
    have h154_nn : (0 : Rat) ≤ 15 / 4 := rat_div_nonneg_nat 15 4 (by decide)
    have hg2 : (15/4 : Rat) * (15/4) ≤ g * g := by
      have hg0 : (0 : Rat) ≤ g := Rat.le_trans h154_nn hg
      exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hg h154_nn)
        (rat_mul_le_mul_of_nonneg_left hg hg0)
    have hle : -(1 - α) * (g * g) ≤ -(1 - α) * ((15/4 : Rat) * (15/4)) := by
      apply rat_le_of_sub_nonneg
      have heq : -(1 - α) * ((15/4 : Rat) * (15/4)) - -(1 - α) * (g * g) =
          (1 - α) * (g * g - (15/4 : Rat) * (15/4)) := by grind
      rw [heq]; exact Rat.mul_nonneg hδ_nonneg (rat_sub_nonneg hg2)
    exact Rat.le_trans hle hpt154
  have hmid_half_ge : ∀ g1 g2 : Rat, g2 - g1 = 1/2 → (4 : Rat) ≤ g1 →
      ((g2 - g1) / 2) * ((g2 - g1) / 2) - (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2)) ≤ A := by
    intro g1 g2 hgap hg1
    have hle : ((g2 - g1) / 2) * ((g2 - g1) / 2) - (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2)) ≤
        ((9/2 - 4 : Rat) / 2) * ((9/2 - 4 : Rat) / 2) -
        (1 - α) * (((4 + 9/2 : Rat) / 2) * ((4 + 9/2 : Rat) / 2)) := by
      have hgap0 : (9/2 - 4 : Rat) = 1/2 := by
        have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
        rw [Rat.div_def, Rat.div_def]; grind
      have hmid0 : (4 + 9/2 : Rat) / 2 = 17/4 := by
        have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
        apply rat_div_eq_of_cross (by decide) (by decide); rw [Rat.div_def]; grind
      have hm_ge : (17/4 : Rat) ≤ (g1 + g2) / 2 := by
        have hg2 : g2 = g1 + 1/2 := by grind
        rw [hg2]
        have hsub := rat_sub_nonneg hg1
        apply rat_le_of_sub_nonneg
        have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
        have h4' : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
        have h2sq : (2 : Rat)⁻¹ * (2 : Rat)⁻¹ = (4 : Rat)⁻¹ := by
          have hmul : ((2 : Rat)⁻¹ * (2 : Rat)⁻¹ - (4 : Rat)⁻¹) * 4 = 0 := by grind
          cases Rat.mul_eq_zero.mp hmul with
          | inl h0 => grind
          | inr h0 => exact False.elim ((by decide : (4 : Rat) ≠ 0) h0)
        have heq : (g1 + (g1 + 1 / 2)) / 2 - 17 / 4 = g1 - 4 := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
        rw [heq]; exact hsub
      have h174_nn : (0 : Rat) ≤ 17/4 := rat_div_nonneg_nat 17 4 (by decide)
      have hm2 : (17/4 : Rat) * (17/4) ≤ ((g1 + g2) / 2) * ((g1 + g2) / 2) := by
        have hm0 : (0 : Rat) ≤ (g1 + g2) / 2 := Rat.le_trans h174_nn hm_ge
        exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hm_ge h174_nn)
          (rat_mul_le_mul_of_nonneg_left hm_ge hm0)
      apply rat_le_of_sub_nonneg
      rw [hgap0, hgap, hmid0]
      have heq : (((1/2 : Rat) / 2) * ((1/2 : Rat) / 2) - (1 - α) * ((17/4 : Rat) * (17/4))) -
          (((1/2 : Rat) / 2) * ((1/2 : Rat) / 2) - (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2))) =
          (1 - α) * (((g1 + g2) / 2) * ((g1 + g2) / 2) - (17/4 : Rat) * (17/4)) := by grind
      rw [heq]; exact Rat.mul_nonneg hδ_nonneg (rat_sub_nonneg hm2)
    exact Rat.le_trans hle hmid174
  have hanc_bd :
      (e2m3Quant (y i0) - y i0) * (e2m3Quant (y i0) - y i0) - (1 - α) * (y i0 * y i0) ≤ A := by
    rw [← absRat_sq (y i0)]
    unfold e2m3Quant
    rw [symQuant_sq_err_abs, nearestNonneg_e2m3_upper hi0]
    have hdiv_le_n : ∀ a b c : Nat, 0 < b → a ≤ c * b → (a : Rat) / (b : Rat) ≤ (c : Rat) := by
      intro a b c hb h
      have h1 := rat_div_le_div_nat a b c 1 hb (by decide) (by omega)
      have hc : (c : Rat) / ((1 : Nat) : Rat) = (c : Rat) := rat_div_eq_int (by decide) (by grind)
      rw [hc] at h1; exact h1
    have hn_le_div : ∀ c a b : Nat, 0 < b → c * b ≤ a → (c : Rat) ≤ (a : Rat) / (b : Rat) := by
      intro c a b hb h
      have h1 := rat_div_le_div_nat c 1 a b (by decide) hb (by omega)
      have hc : (c : Rat) / ((1 : Nat) : Rat) = (c : Rat) := rat_div_eq_int (by decide) (by grind)
      rw [hc] at h1; exact h1
    have hsort : isSorted e2m3UpperLevels := by
      refine ⟨hdiv_le_n 15 4 4 (by decide) (by decide),
              hn_le_div 4 9 2 (by decide) (by decide),
              hdiv_le_n 9 2 5 (by decide) (by decide),
              hn_le_div 5 11 2 (by decide) (by decide),
              hdiv_le_n 11 2 6 (by decide) (by decide),
              hn_le_div 6 13 2 (by decide) (by decide),
              hdiv_le_n 13 2 7 (by decide) (by decide),
              hn_le_div 7 15 2 (by decide) (by decide), trivial⟩
    have hhalf : ∀ n : Nat, ((2 * n + 1 : Nat) : Rat) / 2 - (n : Rat) = 1 / 2 := by
      intro n; rw [Rat.div_def, Rat.div_def]
      have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
      rw [Rat.natCast_add, Rat.natCast_mul]; grind
    have hhalf' : ∀ n : Nat, ((n + 1 : Nat) : Rat) - ((2 * n + 1 : Nat) : Rat) / 2 = 1 / 2 := by
      intro n; rw [Rat.div_def, Rat.div_def]
      have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
      rw [Rat.natCast_add, Rat.natCast_add, Rat.natCast_mul]; grind
    have hgb : gridQuadBound α A e2m3UpperLevels :=
      ⟨hpt154, hmid318,
       hpt_ge 4 (hdiv_le_n 15 4 4 (by decide) (by decide)), hmid174,
       hpt_ge (9/2) (rat_div_le_div_nat 15 4 9 2 (by decide) (by decide) (by decide)),
         hmid_half_ge (9/2) 5 (hhalf' 4) (hn_le_div 4 9 2 (by decide) (by decide)),
       hpt_ge 5 (hdiv_le_n 15 4 5 (by decide) (by decide)),
         hmid_half_ge 5 (11/2) (hhalf 5) (by decide),
       hpt_ge (11/2) (rat_div_le_div_nat 15 4 11 2 (by decide) (by decide) (by decide)),
         hmid_half_ge (11/2) 6 (hhalf' 5) (hn_le_div 4 11 2 (by decide) (by decide)),
       hpt_ge 6 (hdiv_le_n 15 4 6 (by decide) (by decide)),
         hmid_half_ge 6 (13/2) (hhalf 6) (by decide),
       hpt_ge (13/2) (rat_div_le_div_nat 15 4 13 2 (by decide) (by decide) (by decide)),
         hmid_half_ge (13/2) 7 (hhalf' 6) (hn_le_div 4 13 2 (by decide) (by decide)),
       hpt_ge 7 (hdiv_le_n 15 4 7 (by decide) (by decide)),
         hmid_half_ge 7 (15/2) (hhalf 7) (by decide),
       hpt_ge (15/2) (rat_div_le_div_nat 15 4 15 2 (by decide) (by decide) (by decide))⟩
    exact nearestNonneg_quad_le hα_nonneg e2m3UpperLevels hsort hgb (15/4)
      [4, 9/2, 5, 11/2, 6, 13/2, 7, 15/2] rfl (absRat (y i0)) (Rat.le_of_lt hi0) (hmax i0)
  have hsum := sumFinRat_le_anchor i0
    (fun i => (e2m3Quant (y i) - y i) * (e2m3Quant (y i) - y i) - (1 - α) * (y i * y i))
    A C hanc_bd (fun i _ => hnonanc i)
  have hzero : A + ((B - 1 : Nat) : Rat) * C = 0 := by dsimp only [A]; grind
  rw [hzero, sumFinRat_sub, sumFinRat_mul_left] at hsum
  exact rat_le_of_sub_nonneg (by
    have h := rat_sub_nonneg hsum
    have heq : (1 - α) * sumSq y - sumSqErr e2m3Quant y =
        0 - (sumFinRat B (fun i => (e2m3Quant (y i) - y i) * (e2m3Quant (y i) - y i)) -
             (1 - α) * sumFinRat B (fun i => y i * y i)) := by
      unfold sumSq sumSqErr; grind
    rw [heq]; exact h)

/-! #### Exact `e2m3Quant` Witness Evaluations (via `nearestNonneg_map_div`) -/

private theorem e2m3Quant_div_nat (p q : Nat) (hq : 0 < q) :
    e2m3Quant ((p : Rat) / (q : Rat)) = ((nearestNonnegNat 8 e2m3Nums p q : Nat) : Rat) / 8 := by
  unfold e2m3Quant symQuant
  have hnn : (0 : Rat) ≤ (p : Rat) / (q : Rat) := rat_div_nonneg_nat p q hq
  have hn : ¬((p : Rat) / (q : Rat) < 0) := Rat.not_lt.mpr hnn
  simp only [hn, ↓reduceIte]
  rw [e2m3Levels_eq_map]
  exact nearestNonneg_map_div 8 p q (by decide) hq e2m3Nums

private theorem e2m3Quant_17_4 : e2m3Quant (17/4) = 4 := by
  have h := e2m3Quant_div_nat 17 4 (by decide)
  have hnat : nearestNonnegNat 8 e2m3Nums 17 4 = 32 := by decide
  rw [hnat] at h
  exact Eq.trans h (rat_div_eq_int (by decide) (by grind))

private theorem e2m3Quant_31_8 : e2m3Quant (31/8) = 15/4 := by
  have h := e2m3Quant_div_nat 31 8 (by decide)
  have hnat : nearestNonnegNat 8 e2m3Nums 31 8 = 30 := by decide
  rw [hnat] at h
  exact Eq.trans h (rat_div_eq_of_cross (by decide) (by decide) (by grind))

private theorem e2m3Quant_15_2 : e2m3Quant (15/2) = 15/2 := by
  have h := e2m3Quant_div_nat 15 2 (by decide)
  have hnat : nearestNonnegNat 8 e2m3Nums 15 2 = 60 := by decide
  rw [hnat] at h
  exact Eq.trans h (rat_div_eq_of_cross (by decide) (by decide) (by grind))

private theorem e2m3Quant_1_16 : e2m3Quant (1/16) = 0 := by
  have h := e2m3Quant_div_nat 1 16 (by decide)
  have hnat : nearestNonnegNat 8 e2m3Nums 1 16 = 0 := by decide
  rw [hnat] at h
  have h0 : ((0 : Nat) : Rat) / 8 = 0 := rat_div_eq_int (by decide) (by grind)
  rw [h0] at h; exact h

private theorem e2m3Quant_15_4_plus {t : Rat} (ht0 : (0 : Rat) < t) (ht1 : t < 1/8) :
    e2m3Quant (15/4 + t) = 15/4 := by
  unfold e2m3Quant symQuant
  have hpos : (15/4 : Rat) < 15/4 + t := by apply rat_lt_of_sub_pos; grind
  have hnn : (0 : Rat) ≤ 15/4 + t :=
    Rat.le_trans (rat_div_nonneg_nat 15 4 (by decide)) (Rat.le_of_lt hpos)
  have hn : ¬((15/4 + t : Rat) < 0) := Rat.not_lt.mpr hnn
  simp only [hn, ↓reduceIte]
  rw [nearestNonneg_e2m3_upper hpos]
  unfold e2m3UpperLevels
  simp only [nearestNonneg]
  have hle : 15/4 + t ≤ (15/4 + 4) / 2 := by
    have h1 := Rat.le_of_lt ht1
    have h2 := rat_add_le_add (Rat.le_refl (a := (15/4 : Rat))) h1
    have heq : (15/4 + 4 : Rat) / 2 = 15/4 + 1/8 := by
      have h4 : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
      have h8 : (8 : Rat) * (8 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 8 (by decide)
      have h2' : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
      have hmul : ((15/4 + 4 : Rat) / 2 - (15/4 + 1/8)) * 8 = 0 := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr h0 => exact False.elim ((by decide : (8 : Rat) ≠ 0) h0)
    rw [heq]; exact h2
  simp only [hle, ↓reduceIte]

private theorem mxfp6_e2m3_tight (B : Nat) (hB : 0 < B) (ε : Rat) (hε : (0 : Rat) < ε) :
    ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 15/2) ∧
      (∃ i0, (15/4 : Rat) < absRat (y i0)) ∧
      (1 - alphaMXFP6E2M3 B - ε) * sumSq y < sumSqErr e2m3Quant y := by
  let i0 : Fin B := ⟨0, hB⟩
  have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
    have := rat_natCast_sub hB; simpa using this
  have hd1 : (0 : Rat) < (B : Rat) + 4623 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have hd2 : (0 : Rat) < (B : Rat) + 3843 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have hd3 : (0 : Rat) < (B : Rat) + 3599 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have h1_16_nn : (0 : Rat) ≤ (1 : Rat) / 16 := rat_div_nonneg_nat 1 16 (by decide)
  have h1_16_le : (1 : Rat) / 16 ≤ 15 / 2 := rat_div_le_div_nat 1 16 15 2 (by decide) (by decide) (by decide)
  have h44 : (4 : Rat) * 4 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h88 : (8 : Rat) * 8 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h1616 : (16 : Rat) * 16 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h1_16_sq : (1 / 16 : Rat) * (1 / 16) = 1 / 256 := by
    rw [rat_div_sq 1 16 (by decide)]
    exact rat_div_eq_of_cross h1616 (by decide) (by grind)
  have h256 : (256 : Rat) * (256 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 256 (by decide)
  have h17_4_nn : (0 : Rat) ≤ 17 / 4 := rat_div_nonneg_nat 17 4 (by decide)
  have h31_8_nn : (0 : Rat) ≤ 31 / 8 := rat_div_nonneg_nat 31 8 (by decide)
  by_cases h1 : B ≤ 57
  · refine ⟨fun i => if i = i0 then 17/4 else 1/16, ?_, ?_, ?_⟩
    · intro i
      by_cases h : i = i0
      · simp only [h, ↓reduceIte, absRat_of_nonneg h17_4_nn]
        exact rat_div_le_div_nat 17 4 15 2 (by decide) (by decide) (by decide)
      · simp only [h, ↓reduceIte, absRat_of_nonneg h1_16_nn]; exact h1_16_le
    · refine ⟨i0, ?_⟩
      simp only [↓reduceIte, absRat_of_nonneg h17_4_nn]
      exact rat_div_lt_div_nat 15 4 17 4 (by decide) (by decide) (by decide)
    · have hα_eq : alphaMXFP6E2M3 B = 4608 / ((B : Rat) + 4623) := by
        unfold alphaMXFP6E2M3
        have hBle : (B : Rat) ≤ 57 := rat_natCast_le h1
        have h12 : 4608 / ((B : Rat) + 4623) ≤ 3840 / ((B : Rat) + 3843) := by
          apply rat_div_le_div_of_cross hd1 hd2; apply rat_le_of_sub_nonneg
          have heq : 3840 * ((B : Rat) + 4623) - 4608 * ((B : Rat) + 3843) =
              768 * (57 - (B : Rat)) := by grind
          rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hBle)
        have h13 : 4608 / ((B : Rat) + 4623) ≤ 3600 / ((B : Rat) + 3599) := by
          apply rat_div_le_div_of_cross hd1 hd3; apply rat_le_of_sub_nonneg
          have heq : 3600 * ((B : Rat) + 4623) - 4608 * ((B : Rat) + 3599) =
              1008 * (57 - (B : Rat)) + 1152 := by grind
          rw [heq]; exact rat_add_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBle)) (by decide)
        exact rat_min_eq_left (rat_le_min h12 h13)
      have hsq : sumSq (fun i => if i = i0 then (17/4 : Rat) else 1/16) =
          4624/256 + ((B - 1 : Nat) : Rat) / 256 := by
        unfold sumSq
        have hcongr : (fun i => (if i = i0 then (17/4 : Rat) else 1/16) *
            (if i = i0 then (17/4 : Rat) else 1/16)) =
            (fun i => if i = i0 then (4624/256 : Rat) else 1/256) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, rat_div_sq 17 4 (by decide)]
            exact rat_div_eq_of_cross h44 (by decide) (by grind)
          · simp only [h, ↓reduceIte]; exact h1_16_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      have herr : sumSqErr e2m3Quant (fun i => if i = i0 then (17/4 : Rat) else 1/16) =
          16/256 + ((B - 1 : Nat) : Rat) / 256 := by
        unfold sumSqErr
        have hcongr : (fun i => (e2m3Quant (if i = i0 then (17/4 : Rat) else 1/16) -
            (if i = i0 then (17/4 : Rat) else 1/16)) *
            (e2m3Quant (if i = i0 then (17/4 : Rat) else 1/16) -
            (if i = i0 then (17/4 : Rat) else 1/16))) =
            (fun i => if i = i0 then (16/256 : Rat) else 1/256) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, e2m3Quant_17_4]
            have h4 : (4 : Rat) - 17/4 = -(1/4) := by
              have h4i : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
              rw [Rat.div_def, Rat.div_def]; grind
            rw [h4]
            have : (-(1/4 : Rat)) * (-(1/4)) = (1/4 : Rat) * (1/4) := by grind
            rw [this, rat_div_sq 1 4 (by decide)]
            exact rat_div_eq_of_cross h44 (by decide) (by grind)
          · simp only [h, ↓reduceIte, e2m3Quant_1_16]
            have : (0 - 1/16 : Rat) * (0 - 1/16) = (1/16 : Rat) * (1/16) := by grind
            rw [this]; exact h1_16_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      rw [hα_eq, hsq, herr]
      have hsum_pos : (0 : Rat) < 4624/256 + ((B - 1 : Nat) : Rat) / 256 :=
        rat_add_pos_of_pos_of_nonneg (rat_div_pos_nat 4624 256 (by decide) (by decide))
          (rat_div_nonneg (rat_natCast_nonneg _) (by decide))
      have heq_exact : (1 - 4608 / ((B : Rat) + 4623)) * (4624/256 + ((B - 1 : Nat) : Rat) / 256) =
          16/256 + ((B - 1 : Nat) : Rat) / 256 := by
        rw [hBm1_eq]
        have hinv : ((B : Rat) + 4623)⁻¹ * ((B : Rat) + 4623) = 1 :=
          Rat.inv_mul_cancel _ (Rat.ne_of_gt hd1)
        rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]; grind
      apply rat_lt_of_sub_pos
      have hdiff : (16/256 + ((B - 1 : Nat) : Rat) / 256) -
          (1 - 4608 / ((B : Rat) + 4623) - ε) * (4624/256 + ((B - 1 : Nat) : Rat) / 256) =
          ε * (4624/256 + ((B - 1 : Nat) : Rat) / 256) := by
        rw [← heq_exact]; grind
      rw [hdiff]; exact rat_mul_pos hε hsum_pos
  · by_cases h2 : B ≤ 61
    · refine ⟨fun i => if i = i0 then 31/8 else 1/16, ?_, ?_, ?_⟩
      · intro i
        by_cases h : i = i0
        · simp only [h, ↓reduceIte, absRat_of_nonneg h31_8_nn]
          exact rat_div_le_div_nat 31 8 15 2 (by decide) (by decide) (by decide)
        · simp only [h, ↓reduceIte, absRat_of_nonneg h1_16_nn]; exact h1_16_le
      · refine ⟨i0, ?_⟩
        simp only [↓reduceIte, absRat_of_nonneg h31_8_nn]
        exact rat_div_lt_div_nat 15 4 31 8 (by decide) (by decide) (by decide)
      · have hα_eq : alphaMXFP6E2M3 B = 3840 / ((B : Rat) + 3843) := by
          unfold alphaMXFP6E2M3
          have hBge : (57 : Rat) ≤ (B : Rat) := rat_natCast_le (m := 57) (by omega)
          have hBle : (B : Rat) ≤ 61 := rat_natCast_le h2
          have h21 : 3840 / ((B : Rat) + 3843) ≤ 4608 / ((B : Rat) + 4623) := by
            apply rat_div_le_div_of_cross hd2 hd1; apply rat_le_of_sub_nonneg
            have heq : 4608 * ((B : Rat) + 3843) - 3840 * ((B : Rat) + 4623) =
                768 * ((B : Rat) - 57) := by grind
            rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge)
          have h23 : 3840 / ((B : Rat) + 3843) ≤ 3600 / ((B : Rat) + 3599) := by
            apply rat_div_le_div_of_cross hd2 hd3; apply rat_le_of_sub_nonneg
            have heq : 3600 * ((B : Rat) + 3843) - 3840 * ((B : Rat) + 3599) =
                240 * (61 - (B : Rat)) := by grind
            rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hBle)
          rw [rat_min_eq_left h23, rat_min_eq_right h21]
        have hsq : sumSq (fun i => if i = i0 then (31/8 : Rat) else 1/16) =
            3844/256 + ((B - 1 : Nat) : Rat) / 256 := by
          unfold sumSq
          have hcongr : (fun i => (if i = i0 then (31/8 : Rat) else 1/16) *
              (if i = i0 then (31/8 : Rat) else 1/16)) =
              (fun i => if i = i0 then (3844/256 : Rat) else 1/256) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte, rat_div_sq 31 8 (by decide)]
              exact rat_div_eq_of_cross h88 (by decide) (by grind)
            · simp only [h, ↓reduceIte]; exact h1_16_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        have herr : sumSqErr e2m3Quant (fun i => if i = i0 then (31/8 : Rat) else 1/16) =
            4/256 + ((B - 1 : Nat) : Rat) / 256 := by
          unfold sumSqErr
          have hcongr : (fun i => (e2m3Quant (if i = i0 then (31/8 : Rat) else 1/16) -
              (if i = i0 then (31/8 : Rat) else 1/16)) *
              (e2m3Quant (if i = i0 then (31/8 : Rat) else 1/16) -
              (if i = i0 then (31/8 : Rat) else 1/16))) =
              (fun i => if i = i0 then (4/256 : Rat) else 1/256) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte, e2m3Quant_31_8]
              have hdiff : (15/4 : Rat) - 31/8 = -(1/8) := by
                have h4i : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
                have h8i : (8 : Rat) * (8 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 8 (by decide)
                have hmul : ((15/4 : Rat) - 31/8 - -(1/8)) * 8 = 0 := by
                  rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
                cases Rat.mul_eq_zero.mp hmul with
                | inl h0 => grind
                | inr h0 => exact False.elim ((by decide : (8 : Rat) ≠ 0) h0)
              rw [hdiff]
              have : (-(1/8 : Rat)) * (-(1/8)) = (1/8 : Rat) * (1/8) := by grind
              rw [this, rat_div_sq 1 8 (by decide)]
              exact rat_div_eq_of_cross h88 (by decide) (by grind)
            · simp only [h, ↓reduceIte, e2m3Quant_1_16]
              have : (0 - 1/16 : Rat) * (0 - 1/16) = (1/16 : Rat) * (1/16) := by grind
              rw [this]; exact h1_16_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        rw [hα_eq, hsq, herr]
        have hsum_pos : (0 : Rat) < 3844/256 + ((B - 1 : Nat) : Rat) / 256 :=
          rat_add_pos_of_pos_of_nonneg (rat_div_pos_nat 3844 256 (by decide) (by decide))
            (rat_div_nonneg (rat_natCast_nonneg _) (by decide))
        have heq_exact : (1 - 3840 / ((B : Rat) + 3843)) * (3844/256 + ((B - 1 : Nat) : Rat) / 256) =
            4/256 + ((B - 1 : Nat) : Rat) / 256 := by
          rw [hBm1_eq]
          have hinv : ((B : Rat) + 3843)⁻¹ * ((B : Rat) + 3843) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hd2)
          rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]; grind
        apply rat_lt_of_sub_pos
        have hdiff : (4/256 + ((B - 1 : Nat) : Rat) / 256) -
            (1 - 3840 / ((B : Rat) + 3843) - ε) * (3844/256 + ((B - 1 : Nat) : Rat) / 256) =
            ε * (3844/256 + ((B - 1 : Nat) : Rat) / 256) := by
          rw [← heq_exact]; grind
        rw [hdiff]; exact rat_mul_pos hε hsum_pos
    · let t : Rat := min (1/16) (ε * (225/16) / 8)
      have ht_pos : (0 : Rat) < t := by
        dsimp only [t]
        have h1' : (0 : Rat) < 1 / 16 := rat_div_pos_nat 1 16 (by decide) (by decide)
        have h2' : (0 : Rat) < ε * (225/16) / 8 :=
          rat_div_pos (rat_mul_pos hε (rat_div_pos_nat 225 16 (by decide) (by decide))) (by decide)
        change (0 : Rat) < if _ ≤ _ then _ else _
        split
        · exact h1'
        · exact h2'
      have ht_le_16 : t ≤ 1/16 := rat_min_le_left _ _
      have ht_lt_8 : t < 1/8 := rat_lt_of_le_of_lt ht_le_16 (rat_div_lt_div_nat 1 16 1 8 (by decide) (by decide) (by decide))
      have ht_le_eps : t ≤ ε * (225/16) / 8 := rat_min_le_right _ _
      refine ⟨fun i => if i = i0 then 15/4 + t else 1/16, ?_, ?_, ?_⟩
      · intro i
        by_cases h : i = i0
        · simp only [h, ↓reduceIte]
          have hpos : (0 : Rat) ≤ 15/4 + t :=
            rat_add_nonneg (rat_div_nonneg_nat 15 4 (by decide)) (Rat.le_of_lt ht_pos)
          rw [absRat_of_nonneg hpos]
          have h1 : (15/4 : Rat) + t ≤ 15/4 + 1/16 := rat_add_le_add (Rat.le_refl) ht_le_16
          have h2 : (15/4 : Rat) + 1/16 = 61/16 := by
            have h4i : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
            have h16i : (16 : Rat) * (16 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 16 (by decide)
            have hmul : (((15/4 : Rat) + 1/16) - 61/16) * 16 = 0 := by
              rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
            cases Rat.mul_eq_zero.mp hmul with
            | inl h0 => grind
            | inr h0 => exact False.elim ((by decide : (16 : Rat) ≠ 0) h0)
          rw [h2] at h1
          exact Rat.le_trans h1 (rat_div_le_div_nat 61 16 15 2 (by decide) (by decide) (by decide))
        · simp only [h, ↓reduceIte, absRat_of_nonneg h1_16_nn]; exact h1_16_le
      · refine ⟨i0, ?_⟩
        simp only [↓reduceIte]
        have hpos : (0 : Rat) ≤ 15/4 + t :=
          rat_add_nonneg (rat_div_nonneg_nat 15 4 (by decide)) (Rat.le_of_lt ht_pos)
        rw [absRat_of_nonneg hpos]
        apply rat_lt_of_sub_pos; grind
      · have hα_eq : alphaMXFP6E2M3 B = 3600 / ((B : Rat) + 3599) := by
          unfold alphaMXFP6E2M3
          have hBge : (61 : Rat) ≤ (B : Rat) := rat_natCast_le (m := 61) (by omega)
          have h32 : 3600 / ((B : Rat) + 3599) ≤ 3840 / ((B : Rat) + 3843) := by
            apply rat_div_le_div_of_cross hd3 hd2; apply rat_le_of_sub_nonneg
            have heq : 3840 * ((B : Rat) + 3599) - 3600 * ((B : Rat) + 3843) =
                240 * ((B : Rat) - 61) := by grind
            rw [heq]; exact Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge)
          have h31 : 3600 / ((B : Rat) + 3599) ≤ 4608 / ((B : Rat) + 4623) := by
            apply rat_div_le_div_of_cross hd3 hd1; apply rat_le_of_sub_nonneg
            have heq : 4608 * ((B : Rat) + 3599) - 3600 * ((B : Rat) + 4623) =
                1008 * ((B : Rat) - 61) + 2880 := by grind
            rw [heq]
            exact rat_add_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge)) (by decide)
          rw [rat_min_eq_right h32, rat_min_eq_right h31]
        let δ3 : Rat := 1 - 3600 / ((B : Rat) + 3599)
        have hsq : sumSq (fun i => if i = i0 then (15/4 + t : Rat) else 1/16) =
            (15/4 + t) * (15/4 + t) + ((B - 1 : Nat) : Rat) / 256 := by
          unfold sumSq
          have hcongr : (fun i => (if i = i0 then (15/4 + t : Rat) else 1/16) *
              (if i = i0 then (15/4 + t : Rat) else 1/16)) =
              (fun i => if i = i0 then (15/4 + t) * (15/4 + t) else 1/256) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte]
            · simp only [h, ↓reduceIte]; exact h1_16_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        have herr : sumSqErr e2m3Quant (fun i => if i = i0 then (15/4 + t : Rat) else 1/16) =
            t * t + ((B - 1 : Nat) : Rat) / 256 := by
          unfold sumSqErr
          have hcongr : (fun i => (e2m3Quant (if i = i0 then (15/4 + t : Rat) else 1/16) -
              (if i = i0 then (15/4 + t : Rat) else 1/16)) *
              (e2m3Quant (if i = i0 then (15/4 + t : Rat) else 1/16) -
              (if i = i0 then (15/4 + t : Rat) else 1/16))) =
              (fun i => if i = i0 then t * t else 1/256) := by
            funext i; by_cases h : i = i0
            · simp only [h, ↓reduceIte, e2m3Quant_15_4_plus ht_pos ht_lt_8]; grind
            · simp only [h, ↓reduceIte, e2m3Quant_1_16]
              have : (0 - 1/16 : Rat) * (0 - 1/16) = (1/16 : Rat) * (1/16) := by grind
              rw [this]; exact h1_16_sq
          rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
        rw [hα_eq, hsq, herr]
        have h225_eq : (225 : Rat) / 16 = 3600 / 256 :=
          rat_div_eq_of_cross (by decide) (by decide) (by grind)
        have hδ3_exact : δ3 * (225/16 + ((B - 1 : Nat) : Rat) / 256) = ((B - 1 : Nat) : Rat) / 256 := by
          dsimp only [δ3]; rw [hBm1_eq, h225_eq]
          have hinv : ((B : Rat) + 3599)⁻¹ * ((B : Rat) + 3599) = 1 :=
            Rat.inv_mul_cancel _ (Rat.ne_of_gt hd3)
          rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind
        have hδ3_lt1 : δ3 < 1 := by
          dsimp only [δ3]
          apply rat_lt_of_sub_pos
          have heq : (1 : Rat) - (1 - 3600 / ((B : Rat) + 3599)) = 3600 / ((B : Rat) + 3599) := by grind
          rw [heq]; exact rat_div_pos (by decide) hd3
        have hlin : (15/2 : Rat) * t + t * t < 8 * t := by
          apply rat_lt_of_sub_pos
          have h12 : (8 : Rat) - 15/2 = 1/2 := by
            have h2i : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
            rw [Rat.div_def, Rat.div_def]; grind
          have heq : 8 * t - ((15/2 : Rat) * t + t * t) = t * ((8 - 15/2) - t) := by grind
          rw [heq, h12]
          exact rat_mul_pos ht_pos (rat_sub_pos (rat_lt_of_le_of_lt ht_le_16
            (rat_div_lt_div_nat 1 16 1 2 (by decide) (by decide) (by decide))))
        have h8t_le : 8 * t ≤ ε * (225/16) := by
          have hmul := rat_mul_le_mul_of_nonneg_left ht_le_eps (by decide : (0 : Rat) ≤ 8)
          have hcancel : (8 : Rat) * (ε * (225/16) / 8) = ε * (225/16) := by
            rw [Rat.div_def, Rat.mul_comm (ε * (225/16)), ← Rat.mul_assoc]
            have h8 : (8 : Rat) * (8 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 8 (by decide)
            rw [h8, Rat.one_mul]
          rw [hcancel] at hmul; exact hmul
        have h15_sq : (15/4 : Rat) * (15/4) = 225/16 := by
          rw [rat_div_sq 15 4 (by decide)]
          exact rat_div_eq_of_cross h44 (by decide) (by grind)
        have h2_15 : (2 : Rat) * (15/4) = 15/2 := by
          have h4i : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
          have h2i : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 2 (by decide)
          have hmul : ((2 : Rat) * (15/4) - 15/2) * 4 = 0 := by
            rw [Rat.div_def, Rat.div_def]; grind
          cases Rat.mul_eq_zero.mp hmul with
          | inl h0 => grind
          | inr h0 => exact False.elim ((by decide : (4 : Rat) ≠ 0) h0)
        have hstep1 : δ3 * ((15/2 : Rat) * t + t * t) <
            ε * ((15/4 + t) * (15/4 + t) + ((B - 1 : Nat) : Rat) / 256) := by
          have hpos_dt : (0 : Rat) < (15/2 : Rat) * t + t * t :=
            rat_add_pos_of_pos_of_nonneg (rat_mul_pos (rat_div_pos_nat 15 2 (by decide) (by decide)) ht_pos) (rat_sq_nonneg t)
          have ha : δ3 * ((15/2 : Rat) * t + t * t) < 1 * ((15/2 : Rat) * t + t * t) :=
            rat_mul_lt_mul_of_pos_right hδ3_lt1 hpos_dt
          have hb : 1 * ((15/2 : Rat) * t + t * t) < 8 * t := by rw [Rat.one_mul]; exact hlin
          have hc : ε * (225/16) ≤ ε * ((15/4 + t) * (15/4 + t) + ((B - 1 : Nat) : Rat) / 256) := by
            apply rat_mul_le_mul_of_nonneg_left _ (Rat.le_of_lt hε)
            apply rat_le_of_sub_nonneg
            have heq : (15/4 + t) * (15/4 + t) + ((B - 1 : Nat) : Rat) / 256 - 225/16 =
                ((15/2 : Rat) * t + t * t) + ((B - 1 : Nat) : Rat) / 256 := by
              rw [← h15_sq, ← h2_15]; grind
            rw [heq]
            exact rat_add_nonneg (Rat.le_of_lt hpos_dt) (rat_div_nonneg (rat_natCast_nonneg _) (by decide))
          exact rat_lt_of_lt_of_le (rat_lt_trans ha hb) (Rat.le_trans h8t_le hc)
        apply rat_lt_of_sub_pos
        have hsub := rat_sub_pos hstep1
        have heq : (t * t + ((B - 1 : Nat) : Rat) / 256) -
            (1 - 3600 / ((B : Rat) + 3599) - ε) * ((15/4 + t) * (15/4 + t) + ((B - 1 : Nat) : Rat) / 256) =
            t * t + (ε * ((15/4 + t) * (15/4 + t) + ((B - 1 : Nat) : Rat) / 256) -
                     δ3 * ((15/2 : Rat) * t + t * t)) := by
          dsimp only [δ3] at hδ3_exact ⊢
          have hexp : (15/4 + t) * (15/4 + t) = 225/16 + ((15/2 : Rat) * t + t * t) := by
            rw [← h15_sq, ← h2_15]; grind
          rw [hexp]
          have : (1 - 3600 / ((B : Rat) + 3599)) * (225/16 + ((15/2 : Rat) * t + t * t) + ((B - 1 : Nat) : Rat) / 256) =
              (1 - 3600 / ((B : Rat) + 3599)) * (225/16 + ((B - 1 : Nat) : Rat) / 256) +
              (1 - 3600 / ((B : Rat) + 3599)) * ((15/2 : Rat) * t + t * t) := by grind
          grind
        rw [heq]
        exact rat_add_pos_of_pos_of_nonneg (rat_mul_pos ht_pos ht_pos) (Rat.le_of_lt hsub)

/-! #### NVFP6-E2M3 Upper Bound & Exact Attainment -/

private theorem nvfp6_e2m3_upper_bound (B : Nat) (hB : 0 < B) (y : Fin B → Rat)
    (hmax : ∀ i, absRat (y i) ≤ 15/2)
    (hanc : ∃ i0, absRat (y i0) = 15/2) :
    sumSqErr e2m3Quant y ≤ (1 - alphaNVFP6E2M3 B) * sumSq y := by
  let α := alphaNVFP6E2M3 B
  rcases hanc with ⟨i0, hi0⟩
  by_cases hB1 : B = 1
  · subst hB1
    have h0 : i0 = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst h0
    have herr0 : sumSqErr e2m3Quant y = 0 := by
      unfold sumSqErr sumFinRat sumFinRat
      have he : (e2m3Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) *
          (e2m3Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) = 0 := by
        unfold e2m3Quant; rw [symQuant_sq_err_abs, hi0]
        have hq : nearestNonneg e2m3Levels (15/2) = 15/2 := by
          have := e2m3Quant_15_2
          unfold e2m3Quant symQuant at this
          have hn : ¬((15/2 : Rat) < 0) := Rat.not_lt.mpr (rat_div_nonneg_nat 15 2 (by decide))
          simp only [hn, ↓reduceIte] at this; exact this
        rw [hq]; grind
      change (0 : Rat) + (e2m3Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) *
          (e2m3Quant (y ⟨0, by omega⟩) - y ⟨0, by omega⟩) = 0
      rw [he]; grind
    have hα_le1 : α ≤ 1 := by
      have h1 : α ≤ (288 * ((1 : Nat) : Rat) + 612) / (289 * ((1 : Nat) : Rat) + 611) :=
        rat_min_le_left _ _
      have heq : (288 * ((1 : Nat) : Rat) + 612) / (289 * ((1 : Nat) : Rat) + 611) = 1 :=
        rat_div_eq_int (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (by decide)) (by decide))) (by grind)
      rw [heq] at h1; exact h1
    have hsum_nonneg : (0 : Rat) ≤ sumSq y := by
      unfold sumSq sumFinRat sumFinRat
      have hsq := rat_sq_nonneg (y ⟨0, by omega⟩)
      change (0 : Rat) ≤ 0 + _
      rw [Rat.zero_add]; exact hsq
    rw [herr0]
    exact Rat.mul_nonneg (rat_sub_nonneg hα_le1) hsum_nonneg
  · have hB2 : 2 ≤ B := by omega
    have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
      have := rat_natCast_sub hB; simpa using this
    have hBm1_pos : (0 : Rat) < ((B - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
    have hα_pos : (0 : Rat) < α := by
      dsimp only [α]
      unfold alphaNVFP6E2M3
      have h1 : (0 : Rat) < (288 * (B : Rat) + 612) / (289 * (B : Rat) + 611) :=
        rat_div_pos (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide))
          (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide))
      have h2 : (0 : Rat) < 14400 / ((B : Rat) + 14399) :=
        rat_div_pos (by decide) (rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide))
      change (0 : Rat) < if _ ≤ _ then _ else _
      split <;> assumption
    have hα1 : α ≤ (288 * (B : Rat) + 612) / (289 * (B : Rat) + 611) := rat_min_le_left _ _
    have hα2 : α ≤ 14400 / ((B : Rat) + 14399) := rat_min_le_right _ _
    have hδ_nonneg : (0 : Rat) ≤ 1 - α := by
      have hd : (0 : Rat) < (B : Rat) + 14399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
      have hle1 : 14400 / ((B : Rat) + 14399) ≤ 1 := by
        apply rat_div_le_of_mul_le hd
        have hB1 : (1 : Rat) ≤ (B : Rat) := rat_natCast_le hB
        have hsub := rat_sub_nonneg hB1
        apply rat_le_of_sub_nonneg; grind
      exact rat_sub_nonneg (Rat.le_trans hα2 hle1)
    let C : Rat := (1 - α) * ((15/2 : Rat) * (15/2)) / ((B - 1 : Nat) : Rat)
    have hC_nonneg : (0 : Rat) ≤ C :=
      rat_div_nonneg (Rat.mul_nonneg hδ_nonneg (rat_sq_nonneg (15/2))) hBm1_pos
    have hα_unit : α * (4 * ((8 : Nat) : Rat) * ((8 : Nat) : Rat) * ((15/2 : Rat) * (15/2)) + ((B - 1 : Nat) : Rat)) ≤
        4 * ((8 : Nat) : Rat) * ((8 : Nat) : Rat) * ((15/2 : Rat) * (15/2)) := by
      have hd : (0 : Rat) < (B : Rat) + 14399 := rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
      have hmul := rat_mul_le_mul_of_nonneg_right hα2 (Rat.le_of_lt hd)
      have hcancel : 14400 / ((B : Rat) + 14399) * ((B : Rat) + 14399) = 14400 := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
      rw [hcancel] at hmul
      rw [hBm1_eq, rat_div_sq 15 2 (by decide)]
      have heq1 : (4 : Rat) * ((8 : Nat) : Rat) * ((8 : Nat) : Rat) * ((15 * 15 : Rat) / (2 * 2)) = 14400 := by
        have h4i : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
        rw [Rat.div_def]; grind
      rw [heq1]
      have heq2 : (14400 : Rat) + ((B : Rat) - 1) = (B : Rat) + 14399 := by grind
      rw [heq2]; exact hmul
    have hα_ratio : ((B - 1 : Nat) : Rat) *
        ((((4 : Nat) : Rat) / (2 * ((8 : Nat) : Rat))) * (((4 : Nat) : Rat) / (2 * ((8 : Nat) : Rat)))) ≤
        (1 - α) * ((15/2 : Rat) * (15/2) + ((B - 1 : Nat) : Rat) *
          ((((17 : Nat) : Rat) * (((4 : Nat) : Rat) / (2 * ((8 : Nat) : Rat)))) *
           (((17 : Nat) : Rat) * (((4 : Nat) : Rat) / (2 * ((8 : Nat) : Rat)))))) := by
      have hd : (0 : Rat) < 289 * (B : Rat) + 611 :=
        rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide)
      have hmul := rat_mul_le_mul_of_nonneg_right hα1 (Rat.le_of_lt hd)
      have hcancel : (288 * (B : Rat) + 612) / (289 * (B : Rat) + 611) * (289 * (B : Rat) + 611) =
          288 * (B : Rat) + 612 := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
      rw [hcancel] at hmul
      have hsub := rat_sub_nonneg hmul
      apply rat_le_of_sub_nonneg
      rw [hBm1_eq]
      have hsimp1 : ((4 : Nat) : Rat) / (2 * ((8 : Nat) : Rat)) = 1/4 :=
        rat_div_eq_of_cross (Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))) (by decide) (by grind)
      have hsimp2 : ((17 : Nat) : Rat) = 17 := rfl
      rw [hsimp1, hsimp2, rat_div_sq 15 2 (by decide)]
      have h22 : (2 : Rat) * 2 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
      have h44 : (4 : Rat) * 4 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
      have h15_16 : (15 * 15 : Rat) / (2 * 2) = 900 / 16 :=
        rat_div_eq_of_cross h22 (by decide) (by grind)
      have h1_16 : (1/4 : Rat) * (1/4) = 1 / 16 := by
        rw [rat_div_sq 1 4 (by decide)]
        exact rat_div_eq_of_cross h44 (by decide) (by grind)
      have h17_16 : (17 * (1/4 : Rat)) * (17 * (1/4 : Rat)) = 289 / 16 := by
        have : (17 * (1/4 : Rat)) * (17 * (1/4 : Rat)) = 289 * ((1/4 : Rat) * (1/4)) := by grind
        rw [this, h1_16, Rat.div_def, Rat.div_def]; grind
      rw [h15_16, h1_16, h17_16]
      have heq : (1 - α) * (900 / 16 + ((B : Rat) - 1) * (289 / 16)) - ((B : Rat) - 1) * (1 / 16) =
          ((288 * (B : Rat) + 612) - α * (289 * (B : Rat) + 611)) / 16 := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]; grind
      rw [heq]; exact rat_div_nonneg hsub (by decide)
    have hnonanc : ∀ i : Fin B,
        (e2m3Quant (y i) - y i) * (e2m3Quant (y i) - y i) - (1 - α) * (y i * y i) ≤ C := by
      intro i
      rw [← absRat_sq (y i)]
      unfold e2m3Quant
      rw [symQuant_sq_err_abs]
      have hsort : isSorted e2m3Levels := by
        rw [e2m3Levels_eq_map]
        exact isSorted_map_div (by decide) 4 17 e2m3Nums check_e2m3Nums
      have hgb : gridQuadBound α C e2m3Levels := by
        rw [e2m3Levels_eq_map]
        apply gridQuadBound_of_check (D := 8) (maxGap := 4) (ratio := 17) hδ_nonneg hC_nonneg
        · intro a b hab hba hs
          exact unit_step_nvfp (D := 8) (by decide) hB2 hδ_nonneg hα_unit a b hab hba hs
        · intro a b hab hgap hbr
          exact ratio_step_nvfp (D := 8) (maxGap := 4) (ratio := 17) (by decide) (by decide) hB2 hα_ratio a b hab hgap hbr
        · exact check_e2m3Nums
      have hy0 : (0 : Rat) ≤ absRat (y i) := absRat_nonneg (y i)
      have hy152 : absRat (y i) ≤ lastLevel e2m3Levels := by
        have hlast : lastLevel e2m3Levels = 15/2 := rfl
        rw [hlast]; exact hmax i
      exact nearestNonneg_quad_le (Rat.le_of_lt hα_pos) e2m3Levels hsort hgb 0 e2m3Levels.tail rfl (absRat (y i)) hy0 hy152
    have hanc_bd : (e2m3Quant (y i0) - y i0) * (e2m3Quant (y i0) - y i0) - (1 - α) * (y i0 * y i0) ≤
        -(1 - α) * ((15/2 : Rat) * (15/2)) := by
      rw [← absRat_sq (y i0)]
      unfold e2m3Quant; rw [symQuant_sq_err_abs, hi0]
      have hq : nearestNonneg e2m3Levels (15/2) = 15/2 := by
        have := e2m3Quant_15_2
        unfold e2m3Quant symQuant at this
        have hn : ¬((15/2 : Rat) < 0) := Rat.not_lt.mpr (rat_div_nonneg_nat 15 2 (by decide))
        simp only [hn, ↓reduceIte] at this; exact this
      rw [hq]
      have heq : ((15/2 : Rat) - 15/2) * (15/2 - 15/2) - (1 - α) * ((15/2 : Rat) * (15/2)) =
          -(1 - α) * ((15/2 : Rat) * (15/2)) := by grind
      rw [heq]; exact Rat.le_refl
    have hsum := sumFinRat_le_anchor i0
      (fun i => (e2m3Quant (y i) - y i) * (e2m3Quant (y i) - y i) - (1 - α) * (y i * y i))
      (-(1 - α) * ((15/2 : Rat) * (15/2))) C hanc_bd (fun i _ => hnonanc i)
    have hzero : -(1 - α) * ((15/2 : Rat) * (15/2)) + ((B - 1 : Nat) : Rat) * C = 0 := by
      dsimp only [C]
      have hne : ((B - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hBm1_pos
      have hmul : ((B - 1 : Nat) : Rat) * ((1 - α) * ((15/2 : Rat) * (15/2)) / ((B - 1 : Nat) : Rat)) =
          (1 - α) * ((15/2 : Rat) * (15/2)) := by
        rw [Rat.div_def, Rat.mul_comm ((1 - α) * ((15/2 : Rat) * (15/2))), ← Rat.mul_assoc,
            Rat.mul_comm ((B - 1 : Nat) : Rat), Rat.inv_mul_cancel _ hne, Rat.one_mul]
      rw [hmul]; grind
    rw [hzero, sumFinRat_sub, sumFinRat_mul_left] at hsum
    exact rat_le_of_sub_nonneg (by
      have h := rat_sub_nonneg hsum
      have heq : (1 - α) * sumSq y - sumSqErr e2m3Quant y =
          0 - (sumFinRat B (fun i => (e2m3Quant (y i) - y i) * (e2m3Quant (y i) - y i)) -
               (1 - α) * sumFinRat B (fun i => y i * y i)) := by
        unfold sumSq sumSqErr; grind
      rw [heq]; exact h)

private theorem nvfp6_e2m3_attained (B : Nat) (hB : 0 < B) :
    ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 15/2) ∧
      (∃ i0, absRat (y i0) = 15/2) ∧
      sumSqErr e2m3Quant y = (1 - alphaNVFP6E2M3 B) * sumSq y := by
  let i0 : Fin B := ⟨0, hB⟩
  have hBm1_eq : ((B - 1 : Nat) : Rat) = (B : Rat) - 1 := by
    have := rat_natCast_sub hB; simpa using this
  have hd1 : (0 : Rat) < 289 * (B : Rat) + 611 :=
    rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hB)) (by decide)
  have hd2 : (0 : Rat) < (B : Rat) + 14399 :=
    rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hB) (by decide)
  have h15_2_nn : (0 : Rat) ≤ (15 : Rat) / 2 := rat_div_nonneg_nat 15 2 (by decide)
  have h1_16_nn : (0 : Rat) ≤ (1 : Rat) / 16 := rat_div_nonneg_nat 1 16 (by decide)
  have h1_16_le : (1 : Rat) / 16 ≤ 15 / 2 := rat_div_le_div_nat 1 16 15 2 (by decide) (by decide) (by decide)
  have h44 : (4 : Rat) * 4 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h88 : (8 : Rat) * 8 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h1616 : (16 : Rat) * 16 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h1_16_sq : (1 / 16 : Rat) * (1 / 16) = 1 / 256 := by
    rw [rat_div_sq 1 16 (by decide)]
    exact rat_div_eq_of_cross h1616 (by decide) (by grind)
  have h22 : (2 : Rat) * 2 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h44' : (4 : Rat) * 4 ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide) (by decide))
  have h17_4_nn : (0 : Rat) ≤ 17 / 4 := rat_div_nonneg_nat 17 4 (by decide)
  by_cases h1 : B ≤ 47
  · refine ⟨fun i => if i = i0 then 15/2 else 17/4, ?_,
      ⟨i0, by simp only [↓reduceIte, absRat_of_nonneg h15_2_nn]⟩, ?_⟩
    · intro i
      by_cases h : i = i0
      · simp only [h, ↓reduceIte, absRat_of_nonneg h15_2_nn]; exact Rat.le_refl
      · simp only [h, ↓reduceIte, absRat_of_nonneg h17_4_nn]
        exact rat_div_le_div_nat 17 4 15 2 (by decide) (by decide) (by decide)
    · have hα_eq : alphaNVFP6E2M3 B = (288 * (B : Rat) + 612) / (289 * (B : Rat) + 611) := by
        unfold alphaNVFP6E2M3
        apply rat_min_eq_left
        apply rat_div_le_div_of_cross hd1 hd2
        apply rat_le_of_sub_nonneg
        have hB1 : (1 : Rat) ≤ (B : Rat) := rat_natCast_le hB
        have hBle : (B : Rat) ≤ 47 := rat_natCast_le h1
        have heq : 14400 * (289 * (B : Rat) + 611) - (288 * (B : Rat) + 612) * ((B : Rat) + 14399) =
            288 * ((B : Rat) - 1) * (47 - (B : Rat)) + 252 * ((B : Rat) - 1) := by grind
        rw [heq]
        exact rat_add_nonneg
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB1)) (rat_sub_nonneg hBle))
          (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB1))
      have hsq : sumSq (fun i => if i = i0 then (15/2 : Rat) else 17/4) =
          900/16 + ((B - 1 : Nat) : Rat) * (289/16) := by
        unfold sumSq
        have hcongr : (fun i => (if i = i0 then (15/2 : Rat) else 17/4) *
            (if i = i0 then (15/2 : Rat) else 17/4)) =
            (fun i => if i = i0 then (900/16 : Rat) else 289/16) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, rat_div_sq 15 2 (by decide)]
            exact rat_div_eq_of_cross h22 (by decide) (by grind)
          · simp only [h, ↓reduceIte, rat_div_sq 17 4 (by decide)]
            exact rat_div_eq_of_cross h44' (by decide) (by grind)
        rw [hcongr, sumFinRat_single]
      have herr : sumSqErr e2m3Quant (fun i => if i = i0 then (15/2 : Rat) else 17/4) =
          0 + ((B - 1 : Nat) : Rat) * (1/16) := by
        unfold sumSqErr
        have hcongr : (fun i => (e2m3Quant (if i = i0 then (15/2 : Rat) else 17/4) -
            (if i = i0 then (15/2 : Rat) else 17/4)) *
            (e2m3Quant (if i = i0 then (15/2 : Rat) else 17/4) -
            (if i = i0 then (15/2 : Rat) else 17/4))) =
            (fun i => if i = i0 then (0 : Rat) else 1/16) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, e2m3Quant_15_2]; grind
          · simp only [h, ↓reduceIte, e2m3Quant_17_4]
            have h4 : (4 : Rat) - 17/4 = -(1/4) := by
              have h4i : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel 4 (by decide)
              rw [Rat.div_def, Rat.div_def]; grind
            rw [h4]
            have : (-(1/4 : Rat)) * (-(1/4)) = (1/4 : Rat) * (1/4) := by grind
            rw [this, rat_div_sq 1 4 (by decide)]
            exact rat_div_eq_of_cross h44 (by decide) (by grind)
        rw [hcongr, sumFinRat_single]
      rw [hα_eq, hsq, herr, hBm1_eq]
      have hinv : (289 * (B : Rat) + 611)⁻¹ * (289 * (B : Rat) + 611) = 1 :=
        Rat.inv_mul_cancel _ (Rat.ne_of_gt hd1)
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]; grind
  · refine ⟨fun i => if i = i0 then 15/2 else 1/16, ?_,
      ⟨i0, by simp only [↓reduceIte, absRat_of_nonneg h15_2_nn]⟩, ?_⟩
    · intro i
      by_cases h : i = i0
      · simp only [h, ↓reduceIte, absRat_of_nonneg h15_2_nn]; exact Rat.le_refl
      · simp only [h, ↓reduceIte, absRat_of_nonneg h1_16_nn]; exact h1_16_le
    · have hα_eq : alphaNVFP6E2M3 B = 14400 / ((B : Rat) + 14399) := by
        unfold alphaNVFP6E2M3
        apply rat_min_eq_right
        apply rat_div_le_div_of_cross hd2 hd1
        apply rat_le_of_sub_nonneg
        have hBge : (48 : Rat) ≤ (B : Rat) := rat_natCast_le (m := 48) (by omega)
        have heq : (288 * (B : Rat) + 612) * ((B : Rat) + 14399) - 14400 * (289 * (B : Rat) + 611) =
            288 * ((B : Rat) - 48) * ((B : Rat) - 48) + 13572 * ((B : Rat) - 48) + 1692 := by grind
        rw [heq]
        exact rat_add_nonneg
          (rat_add_nonneg
            (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge)) (rat_sub_nonneg hBge))
            (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge)))
          (by decide)
      have hsq : sumSq (fun i => if i = i0 then (15/2 : Rat) else 1/16) =
          14400/256 + ((B - 1 : Nat) : Rat) / 256 := by
        unfold sumSq
        have hcongr : (fun i => (if i = i0 then (15/2 : Rat) else 1/16) *
            (if i = i0 then (15/2 : Rat) else 1/16)) =
            (fun i => if i = i0 then (14400/256 : Rat) else 1/256) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, rat_div_sq 15 2 (by decide)]
            exact rat_div_eq_of_cross h22 (by decide) (by grind)
          · simp only [h, ↓reduceIte]; exact h1_16_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      have herr : sumSqErr e2m3Quant (fun i => if i = i0 then (15/2 : Rat) else 1/16) =
          0 + ((B - 1 : Nat) : Rat) / 256 := by
        unfold sumSqErr
        have hcongr : (fun i => (e2m3Quant (if i = i0 then (15/2 : Rat) else 1/16) -
            (if i = i0 then (15/2 : Rat) else 1/16)) *
            (e2m3Quant (if i = i0 then (15/2 : Rat) else 1/16) -
            (if i = i0 then (15/2 : Rat) else 1/16))) =
            (fun i => if i = i0 then (0 : Rat) else 1/256) := by
          funext i; by_cases h : i = i0
          · simp only [h, ↓reduceIte, e2m3Quant_15_2]; grind
          · simp only [h, ↓reduceIte, e2m3Quant_1_16]
            have : (0 - 1/16 : Rat) * (0 - 1/16) = (1/16 : Rat) * (1/16) := by grind
            rw [this]; exact h1_16_sq
        rw [hcongr, sumFinRat_single, Rat.div_def, Rat.div_def]; grind
      rw [hα_eq, hsq, herr, hBm1_eq]
      have hinv : ((B : Rat) + 14399)⁻¹ * ((B : Rat) + 14399) = 1 :=
        Rat.inv_mul_cancel _ (Rat.ne_of_gt hd2)
      rw [Rat.div_def, Rat.div_def, Rat.div_def]; grind

/-- Theorem 2: Universal all-`B` EF21 contraction law for `MXFP6-E2M3` and `NVFP6-E2M3`. -/
theorem mxfp6_e2m3_nvfp6_ef21_universal (B : Nat) (hB : 0 < B) :
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 15/2) → (∃ i0, (15/4 : Rat) < absRat (y i0)) →
      sumSqErr e2m3Quant y ≤ (1 - alphaMXFP6E2M3 B) * sumSq y) ∧
    (∀ ε : Rat, (0 : Rat) < ε → ∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 15/2) ∧ (∃ i0, (15/4 : Rat) < absRat (y i0)) ∧
      (1 - alphaMXFP6E2M3 B - ε) * sumSq y < sumSqErr e2m3Quant y) ∧
    (∀ y : Fin B → Rat, (∀ i, absRat (y i) ≤ 15/2) → (∃ i0, absRat (y i0) = 15/2) →
      sumSqErr e2m3Quant y ≤ (1 - alphaNVFP6E2M3 B) * sumSq y) ∧
    (∃ y : Fin B → Rat,
      (∀ i, absRat (y i) ≤ 15/2) ∧ (∃ i0, absRat (y i0) = 15/2) ∧
      sumSqErr e2m3Quant y = (1 - alphaNVFP6E2M3 B) * sumSq y) :=
  ⟨mxfp6_e2m3_upper_bound B hB, mxfp6_e2m3_tight B hB,
   nvfp6_e2m3_upper_bound B hB, nvfp6_e2m3_attained B hB⟩

/-! ### 6. Theorem 3: Exact `E2M3` vs `E3M2` Crossover (`B = 43/44` and `B = 178/179`) -/

private theorem rat_lt_min2 {x a b : Rat} (ha : x < a) (hb : x < b) : x < min a b := by
  change x < if a ≤ b then a else b
  split <;> assumption

private theorem rat_lt_min3 {x a b c : Rat} (ha : x < a) (hb : x < b) (hc : x < c) :
    x < min a (min b c) :=
  rat_lt_min2 ha (rat_lt_min2 hb hc)

theorem mxfp6_e2m3_vs_e3m2_exact_crossover (B : Nat) (hB : 0 < B) :
    ((1 ≤ B ∧ B ≤ 43) → alphaMXFP6E3M2 B < alphaMXFP6E2M3 B) ∧
    (44 ≤ B → alphaMXFP6E2M3 B < alphaMXFP6E3M2 B) ∧
    (alphaMXFP6E2M3 32 = 4608 / 4655 ∧ alphaMXFP6E3M2 32 = 327680 / 331807 ∧
     (327680 / 331807 : Rat) < 4608 / 4655) ∧
    (alphaNVFP6E3M2 1 = 1 ∧ alphaNVFP6E2M3 1 = 1) ∧
    ((2 ≤ B ∧ B ≤ 178) → alphaNVFP6E3M2 B < alphaNVFP6E2M3 B) ∧
    (179 ≤ B → alphaNVFP6E2M3 B < alphaNVFP6E3M2 B) := by
  have hBpos : (0 : Rat) < (B : Rat) := rat_natCast_pos hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨_, h43⟩
    have hBle : (B : Rat) ≤ 43 := rat_natCast_le h43
    have hd_e3 : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd1 : (0 : Rat) < (B : Rat) + 4623 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd2 : (0 : Rat) < (B : Rat) + 3843 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd3 : (0 : Rat) < (B : Rat) + 3599 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hα_e3 : alphaMXFP6E3M2 B ≤ 327680 / ((B : Rat) + 331775) := rat_min_le_left _ _
    have hα_e2 : alphaMXFP6E2M3 B = 4608 / ((B : Rat) + 4623) := by
      unfold alphaMXFP6E2M3
      have h12 : 4608 / ((B : Rat) + 4623) ≤ 3840 / ((B : Rat) + 3843) := by
        apply rat_div_le_div_of_cross hd1 hd2; apply rat_le_of_sub_nonneg
        have heq : 3840 * ((B : Rat) + 4623) - 4608 * ((B : Rat) + 3843) =
            768 * (43 - (B : Rat)) + 10752 := by grind
        rw [heq]; exact rat_add_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBle)) (by decide)
      have h13 : 4608 / ((B : Rat) + 4623) ≤ 3600 / ((B : Rat) + 3599) := by
        apply rat_div_le_div_of_cross hd1 hd3; apply rat_le_of_sub_nonneg
        have heq : 3600 * ((B : Rat) + 4623) - 4608 * ((B : Rat) + 3599) =
            1008 * (43 - (B : Rat)) + 15264 := by grind
        rw [heq]; exact rat_add_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBle)) (by decide)
      exact rat_min_eq_left (rat_le_min h12 h13)
    rw [hα_e2]
    refine rat_lt_of_le_of_lt hα_e3 ?_
    apply rat_div_lt_div_of_cross hd_e3 hd1
    apply rat_lt_of_sub_pos
    have heq : 4608 * ((B : Rat) + 331775) - 327680 * ((B : Rat) + 4623) =
        62464 + 323072 * (43 - (B : Rat)) := by grind
    rw [heq]
    exact rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBle))
  · intro h44
    have hBge : (44 : Rat) ≤ (B : Rat) := rat_natCast_le h44
    have hd_e2_1 : (0 : Rat) < (B : Rat) + 4623 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd_e2_3 : (0 : Rat) < (B : Rat) + 3599 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd_e3_1 : (0 : Rat) < (B : Rat) + 331775 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd_e3_2 : (0 : Rat) < (B : Rat) + 230399 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd_e3_3 : (0 : Rat) < (B : Rat) + 200703 := rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    by_cases h61 : B ≤ 61
    · have hle_e2 : alphaMXFP6E2M3 B ≤ 4608 / ((B : Rat) + 4623) := rat_min_le_left _ _
      refine rat_lt_of_le_of_lt hle_e2 ?_
      apply rat_lt_min3
      · apply rat_div_lt_div_of_cross hd_e2_1 hd_e3_1; apply rat_lt_of_sub_pos
        have heq : 327680 * ((B : Rat) + 4623) - 4608 * ((B : Rat) + 331775) =
            260608 + 323072 * ((B : Rat) - 44) := by grind
        rw [heq]; exact rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge))
      · apply rat_div_lt_div_of_cross hd_e2_1 hd_e3_2; apply rat_lt_of_sub_pos
        have heq : 229376 * ((B : Rat) + 4623) - 4608 * ((B : Rat) + 230399) =
            8616448 + 224768 * ((B : Rat) - 44) := by grind
        rw [heq]; exact rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge))
      · apply rat_div_lt_div_of_cross hd_e2_1 hd_e3_3; apply rat_lt_of_sub_pos
        have heq : 200704 * ((B : Rat) + 4623) - 4608 * ((B : Rat) + 200703) =
            11643392 + 196096 * ((B : Rat) - 44) := by grind
        rw [heq]; exact rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge))
    · have hB62 : (62 : Rat) ≤ (B : Rat) := rat_natCast_le (m := 62) (by omega)
      have hle_e2 : alphaMXFP6E2M3 B ≤ 3600 / ((B : Rat) + 3599) :=
        Rat.le_trans (rat_min_le_right _ _) (rat_min_le_right _ _)
      refine rat_lt_of_le_of_lt hle_e2 ?_
      apply rat_lt_min3
      · apply rat_div_lt_div_of_cross hd_e2_3 hd_e3_1; apply rat_lt_of_sub_pos
        have heq : 327680 * ((B : Rat) + 3599) - 3600 * ((B : Rat) + 331775) =
            5023280 + 324080 * ((B : Rat) - 62) := by grind
        rw [heq]; exact rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB62))
      · apply rat_div_lt_div_of_cross hd_e2_3 hd_e3_2; apply rat_lt_of_sub_pos
        have heq : 229376 * ((B : Rat) + 3599) - 3600 * ((B : Rat) + 230399) =
            10085936 + 225776 * ((B : Rat) - 62) := by grind
        rw [heq]; exact rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB62))
      · apply rat_div_lt_div_of_cross hd_e2_3 hd_e3_3; apply rat_lt_of_sub_pos
        have heq : 200704 * ((B : Rat) + 3599) - 3600 * ((B : Rat) + 200703) =
            12023344 + 197104 * ((B : Rat) - 62) := by grind
        rw [heq]; exact rat_add_pos_of_pos_of_nonneg (by decide) (Rat.mul_nonneg (by decide) (rat_sub_nonneg hB62))
  · refine ⟨?_, ?_, rat_div_lt_div_nat 327680 331807 4608 4655 (by decide) (by decide) (by decide)⟩
    · unfold alphaMXFP6E2M3
      have h12 : 4608 / (((32 : Nat) : Rat) + 4623) ≤ 3840 / (((32 : Nat) : Rat) + 3843) := by
        apply rat_div_le_div_of_cross (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
          (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
        apply rat_le_of_sub_nonneg
        have heq : 3840 * (((32 : Nat) : Rat) + 4623) - 4608 * (((32 : Nat) : Rat) + 3843) = 19200 := by grind
        rw [heq]; decide
      have h13 : 4608 / (((32 : Nat) : Rat) + 4623) ≤ 3600 / (((32 : Nat) : Rat) + 3599) := by
        apply rat_div_le_div_of_cross (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
          (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
        apply rat_le_of_sub_nonneg
        have heq : 3600 * (((32 : Nat) : Rat) + 4623) - 4608 * (((32 : Nat) : Rat) + 3599) = 26352 := by grind
        rw [heq]; decide
      rw [rat_min_eq_left (rat_le_min h12 h13)]
      exact rat_div_eq_of_cross (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))) (by decide) (by grind)
    · unfold alphaMXFP6E3M2
      have h12 : 327680 / (((32 : Nat) : Rat) + 331775) ≤ 229376 / (((32 : Nat) : Rat) + 230399) := by
        apply rat_div_le_div_of_cross (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
          (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
        apply rat_le_of_sub_nonneg
        have heq : 229376 * (((32 : Nat) : Rat) + 331775) - 327680 * (((32 : Nat) : Rat) + 230399) = 600932352 := by grind
        rw [heq]; decide
      have h13 : 327680 / (((32 : Nat) : Rat) + 331775) ≤ 200704 / (((32 : Nat) : Rat) + 200703) := by
        apply rat_div_le_div_of_cross (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
          (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))
        apply rat_le_of_sub_nonneg
        have heq : 200704 * (((32 : Nat) : Rat) + 331775) - 327680 * (((32 : Nat) : Rat) + 200703) = 818147328 := by grind
        rw [heq]; decide
      rw [rat_min_eq_left (rat_le_min h12 h13)]
      exact rat_div_eq_of_cross (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))) (by decide) (by grind)
  · refine ⟨?_, ?_⟩
    · unfold alphaNVFP6E3M2
      have h1 : (80 * ((1 : Nat) : Rat) + 116) / (81 * ((1 : Nat) : Rat) + 115) = 1 :=
        rat_div_eq_int (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (by decide)) (by decide))) (by grind)
      have h2 : 802816 / (((1 : Nat) : Rat) + 802815) = 1 :=
        rat_div_eq_int (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))) (by grind)
      rw [h1, h2, rat_min_eq_left Rat.le_refl]
    · unfold alphaNVFP6E2M3
      have h1 : (288 * ((1 : Nat) : Rat) + 612) / (289 * ((1 : Nat) : Rat) + 611) = 1 :=
        rat_div_eq_int (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (by decide)) (by decide))) (by grind)
      have h2 : 14400 / (((1 : Nat) : Rat) + 14399) = 1 :=
        rat_div_eq_int (Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (by decide) (by decide))) (by grind)
      rw [h1, h2, rat_min_eq_left Rat.le_refl]
  · intro ⟨hB2, h178⟩
    have hBge2 : (2 : Rat) ≤ (B : Rat) := rat_natCast_le hB2
    have hBle178 : (B : Rat) ≤ 178 := rat_natCast_le h178
    have hd_e3 : (0 : Rat) < 81 * (B : Rat) + 115 :=
      rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) hBpos) (by decide)
    have hd_e2_1 : (0 : Rat) < 289 * (B : Rat) + 611 :=
      rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) hBpos) (by decide)
    have hd_e2_2 : (0 : Rat) < (B : Rat) + 14399 :=
      rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hle_e3 : alphaNVFP6E3M2 B ≤ (80 * (B : Rat) + 116) / (81 * (B : Rat) + 115) :=
      rat_min_le_left _ _
    refine rat_lt_of_le_of_lt hle_e3 ?_
    apply rat_lt_min2
    · apply rat_div_lt_div_of_cross hd_e3 hd_e2_1; apply rat_lt_of_sub_pos
      have heq : (288 * (B : Rat) + 612) * (81 * (B : Rat) + 115) -
          (80 * (B : Rat) + 116) * (289 * (B : Rat) + 611) =
          912 + (208 * ((B : Rat) - 2) * ((B : Rat) - 2) + 1120 * ((B : Rat) - 2)) := by grind
      rw [heq]
      exact rat_add_pos_of_pos_of_nonneg (by decide)
        (rat_add_nonneg
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge2)) (rat_sub_nonneg hBge2))
          (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge2)))
    · apply rat_div_lt_div_of_cross hd_e3 hd_e2_2; apply rat_lt_of_sub_pos
      have heq : 14400 * (81 * (B : Rat) + 115) - (80 * (B : Rat) + 116) * ((B : Rat) + 14399) =
          7788 + (80 * ((B : Rat) - 2) * (178 - (B : Rat)) + 36 * (178 - (B : Rat))) := by grind
      rw [heq]
      exact rat_add_pos_of_pos_of_nonneg (by decide)
        (rat_add_nonneg
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge2)) (rat_sub_nonneg hBle178))
          (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBle178)))
  · intro h179
    have hBge179 : (179 : Rat) ≤ (B : Rat) := rat_natCast_le h179
    have hd_e2_2 : (0 : Rat) < (B : Rat) + 14399 :=
      rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hd_e3_1 : (0 : Rat) < 81 * (B : Rat) + 115 :=
      rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) hBpos) (by decide)
    have hd_e3_2 : (0 : Rat) < (B : Rat) + 802815 :=
      rat_add_pos_of_pos_of_nonneg hBpos (by decide)
    have hle_e2 : alphaNVFP6E2M3 B ≤ 14400 / ((B : Rat) + 14399) := rat_min_le_right _ _
    refine rat_lt_of_le_of_lt hle_e2 ?_
    apply rat_lt_min2
    · apply rat_div_lt_div_of_cross hd_e2_2 hd_e3_1; apply rat_lt_of_sub_pos
      have heq : (80 * (B : Rat) + 116) * ((B : Rat) + 14399) - 14400 * (81 * (B : Rat) + 115) =
          6408 + (80 * ((B : Rat) - 179) * ((B : Rat) - 179) + 14276 * ((B : Rat) - 179)) := by grind
      rw [heq]
      exact rat_add_pos_of_pos_of_nonneg (by decide)
        (rat_add_nonneg
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge179)) (rat_sub_nonneg hBge179))
          (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge179)))
    · apply rat_div_lt_div_of_cross hd_e2_2 hd_e3_2; apply rat_lt_of_sub_pos
      have heq : 802816 * ((B : Rat) + 14399) - 14400 * ((B : Rat) + 802815) =
          140338048 + 788416 * ((B : Rat) - 179) := by grind
      rw [heq]
      exact rat_add_pos_of_pos_of_nonneg (by decide)
        (Rat.mul_nonneg (by decide) (rat_sub_nonneg hBge179))

end Mxfp6Ef21Rotations
