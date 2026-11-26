/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SoapVertexFourthRoot.Algebra

/-!
# Fast Pure-`Int` Interval Certificate Engine & 5-Step Confinement Theorems (`soap-vertex-fourth-root`)

Certifies continuous worst-case 5-step confinement for all four Cluster 04 (`I031` + `I032`)
schedules over `Rat` with zero `native_decide`, zero Mathlib, and zero `sorry`:
- `bf16_fourth_root_dp5_certified` (`inv4_vertex_bf16_e2`, `[965/1000, 1039/1000]`)
- `bf16_fourth_root_eps1e4_certified` (`inv4_vertex_bf16_e4`, `[935/1000, 1049/1000]`)
- `fp8_hybrid_fourth_root_dp5_certified` (`inv4_vertex_fp8hyb_e2`, `[652/1000, 1329/1000]`)
- `fp8_pure_fourth_root_linear_dp5_certified` (`inv4_linear_fp8_e2`, `[257/1000, 1654/1000]`)
-/

namespace SoapVertexFourthRoot

/-! ## Unnormalized Exact Rational Pairs (`QPair`) for Fast Kernel `decide` -/

/-- Unnormalized rational pair `num / den` with positive denominator `0 < den`.
Avoids `Rat.normalize` / `Nat.gcd` during kernel `decide` reduction. -/
structure QPair where
  num : Int
  den : Int

abbrev QPair.ok (q : QPair) : Prop := (0 : Int) < q.den

def QPair.toRat (q : QPair) : Rat := (q.num : Rat) / (q.den : Rat)

def qAdd (a b : QPair) : QPair := ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩
def qSub (a b : QPair) : QPair := ⟨a.num * b.den - b.num * a.den, a.den * b.den⟩
def qMul (a b : QPair) : QPair := ⟨a.num * b.num, a.den * b.den⟩
def qSq  (a : QPair) : QPair := ⟨a.num * a.num, a.den * a.den⟩
def qPow4 (a : QPair) : QPair := qSq (qSq a)
def qPow8 (a : QPair) : QPair := qSq (qPow4 a)

def qLeB (a b : QPair) : Bool := decide (a.num * b.den ≤ b.num * a.den)
def qLtB (a b : QPair) : Bool := decide (a.num * b.den < b.num * a.den)

private theorem int_cast_pos {d : Int} (hd : (0 : Int) < d) : (0 : Rat) < (d : Rat) := by
  have h1 : (0 : Rat) ≤ (d : Rat) := Rat.intCast_le_intCast.mpr (Int.le_of_lt hd)
  have hne : (d : Rat) ≠ 0 := by
    intro h
    have : d = 0 := Rat.intCast_inj.mp h
    omega
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

private theorem int_cast_ne_zero {d : Int} (hd : (0 : Int) < d) : (d : Rat) ≠ 0 :=
  Rat.ne_of_gt (int_cast_pos hd)

private theorem qAdd_ok {a b : QPair} (ha : a.ok) (hb : b.ok) : (qAdd a b).ok :=
  Int.mul_pos ha hb

private theorem qSub_ok {a b : QPair} (ha : a.ok) (hb : b.ok) : (qSub a b).ok :=
  Int.mul_pos ha hb

private theorem qMul_ok {a b : QPair} (ha : a.ok) (hb : b.ok) : (qMul a b).ok :=
  Int.mul_pos ha hb

private theorem qSq_ok {a : QPair} (ha : a.ok) : (qSq a).ok :=
  Int.mul_pos ha ha

private theorem qPow4_ok {a : QPair} (ha : a.ok) : (qPow4 a).ok :=
  qSq_ok (qSq_ok ha)

private theorem qPow8_ok {a : QPair} (ha : a.ok) : (qPow8 a).ok :=
  qSq_ok (qPow4_ok ha)

private theorem rat_div_eq_of_mul {x y p q : Rat} (hy : y ≠ 0) (hq : q ≠ 0)
    (h : x * q = p * y) : x / y = p / q := by
  have hyi : y * y⁻¹ = 1 := Rat.mul_inv_cancel y hy
  have hqi : q * q⁻¹ = 1 := Rat.mul_inv_cancel q hq
  rw [Rat.div_def, Rat.div_def]
  calc
    x * y⁻¹ = (x * (q * q⁻¹)) * y⁻¹ := by rw [hqi]; grind
    _ = (x * q) * (q⁻¹ * y⁻¹) := by grind
    _ = (p * y) * (q⁻¹ * y⁻¹) := by rw [h]
    _ = p * q⁻¹ * (y * y⁻¹) := by grind
    _ = p * q⁻¹ * 1 := by rw [hyi]
    _ = p * q⁻¹ := by grind

private theorem qAdd_toRat {a b : QPair} (ha : a.ok) (hb : b.ok) :
    (qAdd a b).toRat = a.toRat + b.toRat := by
  unfold qAdd QPair.toRat
  have hda : (a.den : Rat) ≠ 0 := int_cast_ne_zero ha
  have hdb : (b.den : Rat) ≠ 0 := int_cast_ne_zero hb
  have hdab : ((a.den * b.den : Int) : Rat) ≠ 0 := int_cast_ne_zero (Int.mul_pos ha hb)
  have h1 : (a.num : Rat) / (a.den : Rat) + (b.num : Rat) / (b.den : Rat) =
      ((a.num : Rat) * (b.den : Rat) + (b.num : Rat) * (a.den : Rat)) /
        ((a.den : Rat) * (b.den : Rat)) := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hda
    have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hdb
    have hab : (a.den : Rat) * (b.den : Rat) ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact hda h
      | inr h => exact hdb h
    have hiab : ((a.den : Rat) * (b.den : Rat)) * ((a.den : Rat) * (b.den : Rat))⁻¹ = 1 :=
      Rat.mul_inv_cancel _ hab
    have hmul : ((a.den : Rat) * (b.den : Rat)) *
        ((a.num : Rat) * (a.den : Rat)⁻¹ + (b.num : Rat) * (b.den : Rat)⁻¹) =
        (a.num : Rat) * (b.den : Rat) + (b.num : Rat) * (a.den : Rat) := by
      calc
        ((a.den : Rat) * (b.den : Rat)) *
            ((a.num : Rat) * (a.den : Rat)⁻¹ + (b.num : Rat) * (b.den : Rat)⁻¹)
            = (a.num : Rat) * (b.den : Rat) * ((a.den : Rat) * (a.den : Rat)⁻¹) +
              (b.num : Rat) * (a.den : Rat) * ((b.den : Rat) * (b.den : Rat)⁻¹) := by grind
        _ = (a.num : Rat) * (b.den : Rat) * 1 + (b.num : Rat) * (a.den : Rat) * 1 := by
              rw [hia, hib]
        _ = (a.num : Rat) * (b.den : Rat) + (b.num : Rat) * (a.den : Rat) := by grind
    calc
      (a.num : Rat) * (a.den : Rat)⁻¹ + (b.num : Rat) * (b.den : Rat)⁻¹
          = (((a.den : Rat) * (b.den : Rat)) * ((a.den : Rat) * (b.den : Rat))⁻¹) *
              ((a.num : Rat) * (a.den : Rat)⁻¹ + (b.num : Rat) * (b.den : Rat)⁻¹) := by
            rw [hiab]; grind
      _ = (((a.den : Rat) * (b.den : Rat)) *
            ((a.num : Rat) * (a.den : Rat)⁻¹ + (b.num : Rat) * (b.den : Rat)⁻¹)) *
            ((a.den : Rat) * (b.den : Rat))⁻¹ := by grind
      _ = ((a.num : Rat) * (b.den : Rat) + (b.num : Rat) * (a.den : Rat)) *
            ((a.den : Rat) * (b.den : Rat))⁻¹ := by rw [hmul]
  rw [h1]
  simp only [Rat.intCast_add, Rat.intCast_mul]

private theorem qSub_toRat {a b : QPair} (ha : a.ok) (hb : b.ok) :
    (qSub a b).toRat = a.toRat - b.toRat := by
  have hb' : (⟨-b.num, b.den⟩ : QPair).ok := hb
  have h := qAdd_toRat ha hb'
  have heq : qSub a b = qAdd a ⟨-b.num, b.den⟩ := by
    unfold qSub qAdd
    simp only [QPair.mk.injEq]
    grind
  rw [heq, h]
  unfold QPair.toRat
  simp only [Rat.intCast_neg]
  rw [Rat.div_def, Rat.div_def]
  grind

private theorem qMul_toRat {a b : QPair} (ha : a.ok) (hb : b.ok) :
    (qMul a b).toRat = a.toRat * b.toRat := by
  unfold qMul QPair.toRat
  have hda : (a.den : Rat) ≠ 0 := int_cast_ne_zero ha
  have hdb : (b.den : Rat) ≠ 0 := int_cast_ne_zero hb
  have hab : (a.den : Rat) * (b.den : Rat) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hda h
    | inr h => exact hdb h
  simp only [Rat.intCast_mul]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hda
  have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hdb
  have hiab : ((a.den : Rat) * (b.den : Rat)) * ((a.den : Rat) * (b.den : Rat))⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hab
  have hinv : ((a.den : Rat) * (b.den : Rat))⁻¹ = (a.den : Rat)⁻¹ * (b.den : Rat)⁻¹ := by
    have hdiff : ((a.den : Rat) * (b.den : Rat)) *
        (((a.den : Rat) * (b.den : Rat))⁻¹ - (a.den : Rat)⁻¹ * (b.den : Rat)⁻¹) = 0 := by
      calc
        ((a.den : Rat) * (b.den : Rat)) *
            (((a.den : Rat) * (b.den : Rat))⁻¹ - (a.den : Rat)⁻¹ * (b.den : Rat)⁻¹)
            = ((a.den : Rat) * (b.den : Rat)) * ((a.den : Rat) * (b.den : Rat))⁻¹ -
              ((a.den : Rat) * (a.den : Rat)⁻¹) * ((b.den : Rat) * (b.den : Rat)⁻¹) := by grind
        _ = 1 - 1 * 1 := by rw [hiab, hia, hib]
        _ = 0 := by grind
    cases Rat.mul_eq_zero.mp hdiff with
    | inl h => exact False.elim (hab h)
    | inr h => grind
  rw [hinv]
  grind

private theorem qSq_toRat {a : QPair} (ha : a.ok) :
    (qSq a).toRat = a.toRat * a.toRat :=
  qMul_toRat ha ha

private theorem qPow4_toRat {a : QPair} (ha : a.ok) :
    (qPow4 a).toRat = ratPow4 a.toRat := by
  unfold qPow4 ratPow4
  rw [qSq_toRat (qSq_ok ha), qSq_toRat ha]

private theorem qPow8_toRat {a : QPair} (ha : a.ok) :
    (qPow8 a).toRat = ratPow8 a.toRat := by
  unfold qPow8 ratPow8
  rw [qSq_toRat (qPow4_ok ha), qPow4_toRat ha]

private theorem qLeB_sound {a b : QPair} (ha : a.ok) (hb : b.ok) (h : qLeB a b = true) :
    a.toRat ≤ b.toRat := by
  have hint : a.num * b.den ≤ b.num * a.den := of_decide_eq_true h
  have hrat : (a.num : Rat) * (b.den : Rat) ≤ (b.num : Rat) * (a.den : Rat) := by
    have := Rat.intCast_le_intCast.mpr hint
    simp only [Rat.intCast_mul] at this
    exact this
  have hda : (0 : Rat) < (a.den : Rat) := int_cast_pos ha
  have hdb : (0 : Rat) < (b.den : Rat) := int_cast_pos hb
  have hdai : (0 : Rat) ≤ (a.den : Rat)⁻¹ := by
    cases Rat.le_total (a := (0 : Rat)) (b := (a.den : Rat)⁻¹) with
    | inl h1 => exact h1
    | inr h1 =>
      have hprod := rat_mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hda)
      rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hda)] at hprod
      have : (1 : Rat) ≤ 0 := by grind
      exact False.elim (Rat.not_le.mpr (by grind : (0 : Rat) < 1) this)
  have hdbi : (0 : Rat) ≤ (b.den : Rat)⁻¹ := by
    cases Rat.le_total (a := (0 : Rat)) (b := (b.den : Rat)⁻¹) with
    | inl h1 => exact h1
    | inr h1 =>
      have hprod := rat_mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hdb)
      rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hdb)] at hprod
      have : (1 : Rat) ≤ 0 := by grind
      exact False.elim (Rat.not_le.mpr (by grind : (0 : Rat) < 1) this)
  have hinv_nn : (0 : Rat) ≤ (a.den : Rat)⁻¹ * (b.den : Rat)⁻¹ := Rat.mul_nonneg hdai hdbi
  have hscaled := rat_mul_le_mul_of_nonneg_right hrat hinv_nn
  have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hda)
  have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdb)
  have hlhs : (a.num : Rat) * (b.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹) = a.toRat := by
    unfold QPair.toRat
    rw [Rat.div_def]
    calc
      (a.num : Rat) * (b.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹)
          = (a.num : Rat) * (a.den : Rat)⁻¹ * ((b.den : Rat) * (b.den : Rat)⁻¹) := by grind
      _ = (a.num : Rat) * (a.den : Rat)⁻¹ * 1 := by rw [hib]
      _ = (a.num : Rat) * (a.den : Rat)⁻¹ := by grind
  have hrhs : (b.num : Rat) * (a.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹) = b.toRat := by
    unfold QPair.toRat
    rw [Rat.div_def]
    calc
      (b.num : Rat) * (a.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹)
          = (b.num : Rat) * (b.den : Rat)⁻¹ * ((a.den : Rat) * (a.den : Rat)⁻¹) := by grind
      _ = (b.num : Rat) * (b.den : Rat)⁻¹ * 1 := by rw [hia]
      _ = (b.num : Rat) * (b.den : Rat)⁻¹ := by grind
  rw [hlhs, hrhs] at hscaled
  exact hscaled

private theorem qLtB_sound {a b : QPair} (ha : a.ok) (hb : b.ok) (h : qLtB a b = true) :
    a.toRat < b.toRat := by
  have hint : a.num * b.den < b.num * a.den := of_decide_eq_true h
  have hle : a.toRat ≤ b.toRat := qLeB_sound ha hb (decide_eq_true (Int.le_of_lt hint))
  have hne : a.toRat ≠ b.toRat := by
    intro heq
    unfold QPair.toRat at heq
    have hda : (a.den : Rat) ≠ 0 := int_cast_ne_zero ha
    have hdb : (b.den : Rat) ≠ 0 := int_cast_ne_zero hb
    have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hda
    have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hdb
    rw [Rat.div_def, Rat.div_def] at heq
    have hcross : (a.num : Rat) * (b.den : Rat) = (b.num : Rat) * (a.den : Rat) := by
      calc
        (a.num : Rat) * (b.den : Rat)
            = ((a.num : Rat) * (a.den : Rat)⁻¹) * ((a.den : Rat) * (b.den : Rat)) := by
              have : (a.num : Rat) * (a.den : Rat)⁻¹ * ((a.den : Rat) * (b.den : Rat)) =
                  (a.num : Rat) * (b.den : Rat) * ((a.den : Rat) * (a.den : Rat)⁻¹) := by grind
              rw [this, hia]; grind
        _ = ((b.num : Rat) * (b.den : Rat)⁻¹) * ((a.den : Rat) * (b.den : Rat)) := by rw [heq]
        _ = (b.num : Rat) * (a.den : Rat) * ((b.den : Rat) * (b.den : Rat)⁻¹) := by grind
        _ = (b.num : Rat) * (a.den : Rat) * 1 := by rw [hib]
        _ = (b.num : Rat) * (a.den : Rat) := by grind
    have hcast : ((a.num * b.den : Int) : Rat) = ((b.num * a.den : Int) : Rat) := by
      simp only [Rat.intCast_mul]
      exact hcross
    have heqInt : a.num * b.den = b.num * a.den := Rat.intCast_inj.mp hcast
    omega
  exact Rat.lt_of_le_of_ne hle hne

/-! ## Subinterval Checkers & Soundness -/

/-- Exact pure-`Int` checker for one subinterval `[a, b]` of a vertex-form `G^{-1/4}` step. -/
def checkVertexSub (α β μ lo4 hi4 lo8 hi8 a b yLo yHi : QPair) : Bool :=
  let dminSq :=
    if qLeB a μ && qLeB μ b then ⟨0, 1⟩
    else if qLtB μ a then qSq (qSub a μ)
    else qSq (qSub μ b)
  let da := qSq (qSub a μ)
  let db := qSq (qSub b μ)
  let dmaxSq := if qLeB da db then db else da
  let qLo := qAdd α (qMul (qMul lo4 β) dminSq)
  let qHi := qAdd α (qMul (qMul hi4 β) dmaxSq)
  let vLo := qMul (qMul lo8 a) (qPow4 qLo)
  let vHi := qMul (qMul hi8 b) (qPow4 qHi)
  qLeB yLo vLo && qLeB vHi yHi

/-- Exact pure-`Int` checker for one subinterval `[a, b]` of a linear coupled `G^{-1/4}` step. -/
def checkLinearSub (p0 p1 oneSubU oneAddU lo8 hi8 a b yLo yHi : QPair) : Bool :=
  let qLo := qAdd p0 (qMul (qMul p1 oneAddU) b)
  let qHi := qAdd p0 (qMul (qMul p1 oneSubU) a)
  let vLo := qMul (qMul lo8 a) (qPow4 qLo)
  let vHi := qMul (qMul hi8 b) (qPow4 qHi)
  qLtB ⟨0, 1⟩ qLo && qLeB yLo vLo && qLeB vHi yHi

private theorem checkVertexSub_sound
    (α β μ oneSubU oneAddU a b yLo yHi : QPair) (u : Rat)
    (hαok : α.ok) (hβok : β.ok) (hμok : μ.ok)
    (hsok : oneSubU.ok) (haok : oneAddU.ok)
    (hAok : a.ok) (hBok : b.ok) (hyLok : yLo.ok) (hyHok : yHi.ok)
    (hαpos : (0 : Rat) < α.toRat) (hβnn : (0 : Rat) ≤ β.toRat)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1)
    (h1su : oneSubU.toRat = 1 - u) (h1au : oneAddU.toRat = 1 + u)
    (hApos : (0 : Rat) < a.toRat)
    (hchk : checkVertexSub α β μ (qPow4 oneSubU) (qPow4 oneAddU)
              (qPow8 oneSubU) (qPow8 oneAddU) a b yLo yHi = true)
    {m y : Rat} (hmL : a.toRat ≤ m) (hmR : m ≤ b.toRat)
    (hstep : NoisyVertexStep4 α.toRat β.toRat μ.toRat u m y) :
    yLo.toRat ≤ y ∧ y ≤ yHi.toRat := by
  have hmPos : (0 : Rat) < m := rat_lt_of_lt_of_le hApos hmL
  have ⟨henvL, henvR⟩ := noisyVertexStep4_envelope α.toRat β.toRat μ.toRat u m y
    hαpos hβnn hu0 hu1 hmPos hstep
  unfold checkVertexSub at hchk
  rcases Bool.and_eq_true_iff.mp hchk with ⟨hchkL, hchkR⟩
  -- Auxiliary ok proofs
  have hlo4ok : (qPow4 oneSubU).ok := qPow4_ok hsok
  have hhi4ok : (qPow4 oneAddU).ok := qPow4_ok haok
  have hlo8ok : (qPow8 oneSubU).ok := qPow8_ok hsok
  have hhi8ok : (qPow8 oneAddU).ok := qPow8_ok haok
  have hdaok : (qSq (qSub a μ)).ok := qSq_ok (qSub_ok hAok hμok)
  have hdbok : (qSq (qSub b μ)).ok := qSq_ok (qSub_ok hBok hμok)
  -- dminSq properties
  let dminSq :=
    if qLeB a μ && qLeB μ b then (⟨0, 1⟩ : QPair)
    else if qLtB μ a then qSq (qSub a μ)
    else qSq (qSub μ b)
  have hdmin_ok : dminSq.ok := by
    dsimp [dminSq]
    split
    · exact by decide
    · split
      · exact hdaok
      · exact qSq_ok (qSub_ok hμok hBok)
  have hdmin_nn : (0 : Rat) ≤ dminSq.toRat := by
    dsimp [dminSq]
    split
    · unfold QPair.toRat; grind
    · split
      · rw [qSq_toRat (qSub_ok hAok hμok)]; exact rat_sq_nonneg _
      · rw [qSq_toRat (qSub_ok hμok hBok)]; exact rat_sq_nonneg _
  have hdmin_le : dminSq.toRat ≤ (m - μ.toRat) * (m - μ.toRat) := by
    dsimp [dminSq]
    split
    · unfold QPair.toRat
      have : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
      rw [this]; exact rat_sq_nonneg _
    · rename_i hnotmid
      split
      · rename_i hlt
        have hμa : μ.toRat < a.toRat := qLtB_sound hμok hAok hlt
        rw [qSq_toRat (qSub_ok hAok hμok), qSub_toRat hAok hμok]
        have hnn : (0 : Rat) ≤ a.toRat - μ.toRat := rat_sub_nonneg (Rat.le_of_lt hμa)
        have hle : a.toRat - μ.toRat ≤ m - μ.toRat := by
          have := Rat.add_le_add_right (c := -μ.toRat) |>.mpr hmL
          grind
        exact rat_sq_le_sq_of_nonneg hnn hle
      · rename_i hnotlt
        -- Since ¬(a ≤ μ ∧ μ ≤ b) and ¬(μ < a), we must have b < μ, so 0 ≤ μ - b ≤ μ - m
        have haμ : a.toRat ≤ μ.toRat := by
          cases Rat.le_total (a := a.toRat) (b := μ.toRat) with
          | inl h => exact h
          | inr h =>
            by_cases heq : a.toRat = μ.toRat
            · rw [heq]; exact Rat.le_refl
            · have hlt' : μ.toRat < a.toRat := Rat.lt_of_le_of_ne h (Ne.symm heq)
              -- Contradicts hnotlt via qLtB
              have hltInt : μ.num * a.den < a.num * μ.den := by
                have hda : (0 : Rat) < (a.den : Rat) := int_cast_pos hAok
                have hdμ : (0 : Rat) < (μ.den : Rat) := int_cast_pos hμok
                have hmul := rat_mul_le_mul_of_nonneg_right (Rat.le_of_lt hlt')
                  (Rat.mul_nonneg (Rat.le_of_lt hda) (Rat.le_of_lt hdμ))
                unfold QPair.toRat at hmul hlt'
                have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hda)
                have hiμ : (μ.den : Rat) * (μ.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdμ)
                rw [Rat.div_def, Rat.div_def] at hmul hlt'
                have hl : (μ.num : Rat) * (μ.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat)) =
                    (μ.num : Rat) * (a.den : Rat) := by
                  calc (μ.num : Rat) * (μ.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat))
                      = (μ.num : Rat) * (a.den : Rat) * ((μ.den : Rat) * (μ.den : Rat)⁻¹) := by grind
                    _ = (μ.num : Rat) * (a.den : Rat) * 1 := by rw [hiμ]
                    _ = (μ.num : Rat) * (a.den : Rat) := by grind
                have hr : (a.num : Rat) * (a.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat)) =
                    (a.num : Rat) * (μ.den : Rat) := by
                  calc (a.num : Rat) * (a.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat))
                      = (a.num : Rat) * (μ.den : Rat) * ((a.den : Rat) * (a.den : Rat)⁻¹) := by grind
                    _ = (a.num : Rat) * (μ.den : Rat) * 1 := by rw [hia]
                    _ = (a.num : Rat) * (μ.den : Rat) := by grind
                rw [hl, hr] at hmul
                have hleInt : μ.num * a.den ≤ a.num * μ.den := by
                  have : ((μ.num * a.den : Int) : Rat) ≤ ((a.num * μ.den : Int) : Rat) := by
                    simp only [Rat.intCast_mul]; exact hmul
                  exact Rat.intCast_le_intCast.mp this
                have hneInt : μ.num * a.den ≠ a.num * μ.den := by
                  intro heqI
                  have heqR : (μ.num : Rat) * (a.den : Rat) = (a.num : Rat) * (μ.den : Rat) := by
                    have := congrArg (fun z : Int => (z : Rat)) heqI
                    simp only [Rat.intCast_mul] at this
                    exact this
                  have hdiv := rat_div_eq_of_mul (Rat.ne_of_gt hdμ) (Rat.ne_of_gt hda) heqR
                  rw [Rat.div_def, Rat.div_def] at hdiv
                  rw [hdiv] at hlt'
                  exact Rat.lt_irrefl hlt'
                omega
              have : qLtB μ a = true := decide_eq_true hltInt
              exact False.elim (hnotlt this)
        have hbμ : b.toRat ≤ μ.toRat := by
          cases Rat.le_total (a := b.toRat) (b := μ.toRat) with
          | inl h => exact h
          | inr hμb =>
            -- Both a ≤ μ and μ ≤ b hold, contradicting hnotmid
            have h1 : qLeB a μ = true := by
              unfold qLeB
              apply decide_eq_true
              have hda : (0 : Rat) < (a.den : Rat) := int_cast_pos hAok
              have hdμ : (0 : Rat) < (μ.den : Rat) := int_cast_pos hμok
              have hmul := rat_mul_le_mul_of_nonneg_right haμ
                (Rat.mul_nonneg (Rat.le_of_lt hda) (Rat.le_of_lt hdμ))
              unfold QPair.toRat at hmul
              have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hda)
              have hiμ : (μ.den : Rat) * (μ.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdμ)
              rw [Rat.div_def, Rat.div_def] at hmul
              have hl : (a.num : Rat) * (a.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat)) =
                  (a.num : Rat) * (μ.den : Rat) := by
                calc (a.num : Rat) * (a.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat))
                    = (a.num : Rat) * (μ.den : Rat) * ((a.den : Rat) * (a.den : Rat)⁻¹) := by grind
                  _ = (a.num : Rat) * (μ.den : Rat) * 1 := by rw [hia]
                  _ = (a.num : Rat) * (μ.den : Rat) := by grind
              have hr : (μ.num : Rat) * (μ.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat)) =
                  (μ.num : Rat) * (a.den : Rat) := by
                calc (μ.num : Rat) * (μ.den : Rat)⁻¹ * ((a.den : Rat) * (μ.den : Rat))
                    = (μ.num : Rat) * (a.den : Rat) * ((μ.den : Rat) * (μ.den : Rat)⁻¹) := by grind
                  _ = (μ.num : Rat) * (a.den : Rat) * 1 := by rw [hiμ]
                  _ = (μ.num : Rat) * (a.den : Rat) := by grind
              rw [hl, hr] at hmul
              have : ((a.num * μ.den : Int) : Rat) ≤ ((μ.num * a.den : Int) : Rat) := by
                simp only [Rat.intCast_mul]; exact hmul
              exact Rat.intCast_le_intCast.mp this
            have h2 : qLeB μ b = true := by
              unfold qLeB
              apply decide_eq_true
              have hdb : (0 : Rat) < (b.den : Rat) := int_cast_pos hBok
              have hdμ : (0 : Rat) < (μ.den : Rat) := int_cast_pos hμok
              have hmul := rat_mul_le_mul_of_nonneg_right hμb
                (Rat.mul_nonneg (Rat.le_of_lt hdb) (Rat.le_of_lt hdμ))
              unfold QPair.toRat at hmul
              have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdb)
              have hiμ : (μ.den : Rat) * (μ.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdμ)
              rw [Rat.div_def, Rat.div_def] at hmul
              have hl : (μ.num : Rat) * (μ.den : Rat)⁻¹ * ((b.den : Rat) * (μ.den : Rat)) =
                  (μ.num : Rat) * (b.den : Rat) := by
                calc (μ.num : Rat) * (μ.den : Rat)⁻¹ * ((b.den : Rat) * (μ.den : Rat))
                    = (μ.num : Rat) * (b.den : Rat) * ((μ.den : Rat) * (μ.den : Rat)⁻¹) := by grind
                  _ = (μ.num : Rat) * (b.den : Rat) * 1 := by rw [hiμ]
                  _ = (μ.num : Rat) * (b.den : Rat) := by grind
              have hr : (b.num : Rat) * (b.den : Rat)⁻¹ * ((b.den : Rat) * (μ.den : Rat)) =
                  (b.num : Rat) * (μ.den : Rat) := by
                calc (b.num : Rat) * (b.den : Rat)⁻¹ * ((b.den : Rat) * (μ.den : Rat))
                    = (b.num : Rat) * (μ.den : Rat) * ((b.den : Rat) * (b.den : Rat)⁻¹) := by grind
                  _ = (b.num : Rat) * (μ.den : Rat) * 1 := by rw [hib]
                  _ = (b.num : Rat) * (μ.den : Rat) := by grind
              rw [hl, hr] at hmul
              have : ((μ.num * b.den : Int) : Rat) ≤ ((b.num * μ.den : Int) : Rat) := by
                simp only [Rat.intCast_mul]; exact hmul
              exact Rat.intCast_le_intCast.mp this
            have : (qLeB a μ && qLeB μ b) = true := by rw [h1, h2]; rfl
            exact False.elim (hnotmid this)
        rw [qSq_toRat (qSub_ok hμok hBok), qSub_toRat hμok hBok]
        have hnn : (0 : Rat) ≤ μ.toRat - b.toRat := rat_sub_nonneg hbμ
        have hle : μ.toRat - b.toRat ≤ μ.toRat - m := by
          have := rat_sub_nonneg hmR
          exact rat_le_of_sub_nonneg (by grind)
        have hsq := rat_sq_le_sq_of_nonneg hnn hle
        have heqsq : (μ.toRat - m) * (μ.toRat - m) = (m - μ.toRat) * (m - μ.toRat) := by grind
        rw [heqsq] at hsq
        exact hsq
  -- dmaxSq properties
  let da := qSq (qSub a μ)
  let db := qSq (qSub b μ)
  let dmaxSq := if qLeB da db then db else da
  have hdmax_ok : dmaxSq.ok := by
    dsimp [dmaxSq]; split <;> assumption
  have hdmax_ge : (m - μ.toRat) * (m - μ.toRat) ≤ dmaxSq.toRat := by
    have h1 : a.toRat - μ.toRat ≤ m - μ.toRat := by
      have := Rat.add_le_add_right (c := -μ.toRat) |>.mpr hmL; grind
    have h2 : m - μ.toRat ≤ b.toRat - μ.toRat := by
      have := Rat.add_le_add_right (c := -μ.toRat) |>.mpr hmR; grind
    have hsq := rat_sq_le_max_sq h1 h2
    have hdaR : da.toRat = (a.toRat - μ.toRat) * (a.toRat - μ.toRat) := by
      dsimp [da]; rw [qSq_toRat (qSub_ok hAok hμok), qSub_toRat hAok hμok]
    have hdbR : db.toRat = (b.toRat - μ.toRat) * (b.toRat - μ.toRat) := by
      dsimp [db]; rw [qSq_toRat (qSub_ok hBok hμok), qSub_toRat hBok hμok]
    dsimp [dmaxSq]
    split
    · rename_i hle
      have hleR : da.toRat ≤ db.toRat := qLeB_sound hdaok hdbok hle
      rw [hdaR, hdbR] at hleR
      rw [rat_max_eq_right hleR] at hsq
      rw [hdbR]; exact hsq
    · rename_i hnotle
      have hgeR : db.toRat ≤ da.toRat := by
        cases Rat.le_total (a := da.toRat) (b := db.toRat) with
        | inr h => exact h
        | inl h =>
          -- da ≤ db contradicts hnotle
          have hda_p : (0 : Rat) < (da.den : Rat) := int_cast_pos hdaok
          have hdb_p : (0 : Rat) < (db.den : Rat) := int_cast_pos hdbok
          have hmul := rat_mul_le_mul_of_nonneg_right h
            (Rat.mul_nonneg (Rat.le_of_lt hda_p) (Rat.le_of_lt hdb_p))
          unfold QPair.toRat at hmul
          have hia : (da.den : Rat) * (da.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hda_p)
          have hib : (db.den : Rat) * (db.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdb_p)
          rw [Rat.div_def, Rat.div_def] at hmul
          have hl : (da.num : Rat) * (da.den : Rat)⁻¹ * ((da.den : Rat) * (db.den : Rat)) =
              (da.num : Rat) * (db.den : Rat) := by
            calc (da.num : Rat) * (da.den : Rat)⁻¹ * ((da.den : Rat) * (db.den : Rat))
                = (da.num : Rat) * (db.den : Rat) * ((da.den : Rat) * (da.den : Rat)⁻¹) := by grind
              _ = (da.num : Rat) * (db.den : Rat) * 1 := by rw [hia]
              _ = (da.num : Rat) * (db.den : Rat) := by grind
          have hr : (db.num : Rat) * (db.den : Rat)⁻¹ * ((da.den : Rat) * (db.den : Rat)) =
              (db.num : Rat) * (da.den : Rat) := by
            calc (db.num : Rat) * (db.den : Rat)⁻¹ * ((da.den : Rat) * (db.den : Rat))
                = (db.num : Rat) * (da.den : Rat) * ((db.den : Rat) * (db.den : Rat)⁻¹) := by grind
              _ = (db.num : Rat) * (da.den : Rat) * 1 := by rw [hib]
              _ = (db.num : Rat) * (da.den : Rat) := by grind
          rw [hl, hr] at hmul
          have hleI : da.num * db.den ≤ db.num * da.den := by
            have : ((da.num * db.den : Int) : Rat) ≤ ((db.num * da.den : Int) : Rat) := by
              simp only [Rat.intCast_mul]; exact hmul
            exact Rat.intCast_le_intCast.mp this
          exact False.elim (hnotle (decide_eq_true hleI))
      rw [hdaR, hdbR] at hgeR
      rw [rat_max_eq_left hgeR] at hsq
      rw [hdaR]; exact hsq
  -- Combine into qLo, qHi, vLo, vHi
  let qLo := qAdd α (qMul (qMul (qPow4 oneSubU) β) dminSq)
  let qHi := qAdd α (qMul (qMul (qPow4 oneAddU) β) dmaxSq)
  let vLo := qMul (qMul (qPow8 oneSubU) a) (qPow4 qLo)
  let vHi := qMul (qMul (qPow8 oneAddU) b) (qPow4 qHi)
  have hqLok : qLo.ok := qAdd_ok hαok (qMul_ok (qMul_ok hlo4ok hβok) hdmin_ok)
  have hqHok : qHi.ok := qAdd_ok hαok (qMul_ok (qMul_ok hhi4ok hβok) hdmax_ok)
  have hvLok : vLo.ok := qMul_ok (qMul_ok hlo8ok hAok) (qPow4_ok hqLok)
  have hvHok : vHi.ok := qMul_ok (qMul_ok hhi8ok hBok) (qPow4_ok hqHok)
  have hqLo_R : qLo.toRat = α.toRat + ratPow4 (1 - u) * β.toRat * dminSq.toRat := by
    dsimp [qLo]
    rw [qAdd_toRat hαok (qMul_ok (qMul_ok hlo4ok hβok) hdmin_ok),
        qMul_toRat (qMul_ok hlo4ok hβok) hdmin_ok,
        qMul_toRat hlo4ok hβok, qPow4_toRat hsok, h1su]
  have hqHi_R : qHi.toRat = α.toRat + ratPow4 (1 + u) * β.toRat * dmaxSq.toRat := by
    dsimp [qHi]
    rw [qAdd_toRat hαok (qMul_ok (qMul_ok hhi4ok hβok) hdmax_ok),
        qMul_toRat (qMul_ok hhi4ok hβok) hdmax_ok,
        qMul_toRat hhi4ok hβok, qPow4_toRat haok, h1au]
  have hqLo_le : qLo.toRat ≤ qLoVertex α.toRat β.toRat μ.toRat u m := by
    rw [hqLo_R]; unfold qLoVertex
    have hcoeff_nn : (0 : Rat) ≤ ratPow4 (1 - u) * β.toRat :=
      Rat.mul_nonneg (rat_pow4_nonneg _) hβnn
    exact Rat.add_le_add_left.mpr (rat_mul_le_mul_of_nonneg_left hdmin_le hcoeff_nn)
  have hqHi_ge : qHiVertex α.toRat β.toRat μ.toRat u m ≤ qHi.toRat := by
    rw [hqHi_R]; unfold qHiVertex
    have hcoeff_nn : (0 : Rat) ≤ ratPow4 (1 + u) * β.toRat :=
      Rat.mul_nonneg (rat_pow4_nonneg _) hβnn
    exact Rat.add_le_add_left.mpr (rat_mul_le_mul_of_nonneg_left hdmax_ge hcoeff_nn)
  have hqLo_nn : (0 : Rat) ≤ qLo.toRat := by
    rw [hqLo_R]
    exact Rat.le_of_lt (rat_add_pos_of_pos_nonneg hαpos
      (Rat.mul_nonneg (Rat.mul_nonneg (rat_pow4_nonneg _) hβnn) hdmin_nn))
  have hqHiV_nn : (0 : Rat) ≤ qHiVertex α.toRat β.toRat μ.toRat u m := by
    unfold qHiVertex
    exact Rat.le_of_lt (rat_add_pos_of_pos_nonneg hαpos
      (Rat.mul_nonneg (Rat.mul_nonneg (rat_pow4_nonneg _) hβnn) (rat_sq_nonneg _)))
  have hvLo_le : vLo.toRat ≤ vertexLowerEnv4 α.toRat β.toRat μ.toRat u m := by
    dsimp [vLo]; unfold vertexLowerEnv4
    rw [qMul_toRat (qMul_ok hlo8ok hAok) (qPow4_ok hqLok),
        qMul_toRat hlo8ok hAok, qPow8_toRat hsok, qPow4_toRat hqLok, h1su]
    have hlo8_nn : (0 : Rat) ≤ ratPow8 (1 - u) := by unfold ratPow8; exact rat_sq_nonneg _
    have h1 : ratPow8 (1 - u) * a.toRat ≤ ratPow8 (1 - u) * m :=
      rat_mul_le_mul_of_nonneg_left hmL hlo8_nn
    have h2 : ratPow4 qLo.toRat ≤ ratPow4 (qLoVertex α.toRat β.toRat μ.toRat u m) :=
      rat_pow4_le_pow4_of_nonneg hqLo_nn hqLo_le
    exact rat_mul_le_mul h1 h2 (Rat.mul_nonneg hlo8_nn (Rat.le_of_lt hApos)) (rat_pow4_nonneg _)
  have hvHi_ge : vertexUpperEnv4 α.toRat β.toRat μ.toRat u m ≤ vHi.toRat := by
    dsimp [vHi]; unfold vertexUpperEnv4
    rw [qMul_toRat (qMul_ok hhi8ok hBok) (qPow4_ok hqHok),
        qMul_toRat hhi8ok hBok, qPow8_toRat haok, qPow4_toRat hqHok, h1au]
    have hhi8_nn : (0 : Rat) ≤ ratPow8 (1 + u) := by unfold ratPow8; exact rat_sq_nonneg _
    have h1 : ratPow8 (1 + u) * m ≤ ratPow8 (1 + u) * b.toRat :=
      rat_mul_le_mul_of_nonneg_left hmR hhi8_nn
    have h2 : ratPow4 (qHiVertex α.toRat β.toRat μ.toRat u m) ≤ ratPow4 qHi.toRat :=
      rat_pow4_le_pow4_of_nonneg hqHiV_nn hqHi_ge
    exact rat_mul_le_mul h1 h2 (Rat.mul_nonneg hhi8_nn (Rat.le_of_lt hmPos)) (rat_pow4_nonneg _)
  constructor
  · exact Rat.le_trans (qLeB_sound hyLok hvLok hchkL) (Rat.le_trans hvLo_le henvL)
  · exact Rat.le_trans henvR (Rat.le_trans hvHi_ge (qLeB_sound hvHok hyHok hchkR))

private theorem checkLinearSub_sound
    (p0 p1 oneSubU oneAddU a b yLo yHi : QPair) (u : Rat)
    (hp0ok : p0.ok) (hp1ok : p1.ok)
    (hsok : oneSubU.ok) (haok : oneAddU.ok)
    (hAok : a.ok) (hBok : b.ok) (hyLok : yLo.ok) (hyHok : yHi.ok)
    (hp1np : p1.toRat ≤ (0 : Rat))
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1)
    (h1su : oneSubU.toRat = 1 - u) (h1au : oneAddU.toRat = 1 + u)
    (hApos : (0 : Rat) < a.toRat)
    (hchk : checkLinearSub p0 p1 oneSubU oneAddU
              (qPow8 oneSubU) (qPow8 oneAddU) a b yLo yHi = true)
    {m y : Rat} (hmL : a.toRat ≤ m) (hmR : m ≤ b.toRat)
    (hstep : NoisyLinearStep4 p0.toRat p1.toRat u m y) :
    yLo.toRat ≤ y ∧ y ≤ yHi.toRat := by
  unfold checkLinearSub at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hchkPos, hchkL⟩, hchkR⟩
  have hlo8ok : (qPow8 oneSubU).ok := qPow8_ok hsok
  have hhi8ok : (qPow8 oneAddU).ok := qPow8_ok haok
  let qLo := qAdd p0 (qMul (qMul p1 oneAddU) b)
  let qHi := qAdd p0 (qMul (qMul p1 oneSubU) a)
  let vLo := qMul (qMul (qPow8 oneSubU) a) (qPow4 qLo)
  let vHi := qMul (qMul (qPow8 oneAddU) b) (qPow4 qHi)
  have hqLok : qLo.ok := qAdd_ok hp0ok (qMul_ok (qMul_ok hp1ok haok) hBok)
  have hqHok : qHi.ok := qAdd_ok hp0ok (qMul_ok (qMul_ok hp1ok hsok) hAok)
  have hvLok : vLo.ok := qMul_ok (qMul_ok hlo8ok hAok) (qPow4_ok hqLok)
  have hvHok : vHi.ok := qMul_ok (qMul_ok hhi8ok hBok) (qPow4_ok hqHok)
  have hqLo_pos : (0 : Rat) < qLo.toRat := by
    have h0ok : (⟨0, 1⟩ : QPair).ok := by decide
    have h := qLtB_sound h0ok hqLok hchkPos
    unfold QPair.toRat at h
    have h0 : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
    rw [h0] at h
    exact h
  have hqLo_R : qLo.toRat = p0.toRat + p1.toRat * (1 + u) * b.toRat := by
    dsimp [qLo]
    rw [qAdd_toRat hp0ok (qMul_ok (qMul_ok hp1ok haok) hBok),
        qMul_toRat (qMul_ok hp1ok haok) hBok, qMul_toRat hp1ok haok, h1au]
  have hqHi_R : qHi.toRat = p0.toRat + p1.toRat * (1 - u) * a.toRat := by
    dsimp [qHi]
    rw [qAdd_toRat hp0ok (qMul_ok (qMul_ok hp1ok hsok) hAok),
        qMul_toRat (qMul_ok hp1ok hsok) hAok, qMul_toRat hp1ok hsok, h1su]
  have hp1_1au_np : p1.toRat * (1 + u) ≤ 0 := by
    have h1au_nn : (0 : Rat) ≤ 1 + u := by
      have h1 : (1 : Rat) + 0 ≤ 1 + u := Rat.add_le_add_left (c := (1 : Rat)) |>.mpr hu0
      have h0 : (0 : Rat) ≤ 1 + 0 := by grind
      exact Rat.le_trans h0 h1
    have h := rat_mul_le_mul_of_nonneg_right hp1np h1au_nn
    grind
  have hp1_1su_np : p1.toRat * (1 - u) ≤ 0 := by
    have h1su_nn : (0 : Rat) ≤ 1 - u := Rat.le_of_lt (rat_sub_pos_of_lt hu1)
    have h := rat_mul_le_mul_of_nonneg_right hp1np h1su_nn
    grind
  have hqLo_le : qLo.toRat ≤ qLoLinear p0.toRat p1.toRat u m := by
    rw [hqLo_R]; unfold qLoLinear
    exact Rat.add_le_add_left.mpr (rat_mul_le_mul_of_nonpos_left hmR hp1_1au_np)
  have hqHi_ge : qHiLinear p0.toRat p1.toRat u m ≤ qHi.toRat := by
    rw [hqHi_R]; unfold qHiLinear
    exact Rat.add_le_add_left.mpr (rat_mul_le_mul_of_nonpos_left hmL hp1_1su_np)
  have hqLoLin_pos : (0 : Rat) < qLoLinear p0.toRat p1.toRat u m :=
    rat_lt_of_lt_of_le hqLo_pos hqLo_le
  have hmPos : (0 : Rat) < m := rat_lt_of_lt_of_le hApos hmL
  have ⟨henvL, henvR⟩ := noisyLinearStep4_envelope p0.toRat p1.toRat u m y
    hp1np hu0 hu1 hmPos hqLoLin_pos hstep
  have hqHiLin_nn : (0 : Rat) ≤ qHiLinear p0.toRat p1.toRat u m := by
    -- qLoLinear ≤ qHiLinear because p1 ≤ 0, 1 - u ≤ 1 + u, m > 0
    have hle : qLoLinear p0.toRat p1.toRat u m ≤ qHiLinear p0.toRat p1.toRat u m := by
      unfold qLoLinear qHiLinear
      have h1 : 1 - u ≤ 1 + u := by
        have := Rat.add_le_add_left (c := (1 : Rat)) |>.mpr hu0
        grind
      have h2 : p1.toRat * (1 + u) ≤ p1.toRat * (1 - u) :=
        rat_mul_le_mul_of_nonpos_left h1 hp1np
      exact Rat.add_le_add_left.mpr (rat_mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt hmPos))
    exact Rat.le_of_lt (rat_lt_of_lt_of_le hqLoLin_pos hle)
  have hvLo_le : vLo.toRat ≤ linearLowerEnv4 p0.toRat p1.toRat u m := by
    dsimp [vLo]; unfold linearLowerEnv4
    rw [qMul_toRat (qMul_ok hlo8ok hAok) (qPow4_ok hqLok),
        qMul_toRat hlo8ok hAok, qPow8_toRat hsok, qPow4_toRat hqLok, h1su]
    have hlo8_nn : (0 : Rat) ≤ ratPow8 (1 - u) := by unfold ratPow8; exact rat_sq_nonneg _
    have h1 : ratPow8 (1 - u) * a.toRat ≤ ratPow8 (1 - u) * m :=
      rat_mul_le_mul_of_nonneg_left hmL hlo8_nn
    have h2 : ratPow4 qLo.toRat ≤ ratPow4 (qLoLinear p0.toRat p1.toRat u m) :=
      rat_pow4_le_pow4_of_nonneg (Rat.le_of_lt hqLo_pos) hqLo_le
    exact rat_mul_le_mul h1 h2 (Rat.mul_nonneg hlo8_nn (Rat.le_of_lt hApos)) (rat_pow4_nonneg _)
  have hvHi_ge : linearUpperEnv4 p0.toRat p1.toRat u m ≤ vHi.toRat := by
    dsimp [vHi]; unfold linearUpperEnv4
    rw [qMul_toRat (qMul_ok hhi8ok hBok) (qPow4_ok hqHok),
        qMul_toRat hhi8ok hBok, qPow8_toRat haok, qPow4_toRat hqHok, h1au]
    have hhi8_nn : (0 : Rat) ≤ ratPow8 (1 + u) := by unfold ratPow8; exact rat_sq_nonneg _
    have h1 : ratPow8 (1 + u) * m ≤ ratPow8 (1 + u) * b.toRat :=
      rat_mul_le_mul_of_nonneg_left hmR hhi8_nn
    have h2 : ratPow4 (qHiLinear p0.toRat p1.toRat u m) ≤ ratPow4 qHi.toRat :=
      rat_pow4_le_pow4_of_nonneg hqHiLin_nn hqHi_ge
    exact rat_mul_le_mul h1 h2 (Rat.mul_nonneg hhi8_nn (Rat.le_of_lt hmPos)) (rat_pow4_nonneg _)
  constructor
  · exact Rat.le_trans (qLeB_sound hyLok hvLok hchkL) (Rat.le_trans hvLo_le henvL)
  · exact Rat.le_trans henvR (Rat.le_trans hvHi_ge (qLeB_sound hvHok hyHok hchkR))

/-! ## Uniform Partition Checker & Induction -/

def checkUniformAux (K : Nat) (L_n span DK : Int) (chk : QPair → QPair → Bool) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let a : QPair := ⟨L_n * K + span * k, DK⟩
    let b : QPair := ⟨L_n * K + span * (k + 1), DK⟩
    chk a b && checkUniformAux K L_n span DK chk k

def checkUniform (K : Nat) (L_n R_n D : Int) (chk : QPair → QPair → Bool) : Bool :=
  checkUniformAux K L_n (R_n - L_n) (D * K) chk K

private theorem checkUniformAux_sound
    (K : Nat) (L_n span DK : Int) (chk : QPair → QPair → Bool)
    (P : Rat → Prop)
    (hstep : ∀ k : Nat, k < K →
      chk ⟨L_n * K + span * k, DK⟩ ⟨L_n * K + span * (k + 1), DK⟩ = true →
      ∀ m : Rat,
        (⟨L_n * K + span * k, DK⟩ : QPair).toRat ≤ m →
        m ≤ (⟨L_n * K + span * (k + 1), DK⟩ : QPair).toRat →
        P m) :
    ∀ n : Nat, n < K →
      checkUniformAux K L_n span DK chk (n + 1) = true →
      ∀ m : Rat,
        (⟨L_n * K, DK⟩ : QPair).toRat ≤ m →
        m ≤ (⟨L_n * K + span * (n + 1 : Nat), DK⟩ : QPair).toRat →
        P m := by
  intro n
  induction n with
  | zero =>
    intro h0 hchk m hmL hmR
    unfold checkUniformAux at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨h1, _⟩
    have haEq : (⟨L_n * K + span * (0 : Nat), DK⟩ : QPair) = ⟨L_n * K, DK⟩ := by
      simp only [Int.ofNat_zero, Int.mul_zero, Int.add_zero]
    rw [← haEq] at hmL
    exact hstep 0 h0 h1 m hmL hmR
  | succ k ih =>
    intro hk hchk m hmL hmR
    unfold checkUniformAux at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨h1, h2⟩
    let mid : QPair := ⟨L_n * K + span * (k + 1 : Nat), DK⟩
    cases Rat.le_total (a := m) (b := mid.toRat) with
    | inl hle =>
      exact ih (by omega) h2 m hmL hle
    | inr hge =>
      exact hstep (k + 1) hk h1 m hge hmR

private theorem checkUniform_sound
    (K : Nat) (hK : 0 < K) (L_n R_n D : Int) (hD : (0 : Int) < D)
    (chk : QPair → QPair → Bool) (P : Rat → Prop)
    (hstep : ∀ k : Nat, k < K →
      chk ⟨L_n * K + (R_n - L_n) * k, D * K⟩ ⟨L_n * K + (R_n - L_n) * (k + 1), D * K⟩ = true →
      ∀ m : Rat,
        (⟨L_n * K + (R_n - L_n) * k, D * K⟩ : QPair).toRat ≤ m →
        m ≤ (⟨L_n * K + (R_n - L_n) * (k + 1), D * K⟩ : QPair).toRat →
        P m)
    (hchk : checkUniform K L_n R_n D chk = true) :
    ∀ m : Rat, (L_n : Rat) / (D : Rat) ≤ m → m ≤ (R_n : Rat) / (D : Rat) → P m := by
  intro m hmL hmR
  obtain ⟨k0, rfl⟩ : ∃ k0, K = k0 + 1 := ⟨K - 1, by omega⟩
  have hKpos : (0 : Int) < ((k0 + 1 : Nat) : Int) := by omega
  have hDKpos : (0 : Int) < D * ((k0 + 1 : Nat) : Int) := Int.mul_pos hD hKpos
  have hL_eq : (⟨L_n * (k0 + 1 : Nat), D * (k0 + 1 : Nat)⟩ : QPair).toRat =
      (L_n : Rat) / (D : Rat) := by
    unfold QPair.toRat
    apply rat_div_eq_of_mul (int_cast_ne_zero hDKpos) (int_cast_ne_zero hD)
    simp only [Rat.intCast_mul]
    grind
  have hR_eq : (⟨L_n * (k0 + 1 : Nat) + (R_n - L_n) * (k0 + 1 : Nat), D * (k0 + 1 : Nat)⟩ : QPair).toRat =
      (R_n : Rat) / (D : Rat) := by
    unfold QPair.toRat
    apply rat_div_eq_of_mul (int_cast_ne_zero hDKpos) (int_cast_ne_zero hD)
    simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul]
    grind
  rw [← hL_eq] at hmL
  rw [← hR_eq] at hmR
  exact checkUniformAux_sound (k0 + 1) L_n (R_n - L_n) (D * (k0 + 1 : Nat)) chk P hstep
    k0 (by omega) hchk m hmL hmR

/-- Top-level sound certificate for one vertex-form `G^{-1/4}` step on `[L_n/D, R_n/D]`. -/
def checkVertexStep (K : Nat) (L_n R_n D : Int)
    (α β μ oneSubU oneAddU yLo yHi : QPair) : Bool :=
  let lo4 := qPow4 oneSubU
  let hi4 := qPow4 oneAddU
  let lo8 := qPow8 oneSubU
  let hi8 := qPow8 oneAddU
  checkUniform K L_n R_n D (fun a b => checkVertexSub α β μ lo4 hi4 lo8 hi8 a b yLo yHi)

private theorem certifyVertexStep
    (K : Nat) (hK : 0 < K) (L_n R_n D : Int) (hD : (0 : Int) < D)
    (hLpos : (0 : Int) < L_n) (hLR : L_n ≤ R_n)
    (α β μ oneSubU oneAddU yLo yHi : QPair) (u : Rat)
    (hαok : α.ok) (hβok : β.ok) (hμok : μ.ok)
    (hsok : oneSubU.ok) (haok : oneAddU.ok)
    (hyLok : yLo.ok) (hyHok : yHi.ok)
    (hαpos : (0 : Rat) < α.toRat) (hβnn : (0 : Rat) ≤ β.toRat)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1)
    (h1su : oneSubU.toRat = 1 - u) (h1au : oneAddU.toRat = 1 + u)
    (hchk : checkVertexStep K L_n R_n D α β μ oneSubU oneAddU yLo yHi = true)
    {m y : Rat}
    (hmL : (L_n : Rat) / (D : Rat) ≤ m) (hmR : m ≤ (R_n : Rat) / (D : Rat))
    (hstep : NoisyVertexStep4 α.toRat β.toRat μ.toRat u m y) :
    yLo.toRat ≤ y ∧ y ≤ yHi.toRat := by
  have hKpos : (0 : Int) < (K : Int) := by omega
  have hDKok : (0 : Int) < D * (K : Int) := Int.mul_pos hD hKpos
  refine checkUniform_sound K hK L_n R_n D hD
    (fun a b => checkVertexSub α β μ (qPow4 oneSubU) (qPow4 oneAddU)
      (qPow8 oneSubU) (qPow8 oneAddU) a b yLo yHi)
    (fun m' => ∀ y', NoisyVertexStep4 α.toRat β.toRat μ.toRat u m' y' →
      yLo.toRat ≤ y' ∧ y' ≤ yHi.toRat)
    ?_ hchk m hmL hmR y hstep
  intro k _ hsub m' hm'L hm'R y' hstep'
  have hApos_int : (0 : Int) < L_n * (K : Int) + (R_n - L_n) * (k : Int) := by
    have h1 : (0 : Int) < L_n * (K : Int) := Int.mul_pos hLpos hKpos
    have h2 : (0 : Int) ≤ (R_n - L_n) * (k : Int) := Int.mul_nonneg (by omega) (by omega)
    omega
  have hApos : (0 : Rat) < (⟨L_n * (K : Int) + (R_n - L_n) * (k : Int), D * (K : Int)⟩ : QPair).toRat := by
    have h0ok : (⟨0, 1⟩ : QPair).ok := by decide
    have hAok : (⟨L_n * (K : Int) + (R_n - L_n) * (k : Int), D * (K : Int)⟩ : QPair).ok := hDKok
    have hlt := qLtB_sound h0ok hAok (decide_eq_true (by omega :
      (0 : Int) * (D * (K : Int)) < (L_n * (K : Int) + (R_n - L_n) * (k : Int)) * 1))
    unfold QPair.toRat at hlt
    have h0 : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
    rw [h0] at hlt
    exact hlt
  exact checkVertexSub_sound α β μ oneSubU oneAddU
    ⟨L_n * (K : Int) + (R_n - L_n) * (k : Int), D * (K : Int)⟩
    ⟨L_n * (K : Int) + (R_n - L_n) * ((k + 1 : Nat) : Int), D * (K : Int)⟩
    yLo yHi u hαok hβok hμok hsok haok hDKok hDKok hyLok hyHok
    hαpos hβnn hu0 hu1 h1su h1au hApos hsub hm'L hm'R hstep'

/-- Top-level sound certificate for one linear coupled `G^{-1/4}` step on `[L_n/D, R_n/D]`. -/
def checkLinearStep (K : Nat) (L_n R_n D : Int)
    (p0 p1 oneSubU oneAddU yLo yHi : QPair) : Bool :=
  let lo8 := qPow8 oneSubU
  let hi8 := qPow8 oneAddU
  checkUniform K L_n R_n D (fun a b => checkLinearSub p0 p1 oneSubU oneAddU lo8 hi8 a b yLo yHi)

private theorem certifyLinearStep
    (K : Nat) (hK : 0 < K) (L_n R_n D : Int) (hD : (0 : Int) < D)
    (hLpos : (0 : Int) < L_n) (hLR : L_n ≤ R_n)
    (p0 p1 oneSubU oneAddU yLo yHi : QPair) (u : Rat)
    (hp0ok : p0.ok) (hp1ok : p1.ok)
    (hsok : oneSubU.ok) (haok : oneAddU.ok)
    (hyLok : yLo.ok) (hyHok : yHi.ok)
    (hp1np : p1.toRat ≤ (0 : Rat))
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1)
    (h1su : oneSubU.toRat = 1 - u) (h1au : oneAddU.toRat = 1 + u)
    (hchk : checkLinearStep K L_n R_n D p0 p1 oneSubU oneAddU yLo yHi = true)
    {m y : Rat}
    (hmL : (L_n : Rat) / (D : Rat) ≤ m) (hmR : m ≤ (R_n : Rat) / (D : Rat))
    (hstep : NoisyLinearStep4 p0.toRat p1.toRat u m y) :
    yLo.toRat ≤ y ∧ y ≤ yHi.toRat := by
  have hKpos : (0 : Int) < (K : Int) := by omega
  have hDKok : (0 : Int) < D * (K : Int) := Int.mul_pos hD hKpos
  refine checkUniform_sound K hK L_n R_n D hD
    (fun a b => checkLinearSub p0 p1 oneSubU oneAddU (qPow8 oneSubU) (qPow8 oneAddU) a b yLo yHi)
    (fun m' => ∀ y', NoisyLinearStep4 p0.toRat p1.toRat u m' y' →
      yLo.toRat ≤ y' ∧ y' ≤ yHi.toRat)
    ?_ hchk m hmL hmR y hstep
  intro k _ hsub m' hm'L hm'R y' hstep'
  have hApos_int : (0 : Int) < L_n * (K : Int) + (R_n - L_n) * (k : Int) := by
    have h1 : (0 : Int) < L_n * (K : Int) := Int.mul_pos hLpos hKpos
    have h2 : (0 : Int) ≤ (R_n - L_n) * (k : Int) := Int.mul_nonneg (by omega) (by omega)
    omega
  have hApos : (0 : Rat) < (⟨L_n * (K : Int) + (R_n - L_n) * (k : Int), D * (K : Int)⟩ : QPair).toRat := by
    have h0ok : (⟨0, 1⟩ : QPair).ok := by decide
    have hAok : (⟨L_n * (K : Int) + (R_n - L_n) * (k : Int), D * (K : Int)⟩ : QPair).ok := hDKok
    have hlt := qLtB_sound h0ok hAok (decide_eq_true (by omega :
      (0 : Int) * (D * (K : Int)) < (L_n * (K : Int) + (R_n - L_n) * (k : Int)) * 1))
    unfold QPair.toRat at hlt
    have h0 : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
    rw [h0] at hlt
    exact hlt
  exact checkLinearSub_sound p0 p1 oneSubU oneAddU
    ⟨L_n * (K : Int) + (R_n - L_n) * (k : Int), D * (K : Int)⟩
    ⟨L_n * (K : Int) + (R_n - L_n) * ((k + 1 : Nat) : Int), D * (K : Int)⟩
    yLo yHi u hp0ok hp1ok hsok haok hDKok hDKok hyLok hyHok
    hp1np hu0 hu1 h1su h1au hApos hsub hm'L hm'R hstep'

/-! ## Theorem 4: BF16 5-Step Vertex `G^{-1/4}` (`ε = 1/100`, `inv4_vertex_bf16_e2`) -/

private theorem bf16_e2_cert1 :
    checkVertexStep 128 1 100 100 ⟨27, 32⟩ ⟨133, 64⟩ ⟨243, 256⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨448, 1000⟩ ⟨3759, 1000⟩ = true := by decide

private theorem bf16_e2_cert2 :
    checkVertexStep 128 448 3759 1000 ⟨185, 256⟩ ⟨87, 1024⟩ ⟨83, 32⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨612, 1000⟩ ⟨1930, 1000⟩ = true := by decide

private theorem bf16_e2_cert3 :
    checkVertexStep 128 612 1930 1000 ⟨207, 256⟩ ⟨87, 1024⟩ ⟨81, 32⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨911, 1000⟩ ⟨1092, 1000⟩ = true := by decide

private theorem bf16_e2_cert4 :
    checkVertexStep 128 911 1092 1000 ⟨227, 256⟩ ⟨37, 256⟩ ⟨241, 128⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨957, 1000⟩ ⟨1041, 1000⟩ = true := by decide

private theorem bf16_e2_cert5 :
    checkVertexStep 128 957 1041 1000 ⟨251, 256⟩ ⟨183, 256⟩ ⟨149, 128⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨965, 1000⟩ ⟨1039, 1000⟩ = true := by decide

theorem bf16_fourth_root_dp5_certified (m0 m5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyVertexTraj5
      bf16E2Step1 bf16E2Step2 bf16E2Step3 bf16E2Step4 bf16E2Step5 uBF16 m0 m5) :
    (965 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1039 / 1000 : Rat) := by
  rcases htraj with ⟨m1, m2, m3, m4, hs1, hs2, hs3, hs4, hs5⟩
  have hu0 : (0 : Rat) ≤ uBF16 := by unfold uBF16; grind
  have hu1 : uBF16 < 1 := by unfold uBF16; grind
  have h1su : (⟨255, 256⟩ : QPair).toRat = 1 - uBF16 := by unfold QPair.toRat uBF16; grind
  have h1au : (⟨257, 256⟩ : QPair).toRat = 1 + uBF16 := by unfold QPair.toRat uBF16; grind
  have hm0R : m0 ≤ ((100 : Int) : Rat) / ((100 : Int) : Rat) := by grind
  have ⟨h1L, h1R⟩ := certifyVertexStep 128 (by decide) 1 100 100 (by decide) (by decide) (by decide)
    ⟨27, 32⟩ ⟨133, 64⟩ ⟨243, 256⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨448, 1000⟩ ⟨3759, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e2_cert1 hlo hm0R hs1
  have ⟨h2L, h2R⟩ := certifyVertexStep 128 (by decide) 448 3759 1000 (by decide) (by decide) (by decide)
    ⟨185, 256⟩ ⟨87, 1024⟩ ⟨83, 32⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨612, 1000⟩ ⟨1930, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e2_cert2 h1L h1R hs2
  have ⟨h3L, h3R⟩ := certifyVertexStep 128 (by decide) 612 1930 1000 (by decide) (by decide) (by decide)
    ⟨207, 256⟩ ⟨87, 1024⟩ ⟨81, 32⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨911, 1000⟩ ⟨1092, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e2_cert3 h2L h2R hs3
  have ⟨h4L, h4R⟩ := certifyVertexStep 128 (by decide) 911 1092 1000 (by decide) (by decide) (by decide)
    ⟨227, 256⟩ ⟨37, 256⟩ ⟨241, 128⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨957, 1000⟩ ⟨1041, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e2_cert4 h3L h3R hs4
  exact certifyVertexStep 128 (by decide) 957 1041 1000 (by decide) (by decide) (by decide)
    ⟨251, 256⟩ ⟨183, 256⟩ ⟨149, 128⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨965, 1000⟩ ⟨1039, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e2_cert5 h4L h4R hs5

/-! ## Theorem 5: BF16 5-Step Vertex `G^{-1/4}` (`ε = 1/10000`, `inv4_vertex_bf16_e4`) -/

private theorem bf16_e4_cert1 :
    checkVertexStep 128 1 10000 10000 ⟨1, 4⟩ ⟨133, 64⟩ ⟨243, 256⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨175, 100000⟩ ⟨110585, 100000⟩ = true := by decide

private theorem bf16_e4_cert2 :
    checkVertexStep 128 175 110585 100000 ⟨1, 4⟩ ⟨9, 8⟩ ⟨243, 256⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨350, 100000⟩ ⟨15289, 100000⟩ = true := by decide

private theorem bf16_e4_cert3 :
    checkVertexStep 128 350 15289 100000 ⟨1, 4⟩ ⟨133, 64⟩ ⟨243, 256⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨62, 1000⟩ ⟨1048, 1000⟩ = true := by decide

private theorem bf16_e4_cert4 :
    checkVertexStep 128 62 1048 1000 ⟨209, 256⟩ ⟨33, 32⟩ ⟨243, 256⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨379, 1000⟩ ⟨836, 1000⟩ = true := by decide

private theorem bf16_e4_cert5 :
    checkVertexStep 128 379 836 1000 ⟨131, 128⟩ ⟨153, 256⟩ ⟨131, 128⟩
      ⟨255, 256⟩ ⟨257, 256⟩ ⟨935, 1000⟩ ⟨1049, 1000⟩ = true := by decide

theorem bf16_fourth_root_eps1e4_certified (m0 m5 : Rat)
    (hlo : (1 / 10000 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyVertexTraj5
      bf16E4Step1 bf16E4Step2 bf16E4Step3 bf16E4Step4 bf16E4Step5 uBF16 m0 m5) :
    (935 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1049 / 1000 : Rat) := by
  rcases htraj with ⟨m1, m2, m3, m4, hs1, hs2, hs3, hs4, hs5⟩
  have hu0 : (0 : Rat) ≤ uBF16 := by unfold uBF16; grind
  have hu1 : uBF16 < 1 := by unfold uBF16; grind
  have h1su : (⟨255, 256⟩ : QPair).toRat = 1 - uBF16 := by unfold QPair.toRat uBF16; grind
  have h1au : (⟨257, 256⟩ : QPair).toRat = 1 + uBF16 := by unfold QPair.toRat uBF16; grind
  have hm0R : m0 ≤ ((10000 : Int) : Rat) / ((10000 : Int) : Rat) := by grind
  have ⟨h1L, h1R⟩ := certifyVertexStep 128 (by decide) 1 10000 10000 (by decide) (by decide) (by decide)
    ⟨1, 4⟩ ⟨133, 64⟩ ⟨243, 256⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨175, 100000⟩ ⟨110585, 100000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e4_cert1 hlo hm0R hs1
  have ⟨h2L, h2R⟩ := certifyVertexStep 128 (by decide) 175 110585 100000 (by decide) (by decide) (by decide)
    ⟨1, 4⟩ ⟨9, 8⟩ ⟨243, 256⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨350, 100000⟩ ⟨15289, 100000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e4_cert2 h1L h1R hs2
  have ⟨h3L, h3R⟩ := certifyVertexStep 128 (by decide) 350 15289 100000 (by decide) (by decide) (by decide)
    ⟨1, 4⟩ ⟨133, 64⟩ ⟨243, 256⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨62, 1000⟩ ⟨1048, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e4_cert3 h2L h2R hs3
  have ⟨h4L, h4R⟩ := certifyVertexStep 128 (by decide) 62 1048 1000 (by decide) (by decide) (by decide)
    ⟨209, 256⟩ ⟨33, 32⟩ ⟨243, 256⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨379, 1000⟩ ⟨836, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e4_cert4 h3L h3R hs4
  exact certifyVertexStep 128 (by decide) 379 836 1000 (by decide) (by decide) (by decide)
    ⟨131, 128⟩ ⟨153, 256⟩ ⟨131, 128⟩ ⟨255, 256⟩ ⟨257, 256⟩ ⟨935, 1000⟩ ⟨1049, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au bf16_e4_cert5 h4L h4R hs5

/-! ## Theorem 6: Hybrid FP8 5-Step Vertex `G^{-1/4}` (`ε = 1/100`, `inv4_vertex_fp8hyb_e2`) -/

private theorem fp8hyb_e2_cert1 :
    checkVertexStep 128 1 100 100 ⟨7, 8⟩ ⟨15, 4⟩ ⟨11, 16⟩
      ⟨31, 32⟩ ⟨33, 32⟩ ⟨239, 1000⟩ ⟨4138, 1000⟩ = true := by decide

private theorem fp8hyb_e2_cert2 :
    checkVertexStep 128 239 4138 1000 ⟨5, 8⟩ ⟨11, 128⟩ ⟨3, 1⟩
      ⟨31, 32⟩ ⟨33, 32⟩ ⟨328, 1000⟩ ⟨1683, 1000⟩ = true := by decide

private theorem fp8hyb_e2_cert3 :
    checkVertexStep 128 328 1683 1000 ⟨13, 16⟩ ⟨1, 8⟩ ⟨9, 4⟩
      ⟨31, 32⟩ ⟨33, 32⟩ ⟨553, 1000⟩ ⟨1608, 1000⟩ = true := by decide

private theorem fp8hyb_e2_cert4 :
    checkVertexStep 128 553 1608 1000 ⟨7, 8⟩ ⟨7, 32⟩ ⟨13, 8⟩
      ⟨31, 32⟩ ⟨33, 32⟩ ⟨612, 1000⟩ ⟨1297, 1000⟩ = true := by decide

private theorem fp8hyb_e2_cert5 :
    checkVertexStep 128 612 1297 1000 ⟨15, 16⟩ ⟨7, 16⟩ ⟨5, 4⟩
      ⟨31, 32⟩ ⟨33, 32⟩ ⟨652, 1000⟩ ⟨1329, 1000⟩ = true := by decide

theorem fp8_hybrid_fourth_root_dp5_certified (m0 m5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyVertexTraj5
      fp8HybE2Step1 fp8HybE2Step2 fp8HybE2Step3 fp8HybE2Step4 fp8HybE2Step5 uFP8Hybrid m0 m5) :
    (652 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1329 / 1000 : Rat) := by
  rcases htraj with ⟨m1, m2, m3, m4, hs1, hs2, hs3, hs4, hs5⟩
  have hu0 : (0 : Rat) ≤ uFP8Hybrid := by unfold uFP8Hybrid; grind
  have hu1 : uFP8Hybrid < 1 := by unfold uFP8Hybrid; grind
  have h1su : (⟨31, 32⟩ : QPair).toRat = 1 - uFP8Hybrid := by unfold QPair.toRat uFP8Hybrid; grind
  have h1au : (⟨33, 32⟩ : QPair).toRat = 1 + uFP8Hybrid := by unfold QPair.toRat uFP8Hybrid; grind
  have hm0R : m0 ≤ ((100 : Int) : Rat) / ((100 : Int) : Rat) := by grind
  have ⟨h1L, h1R⟩ := certifyVertexStep 128 (by decide) 1 100 100 (by decide) (by decide) (by decide)
    ⟨7, 8⟩ ⟨15, 4⟩ ⟨11, 16⟩ ⟨31, 32⟩ ⟨33, 32⟩ ⟨239, 1000⟩ ⟨4138, 1000⟩ uFP8Hybrid
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au fp8hyb_e2_cert1 hlo hm0R hs1
  have hs2' : NoisyVertexStep4 (⟨5, 8⟩ : QPair).toRat (⟨11, 128⟩ : QPair).toRat (⟨3, 1⟩ : QPair).toRat
      uFP8Hybrid m1 m2 := by
    have heq : (⟨3, 1⟩ : QPair).toRat = (3 : Rat) := by unfold QPair.toRat; grind
    rw [heq]; exact hs2
  have ⟨h2L, h2R⟩ := certifyVertexStep 128 (by decide) 239 4138 1000 (by decide) (by decide) (by decide)
    ⟨5, 8⟩ ⟨11, 128⟩ ⟨3, 1⟩ ⟨31, 32⟩ ⟨33, 32⟩ ⟨328, 1000⟩ ⟨1683, 1000⟩ uFP8Hybrid
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au fp8hyb_e2_cert2 h1L h1R hs2'
  have ⟨h3L, h3R⟩ := certifyVertexStep 128 (by decide) 328 1683 1000 (by decide) (by decide) (by decide)
    ⟨13, 16⟩ ⟨1, 8⟩ ⟨9, 4⟩ ⟨31, 32⟩ ⟨33, 32⟩ ⟨553, 1000⟩ ⟨1608, 1000⟩ uFP8Hybrid
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au fp8hyb_e2_cert3 h2L h2R hs3
  have ⟨h4L, h4R⟩ := certifyVertexStep 128 (by decide) 553 1608 1000 (by decide) (by decide) (by decide)
    ⟨7, 8⟩ ⟨7, 32⟩ ⟨13, 8⟩ ⟨31, 32⟩ ⟨33, 32⟩ ⟨612, 1000⟩ ⟨1297, 1000⟩ uFP8Hybrid
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au fp8hyb_e2_cert4 h3L h3R hs4
  exact certifyVertexStep 128 (by decide) 612 1297 1000 (by decide) (by decide) (by decide)
    ⟨15, 16⟩ ⟨7, 16⟩ ⟨5, 4⟩ ⟨31, 32⟩ ⟨33, 32⟩ ⟨652, 1000⟩ ⟨1329, 1000⟩ uFP8Hybrid
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) (by unfold QPair.toRat; grind)
    hu0 hu1 h1su h1au fp8hyb_e2_cert5 h4L h4R hs5

/-! ## Theorem 7: Pure FP8 E4M3 5-Step Linear `G^{-1/4}` (`ε = 1/100`, `inv4_linear_fp8_e2`) -/

set_option maxRecDepth 2048 in
private theorem fp8lin_e2_cert1 :
    checkLinearStep 256 1 100 100 ⟨7, 4⟩ ⟨-9, 8⟩
      ⟨15, 16⟩ ⟨17, 16⟩ ⟨53, 1000⟩ ⟨2095, 1000⟩ = true := by decide

set_option maxRecDepth 2048 in
private theorem fp8lin_e2_cert2 :
    checkLinearStep 256 53 2095 1000 ⟨15, 8⟩ ⟨-1, 2⟩
      ⟨15, 16⟩ ⟨17, 16⟩ ⟨364, 1000⟩ ⟨6644, 1000⟩ = true := by decide

set_option maxRecDepth 2048 in
private theorem fp8lin_e2_cert3 :
    checkLinearStep 256 364 6644 1000 ⟨11, 8⟩ ⟨-13, 128⟩
      ⟨15, 16⟩ ⟨17, 16⟩ ⟨685, 1000⟩ ⟨6927, 1000⟩ = true := by decide

set_option maxRecDepth 2048 in
private theorem fp8lin_e2_cert4 :
    checkLinearStep 256 685 6927 1000 ⟨1, 1⟩ ⟨-1, 16⟩
      ⟨15, 16⟩ ⟨17, 16⟩ ⟨337, 1000⟩ ⟨2288, 1000⟩ = true := by decide

set_option maxRecDepth 2048 in
private theorem fp8lin_e2_cert5 :
    checkLinearStep 256 337 2288 1000 ⟨9, 8⟩ ⟨-5, 32⟩
      ⟨15, 16⟩ ⟨17, 16⟩ ⟨257, 1000⟩ ⟨1654, 1000⟩ = true := by decide

theorem fp8_pure_fourth_root_linear_dp5_certified (m0 m5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ m0) (hhi : m0 ≤ 1)
    (htraj : NoisyLinearTraj5
      fp8LinE2Step1 fp8LinE2Step2 fp8LinE2Step3 fp8LinE2Step4 fp8LinE2Step5 uFP8Pure m0 m5) :
    (257 / 1000 : Rat) ≤ m5 ∧ m5 ≤ (1654 / 1000 : Rat) := by
  rcases htraj with ⟨m1, m2, m3, m4, hs1, hs2, hs3, hs4, hs5⟩
  have hu0 : (0 : Rat) ≤ uFP8Pure := by unfold uFP8Pure; grind
  have hu1 : uFP8Pure < 1 := by unfold uFP8Pure; grind
  have h1su : (⟨15, 16⟩ : QPair).toRat = 1 - uFP8Pure := by unfold QPair.toRat uFP8Pure; grind
  have h1au : (⟨17, 16⟩ : QPair).toRat = 1 + uFP8Pure := by unfold QPair.toRat uFP8Pure; grind
  have hm0R : m0 ≤ ((100 : Int) : Rat) / ((100 : Int) : Rat) := by grind
  have hs1' : NoisyLinearStep4 (⟨7, 4⟩ : QPair).toRat (⟨-9, 8⟩ : QPair).toRat uFP8Pure m0 m1 := by
    have heq : (⟨-9, 8⟩ : QPair).toRat = (-9 / 8 : Rat) := by unfold QPair.toRat; grind
    rw [heq]; exact hs1
  have ⟨h1L, h1R⟩ := certifyLinearStep 256 (by decide) 1 100 100 (by decide) (by decide) (by decide)
    ⟨7, 4⟩ ⟨-9, 8⟩ ⟨15, 16⟩ ⟨17, 16⟩ ⟨53, 1000⟩ ⟨2095, 1000⟩ uFP8Pure
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) hu0 hu1 h1su h1au fp8lin_e2_cert1 hlo hm0R hs1'
  have hs2' : NoisyLinearStep4 (⟨15, 8⟩ : QPair).toRat (⟨-1, 2⟩ : QPair).toRat uFP8Pure m1 m2 := by
    have heq : (⟨-1, 2⟩ : QPair).toRat = (-1 / 2 : Rat) := by unfold QPair.toRat; grind
    rw [heq]; exact hs2
  have ⟨h2L, h2R⟩ := certifyLinearStep 256 (by decide) 53 2095 1000 (by decide) (by decide) (by decide)
    ⟨15, 8⟩ ⟨-1, 2⟩ ⟨15, 16⟩ ⟨17, 16⟩ ⟨364, 1000⟩ ⟨6644, 1000⟩ uFP8Pure
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) hu0 hu1 h1su h1au fp8lin_e2_cert2 h1L h1R hs2'
  have hs3' : NoisyLinearStep4 (⟨11, 8⟩ : QPair).toRat (⟨-13, 128⟩ : QPair).toRat uFP8Pure m2 m3 := by
    have heq : (⟨-13, 128⟩ : QPair).toRat = (-13 / 128 : Rat) := by unfold QPair.toRat; grind
    rw [heq]; exact hs3
  have ⟨h3L, h3R⟩ := certifyLinearStep 256 (by decide) 364 6644 1000 (by decide) (by decide) (by decide)
    ⟨11, 8⟩ ⟨-13, 128⟩ ⟨15, 16⟩ ⟨17, 16⟩ ⟨685, 1000⟩ ⟨6927, 1000⟩ uFP8Pure
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) hu0 hu1 h1su h1au fp8lin_e2_cert3 h2L h2R hs3'
  have hs4' : NoisyLinearStep4 (⟨1, 1⟩ : QPair).toRat (⟨-1, 16⟩ : QPair).toRat uFP8Pure m3 m4 := by
    have heq1 : (⟨1, 1⟩ : QPair).toRat = (1 : Rat) := by unfold QPair.toRat; grind
    have heq2 : (⟨-1, 16⟩ : QPair).toRat = (-1 / 16 : Rat) := by unfold QPair.toRat; grind
    rw [heq1, heq2]; exact hs4
  have ⟨h4L, h4R⟩ := certifyLinearStep 256 (by decide) 685 6927 1000 (by decide) (by decide) (by decide)
    ⟨1, 1⟩ ⟨-1, 16⟩ ⟨15, 16⟩ ⟨17, 16⟩ ⟨337, 1000⟩ ⟨2288, 1000⟩ uFP8Pure
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) hu0 hu1 h1su h1au fp8lin_e2_cert4 h3L h3R hs4'
  have hs5' : NoisyLinearStep4 (⟨9, 8⟩ : QPair).toRat (⟨-5, 32⟩ : QPair).toRat uFP8Pure m4 m5 := by
    have heq : (⟨-5, 32⟩ : QPair).toRat = (-5 / 32 : Rat) := by unfold QPair.toRat; grind
    rw [heq]; exact hs5
  exact certifyLinearStep 256 (by decide) 337 2288 1000 (by decide) (by decide) (by decide)
    ⟨9, 8⟩ ⟨-5, 32⟩ ⟨15, 16⟩ ⟨17, 16⟩ ⟨257, 1000⟩ ⟨1654, 1000⟩ uFP8Pure
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by unfold QPair.toRat; grind) hu0 hu1 h1su h1au fp8lin_e2_cert5 h4L h4R hs5'

end SoapVertexFourthRoot
