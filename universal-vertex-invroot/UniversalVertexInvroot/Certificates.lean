/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UniversalVertexInvroot.Algebra

/-!
# Fast Pure-`Int` Interval Certificate Engine & BF16 Confinement Theorems (`p ∈ {2, 3, 8}`)

Certifies continuous worst-case 6-step stationary BF16 (`u = 1/256`) confinement from
`[85/100, 115/100]` over `Rat` with zero `native_decide`, zero Mathlib, and zero `sorry`:
- `bf16_inv_sqrt_vertex_certified` (`p = 2`, `[982/1000, 1018/1000]`, `δ_M ≤ 0.018`)
- `bf16_inv_cbrt_vertex_certified` (`p = 3`, `[974/1000, 1026/1000]`, `δ_M ≤ 0.026`)
- `bf16_inv_eighth_vertex_certified` (`p = 8`, `[932/1000, 1068/1000]`, `δ_M ≤ 0.068`)
-/

namespace UniversalVertexInvroot

/-! ## Unnormalized Exact Rational Pairs (`QPair`) with Sound Dyadic Rounding -/

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

def qPow (a : QPair) : Nat → QPair
  | 0 => ⟨1, 1⟩
  | n + 1 => qMul (qPow a n) a

/-- Scale `2^40` for sound outward dyadic rounding of intermediate interval bounds. -/
def dyadicScale : Int := 1099511627776

/-- Sound downward rounding onto the `2^-40` dyadic grid (keeps `p = 8` powers compact). -/
def qFloor40 (q : QPair) : QPair :=
  ⟨(q.num * dyadicScale) / q.den, dyadicScale⟩

/-- Sound upward rounding onto the `2^-40` dyadic grid (keeps `p = 8` powers compact). -/
def qCeil40 (q : QPair) : QPair :=
  ⟨(q.num * dyadicScale + q.den - 1) / q.den, dyadicScale⟩

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

private theorem qAdd_ok {a b : QPair} (ha : a.ok) (hb : b.ok) : (qAdd a b).ok := Int.mul_pos ha hb
private theorem qSub_ok {a b : QPair} (ha : a.ok) (hb : b.ok) : (qSub a b).ok := Int.mul_pos ha hb
private theorem qMul_ok {a b : QPair} (ha : a.ok) (hb : b.ok) : (qMul a b).ok := Int.mul_pos ha hb
private theorem qSq_ok  {a : QPair} (ha : a.ok) : (qSq a).ok := Int.mul_pos ha ha

private theorem qPow_ok {a : QPair} (ha : a.ok) : ∀ n : Nat, (qPow a n).ok
  | 0 => by change (0 : Int) < 1; decide
  | n + 1 => qMul_ok (qPow_ok ha n) ha

private theorem qFloor40_ok (q : QPair) : (qFloor40 q).ok := by change (0 : Int) < dyadicScale; unfold dyadicScale; decide
private theorem qCeil40_ok  (q : QPair) : (qCeil40 q).ok  := by change (0 : Int) < dyadicScale; unfold dyadicScale; decide

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
  have hab : (a.den : Rat) * (b.den : Rat) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hda h
    | inr h => exact hdb h
  have h1 : (a.num : Rat) / (a.den : Rat) + (b.num : Rat) / (b.den : Rat) =
      ((a.num : Rat) * (b.den : Rat) + (b.num : Rat) * (a.den : Rat)) /
        ((a.den : Rat) * (b.den : Rat)) := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hda
    have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hdb
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
  simp only [Rat.intCast_mul]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, rat_inv_mul_eq hda hdb]
  grind

private theorem qSq_toRat {a : QPair} (ha : a.ok) :
    (qSq a).toRat = a.toRat * a.toRat :=
  qMul_toRat ha ha

private theorem qPow_toRat {a : QPair} (ha : a.ok) :
    ∀ n : Nat, (qPow a n).toRat = ratPow a.toRat n
  | 0 => by unfold qPow ratPow QPair.toRat; grind
  | n + 1 => by
    unfold qPow ratPow
    rw [qMul_toRat (qPow_ok ha n) ha, qPow_toRat ha n]

private theorem qLeB_sound {a b : QPair} (ha : a.ok) (hb : b.ok) (h : qLeB a b = true) :
    a.toRat ≤ b.toRat := by
  have hint : a.num * b.den ≤ b.num * a.den := of_decide_eq_true h
  have hrat : (a.num : Rat) * (b.den : Rat) ≤ (b.num : Rat) * (a.den : Rat) := by
    have := Rat.intCast_le_intCast.mpr hint
    simp only [Rat.intCast_mul] at this
    exact this
  have hda : (0 : Rat) < (a.den : Rat) := int_cast_pos ha
  have hdb : (0 : Rat) < (b.den : Rat) := int_cast_pos hb
  have hinv_nn : (0 : Rat) ≤ (a.den : Rat)⁻¹ * (b.den : Rat)⁻¹ :=
    Rat.mul_nonneg (Rat.le_of_lt (rat_inv_pos hda)) (Rat.le_of_lt (rat_inv_pos hdb))
  have hscaled := rat_mul_le_mul_of_nonneg_right hrat hinv_nn
  have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hda)
  have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdb)
  have hlhs : (a.num : Rat) * (b.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹) = a.toRat := by
    unfold QPair.toRat; rw [Rat.div_def]
    calc (a.num : Rat) * (b.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹)
        = (a.num : Rat) * (a.den : Rat)⁻¹ * ((b.den : Rat) * (b.den : Rat)⁻¹) := by grind
      _ = (a.num : Rat) * (a.den : Rat)⁻¹ * 1 := by rw [hib]
      _ = (a.num : Rat) * (a.den : Rat)⁻¹ := by grind
  have hrhs : (b.num : Rat) * (a.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹) = b.toRat := by
    unfold QPair.toRat; rw [Rat.div_def]
    calc (b.num : Rat) * (a.den : Rat) * ((a.den : Rat)⁻¹ * (b.den : Rat)⁻¹)
        = (b.num : Rat) * (b.den : Rat)⁻¹ * ((a.den : Rat) * (a.den : Rat)⁻¹) := by grind
      _ = (b.num : Rat) * (b.den : Rat)⁻¹ * 1 := by rw [hia]
      _ = (b.num : Rat) * (b.den : Rat)⁻¹ := by grind
  rw [hlhs, hrhs] at hscaled
  exact hscaled

private theorem qLeB_complete {a b : QPair} (ha : a.ok) (hb : b.ok) (h : a.toRat ≤ b.toRat) :
    qLeB a b = true := by
  unfold qLeB
  apply decide_eq_true
  have hda : (0 : Rat) < (a.den : Rat) := int_cast_pos ha
  have hdb : (0 : Rat) < (b.den : Rat) := int_cast_pos hb
  have hmul := rat_mul_le_mul_of_nonneg_right h
    (Rat.mul_nonneg (Rat.le_of_lt hda) (Rat.le_of_lt hdb))
  unfold QPair.toRat at hmul
  have hia : (a.den : Rat) * (a.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hda)
  have hib : (b.den : Rat) * (b.den : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdb)
  rw [Rat.div_def, Rat.div_def] at hmul
  have hl : (a.num : Rat) * (a.den : Rat)⁻¹ * ((a.den : Rat) * (b.den : Rat)) =
      (a.num : Rat) * (b.den : Rat) := by
    calc (a.num : Rat) * (a.den : Rat)⁻¹ * ((a.den : Rat) * (b.den : Rat))
        = (a.num : Rat) * (b.den : Rat) * ((a.den : Rat) * (a.den : Rat)⁻¹) := by grind
      _ = (a.num : Rat) * (b.den : Rat) * 1 := by rw [hia]
      _ = (a.num : Rat) * (b.den : Rat) := by grind
  have hr : (b.num : Rat) * (b.den : Rat)⁻¹ * ((a.den : Rat) * (b.den : Rat)) =
      (b.num : Rat) * (a.den : Rat) := by
    calc (b.num : Rat) * (b.den : Rat)⁻¹ * ((a.den : Rat) * (b.den : Rat))
        = (b.num : Rat) * (a.den : Rat) * ((b.den : Rat) * (b.den : Rat)⁻¹) := by grind
      _ = (b.num : Rat) * (a.den : Rat) * 1 := by rw [hib]
      _ = (b.num : Rat) * (a.den : Rat) := by grind
  rw [hl, hr] at hmul
  have : ((a.num * b.den : Int) : Rat) ≤ ((b.num * a.den : Int) : Rat) := by
    simp only [Rat.intCast_mul]; exact hmul
  exact Rat.intCast_le_intCast.mp this

private theorem qLtB_sound {a b : QPair} (ha : a.ok) (hb : b.ok) (h : qLtB a b = true) :
    a.toRat < b.toRat := by
  have hint : a.num * b.den < b.num * a.den := of_decide_eq_true h
  have hle : a.toRat ≤ b.toRat := qLeB_sound ha hb (decide_eq_true (Int.le_of_lt hint))
  have hne : a.toRat ≠ b.toRat := by
    intro heq
    have hge : qLeB b a = true := qLeB_complete hb ha (by rw [heq]; exact Rat.le_refl)
    have hint2 : b.num * a.den ≤ a.num * b.den := of_decide_eq_true hge
    omega
  exact Rat.lt_of_le_of_ne hle hne

private theorem qLtB_complete {a b : QPair} (ha : a.ok) (hb : b.ok) (h : a.toRat < b.toRat) :
    qLtB a b = true := by
  unfold qLtB
  apply decide_eq_true
  have hle : a.num * b.den ≤ b.num * a.den :=
    of_decide_eq_true (qLeB_complete ha hb (Rat.le_of_lt h))
  have hne : a.num * b.den ≠ b.num * a.den := by
    intro heq
    have hge : b.toRat ≤ a.toRat := qLeB_sound hb ha (decide_eq_true (by omega))
    exact Rat.not_le.mpr h hge
  omega

private theorem qFloor40_le {q : QPair} (hq : q.ok) (hnn : (0 : Rat) ≤ q.toRat) :
    (0 : Rat) ≤ (qFloor40 q).toRat ∧ (qFloor40 q).toRat ≤ q.toRat := by
  have h0ok : (⟨0, 1⟩ : QPair).ok := by decide
  have hqnum_nn : (0 : Int) ≤ q.num := by
    have h0 : (⟨0, 1⟩ : QPair).toRat ≤ q.toRat := by
      unfold QPair.toRat
      have : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
      rw [this]; exact hnn
    have hle := of_decide_eq_true (qLeB_complete h0ok hq h0)
    change (0 : Int) * q.den ≤ q.num * 1 at hle
    omega
  have hS : (0 : Int) < dyadicScale := by unfold dyadicScale; decide
  have hdiv_nn : (0 : Int) ≤ (q.num * dyadicScale) / q.den :=
    Int.ediv_nonneg (Int.mul_nonneg hqnum_nn (Int.le_of_lt hS)) (Int.le_of_lt hq)
  have hdiv_le : ((q.num * dyadicScale) / q.den) * q.den ≤ q.num * dyadicScale := by
    have hmod := Int.mul_ediv_add_emod (q.num * dyadicScale) q.den
    have hrem : (0 : Int) ≤ (q.num * dyadicScale) % q.den :=
      Int.emod_nonneg (q.num * dyadicScale) (by omega)
    have hcomm : ((q.num * dyadicScale) / q.den) * q.den =
        q.den * ((q.num * dyadicScale) / q.den) := Int.mul_comm _ _
    omega
  constructor
  · have h := qLeB_sound h0ok (qFloor40_ok q) (decide_eq_true (by
      change (0 : Int) * dyadicScale ≤ ((q.num * dyadicScale) / q.den) * 1
      omega))
    unfold QPair.toRat at h
    have h0 : ((0 : Int) : Rat) / ((1 : Int) : Rat) = 0 := by grind
    rw [h0] at h
    exact h
  · exact qLeB_sound (qFloor40_ok q) hq (decide_eq_true hdiv_le)

private theorem qCeil40_ge {q : QPair} (hq : q.ok) :
    q.toRat ≤ (qCeil40 q).toRat := by
  have hdiv_ge : q.num * dyadicScale ≤ ((q.num * dyadicScale + q.den - 1) / q.den) * q.den := by
    have hmod := Int.mul_ediv_add_emod (q.num * dyadicScale + q.den - 1) q.den
    have hrem : (q.num * dyadicScale + q.den - 1) % q.den < q.den :=
      Int.emod_lt_of_pos (q.num * dyadicScale + q.den - 1) hq
    have hcomm : ((q.num * dyadicScale + q.den - 1) / q.den) * q.den =
        q.den * ((q.num * dyadicScale + q.den - 1) / q.den) := Int.mul_comm _ _
    omega
  exact qLeB_sound hq (qCeil40_ok q) (decide_eq_true hdiv_ge)

/-! ## Parameterized Subinterval & Uniform-Partition Checkers -/

/-- Exact pure-`Int` checker for one subinterval `[a, b]` of a coupled `G^{-1/p}` vertex step. -/
def checkVertexSubP (p : Nat) (α β μ lo4 hi4 lo2p hi2p a b yLo yHi : QPair) : Bool :=
  let dminSq :=
    if qLeB a μ && qLeB μ b then ⟨0, 1⟩
    else if qLtB μ a then qSq (qSub a μ)
    else qSq (qSub μ b)
  let da := qSq (qSub a μ)
  let db := qSq (qSub b μ)
  let dmaxSq := if qLeB da db then db else da
  let qLo := qFloor40 (qAdd α (qMul (qMul lo4 β) dminSq))
  let qHi := qCeil40  (qAdd α (qMul (qMul hi4 β) dmaxSq))
  let vLo := qMul (qMul lo2p a) (qPow qLo p)
  let vHi := qMul (qMul hi2p b) (qPow qHi p)
  qLeB yLo vLo && qLeB vHi yHi

private theorem checkVertexSubP_sound
    (p : Nat) (α β μ oneSubU oneAddU a b yLo yHi : QPair) (u : Rat)
    (hαok : α.ok) (hβok : β.ok) (hμok : μ.ok)
    (hsok : oneSubU.ok) (haok : oneAddU.ok)
    (hAok : a.ok) (hBok : b.ok) (hyLok : yLo.ok) (hyHok : yHi.ok)
    (hαpos : (0 : Rat) < α.toRat) (hβnn : (0 : Rat) ≤ β.toRat)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1)
    (h1su : oneSubU.toRat = 1 - u) (h1au : oneAddU.toRat = 1 + u)
    (hApos : (0 : Rat) < a.toRat)
    (hchk : checkVertexSubP p α β μ (qPow oneSubU 4) (qPow oneAddU 4)
              (qPow oneSubU (2 * p)) (qPow oneAddU (2 * p)) a b yLo yHi = true)
    {m y : Rat} (hmL : a.toRat ≤ m) (hmR : m ≤ b.toRat)
    (henv : vertexLowerEnv p α.toRat β.toRat μ.toRat u m ≤ y ∧
            y ≤ vertexUpperEnv p α.toRat β.toRat μ.toRat u m) :
    yLo.toRat ≤ y ∧ y ≤ yHi.toRat := by
  have hmPos : (0 : Rat) < m := rat_lt_of_lt_of_le hApos hmL
  have hloNN : (0 : Rat) ≤ 1 - u := Rat.le_of_lt (rat_sub_pos_of_lt hu1)
  have hhiNN : (0 : Rat) ≤ 1 + u := Rat.le_of_lt (rat_add_pos_of_pos_nonneg (by decide) hu0)
  unfold checkVertexSubP at hchk
  rcases Bool.and_eq_true_iff.mp hchk with ⟨hchkL, hchkR⟩
  have hlo4ok : (qPow oneSubU 4).ok := qPow_ok hsok 4
  have hhi4ok : (qPow oneAddU 4).ok := qPow_ok haok 4
  have hlo2pok : (qPow oneSubU (2 * p)).ok := qPow_ok hsok (2 * p)
  have hhi2pok : (qPow oneAddU (2 * p)).ok := qPow_ok haok (2 * p)
  have hdaok : (qSq (qSub a μ)).ok := qSq_ok (qSub_ok hAok hμok)
  have hdbok : (qSq (qSub b μ)).ok := qSq_ok (qSub_ok hBok hμok)
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
          have := Rat.add_le_add_right (c := -μ.toRat) |>.mpr hmL; grind
        exact rat_sq_le_sq_of_nonneg hnn hle
      · rename_i hnotlt
        have haμ : a.toRat ≤ μ.toRat := by
          cases Rat.le_total (a := a.toRat) (b := μ.toRat) with
          | inl h => exact h
          | inr h =>
            by_cases heq : a.toRat = μ.toRat
            · rw [heq]; exact Rat.le_refl
            · exact False.elim (hnotlt (qLtB_complete hμok hAok (Rat.lt_of_le_of_ne h (Ne.symm heq))))
        have hbμ : b.toRat ≤ μ.toRat := by
          cases Rat.le_total (a := b.toRat) (b := μ.toRat) with
          | inl h => exact h
          | inr hμb =>
            have h1 := qLeB_complete hAok hμok haμ
            have h2 := qLeB_complete hμok hBok hμb
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
  let da := qSq (qSub a μ)
  let db := qSq (qSub b μ)
  let dmaxSq := if qLeB da db then db else da
  have hdmax_ok : dmaxSq.ok := by dsimp [dmaxSq]; split <;> assumption
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
        | inl h => exact False.elim (hnotle (qLeB_complete hdaok hdbok h))
      rw [hdaR, hdbR] at hgeR
      rw [rat_max_eq_left hgeR] at hsq
      rw [hdaR]; exact hsq
  let qLoRaw := qAdd α (qMul (qMul (qPow oneSubU 4) β) dminSq)
  let qHiRaw := qAdd α (qMul (qMul (qPow oneAddU 4) β) dmaxSq)
  let qLo := qFloor40 qLoRaw
  let qHi := qCeil40  qHiRaw
  let vLo := qMul (qMul (qPow oneSubU (2 * p)) a) (qPow qLo p)
  let vHi := qMul (qMul (qPow oneAddU (2 * p)) b) (qPow qHi p)
  have hqLoRaw_ok : qLoRaw.ok := qAdd_ok hαok (qMul_ok (qMul_ok hlo4ok hβok) hdmin_ok)
  have hqHiRaw_ok : qHiRaw.ok := qAdd_ok hαok (qMul_ok (qMul_ok hhi4ok hβok) hdmax_ok)
  have hqLok : qLo.ok := qFloor40_ok qLoRaw
  have hqHok : qHi.ok := qCeil40_ok qHiRaw
  have hvLok : vLo.ok := qMul_ok (qMul_ok hlo2pok hAok) (qPow_ok hqLok p)
  have hvHok : vHi.ok := qMul_ok (qMul_ok hhi2pok hBok) (qPow_ok hqHok p)
  have hqLoRaw_R : qLoRaw.toRat = α.toRat + ratPow (1 - u) 4 * β.toRat * dminSq.toRat := by
    dsimp [qLoRaw]
    rw [qAdd_toRat hαok (qMul_ok (qMul_ok hlo4ok hβok) hdmin_ok),
        qMul_toRat (qMul_ok hlo4ok hβok) hdmin_ok,
        qMul_toRat hlo4ok hβok, qPow_toRat hsok 4, h1su]
  have hqHiRaw_R : qHiRaw.toRat = α.toRat + ratPow (1 + u) 4 * β.toRat * dmaxSq.toRat := by
    dsimp [qHiRaw]
    rw [qAdd_toRat hαok (qMul_ok (qMul_ok hhi4ok hβok) hdmax_ok),
        qMul_toRat (qMul_ok hhi4ok hβok) hdmax_ok,
        qMul_toRat hhi4ok hβok, qPow_toRat haok 4, h1au]
  have hqLoRaw_nn : (0 : Rat) ≤ qLoRaw.toRat := by
    rw [hqLoRaw_R]
    exact Rat.le_of_lt (rat_add_pos_of_pos_nonneg hαpos
      (Rat.mul_nonneg (Rat.mul_nonneg (ratPow_nonneg hloNN 4) hβnn) hdmin_nn))
  have ⟨hqLo_nn, hqLo_floor⟩ := qFloor40_le hqLoRaw_ok hqLoRaw_nn
  have hqHi_ceil : qHiRaw.toRat ≤ qHi.toRat := qCeil40_ge hqHiRaw_ok
  have hqLo_le : qLo.toRat ≤ qLoVertex α.toRat β.toRat μ.toRat u m := by
    refine Rat.le_trans hqLo_floor ?_
    rw [hqLoRaw_R]; unfold qLoVertex
    exact Rat.add_le_add_left.mpr
      (rat_mul_le_mul_of_nonneg_left hdmin_le (Rat.mul_nonneg (ratPow_nonneg hloNN 4) hβnn))
  have hqHi_ge : qHiVertex α.toRat β.toRat μ.toRat u m ≤ qHi.toRat := by
    refine Rat.le_trans ?_ hqHi_ceil
    rw [hqHiRaw_R]; unfold qHiVertex
    exact Rat.add_le_add_left.mpr
      (rat_mul_le_mul_of_nonneg_left hdmax_ge (Rat.mul_nonneg (ratPow_nonneg hhiNN 4) hβnn))
  have hqHiV_nn : (0 : Rat) ≤ qHiVertex α.toRat β.toRat μ.toRat u m := by
    unfold qHiVertex
    exact Rat.le_of_lt (rat_add_pos_of_pos_nonneg hαpos
      (Rat.mul_nonneg (Rat.mul_nonneg (ratPow_nonneg hhiNN 4) hβnn) (rat_sq_nonneg _)))
  have hvLo_le : vLo.toRat ≤ vertexLowerEnv p α.toRat β.toRat μ.toRat u m := by
    dsimp [vLo]; unfold vertexLowerEnv
    rw [qMul_toRat (qMul_ok hlo2pok hAok) (qPow_ok hqLok p),
        qMul_toRat hlo2pok hAok, qPow_toRat hsok (2 * p), qPow_toRat hqLok p, h1su]
    have hlo2p_nn : (0 : Rat) ≤ ratPow (1 - u) (2 * p) := ratPow_nonneg hloNN (2 * p)
    have h1 : ratPow (1 - u) (2 * p) * a.toRat ≤ ratPow (1 - u) (2 * p) * m :=
      rat_mul_le_mul_of_nonneg_left hmL hlo2p_nn
    have h2 : ratPow qLo.toRat p ≤ ratPow (qLoVertex α.toRat β.toRat μ.toRat u m) p :=
      ratPow_le_pow_of_nonneg hqLo_nn hqLo_le p
    exact rat_mul_le_mul h1 h2
      (Rat.mul_nonneg hlo2p_nn (Rat.le_of_lt hApos)) (ratPow_nonneg hqLo_nn p)
  have hvHi_ge : vertexUpperEnv p α.toRat β.toRat μ.toRat u m ≤ vHi.toRat := by
    dsimp [vHi]; unfold vertexUpperEnv
    rw [qMul_toRat (qMul_ok hhi2pok hBok) (qPow_ok hqHok p),
        qMul_toRat hhi2pok hBok, qPow_toRat haok (2 * p), qPow_toRat hqHok p, h1au]
    have hhi2p_nn : (0 : Rat) ≤ ratPow (1 + u) (2 * p) := ratPow_nonneg hhiNN (2 * p)
    have h1 : ratPow (1 + u) (2 * p) * m ≤ ratPow (1 + u) (2 * p) * b.toRat :=
      rat_mul_le_mul_of_nonneg_left hmR hhi2p_nn
    have h2 : ratPow (qHiVertex α.toRat β.toRat μ.toRat u m) p ≤ ratPow qHi.toRat p :=
      ratPow_le_pow_of_nonneg hqHiV_nn hqHi_ge p
    exact rat_mul_le_mul h1 h2
      (Rat.mul_nonneg hhi2p_nn (Rat.le_of_lt hmPos)) (ratPow_nonneg hqHiV_nn p)
  constructor
  · exact Rat.le_trans (qLeB_sound hyLok hvLok hchkL) (Rat.le_trans hvLo_le henv.1)
  · exact Rat.le_trans henv.2 (Rat.le_trans hvHi_ge (qLeB_sound hvHok hyHok hchkR))

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
    | inl hle => exact ih (by omega) h2 m hmL hle
    | inr hge => exact hstep (k + 1) hk h1 m hge hmR

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
    simp only [Rat.intCast_mul]; grind
  have hR_eq : (⟨L_n * (k0 + 1 : Nat) + (R_n - L_n) * (k0 + 1 : Nat), D * (k0 + 1 : Nat)⟩ : QPair).toRat =
      (R_n : Rat) / (D : Rat) := by
    unfold QPair.toRat
    apply rat_div_eq_of_mul (int_cast_ne_zero hDKpos) (int_cast_ne_zero hD)
    simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul]; grind
  rw [← hL_eq] at hmL
  rw [← hR_eq] at hmR
  exact checkUniformAux_sound (k0 + 1) L_n (R_n - L_n) (D * (k0 + 1 : Nat)) chk P hstep
    k0 (by omega) hchk m hmL hmR

/-- Top-level sound certificate for one coupled `G^{-1/p}` vertex step on `[L_n/D, R_n/D]`. -/
def checkVertexStepP (p K : Nat) (L_n R_n D : Int)
    (α β μ oneSubU oneAddU yLo yHi : QPair) : Bool :=
  let lo4  := qPow oneSubU 4
  let hi4  := qPow oneAddU 4
  let lo2p := qPow oneSubU (2 * p)
  let hi2p := qPow oneAddU (2 * p)
  checkUniform K L_n R_n D (fun a b => checkVertexSubP p α β μ lo4 hi4 lo2p hi2p a b yLo yHi)

private theorem certifyVertexStepP
    (p K : Nat) (hK : 0 < K) (L_n R_n D : Int) (hD : (0 : Int) < D)
    (hLpos : (0 : Int) < L_n) (hLR : L_n ≤ R_n)
    (α β μ oneSubU oneAddU yLo yHi : QPair) (u : Rat)
    (hαok : α.ok) (hβok : β.ok) (hμok : μ.ok)
    (hsok : oneSubU.ok) (haok : oneAddU.ok)
    (hyLok : yLo.ok) (hyHok : yHi.ok)
    (hαpos : (0 : Rat) < α.toRat) (hβnn : (0 : Rat) ≤ β.toRat)
    (hu0 : (0 : Rat) ≤ u) (hu1 : u < 1)
    (h1su : oneSubU.toRat = 1 - u) (h1au : oneAddU.toRat = 1 + u)
    (hchk : checkVertexStepP p K L_n R_n D α β μ oneSubU oneAddU yLo yHi = true)
    {m y : Rat}
    (hmL : (L_n : Rat) / (D : Rat) ≤ m) (hmR : m ≤ (R_n : Rat) / (D : Rat))
    (henv : (0 : Rat) < m →
      vertexLowerEnv p α.toRat β.toRat μ.toRat u m ≤ y ∧
      y ≤ vertexUpperEnv p α.toRat β.toRat μ.toRat u m) :
    yLo.toRat ≤ y ∧ y ≤ yHi.toRat := by
  have hKpos : (0 : Int) < (K : Int) := by omega
  have hDKok : (0 : Int) < D * (K : Int) := Int.mul_pos hD hKpos
  refine checkUniform_sound K hK L_n R_n D hD
    (fun a b => checkVertexSubP p α β μ (qPow oneSubU 4) (qPow oneAddU 4)
      (qPow oneSubU (2 * p)) (qPow oneAddU (2 * p)) a b yLo yHi)
    (fun m' => ((0 : Rat) < m' →
      vertexLowerEnv p α.toRat β.toRat μ.toRat u m' ≤ y ∧
      y ≤ vertexUpperEnv p α.toRat β.toRat μ.toRat u m') →
      yLo.toRat ≤ y ∧ y ≤ yHi.toRat)
    ?_ hchk m hmL hmR henv
  intro k _ hsub m' hm'L hm'R henv'
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
  have hm'Pos : (0 : Rat) < m' := rat_lt_of_lt_of_le hApos hm'L
  exact checkVertexSubP_sound p α β μ oneSubU oneAddU
    ⟨L_n * (K : Int) + (R_n - L_n) * (k : Int), D * (K : Int)⟩
    ⟨L_n * (K : Int) + (R_n - L_n) * ((k + 1 : Nat) : Int), D * (K : Int)⟩
    yLo yHi u hαok hβok hμok hsok haok hDKok hDKok hyLok hyHok
    hαpos hβnn hu0 hu1 h1su h1au hApos hsub hm'L hm'R (henv' hm'Pos)

/-! ## Theorem 4: BF16 6-Step Stationary Vertex `G^{-1/2}` (`p = 2`, `[982/1000, 1018/1000]`) -/

private def p2α : QPair := ⟨4115409943, 4294967296⟩
private def p2β : QPair := ⟨6258468564, 4294967296⟩
private def p2μ : QPair := ⟨5020662387, 4294967296⟩

private theorem p2_cert1 :
    checkVertexStepP 2 16 85 115 100 p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9641, 10000⟩ ⟨10849, 10000⟩ = true := by decide
private theorem p2_cert2 :
    checkVertexStepP 2 16 9641 10849 10000 p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9752, 10000⟩ ⟨10382, 10000⟩ = true := by decide
private theorem p2_cert3 :
    checkVertexStepP 2 16 9752 10382 10000 p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9787, 10000⟩ ⟨10233, 10000⟩ = true := by decide
private theorem p2_cert4 :
    checkVertexStepP 2 16 9787 10233 10000 p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9799, 10000⟩ ⟨10206, 10000⟩ = true := by decide
private theorem p2_cert5 :
    checkVertexStepP 2 32 9799 10206 10000 p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9814, 10000⟩ ⟨10189, 10000⟩ = true := by decide
private theorem p2_cert6 :
    checkVertexStepP 2 64 9814 10189 10000 p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨982, 1000⟩ ⟨1018, 1000⟩ = true := by decide

theorem bf16_inv_sqrt_vertex_certified (m0 m6 : Rat)
    (hlo : (85 / 100 : Rat) ≤ m0) (hhi : m0 ≤ (115 / 100 : Rat))
    (htraj : NoisyVertexTraj6_2 bf16InvSqrtParams uBF16 m0 m6) :
    (982 / 1000 : Rat) ≤ m6 ∧ m6 ≤ (1018 / 1000 : Rat) := by
  rcases htraj with ⟨m1, m2, m3, m4, m5, hs1, hs2, hs3, hs4, hs5, hs6⟩
  have hu0 : (0 : Rat) ≤ uBF16 := by unfold uBF16; grind
  have hu1 : uBF16 < 1 := by unfold uBF16; grind
  have h1su : (⟨255, 256⟩ : QPair).toRat = 1 - uBF16 := by unfold QPair.toRat uBF16; grind
  have h1au : (⟨257, 256⟩ : QPair).toRat = 1 + uBF16 := by unfold QPair.toRat uBF16; grind
  have hαpos : (0 : Rat) < p2α.toRat := by unfold p2α QPair.toRat; grind
  have hβnn  : (0 : Rat) ≤ p2β.toRat := by unfold p2β QPair.toRat; grind
  have ⟨h1L, h1R⟩ := certifyVertexStepP 2 16 (by decide) 85 115 100 (by decide) (by decide) (by decide)
    p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9641, 10000⟩ ⟨10849, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p2_cert1 hlo hhi
    (fun hm => noisyVertexStep2_envelope p2α.toRat p2β.toRat p2μ.toRat uBF16 m0 m1 hαpos hβnn hu1 hm hs1)
  have ⟨h2L, h2R⟩ := certifyVertexStepP 2 16 (by decide) 9641 10849 10000 (by decide) (by decide) (by decide)
    p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9752, 10000⟩ ⟨10382, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p2_cert2 h1L h1R
    (fun hm => noisyVertexStep2_envelope p2α.toRat p2β.toRat p2μ.toRat uBF16 m1 m2 hαpos hβnn hu1 hm hs2)
  have ⟨h3L, h3R⟩ := certifyVertexStepP 2 16 (by decide) 9752 10382 10000 (by decide) (by decide) (by decide)
    p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9787, 10000⟩ ⟨10233, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p2_cert3 h2L h2R
    (fun hm => noisyVertexStep2_envelope p2α.toRat p2β.toRat p2μ.toRat uBF16 m2 m3 hαpos hβnn hu1 hm hs3)
  have ⟨h4L, h4R⟩ := certifyVertexStepP 2 16 (by decide) 9787 10233 10000 (by decide) (by decide) (by decide)
    p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9799, 10000⟩ ⟨10206, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p2_cert4 h3L h3R
    (fun hm => noisyVertexStep2_envelope p2α.toRat p2β.toRat p2μ.toRat uBF16 m3 m4 hαpos hβnn hu1 hm hs4)
  have ⟨h5L, h5R⟩ := certifyVertexStepP 2 32 (by decide) 9799 10206 10000 (by decide) (by decide) (by decide)
    p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9814, 10000⟩ ⟨10189, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p2_cert5 h4L h4R
    (fun hm => noisyVertexStep2_envelope p2α.toRat p2β.toRat p2μ.toRat uBF16 m4 m5 hαpos hβnn hu1 hm hs5)
  exact certifyVertexStepP 2 64 (by decide) 9814 10189 10000 (by decide) (by decide) (by decide)
    p2α p2β p2μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨982, 1000⟩ ⟨1018, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p2_cert6 h5L h5R
    (fun hm => noisyVertexStep2_envelope p2α.toRat p2β.toRat p2μ.toRat uBF16 m5 m6 hαpos hβnn hu1 hm hs6)

/-! ## Theorem 5: BF16 6-Step Stationary Vertex `G^{-1/3}` (`p = 3`, `[974/1000, 1026/1000]`) -/

private def p3α : QPair := ⟨4185630849, 4294967296⟩
private def p3β : QPair := ⟨4605301221, 4294967296⟩
private def p3μ : QPair := ⟨4951892153, 4294967296⟩

private theorem p3_cert1 :
    checkVertexStepP 3 16 85 115 100 p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9562, 10000⟩ ⟨11033, 10000⟩ = true := by decide
private theorem p3_cert2 :
    checkVertexStepP 3 16 9562 11033 10000 p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9654, 10000⟩ ⟨10576, 10000⟩ = true := by decide
private theorem p3_cert3 :
    checkVertexStepP 3 16 9654 10576 10000 p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9688, 10000⟩ ⟨10368, 10000⟩ = true := by decide
private theorem p3_cert4 :
    checkVertexStepP 3 32 9688 10368 10000 p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9723, 10000⟩ ⟨10292, 10000⟩ = true := by decide
private theorem p3_cert5 :
    checkVertexStepP 3 64 9723 10292 10000 p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9735, 10000⟩ ⟨10269, 10000⟩ = true := by decide
set_option maxRecDepth 2048 in
private theorem p3_cert6 :
    checkVertexStepP 3 160 9735 10269 10000 p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨974, 1000⟩ ⟨1026, 1000⟩ = true := by decide

theorem bf16_inv_cbrt_vertex_certified (m0 m6 : Rat)
    (hlo : (85 / 100 : Rat) ≤ m0) (hhi : m0 ≤ (115 / 100 : Rat))
    (htraj : NoisyVertexTraj6_3 bf16InvCbrtParams uBF16 m0 m6) :
    (974 / 1000 : Rat) ≤ m6 ∧ m6 ≤ (1026 / 1000 : Rat) := by
  rcases htraj with ⟨m1, m2, m3, m4, m5, hs1, hs2, hs3, hs4, hs5, hs6⟩
  have hu0 : (0 : Rat) ≤ uBF16 := by unfold uBF16; grind
  have hu1 : uBF16 < 1 := by unfold uBF16; grind
  have h1su : (⟨255, 256⟩ : QPair).toRat = 1 - uBF16 := by unfold QPair.toRat uBF16; grind
  have h1au : (⟨257, 256⟩ : QPair).toRat = 1 + uBF16 := by unfold QPair.toRat uBF16; grind
  have hαpos : (0 : Rat) < p3α.toRat := by unfold p3α QPair.toRat; grind
  have hβnn  : (0 : Rat) ≤ p3β.toRat := by unfold p3β QPair.toRat; grind
  have ⟨h1L, h1R⟩ := certifyVertexStepP 3 16 (by decide) 85 115 100 (by decide) (by decide) (by decide)
    p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9562, 10000⟩ ⟨11033, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p3_cert1 hlo hhi
    (fun hm => noisyVertexStep3_envelope p3α.toRat p3β.toRat p3μ.toRat uBF16 m0 m1 hαpos hβnn hu1 hm hs1)
  have ⟨h2L, h2R⟩ := certifyVertexStepP 3 16 (by decide) 9562 11033 10000 (by decide) (by decide) (by decide)
    p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9654, 10000⟩ ⟨10576, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p3_cert2 h1L h1R
    (fun hm => noisyVertexStep3_envelope p3α.toRat p3β.toRat p3μ.toRat uBF16 m1 m2 hαpos hβnn hu1 hm hs2)
  have ⟨h3L, h3R⟩ := certifyVertexStepP 3 16 (by decide) 9654 10576 10000 (by decide) (by decide) (by decide)
    p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9688, 10000⟩ ⟨10368, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p3_cert3 h2L h2R
    (fun hm => noisyVertexStep3_envelope p3α.toRat p3β.toRat p3μ.toRat uBF16 m2 m3 hαpos hβnn hu1 hm hs3)
  have ⟨h4L, h4R⟩ := certifyVertexStepP 3 32 (by decide) 9688 10368 10000 (by decide) (by decide) (by decide)
    p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9723, 10000⟩ ⟨10292, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p3_cert4 h3L h3R
    (fun hm => noisyVertexStep3_envelope p3α.toRat p3β.toRat p3μ.toRat uBF16 m3 m4 hαpos hβnn hu1 hm hs4)
  have ⟨h5L, h5R⟩ := certifyVertexStepP 3 64 (by decide) 9723 10292 10000 (by decide) (by decide) (by decide)
    p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9735, 10000⟩ ⟨10269, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p3_cert5 h4L h4R
    (fun hm => noisyVertexStep3_envelope p3α.toRat p3β.toRat p3μ.toRat uBF16 m4 m5 hαpos hβnn hu1 hm hs5)
  exact certifyVertexStepP 3 160 (by decide) 9735 10269 10000 (by decide) (by decide) (by decide)
    p3α p3β p3μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨974, 1000⟩ ⟨1026, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p3_cert6 h5L h5R
    (fun hm => noisyVertexStep3_envelope p3α.toRat p3β.toRat p3μ.toRat uBF16 m5 m6 hαpos hβnn hu1 hm hs6)

/-! ## Theorem 6: BF16 6-Step Stationary Vertex `G^{-1/8}` (`p = 8`, `[932/1000, 1068/1000]`) -/

private def p8α : QPair := ⟨4193173389, 4294967296⟩
private def p8β : QPair := ⟨701570769, 4294967296⟩
private def p8μ : QPair := ⟨5914773772, 4294967296⟩

private theorem p8_cert1 :
    checkVertexStepP 8 16 85 115 100 p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9148, 10000⟩ ⟨11040, 10000⟩ = true := by decide
private theorem p8_cert2 :
    checkVertexStepP 8 16 9148 11040 10000 p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9215, 10000⟩ ⟨10831, 10000⟩ = true := by decide
private theorem p8_cert3 :
    checkVertexStepP 8 32 9215 10831 10000 p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9280, 10000⟩ ⟨10743, 10000⟩ = true := by decide
private theorem p8_cert4 :
    checkVertexStepP 8 64 9280 10743 10000 p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9306, 10000⟩ ⟨10703, 10000⟩ = true := by decide
private theorem p8_cert5 :
    checkVertexStepP 8 128 9306 10703 10000 p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9317, 10000⟩ ⟨10686, 10000⟩ = true := by decide
set_option maxRecDepth 2048 in
private theorem p8_cert6 :
    checkVertexStepP 8 320 9317 10686 10000 p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨932, 1000⟩ ⟨1068, 1000⟩ = true := by decide

theorem bf16_inv_eighth_vertex_certified (m0 m6 : Rat)
    (hlo : (85 / 100 : Rat) ≤ m0) (hhi : m0 ≤ (115 / 100 : Rat))
    (htraj : NoisyVertexTraj6_8 bf16InvEighthParams uBF16 m0 m6) :
    (932 / 1000 : Rat) ≤ m6 ∧ m6 ≤ (1068 / 1000 : Rat) := by
  rcases htraj with ⟨m1, m2, m3, m4, m5, hs1, hs2, hs3, hs4, hs5, hs6⟩
  have hu0 : (0 : Rat) ≤ uBF16 := by unfold uBF16; grind
  have hu1 : uBF16 < 1 := by unfold uBF16; grind
  have h1su : (⟨255, 256⟩ : QPair).toRat = 1 - uBF16 := by unfold QPair.toRat uBF16; grind
  have h1au : (⟨257, 256⟩ : QPair).toRat = 1 + uBF16 := by unfold QPair.toRat uBF16; grind
  have hαpos : (0 : Rat) < p8α.toRat := by unfold p8α QPair.toRat; grind
  have hβnn  : (0 : Rat) ≤ p8β.toRat := by unfold p8β QPair.toRat; grind
  have ⟨h1L, h1R⟩ := certifyVertexStepP 8 16 (by decide) 85 115 100 (by decide) (by decide) (by decide)
    p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9148, 10000⟩ ⟨11040, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p8_cert1 hlo hhi
    (fun hm => noisyVertexStep8_envelope p8α.toRat p8β.toRat p8μ.toRat uBF16 m0 m1 hαpos hβnn hu1 hm hs1)
  have ⟨h2L, h2R⟩ := certifyVertexStepP 8 16 (by decide) 9148 11040 10000 (by decide) (by decide) (by decide)
    p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9215, 10000⟩ ⟨10831, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p8_cert2 h1L h1R
    (fun hm => noisyVertexStep8_envelope p8α.toRat p8β.toRat p8μ.toRat uBF16 m1 m2 hαpos hβnn hu1 hm hs2)
  have ⟨h3L, h3R⟩ := certifyVertexStepP 8 32 (by decide) 9215 10831 10000 (by decide) (by decide) (by decide)
    p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9280, 10000⟩ ⟨10743, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p8_cert3 h2L h2R
    (fun hm => noisyVertexStep8_envelope p8α.toRat p8β.toRat p8μ.toRat uBF16 m2 m3 hαpos hβnn hu1 hm hs3)
  have ⟨h4L, h4R⟩ := certifyVertexStepP 8 64 (by decide) 9280 10743 10000 (by decide) (by decide) (by decide)
    p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9306, 10000⟩ ⟨10703, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p8_cert4 h3L h3R
    (fun hm => noisyVertexStep8_envelope p8α.toRat p8β.toRat p8μ.toRat uBF16 m3 m4 hαpos hβnn hu1 hm hs4)
  have ⟨h5L, h5R⟩ := certifyVertexStepP 8 128 (by decide) 9306 10703 10000 (by decide) (by decide) (by decide)
    p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨9317, 10000⟩ ⟨10686, 10000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p8_cert5 h4L h4R
    (fun hm => noisyVertexStep8_envelope p8α.toRat p8β.toRat p8μ.toRat uBF16 m4 m5 hαpos hβnn hu1 hm hs5)
  exact certifyVertexStepP 8 320 (by decide) 9317 10686 10000 (by decide) (by decide) (by decide)
    p8α p8β p8μ ⟨255, 256⟩ ⟨257, 256⟩ ⟨932, 1000⟩ ⟨1068, 1000⟩ uBF16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hαpos hβnn hu0 hu1 h1su h1au p8_cert6 h5L h5R
    (fun hm => noisyVertexStep8_envelope p8α.toRat p8β.toRat p8μ.toRat uBF16 m5 m6 hαpos hβnn hu1 hm hs6)

end UniversalVertexInvroot
