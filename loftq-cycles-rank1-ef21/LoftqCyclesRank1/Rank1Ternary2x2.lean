/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LoftqCyclesRank1.Defs
import LoftqCyclesRank1.Rank1OneBit

/-!
# Theorem 2: Exact Algebraic `(2, 2)` Rank-1 Ternary EF21 Contraction Constant `(2 + √2) / 8`

Proves `rank1_ternary_2x2_contraction_exact` over `QSqrt2 = ℚ(√2)`:
1. Universal lower bound for ALL `W : RatMat 2 2`:
   there exist nonzero ternary vectors `u, v ∈ {-1, 0, 1}^2 \ {0}` such that
   `((2 + √2) / 8) * ‖W‖_F^2 * ‖u‖_2^2 * ‖v‖_2^2 ≤ (u^T W v)^2`.
2. Exact attainment by `W_rot2x2 = [[1, √2 - 1], [-(√2 - 1), 1]]` (proportional to `R(π/8)`):
   `‖W_rot2x2‖_F^2 = 8 - 4√2`, `((2 + √2) / 8) * ‖W_rot2x2‖_F^2 = 1`,
   for ALL nonzero ternary `u, v`, `(u^T W_rot2x2 v)^2 ≤ ((2 + √2) / 8) * ‖W_rot2x2‖_F^2 * ‖u‖_2^2 * ‖v‖_2^2`
   (proved algebraically via Brahmagupta's identity `q^2 + r^2 = ‖u‖^2 ‖v‖^2 ∈ {1, 2, 4}`),
   and equality holds for `u = (1, 0), v = (1, 0)`.
-/

namespace LoftqCyclesRank1

/-! ### `QSqrt2` Component Lemmas (preserving `*`, `+`, `-` on `Rat` for `grind`) -/

theorem q2_add_mk (a1 b1 a2 b2 : Rat) :
    (⟨a1, b1⟩ : QSqrt2) + ⟨a2, b2⟩ = ⟨a1 + a2, b1 + b2⟩ := rfl

theorem q2_sub_mk (a1 b1 a2 b2 : Rat) :
    (⟨a1, b1⟩ : QSqrt2) - ⟨a2, b2⟩ = ⟨a1 - a2, b1 - b2⟩ := rfl

theorem q2_mul_mk (a1 b1 a2 b2 : Rat) :
    (⟨a1, b1⟩ : QSqrt2) * ⟨a2, b2⟩ = ⟨a1 * a2 + 2 * b1 * b2, a1 * b2 + b1 * a2⟩ := rfl

/-! ### Exact 1D Ternary Lemma for `d = 2` over `Rat` and `QSqrt2` -/

theorem ternary_1d_dim2_nonneg (a b : Rat) (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    QSqrt2.nonneg (QSqrt2.ofRat (a * a) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (a * a + b * b)) ∨
    QSqrt2.nonneg (QSqrt2.ofRat ((a + b) * (a + b)) - (⟨1, 1 / 2⟩ : QSqrt2) * QSqrt2.ofRat (a * a + b * b)) := by
  by_cases hsplit : 2 * (a + b) * (a + b) ≤ 4 * a * a
  · left
    have hrew : QSqrt2.ofRat (a * a) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (a * a + b * b) =
        ⟨a * a - (1 / 2) * (a * a + b * b), -(1 / 4) * (a * a + b * b)⟩ := by
      simp only [QSqrt2.ofRat, q2_mul_mk, q2_sub_mk]
      congr 1 <;> grind
    rw [hrew]
    by_cases hzero : a * a + b * b = 0
    · left
      have ha0 : a * a = 0 := by
        have hb2 := rat_sq_nonneg b
        have ha2 := rat_sq_nonneg a
        grind
      rw [hzero, ha0]
      constructor <;> grind
    · right; left
      have hsum_pos : 0 < a * a + b * b := by
        have ha2 := rat_sq_nonneg a
        have hb2 := rat_sq_nonneg b
        have hge : 0 ≤ a * a + b * b := by grind
        exact Rat.lt_of_le_of_ne hge (Ne.symm hzero)
      have hb_lt_a : b * b ≤ a * a := by
        have h1 : b * b ≤ b * a := Rat.mul_le_mul_of_nonneg_left hba hb
        have h2 : b * a ≤ a * a := Rat.mul_le_mul_of_nonneg_right hba ha
        exact Rat.le_trans h1 h2
      refine ⟨by grind, by grind, ?_⟩
      have hfac1 : 0 ≤ a * a - 2 * a * b - b * b := by grind
      have hfac2 : 0 ≤ a * a + 2 * a * b - b * b := by
        have hab : 0 ≤ a * b := Rat.mul_nonneg ha hb
        grind
      have hprod : 0 ≤ (a * a - 2 * a * b - b * b) * (a * a + 2 * a * b - b * b) :=
        Rat.mul_nonneg hfac1 hfac2
      have hident :
          (a * a - (1 / 2) * (a * a + b * b)) * (a * a - (1 / 2) * (a * a + b * b)) -
          2 * (-(1 / 4) * (a * a + b * b)) * (-(1 / 4) * (a * a + b * b)) =
          (1 / 8) * ((a * a - 2 * a * b - b * b) * (a * a + 2 * a * b - b * b)) := by
        grind
      have hnn : 0 ≤ (1 / 8 : Rat) * ((a * a - 2 * a * b - b * b) * (a * a + 2 * a * b - b * b)) :=
        Rat.mul_nonneg (by grind) hprod
      rw [← hident] at hnn
      grind
  · right
    have hrew : QSqrt2.ofRat ((a + b) * (a + b)) - (⟨1, 1 / 2⟩ : QSqrt2) * QSqrt2.ofRat (a * a + b * b) =
        ⟨(a + b) * (a + b) - (a * a + b * b), -(1 / 2) * (a * a + b * b)⟩ := by
      simp only [QSqrt2.ofRat, q2_mul_mk, q2_sub_mk]
      congr 1 <;> grind
    rw [hrew]
    have hlt : 4 * a * a < 2 * (a + b) * (a + b) := Rat.not_le.mp hsplit
    have hab : 0 ≤ a * b := Rat.mul_nonneg ha hb
    have hsum_pos : 0 < a * a + b * b := by
      have ha2 := rat_sq_nonneg a
      have hb2 := rat_sq_nonneg b
      exact Classical.byContradiction fun hnp => by
        have hle0 : a * a + b * b ≤ 0 := Rat.not_lt.mp hnp
        have ha0 : a * a = 0 := by grind
        have hb0 : b * b = 0 := by grind
        have hab0 : a * b = 0 := Classical.byContradiction fun hne => by
          have hpos : 0 < a * b := Rat.lt_of_le_of_ne hab (Ne.symm hne)
          have hsqp : 0 < (a * b) * (a * b) := Rat.mul_pos hpos hpos
          have heq : (a * b) * (a * b) = (a * a) * (b * b) := by grind
          rw [heq, ha0, hb0] at hsqp
          grind
        grind
    right; left
    refine ⟨by grind, by grind, ?_⟩
    have hfac1 : 0 ≤ b * b + 2 * a * b - a * a := by grind
    have hfac2 : 0 ≤ a * a + 2 * a * b - b * b := by
      have h1 : b * b ≤ b * a := Rat.mul_le_mul_of_nonneg_left hba hb
      have h2 : b * a ≤ a * a := Rat.mul_le_mul_of_nonneg_right hba ha
      grind
    have hprod : 0 ≤ (b * b + 2 * a * b - a * a) * (a * a + 2 * a * b - b * b) :=
      Rat.mul_nonneg hfac1 hfac2
    have hident :
        ((a + b) * (a + b) - (a * a + b * b)) * ((a + b) * (a + b) - (a * a + b * b)) -
        2 * (-(1 / 2) * (a * a + b * b)) * (-(1 / 2) * (a * a + b * b)) =
        (1 / 2) * ((b * b + 2 * a * b - a * a) * (a * a + 2 * a * b - b * b)) := by
      grind
    have hnn : 0 ≤ (1 / 2 : Rat) * ((b * b + 2 * a * b - a * a) * (a * a + 2 * a * b - b * b)) :=
      Rat.mul_nonneg (by grind) hprod
    rw [← hident] at hnn
    grind

theorem absRat_nonneg (x : Rat) : (0 : Rat) ≤ absRat x := by
  unfold absRat
  split <;> grind

theorem absRat_sq (x : Rat) : absRat x * absRat x = x * x := by
  unfold absRat
  split <;> grind

theorem sign_mul_abs (x : Rat) :
    let s : Int := if x < 0 then -1 else 1
    x * (s : Rat) = absRat x := by
  dsimp only [absRat]
  split <;> grind

theorem ternary_1d_dim2_vec (x0 x1 : Rat) :
    ∃ v : Fin 2 → Int, isTernVec v ∧
      (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt (vecSqNormInt v) ≤
      QSqrt2.ofRat ((x0 * (v 0 : Rat) + x1 * (v 1 : Rat)) * (x0 * (v 0 : Rat) + x1 * (v 1 : Rat))) := by
  let a := absRat x0
  let b := absRat x1
  have ha : 0 ≤ a := absRat_nonneg x0
  have hb : 0 ≤ b := absRat_nonneg x1
  have ha2 : a * a = x0 * x0 := absRat_sq x0
  have hb2 : b * b = x1 * x1 := absRat_sq x1
  let s0 : Int := if x0 < 0 then -1 else 1
  let s1 : Int := if x1 < 0 then -1 else 1
  have hs0 : x0 * (s0 : Rat) = a := sign_mul_abs x0
  have hs1 : x1 * (s1 : Rat) = b := sign_mul_abs x1
  have hs0_tern : s0 = -1 ∨ s0 = 0 ∨ s0 = 1 := by simp only [s0]; split <;> simp
  have hs1_tern : s1 = -1 ∨ s1 = 0 ∨ s1 = 1 := by simp only [s1]; split <;> simp
  by_cases hba : b ≤ a
  · rcases ternary_1d_dim2_nonneg a b ha hb hba with h1 | h2
    · let v : Fin 2 → Int := fun j => if j.val = 0 then 1 else 0
      refine ⟨v, ?_, ?_⟩
      · refine ⟨fun j => by match j with | ⟨0, _⟩ => simp [v] | ⟨1, _⟩ => simp [v], ⟨0, by decide⟩⟩
      · have hvnorm : vecSqNormInt v = 1 := by decide
        have hdot : x0 * (v 0 : Rat) + x1 * (v 1 : Rat) = x0 := by
          simp only [v, Fin.val_zero, ↓reduceIte, Fin.val_one, Nat.one_ne_zero]; grind
        rw [hvnorm, hdot]
        change QSqrt2.nonneg (QSqrt2.ofRat (x0 * x0) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 1)
        have heq : QSqrt2.ofRat (x0 * x0) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 1 =
            QSqrt2.ofRat (a * a) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (a * a + b * b) := by
          rw [ha2, hb2]
          simp only [QSqrt2.ofRat, QSqrt2.ofInt, q2_mul_mk, q2_sub_mk]
          congr 1 <;> grind
        rw [heq]
        exact h1
    · let v : Fin 2 → Int := fun j => if j.val = 0 then s0 else s1
      refine ⟨v, ?_, ?_⟩
      · refine ⟨fun j => by match j with | ⟨0, _⟩ => exact hs0_tern | ⟨1, _⟩ => exact hs1_tern,
                ⟨0, by simp [v, s0]; split <;> decide⟩⟩
      · have hvnorm : vecSqNormInt v = 2 := by
          simp only [vecSqNormInt, sumFinInt, v, Fin.val_castSucc, Fin.val_last, ↓reduceIte, Nat.one_ne_zero]
          have hs0sq : s0 * s0 = 1 := by simp only [s0]; split <;> decide
          have hs1sq : s1 * s1 = 1 := by simp only [s1]; split <;> decide
          omega
        have hdot : x0 * (v 0 : Rat) + x1 * (v 1 : Rat) = a + b := by
          simp only [v, Fin.val_zero, ↓reduceIte, Fin.val_one, Nat.one_ne_zero]
          rw [hs0, hs1]
        rw [hvnorm, hdot]
        change QSqrt2.nonneg (QSqrt2.ofRat ((a + b) * (a + b)) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 2)
        have heq : QSqrt2.ofRat ((a + b) * (a + b)) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 2 =
            QSqrt2.ofRat ((a + b) * (a + b)) - (⟨1, 1 / 2⟩ : QSqrt2) * QSqrt2.ofRat (a * a + b * b) := by
          rw [ha2, hb2]
          simp only [QSqrt2.ofRat, QSqrt2.ofInt, q2_mul_mk, q2_sub_mk]
          congr 1 <;> grind
        rw [heq]
        exact h2
  · have hab : a ≤ b := Rat.le_of_lt (Rat.not_le.mp hba)
    rcases ternary_1d_dim2_nonneg b a hb ha hab with h1 | h2
    · let v : Fin 2 → Int := fun j => if j.val = 1 then 1 else 0
      refine ⟨v, ?_, ?_⟩
      · refine ⟨fun j => by match j with | ⟨0, _⟩ => simp [v] | ⟨1, _⟩ => simp [v], ⟨1, by decide⟩⟩
      · have hvnorm : vecSqNormInt v = 1 := by decide
        have hdot : x0 * (v 0 : Rat) + x1 * (v 1 : Rat) = x1 := by
          simp only [v, Fin.val_zero, Fin.val_one, ↓reduceIte, Nat.zero_ne_one]; grind
        rw [hvnorm, hdot]
        change QSqrt2.nonneg (QSqrt2.ofRat (x1 * x1) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 1)
        have heq : QSqrt2.ofRat (x1 * x1) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 1 =
            QSqrt2.ofRat (b * b) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (b * b + a * a) := by
          rw [ha2, hb2]
          simp only [QSqrt2.ofRat, QSqrt2.ofInt, q2_mul_mk, q2_sub_mk]
          congr 1 <;> grind
        rw [heq]
        exact h1
    · let v : Fin 2 → Int := fun j => if j.val = 0 then s0 else s1
      refine ⟨v, ?_, ?_⟩
      · refine ⟨fun j => by match j with | ⟨0, _⟩ => exact hs0_tern | ⟨1, _⟩ => exact hs1_tern,
                ⟨0, by simp [v, s0]; split <;> decide⟩⟩
      · have hvnorm : vecSqNormInt v = 2 := by
          simp only [vecSqNormInt, sumFinInt, v, Fin.val_castSucc, Fin.val_last, ↓reduceIte, Nat.one_ne_zero]
          have hs0sq : s0 * s0 = 1 := by simp only [s0]; split <;> decide
          have hs1sq : s1 * s1 = 1 := by simp only [s1]; split <;> decide
          omega
        have hdot : x0 * (v 0 : Rat) + x1 * (v 1 : Rat) = a + b := by
          simp only [v, Fin.val_zero, ↓reduceIte, Fin.val_one, Nat.one_ne_zero]
          rw [hs0, hs1]
        rw [hvnorm, hdot]
        change QSqrt2.nonneg (QSqrt2.ofRat ((a + b) * (a + b)) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 2)
        have heq : QSqrt2.ofRat ((a + b) * (a + b)) - (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat (x0 * x0 + x1 * x1) * QSqrt2.ofInt 2 =
            QSqrt2.ofRat ((b + a) * (b + a)) - (⟨1, 1 / 2⟩ : QSqrt2) * QSqrt2.ofRat (b * b + a * a) := by
          rw [ha2, hb2]
          simp only [QSqrt2.ofRat, QSqrt2.ofInt, q2_mul_mk, q2_sub_mk]
          congr 1 <;> grind
        rw [heq]
        exact h2

/-! ### `QSqrt2.nonneg` Monotonicity Helper -/

theorem qsqrt2_nonneg_add_nonneg_pair {x : QSqrt2} {da db : Rat}
    (hx : QSqrt2.nonneg x) (hda : 0 ≤ da) (hdb : 0 ≤ db) :
    QSqrt2.nonneg ⟨x.a + da, x.b + db⟩ := by
  rcases hx with ⟨hxa, hxb⟩ | ⟨hxa, hxb, hxs⟩ | ⟨hxa, hxb, hxs⟩
  · left; exact ⟨by grind, by grind⟩
  · by_cases hsum : 0 ≤ x.b + db
    · left; exact ⟨by grind, hsum⟩
    · right; left
      refine ⟨by grind, Rat.not_le.mp hsum, ?_⟩
      have h1 : (x.b + db) * (x.b + db) ≤ x.b * x.b := by
        have hlt : x.b + db < 0 := Rat.not_le.mp hsum
        have hneg : 0 ≤ -(x.b + db) := by grind
        have hle : -(x.b + db) ≤ -x.b := by grind
        have hm1 := Rat.mul_le_mul_of_nonneg_left hle hneg
        have hm2 := Rat.mul_le_mul_of_nonneg_right hle (by grind : 0 ≤ -x.b)
        have htr := Rat.le_trans hm1 hm2
        have e1 : (-(x.b + db)) * (-(x.b + db)) = (x.b + db) * (x.b + db) := by grind
        have e2 : (-x.b) * (-x.b) = x.b * x.b := by grind
        rw [e1, e2] at htr; exact htr
      have h2 : x.a * x.a ≤ (x.a + da) * (x.a + da) := by
        have hle : x.a ≤ x.a + da := by grind
        have hm1 := Rat.mul_le_mul_of_nonneg_left hle hxa
        have hm2 := Rat.mul_le_mul_of_nonneg_right hle (by grind : 0 ≤ x.a + da)
        exact Rat.le_trans hm1 hm2
      grind
  · by_cases hsum : 0 ≤ x.a + da
    · left; exact ⟨hsum, by grind⟩
    · right; right
      refine ⟨Rat.not_le.mp hsum, by grind, ?_⟩
      have h1 : (x.a + da) * (x.a + da) ≤ x.a * x.a := by
        have hlt : x.a + da < 0 := Rat.not_le.mp hsum
        have hneg : 0 ≤ -(x.a + da) := by grind
        have hle : -(x.a + da) ≤ -x.a := by grind
        have hm1 := Rat.mul_le_mul_of_nonneg_left hle hneg
        have hm2 := Rat.mul_le_mul_of_nonneg_right hle (by grind : 0 ≤ -x.a)
        have htr := Rat.le_trans hm1 hm2
        have e1 : (-(x.a + da)) * (-(x.a + da)) = (x.a + da) * (x.a + da) := by grind
        have e2 : (-x.a) * (-x.a) = x.a * x.a := by grind
        rw [e1, e2] at htr; exact htr
      have h2 : x.b * x.b ≤ (x.b + db) * (x.b + db) := by
        have hle : x.b ≤ x.b + db := by grind
        have hm1 := Rat.mul_le_mul_of_nonneg_left hle hxb
        have hm2 := Rat.mul_le_mul_of_nonneg_right hle (by grind : 0 ≤ x.b + db)
        exact Rat.le_trans hm1 hm2
      grind

/-! ### Exact Algebraic Attainment of `W_rot2x2` via Brahmagupta Identity -/

theorem W_rot2x2_frobSq : frobSqQ2 W_rot2x2 = ⟨8, -4⟩ := by
  simp only [frobSqQ2, sumFinQ2, W_rot2x2, QSqrt2.zero, Fin.val_castSucc, Fin.val_last,
             q2_add_mk, q2_mul_mk]
  congr 1 <;> grind

theorem W_rot2x2_alpha_mul_frobSq : QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 = QSqrt2.one := by
  rw [W_rot2x2_frobSq]
  simp only [QSqrt2.alpha2x2, QSqrt2.one, q2_mul_mk]
  congr 1 <;> grind

theorem brahmagupta_tern2_nonneg (u0 u1 v0 v1 : Int)
    (hu0 : u0 = -1 ∨ u0 = 0 ∨ u0 = 1) (hu1 : u1 = -1 ∨ u1 = 0 ∨ u1 = 1)
    (hv0 : v0 = -1 ∨ v0 = 0 ∨ v0 = 1) (hv1 : v1 = -1 ∨ v1 = 0 ∨ v1 = 1) :
    let q := u0 * v0 + u1 * v1
    let r := u0 * v1 - u1 * v0
    0 ≤ r * (r - q) := by
  rcases hu0 with rfl | rfl | rfl <;>
  rcases hu1 with rfl | rfl | rfl <;>
  rcases hv0 with rfl | rfl | rfl <;>
  rcases hv1 with rfl | rfl | rfl <;>
  decide

theorem W_rot2x2_upper_bound (u v : Fin 2 → Int) (hu : isTernVec u) (hv : isTernVec v) :
    quadFormQ2 W_rot2x2 u v * quadFormQ2 W_rot2x2 u v ≤
      QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v) := by
  rw [W_rot2x2_alpha_mul_frobSq]
  let u0 := u 0
  let u1 := u 1
  let v0 := v 0
  let v1 := v 1
  let q : Int := u0 * v0 + u1 * v1
  let r : Int := u0 * v1 - u1 * v0
  have hrrq : 0 ≤ r * (r - q) :=
    brahmagupta_tern2_nonneg u0 u1 v0 v1 (hu.1 0) (hu.1 1) (hv.1 0) (hv.1 1)
  have hdiff : QSqrt2.one * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v) -
      quadFormQ2 W_rot2x2 u v * quadFormQ2 W_rot2x2 u v =
      ⟨-2 * ((r * (r - q) : Int) : Rat), 2 * ((r * (r - q) : Int) : Rat)⟩ := by
    simp only [quadFormQ2, sumFinQ2, W_rot2x2, vecSqNormInt, sumFinInt,
               QSqrt2.zero, QSqrt2.one, QSqrt2.ofInt, Fin.val_castSucc, Fin.val_last,
               q2_add_mk, q2_sub_mk, q2_mul_mk]
    have h00 : (Fin.castSucc (Fin.last 0) : Fin 2) = 0 := rfl
    have h11 : (Fin.last 1 : Fin 2) = 1 := rfl
    rw [h00, h11]
    congr 1 <;> grind
  show QSqrt2.nonneg (QSqrt2.one * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v) -
      quadFormQ2 W_rot2x2 u v * quadFormQ2 W_rot2x2 u v)
  rw [hdiff]
  let k : Rat := ((r * (r - q) : Int) : Rat)
  have hk : 0 ≤ k := by
    dsimp [k]
    exact Rat.intCast_nonneg.mpr hrrq
  by_cases hk0 : k = 0
  · left
    dsimp only
    rw [show ((r * (r - q) : Int) : Rat) = 0 from hk0]
    constructor <;> grind
  · right; right
    have hkpos : 0 < k := Rat.lt_of_le_of_ne hk (Ne.symm hk0)
    have h4k2 : 0 ≤ 4 * k * k := by
      have : 4 * k * k = 4 * (k * k) := by grind
      rw [this]
      exact Rat.mul_nonneg (by grind) (rat_sq_nonneg k)
    refine ⟨by grind, by grind, ?_⟩
    grind

/-! ### Main Theorem 2 -/

theorem rank1_ternary_2x2_contraction_exact :
    (∀ W : RatMat 2 2,
      ∃ u v : Fin 2 → Int, isTernVec u ∧ isTernVec v ∧
        QSqrt2.alpha2x2 * QSqrt2.ofRat (frobSq W) * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v) ≤
        QSqrt2.ofRat (quadFormRat W u v * quadFormRat W u v)) ∧
    (frobSqQ2 W_rot2x2 = ⟨8, -4⟩ ∧
     QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 = QSqrt2.one ∧
     (∀ u v : Fin 2 → Int, isTernVec u → isTernVec v →
       quadFormQ2 W_rot2x2 u v * quadFormQ2 W_rot2x2 u v ≤
         QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v)) ∧
     (∃ u v : Fin 2 → Int, isTernVec u ∧ isTernVec v ∧
       quadFormQ2 W_rot2x2 u v * quadFormQ2 W_rot2x2 u v =
         QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v))) := by
  constructor
  · intro W
    let r0 : Rat := W 0 0 * W 0 0 + W 0 1 * W 0 1
    let r1 : Rat := W 1 0 * W 1 0 + W 1 1 * W 1 1
    have hfrob : frobSq W = r0 + r1 := by
      simp only [frobSq, sumFinRat, r0, r1]; grind
    by_cases hrow : r1 ≤ r0
    · obtain ⟨v, hv, h1d⟩ := ternary_1d_dim2_vec (W 0 0) (W 0 1)
      let u : Fin 2 → Int := fun i => if i.val = 0 then 1 else 0
      refine ⟨u, v, ⟨fun i => by match i with | ⟨0, _⟩ => simp [u] | ⟨1, _⟩ => simp [u], ⟨0, by decide⟩⟩, hv, ?_⟩
      have hun : vecSqNormInt u = 1 := by decide
      have hq : quadFormRat W u v = W 0 0 * (v 0 : Rat) + W 0 1 * (v 1 : Rat) := by
        simp only [quadFormRat, sumFinRat, u, Fin.val_castSucc, Fin.val_last, ↓reduceIte, Nat.one_ne_zero]
        have h00 : (Fin.castSucc (Fin.last 0) : Fin 2) = 0 := rfl
        have h11 : (Fin.last 1 : Fin 2) = 1 := rfl
        rw [h00, h11]; grind
      rw [hun, Int.one_mul, hq, hfrob]
      have hvn : 0 ≤ (vecSqNormInt v : Rat) := by
        have hv0 : 0 ≤ (v 0 : Rat) * (v 0 : Rat) := rat_sq_nonneg _
        have hv1 : 0 ≤ (v 1 : Rat) * (v 1 : Rat) := rat_sq_nonneg _
        simp only [vecSqNormInt, sumFinInt]
        grind
      have hd : 0 ≤ (r0 - r1) * (vecSqNormInt v : Rat) := Rat.mul_nonneg (by grind) hvn
      have hsplit : QSqrt2.ofRat ((W 0 0 * (v 0 : Rat) + W 0 1 * (v 1 : Rat)) *
                                  (W 0 0 * (v 0 : Rat) + W 0 1 * (v 1 : Rat))) -
            QSqrt2.alpha2x2 * QSqrt2.ofRat (r0 + r1) * QSqrt2.ofInt (vecSqNormInt v) =
          ⟨(QSqrt2.ofRat ((W 0 0 * (v 0 : Rat) + W 0 1 * (v 1 : Rat)) *
                          (W 0 0 * (v 0 : Rat) + W 0 1 * (v 1 : Rat))) -
            (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat r0 * QSqrt2.ofInt (vecSqNormInt v)).a +
            (1 / 4) * ((r0 - r1) * (vecSqNormInt v : Rat)),
           (QSqrt2.ofRat ((W 0 0 * (v 0 : Rat) + W 0 1 * (v 1 : Rat)) *
                          (W 0 0 * (v 0 : Rat) + W 0 1 * (v 1 : Rat))) -
            (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat r0 * QSqrt2.ofInt (vecSqNormInt v)).b +
            (1 / 8) * ((r0 - r1) * (vecSqNormInt v : Rat))⟩ := by
        simp only [QSqrt2.alpha2x2, QSqrt2.ofRat, QSqrt2.ofInt, q2_mul_mk, q2_sub_mk]
        congr 1 <;> grind
      show QSqrt2.nonneg _
      rw [hsplit]
      exact qsqrt2_nonneg_add_nonneg_pair h1d (by grind) (by grind)
    · have hrow' : r0 ≤ r1 := Rat.le_of_lt (Rat.not_le.mp hrow)
      obtain ⟨v, hv, h1d⟩ := ternary_1d_dim2_vec (W 1 0) (W 1 1)
      let u : Fin 2 → Int := fun i => if i.val = 1 then 1 else 0
      refine ⟨u, v, ⟨fun i => by match i with | ⟨0, _⟩ => simp [u] | ⟨1, _⟩ => simp [u], ⟨1, by decide⟩⟩, hv, ?_⟩
      have hun : vecSqNormInt u = 1 := by decide
      have hq : quadFormRat W u v = W 1 0 * (v 0 : Rat) + W 1 1 * (v 1 : Rat) := by
        simp only [quadFormRat, sumFinRat, u, Fin.val_castSucc, Fin.val_last, ↓reduceIte, Nat.zero_ne_one]
        have h00 : (Fin.castSucc (Fin.last 0) : Fin 2) = 0 := rfl
        have h11 : (Fin.last 1 : Fin 2) = 1 := rfl
        rw [h00, h11]; grind
      rw [hun, Int.one_mul, hq, hfrob]
      have hvn : 0 ≤ (vecSqNormInt v : Rat) := by
        have hv0 : 0 ≤ (v 0 : Rat) * (v 0 : Rat) := rat_sq_nonneg _
        have hv1 : 0 ≤ (v 1 : Rat) * (v 1 : Rat) := rat_sq_nonneg _
        simp only [vecSqNormInt, sumFinInt]
        grind
      have hd : 0 ≤ (r1 - r0) * (vecSqNormInt v : Rat) := Rat.mul_nonneg (by grind) hvn
      have hsplit : QSqrt2.ofRat ((W 1 0 * (v 0 : Rat) + W 1 1 * (v 1 : Rat)) *
                                  (W 1 0 * (v 0 : Rat) + W 1 1 * (v 1 : Rat))) -
            QSqrt2.alpha2x2 * QSqrt2.ofRat (r0 + r1) * QSqrt2.ofInt (vecSqNormInt v) =
          ⟨(QSqrt2.ofRat ((W 1 0 * (v 0 : Rat) + W 1 1 * (v 1 : Rat)) *
                          (W 1 0 * (v 0 : Rat) + W 1 1 * (v 1 : Rat))) -
            (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat r1 * QSqrt2.ofInt (vecSqNormInt v)).a +
            (1 / 4) * ((r1 - r0) * (vecSqNormInt v : Rat)),
           (QSqrt2.ofRat ((W 1 0 * (v 0 : Rat) + W 1 1 * (v 1 : Rat)) *
                          (W 1 0 * (v 0 : Rat) + W 1 1 * (v 1 : Rat))) -
            (⟨1 / 2, 1 / 4⟩ : QSqrt2) * QSqrt2.ofRat r1 * QSqrt2.ofInt (vecSqNormInt v)).b +
            (1 / 8) * ((r1 - r0) * (vecSqNormInt v : Rat))⟩ := by
        simp only [QSqrt2.alpha2x2, QSqrt2.ofRat, QSqrt2.ofInt, q2_mul_mk, q2_sub_mk]
        congr 1 <;> grind
      show QSqrt2.nonneg _
      rw [hsplit]
      exact qsqrt2_nonneg_add_nonneg_pair h1d (by grind) (by grind)
  · refine ⟨W_rot2x2_frobSq, W_rot2x2_alpha_mul_frobSq, W_rot2x2_upper_bound, ?_⟩
    let e0 : Fin 2 → Int := fun i => if i.val = 0 then 1 else 0
    refine ⟨e0, e0,
      ⟨fun i => by match i with | ⟨0, _⟩ => simp [e0] | ⟨1, _⟩ => simp [e0], ⟨0, by decide⟩⟩,
      ⟨fun i => by match i with | ⟨0, _⟩ => simp [e0] | ⟨1, _⟩ => simp [e0], ⟨0, by decide⟩⟩, ?_⟩
    rw [W_rot2x2_alpha_mul_frobSq]
    simp only [quadFormQ2, sumFinQ2, W_rot2x2, vecSqNormInt, sumFinInt, e0,
               QSqrt2.zero, QSqrt2.one, QSqrt2.ofInt, Fin.val_castSucc, Fin.val_last,
               ↓reduceIte, Nat.one_ne_zero, q2_add_mk, q2_mul_mk]
    congr 1 <;> grind

end LoftqCyclesRank1
