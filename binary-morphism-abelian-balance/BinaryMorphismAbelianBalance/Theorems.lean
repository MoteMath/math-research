/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BinaryMorphismAbelianBalance.Defs

/-!
# Theorems (`binary-morphism-abelian-balance`)

Full proofs of the headline infinite theorems of Binary Word-Morphism Modular-Stratified Abelian Balance Engine.
-/

namespace MSQRPAIE

theorem neg_sq (a : Int) : (-a) * (-a) = a * a := by
  rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have := Int.mul_nonneg h' h'
    rw [neg_sq] at this
    exact this

theorem sq_pos_of_ne_zero {a : Int} (h : a ≠ 0) : 0 < a * a := by
  by_cases h1 : 0 < a
  · exact Int.mul_pos h1 h1
  · have h2 : 0 < -a := by omega
    have := Int.mul_pos h2 h2
    rw [neg_sq] at this
    exact this

theorem mul_le_mul_nonneg {a b c d : Int}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d := by
  have h1 : a * c ≤ b * c := Int.mul_le_mul_of_nonneg_right hab hc
  have h2 : b * c ≤ b * d := Int.mul_le_mul_of_nonneg_left hcd (by omega)
  omega

theorem mul_lt_mul_pos {a b c d : Int}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a < b) (hcd : c < d) : a * c < b * d := by
  have hb : 0 < b := by omega
  have h1 : a * c ≤ b * c := Int.mul_le_mul_of_nonneg_right (by omega) hc
  have h2 : b * c < b * d := Int.mul_lt_mul_of_pos_left hcd hb
  omega

theorem le_of_sq_le_sq {a b : Int} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have h1 : b * b < a * a := mul_lt_mul_pos hb hb (by omega) (by omega)
    omega

theorem lt_of_sq_lt_sq {a b : Int} (hb : 0 ≤ b) (h : a * a < b * b) : a < b := by
  by_cases hab : a < b
  · exact hab
  · have h1 : b * b ≤ a * a := mul_le_mul_nonneg hb hb (by omega) (by omega)
    omega

theorem sq_cancel_pos {k a b : Int} (hk : 0 < k) (h : k * a ≤ k * b) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have := Int.mul_lt_mul_of_pos_left (by omega : b < a) hk
    omega

theorem sq_cancel_pos_lt {k a b : Int} (hk : 0 < k) (h : k * a < k * b) : a < b := by
  by_cases hab : a < b
  · exact hab
  · have := Int.mul_le_mul_of_nonneg_left (by omega : b ≤ a) (by omega : 0 ≤ k)
    omega

theorem sub_sq_gt_left {d a b u v : Int}
    (ha : 0 ≤ a) (hu : 0 < u) (hv : 0 ≤ v) (hvu : v < u)
    (h1 : d * (u * u) < a * a) (h2 : b * b ≤ d * (v * v)) :
    d * ((u - v) * (u - v)) < (a - b) * (a - b) := by
  have hav_bu : b * u ≤ a * v := by
    apply le_of_sq_le_sq (Int.mul_nonneg ha hv)
    have e1 : (b * u) * (b * u) = (b * b) * (u * u) := by grind
    have e2 : (a * v) * (a * v) = (a * a) * (v * v) := by grind
    have m1 : (b * b) * (u * u) ≤ (d * (v * v)) * (u * u) :=
      Int.mul_le_mul_of_nonneg_right h2 (sq_nonneg u)
    have m2 : (d * (u * u)) * (v * v) ≤ (a * a) * (v * v) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (sq_nonneg v)
    have eqm : (d * (v * v)) * (u * u) = (d * (u * u)) * (v * v) := by grind
    omega
  have hstep : a * (u - v) ≤ u * (a - b) := by
    have e1 : a * (u - v) = a * u - a * v := Int.mul_sub a u v
    have e2 : u * (a - b) = a * u - b * u := by grind
    omega
  have hsq : (a * (u - v)) * (a * (u - v)) ≤ (u * (a - b)) * (u * (a - b)) :=
    mul_le_mul_nonneg (Int.mul_nonneg ha (by omega)) (Int.mul_nonneg ha (by omega)) hstep hstep
  have e3 : (a * (u - v)) * (a * (u - v)) = (a * a) * ((u - v) * (u - v)) := by grind
  have e4 : (u * (a - b)) * (u * (a - b)) = (u * u) * ((a - b) * (a - b)) := by grind
  have h5 : (d * (u * u)) * ((u - v) * (u - v)) < (a * a) * ((u - v) * (u - v)) :=
    Int.mul_lt_mul_of_pos_right h1 (sq_pos_of_ne_zero (by omega))
  have eq5 : (u * u) * (d * ((u - v) * (u - v))) = (d * (u * u)) * ((u - v) * (u - v)) := by grind
  have h6 : (u * u) * (d * ((u - v) * (u - v))) < (u * u) * ((a - b) * (a - b)) := by omega
  exact sq_cancel_pos_lt (sq_pos_of_ne_zero (by omega : u ≠ 0)) h6

theorem sub_sq_lt_right {d a b u v : Int}
    (hb : 0 ≤ b) (hab : b ≤ a) (hu : 0 < u) (_hvu : v < u)
    (h1 : a * a ≤ d * (u * u)) (h2 : d * (v * v) < b * b) :
    (a - b) * (a - b) < d * ((u - v) * (u - v)) := by
  have hav_bu : a * v < b * u := by
    apply lt_of_sq_lt_sq (Int.mul_nonneg hb (by omega))
    have e1 : (a * v) * (a * v) = (a * a) * (v * v) := by grind
    have e2 : (b * u) * (b * u) = (b * b) * (u * u) := by grind
    have m1 : (a * a) * (v * v) ≤ (d * (u * u)) * (v * v) :=
      Int.mul_le_mul_of_nonneg_right h1 (sq_nonneg v)
    have m2 : (d * (v * v)) * (u * u) < (b * b) * (u * u) :=
      Int.mul_lt_mul_of_pos_right h2 (sq_pos_of_ne_zero (by omega))
    have eqm : (d * (u * u)) * (v * v) = (d * (v * v)) * (u * u) := by grind
    omega
  have hstep : u * (a - b) < a * (u - v) := by
    have e1 : a * (u - v) = a * u - a * v := Int.mul_sub a u v
    have e2 : u * (a - b) = a * u - b * u := by grind
    omega
  have hsq : (u * (a - b)) * (u * (a - b)) < (a * (u - v)) * (a * (u - v)) :=
    mul_lt_mul_pos (Int.mul_nonneg (by omega) (by omega)) (Int.mul_nonneg (by omega) (by omega)) hstep hstep
  have e3 : (a * (u - v)) * (a * (u - v)) = (a * a) * ((u - v) * (u - v)) := by grind
  have e4 : (u * (a - b)) * (u * (a - b)) = (u * u) * ((a - b) * (a - b)) := by grind
  have h5 : (a * a) * ((u - v) * (u - v)) ≤ (d * (u * u)) * ((u - v) * (u - v)) :=
    Int.mul_le_mul_of_nonneg_right h1 (sq_nonneg (u - v))
  have eq5 : (u * u) * (d * ((u - v) * (u - v))) = (d * (u * u)) * ((u - v) * (u - v)) := by grind
  have h6 : (u * u) * ((a - b) * (a - b)) < (u * u) * (d * ((u - v) * (u - v))) := by omega
  exact sq_cancel_pos_lt (sq_pos_of_ne_zero (by omega : u ≠ 0)) h6

theorem add_sq_gt_left {d a b u v : Int}
    (hd : 0 < d) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : d * (u * u) < a * a) (h2 : d * (v * v) ≤ b * b) :
    d * ((u + v) * (u + v)) < (a + b) * (a + b) := by
  have hcross : d * (u * v) ≤ a * b := by
    apply le_of_sq_le_sq (Int.mul_nonneg ha hb)
    have e1 : (d * (u * v)) * (d * (u * v)) = (d * (u * u)) * (d * (v * v)) := by grind
    have e2 : (a * b) * (a * b) = (a * a) * (b * b) := by grind
    have m := mul_le_mul_nonneg (Int.mul_nonneg (by omega : 0 ≤ d) (sq_nonneg u))
                                (Int.mul_nonneg (by omega : 0 ≤ d) (sq_nonneg v)) (by omega : d * (u * u) ≤ a * a) h2
    omega
  have eL : d * ((u + v) * (u + v)) = d * (u * u) + 2 * (d * (u * v)) + d * (v * v) := by grind
  have eR : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by grind
  omega

theorem add_sq_lt_left {d a b u v : Int}
    (hd : 0 < d) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h1 : a * a < d * (u * u)) (h2 : b * b ≤ d * (v * v)) :
    (a + b) * (a + b) < d * ((u + v) * (u + v)) := by
  have hcross : a * b ≤ d * (u * v) := by
    apply le_of_sq_le_sq (Int.mul_nonneg (by omega) (Int.mul_nonneg hu hv))
    have e1 : (a * b) * (a * b) = (a * a) * (b * b) := by grind
    have e2 : (d * (u * v)) * (d * (u * v)) = (d * (u * u)) * (d * (v * v)) := by grind
    have m := mul_le_mul_nonneg (sq_nonneg a) (sq_nonneg b) (by omega : a * a ≤ d * (u * u)) h2
    omega
  have eL : d * ((u + v) * (u + v)) = d * (u * u) + 2 * (d * (u * v)) + d * (v * v) := by grind
  have eR : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by grind
  omega

theorem signSqrtGe_iff (d : Nat) (X Y : Int) :
    signSqrtGe d X Y = true ↔
      (0 ≤ Y ∧ 0 ≤ X ∧ (d : Int) * (Y * Y) ≤ X * X) ∨
      (Y < 0 ∧ (0 ≤ X ∨ X * X ≤ (d : Int) * (Y * Y))) := by
  unfold signSqrtGe
  by_cases h0 : Y = 0
  · subst h0
    simp only [beq_self_eq_true, ↓reduceIte, decide_eq_true_eq, Int.mul_zero, Int.lt_irrefl,
               false_and, or_false]
    constructor
    · intro hx; exact ⟨Int.le_refl 0, hx, sq_nonneg X⟩
    · intro h; exact h.2.1
  · have hne : (Y == 0) = false := beq_false_of_ne h0
    rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hp : 0 < Y
    · simp [hp]; omega
    · simp [hp]; omega

theorem signSqrtGt_iff (d : Nat) (X Y : Int) :
    signSqrtGt d X Y = true ↔
      (Y = 0 ∧ 0 < X) ∨
      (0 < Y ∧ 0 < X ∧ (d : Int) * (Y * Y) < X * X) ∨
      (Y < 0 ∧ (0 ≤ X ∨ X * X < (d : Int) * (Y * Y))) := by
  unfold signSqrtGt
  by_cases h0 : Y = 0
  · subst h0; simp
  · have hne : (Y == 0) = false := beq_false_of_ne h0
    rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hp : 0 < Y
    · simp [hp]; omega
    · simp [hp]; omega

theorem signSqrtGt_imp_ge {d : Nat} {X Y : Int} (h : signSqrtGt d X Y = true) :
    signSqrtGe d X Y = true := by
  rw [signSqrtGt_iff] at h
  rw [signSqrtGe_iff]
  rcases h with ⟨rfl, hx⟩ | ⟨hy, hx, hsq⟩ | ⟨hy, hcase⟩
  · left; refine ⟨by omega, by omega, ?_⟩; simp; exact sq_nonneg X
  · left; exact ⟨by omega, by omega, by omega⟩
  · right; refine ⟨hy, ?_⟩; rcases hcase with hx | hsq; exact Or.inl hx; exact Or.inr (by omega)

theorem signSqrtGt_not_neg {d : Nat} (hd : 0 < d) {X Y : Int}
    (h1 : signSqrtGt d X Y = true) (h2 : signSqrtGe d (-X) (-Y) = true) : False := by
  rw [signSqrtGt_iff] at h1
  rw [signSqrtGe_iff] at h2
  have eqX : (-X) * (-X) = X * X := neg_sq X
  have eqY : (-Y) * (-Y) = Y * Y := neg_sq Y
  rcases h1 with ⟨rfl, hx⟩ | ⟨hy, hx, hsq⟩ | ⟨hy, hcase⟩
  · rcases h2 with ⟨_, hnx, _⟩ | ⟨hny, _⟩ <;> omega
  · rcases h2 with ⟨hny, _, _⟩ | ⟨_, hnx | hnsq⟩
    · omega
    · omega
    · rw [eqX, eqY] at hnsq; omega
  · rcases h2 with ⟨_, hnx, hnsq⟩ | ⟨hny, _⟩
    · rw [eqX, eqY] at hnsq
      rcases hcase with hx | hsq
      · have hx0 : X = 0 := by omega
        subst hx0
        have hpos : 0 < (d : Int) * (Y * Y) := Int.mul_pos (by omega) (sq_pos_of_ne_zero (by omega))
        simp at hnsq; omega
      · omega
    · omega

/-- Core strict + non-strict addition theorem in `ℤ[√d]`. -/
theorem signSqrtGt_add_ge {d : Nat} (hd : 0 < d) {X1 Y1 X2 Y2 : Int}
    (h1 : signSqrtGt d X1 Y1 = true) (h2 : signSqrtGe d X2 Y2 = true) :
    signSqrtGt d (X1 + X2) (Y1 + Y2) = true := by
  have hdI : (0 : Int) < (d : Int) := by omega
  rw [signSqrtGt_iff] at h1
  rw [signSqrtGe_iff] at h2
  rw [signSqrtGt_iff]
  have pos_of_ge_negY1 : ∀ {x1 y1 x2 y2 : Int},
      y1 < 0 → 0 ≤ x1 →
      ((0 ≤ y2 ∧ 0 ≤ x2 ∧ (d : Int) * (y2 * y2) ≤ x2 * x2) ∨
       (y2 < 0 ∧ (0 ≤ x2 ∨ x2 * x2 ≤ (d : Int) * (y2 * y2)))) →
      (y1 + y2 = 0 ∧ 0 < x1 + x2) ∨
      (0 < y1 + y2 ∧ 0 < x1 + x2 ∧ (d : Int) * ((y1 + y2) * (y1 + y2)) < (x1 + x2) * (x1 + x2)) ∨
      (y1 + y2 < 0 ∧ (0 ≤ x1 + x2 ∨ (x1 + x2) * (x1 + x2) < (d : Int) * ((y1 + y2) * (y1 + y2)))) := by
    intro x1 y1 x2 y2 hy1 hx1 h2'
    rcases h2' with ⟨hy2, hx2, hsq2⟩ | ⟨hy2, hx2 | hsq2⟩
    · by_cases hy : y1 + y2 = 0
      · left
        refine ⟨hy, ?_⟩
        by_cases hx20 : x2 = 0
        · subst hx20
          have hpos : 0 < (d : Int) * (y2 * y2) := Int.mul_pos hdI (sq_pos_of_ne_zero (by omega))
          simp at hsq2; omega
        · omega
      · by_cases hyp : 0 < y1 + y2
        · right; left
          have hX2p : 0 < x2 := by
            by_cases hx20 : x2 = 0
            · subst hx20
              have hpos : 0 < (d : Int) * (y2 * y2) := Int.mul_pos hdI (sq_pos_of_ne_zero (by omega))
              simp at hsq2; omega
            · omega
          refine ⟨hyp, by omega, ?_⟩
          have m1 : (y1 + y2) * (y1 + y2) < y2 * y2 := mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
          have m2 : (d : Int) * ((y1 + y2) * (y1 + y2)) < (d : Int) * (y2 * y2) := Int.mul_lt_mul_of_pos_left m1 hdI
          have m3 : x2 * x2 ≤ (x1 + x2) * (x1 + x2) := mul_le_mul_nonneg hx2 hx2 (by omega) (by omega)
          omega
        · right; right; exact ⟨by omega, Or.inl (by omega)⟩
    · right; right; exact ⟨by omega, Or.inl (by omega)⟩
    · right; right
      refine ⟨by omega, ?_⟩
      by_cases hs : 0 ≤ x1 + x2
      · exact Or.inl hs
      · right
        have hlt : (-(x1 + x2)) * (-(x1 + x2)) ≤ (-x2) * (-x2) :=
          mul_le_mul_nonneg (by omega) (by omega) (by omega) (by omega)
        have m1 : (-y2) * (-y2) < (-(y1 + y2)) * (-(y1 + y2)) :=
          mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
        have m2 : (d : Int) * ((-y2) * (-y2)) < (d : Int) * ((-(y1 + y2)) * (-(y1 + y2))) :=
          Int.mul_lt_mul_of_pos_left m1 hdI
        rw [neg_sq, neg_sq] at hlt
        rw [neg_sq, neg_sq] at m2
        omega
  rcases h1 with ⟨rfl, hx1⟩ | ⟨hy1, hx1, hsq1⟩ | ⟨hy1, hx1 | hsq1⟩
  · rcases h2 with ⟨hy2, hx2, hsq2⟩ | ⟨hy2, hx2 | hsq2⟩
    · by_cases hy20 : Y2 = 0
      · subst hy20; left; omega
      · right; left
        refine ⟨by omega, by omega, ?_⟩
        have hlt : X2 * X2 < (X1 + X2) * (X1 + X2) := mul_lt_mul_pos hx2 hx2 (by omega) (by omega)
        simp; omega
    · right; right; exact ⟨by omega, Or.inl (by omega)⟩
    · right; right
      refine ⟨by omega, ?_⟩
      by_cases hs : 0 ≤ X1 + X2
      · exact Or.inl hs
      · right
        have hlt : (-(X1 + X2)) * (-(X1 + X2)) < (-X2) * (-X2) :=
          mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
        rw [neg_sq, neg_sq] at hlt
        simp; omega
  · rcases h2 with ⟨hy2, hx2, hsq2⟩ | ⟨hy2, hx2 | hsq2⟩
    · right; left
      exact ⟨by omega, by omega, add_sq_gt_left hdI (by omega) hx2 hsq1 hsq2⟩
    · by_cases hy : Y1 + Y2 = 0
      · left; exact ⟨hy, by omega⟩
      · by_cases hyp : 0 < Y1 + Y2
        · right; left
          refine ⟨hyp, by omega, ?_⟩
          have m1 : (Y1 + Y2) * (Y1 + Y2) < Y1 * Y1 := mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
          have m2 : (d : Int) * ((Y1 + Y2) * (Y1 + Y2)) < (d : Int) * (Y1 * Y1) := Int.mul_lt_mul_of_pos_left m1 hdI
          have m3 : X1 * X1 ≤ (X1 + X2) * (X1 + X2) := mul_le_mul_nonneg (by omega) (by omega) (by omega) (by omega)
          omega
        · right; right; exact ⟨by omega, Or.inl (by omega)⟩
    · by_cases hx2p : 0 ≤ X2
      · by_cases hy : Y1 + Y2 = 0
        · left; exact ⟨hy, by omega⟩
        · by_cases hyp : 0 < Y1 + Y2
          · right; left
            refine ⟨hyp, by omega, ?_⟩
            have m1 : (Y1 + Y2) * (Y1 + Y2) < Y1 * Y1 := mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
            have m2 : (d : Int) * ((Y1 + Y2) * (Y1 + Y2)) < (d : Int) * (Y1 * Y1) := Int.mul_lt_mul_of_pos_left m1 hdI
            have m3 : X1 * X1 ≤ (X1 + X2) * (X1 + X2) := mul_le_mul_nonneg (by omega) (by omega) (by omega) (by omega)
            omega
          · right; right; exact ⟨by omega, Or.inl (by omega)⟩
      · have hsq2' : (-X2) * (-X2) ≤ (d : Int) * ((-Y2) * (-Y2)) := by rw [neg_sq, neg_sq]; exact hsq2
        by_cases hy : Y1 + Y2 = 0
        · left
          refine ⟨hy, ?_⟩
          have heq : -Y2 = Y1 := by omega
          rw [heq] at hsq2'
          have hlt2 := lt_of_sq_lt_sq (by omega) (by omega : (-X2) * (-X2) < X1 * X1)
          omega
        · by_cases hyp : 0 < Y1 + Y2
          · have hXgt : -X2 < X1 := by
              apply lt_of_sq_lt_sq (by omega)
              have m1 : (-Y2) * (-Y2) < Y1 * Y1 := mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
              have m2 : (d : Int) * ((-Y2) * (-Y2)) < (d : Int) * (Y1 * Y1) := Int.mul_lt_mul_of_pos_left m1 hdI
              omega
            right; left
            refine ⟨hyp, by omega, ?_⟩
            have hsub := sub_sq_gt_left (by omega) hy1 (by omega) (by omega) hsq1 hsq2'
            have e1 : Y1 - (-Y2) = Y1 + Y2 := by omega
            have e2 : X1 - (-X2) = X1 + X2 := by omega
            rw [e1, e2] at hsub; exact hsub
          · right; right
            refine ⟨by omega, ?_⟩
            by_cases hs : 0 ≤ X1 + X2
            · exact Or.inl hs
            · right
              have hsub := sub_sq_lt_right (by omega) (by omega) (by omega) (by omega) hsq2' hsq1
              have e1 : (-X2 - X1) * (-X2 - X1) = (X1 + X2) * (X1 + X2) := by grind
              have e2 : (-Y2 - Y1) * (-Y2 - Y1) = (Y1 + Y2) * (Y1 + Y2) := by grind
              rw [e1, e2] at hsub; exact hsub
  · exact pos_of_ge_negY1 hy1 hx1 h2
  · by_cases hx1p : 0 ≤ X1
    · exact pos_of_ge_negY1 hy1 hx1p h2
    · have hsq1' : (-X1) * (-X1) < (d : Int) * ((-Y1) * (-Y1)) := by rw [neg_sq, neg_sq]; exact hsq1
      rcases h2 with ⟨hy2, hx2, hsq2⟩ | ⟨hy2, hx2 | hsq2⟩
      · by_cases hy : Y1 + Y2 = 0
        · left
          refine ⟨hy, ?_⟩
          have heq : -Y1 = Y2 := by omega
          rw [heq] at hsq1'
          have hlt2 := lt_of_sq_lt_sq hx2 (by omega : (-X1) * (-X1) < X2 * X2)
          omega
        · by_cases hyp : 0 < Y1 + Y2
          · have hXgt : -X1 < X2 := by
              apply lt_of_sq_lt_sq hx2
              have m1 : (-Y1) * (-Y1) < Y2 * Y2 := mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
              have m2 : (d : Int) * ((-Y1) * (-Y1)) < (d : Int) * (Y2 * Y2) := Int.mul_lt_mul_of_pos_left m1 hdI
              omega
            right; left
            refine ⟨hyp, by omega, ?_⟩
            have hav_bu : (-X1) * Y2 < X2 * (-Y1) := by
              apply lt_of_sq_lt_sq (Int.mul_nonneg hx2 (by omega))
              have e1 : ((-X1) * Y2) * ((-X1) * Y2) = ((-X1) * (-X1)) * (Y2 * Y2) := by grind
              have e2 : (X2 * (-Y1)) * (X2 * (-Y1)) = (X2 * X2) * ((-Y1) * (-Y1)) := by grind
              have m1 : ((-X1) * (-X1)) * (Y2 * Y2) < ((d : Int) * ((-Y1) * (-Y1))) * (Y2 * Y2) :=
                Int.mul_lt_mul_of_pos_right hsq1' (sq_pos_of_ne_zero (by omega))
              have m2 : ((d : Int) * (Y2 * Y2)) * ((-Y1) * (-Y1)) ≤ (X2 * X2) * ((-Y1) * (-Y1)) :=
                Int.mul_le_mul_of_nonneg_right hsq2 (sq_nonneg (-Y1))
              have eqm : ((d : Int) * ((-Y1) * (-Y1))) * (Y2 * Y2) = ((d : Int) * (Y2 * Y2)) * ((-Y1) * (-Y1)) := by grind
              omega
            have hstep : X2 * (Y2 - (-Y1)) < Y2 * (X2 - (-X1)) := by
              have e1 : X2 * (Y2 - (-Y1)) = X2 * Y2 - X2 * (-Y1) := Int.mul_sub X2 Y2 (-Y1)
              have e2 : Y2 * (X2 - (-X1)) = X2 * Y2 - (-X1) * Y2 := by grind
              omega
            have hsq : (X2 * (Y2 - (-Y1))) * (X2 * (Y2 - (-Y1))) < (Y2 * (X2 - (-X1))) * (Y2 * (X2 - (-X1))) :=
              mul_lt_mul_pos (Int.mul_nonneg hx2 (by omega)) (Int.mul_nonneg hx2 (by omega)) hstep hstep
            have e3 : (X2 * (Y2 - (-Y1))) * (X2 * (Y2 - (-Y1))) = (X2 * X2) * ((Y2 - (-Y1)) * (Y2 - (-Y1))) := by grind
            have e4 : (Y2 * (X2 - (-X1))) * (Y2 * (X2 - (-X1))) = (Y2 * Y2) * ((X2 - (-X1)) * (X2 - (-X1))) := by grind
            have h5 : ((d : Int) * (Y2 * Y2)) * ((Y2 - (-Y1)) * (Y2 - (-Y1))) ≤ (X2 * X2) * ((Y2 - (-Y1)) * (Y2 - (-Y1))) :=
              Int.mul_le_mul_of_nonneg_right hsq2 (sq_nonneg _)
            have eq5 : (Y2 * Y2) * ((d : Int) * ((Y2 - (-Y1)) * (Y2 - (-Y1)))) =
                       ((d : Int) * (Y2 * Y2)) * ((Y2 - (-Y1)) * (Y2 - (-Y1))) := by grind
            have h6 : (Y2 * Y2) * ((d : Int) * ((Y2 - (-Y1)) * (Y2 - (-Y1)))) < (Y2 * Y2) * ((X2 - (-X1)) * (X2 - (-X1))) := by omega
            have hfin := sq_cancel_pos_lt (sq_pos_of_ne_zero (by omega : Y2 ≠ 0)) h6
            have e5 : Y2 - (-Y1) = Y1 + Y2 := by omega
            have e6 : X2 - (-X1) = X1 + X2 := by omega
            rw [e5, e6] at hfin; exact hfin
          · right; right
            refine ⟨by omega, ?_⟩
            by_cases hs : 0 ≤ X1 + X2
            · exact Or.inl hs
            · right
              have hav_bu : (-X1) * Y2 ≤ X2 * (-Y1) := by
                apply le_of_sq_le_sq (Int.mul_nonneg hx2 (by omega))
                have e1 : ((-X1) * Y2) * ((-X1) * Y2) = ((-X1) * (-X1)) * (Y2 * Y2) := by grind
                have e2 : (X2 * (-Y1)) * (X2 * (-Y1)) = (X2 * X2) * ((-Y1) * (-Y1)) := by grind
                have m1 : ((-X1) * (-X1)) * (Y2 * Y2) ≤ ((d : Int) * ((-Y1) * (-Y1))) * (Y2 * Y2) :=
                  Int.mul_le_mul_of_nonneg_right (by omega) (sq_nonneg Y2)
                have m2 : ((d : Int) * (Y2 * Y2)) * ((-Y1) * (-Y1)) ≤ (X2 * X2) * ((-Y1) * (-Y1)) :=
                  Int.mul_le_mul_of_nonneg_right hsq2 (sq_nonneg (-Y1))
                have eqm : ((d : Int) * ((-Y1) * (-Y1))) * (Y2 * Y2) = ((d : Int) * (Y2 * Y2)) * ((-Y1) * (-Y1)) := by grind
                omega
              have hstep : (-Y1) * (-X1 - X2) ≤ (-X1) * (-Y1 - Y2) := by
                have e1 : (-X1) * (-Y1 - Y2) = (-X1) * (-Y1) - (-X1) * Y2 := Int.mul_sub (-X1) (-Y1) Y2
                have e2 : (-Y1) * (-X1 - X2) = (-X1) * (-Y1) - X2 * (-Y1) := by grind
                omega
              have hsq : ((-Y1) * (-X1 - X2)) * ((-Y1) * (-X1 - X2)) ≤ ((-X1) * (-Y1 - Y2)) * ((-X1) * (-Y1 - Y2)) :=
                mul_le_mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (Int.mul_nonneg (by omega) (by omega)) hstep hstep
              have e3 : ((-X1) * (-Y1 - Y2)) * ((-X1) * (-Y1 - Y2)) = ((-X1) * (-X1)) * ((-Y1 - Y2) * (-Y1 - Y2)) := by grind
              have e4 : ((-Y1) * (-X1 - X2)) * ((-Y1) * (-X1 - X2)) = ((-Y1) * (-Y1)) * ((-X1 - X2) * (-X1 - X2)) := by grind
              have h5 : ((-X1) * (-X1)) * ((-Y1 - Y2) * (-Y1 - Y2)) < ((d : Int) * ((-Y1) * (-Y1))) * ((-Y1 - Y2) * (-Y1 - Y2)) :=
                Int.mul_lt_mul_of_pos_right hsq1' (sq_pos_of_ne_zero (by omega))
              have eq5 : ((-Y1) * (-Y1)) * ((d : Int) * ((-Y1 - Y2) * (-Y1 - Y2))) =
                         ((d : Int) * ((-Y1) * (-Y1))) * ((-Y1 - Y2) * (-Y1 - Y2)) := by grind
              have h6 : ((-Y1) * (-Y1)) * ((-X1 - X2) * (-X1 - X2)) < ((-Y1) * (-Y1)) * ((d : Int) * ((-Y1 - Y2) * (-Y1 - Y2))) := by omega
              have hfin := sq_cancel_pos_lt (sq_pos_of_ne_zero (by omega : -Y1 ≠ 0)) h6
              have e5 : (-X1 - X2) * (-X1 - X2) = (X1 + X2) * (X1 + X2) := by grind
              have e6 : (-Y1 - Y2) * (-Y1 - Y2) = (Y1 + Y2) * (Y1 + Y2) := by grind
              rw [e5, e6] at hfin; exact hfin
      · right; right
        refine ⟨by omega, ?_⟩
        by_cases hs : 0 ≤ X1 + X2
        · exact Or.inl hs
        · right
          have hlt : (-(X1 + X2)) * (-(X1 + X2)) ≤ (-X1) * (-X1) :=
            mul_le_mul_nonneg (by omega) (by omega) (by omega) (by omega)
          have m1 : (-Y1) * (-Y1) < (-(Y1 + Y2)) * (-(Y1 + Y2)) :=
            mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
          have m2 : (d : Int) * ((-Y1) * (-Y1)) < (d : Int) * ((-(Y1 + Y2)) * (-(Y1 + Y2))) :=
            Int.mul_lt_mul_of_pos_left m1 hdI
          rw [neg_sq, neg_sq] at hlt
          rw [neg_sq, neg_sq] at m2
          omega
      · right; right
        refine ⟨by omega, ?_⟩
        by_cases hs : 0 ≤ X1 + X2
        · exact Or.inl hs
        · by_cases hx2p : 0 ≤ X2
          · right
            have hlt : (-(X1 + X2)) * (-(X1 + X2)) ≤ (-X1) * (-X1) :=
              mul_le_mul_nonneg (by omega) (by omega) (by omega) (by omega)
            have m1 : (-Y1) * (-Y1) < (-(Y1 + Y2)) * (-(Y1 + Y2)) :=
              mul_lt_mul_pos (by omega) (by omega) (by omega) (by omega)
            have m2 : (d : Int) * ((-Y1) * (-Y1)) < (d : Int) * ((-(Y1 + Y2)) * (-(Y1 + Y2))) :=
              Int.mul_lt_mul_of_pos_left m1 hdI
            rw [neg_sq, neg_sq] at hlt
            rw [neg_sq, neg_sq] at m2
            omega
          · right
            have hsq2' : (-X2) * (-X2) ≤ (d : Int) * ((-Y2) * (-Y2)) := by rw [neg_sq, neg_sq]; exact hsq2
            have hadd := add_sq_lt_left hdI (by omega) (by omega) hsq1' hsq2'
            have e1 : (-X1 + -X2) * (-X1 + -X2) = (X1 + X2) * (X1 + X2) := by grind
            have e2 : (-Y1 + -Y2) * (-Y1 + -Y2) = (Y1 + Y2) * (Y1 + Y2) := by grind
            rw [e1, e2] at hadd; exact hadd

theorem signSqrtGe_add_gt {d : Nat} (hd : 0 < d) {X1 Y1 X2 Y2 : Int}
    (h1 : signSqrtGe d X1 Y1 = true) (h2 : signSqrtGt d X2 Y2 = true) :
    signSqrtGt d (X1 + X2) (Y1 + Y2) = true := by
  rw [Int.add_comm X1 X2, Int.add_comm Y1 Y2]
  exact signSqrtGt_add_ge hd h2 h1

theorem signSqrtGt_add {d : Nat} (hd : 0 < d) {X1 Y1 X2 Y2 : Int}
    (h1 : signSqrtGt d X1 Y1 = true) (h2 : signSqrtGt d X2 Y2 = true) :
    signSqrtGt d (X1 + X2) (Y1 + Y2) = true :=
  signSqrtGt_add_ge hd h1 (signSqrtGt_imp_ge h2)

theorem signSqrtGt_scale_pos {d : Nat} {k X Y : Int}
    (hk : 0 < k) (h : signSqrtGt d X Y = true) :
    signSqrtGt d (k * X) (k * Y) = true := by
  rw [signSqrtGt_iff] at h ⊢
  have hk2 : 0 < k * k := Int.mul_pos hk hk
  rcases h with ⟨rfl, hx⟩ | ⟨hy, hx, hsq⟩ | ⟨hy, hx | hsq⟩
  · left; exact ⟨by simp, Int.mul_pos hk hx⟩
  · right; left
    refine ⟨Int.mul_pos hk hy, Int.mul_pos hk hx, ?_⟩
    have e1 : (d : Int) * ((k * Y) * (k * Y)) = (k * k) * ((d : Int) * (Y * Y)) := by grind
    have e2 : (k * X) * (k * X) = (k * k) * (X * X) := by grind
    have m := Int.mul_lt_mul_of_pos_left hsq hk2
    omega
  · right; right
    exact ⟨Int.mul_neg_of_pos_of_neg hk hy, Or.inl (Int.mul_nonneg (by omega) hx)⟩
  · right; right
    refine ⟨Int.mul_neg_of_pos_of_neg hk hy, Or.inr ?_⟩
    have e1 : (k * X) * (k * X) = (k * k) * (X * X) := by grind
    have e2 : (d : Int) * ((k * Y) * (k * Y)) = (k * k) * ((d : Int) * (Y * Y)) := by grind
    have m := Int.mul_lt_mul_of_pos_left hsq hk2
    omega

theorem signSqrtGt_scale_unscale {d : Nat} {k X Y : Int}
    (hk : 0 < k) (h : signSqrtGt d (k * X) (k * Y) = true) :
    signSqrtGt d X Y = true := by
  rw [signSqrtGt_iff] at h ⊢
  have hk2 : 0 < k * k := Int.mul_pos hk hk
  have pos_of_mul_pos : ∀ {z : Int}, 0 < k * z → 0 < z := fun hz =>
    sq_cancel_pos_lt hk (by simp; exact hz)
  have nonneg_of_mul_nonneg : ∀ {z : Int}, 0 ≤ k * z → 0 ≤ z := fun hz =>
    sq_cancel_pos hk (by simp; exact hz)
  have neg_of_mul_neg : ∀ {z : Int}, k * z < 0 → z < 0 := by
    intro z hz
    have : 0 < k * (-z) := by rw [Int.mul_neg]; omega
    have := pos_of_mul_pos this
    omega
  rcases h with ⟨hy0, hkx⟩ | ⟨hky, hkx, hsq⟩ | ⟨hky, hkx | hsq⟩
  · have hy : Y = 0 := by
      have h1 : 0 ≤ Y := nonneg_of_mul_nonneg (by omega)
      have h2 : 0 ≤ -Y := nonneg_of_mul_nonneg (by rw [Int.mul_neg]; omega)
      omega
    exact Or.inl ⟨hy, pos_of_mul_pos hkx⟩
  · right; left
    refine ⟨pos_of_mul_pos hky, pos_of_mul_pos hkx, ?_⟩
    have e1 : (d : Int) * ((k * Y) * (k * Y)) = (k * k) * ((d : Int) * (Y * Y)) := by grind
    have e2 : (k * X) * (k * X) = (k * k) * (X * X) := by grind
    rw [e1, e2] at hsq
    exact sq_cancel_pos_lt hk2 hsq
  · exact Or.inr (Or.inr ⟨neg_of_mul_neg hky, Or.inl (nonneg_of_mul_nonneg hkx)⟩)
  · right; right
    refine ⟨neg_of_mul_neg hky, Or.inr ?_⟩
    have e1 : (k * X) * (k * X) = (k * k) * (X * X) := by grind
    have e2 : (d : Int) * ((k * Y) * (k * Y)) = (k * k) * ((d : Int) * (Y * Y)) := by grind
    rw [e1, e2] at hsq
    exact sq_cancel_pos_lt hk2 hsq

/-- Positive scalar cancellation: if `k * (X - Y√d) > 0` and `X - Y√d > 0`, then `k > 0`. -/
theorem signSqrtGt_pos_of_scale {d : Nat} (hd : 0 < d) {k X Y : Int}
    (hxy : signSqrtGt d X Y = true) (hkxy : signSqrtGt d (k * X) (k * Y) = true) :
    0 < k := by
  by_cases hkp : 0 < k
  · exact hkp
  · exfalso
    by_cases hk0 : k = 0
    · subst hk0
      rw [Int.zero_mul, Int.zero_mul, signSqrtGt_iff] at hkxy
      rcases hkxy with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · have hm : 0 < -k := by omega
      have hpos := signSqrtGt_scale_pos hm hxy
      have e1 : -(k * X) = (-k) * X := by rw [Int.neg_mul]
      have e2 : -(k * Y) = (-k) * Y := by rw [Int.neg_mul]
      rw [← e1, ← e2] at hpos
      exact signSqrtGt_not_neg hd hkxy (signSqrtGt_imp_ge hpos)

/-- Brahmagupta's identity: `(A*X + d*B*Y)^2 - d*(A*Y + B*X)^2 = (A^2 - d*B^2)*(X^2 - d*Y^2)`. -/
theorem brahmagupta (d A B X Y : Int) :
    (A * X + d * B * Y) * (A * X + d * B * Y) - d * ((A * Y + B * X) * (A * Y + B * X)) =
    (A * A - d * (B * B)) * (X * X - d * (Y * Y)) := by
  grind

/-- Product of two strictly positive elements of `ℤ[√d]` is strictly positive! -/
theorem signSqrtGt_mul {d : Nat} (hd : 0 < d) {A B X Y : Int}
    (h1 : signSqrtGt d A B = true) (h2 : signSqrtGt d X Y = true) :
    signSqrtGt d (A * X + (d : Int) * B * Y) (A * Y + B * X) = true := by
  have hdI : (0 : Int) < (d : Int) := by omega
  have hB := brahmagupta (d : Int) A B X Y
  rw [signSqrtGt_iff] at h1 h2 ⊢
  have case_pos_pos : ∀ {a b x y : Int},
      0 < a → 0 ≤ b → (d : Int) * (b * b) < a * a →
      0 < x → 0 ≤ y → (d : Int) * (y * y) < x * x →
      (a * y + b * x = 0 ∧ 0 < a * x + (d : Int) * b * y) ∨
      (0 < a * y + b * x ∧ 0 < a * x + (d : Int) * b * y ∧
       (d : Int) * ((a * y + b * x) * (a * y + b * x)) < (a * x + (d : Int) * b * y) * (a * x + (d : Int) * b * y)) := by
    intro a b x y ha hb hn1 hx hy hn2
    have hP : 0 < a * x + (d : Int) * b * y := by
      have m1 : 0 < a * x := Int.mul_pos ha hx
      have m2 : 0 ≤ (d : Int) * b * y := Int.mul_nonneg (Int.mul_nonneg (by omega) hb) hy
      omega
    have hQ : 0 ≤ a * y + b * x := by
      have m1 : 0 ≤ a * y := Int.mul_nonneg (by omega) hy
      have m2 : 0 ≤ b * x := Int.mul_nonneg hb (by omega)
      omega
    by_cases hq0 : a * y + b * x = 0
    · exact Or.inl ⟨hq0, hP⟩
    · right
      have hbr := brahmagupta (d : Int) a b x y
      have hprod : 0 < (a * a - (d : Int) * (b * b)) * (x * x - (d : Int) * (y * y)) :=
        Int.mul_pos (by omega) (by omega)
      exact ⟨by omega, hP, by omega⟩
  have case_pos_neg : ∀ {a b x y : Int},
      0 < a → 0 ≤ b → (d : Int) * (b * b) < a * a →
      y < 0 → (0 ≤ x ∨ x * x < (d : Int) * (y * y)) →
      (a * y + b * x = 0 ∧ 0 < a * x + (d : Int) * b * y) ∨
      (0 < a * y + b * x ∧ 0 < a * x + (d : Int) * b * y ∧
       (d : Int) * ((a * y + b * x) * (a * y + b * x)) < (a * x + (d : Int) * b * y) * (a * x + (d : Int) * b * y)) ∨
      (a * y + b * x < 0 ∧ (0 ≤ a * x + (d : Int) * b * y ∨
       (a * x + (d : Int) * b * y) * (a * x + (d : Int) * b * y) < (d : Int) * ((a * y + b * x) * (a * y + b * x)))) := by
    intro a b x y ha hb hn1 hy hxc
    have hbr := brahmagupta (d : Int) a b x y
    rcases hxc with hx | hsqx
    · by_cases hqp : 0 < a * y + b * x
      · have hbpos : 0 < b := by
          by_cases hbp : 0 < b
          · exact hbp
          · have hb0 : b = 0 := by omega
            subst hb0; simp at hqp
            have : a * y < 0 := Int.mul_neg_of_pos_of_neg ha hy
            omega
        have hbx : a * (-y) < b * x := by
          have : a * (-y) = -(a * y) := Int.mul_neg a y
          omega
        have hN2 : (d : Int) * (y * y) < x * x := by
          have hsq : (a * (-y)) * (a * (-y)) < (b * x) * (b * x) :=
            mul_lt_mul_pos (Int.mul_nonneg (by omega) (by omega)) (Int.mul_nonneg (by omega) (by omega)) hbx hbx
          have e1 : (a * (-y)) * (a * (-y)) = (a * a) * (y * y) := by grind
          have e2 : (b * x) * (b * x) = (b * b) * (x * x) := by grind
          have m1 : ((d : Int) * (b * b)) * (y * y) < (a * a) * (y * y) :=
            Int.mul_lt_mul_of_pos_right hn1 (sq_pos_of_ne_zero (by omega))
          have eqm : (b * b) * ((d : Int) * (y * y)) = ((d : Int) * (b * b)) * (y * y) := by grind
          have h6 : (b * b) * ((d : Int) * (y * y)) < (b * b) * (x * x) := by omega
          exact sq_cancel_pos_lt (sq_pos_of_ne_zero (by omega : b ≠ 0)) h6
        have hP : 0 < a * x + (d : Int) * b * y := by
          have hlt : (d : Int) * b * (-y) < a * x := by
            apply lt_of_sq_lt_sq (Int.mul_nonneg (by omega) hx)
            have e1 : ((d : Int) * b * (-y)) * ((d : Int) * b * (-y)) = ((d : Int) * (b * b)) * ((d : Int) * (y * y)) := by grind
            have e2 : (a * x) * (a * x) = (a * a) * (x * x) := by grind
            have m := mul_lt_mul_pos (Int.mul_nonneg (by omega) (sq_nonneg b)) (Int.mul_nonneg (by omega) (sq_nonneg y)) hn1 hN2
            omega
          have e3 : (d : Int) * b * (-y) = -((d : Int) * b * y) := Int.mul_neg ((d : Int) * b) y
          omega
        have hprod : 0 < (a * a - (d : Int) * (b * b)) * (x * x - (d : Int) * (y * y)) :=
          Int.mul_pos (by omega) (by omega)
        exact Or.inr (Or.inl ⟨hqp, hP, by omega⟩)
      · by_cases hq0 : a * y + b * x = 0
        · have hbx : a * (-y) = b * x := by
            have : a * (-y) = -(a * y) := Int.mul_neg a y
            omega
          have hP : 0 < a * x + (d : Int) * b * y := by
            have h1 : a * (a * x + (d : Int) * b * y) = a * a * x - (d : Int) * b * (a * (-y)) := by grind
            rw [hbx] at h1
            have h2 : a * a * x - (d : Int) * b * (b * x) = (a * a - (d : Int) * (b * b)) * x := by grind
            have hxpos : 0 < x := by
              by_cases hxp : 0 < x
              · exact hxp
              · have hx0 : x = 0 := by omega
                subst hx0; simp at hbx
                have : 0 < a * (-y) := Int.mul_pos ha (by omega)
                omega
            have hpos : 0 < (a * a - (d : Int) * (b * b)) * x := Int.mul_pos (by omega) hxpos
            exact sq_cancel_pos_lt ha (by omega)
          exact Or.inl ⟨hq0, hP⟩
        · right; right
          refine ⟨by omega, ?_⟩
          by_cases hpp : 0 ≤ a * x + (d : Int) * b * y
          · exact Or.inl hpp
          · right
            have hN2 : x * x < (d : Int) * (y * y) := by
              by_cases hltN : x * x < (d : Int) * (y * y)
              · exact hltN
              · have hlt : (d : Int) * b * (-y) < a * x := by
                  apply lt_of_sq_lt_sq (Int.mul_nonneg (by omega) hx)
                  have e1 : ((d : Int) * b * (-y)) * ((d : Int) * b * (-y)) = ((d : Int) * (b * b)) * ((d : Int) * (y * y)) := by grind
                  have e2 : (a * x) * (a * x) = (a * a) * (x * x) := by grind
                  have m1 : ((d : Int) * (b * b)) * ((d : Int) * (y * y)) < (a * a) * ((d : Int) * (y * y)) :=
                    Int.mul_lt_mul_of_pos_right hn1 (Int.mul_pos hdI (sq_pos_of_ne_zero (by omega)))
                  have m2 : (a * a) * ((d : Int) * (y * y)) ≤ (a * a) * (x * x) :=
                    Int.mul_le_mul_of_nonneg_left (by omega) (sq_nonneg a)
                  omega
                have e3 : (d : Int) * b * (-y) = -((d : Int) * b * y) := Int.mul_neg ((d : Int) * b) y
                omega
            have hprod : (a * a - (d : Int) * (b * b)) * (x * x - (d : Int) * (y * y)) < 0 :=
              Int.mul_neg_of_pos_of_neg (by omega) (by omega)
            omega
    · have hQneg : a * y + b * x < 0 := by
        by_cases hxp : 0 ≤ x
        · have hlt : b * x < a * (-y) := by
            apply lt_of_sq_lt_sq (Int.mul_nonneg (by omega) (by omega))
            have e1 : (b * x) * (b * x) = (b * b) * (x * x) := by grind
            have e2 : (a * (-y)) * (a * (-y)) = (a * a) * (y * y) := by grind
            have m1 : (d : Int) * ((b * b) * (x * x)) ≤ (d : Int) * ((b * b) * ((d : Int) * (y * y))) :=
              Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left (by omega) (sq_nonneg b)) (by omega)
            have m2 : ((d : Int) * (b * b)) * ((d : Int) * (y * y)) < (a * a) * ((d : Int) * (y * y)) :=
              Int.mul_lt_mul_of_pos_right hn1 (Int.mul_pos hdI (sq_pos_of_ne_zero (by omega)))
            have eq1 : (d : Int) * ((b * b) * ((d : Int) * (y * y))) = ((d : Int) * (b * b)) * ((d : Int) * (y * y)) := by grind
            have eq2 : (a * a) * ((d : Int) * (y * y)) = (d : Int) * ((a * a) * (y * y)) := by grind
            have m4 := sq_cancel_pos_lt hdI (by omega : (d : Int) * ((b * b) * (x * x)) < (d : Int) * ((a * a) * (y * y)))
            omega
          have e3 : a * (-y) = -(a * y) := Int.mul_neg a y
          omega
        · have m1 : a * y < 0 := Int.mul_neg_of_pos_of_neg ha hy
          have m2 : b * x ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hb (by omega)
          omega
      have hprod : (a * a - (d : Int) * (b * b)) * (x * x - (d : Int) * (y * y)) < 0 :=
        Int.mul_neg_of_pos_of_neg (by omega) (by omega)
      exact Or.inr (Or.inr ⟨hQneg, Or.inr (by omega)⟩)
  have case_neg_ge_lt : ∀ {a b x y : Int},
      b < 0 → 0 ≤ a → y < 0 → x < 0 → x * x < (d : Int) * (y * y) →
      (a * y + b * x = 0 ∧ 0 < a * x + (d : Int) * b * y) ∨
      (0 < a * y + b * x ∧ 0 < a * x + (d : Int) * b * y ∧
       (d : Int) * ((a * y + b * x) * (a * y + b * x)) < (a * x + (d : Int) * b * y) * (a * x + (d : Int) * b * y)) ∨
      (a * y + b * x < 0 ∧ (0 ≤ a * x + (d : Int) * b * y ∨
       (a * x + (d : Int) * b * y) * (a * x + (d : Int) * b * y) < (d : Int) * ((a * y + b * x) * (a * y + b * x)))) := by
    intro a b x y hb ha0 hy hx0 hsqX
    have hbr := brahmagupta (d : Int) a b x y
    by_cases hN1 : a * a < (d : Int) * (b * b)
    · have hP : 0 < a * x + (d : Int) * b * y := by
        have hlt : a * (-x) < (d : Int) * ((-b) * (-y)) := by
          apply lt_of_sq_lt_sq (Int.mul_nonneg (by omega) (Int.mul_nonneg (by omega) (by omega)))
          have e1 : (a * (-x)) * (a * (-x)) = (a * a) * (x * x) := by grind
          have e2 : ((d : Int) * ((-b) * (-y))) * ((d : Int) * ((-b) * (-y))) =
              ((d : Int) * (b * b)) * ((d : Int) * (y * y)) := by grind
          have m := mul_lt_mul_pos (sq_nonneg a) (sq_nonneg x) hN1 hsqX
          omega
        have e3 : a * (-x) = -(a * x) := Int.mul_neg a x
        have e4 : (d : Int) * ((-b) * (-y)) = (d : Int) * b * y := by grind
        omega
      have hprod : 0 < (a * a - (d : Int) * (b * b)) * (x * x - (d : Int) * (y * y)) :=
        Int.mul_pos_of_neg_of_neg (by omega) (by omega)
      by_cases hq0 : a * y + b * x = 0
      · exact Or.inl ⟨hq0, hP⟩
      · by_cases hqp : 0 < a * y + b * x
        · exact Or.inr (Or.inl ⟨hqp, hP, by omega⟩)
        · exact Or.inr (Or.inr ⟨by omega, Or.inl (by omega)⟩)
    · have hQ : a * y + b * x < 0 := by
        have hlt : (-b) * (-x) < a * (-y) := by
          apply lt_of_sq_lt_sq (Int.mul_nonneg ha0 (by omega))
          have e1 : ((-b) * (-x)) * ((-b) * (-x)) = (b * b) * (x * x) := by grind
          have e2 : (a * (-y)) * (a * (-y)) = (a * a) * (y * y) := by grind
          have m1 : (d : Int) * ((b * b) * (x * x)) < (d : Int) * ((b * b) * ((d : Int) * (y * y))) :=
            Int.mul_lt_mul_of_pos_left (Int.mul_lt_mul_of_pos_left hsqX (sq_pos_of_ne_zero (by omega))) hdI
          have m2 : ((d : Int) * (b * b)) * ((d : Int) * (y * y)) ≤ (a * a) * ((d : Int) * (y * y)) :=
            Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg (by omega) (sq_nonneg y))
          have eq1 : (d : Int) * ((b * b) * ((d : Int) * (y * y))) = ((d : Int) * (b * b)) * ((d : Int) * (y * y)) := by grind
          have eq2 : (a * a) * ((d : Int) * (y * y)) = (d : Int) * ((a * a) * (y * y)) := by grind
          have m3 := sq_cancel_pos_lt hdI (by omega : (d : Int) * ((b * b) * (x * x)) < (d : Int) * ((a * a) * (y * y)))
          omega
        have e3 : (-b) * (-x) = b * x := by grind
        have e4 : a * (-y) = -(a * y) := Int.mul_neg a y
        omega
      by_cases hN1eq : a * a = (d : Int) * (b * b)
      · have hP : 0 < a * x + (d : Int) * b * y := by
          have hlt : a * (-x) < (d : Int) * ((-b) * (-y)) := by
            apply lt_of_sq_lt_sq (Int.mul_nonneg (by omega) (Int.mul_nonneg (by omega) (by omega)))
            have e1 : (a * (-x)) * (a * (-x)) = (a * a) * (x * x) := by grind
            have e2 : ((d : Int) * ((-b) * (-y))) * ((d : Int) * ((-b) * (-y))) =
                ((d : Int) * (b * b)) * ((d : Int) * (y * y)) := by grind
            have hAp : 0 < a * a := by
              have : 0 < (d : Int) * (b * b) := Int.mul_pos hdI (sq_pos_of_ne_zero (by omega))
              omega
            have m := Int.mul_lt_mul_of_pos_left hsqX hAp
            rw [hN1eq] at e1 m; omega
          have e3 : a * (-x) = -(a * x) := Int.mul_neg a x
          have e4 : (d : Int) * ((-b) * (-y)) = (d : Int) * b * y := by grind
          omega
        exact Or.inr (Or.inr ⟨hQ, Or.inl (by omega)⟩)
      · have hprod : (a * a - (d : Int) * (b * b)) * (x * x - (d : Int) * (y * y)) < 0 :=
          Int.mul_neg_of_pos_of_neg (by omega) (by omega)
        exact Or.inr (Or.inr ⟨hQ, Or.inr (by omega)⟩)
  have sym : ∀ {a b x y : Int},
      a * x + (d : Int) * b * y = x * a + (d : Int) * y * b ∧
      a * y + b * x = x * b + y * a := fun {_ _ _ _} => ⟨by grind, by grind⟩
  rcases h1 with ⟨rfl, ha⟩ | ⟨hb, ha, hn1⟩ | ⟨hb, ha_c⟩
  · have hn0 : (d : Int) * (0 * 0) < A * A := by simp; exact sq_pos_of_ne_zero (by omega)
    rcases h2 with ⟨rfl, hx⟩ | ⟨hy, hx, hn2⟩ | ⟨hy, hxc⟩
    · rcases case_pos_pos ha (Int.le_refl 0) hn0 hx (Int.le_refl 0) (by simp; exact sq_pos_of_ne_zero (by omega)) with h | h
      exact Or.inl h; exact Or.inr (Or.inl h)
    · rcases case_pos_pos ha (Int.le_refl 0) hn0 hx (by omega) hn2 with h | h
      exact Or.inl h; exact Or.inr (Or.inl h)
    · exact case_pos_neg ha (Int.le_refl 0) hn0 hy hxc
  · rcases h2 with ⟨rfl, hx⟩ | ⟨hy, hx, hn2⟩ | ⟨hy, hxc⟩
    · rcases case_pos_pos ha (by omega) hn1 hx (Int.le_refl 0) (by simp; exact sq_pos_of_ne_zero (by omega)) with h | h
      exact Or.inl h; exact Or.inr (Or.inl h)
    · rcases case_pos_pos ha (by omega) hn1 hx (by omega) hn2 with h | h
      exact Or.inl h; exact Or.inr (Or.inl h)
    · exact case_pos_neg ha (by omega) hn1 hy hxc
  · rcases h2 with ⟨rfl, hx⟩ | ⟨hy, hx, hn2⟩ | ⟨hy, hxc⟩
    · have hn0 : (d : Int) * (0 * 0) < X * X := by simp; exact sq_pos_of_ne_zero (by omega)
      rw [(sym (a := A) (b := B) (x := X) (y := 0)).1, (sym (a := A) (b := B) (x := X) (y := 0)).2]
      exact case_pos_neg hx (Int.le_refl 0) hn0 hb ha_c
    · rw [(sym (a := A) (b := B) (x := X) (y := Y)).1, (sym (a := A) (b := B) (x := X) (y := Y)).2]
      exact case_pos_neg hx (by omega) hn2 hb ha_c
    · by_cases ha0 : 0 ≤ A
      · by_cases hx0 : 0 ≤ X
        · have hP : 0 < A * X + (d : Int) * B * Y := by
            have m1 : 0 ≤ A * X := Int.mul_nonneg ha0 hx0
            have m2 : 0 < (d : Int) * ((-B) * (-Y)) := Int.mul_pos hdI (Int.mul_pos (by omega) (by omega))
            have e : (d : Int) * B * Y = (d : Int) * ((-B) * (-Y)) := by grind
            omega
          have hQ : A * Y + B * X ≤ 0 := by
            have m1 : A * Y ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos ha0 (by omega)
            have m2 : B * X ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hx0
            omega
          by_cases hq0 : A * Y + B * X = 0
          · exact Or.inl ⟨hq0, hP⟩
          · exact Or.inr (Or.inr ⟨by omega, Or.inl (by omega)⟩)
        · have hsqX : X * X < (d : Int) * (Y * Y) := by rcases hxc with h | h; omega; exact h
          exact case_neg_ge_lt hb ha0 hy (by omega) hsqX
      · have hsqA : A * A < (d : Int) * (B * B) := by rcases ha_c with h | h; omega; exact h
        by_cases hx0 : 0 ≤ X
        · rw [(sym (a := A) (b := B) (x := X) (y := Y)).1, (sym (a := A) (b := B) (x := X) (y := Y)).2]
          exact case_neg_ge_lt hy hx0 hb (by omega) hsqA
        · have hsqX : X * X < (d : Int) * (Y * Y) := by rcases hxc with h | h; omega; exact h
          have hP : 0 < A * X + (d : Int) * B * Y := by
            have m1 : 0 < A * X := Int.mul_pos_of_neg_of_neg (by omega) (by omega)
            have m2 : 0 < (d : Int) * ((-B) * (-Y)) := Int.mul_pos hdI (Int.mul_pos (by omega) (by omega))
            have e : (d : Int) * B * Y = (d : Int) * ((-B) * (-Y)) := by grind
            omega
          have hQ : 0 < A * Y + B * X := by
            have m1 : 0 < A * Y := Int.mul_pos_of_neg_of_neg (by omega) hy
            have m2 : 0 < B * X := Int.mul_pos_of_neg_of_neg hb (by omega)
            omega
          have hprod : 0 < (A * A - (d : Int) * (B * B)) * (X * X - (d : Int) * (Y * Y)) :=
            Int.mul_pos_of_neg_of_neg (by omega) (by omega)
          exact Or.inr (Or.inl ⟨hQ, hP, by omega⟩)

/-! ### Lifted `QElem` order laws -/

theorem qLt_trans_le {tr : Int} {d : Nat} (hd : 0 < d) {x y z : QElem}
    (h1 : qLt tr d x y = true) (h2 : qLe tr d y z = true) : qLt tr d x z = true := by
  simp only [qLt, qLe, qPos, qNonneg, qToXY, qSub] at h1 h2 ⊢
  have h := signSqrtGt_add_ge hd h1 h2
  have e1 : 2 * (y.1 - x.1) + tr * (y.2 - x.2) + (2 * (z.1 - y.1) + tr * (z.2 - y.2)) =
            2 * (z.1 - x.1) + tr * (z.2 - x.2) := by grind
  have e2 : (y.2 - x.2) + (z.2 - y.2) = z.2 - x.2 := by omega
  rw [e1, e2] at h; exact h

theorem qLe_trans_lt {tr : Int} {d : Nat} (hd : 0 < d) {x y z : QElem}
    (h1 : qLe tr d x y = true) (h2 : qLt tr d y z = true) : qLt tr d x z = true := by
  simp only [qLt, qLe, qPos, qNonneg, qToXY, qSub] at h1 h2 ⊢
  have h := signSqrtGe_add_gt hd h1 h2
  have e1 : 2 * (y.1 - x.1) + tr * (y.2 - x.2) + (2 * (z.1 - y.1) + tr * (z.2 - y.2)) =
            2 * (z.1 - x.1) + tr * (z.2 - x.2) := by grind
  have e2 : (y.2 - x.2) + (z.2 - y.2) = z.2 - x.2 := by omega
  rw [e1, e2] at h; exact h

theorem qLt_trans {tr : Int} {d : Nat} (hd : 0 < d) {x y z : QElem}
    (h1 : qLt tr d x y = true) (h2 : qLt tr d y z = true) : qLt tr d x z = true :=
  qLt_trans_le hd h1 (signSqrtGt_imp_ge h2)

theorem qLt_add_right {tr : Int} {d : Nat} {x y c : QElem}
    (h : qLt tr d x y = true) : qLt tr d (qAdd x c) (qAdd y c) = true := by
  simp only [qLt, qPos, qToXY, qSub, qAdd] at h ⊢
  have e1 : (y.1 + c.1) - (x.1 + c.1) = y.1 - x.1 := by omega
  have e2 : (y.2 + c.2) - (x.2 + c.2) = y.2 - x.2 := by omega
  rw [e1, e2]; exact h

theorem qLt_add_both {tr : Int} {d : Nat} (hd : 0 < d) {x1 y1 x2 y2 : QElem}
    (h1 : qLt tr d x1 y1 = true) (h2 : qLt tr d x2 y2 = true) :
    qLt tr d (qAdd x1 x2) (qAdd y1 y2) = true := by
  simp only [qLt, qPos, qToXY, qSub, qAdd] at h1 h2 ⊢
  have h := signSqrtGt_add hd h1 h2
  have e1 : 2 * (y1.1 - x1.1) + tr * (y1.2 - x1.2) + (2 * (y2.1 - x2.1) + tr * (y2.2 - x2.2)) =
            2 * (y1.1 + y2.1 - (x1.1 + x2.1)) + tr * (y1.2 + y2.2 - (x1.2 + x2.2)) := by grind
  have e2 : (y1.2 - x1.2) + (y2.2 - x2.2) = y1.2 + y2.2 - (x1.2 + x2.2) := by omega
  rw [e1, e2] at h; exact h

theorem qLt_sub_of_lt {tr : Int} {d : Nat} (hd : 0 < d) {a b c e : QElem}
    (h1 : qLt tr d a b = true) (h2 : qLt tr d c e = true) :
    qLt tr d (qSub a e) (qSub b c) = true := by
  simp only [qLt, qPos, qToXY, qSub] at h1 h2 ⊢
  have h := signSqrtGt_add hd h1 h2
  have e1 : 2 * (b.1 - a.1) + tr * (b.2 - a.2) + (2 * (e.1 - c.1) + tr * (e.2 - c.2)) =
            2 * (b.1 - c.1 - (a.1 - e.1)) + tr * (b.2 - c.2 - (a.2 - e.2)) := by grind
  have e2 : (b.2 - a.2) + (e.2 - c.2) = b.2 - c.2 - (a.2 - e.2) := by omega
  rw [e1, e2] at h; exact h

/-- Exact monotonicity of `qMulLam2` when `λ₂ > 0`. -/
theorem qMulLam2_lt_of_pos {tr det : Int} {d : Nat}
    (hd : 0 < d) (hdisc : (d : Int) = tr * tr - 4 * det)
    (hlam : qPos tr d (0, 1) = true) {x y : QElem} (hxy : qLt tr d x y = true) :
    qLt tr d (qMulLam2 tr det x) (qMulLam2 tr det y) = true := by
  simp only [qPos, qToXY, Int.mul_zero, Int.zero_add, Int.mul_one] at hlam
  simp only [qLt, qPos, qToXY, qSub, qMulLam2] at hxy ⊢
  have hm := signSqrtGt_mul hd hlam hxy
  have eX : tr * (2 * (y.1 - x.1) + tr * (y.2 - x.2)) + (d : Int) * 1 * (y.2 - x.2) =
            2 * (2 * (-det * y.2 - -det * x.2) + tr * (y.1 + tr * y.2 - (x.1 + tr * x.2))) := by grind
  have eY : tr * (y.2 - x.2) + 1 * (2 * (y.1 - x.1) + tr * (y.2 - x.2)) =
            2 * (y.1 + tr * y.2 - (x.1 + tr * x.2)) := by grind
  rw [eX, eY] at hm
  exact signSqrtGt_scale_unscale (by omega : (0 : Int) < 2) hm

/-- Exact order-reversal of `qMulLam2` when `λ₂ < 0`. -/
theorem qMulLam2_lt_of_neg {tr det : Int} {d : Nat}
    (hd : 0 < d) (hdisc : (d : Int) = tr * tr - 4 * det)
    (hlam : qPos tr d (0, -1) = true) {x y : QElem} (hxy : qLt tr d x y = true) :
    qLt tr d (qMulLam2 tr det y) (qMulLam2 tr det x) = true := by
  simp only [qPos, qToXY, Int.mul_zero, Int.zero_add, Int.mul_neg, Int.mul_one] at hlam
  simp only [qLt, qPos, qToXY, qSub, qMulLam2] at hxy ⊢
  have hm := signSqrtGt_mul hd hlam hxy
  have eX : (-tr) * (2 * (y.1 - x.1) + tr * (y.2 - x.2)) + (d : Int) * (-1) * (y.2 - x.2) =
            2 * (2 * (-det * x.2 - -det * y.2) + tr * (x.1 + tr * x.2 - (y.1 + tr * y.2))) := by grind
  have eY : (-tr) * (y.2 - x.2) + (-1) * (2 * (y.1 - x.1) + tr * (y.2 - x.2)) =
            2 * (x.1 + tr * x.2 - (y.1 + tr * y.2)) := by grind
  rw [eX, eY] at hm
  exact signSqrtGt_scale_unscale (by omega : (0 : Int) < 2) hm

/-- Integer scalar bound cancellation in `ℤ[λ₂]`:
    if `k * Λ < B * Λ` and `0 < Λ`, then `k < B`. -/
theorem qScale_lt_cancel {tr : Int} {d : Nat} (hd : 0 < d) {k B : Int} {L : QElem}
    (hL : qPos tr d L = true) (h : qLt tr d (qScale k L) (qScale B L) = true) : k < B := by
  simp only [qPos, qToXY] at hL
  simp only [qLt, qPos, qToXY, qSub, qScale] at h
  have e1 : 2 * (B * L.1 - k * L.1) + tr * (B * L.2 - k * L.2) = (B - k) * (2 * L.1 + tr * L.2) := by grind
  have e2 : B * L.2 - k * L.2 = (B - k) * L.2 := by grind
  rw [e1, e2] at h
  have hpos := signSqrtGt_pos_of_scale hd hL h
  omega

/-! =========================================================================
    SECTION 2: Binary Morphisms, Infinite Fixed Points, & Dumont–Thomas Oracle
    ========================================================================= -/

theorem countZeros_append (u v : List Bool) :
    countZeros (u ++ v) = countZeros u + countZeros v := by
  induction u with
  | nil => simp [countZeros]
  | cons b t ih => cases b <;> simp [countZeros, ih] <;> omega

theorem countOnes_append (u v : List Bool) :
    countOnes (u ++ v) = countOnes u + countOnes v := by
  induction u with
  | nil => simp [countOnes]
  | cons b t ih => cases b <;> simp [countOnes, ih] <;> omega

theorem countZeros_add_countOnes (w : List Bool) :
    countZeros w + countOnes w = w.length := by
  induction w with
  | nil => rfl
  | cons b t ih => cases b <;> simp [countZeros, countOnes] <;> omega

namespace Morphism

theorem applyWord_nil (m : Morphism) : m.applyWord [] = [] := rfl

theorem applyWord_cons (m : Morphism) (b : Bool) (t : List Bool) :
    m.applyWord (b :: t) = m.applyChar b ++ m.applyWord t := rfl

theorem applyWord_append (m : Morphism) (u v : List Bool) :
    m.applyWord (u ++ v) = m.applyWord u ++ m.applyWord v := by
  simp [applyWord, List.flatMap_append]

theorem discWord_nil (m : Morphism) : m.discWord [] = (0, 0) := by
  simp [discWord, countZeros, countOnes]

theorem discWord_append (m : Morphism) (u v : List Bool) :
    m.discWord (u ++ v) = qAdd (m.discWord u) (m.discWord v) := by
  simp only [discWord, qAdd, countZeros_append, countOnes_append, Int.natCast_add, Prod.mk.injEq]
  constructor <;> grind

/-- Unconditional algebraic eigenvalue identity: `D(σ(w)) = λ₂ · D(w)` in `ℤ[λ₂]`. -/
theorem discWord_applyWord (m : Morphism) (w : List Bool) :
    m.discWord (m.applyWord w) = qMulLam2 m.mTr m.mDet (m.discWord w) := by
  induction w with
  | nil => simp [applyWord, discWord, countZeros, countOnes, qMulLam2]
  | cons b t ih =>
    rw [applyWord_cons, discWord_append, ih]
    have hcons : m.discWord (b :: t) = qAdd (m.discWord [b]) (m.discWord t) := by
      have : b :: t = [b] ++ t := rfl
      rw [this, discWord_append]
    rw [hcons]
    have hmul_add : ∀ x y : QElem,
        qMulLam2 m.mTr m.mDet (qAdd x y) = qAdd (qMulLam2 m.mTr m.mDet x) (qMulLam2 m.mTr m.mDet y) := by
      intro x y; simp only [qMulLam2, qAdd, Prod.mk.injEq]; constructor <;> grind
    rw [hmul_add]
    have hchar : m.discWord (m.applyChar b) = qMulLam2 m.mTr m.mDet (m.discWord [b]) := by
      cases b
      · simp only [applyChar, Bool.false_eq_true, ↓reduceIte, discWord, qMulLam2, countZeros, countOnes,
                   mA, mB, mC, mD, mTr, mDet, Prod.mk.injEq]
        constructor <;> grind
      · simp only [applyChar, ↓reduceIte, discWord, qMulLam2, countZeros, countOnes,
                   mA, mB, mC, mD, mTr, mDet, Prod.mk.injEq]
        constructor <;> grind
    rw [hchar]

/-- Exact factor-difference identity: for `|u| = |v|`, `D(u) - D(v) = (#₁(u) - #₁(v)) · Λ`. -/
theorem discWord_factor_diff (m : Morphism) {u v : List Bool} (hlen : u.length = v.length) :
    qSub (m.discWord u) (m.discWord v) =
    qScale ((countOnes u : Int) - (countOnes v : Int)) m.mLambda := by
  have hu := countZeros_add_countOnes u
  have hv := countZeros_add_countOnes v
  have hz : (countZeros u : Int) - (countZeros v : Int) = -((countOnes u : Int) - (countOnes v : Int)) := by
    omega
  simp only [discWord, qSub, qScale, mLambda, Prod.mk.injEq]
  constructor <;> grind

theorem applyWord_length_mod (m : Morphism) {M : Nat}
    (h0 : m.w0.length % M = 0) (h1 : m.w1.length % M = 0) (w : List Bool) :
    (m.applyWord w).length % M = 0 := by
  induction w with
  | nil => simp [applyWord]
  | cons b t ih =>
    rw [applyWord_cons, List.length_append, Nat.add_mod, ih]
    cases b
    · simp [applyChar, h0]
    · simp [applyChar, h1]

/-! ### Constructive infinite fixed point `x = lim_{k→∞} σ^k(0)` -/

theorem iter_prefix_succ (m : Morphism) (hhead : m.w0.head? = some false) :
    ∀ k : Nat, ∃ s : List Bool, m.iter (k + 1) = m.iter k ++ s := by
  intro k
  induction k with
  | zero =>
    cases hw : m.w0 with
    | nil => simp [hw] at hhead
    | cons c rest =>
      simp [hw] at hhead; subst hhead
      exact ⟨rest, by simp [iter, applyWord, applyChar, hw]⟩
  | succ k ih =>
    rcases ih with ⟨s, hs⟩
    refine ⟨m.applyWord s, ?_⟩
    show m.applyWord (m.iter (k + 1)) = m.applyWord (m.iter k) ++ m.applyWord s
    rw [hs, applyWord_append]

theorem iter_prefix_le (m : Morphism) (hhead : m.w0.head? = some false) :
    ∀ {k k' : Nat}, k ≤ k' → ∃ s : List Bool, m.iter k' = m.iter k ++ s := by
  intro k k' hle
  induction hle with
  | refl => exact ⟨[], by simp⟩
  | @step m' _ ih =>
    rcases ih with ⟨s1, hs1⟩
    rcases iter_prefix_succ m hhead m' with ⟨s2, hs2⟩
    exact ⟨s1 ++ s2, by rw [hs2, hs1, List.append_assoc]⟩

theorem iter_head (m : Morphism) (hhead : m.w0.head? = some false) :
    ∀ k : Nat, ∃ rest : List Bool, m.iter k = false :: rest := by
  intro k
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    rcases ih with ⟨rest, hr⟩
    cases hw : m.w0 with
    | nil => simp [hw] at hhead
    | cons c r0 =>
      simp [hw] at hhead; subst hhead
      refine ⟨r0 ++ m.applyWord rest, ?_⟩
      show m.applyWord (m.iter k) = false :: (r0 ++ m.applyWord rest)
      rw [hr, applyWord_cons]
      simp [applyChar, hw]

theorem applyWord_length_ge (m : Morphism) (h0 : 1 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length) :
    ∀ u : List Bool, u.length ≤ (m.applyWord u).length := by
  intro u
  induction u with
  | nil => simp [applyWord]
  | cons b t ih =>
    rw [applyWord_cons, List.length_append, List.length_cons]
    cases b <;> simp [applyChar] <;> omega

theorem iter_length_ge (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length) :
    ∀ k : Nat, k + 1 ≤ (m.iter k).length := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rcases iter_head m hhead k with ⟨rest, hr⟩
    show k + 2 ≤ (m.applyWord (m.iter k)).length
    rw [hr, applyWord_cons, List.length_append]
    have hrest : rest.length ≤ (m.applyWord rest).length :=
      applyWord_length_ge m (by omega) h1 rest
    have hlen : (m.iter k).length = rest.length + 1 := by rw [hr]; simp
    simp [applyChar]
    omega

theorem take_append_of_le {α : Type} {u v : List α} {n : Nat} (h : n ≤ u.length) :
    (u ++ v).take n = u.take n := by
  rw [List.take_append_of_le_length h]

theorem wordPrefix_eq_iter_take (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length)
    {k n : Nat} (hkn : n ≤ (m.iter k).length) :
    (m.iter k).take n = m.wordPrefix n := by
  unfold wordPrefix
  by_cases hle : k ≤ n
  · rcases iter_prefix_le m hhead hle with ⟨s, hs⟩
    rw [hs, take_append_of_le hkn]
  · rcases iter_prefix_le m hhead (by omega : n ≤ k) with ⟨s, hs⟩
    have hnlen : n ≤ (m.iter n).length := by
      have := iter_length_ge m hhead h0 h1 n; omega
    rw [hs, take_append_of_le hnlen]

theorem wordPrefix_length (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length)
    (n : Nat) : (m.wordPrefix n).length = n := by
  unfold wordPrefix
  have := iter_length_ge m hhead h0 h1 n
  rw [List.length_take]; omega

theorem wordFactor_length (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length)
    (i n : Nat) : (m.wordFactor i n).length = n := by
  unfold wordFactor
  have := iter_length_ge m hhead h0 h1 (i + n)
  rw [List.length_take, List.length_drop]; omega

theorem list_take_add {α : Type} (l : List α) (i n : Nat) :
    l.take (i + n) = l.take i ++ (l.drop i).take n := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i' =>
      have : i' + 1 + n = (i' + n) + 1 := by omega
      rw [this]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [ih i']

theorem wordPrefix_add (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length)
    (i n : Nat) :
    m.wordPrefix (i + n) = m.wordPrefix i ++ m.wordFactor i n := by
  have hi : i ≤ (m.iter (i + n)).length := by
    have := iter_length_ge m hhead h0 h1 (i + n); omega
  have h1' : m.wordPrefix i = (m.iter (i + n)).take i :=
    (wordPrefix_eq_iter_take m hhead h0 h1 hi).symm
  rw [h1']
  unfold wordPrefix wordFactor
  exact list_take_add (m.iter (i + n)) i n

theorem discWord_wordFactor (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length)
    (i n : Nat) :
    m.discWord (m.wordFactor i n) =
    qSub (m.discWord (m.wordPrefix (i + n))) (m.discWord (m.wordPrefix i)) := by
  have h := wordPrefix_add m hhead h0 h1 i n
  have hd : m.discWord (m.wordPrefix (i + n)) =
            qAdd (m.discWord (m.wordPrefix i)) (m.discWord (m.wordFactor i n)) := by
    rw [h, discWord_append]
  rw [hd]
  cases m.discWord (m.wordPrefix i); cases m.discWord (m.wordFactor i n)
  simp only [qAdd, qSub, Prod.mk.injEq]; omega

/-- Key Prefix-Automaton Decomposition Lemma: every strict prefix `p` of `σ(u)` with next bit `c'`
    splits uniquely as `p = σ(w) ++ r` where `u = w ++ [c] ++ v` and `σ(c) = r ++ [c'] ++ t`. -/
theorem applyWord_split (m : Morphism) :
    ∀ (u p s : List Bool) (c' : Bool),
      m.applyWord u = p ++ [c'] ++ s →
      ∃ (w v r t : List Bool) (c : Bool),
        u = w ++ [c] ++ v ∧ m.applyChar c = r ++ [c'] ++ t ∧ p = m.applyWord w ++ r := by
  intro u
  induction u with
  | nil =>
    intro p s c' h
    simp [applyWord] at h
  | cons a tail ih =>
    intro p s c' h
    rw [applyWord_cons] at h
    by_cases hlt : p.length < (m.applyChar a).length
    · -- Split falls inside `m.applyChar a`
      have hlen_le : p.length + 1 ≤ (m.applyChar a).length := by omega
      have htake : (m.applyChar a).take p.length = p := by
        have ht := congrArg (List.take p.length) h
        rw [List.take_append_of_le_length (by omega), List.append_assoc,
            List.take_append_of_le_length (Nat.le_refl _), List.take_length] at ht
        exact ht
      have hdrop : (m.applyChar a).drop p.length = c' :: ((m.applyChar a).drop (p.length + 1)) := by
        have hd := congrArg (List.drop p.length) h
        rw [List.drop_append_of_le_length (by omega), List.append_assoc,
            List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append] at hd
        cases hda : (m.applyChar a).drop p.length with
        | nil =>
          have : ((m.applyChar a).drop p.length).length = 0 := by rw [hda]; rfl
          rw [List.length_drop] at this; omega
        | cons x xs =>
          rw [hda] at hd
          simp only [List.cons_append, List.cons.injEq] at hd
          have hxs : (m.applyChar a).drop (p.length + 1) = xs := by
            have := congrArg List.tail hda
            rw [List.tail_drop] at this
            simpa using this
          rw [hd.1, hxs]
      have hchar : m.applyChar a = p ++ [c'] ++ (m.applyChar a).drop (p.length + 1) := by
        have htd := (List.take_append_drop p.length (m.applyChar a)).symm
        rw [htake, hdrop] at htd
        simpa [List.append_assoc] using htd
      exact ⟨[], tail, p, (m.applyChar a).drop (p.length + 1), a, by simp, hchar, by simp [applyWord]⟩
    · -- Split falls after `m.applyChar a`, inside `m.applyWord tail`
      have hge : (m.applyChar a).length ≤ p.length := by omega
      have hpref : p.take (m.applyChar a).length = m.applyChar a := by
        have ht := congrArg (List.take (m.applyChar a).length) h
        rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length, List.append_assoc,
            List.take_append_of_le_length hge] at ht
        exact ht.symm
      have hrem : m.applyWord tail = p.drop (m.applyChar a).length ++ [c'] ++ s := by
        have hd := congrArg (List.drop (m.applyChar a).length) h
        rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append,
            List.append_assoc, List.drop_append_of_le_length hge] at hd
        simpa [List.append_assoc] using hd
      rcases ih (p.drop (m.applyChar a).length) s c' hrem with ⟨w, v, r, t, c, hu, hc, hp⟩
      refine ⟨a :: w, v, r, t, c, by simp [hu], hc, ?_⟩
      rw [applyWord_cons, List.append_assoc, ← hp]
      calc p = p.take (m.applyChar a).length ++ p.drop (m.applyChar a).length := (List.take_append_drop _ _).symm
           _ = m.applyChar a ++ p.drop (m.applyChar a).length := by rw [hpref]

/-! ### Verified `O(log n)` Dumont–Thomas Prefix-Weight Transducer -/

theorem iterChar_false_eq_iter (m : Morphism) (d : Nat) : m.iterChar d false = m.iter d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [iterChar, iter, ih]

theorem iterChar_succ_eq_flatMap (m : Morphism) (d : Nat) (b : Bool) :
    m.iterChar (d + 1) b = (m.applyChar b).flatMap (m.iterChar d) := by
  induction d with
  | zero =>
    simp [iterChar, applyWord]
  | succ d ih =>
    show m.applyWord (m.iterChar (d + 1) b) = (m.applyChar b).flatMap (fun x => m.applyWord (m.iterChar d x))
    rw [ih]
    have hfm : ∀ l : List Bool, m.applyWord (l.flatMap (m.iterChar d)) = l.flatMap (fun x => m.applyWord (m.iterChar d x)) := by
      intro l
      induction l with
      | nil => simp [applyWord]
      | cons x xs ihx => simp [List.flatMap_cons, applyWord_append, ihx]
    exact hfm (m.applyChar b)

theorem flatMap_length_stats (f : Bool → List Bool) (w : List Bool) :
    (w.flatMap f).length = countZeros w * (f false).length + countOnes w * (f true).length := by
  induction w with
  | nil => simp [countZeros, countOnes]
  | cons b t ih =>
    cases b <;> simp [countZeros, countOnes, ih] <;> grind

theorem flatMap_ones_stats (f : Bool → List Bool) (w : List Bool) :
    countOnes (w.flatMap f) = countZeros w * countOnes (f false) + countOnes w * countOnes (f true) := by
  induction w with
  | nil => simp [countZeros, countOnes]
  | cons b t ih =>
    cases b <;> simp [countZeros, countOnes, countOnes_append, ih] <;> grind

theorem dtStats_spec (m : Morphism) (d : Nat) :
    m.dtStats d = ((m.iterChar d false).length, (m.iterChar d true).length,
                   countOnes (m.iterChar d false), countOnes (m.iterChar d true)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [dtStats, ih, iterChar_succ_eq_flatMap, applyChar, Bool.false_eq_true, ↓reduceIte,
               flatMap_length_stats, flatMap_ones_stats]

theorem dtTakeOnes_spec (m : Morphism) (d : Nat) :
    ∀ (b : Bool) (pos : Nat), m.dtTakeOnes d b pos = countOnes ((m.iterChar d b).take pos) := by
  induction d with
  | zero =>
    intro b pos
    cases pos with
    | zero => simp [dtTakeOnes, iterChar, countOnes]
    | succ p => cases b <;> simp [dtTakeOnes, iterChar, countOnes]
  | succ d ih =>
    intro b pos
    simp only [dtTakeOnes, dtStats_spec, iterChar_succ_eq_flatMap]
    suffices ∀ (w : List Bool) (p : Nat),
        dtTakeOnesScan m d (m.iterChar d false).length (m.iterChar d true).length
          (countOnes (m.iterChar d false)) (countOnes (m.iterChar d true))
          (m.dtTakeOnes d) w p = countOnes ((w.flatMap (m.iterChar d)).take p) from
      this (m.applyChar b) pos
    intro w
    induction w with
    | nil => intro p; simp [dtTakeOnesScan, countOnes]
    | cons ch rest ihr =>
      intro p
      simp only [dtTakeOnesScan, List.flatMap_cons]
      have hl : (if ch then (m.iterChar d true).length else (m.iterChar d false).length) =
                (m.iterChar d ch).length := by cases ch <;> rfl
      have ho : (if ch then countOnes (m.iterChar d true) else countOnes (m.iterChar d false)) =
                countOnes (m.iterChar d ch) := by cases ch <;> rfl
      rw [hl, ho]
      by_cases hlt : p < (m.iterChar d ch).length
      · simp only [hlt, ↓reduceIte, ih ch p]
        rw [List.take_append_of_le_length (by omega : p ≤ (m.iterChar d ch).length)]
      · simp only [hlt, ↓reduceIte, ihr (p - (m.iterChar d ch).length)]
        rw [List.take_append, List.take_of_length_le (by omega : (m.iterChar d ch).length ≤ p), countOnes_append]

theorem dtTakeOnes_wordFactor (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length)
    {d i n : Nat} (hd : i + n ≤ (m.dtStats d).1) :
    countOnes (m.wordFactor i n) = m.dtTakeOnes d false (i + n) - m.dtTakeOnes d false i := by
  have hlen : i + n ≤ (m.iter d).length := by
    rw [dtStats_spec, iterChar_false_eq_iter] at hd; exact hd
  have h1' : m.dtTakeOnes d false (i + n) = countOnes (m.wordPrefix (i + n)) := by
    rw [dtTakeOnes_spec, iterChar_false_eq_iter, wordPrefix_eq_iter_take m hhead h0 h1 hlen]
  have h2' : m.dtTakeOnes d false i = countOnes (m.wordPrefix i) := by
    rw [dtTakeOnes_spec, iterChar_false_eq_iter, wordPrefix_eq_iter_take m hhead h0 h1 (by omega)]
  have hadd : countOnes (m.wordPrefix (i + n)) = countOnes (m.wordPrefix i) + countOnes (m.wordFactor i n) := by
    rw [wordPrefix_add m hhead h0 h1 i n, countOnes_append]
  omega

end Morphism

theorem mem_wordSplitsAux {pref w r t : List Bool} {c : Bool}
    (h : w = r ++ [c] ++ t) : (pref ++ r, c, t) ∈ wordSplitsAux pref w := by
  induction r generalizing pref w with
  | nil =>
    simp at h; subst h
    simp [wordSplitsAux]
  | cons a r' ih =>
    simp only [List.cons_append] at h
    subst h
    simp only [wordSplitsAux, List.mem_cons]
    right
    have := ih (pref := pref ++ [a]) (w := r' ++ [c] ++ t) (by simp [List.append_assoc])
    simpa [List.append_assoc] using this

theorem mem_wordSplits {w r t : List Bool} {c : Bool}
    (h : w = r ++ [c] ++ t) : (r, c, t) ∈ wordSplits w := by
  simpa [wordSplits] using mem_wordSplitsAux (pref := []) h

theorem qScale_mulLam2 (k tr det : Int) (x : QElem) :
    qScale k (qMulLam2 tr det x) = qMulLam2 tr det (qScale k x) := by
  simp only [qScale, qMulLam2, Prod.mk.injEq]; constructor <;> grind

theorem qScale_add (k : Int) (x y : QElem) :
    qScale k (qAdd x y) = qAdd (qScale k x) (qScale k y) := by
  simp only [qScale, qAdd, Prod.mk.injEq]; constructor <;> grind

theorem qScale_sub (k : Int) (x y : QElem) :
    qScale k (qSub x y) = qSub (qScale k x) (qScale k y) := by
  simp only [qScale, qSub, Prod.mk.injEq]; constructor <;> grind

theorem qScale_qScale (a b : Int) (x : QElem) :
    qScale a (qScale b x) = qScale (a * b) x := by
  simp only [qScale, Prod.mk.injEq]; constructor <;> grind

/-- Core induction lifting the finite 2-state prefix-automaton certificate to ALL morphism depths `k`. -/
theorem iter_prefix_invariant (m : Morphism) (cert : StratCert)
    (hd : 0 < m.mDisc) (hdisc : (m.mDisc : Int) = m.mTr * m.mTr - 4 * m.mDet)
    (hlam : qPos m.mTr m.mDisc (0, 1) = true ∨ qPos m.mTr m.mDisc (0, -1) = true)
    (hL0 : qLt m.mTr m.mDisc cert.L0 (0, 0) = true)
    (hU0 : qLt m.mTr m.mDisc (0, 0) cert.U0 = true)
    (htrans : checkAllTransitions m cert (qPos m.mTr m.mDisc (0, 1)) = true) :
    ∀ (k : Nat) (p s : List Bool) (c' : Bool),
      m.iter k = p ++ [c'] ++ s →
      qLt m.mTr m.mDisc (cert.loState c') (qScale (cert.D : Int) (m.discWord p)) = true ∧
      qLt m.mTr m.mDisc (qScale (cert.D : Int) (m.discWord p)) (cert.hiState c') = true := by
  intro k
  induction k with
  | zero =>
    intro p s c' h
    simp only [Morphism.iter] at h
    cases p with
    | nil =>
      simp only [List.nil_append, List.singleton_append, List.cons.injEq] at h
      rcases h with ⟨hc', _⟩
      subst hc'
      simp only [StratCert.loState, StratCert.hiState, Bool.false_eq_true, ↓reduceIte,
                 Morphism.discWord_nil, qScale, Int.mul_zero]
      exact ⟨hL0, hU0⟩
    | cons a p' =>
      simp only [List.cons_append, List.cons.injEq] at h
      have hlen := congrArg List.length h.2
      simp at hlen
  | succ k ih =>
    intro p s c' h
    show _
    have hsplit := m.applyWord_split (m.iter k) p s c' h
    rcases hsplit with ⟨w, v, r, t, c, hu, hc, hp⟩
    rcases ih w v c hu with ⟨hwLo, hwHi⟩
    have hmem : (r, c', t) ∈ wordSplits (m.applyChar c) := mem_wordSplits hc
    simp only [checkAllTransitions, Bool.and_eq_true, List.all_eq_true] at htrans
    have hchk : checkTransition m cert (qPos m.mTr m.mDisc (0, 1)) c (r, c', t) = true := by
      cases c
      · exact htrans.1 (r, c', t) hmem
      · exact htrans.2 (r, c', t) hmem
    simp only [checkTransition, Bool.and_eq_true] at hchk
    have hleLo := hchk.1.1.1
    have hleHi := hchk.1.1.2
    have hdisc_p : qScale (cert.D : Int) (m.discWord p) =
        qAdd (qMulLam2 m.mTr m.mDet (qScale (cert.D : Int) (m.discWord w)))
             (qScale (cert.D : Int) (m.discWord r)) := by
      rw [hp, Morphism.discWord_append, Morphism.discWord_applyWord, qScale_add, qScale_mulLam2]
    rw [hdisc_p]
    by_cases hlp : qPos m.mTr m.mDisc (0, 1) = true
    · simp only [hlp, ↓reduceIte] at hleLo hleHi
      have h1 := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                   (qMulLam2_lt_of_pos hd hdisc hlp hwLo)
      have h2 := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                   (qMulLam2_lt_of_pos hd hdisc hlp hwHi)
      exact ⟨qLe_trans_lt hd hleLo h1, qLt_trans_le hd h2 hleHi⟩
    · have hln : qPos m.mTr m.mDisc (0, -1) = true := by
        rcases hlam with h1 | h2; exact absurd h1 hlp; exact h2
      have hlp_f : qPos m.mTr m.mDisc (0, 1) = false := Bool.eq_false_iff.mpr hlp
      simp only [hlp_f, Bool.false_eq_true, ↓reduceIte] at hleLo hleHi
      have h1 := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                   (qMulLam2_lt_of_neg hd hdisc hln hwHi)
      have h2 := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                   (qMulLam2_lt_of_neg hd hdisc hln hwLo)
      exact ⟨qLe_trans_lt hd hleLo h1, qLt_trans_le hd h2 hleHi⟩

/-- **MASTER SOUNDNESS THEOREM A (Stratified Prefix-Discrepancy Invariant)**:
    Any accepted pure-data certificate `cert` certifies strict residue-stratified quadratic-ring
    prefix discrepancy bounds for ALL `n : Nat`. -/
theorem stratCert_sound_prefix (m : Morphism) (cert : StratCert)
    (hcert : verifyCert m cert = true) :
    ∀ n : Nat,
      qLt m.mTr m.mDisc (cert.Lres.getD (n % cert.M) (0, 0))
          (qScale (cert.D : Int) (m.discWord (m.wordPrefix n))) = true ∧
      qLt m.mTr m.mDisc (qScale (cert.D : Int) (m.discWord (m.wordPrefix n)))
          (cert.Ures.getD (n % cert.M) (0, 0)) = true := by
  simp only [verifyCert, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhead, h0⟩, h1⟩, _hD⟩, _hM⟩, _hLr⟩, _hUr⟩, hm0⟩, hm1⟩, hdiscPos⟩, _hLam⟩, hlam⟩, hL0⟩, hU0⟩, htrans⟩, _hdiam⟩
  have hd : 0 < m.mDisc := by unfold Morphism.mDisc; omega
  have hdisc : (m.mDisc : Int) = m.mTr * m.mTr - 4 * m.mDet := by
    unfold Morphism.mDisc Morphism.mDiscInt at *; omega
  intro n
  -- Split `m.iter (n + 1)` at position `n` into `wordPrefix n ++ [c'] ++ s`!
  have hlen : n + 1 < (m.iter (n + 1)).length := by
    have := m.iter_length_ge hhead h0 h1 (n + 1); omega
  have htake : (m.iter (n + 1)).take n = m.wordPrefix n :=
    m.wordPrefix_eq_iter_take hhead h0 h1 (by omega)
  cases hdrop : (m.iter (n + 1)).drop n with
  | nil =>
    have : ((m.iter (n + 1)).drop n).length = 0 := by rw [hdrop]; rfl
    rw [List.length_drop] at this; omega
  | cons c' s =>
    have hiter_eq : m.applyWord (m.iter n) = m.wordPrefix n ++ [c'] ++ s := by
      have htd := (List.take_append_drop n (m.iter (n + 1))).symm
      rw [htake, hdrop] at htd
      simpa [Morphism.iter, List.append_assoc] using htd
    rcases m.applyWord_split (m.iter n) (m.wordPrefix n) s c' hiter_eq with
      ⟨w, v, r, t, c, hu, hc, hp⟩
    have hinv := iter_prefix_invariant m cert hd hdisc hlam hL0 hU0 htrans n w v c hu
    rcases hinv with ⟨hwLo, hwHi⟩
    have hmem : (r, c', t) ∈ wordSplits (m.applyChar c) := mem_wordSplits hc
    simp only [checkAllTransitions, Bool.and_eq_true, List.all_eq_true] at htrans
    have hchk : checkTransition m cert (qPos m.mTr m.mDisc (0, 1)) c (r, c', t) = true := by
      cases c
      · exact htrans.1 (r, c', t) hmem
      · exact htrans.2 (r, c', t) hmem
    simp only [checkTransition, Bool.and_eq_true] at hchk
    have hresLo := hchk.1.2
    have hresHi := hchk.2
    have hmod : n % cert.M = r.length % cert.M := by
      have hplen := m.wordPrefix_length hhead h0 h1 n
      rw [← hplen, hp, List.length_append, Nat.add_mod, m.applyWord_length_mod hm0 hm1 w, Nat.zero_add, Nat.mod_mod]
    rw [hmod]
    have hdisc_p : qScale (cert.D : Int) (m.discWord (m.wordPrefix n)) =
        qAdd (qMulLam2 m.mTr m.mDet (qScale (cert.D : Int) (m.discWord w)))
             (qScale (cert.D : Int) (m.discWord r)) := by
      rw [hp, Morphism.discWord_append, Morphism.discWord_applyWord, qScale_add, qScale_mulLam2]
    rw [hdisc_p]
    by_cases hlp : qPos m.mTr m.mDisc (0, 1) = true
    · simp only [hlp, ↓reduceIte] at hresLo hresHi
      have h1' := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                    (qMulLam2_lt_of_pos hd hdisc hlp hwLo)
      have h2' := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                    (qMulLam2_lt_of_pos hd hdisc hlp hwHi)
      exact ⟨qLe_trans_lt hd hresLo h1', qLt_trans_le hd h2' hresHi⟩
    · have hln : qPos m.mTr m.mDisc (0, -1) = true := by
        rcases hlam with h1' | h2'; exact absurd h1' hlp; exact h2'
      have hlp_f : qPos m.mTr m.mDisc (0, 1) = false := Bool.eq_false_iff.mpr hlp
      simp only [hlp_f, Bool.false_eq_true, ↓reduceIte] at hresLo hresHi
      have h1' := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                    (qMulLam2_lt_of_neg hd hdisc hln hwHi)
      have h2' := qLt_add_right (c := qScale (cert.D : Int) (m.discWord r))
                    (qMulLam2_lt_of_neg hd hdisc hln hwLo)
      exact ⟨qLe_trans_lt hd hresLo h1', qLt_trans_le hd h2' hresHi⟩

/-- **MASTER SOUNDNESS THEOREM B (Infinite Exact `C`-Balance)**:
    Any accepted pure-data certificate `cert` proves universal `C`-balance for ALL equal-length
    factors `x[i..i+n)` and `x[j..j+n)` across the infinite fixed point `x`. -/
theorem stratCert_sound_balance (m : Morphism) (cert : StratCert)
    (hcert : verifyCert m cert = true) :
    ∀ i j n : Nat,
      Int.natAbs ((countOnes (m.wordFactor i n) : Int) - (countOnes (m.wordFactor j n) : Int)) ≤ cert.C := by
  have hpref := stratCert_sound_prefix m cert hcert
  simp only [verifyCert, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhead, h0⟩, h1⟩, hD⟩, hM⟩, _hLr⟩, _hUr⟩, _hm0⟩, _hm1⟩, hdiscPos⟩, hLam⟩, _hlam⟩, _hL0⟩, _hU0⟩, _htrans⟩, hdiam⟩
  have hd : 0 < m.mDisc := by unfold Morphism.mDisc; omega
  -- Helper proving one direction: `#₁(u) - #₁(v) ≤ C`
  have one_dir : ∀ i j n : Nat,
      (countOnes (m.wordFactor i n) : Int) - (countOnes (m.wordFactor j n) : Int) ≤ (cert.C : Int) := by
    intro i j n
    let r := i % cert.M
    let s := (j + n) % cert.M
    let rho := n % cert.M
    have hr_lt : r < cert.M := Nat.mod_lt i hM
    have hs_lt : s < cert.M := Nat.mod_lt (j + n) hM
    have hrho_lt : rho < cert.M := Nat.mod_lt n hM
    have hrp : (i + n) % cert.M = (r + rho) % cert.M := by
      simp [r, rho, Nat.add_mod]
    have hsp : j % cert.M = (s + (cert.M - rho) % cert.M) % cert.M := by
      have h1' : (j + n + (cert.M - rho)) % cert.M = j % cert.M := by
        have hsum : (n + (cert.M - rho)) % cert.M = 0 := by
          have hnm : n % cert.M = rho := rfl
          have : (n + (cert.M - rho)) % cert.M = (rho + (cert.M - rho)) % cert.M := by
            calc (n + (cert.M - rho)) % cert.M
                = (n % cert.M + (cert.M - rho) % cert.M) % cert.M := Nat.add_mod _ _ _
              _ = (rho % cert.M + (cert.M - rho) % cert.M) % cert.M := by rw [hnm, Nat.mod_eq_of_lt hrho_lt]
              _ = (rho + (cert.M - rho)) % cert.M := (Nat.add_mod _ _ _).symm
          rw [this, Nat.add_sub_of_le (Nat.le_of_lt hrho_lt), Nat.mod_self]
        rw [Nat.add_assoc, Nat.add_mod, hsum, Nat.add_zero, Nat.mod_mod]
      rw [← h1']
      simp [s, Nat.add_mod]
    -- Prefix bounds at i, i+n, j, j+n:
    have hi_lo := (hpref i).1
    have hin_hi := (hpref (i + n)).2
    have hjn_lo := (hpref (j + n)).1
    have hj_hi := (hpref j).2
    rw [hrp] at hin_hi
    rw [hsp] at hj_hi
    -- Combine: D*(disc(u)) < Ures[rp] - Lres[r] and D*(-disc(v)) < Ures[sp] - Lres[s]
    have hu_lt : qLt m.mTr m.mDisc
        (qScale (cert.D : Int) (m.discWord (m.wordFactor i n)))
        (qSub (cert.Ures.getD ((r + rho) % cert.M) (0, 0)) (cert.Lres.getD r (0, 0))) = true := by
      rw [m.discWord_wordFactor hhead h0 h1 i n, qScale_sub]
      exact qLt_sub_of_lt hd hin_hi hi_lo
    have hv_lt : qLt m.mTr m.mDisc
        (qSub (qScale (cert.D : Int) (m.discWord (m.wordPrefix j)))
              (qScale (cert.D : Int) (m.discWord (m.wordPrefix (j + n)))))
        (qSub (cert.Ures.getD ((s + (cert.M - rho) % cert.M) % cert.M) (0, 0))
              (cert.Lres.getD s (0, 0))) = true :=
      qLt_sub_of_lt hd hj_hi hjn_lo
    have hsum_lt := qLt_add_both hd hu_lt hv_lt
    -- Extract certificate diameter inequality for (rho, r, s)
    simp only [checkStratDiameter, List.all_eq_true, List.mem_range] at hdiam
    have hdiam_inst := hdiam rho hrho_lt r hr_lt s hs_lt
    have htot := qLt_trans_le hd hsum_lt hdiam_inst
    -- Rewrite LHS as `((#₁(u) - #₁(v)) * D) * Lambda`
    have hlen_eq : (m.wordFactor i n).length = (m.wordFactor j n).length := by
      rw [m.wordFactor_length hhead h0 h1, m.wordFactor_length hhead h0 h1]
    have hdiff_eq :
        qAdd (qScale (cert.D : Int) (m.discWord (m.wordFactor i n)))
             (qSub (qScale (cert.D : Int) (m.discWord (m.wordPrefix j)))
                   (qScale (cert.D : Int) (m.discWord (m.wordPrefix (j + n))))) =
        qScale (((countOnes (m.wordFactor i n) : Int) - (countOnes (m.wordFactor j n) : Int)) * (cert.D : Int))
               m.mLambda := by
      have hfj := m.discWord_wordFactor hhead h0 h1 j n
      have hfd := m.discWord_factor_diff hlen_eq
      have h1' : qAdd (qScale (cert.D : Int) (m.discWord (m.wordFactor i n)))
                      (qSub (qScale (cert.D : Int) (m.discWord (m.wordPrefix j)))
                            (qScale (cert.D : Int) (m.discWord (m.wordPrefix (j + n))))) =
                 qScale (cert.D : Int) (qSub (m.discWord (m.wordFactor i n)) (m.discWord (m.wordFactor j n))) := by
        rw [hfj]
        simp only [qAdd, qSub, qScale, Prod.mk.injEq]
        constructor <;> grind
      rw [h1', hfd, qScale_qScale, Int.mul_comm]
    rw [hdiff_eq] at htot
    have hlt_int := qScale_lt_cancel hd hLam htot
    -- `((#₁(u) - #₁(v)) * D) < (C + 1) * D` with `D > 0` => `#₁(u) - #₁(v) ≤ C`!
    have hD_pos : (0 : Int) < (cert.D : Int) := by omega
    have hlt2 : ((countOnes (m.wordFactor i n) : Int) - (countOnes (m.wordFactor j n) : Int)) < (cert.C + 1 : Int) := by
      by_cases hle : (countOnes (m.wordFactor i n) : Int) - (countOnes (m.wordFactor j n) : Int) < (cert.C + 1 : Int)
      · exact hle
      · have hge : (cert.C + 1 : Int) ≤ (countOnes (m.wordFactor i n) : Int) - (countOnes (m.wordFactor j n) : Int) := by omega
        have hm := Int.mul_le_mul_of_nonneg_right hge (by omega : (0 : Int) ≤ (cert.D : Int))
        have hcast : (((cert.C + 1 : Nat) * cert.D : Nat) : Int) = (cert.C + 1 : Int) * (cert.D : Int) := by
          simp [Int.natCast_mul, Int.natCast_add]
        omega
    omega
  intro i j n
  have h1' := one_dir i j n
  have h2' := one_dir j i n
  omega

/-! =========================================================================
    SECTION 4: Flagship Infinite Theorems, Sharpness & Hostile Mutation Tests
    ========================================================================= -/

/-! ### 4.1 Infinite Parametric Family `σ_k : 0 ↦ 0^k 1 0, 1 ↦ 0 1` (`det M_k = k`) -/

theorem countZeros_replicate_false (j : Nat) : countZeros (List.replicate j false) = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, countZeros, ih]

theorem countOnes_replicate_false (j : Nat) : countOnes (List.replicate j false) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, countOnes, ih]

theorem sigmaK_invariants (k : Nat) :
    (sigmaK k).mA = (k : Int) + 1 ∧
    (sigmaK k).mB = 1 ∧
    (sigmaK k).mC = 1 ∧
    (sigmaK k).mD = 1 ∧
    (sigmaK k).mTr = (k : Int) + 2 ∧
    (sigmaK k).mDet = (k : Int) ∧
    (sigmaK k).mDiscInt = (k : Int) * (k : Int) + 4 ∧
    (sigmaK k).mDisc = k * k + 4 := by
  have hA : (sigmaK k).mA = (k : Int) + 1 := by
    simp [sigmaK, Morphism.mA, countZeros_append, countZeros_replicate_false, countZeros]
  have hB : (sigmaK k).mB = 1 := by
    simp [sigmaK, Morphism.mB, countOnes_append, countOnes_replicate_false, countOnes]
  have hC : (sigmaK k).mC = 1 := rfl
  have hD : (sigmaK k).mD = 1 := rfl
  have hTr : (sigmaK k).mTr = (k : Int) + 2 := by
    unfold Morphism.mTr; rw [hA, hD]; omega
  have hDet : (sigmaK k).mDet = (k : Int) := by
    unfold Morphism.mDet; rw [hA, hB, hC, hD]; grind
  have hDiscInt : (sigmaK k).mDiscInt = (k : Int) * (k : Int) + 4 := by
    unfold Morphism.mDiscInt; rw [hTr, hDet]; grind
  have hDisc : (sigmaK k).mDisc = k * k + 4 := by
    unfold Morphism.mDisc; rw [hDiscInt]
    have : (k : Int) * (k : Int) + 4 = ((k * k + 4 : Nat) : Int) := by
      simp [Int.natCast_add, Int.natCast_mul]
    rw [this]; rfl
  exact ⟨hA, hB, hC, hD, hTr, hDet, hDiscInt, hDisc⟩

theorem mem_wordSplits_sigmaK_w0 (k : Nat) {r t : List Bool} {dst : Bool}
    (hmem : (r, dst, t) ∈ wordSplits (sigmaK k).w0) :
    (∃ j : Nat, j < k ∧ r = List.replicate j false ∧ dst = false) ∨
    (r = List.replicate k false ∧ dst = true) ∨
    (r = List.replicate k false ++ [true] ∧ dst = false) := by
  -- Helper characterizing `wordSplitsAux pref (List.replicate m false ++ [true, false])`
  have haux : ∀ (m : Nat) (pref : List Bool),
      (r, dst, t) ∈ wordSplitsAux pref (List.replicate m false ++ [true, false]) →
      (∃ j : Nat, j < m ∧ r = pref ++ List.replicate j false ∧ dst = false) ∨
      (r = pref ++ List.replicate m false ∧ dst = true) ∨
      (r = pref ++ List.replicate m false ++ [true] ∧ dst = false) := by
    intro m
    induction m with
    | zero =>
      intro pref hm
      simp only [List.replicate_zero, List.nil_append, wordSplitsAux, List.mem_cons,
                 List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨hr, hd, _⟩ | ⟨hr, hd, _⟩
      · right; left; exact ⟨by simpa using hr, hd⟩
      · right; right; exact ⟨by simpa using hr, hd⟩
    | succ m ih =>
      intro pref hm
      simp only [List.replicate_succ, List.cons_append, wordSplitsAux, List.mem_cons,
                 Prod.mk.injEq] at hm
      rcases hm with ⟨hr, hd, _⟩ | htail
      · left; exact ⟨0, by omega, by simpa using hr, hd⟩
      · rcases ih (pref ++ [false]) htail with ⟨j, hj, hr, hd⟩ | ⟨hr, hd⟩ | ⟨hr, hd⟩
        · left
          refine ⟨j + 1, by omega, ?_, hd⟩
          rw [hr, List.append_assoc, List.replicate_succ, List.singleton_append]
        · right; left
          refine ⟨?_, hd⟩
          rw [hr, List.append_assoc, List.replicate_succ, List.singleton_append]
        · right; right
          refine ⟨?_, hd⟩
          rw [hr, List.append_assoc, List.append_assoc, List.replicate_succ, List.singleton_append]
          simp [List.append_assoc]
  simpa [sigmaK, wordSplits] using haux k [] hmem

/-- Symbolic verification of `sigmaKCert k` for ALL `k ≥ 8` (`phaseBound k = 2*k - 4`). -/
theorem verifyCert_sigmaK_ge8 (k : Nat) (hk : 8 ≤ k) :
    verifyCert (sigmaK k) (sigmaKCert k) = true := by
  have hinv := sigmaK_invariants k
  rcases hinv with ⟨hA, hB, hC, hD, hTr, hDet, hDiscInt, hDisc⟩
  have hne1 : (k == 1) = false := beq_false_of_ne (by omega)
  have hne2 : (k == 2) = false := beq_false_of_ne (by omega)
  have hne3 : (k == 3) = false := beq_false_of_ne (by omega)
  have hnot7 : ¬ (k ≤ 7) := by omega
  have hcert_eq : sigmaKCert k =
      { D := 1, M := 1, C := 2 * k - 4,
        L0 := (1 - (k : Int), 0), U0 := (1, -1),
        L1 := (-(k : Int), 1), U1 := (0, -1),
        Lres := [(-(k : Int), 1)], Ures := [(1, -1)] } := by
    simp [sigmaKCert, phaseBound, hne1, hne2, hne3, hnot7]
  rw [hcert_eq]
  have hd_cast : ((k * k + 4 : Nat) : Int) = (k : Int) * (k : Int) + 4 := by
    simp [Int.natCast_add, Int.natCast_mul]
  -- Check λ₂ > 0
  have hlamPos : qPos (sigmaK k).mTr (sigmaK k).mDisc (0, 1) = true := by
    rw [hTr, hDisc]; simp only [qPos, qToXY, signSqrtGt_iff, hd_cast]
    right; left
    have hsq : ((k : Int) * (k : Int) + 4) * (1 * 1) < ((k : Int) + 2) * ((k : Int) + 2) := by
      have : ((k : Int) + 2) * ((k : Int) + 2) - ((k : Int) * (k : Int) + 4) * (1 * 1) = 4 * (k : Int) := by grind
      omega
    exact ⟨by omega, by omega, by simpa using hsq⟩
  -- Check Λ = (2, -1) > 0
  have hLam : qPos (sigmaK k).mTr (sigmaK k).mDisc (sigmaK k).mLambda = true := by
    unfold Morphism.mLambda; rw [hC, hD, hTr, hDisc]
    simp only [qPos, qToXY, signSqrtGt_iff, hd_cast]
    right; right
    refine ⟨by omega, Or.inr ?_⟩
    have : (2 * (1 + 1) + ((k : Int) + 2) * (-1)) * (2 * (1 + 1) + ((k : Int) + 2) * (-1)) =
           (k : Int) * (k : Int) - 4 * (k : Int) + 4 := by grind
    have : ((k : Int) * (k : Int) + 4) * ((-1) * (-1)) = (k : Int) * (k : Int) + 4 := by grind
    omega
  -- Check L0 < 0 < U0
  have hL0 : qLt (sigmaK k).mTr (sigmaK k).mDisc (1 - (k : Int), 0) (0, 0) = true := by
    rw [hTr, hDisc]; simp only [qLt, qPos, qToXY, qSub, signSqrtGt_iff]
    left; omega
  have hU0 : qLt (sigmaK k).mTr (sigmaK k).mDisc (0, 0) (1, -1) = true := by
    rw [hTr, hDisc]; simp only [qLt, qPos, qToXY, qSub, signSqrtGt_iff, hd_cast]
    right; right
    refine ⟨by omega, Or.inr ?_⟩
    have : (2 * (1 - 0) + ((k : Int) + 2) * (-1 - 0)) * (2 * (1 - 0) + ((k : Int) + 2) * (-1 - 0)) =
           (k : Int) * (k : Int) := by grind
    have : ((k : Int) * (k : Int) + 4) * ((-1 - 0) * (-1 - 0)) = (k : Int) * (k : Int) + 4 := by grind
    omega
  -- Helper: prove `qNonneg ((k:Int)+2) (k*k+4) p = true` by normalizing `p = (u, v)`
  have h_pos_mm : ∀ m : Int, 0 ≤ m → qNonneg ((k : Int) + 2) (k * k + 4) (m, -m) = true := by
    intro m hm
    simp only [qNonneg, qToXY, signSqrtGe_iff, hd_cast]
    by_cases hm0 : m = 0
    · subst hm0; left; simp
    · right
      refine ⟨by omega, Or.inr ?_⟩
      have e1 : (2 * m + ((k : Int) + 2) * (-m)) * (2 * m + ((k : Int) + 2) * (-m)) =
                (k : Int) * (k : Int) * (m * m) := by grind
      have e2 : ((k : Int) * (k : Int) + 4) * ((-m) * (-m)) =
                (k : Int) * (k : Int) * (m * m) + 4 * (m * m) := by grind
      have hm2 : 0 ≤ m * m := sq_nonneg m
      omega
  have h_pos_zero : qNonneg ((k : Int) + 2) (k * k + 4) (0, 0) = true := by
    simp [qNonneg, qToXY, signSqrtGe_iff]
  have h_pos_one : qNonneg ((k : Int) + 2) (k * k + 4) (1, 0) = true := by
    simp [qNonneg, qToXY, signSqrtGe_iff]
  have h_pos_lam : qNonneg ((k : Int) + 2) (k * k + 4) (0, 1) = true := by
    have := signSqrtGt_imp_ge (by simpa [qPos, qToXY, hTr, hDisc] using hlamPos)
    simpa [qNonneg, qToXY] using this
  have h_pos_m1_2 : qNonneg ((k : Int) + 2) (k * k + 4) (-1, 2) = true := by
    simp only [qNonneg, qToXY, signSqrtGe_iff, hd_cast]
    left; refine ⟨by omega, by omega, ?_⟩
    have : (2 * (-1 : Int) + ((k : Int) + 2) * 2) * (2 * (-1 : Int) + ((k : Int) + 2) * 2) -
           ((k : Int) * (k : Int) + 4) * (2 * 2) = 8 * (k : Int) - 12 := by grind
    omega
  have h_pos_1mk_kp1 : qNonneg ((k : Int) + 2) (k * k + 4) (1 - (k : Int), (k : Int) + 1) = true := by
    simp only [qNonneg, qToXY, signSqrtGe_iff, hd_cast]
    left
    have hk2 : 0 ≤ (k : Int) * (k : Int) := sq_nonneg k
    have e1 : 2 * (1 - (k : Int)) + ((k : Int) + 2) * ((k : Int) + 1) = (k : Int) * (k : Int) + (k : Int) + 4 := by grind
    rw [e1]
    refine ⟨by omega, by omega, ?_⟩
    have e2 : ((k : Int) * (k : Int) + (k : Int) + 4) * ((k : Int) * (k : Int) + (k : Int) + 4) -
              ((k : Int) * (k : Int) + 4) * (((k : Int) + 1) * ((k : Int) + 1)) =
              4 * ((k : Int) * (k : Int)) + 12 := by grind
    omega
  have h_pos_1mk_k : qNonneg ((k : Int) + 2) (k * k + 4) (1 - (k : Int), (k : Int)) = true := by
    simp only [qNonneg, qToXY, signSqrtGe_iff, hd_cast]
    left
    have hk2 : 0 ≤ (k : Int) * (k : Int) := sq_nonneg k
    have e1 : 2 * (1 - (k : Int)) + ((k : Int) + 2) * (k : Int) = (k : Int) * (k : Int) + 2 := by grind
    rw [e1]
    refine ⟨by omega, by omega, ?_⟩
    have e2 : ((k : Int) * (k : Int) + 2) * ((k : Int) * (k : Int) + 2) -
              ((k : Int) * (k : Int) + 4) * ((k : Int) * (k : Int)) = 4 := by grind
    omega
  have h_pos_2mk_k : qNonneg ((k : Int) + 2) (k * k + 4) (2 - (k : Int), (k : Int)) = true := by
    simp only [qNonneg, qToXY, signSqrtGe_iff, hd_cast]
    left
    have hk2 : 0 ≤ (k : Int) * (k : Int) := sq_nonneg k
    have e1 : 2 * (2 - (k : Int)) + ((k : Int) + 2) * (k : Int) = (k : Int) * (k : Int) + 4 := by grind
    rw [e1]
    refine ⟨by omega, by omega, ?_⟩
    have e2 : ((k : Int) * (k : Int) + 4) * ((k : Int) * (k : Int) + 4) -
              ((k : Int) * (k : Int) + 4) * ((k : Int) * (k : Int)) = 4 * ((k : Int) * (k : Int)) + 16 := by grind
    omega
  have h_pos_kj : ∀ j : Nat, j < k →
      qNonneg ((k : Int) + 2) (k * k + 4) (1 - ((k : Int) - (j : Int)), (k : Int) - (j : Int)) = true := by
    intro j hj
    simp only [qNonneg, qToXY, signSqrtGe_iff, hd_cast]
    left
    have hm : 0 ≤ ((k : Int) - (j : Int)) * (j : Int) := Int.mul_nonneg (by omega) (by omega)
    have hkm : 0 ≤ (k : Int) * ((k : Int) - (j : Int)) := Int.mul_nonneg (by omega) (by omega)
    have e1 : 2 * (1 - ((k : Int) - (j : Int))) + ((k : Int) + 2) * ((k : Int) - (j : Int)) =
              (k : Int) * ((k : Int) - (j : Int)) + 2 := by grind
    rw [e1]
    refine ⟨by omega, by omega, ?_⟩
    have e2 : ((k : Int) * ((k : Int) - (j : Int)) + 2) * ((k : Int) * ((k : Int) - (j : Int)) + 2) -
              ((k : Int) * (k : Int) + 4) * (((k : Int) - (j : Int)) * ((k : Int) - (j : Int))) =
              4 * (((k : Int) - (j : Int)) * (j : Int)) + 4 := by grind
    omega
  -- Check all transitions for w0 and w1
  let cert0 : StratCert :=
      { D := 1, M := 1, C := 2 * k - 4,
        L0 := (1 - (k : Int), 0), U0 := (1, -1),
        L1 := (-(k : Int), 1), U1 := (0, -1),
        Lres := [(-(k : Int), 1)], Ures := [(1, -1)] }
  have htrans : checkAllTransitions (sigmaK k) cert0 (qPos (sigmaK k).mTr (sigmaK k).mDisc (0, 1)) = true := by
    rw [hlamPos]
    simp only [checkAllTransitions, Bool.and_eq_true, List.all_eq_true]
    constructor
    · -- Splits of w0
      intro sp hmem
      rcases sp with ⟨r, dst, t⟩
      rcases mem_wordSplits_sigmaK_w0 k hmem with ⟨j, hj, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- r = 0^j (j < k), dst = false
        have hdr : (sigmaK k).discWord (List.replicate j false) = (-(j : Int), (j : Int)) := by
          simp [Morphism.discWord, hC, hD, countZeros_replicate_false, countOnes_replicate_false]
        simp only [checkTransition, cert0, StratCert.loState, StratCert.hiState, Bool.false_eq_true,
                   ↓reduceIte, hdr, hTr, hDet, hDisc, qScale, qMulLam2, qAdd, Nat.mod_one,
                   List.getD_cons_zero, Bool.and_eq_true, qLe, qSub]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · have heq : (-((k : Int)) * 0 + (1 : Nat) * -(j : Int) - (1 - (k : Int)),
                      1 - (k : Int) + ((k : Int) + 2) * 0 + (1 : Nat) * (j : Int) - 0) =
                     ((k : Int) - 1 - (j : Int), -((k : Int) - 1 - (j : Int))) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_mm ((k : Int) - 1 - (j : Int)) (by omega)
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * -(j : Int)),
                      -1 - (1 + ((k : Int) + 2) * -1 + (1 : Nat) * (j : Int))) =
                     (1 - ((k : Int) - (j : Int)), (k : Int) - (j : Int)) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_kj j hj
        · have heq : (-((k : Int)) * 0 + (1 : Nat) * -(j : Int) - -(k : Int),
                      1 - (k : Int) + ((k : Int) + 2) * 0 + (1 : Nat) * (j : Int) - 1) =
                     ((k : Int) - (j : Int), -((k : Int) - (j : Int))) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_mm ((k : Int) - (j : Int)) (by omega)
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * -(j : Int)),
                      -1 - (1 + ((k : Int) + 2) * -1 + (1 : Nat) * (j : Int))) =
                     (1 - ((k : Int) - (j : Int)), (k : Int) - (j : Int)) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_kj j hj
      · -- r = 0^k, dst = true
        have hdr : (sigmaK k).discWord (List.replicate k false) = (-(k : Int), (k : Int)) := by
          simp [Morphism.discWord, hC, hD, countZeros_replicate_false, countOnes_replicate_false]
        simp only [checkTransition, cert0, StratCert.loState, StratCert.hiState, Bool.false_eq_true,
                   ↓reduceIte, hdr, hTr, hDet, hDisc, qScale, qMulLam2, qAdd, Nat.mod_one,
                   List.getD_cons_zero, Bool.and_eq_true, qLe, qSub]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · have heq : (-((k : Int)) * 0 + (1 : Nat) * -(k : Int) - -(k : Int),
                      1 - (k : Int) + ((k : Int) + 2) * 0 + (1 : Nat) * (k : Int) - 1) = (0, 0) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_zero
        · have heq : (0 - (-((k : Int)) * -1 + (1 : Nat) * -(k : Int)),
                      -1 - (1 + ((k : Int) + 2) * -1 + (1 : Nat) * (k : Int))) = (0, 0) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_zero
        · have heq : (-((k : Int)) * 0 + (1 : Nat) * -(k : Int) - -(k : Int),
                      1 - (k : Int) + ((k : Int) + 2) * 0 + (1 : Nat) * (k : Int) - 1) = (0, 0) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_zero
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * -(k : Int)),
                      -1 - (1 + ((k : Int) + 2) * -1 + (1 : Nat) * (k : Int))) = (1, 0) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_one
      · -- r = 0^k 1, dst = false
        have hdr : (sigmaK k).discWord (List.replicate k false ++ [true]) = (1 - (k : Int), (k : Int)) := by
          simp [Morphism.discWord, hC, hD, countZeros_append, countOnes_append,
                countZeros_replicate_false, countOnes_replicate_false, countZeros, countOnes]
        simp only [checkTransition, cert0, StratCert.loState, StratCert.hiState, Bool.false_eq_true,
                   ↓reduceIte, hdr, hTr, hDet, hDisc, qScale, qMulLam2, qAdd, Nat.mod_one,
                   List.getD_cons_zero, Bool.and_eq_true, qLe, qSub]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · have heq : (-((k : Int)) * 0 + (1 : Nat) * (1 - (k : Int)) - (1 - (k : Int)),
                      1 - (k : Int) + ((k : Int) + 2) * 0 + (1 : Nat) * (k : Int) - 0) = (0, 1) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_lam
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * (1 - (k : Int))),
                      -1 - (1 + ((k : Int) + 2) * -1 + (1 : Nat) * (k : Int))) = (0, 0) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_zero
        · have heq : (-((k : Int)) * 0 + (1 : Nat) * (1 - (k : Int)) - -(k : Int),
                      1 - (k : Int) + ((k : Int) + 2) * 0 + (1 : Nat) * (k : Int) - 1) = (1, 0) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_one
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * (1 - (k : Int))),
                      -1 - (1 + ((k : Int) + 2) * -1 + (1 : Nat) * (k : Int))) = (0, 0) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_zero
    · -- Splits of w1 = [false, true]
      intro sp hmem
      simp only [sigmaK, wordSplits, wordSplitsAux, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · -- r = [], dst = false
        have hdr : (sigmaK k).discWord [] = (0, 0) := (sigmaK k).discWord_nil
        simp only [checkTransition, cert0, StratCert.loState, StratCert.hiState, Bool.false_eq_true,
                   ↓reduceIte, hdr, hTr, hDet, hDisc, qScale, qMulLam2, qAdd, Nat.mod_one,
                   List.getD_cons_zero, Bool.and_eq_true, qLe, qSub]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · have heq : (-((k : Int)) * 1 + (1 : Nat) * 0 - (1 - (k : Int)),
                      -(k : Int) + ((k : Int) + 2) * 1 + (1 : Nat) * 0 - 0) = (-1, 2) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_m1_2
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * 0),
                      -1 - (0 + ((k : Int) + 2) * -1 + (1 : Nat) * 0)) = (1 - (k : Int), (k : Int) + 1) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_1mk_kp1
        · have heq : (-((k : Int)) * 1 + (1 : Nat) * 0 - -(k : Int),
                      -(k : Int) + ((k : Int) + 2) * 1 + (1 : Nat) * 0 - 1) = (0, 1) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_lam
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * 0),
                      -1 - (0 + ((k : Int) + 2) * -1 + (1 : Nat) * 0)) = (1 - (k : Int), (k : Int) + 1) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_1mk_kp1
      · -- r = [false], dst = true
        have hdr : (sigmaK k).discWord [false] = (-1, 1) := by
          simp [Morphism.discWord, hC, hD, countZeros, countOnes]
        simp only [checkTransition, cert0, StratCert.loState, StratCert.hiState, List.nil_append,
                   ↓reduceIte, hdr, hTr, hDet, hDisc, qScale, qMulLam2, qAdd, Nat.mod_one,
                   List.getD_cons_zero, Bool.and_eq_true, qLe, qSub]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · have heq : (-((k : Int)) * 1 + (1 : Nat) * -1 - -(k : Int),
                      -(k : Int) + ((k : Int) + 2) * 1 + (1 : Nat) * 1 - 1) = (-1, 2) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_m1_2
        · have heq : (0 - (-((k : Int)) * -1 + (1 : Nat) * -1),
                      -1 - (0 + ((k : Int) + 2) * -1 + (1 : Nat) * 1)) = (1 - (k : Int), (k : Int)) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_1mk_k
        · have heq : (-((k : Int)) * 1 + (1 : Nat) * -1 - -(k : Int),
                      -(k : Int) + ((k : Int) + 2) * 1 + (1 : Nat) * 1 - 1) = (-1, 2) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_m1_2
        · have heq : (1 - (-((k : Int)) * -1 + (1 : Nat) * -1),
                      -1 - (0 + ((k : Int) + 2) * -1 + (1 : Nat) * 1)) = (2 - (k : Int), (k : Int)) := by
            simp only [Prod.mk.injEq]; constructor <;> grind
          rw [heq]; exact h_pos_2mk_k
  -- Check stratified diameter (`M = 1`): governed by `2k^2 - 21k + 48 = (k-8)(2k-5) + 8 ≥ 8 > 0`!
  have hdiam : checkStratDiameter (sigmaK k) cert0 = true := by
    simp only [checkStratDiameter, cert0, Morphism.mLambda, hC, hD, hTr, hDisc,
               List.range_one, List.all_cons, List.all_nil, Bool.and_true, Nat.mod_one,
               List.getD_cons_zero, qScale, qSub, qAdd, qLe, qNonneg, qToXY, signSqrtGe_iff, hd_cast]
    have hCcast : (((2 * k - 4 + 1) * 1 : Nat) : Int) = 2 * (k : Int) - 3 := by omega
    rw [hCcast]
    right
    have eY : (2 * (k : Int) - 3) * (-1) - (-1 - 1 + (-1 - 1)) = 7 - 2 * (k : Int) := by grind
    have eX : 2 * ((2 * (k : Int) - 3) * (1 + 1) - (1 - -(k : Int) + (1 - -(k : Int)))) +
              ((k : Int) + 2) * ((2 * (k : Int) - 3) * (-1) - (-1 - 1 + (-1 - 1))) =
              -2 * (k : Int) * (k : Int) + 7 * (k : Int) - 2 := by grind
    rw [eX, eY]
    refine ⟨by omega, Or.inr ?_⟩
    have hcrit : ((k : Int) * (k : Int) + 4) * ((7 - 2 * (k : Int)) * (7 - 2 * (k : Int))) -
                 ((-2 * (k : Int) * (k : Int) + 7 * (k : Int) - 2) *
                  (-2 * (k : Int) * (k : Int) + 7 * (k : Int) - 2)) =
                 4 * (((k : Int) - 8) * (2 * (k : Int) - 5) + 8) := by grind
    have hnn : 0 ≤ ((k : Int) - 8) * (2 * (k : Int) - 5) := Int.mul_nonneg (by omega) (by omega)
    omega
  -- Assemble all `verifyCert` checks
  have hhead : (sigmaK k).w0.head? = some false := by
    cases hk' : k with
    | zero => omega
    | succ k' => simp [sigmaK, List.replicate_succ]
  have hlen0 : 2 ≤ (sigmaK k).w0.length := by simp [sigmaK]
  have hlen1 : 1 ≤ (sigmaK k).w1.length := by simp [sigmaK]
  have hdiscPos : 0 < (sigmaK k).mDiscInt := by
    rw [hDiscInt]; have := sq_nonneg (k : Int); omega
  show verifyCert (sigmaK k) cert0 = true
  simp only [verifyCert, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhead, hlen0⟩, hlen1⟩, Nat.zero_lt_one⟩, Nat.zero_lt_one⟩, rfl⟩, rfl⟩,
          Nat.mod_one _⟩, Nat.mod_one _⟩, hdiscPos⟩, hLam⟩, Or.inl hlamPos⟩, hL0⟩, hU0⟩, htrans⟩, hdiam⟩

theorem verifyCert_sigmaK_all (k : Nat) (hk : 1 ≤ k) :
    verifyCert (sigmaK k) (sigmaKCert k) = true := by
  by_cases h8 : 8 ≤ k
  · exact verifyCert_sigmaK_ge8 k h8
  · have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **FLAGSHIP THEOREM 1 (Symbolic Infinite Family & Phase Transition at `k = 7 → 8`)**:
    For EVERY `k ≥ 1` (non-unimodular `det M_k = k`) and EVERY `i, j, n : Nat`, the infinite
    word of `σ_k : 0 ↦ 0^k 1 0, 1 ↦ 0 1` satisfies exact `phaseBound k`-balance. -/
theorem family_sigmaK_balance (k : Nat) (hk : 1 ≤ k) :
    ∀ i j n : Nat,
      Int.natAbs ((countOnes ((sigmaK k).wordFactor i n) : Int) -
                  (countOnes ((sigmaK k).wordFactor j n) : Int)) ≤ phaseBound k := by
  have h := stratCert_sound_balance (sigmaK k) (sigmaKCert k) (verifyCert_sigmaK_all k hk)
  have hC : (sigmaKCert k).C = phaseBound k := by
    unfold sigmaKCert phaseBound
    by_cases h1 : k = 1
    · subst h1; rfl
    · have : (k == 1) = false := beq_false_of_ne h1
      simp [this]
  rw [hC] at h
  exact h

/-- **FLAGSHIP THEOREM 1B (Exact Symbolic Prefix Discrepancy Bounds for ALL `k ≥ 2`, `n : Nat`)**:
    `-k + λ₂(k) < D(x_k[0..n)) < 1 - λ₂(k)` holds universally. -/
theorem family_sigmaK_prefix_bounds (k : Nat) (hk : 2 ≤ k) :
    ∀ n : Nat,
      qLt (sigmaK k).mTr (sigmaK k).mDisc (-(k : Int), 1)
          ((sigmaK k).discWord ((sigmaK k).wordPrefix n)) = true ∧
      qLt (sigmaK k).mTr (sigmaK k).mDisc ((sigmaK k).discWord ((sigmaK k).wordPrefix n))
          (1, -1) = true := by
  have h := stratCert_sound_prefix (sigmaK k) (sigmaKCert k) (verifyCert_sigmaK_all k (by omega))
  have hne1 : (k == 1) = false := beq_false_of_ne (by omega)
  intro n
  have hn := h n
  simp only [sigmaKCert, hne1, Bool.false_eq_true, ↓reduceIte, Nat.mod_one,
             List.getD_cons_zero, qScale] at hn
  have h1 : ((1 : Nat) : Int) * ((sigmaK k).discWord ((sigmaK k).wordPrefix n)).1 =
            ((sigmaK k).discWord ((sigmaK k).wordPrefix n)).1 := by omega
  have h2 : ((1 : Nat) : Int) * ((sigmaK k).discWord ((sigmaK k).wordPrefix n)).2 =
            ((sigmaK k).discWord ((sigmaK k).wordPrefix n)).2 := by omega
  simpa [h1, h2] using hn

/-! ### 4.2 Infinite Asymptotic Prefix Sharpness (`∀ k ≥ 2, ∀ m : Nat`) -/

theorem replicate_split_last {α : Type} (a : α) :
    ∀ n : Nat, List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    calc List.replicate (n + 1 + 1) a
        = a :: List.replicate (n + 1) a := List.replicate_succ
      _ = a :: (List.replicate n a ++ [a]) := by rw [ih]
      _ = (a :: List.replicate n a) ++ [a] := rfl
      _ = List.replicate (n + 1) a ++ [a] := by rw [← List.replicate_succ]

theorem uMinBase_is_prefix (k : Nat) (hk : 2 ≤ k) :
    ∀ m : Nat, ∃ s : List Bool, (sigmaK k).iter m = uMinBase k m ++ [false] ++ s := by
  intro m
  induction m with
  | zero => exact ⟨[], rfl⟩
  | succ m ih =>
    rcases ih with ⟨s, hs⟩
    have hw0 : (sigmaK k).w0 = List.replicate (k - 1) false ++ [false] ++ [true, false] := by
      have hk1 : k = (k - 1) + 1 := by omega
      have hrep : List.replicate k false = List.replicate (k - 1) false ++ [false] := by
        rw [← replicate_split_last false (k - 1), ← hk1]
      simp only [sigmaK, hrep, List.append_assoc]
    refine ⟨[true, false] ++ (sigmaK k).applyWord s, ?_⟩
    show (sigmaK k).applyWord ((sigmaK k).iter m) = _
    rw [hs, Morphism.applyWord_append, Morphism.applyWord_append]
    simp only [Morphism.applyWord_cons, Morphism.applyWord_nil, List.append_nil,
               Morphism.applyChar, Bool.false_eq_true, ↓reduceIte, hw0, uMinBase, List.append_assoc]

theorem uMin_is_prefix (k : Nat) (hk : 2 ≤ k) (m : Nat) :
    ∃ s : List Bool, (sigmaK k).iter (m + 1) = uMin k m ++ [true] ++ s := by
  rcases uMinBase_is_prefix k hk m with ⟨s, hs⟩
  refine ⟨[false] ++ (sigmaK k).applyWord s, ?_⟩
  show (sigmaK k).applyWord ((sigmaK k).iter m) = _
  rw [hs, Morphism.applyWord_append, Morphism.applyWord_append]
  have htf : [true, false] = [true] ++ [false] := rfl
  simp only [Morphism.applyWord_cons, Morphism.applyWord_nil, List.append_nil,
             Morphism.applyChar, Bool.false_eq_true, ↓reduceIte, sigmaK, uMin, htf, List.append_assoc]

theorem vMax_is_prefix (k : Nat) :
    ∀ m : Nat, ∃ s : List Bool, (sigmaK k).iter m = vMax k m ++ [false] ++ s := by
  intro m
  induction m with
  | zero => exact ⟨[], rfl⟩
  | succ m ih =>
    rcases ih with ⟨s, hs⟩
    refine ⟨(sigmaK k).applyWord s, ?_⟩
    show (sigmaK k).applyWord ((sigmaK k).iter m) = _
    rw [hs, Morphism.applyWord_append, Morphism.applyWord_append]
    have htf : [true, false] = [true] ++ [false] := rfl
    simp only [Morphism.applyWord_cons, Morphism.applyWord_nil, List.append_nil,
               Morphism.applyChar, Bool.false_eq_true, ↓reduceIte, sigmaK, vMax, htf, List.append_assoc]

theorem disc_uMinBase_exact (k : Nat) (hk : 2 ≤ k) :
    ∀ m : Nat,
      (sigmaK k).discWord (uMinBase k m) =
      qAdd (1 - (k : Int), 0) (qScale ((k : Int) - 1) (lam2Pow k m)) := by
  have hinv := sigmaK_invariants k
  rcases hinv with ⟨_, _, hC, hD, hTr, hDet, _, _⟩
  intro m
  induction m with
  | zero =>
    simp only [uMinBase, Morphism.discWord_nil, lam2Pow, qAdd, qScale, Prod.mk.injEq]
    omega
  | succ m ih =>
    have hdr : (sigmaK k).discWord (List.replicate (k - 1) false) = (1 - (k : Int), (k : Int) - 1) := by
      simp only [Morphism.discWord, hC, hD, countZeros_replicate_false, countOnes_replicate_false,
                 Prod.mk.injEq]
      omega
    rw [uMinBase, Morphism.discWord_append, Morphism.discWord_applyWord, ih, hdr, hTr, hDet]
    simp only [lam2Pow, qMulLam2, qAdd, qScale, Prod.mk.injEq]
    constructor <;> grind

/-- **FLAGSHIP THEOREM 1C (Exact Infinite Asymptotic Sharpness of Lower & Upper Bounds)**:
    For EVERY `k ≥ 2` and EVERY `m : Nat`, the explicit prefix `uMin k m` (resp. `vMax k m`)
    of `x_k` satisfies exact geometric convergence to `-k + λ₂(k)` (resp. `1 - λ₂(k)`). -/
theorem family_sigmaK_prefix_sharp (k : Nat) (hk : 2 ≤ k) (m : Nat) :
    (sigmaK k).discWord (uMin k m) =
      qAdd (-(k : Int), 1) (qScale ((k : Int) - 1) (lam2Pow k (m + 1))) ∧
    (sigmaK k).discWord (vMax k m) =
      qSub (1, -1) (qSub (lam2Pow k m) (lam2Pow k (m + 1))) := by
  have hinv := sigmaK_invariants k
  rcases hinv with ⟨_, _, hC, hD, hTr, hDet, _, _⟩
  constructor
  · have hdr : (sigmaK k).discWord (List.replicate k false) = (-(k : Int), (k : Int)) := by
      simp [Morphism.discWord, hC, hD, countZeros_replicate_false, countOnes_replicate_false]
    rw [uMin, Morphism.discWord_append, Morphism.discWord_applyWord,
        disc_uMinBase_exact k hk m, hdr, hTr, hDet]
    simp only [lam2Pow, qMulLam2, qAdd, qScale, Prod.mk.injEq]
    constructor <;> grind
  · induction m with
    | zero =>
      simp only [vMax, Morphism.discWord_nil, lam2Pow, qMulLam2, qSub, Prod.mk.injEq]
      constructor <;> grind
    | succ m ih =>
      have hdr : (sigmaK k).discWord (List.replicate k false ++ [true]) = (1 - (k : Int), (k : Int)) := by
        simp [Morphism.discWord, hC, hD, countZeros_append, countOnes_append,
              countZeros_replicate_false, countOnes_replicate_false, countZeros, countOnes]
      rw [vMax, List.append_assoc, Morphism.discWord_append, Morphism.discWord_applyWord,
          ih, hdr, hTr, hDet]
      simp only [lam2Pow, qMulLam2, qAdd, qSub, Prod.mk.injEq]
      constructor <;> grind

/-! ### 4.3 Same-Matrix Balance Doubling (`det = -2`, `λ₂ < 0`, `D = 4`) -/

theorem tauA_tauB_same_matrix :
    tauA.mA = tauB.mA ∧ tauA.mB = tauB.mB ∧ tauA.mC = tauB.mC ∧ tauA.mD = tauB.mD ∧
    tauA.mTr = 3 ∧ tauA.mDet = -2 ∧ tauA.mDisc = 17 := by decide

theorem tauA_cert_valid : verifyCert tauA tauACert = true := by decide

theorem tauB_cert_valid : verifyCert tauB tauBCert = true := by decide

/-- **FLAGSHIP THEOREM 2A (`tauA`: `0101 / 001` is infinitely 2-balanced)**. -/
theorem tauA_balance_infinite :
    ∀ i j n : Nat,
      Int.natAbs ((countOnes (tauA.wordFactor i n) : Int) -
                  (countOnes (tauA.wordFactor j n) : Int)) ≤ 2 :=
  stratCert_sound_balance tauA tauACert tauA_cert_valid

/-- **FLAGSHIP THEOREM 2B (`tauB`: `0110 / 001` is infinitely 4-balanced)**. -/
theorem tauB_balance_infinite :
    ∀ i j n : Nat,
      Int.natAbs ((countOnes (tauB.wordFactor i n) : Int) -
                  (countOnes (tauB.wordFactor j n) : Int)) ≤ 4 :=
  stratCert_sound_balance tauB tauBCert tauB_cert_valid

/-! ### 4.4 Strict Modular-Stratification Separation (`M = 3` beats unstratified `M = 1`!) -/

/-- Exact unstratified impossibility for `mu1`: `2*(U0 - L1) > 3 * D * Λ` in `ℤ[λ₂]`. -/
theorem mu1_unstrat_impossible :
    qLt mu1.mTr mu1.mDisc (qScale 9 mu1.mLambda) (qScale 2 (qSub (6, -1) (-9, 2))) = true ∧
    verifyCert mu1 mu1CertM1_failC2 = false := by decide

theorem mu1_cert_M3_valid : verifyCert mu1 mu1CertM3 = true := by decide

/-- **FLAGSHIP THEOREM 3A (Strict `M = 3` Oscillating Separation)**:
    Unstratified Rauzy diameter fails to prove 2-balance on `010101 / 001`,
    but `M = 3` modular stratification proves exact infinite 2-balance (`∀ i j n`). -/
theorem mu1_strat_balance_infinite :
    ∀ i j n : Nat,
      Int.natAbs ((countOnes (mu1.wordFactor i n) : Int) -
                  (countOnes (mu1.wordFactor j n) : Int)) ≤ 2 :=
  stratCert_sound_balance mu1 mu1CertM3 mu1_cert_M3_valid

/-- Exact unstratified impossibility for `mu2`: `2*(U0 - L1) > 5 * Λ` in `ℤ[λ₂]`. -/
theorem mu2_unstrat_impossible :
    qLt mu2.mTr mu2.mDisc (qScale 5 mu2.mLambda) (qScale 2 (qSub (2, 0) (-5, 1))) = true ∧
    verifyCert mu2 mu2CertM1_failC4 = false := by decide

theorem mu2_cert_M3_valid : verifyCert mu2 mu2CertM3 = true := by decide

/-- **FLAGSHIP THEOREM 3B (Strict `M = 3` Monotone Separation)**:
    Unstratified Rauzy diameter fails to prove 4-balance on `000001 / 100`,
    but `M = 3` modular stratification proves exact infinite 4-balance (`∀ i j n`). -/
theorem mu2_strat_balance_infinite :
    ∀ i j n : Nat,
      Int.natAbs ((countOnes (mu2.wordFactor i n) : Int) -
                  (countOnes (mu2.wordFactor j n) : Int)) ≤ 4 :=
  stratCert_sound_balance mu2 mu2CertM3 mu2_cert_M3_valid

/-! ### 4.5 Kernel-Checked Sharpness Witnesses (via Verified `O(log n)` Dumont–Thomas Oracle) -/

theorem sharp_witness_via_dt (m : Morphism)
    (hhead : m.w0.head? = some false) (h0 : 2 ≤ m.w0.length) (h1 : 1 ≤ m.w1.length)
    (d i j n expected : Nat)
    (hdi : i + n ≤ (m.dtStats d).1) (hdj : j + n ≤ (m.dtStats d).1)
    (heq : Int.natAbs (((m.dtTakeOnes d false (i + n) - m.dtTakeOnes d false i : Nat) : Int) -
                       ((m.dtTakeOnes d false (j + n) - m.dtTakeOnes d false j : Nat) : Int)) = expected) :
    Int.natAbs ((countOnes (m.wordFactor i n) : Int) -
                (countOnes (m.wordFactor j n) : Int)) = expected := by
  rw [m.dtTakeOnes_wordFactor hhead h0 h1 hdi, m.dtTakeOnes_wordFactor hhead h0 h1 hdj]
  exact heq

/-- Sharpness witnesses proving our certified bounds are **100% EXACT** on `σ_1, σ_2, σ_3, τ_A, τ_B, μ_1, μ_2`! -/
theorem sharp_sigma1 :
    Int.natAbs ((countOnes ((sigmaK 1).wordFactor 0 1) : Int) -
                (countOnes ((sigmaK 1).wordFactor 1 1) : Int)) = 1 :=
  sharp_witness_via_dt (sigmaK 1) rfl (by decide) (by decide) 2 0 1 1 1 (by decide) (by decide) (by decide)

theorem sharp_sigma2 :
    Int.natAbs ((countOnes ((sigmaK 2).wordFactor 6 7) : Int) -
                (countOnes ((sigmaK 2).wordFactor 13 7) : Int)) = 2 :=
  sharp_witness_via_dt (sigmaK 2) rfl (by decide) (by decide) 3 6 13 7 2 (by decide) (by decide) (by decide)

theorem sharp_sigma3 :
    Int.natAbs ((countOnes ((sigmaK 3).wordFactor 90 157) : Int) -
                (countOnes ((sigmaK 3).wordFactor 247 157) : Int)) = 3 :=
  sharp_witness_via_dt (sigmaK 3) rfl (by decide) (by decide) 5 90 247 157 3 (by decide) (by decide) (by decide)

theorem sharp_tauA :
    Int.natAbs ((countOnes (tauA.wordFactor 4 9) : Int) -
                (countOnes (tauA.wordFactor 13 9) : Int)) = 2 :=
  sharp_witness_via_dt tauA rfl (by decide) (by decide) 3 4 13 9 2 (by decide) (by decide) (by decide)

theorem sharp_tauB :
    Int.natAbs ((countOnes (tauB.wordFactor 39 73) : Int) -
                (countOnes (tauB.wordFactor 137 73) : Int)) = 4 :=
  sharp_witness_via_dt tauB rfl (by decide) (by decide) 5 39 137 73 4 (by decide) (by decide) (by decide)

theorem sharp_mu1 :
    Int.natAbs ((countOnes (mu1.wordFactor 6 11) : Int) -
                (countOnes (mu1.wordFactor 26 11) : Int)) = 2 :=
  sharp_witness_via_dt mu1 rfl (by decide) (by decide) 3 6 26 11 2 (by decide) (by decide) (by decide)

theorem sharp_mu2 :
    Int.natAbs ((countOnes (mu2.wordFactor 166 101) : Int) -
                (countOnes (mu2.wordFactor 4805 101) : Int)) = 4 :=
  sharp_witness_via_dt mu2 rfl (by decide) (by decide) 6 166 4805 101 4 (by decide) (by decide) (by decide)

/-! ### 4.6 Hostile Mutation & Non-Vacuity Tests -/

/-- Non-vacuity witness: the engine's hypotheses are constructively inhabited across
    multiple distinct regimes (monotone, oscillating, non-unimodular, modularly stratified). -/
theorem non_vacuity_witnesses :
    ∃ (m : Morphism) (c : StratCert), verifyCert m c = true ∧ c.M = 3 ∧ c.D = 3 ∧ c.C = 2 :=
  ⟨mu1, mu1CertM3, mu1_cert_M3_valid, rfl, rfl, rfl⟩

/-- Negative / hostile mutation tests: `verifyCert` rejects over-tight `C`, corrupted endpoints,
    wrong modulus, and non-Pisot morphisms (`0111 / 001` has `|λ₂| > 1`). -/
theorem hostile_mutation_rejections :
    verifyCert tauA { tauACert with C := 1 } = false ∧
    verifyCert tauB { tauBCert with C := 3 } = false ∧
    verifyCert mu1 { mu1CertM3 with C := 1 } = false ∧
    verifyCert mu2 { mu2CertM3 with C := 3 } = false ∧
    verifyCert mu1 { mu1CertM3 with L0 := (-5, -1) } = false ∧
    verifyCert mu2 { mu2CertM3 with U0 := (1, 0) } = false ∧
    verifyCert { w0 := [false, true, true, true], w1 := [false, false, true] }
               { D := 1, M := 1, C := 10, L0 := (-10, 0), U0 := (10, 0),
                 L1 := (-10, 0), U1 := (10, 0), Lres := [(-10, 0)], Ures := [(10, 0)] } = false := by
  decide

end MSQRPAIE
