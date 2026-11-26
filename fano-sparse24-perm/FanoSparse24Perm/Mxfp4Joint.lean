/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FanoSparse24Perm.RatOrder

/-!
# Theorem 2: Joint `k:m + MXFP4` (`B = 32`) Worst-Case EF21 Contraction & Anchor-Group Dilution

Proves universally over all rational blocks `x ∈ [0, 3]^{32}` with anchor `x 0 0 = 3` that:
1. `4:8 + MXFP4` (`g = 4, k = 4, m = 8`) satisfies the exact EF21 contraction `α = 18 / 37`
   (`blockMxfp4ErrSq ≤ (1 - 18 / 37) * blockMxfp4Energy`), with exact attainment witness
   (anchor group all `3`, off-anchor groups all `5 / 2`).
2. `2:4 + MXFP4` (`g = 8, k = 2, m = 4`) satisfies the exact EF21 contraction `α = 72 / 151`
   (`blockMxfp4ErrSq ≤ (1 - 72 / 151) * blockMxfp4Energy`), with exact attainment witness
   (anchor group all `3`, off-anchor groups all `1 / 4`).
3. Strict anchor-group dilution dominance: `72 / 151 < 18 / 37` (gap `54 / 5587 > 0`).
4. Exact closed-form dense max-abs Ternary contraction law `α(Ternary, B) = 4 / (B + 3)`
   for all `B ≥ 1` (`4 / 35` at `B = 32`), with exact attainment witness `(1, 1/2, ..., 1/2)`.
-/

namespace FanoSparse24Perm

/-! ### Convex Quadratic Interval Lemma -/

theorem quad_le_of_endpoints {c p r a b u M : Rat}
    (hc : (0 : Rat) ≤ c) (hab : a < b) (hau : a ≤ u) (hub : u ≤ b)
    (haM : c * (a * a) + p * a + r ≤ M) (hbM : c * (b * b) + p * b + r ≤ M) :
    c * (u * u) + p * u + r ≤ M := by
  have hba_pos : (0 : Rat) < b - a := rat_sub_pos hab
  have hua_nn : (0 : Rat) ≤ u - a := rat_sub_nonneg hau
  have hbu_nn : (0 : Rat) ≤ b - u := rat_sub_nonneg hub
  have hquad_nn : (0 : Rat) ≤ c * (u - a) * (b - u) :=
    Rat.mul_nonneg (Rat.mul_nonneg hc hua_nn) hbu_nn
  have h1 : (0 : Rat) ≤ (b - u) * (M - (c * (a * a) + p * a + r)) :=
    Rat.mul_nonneg hbu_nn (rat_sub_nonneg haM)
  have h2 : (0 : Rat) ≤ (u - a) * (M - (c * (b * b) + p * b + r)) :=
    Rat.mul_nonneg hua_nn (rat_sub_nonneg hbM)
  have h3 : (0 : Rat) ≤ (b - a) * (c * (u - a) * (b - u)) :=
    Rat.mul_nonneg (Rat.le_of_lt hba_pos) hquad_nn
  have hsum : (0 : Rat) ≤
      (b - u) * (M - (c * (a * a) + p * a + r)) +
      (u - a) * (M - (c * (b * b) + p * b + r)) +
      (b - a) * (c * (u - a) * (b - u)) :=
    rat_add_nonneg (rat_add_nonneg h1 h2) h3
  have hid :
      (b - u) * (M - (c * (a * a) + p * a + r)) +
      (u - a) * (M - (c * (b * b) + p * b + r)) +
      (b - a) * (c * (u - a) * (b - u)) =
      (M - (c * (u * u) + p * u + r)) * (b - a) := by
    grind
  rw [hid] at hsum
  have hle : (0 : Rat) ≤ M - (c * (u * u) + p * u + r) := by
    apply rat_le_of_mul_pos_right hba_pos
    rw [Rat.zero_mul]
    exact hsum
  exact rat_le_of_sub_nonneg hle

/-! ### Dinkelbach Potential `h(lam, y) = e2m1ErrSq y - lam * y^2` -/

def dinkH (lam y : Rat) : Rat :=
  e2m1ErrSq y - lam * (y * y)

theorem quad_piece_antitone {lam lvl u w : Rat}
    (hstep : (1 - lam) * (u + w) ≤ 2 * lvl) (huw : u ≤ w) :
    ((w - lvl) * (w - lvl) - lam * (w * w)) ≤
      ((u - lvl) * (u - lvl) - lam * (u * u)) := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ w - u := rat_sub_nonneg huw
  have h2 : (0 : Rat) ≤ 2 * lvl - (1 - lam) * (u + w) := rat_sub_nonneg hstep
  have hprod : (0 : Rat) ≤ (w - u) * (2 * lvl - (1 - lam) * (u + w)) := Rat.mul_nonneg h1 h2
  have hid :
      ((u - lvl) * (u - lvl) - lam * (u * u)) - ((w - lvl) * (w - lvl) - lam * (w * w)) =
      (w - u) * (2 * lvl - (1 - lam) * (u + w)) := by
    grind
  rw [hid]
  exact hprod

theorem dinkH_antitone_on_tail {lam u w : Rat}
    (hlam1 : (1 / 3 : Rat) ≤ lam) (hlam2 : lam ≤ 1)
    (hu : (1 / 4 : Rat) ≤ u) (huw : u ≤ w) (hw : w ≤ 3) :
    dinkH lam w ≤ dinkH lam u := by
  have hnn : (0 : Rat) ≤ 1 - lam := rat_sub_nonneg hlam2
  have hpiece1 : ∀ a b : Rat, (1 / 4 : Rat) ≤ a → a ≤ b → b ≤ 3 / 4 →
      ((b - 1 / 2) * (b - 1 / 2) - lam * (b * b)) ≤
      ((a - 1 / 2) * (a - 1 / 2) - lam * (a * a)) := by
    intro a b _ hab hb
    apply quad_piece_antitone _ hab
    have hs : a + b ≤ 3 / 2 := by
      have := rat_add_le_add (Rat.le_trans hab hb) hb; grind
    have h1 : (1 - lam) * (a + b) ≤ (1 - lam) * (3 / 2) :=
      rat_mul_le_mul_of_nonneg_left hs hnn
    have h2 : (1 - lam) * (3 / 2) ≤ 2 * (1 / 2 : Rat) := by grind
    exact Rat.le_trans h1 h2
  have hpiece2 : ∀ a b : Rat, (3 / 4 : Rat) ≤ a → a ≤ b → b ≤ 5 / 4 →
      ((b - 1) * (b - 1) - lam * (b * b)) ≤
      ((a - 1) * (a - 1) - lam * (a * a)) := by
    intro a b _ hab hb
    apply quad_piece_antitone _ hab
    have hs : a + b ≤ 5 / 2 := by
      have := rat_add_le_add (Rat.le_trans hab hb) hb; grind
    have h1 : (1 - lam) * (a + b) ≤ (1 - lam) * (5 / 2) :=
      rat_mul_le_mul_of_nonneg_left hs hnn
    have h2 : (1 - lam) * (5 / 2) ≤ 2 * (1 : Rat) := by grind
    exact Rat.le_trans h1 h2
  have hpiece3 : ∀ a b : Rat, (5 / 4 : Rat) ≤ a → a ≤ b → b ≤ 7 / 4 →
      ((b - 3 / 2) * (b - 3 / 2) - lam * (b * b)) ≤
      ((a - 3 / 2) * (a - 3 / 2) - lam * (a * a)) := by
    intro a b _ hab hb
    apply quad_piece_antitone _ hab
    have hs : a + b ≤ 7 / 2 := by
      have := rat_add_le_add (Rat.le_trans hab hb) hb; grind
    have h1 : (1 - lam) * (a + b) ≤ (1 - lam) * (7 / 2) :=
      rat_mul_le_mul_of_nonneg_left hs hnn
    have h2 : (1 - lam) * (7 / 2) ≤ 2 * (3 / 2 : Rat) := by grind
    exact Rat.le_trans h1 h2
  have hpiece4 : ∀ a b : Rat, (7 / 4 : Rat) ≤ a → a ≤ b → b ≤ 5 / 2 →
      ((b - 2) * (b - 2) - lam * (b * b)) ≤
      ((a - 2) * (a - 2) - lam * (a * a)) := by
    intro a b _ hab hb
    apply quad_piece_antitone _ hab
    have hs : a + b ≤ 5 := by
      have := rat_add_le_add (Rat.le_trans hab hb) hb; grind
    have h1 : (1 - lam) * (a + b) ≤ (1 - lam) * 5 :=
      rat_mul_le_mul_of_nonneg_left hs hnn
    have h2 : (1 - lam) * 5 ≤ 2 * (2 : Rat) := by grind
    exact Rat.le_trans h1 h2
  have hpiece5 : ∀ a b : Rat, (5 / 2 : Rat) ≤ a → a ≤ b → b ≤ 3 →
      ((b - 3) * (b - 3) - lam * (b * b)) ≤
      ((a - 3) * (a - 3) - lam * (a * a)) := by
    intro a b _ hab hb
    apply quad_piece_antitone _ hab
    have hs : a + b ≤ 6 := by
      have := rat_add_le_add (Rat.le_trans hab hb) hb; grind
    have h1 : (1 - lam) * (a + b) ≤ (1 - lam) * 6 :=
      rat_mul_le_mul_of_nonneg_left hs hnn
    have h2 : (1 - lam) * 6 ≤ 2 * (3 : Rat) := by grind
    exact Rat.le_trans h1 h2
  have eval1 : ∀ y : Rat, (1 / 4 : Rat) ≤ y → y ≤ 3 / 4 →
      dinkH lam y = (y - 1 / 2) * (y - 1 / 2) - lam * (y * y) := by
    intro y hy1 hy2
    unfold dinkH e2m1ErrSq
    by_cases h14 : y ≤ 1 / 4
    · have heq : y = 1 / 4 := Rat.le_antisymm h14 hy1
      simp [h14]; rw [heq]; grind
    · simp [h14, hy2]
  have eval2 : ∀ y : Rat, (3 / 4 : Rat) ≤ y → y ≤ 5 / 4 →
      dinkH lam y = (y - 1) * (y - 1) - lam * (y * y) := by
    intro y hy1 hy2
    unfold dinkH e2m1ErrSq
    by_cases h34 : y ≤ 3 / 4
    · have heq : y = 3 / 4 := Rat.le_antisymm h34 hy1
      have h14 : ¬ y ≤ 1 / 4 := by rw [heq]; grind
      simp [h14, h34]; rw [heq]; grind
    · have h14 : ¬ y ≤ 1 / 4 := fun h => h34 (Rat.le_trans h (by grind))
      simp [h14, h34, hy2]
  have eval3 : ∀ y : Rat, (5 / 4 : Rat) ≤ y → y ≤ 7 / 4 →
      dinkH lam y = (y - 3 / 2) * (y - 3 / 2) - lam * (y * y) := by
    intro y hy1 hy2
    unfold dinkH e2m1ErrSq
    by_cases h54 : y ≤ 5 / 4
    · have heq : y = 5 / 4 := Rat.le_antisymm h54 hy1
      have h14 : ¬ y ≤ 1 / 4 := by rw [heq]; grind
      have h34 : ¬ y ≤ 3 / 4 := by rw [heq]; grind
      simp [h14, h34, h54]; rw [heq]; grind
    · have h34 : ¬ y ≤ 3 / 4 := fun h => h54 (Rat.le_trans h (by grind))
      have h14 : ¬ y ≤ 1 / 4 := fun h => h54 (Rat.le_trans h (by grind))
      simp [h14, h34, h54, hy2]
  have eval4 : ∀ y : Rat, (7 / 4 : Rat) ≤ y → y ≤ 5 / 2 →
      dinkH lam y = (y - 2) * (y - 2) - lam * (y * y) := by
    intro y hy1 hy2
    unfold dinkH e2m1ErrSq
    by_cases h74 : y ≤ 7 / 4
    · have heq : y = 7 / 4 := Rat.le_antisymm h74 hy1
      have h14 : ¬ y ≤ 1 / 4 := by rw [heq]; grind
      have h34 : ¬ y ≤ 3 / 4 := by rw [heq]; grind
      have h54 : ¬ y ≤ 5 / 4 := by rw [heq]; grind
      simp [h14, h34, h54, h74]; rw [heq]; grind
    · have h54 : ¬ y ≤ 5 / 4 := fun h => h74 (Rat.le_trans h (by grind))
      have h34 : ¬ y ≤ 3 / 4 := fun h => h74 (Rat.le_trans h (by grind))
      have h14 : ¬ y ≤ 1 / 4 := fun h => h74 (Rat.le_trans h (by grind))
      simp [h14, h34, h54, h74, hy2]
  have eval5 : ∀ y : Rat, (5 / 2 : Rat) ≤ y → y ≤ 3 →
      dinkH lam y = (y - 3) * (y - 3) - lam * (y * y) := by
    intro y hy1 _
    unfold dinkH e2m1ErrSq
    by_cases h52 : y ≤ 5 / 2
    · have heq : y = 5 / 2 := Rat.le_antisymm h52 hy1
      have h14 : ¬ y ≤ 1 / 4 := by rw [heq]; grind
      have h34 : ¬ y ≤ 3 / 4 := by rw [heq]; grind
      have h54 : ¬ y ≤ 5 / 4 := by rw [heq]; grind
      have h74 : ¬ y ≤ 7 / 4 := by rw [heq]; grind
      simp [h14, h34, h54, h74, h52]; rw [heq]; grind
    · have h74 : ¬ y ≤ 7 / 4 := fun h => h52 (Rat.le_trans h (by grind))
      have h54 : ¬ y ≤ 5 / 4 := fun h => h52 (Rat.le_trans h (by grind))
      have h34 : ¬ y ≤ 3 / 4 := fun h => h52 (Rat.le_trans h (by grind))
      have h14 : ¬ y ≤ 1 / 4 := fun h => h52 (Rat.le_trans h (by grind))
      simp [h14, h34, h54, h74, h52]
  have h12 : dinkH lam (3 / 4) ≤ dinkH lam (1 / 4) := by
    rw [eval1 (3/4) (by grind) Rat.le_refl, eval1 (1/4) Rat.le_refl (by grind)]
    exact hpiece1 _ _ Rat.le_refl (by grind) Rat.le_refl
  have h23 : dinkH lam (5 / 4) ≤ dinkH lam (3 / 4) := by
    rw [eval2 (5/4) (by grind) Rat.le_refl, eval2 (3/4) Rat.le_refl (by grind)]
    exact hpiece2 _ _ Rat.le_refl (by grind) Rat.le_refl
  have h34 : dinkH lam (7 / 4) ≤ dinkH lam (5 / 4) := by
    rw [eval3 (7/4) (by grind) Rat.le_refl, eval3 (5/4) Rat.le_refl (by grind)]
    exact hpiece3 _ _ Rat.le_refl (by grind) Rat.le_refl
  have h45 : dinkH lam (5 / 2) ≤ dinkH lam (7 / 4) := by
    rw [eval4 (5/2) (by grind) Rat.le_refl, eval4 (7/4) Rat.le_refl (by grind)]
    exact hpiece4 _ _ Rat.le_refl (by grind) Rat.le_refl
  have step_le : ∀ a b : Rat, (1 / 4 : Rat) ≤ a → a ≤ b → b ≤ 3 →
      (b ≤ 3 / 4 ∨ (3 / 4 ≤ a ∧ b ≤ 5 / 4) ∨ (5 / 4 ≤ a ∧ b ≤ 7 / 4) ∨
       (7 / 4 ≤ a ∧ b ≤ 5 / 2) ∨ 5 / 2 ≤ a) → dinkH lam b ≤ dinkH lam a := by
    intro a b ha hab hb hcase
    rcases hcase with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · rw [eval1 b (Rat.le_trans ha hab) h, eval1 a ha (Rat.le_trans hab h)]
      exact hpiece1 a b ha hab h
    · rw [eval2 b (Rat.le_trans h1 hab) h2, eval2 a h1 (Rat.le_trans hab h2)]
      exact hpiece2 a b h1 hab h2
    · rw [eval3 b (Rat.le_trans h1 hab) h2, eval3 a h1 (Rat.le_trans hab h2)]
      exact hpiece3 a b h1 hab h2
    · rw [eval4 b (Rat.le_trans h1 hab) h2, eval4 a h1 (Rat.le_trans hab h2)]
      exact hpiece4 a b h1 hab h2
    · rw [eval5 b (Rat.le_trans h hab) hb, eval5 a h (Rat.le_trans hab hb)]
      exact hpiece5 a b h hab hb
  by_cases hu1 : u ≤ 3 / 4
  · by_cases hw1 : w ≤ 3 / 4
    · exact step_le u w hu huw hw (Or.inl hw1)
    · have hw1' : (3 / 4 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw1)
      have ha : dinkH lam (3 / 4) ≤ dinkH lam u := step_le u (3/4) hu hu1 (by grind) (Or.inl Rat.le_refl)
      by_cases hw2 : w ≤ 5 / 4
      · exact Rat.le_trans (step_le (3/4) w (by grind) hw1' hw (Or.inr (Or.inl ⟨Rat.le_refl, hw2⟩))) ha
      · have hw2' : (5 / 4 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw2)
        have hb := Rat.le_trans h23 ha
        by_cases hw3 : w ≤ 7 / 4
        · exact Rat.le_trans (step_le (5/4) w (by grind) hw2' hw (Or.inr (Or.inr (Or.inl ⟨Rat.le_refl, hw3⟩)))) hb
        · have hw3' : (7 / 4 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw3)
          have hc := Rat.le_trans h34 hb
          by_cases hw4 : w ≤ 5 / 2
          · exact Rat.le_trans (step_le (7/4) w (by grind) hw3' hw (Or.inr (Or.inr (Or.inr (Or.inl ⟨Rat.le_refl, hw4⟩))))) hc
          · have hw4' : (5 / 2 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw4)
            have hd := Rat.le_trans h45 hc
            exact Rat.le_trans (step_le (5/2) w (by grind) hw4' hw (Or.inr (Or.inr (Or.inr (Or.inr Rat.le_refl))))) hd
  · have hu1' : (3 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu1)
    by_cases hu2 : u ≤ 5 / 4
    · by_cases hw2 : w ≤ 5 / 4
      · exact step_le u w hu huw hw (Or.inr (Or.inl ⟨hu1', hw2⟩))
      · have hw2' : (5 / 4 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw2)
        have ha : dinkH lam (5 / 4) ≤ dinkH lam u :=
          step_le u (5/4) hu hu2 (by grind) (Or.inr (Or.inl ⟨hu1', Rat.le_refl⟩))
        by_cases hw3 : w ≤ 7 / 4
        · exact Rat.le_trans (step_le (5/4) w (by grind) hw2' hw (Or.inr (Or.inr (Or.inl ⟨Rat.le_refl, hw3⟩)))) ha
        · have hw3' : (7 / 4 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw3)
          have hb := Rat.le_trans h34 ha
          by_cases hw4 : w ≤ 5 / 2
          · exact Rat.le_trans (step_le (7/4) w (by grind) hw3' hw (Or.inr (Or.inr (Or.inr (Or.inl ⟨Rat.le_refl, hw4⟩))))) hb
          · have hw4' : (5 / 2 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw4)
            have hc := Rat.le_trans h45 hb
            exact Rat.le_trans (step_le (5/2) w (by grind) hw4' hw (Or.inr (Or.inr (Or.inr (Or.inr Rat.le_refl))))) hc
    · have hu2' : (5 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu2)
      by_cases hu3 : u ≤ 7 / 4
      · by_cases hw3 : w ≤ 7 / 4
        · exact step_le u w hu huw hw (Or.inr (Or.inr (Or.inl ⟨hu2', hw3⟩)))
        · have hw3' : (7 / 4 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw3)
          have ha : dinkH lam (7 / 4) ≤ dinkH lam u :=
            step_le u (7/4) hu hu3 (by grind) (Or.inr (Or.inr (Or.inl ⟨hu2', Rat.le_refl⟩)))
          by_cases hw4 : w ≤ 5 / 2
          · exact Rat.le_trans (step_le (7/4) w (by grind) hw3' hw (Or.inr (Or.inr (Or.inr (Or.inl ⟨Rat.le_refl, hw4⟩))))) ha
          · have hw4' : (5 / 2 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw4)
            have hb := Rat.le_trans h45 ha
            exact Rat.le_trans (step_le (5/2) w (by grind) hw4' hw (Or.inr (Or.inr (Or.inr (Or.inr Rat.le_refl))))) hb
      · have hu3' : (7 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu3)
        by_cases hu4 : u ≤ 5 / 2
        · by_cases hw4 : w ≤ 5 / 2
          · exact step_le u w hu huw hw (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu3', hw4⟩))))
          · have hw4' : (5 / 2 : Rat) ≤ w := Rat.le_of_lt (Rat.not_le.mp hw4)
            have ha : dinkH lam (5 / 2) ≤ dinkH lam u :=
              step_le u (5/2) hu hu4 (by grind) (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu3', Rat.le_refl⟩))))
            exact Rat.le_trans (step_le (5/2) w (by grind) hw4' hw (Or.inr (Or.inr (Or.inr (Or.inr Rat.le_refl))))) ha
        · have hu4' : (5 / 2 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu4)
          exact step_le u w hu huw hw (Or.inr (Or.inr (Or.inr (Or.inr hu4'))))

theorem dinkH_le_quarter {lam y : Rat}
    (hlam1 : (1 / 3 : Rat) ≤ lam) (hlam2 : lam ≤ 1)
    (hy0 : (0 : Rat) ≤ y) (hy3 : y ≤ 3) :
    dinkH lam y ≤ (1 - lam) / 16 := by
  by_cases h14 : y ≤ 1 / 4
  · unfold dinkH e2m1ErrSq
    simp [h14]
    have hsq : y * y ≤ (1 / 4 : Rat) * (1 / 4) := rat_sq_le_sq hy0 h14
    have hnn : (0 : Rat) ≤ 1 - lam := rat_sub_nonneg hlam2
    have hmul := rat_mul_le_mul_of_nonneg_left hsq hnn
    have hl : y * y - lam * (y * y) = (1 - lam) * (y * y) := by grind
    have hr : (1 - lam) * ((1 / 4 : Rat) * (1 / 4)) = (1 - lam) / 16 := by grind
    rw [hl, ← hr]
    exact hmul
  · have hy14 : (1 / 4 : Rat) ≤ y := Rat.le_of_lt (Rat.not_le.mp h14)
    have hanti := dinkH_antitone_on_tail hlam1 hlam2 Rat.le_refl hy14 hy3
    have hq : dinkH lam (1 / 4) = (1 - lam) / 16 := by
      unfold dinkH e2m1ErrSq
      simp; grind
    rw [← hq]
    exact hanti

/-! ### Piecewise Convex Quadratic Envelope Bound on `[1/4, 3]` -/

theorem e2m1_combo_le_on_tail {A B u M : Rat}
    (hAB : (0 : Rat) ≤ A + B)
    (hu1 : (1 / 4 : Rat) ≤ u) (hu3 : u ≤ 3)
    (h14 : A * (1 / 16) + B * (1 / 16) ≤ M)
    (h34 : A * (1 / 16) + B * (9 / 16) ≤ M)
    (h54 : A * (1 / 16) + B * (25 / 16) ≤ M)
    (h74 : A * (1 / 16) + B * (49 / 16) ≤ M)
    (h52 : A * (1 / 4) + B * (25 / 4) ≤ M)
    (h3  : B * 9 ≤ M) :
    A * e2m1ErrSq u + B * (u * u) ≤ M := by
  by_cases c1 : u ≤ 1 / 4
  · have heq : u = 1 / 4 := Rat.le_antisymm c1 hu1
    rw [heq]; unfold e2m1ErrSq
    simp
    have : A * ((1 / 4 : Rat) * (1 / 4)) + B * ((1 / 4 : Rat) * (1 / 4)) =
        A * (1 / 16) + B * (1 / 16) := by grind
    rw [this]; exact h14
  · by_cases c2 : u ≤ 3 / 4
    · unfold e2m1ErrSq; simp [c1, c2]
      have hrewrite : A * ((u - 1 / 2) * (u - 1 / 2)) + B * (u * u) =
          (A + B) * (u * u) + (-A) * u + A * (1 / 4) := by grind
      rw [hrewrite]
      apply quad_le_of_endpoints hAB (by grind : (1 / 4 : Rat) < 3 / 4) hu1 c2
      · have : (A + B) * ((1 / 4 : Rat) * (1 / 4)) + (-A) * (1 / 4) + A * (1 / 4) =
            A * (1 / 16) + B * (1 / 16) := by grind
        rw [this]; exact h14
      · have : (A + B) * ((3 / 4 : Rat) * (3 / 4)) + (-A) * (3 / 4) + A * (1 / 4) =
            A * (1 / 16) + B * (9 / 16) := by grind
        rw [this]; exact h34
    · have hu2 : (3 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp c2)
      by_cases c3 : u ≤ 5 / 4
      · unfold e2m1ErrSq; simp [c1, c2, c3]
        have hrewrite : A * ((u - 1) * (u - 1)) + B * (u * u) =
            (A + B) * (u * u) + (-2 * A) * u + A := by grind
        rw [hrewrite]
        apply quad_le_of_endpoints hAB (by grind : (3 / 4 : Rat) < 5 / 4) hu2 c3
        · have : (A + B) * ((3 / 4 : Rat) * (3 / 4)) + (-2 * A) * (3 / 4) + A =
              A * (1 / 16) + B * (9 / 16) := by grind
          rw [this]; exact h34
        · have : (A + B) * ((5 / 4 : Rat) * (5 / 4)) + (-2 * A) * (5 / 4) + A =
              A * (1 / 16) + B * (25 / 16) := by grind
          rw [this]; exact h54
      · have hu3' : (5 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp c3)
        by_cases c4 : u ≤ 7 / 4
        · unfold e2m1ErrSq; simp [c1, c2, c3, c4]
          have hrewrite : A * ((u - 3 / 2) * (u - 3 / 2)) + B * (u * u) =
              (A + B) * (u * u) + (-3 * A) * u + A * (9 / 4) := by grind
          rw [hrewrite]
          apply quad_le_of_endpoints hAB (by grind : (5 / 4 : Rat) < 7 / 4) hu3' c4
          · have : (A + B) * ((5 / 4 : Rat) * (5 / 4)) + (-3 * A) * (5 / 4) + A * (9 / 4) =
                A * (1 / 16) + B * (25 / 16) := by grind
            rw [this]; exact h54
          · have : (A + B) * ((7 / 4 : Rat) * (7 / 4)) + (-3 * A) * (7 / 4) + A * (9 / 4) =
                A * (1 / 16) + B * (49 / 16) := by grind
            rw [this]; exact h74
        · have hu4' : (7 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp c4)
          by_cases c5 : u ≤ 5 / 2
          · unfold e2m1ErrSq; simp [c1, c2, c3, c4, c5]
            have hrewrite : A * ((u - 2) * (u - 2)) + B * (u * u) =
                (A + B) * (u * u) + (-4 * A) * u + A * 4 := by grind
            rw [hrewrite]
            apply quad_le_of_endpoints hAB (by grind : (7 / 4 : Rat) < 5 / 2) hu4' c5
            · have : (A + B) * ((7 / 4 : Rat) * (7 / 4)) + (-4 * A) * (7 / 4) + A * 4 =
                  A * (1 / 16) + B * (49 / 16) := by grind
              rw [this]; exact h74
            · have : (A + B) * ((5 / 2 : Rat) * (5 / 2)) + (-4 * A) * (5 / 2) + A * 4 =
                  A * (1 / 4) + B * (25 / 4) := by grind
              rw [this]; exact h52
          · have hu5' : (5 / 2 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp c5)
            unfold e2m1ErrSq; simp [c1, c2, c3, c4, c5]
            have hrewrite : A * ((u - 3) * (u - 3)) + B * (u * u) =
                (A + B) * (u * u) + (-6 * A) * u + A * 9 := by grind
            rw [hrewrite]
            apply quad_le_of_endpoints hAB (by grind : (5 / 2 : Rat) < 3) hu5' hu3
            · have : (A + B) * ((5 / 2 : Rat) * (5 / 2)) + (-6 * A) * (5 / 2) + A * 9 =
                  A * (1 / 4) + B * (25 / 4) := by grind
              rw [this]; exact h52
            · have : (A + B) * ((3 : Rat) * 3) + (-6 * A) * 3 + A * 9 = B * 9 := by grind
              rw [this]; exact h3

theorem groupMxfp4_dink_decomp {k m : Nat} (hkm : k ≤ m) (lam : Rat) (a : Nat → Rat) :
    groupMxfp4ErrSq k m a - lam * blockEnergy m a =
      sumRange k (fun i => dinkH lam (a i)) +
      sumRange (m - k) (fun j => (1 - lam) * (a (k + j) * a (k + j))) := by
  unfold groupMxfp4ErrSq blockEnergy dinkH
  have hm : k + (m - k) = m := Nat.add_sub_of_le hkm
  have hsp := sumRange_split k (m - k) (fun i => a i * a i)
  rw [hm] at hsp
  rw [hsp]
  have h1 : sumRange k (fun i => e2m1ErrSq (a i) - lam * (a i * a i)) =
      sumRange k (fun i => e2m1ErrSq (a i)) - lam * sumRange k (fun i => a i * a i) := by
    have ha : sumRange k (fun i => e2m1ErrSq (a i) - lam * (a i * a i)) +
        lam * sumRange k (fun i => a i * a i) = sumRange k (fun i => e2m1ErrSq (a i)) := by
      rw [← sumRange_mul_left, ← sumRange_add]
      apply sumRange_congr; intro i _; grind
    grind
  have h2 : sumRange (m - k) (fun j => (1 - lam) * (a (k + j) * a (k + j))) =
      sumRange (m - k) (fun j => a (k + j) * a (k + j)) -
      lam * sumRange (m - k) (fun j => a (k + j) * a (k + j)) := by
    rw [sumRange_mul_left]; grind
  rw [h1, h2]
  grind

/-! ### `4:8 + MXFP4` (`λ = 19 / 37`, `α = 18 / 37`) -/

theorem group_other_48_mxfp4 {a : Nat → Rat}
    (ha : NonIncreasingMags 8 a) (hb : ∀ i : Nat, i < 8 → a i ≤ 3) :
    groupMxfp4ErrSq 4 8 a - (19 / 37 : Rat) * blockEnergy 8 a ≤ 12 / 37 := by
  rw [groupMxfp4_dink_decomp (by decide : 4 ≤ 8)]
  have hlam1 : (1 / 3 : Rat) ≤ 19 / 37 := by grind
  have hlam2 : (19 / 37 : Rat) ≤ 1 := by grind
  have h1ml : (0 : Rat) ≤ 1 - (19 / 37 : Rat) := by grind
  let u := a 3
  have hu3 : u ≤ 3 := hb 3 (by decide)
  by_cases hu14 : u ≤ 1 / 4
  · have hkept : sumRange 4 (fun i => dinkH (19 / 37) (a i)) ≤
        (4 : Rat) * ((1 - (19 / 37 : Rat)) / 16) := by
      have h := sumRange_le_sumRange (n := 4) (g := fun _ => (1 - (19 / 37 : Rat)) / 16)
        (fun i hi => dinkH_le_quarter hlam1 hlam2 (ha.1 i (by omega)) (hb i (by omega)))
      rw [sumRange_const] at h; exact h
    have hpruned : sumRange 4 (fun j => (1 - (19 / 37 : Rat)) * (a (4 + j) * a (4 + j))) ≤
        (4 : Rat) * ((1 - (19 / 37 : Rat)) * ((1 / 4 : Rat) * (1 / 4))) := by
      have h := sumRange_le_sumRange (n := 4) (g := fun _ => (1 - (19 / 37 : Rat)) * ((1 / 4 : Rat) * (1 / 4)))
        (fun j hj => by
          have hle : a (4 + j) ≤ 1 / 4 := Rat.le_trans (ha.2 3 (4 + j) (by omega) (by omega)) hu14
          exact rat_mul_le_mul_of_nonneg_left (rat_sq_le_sq (ha.1 (4 + j) (by omega)) hle) h1ml)
      rw [sumRange_const] at h; exact h
    exact Rat.le_trans (rat_add_le_add hkept hpruned) (by grind)
  · have hu14' : (1 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu14)
    have hkept : sumRange 4 (fun i => dinkH (19 / 37) (a i)) ≤ (4 : Rat) * dinkH (19 / 37) u := by
      have h := sumRange_le_sumRange (n := 4) (g := fun _ => dinkH (19 / 37) u)
        (fun i hi => dinkH_antitone_on_tail hlam1 hlam2 hu14' (ha.2 i 3 (by omega) (by decide)) (hb i (by omega)))
      rw [sumRange_const] at h; exact h
    have hpruned : sumRange 4 (fun j => (1 - (19 / 37 : Rat)) * (a (4 + j) * a (4 + j))) ≤
        (4 : Rat) * ((1 - (19 / 37 : Rat)) * (u * u)) := by
      have h := sumRange_le_sumRange (n := 4) (g := fun _ => (1 - (19 / 37 : Rat)) * (u * u))
        (fun j hj => rat_mul_le_mul_of_nonneg_left
          (rat_sq_le_sq (ha.1 (4 + j) (by omega)) (ha.2 3 (4 + j) (by omega) (by omega))) h1ml)
      rw [sumRange_const] at h; exact h
    have hsum := rat_add_le_add hkept hpruned
    have hrew : (4 : Rat) * dinkH (19 / 37) u + (4 : Rat) * ((1 - (19 / 37 : Rat)) * (u * u)) =
        (4 : Rat) * e2m1ErrSq u + (-4 / 37 : Rat) * (u * u) := by
      unfold dinkH; grind
    rw [hrew] at hsum
    refine Rat.le_trans hsum ?_
    exact e2m1_combo_le_on_tail (by grind) hu14' hu3
      (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)

theorem group_anchor_48_mxfp4 {a : Nat → Rat}
    (ha : NonIncreasingMags 8 a) (hb : ∀ i : Nat, i < 8 → a i ≤ 3) (h0 : a 0 = 3) :
    groupMxfp4ErrSq 4 8 a - (19 / 37 : Rat) * blockEnergy 8 a ≤ -36 / 37 := by
  rw [groupMxfp4_dink_decomp (by decide : 4 ≤ 8)]
  have hlam1 : (1 / 3 : Rat) ≤ 19 / 37 := by grind
  have hlam2 : (19 / 37 : Rat) ≤ 1 := by grind
  have h1ml : (0 : Rat) ≤ 1 - (19 / 37 : Rat) := by grind
  have hhead : sumRange 4 (fun i => dinkH (19 / 37) (a i)) =
      dinkH (19 / 37) 3 + sumRange 3 (fun j => dinkH (19 / 37) (a (1 + j))) := by
    have hsp := sumRange_split 1 3 (fun i => dinkH (19 / 37) (a i))
    have h1 : sumRange 1 (fun i => dinkH (19 / 37) (a i)) = dinkH (19 / 37) 3 := by
      simp only [sumRange, h0]; grind
    rw [hsp, h1]
  have hd3 : dinkH (19 / 37) 3 = -171 / 37 := by
    unfold dinkH e2m1ErrSq
    have c1 : ¬ (3 : Rat) ≤ 1 / 4 := by grind
    have c2 : ¬ (3 : Rat) ≤ 3 / 4 := by grind
    have c3 : ¬ (3 : Rat) ≤ 5 / 4 := by grind
    have c4 : ¬ (3 : Rat) ≤ 7 / 4 := by grind
    have c5 : ¬ (3 : Rat) ≤ 5 / 2 := by grind
    simp [c1, c2, c3, c4, c5]; grind
  rw [hhead, hd3]
  let u := a 3
  have hu3 : u ≤ 3 := hb 3 (by decide)
  by_cases hu14 : u ≤ 1 / 4
  · have hkept : sumRange 3 (fun j => dinkH (19 / 37) (a (1 + j))) ≤
        (3 : Rat) * ((1 - (19 / 37 : Rat)) / 16) := by
      have h := sumRange_le_sumRange (n := 3) (g := fun _ => (1 - (19 / 37 : Rat)) / 16)
        (fun j hj => dinkH_le_quarter hlam1 hlam2 (ha.1 (1 + j) (by omega)) (hb (1 + j) (by omega)))
      rw [sumRange_const] at h; exact h
    have hpruned : sumRange 4 (fun j => (1 - (19 / 37 : Rat)) * (a (4 + j) * a (4 + j))) ≤
        (4 : Rat) * ((1 - (19 / 37 : Rat)) * ((1 / 4 : Rat) * (1 / 4))) := by
      have h := sumRange_le_sumRange (n := 4) (g := fun _ => (1 - (19 / 37 : Rat)) * ((1 / 4 : Rat) * (1 / 4)))
        (fun j hj => by
          have hle : a (4 + j) ≤ 1 / 4 := Rat.le_trans (ha.2 3 (4 + j) (by omega) (by omega)) hu14
          exact rat_mul_le_mul_of_nonneg_left (rat_sq_le_sq (ha.1 (4 + j) (by omega)) hle) h1ml)
      rw [sumRange_const] at h; exact h
    have hsum := rat_add_le_add (rat_add_le_add (Rat.le_refl (a := (-171 / 37 : Rat))) hkept) hpruned
    exact Rat.le_trans hsum (by grind)
  · have hu14' : (1 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu14)
    have hkept : sumRange 3 (fun j => dinkH (19 / 37) (a (1 + j))) ≤ (3 : Rat) * dinkH (19 / 37) u := by
      have h := sumRange_le_sumRange (n := 3) (g := fun _ => dinkH (19 / 37) u)
        (fun j hj => dinkH_antitone_on_tail hlam1 hlam2 hu14' (ha.2 (1 + j) 3 (by omega) (by decide)) (hb (1 + j) (by omega)))
      rw [sumRange_const] at h; exact h
    have hpruned : sumRange 4 (fun j => (1 - (19 / 37 : Rat)) * (a (4 + j) * a (4 + j))) ≤
        (4 : Rat) * ((1 - (19 / 37 : Rat)) * (u * u)) := by
      have h := sumRange_le_sumRange (n := 4) (g := fun _ => (1 - (19 / 37 : Rat)) * (u * u))
        (fun j hj => rat_mul_le_mul_of_nonneg_left
          (rat_sq_le_sq (ha.1 (4 + j) (by omega)) (ha.2 3 (4 + j) (by omega) (by omega))) h1ml)
      rw [sumRange_const] at h; exact h
    have hsum := rat_add_le_add (rat_add_le_add (Rat.le_refl (a := (-171 / 37 : Rat))) hkept) hpruned
    have hrew : (-171 / 37 : Rat) + (3 : Rat) * dinkH (19 / 37) u +
        (4 : Rat) * ((1 - (19 / 37 : Rat)) * (u * u)) =
        (-171 / 37 : Rat) + ((3 : Rat) * e2m1ErrSq u + (15 / 37 : Rat) * (u * u)) := by
      unfold dinkH; grind
    rw [hrew] at hsum
    have hcomb : (3 : Rat) * e2m1ErrSq u + (15 / 37 : Rat) * (u * u) ≤ 135 / 37 :=
      e2m1_combo_le_on_tail (by grind) hu14' hu3
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
    exact Rat.le_trans hsum (Rat.le_trans (rat_add_le_add (Rat.le_refl (a := (-171 / 37 : Rat))) hcomb) (by grind))

theorem mxfp4_48_contraction_exact {x : Nat → Nat → Rat} (hx : ValidMxfp4Block 4 8 x) :
    blockMxfp4ErrSq 4 4 8 x ≤ (1 - 18 / 37) * blockMxfp4Energy 4 8 x := by
  apply rat_le_of_sub_nonneg
  have h0 : blockMxfp4ErrSq 4 4 8 x - (19 / 37 : Rat) * blockMxfp4Energy 4 8 x ≤ 0 := by
    unfold blockMxfp4ErrSq blockMxfp4Energy
    simp only [sumRange]
    have h_g0 := group_anchor_48_mxfp4 (hx.1 0 (by decide)) (hx.2.1 0 · (by decide)) hx.2.2
    have h_g1 := group_other_48_mxfp4 (hx.1 1 (by decide)) (hx.2.1 1 · (by decide))
    have h_g2 := group_other_48_mxfp4 (hx.1 2 (by decide)) (hx.2.1 2 · (by decide))
    have h_g3 := group_other_48_mxfp4 (hx.1 3 (by decide)) (hx.2.1 3 · (by decide))
    have hsum := rat_add_le_add (rat_add_le_add (rat_add_le_add h_g0 h_g1) h_g2) h_g3
    have hrew :
        (0 + groupMxfp4ErrSq 4 8 (x 0) + groupMxfp4ErrSq 4 8 (x 1) +
          groupMxfp4ErrSq 4 8 (x 2) + groupMxfp4ErrSq 4 8 (x 3)) -
        (19 / 37 : Rat) *
          (0 + blockEnergy 8 (x 0) + blockEnergy 8 (x 1) +
            blockEnergy 8 (x 2) + blockEnergy 8 (x 3)) =
        (groupMxfp4ErrSq 4 8 (x 0) - (19 / 37 : Rat) * blockEnergy 8 (x 0)) +
        (groupMxfp4ErrSq 4 8 (x 1) - (19 / 37 : Rat) * blockEnergy 8 (x 1)) +
        (groupMxfp4ErrSq 4 8 (x 2) - (19 / 37 : Rat) * blockEnergy 8 (x 2)) +
        (groupMxfp4ErrSq 4 8 (x 3) - (19 / 37 : Rat) * blockEnergy 8 (x 3)) := by grind
    rw [hrew]
    exact Rat.le_trans hsum (by grind)
  have h1 : (1 - (18 / 37 : Rat)) * blockMxfp4Energy 4 8 x - blockMxfp4ErrSq 4 4 8 x =
      -(blockMxfp4ErrSq 4 4 8 x - (19 / 37 : Rat) * blockMxfp4Energy 4 8 x) := by grind
  rw [h1]
  have := rat_sub_nonneg h0
  grind

/-! ### `2:4 + MXFP4` (`λ = 79 / 151`, `α = 72 / 151`) -/

theorem group_other_24_mxfp4 {a : Nat → Rat}
    (ha : NonIncreasingMags 4 a) (hb : ∀ i : Nat, i < 4 → a i ≤ 3) :
    groupMxfp4ErrSq 2 4 a - (79 / 151 : Rat) * blockEnergy 4 a ≤ 18 / 151 := by
  rw [groupMxfp4_dink_decomp (by decide : 2 ≤ 4)]
  have hlam1 : (1 / 3 : Rat) ≤ 79 / 151 := by grind
  have hlam2 : (79 / 151 : Rat) ≤ 1 := by grind
  have h1ml : (0 : Rat) ≤ 1 - (79 / 151 : Rat) := by grind
  let u := a 1
  have hu3 : u ≤ 3 := hb 1 (by decide)
  by_cases hu14 : u ≤ 1 / 4
  · have hkept : sumRange 2 (fun i => dinkH (79 / 151) (a i)) ≤
        (2 : Rat) * ((1 - (79 / 151 : Rat)) / 16) := by
      have h := sumRange_le_sumRange (n := 2) (g := fun _ => (1 - (79 / 151 : Rat)) / 16)
        (fun i hi => dinkH_le_quarter hlam1 hlam2 (ha.1 i (by omega)) (hb i (by omega)))
      rw [sumRange_const] at h; exact h
    have hpruned : sumRange 2 (fun j => (1 - (79 / 151 : Rat)) * (a (2 + j) * a (2 + j))) ≤
        (2 : Rat) * ((1 - (79 / 151 : Rat)) * ((1 / 4 : Rat) * (1 / 4))) := by
      have h := sumRange_le_sumRange (n := 2) (g := fun _ => (1 - (79 / 151 : Rat)) * ((1 / 4 : Rat) * (1 / 4)))
        (fun j hj => by
          have hle : a (2 + j) ≤ 1 / 4 := Rat.le_trans (ha.2 1 (2 + j) (by omega) (by omega)) hu14
          exact rat_mul_le_mul_of_nonneg_left (rat_sq_le_sq (ha.1 (2 + j) (by omega)) hle) h1ml)
      rw [sumRange_const] at h; exact h
    exact Rat.le_trans (rat_add_le_add hkept hpruned) (by grind)
  · have hu14' : (1 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu14)
    have hkept : sumRange 2 (fun i => dinkH (79 / 151) (a i)) ≤ (2 : Rat) * dinkH (79 / 151) u := by
      have h := sumRange_le_sumRange (n := 2) (g := fun _ => dinkH (79 / 151) u)
        (fun i hi => dinkH_antitone_on_tail hlam1 hlam2 hu14' (ha.2 i 1 (by omega) (by decide)) (hb i (by omega)))
      rw [sumRange_const] at h; exact h
    have hpruned : sumRange 2 (fun j => (1 - (79 / 151 : Rat)) * (a (2 + j) * a (2 + j))) ≤
        (2 : Rat) * ((1 - (79 / 151 : Rat)) * (u * u)) := by
      have h := sumRange_le_sumRange (n := 2) (g := fun _ => (1 - (79 / 151 : Rat)) * (u * u))
        (fun j hj => rat_mul_le_mul_of_nonneg_left
          (rat_sq_le_sq (ha.1 (2 + j) (by omega)) (ha.2 1 (2 + j) (by omega) (by omega))) h1ml)
      rw [sumRange_const] at h; exact h
    have hsum := rat_add_le_add hkept hpruned
    have hrew : (2 : Rat) * dinkH (79 / 151) u + (2 : Rat) * ((1 - (79 / 151 : Rat)) * (u * u)) =
        (2 : Rat) * e2m1ErrSq u + (-14 / 151 : Rat) * (u * u) := by
      unfold dinkH; grind
    rw [hrew] at hsum
    refine Rat.le_trans hsum ?_
    exact e2m1_combo_le_on_tail (by grind) hu14' hu3
      (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)

theorem group_anchor_24_mxfp4 {a : Nat → Rat}
    (ha : NonIncreasingMags 4 a) (hb : ∀ i : Nat, i < 4 → a i ≤ 3) (h0 : a 0 = 3) :
    groupMxfp4ErrSq 2 4 a - (79 / 151 : Rat) * blockEnergy 4 a ≤ -126 / 151 := by
  rw [groupMxfp4_dink_decomp (by decide : 2 ≤ 4)]
  have hlam1 : (1 / 3 : Rat) ≤ 79 / 151 := by grind
  have hlam2 : (79 / 151 : Rat) ≤ 1 := by grind
  have h1ml : (0 : Rat) ≤ 1 - (79 / 151 : Rat) := by grind
  have hhead : sumRange 2 (fun i => dinkH (79 / 151) (a i)) =
      dinkH (79 / 151) 3 + dinkH (79 / 151) (a 1) := by
    simp only [sumRange, h0]; grind
  have hd3 : dinkH (79 / 151) 3 = -711 / 151 := by
    unfold dinkH e2m1ErrSq
    have c1 : ¬ (3 : Rat) ≤ 1 / 4 := by grind
    have c2 : ¬ (3 : Rat) ≤ 3 / 4 := by grind
    have c3 : ¬ (3 : Rat) ≤ 5 / 4 := by grind
    have c4 : ¬ (3 : Rat) ≤ 7 / 4 := by grind
    have c5 : ¬ (3 : Rat) ≤ 5 / 2 := by grind
    simp [c1, c2, c3, c4, c5]; grind
  rw [hhead, hd3]
  let u := a 1
  have hu3 : u ≤ 3 := hb 1 (by decide)
  by_cases hu14 : u ≤ 1 / 4
  · have hkept : dinkH (79 / 151) u ≤ (1 - (79 / 151 : Rat)) / 16 :=
      dinkH_le_quarter hlam1 hlam2 (ha.1 1 (by decide)) hu3
    have hpruned : sumRange 2 (fun j => (1 - (79 / 151 : Rat)) * (a (2 + j) * a (2 + j))) ≤
        (2 : Rat) * ((1 - (79 / 151 : Rat)) * ((1 / 4 : Rat) * (1 / 4))) := by
      have h := sumRange_le_sumRange (n := 2) (g := fun _ => (1 - (79 / 151 : Rat)) * ((1 / 4 : Rat) * (1 / 4)))
        (fun j hj => by
          have hle : a (2 + j) ≤ 1 / 4 := Rat.le_trans (ha.2 1 (2 + j) (by omega) (by omega)) hu14
          exact rat_mul_le_mul_of_nonneg_left (rat_sq_le_sq (ha.1 (2 + j) (by omega)) hle) h1ml)
      rw [sumRange_const] at h; exact h
    have hsum := rat_add_le_add (rat_add_le_add (Rat.le_refl (a := (-711 / 151 : Rat))) hkept) hpruned
    exact Rat.le_trans hsum (by grind)
  · have hu14' : (1 / 4 : Rat) ≤ u := Rat.le_of_lt (Rat.not_le.mp hu14)
    have hpruned : sumRange 2 (fun j => (1 - (79 / 151 : Rat)) * (a (2 + j) * a (2 + j))) ≤
        (2 : Rat) * ((1 - (79 / 151 : Rat)) * (u * u)) := by
      have h := sumRange_le_sumRange (n := 2) (g := fun _ => (1 - (79 / 151 : Rat)) * (u * u))
        (fun j hj => rat_mul_le_mul_of_nonneg_left
          (rat_sq_le_sq (ha.1 (2 + j) (by omega)) (ha.2 1 (2 + j) (by omega) (by omega))) h1ml)
      rw [sumRange_const] at h; exact h
    have hsum := rat_add_le_add (rat_add_le_add (Rat.le_refl (a := (-711 / 151 : Rat))) (Rat.le_refl (a := dinkH (79 / 151) u))) hpruned
    have hrew : (-711 / 151 : Rat) + dinkH (79 / 151) u +
        (2 : Rat) * ((1 - (79 / 151 : Rat)) * (u * u)) =
        (-711 / 151 : Rat) + ((1 : Rat) * e2m1ErrSq u + (65 / 151 : Rat) * (u * u)) := by
      unfold dinkH; grind
    rw [hrew] at hsum
    have hcomb : (1 : Rat) * e2m1ErrSq u + (65 / 151 : Rat) * (u * u) ≤ 585 / 151 :=
      e2m1_combo_le_on_tail (by grind) hu14' hu3
        (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
    exact Rat.le_trans hsum (Rat.le_trans (rat_add_le_add (Rat.le_refl (a := (-711 / 151 : Rat))) hcomb) (by grind))

theorem mxfp4_24_contraction_exact {x : Nat → Nat → Rat} (hx : ValidMxfp4Block 8 4 x) :
    blockMxfp4ErrSq 8 2 4 x ≤ (1 - 72 / 151) * blockMxfp4Energy 8 4 x := by
  apply rat_le_of_sub_nonneg
  have h0 : blockMxfp4ErrSq 8 2 4 x - (79 / 151 : Rat) * blockMxfp4Energy 8 4 x ≤ 0 := by
    unfold blockMxfp4ErrSq blockMxfp4Energy
    have hsp : sumRange 8 (fun r => groupMxfp4ErrSq 2 4 (x r) - (79 / 151 : Rat) * blockEnergy 4 (x r)) =
        sumRange 8 (fun r => groupMxfp4ErrSq 2 4 (x r)) -
        (79 / 151 : Rat) * sumRange 8 (fun r => blockEnergy 4 (x r)) := by
      have ha : sumRange 8 (fun r => groupMxfp4ErrSq 2 4 (x r) - (79 / 151 : Rat) * blockEnergy 4 (x r)) +
          (79 / 151 : Rat) * sumRange 8 (fun r => blockEnergy 4 (x r)) =
          sumRange 8 (fun r => groupMxfp4ErrSq 2 4 (x r)) := by
        rw [← sumRange_mul_left, ← sumRange_add]
        apply sumRange_congr; intro r _; grind
      grind
    rw [← hsp]
    have hhead := sumRange_split 1 7 (fun r => groupMxfp4ErrSq 2 4 (x r) - (79 / 151 : Rat) * blockEnergy 4 (x r))
    rw [hhead]
    have h_g0 : sumRange 1 (fun r => groupMxfp4ErrSq 2 4 (x r) - (79 / 151 : Rat) * blockEnergy 4 (x r)) ≤ -126 / 151 := by
      simp only [sumRange]
      have hg := group_anchor_24_mxfp4 (hx.1 0 (by decide)) (hx.2.1 0 · (by decide)) hx.2.2
      grind
    have h_rest : sumRange 7 (fun j => groupMxfp4ErrSq 2 4 (x (1 + j)) - (79 / 151 : Rat) * blockEnergy 4 (x (1 + j))) ≤
        (7 : Rat) * (18 / 151) := by
      have h := sumRange_le_sumRange (n := 7) (g := fun _ => (18 / 151 : Rat))
        (fun j hj => group_other_24_mxfp4 (hx.1 (1 + j) (by omega)) (hx.2.1 (1 + j) · (by omega)))
      rw [sumRange_const] at h; exact h
    exact Rat.le_trans (rat_add_le_add h_g0 h_rest) (by grind)
  have h1 : (1 - (72 / 151 : Rat)) * blockMxfp4Energy 8 4 x - blockMxfp4ErrSq 8 2 4 x =
      -(blockMxfp4ErrSq 8 2 4 x - (79 / 151 : Rat) * blockMxfp4Energy 8 4 x) := by grind
  rw [h1]
  have := rat_sub_nonneg h0
  grind

/-! ### Exact Attainment Witnesses for `4:8 + MXFP4` and `2:4 + MXFP4` -/

def witness48Mxfp4 (r _ : Nat) : Rat :=
  if r == 0 then 3 else 5 / 2

def witness24Mxfp4 (r _ : Nat) : Rat :=
  if r == 0 then 3 else 1 / 4

theorem e2m1ErrSq_3 : e2m1ErrSq 3 = 0 := by
  unfold e2m1ErrSq
  have c1 : ¬ (3 : Rat) ≤ 1 / 4 := by grind
  have c2 : ¬ (3 : Rat) ≤ 3 / 4 := by grind
  have c3 : ¬ (3 : Rat) ≤ 5 / 4 := by grind
  have c4 : ¬ (3 : Rat) ≤ 7 / 4 := by grind
  have c5 : ¬ (3 : Rat) ≤ 5 / 2 := by grind
  simp [c1, c2, c3, c4, c5]; grind

theorem e2m1ErrSq_5_2 : e2m1ErrSq (5 / 2) = 1 / 4 := by
  unfold e2m1ErrSq
  have c1 : ¬ (5 / 2 : Rat) ≤ 1 / 4 := by grind
  have c2 : ¬ (5 / 2 : Rat) ≤ 3 / 4 := by grind
  have c3 : ¬ (5 / 2 : Rat) ≤ 5 / 4 := by grind
  have c4 : ¬ (5 / 2 : Rat) ≤ 7 / 4 := by grind
  simp [c1, c2, c3, c4]; grind

theorem e2m1ErrSq_1_4 : e2m1ErrSq (1 / 4) = 1 / 16 := by
  unfold e2m1ErrSq
  simp; grind

theorem witness48Mxfp4_exact :
    ValidMxfp4Block 4 8 witness48Mxfp4 ∧
    blockMxfp4ErrSq 4 4 8 witness48Mxfp4 = 114 ∧
    blockMxfp4Energy 4 8 witness48Mxfp4 = 222 ∧
    1 - blockMxfp4ErrSq 4 4 8 witness48Mxfp4 / blockMxfp4Energy 4 8 witness48Mxfp4 = 18 / 37 := by
  have hw0 : ∀ i, witness48Mxfp4 0 i = 3 := fun _ => rfl
  have hw1 : ∀ i, witness48Mxfp4 1 i = 5 / 2 := fun _ => rfl
  have hw2 : ∀ i, witness48Mxfp4 2 i = 5 / 2 := fun _ => rfl
  have hw3 : ∀ i, witness48Mxfp4 3 i = 5 / 2 := fun _ => rfl
  have herr : blockMxfp4ErrSq 4 4 8 witness48Mxfp4 = 114 := by
    simp only [blockMxfp4ErrSq, groupMxfp4ErrSq, sumRange, hw0, hw1, hw2, hw3,
      e2m1ErrSq_3, e2m1ErrSq_5_2]
    grind
  have hene : blockMxfp4Energy 4 8 witness48Mxfp4 = 222 := by
    simp only [blockMxfp4Energy, blockEnergy, sumRange, hw0, hw1, hw2, hw3]
    grind
  refine ⟨?_, herr, hene, by rw [herr, hene]; grind⟩
  refine ⟨?_, ?_, by simp [witness48Mxfp4]⟩
  · intro r _
    unfold witness48Mxfp4 NonIncreasingMags
    by_cases h : r == 0
    · constructor
      · intro _ _; simp [h]; grind
      · intro _ _ _ _; simp [h]
    · constructor
      · intro _ _; simp [h]; grind
      · intro _ _ _ _; simp [h]
  · intro r _ _ _
    unfold witness48Mxfp4
    by_cases h : r == 0
    · simp [h]
    · simp [h]; grind

theorem witness24Mxfp4_exact :
    ValidMxfp4Block 8 4 witness24Mxfp4 ∧
    blockMxfp4ErrSq 8 2 4 witness24Mxfp4 = 79 / 4 ∧
    blockMxfp4Energy 8 4 witness24Mxfp4 = 151 / 4 ∧
    1 - blockMxfp4ErrSq 8 2 4 witness24Mxfp4 / blockMxfp4Energy 8 4 witness24Mxfp4 = 72 / 151 := by
  have hw0 : ∀ i, witness24Mxfp4 0 i = 3 := fun _ => rfl
  have hw1 : ∀ i, witness24Mxfp4 1 i = 1 / 4 := fun _ => rfl
  have hw2 : ∀ i, witness24Mxfp4 2 i = 1 / 4 := fun _ => rfl
  have hw3 : ∀ i, witness24Mxfp4 3 i = 1 / 4 := fun _ => rfl
  have hw4 : ∀ i, witness24Mxfp4 4 i = 1 / 4 := fun _ => rfl
  have hw5 : ∀ i, witness24Mxfp4 5 i = 1 / 4 := fun _ => rfl
  have hw6 : ∀ i, witness24Mxfp4 6 i = 1 / 4 := fun _ => rfl
  have hw7 : ∀ i, witness24Mxfp4 7 i = 1 / 4 := fun _ => rfl
  have herr : blockMxfp4ErrSq 8 2 4 witness24Mxfp4 = 79 / 4 := by
    simp only [blockMxfp4ErrSq, groupMxfp4ErrSq, sumRange,
      hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, e2m1ErrSq_3, e2m1ErrSq_1_4]
    grind
  have hene : blockMxfp4Energy 8 4 witness24Mxfp4 = 151 / 4 := by
    simp only [blockMxfp4Energy, blockEnergy, sumRange,
      hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
    grind
  refine ⟨?_, herr, hene, by rw [herr, hene]; grind⟩
  refine ⟨?_, ?_, by simp [witness24Mxfp4]⟩
  · intro r _
    unfold witness24Mxfp4 NonIncreasingMags
    by_cases h : r == 0
    · constructor
      · intro _ _; simp [h]; grind
      · intro _ _ _ _; simp [h]
    · constructor
      · intro _ _; simp [h]; grind
      · intro _ _ _ _; simp [h]
  · intro r _ _ _
    unfold witness24Mxfp4
    by_cases h : r == 0
    · simp [h]
    · simp [h]; grind

/-! ### Exact Closed-Form Dense Max-Abs Ternary Contraction Law (`4 / (B + 3)`) -/

theorem ternary_dink_entry {B : Nat} (hB : 1 ≤ B) {y : Rat} (hy0 : (0 : Rat) ≤ y) (hy1 : y ≤ 1) :
    ternaryErrSq y - (1 - ternaryDenseAlpha B) * (y * y) ≤ ternaryDenseAlpha B / 4 := by
  let α := ternaryDenseAlpha B
  have hB3 : (0 : Rat) < ((B + 3 : Nat) : Rat) := rat_natCast_pos (by omega)
  have hα_pos : (0 : Rat) < α := rat_div_pos (by grind) hB3
  have hα_le1 : α ≤ 1 := by
    apply rat_div_le_of_mul_le hB3
    have h4 : ((4 : Nat) : Rat) ≤ ((B + 3 : Nat) : Rat) := rat_natCast_le (by omega)
    grind
  by_cases hhalf : y ≤ 1 / 2
  · unfold ternaryErrSq; simp [hhalf]
    have hsq : y * y ≤ (1 / 4 : Rat) := by
      have := rat_sq_le_sq hy0 hhalf; grind
    have hmul := rat_mul_le_mul_of_nonneg_left hsq (Rat.le_of_lt hα_pos)
    have hl : y * y - (1 - α) * (y * y) = α * (y * y) := by grind
    have hr : α * (1 / 4 : Rat) = α / 4 := by grind
    rw [hl, ← hr]; exact hmul
  · have hy12 : (1 / 2 : Rat) ≤ y := Rat.le_of_lt (Rat.not_le.mp hhalf)
    unfold ternaryErrSq; simp [hhalf]
    have hrew : (y - 1) * (y - 1) - (1 - α) * (y * y) = α * (y * y) + (-2) * y + 1 := by grind
    rw [hrew]
    apply quad_le_of_endpoints (Rat.le_of_lt hα_pos) (by grind : (1 / 2 : Rat) < 1) hy12 hy1
    · have : α * ((1 / 2 : Rat) * (1 / 2)) + (-2) * (1 / 2) + 1 = α / 4 := by grind
      rw [this]; exact Rat.le_refl
    · have : α * ((1 : Rat) * 1) + (-2) * 1 + 1 = α - 1 := by grind
      rw [this]
      apply rat_le_of_sub_nonneg
      have h1 : α / 4 - (α - 1) = (1 - α) + α / 4 := by grind
      rw [h1]
      exact rat_add_nonneg (rat_sub_nonneg hα_le1) (Rat.le_of_lt (rat_div_pos hα_pos (by grind)))

theorem dense_ternary_contraction_exact {B : Nat} (hB : 1 ≤ B) {x : Nat → Rat}
    (hx0 : x 0 = 1) (hx_bounds : ∀ i : Nat, i < B → (0 : Rat) ≤ x i ∧ x i ≤ 1) :
    sumRange B (fun i => ternaryErrSq (x i)) ≤
      (1 - ternaryDenseAlpha B) * sumRange B (fun i => x i * x i) := by
  let α := ternaryDenseAlpha B
  have hB3_pos : (0 : Rat) < ((B + 3 : Nat) : Rat) := rat_natCast_pos (by omega)
  have hB3_ne : ((B + 3 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hB3_pos
  apply rat_le_of_sub_nonneg
  have hdiff : sumRange B (fun i => ternaryErrSq (x i)) - (1 - α) * sumRange B (fun i => x i * x i) ≤ 0 := by
    have hsp : sumRange B (fun i => ternaryErrSq (x i) - (1 - α) * (x i * x i)) =
        sumRange B (fun i => ternaryErrSq (x i)) - (1 - α) * sumRange B (fun i => x i * x i) := by
      have ha : sumRange B (fun i => ternaryErrSq (x i) - (1 - α) * (x i * x i)) +
          (1 - α) * sumRange B (fun i => x i * x i) = sumRange B (fun i => ternaryErrSq (x i)) := by
        rw [← sumRange_mul_left, ← sumRange_add]
        apply sumRange_congr; intro i _; grind
      grind
    rw [← hsp]
    have hB1 : 1 + (B - 1) = B := by omega
    have hsplit := sumRange_split 1 (B - 1) (fun i => ternaryErrSq (x i) - (1 - α) * (x i * x i))
    rw [hB1] at hsplit
    rw [hsplit]
    have h0 : sumRange 1 (fun i => ternaryErrSq (x i) - (1 - α) * (x i * x i)) = -(1 - α) := by
      simp only [sumRange, hx0]
      have ht1 : ternaryErrSq 1 = 0 := by
        unfold ternaryErrSq
        have h : ¬ (1 : Rat) ≤ 1 / 2 := by grind
        simp [h]; grind
      rw [ht1]; grind
    have hrest : sumRange (B - 1) (fun j => ternaryErrSq (x (1 + j)) - (1 - α) * (x (1 + j) * x (1 + j))) ≤
        ((B - 1 : Nat) : Rat) * (α / 4) := by
      rw [← sumRange_const (B - 1)]
      exact sumRange_le_sumRange (fun j hj =>
        ternary_dink_entry hB (hx_bounds (1 + j) (by omega)).1 (hx_bounds (1 + j) (by omega)).2)
    rw [h0]
    have hcancel : -(1 - α) + ((B - 1 : Nat) : Rat) * (α / 4) = 0 := by
      have hα_mul : α * ((B + 3 : Nat) : Rat) = 4 := rat_div_mul_cancel hB3_ne
      have hBcast : ((B - 1 : Nat) : Rat) + 4 = ((B + 3 : Nat) : Rat) := by
        have h4 : (4 : Rat) = ((4 : Nat) : Rat) := rfl
        rw [h4, ← Rat.natCast_add]
        have : B - 1 + 4 = B + 3 := by omega
        rw [this]
      grind
    have hsum := rat_add_le_add (Rat.le_refl (a := -(1 - α))) hrest
    rw [hcancel] at hsum
    exact hsum
  have h1 : (1 - α) * sumRange B (fun i => x i * x i) - sumRange B (fun i => ternaryErrSq (x i)) =
      -(sumRange B (fun i => ternaryErrSq (x i)) - (1 - α) * sumRange B (fun i => x i * x i)) := by grind
  rw [h1]
  have := rat_sub_nonneg hdiff
  grind

def witnessTernary (i : Nat) : Rat :=
  if i == 0 then 1 else 1 / 2

theorem witnessTernary_attains {B : Nat} (hB : 1 ≤ B) :
    witnessTernary 0 = 1 ∧
    (∀ i : Nat, i < B → (0 : Rat) ≤ witnessTernary i ∧ witnessTernary i ≤ 1) ∧
    sumRange B (fun i => ternaryErrSq (witnessTernary i)) =
      (1 - ternaryDenseAlpha B) * sumRange B (fun i => witnessTernary i * witnessTernary i) := by
  have hB3_ne : ((B + 3 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (by omega))
  refine ⟨by simp [witnessTernary], ?_, ?_⟩
  · intro i _
    unfold witnessTernary
    by_cases h : i == 0 <;> simp [h] <;> grind
  · have hB1 : 1 + (B - 1) = B := by omega
    have hE : sumRange B (fun i => ternaryErrSq (witnessTernary i)) = ((B - 1 : Nat) : Rat) / 4 := by
      have hsp := sumRange_split 1 (B - 1) (fun i => ternaryErrSq (witnessTernary i))
      rw [hB1] at hsp; rw [hsp]
      have h0 : sumRange 1 (fun i => ternaryErrSq (witnessTernary i)) = 0 := by
        simp only [sumRange, witnessTernary]
        have h : ¬ (1 : Rat) ≤ 1 / 2 := by grind
        simp [ternaryErrSq, h]; grind
      have h1 : sumRange (B - 1) (fun j => ternaryErrSq (witnessTernary (1 + j))) =
          ((B - 1 : Nat) : Rat) * (1 / 4) := by
        rw [← sumRange_const (B - 1)]
        apply sumRange_congr; intro j _
        have hne : (1 + j == 0) = false := by cases j <;> rfl
        simp [witnessTernary, hne, ternaryErrSq]; grind
      rw [h0, h1]; grind
    have hN : sumRange B (fun i => witnessTernary i * witnessTernary i) =
        ((B + 3 : Nat) : Rat) / 4 := by
      have hsp := sumRange_split 1 (B - 1) (fun i => witnessTernary i * witnessTernary i)
      rw [hB1] at hsp; rw [hsp]
      have h0 : sumRange 1 (fun i => witnessTernary i * witnessTernary i) = 1 := by
        simp only [sumRange, witnessTernary]; grind
      have h1 : sumRange (B - 1) (fun j => witnessTernary (1 + j) * witnessTernary (1 + j)) =
          ((B - 1 : Nat) : Rat) * (1 / 4) := by
        rw [← sumRange_const (B - 1)]
        apply sumRange_congr; intro j _
        have hne : (1 + j == 0) = false := by cases j <;> rfl
        simp [witnessTernary, hne]; grind
      have hBcast : ((B - 1 : Nat) : Rat) + 4 = ((B + 3 : Nat) : Rat) := by
        have h4 : (4 : Rat) = ((4 : Nat) : Rat) := rfl
        rw [h4, ← Rat.natCast_add]
        have : B - 1 + 4 = B + 3 := by omega
        rw [this]
      rw [h0, h1]; grind
    rw [hE, hN]
    unfold ternaryDenseAlpha
    have hmul : ((4 : Rat) / ((B + 3 : Nat) : Rat)) * ((B + 3 : Nat) : Rat) = 4 :=
      rat_div_mul_cancel hB3_ne
    have hBcast : ((B - 1 : Nat) : Rat) + 4 = ((B + 3 : Nat) : Rat) := by
      have h4 : (4 : Rat) = ((4 : Nat) : Rat) := rfl
      rw [h4, ← Rat.natCast_add]
      have : B - 1 + 4 = B + 3 := by omega
      rw [this]
    grind

/-- Headline Theorem 2: Exact Joint `k:m + MXFP4` (`B = 32`) Worst-Case EF21 Contraction
    Proving `4:8 + MXFP4` (`18/37`) Strictly Beats `2:4 + MXFP4` (`72/151`) via Anchor-Group Dilution,
    plus the Exact Closed-Form Dense Ternary Contraction Law `4 / (B + 3)`. -/
theorem mxfp4_anchor_dilution_48_beats_24_exact :
    (∀ x : Nat → Nat → Rat, ValidMxfp4Block 4 8 x →
      blockMxfp4ErrSq 4 4 8 x ≤ (1 - 18 / 37) * blockMxfp4Energy 4 8 x) ∧
    (∃ x : Nat → Nat → Rat, ValidMxfp4Block 4 8 x ∧
      blockMxfp4ErrSq 4 4 8 x = 114 ∧ blockMxfp4Energy 4 8 x = 222 ∧
      1 - blockMxfp4ErrSq 4 4 8 x / blockMxfp4Energy 4 8 x = 18 / 37) ∧
    (∀ x : Nat → Nat → Rat, ValidMxfp4Block 8 4 x →
      blockMxfp4ErrSq 8 2 4 x ≤ (1 - 72 / 151) * blockMxfp4Energy 8 4 x) ∧
    (∃ x : Nat → Nat → Rat, ValidMxfp4Block 8 4 x ∧
      blockMxfp4ErrSq 8 2 4 x = 79 / 4 ∧ blockMxfp4Energy 8 4 x = 151 / 4 ∧
      1 - blockMxfp4ErrSq 8 2 4 x / blockMxfp4Energy 8 4 x = 72 / 151) ∧
    ((72 / 151 : Rat) < 18 / 37 ∧ (18 / 37 : Rat) - 72 / 151 = 54 / 5587) ∧
    (∀ (B : Nat) (x : Nat → Rat), 1 ≤ B → x 0 = 1 →
      (∀ i : Nat, i < B → (0 : Rat) ≤ x i ∧ x i ≤ 1) →
      sumRange B (fun i => ternaryErrSq (x i)) ≤
        (1 - ternaryDenseAlpha B) * sumRange B (fun i => x i * x i)) ∧
    (∀ B : Nat, 1 ≤ B →
      ∃ x : Nat → Rat, x 0 = 1 ∧
        (∀ i : Nat, i < B → (0 : Rat) ≤ x i ∧ x i ≤ 1) ∧
        sumRange B (fun i => ternaryErrSq (x i)) =
          (1 - ternaryDenseAlpha B) * sumRange B (fun i => x i * x i)) ∧
    ternaryDenseAlpha 32 = 4 / 35 := by
  refine ⟨?_, ?_, ?_, ?_, by grind, ?_, ?_, by unfold ternaryDenseAlpha; grind⟩
  · intro x hx; exact mxfp4_48_contraction_exact hx
  · exact ⟨witness48Mxfp4, witness48Mxfp4_exact⟩
  · intro x hx; exact mxfp4_24_contraction_exact hx
  · exact ⟨witness24Mxfp4, witness24Mxfp4_exact⟩
  · intro B x hB hx0 hxb; exact dense_ternary_contraction_exact hB hx0 hxb
  · intro B hB; exact ⟨witnessTernary, witnessTernary_attains hB⟩

end FanoSparse24Perm
