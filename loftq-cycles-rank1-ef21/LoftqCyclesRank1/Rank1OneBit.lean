/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LoftqCyclesRank1.Defs

/-!
# Theorem 1: Exact Universal Rank-1 1-Bit Sign EF21 Matrix Contraction (`1 / (m * n)`)

Proves `rank1_onebit_ef21_contraction_exact` for all `m, n ≥ 1` over `ℚ^{m × n}`:
1. Universal upper bound: for every `W : RatMat m n`, there exist `u ∈ {-1, 1}^m`,
   `v ∈ {-1, 1}^n`, and `γ : Rat` such that
   `‖W - γ u v^T‖_F^2 ≤ (1 - 1 / (m * n)) * ‖W‖_F^2`.
2. Exact attainment: for every `m, n ≥ 1`, the rank-1 spike `W = e_0 e_0^T` satisfies
   `‖W‖_F^2 = 1 > 0` and `‖W - γ u v^T‖_F^2 ≥ (1 - 1 / (m * n)) * ‖W‖_F^2`
   for all `u ∈ {-1, 1}^m`, `v ∈ {-1, 1}^n`, and `γ : Rat`.
-/

namespace LoftqCyclesRank1

/-! ### Basic `Rat` and `sumFinRat` Algebraic Lemmas -/

theorem rat_sq_nonneg (x : Rat) : (0 : Rat) ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hlt : x < 0 := Rat.not_le.mp hx
    have hneg : 0 ≤ -x := by grind
    have hmul : 0 ≤ (-x) * (-x) := Rat.mul_nonneg hneg hneg
    have heq : (-x) * (-x) = x * x := by grind
    rw [heq] at hmul
    exact hmul

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr hb))

theorem sumFinRat_congr {n : Nat} (f g : Fin n → Rat) (h : ∀ i, f i = g i) :
    sumFinRat n f = sumFinRat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => h i.castSucc), h (Fin.last k)]

theorem sumFinRat_zero (n : Nat) : sumFinRat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumFinRat, ih]; grind

theorem sumFinRat_add {n : Nat} (f g : Fin n → Rat) :
    sumFinRat n (fun i => f i + g i) = sumFinRat n f + sumFinRat n g := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem sumFinRat_sub {n : Nat} (f g : Fin n → Rat) :
    sumFinRat n (fun i => f i - g i) = sumFinRat n f - sumFinRat n g := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

theorem sumFinRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumFinRat n (fun i => c * f i) = c * sumFinRat n f := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i => f i.castSucc), Rat.mul_add]

theorem sumFinRat_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumFinRat n (fun i => f i * c) = sumFinRat n f * c := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i => f i.castSucc), Rat.add_mul]

theorem sumFinRat_const (n : Nat) (c : Rat) :
    sumFinRat n (fun _ => c) = (n : Rat) * c := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ k ih =>
    simp only [sumFinRat, ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [hcast]
    grind

theorem sumFinRat_swap {m n : Nat} (f : Fin m → Fin n → Rat) :
    sumFinRat m (fun i => sumFinRat n (fun j => f i j)) =
    sumFinRat n (fun j => sumFinRat m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFinRat]
    exact (sumFinRat_zero n).symm
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i j => f i.castSucc j)]
    rw [← sumFinRat_add]

theorem sumFinRat_single_zero {n : Nat} (hn : 0 < n) (f : Fin n → Rat)
    (h0 : ∀ i : Fin n, i.val ≠ 0 → f i = 0) :
    sumFinRat n f = f ⟨0, hn⟩ := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simp only [sumFinRat, Rat.zero_add]
      rfl
    | succ k' =>
      simp only [sumFinRat]
      have hlast : f (Fin.last (k' + 1)) = 0 := h0 (Fin.last (k' + 1)) (by simp)
      rw [hlast, Rat.add_zero]
      exact ih (Nat.zero_lt_succ k') (fun i => f i.castSucc) (fun i hi => h0 i.castSucc hi)

/-! ### Sign-Vector Energy Maximization (1D and 2D Matrix) -/

theorem sign_sq_one {z : Int} (hz : z = 1 ∨ z = -1) : (z : Rat) * (z : Rat) = 1 := by
  rcases hz with rfl | rfl <;> grind

theorem exists_sign_vec_1d (n : Nat) (x : Fin n → Rat) :
    ∃ v : Fin n → Int, isSignVec v ∧
      sumFinRat n (fun j => x j * x j) ≤
      (sumFinRat n (fun j => x j * (v j : Rat))) * (sumFinRat n (fun j => x j * (v j : Rat))) := by
  induction n with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    simp only [sumFinRat]
    grind
  | succ k ih =>
    obtain ⟨v', hv', hle'⟩ := ih (fun j => x j.castSucc)
    let S : Rat := sumFinRat k (fun j => x j.castSucc * (v' j : Rat))
    let a : Rat := x (Fin.last k)
    let s : Int := if 0 ≤ S * a then 1 else -1
    let v : Fin (k + 1) → Int := fun j =>
      if h : j.val < k then v' ⟨j.val, h⟩ else s
    refine ⟨v, ?_, ?_⟩
    · intro j
      simp only [v]
      split
      · exact hv' _
      · simp only [s]
        split <;> simp
    · have hsum_v : sumFinRat (k + 1) (fun j => x j * (v j : Rat)) = S + a * (s : Rat) := by
        simp only [sumFinRat]
        have h1 : sumFinRat k (fun j => x j.castSucc * (v j.castSucc : Rat)) = S := by
          apply sumFinRat_congr
          intro j
          simp only [v, Fin.val_castSucc, j.isLt, dite_true]
        have h2 : v (Fin.last k) = s := by
          simp only [v, Fin.val_last, Nat.lt_irrefl, dite_false]
        rw [h1, h2]
      rw [hsum_v]
      simp only [sumFinRat]
      have hs2 : (s : Rat) * (s : Rat) = 1 := by
        simp only [s]
        split <;> grind
      have hcross : (0 : Rat) ≤ S * a * (s : Rat) := by
        simp only [s]
        split <;> grind
      have hexp : (S + a * (s : Rat)) * (S + a * (s : Rat)) =
          S * S + 2 * (S * a * (s : Rat)) + a * a * ((s : Rat) * (s : Rat)) := by
        grind
      rw [hexp, hs2, Rat.mul_one]
      grind

theorem exists_sign_vec_rows (m n : Nat) (W : RatMat m n) :
    ∃ u : Fin m → Int, isSignVec u ∧
      frobSq W ≤
      sumFinRat n (fun j =>
        (sumFinRat m (fun i => (u i : Rat) * W i j)) *
        (sumFinRat m (fun i => (u i : Rat) * W i j))) := by
  induction m with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    simp only [frobSq, sumFinRat]
    have h0 : sumFinRat n (fun _ => (0 : Rat) * 0) = 0 := by
      rw [sumFinRat_congr (fun _ => (0 : Rat) * 0) (fun _ => 0) (fun _ => by grind)]
      exact sumFinRat_zero n
    rw [h0]
    grind
  | succ k ih =>
    obtain ⟨u', hu', hle'⟩ := ih (fun i j => W i.castSucc j)
    let S : Fin n → Rat := fun j => sumFinRat k (fun i => (u' i : Rat) * W i.castSucc j)
    let w : Fin n → Rat := fun j => W (Fin.last k) j
    let ip : Rat := sumFinRat n (fun j => S j * w j)
    let s : Int := if 0 ≤ ip then 1 else -1
    let u : Fin (k + 1) → Int := fun i =>
      if h : i.val < k then u' ⟨i.val, h⟩ else s
    refine ⟨u, ?_, ?_⟩
    · intro i
      simp only [u]
      split
      · exact hu' _
      · simp only [s]
        split <;> simp
    · have hrow : ∀ j : Fin n,
          sumFinRat (k + 1) (fun i => (u i : Rat) * W i j) = S j + (s : Rat) * w j := by
        intro j
        simp only [sumFinRat]
        have h1 : sumFinRat k (fun i => (u i.castSucc : Rat) * W i.castSucc j) = S j := by
          apply sumFinRat_congr
          intro i
          simp only [u, Fin.val_castSucc, i.isLt, dite_true]
        have h2 : u (Fin.last k) = s := by
          simp only [u, Fin.val_last, Nat.lt_irrefl, dite_false]
        rw [h1, h2]
      have hs2 : (s : Rat) * (s : Rat) = 1 := by
        simp only [s]
        split <;> grind
      have hrhs : sumFinRat n (fun j =>
            (sumFinRat (k + 1) (fun i => (u i : Rat) * W i j)) *
            (sumFinRat (k + 1) (fun i => (u i : Rat) * W i j))) =
          sumFinRat n (fun j => S j * S j) + 2 * (s : Rat) * ip + sumFinRat n (fun j => w j * w j) := by
        have hcongr : sumFinRat n (fun j =>
              (sumFinRat (k + 1) (fun i => (u i : Rat) * W i j)) *
              (sumFinRat (k + 1) (fun i => (u i : Rat) * W i j))) =
            sumFinRat n (fun j => (S j * S j + (2 * (s : Rat)) * (S j * w j)) + w j * w j) := by
          apply sumFinRat_congr
          intro j
          rw [hrow j]
          have : (S j + (s : Rat) * w j) * (S j + (s : Rat) * w j) =
              S j * S j + (2 * (s : Rat)) * (S j * w j) + ((s : Rat) * (s : Rat)) * (w j * w j) := by
            grind
          rw [this, hs2, Rat.one_mul]
        rw [hcongr, sumFinRat_add, sumFinRat_add, sumFinRat_mul_left]
      rw [hrhs]
      have hfrob : frobSq W = frobSq (fun i j => W i.castSucc j) + sumFinRat n (fun j => w j * w j) := by
        simp only [frobSq, sumFinRat, w]
      rw [hfrob]
      have hcross : (0 : Rat) ≤ (s : Rat) * ip := by
        simp only [s]
        split <;> grind
      grind

theorem exists_sign_pair_quadForm (m n : Nat) (W : RatMat m n) :
    ∃ u : Fin m → Int, ∃ v : Fin n → Int, isSignVec u ∧ isSignVec v ∧
      frobSq W ≤ quadFormRat W u v * quadFormRat W u v := by
  obtain ⟨u, hu, hrows⟩ := exists_sign_vec_rows m n W
  let y : Fin n → Rat := fun j => sumFinRat m (fun i => (u i : Rat) * W i j)
  obtain ⟨v, hv, h1d⟩ := exists_sign_vec_1d n y
  refine ⟨u, v, hu, hv, ?_⟩
  have hq : quadFormRat W u v = sumFinRat n (fun j => y j * (v j : Rat)) := by
    unfold quadFormRat
    have h1 : sumFinRat m (fun i => (u i : Rat) * sumFinRat n (fun j => W i j * (v j : Rat))) =
        sumFinRat m (fun i => sumFinRat n (fun j => (u i : Rat) * W i j * (v j : Rat))) := by
      apply sumFinRat_congr
      intro i
      rw [← sumFinRat_mul_left]
      apply sumFinRat_congr
      intro j
      grind
    rw [h1, sumFinRat_swap]
    apply sumFinRat_congr
    intro j
    rw [sumFinRat_mul_right]
  rw [hq]
  exact Rat.le_trans hrows h1d

/-! ### Exact Frobenius Error Expansion for Rank-1 Sign Matrices -/

theorem frobSqErr_rank1_sign {m n : Nat} (W : RatMat m n)
    (u : Fin m → Int) (v : Fin n → Int) (hu : isSignVec u) (hv : isSignVec v) (γ : Rat) :
    frobSqErr W (rank1Mat γ u v) =
      frobSq W - 2 * γ * quadFormRat W u v + ((m * n : Nat) : Rat) * (γ * γ) := by
  unfold frobSqErr frobSq matSub rank1Mat quadFormRat
  have hexp : ∀ i : Fin m,
      sumFinRat n (fun j => (W i j - γ * (u i : Rat) * (v j : Rat)) *
                            (W i j - γ * (u i : Rat) * (v j : Rat))) =
      sumFinRat n (fun j => W i j * W i j) -
      2 * γ * ((u i : Rat) * sumFinRat n (fun j => W i j * (v j : Rat))) +
      (n : Rat) * (γ * γ) := by
    intro i
    have hui : (u i : Rat) * (u i : Rat) = 1 := sign_sq_one (hu i)
    have hcongr : sumFinRat n (fun j => (W i j - γ * (u i : Rat) * (v j : Rat)) *
                                        (W i j - γ * (u i : Rat) * (v j : Rat))) =
        sumFinRat n (fun j => (W i j * W i j - (2 * γ * (u i : Rat)) * (W i j * (v j : Rat))) + γ * γ) := by
      apply sumFinRat_congr
      intro j
      have hvj : (v j : Rat) * (v j : Rat) = 1 := sign_sq_one (hv j)
      have h1 : (γ * (u i : Rat) * (v j : Rat)) * (γ * (u i : Rat) * (v j : Rat)) =
          (γ * γ) * ((u i : Rat) * (u i : Rat)) * ((v j : Rat) * (v j : Rat)) := by grind
      have h2 : (W i j - γ * (u i : Rat) * (v j : Rat)) * (W i j - γ * (u i : Rat) * (v j : Rat)) =
          W i j * W i j - (2 * γ * (u i : Rat)) * (W i j * (v j : Rat)) +
          (γ * (u i : Rat) * (v j : Rat)) * (γ * (u i : Rat) * (v j : Rat)) := by grind
      rw [h2, h1, hui, hvj, Rat.mul_one, Rat.mul_one]
    rw [hcongr, sumFinRat_add, sumFinRat_sub, sumFinRat_mul_left, sumFinRat_const]
    grind
  rw [sumFinRat_congr _ _ hexp, sumFinRat_add, sumFinRat_sub, sumFinRat_mul_left, sumFinRat_const]
  have hcast : ((m * n : Nat) : Rat) = (m : Rat) * (n : Rat) := by grind
  rw [hcast]
  grind

/-! ### Main Theorem 1 -/

theorem rank1_onebit_ef21_contraction_exact (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    (∀ W : RatMat m n,
      ∃ u : Fin m → Int, ∃ v : Fin n → Int, isSignVec u ∧ isSignVec v ∧
      ∃ γ : Rat, frobSqErr W (rank1Mat γ u v) ≤
        (1 - 1 / ((m * n : Nat) : Rat)) * frobSq W) ∧
    (∃ W : RatMat m n,
      (0 : Rat) < frobSq W ∧
      ∀ u : Fin m → Int, ∀ v : Fin n → Int, isSignVec u → isSignVec v →
      ∀ γ : Rat,
        (1 - 1 / ((m * n : Nat) : Rat)) * frobSq W ≤ frobSqErr W (rank1Mat γ u v)) := by
  have hmn_pos_nat : 0 < m * n := Nat.mul_pos hm hn
  have hmn_pos : (0 : Rat) < ((m * n : Nat) : Rat) := Rat.natCast_pos.mpr hmn_pos_nat
  have hmn_ne : ((m * n : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hmn_pos
  constructor
  · intro W
    obtain ⟨u, v, hu, hv, hq⟩ := exists_sign_pair_quadForm m n W
    let q : Rat := quadFormRat W u v
    let mn : Rat := ((m * n : Nat) : Rat)
    let γ : Rat := q / mn
    refine ⟨u, v, hu, hv, γ, ?_⟩
    rw [frobSqErr_rank1_sign W u v hu hv γ]
    have h1 : mn * γ = q := by
      dsimp [γ]
      rw [Rat.mul_comm, Rat.div_mul_cancel hmn_ne]
    have hsimp : frobSq W - 2 * γ * q + mn * (γ * γ) = frobSq W - (q * q) / mn := by
      have h2 : mn * (γ * γ) = q * γ := by
        calc mn * (γ * γ) = (mn * γ) * γ := by grind
          _ = q * γ := by rw [h1]
      have h3 : q * γ = (q * q) / mn := by
        dsimp [γ]
        rw [Rat.div_def, Rat.div_def]
        grind
      grind
    rw [hsimp]
    have hdiv : frobSq W / mn ≤ (q * q) / mn := by
      have hinv : (0 : Rat) ≤ mn⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hmn_pos)
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right hq hinv
    have hrhs : (1 - 1 / mn) * frobSq W = frobSq W - frobSq W / mn := by
      rw [Rat.div_def, Rat.div_def]
      grind
    rw [hrhs]
    grind
  · let W : RatMat m n := fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0
    have hfrob : frobSq W = 1 := by
      unfold frobSq
      rw [sumFinRat_single_zero hm]
      · rw [sumFinRat_single_zero hn]
        · simp [W]
        · intro j hj
          simp [W, hj]
      · intro i hi
        have h0 : sumFinRat n (fun j => W i j * W i j) = sumFinRat n (fun _ => 0) := by
          apply sumFinRat_congr
          intro j
          simp [W, hi]
        rw [h0, sumFinRat_zero]
    refine ⟨W, ?_, ?_⟩
    · rw [hfrob]; grind
    · intro u v hu hv γ
      rw [frobSqErr_rank1_sign W u v hu hv γ, hfrob, Rat.mul_one]
      have hq : quadFormRat W u v = (u ⟨0, hm⟩ : Rat) * (v ⟨0, hn⟩ : Rat) := by
        unfold quadFormRat
        rw [sumFinRat_single_zero hm]
        · rw [sumFinRat_single_zero hn]
          · simp [W]
          · intro j hj
            simp [W, hj]
        · intro i hi
          have h0 : sumFinRat n (fun j => W i j * (v j : Rat)) = sumFinRat n (fun _ => 0) := by
            apply sumFinRat_congr
            intro j
            simp [W, hi]
          rw [h0, sumFinRat_zero, Rat.mul_zero]
      rw [hq]
      let s : Rat := (u ⟨0, hm⟩ : Rat) * (v ⟨0, hn⟩ : Rat)
      have hs2 : s * s = 1 := by
        dsimp [s]
        have hu0 := sign_sq_one (hu ⟨0, hm⟩)
        have hv0 := sign_sq_one (hv ⟨0, hn⟩)
        calc ((u ⟨0, hm⟩ : Rat) * (v ⟨0, hn⟩ : Rat)) * ((u ⟨0, hm⟩ : Rat) * (v ⟨0, hn⟩ : Rat))
            = ((u ⟨0, hm⟩ : Rat) * (u ⟨0, hm⟩ : Rat)) * ((v ⟨0, hn⟩ : Rat) * (v ⟨0, hn⟩ : Rat)) := by grind
          _ = 1 * 1 := by rw [hu0, hv0]
          _ = 1 := by grind
      let mn : Rat := ((m * n : Nat) : Rat)
      have hdiff : (1 - 2 * γ * s + mn * (γ * γ)) - (1 - 1 / mn) =
          ((mn * γ - s) * (mn * γ - s)) / mn := by
        have hsq : (mn * γ - s) * (mn * γ - s) = mn * mn * (γ * γ) - 2 * mn * γ * s + 1 := by
          have : (mn * γ - s) * (mn * γ - s) = mn * mn * (γ * γ) - 2 * mn * γ * s + s * s := by grind
          rw [this, hs2]
        rw [hsq]
        have hinv : (1 / mn) * mn = 1 := Rat.div_mul_cancel hmn_ne
        have hmul : (mn * (γ * γ) - 2 * γ * s + 1 / mn) * mn =
            mn * mn * (γ * γ) - 2 * mn * γ * s + 1 := by grind
        have h1 : (mn * mn * (γ * γ) - 2 * mn * γ * s + 1) / mn =
            mn * (γ * γ) - 2 * γ * s + 1 / mn := by
          rw [← hmul, Rat.mul_div_cancel hmn_ne]
        rw [h1]
        grind
      have hnonneg : (0 : Rat) ≤ ((mn * γ - s) * (mn * γ - s)) / mn :=
        rat_div_nonneg (rat_sq_nonneg _) hmn_pos
      rw [← hdiff] at hnonneg
      grind

end LoftqCyclesRank1
