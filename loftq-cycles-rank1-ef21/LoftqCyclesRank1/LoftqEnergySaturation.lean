/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LoftqCyclesRank1.Defs
import LoftqCyclesRank1.Rank1OneBit

/-!
# Theorem 4: LoftQ Monotone Energy Descent, Spiked Separation, and Exact `4M^2` Saturation Law

Proves `loftq_alternating_monotone_energy_and_4m2_saturation`:
1. **Universal Euclidean-Projection LoftQ Lyapunov Monotonicity (`∀ m n`):**
   When both `Q_{t+1} = argmin_{Q ∈ S_Q} ‖(W - L_t) - Q‖_F^2` and
   `L_{t+1} = argmin_{L ∈ S_L} ‖(W - Q_{t+1}) - L‖_F^2` are exact Euclidean projections,
   `‖W - Q_{t+1} - L_{t+1}‖_F^2 ≤ ‖W - Q_{t+1} - L_t‖_F^2 ≤ ‖W - Q_t - L_t‖_F^2`.
2. **Exact Spiked-Matrix Separation (`∀ d ≥ 3, M ≥ 1, k ≥ 2`):**
   On `W = diag(2*M*k, k-1, ..., k-1)`, 1-shot absmax-RTN + rank-1 SVD leaves exact squared
   error `(d - 2) * (k - 1)^2 = Ω(d σ^2 / M^2)`, whereas 2-step alternating LoftQ achieves
   exact squared error `0`.
3. **Exact `4M^2` Saturation Law (`∀ M ≥ 1`):**
   - Exact uniform-bulk variance ratio `uniformBulkVarianceRatio M = 4 * M^2`
     (`4` for ternary `M = 1`, `36` for INT3 `M = 3`, `196` for INT4 `M = 7`).
   - Exact worst-case per-entry discrete-grid error barrier on `[-1, 1]` at scale `1 / M`:
     for all `x` with `|x| ≤ 1`, `(absmaxQuantAtScale M (1/M) x - x)^2 ≤ 1 / (4 M^2)`,
     with exact attainment at `x = 1 / (2 M)`.
-/

namespace LoftqCyclesRank1

/-! ### Part 1: Universal Euclidean-Projection LoftQ Monotone Energy -/

theorem frobSqErr_matAdd_comm_sub_left {m n : Nat} (W Q L : RatMat m n) :
    frobSqErr W (matAdd Q L) = frobSqErr (matSub W L) Q := by
  unfold frobSqErr frobSq matAdd matSub
  apply sumFinRat_congr; intro i
  apply sumFinRat_congr; intro j
  grind

theorem frobSqErr_matAdd_comm_sub_right {m n : Nat} (W Q L : RatMat m n) :
    frobSqErr W (matAdd Q L) = frobSqErr (matSub W Q) L := by
  unfold frobSqErr frobSq matAdd matSub
  apply sumFinRat_congr; intro i
  apply sumFinRat_congr; intro j
  grind

theorem loftq_euclid_monotone {m n : Nat} (W Q_t Q_next L_t L_next : RatMat m n)
    (S_Q S_L : RatMat m n → Prop)
    (hQt : S_Q Q_t) (hLt : S_L L_t)
    (hQnext : isBestApprox S_Q (matSub W L_t) Q_next)
    (hLnext : isBestApprox S_L (matSub W Q_next) L_next) :
    frobSqErr W (matAdd Q_next L_next) ≤ frobSqErr W (matAdd Q_next L_t) ∧
    frobSqErr W (matAdd Q_next L_t) ≤ frobSqErr W (matAdd Q_t L_t) := by
  constructor
  · rw [frobSqErr_matAdd_comm_sub_right W Q_next L_next,
        frobSqErr_matAdd_comm_sub_right W Q_next L_t]
    exact hLnext.2 L_t hLt
  · rw [frobSqErr_matAdd_comm_sub_left W Q_next L_t,
        frobSqErr_matAdd_comm_sub_left W Q_t L_t]
    exact hQnext.2 Q_t hQt

/-! ### Part 2: Exact `roundHalfUp` Properties and Spiked-Matrix Separation -/

theorem rat_intCast_natCast (n : Nat) : ((n : Int) : Rat) = (n : Rat) := rfl

theorem rat_eq_num_div_den (x : Rat) : x = (x.num : Rat) / (x.den : Rat) := by
  rw [← rat_intCast_natCast, ← Rat.divInt_eq_div]
  cases x with
  | mk' num den den_nz reduced =>
    simp [Rat.divInt, mkRat, Rat.normalize, den_nz, reduced]

theorem intCast_rat_le_iff (a b : Int) : (a : Rat) ≤ (b : Rat) ↔ a ≤ b :=
  Rat.intCast_le_intCast

theorem intCast_rat_lt_iff (a b : Int) : (a : Rat) < (b : Rat) ↔ a < b :=
  Rat.intCast_lt_intCast

theorem rat_num_neg_of_lt_zero {x : Rat} (hx : x < 0) : x.num < 0 := by
  have hq := rat_eq_num_div_den x
  have hden_r : (0 : Rat) < (x.den : Rat) := Rat.natCast_pos.mpr x.den_pos
  rw [hq] at hx
  have hm := Rat.mul_lt_mul_of_pos_right hx hden_r
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hden_r), Rat.zero_mul] at hm
  exact (intCast_rat_lt_iff x.num 0).mp hm

theorem roundHalfUp_intCast (z : Int) : roundHalfUp (z : Rat) = z := by
  unfold roundHalfUp
  have hnum : (z : Rat).num = z := rfl
  have hden : (z : Rat).den = 1 := rfl
  rw [hnum, hden]
  split
  · rename_i hge
    have hz : 0 ≤ z := (intCast_rat_le_iff 0 z).mp hge
    omega
  · rename_i hlt
    have hz : z < 0 := (intCast_rat_lt_iff z 0).mp (Rat.not_le.mp hlt)
    omega

theorem roundHalfUp_eq_zero_of_nonneg_lt_half {x : Rat} (h0 : 0 ≤ x) (h1 : x < 1 / 2) :
    roundHalfUp x = 0 := by
  unfold roundHalfUp
  simp only [h0, ↓reduceIte]
  have hden_pos : (0 : Int) < (x.den : Int) := Int.natCast_pos.mpr x.den_pos
  have hnum_nn : 0 ≤ x.num := Rat.num_nonneg.mpr h0
  have hnum_lt : 2 * x.num < (x.den : Int) := by
    have hq := rat_eq_num_div_den x
    have hden_r : (0 : Rat) < (x.den : Rat) := Rat.natCast_pos.mpr x.den_pos
    rw [hq] at h1
    have hmul := Rat.mul_lt_mul_of_pos_right h1 hden_r
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hden_r)] at hmul
    have h2 : ((2 * x.num : Int) : Rat) < ((x.den : Int) : Rat) := by
      rw [rat_intCast_natCast]; grind
    exact (intCast_rat_lt_iff _ _).mp h2
  have hdiv := Int.mul_ediv_add_emod (2 * x.num + (x.den : Int)) (2 * (x.den : Int))
  have hmod_nn : 0 ≤ (2 * x.num + (x.den : Int)) % (2 * (x.den : Int)) :=
    Int.emod_nonneg _ (by omega)
  have hmod_lt : (2 * x.num + (x.den : Int)) % (2 * (x.den : Int)) < 2 * (x.den : Int) :=
    Int.emod_lt_of_pos _ (by omega)
  have hlt_den : 2 * x.num + (x.den : Int) < 2 * (x.den : Int) := by omega
  have hnn_num : 0 ≤ 2 * x.num + (x.den : Int) := by omega
  have hq_eq : (2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) = 0 := by
    have hq0 : (2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) ≤ 0 := by
      exact Classical.byContradiction fun h => by
        have hge1 : 1 ≤ (2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) := by omega
        have hm : 2 * (x.den : Int) * 1 ≤ 2 * (x.den : Int) * ((2 * x.num + (x.den : Int)) / (2 * (x.den : Int))) :=
          Int.mul_le_mul_of_nonneg_left hge1 (by omega)
        omega
    have hq1 : 0 ≤ (2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) :=
      Int.ediv_nonneg hnn_num (by omega)
    omega
  exact hq_eq

theorem roundHalfUp_dist_le_half (x : Rat) :
    ((roundHalfUp x : Rat) - x) * ((roundHalfUp x : Rat) - x) ≤ 1 / 4 := by
  have hden_pos : (0 : Int) < (x.den : Int) := Int.natCast_pos.mpr x.den_pos
  have hden_r_pos : (0 : Rat) < (x.den : Rat) := Rat.natCast_pos.mpr x.den_pos
  have hden_ne : (x.den : Rat) ≠ 0 := Rat.ne_of_gt hden_r_pos
  have hq := rat_eq_num_div_den x
  have hbound : -(x.den : Int) ≤ 2 * (roundHalfUp x * (x.den : Int) - x.num) ∧
                2 * (roundHalfUp x * (x.den : Int) - x.num) ≤ (x.den : Int) := by
    unfold roundHalfUp
    split
    · rename_i hge
      have hdiv := Int.mul_ediv_add_emod (2 * x.num + (x.den : Int)) (2 * (x.den : Int))
      have hmod_nn : 0 ≤ (2 * x.num + (x.den : Int)) % (2 * (x.den : Int)) :=
        Int.emod_nonneg _ (by omega)
      have hmod_lt : (2 * x.num + (x.den : Int)) % (2 * (x.den : Int)) < 2 * (x.den : Int) :=
        Int.emod_lt_of_pos _ (by omega)
      have hcomm : 2 * ((2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) * (x.den : Int)) =
          2 * (x.den : Int) * ((2 * x.num + (x.den : Int)) / (2 * (x.den : Int))) := by grind
      omega
    · rename_i hlt
      have hdiv := Int.mul_ediv_add_emod (2 * (-x.num) + (x.den : Int)) (2 * (x.den : Int))
      have hmod_nn : 0 ≤ (2 * (-x.num) + (x.den : Int)) % (2 * (x.den : Int)) :=
        Int.emod_nonneg _ (by omega)
      have hmod_lt : (2 * (-x.num) + (x.den : Int)) % (2 * (x.den : Int)) < 2 * (x.den : Int) :=
        Int.emod_lt_of_pos _ (by omega)
      have hcomm : 2 * (-((2 * (-x.num) + (x.den : Int)) / (2 * (x.den : Int))) * (x.den : Int)) =
          -(2 * (x.den : Int) * ((2 * (-x.num) + (x.den : Int)) / (2 * (x.den : Int)))) := by grind
      omega
  let errInt : Int := 2 * (roundHalfUp x * (x.den : Int) - x.num)
  have herr_sq : errInt * errInt ≤ (x.den : Int) * (x.den : Int) := by
    have h1 : 0 ≤ ((x.den : Int) - errInt) * ((x.den : Int) + errInt) :=
      Int.mul_nonneg (by omega) (by omega)
    have h2 : ((x.den : Int) - errInt) * ((x.den : Int) + errInt) =
        (x.den : Int) * (x.den : Int) - errInt * errInt := by grind
    omega
  have herr_sq_r : (errInt : Rat) * (errInt : Rat) ≤ (x.den : Rat) * (x.den : Rat) := by
    have h := (intCast_rat_le_iff (errInt * errInt) ((x.den : Int) * (x.den : Int))).mpr herr_sq
    have hL : ((errInt * errInt : Int) : Rat) = (errInt : Rat) * (errInt : Rat) := by grind
    have hR : (((x.den : Int) * (x.den : Int) : Int) : Rat) = (x.den : Rat) * (x.den : Rat) := by
      have h1 : (((x.den : Int) * (x.den : Int) : Int) : Rat) = ((x.den : Int) : Rat) * ((x.den : Int) : Rat) := by grind
      rw [h1, rat_intCast_natCast]
    rw [hL, hR] at h
    exact h
  have hrel : (errInt : Rat) = 2 * (x.den : Rat) * ((roundHalfUp x : Rat) - x) := by
    have hmul : (x.den : Rat) * ((roundHalfUp x : Rat) - x) =
        (roundHalfUp x : Rat) * (x.den : Rat) - (x.num : Rat) := by
      have hdiv_cancel : (x.den : Rat) * x = (x.num : Rat) := by
        calc (x.den : Rat) * x = x * (x.den : Rat) := Rat.mul_comm _ _
          _ = ((x.num : Rat) / (x.den : Rat)) * (x.den : Rat) := by rw [← hq]
          _ = (x.num : Rat) := Rat.div_mul_cancel hden_ne
      grind
    have he : (errInt : Rat) = 2 * ((roundHalfUp x : Rat) * (x.den : Rat) - (x.num : Rat)) := by
      dsimp [errInt]
      have h1 : ((2 * (roundHalfUp x * (x.den : Int) - x.num) : Int) : Rat) =
          2 * ((roundHalfUp x : Rat) * ((x.den : Int) : Rat) - (x.num : Rat)) := by grind
      rw [h1, rat_intCast_natCast]
    rw [he, ← hmul]; grind
  rw [hrel] at herr_sq_r
  have hd2_pos : (0 : Rat) < 4 * ((x.den : Rat) * (x.den : Rat)) := by
    have := Rat.mul_pos hden_r_pos hden_r_pos
    grind
  have hfac : (2 * (x.den : Rat) * ((roundHalfUp x : Rat) - x)) *
              (2 * (x.den : Rat) * ((roundHalfUp x : Rat) - x)) =
      4 * ((x.den : Rat) * (x.den : Rat)) * (((roundHalfUp x : Rat) - x) * ((roundHalfUp x : Rat) - x)) := by
    grind
  rw [hfac] at herr_sq_r
  have hinv := Rat.le_of_lt (Rat.inv_pos.mpr hd2_pos)
  have hm := Rat.mul_le_mul_of_nonneg_left herr_sq_r hinv
  have hL : (4 * ((x.den : Rat) * (x.den : Rat)))⁻¹ *
      (4 * ((x.den : Rat) * (x.den : Rat)) * (((roundHalfUp x : Rat) - x) * ((roundHalfUp x : Rat) - x))) =
      ((roundHalfUp x : Rat) - x) * ((roundHalfUp x : Rat) - x) := by
    have hne : 4 * ((x.den : Rat) * (x.den : Rat)) ≠ 0 := Rat.ne_of_gt hd2_pos
    have h1 := Rat.inv_mul_cancel _ hne
    grind
  have hR : (4 * ((x.den : Rat) * (x.den : Rat)))⁻¹ * ((x.den : Rat) * (x.den : Rat)) = 1 / 4 := by
    have hne : 4 * ((x.den : Rat) * (x.den : Rat)) ≠ 0 := Rat.ne_of_gt hd2_pos
    have h1 := Rat.inv_mul_cancel _ hne
    grind
  rw [hL, hR] at hm
  exact hm

theorem roundHalfUp_bound_of_abs_le {M : Nat} {x : Rat} (hx : absRat x ≤ (M : Rat)) :
    -(M : Int) ≤ roundHalfUp x ∧ roundHalfUp x ≤ (M : Int) := by
  have hden_pos : (0 : Int) < (x.den : Int) := Int.natCast_pos.mpr x.den_pos
  have hden_r_pos : (0 : Rat) < (x.den : Rat) := Rat.natCast_pos.mpr x.den_pos
  have hden_ne : (x.den : Rat) ≠ 0 := Rat.ne_of_gt hden_r_pos
  have hq := rat_eq_num_div_den x
  have hle_M : x ≤ (M : Rat) := by
    unfold absRat at hx; split at hx <;> grind
  have hge_M : -(M : Rat) ≤ x := by
    unfold absRat at hx; split at hx <;> grind
  have hnum_le : x.num ≤ (M : Int) * (x.den : Int) := by
    rw [hq] at hle_M
    have hm := Rat.mul_le_mul_of_nonneg_right hle_M (Rat.le_of_lt hden_r_pos)
    rw [Rat.div_mul_cancel hden_ne] at hm
    have hcast : (((M : Int) * (x.den : Int) : Int) : Rat) = (M : Rat) * (x.den : Rat) := by
      have h1 : (((M : Int) * (x.den : Int) : Int) : Rat) = ((M : Int) : Rat) * ((x.den : Int) : Rat) := by grind
      rw [h1, rat_intCast_natCast, rat_intCast_natCast]
    exact (intCast_rat_le_iff _ _).mp (by rw [hcast]; exact hm)
  have hnum_ge : -(M : Int) * (x.den : Int) ≤ x.num := by
    rw [hq] at hge_M
    have hm := Rat.mul_le_mul_of_nonneg_right hge_M (Rat.le_of_lt hden_r_pos)
    rw [Rat.div_mul_cancel hden_ne] at hm
    have hcast : ((-(M : Int) * (x.den : Int) : Int) : Rat) = -(M : Rat) * (x.den : Rat) := by
      have h1 : ((-(M : Int) * (x.den : Int) : Int) : Rat) = -((M : Int) : Rat) * ((x.den : Int) : Rat) := by grind
      rw [h1, rat_intCast_natCast, rat_intCast_natCast]
    exact (intCast_rat_le_iff _ _).mp (by rw [hcast]; exact hm)
  unfold roundHalfUp
  split
  · rename_i hge
    have hnn : 0 ≤ x.num := Rat.num_nonneg.mpr hge
    have hdiv := Int.mul_ediv_add_emod (2 * x.num + (x.den : Int)) (2 * (x.den : Int))
    have hmod_nn : 0 ≤ (2 * x.num + (x.den : Int)) % (2 * (x.den : Int)) :=
      Int.emod_nonneg _ (by omega)
    have hq_nn : 0 ≤ (2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) :=
      Int.ediv_nonneg (by omega) (by omega)
    have hq_le : (2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) ≤ (M : Int) := by
      exact Classical.byContradiction fun h => by
        have hgt : (M : Int) + 1 ≤ (2 * x.num + (x.den : Int)) / (2 * (x.den : Int)) := by omega
        have hm : 2 * (x.den : Int) * ((M : Int) + 1) ≤
            2 * (x.den : Int) * ((2 * x.num + (x.den : Int)) / (2 * (x.den : Int))) :=
          Int.mul_le_mul_of_nonneg_left hgt (by omega)
        have hmul_eq : 2 * (x.den : Int) * ((M : Int) + 1) = 2 * ((M : Int) * (x.den : Int)) + 2 * (x.den : Int) := by grind
        have hneg_eq : -(M : Int) * (x.den : Int) = -((M : Int) * (x.den : Int)) := by grind
        omega
    omega
  · rename_i hlt
    have hneg : x.num < 0 := rat_num_neg_of_lt_zero (Rat.not_le.mp hlt)
    have hdiv := Int.mul_ediv_add_emod (2 * (-x.num) + (x.den : Int)) (2 * (x.den : Int))
    have hmod_nn : 0 ≤ (2 * (-x.num) + (x.den : Int)) % (2 * (x.den : Int)) :=
      Int.emod_nonneg _ (by omega)
    have hq_nn : 0 ≤ (2 * (-x.num) + (x.den : Int)) / (2 * (x.den : Int)) :=
      Int.ediv_nonneg (by omega) (by omega)
    have hq_le : (2 * (-x.num) + (x.den : Int)) / (2 * (x.den : Int)) ≤ (M : Int) := by
      exact Classical.byContradiction fun h => by
        have hgt : (M : Int) + 1 ≤ (2 * (-x.num) + (x.den : Int)) / (2 * (x.den : Int)) := by omega
        have hm : 2 * (x.den : Int) * ((M : Int) + 1) ≤
            2 * (x.den : Int) * ((2 * (-x.num) + (x.den : Int)) / (2 * (x.den : Int))) :=
          Int.mul_le_mul_of_nonneg_left hgt (by omega)
        have hmul_eq : 2 * (x.den : Int) * ((M : Int) + 1) = 2 * ((M : Int) * (x.den : Int)) + 2 * (x.den : Int) := by grind
        have hneg_eq : -(M : Int) * (x.den : Int) = -((M : Int) * (x.den : Int)) := by grind
        omega
    omega

theorem absmaxQuantAtScale_unit_err_bound (M : Nat) (hM : 0 < M) (x : Rat) (hx : absRat x ≤ 1) :
    (absmaxQuantAtScale M (1 / (M : Rat)) x - x) * (absmaxQuantAtScale M (1 / (M : Rat)) x - x) ≤
      1 / (4 * (M : Rat) * (M : Rat)) := by
  have hM_pos : (0 : Rat) < (M : Rat) := Rat.natCast_pos.mpr hM
  have hM_ne : (M : Rat) ≠ 0 := Rat.ne_of_gt hM_pos
  have hs_pos : (0 : Rat) < 1 / (M : Rat) := by
    rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr hM_pos
  have hs_nle : ¬ (1 / (M : Rat) ≤ 0) := Rat.not_le.mpr hs_pos
  unfold absmaxQuantAtScale
  simp only [hs_nle, ↓reduceIte]
  have hdiv_eq : x / (1 / (M : Rat)) = (M : Rat) * x := by
    rw [Rat.div_def, Rat.div_def, Rat.one_mul, Rat.inv_inv]; grind
  rw [hdiv_eq]
  have habs_Mx : absRat ((M : Rat) * x) ≤ (M : Rat) := by
    unfold absRat at hx ⊢
    by_cases hx0 : x < 0
    · have hMx0 : (M : Rat) * x < 0 := by
        have := Rat.mul_lt_mul_of_pos_left hx0 hM_pos
        simpa [Rat.mul_zero] using this
      simp only [hx0, ↓reduceIte] at hx
      simp only [hMx0, ↓reduceIte]
      have := Rat.mul_le_mul_of_nonneg_left hx (Rat.le_of_lt hM_pos)
      grind
    · have hMx0 : ¬ ((M : Rat) * x < 0) := by
        have hxge : 0 ≤ x := Rat.not_lt.mp hx0
        exact Rat.not_lt.mpr (Rat.mul_nonneg (Rat.le_of_lt hM_pos) hxge)
      simp only [hx0, ↓reduceIte] at hx
      simp only [hMx0, ↓reduceIte]
      have := Rat.mul_le_mul_of_nonneg_left hx (Rat.le_of_lt hM_pos)
      grind
  have ⟨hcl1, hcl2⟩ := roundHalfUp_bound_of_abs_le habs_Mx
  have hclamp : max (-(M : Int)) (min (M : Int) (roundHalfUp ((M : Rat) * x))) =
      roundHalfUp ((M : Rat) * x) := by omega
  rw [hclamp]
  have herr := roundHalfUp_dist_le_half ((M : Rat) * x)
  have hfactor : ((roundHalfUp ((M : Rat) * x) : Rat) * (1 / (M : Rat)) - x) *
                 ((roundHalfUp ((M : Rat) * x) : Rat) * (1 / (M : Rat)) - x) =
      (((roundHalfUp ((M : Rat) * x) : Rat) - (M : Rat) * x) *
       ((roundHalfUp ((M : Rat) * x) : Rat) - (M : Rat) * x)) / ((M : Rat) * (M : Rat)) := by
    have h1 : (roundHalfUp ((M : Rat) * x) : Rat) * (1 / (M : Rat)) - x =
        ((roundHalfUp ((M : Rat) * x) : Rat) - (M : Rat) * x) / (M : Rat) := by
      rw [Rat.div_def, Rat.div_def]
      have hinv : (M : Rat) * (M : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ hM_ne
      grind
    rw [h1, Rat.div_def, Rat.div_def]
    have hinv2 : ((M : Rat) * (M : Rat))⁻¹ = (M : Rat)⁻¹ * (M : Rat)⁻¹ := by
      have hne2 : (M : Rat) * (M : Rat) ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hM_pos hM_pos)
      have h1 := Rat.mul_inv_cancel _ hM_ne
      have h2 := Rat.mul_inv_cancel _ hne2
      grind
    rw [hinv2]; grind
  rw [hfactor]
  have hM2_pos : (0 : Rat) < (M : Rat) * (M : Rat) := Rat.mul_pos hM_pos hM_pos
  have hinv_nn : (0 : Rat) ≤ ((M : Rat) * (M : Rat))⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hM2_pos)
  rw [Rat.div_def]
  have hm := Rat.mul_le_mul_of_nonneg_right herr hinv_nn
  have hR : (1 / 4 : Rat) * ((M : Rat) * (M : Rat))⁻¹ = 1 / (4 * (M : Rat) * (M : Rat)) := by
    have h4M2_ne : 4 * (M : Rat) * (M : Rat) ≠ 0 := by
      have : 0 < 4 * (M : Rat) * (M : Rat) := by grind
      exact Rat.ne_of_gt this
    have hM2_ne : (M : Rat) * (M : Rat) ≠ 0 := Rat.ne_of_gt hM2_pos
    have h1 := Rat.mul_inv_cancel _ h4M2_ne
    have h2 := Rat.mul_inv_cancel _ hM2_ne
    rw [Rat.div_def, Rat.div_def]
    grind
  rw [hR] at hm
  exact hm

theorem absmaxQuantAtScale_unit_err_attained (M : Nat) (hM : 0 < M) :
    let x : Rat := 1 / (2 * (M : Rat))
    absRat x ≤ 1 ∧
    (absmaxQuantAtScale M (1 / (M : Rat)) x - x) * (absmaxQuantAtScale M (1 / (M : Rat)) x - x) =
      1 / (4 * (M : Rat) * (M : Rat)) := by
  have hM_pos : (0 : Rat) < (M : Rat) := Rat.natCast_pos.mpr hM
  have hM_ne : (M : Rat) ≠ 0 := Rat.ne_of_gt hM_pos
  have h2M_pos : (0 : Rat) < 2 * (M : Rat) := by grind
  have h2M_ne : 2 * (M : Rat) ≠ 0 := Rat.ne_of_gt h2M_pos
  have hs_pos : (0 : Rat) < 1 / (M : Rat) := by
    rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr hM_pos
  have hs_nle : ¬ (1 / (M : Rat) ≤ 0) := Rat.not_le.mpr hs_pos
  have hx_pos : (0 : Rat) < 1 / (2 * (M : Rat)) := by
    rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr h2M_pos
  have hx_le1 : 1 / (2 * (M : Rat)) ≤ 1 := by
    have hge : (1 : Rat) ≤ 2 * (M : Rat) := by
      have h1 : (1 : Rat) ≤ (M : Rat) := (intCast_rat_le_iff 1 (M : Int)).mpr (by omega)
      grind
    have hinv := Rat.le_of_lt (Rat.inv_pos.mpr h2M_pos)
    have hm := Rat.mul_le_mul_of_nonneg_right hge hinv
    rw [Rat.mul_inv_cancel _ h2M_ne, Rat.one_mul] at hm
    rw [Rat.div_def, Rat.one_mul]; exact hm
  constructor
  · unfold absRat
    have hnl : ¬ (1 / (2 * (M : Rat)) < 0) := Rat.not_lt.mpr (Rat.le_of_lt hx_pos)
    simp only [hnl, ↓reduceIte]
    exact hx_le1
  · unfold absmaxQuantAtScale
    simp only [hs_nle, ↓reduceIte]
    have hdiv_eq : (1 / (2 * (M : Rat))) / (1 / (M : Rat)) = (1 / 2 : Rat) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul, Rat.inv_inv]
      have h1 := Rat.mul_inv_cancel _ h2M_ne
      have h2 := Rat.mul_inv_cancel _ hM_ne
      grind
    rw [hdiv_eq]
    have hr : roundHalfUp (1 / 2 : Rat) = 1 := by
      have h12 : (1 / 2 : Rat) = Rat.mk' 1 2 (by decide) (by decide) := by
        have h := Rat.divInt_eq_div 1 2
        have h1 : Rat.divInt 1 2 = Rat.mk' 1 2 (by decide) (by decide) := by decide
        rw [← h1, h]; grind
      rw [h12]
      unfold roundHalfUp
      have hnn : (0 : Rat) ≤ Rat.mk' 1 2 (by decide) (by decide) := by
        rw [← h12]; grind
      simp only [hnn, ↓reduceIte]
      decide
    rw [hr]
    have hcl : max (-(M : Int)) (min (M : Int) 1) = 1 := by omega
    rw [hcl]
    have hsub : ((1 : Int) : Rat) * (1 / (M : Rat)) - 1 / (2 * (M : Rat)) = 1 / (2 * (M : Rat)) := by
      rw [Rat.div_def, Rat.div_def]
      have h1 := Rat.mul_inv_cancel _ h2M_ne
      have h2 := Rat.mul_inv_cancel _ hM_ne
      grind
    rw [hsub]
    have h4M2_ne : 4 * (M : Rat) * (M : Rat) ≠ 0 := by
      have : 0 < 4 * (M : Rat) * (M : Rat) := by
        have := Rat.mul_pos hM_pos hM_pos; grind
      exact Rat.ne_of_gt this
    have h1 := Rat.mul_inv_cancel _ h2M_ne
    have h2 := Rat.mul_inv_cancel _ h4M2_ne
    rw [Rat.div_def, Rat.div_def]
    grind

theorem diagMat_frobSq {d : Nat} (v : Fin d → Rat) :
    frobSq (diagMat v) = sumFinRat d (fun i => v i * v i) := by
  unfold frobSq diagMat
  apply sumFinRat_congr
  intro i
  have hsingle : ∀ (n : Nat) (f : Fin n → Rat) (k : Fin n),
      (∀ j : Fin n, j ≠ k → f j = 0) → sumFinRat n f = f k := by
    intro n
    induction n with
    | zero => intro _ k; exact Fin.elim0 k
    | succ m ih =>
      intro f k h0
      simp only [sumFinRat]
      by_cases hk : k = Fin.last m
      · subst hk
        have hzero : sumFinRat m (fun j => f j.castSucc) = 0 := by
          rw [sumFinRat_congr (fun j => f j.castSucc) (fun _ => 0)]
          · exact sumFinRat_zero m
          · intro j
            apply h0
            intro heq
            have hv := congrArg Fin.val heq
            simp at hv
            omega
        rw [hzero, Rat.zero_add]
      · have hlast : f (Fin.last m) = 0 := h0 (Fin.last m) (Ne.symm hk)
        rw [hlast, Rat.add_zero]
        have hklt : k.val < m := by
          have := k.isLt
          have hne : k.val ≠ m := fun h => hk (Fin.ext h)
          omega
        let k' : Fin m := ⟨k.val, hklt⟩
        have hcast : k'.castSucc = k := Fin.ext rfl
        rw [ih (fun j => f j.castSucc) k']
        · rw [hcast]
        · intro j hj
          apply h0
          intro heq
          apply hj
          apply Fin.ext
          have := congrArg Fin.val heq
          simpa using this
  rw [hsingle d (fun j => (if i = j then v i else 0) * (if i = j then v i else 0)) i]
  · simp
  · intro j hj
    have hne : i ≠ j := Ne.symm hj
    simp [hne]

theorem sumFinRat_skip2 (n : Nat) (hn : 2 ≤ n) (c : Rat) :
    sumFinRat n (fun i : Fin n => if i.val = 0 ∨ i.val = 1 then (0 : Rat) else c) =
    ((n - 2 : Nat) : Rat) * c := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 1
    · subst hm
      simp only [sumFinRat, Fin.val_castSucc, Fin.val_last, ↓reduceIte, true_or, or_true]
      grind
    · have hm2 : 2 ≤ m := by omega
      simp only [sumFinRat]
      have hlast : ¬ ((Fin.last m).val = 0 ∨ (Fin.last m).val = 1) := by
        simp; omega
      simp only [hlast, ↓reduceIte]
      have hprev : sumFinRat m (fun i : Fin m => if i.castSucc.val = 0 ∨ i.castSucc.val = 1 then (0 : Rat) else c) =
          ((m - 2 : Nat) : Rat) * c := ih hm2
      rw [hprev]
      have hsub : m + 1 - 2 = (m - 2) + 1 := by omega
      rw [hsub]
      have hcast : (((m - 2) + 1 : Nat) : Rat) = ((m - 2 : Nat) : Rat) + 1 := by grind
      rw [hcast]; grind

theorem spiked_separation_exact (d M k : Nat) (hd : 3 ≤ d) (hM : 0 < M) (hk : 2 ≤ k) :
    let W := spikedDiag d M k
    let s1 : Rat := (2 * k : Rat)
    let Q1 : RatMat d d := fun i j => absmaxQuantAtScale M s1 (W i j)
    let L1 : RatMat d d := diagMat (fun i => if i.val = 1 then ((k - 1 : Nat) : Rat) else 0)
    let Lalt : RatMat d d := diagMat (fun i => if i.val = 0 then (2 * M * k : Rat) else 0)
    let s2 : Rat := ((k - 1 : Nat) : Rat) / (M : Rat)
    let Qalt : RatMat d d := fun i j => absmaxQuantAtScale M s2 (matSub W Lalt i j)
    frobSqErr W (matAdd Q1 L1) =
      ((d - 2 : Nat) : Rat) * (((k - 1 : Nat) : Rat) * ((k - 1 : Nat) : Rat)) ∧
    frobSqErr W (matAdd Qalt Lalt) = 0 := by
  intro W s1 Q1 L1 Lalt s2 Qalt
  have hM_pos : (0 : Rat) < (M : Rat) := Rat.natCast_pos.mpr hM
  have hM_ne : (M : Rat) ≠ 0 := Rat.ne_of_gt hM_pos
  have hk_pos : (0 : Rat) < (k : Rat) := Rat.natCast_pos.mpr (by omega)
  have hs1_pos : (0 : Rat) < s1 := by dsimp [s1]; grind
  have hs1_nle : ¬ (s1 ≤ 0) := Rat.not_le.mpr hs1_pos
  have hs1_ne : s1 ≠ 0 := Rat.ne_of_gt hs1_pos
  have hkm1_pos : (0 : Rat) < ((k - 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have hs2_pos : (0 : Rat) < s2 := by
    dsimp [s2]; rw [Rat.div_def]; exact Rat.mul_pos hkm1_pos (Rat.inv_pos.mpr hM_pos)
  have hs2_nle : ¬ (s2 ≤ 0) := Rat.not_le.mpr hs2_pos
  have hq_zero : ∀ s, absmaxQuantAtScale M s 0 = 0 := by
    intro s
    unfold absmaxQuantAtScale
    split
    · rfl
    · have h0 : (0 : Rat) / s = 0 := by rw [Rat.div_def, Rat.zero_mul]
      rw [h0]
      have hr0 : roundHalfUp 0 = 0 := roundHalfUp_intCast 0
      dsimp only
      rw [hr0]
      have hcl : max (-(M : Int)) (min (M : Int) 0) = 0 := by omega
      rw [hcl]; grind
  have hq1_spike : absmaxQuantAtScale M s1 (2 * M * k : Rat) = (2 * M * k : Rat) := by
    unfold absmaxQuantAtScale
    simp only [hs1_nle, ↓reduceIte]
    have hdiv : (2 * (M : Rat) * (k : Rat)) / s1 = ((M : Int) : Rat) := by
      rw [rat_intCast_natCast]
      dsimp [s1]
      have : (2 * (M : Rat) * (k : Rat)) = (M : Rat) * (2 * (k : Rat)) := by grind
      rw [this, Rat.mul_div_cancel hs1_ne]
    have hcast : (2 * M * k : Rat) = 2 * (M : Rat) * (k : Rat) := by grind
    rw [hcast, hdiv, roundHalfUp_intCast]
    have hcl : max (-(M : Int)) (min (M : Int) (M : Int)) = (M : Int) := by omega
    rw [hcl, rat_intCast_natCast]; dsimp [s1]; grind
  have hq1_bulk : absmaxQuantAtScale M s1 ((k - 1 : Nat) : Rat) = 0 := by
    unfold absmaxQuantAtScale
    simp only [hs1_nle, ↓reduceIte]
    have hnn : 0 ≤ ((k - 1 : Nat) : Rat) / s1 := rat_div_nonneg (Rat.le_of_lt hkm1_pos) hs1_pos
    have hlt : ((k - 1 : Nat) : Rat) / s1 < 1 / 2 := by
      have hkm1_eq : ((k - 1 : Nat) : Rat) = (k : Rat) - 1 := by
        have h : (k - 1) + 1 = k := by omega
        have hc : (((k - 1) + 1 : Nat) : Rat) = (k : Rat) := by rw [h]
        grind
      rw [hkm1_eq]
      dsimp [s1]
      have h2k_pos : (0 : Rat) < 2 * (k : Rat) := by grind
      have hinv := Rat.inv_pos.mpr h2k_pos
      have h1 : (k : Rat) - 1 < (k : Rat) := by grind
      have hm := Rat.mul_lt_mul_of_pos_right h1 hinv
      have hR : (k : Rat) * (2 * (k : Rat))⁻¹ = 1 / 2 := by
        have h2k_ne : 2 * (k : Rat) ≠ 0 := Rat.ne_of_gt h2k_pos
        have := Rat.mul_inv_cancel _ h2k_ne
        rw [Rat.div_def]; grind
      rw [hR] at hm
      rw [Rat.div_def]
      exact hm
    rw [roundHalfUp_eq_zero_of_nonneg_lt_half hnn hlt]
    have hcl : max (-(M : Int)) (min (M : Int) 0) = 0 := by omega
    rw [hcl]; grind
  have hq2_bulk : absmaxQuantAtScale M s2 ((k - 1 : Nat) : Rat) = ((k - 1 : Nat) : Rat) := by
    unfold absmaxQuantAtScale
    simp only [hs2_nle, ↓reduceIte]
    have hdiv : ((k - 1 : Nat) : Rat) / s2 = ((M : Int) : Rat) := by
      rw [rat_intCast_natCast]
      dsimp [s2]
      have hkm1_ne : ((k - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hkm1_pos
      have h1 := Rat.mul_inv_cancel _ hkm1_ne
      have h2 := Rat.mul_inv_cancel _ hM_ne
      rw [Rat.div_def, Rat.div_def]
      have hinv : (((k - 1 : Nat) : Rat) * (M : Rat)⁻¹)⁻¹ = (((k - 1 : Nat) : Rat))⁻¹ * (M : Rat) := by
        have hne : ((k - 1 : Nat) : Rat) * (M : Rat)⁻¹ ≠ 0 := Rat.ne_of_gt hs2_pos
        have h3 := Rat.mul_inv_cancel _ hne
        grind
      rw [hinv]; grind
    rw [hdiv, roundHalfUp_intCast]
    have hcl : max (-(M : Int)) (min (M : Int) (M : Int)) = (M : Int) := by omega
    rw [hcl, rat_intCast_natCast]; dsimp [s2]
    rw [Rat.mul_comm, Rat.div_mul_cancel hM_ne]
  constructor
  · let res1 : Fin d → Rat := fun i => if i.val = 0 ∨ i.val = 1 then 0 else ((k - 1 : Nat) : Rat)
    have hres1 : matSub W (matAdd Q1 L1) = diagMat res1 := by
      funext i j
      simp only [matSub, matAdd, W, spikedDiag, Q1, L1, diagMat, res1]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        by_cases h0 : i.val = 0
        · simp only [h0, ↓reduceIte, true_or, Nat.zero_ne_one]
          rw [hq1_spike]; grind
        · by_cases h1 : i.val = 1
          · simp only [h1, ↓reduceIte, or_true, Nat.one_ne_zero]
            rw [hq1_bulk]; grind
          · simp only [h0, h1, ↓reduceIte, or_self]
            rw [hq1_bulk]; grind
      · simp only [hij, ↓reduceIte]
        rw [hq_zero]; grind
    unfold frobSqErr
    rw [hres1, diagMat_frobSq]
    let c : Rat := ((k - 1 : Nat) : Rat) * ((k - 1 : Nat) : Rat)
    have hcongr : sumFinRat d (fun i => res1 i * res1 i) =
        sumFinRat d (fun i : Fin d => if i.val = 0 ∨ i.val = 1 then (0 : Rat) else c) := by
      apply sumFinRat_congr
      intro i
      dsimp only [res1, c]
      split <;> grind
    rw [hcongr, sumFinRat_skip2 d (by omega) c]
  · have hzero : matSub W (matAdd Qalt Lalt) = fun _ _ => 0 := by
      funext i j
      simp only [matSub, matAdd, W, spikedDiag, Qalt, Lalt, diagMat]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        by_cases h0 : i.val = 0
        · simp only [h0, ↓reduceIte]
          have hsub0 : (2 * M * k : Rat) - (2 * M * k : Rat) = 0 := by grind
          rw [hsub0, hq_zero]; grind
        · simp only [h0, ↓reduceIte]
          have hsub0 : ((k - 1 : Nat) : Rat) - 0 = ((k - 1 : Nat) : Rat) := by grind
          rw [hsub0, hq2_bulk]; grind
      · simp only [hij, ↓reduceIte]
        have hsub0 : (0 : Rat) - 0 = 0 := by grind
        rw [hsub0, hq_zero]; grind
    unfold frobSqErr frobSq
    rw [hzero]
    have hrow0 : ∀ i : Fin d, sumFinRat d (fun _ => (0 : Rat) * 0) = 0 := by
      intro i
      rw [sumFinRat_congr (fun _ => (0 : Rat) * 0) (fun _ => 0) (fun _ => by grind)]
      exact sumFinRat_zero d
    rw [sumFinRat_congr _ (fun _ => 0) hrow0, sumFinRat_zero]

/-! ### Part 3: Exact `4M^2` Saturation Law -/

theorem uniformBulkVarianceRatio_eq (M : Nat) (_hM : 0 < M) :
    uniformBulkVarianceRatio M = 4 * (M : Rat) * (M : Rat) := by
  unfold uniformBulkVarianceRatio
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul, Rat.inv_inv]
  grind

/-! ### Main Theorem 4 -/

theorem loftq_alternating_monotone_energy_and_4m2_saturation :
    (∀ {m n : Nat} (W Q_t Q_next L_t L_next : RatMat m n)
        (S_Q S_L : RatMat m n → Prop),
      S_Q Q_t → S_L L_t →
      isBestApprox S_Q (matSub W L_t) Q_next →
      isBestApprox S_L (matSub W Q_next) L_next →
      frobSqErr W (matAdd Q_next L_next) ≤ frobSqErr W (matAdd Q_next L_t) ∧
      frobSqErr W (matAdd Q_next L_t) ≤ frobSqErr W (matAdd Q_t L_t)) ∧
    (∀ (d M k : Nat), 3 ≤ d → 0 < M → 2 ≤ k →
      let W := spikedDiag d M k
      let Q1 : RatMat d d := fun i j => absmaxQuantAtScale M (2 * k : Rat) (W i j)
      let L1 : RatMat d d := diagMat (fun i => if i.val = 1 then ((k - 1 : Nat) : Rat) else 0)
      let Lalt : RatMat d d := diagMat (fun i => if i.val = 0 then (2 * M * k : Rat) else 0)
      let Qalt : RatMat d d := fun i j => absmaxQuantAtScale M (((k - 1 : Nat) : Rat) / (M : Rat)) (matSub W Lalt i j)
      frobSqErr W (matAdd Q1 L1) =
        ((d - 2 : Nat) : Rat) * (((k - 1 : Nat) : Rat) * ((k - 1 : Nat) : Rat)) ∧
      frobSqErr W (matAdd Qalt Lalt) = 0) ∧
    (∀ M : Nat, 0 < M →
      uniformBulkVarianceRatio M = 4 * (M : Rat) * (M : Rat) ∧
      (∀ x : Rat, absRat x ≤ 1 →
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) *
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) ≤ 1 / (4 * (M : Rat) * (M : Rat))) ∧
      (∃ x : Rat, absRat x ≤ 1 ∧
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) *
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) = 1 / (4 * (M : Rat) * (M : Rat)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n W Q_t Q_next L_t L_next S_Q S_L hQt hLt hQnext hLnext
    exact loftq_euclid_monotone W Q_t Q_next L_t L_next S_Q S_L hQt hLt hQnext hLnext
  · intro d M k hd hM hk
    exact spiked_separation_exact d M k hd hM hk
  · intro M hM
    refine ⟨uniformBulkVarianceRatio_eq M hM, absmaxQuantAtScale_unit_err_bound M hM, ?_⟩
    exact ⟨1 / (2 * (M : Rat)), absmaxQuantAtScale_unit_err_attained M hM⟩

end LoftqCyclesRank1
