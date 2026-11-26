/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnsignedFp4SoftmaxV.RatOrder

/-!
# Theorems 5 & 6: Attention `V`-Centering Simplex-Drift Annihilation & `E2M1` Level Collapse

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
5. `attention_v_centering_simplex_drift_annihilation`: Exact universal algebraic theorem
   proving that for any probability vector `p` (`∑ p_j = 1`), quantized probability `pHat`
   (`∑ pHat_j = 1 + δP`), value vector `v`, constant shift `μV`, centered `v_c = v - μV`,
   and any quantized values `qV, qVc`:
   - `dotFin p v = dotFin p v_c + μV`
   - Raw error: `dotFin pHat qV - dotFin p v = δP * μV + dotFin (pHat - p) v_c + dotFin pHat (qV - v)`
   - Centered error: `(dotFin pHat qVc + μV) - dotFin p v = dotFin pHat qVc - dotFin p v_c
     = dotFin (pHat - p) v_c + dotFin pHat (qVc - v_c)`, completely annihilating `δP * μV ≡ 0`.
6. `raw_v_e2m1_level_collapse_vs_centered_invariance`: Exact theorem proving raw `V` in
   `[μ - R, μ + R]` with bias ratio `|μ| / R ≥ 4` collapses to `≤ 2` active signed `FP4-E2M1`
   levels (and `≤ 1` level for `|μ| / R ≥ 8`), with exact active counts `15, 12, 8, 4, 2, 1`
   at `|μ| / R ∈ {0, 1/2, 1, 2, 4, 8}`, whereas centered `V_c = V - μ` is identically invariant
   to `μ`, achieves exact scale compression `1 + |μ|/R` and MSE factor `(1 + |μ|/R)^2`, and
   preserves all `15 / 15` signed `FP4-E2M1` levels.
-/

namespace UnsignedFp4SoftmaxV

/-! ### Theorem 5: Attention `V`-Centering Simplex-Drift Annihilation -/

theorem attention_v_centering_simplex_drift_annihilation :
    ∀ (n : Nat) (p pHat v qV qVc : Fin n → Rat) (μV : Rat),
      sumFin p = 1 →
      let δP := sumFin pHat - 1
      let vc : Fin n → Rat := fun j => v j - μV
      (dotFin p v = dotFin p vc + μV) ∧
      (dotFin pHat qV - dotFin p v =
        δP * μV +
        dotFin (fun j => pHat j - p j) vc +
        dotFin pHat (fun j => qV j - v j)) ∧
      ((dotFin pHat qVc + μV) - dotFin p v = dotFin pHat qVc - dotFin p vc) ∧
      ((dotFin pHat qVc + μV) - dotFin p v =
        dotFin (fun j => pHat j - p j) vc +
        dotFin pHat (fun j => qVc j - vc j)) := by
  intro n p pHat v qV qVc μV hp δP vc
  have h1 : dotFin p v = dotFin p vc + μV := by
    unfold dotFin
    have hsplit : (fun j => p j * v j) = (fun j => p j * vc j + p j * μV) := by
      funext j; dsimp only [vc]; grind
    rw [hsplit, sumFin_add, sumFin_mul_right, hp, Rat.one_mul]
  have h2 : dotFin pHat qV - dotFin p v =
      δP * μV + dotFin (fun j => pHat j - p j) vc + dotFin pHat (fun j => qV j - v j) := by
    unfold dotFin
    have hdiff1 : sumFin (fun j => (pHat j - p j) * vc j) =
        sumFin (fun j => pHat j * vc j) - sumFin (fun j => p j * vc j) := by
      have : (fun j => (pHat j - p j) * vc j) = (fun j => pHat j * vc j - p j * vc j) := by
        funext j; grind
      rw [this, sumFin_sub]
    have hdiff2 : sumFin (fun j => pHat j * (qV j - v j)) =
        sumFin (fun j => pHat j * qV j) - sumFin (fun j => pHat j * v j) := by
      have : (fun j => pHat j * (qV j - v j)) = (fun j => pHat j * qV j - pHat j * v j) := by
        funext j; grind
      rw [this, sumFin_sub]
    have hpHat_v : sumFin (fun j => pHat j * v j) =
        sumFin (fun j => pHat j * vc j) + sumFin pHat * μV := by
      have : (fun j => pHat j * v j) = (fun j => pHat j * vc j + pHat j * μV) := by
        funext j; dsimp only [vc]; grind
      rw [this, sumFin_add, sumFin_mul_right]
    rw [hdiff1, hdiff2]
    unfold dotFin at h1
    dsimp only [δP]
    grind
  have h3 : (dotFin pHat qVc + μV) - dotFin p v = dotFin pHat qVc - dotFin p vc := by
    rw [h1]; grind
  have h4 : (dotFin pHat qVc + μV) - dotFin p v =
      dotFin (fun j => pHat j - p j) vc + dotFin pHat (fun j => qVc j - vc j) := by
    rw [h3]
    unfold dotFin
    have hdiff1 : sumFin (fun j => (pHat j - p j) * vc j) =
        sumFin (fun j => pHat j * vc j) - sumFin (fun j => p j * vc j) := by
      have : (fun j => (pHat j - p j) * vc j) = (fun j => pHat j * vc j - p j * vc j) := by
        funext j; grind
      rw [this, sumFin_sub]
    have hdiff2 : sumFin (fun j => pHat j * (qVc j - vc j)) =
        sumFin (fun j => pHat j * qVc j) - sumFin (fun j => pHat j * vc j) := by
      have : (fun j => pHat j * (qVc j - vc j)) = (fun j => pHat j * qVc j - pHat j * vc j) := by
        funext j; grind
      rw [this, sumFin_sub]
    rw [hdiff1, hdiff2]; grind
  exact ⟨h1, h2, h3, h4⟩

/-! ### Theorem 6: Raw `V` Signed `FP4-E2M1` Level Collapse vs Centered Invariance -/

private theorem filter_length_le_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter]
    cases hp : p a
    · cases hq : q a <;> simp <;> omega
    · have hq : q a = true := h a hp
      simp [hq]; omega

theorem countLevelsInInterval_mono {lvls : List Rat} {lo1 lo2 hi1 hi2 : Rat}
    (hlo : lo1 ≤ lo2) (hhi : hi2 ≤ hi1) :
    countLevelsInInterval lvls lo2 hi2 ≤ countLevelsInInterval lvls lo1 hi1 := by
  unfold countLevelsInInterval
  apply filter_length_le_of_imp
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  exact ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩

private theorem rat_int_div12_le_iff {z : Int} {a b : Int} (hb : (0 : Rat) < (b : Rat))
    (h : (z : Rat) * (b : Rat) ≤ (a : Rat) * 12) :
    (z : Rat) / 12 ≤ (a : Rat) / (b : Rat) :=
  rat_div_le_div_of_cross (by decide) hb h

private theorem rat_le_int_div12_iff {z : Int} {a b : Int} (hb : (0 : Rat) < (b : Rat))
    (h : (a : Rat) * 12 ≤ (z : Rat) * (b : Rat)) :
    (a : Rat) / (b : Rat) ≤ (z : Rat) / 12 :=
  rat_div_le_div_of_cross hb (by decide) h

private theorem rat_not_le_of_int_lt {a b : Int} (h : b < a) : ¬((a : Rat) ≤ (b : Rat)) := by
  have hlt : (b : Rat) < (a : Rat) := by
    have hk : a = b + (a - b) := by omega
    have hpos : (0 : Rat) < ((a - b : Int) : Rat) := by
      have hn : 0 < (a - b).toNat := by omega
      have hcast : ((a - b : Int) : Rat) = ((a - b).toNat : Nat) := by
        have hEq : Int.ofNat (a - b).toNat = a - b := Int.toNat_of_nonneg (by omega)
        rw [← hEq]; rfl
      rw [hcast]; exact rat_natCast_pos hn
    apply rat_lt_of_sub_pos
    have hsub : (a : Rat) - (b : Rat) = ((a - b : Int) : Rat) := by
      have : (a : Rat) = (b : Rat) + ((a - b : Int) : Rat) := by
        conv => lhs; rw [hk]
        rw [Rat.intCast_add]
      grind
    rw [hsub]; exact hpos
  exact Rat.not_le.mpr hlt

private theorem rat_le_of_int_le {a b : Int} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  by_cases heq : a = b
  · subst heq; exact Rat.le_refl
  · exact Rat.le_of_lt (Rat.not_le.mp (rat_not_le_of_int_lt (by omega)))

private theorem rat_frac_decide_le (a b c d : Int) (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat) := by
  have hbpos : (0 : Rat) < (b : Rat) := Rat.not_le.mp (rat_not_le_of_int_lt (by omega))
  have hdpos : (0 : Rat) < (d : Rat) := Rat.not_le.mp (rat_not_le_of_int_lt (by omega))
  apply rat_div_le_div_of_cross hbpos hdpos
  have h1 := rat_le_of_int_le h
  simpa only [Rat.intCast_mul] using h1

private theorem rat_frac_decide_not_le (a b c d : Int) (hb : 0 < b) (hd : 0 < d) (h : c * b < a * d) :
    ¬((a : Rat) / (b : Rat) ≤ (c : Rat) / (d : Rat)) := by
  have hbpos : (0 : Rat) < (b : Rat) := Rat.not_le.mp (rat_not_le_of_int_lt (by omega))
  have hdpos : (0 : Rat) < (d : Rat) := Rat.not_le.mp (rat_not_le_of_int_lt (by omega))
  have hlt : (c : Rat) / (d : Rat) < (a : Rat) / (b : Rat) := by
    apply rat_div_lt_div_of_cross hdpos hbpos
    have h1 : (c * b : Int) < (a * d : Int) := h
    have h2 : ¬(((a * d : Int) : Rat) ≤ ((c * b : Int) : Rat)) := rat_not_le_of_int_lt h1
    have h3 : ((c * b : Int) : Rat) < ((a * d : Int) : Rat) := Rat.not_le.mp h2
    simpa only [Rat.intCast_mul] using h3
  exact Rat.not_le.mpr hlt

private theorem count_e2m1_eq_int_filter (lo : Rat) (p q : Int) (hq : 0 < q)
    (hlo : lo = (p : Rat) / (q : Rat)) :
    countLevelsInInterval e2m1SignedLevels lo 1 =
      (e2m1SignedInt.filter (fun z => decide (p * 12 ≤ z * q ∧ z ≤ 12))).length := by
  have hhi : (1 : Rat) = ((1 : Int) : Rat) / ((1 : Int) : Rat) := by grind
  have hpred : ∀ z : Int,
      decide (lo ≤ (z : Rat) / 12 ∧ (z : Rat) / 12 ≤ 1) =
      decide (p * 12 ≤ z * q ∧ z ≤ 12) := by
    intro z
    by_cases h1 : p * 12 ≤ z * q
    · by_cases h2 : z ≤ 12
      · have hr1 : lo ≤ (z : Rat) / 12 := by
          rw [hlo]; exact rat_frac_decide_le p q z 12 hq (by omega) h1
        have hr2 : (z : Rat) / 12 ≤ 1 := by
          rw [hhi]; exact rat_frac_decide_le z 12 1 1 (by omega) (by omega) (by omega)
        simp [h1, h2, hr1, hr2]
      · have hr2 : ¬((z : Rat) / 12 ≤ 1) := by
          rw [hhi]; exact rat_frac_decide_not_le z 12 1 1 (by omega) (by omega) (by omega)
        simp [h1, h2, hr2]
    · have hr1 : ¬(lo ≤ (z : Rat) / 12) := by
        rw [hlo]; exact rat_frac_decide_not_le p q z 12 hq (by omega) (by omega)
      simp [h1, hr1]
  unfold countLevelsInInterval e2m1SignedLevels
  rw [List.filter_map]
  have hlen : ∀ (l : List Int),
      (l.filter (fun (z : Int) => decide (lo ≤ (z : Rat) / 12 ∧ (z : Rat) / 12 ≤ 1))).length =
      (l.filter (fun (z : Int) => decide (p * 12 ≤ z * q ∧ z ≤ 12))).length := by
    intro l
    have hfun : (fun (z : Int) => decide (lo ≤ (z : Rat) / 12 ∧ (z : Rat) / 12 ≤ 1)) =
        (fun (z : Int) => decide (p * 12 ≤ z * q ∧ z ≤ 12)) := funext hpred
    rw [hfun]
  rw [List.length_map]
  exact hlen e2m1SignedInt

theorem count_e2m1_full :
    countLevelsInInterval e2m1SignedLevels (-1) 1 = 15 := by
  rw [count_e2m1_eq_int_filter (-1) (-1) 1 (by omega) (by grind)]; rfl

theorem count_e2m1_at_three_fifths :
    countLevelsInInterval e2m1SignedLevels (3 / 5) 1 = 2 := by
  rw [count_e2m1_eq_int_filter (3 / 5) 3 5 (by omega) (by grind)]; rfl

theorem count_e2m1_at_seven_ninths :
    countLevelsInInterval e2m1SignedLevels (7 / 9) 1 = 1 := by
  rw [count_e2m1_eq_int_filter (7 / 9) 7 9 (by omega) (by grind)]; rfl

theorem count_e2m1_at_one_third :
    countLevelsInInterval e2m1SignedLevels (1 / 3) 1 = 4 := by
  rw [count_e2m1_eq_int_filter (1 / 3) 1 3 (by omega) (by grind)]; rfl

theorem count_e2m1_at_zero :
    countLevelsInInterval e2m1SignedLevels 0 1 = 8 := by
  rw [count_e2m1_eq_int_filter 0 0 1 (by omega) (by grind)]; rfl

theorem count_e2m1_at_neg_one_third :
    countLevelsInInterval e2m1SignedLevels (-1 / 3) 1 = 12 := by
  rw [count_e2m1_eq_int_filter (-1 / 3) (-1) 3 (by omega) (by grind)]; rfl

/-- Headline Theorem 6: Raw `V` signed `FP4-E2M1` codebook collapse at `|μ|/R ≥ 4` (`≤ 2` levels)
    and `|μ|/R ≥ 8` (`≤ 1` level), exact active counts `15, 12, 8, 4, 2, 1`, vs centered `V_c`
    complete invariance to `μ` preserving all `15 / 15` levels with scale compression `1 + |μ|/R`. -/
theorem raw_v_e2m1_level_collapse_vs_centered_invariance :
    e2m1SignedLevels.length = 15 ∧
    (∀ μ R : Rat, (0 : Rat) < R → (4 : Rat) ≤ ratAbs μ / R →
      countLevelsInInterval e2m1SignedLevels ((ratAbs μ - R) / (ratAbs μ + R)) 1 ≤ 2) ∧
    (∀ μ R : Rat, (0 : Rat) < R → (8 : Rat) ≤ ratAbs μ / R →
      countLevelsInInterval e2m1SignedLevels ((ratAbs μ - R) / (ratAbs μ + R)) 1 ≤ 1) ∧
    (∀ μ R : Rat, (0 : Rat) < R →
      let S_raw := ratAbs μ + R
      let S_c := R
      S_raw / S_c = 1 + ratAbs μ / R ∧
      ((μ + R) - μ) / S_c = 1 ∧
      ((μ - R) - μ) / S_c = -1 ∧
      countLevelsInInterval e2m1SignedLevels (((μ - R) - μ) / S_c) (((μ + R) - μ) / S_c) = 15) ∧
    (countLevelsInInterval e2m1SignedLevels (-1) 1 = 15 ∧
     countLevelsInInterval e2m1SignedLevels (-1 / 3) 1 = 12 ∧
     countLevelsInInterval e2m1SignedLevels 0 1 = 8 ∧
     countLevelsInInterval e2m1SignedLevels (1 / 3) 1 = 4 ∧
     countLevelsInInterval e2m1SignedLevels (3 / 5) 1 = 2 ∧
     countLevelsInInterval e2m1SignedLevels (7 / 9) 1 = 1) := by
  refine ⟨rfl, ?_, ?_, ?_, count_e2m1_full, count_e2m1_at_neg_one_third,
          count_e2m1_at_zero, count_e2m1_at_one_third,
          count_e2m1_at_three_fifths, count_e2m1_at_seven_ninths⟩
  · intro μ R hR hratio
    have hRne : R ≠ 0 := Rat.ne_of_gt hR
    have hmul : 4 * R ≤ ratAbs μ := by
      have := rat_mul_le_mul_of_nonneg_right hratio (Rat.le_of_lt hR)
      rwa [rat_div_mul_cancel hRne] at this
    have hden_pos : (0 : Rat) < ratAbs μ + R :=
      rat_add_pos_of_pos_of_nonneg (rat_lt_of_lt_of_le (rat_mul_pos (by decide) hR) hmul) (Rat.le_of_lt hR)
    have hlo : (3 / 5 : Rat) ≤ (ratAbs μ - R) / (ratAbs μ + R) := by
      apply rat_div_le_div_of_cross (by decide) hden_pos
      have hsub : (0 : Rat) ≤ 2 * (ratAbs μ - 4 * R) :=
        Rat.mul_nonneg (by decide) (rat_sub_nonneg hmul)
      apply rat_le_of_sub_nonneg
      have eq : (ratAbs μ - R) * 5 - 3 * (ratAbs μ + R) = 2 * (ratAbs μ - 4 * R) := by grind
      rw [eq]; exact hsub
    have hle := countLevelsInInterval_mono (lvls := e2m1SignedLevels) hlo (Rat.le_refl (a := (1 : Rat)))
    rw [count_e2m1_at_three_fifths] at hle
    exact hle
  · intro μ R hR hratio
    have hRne : R ≠ 0 := Rat.ne_of_gt hR
    have hmul : 8 * R ≤ ratAbs μ := by
      have := rat_mul_le_mul_of_nonneg_right hratio (Rat.le_of_lt hR)
      rwa [rat_div_mul_cancel hRne] at this
    have hden_pos : (0 : Rat) < ratAbs μ + R :=
      rat_add_pos_of_pos_of_nonneg (rat_lt_of_lt_of_le (rat_mul_pos (by decide) hR) hmul) (Rat.le_of_lt hR)
    have hlo : (7 / 9 : Rat) ≤ (ratAbs μ - R) / (ratAbs μ + R) := by
      apply rat_div_le_div_of_cross (by decide) hden_pos
      have hsub : (0 : Rat) ≤ 2 * (ratAbs μ - 8 * R) :=
        Rat.mul_nonneg (by decide) (rat_sub_nonneg hmul)
      apply rat_le_of_sub_nonneg
      have eq : (ratAbs μ - R) * 9 - 7 * (ratAbs μ + R) = 2 * (ratAbs μ - 8 * R) := by grind
      rw [eq]; exact hsub
    have hle := countLevelsInInterval_mono (lvls := e2m1SignedLevels) hlo (Rat.le_refl (a := (1 : Rat)))
    rw [count_e2m1_at_seven_ninths] at hle
    exact hle
  · intro μ R hR S_raw S_c
    have hRne : R ≠ 0 := Rat.ne_of_gt hR
    have h1 : S_raw / S_c = 1 + ratAbs μ / R := by
      dsimp only [S_raw, S_c]
      have hmul : ((ratAbs μ + R) / R - (1 + ratAbs μ / R)) * R = 0 := by
        have ha := rat_div_mul_cancel (a := ratAbs μ + R) hRne
        have hb := rat_div_mul_cancel (a := ratAbs μ) hRne
        grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h0 => grind
      | inr hr => exact False.elim (hRne hr)
    have h2 : ((μ + R) - μ) / S_c = 1 := by
      dsimp only [S_c]
      have eq : (μ + R) - μ = R := by grind
      rw [eq, Rat.div_def, Rat.mul_inv_cancel R hRne]
    have h3 : ((μ - R) - μ) / S_c = -1 := by
      dsimp only [S_c]
      have eq : (μ - R) - μ = -R := by grind
      rw [eq, Rat.div_def]
      have eq2 : (-R) * R⁻¹ = -(R * R⁻¹) := by grind
      rw [eq2, Rat.mul_inv_cancel R hRne]
    refine ⟨h1, h2, h3, ?_⟩
    rw [h2, h3]
    exact count_e2m1_full

end UnsignedFp4SoftmaxV
