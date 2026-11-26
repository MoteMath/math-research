import Lib.DiscreteSeries.FlenstedJensen.TailBounds
open Finset Int
section
open MeasureTheory ComplexConjugate Complex Circle
variable {n} [Fintype n] {ε o Φ F} [Fintype Φ] {u : Φ → _} (ho : @IsPosFirstOrder n ε o) (hu : ∀ τ, IsKDominant ε o (u τ)) (hF : IsHolOfWeight ε o u F)
attribute [local simp] holMinorsPi holMinors sum_nonneg zpow_add₀ weightMinors_ite_eq_zpow ite_eq_iff prod_ne_zero_iff fieldEq diagTorus Measure.real
lemma holMinors_ite_sign {a b} (h : a ≤ b) (g : USign ε) : holMinors ε (if ε · = 1 then a else b) g = g.1.1.det ^ b / principalMinor g (ε · = 1) ^ (b - a) := by rw [holMinors, weightMinors_ite_eq_zpow, div_eq_div_iff, ← weightMinors_add_ite, ← weightMinors_const, ← weightMinors_add_ite] <;> simp <;> grind
  [neg_sum_abs_le_and_le_sum_abs (if ε · = 1 then a else b)]
@[simp] lemma holMinorsPi_one : holMinorsPi ε u 1 = 1 := by simp
include ho hu
omit [Fintype Φ] in
lemma IsPosFirstOrder.iKDs a τ : IsKDominant 1 o fun i ↦ cond a 1 0 * u τ i + ite (ε i = 1) (2 * ∑ j, |u τ j|) 0 := by have := neg_sum_abs_le_and_le_sum_abs (u τ); grind [IsKDominant, IsPosFirstOrder, units_eq_one_or (ε _)]
lemma isHolOfWeight_holMinorsPi : IsHolOfWeight ε o u (holMinorsPi ε u) := by
 choose f _ using (isHolOfWeight_weightMinors (ε := ε) ho.1 1 <| ho.iKDs hu ·)
 use f true / f false
 simp_all (maxDischargeDepth := 4) [AnalyticAt.div, diagChar, IsBorelMatrix.diag_ne_zero ho.1, -mul_ite]
include hF
lemma IsHolOfWeight.circle_mean_holMinorsPi h : ∫ θ : UnitAddCircle, F ((fun _ ↦ diagTorus ε (θ.toCircle ^ o ·)) * h) * ∏ τ, ∏ i, ↑((θ.toCircle ^ o i) ^ u τ i)⁻¹ = holMinorsPi ε u h * F 1 := by
  simp [← integral_mul_const]; convert! (hF.mul ho.1 (isHolOfWeight_weightMinors ho.1 1
  (ho.iKDs hu false))).circle_mean_weightMinors ho.1 (by
  simpa using! ho.iKDs hu true) _ 1 analyticOnNhd_const using 2 <;> simp (maxDischargeDepth := 4) [-mul_ite, Pi.add_def, ← weightMinors_ite_eq_zpow, funext_iff]
lemma IsHolOfWeight.integral_mul_conj_holMinorsPi (hi : Integrable fun h ↦ F h * conj (holMinorsPi ε u h)) : ∫ h, F h * conj (holMinorsPi ε u h) = (∫ h, ‖holMinorsPi ε u h‖ ^ 2) * F 1 := by rw [← integral_complex_ofReal, ← integral_mul_const, integral_eq_of_circle_mean (map_mul_left_eq_self _ fun _ ↦ diagTorus ε fun i ↦ ·.toCircle ^ o i) hi]; simp [← conj_mul', mul_assoc, ← hF.circle_mean_holMinorsPi, *, ← integral_const_mul, -holMinorsPi]; congr! 2; simp (disch := simp) [← coe_inv_eq_conj, -pow_ite, mul_div_mul_comm]
lemma IsHolOfWeight.eq_holMinorsPi_mul (i : ∀ g, F g⁻¹ = conj (F g)) h : F h = holMinorsPi ε u h * F 1 := by simp [mul_comm, -Circle.coe_zpow, ← fun t y ↦ by
  simpa [← i, ← coe_inv_eq_conj, ← coe_zpow, -fieldEq] using congrArg
    conj (hF.apply_mul_diagTorus y⁻¹ t), ← hF.circle_mean_holMinorsPi, *, -holMinorsPi]
end
section
open Fintype GlModule HCParam.IsKHighest Finite
lemma dsCoeff_eq_holMinors {n} [Fintype n] {ε o} (ho : @IsPosFirstOrder n ε o) [Nonempty n] A γ w (hu : IsKDominant ε o w) (hw : HasHolGap ε w γ) (h : 500 * card n ^ 3 + A + card n + 1 < γ) : let l : HCParam ε := 2 * w + twoRho (-o) ⊤
  l.HasLargeGap A ∧ ∀ g : USign ε, l.dsCoeff g = holMinors ε w g := ho.rec (by
  intro t _ l
  clear_value (L : l = _)
  simp [funext_iff, twoRho] at L
  have k a b (q : o a < o b) : ite (ε a = ε b) (l b < l a) (2 * (γ - card n) ≤ l b - l a) := by
    grind [IsKDominant, HasHolGap, twoRho, twoRho_lt_twoRho q, units_eq_one_or (ε _)]
  have hg : l.HasLargeGap A := ⟨(by grind [o · |>.lt_or_le <| o ·]), (by grind [card_lt_add_card_gt_add_one t ·]), gapThreshold.eq_1 n A ▸ mod_cast by grind⟩
  obtain ⟨rfl, x⟩ := (by grind [(by simpa [twoRho, ← sum_boole, ← sum_sub_distrib, add_assoc, ← sum_add_distrib] using (L · ▸ two_mul_lowestKType hg _ :))] : l.lowestKType = w), isKHighest_dsGenerator hg
  simpa [holMinorsPi, hg] using ((isHolOfWeight_coeffMap (c := fun _ g ↦ ⟨⟨(·.1.1 g), by simp⟩, by simp⟩) t (fun _ ↦ ⟨x.1, by
    have ⟨(a, b), m⟩ := exists_max fun (a, b) ↦ ite (l.dsAction.E a b l.dsGenerator = 0) 0 (o b - o a)
    by_contra; have := cBnd hg.isUnitaryCasimirGe_dsAction.1
      ⟨(x.eWW [(a, b)] · |>.1), by simp +contextual [word, aaB, x.2, mSMS, DFunLike.ite_apply] at *; grind⟩
    simp [word, sub_mul] at *
    grind [x.2 a]⟩) (fun _ _ _ _ ↦ hasDerivAt_rightDeriv_expU _ _ _)
    (.mkPiAlgebra ..)).eq_holMinorsPi_mul ho (by simpa) (by simp [← dsCoeff_inv]) ![·]))
end
