import Lib.DiscreteSeries.Bessel.RealMeasures
section
noncomputable section
open MeasureTheory Measure Matrix Real Fintype Set Complex ComplexConjugate Sum GaussianFourier ComplexOrder Function
variable {κ : Type} [Fintype κ] (𝔰 : Shape) (l : ℕ) (c : ℂ)
lemma eum ω {v : κ → ℂ} (h : star ω ⬝ᵥ ω = star v ⬝ᵥ v) : ∃ u : U 1, u.1.1 *ᵥ ω = v := if o : _ then ⟨1, by have := h.symm; aesop⟩ else (witt ⟨I, by simp⟩ (by simp) isUnit_one (.of_ne_zero o) (.of_ne_zero (by aesop)) (by aesop)).imp fun _ ↦ replicateCol_inj.1
attribute [local simp] wave skewAdjoint.mem_iff LeftInverse Matrix.mul_apply inclMatrix frameGram dotProduct conj_mul' mem_floorGroup val_toBesselH_apply_coe mul_pow orbitPoint le_of_lt funext_iff neg_add_eq_sub
@[simps] instance complexPlace : Place ℂ := have e := HasGaussianIntegral.integral_exp_eq (V := ℂ) one_pos
  have J := Integrable.of_integral_ne_zero (e.trans_ne (by simp)); have h z := integral_cexp_neg_mul_sq_norm_add (b := 1) one_pos (2 * I) (z / I); have := ofReal_integral_norm_eq_lintegral_enorm (J.const_mul π)
  by refine .mk (haar := AddEquiv.isAddHaarMeasure_map _ ⟨⟨_, (·.1.im), ?_, by simp_all
    [RightInverse, Complex.ext_iff, self_eq_neg]⟩, ?_⟩ ?_ ?_) (toTraceOne := ⟨2⁻¹, ?_⟩) (.mk0 (I / 2) ?_) (volume.map fun r : ℝ ↦ ⟨r * I, by simp⟩) ⟨⟨(‖·‖ₑ ^ 2), ?_⟩, ?_⟩ ⟨wave, ?_, by
    simp [← Complex.exp_add, sub_add_sub_comm]⟩ (.ofReal (π ^ 2)) ?_ ?_ ?_ ⟨?_, by
    rw [map_prod_map, Measure.map_map, ← volume_preserving_equiv_real_prod.symm.2] <;> try fun_prop
    congr 1; simp [Complex.ext_iff]⟩ ?_ ?_ ?_ ⟨(‖·‖⁻¹), locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_, ?_⟩ ?_ ⟨_, ?_, J, ?_, ?_, by
    simp_all [← Complex.exp_add, ↓sub_conj, mul_right_comm _ _ I, ← sub_eq_add_neg, sq, ← ofReal_norm, abs_of_pos pi_pos]; grind⟩ <;> norm_num +contextual [map_mulVec_haar, Pi.le_def, exp_pos, add_mul, ae_ne, neg_div, rpow_neg_one, ENNReal.inv_pow] <;> fun_prop [wave]
def complexBasis : HyperbolicBasis {i // i ≠ 𝔰.k₀} (𝔰.middleGram (1 : ℂ)) 0 := ⟨of fun i ↦ (fun a ↦ (1 + I) / 2 * (Pi.single 𝔰.k₀ 1 ⊕ᵥ ![1, -1] a) i) ⊕ᵥ (0 ⊕ᵥ (inclMatrix ℂ (inl ·.1) i ⊕ᵥ 0)), by simp [← ext_iff, middleGram, map_ofNat]; grind [I_sq], by simp; grind [card_pos_iff.2 ⟨𝔰.k₀⟩], by simp [middleGram]⟩
lemma measurePreserving_normSq_sphereDensity [Nonempty κ] : MeasurePreserving (fun ω : κ → ℂ ↦ ‖star ω ⬝ᵥ ω‖) volume ((volume.restrict (Ioi 0)).withDensity fun r ↦ .ofReal (sphereDensity (card κ) r / 2)) := by
  refine have k a := Eq.trans ?_ (Complex.volume_sum_rpow_lt κ one_le_two √a); ⟨by fun_prop, FiniteSpanningSetsIn.ext (borel_eq_generateFrom_Iio ℝ) isPiSystem_Iio ⟨(Iio ·), by simp, (k ·
    |>.trans_lt (by tauto)), iUnion_eq_univ_iff.2 exists_nat_gt⟩ fun _ ⟨a, e⟩ ↦ e ▸ (k a).trans ?_⟩
  simp (disch := first | positivity | measurability)
    [preimage, ↓← sqrt_eq_rpow, ↓star_dot_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
  rw [withDensity_apply, restrict_restrict, (by grind : _ ∩ _ = Ioo 0 (√a ^ 2)), restrict_Ioo_eq_restrict_Ioc, ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Ioc (by fun_prop)) (ae_restrict_of_forall_mem ..), ← intervalIntegral.integral_of_le, pow_mul] <;>
    norm_num [← ENNReal.ofReal_pow, sq_nonneg, ← ENNReal.ofReal_mul, Real.Gamma_nat_eq_factorial, ← Nat.mul_factorial_pred card_ne_zero, card_pos]
  grind [card_pos]; bound
def cellChart : 𝔰.G₁ := let a := c / min 1 ‖c‖
 let s := √(‖a‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1; dite (l = 𝔰.ϱ ∧ 1 ≤ ‖a‖) (fun h ↦ U.of IsHermUnit.isUnit (fromBlocks 1 0 0 (((diagonal (update 1 𝔰.k₀ (conj a))).fromBlocks (replicateCol _ s) (-replicateRow _ s) (of fun _ _ ↦ -a)).fromBlocks 0 0 1)) (by simp [s, splitGram, middleGram, ← ext_iff, diagonal_apply, update_apply, apply_ite conj, ← ofReal_mul, RCLike.star_def, *]; grind [conj_mul'])) fun _ ↦ floorWeyl l c
def cellDensity := ite (l < 𝔰.ϱ) (‖c‖ₑ ^ (2 * (𝔰.k - 1) + 4 * (𝔰.ϱ - l))) (.ofReal (sphereDensity 𝔰.k (‖c‖ ^ 2 - 1)⁺))
variable {𝔰 l c}
abbrev cellLaw l := (volume.withDensity (cellDensity 𝔰 l)).map fun c ↦ (cellChart 𝔰 l c)⁻¹
lemma cellChart_mem : cellChart 𝔰 l c ∈ GT l := dite_mem.2 (by simp +contextual [↓floorWeyl_mem_floorGroup])
lemma embedH_mem_floorGroup k : @embedH 𝔰 k ∈ GT 𝔰.ϱ := by simp
@[fun_prop] lemma measurable_cellChart : Measurable (cellChart 𝔰 l) := measurable_unitary_of_coe (by
 simp -iota [cellChart, apply_dite]; apply Measurable.ite <;> measurability)
@[fun_prop] lemma measurable_cellDensity : Measurable (cellDensity 𝔰 l) := by delta cellDensity; measurability
attribute [local simp] splitGram middleGram cellChart mulVec Nat.sub_eq_zero_iff_le min_eq_left
lemma realFrameGram_cellChart (h : 1 < ‖c‖) : realFrameGram (cellChart 𝔰 𝔰.ϱ c) 𝔰.top 𝔰.top = c := by simp [*, U.of]
lemma cartan_decomposition {σ} (h : σ ∈ GT 𝔰.ϱ) (e : realFrameGram σ 𝔰.top 𝔰.top = c) (hc : 1 < ‖c‖) : ∃ k k', σ = embedH k * cellChart 𝔰 𝔰.ϱ c * embedH k' := by have d := congr(diag $(σ.2) 𝔰.z); simp [floorGroup_apply h, neg_eq_iff_eq_neg, add_neg_eq_iff_eq_add] at d e; refine (eum (√(‖c‖ ^ 2 - 1) • Pi.single 𝔰.k₀ 1) ?_).imp fun u f ↦ (exists_toBesselH_eq (unitriGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq (mul_mem (embedH_mem_floorGroup u) cellChart_mem) h (by simpa [e, -splitGram, -middleGram, hc, floorGroup_apply h] using f)))).imp fun _ ↦ eq_mul_of_inv_mul_eq; simp [← ofReal_mul, *]
lemma map_orbitPoint_cellLaw_top (_ : 1 < 𝔰.k) : (cellLaw 𝔰.ϱ ∗ₘ volume.map embedH).map (orbitPoint 𝔰.top) = (complexBasis 𝔰).floorQuadric 𝔰.top := ext_of_lintegral _ fun f hf ↦ by
  let χ Γ (p : ℂ × U 1) := open Calc in update
    (𝔰.definiteCols *ᵥ (√(Γ + ‖p.1‖ ^ 2) * p.2.1.1 · 𝔰.k₀)) 𝔰.z p.1
  erw [(HyperbolicBasis.isDisintegration_floorVolume _ _ (map_inclMatrix_eq_floorVolume (inr ∘ inl))).unique (l' := ((fun Γ ↦ map (χ Γ) (volume.withDensity fun p ↦ .ofReal (sphereDensity 𝔰.k (Γ + ‖p.1‖ ^ 2)⁺))) <| 2 * im ·.1)) ⟨fun a s ↦ ?_, fun f m ↦ ?_⟩] <;> simp (disch := with_unfolding_all fun_prop)
    only [lintegral_map, lintegral_mconv, lintegral_withDensity_eq_lintegral_mul, Pi.mul_apply]
  any_goals exact continuous_lintegral_and_lt_top ((s.image_auto (· 𝔰.z)).prod isCompact_univ) (by
    fun_prop) fun _ _ h ↦ ⟨⟨_, subset_closure (right_ne_zero_of_mul h), rfl⟩, ⟨⟩⟩
  all_goals simp (disch := fun_prop) only [volume_eq_prod, lintegral_prod, lintegral_const_mul]
  · rw [← lintegral_neg_eq_self, (by simp : 2 * im _ = -1)]; congr with c
    rw [← lintegral_inv_eq_self]; by_cases 1 < ‖c‖; congr!
    all_goals simp_all [cellDensity, χ, -middleGram, -splitGram]
  erw [lintegral_lintegral_swap, ← measurePreserving_sumElim.lintegral_comp, lintegral_prod_symm, ← (volume_preserving_funUnique ..).symm.lintegral_comp] <;> try fun_prop
  have lp {g} (m : Measurable g) : ∫⁻ ω : 𝔰.κ → ℂ, g ω = ∫⁻ r in Ioi 0, .ofReal (sphereDensity 𝔰.k r / 2) * ∫⁻ h : U 1, g (h.1.1 *ᵥ √r • Pi.single 𝔰.k₀ 1) := by
    erw [← lintegral_withDensity_eq_lintegral_mul, ← (@measurePreserving_normSq_sphereDensity _ _ ⟨𝔰.k₀⟩).lintegral_comp, ← lintegral_eq_const (ae_of_all volume fun h : U 1 ↦ (complexPlace.measurePreserving_mulVec _ (U.det (by simp) h).2.1).lintegral_comp m), lintegral_lintegral_swap] <;> try fun_prop
    refine lintegral_congr fun ω ↦ (eum ω ?_).elim fun u e ↦ (lintegral_mul_right_eq_self _ u).symm.trans (by simp [-mulVec_smul, ← mulVec_mulVec, e]; rfl); simp (disch := positivity) [← ofReal_mul, norm_of_nonneg']
  congr with c; erw [lp, ← lintegral_indicator (by simp), ← lintegral_add_right_eq_self _ (‖c‖ ^ 2), ← smul_map_volume_mul_left two_ne_zero, lintegral_smul_measure, lintegral_map, lintegral_map, smul_eq_mul, ← lintegral_const_mul] <;> try fun_prop (disch := simp)
  congr with Γ; fun_cases indicator <;> simp_all [-mulVec_smul, ← mul_div, mul_assoc]; congr! 5 with u; simp [-mulVec_smul, χ, apply_ite conj, mul_left_comm I, -map_mul, ← Finset.sum_mul, by simpa using congr(diag $(u.2) 𝔰.k₀)]; norm_cast; grind
instance : IsProbabilityMeasure (volume.map (@embedH 𝔰)) := (isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
end
end
seal Finset.univ Finset.sum Finset.prod
open Matrix MeasureTheory Measure Fintype Real Finset
variable {𝔰 : Shape}
attribute [-instance] MeasurableSingletonClass.toDiscreteMeasurableSpace
noncomputable abbrev fg l (g : 𝔰.G₁) := ‖rexp (-π * ∑ b with b.1 < l, let w := g.1.1 *ᵥ Pi.single (eStar b) 1; ∑ i with b < floorOf i, ‖w i‖ ^ 2 + (w (.inl b)).im ^ 2)‖ₑ
lemma ascConv_heisenbergMeasure_eq_besselHaar : ascConv Place.heisenbergMeasure 𝔰.ϱ = 𝔰.besselHaar.map .val := ext_of_lintegral _ fun f hf ↦ by
 have lf {l} (hl : l ≤ 𝔰.ϱ) : ∫⁻ ν : 𝔰.G₁, fg l ν ∂ascConv Place.heisenbergMeasure l = 1 := by
  induction' l with a ih; simp [ascConv, fg]; erw [lintegral_mconv_symm, Place.heisenbergMeasure, dite_eq_left, ← volume.map_id, map_prod_map, lintegral_map, lintegral_map, lintegral_congr fun x ↦ lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν h ↦ ?_, lintegral_lintegral_mul, lintegral_gaussian_eq_one, ih (by lia), one_mul]; any_goals fun_prop
  push_cast [fg, ← mulVec_mulVec, heisenbergElem_mulVec]; rw [← add_sum_erase (a := ⟨a, hl⟩), mul_add, exp_add, enorm_mul, ← sum_subtype_eq_sum_filter]; congr! <;> try rw [unipotentBelow_mulVec_apply h]
  all_goals simp_all [Complex.conj_eq_iff_im.1 (star_form IsHermUnit.conjTranspose_eq ..), ne_of_gt, inclMatrix_val_mulVec, -mulVec_mulVec, Fin.ext_iff, Nat.lt_of_succ_le] <;> grind [floorOf]
 trans ∫⁻ y, ∫⁻ x, fg 𝔰.ϱ (y⁻¹.1 * x) * f y ∂ascConv complexPlace.heisenbergMeasure 𝔰.ϱ ∂𝔰.besselHaar; rw [eq_comm, lintegral_lintegral_swap, lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow (lintegral_mul_left_eq_self _ ⟨·, unipotentBelow_le_besselU ·⟩ |>.symm.trans (by aesop)), lintegral_lintegral_swap, lintegral_congr fun y ↦ ?_, lintegral_mul_const, measurePreserving_freeEntries_besselHaar.lintegral_comp, lintegral_gaussian_eq_one, one_mul]
 all_goals first | fun_prop | simp (disch := first | fun_prop | simp [unipotentBelow_eq_besselU]) [lintegral_mul_const, ← lintegral_mconv_dirac, ← lintegral_dirac_mconv, lintegral_map, ascConv_heisenbergMeasure_invariant, lf]
 erw [fg, U.coe_inv IsHermInvolution.mul_self, ← sum_toFinset_eq_subtype _ (‖y.1.1.1.toRows₁ · ·‖ ^ 2).uncurry]; simp [sum_filter, sum_prod_type, splitGram, middleGram, mul_apply]; ring
lemma exists_chart_ascConv_cellLaw j : ∃ g : (Fin j → ℂ) → 𝔰.G₁, Measurable g ∧ (∀ p : ℕ → ℂˣ, j ≤ 𝔰.n → g (p ·) = if j ≤ 𝔰.ϱ then weylElem j p else weylElem 𝔰.ϱ p * cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ)) ∧ ∀ X, Measurable X → ∫⁻ x, X x ∂ascConv cellLaw j = ∫⁻ z, (∏ a : Fin j, cellDensity 𝔰 a (z a)) * X (g z)⁻¹ := j.rec ⟨1, by simp! [measurable_one, univ_eq_empty, volume_pi]⟩ fun j ⟨g, m, e⟩ ↦ ⟨fun z ↦ cellChart 𝔰 j (z (.last j)) * g (z ·.castSucc), by fun_prop,
  by simp! +contextual (disch := with_unfolding_all fun_prop) [lintegral_mconv, *, mul_assoc, (measurePreserving_piFinSuccAbove _ (.last j)).symm.lintegral_map_equiv, lintegral_prod_symm, volume_pi, lintegral_map, lintegral_withDensity_eq_lintegral_mul, Fin.prod_univ_castSucc]; grind [cellChart, weylElem_succ, (commute_weylElem cellChart_mem).eq]⟩
