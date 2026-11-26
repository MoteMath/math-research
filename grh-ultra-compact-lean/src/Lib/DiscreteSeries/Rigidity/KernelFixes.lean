import Lib.DiscreteSeries.CuspKernel.SchurOrthogonality
open Matrix MeasureTheory ComplexConjugate Complex Norms.L2Operator ComplexOrder GlModule Submodule WithLp HCParam
attribute [-simp] _root_.mul_apply
variable {n} [Fintype n] {ε A X} {l : @HCParam n ε} [NormedAddCommGroup X] [NormedSpace ℂ X] (π : USign ε →* X →L[ℂ] X) (f : USign ε → ℂ)
attribute [local simp] dsKernel mul_assoc maxCompactU.coe_inv weightMinors_pos div_eq_inv_mul conj_weightMinors integral_smul integral_add ne_of_gt strongIntegral_apply casimir RingHom.map_mul
@[fun_prop] lemma continuous_dsKernel : Continuous l.dsKernel := by fun_prop [dsKernel]
lemma conj_dsKernel_neg {h} (hg : l.HasGap h) x : conj ((-l).dsKernel x) = l.dsKernel x := by simp [formalDegree]
noncomputable def integratedRep := strongIntegral volume fun g ↦ f g • π g
variable {π f} [Nonempty n] {M Y W} [AddCommGroup M] [Module ℂ M] {B ι v c} {ρ : GlModule n M} (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B) (hd : IsDerivedAction π ι ρ) [MeasurableSpace W] {ν : Measure W} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] (hf : Integrable fun g ↦ f g * ‖g.1.1‖ ^ A) (hv : l.IsKHighest ρ l.lowestKType v) (hc : ι (ρ.casimirK 1 v) = ofReal c • ι v) (hl : l.casimirValue ≤ c)
attribute [local fun_prop] IsUnitaryRep.continuous
lemma rIP [NeZero ν] {f} (i : Integrable f ν) (h : ∀ w, 0 < re (f w)) : 0 < (integral ν f).re := (integral_re i).subst ((integral_pos_iff_support_of_nonneg (h · |>.le) i.re).2 (by simp_all [Function.support, neZero_iff]))
include hu hd in
omit [Nonempty n] in
lemma HCParam.IsKHighest.integral_conj_weightMinors_smul {h} {ν : HCParam ε} (hx : l.IsKHighest ρ ν v) [hg : l.HasGap h] (hν : IsKDominant ε (-l) ν) (φ : _ →L[ℂ] ℂ) : ∫ k, conj (weightMinors ν k) * φ (π k (ι v)) ∂haarK ε = ν.kTypeNormSq * φ (ι v) := by simpa [mul_comm] using (isHolOfWeight_coeffMap hg.neg.1 (fun _ ↦ by simpa) (fun _ ↦ hd.isCoeffMap φ) (.mkPiAlgebra ..)).integral_mul_conj_weightMinors hg.neg.1 hν
include hu hf in
lemma integrable_smul_rep x : Integrable fun g ↦ f g • π g x := by simpa [Pi.smul_def', smul_smul]
  using (hf.smul_bdd (_ * ‖x‖) (f := fun g ↦ (‖g.1.1‖ ^ A : ℂ)⁻¹ • π g x) (by fun_prop)
  (.of_forall fun g ↦ by grw [norm_smul, (π g).le_opNorm, hu.5.choose_spec]; simp [field]))
variable [CompleteSpace X]
include hu hf in lemma map_integratedRep (T : X →L[ℂ] Y) x : T (integratedRep π f x) = ∫ g, f g • T (π g x) := by simp [integratedRep, ← T.integral_comp_comm, integrable_smul_rep hu hf]
include hg
lemma HCParam.HasLargeGap.isIdempotentKernel_dsKernel : IsIdempotentKernel l.dsKernel := ⟨by fun_prop, by simpa using! hg.integrable_norm_pow_smul_dsKernel 0, by simp [↓dsCoeff_inv], by simp, fun x y ↦ by simpa [↓← dsCoeff_inv, mul_left_comm, mul_comm] using congr(l.formalDegree * $(dsCoeff_schur_orthogonality hg y⁻¹ x))⟩
lemma HCParam.HasLargeGap.exists_bump_conv_dsKernel : ∃ α : Bumps ε, ∀ g, ∫ x, α.1.1 x⁻¹ * l.dsKernel (x⁻¹ * g) = l.dsKernel g := (exists_smear_dsCoeffSmooth_eq hg l.dsGenerator).imp fun _ e ↦ (by simpa [↓← dsCoeff_inv, mul_left_comm] using congr($e ·⁻¹))
include hu hd
lemma exIP : ∃ P : _ →ₗ[ℂ] _, integratedRep π l.dsKernel = P dsGenerator ∧ ∀ Y f v, P f (ι (ρ Y v)) = -P ((-l).dsAction Y f) (ι v) := by
  have i f := integrable_smul_rep hu (HasLargeGap.integrable_norm_pow_smul hg.neg f); let P : (-l).DsModule →ₗ[ℂ] _ := by use! (integratedRep π ·.1) <;> simp [DFunLike.ext_iff, integratedRep, i, add_smul, mul_smul, Integrable.fun_smul]
  have k Y (f : (-l).DsModule) v := by simpa [i, add_eq_zero_iff_eq_neg, -map_mul, integral_sub, (i ..).comp_mul_right, integral_mul_right_eq_self fun g ↦ f.1.1 g • π g (ι v)] using ((integral_skew_product (map_mul_right_eq_self _ <|
    expU <| · • Y) (((i ..).add (i ((-l).dsAction Y f) _)).comp_snd _)).2.symm
    |>.trans (congrArg _ (funext fun g ↦ (intervalIntegral.integral_of_le zero_le_one).symm.trans (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ (hasDerivAt_rightDeriv_expU ..).smul (hd.isCoeffMap 1 g Y v t)) (Continuous.intervalIntegrable (by fun_prop) ..)))))
  use l.formalDegree • P, (congrArg _ (funext (by simp))).trans (P.map_smul ..), (eq_unitaryLiePart_add_I_smul ε · ▸ by simp_intro .. [↓map_add, P, integratedRep, *]; abel)
lemma iRDC : integratedRep π l.dsKernel (ι (ρ.casimirK 1 v)) = ofReal l.casimirValue • integratedRep π l.dsKernel (ι v) := by obtain ⟨⟨P⟩, _⟩ := exIP hg hu hd, hg.neg; simp [*, casimirValue]; rw [Finset.sum_comm]; simpa [twoRho_neg, casimirValue] using! congr(P $(casimirK_generatedBy casimir_dsCoeffSmooth _) _)
lemma iR0 {ν} (hv : l.IsKHighest ρ ν v) (q : ν - l.lowestKType ∉ l.rootCone) y : integratedRep π l.dsKernel (π y (ι v)) = 0 := by
  by_contra p; choose _ _ _ _ e u using hu.exists_innerProductSpace
  have hν : IsKDominant ε (-l) ν := fun a b _ _ ↦ have := hd.form_E_eq_sign_mul hu b a v _ ▸ e .. ▸ inner_self_nonneg
    by simp_all [ρ.aaB, IsKHighest, hu.4 (ι v) (by grind)]
  absurd hu.4 _ p; rw [map_integratedRep hu hg.integrable_norm_pow_smul_dsKernel, ← integral_inv_eq_self]
  rcases (hv.integral_conj_weightMinors_smul hu hd hν <| B ·), (integral_conj_weightMinors_mul_dsCoeff hg y · hν (.inr q) |>.trans (ite_eq_right (q <| by simp [·, rootCone]))), fun w ↦ (_root_.integral_conv (y * ·.1)⁻¹ (ν := haarK ε)
    (k := (conj <| weightMinors ν ·)) integrable_of_compactSpace (hg.integrable_norm_pow_smul l.dsGenerator 0) (F := (B w <| π ·⁻¹ (ι v))) (.of ⟨_, fun g ↦ by grw [← e, norm_inner_le_norm, u]⟩)).elim (·.symm.trans)
  simp_all [↓dsCoeff_inv, hu.form_apply_eq_form_inv_apply, ← real_smul]
include hv in lemma re_integratedRep_dsKernel_pos (hp : ∀ z, z.1.1.PosDef → 0 < B (ι v) (π z (ι v))) : 0 < (B (ι v) (integratedRep π l.dsKernel (ι v))).re := by
 have hR w g := hv.integral_conj_weightMinors_smul hu hd hg.isKDominant_lowestKType (B w ∘L π g); have hL w := congr(conj $(by simpa [hu.form_apply_eq_form_inv_apply] using hR w 1)); simp [← integral_conj, hu.3, rep_apply_apply, -map_mul] at *; refine (integral_skew_product (fun q ↦ ((measurePreserving_mul_right _ q.2).mul_left _ q.1⁻¹).2) (((B (ι v)).integrable_comp (integrable_smul_rep hu hg.integrable_norm_pow_smul_dsKernel (ι v))).comp_snd ((haarK ε).prod (haarK ε)))).elim (rIP · (fun g ↦ ?_) |>.trans_eq <| by simp [↓·, map_integratedRep hu hg.integrable_norm_pow_smul_dsKernel])
 obtain ⟨κ, z, hz, ⟨⟨⟩⟩⟩ := exists_polar g; have P (u : USign ε) := hz.conjTranspose_mul_mul_same (mulVec_injective_of_invertible u); simp [fun p ↦ (by simpa using dsCoeff_polar hg (p⁻¹ * κ) ·⁻¹ hz), ← integral_conj, hz.1.eq, ← integral_const_mul, ← integral_mul_const, -map_mul]; rw [integral_integral_swap ?j]; refine rIP (.integral_prod_right ?j) fun u ↦ (pos_iff.1 ?_).1; rw [← integral_mul_left_eq_self _ (κ * u, u), integral_prod_symm _ integrable_of_compactSpace]; simp [← maxCompactU.coe_inv, mul_left_comm (weightMinors _ (Units.val _)), mul_left_comm _ (ofReal _), hL]; simp [*, -map_mul, rep_apply_apply, ← mul_assoc]; exact integrable_of_compactSpace (by fun_prop (disch := simp [P, ← mul_assoc]))
include hv hc hl
attribute [local simp] WithLp.ext_iff IsKHighest in
attribute [-simp] Complex.coe_smul coe_inner Subtype.forall casimir ne_of_gt in
omit [CompleteSpace X] in
lemma cD g : B (ι v) (π g (ι v)) = B (ι v) (ι v) * l.dsCoeff g := by
  obtain ⟨⟨H, _, _, j, f, U⟩⟩ := hu.exists_innerProductSpace, hd.form_E_eq_sign_mul hu; let x := (j.1 ∘ₗ ι).rangeRestrict v; have ⟨σ, q⟩ := ρ.onRange (j.1 ∘ₗ ι) fun X v h ↦ inner_self_eq_zero (𝕜 := ℂ).1 (by nth_rw 1 [apply_eq_sum]; simp_all); have t X y : σ.generatedBy x X y = ⟨_, _⟩ := rfl; obtain ⟨⟨_, _, b⟩⟩ := hg.isUnitaryCasimirGe_dsAction, isKHighest_dsGenerator hg, (⟨fun a b ⟨⟨_, v, rfl⟩, _⟩ ⟨⟨_, w, rfl⟩, _⟩ ↦ by simp [t, coe_inner]; erw [q, q]; simp [*], by
    intro; grw [hl, casimirK_generatedBy (c := c) (by ext; simp_all [x, casimir, ← map_sum])]; simp [sq]⟩ : IsUnitaryCasimirGe l (σ.generatedBy x))
  let P := GlModule.mk ((WithLp.linearEquiv 2 ..).symm.conj.1 ∘ₗ .prodMapLinear .. ∘ₗ (σ.generatedBy x).ρ.prod l.dsAction.ρ) (by simp [DFunLike.ext_iff, map_bracket]); have p X v : P X v = toLp _ _ := rfl; have ⟨I, W⟩ : IsUnitaryCasimirGe l P ∧ ∀ t : ℂ, l.IsKHighest P l.lowestKType
    (toLp _ (⟨x, self_mem_filtration⟩, t • l.dsGenerator)) := by simp_all [IsUnitaryCasimirGe, casimir, ↓p, mul_add, prod_norm_sq_eq_of_L2, add_le_add, x, smul_smul, mul_comm]
  simpa [x, ← f] using! (W 1).coeffMap_eq_zero I (c := fun g ↦ (B _ ∘L π g).1 ∘ₗ (j.symm.1.domRestrict _).domRestrict _ ∘ₗ fstₗ .. - inner ℂ x x • .domRestrict (.proj g) _ ∘ₗ l.DsModule.subtype ∘ₗ sndₗ ..) (fun g Y (toLp _ (⟨⟨_, v, rfl⟩, _⟩, _)) _ ↦ .sub (by simp [*]; erw [q]; simpa using hd.isCoeffMap ..) (.const_mul _
    (hasDerivAt_rightDeriv_expU ..))) (by simp_intro .. [← f]; grw [norm_sub_le, norm_inner_le_norm, norm_mul, b, U, j.apply_symm_apply, norm_coe, norm_coe, WithLp.norm_fst_le, WithLp.norm_snd_le, add_mul])
    (by simpa [-sub_eq_zero, ← f, ← hg.toL2_spec.2, mem_orthogonal', ↓inner_smul_left] using! mem_orthogonal_filtration_of_casimirK 0 I (W 1) _ (W
    (-inner ℂ x x)).casimirK_eq_smul (by simp) ((W 1).fLWM (innerSLFlip ℂ
    _).ker (by simp +contextual [I.1, (W _).2, -neg_smul]) (by simp [*, word]))) g
include hf in
lemma iRFH (hr : ∀ g, ∫ y, f y * l.dsKernel (y⁻¹ * g) = l.dsKernel g) : integratedRep π f (ι v) = ι v := by
  by_contra k; rcases cD hg hu hd hv hc hl, hr 1, hu.4 _ (sub_ne_zero.2 k)
  simp_all [by simpa using dsCoeff_inv hg, map_integratedRep hu, hu.form_apply_eq_form_inv_apply _
    (π _ _), rep_apply_apply, -map_mul, ← hu.3 _ ((_ : X →L[ℂ] X) _), mul_left_comm (f _)]
lemma eCV (o : ι v ≠ 0) : c = l.casimirValue := by
  simpa [*, -casimir, smul_left_inj, (iRFH hg hu hd hg.integrable_norm_pow_smul_dsKernel hv hc hl hg.isIdempotentKernel_dsKernel.convolution_self)] using iRDC hg hu hd (v := v)
