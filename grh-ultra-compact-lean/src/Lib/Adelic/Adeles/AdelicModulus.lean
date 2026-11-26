import Lib.ClassField.HeckeL.EulerProduct
import Lib.Adelic.Adeles.RationalPoints
import Lib.General.Algebra.GeneralisedIndex
import Lib.Weil.DualPair.Kronecker
import Lib.General.Algebra.InertResidue
noncomputable section
section
open MonoidHom NumberField FinitePlace
variable {E} [Field E] [NumberField E] {x : (𝔸 E)ˣ}
def ideleAbs : (𝔸 E)ˣ →* ℝ := ⟨⟨fun x ↦ (∏ w, ‖x.1.1 w‖ ^ 2) * ∏ᶠ w, ‖x.1.2 w‖, by simp⟩, fun x y ↦ have h (z : (𝔸 E)ˣ) t := (finite_idele_val_ne_one (z.map (snd ..))).subset (t := t); by simp +contextual [sq, norm_def, not_imp_not, field, finprod_mul_distrib (h x _ _) (h y _ _)]⟩
@[simp] lemma ideleAbs_nonneg_and_ne_zero : 0 ≤ ideleAbs x ∧ ideleAbs x ≠ 0 := ⟨mul_nonneg (by positivity) (finprod_nonneg (by simp)), (toHomUnits _ x).ne_zero⟩
@[simp] lemma ideleAbs_pos : 0 < ideleAbs x := by simp [lt_of_le_of_ne']
lemma ideleAbs_eq_prod_of_v_eq_one : (∀ w, Valued.v (x.1.2 w) = 1) → ideleAbs x = ∏ w, ‖x.1.1 w‖ ^ 2 := by simp_all [ideleAbs, norm_def]
@[fun_prop] lemma continuous_ideleAbs : Continuous (@ideleAbs E _ _) := continuous_of_continuousAt_one _ (.congr (by fun_prop) (.mono (((continuous_snd.units_map (snd ..)).1 _ (isOpen_idelesUnitOff ∅)).mem_nhds (by simp)) fun _ _ ↦ (ideleAbs_eq_prod_of_v_eq_one (by aesop)).symm))
lemma ideleAbs_toAdele [IsTotallyComplex E] [PlaceEmbedding E] (x : Eˣ) : @ideleAbs E _ _ (x.map (toAdele (E := E))) = 1 := by simpa [← finprod_comp_equiv equivHeightOneSpectrum.symm, ideleAbs, ← InfinitePlace.apply] using! prod_abs_eq_one x.ne_zero
@[simp] lemma ideleAbs_star [IsCMField E] : ideleAbs (star x) = ideleAbs x := congr($(by simp) * $(finprod_eq_of_bijective _ star_involutive.bijective (by simp [norm_def])))
lemma ideleAbs_eq_one_of_mem_unitary [IsCMField E] (h : x.1 ∈ unitary _) : ideleAbs x = 1 := by simpa using congr(√(ideleAbs $((Units.unitary_eq.ge h).1)))
end
open LinearMap RingHom Subgroup Units Algebra Matrix MeasureTheory NumberField Valued WithZero MeasureTheory.Measure FinitePlace Valuation.IsRankOneDiscrete Valuation.IsUniformizer
variable {E n : Type*} [Field E] [NumberField E] [Fintype n] {w : FinPlace E} (a : GL n (𝔸 E))
lemma v_uniformizer_inv_mul_le_one_iff {y} : v ((uniformizer w).1⁻¹ * y) ≤ 1 ↔ v y < 1 := by simp [← lt_mul_exp_iff_le]
lemma norm_locField_eq_q_zpow {x : LocField w} : x ≠ 0 → ‖x‖ = w.q ^ (v x).log := by simp_all [FinitePlace.norm_def, WithZeroMulInt.toNNReal]
private lemma eq_inv_norm (χ : (LocField w)ˣ →* ℝ) (h : ∀ {x}, v x.1 = exp (-1) → χ x = w.q) {x} : χ x = ‖x.1‖⁻¹ := by simpa [norm_locField_eq_q_zpow, h (v_uniformizer w), field] using @h (x * uniformizer w ^ (v x.1).log * uniformizer w) (by simp [WithZero.exp_neg, -inv_exp])
lemma isValuationPair_Ohat : IsValuationPair (Ô E) := fun a b ↦ ⟨⟨_, idem_mem_Ô {w | v (a w) ≤ v (b w)}⟩, by aesop (add simp [exists_eq_mul_iff_v_le, idem_apply, le_of_lt])⟩
instance [IsCMField E] : IsStarStable (Ô E) := ⟨star_mem_Ô⟩
def finIdeleAbs := (@ideleAbs E).comp finIdeleIncl
@[simp] lemma finIdeleAbs_principalIdele x : finIdeleAbs (principalIdele (x : Eˣ)) = |Algebra.norm ℚ x.1|⁻¹ := by simpa [finIdeleAbs, ideleAbs, ← (finprod_comp_equiv equivHeightOneSpectrum.symm)] using! prod_eq_inv_abs_norm x.ne_zero
@[simp] lemma finIdeleAbs_locIdele x : finIdeleAbs (locIdele w x) = ‖x.1‖ := by simp_all [finIdeleAbs, ideleAbs, finprod_eq_single _ w]
lemma genIndex_eq_inv_finIdeleAbs (a : (𝔸f E)ˣ) : genIndex a.1 = (finIdeleAbs a)⁻¹ :=
  mem_of_locIdele_mem (H := (genIndex.1.comp (coeHom _)).eqLocus (invMonoidHom.comp _)) (isClosed_of_isOpen _ (isOpen_mono (fun _ _ ↦ .symm (by simp_all [Nat.card_unique, genIndex_eq_card isOpen_Ô isCompact_Ô, mem_Ô, finIdeleAbs, ideleAbs_eq_prod_of_v_eq_one])) (isOpen_idelesUnitOff ∅))) fun w ↦
  .trans (eq_inv_norm ((genIndex.1.comp _).comp _) (fun _ ↦ by
    erw [← card_ResField, ← Nat.card_congr (quotientKerEquivOfSurjective (funext (reduceAt_algebraMap w) ▸ algebraMap_ResField_surjective w).of_comp).1, genIndex_eq_card isOpen_Ô isCompact_Ô (mem_Ô.2 _)]
    congr with
    all_goals simp_all +decide [Ideal.mem_span_singleton, Subtype.ext_iff, dvd_def, ← and_forall_ne w, exists_eq_mul_iff_v_le, mem_Ô.1, ← lt_mul_exp_iff_le, ← WithZero.exp_add])) (by simp)
lemma genIndex_eq_inv_norm (a : (LocField w)ˣ) : genIndex a.1 = ‖a.1‖⁻¹ := eq_inv_norm (genIndex.1.comp (coeHom _)) (by erw [genIndex_eq_card (isOpen_valuationSubring _) (isCompact_LocInt _), ← is_generator, card_ResField] <;> simp_all +decide [iff, generator_eq_exp_neg_one_of_mem_range ⟨_, ·⟩])
lemma map_mulVec_haar_finAdele μ [IsAddHaarMeasure μ] (a : GL n (𝔸f E)) : μ.map (a.1 *ᵥ ·) = ENNReal.ofReal (finIdeleAbs a.det)⁻¹ • μ := (distribHaarChar_GL_eq_det isOpen_Ô isCompact_Ô isValuationPair_Ohat a).trans (genIndex_eq_inv_finIdeleAbs a.det) ▸ map_smul_eq_inv_distribHaarChar_smul a
lemma volume_map_mulVec_adele : volume.map (a.1 *ᵥ ·) = ENNReal.ofReal (ideleAbs a.det)⁻¹ • volume := map_haar_eq_smul_of_semiconj _ (.mk ⟨.arrowProdEquivProdArrow .., by tauto⟩) (congrFun (by ext : 3; exacts [Prod.fst_sum, Prod.snd_sum])) ((MeasurePreserving.prod ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, map_linearMap_addHaar_eq_smul_addHaar addHaar ((a.map (.fst ..)).toLin.toLinearEquiv.restrictScalars _).isUnit_det'.ne_zero⟩ ⟨by fun_prop, map_mulVec_haar_finAdele volume (a.map (.snd ..))⟩).2.trans (by erw [det_restrictScalars, det_toLin', ← map_det, a.map_det, det_pi (mul ℝ ℂ ∘ _), funext (norm_complex_apply ∘' _)]; simp [ideleAbs, finIdeleAbs, ← Complex.sq_norm, prod_smul_left, prod_smul_right, mul_smul, finprod_nonneg, Finset.prod_pow])) ((LinearMap.continuous_of_finiteDimensional _).measurable.prodMap (by fun_prop))
@[simp] lemma det_star [IsCMField E] : (star a).det = star a.det := Units.ext (det_conjTranspose _)
lemma volume_map_mul_mul_adele (b : GL Unit (𝔸 E)) : volume.map (α := Matrix n Unit (𝔸 E)) (a.1 * · * b.1) = ENNReal.ofReal (ideleAbs (b.det ^ Fintype.card n * a.det))⁻¹ • volume := map_haar_eq_smul_of_semiconj _ (.mk ⟨.mk _ (· <| Prod.swap ⟨·, ·⟩), vec_add⟩) (.symm <| kronecker_mulVec_vec _ · _) ((volume_map_mulVec_adele (kroneckerGL ..)).trans (by simp [ideleAbs]; erw [det_kronecker']; simp))
