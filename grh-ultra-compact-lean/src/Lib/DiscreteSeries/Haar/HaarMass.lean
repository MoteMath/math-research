import Lib.DiscreteSeries.FlenstedJensen.RepresentationDefs
import Lib.Adelic.QuotientMeasure.CocompactIntegrable
section
noncomputable section
open Complex Matrix NormedSpace Topology U Norms.L2Operator VectorField ContDiff Ring Module
section
variable {n} [Fintype.{0} n] {ε : n → ℤˣ} {J X : Matrix n n ℂ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [AddCommGroup M] [Module ℂ M] (ρ : GlModule n M)
variable (n E) in
def SmoothMat : Submodule ℂ (Matrix n n ℂ → E) := by use! {f | ContDiff ℝ ∞ f}, (·.out.add), contDiff_const (n := ∞); simp; fun_prop
lemma SmoothMat.differentiable (f : SmoothMat n E) : Differentiable ℝ f.1 := ContDiff.differentiable (n := ∞) f.2 nofun
open SmoothMat IsHermInvolution ContinuousLinearMap
@[simp] lemma expU_zero : expU 0 = (1 : U J) := by aesop
@[fun_prop] lemma U.continuous_mat : Continuous (·.1.1 : U J → _) := by fun_prop
@[fun_prop] lemma continuous_expU [IsHermInvolution J] : Continuous (expU (J := J)) := continuous_U_iff_matrix.2 ((@exp_continuous _ _ (.restrictScalars ℚ ℂ _) _).comp (by fun_prop))
lemma hasDerivAt_expU (Y : unitaryLie J) g t : let γ (t : ℝ) := (g * expU (t • Y)).1.1; HasDerivAt γ (γ t * Y) t := by simp [mul_assoc, (hasDerivAt_exp_smul_const ..).const_mul]
variable (ε X E)
abbrev SmoothU := (.funLeft ℂ E (·.1.1 : USign ε → _) ∘ₗ (SmoothMat ..).subtype).range
attribute [local simp] mul_add add_mul det_ne_zero mul_sub sub_mul mul_assoc
attribute [local instance] LieRing.ofAssociativeRing
@[irreducible] def GlModule.onRange {N} [AddCommGroup N] [Module ℂ N] (ι : M →ₗ[ℂ] N) (h : ∀ X x, ι x = 0 → ι (ρ X x) = 0) : {σ : GlModule n _ // ∀ X x, σ X (ι.rangeRestrict x) = ι.rangeRestrict (ρ X x)} := by use! fun X ↦ ι.quotKerEquivRange.conj (ι.ker.mapQ _ _ (h X)) <;> aesop (add simp [map_bracket, DFunLike.ext_iff, LinearMap.codRestrict, ι.quotKerEquivRange_symm_apply_image])
def unitaryLiePart : unitaryLie (signMatrix ε) := ⟨(2⁻¹ : ℝ) • (X - (signMatrix ε)⁻¹ * Xᴴ * signMatrix ε), by simp [unitaryLie, isHermitian.inv.eq, isHermitian.eq]⟩
lemma eq_unitaryLiePart_add_I_smul X : X = unitaryLiePart ε X + I • unitaryLiePart ε (-I • X) := by ext; simp [unitaryLiePart]; grind [I_sq]
def rDM : GlModule n (SmoothMat n E) := let r X : End ℂ (SmoothMat n E) := (by
 use! fun f ↦ ⟨_, (contDiff_infty_iff_fderiv.1 f.2).2.clm_apply ((mul ℝ _).flip (unitaryLiePart ε X).1).contDiff⟩ <;> aesop (add simp [fderiv_add, fderiv_const_smul, (SmoothMat.differentiable _ _)])); by
 refine ⟨⟨⟨fun X ↦ r X + I • r (-I • X), ?_⟩, fun ⟨_, _⟩ ↦ ?_⟩, fun _ _ ↦ .trans ?_ (lie_def ..)⟩
 all_goals intros; ext f; simp +decide [r, lieBracket, -flip_apply, ← fderiv_apply_lieBracket (contDiffAt (n := ∞) f.2)]; simp [unitaryLiePart, mk_eq_add_mul_I, add_smul, smul_sub, mul_smul, smul_smul I, @smul_comm ℂ]; module
def rightDeriv : GlModule n (SmoothU ε E) := ((rDM ε E).onRange _ fun X f h ↦
 funext fun g ↦ by have k Y := ((SmoothMat.differentiable f _).hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_expU Y g 0)).deriv.symm.trans congr(deriv ($h ∘ _) _); simp_all [rDM]).1
variable {ε X E}
@[fun_prop] lemma SmoothU.continuous : ∀ f : SmoothU ε E, Continuous f.1
 | ⟨_, F, rfl⟩ => (SmoothMat.differentiable F).continuous.comp continuous_mat
lemma hasDerivAt_curve f {γ : ℝ → USign ε} {t} (h : HasDerivAt (γ · |>.1.1) ((γ t).1 * X) t) : HasDerivAt (f.1 <| γ ·) ((rightDeriv ε E X f).1 (γ t)) t := have ⟨_, F, rfl⟩ := f; ((SmoothMat.differentiable ..).hasFDerivAt.comp_hasDerivAt t h).congr_deriv (by
 erw [(GlModule.onRange ..).2]; simp [rDM, unitaryLiePart, ← two_smul ℝ, by simpa [logDerivU, h.deriv, ← mul_assoc, mem_U.1, isHermitian.eq] using (conjTranspose_logDerivU h.differentiableAt 1)])
lemma hasDerivAt_rightDeriv_expU f g Y t : let γ (t : ℝ) := g * expU (t • Y); HasDerivAt (f.1 <| γ ·) ((rightDeriv ε E Y f).1 (γ t)) t := hasDerivAt_curve f (hasDerivAt_expU ..)
lemma rDF {f F g} {D : _ →L[ℂ] _} (hF : HasFDerivAt F D g.1.1) (h : ∀ g, F g.1.1 = f.1 g) X : (rightDeriv ε E X f).1 g = D (g * X) := eq_unitaryLiePart_add_I_smul ε X ▸ have k Y := ((funext h ▸ hasDerivAt_rightDeriv_expU ..).unique ((hF.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 (hasDerivAt_expU Y g _) (by simp))); by aesop
lemma rDC {f f' g} (L : E →L[ℂ] ℂ) (h : f'.1 =ᶠ[𝓝 g] L ∘ f.1) : (rightDeriv ε ℂ X f').1 =ᶠ[𝓝 g] L ∘ (rightDeriv ε E X f).1 := h.eventually_nhds.mono fun y h ↦ have k Y := ((hasDerivAt_rightDeriv_expU ..).unique (((hasDerivAt_rightDeriv_expU f y Y 0).map_clm L).congr_of_eventuallyEq (Continuous.tendsto' (by fun_prop) 0 y (by simp) h))); eq_unitaryLiePart_add_I_smul ε X ▸ by simp_all
lemma one_le_cast_card n [Fintype n] [Nonempty n] : (1 : ℝ) ≤ Fintype.card n := mod_cast NeZero.one_le
end
end
end
section
open Haar Matrix MeasureTheory Complex Fintype Module LinearMap Norms.L2Operator MatMul
variable {n} [Fintype n] (k₀ : n)
set_option synthInstance.maxSize 999
omit [Fintype n] in
@[scoped simp] lemma Haar.val_ne_and_ne_val (i : Subtype (· ≠ k₀)) : i ≠ k₀ ∧ k₀ ≠ i := by lia
noncomputable def skewColumnEquiv := (HasGaussianIntegral.exists_measurePreserving_equiv ⟨⟨fun y ↦ ((y k₀ k₀, (skewOfReal y ·.1 k₀ : Subtype (· ≠ k₀) → ℂ)), y.toBlock (· ≠ k₀) (· ≠ k₀)), by aesop⟩, by aesop⟩ (by simp [add_assoc, skewOfReal, div_pow, sum_eq_add_sum_subtype_ne _ k₀, ← Finset.sum_add_distrib, RCLike.norm_sq_eq_def]; grind) (by simp [finrank_matrix]; zify [@card_pos _ _ ⟨k₀⟩]; lia)).choose.toContinuousLinearEquiv
@[simp] lemma skewColumnEquiv_spec : MeasurePreserving (skewColumnEquiv k₀) ∧ ∀ y, (skewColumnEquiv k₀).symm y = ((y k₀ k₀, (skewOfReal y ·.1 k₀)), y.toBlock _ _) := by simp [skewColumnEquiv]; grind
@[simp] lemma skewOfReal_skewColumnEquiv : ∀ p, letI S := skewOfReal (skewColumnEquiv k₀ p); S k₀ k₀ = p.1.1 * I ∧ ∀ i, S i.1 k₀ = p.1.2 i ∧ S k₀ i = -star (p.1.2 i) ∧ ∀ j, S i j.1 = skewOfReal p.2 i j := by simp [↓reindex_equiv (skewColumnEquiv _).symm, -skewColumnEquiv_spec]; simp [skewOfReal]; grind
lemma cayleyChart_col_injective : (fun θ ↦ (cayleyChart 1 (skewColumnEquiv k₀ (θ, 0))).1.1.col k₀).Injective := fun _ _ ↦ by
 have a θ := (and_forall_ne k₀).2 (congrFun₂ (mul_nonsing_inv _ (det_cayleyDenom_one_ne_zero (skewColumnEquiv k₀ (θ, 0))).isUnit) · k₀); simp_all [sum_eq_add_sum_subtype_ne _ k₀, mul_apply, funext_iff, -Prod.forall, val_cayleyChart_coe, Subtype.forall', -Subtype.forall, cayleyDenom, Subtype.val_inj]; grind +extAll [ofReal_inj, I_ne_zero, sum_eq_zero]
lemma abs_det_logDerivU_col_eq_cayleyDensity θ : |(fst .. ∘ₗ (skewColumnEquiv _).symm.1.1 ∘ₗ skewCoords ∘ₗ logDerivU (cayleyChart 1) (skewColumnEquiv k₀ (θ, 0)) ∘ₗ (skewColumnEquiv k₀).1.1 ∘ₗ inl ..).det| = cayleyDensity 1 (skewColumnEquiv _ (θ, 0)) := by
 have h := abs_det_skew_congruence (skewColumnEquiv k₀).1.symm ?D
  (coprod ?L ((skewColumnEquiv _).1.1 ∘ₗ inr ..))
 rw [← LinearMap.det_conj _ (.prodComm ..), det_eq_mul_of_block_triangular id _ (id.ext _), det_eq_mul_of_block_triangular (fst .. ∘ₗ (skewColumnEquiv _).symm.1.1 ∘ₗ ?L) _ (id.ext _)] at h; simpa [cayleyDensity, pow_mul] using eq_inv_of_mul_eq_one_right (h.symm.trans (by simp))
 repeat simp [conjTranspose_nonsing_inv, Prod.mk_zero_zero, lCC, -skewColumnEquiv_spec] <;> simp [entrywise, skewCoords, cayleyDenom, sum_eq_add_sum_subtype_ne _ k₀] <;> simp [skewOfReal] <;> grind
end
section
open Matrix MeasureTheory Real Complex Fintype Haar Subtype
lemma lintegral_cayleyDensity_skewColumnEquiv {n} [Fintype n] (k₀ : n) η {a} (_ : 0 < a) : ∫⁻ θ, .ofReal (cayleyDensity 1 (skewColumnEquiv k₀ (θ, η)) / (sphereDensity (card n) 1 * a)) = .ofReal (cayleyDensity 1 η / a) := by
 obtain ⟨⟨k⟩⟩ := Nat.exists_eq_add_of_lt (@card_pos _ _ ⟨k₀⟩), det_cayleyDenom_one_ne_zero η; choose x e using (canLift.1 (star _) <| neg_eq_zero.2 <| IsHermitian.im_star_dotProduct_mulVec_self (skewAdjoint.negISMul ⟨_, conjTranspose_skewOfReal η⟩).2 ·); erw [lintegral_prod_symm, lintegral_eq_det_mul (ofReal 2 • _) (by simpa), lintegral_congr fun w ↦ ?e, lintegral_mul_const, lintegral_inv_add_rpow one_pos, ← @doublingGamma_eq_Gamma (2 * k.succ - 1)]
 case' e => rw [lintegral_congr fun _ ↦ ?p, lintegral_mul_const (.ofReal (rpow ‖-I / 2 * (cayleyDenom 1 η).det‖ _ / _)), lintegral_norm_add_rpow ⟨-x w, (_ + _) * 2⟩, mul_rpow, rpow_neg_eq_inv_rpow, mul_left_comm, ENNReal.ofReal_mul, mul_assoc]
 case' p => erw [← ENNReal.ofReal_mul, mul_div, ← mul_rpow, ← norm_mul, ← mul_assoc]; simp [ cayleyDensity, rpow_neg, rpow_mul, -norm_mul, -Complex.norm_mul, -Nat.cast_add]; congr
 any_goals first | fun_prop | finiteness | simp [*] <;> grind
 convert det_updateCol_sum _ k₀ (val.extend w 1) ▸ twoBlockTriangular_det₀ _ (· = k₀)
  (Subtype.forall'.2 _); aesop
 repeat simp [*, toSquareBlockProp, entrywise, mk_eq_add_mul_I, sum_eq_add_sum_subtype_ne _ k₀, ← Finset.mul_sum, conj_mul', mul_assoc, mul_comm (w _), default, cayleyDenom, sub_mul, val_inj] <;> grind [I_sq]
 simp (disch := positivity) [← ENNReal.ofReal_mul, doublingGamma, ← add_sub, rpow_add, ← Real.Gamma_nat_eq_factorial, *, rpow_neg, field, two_mul, mul_pow]; ring
end
open MeasureTheory Measure Fintype
variable {n} [Fintype.{0} n]
instance isProbabilityMeasure_haarU : @IsProbabilityMeasure (U (1 : Matrix n n ℂ)) _ volume := ⟨by
 simp [← lintegral_one, ↓lintegral_eq_cayleyChart]; induction' hk : card n with k ih generalizing n; rw [card_eq_zero_iff] at hk; simpa [volU] using! pi_empty_univ _
 erw [volU, Finset.prod_range_succ_comm, ← (skewColumnEquiv_spec ((equivFinOfCardEq hk).2 0)).1.lintegral_comp, lintegral_prod_symm,
  funext (hk ▸ lintegral_cayleyDensity_skewColumnEquiv _ · (vUP k) :), ih] <;> measurability⟩
instance : @IsProbabilityMeasure (U (@signMatrix n 1)) _ volume := by rw! [signMatrix_one]; infer_instance
instance {J} [@IsHermInvolution n _ J] : (@volume (U J) _).IsMulRightInvariant := ⟨(measurePreserving_haarU 1 · 1 (.mulRight _) |>.2)⟩
