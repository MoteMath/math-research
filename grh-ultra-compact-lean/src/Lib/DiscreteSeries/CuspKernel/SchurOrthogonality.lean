import Lib.General.LinearAlgebra.SmoothMatrices
import Lib.General.LinearAlgebra.BlockDiagonalDet
import Lib.DiscreteSeries.FlenstedJensen.PsiBasic
import Lib.DiscreteSeries.Haar.RegularRepL2
import Lib.DiscreteSeries.Rigidity.AnalyticVectors
section
open Set Matrix.Norms.L2Operator
attribute [-simp] finsum_eq_sum_of_fintype
variable {n : Type} [Fintype n] {ε} (l : @HCParam n ε)
@[simps] noncomputable def HCParam.dsCoeffSmooth : SmoothU ε ℂ := ⟨(l.dsCoeff ·), (SmoothPartitionOfUnity.exists_isSubordinate _ isClosedEmbedding_U.2 _ (fun _ ↦ isOpen_analyticAt ℂ l.dsCoeff) (subset_iUnion_of_subset () (range_subset_iff.2 aDC))).elim fun f h ↦ ⟨⟨_, (f.contMDiff_finsum_smul fun i _ x ↦ (h i x).restrictScalars.contDiffAt.contMDiffAt).contDiff⟩,
 funext (by simp [↓← finsum_smul, f.sum_eq_one])⟩⟩
@[fun_prop] lemma continuous_dsCoeff {X} [TopologicalSpace X] {f : X → USign ε} : Continuous f → Continuous (l.dsCoeff <| f ·) := (SmoothU.continuous l.dsCoeffSmooth).comp
end
section
open Matrix Filter Norms.L2Operator ContinuousMap GlModule U HCParam
variable {n} [Fintype n] {ε h} {l : n → ℤ}
lemma exists_equiv_fin_lt_iff (hl : l.Injective) : ∃ e : Fin (Fintype.card n) ≃ n, ∀ a b, l (e a) < l (e b) ↔ a < b := ⟨_, fun _ _ ↦ lt_iff_lt_of_le_iff_le (@monoEquivOfFin n _ (.lift' l hl) _ rfl).2⟩
lemma casimir_dsCoeffSmooth {l : @HCParam n ε} [hg : l.HasGap h] : (rightDeriv ε ℂ).casimirK 1 l.dsCoeffSmooth = (l.casimirValue : ℂ) • l.dsCoeffSmooth := by
  ext g; have ⟨_, hF, e⟩ := iAF g l analyticAt_const rfl; obtain ⟨⟨_, d, e'⟩, _⟩ := exists_contDiff_eventuallyEq hF.restrictScalars.contDiffAt, hg.neg.signs_one; let f : SmoothU ε _ := ⟨_, ⟨_, d⟩, rfl⟩
  have ⟨L, ψ⟩ : ∃ L : StrongDual ℂ _, l.dsCoeffSmooth.1 =ᶠ[_] L ∘ f.1 := ⟨l.lowestKType.kTypeNormSq⁻¹ • strongIntegral (haarK ε) (evalCLM ℂ), .mono (continuous_mat.tendsto _ (e.and (e'.and (tendsto_id.const_mul _ (isAccretive_blockDiagPart_inv_mul g).2.setOf_mem_nhds)))) (by simp +contextual [f, strongIntegral_eval, dsCoeff_eq_flenstedJensen hg (blockDiagPart_mem g), flenstedJensen,
    field])⟩
  suffices ((rightDeriv ε C(_, ℂ)).casimirK 1 f).1 g = ((-l).compactForm.casimirKValue (paramAddRho l) : ℂ) • f.1 g by convert congr(L $this) <;> simp [casimir, (rDC _ (rDC _ ψ)).eq_of_nhds, ↓ψ.eq_of_nhds, casimirKValue, casimirValue, twoRho_neg, ← sub_eq_of_eq_add (two_mul_paramAddRho hg _)]; grind [twoRho]
  ext k; exact ((rightDeriv ε _).onRange ⟨⟨(Germ.ofFun <| evalCLM ℂ k ∘ ·.1), by simp⟩, by tauto⟩ fun _ _ h ↦ (rDC (f' := 0) _ (Quotient.exact h.symm)).germ_eq.symm.trans (by simp)).rec fun σ s ↦ congr($((by simp [↓casimirK_one_adTwist, casimir, s] : LinearMap.rangeRestrict _ (casimirK _ _ f) = _).trans (IsKHighest.casimirK_eq_smul (σ := σ.adTwist k) (.of_E_eq_smul fun a b q o ↦ (s _ f).trans (Subtype.ext (Quot.sound (.mono (continuous_mat.tendsto _ ((e.and e').eventually_nhds.and (hF.congr e'.symm).eventually_analyticAt)) fun y ⟨hy, _, D⟩ ↦ congr($(rDF D.hasFDerivAt (by tauto) _) k).trans (fBE 1 ((evalCLM ℂ k).hasFDerivAt.comp _ D.hasFDerivAt) o q ((y * ·) ∘ (k * · * k⁻¹)) (hy.mono (by intros; simp_all [hy.self_of_nhds, ← mul_assoc, diagChar,
    field, hg.iKN.weightMinors_mul_borel hg.1]))))))))).1.value)
end
section
open Matrix MeasureTheory Finset Real ComplexOrder Norms.L2Operator PosDef U
variable {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) {c : ℕ} (hc : c ≤ h) (g : USign ε)
lemma weightMinors_pos {z} (hz : PosDef z) w : 0 < @weightMinors n _ w z := by apply finprod_induction <;> simp_all [principalMinor, toSquareBlockProp, toBlock, det_pos, hz.submatrix, apply_ite]
include hg hc
lemma norm_dsCoeff_sq_mul_det_pow_le_one : ‖l.dsCoeff g‖ ^ 2 * ‖(blockDiagPart ε g).det‖ ^ c ≤ 1 := by
  have d (g : USign ε) (p : g.1.1.PosDef) : ‖(blockDiagPart ε g).det‖ ^ c ≤ ‖weightMinors (-paramAddRho l) g‖ ^ 2 := by
    let v i := paramAddRho l i + ite True ↑c 0; have q : (blockDiagPart ε g).PosDef := p.1 ▸ (by simp [blockDiagPart_eq, ← inv_mat, p, PosDef.add, PosDef.smul])
    suffices ‖weightMinors v (blockDiagPart ε g)‖ ≤ ‖_ * weightMinors (paramAddRho l) g * weightMinors v g⁻¹‖ by simpa [v, principalMinor_of_forall, ↓weightMinors_add_ite, weightMinors_neg, wUI, q.isAccretive, field]
    obtain ⟨⟨⟩, ⟨B⟩⟩ := hg.mono hc, Finite.exists_le (|paramAddRho l| ⊔ |v|); norm_cast at *; simp_all [abs_le, jacobi_complementary_minor, weightMinors_eq_det_zpow_mul_prod _ (-B) B, mul_assoc, ← prod_mul_distrib]; gcongr; grw [← fischer_inequality p.posSemidef (e := fun _ ↦ not_not), principalMinor_compl]; simp; apply (fischer_inequality q.posSemidef ..).trans_eq congr(_ * ‖$(ext fun _ _ ↦ ite_eq_left _).det‖)
    repeat grind [paramAddRho]
  obtain ⟨I, k, z, ⟨p⟩⟩ := Integrable.of_integral_ne_zero (kTypeNormSq_pos l.lowestKType).ne', exists_polar g; simp [*, by simpa using dsCoeff_polar hg k 1 p, ← maxCompactU.coe_inv]; grw [norm_integral_le_of_norm_le (((I.comp_mul_left k).add I).div_const (2 * √(‖(blockDiagPart ε g).det‖ ^ c))) (.of_forall fun x ↦ ?_), integral_div, integral_add' integrable_of_compactSpace, ← integral_mul_left_eq_self _ k⁻¹, ← div_div] <;> simp [field, *, div_self_le_one]; grw [← mul_rotate, two_mul_le_add_sq, sqrt_le_iff.2]; swap; simpa [← mem_maxCompactU] using d (x⁻¹ * z * x) (by simp [maxCompactU.coe_inv, p.conjTranspose_mul_mul_same, mulVec_injective_of_isUnit])
  repeat simp [← mem_maxCompactU]
lemma norm_dsCoeff_le_pow [Nonempty n] : ‖l.dsCoeff g‖ ≤ (2 / ‖g.1.1‖) ^ c := by grw [← sq_le_sq₀, pow_right_comm, ← inv_div, inv_pow, sq_le_norm_det_blockDiagPart] <;> simp [field, norm_dsCoeff_sq_mul_det_pow_le_one hg hc]
end
section
open Matrix MeasureTheory ComplexConjugate Norms.L2Operator ComplexOrder
attribute [local simp] diagTorus Pi.star_def ne_of_gt wUI
lemma integral_conj_weightMinors_mul_dsCoeff {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) (x b : USign ε) {ν} (hν : IsKDominant ε (-l) ν) (hz : ν = l.lowestKType ∨ ν - l.lowestKType ∉ l.rootCone) : ∫ k, conj (weightMinors ν k.1) * l.dsCoeff ↑(x * k * b) ∂haarK ε = if ν = l.lowestKType then l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff b) else 0 := by
  obtain ⟨o, ho, N, hN, hz⟩ : ∃ o, _ ∧ ∃ N : ℕ, N = o ⬝ᵥ (ν - l.lowestKType) ∧ (N = 0 ↔ ν = l.lowestKType) := hz.elim (⟨-l, by simp [·]⟩) (not_forall₂.1 · |>.imp fun o h ↦ ⟨h.1, _, Int.toNat_of_nonneg (by lia), by aesop⟩)
  have oj : o.Injective | i => by have := ho i; grind [HasGap]
  obtain ⟨⟨T, D⟩, c, _, rfl, ca, _⟩ := (by grind [IsKDominant, mt (ho _ _), HasGap, Pi.neg_apply, paramAddRho] : (Unit → IsKDominant ε o ν) ∧ IsKDominant 1 (-o) (-paramAddRho l)), exists_analytic_path (.inl rfl) b (by simp); let S y (k : maxCompactU ε) := k.1.1.1ᴴ * y * k; obtain ⟨I, p, Z⟩ := neg_injective.comp oj, l.aDC, isCompact_univ.eventually_forall_mem (x₀ := 1) (fun y k ↦ S ((blockDiagPart ε x)⁻¹ * x) k * y) {z | z.IsAccretive} (by simp [S, IsAccretive.setOf_mem_nhds])
  rw [← mul_boole]; generalize (1 : ℝ) = t; revert t; refine congrFun (AnalyticOnNhd.eq_of_eventuallyEq (fun t _ ↦ ((IsAnalyticFamily.of_analyticAt (.prodMk ?_ ?_) (fun (b, y, z) ↦ y * l.dsCoeff (z * b)) fun k ↦ have := p (x * ↑k * c t); ?_).analyticAt_integral _).restrictScalars.comp (ca t)) (fun t _ ↦ have := (p (c t)).restrictScalars (𝕜 := ℝ); ?_) (.mono ((ca 0).continuousAt (isCompact_univ.eventually_forall_mem S _ fun k _ ↦ (Z.and (.and PosDef.one.isAccretive.setOf_mem_nhds (eventually_exists_torus_entire_factor I D Z))).filter_mono (by simp [*, S, ← maxCompactU.coe_inv]))) fun t h ↦ ?_)) <;> try fun_prop (disch := simp)
  choose U W A C tC _ _ P _ e using (by simpa [S, -Subtype.forall] using h); let G (j k : maxCompactU ε) y := weightMinors l.lowestKType (blockDiagPart ε x * j) * conj (weightMinors l.lowestKType k) / weightMinors (-paramAddRho l) (S ((blockDiagPart ε x)⁻¹ * x) j * y); have : Continuous (fun j k ↦ weightMinors ν (k * j⁻¹).1 * G j k (S (c t) k)).uncurry := by unfold G S; fun_prop (disch := simp [U])
  simp only; rw [dsCoeff, dsCoeff_eq_flenstedJensen hg (one_mem _) (by simpa using W 1), flenstedJensen, flenstedJensen]; field_simp; simp_rw [← integral_prod_mul, ← integral_mul_const]; refine .trans ?_ (((measurePreserving_mul_prod ..).fubini (integrable_of_compactSpace this)).2.trans (integral_eq_of_circle_mean (fun θ ↦ map_mul_right_eq_self _ (1, diagTorusK (θ.toCircle ^ o ·))) (integrable_of_compactSpace this) fun (j, k) ↦ .trans ?_ (((isHolOfWeight_weightMinors oj k T).circle_mean_weightMinors oj T (fun _ ↦ mem_maxCompactU.1 j⁻¹.2) (fun s ↦ s ^ N * G j k (A k s) / diagChar (-paramAddRho l) (C k)) ?_).trans ?_)))
  · congr with k; rw [dsCoeff_eq_flenstedJensen hg (mul_mem (blockDiagPart_mem x) (mem_maxCompactU.1 k.2)), flenstedJensen] <;> simp [G, S, mul_assoc, ← maxCompactU.coe_inv]
    simpa [S, mul_assoc, ← maxCompactU.coe_inv] using U 1 k
  · congr with θ; set s := θ.toCircle; have := D.weightMinors_mul_borel I (P k s s.norm_coe.le j).det_ne_zero
      (by simp) (((isBorelMatrix_diagonal s).mul (tC k)).mul (isBorelMatrix_diagonal s⁻¹))
    simp at this; rw [mul_assoc, ← (A k s).mul_assoc, ← e] at this; simp [G, S, mul_assoc, conj_weightMinors, dotProduct, diagChar, hN, ← _root_.zpow_mul, ← zpow_sum_of_ne_zero, mul_sub, zpow_sub₀, ← s.coe_inv_eq_conj, ← zpow_natCast s.1] at *; simp [*]; field_simp; simp
  simp_intro s r; fun_prop (disch := simp [*, S, -det_mul, IsAccretive.det_ne_zero]); simp [zero_pow_eq]; grind
end
section
noncomputable section
open MeasureTheory ContinuousLinearMap Set Matrix Norms.L2Operator
variable {n} [Fintype n] (ε : n → _) {E} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev Bumps : Submodule ℂ (SmoothU ε ℂ) := ⟨⟨⟨{β | HasCompactSupport β.1}, .add⟩, .zero⟩, fun _ ↦ .smul_left⟩
variable {ε} (F : USign ε → E) (α : Bumps ε) (hF : Continuous F := by fun_prop)
def bumpDeriv := (rightDeriv ..).restrictTo (Bumps ε) fun _ f ↦ (.intro · fun _ h ↦ (rDC (f := f) 0 (notMem_tsupport_iff_eventuallyEq.1 h)).eq_of_nhds)
include hF
lemma integrable_bump_inv_smul : Integrable fun y ↦ α.1.1 y⁻¹ • F y := (α.2.comp_homeomorph (.inv _)).smul_right.integrable
@[simps] def smear : Bumps ε →ₗ[ℂ] USign ε → E := by use! fun α g ↦ ∫ y, α.1.1 y⁻¹ • F (g * y) <;> simp [add_smul, integral_add, mul_smul, fun g ↦ (integrable_bump_inv_smul (F <| g * ·) ·), integral_smul, funext_iff]
lemma hasDerivAt_smear {γ : ℝ → USign ε} {t X} (h : HasDerivAt (γ · |>.1.1) ((γ t).1 * X) t) : HasDerivAt (smear F hF α <| γ ·) (smear F hF (bumpDeriv X α) (γ t)) t := by
  obtain ⟨⟨A, a⟩, ⟨C, c⟩, N, k, m⟩ := α.1.2, h.isBigO_sub.bound, exists_compact_mem_nhds (γ t); obtain ⟨K, n⟩ := α.2.mul k.inv, mem_of_mem_nhds m; let ⟨L, l⟩ := (contDiff_infty.1 A.2 1).locallyLipschitz.locallyLipschitzOn
    |>.exists_lipschitzOnWith_of_compact ((K.mul k).image_auto (·.1.1))
  have ⟨i, j⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip' (c.and (isClosedEmbedding_U.continuousAt_iff.2 h.continuousAt m)) (by fun_prop) (.congr ((integrable_bump_inv_smul (F <| γ t * ·) α).comp_mul_left (γ t)⁻¹) (by simp))
    (by simp [← smulRight_one_eq_toSpanSingleton]; fun_prop) (.of_forall fun y s ⟨p, q⟩ ↦ by
    rw [indicator]; split_ifs with b
    · simp [← a, ← sub_smul, norm_smul, mul_assoc, -coe_units_inv] at *
      grw [l.norm_sub_le, ← mul_sub, norm_mul_le, p, mul_comm] <;> exact ⟨_, mul_mem_mul b ‹_›, rfl⟩
    simp [fun x o ↦ image_eq_zero_of_notMem_tsupport (b ⟨y⁻¹ * x, ·, x⁻¹, o, by simp⟩), *])
    ((K.inv.integrableOn fun y ↦ ‖F y‖ * L * ‖y⁻¹.1.1‖ * C).integrable_indicator K.inv.measurableSet) (.of_forall fun y ↦ (hasDerivAt_curve α.1 (γ := (y⁻¹ * γ ·)) (X := X) (by simp [mul_assoc, h.const_mul])).smul_const (F y))
  convert ← j.hasDerivAt <;> simp [integral_apply i] <;>
    rw [← integral_mul_left_eq_self] <;> congr! 4 <;> simp
lemma rightDeriv_smear {α f} (e : smear F hF α = f.1) X : smear F hF (bumpDeriv X α) = (rightDeriv ε E X f).1 := have k Y g := (hasDerivAt_smear F α hF (hasDerivAt_expU Y g 0)).unique (e ▸ hasDerivAt_rightDeriv_expU ..); eq_unitaryLiePart_add_I_smul ε X ▸ by simp_all [funext_iff]
end
end
noncomputable section
open Matrix MeasureTheory ComplexConjugate Complex GlModule InnerProductSpace Real Norms.L2Operator Submodule Lp simpleFunc MemLp
variable {n} [Fintype n] {ε h A} {l : @HCParam n ε}
abbrev HCParam.DsModule := (rightDeriv ..).filtration 1 l.dsCoeffSmooth 0
def HCParam.dsAction := (rightDeriv ..).generatedBy l.dsCoeffSmooth
@[simps] def HCParam.dsGenerator : l.DsModule := ⟨_, self_mem_filtration⟩
attribute [local simp] integral_complex_ofReal inner_smul_right_eq_smul conj_mul' mul_assoc ne_of_gt le_of_lt div_pow
lemma isKHighest_dsGenerator (hg : l.HasGap h) : l.IsKHighest l.dsAction l.lowestKType l.dsGenerator := .of_E_eq_smul fun a b q k ↦ by
  ext g; obtain ⟨d, e⟩ := (((-l).aDC g⁻¹).comp_of_eq (aMI g.1.det_ne_zero) (by simp)).differentiableAt.hasFDerivAt, by simpa using dsCoeff_inv hg.neg
  erw [rDF d (by simpa), fBE ε d k q (g * ·) (.of_forall fun _ x m t _ ↦ by simp [*, t.2, by simpa using isAccretive_blockDiagPart_inv_mul g⁻¹, dsCoeff, flenstedJensen, ← mul_assoc, weightMinors_neg, hg.isKDominant_lowestKType.weightMinors_mul_borel hg.neg.1, ← integral_const_mul, mul_div]; ac_rfl)]
  aesop
lemma norm_dsCoeff_le_one (hg : l.HasGap h) (g : USign ε) : ‖l.dsCoeff g‖ ≤ 1 := by simpa using norm_dsCoeff_sq_mul_det_pow_le_one (c := 0) ⟨hg.1, hg.2, by simp⟩ le_rfl g
variable [Nonempty n] (hg : l.HasLargeGap A)
include hg
omit [Nonempty n] in
lemma iMT {w} (i : Integrable w) (hw : ∀ g, ∫ k, conj (weightMinors l.lowestKType k) * w (k.1⁻¹ * g) ∂haarK ε = l.lowestKType.kTypeNormSq * w g) x a : ∫ g, w g * l.dsCoeff (x * g * a :) = l.dsCoeff x * ∫ g, w g * l.dsCoeff (g * a :) :=
 by simpa [hw, mul_left_comm (w _), by simpa using fun g ↦ integral_conj_weightMinors_mul_dsCoeff hg x (g * a) hg.isKDominant_lowestKType] using (_root_.integral_conv (k := (conj <| weightMinors l.lowestKType ·)) (ν := haarK ε) (↑) integrable_of_compactSpace i (.of ⟨_, (norm_dsCoeff_le_one hg <| x * · * a)⟩)).symm.elim (·.symm.trans)
lemma exists_smear_dsCoeffSmooth_eq (f : l.DsModule) : ∃ β, (smear l.dsCoeffSmooth.1) β = f := by
  let b : @ContDiffBump (Matrix n n ℂ) 0 := default; have ⟨P, e⟩ := l.dsCoeffSmooth.2
  let β : Bumps ε := ⟨⟨_, ⟨_, (ofRealCLM.contDiff.comp ((b.contDiff.comp (contDiff_id.mul (starL' ℝ).contDiff)).pow 2)).mul P.2⟩, congr(_ * $e)⟩, .intro (isCompact_U_norm_le √b.rOut) (by
    simp +contextual [b.zero_of_le_dist, CStarRing.norm_self_mul_star, sqrt_lt', sq])⟩
  refine mem_sInf.1 f.2 ((smear ..).range.submoduleOf _) ⟨(smul_mem_iff_of_isUnit _ ?_).1 ⟨β, funext (by simpa [mul_comm (dsCoeff ..)] using! iMT hg (integrable_bump_inv_smul 1 β) (by simp [β, star, mul_left_comm, ← maxCompactU.coe_inv, by simpa using integral_conj_weightMinors_mul_dsCoeff hg ·⁻¹ 1 hg.isKDominant_lowestKType]) · 1)⟩, fun _ _ _ _ ⟨_, e⟩ ↦ ⟨_, rightDeriv_smear _ _ e _⟩⟩
  simpa [β, ↓dsCoeff_inv, ← ofReal_pow, ← ofReal_mul] using (integral_pos_of_integrable_nonneg_nonzero (x := 1) (by clear_value β; fun_prop) (integrable_bump_inv_smul (l.dsCoeff ·) β).norm.abs (abs_nonneg _) (by simp [β, b, ContDiffBump.one_of_mem_closedBall, default])).ne'
namespace HCParam.HasLargeGap
lemma eDB (f : l.DsModule) (c : ℕ) (hc : c ≤ gapThreshold n A) : ∃ K, ∀ g, ‖f.1.1 g‖ ≤ K * (2 / ‖g.1.1‖) ^ c := (exists_smear_dsCoeffSmooth_eq hg f).elim fun α e ↦ e ▸ ⟨_, fun g ↦ .trans_eq (norm_integral_le_of_norm_le ((integrable_bump_inv_smul (E := ℂ) (‖·.1.1‖ ^ c) α).norm.mul_const _) (.of_forall (by grw [norm_smul, dsCoeffSmooth, norm_dsCoeff_le_pow hg hc]; simp [field]; grw [mul_assoc, ← mul_pow, ← U.norm_inv ·, ← norm_mul_le]; simp))) (integral_mul_const ..)⟩
lemma integrable_norm_pow_smul (f : l.DsModule) (C := A) (h : (C : ℝ) ≤ A + 1 := by grind) : Integrable fun g ↦ f.1.1 g * ‖g.1.1‖ ^ C := (hg.eDB f (C + (8 * Fintype.card n ^ 2).succ) (by simp; nlinarith [one_le_cast_card n])).elim fun K k ↦ ((integral_decay_le _ .monoidHom_id .refl 1).1.const_mul (K * 2 ^ C)).mono' (by fun_prop) (.of_forall (by grw [norm_mul, k ·, pow_add]; simp [field]))
lemma memLp (f : l.DsModule) : MemLp f.1.1 2 := (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 (by simpa [sq] using (hg.integrable_norm_pow_smul f 0).norm.mul_bdd (by fun_prop) (.of_forall (by simpa using (hg.eDB f 0 (by simp; bound)).choose_spec)))
@[simp] lemma _root_.formalDegree_pos : 0 < l.formalDegree := inv_pos.2 (integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop) (hg.memLp l.dsGenerator).norm.integrable_sq (by aesop_cat) (by simp))
lemma integrable_norm_pow_smul_dsKernel (C := A) (h : (C : ℝ) ≤ A + 1 := by grind) : Integrable fun g ↦ l.dsKernel g * ‖g.1.1‖ ^ C := by simpa [dsKernel] using (integrable_norm_pow_smul hg.neg dsGenerator C).const_mul _
lemma _root_.dsCoeff_schur_orthogonality (x a : USign ε) : l.formalDegree * ∫ y, l.dsCoeff (x * y * a :) * conj (l.dsCoeff y) = l.dsCoeff x * l.dsCoeff a := by
  have k := iMT hg (hg.integrable_norm_pow_smul l.dsGenerator 0).comp_inv
    (by simpa using integral_conj_weightMinors_mul_dsCoeff hg ·⁻¹ 1 hg.isKDominant_lowestKType)
  rcases (integral_div_left_eq_self _ _ a⁻¹).trans (k a 1), formalDegree_pos hg
  simp_all [by simpa using dsCoeff_inv hg, mul_div, mul_comm _ (conj _), formalDegree, ← ofReal_pow,
    field]
def toL2 := √l.formalDegree • IsLinearMap.mk' (R := ℂ) (hg.memLp · |>.toLp) ⟨by tauto, by tauto⟩
lemma toL2_spec : IsDerivedAction rightRegularL2 hg.toL2 l.dsAction ∧ (∀ y g, ⟪hg.toL2 l.dsGenerator, rightRegularL2 g (hg.toL2 y)⟫_ℂ = y.1.1 g) ∧ ∀ y z x, ⟪hg.toL2 y, rightRegularL2 x (hg.toL2 z)⟫_ℂ = l.formalDegree * ∫ g, z.1.1 (g * x) * conj (y.1.1 g) := by
  have i w h z k (x : USign ε) : ⟪toLp w h, rightRegularL2 x (toLp z k)⟫_ℂ = _ := integral_congr_ae (h.coeFn_toLp.comp₂ _ (AEEqFun.coeFn_mk ..)); have c := iUR.1 (hg.toL2 l.dsGenerator); choose β e using exists_smear_dsCoeffSmooth_eq hg
  have B {y β} (e : (smear l.dsCoeffSmooth.1) β = y.1) g : rightRegularL2 g (hg.toL2 y) = smear _ c β g := (simpleFunc.denseRange (by simp)).eq_of_inner_right ℂ fun w ↦ toLp_toSimpleFunc w ▸ .trans (by simpa [toL2, i, -map_mul, ← e, mul_left_comm, mul_comm] using (_root_.integral_conv (· * g) (((SimpleFunc.memLp_iff_integrable two_ne_zero nofun).1 (simpleFunc.memLp w)).inner_const 1) (integrable_bump_inv_smul 1 β) (.of ⟨_, norm_dsCoeff_le_one hg⟩)).1) (integral_inner (integrable_bump_inv_smul ..) _)
  suffices _ from ⟨fun Y v ↦ ?_, fun y g ↦ ?_, this⟩; erw [B (e y), ← integral_inner (integrable_bump_inv_smul ..)]; simp [*, ← e, -map_mul, by simpa using (dsCoeff_schur_orthogonality hg 1 <| g * ·)]; simp [toL2, inner_smul_left_eq_smul, i, smul_smul, ← real_smul]; simpa [B (e v), ↓← @B (l.dsAction Y v) _ (rightDeriv_smear _ _ (e v) _)] using hasDerivAt_smear _ (β v) c (hasDerivAt_expU Y 1 0)
variable [hg]
instance : NormedAddCommGroup l.DsModule := .induced _ _ hg.toL2 fun _ ↦ by grind +extAll [hg.toL2_spec]
instance : InnerProductSpace ℂ l.DsModule := induced hg.toL2
variable (hg)
lemma isUnitaryCasimirGe_dsAction : IsUnitaryCasimirGe l l.dsAction ∧ ‖l.dsGenerator‖ = 1 ∧ ∀ (y : l.DsModule) g, ‖y.1.1 g‖ ≤ ‖y‖ := by have ⟨d, k, _⟩ := hg.toL2_spec; have u := (by simpa using congr(√‖$(k l.dsGenerator 1)‖)); use ⟨d.form_E_eq_sign_mul iUR, by simp [dsAction, casimirK_generatedBy casimir_dsCoeffSmooth, sq]⟩, u, (k · · ▸ by grw [norm_inner_le_norm, u]; simp [rightRegularL2]; rfl)
