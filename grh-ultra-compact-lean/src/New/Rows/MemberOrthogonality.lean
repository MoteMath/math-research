import New.Rows.GluedFormTheta
import New.Seesaw.BesselGeneric
import New.Selmer.RankOneDenominator
import New.Exchange.RowLadder
import Lib.Shimura.ComplexTheta.PeriodVanishing
section
open Nat Fint Fintype Function PolyRep Ideal LValueData Matrix MvPolynomial AuxPair LevelPlaces Real
lemma Data.Pair.g9 {P} {D} {p : @Pair P D} {n} [Fintype n] (H :
  p.IsFlat n) (σ : ℂ ≃+* ℂ) : ‖σ (intAlgPart H.2 .one)‖ ≤ exp (D.x ^ 34) := by
  let X := trivialLift H.2 .one
  have k σ : X.normSqAt σ ≤ _ := classSum_le_card_mul_sq fun _ ↦ by grw (transparency := default) [trivialLift_apply, sqrt_weylNormSq_sum_le, (P.norm_jet_le_of_isAdmissibleComb (hb := b_hasWeight _)
    (P.isAdmissibleComb_vacuumDatum 1 (by grind [levelIndicator, norm_one, norm_zero])) ..).2 1 (LValueData.isLiftWeight _), Fintype.card_fun, card_levelModulus_resRing, prod_q_chosenPlace,
    prod_eq_one _ nofun, (by aesop : AuxPair.κ _ = 0), (congrArg _ (by simp [_root_.funext_iff, weylEval, nablaBasis_eq_one])).trans (weylNormSq_weylEval_permArray (rowPos _))]
  have := X.norm_map_inner_le X
  simp [intAlgPart, twist_one_spec, diagramWeight, ← card_eq_fintype_card, Nat.card_pi] at *
  grw [this, k, k, mul_self_sqrt (by bound), D.card_stdClasses_le_exp (D.principalLevel_le_chosenLevel ⟨_, rfl⟩), prod_eq_one _ nofun, D.card_stdClasses_le_exp (principalLevel_le_levelOf (·.rec (mul_mem_right _ _ ·.2.2.1) nofun)) (H.2.1 ▸ D.nat_le_of_hasLogBound), ← le_exp_of_log_le]
  simpa [denomBound, H, log_mul, NeZero.ne] using D.le_of_hasLogBound
lemma Data.v5 {P} {D : Data P} ϑ s z g : (ι ϑ (D.goodProjTranslate s
  z).1).1 g = ∑ t, (Nat.card D.G * D.e₀.coeff t) • (ι ϑ z).1 (g * d1 ϑ (t * s)) := by
  simp [asAlgebraHom_eq_sum, ← Module.End.mul_apply, ← map_mul, c8, Finset.smul_sum, mul_smul]
lemma Data.goodProjTranslate_mem_integralForms {P} {D : Data P} {l} [Fact l.Prime] (j : PadicPlace l) {ϑ} {a : ℂ} {z} (h : a • iotaAtLevel ϑ z ∈ LevelForm.integralForms j) s :
  a • iotaAtLevel ϑ (D.goodProjTranslate s z).1 ∈ LevelForm.integralForms j := fun _ ↦ by
  erw [weylGauge_smul, v5, ← weylGauge_smul, Finset.smul_sum]; apply weylGauge_sum_le <;> intros; simp
  grw [smul_comm, weylGauge_smul, norm_le_one_of_isIntegral, one_mul, ← weylGauge_mul]
  exacts [h _, Kf_le_localLevel (d1 ..).2, norm_nonneg _, D.isCentralProj_e₀.isChar.isIntegral _]
lemma Data.normSqAt_goodProjTranslate_le {P} {D : Data P} {σ : ℂ ≃+* ℂ} {z s B} (h : ∀ g, weylNormSq (σ ∘ (D.ι .one z).1 g)
  ≤ exp B) : (D.iotaAtLevel .one (D.goodProjTranslate s z).1).normSqAt σ ≤ exp (D.x ^ 99 + B) := by
  have k s := by simpa [apply_ite, inv_mul_eq_one] using (Finset.single_le_sum (by simp)
    (Finset.mem_univ s)).trans ((D.isCentralProj_e₀.map σ).sum_norm_conv_le (.id _) (Pi.single 1 (1 : ℂ)))
  grw [LevelForm.normSqAt, classSum_le_card_mul_sq fun g ↦ by
    erw [v5]; grw [sqrt_weylNormSq_sum_le]; simp [-Fintype.card_pi]; grw [h, k], D.card_stdClasses_le_exp (principalLevel_le_levelOf (·.rec (mul_mem_right _ _ ·.2.2.1) nofun)) (D.card_Y_le .refl)]
  simp [exp_add, ← card_eq_fintype_card, field, exp_nonneg]
  grw [Nat.le_of_dvd Fin.pos' (D.card_GL_dvd_chosenGroupOrder D.nat_le_of_hasLogBound), le_exp_log D.chosenGroupOrder]; use D.le_of_hasLogBound D.lt_of_hasLogBound
attribute [-simp] map_nablaBasis
attribute [local simp↓] Finsupp.prod_mapDomain_index_inj Injective.eq_1 coeff_map rename_monomial fockPairing_monomial fockPairing_rowSubst diagramWeight mem_nabla mul_pow pow_add borelMul
lemma s22_k9 {P} {D : Data P} {n} [Fintype n] (X : LValueData D.E n) {r} (e : Fin r ↪ n) {α : _ →₀ ℕ} (hα : ∀ τ, ∑ i, α (τ, i, ()) = X.jetDeg τ) :
  ∃ v : _ → ℤ, X.auxPair.harmonicPoly (star ((↑) ∘ v)) = ((∏ τ, (X.jetDeg τ)!) / α.prod fun _ k ↦ (k ! : ℂ)) • renameRowsCols e id (monomial α 1) ∧ ∀ {R} [Field R] [CharZero R]
  {g : _ → GL n R} {w}, w = (↑) ∘ v → (∀ i a b, (g i).1 b (e a) = ite (b = e a) 1 0) → weylRep _ X.auxPair.detExp g *ᵥ w = w := ⟨fun k ↦ (nablaBasis ℤ _ _ k).coeff ?δ, rename_injective _ (by simp) ((X.toPoly_eq_rename_harmonicPoly _).symm.trans ((range_toPoly.ge
  (by simp [aeval_monomial, X.one_lt_card, mixedWeight, ← hα, ← Finsupp.prod_finsetSum_index, prod_prod_type, ← Finset.prod_pow_eq_pow_sum]; intros; ring)).elim fun ξ m ↦ .trans (congrArg _
  (funext (by simpa [m, field, ← map_nablaBasis (algebraMap ℤ ℂ), X.hookNumber_eq_prod_factorial,
  Finset.prod_eq_zero_iff] using fockPairing_toPoly_nablaBasis ξ))) m)), fun {R _ _ g w} k h ↦ by
  simpa [k, funext_iff, ↓← sum_schur_smul_nablaBasis, weylRep, coeff_sum, mulVec_eq_sum, ← map_nablaBasis (algebraMap ℤ R)]
    using congr(fockPairing R $(show IsFixedPt (rowSubst (g · |>.1.transpose)) (monomial ?δ 1) by
    simp [IsFixedPt, rowSubst, h, monomial_eq]) ∘ nablaBasis R _ _)⟩
end
seal Finset.univ Finset.sum Finset.prod
open AutChar ComplexConjugate Fintype G Gf MatMul Matrix MeasureTheory AuxPair Prod Space Sum ThetaKernel
variable {E r n N a l} [Field E] [CMType E] [Fintype r] [Fintype n] [Fintype N] [Fintype l] [WeilData E] {O : AuxPair E r n} {z} (V : DividedSplitting N l a O z) {l₀} [Nonempty r] (hO : O.FitsParams l₀) (hQ : ∀ i, O.ψ (O.twistPlace i) ≠ 1) {Ξ} (hM : ∀ (i) (v : (x : O.ChosenIndex) → _), v i ≠ 0 → (O.formAction.asAlgebraHom (piTensorElem fun i ↦ reflectionSum (O.ψ _) (v i))) Ξ = 0) (h0 : O.θ Ξ = 0) {w} {hw : _ ≠ w} {hS} (hH : O.heckePolyOnForms hw hS (O.testValue w) Ξ = 0) (hn : 2 * card r + 2 * card N + 3 < card n)
include hO hQ hM h0 hH hn
set_option backward.isDefEq.respectTransparency false
lemma s22_j2 (ε : N ⊕ l ≃ n) {κ Y e'} hY (C : _ →ₗ⋆[ℂ] _) (hC : ∀ (g y : GInf E 1) ζ, (∀ τ, (g τ).1 = reindexGL ε (blockGL (1, y τ))) → conjWeylRep _ O.detExp g (C ζ) = C (conjWeylRep κ 0 y ζ)) {b 𝔪} (h𝔪 : 𝔪.places ⊆ O.places) {Ψ g h₁ x} (hx : x ∈ supportedOn n (.range O.chosenPlace)) {K} [ho : IsLevel K] {f} (hf : ∀ h, f h = inner ℂ (pointForm (Y := Y) (U.block ε (h₁, h) * x) hY e' (C (kernelVector O b 𝔪 Ψ κ g h))) Ξ) {u}
  (he : ⇑e' = ε ∘ inl ∘ u) (hk : ∀ k, k.1 ∈ K → (∀ T, Ψ ((𝔪.reductionK₀ k⁻¹).1 * T) = Ψ T) ∧ ∃ m, ∀ i, (Kf.reduceAt _ ⟨x⁻¹ * U.block ε (1, k) * x, m⟩).1 * Y i = Y i) : stdClassSum K f = 0 := by
  have dv u : DescentsVanish (hypSum N O.W) (stdSpace E n) (O.a * WeilData.upsilonU1 ^ card N) O.places.conjClosureᶜ (star (algFormCoeff 1 (gramForm u) Ξ.1)) := by
    have p := pairWeil_integrated O.W (stdSpace E n) O.a O.b
    simp [theta_eq_smul_star_lift_swap, -card_pi] at h0
    refine' descentsVanish_add_planes (descentsVanish_of_reflectionSum _ hQ hM fun P ↦ funext fun g ↦ highestVector_cyclic (O.isHCParam_paramV · |>.1) O.detExp (.proj g ∘ₗ liftBilin _ _ ∘ₗ ⟨⟨fun u ↦ ⟨_, (isAutomorphic_star_algFormCoeff (gramForm u) Ξ).mem_rapidFunctions⟩, _⟩, _⟩) u
      (.inr fun x ↦ _)) (removePlanes ..) _ hw _ (by grind [star_star]) (by simp [funext_iff, ← algFormCoeff_algFormRep, ↓mem_levelSpace.1 (Ξ.mem_sphericalAt hS)]) _
      ((map_heckePolyOp ((starLinearEquiv ℂ).1 ∘ₛₗ _) _ (by simp [funext_iff, algFormCoeff_algFormRep])).symm.trans ((congrArg _ congr(($hH).1)).trans (map_zero _))) hn
    any_goals simp [↓isAutomorphic_star_algFormCoeff, algFormCoeff, funext_iff, ↓HasWeight.charUnramifiedAt, testValue, frobValue]
    simpa [algFormCoeff_apply, ← gramForm_conjWeylRep (e := O.detExp) x (highestVector _ _), liftBilin, pairWeil_apply, realConv, lift, mul_left_comm _ _⁻¹, mul_assoc] using
      congrFun (((pairThetaKer ..).swap.lift_omega_left (isAutomorphic_star_algFormCoeff _ Ξ) (x⁻¹, 1)).symm.trans (congr(lift _ $(p ..) _).trans (((hO.isEdge.2.lift_isForm_and_eq_realConv _
      (by simp [realPairWeil_polyVector, negCount])).choose_spec _ (by simp [p]) (isForm_ofAlgForm O.isHCParam_paramV Ξ.1).conj).2.trans (congrArg _ h0)))) g
  obtain ⟨o, s, t⟩ := (s22_w1 hY e').choose_spec
  simp_rw [s22_d4] at hf; set A := Exists.choose _
  let D : _ →* G E 1 := blockEmb (e := ε) elim_one_one.symm
  have ⟨y, z⟩ := not_forall.1 (eq_zero_of_realVec (f := pairWeil O.W (stdSpace ..) O.a b⁻¹ (g, 1, h₁) (vacElem _)).mt fun e ↦ by simpa using congr(dataInner _ $e $e))
  rw [← θ_ϱ, varrho_pairWeil, ← pairTheta] at z
  set v := (O.W.hom (stdSpace E N)).ϱ _ _
  let φ j := (O.W.hom (stdSpace ..)).boxProd (homSigns_sum_target (e := ε) (by simp)) v (modDatum O.W (stdSpace ..) 𝔪 Ψ (polyVector _ (fockLetters O.signs O.ord (-1) (nablaBasis ℂ _ κ j))))
  have hφ j : projOn _ O.places.conjClosureᶜ (φ j) = φ j := by erw [← boxProd_projOn,
    projOn_ϱ _ (by simp [matToVec, vecToMat, realVec, mul_apply, snd_sum]), projOn_vacElem,
    projOn_integrated, projOn_name_vacElem _ (by clear * - h𝔪; grind)]; rfl
  let L j := gramForm (C (Pi.single j 1))
  have Y j := (isAutomorphic_star_algFormCoeff (L j) Ξ).comp_mul_right (1, x * A)
  let F h := ∑ j, pairTheta _ _ O.a 1 (φ j) (g, h) * star (algFormCoeff 1 (L j) Ξ.1) (h * (1, x * A))
  obtain ⟨this, o⟩ := (Y · |>.1), mul_mem (supportedOn_mono (by simp) hx) o
  have hΓ γ m h : F (γ * h) =
    F h := congr(∑ j, $((pairThetaKer ..).swap.theta_rat_mul _ m h) * $((Y j).2 _ m h))
  have e y h : F (D (h₁, y, h)) = pairTheta _ _ O.a b⁻¹ v (g, h₁) * conj (f h) := by
    simp (disch := simp [blockEmb]) only [F, φ, pairTheta, D, ← inv_mul_cancel b, theta_boxProd_target, mul_assoc, modDatum, pairWeil_boxProd_target (g₁ := (1, h₁)) (g₂ := (y, h)) .., ← Finset.mul_sum, ← rep_apply_apply, pairWeil_integrated_right, (by simp : (g, y, h) = (g, ↑h) * (1, y, 1)), realPairWeil_fockLetters]
    erw [hf, ← gramForm_conjWeylRep (D (1, y, h)).1⁻¹, hC _ y⁻¹ _ (by tauto), pi_eq_sum_univ' (conjWeylRep κ _ _ _), toLin'_apply, ← star_inj]
    simp [algFormCoeff_apply, mul_assoc, weylRep, schur_map, -map_inv]; tauto
  have := (period_eq_zero (by fun_prop) hΓ (fun c m h ↦ sum_congr _ _ fun j ↦ by erw [← mul_one g, ← mk_mul_mk, pairTheta_mul, pairWeil_eq_smul_of_projOn_eq _ (hφ j)] <;> simp [↓m, upsilonU1_det_of_mem_Kf m.1, mul_assoc h, ← (commute_supportedOn_trivialOn o (supportedOn_compl.le m.2)).eq, ← algFormCoeff_algFormRep, Ξ.algFormRep_eq_self_of_mem
    (inf_trivialOn_le_levelOf ⟨m.1, supportedOn_compl.le m.2⟩)]) ε (by simp) (fun ψ hψ ↦ funext
    fun a ↦ .trans (by simp [hypSum, lift, F, theta_boxProd_source, pairTheta, Finset.mul_sum, mul_comm O.a, pairWeil_boxProd_source, mul_assoc, -θ_apply]) ((integral_finsetSum _ fun j _ ↦ integrable_theta_mul _ (Y j).mem_rapidFunctions ..).trans (sum_eq_zero _ fun j ↦ congrFun ((lift_omega_left _ (isAutomorphic_star_algFormCoeff _ Ξ) (1, x * A)⁻¹).symm.trans (dv _ _ (projOn_pairWeil ((boxProd_projOn ..).symm.trans congr(boxProd homSigns_sum_source $hψ $(hφ j))) _ fun w m ↦
    onHom_atPlace_mem (by simp) ((not_or.1 m).elim (mem_supportedOn.1 (inv_mem o) w) ▸ one_mem _))))
    (.sum (a, g))))) h₁).symm.trans (integral_quotMeasure_eq_classSum (fun γ _ h ↦ .trans (by
    simp [D, ← map_mul]) (hΓ (D (1, γ)) (by simpa [D]) _)) (by simp [e, D]; tauto) K fun k q h ↦ ?_)
  simpa [z, ← mul_classSum, ← map_classSum]
  lift k to Kf E l using ho.1 q; obtain ⟨p, m, a⟩ := hk k q
  have := congr($(O.smul_chosenGLRep_eq Ξ 1 (k := A⁻¹ * ⟨_, m⟩ * A) rfl ?_).1 (U.block ε (h₁, h) * x * A))
  simp [← mul_assoc, ← Pi.one_def, ← (U.block ε).map_mul] at this p
  simp +unfoldPartialApp [kernelVector, modKernel_mul_Kf_right, *]
  simp [*, Kf.reduceFamily, ← t, transpose_nonsing_inv, -elim_inl, -elim_inr, inv_mul_eq_iff_eq_mul_of_invertible, Matrix.mul_right_inj_of_invertible]; intro
  erw [((MonoidHom.eq_iff _).2 (Kf.reduceAt_eq_one_of_atPlace (w := O.twistPlace _) (by simp [atPlace_twistPlace_eq_one hx]))).trans (map_block_eq_blockGL _ ε 1 k).2, mul_inclMatrix]; simp [← ext_iff, reindex_equiv ε, inclMatrix, @eq_comm N]
lemma DividedSplitting.stdClassSum_inner_productForm_eq_zero {ϖ} [Fact (ϖ ≠ 0)] (t : O.chosenModulusSq.ideal = .span {ϖ}) L x y b Ψ g : stdClassSum (principalLevel l ϖ) (fun h ↦ inner ℂ (V.productForm L (x, h) y (star (kernelVector O b O.chosenModulusSq Ψ _ g h))) Ξ) = 0 := s22_j2 hO hQ hM h0 hH hn V.ε (fun _ ↦ inclMatrix_mulVecLin_injective ..) (𝔪 := O.chosenModulusSq) (cartanProduct V.ε 1 y ∘ₛₗ (starLinearEquiv ℂ).1) (fun g u ζ h ↦ by
    simp [conjWeylRep, weylRep_cartanProduct, V.low, HasColumnsBelow]
    simp [cartanProduct, weylRep, star_mulVec, ← mulVec_transpose, conjTranspose_transpose, V.low.2.schur_mul_schur, ← map_inv, by simpa using (U.form_mul_inv_eq <| g ·)]
    congr! 6 <;> simp [h, entrywise, reindex_equiv V.ε]) (by simp [places_levelModulus_false])
  L.mem_supportedOn (by tauto) rfl fun k
  q ↦ have ⟨m, s⟩ := map_block_eq_blockGL O.chosenModulusSq.reduction V.ε 1 k; by
    simp_all [Modulus.mem_principalLevel_iff t, Modulus.reductionK₀]; peel L.reduceAt_conj_eq_one _ s; simp [*]
