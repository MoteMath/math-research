import Lib.Weil.MixedModel.EquivariantCoefficients
import Lib.Weil.DualPair.ThetaIntegralLaws
noncomputable section
variable {E n n' r r' b s s' t t'} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n'] [Fintype r] [Fintype r'] {W : Space E n s} {W' : Space E n' s'} {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit)
section
open Matrix WeilData MeasureTheory SemilocalField Space Splitting Fintype MatMul
variable [Fintype b] (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n)
attribute [local simp] stdColDatum stdForm adaptedFrame mulVec dotProduct iCoord sum_prod_type vecToMat matToVec mul_assoc Matrix.mul_apply
lemma exLTLD X [IsBaseAdapted A] [IsBaseAdapted X] : ∃ l : _ → ℂˣ, ∀ {F} [SemilocalField F] {S π} {χ : MulChar F _} (r : ReadsAt S π) (h : TameLocalChar χ), ∃ γ, ‖γ‖ ^ 2 = (Nat.card h.ResidueRing : ℝ)⁻¹ ∧ ∀ s β v x, let a := x * (scaleIdele E)⁻¹.1; lineTerm A X β x (localDatum _ V' v (stdRowDatum σ' χ (s * (adaptedFrame r A).I')) r) = (l β * γ * ite (idem S.conjClosureᶜ * a.2 ∈ Ô E) (invOnUnits χ (π a.2) / invOnUnits χ (π (star a.2) * ϖ.1)) 0) • localDatum W V (lineTermReal A X β a.1 v) (stdRowDatum σ χ s) r := by
  choose e d l using (tsum_lineTerm A X · |>.2.choose_spec.choose_spec); use (vacuumFactor <| d ·); introv; let Q := adaptedFrame r X; let H (K L : type_of% Q.K) I := ((fromRows 0 K).fromCols (((fromBlocks 1 0 0 I).submatrix id σ.symm).fromCols (fromRows 0 L))).submatrix σ'.symm id; let G := H Q.K Q.L Q.I; have j := (adaptedFrame r A).spec; extract_lets P R at j
  obtain ⟨⟨j, j', p, q⟩, ⟨γ, _, Γ⟩, u, H', u', _⟩ := j, exists_local_gauss_sum h
    r.hasIntegralConductor_psi, (by use ?_, (H Q.K'ᵀ Q.L'ᵀ Q.I'ᵀ)ᵀ <;> simp [← ext_iff, G, H, eq_comm, ite_mem, IsIntMatrix, reindex_equiv σ, reindex_equiv σ', by simpa [← ext_iff, IsIntMatrix] using Q.blocks_spec] : IsPrimitiveMatrix O G)
  let ε := invOnUnits χ (R * G).det
  have K (T : type_of% (R * G)) : stdColDatum χ 1 (G * T * R) = ε * stdColDatum χ 1 T := by
    simpa [← det_comm' q p, ← Matrix.mul_assoc] using if_ctx_congr
      ⟨(by simpa [← H'.mul_assoc, *] using u'.mul <| ·.mul j), (u.mul · |>.mul j')⟩ (invOnUnits_mul (j'.mul u).det_mem ·.det_mem) (by simp)
  use ε * γ, by simpa [ε, invOnUnits, h.norm_eq_one, isPrimitiveMatrix_iff_isIntegralUnit_det.1 ((IsPrimitiveMatrix.mul_iff ⟨j', _, j, p⟩).2 ⟨u, by tauto⟩)]
  introv a
  rw [lineTermReal, e, (by simp [funext_iff, a, Units.smul_def, mul_comm x] : _ ⊕ᵥ _ =
    scaleIdele E • (a * ·.isRight.toNat)), mixedTerm_localDatum r (d β) (stdRowDatum_mem _ _) _ _ (1 ⊕ᵥ fun _ ↦ ε • invOnUnits χ (π a.2) • invOnUnits χ) fun y z ↦ let Y := (s.fromRows y).submatrix σ.symm id; ((congrArg _ ?_).trans (K (fromBlocks (cond β (π a.2) (z (.inr 0)) • 1) (vecToMat (z ∘ .inl ∘ .inl)) 0 (Y.fromBlocks ((fromRows 0 (vecToMat (z ∘ .inl ∘ .inr))).submatrix σ.symm id) 0 (cond β (z (.inr 0)) (π a.2) • 1))))).trans ?_]
  simp [volume_O, Measure.real, Γ, mul_comm (r.ψ _)]; ring_nf; rfl; simp +zetaDelta [↓l]; cases β <;> congr with ⟨⟩ <;> simp [Finset.mul_sum, diagonal, mul_add] <;> ac_nf
  have q (h : IsIntMatrix O Y) := h.det_mem; simp [Y, stdRowDatum, IsIntMatrix, reindex_equiv σ, Unique.forall_iff, prod_ite_zero, prod_prod_type, -ite_smul] at q ⊢; grind [invOnUnits_mul, mul_mem, invOnUnits]
end
section
seal Finset.univ Finset.sum Finset.prod
open Matrix MeasureTheory Measure Units MulAction Space Splitting Submodule Pointwise Function Equiv WeilData
variable (X : V'.Splitting V Unit) (a b : AutChar E)
abbrev radicalMeasure := (ratMatrices E n Unit).qms.prod (ratMatrices E Unit Unit).qms
def constTermAt x f := if xᴴ * V.J * x = 0 then ⨍ y, A.thetaTerm V 1 1 f (lineRadical A (y, 0)) x 1 ∂(ratMatrices ..).qms else 0
attribute [-instance] locallyCompact_of_proper DiscreteUniformity.instDiscreteTopology
attribute [local simp] Splitting.thetaTerm sourceTerm_radicalElt star_eq_conjTranspose lineLevi radicalElt_mul_kAdelic radicalElt_inv
lemma ctInt x f : constTermAt A x f = ∫ q, A.thetaTerm V a b f (lineRadical A q) x 1 ∂radicalMeasure := by erw [constTermAt, ← mul_boole, ← isDualFamily_ratMatrices.quotMean_eq_ite, ← average_quotMeasure_eq_quotMean _ volume (isDualFamily_ratMatrices.1 _), ← integral_prod_mul]; simp [↓gram_at_point_eq_map, ← mul_assoc, ← map_mul, -coe_units_inv]; simp [trace, entrywise, mul_comm]
lemma hsCT {f} : HasSum (fun x ↦ constTermAt A (replicateCol _ x) f) (∫ q, pairTheta _ V a b f (lineRadical A q, 1) ∂radicalMeasure) := by simp_rw [ctInt A a b, Splitting.thetaTerm]; exact (piCongrRight fun _ ↦ funUnique ..).hasSum_iff.1 (hasSum_integral_of_dominated_convergence _ (by fun_prop) (by simpa [↓sourceTerm_radicalElt, ↓sourceTerm_eq_mixedTerm] using fun _ ↦ .of_forall fun _ ↦ norm_apply_le ..) (.of_forall fun _ ↦ ((summable_norm_mixedTerm ..).mul_left _).comp_injective uncurry_injective) (by simp) (.of_forall fun _ ↦ hasSum_theta_sourceTerm ..))
lemma constTermAt_zero f : constTermAt A 0 f = θ _ (A.sourceTerm V 0 f) := by simp [constTermAt]
open MatMul
lemma constTermAt_smul_k {ξ} (h : ξ ≠ 0) {f} : constTermAt A (ξ • X.k) f = θ _ (lineTerm A X true (toAdele ξ) f) := by
  let φ : Matrix n Unit (𝔸 E) →+ _ := .mk' (toAdele ξ • matToVec ·ᴴ) (by simp); have h₀ y : y ∈ ratMatrices .. → φ y ∈ _root_.ratVectors .. := .imp' (ξ • matToVec ·ᴴ) (by aesop); erw [Splitting.zeroTerm_apply, ← quotMean_comp _ φ (isContPeriodic_along_k ..) h₀ (⟨conjTranspose <| toAdele ξ⁻¹ • vecToMat ·, _⟩) _, ← average_quotMeasure_eq_quotMean _ volume ⟨_, by grind -ring -linarith [(isContPeriodic_along_k ..).2]⟩, constTermAt] <;>
  simp [X.k.map_smulₛₗ _ toAdele, φ, kAdelic, ↓homTarget_kAdelic, smul_smul, ← map_mul, h, kronecker_mulVec_eq_matToVec, dualFrame, -transpose_mul] <;> fun_prop [matToVec]
lemma integral_thetaIntegral_lineRadical {f} (h : IsTargetBounded _ V f) g : ∫ q, thetaIntegral _ V a b f (lineRadical A q * g) ∂radicalMeasure = ∫ h, ∑' x, constTermAt A (replicateCol _ x) (pairWeil _ V a b (g, h) f) ∂V.quotMeasure := h.elim fun _ ⟨_, h⟩ ↦ by
  choose _ k _ _ o e using exCpRE A
  simpa [(hsCT A a b).tsum_eq, ← pairTheta_mul] using! integral_integral_swap
    (.of_bound (by fun_prop) _ (.of_forall fun _ ↦ (h ..).trans ((exists_mul_height_pow_le (k.image_auto (· * g)) _).choose_spec _ _ (o ..) ⟨_, e .., mul_assoc ..⟩)))
lemma exUnfCT : ∃ c ≠ (0 : ℝ), ∀ a b f g, let F h := pairWeil _ V' a b (g, h) f
  let T β ξ (p : _ × maxCompact E t') := θ _ (lineTerm A X β ξ (F (lineLevi X p.1 * p.2)))
  let Θ p := (ideleAbs p.1.1 ^ (Fintype.card r + 1) : ℝ) * ∑' ξ : Eˣ, T true ↑ξ p
  let ν := (((pAU E).qms haar).prod V.quotMeasure).prod haar
  (∀ h, constTermAt A 0 (F h) = 0) → Integrable Θ ν → ∫ h, ∑' x, constTermAt A (replicateCol _ x) (F h) ∂V'.quotMeasure = c * integral ν Θ := by
  have m : ∀ g, (g ∈ V'.Γ ∧ ∃ ξ : Eˣ, X.ActsOnFrame g (scalar _ ↑ξ)) ↔ g ∈ (stabilizer _ (E ∙ X.k.col ())).map
    V'.ratEmbed := by simpa [Units.smul_def, -Prod.forall, ← ext_iff, smul_span, funext_iff, ← ratEmbed_mulVec_vecAtPoint, -Subtype.exists, comm.trans span_singleton_eq_span_singleton, Unique.forall_iff, mul_comm (toAdele _), ← comm.trans V'.vecAtPoint_injective.eq_iff, Subgroup.smul_def] using! Set.ext_iff.1 Set.image_preimage_eq_range_inter.symm
  let P b : selfAdjoint (Matrix Unit Unit (𝔸 E)) := ⟨_, .add_star_self (toAdele (2⁻¹ : E) • b)⟩
  let η (p : _ × selfAdjoint _) := X.radicalElt p.1 p.2.1
  have ρ c b : X.radicalElt c b ∈ Set.range η := ⟨(c, P b), G.ext_mat (by simp [η, P, radicalElt]; match_scalars <;> grind)⟩
  obtain ⟨_, h, _, κ, K⟩ := Surjective.countable (inferInstance : IsNoetherian E (r' → E)).1, LeftInverse.isClosedEmbedding (f := fun g ↦ (-X.iCoord * g.mat * X.lAdelic, P (-toAdele (j : E) • X.kCoord * g.mat * X.lAdelic))) (g := η) (by rintro ⟨_, _, b⟩; simp [η, P, radicalElt, IsHermitian.eq b]; match_scalars
    <;> grind) (by fun_prop) (by fun_prop), exCpRE X
  let N := Subgroup.ofDiv (.range η) .of_subtype (by rintro _ ⟨_, rfl⟩ _ ⟨_, rfl⟩; erw [radicalElt_inv, radicalElt_mul]; apply ρ)
  let e : _ ≃ₜ N := h.toHomeomorph
  have : IsHaarMeasure ((volume.prod addHaar).map e) := by
    refine' { IsFiniteMeasureOnCompacts.map _ e, e.2.isOpenPosMeasure_map e.surjective with .. }
    refine fun ⟨_, x, rfl⟩ ↦ ((e.measurable.measurePreserving _).of_semiconj ((measurePreserving_add_left _ x.1).skew_product (g := fun c b ↦ x.2 + P (toAdele (j : E) • x.1ᴴ * stdForm E t * c) + b) (Continuous.measurable ?_) ?_) (by
      intro; ext1; show η _ = _ * η _; apply G.ext_mat; simp [η, P, radicalElt]; clear * -
      match_scalars <;> grind) ?_).2 <;> first | fun_prop | simp [map_add_left_eq_self]
  refine (integral_orbitMeasure_iwasawa (ideleAbs ·.1 ^ (Fintype.card r + 1)) volume (haar.prod volume) haar (lineLevi X) h.2 (by fun_prop) (by simp) (by simp [G.continuous_iff, Splitting.levi]; fun_prop) (X.iwasawa · |>.elim fun _ ⟨hk, a, _, _, _, _, p, h⟩ ↦ ⟨⟨_, ρ ..⟩, (a.det⁻¹, p), ⟨_, hk⟩⁻¹, eq_mul_inv_of_mul_eq (h.trans congr(_ * X.levi $(by ext <;> simp)))⟩) (fun p f o ↦ (e.measurableEmbedding |>.lintegral_map _).trans (congr(∫⁻ _, f $(mul_inv_eq_of_eq_mul (levi_conj_radicalElt ..)) ∂_).trans (((MeasurePreserving.prod ⟨Continuous.measurable (by fun_prop), volume_map_mul_mul_adele _ (star _)⟩ ⟨by fun_prop, mapCSA addHaar⟩).lintegral_comp (o.comp h.measurable)).trans ?_))) (fun (a, g) ⟨_, e⟩ ↦ by simpa [Splitting.levi, η, radicalElt, ← G.isClosedEmbedding_mat.1.2.eq_iff, ← ext_iff] using congr((X.kCoord * ($e).mat * X.kAdelic, X.iCoord * ($e).mat * X.iAdelic)).symm) ((pAU E).subtype_injective.prodMap Subtype.val_injective) (((pAU E).qms haar).prod V.quotMeasure) (fun f h ↦ ?_) (fun ⟨⟨_, ξ, rfl⟩, _, h⟩ ↦ (m _).1 ⟨congr(X.levi ($(by ext : 2; simp), _) ∈ _).mp (X.levi_mem_Γ (.scalar _ ξ⁻¹) h), ξ⁻¹, by exact levi_mul_kAdelic ..⟩) (m · |>.2 · |>.elim fun ⟨M, e⟩ ⟨ξ, h⟩ ↦ (X.exists_eq_radicalElt_mul_levi h).elim fun c ⟨b, t, p, o, u, v⟩ ↦ ⟨(⟨_, ξ, rfl⟩, ⟨p, V.mem_Γ_iff_range.2 (mem_ratMatrices.1 ⟨V.J⁻¹ * X.iᴴ * V'.J * M.1.1 * X.i, by simp [← e, iCoord, v, iAdelic, mat_ratEmbed, V'.map_J, map_J_inv, Space.ratMap]⟩)⟩⁻¹), by
    simp [← Prod.inv_mk, (ext u : t = .scalar _ (ξ.map _)), o]; apply ρ⟩) ⟨_, κ.preimage_val h.2, fun ⟨_, _, rfl⟩ ↦ (K ..).elim fun _ ⟨_, a, b⟩ ↦ ⟨⟨_, ρ ..⟩, (m (radicalElt ..)).1 ⟨a, 1, by simp⟩, b⟩⟩).imp fun c ↦ .imp_right fun H a b f g o i ↦ ?_
  · simp [ideleAbs_eq_one_of_mem_unitary (x := p.2.toUnitary.1.det) p.2.det.2, pow_succ', prod_smul_left, prod_smul_right, mul_assoc, e.measurableEmbedding.lintegral_map]; rfl
  · rw [lintegral_prod, ← lintegral_orbitMeasure_lintegral (ν := @count (pAU E) _), lintegral_prod]
    congr!; simp (disch := fun_prop) [↓lintegral_count, lintegral_tsum, ← lintegral_orbitMeasure_lintegral (ν := @count V.Γ _)]; rfl; repeat fun_prop
  let k y h := ∑' x : (E ∙ ·) ⁻¹' {y}, constTermAt A (replicateCol _ x.1) (pairWeil _ _ a b (g, h) f)
  have ek : k (E ∙ X.k.col ()) = _ := funext fun h ↦ (((ofInjective _ ((smul_left_injective _ (mt (congrArg (_ * replicateCol _ ·)) (X.gram_lk.trans_ne (by simp)))).comp val_injective)).trans (subtypeEquivRight fun _ ↦ span_singleton_eq_span_singleton.symm.trans comm)).tsum_eq _).symm.trans (tsum_congr (constTermAt_smul_k A X ·.ne_zero))
  have hk γ y h : k (γ • y) (V'.ratEmbed γ * h) = k y h := (((toPerm γ).subtypeEquiv fun x ↦ .trans (smul_left_cancel_iff γ).symm (by erw [smul_span]; simp)).tsum_eq _).symm.trans (tsum_congr fun x ↦ by simpa [ctInt A a b, rep_apply_apply] using! congr(integral _ fun _ ↦ $(thetaTerm_ratEmbed_mul ..)))
  have km y : Measurable (k y) :=
    .tsum fun _ ↦ by simpa [ctInt A a b, -sourceTerm_radicalElt] using
    (Continuous.stronglyMeasurable (by fun_prop)).integral_prod_left.measurable
  refine (integral_tsum_orbit V'.ratEmbed_injective (by rfl) km hk rfl fun _ ↦ .rfl).elim
    fun f O ↦ (H _ (km _) (fun n e h ↦ ?_) f (ek ▸ i)).elim fun p q ↦ .trans (congrArg _ (funext fun h ↦ ((hasSum_subtype_iff_of_support_subset fun y hy ↦ ?_).2 ((hsCT A a b).summable.hasSum.tsum_fiberwise _)).tsum_eq.symm)) (ek ▸ q ▸ (O (.inr p)).2.1)
  obtain ⟨⟨⟨⟩, rfl⟩, p, q, r⟩ := e, A.sourceTerm_levi V' (a / upsilonU1) b 1 1 n, (X.homTarget_zeroTerm_pairWeil W · (b / upsilonU1) n 1 1 · · 1), map_mul (pairWeil W' V' a b) (1, n) (g, h)
  clear * - p q r ek; simp_all [lineTerm, radicalElt_mul_iAdelic, η]
  obtain ⟨⟨x, rfl⟩, hx⟩ := not_forall.1 (hy <| tsum_congr · |>.trans tsum_zero)
  exact (V'.witt (.of_ne_zero (x := x) (hx <| · ▸ o _)) ⟨_, X.gram_lk⟩ (X.gram_kk ▸ by_contra (hx <| ite_eq_right ·))).imp fun _ e ↦ (map_span ..).trans (by simp [← e]; rfl)
unseal Finset.univ Finset.sum Finset.prod
end
open Complex Fintype MatMul MeasureTheory ProbabilityTheory Real SemilocalField Set Space WeilData MeasureTheory.Measure
attribute [-instance] DiscreteUniformity.instDiscreteTopology
attribute [-simp] card_punit card_unique Nat.cast_add θ_apply map_smul
variable {μ} (𝔠 : SplitTameChar E μ) (e : ℤ)
omit [WeilData E] in
def lValueProd S (ν : AutChar E) (e : ℕ) := (∏ᶠ w ∈ S, FinPlace.q w : ℕ) ^ e ^ 2 * ∏ z ∈ .Icc 1 e, ‖ν.L S z‖ ^ 2
omit [WeilData E] in
def lValueProdInt := lValueProd 𝔠.S 𝔠.ν e.toNat / lValueProd 𝔠.S 𝔠.ν (-e).toNat
omit [WeilData E] in
lemma lValueProdInt_pos : 0 < lValueProdInt 𝔠 e := by apply_rules [div_pos, mul_pos] <;> simp +contextual [sq_pos_iff, ↓finprod_mem_coe_finset, (𝔠.weight_pos _).ne', 𝔠.hasWeight.L_ne_zero, funext_iff, Finset.prod_pos]
variable [Fintype b] {ν : AutChar E} (X : V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X]
lemma rankTwist_eq_mul_of_splitting (A : W'.Splitting W b) : rankTwist ν n' = rankTwist ν n * upsilonU1 ^ card b := by simp [rankTwist, mul_assoc, pow_add, A.card_eq, Nat.add_mul_div_left]
lemma pairWeil_stdRowDatum_eq_self {𝔠 : SplitTameChar E μ} {c v z k f} (σ : r' ⊕ r ≃ n) (hz : IsIntMatrix O z) (hk : k ∈ Kf E r) (e : localDatum W V v (stdRowDatum σ 𝔠.χ z) 𝔠.readsAt = f) : pairWeil W V (rankTwist 𝔠.ν⁻¹ n) c (1, k) f = f := by erw [← e, 𝔠.readsAt.pairWeil_localDatum_of_mem_Kf (stdRowDatum_mem ..) (by simp) hk, ← map_smul, smul_name]; congr!; convert (isPartner_stdRowDatum_stdColDatum σ hz).left_mul (g := atPlaces _ k⁻¹) _ <;> cases mem_intGL.1 hk <;> simp_all [atPlaces, rankTwist, ↓← 𝔠.nu_det_of_mem_Kf (s := t), ← map_inv, mem_intGL, evalPlaces_mem_O]
set_option synthInstance.maxSize 999
local instance : LocallyCompactSpace (maxCompact E t) := inferInstance
lemma exists_constant_term_thetaLarge {b} [Fintype b] σ' (σ : b ⊕ r ≃ n) (hn : 2 ∣ card n) μ : ∃ β, ∃ z ≥ 1, ∃ C, ∀ 𝔠 : SplitTameChar E μ, ∃ γ ≠ 0, ‖γ‖ ^ 2 * lValueProdInt 𝔠 (card r - card n / 2) = C * lValueProdInt 𝔠 (card r - card n / 2 + 1) ∧ ∀ v', IsRapidDatum v' → ∀ s, IsIntMatrix O s → ∀ u g, u = 1 ∨ card r = card n → ∫ q, thetaLarge W' V' 𝔠 v' (stdRowDatum σ' 𝔠.χ (s * (adaptedFrame 𝔠.readsAt A).I')) (lineRadical A q * A.levi (.scalar _ u, g)) ∂radicalMeasure = γ * thetaLarge W V 𝔠 (haar.prod haar)[coneIntegrand A X μ β z v'] (stdRowDatum σ 𝔠.χ s) g := by
  obtain ⟨a, ⟨d, hc⟩, β, z, hz⟩ := @measurePreserving_prodAssoc, id hn, (Int.rec (⟨true, ·, rfl⟩) (⟨false, ·, by lia⟩) : ∀ e, ∃ β, ∃ z : ℕ, e = _root_.cond β ↑z (-↑z - 1)) (card r - card n / 2); let τ (β : Bool) x : ℝ := d - card r + ite β (x - 1) (-x); obtain ⟨⟨c₁, _, H₁⟩, ⟨l, H₃⟩, e, k, k'⟩ := exUnfCT A X, exLTLD A σ' σ X, show τ β z.succ = 0 ∧ (1 : ℝ) ≤ z.succ ∧ (1 : ℝ) < z.succ + 1 by norm_cast +zetaDelta +beta; lia
  let j β : (𝔸 E)ˣ ≃ₜ* _ := _root_.cond β (.refl _)
    ⟨.inv _ * starMulAut, continuous_star.inv, continuous_inv.star⟩
  let ε β := (j β).trans {MulEquiv.prodUnits, Homeomorph.prodUnits with}; choose ρ _ hε using fun β ↦ (⟨_, .nnreal_smul haar (haarScalarFactor_pos_of_isHaarMeasure ..).ne', by fun_prop, (isMulLeftInvariant_eq_smul ..).trans (prod_smul_right _).symm⟩ : ∃ ρ, IsHaarMeasure ρ ∧ MeasurePreserving (ε β) haar (haar.prod ρ)); let η β := (ρ β).real (@idelesUnitOff E _ _ ∅ ∩ univ); refine ⟨β, _, k, ‖c₁ * η β * (l β).1 * ideleAbs (scaleIdele E) ^ z.succ‖ ^ 2, fun 𝔠 ↦ ?_⟩
  obtain ⟨i, q, ⟨γ, hγ, H₃⟩, w, c, d₁, d₂, d₃ : ideleAbs (finIdeleIncl c)⁻¹ = _⟩ :=
    𝔠.hasWeight.isHeckeOfType, 𝔠.readsAt, H₃ 𝔠.readsAt 𝔠.tameLocalChar, (lValueProdInt_pos 𝔠 z.succ).ne', exists_idele_star_eq_unif 𝔠
  set N := adaptedFrame q A; let K := finIdeleIncl c⁻¹ * scaleIdele E; let R β (s : ℝ) := l β * γ * 𝔠.ν.baseChange.1 K * (ideleAbs K ^ s :)
  let f p a := ite (idem (conjClosure 𝔠.S)ᶜ * a ∈ Ô E)
    (invOnUnits 𝔠.χ (evalPlaces _ a) / invOnUnits 𝔠.χ (evalPlaces _ (star a) * p)) 0
  choose U M Y using fun β ↦ i.tate_integral (conjClosure 𝔠.S) (f 1 ·) _ (ρ β) isOpen_univ ⟨⟩ (by unfold f; simp +contextual [invOnUnits, ↓isIntegralUnit_iff_v_eq_one, or_imp, idem_mul_mem_Ô, star_involutive.surjective.forall (p := (star · ∈ _ → _))])
    (by unfold f; simp +contextual [div_mul_eq_mul_div, 𝔠.invOnUnits_mul_div_star, idem_mul_mem_Ô]) (by unfold f; simp +contextual [mem_Ô, evalPlaces, RingHom.pi, ↓idem_mul_mem_Ô])
  constructor
  refine (fun h ↦ ⟨fun e ↦ U β (by simpa [(lValueProdInt_pos ..).ne', η, *] using h.1), h⟩)
    (.symm ⟨fun v hv s hs u g hu ↦ .trans (integral_thetaIntegral_lineRadical A _ _ (q.isTargetBounded hv (stdRowDatum_mem ..)) _) (H₁ _ _ _ _ |> fun H ↦ And.elim (H (by simp [rankTwist_eq_mul_of_splitting A, constTermAt_zero, A.sourceTerm_levi, (by simpa [localDatum, ← Pi.zero_def] using (q.sourceTerm_localDatum A V' (G := 0) (stdRowDatum_mem σ' 𝔠.χ (s := s * N.I')) 0 v fun w k ↦ by_contra fun h ↦ by
    simpa [k, IntegralFrame.blocks_spec, N] using congr(N.K' * $((isPrimitiveMatrix_of_stdColDatum_ne_zero .one _ (.trans_eq h (ite_self 0))).2.choose_spec.2) * N.K)) :)]) · |>.trans) ?_), ?_⟩)
  extract_lets F T Θ₀ m at H; let L h := θ _ ∘L pairWeil W V (rankTwist 𝔠.ν⁻¹ n) (rankTwist 𝔠.ν⁻¹ n) (g, h) ∘L (integrated _).flip (namedVector W V (stdRowDatum σ 𝔠.χ s) q); have key β ξ p : T β ξ p = θ _ _ := rfl; simp_rw [F, (by simp : ∀ (x : G E s') (y k : G E t'), (x, y * k) = (x, y) * ((1, k.1, 1) * (1, ↑k.2))), ← rep_apply_apply, pairWeil_stdRowDatum_eq_self _ (hs.mul N.blocks_spec.2.1) (_ : maxCompact ..).2.2 rfl, pairWeil_integrated_right, rankTwist_eq_mul_of_splitting A, card_unit, pow_one, lineTerm_pairWeil_levi A X hu, spaceChar_rankTwist hn, H₃] at key
  let J β : _ ≃ pAU E := (_root_.cond β 1 (.inv _ * starMulAut.1)).trans
    (.ofInjective _ (Units.map_injective (@toAdele E ..).injective))
  have P β p : _ = ∑' ξ, T β (toAdele ξ) p := Units.val_injective.tsum_eq fun _ ↦ Ne.isUnit ∘ mt (by simp [invOnUnits, key, ·]); let Θ σ p := Θ₀ p * (ideleAbs (p.1.1 * u)).rpow σ; let Z β x := (L · <| coneIntegrand A X μ β x v ·).uncurry; have o β : Z β = _ := funext₂ fun x p ↦ (map_smul ..).trans (mul_rotate ..).symm; have hI β x h : Integrable (Z β x) (V.quotMeasure.prod _)
  · obtain ⟨m, i, -, H⟩ := stdRowDatum_mem σ 𝔠.χ, integrable_coneIntegrand A X μ β h hv
    exact (pairTheta_decay_of_onto W V _ _ _ q.1 (q.isSchwartzBruhat m) (fun _ ↦ @m.2.2 _) 0).elim fun N ⟨Q, D, b⟩ ↦ (H Q).elim fun _ ⟨j, H⟩ ↦ ((j.comp_snd _).norm.const_mul _).mono' ((by simp [L]; fun_prop :
      Continuous (L · ·).uncurry).comp_aestronglyMeasurable₂ (by fun_prop) i.1.comp_snd)
      (.of_forall fun p ↦ (mul_one _).ge.trans ((b _ _ _ ((H _).trans_lt enorm_lt_top).ne).trans (by grw +useKAbstract [mul_right_comm, le_abs_self (D * _), H, toReal_enorm]; simp)))
  have B β s h : Integrable (Θ (τ β s)) m ∧ m[Θ (τ β s)] = R β s * (𝔠.ν.L 𝔠.S s * η β) * (V.quotMeasure.prod (haar.prod haar))[Z β s]
  · refine (?_ : _ = Θ _) ▸ ((((a ..).prod (.id _)).comp ((a ..).symm.comp (.comp (.prod (.id _) ((hε β).comp (measurePreserving_orbitMeasure.mul_right _ (u / (j β).symm K)))) ((a ..).comp ((measurePreserving_swap.comp (a ..)).prod (.id _)))))).fubini ((hI β s h.le).mul_prod ((M β s h).const_mul _))).imp (·.integral_prod_left)
      (by erw [·, ← Y β s h, mul_comm, ← integral_const_mul, ← integral_prod_mul])
    simp_rw [Θ, Θ₀, fun p ↦ (P _ p).trans (.trans ((tsum_lineTerm A X β).1 _) (P β p).symm), ← tsum_mul_left, ← tsum_mul_right, integral_count_eq_tsum, ← (J β).tsum_eq]; congr! with ⟨⟨a⟩⟩ ξ; simp [MeasurableEquiv.prodAssoc, -map_mul]; have e : toAdele ξ.1 = j β (J β ξ) := β.rec (eq_star_of_eq_star (star_toAdele _).symm) rfl
    generalize h : ε _ _ = y; rw [(by rw [← h, (Units.ext (Prod.fst_mul_snd _) : (ε β _).1.map (.inl ..) * finIdeleIncl (ε β _).2 = j β _)]; simp [Subgroup.smul_def, mul_assoc, K] : a =
      (j β).symm ((j β (J β ξ))⁻¹ * (y.1.map (.inl ..) * finIdeleIncl y.2 * finIdeleIncl c⁻¹ * scaleIdele E)) * u⁻¹), (β.rec rfl rfl : ⇑(j β).symm = _root_.cond β id star⁻¹)]
    have a a : ite .. = _ := show f ϖ.1 a = f 1 (a * c) by unfold f; simp +contextual [d₁, d₂, idem_mul_mem_Ô, (funext (d₁ _ <| 𝔠.star_notMem _ ·.2) : evalPlaces _ _ = 1)]
    cases β <;> simp [↓a, (congrArg _ (Units.ext e)).symm.trans (ideleAbs_toAdele ξ), e, key, o, hc, L, τ, R, K, pow_mul, fun x ↦ (congr(𝔠.ν.1 ⟨$(by simp [mul_comm]), _⟩) : 𝔠.ν.baseChange.1 (star x) = 𝔠.ν.baseChange.1 x⁻¹), pow_add, 𝔠.hasWeight.baseChange_apply_inf, HeckeChar.finPart, finIdeleAbs, mul_pow, rpow_add, rpow_sub, inv_rpow, rpow_neg, mul_rpow, ← ofReal_pow, 𝔠.ν.baseChange.2 _ ⟨_, e⟩] <;> field (disch := simp [rpow_def_of_pos])
  have I := mellin_analytic_on_strip (by simp) (by fun_prop) (B false _ k').1.2 (B true _ k').1
  obtain ⟨a, a'⟩ := I.1 0 (by clear * - e; grind), EqOn.of_subset_closure (B β · ·.1 |>.2)
    (I.2.1.comp (by unfold τ; split <;> fun_prop) fun _ ↦ by clear * -; grind) (.mul (.mul (by
    fun_prop (disch := simp)) (((i.exists_hasPrimeDensity (by simp [Finite.star]) (i.ne_one (by simp
               [↓funext_iff, (𝔠.weight_pos _).ne']))).1.mono fun _ ↦ (·.1)).mul_const _)) (o β ▸ (mellin_analytic_on_strip (by simp) (continuous_ideleAbs.comp (.units_map _ (.prodMk_left _))).snd'.snd'.measurable (o β ▸ hI β 1 le_rfl).2 (o β ▸ hI β _ k'.le)).2.1)) Ioc_subset_Icc_self (by simp) ⟨k, by simp⟩
  simp [e, Θ] at a a'; use a; erw [a', ← mul_assoc, integral_prod _ (hI β _ k)]; rcongr; exact (L _).integral_comp_comm (integrable_coneIntegrand _ _ _ β k hv).1; cases β <;> simp [hz, mul_pow, lValueProdInt, lValueProd, add_comm (1 : ℤ), R, K, d₃, Finset.prod_Icc_succ_top, ↓neg_add', ↓finprod_mem_coe_finset, card_ResField, ← 𝔠.S.prod_attach, hγ, TameLocalChar.ResidueRing, Nat.card_pi] at w ⊢ <;> field (disch := simp [w])
