import Lib.General.Groups.IndexOfProduct
import Lib.Weil.DualPair.Flip
import Lib.Weil.Lift.Staircase
import Lib.SiegelWeil.Formula.SiegelWeilFormula
seal Finset.univ Finset.sum Finset.prod
noncomputable section
section
open ComplexConjugate ContinuousLinearMap Filter Fintype Gf Kronecker Lagrangian stdLattice MatMul Matrix MeasureTheory Space Valued WeilData Splitting Std Weil NumberField CompactlySupported
variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] {s t} {S : Space E n s} {T : Space E m t} (b : AutChar E)
def vacuumCoeff M (b : AutChar E) (g : Gf E n) := (b.1 (detFin 1 g) * finMultiplier g ^ M)⁻¹
def cosetRep {A} (γ : Gf E n ⧸ localLevel n A) : supportedOn n A := ⟨componentOn n A γ.out, by aesop⟩
def dD : 𝒮 (S.hom T) →L⋆[ℂ] 𝒮 (S.hom T) →L[ℂ] 𝒮 ((S.sum S.neg).hom T) := (boxProd homSigns_sum_source).flip.comp ((exists_theta_negSource S T).choose • negSource.map (V := S.neg.hom T))
attribute [local simp] add_mem localLevel mem_stdLattice coordMatrix add_mul dD ite_mem mem_Kf_iff mem_LocInt mul_add mul_assoc pos_iff_ne_zero finMultiplier_inv rep_apply_apply
@[simp] def gS (S : Space E n s) (δ : U S.J) : CompleteSplitting (S.sum S.neg) n := by use fromRows δ (-1), fromRows δ.1.1 1 * (2⁻¹ : E) • S.J⁻¹, 0 <;> simp [← U.form_mul_inv_eq, S.isHermitian_J.inv.eq, two_mul, ← two_smul E]; ext ⟨⟩
def cosetTerm M b A {e} (y' y : S.Form e) (γ : Gf E n ⧸ localLevel n A) := vacuumCoeff M b
    (cosetRep γ).1 * inner ℂ y' (S.formRep _ (cosetRep γ) y)
abbrev weilMatrixCoeff f (f' := f) g := dataInner _ f' (pairWeil S T 1 b (g, 1) f)
def IsClean F := (∀ i j, s i = s j) ∨ ∃ A Ψ w f, Set.IsConjDisjoint A ∧ IsSchwartzBruhat A Ψ ∧ (∀ y, Ψ y ≠ 0 → HasLeftInv ((vecToMat y).map (_root_.evalAt w))) ∧ F = (S.hom T).name A Ψ f
structure IsSharp S₀ (F : 𝒮 (S.hom T)) J c where
  self_ne_zero : dataInner _ F F ≠ 0
  mem_finitePart : F ∈ finitePart _
  vacuum_off A v : Disjoint S₀ A → projOn _ A (integrated _ v F) = integrated _ v F
  coeffIntegrand_eq : ∀ g ∈ localLevel n S₀ᶜ, weilMatrixCoeff b F F g = if g ∈ J ⊓ Kf E n then dataInner _ F F else 0
  mass_eq : dataInner _ F F / stdLevelIndex J = c
  clean v : IsClean (integrated _ v F)
lemma ztGS δ f f' : (gS S δ).lagrangian.zeroTerm T (dD f' f) = weilMatrixCoeff b f f' (S.ratEmbed δ⁻¹) := by
  rw [weilMatrixCoeff, dataInner_eq_quotMean, ← quotMean_comp (_root_.ratVectors E (m × n)) ((S.hom T).x⁻¹.1 * (T.J⁻¹ ⊗ₖ S.Jᵀ).map toAdele).toLin' (by apply (isThetaFunctional_rawTheta _).1.isContPeriodic (isThetaFunctional_rawTheta _).1) (by simp_all [map_mulVec_mem_ratVectors, mem_ratVectors_iff]) (mulVec_surjective_iff_isUnit.2 (by rw [hom_point_inv_mul_kronecker]; refine (kroneckerGL (IsUnit.unit ?_) ((isUnit_transpose _).2 ?_).unit).isUnit <;> simp [S.map_J, map_J_inv])), ztLag, θ_apply, Splitting.zeroTerm_apply]; congr!
  dsimp [kAdelic, homSource, -θ_apply]; rw [← θ_ϱ, rho_boxProd, theta_boxProd_source, _root_.smul_apply, map_smul, ← Std.map_ϱ, (exists_theta_negSource ..).choose_spec.2, pairWeil_of_mem_Gamma]; simp_rw [hom_point_inv_mul_kronecker, kronecker_mulVec_eq_matToVec, mat_ratEmbed]; any_goals simp [Γ, sum, Space.neg, ← U.form_mul_inv_eq]
  congr; apply inv_smul_smul (normNegOneIdele E)
attribute [-simp] conjTranspose_map_toAdele
lemma exGrEq {a b f g f'} (hf : IsClean f) L (h : Lagrangian.zeroTerm T L (dD f' (pairWeil S T a b (g, 1) f)) ≠ 0) : ∃ δ, (gS S δ⁻¹).lagrangian = L := by
  obtain ⟨⟨_, D⟩, rfl⟩ := L.cS; have e := D.k.fromRows_toRows.symm; generalize toRows₁ _ = K, toRows₂ _ = K' at e
  obtain ⟨k, rfl⟩ := by simpa [e, add_neg_eq_zero, ← two_mul] using And.intro D.gram_kk D.card_eq
  obtain ⟨B, o : K' * B = 1⟩ := ((mulLeftLinearMap n E K').linearEquivOfInjective (.of_ker _ fun c (i : K' * c = 0) ↦ by
    suffices K * c = 0 by simpa [*] using congr($D.gram_lk * c).symm
    obtain hs | ⟨A, Ψ, w, f, hA, _, hy, rfl⟩ := hf
    exacts [ext_col fun j ↦ eq_zero_of_isotropic_of_definite hs _ (by
      simpa [i, ← cᴴ.mul_assoc, ← conjTranspose_mul] using! congr((cᴴ * $k * c) j j)), by_contra fun o ↦ let F := dD f' ∘L pairWeil S T a b (g, 1); h <| name_eq_zero_of_invariant hA _ (S.coordMatrix g _) (ℓ := Lagrangian.zeroTerm T _ ∘L F) (fun z f ↦ by
        simpa [F, homSource_kAdelic, pairWeil, ω_ϱ, ztLag, show (c.map toAdele)ᴴ * D.lCoord = (fromCols ((S.coordMatrix 1 (K * c))ᴴ * stdForm E s) 0) by simp [lCoord, kAdelic, ← map_inv, *, sum, ← stdForm_sum, ← (c.map _)ᴴ.mul_assoc, ← conjTranspose_mul, ← Matrix.map_mul],
          ↓kronecker_mulVec_eq_matToVec, rho_boxProd, Function.comp_def, g⁻¹.mat_preserves_stdForm,
          matToVec, ← Pi.zero_def] using! (congrArg (θ _) ((D.homSource T).zeroTerm_rho_kAdelic (matToVec (vecToMat z * (c.map toAdele)ᴴ)) (F f)))) (S.mul_coordMatrix_ne_zero o T.dualFrame⁻¹ <| hy · ·) f]) (by simp [Module.finrank_matrix])).surjective 1
  use (U.of (by simp) (-K * B) (by simpa [o, ← Bᴴ.mul_assoc, ← conjTranspose_mul] using
    congr(Bᴴ * $k * B)))⁻¹, eq_of_le fun | _, ⟨y, rfl⟩ => ⟨-B *ᵥ y, by simp [*]⟩
lemma gsInj : (gS S ·⁻¹ |>.lagrangian).Injective :=
  fun _ _ e ↦ by simpa [fromRows_ext_iff, ← Units.ext_iff, -coe_units_inv] using
  Filling.exists_mul_eq_of_col_mem_range (e.ge ⟨_, mulVec_single_one _ ·⟩)
lemma inner_product_formula (h : 2 * card n < card m) a b {f} (hf : IsClean f) {y y'} (hy : y ∈ S.rapidFunctions) (hy' : y' ∈ S.rapidFunctions) (f' := f) : let k g := weilMatrixCoeff b f f' g * S.petersson y' (rightRegular ℂ _ ℂ g y); Integrable k ∧ T.petersson (lift (pairThetaKer S T a b) f' y') (lift (pairThetaKer S T a b) f y) = T.quotMeasure.real .univ * ∫ g, k g := by
  choose _ η hη hB using ((pairThetaKer S T 1 b).swap.exists_rat_norm_le_height 1).exists; let u (y : _ → ℂ) g := y g • (pairThetaKer S T 1 b).swap.ω (1, η g * g); let d g g' := dD (u y' g' f') (u y g f)
  have q g g' h : θ _ (sw _ T (1, h) (d g g')) = conj (θ _ (pairWeil S T a b (g', h) f') * y' g') * (θ _ (pairWeil S T a b (g, h) f) * y g) := by
    dsimp [d, u, -θ_apply]; rw [show ∀ c, sw _ T _ = pairWeil _ T (a * (a⁻¹ * upsilonU1 ^ card n)) c (.sum (1, G.neg 1), h) by simp [pairWeil, ← two_mul], pairWeil_boxProd_source, theta_boxProd_source, mul_comm, _root_.smul_apply,
      map_smul, pairWeil_negSource a b, (exists_theta_negSource ..).choose_spec.2,
      ← (pairThetaKer ..).theta_rat_mul _ (hη g') g', ← (pairThetaKer ..).theta_rat_mul _ (hη g) g]
    simp [pairWeil, ← map_mul]; ring_nf
  obtain ⟨⟨V, W⟩, ⟨N, i, o, H⟩, _, _⟩ := siegel_weil T (gS S 1) h, thNT T (gS S 1) h, hy.1.1, hy'.1.1; let Φ := fun (x, g) ↦ weilMatrixCoeff b f f' g * (conj (y' x) * y (x * g)); let ε g g' := Equiv.trans (β := S.Γ) (.ofInjective _ S.ratEmbed_injective) (.trans (.mulLeft ⟨_, hη g'⟩⁻¹) (.mulRight ⟨_, hη g⟩))
  have e g g' δ : (gS S δ⁻¹).lagrangian.zeroTerm T (d g g') = Φ (g', g'⁻¹ * (ε g g' δ * g)) := by
    rw [ztGS b, weilMatrixCoeff, ← dataInner_pairWeil _ _ 1 b ((η g' * g')⁻¹, 1)]; simp [Φ, u, hy.1.2]; erw [Equiv.trans_apply]; simp; ring!
  have k {y} (r : S.IsRapid y) g := show ‖u y g‖ₑ ≤ .ofReal _ by
    grw [← ofReal_norm, norm_smul, hB, mul_left_comm, (r _).choose_spec]
  have l {c} (_ : c ≠ ⊤) : ∫⁻ g, c * ‖d g.2 g.1‖ₑ ∂S.quotMeasure.prod S.quotMeasure < ⊤ := by
    grw [le_opENorm₂, le_opENorm, le_opENorm, k hy.2, k hy'.2, lintegral_const]; finiteness
  have P := (measurePreserving_prod_inv_mul S.quotMeasure _).comp (.comp (.prod (.id _) measurePreserving_orbitMeasure) (measurePreserving_prodAssoc _ S.quotMeasure _))
  have J : Integrable Φ _ := ⟨Continuous.aestronglyMeasurable (by fun_prop), (l (tsum_enorm_ne_top_iff_summable_norm.2 (V.comp_injective gsInj))).trans_le' (by
    grw [← P.lintegral_comp (by fun_prop), lintegral_prod_le]; gcongr
    grw [lintegral_count, ← (ε ..).tsum_eq, ← ENNReal.tsum_mul_right, ← le_opENorm]
    simp_rw [e]; rfl)⟩
  simp_rw [petersson, lift, ← integral_const_mul (dataInner _ f' _), ← integral_conj, ← integral_prod_mul]; use J.integral_prod_right; erw [← integral_prod_symm _ J, ← (P.fubini J).2, ← integral_integral_swap ⟨by fun_prop, (l o).trans_le' (by simp_rw [← lintegral_mul_const _ i]; grw [lintegral_prod_le, ← H _ 0]; simp [q])⟩]; simp_rw [← q, integral_count_eq_tsum, ← integral_const_mul, W]
  congr!; rw [← (ε ..).tsum_eq, ← gsInj.tsum_eq fun L ↦ by
    simpa [d, u, -dD] using fun _ _ ↦ exGrEq hf L,
    funext (e _ _)]; rfl
omit [WeilData E] in
lemma opLL A : IsOpen {g : G E s | g.2 ∈ localLevel n A} := (Subgroup.isOpen_mono (by simp_all [LE.le]) isOpen_Kf).preimage_of_continuous
def partialIntegral A (Φ : G E s → ℂ) := ∫ g in {g | g.2 ∈ localLevel n A}, Φ g
lemma hasSum_partialIntegral_coset B {D A ι b f c} (t : ι → supportedOn n A) (hf : projOn (S.hom T) A f = f) (hΦ : Integrable (weilMatrixCoeff b f * c)) (o : supportedOn n A ≤ localLevel n B) (e : localLevel n D = localLevel n A ⊓ localLevel n B) (ht : ∀ g, ∃! γ, (t γ).1⁻¹ * g ∈ localLevel n A) : HasSum (fun γ ↦ vacuumCoeff (card m) b (t γ).1 * partialIntegral D (weilMatrixCoeff b f * (c <| (t γ).1 * ·))) (partialIntegral B (weilMatrixCoeff b f * c)) := by
  unfold partialIntegral; have M := opLL (s := s) D; have O γ :=
    isOpenMap_mul_left ↑(t γ).1 _ M
  have := Pairwise.countable_of_isOpen_disjoint ?d O fun _ ↦ ⟨_, 1, by simp, rfl⟩; convert! hasSum_integral_iUnion (O · |>.measurableSet) ?d hΦ.restrict; rw [(measurePreserving_mul_left ..).setIntegral_image_emb (measurableEmbedding_mulLeft _), ← integral_const_mul, ← setIntegral_congr_fun M.measurableSet fun g k ↦ ?_]; erw [Pi.mul_apply, weilMatrixCoeff, ← Prod.mk_one_mul_mk_one, map_mul, pairWeil_apply, map_smul, ← congr(dataInner _ $hf), dataInner_projOn, G.onHom_fin, projOn_ω _ _ (projOn_pairWeil hf _)] <;> simp [finMultiplier_onHom_left, vacuumCoeff, field]; congrm _ * b.1 ?_ / _; ext <;> simp
  all_goals simp [Set.ext_iff, Pairwise, e, mul_mem_cancel_left, o (t _).2, -localLevel, (ht _).exists] <;> grind [(ht _).unique]
omit [WeilData E] in
lemma tendsto_partialIntegral B {Φ : G E s → ℂ} (hΦ : Integrable Φ) : Tendsto (fun R : Finset (FinPlace E) ↦ partialIntegral (R \ B) Φ) atTop (nhds (partialIntegral Bᶜ Φ)) := (tendsto_setIntegral_of_antitone (fun _ ↦ (opLL _).measurableSet) (fun _ ↦ by aesop) ⟨∅, by simpa⟩).trans_eq (by congr with; simpa using ⟨(· {·} _ (by simp)), by tauto⟩)
lemma exists_integral_isotropic_frame (h : 2 * card n ≤ card m) : ∃ x : Matrix m n _, (∀ i j, x i j ∈ Ô E) ∧ xᴴ * x = 0 ∧ ∃ u : n ↪ m, ∀ i, x (u i) = Pi.single i 1 := by have ⟨ι⟩ := @Function.Embedding.nonempty_of_card_le (n ⊕ n) m _ _ (by simp; lia); use inclMatrix _ (ι ∘ .inl) + (inclMatrix _ (ι ∘ .inr)).map (Weil.normNegOne.1.1 * ·), ?_, ?_, .trans .inl ι <;> simp [inclMatrix, entrywise, apply_ite star, ite_add_ite, funext_iff, eq_comm]
lemma exDD (h : 2 * card n < card m) {f A} (hf : projOn (S.hom T) A f = f) (hA : A.Finite) : ∃ f', ∀ g, weilMatrixCoeff b f f' g = if g.2 ∈ localLevel n A then weilMatrixCoeff b f f g else 0 := by
  obtain ⟨⟨x, _, _, u, _⟩, N, _, hN⟩ := exists_integral_isotropic_frame (E := E) h.le, @exists_forall_mul_mem_Ô E _ _ _ hA.cj (singleAdele ·.1 (uniformizer _).1⁻¹ * (j⁻¹ : E)); let z := idem A.conjClosure * (j / N : E); let κ := G.onHom (s := s) (s' := t) (1, 1, U.of (by simp) (1 + z • x * xᴴ) (by simp [z, ← xᴴ.mul_assoc, neg_div, *]))
  have V p q y (h : (p⁻¹ * q : G ..).2.1.1 *ᵥ y ∈ _) := by
    simpa [*] using congr(ω _ p $(finHeisOp_projOn _ (S := A) h f))
  use finHeisOp _ (idem A.conjClosure • ∑ k, Pi.single (u k, k) 1) (ω _ κ (finMultiplier κ.2⁻¹ • f)), inv_surjective.forall.2 fun g ↦ ?_; split_ifs with c
  · unfold κ; erw [G.onHom_fin]
    rw [weilMatrixCoeff, ← projOn_pairWeil hf _, ← finHeisOp_projOn, dataInner_finHeisOp, ← dataInner_projOn, projOn_ω] <;>
      simp +contextual [atPlace, *, z, finMultiplier_ne_zero, Units.ext_iff, ← ext_iff, apply_ite]
  simp [weilMatrixCoeff, pairWeil, finMultiplier_ne_zero]; contrapose c
  have K w (_ : w ∈ A.conjClosure) i k : v (g.2.1 i k w) ≤ 1 := (@Finite.exists_max _ _ _ ⟨k⟩ _ (v <| g.2.1 i · w)).elim fun l hp ↦ (hp k).trans (_root_.not_lt.1 fun o ↦
    have Z : 1 < v (z w) := by simpa [z, ← map_natCast (algebraMap E (𝔸f E)), -map_natCast, field, ← WithZero.lt_mul_exp_iff_le, *] using mem_Ô.1 (hN ⟨w, ‹_›⟩) w
    have ⟨μ, _⟩ := w.valuedAdicCompletion_surjective E (v (z w) ⊔ v (g.2.1 i l w))
    let σ := singleAdele w μ⁻¹
    have I y : y * σ ∈ Ô E ↔ v (y w) ≤ v μ := by
      rw [mem_Ô, ← and_forall_ne w]; aesop (add simp field)
    mt (forall_psi₀_mul_eq_one_iff (idem A.conjClosure * idem A.conjClosure * z * g.2.1 i l * σ)).1
      (by simp [↓I, *, o.pos, Z.pos]) fun d hd ↦ star_inj.1 (mul_right_cancel₀ c (by
    nth_rw 2 [← dataInner_finHeisOp _ (idem A.conjClosure • (κ * G.onHom (g⁻¹, 1)).2 *ᵥ Pi.single (u l, i) (d * σ))]
    rw [V, finHeisOp_comm, V] <;> simp (maxDischargeDepth := 4) [κ, ← map_inv, ← map_mul, G.onHom_snd, psi₀_eq_one_of_mem, sum_dotProduct, apply_ite star, mul_apply, (psi₀ E).map_add_eq_mul, mul_left_comm _ d, mul_mem, mul_left_comm z, mul_comm σ, (mem_Ô.1 hd w).trans Z.le, *])))
  exact fun w h ↦ mem_intGL.2 ⟨by rw [atPlace_star (star_star w)]; simp [atPlace, *], by tauto⟩
attribute [local simp] G.mat_scalarFin Modulus.disjoint_places_star dataInner_name coe_divStar matToVec
variable (𝔪 : Modulus E) (S : Space E n s) (T : Space E m t)
def Modulus.flipScalar (n := Unit) [Fintype n] := scalarFin n (divStar (star (𝔪.generator * α)))
attribute [-simp] boxIndicator_apply
lemma Modulus.exMKF (c : (Ô E)ˣ) (hc : star c.1.1 * c = -1) V (hl : ((1, c) : 𝔸 E) • T.x.1 = V.x) a b : ∃ C, ‖C‖ ^ 2 * card 𝔪.ResRing ^ (card m * card n) = 1 ∧ ∀ D P g h, modKernel V S a b 𝔪 D P (.neg g) h = C * modKernel S T (b⁻¹ * upsilonU1 ^ card n) (a⁻¹ * upsilonU1 ^ card m) 𝔪 (matrixFourier (𝔪.primAddChar.mulShift (𝔪.reduction (-star c))) D) (flipPoly t s P) h (g * (1, 𝔪.flipScalar m)) := by
  have H w := congr(_ • name _ _ $((𝔪.liftFn_single w).trans (by
    ext; simp [boxIndicator, mem_integralBox, mem_Ô, vecToMat, scalarFin, idem_apply]
    congr! 6; grind [generator_spec, disjoint_places_star])) _).trans (pairWeil_name_on (a := a) (b := b) 𝔪.disjoint_places_star (Ψ := (boxIndicator _ 𝔪.places <| · + -𝔪.generator⁻¹.1 • (↑) ∘ w)) (g := scalarFin _ (divStar (star 𝔪.generator))) (by simp_all [Gf.atPlace, scalarFin, generator_spec, map_mul, Units.ext_iff, map_zero]) (one_mem _) (V.hom S).vacElem).symm
  choose z _ hF using exists_pairTheta_flip (c := -c) (by simpa) (by simp) V S T (1, scalarFin _ (divStar (star α))) (by simp [← hl, val_flipIdele, smul_smul, Prod.star_def]; grind) b; constructor; use ?hN; introv; nth_rw 1 [eq_inv_mul_iff_mul_eq₀ (b := z * _) (by simpa [·] using ?hN), pi_eq_sum_univ' D]; simp [matrixFourier.eq_unfold, ← modKernelBilin_apply, Finset.smul_sum, ← smul_eq_mul, ← Pi.smul_def, ← Finset.sum_fn, smul_comm _ (D _)]; rcongr v; erw [← (𝔪.reduction_surjective.comp_left.comp_left v).choose_spec, modKernelBilin_apply, modKernel, modDatum, Pi.single_comp_equiv (.curry ..), smul_eq_mul, ← map_smul, ← map_smul, ← map_smul, H, ← isSchwartzBruhat_boxIndicator.schrodingerAct_idem, name_schrodingerAct_boxIndicator, ← pairWeil_integrated_fin, ← pairTheta, ← pairTheta_mul, ← hF, projOn_vacElem, map_integrated, ← (apply_finVec (flipCoords ..) _).trans (congrArg _ ?_), map_ϱ, map_vacElem, ← projOn_vacElem, ← 𝔪.name_char_eq_translate_projOn _ (-star c.1 • matToVec _ ∘ .swap), realMap_flipCoords_polyVector]; congr with x; simp [dotProduct, sum_prod_type, mul_left_comm (x _), ← Finset.mul_sum]; rfl; any_goals simp [flipCoords, starCoordEquiv, funext_iff, hc, flipScalar, -map_mul, smul_smul]
  iterate 2 grind [idem_mul_self, idem_mul_star, idem_conjClosure_eq_add_star, disjoint_places_star]
  simpa [localInner_liftFn, name_boxIndicator, field, mul_comm, *] using congr(‖dataInner _ $(H 0) $(H 0)‖⁻¹)
lemma exists_conj_modKernel_eq_swap a b : ∃ c, ‖c‖ ^ 2 * card 𝔪.ResRing ^ (card n * card m) = 1 ∧ ∀ D P g h, conj (modKernel S T a b 𝔪 D P g h) = c * modKernel T S b a 𝔪 (matrixFourier 𝔪.primAddChar (conj <| D ·)) (flipPoly s t (P.map conj)) h (g * 𝔪.flipScalar n) := by
  obtain ⟨⟨c, _, K⟩, C, _, H⟩ := exists_modKernel_neg_left S T, 𝔪.exMKF T S _ star_normNegOne_mul_self S.neg rfl ..; use c * C, by simp [*]
  intros; rw [K, H, mul_assoc]; congr 3 with <;> simp [field, -map_neg]
  apply sum_equiv (MulAction.toPerm 𝔪.normNegOne⁻¹); simp [-map_neg]; tauto
lemma exists_modKernel_flip_line u 𝔪 b a' k : ∃ ψ, ∃ c : ℂˣ, ‖c.1‖ ^ 2 * card (n → 𝔪.ResRing) = 1 ∧ ∀ P D h, modKernel (signedSpace E fun _ ↦ -u) S 1 b 𝔪 D P (1, k) h = c * modKernel S (signedSpace E fun _ ↦ u) a' upsilonU1 𝔪 (matrixFourier ψ D) (flipPoly (fun _ ↦ u) s P) h (1, k * 𝔪.flipScalar) := by refine ⟨_, (𝔪.exMKF S _ (normNegOne ^ u.1) ?_ _ ?_ ..).elim fun _ H ↦ ⟨.mk0 _ (fun _ ↦ by simp_all) * Circle.toUnits _, .trans ?_ H.1, by
  intros; erw [H.2 _ _ (1, k)]; rw [← mul_div_cancel a' (_ * _), mul_comm 1⁻¹, modKernel_twist]; simp [field]⟩⟩ <;> fin_cases u <;>
  simp [signedSpace, ← Matrix.ext_iff, normNegOneIdele, normNegOne_inv, mul_comm normNegOne.1.1]
variable {n'} [Fintype n'] (l : InfinitePlace E → _) (s : n → _) {s'}
def kernelPair d := typeKernel (negIf d l) s
variable {l l' s} (S : Space E n s) (T : Space E n' s') (a : ∀ n [Fintype n], AutChar E) {𝔪 : _} (P Ψ)
abbrev modLift e e' := formLift (pairThetaKer S T (a n) (a n')) e e' (modDatum S T 𝔪 Ψ (polyVector _ P))
abbrev modDescent e' e := formLift (pairThetaKer S T (a n) (a n')).swap e' e (modDatum S T 𝔪 Ψ (polyVector _ P))
variable {S T P Ψ} {I : Type*} (a : I → ∀ n [Fintype n], AutChar E) (k : Bool → GInf E s → ℂ) (k' : Bool → GInf E s' → ℂ)
lemma pairWeil_modDatum_single {a b x y v} k k' (h : x = (𝔪.reductionK₀ k')⁻¹.1 * y * (𝔪.reductionK₀ k).1 := by simp; rfl) :
  let g := ((1, k.1), 1, k'.1); pairWeil S T a b g (modDatum S T 𝔪 (Pi.single x 1) v) = pairChar a b g • modDatum S T 𝔪 (Pi.single y 1) v := by simp [pairWeil_modDatum_Kf, h, funext (Pi.single_apply _ _), Matrix.mul_left_inj_of_invertible, Matrix.mul_right_inj_of_invertible]
def IsConjKernelPair := ∀ d, IsCuspKernel 0 (k d) ∧ k (!d) = star (k d)
def IsEdgeFamily d Φ := IsConjKernelPair k ∧ IsConjKernelPair k' ∧ ∃ γ γ', ∃ ψ : I → _, (∀ i, (a i n).HasWeight γ (ψ i)) ∧ (∀ i, (a i n').HasWeight γ' (ψ i)) ∧ IsEdge (realPairWeil γ γ') (k d) (k' d) (polyVector _ Φ)
omit [WeilData E] in
lemma isConjKernelPair_kernelPair {d} [Nonempty n] (h : ∀ w, (toHCParam s (negIf d l w)).HasLargeGap 0) : IsConjKernelPair (kernelPair l s) := by have := (h · |>.neg); cases d <;> simp_all [IsConjKernelPair, kernelPair, typeKernel, isCuspKernel_typeKernel, funext_iff] <;> simp [← conj_dsKernel_neg (h _)]
lemma isEdgeFamily_of_paramsCorrespond [Nonempty n] [Nonempty n'] {γ : ∀ n [Fintype n], _} {ψ : _ → _} d [H : ∀ i n [Fintype n], (a i n).HasWeight (γ n) (ψ i)] (h : ParamsCorrespond (γ n) (γ n') (negIf d l) (negIf d l') s s') : IsEdgeFamily a (kernelPair l s) (kernelPair l' s') d (jointHarmonic (γ n) (γ n') (negIf d l) (negIf d l') s s') := ⟨isConjKernelPair_kernelPair (by simpa using h · |>.swap.hasLargeGap.neg), isConjKernelPair_kernelPair (h · |>.hasLargeGap), _, _, _, (H · _), (H · _), h.isEdge_jointHarmonic⟩
variable {a k k' d} (h : IsEdgeFamily a k k' d P) {i}
omit [WeilData E] in
lemma IsConjKernelPair.form_mem_rapidFunctions (h : IsConjKernelPair k) (y : S.Form (k d)) : ↑y ∈ S.rapidFunctions := y.2.mem_rapidFunctions (h _).1
include h
lemma IsEdgeFamily.isArrow_modDatum : let K := pairThetaKer S T (a i n) (a i n'); let φ := modDatum S T 𝔪 Ψ (polyVector _ P)
    IsArrow K (k d) (k' d) φ ∧ IsArrow K.swap (k' !d) (k !d) φ := have ⟨A, B, _, _, _, _, _, v⟩ := h
  by simp [A d, B d, modDatum, v.isArrow, name_mem_finitePart]
lemma IsEdgeFamily.exists_lift_eq_realConv Q : ∃ α : C_c(_, ℂ), ∀ i S T 𝔪 x y, lift (pairThetaKer S T (a i n) (a i n')) (modDatum S T 𝔪 x (polyVector _ Q)) y.1 = realConv α (modLift S T (a i) P x (k d) (k' d) y) := have ⟨_, _, _, _, _, v⟩ := h.2.2
  (v.lift_isForm_and_eq_realConv _ ⟨Q, rfl⟩).imp (by introv m; simpa [h.isArrow_modDatum.1.coe_formLift] using!
    (m _ (pairWeil_integrated _ _ _ _) y.2).2)
lemma IsEdgeFamily.petersson_descent_eq Q : ∃ κ, ∀ i S T 𝔪 x y z, T.petersson z.1 (star (lift (pairThetaKer S T (a i n) (a i n')) (modDatum S T 𝔪 x (polyVector _ Q)) (star y.1))) = κ * inner ℂ (modDescent S T (a i) P x (k' !d) (k !d) z) y :=
  (h.exists_lift_eq_realConv Q).imp' _ (by introv m; erw [m (y := conjForm _ y), h.isArrow_modDatum.2.inner_formLift_adjoint h.isArrow_modDatum.1, ← z.2.petersson_realConv_realConv (h.2.1 _).1 (Subtype.prop _) _ (star a).integrable, z.2.3] <;>
  simp [Space.petersson, realConv, ← integral_conj, h.1 d, h.2.1 d, ↓(h.2.1 _).1.1.2]; rfl)
end
attribute [local simp↓] Modulus.disjoint_places_star Modulus.localInner_liftFn Space.dataInner_name
variable {E n m : Type} [Field E] [CMType E] {𝔪 : Modulus E} [Fintype n] [Fintype m] {s t} [WeilData E] {S : Space E n s} (T : Space E m t) {w : FinPlace E}
lemma isSharp_modDatum b (hn : (∀ i j, s i = s j) ∨ Nonempty 𝔪.places) (L : Matrix n m 𝔪.ResRing) {F : Matrix m n _ → ℂ} (u : ∀ y, F y ≠ 0 → L * y = 1) {γ ψ} [hb : AutChar.HasWeight b γ ψ] (hψ : ∀ w ∉ 𝔪.places, ψ w = 1) (ne : star F ⬝ᵥ F ≠ 0) : IsSharp b 𝔪.places.conjClosure ((S.hom T).name 𝔪.places (𝔪.liftFn (F ∘ vecToMat)) (Space.vacElem _)) (𝔪.levelOfSubgroup ⊥) (star F ⬝ᵥ F / Fintype.card (m × n → 𝔪.ResRing) / Fintype.card (GL n 𝔪.ResRing)) := by
  erw [← comp_equiv_dotProduct_comp_equiv _ _ (.curry ..)] at *; have q := isPrimitiveMatrix_of_liftFn_ne_zero Prod.mk fun _ ↦ (⟨L, u _ ·⟩)
  refine ⟨by simpa, Space.name_mem_finitePart .., by simp_all [Space.projOn_name_vacElem], fun g _ ↦
    ?_, by simp [Modulus.stdLevelIndex_levelOfSubgroup]; rfl, fun _ ↦ hn.imp_right fun ⟨w⟩ ↦ ⟨_, _, _, _, by simp, inferInstance, fun _ ↦ (q w.2 ·|>.2.imp (by tauto)), Space.integrated_name ..⟩⟩
  by_cases k :
    g ∈ Kf E n; erw [weilMatrixCoeff, ← modDatum_vacVector, pairWeil_modDatum_Kf _ _ _ _ _ ⟨g, k⟩ 1]
  split <;> simp_all [hb.apply_det_eq_charOfTamePart hψ ⟨g, k⟩]
  exact .inr (Finset.sum_eq_zero (by simp; grind [=_ Matrix.mul_assoc, Units.val_eq_one])); rw [weilMatrixCoeff, pairWeil_apply, (Space.omega_name ..).2, map_smul, Space.dataInner_name, localInner, MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero] <;> simp_intro .. [k]
  by_contra! c
  have o w h : IsPrimitiveMatrix _ (g.atPlace w).1 :=
    (q h c.1).mul_iff.1 (Matrix.map_mul.subst (q h c.2 :))
  grind [mem_Kf_iff, Gf.atPlace_star_mem_iff, mem_localLevel, isPrimitiveMatrix_iff_mem_intGL]
def realZetaCoeff (w : FinPlace E) : ℂ := ite (WellOrderingRel w (star w)) (-1) 1
omit [WeilData E] in
lemma realZetaCoeff_factor_mul (hw : w.IsSplit) x : (1 - realZetaCoeff (star w) * x) * (1 - realZetaCoeff w * x) = 1 - x ^ 2 := by grind [realZetaCoeff, star_star, trichotomous_of WellOrderingRel, @asymm _ WellOrderingRel]
lemma exists_hasSum_vacuumCoeff_at_place {ν l ψ k} (hν : ν.HasWeight l ψ) (hψ : ψ w = 1) (hψ' : ψ (star w) = 1) (hk : 1 < k) : ∃ (ι : Type) (t : ι → Gf.supportedOn _ {w}), (∀ g, ∃! γ, (t γ).1⁻¹ * g ∈ localLevel Unit {w}) ∧ HasSum (vacuumCoeff (2 * k) (ν * WeilData.upsilonU1 ^ k) <| t ·|>.1) (∏ u ∈ {w, star w}, (1 - realZetaCoeff u / u.q ^ k) / (1 - (ν.baseChange.atUnif u)⁻¹ / u.q ^ k)) := have m g : g ∈ Kw Unit w ↔ (Valued.v g.1.det).log = 0 := mem_intGL_iff_det.trans (by simp [← @WithZero.exp_eq_one ℤ, -Matrix.det_unique]; aesop)
  if h : _ then ⟨Unit, 1, fun g ↦ by simpa [m, self_eq_neg, localLevel] using congr((Valued.v $(g.atPlace_star h).det).log), by simp [vacuumCoeff, finMultiplier_eq_one_of_mem, irrefl, HeckeChar.atUnif, hk.ne_zero, realZetaCoeff, *, (hν.exists_baseChange_finPart_locIdele ..).2, MulChar.one_apply, w.one_lt_q.ne']⟩ else ⟨ℤ, (⟨_, atSplit_mem_supportedOn h <| diagGL fun _ ↦ uniformizer w ^ ·⟩), by simp [m, localLevel, add_eq_zero_iff_eq_neg, -Matrix.det_unique], by
    have d (z : ℤ) := by apply glMultiplier_eq_pow_of_local (b := locGL w (diagGL fun () ↦ uniformizer w ^ z)) (y := diagGL fun _ ↦ uniformizer w ^ (-z).toNat) _ ⟨_, _, _, _, 1, _, eq_add_of_sub_eq rfl⟩ <;> cases z <;> simp_all
      [mem_subring_matrix_iff, sub_mem, (LocInt w).pow_mem ((v_uniformizer w).trans_le (by decide))]
    have B u : ‖ν.baseChange.atUnif u / u.q ^ k‖ < 1 := by simp [field, one_lt_pow₀, hk.ne_zero]
    convert! have H u := hasSum_geometric_of_norm_lt_one (B u)
      (H (star w)).int_rec ((hasSum_nat_add_iff' 1).2 (H w))
    erw [vacuumCoeff, finMultiplier, glMultiplier_mul (by grind [evalAt_star_locGL, evalAt_locGL_of_ne]), G.det_of_supportedOn, detOn_eq_prod _ {w}, Finset.prod_singleton, ((hν.mul_upsilonU1_pow k).charUnramifiedAt _ _).apply_locFullIdele] <;> simp [*, ↓hν.atUnif_star, ← map_inv, Pi.inv_def, ← zpow_neg, HeckeChar.atUnif, HeckeChar.finPart, glMSt]; cases ‹ℤ› <;> simp [zpow_add_one₀, mul_pow, div_pow, add_nonneg, ← Circle.coe_inv_eq_conj, w.q_eq_sqrt_sq] <;> field
    simp [*, hν.atUnif_star, Ne.symm]
    grind [norm_one, q_star, HeckeChar.norm_atUnif, hν.atUnif_star, realZetaCoeff_factor_mul h (w.q ^ k)⁻¹]⟩
