import Lib.Shimura.Uniformisation.LiftedIsogenies
import Lib.Shimura.TraceFormula.DefiniteTrace
import Lib.Shimura.Uniformisation.ModelAlongArc
import Lib.General.Geometry.Lefschetz
import Lib.Shimura.GoodReduction.ThetaOrthogonality
import Lib.Shimura.AbelianScheme.ThetaFamily
section FoldSeg0
open CategoryTheory AlgebraicGeometry Submodule LineBundle Set Nat IsLocalRing Spec
attribute [local simp] H0_smul ValuativeArc.genericPt_eq
attribute [local simp ←] Over.comp_left map_nsmul
lemma ThetaObject.TorusModel.isRigid_pullback {E O W} [Field E] [CMBase E] [CommRing O]
    [ValuativeArc O] [FinComplexSpace W] {D : PEL E} {Z τ} {X : ThetaFamily D Z τ} {y :
  ThetaObject X (Spec ⟨O⟩)} {g ℓ} {Y : PeriodMap D g ℓ W} (a :
  y.TorusModel Y) {k} [Field k] [IsAlgClosed k] (χ : O →+* k) {x₀ : ThetaObject X _}
  (h : specMap χ ≫ y = x₀) : x₀.IsRigid := fun B _ _ _ x ↦ map_surjective.forall.2 fun ϕ g ↦ by
  obtain ⟨h : x.IsPullbackAlong _ y, C, m, hN⟩ := (map_comp_assoc ..).trans (h ▸ g),
    hasConstFunctions_of_isPullback g.isGroupBaseChange.1, (eventually_span_coordSection
    x.groupScheme x₀.isProjEmbedding g.isGroupBaseChange.1).exists_forall_of_atTop
  have ⟨c, P, e⟩ : ∃ c > m, (c : k) ≠ 0 := by by_contra!; simpa [*] using @cast_succ k _ m.succ
  let M {S} (x : ThetaObject X S) := x.lineBundle.pull (c • 𝟙 x.groupScheme).1
  let Λ {R} [CommRing R] x := pullSections (.id R) (by simp) (refl (M x))
  let Q := pullSections _ h.schemeMap.w (by simp [M, h.lineBundle_eq_pull, ← pull_comp _,
    h.isGroupBaseChange.nsmul_id_comp] : M x = .pull (M y) _)
  obtain ⟨hΦ, hR, N⟩ := (isSectionLift_pullSections ..).comp (Θ := Q) (exists_isSectionLift (L :=
    .pow _ _) (𝟙 _) (picClass_pow .. ▸ pull_nsmul_eq_sq_smul y.hasClassLaws.1 c)).choose_spec,
    a.uniformisation.card_torsion P.ne_zero, P.ne_zero
  obtain ⟨⟨_, h'⟩, F, ⟨⟩⟩ := exists_isSectionLift (𝟙 _) (L := M x) hΦ.picClass_eq.symm,
    (equivFinOfCardPos (hR.trans_ne
    (by simp [N]))).symm, by exact_mod_cast x.finite_flat_surjective_smul (cast_ne_zero.2 N)
  let τ {B} [CommRing B] {x} (j : _ →+ _) := ∑ z, pullSections (.id B) (by simp) (by simp [M,
    ← pull_comp _, ← comp_nsmul _, (F z).2] : M x = (M x).pull (translation (j (F z).1)).1)
  refine ⟨C, top_unique fun σ _ ↦ (smul_mem_iff_of_isUnit _ ((e.isUnit.map ϕ.1).pow _)).1
    ((apply_mem_span_image_iff_mem_span (isSectionLift_pullSections ..).injective).1 (Eq.subst (by
    ext; simp [τ, Λ, ← comp_nsmul _, (F _).2, *]; rfl) (mem_comap.1 ((h'.injective.mem_set_image
    (a := Λ x σ)).1 (span_le.2 (range_subset_iff.2 fun j ↦
    (((isSectionLift_pullSections _ h.schemeMap.w rfl).exists_eq_smul C (h'.comp hΦ)).choose_spec
    (coordSection (a.hasThetaCoords.pow _).1 j)).symm.subst (smul_mem _ _ (mem_map_of_mem ((fun θ ↦
    by_contra fun hσ : τ h.isGroupBaseChange.pullSection (Q θ) ∉ span B (Λ x '' _) ↦ ?_) _))))
    ((h.lineBundle_pow_eq_pull _ ▸ g.lineBundle_eq_pull ▸
    hN (c ^ 2) (by nlinarith)) ((a.hasThetaCoords.pow _).1.pull _) ▸ ⟨⟩))))))⟩
  let ω := τ (.id _) θ; let v z := a.uniformisation.expMap ((c : ℂ)⁻¹ • z)
  have hv z : c • v z = a.uniformisation.expMap z := by simp [v, ← cast_smul_eq_nsmul ℂ, N]
  have J z : atGeneric v z ≫ (c • 𝟙 y.groupScheme).1 =
    atGeneric a.uniformisation.expMap z := by simp [atGeneric, ← hv]
  have s := a.hasThetaCoords.pull 1 (J · |>.symm) fun _ ↦ id
  obtain ⟨r, _, _⟩ := by simpa using (s.exists_theta_of_isSection (s.pow 0) (w :=
    (ω.1 ·.1)) (by simpa [IsSection, LineBundle.pow, inf_of_le_left] using! ω.2.1) (fun _ ↦
    (a.uniformisation.immersive _).1.comp (by fun_prop)) fun l _ _ _ ↦
    by simp [ω, τ]; apply Fintype.sum_equiv (F.symm.permCongr (.subtypeEquiv (.addLeft (v l)) _))
    <;> simp_all [v, atGeneric, add_assoc])
  have K (w : span O (range (coordSection a.hasThetaCoords.1))) b (p : ∀ i,
    _ := by simp +contextual [Λ, M, a.hasThetaCoords.4 .., *] <;> simp [atGeneric,
    field, *]) := have H : Λ y w = b • ω := H0_ext fun {i} ↦ ((isSeparatingFamily_atGeneric (s :=
      v) (a.uniformisation.4.comp (MulAction.surjective₀ (by simpa)))).pointFn_ext · · (p i))
    (⟨(residue_eq_zero_iff b).2 fun z ↦ hσ (Eq.subst (a := Q ω) (by ext; simp [Q, ω, τ,
      h.isGroupBaseChange.translation_comp]) (mem_comap.1 ((smul_mem_iff_of_isUnit _ z).1
      (((Λ y).map_span_le ..).2 (by simp [Λ, Q, pullSections_coordSection, mem_span_of_mem,
      ← range_comp', ↓forall_mem_range]) ⟨_, w.2, H⟩)))), H⟩ : _ ∧ _)
  obtain ⟨γ, _, n, p, G⟩ := exists_sections_of_translation_stable _ a.hasThetaCoords
    y.obj_isThetaStructure.4 a.exists_isTranslationLift_of_dualLattice (by bound)
    (by tauto) () (by simpa [·] using K 0 1)
  obtain ⟨g, e⟩ | ⟨g, e⟩ := ValuationRing.isInteger_or_isInteger O γ
  exact (K (n 0) g).elim fun k e ↦ G _ (_ ≫ (y.levelPoints 0).1) fun z _ _ i ↦ by
    simpa [Λ, hv, k] using congr($e.1 i _ (specMap (residue O) ≫ (v z).1))
  simpa using K (g • n 0) 1
end FoldSeg0
section FoldSeg1
noncomputable section
open Topology Matrix Polynomial ComplexOrder Complex LinearMap Real Fintype Finset
variable (E) {n} [Field E] [Ψ : CMBase E] [Fintype.{0} n] {D : PEL E} (e : (n → ℂ)
    ≃L[ℂ] ℂ × BallBase n) (H : Matrix n n ℂ)
attribute [local simp] map_smul' mulVec_sub ModuliPoint.act polarisationForm mul_sum
  vecMulVec_mulVec roots_eq_map_numberedRoots smul_smul
  PeriodMap.intAction PEL.xi_im_pos_and_re_eq_zero Prod.ext_iff toBilin'_apply' mulVec_transpose
attribute [local simp ←] Complex.coe_smul dotProduct_mulVec mulVec_mulVec
attribute [-simp] Prod.forall map_smul map_smul_of_tower map_sum Pi.star_apply Prod.smul_mk
@[simp] def ballPeriod : ℂ × BallBase n →ₗ[ℂ] RealVectors E n →ₗ[ℝ] BallFibre E
  n := by apply mk₂' ℂ ℝ fun q w ↦
  ((e.symm q ⬝ᵥ H *ᵥ (w · v₀)) • (1, 0) + q.1 • e (star (w · v₀)) - (e (star (w · v₀))).1 • q,
  fun v ↦ q.1 • (w · v)) <;> intros <;> ext <;>
  simp [-smul_eq_mul, ← Pi.add_def, ← Pi.smul_def] <;> ring
abbrev positiveBall := {b | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re}
abbrev formReflection u := vecMulVec u ((2 / star u ⬝ᵥ H *ᵥ u) • star u ᵥ* H) - 1
variable {E H}
lemma exists_eq_formReflection (hH : H.IsHermitian) {J} (p : (H * J).PosDef) : IsReflection J →
  ∃ u, 0 < star u ⬝ᵥ H *ᵥ u ∧ J = formReflection H u | ⟨u, _, _⟩ => ⟨u, by
              obtain _ := p.dotProduct_mulVec_pos (by aesop : u ≠ 0), star_form p.1
              simp_all [star_form hH, ext_iff_mulVec]
              grind⟩
lemma exists_analyticFamily_positiveBall e {H} (hS : IsConnected (positiveBall e H)) (hn : ∀ y ≠ 0,
  (e (star y)).1 = 0 → star y ⬝ᵥ H
  *ᵥ y < 0) {ℓ g β} (hβ : IsSignedFrameFor g ℓ β) (hH : β.map (Φ v₀) = H) : ∃ f : AnalyticFamily D,
  f.U.1 = positiveBall e H ∧ f.frame = g ∧ ∀ b ∈ f.U, f.reflection b =
  formReflection H (star (e.symm (1, b))) ∧ ⇑(f.torus b).Q = ⇑(ballPeriod E e H (1, b)) := by
  let f v := by apply mk₂' ℝ ℂ fun (w : RealVectors E D.Index) (p : BallFibre E D.Index) ↦ 2 * π *
    (Φ v D.ξ).im * if h : v = v₀ then (e (star (w · v))).1 * p.1.1 - e.symm (p.1 - p.1.1 •
    (1, 0)) ⬝ᵥ H *ᵥ (w · v) else star (w · v) ⬝ᵥ β.map (Φ v) *ᵥ p.2 ⟨v,
    h⟩ <;> as_aux_lemma => intros; split <;> simp [-smul_eq_mul, ← Pi.add_def,
      ← Pi.smul_def] <;> ring
  have U : IsOpen (positiveBall e H) := by apply isOpen_lt <;> fun_prop
  choose r hr _ using
    (hS.1.elim (by grind) : ∀ b, ∃ c ∈ positiveBall e H, b ∈ positiveBall e H → c = b)
  have z b := ne_zero_of_re_pos (hr b)
  let P b := ballPeriod E e H (1, r b)
  have l b w v (hv : (w · v) ≠ 0) : 0 < (f v w (P b w)).re := by
    by_cases v = v₀ <;> simp [*, f, P, pi_pos]
    set s := (e _).1
    linarith [by simpa [normSq, ← star_form (hH ▸ hβ.1.isHermitian_map) (star _)] using (by_cases
      (fun _ ↦ by simp_all) (hn ((w · v₀) - star (s • e.symm (1, r b))) · (by simp [s])
      |>.1.trans_le (mul_nonneg s.normSq_nonneg (hr b).le)))]
    simpa [*] using (hβ.2 v).re_dotProduct_pos hv
  have pos b w hw := sum_pos (Pi.lt_def.2 ⟨(by_cases (by simp [f, ·]) <|
    le_of_lt ∘ l b w ·), (Function.ne_iff.1 (mt transpose_eq_zero.1 hw)).imp (l b w)⟩)
  let Q b := ((P b).linearEquivOfInjective (.of_ker _ fun w ↦ (by simpa [·] using! pos b w))
    (by zify; simp [Fin.pos']; ring)).toContinuousLinearEquiv
  have hP b : IsPeriodMap (formReflection H (star (e.symm (1, r b)))) (Q b) := by
    simp_all [Q, P, IsPeriodMap, funext_iff, -smul_eq_mul, ← Pi.sub_def, ← Pi.smul_def]
    grind [smul_eq_mul]
  have d {w} b hb := (((ballPeriod E e H).flip w).toContinuousLinearMap.hasFDerivAt.comp _
    (hasFDerivAt_prodMk_right 1 b)).congr_of_eventuallyEq (f₁ := (Q · w))
    (.mono (U.mem_nhds hb) (by simp_all [P, Q]))
  refine suffices ∀ b, _ from ⟨⟨⟨_, U⟩, hS, g, _, fun b ↦ ⟨⟨β, _, (restrictScalars ℝ
    toContinuousLinearMap.1 ∘ₗ ∑ v, f v).toContinuousLinearMap ∘L (Q b).symm, hβ.1, hP _, ?_, ?_,
    isPosRiemann_of_re_pos (this b)⟩, ⟨_, _, by simp [z], rfl⟩, fun c ↦ ?_, .refl .., by
      simp [LinearMap.ext_iff, reindex_equiv (Q b)]; simp [Q, P, -smul_eq_mul, ← Pi.smul_def]
      simp [funext_iff, field]⟩, fun _ h _ ↦
      analyticAt_of_eventually_differentiable (.mono (U.mem_nhds h) (⟨_, d · ·⟩)), fun b hb v p ↦ by
    simpa [z, ← hP .., (d _ hb).fderiv, two_smul, self_eq_neg, -smul_eq_mul, ← Pi.smul_def] using
    congr($(p (Q b fun i _ ↦ star (e.symm (1, r b)) i)).1.2), by simp, this⟩, rfl, rfl, by
      simp +contextual [*, Q, P, funext_iff]⟩; (Q · |> reindex_equiv |>.1.2
      (by simpa using! pos _)) <;> simp [riemannForm_def, div_eq_iff, reindex_equiv (Q
    b)] <;> as_aux_lemma => intro y; simp [f, Q, P, ← hH, sum_mul, ← sum_sub_distrib, -smul_eq_mul,
    ← Pi.smul_def, ← star_form hβ.1.isHermitian_map (y · _)]; congr! 1; split <;> simp [*,
    mul_sub] <;> ring
lemma exists_ball_chart (hH : H.IsHermitian) {u a} (ha : star u ⬝ᵥ H *ᵥ u = a) (hu : 0 < a) : ∃ e,
  StarConvex ℝ 0 (positiveBall e H) ∧ (∀ y, a * (e y).1 = y ⬝ᵥ H *ᵥ u) ∧ e.symm (1, 0) =
  star u := by
  let j := ContinuousLinearEquiv.equivOfRightInverse (a⁻¹ • H.toBilin'.flip u
    ).toContinuousLinearMap (.toSpanSingleton ℂ (star u)) fun c ↦ by simp [*, hu.ne']
  refine .imp (fun e h ↦ ⟨fun b hb s t _ _ _ ↦ ?_, h⟩) ⟨j.trans (.prodCongr (.refl ..) (.ofFinrankEq
    (by simpa -dsimp using congr($j.finrank_eq.symm - 1)))), by simp -dsimp [j, hu.ne']⟩
  simpa [(e.injective (by simp [← h]) : e.symm (1, ofReal t • b) = star u + t • (e.symm (1, b) -
    star u)), ← h.1 (e.symm _), *, ← star_form hH (star _), field]
    using (convex_Ioi 0).add_smul_sub_mem hu.1 hb ⟨sq_nonneg t, by bound⟩
lemma exists_roots_eq_erase {K} [Field K] ν (Y : Module.End K _) (h₀ : Y (1, 0) = (ν, 0)) (h : ∀ w,
    (Y (0, w)).1 = 0) : ∃ N : Matrix n n K, (∀ x, Y x = (ν * x.1, N *ᵥ x.2)) ∧ N.charpoly.roots =
    Y.charpoly.roots.erase ν := .imp (fun N (e : Y = .prodMap (0 - -ν • 1) N.toLin') ↦ e ▸ by
  simp [↓charpoly_prodMap, roots_mul, X_add_C_ne_zero, N.charpoly_monic.ne_zero, ↓charpoly_sub_smul,
    -map_neg]) ⟨(snd .. ∘ₗ Y ∘ₗ inr ..).toMatrix', by ext <;> simp [*, Prod.mk_zero_zero]⟩
@[simp] def AnalyticFamily.ballPoint {ν} (f : AnalyticFamily D) (P : Fin ν → _) (p : _ × _) :=
  ModuliPoint.mk _ _ ((f.torus p.1).Q.symm ∘ p.2 + P) ⟨_,
  (f.torus p.1).isSignedFrameFor⟩ (f.torus _).reflection
def AnalyticFamily.heckeTranslate (f : AnalyticFamily D) (γ : GUPlus E D.Index) :
  AnalyticFamily D := by
  choose c h k using γ.2.1
  exact ⟨_, f.isConnected, f.frame * γ, _, fun b ↦ let x := f.torus b
    ⟨⟨_, _, c • x.B, x.isFrameFor.mul_iff.2 k,
      x.isPeriodMap, by simp [x.re_symm], by simp [map_rat_smul, x.riemannForm_eq, Rat.smul_def,
      mul_left_comm], isPosRiemann_of_re_pos (by simpa [h] using f.re_pos b)⟩,
      x.reflection, by simpa [h.ne'] using x.adjoint, x.exists_std_equiv⟩, f.analyticAt,
    f.eq_zero_of_linear, by simp [f.form_const 0], by simpa [h] using f.re_pos⟩
lemma exists_ball_family {ν} (o : ModuliPoint E D.Index ν) : ∃ f : AnalyticFamily D, 0 ∈ f.U ∧
  f.ballPoint o.P 0 = o ∧ (∀ a : ModuliPoint E D.Index ν, a.x = o.x → ∃ p ∈ f.U.1 ×ˢ .univ,
  f.ballPoint 0 p = a) ∧ ∀ {g α z μ}, z.1.charpoly.Separable → o.reflection = eigenReflection True z
  μ → (o.act g α).IsLevelIso (levelGU D.Index D.𝔑) z o → ∃ K : Module.End ℂ _, (∀ᶠ q in 𝓝 0,
  ((f.ballPoint o.P q).act g α).IsLevelIso (levelGU D.Index D.𝔑) z (f.ballPoint o.P (K q))) ∧ ∀ t,
  (localTerm α z.1.charpoly μ).eval t = (localTerm α z.1.charpoly μ).eval 0 * (1 - t • K).det := by
  have ⟨_, _, _, ⟨β, S⟩, r₀⟩ := o
  obtain ⟨T, hH⟩ := ite_eq_left rfl ▸ S.2 _, S.1.isHermitian_map
  obtain ⟨u₀, hu₀, rfl⟩ := exists_eq_formReflection hH T r₀
  have ⟨e, hS, he, he₀⟩ := exists_ball_chart hH rfl hu₀
  have hn y hy (h : (e (star y)).1 = 0) := by
    simpa [← he (star y), h] using T.dotProduct_mulVec_pos (x := y) hy
  obtain ⟨f, hU, rfl, hf⟩ := exists_analyticFamily_positiveBall e (hS.isPathConnected
    (by simpa [*] using hu₀.1)).isConnected hn S rfl
  have h0 := (hU ▸ hS).mem f.isConnected.1
  refine ⟨f, h0, by simp [hf _ h0, *], ?_, fun {k α z j} hz hμ R ↦ ?_⟩
  rintro ⟨_, _, P, ⟨_, s⟩, h⟩ ⟨⟩
  cases by simpa using s.conj_eq_smul S (y := 1) ⟨one_pos, 1, by simp⟩
  obtain ⟨u, hu, rfl⟩ := exists_eq_formReflection hH (ite_eq_left rfl ▸ s.2 _ :) h
  have k := mt (hn u (by aesop)) hu.not_gt
  have ⟨b, hb⟩ : ∃ b, (1, b) = (e (star u)).1⁻¹ • e (star u) := by simp [k]
  have m : b ∈ f.U := hU.ge (by simpa [*, inv_mul_eq_div, div_div, mul_conj] using hu.1)
  exact ⟨(b, (f.torus b).Q ∘ P), by
    simp [(hf b m).1, m, hb, formReflection, ext_iff_mulVec, funext_iff]; simp [field, *]⟩
  obtain ⟨⟨c, h₀⟩, _, a, u⟩ := div_mem k.2.1 R.mem_level.1,
    (isReflection_eigenReflection hz).2 _ r₀ R.2
  obtain ⟨⟨⟩, hc, h₂⟩ := (u _).1 hμ,
    S.similitude_and_root_norm (by simpa [← mul_assoc] using h₀) R.reflection_eq
  set μ := numberedRoots (Ψ.Φ v₀) _ j
  have hr := h₂ v₀ μ (by aesop)
  obtain ⟨hμ, h₀⟩ := by simpa [hu₀.ne', smul_comm μ, -vecMulVec_smul] using congr($a *ᵥ u₀),
    mul_ne_zero_iff.1 (hr.trans_ne (by aesop))
  have hZ x w := by simpa [↓map_conjTranspose_mul_mul,
    dotProduct_mulVec _ _ᴴ, -dotProduct_mulVec] using congr(x ⬝ᵥ ($hc).map (Φ v₀) *ᵥ w)
  have ⟨N, hY, hN⟩ := exists_roots_eq_erase (star μ) (e.conj (z.1.map (Φ v₀))ᴴᵀ.toLin')
    (by simp [*, ← star_mulVec, ← e.symm_apply_eq.1 he₀]) fun w ↦ by
    simpa [hμ, ← he (_ ᵥ* _), ← he (e.symm _), hu₀.ne', h₀] using hZ (e.symm (0, w)) u₀
  erw [e.charpoly_conj, charpoly_toLin', z.1.charpoly_map (star _)] at hN
  let G a := ((mulLeft ℂ (Ψ.Φ v₀ a * μ)).prodMap (star (Φ v₀ a) • N).toLin').prodMap
    (piMap fun v : {a // a ≠ Ψ.v₀} ↦ (Φ v a • z.1.map (Φ v)).toLin')
  let K := (star μ⁻¹ • N).toLin'.prodMap (piMap (G <| α ·))
  refine ⟨K, .mono (((f.U.2.prod f.U.2).preimage (f := fun p ↦ ((K p).1, p.1))
    (by fun_prop)).mem_nhds (by simpa)) fun p ⟨h', h⟩ ↦
    have key a w : (f.torus (K p).1).Q (cmEmbedding a • z.1.map cmEmbedding *ᵥ w) =
      G a ((f.torus p.1).Q w) := by
      simp [hf _ h, hf _ h', -smul_eq_mul, ← Pi.smul_def]
      simpa [G, K, star_mulVec, by simpa [reindex_equiv e, ← e.eq_symm_apply] using hY, funext_iff,
        *, ← hr, field] using Or.inl (hZ (star μ⁻¹ • e.symm (1, p.1)) _)
    ⟨R.mem_level,
      (f.torus _).isPeriodMap.ratConj_eq (f.torus _).isPeriodMap (G 1) (by simp [← key]), by
      simpa [K, (f.torus _).Q.eq_symm_apply.2 (key ..)] using R.sub_mem_lattice⟩, fun t ↦ ?_⟩
  have hn r : _ → μ * t - r = -r * (1 - (star μ)⁻¹ * star r * t) := (by grind) ∘ h₂ v₀ r
  simp [lieRoots, (id rfl : 1 - t • K = .prodMap (1 - t • toLin' _) (piMap fun i ↦
    .prodMap (.prodMap (1 - t • mulLeft ..) (1 - t • toLin' _)) (piMap fun v ↦ 1 - t • toLin' _))),
    ← det_toMatrix', map_smul, prod_eq_mul_prod_subtype_ne _ v₀, IsLieRoot, sub_ite, μ,
    ← star_def, *, localTerm, ← map_val, ← map_erase, ← Multiset.map_erase _
    star_injective, ← erase_val, prod_ite, filter_eq', filter_ne', det_pi, piMap, @Subtype.prop _ (·
    ≠ _), -mul_eq_mul_left_iff, charpoly_map, det_prodMap, det_one_sub_smul_eq_prod_roots,
    ↓s11_p6, mul_comm t, eval_prod, ↓prod_embeddings_eq_prod_pairs,
    mul_assoc, -neg_mul, Lagrange.basis, Lagrange.basisDivisor]
  ring
end
end FoldSeg1
noncomputable section
open NumberField Subgroup Submodule nonZeroDivisors
variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {𝔑 : 𝓞 E} (𝔪 : (𝓞 E)⁰)
@[simp] lemma levelGU_inf_one : levelGU n 𝔑 ⊓ levelGU n 1 = levelGU n 𝔑 := inf_of_le_left fun _ h ↦
  mem_levelGU_of_local h.1 h.2.1 (·.2.one_notMem.elim)
lemma exists_level_conj_mem (h : 𝔑 ≠ 0) (s : Finset ((𝓞 E)⁰ × GUPlus E n)) : ∃ m,
  ∀ x ∈ insert (m, 1) (insert 1 s), ∀ k ∈ levelGU n m.1, x.2.1⁻¹ * k * x.2 ∈ levelGU n 𝔑 ⊓ levelGU n
  x.1 := have ⟨M, _, H⟩ := (exists_congruenceGL_subset ((insert 1 s).eventually_all.2 fun x _ ↦
    (by fun_prop : ContinuousAt (x.2.1⁻¹ * · * x.2) 1) (((isOpen_congruenceGL_span h).inter
    (isOpen_congruenceGL_span (coe_ne_zero x.1))).mem_nhds (by simp))))
  ⟨⟨M, by simpa⟩, by
    simp_all [levelGU]; rintro _ _ _ ⟨a, b⟩ s k c d
    simp [mul_mem, inv_mem, *, (H k d).2 _ _ _ _ s]⟩
abbrev NonzeroTorsion n := {s : torsionBy _ (AdelicTorsion E n) 𝔪.1 // s ≠ 0}
instance finite_torsionBy :
  Finite (torsionBy _ (AdelicTorsion E n) 𝔪.1) := Nat.finite_of_card_ne_zero
  (by rw [← torsionBySet_span_singleton_eq, card_torsionBySet_adelicTorsion] <;> simp)
instance : ((levelGU n 𝔪).subgroupOf (levelGU n 𝔑)).FiniteIndex := ⟨relIndex_inf_ne_zero (by
  simp [relIndex_eq_one.2, levelGU]) ((isCompact_intGL isCompact_Ô).relIndex_ne_zero
  (isOpen_congruenceGL_span (by simp)) ∘ relIndex_eq_zero_of_le_right fun _ ↦ (·.2.1))⟩
open Matrix IsDedekindDomain HeightOneSpectrum Nat Set QuadField GeneralLinearGroup
attribute [-simp] coe_units_inv MonoidHom.coe_comp
section
variable {E n : Type} [Field E] [NumberField E] [Fintype n]
lemma exists_residue_torsion_emb w : ∃ ρ : _ →ₗ[𝓞 E] _, (⇑ρ).Injective ∧ ρ.range = .torsionBySet _ _
  w.1 ∧ ∀ x, ∃ v, ρ x = torsionClass v ∧ ∀ g : Matrix n n (Ô E), torsionClass (g.map (·.1) *ᵥ
  v) = 0 ↔ x ∈ residueKer (g.map (·.1 w)) := have L (x : n → Ô E) : torsionClass (singleAdele w
    (uniformizer w).1⁻¹ • (·.1) ∘ x) = 0 ↔ reduceAt w ∘ x = 0 := by simp_all [funext_iff, mem_Ô,
    ← and_forall_ne w, ← v_uniformizer_inv_mul_le_one_iff]
  let p := (Algebra.linearMap (𝓞 E) (ResField w)).compLeft n
  have hk : (torsionClass ∘ₗ ((_ : 𝔸f E) • (Algebra.linearMap ..).compLeft n)).ker = p.ker :=
    Submodule.ext (L <| algebraMap .. ∘ ·)
  have hp : (⇑p).Surjective := (algebraMap_ResField_surjective w).comp_left
  let ρ := liftQ _ _ hk.ge ∘ₗ (p.quotKerEquivOfSurjective hp).symm.1
  have I := ρ.ker_eq_bot.1 (by simp [ρ, LinearMap.ker_comp, ker_liftQ, *])
  by use ρ, I, SetLike.ext' (Finite.eq_of_subset_of_card_le (finite_of_card_ne_zero ?_)
    (by simp_all [subset_def, ← map_smul, funext_iff, Algebra.smul_def])
    (card_range_of_injective I ▸ ?_)), hp.forall.2 fun c ↦ ⟨_, by aesop, fun g ↦ by
    simpa [residueOrZero, funext_iff, mulVec_apply_eq_sum, mem_Ô.1] using! L (g *ᵥ algebraMap .. ∘
      c)⟩ <;> erw [card_torsionBySet_adelicTorsion w.3] <;> simp [card_pi, card_ResField]
end
variable {E n : Type} [Field E] [CMBase E] [Fintype n] {D : PEL E} {d₀ : ℕ} [HasQuadSubfield d₀ E]
  {v : n → 𝔸f E} {w : SplitFinPlace E} {C : Submodule (ResField w.1) (n → ResField w.1)}
omit [Fintype n] in
lemma smul_torsionClass_eq_zero_iff {a} : a • torsionClass v = 0 ↔ ∀ i u,
  u.intValuation a * Valued.v (v i u) ≤ 1 :=
  torsionClass_eq_zero.trans (by simp [mem_Ô, ← v_algebraMap_eq_intValuation, ← map_mul]; rfl)
lemma heckeIsogeny_inv_at_eq_basicCosetRep {I} (hw : IsSafe I w.1) : (heckeIsogeny w C)⁻¹.1.map
  (evalAt _) = (basicCosetRep C).1 := by simp [↓← val_map_apply, heckeIsogeny,
  evalAt_centralScalar_of_ne hw.1.star_ne_and_prime_norm.1.symm, invTransposeGL, transposeGL]
lemma heckeIsogeny_inv_mulVec_of_ne {u} (hu : u ≠ w.1) (hu' :
  u.below _ ≠ star (w.1.below (QuadField d₀))) i : ((heckeIsogeny w C)⁻¹.1
  *ᵥ v) i u = v i u := ((evalAt u).map_mulVec ..).trans (by simp [↓← val_map_apply, heckeIsogeny,
  evalAt_centralScalar_of_ne hu', evalAt_conjAtSplit_of_ne _ hu (by grind [below_star, star_star])])
lemma isScalarFrame_heckeIsogeny : IsScalarFrame (heckeIsogeny w C)
  (w.1.q ^ Module.finrank (ResField w.1) C : ℕ) := ((centralScalar_mem_GU _).2 _ (by simp
  [finIdeleAbs_adeleNorm, norm_locField_eq_q_zpow])).imp_right
  (congr(IsFrameFor $(one_smul ..) _).mp <| ·.mul_iff.2 ⟨1, by simp⟩)
lemma heckeIsogeny_torsionClass C v (hβ : D.β = algebraMap _ _ (c₀ d₀)) (hw :
  IsSafe D.𝔑 w) {b : ℤ} (co : IsCoprime (D.β - b) (star D.β - b)) (hb : D.β - b ∈
  w.1.1) : let s := torsionClass ((heckeIsogeny w C)⁻¹.1 *ᵥ v); (torsionClass v ∈ D.levelTorsion →
    s = torsionClass v) ∧ ∀ N, (D.β - b) ^ N • torsionClass v = 0 → s = 0 →
    torsionClass v ∈ torsionBySet (𝓞 E) _ w.1.1 := by
  simp [PEL.levelTorsion, smul_torsionClass_eq_zero_iff, mem_Ô, torsionClass_eq_iff]
  use fun hv i u ↦ if e : D.𝔑 ∈ u.1 then by simp [heckeIsogeny_inv_mulVec_of_ne (by grind [IsSafe])
    (hw.2.2 u · e)] else have H i := by simpa [intValuation_eq_one_iff.2 e] using! hv i u
    ((LocInt u).1.comap (evalAt u)).sub_mem (sum_mem fun a _ ↦
      mul_mem (mem_Ô.1 ((heckeIsogeny_mem_GUPlus ..).2 i a)
    u) (H a)) (H i), fun N hv h a ha i u ↦ if hu : u = w then hu ▸ mul_le_mul'
    ((intValuation_le_pow_iff_mem _ _ 1).2 (by simpa)) ((congrArg _ (by simp [RingHom.map_mulVec,
    heckeIsogeny_inv_at_eq_basicCosetRep hw] : _ = (_ *ᵥ fun _ ↦ evalAt _ _) i)).trans_le
    (v_matrix_mul_le (basicCosetRep_spec C).1.2.1 (fun _ ↦ h · w) i i)) else mul_le_one'
    (intValuation_le_one ..) (if e : D.β - b ∈ _ then heckeIsogeny_inv_mulVec_of_ne hu (fun h ↦
    w.1.2.notMem_of_isCoprime_of_mem co hb (cast (by simpa [hβ, ↓D.star_beta] using! congr(c₀ _ -
    b ∈ ($h).1)) e)) i ▸ h .. else by simpa [intValuation_eq_one_iff.2 e] using hv i u)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory ThetaFamily
  ThetaObject Obj Over Fintype TorusModel ValuativeArc ModuliPoint Fint Function
variable {E : Type} [Field E] [CMBase E] (D : PEL E)
  (R : Subalgebra (𝓞 E) E) {κ} {ν : ℕ} [Finite κ] {T : AlgebraicGeometry.Scheme}
  {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {O : Type} [CommRing O] [ValuativeArc O]
structure UniversalFamily where
  isDedekindDomain : IsDedekindDomain R
  base : Over (Spec ⟨R⟩)
  family : ThetaFamily D _ (base.hom ≫ specMap (algebraMap ..))
  hasProjEmbedding : HasProjEmbedding base.hom
  smooth : SmoothOfRelativeDimension (card D.Index - 1) base.hom
  obj : AnalyticFamily D × _ → (specOver R ℂ ⟶ base)
  model a : TorusModel (X := family) (obj a).left (a.1.torus a.2).toPeriodMap
  holomorphic f : ∀ b ∈ f.U, ∀ z, HolomorphicAt (fun q ↦
    atGeneric (model (f, q.1)).uniformisation.expMap q.2 ≫ (toFamily (obj _).left).left) (b, z)
  dense : IsDenseFamily (obj · |>.left)
attribute [instance] UniversalFamily.hasProjEmbedding
variable {D R} {U : UniversalFamily D R} (𝔪 : (𝓞 E)⁰) (y : ThetaObject X T) (Q : κ →
  (𝟙_ _ ⟶ y.groupScheme))
instance {S : Scheme} {F : Discrete κ ⥤ Over S} : HasLimit F := inferInstance
abbrev ThetaFamily.fibrePower κ [Finite.{1} κ] := ∏ᶜ fun _ : κ ↦ X.A
abbrev ThetaFamily.proj i := (Pi.π _ i : X.fibrePower κ ⟶ _).left
def ThetaObject.pointOf : T ⟶ (X.fibrePower κ).left :=
  (Pi.lift (y.isGroupBaseChange.pointEquiv <| Q ·)).left
variable {y Q} (a : ModuliPoint E D.Index ν) (t :
  Spec ⟨O⟩ ⟶ (X.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left)
@[mk_iff] inductive ThetaFamily.IsPointOf : Prop | mk {x V} [FinComplexSpace V] {Y :
  PeriodMap D a.x a.reflection V} (m : TorusModel x Y)
  (h : t = x.pointOf ((m.fullStructure.torsionPoint ·.1) ⊕ᵥ (m.π <| a.P ·)))
@[reassoc (attr := simp)] lemma ThetaObject.pointOf_hom : y.pointOf Q ≫ hom _ =
  y := by simp [pointOf]
@[reassoc (attr := simp)] lemma ThetaObject.pointOf_proj i : y.pointOf Q ≫ proj i =
  (Q i).left ≫ y.toFamily.left := congrArg Hom.left (Pi.lift_comp_π ..)
def UniversalFamily.datumPoint := ((exists_ball_family a).elim fun f h ↦ h.2.1 ▸ ⟨homMk _, U.model
  (f, 0), rfl⟩ : ∃ t : specOver R ℂ ⟶ (Over.map U.base.hom) _, U.family.IsPointOf 𝔪 a t.1).choose
lemma fibrePower_ext_iff {t t' : T ⟶ _} : t = t' ↔ t ≫ (X.fibrePower κ).hom = t' ≫ hom _ ∧ ∀ i, t ≫
  proj i = t' ≫ proj i := ⟨by lia, (congr($(show homMk (U := .mk _) t ·.1 = homMk t' by aesop).1))⟩
variable {𝔪} {a} {b : ModuliPoint E D.Index ν} {t} {J : Type} [Finite J]
  (γ : J → (𝓞 E)⁰ × GUPlus E D.Index) {s u : Spec ⟨ℂ⟩ ⟶ _}
attribute [local simp] act isLevelIso_iff fibrePower_ext_iff
lemma ThetaFamily.IsPointOf.of_generic (k : IsPointOf 𝔪 a (genericPt ≫ t)) : IsPointOf 𝔪 a t :=
  k.rec fun m h ↦ have H : IsPullbackAlong .. := ((reassoc_of% h) _).trans pointOf_hom
  (m.exists_model_over_arc H).elim fun m' E ↦ ⟨m', ext_of_isDominant_of_isSeparated (hom _)
    (by simp) genericPt (by simp [*, reassoc_of% E, H.comp_toFamily, fullStructure, ← π.eq_1])⟩
lemma ThetaFamily.IsPointOf.eq_iff (h : X.IsPointOf 𝔪 a s) (k : IsPointOf 𝔪 b u) :
    s = u ↔ ∃ z, a.IsLevelIso (levelGU _ D.𝔑 ⊓ levelGU _ 𝔪) z b := by
  obtain ⟨⟨m, rfl⟩, m', rfl⟩ := h, k
  have J :=
    (Over.forget _).map_injective.comp ((isGroupBaseChange ‹_›).pointEquiv (T := 𝟙_ _)).injective
  simp [show ∀ w, w ∈ frameLattice b.x ↔ ‹PeriodMap ..›.Q w ∈ m'.uniformisation.L by
    simp [m'.lattice_eq, mem_classLattice, frameLattice], ← π.eq_1]
  use fun ⟨rfl, s, P⟩ ↦ ?_, fun ⟨z, ⟨h, k⟩, hz, P⟩ ↦ (m.exists_isogeny z hz m' rfl h.2.1.isIntMatrix
    (levelGU.isScalarFrame_inv_one h)).elim fun ρ ⟨ψ, _, _, c, v, p⟩ ↦ by
    suffices T : ∀ {𝔞}, _ ∈ levelGU D.Index 𝔞 → ∀ s ∈ torsionBy _ _ 𝔞,
      m.fullStructure.torsionPoint s ≫ ψ = m'.fullStructure.torsionPoint s from ((m.isRigid_pullback
      (.id _) (by simp [specMap])).eq_of_hom (Category.id_comp _) ρ.symm ψ (by simp [← pairing_comp,
      c]) (by rw [FullStructure.eta_eq, FullStructure.eta_eq, T h _ ·.2])).imp_right
      (by simp_all [← ·, ← comp_left_assoc, T k])
    rintro 𝔞 k ⟨y⟩ a; choose M m e using (mem_span_singleton_iff_exists_mul.1 <| k.2.2 · ·)
    erw [v, eq_add_of_sub_eq (Matrix.ext e : _ = 𝔞 • M), add_mulVec, smul_mulVec, ← mulVec_smul,
      map_add, torsionClass_mulVec_eq_zero m a]; aesop
  choose z hF hQ hz using m.exists_matrix_of_hom m' (𝟙 _) (hψ := ⟨by simp⟩) one_ne_zero (by simp)
  have T := m.torsionPoint_comp _ hF
  set k := _ * a.x
  simp at T
  have I {k} (h : ∀ {y}, _ = 0 → torsionClass (k *ᵥ y) = 0) (i j : D.Index) : k i j ∈ Ô E :=
    mul_one k ▸ torsionClass_eq_zero.1 (h (torsionClass_eq_zero.2 ((Ô E).matrix.one_mem · j))) i
  have K {𝔞} h (s : ∀ {y}, 𝔞 • y = 0 → m.fullStructure.torsionPoint y = _) : k ∈ levelGU _ 𝔞 :=
    ⟨⟨1, by
    simp [k, ↓← ‹PeriodMap ..›.isFrameFor.mul_iff, mul_assoc, ← IsFrameFor.conj_iff]
    convert ← ‹PeriodMap _ a.x ..›.isFrameFor
    ext; exact sub_eq_zero.1 ((traceForm_nondegenerate ℚ E).1 _ fun a ↦ by
      simpa [show D.ξ ≠ 0 from (by simpa [·] using D.xi_im_pos_and_re_eq_zero v₀), mul_assoc,
        mul_comm a] using hQ (toRealVectors (Pi.single _ a)) (toRealVectors (Pi.single _
        (star D.ξ⁻¹))))⟩, mem_intGL.2 ⟨I (m'.fullStructure.injective <| by simp [← T, ·]),
    I (m.fullStructure.injective <| by simp [T, ·])⟩, fun i j ↦
    mem_span_singleton_iff_exists_mul.2 ⟨_, torsionClass_eq_iff.1 (m'.fullStructure.injective
    (T (Pi.single j (isUnit_algebraMap_finAdele (a := 𝔞) h).unit⁻¹.1) ▸ s (torsionClass_eq_zero.2
    (by simp [ite_mem, Algebra.smul_def])))) i, by simp [mul_sub, mul_left_comm]⟩⟩
  use z, ⟨K D.level_ne_zero (m.fullStructure.eta_eq ⟨_, ·⟩ ▸ m'.fullStructure.eta_eq _),
    K (by simp) (dite _ (by simp [·]) <| (J ·) ∘ s _ ·)⟩, hz, (J <| hF _ ▸ P ·)
namespace UniversalFamily
abbrev GraphClosure ν := ReducedClosure fun j a ↦ U.datumPoint (ν := ν) (γ j).1 (.act a (γ j).2)
variable {γ} (C : U.GraphClosure γ ν)
lemma isPointOf_datumPoint : U.family.IsPointOf 𝔪 a (datumPoint 𝔪 a).1 := by grind [datumPoint]
lemma IsPt.eq_datumPoint (h : U.family.IsPointOf 𝔪 a u) : u = (datumPoint 𝔪 a).1 :=
  (h.eq_iff isPointOf_datumPoint).2 ⟨1, by simp [ratConj]⟩
lemma datumPoint_eq_iff : U.datumPoint 𝔪 a = datumPoint 𝔪 b ↔ ∃ z, a.IsLevelIso (levelGU _ D.𝔑 ⊓
  levelGU _ 𝔪) z b := OverMorphism.ext_iff.trans (isPointOf_datumPoint.eq_iff isPointOf_datumPoint)
instance : HasProjEmbedding X.A.hom := ⟨X.embeds⟩
instance : HasProjEmbedding (X.fibrePower κ).hom := .pi (𝟙 _)
instance : HasProjEmbedding C.W.hom := .pi C.incl
lemma GraphClosure.exists_level_point_eq : ∃ m : (𝓞 E)⁰, ∀ {a b z}, IsLevelIso (levelGU _ m) z a b →
  C.point a = C.point b := (exists_level_conj_mem D.level_ne_zero (.image γ .univ)).imp fun _ h _ _
  z r ↦ C.hom_ext fun j ↦ by simpa [datumPoint_eq_iff, -act] using
  ⟨z, by simpa [mul_assoc] using h _ (by simp) _ r.mem_level, r.reflection_eq,
  (by simpa using realVecAction_mem_frameLattice (A := 1) (by simpa using (γ j).2.2.2) <|
  r.sub_mem_lattice ·)⟩
lemma fibrePower_spec ν : let Z := (Over.map U.base.hom) (fibrePower (_ ⊕ Fin ν))
  let c : _ → (_ ⟶ Z) := datumPoint 1; SmoothOfRelativeDimension (card D.Index - 1 + ν * abelianDim
    E D.Index) Z.hom ∧ IsDenseFamily (c · |>.1) ∧ ∃ m : _ → _, ∀ g α a, c (.act a g) ≫ m α =
    c (a.act g α) := suffices _ from ⟨Nat.add_comm .. ▸ smoothOfRelativeDimension_comp (hf := this)
    (hg := U.smooth) .., U.dense.of_fibres _ (s := this.smooth) fun a y h ↦ ⟨a.1.ballPoint 0 (_,
    fun i ↦ surjInv (U.model a).uniformisation.surjective ((ThetaObject.isGroupBaseChange
    _).pointEquiv.2 (homMk (y ≫ U.family.proj (.inr i))))), (IsPt.eq_datumPoint ⟨U.model a,
    fibrePower_ext_iff.2 (by simp_all [π, IsGroupBaseChange.pointEquiv, surjInv_eq])⟩).symm⟩,
    fun α ↦ (Over.map _).map (Limits.Pi.map (·.swap.elim α 1 • 𝟙 _)), fun g α a ↦
    isPointOf_datumPoint.rec fun m h ↦ by ext; exact IsPt.eq_datumPoint ⟨by exact m,
    (h =≫ _).trans (congrArg Hom.left (Pi.hom_ext (_ ≫ _) _ (by simp [π, m.equivariant])))⟩⟩
  Exists.elim (by refine ν.rec ⟨⟨Fan.mk (𝟙_ _) nofun, .mk (toUnit ·.1)⟩, ?_⟩ fun m ⟨F, H⟩ ↦
    ⟨⟨_, extendFanIsLimit _ F.2 (tensorProductIsBinaryProduct ..)⟩, ?_⟩ <;> simp [extendFan,
    add_mul, pullback.condition, add_comm] <;> infer_instance) fun F ↦
  (smoothOfRelativeDimension_isStableUnderBaseChange _).1 (.of_horiz_isIso ⟨(Pi.reindex
  (@Equiv.emptySum _ _ ⟨by simp⟩) (fun _ ↦ U.family.A) ≪≫ limit.isoLimitCone F).hom.3⟩)
end UniversalFamily
end
section FoldSeg3
open Matrix _root_.Module ThetaObject AddSubgroup AlgebraicGeometry CategoryTheory FiniteField
  IsGroupBaseChange QuadField NumberField Pic CartesianMonoidalCategory Category Over
lemma UniversalFamily.congruence_step {E k d d₀} [Field E] [CMBase E] {D R} [HasQuadSubfield d₀ E]
  (U : UniversalFamily D R) (hβ : D.β = algebraMap _ _ (c₀ d₀)) {V : ValuationSubring ℂ} {z :
  ModuliPoint E D.Index d} {s} (o : U.family.IsPointOf 1 z s) {w : SplitFinPlace E} [Field k]
  [IsAlgClosed k] {π : V →+* k} (hπ : (⇑π).Surjective) {x₀ : ThetaObject U.family _}
  (b₀ : x₀.IsPullbackAlong (specMap π) (s ≫ hom _)) (hk : w.1.1 = RingHom.ker x₀.baseHom) (hw :
  D.IsGoodAt w.1.1) (hG : IsSafe D.𝔑 w) {l} [Fact l.Prime] [CharP k l] {m α : Submodule .. →
  _} (hq : ∀ A, l ^ m A = w.1.q ^ (D.rank - finrank (ResField w.1) A)) (S : ∀ A,
  U.family.IsPointOf 1 (z.act ⟨_, heckeIsogeny_mem_GUPlus w A⟩ 1) (α A)) : ∃ W ≠ ⊥,
  (fun A ↦ specMap ((iterateFrobenius _ l (m A)).comp π) ≫ α A).FactorsThrough (· ⊔ W) := by
  obtain ⟨⟨e, rfl⟩, _, b, _, _, hb, co, _⟩ := o, hw.2
  choose y' _ _ _ S a using (ThetaFamily.isPointOf_iff .. |>.1 <| S ·)
  choose r ψ _ _ p o s using fun A ↦ e.exists_isogeny 1 (by simp [ratConj, ModuliPoint.act]) (S A)
    (by simp [ModuliPoint.act]) (heckeIsogeny_mem_GUPlus w A).2 isScalarFrame_heckeIsogeny
  choose σ hσ σ₂ _ K L using exists_residue_torsion_emb (n := D.Index) w.1
  have J {C v} := σ₂ ▸ heckeIsogeny_torsionClass C v hβ hG co hb
  have q := by simpa [← hβ,
    ← D.star_beta] using congr(algebraMap _ (𝓞 E) $(absNorm_span_eq_mul_star d₀ (c₀ d₀ - b)))
  simp_rw [hk, pointOf_hom] at hw hb σ₂ b₀
  obtain ⟨⟨_, ⟨_, ⟨t, rfl⟩, T, ht⟩, -⟩, ⟨_, c, h2⟩, i, j⟩ :=
    σ₂ ▸ exists_param_pow_card_eq_zero hw e.fullStructure b₀,
    co.pow (n := m ⊥), by simpa [CharP.intCast_eq_zero_iff] using Ideal.mem_of_dvd _ ⟨_, q⟩ hb
  let μ := l ^ m ⊥
  set υ' := (D.β - b) ^ m ⊥
  choose x hp using (y' · |>.exists_isPullbackAlong _)
  have hM B : l ^ m B * _ = μ := (by simpa [μ, hq] using pow_sub_mul_pow _ B.finrank_le)
  let F B : map (specMap ((iterateFrobenius _ l _).comp π)) ⟶ map (specMap π) := ⟨fun T ↦
    homMk _ (by simpa [specMap] using! (absFrobenius_comm ..).trans (T.3 ≫= comp_absFrobenius (m B)
    (.mk (𝟙 _)) (𝟙 _)) =≫ _), by simp [absFrobenius_comm, OverMorphism.ext_iff]⟩
  choose g Hg lg G using fun B ↦
    b₀.isGroupBaseChange.exists_hom_baseChange (hp B).isGroupBaseChange (F B) (ψ B)
  have cg B : pull (g B).1 (ThetaObject.lineBundle _).picClass = μ • _ := (by
    rw [← hM, mul_nsmul, picClass_pull_absFrobenius _ _ x₀.isProjEmbedding.1,
      (hp B).lineBundle_eq_pull, b₀.lineBundle_eq_pull]
    simpa [← pull_picClass, pull_comp,
      p] using! congr(pull $(Hg B (𝟙 _)).1 (ThetaObject.lineBundle _).picClass))
  have _ B := finite_flat_of_quasiFinite _ (locallyQuasiFinite_of_pull_picClass (isProjEmbedding _)
    NeZero.out (cg B)) ⟨fun z ↦ ((ψ B).1.surjective _).elim fun a e ↦
    (Scheme.exists_preimage_of_isPullback b₀.isGroupBaseChange.1 a _
    (by simpa [specMap, ← (ψ B).w, e, -Over.w] using! congr($((hp B).schemeMap.w) z))
    ).imp fun c k ↦ (IsClosedImmersion.isStableUnderBaseChange.1 (hp B).isGroupBaseChange.1.flip
    (.spec_of_surjective _ ((bijective_iterateFrobenius ..).2.comp hπ))).2.injective
    (by simpa [*, F, absFrobenius_apply, pointEquiv_apply] using congr($(Hg B (𝟙 _)).1 c))⟩
  have Δ C {v} := o C v ▸ map_eq_zero_iff _ (S C).fullStructure.injective
  have κ C x := K x ▸ (Δ C).trans (by erw [L _ (⟨_, (heckeIsogeny_mem_GUPlus w _).2 · ·⟩),
    heckeIsogeny_inv_at_eq_basicCosetRep hG, (basicCosetRep_spec _).2])
  have Z {C v} h : μ • torsionClass v = 0 :=
    (torsionClass_mulVec_eq_zero · ((@Δ C v).1 h)) |> fun H ↦ by
    rw [mulVec_mulVec, gram_inv_of_gram_eq isScalarFrame_heckeIsogeny.2.choose_spec] at H
    rw [← hM, mul_smul, smul_eq_zero_of_right]
    simpa [map_smul', ← map_nsmul, mul_mem, star_mem_Ô,
      (heckeIsogeny_mem_GUPlus w C).2, -coe_units_inv] using! H
  have K {B T} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] {t u} (hu : u ≫ g B = 0) :=
    (e.isRigid_pullback _ b₀).eq_zero_of_pairing_eq_zero (B :=
    T) (id_comp _) (u ≫ (μ • 𝟙 _)) 0 _ (b₀.isGroupBaseChange.pointEquiv.map_eq_zero_iff.1
    (by simpa [eq_zero_iff_factors_zero_section, pointEquiv_apply,
    b₀.isGroupBaseChange.nsmul_id_comp, -comp_nsmul] using! (ker_factors_of_torsionPoint
    e.fullStructure (ψ B) _ (torsionClass_induction (⟨𝟙 _, by simp [← map_nsmul, Hom.zero_def,
    @Z B · ·]⟩)) ((F B).1 (.mk t) ≫ b₀.isGroupBaseChange.pointEquiv u) (by simp [← Hg, hu]))))
    (by simp [← x₀.hasClassLaws.1.nsmul_class_pairing, cg B ▸ pairing_comp _, hu, pairing.eq_1])
  let Φ (A : Submodule (ResField w.1) _) : A →+ _ := .mk' (toUnit ((map (specMap π)) (specOver k
    k)) ≫ e.fullStructure.torsionPoint.comp σ ·.1) (by simp)
  have M A o : l ^ m A * .card (Φ A ⁻¹' {o}) = ite (o ∈ (Φ A).range) (μ / .card (Φ A).range) 0 := by
    split_ifs with h
    rw [← h.choose_spec, Nat.card_congr ((Φ A).fiberEquivKer _), ← hM A, ← card_ResField,
      ← index_ker, ← natCard_eq_pow_finrank, ← (Φ A).ker.card_mul_index]
    simp [← mul_assoc, index_ne_zero_of_finite]
    simp [Set.preimage_singleton_eq_empty.2 h]
  have Y {N} [AddCommGroup N] [Module (𝓞 E) N] {s : N} (h :
    μ • s = 0) := by simpa [← mul_comm i, j,
    (mod_cast h : (l : 𝓞 E) ^ m ⊥ • s = 0), mul_pow, mul_smul] using congr($q ^ m ⊥ • s).symm
  choose ν _ W using fun {A A'} (h : (Φ A').range = _) ↦
    exists_factor_through_isogeny (g A) _ fun B ↦ fun u hu ↦ by
    have H C := (exists_ker_parameter e.fullStructure b₀ hb co _ _ (Y (by
      simpa using congr(b₀.isGroupBaseChange.pointEquiv $(K hu)))) (nullstellensatz_exists_le_ker
      bot_ne_top).choose).choose_spec.2 (ψ C) ⟨_, hσ.injOn.injective.codRestrict
      fun x : C ↦ σ₂.le ⟨x, rfl⟩⟩ _ ((F C).1 (specOver k B)) (comp_absFrobenius _ (.mk _) (𝟙 _))
    simpa [← Hg, ← map_smul, ← ModuleObj.comp_smul, κ] using ((H A').2 · <| by erw [← pow_mul, M, h,
      ← M, pow_mul, (H A).1 _ _ rfl (torsionClass_induction fun v g ↦ Subtype.exists.2 <| by
     apply (J.2 _ (Y (Z g)) ((Δ A).1 _)).imp <;> simp +contextual [← κ, g]) (by simp [← Hg, hu])])
  have P {A B j} (a : 𝓞 E) (h : g A ≫ j = a • g B) := pairing_eq_of_fpqc_cover (.id_horiz _) (g A)
    (a • 𝟙 _) (g A) j (g B) (by simp [h, ← IsLinear.smul_comp, ← pairing_comp]; rw [cg, cg]; simp)
  use _ ∙ t, T ∘ by simp +contextual, fun A' A h ↦ ?_
  have hN : (Φ A').range = (Φ A).range := by simpa [Φ, SetLike.ext_iff, ht,
    Submodule.mem_span_singleton,
    (algebraMap_ResField_surjective _).exists] using congr((Φ $h).range)
  obtain ⟨j, _, hj⟩ := exists_factor_through_isogeny (g A') _ fun T ↦ fun y hy ↦ by
    simpa [add_smul, mul_smul, ← W hN.symm, reassoc_of% hy, ((S A).isRigid_pullback _ (hp
      A)).eq_zero_of_pairing_eq_zero (id_comp _) (y ≫ (υ' • g A)) _ (𝟙 _) (by simpa using _ ≫= K hy
      =≫ (υ' • g A)) fun _ i ↦ by simpa [pairing_comm _ (i ≫ _), pairing.eq_1 _ _ 0, υ', hy,
      pairing_pow_smul_adjoint] using (P _ (W hN) · (i ≫ y))] using congr(y ≫ ($h2 • g A)).symm
  open Fint in have ⟨t, q⟩ := ((S _).isRigid_pullback _ (hp _)).eq_of_hom (id_comp _) (by
    ext a; simpa [(hp _).baseHom_eq_comp, iterateFrobenius, ← card_ResField, r,
      ← algebraMap_ResField_eq_zero, b₀.baseHom_eq_comp, pow_card_pow, hq] using
      (congr(a ^ l ^ m A' - a ^ l ^ m A ∈ $hk))) j (hl := ⟨((epi_of_epi_left _).1 _ _ <| by
    simpa [← assoc, ← hj] using (lg A).2 ·)⟩) (pairing_eq_of_fpqc_cover (.id_horiz _) (g _) (𝟙
    _) (𝟙 _) j j (by simp [pairing_comm, hj, by simpa using P 1 (by simpa)])) (Subtype.forall.2
    (torsionClass_induction fun v h ↦ by simp [(hp _).levelPoints_eq_pullSection,
    (S _).fullStructure.eta_eq, ← G, hj, ← J.1 h ▸ o _ v]))
  simp [fibrePower_ext_iff, a, ModuliPoint.act, ↓← by simpa using s, -comp_left, ← comp_left_assoc,
    ← (hp _).isGroupBaseChange.pullSection_comp_assoc, ← G, (hp _).comp_toFamily, ← q, hj, hp, t]
end FoldSeg3
section FoldSeg4
noncomputable section
open CategoryTheory AlgebraicGeometry TrivSqZeroExt ThetaObject Obj IsGroupBaseChange CommRingCat
  DualNumber Module Dual Spec Over OverMorphism RingHom Algebra
variable {E k M} [Field E] [CMBase E] {D : PEL E} [Field k] {Z σ} [AddCommGroup M] [Module k M] {X :
  ThetaFamily D Z σ} {x₀ : ThetaObject X _} {x} (hp : IsPullbackAlong (sqZeroReduction k (M →ₗ[k]
  k)) x₀ x) ⦃C : Type⦄ {C'} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] (φ : C →ₐ[k] C')
instance : CommRing (TrivSqZeroExt C (M →ₗ[k] C)) := inferInstance
instance : IsLocalRing (TrivSqZeroExt k (M →ₗ[k] k)) :=
  .of_nonunits_add (by simp_all [isUnit_iff_isUnit_fst])
attribute [-simp] smul_eq_zero
attribute [local simp ←] Spec.map_comp map_comp_assoc ofHom_comp AlgHom.comp_toRingHom smul_smul
  map_smul
attribute [local simp↓] map_inj lift_def algebraMap_eq_inl'
@[simps] def sqZeroMap : TrivSqZeroExt C (M →ₗ[k] C) →+* TrivSqZeroExt C' (M →ₗ[k] C') := by
  refine' {toFun x := inl (φ x.fst) + inr (φ ∘ₗ x.snd), ..} <;> aesop
variable (C) in
def toSqZeroSpec : map (sqZeroReduction k (M →ₗ[k] k)) (specOver k C) ⟶ .mk (specMap
  (sqZeroMap (ofId k C))) := homMk (sqZeroReduction ..)
lemma exists_point_lift [IsLocalRing C] y : ∃ Z, toSqZeroSpec C ≫ Z =
  hp.isGroupBaseChange.pointEquiv y :=
  let ⟨_, _, i, L⟩ := exists_isEtaleChart _ x.smoothOfRelativeDimension
  (L _ (inl ∘ _) (landsIn_iff_mem.2 i) ((Over.w _).trans (toSqZeroSpec C).w.symm) rfl).imp fun _ ↦
    (ext ·.1.1)
def sqZeroSpecMap : Over.mk (specMap (sqZeroMap (ofId k C'))) ⟶ .mk
  (specMap (sqZeroMap (M := M) (ofId k C))) := homMk (specMap (sqZeroMap φ))
lemma sqZeroSpecMap_point_lift {y Z} (e : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y) :
  toSqZeroSpec _ ≫ sqZeroSpecMap φ ≫ Z = hp.isGroupBaseChange.pointEquiv (specOver.map φ ≫ y) := by
  simp [pointEquiv_apply] at *; ext; simp [← e, toSqZeroSpec, sqZeroSpecMap,
    specOver.map]; congr 2; aesop
lemma isInfinitesimal_of_comp_eq_zero (Z : _ ⟶ x.groupScheme) : toSqZeroSpec C ≫ Z = 0 →
  IsInfinitesimal (ofHom (fstHom C ..).1) Z := by
  simp [IsInfinitesimal, ↓eq_zero_iff_factors_zero_section]; tauto
include hp in
lemma tangent_bound [IsAlgClosed k] (hw : D.IsGoodAt (ker x₀.baseHom)) {V : ValuationSubring ℂ} {w}
  (e : FullStructure w) (hr : x₀.IsRigid) {χ : V →+* k} (h₀ : x₀.IsPullbackAlong (specMap χ) w)
  (hρ : x.baseHom = (algebraMap ..).comp x₀.baseHom) (h : ∀ l, specMap (map (eval k M l)).1 ≫ x =
  specMap (algebraMap ..) ≫ x₀ → l = 0) : finrank k M ≤ Fintype.card D.Index - 1 := by
  obtain ⟨_, ⟨-, c, hc, hc0, t, ht, H⟩, b, hb, ⟨_, _, co⟩, hN⟩ := isGoodAt_ker_spec hw
  choose ω L Q A F P using by simpa [hρ] using x.exists_tangent_log (b := b) (by simp [*])
  choose Y J using exists_point_lift hp
  choose N hL using fun {C} [CommRing C] [Algebra k C] [IsLocalRing C] (y : placeTorsion x₀ C) ↦
    have N := isInfinitesimal_of_comp_eq_zero (c • Y y.1) (y.rec (by simp_all))
    have hL Z (e : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv
      y := by simp [J]) := have n := isInfinitesimal_of_comp_eq_zero (Z - Y y.1) (by
        simp [*]); by simpa [← smul_add, L n, hc] using (A (n.smul c) N).symm
    And.intro N @hL
  refine finrank_le_of_placeTorsion hw h₀ e (fun _ ↦ ⟨⟨(snd <| ω <| c • Y ·.1), fun y
    z ↦ by simp [↓hL (y + z) (Y y + Y z), A (N y) (N z)]⟩, fun a y ↦ by simp [↓hL (a • y) (a • Y y),
    smul_comm c, L (N y)]⟩) (fun φ y ↦ by simp [hL (placeTorsionMap φ y) _ (sqZeroSpecMap_point_lift
    hp φ (J _)), ← ModuleObj.comp_smul, P (N y) (sqZeroSpecMap φ) rfl]) (fun y u ↦ by simp [hc, (hL
    y (Y y - sqZeroSpecMap (.comp (ofId ..) (fstHom ..)) ≫ Y y.1) (by simp [sqZeroSpecMap_point_lift
    hp, ← specOver.map_comp_assoc, *])).trans (@L _ _ (ofHom (sqZeroMap (fstHom ..))) ⟨(⟨sqZeroMap
    (ofId ..) ·, by ext <;> simp⟩), by simp +contextual [TrivSqZeroExt.ext_iff, DFunLike.ext_iff]⟩ _
    _ (by simp [IsInfinitesimal, OverMorphism.ext_iff, sqZeroSpecMap]; congr; ext <;> simp) c)])
    fun l hl ↦ ?_
  let m := specMap (map (eval k M l)).1
  obtain ⟨⟨z, hz⟩, z₀, hz'⟩ := x.exists_isPullbackAlong m,
    x₀.exists_isPullbackAlong (specMap (algebraMap _ k[ε]))
  obtain ⟨o, hq, hq₀⟩ := by simpa [hρ, ← comp_assoc] using hz.baseHom_eq_comp,
    (by simpa [m, ← hz, IsPullbackAlong] using! hp : IsPullbackAlong (sqZeroReduction ..) x₀ z),
    (by simp [← hz', IsPullbackAlong] : IsPullbackAlong (sqZeroReduction ..) x₀ z₀)
  choose G _ u K using drinfeld_lift hq₀ hq fun _ _ ↦ (·.ringChar_smul_and_smul_eq_zero.2 o hb hc)
  choose f _ g using exists_lift_of_kills_ker (hq' := hq₀) (c • 𝟙 _) (by simp) hc0 _ _ _ u fun C ↦
    fun y hy _ ↦ by
    algebraize [(algebraMap _ C).comp (inlHom k k)]
    let χ := (liftEquivOfComm (A := C) ⟨(ε : k[ε]) • .applyₗ' (R := k) C l, by simp [smul_smul]⟩).1
    let d : (map m) (specOver ..) ⟶ .mk (specMap (sqZeroMap (ofId ..))) :=
      homMk (specMap χ) (homEquiv.injective
      (by ext; simp [m, χ, TrivSqZeroExt.map, smul_def, algebraMap_toAlgebra, mul_comm]))
    let v : specOver k C ⟶ _ := homMk (V := (Over.map _).obj (specOver k[ε] C)) (𝟙 (Spec _))
      (by simp) ≫ hz'.isGroupBaseChange.pointEquiv y
    obtain ⟨⟨_, ψ, _, -, _, e, U⟩, hy⟩ := exists_isSqZeroExt_mod_eps (specOver k[ε] C).hom,
      show c • v = 0 by simpa [map_smul] using congr(_ ≫ hz'.isGroupBaseChange.pointEquiv $hy)
    obtain ⟨a, n⟩ := show ofHom χ ≫ ψ = ofHom (fstHom C ..).1 ≫ ψ by ext; simp [χ, smul_def, e,
      -map_mul], isInfinitesimal_of_comp_eq_zero (c • Y v) (by simp [*])
    refine (K _ (hz.isGroupBaseChange.pointEquiv.symm (d ≫ Y v)) y fun _ _ s ↦ (U s.w).rec fun s'
      g ↦ by ext; simpa [← g, hp.comp_toFamily, hz'.comp_toFamily, ← hz.comp_toFamily, d, v,
      toSqZeroSpec, a, pointEquiv] using (s' ≫= map ψ ≫= congr($(J v).1 ≫ x.toFamily.1))
      ).trans (hz.isGroupBaseChange.pointEquiv.injective ?_)
    simpa using Q (n.precomp d rfl _ a) (by simpa [↓P n d rfl, by simpa [smul_comm c, L n,
      ((sub_mem_ker_iff _).1 ht)] using (congr(snd $(hL ⟨t • v, by simpa using ((Ideal.torsionOf _
           _ v).span_singleton_le_iff_mem.2 hy <| H ⟨·, ·, mul_comm ..⟩)⟩ (t • Y v)) l).symm.trans
           (@hl _ _ _ _ (.trans k[ε] C) _)), χ] using F n)
  choose μ _ g using exists_lift_of_kills_ker f g (by simpa [·, hb] using congr(x₀.baseHom $co)) hq₀
    ((star D.β - b) • 𝟙 _) 1 (by simp) fun _ ↦ fun y h K ↦ by simpa [add_smul, K,
    (hr.eq_zero_of_pairing_eq_zero hz' ((D.β - b) • (star D.β - b) • y) 1 (𝟙 _) (by simp [smul_comm
    _ (D.β - _), AgreeModEps.ringChar_smul_and_smul_eq_zero hq₀, *,
    isLinear_and_pairing_eq_of_reduction f g]) fun _ t w ↦ by
    simpa [h, Pic.pairing.eq_1 _ 0, by simpa using (z₀.pairing_pow_smul_adjoint b 1 · w)] using
      ((isLinear_and_pairing_eq_of_reduction f g).2.2 hz' (t ≫ y) w).symm)] using congr($co • (star
    D.β - b) • y).symm
  choose μ _ g using exists_lift_of_kills_ker μ g (by simp) hq (𝟙 _) 1 (by simp) (by simp)
  obtain ⟨_, -, N⟩ := isLinear_and_pairing_eq_of_reduction _ g
  refine h l (hz ▸ hz' ▸ (hr.eq_of_hom hz' (o ▸ hz'.baseHom_eq_comp) μ (by simp [N hz']) fun l ↦
    eq_of_sub_eq_zero ((Ideal.torsionOf_eq_top_iff ..).1 (eq_top_mono (sup_le (by simp [smul_sub,
    ← IsLinear.smul_comp, (Subtype.ext l.2 : D.𝔑 • l = 0)]) ?_) hN))).1.symm)
  have K := AgreeModEps.ringChar_smul_and_smul_eq_zero hq (y := z₀.levelPoints l ≫ μ - z.levelPoints
    l) fun _ _ t ↦ by simp [hq.levelPoints_eq_pullSection, ← hq₀.levelPoints_eq_pullSection,
    g, OverMorphism.ext_iff, by simpa using t.w, ← hq.isGroupBaseChange.pullSection_comp,
    ← hq₀.isGroupBaseChange.pullSection_comp_assoc, ← comp_left _ _ _ hq₀.schemeMap]
  simpa [mul_comm (ker _), smul_comm (ringChar k), Ideal.span_insert, Ideal.sup_mul,
    Ideal.span_singleton_mul_le_iff, Nat.cast_smul_eq_nsmul, K] using (@K.2 _ o _ · hb)
end
end FoldSeg4
noncomputable section
open Complex ComplexConjugate QuotientAddGroup LinearMap LinearEquiv NeZero Algebra.IsAlgebraic
variable {V R : Type} [FinComplexSpace V] [CommRing R] [StarRing R] (L : Submodule ℤ V) (B :
  LatticeForm L) (F : R →+* V →L[ℂ] V) (β : R) [IsDomain R] [Module.Finite ℤ R]
structure IsHermitianAction where
  map_mem a : ∀ l ∈ L, F a l ∈ L
  conj_symm x y : B x y = conj (B y x)
  pos : ∀ x ≠ 0, 0 < (B x x).re
  adjoint a x y : B (F a x) y = B x (F (star a) y)
  riemannForm_integral : ∀ᵉ (l ∈ L) (m ∈ L), ∃ n : ℤ, B.riemannForm l m = n
  star_eq_one_sub : star β = 1 - β
variable {L} {B} {F} {β} {x : V} {y : V} {f : V → ℂ} (h : IsHermitianAction L B F β) (a : R)
  [NeZero a]
instance : NeZero (star a) := ⟨by simp [ne]⟩
omit [StarRing R] [IsDomain R] [Module.Finite ℤ R] in
lemma action_comm r s x : F r (F s x) = F s (F r x) := congr($((Commute.all ..).map F) _)
omit [StarRing R] in
lemma action_injective : (⇑(F a)).Injective := (exists_smul_eq_mul ℤ 1 (ne a)).elim fun b ⟨_, r,
  e⟩ x y k ↦ by simpa [k, r, action_comm a, ← Int.cast_smul_eq_zsmul ℂ] using congr(F $e x = F $e y)
omit [StarRing R] in
@[simp] lemma action_isInvertible : (F a).IsInvertible :=
  ⟨(ofInjectiveEndo _ (action_injective a)).toContinuousLinearEquiv, rfl⟩
namespace IsHermitianAction
@[simp] abbrev multiplier (_ : IsHermitianAction L B F β) := canonicalMultiplier B (F β)
@[simp] abbrev normShift (_ : IsHermitianAction L B F β) := normalizedShift B (F β)
def divLattice (_ : IsHermitianAction L B F β) a := L.toAddSubgroup.comap (F a).toAddMonoidHom
abbrev MulKernel := _ ⧸ L.toAddSubgroup.addSubgroupOf (h.divLattice a)
omit [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
@[simp] lemma map_divLattice_mem (z : h.divLattice a) : F a z ∈ L := z.2
omit [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
lemma out_mem_iff_eq_zero (z : h.MulKernel a) : z.out.1 ∈ L ↔ z = 0 :=
  (out_eq' z ▸ eq_zero_iff _).symm
include h
section
omit [IsDomain R] [Module.Finite ℤ R]
lemma riemannForm_beta u w : B.riemannForm (F β u) w =
  B.riemannForm u w - B.riemannForm u (F β w) := by simp [riemannForm, h.4, h.6]; ring
lemma isAppellHumbert : IsAppellHumbert B h.multiplier := by grind
  [isAppellHumbert_canonicalMultiplier, riemannForm_beta, IsHermitianAction, conj_re]
lemma riemannPhase_eq_one {a} (hx : x ∈ B.dualLattice) (hy : F (star a) y ∈ L) :
  B.riemannPhase (F a x) y = 1 :=
  by grind [hx _ hy, riemannForm_def, IsHermitianAction, Circle.coe_eq_one, fourierChar_eq_one]
lemma multiplier_eq_exp : h.multiplier x = exp (B x (F (star β) x) - B x x / 2) := by grind
  [canonicalMultiplier, h.isAppellHumbert.sub_eq_riemannForm, IsHermitianAction]
lemma nsmul {m} (hm : m ≠ 0) : IsHermitianAction L (m • B) F β := by use h.1, ?_, ?_, ?_,
  (h.isAppellHumbert.nsmul _).le_dualLattice, h.6 <;> simp_all [← h.2, hm.pos, h.3, h.4]
end
variable [IsFullRankLattice L]
lemma card_mulKernel : Nat.card (h.MulKernel a) = (F a).det * conj (F a).det :=
  relIndex_comap_lattice (h.1 a) (action_injective a)
instance : Fintype (h.MulKernel a) := AddSubgroup.fintypeOfIndexNeZero (ne_of_apply_ne _
  ((h.card_mulKernel a).trans_ne (by simp [det_eq_zero_iff_ker_ne_bot, ker_eq_bot,
  action_injective])))
lemma normShift_sum_eq_char_smul (hf : ∀ l ∈ L, h.normShift (F a l) f = f) (ξ :
  AddChar (h.MulKernel a) ℂ) (y : h.divLattice a) {s}
  (hs : s = ∑ k, ξ (-k) • h.normShift (F a k.out) f) : h.normShift (F a y) s = ξ y • s := by
  rw [hs, map_sum, Finset.smul_sum, Fintype.sum_equiv (.addLeft ↑y)]
  intro k; have ⟨l, e⟩ := mk_out_eq_add (L.toAddSubgroup.addSubgroupOf _) (y + k.out)
  nth_rw 1 [← hf _ l.2]
  simp_all [h.isAppellHumbert.normalizedShift_normalizedShift h.riemannForm_beta,
    ↓h.riemannPhase_eq_one (h.5 _ _) (h.1 ..), smul_smul, ← ξ.map_add_eq_mul, add_mem, add_assoc]
end IsHermitianAction
end
namespace IsHermitianAction
open Complex ComplexConjugate Matrix Module MeasureTheory ComplexOrder QuotientAddGroup Fintype
variable {V R} [FinComplexSpace V] [CommRing R] [StarRing R] {L : Submodule ℤ V} {B F} {β :
  R} (h : IsHermitianAction L B F β) {x y}
lemma gauss_sum_pow_four_real [IsFullRankLattice L] [IsDomain R] [Module.Finite ℤ R]
    {κ r} [NeZero κ] (q : h.MulKernel κ → ℂ) (H : ∀ x : h.divLattice κ,
  q x = exp (B x (F r x))) : (∑ z, conj (q z)) ^ 4 = (∑ z, q z) ^ 4 := by
  choose a b c d e using (card (h.MulKernel κ) ^ 2 - 1).sum_four_squares
  let M := !![(a : ℤ), b, c, d; -b, a, -d, c; -c, d, a, -b; -d, -c, b, a]
  have T : ∀ {z}, 1 = q z ^ card (h.MulKernel κ) ^ 2 := by simpa [forall_mk, H, ← mk_zero,
          ← exp_nsmul, pow_mul, sq] using (H <| card (h.MulKernel κ) • ·)
  simp [sum_pow, inv_eq_of_mul_eq_one_left (T ▸ pow_sub_one_mul ..), ← inv_eq_conj,
    norm_eq_one_of_pow_eq_one T.symm]
  refine Finset.sum_bijective (M • ·) (Finite.surjective_iff_bijective.1 fun p ↦ ⟨-Mᵀ • p, by
    linear_combination (norm := (ext j; fin_cases j <;> simp [M, Fin.sum_univ_four, sq, sub_nsmul,
    NeZero.one_le, mul_smul] <;> module)) -e • p⟩) (by simp) (mk_surjective.comp_left.forall.2 ?_)
  simp [← mk_zsmul, ← mk_add, H, ← e, ← exp_nsmul, ← exp_sum, M, Fin.sum_univ_four]
  grind
include h
lemma exp_eq_of_mem_lattice {s t} : x ∈ L → y ∈ L → s = t + B x y - B y x → exp s = exp t := by
  grind [exp_eq_exp_iff_exists_int, IsHermitianAction, h.isAppellHumbert.sub_eq_riemannForm,
    ofReal_intCast]
lemma poincareSeries_add l (hl : l ∈ L) : h.isAppellHumbert.poincareSeries (x + l) y =
  (h.multiplier l)⁻¹ * exp (-(B l x + B l l / 2)) * h.isAppellHumbert.poincareSeries x y :=
  ((Equiv.addRight ⟨l, hl⟩).tsum_eq _).symm.trans ((tsum_congr (by
  simp [IsAppellHumbert.poincareTerm, h.isAppellHumbert.3, *, ← exp_add,
    field]; grind [h.isAppellHumbert.sub_eq_riemannForm])).trans tsum_mul_left)
variable [IsFullRankLattice L]
lemma isContPeriodic_poincareSeries a w : IsContPeriodic L.toAddSubgroup fun x ↦
  h.isAppellHumbert.poincareSeries (F (star a) (x + w)) (F a (x + w)) :=
  (h.isAppellHumbert.poincareSeries_spec h.3).2.elim fun _ A ↦
  ⟨by fun_prop, by simp_all [add_rotate _ _ w, poincareSeries_add,
  (A.1 _).2, multiplier_eq_exp, action_comm, h.4, h.1, exp_neg, exp_add, field]⟩
lemma isSelfAdjoint_quotMean_pow [IsDomain R] [Module.Finite ℤ R]
    c {κ} [NeZero κ] (k : κ = c - star c) :
  IsSelfAdjoint ((quotMean L.toAddSubgroup (fun x ↦
  h.isAppellHumbert.poincareSeries (F (star c) x) (F c x)) * conj (F (star c)).det) ^ 4) := by
  borelize V
  obtain ⟨b, _⟩ := finBasis ℂ V, ‹IsFullRankLattice L›.1
  let e := b.equivFun.symm.toContinuousLinearEquiv
  let M a := (.pi (B <| b ·) ∘ₗ (F a).1 ∘ₗ e.1.1).toMatrix'
  have Mt a : (M a)ᴴ = M (star a) := ext (by simp [M, e, ← h.2, h.4])
  have X a x : star x ⬝ᵥ M a *ᵥ x = conj (B (F a (e x)) (e x)) := by simp [M, e, dotProduct, ← h.2]
  have P := PosDef.of_dotProduct_mulVec_pos (M (κ * star c))ᴴ.isHermitian_add_transpose_self fun x
    _ ↦ (zero_lt_real.2 (h.3 (F κ (e x)) (by simpa [map_eq_zero_iff, action_injective]))).trans_eq
    (by simp [re_eq_add_conj, h.4, ← h.2, *]; ring)
  let g a x := (B x (F (κ * a) x)).exp
  have I : ∫ x, g c x ∂(realMeasure _).map e = _ := .trans
    (by simp (disch := fun_prop) [integral_map, g, ← h.2, *]) (integral_gauss P 0)
  let a := star β * κ - c
  obtain ⟨n, _, D⟩ := IsAccretive.det_ne_zero P, isFiniteMeasure_addOrbitMeasure
    ((realMeasure _).map e) (isCocompact_of_isFullRankLattice (L := L)),
    congr(($((ext (by simp [↓Mt, M, k]) : (M κ)ᴴ = -M κ)) ^ 4).det)
  norm_num [(.trans (ext (by simp [M, e])) (LinearMap.toMatrix'_mul ..) :
    M (κ * star c) = M κ * (F (star c)).toMatrix b b)] at n D I; have i z :=
    ((Integrable.of_integral_ne_zero (I.trans_ne (by simp_all))).comp_add_right z).const_mul
  have H (x : h.divLattice κ) y (l : x.1 - y ∈ L) : g a x = g a y := h.exp_eq_of_mem_lattice l (h.1
    a _ (sub_mem x.2 (h.1 (β * κ) _ l))) (by simp [a, k, h.4, action_comm, h.6]; ring)
  erw [IsSelfAdjoint, quotMean_tsum_eq_integral _ _ (integrable_finsetSum _ fun z _ ↦ i z.out (g a
    z.out)) (by simpa using! h.isContPeriodic_poincareSeries c 0) fun x ↦
    ((((preimageMkEquivAddSubgroupProdSet ..).trans (.prodCongr (AddSubgroup.addSubgroupOfEquivOfLe
    (h.1 κ)).1 (Equiv.Set.univ _))).symm.trans ((Equiv.Set.univ _).trans
    (LinearEquiv.ofInjectiveEndo _ (action_injective κ)).subtypeEquivOfSubtype) : _ × h.MulKernel
    κ ≃ L).hasSum_iff.2 ((h.isAppellHumbert.poincareSeries_spec h.3).1 ..).hasSum).prod_fiberwise
    fun l ↦ (hasSum_fintype _).congr_fun fun z ↦ show h.isAppellHumbert.poincareTerm _ _
    ⟨F κ (_ + l), _⟩ = _ by simp [↓H _ (z.out + l), g, a, action_comm, exp_add, multiplier_eq_exp,
    exp_sub, *, h.4, IsAppellHumbert.poincareTerm, AddSubgroup.vadd_def, field]]
  simp [integral_finsetSum, integral_add_right_eq_self, ← Finset.sum_mul, *, -k, field,
    h.gauss_sum_pow_four_real (g a ·.out) (H _ · (eq_iff_sub_mem.1 (out_eq' (_ : h.MulKernel κ))))]
end IsHermitianAction
namespace IsHermitianAction
open MeasureTheory Complex NNReal Function Finset LinearMap Ideal Filter FiniteDimensional
variable {V R} [FinComplexSpace V] [CommRing R] [StarRing R] {L :
  Submodule ℤ V} {B F f} {β c d : R} (h :
  IsHermitianAction L B F β) {v} [NeZero c] [NeZero d] {A : LatticeForm L}
abbrev torsionAction (a : R) (x : torsionPoints L) : torsionPoints L :=
  ⟨F a x, x.2.imp (by grind [IsHermitianAction])⟩
include h
lemma normShift_comm x y : h.normShift x (h.normShift y f) = B.riemannPhase x y • h.normShift y
  (h.normShift x f) := by simp [normalizedShift, h.isAppellHumbert.thetaShift_comm x]; module
lemma multiplier_sq l (k : l ∈ L) : h.multiplier l ^ 2 = 1 :=
  h.isAppellHumbert.exp_riemannForm_pow_eq_one (nsmul_mem (h.1 _ l k) 1) (nsmul_mem k 1)
lemma isAmpleType : IsAmpleType B h.multiplier :=
  ⟨h.isAppellHumbert, isPosRiemann_of_re_pos h.3, 2, nofun, h.multiplier_sq⟩
attribute [local simp] funLeft canonicalMultiplier out_mem_iff_eq_zero thetaShift_apply mul_smul
  add_mem
lemma sizeAt_add x w : B.sizeAt v f (x + w) = v (h.normShift x (h.normShift w f) 0) := by
  simp [↓← h.isAppellHumbert.sizeAt_thetaShift, normalizedShift, LatticeForm.sizeAt,
    h.isAppellHumbert.valuation_exp_riemannForm (h.torsionAction ..)]
lemma sizeAt_eq_normShift x : B.sizeAt v f x =
  v (h.normShift x f 0) := by simpa [normalizedShift] using h.sizeAt_add x 0
variable [IsDomain R] [IsFullRankLattice L] [Module.Finite ℤ R]
lemma mem_torsionPoints (a : h.divLattice c) : ↑a ∈ torsionPoints L :=
  ⟨_, Nat.card_pos.ne', L.toAddSubgroup.nsmul_relIndex_mem a.2⟩
lemma torsionAction_surjective c [NeZero c] :
  Surjective (h.torsionAction c) | ⟨y, n, _⟩ => ⟨⟨(F c).inverse y, (h.mem_torsionPoints (c :=
  c) ⟨n • (F c).inverse y, by simp_all [divLattice]⟩).imp' (· * n) (by aesop)⟩, by aesop⟩
variable {w : torsionPoints L} (hd : star c = d) (h1 : ∀ a ∈ B.dualLattice, F c a - a ∈ L ∧
  F d a - a ∈ L)
omit [NeZero d] [IsFullRankLattice L] in
include hd in lemma normShift_map_eq_map_star w f : h.normShift (F d w) (f ∘ F c ∘ (F d).inverse) =
    h.normShift (F c w) f ∘ F c ∘ (F d).inverse := by ext; simp [normalizedShift, riemannForm, h.4,
  action_comm, ← hd]
include hd h1
lemma exists_sum_normShift_eq_smul : ∃ μ, ∑ _ : h.MulKernel d, quotMean L.toAddSubgroup (fun x ↦
  h.isAppellHumbert.poincareSeries (F d x) (F c x)) = μ ∧ ∀ t ∈ B.thetaSpace h.multiplier,
  (∑ z : h.MulKernel d, h.normShift (F d z.out)) (t ∘ F c ∘ (F d).inverse) = μ • t := by
  let Q := (∑ z : h.MulKernel d, h.normShift (F d z.out)) ∘ₗ funLeft ℂ ℂ (F c ∘ (F d).inverse)
  obtain ⟨rfl, _, _, μ, H⟩ := hd, h.isAppellHumbert.poincareSeries_spec h.3,
    quotMean_comp L.toAddSubgroup (F d) (h.isContPeriodic_poincareSeries 1 0) (h.1 d)
    (action_isInvertible d).surjective, h.isAppellHumbert.schur_lemma (hp := h.isAmpleType.2) (Q :=
    Q.restrict fun t ⟨_, _⟩ ↦ mem_thetaSpace_iff_normalizedShift.2
    ⟨by simp [Q, normalizedShift]; fun_prop, (action_isInvertible d).surjective.forall.2 (by
    simpa [Q] using h.normShift_sum_eq_char_smul d (by grind [mem_thetaSpace_iff_normalizedShift,
      map_mem, normShift_map_eq_map_star]) 1 ⟨·, ·⟩ rfl)⟩) fun ⟨a, ha⟩ ↦ by
    have o y (e : y - a ∈ L) (f : B.thetaSpace h.multiplier) := by
      simpa [h.isAppellHumbert.normalizedShift_normalizedShift h.riemannForm_beta,
        h.riemannPhase_eq_one, h.1, *, -map_sub] using
        congr(h.normShift a $((mem_thetaSpace_iff_normalizedShift.1 f.2).2 _ e))
    exact ext fun f ↦ Subtype.ext (smul_right_injective _ (by simp) (map_smul Q .. ▸ (by simp [Q,
      normShift_comm, h.normShift_map_eq_map_star hd a, h.riemannPhase_eq_one, h.1, *] :
      Q (h.normShift a f) = _).trans (o _ (h1 a ha).2 _))).symm
  have K t ht x := by simpa [Q] using congr(($H ⟨t, ht⟩).1 (F (star c) x))
  exact ⟨_, ((integral_finsetSum _ fun z _ ↦ (h.isContPeriodic_poincareSeries c
    z.out).integrable_out).trans (sum_congr rfl fun _ _ ↦ quotMean_translate (by
    simpa using h.isContPeriodic_poincareSeries c 0) _)).symm.trans (by simp_all [normalizedShift,
    poincareSeries_add, mul_assoc, quotMean]), fun t ht ↦ congr(($H ⟨t, ht⟩))⟩
lemma hasShiftBound_one_of_ker [NeZero (c - d)] {p n : ℕ} (pp : p.Prime) (hv : v p < 1) (N :
  v (F d).1.det = 1) (o : IsPosRiemann (B + -A)) (b : F c w ∈ L) : IsCoprime c d → p ^ n • w.1 ∈ L →
  A.HasShiftBound v w 1 := fun ⟨_, γ, s⟩ T ↦ .of_isPosRiemann_sub h.isAmpleType o fun f hf _ ↦ by
  obtain ⟨rfl, ⟨μ, M, H⟩, ⟨_, rfl, G⟩, ⟨t, ht, x, X⟩, R, D, P, a, hφ⟩ := hd,
    h.exists_sum_normShift_eq_smul hd h1, h.exists_sum_normShift_eq_smul (hd ▸ star_star c)
    (by aesop), by simpa [funext_iff] using h.isAppellHumbert.exists_theta_ne_zero (hp :=
    h.isAmpleType.2), (h.isSelfAdjoint_quotMean_pow c (by rw [hd])).star_eq, h.card_mulKernel d,
    pow_ne_zero n pp.ne_zero, fun {z : h.MulKernel d} ↦ action_comm
    c _ z.out.1 ▸ h.1 c _ z.out.2, LatticeForm.sizes.of_mem_thetaSpace (v := v) h.isAmpleType hf
  have r {ζ : ℂ} (k : ζ ^ p ^ n = 1) := by simpa [k, Algebra.algebraMap_ofSubring] using
    (Valuation.integer.integers v).le_of_dvd ⟨_, sub_eq_of_eq_add' (add_pow_prime_pow_eq' pp 1
    (⟨ζ, (valuation_eq_one_of_pow_eq_one P k).le⟩ - 1 : v.integer) n)⟩
  have E := by simpa [↓smul_smul, ← H _ ht,
    h.normShift_map_eq_map_star] using congr($(G _ (Submodule.smul_mem _ μ ht)) x)
  erw [sum_comm, Fintype.sum_eq_single 0 fun z ↦ (by_contra fun k ↦ · ?_), funext fun x ↦
    (tsum_congr fun l ↦ ?_).trans
    (tsum_comp_neg (star (h.isAppellHumbert.poincareTerm (F (star c) x) (F c x))))] at E
  simp [mem_thetaSpace_iff_normalizedShift.1 ht, h.1, quotMean, ← integral_conj,
    IsAppellHumbert.poincareSeries, conj_tsum, field] at E R D M
  grw [size_le_iSup hφ, one_mul, ← le_sqrt_iff_sq_le, le_of_not_gt fun o ↦ (max_lt o
    (mul_lt_of_lt_one_left o.pos ((powOrderIso _ P).symm_apply_lt.2 ((one_pow _).trans_gt hv)))
    ).not_ge (ciSup_le ((h.torsionAction_surjective (star c)).forall.2 fun q ↦ ?_))]
  have k := sub_eq_iff_comm.1 congr((h.normShift (F (star c) q) * h.normShift (F (star c) (F γ w)) -
    h.normShift (F (star c) q)) $(H f hf) 0).symm ▸ v.map_sub ..
  simp [h.normShift_map_eq_map_star, h.normShift_comm (F γ _),
    mem_thetaSpace_iff_normalizedShift.1 hf, ← sub_one_mul, action_comm c, h.1, b,
    by simpa [N] using congrArg v (by grind : μ ^ 8 = (F (star c)).det ^ 8)] at k
  grw [le_max_iff, le_sqrt_iff_sq_le, ← size_le_iSup (mul_shift_mem_sizes hφ hφ w) (h.torsionAction
    (star c) q), sq, factorsThrough_mkQ_of_mem_sizes hφ (a := _ + w) (b :=
    h.torsionAction (star c) q + h.torsionAction _ (h.torsionAction γ w)) (SModEq.sub_mem.2 (by
    simpa [b, action_comm γ, h.1] using congr(F $(eq_sub_of_add_eq s) w ∈ L))), h.sizeAt_add,
    h.sizeAt_eq_normShift]
  exact k.imp (mul_le_mul_right · _) (.trans' (v.map_sum_le fun z _ ↦ map_mul v .. ▸ mul_le_mul'
    ((OrderIso.le_symm_apply _).2 (r (by simpa [action_comm c, ← exp_nsmul, mul_left_comm] using
    (h.riemannPhase_eq_one (h.5 _ (h.1 γ _ T)) a)))) (h.sizeAt_add (h.torsionAction ..) ⟨_,
    h.mem_torsionPoints ⟨_, a⟩⟩ ▸ size_le_iSup hφ _)))
  simp [IsAppellHumbert.poincareTerm, ↓h.multiplier_eq_exp, ← exp_sub,
    ← exp_conj]; grind [h.exp_eq_of_mem_lattice l.2 (h.1 β _ l.2), action_comm, adjoint, conj_symm]
  simpa [h.1, (L.sub_mem_iff_right a).1 (h1 (F c z.out) fun l hl ↦ by
    have := h.normShift_sum_eq_char_smul c (fun l k ↦ by rw [normShift_comm,
      h.riemannPhase_eq_one (h.5 l k) (@a z), one_smul, (mem_thetaSpace_iff_normalizedShift.1 ht).2
      _ (h.1 _ _ k)]) 1 ⟨(F c).inverse l, by simpa [divLattice]⟩ rfl
    simp [← sum_mul, funext_iff, h.normShift_comm, mem_thetaSpace_iff_normalizedShift.1 ht, *] at *
    simpa [k, riemannForm_swap l, exp_neg, ← fourierChar_eq_one, Circle.ext_iff] using this x).2]
    using congr(F $s z.out ∈ L)
omit hd h1
lemma hasShiftBound_descent (G : ∀ (A : LatticeForm L) y, F c y.1 ∈ L → A.HasShiftBound v y 1) (p :
  IsPosRiemann (pullForm (F c) B + -A)) {D} : B.HasShiftBound v (h.torsionAction c w) D →
  A.HasShiftBound v w (D * (v (Nat.card (h.MulKernel c)))⁻¹ ^ 2) :=
  have H : IsHermitianAction L _ F β := by grind [IsHermitianAction, pullForm_apply_apply,
    action_comm, riemannForm_def, (action_injective c).ne]
  fun I ↦ .of_isPosRiemann_sub H.isAmpleType p fun t ht@⟨_, _⟩ x ↦ by
  have T a t : h.normShift (F c a) (t ∘ (F c).inverse) = H.normShift a t ∘ (F c).inverse := by
    ext; simp [normalizedShift, riemannForm, action_comm]
  let s (ξ : AddChar (h.MulKernel c) ℂ) := ∑ k, ξ (-k) • h.normShift (F c k.out) (t ∘ (F c).inverse)
  grw [← le_sqrt_iff_sq_le, mul_right_comm, sqrt_mul, sqrt_sq,
    ← (v.map_sum_le fun ξ _ ↦ ?_ : v (∑ ξ, h.normShift (h.torsionAction c x) (s ξ) 0) ≤ .sqrt _)]
  simp [s, sum_comm, ← sum_mul, T, mem_thetaSpace_iff_normalizedShift.1 ht,
    AddChar.sum_apply_eq_ite, field, H.sizeAt_eq_normShift]
  grw [← sizeAt_eq_normShift, le_sqrt_iff_sq_le, fun ξ ↦
    I _ (.of_mem_thetaSpace (f := s ξ) (χ := h.multiplier * fun l ↦ if hl : l ∈ L then
    ξ ⟦⟨(F c).inverse l, by simpa [divLattice]⟩⟧ else 1) ⟨add_zero B ▸ h.isAppellHumbert.add
    (by simp_all [isAppellHumbert_iff, ← ξ.map_add_eq_mul]; tauto), h.isAmpleType.2, 2 * .card
    (h.MulKernel c), by simp_all [mul_pow, pow_mul, multiplier_sq, -canonicalMultiplier,
    ← ξ.map_nsmul_eq_pow]⟩ ⟨by simp [s, normalizedShift]; fun_prop, fun l hl ↦ by
    simpa [normalizedShift, ← neg_add_rev, exp_neg, field, mul_right_comm _ (ξ _), funext_iff, *]
      using h.normShift_sum_eq_char_smul c (by grind [mem_thetaSpace_iff_normalizedShift.1 ht]) ξ
      ⟨(F c).inverse l, by simpa [divLattice]⟩ (refl (s ξ))⟩),
    ← (h.torsionAction_surjective c).iSup_comp, ciSup_le']
  simpa only [h.sizeAt_eq_normShift, ← map_mul, s, map_sum, univ.sum_apply, sum_mul_sum] using
    fun x ↦ v.map_sum_le fun i _ ↦ v.map_sum_le fun j _ ↦
    (mul_le_iSup_of_hasShiftBound ⟨H.isAmpleType, ht⟩ ⟨H.isAmpleType, ht⟩ (x := x + ⟨_,
    h.mem_torsionPoints i.out⟩) (y := x + w + ⟨_, h.mem_torsionPoints j.out⟩)
    (G _ _ (by simp [sub_sub, add_right_comm, sub_mem]))).trans_eq' (by simp [← map_add, T,
    H.sizeAt_add, valuation_eq_one_of_pow_eq_one (orderOf_pos ξ).ne', ← ξ.pow_apply])
variable (G : ∃ᶠ d : V →L[ℂ] V in nhds 0, ∃ c, ∃ _ : NeZero c, (∀ x, F c (d x) = x) ∧
  ∀ (A : LatticeForm L) y, F c y.1 ∈ L → A.HasShiftBound v y 1)
include G
lemma eventually_hasShiftBound : ∀ᶠ C in atTop, B.HasShiftBound v w C :=
  h.isAmpleType.rec fun A _ _ ↦ by
  have := of_finrank_pos (A.nsmul 2).finrank_sq_eq_relIndex.2.2
  let e x := proj 0 ∘ₗ ((2 • B).thetaShift x).domRestrict ((2 • B).thetaSpace (h.multiplier ^ 2))
  have ⟨g, D⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_iInf_ker_le_ker (K := e
    0) (L := fun y : {y // (B + B).HasShiftBound v (y + y - w) 1} ↦ e y) fun f hf ↦ by
    simp [e] at hf ⊢; simpa using congr($(eq_zero_of_small_mesh (f.2.1.continuous.comp (f :=
      midpoint ℝ ↑w)
      (by fun_prop [midpoint])) (G.mono fun _ ⟨c, _, e, K⟩ ↦ ⟨_, e, fun z k ↦ hf _ ((add_mem w.2
      (h.mem_torsionPoints ⟨z, k⟩)).imp' (· * 2) (by simp [two_smul])) (K _ _ (by simpa))⟩)) (-w)))
  filter_upwards [mem_atTop (g.support.sup (v ∘ g))] with K o _ (.of_mem_thetaSpace (f := f) H k@⟨_,
    T⟩) x
  have E y : v (e y.1 ⟨fun y ↦ (-B x x).exp * f (x - y) * f (x + y), by fun_prop, fun l hl z ↦ by
      simp [← add_assoc, ← sub_sub, sub_add_cancel _ l ▸ T l hl (x - z - l), exp_add, exp_sub,
      two_mul, field, ↓multiplier_sq, *]⟩) = B.sizeAt v f (x - y) * B.sizeAt v f (x + y) := by
    simp [LatticeForm.sizeAt, e, ← map_mul, mul_mul_mul_comm _ (f _), ← exp_add, ← mul_assoc]; ring
  simpa [sq] using (E 0).ge.trans (D ▸ congr(v $(LinearMap.sum_apply ..)).trans_le (v.map_sum_le fun
    y h ↦ map_mul v .. ▸ mul_le_mul' ((le_sup h).trans o) (E _ ▸ mul_le_iSup_of_hasShiftBound ⟨H,
    k⟩ ⟨H, k⟩ (by aesop))))
lemma hasMultiplicativeNorm_of_frequently : HasMultiplicativeNorm v L := fun _ _ _ _ s t ↦
  (G.and_eventually ((by simp [continuous_clm_apply]; fun_prop : Continuous
  (pullForm · (B + B))).tendsto' 0 _ (by aesop) h.isAmpleType.eventually_add_neg)).exists.elim fun _
  ⟨⟨c, _, e, K⟩, P⟩ ↦ (ciSup_mul_le_ciSup_mul_ciSup (bddAbove_of_mem_sizes s)
  (bddAbove_of_mem_sizes t)).antisymm (iSup_mul_iSup_le fun x y ↦ (mul_le_iSup_of_hasShiftBound s t
  ((y - x - 0).2.elim fun n o ↦ .of_doubling id (const _ _) ⟨(v (Nat.card (h.MulKernel c)))⁻¹ ^ 2,
  fun A ↦ have ⟨a, m, Q⟩ := (h.isAmpleType.eventually_isPosRiemann_smul_sub A).exists
  have k := h.nsmul m
  .of_isPosRiemann_sub k.isAmpleType Q fun _ q ↦
    LatticeForm.HasShiftBound.of_doubling (const _ _) Subtype.val ((nonempty_of_mem ((sInter_mem
  (finite_range_nsmul_torsion o.1 (p := LatticeForm.HasShiftBound v _) fun _ _ e ↦ by
    delta LatticeForm.HasShiftBound; congr! 9; apply factorsThrough_mkQ_of_mem_sizes <;> aesop)
  ).2 (Set.forall_mem_range.2 fun _ ↦ k.eventually_hasShiftBound G))).elim (⟨·, Set.mem_iInter.1
    ·⟩)) (fun D I w ↦ k.hasShiftBound_descent K ⟨(by simpa [riemannForm, action_injective c (e _),
    map_eq_zero_iff, action_injective] using (P.nsmul m).1 <| F c ·)⟩ (I
  ⟨_, by simpa using h.1 c _ w.2⟩)) ⟨_, o.2⟩ _ ⟨k.isAmpleType, q⟩⟩ (by aesop) _)).trans (by simp))
omit G
lemma _root_.hasMultiplicativeNorm_of_expanding [CharZero R] {n p : ℕ} (hn : ¬p ∣ n) (tor :
  ∀ a ∈ B.dualLattice, n • a ∈ L) (pp : p.Prime) (hv : v p < 1) (hc : ∃ᶠ d : V →L[ℂ] V in nhds 0,
  ∃ c k, (∀ x, F c (d x) = x) ∧ ¬IsUnit c ∧ IsCoprime c (star c) ∧ c ∣ p ^ k ∧
  v (F (star c)).det = 1) : HasMultiplicativeNorm v L := h.hasMultiplicativeNorm_of_frequently
  (hc.mono fun _ ⟨c, k, e, _, co, cp@⟨_, _⟩, _⟩ ↦ have : NeZero c := ⟨by aesop⟩
  ⟨c, ‹_›, e, fun A y _ ↦ by
  have ⟨i, hi, i0, P⟩ := ((Nat.frequently_modEq pp.ne_zero n).and_eventually
    (h.isAmpleType.eventually_isPosRiemann_smul_sub A)).exists
  have := (span {(n * i : R)}).finiteQuotientOfFreeOfNeBot (by aesop)
  have ⟨j + 1, _, e⟩ := ((((pp.coprime_iff_not_dvd.2 (pp.not_dvd_mul hn ((hi.dvd_iff dvd_rfl).1.mt
    hn))).cast.pow_left.mono cp dvd_rfl).map (Ideal.Quotient.mk (span {↑n * ↑i}))
    ).isUnit_of_dvd (by simp)).isOfFinOrder.exists_pow_eq_one
  obtain ⟨co, t, e⟩ := star_pow c _ ▸ co.pow (m := j + 1), mk_span_eq_iff_dvd_sub.1 e
  have := NeZero.mk (sub_ne_zero.2 (by simpa [*] using co.isUnit_of_dvd ·.dvd))
  exact (h.nsmul i0).hasShiftBound_one_of_ker rfl (fun a ha ↦ by simp [eq_add_of_sub_eq e,
    (by simpa using h.1 · _ (tor _ (mem_dualLattice_nsmul.1 ha)))]) pp hv (by simp [*]) P (by grind
    [map_mem]) co (map_natCast F _ ▸ (by grind [action_comm, map_mem] : F ↑(p ^ k) y ∈ L))⟩)
end IsHermitianAction
section FoldSeg8
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ThetaObject Obj LineBundle PointFn AddObj Scheme ThetaTorus PeriodMap Category Over Spec
  IsLocalRing Fint
attribute [local simp] pullback.lift_fst pullback.lift_snd IsHomogCoords.pull_iff paddingTuple
  doubledCoeffs thetaProduct pull_pi coordSection
  landsIn_iInf AddChar.map_add_eq_mul Finset.prod_ne_zero_iff Int.cast_smul_eq_zsmul funext_iff
attribute [-simp] map_smul
variable {V ι κ : Type} [FinComplexSpace V] {S} [IsReduced S] [IsLocallyNoetherian S] [Finite ι]
  {η : κ → _} (j : ι → κ) (hη : @IsDenseFamily ι S (η <| j ·))
omit [Finite ι] in
lemma LineBundle.IsHomogCoords.pi {K X t V} [Fintype K] {M : K → LineBundle X ι} {θ : ι →
  V → ℂ} {w : K → V} (h : ∀ l, (M l).IsHomogCoords (A := ⟨ℂ⟩) t (θ · (w l))) :
  (LineBundle.pi M).IsHomogCoords t fun μ ↦ ∏ l, θ (μ l) (w l) := by simp_all [IsHomogCoords]
include hη
lemma exists_isAbelianScheme {O A} [CommRing O] {e : ∀ i, V → (Over.mk (η i) ⟶ A)} (he : ∀ i,
  IsSeparatingFamily fun v ↦
  (lift (e i v) (𝟙 _)).1) (s : IsSeparatingFamily fun s : κ × V ↦ (e s.1 s.2).left) [Flat A.hom]
  [IsProper A.hom] (red : AllSpecializeTo S fun t ↦ IsReduced (pullback A.hom t)) {f : O → _} {F :
  κ → O →+* V →L[ℂ] V} (q : ∀ d i z, e i z ≫ f d = e i (F i d z)) m o (hm : ∀ i y z, e i (y + z) =
  lift (e i y) (e i z) ≫ m) (ho : ∀ i, toUnit _ ≫ o = e i 0) : ∃ (_ : IsAbelianScheme A) (_ :
  ModuleObj O A) (ε : ∀ _, V →+ _), e = (ε · ·) ∧ ∀ c i z, c • e i z = e i (F i c z) := by
  obtain ⟨t, _ : Flat (A ⊗ A).hom⟩ := s.prod hη s.1 (he ·.1), Flat.comp (pullback.fst ..) _
  have := t.prod hη s.1 (he ·.1.1)
  refine let _ : AddObj A := { AddGrpObj.mk (toAddMonObj := ⟨o, m, (λ_ A).inv_comp_eq_id.1 (?_ :
      lift (toUnit A) (𝟙 A) ≫ _ = _), (ρ_ A).inv_comp_eq_id.1 (?_ : lift (𝟙 A) (toUnit A) ≫ _ = _),
      (α_ A A A).inv_comp_eq.1 ?_⟩) (f (-1)) ?_ ?_ with add_comm := ?_ }
    let _ := @ModuleObj.mk _ O _ A _ (fun T ↦ @.ofMinimalAxioms _ _ _ _ ⟨flip (· ≫ f ·)⟩
      (have := isAdditive_of_universal (f := f ·) ?_; (add_comp · · _)) (fun _ _ ↦
      (· ≫= ?_ |>.trans (comp_add ..)))
      (fun _ _ ↦ (· ≫= (?_ : _ = _ ≫ _))) (· ≫= (?_ : _ = 𝟙 A))) fun _ _ _ ↦ (assoc ..).symm
    ⟨.mk (toSmooth := open HasRingHomProperty RingHom MorphismProperty Hom Pullback in
    smoothLocus_eq_top_iff.1 (top_unique fun y _ ↦ have ⟨k, _, _, t, a, H⟩ := red (A.hom y)
      have ⟨⟨x, b, a⟩, U', u, n⟩ :=
        And.intro ((isClosedMap _).specializingMap a) (exists_isAffineOpen_landsIn t)
      let ⟨W, v, m, e⟩ := exists_isAffineOpen_mem_and_subset ((mem_preimage _).2 (a ▸ n ⟨⟩))
      let := (appLE _ U' W e).1.toAlgebra
      b.mem_open (smoothLocus _).2 ((formallySmooth_stalkMap_iff U' u W v e m).2
        (@.of_formallySmooth_fiber _ _ _ _ _ (flat_appLE _ u v _) (finitePresentation_appLE _ u v _)
        _ _ _ _ ⟨rfl⟩ (smooth_algebraMap.1 (Spec_iff.1 (of_isPullback (.paste_horiz (.of_horiz_isIso
        ⟨(fiberToSpecResidueFieldIso ..).2.w⟩) (isPullback_fiberToSpecResidueField_of_isPullback
        (.of_horiz_isIso_mono ⟨id_comp _⟩) (Spec.map _ _))) (by
      erw [← Hom.comp_apply, u.SpecMap_appLE_fromSpec _ v, Hom.comp_apply, v.fromSpec_primeIdealOf,
        a]
      exact instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact.1
        (isPullback_fiberToSpecResidueField_of_isPullback (.paste_vert (.of_hasPullback ..)
        (.of_hasPullback _ t)) (id (closedPoint k))).flip (by and_intros <;> infer_instance)
        (of_isPullback (.of_hasPullback ..) (comp_mem _ _ _ inferInstance ((pullbackAddObj
        t).of_chart _ (Opens.ι _) ((pullback.snd _ t).dense_smoothLocus_of_perfectField
        |>.nonempty_iff.2 (exists_preimage_pullback x _ a).nonempty).to_subtype (by
        simp [← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq])))))))).1))))
    fun m hm ↦ m.cast_smul_eq_nsmul O (𝟙 A) ▸ s.2.surjective _ _ fun z ↦ congr($(q m _ ((m⁻¹
    : ℂ) • z.2)).1).trans (by simp [← smul_assoc, hm]), ‹_›, (.mk' _ <| hm ·), rfl, q⟩ <;> exact
    IsSeparatingFamily.hom_ext ‹_› (by simp +zetaDelta [← hm, q, ← assoc, Hom.add_def,
    AddMonObj.add] <;> grind)
unseal ThetaObject.groupScheme ThetaObject.toFamily in
theorem exists_thetaFamily_of_points {E} [Field E] [CMBase E] {D : PEL E} {R} {π : S ⟶ Spec R}
  {φ : 𝓞 E →+* R} (hd : Mono (specMap φ)) (ho : ∀ i c, (preimage (η i ≫ π ≫ specMap φ)).hom c = Φ v₀
  c.val) {g ℓ : κ → _} {c : D.levelTorsion → LineBundle S D.T} {x : ∀ k, ThetaTorus D (g k) (ℓ k) V}
  (hc : ∀ ω, (c ω).IsLinearSystem) [Fintype D.levelTorsion] (hπ : (pi c).IsProjEmbedding π) (hx :
  ∀ i ω, (c ω).IsHomogCoords (η i) ((x i).thetaCoord · ((x i).torsionLift ω))) (hβ :
  IsUnit (φ (star D.β - D.β))) (hT : IsUnit (Nat.card D.T : R)) (cl : AllSpecializeTo S fun t ↦ ∃ 𝔭,
  IsCutOutAt D.r D.i (thetaRanks D.T D.r) c t 𝔭) (cv : ∀ t s, ∃ o, ∀ (l : D.T) k, l + k ∈ [o, -o,
  s - o] → t ∈ (c ⟨l, D.T_le_levelTorsion l.2⟩).opens k) : ∃ X : ThetaFamily D S (π ≫ specMap φ),
  ∀ i, ∃ m : TorusModel (X := X) (η i) (x i).toPeriodMap, m.θ = fun μ v ↦ (x i).thetaCoord v μ := by
  have u := @Valuation.one_apply_le_one ℂ NNReal
  have ⟨A, N, e, hN@⟨hn, _, _⟩, _, hl, he, red, s₁⟩ := exists_flat_closure j hη hc
    (Nat.le_of_lt D.three_le_r) D.degree_spec.1 (x · |>.thetaCoord_vector_ne_zero)
    (fun i ↦ have k z : IsIntegralCoords _ fun _ ↦ ⟨_, u _⟩ := ⟨1, by
                                simpa using (x i).thetaCoord_vector_ne_zero z⟩
    (x i).isCutOutAt_reduction (φ :=
      algebraMap ..) (by tauto) (x i).hasGoodReduction_trivial k (fun _ ↦ k _) (hx i)) cl
  have s₀ : IsSeparatingFamily fun i ↦ (toUnit (Over.mk (η i))).1 := ⟨‹_›, hη.of_comp⟩
  obtain ⟨s₂, ⟨a, hA, h₁⟩, b, -, h₂⟩ := s₁.prod hη s₁.1 (he ·.1), D.exists_padding
  choose σ hσ hσ' using (s₀.exists_map_of_coords (hW := hc ·) hN (hx · _) (hl · _))
  have H (a : Fin (D.r - 3) → 𝓞 E) (c : 𝓞 E) (h : star c * c + 3 + ∑ l, star (a l) * a l = D.r)
    (ψ := fun c : _ × _ ↦ ite (c.1 = 1) (fst ..) (ite (c.2 = 1) (snd ..) (toUnit _ ≫ σ 0))) (b := by
    simp +zetaDelta [← comp_left, -lift_left, hσ, hl, hA]) :=
    let P b := paddingTuple (cond b a 1) (cond b c 0)
    have q b :
      IsRiemannTuple (P b) D := by cases b <;> simp [IsRiemannTuple, P, D.three_le_r, ← h] <;> ring
    (exists_isLinearSystem (fun b a ↦
      ((x a.1.1).thetaProduct (doubledCoeffs (P b) (P !b)) · a.1.2 a.2)) s₂ (.pi fun l ↦ hn.pull
    (ψ (doubledCoeffs (P false) (P true) l)).1) (forall_imp (fun _ ↦ .pi) b) fun b μ s ↦
    let y := ∑ l, star (P b l).1 • μ (.inr l) - ∑ l, star (P (!b) (.inr l)).1 • μ (.inl (.inr l))
    (cv _ y).elim fun o a ↦ let ν := Sum.elim (cond · (y - o) o) (μ ∘ .inl ∘ .inr)
      ⟨_, by exact ⟨⟨a 0 _ (by simp), a 0 _ (by simp)⟩, ⟨⟩⟩, fun q ↦ Sum.elim (μ ∘ .inr - (·.1 • q)
        ∘ P b) (ν + (·.1 • q) ∘ P !b), _, ((((hc 0).mul (hc 0)).1 (o, y - o) (μ (.inl (.inl true)),
    μ (.inl (.inl false)))).1.mul (isRegularOn_ofSection ((hT.map (toSpecΓ R ≫
        π.appTop).hom).unit⁻¹.1 * ↑(D.rTorsion.relIndex D.T).sqrt))).pull (A ⊗ A).hom, fun ⟨⟨i, u⟩,
        v⟩ U ↦ by simp [ofSection_eq, hx .., by simpa [hx ..] using U, P, ν, ↓Over.w, mul_assoc,
        ← by simpa [P, ν, mul_assoc] using (x i).riemann_relation (w := u) (q b) rfl (q !b) (μ :=
        μ ∘ .inr) (μ' := ν) (by simp [ν, y, P]) v, mul_left_comm ((x i).thetaCoord o 0)⁻¹]⟩).elim
      fun _ H ↦ (s₂.exists_map_of_coords H.1 (isProjEmbedding_pi _ (fun _ ↦ hN) (Pi.hom_ext _ _))
      H.2.1 fun z ↦ .pi (t := (Pi.lift fun k ↦ e _ _).1) fun k ↦ by
      simpa [← comp_left] using hl _ _).imp fun _ k ↦ And.intro (k.1 ⟨⟨·, ·⟩, ·⟩) (k.2 ▸ H.2.2)
  obtain ⟨g, hg, -⟩ := H a (-1) (by simp [← h₁])
  let μ k := g ≫ Pi.π _ (.inr (.inr k))
  choose f q using (Submodule.mem_span (x := ·) |>.1 (hA.ge ⟨⟩) (AddSubgroup.ofSub {d | ∃ f, ∀ i a,
    e i a ≫ f = e i ((x i).intAction d a)} ⟨1, 𝟙 _, by simp⟩ fun _ ⟨f, h⟩ _ ⟨k, l⟩ ↦ ⟨lift k f ≫ μ
    (.inl true), by simp [*, μ, ← assoc, neg_add_eq_sub, sub_eq_add_neg]⟩).toIntSubmodule
    fun | _, ⟨l, rfl⟩ => ⟨lift (𝟙 A) (𝟙 A) ≫ μ (.inr l), by simp [μ, hg, ← assoc]⟩)
  obtain ⟨_, _, e, rfl, hA⟩ := exists_isAbelianScheme j hη he s₁ red
    q (μ (.inl false)) (σ 0) (by simp [μ, hg, ← assoc]) (by simp [hσ])
  let ψ (c : 𝓞 E × 𝓞 E) := c.1 • fst A A + c.2 • snd A A
  have G i l h := by simpa using (OverMorphism.ext (hN.eq_of_isHomogCoords (by simp)
    (funext ((x i).thetaCoord_mem_thetaSpace · |>.2 l h 0) ▸ hl i _)
    ((hl i 0).smul (by simp [(x i).isAppellHumbert_periodLattice.ne_zero h]))) :)
  have w : D.HasClassLaws N.picClass := by
    simp_rw [PEL.HasClassLaws, Pic.ParallelogramLaw, ← forall_and]
    intro T y z
    have w {c a} h (y z : T ⟶ A) := (H a c h ψ).elim fun g k ↦ by
      simpa -implicitDefEqProofs [ψ, fun l ↦ (s₂.hom_ext (by simp [*, ← assoc]) : g ≫ Pi.π _ l =
        ψ (doubledCoeffs (paddingTuple a c) (paddingTuple 1 0)
        l)), -lift_left, ← pull_comp, ← comp_left] using (congr($(k.2).pull (lift y z).1))
    have := congr(($(w h₁ z 0) - $(@w (-1) a (by simp [← h₁]) z y), $(w h₂ y 0) - $(w h₂ y z),
      $(w h₂ z 0) - $(@w (-star D.β) b (by simp [← h₂, mul_comm]) z z),
      $(w h₁ y 0) - $(w h₁ y (star D.β • z))))
    simp [Pic.pairing, Pic.atPoint, sub_smul,
      D.star_beta] at this ⊢; clear * - this; grind [sub_eq_add_neg]
  have hp i := isGroupBaseChange_counit (A := A) (η i)
  let L i : (.mk (η i) ⟶ A) →ₗ[𝓞 E] _ := ((hp i).pointEquiv (T := 𝟙_ _)).symm.1
  have H i u : (L i u).1 = (lift u (𝟙 _)).1 :=
    pullback.hom_ext (by simpa using! (hp i).1.lift_fst ..) (by simpa using! (L i u).w)
  have U i d h := by refine ((x i).exists_uniformisation_of_dense d h (hN.of_isPullback (hp i).1) ?_
    (.comp (L i) (e i)) ?_ ?_ ?_) <;> simp +contextual [Pic.ParallelogramLaw,
    w.1 _, ↓(hp _).atPoint_picClass_pull, H, hl, G]; apply he
  have dim := smoothOfRelativeDimension_of_fibres s₁.2 (U ·.1 · · |>.choose_spec.2.2.2)
  choose u t using (U · (abelianDim E D.Index) (by simp; infer_instance))
  let ς :
    D.levelTorsion →ₗ[𝓞 E] _ := by use! σ <;> exact fun a b ↦ s₀.hom_ext fun i ↦ sub_eq_zero.1 (by
              simp [hσ, hA, PeriodMap.torsionLift, intAction, ← toRealVectors_smul, ← map_add,
                ← map_sub]; exact G i _ ⟨_, by simp, rfl⟩)
  refine ⟨{
    A := A, N := N, class_laws := w, relative_dim := dim, embeds := hN, η := ς
    theta_law t T _ _ q h := by
      as_aux_lemma =>
        have L i l k := by simpa [thetaShift_apply, ← eq_inv_mul_iff_mul_eq₀,
          ← PeriodMap.torsionLift.eq_1]
          using ((x i).thetaShift_thetaCoord (s := l) (frameTorsionClass_ratLift _) k)
        choose W r hr hW v using fun l m ↦ ((cv _ m).elim fun o H ↦ ⟨_, _, (((hc _).mul (hc 0)).1
          (-o - l, m - o) (m - o - l, -o)).1, landsIn_iff_mem.2 ⟨H l _ (by simp), H 0 _
          (by simp)⟩, by simp +contextual [hx .., sub_eq_add_neg, field, zero_add (_ : V) ▸ L ..]⟩ :
          ∃ W r, IsRegularOn r W ∧ LandsIn t W ∧ ∀ i, LandsIn (η i) W → r _ (η i) =
          (x i).bicharacter (torsionLift_mem ..) m)
        have F f g (h := by simp +contextual [v, bicharacter_neg_eq_swap]) (a : IsRegularOn f _ ∧
          IsRegularOn g (iInf W.uncurry) :=
          by simp +contextual [IsRegularOn, hr _ _ _]) := a.elim s₀.pointFn_ext h _ t (by simp [hW])
        refine ⟨fun s ↦ ⟨(r s · _ t), F _ 1, fun _ _ ↦ F _ (_ * _)⟩, fun s u ↦ F .., fun u s ↦
          exists_isSectionLift_coordSection _ _ fun l m B y a b ↦ ⟨⟨u.1 • l - s, by simp [N.5,
          landsIn_preimage.1 a, ↓H0_smul, smul_smul, AddChar.val_isUnit, IsUnit.map,
          -AddChar.coe_mk]⟩, fun j ↦ ?_⟩, fun s h ↦ H0_ext fun _ _ _ _ a ↦ s₁.pointFn_ext
          (hn.1 ..).1 (hn.1 ..).1 (by simp +contextual [hl .., thetaCoord_eq_of_mem_lagrangian _ s
          h]) _ _ a, by simpa using hT.map (preimage (t ≫ π)).hom,
          fun s h ↦ by simpa using! F (∑ l : D.lagrangian.addSubgroupOf D.T, r s l ^ 2) 0 (by
          simp +contextual [v]; exact fun i _ ↦ (((x i).bicharacter _ ^ 2).compAddMonoidHom
          (AddSubgroup.subtype _)).sum_eq_zero_iff_ne_zero.2
            (h ∘ (x i).mem_lagrangian_of_bicharacter_sq s ∘ DFunLike.congr_fun))⟩
        let f := translation (σ ⟨s, D.T_le_levelTorsion s.2⟩)
        have w := by simpa [f, ← h.translation_comp] using h.smul_id_comp u.1 =≫ f.1
        have R m := ((hr s m).pull A.hom).mul (hn.1 l (u.1 • (s + m))).1
        choose _ H using (x · |>.exists_thetaCoord_sign_smul u)
        simpa [↓H0_smul, ← hr _ _ _, hW, f, ← w, -comp_add] using! s₁.pointFn_ext ((R j).mono
          inf_le_left) (((R m).mul ((hn.1 ..).1.pull ((u.1 • 𝟙 A) ≫ f).1)).mono inf_le_right) (by
          simp +contextual [v, hl .., L, H, ← comp_left, field, f, hσ, ← map_zsmul, ← map_add])
          _ (y ≫ q.1) (by simp [f, ← w, LandsIn.comp, hW, -comp_add]; tauto)
    signature b _ s _ := Spec_stalkClosedPointTo_fromSpecStalk
      s ▸ by as_aux_lemma => simpa using (exists_isLieChart dim _).imp fun V ⟨z, m, J⟩ ↦ ⟨z, _,
      J rfl, .of_points (stalk_eq_zero_of_dense hη) (fun ⟨i, _, E⟩ ↦ (x (j i)).4.elim fun ε he ↦
      ((u _).hasSignature_iff (F := (x (j i)).intAction) (by simp
      [t, ← hA]) (J E) (hp _) (x (j i)).isPeriodMap.finrank_eq_abelianDim).2 (by
      use ε.symm ((1, 0), 0), ?_, ?_, Φ v₀ (star D.β.val - D.β) • .fst .. ∘ₗ .fst .. ∘ₗ ε.1 <;>
        simp +contextual [by simpa [← E] using ho (j i), ← ε.injective.eq_iff, D.emb_beta_eq_of_ne,
        fun a z ↦ by simpa using congr($(he a) (ε z)), Prod.ext_iff, sub_mul, map_smul])) _
      (.map _ (by simpa [← assoc] using hβ.map (preimage
        (S.fromSpecStalk (s (closedPoint _)) ≫ π)).hom))⟩
    eq_of_list_eq _ _ h b := hπ.ext (by simpa [← hσ'] using! congr(pi $(funext b))) (hd.1 _ _ h) },
    fun i ↦ ⟨⟨ho i, _, _, _, (t i).1, fun c w ↦ by simpa [*, intAction] using! ((L i).map_smul
    c (e i ((x i).Q w))), (by simpa [t] using! congr(L i $(hσ · i))), (t i).2.2.1⟩, rfl⟩⟩
end FoldSeg8
section FoldSeg9
open NumberField IsLocalRing Valuation LinearMap Ideal IsPrime valuationSubring PeriodMap
lemma ThetaTorus.hasGoodReduction_and_val_card_eq_one {E} [Field E] [CMBase E] {V}
  [FinComplexSpace V] {D g ℓ} (x : ThetaTorus D g ℓ V)
  {v} {ρ : 𝓞 E →+* v.valuationSubring} (B : ∀ c, ρ c = Φ v₀ c.val) (hw : D.IsGoodAt
  (comap ρ (maximalIdeal _))) : HasGoodReduction x.B x.multiplier v D.r ∧ v (Nat.card D.T) = 1 := by
  have ⟨⟨hr, hT⟩, p, b, pp, pw, bw, cb, _, w, ww, pw', q⟩ := hw
  obtain ⟨⟨t, tw, tn⟩, n⟩ := Set.not_subset.1 (ww ∘ w.isMaximal.eq_of_le ne_top'),
    notMem_of_isCoprime_of_mem cb bw
  simp [(integers v).isUnit_iff_valuation_eq_one, B] at hr hT tn n
  let H := (2⁻¹ : ℂ) • (x.B + x.B.pullForm (Complex.I • 1))
  have : riemannForm H = x.B.riemannForm := by ext; simp [riemannForm, H, re_symm]; ring
  use ⟨x.hasGoodReduction_trivial.1, by grind [dualLattice_periodLattice,
    card_nsmul_mem_periodLattice], hr, x.hasGoodReduction_trivial.4,
    hasMultiplicativeNorm_of_expanding (B := H) ⟨x.intAction_mem_periodLattice, fun y z ↦ by
    simpa [H, Complex.ext_iff, re_symm, add_comm] using x.re_symm (Complex.I • y) (Complex.I • _),
    (by simpa [H, riemannForm, field] using x.isPosRiemann.1 · ·), by simp [H, ← adjoint],
    this ▸ x.isAppellHumbert_periodLattice.le_dualLattice, D.star_beta⟩
    (hw.1.2 <| mem_of_dvd _ ·.natCast pw) (by grind [dualLattice_periodLattice,
    card_nsmul_mem_periodLattice, RealComplexForm.dualLattice]) pp (by simp_all
    [v.mem_maximalIdeal_iff]) ((Continuous.tendsto' (by simp [continuous_clm_apply]; fun_prop) _ _
    x.isPeriodMap.complexMul.2).frequently (Metric.nhds_basis_ball.frequently_iff.2 fun r r0 ↦
    have ⟨a, ⟨k, ha⟩, nu, A⟩ := exists_pow_eq_span_inv_lt w.one_lt_q r0
    have K {y} h := mem_span_singleton.1 (ha.le (pow_mem_pow (x := y) h k))
    have h σ {y} h (e : v (σ y.val) = 1) := (@K y h).elim fun c k ↦
      have I c := (integers (v.comap σ)).mem_of_integral c.2.tower_top
      eq_one_of_one_le_mul_left (a := v (σ a)) (I a) (I c) (by simp [← map_mul, ← k, e])
    ⟨(Φ · (star a))⁻¹, by simp [pi_norm_lt_iff, *], star a,
      k, by simp [intAction, ← x.Q.eq_symm_apply,
      funext_iff, (by aesop : a ≠ 0)], by simpa, by grw [star_star, ← starRingAut_apply, K q]; simp
      [cb.symm.pow], by simpa using map_dvd starRingAut (K pw'), x.4.rec fun ε _ ↦ by
    simpa [← det_conj _ ε, det_prodMap, piMap, det_pi, h _ q, *, h _ tw, Subtype.forall'.1
      D.emb_beta_eq_of_ne] using .inl (h (star _) q (by simpa))⟩))⟩
end FoldSeg9
section FoldSeg10
seal Finset.univ Finset.sum Finset.prod
open ThetaObject Set AlgebraicGeometry Cardinal CategoryTheory Classical Filter IsLocalRing
  NumberField ModuliPoint Submodule LocallyOfFiniteType Over TorusModel
variable {E} [Field E] [CMBase E] {D : PEL E} {R ν} [NeZero ν] {U :
  UniversalFamily D R} {J} [Finite J] {γ : J → _} (C : U.GraphClosure γ ν) {f : AnalyticFamily D}
lemma AnalyticFamily.holomorphic_immersive {Z τ} {X : ThetaFamily D Z τ} {x : _ →
  ThetaObject X _} (m : ∀ b, (x b).TorusModel (f.torus b).toPeriodMap) {b}
  (h₀ : b ∈ f.U) : let ψ q := atGeneric (m _).uniformisation.expMap q.2 ≫ (x q.1).toFamily.left
  (∀ z, HolomorphicAt ψ (b, z)) → IsHolImmersionAt x b := by
  intro ψ H
  use by simpa [ψ] using ((H 0).comp (g := (·, _)) (by fun_prop)).comp_hom (hom _), fun v hv ↦
    f.eq_zero_of_linear _ h₀ _ fun _ ↦ sub_eq_zero.1
    (((m _).uniformisation.immersive_of_isPullback (x _).isGroupBaseChange.1 0).2 _ ((isJet_comp_iff
    (by fun_prop) (H _)).2 (isFirstOrderConst_iff.2 fun U r k ↦ ?_)))
  obtain ⟨d, a, L, c⟩ := f.analyticAt _ h₀,
    (H 0 (PointFn.isRegularOn_ofSection r) k).imp_right (·.fderiv.neg.differentiableAt)
  set i : _ →L[ℂ] BallBase D.Index × BallFibre E D.Index := .inr ..
  have R w : fderiv ℂ (PointFn.ofSection r _ <| ψ ·) (b, 0)
      (i (fderiv ℂ (f.torus · |>.Q ((f.torus b).Q.symm w)) b v)) = L (i w) (v, 0) := by
    induction eq_top_iff'.1 (m b).uniformisation.3.2.1 w using span_induction
    any_goals simp (disch := fun_prop) [fderiv_fun_add, fderiv_fun_const_smul, *]
    by_contra
    apply (tendsto_natCast_atTop_cobounded.eventually (tendsto_inv₀_cobounded' (((c.hasLineDerivAt
      _).clm_apply ((hasFDerivAt_id _).hasLineDerivAt _)).neg.eventually_ne
      (by simpa [add_neg_eq_zero])))).frequently
    filter_upwards [tendsto_const_nhds.prodMk_nhds (tendsto_inv_atTop_nhds_zero_nat
      (𝕜 := ℂ).zero_smul_const _) a, eventually_ne_atTop 0] with n u hn
    simpa [i] using isFirstOrderConst_iff.1 ((H _).isFirstOrderConst_of_nsmul X.relative_dim hn
      ((isJet_comp_iff (.prodMk (hasFDerivAt_id _)
      ((d ((f.torus b).Q.symm _)).differentiableAt.hasFDerivAt.const_smul (_ : ℂ)))
      ((H _).comp_hom _)).1 (cast (by simp_all [← (x _).isGroupBaseChange.nsmul_id_comp,
      ← comp_left_assoc, ← map_nsmul, (Uniformisation.eq_zero_iff ..).1, ← Nat.cast_smul_eq_nsmul ℂ,
      (f.torus _).Q.eq_symm_apply, TorusModel.lattice_eq, ψ, mem_classLattice,
      ← (x _).isGroupBaseChange.pullSection_comp]) (hv.comp_hom (X.η 0).1)))) U r u
  simp [*]
lemma ModuliPoint.exists_finite_reps D ν {𝔪} (h : 𝔪 ≠ 0) : ∃ (κ : Type) (f : κ → AnalyticFamily D),
  Finite κ ∧ ∀ a : ModuliPoint E _ ν, ∃ k, ∃ p ∈ (f k).U.1 ×ˢ .univ, ∃ z,
  a.IsLevelIso (levelGU _ 𝔪) z ((f k).ballPoint 0 p) := let φ := _ ∘ x
  (axiomOfChoice (exists_ball_family <| rangeSplitting φ ·)).elim fun f H ↦
    ⟨_, f, (finite_isSignedFrame_classes
    (isOpen_congruenceGL_span h)).subset fun _ ⟨a, e⟩ ↦ ⟨_, ⟨_, a.isSignedFrame⟩, e⟩, fun a ↦
    have ⟨_, ⟨z, rfl⟩, _, h, e⟩ := DoubleCoset.eq.1 (apply_rangeSplitting φ ⟨_, a, rfl⟩).symm
    ⟨_, ((H _).2.2.1 ⟨_, _, realVecAction z ∘ a.P, a.isSignedFrame.mul z h.1, a.isReflection.conj _⟩
      e.symm).imp fun _ ↦ .imp_right (⟨z, · ▸ by simpa [isLevelIso_iff, mul_assoc]⟩)⟩⟩
attribute [local simp] act ratConj
lemma UniversalFamily.isHolImmersionAt_datumPoint {P : Fin ν → _} {𝔪} p (hp : p.1 ∈ f.U) :
  IsHolImmersionAt (f.ballPoint P · |> U.datumPoint 𝔪 |>.left) p := by
  obtain ⟨I, _⟩ := f.holomorphic_immersive (U.model ⟨f, ·⟩) hp (U.holomorphic f _ hp),
    (f.analyticAt _ hp · |>.contDiffAt.fst'')
  simp_rw [← IsPt.eq_datumPoint (a := f.ballPoint ..) ⟨U.model (f, _), rfl⟩]
  refine (fun H ↦ ⟨H, fun (_, _) hv ↦ ?_⟩) (HasGermAt.of_jointly_mono ((Over.map U.base.hom).map <|
    Limits.Pi.π _ ·) (fun e ↦ OverMorphism.ext
    (fibrePower_ext_iff.2 ⟨by simpa using congr($(e ofNonempty).1 ≫ U.family.A.hom), (congr($(e
    ·).1))⟩)) (by rintro ⟨⟩ <;> simp <;> apply (U.holomorphic f _ hp _).comp (g :=
    (Prod.fst ·, _)) (ContDiffAt.analyticAt _) <;> (try simp) <;> fun_prop) (by simp; rfl))
  cases I.2 _ ((isJet_comp_iff hasFDerivAt_fst I.1).1
    (by simpa using hv.comp_hom (U.family.fibrePower _).hom))
  simpa [funext_iff] using fun i ↦ (Uniformisation.immersive_of_isPullback _
    (ThetaObject.isGroupBaseChange _).1 _).elim fun h k ↦ k _
    ((isJet_comp_iff ((hasFDerivAt_apply i p.2).add_const _) h).1 (by simpa [π] using
    ((isJet_comp_iff (hasFDerivAt_prodMk_right p.1 p.2) H).2 hv).comp_hom (U.family.proj (.inr i))))
lemma UniversalFamily.GraphClosure.holomorphicAt_point P p (hp : p.1 ∈ f.U) :
  HolomorphicAt (f.ballPoint P · |> C.point |>.left) p := .of_jointly_mono _ C.hom_ext
  fun j ↦ by simpa [↓← comp_left, ↓C.point_comp_proj] using!
  (isHolImmersionAt_datumPoint (f := f.heckeTranslate _) p hp).1
lemma UniversalFamily.GraphClosure.exists_arc z : ∃ᵉ (V : ValuationSubring ℂ) (α) (b) (ρ :
  C.W.left.residueField z →+* _), specMap ρ ≫ C.W.left.fromSpecResidueField z =
  specMap (residue V) ≫ α ∧ ∀ {𝔪 u} {a : ModuliPoint E _ ν}, C.point b ≫ u = U.datumPoint 𝔪 a →
  U.family.IsPointOf 𝔪 a (α ≫ u.1) := C.exists_level_point_eq.elim fun m M ↦ by
  obtain ⟨_, _, f, _, H⟩ := U.isDedekindDomain, exists_finite_reps D ν (by simp : m.1 ≠ 0)
  choose b _ G using fun i ↦ exists_generic_member (hom _) ((f i).U.2.prod (by simp))
    ((f i).2.prod isConnected_univ) (C.holomorphicAt_point 0 · ·.1)
  obtain ⟨i, V, α, l, rfl⟩ := @_root_.exists_arc _ _ (isLocallyNoetherian (hom _)) _ _
    (C.isSeparatingFamily.2.induction_on · (by simp) (H · |>.elim fun c ⟨q, h, _, r⟩ ↦ M r
    ▸ (G c q h).mem_closed (by simp) (subset_closure (mem_range_self c)))) z
  exact (comap_closedPoint (residue _)).rec ⟨_, α, _, _, (Scheme.SpecToEquivOfField ..).3 (specMap
    _ ≫ α), fun h ↦ .of_generic (((reassoc_of% l) _).trans congr($h.1) ▸ isPointOf_datumPoint)⟩
lemma UniversalFamily.GraphClosure.point_surjective {c} (hc : ∀ a, C.point a ≫ c =
  U.datumPoint 1 a) : C.point.Surjective := fun t ↦ by
  have ⟨z, φ, hφ, _⟩ := exists_countable_residue_point (hom _) t.1
  have ⟨V, α, b, j, hα, H⟩ := C.exists_arc z
  obtain ⟨⟨φ, rfl⟩, e, ho⟩ := exists_ringHom_complex_extend j.injective φ.injective
    (mk_quotient_le.trans (mk_set_le _)), H (hc _)
  have hφ := reassoc_of% (by simp_all [specMap] : specMap (φ.comp (residue _)) ≫ α = t.1)
  choose x p using fun {y} ↦ exists_isPullbackAlong (X := U.family) (specMap (φ.comp (residue V))) y
  choose f w using fun {y} ↦ FullStructure.exists_pullback (@p y)
  have ⟨g, ℓ, d, Y, m, v, s₂⟩ := exists_torusModel (f e.fullStructure) (by simp [baseHom, ← p, hφ,
    reassoc_of% (by simp [← c.w, reassoc_of% ho] : ‹ThetaObject ..› ≫ hom _ = α ≫ hom _)]; tauto)
  choose P G using (@id m.π.Surjective (m.uniformisation.surjective.comp Y.Q.surjective) <|
    p.isGroupBaseChange.pullSection <| e.π ·)
  use ⟨_, _, P ∘ b.P, ⟨_, Y.isSignedFrameFor⟩, s₂⟩, C.hom_ext fun i ↦ (γ i).2.2.1.elim fun _ q ↦ ?_
  obtain ⟨⟨_ | _, rfl⟩, f', h⟩ := q.2.exists_intCast_eq (γ i).2.2,
    H (C.point_comp_proj _ i) <;> simp [↓Int.cast_pos] at q
  obtain ⟨o, χ, _, _, l, _⟩ := exists_isogeny 1 (by simp) e f' (by simp) (γ i).2.2.2 (by simpa)
  obtain ⟨⟨ψ, a, _, K⟩, g₀, ℓ₀, d, Y', m', u, s⟩ :=
    p.isGroupBaseChange.exists_hom_baseChange p.isGroupBaseChange (𝟙 _) χ,
    exists_torusModel (f f'.fullStructure) (by simp [p.baseHom_eq_comp, o, ← m.baseHom_eq])
  exact (exists_matrix_of_hom m m' ψ q.1.ne' (by simpa [p.lineBundle_eq_pull] using!
    (congr((ThetaObject.lineBundle _).picClass.pull $(a (𝟙 _)).1).trans congr(($l).pull _)))).elim
    fun z ⟨F, _, _⟩ ↦ (C.point_comp_proj ..).trans (OverMorphism.ext ((isPointOf_datumPoint.eq_iff
    (b := ⟨_, _, (realVecAction z <| P <| b.P ·), ⟨_, Y'.isSignedFrameFor⟩, s⟩) ⟨m', by
    rw [comp_left, ← hφ, h]; simp [fibrePower_ext_iff, ← p.comp_toFamily, ↓← F,
      IsGroupBaseChange.pullSection_comp_assoc, *]⟩).2 ⟨z, by erw [isLevelIso_iff, ← mul_assoc,
    ← (Units.ext (funext₂ fun a b ↦ sub_eq_zero.1 (eq_zero_of_forall_mul_integral
    fun x ↦ by simpa [mul_comm, mul_sub] using torsionClass_eq_iff.1 (m'.fullStructure.injective
    (.trans (by simp [*]) (torsionPoint_comp _ _ F (Pi.single b x))) :
    torsionClass (x • (γ i).2.1.2.col b) = _) a)) : _⁻¹ = _ * g)]; simpa⟩))
open And LineBundle PeriodMap ProjSpace Ideal.IsPrime
lemma nonempty_universalFamily {E} [Field E] [CMBase E] {D M} {R :
  Subalgebra _ E} [IsLocalization M R] (hM : M ≤ nonZeroDivisors (𝓞 E)) (hR : ∀ m, m.IsMaximal →
  D.IsGoodAt (.comap (algebraMap _ R) m)) : Nonempty (UniversalFamily D R) := by
  obtain ⟨_, _, ι, f, _, rep⟩ :=
    @Fintype.ofFinite D.levelTorsion (finite_torsionBy ⟨_, by simp [D.level_ne_zero]⟩),
    IsLocalization.isDedekindDomain _ hM R, ModuliPoint.exists_finite_reps D 0 D.level_ne_zero
  choose t k ht using fun (ω : D.levelTorsion) (a : AnalyticFamily D × _) ↦
    exists_isHomogCoords (v := ((a.1.torus a.2).thetaCoord · ((a.1.torus a.2).torsionLift ω)))
    (specOver R ℂ).hom (Function.ne_iff.1 (thetaCoord_vector_ne_zero _ _)).choose_spec.isUnit
  have Z {B} (y : B → _) :=
    Set.univ_nonempty.imp fun (C : ReducedClosure (Over.homMk (V := Over.mk _) _ <|
    k · <| y ·)) _ ↦ let c ω := ((hyperplaneBundle _).pull Limits.prod.fst).pull (C.proj ω).1
    have := HasProjEmbedding.pi C.incl (h := fun _ ↦ ⟨isProjEmbedding_projSpace⟩)
    have A : (LineBundle.pi c).IsProjEmbedding _ ∧ ∀ a ω, (c ω).IsHomogCoords (C.point a).1 _ :=
      ⟨isProjEmbedding_pi _ (fun _ ↦ isProjEmbedding_projSpace) C.hom_ext, by
      intros; rw [IsHomogCoords.pull_iff, ← Over.comp_left, C.point_comp_proj]; apply ht⟩
    have := LocallyOfFiniteType.isLocallyNoetherian C.W.hom
    intro A fun {ι} (j : ι → B) [Finite ι] hd ↦ have H z := ((Ideal.exists_le_maximal _ (C.W.hom
      z).2.1).elim fun m h ↦ (C.W.hom.isClosedMap.specializingMap ((PrimeSpectrum.le_iff_specializes
      _ ⟨m, h.1.isPrime⟩).1 h.2)).elim fun w k ↦ Exists₃.imp (fun _ O a ↦ imp_right fun e ↦
      intro (e.symm.subst k.1) (congr(D.IsGoodAt ($(Spec.map_preimage (a ≫ C.W.hom ≫ (specOver (𝓞 E)
      R).hom)) (closedPoint _)).1).mpr (hR _ (by erw [e, k.2]; tauto)))) (exists_arc _ hd w))
      intro H ((forall_and.1 (H · |>.elim fun i ⟨v, α, h, l, d⟩ ↦ by
    let x := (y (j i)).1.torus (y (j i)).2
    obtain ⟨hx, hc, G⟩ := h ▸ A.2 _, ?hc,
      x.hasGoodReduction_and_val_card_eq_one (by simpa [← h] using ?o (j i)) d
    choose i hi using (c · |>.exists_landsIn α)
    have n ω := ((hx ..).1.1 ((hi ω).comp _)).ne_zero
    have e ω j : Subtype.val _ = _ := ((hc ω).1 ..).1 _ _ (hi ω) ▸ (hx ..).2 j (n ω).isUnit
    have R ω := funext ((hc ω).1 _ · |>.1 _ α (hi ω)) ▸ (hc ω).2 ((hi ω).comp (specMap (residue _)))
    choose m hm using fun z ↦ Finite.exists_max (v <| x.thetaCoord · z)
    rw [← comap_closedPoint (residue _)] at l; refine ⟨⟨_, _, inferInstance, _, by exact l,
      _, x.isCutOutAt_reduction residue_surjective G.1 (q := fun z j ↦ ⟨_, by simp; bound⟩) (fun z ↦
      ⟨_, fun _ ↦ rfl, m z, by simpa using (x.thetaCoord_vector_ne_zero z <| by
      simpa [·, funext_iff] using hm z)⟩) (fun a ↦ ⟨_, by simpa using! e a, i a, by simp [*]⟩) R⟩, (
      G.elim x.exists_peak · |>.imp fun o H u _ w ↦
      l.mem_open (LineBundle.opens ..).2 (landsIn_iff_mem.1 ((R ..).1.2 ?_)))⟩
    have L i := by simpa [thetaShift, valuation_multiplier_mul_bicharacter]
      using congr(v ($(x.thetaShift_thetaCoord (frameTorsionClass_ratLift u.1) i) 0))
    simpa [v.mem_maximalIdeal_iff, e, le_mul_inv_iff₀, n, ← L, zero_lt_iff] using!
      H _ w (u + _))).elim ((IsUnit.mul_iff.1 (by_contra (exists_max_ideal_of_mem_nonunits · |>.elim
        fun m ⟨e, k⟩ ↦ (hR m e).elim fun n ⟨_, _, _, _, a, c, _⟩ ↦ notMem_of_isCoprime_of_mem c
      a (by simpa using add_mem ((mem_or_mem' k).resolve_right n.2) a)))).elim
        (exists_thetaFamily_of_points j
      hd (IsPreimmersion.of_isLocalization M).instMonoScheme ?o ?hc A.1 A.2)))
  have ⟨C, ⟨emb@⟨_, _, _⟩, hx⟩, K⟩ := Z id
  have hs {f} ⦃b⦄ n :
    HolomorphicAt (C.point ⟨f, ·⟩ |>.1) b := have ⟨_, h, k⟩ := f.exists_analytic_thetaCoord n
    .of_isHomogCoords emb (fun _ ↦ Finset.analyticAt_fun_prod _ fun ω _ ↦ (h ..).comp₂ analyticAt_id
               (f.analyticAt _ n (toRealVectors (ratLift f.frame _)))) (k.mono fun _ h ↦ .pi (w :=
      (·)) (hx _ · |>.smul h))
  choose b hb G using fun i ↦ exists_generic_member C.W.hom (f i).U.2 (f i).2 hs
  choose A X m hm using K (fun i ↦ (f i,
    b i)) (C.isSeparatingFamily.2.induction_on · isClosed_closure fun x ↦ by
    choose i a ha z r using rep (x.1.ballPoint 0 (x.2, 0))
    choose _ _ m _ using
      (Z ![x, (f i, a.1)]).choose_spec.2 id (ReducedClosure.isSeparatingFamily _).2
    simpa [(C.hom_ext fun ω ↦ by simpa using (Over.OverMorphism.ext (((ThetaFamily.IsPointOf.eq_iff
      (𝔪 := 1) ⟨m 0, rfl⟩ ⟨m 1, rfl⟩).2 ⟨z, levelGU_inf_one.ge r.mem_level, r.reflection_eq,
      r.sub_mem_lattice⟩ ▸ pointOf_hom :).symm.trans pointOf_hom) =≫ ReducedClosure.proj _ ω) :
      C.point x = C.point _)] using closure_mono (by simp) (G _ _ ha.1).mem_closure)
  choose i O a ha l gd using A
  refine ⟨‹_›, _, X, ⟨emb⟩, ?_, _, m, ?l, C.isSeparatingFamily.2⟩
  choose U h h' using fun z ↦
    smooth_of_immersion _ ((f _).holomorphic_immersive (m ⟨_, ·⟩) (hb _) (?l _ _ (hb _)))
    (ha z) (fun _ ↦ Over.w _) (FaithfulSMul.algebraMap_injective ..) (((f _).U.2.eventually_mem
    (hb _)).mono (G _)) fun _ τ h₁ h₂ ↦ ((m _).exists_model_over_arc (ha _)).elim fun m _ ↦
    tangent_bound h₁ (by simp [← RingHom.comap_ker, ker_residue, baseHom]; apply gd) m.fullStructure
    (m.isRigid_pullback (residue _) rfl) rfl (by simp [baseHom, reassoc_of% h₂, RingHom.comp_assoc])
  exact HasRingHomProperty.instIsZariskiLocalAtSource.of_iSup_eq_top U (top_unique fun z _ ↦
    le_iSup U z ((l z).mem_open (U z).2 (h z ⟨⟩))) h'
  exact fun f b h z ↦ match f.exists_analytic_thetaCoord h, (hs h).exists_isHomogCoords emb.1 with
    | ⟨_, u, v⟩, ⟨_, k, r⟩ => .of_isHomogCoords (X.embeds.mul emb) (hb := by simp; rfl) (fun _ ↦
      (u ..).mul ((k _).comp analyticAt_fst)) (((r.and v).prod_inl_nhds _).mono fun w h ↦ .mul
    (by simpa [hm] using! ((m _).hasThetaCoords.4 _).smul h.2) (by simpa [IsHomogCoords] using h.1))
  all_goals simp [c, (isLinearSystem_hyperplaneBundle.pull _).pull] <;> tauto
end FoldSeg10
section FoldSeg11
open Algebra _root_.RingHom CategoryTheory Classical ReducedClosure UniversalFamily Filter Finset
  Function IsLocalRing NumberField QuotientGroup AlgebraicGeometry.Spec Category
attribute [-simp] sup_of_le_left sup_of_le_right
attribute [local simp] datumPoint_eq_iff ModuliPoint.act ModuliPoint.isLevelIso_iff QuotientGroup.eq
  ratConj mul_assoc
lemma exists_model {E} [Field E] [CMBase E] {d₀} [HasQuadSubfield _ E]
  {R} {D : PEL E} (U : UniversalFamily D R) (hN : IsNeat D.Index D.𝔑) (hβ : D.β =
  algebraMap _ _ (QuadField.c₀ d₀))
  (hG : ∀ w, IsSafe D.𝔑 w → D.IsGoodAt w.1) ν [NeZero ν] : Nonempty (Model D.Index d₀ D.𝔑 ν R) := by
  choose M hM using exists_level_conj_mem (n := D.Index) hN.1
  let Q i := _ ⧸ ((levelGU _ (M i)).subgroupOf (levelGU D.Index D.𝔑)).normalCore
  let γ i (j : Q i × ↥(insert (M i, 1) (insert 1 i))) :=
    (j.2.1.1, ⟨_, mem_GUPlus_of_mem_levelGU j.1.out.2⟩ * j.2.1.2)
  obtain ⟨⟨hs, sj, m, hm⟩, C⟩ := U.fibrePower_spec ν, (ofNonempty : ∀ i, U.GraphClosure (γ i) ν)
  have L {i x a} k := ((C i).point_comp_proj a (⟦k⟧, x)).trans (c := datumPoint x.1.1
    (a.act (⟨_, mem_GUPlus_of_mem_levelGU k.2⟩ * x.1.2))) (datumPoint_eq_iff.2 ⟨1, by
    simpa using! hM i _ x.2 _ (QuotientGroup.eq.1 (k : Q i).out_eq.symm 1)⟩)
  choose p P pp using fun {i} (κ : levelGU _ D.𝔑) ↦
    (C i).exists_lift (·.act ⟨_, mem_GUPlus_of_mem_levelGU κ⁻¹.2⟩)
    (fun j ↦ (C i).proj (κ⁻¹ * j.1, j.2)) fun _ ↦ (·.1.out_eq ▸ (L _).trans (by simp [γ]))
  choose u hu using fun i ↦ (@factorsThrough_iff (Σ' g f, ∀ a, (C i).point a ≫ f = U.datumPoint 1
    (a.act g)) (_ ⧸ levelGU D.Index D.𝔑) _ (·.1) (·.2.1) ⟨(C i).proj ⟨1, 1, by simp⟩⟩).1 fun p q e ↦
    (isSeparatingFamily _).hom_ext fun a ↦ by simpa [p.2.2, q.2.2] using ⟨1, by simpa using e.symm⟩
  let s i := {g | ∃ h, ∀ a, point _ a ≫ u i ⟦g⟧ = datumPoint 1 (a.act ⟨g, h⟩)}
  have o i : 1 ∈ s i := ⟨one_mem _, fun _ ↦ congr(_ ≫ $(hu i)
    ⟨1, (C i).proj ⟨⟦1⟧, 1, by simp⟩, by simp [↓L]⟩).symm.trans (by simp [↓L])⟩
  have hc {i} := by simpa using (o i).2
  have T {g k i j f} (h : ∀ a, (C i).point a ≫ f = (C j).point (a.act ⟨g, k⟩)) ⦃q⦄ (H : q ∈ s j) : f
    ≫ u j ⟦q⟧ = u i ⟦g * q⟧ := congr($(hu i) ⟨⟨_, mul_mem k H.1⟩, _, by simp [reassoc_of% h, H.2]⟩)
  refine ⟨_, _, s, u, o, fun j hg ↦ (eventually_all.2 fun x ↦ eventually_finset_mem_atTop ((γ j
    x).1, (⟨_, hg⟩ * (γ j x).2 :))).mono fun i h ↦ ((C j).exists_lift (·.act ⟨_, hg⟩) ((C i).proj
    ⟨⟦1⟧, _, mem_insert_of_mem <| mem_insert_of_mem <| h ·⟩ :) (by simp [↓L])).elim fun f h ↦
    ⟨⟨hg, by simp [← by simpa using T h.2 (o j), ← assoc, *]⟩, f, T h.2⟩, (.of <| Q ·), fun _ ↦
    lift _ ⟨⟨(.of <| p ·), End.ext ((isSeparatingFamily _).hom_ext (by simp [pp]))⟩, fun _ _ ↦
    End.ext ((isSeparatingFamily _).hom_ext (by simp [pp, ← assoc]))⟩ fun κ h ↦ End.ext <|
    hom_ext _ fun j ↦ by erw [P,
    mul_eq_right.2] <;> simp [h], fun _ ↦ Quot.ind (⟨·⁻¹, T (pp _)⟩), m, _, (C · |>.point_surjective
    hc), by simp [*], fun g α a h ↦ by simp [reassoc_of% h.2, *, -ModuliPoint.act], _,
    hs, fun i ↦ isGaloisCovering_of_complex_points (fun k _ _ f ↦ let := f.toAlgebra
    ((IsAlgebraic.trans _ (𝓞 E) _).tower_bot_of_injective Subtype.val_injective).injective_tower_top
      R Int.cast_injective) (Quot.ind fun _ ↦ (T (pp _) (o _)).trans (by congr 1; simp))
    (sj.surjective _ _ (congr($(hc ·).1))) (((C i).point_surjective hc).forall₂.2 fun x y e ↦
    existsUnique_of_exists_of_unique ((datumPoint_eq_iff.1 (hc x ▸ hc y ▸ e)).elim fun z r ↦
    ⟨⟦⟨_, r.mem_level.1⟩⟧, (pp ..).trans ((C i).exists_level_point_eq.choose_spec ⟨by simp,
    r.reflection_eq, by simpa using r.sub_mem_lattice⟩)⟩) (mk_surjective.forall₂.2 fun κ κ' e e' ↦
    QuotientGroup.eq.2 fun q ↦ (datumPoint_eq_iff.1 (L _ ▸ L _ ▸ (pp
    ..).symm.trans (e ▸ e' ▸ pp ..) =≫ (C i).proj ⟨⟦κ * q⁻¹⟧, _, mem_insert_self
    ..⟩)).elim fun z r ↦ ?_)), fun i g α a _ _ h x y z ↦ ?_, fun w H i _ N h l m _ f k _ _ x X ↦ ?_⟩
  · cases hN.2 x.isSignedFrame
      (by simpa [mul_mem_cancel_left] using mul_mem r.mem_level.1 q.2) r.reflection_eq
    simpa using r.mem_level.2
  · choose f h0 e _ hb using exists_ball_family a
    obtain ⟨⟨K, k⟩, σ, hσ⟩ := hb x y z, ((C i).holomorphicAt_point a.P 0 h0).exists_isJet .id
    have T x :
      IsJet (f.ballPoint a.P · |> (C i).point |>.left) 0 (.applyₗ x) (specMap (TrivSqZeroExt.map
      (.applyₗ x)).1 ≫ σ) := (by simp [PointFn.isRegularOn_ofSection _ _, hσ · · ·, LandsIn.comp])
    have S x := ((T x).comp_hom _).congr (.of_forall fun _ ↦ congr($(hc _).1))
    exact ⟨.of ℂ _, ⟨Over.homMk _ ((hσ.comp_base_eq fun _ ↦ Over.w _).trans (map_comp ..).symm)⟩,
      K, by simp [(f.torus 0).isPeriodMap.finrank_eq_abelianDim], congr(⟨$(Over.OverMorphism.ext
      (e ▸ hσ.fst_comp :))⟩), fun x y e ↦
      sub_eq_zero.1 ((U.isHolImmersionAt_datumPoint 0 h0).2 _ (isFirstOrderConst_iff.2 fun U f i ↦
      by simpa using! congr($((S x U f i).2.symm.trans (congr(PointFn.ofSection f _ $e.1.1).trans (S
      y U f i).2)).snd))), fun x ↦ ULift.up_inj.2 (Over.OverMorphism.ext (((isJet_comp_iff
      (ContinuousLinearMap.mk K).hasFDerivAt (U.isHolImmersionAt_datumPoint _ (by simpa)).1).2
      (K.map_zero ▸ S _)).unique (((T x).comp_hom _).congr (k.1.mono fun q r ↦ congr($(((reassoc_of%
      h.2) _ _).trans ((hm ..).trans (datumPoint_eq_iff.2 ⟨_, by simpa using r⟩))).1)))).symm), k.2⟩
  obtain ⟨z, ρ, ⟨⟩, -⟩ := exists_countable_residue_point (Over.hom _) x
  choose V α b ρ' r S using (C i).exists_arc z
  rcases ρ.charP ρ.injective, charP_of_injective_ringHom ρ'.injective, @Fintype.toLocallyFiniteOrder
  refine (U.congruence_step hβ (S (hc b)) residue_surjective rfl (w.1.isMaximal.eq_of_le (ker_ne_top
    _) fun a h ↦ ?_) (hG _ H) H (fun _ ↦ f ▸ pow_mul' ..) (S <| h · |>.2 b)).elim fun W G ↦ .mono
    (.mono ((FreeAbelianGroup.equivFinsupp _).injective (Finsupp.ext
    (IncidenceAlgebra.moebius_inversion_bot _ 0 (fun A ↦ by by_cases W ≤ A <;> simp [‹_›, sum_ite,
    ← @Int.cast_inj ℂ, prod_eq_zero (i := 0), q_binomial_submodule,
    zero_lt_iff, ne_bot_of_le_ne_bot G.1, ← card_ResField, Finsupp.single_apply, -zsmul_eq_mul,
    sum_fiberwise_eq_sum_filter, filter_filter]) · |>.trans (by simp)))) G.2) fun A B t ↦ ?_
  · erw [ThetaObject.baseHom, ← assoc, preimage_comp]
    simpa [← reassoc_of% r, ← (u i ⟦1⟧).w] using X _ (N a h)
  simp [specMap] at t
  simp [← reassoc_of% r, ← map_comp_assoc, ← CommRingCat.ofHom_comp, ← iterateFrobenius_comm] at t ⊢
  simpa [cancel_epi] using t
end FoldSeg11
