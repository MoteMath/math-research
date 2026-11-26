import Lib.General.Geometry.SeparatingPoints
import Lib.Shimura.Deformation.DrinfeldLifting
import Lib.Shimura.TraceFormula.MarkedEqDefinite
section FoldSeg0
open CategoryTheory AlgebraicGeometry Spec Set IsLocalRing CommRingCat TrivSqZeroExt Algebra Module
  TensorProduct MvPolynomial KaehlerDifferential IsLocalization.Away Localization LinearMap RingHom
  Cardinal PointFn HasRingHomProperty IsStandardSmoothOfRelativeDimension
attribute [local simp] map_inj ConcreteCategory.hom_ext_iff
lemma smooth_of_immersion {d X R b u k} {φ : (Fin d → ℂ) → _} {V : ValuationSubring ℂ}
  {a} [Field k] {ϑ : V →+* k} [IsLocalHom ϑ] (s : X ⟶ Spec R) [LocallyOfFiniteType s] [IsDomain R]
  [IsIntegrallyClosed R] (h : IsHolImmersionAt φ b) (ha : specMap V.subtype ≫ a = φ b) (hs : ∀ w,
  φ w ≫ s = Spec.map u) (hi : (⇑u).Injective) (hg : ∀ᶠ w in nhds b, φ b (closedPoint ℂ) ⤳ φ w
  (closedPoint ℂ)) (H : ∀ (M : ModuleCat k) τ, let t := specMap ϑ ≫ a; sqZeroReduction k _ ≫ τ = t →
    τ ≫ s = specMap (algebraMap k _) ≫
  t ≫ s → (∀ l, specMap (map (Dual.eval k M l)).1 ≫ τ = specMap (algebraMap k _) ≫ t → l = 0) →
  finrank k M ≤ d) : ∃ U, LandsIn a U ∧ SmoothOfRelativeDimension d (U.ι ≫ s) := by
  have ⟨W, hW, hb⟩ := exists_isAffineOpen_landsIn a
  let B := Γ(X, W)
  obtain ⟨⟨ρ, hρ⟩, α, rfl⟩ := map_surjective (hW.fromSpec ≫ s), landsIn_opensRange.1
    (hW.opensRange_fromSpec ▸ hb)
  have := Spec_iff.1 (hρ ▸ locallyOfFiniteType_comp ..)
  algebraize [ρ.hom, ϑ.comp α.1]
  have ⟨ι, x, _, hx, li⟩ := exists_linearIndependent' k (mk B k _ 1 ∘ D R B)
  simp [range_comp _ (D ..), ← Submodule.baseChange_span, span_range_derivation] at hx
  have ⟨i⟩ : #ι ≤ #(Fin d) := by grw [li.cardinalMk_le_finrank, ← Subspace.dual_finrank_eq,
    H (.of k _) (specMap {toFun b := .inl (ϑ (α b)) + .inr (applyₗ (mk B k _ 1 (D R B b))), ..} ≫
    hW.fromSpec) _ _ fun l ↦ ext_on_range hx ∘ _] <;> simp [← hρ, ← Spec.map_comp, B,
    ← map_comp_assoc, cancel_mono, forall_and, TrivSqZeroExt.ext_iff, tmul_add,
    ← algebraMap_toAlgebra ρ.hom] <;> tauto
  obtain ⟨z, rfl⟩ := i.2.surjective_comp_right x
  let p := PrimeSpectrum.comap (algebraMap B k) ⊥
  let A := MvPolynomial (Fin d) R
  let e := mvPolynomialBasis R (Fin d)
  algebraize [(Ideal.ResidueField.liftₐ p.1 (ofId ..) le_rfl fun _ ↦ .mk0 _).1, (eval₂AlgHom R z).1]
  obtain ⟨hw, _, _, _ : IsIntegrallyClosed (MvPolynomial (Fin d) R)⟩ := ha ▸ hb.comp _,
    FiniteType.of_restrictScalars_finiteType R A B, IsStandardSmooth.of_basis_kaehlerDifferential e
    (by simp [e]), d.rec (.of_equiv (isEmptyRingEquiv ..).symm) fun _ _ ↦ .of_equiv
    (finSuccEquiv R _).symm.toRingEquiv
  have ⟨f, hf, C, π, hπ⟩ := (unramifiedLocus_eq_compl_support.ge (
    have := (mem_support_iff_nontrivial_residueField_tensorProduct p).1 ·
    have := (AlgebraTensorModule.cancelBaseChange B p.1.ResidueField k k Ω[B⁄A]).symm.nontrivial
    ne_zero_of_surjective (baseChange_surjective k (map_surjective R A _)) (ext_on_range hx (by
    simp [← (id (aeval_X ..) : algebraMap A B _ = _)]))) :
    IsUnramifiedAt A _).exists_hasStandardEtaleSurjectionOn
  obtain ⟨⟨β, rfl⟩ : ∃ β, ofHom (algebraMap B (Away f)) ≫ β = α, ⟨⟨G⟩⟩, r⟩ := ⟨_, hom_ext (lift_comp
    _ (.of_map ϑ _ (.mk0 _ hf)))⟩, instIsStandardEtaleRing C,
    (isRegularOn_ofSection · |> (h.1 · hw))
  algebraize [β.1, β.1.comp (algebraMap A _)]
  have hx := (G.hasMap.map π).map (algHom _ _ V)
  with_unfolding_all have := (faithfulSMul_iff_algebraMap_injective A V).2 (.of_ker _ fun Q hQ ↦
   map_injective _ hi (funext (eq_zero_of_submersion (.eval_mvPolynomial _)
   (hasStrictFDerivAt_pi.2 (z · |> r |>.2.hasStrictFDerivAt)) (ker_eq_bot_iff_range_eq_top.1
   (bot_unique fun v h0 ↦ h.2 v ((h.1.exists_isJet _).elim fun τ hτ ↦ by
   convert hτ
   obtain ⟨τ, rfl⟩ :=
     landsIn_opensRange.1 (hτ _ 0 (landsIn_opensRange.2 ⟨β ≫ _, by simpa using ha⟩)).1
   algebraize [τ.hom.comp (algebraMap A _)]
   simpa [← hτ.fst_comp, specMap] using congr(specMap $((FormallyUnramified.of_surjective π hπ).ext'
     _ ⟨2, kerIdeal_sq ℂ ℂ⟩ ⟨(inlHom ..).comp ((fstHom ..).1.comp τ.hom), fun Q ↦ by
     have := And.intro (hτ.comp_base_eq hs) (hτ W <| z ·)
     simp [← hρ, ← map_comp_assoc, ← Spec.map_comp, funext_iff] at this h0
     apply Q.induction_on <;> simp +contextual [A, algebraMap_toAlgebra, algebraMap_eq_inl,
       IsScalarTower.algebraMap_apply A B, *]⟩ ⟨τ.hom, by tauto⟩ (by tauto)).1 ≫ _))))
   ((r 0).1.mp (hg.mono fun w h k ↦ by
   simpa [← (landsIn_iff_mem), landsIn_basicOpen, ofSection_eq, k,
     ← (map_injective (by simp [*, reassoc_of% map_evalSection_fromSpec]) : ρ ≫ evalSection _ k =
     u)] using! mt (h.mem_open (X.basicOpen (aeval z Q)).2)
     (ha ▸ ((hW.fromSpec_preimage_basicOpen _).le · (·.ne_zero congr($hQ)))))))))
  have hm p := minpoly.isIntegrallyClosed_dvd (p := p) ⟨_, G.monic_f, hx.1⟩
  have ⟨g, hg⟩ := hm _ hx.1
  have := Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 (.of_equiv (.ofBijective (awayMapₐ π
    _) ⟨awayMap_injective_iff.2 fun c (k : π c = 0) ↦ (G.exists_mul_aeval_x_g_pow_eq_aeval_x c).elim
    fun a ⟨n, ha⟩ ↦ ⟨1, by grw [← zero_dvd_iff, ← (G.hasMap.2.pow n).dvd_mul_right, mul_assoc, ha,
    pow_one, ← map_mul, ← hm a (by simp [a.aeval_algHom_apply, ← ha, k]), mul_comm, ← hg,
    G.hasMap.1]⟩, mapₐ_surjective_of_surjective _ hπ⟩))
  refine ⟨_, landsIn_opensRange (c := specMap (algebraMap ..) ≫ specMap (algebraMap _ (Away f)) ≫
    hW.fromSpec).2 ⟨ofHom (awayLift β.hom _ (by simpa [hg, g.aeval_algHom_apply] using!
    hx.isUnit_derivative_f : _ ∧ _).2), by rw [← map_comp_assoc, ← ofHom_comp]; simp⟩, ?_⟩
  simpa [← Scheme.Hom.isoOpensRange_inv_comp, ← hρ, ← Spec.map_comp] using comp_of_isOpenImmersion
    _ _ _ (Spec_iff.2 (locally_of isStandardSmoothOfRelativeDimension_respectsIso _ (by
    simpa [← isStandardSmoothOfRelativeDimension_algebraMap] using! ((iff_of_isStandardSmooth _).2
      (rank_eq_card_basis e)).trans _ 0 ..)))
end FoldSeg0
section FoldSeg1
noncomputable section
open CategoryTheory AlgebraicGeometry Limits RingHom Over Set Scheme IsArtinianRing Pi pullback
  CommRingCat Ideal Quotient Algebra TensorProduct Function Finset Module Spec OverMorphism
  FormallyUnramified LocallyQuasiFinite IsOpenImmersion IsLocalization IsIntegralClosure Fint
variable {S} {b : Spec ⟨ℂ⟩ ⟶ S} {J A : Type} [Finite J] {Z : J → _} (F : ∀ j, A → (Over.mk b ⟶ Z j))
structure ReducedClosure where
  W : _
  incl : W ⟶ ∏ᶜ Z
  point _a : _ ⟶ W
  point_incl a : point a ≫ incl = lift (F · a)
  isClosedImmersion : IsClosedImmersion incl.left
  isSeparatingFamily : IsSeparatingFamily (point · |>.left)
attribute [instance] ReducedClosure.isClosedImmersion
variable {F} (C : ReducedClosure F) {J' Z' F'} [Finite J'] {C' : @ReducedClosure S b J' A _ Z' F'}
instance : IsReduced C.W.left := C.isSeparatingFamily.1
def ReducedClosure.proj j := C.incl ≫ Pi.π Z j
@[simp] lemma ReducedClosure.point_comp_proj a j : C.point a ≫ C.proj j =
  F j a := by simp [proj, reassoc_of% point_incl]
instance : Nonempty (ReducedClosure F) := (exists_reduced_closure _).elim fun _ ⟨i, _, c, h, r⟩ ↦
  ⟨.mk (i ≫ _), homMk i, fun a ↦ homMk _ (by simp [reassoc_of% h]), (ext <| h ·), c, r⟩
lemma ReducedClosure.hom_ext {T} {f g : T ⟶ _} (h : ∀ j, f ≫ C.proj j = g ≫ C.proj j) : f = g :=
  (mono_of_mono_left _).1 _ _ (Pi.hom_ext _ _ h)
lemma ReducedClosure.exists_lift (σ : A → _) (f : ∀ _, _ ⟶ _) (h : ∀ a j, C'.point a ≫ f j =
  F j (σ a)) : ∃ g, (∀ j, g ≫ C.proj j = f j) ∧ ∀ a, C'.point a ≫ g = C.point (σ a) :=
  have ⟨g, e⟩ := exists_lift_of_dense_preimage _ (lift f).1 (C'.isSeparatingFamily.2.mono
    (forall_mem_range.2 fun a ↦ ⟨_, congr($((C.4 (σ a)).trans (by aesop : _ = _ ≫ _)).1 _)⟩))
  have G j : homMk g (by simpa using e =≫ hom _) ≫ _ = _ := lift_comp_π f _ ▸ ext (e =≫ _)
  ⟨_, G, fun _ ↦ C.hom_ext (by simp [*])⟩
variable {R : CommRingCat} {W Z : Over (Spec R)} [IsProper W.hom] [IsSeparated Z.hom]
  {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* End W}
attribute [local instance 10] Quotient.field rightAlgebra finitePresentation_of_projective
  IsFinite.of_isProper_of_locallyQuasiFinite finite_of_free
lemma etale_of_simply_transitive {A B G} [CommRing A] [CommRing.{0} B] [Algebra A B] [Module.Finite
  A B] [Group G] [Finite G] (I : Injective (algebraMap A B)) (σ : G →* (B →ₐ[A] B)ᵐᵒᵖ) (H :
  ∀ k [Field.{0} k] [Algebra A k] (x y : B →ₐ[A] k), ∃! g, ∀ b, x ((σ g).unop b) = y b)
  (V : ∀ s, (∀ g, (σ g).unop s = s) → ∃ a, algebraMap A B a = s) : Etale A B := by
  let t := (∑ g, (σ g).unop.toLinearMap).codRestrictOfInjective (Algebra.linearMap ..) (id I)
    fun s ↦ id (V _ fun g ↦ by simpa using Equiv.sum_comp (.mulRight g) (σ · |>.unop s))
  choose u E using exists_forall_sub_mem_ideal (I := fun g ↦ ker (productMap (σ g).unop (.id ..)))
    (fun _ _ ↦ isCoprime_iff_sup_eq.2 ∘ Not.imp_symm (exists_le_maximal _ · |>.elim fun m ⟨_, _⟩ ↦
    by apply (H _ (.comp (mkₐ _ m) includeRight) (.comp (mkₐ ..) includeLeft)).unique <;>
      simp_all [Ideal.Quotient.eq, ↓sup_le_iff, IsConcreteLE.le_iff])) (Pi.single 1 1)
  obtain ⟨_, y, x, ⟨⟩⟩ := exists_sum_tmul_eq u
  have K z : ∑ i, t (z * y i) • x i = z := by simp_all [Algebra.smul_def, t, sum_mul, sum_comm,
    ← linearMap_apply, mul_assoc, ← mul_sum]
  have J s := congr(∑ i, x i ⊗ₜ[A] $(K (s * y i)))
  simp [↓tmul_sum, ↓← smul_tmul, sum_comm, ← sum_tmul, mul_right_comm, K] at J
  rcases iff_exists_tensorProduct.2 ⟨_, fun s ↦ (sub_mul ..).trans (congr(_ * $(J 1) -
    _).trans (by simp [mul_sum, J])), by simpa using E 1⟩, Projective.of_split
    (.pi (t.comp ∘ .mulRight A ∘ y)) (Fintype.linearCombination _ x) (by bound)
  exact .of_formallyUnramified_of_flat
lemma isGaloisCovering_of_complex_points [Countable R] [Algebra R ℂ] (hR :
  ∀ k [Field.{0} k] [CharZero k] (f : R →+* k),
  Injective f) (b : ∀ g, (s g).asHom ≫ c = c) (hc : AlgebraicGeometry.Surjective c.left)
    (o : ∀ y z :
  specOver R ℂ ⟶ W, y ≫ c = z ≫ c → ∃! g, y ≫ (s g).asHom = z) : IsGaloisCovering c s := ⟨b, hc, by
    intros
    obtain ⟨x, ⟨⟩, ⟨⟩⟩ := lift' _ _ ‹_›
    obtain ⟨z, φ, ⟨⟩, _⟩ := exists_countable_residue_point (fst .. ≫ hom W) x
    set j := fromSpecResidueField _ z
    choose ψ f using exists_ringHom_complex_extend (@hR _ _ φ.charZero (Spec.preimage (j ≫ fst .. ≫
      hom W)).hom) (hR _ (algebraMap ..)) (by simp [Cardinal.aleph0_le_continuum.trans'])
    specialize o (homMk (specMap ψ ≫ j ≫ fst ..) ?_) (homMk (specMap ψ ≫ j ≫ snd ..) ?_) <;>
    simp_all [OverMorphism.ext_iff, cancel_epi, ← f, ← c.w, condition_assoc, -w]⟩
lemma IsGaloisCovering.smoothOfRelativeDimension_baseChange [IsDomain R]
    (G : IsGaloisCovering c s) d
  [IsReduced W.left] [SmoothOfRelativeDimension d Z.hom] k [Field k] [CharZero k] [Algebra R k]
  [FaithfulSMul R k] : SmoothOfRelativeDimension d (snd W.hom (specMap (algebraMap R k))) := by
  let ι : Spec ⟨functionField _⟩ ⟶ Spec R := fromSpecStalk ..
  obtain ⟨⟨ψ, e⟩, b, hc, o⟩ := (⟨IsFractionRing.lift (FaithfulSMul.algebraMap_injective R k), (_ ≫=
    fromSpecStalk_eq ..).trans (map_comp .. ▸ congr(specMap $(lift_comp _)))⟩ : ∃ ψ, specMap ψ ≫ ι =
    specMap (algebraMap R k)), G
  let π := fst Z.hom ι
  let q := snd c.1 π
  have C {k} [Field k] y := (charZero_iff (@preimage _ ⟨k⟩ (y ≫ snd Z.hom ι)).1.injective).1
    ψ.charZero
  have O {X p} (q : X ⟶ _) (h : p ≫ c.1 = q ≫ π) w v (e : q v = q w) : ∃ g,
    (s g).asHom.1 (p w) = p v :=
    by obtain ⟨t, ⟨⟩, ⟨⟩⟩ := Pullback.exists_preimage_pullback _ _ e
       exact fromSpecResidueField_apply t _ ▸ (@o _ _ (C (fromSpecResidueField _ t ≫ fst .. ≫ q))
    (_ ≫ _ ≫ p) (_ ≫ _ ≫ p) (by grind [condition])).exists.imp fun _ ↦ (congrArg (· default) ·)
  have et {P} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] {A B : CommRingCat} {_ : Algebra P A}
    (_ : Etale P A) {_ : Algebra A B} (_ : Module.Finite A B) [IsReduced B] {p u} [Mono p]
    (hp : IsPullback p (specOver A B).hom c.1 (u ≫ π)) : Etale A B := ?_
  rcases @isReduced_of_isReduced_stalk _ (⟨(fst c.1 π).stalkMap_surjective · |>.forall.2 (by simp
    [IsNilpotent.map_iff, stalkMap_injective_of_flat])⟩),
    of_finite_preimage_singleton q (q.surjective.forall.2
    (((finite_range _).preimage (fst _ π).injective.injOn).subset <| O _ condition ·))
  refine e ▸ c.w ▸ (smoothOfRelativeDimension_isStableUnderBaseChange d).1
    (.of_right' (.of_hasPullback ..) (.paste_vert (.of_hasPullback ..) (.of_hasPullback ..)))
    (d.zero_add ▸ smoothOfRelativeDimension_comp (hf := ⟨fun x ↦ ?_⟩) ..)
  choose U _ V h hx e hs using (inferInstance : SmoothOfRelativeDimension d (snd _ ι)).1 (q x)
  obtain ⟨⟨⟩, r⟩ := U.eq_bot_or_top.resolve_left (·.le (e hx)), h.preimage q
  exact ⟨_, h, _, r, hx, _, etale_iff_isStandardSmoothOfRelativeDimension_zero.1 (et
    hs.exists_etale_mvPolynomial.choose_spec.2 (q.app_eq_appLE ▸ q.finite_app _ h) ((isPullback _ _
    _ _ (h.SpecMap_appLE_fromSpec q r _).symm (by simp)).flip.paste_horiz (.of_hasPullback ..)))⟩
  have L k [CommRing k] [Algebra A k] y hy : ∃ χ : B →ₐ[A] k, specMap χ ≫ p = y :=
    (specOver.map_bijective.2
    (homMk _ (hp.lift_snd y _ hy))).imp fun _ e ↦ by simpa using! congr($e.1 ≫ p)
  choose a h0 using fun g ↦ L B (p ≫ (s g).asHom.1) (by simp [← comp_left, b, hp.w])
  let F := FractionRing P
  let N := A ⊗[P] F
  obtain ⟨h1, hm⟩ := h0 1, (h0 <| · * ·), fun {k} [Field k] [Algebra A k] ↦
    C ((specOver A k).hom ≫ u), Etale.of_equiv (commRight P F A)
  obtain H := fun {k} [Field k] [Algebra A k] (x y : B →ₐ[A] k) ↦ o k (specMap x ≫ p) (specMap y ≫
    p) (by simp [hp.w, ← Spec.map_comp_assoc, ← ofHom_comp]), isReduced_of_field F N, of_finite F N
  simp [← h0, ← reassoc_of% h0, ← Spec.map_comp_assoc, cancel_mono, cancel_mono_id, Spec.map_inj,
    -Spec.map_comp, ConcreteCategory.hom_ext_iff] at h1 hm H
  let Ω (m : MaximalSpectrum N) := AlgebraicClosure (_ ⧸ m.1)
  have inj := ((equivPi _).injective_comp _).2 (.piMap (Ω · |> algebraMap _ |>.injective))
  let χ := AlgHom.pi fun m ↦ (L (Ω m) _ (exists_point_over _ (hc.1 _)).choose_spec).choose
  have hA := χ.comp_algebraMap ▸ @id (Injective (algebraMap ..)) (inj.comp
    (includeLeft_injective (S := P) (IsFractionRing.injective ..)))
  refine etale_of_simply_transitive (.of_comp (f := χ) hA) ⟨⟨(⟨a ·⟩), congr(⟨$(AlgHom.ext h1)⟩)⟩,
    (congr(⟨$(AlgHom.ext <| hm · ·)⟩))⟩ @H fun s hb ↦ ?_
  obtain ⟨v, hv : algebraMap _ _ v = _⟩ := (reindex_equiv (equivPi _)).2.1.1 ((range_piMap _).ge
    fun m _ ↦ (InfiniteGalois.mem_bot_iff_fixed _).2 fun σ ↦ (H
    ((σ.restrictScalars A).toAlgHom.comp (.comp (evalAlgHom _ _ m) χ)) _).exists.elim (hb · ▸ · _))
  obtain ⟨x, ⟨⟩⟩ := toIntegralClosure_bijective_of_smooth (B := F).2.comp (includeLeft_surjective A
    A (isIntegral_iff.1 ·.2 |>.imp (by bound))) ⟨v, .tower_bot inj (hv ▸ .map χ (.of_finite ..))⟩
  use x, sub_eq_zero.1 (nilpotent_iff_mem_prime.2 fun q i ↦ (exists_ideal_over_prime_of_isIntegral
    (q.under A) (ker χ) (comap_bot_le_of_injective _ hA)).elim fun Q ⟨hQ, j, e⟩ ↦ (O (_ ≫ u) hp.w
    ⟨Q, j⟩ ⟨q, i⟩ congr(u ⟨$e.symm, _⟩)).elim fun g e ↦ congr($(p.injective (congr($(h0 g) _
    ).trans e)).1).le (hQ (by erw [map_sub, hb]; simpa))).eq_zero
open NumberField Matrix Polynomial LinearMap Nat ModuliPoint QuotientAddGroup
variable {E} [Field E] [CMBase E] {d₀ n} [Fintype n] [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν} {R :
  _} (X : Model n d₀ 𝔑 ν R) [Nonempty n]
def IsNullHecke ν h (b : heckeAlgebra n ℂ 𝔑) := IsRegularHecke b → ∀ α : Fin ν → _, (countTerm True
  b 1).support.Finite ∧ ∑ᶠ x, countTerm True b (localTerm (2 * α) · · |>.coeff h) x = 0
def OccursInWeight a ν (θ : SafePlace 𝔑 → ℕ → ℂ) h := ∀ s (c : List _ → ℂ), ∑ L ∈ s,
  c L * (L.map ↿θ).prod = 1 →
  ¬∀ b : heckeAlgebra (Fin a) .., IsNullHecke ν h (b * ∑ L ∈ s, c L • (L.map tauHecke).prod)
attribute [local simp] mul_assoc ratConj_eigenReflection isLevelIso_iff map_smul'
  Matrix.map_sub prod_ne_zero_iff
  eval_prod eval_multiset_prod charpoly_map det_one_sub_smul_eq_prod_roots Nat.card_pi
lemma Model.isNullHecke_of_isNullFamily (hN : IsNeat n 𝔑) {b : heckeAlgebra _ ℂ 𝔑} {h}
  (hF : ∀ᶠ i in .atTop, ∀ α, IsNullFamily (X.leg i ⟦·.out⟧ ≫ X.m α) (heckeCosetFn b) X.d h) :
  IsNullHecke ν h b := fun hr α ↦ let f := heckeCosetFn b
  have o (c : f.support) := heckeAlgebra.mem_GUPlus_of_ne_zero (by aesop : f c.1.out ≠ 0)
  (hF.and (.all (X.eventually_translate ∅ <| o ·))).exists.elim fun i ⟨hF, ok⟩ ↦ by
  let B (z : GL n E) j := 1 - (2 * α j).val • z.1
  let L x z j := (frameLattice x).comap (realVecAction (B z j)).toAddMonoidHom
  let Q x z j := _ ⧸ (frameLattice x).addSubgroupOf (L x z j)
  have hd {x z} (h : f (γ z x) ≠ 0) j : frameLattice x ≤ L x z j ∧ (B z j).det ≠ 0 ∧
    Nat.card (Q x z j) = ∏ σ : E →+* ℂ, σ (B z j).det := ?_
  let Fx p (t : _ × _) := f (γ t.1 (x p)) ≠ 0 ∧ p.reflection = eigenReflection True t.1 t.2 ∧ ∀ j,
    p.P j ∈ L p.x t.1 j
  choose q hq using X.point_surjective i
  obtain ⟨hF, g⟩ := hF _ _, X.covering i
  extract_lets S at hF
  have ra c {p} z : (act p ⟨_, o c⟩ (2 * α)).IsLevelIso (levelGU _ 𝔑) z p ↔ γ z p.x = c.1 ∧ ratConj
    z p.reflection = p.reflection ∧ ∀ j, p.P j ∈ L p.x z j := by simp +zetaDelta [act,
                      sub_mem_comm_iff, Quotient.mk_eq_iff_out.trans QuotientGroup.leftRel_apply]
  have e c y := by simpa only [*, ← point_leg] using
    (X.point_eq_iff i _ (q y)).trans (exists_congr (ra c))
  choose! r hs un using fun s (h : s ∈ S) ↦ (((e ..).1 h.symm).elim fun z ⟨e, H⟩ ↦
    ((isReflection_eigenReflection (hr (e ▸ (f.3 _).1 s.1.2))).2 _ (ModuliPoint.isReflection _)
    H.1).elim fun μ U ↦ ⟨(z, μ), by grind, fun t a ↦ by grind
    [mul_inv_eq_one.1 (hN.2 (isSignedFrame _) (by simpa [← a.2, QuotientGroup.eq] using e)
    (by simpa [a.1.2] using H.1))]⟩ : ∃! t, Fx (q s.2.1) t ∧ γ t.1 (q s.2.1).x = s.1.1)
  let cl := Quotient.mk (MulAction.orbitRel (GL n E) (MarkedTriple (levelGU n 𝔑) n))
  have fix {p q z t} (hz : p.IsLevelIso _ z q) (h : Fx p t) : Fx q (z * t.1 * z⁻¹, t.2) :=
    have k := heckeAlgebra.heckeCosetFn_conj hz.mem_level ▸ by simpa using h.1
    ⟨k, by simp [← hz.reflection_eq, h.2], fun j ↦ (add_mem_cancel_left
      ((hd k _).1 (hz.sub_mem_lattice j))).1 (by simpa +zetaDelta [-sub_mulVec, mul_sub,
      sub_mul] using realVecAction_mem_frameLattice hz.mem_level.2.1.isIntMatrix (h.2.2 j))⟩
  have H {p q s t} (h : Fx p t) (hs : Fx q s) : cl (p.x, t) = cl (q.x, s) ↔ ∃ w,
    q.IsLevelIso (levelGU _ 𝔑) w {p with P j := realVecAction w (q.P j)} ∧ (w * s.1 * w⁻¹, s.2) =
    t := Quotient.eq.trans (exists_congr fun w ↦ Prod.ext_iff.trans (.symm (and_congr_left fun e ↦
    .trans (by simp [hs.2, h.2, ← e]) (QuotientGroup.eq.symm.trans comm))))
  have hc {p z δ} (e : X.point i p ≫ _ = z) := g.1 δ ▸ (reassoc_of% e) _
  have bij p {t} (h : Fx p t) : {s ∈ S | cl ((q s.2.1).x, r s) = cl (p.x, t)}.BijOn (·.2.1) (.range
    fun u : (∀ j, Q p.x t.1 j) × _ ↦
      X.point i {p with P j := (u.1 j).out} ≫ (X.deck i u.2).asHom) :=
    ⟨fun s ⟨m, a⟩ ↦ ((H h (hs s m).1).1 a.symm).elim fun w ⟨R, e⟩ ↦ let u j : Q .. := ⟦⟨_, (e ▸ fix
    R (hs s m).1).2.2 j⟩⟧; (g.3 ℂ _ _ congr($((hq _ ▸ (X.point_eq_iff i _ {p with P j :=
      (u j).out}).2 ⟨w, R.mem_level, R.reflection_eq, (eq_iff_sub_mem.1 <| u
      · |>.out_eq.symm :)⟩ :).symm).1)).exists.imp' (u, ·) fun _ _ ↦ by ext; tauto,
          fun ⟨c, ⟨y⟩⟩ a ⟨c', ⟨_⟩⟩ b E ↦ by
    cases E
    obtain ⟨w, R, e⟩ := (H (hs _ b.1).1 (hs _ a.1).1).1 (b.2.trans a.2.symm)
    cases hN.2 (isSignedFrame _) R.mem_level R.reflection_eq
    congr 1
    exact Subtype.ext ((hs _ a.1).2.symm.trans (.trans (by simp [← e]) (hs _ b.1).2)),
      fun y ⟨P, E⟩ ↦
    ((point_eq_iff ..).1 (hc (hq y ▸ E :))).elim fun w R ↦ have a := fix R ⟨h.1, by simp [h.2]⟩
    have m := ((e ⟨_, (f.3 _).2 a.1⟩ y).2 ⟨_, rfl, by simp [a.2], a.2.2⟩).symm
    ⟨⟨_, ⟨y⟩⟩, ⟨m,
      un ⟨_, ⟨y⟩⟩ m _ ⟨a, rfl⟩ ▸ (H a h).2 ⟨w, ⟨R.mem_level, R.reflection_eq, by simp⟩, rfl⟩⟩, rfl⟩⟩
  have hP {p t} (h : Fx p t) : (localTerm (2 * α) t.1.1.charpoly t.2).eval 1 = Nat.card (∀ j, Q p.x
    t.1 j) := by simp [hd h.1, B, lieRoots, apply_ite, RingHom.map_det, localTerm,
    (numberedRoots ..).injective]
  obtain ⟨fS, sum⟩ := hF _ (hs · · |>.elim fun h k ↦ ⟨hq _ ▸ X.tangent i _ _ _ _ _ (ok _).1 (hr h.1)
    h.2.1 ((ra ..).2 ⟨k, by simp [h.2]⟩), by simp [hP h, hd h.1]⟩)
  have sup {w} : (countTerm _ b w).support ⊆ _ := fun c hc ↦ ((ite_ne_right_iff.1 hc).imp_right
    left_ne_zero_of_mul).elim fun h₂ h₃ ↦
    ((bij ⟨_, _, 0, h₂, (isReflection_eigenReflection (hr h₃)).1 _⟩ ⟨h₃, by
    simp⟩).surjOn ⟨(0, 1), rfl⟩).imp fun _ ↦ (·.1.imp_right (·.trans (by simp; exact c.out_eq)))
  use (fS.image _).subset sup, Set.indicator_eq_self.2 sup ▸ (finsum_mem_def ..).symm.trans
    (finsum_image_eq_zero_of_fibers fS _ sum (hs · · |>.elim fun a k ↦ by
    rw [countTerm_mk, ite_eq_left (a.2.1 ▸ isSignedFrame _), k, card_congr (bij _ a).equiv,
      Nat.card_range_of_injective, card_prod, cast_mul, hP a, div_div]
    rintro ⟨u⟩ ⟨v⟩ e
    cases (((point_eq_iff ..).1 ((hc e).trans (hc rfl).symm)).elim fun w R ↦
      funext (Quotient.out_equiv_out
      |>.1 <| by simpa [leftRel_apply, neg_add_eq_sub, hN.2 (isSignedFrame _) R.mem_level
                   R.reflection_eq] using! R.sub_mem_lattice ·) : v = u)
    simpa using (g.3 ℂ _ _ congr($(hc e).1)).unique congr($e.1) rfl))
  let F := (realVecAction (B z j)).restrictScalars ℂ
  let G := 1 + -2 • ((realVecAction ((α j).1 • z.1)).restrictScalars ℤ).restrict fun _ ↦
    realVecAction_mem_frameLattice (by
    simpa using! mul_mem (coe_mem_Ô _) <| (heckeAlgebra.mem_GUPlus_of_ne_zero h).2 · ·)
  have hG y : F y.1 = G y := by simp +zetaDelta [mul_smul, map_ofNat]; rfl
  have hf := let c := Module.finBasis ..; show (F.restrictScalars ℝ).det = (G.toMatrix c c).det by
    simp [det_apply', hG, ← det_toMatrix (c.ofZLatticeBasis ℝ), toMatrix_apply].trans_ne (by
    rw [Int.cast_ne_zero, map_add, toMatrix_one, map_smul, det_one_add_smul]; omega)
  obtain ⟨le, dL⟩ := (hG ⟨·, ·⟩ ▸ (G _).2), show F.det = _ by erw [det_restrictScalars,
    det_toLin', ← cmEmbedding.map_det, det_pi (LinearMap.mul ℂ ℂ <| Φ · _)]
  exact ⟨le, (hf <| by simp [det_restrictScalars, dL, ·]), (relIndex_comap_lattice le
    (equivOfDetNeZero _ hf).injective).trans (by simp [dL, prod_embeddings_eq_prod_pairs])⟩
end
end FoldSeg1
