import Lib.ClassField.Places.DecompositionLocal
import Lib.Cohomology.ProjectiveLine.NormalizationPullback
import Lib.General.Geometry.ChartedSchemes
import Lib.PadicComparison.Primitive.PrimitivePeriods
open CategoryTheory AlgebraicGeometry ObjectProperty Function Ideal nonZeroDivisors Algebra
  PrimeSpectrum CommRingCat Set Localization TensorProduct IsSmoothAt Comparison
set_option backward.isDefEq.respectTransparency false
section
variable {C} [Category C] {ℓ A} [CommRing A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A}
  (D : ComparedTheory g)
lemma ComparedTheory.mem_of_isClosedClass_of_isCharting [PreValuationRing A] {P} (c : IsClosedClass
  P) (b : ∀ {X}, P (freeAb X) ↔ D.IsGood (relFreeAb (offClosedFibre X))) {k} [CommRing k] [Algebra k
  A] {X} (T : ∃ V, @IsCharting k _ X V) (h : P (freeAb (reprBy (.ofSelf A)))) : P (freeAb ((ι _ ⋙
  restrictAlg k A) ⋙ X)) := T.elim fun V T ↦ b.2 ((D.isGood_iff_of_locally_bijective (V.whisker _).ι
  (T.1.whisker _ · · · · |>.imp (by simp; tauto))).1 (b.1 (T.2 _ (c.comap (restrictAlong _)) fun e
  _ ↦ ((c.comap (restrictAlong _)).of_bijective _ (pointMap_algBaseChange_unit_bijective _) (by
  choose a n d _ _ k using (exists_isStandardEtale_mvPolynomial (R := A) (p := @asIdeal (A ⊗[k] e.R)
    _ ·))
  have ⟨s, e⟩ := finite_cover_nhds (isOpen_basicOpen.mem_nhds ∘' n)
  exact b.2 ((D.isGood_iff_of_locally_bijective (⨆ p : s, testUnitLocus (a p)).ι fun c φ m M ↦
    (iUnion₂_eq_univ_iff.1 e (comap φ.1.1.1 ⟨m, M.isPrime⟩)).elim fun _ ↦ (⟨_, ·.2, by aesop⟩)).1
    (b.1 (c.freeAb_iSup {testUnitLocus (a p * f) | (p) (f)} (fun | _, ⟨p, f, rfl⟩ => ((fun x ↦ (k
    p).of_isLocalizationAway (Sₛ := Away x) x) (algebraMap _ _ f)).1.elim fun P ↦ ⟨(c.iff_of_isIso
    (freeAb.map ((testUnitLocus.nonempty_iso_away _).some.2 ≫ (ι _).whiskerLeft (reprMap
    (CommAlgCat.isoMk ((P.equivRing.trans P.equivAwayAdjoinRoot).restrictScalars A)).1) ≫
    (testUnitLocus.nonempty_iso_away _ _).some.1))).1 (b.2 (D.isGood_standard_etale
    (b.1 (c.of_bijective _ pointMap_ofSelf_bijective h)) _ (MvPolynomial.finSuccEquiv ..))), fun _
    ⟨q, g, _⟩ ↦ ⟨p, f * a q * g, by aesop (add simp testUnitLocus)⟩⟩) (⟨·, 1, by simp⟩))))) :))))
end
variable {ℓ} [ThePrime ℓ] {R : CommRingCat} (A) [CommRing A] [Algebra R A] (Y : Over (Spec R))
noncomputable def algToBaseChange : algPointsOf A R Y ⟶ forget₂ .. ⋙ geomPoints R A Y :=
  ⟨fun c ↦ ↾(⟨(⟨_⟩, ⟨ofHom _⟩), congr(⟨$(Spec.homEquiv.eq_symm_apply.1 ·.1.w)⟩)⟩), fun _ _ f ↦ by
  ext; exact baseChangeOf.ext rfl (f.1.2 · |>.symm)⟩
lemma isBijective_algToBaseChange F : (Comparison.restrict (TestOver.toTest A) F).IsBijective
  (freeAbMap (Y := testIncl ⋙ _) ((ι _).whiskerLeft (algToBaseChange A Y))) :=
  HasUnivPoints.isBijective fun c y ↦ ⟨⟨@.of A _ _ _ y.1.2.1.1.toAlgebra, c.2⟩, ⟨Over.homMk _
  (Spec.homEquiv.eq_symm_apply.2 congr($(y.2).1))⟩, 𝟙 c, by aesop, fun _ _ f k ↦
  ⟨⟨CommAlg.homOfRingHom _ (congr($k.1.2.1.1 ·).symm)⟩, ⟨.symm congr(⟨$k.1.1.1, _, _⟩),
  rfl⟩, by bound⟩, by simpa using! bijective_id⟩
lemma isCohomEquiv_generic_fibre {A : ClosurePlace} {p : ℕ} [Fact p.Prime] (hp :
  A.valuation p < 1) (hℓ : IsUnit (ℓ : A)) [Algebra R A] Y [IsCharted Y R] :
  Components ⟨ZMod ℓ⟩ (Y := geomPoints R A Y) (baseChangeTransition _ (ofHom A.subtype) rfl) := by
  obtain ⟨_, _, j, J⟩ := InvertsPrime.mk hℓ, (.comp (algebraMap (PadicAlgCl ℓ) _)
    Classical.ofNonempty : Ω →+* ℂ_[ℓ]).toAlgebra, exists_comap_intQpBar_eq hp
  have L := have : FaithfulSMul A ℂ_[ℓ] := A.faithfulSMul; hasLineFormula_locallyConstant A
  let κ := Comparison.restrict (TestOver.resScalars A Ω) (locConstAlong (𝟭 _))
  exact IsBijective.eqv ((@isBijective_algToBaseChange _ Ω _ (.compHom ..) Y _).trans_iff.1
    ((isBijective_algToBaseChange A Y (locConstCoeff _)).trans
    (ComparedTheory.mem_of_isClosedClass_of_isCharting ⟨_, Empty, nofun, L, L⟩ (κ.devissage (𝟭 _)
    (𝟙 _)).isClosedClass (@fun X ↦ ((HasUnivPoints.isBijective (Y := (offClosedFibre X).toFunctor)
    (Y' := _ ⋙ X) (u := {app c := ↾(⟨·, eq_top_of_isUnit_mem _ (mem_map_of_mem _
    ((A.valuation_lt_one_iff p).2 hp)) ((isUnit_of_invertible ↑p).map (algebraMap Ω c.1))⟩)}) fun c
    y ↦ (hasUnivPoints_structurePt A Ω c
    ⟨⟨CommAlg.homOfRingHom _ (IsLocalization.lift_eq fun a : A⁰ ↦ by
    simpa using! eq_top_mono ((map_mono (by intro; simp +contextual [radical, mem_span_singleton,
      (J ▸ Valuation.integer.integers _ : (Valued.v.comap j).Integers A).dvd_iff_le,
      isUnit_iff_dvd_one, (exists_pow_lt_of_lt_one ..).imp fun _ ↦ le_of_lt])).trans (map_radical_le
      (I := span {a.1}) _)) y.2)⟩⟩).imp fun _ ⟨_, s, _, k, B⟩ ↦ by exact ⟨_, s, rfl, fun d _ f e ↦
    (k d ⟨⟩ f congr(⟨⟨CommAlgCat.ofHom $(IsLocalization.algHom_ext A⁰ (by ext))⟩⟩)).imp fun _ ⟨⟨_,
    rfl⟩, n⟩ ↦ ⟨⟨by simpa using congr($e.1).symm, rfl⟩, by tauto⟩, B⟩).trans_iff (c := .id _)).trans
    ((isCohomEquiv_iff_isBijective.symm.trans (relFreeAb.isCohomEquiv_iff_subsingleton _)).trans
    ⟨fun h ↦ ⟨Unique.bijective (B := TotalH (relFreeAb _) (locConstAlong ..)), .of_subsingleton⟩,
    fun h n ↦ ⟨fun _ _ ↦ DirectSum.of_injective _ (h.1.2.subsingleton.1 ..)⟩⟩)) ‹IsCharted ..›.1
    (by simpa using! (κ.isBijective_of_repr (u := 𝟙 _) ⟨⟨structureMap⟩⟩ (((pointMap_ofSelf_bijective
    _).of_comp_iff' _).1 ∘' pointMap_ofSelf_bijective) (((@bijective_const_of_isDomain (.of A) _
    _).of_comp_iff _).1
      (bijective_const_of_isDomain (B := .of Ω))
  ))) :) rfl))
