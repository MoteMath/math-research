import Lib.General.Geometry.ProperSchemes
import Lib.Cohomology.ProjectiveLine.LineChernClass
import Lib.PadicComparison.Descent.AlmostAcyclic
import Lib.PadicComparison.HodgeTate.HodgeTatePairs
import Lib.General.Geometry.EtaleCharts
import Lib.General.Geometry.ProperAtlas
import Lib.PadicComparison.Primitive.TiltedTheory
import Lib.PadicComparison.Duality.IntegrationOverLine
section
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor
open CategoryTheory RingHom CommRingCat Ideal HV Subfunctor IsLocalRing Algebra PrimeSpectrum Set
variable {ℓ n W} [ThePrime ℓ] {R S T : CommRingCat} {s : W ⟶ reprBy R} (h : IsProperOver s) (u :
  IsUnit (ℓ : R))
lemma HV.map_eq_zero_of_factors {Λ X Z v v' x w} (e : w ≫ v = v') :
    @map Λ W X v n x = 0 → @map _ Z _ v' n x = 0 := by simp_all [← e, map_comp]
include h u
lemma IsProperOver.injective_map_residue {A} [CommRing A] [IsAICLocal A] [PreValuationRing A] {a} :
  (⇑(map ⟨ZMod ℓ⟩ (baseChangeTransition s (ofHom (residue A)) (a := a) rfl) n)).Injective := .of_ker
  _ fun _ ↦ (map_eq_zero_iff _ ((h.baseChange a).proper_base_change (by simpa using u.map a.1)
  n).1).1 ∘ map_eq_zero_of_factors (w := ⟨fun _ ↦ ↾fun y ↦ ⟨(_, ⟨ofHom (Ideal.Quotient.lift
  _ _ y.2)⟩), y.1.2⟩, by intros; ext; exact baseChangeOf.ext rfl (Quot.ind (by tauto))⟩) rfl
lemma IsProperOver.isCohomEquiv_field_extension {a b} {φ : S ⟶ T} (e : a ≫ φ = b) (hS :
  IsField S) (hT : IsField T) (iS : IsAIC S) (iT : IsAIC T) :
  Components ⟨ZMod ℓ⟩ (baseChangeTransition s _ e) := e.rec fun n ↦ by
  algebraize [φ.1]; let := hS.toField; let := hT.toField
  rcases iS.isAlgClosed, iT.isAlgClosed; have β (t : Finset T) := (nullstellensatz_exists_le_ker
    (f := .adjoin_of_finite (R := S) t.finite_toSet) bot_ne_top).choose
  let b t : fibreProd s (reprMap a) ⟶ _ :=
    (baseChangeFunctor s).map ((Under.map a).map (β t).toUnder).op
  refine (h.isCohomContinuous.isFilteredColimit_adjoin s T a n).imp (fun p ↦ .of_ker _ fun x g ↦
    (p ∅ _ ((map_comp _ (baseChangeTransition s _ rfl) _).symm.trans g)).elim fun t ⟨_,
    e⟩ ↦ by simpa [HV.map] using! map_eq_zero_of_factors (by ext; exact baseChangeOf.ext rfl (
    congrArg _ <| (β t).2 ·) : b t ≫ _ = 𝟙 _) ((map_comp ..).trans e)) (· · |>.elim fun t ⟨x, e⟩ ↦
    .elim (image_subset_nonunits_valuationSubring (A := (adjoin ..).toSubring) _
    (ker_ne_top (β t))) fun V W ↦ let i := ofHom (R := adjoin S _) (Subring.inclusion W.1)
    ⟨map _ (b t) n x, e ▸ (map_comp (baseChangeTransition s (ofHom V.subtype) rfl)
      (baseChangeTransition s (ofHom (algebraMap S _) ≫ i) rfl) _).trans ((congrArg _
      (h.injective_map_residue u ?_)).trans (map_comp _ (baseChangeTransition s i rfl) x).symm)⟩)
  repeat erw [← map_comp]
  congr 2 with; exact baseChangeOf.ext rfl fun _ ↦ congrArg _ (Ideal.Quotient.eq.2 (
    V.coe_mem_nonunits_iff.1 (W.2 ⟨_, (sub_mem_ker_iff _).2 ((β t).2 _), rfl⟩)))
lemma IsProperOver.isOpen_zero_set_and_eq_zero (T :
  TestRing) {a x} : let z := {P : PrimeSpectrum T.1 | map ⟨ZMod ℓ⟩ (baseChangeTransition s (ofHom
    (algebraMap T.1 P.1.ResidueField)) (a := a) rfl) n x = 0}; IsOpen z ∧ (z = univ → x = 0) := by
  intro z; let q := fibreProd.snd s (reprMap a)
  have v {I b} (k : ∀ c ∈ I, _) : unitPoints q {b} ≤ unitPoints q I :=
    fun _ _ h c i ↦ isUnit_of_dvd_unit (map_dvd _ (k c i)) (h b rfl)
  have w {I b} k := map_eq_zero_of_factors (x := x) (homOfLe_ι (@v I b k))
  let J : Ideal _ :=
    ⟨⟨⟨{b | map _ (unitPoints q {b}).ι n x = 0}, @fun b c i j ↦ let ⟨e, o, _⟩ := T.2.2 b c
    have l a {d} := @v {d} ((1 - a) * d) (by simp)
    (map_eq_zero_iff _ ((mayer_vietoris_injective (l e) (l _) (.of_preimage_le
      (hasPartitions_locConstCoeff.isCohomDense_partition _ o) (by exact .mk fun _ ↦
      ↾(⟨⟨·.1.1.2.1⟩⟩)) fun _ y ↦ by apply Or.imp <;> rintro k _ rfl <;> erw [map_mul, map_sub, k]
      <;> simpa using (y.2 _ rfl)) n rfl).2 fun _ k ↦ by
      simpa [*, ← map_mul, mul_mul_mul_comm] using (k.2.1 _ rfl).mul (k.2.2 _ rfl)).1).1
      (by ext <;> apply (H.map_map ..).trans <;> [apply w _ j; apply w _ i] <;> simp [*,
      mul_add, dvd_add])⟩, hasPartitions_locConstCoeff.eq_zero_of_zero_ring
    (by simp [unitPoints]) ..⟩, fun _ _ ↦ w (by simp)⟩
  rw [← (Set.ext fun P ↦ not_subset.trans ⟨fun ⟨b, k, l⟩ ↦ map_eq_zero_of_factors (lift_ι _ (by
    rintro _ _ ⟨y, rfl⟩ _ rfl; exact (Ne.isUnit (algebraMap_residueField_eq_zero.1.mt l)).map
      y.1.2.1.1)) k, fun e ↦ ?_⟩ : (zeroLocus J)ᶜ = z)]
  simpa [HV.map, eq_top_iff_one, isClosed_zeroLocus, zeroLocus_empty_iff_eq_top] using!
    map_eq_zero_of_factors (lift_ι (𝟙 _) fun _ ↦ by simp [unitPoints])
  have ⟨_, _, _⟩ := T.2.exists_valuationSubring_atPrime P; let M := P.1.primeCompl
  exact (((h.baseChange a).isCohomContinuous.isFilteredColimit_antitoneFamily (V := unitPoints q)
    (by tauto) (fun I ↦ isRelAffine_of_zero_unit_locus (⟨∅, baseRingMap q · '' I, by simp
    [unitPoints]⟩)) (D := (monotone_image.comp Finset.coeEmb.monotone).functor) (m :=
    ⟨M, .mk fun _ ↦ ⟨⟨image_val_subset⟩⟩⟩) (· {⟨·, ·⟩} _ (by simp))).1 ∅ _
    ((map_comp _ (ι _) _).symm.trans (map_eq_zero_of_factors ((isPullback_fibreProd.of_bot (v₁₁ :=
    baseChangeTransition s (ofHom (algebraMap T.1 (Localization M))) rfl) (v₁₂ := reprMap _) rfl
    isPullback_fibreProd).lift_snd _ (ι (.preimage _ q)) ((Category.assoc ..).trans ((fromPreimage
    .. ≫ homOfLe (unitPoints_le_range_reprMap _ M)) ≫= IsIso.inv_hom_id_assoc (toRange
    (uliftCoyoneda.map _)) (ι _)))) (h.injective_map_residue u (by simpa [← map_comp]))))).elim
    fun t ⟨_, e⟩ ↦ ⟨_, w (forall_mem_image.2 fun
    _ ↦ t.dvd_prod_of_mem _) ((map_comp ..).trans e :), M.prod_mem fun c _ ↦ c.2⟩
end
section
open AddEquiv CategoryTheory CommRingCat Function Ideal projLine MonoidalCategory
lemma isProperOver_projLinePow ι :
  IsProperOver ((zIsInitial.op.isTerminalObj uliftCoyoneda _).from (projLinePow ι)) := ⟨fun _ x y ↦
  ⟨⨆ i, span {HSub.hSub.uncurry (unimodularRow (x i) * (unimodularRow (y i)).swap)}, fun _ f ↦
  funext_iff.trans ((forall_congr' fun i ↦ ULift.up_inj.trans ((x i).1.out_eq ▸ (y i).1.out_eq ▸ by
  simp [Quotient.eq, projLineSetoid, unimodularRow])).trans iSup_le_iff.symm)⟩,
  of (FreeCommRing _), fun i ↦ ⟨⟦⟨.of (Sum.inl i), .of (.inr i)⟩⟧⟩, fun O x _ ↦ by
  choose u v e using fun i ↦ (x i).1.ind (motive := (∃ u v : O, ⟦⟨u, v⟩⟧ = ·)) fun a ↦ by
    obtain ⟨c, _⟩ | ⟨c, _⟩ := le_total (O.valuation a.2) ⟦_⟧ <;>
      [use 0, c; use c - 1, 1] <;> simp [Quotient.eq, projLineSetoid] <;> tauto
  use ofHom (FreeCommRing.lift (Sum.elim u v)), congr((⟨$(e · ▸ by simp)⟩))⟩
variable {A} [CommRing A] {D} [Category D] (g : D ⥤ TestOver A) {X} (I :
  IdealFamily (elementsProj (X ⊗ reprBy (of A)))) {ℓ : ℕ}
def residueTest (c : TestOver A) (P : PrimeSpectrum c.1) : Under c :=
  .mk (Y := ⟨.of A P.1.ResidueField, have := (c.2.exists_valuationSubring_atPrime
    P).1; isTest_of_preValuationRing⟩) ⟨CommAlg.homOfRingHom (algebraMap ..) (by tauto)⟩
def IsDetectedAtPoints F := (∀ c n x, let z := {P | H.map F (freeAb.map
    (g.whiskerLeft (reprMap (residueTest c P).hom))) n x = 0}; IsOpen z ∧ (z = .univ → x = 0)) ∧ ∀ V
  k (φ : V ⟶ k), IsField V.1 → IsField k.1 → IsCohomEquiv F (freeAb.map (g.whiskerLeft (reprMap φ)))
def IdealFamily.pullToTests : IdealFamily (ringOf (testOfPoint A X)) :=
  I.whisker (sectionLift (ringOf (testOfPoint A X))
  ⟨(·.2, ⟨ofHom _⟩), fun f ↦ congr(⟨$(f.2), ⟨ofHom $(f.1.1.1.comp_algebraMap)⟩⟩)⟩)
lemma IdealFamily.isDetectedAtPoints_of_proper (I : IdealFamily _) [InvertsPrime A ℓ] {p} (hX :
  @IsProperOver X ⟨ℤ⟩ p) {F} (β : locConstAlong (testOfPoint A X) ⟶ F) (hβ : ∀ a,
  I.pullToTests.I a = ⊥ → Bijective (β a)) (hΓ : IsCohomDense F I.pullToTests.botLocus) :
  IsDetectedAtPoints (testOfPoint A X) F := let W : Subfunctor (baseChangeOf _ (zIsInitial.to _)) :=
    ⟨_, fun f x ↦ @I.botLocus.map ⟨x.1⟩ _ ⟨f, rfl⟩ ⟨⟩⟩
  have ⟨h, T, a, ha⟩ := hX.baseChange _
  let s := W.ι ≫ fibreProd.snd ..
  have k {C} f := @I.2 ⟨a.1⟩ (.mk (obj := C) ((baseChangeOf ..).map f a).1) ⟨f, rfl⟩
  have hs : IsProperOver s := ⟨(by convert h · ·.1 ·.1; exact Subtype.ext_iff), _, ⟨_, (k (ofHom
    _)).symm.trans (map_quotient_self _)⟩, fun O z i ↦ (ha O z.1 i).elim fun u e ↦ ⟨ofHom
    (Ideal.Quotient.lift _ _ fun _ b ↦ Subtype.ext (((k _).trans (e ▸ z.2)).le (le_comap_map b))),
    Subtype.ext ((Functor.map_comp_apply ..).symm.trans e)⟩⟩
  let κ : Comparison (locConstCoeff _) F := ⟨_ ⋙ TestOver.toTest A, β⟩
  let u c : (I.pullToTests.botLocus.preimage (toUnit (testOfPoint A X ⋙ reprBy c))).toFunctor ⟶ κ.φ
    ⋙ testIncl ⋙ baseChangeOf s (ofHom _) := ⟨fun _ ↦ ↾fun x ↦ ⟨(⟨⟨_, congr(⟨$(zIsInitial.hom_ext
    ..)⟩)⟩, x.2⟩, ⟨_⟩), congr(⟨ofHom $(x.1.1.1.1.comp_algebraMap.symm)⟩)⟩, fun _ _ f ↦
    .symm congr(↾fun _ ↦ ⟨(⟨$(baseChangeOf.ext f.2 f.1.1.1.2), _⟩, _), _⟩)⟩
  have t c := Comparison.HasUnivPoints.isBijective (u :=
    u c) fun T y ↦ let : Algebra A T.1 := y.1.1.1.1.2.1.1.toAlgebra
    ⟨.mk (obj := ⟨_, T.2⟩) _, ⟨⟨⟨CommAlgCat.ofHom ⟨_, (congr($(y.2).1.1 ·).symm)⟩⟩⟩, y.1.1.2⟩,
      𝟙 T, .symm
      (Functor.map_id_apply ..), fun _ _ f k ↦ ⟨⟨⟨CommAlg.homOfRingHom _ (congr($k.1.1.1.1.2.1.1
      ·).symm)⟩, congr($k.1.1.1.1.1).symm⟩, ⟨congr(⟨⟨⟨CommAlg.homOfRingHom $k.symm.1.2.1.1 _⟩⟩, _⟩),
      rfl⟩, fun _ e ↦ e.2 ▸ rfl⟩, .comp (hβ _ y.1.1.2) bijective_id⟩
  let e {c n} := (ofBijective _ ((hΓ.preimage _).isCohomEquiv n)).trans (ofBijective _ (t c n)).symm
  have w {c k} φ n x : HV.map _ (baseChangeTransition s ((ringOf (𝟭 _)).map φ) (hom_ext
    φ.1.1.comp_algebraMap)) n _ = e _ := (t k n).1 (.trans (κ.map_pull_eq_pull_map (a :=
    freeAbMap (u c)) (a' := freeAb.map (Subfunctor.fromPreimage _
    (Functor.whiskerLeft _ (reprMap φ)))) ..).symm (by simp [e, H.map_map, -Functor.map_comp]; rfl))
  ⟨fun c n x ↦ by simpa only [← e.map_eq_zero_iff, ← w] using!
    hs.isOpen_zero_set_and_eq_zero InvertsPrime.isUnit_prime ⟨of _, c.2⟩, fun V k φ a b n ↦
    (Comparison.bijective_iff_of_comm_sq (w φ n) e.bijective e.bijective).2
    (hs.isCohomEquiv_field_extension InvertsPrime.isUnit_prime _ a b V.2.1 k.2.1 n)⟩
end
section
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor
open CategoryTheory Classical CommAlgCat Finsupp IsLocalRing TotalH ObjectProperty
noncomputable def IdealFamily.ofMaximalIdeal {A} [CommRing A] [IsLocalRing A] :
  IdealFamily (ringOf (𝟭 (TestOver A))) :=
  ⟨fun c ↦ (maximalIdeal A).map (algebraMap A c.1), (·.1.1.comp_algebraMap ▸ Ideal.map_map ..)⟩
variable {ℓ A} [CommRing A] [InvertsPrime A ℓ] {D} [Category D] {g : D ⥤ TestOver A}
lemma lerayHirsch_bijective_of_fields {F I} {d : I → ℕ} (hP : IsDetectedAtPoints g F) {θ : ∀ i,
  H (restrictAlong g (locConstAlong (𝟭 _))) F (d i)} {c}
  (h : ∀ k, (c ⟶ k) → IsField k.1 → IsLerayHirschBasis θ (freeAb (reprBy k))) :
  IsLerayHirschBasis θ (freeAb (reprBy c)) := let s d :
    (I →₀ ULift (LocallyConstant ..)) ≃+ _ := mapRange.addEquiv (sectionEquiv (locConstAlong ..) d)
  let E P := Equiv.ofBijective _
    (((h _ (residueTest _ P).hom (Field.toIsField P.1.ResidueField)).comp (s _).bijective).comp
    (mapRange_bijective _ rfl (@bijective_const_of_isDomain _ _ (Ideal.Quotient.isDomain _))))
  ((s c).bijective_comp _).1 (.of_existsUnique _ fun y ↦
  have z m P := (AddMonoidHom.sub_mem_ker_iff _ (x := y).trans (((lerayHirsch_mapRange_comp θ
    (map_homClass (f := freeAb.map (reprMap (residueTest _ P).hom))) (s c m)).symm.trans (congrArg _
    (ext fun _ ↦ (homClass_comp ..).symm.trans (congrArg _ ((homReprEquiv ..).eq_symm_apply.2
    ((add_zero _).trans congr(⟨⟨$(funext (congrArg _ <| P.residueField_comap.le ⟨·, rfl⟩)),
    _⟩⟩)))))) : _ = E P (mapRange (·.1 P) rfl m)).congr_right.trans ((E P).symm_apply_eq.symm.trans
    Finsupp.ext_iff))).symm.trans (congr($comp_homClass_eq _).congr_left.trans DFinsupp.ext_iff)
  have l := (IsLocallyConstant.iff_eventually_eq _).2 fun P ↦ .mono ((DFinsupp.finite_support
    _).eventually_all.2 fun n _ ↦ (hP.1 ..).1.mem_nhds ((z (mapRange (⟨.const _ ·⟩) rfl _) _).1 (by
   tauto) n)) fun _ e ↦ ext ((z ..).2 (byCases (congrArg (H.map ..) · |>.trans (by simp)) <| e ·))
  ⟨.onFinset (l.range_finite.toFinset.sup support) (fun i ↦ ⟨_, l.comp (· i)⟩) fun _ ↦
    not_imp_comm.1 (by aesop), (sub_eq_zero.1 (DFinsupp.ext fun n ↦ (hP.1 ..).2
    (top_unique fun _ _ ↦ (z ..).1 (by tauto) _))).symm, by intros; ext; erw [(z ..).2] <;> bound⟩)
lemma exists_lerayHirsch_basis (M : TorsionCoeff g) (hl : IsDetectedAtPoints g M.F) (d :
  IsCohomDense M.F (IdealFamily.ofMaximalIdeal.botLocus.whisker g))
  (j : Σ n, H (restrictAlong g (locConstAlong (𝟭 _))) M.F n) : ∃ b : Set _, (pullbackAlong
  oneLocConst j.2.toTotalH ≠ 0 → j ∈ b) ∧ ∀ c, ⟨⟩ ∈ IdealFamily.ofMaximalIdeal.botLocus c →
  IsLerayHirschBasis (fun i : b ↦ i.1.2) (freeAb (reprBy c)) := by
  have {N} := AddCommGroup.zmodModule (M.nsmul_totalH_eq_zero (N := N))
  let u (i : Sigma (H (locConstAlong g) M.F)) := i.2.toTotalH.pullbackAlong oneLocConst
  obtain ⟨b, -, o, q, l⟩ := exists_linearIndepOn_extension (by by_cases u j = 0 <;> simp_all :
    LinearIndepOn (ZMod ℓ) u ({j} ∩ u.support)) le_top
  let f {c : TestOver A} h : ⟨of A (ResidueField A), isTest_of_preValuationRing⟩ ⟶ c :=
    ⟨ofHom (Ideal.Quotient.liftₐ _ structureMap.1 ((Ideal.map_eq_bot_iff_le_ker _).1 h))⟩
  use b, by tauto, fun c h ↦ lerayHirsch_bijective_of_fields hl fun k φ hk ↦
    (Comparison.bijective_iff_of_comm_sq (fun w ↦ ?_) (mapRange.addEquiv (.trans ⟨.ofBijective _
    (@bijective_const_of_isDomain _ _ hk.isDomain), by tauto⟩ (sectionEquiv (locConstAlong ..)
    k))).bijective ((hl.2 _ _ (f (IdealFamily.ofMaximalIdeal.botLocus.map φ h)) (Field.toIsField _)
    hk).comp_iff.2 (d.isCohomEquiv_of_fromPreimage (u := toUnit _) (.of_bijective fun a ↦
    ⟨fun _ _ _ ↦ congr(⟨⟨⟨ofHom $(Ideal.Quotient.algHom_ext _ (by ext))⟩⟩, _⟩),
    fun ⟨_, x⟩ ↦ ⟨⟨⟨f x⟩, x⟩, rfl⟩⟩ ))).bijective_totalH).1 ⟨l,
    M.comp_oneLocConst_surjective.forall.2 ((range_linearCombination _).ge
    <| ·.induction_on (by simp) (b.image_eq_range u ▸ q ⟨⟨·, ·⟩, ⟨⟩, rfl⟩) (by clear * -; aesop))⟩
  simp [lerayHirsch, mapThenComp, sum_mapRange_index, linearCombination, map_finsuppSum]
  refine sum_congr fun i _ ↦ (w i).natCast_zmod_val ▸ ?_
  simp [← nsmul_one, -nsmul_eq_mul, u, homClass_comp_homClass_comp]
  congr 3; exact map_homClass.trans (congrArg _ (freeAb.hom_ext (Y := g ⋙ reprBy k)))
instance TestOver.hasCoveringPoints : HasCoveringPoints (ι _ : TestOver A ⥤ _) :=
  .mk fun B _ _ ↦ have ⟨E, η, t, s⟩ := Envelope.exists_functorial_test ![_]
  let := ((η ⟨B⟩).1.comp (algebraMap A B)).toAlgebra
  ⟨⟨_, t _⟩, ⟨ofHom ⟨(η ⟨B⟩).1, by tauto⟩⟩, fun c φ ↦ (s 0 ⟨_, c.2⟩ ((forget₂ ..).map φ.1)).elim
    fun ψ e ↦ ⟨⟨⟨CommAlg.homOfRingHom _ (φ.1.1.2 · ▸ congr($e _))⟩⟩, congr(⟨ofHom ⟨$(e).1, _⟩⟩)⟩⟩
lemma isAffinelyCovered_projLinePow {J} : IsAffinelyCovered (ι _ : TestOver A ⥤ _)
  (forget₂ .. ⋙ projLinePow J) := ⟨⟨fun _ ↦ ((isProperOver_projLinePow J).1 _ · · |>.imp
  (by aesop))⟩, of A (MvPolynomial ..), fun i ↦ ⟨⟦(.X (Sum.inl i), .X (.inr i))⟧⟩, fun _ _ ↦
  ⟨⟨ofHom (MvPolynomial.aeval (·.rec _ _))⟩, congr(fun _ ↦ ⟨$(.trans (by aesop) (Quot.out_eq _))⟩)⟩⟩
lemma isDetectedAtPoints_projLine : IsDetectedAtPoints (testOfPoint A _)
  (locConstAlong (testOfPoint A projLine)) := have h := isProperOver_projLinePow Unit
  IdealFamily.isDetectedAtPoints_of_proper ⟨⊥, by simp⟩
    (h.of_isPullback h (.of_vert_isIso (snd := (NatIso.ofComponents fun _ ↦ (Equiv.piUnique
    _).toIso).2) (f := 𝟙 _) ⟨rfl⟩) h (𝟙 _) rfl) (𝟙 _) (fun _ _ ↦ Function.bijective_id) .of_top_le
end
noncomputable section
open AddMonoidAlgebra CategoryTheory Comparison CommAlgCat Function H LinearEquiv NNRat
  TensorProduct PadicTest CategoryTheory.Functor MonoidalCategory
set_option backward.isDefEq.respectTransparency false
instance {C} [Category C] {F A : AbFunctor C} [HasFlatValues F] [HasFlatValues A] :
  HasFlatValues (abTensor F A) := have := @HasFlatValues.flat; ⟨fun _ ↦ .instTensorProduct⟩
variable {p} [ThePrime p] (S : Type) [AddCommMonoid S] (χ : Multiplicative ℚ →* OFlat) (g : ℚ≥0 →+
  ℚ) (a : ULift.{1} Bool) (B : ULift.{1} Bool → CommAlg OFlat) (ψ :
  _ ⥤ CommAlg OFlat := 𝟭 _) {b b' : CommAlg OFlat}
abbrev monoidAlg := CommAlgCat.of OFlat OFlat[S]
def charTwist {S} [AddCommMonoid S] (f : S →+ ℚ) : monoidAlg S ⟶ monoidAlg S :=
  ofHom ((AddMonoidAlgebra.lift ..)
  ((algebraMap ..).1.comp (χ.comp f.toMultiplicative) * AddMonoidAlgebra.of ..))
abbrev discToTorus : monoidAlg ℚ≥0 ⟶ monoidAlg ℚ := ofHom (mapDomainAlgHom _ _ g)
abbrev evalZero b : monoidAlg ℚ≥0 ⟶ b := ofHom
    ((AddMonoidAlgebra.lift ..) ⟨⟨(if · = 1 then 1 else 0), ite_eq_left rfl⟩, by aesop⟩)
def pointOrTorus := cond a.1 (monoidAlg ℚ) (.of _ OFlat)
abbrev tiltPointsSum := sigma fun a ↦ tilt ⋙ reprBy (ψ (B a))
abbrev twoDiscs := tiltPointsSum (fun _ ↦ monoidAlg ℚ≥0) ψ
abbrev gluing : freeAb (tiltPointsSum pointOrTorus ψ) ⟶ freeAb (twoDiscs ψ) :=
  freeAb.desc (fun | _, ⟨⟨true⟩, t⟩ => .of ⟨⟨false⟩, ⟨ψ.map (discToTorus (-coeHom)) ≫ t.1⟩⟩ - .of ⟨⟨true⟩,
       ⟨ψ.map (discToTorus coeHom) ≫ t.1⟩⟩ | _, ⟨⟨false⟩, t⟩ => .of ⟨⟨false⟩, ⟨ψ.map (evalZero _) ≫ t.1⟩⟩) (by bound)
@[simp] lemma evalZero_comp g : evalZero b ≫ g = evalZero b' := by aesop
variable (X : PadicTest ⥤ _ := pointFunctor _) {B : ULift.{1} Bool → CommAlg OFlat} (Δ : ∀ b,
  B b ⟶ B b)
abbrev origin : freeAb X ⟶ freeAb twoDiscs :=
  freeAb.desc (fun _ _ ↦ .of ⟨a, ⟨evalZero _⟩⟩) (by intros; congr; simp)
abbrev projFirst : freeAb (tiltPointsSum B) ⟶ freeAb (tilt ⋙ reprBy (B ⟨true⟩)) := freeAb.desc
    (fun | _, ⟨⟨true⟩, t⟩ => .of t | _, ⟨⟨false⟩, _⟩ => 0) (by bound)
abbrev oneSub : freeAb (tiltPointsSum B) ⟶ freeAb (tiltPointsSum B) :=
  freeAb.desc (fun _ x ↦ .of x - .of ⟨_, ⟨Δ _ ≫ x.2.1⟩⟩) (by bound)
@[simp] lemma charTwist_comp_evalZero : charTwist χ g ≫ evalZero b =
  evalZero b := by ext; simp_all [charTwist]
@[reassoc] lemma charTwist_comp_discToTorus : charTwist χ g ≫ discToTorus g =
  discToTorus g ≫ charTwist χ (.id _) := by ext; simp [charTwist]
lemma oneSub_comp_gluing : oneSub (fun ⟨b⟩ ↦ b.rec (𝟙 _) (charTwist χ (.id _))) ≫ gluing =
  gluing ≫ oneSub (charTwist χ <| cond ·.1 coeHom (-coeHom)) :=
  freeAb.hom_ext (by rintro _ ⟨⟨⟨⟩⟩⟩ <;> simp [charTwist_comp_discToTorus_assoc]; abel)
instance : Mono gluing := have I : Epi (discToTorus coeHom) := ⟨fun x y h ↦ hom_ext (algHom_ext'
         (MonoidHom.ext fun s ↦ mabs_mem_iff (H := MonoidHom.eqLocus ..).1
         (by simpa [mabs] using! congr($h (single s.nnabs 1)))) (by ext))⟩
  (NatTrans.mono_iff_mono_app _).2 fun c ↦ SplitMono.mono ⟨AddCommGrpCat.ofHom
         (FreeAbelianGroup.lift fun ⟨⟨b⟩, ⟨t⟩⟩ ↦
    .of ⟨⟨false⟩, ⟨_root_.structureMap⟩⟩ - cond b (Function.extend (discToTorus coeHom ≫ ·)
    (.of ⟨⟨true⟩, ⟨·⟩⟩) 0 t) 0), by dsimp [freeAb, AddCommGrpCat.free]; ext ⟨⟨⟨⟩⟩⟩ <;>
    simp [freeAb.desc, freeAb, Injective.extend_apply I.1] <;> rcongr⟩
lemma isCohomEquiv_gluing_tilt {N} c : let G := moduleCoeff (tensorCoeff
    N); let ψ := tensorLeft (tilt c); IsAcyclicOnPerfect G → FP (freeAb (twoDiscs ψ)) ∧
      FP (freeAb (tiltPointsSum pointOrTorus ψ)) ∧ IsCohomEquiv (tilt ⋙ G) (gluing ψ) := by
  intro G ψ ac
  let L := asModules (𝟭 (CommAlg OFlat))
  let U := tensorWith (S := OFlat) _ (tilt c) ⋙ moduleCoeff (tensorRight N)
  let D {X} B (f : ∀ b, X ⟶ L (B b)) x : freeAb (tiltPointsSum B ψ) ⟶ _ ⋙ G :=
    freeAb.desc (fun _ t ↦ G.map t.2.1 (U.map (f _) x)) (by solve_by_elim [G.map_comp_apply])
  have κ {X} B (h : ∀ b, _) f (e : Bijective fun x ↦ (f ⟨false⟩ x, f ⟨true⟩ x)) :
      Bijective (Abelian.Ext.mk₀ ∘ @D X B f) ∧ _ ∧ FP (freeAb (tiltPointsSum B ψ)) :=
    have u b : PerfectRing (ψ (B b)) p :=
      perfectRing_tensor p_eq_zero_of_algebra_oFlat ⟨_, c.isPerfectTorsionFree_tilt.1⟩ ⟨_, h b⟩
    have ⟨a, _⟩ := forall_and.1 (isBijective_reprBy_iff.1 <| @ac _ <| u ·)
    have := e.map_prod (U ⋙ forget _)
    ⟨(bijective_iff_of_comm_sq (fun _ ↦ by ext; simpa [H.map] using congrArg _ freeAb.hom_ext)
      (.comp (f := fun x b ↦ U.map (f b) x) (.piMap a) (by simp_all [bijective_iff_existsUnique,
      funext_iff])) (sigma_bijective ..)).2 (.piMap fun _ ↦ Abelian.Ext.mk₀_bijective ..), (· + 1 |>
      sigma_bijective (fun a ↦ tilt ⋙ reprBy (ψ (B a))) (tilt ⋙ G) |>.1.subsingleton), by
    (repeat intro); exact (bijective_iff_of_comm_sq (by induction · <;> simp_all [mapₗ, map_push,
      funext_iff]) ((ofBijective (.pi fun _ ↦ mapₗ ..) (sigma_bijective ..)).lTensor _ ≪≫ₗ piRight
      ..).bijective (sigma_bijective ..)).2 (.piMap fun x ↦
      hasFlatBaseChange_of_iso_reprBy homTiltIso.symm ..)⟩
  let π b := ModuleCat.ofHom (cond b (.snd ..) (.fst ..) : _ →ₗ[OFlat] monoidAlg ℚ≥0)
  obtain ⟨⟨k, _, f⟩, l, _, f'⟩ := κ (fun _ ↦ monoidAlg ℚ≥0) (by simp [perfectRing_monoidAlgebra])
    (π ·.1) bijective_id, κ pointOrTorus (by simp [pointOrTorus, Bool.cond_true, Bool.cond_false,
    perfectRing_monoidAlgebra, instPerfectRingOFlat])
      (fun ⟨b⟩ ↦ b.rec (π false ≫ L.map (evalZero _))
    (π false ≫ L.map (discToTorus (-coeHom)) - π true ≫ L.map (discToTorus coeHom))) (by
    refine (ofLinearMap (.prod _ _) (.coprod (Algebra.linearMap ..) (Finsupp.linearCombination _
    (fun t ↦ if 0 ≤ t then (0, -single t.toNNRat 1) else (single (-t).toNNRat 1, 0)) ∘ₗ
    (coeffLinearEquiv _).1)) ?_ ?_ :
      _ ≃ₗ[_] _).bijective <;> dsimp +zetaDelta [pointOrTorus, Bool.cond_true, Bool.cond_false] <;>
          ext : 3 <;>
    simp <;> split <;> simp_all [le_of_lt, Rat.coe_toNNRat, ← one_def, ← single_neg, Prod.ext_iff])
  use f, f', Nat.rec ((k.of_comp_iff _).1 ?_) (by simp [bijective_iff_existsUnique, nontriviality])
  convert l; ext; simp [H.map]; congr; exact freeAb.hom_ext
    (by rintro _ ⟨⟨⟨⟩⟩⟩ <;> simp [D, -comp_obj] <;> rfl)
lemma isCohomEquiv_gluing_generic c : IsCohomEquiv genericCoeff (gluing (tensorLeft (tilt c))) :=
  have := IsLocalization.flat ℂ_[p] (.powers (p : OC))
  (isCohomEquiv_gluing_tilt c (isAcyclicAt_almostCoeff isPeriodRingPair_OC.pFlat_smul_eq_zero)).elim
    fun f ⟨g, e⟩ ↦
    ((coeffCompBij_id_iff_restrict (by exact exists_periodAlg_iso_genericAlg.choose)).1
    (.periodAlg_of_almostCoeff f isPeriodRingPair_OC (by clear f; tauto) isPerfectTorsionFree_tilt
    isPerfectTorsionFree_tilt ((coeffCompBij_id_iff_restrict (.refl _)).2 e.bij))).eqv
lemma subsingleton_coker_gluing {F} (h : ∀ c, IsCohomEquiv F (gluing (tensorLeft (tilt c)))) S
  [HasFlatValues S] : ∀ n, Subsingleton (H (abTensor S (Limits.cokernel gluing)) F n) :=
  (isCohomEquiv_iff_subsingleton (.map ⟨ShortComplex.exact_cokernel _⟩ _)).1 (IsBijective.eqv
  (((Comparison.id F).devissage (abTensor.flip _) (abTensor.flip.map _)).bijective_of_sigma_repr
  (fun ι c n ↦ let u B : sigma (tiltPointsSum B <| tensorLeft <| tilt <| c ·) ⟶ sigma (reprBy <|
    c ·) ⊗ tiltPointsSum B := ⟨fun _ ↦ ↾fun
  x ↦ (⟨_, ⟨preimage _ (tensorInl ≫ x.2.2.1)⟩⟩, ⟨_, ⟨tensorInr ≫ x.2.2.1⟩⟩),
    by intros; ext; simp; erw [← Category.assoc, preimage_comp, preimage_map]; rfl⟩
  have b B := (sigma_bijective ..).comp (((IsCohomEquiv.of_bijective (p := u B) fun _ ↦
    Equiv.bijective ⟨_, fun (⟨_, ⟨f⟩⟩, ⟨_, ⟨t⟩⟩) ↦ ⟨_, _, ⟨ofHom (Algebra.TensorProduct.productMap
      (tilt.map f).hom t.hom)⟩⟩, fun _ ↦ by simp; congr; aesop,
      fun ⟨⟨_, ⟨_⟩⟩, _, ⟨_⟩⟩ ↦ by simp [← ofHom_comp]⟩).comp_iff.2 (.of_isIso (freeAb.prod ..))) n)
  (bijective_iff_of_comm_sq (fun _ ↦ by ext; simp [← H.map_comp]; congr 2; exact freeAb.hom_ext (by
    rintro _ ⟨⟨⟨⟩⟩⟩ <;> show _ = _ ⊗ₜ _ <;> simp [u, sigma.ι, tmul_sub,
    ← Category.assoc, ← ofHom_comp, (· ◁ ·)] <;> rfl)) (b _) (b _)).2 (.piMap fun _ ↦ h ..)) S))
end
section
open CategoryTheory CommAlgCat Fin Ideal MvPolynomial Set MonoidalCategory RingHom
attribute [local simp] mem_span_singleton span_le Units.smul_def _root_.funext_iff
variable (k) [Field k] (d) {A : CommAlg k} {v w : Fin (d + 1) → A} {h : span (range v) = ⊤}
def projSpace : CommAlg k ⥤ Type 1 := by refine ⟨fun A ↦ Quot ((MulAction.orbitRel Aˣ _).comap
  (·.1.1 : @unimodular k _ (d + 1) A → _)), fun f ↦ ↾.map (unimodular.toFunctor.map f) fun _ _ ⟨u,
  h⟩ ↦ ⟨u.map _, by simpa using! congr(f ∘ $h)⟩, ?_, ?_⟩ <;> intros <;> ext ⟨⟩ <;> rfl
variable {k d}
lemma projSpace.exists_isUnit_of_span_eq_top [IsLocalRing A] (h : span (Set.range v) = ⊤) : ∃ i,
  IsUnit (v i) := by simpa [← h] using (IsLocalRing.maximalIdeal.isMaximal A).lt_top.not_ge
def projSpace.mk (v : Fin (d + 1) → A) (h : span (Set.range v) = ⊤) : projSpace k d A :=
  .mk _ ⟨_, h⟩
lemma projSpace.mk_eq_mk_iff_exists_unit {h'} : mk v h = mk w h' ↔ ∃ u : Aˣ, u • v = w :=
  eq_comm.trans Quotient.eq
lemma projSpace.mk_eq_mk_iff_cross_mul {h'} : mk v h = mk w h' ↔ ∀ a b, v a * w b = w a * v b :=
  mk_eq_mk_iff_exists_unit.trans ⟨by
  simp; grind, fun e ↦ have ⟨a, ha⟩ := mem_span_range_iff_exists_fun.1 (h.ge (x := 1) ⟨⟩)
  have E l := by simpa [← mul_assoc, ← Finset.sum_mul, ha] using congr(∑ i, a i * $(e i l))
  ⟨(span_singleton_eq_top.1 (eq_top_mono (by simpa using (⟨_, E ·⟩)) h')).unit, (funext E).symm⟩⟩
abbrev projSpace.affinePoint i v :=
  @mk k _ d A (i.insertNth 1 v) (span_eq_top_of_isUnit i (by simp))
lemma projSpace.mk_mem_stdChart_iff i : mk v h ∈ Subfunctor.range
  (pointMap (affinePoint (A := of k (MvPolynomial _ k)) i X)) A ↔ IsUnit (v i) :=
  ⟨fun ⟨φ, e⟩ ↦ (mk_eq_mk_iff_exists_unit.1 e).rec (by aesop), fun ⟨u, e⟩ ↦ ⟨⟨ofHom (aeval
  (u⁻¹ • v ∘ i.succAbove))⟩, mk_eq_mk_iff_exists_unit.2 ⟨u, by simp [i.forall_iff_succAbove, ← e]⟩⟩⟩
variable [CharZero k]
lemma projSpace.exists_eq_single_of_mul_eq_zero [IsLocalRing A] {w : Fin 2 → A} H hw (h : ∀ i,
  (w 1 - i * w 0) * v i = 0) : IsUnit (w 0 * ∑ i, v i) ∧ ∃ j, (mk v H, mk w hw) =
  (_ ⊗ projSpace k 1).map structureMap (affinePoint j 0, affinePoint 0 ![j]) := by
  have ⟨j, J⟩ := exists_isUnit_of_span_eq_top H
  have e := J.mul_left_eq_zero.1 (h j)
  obtain ⟨_, u⟩ := by simpa [sub_eq_zero.1 e, or_and_left] using exists_isUnit_of_span_eq_top hw
  have z i (m : v i ≠ 0) : i = j := Fin.ext (Nat.cast_injective
    (smul_left_injective k m (u.mul_left_cancel (by grind [Nat.cast_smul_eq_nsmul]))))
  use u.mul (by grind [Fintype.sum_eq_single j]),
    j; ext <;> erw [mk_eq_mk_iff_cross_mul] <;> simp <;> grind
variable (k d)
noncomputable def projSpace.stdChart (i : Fin (d + 1)) : EtaleChart d (projSpace k d) :=
  ⟨_, _, X, by simpa using .containsIdentities _,
  fun _ _ _ h ↦ by ext; simpa using mk_eq_mk_iff_cross_mul.1 h (i.succAbove _) i,
  fun _ ↦ Quot.ind (⟨span {·.1.1 i}, fun _ _ ↦ (mk_mem_stdChart_iff i).trans (by simp)⟩)⟩
instance projSpace.hasAtlas : HasAtlas d (projSpace k d) :=
  {exists_finite_charts := ⟨_, stdChart k d, fun _ h ↦ let := h.toField
  Quot.ind (exists_isUnit_of_span_eq_top ·.2 |>.imp (mk_mem_stdChart_iff · |>.2))⟩,
   exists_ideal := by rintro _ ⟨⟨⟨v⟩⟩⟩ ⟨⟨⟨w⟩⟩⟩; exact ⟨⨆
     (a) (b), span {v a * w b - w a * v b}, fun _ _ ↦ mk_eq_mk_iff_cross_mul.trans (by simp)⟩}
def projSpace.lineProductMap : projSpace k d ⊗ projSpace k 1 ⟶ projSpace k d.succ := by refine
  ⟨fun A ↦ ↾fun x ↦ x.1.liftOn₂ x.2 (fun ⟨⟨v⟩, a⟩ ⟨⟨w⟩, b⟩ ↦ mk (cons (w 0 * ∑ i, v i) fun i ↦
  (w 1 - i * w 0) * v i) ((span _).map_id.symm.trans ((map_eq_top_iff_fields _ (𝟙 A)).2 fun K ψ
  h ↦ let := h.toField; by simpa [-not_and, not_and', insert_subset_iff] using!
    (exists_eq_single_of_mul_eq_zero (unimodular.map ψ a) (unimodular.map ψ b) · |>.1))))
  ?_ ?_, ?_⟩ <;> (first | rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨c, rfl⟩ | intros; ext ⟨⟨⟩, ⟨⟩⟩)
  <;> erw [mk_eq_mk_iff_cross_mul] <;> simp [forall_fin_succ, ← Finset.mul_sum] <;> grind
variable {k : _} [Field k] {X} {d : _} {R K : CommAlg k} {g : Fin d → R} {x P s}
lemma eq_comp_structureMap_of_ker_le {ζ : R ⟶ _} {φ : R ⟶ K} (h : ker ζ.hom ≤ ker φ.hom) : φ =
  ζ ≫ structureMap := by ext r; simpa using @h (r - algebraMap _ _ (ζ r))
def CutsOutLocus (X : CommAlg k ⥤ Type 1) (P : ∀ _, _ → _) x (f : Fin d → R) :=
  ∀ C α, span (range f) ≤ ker α.hom ↔ P C (@X.map R C α x)
lemma mem_offPoints_iff [IsSepFunctor X] (l : IsField K) : x ∈ offPoints s K ↔
  ¬@ComesFromPoints _ _ X s K x := ⟨(X.map_id_apply _ x ▸ · _ _ l), fun H _ φ m ⟨z, e, q⟩ ↦
  mem_offDiagonal_of_ne l (H ⟨z, e, ·⟩) _ _ m (map_map_structureMap φ z ▸ q)⟩
lemma CutsOutLocus.preimage_fieldLocus_not (h : CutsOutLocus X P x g) :
  (fieldLocus (¬P · ·)).preimage (pointMap x) = unimodular.preimage (pointMap ⟨g⟩) :=
  by ext; simpa [↓h _, ← range_comp] using! (map_eq_top_iff_fields (span (range g)) _).symm
end
section
open Fin MvPolynomial Finset Function Finite IsScalarTower FaithfulSMul Algebra Ideal RingHom
namespace CutsOutLocus
variable {k L ι A B C : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A] {u : A}
  [CommRing B] [Algebra k B] [CommRing C] [Algebra k C] {g : ι → B} {v : ι → A} {d} (Λ : Fin (d
  + 1) → homogeneousSubmodule ι k 1) {F : MvPolynomial ι k} (φ : A →ₐ[k] C) (ψ : A →ₐ[k] L)
variable (k g v) in def IsHomogSolution := ∀ ⦃n F⦄, @IsHomogeneous _ k _ F n → F.aeval g = 0 →
  F.aeval v = 0
noncomputable abbrev evalForms v j := ((Λ j).1.aeval v : A)
@[grind =>] lemma aeval_smul_of_isHomogeneous {n} : F.IsHomogeneous n → aeval (u • v) F =
  u ^ n * aeval v F := (eval₂_mul_of_isHomogeneous · ..)
lemma IsHomogSolution.of_ker {D} [CommRing D] [Algebra k D] (ψ : A →ₐ[k] D) : (∀ r, φ r = 0 →
  ψ r = 0) → IsHomogSolution k g (φ ∘ v) →
  IsHomogSolution k g (ψ ∘ v) := by simp [IsHomogSolution, comp_def, ← comp_aeval_apply]; tauto
lemma IsHomogSolution.map : IsHomogSolution k g v → IsHomogSolution k g (φ ∘ v) :=
  of_ker 1 φ (by simp)
lemma IsHomogSolution.smul (u : C) : IsHomogSolution k g v → IsHomogSolution k g (u • φ ∘ v) :=
  (by grind [IsHomogSolution]) ∘ map φ
@[simp] lemma evalForms_map v : evalForms Λ (φ ∘ v) =
  φ ∘ evalForms Λ v := by simp [comp_aeval_apply, comp_def]
@[simp] lemma evalForms_smul : evalForms Λ (u • v) = u • evalForms Λ v := by simp [funext_iff,
  aeval_smul_of_isHomogeneous (Λ _).2]
lemma IsHomogSolution.aeval_eq_zero_of_transcendental [Algebra B L] [IsScalarTower k B L] {t :
  L} (T : Transcendental B t) (h : IsHomogSolution k g v)
  (e : aeval (t • algebraMap B L ∘ g) F = 0) : aeval v F = 0 := by
  rw [← F.sum_homogeneousComponent, map_sum] at *
  refine sum_eq_zero fun n m ↦ h (homogeneousComponent_mem ..) ?_
  simp_rw [aeval_smul_of_isHomogeneous (homogeneousComponent_mem ..), aeval_algebraMap_apply,
    ← commutes, ← Polynomial.aeval_monomial, ← map_sum] at e
  simpa [Polynomial.coeff_monomial, m] using congr($(transcendental_iff.1 T _ e).coeff n)
lemma IsHomogSolution.refl : IsHomogSolution k v v := by tauto
lemma isIntegralElem_of_valuationSubring {f : A →+* L} {x} (h : ∀ V : ValuationSubring L,
  (∀ a, f a ∈ V) → x ∈ V) : f.IsIntegralElem x := let := f.toAlgebra
  (integralClosure ..).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge
    (by simpa using (h · fun _ ↦ · isIntegral_algebraMap))
def IsNoetherNormalization (g : ι → L) := IsHomogSolution k (evalForms Λ g) (@X k _ _) ∧
  ∀ {K R : Type} [Field K] [Algebra k K] [CommRing R] [Algebra k R] (φ : R →ₐ[k] K) p v,
  IsHomogSolution k g v → evalForms Λ v = φ ∘ p → ∀ i, φ.IsIntegralElem (v i)
attribute [local instance 10] FractionRing.liftAlgebra ker_isPrime
lemma exists_algHom_comp_eq_of_integral [IsAlgClosed L] (hf : φ.IsIntegral) (h : ker φ ≤ ker ψ) :
  ∃ χ, .comp χ φ = ψ := by
  algebraize [φ.1, (kerLiftAlg ψ).1]
  choose q _ _ e using exists_ideal_over_prime_of_isIntegral _ ⊥ h
  have := LiesOver.mk e.symm
  let φ := @IsAlgClosed.lift L _ _ _ _ _ (C ⧸ q) _ _ _ _ (to_isTorsionFree ..)
    (Module.isTorsionFree_iff_algebraMap_injective.2 (kerLiftAlg_injective ψ)) _
  use .comp (φ.restrictScalars k) (toAlgHom ..), AlgHom.ext (φ.2 ⟦·⟧)
variable {Λ} {g : ι → L} [CharZero k] [Finite ι]
open IsIntegralClosure FiniteGaloisIntermediateField in
lemma exists_galois_hull [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsIntegrallyClosed A]
    [IsAlgClosed L] [Algebra A L] [FaithfulSMul A L] (I : ∀ i, IsIntegral A (g i)) :
    ∃ᵉ (B : CommAlgCat.{0} A) (_ : Fintype Gal(B/A)) (j : B →ₐ[A] L) (x), IsInvariant A B Gal(B/A) ∧
  (algebraMap A B).Finite ∧ Injective j ∧ j ∘ x = g := let K := FractionRing A
  let N := (adjoin (K := algebraicClosure K L) K (.range (⟨_, I · |>.tower_top⟩))).1
  let B := integralClosure A N
  have := isFractionRing_of_finite_extension A K N B
  ⟨.of .., .ofEquiv _ (galRestrict A K N B).1, ⟨_, by tauto⟩, (⟨⟨_, subset_adjoin K _
    ⟨·, rfl⟩⟩, .of_map (algebraMap_injective N L) (I _)⟩), isInvariant_of_isGalois' A K N B,
    finite_algebraMap.2 (finite A K N B), algebraMap_injective .., rfl⟩
lemma exists_isNoetherNormalization (h : g ≠ 0) : ∃ d Λ, evalForms Λ g 0 ≠ 0 ∧ ∀ u : Lˣ,
  IsNoetherNormalization (k := k) (d := d) Λ (u • g) := by
  have ⟨n, Λ, h₂⟩ : ∃ᵉ (n) (Λ : _ → homogeneousSubmodule ι k 1), ∀ {K} [Field K] [Algebra k K] v,
    IsHomogSolution k g v → (∀ j, (Λ j).1.aeval v = (0 : K)) → v = 0 := ⟨_, (⟨_,
    isHomogeneous_X _ <| (equivFin ι).2 ·⟩), by simp [(equivFin ι).forall_congr_left, funext_iff]⟩
  induction' n with n I
  cases h (h₂ g .refl nofun)
  obtain ⟨m, f, c, h, z⟩ | H := (em' (IsHomogSolution k (evalForms Λ g) (@X k _ _))).imp_left
    (by simpa [IsHomogSolution] using ·)
  choose a _ using not_forall.1 (funext.mt (mul_ne_zero z (X_ne_zero 0)))
  refine I (fun i ↦ Λ i.succ - a i.succ • a⁻¹ 0 • Λ 0) fun x w H ↦ h₂ x w ?_
  specialize w (c.aeval _ (Λ · |>.2)) ((aeval_bind₁ ..).trans h)
  erw [aeval_bind₁, (funext ?_ : (Λ · |>.1.aeval x) =
    (a⁻¹ 0 • evalForms Λ x 0) • algebraMap k _ ∘ a), aeval_smul_of_isHomogeneous c,
    aeval_algebraMap_apply] at w <;> simp_all [forall_fin_succ, algebraMap_eq_smul_one]
  use n, Λ, by simpa using H (isHomogeneous_X ..), fun u ↦ ⟨fun _ _ c ↦ H c ∘ by simp [
    u.smul_def, aeval_smul_of_isHomogeneous c], fun φ p v w e i ↦
    isIntegralElem_of_valuationSubring fun V W ↦ ?_⟩
  choose j x hx using @exists_max _ _ _ ⟨i⟩ _ (V.valuation ∘ v)
  algebraize [(φ.1.codRestrict V W).comp (algebraMap k _)]
  let S := AlgHom.mk V.subtype φ.2
  refine hx i ▸ mul_mem (x i).2 (V.mem_of_valuation_le_one _ (not_lt.1 fun t ↦ ?_))
  have E := (eq_inv_smul_iff₀ (ne_zero_of_map t.ne_zero)).2 ((mul_comm _ (S ∘ x)).trans (funext hx))
  have F {y} := (IsLocalRing.residue_eq_zero_iff y).trans (V.valuation_lt_one_iff y)
  simpa [t.ne_zero] using congr(V.valuation ($E j)).ge.trans_lt (F.1 (congrFun (h₂ _ (.of_ker
    S (toAlgHom ..) (by aesop) (by grind [IsHomogSolution, Units.smul_def])) fun l ↦ by
    erw [← comp_aeval_apply, F, ← congr(V.valuation ($(evalForms_map Λ S x) l))]
    simpa [*, inv_mul_lt_one₀ t.pos] using (V.valuation_le_one ⟨_, W _⟩).trans_lt t) j))
lemma IsNoetherNormalization.exists_galois_closure (h : IsNoetherNormalization Λ g) :
  ∃ (G : GrpCat.{0}) (B : CommAlgCat k) (_ : Fintype G)
  (f : MvPolynomial _ k →ₐ[k] B) (b : G → _), (∀ σ, IsHomogSolution k g (b σ) ∧ evalForms Λ (b σ) =
  f ∘ X) ∧ f.1.Finite ∧ Injective f ∧ ∀ {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ
  : B →ₐ[k] K) (u : K), u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ, ∀ σ, ψ ∘ b σ = u • φ ∘ b (τ * σ) := by
  let Ω := AlgebraicClosure (RatFunc L)
  let φ := toAlgHom k L Ω
  let A := MvPolynomial (Fin d.succ) k
  have ⟨t, ht⟩ := PSigma.mk _ ((transcendental_algebraMap_iff
    (algebraMap_injective (RatFunc L) Ω)).2 RatFunc.transcendental_X)
  have := not_exists.1 ht .X
  algebraize [(aeval (R := k) (evalForms Λ (t • φ ∘ g))).1]
  have := (faithfulSMul_iff_algebraMap_injective A Ω).2 (algebraicIndependent_iff.2 fun _ ↦
    by simpa using! h.1.aeval_eq_zero_of_transcendental ht)
  choose B _ J x Γ Z hj e using exists_galois_hull (h.2 (aeval _) X _ (.smul φ t .refl) (by aesop))
  algebraize [(algebraMap A B).comp C]
  let j := J.restrictScalars k
  have c := congr($(funext J.2) ∘ X).trans (funext (aeval_X _))
  let b (σ : Gal(B/A)) := σ.toAlgHom.restrictScalars k ∘ x
  have hb σ : IsHomogSolution k g (b σ) := .of_ker j _ (by aesop) (e ▸ .smul φ t .refl)
  have y σ : evalForms Λ (b σ) = toAlgHom k A B ∘ X := (evalForms_map ..).trans
    (hj.comp_left (c ▸ e ▸ evalForms_map Λ j x) ▸ funext (σ.4 <| X ·))
  have e : t • toAlgHom k (integralClosure L Ω) Ω ∘ (fun (σ, i) ↦ ⟨_, h.2 φ (evalForms Λ g) _ ((hb
    σ).smul j t⁻¹) (by erw [evalForms_smul, evalForms_map, y, c]; simp_all) i⟩) = j ∘ ↿b := by aesop
  refine ⟨.of _, .of .., ‹_›, _, b, (⟨hb ·, y _⟩), Z, .of_comp (funext J.2 ▸ algebraMap_injective
    ..), fun φ ψ u E ↦ (exists_algHom_comp_eq_of_integral (aeval ↿b) _ (.tower_top (bind₁ (rename
    (.mk 1) <| Λ ·)).1 _ ((ringHom_ext (by aesop)
    (by simpa [aeval_rename] using! congrFun (y 1))).symm.subst Z.to_isIntegral)) fun _ m ↦ (((e ▸
    IsHomogSolution.refl.smul _ t).of_ker j 1 (by aesop)).smul φ u).aeval_eq_zero_of_transcendental
    ht.integralClosure (by erw [e, ← comp_aeval_apply, m, map_zero])).elim fun χ H ↦ ?_⟩
  have H σ : u • φ ∘ b σ = χ ∘ b σ := by ext; simpa using! congr($H (X (σ, _))).symm
  refine .imp (by aesop) (Subspace.exists_eq_top_of_iUnion_eq_univ
    (p := fun τ ↦ (ψ.equalizer (χ.comp (τ.restrictScalars k))).toSubmodule) ?_)
  ext a
  have ⟨P, (e : P.map _ = _)⟩ := Γ.charpoly_mem_lifts (b := a)
  have := congr(P.eval₂ $((algHom_ext (congrFun (E.symm.trans (by
    simpa [y] using! congrArg (evalForms Λ) (H 1)))) : ψ.comp _ =
    χ.comp (toAlgHom ..))).1 (ψ a) = 0)
  repeat erw [← P.eval₂_map, e, Polynomial.eval₂_finsetProd, prod_eq_zero_iff] at this
  simpa using this.le ⟨1, by simp⟩
end CutsOutLocus
open CategoryTheory AlgebraicGeometry CutsOutLocus CommAlgCat ProjSpace Over Category
variable {k ι F} [Field k] {R} [Algebra R.1 k] {Y : Over (Spec R)} [Finite ι] (L : LineBundle _ ι)
  {A B : CommAlg k} (x x' : PointsIn Y A) (v : ι → A) [Field F] [Algebra k F] [hL :
  Fact (L.IsProjEmbedding Y.hom)]
abbrev IsUnimodCoords := L.IsHomogCoords x.1.left v ∧ ∃ i, IsUnit (v i)
omit [Finite ι] in
lemma IsUnimodCoords.exists_chart_coords (hK :
  IsField A) {d} [IsChartCovered d (algPointsOf k R Y)] : ∃ᵉ (c : EtaleChart d _)
  (κ) (w), .map κ c.point = x ∧ IsUnimodCoords L c.point w := let := hK.toField
  ((isOpenSub_of_landsIn (·.1.1) (by tauto) ⟨_, by tauto⟩ fun _ _ ↦
    .rfl).exists_chart_le hK (L.exists_landsIn
    _).choose_spec).imp fun a ⟨⟨_, E⟩, I⟩ ↦ ⟨_, _, E, hL.1.1.2 I, _, L.isUnit_transition I I⟩
variable {L x x' v} {ξ : PointsIn Y (of k F)} {g i} (hξ : IsUnimodCoords L ξ g)
omit [Finite ι] [Fact (L.IsProjEmbedding Y.hom)] in
lemma IsUnimodCoords.exists_unit_smul_eq {w} : IsUnimodCoords L x v → IsUnimodCoords L x w → ∃ u :
  Aˣ, u • v = w | ⟨h, i, u⟩, ⟨H, _⟩ => ⟨(
  u.ringInverse.mul ((H i).1.1 ((h i).1.2 u))).unit, by ext; simp; grind [h i, H i]⟩
section
omit [Finite ι]
lemma IsUnimodCoords.map_unit_smul (h : IsUnimodCoords L x v) (φ : A ⟶ B) (u : Bˣ) :
  IsUnimodCoords L (x.map φ) (u • φ ∘ v) :=
  ⟨(h.1.map hL.1.1 h.2.choose_spec _).smul u.isUnit, h.2.imp (by simp_all [IsUnit.map])⟩
lemma IsUnimodCoords.comp (h : IsUnimodCoords L x v) (φ : A ⟶ B) :
  IsUnimodCoords L (x.map φ) (φ ∘ v) := by simpa using h.map_unit_smul φ 1
lemma IsUnimodCoords.ext (h : IsUnimodCoords L x v) (H : IsUnimodCoords L x' v) : x =
  x' := congr(⟨$(OverMorphism.ext
  (hL.1.eq_of_isHomogCoords (by erw [w, w]) h.1 H.1 (by grind [LineBundle.IsHomogCoords])))⟩)
end
include hξ
lemma IsUnimodCoords.exists_descend_of_injective (φ : A ⟶ _) (I : Injective φ) (e : g i • φ ∘ v =
  g) : ∃ x, IsUnimodCoords L x v ∧ ξ = x.map φ := by
  have hi := isUnit_of_mul_isUnit_left (e ▸ hξ).2.choose_spec
  have hv := (map_eq_one_iff _ I).1 (hi.mul_eq_left.1 congr($e i)) ▸ isUnit_one
  obtain ⟨⟨j, _, a, rfl⟩, t, b, ht⟩ := hL.1.exists_isClosedImmersion,
    exists_isHomogCoords (specAlg k R A).1.hom hv
  obtain ⟨x, rfl⟩ := (exists_ideal_le_ker_iff_factors j t).elim fun _ H ↦ by simpa using ((H.2
    (.id _)).1 (.trans ((H.2 φ.1.1).2 ⟨_, isProjEmbedding_projSpace.eq_of_isHomogCoords
    (by erw [assoc, a, assoc, b, w, ((specAlg ..).map φ).1.w]) hξ.1
    (e ▸ (ht.map (isLinearSystem_hyperplaneBundle.pull _) hv _).smul hi)⟩) (by aesop_cat)))
  exact ⟨⟨homMk x⟩, by tauto, hξ.ext (e ▸ map_unit_smul (by tauto) _ hi.unit)⟩
lemma IsUnimodCoords.exists_universal_chart (hv : IsHomogSolution k g v) (h : v i ≠ 0) : ∃ D y,
  ∃ (j : D ⟶ of k F) (G : D → MvPolynomial ι k), (Injective j ∧ ξ = .map j y) ∧ ∀ {C w},
  IsHomogSolution k g w → IsUnit (w i) → ∃ φ :
  D ⟶ C, (∀ d, Associated (aeval w (G d)) (φ d)) ∧ IsUnimodCoords L (y.map φ) w := by
  have h := Ne.isUnit (by simpa [h] using hv (isHomogeneous_X _ i))
  choose G hG E using (exists_homogenization (isHomogeneous_X k i) · .refl)
  choose φ a b using fun {C : CommAlg k} {w} (u : IsUnit (w i)) ↦
    (⟨aeval (u.unit⁻¹.1 • w), by simp [← mul_assoc, funext_iff],
    (by simp [← E ·, aeval_smul_of_isHomogeneous (hG _), associated_unit_mul_right,
    IsUnit.pow])⟩ : ∃ φ : _ →ₐ[k] C, w i • φ ∘ X = w ∧ ∀ P, Associated ((G P).aeval w) (φ P))
  obtain ⟨y, H, e⟩ := hξ.exists_descend_of_injective (ofHom _) (kerLiftAlg_injective (φ h)) (v :=
    (⟦X ·⟧)) (a h)
  exact ⟨_, y, _, _, ⟨kerLiftAlg_injective _, e⟩, fun w u ↦ ⟨ofHom (Quotient.liftₐ _ _ (by
    simpa [(b u _).eq_zero_iff, (b h _).eq_zero_iff] using w <| hG ·)),
    (congrArg _ ·.out_eq |>.subst (b u _)), (a u).subst (H.map_unit_smul _ u.unit)⟩⟩
lemma IsUnimodCoords.exists_function_const [IsAlgClosed k] (f : _ ⟶ affineSpace k 1) : ∃ c,
  ∀ {A} [Nontrivial A.1] {x v}, IsUnimodCoords L x v → IsHomogSolution k g v → (f A x).1 0 =
  algebraMap k A c := have := hξ.2.nonempty
  (IsAIC.mem_range_of_isIntegralElem (isIntegralElem_of_valuationSubring (x :=
    (f _ ξ).1 0) fun V hV ↦ by
    choose i w hw using Finite.exists_max (V.valuation ∘ g)
    obtain ⟨y, -, rfl⟩ := hξ.exists_descend_of_injective (ofHom (Subalgebra.val ⟨_, hV⟩)) (by simp)
      (.trans (mul_comm ..) (funext hw))
    simpa using! Subtype.prop _)).imp fun c e ↦ fun h@⟨_, _, u⟩ hv ↦ by
                          choose _ y j _ I φ _ H using hξ.exists_universal_chart hv u.ne_zero
                          simp_all [h.ext (H ..)]
                          exact (I.1 ((j.1.2 c).trans e) ▸ (φ _ u).1.2 c :)
lemma IsUnimodCoords.exists_mem_open_of_isUnit {V} (hV : IsOpenSub V) (hx : ξ ∈ V _) : ∃ b,
  aeval (R := k) g b ≠ 0 ∧ ∀ {C w}, IsHomogSolution k g w → IsUnit (aeval w b) → ∃ z ∈ V C,
  IsUnimodCoords L z w := hξ.2.elim fun i hi ↦ by
  choose _ z _ G _ _ _ H using hξ.exists_universal_chart .refl hi.ne_zero
  have ⟨b, _, _⟩ := hV.exists_basicOpen _ z (Field.toIsField _) ((H .refl hi).ext hξ ▸ hx)
  use G b * X i; simp_all [← isUnit_iff_ne_zero]; grind [Associated.isUnit_iff]
end
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor
noncomputable section
section
open AddMonoidAlgebra CategoryTheory projLine TotalH TensorProduct Limits ShortComplex
set_option backward.isDefEq.respectTransparency false
attribute [-simp] Bool.cond_eq_ite
attribute [local simp] Bool.cond_true Bool.cond_false
lemma TotalH.bijective_of_two_triangles {K P I W B a e} [AddGroup K] [AddGroup P] [AddGroup I]
  [AddGroup W] [AddGroup B] {b : W →+ I} {c : I →+ B} {d : I →+ P} {f : K →+ I} (h : Function.Exact
  a b ∧ Function.Exact b c ∧ Function.Exact c a) (k : Function.Exact d e ∧ Function.Exact e f ∧
  Function.Exact f d) (t : Function.Bijective (d.comp b)) : Function.Bijective (c.comp f) := by
  simp [Function.Exact, ↓injective_iff_map_eq_zero, Function.Bijective, t.2.of_comp (f := d) _] at *
  use by grind, (h.2.2 · |>.1 (t.1 _ (by grind)) |>.rec
    fun r ↦ (t.2 (d r)).rec fun w ↦ by grind [k.2.2 (r - b w), sub_self, sub_zero])
variable {C} [Category C] {W' W Z₀ : AbFunctor C} {S T : ShortComplex (AbFunctor C)}
lemma toda_squares {i : W' ⟶ W} [Mono i] {δ' δ} (w : δ' ≫ i = i ≫ δ) (z : _ ⟶ W) (o : z ≫ δ = 0)
  (k₁ : S.ShortExact) (k₂ : T.ShortExact) f α κ n α₁ (e₁ : α₁ ≫ S.f = i ≫ f) (e₂ : δ ≫ f = 0) (e₃ :
  δ' ≫ α = i ≫ κ ≫ T.f) (n₁ : α₁ ≫ n = α ≫ T.g) : ∃ B K, ∃ (j : B ⟶ S.X₃) (y : Z₀ ⟶ K), ∃ ω,
  (∀ Q R g (r : Q ⟶ R) s, i ≫ g = 0 → δ ≫ g = 0 → g ≫ r = f ≫ S.g ≫ s → ∃ t, t ≫ r = j ≫ s) ∧ ∀ E
  [Category E] (Φ : _ ⥤ AbFunctor E) [IsExactFunctor Φ] F, (∀ n, Subsingleton (H (Φ (cokernel i)) F
  n)) → (∀ N (τ : N ⟶ _) m s, comp (F := F) (.homClass (Φ.map j)) (comp (.map Φ (k₁.extClass.comp
  (H.map _ n 1 k₂.extClass) rfl).toTotalH) m) = comp (.map Φ ω) s → comp (.homClass (τ ≫ Φ.map (z ≫
  κ))) m = comp (.homClass (τ ≫ Φ.map y)) s) ∧ Function.Surjective (comp (F := F) (.map Φ ω)) := by
  let D := pushout.desc i δ w
  obtain ⟨c₁, c₂, _⟩ := ShortExact.mk (exact_cokernel (Abelian.factorThruCoimage D)),
    ShortExact.mk (exact_cokernel (kernel.ι D)), k₁.2, k₂.2
  have s : CommSq (pushout.desc α₁ 0 (by simp [← cancel_mono S.f, reassoc_of% w, *]))
    (cokernel.π _) S.f (Abelian.factorThruCoimage D ≫ f) := ⟨by ext1 <;> simp [D, *]⟩
  have q : pushout.desc α _ e₃ ≫ T.g = cokernel.π _ ≫ s.lift ≫ n := by ext1 <;> simp [*]
  have ⟨u, h⟩ := k₂.1.lift' (kernel.ι D ≫ pushout.desc α _ e₃) (by simp [*, -CommSq.fac_left_assoc])
  refine ⟨_, _, cokernel.desc _ (f ≫ S.g) (by simp [← reassoc_of% s.fac_right]), kernel.lift D
    (z ≫ pushout.inr ..) (by simpa [D]), comp c₁.extClass.toTotalH c₂.extClass.toTotalH, by
      intros; use cokernel.desc _ ‹_› ?_ <;> simp [coequalizer.hom_ext_iff, pushout.hom_ext_iff, D,
      *], fun _ _ Φ _ F e ↦ (?_ : Function.Bijective _).imp_left fun b _ τ m _ a ↦ by
    simp [← b ((comp_assoc_of_sq (y := TotalH.homClass (Φ.map u))
      (by simp [← map_homClass, H.map, c₂.extClass_naturality k₂ ⟨_, _, _, h, q⟩, ← TotalH.map_comp,
      ← Abelian.Ext.comp_assoc (h₁₂ := zero_add 1), ← c₁.extClass_naturality k₁ ⟨_, f, _,
      s.fac_right, (cokernel.π_desc ..).symm⟩, -map_of, comp_of]) m).trans a),
      homClass_comp_homClass_comp, ← Functor.map_comp]; congr 5; simp [← cancel_mono T.f, *]⟩
  simpa [funext (map_comp_assoc _)] using! bijective_of_two_triangles (exact_triangle (c₁.map Φ) F)
    (exact_triangle (c₂.map Φ) _) ((funext (homClass_comp_homClass_comp
    _)).symm.subst (((isCohomEquiv_iff_subsingleton (.map ⟨exact_cokernel _⟩ Φ)).2
    (IsCohomEquiv.of_isIso (Φ.map (inv _ (I := isIso_cokernel_map_of_isPushout (.flip
    (.of_hasPushout ..))))) · |>.2.subsingleton)).comp_iff.1 (by simpa [← Φ.map_comp, D] using
    (isCohomEquiv_iff_subsingleton (.map ⟨exact_cokernel i⟩ Φ)).2 e)).bijective_totalH)
variable {ℓ A} [CommRing A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A} (M : TorsionCoeff g) (Θ :
  Theory g) {S : AbFunctor C} [HasFlatValues S]
lemma TorsionCoeff.sliceEquiv_mulClass (v : TotalH S _) : sliceEquiv
  (M.mulClass (etaClass g).toTotalH v) = comp (.map (restrictAlong _) v) M.cupClass.toTotalH := by
  erw [← M.onElements.mulClass_eq_comp_etaAt (S := _ ⋙ S) _ _ rfl, ← comp_id (x := TotalH.map _ v),
    ← map_restrictAlong_etaClass (elementsProj _), ← M.mulClass_naturality, comp_id]; rfl
lemma etaAt_swap x : let t q : S ⟶ abTensor S _ := tensorPoint (freeAbSectionMap q) S
  let o q r := comp (pullbackAlong (t q) x) (Θ.etaAt (freeAbSectionMap r)).toTotalH
  pullbackAlong (t (basePt g)) x = 0 → ∀ q r, o q r = o r q := by
  intro t o k
  have D q r := (exists_etaClass_supported_diagonal ..).elim fun J ⟨z, ξ, e⟩ ↦ have c a :=
      (Θ.mulClass_congr_of_eq_on_zeros J ξ (a := t a) (a' := t r) · x ▸ Θ.mulClass_eq_comp_etaAt _ _
      e _); c q (by ext; exact congr(_ ⊗ₜ .of $(z · ·))) ▸ c r (by simp)
  simpa [by simpa [k, Θ.comp_etaAt_basePt] using (D · (basePt _))] using D
lemma line_formula_of_mulClass_injective (i : Function.Injective (Θ.mulClass (S :=
  S) (etaClass g).toTotalH)) (s : ∀ x, Θ.onElements.mulClass (S := _ ⋙
  S) (etaClass _).toTotalH (sliceEquiv x) = comp (.map (restrictAlong _) x) Θ.cupClass.toTotalH →
  x ∈ (Θ.mulClass (etaClass g).toTotalH).range) : IsLerayHirschBasis Θ.lineBasis
  S := have a S (x : TotalH S Θ.F) := (x.map_map (restrictAlong (elementsProj (projLineAlong g)))
    (restrictAlong (sectionLift (𝟭 C) (basePt g)))).trans x.map_id
  (Comparison.bijective_iff_of_comm_sq
    (fun _ ↦ by simp [lerayHirsch, Finsupp.sum_fintype, mapThenComp, TorsionCoeff.lineBasis,
    Θ.sliceEquiv_mulClass, Function.Exact.splitSurjectiveEquiv]; abel!)
    (Finsupp.equivFunOnFinite.trans (.boolArrowEquivProd _)).symm.bijective sliceEquiv.bijective).1
    (Function.Exact.splitSurjectiveEquiv (f := (Θ.mulClass _).toIntLinearMap) (g :=
    (comp _).toIntLinearMap) (.of_comp_of_mem_range (funext (Θ.comp_etaAt_basePt · ▸
    Θ.mulClass_eq_comp_etaAt _ _ rfl _)) fun x e ↦ s x (sliceEquiv.injective (by
    erw [TorsionCoeff.sliceEquiv_mulClass, map_homClass_comp]
    exact .trans (etaAt_swap Θ.onElements.onElements (S := _ ⋙ _) _ (by
      simpa -dsimp [map_homClass_comp] using! congr(TotalH.map (restrictAlong _)
        (.map (restrictAlong _) $e))) ⟨_, (·.1.2)⟩ _) ((comp_assoc ..).trans
      (congrArg _ (by erw [TotalH.map_comp, Θ.onElements.map_etaAt_onElements]; rfl)))))) i
    ⟨(sliceEquiv.symm.toAddMonoidHom.comp (TotalH.map (restrictAlong _))).toIntLinearMap,
    LinearMap.ext fun x ↦ ((map_homClass_comp.trans (a .. ▸ rfl)).congr (a _ x)).1
    (congrArg _ (sliceEquiv.right_inv _))⟩).1.symm.bijective
lemma hasLineFormula_tiltTheory M [Algebra A ℂ_[ℓ]] ac : (tiltTheory A M ac).HasLineFormula := by
  have := (@cyclotomicRootSystem _ A).2
  have ⟨χ, hχ⟩ := exists_tilt_lift_of_character ((algebraMap A _).1.comp
    ((Units.coeHom _).comp cyclotomicRootSystem.1)) (by aesop)
  choose ε h using @exists_unit_smul_unimodularRow
  let F c x : (cocycle (genericTestOver A)).extension.X₂ c := (⟨ε x⟩, .of ⟨⟦x⟧⟩)
  have hF c d f x : (cocycle _).extension.X₂.map f (F c x) = F d _ :=
    Prod.ext (add_rowUnit_eq _ _ (.trans (by simp -dsimp [← h]) (h _))) rfl
  let ρ c : PadicTest.tilt c →*₀ c.GenericRing :=
    .comp (.ofClass (algebraMap ..)) (Perfection.teichmuller₀ ..)
  have n c d f x : (ringOf (genericTestOver A)).map f (ρ c x) = ρ d _ :=
    untilt_tiltMap f.1 x ▸ c.mapGeneric_algebraMap ..
  have G c (s : OFlat) : ρ c (algebraMap _ _ s) = _ :=
    (untilt_tiltMap c.structureMap s ▸ c.structMap_coe _).symm
  let Θ := tiltTheory A M ac
  have l := @subsingleton_coker_gluing _ _ Θ.F (isCohomEquiv_gluing_tilt · ac |>.2.2)
  obtain ⟨_, _, j, y, _, -, t⟩ := by
    refine toda_squares (oneSub_comp_gluing χ) (origin ⟨true⟩) (freeAb.hom_ext (by simp -dsimp))
      (cocycle _).shortExact_extension (shortExact_kummerSeq (genericTestOver A)) (freeAb.desc
      (fun c y ↦ F c (0, 0) - F _ (cond y.1.1 (· - 1, 1) (0, ·) (ρ c (y.2.1.hom (single 1 1)))))
      fun _ _ ↦ ?_) (projFirst ≫ freeAb.desc (fun _ t ↦ .comp (.mk' .up (by tauto))
      ((ρ _).toMonoidHom.comp (t.1.hom.1.1.comp (of ..))).toHomUnits.toAdditiveRight) fun _ _ _ _ ↦
      AddMonoidHom.ext fun _ ↦ Gm.ext.2 (n ..).symm) (projFirst ≫ freeAb.map (toUnit _) ≫ tateGen _)
      _ _ ?_ ?_ ?_ (Category.comp_id _) <;>
      (try apply freeAb.hom_ext) <;> rintro c ⟨⟨⟨⟩⟩, y⟩ <;> simp [*, charTwist, ← neg_eq_iff_eq_neg,
      -coe_algebraMap, -Functor.comp_map, -Functor.comp_obj] <;> try rfl
    exacts [eq_sub_of_add_eq (Prod.ext_iff.2 (.imp ULift.ext_iff.2 ((zero_add _).trans ∘ congrArg
      FreeAbelianGroup.of) (smul_unimodularRow_inj (by erw [mul_smul, ← h, ← h]; simpa using ⟨rfl,
      Units.mul_inv _⟩)))), sub_eq_of_eq_add (AddMonoidHom.ext fun _ ↦ Gm.ext.2 (congr(ρ c (y.1.hom
      $(lift_of ..))).trans
      (by erw [map_mul, map_mul, AlgHom.commutes, G, hχ, freeAb.desc_of]; rfl)))]
  erw [H.map_id, ← etaClass] at t
  refine lerayHirsch_bijective_of_repr fun c ↦ line_formula_of_mulClass_injective Θ (.of_ker _ fun v
    a ↦ ((Θ.tateGen_comp_tateAction v).congr (map_zero _)).1 ((t _ _ _ (l _)).1 _ (tensorPoint (𝟙 _)
    _) _ 0 (a ▸ by simp))) fun x a ↦ ((t _ _ _ (l _)).2 (pullbackAlong ((abTensor _).map j) x)).imp'
    (pullbackAlong (tensorPoint y _)) fun w b ↦ sliceEquiv.injective ?_
  erw [Θ.sliceEquiv_mulClass, map_homClass_comp, comp_assoc, ← (t _ (restrictAlong _ ⋙ _) ..).1 _
    (tensorPoint (𝟙 _) _), Θ.onElements.tateGen_comp_tateAction]
  erw [← TotalH.map_map, map_restrictAlong_etaClass, a]
  simpa -dsimp [map_comp_assoc,
    TotalH.map_map] using! congr(comp (.map (restrictAlong _) $b) _).symm
  exact fun _ ↦ ((IsCohomEquiv.of_isIso (NatIso.ofComponents (F := abTensor (abTensor _ (freeAb _))
    _) (fun _ ↦ (rightComm ℤ ..).toAddCommGrpIso) fun _ ↦ addCommGrp_tensor_hom_ext (·.inductionOn
    (by tauto) (by simp_all [add_tmul]))).1).bijective_totalH.1.comp (sliceEquiv (N :=
    abTensor (freeAb _) _).symm.injective.comp (DirectSum.of_injective _))).subsingleton
end
section
open CategoryTheory CommAlgCat Finsupp Ideal TotalH MonoidalCategory
section
seal locConstCoeff projLine
set_option backward.isDefEq.respectTransparency false
variable {C} [Category C] {ℓ A} [CommRing A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A}
  {M : TorsionCoeff g}
lemma line_formula_of_basis (Θ : Theory g) {I} {d : I → ℕ} (θ : ∀ i, H (restrictAlong _ Θ.F) _ (d
  i)) i (hi : (θ i).toTotalH = Θ.cupClass.toTotalH) (h : IsLerayHirschBasis θ (freeAb (pointFunctor
  _))) (h' : IsLerayHirschBasis θ (freeAb (projLineAlong g))) : IsLerayHirschBasis Θ.lineBasis
  (freeAb (pointFunctor _)) := line_formula_of_mulClass_injective Θ (fun v w k ↦ single_injective i
  (h.1 (by simp_all only [lerayHirsch_single, ← Θ.sliceEquiv_mulClass]))) fun x k ↦
  (h.2 _).imp' (· i) fun w e ↦ (Finsupp.ext_iff.1 (((isClosedClass_lerayHirsch.iff_of_isIso
  (freeAb.map (λ_ _).inv ≫ freeAb.prod (pointFunctor _) _)).1 h').1 ((lerayHirsch_naturality θ _
  (fun _ _ ↦ Θ.mulClass_naturality ..) w).trans (by rwa [lerayHirsch_single,
  map_restrictAlong_etaClass, e, hi]))) i).trans (by simp)
def etaOneClass c := H.map _ (freeAb.map (toUnit (testOfPoint A _ ⋙ reprBy c))) 2
  (.map _ oneLocConst 2 Theory.locallyConstant.cupClass)
lemma pull_etaOneClass {T c} (u : pointFunctor C ⟶ g ⋙ reprBy c) :
  comp ((Comparison.restrict (Functor.Elements.precomp g _) _).pull
  (freeAbMap ((elementsProj _).whiskerLeft u)) 2 (etaOneClass c)).toTotalH T =
  pullbackAlong (oneLocConst (g := elementsProj _ ⋙ g)) (comp T M.cupClass.toTotalH) := by
  simp [etaOneClass, Comparison.pull, H.map, H.push]
  erw [Abelian.Ext.toTotalH, ← homClass_comp_of, ← map_of, comp_assoc,
    Theory.locallyConstant.onElements.etaAt_naturality]
  exact congr(pullbackAlong $freeAb.hom_ext _)
variable (A) (k : Type) [Field k] [Algebra A k]
def TestOver.resScalars : TestOver k ⥤ TestOver A :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ restrictAlg ..) (·.2)
def TestOver.structurePt [IsAlgClosed k] :
  pointFunctor _ ⟶ resScalars A k ⋙ reprBy ⟨of A k, isTest_of_preValuationRing⟩ := sectionMap
  ⟨fun B ↦ ⟨⟨CommAlg.homOfRingHom _ (by tauto)⟩⟩, (congr(⟨⟨$(by ext; apply ·.1.1.2)⟩⟩))⟩
lemma hasUnivPoints_structurePt [IsAlgClosed k] : (Comparison.restrict (TestOver.resScalars A k)
  Theory.locallyConstant.F).HasUnivPoints (TestOver.structurePt A k) := fun B y ↦ ⟨⟨@of k _ _ _
  y.1.1.1.1.toAlgebra, B.2⟩, ⟨⟩, ⟨CommAlg.homOfRingHom _ (y.1.1.1.2 · |>.symm)⟩, rfl, fun _ _ f e ↦
  ⟨⟨CommAlg.homOfRingHom _ (congr($e.1.1.1 ·).symm)⟩, by bound⟩,
  ConcreteCategory.bijective_of_isIso ((locConstCoeff _).map (𝟙 _))⟩
abbrev TestOver.ofSelf (A) [CommRing A] [IsAICLocal A] [PreValuationRing A] : TestOver A :=
  ⟨of A A, isTest_of_preValuationRing⟩
lemma pointMap_ofSelf_bijective {A} [CommRing A] [IsAICLocal A] [PreValuationRing A] :
  AllBijective (@pointMap _ _ (pointFunctor _) (TestOver.ofSelf A) ⟨⟩
  ·) := fun _ ↦ ⟨fun _ _ _ ↦ congr(⟨⟨$(by ext)⟩⟩), (⟨⟨⟨structureMap⟩⟩, .refl ·⟩)⟩
variable [PreValuationRing A]
lemma hasLineFormula_of_cupClass_ne_zero (hg : ∀ d, ∀ a ≠ 0, IsUnit (algebraMap A (g d).1 a)) (M :
  TorsionCoeff g) (ne : ¬∀ y, lerayHirsch M.lineBasis (freeAb (pointFunctor C)) (.single false
  y) = 0) : Theory.locallyConstant (A := A).HasLineFormula := lerayHirsch_bijective_of_repr fun _ ↦
  lerayHirsch_bijective_of_fields isDetectedAtPoints_projLine fun ⟨k, o⟩ _ hc ↦ let := hc.toField
  have := o.isAlgClosed
  have := InvertsPrime.mk (map_natCast (algebraMap A k) ℓ ▸ InvertsPrime.isUnit_prime.map _)
  have z c : (@IdealFamily.ofMaximalIdeal k _ _).I c = ⊥ := by simp [IdealFamily.ofMaximalIdeal,
    IsLocalRing.maximalIdeal_eq_bot]
  let Θ : Theory (TestOver.resScalars A k ⋙ 𝟭 _) := {Theory.locallyConstant with}
  (exists_lerayHirsch_basis Theory.locallyConstant.1.onElements isDetectedAtPoints_projLine
    .of_top_le ⟨2, Θ.cupClass⟩).elim fun b t ↦
    (TorsionCoeff.HasLineFormula.bijective_iff_of_hasUnivPoints _ (hasUnivPoints_structurePt A k)).2
    (line_formula_of_basis Θ _ ⟨_, t.1 fun e ↦ ne (M.comp_oneLocConst_surjective.forall.2 fun T ↦ by
  let l Q {T} h h' : (residueTest (.ofSelf A) Q).right ⟶ T :=
    ⟨ofHom (ResidueField.liftₐ _ structureMap.1 h h')⟩
  have z : etaOneClass _ = 0 := (H.map_map ..).symm.trans (((PrimeSpectrum.le_iff_specializes
    ..).1 bot_le).mem_open (isDetectedAtPoints_projLine.1 _ 2 (etaOneClass _)).1 ((H.map_map
    ..).trans ((isDetectedAtPoints_projLine.2 _ ⟨k, o⟩ (l (.comap _ ⊥) le_rfl fun _ ↦ .mk0 _)
    (Field.toIsField (ResidueField _)) hc 2).1 ((H.map_map ..).trans (((hasUnivPoints_structurePt A
    k).on_elements.isBijective 2).1 (DirectSum.of_injective _ (((comp_id.congr
    (congrArg _ id_comp)).1 (pull_etaOneClass (M := Θ.1) _)).trans (by simpa))))))))
  erw [lerayHirsch_single, map_comp_assoc, map_homClass, ← pull_etaOneClass (sectionMap
    ⟨(⟨l ⊥ bot_le <| hg ·⟩), fun _ ↦ congr(⟨⟨ofHom $(ResidueField.algHom_ext (by ext))⟩⟩)⟩), z]
  simp)⟩ rfl (isClosedClass_lerayHirsch.of_bijective _ pointMap_ofSelf_bijective (t.2 _ (z _)))
    (isClosedClass_lerayHirsch.of_bijective (E := _ ⋙ projLinePow Unit) {app _ := ↾_} (fun _ ↦
    (Equiv.funUnique ..).bijective)
    (bijective_lerayHirsch_iff.2 (isAffinelyCovered_projLinePow.devissage_bijective
    lerayHirsch.devissage (bijective_lerayHirsch_iff.1 <| t.2 · (z _))) :)))
lemma hasLineFormula_locallyConstant [Algebra A ℂ_[ℓ]] [FaithfulSMul A ℂ_[ℓ]] :
  Theory.locallyConstant (A := A).HasLineFormula :=
  have m := isAcyclicAt_almostCoeff (N := _ ⧸ span {pFlat}) (by simp [Algebra.smul_def])
  hasLineFormula_of_cupClass_ne_zero A (fun d _ k ↦ .map d.structMap (by simpa)) (tiltTheory A _
    m).1 fun z ↦ by simpa [Submodule.mem_smul_top_iff, mem_span_singleton_mul, pFlat_ne_zero] using
    (LinearMap.ker_tensorProductMk _).le ((TensorProduct.lid OFlat _).symm.injective
    (ULift.up_injective ((sectionEquiv ..).injective
    ((m _).bijective_totalH.1 ((IsCohomEquiv.of_bijective (p := toUnit (_ ⋙ reprBy _)) fun _ ↦
    ⟨fun _ _ _ ↦ congr(⟨$(isInitialSelf.hom_ext ..)⟩), (⟨⟨structureMap⟩,
    .refl ·⟩)⟩).bijective_totalH.2.forall₂.2 (fun v w ↦ congrArg _ (single_injective _
    ((hasLineFormula_tiltTheory ..).1 (by erw [z, z])))) ..)))) : _ ⊗ₜ ⟨_, not_isUnit_pFlat⟩ = 0)
lemma IsProperOver.isCohomDense_of_coincidences {Λ Y Z D s} (h : @IsProperOver Z D s) {U J}
  [Finite.{1} J] (P : J → (Y ⟶ Z)) (H : ∀ {k} [Field k] [IsAlgClosed k] z B x,
  (P · B.1 x).FactorsThrough (P · ⟨k⟩ z) → x ∈ U B) : IsCohomDense (Y := testIncl.comp Y)
  (locConstCoeff Λ) U := .of_affine_cover (V := fun ε : J → Set J ↦ ⟨({y | ∀ᵉ (i) (j ∈ ε i),
  P i · y = P j _ y}), by simp; grind⟩) (fun ε ↦ isRelAffine_of_zero_unit_locus fun y ↦ by
  choose I h using h.1; use ⋃ (i) (j ∈ ε i), I _ (P i _ y) (P j _ y), ∅
  simp_all; tauto) fun O y ↦ ⟨_, H (Y.map (CommRingCat.ofHom
  O.subtype) y), fun _ _ _ ↦ h.injective_map_valuationSubring O (by aesop)⟩
end
open CartesianMonoidalCategory Finset IsLocalRing projLine Subfunctor relFreeAb
open Polynomial hiding comp
set_option backward.isDefEq.respectTransparency false
variable {Γ} [Category Γ] {ℓ d} {A B R T : Type} [CommRing A] {g : Γ ⥤ TestOver A} [CommRing B]
  [CommRing R] {E Y : TestOver A ⥤ Type 1} {U V : Subfunctor Y} [CommRing T] [Algebra A T]
  (e : MvPolynomial (Fin d) A ≃ₐ[A] T)
def multihomIdeal (Φ : MvPolynomial _ A) J (φ : A →+* B) (r : Fin d → B × B) :=
  span {(∑ m ∈ Φ.support, φ
  (Φ.coeff m) * ∏ i, (r i).1 ^ m i * (r i).2 ^ (Φ.degreeOf i - m i)) * ∏ i, (r i).2} ⊔ .map φ J
lemma map_multihomIdeal Φ {J} {φ : A →+* _} (f : B →+* R) {r r'} {l : Fin d → Rˣ} (h : ∀ i, .map f f
  (r i) = (l i).1 • r' i) : (multihomIdeal Φ J φ r).map f = multihomIdeal Φ J (f.comp φ) r' := by
  erw [Ideal.map_sup, multihomIdeal,
    ← span_singleton_mul_right_unit (∏ i, l i * l i ^ Φ.degreeOf i).isUnit]
  simp_all [J.map_map, Finset.sum_mul, Prod.ext_iff, mul_assoc, ← prod_mul_distrib]
  congr! 6; rw [← pow_mul_pow_sub _ (Φ.monomial_le_degreeOf _ ‹_›)]; ring
variable (A T) in
abbrev testSpec := (ObjectProperty.ι _ : TestOver A ⥤ _) ⋙ reprBy (of A T)
abbrev testSpec.asAlgHom {c} (ψ : testSpec A T c) : T →ₐ[A] c.1 := ψ.1.hom
def testUnitLocus (a : T) : Subfunctor (testSpec A T) :=
  ⟨fun _ ↦ {ψ | IsUnit (testSpec.asAlgHom ψ a)}, fun f _ ↦ .map f.1.1⟩
open IsLocalization Away Algebra in
lemma testUnitLocus.nonempty_iso_away (a : T) (L :=
  Localization.Away a) [CommRing L] [Algebra A L] [Algebra T L] [IsScalarTower A T L] [Away a L] :
  Nonempty (testSpec A L ≅ (testUnitLocus a).toFunctor) := by refine' ⟨
  NatIso.ofComponents fun _ ↦ Equiv.toIso ⟨(⟨⟨ofHom (algHom ..) ≫ _⟩, (algebraMap_isUnit a).map
  ·.1.1⟩), (⟨ofHom <| liftAlgHom a ·.2⟩), fun _ ↦ congr(⟨ofHom $(algHom_ext (.powers a) _)⟩), fun _
  ↦ congr(⟨⟨ofHom $_⟩, _⟩)⟩⟩ <;> ext <;> apply IsLocalization.lift_eq
def affineToLines : testSpec A T ⟶ ringOf (𝟭 _) ⋙ projLinePow (Fin d) :=
  ⟨fun _ ↦ ↾fun ψ i ↦ affinePt (testSpec.asAlgHom ψ (e (.X i))), fun _ _ _ ↦
  congr(↾fun _ _ ↦ $(.symm (map_affinePt ..)))⟩
seal Finset.sum in
instance : Mono (affineToLines e) := mono_of_app_injective fun c ψ χ
  h ↦ congr(⟨$((cancel_epi (isoMk e).1).1 (by ext; exact affinePt_injective congr($h _)))⟩)
lemma multihomIdeal_eq_top_iff {a c q} : multihomIdeal (e.symm a) ⊥ (algebraMap A c.1)
  (unimodularRow <| q ·) = ⊤ ↔ q ∈ range ((testUnitLocus a).ι ≫ affineToLines e) c := by
  obtain ⟨ψ, rfl⟩ | h := em (q ∈ range (affineToLines e) c)
  erw [← (ψ.1.hom.comp e.toAlgHom).comp_algebraMap, ← map_multihomIdeal _ _ (r := (.X ·, 1)) fun _ ↦
    .trans ?_ (@exists_unit_smul_unimodularRow (.of _) _).choose_spec, range_comp,
    (injective_of_mono _).mem_set_image] <;>
    simp [multihomIdeal, ← MvPolynomial.eval₂_eq', testUnitLocus]
  exact ψ.1.hom.map_one
  use fun k ↦ h.elim ?_, by aesop
  choose x r using ((IsUnit.dvd (by simp_all [multihomIdeal])).imp <| affinePt_eq_map (𝟙 _) <| q ·)
  use ⟨ofHom (.comp (MvPolynomial.aeval x) e.symm)⟩, by simp [affineToLines, testSpec.asAlgHom, *]
variable [InvertsPrime A ℓ] (D : ComparedTheory g)
abbrev offClosedFibre Y := (@IdealFamily.ofMaximalIdeal A _ _).topLocus.preimage (toUnit Y)
namespace ComparedTheory
lemma isGood_iff_of_locally_bijective (u : E ⟶ Y) (s : IsLocallyEverything (ringOf (𝟭 _)) (.range
  u ⊔ U)) (i : IsLocallyEverything (ringOf (𝟭 _)) (Y := fibreProd u u) ⟨fun _ x ↦ relFreeAb.mk _
  x.1.1 = relFreeAb.mk _ x.1.2, fun f _ ↦ congrArg ((relFreeAb (U.preimage u)).map f)⟩ := by
  exact fun _ ⟨(a, b), e⟩ m _ ↦ ⟨1, m.one_notMem, by cases (by apply_rules [Subtype.ext] : a = b)
    <;> tauto⟩) : D.IsGood (relFreeAb (U.preimage u)) ↔ D.IsGood (relFreeAb U) :=
  D.isGood_iff_of_isCohomEquiv (map u le_rfl) fun g z ↦
  LocalIso.isCohomEquiv ⟨fun c ↦ Quot.ind (mem_of_map_eq_zero u (π _) _ (fun x y e ↦ (z (i.whisker
  g)).of_preimage_le (pointMap ⟨(_, _), e⟩) fun _ _ ↦ sub_eq_zero.2) (by simp_all [mk_eq_zero])),
  fun c ↦ mem_of_mk_mem (U := .whisker ..) (.comap _ (locallyZero ..)) fun y ↦ (z
  (s.whisker g)).of_preimage_le (pointMap y) fun _ _ ↦ (QuotientAddGroup.eq_zero_iff _).2 ∘ Or.rec
  (.imp' (relFreeAb.mk _) fun _ ↦ congrArg (relFreeAb.mk U)) (⟨0, mk_eq_zero · |>.symm⟩)⟩
def mulClassOp {N N' K P : AbFunctor (TestOver A)} [HasFlatValues N] (ξ :
  TotalH P (tateModule (𝟭 _))) (p : N' ⟶ abTensor N P) (π : N ⟶ K) : NaturalOp 0 K N' :=
  ⟨fun t ↦ (pullbackAlong (t.g.whiskerLeft p)).comp ((t.Θ.mulClass (.map (restrictAlong _) ξ)).comp
  (pullbackAlong (t.g.whiskerLeft π))), by
  intros; erw [mapThenComp_comp map_homClass, TorsionCoeff.mulClass_naturality (S := _ ⋙ N) (P :=
    _ ⋙ P), map_restrictAlong_restrictAlong _ _ ξ, map_comp_assoc, map_homClass]; rfl⟩
lemma isGood_of_prod_projLine : D.IsGood (relFreeAb (V.preimage (fst ..) ⊔ (affineChart.whisker
  (ringOf (𝟭 _))).preimage (snd ..))) → D.IsGood (relFreeAb V) := (((TotalH.exact_triangle
  (shortExact _).2 _).1 _).1 (comp_etaClass_eq_zero_of_isUnit (affineChart.whisker _).ι fun _ ↦
  (·.2))).elim fun ξ e ↦ D.isGood_of_retract ![mulClassOp ξ (relFreeAb.prod ..) _] ![.integrate
  ⟨fun t ↦ pullbackAlong (map (U := .whisker (_ ⊔ _) _) (U' := .whisker ..)
  (CartesianMonoidalCategory.lift (𝟙 _) (toUnit _ ≫ sectionMap (projLinePow.component t.points 0)))
  (by tauto)), by intros; apply mapThenComp_comp map_homClass⟩] fun t x ↦ (Fin.sum_univ_one _).trans
  (.trans (congrArg t.line_formula.integrate ((congrArg _ map_homClass_comp).trans (by
  conv_rhs => erw [map_zero, add_zero, ← TorsionCoeff.sliceEquiv_mulClass,
    ← map_restrictAlong_etaClass (g := 𝟭 _), ← e, map_homClass_comp, map_comp_assoc, map_homClass]
  exact (comp_assoc_of_sq (by simpa [← homClass_comp] using congrArg _ (hom_ext (U := .whisker ..)))
    _).trans (congrArg _ map_homClass_comp).symm))) (t.line_formula.integrate_mul_cupClass _ 0))
variable (L : D.IsGood (relFreeAb IdealFamily.ofMaximalIdeal.topLocus)) [Algebra A R] (P :
  StandardEtalePair R)
open AdjoinRoot Ideal.Quotient testSpec Finsupp
def rootPairs : Subfunctor ((testUnitLocus (A := A) (AdjoinRoot.mk P.f P.g)).toFunctor ⊗
  (testUnitLocus P.g).toFunctor) := ⟨fun _ (w, ψ) ↦ Associated (asAlgHom ψ P.f)
  (asAlgHom ψ.1 X - asAlgHom w.1 (root _)) ∧ ∀ r, asAlgHom w.1 (.of _ r) = asAlgHom ψ
  (C r), fun f _ ↦ .imp (by simpa using! ·.map f.1.1) (congr(f.1 $(· ·)))⟩
lemma exists_notMem_of_rootPairs {P} {c : TestOver A} {t m ε} (w : _ →ₐ[A] _) (ψ :
  _ →ₐ[A] c.1) [IsPrime m] (n : IsUnit (w (.mk _ P.g)) ∨ IsUnit (ψ P.g)) {S : ∀ d, (c ⟶ d) → _} (o :
  ε ∉ m) (k : t ∈ m) (s : ∀ d f h i, IsUnit (f.1.hom ε) → (⟨⟨ofHom w ≫ f.1⟩, h⟩,
  ⟨⟨ofHom ψ ≫ f.1⟩, i⟩) ∈ rootPairs P d → S d f) (j : ψ X = w (root
  _) + t ∧ ∀ r : R, w r = ψ (C r) := by simp_all) : ∃ a ∉ m, ∀ d f, IsUnit (f.1.hom a) → S d f := by
  have T p : ∃ r, ψ p = w (.mk _ p) + r * t ∧ r - ψ p.derivative ∈ m := p.recOnHorner ⟨0, by simp⟩
    (by simp; grind) fun p _ ↦ .imp' (· * w (root _) + ψ p) (by simp_all [← eq_zero_iff_mem]; grind)
  obtain ⟨⟨r⟩, ⟨⟩, ⟨_, _, _, e⟩⟩ := T P.f, T P.g, P.4, n.imp m.notMem_of_isUnit m.notMem_of_isUnit
  replace e := congr(Ideal.Quotient.mk m (ψ $e.symm))
  use w (.mk _ P.g) * ψ P.g * ε * r, fun _ ↦ by simp_all [← eq_zero_iff_mem]
  simpa using! (s · · · · · ∘ fun _ ↦ by
    constructor <;> simp [asAlgHom, *, associated_unit_mul_left])
include L
lemma isGood_principal_open a :
  D.IsGood (relFreeAb (.range ((testUnitLocus a).ι ≫ affineToLines e) ⊔ offClosedFibre _)) := by
  let I J : IdealFamily (elementsProj (projLinePow _ ⊗ reprBy (.of A))) :=
    ⟨fun x ↦ multihomIdeal (e.symm a) J x.2.2.1.1 (unimodularRow ∘ x.2.1),
    (·.2 ▸ map_multihomIdeal _ _ fun _ ↦ unimodularRow_map ..)⟩
  let Q := @IdealFamily.ofMaximalIdeal A _ _
  have γ := Theory.locallyConstant.onElements.isCohomDense_botLocus (I (maximalIdeal A)).pullToTests
  have δ := γ.mono (V := Q.botLocus.whisker (testOfPoint ..)) fun _ _ ↦ eq_bot_mono le_sup_right
  obtain ⟨ι, -, h⟩ :=
    exists_lerayHirsch_basis (Theory.onZeros ..) ((I _).isDetectedAtPoints_of_proper
    (isProperOver_projLinePow _) _ (IdealFamily.bijective_toZerosCoeff _ _) γ) δ ⟨0, 0⟩
  choose θ l using fun i : ι ↦ (δ.isCohomEquiv_of_bijective_on (α :=
    (restrictAlong _).map (Q.toZerosCoeff _)) (fun _ ↦ Q.bijective_toZerosCoeff _ _) _).2 i.1.2
  have t {E Y} (u : NatTrans E Y) (h : ∀ c k, _) := have b c k := (FreeAbelianGroup.equivOfEquiv
    (.ofBijective (u.1 c) (h c k))).bijective; (Comparison.bijective_iff_of_comm_sq
      (lerayHirsch_mapRange_comp θ (map_homClass (f := freeAb.map u))) (mapRange_bijective _ _
      ((Theory.locallyConstant.isCohomDense_botLocus Q).isCohomEquiv_of_bijective_on
      b).bijective_totalH) (δ.isCohomEquiv_of_bijective_on (b ·.1)).bijective_totalH).2
  choose _ q _ _ u k using (TestOver.exists_quotient · (Q.I _))
  have R {Y} := bijective_lerayHirsch_iff.2 ∘ @IsAffinelyCovered.devissage_bijective _ _ _ _ _ _ _
    TestOver.hasCoveringPoints Y _ _ _ lerayHirsch.devissage fun c ↦ bijective_lerayHirsch_iff.1 (t
    (reprMap _) (fun _ h ↦ ULift.map_bijective.2 (.of_existsUnique _ (u c _ · ((Q.2 _).trans h))))
    (.imp (·.of_comp_right (mapRange_surjective _ _ ((sectionEquiv ..).surjective.forall.2
    (Quot.ind (⟨sectionEquiv _ _ ·, by erw [of_comp_homClass, push_homReprEquiv_symm]; rfl⟩)))))
    .of_comp ((funext (lerayHirsch_naturality _ (comp.flip (.homClass _)) (r' := .id _)
    fun _ _ ↦ by erw [map_comp_assoc, map_homClass, homClass_comp_of, l]; rfl)).symm.subst
    (h _ ((Q.2 _).symm.trans (k c))))))
  have h : _ ⊔ offClosedFibre _ ≤ (I _).pullToTests.topPoints := fun c q ↦ Or.rec (eq_top_mono
    (sup_le_sup_left (by simp) _) ∘ (multihomIdeal_eq_top_iff e).2) (eq_top_mono le_sup_right)
  refine (D.isGood_iff_of_isCohomEquiv (relFreeAb.map (𝟙 _) h) fun g z ↦
    isCohomEquiv_of_le (U := .whisker ..) (U' := .whisker ..) (by tauto) (z fun c q m M ↦ ?_)).2
    (D.isGood_topPoints_of_surjective _ ((isClosedClass_lerayHirsch.2 _ (shortExact _).2 (t (homOfLe
    (le_sup_left.trans h)) (fun c k ↦ ⟨injective_of_mono _, (⟨⟨_, (multihomIdeal_eq_top_iff e).1 <|
    eq_top_mono (sup_le_sup_left (k.le.trans bot_le) _) ·.2⟩, rfl⟩)⟩)
    ((isClosedClass_lerayHirsch.iff_of_isIso (freeAb.map ((testUnitLocus.nonempty_iso_away a).some.1
    ≫ toRange _))).1 (R (isAffinelyCovered_reprBy _))))).1 (R isAffinelyCovered_projLinePow :)).2
    ((D.isGood_iff_of_isCohomEquiv _ (Q.isCohomEquiv_constToZeros · .locallyConstant rfl)).1
    ((D.isClosedClass_isGood.2 _ (shortExact_nsmul_abCoker (N := relFreeAb _)).2 L).1 L)))
  exact by_cases (fun k ↦ ((I ⊥).pullToTests.exists_notMem_eq_top (c := ⟨q.1⟩) fun h ↦
    M.ne_top (eq_top_mono (sup_le (le_sup_left.trans h) k) q.2)).imp fun _ ↦
    .imp_right fun H c f u ↦ .inl <| (multihomIdeal_eq_top_iff e).1 <| H (.mk (obj := g c) _)
    ⟨g.map f, rfl⟩ u) (by peel (Q.whisker g).exists_notMem_eq_top ·; tauto)
lemma isGood_standard_etale (e : MvPolynomial (Fin d) A ≃ₐ[A] R[X]) :
  D.IsGood (relFreeAb (offClosedFibre (testUnitLocus (AdjoinRoot.mk P.f P.g)).toFunctor)) := by
  let v : (rootPairs P).toFunctor ⟶ _ ⊗ projLineAlong (𝟭 (TestOver A)) :=
    ⟨fun c ↦ ↾fun ⟨(w, ψ), _⟩ ↦ (w, affinePt (asAlgHom ψ.1 X - asAlgHom w.1 (root _))),
    fun _ _ f ↦ congr(↾fun _ ↦ (_, $(by erw [map_affinePt, map_sub]; rfl)))⟩
  have n c : (⇑(v c)).Injective := fun ⟨⟨_, ⟨_⟩, _⟩, _, j⟩ ⟨_, _, i⟩ e ↦ by
    cases congr($e.1); congr; simp; ext; simp [j, ← i]
    simpa [j, ← i] using affinePt_injective congr($e.2)
  refine D.isGood_of_prod_projLine (Iff.mp (D.isGood_iff_of_locally_bijective v fun c ⟨w, (q :
    projLine (.of c.1))⟩ m M ↦ by_cases (fun h : (unimodularRow
    q).1 ∈ m ↦ (exists_idempotent_dvd_of_notMem c.2.2 M (g := (unimodularRow q).2) (fun _ ↦ by
    simp_all [unimodularRow, ← eq_zero_iff_mem])).elim fun ε ⟨n, i, z, l⟩ ↦
    exists_notMem_of_rootPairs _ (aevalTower ((asAlgHom w.1).comp (ofAlgHom ..)) (asAlgHom w.1
    (root _) + z * (unimodularRow q).1)) (.inl w.2) n (m.mul_mem_left z h) fun _ f _ _ u k ↦ .inl
    ⟨⟨_, k⟩, congrArg _ (affinePt_eq_map _ _ _ (by
    simpa [mul_assoc, asAlgHom, l] using! congr($(u.mul_eq_left.1 (i.map
    _)) * _).symm))⟩) (⟨_, ·, fun _ _ ↦ .inr ∘ .inr ∘ isUnit_unimodularRow_map _ _⟩)) (cast
    (by congr 2 with c ψ; exact .or .rfl (ψ.2.1.isUnit_iff.trans (.symm
    isUnit_unimodularRow_affinePt_iff))) ((D.isGood_iff_of_locally_bijective (U :=
    (offClosedFibre _ ⊔ testUnitLocus P.f).preimage (ι _)) ((rootPairs P).ι ≫ snd ..) (fun c ψ m M ↦
    by_cases (fun k ↦ (c.2.exists_root_map_eq (P.monic_f.map _) (by erw [eval₂_map, ← hom_eval₂,
    ← hom_eval₂, eval₂_C_X, eq_zero_iff_mem.2 k])).elim fun y e ↦ exists_notMem_of_rootPairs
    (liftAlgHom _ ((asAlgHom ψ.1).comp CAlgHom) y ((eval₂_eq_eval_map _).trans e.1)) _ (.inr ψ.2)
    m.one_notMem (Ideal.Quotient.eq.1 e.2.symm) fun _ _ _ _ _ k ↦ .inl ⟨⟨_, k⟩, rfl⟩)
    (⟨_, ·, by tauto⟩)) fun c ⟨⟨⟨(w, ψ), a, j⟩, (χ, _), b, i⟩, rfl⟩ m M ↦ by_cases (fun n ↦
    exists_notMem_of_rootPairs _ ((asAlgHom w.1).comp (.restrictScalars A (mkₐ _))) (.inl χ.2)
    m.one_notMem (m.mem_of_dvd (b.dvd.sub a.dvd) n) fun _ _ _ _ _ k ↦ congr(relFreeAb.mk _ ⟨(⟨⟨ofHom
    $(by ext; exacts [(k.2 _).symm, by simpa [asAlgHom] using! k.1.dvd])⟩, _⟩, _), _⟩)) (⟨_, ·,
    fun _ _ h ↦ .trans (relFreeAb.mk_eq_zero (.inr h)) (.symm (relFreeAb.mk_eq_zero (.inr h)))⟩)).2
    (Eq.mpr ?_ (D.isGood_of_shortExact (shortExact_triple ((testUnitLocus P.g).ι ≫ affineToLines e)
    _).2 (D.isGood_principal_open e L (P.g * P.f)) (cast ?_ (D.isGood_principal_open e L P.g)))))))
    <;> congr 2 with _ <;> simp [range_comp, (injective_of_mono _).eq_iff, testUnitLocus] <;> grind
end ComparedTheory
end
open MvPolynomial CategoryTheory Ideal Function MonoidalCategory CartesianMonoidalCategory
lemma CutsOutLocus.IsNoetherNormalization.pullback_injective {p k ι F} [Field k] [EmbeddedInQpBar p
  k] [Field F] {R} [Algebra R.1 k] [Finite ι] [Algebra k F] {g d n Y Λ} {L : LineBundle _ ι}
  [Fact (L.IsProjEmbedding Y.hom)] {ξ : PointsIn Y (.of k F)} (hξ : IsUnimodCoords L ξ g) (h :
  IsNoetherNormalization (k := k) Λ g) {Γ : Subfunctor (algPointsOf k R Y ⊗ projSpace k d)} {O :
  Subfunctor _} (E : ∀ {A x v h}, IsHomogSolution k g v → IsUnimodCoords L x v → ∃ a,
  ⟨(x, projSpace.mk (evalForms Λ v) h), a⟩ ∈ O A) :
  Injective (H.map genericCoeff (genericOver.whiskerLeft (freeAb.map (O.ι ≫ Γ.ι ≫ snd ..))) n) := by
  choose G B _ f b N i₁ i₂ M using h.exists_galois_closure
  let W := genericOver ⋙ .mk (fun A ↦ {x : (G → _) × (B ⟶ A) // (∀ σ,
    IsUnimodCoords L (x.1 σ) (x.2 ∘ b σ)) ∧ span (.range (x.2 ∘ f ∘ X)) = ⊤}) fun φ ↦ ↾fun x ↦
    ⟨(_, _ ≫ φ), (x.2.1 · |>.comp φ), unimodular.2 φ (a := ⟨_⟩) x.2.2⟩
  let t σ : W ⟶ genericOver ⋙ O.toFunctor := .mk fun _ ↦ ↾fun x ↦ ⟨_, show ∃ a, ⟨(x.1.1 σ,
    projSpace.mk _ x.2.2), a⟩ ∈ _ by convert E ((N _).1.map _) (x.2.1 σ) <;> simp [*, x.2].2⟩
  let π := genericOver.whiskerLeft (O.ι ≫ Γ.ι ≫ snd ..)
  choose _ _ _ _ _ _ e D using exists_transfer_map (by tauto : ∀ i, t i ≫ π = t 1 ≫ π)
  refine .of_comp ((funext (congr($(e ▸ map_nsmul (H.mapHom ..) ..) ·).symm.trans (H.map_comp
    ..))).subst (((HasUniqueDiv.of_isTorsionFree k _).1 (by simp)).comp (D _ ?_ ?_ n).1))
  all_goals
    refine hasZariskiDescent_genericOver (𝟭 _) (hasPartitions_periodAlg _
      exists_periodAlg_iso_genericAlg.choose) fun c x (m : Ideal (genericOver c)) hm ↦ ?_
    have I : IsTest (genericOver c) := c.isTest.localization
    choose _ _ _ _ _ O i _ using I.exists_valuationSubring_atPrime m
    algebraize [(O.subtype.comp i.2).comp (algebraMap k _)]
    let κ : _ →ₐ[k] _ := ⟨O.subtype.comp i.2, fun _ ↦ rfl⟩
    have P {σ} [Finite σ] {r s : σ → _} (h : ∀ i, κ (r i) = κ (s i)) := (IsLocalizedModule.pi
      m.primeCompl fun _ ↦ Algebra.linearMap ..).3 (funext (Subtype.ext <| h ·))
  · obtain ⟨⟨w⟩, hw⟩ := x
    obtain ⟨⟨_, π, S, s, hs⟩, φ, E⟩ := RingHom.FinitePresentation.of_finiteType.1 i₁.finiteType,
      exists_algHom_comp_eq_of_integral f (κ.comp (aeval w)) i₁.to_isIntegral
      (comap_bot_le_of_injective _ i₂)
    algebraize [f.1]
    rw [aeval_unique π] at *
    choose r H using fun i ↦ I.mem_range_of_isIntegralElem (.of_comp
      (congr(($E).IsIntegralElem _).mp ((i₁.to_isIntegral _).map _)))
    obtain ⟨⟨g, n⟩, e⟩ := @P s _ _ 0 fun x ↦ ((hom_eval₂ ..).trans (eval₂Hom_congr congr($E.symm.1)
      (funext H) rfl)).trans ((hom_eval₂ ..).symm.trans (congr(φ $(hs.le (subset_span x.2))).trans
      (by simp)))
    let H {A : CommAlg k} (ψ : _ →ₐ[k] A) (h : IsUnit (ψ g)) : {v : B ⟶ A // v ∘ f ∘ X = ψ ∘ w} :=
      ⟨_, by
      ext; simpa using! (aevalTower f _).liftOfSurjective_apply S (ψ.comp (aevalTower (aeval w) r))
       (hs ▸ span_le.2 (by simpa [h.mul_right_eq_zero, funext_iff] using! congr(ψ ∘ $e))) (C (X _))⟩
    let v := @H (.of k m.ResidueField) (IsScalarTower.toAlgHom ..) (by simpa)
    choose i hi using fun σ ↦ ne_iff.1 fun H : v.1 ∘ b σ = 0 ↦ hm.ne_top (eq_top_mono (span_le.2 (by
      simpa [funext_iff, ← H, N, v.2] using evalForms_smul Λ (u := v.1 0) (v := 0))) hw)
    choose _ _ _ _ _ _ _ S using (hξ.exists_universal_chart ((N _).1.map _) <| hi ·)
    refine ⟨_, mul_mem n (prod_mem (t := ⊤) fun σ _ ↦
      hi σ ∘ algebraMap_residueField_eq_zero.2), fun _ φ h ↦ ?_⟩
    simp at h; let v := H _ h.1
    use ⟨(_, v), (S · ((N _).1.map v.1.1) (h.2 _)),
      v.2.substr (unimodular.2 _ hw)⟩, congr(projSpace.mk $(v.2) _)
  choose u e using projSpace.mk_eq_mk_iff_exists_unit.1 (x.2 0 1)
  choose τ q using M (κ.comp _) (κ.comp _) _ (by simpa [funext_iff, u.smul_def] using congr(κ ∘ $e))
  obtain ⟨⟨g, n⟩, e⟩ := P fun l : G × ι ↦ congr($(q l.1) l.2).trans (map_mul ..).symm
  use g, n, fun _ f h ↦ ⟨.mulLeft τ, fun ρ ↦ congr(⟨⟨($(IsUnimodCoords.ext ((funext fun l ↦
    h.mul_left_cancel (by simpa using! congr(genericOver.map f ($e (ρ, l))))).subst (((x.1 1).2.1
    ρ).comp _)) (((x.1 0).2.1 _).map_unit_smul _ (u.map _))), $(((cech ..).map f x).2 ..)), _⟩, _⟩)⟩
