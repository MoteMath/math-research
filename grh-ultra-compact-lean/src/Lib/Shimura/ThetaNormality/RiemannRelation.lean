import Lib.Shimura.ThetaNormality.NormalGeneration
import Lib.Shimura.Uniformisation.RiemannFormAdelic
section
section
open CategoryTheory AlgebraicGeometry Limits pullback Set Scheme Spec Pullback Over PointFn Filter
variable {S} [IsReduced S] {A B : Over S} {V W J} [Finite J] {ξ : J → (_ ⟶ S)} {η : W → (Spec ⟨ℂ⟩ ⟶ S)} [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
omit [IsReduced S] in
lemma isSeparatingFamily_stalk {A z x} [IsReduced A] (d : @IsDenseFamily W A x) (hx : (range (x · ≫ z)).Finite) s : IsSeparatingFamily fun n : Σ' w ψ, map ψ ≫ S.fromSpecStalk s = x w ≫ z ↦ lift _ _
  n.2.2.symm := ⟨@isReduced_of_isReduced_stalk _ (⟨(fst z _).stalkMap_surjective · |>.forall.2 (by simp [IsNilpotent.map_iff, stalkMap_injective_of_flat])⟩), (fst z _).isEmbedding.dense_iff.2 fun y ↦ (((mem_closure_iff_frequently.1 (d _)).and_eventually (z.continuous.tendsto _ (range_fromSpecStalk.le ((range_fst ..).le ⟨y, rfl⟩) (hx.eventually_all.2 fun p _ ↦ eventually_imp_distrib_right.2 (specializes_iff_mem_closure (x := p _).2 ·.mem_closure))))).mono fun | _, ⟨⟨w, rfl⟩, b⟩ => ⟨_, ⟨⟨w, S.presheaf.stalkSpecializes (b _ ⟨w, rfl⟩ rfl) ≫ _, by
  simpa [-Hom.comp_base] using Spec_stalkClosedPointTo_fromSpecStalk _⟩, rfl⟩, by
  erw [← Hom.comp_apply, lift_fst]⟩).mem_closure⟩
lemma stalk_eq_zero_of_dense (hξ : IsDenseFamily ξ) {x} a (h : ∀ n : Σ' i ψ, map ψ ≫ S.fromSpecStalk x = ξ i, n.2.1 a = 0) : a = 0 := by simpa using ((isSeparatingFamily_stalk
  hξ (toFinite _) x).pointFn_ext (f := fun _ y ↦ preimage (y ≫ snd ..) a) (by simp [IsRegularOn])
  (isRegularOn_ofSection 0) (by simpa [lift_snd]) _ (inv (snd (𝟙 _) _)) landsIn_top)
open MonoidalCategory IsSchemeTheoreticallyDominant LocallyOfFiniteType CartesianMonoidalCategory
lemma IsSeparatingFamily.prod [IsLocallyNoetherian S] [Flat A.hom] [Flat B.hom] {y : ∀ w, .mk (η w) ⟶ B} {e : ∀ _, V → (_ ⟶ A)} (k : IsSeparatingFamily (y · |>.1)) (hξ : IsDenseFamily ξ) (r : IsReduced A.left) (h : ∀ w, IsSeparatingFamily fun v ↦ lift _ (𝟙 _) (e w v).w) : IsSeparatingFamily fun z : W × V ↦ (lift (e _ z.2) (y z.1)).1 := by
  let j := A.hom.smoothLocus.ι
  obtain _ := k.1, isLocallyNoetherian A.hom, isLocallyNoetherian B.hom, (j ≫ A.hom).smoothLocus_eq_top_iff.1 (by simp [j, ← j.preimage_smoothLocus_eq]), @of_isDominant
    _ _ j ⟨((dense_iff_closure_eq.2 genericPoints.closure).mono ((fun k ↦ @.of_perfectField _ _ k.toField (IsLocalHom.isField (stalkMap_injective_of_flat ..) k).toField (_) (@.ofCharZero _ (_) (not_forall.1 (one_ne_zero ∘ stalk_eq_zero_of_dense hξ 1)).choose.2.1.1.charZero) (stalkMap ..)) ∘ isField_stalk_of_closure_mem_irreducibleComponents _ ·)).denseRange_val⟩ _
  use isReduced ((pullbackRightPullbackFstIso _ _ j).inv ≫ snd ..), (k.2.preimage (Hom.isOpenMap _)).induction (fun t ⟨w, a⟩ ↦ (by simpa [range_map, whiskerLeft_left] using ⟨_, a⟩ : t ∈ range
    (A ◁ y w).1).choose_spec ▸ map_mem_closure (by fun_prop) ((h w).2 _) fun _ ⟨q, o⟩ ↦ o ▸
    ⟨⟨w, q⟩, congr($(lift_whiskerLeft (e ..) (𝟙 _) _).1 _).symm⟩) (by simp)
end
open CategoryTheory PointFn LineBundle AlgebraicGeometry Limits MvPolynomial Scheme RingHom Flat pullback Over
lemma exists_isLinearSystem {Z J Q X M} [Fintype J] [Fintype Q] {ξ : X → (_ ⟶ Z)} (w : _ → X → J → ℂ) (sep : IsSeparatingFamily ξ) (hM : IsLinearSystem M) (blk : ∀ a, M.IsHomogCoords (ξ a) (w false a)) (h : ∀ b j s, ∃ U, s ∈ U ∧ ∃ e : Q → _, ∃ c, IsRegularOn c U ∧ ∀ a, LandsIn (ξ a) U → c _ (ξ a) * ∑ q, w (!b) a (e q) = w b a j) : ∃ N, IsLinearSystem N ∧ (∀ a, N.IsHomogCoords (ξ a) (w true a)) ∧ N.picClass = M.picClass := by
  choose U _ e c _ _ using h true
  let σ j (k : J × (J → Z)) := c j (k.2 j) * ∑ q, M.transition k.1 (e j (k.2 j) q)
  refine ((M.mul (LineBundle.pi (LineBundle.mk (opens := U ·) 1 (by aesop)) ∅)).exists_picClass_eq_pull_hyperplane (𝟙 _) (s := σ) (fun j ↦ ⟨?_, fun i k _ _ ↦ (sep.pointFn_ext (g := _ * _) ?_ ?_ ?_ _ _ <| landsIn_inf.2 ⟨·, ·⟩)⟩) fun k _ _ _ n ↦ (h false k.1 _).elim fun _ ⟨v, e, c, _⟩ ↦ Function.mtr (by simp_all) (sep.pointFn_ext (g := 1) (f := c * ∑ q, σ (e q) k) ?_ ?_ ?_ _ _ (landsIn_inf.2 ⟨n, landsIn_iff_mem.2 v⟩))).elim fun f r ↦ ⟨_, ProjSpace.isLinearSystem_hyperplaneBundle.pull f, (ξ · |> exists_landsIn _ |>.elim (forall_imp ?_ <| r.2 · _ _)), ?_⟩ <;> simp_all [σ, IsRegularOn, IsLinearSystem, IsHomogCoords, ← mul_assoc, ← Finset.sum_mul, landsIn_iInf]; grind
attribute [local simp] lift_fst lift_snd specMap
def IsCutOutAt {J I K} [Field K] {S} r i σ (P : I → LineBundle S J) t (Z : Set (J → K)) := ∀ l : I → _, (∀ a, LandsIn t ((P a).opens (l a))) → ∀ c, IsCutOut r i σ c (fun a j ↦ (P a).transition (l a) j ⟨K⟩ t) (⨅ v ∈ {v ∈ Z | v c ≠ 0}, ker (eval (v · / v c)))
lemma exists_flat_closure {J W ι I κ S r i σ} [Finite J] [Finite ι] [IsReduced S] (j : ι → κ) {η : κ → _} (D : IsDenseFamily fun n ↦ η (j n)) {P : I → _} (B : ∀ a, (P a).IsLinearSystem) (H : 1 < r) (Y : IsCutDegree J i r σ) {θ : κ → W → J → ℂ} (hθ : ∀ n z, θ n z ≠ 0) (h : ∀ n, IsCutOutAt r i σ P (η n) (.range (θ n))) (cl : AllSpecializeTo S fun t ↦ ∃ Z, IsCutOutAt r i σ P t Z) : ∃ A N, ∃ e : ∀ n, W → (mk (η n) ⟶ A), IsProjEmbedding N A.hom ∧ Flat A.hom ∧ (∀ n z, IsHomogCoords N (e n z).left (θ n z)) ∧ (∀ n, IsSeparatingFamily fun v ↦ (lift _ (𝟙 _) (e n v).w :)) ∧ AllSpecializeTo S (fun t ↦ IsReduced (pullback A.hom t)) ∧ IsSeparatingFamily fun s : κ × W ↦ (e s.1 s.2).left := by
  choose χ ν using (Function.ne_iff.1 <| hθ · ·)
  choose p o g using fun w : ι × W ↦ ProjSpace.exists_isHomogCoords (η (j w.1)) (ν (j w.1) w.2).isUnit
  choose Z ε x₀ _ E b d using exists_reduced_closure p
  simp [← E, ← IsHomogCoords.pull_iff, -Prod.forall] at o g
  generalize ε ≫ _ = z, pull _ ε = N, (isProjEmbedding_projSpace).comp ε = M at *
  choose T u Q F V using fun {R b c} ↦ (M.of_isPullback (.of_hasPullback z b)).exists_affine_chart (R := R) c
  let O {R} b := (AffineOpenCover.ofIsOpenCover _ (cover _) (@T R b)).openCover
  have L {R b c A} [CommRing A] {φ : _ →+* A} : ker (@u R b c) ≤ RingHom.ker φ ↔ ∃ y, LandsIn y (N.opens c)
    ∧ y ≫ z = specMap (φ.comp C) ≫ b ∧ ∀ j, N.transition c j _ y = φ (X j) := ⟨fun h ↦ by
    obtain ⟨ψ, ⟨⟩⟩ := (u.liftOfSurjective Q).symm.surjective ⟨φ, h⟩
    exact landsIn_fromSpec T (specMap ψ) |> fun i ↦ ⟨_, landsIn_preimage.1 i, by simp [ext (f := ψ.comp _) (ofSection_map_fromSpec .. ▸ V i ·), condition]⟩, fun ⟨y, a, k, h⟩ f _ ↦
    by simpa [*, mem_ker.1, ← hom_eval₂] using (V (lift_fst _ _ k ▸ a :) f).symm⟩
  choose G k R using fun {k} [Field k] {t 𝔭} (h₀ : IsCutOutAt (K := k) r i σ P t 𝔭) ↦ show _ ∧ _ ∧ _ by
    have a := Spec_stalkClosedPointTo_fromSpecStalk t
    set c := fromSpecStalk ..
    choose _ q using (P · |>.exists_landsIn c)
    have v F ψ := funext₂ fun a j ↦ @((B a).1 _ j).1 _ F ψ _ (q a)
    have K m := map_eq_and_flat_of_isCutOut _ (ker (@u _ c m)) (stalk_eq_zero_of_dense D) H Y
      (v .. ▸ (a ▸ h₀) _ (q · |>.comp _) m) (fun n ↦ v .. ▸ (n.2.2 ▸ h _) _ (q · |>.comp _) m)
      fun f ↦ .trans ⟨by tauto, fun h ↦ (ofSection_map_fromSpec T _ (𝟙 _)).symm.trans
      (((isSeparatingFamily_stalk d ((Set.finite_range (η ∘ j)).subset (by simp_all)) _).pointFn_ext (isRegularOn_ofSection _) (isRegularOn_ofSection 0) h _ _ (landsIn_fromSpec T _)).trans (by simp))⟩ (by simp +contextual [*, g .., division_def, PSigma.forall, @forall_comm W])
    have e m := (K m).1.trans (eq_of_forall_ge_iff (b := ker (@u _ t m)) (·.mk_ker ▸ by
      simp [↓Ideal.map_le_iff_le_comap, ↓comap_ker, ↓L, comp_assoc, a]))
    use fun y ↦ (comp_iff_of_bijective_left ⟨stalkMap_injective_of_flat .., Hom.stalkMap_surjective _ y⟩).1 (Hom.stalkMap_comp .. ▸ @stalkMap _ _ _ (condition.symm.subst (.comp (hf := HasRingHomProperty.instIsZariskiLocalAtSource.of_openCover (O c) fun m ↦ F ▸ SpecMap_iff.2 (respectsIso.1 _ (quotientKerEquivOfSurjective Q) (flat_algebraMap_iff.2 (K m).2))) ..)) y), e, @IsReduced.of_openCover _ (O t) fun c ↦ (affine_isReduced_iff _).2
      ((ker_isRadical_iff_reduced_of_surjective Q).1 (e c ▸ fun _ h ↦ h.elim (by simp_all)))
  choose x q using fun n v ↦ ((L.1 ((k (h n) _).ge.trans (iInf₂_le _ ⟨⟨v, rfl⟩, ν n v⟩))).elim fun y ⟨b, e, E⟩ ↦ ⟨homMk y (by simp [e, MvPolynomial.eval]), by grind [M.1.2 b, IsHomogCoords, eval_X, homMk_left]⟩ : ∃ x : mk (η n) ⟶ mk z, N.IsHomogCoords x.1 (θ n v))
  exact ⟨_, N, x, M, .of_stalkMap _ fun x ↦ (cl (z x)).elim fun _ ⟨_, _, _, s, _, h⟩ ↦ ((Pullback.range_fst ..).ge (range_fromSpecStalk.ge s)).choose_spec ▸ G h _, q, fun n ↦ ⟨R (h n), fun y ↦ by_contra fun H ↦ have ⟨c, a⟩ := TopologicalSpace.IsOpenCover.exists_mem (cover _) y
    have ⟨f, F, Y⟩ := Q.exists.1 (T.exists_basicOpen_le (V := ⟨_, isClosed_closure.1⟩) ⟨y, H⟩ a)
    by simpa using ((k (h n) c).le (by simpa using fun v _ ↦ by_contra fun _ ↦ F (landsIn_iff_mem.1
      (by rw [landsIn_basicOpen]; simpa [q .., *]; simp [q .., *])) (subset_closure ⟨v, rfl⟩)) ▸
      Y :)⟩, by peel 6 cl; tauto, b,
    d.mono (by simp [fun w ↦ M.eq_of_isHomogCoords ((x ..).w ▸ o w) (g w) (q _ _)])⟩
end
noncomputable section
open CategoryTheory Fint Pi ComplexOrder
instance {X S s A} [a : HasProjEmbedding A.hom] [b : @HasProjEmbedding X S s] : HasProjEmbedding ((Over.map s).obj A).hom := a.rec fun a ↦ b.rec (⟨a.mul ·⟩)
lemma HasProjEmbedding.pi {S ι W} [Finite.{1} ι] {A : ι → Over S} (i : W ⟶ ∏ᶜ A)
    [AlgebraicGeometry.IsClosedImmersion i.left] [h : ∀ i, HasProjEmbedding (A i).hom] :
  HasProjEmbedding W.hom := by
  choose _ _ _ h using ((hasProjEmbedding_iff _).1 <| h ·)
  exact ⟨i.w ▸ (LineBundle.isProjEmbedding_pi _ h (Limits.Pi.hom_ext _ _)).comp _⟩
lemma PeriodMap.isSignedFrameFor {E} [Field E] [CMBase E] {V} [FinComplexSpace V] {D : PEL E}
    {g ℓ} (x : PeriodMap D g ℓ V) : IsSignedFrameFor g ℓ x.β := ⟨x.4, fun v ↦ by
  have key a b := x.5 (Pi.single v ∘ b) ▸ x.7 _ (Pi.single v ∘ a)
  simp +contextual [polarisationForm, Fintype.sum_eq_single v, ← zero_def, ← smul_def, -smul_eq_mul, -mul_ite] at key
  suffices _ from .of_dotProduct_mulVec_pos this fun u _ ↦ ⟨by
    simpa [riemannForm_swap, *, D.xi_im_pos_and_re_eq_zero] using x.8.1 (x.Q (Pi.single v ∘ u)) (by
    simp_all [funext_iff]), (this.im_star_dotProduct_mulVec_self u).symm⟩
  exact .ext fun i j ↦ ext_inner_right ℝ fun c ↦ by simpa [-single_apply, ne_of_gt, D.xi_im_pos_and_re_eq_zero] using
    ((fun a b ↦ (key a b).symm.trans (.trans (by simpa [riemannForm_def, x.6] using (x.6 (Complex.I • _) (Complex.I • _))) (key b a))) (Pi.single j 1) (Pi.single i c))⟩
open AddSubgroup Submodule Complex Function NumberField AddChar Set thetaSpace IsAppellHumbert PEL
variable {E n} {v : Valuation ℂ NNReal} [Field E] [CMBase E] [Fintype.{0} n] (D : PEL E)
def PEL.rescaledBeta := Nat.card D.T • D.β - ↑(Nat.card D.T / 2)
lemma PEL.lagrangian_le_T : D.lagrangian ≤ D.T := torsionClass_induction (by grind [mem_T, mem_lagrangian, zero_mem])
def PEL.rTorsion := comap (@nsmulAddMonoidHom (_root_.AdelicTorsion E D.Index) _ D.r) ⊥
variable {D g ℓ y z V} [FinComplexSpace V] (x : PeriodMap D g ℓ V) (s t : D.T) {u S S'}
def ratLift g := (fun σ s ↦ σ s - σ 0) (surjInv (@frameTorsionClass_surjective E n _ _ _ g))
@[simp] lemma frameTorsionClass_ratLift s : frameTorsionClass g (ratLift g s) = s := by simp [ratLift, surjInv_eq]
def PeriodMap.intAction := x.isPeriodMap.complexMul.comp (cmEmbedding.comp (algebraMap (𝓞 E) E))
variable (D g ℓ V) in
structure ThetaTorus extends PeriodMap D g ℓ V where
  reflection : IsReflection ℓ
  adjoint c y z : B (toPeriodMap.intAction c y) z = B y (toPeriodMap.intAction (star c) z)
  exists_std_equiv : ∃ e : V ≃ₗ[ℂ] BallFibre E D.Index, ∀ a, e.1 ∘ₗ toPeriodMap.intAction a ∘ₗ
    e.symm.1 = .prodMap (.prodMap (Φ v₀ a.val • 1) (star (Φ v₀ a.val) • 1)) (.piMap (Φ ·.1 a • 1))
namespace PeriodMap
abbrev latticeOver S := classLattice g S x.Q
abbrev periodLattice := x.latticeOver ⊥
abbrev multiplier := canonicalMultiplier x.B (x.intAction D.rescaledBeta)
abbrev periodPoint y := x.Q (toRealVectors y)
def torsionLift s := x.periodPoint (ratLift g s)
attribute [local simp] torsionLift periodPoint canonicalMultiplier RealComplexForm.riemannPhase thetaShift_apply map_add_eq_mul map_neg_eq_inv ne_of_gt Nat.mul_add_div map_nsmul_eq_pow add_mul toRealVectors_injective frameTorsionClass_surjective
attribute [local simp ←] fourierChar_eq_one
attribute [instance] isPosRiemann
@[simp] lemma torsionLift_zero : x.torsionLift 0 = 0 := by simp [ratLift]
@[simp] lemma mem_latticeOver : x.periodPoint y ∈ x.latticeOver S ↔ frameTorsionClass g y ∈ S := mem_map_iff_mem (by simp)
lemma latticeOver_mono (h : S ≤ S') : x.latticeOver S ≤ x.latticeOver S' := image_mono (by tauto)
lemma dualLattice_inf_latticeOver_top (h : ∀ y, torsionClass y ∈ S' ↔ ∀ w, torsionClass w ∈ S → ψf E (xiForm D.ξ y w) = 1) : x.B.dualLattice (L := x.latticeOver S) ⊓ x.latticeOver ⊤ = x.latticeOver S' := ext (by
  have {y} := isClosed_property (denseRange_frameCoords (g := g))
    (isClosed_imp (isOpen_preimage_torsionClass S) (isClosed_eq (f := ψf E ∘ xiForm D.ξ y) (by fun_prop [xiForm]) continuous_one))
  simp [RealComplexForm.dualLattice, Submodule.copy, mem_classLattice, frameTorsionClass, reindex_equiv x.Q, riemannForm_eq] at *
  grind [ψf_unit_eq_one, fourierChar_polarisationForm x.isFrameFor.choose_spec])
lemma intAction_mem_periodLattice bicharacter : ∀ l ∈ x.periodLattice, x.intAction bicharacter l ∈
  x.periodLattice := forall_mem_image.2 (by simp_all [intAction, ← toRealVectors_smul])
lemma nsmul_mem_latticeOver {m} (h : m ≠ 0) : m • u ∈ x.latticeOver S ↔ u ∈ x.latticeOver (S.comap (nsmulAddMonoidHom m)) := (MulAction.surjective₀ (a := (m : E)) (by simpa)).exists.trans (by
  simp_all [mem_classLattice, Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul ℝ, -nsmul_eq_mul])
lemma relIndex_latticeOver : (x.latticeOver S).toAddSubgroup.relIndex (x.latticeOver S').toAddSubgroup = S.relIndex S' := by erw [relIndex_map_map_of_injective, relIndex_comap, map_comap_eq_self_of_surjective] <;> simp
lemma card_nsmul_mem_periodLattice (h : u ∈ x.latticeOver D.T) : Nat.card D.T • u ∈
  x.periodLattice := D.T.relIndex_bot_left ▸ x.relIndex_latticeOver ▸ nsmul_relIndex_mem _ h
lemma intAction_rescaledBeta_mem_latticeOver (h : S ≤ D.T) (k : u ∈ x.latticeOver S) : x.intAction D.rescaledBeta u ∈ x.latticeOver S := by
  simpa [rescaledBeta] using
    _root_.sub_mem (x.latticeOver_mono bot_le (x.intAction_mem_periodLattice _ _ (x.card_nsmul_mem_periodLattice (x.latticeOver_mono h k)))) (by aesop)
lemma riemannForm_intAction_rescaledBeta : ∀ u w, x.B.riemannForm (x.intAction D.rescaledBeta u) w = x.B.riemannForm u w - x.B.riemannForm u (x.intAction D.rescaledBeta w) := by simp [reindex_equiv x.Q, intAction, riemannForm_eq, polarisationForm, mul_sub, ← map_star_complex, ← Pi.smul_def, -smul_eq_mul, sub_smul, ← coe_star_ringOfIntegers, -mul_re, (D.odd_card.rec (by simp_all [rescaledBeta, D.star_beta]; grind) : star D.rescaledBeta = 1 - D.rescaledBeta)]
lemma isAppellHumbert_of_le {L} (hL : L ≤ x.latticeOver D.lagrangian) : IsAppellHumbert (L := L) x.B
  x.multiplier := isAppellHumbert_canonicalMultiplier x.riemannForm_intAction_rescaledBeta x.re_symm
  fun _ k ↦ ((x.dualLattice_inf_latticeOver_top D.mem_lagrangian ▸ x.intAction_rescaledBeta_mem_latticeOver D.lagrangian_le_T (hL k)).1 · ∘ @hL _)
instance isAppellHumbert_periodLattice : IsAppellHumbert x.B x.multiplier := x.isAppellHumbert_of_le (x.latticeOver_mono bot_le)
instance isAppellHumbert_latticeOver_lagrangian : IsAppellHumbert (L := x.latticeOver D.lagrangian) x.B x.multiplier := x.isAppellHumbert_of_le le_rfl
lemma dualLattice_le_latticeOver_top : x.B.dualLattice (L := x.latticeOver S) ≤ x.latticeOver ⊤ := x.isAppellHumbert_periodLattice.exists_nsmul_mem_of_mem_dualLattice.rec fun _ ⟨a, b⟩ _ h ↦ x.latticeOver_mono le_top
  ((x.nsmul_mem_latticeOver a).1 (b _ (h · <| x.latticeOver_mono bot_le ·)))
lemma dualLattice_periodLattice : x.B.dualLattice = x.latticeOver D.T := inf_of_le_left x.dualLattice_le_latticeOver_top ▸ x.dualLattice_inf_latticeOver_top D.mem_T
instance discreteTopology_latticeOver_lagrangian : DiscreteTopology (x.latticeOver D.lagrangian) := isFullRankLattice_dualLattice.1.of_subset
  (x.dualLattice_periodLattice ▸ x.latticeOver_mono D.lagrangian_le_T)
lemma sub_mem_periodLattice_iff : x.periodPoint y - x.periodPoint z ∈ x.periodLattice ↔ frameTorsionClass g y = frameTorsionClass g z := by simp [← map_sub, ← sub_eq_zero]
lemma torsionLift_mem : x.torsionLift s ∈ x.latticeOver D.T := by simp
lemma riemannPhase_rescaledBeta_eq (h : u ∈ x.latticeOver D.T) (t : x.periodPoint y ∈ x.latticeOver D.T) (k : frameTorsionClass g z = frameTorsionClass g y) : x.B.riemannPhase
  (x.intAction D.rescaledBeta u) (x.periodPoint y) =
  x.B.riemannPhase (x.periodPoint z) ((.card D.T / 2) • u) := by
  obtain := x.dualLattice_periodLattice.ge t _
    (x.intAction_mem_periodLattice D.β _ (x.card_nsmul_mem_periodLattice h)),
    x.dualLattice_periodLattice.ge h _ (x.sub_mem_periodLattice_iff.2 k)
  simp_all [rescaledBeta, riemannForm_swap (x.Q _), inv_mul_eq_one, -nsmul_eq_mul]
def bicharacter (h : u ∈ x.latticeOver D.T) : AddChar D.T ℂ := ⟨(x.B.riemannPhase (x.intAction D.rescaledBeta u) <| x.torsionLift ·), by simp [ratLift], fun s t ↦ by simp [riemannPhase_rescaledBeta_eq (z := ratLift g s + ratLift g t), riemannPhase_rescaledBeta_eq _ h _ rfl, add_mem, h]⟩
lemma bicharacter_neg_eq_swap : x.bicharacter (x.torsionLift_mem s) (-t) = x.bicharacter (x.torsionLift_mem t) s := by simp [bicharacter, x.riemannPhase_rescaledBeta_eq _ _ rfl, riemannForm_swap (x.periodPoint (ratLift g t))]
lemma mem_lagrangian_of_bicharacter_sq (h : ∀ l : D.lagrangian.addSubgroupOf D.T, x.bicharacter (x.torsionLift_mem s) l ^ 2 = 1) : ↑s ∈ D.lagrangian := frameTorsionClass_ratLift s.1 ▸
  x.mem_latticeOver.1 (x.dualLattice_inf_latticeOver_top D.mem_lagrangian ▸ ⟨fun l ⟨y, hy, e⟩ ↦ D.lagrangian_le_T (x := frameTorsionClass g y) hy |> fun k ↦ by
  obtain ⟨⟨⟩⟩ := D.odd_card, x.dualLattice_periodLattice.ge (by tauto) _
    (x.card_nsmul_mem_periodLattice (x.torsionLift_mem s)), h ⟨⟨_, k⟩, hy⟩
  simp_all [bicharacter, riemannPhase_rescaledBeta_eq (z := y), sq, @two_mul ℝ, riemannForm_swap l, Circle.ext_iff, -coe_fourierChar_eq_exp], by simp⟩)
def exists_thetaSpace_lagrangian_le_span := Classical.indefiniteDescription _ (finrank_eq_one_iff'.1 (by simpa [inf_of_le_left x.dualLattice_le_latticeOver_top ▸ x.dualLattice_inf_latticeOver_top D.mem_lagrangian] using
  x.isAppellHumbert_latticeOver_lagrangian.finrank_sq_eq_relIndex.2.1))
def thetaCoord := normalizedShift x.B (x.intAction D.rescaledBeta) (x.torsionLift t)
  x.exists_thetaSpace_lagrangian_le_span
@[simp] lemma thetaCoord_mem_thetaSpace : x.thetaCoord t ∈ x.B.thetaSpace x.multiplier := smul_mem _ _ (thetaShift_mem_of_dual (by simp [dualLattice_periodLattice]) (x.exists_thetaSpace_lagrangian_le_span.1.2.imp id (· · <| x.latticeOver_mono bot_le ·)))
lemma thetaCoord_mem_thetaSpace_lagrangian : x.thetaCoord t ∈ x.B.thetaSpace (L := x.latticeOver D.lagrangian) fun l ↦ x.multiplier l * x.B.riemannPhase l (x.torsionLift t) := smul_mem _ _ (by simp [↓thetaShift_mem])
lemma thetaCoord_ne_zero : x.thetaCoord t ≠ 0 := ne_of_apply_ne (x.B.thetaShift (-x.torsionLift t)) (by simp [thetaCoord, normalizedShift, x.isAppellHumbert_periodLattice.thetaShift_thetaShift, x.exists_thetaSpace_lagrangian_le_span.2])
lemma thetaCoord_eq_of_mem_lagrangian (h : ↑s ∈ D.lagrangian) : x.thetaCoord s = x.thetaCoord 0 := by simp [thetaCoord, mem_thetaSpace_iff_normalizedShift.1 x.exists_thetaSpace_lagrangian_le_span.1.2, h]
variable {s t}
lemma thetaCoord_eq_normalizedShift y (hy : frameTorsionClass g y = t) : x.thetaCoord t = normalizedShift x.B (x.intAction D.rescaledBeta) (x.periodPoint y)
  x.exists_thetaSpace_lagrangian_le_span := by
  have h := x.sub_mem_periodLattice_iff.2 (frameTorsionClass_ratLift (frameTorsionClass g y)).symm
  obtain := x.dualLattice_periodLattice.ge (x.torsionLift_mem t) _
    (x.intAction_rescaledBeta_mem_latticeOver bot_le h),
    (mem_thetaSpace_iff_normalizedShift.1 (x.thetaCoord_mem_thetaSpace t)).2 _ h
  simp_all [thetaCoord, x.isAppellHumbert_periodLattice.normalizedShift_normalizedShift x.riemannForm_intAction_rescaledBeta, riemannForm_swap (x.Q _), -map_sub]
lemma thetaShift_thetaCoord (hy : frameTorsionClass g y = s) t : x.B.thetaShift (x.periodPoint y) (x.thetaCoord t) = (x.multiplier (x.periodPoint y) * x.bicharacter (x.mem_latticeOver.2 (hy ▸ s.2)) t) • x.thetaCoord (s + t) := by
  simpa [bicharacter, x.thetaCoord_eq_normalizedShift (y + ratLift g t), *, mul_smul, ← inv_smul_eq_iff₀] using! x.isAppellHumbert_periodLattice.normalizedShift_normalizedShift
    x.riemannForm_intAction_rescaledBeta
lemma exists_thetaCoord_sign_smul (m : ℤˣ) : ∃ ε, ∀ z t, x.thetaCoord t (m.1 • z) = ε * x.thetaCoord (m.1 • t) z := (Int.units_eq_one_or m).rec (⟨1, by simp [·]⟩) fun _ ↦ (x.exists_thetaSpace_lagrangian_le_span.2.2 ⟨_, x.exists_thetaSpace_lagrangian_le_span.1.2.imp (·.comp differentiable_fun_id.neg) (by simp_all [↓neg_add])⟩).imp (by
  simp_all [Subtype.ext_iff, funext_iff, ↓x.thetaCoord_eq_normalizedShift (-ratLift g _), thetaCoord, normalizedShift, add_comm, field])
attribute [irreducible] thetaCoord bicharacter
lemma valuation_multiplier_mul_bicharacter (h : u ∈ x.latticeOver D.T) : v (x.multiplier u * x.bicharacter h t) = 1 := by simp_all [bicharacter, two_mul, exp_add, valuation_eq_one_of_pow_eq_one _ (x.isAppellHumbert_periodLattice.exp_riemannForm_pow_eq_one (card_nsmul_mem_periodLattice ..) (card_nsmul_mem_periodLattice ..)), intAction_rescaledBeta_mem_latticeOver]
lemma hasGoodReduction_trivial : HasGoodReduction x.B x.multiplier 1 D.r := ⟨{finite_order := ⟨2 * 1 * 1, nofun, fun _ _ ↦ x.isAppellHumbert_periodLattice.exp_riemannForm_pow_eq_one (by simp [intAction_mem_periodLattice, *]) (by simpa)⟩}, by
  simp [x.isAppellHumbert_periodLattice.exists_nsmul_mem_of_mem_dualLattice], by
  simp [D.three_le_r.trans_lt'], Nat.le_of_lt D.three_le_r, fun _ _ _ _ ⟨_, a, _⟩ ⟨_, b, _⟩ ↦ by
  have (B : LatticeForm x.periodLattice) f hf (H : B.thetaNorm 1 f ≠ 1) := eq_zero_of_torsionPoints
    hf (by simpa [IsGreatest, LatticeForm.sizeAt, upperBounds, -map_mul, Valuation.one_apply_le_one] using H ∘ IsGreatest.csSup_eq)
  grind +splitImp [thetaNorm_zero, =_ sizeAt_mul, eq_zero_of_entire_mul_eq_zero a, a.mul b]⟩
lemma thetaNorm_thetaCoord i : x.B.thetaNorm v (x.thetaCoord i) = x.B.thetaNorm v (x.thetaCoord 0) := .trans (by simp [thetaShift_thetaCoord, thetaNorm_smul, valuation_multiplier_mul_bicharacter, -canonicalMultiplier, -map_zero_eq_one]) (x.hasGoodReduction_trivial.thetaNorm_thetaShift (x.dualLattice_periodLattice ▸ x.torsionLift_mem i))
lemma formSpan_eq_normBall (G : HasGoodReduction x.B x.multiplier v D.r) bicharacter j : _root_.formSpan _ x.thetaCoord (D.r ^ j) = (G.pow j).normBall (x.thetaCoord bicharacter ^ D.r ^ j) := G.normBall_pow_pow (x.thetaCoord_mem_thetaSpace bicharacter) inferInstance
  (x.thetaCoord_mem_thetaSpace_lagrangian bicharacter) (fun _ h ↦ x.latticeOver_mono D.torsion_mem_lagrangian ((x.nsmul_mem_latticeOver G.one_lt.ne_bot).1 h)) j ▸
  congrArg (· ^ _) (span_eq_of_le _ (by simp [G.mem_normBall, thetaNorm_thetaCoord]) fun _ h ↦ G.mem_of_mem_normBall (x.thetaCoord_mem_thetaSpace bicharacter) le_rfl G.isAppellHumbert (x.thetaCoord_mem_thetaSpace bicharacter) h.1 (x.dualLattice_periodLattice ▸ fun _ ⟨_, a, e⟩ ↦ e ▸ x.thetaShift_thetaCoord (s := ⟨_, a⟩) rfl bicharacter ▸ smul_mem _ (⟨_, (x.valuation_multiplier_mul_bicharacter _).le⟩ : v.integer) (by aesop)) h)
lemma thetaCoord_vector_ne_zero z : (x.thetaCoord · z) ≠ 0 := (x.isAppellHumbert_periodLattice.exists_apply_ne_zero z _ x.hasGoodReduction_trivial.4).rec fun _
  ⟨_, _⟩ h ↦ by
  obtain ⟨c, _, H, ⟨⟩⟩ := (x.hasGoodReduction_trivial.pow 1).exists_eq_smul_normBall
    (pow (x.thetaCoord_mem_thetaSpace 0) _) (by simp [thetaCoord_ne_zero]) (by simpa)
  have := (map_pow (mapHom (Pi.evalAlgHom _ _ z)) ..).le ⟨_,
    x.formSpan_eq_normBall x.hasGoodReduction_trivial .. ▸ H, rfl⟩
  simp_all [map_span, ← range_comp', bot_pow x.hasGoodReduction_trivial.4.ne_bot]
end PeriodMap
end
section
open Complex Finite LatticeForm Finset Fint Function Module MvPolynomial NNReal NumberField PeriodMap Submodule thetaSpace
variable {V E k K : Type} [FinComplexSpace V] {v} [Field E] [CMBase E] {D : PEL E} {g ℓ} (x : ThetaTorus D g ℓ V) [Fintype K] (a : K → 𝓞 E) {μ μ' : K → D.T} {w t} (p : K → 𝓞 E × 𝓞 E)
namespace ThetaTorus
attribute [-simp] map_eq_zero map_smul nsmul_eq_mul
noncomputable instance : Module (𝓞 E) D.T := module ⟨_, by
  rintro a ⟨y⟩ h; exact (D.mem_T _).2 fun z k ↦ by simpa [xiForm, ↓star_smul] using
    ((D.mem_T y).1 h (algebraMap E (𝔸f E) (star a) • z) (torsionClass.ker.smul_mem (star a) k))⟩
def IsRiemannTuple (D : PEL E) := ∑ l, star (p l).1 * (p l).1 = D.r ∧ ∑ l, star (p l).1 * (p l).2 = 0
def doubledCoeffs (k : K → 𝓞 E × _) := Sum.elim (0, k · |>.2) p
noncomputable def thetaProduct (μ : K → _) w z := ∏ k, x.thetaCoord (μ k) (x.intAction (p k).1 z + x.intAction (p k).2 w)
attribute [local simp] thetaShift_apply exp_add exp_neg Ideal.Quotient.eq_zero_iff_mem map_eval PeriodMap.torsionLift bicharacter thetaCoord_ne_zero periodPoint PeriodMap.sub_mem_periodLattice_iff adjoint thetaProduct Valuation.pos_iff canonicalMultiplier div_eq_inv_mul mul_pow thetaNorm_pow thetaRanks
lemma thetaShift_thetaProduct {p} (hp : IsRiemannTuple p D) (ht : ∑ k, star (p k).1 • μ k = t) {u y}
    (k : y ∈ x.latticeOver D.T) (h : ∀ k, x.B.thetaShift (x.intAction (p k).1 u) (x.thetaCoord (μ k)) = (x.multiplier (x.intAction (p k).1 u) * x.B.riemannPhase (x.intAction (p k).1 y) (x.torsionLift (μ k))) • x.thetaCoord (μ' k)) z : (D.r • x.B).thetaShift u (x.thetaProduct p μ w)
  z = x.multiplier u ^ D.r * x.B.riemannPhase y (x.torsionLift t) * x.thetaProduct p μ' w z := by
  obtain ⟨⟨⟩⟩ := x.dualLattice_periodLattice.ge k (∑ k, x.intAction _ (x.torsionLift _) - x.torsionLift t) (by simp [intAction, ← toRealVectors_smul, ← map_sum]; simp [← ht]; rfl), (congr(x.B u <| x.intAction $(hp.1) ·)), congr(x.B u (x.intAction $(hp.2) w)), congr(x.B.riemannForm (x.intAction (D.rescaledBeta * $(hp.1)) u) u)
  simp [← ofReal_inj, sub_eq_iff_eq_add', map_sub, riemannForm_def, mul_sum, ↓mul_left_comm D.rescaledBeta] at *
  simpa [*, ← exp_sum, add_right_comm, mul_add, ← zsmul_eq_mul', ← mul_sum, ← exp_nsmul, mul_left_comm D.r.cast, nsmul_eq_mul] using congr(∏ k, $(h k) (x.intAction (p k).1 z + x.intAction (p k).2 w))
lemma riemann_relation {p} (hp : IsRiemannTuple p D) (ht : ∑ k, star (p k).1 • μ k = t) {q} (hq : IsRiemannTuple q D) (h : ∑ k, star (q k).1 • μ' k = t) [Fintype D.T] z : Fintype.card D.T * x.thetaProduct q μ' w 0 * x.thetaProduct p μ w z = (D.rTorsion.relIndex D.T).sqrt * ∑ s, x.thetaProduct p (μ - (·.1 • s) ∘ p) w 0 * x.thetaProduct q (μ' + (·.1 • s) ∘ q) w z := by
  obtain ⟨m, r, _⟩ := x.latticeOver_mono (S := D.rTorsion) D.torsion_mem_lagrangian, x.hasGoodReduction_trivial.4.ne_bot, (x.thetaCoord_mem_thetaSpace · |>.1)
  obtain ⟨_, d⟩ := x.discreteTopology_latticeOver_lagrangian.of_subset m, ((dualLattice_nsmul_le r fun _ ↦ (x.nsmul_mem_latticeOver r).1).antisymm fun _ h _ ↦ by simpa using h _ ∘ (x.nsmul_mem_latticeOver r).2).trans x.dualLattice_periodLattice
  rw [← x.relIndex_latticeOver, ← (((x.isAppellHumbert_of_le m).nsmul _).shift _ _).sum_shift_mul_shift (hp := x.isPosRiemann.nsmul r) _ (⟨_, d.ge <| x.torsionLift_mem ·⟩) (d.le ·.2 |>.elim fun y ⟨h, e⟩ ↦ ⟨.addLeft ⟨_, h⟩, by simp [← e, ← map_add, ← map_sub]; simp⟩) ⟨_, ?_⟩ ⟨_, ?_⟩] <;> try exact ⟨by fun_prop [thetaProduct], fun l
    h z ↦ by erw [mul_right_comm, ← x.thetaShift_thetaProduct ‹_› ‹_› (x.latticeOver_mono
    D.lagrangian_le_T (m h)) fun k ↦ thetaShift_of_mem (x.thetaCoord_mem_thetaSpace_lagrangian _) (m (by grind [=_ nsmul_mem_latticeOver, PEL.rTorsion, intAction_mem_periodLattice, =_ map_nsmul]))]; simp [field]⟩
  congr with s; have d := congr($(x.riemannPhase_rescaledBeta_eq (x.torsionLift_mem s)
    (x.torsionLift_mem s) rfl) ^ D.r)
  have L y h p μ := (x.thetaShift_thetaProduct (p := p) (K := K) (w := w) (μ' := μ +
    (·.1 • ⟨frameTorsionClass g y, h⟩) ∘ p) · rfl (x.intAction_rescaledBeta_mem_latticeOver le_rfl (by tauto)) (u := x.Q _) fun k ↦ by simpa [intAction, smul_comm (cmEmbedding (p k).1.val),
    add_comm] using (x.thetaShift_thetaCoord (s := (p k).1 • ⟨_, h⟩) (map_smul ..) _))
  erw [← map_neg, ← map_neg, L] <;> simp [*, two_mul, add_mul, field, sub_eq_add_neg] at *
  simp [← smul_neg, sq_eq_one_iff.2 d]; ring!
lemma exists_peak (G : HasGoodReduction x.B x.multiplier v D.r) (hv : v (Nat.card D.T) = 1) s : ∃ u, ∀ w ∈ [u, -u, s - u], ∀ t, v (x.thetaCoord t 0) ≤ v (x.thetaCoord w 0) := by
  obtain ⟨T, ⟨o, ho⟩, ⟨η, H⟩, ⟨r, e⟩, u, hu⟩ := (sizes.of_mem_thetaSpace G.1 <| x.thetaCoord_mem_thetaSpace ·), exists_max (v <| x.thetaCoord · 0), x.exists_thetaCoord_sign_smul (-1), Nat.exists_eq_add_of_lt D.three_le_r, exists_max fun u ↦ v (x.thetaCoord (s - u) 0) ⊓ _
  obtain ⟨N, le⟩ := G.hasMultiplicativeNorm (φ := _ * _) (by simpa using! mul_shift_mem_sizes (T s) (T (D.r • o - s)) 0)
    ⟨G.nsmul r.succ_ne_zero, pow (x.thetaCoord_mem_thetaSpace 0) _⟩, (size_le_iSup <| T ·)
  simp [-Subtype.forall, sizeAt, field, thetaNorm_thetaCoord, G.hasMultiplicativeNorm (T _) (T _)] at le N hv H
  have A := not_lt.1 fun q ↦ q.not_ge ((le_of_mul_le_mul_right (congr(v (x.thetaCoord
    o 0) * $N).ge.trans (mul_iSup_le fun z ↦ ?_)) (by simp [G.thetaNorm_pos])).trans (hu u))
  · use u, List.forall_mem_cons.2 ⟨fun _ ↦ by grw [← neg_zero, H, H, map_mul, ho, map_mul, A, inf_le_right], by simp [(ho _).trans, A.trans]⟩
  have := congr(v $(x.riemann_relation (w := 0) (p := const _ (1, 0)) (μ' := const _ o) (μ :=
    Option.elim'
    (D.r • o - s) (Sum.elim ![s, 0] (0 : Fin r → _))) ?S ?_ ?S rfl z)).trans_le ((v.leSubmodule _).smul_mem (Nat.cast _) (sum_mem fun t ↦ by simp; grw [ho, ← min_mul_max _ (v _), hu, ho (s - t), ho (-t), le])) <;> simp [IsRiemannTuple, ↓sizeAt_pow, sizeAt, *, field, pow_add, q.pos] at *
  linarith
lemma isCutOutAt_reduction [Field k] {φ : v.valuationSubring →+* k} (hφ : Surjective φ) (G : HasGoodReduction x.B x.multiplier v D.r) {q p : _ → _} (hq : ∀ z, IsIntegralCoords (x.thetaCoord
  · z) (q z)) (hp : ∀ l : D.levelTorsion, IsIntegralCoords (x.thetaCoord · (x.torsionLift l)) (p l))
  {S t} {N : _ → LineBundle S _} (hx : ∀ l, (N l).IsHomogCoords t (φ <| p l ·)) :
  IsCutOutAt D.r D.i (thetaRanks D.T D.r) N t (.range (φ ∘ q ·)) := fun l hl c ↦ by
  obtain ⟨T, R, H, Y, U⟩ := pow (x.thetaCoord_mem_thetaSpace c), G.pow, @eval₂_mul_of_isHomogeneous, @isHomogeneous_X_pow, (x.formSpan_eq_normBall G c · ▸ (LinearMap.range_domRestrict ..).trans (map_homogeneousSubmodule_eq_formSpan ..))
  choose e _ E using (lt_iff_exists_add.1 <| @Nat.pow_lt_pow_succ _ · G.one_lt)
  have W j := ext fun _ ↦ mem_dualLattice_nsmul.trans
    (x.dualLattice_periodLattice ▸ x.nsmul_mem_latticeOver (pow_ne_zero j G.one_lt.ne_bot))
  have P j {I} {a p : I → _} k (h : ∀ b, IsIntegralCoords (x.thetaCoord · (a b)) (p b)) := (R j).thetaNorm_lt_iff_coords (T _) (by simp) (p := fun l ↦ (·.1.eval (p l))) (U j) k (h · |>.imp' _ fun s ⟨e, t, h⟩ ↦ ⟨fun f ↦ by simpa
    [eval_eq, aeval_def, eval₂_eq, e] using (H f.2 (algebraMap ..) s⁻¹ _), ⟨_, Y t _⟩, by simp [h]⟩)
  have Q j (f : homogeneousSubmodule ..) := P _ (⟨·.1, by simp⟩) hq ⟨_, E j ▸ f.2.mul (Y c _)⟩
  simp [*, G.hasMultiplicativeNorm (.of_mem_thetaSpace (f := aeval _ (Subtype.val _)) (R _).1 ((U _).le ⟨_, rfl⟩).1) ⟨G.nsmul _, _⟩, -Subtype.forall, add_smul, ↓thetaNorm_pow, pow_add, G.thetaNorm_pos (x.thetaCoord_mem_thetaSpace c) (x.thetaCoord_ne_zero c), LatticeForm.thetaNorm, ne_of_gt, or_iff_not_imp_right, ↓← v.mem_maximalIdeal_iff, ← IsLocalRing.ker_eq_maximalIdeal φ hφ] at P Q
  have L d : Surjective fun f : homogeneousSubmodule D.T _ d ↦ (⟨_, f.2.map φ⟩ : homogeneousSubmodule ..) | ⟨g, h⟩ => ⟨⟨_, sum_mem fun m a ↦ isHomogeneous_monomial (surjInv hφ (g.coeff m)) (h.degree_eq_sum_deg_support a).symm⟩, by simp [surjInv_eq]⟩
  use by simp +contextual, fun j ↦ ?_, fun _ a ↦ Subtype.forall'.2 ((L _).forall.2 fun f ↦ by
   simpa +contextual [Q, hx .., ((hx ..).1.1 (hl _)).ne_zero, H f.2, mul_comm (φ _)] using! P
    _ (W _ ▸ fun ⟨_, y, h, rfl⟩ ↦ ⟨⟨_, D.degree_spec.2 _ a _ h⟩, by simp⟩) hp f)
  erw [← (imageMod ..).span_eq, map_coe, Set.image_eq_range, ← (L _).range_comp, (R _).finrank_reduction_eq (T _) (by simp) (U _) hφ (y := ⟨⟨_, by simp⟩, by
    simp [Algebra.smul_def]; tauto⟩) fun f ↦ by simp +contextual [Q, H f.2], ← (finrank
    ..).sqrt_eq', (R _).finrank_sq_eq_relIndex (hp := (R _).isPosRiemann).2.1, W,
    relIndex_latticeOver]; simp
noncomputable def _root_.paddingTuple bicharacter := @Sum.elim Bool _ _ (fun _ ↦ (1, 0))
    (Sum.elim (cond · (bicharacter, 1) (1, -star bicharacter)) (a ·, 0))
end ThetaTorus
end
