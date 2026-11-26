import Lib.Cohomology.Etale.TestRings
import Lib.General.Algebra.CechDescent
import Lib.Cohomology.Etale.BijectiveComparisons
import Lib.Cohomology.Etale.ClosedClasses
import Lib.General.Algebra.TensorCohomology
section
open CategoryTheory Classical CommRingCat MvPolynomial Ideal.Quotient
variable (B) {W V J : Type} [CommRing B] [CommRing W] [CommRing V] (g : W →+* V)
namespace Envelope
def IsSolution (a : ℕ → V) x | 0 => IsIdempotentElem x ∧ a 0 ∣ x * a 1 ∧ a 1 ∣ (1 - x) * a 0
                             | 1 => ∀ n, a 0 ^ n ∣ a (n + 1) - x | n + 2 => ∑ k ∈ .range n, a k * x ^ k = 0
inductive SN
  | op (o : ℕ) (n : ℕ → ℕ) (P : ∀ k, MvPolynomial (Fin (n k)) B) (t : ∀ k, Fin (n k) → SN)
def SC := (⇑g).Injective ∧ ∀ o a, (∃ x, IsSolution (g ∘ a) x o) → ∃ x, IsSolution (g ∘ a) (g x) o
variable {B g}
lemma exists_isSolutionClosed φ : ∃ g : MvPolynomial (SN B) B →+* V, g.comp C = φ ∧ SC g.kerLift := ⟨eval₂Hom φ (·.rec fun o _ P _ v ↦ epsilon (IsSolution (P · |>.eval₂ φ (v _)) · o)), by simp, RingHom.kerLift_injective _, fun _ ↦ mk_surjective.comp_left.forall.2 fun a h ↦ by
  choose n t _ P e using (a · |>.exists_fin_rename)
  exact ⟨mk _ (X (.op ..)), by simpa [e, eval₂_rename, Function.comp_def] using epsilon_spec h⟩⟩
lemma SC.map_dvd_iff (h : SC g) {x y} : g x ∣ g y ↔ x ∣ y := ⟨by simpa [← h.1.eq_iff, dvd_def, IsSolution, Finset.sum_range, neg_add_eq_zero] using (h.2 4 ([-y].getD · x)), map_dvd g⟩
lemma SC.isTest (h : SC g) : IsTest V → IsTest W
  | ⟨a, c, _⟩ => ⟨⟨fun P m d ↦ by simpa [P.eval_eq_sum_range, ← h.1.eq_iff] using! (h.2 (_ + 3)
    _ (by simpa [P.eval₂_eq_sum_range] using! a.exists_eval₂_eq_zero g m d))⟩, fun x y ↦ by simpa [← h.map_dvd_iff, ← h.1.eq_iff, IsIdempotentElem] using! (h.2 0 ([x].getD · y) (c ..)), isReduced_of_injective g h.1⟩
lemma exists_functorial_test (R : J → _) : ∃ E, ∃ θ : 𝟭 CommRingCat ⟶ E, (∀ A, IsTest (E A)) ∧ ∀ o (A : TestRing) φ, ∃ ψ : _ ⟶ A.1, θ (R o) ≫ ψ = φ := let e {S} := Pi.evalRingHom fun x : Σ q : {q : Σ o, Ideal (MvPolynomial (SN (R o)) (R o)) // IsTest (_ ⧸ q.2)}, S ⟶ of (_ ⧸ q.1.2) ↦ _ ⧸ x.1.1.2
  ⟨.mk _ fun f ↦ ofHom (.pi (e ⟨_, f ≫ ·.2⟩)), .mk fun _ ↦ ofHom (.pi (·.2.1)), fun _ ↦ .pi (·.1.2), fun _ A φ ↦ (exists_isSolutionClosed φ.1).elim fun g h ↦ ⟨ofHom (g.kerLift.comp (e ⟨⟨⟨_, _⟩, h.2.isTest A.2⟩, ofHom (algebraMap ..)⟩)), hom_ext h.1⟩⟩
end Envelope
end
open CategoryTheory.Abelian.Ext in seal CategoryTheory.Abelian.Ext instAddCommGroup comp mk₀ homEquiv mapExactFunctor
noncomputable section
open CategoryTheory Limits Function Functor AddCommGrpCat MorphismProperty colimit Arrow LongExactSeq H Comparison
variable {C} [Category C] {F : AbFunctor C} {J} [SmallCategory.{0} J] [IsFiltered J] {D : Jᵒᵖ ⥤ C ⥤ Type 1} {T} [Category* T]
def IsFilteredColimit {X : J ⥤ Ab} (c : Cocone X) := (∀ j x, c.ι j x = 0 → ∃ i f, @X.map j i f x = 0) ∧ ∀ y : c.pt, ∃ j x, c.ι j x = y
abbrev cohFunctor F n := opHom T (AbFunctor C) ⋙ (whiskeringRight ..) ⟨_, (ofHom <| map F ·.unop n), by aesop, fun _ _ ↦ ext (map_comp _ _)⟩
def ContinuousUpTo F (c : Cone D) := BijectiveUpTo fun n ↦ desc _ ((cohFunctor F n ⟨freeAb⟩).mapCocone (coconeRightOpOfCone c))
attribute [local instance] preservesSmallestFilteredColimits_of_preservesFilteredColimits
lemma fcBij {X : J ⥤ Ab.{2}} {c} : IsFilteredColimit c ↔ Bijective (desc X c) := by have z := (by simpa using Concrete.from_union_surjective_of_isColimit X (isColimit _)); simp [IsFilteredColimit, Bijective, injective_iff_map_eq_zero, Surjective, z.forall, z.exists, Sigma.forall, by simpa using ((isColimit X).eq_iff' (i := ·) · 0)]
lemma ContinuousUpTo.of_cech {A : Jᵒᵖ ⥤ _} (a : Cone A) (hp : ∀ j, IsCover F (A j).hom) (hq : IsCover F a.pt.hom) {r} (h₀ : ContinuousUpTo F (leftFunc.mapCone a) r) (h : ∀ m, ContinuousUpTo F ((cF m).mapCone a) (r - 1)) : ContinuousUpTo F (rightFunc.mapCone a) r := let G := (whiskeringLeft ..) A.rightOp ⋙ colim
  let η : G ⟶ (evaluation ..) _ := ⟨(desc _ <| ·.mapCocone (coconeRightOpOfCone a)), by simp [G, colimit.hom_ext_iff]⟩
  let k := ((toArr ⋙ whiskeringLeft ..).flip.op ⋙ cohFunctor F ·)
  (BijectiveUpTo.congr (fun n ↦ (colim.mapIso (isoOfAppBijective _ (hp ⟨·⟩ n))).addCommGroupIsoToAddEquiv.bijective) hq fun n x ↦ (η.naturality_apply ((k n).map ⟨freeAb.map (Subfunctor.range leftToRight).ι⟩) x).symm).2 (cech_descent_step _ (f := fun N n ↦ η (k n ⟨N⟩)) ⟨fun {S _} x ↦ by
    let L {t} := contravariant (x.map_of_exact ((whiskeringLeft ..) (toArr t))) F
    refine LongExactSeq.Hom.four_lemma (by constructor <;> intro <;> apply η.naturality_apply : Hom ⟨(k · ⋙ G |>.map S.g.op |>.hom), (k · ⋙ G |>.map S.f.op |>.hom), fun n ↦ (G.map ⟨fun t ↦ @ofHom (L.C n) (L.A _) _ _ (L.δ n), fun _ _ f ↦ .symm (ext
      ?n)⟩).hom, (AddCommGrpCat.mono_iff_injective _).1 ((monomorphisms _).colimMap _ fun _ ↦ ConcreteCategory.mono_of_injective _ L.injective_f), ?_, ?_, ?_⟩ L ..)
    case n => simpa only [id_pull] using! (pull_hom_contravariant (x.map_of_exact _) _ (.id F) (S.mapNatTrans ((whiskeringLeft ..).map _))).comm_delta n
    all_goals exact fun _ ↦ exact_of_shortComplex_exact ((exact_of_app fun _ ↦ by apply_rules [L.exact_f_g, L.exact_g_delta, L.exact_delta_f]).2.map G)⟩ h₀ h)
end
section
open CategoryTheory CommRingCat IsLocalization Ideal Quotient
variable {X Y W V : PointFunctor} {p : X ⟶ Y} {u : W ⟶ Y} {q v R} (s : X ⟶ reprBy R) (I)
abbrev IsRelAffine : MorphismProperty PointFunctor := reprFunctor.relativelyRepresentable
lemma IsRelAffine.baseChange : IsRelAffine p → IsPullback v q p u → @IsRelAffine V W q := flip IsRelAffine.of_isPullback
lemma IsRelAffine.comp : @IsRelAffine W X v → IsRelAffine p → IsRelAffine (v ≫ p) := IsRelAffine.comp_mem v p
lemma unitPoints_le_range_reprMap L [CommRing L] [Algebra R L] M [IsLocalization (R := R) M L] : unitPoints (𝟙 _) M ≤ .range (reprMap (ofHom (algebraMap R L))) := fun _ _ _ ↦ ⟨⟨_⟩, congr(⟨ofHom $(lift_comp (by simpa))⟩)⟩
lemma isRelAffine_of_zero_unit_locus {U} (h : ∀ {R} y, ∃ A N : Set _, ∀ B f, @Y.map R B f y ∈ U B ↔ (∀ a ∈ A, f a = 0) ∧ ∀ a ∈ N, IsUnit (f a)) : IsRelAffine (Subfunctor.ι U) := fun _ ↦ uliftCoyonedaEquiv.forall_congr_left.2 (h · |>.elim fun A ⟨N, h⟩ ↦ let L := Localization (.closure N); ⟨_, ⟨ofHom (algebraMap _ (_ ⧸ span (algebraMap _ L '' A)))⟩, pointMap ⟨_, (h ..).2 ⟨fun _ _ ↦ eq_zero_iff_mem.2 (by aesop), (isUnit_comp _ _ ⟨·, Submonoid.subset_closure ·⟩)⟩⟩, isPullback_iff.2 ⟨fun _ _ ↦ (Y.map_comp_apply ..).symm, by
    rintro _ ⟨⟩ ⟨⟩ ⟨⟩; cases (h ..).1 ‹_›; obtain ⟨l, ⟨⟩⟩ := (unitPoints_le_range_reprMap L _ _ (((IsUnit.submonoid _).comap _).closure_le.2 ‹_›)); exact ⟨⟨ofHom (lift _ _ ((RingHom.ker _).span_le.2 (by simpa)))⟩, ⟨rfl, SetCoe.ext (Y.map_comp_apply ..).symm⟩, fun ⟨_⟩ ⟨a, _⟩ ↦ congrArg _ (hom_ext (ringHom_ext (ringHom_ext (.closure N) congr($a.1.1))))⟩⟩⟩)
lemma isRelAffine_zeroPoints : IsRelAffine (zeroPoints s I).ι := isRelAffine_of_zero_unit_locus (⟨baseRingMap s · '' I, ∅, by simp [zeroPoints]⟩)
open Limits colimit Concrete Function Abelian.Ext LocallyConstant PrimeSpectrum Comparison ULift IsFiltered
variable {Λ : Ab} {J B B' T T'} (q : T ⟶ testIncl ⋙ reprBy B) {q' : T' ⟶ testIncl ⋙ reprBy B'} [SmallCategory J] [IsFiltered J] {L : J ⥤ CommRingCat}
lemma isFilteredColimit_locConstSpec {c : Cocone L} (s : ∀ y : c.pt, ∃ j x, c.ι j x = y) (h : ∀ j x, c.ι j x = 0 → ∃ i f, @L.map j i f x = 0) : IsFilteredColimit ((locConstSpec Λ).mapCocone c) := ⟨fun j x l ↦ (isClopen_iff_zeroLocus.1 (x.2.isClopen_fiber 0)).elim fun e ⟨i, o⟩ ↦ by peel h _ e ((i.map _).eq_zero_of_isNilpotent (nilpotent_iff_mem_prime.2 (o.le congr($l.1 ⟨·, ·⟩) rfl))) using LocallyConstant.ext fun _ ↦ o.ge (by aesop), fun y ↦ (locallyConstant_mem_of_indicator (fun a e k ↦ (s e).elim fun j ⟨d, r⟩ ↦ (h _ (d * d - d) (by aesop)).elim fun i ⟨f, _⟩ ↦ by simpa only [← r, ← c.w f] using ⟨_, ι_desc_apply ((locConstSpec Λ).mapCocone c) i (indicator (.const ..) (isClopen_iff.2 ⟨_, by aesop, rfl⟩))⟩) y : y ∈ (desc (C := Ab) ..).hom.range).elim (colimit_exists_rep _ · |>.elim (by aesop))⟩
noncomputable def locConstClass : ∀ n, locConstSpec Λ B →+ H (freeAb T) (locConstCoeff Λ) n
  | 0 => .comp (.mk' mk₀ mk₀_add)
    ((Comparison.homOfValue ⟨testIncl, 𝟙 (_ ⋙ liftCoeff _)⟩ q).comp (.mk' _ (by tauto))) | _ => 0
def IsAcyclicOver Λ := Injective (@locConstClass Λ B T q 0) ∧ ∀ n, Surjective (@locConstClass Λ B T q n)
variable {q}
lemma map_locConstClass {e f f'} (h : ∀ c x, (locConstSpec Λ).map (q c (e c x)).1 f = (locConstSpec Λ).map (q' c x).1 f') : ∀ n, .map _ (freeAb.map e) n (locConstClass q n f) = locConstClass q' n f'
  | 0 => (mk₀_comp_mk₀ ..).trans (congrArg _ (freeAb.hom_ext fun _ _ ↦ congr(⟨$(by tauto)⟩)))
  | _+1 => map_zero _
lemma bijective_const_of_isDomain {Λ} [IsDomain B] : Bijective (⟨.const _ ·⟩ : Λ → ULift.{1} (LocallyConstant (PrimeSpectrum B) Λ)) := ⟨fun _ _ ↦ (congr($(·).1 ⊥)), fun ⟨x⟩ ↦ x.eq_const ⊥ ▸ ⟨_, rfl⟩⟩
lemma IsAcyclicOver.isCohomEquiv (a : IsDomain B) (b : IsDomain B') u (h : IsAcyclicOver q Λ)
    (h' : IsAcyclicOver q' Λ) : IsCohomEquiv (locConstCoeff Λ) (@freeAb.map T' T u)
  | 0 => (bijective_iff_of_comm_sq (by exact fun _ ↦ map_locConstClass (by tauto) 0) (.comp ⟨h.1, h.2 0⟩ (down_bijective.comp bijective_const_of_isDomain)) (.comp ⟨h'.1, h'.2 0⟩ (down_bijective.comp bijective_const_of_isDomain))).1 bijective_id
  | _+1 => ⟨(h.2 _).forall₂.2 (by tauto), (h'.2 _).forall.2 fun _ ↦ ⟨_, map_zero _⟩⟩
seal Comparison.homOfValue
lemma IsAcyclicOver.of_bijective (h : IsTest B) (b : ∀ {C}, Bijective (q C)) : IsAcyclicOver q Λ := (isBijective_reprBy_iff.1 (.precomp_of_bijective (isBijective_of_repr _ (pointMap_id_bijective_of_fullyFaithful testIncl ⟨B, h⟩) bijective_id) q (Category.comp_id _) @b)).elim fun a b ↦ ((mk₀_bijective ..).comp (a.comp up_bijective)).imp_right (Nat.rec · fun _ _ ↦ (⟨0, (b _).1 _ ·⟩))
abbrev onTests := restrictAlong (D := Type 1) testIncl
lemma cULC (h : ∀ j, IsTest (L j)) : ∀ r, ContinuousUpTo (locConstCoeff Λ) ((reprFunctor ⋙ onTests).mapCone (cocone L).op) r := have ht : IsTest ↑(colimit L) := (by choose j _ hy using colimit_exists_rep L; choose! z hz using fun s x _ ↦ Set.mem_range.2 ⟨_, hy _ ▸ w_apply L (toSup (.image ..) ∅ (by aesop)) _⟩; use ⟨fun P ↦ (h _).exists_root_of_coeffs_subset_range (by tauto)⟩, fun f g ↦ ((h _).2 (z _ f) (z {f, g} g)).imp' (ι L _) (by grind [IsIdempotentElem, → map_dvd (ι L _).hom]), fun x ⟨n, e⟩ ↦ ?_; erw [← hy x, ← map_zero (ι L _).hom, ← map_pow, (isColimit L).eq_iff'] at *; grind [(h _).3.1 _ ⟨n, _⟩]); forall_bijective_iff_bijectiveUpTo.1 (fcBij.1 ∘' by choose i s using (@IsAcyclicOver.of_bijective Λ · _ (𝟙 _) · bijective_id); rintro ⟨⟩ <;> simp [IsFilteredColimit, (s _ _ _).forall, (s _ _ _).exists, (i ..).eq_iff, ↓fun A B φ x ↦ @map_locConstClass Λ A B _ _ (𝟙 _) (𝟙 _) (mapOnTests (reprMap φ)) x ((locConstSpec _).map φ x) (by tauto), _root_.map_eq_zero_iff, locConstClass.eq_2, nonempty, *]; exacts [isFilteredColimit_locConstSpec (colimit_exists_rep _) fun _ x ↦ by simpa using ((isColimit L).eq_iff' x 0).1, (⟨·, ⟨𝟙 _⟩⟩)])
end
section
open CategoryTheory Limits IsLimit colimit Functor essImage Over Comma Subfunctor Subalgebra Algebra CostructuredArrow.CreatesConnected Types FilteredColimit Preorder
attribute [local simp] OverMorphism.ext_iff fibreProd
variable {X Y W : PointFunctor} (u : W ⟶ X) (s : X ⟶ Y)
lemma HV.map_comp {Λ n} x : map Λ (u ≫ s) n x = map Λ u n (map Λ s n x) := by simp [H.map]
lemma baseChangeOf.ext {A R s φ B} {x y : @baseChangeOf X R s A φ B} (h : x.1.1 = y.1.1) (e : ∀ a, x.1.2.1.hom a = y.1.2.1.hom a) : x = y := congr(⟨($h, ⟨$(by aesop)⟩), _⟩)
set_option backward.isDefEq.respectTransparency false
def pbO : Over Y ⥤ Over X := .mk (.mk <| fibreProd.fst s ·.3) fun f ↦ homMk (.mk fun _ ↦ ↾(⟨(_, f.1 _ _), congr(($f.w) _ _) ▸ ·.2⟩))
instance : (pbO s).IsRightAdjoint := ⟨_, ⟨(mapPullbackAdj s).ofNatIsoRight (NatIso.ofComponents fun _ ↦ isoMk isPullback_fibreProd.isoPullback).symm⟩⟩
def IsCohomContinuous Λ X := ∀ ⦃J⦄ [SmallCategory J] [IsFiltered J] ⦃D⦄ ⦃c : Cone D⦄, IsLimit ((forget X).mapCone c) → (∀ j : Jᵒᵖ, IsRelAffine (D j).hom) → ∀ r, ContinuousUpTo (locConstCoeff Λ) ((forget X ⋙ onTests).mapCone c) r
variable {Λ R} {S : CommRingCat} (s : X ⟶ reprBy R) {T} {q : X ⟶ Y} {α} [Preorder α] {V : α → Subfunctor Y} (hV : Antitone V)
lemma IsCohomContinuous.of_isRelAffine (h : IsRelAffine q) (hY : IsCohomContinuous Λ Y) : IsCohomContinuous Λ X := fun _ _ _ _ c ↦ (hY (c := (map q).mapCone c) · ∘ (· · |>.comp h))
noncomputable abbrev HV.antitoneFamily Λ n := .mk _ (hV ·.le |> homOfLe |>.op) ⋙ onTests.op ⋙ cohFunctor (locConstCoeff Λ) n ⟨freeAb⟩
lemma IsCohomContinuous.isFilteredColimit_antitoneFamily {J} [SmallCategory J] [IsFiltered J] {D : J ⥤ α} (h : IsCohomContinuous Λ Y) (ht : ∀ j, IsRelAffine (V j).ι) {m : Cocone D} (e : ∀ {A x}, (∀ j, x ∈ V (D j) A) → x ∈ V m.1 A) {n} : IsFilteredColimit ((HV.antitoneFamily hV Λ n).mapCocone m) := fcBij.2 (forall_bijective_iff_bijectiveUpTo.2 (h (isLimitOfPreserves _ (isLimitOfPreserves ((equivalenceMonoOver _).1 ⋙ MonoOver.forget _) (isLimitOfIsGLB _ (mapCone ((orderDualEquivalence _).2 ⋙ hV.dual_left.functor) m.op) ⟨conePt_mem_lowerBounds .., fun _ _ _ _ ↦ by aesop⟩))) (by tauto)) n)
def baseChangeFunctor := ((opEquivOpUnder R).2 ⋙ post uliftCoyoneda ⋙ pbO s) ⋙ forget X
abbrev baseChangeTransition {a b} (f : S ⟶ T) (h : a ≫ f = b) : baseChangeOf s b ⟶ baseChangeOf s a := (baseChangeFunctor s).map (Under.homMk f h : Under.mk a ⟶ .mk b).op
lemma IsCohomContinuous.isFilteredColimit_adjoin (h : IsCohomContinuous Λ X) T [CommRing T] [Algebra S T] a n : IsFilteredColimit (((baseChangeFunctor s ⋙ onTests).rightOp ⋙ cohFunctor (locConstCoeff Λ) n ⟨freeAb⟩).mapCocone ((Under.map a).mapCocone (J := Finset T) (F := .mk (S.mkUnder <| adjoin S (A := T) ·) (adjoin_mono ·.le |> inclusion |>.toUnder)) ⟨_, .mk fun _ ↦ (val _).toUnder⟩)) := fcBij.2 (forall_bijective_iff_bijectiveUpTo.2 (h (isLimitOfPreserves _ (isLimitOfPreserves (_ ⋙ _ ⋙ pbO s) ((reflectsColimit_of_reflectsIsomorphisms _ (Under.forget R ⋙ forget _)).1 (isColimitOf' _ _ (by exact (⟨{·}, ⟨_, by simp⟩, rfl⟩)) fun _ _ _ ↦ (⟨_, 𝟙 _, SetCoe.ext ·⟩))).some.op)) fun _ ↦ .baseChange (.map uliftCoyoneda _) isPullback_fibreProd) n)
lemma IsCohomContinuous.of_atlas {q} (r : @IsRelAffine (reprBy T) Y q) (hq : HasCohomDenseImage Λ q) : IsCohomContinuous Λ Y := fun J _ _ D c hc d n ↦ have := IsFiltered.isConnected J; by
  induction' n with _ ih generalizing D; tauto
  have ⟨B, e⟩ : Σ B, .op B ⋙ uliftCoyoneda ≅ D ⋙ pbO q ⋙ forget _ := ⟨.unop _, liftFunctorCompIso _
    uliftCoyoneda fun _ ↦ ⟨_, ⟨((d _).isPullback _).isoIsPullback _ _ isPullback_fibreProd⟩⟩⟩
  let ⟨E, θ, _, s⟩ := Envelope.exists_functorial_test (Option.rec (colimit B) B)
  let ε : pbO q ⋙ forget _ ⟶ forget Y := .mk (fibreProd.snd _ ·.3)
  let p := whiskerRight (NatTrans.op (B.whiskerLeft θ)) _ ≫ e.1 ≫ D.whiskerLeft ε
  let K {D} o e : HasCohomDenseImage Λ (reprMap _ ≫ Iso.hom e ≫ ε D) := hq.of_preimage_le (mapOnTests _) fun A _ ⟨_, k⟩ ↦ ((e.app _).toEquiv.surjective.comp
    (ULift.map_surjective.2 (s o A)) ⟨(_, _), k⟩).imp fun _ ↦ (congrArg (·.1.2) ·)
  let a := coneOfPreserves (toArr (.mk p)) (reprFunctor.mapCone (cocone _).op) hc
  let _ m : (cech Arrow.leftToRight m).IsCorepresentable := ⟨isTerminalPUnit.from (ULift _), ⟨.mk (.mk ((cech ..).map · ⟨.up, by tauto⟩) (fun e ↦ ⟨↾(e.1 ·.1), ↾fun _ ↦ _, by ext; apply e.2 _ 0⟩) (by ext; exacts [rfl, congr($(·.w) _)]))⟩⟩
  refine .of_cech (onTests.mapArrow.mapCone a) (K ·.1 (e.app _) |>.isCohomEquiv)
    ((K none ((isLimitOfPreserves _ (isColimit _).op).conePointsIsoOfNatIso (isLimitOfPreserves _ (isLimitOfReflects _ hc)) e)).mono ?_).isCohomEquiv (cULC (by tauto) _)
    fun m ↦ ih (Over.lift (toArr (.mk p) ⋙ cF _) (.mk (p · |> (cech.proj · _ 0)) ≫ p ≫ .mk fun _ ↦ hom _)) (raiseCone ((cF _).mapCone a))
    (evaluationJointlyReflectsLimits _ (let v := (evaluation ..) ·; fstSndJointlyReflectLimit (c := v.mapArrow.mapCone a) (isLimitOfPreserves (uliftCoyoneda ⋙ v) (isColimit _).op) (isLimitOfPreserves v hc) |> isLimitOfPreserves (cech ..))) (.comp ?_ <| .comp ?R <| d ·)
  erw [(hc.hom_ext fun _ ↦ ?_ : _ ≫ _ = reprMap (post ..) ≫ _), mapOnTests, whiskerLeft_comp]
  apply range_comp_le
  simp; erw [← ε.2, map_π_assoc, fac, ← map_comp_assoc, ← op_comp, θ.2, ← ι_post]
  exacts [rfl, m.rec (.of_isIso ..) fun _ h ↦ (h.comp ?R).baseChange (.flip isPullback_cech), .comp (.map uliftCoyoneda _) (.comp (.of_isIso ..) (r.baseChange isPullback_fibreProd.flip))]
end
open PrimeSpectrum ULift CommRingCat Ideal Quotient CategoryTheory Functor ConcreteCategory
lemma IsTest.radIdem {A} [CommRing A] (h : IsTest A) {e : A} (he : IsIdempotentElem e) : (span {e}).IsRadical := he.ker_toSpanSingleton_one_sub_eq_span ▸ fun x ⟨n, _⟩ ↦ h.3.1 _ ⟨n + 1, by simp_all [mul_pow]; grind⟩
lemma hasPartitions_locConstCoeff {Λ} : HasPartitions testIncl (locConstCoeff Λ) := ⟨fun A e h _ ↦ ⟨⟨_, A.2.quotient (A.2.radIdem h)⟩, ⟨CommRingCat.ofHom _⟩, mk_singleton_self _, fun _ f _ ↦ ⟨⟨CommRingCat.ofHom (lift _ f.1.hom (by simp_all [mem_span_singleton']))⟩, by aesop⟩, exists_rep, mk_ker.le⟩, fun _ _
  h ↦ Eq.subst (by ext x <;> use congr(x.1 $(by ext; erw [mem_prod]; simp))) (Equiv.ulift.trans
  ((LocallyConstant.congrLeft ((homeomorphOfRingEquiv (.ofBijective (RingHom.prod ..) h)).trans primeSpectrumProdHomeo)).trans (.mk (fun x ↦ (up (x.comap (.mk .inl)), up (x.comap (.mk .inr)))) (fun (⟨x⟩, ⟨y⟩) ↦ ⟨Sum.elim x y, (⟨x.2 ·, y.2 _⟩)⟩) (by cat_disch)))).bijective⟩
lemma Comparison.coeffCompBij_id_iff_restrict {C C' D S} [Category C] [Category C'] [Category D] [CommRing S] {φ N} {N' : AbFunctor C'} {α : N' ⟶ φ ⋙ N} {Ψ : C ⥤ D} {G M} (θ : Ψ ⋙ G ≅ M) : CoeffCompBij (S := S) (𝟙 (φ ⋙ Ψ)) α G ↔ (restrict φ (moduleCoeff M)).IsBijective α := let γ := whiskerRight θ.1 (moduleCoeff (𝟭 _)); by apply isBijective_iff_of_coeff_iso γ (φ.whiskerLeft γ); aesop
variable {C k S} [Category C] [CommRing k] [CommRing S] [Algebra k S]
def algBaseChangeAdj : algBaseChange S ⊣ restrictAlg k S := .mkOfHomEquiv (.mk (homEquiv.trans <| .symm <| homEquiv.trans <| @AlgHom.liftEquiv k S · · _ _ _ _ _ _ _ (_) (.of_compHom ..)) fun _ _ ↦ ConcreteCategory.ext tmul_ext)
abbrev baseChangeTranspose := ((@algBaseChangeAdj k S _ _ _).whiskerRight C).homEquiv
lemma pointMap_algBaseChange_unit_bijective B : AllBijective (pointMap (Y := restrictAlg k S ⋙ reprBy B) ⟨algBaseChangeAdj.unit B⟩ ·) := fun _ ↦ ULift.map_bijective.2 (algBaseChangeAdj.homEquiv ..).bijective
open Function Perfection RingHom WittVector Subfunctor Abelian.Ext LongExactSeq
variable {p} [ThePrime p] (c : PadicTest)
noncomputable def cellPoint B {I} [n : Nonempty I] {W : I → _} [∀ i, CommRing (W i)] [∀ i, IsCell p (W i)] (y : ∀ i, B.1 →+* W i) : Sigma (PadicTest.algFunctor ⋙ reprBy B) := ⟨⟨I, W, .comp (.pi y) _⟩, ⟨ConcreteCategory.ofHom ⟨.pi y, by tauto⟩⟩⟩
lemma PadicTest.isTest : IsTest c.ProdRing := .pi
instance : IsAIC c.ProdRing := c.isTest.1
lemma PadicTest.isLeftRegular_p : IsLeftRegular (p : c.ProdRing) := Pi.isLeftRegular_iff.2 fun _ ↦ by simp [isRegular_iff_ne_zero, IsCell.p_ne_zero]
noncomputable def PadicTest.tiltPiEquiv := RingEquiv.ofBijective (RingHom.pi (tiltMap (p := p) <| Pi.evalRingHom c.Cell ·)) (((quotientMulEquiv ..).bijective_comp _).1 ((((Equiv.piComm fun _ ↦ c.Cell).subtypeEquiv (by simp [funext_iff]; tauto)).trans .subtypePiEquivPi).trans (.piCongrRight fun _ ↦ (quotientMulEquiv ..).1)).bijective)
lemma PadicTest.dvdU {x y : c.TiltRing} (h : x.untilt ∣ y.untilt) : x ∣ y := (map_dvd_iff c.tiltPiEquiv).1 <| pi_dvd_iff.2 (untilt_dvd_iff.1 <| by convert pi_dvd_iff.1 h · <;> apply untilt_tiltMap)
lemma PadicTest.isPerfectTorsionFree_tilt : IsPerfectTorsionFree (tilt c) := (⟨inferInstance, .of_right_eq_zero_of_smul fun _ _ ↦ zero_dvd_iff.1 (c.dvdU (c.isLeftRegular_p (Dvd.elim_left (map_dvd c.structureMap untilt_constantCoeff_xi_dvd_p) (by simp_all [pFlat, ← untilt_tiltMap, mul_assoc, ← map_mul, Algebra.smul_def, algebraMap]))).dvd)⟩ : IsPerfectTorsionFree (.of _ c.TiltRing))
@[simp] lemma PadicTest.ker_theta : ker (fontaineTheta c.ProdRing p) = span {xi.map (algebraMap ..)} := have h := mem_ker.2 ((fontaineTheta_map_tiltMap ..).trans (theta_xi ▸ c.structureMap.map_zero))
  le_antisymm (mem_span_singleton.2 <| Witt.dvd_of_mem_of_constantCoeff_dvd h (by simp [c.isLeftRegular_p.mul_left_eq_zero_iff]) (fun _ _ ↦ c.dvdU ((untilt_tiltMap ..).dvd.trans ((map_dvd _ untilt_constantCoeff_xi_dvd_p).trans (by simp_all [← Quotient.eq_zero_iff_dvd, ← mk_fontaineTheta])))) · ·) (by simpa)
lemma PadicTest.exists_isIdemQuotient (e : c.ProdRing) (he : IsIdempotentElem e) (h : e ≠ 1) : ∃ d f, IsIdemQuotient (B := d) ringFunctor e f := let f := (cellPoint (.of ..) (n := nonempty_subtype.2 (ne_iff.1 h)) (Pi.evalRingHom c.Cell ·)).2.1.1
  let s := Subtype.surjective_restrict _
  let k x h := mem_span_singleton'.2 ⟨x, by
    simpa [funext_iff, mul_right_eq_self₀, or_iff_not_imp_left, cellPoint] using! congrFun h⟩
  ⟨_, f, funext (eq_zero_of_mul_eq_self_left ·.2 congr($he _)), fun d g h ↦ f.liftOfSurjective_comp s g (.trans k (by simpa)) ▸ ⟨_, rfl, (·.cancel_right s |>.1)⟩, s, k⟩
noncomputable def PadicTest.thetaIso : tilt ⋙ wittFunctor ⋙ algBaseChange _ ≅ algFunctor := isoOfAppBijective ((baseChangeTranspose (_ ⋙ wittFunctor) _).2 ⟨(ConcreteCategory.ofHom ⟨_, fontaineTheta_map_tiltMap ·.structureMap⟩), fun _ _ f ↦ ext_apply (fontaineTheta_map_tiltMap f.1)⟩) fun c ↦ ⟨.of_ker _ ((TensorProduct.mk_surjective _ _ _ theta_surjective).forall.2 fun _ ↦ (c.ker_theta.trans_le ((ker Algebra.TensorProduct.includeRight).span_singleton_le_iff_mem.2 ((AlgHom.commutes ..).trans (by simp [algebraMap]))) <| (one_smul OC _).symm.trans ·)), by exact fontaineTheta_surjective_of_isAIC (R := c.ProdRing).forall.2 (⟨1 ⊗ₜ ·, one_smul OC _⟩)⟩
lemma PadicTest.thetaIso_hom_one_tmul x : thetaIso.1 c (1 ⊗ₜ x) = x.fontaineTheta _ p := one_smul OC _
variable {Λ R} [CommRing.{0} R] {X Y : PointFunctor} {U V W : Subfunctor Y} (l : U ≤ W) (l' : V ≤ W)
lemma IsRelAffine.preimage (h : IsRelAffine U.ι) (f : X ⟶ Y) : IsRelAffine (U.preimage f).ι := h.baseChange (v := fromPreimage ..) (isPullback_iff.2 (by aesop (add simp [ExistsUnique, toFunctor])))
lemma HV.mayer_vietoris_injective (d : IsCohomDense (locConstCoeff Λ) (((U ⊔ V).preimage W.ι).whisker testIncl)) n : ∀ {T} (e : T = U ⊓ V), let P := (map Λ (homOfLe l) n).prod (map Λ (homOfLe l') n); ((∀ m < n, ∀ z, ∃ x y, map Λ (homOfLe (e ▸ inf_le_left)) m x - map Λ (homOfLe (e ▸ inf_le_right)) m y = z) → Injective P) ∧ ((∀ B, T.toFunctor B → (0 : B) = 1) → Bijective P)
  | _, rfl => have r := (isCohomEquiv_iff_range (g := homOfLe (by simp; tauto : U.whisker testIncl ⊔ V.whisker _ ≤ W.whisker _)) (by aesop (add simp [homOfLe, toFunctor]))).2 d.isCohomEquiv; by
      constructor <;> intro h <;> [convert! ← (biprodAddEquiv.injective.comp (flip .comp (r n).1 ((contravariant mvSE.2 _).f_injective_of_g_surjective (h · · ·
        |> Prod.exists'.2 |>.imp' biprodAddEquiv.symm ?_)))) <;> (delta contravariant);
        convert! ← (biprodAddEquiv.bijective.comp ((isCohomEquiv_quotient_of_acyclic mvSE.2 (hasPartitions_locConstCoeff.eq_zero_of_zero_ring (h ·.1))).comp_iff.2 r n))] <;> funext <;> simp [biprodAddEquiv, H.map, ← Functor.map_comp, sub_eq_add_neg] <;> tauto
lemma zorn_injective_and_surjective {α} [PartialOrder α] {G K : α ⥤ Ab} {π : ∀ _, _ →+ _} (w : ∀ {a b} h x, @K.map a b h (π a x) = π b (G.map h x)) (hc : ∀ {c : Set α} [IsDirectedOrder c] [Nonempty c], ∃ m, IsFilteredColimit (G.mapCocone m) ∧ IsFilteredColimit (K.mapCocone (F := .mk (·.1 : c → α) _root_.id) m)) : ((∀ a x, π a x = 0 → (∀ b (h : a < b), G.map h.le.hom x = 0) → x = 0) → ∀ a, Injective (π a)) ∧ ((∀ a y, (∀ b (h : a < b), ∃ x, π b x = K.map h.le.hom y) → ∃ x, π a x = y) → ∀ a, Surjective (π a)) := by refine ⟨fun hs _ ↦ .of_ker _ (hs _ · · ?_), (· · · ?_)⟩ <;> refine by_contra (not_forall₂.1 · |>.imp (zorn_le_nonempty₀ {b | _} fun c h h' z hz ↦ (@hc _ ⟨h'.directed⟩ ⟨_, hz⟩).imp' _ fun m ⟨k, l, _⟩ ↦ ⟨⟨(h hz).1.trans_le (m.ι ⟨_, hz⟩).le, fun e ↦ ?_⟩, (m.ι ⟨·, ·⟩ |>.le)⟩) |>.elim fun _ ⟨m, _, M⟩ ↦ M.1.2 (by apply_assumption <;> simp [← Functor.map_comp_apply] <;> grind [M.not_gt, M.1.1])); use (k.1 ⟨z, hz⟩ _ (G.map_comp_apply (h hz).1.le.hom .. ▸ e)).elim fun b ⟨_, s⟩ ↦ (h b.2).2 (G.map_comp_apply .. ▸ s); cases e; obtain ⟨b, x, rfl⟩ := k.2 ‹_›; refine (l b (π b x - K.map (h b.2).1.le.hom ‹_›) ?_).elim fun d ⟨q, s⟩ ↦ (h d.2).2 ⟨G.map q x, ?_⟩ <;> erw [_root_.map_sub, w, ← K.map_comp_apply, sub_eq_zero] at * <;> tauto
lemma Components.isCohomEquiv_of_connected (hX : IsCohomContinuous Λ X) (hY : IsCohomContinuous Λ Y) (u : X ⟶ Y) {U : Ideal R → Subfunctor Y} (hU : Antitone U) (r : ∀ a, IsRelAffine (U a).ι) (N : ∀ {A}, Y A → AddSubmonoid R) (m : ∀ {A x a}, x ∈ U a A ↔ a.toAddSubmonoid ≤ N x) (t : ∀ {A} {x : Y A}, 1 ∈ N x → Subsingleton A) (d : ∀ e, IsIdempotentElem e → IsCohomDense (locConstCoeff Λ) ((U (span {e}) ⊔ U (span {1 - e})).whisker testIncl)) (h : ∀ a ≠ ⊤, (∀ e, IsIdempotentElem e → e ∈ a ∨ 1 - e ∈ a) → Components Λ (fromPreimage (U a) u)) : Components Λ u := (IsCohomDense.of_top_le (U := (U ⊥).whisker _) fun _ _ _ ↦ m.2 bot_le).isCohomEquiv_of_fromPreimage fun n ↦ by
  have g {X} (p : X ⟶ Y) : Antitone (U · |>.preimage p) := by tauto
  have J {X} p {a e} i := let o e := @g X p _ (a ⊔ span {e}) le_sup_left;
      (HV.mayer_vietoris_injective (o e) (o (1 - e)) ((d e i).of_preimage_le (mapOnTests (_ ≫ p)) fun _ x ↦ by apply Or.imp <;> erw [m, m, a.sup_toAddSubmonoid] <;> use (sup_le (m.1 x.2))) n
      rfl).2 fun _ ⟨_, x, y⟩ ↦ (t (by
    convert add_mem (m.1 x (?_ : e ∈ _)) (m.1 y (?_ : 1 - e ∈ _)) <;> simp [mem_sup_right])).1 ..
  have S {a} := by simpa using or_not.imp_left fun g ↦ by_cases (· ▸ by
    apply @Unique.bijective .. <;> use ⟨0⟩, hasPartitions_locConstCoeff.eq_zero_of_zero_ring (by
    exact fun _ x ↦ (t (m.1 x.2 ⟨⟩)).1 ..) n) (h a · g n)
  refine (zorn_injective_and_surjective ?w ⟨⟨_, .mk (⟨⟨le_sSup ·.2⟩⟩)⟩, hY.isFilteredColimit_antitoneFamily hU r ?_, hX.isFilteredColimit_antitoneFamily (g u) (r · |>.preimage u) ?_⟩).imp (· (fun a x e G ↦ S.elim (·.1 ?_) fun ⟨_, j, _⟩ ↦ (_root_.map_eq_zero_iff _ (J (𝟙 _) j).1).1 (Prod.ext (G _ ?_) (G _ ?_))) _) (· (fun a y G ↦ S.elim (·.2 y) fun ⟨_, j, _⟩ ↦ (G _ ?_).elim fun x _ ↦ (G _ ?_).elim fun z _ ↦ ((J (𝟙 _) j).2 (x, z)).imp fun _ k ↦ (J u j).1 (by cases k; ext <;> use (?w le_sup_left.hom _).trans ‹_›)) _) <;> simp [*, ← HV.map_comp]; tauto
