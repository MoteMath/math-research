import Lib.Cohomology.Etale.ConnectedComponents
import Lib.Cohomology.Hodge.HodgeSite
open CategoryTheory.Abelian.Ext in seal CategoryTheory.Abelian.Ext instAddCommGroup comp mk₀ homEquiv mapExactFunctor
set_option backward.isDefEq.respectTransparency false
noncomputable section
section
open CategoryTheory Abelian TotalH AddCommGrpCat Function DirectSum Finsupp H
variable {C} [Category C] {N K : AbFunctor C}
abbrev pointFunctor C [Category C] := Functor.const C PUnit.{2}
def tensorPoint (ρ : freeAb (pointFunctor C) ⟶ K) : 𝟭 _ ⟶ abTensor.flip K where app _ := ⟨fun c ↦ ofHom ((TensorProduct.mk ℤ ..).flip (ρ c (.of ⟨⟩))).toAddMonoidHom, fun _ _ ↦ (ρ.naturality_apply · (.of ⟨⟩) ▸ rfl)⟩
lemma exists_tensor_class [HasFlatValues N] [HasFlatValues K] ξ : ∃ h : ∀ D [Category D] φ S, H _ (abTensor.flip (φ ⋙ K) S) 2, ∀ D [Category D] φ S, (∀ S' y, TotalH.comp (TotalH.map (abTensor.flip (φ ⋙ N)) y) (h D φ S').toTotalH = .comp (h D φ S).toTotalH (TotalH.map _ y)) ∧ (∀ [HasFlatValues S], (h D φ S).toTotalH = TotalH.map (abTensor S) (.map (restrictAlong φ) (.of _ 2 ξ))) ∧ ∀ E [Category E] (ψ : E ⥤ D), TotalH.map (restrictAlong ψ) (h D φ S).toTotalH = (h E (ψ ⋙ φ) (ψ ⋙ S)).toTotalH := by
  choose _ _ g h s using @acC C
  have f M : HasFlatValues (kerComplex (g M)).1 := have := @HasFlatValues.flat
    ⟨fun _ ↦ inferInstanceAs (Module.Flat _ (AddMonoidHom.toIntLinearMap _).ker)⟩
  obtain ⟨u, rfl⟩ := (s N _ _).comp ((s _ _ _).comp (Ext.mk₀_bijective ..).2) ξ
  have e {D} [Category D] φ N [HasFlatValues N] := @abTensor_shortExact D _ (φ ⋙ N) (φ ⋙ _) _
    (hS := (h N).map_of_exact (restrictAlong φ))
  use fun _ _ φ S ↦ (e ..).extClass.comp ((e _ (kerComplex _).1 _).extClass.comp (.mk₀ ((abTensor.flip.map (φ.whiskerLeft u)).1 S)) rfl) rfl, fun _ _ φ _ ↦ ⟨fun _ ↦ (·.induction_on ?_ ?_ ?_), by simp [↓TotalH.map_of, LongExactSeq.contravariant]; tauto⟩ <;> simp_all [← comp_of, TotalH.comp_assoc, naturality, smul_smul, comp_assoc_of_eq (extClass_sign_comm (e φ _) _), ← mul_pow, -TotalH.map_of, -Functor.flip_obj_obj, -Functor.flip_map_app]
variable {A} {C : _} [Category A] [Category C] {Φ} [@IsExactFunctor A C _ _ Φ] {G S S' n e F} {N : _} {M I} {d : I → ℕ} (θ : ∀ i, H (Φ G) F (d i)) {X : ShortComplex (AbFunctor A)} (h : X.ShortExact)
attribute [local simp] mapThenComp lof_eq_of comp_of LinearMap.restrict_apply comp_homClass_eq funext_iff
def lerayHirsch S : (I →₀ TotalH S G) →ₗ[ℤ] TotalH (Φ S) F := lsum ℤ fun i ↦ (mapThenComp Φ (θ i).toTotalH).toIntLinearMap
abbrev IsLerayHirschBasis S := Bijective (lerayHirsch θ S)
lemma lerayHirsch_single i x : lerayHirsch θ S (.single i x) = .comp (.map Φ x) (θ i).toTotalH := by simp [lerayHirsch]
lemma lerayHirsch_naturality {A' C'} [Category A'] [Category C'] {Φ'} [@IsExactFunctor A' C' _ _ Φ'] {G' T F' θ'} (r : TotalH S G →+ TotalH T G') {r' : _ →+ TotalH _ F'} (h : ∀ i x, mapThenComp Φ' (DirectSum.of _ (d i) (θ' i)) (r x) = r' (mapThenComp Φ (θ i).toTotalH x)) w : lerayHirsch θ' T (w.mapRange r r.map_zero) = r' (lerayHirsch θ S w) := by simp_all [lerayHirsch, sum_mapRange_index, map_finsuppSum]
lemma lerayHirsch_mapRange_comp {ξ ζ} (k : TotalH.map Φ ξ = ζ) w : lerayHirsch θ S' (w.mapRange _ (TotalH.comp ξ).map_zero) = .comp ζ (lerayHirsch θ S w) := lerayHirsch_naturality _ _ (by simp [map_comp_assoc, k]) w
@[aesop simp] def dT (d : I → ℕ) n := (finsuppLequivDFinsupp (M := TotalH S G) ℤ).symm.conj (DFinsupp.mapRange.linearMap fun i ↦ lmap (if · + d i < n then .id else 0))
lemma dTp (ξ : @H C _ M N e) : have φ := mapRange.linearMap (TotalH.comp (F := F) ξ.toTotalH).toIntLinearMap; φ ∘ₗ dT d n = dT d (n + e) ∘ₗ φ := by aesop (add safe (by omega))
lemma dTl S n : have φ := lsingle () ∘ₗ lerayHirsch θ S; φ ∘ₗ dT d
    n = dT 0 n ∘ₗ φ := by aesop (add simp lerayHirsch)
def tM {J b m φ} (h : φ ∘ₗ @dT A _ G S I d n = @dT C _ F N J b m ∘ₗ φ) := show (.of (dT d n).range : Ab) →+ (.of (dT b m).range : Ab) from (φ.restrict (by simp_all [LinearMap.ext_iff])).toAddMonoidHom
variable {θ}
lemma bijective_lerayHirsch_iff : IsLerayHirschBasis θ S ↔ AllBijective (tM <| dTl θ S ·) := by simpa [AllBijective, Bijective, tM, injective_iff_map_eq_zero, Surjective] using ⟨fun h n ↦ ⟨by tauto, fun z ↦ (h.2 (z ⟨⟩)).imp fun _ _ ↦ congr($(dTl ..) _).trans (by aesop)⟩, fun h ↦ ⟨fun a e ↦ by ext i m; simpa [dT] using congr($((h (m + d i).succ).1 a (by simpa [e] using congr($(dTl θ ..) a))) i m), (·.induction_on ⟨0, by simp⟩ (fun n z ↦ ((h n.succ).2 (single ⟨⟩ z.toTotalH)).imp' _ fun _ e ↦ by simpa [dT] using congr($e ⟨⟩)) @(LinearMap.range _).add_mem)⟩⟩
lemma tMe {ξ ζ} (h : Exact (TotalH.comp (DirectSum.of _ _ ξ)) (@TotalH.comp C _ S M F (DirectSum.of _ n ζ))) m : Exact (tM (@dTp C _ m e F N M I d ξ)) (tM (dTp ζ)) := by simpa [Exact, tM] using fun a ↦ ⟨fun k ↦ ((range_mapRange ..).ge ((h _).1 congr($k ·))).imp fun _ _ ↦ congr($(dTp ..) _).trans (by aesop), fun ⟨_, k⟩ ↦ k ▸ Finsupp.ext (by simp [h _])⟩
def tMl := LongExactSeq.mk _ _ _ (by rintro ⟨_, _, _⟩ ⟨_, _, _⟩ _; ext; aesop)
  (tMe (d := d) (exact_triangle h G).1) (tMe (exact_triangle h _).2.1)
  (tMe (exact_triangle ..).2.2)
lemma lerayHirsch.longExact_hom : have t {S} n := tM (dTl θ S n); (tMl h).Hom (tMl (h.map_of_exact Φ)) t t t := by constructor <;> intros <;> apply_rules [Subtype.ext, Eq.trans _ mapRange_single.symm, congrArg (single _), lerayHirsch_mapRange_comp] <;> aesop
lemma lerayHirsch.devissage : Devissage (tM <| dTl θ · ·) := ⟨⟨(longExact_hom · |>.four_lemma)⟩, fun _ h ↦ bijective_lerayHirsch_iff.1 (by
  obtain _ := subsingleton_of_id_eq_zero h, subsingleton_of_id_eq_zero (by simpa using Φ.congr_map h); aesop), fun _ e ↦ (longExact_hom e).five_lemma⟩
lemma isClosedClass_lerayHirsch : IsClosedClass (IsLerayHirschBasis θ ·) := by simp [bijective_lerayHirsch_iff, lerayHirsch.devissage.isClosedClass]
lemma Devissage.bijective_of_sigma_repr {A B f} (h : @Devissage C _ A B f) (k : ∀ ι (c : ι → C), AllBijective (f (freeAb.obj (sigma (reprBy <| c ·))))) S : AllBijective (f S) := forall_bijective_iff_bijectiveUpTo.2 (·.rec (by tauto) (fun _ _ S ↦ by choose _ _ _ e _ using acC S; apply_rules [h.step e, forall_bijective_iff_bijectiveUpTo.1]) S)
lemma lerayHirsch_bijective_of_repr [Finite I] {φ} {θ : ∀ i, H (restrictAlong φ G) F (d i)} (h : ∀ c, IsLerayHirschBasis θ (freeAb (reprBy c))) S : IsLerayHirschBasis θ S := bijective_lerayHirsch_iff.2 (lerayHirsch.devissage.bijective_of_sigma_repr (fun _ X ↦ bijective_lerayHirsch_iff.1 (have j {D} [Category D] N {F} : Injective fun x c ↦ pullbackAlong (G := F) (freeAb.map (@sigma.ι D _ _ N c)) x := fun _ _ e ↦ DirectSum.ext fun m ↦ (sigma_bijective ..).1 (by simpa using congr(($e · m))); .of_comp_left (by exact (funext₂ fun x c ↦ lerayHirsch_mapRange_comp θ map_homClass x).subst ((Bijective.piMap (h ∘' X)).comp ⟨fun x y e ↦ Finsupp.ext fun i ↦ j _ congr(($e · i)), fun w ↦ by
    choose y _ using fun i ↦ (sigma_bijective ..).2 (w · i 0)
    use equivFunOnFinite.symm (y · |>.toTotalH)
    ext _ _ ⟨⟩ <;> aesop_cat⟩)) (j (φ.comp ∘ reprBy ∘ X)))) S)
end
open CategoryTheory Function QuotientAddGroup AddCommGrpCat ObjectProperty Abelian.Ext CategoryOfElements Ideal CommAlgCat CartesianMonoidalCategory TotalH Comparison H Subtype
export CartesianMonoidalCategory (toUnit)
variable {C C'} [Category C] [Category C'] {F G M N : AbFunctor C} {α : M ⟶ N} {X E : C ⥤ Type 1} (φ : C' ⥤ C) {F' N' : AbFunctor C'} {c : Comparison F F'}
lemma surjective_and_dies_of_quotient_sieve {A} {R : Subfunctor (reprBy A)} [φ.Full] [φ.Faithful] {b} (q : φ A ⟶ b) (r : ∀ {d} f, ⟨f⟩ ∈ R d → ∃! g, q ≫ g = φ.map f) (z : ∀ {d} f g, q ≫ g = φ.map f → ⟨f⟩ ∈ R d) (h : IsAcyclicAt φ F b) : (Surjective (F.map q) → ∀ n, Surjective (H.map (φ ⋙ F) (freeAb.map R.ι) n)) ∧ ∀ x, (∀ d f, ⟨f⟩ ∈ R d → (φ ⋙ F).map f x = 0) → F.map q x = 0 := have ⟨B, _⟩ := isBijective_reprBy_iff.1 h
  let v : φ ⋙ reprBy b ⟶ R.toFunctor := ⟨fun d ↦ ↾(⟨_, z _ ·.1 (φ.map_preimage _).symm⟩), by
    intros; ext; simp [reprBy, reprFunctor, ← Category.assoc]⟩
  ⟨fun k n ↦ .of_comp_left (by cases n; exacts [addEquiv₀.forall_congr_left.2 ((B.2.comp k).forall.2
    (⟨mk₀ <| (homReprEquiv ..).symm ·, by
    simp [H.map]; congr; use freeAb.hom_ext fun _ _ ↦ congr($(by simp [v, uliftCoyonedaEquiv]) + 0)⟩)), surjective_to_subsingleton _]) (IsCohomEquiv.of_bijective (p := v) (fun _ ↦ .of_existsUnique _ ((Equiv.ulift.existsUnique_congr (by aesop)).2 <| r _ ·.2)) n).1, fun _ k ↦ B.1 (freeAb.hom_ext (by rw [homOfValue_app]; simpa using k _ _ <| v · · |>.2))⟩
def sectionLift (q : (φ ⋙ X).sections) : C' ⥤ X.Elements := .mk (X.elementsMk _ <| q.1 ·) (⟨_, q.2 ·⟩)
def sectionMap (q : X.sections) : pointFunctor C ⟶ X := X.sectionsEquivHom _ q
abbrev elementsProj (X : C ⥤ Type 1) := π X
lemma Comparison.HasUnivPoints.on_elements {E'} {u : E' ⟶ _} (h : c.HasUnivPoints u) : HasUnivPoints (F := _root_.elementsProj X ⋙ F) ⟨Functor.Elements.precomp _ X, (_root_.elementsProj _).whiskerLeft c.coeffHom⟩ (Y := _root_.elementsProj X ⋙ E) ((_root_.elementsProj _).whiskerLeft u) := (h ·.1 · |>.elim fun b ⟨x, s, e, k, B⟩ ↦ ⟨(c.φ ⋙ X).elementsMk b _, x, ⟨s, rfl⟩, e, fun _ w f l ↦ (k _ w f.1 l).elim fun g m _ ↦ ⟨⟨g, X.map_comp_apply .. ▸ m.2 ▸ f.2⟩, by bound⟩, B⟩)
lemma hasUnivPoints_reprBy_elements (a : E.Elements) : HasUnivPoints (.restrict (elementsProj E) G) (Y := reprBy a.1) (Y' := reprBy a) {app _ := ↾(⟨·.1.1⟩)} := (⟨E.elementsMk · _, ⟨⟨·.1, rfl⟩⟩, 𝟙 _, by aesop, by rintro _ ⟨_, e⟩ f ⟨⟩; use ⟨f, E.map_comp_apply .. ▸ e⟩; aesop, by simpa using! bijective_id⟩)
def tautSection : pointFunctor _ ⟶ elementsProj X ⋙ X := sectionMap ⟨_, (·.2)⟩
lemma hasUnivPoints_elements : HasUnivPoints (.restrict (elementsProj X) G) tautSection := (⟨X.elementsMk · ·, ⟨⟩, 𝟙 _, by aesop, fun _ _ ↦ (⟨⟨·, ·.symm⟩, by aesop⟩), by simpa using! bijective_id⟩)
lemma isBijective_relFreeAb_taut U : IsBijective (.restrict (elementsProj X) G) (N := _root_.relFreeAb U) (relFreeAb.map (U := U.whisker _) tautSection le_rfl) := ((pull_hom_contravariant (relFreeAb.shortExact U).2 (relFreeAb.shortExact _).2 _ ⟨_, _, _, freeAb.hom_ext, rfl⟩).five_lemma (hasUnivPoints_elements.bijSub _)).1 hasUnivPoints_elements.isBijective
lemma bijective_total_iff_isBijective {α : N' ⟶ c.φ ⋙ N} : (Bijective fun x ↦ pullbackAlong α (.mapThenComp (restrictAlong _) (.homClass c.coeffHom) x)) ↔ c.IsBijective α := congr(Bijective $(show AddMonoidHom.comp .. = _ by
    ext; simp [mapThenComp, pull]; erw [map_of, of_comp_homClass, homClass_comp_of])).to_iff.trans
  (.trans (.and (DirectSum.map_injective _) (DirectSum.map_surjective _)) forall_and.symm)
alias ⟨_, Comparison.IsBijective.bijective_totalH⟩ := bijective_total_iff_isBijective
def sliceEquiv : TotalH (abTensor N (freeAb X)) F ≃+ TotalH (elementsProj X ⋙ N) (elementsProj X ⋙ F) := .ofBijective ((TotalH.comp _).comp (map (restrictAlong _))) (by simpa [mapThenComp] using! IsBijective.bijective_totalH ((devissage (.restrict ..) (abTensor.flip (freeAb X)) ((restrictAlong _).whiskerLeft (tensorPoint (freeAbMap tautSection)))).bijective_of_sigma_repr (fun _ _ ↦ (IsCohomEquiv.of_isIso (freeAb.prod ..)).bij.trans (hasUnivPoints_elements.bijPb (v := lift (𝟙 _) (toUnit _ ≫ tautSection)) (toUnit (_ ⋙ sigma _)) (snd ..) (isPullback_iff.2 ⟨by tauto, fun _ _ _ ↦ (⟨_, ⟨rfl, Prod.ext rfl ·.symm⟩, by bound⟩)⟩))) N))
variable (A : Type) [CommRing A]
class InvertsPrime (ℓ : outParam ℕ) extends ThePrime ℓ, IsAICLocal A where isUnit_prime : IsUnit (ℓ : A)
abbrev TestOver := @FullSubcategory (CommAlg A) _ (IsTest ·)
def TestOver.toTest : TestOver A ⥤ TestRing := lift _ (ι _ ⋙ forget₂ ..) (·.2)
variable {A}
abbrev locConstAlong {ℓ} (g : C ⥤ TestOver A) [InvertsPrime A ℓ] := g ⋙ TestOver.toTest A ⋙ locConstCoeff ⟨ZMod ℓ⟩
variable {ℓ} [InvertsPrime A ℓ] (g : C ⥤ TestOver A) (ι : C ⥤ CommRingCat.{0})
abbrev ringOf := g ⋙ TestOver.toTest A ⋙ testIncl
structure TorsionCoeff [InvertsPrime A ℓ] where
  F : AbFunctor C
  killed c (x : F c) : ℓ • x = 0
  zariski_descent : HasZariskiDescent (ringOf g) F
structure IdealFamily where
  I c : Ideal (ι c)
  map_eq {a b} f : (I a).map (ι.map f).hom = I b
def killingMaps {c} (I : Ideal (ι c)) : Subfunctor (reprFunctor ⟨c⟩) := ⟨fun _ ↦ {f | I.map (ι.map f.1).hom = ⊥}, by simp_all [reprFunctor, ← I.map_map]⟩
structure Theory extends TorsionCoeff g where
  restrict_surjective c I n : Surjective (H.map F (freeAb.map (@killingMaps _ _ (ringOf g) c I).ι) n)
  dies_near c I x : (∀ d f, ⟨f⟩ ∈ killingMaps _ I d → F.map f x = 0) → ∀ m, m.IsMaximal → I ≤ m → ∃ a ∉ m, ∀ d f, IsUnit ((ringOf g).map f a) → @F.map c d f x = 0
variable {g ι} (I : IdealFamily ι) (G)
def IdealFamily.whisker φ : @IdealFamily C' _ (φ ⋙ ι) := ⟨_, fun _ ↦ I.2 _⟩
def IdealFamily.botLocus : Subfunctor (pointFunctor C) := ⟨({_x | I.I · = ⊥}), (by simp_all [← I.2 ·])⟩
def IdealFamily.topLocus : Subfunctor (pointFunctor C) := ⟨({_x | I.I · = ⊤}), (by grind [I.2 ·, Ideal.map_top])⟩
lemma IdealFamily.exists_notMem_eq_top {c m} (h : ¬I.I c ≤ m) : ∃ a ∉ m, ∀ d f, IsUnit (@ι.map c d f a) → I.I d = ⊤ := (Set.not_subset.1 h).imp fun _ ⟨a, b⟩ ↦ ⟨b, (eq_top_of_isUnit_mem _ <| @I.2 c · · ▸ mem_map_of_mem _ a)⟩
def IdealFamily.zerosCoeff : AbFunctor C := .mk (fun c ↦ .of (_ ⧸ AddSubgroup.ofSub {x | ∀ d f, I.I d = ⊥ → @G.map c d f x = 0} ⟨0, by simp⟩ (by simp_all))) fun f ↦ ofHom (QuotientAddGroup.map _ _ (G.map f).hom fun _ ↦ (by simpa using · · <| f ≫ ·))
def IdealFamily.toZerosCoeff : G ⟶ I.zerosCoeff G where app _ := ofHom (mk' _)
lemma IdealFamily.bijective_toZerosCoeff d (h : I.I d = ⊥) : Bijective (I.toZerosCoeff G d) := ⟨fun _ _ ↦ (by simpa using eq_iff_sub_mem.1 · d (𝟙 _) h), mk_surjective⟩
lemma IsCohomDense.isCohomEquiv_of_bijective_on {V} (h : @IsCohomDense C _ (pointFunctor C) F V) (k : ∀ c, ⟨⟩ ∈ V c → Bijective (α c)) : IsCohomEquiv F α := LocalIso.isCohomEquiv (by
  constructor <;> intros <;> apply h.of_preimage_le (toUnit _) <;> intro _ _ h
  exacts [(k _ h).1 (α.naturality_apply .. ▸ by aesop), (eq_zero_iff _).2 ((k _ h).2 _)])
lemma TestOver.exists_quotient B I : ∃ D π, RingHom.ker ((ringOf (𝟭 (TestOver A))).map (π : B ⟶ D)).hom = radical I ∧ Surjective π.1.1 ∧ (∀ E f, ⟨f⟩ ∈ killingMaps _ I E → ∃! k, π ≫ k = f) ∧ I.map π.1.1 = ⊥ := ⟨⟨_, B.2.quotient (by aesop_cat)⟩, ⟨ofHom (Quotient.mkₐ ..)⟩, mk_ker, mk_surjective, fun E f k ↦ ⟨⟨ofHom
  (Quotient.liftₐ _ _ fun _ ⟨n, h⟩ ↦ E.2.3.1 _ ⟨n, by simpa using! le_comap_of_map_le k.le h⟩)⟩, rfl, by rintro _ ⟨⟩; ext ⟨⟩; rfl⟩, map_mk_eq_bot_of_le le_radical⟩
lemma lcC {c} (s : locConstAlong g c) P : ∃ a ∉ P.1, ∀ d f, IsUnit ((ringOf g).map (Y := d) f a) → (locConstAlong g).map f s = ⟨.const _ (s.1.1 P)⟩ := have ⟨_, e⟩ := s.1.2 {_}
  (Set.not_subset.1 (e.le · rfl)).imp fun _ h ↦ ⟨h.2, fun _ _ u ↦ congr(⟨⟨$(funext (of_not_not <| mt (e.ge · h.1) <| ·.1.notMem_of_isUnit u)), _⟩⟩)⟩
def Theory.locallyConstant : Theory (𝟭 (TestOver A)) := ⟨⟨locConstAlong .., fun _ _ ↦ congr(⟨⟨$(by aesop), _⟩⟩), HasPartitions.hasZariskiDescent ⟨fun B e ↦ (fun _ _ ↦ by peel B.exists_quotient (span {e}); aesop (add simp [IsIdemQuotient, killingMaps])) ∘ B.2.radIdem, fun _ _ ↦ by apply hasPartitions_locConstCoeff.2⟩ (𝟙 _) (by simp) (·.2.2)⟩, fun B I ↦ (B.exists_quotient I).elim fun _ ⟨π, _, k, u, z⟩ ↦ (surjective_and_dies_of_quotient_sieve
  (𝟭 _) π @u (fun | _, g, rfl => (killingMaps ..).2 g z) (IsCohomEquiv.of_isIso _).bij).1 (ULift.map_surjective.2 (locConst_comap_surjective _ (B.2.isComparableRing_of_associated (k.forall.2 (⟨·, .rfl⟩))))), fun B I s h m M e ↦ (lcC s (.comap _ ⊥)).imp fun _ ↦ .imp (mk_ker.ge ·).mt (· · · · |>.trans congr(⟨.const _ ($(h ⟨_, B.2.quotient M.isPrime.isRadical⟩ ⟨ofHom (Quotient.mkₐ ..)⟩ (map_mk_eq_bot_of_le e)).1.1 _)⟩))⟩
variable (Θ : Theory g) (I : IdealFamily (ringOf g)) (M : TorsionCoeff g)
def oneLocConst : freeAb (pointFunctor C) ⟶ locConstAlong g := freeAb.desc (fun _ _ ↦ ⟨.const _ 1⟩) (by tauto)
protected def TorsionCoeff.onElements : TorsionCoeff (elementsProj X ⋙ g) := ⟨_, (M.killed ·.1), fun Y U k a y ↦ ((hasUnivPoints_reprBy_elements a).isCohomEquiv_incl_iff ⟨fun b ↦ {f | ⟨⟨_, rfl⟩⟩ ∈ U.preimage (pointMap y) (X.elementsMk b (X.map f.1 a.2))}, fun g _ ↦ ((U.preimage _).2 (Functor.Elements.homMk (y := X.elementsMk _ _) g (by simp [reprBy, reprFunctor])) ·)⟩
  (by ext @⟨d, x⟩ ⟨_ : _ ⟶ d, rfl : X.map _ _ = x⟩; rfl)).1
  (IsCohomDense.isCohomEquiv (M.zariski_descent fun b f ↦ (k (X.elementsMk b (X.map f.1 a.2)) (Y.map ⟨_, rfl⟩ y) · · |>.imp fun _ ↦ .imp_right fun h b f ↦ congr($(Y.4 ..) _ ∈ _).ge ∘ h (X.elementsMk b _) ⟨f, by simp [reprBy, reprFunctor]⟩)))⟩
def Theory.onElements : Theory (_root_.elementsProj X ⋙ g) := ⟨.onElements _, fun a I n ↦ (((hasUnivPoints_reprBy_elements a).bijSub ..).2.comp (Θ.restrict_surjective _ I n)).forall.2 (⟨Equiv.ofBijective _ ((hasUnivPoints_reprBy_elements a).isBijective n) ·, map_pull_eq_pull_map ..⟩), fun a I x h ↦ by peel Θ.dies_near _ I x (fun b f ↦ h (X.elementsMk b (X.map f _)) ⟨_, rfl⟩); tauto⟩
lemma Theory.isLocallyEverything_ker_toZerosCoeff : IsLocallyEverything (ringOf g) (zSec (kerComplex (I.toZerosCoeff Θ.F)).X₁ ⊔ I.topLocus.preimage (toUnit _)) := fun c x m M ↦ by_cases (by peel Θ.dies_near c _ _ ((eq_zero_iff _).1 x.2 · · <| I.2 _ ▸ ·) m M; aesop (add simp kerComplex)) (.imp (by tauto) ∘ I.exists_notMem_eq_top)
lemma Theory.isCohomDense_botLocus : IsCohomDense (I.zerosCoeff Θ.F) I.botLocus := fun c y n ↦ ⟨n.casesOn (.of_ker _ ((addEquiv₀.trans (homReprEquiv ..)).forall_congr_left.2 (by
  rintro ⟨⟩ e; simp_all [H.map]; use (eq_zero_iff _).2 fun d f h ↦ (I.bijective_toZerosCoeff _ d h).1 ((add_zero _).symm.trans congr($e d (.of ⟨_, h⟩)))))) (by cat_disch), ((pushBij _ (I.bijective_toZerosCoeff _ · ∘ prop) n).2.comp
  (by convert Θ.restrict_surjective c (I.I c) n <;> simp_rw [killingMaps, I.2] <;> rfl)).forall.2
  (⟨_, map_push _ _ ·⟩)⟩
def Theory.onZeros : TorsionCoeff g := ⟨_, (Quot.ind <| congrArg _ ∘' Θ.killed ·), fun _ _ hU ↦ ((Θ.isCohomDense_botLocus I).preimage (toUnit _)).trans fun _ z n ↦ (fun b ↦ (bijective_iff_of_comm_sq (map_push _ _) (pushBij _ b n) (pushBij _ (b · ∘ val) n)).1 (Θ.zariski_descent hU ..)) (I.bijective_toZerosCoeff _ _ <| pointMap z · · |>.2)⟩
lemma TorsionCoeff.nsmul_totalH_eq_zero (y : TotalH N M.F) : ℓ • y = 0 := let := CoeffAction.mk (.id (End M.F))
  smul_one_smul (End M.F) ℓ y ▸ smul_eq_zero_of_left (End.ext (by bound [M.killed])) y
variable [NeZero ℓ] [HasFlatValues N]
lemma shortExact_nsmul_abCoker : ∃ w, ShortComplex.ShortExact ⟨ℓ • 𝟙 N, abCoker.π (ℓ • 𝟙 N), w⟩ := have := @HasFlatValues.flat
  shortExact_of_app (fun _ ↦ (HasUniqueDiv.of_isTorsionFree ℤ _).1 NeZero.out) (fun _ ↦ eq_zero_iff) fun _ ↦ mk_surjective
lemma TorsionCoeff.comp_abCoker_surjective : Surjective (pullbackAlong (G := M.F) (abCoker.π (ℓ • 𝟙 N))) := ((exact_triangle shortExact_nsmul_abCoker.2 _).1 · |>.1 (by
  simp_rw [pullbackAlong, TotalH.homClass, ← addEquiv₀_symm_apply, map_nsmul]; apply M.nsmul_totalH_eq_zero))
def IdealFamily.constToZeros : abCoker (ℓ • 𝟙 (_root_.relFreeAb I.topLocus)) ⟶ zerosCoeff (locConstAlong g) I := abCoker.desc (abCoker.desc (oneLocConst ≫ I.toZerosCoeff _) (freeAb.hom_ext fun _ u ↦ (eq_zero_iff _).2 fun _ f e ↦ congr(⟨$(funext (·.2.1.elim (eq_top_mono bot_le (e ▸ I.topLocus.2 f u.2)))), _⟩))) (relFreeAb.hom_ext fun _ _ ↦ congr(⟦$(by rw [map_nsmul, Theory.locallyConstant.killed])⟧))
omit [NeZero ℓ] in
lemma IdealFamily.isCohomEquiv_constToZeros (e : Θ.F = locConstAlong g) (hF : HasZariskiDescent (ringOf (φ ⋙ g)) F') : IsCohomEquiv F' (φ.whiskerLeft I.constToZeros) := have a c (n : ℤ) : I.constToZeros c ⟦n • relFreeAb.mk I.topLocus ⟨⟩⟧ = ⟦⟨.const _ n⟩⟧ := congr(⟦$(by erw [map_zsmul, freeAb.desc_of, ← zsmul_one]; rfl)⟧)
  LocalIso.isCohomEquiv ⟨fun c ↦ Quot.ind ((Surjective.forall (relFreeAb.mem_of_mk_mem (.zmultiples _) (by simp))).2 fun n k ↦ (hF ((e ▸ Θ.isLocallyEverything_ker_toZerosCoeff I :).whisker
    φ)).of_preimage_le (pointMap ⟨_, a .. ▸ k⟩) fun B f u ↦ by_cases (congr(⟦$(relFreeAb.mem_of_mk_mem (s := _) ⊥ fun _ ↦ relFreeAb.mk_eq_zero ·)⟧)) fun k ↦ by
    obtain ⟨r, rfl⟩ := (exists_le_maximal _ k).elim ((CharP.intCast_eq_zero_iff ..).1
      congr($(u.resolve_right k).1.1.1 ⟨·, ·.1.isPrime⟩))
    use (eq_zero_iff _).2 ⟨_, by simp [mul_smul]; rfl⟩), fun c t ↦ (hF (by
    rintro _ ⟨⟨⟩⟩ m M; peel lcC ‹_› ⟨m, M.isPrime⟩; use (eq_zero_iff _).2 ⟨_, by erw [a, ZMod.coe_valMinAbs, ← this]; rfl⟩)).preimage _⟩
lemma TorsionCoeff.comp_oneLocConst_surjective : Surjective (@pullbackAlong _ _ _ (locConstAlong g) M.F oneLocConst) := let I := IdealFamily.mk ⊥ (by simp); (((isCohomEquiv_quotient_of_acyclic
    (relFreeAb.shortExact (I.whisker g).topLocus).2 fun n _ ↦ ((M.zariski_descent (U := ⊥) fun _ y _ ↦ (·.1.1.elim (eq_top_mono bot_le (prop y)))).isCohomEquiv n).1 ((subsingleton_of_id_eq_zero (freeAb.hom_ext nofun) ..).1 ..)).bijective_totalH.2.comp M.comp_abCoker_surjective).comp (I.isCohomEquiv_constToZeros g .locallyConstant rfl M.zariski_descent).bijective_totalH.2).forall.2 (⟨pullbackAlong (g.whiskerLeft (I.toZerosCoeff _)) ·, .symm (by simp [homClass_comp_homClass_comp]; apply homClass_comp_homClass_comp)⟩)
open ExteriorAlgebra CliffordAlgebra
variable {T T' M M' : Type} [CommRing T] [CommRing T'] [AddCommGroup M] [AddCommGroup M'] [Module T M] [Module T' M'] {a : T →+* T'} (φ : M →ₛₗ[a] T' × M')
attribute [local simp] Algebra.algebraMap_eq_smul_one mul_add add_mul sub_mul mul_assoc
lemma algebraMapInv_exteriorMap (m : M →ₛₗ[a] M') x : algebraMapInv (exteriorMap m x) = a (algebraMapInv x) := by induction x using left_induction <;> simp_all [algebraMapInv]
def contraction : ExteriorAlgebra T M →ₛₗ[a] ExteriorAlgebra T' M' := ⟨⟨ExteriorAlgebra.map (.snd ..) ∘ contractLeft (.fst ..) ∘ exteriorMap φ, by simp⟩, by simp⟩
@[simp] lemma contraction_one : contraction φ 1 = 0 := by simp [contraction]
abbrev exteriorMapSnd := exteriorMap (.snd .. ∘ₛₗ φ)
@[simp] lemma contraction_iota_mul m x : contraction φ (ExteriorAlgebra.ι T m * x) = (φ m).1 • exteriorMapSnd φ x - ExteriorAlgebra.ι T' (φ m).2 * contraction φ x := by simp [contraction, contractLeft_ι_mul]; congr 1; induction x using left_induction <;> simp_all
lemma contraction_mul {s : _ →ₗ[_] _} (h : ∀ m, s m = -m) x y : contraction φ (x * y) = exteriorMap s (exteriorMapSnd φ x) * contraction φ y + contraction φ x * exteriorMapSnd φ y := by induction x using left_induction <;> simp_all <;> abel
