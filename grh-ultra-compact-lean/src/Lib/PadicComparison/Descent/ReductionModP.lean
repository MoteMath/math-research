import Lib.General.Geometry.LocalTerms
import Lib.General.Algebra.MultivariateHensel
import Lib.PadicHodge.PeriodRings.ThetaKernel
section
open CategoryTheory ObjectProperty Ideal Nat Finset
variable {p} [ThePrime p] (S) [CommRing.{0} S] {B k} [CommRing B] [CommRing k] (f : B →+* k)
def pdIdeal : Ideal S := ⟨⟨⟨{x | ∀ n, ↑n ! ∣ x ^ n}, fun a b n ↦ @add_pow .. ▸ dvd_sum (by grw [← a ·, ← b _, ← choose_mul_factorial_mul_factorial <| mem_range_succ_iff.1 ·, mul_rotate]; simp)⟩, by rintro ⟨⟩ <;> simp⟩, by simp_all [mul_pow, Dvd.dvd.mul_left]⟩
lemma pdIdeal_le_comap : pdIdeal B ≤ comap f (pdIdeal k) := fun _ ↦ (by simpa using map_dvd f <| · ·)
abbrev pdQuotientMk := Ideal.Quotient.mk (pdIdeal S)
abbrev pdQuotientMap := quotientMap _ f (pdIdeal_le_comap f)
structure IsCompleteTorsionFree [ThePrime p] where
  (regular : IsSMulRegular S p) complete : IsAdicComplete (span {(p : S)}) S
abbrev CrysTest := @FullSubcategory (CommAlg S) _ (IsCompleteTorsionFree ·)
def pdReduction (r : k →+* B ⧸ pdIdeal B) : CrysTest B ⥤ CommAlg k := by
  let (A : CrysTest B) := ((pdQuotientMap (algebraMap _ A.1)).comp r).toAlgebra
  refine ⟨(.of _ <| ·.1.1 ⧸ _), fun f ↦ ConcreteCategory.ofHom ⟨pdQuotientMap _, (by
  simp [algebraMap]; rcases r ·; exact congr($(f.1.1.2 _)))⟩, ?_, ?_⟩ <;> intros <;> ext ⟨⟩ <;> rfl
def CrysTest.restrictScalars [Algebra S B] : CrysTest B ⥤ CrysTest S :=
  lift _ (ι _ ⋙ restrictAlg ..) (·.2)
abbrev PadicCompletion (p : ℕ) := AdicCompletion (span {(p : S)}) S
lemma isCompleteTorsionFree_completion (h : IsSMulRegular B p) : IsCompleteTorsionFree (PadicCompletion B p) := ⟨isSMulRegular_completion h, isAdicComplete⟩
end
noncomputable section
open CategoryTheory Functor CommAlgCat TensorProduct Ideal AdicCompletion WittVector ModuleCat H
variable {C C'} [Category C] [Category C'] {S : Type} [CommRing S] (p) [ThePrime p] (T M : Type) [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M] (m : M) (φ : C' ⥤ C) (N : AbFunctor C) (Φ : C ⥤ ModuleCat S)
abbrev asModules (Φ : C ⥤ CommAlg S) := Φ ⋙ forget₂ .. ⋙ forget₂ (AlgCat S) (ModuleCat S)
def tensorWith : ModuleCat.{0} S ⥤ ModuleCat T := .mk _ (ofHom <| AlgebraTensorModule.lTensor T M ·.hom)
instance : (tensorWith (S := S) T M).Additive := ⟨Hom.ext (map_add ..)⟩
variable {M} in
def tensorWith.mk : moduleCoeff Φ ⟶ moduleCoeff (Φ ⋙ tensorWith T M) := whiskerRight {app A := AddCommGrpCat.ofHom (TensorProduct.mk S M (Φ A) m).toAddMonoidHom} _
def baseChangeMap n : M ⊗[S] H N (moduleCoeff Φ) n →ₗ[T] H N (moduleCoeff (Φ ⋙ tensorWith T M)) n := by
  use (liftAddHom ((pushHom ..).comp (.mk' (tensorWith.mk T · Φ) ?_)) fun (s : S) m ↦ (congr(push N $(?_) n ·).trans (push_comp ..))).toAddHom,
    fun t x ↦ by induction x <;> simp_all; exact .symm (push_comp ..).symm
  all_goals intros; ext; apply_rules [ULift.ext, add_tmul, smul_tmul]
def FP := ∀ S T M [CommRing S] [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M] [Module.Flat S M] (Φ : C ⥤ ModuleCat S) n, (⇑(baseChangeMap T M N Φ n)).Bijective
variable {Φ}
def coeffMap {Ψ} (β : Φ ⟶ Ψ) : moduleCoeff Φ ⟶ moduleCoeff Ψ := by apply_rules [whiskerRight]
abbrev Comparison.ofModuleHom {Φ'} (β : φ ⋙ Φ ⟶ Φ') := of (F := moduleCoeff Φ) _ (coeffMap β)
abbrev Comparison.restrict := of φ (𝟙 (φ ⋙ N))
def algBaseChange : CommAlg S ⥤ CommAlg T := .mk _ (ofHom <| Algebra.TensorProduct.lTensor T ·.1)
instance not_isUnit_p [Nontrivial S] [IsAdicComplete (span {(p : S)}) S] : Fact ¬IsUnit (p : S) := ⟨zero_ne_one ∘ eq_of_forall_pow_dvd_sub _ ∘ (·.pow · |>.dvd)⟩
variable (S) [Algebra Ainf T]
class IsCell extends IsDomain T, ValuationRing T, IsAdicComplete (span {(p : T)}) T, IsAIC T where
  p_ne_zero : (p : T) ≠ 0
structure PadicTest {p} [ThePrime p] where
  Index : Type
  Cell : Index → _
  [nonempty : Nonempty Index]
  [commRing (i) : CommRing (Cell i)]
  [isCell (i) : IsCell p (Cell i)]
  structureMap : OC →+* ∀ i, Cell i
namespace PadicTest
variable {p} (c : PadicTest)
attribute [instance] nonempty commRing isCell
abbrev ProdRing := ∀ i, c.Cell i
instance : Algebra OC c.ProdRing := c.structureMap.toAlgebra
instance : Category PadicTest := {Hom := (·.ProdRing →ₐ[OC] ·.ProdRing), id c := .id .., comp f := (·.comp f)}
instance : Nontrivial c.ProdRing := Pi.nontrivial_at c.nonempty.some
instance isAdicComplete_prodRing : IsAdicComplete (span {(p : c.ProdRing)}) c.ProdRing := by refine {haus' x h := funext (c.isCell · |>.haus _ ?_), prec' f h := (Classical.skolem.1 (c.isCell · |>.prec' (f · _) ?_)).imp ?_} <;> simp_all [↓smodEq_span_pow_iff_dvd, pi_dvd_iff]
abbrev TiltRing := PreTilt c.ProdRing p
instance : Algebra OFlat c.TiltRing := (tiltMap c.structureMap).toAlgebra
def twist (g : Gp p) : PadicTest ⥤ PadicTest := .mk (⟨_, _, ·.structureMap.comp (MulSemiringAction.toRingHom _ _ g)⟩) (⟨_, ·.2 ∘' _⟩)
def algFunctor : PadicTest ⥤ CommAlg OC := .mk _ ofHom
abbrev ringFunctor := algFunctor ⋙ forget₂ _ CommRingCat
def tilt : PadicTest ⥤ CommAlg OFlat := ⟨_, fun f ↦ ofHom ⟨_, (f.comp_algebraMap ▸ tiltMap_comp _ _ · |>.symm)⟩, by intro; ext; apply tiltMap_id, by intros; ext; apply tiltMap_comp⟩
end PadicTest
open PadicTest Int PrimeSpectrum Function Module LinearMap Flat Ainf AlgebraTensorModule LocallyConstant Nat ZMod IsSMulRegular AlgebraicGeometry.StructureSheaf
def algCompletion : CommAlg S ⥤ CommAlg S := by
  refine ⟨_, (ofHom ⟨adicMap (I := span {↑p}) ·.hom.1 (by simp), ?_⟩), ?_, ?_⟩ <;> intros <;>
    (try ext x : 2; cases x using induction_on) <;> apply ext_evalₐ <;> simp
variable {p S}
instance : IsCell p OC := ⟨NeZero.out⟩
instance : Algebra Ainf OFlat := constantCoeff.toAlgebra
instance : Algebra Ainf OC := (fontaineTheta ..).toAlgebra
def wittFunctor {k} [CommRing k] (S := WittVector p k) [CommRing S] [Algebra S (WittVector p k)] : CommAlg k ⥤ CommAlg S := .mk (fun b ↦ @of _ _ _ _ ((WittVector.map b.3.2).comp ‹Algebra ..›.2).toAlgebra) fun f ↦ by use WittVector.map f.hom; intro; ext; apply f.1.2
abbrev periodAlg := wittFunctor (k := OFlat) ⋙ algBaseChange T ⋙ algCompletion T p
def testPoints {R : CommRingCat} [Algebra R OC] := algPoints R R ⋙ restrictAlong (algFunctor ⋙ restrictAlg ..)
lemma exists_compatible_roots [h : IsAIC S] x : ∃ χ : ℚ →+ Additive Sˣ, χ 1 = x :=
  have := @AddGroup.divisibleByIntOfDivisibleByNat _ _ (divisibleByOfSMulRightSurj (Additive _) _ fun k y ↦ (@h.exists_pow_eq _ _ _ ⟨k⟩ _).rec (⟨.ofPow _ · k ·, Units.ext ‹_›⟩))
  ((Module.Baer.of_divisible _).extension_property_addMonoidHom (castAddHom ℚ) Int.cast_injective (zmultiplesHom _ x)).imp (by simp [AddMonoidHom.ext_int_iff])
variable (M S : _) {S' Λ} [CommRing M] [CommRing S] [CommRing S'] [Algebra M S] [AddCommGroup Λ] {f : S →+* S'} {p : _} [ThePrime p]
lemma exists_ringHom_of_locallyConstant : ∃ f : LocallyConstant (PrimeSpectrum S) M →+* S, ∀ x q, algebraMap _ (Localization.AtPrime q.1) (f x) = algebraMap _ _ (x q) := let e := globalSectionsIso S
  ⟨e.2.1.comp (.codRestrict (.pi ((algebraMap M (Localization _)).comp <| evalRingHom ·.1)) (sectionsSubalgebra ..) fun x ↦ (⟨⟨_, x.2 {x ·.1}⟩, rfl, default, _, 1, (⟨_, congrArg (algebraMap ..) ·.2⟩)⟩)), fun _ q ↦ congrArg (·.1 ⟨q, ⟨⟩⟩) (e.inv_hom_id_apply _)⟩
lemma locConst_comap_surjective (h : IsComparableRing f) : Surjective (comapAddMonoidHom (Z := Λ) ⟨_, continuous_comap f⟩) := locallyConstant_mem_of_indicator (S := AddMonoidHom.range _) fun a y i ↦ (h y (1 - y)).elim fun e ⟨j, k⟩ ↦ ⟨indicator (LocallyConstant.const _ a) (isClopen_iff.2 ⟨e, j, rfl⟩), (by grind [dvd_def, i.eq] : f e = y) ▸ rfl⟩
def locConstAlg : CommRingCat ⥤ CommAlg (ZMod p) := .mk _ (CommAlgCat.ofHom <| comapₐ (Z := ZMod p) _ ⟨_, continuous_comap ·.hom⟩)
instance : Algebra (ZMod p) OFlat := ZMod.algebra ..
deriving instance Algebra (ZMod p), IsScalarTower (ZMod p) OFlat for @CFlat p _
instance perfectRing_locConstAlg A : PerfectRing (locConstAlg A) p := ⟨by convert bijective_id; exact LocallyConstant.ext fun _ ↦ pow_card _⟩
def pFlat := constantCoeff xi
abbrev IsPerfectTorsionFree (b : CommAlg OFlat) := PerfectRing b p ∧ IsSMulRegular b pFlat
def IsReductionMod {R A B} [SMul R A] [Zero B] (m : R) (f : A → B) := Surjective f ∧ Exact (m • ·) f
lemma witt_reduction_spec [IsDomain M] [CharP M p] [PerfectRing S p] : IsReductionMod p (@constantCoeff p S _ _) ∧ IsCompleteTorsionFree (WittVector p S) ∧ RingHom.ker (@constantCoeff p S ..) = span {↑p} ∧ ∀ k x, (∀ i < k, @coeff p S x i = 0) ↔ ∃ y, p ^ k • y = x := by
  by_cases! Subsingleton S <;> [have : Subsingleton (WittVector p S) := ⟨by cat_disch⟩;
    have := CharP.of_ringHom_of_ne_zero (algebraMap M S) p NeZero.out] <;> use ⟨by tauto, ?_⟩,
    ⟨.of_right_eq_zero_of_smul ?_, {}⟩ <;> simp [mem_span_p_pow_iff_le_coeff_eq_zero, mul_comm, Exact, ← mem_span_singleton', nontriviality, ← ker_constantCoeff]
  apply eq_zero_of_p_mul_eq_zero
variable {S M M' L : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M'] [AddCommGroup L] [Module S L] (f : M →ₗ[S] M') {m : ℕ}
lemma pFlat_ne_zero : pFlat ≠ 0 := not_p_dvd_xi ∘ Witt.p_dvd_iff.2
lemma not_isUnit_pFlat : ¬IsUnit pFlat := prime_xi.not_isUnit ∘ Ainf.isUnit_iff_isUnit_constantCoeff.2
lemma IsReductionMod.lTensor (h : IsReductionMod m f) : IsReductionMod m (f.lTensor L) := ⟨lTensor_surjective _ h.1, congr(Exact $(map_natCast (End.lTensorAlgHom ..) m) _).mp (lTensor_exact L h.2 h.1)⟩
lemma IsReductionMod.bijective_rTensor (h : IsReductionMod m f) (z : ∀ y : L, m • y = 0) : Bijective (f.rTensor L) := ⟨(injective_iff_eq_zero_of_exact (rTensor_exact L (f := m.cast) h.2 h.1)).2 (ext' (by simp_all [smul_tmul])), rTensor_surjective L h.1⟩
lemma tmul_ext {P F} [AddCommGroup P] [FunLike F (M ⊗[S] L) P] [AddMonoidHomClass F ..] {f g : F} (h : ∀ m x, f (m ⊗ₜ x) = g (m ⊗ₜ x) := by tauto) : f = g := DFunLike.ext _ _ (by induction · with simp_all)
instance [IsDomain S] [IsBezout S] [IsTorsionFree S L] : Flat S L := flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)
lemma isTorsionFree_of_dvd_pow [IsDomain S] {π : S} (h : IsSMulRegular L π) (ha : ∀ {t}, t ≠ 0 → ∃ n, t ∣ π ^ n) : IsTorsionFree S L := ⟨(by grind [mul_iff, !h.pow, dvd_def, @ha · ·.ne_zero])⟩
lemma isSMulRegular_tensor_of_flat_mod {O : Type} [CommRing O] [Algebra S O] [Module O M'] [IsScalarTower S O M'] [Flat O M'] (hO : IsReductionMod m (Algebra.linearMap S O)) (hf : IsReductionMod m f) (hM : IsSMulRegular M m) (hN : IsSMulRegular L m) : IsSMulRegular (L ⊗[S] M) m := by
  simp [IsReductionMod, ← cast_smul_eq_nsmul S, IsSMulRegular] at *
  obtain ⟨q, e, t, l⟩ := Finsupp.linearCombination_id_surjective S L, @exact_subtype_ker_map,
   @lTensor_injective_of_exact_of_exact_of_rTensor_injective, @lTensor_preserves_injective_linearMap
  apply congr(⇑$(lTensor_smul_action ..)).subst (t (e _) q hf.2 hf.1 _ (l _ hM))
  simpa [← lTensor_inj_iff_rTensor_inj] using! congr(⇑$(lTensor_comp_cancelBaseChange _ O ..)).symm.subst ((cancelBaseChange ..).injective.comp (l _ (t (f₁ := mul S S m) hO.2 hO.1 (e _) q (lTensor _ hN) (by simp))))
