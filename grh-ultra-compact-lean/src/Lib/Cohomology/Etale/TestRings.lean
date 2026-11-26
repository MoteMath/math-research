import Lib.Cohomology.Etale.Functoriality
import Lib.General.Algebra.AdicRingHomExt
section
open PrimeSpectrum AlgebraicGeometry CategoryTheory
variable (A) [CommRing A]
class IsAICLocal extends IsDomain A, IsLocalRing A, IsAIC A
structure IsTest extends IsAIC A where
  (isComparableRing : IsComparableRing (· : A → A)) isReduced : IsReduced A
abbrev TestRing := @ObjectProperty.FullSubcategory CommRingCat.{0} _ (IsTest ·)
abbrev testIncl : TestRing ⥤ CommRingCat := ObjectProperty.ι _
abbrev PointFunctor := CommRingCat.{0} ⥤ Type 1
variable (Λ : Ab.{0}) {X Y : PointFunctor} (u : X ⟶ Y) {R} (s : X ⟶ reprBy R) (I : Set R) {B} (φ : R ⟶ B)
def locConstSpec : CommRingCat.{0} ⥤ Ab := .mk _ (AddCommGrpCat.ofHom <| LocallyConstant.comapAddMonoidHom (Z := Λ) ⟨_, continuous_comap ·.hom⟩)
def locConstCoeff := liftCoeff (testIncl ⋙ locConstSpec Λ)
abbrev mapOnTests := testIncl.whiskerLeft u
noncomputable abbrev HV.map := H.map (locConstCoeff Λ) (freeAb.map (mapOnTests u))
abbrev Components := IsCohomEquiv (locConstCoeff Λ) (freeAb.map (mapOnTests u))
abbrev HasCohomDenseImage := IsCohomDense (locConstCoeff Λ) (.range (mapOnTests u))
noncomputable def pointsToBase {X R} (s : X ⟶ Spec R) : Scheme.Spec.rightOp ⋙ uliftYoneda X ⟶ reprBy R := ⟨fun _ ↦ ↾(⟨Spec.preimage <| ·.1 ≫ s⟩), by delta reprBy reprFunctor; aesop⟩
def baseRingMap (x : X B) : R ⟶ B := (s B x).1
@[simp] lemma baseRingMap_map {B'} f x : baseRingMap s (@X.map B B' f x) = baseRingMap s x ≫ f := by aesop (add simp baseRingMap)
def zeroPoints := Subfunctor.mk (fun _ ↦ {x | ∀ a ∈ I, baseRingMap s x a = 0}) (by aesop)
def unitPoints := Subfunctor.mk (fun _ ↦ {x | ∀ a ∈ I, IsUnit (baseRingMap s x a)}) (by simp_all [IsUnit.map])
abbrev baseChangeOf := fibreProd s (reprMap φ)
end
open IsLocalRing Classical ValuationRing IsLocalization IsAIC LocallyConstant Ideal.Quotient
universe u
variable {A : Type u} {B : Type*} [CommRing A] [CommRing B] {M : Submonoid A} {f : A →+* B} (K : Type*) [Field K] [IsAlgClosed K]
instance : IsAICLocal K := {}
instance (V : ValuationSubring K) : IsAICLocal V := {of_isIntegrallyClosedIn K with}
lemma locallyConstant_mem_of_indicator {Λ} [AddCommGroup Λ] {S : AddSubgroup (LocallyConstant _ Λ)} (h : ∀ a (e : A) i, indicator (const _ a) (PrimeSpectrum.isClopen_iff.2 ⟨e, i, rfl⟩) ∈ S) y : y ∈ S := by choose e i H using (PrimeSpectrum.isClopen_iff.1 <| y.2.isClopen_fiber ·); convert sum_mem (t := y.range_finite.toFinset) fun a _ ↦ h a _ (i a); ext; erw [map_sum (evalAddMonoidHom _)]; simp [Set.indicator, ← H]
lemma exists_map_dvd_of_mem_map [PreValuationRing A] {J x} : x ∈ Ideal.map f J → ∃ i ∈ J, f i ∣ x := by apply Submodule.span_induction <;> simp <;> grind [map_dvd, dvd_trans, dvd_add, dvd_mul_left, J.zero_mem, dvd_total]
lemma isTest_of_preValuationRing [IsDomain A] [PreValuationRing A] [IsAIC A] : IsTest A := ⟨‹_›, by simp [IsComparableRing, dvd_total], inferInstance⟩
lemma IsTest.pi {ι} {K : ι → _} [∀ i, CommRing (K i)] (h : ∀ i, IsTest (K i) := by
    exact fun _ ↦ isTest_of_preValuationRing) : IsTest (∀ i, K i) := have := (h · |>.3)
  ⟨⟨fun P m d ↦ by simpa [P.eval₂_eq_sum_range, Polynomial.eval, funext_iff, skolem] using (h · |>.exists_eval₂_eq_zero (Pi.evalRingHom ..) m d)⟩, fun _ _ ↦ by simpa [IsIdempotentElem, funext_iff, pi_dvd_iff, skolem, forall_and] using (h · |>.2 ..), inferInstance⟩
lemma IsTest.isComparableRing_of_associated (h : IsTest A) (g : ∀ y, ∃ x, Associated (f x) y) : IsComparableRing f := fun y z ↦ by
  obtain ⟨⟨x, _, ⟨⟩⟩, z, _, ⟨⟩⟩ := g y, g z
  peel h.2 x z; simpa [← mul_assoc] using this.imp f.map_dvd f.map_dvd
lemma IsComparableRing.id : IsComparableRing f → IsComparableRing (@_root_.id B) := (· · · |>.imp' f (by grind [IsIdempotentElem]))
lemma exists_associated_localization y : ∃ x, Associated (algebraMap A (Localization M) x) y := ⟨_, .symm ⟨(map_units ..).unit, sec_spec M y⟩⟩
lemma IsTest.localization : IsTest A → IsTest (Localization M) | h@⟨_, _, _⟩ => ⟨of_isLocalization M, (h.isComparableRing_of_associated exists_associated_localization).id, inferInstance⟩
lemma IsTest.quotient (h : IsTest A) {J : Ideal A} : J.IsRadical → IsTest (A ⧸ J) := (⟨h.of_surjective mk_surjective, .id (h.isComparableRing_of_associated (mk_surjective.forall.2 (⟨·, .rfl⟩))), J.isRadical_iff_quotient_reduced.1 ·⟩)
lemma IsTest.exists_valuationSubring_atPrime (h : IsTest A) (p : Ideal A) [p.IsPrime] : let L := Localization.AtPrime p
  IsAICLocal L ∧ PreValuationRing L ∧ ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (O : ValuationSubring K) (_ : Algebra A O), IsLocalization.AtPrime O p := by
  intro L; have ⟨_, c, _⟩ : IsTest L := h.localization
  have := PreValuationRing.iff_dvd_total.2
    ⟨(c · · |>.elim (by cases isUnit_or_isUnit_one_sub_self · <;> simp_all))⟩
  have := @NoZeroDivisors.to_isDomain L _ _ ⟨@fun x y e ↦ by
    simpa [e, ← sq] using (dvd_total y x).imp (mul_dvd_mul_left x) (mul_dvd_mul_right · y)⟩
  exact ⟨{}, ‹_›, FractionRing L, _, h.localization.localization.isAlgClosed, @Valuation.valuationSubring .., _, (isLocalization_iff_of_ringEquiv _ (@equivInteger L _ _ _ _ _ {} _)).1 inferInstance⟩
instance [IsAICLocal A] : IsAlgClosed (ResidueField A) := isAlgClosed (.of_surjective residue_surjective)
