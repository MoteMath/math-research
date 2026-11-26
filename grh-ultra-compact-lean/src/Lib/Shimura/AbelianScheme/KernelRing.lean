import Lib.General.Geometry.TensorPowers
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Adjunction CommRingCat Over Equiv Obj AddMonObj AddGrpObj Functor Over.OverMorphism Spec MorphismProperty
variable {S S' : Scheme.{0}} (b : S' ⟶ S) (O : outParam Type) [CommRing O] (A : Over S)
class abbrev AddObj := AddGrpObj A, IsCommAddMonObj A
attribute [instance] Hom.addCommGroup
export AddMonObj (comp_add add_comp comp_nsmul nsmul_comp comp_zero)
class ModuleObj [AddObj A] where
  [homModule (T) : Module O (T ⟶ A)]
  comp_smul {T' T} (a : T' ⟶ T) (c : O) x : a ≫ (c • x : _ ⟶ A) = c • a ≫ x
attribute [reducible, instance] ModuleObj.homModule
class IsAbelianScheme extends AddObj A, Smooth A.hom, IsProper A.hom where
  nsmul_surjective : ∀ m ≠ 0, Surjective (m • 𝟙 A).left
variable {A B T X Y : Over S} [AddObj A] [AddObj B] {R : outParam _} [CommRing R] [ModuleObj R A] [ModuleObj R B] (c : R) (f : A ⟶ B)
structure IsGroupBaseChange {B} [AddObj B] [ModuleObj R B] (p :
  (CategoryTheory.Over.map b).obj B ⟶ A) where
  isPullback : IsPullback p.left B.hom A.hom b
  linear {U} : IsLinearMap R (@(CategoryTheory.Over.map b).map U _ · ≫ p)
abbrev IsAdditive := IsAddMonHom f
class abbrev IsIsogeny := IsAddMonHom f, IsFinite f.left, Flat f.left, Surjective f.left
class IsLinear extends IsAddMonHom f where smul_id_comp (c : R) : (c • 𝟙 A) ≫ f = c • f
variable {f}
@[simp] lemma IsLinear.smul_comp [h : IsLinear f] t : (c • t : T ⟶ A) ≫ f = c • t ≫ f := by grind [t ≫= h.2 c, ModuleObj.comp_smul]
attribute [simp] comp_add ModuleObj.comp_smul add_comp comp_neg comp_sub sub_comp comp_nsmul nsmul_comp comp_zsmul zsmul_comp
lemma isAdditive_of_universal (h : (fst A A + snd ..) ≫ f = fst .. ≫ f + snd .. ≫ f) : IsAdditive f := ⟨by simpa [comp_add_assoc] using! 0 ≫= h, by simpa [add_eq_add]⟩
instance (priority := low) : ModuleObj ℤ A := ⟨by simp⟩
omit [ModuleObj R A] in instance [IsAdditive f] : IsAdditive (c • f) := isAdditive_of_universal (by simp)
@[irreducible] instance pullbackAddObj : AddObj ((pullback b).obj A) where
  add_comm := by simp [← LaxBraided.braided_assoc, ↓← Functor.map_comp, IsCommAddMonObj.add_comm]
instance : ModuleObj R ((pullback b).obj A) where
  homModule _ := AddEquiv.module _ (.symm ⟨(mapPullbackAdj b).homEquiv .., by
          delta pullbackAddObj; simp [Adjunction.homEquiv, Functor.map_add']⟩)
  comp_smul := by simp [smul_def, ← homEquiv_naturality_left, homEquiv_counit]
variable (c : Pic A.left) (x y : T ⟶ A) (f : X ⟶ Y) (z : 𝟙_ _ ⟶ A)
instance [IsIso f] : IsIso f.left := map_isIso (forget S) f
instance [IsProper X.hom] [IsSeparated Y.hom] : IsProper f.1 := by simp_all [IsProper.of_comp _ Y.3]
instance {X Y S d} f g [@SmoothOfRelativeDimension d X S f] : @SmoothOfRelativeDimension d _ Y (Limits.pullback.snd f g) := (smoothOfRelativeDimension_isStableUnderBaseChange d).1 (.of_hasPullback ..) ‹_›
abbrev specOver R B [CommRing.{0} R] [CommRing B] [Algebra R B] := CategoryTheory.Over.mk (Spec.map (ofHom (algebraMap R B)))
@[simp] abbrev translation := 𝟙 A + toUnit A ≫ z
instance : IsIso (translation z) := ⟨translation (-z), by simp⟩
namespace Pic
def atPoint := c.pull x.left
def pairing := c.atPoint (x + y) - c.atPoint x - c.atPoint y + c.atPoint 0
def ParallelogramLaw := ∀ ⦃T⦄ x y, @atPoint _ _ T c (x + y) + c.atPoint (x - y) + 2 • c.atPoint 0 = 2 • (c.atPoint x + c.atPoint y)
end Pic
variable {R C D : Type} [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra R D] {E : Type} [CommRing E] [Algebra R E] (φ : C →ₐ[R] D) (ψ : D →ₐ[R] E)
def specOver.map : specOver R D ⟶ specOver R C := Over.homMk (Spec.map (ofHom φ)) (by simp [← Spec.map_comp, ← ofHom_comp])
@[reassoc] lemma specOver.map_comp : map ψ ≫ map φ = map (ψ.comp φ) := OverMorphism.ext (Spec.map_comp ..).symm
@[simp] lemma specOver.map_id : map (.id R C) = 𝟙 _ := OverMorphism.ext (Spec.map_id _)
lemma specOver.map_bijective : (map : (C →ₐ[R] D) → _).Bijective := ((Equiv.mk (CommAlgCat.ofHom · |>.op) (·.1.1)).trans (@algSpec.fullyFaithful ⟨R⟩).homEquiv).bijective
variable {R : _} [CommRing R] {A B : Over (Spec ⟨R⟩)} {f : A ⟶ B}
lemma locallyOfFinitePresentation_left [g : LocallyOfFiniteType B.hom] [h : LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation f.left := by solve_by_elim (maxDepth := 20) [(f.1.appLE_comp_appLE .. ▸ (f.w ▸ h).1 .. :).of_comp_finiteType, g.1, isAffineOpen_top]
lemma exists_isPullback_SpecMap {X Y} f [@IsAffineHom.{0} X Y f] {C} i : ∃ P φ j, IsPullback j (@Spec.map C P φ) f i := ⟨_, _, _, .of_iso_pullback ⟨by simp [Limits.pullback.condition]⟩ (Scheme.isoSpec _).symm rfl (Spec.map_preimage _).symm⟩
lemma eq_zero_iff_factors_zero_section [AddObj B] : f = 0 ↔ ∃ l, l ≫ ζ[B].left = f.left := ⟨by aesop, fun ⟨l, e⟩ ↦ by ext; simp [CategoryTheory.Hom.zero_def, ← f.w, ← e]⟩
variable [AddObj B] [IsSeparated B.hom]
instance : IsClosedImmersion ζ[B].left := of_postcomp _ _ _ ‹_› (by simp; infer_instance)
lemma exists_finite_kernel_ring (F : IsFinite f.left) : ∃ (S : CommAlgCat R) (ι : specOver R S ⟶ A), Module.Finite R S ∧ (∀ [Flat f.left], Module.Flat R S) ∧ IsClosedImmersion ι.left ∧ ι ≫ f = 0 ∧ ∀ ⦃T⦄ (y : T ⟶ A), y ≫ f = 0 → ∃ z, z ≫ ι = y := (exists_isPullback_SpecMap _ ζ[B].1).elim fun P
  ⟨φ, i, H⟩ ↦ ⟨@.of .., homMk i (by simpa using! H.w =≫ B.3), by simpa using! of_isPullback H F, Flat.SpecMap_iff.1 (of_isPullback H ‹_›), of_isPullback H.flip inferInstance, by ext; exact H.w, fun _ _ h ↦ ⟨homMk _ (H.lift_snd _ _ congr($h.1)), by aesop⟩⟩
