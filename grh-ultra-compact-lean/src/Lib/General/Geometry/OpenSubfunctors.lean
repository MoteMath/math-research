import Lib.Cohomology.Hodge.CupProduct
import Lib.Cohomology.Etale.ClosedClasses
open CategoryTheory Function Set MonoidalCategory CommAlgCat RingHom Ideal Quotient
attribute [local simp] eq_zero_iff_mem Ideal.map_top range_comp
attribute [local simp ←] map_eq_bot_iff_le_ker map_mapₐ map_span comap_map_of_surjective'
variable {C} [Category C] (k) [CommRing k] (d : outParam ℕ)
structure HodgeTest where (baseAlg : CommAlg k) (Index) [fintypeIndex : Fintype Index] [linearOrderIndex : LinearOrder Index]
attribute [instance] HodgeTest.fintypeIndex HodgeTest.linearOrderIndex
def affineSpace : CommAlg k ⥤ Type 1 := .mk (ULift <| Fin d → ·) fun f ↦ ↾(⟨f ∘ ·.1⟩)
variable {k} {X Y : CommAlg k ⥤ Type 1} (V : Subfunctor X) {A B : CommAlg k} (P : ∀ K, X K → _)
def unimodular {d} : Subfunctor (affineSpace k d) := ⟨fun _ ↦ {v | span (range v.1) = ⊤}, by delta affineSpace; simp_all⟩
@[simp] abbrev structureMap : of k k ⟶ A := ofHom (Algebra.ofId ..)
def fieldLocus : Subfunctor X := ⟨fun _ ↦ {x | ∀ K φ, IsField K.1 → P K (X.map φ x)}, by grind [=_ X.map_comp_apply]⟩
def ComesFromPoints (s : Set _) K (x : X K) := ∃ z ∈ s, x = X.map structureMap z
def offPoints s := @fieldLocus k _ X (¬ComesFromPoints s · ·)
def IsOpenSub := ∀ A x, ∃ I, ∀ B φ, @X.map A B φ x ∈ V B ↔ map φ.hom I = ⊤
variable (X) (ι : C ⥤ CommAlg k)
class IsSepFunctor where exists_ideal A x y : ∃ J, ∀ B φ, @X.map A B φ x = X.map φ y ↔ J ≤ ker φ.hom
def IsAffinelyCovered X := IsSepFunctor X ∧ ∃ B y, IsPointwiseSurjective (ι.whiskerLeft (@pointMap _ _ X B y))
class HasCoveringPoints where
 exists_surjective_point B {c} (z : (ι ⋙ reprBy B) c) : ∃ᵉ (c') (y : (ι ⋙ reprBy B) c'),
  IsPointwiseSurjective (pointMap y)
def offDiagonal := @fieldLocus k _ (X ⊗ X) fun _ x ↦ x.1 ≠ x.2
structure EtaleChart where
 (R) point : X R
 coordinate : Fin d → R
 etale : (MvPolynomial.aeval (R := k) coordinate).1.Etale
 injective A : Injective (@X.map R A · point)
 isOpenSub : IsOpenSub (.range (pointMap point))
variable {X P d V} (a : EtaleChart d X) (I : Ideal A) (φ : A ⟶ B) {v : Fin d → A}
def IsSquareZero := Surjective φ ∧ ker φ.hom ^ 2 = ⊥
abbrev EtaleChart.locus := Subfunctor.range (pointMap a.point)
instance EtaleChart.mono_pointMap : Mono (pointMap a.point) := mono_of_app_injective (a.injective · |>.comp ULift.down_injective)
lemma EtaleChart.eq_comp_of_map_point_eq {ψ χ} (e : X.map χ a.point = X.map φ (X.map ψ a.point)) : χ = ψ ≫ φ := a.injective _ (by simp [e])
lemma projSpace.span_eq_top_of_isUnit i : IsUnit (v i) → span (range v) = ⊤ := eq_top_of_isUnit_mem _ (by bound)
lemma map_eq_top_iff_fields : I.map φ.hom = ⊤ ↔ ∀ K (ψ : B ⟶ K), IsField K → ¬I ≤ ker (φ ≫ ψ).hom := by simpa using ⟨by aesop, (ne_top_iff_exists_maximal.not_right.2 fun ⟨m, _, l⟩ ↦ · _ (ofHom (mkₐ ..)) (Quotient.field m).toIsField (map_mk_eq_bot_of_le l))⟩
lemma IsOpenSub.fieldLocus_le : IsOpenSub V → fieldLocus V ≤ V := (· · · |>.elim fun _ h e ↦ by
 simpa +contextual [↓map_eq_top_iff_fields, (h ..).1 (e ..)] using h _ (𝟙 _))
lemma IsOpenSub.exists_basicOpen (h : IsOpenSub V) x (k : IsField B) (e : X.map φ x ∈ V B) : ∃ f, φ f ≠ 0 ∧ ∀ B ψ, IsUnit (ψ f) → X.map ψ x ∈ V B := (h A x).elim fun I _ ↦ (not_subset.1 (by aesop : ¬I ≤ ker φ.hom)).imp (by aesop (add safe [eq_top_of_isUnit_mem, mem_map_of_mem]))
lemma isOpenSub_fieldLocus (h : ∀ A x, ∃ J, ∀ K φ, IsField K.1 → (P K (@X.map A K φ x) ↔ ¬J ≤ ker φ.hom)) : IsOpenSub (fieldLocus P) := by peel 3 h; simp_all [fieldLocus, map_eq_top_iff_fields, ↓← this]
namespace IsOpenSub
lemma mem_of_isSquareZero (h : IsOpenSub V) (s : IsSquareZero φ) x : X.map φ x ∈ V B → x ∈ V A := (h A x).elim fun I h _ ↦ by simpa [← s.2 ▸ I.sup_pow_eq_top (by simp_all [IsSquareZero])] using h _ (𝟙 _)
lemma inf {W} (h : IsOpenSub V) (h' : IsOpenSub W) : IsOpenSub (V ⊓ W) := fun _ x ↦
 (h _ x).elim fun I _ ↦ (h' _ x).imp' (I * ·) (by simp_all [I.map_mul, ← one_eq_top])
lemma preimage (h : IsOpenSub V) u : @IsOpenSub _ _ Y (V.preimage u) := by aesop_cat
lemma whisker_restrictAlg {E} [CommRing E] [Algebra k E] (h : IsOpenSub V) : IsOpenSub (V.whisker (restrictAlg k E)) := fun _ x ↦ (h _ x).imp fun _ H _ _ ↦ H _ _
end IsOpenSub
@[simp] lemma map_map_structureMap z : X.map φ (X.map structureMap z) = X.map structureMap z := X.map_comp_apply .. ▸ by rcongr
lemma isOpenSub_offPoints [IsSepFunctor X] {s : Set _} [Finite s] : @IsOpenSub _ _ X (offPoints s) := isOpenSub_fieldLocus fun _ x ↦ by
 choose J _ using (IsSepFunctor.exists_ideal _ x <| X.map structureMap ·)
 use s.toFinite.toFinset.inf J, by simp_all [ComesFromPoints, IsField.isDomain, (ker_isPrime _).inf_le']
lemma isOpenSub_offDiagonal [IsSepFunctor X] : IsOpenSub (offDiagonal X) := isOpenSub_fieldLocus fun _ ⟨x, y⟩ ↦ by peel IsSepFunctor.exists_ideal _ x y; tauto
lemma mem_offDiagonal_of_ne [IsSepFunctor X] (k : IsField A) {x y} (e : x ≠ y) : (x, y) ∈ offDiagonal X A := (IsSepFunctor.exists_ideal _ x y).elim fun _ H _ _ _ ↦ let := k.toField; (H ..).1.mt (by simpa [LE.le, *] using H _ (𝟙 A))
lemma isLocallyEverything_of_open_cover {Θ : C ⥤ _} {T} (H : ∀ K, IsField K.1 → ∀ x, ∃ O, @IsOpenSub _ _ X O ∧ x ∈ O K ∧ O.whisker Θ ≤ T) : IsLocallyEverything (Θ ⋙ forget₂ ..) T := fun _ y m _ ↦ have := (Quotient.field m).toIsField; (H _ this _).elim fun _ ⟨o, p, _⟩ ↦ (o.exists_basicOpen (ofHom (mkₐ ..)) y this p).imp (by aesop)
variable (d X)
class IsChartCovered where exists_chart K : IsField K.1 → ∀ x, ∃ a : EtaleChart d X, x ∈ a.locus K
class HasAtlas extends IsSepFunctor X where
 exists_finite_charts : ∃ᵉ (n) (a : Fin n → EtaleChart d X), ∀ K, IsField K.1 → ∀ x, ∃ i,
  x ∈ (a i).locus K
