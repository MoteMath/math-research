import Lib.ClassField.GaloisCohomology.CyclicClass
import Lib.General.Analysis.OstrowskiTaussky
noncomputable section
open NumberField Units Classical
variable {Γ K Ω} [Group Γ] [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω] (A : ValuationSubring Ω) [TopologicalSpace Γ]
def IsUniformiser π := ∀ x, valuationVia K A x < 1 ↔ valuationVia K A x ≤ valuationVia K A π
abbrev fixedFieldOf [IsProGalois Γ K Ω] (H : Subgroup Γ) : IntermediateField K Ω := FixedPoints.intermediateField H
section
variable (Ω) [IsTopologicalGroup Γ] (χ : QZChar Γ)
def cycCharMod N [NeZero N] [HasEnoughRootsOfUnity Ω N] := (modularCyclotomicCharacter Ω (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N)).comp (MulSemiringAction.toRingAut Γ Ω)
def QZChar.toHom := MonoidHom.mk' (Multiplicative.ofAdd <| χ.1 ·) χ.2.2
abbrev QZChar.ker := (toHom χ).ker
def QZChar.abelianLift : TopologicalAbelianization Γ →* Multiplicative QZ := QuotientGroup.lift _ (toHom χ) (closure_minimal (Abelianization.commutator_subset_ker _) ⟨χ.2.1.1 {0}ᶜ ⟨⟩⟩)
variable (Γ)
def DiscreteUnits.ofBase [SMulCommClass Γ K Ω] : Additive Kˣ →+ (@unitsRep Γ Ω _ _ _).invariants := .codRestrict (map (algebraMap K Ω)).toAdditive _ fun _ _ ↦ ext (smul_algebraMap ..)
variable (K) {Ω}
abbrev residueCard := Nat.card (IsLocalRing.ResidueField (valRingBelow K A))
def ordRat := epsilon fun f : DiscreteUnits Ω →+ ℚ ↦ ∀ π : Kˣ, IsUniformiser A π.1 → ∀ x (n : ℕ) (a : ℤ), A.valuation x.toMul ^ n = valuationVia K A π ^ a ↔ n * f x = a
def IsClassOfInv (b : QZ →+ H2 (@unitsRep Γ Ω _ _ _)) := (⇑b).Injective ∧ ∀ χ, (∀ g ∈ inertiaGroup Γ A, χ.1 g = 0) → ∀ φ, IsFrob A (residueCard K A) φ → ∀ w (n : ℤ), ordRat K A w.1 = n → cyclicClass _ χ w = n • b (χ.1 φ)
def classOfInv := epsilon (IsClassOfInv Γ K A)
def IsLocalArtin {L} [Field L] [Algebra L Ω] [SMulCommClass Γ L Ω] (f : Lˣ →* TopologicalAbelianization Γ) := ∀ χ x, classOfInv Γ K A (QZChar.abelianLift χ (f x)).toAdd = -cyclicClass _ χ (DiscreteUnits.ofBase _ Ω (.ofMul x))
end
variable (Γ) [IsProGalois Γ K Ω] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
def localArtin := epsilon fun f : (v.adicCompletion K)ˣ →* _ ↦ IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A (f.comp (map (algebraMap K _).1))
def placeOver [Algebra K _root_.Ω] : ClosurePlace := epsilon (IsPlaceOver · v)
