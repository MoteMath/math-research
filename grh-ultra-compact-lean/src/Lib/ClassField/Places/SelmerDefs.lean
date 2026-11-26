import Lib.Adelic.Adeles.LocalComponents
import Lib.General.NumberTheory.StableLattice
import Lib.ClassField.HeckeCharacter.CharacterLevels
import Lib.ClassField.Local.ArtinMapAtPlace
noncomputable section
variable {ℓ : ℕ} [Fact ℓ.Prime] (E : Type) [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E] {C} [CommMonoid C]
class UnramCMField E [Field E] extends EmbeddedNumberField E, NumberField.IsCMField E, StablyUnram E
def ellVal (x : PadicAlgCl ℓ) := ite (‖x‖ = 0) ⊤ (ENNReal.ofReal (-.logb ℓ ‖x‖))
def cmConj := (exists_isComplexConj Gal(Ω/ℚ) Rat.isReal_infinitePlace).choose
lemma isComplexConj_cmConj : IsComplexConj cmConj := .choose_spec _
def placesDividing (N : ℕ) := {v : FinPlace E | ↑N ∈ v.1}
instance : Fintype (placesDividing E ℓ) := (finite_natCast_mem ℓ).fintype
variable {E G O O' n} [CommRing O] [CommRing O'] [Fintype n] [Monoid G]
@[simp] lemma cmConj_cmConj x : cmConj (cmConj x) = x := congr($isComplexConj_cmConj.mul_self x)
@[simp] lemma cmConj_algebraMap x : cmConj (algebraMap E Ω x) = algebraMap E Ω (star x) := isComplexConj_cmConj.elim (·.injective <| map_star_complex (.comp ..) x ▸ · _)
def conjGal : Gal(Ω/E) →* Gal(Ω/E) := .mk' ({cmConj * ·.restrictScalars ℚ * cmConj with commutes' := by simp}) (by aesop)
structure IsFromU1 S I (χ : Gal(Ω/E) →* C) where
  isLocallyConstant : IsLocallyConstant χ
  exists_ideleChar : ∃ η : _ →* C, (∀ x, η (principalIdele x) = 1) ∧ (∀ a ∈ idelesUnitOff (.conjClosure S), (∀ w ∈ I \ S.conjClosure, Valued.v ((ideleAt w a).1 - 1) < 1) → η a = 1) ∧ ∀ x (g : Gal(Ω/E)), artinMap Gal(Ω/E) x = g → χ g = η (x / star x)
def twistRep (e : O →+* O') (ψ : G →* O') (ρ : G →* Matrix n n O) := smulMonoidHom.comp (ψ.prod (e.mapMatrix.1.comp ρ))
variable (ρ : Gal(Ω/E) → Matrix n n O) (S L B) [AddCommGroup B] [Module O B]
def locConst [TopologicalSpace G] : Submodule O (G → B) := ⟨⟨⟨Set.ofPred IsLocallyConstant, (·.add)⟩, .const _⟩, fun _ ↦ (·.comp _)⟩
def selmerModule := obeying (cocycleRels ρ ∪ (.single · 1) '' inertiaAbove Sᶜ ∪ L) B ⊓ locConst _
variable (ℓ E) (Λ : Type) [CommRing Λ] [Algebra ℤ_[ℓ] Λ] (e ν : ℕ)
def cycInv := (Units.coeHom _).comp (cycCharIn (Γ := Gal(Ω/E)) Λ Ω ℓ)⁻¹
def tateTwist := (Matrix.scalar Unit).1.comp (cycInv ℓ E Λ ^ e)
def shaLocalSet := {g : Gal(Ω/E) | ∃ A : ClosurePlace, A.valuation ℓ < 1 ∧ if e = 0 then g ∈ inertiaGroup _ A else g ∈ decompGroup _ A ∧ cycChar Ω ℓ g = 1}
def shaOdd := .pi (shaLocalSet ℓ E e) ⊥ ⊓ (⨅ _ : e ≠ 0, LinearMap.ker (1 + .funLeft _ _ conjGal)) ⊓ selmerModule (tateTwist ℓ E Λ e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : Λ))
