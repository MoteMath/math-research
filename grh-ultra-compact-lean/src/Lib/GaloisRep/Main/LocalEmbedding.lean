import Lib.ClassField.Places.PadicDecomposition
import Lib.PadicHodge.Crystalline.Defs
import Lib.Weil.Unramified.SphericalHecke
variable (ℓ) [ThePrime ℓ] (E m : Type) [Fintype m] [Field E] [Algebra E Ω]
abbrev GalRep := Gal(Ω/E) →* GL m (PadicAlgCl ℓ)
class PadicPlaceEmbedding (A : ClosurePlace) (ℓ : outParam ℕ) [ThePrime ℓ] extends OverGp
  (decompGroup Gal(Ω/E) A) ℓ where (e) inducesPlace : InducesPlace E A e toGp
variable {ℓ E m} (r : GalRep ℓ E m) (A : ClosurePlace) [NumberField E] [PadicIso ℓ] (R : ℕ → ℕ → Prop) (J : (E →+* ℂ) → Multiset ℤ) (w : FinPlace E)
noncomputable abbrev decompRep := matrixRep (r.comp (decompGroup _ A).subtype)
def IsGoodAt := (A.valuation ℓ = 1 → ∀ s ∈ inertiaGroup _ A, r s = 1) ∧ ∀ [PadicPlaceEmbedding E A ℓ], IsCrystalline (decompRep r A)
def IsFiniteTypeAt := (A.valuation ℓ = 1 → ∀ᶠ s in nhds 1, s ∈ inertiaGroup _ A → r s = 1) ∧ ∀ [PadicPlaceEmbedding E A ℓ], IsPotCrys (decompRep r A)
def PolyKillsAt s P := (A.valuation ℓ = 1 → Polynomial.aeval (r s).1 P = 0) ∧ ∀ [L : PadicPlaceEmbedding ..] ⦃h k⦄, IsWeilPair (L.toGp ⟨s, h⟩) k → IsKilledBy (decompRep r A) ⟨s, h⟩ k P
def JumpsRelAt := ∀ ⦃L : PadicPlaceEmbedding E A ℓ⦄ ⦃γ⦄ ⦃g : Gp ℓ⦄, (∀ x, γ x = ↑(g x)) → ∀ u, R ((J (.comp ιℓ.symm
 (.comp ↑g⁻¹ (L.e.comp (algebraMap ..)) : E →+* PadicAlgCl ℓ))).count u) (jump (decompRep r A) γ u)
abbrev HasJumpsAt := JumpsRelAt r A Eq J
abbrev OccursIn m n := m ≠ 0 → n ≠ 0
def SphericalClause P := ∀ ⦃A⦄, IsPlaceOver A w → IsGoodAt r A ∧ JumpsRelAt r A R J ∧ ∀ s, IsFrob A w.q s⁻¹ → PolyKillsAt r A s P
variable {ℓ : _} [ThePrime ℓ] {E : _} [Field E] [Algebra E Ω] {A : _} [h : PadicPlaceEmbedding E A ℓ]
lemma PadicPlaceEmbedding.isFrob_iff {q s} : IsFrob (intQpBar ℓ) q (h.toGp s) ↔ IsFrob A q s.1 := by
 obtain @⟨_, e, ⟨⟨⟩, k⟩, -⟩ := h
 simpa [IsFrob, isLocalGalois_padic.4, val_comap_lt_one, ← k, ← mem_ball_zero_iff, -Metric.mem_ball, -AlgEquiv.smul_def] using ⟨by tauto, (isClosed_property (denseRange_emb_padicAlgCl e) (isClosed_imp (Valued.isOpen_integer (PadicAlgCl ℓ)) (IsUltrametricDist.isClosed_ball ..).preimage_of_continuous) ·)⟩
lemma PadicPlaceEmbedding.isWeilPair_zero_iff {s} : IsWeilPair (h.toGp s) 0 ↔ s ∈ inertiaGroup _ A := _root_.isWeilPair_zero_iff.trans isFrob_iff
lemma PadicPlaceEmbedding.cyclotomicGp_eq_cycChar g : cyclotomicGp (h.toGp g) = cycChar Ω ℓ g.1 := (cycChar_eq_of_equivariant ℓ (symm ∘' h.inducesPlace.1.2 g)).symm
