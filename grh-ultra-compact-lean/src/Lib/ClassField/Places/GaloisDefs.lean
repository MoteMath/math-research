import Lib.General.LinearAlgebra.Base
noncomputable section
open NumberField Pointwise MulAction Units MulSemiringAction ValuationSubring SetLike
def Ω := AlgebraicClosure ℚ deriving Field, IsAlgClosed, CharZero
instance : Algebra.IsAlgebraic ℚ Ω := AlgebraicClosure.isAlgebraic ℚ
abbrev ClosurePlace := ValuationSubring Ω
def IsComplexConj {Γ} [SMul Γ Ω] (c : Γ) := ∃ j : Ω →+* ℂ, ∀ x, j (c • x) = star (j x)
variable (O Γ : Type*) (K Ω : outParam Type*) [Group Γ] [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω] (l : ℕ) [Fact l.Prime] [CommRing O] [Algebra ℤ_[l] O]
abbrev DiscreteUnits := Additive Ωˣ
instance : TopologicalSpace (DiscreteUnits Ω) := ⊥
instance : DiscreteTopology (DiscreteUnits Ω) := ⟨rfl⟩
class IsProGalois [TopologicalSpace Γ] extends IsGaloisGroup Γ K Ω, IsGalois K Ω, IsTopologicalGroup Γ, CompactSpace Γ, TotallyDisconnectedSpace Γ where
  isOpen_stabilizer (x : Ω) : @IsOpen Γ _ (stabilizer Γ x)
instance : CoeFun (ValuationSubring Ω) (Ω → ·.ValueGroup) := ⟨(·.valuation)⟩
variable {Ω} (A : ValuationSubring Ω)
abbrev decompGroup := stabilizer Γ A
abbrev valuationVia x := A (algebraMap K Ω x)
abbrev valRingBelow := (A.valuation.comap (algebraMap K Ω)).valuationSubring
class IsLocalGalois (A : outParam (ValuationSubring Ω)) [TopologicalSpace Γ] extends IsProGalois Γ K Ω, IsAlgClosed Ω, CharZero Ω where
  mem_decompGroup g : g ∈ decompGroup Γ A
  dvr : IsDiscreteValuationRing (valRingBelow K A)
  finite_residue : Finite (IsLocalRing.ResidueField (valRingBelow K A))
variable {Γ K} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
def unitsRep : Representation ℤ Γ (DiscreteUnits Ω) := @.ofMulDistribMulAction Γ _ _ _ mulDistribMulActionRight
def IsFrob q σ := σ ∈ decompGroup Γ A ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ • x - x ^ q) < 1
def IsPlaceOver := ∀ x : 𝓞 K, A.valuation (algebraMap K Ω x) < 1 ↔ x ∈ v.asIdeal
variable {A q} {σ τ g : Γ} {Γ' Ω'} [Group Γ'] [Field Ω'] [MulSemiringAction Γ' Ω'] {φ : Γ' → Γ} {j : Ω →+* Ω'} (e : ∀ g x, j (φ g • x) = g • j x) {A' s q'} (h : IsFrob A q σ)
lemma mem_decompGroup_iff : σ ∈ decompGroup Γ A ↔ ∀ x, σ • x ∈ A ↔ x ∈ A := ext'_iff.trans mem_stabilizer_set
lemma smul_eq_comap : g • A = A.comap (toRingHom _ _ g⁻¹) := ext' (Set.preimage_smul_inv ..).symm
lemma conj_mem_decompGroup_smul : σ ∈ decompGroup Γ A → g * σ * g⁻¹ ∈ decompGroup Γ (g • A) := by simp_all [mul_smul]
lemma isEquiv_comap : (comap A' j).valuation.IsEquiv (A'.valuation.comap j) := Valuation.isEquiv_of_val_le_one (by simp)
lemma val_comap_lt_one {x} : (comap A' j) x < 1 ↔ A' (j x) < 1 := isEquiv_comap.lt_one_iff_lt_one
attribute [local simp↓] IsFrob mem_decompGroup_iff mul_smul smul_sub val_comap_lt_one
lemma val_smul_lt_one (g : Γ) {x} : (g • A) (g • x) < 1 ↔ A x < 1 := by rw [smul_eq_comap]; simp
include e
lemma decompGroup.map : s ∈ decompGroup _ A' → φ s ∈ decompGroup Γ (A'.comap j) := by aesop
lemma IsFrob.map : IsFrob A' q s → IsFrob (A'.comap j) q (φ s) := by simp_all
omit e
include h
lemma IsFrob.conj g : IsFrob (g • A) q (g * σ * g⁻¹) := by rw [smul_eq_comap]; aesop
lemma IsFrob.mul_iff : IsFrob A (q * q') (σ * τ) ↔ IsFrob A q' τ := (mul_mem_cancel_left h.1).and (forall₂_congr fun x _ ↦ .trans (by simp [pow_mul']; rfl) ((add_mem_cancel_right
  (H := A.nonunits) (h.2 (x ^ q') (by grind [pow_le_one']))).trans (h.1 ▸ val_smul_lt_one σ)))
lemma IsFrob.pow n : IsFrob A (q ^ n) (σ ^ n) := n.rec (by simp) (by grind [mul_iff, pow_succ])
variable (Γ A) in
def inertiaGroup : Subgroup Γ := ⟨⟨⟨{σ | IsFrob A 1 σ}, (·.mul_iff.2)⟩, by simp⟩, (·.mul_iff.1 (by simp))⟩
lemma IsFrob.inv_mul : IsFrob A q τ → σ⁻¹ * τ ∈ inertiaGroup Γ A := h.mul_iff.1 ∘ by simp
variable (Ω)
def cycChar : Γ →* ℤ_[l]ˣ := (cyclotomicCharacter Ω l).comp (toRingAut ..)
abbrev cycCharIn := (map (algebraMap _ O).1).comp (cycChar (Γ := Γ) Ω l)
