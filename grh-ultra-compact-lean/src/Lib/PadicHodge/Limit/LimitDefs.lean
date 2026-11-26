import Lib.PadicHodge.Crystalline.HodgeTateFrame
open TensorProduct Module
variable {p} [ThePrime p] {Γ T R : Type} [Group Γ] [OverGp Γ p] [AddCommGroup T] [Module ℤ_[p] T] [CommRing R] [Module R T] [Algebra ℤ_[p] R] [IsScalarTower ℤ_[p] R T]
lemma periodTensorMap_injective [Flat ℤ_[p] T] : (periodTensorMap _ _ .id : Amax ⊗[_] T → Bcris ⊗ T).Injective := Flat.rTensor_preserves_injective_linearMap (Algebra.algHom ..).toLinearMap (injective_BPlus_Bcris.comp injective_Amax_BPlus)
def IsCrystallineUpTo (h : ℕ) (ρ : Representation R Γ T) := IsCrystalline ρ ∧ ∀ γ k, jump ρ γ k ≠ 0 → 0 ≤ k ∧ k ≤ h
structure PadicRep Γ [Group Γ] p [ThePrime p] where
  {Index : Type} [fintypeIndex : Fintype Index] (rep : Γ →* GL Index (PadicAlgCl p))
attribute [instance] PadicRep.fintypeIndex
noncomputable abbrev applyVec {m} [Fintype m] (u : T →ₗ[ℤ_[p]] Matrix m m (PadicAlgCl p)) v := (Matrix.mulVecBilin _ ℤ_[p]).flip v ∘ₗ u
