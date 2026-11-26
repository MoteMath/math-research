import Lib.Adelic.Witt.SpaceOperations
import Lib.General.LinearAlgebra.ExpSurjective
@[simps! apply_coe_val] noncomputable def U.inl {n m} [Fintype n]
  [Fintype m] (ε : n → _) (η : m → _) := (sum (signMatrix_sum ε η)).comp (.inl ..)
variable (E) {n} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n] (s : n → ℤˣ)
noncomputable def maxCompact : Subgroup (G E s) := .prod (.pi .univ fun _ ↦ maxCompactU s) (Kf ..)
variable {E s}
lemma isCompact_maxCompact : IsCompact (maxCompact E s : Set (G E s)) := (isCompact_univ_pi fun _ ↦
  isCompact_iff_compactSpace.2 ⟨@isCompact_univ (maxCompactU s) _ _⟩).prod isCompact_Kf
