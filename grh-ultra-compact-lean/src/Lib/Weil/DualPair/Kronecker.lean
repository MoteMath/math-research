import Lib.General.LinearAlgebra.ExtendColumns
open Matrix Kronecker
scoped[Kronecker] attribute [simp] conjTranspose_kronecker det_kronecker' transpose_map
  conjTranspose_transpose_eq_transpose_conjTranspose
scoped[Kronecker] attribute [simp ←] mul_kronecker_mul transpose_mul
variable {m n R : Type*} [Fintype m] [Fintype n]
@[local simp] noncomputable def kroneckerGL [CommSemiring R] (x : GL m R) (y : GL n R) :
    GL (m × n) R := ⟨x ⊗ₖ y, ↑x⁻¹ ⊗ₖ ↑y⁻¹, by simp, by simp⟩
@[simps! apply_coe_val] noncomputable def U.kron [CommRing R] [StarRing R] {S K : Matrix n n R}
    {T : Matrix m m R} {J} (hS : S * K = 1) (h : J = T ⊗ₖ Kᵀ) : U S × U T →* U J := .mk'
  (fun p ↦ ⟨kroneckerGL p.2 (transposeGL p.1⁻¹), by simpa [U, inv_eq_right_inv hS, h,
                 conjTranspose_nonsing_inv] using! congr($(p.2.2) ⊗ₖ $(p.1.2)⁻¹ᵀ)⟩) (by aesop)
lemma map_kronecker {a b c d R S} [Ring R] [Ring S] (f : R →+* S) (A : Matrix a b R)
    (B : Matrix c d R) : (A ⊗ₖ B).map f = A.map f ⊗ₖ B.map f := by aesop
