import Lib.General.LinearAlgebra.HuaIntegral
open Matrix CStarRing Norms.L2Operator
class IsHermInvolution {n} [Fintype n] (J : Matrix n n ℂ) where (isHermitian : J.IsHermitian) (mul_self : J * J = 1)
variable {n} [Fintype n] {J : Matrix n n ℂ} [IsHermInvolution J] (g : U J)
instance (ε : n → _) : IsHermInvolution (signMatrix ε) := ⟨by simp [signMatrix, IsHermitian], signMatrix_mul_self ε⟩
instance : @IsHermInvolution n _ 1 := ⟨by simp, by simp⟩
lemma IsHermInvolution.det_ne_zero (J : Matrix n n ℂ) [IsHermInvolution J] : J.det ≠ 0 := det_ne_zero_of_left_inverse mul_self
noncomputable def skewOfReal : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℂ := by use! (fun y ↦ of fun a b ↦ ((1 + Complex.I) * y a b - (1 - Complex.I) * y b a) / ite (a = b) 2 √2) <;> simp [funext_iff] <;> grind
noncomputable def skewCoords : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℝ := by use! (fun x ↦ of fun a b ↦ ((x a b).re + (x a b).im) / ite (a = b) 1 √2) <;> simp [funext_iff] <;> grind
lemma IsHermInvolution.isUnit : IsUnit J := .of_mul_eq_one _ mul_self
lemma IsHermInvolution.mem_unitary : J ∈ _root_.unitary _ := by simp [Unitary.mem_iff, isHermitian.star_eq, mul_self]
@[simp] lemma U.norm_det : ‖g.1.1.det‖ = 1 := norm_coe_unitary (det (IsHermInvolution.det_ne_zero J).isUnit g)
lemma U.norm_inv : ‖g⁻¹.1.1‖ = ‖g.1.1‖ := by simp [↓coe_inv IsHermInvolution.mul_self, norm_mul_mem_unitary, norm_mem_unitary_mul, IsHermInvolution.mem_unitary, l2_opNorm_conjTranspose]
lemma U.one_le_norm [Nonempty n] : 1 ≤ ‖g.1.1‖ := by simpa [← pow_two, ↓norm_inv] using norm_mul_le g⁻¹.1.1 g
