import Lib.LocalGL.Green.LabelIdempotents
variable {G V} [Group G] [Fintype G] [NormedAddCommGroup V] [InnerProductSpace ℂ V] {e : MonoidAlgebra ℂ G}
lemma IsCentralProj.self_adjoint (ρ : Representation ℂ G V) (he : IsCentralProj e) (σ : ℂ ≃+* ℂ) (B : V →ₛₗ[(.comp ↑σ⁻¹ ((starRingEnd ℂ).comp σ) : ℂ →+* ℂ)] V →ₗ[ℂ] ℂ) (hρ : ∀ s x y, B (ρ s x) (ρ s y) = B x y) x y : B (ρ.asAlgebraHom e x) y = B x (ρ.asAlgebraHom e y) := by simpa [asAlgebraHom_eq_sum] using Fintype.sum_equiv (.inv G) _ _ (by simp [← hρ · x, ← by simpa using (he.map σ).isChar.apply_inv])
lemma IsCentralProj.sum_norm_conv_le (he : IsCentralProj e) {H} [Group H] [Fintype H] (φ : G →* H) (f : H → V) : ∑ s, ‖∑ t, e.coeff t • f ((φ t)⁻¹ * s)‖ ^ 2 ≤ ∑ s, ‖f s‖ ^ 2 := by
 let L t := LinearIsometryEquiv.piLpCongrLeft 2 ℂ V (.mulLeft (φ t))
 choose K _ h using LinearMap.isSymmetricProjection_iff_eq_coe_starProjection.1 ⟨he.1.map _, he.self_adjoint ⟨⟨(L · |>.1.1), by aesop⟩, by aesop⟩ 1 (innerₛₗ ℂ) (L · |>.inner_map_map)⟩
 simpa (disch := positivity) [PiLp.norm_eq_of_L2, asAlgebraHom_eq_sum, L] using
  congr(‖$h (.toLp 2 f)‖).trans_le (K.norm_starProjection_apply_le _)
