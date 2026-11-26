import Lib.Shimura.IntegralModel.NeatLevel
open Polynomial Finset Set
variable {E n M : Type} [Field E] [CMType E] [Fintype n]
@[simp] lemma coeff_heckePoly {R} [CommRing R] q N t j : (@heckePoly R _ q N t).coeff j = (ite (j ≤ N) ((-1) ^ (N - j) * q ^ (N - j).choose 2) 0 : ℤ) * t (N - j) := by
 simp [heckePoly, -map_mul]; grind [sum_eq_single (N - j)]
lemma HasHeckePolyAt.isMonicOfDegree {f : Gf E n → M → ℂ} (hf : f ≠ 0) {w hw P} : HasHeckePolyAt f w hw P → P.IsMonicOfDegree (Fintype.card n) := fun ⟨k, t, h, ht⟩ ↦ by simp_all [isMonicOfDegree_iff, heckeSplit, natDegree_le_iff_coeff_eq_zero, not_le.2, ← smul_left_inj hf, ← ht, heckeGL_zero, mem_sphericalAt_iff hw]
variable {G G' W : Type _} [Group G] [Group G'] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W) (K : Subgroup G) {J : Subgroup G'} {f : G → ℂ} {F : G' → ℂ} (T : Module.End ℂ (levelSpace π K))
attribute [local simp] indicator mul_mem_cancel_left mul_assoc heckeFun_sum
def s08_r8 : Representation ℂ G (G → ℂ) := ⟨⟨fun g ↦ .funLeft _ _ (g⁻¹ * ·), by aesop⟩, by aesop⟩
def IsOperatorOf f := ∃ a, f = (cosetFn K a · : G → _) ∧ ∀ v, T v = π.asAlgebraHom a v
variable {π K T}
lemma r9 {k g} : k ∈ K → indicator K 1 (k * g) = (indicator K 1 g : ℂ) := by aesop
lemma IsOperatorOf.t3 {φ a s} (hF : HasFiniteCosets J F) (e : φ = heckeFun (s08_r8.comp a) J F f) : IsOperatorOf π K T f → IsOperatorOf π K ((heckeFun (π.comp a) J F).restrict s * T) φ := .imp' (∑ q ∈ hF.toFinset, .single (a q.out) (F q.out) * ·) (by simp_all [cosetFn, funext_iff, s08_r8])
