import Lib.GaloisRep.Pseudocharacter.FibreSum
import Lib.LocalGL.TraceFormula.ChangingSigns
noncomputable section
section
open Quotient ConjAct Finset Matrix MulAction NumberField Polynomial
variable {E n} [Field E] [CMBase E] [Fintype n] {x g : GL n (𝔸f E)} {ℓ ε} {𝔑 : 𝓞 E} {f : heckeAlgebra n ℂ 𝔑}
lemma ratConj_eigenReflection {ε μ} {y : GL n E} z : ratConj z (eigenReflection ε y μ) = eigenReflection ε (z * y * z⁻¹) μ := by simp [eigenReflection, ratConj, ← aeval_smul, units_smul_def, ← map_inv]
lemma isSignedFrame_mul_iff z (h : g ∈ GU E n) : IsSignedFrame (x * g) ℓ ↔ IsSignedFrame (toFinGL z * x) (ratConj z ℓ) := ⟨(by simpa [mul_assoc] using ·.mul z (inv_mem h)), (by simpa [ratConj] using ·.mul z⁻¹ h)⟩
lemma finsum_countTerm_eq_sum w (h : (countTerm ε f 1).support.Finite) : ∑ᶠ c, countTerm ε f w c = ∑ c ∈ h.toFinset, countTerm ε f 1 c * w c.out.2.1.1.charpoly c.out.2.2 := by convert finsum_eq_sum_of_support_subset .. <;> simp [countTerm] <;> grind
lemma isReflection_eigenReflection {y : GL n E} (hz : y.1.charpoly.Separable) : (∀ i, IsReflection (eigenReflection True y i)) ∧ ∀ J, IsReflection J → ratConj y J = J → ∃ i, y.1.map (Φ v₀) * (J + 1) = numberedRoots (Φ v₀) y.1.charpoly i • (J + 1) ∧ ∀ j, J = eigenReflection True y j ↔ i = j := ((isConj_diagonal_of_isRoot_charpoly (isRoot_numberedRoots hz _)).imp (·.mul_inv_eq_iff_eq_mul.2)).rec fun k (h : toConjAct k • diagonalAlgHom ℂ _ = y.1.map (Φ v₀)) ↦ by
  simp [eigenReflection, ← h, aeval_smul, aeval_algHom_apply, aeval_pi_apply, -Lagrange.interpolate_apply, eval_interpolate_univ_node, -diagonalAlgHom_apply]
  refine .symm ⟨fun J r c ↦ (r.conj k⁻¹).elim fun u ⟨w, a, e⟩ ↦ (exists_ne_zero_of_sum_ne_zero (a ▸ two_ne_zero)).imp fun i s ↦ ?_, fun i ↦ .conj k ⟨diagonal 1 i, diagonal 2 i, ?_⟩⟩
  obtain ⟨rfl, c⟩ := inv_smul_eq_iff (g := toConjAct k).1 e, (Units.mul_inv_eq_iff_eq_mul _).1 c
  simp [← h, ← smul_mul', smul_comm (_ : ℂ), ↓smul_left_cancel_iff, mul_sub, sub_mul, smul_sub] at *
  all_goals simp_all [← ext_iff, diagonal_apply, vecMulVec, mul_comm]
  repeat grind [dotProduct, sum_eq_single i]
lemma heckeAlgebra.heckeCosetFn_conj (h : x ∈ levelGU n 𝔑) : heckeCosetFn f (x⁻¹ * g * x) = heckeCosetFn f g := by simpa [h] using! congr($(f.2.2 single_one_mem_levelSpace ⟨x, h⟩).1 g)
lemma heckeAlgebra.mem_GUPlus_of_ne_zero : heckeCosetFn f g ≠ 0 → g ∈ GUPlus E n := (spanOn.exists_mem_of_cosetFn_ne_zero f.2.1 · |>.rec fun _ ⟨d, e⟩ ↦ by simpa using mul_mem d (mem_GUPlus_of_mem_levelGU (QuotientGroup.eq.1 e)))
lemma countTerm_mk {μ w y} : countTerm ε f w ⟦(x, y, μ)⟧ = ite (IsSignedFrame x (eigenReflection ε y μ)) (heckeCosetFn f (γ y x) * w y.1.charpoly μ) 0 := (@mk_out _ (orbitRel _ (MarkedTriple _ n)) (⟦x⟧, y, μ)).rec fun z (e : (⟦_⟧, z * y * _, μ) = _) ↦ (QuotientGroup.mk_out_eq_mul _ (toFinGL z * x)).rec fun k h ↦ by
  rw [← heckeAlgebra.heckeCosetFn_conj k.2, countTerm, ← e]
  simp [h, γ, ← ratConj_eigenReflection, mul_assoc _ _ k.1, ← isSignedFrame_mul_iff z k⁻¹.2.1]; group
end
variable {E : Type} [Field E] [CMBase E] {n : Type} [Fintype n] (𝔑) {W} [AddCommGroup.{0} W] [Module ℂ W] (ξ : Representation ℂ (GL n E) W)
abbrev definiteForms := ξ.coindV toFinGL ⊓ .pi {x | ¬IsSignedFrame x 1} ⊥ ⊓ levelSpace (rightRegular ..) (levelGU n 𝔑)
open Set Submodule _root_.Quotient
attribute [local simp] eigenReflection subset_def countTerm_mk ratConj mul_assoc
def definiteForms.rep := Representation.subrepresentation ((rightRegular ..).asAlgebraHom.comp (heckeAlgebra n ℂ 𝔑).val).toMonoidHom (definiteForms 𝔑 ξ) fun a φ h ↦ ⟨(comap ((rightRegular ..).asAlgebraHom.toLinearMap.flip φ) (_ ⊓ _)).span_le.2 (by simp_all [↓image_subset_iff, isSignedFrame_mul_iff 1, GUPlus]) a.2.1, a.2.2 h.2⟩
lemma trace_definiteForms {𝔑} [Module.Finite ℂ W] (hN : IsNeat n 𝔑) a w : Module.Finite ℂ (definiteForms 𝔑 ξ) ∧ (countTerm False a w).support.Finite ∧ (IsRegularHecke a → (∀ y, y.1.charpoly.Separable → (ξ y⁻¹).trace ℂ _ = ∑ i, w y.1.charpoly i) → (definiteForms.rep 𝔑 ξ a).trace ℂ _ = ∑ᶠ c, countTerm False a w c) := by
  let I := {c : DoubleCosets toFinGL.range (levelGU n 𝔑) // IsSignedFrame c.out 1}
  cases @nonempty_fintype I ((finite_isSignedFrame_classes (isOpen_congruenceGL_span hN.1)).subset fun c ↦ (⟨_, ⟨_, ·⟩, c.out_eq⟩))
  choose c γ e using by simpa [← inv_mul_eq_iff_eq_mul, -MonoidHom.coe_range] using exists_eq_map_mul_rep_mul toFinGL (levelGU n 𝔑) out_eq
  have D g := by simpa using isSignedFrame_mul_iff (x := (toFinGL (γ g))⁻¹ * g) (ℓ := 1) (γ g) (inv_mem (e g).1)
  have i {c} {d : I} := eq_and_eq_one_of_doubleCoset_rep (c := c) out_eq fun _ ↦ (hN.2 d.2 · (by simp))
  refine .imp_right (⟨finite_of_finite_preimage (f := fun ((c : I), y, μ) ↦ ⟦(c.1.out, y⁻¹, μ)⟧) ?A ?S, fun r hw ↦ .trans · ?_⟩) (trace_eq_weighted_sum (·.1.out) 1 _ (range_subtype _) 1 (s := 1) (fun (j : I) g ↦ ite (j = c g) {γ g} ∅) (fun j g y ↦ ?_) (by simp +contextual [apply_ite, Subtype.coe_eq_iff, D]) (by tauto) rfl)
  exact (finite_iUnion fun c : I ↦ (((heckeCosetFn a).hasFiniteSupport.preimage (f := (⟦c.1.out⁻¹ * toFinGL · * c.1.out⟧)) fun y _ z _ h ↦ inv_mul_eq_one.1 (i _ (by simpa using QuotientGroup.eq.1 h)).2).prod finite_univ).image (c, ·)).subset (by simp; tauto)
  use Quotient.ind fun ⟨q, y, μ⟩ ↦ q.inductionOn fun x H ↦ ⟨(⟨_, by simp_all⟩, (_ * _)⁻¹, μ), sound ⟨(γ x)⁻¹, Prod.ext (QuotientGroup.eq.2 (e x)).symm rfl⟩⟩
  rw [← indicator_eq_self.2 ?S, ← finsum_mem_def, finsum_mem_range, finsum_curry₃ _ ?A]
  simp [(_ : I).2, ← Finset.mul_sum]; congr! 3; simpa [or_iff_not_imp_right] using hw _ ∘ @r _⁻¹ _
  use fun p q h ↦ (exact h).rec fun g h ↦ by grind [i g (by simpa using QuotientGroup.eq.1 congr($h.1).symm), inv_inj, one_smul]
  rw [← mul_mem_cancel_left (e g)]; simp [mem_ite]; use by simp_all, fun H ↦ by grind [i ((γ g)⁻¹ * y) (by simpa), inv_mul_eq_one]
