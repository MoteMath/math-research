import Lib.Adelic.Hecke.ClassMean
import Lib.GLn.Branching.BranchingVector
noncomputable section
open Complex HasFiniteType ComplexOrder Finset Function PolyRep Matrix MatrixOrder
variable {G Γ W : Type*} [Group G] [Group Γ] {K : Subgroup G} [AddCommGroup W] [Module ℂ W] {e : Γ →* G} {ρ : Representation ℂ Γ W} {χ : K →* ℂ} [TopologicalSpace G] [IsTopologicalGroup G] {Φ : Type} [Fintype Φ] {n n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] {κ : Φ → ℕ → ℕ}
def SmoothForm (e : Γ →* G) (ρ : Representation ℂ Γ W) := (smoothFunctions ℂ).1 ⊓ ρ.coindV e
@[simps! -fullyApplied apply_apply_coe] def smoothFormRep (e : Γ →* G) (ρ : Representation ℂ Γ W) := (rightRegular ..).subrepresentation (SmoothForm e ρ) fun a _ ↦ .imp ((smoothFunctions ℂ).2 a ·) (by simp [mul_assoc, · _])
lemma PolyRep.schur_conjTranspose_weylGram_schur (hF : FitsRanks n n' κ) (w z : ∀ τ, Matrix (n' τ) (n τ) ℂ) : (schur κ w)ᴴ * ((weylGram n' κ).map (@Int.cast ℂ _) * schur κ z) = (∏ τ, ((w τ)ᴴ * z τ).det ^ schurDetExp n n' κ τ) • (weylGramOver * schur κ fun τ ↦ (w τ)ᴴ * z τ) := ext_iff_mulVec.2 (by simp [conjTranspose, hF, transpose_map, vecMul_schur_eq_iff, nablaCombination_weylGramOver_mulVec, rowSubst_rowSubst, ← mulVec_mulVec, mulVec_transpose, ↓← det_transpose (_ᴴ * _)])
lemma weylNormSq_schur_le (hF : FitsRanks n n' κ) (z : ∀ τ, Matrix (n' τ) (n τ) ℂ) : ∃ ρ : Φ → ℕ → NNReal, (∀ τ, (range (rankAt n τ)).sum (ρ τ) ≤ ∑ a, ∑ b, ‖z τ a b‖ ^ 2) ∧ ∀ ξ, weylNormSq (schur κ z *ᵥ ξ) ≤ (∏ τ, ∏ i ∈ range (rankAt n τ), ρ τ i ^ diagramWeight (rankAt n') κ (τ, i)) * weylNormSq ξ := by
 let := Prop.linearOrder
 have hA τ := (z τ).posSemidef_conjTranspose_mul_self
 choose d h2 using (NNReal.canLift.1 _ <| hA · |>.eigenvalues_nonneg ·)
 choose ρ hρ P using fun τ ↦ univ.induction_on_max_value (d τ) (motive := fun S ↦ ∃ ρ, (range #S).sum ρ = S.sum (d τ) ∧ ∀ A ⊆ S, A.prod (d τ) ≤ (range #A).prod ρ) (by simp) fun a s h _ ⟨ρ, _⟩ ↦ ⟨(·.casesOn (d τ a) ρ), by simp_all [sum_range_succ', add_comm], (·.induction_on_max_value (Eq a) (by simp) (by simp_all [prod_range_succ', mul_comm]; grind [mul_le_mul']))⟩
 use ρ, (hρ · ▸ by simpa [← real_le_real, h2, conj_mul'] using (hA _).1.trace_eq_sum_eigenvalues.ge.trans_eq sum_comm)
 have k (M : ℝ) (c : ℂ) h ξ := (Commute.mul_nonneg weylGram_posDef.posSemidef.nonneg (b := M • 1 - c • schur κ fun τ ↦ diagonal (ofReal ∘ (hA τ).1.eigenvalues)) h (by simp [commute_iff_eq, mul_sub, sub_mul, weylGram_mul_schur]; simp [schur_diagonal_eq_prod])).posSemidef.re_dotProduct_nonneg (schur κ (star (hA · |>.1.eigenvectorUnitary.1)) *ᵥ ξ)
 simp [weylNormSq, star_mulVec_dotProduct, schur_conjTranspose_weylGram_schur, hF, mul_assoc, ← star_eq_conjTranspose (star _), mul_sub, sub_mul, ← by simpa [mul_assoc] using (hA · |>.1.spectral_theorem)] at k ⊢; apply k
 simp [schur_diagonal_eq_prod, ← diagonal_one, le_iff, ← diagonal_smul, ← h2, (hA _).1.det_eq_prod_eigenvalues]
 norm_cast; grw (transparency := default) [diagramWeight_eq_of_fitsRanks hF, P, (prod_map _ ⟨_, tableau_col_injective ..⟩ _).ge, P] <;> simp +contextual [pow_add, diagramWeight, ← prod_pow_eq_pow_sum, ite_and, prod_pow, field, Finsupp.single_apply, prod_comm, -mem_range]; simp [prod_range (n := rankAt ..)]
attribute [-simp] MonoidHom.coe_range mem_classAut
attribute [local simp] DFunLike.dite_apply classSum mul_assoc
lemma levelSpace_smoothFormRep_apply {φ} (h : φ ∈ levelSpace (smoothFormRep e ρ) K χ) γ g (k : K) : φ.1 (e γ * g * k) = χ k • ρ γ (φ.1 g) := φ.2.2 .. ▸ congr($(h k).1 _)
lemma eq_of_eq_on_class_reps {r : _ → G} (hr : ∀ c, DoubleCoset.mk e.range K (r c) = c) : Injective (((LinearMap.funLeft ℂ W r).domRestrict _).domRestrict (levelSpace (smoothFormRep e ρ) K χ)) := by simp_intro _ _ _ [funext_iff]; ext; choose _ _ _ _ using exists_eq_map_mul_rep_mul e K hr ‹_›; grind [=> levelSpace_smoothFormRep_apply]
instance : Fact ((1 : K →* ℂ) =ᶠ[nhds 1] 1) := ⟨.rfl⟩
lemma mem_smoothFunctions_of_eigen (χ : K →* ℂ) [o : Fact (χ =ᶠ[nhds 1] 1)] (hK : @IsOpen G _ K) {f} (h : ∀ k : K, rightRegular ℂ G W k f = χ k • f) : f ∈ (smoothFunctions ℂ).1 := (rightStab _).isOpen_of_mem_nhds (hK.isOpenMap_subtype_val.nhds_le 1 (o.1.mono (by simp_all [funext_iff])))
variable (e ρ χ) [o : Fact (χ =ᶠ[nhds 1] 1)] [H : HasFiniteType e.range K] [i : Fact (Injective e)]
@[local simp] def deltaForm (x : G) : W →ₗ[ℂ] levelSpace (smoothFormRep e ρ) K χ := by
 choose s h using exists_transporter e.range i.1 .rfl K x
 refine have t v k := ?_; .codRestrict _ (.codRestrict _ (.pi fun y ↦ ∑ γ ∈ s y, dite _ (χ ⟨x⁻¹ * e γ * y, ·⟩ • ρ γ⁻¹) fun _ ↦ 0) fun v ↦ ⟨mem_smoothFunctions_of_eigen χ H.3 (t v), by simp_intro γ _; apply sum_equiv (.mulRight γ) <;> simp_all⟩) (Subtype.ext <| t · ·)
 ext; simp [smul_sum]; apply sum_equiv 1 <;> simp_all [mul_mem_cancel_right, smul_smul, ← mul_assoc, mul_comm (χ k), ← map_mul, K.mul_def]
def freeLevelEquiv (h : ∀ g, classAut e.range K g = ⊥) {r : _ → G} (hr : ∀ c, DoubleCoset.mk e.range K (r c) = c := by exact (·.out_eq)) : levelSpace (smoothFormRep e ρ) K χ ≃ₗ[ℂ] DoubleCosets e.range K → W := by
 refine ⟨_, fun f ↦ ∑ c, deltaForm e ρ χ (r c) (f c), fun _ ↦ eq_of_eq_on_class_reps hr (?t _), ?t⟩
 intro; ext d; simp [h]; rw [sum_eq_single d, sum_eq_single 1]; simp [← K.one_def]
 repeat grind [card_le_one, sum_eq_zero, e.map_one, one_mem, inv_mul_cancel]
variable {e ρ χ}
lemma classSum_deltaForm (L : G → W →+ ℂ) {x v} (hL : ∀ γ (k : K), L (e γ * x * k) (χ k • ρ γ v) = L x v) : classSum e.range K (fun g ↦ L g ((deltaForm e ρ χ x v).1.1 g)) = L x v := by have t y γ := (hL γ⁻¹ ⟨x⁻¹ * e γ * y, ·⟩); simp_all [-Nat.card_eq_fintype_card, Rat.smul_def]; rw [sum_eq_single (DoubleCoset.mk _ _ x), sum_eq_card_nsmul (b := L x v), inv_mul_eq_iff_eq_mul₀ (by simp)] <;> grind [card_classAut_out, DoubleCoset.out_eq', sum_eq_zero]
variable [Module.Finite ℂ W]
instance finite_levelSpace_smoothFormRep : Module.Finite ℂ (levelSpace (smoothFormRep e ρ) K χ) := .of_injective _ (eq_of_eq_on_class_reps Quot.out_eq)
lemma finrank_levelSpace_smoothFormRep (h : ∀ g, classAut e.range K g = ⊥) : Module.finrank ℂ (levelSpace (smoothFormRep e ρ) K χ) = .card (DoubleCosets e.range K) * Module.finrank ℂ W := by simp [(freeLevelEquiv _ ρ χ h).finrank_eq]
