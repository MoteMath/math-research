import Lib.General.LinearAlgebra.Base
open Polynomial AdjoinRoot ComplexOrder DoubleCoset Fintype Function IsLocallyConstant Matrix MeasureTheory Submodule
variable {B A n Λ} [CommRing B] [CommRing A] [Fintype n] [Algebra B A] [Ring Λ] [Algebra B Λ]
lemma exists_adjugate_of_charpoly_mem (ρ : Λ →ₐ[B] Matrix n n A) (c : ∀ w k, (ρ w).charpoly.coeff k ∈ (algebraMap B A).range) w : ∃ v F, (ρ w).det = algebraMap B A F ∧ ρ (v * w) = ρ (F • 1) ∧ ρ w * ρ v = F • 1 := by have ⟨Q, hQ⟩ := (lifts_iff_coeff_lifts _).2 (c (-w)); have := Q.divX_mul_X_add ▸ hQ ▸ And.intro (aeval_self_charpoly _) (eval_charpoly _ 0); have := congr(aeval (-ρ w) $Q.divX.X_mul); use Q.divX.aeval (-w), Q.coeff 0; simp_all [← aeval_algHom_apply, neg_add_eq_zero, Algebra.algebraMap_eq_smul_one]
lemma amitsur_charpoly_mem_of_span (ρ : Λ →ₐ[B] Matrix n n A) (hρ : span B {s | ∀ k, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range} = ⊤) w k : (ρ w).charpoly.coeff k ∈ (algebraMap B A).range := by let e := revAt (ρ w).charpoly.natDegree k + 1; let R := (aeval (R := B) (root (@X A _ ^ e))).range; let t : R := ⟨_, X, rfl⟩; let f := ((ofAlgHom B (X ^ e)).mapMatrix.comp ρ).liftEquiv B R _ _; have H s (c : R) : (1 - c • f (1 ⊗ₜ s)).det = (ρ s).charpoly.reverse.aeval c.1 := (by simp [f, reverse_charpoly, charpolyRev, AlgHom.map_det, R.smul_def, map_sub, Matrix.map_smul', comp_def]); cases (Nat.decreasingInduction (fun j _ Q γ ↦ closure_induction (x := γ) (by simp) (by simp_all [← add_assoc, -map_add]) (fun c x ⟨s, hs, e⟩ β h ↦ let ⟨_, b⟩ := (lifts_iff_coeff_lifts _).2 hs; sub_add_cancel (β + _) _ ▸ Q (β * c • x) _ (by convert (det_mul ..).symm.subst (mul_mem h ((H s (t ^ j.succ * c)).substr (by simp [reverse, ← b, reflect_map, -MulMemClass.coe_mul]))); simp [← e, mul_sub, sub_mul]; module)) ((hρ ▸ baseChange_span R _ :).le (by simp))) (by simp [R.smul_def, t, ← mk_X, ← map_pow]) e.zero_le : ∀ γ β, (1 - t • f β).det ∈ R → (1 - t • f (β + t ^ 0 • γ)).det ∈ R) (1 ⊗ₜ w) 0 (by simp); simp_all [aeval_eq_of_algebra, t, X_pow_dvd_iff, coeff_reverse]; grind [revAt_invol]
lemma charpoly_smul_coeff a (M : Matrix n n A) k : (a • M).charpoly.coeff k = a ^ (card n - k) * M.charpoly.coeff k := by
  by_cases! h : card n < k
  · nontriviality; simp [*, coeff_eq_zero_of_natDegree_lt]
  rw [← Nat.sub_sub_self h]; simp [charpoly_coeff_eq_sum_minors, Finset.mul_sum, submatrix_smul]; grind [Finset.sum_congr]
variable (A G W : Type*) [Group G] [CommSemiring A] [AddCommMonoid W] [Module A W]
lemma herm_represents_one {m} [Fintype m] {β : Matrix m m ℂ} (h : β.IsHermitian) (S : Submodule ℂ _) (n : ¬∀ v ∈ S, star v ⬝ᵥ β *ᵥ v ≤ 0) : ∃ v ∈ S, star v ⬝ᵥ β *ᵥ v = 1 := by obtain ⟨⟨v, k, n⟩, _⟩ := not_forall₂.1 n, h.im_star_dotProduct_mulVec_self; exists _, S.smul_mem (√(star v ⬝ᵥ β *ᵥ v).re)⁻¹ k; simp_all [Complex.le_def, Complex.ext_iff]; grind
def HasLargeSplit {X : Type} (N : (X →₀ ℕ) → NNReal) k D (r : ℝ) := ∃ α : Fin k → _, ∑ b, α b = D ∧ r ≤ ∏ b, N (α b)
attribute [simp↓ low] finsum_eq_sum_of_fintype
instance : CoeFun (Rep A G) (G → Module.End A ·) := ⟨(·.ρ)⟩
@[simps! apply_apply] def rightRegular : Representation A G (G → W) := by use! fun g ↦ .funLeft A W (· * g) <;> aesop (add simp mul_assoc)
variable {A G W} (π : Representation A G W) (K Γ K' : Subgroup G)
def levelSpace (χ : K →* A := 1) : Submodule A W := by use! {v | ∀ k, π k.1 v = χ k • v} <;> simp_all [smul_comm (χ _)]
noncomputable def heckeFun (f : G → A) : Module.End A W := ∑ᶠ q : G ⧸ K, f q.out • π q.out
noncomputable def heckeCoset g := heckeFun π K ((doubleCoset g K K).indicator 1)
def classAut g := Γ ⊓ K'.comap (MulAut.conj g⁻¹).toMonoidHom
abbrev DoubleCosets := @Quotient G _ Γ K'
variable {K H : Subgroup G} {Δ} [Group Δ] {π : Representation A G W}
@[simp] lemma mem_levelSpace {χ v} : v ∈ levelSpace π K χ ↔ ∀ k, π k.1 v = χ k • v := .rfl
lemma map_mem_levelSpace_of_commute {χ v a} : v ∈ levelSpace π K χ → (∀ k : K, Commute (π k) a) → a v ∈ levelSpace π K χ := by simp_all [commute_iff_eq, DFunLike.ext_iff]
@[simp] lemma mem_classAut {g γ} : γ ∈ classAut H K g ↔ γ ∈ H ∧ g⁻¹ * γ * g ∈ K := by simp [classAut]
lemma exists_eq_map_mul_rep_mul (e : Δ →* G) K {r : _ → G} (hr : ∀ c, DoubleCoset.mk e.range K (r c) = c) g : ∃ c γ, ∃ k : K, g = e γ * r c * k := ⟨_, by simpa using (eq ..).1 (hr _)⟩
lemma eq_and_eq_one_of_doubleCoset_rep {e : Δ →* G} {r : _ → G} (hr : ∀ c, DoubleCoset.mk e.range K (r c) = c) {c d} (h : ∀ γ, (r d)⁻¹ * e γ * r d ∈ K → γ = 1) γ (H : (r c)⁻¹ * e γ * r d ∈ K) : c = d ∧ γ = 1 := by grind [(@DoubleCoset.eq _ _ e.range K (r d) (r c)).2 ⟨_, ⟨γ, rfl⟩, _, inv_mem H, by group⟩]
noncomputable def classSum [Module ℚ W] Γ K (f : G → W) := ∑ᶠ c, (Nat.card (classAut Γ K (c : Quotient Γ K).out) : ℚ)⁻¹ • f c.out
variable [TopologicalSpace G] [IsTopologicalGroup G] (hK : @IsCompact G _ K) (hH : @IsOpen G _ H)
@[to_additive] lemma isLocallyConstant_of_eventually_mul {X} {f : G → X} (e : ∀ᶠ k in nhds 1, ∀ x, f (x * k) = f x) : IsLocallyConstant f := (iff_eventually_eq f).2 (map_mul_left_nhds_one · ▸ e.mono (by tauto))
include hH
lemma finite_quotient_image_of_isCompact {C} (h : @IsCompact G _ C) : ((↑) '' C : Set (G ⧸ H)).Finite := (@isCompact_iff_finite _ _ _ (QuotientGroup.discreteTopology hH)).1 (h.image (by tauto))
include hK
@[to_additive relIndex_ne_zero_add] lemma IsCompact.relIndex_ne_zero : H.relIndex K ≠ 0 := have := hK.compactSpace; (Subgroup.quotient_finite_of_isOpen _ hH.preimage_val).card_pos.ne'
variable [MeasurableSpace G] [BorelSpace G] [T2Space G] (μ : Measure G) [μ.IsMulLeftInvariant]
@[to_additive] lemma relIndex_mul_measure_inf : H.relIndex K * μ ↑(H ⊓ K) = μ K := by have e : MeasurableEmbedding K.subtype := .subtype_coe hK.measurableSet; simpa [↓e.comap_apply, ↓← Subgroup.coe_map] using! @Subgroup.index_mul_measure _ _ _ _ _ ⟨hK.relIndex_ne_zero hH⟩ (e.2 hH.measurableSet) _ (.comap μ e)
@[to_additive measure_inter_eq_inv_relIndex_add] lemma measure_inter_eq_inv_relIndex (h : μ K = 1) : μ (H ∩ K) = (↑(H.relIndex K))⁻¹ := by simp [ENNReal.eq_inv_of_mul_eq_one_left (h ▸ relIndex_mul_measure_inf hK hH μ)]
omit hK hH
lemma hasDerivAt_det {γ : ℝ → Matrix n n ℂ} {Y s} (e : γ s = 1) (h : HasDerivAt γ Y s) : HasDerivAt (γ · |>.det) Y.trace s := ((ContinuousMultilinearMap.hasFDerivAt ⟨(@detRowAlternating n _ _ ℂ _).1.restrictScalars ℝ, continuous_id.matrix_det⟩ _).comp_hasDerivAt s h).congr_deriv (by erw [_root_.sum_apply, ← _root_.funext fun _ ↦ cramer_transpose_apply ..]; aesop)
lemma pderiv_comm {σ} a b (p : MvPolynomial σ B) : (p.pderiv b).pderiv a = (p.pderiv a).pderiv b := by ext; simp [MvPolynomial.coeff_pderiv, Finsupp.single_apply]; grind
