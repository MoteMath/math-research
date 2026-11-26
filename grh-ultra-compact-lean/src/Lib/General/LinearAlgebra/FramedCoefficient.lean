import Lib.DiscreteSeries.Rigidity.KernelFixes
noncomputable section
open Matrix Finset Norms.Frobenius Complex intervalIntegral ComplexConjugate MatrixOrder WithLp
variable {n} [Fintype n] {ε h} {l : @HCParam n ε} {P X Y : Matrix n n ℂ} {ρ σ : ℝ}
@[simp] abbrev intDiagonal (w : n → ℤ) := diagonal (w · : n → ℂ)
lemma frobenius_norm_sq_eq_sum : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by simp (disch := positivity) [frobenius_norm_def, ↓← Real.sqrt_eq_rpow]
lemma norm_trace_mul_le (a : ‖X‖ ≤ ρ := by rfl) (b : ‖Y‖ ≤ σ := by rfl) : ‖(X * Y).trace‖ ≤ ρ * σ := ((innerSL ℂ (toLp 2 (toLp 2 <| Xᴴ ·))).le_of_opNorm_le_of_le (x := toLp ..) (by simpa using norm_star X ▸ a) b).trans' (by simp [↓X.trace_mul_comm, inner, trace, mul_apply])
lemma trace_star_mul_self_eq_norm_sq : (Xᴴ * X).trace = ↑(‖X‖ ^ 2) := sum_comm.trans (by simp [frobenius_norm_sq_eq_sum, conj_mul'])
lemma frobenius_norm_mul_of_unitary (h : Xᴴ * X = 1) Y : ‖X * Y‖ = ‖Y‖ := by rw [← sq_eq_sq₀, ← ofReal_inj] <;> simp [↓← trace_star_mul_self_eq_norm_sq]; grind
lemma norm_smul_le_of_le_one (ρ : ℝ) (a : ‖X‖ ≤ σ) (h : 0 ≤ ρ ∧ ρ ≤ 1 := by grind) : ‖ρ • X‖ ≤ σ := by grw [norm_smul_of_nonneg, h.2, a] <;> bound
lemma inv_one_add_bounds (h : ‖X‖ ≤ σ) (hσ : σ ≤ 2⁻¹ := by nlinarith) : ((1 + X).det ≠ 0 ∧ (1 + X) * (1 + X)⁻¹ = 1 ∧ (1 + X)⁻¹ * (1 + X) = 1) ∧ ‖(1 + X)⁻¹ - 1‖ ≤ 2 * σ := by let ⟨V, e⟩ := (add_left_surjective 1).exists.1 (IsUnit.exists_left_inv ⟨.oneSub _ (by simp; grind), sub_neg_eq_add _ X⟩); simp_all [inv_eq_left_inv e, ↓mul_nonsing_inv, det_ne_zero_of_left_inverse e, mul_add, add_mul, add_assoc, add_eq_zero_iff_neg_eq]; grind [norm_neg, norm_add_le, norm_mul_le_of_le (refl ‖V‖) (h.trans hσ)]
def logOneAdd (X : Matrix n n ℂ) := ∫ s in 0..1, (1 + s • X)⁻¹ * X
lemma trace_mul_logOneAdd (h : ‖X‖ ≤ 2⁻¹) D : let f s := trace (D * ((1 + s • X)⁻¹ * X)); IntervalIntegrable f MeasureTheory.volume 0 1 ∧ ∫ s in 0..1, f s = (D * logOneAdd X).trace := by use ?_, (traceLinearMap .. ∘ₗ .mulLeft ℂ D).toContinuousLinearMap.intervalIntegral_comp_comm ?_ <;> apply ContinuousOn.intervalIntegrable <;> simp [Matrix.inv_def] <;> fun_prop (disch := grind [inv_one_add_bounds (norm_smul_le_of_le_one _ h _)])
lemma det_one_add_eq_exp_trace_logOneAdd (h : ‖X‖ ≤ 2⁻¹) : (1 + X).det = cexp (logOneAdd X).trace := by
  obtain ⟨⟨i, e⟩, u⟩ := trace_mul_logOneAdd h 1, (inv_one_add_bounds <| norm_smul_le_of_le_one · h ·)
  refine have := integral_eq_sub_of_hasDerivAt ?_ (i.sub i) (f := fun t ↦ (1 + t • X).det / exp (∫ s in 0..t, ((1 + s • X)⁻¹ * X).trace)); by simp_all; grind
  simp_intro s hs
  convert! ((hasDerivAt_det (nonsing_inv_mul ..) ((((hasDerivAt_id s).smul_const X).const_add 1).const_mul _)).const_mul (1 + s • X).det).div (integral_hasDerivAt_right (i.mono_set ?_) ⟨⊤, ?_⟩ ?_).cexp _
  any_goals simp [field, Set.Icc_subset_Icc, *]
  all_goals simp [Matrix.inv_def]; fun_prop (disch := simp [*])
lemma norm_logOneAdd_le (h : ‖X‖ ≤ 2⁻¹) : ‖logOneAdd X‖ ≤ 2 * ‖X‖ := (norm_integral_le_of_norm_le_const fun _ _ ↦ by grw [norm_le_insert', ← sub_one_mul, norm_mul_le, (inv_one_add_bounds (norm_smul_le_of_le_one _ h)).2]).trans_eq (by ring)
lemma norm_proj_mul_le (h : IsStarProjection P) (a : ‖X‖ ≤ ρ) : ‖P * X‖ ≤ ρ := by simpa [sub_mul, two_mul P, ← two_smul ℝ, norm_smul] using norm_add_le_of_le (frobenius_norm_mul_of_unitary h.two_mul_sub_one_mem_unitary.1 X ▸ a :) a
variable (p) [@DecidablePred.{1} n p]
def coordProj : Matrix n n ℂ := diagonal (if p · then 1 else 0)
lemma isStarProjection_coordProj : IsStarProjection (coordProj p) := by aesop (add simp [isStarProjection_iff', coordProj, star])
lemma norm_entryMask_le {r} [DecidableRel r] : ‖entryMask r X‖ ≤ ‖X‖ := by simp [frobenius_norm_def]; gcongr; bound
lemma isAccretive_of_norm_sub_one_lt (h : ‖X - 1‖ < 1) : X.IsAccretive := ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos _ (.add_star_self X)).2 fun x ↦ Not.imp_symm fun _ ↦ ⟨Units.mk0 (x - 2 : ℝ) (by grind) • .oneSub ((2 - x)⁻¹ • (1 - X - star (X - 1))) (by grw [norm_smul_of_nonneg, norm_sub_le, norm_sub_rev, norm_star, h] <;> bound), by simp [Algebra.algebraMap_eq_smul_one]; match_scalars <;> grind⟩).posDef
lemma flenstedJensen_shift_eq_conj (hg : l.HasGap h) {u} (hu : ∀ i j, ¬(l i < l j ∧ ε i = ε j) → u i j = 0) (a : X.IsAccretive) (b : ((1 - u) * X).IsAccretive) : l.flenstedJensen 1 ((1 - u) * X)ᴴ = conj (l.flenstedJensen 1 X) := have := b.det_ne_zero; have k : 1 - u ∈ _ := mem_blockDiagAlg.2 (by aesop); have := flenstedJensen_eq_of_accretive hg (one_mem _) (by simpa) k (by aesop); by simp_all [flenstedJensen, conj_weightMinors, mul_comm, mul_assoc, hg.isKDominant_lowestKType.weightMinors_oppBorel_mul hg.neg.1 _ k (by simp_all [IsBorelMatrix, BlockTriangular]; grind), diagChar, ← integral_conj]
open Polynomial Lagrange Real Calc MeasureTheory
lemma exists_lagrange_weights {M} {x : Fin M → ℤ} (hx : StrictAnti x) : ∃ c : _ → ℝ, (∀ k, 1 ≤ c k ∧ c k ^ 2 = (-1) ^ k.1 * ∏ j ∈ univ.erase k, (x k - x j : ℝ)) ∧ ∀ P : ℝ[X], P.degree < M → P.coeff (M - 1) = ∑ k, (-1) ^ k.1 * (P.eval (x k : ℝ) / c k ^ 2) := ⟨_, (⟨·, by simpa [*, mul_div_mul_left, mul_div] using fun P ↦ coeff_eq_sum (s := univ) (Int.cast_injective.comp hx.injective).injOn⟩) fun k ↦ (⟨one_le_sqrt.2 ·, sq_sqrt (by grind)⟩) (mod_cast by erw [← compl_singleton, ← Ioi_disjUnion_Iio, prod_disjUnion, ← Fin.card_Iio, mul_left_comm, ← prod_neg]; simp [Order.one_le_iff_pos, prod_pos, hx.lt_iff_gt])⟩
variable {n : _} [Fintype n]
class SignFrame (J ε : outParam _) where (p : GL n ℂ) (gram_eq : p.1ᴴ * J * p.1 = signMatrix ε)
variable {ε : _} {A J} {l : @HCParam n ε} [p : SignFrame J ε] [IsHermInvolution J]
def frameEquiv : U J ≃ₜ* USign ε := .mk (U.conj _ p.2).symm
def HCParam.psiInFrame (l : HCParam ε) (g : U J) := l.dsCoeff (frameEquiv g)
omit [IsHermInvolution J] in
@[fun_prop] lemma continuous_psiInFrame : Continuous l.psiInFrame := by fun_prop [HCParam.psiInFrame]
lemma measurePreserving_frameEquiv : MeasurePreserving (frameEquiv (p := p)) := measurePreserving_haarU _ p.1 1 _ (by simp [p.2]) (by tauto)
lemma integral_comp_frameEquiv {E} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : USign ε → E) : ∫ g, f (frameEquiv g) = ∫ g, f g := measurePreserving_frameEquiv.integral_comp frameEquiv.measurableEmbedding _
lemma isIdempotentKernel_psiInFrame [Nonempty n] (hg : l.HasLargeGap A) : IsIdempotentKernel (l.formalDegree * l.psiInFrame ·) := have h := HCParam.HasLargeGap.isIdempotentKernel_dsKernel hg.neg; by simpa [dsKernel, formalDegree] using! show IsIdempotentKernel ((-l).dsKernel <| frameEquiv ·) by use by fun_prop, measurePreserving_frameEquiv.integrable_comp_of_integrable h.2 <;> simp [h.4, ← h.3, ← h.5, ← integral_comp_frameEquiv]
