import Lib.General.Analysis.OstrowskiTaussky
seal Finset.univ Finset.sum Finset.prod
open NumberField Matrix Submodule Polynomial Finset Lagrange Multiset Set SetLike Fintype
variable {a ι S K R} [Fintype ι] [Fintype S] [Field K] [CommRing R] [Algebra K R]
lemma sum_lagrange_smul_rootCoeffEval (l : Fin a → ℕ) (r : Fin a ↪ K) : ∑ i, aeval (X * C (r i)) (Lagrange.basis univ r i) • rootCoeffEval (univ.1.map fun k ↦ ite (k = i) X 1 * C (r k)) (genericSchur l) = C (rootCoeffEval (univ.1.map r) (genericSchur l)) * ∑ j, X ^ l j := by
 erw [← rootCoeffEval_map, Multiset.map_map, ← mul_left_inj' (det_vandermonde_ne_zero_iff'.2 (C_injective.comp r.2)), mul_right_comm, rootCoeffEval_genericSchur_mul_det, sum_mul]
 simp_rw [smul_mul_assoc, ← mul_smul_comm]
 refine .trans (sum_congr _ _ fun i ↦ (congrArg _ ?_).trans (rootCoeffEval_genericSchur_mul_det ..)) (by simp [← Equiv.eq_symm_apply, det_apply', sum_comm, ← mul_sum, sum_mul, -ite_mul, mul_assoc, X_pow_mul, mul_pow, Equiv.sum_comp _ (X ^ l ·)])
 rw [← det_updateRow_sum _ i fun _ ↦ aeval _ _]
 congr with k j; have := congr(aeval (X * C (r i)) $(eq_interpolate r.2.injOn (by simp : degree (X ^ ↑j) < #univ))); by_cases k = i <;> simp_all [mul_comm (_ ^ _)]
open MvPolynomial RingOfIntegers Finsupp ComplexConjugate Fint
omit [Fintype ι] in lemma algebraicIndependent_emb {E} [Field E] [NumberField E] : AlgebraicIndependent ℂ fun (p : ι × (E →+* ℂ)) (α : ι → _) ↦ p.2 (2 * α p.1 : 𝓞 E) := algebraicIndependent_iff.2 fun P h ↦ funext fun v ↦ let b := canonicalEmbedding.latticeBasis E; by simpa [aeval_bind₁, two_mul, by simpa [↓funext_iff] using b.sum_repr] using congr(aeval (fun p ↦ b.repr (v ⟨p.1, ·⟩ / 2) p.2) $((funext_set _ (fun _ ↦ infinite_range_of_injective Nat.cast_injective) (by simpa [← range_piMap, ← aeval_eq_eval, aeval_bind₁, b, two_mul, comp_aeval_apply] using fun z : _ × _ → ℕ ↦ (congr(Pi.evalAlgHom ℂ _ (∑ k, z ⟨·, k⟩ * basis E k) $h))) : P.bind₁ (fun (i, σ) ↦ 2 • ∑ k, .X (i, k) * .C (b k σ)) = 0)))
lemma map_prod_rootCoeffEval_eq_zero {A} {q : S → MvPolynomial (Fin a) ℤ} (hι : ∀ σ, (q σ).totalDegree ≤ card ι) {c : ι × S → A → K} (hc : AlgebraicIndependent K c) {J} {x : J → S → _} (hx : ∀ j σ, (x j σ).card = a) (L : _ →ₗ[K] K) (h : ∀ α, L (fun j ↦ ∏ i, ∏ σ, ((x j σ).map (1 - algebraMap K R (c (i, σ) α) * ·)).prod) = 0) : L (fun j ↦ ∏ σ, rootCoeffEval (x j σ) (q σ)) = 0 := by
 let e σ (k : Fin a.succ) j := (-1) ^ k.1 * (x j σ).esymm k
 rw [← prod_fn]; refine (show ∏ σ, ∏ _ : ι, span K (.range (e σ)) ≤ L.ker by
  simp [↓← prod_prod_type_right', prod_span, span_le, ← image_fintype_prod_pi, ← range_piMap]
  exact linearIndependent_iff.1 (((basisMonomials _ K).linearIndependent.map_injOn (MvPolynomial.aeval c).toLinearMap hc.injOn).comp _ (equivFunOnFinite.4.injective.comp Fin.val_injective.comp_left)) _ (by
   simpa [funext_iff, ↓← prod_prod_type', prod_univ_sum, prod_smul, ← sum_fn, mul_comm, e, ↓← Algebra.smul_def, ← Pi.smul_def, prod_fn, aeval_eq_eval₂Hom, fun j σ (c : K) ↦ by simpa [eval_multiset_prod, sum_range, eval_finsetSum, hx, ← pow_smul_esymm] using congr($(((x j σ).map (c • ·)).prod_X_sub_X_eq_sum_esymm).eval 1)] using h)) (prod_hom_rel ⟨1, by simp⟩ fun σ _ _ ↦ mul_mem_mul ?_)
 simp [rootCoeffEval, aeval_eq_eval₂Hom, eval₂_eq', ← sum_fn, ← zsmul_eq_mul]
 refine sum_mem fun d h ↦ zsmul_mem (le_def.1 (pow_le_pow_right' (one_le.2 (subset_span (.intro 0 (by ext; simp [e, Multiset.esymm])))) ((le_totalDegree h).trans (hι σ))) ?_) _
 simpa [sum_fintype, prod_fn, prod_X_sub_C_coeff, *, e] using prod_pow_mem_graded (span K (.range (e σ)) ^ · :) 1 (e σ ·.castSucc.rev) d (by simp [mem_span_of_mem])
attribute [simp↓ low] finsum_eq_sum_of_fintype
variable {G} [Group G] [Finite G] (f h : G → ℂ)
noncomputable def finMean := finsum f / Nat.card G
noncomputable def classInner := finMean fun g ↦ starRingEnd ℂ (f g) * h g
@[simps] noncomputable def groupAlgElem : MonoidAlgebra ℂ G := ⟨Finsupp.equivFunOnFinite.symm f⟩
def IsChar := ∃ V : FDRep ℂ G, V.character = f
@[simp] abbrev IsClassFunction := ∀ g x, f (x * g * x⁻¹) = f g
def IsIrrChar := IsChar f ∧ classInner f f = 1 ∧ ∀ h, IsClassFunction h → ∀ y, f 1 * finMean (fun t ↦ starRingEnd ℂ (f t) * h (t * y)) = classInner f h * f y
variable {α β} {ι : _} [Finite α] [Finite β] {f : α → ℂ} {g}
attribute [local simp] finMean Finset.mul_sum sum_prod_type sum_div Equiv.sum_comp
omit [Finite α] in lemma finMean_eq [Fintype α] : finMean f = (∑ x, f x) / Fintype.card α := by simp
@[simp] lemma finMean_const_mul c : finMean (c * f ·) = c * finMean f := by simp [mul_div]
lemma finMean_sum s (f : ι → α → ℂ) : finMean (∑ i ∈ s, f i ·) = ∑ i ∈ s, finMean (f i) := by simp [s.sum_comm]
@[simp] lemma finMean_const [Nonempty α] c : @finMean α (fun _ ↦ c) = c := by simp
lemma finMean_conj : finMean (conj <| f ·) = conj (finMean f) := by simp
lemma finMean_equiv (e : β ≃ α) (h : ∀ x, f (e x) = g x) : finMean f = finMean g := by simp [← h, card_congr e]
lemma finMean_prod f : @finMean (α × β) f = finMean fun x ↦ finMean (f ⟨x, ·⟩) := by simp; grind
lemma finMean_comp_surjective [AddGroup α] [AddGroup β] (p : α →+ β) (hp : (⇑p).Surjective) f : finMean (f <| p ·) = finMean f := finMean_equiv (f := (f ·.1)) (.trans (.symm (.sigmaFiberEquiv p)) (.sigmaEquivProdOfEquiv (p.fiberEquivKerOfSurjective hp))) (by tauto) ▸ by simp [finMean_prod, -finMean]
