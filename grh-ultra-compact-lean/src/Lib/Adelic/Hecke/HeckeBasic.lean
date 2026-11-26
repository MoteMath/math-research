import Lib.General.LinearAlgebra.PartialDerivComm
open Set Classical Function HasFiniteSupport DoubleCoset QuotientGroup Finset
variable {A G W W'} [Group G] [CommSemiring A] [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W'] {π} (K K' : Subgroup G) {χ' : K' →* A} (f : G → A) {v : W} {G'} [Group G']
abbrev HasFiniteCosets := (@support (G ⧸ K) A _ (f ·.out)).Finite
abbrev IsBiInvariant := HasFiniteCosets K f ∧ ∀ᵉ (g) (k ∈ K), f (g * k) = f g ∧ f (k * g) = f g
variable {K K' f} {J : Subgroup G'} {F} (a : G' →* G) (L : W →ₗ[A] W') (h : HasFiniteCosets K f) {π'} (hf : ∀ g (k : K), f (g * k) = f g) (hf' : ∀ g k, χ' k * f (k * g) = f g) (h1 : v ∈ levelSpace (A := A) π K)
lemma heckeFun_sum v : heckeFun π K f v = ∑ q ∈ h.toFinset, f q.out • π q.out v := by
 rw [heckeFun, finsum_eq_sum_of_support_subset] <;> aesop
attribute [local simp] indicator heckeFun_sum mem_doubleCoset
include h in lemma map_heckeFun : (∀ g, L (π g v) = π' g (L v)) → L (heckeFun π K f v) = heckeFun π' K f (L v) := by aesop
lemma levelSpace_anti : K ≤ K' → levelSpace π K' ≤ levelSpace π K := by aesop_cat
attribute [local simp ←] mul_assoc smul_finsum' smul_smul
lemma isBiInvariant_doubleCoset [TopologicalSpace G] [IsTopologicalGroup G] (hK : @IsOpen G _ K) [CompactSpace K] g : IsBiInvariant K (@indicator _ A _ (doubleCoset g K K) 1) := ⟨(finite_quotient_image_of_isCompact hK (by
 apply_rules [IsCompact.mul, isCompact_iff_compactSpace.2])).subset fun q a ↦ ⟨_,
 support_indicator_subset a, q.out_eq⟩, fun _ _ _ ↦ ⟨by simp_all [← inv_mul_eq_iff_eq_mul,
 mul_mem_cancel_right], by simp_all [← mul_inv_eq_iff_eq_mul, mul_assoc, mul_mem_cancel_left]⟩⟩
include hf h1
lemma heckeFun_eq_sum {ι s} {r : ι → G} (hr : InjOn (@mk _ _ K <| r ·) (SetLike.coe s)) (hs : ∀ g, f g ≠ 0 → ∃ i ∈ s, (r i : G ⧸ K) = g) : HasFiniteCosets K f ∧ heckeFun π K f v = ∑ i ∈ s, f (r i) • π (r i) v := have H := (out_eq' · ▸ mem_image.2 ∘ hs _); ⟨(toFinite _).subset H, (axiomOfChoice (mk_out_eq_mul K)).rec (by simp_all [heckeFun,
 finsum_eq_sum_of_support_subset _ (H · ∘ left_ne_zero_of_smul)])⟩
lemma heckeFun_eq_sum_pullback s (θ : _ → G) (hθ : ∀ g, f g ≠ 0 → ∃ x, (θ x : G ⧸ K) = g) (H : ∀ a b, (θ a)⁻¹ * θ b ∈ K ↔ a⁻¹ * b ∈ J) (hs : ∀ q ∉ s, f (θ (q : _ ⧸ J).out) = 0) : HasFiniteCosets K f ∧ heckeFun π K f v = ∑ q ∈ s, f (θ q.out) • π (θ q.out) v := by
 apply heckeFun_eq_sum hf <;> simp_all [← QuotientGroup.eq, exists_mk]; peel hθ
 grind [@QuotientGroup.eq _ _ K, mul_inv_cancel_left, Quotient.out_eq]
lemma heckeFun_comp (hF : HasFiniteCosets J F) (ha : Surjective a) (hK : ∀ g, a g ∈ K ↔ g ∈ J) {ρ} (hρ : ∀ g, ρ g v = π (a g) v) (e : ∀ g, F g = f (a g)) : heckeFun ρ J F v = heckeFun π K f v := by simp_all [heckeFun_eq_sum_pullback _ _ hF.toFinset a (ha.forall.2 _), ← hK]
include h
lemma apply_heckeFun x : HasFiniteCosets K (f <| x⁻¹ * ·) ∧ heckeFun π K (f <| x⁻¹ * ·) v = π x (heckeFun π K f v) := by simp_all [heckeFun_eq_sum_pullback _ h1 h.toFinset (x * ·) (fun _ ↦ ⟨x⁻¹ * ·, _⟩)]
lemma heckeFun_heckeFun {f'} (h' : HasFiniteCosets K f') : heckeFun π K f' (heckeFun π K f v) = heckeFun π K (fun x ↦ ∑ q ∈ h'.toFinset, f' q.out * f (q.out⁻¹ * x)) v := have := apply_heckeFun h hf h1; by simp_all [↓heckeFun_sum, heckeFun, sum_smul, finsum_sum_comm, fun_smul_left (this _).1, fun_smul_right]
include hf'
lemma heckeFun_mem_levelSpace : heckeFun π K f v ∈ levelSpace π _ χ' := (by
 simp [↓← (apply_heckeFun h hf h1 _).2, heckeFun, ← hf' (_ * _) ·, fun_smul_left h])
omit h hf hf'
lemma IsBiInvariant.heckeFun_mem (hb : IsBiInvariant K f) : heckeFun π K f v ∈ levelSpace π K := by simp_all [↓heckeFun_mem_levelSpace]
