import Lib.PadicHodge.PeriodRings.CpIntegers
import Lib.ClassField.Places.UnramifiedCharacters
open Nat Polynomial Finset InfiniteGalois IntermediateField IsAlgClosed IsPrimitiveRoot IsUltrametricDist Multiset Padic PadicComplex Real UniformSpace.Completion
variable {F} [NormedField F] [IsUltrametricDist F] {ζ : F} {p : ℕ} [Fact p.Prime]
lemma norm_pow_sub_one_le_norm_sub_one (h : ‖ζ‖ ≤ 1) a : ‖ζ ^ a - 1‖ ≤ ‖ζ - 1‖ := (Valuation.integer.integers NormedField.valuation).le_of_dvd (sub_one_dvd_pow_sub_one ⟨ζ, h⟩ a)
lemma norm_zeta_sub_one_pow {m} (h : IsPrimitiveRoot ζ (p ^ (m + 1))) : ‖ζ - 1‖ ^ φ (p ^ (m + 1)) = ‖(p : F)‖ := by simp [← eval_one_cyclotomic_prime_pow m, cyclotomic_eq_prod_X_sub_primitiveRoots h, eval_prod]; grind [prod_eq_pow_card, card_primitiveRoots, mem_primitiveRoots, isOfFinOrder, norm_sub_rev, isPrimitiveRoot_iff, IsOfFinOrder.norm_eq_one, norm_pow_sub_one_le_norm_sub_one]
lemma pow_le_norm_aeval {K L} [Field K] [IsAlgClosed K] [NormedField L] [Algebra K L] (f : K[X]) x {r} (hr : 0 ≤ r) (h : ∀ w ∈ f.roots, r ≤ ‖x - algebraMap K L w‖) : ‖algebraMap K L f.leadingCoeff‖ * r ^ f.natDegree ≤ ‖aeval x f‖ := by nth_rw 3 [(splits f).eq_prod_roots]; simp [← normHom_apply, map_multiset_prod]; grw [← prod_map_le_prod_map₀ fun _ ↦ r] <;> simp_all [card_roots_eq_natDegree]
lemma ax_exists_near_fixed (J : Subgroup (Gp p)) {x : ℂ_[p]} (hx : ∀ g ∈ J, g • x = x) : x ∈ closure (coe' '' fixedField J) := SeminormedAddCommGroup.mem_closure_iff.2 fun ε _ ↦ by_contra fun _ ↦
  have H {k} : ∀ S, #(toFinset S) ≤ 2 ^ k → (∀ g ∈ J, ∀ z, z ∈ S ↔ g z ∈ S) → ∀ z ∈ S, ε / 16 * 2 ^ ((2 * k.cast + 4) / 2 ^ k : ℝ) ≤ ‖x - z‖ := k.rec (by simp_all [card_le_one]; grind) fun k ih S h _ z _ ↦ le_of_pow_le_pow_left₀ k.two_pow_pos.ne' (by simp) (by
    let T := S.toFinset.filter (‖x - coe' ·‖ = ‖x - z‖); let f := ∑ t ∈ T, (X - C t) ^ 2 ^ k
    have hf : f.coeff (2 ^ k) = (#T : ℚ_[p]) := by
      simp [f, sub_eq_add_neg, ← map_neg, coeff_X_add_C_pow]
    have hT : T.Nonempty := ⟨z, by grind⟩; have := natDegree_eq_of_le_of_coeff_ne_zero (by
      simp [f, natDegree_sum_le_of_forall_le]) (hf.trans_ne (by aesop))
    apply ((pow_le_norm_aeval f _ (by bound) (ih _ (by grind [toFinset_card_le, card_roots']) (by
      simp [f, eval_finsetSum]; introv _ _; rw [← map_eq_zero g, map_sum, sum_equiv g.1] <;> simp; grind [smul_coe_Cp, dist_smul, =_ dist_eq_norm]))).trans (by simp_all [f, T, ← coe_eq, norm_sum_le_of_forall_le_of_nonneg])).trans'; simp_all [hT.ne_empty, leadingCoeff, -map_natCast, norm_eq_zpow_neg_valuation, le_inv_mul_iff₀', NeZero.pos]
    nth_grw 1 [← cast_pow, le_of_dvd hT.card_pos pow_padicValNat_dvd, card_filter_le, h]
    simp [mul_pow, ← rpow_mul_natCast, ← rpow_add_natCast, field]; ring; rfl)
  (denseRange_coe.exists_dist_lt x (by bound : 0 < ε / 16)).rec fun z ↦ by
   grw [dist_eq_norm, ← H ((minpoly ℚ_[p] z).aroots _) lt_log2_self.le] <;> simp (disch := bound) [one_le_rpow, aeval_algEquiv, minpoly.ne_zero_iff, IsGalois.integral]
lemma exists_algebraic_of_fixed_near_one {x : ℂ_[p]} (hx : ∀ᶠ g : Gp p in nhds 1, g • x = x) : ∃ y, x = coe' y := ((krullTopology_mem_nhds_one_iff ..).1 hx).elim fun E ⟨_, h⟩ ↦ ((E.toSubmodule.map toComplL.1).closed_of_finiteDimensional.closure_subset (fixedField_fixingSubgroup E ▸ ax_exists_near_fixed _ h)).imp (by tauto)
open Subtype decompGroup MulSemiringAction PadicInt Set Topology
variable {p : _} [Fact (Nat.Prime p)] (ι : Ω →+* PadicAlgCl p) {K} [Field K] {Γ} [Group Γ] [TopologicalSpace Γ] (e : K →+* PadicAlgCl p) (j : Γ →* Gp p)
lemma valuation_comap_intQpBar_lt_one : ((intQpBar p).comap ι) p < 1 := by simp [val_comap_lt_one, _root_.norm_p_lt_one]
lemma residueCard_padic : residueCard ℚ_[p] (intQpBar p) = p := (Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv (.subringCongr (t := subring p) (by aesop))).trans residueField).1).trans (by simp)
instance isLocalGalois_padic : IsLocalGalois (Gp p) ℚ_[p] (intQpBar p) := ⟨fun g ↦ mem_decompGroup_iff.2 (by simp [← nndist_zero_right, ← nndist_smul g ·]), (congrArg (a₁ := subring p) (IsDiscreteValuationRing ·) (by aesop)).mp instIsDiscreteValuationRing, (Nat.card_ne_zero.1 (residueCard_padic.trans_ne NeZero.out)).2⟩
lemma pClos {F} [NormedField F] [PadicField F p] (S : Subfield F) x : algebraMap ℚ_[p] F x ∈ S.topologicalClosure := map_mem_closure (by fun_prop) (x.denseRange_ratCast _) (by simp)
lemma denseRange_emb_padicAlgCl : DenseRange ι := isDenseInducing_coe.dense_iff.2 (let L := Subfield.toIntermediateField _ (pClos (coeRingHom.comp ι).fieldRange); range_comp .. ▸ (IsGalois.integral _ · |>.algebraMap.mem_intermediateField_of_minpoly_splits ((@IsAlgClosed.of_denseRange Ω L _ _ isClosed_closure.completeSpace_coe _ _ (RingHom.codRestrict _ L (subset_closure ⟨·, rfl⟩)).toAlgebra (dense_iff.2 (range_comp .. ▸ .rfl)) _).1 _)))
def IsCompletionGroup := IsOpenEmbedding j ∧ ∀ g, g ∈ j.range ↔ ∀ x, g (e x) = e x
lemma isLocalGalois_localFieldOf {j : Γ →* Gp p} (hj : IsOpenEmbedding j) : let := compHom (PadicAlgCl p) j
  IsLocalGalois Γ (fixedFieldOf j.range) (intQpBar p) := by intro; exact
  { IsClosedEmbedding.compactSpace ⟨hj.1, j.range.isClosed_of_isOpen hj.2⟩, hj.topologicalGroup, hj.toHomeomorph.symm.totallyDisconnectedSpace, IsGaloisGroup.of_mulEquiv (j.ofInjective hj.1.2) (by tauto), (isLocalGalois_padic.of_finite (id ⟨j.range, hj.2⟩)).1 with mem_decompGroup g := isLocalGalois_padic.4 _, isOpen_stabilizer x := hj.continuous.1 _ (isLocalGalois_padic.1.6 x) }
def InducesPlace [MulSemiringAction Γ Ω] K [Field K] [Algebra K Ω] (A : ClosurePlace) e (j : decompGroup Γ A →* Gp p) := ((intQpBar p).comap e = A ∧ ∀ g x, j g (e x) = e (g.1 • x)) ∧ IsCompletionGroup (e.comp (algebraMap K Ω)) j
variable (K Γ) [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
lemma exists_inducesPlace [NumberField K] {ι A} (h : (intQpBar p).comap ι = A) : ∃ j, InducesPlace (Γ := Γ) K A ι j := h ▸ let U := id (OpenSubgroup.mk _ (adjoin ℚ_[p] (Set.range (ι.comp (algebraMap K Ω)))).fixingSubgroup_isOpen)
  have ⟨⟨f, c⟩, hf⟩ := exists_galois_restrict Γ U.1 ι
  let e := (f.ofInjective fun g h e ↦ Subtype.coe_injective (eq_of_smul_eq_smul
    ((denseRange_emb_padicAlgCl ι).eq (hf g · ▸ e ▸ hf ..)))).trans (.subgroupCongr (le_antisymm (fun _ ⟨o, k⟩ ↦ k ▸ decompGroup.map hf <| isLocalGalois_padic.4 o.1) fun σ s ↦ fixingSubgroup_fixedFieldOf _ (h := (isCompact_range c).isClosed).le fun ⟨x, m⟩ ↦ ι.injective (dist_le_zero.1 (_root_.dist_self (ι x) ▸ le_on_closure (by simp [dist_eq_norm, ← valuation_intQpBar_le_iff, ← map_sub, ← Valuation.comap_apply, ← isEquiv_comap _, ← val_smul s (x - _), smul_sub]) (by fun_prop) (by fun_prop) (adjoin_le_subfield _ _ (fun _ ⟨o, k⟩ ↦ k ▸ pClos (RingHom.fieldRange _) o) subset_closure
    ((fixedFieldOf_fixingSubgroup _).le (hf · x ▸ congrArg ι (m ⟨_, _, rfl⟩))))))))
  ⟨U.1.subtype.comp e.symm, by simpa [↓e.surjective.forall, eq_comm] using! hf, U.2.isOpenEmbedding_subtypeVal.comp ((c.subtype_mk _).homeoOfEquivCompactToT2 (f := e.1)).symm.isOpenEmbedding, by simp [U, MonoidHom.range_comp, ← AlgEquiv.smul_def, forall_mem_adjoin_smul_eq_self_iff]⟩
