import New.Trace.LabelRigidity
namespace Data
open Kf Matrix Module Submodule LinearMap Gf Finset SetLike GradeZero Fint
attribute [-instance] instCommRing instSemiring instCommSemiring GradeZero.instRing OneMemClass.one AddSubgroupClass.sub
seal eigenPart
variable {P} (D : Data P) {s s'} {V : Space D.E _ s} {V' : Space D.E _ s'} [∀ v, (toHCParam s (D.paramW v)).HasGap D.h] [∀ v, (toHCParam s' (D.paramW v)).HasGap D.h] (o : D.HasRigidLabels V) (o' : D.HasRigidLabels V')
attribute [local instance high] Finite.linearMap Finite.map FiniteDimensional.finiteDimensional_submodule in
lemma exists_common_hecke_rallis ϑ j {a a'} {B B' : _ → _ → ℂ} (h : ∀ z y, HasSum (a * D.rallisTerm ϑ j V z y ·) (B z y)) (h' : ∀ z y, HasSum (a' * D.rallisTerm ϑ j _ z y ·) (B' z y)) : ∃ p : D.heckeAlgebra, (∀ z y, B z y = a * inner ℂ z (p.1 V y)) ∧ ∀ z y, B' z y = a' * inner ℂ z (p.1 V' y) := by
  let Φ {s} V : End ℂ (@D.principalForms _ s V) →ₗ[ℂ] _ := .pi fun z ↦ .pi (innerₛₗ ℂ z ∘ₗ applyₗ ·); simp_rw [← Pi.hasSum] at *; refine ((h.prodMk h').tsum_eq ▸ tsum_mem (((proj V ∘ₗ proj s).prod (proj V' ∘ₗ proj s') ∘ₗ D.heckeAlgebra.val.toLinearMap).range.map ((a • Φ V).prodMap (a' • Φ V'))).closed_of_finiteDimensional fun i ↦ ?_).elim (by rintro _ ⟨⟨p, ⟨⟩⟩, ⟨⟩⟩; tauto); have f {s V} (y : @D.principalForms _ s V) := by simpa using (y.2 ·)
  let r := cosetRep i; let H := (D.chosenLevel.comap (MulAut.conj r.1⁻¹).toMonoidHom).subgroupOf D.chosenLevel; have := H.fintypeOfIndexNeZero (IsLevel.isCompact.relIndex_ne_zero ((IsTopologicalGroup.continuous_conj _).1 _ isOpen_levelOf))
  exact ⟨_, ⟨(_ / _ / this.card : ℂ) • ⟨fun V ↦ .restrict _ fun y hy ↦ by
    simpa [f ⟨y, hy⟩] using sum_out_mul H (fun k ↦ V.formRep _ (k * r) y) (fun k _ h ↦ by
    simpa using congr(V.formRep _ (k * r) $(f ⟨y, hy⟩ _ h))), ∑ q : _ ⧸ H, .single ⟨q.out * r * q.out⁻¹, mem_trivialOn.2 fun _ ⟨x, e⟩ ↦ by simp [mem_supportedOn.1 r.2, places_levelModulus (S := D.levelPlaces ϑ).ge ⟨.inl x, e⟩]⟩ 1, fun _ _ _ ↦ rfl⟩, rfl⟩, by ext <;> simp [Φ, f, rallisTerm, cosetTerm, inner_sum, fun s V ↦ (@f s V · · · ▸ V.inner_formRep _ _), mul_comm_div, mul_div_assoc] <;> apply mul_left_comm⟩
include o o'
lemma d2 p : trace ℂ _ (D.heckeOnGood V p) = trace ℂ _ (D.heckeOnGood V' p) := by
  let F := ((D.m8 V ⊤).union (D.m8 V' ⊤)).toFinset; choose π hb using (D.k9 · F); choose b e using (p * π · |>.2); choose Q l c using fun q w ↦ (s23_p8 (D.card_rowIndex.trans D.r_pow.choose_spec) (D.dvd_card_resField_sub_one w).1 · (o q w) (o' q w))
  have E {s} W [Module.Finite ℂ (@D.principalForms _ s W)] (m : D.occurringLabels W ≤ D.occurringLabels V ⊔ D.occurringLabels V' ∧ ∀ d ∉ F, D.eigenPart W d = ⊥ := by simp +contextual [F, top_inf_eq]) : trace ℂ _ (D.heckeOnGood W p) =
    trace ℂ _ (∑ q ∈ F, (p * π q).1 W * (D.principalRep W).asAlgebraHom (D.e₀ - ∑ c ∈ D.goodTupleFamilies, tupleIdem D.RowIndex fun w ↦ Q q w (c w))) := ((trace_comp_comm' (rangeRestrict _) ((goodForms ..).subtype ∘ₗ _)).trans (congrArg _ (ext fun _ ↦ (D.isCentralProj_e₀.1.map _).isProj_range.codRestrict_apply_cod _))).symm.trans
    (congrArg _ (eqLocus_eq_top.1 (top_unique (D.iSup_eigenPart W ▸ iSup_le fun d v e ↦ by
    cases em' (d ∈ F); simp_all; simp [-map_sub, hb _ d, principalRep_mem_eigenPart, *, apply_ite]; simp; rw [← map_sum, sum_eq_zero fun c h ↦ ((mem_filter.1 (Fintype.mem_piFinset.1 (mem_map_equiv.1 h) 0)).2.2.imp (l d ⟨0, ·⟩ _)).elim fun w a ↦ piTensorElem_apply_eq_zero _ (by_contra (a.2 <| m.1 d _ ⟨a.1, v, e, ·⟩))]; simp; rfl))))
  simp [E V, E V', trace_eq_sum_inner _ (stdOrthonormalBasis ..), ← e, asAlgebraHom_eq_sum_support, inner_sum, inner_smul_right, univ.sum_comm, ← mul_sum, -MulMemClass.coe_mul]; congr! 5 with q _ g h k; let ⟨i, hi⟩ : ∃ i, Irreducible (g i).1.charpoly := by contrapose! h; simp [e₀, tupleIdem, ← c, h]
  refine (Space.exists_trace_eq (h := k.1 * _) (B := D.h₂) (by cases D.m_pow; simp [towerDeg, P.card_infinitePlace_E, parity_simps, *]) (finrank_eq_two_mul_card_infinitePlace D.E ▸ D.nat_le_of_hasLogBound) ?_ _ D.h D.le_of_hasLogBound).elim fun _ Z ↦ by
    simp at Z; erw [Z, Z] <;> apply_rules [isCuspKernel_paramW]
  rintro _ ⟨_, ⟨b, hb, ⟨⟩⟩, ⟨⟩⟩; obtain ⟨t : GL _ (LocInt _), ht⟩ := mem_Kf_iff.1 (liftResidue g * b).2 (D.chosen i); erw [← mul_one g, ← hb, ← reduceFamily_liftResidue g, ← map_mul, show reduceFamily _ _ i = _ from reduceAt_eq_of_atPlace ht.symm, charpoly_map] at hi; constructor; erw [← ht.trans (c := Gf.atPlace _ _) (by simp [mem_trivialOn.1 k.2]), charpoly_map]; exact t.1.charpoly_monic |> fun m ↦ m.irreducible_iff_irreducible_map_fraction_map.1 (m.irreducible_of_irreducible_map _ _ hi)
lemma det_heckeOnGood_eq p : (D.heckeOnGood V p).det = (D.heckeOnGood V' p).det := by simp [← det_toMatrix (finBasis ℂ (D.goodForms V)), ← det_toMatrix (finBasis ℂ (D.goodForms V')), det_eq_prod_roots_charpoly]; congr 2; apply (charpoly_eq_mul_of_trace_pow_add _ ∅ id _).trans (by simp; rfl); simp [toMatrix_pow, ← trace_eq_matrix_trace, ← map_pow, D.d2 o o']
lemma s23_c7 {q} (e : D.goodForms V' ⊓ D.eigenPart _ q = ⊥) : D.goodForms V ⊓ D.eigenPart V q = ⊥ := (D.k9 q (D.m8 V' ⊤).toFinset).elim fun π h ↦ bot_unique fun y a ↦ congr($(ker_eq_bot'.1 (equivOfDetNeZero _ (((D.det_heckeOnGood_eq o o' (1 - π)).trans (congrArg _ (a₂ := 1) (ext fun z ↦ Subtype.ext (sub_eq_self.2 (e.le ⟨(D.heckeOnGood _ π z).2, mem_comap.1 (((iSup_ne_bot_subtype _).trans (iSup_eigenPart ..)).ge.trans (iSup_le fun d v a ↦ by
  simpa [h d, a, top_inf_eq, ite_mem] using (· ▸ a)) ⟨⟩)⟩))))).trans_ne (by simp))).ker ⟨y, a.1⟩ (Subtype.ext (sub_eq_zero.2 (by simp [h q _ y a.2])))).1)
omit o o'
lemma finrank_rows_eq_finrank_goodForms (j : D.LiftIndex) : D.rowDim = finrank ℂ (D.goodForms (D.spaceW j)) := by simpa using D.d2 D.hasRigidLabels_spaceY_zero (D.hasRigidLabels_spaceW j) 1
