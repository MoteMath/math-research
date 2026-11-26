import New.Filling.FillingTheorem
seal Finset.univ Finset.sum Finset.prod
open Finset Function Gf IsTopologicalGroup MeasureTheory MulAction ProbabilityTheory TensorChain
namespace Data
seal SmoothForm chain
variable {P} (D : Data P)
lemma d3 k hk : let Y := q6 k hk; ∃ A, IsLevel A ∧ D.columnLevel k ≤ A.comap
    Y.inclXFin ∧ ∀ ϑ, ∃ T : Finset (_ ⧸ levelY ϑ k), (∀ p : Y.besselFin, ↑p ∈ A → ∀ t, t ∈ T ↔ p • t ∈ T) ∧ (∀ ⦃x⦄, ⟦x⟧ ∈ T → x ∈ localLevel _ {w | ↑ϑ.levelNorm ∉ w.1} ∧ (k = 0 → x ∈ chosenLevel))
    ∧ ∀ x, (⟦x⟧ ∈ T ∨ ∃ φ ∈ D.ramifiedColumns, ∃ ξ y g, s22_z2 ϑ φ ξ y k hk.step Y (g, x) ≠ 0 ∧ y 0 ∈ chosenLevel) → ∃ j, q3 Y.besselFin A T ⟦x⟧ ∣ ϑ.levelNorm ^ j := by
  intro Y; simp_rw [← Subgroup.mem_iInf, ← Subgroup.mem_inf]
  obtain rfl | e := eq_or_ne k 0
  · exact ⟨D.chosenLevel, inferInstance, fun a h ↦ D.filling_fits.mem_stdPrincipalLevel_iff.2 (D.filling_fits.finiteEquiv_inclX (1, a) ▸ D.columnLevel_zero_eq_comap.le h), fun ϑ
      ↦ have b := (by simp [levelOf_le_Kf.trans Kf_le_localLevel]); s22_y0 (levelY_le_chosenLevel ..) IsLevel.isCompact
      b (fun x a ↦ ⟨b a, 0, fun u b ↦ by simp_all [mul_mem, levelY_le_chosenLevel _ _ b]⟩) fun x ⟨_,
        _, _, _, _, e, _⟩ ↦ (D.filling_fits.q9 _ e :)⟩
  choose b β hb using Y.k4
  have l {x y b β w} (h : Y.IsAdaptedAt y b β) (e : x.atPlace w = y.atPlace w) := (hb x).f6 h (by simpa)
  let Φ Q d i (w : ↥(star '' Q ∪ Q)) := ideleLogVal (β d i) w.1 - ideleLogVal (β 1 i) w.1
  have ⟨_, _, f, n⟩ := Y.g1 (D.z4 ..) le_rfl (x := 1) (Q := ∅) ⟨1, by simp⟩
  refine ⟨Kf .., inferInstance, fun _ ↦ (Y.d5 (D.z4 ..) D.piIdele_spec ·.2), fun ϑ ↦ s22_y0 levelOf_le_Kf (((Set.finite_Icc
    (-↑k) ↑k).image (componentOn _ ϑ.Q ∘ invFun (Φ ϑ.Q))).isCompact.mul isCompact_Kf) (by simp [e,
    Kf_le_localLevel]) (fun x ⟨_, ⟨y, _, rfl⟩, z, hz, d⟩ ↦ ⟨⟨fun w o ↦ by simp [← d, mem_Kf_iff.1 hz, not_or.1 (o <| D.levelNorm_mem_and_notMem_of_mem_Q ϑ · |>.1)],
    by simp [e]⟩, (ϑ.Q.eventually_all.2 fun w o ↦ (eventually_localCongruence_subset (((isOpen_Kw
    w).preimage (continuous_conj (x.atPlace w))).mem_nhds (by simp))).mono fun n H u (hu : u ∈ levelY ϑ k) ↦ H (pow_pow_mem_localCongruence (D.levelNorm_mem_and_notMem_of_mem_Q ϑ (.inl o)).1 (mem_localCongruence_zero.2 ⟨mem_Kf_iff.1 (levelOf_le_Kf hu) w, congrFun (mem_levelOf.1 hu).2 (.inr ⟨w, o⟩)⟩) n)).exists.imp fun n H u hu ↦ mem_Kf_iff.2 fun w ↦
    by_contra fun a ↦ a ?_⟩) fun x ⟨_, r, _, _, _, b, a⟩ ↦ (s22_k3 ϑ _
    _ ⟨_, r⟩ a _ _ _ b).elim fun _ ⟨_, g, o⟩ ↦ by clear * - o n l g f hb; exact
    (g.m1 (hb _) (by grind [l g, atPlace_componentOn, by
    simpa [funext_iff] using invFun_eq (f := Φ ϑ.Q) ⟨x, rfl⟩])).elim fun z a ↦ ⟨_, a.2, _, ⟨Φ _ x, by simp [Pi.le_def]; grind, rfl⟩, z, a.1, eq_mul_of_mul_inv_eq rfl⟩⟩
  simp [mem_Kf_iff.1 hz, ← d, mem_supportedOn.1 componentOn_mem_supportedOn w
    (a <| by simpa using H w · u hu) (a <| atPlace_star_mem_iff.1 <| by simpa using H _ · u hu),
    mul_mem, pow_mem (mem_Kf_iff.1 (levelOf_le_Kf hu) _)]
lemma k8 k l {X s} [Fintype X] (Y : Grading (D.spaceY k) _ X s) (hs : s = 2 * D.ϱ + 1 - k) (a : _ → ℂ) : ∃ κ, ∀ {ϑ} {M : ModuleCat ℂ} (S : (∀ i, _ ⧸ levelY ϑ i) → M), ∃ w, IsAdmissibleComb (fun y : ∀ i, localLevel _ {w | ↑ϑ.levelNorm ∉ w.1} ↦ S (⟦y · |>.1⟧)) .univ
  ϑ.levelNorm 1 (ϑ.Q = ∅) (D.f8 ^ k) w ∧ (∀ (b : ∀ i, D.columnLevel i) (ω : _ →ₗ[ℂ] _), (∀ q, ω (S q) = S fun i ↦ (if _ : i < k then (D.q6 i).inclXFin (b i) else 1) • q i) → ω w = w) ∧ ∀ (z : (D.spaceY k).Form (star (typeKernel (D.paramY k) _))) (φ : D.ramifiedColumns) (L : _ →ₗ[ℂ] _), (∀ ξ y, y (2 * D.ϱ + 2) = 1 → y 0 ∈ D.chosenLevel →
  let F := s22_z2 ϑ φ ξ y k l Y * z; Integrable F Y.ratBessel.qms → Y.ratBessel.qms[F] = a ξ * L (S (y ·))) → (D.spaceY k).quotMeasure[z * (liftChainY ϑ k (D.poincare φ)).1] = κ * L w := by
  subst hs; induction' k with k ih generalizing X a
  · exact ⟨a 1, fun S ↦ ⟨_, .single 1 trivial, by simp +contextual, fun z φ L H ↦ .trans
      (D.filling_fits.poincareMap.2 _ ▸ (D.filling_fits.integral_poincare _ le_rfl z.2).2 :) ((D.filling_fits.integral_poincare _ inf_le_left z.2).symm.elim (·.symm.trans <| (mul_comm _ z.1 ▸ H 1 1 rfl (one_mem _)) ·))⟩⟩
  choose A hA hA' T c₁ c₃ c₄ using D.d3 k (by omega)
  let Y := D.q6 k
  choose κ H₂ using fun ξ ↦ Y.p5 A (a <| update ξ k ·)
  refine (ih (by omega) κ Y).imp fun _ H ϑ _ S ↦ (H fun y ↦ ∑ t ∈ T ϑ, (q3 Y.besselFin A (T ϑ) t : ℂ)⁻¹ • S (update y k t)).imp fun w ↦
    .imp (·.bind 1 D.f8 (fun y _ ↦ .of_eq_isOfFinOrder_smul (.of_sum (Quot.ind fun t a ↦ div_mem_integralAway ((c₄ ϑ t (.inl a)).choose_spec.mul_left 1)) fun e _ ↦ ?_) (Quot.ind fun t a ↦ ⟨1, .one, _, trivial, ((one_smul ..).trans congr(S $(funext (apply_update (fun _ x ↦ ⟦x.1⟧)
    y k ⟨t, (c₃ ϑ a).1⟩)))).symm⟩)) dvd_rfl (by simp [pow_succ])) (.imp (fun H b ω e ↦ H b ω fun y ↦ ?_) fun H z φ L G ↦ (isArrow_datumY ϑ (D.m_eq_two_mul_varrho_add_two ▸ l)).elim fun A B ↦ ?_)
  · refine .trans (by erw [mul_comm ?z.1, mul_smul_comm, ← smul_mul_assoc]; exact (A.integral_mul_formLift_swap B _ ((_ : ℂ) • _))) (H ?z φ L fun ξ y y₁ y₀ h ↦ (H₂ ξ (L <| S <| update (y ·) k ·) (s22_w7 ..)
      ?z.2.1 h (c₁ ϑ) (fun g e ↦ ne_zero_of_dvd_ne_zero (by simp [prod_eq_zero_iff]) (c₄ ϑ _ (.inr ⟨φ, φ.2, ξ, y, _, left_ne_zero_of_mul e, y₀⟩)).choose_spec) fun t i ↦ .trans ?_ (congrArg _ ((Grading.integral_besselGroup_unfold _ _ _ (s22_w7 ..) _ z.2.1 (B _).1.2).elim fun j ↦ (·.trans (funext (apply_update (fun _ ↦ (⟦·⟧)) y k t.2) ▸ G _ _
      (by simp [Nat.ne_of_gt l, y₁]) (by cases k <;> simp [c₃ ϑ i, *]) j))))).trans (by simp))
    simp [f3]; rw [← integral_const_mul]; congr; ext; erw [mul_left_comm, B.coe_formLift]; rfl
  · grw [sum_le_card_nsmul _ _ 1, nsmul_eq_mul, ← Nat.card_eq_finsetCard, (relIndex_principalLevel_le D.piGBar_ne_zero).trans' (Finite.card_le_of_injective' (f := fun t ↦ ⟦⟨t.1.out, by simpa [e, mem_Kf_iff, localLevel, Ideal.one_notMem] using (c₃ ϑ
      (by simp)).1⟩⟧) (fun _ _ d ↦ by simpa using QuotientGroup.eq.2 (D.chosenLevel_inf_trivialOn_le
      ϑ ⟨D.principalLevel_le_chosenLevel dvd_rfl (QuotientGroup.eq.1 d :), by
      simp [e]⟩)) (absurd · (have := Fact.mk D.piGBar_ne_zero; relIndex_ne_zero_of_isLevel _))), s22_b6, ← pow_mul, card_Y_le] <;> simp [m_eq_two_mul_varrho_add_two, Nat.cast_inv_le_one, NeZero.pos]; omega
  simp [e]
  refine sum_equiv (toPerm _) (c₁ ϑ ⟨_, Y.snd_mem_besselFin (Y.inclX_mem_besselGroup _)⟩ (hA' (b k).2)) fun t _ ↦ congr(($(s22_v1 _ _ t) : ℂ)⁻¹ • S $(update_eq_iff.2 ?_)).symm
  simp +contextual [le_iff_lt_or_eq]; rfl
lemma seesaw : ∃ c : ℂˣ, ∀ ϑ, ∃ Ψ, IsGoodDatum ϑ Ψ ∧ ∀ φ, ι ϑ (D.poincare ((c.1 • D.ramifiedColumns.subtype) φ)) = Bμ ϑ Ψ φ := by
  choose C hC using D.j7
  choose R B c A using D.exists_last_stage_map D.m_eq_two_mul_varrho_add_two
  choose T H using (g8 · _ .refl _ (by simp [n2]; rfl) 1)
  choose a w s₁ s₂ G using D.k8 _ le_rfl
    (D.lastGrading D.m_eq_two_mul_varrho_add_two) (by omega) (c ∘ T)
  refine ⟨normUnit (a * C / (D.f8 ^ (2 * D.m))), fun ϑ ↦ (D.p4 ϑ (.normUnit_smul a NeZero.out ((s₁ fun q ↦ pure (z0 ϑ (q · |>.out)) _).bind _ 1 fun
    y _ ↦ by simpa [s22_y9] using hC ϑ _ (y · |>.2))) fun b a ↦ ?_).imp
    fun Ψ ↦ .imp_right fun e φ ↦ B (.trans (ext_inner_left ℂ fun Ξ ↦ ?_) congr(R $(e _)))⟩
  · simp; congr; apply s₂ _ b
    simp only [← Quotient.mk_smul_out, s22_y9, s22_z6, TensorChain.map_pure]
    clear * - a
    exact fun q ↦ (pure_congr fun i hi ↦ by cases hi <;> simp (disch := lia) only [z0, z7, *, smul_eq_mul, ← Prod.mk_mul_mk, map_mul, n2, Module.End.mul_apply, dite_eq_left, dite_eq_right] <;> apply_rules [ArrowPair.d2, map_one]).symm
  simpa [inner_smul_right] using! G _ ⟨_, Ξ.2.conj⟩ φ (innerₛₗ ℂ Ξ ∘ₗ R ∘ₗ lift (TensorChain.liftInPairs (D.liftKernel ϑ · |>.lift)) φ (_ + 1)) fun ξ y a b _ ↦ (A _ Ξ (by simpa [a] using! H ξ ϑ φ y b)).trans (by simp [s22_y9, chain₂])
