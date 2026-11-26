import Lib.PadicHodge.Comparison.CrystallineLimit
noncomputable section
section
open Module Nat crysCocycles PadicInt LinearMap LE DiscreteModule Function Classical AddSubgroup Fint Topology
variable {p} [ThePrime p] {Γ R T μ : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T] [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup μ] [𝒥 : OverGp Γ p] {ρ : Representation R Γ T} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (hj : IsOpenEmbedding 𝒥.toGp)
variable (T) in
abbrev pPowMultiples m := (lsmul ℤ_[p] T (p ^ m)).range.toAddSubgroup
@[simp] lemma index_pPowMultiples m : (pPowMultiples T m).index = (p ^ m) ^ finrank ℤ_[p] T := by erw [index_eq_card, pPowMultiples, range_eq_map, card_congr (QuotSMulTop.equivQuotTensor ..).toEquiv, card_congr ((finBasis ..).baseChange _).equivFun.toEquiv, ← ker_toZModPow, card_pi, card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _)).1]; simp
def zmodPowToUnits m : QuotSpan (p ^ m : ℤ_[p]) →+ DiscreteUnits (PadicAlgCl p) := (rootPowHom ..).1.comp (Ideal.Quotient.lift _ (toZModPow m) (by simp [← ker_toZModPow])).toAddMonoidHom
lemma map_cyclotomicGp_smul [Module ℤ_[p] μ] (f : μ →+ DiscreteUnits (PadicAlgCl p)) {n} (h : ∀ x, p ^ n • f x = 0) x g : f ((cyclotomicGp g).1 • x) = unitsRep g (f x) := (map_cycChar_smul f n h x).trans (cycCharMod_eq_iff_unitsRep.1 zmod_eq_natCast_val (h x)).symm
variable (h : IsPotCrys ρ) {S} [CommRing S] {V : DiscreteModule S Γ} {q : T →+ V} {m}
lemma nsmul_zmodPowToUnits x : p ^ m • zmodPowToUnits m x = 0 := by simp [← map_nsmul, ↓nsmul_quot_eq_zero]
include hj h
lemma crysCocycles.continuous_comp [TopologicalSpace μ] (q : T →+ μ) (k : ∀ y, p ^ m • q y = 0)
    {x} (hx : x ∈ crysCocycles ρ) : Continuous (q ∘ x) := (isLocallyConstant_of_eventually_mul (nearOne_eq_nhds_one hj ▸ (eventually_eq_pow_smul h hx m).mono (by grind [apply_mul hx]))).continuous
variable (e : ∀ g x, q (ρ g x) = V.ρ g (q x)) (k : q.ker = pPowMultiples T m)
abbrev IsPotCrys.reducedCocycle : crysCocycles ρ →+ Z1 V.ρ := .codRestrict ((q.compLeft Γ).domRestrict _) _ fun ⟨_, u⟩ ↦ ⟨continuous_comp hj h q (by simpa [le, ← map_nsmul, ← cast_smul_eq_nsmul ℤ_[p]] using k.ge) u, by simp_all [apply_mul u]⟩
lemma IsPotCrys.ker_reducedCocycle : (h.reducedCocycle hj e k).ker = pPowMultiples _ m := by ext ⟨c, u⟩; simpa [funext_iff, ← q.mem_ker, k, skolem] using ⟨.imp fun _ E ↦ ⟨of_smul NeZero.out (funext E ▸ u), E⟩, by tauto⟩
lemma IsPotCrys.holdsCorestrictions [CompactSpace Γ] (o : Surjective q) {U : OpenSubgroup Γ} (hU : IsOpenEmbedding (toGp.comp U.subtype)) : V.HoldsCorestrictions U (reducedCocycle (𝒥 := ⟨_, ⟨hU.2⟩⟩) hU (h.comp _) (e ·) k).range (h.reducedCocycle hj e k).range := have ⟨s, n, _, m⟩ := exists_coset_section U
  ⟨o.forall.2 (⟨⟨_, coboundary_mem ·⟩, by aesop⟩), fun ⟨y, _, c⟩ ⟨⟨_, Y, hz⟩, E⟩ ↦ ⟨⟨fun g x ↦ V.ρ (s x) (y ⟨_, m x g⟩), by fun_prop, fun g
    k ↦ by simpa [mul_assoc, mul_smul, subgroupIncl, -ContinuousMonoidHom.coe_toMonoidHom] using! (congr(fun x ↦ V.ρ (s x) $(c ⟨_, m x g⟩ ⟨_, m (g⁻¹ • x) k⟩)))⟩, by
    ext u; show V.ρ _ (y ⟨_, m _ u⟩) = _; simp [n], ⟨_, ∑ x, tensorAction _ (toGp (s x)) (ρ _) Y, fun g ↦ by rw [map_sum, ← (MulAction.bijective g⁻¹).sum_comp, TensorProduct.tmul_sum]; simpa [↓tensorAction_tensorAction, ↓map_sub, tensorAction, ← map_mul, ← mul_assoc] using (congr(∑ x, tensorAction _ (toGp (s x)) (ρ (s x)) $(hz ⟨_, m x g⟩)))⟩, by cases E; ext; simp [sum, e]⟩⟩
end
open Module Matrix IsScalarTower RingHom Function Algebra Submodule.Quotient BdRPlus algebraMap
private lemma k2 {p} [ThePrime p] Γ [Group Γ] [𝒥 : OverGp Γ p] n w : ∃ t, ∀ {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι] (ε : Basis ι ℤ_[p] T) {ρ} x, IsCrystallineUpTo (R := ℤ_[p]) n ρ → ∃ z : ι → ℂ_[p], (∀ s, ‖z s‖ ≤ 1) ∧ ∀ γ (r : PadicRep Γ p) (u : T →ₗ[ℤ_[p]] _), (∀ g y, u (ρ g y) = (r.rep g).1 * u y) → u x = 1 → IsPotCrys (matrixRep r.rep) → t * ∑ s, z s * γ (u (ε s)).trace = jump (matrixRep r.rep) γ w := by
  obtain ⟨e, K, H⟩ := Lift.uniform_period_bound Γ n; replace K := algebraMap_apply _ Bcris BdR e ▸ (K.map _).ne_zero; obtain ⟨⟨m, δ, he⟩, R, hR⟩ := q5 (ne_zero_of_map (algebraMap_apply _ BdRPlus BdR e ▸ K)), ((localFieldOf Γ).essFiniteType_iff.1 inferInstance).choose_spec ▸ CoeffRing.exists_mem_of_mem_adjoin _; let O := (toAlgHom ..).liftEquiv ℤ_[p] Amax R BdRPlus; let ⟨c, B⟩ := (@End.isNilpotent_iff_of_finite Amax (_ ⧸ (((toAlgHom _ BPlus _).toLinearMap ∘ₗ Algebra.linearMap ..).coprod (.mulLeft _ (xi ^ m.succ • 1))).range.comap O.toLinearMap) _ _ _ _ p).2 (Quot.ind (O · |>.q0 m.succ |>.imp fun l ⟨a, w, h⟩ ↦ mod_cast (mk_eq_zero _).2 ⟨(a, w), by simp [← h, smul_def, ← algebraMap_apply]⟩))
  have B {z y} (h : O y = e • z) : ‖thetaBdR (p ^ (2 * m) * (δ * (p ^ c * z)))‖ ≤ 1 := by
    obtain ⟨a, w, k⟩ := by simpa [h, smul_def, ← he, pow_succ, mul_assoc, mul_left_comm (_ ^ c), ← mul_sub, ← eq_sub_iff_add_eq] using (mk_eq_zero _).1 congr($((p.cast_pow c).trans B) ⟦y⟧)
    cases w2.1 ⟨_, k⟩; cases x1.y8 ⟨_, xi_mul_tau.symm⟩ ⟨a, by simpa [smul_def]⟩; convert (x2 ‹_›).2; clear K B H hR; simp_all [← w1, ← w7, ← algebraMap_apply, prime_xi.1]
  use (p ^ (2 * m) * thetaBdR δ * p ^ c)⁻¹; introv hx; choose _ U U' Q hr using H ε hx
  obtain ⟨⟨Y, Z⟩, W, k, ⟨W, rfl⟩, A, E, H, I⟩ := exists_hodge_frame Γ le_top (isUnit_of_mul_isUnit_left
    (by rw [← map_mul, Q]; simp [smul_eq_diagonal_mul, K, Pi.isUnit_iff])) (.trans (by
    simp [comp_def]; rfl) <| congrArg (algebraMap ..).mapMatrix <| hr ·)
  let ⟨y, J⟩ : ∃ y, O.mapMatrix y = (algebraMap ..).mapMatrix Y := ⟨of (1 ⊗ₜ ⟨Y · ·,
    by clear * - hR A I; simp_all [← ext_iff]⟩), ext (by simp [O])⟩
  let D {κ R} (k : κ → ℤ) [Ring R] := diagonal (if w = k · then (1 : R) else 0); let z := W.1 *ᵥ D k *ᵥ W⁻¹ *ᵥ (↑) ∘ ε.repr x; refine ⟨_, fun s ↦ @B (z s) (mulVec (U.map (↑) * y * D k * y.adjugate * U'.map (↑)) ((↑) ∘ ε.repr x) s) ?_, fun γ r u v o h ↦ ?_⟩
  erw [O.map_mulVec, ← O.mapMatrix_apply]; simp [↓map_mul, O.map_adjugate, comp_def, ← map_det, *, z, (map_injective (IsFractionRing.injective _ BdR)
    (by simp; erw [E, ← mul_assoc]; simp [hodgeMatrix, D, mul_assoc]) : SemiconjBy (U.map (↑) * (algebraMap ..).mapMatrix Y) ((D k).map O) (W.1 * D k * W.2)), mul_assoc, mul_adjugate, -mapMatrix_apply, ← U.map_mul, map_smul', -TensorProduct.algebraMap_apply]
  obtain ⟨_, ⟨P, k₁, -, hJ, b, hb, eb⟩, -, β, hβ, eβ⟩ := Finite.of_basis ε, h.exists_isHodgeTateFrame (Pi.basisFun ..) γ, hasJumps_of_rows (γ := ofId ..) ε (W.map thetaBdR.1.mapMatrix.1)⁻¹ _ (by exact .of_forall (H.mono fun _ ↦ inv_mul_apply_of_isHodgeTateFrame ∘ isHodgeTateFrame_of_hodgeMatrix))
  let F y := P.2 * (u y).map γ; suffices ∑ s, thetaBdR _ • F _ = D k₁ * F x by
    simpa [F, Finset.mul_sum, mul_assoc, P.1.trace_mul_comm, D, o, hJ w, Multiset.count_map, ← isUnit_iff, NeZero.ne, AddMonoidHom.map_trace] using! congr((P * $this).trace)
  ext i c; simp [D, Matrix.sum_apply, -ite_mul, -mulVec_single, show ∀ y, F y i c = b i (u y *ᵥ Pi.single c 1) by simp [pi_eq_sum_univ' (col _ c), F, ← eb, ↓mul_apply, mul_comm]]; refine (LinearMap.eqOn_span (f := dotProductBilin ℤ _ _ ∘ₗ .pi (.flip .id ∘ ε)) (g := .mulLeft .. ∘ₗ .flip .id x) (Set.forall_mem_image.2 fun l e ↦ ?_) (hodgeTateMaps.mem_span_same_weight hβ (hodgeTateMaps.pull (φ := algebraMap ..) ⟨applyVec u _, by simp⟩ (by simp [v]) ⟨_, hb i⟩).2 (β.mem_span _)) :); rw [← ε.sum_repr x, map_sum]; simpa [-toRingHom_ofId, eβ, e.out, D, entrywise, smul_def, diagonal, apply_ite, ite_apply, mul_comm] using congr(thetaBdR ($((inv_smul_smul W _ : _ *ᵥ z = _)) l))
end
attribute [-simp] map_eq_zero isUnit_map_iff
open Matrix Polynomial MonoidAlgebra Finset Module Metric IsUltrametricDist Submodule Set hodgeTateMaps TensorProduct Function LinearMap Amax Classical Filter
lemma local_clauses_of_trace_limit {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E m I : Type} [Field E]
  [EmbeddedNumberField E] [Fintype m] {r : GalRep ℓ E m} {A} (hr : Continuous r) (hn : IsTraceNondeg r) R {R' J} {ι : I → Type} [∀ η, Fintype (ι η)] F [NeBot F] (a J' : ∀ _ _, _) (ρ : ∀ η, ι η → PadicRep _ ℓ) (hc : ∀ η i, Continuous (ρ η i).rep) (hU : ∀ η i, IsGoodAt (ρ η i).rep A) (hJ : ∀ η i, JumpsRelAt (ρ η i).rep A R' (J' η i)) (hS : Finite I ∨ ∀ η i, HasJumpsAt (ρ η i).rep A J)
  (T : TendstoUniformly (fun η g ↦ ∑ i, a η i * ((ρ η i).rep g).1.trace) (r · |>.1.trace) F) (h' : ∀ τ u (x : ∀ _ _, ℕ) (n : ℕ), (∀ η i, R' ((J' η i τ).count u) (x η i)) → F.Tendsto (fun η ↦ ∑ i, a η i * x η i) (nhds n) → R ((J τ).count u) n) : IsGoodAt r A ∧ JumpsRelAt r A R J ∧ ∀ ⦃s N P⦄ ⦃Q : ∀ _ _, _⦄, natDegree P < N → (∀ η i, natDegree (Q η i) < N ∧ PolyKillsAt (ρ η i).rep A s (Q η i)) → (∀ l, TendstoUniformly (fun η g ↦ ∑ i, a η i * (Q η i).coeff l * ((ρ η i).rep g).1.trace) (fun g ↦ P.coeff l * (r g).1.trace) F) → PolyKillsAt r A s P := by
  let W b c := TendstoUniformly (fun η g ↦ ∑ x, (a * c) η x * ((ρ η x).rep g).1.trace)
    ((b * ·.1.trace) ∘ r) F
  obtain ⟨⟨t₀⟩, T : W 1 1⟩ := F.nonempty_of_neBot, by simpa [W]
  have B {b c} (H : W b c) η hη := (tendstoUniformly_iff.1 H η hη).mono fun n h y ↦ show
    b * (groupRingHom ⟨r⟩ y).trace - ∑ x, (a * c) n x * (groupRingHom _ y).trace ∈ ball 0 η by
    simpa [lift_apply, Finsupp.sum, mul_sum, univ.sum_comm, smul_sub, smul_sum, -mem_ball] using! sum_mem (S := ball_openAddSubgroup _ hη) fun g _ ↦ balanced_ball_zero.smul_mem
      (y.coeff g).2 (mem_ball_zero_iff.2 (mem_ball_iff_norm.1 (h g)))
  have Z S {b c : ℕ → _} (H : ∀ {l}, W (b l) (c l)) (y : ∀ _ _, _) (h : ∀ θ x, ∑ l ∈ S, c l θ x • groupRingHom (ρ θ x) _ = 0) {M} (e : ∀ θ, M = ∑ l ∈ S, b l • groupRingHom ⟨r⟩ (y θ l)) :
    M = 0 := hn _ (by simp (maxDischargeDepth := 9) [e t₀, lift_apply, Finsupp.sum, sum_mem, smul_of_tower_mem, mem_span_of_mem]) fun g ↦ (tendsto_const_nhds_iff.1 ((tendsto_finsetSum S fun l _ ↦ tendsto_nhds.2 (B (@H l) · · |>.mono fun θ h ↦ h (y θ l * .single g 1))).congr fun θ ↦ by simpa [e θ, sum_mul, mul_sum, mul_assoc, S.sum_comm] using
    congr(∑ x, _ * ($(h θ x) * ((ρ θ x).rep g).1).trace))).trans sum_const_zero
  obtain ⟨p, g, hg⟩ := @PadicInt.maximalIdeal_eq_span_p ℓ, skolem.1 exists_gp_eq_algHom
  let Δ := decompGroup Gal(Ω/E) A
  let X η := Option.elim' ⟨r⟩ (ρ η)
  refine ⟨⟨fun l s b ↦ by simpa using (Z {0} T (fun _ _ ↦ .single s 1 - 1) (by simp
    [(hU ..).1, *]) fun _ ↦ rfl), @fun l ↦ ?_⟩, fun l γ _ b w ↦ h' _ w _ _ (hJ · · b w) ?_, fun s n
    P Q hP h O ↦ ⟨fun l ↦ Z (range n) @O (fun _ ↦ (.single s 1 ^ ·)) (by simp [(h ..).2.1, *, ← aeval_eq_sum_range']) (by simp [aeval_eq_sum_range' hP]), @fun l m k w ↦ ?_⟩⟩ <;> (
    choose L q u _ _ hs hu _ U using fun η ↦ exists_finite_groupRing_quotient Δ (τ := X η) (·.rec hr (hc η))
    have b η : ∀ᶠ k in cofinite, ∀ o γ, jump (decompRep (X η o).rep A) γ k = 0 := exists_jump_bound
      (ρ := actionRep _ (L η) (.domRestrict ((lift _ _ _).symm (q η)) _)).rec fun _ h ↦ (finite_Icc ..).subset (h · ∘ mt fun e o γ ↦ jump_eq_zero_iff.2 fun f a ↦ f.ext fun v ↦ (congrArg f (by
      simp [asSemilinear])).trans congr($(jump_eq_zero_iff.1 e _
      (pull (asSemilinear (applyVec (u _ o)) (v, γ)) (by simp [hu, asSemilinear]) ⟨_, a⟩).2) 1))
    have ⟨d, hd⟩ := ((hS.elim (fun _ ↦ .all b) fun H ↦ ((b t₀).and (∑ τ, J τ).finite_toSet.compl_mem_cofinite).mono fun k h η ↦ (·.rec (h.1 none) fun x γ ↦ by
      simp at h; erw [← H η x (hg γ)]; simp [*])).image Int.natAbs).bddAbove
    let α := singleHom.comp (((Units.coeHom _).comp (χ⁻¹ ^ d)).prod Δ.subtype)
    have ew {σ} g x : viaGroupRing α σ g x = (χ g ^ (-d : ℤ)).1 • decompRep σ.rep A g x := by simp [α]
    have K η o c : IsCrystalline .. ∧ IsCrystallineUpTo (2 * d) (viaGroupRing α (X η o)) := ⟨c, c.tate_twist _ ew, fun γ u h ↦ by have := hd ⟨u - d, by simp [← jump_twist_cyclotomicGp _ ew]; tauto, rfl⟩; omega⟩
    choose C H using fun θ o ↦ K θ o (o.rec (.tate_twist (isCrystalline_of_trace_limit α hr hn (X := ρ) (K · · (hU ..).2 |>.2) hc (B T · · |>.exists.imp fun _ b y z ↦ le_of_lt (by simpa [z] using! b y))) d (by simp [α, smul_smul, ← mul_pow])) (hU θ · |>.2)))
  use C t₀ none
  have N {x} : ‖γ x‖ = ‖x‖ := by simp [*, ← smul_coe_Cp]
  choose t z hz S using (k2 _ _ (w - -d)).imp fun t S θ ↦ S (finBasis ..) 1 (U θ (H θ))
  choose y hy using (hs · <| finBasis ℤ_[ℓ] _ ·)
  refine tendsto_nhds.2 fun ε e ↦ (exists_pos_mul_lt e ‖t‖).elim fun δ ⟨e, k⟩ ↦ (B T δ e).mono fun θ
    h ↦ k.trans_le' (.trans_eq' (norm_mul_le_of_le le_rfl (norm_tsum_le_of_forall_le_of_nonneg e.le fun s ↦ (norm_mul_le_of_le (hz θ s) N.le).trans (by simpa using (h (y θ s)).le))) ?_)
  have S o := S θ γ ⟨.toHomUnits _⟩ (u θ o) (by simp [hu]) (by simp) (H θ o).1.isPotCrys
  simpa [← hy, hu, mul_sub, mul_sum, sum_comm (γ := ι _), mul_left_comm (γ _), dist_eq_norm', ← N, ↓jump_twist_cyclotomicGp _ ew] using! congr(‖$(S none) - ∑ x, γ (a θ x) * $(S x)‖)
  obtain ⟨⟨δ, D, S⟩, ⟨c⟩⟩ := Lift.uniform_period_bound Δ _, p ▸ nonempty_adicBasis _ p
  choose Y V using fun θ N ↦ span_le (p := (periodTensorMap _ _ id).range.comap (.restrictScalars _ _ ∘ₗ periodTensorMap _ _ id)).2 (fun y a ↦ ⟨_, .symm ((linearFrob_apply (U θ (H θ)).1.isPotCrys (w.pow N) (fixedPeriods.map (by simp)
    ((nearOne _).univ_mem' a))).trans (tensorAction_periodTensorMap (fun _ ↦ id_apply _) ..))⟩)
    (nsmul_mem ((S (finBasis ..) (U θ (H θ))).1 1) ((ℓ ^ (k * d)) ^ (n - N)))
  choose G hG using (Y · · |>.exists_finset)
  choose M V E using fun θ o {Q} (h : natDegree Q < n) v ↦ show ∃ M, periodTensorMap _ _ id M = (δ • (ℓ ^ _ : Bcris) ^ n) • Q.eval₂ (coefEnd (PadicAlgCl ℓ) _) (linearFrob (decompRep (X θ o).rep A) ..) _ ∧ ∀ f, lift (lsmul .. ∘ₗ f) M = (∑ N ∈ range n, Q.coeff N • groupRingHom _ (surjInv (hs θ) (lift (lsmul .. ∘ₗ f) (Y θ N)))) *ᵥ v from ⟨∑ N ∈ range n, lTensor _ (Q.coeff N • applyVec (u θ o) v) (Y θ N), by simpa +contextual [eval₂_eq_sum_range' _ h, smul_sum, periodTensorMap, hG, smul_comm _ δ, tmul_eq_smul_one_tmul δ, ← Nat.cast_smul_eq_nsmul Bcris, smul_smul, ← pow_add, mem_range_le, _root_.smul_pow, ↓linearFrob_pow (H ..).1.isPotCrys w, ↓linearFrob_twist_cyclotomicGp (C ..).isPotCrys w d ew, ↓map_nsmul] using congr(∑ N ∈ range n, (coefEnd ..) _ ($((congrArg _ (V θ N)).trans (baseChange_linearFrob (U θ (H θ)).1.isPotCrys (w.pow N) (H θ o).1.isPotCrys (applyVec (u θ o) v) (by simp [hu]) _)))),
    by simp [← hu, hG, surjInv_eq, sum_mulVec, smul_sum, smul_comm (Q.coeff _)]⟩
  have Z f := Z _ @O _ (fun θ x ↦ ext_iff_mulVec.2 fun v ↦ by
    erw [← E θ x (h ..).1, periodTensorMap_injective (a₂ := 0) ((V ..).trans (((h ..).2.2 w).2 ▸ smul_zero _))]
    simp; rfl) fun θ ↦ ext_iff_mulVec.2 fun v ↦ (E t₀ none hP v f).symm.trans
    (periodTensorMap_injective (V t₀ none hP v ▸ V θ none hP v) ▸ E ..)
  use (C t₀ none).isPotCrys, (isBaseChange ..).algHom_ext _ _ fun v ↦ ?_
  simpa [D.ne_zero, Algebra.smul_def δ, (NeZero.of_faithfulSMul ℚ_[ℓ] _ ℓ).1, tensor_eq_zero_of_separating c.eq_zero_of_coord _ fun f ↦ (E ..).trans (Z _ ▸ zero_mulVec v)] using! (V t₀ none hP v).symm
