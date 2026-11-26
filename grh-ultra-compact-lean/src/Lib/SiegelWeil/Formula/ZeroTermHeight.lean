import Lib.Weil.DualPair.ThetaIntegralLaws
noncomputable section
open ContinuousLinearMap ENNReal Filling Fintype Matrix Real Space Subsingleton Splitting
attribute [-simp] map_zero
variable {E n m n₁ r : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] [Fintype n₁] [Fintype r] {s t s₁} {S : Space E n s} {S₁ : Space E n₁ s₁} (T : Space E m t) {p : Type} [Fintype p] (D₁ : S.Splitting S₁ r) {A : Matrix n r E} (S' : Space E n s) (T' : Space E m t)
abbrev CompleteSplitting (p : Type) [Fintype p] := T.Splitting (stdSpace E Empty) p
abbrev sw := pairWeil S' T' (1 * WeilData.upsilonU1 ^ (card n / 2)) 1
abbrev Lagrangian := {L : Submodule E _ // ∀ y, y ∈ L ↔ ∀ x ∈ L, star x ⬝ᵥ S'.J *ᵥ y = 0}
lemma sourceTerm_zero : D₁.sourceTerm T 0 = (D₁.homSource T).zeroTerm := by ext; simp [sourceTerm]
variable (P : CompleteSplitting S p) (L : Lagrangian S) (γ : U S.J)
section
attribute [local simp] Splitting.comp sw star_mulVec_dotProduct
attribute [simp] sourceTerm_zero ideleAbs_det_dyadicDiag_natCast sqrt_sq_eq_abs abs_of_nonneg
attribute [local simp ←] ext_iff Matrix.mul_assoc
omit [WeilData E] in
@[local simp↓] lemma forall_colSpan_dot_eq_zero_iff {y} : (∀ x ∈ colSpan A, star x ⬝ᵥ y = 0) ↔ Aᴴ *ᵥ y = 0 := ⟨fun h ↦ funext (h _ ⟨_, A.mulVec_single_one ·⟩), by aesop⟩
lemma exDecO : ∀ y, D₁.kᴴ *ᵥ S.J *ᵥ y = 0 → ∃ a w, D₁.k *ᵥ a + D₁.i *ᵥ w = y := by simp_all [(mulVec_surjective_iff_exists_right_inverse.2 ⟨_, (mul_eq_one_comm_of_card_eq _ _ _ (by simp +arith [D₁.card_eq])).1 (HasLeftInv.of_isUnit_gram (D₁.gram_eq_hypSum ▸ isUnit_J _)).choose_spec⟩).forall]
def mV x := θ _ ∘L P.sourceTerm T x
def CompleteSplitting.lagrangian : Lagrangian S := ⟨colSpan P.k, by simpa [iff_def, forall_and, eq_zero P.i] using exDecO P⟩
omit [WeilData E] in
lemma Lagrangian.eq_of_le {L L' : Lagrangian S} : L.1 ≤ L' → L = L' := by grind +extAll [IsConcreteLE.le_iff]
def Lagrangian.cS : {P : Σ r, CompleteSplitting S (Fin r) // P.2.lagrangian = L} := Nonempty.some (by
  have ⟨k, i, h⟩ := exists_basis_matrix L.1
  have o {y} := h ▸ L.2 y; simp at o
  obtain ⟨_ | _, _, V, P, rfl⟩ := S.exists_splitting i (ext_col (o.1 ⟨_, k.mulVec_single_one ·⟩))
  use ⟨_, by use P.k, P.l, 0 <;> simp [P.card_eq]⟩, eq_of_le h.le
  simpa [IsUnit.ne_zero] using congr(P.iᴴ * S.J * $((exists_mul_eq_of_col_mem_range (o.2 congr(col $P.gram_ki ·))).choose_spec.symm)))
def Lagrangian.zeroTerm := mV T L.cS.1.2 0
lemma ztLag f : P.lagrangian.zeroTerm T f = θ _ ((P.homSource T).zeroTerm f) := (exists_mul_eq_of_col_mem_range (P.lagrangian.cS.2.ge ⟨_, mulVec_single_one _ ·⟩)).elim fun _ h ↦ by simp [Lagrangian.zeroTerm, mV, P.zeroTerm_homSource_congr, ← h]
def isoS : S.Splitting S Empty := by use 0, 0, γ <;> simp [↓← mem_U]
lemma ztIso f : ((isoS γ).homSource T).zeroTerm f = sw S T (S.ratEmbed γ⁻¹, 1) f := by ext; erw [Splitting.zeroTerm_apply, pairWeil_of_mem_Gamma, homSource_iAdelic, iCoord, eq_zero (kAdelic _), ← (S.ratEmbed γ).mat_inv] <;> simp [Γ]
lemma exIsoO (l : HasLeftInv A) (h : Aᴴ * S.J * A = 0) : ∃ γ : U S.J, Aᴴ * S.J * (γ.1.1 * P.k) = 0 := (Function.Embedding.nonempty_of_card_le (by grind [Splitting, S.exists_splitting l h, card_empty])).elim fun ι ↦ (S.witt ⟨_, congr(submatrix $P.gram_lk ι ι).trans (by simp)⟩ l (h ▸ congr(submatrix $P.gram_kk _ _))).elim (⟨·, · ▸ (U.gram_invariant ..).trans congr(submatrix $P.gram_kk _ _)⟩)
lemma exLagEq : ∃ σ : _ ≃ {L : Lagrangian S // colSpan D₁.k ≤ L}, ∀ L f, Lagrangian.zeroTerm T (σ L) f = Lagrangian.zeroTerm T L ((D₁.homSource T).zeroTerm f) := by
  use ⟨(⟨CompleteSplitting.lagrangian <| D₁.comp ·.cS.1.2, ?_⟩), fun L ↦ ⟨.comap D₁.i.mulVecLin L, fun _ ↦ by
    erw [L.1.2, iff_comm]; constructor <;> intro h x hx
    obtain ⟨a, w, rfl⟩ :=
      exDecO _ x (forall_colSpan_dot_eq_zero_iff.1 ((L.1.2 x).1 hx · <| L.2 ·))
    erw [add_mem_cancel_left (L.2 ⟨_, rfl⟩)] at hx
    all_goals simp [← h _ hx]⟩, ((Lagrangian.eq_of_le ?_).symm.trans ·.cS.2), fun L ↦ Subtype.ext (Lagrangian.eq_of_le ?_)⟩, fun _ _ ↦ (ztLag ..).trans
    (by simp [Lagrangian.zeroTerm, mV, ↓zeroTerm_homSource_comp]) <;> rintro _ ⟨x, rfl⟩
  exacts [⟨x ⊕ᵥ 0, by simp⟩, ⟨0 ⊕ᵥ x, by simp⟩, by simpa using add_mem (L.2 ⟨_, rfl⟩) ((Lagrangian.cS _).2.le ⟨x ∘ .inr, rfl⟩ :)]
lemma mvSW h x f : mV T P x (sw S T (1, h) f) = mV T P (h⁻¹.mat * x) f := by simpa [P.card_eq, pairWeil, eq_one (G.onHom _)] using! congr($(P.sourceTerm_levi T 1 1 1 1 ..) 0)
def nT (x : p → ℕ) := (((2 ^ numInfPlaces E) ^ ∑ i, x i) ^ card m : ℂ)⁻¹ • sw S T (P.levi (dyadicDiag (x ·), 1), 1)
@[simp] lemma normalisedTorus_zero : nT T P 0 = 1 := by simp [nT, dyadicDiag, ← Pi.one_def]
lemma thNT (hm : 2 * card p < card m) : ∃ N, Measurable N ∧ ∫⁻ h, N h ∂T.quotMeasure ≠ ⊤ ∧ ∀ h x f, ‖θ _ (sw S T (1, h) (nT T P x f))‖ₑ ≤ N h * ‖f‖ₑ := by choose B k M hM using (P.homSource T).exists_tsum_mixedTerm_le; have hB := (k.prod (isCompact_closedBall_prod_integral (E := E)).matrix).image_auto (fun (a, (c : Matrix p p (𝔸 E))) ↦ vecToMat a * c) (by fun_prop [vecToMat]); refine ⟨_, .mul_const ?N (‖θ ((stdSpace E Empty).hom T)‖ₑ * M), MeasureTheory.lintegral_mul_const _ ?N ▸ mul_ne_top (T.lintegral_encard_ne_top hB (by lia)) coe_ne_top, fun h x f ↦ ?_⟩; use .comp .of_discrete (measurable_encard.comp (measurable_pi_iff.2 fun _ ↦ hB.isClosed.preimage_of_continuous (f := fun x ↦ _ * (G.mat x⁻¹ * _) * _).measurableSet.mem)); grw [← (P.hasSum_theta_sourceTerm ..).tsum_eq, enorm_tsum_le_tsum_enorm, mul_left_comm, mul_assoc, ← Set.encard_mono ?_, ← hM (.mk' (fun ξ ↦ matToVec ((T.toRatCoords h).1⁻¹.1 * ξ.map toAdele * (dyadicDiag (E := E) (x ·)).1)) (by open MatMul in simp [Matrix.map_add])), ← ENNReal.tsum_mul_left, ← (θ _).le_opENorm]; gcongr; erw [mvSW]; simpa [← sourceTerm_eq_mixedTerm, nT, P.card_eq, ← ofReal_norm, field, toRatCoords, G.mat] using! congr(‖$(P.sourceTerm_levi T 1 1 (dyadicDiag (x ·)) 1 1 ..) 0‖).le; use fun ξ k ↦ ⟨(_, _), ⟨k, dyadicDiag_inv_mem x⟩, by simp⟩
end
seal CStarMatrix
attribute [local simp ←] ext_iff Matrix.mul_assoc map_mul
lemma nztPM {T : Space E m t} {P : CompleteSplitting S p} {g} {a : GL p _} (hk : P.ActsOnFrame g a.1) g' f : ‖P.lagrangian.zeroTerm T (sw S T (g * g', 1) f)‖ = √(ideleAbs a.det) ^ card m * ‖P.lagrangian.zeroTerm T (sw S T (g', 1) f)‖ := by rw [← Prod.mk_one_mul_mk_one, ← rep_apply_apply]; simp [ztLag, sw, P.card_eq, -one_mul, homSource_zeroTerm_pairWeil (g₀ := 1) (hk := hk)]
lemma nztVP g : 0 < ‖P.lagrangian.zeroTerm T (sw S T (g, 1) (vacElem _))‖ := by simp [ztLag, pairWeil]; generalize P.homSource T = P, G.onHom (g, 1) (s' := t) = g; have ⟨g₀, h, _⟩ := P.exists_isAdapted_and_frame_eq 1; choose κ H b _ e _ using P.iwasawa; have ⟨_, _, h⟩ := IsAdapted.mixedTerm_omega_vacElem (.of_eq_submatrix_mul (A := G.mat _) (.imp (by simpa [maxCompactU, U] using! · ·) mem_Kf.1 (div_mem (H g) (H g₀))) id h (by simp [Splitting.frameAt, division_def]) : P.IsAdapted (g₀ * κ g₀ * (κ g)⁻¹) 1); rw [← mul_inv_cancel_right g (κ g), ← rep_apply_apply] at *; simpa [prod_empty, *, mixedTerm, chiAdelic, vacElem_apply_eq_prod_lineTheta, funext_iff, vacuumFn, P.zeroTerm_omega 1 _ (e _) (b _).det rfl] using congr($(h 0) 0 = 0)
lemma exZtNT (P' : CompleteSplitting S r) {K} (Z : Matrix r n (𝔸 E)) (h : Z * P'.kAdelic = 1) (hK : IsCompact K) : ∃ R : NNReal, ∀ g ∈ K, ∀ x u : p → ℕ, Z * g.mat * P.kAdelic * (dyadicDiag (x ·)).1 = Z * g.mat * P.kAdelic * (dyadicDiag (u ·)).1 → ∀ f, ‖P'.lagrangian.zeroTerm T (sw S T (g, 1) (nT T P x f))‖ ≤ R * ‖f‖ * ((2 ^ numInfPlaces E) ^ (∑ i, u i - ∑ i, x i : ℤ)) ^ card m := by
  have c := (isCompact_closedBall_prod_integral (E := E)).matrix (m := p) (n := p); constructor; introv hg _; choose κ hκ a _ e _ using P'.iwasawa _; simp [nT, rep_apply_apply, ↓zpow_natCast_sub_natCast₀, div_pow, field]; grw [← mul_inv_cancel_right (g * _), nztPM e, ← mul_inv_cancel_left _ a.det, map_mul, sqrt_mul', ideleAbs_det_dyadicDiag_natCast u, sqrt_sq, (le_max_iff.2 ((le_total ..).imp_left (le_csSup ((isCompact_setOf_le_ideleAbs_det ((hK.prod (isCompact_maxCompact.prod (c.prod c))).image_auto fun (g, κ, u, x) ↦ !![(fromBlocks (Z * g.mat * (P.lAdelic * xᴴ * P.lCoord :) * κ.mat * P'.kAdelic) (Z * g.mat * P.kAdelic) (-P.kCoord * κ.mat * P'.kAdelic) u).det]) one_pos).image_auto (ideleAbs ·.det)).bddAbove ⟨.scalar _ _, ⟨⟨(_, _, _, _), ⟨hg, hκ, dyadicDiag_inv_mem u, dyadicDiag_inv_mem x⟩, ?_⟩, ·⟩, rfl⟩))).trans_eq' (congrArg _ (Units.ext (det_diagonal.trans (prod_unique _)))), le_opNorm, le_opNorm, ((pairThetaKer ..).exists_norm_le_of_isCompact (isCompact_maxCompact.prod isCompact_maxCompact)).choose_spec, ← le_coe_toNNReal, mul_pow, mul_rotate, ← mul_assoc, ← mul_assoc] <;> simp [*, (det_classical _).symm.trans (det_fromBlocks₂₂ ..), add_comm]
  simpa [*, Splitting.levi, add_comm, Matrix.mul_add, Matrix.add_mul, eq_zero iAdelic] using
    congr(_ * Matrix.det (Z * $e))
