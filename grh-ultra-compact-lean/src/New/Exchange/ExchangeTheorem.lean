import Lib.Weil.DualPair.ThetaIntegralLaws
import Lib.Weil.MixedModel.EquivariantCoefficients
import Lib.SiegelWeil.Tower.LargeSideConstantTerm
import Lib.Weil.MixedModel.RapidSections
import Lib.Weil.DualPair.Flip
import New.Exchange.SquareLawFourier
import Lib.ClassField.HeckeCharacter.LevelModulus
section
noncomputable section
open Matrix schwartzBruhat SemilocalField Classical Finsupp MatMul MulChar Function
variable {F : Type} [SemilocalField F] {a b n : Type} [Fintype a] [Fintype b] [Fintype n] (χ : MulChar F ℂ) (e : b ⊕ a ≃ n) (y : Matrix n b F)
lemma exists_common_coset_reps : ∃ (ℓ : (_ → ℂ) →ₗ[ℂ] ℂ) (r : GL b F ⧸ intGL b O → GL b F), (∀ t f, (∀ q, f (r q) ≠ 0 → q ∈ t) → ℓ f = ∑ q ∈ t, f (r q)) ∧ ∀ y : Matrix n b F, HasLeftInv y → (∃! q, IsPrimitiveMatrix O (y * (r q).1)) ∧ ∃! q, IsPrimitiveMatrix O (y * (r q).1⁻¹) := match skolem.1 (exists_invTransposeGL_inv_eq valPair ·.out), lcoeFun.dualMap_surjective_of_injective DFunLike.coe_injective (lsum ℂ 1) with | ⟨k, _⟩, ⟨ℓ, L⟩ => ⟨ℓ ∘ₗ .funLeft .., (·.out) * k, fun t f h ↦ congr($L (onFinset t _ h)).trans (by simp), fun y h ↦ (valPair.exists_isPrimitiveMatrix_mul h).elim fun u p ↦ by have := (p.2.mul_iff.trans <| isPrimitiveMatrix_iff_mem_intGL <| u⁻¹ * ·); simp_all [← coe_units_inv, -Pi.mul_apply]; simp_all [↓← invTransposeGL_mem_intGL (_ * _⁻¹), ← QuotientGroup.eq, mul_assoc]⟩
def localSection := (@exists_common_coset_reps F _ b n).choose ∘ₗ .mulLeft ℂ (χ ·.1.det) ∘ₗ .funLeft ℂ ℂ (y * ·.1)
def matchingPairs := .prod (schwartzBruhat (HasLeftInv ·ᵀ)) (schwartzBruhat HasLeftInv) ⊓ (LinearMap.pi fun k ↦ (localSection χ (invLastRows e k)ᵀ ∘ₗ .funLeft ℂ ℂ transpose).coprod (-(χ k.1.det • localSection χ (firstCols e k)))).ker
lemma localSection_of_primitive (hy : HasLeftInv y) : ∃ g : GL b F, IsPrimitiveMatrix O (y * g.1) ∧ ∀ Ψ, (∀ x, Ψ x ≠ 0 → IsPrimitiveMatrix O x) → localSection χ y Ψ = χ g.1.det * Ψ (y * g.1) := exists_common_coset_reps.choose_spec.elim fun _ ⟨S, R⟩ ↦ (R y hy).1.imp' _ fun p ↦ .imp_right (by intros; erw [S {p}] <;> aesop)
lemma TameLocalChar.isClopen_primitive (_ : TameLocalChar χ) (e : b ⊕ a ≃ n) : IsClopen {y : Matrix n a F | IsPrimitiveMatrix O y} := ⟨by simpa [Set.image, eq_comm, valPair.exists_firstCols_iff] using ((isCompact_intGL isCompact_O).image_auto (firstCols (.trans (.sumComm ..) e))).isClosed, isOpen_iff_forall_mem_open.2 fun _ ⟨_, _, h, _⟩ ↦ ⟨_ ⁻¹' {0}ᶜ, isPrimitiveMatrix_of_stdColDatum_ne_zero h, (stdColDatum_mem_schwartzBruhat χ h).1 _, by simp [stdColDatum, invOnUnits, *]⟩⟩
lemma matchingPairs.translate_mem {p} (h : p ∈ matchingPairs χ e) (g : GL n F) : (χ g.1.det • (p.1 <| · * g.1), (p.2 <| g⁻¹.1 * ·)) ∈ matchingPairs χ e := ⟨⟨(schwartzBruhat _).smul_mem _ (schwartzBruhat.comp h.1.1 (· * g.2) fun _ ↦ .imp' (· * g.1ᵀ) (by simp [← transpose_mul])), schwartzBruhat.comp h.1.2 (g.1 * ·) fun _ ↦ .imp' (· * g.2) (by simp)⟩, by simpa [↓funext_iff, mul_add, localSection, Pi.mul_def, ← show ∀ g k : GL n F, g.1 * firstCols e k = firstCols e (g * k) from fun _ _ ↦ rfl, ← mul_assoc, ← map_mul, ← det_mul] using! congr(χ g.det • $(h.2) ∘ (g⁻¹ * ·))⟩
lemma matchingPairs.exists_linear_factor {X} (hχ : TameLocalChar χ) (Λ : _ →ₗ[ℂ] X → ℂ) (hΛ : ∀ g : GL a F, ∀ Φ ∈ schwartzBruhat (HasLeftInv ·ᵀ), χ g.1.det • Λ (Φ <| g.1 * ·) = Λ Φ) : ∃ T : _ →ₗ[ℂ] _, ∀ p ∈ matchingPairs χ e, T p.2 = Λ p.1 := by
  choose! k _ K using (exists_invLastRows_iff_transpose e (x := ·).2 ∘ ((@valPair F _).exists_firstCols_iff _).2)
  use Λ ∘ₗ .pi fun x ↦ ite (IsPrimitiveMatrix O xᵀ) (χ (k x).det) 0 • localSection χ (firstCols e (k x))
  rintro _ ⟨⟨m⟩, h⟩; choose r S R using (@exists_common_coset_reps F _ a n).choose_spec
  have o q : _ ∈ schwartzBruhat _ := ⟨(LocallyConstant.indicator ⟨_, m.1⟩ ((hχ.isClopen_primitive _ e).preimage (f := (·ᵀ * (r q).2)) (by fun_prop))).2, m.2.imp (·.mono (by simp)) (.trans (by simp))⟩
  choose! _ p _ U using (R _ ∘ @m.2.2 ·)
  let ⟨t, ht⟩ := ((m.1 {0}).isClosed_compl.closure_eq.subst m.2.1).elim_finite_subcover _ (o · |>.1 {0}ᶜ) fun _ ↦ by simp; tauto
  convert congr(∑ q ∈ t, $(hΛ (transposeGL (r q)) _ (o q))) <;> simp only [← map_smul, ← map_sum, Λ.comp_apply] <;> congr with x <;> simp [-ite_smul, Set.indicator, Set.subset_def] at ht U ⊢
  split; apply (sub_eq_zero.1 congr($h _) ▸ S t ..).trans <;> simp [← K _ ‹_›]
  repeat grind [t.sum_eq_single (p x), fun q _ ↦ (U ((r q).1ᵀ * x) · q (by simpa))]
end
end
section
open SemilocalField
attribute [-simp] submatrix_id_mul
lemma IsPartner.mem_matchingPairs {a b n} [Fintype a] [Fintype b] [Fintype n] {F} [SemilocalField F] {χ e Φ Ψ} (hχ : TameLocalChar χ) (h : @IsPartner F a b n _ _ O e χ Φ Ψ) (hΨ : IsLocallyConstant Ψ) : (Φ, Ψ) ∈ matchingPairs χ e := by
  refine' ⟨⟨.transpose_mem_schwartzBruhat (schwartzBruhat.of_support_primitive (fun s ↦ (Set.ext _).subst (((IsLocallyConstant.zero s).union (hχ.isClopen_primitive _ e).2).sdiff (((isCompact_intGL isCompact_O).diff ((hΨ.comp_continuous (f := firstCols e) (by fun_prop)).div (hχ.isLocallyConstant_invOnUnits.comp_continuous Units.continuous_val.matrix_det) s)).image_auto (Matrix.transpose ∘ invLastRows e)).isClosed)) ?l), schwartzBruhat.of_support_primitive hΨ ?r⟩, funext fun k ↦ match localSection_of_primitive _ _ (hasLeftInv_invLastRows_transpose ..), localSection_of_primitive _ _ ⟨_, invFirstRows_mul_firstCols ..⟩ with | ⟨g, a, A⟩, ⟨u, b, B⟩ => (congr($(A _ ?l) - _ * $(B _ ?r)).trans ((exists_firstCols_eq_mul e k ⊤ u _ (transposeGL g) ..).elim fun j p ↦ (_ : ∃ i ∈ intGL n O, invLastRows e j = invLastRows e i).elim (b.mul_iff (x := invFirstRows e j * firstCols e ·) |>.elim _)))⟩
  repeat simp_all [← mul_assoc, ← map_mul, mem_intGL (O := ⊤)] <;> grind [invOnUnits, isPrimitiveMatrix_iff_isIntegralUnit_det, Matrix.transpose_submatrix, Matrix.transpose_mul, Matrix.transpose_transpose, right_mul, det_fromRows_invLastRows, χ.map_one, (exists_invLastRows_iff_transpose e).trans (valPair.exists_firstCols_iff _)]
end
section
open Matrix MeasureTheory SemilocalField schwartzBruhat IsIntMatrix Finset Function MatMul Fint
variable {F a b m n} [V : SemilocalField F] [Fintype a] [Fintype b] [Fintype m] [Fintype n] {χ P Φ Ψ} [hχ : TameLocalChar χ] {e : b ⊕ a ≃ n} {U : Set (Matrix n b F)} (hP : ∀ g : GL n F, ∀ f ∈ P, (f <| g.1 * ·) ∈ P) (hS : P ≤ schwartzBruhat U) (hΨ : IsLocallyConstant Ψ) (Q : IsPartner V.O e χ Φ Ψ) (A : IntegralFrame F n m b)
lemma IntegralFrame.exists_stdRowDatum_eq_stdDatum σ : ∃ c, ‖c‖ = 1 ∧ stdRowDatum σ χ A.L' = A.stdDatum (c * invOnUnits χ ·.det) := by
  refine' A.blocks_spec |> fun _ ↦ (⟨_, hχ.norm_eq_one ·, funext fun x ↦ if_congr _ (invOnUnits_eq_mul_of_unit ‹_› ▸ _) _⟩) (isPrimitiveMatrix_iff_isIntegralUnit_det (A := (A.L.fromCols (A.K.fromCols A.I)).submatrix id σ.symm).1 ⟨_, (A.L'.fromRows (A.K'.fromRows A.I')).submatrix σ.symm id, _⟩).2 <;> simp_all [IsIntMatrix, reindex_equiv σ, ↓fromRows_mul_fromCols, ← det_mul, ← submatrix_mul]
attribute [local simp] mul_add stdColDatum
include hS hP hΨ Q
lemma partner_mem_of_stdColDatum {p x s} (hp : p ∈ P) (hx : IsIntMatrix O x) (hs : IsIntMatrix O s) (e₁ : s * x = 1) (r : _ → ℕ) (H : ∀ y, p y = r y • stdColDatum χ s y) (h₁ : r x ≠ 0) : Ψ ∈ P := by
  obtain ⟨⟨c, hc⟩, _⟩ := ((V.unif_nilpotent.smul_const (.id _)).eventually (ContinuousMap.eventually_mapsTo isCompact_O.matrix ((isLocallyConstant_curry (Q.mem_matchingPairs hχ hΨ).1.2 (· + ·) (-· + ·)).isOpen_fiber Ψ) (by simp_intro _))).exists, (isCompact_intGL (n := n) V.isCompact_O).compactSpace
  let d : GL n F := V.ϖ⁻¹ ^ c • .mk'' (1 - x * (s - V.ϖ ^ c • s)) (by simp [↓det_one_sub_mul_comm x, *])
  have L := isLocallyConstant_curry (Γ := intGL n O) (hS hp) (d.1 * ·.1.1 * ·) (·.1.2 * d.2 * ·)
  rw [← P.smul_mem_iff ((L.comp (‖· x‖)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := .haar) (x := 1) (.of_compactSpace _) (by simp_intro _) (by simp [d, invOnUnits, *])).ne']
  convert ← integral_mem_of_isLocallyConstant .haar (L.comp (norm ∘ · • Ψ)) fun k ↦ (funext fun y ↦ ?_).subst (P.smul_mem (Ψ (k.1.2 * x)) (hP (d * k) _ hp))
  obtain ⟨_ | ⟨l, c, ⟨⟩⟩, j, a, ⟨⟩⟩ := not_or_of_imp (Q.2 ‹_›), (valPair.exists_firstCols_iff e).2 ⟨hx, by tauto⟩
  simp_all; rw [← integral_mul_right_eq_self _ ⟨_, div_mem a c⟩]
  simp [show ∀ g k : GL n F, g.1 * firstCols e k = firstCols e (g * k) from fun _ _ ↦ rfl, ← integral_smul_const]
  simp [H, invOnUnits]; split_ifs with i v <;> simp [hχ.norm_eq_one, *]
  have ⟨g, m, _⟩ := isPrimitiveMatrix_iff.1 (isPrimitiveMatrix_iff_isIntegralUnit_det.2 ⟨hs.mul i, v⟩)
  erw [← Q.right_mul _ m, ← congrFun (hc (k.2.isIntMatrix_inv.mul (i.sub (hx.mul m.isIntMatrix)))), (_ : V.ϖ ^ c • _ + _ = y)]; grind [hχ.norm_eq_one v, norm_zero]
  simp [d, *, smul_sub, ← Matrix.mul_assoc, sub_sub]
lemma IntegralFrame.partner_mem_of_unimodular_vanishing {ψ} {M : Submodule ℂ _} (hψ : HasIntegralConductor ψ) :
  let S (z : Matrix b b F) y := stdColDatum χ A.K' (y + A.L * z * (A.K' * y))
  (∀ z, S z ∈ M) → (∀ Ψ ∈ M, (∀ T (Λ : _ →ₗ[ℂ] ℂ), (∀ z, Λ (S z) = ψ (T * z).trace • Λ (stdColDatum χ A.K')) → (IsPrimitiveMatrix O T → Λ (stdColDatum χ A.K') = 0) → Λ Ψ = 0) → Ψ ∈ P) → Ψ ∈ P := by
  obtain ⟨R, π, η, κ, u, d⟩ := id hχ
  let l r := ite (r = 1) 1 (@map b b _ _ r (surjInv κ.1))
  intro S hM h₂
  obtain ⟨⟨c, _, aK, aL, aK', _⟩, ⟨φ, hφ, e⟩, hl⟩ := A.blocks_spec, exists_primitive_residue_addChar κ hψ.2, fun r ↦ congrFun₂ (by aesop : (l r).map π = r)
  use partner_mem_of_stdColDatum hP hS hΨ Q (hP (-V.ϖ⁻¹ • 1) _ (h₂ (∑ r, η r.det • S (V.ϖ.2 • (l r).map (↑))) (sum_mem (by bound)) fun T Λ hZ _ ↦ by_contra ?_)) (aL.sub (aK.smul ϖ_mem)) c
    (by simp [*]) _ (fun y ↦ .trans (sum_apply ..) ((sum_filter_ne_zero _).symm.trans (sum_eq_card_nsmul ?_))) (card_ne_zero.2 ⟨1, by simp [l, ← Units.smul_def, S, invOnUnits, *]⟩)
  simp_intro q [hZ, ← mul_assoc, ← sum_mul]
  have i a b := (hψ.2 _).1 fun s _ ↦ by simpa [trace_mul_single] using ((right_eq_mul₀ q.2).1 (.trans (congrArg _ (by grind [stdColDatum, IsIntMatrix.add, mul, IsIntMatrix.sub, =_ Matrix.mul_assoc, add_sub_cancel_right, Matrix.mul_add, IsIntMatrix, zero_mem])) (hZ (.single b a s))))
  obtain := (matrix_gauss_sum hφ u (η ·.det) (by simp)).1 (of (π ⟨_, i · ·⟩)), d (det (of (⟨_, i ·
    ·⟩))), isPrimitiveMatrix_of_stdColDatum_ne_zero (χ := χ) .one T, (e <| trace <| of (⟨_, i · ·⟩) * l ·)
  simp_all [matrixFourier, trace, mul_apply, det_apply', η.inv_apply_eq_inv, IsIntMatrix]
  simp_intro r hr
  obtain ⟨_, g, i, k, _⟩ := d (l r).det, show IsIntMatrix O ((l r).map (·.1)) by
    simp [IsIntMatrix], isIntMatrix_of_stdColDatum_ne_zero aK' hr.2
  obtain := d (det (of (⟨_, g.mul k · ·⟩) - of (⟨_, ϖ_mem⟩ * ⟨_, mul c i · ·⟩))), d (det (of (⟨_, g.mul k · ·⟩))), (aL.mul (g.mul k)).sub (i.smul ϖ_mem), invOnUnits_mul (χ := χ) g.det_mem k.det_mem
  simp_all [↓S, ↓← det_mul, det_apply, (κ.2 _).2, ← Matrix.mul_assoc, Units.smul_def, smul_smul, ← mul_assoc, -MulMemClass.mk_mul_mk]
end
section
open RingHom Matrix Pi WeilData SemilocalField Fintype SplitTameChar GeneralLinearGroup
variable {E} [Field E] [CMType E] [WeilData E] {n a b} [Fintype n] [Fintype a] [Fintype b] {s t t' μ} (W : Space E n s) (V : Space E a t) (V' : Space E b t') (𝔠 : SplitTameChar E μ)
noncomputable abbrev thetaSmall v (Ψ : _ → ℂ) := thetaIntegral W V (rankTwist 𝔠.ν n) (upsilonU1 ^ card a) (localDatum W V v (Ψ ·ᵀ) 𝔠.readsAt.star)
attribute [local simp] atPlaces_star atPlaces_of_mem_trivialOn nu_det_of_mem_Kf MulChar.inv_apply_eq_inv'
private lemma detOn_star {n' : Type} [Fintype n'] {A : Set (FinPlace E)} (g : Gf E n') : detOn (star ⁻¹' A) g.1 = star (detOn A g.1)⁻¹ := by ext <;> simp [detOn, cutGL, star_idem, ← det_conjTranspose, inv_eq_left_inv g.2]
lemma exists_isEquivariantLift σ (hn : 2 ∣ card n) {v v'} (hv : IsRapidDatum v) (hv' : IsRapidDatum v') (c : ℂ) : ∃ M 𝒟, IsEquivariantLift
  𝔠 W (localChar _ (υ ^ card b) (card b))⁻¹ M 𝒟 ∧ ∀ {Φ Ψ}, IsLocallyConstant Ψ → IsPartner O σ 𝔠.χ Φ Ψ → Ψ ∈ M ∧ 𝒟 Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W V' 𝔠 v' Ψ := by
  obtain ⟨⟨Λ, H⟩, ⟨Λ', H'⟩, r, r'⟩ := exists_linear_thetaIntegral W V .., exists_linear_thetaIntegral W V' .., 𝔠.readsAt, 𝔠.readsAt.star
  have e := matchingPairs.exists_linear_factor _ σ (𝔠.tameLocalChar (card n)) (Λ ∘ₗ ⟨⟨(localDatum W V v · r), ?_⟩, ?_⟩) fun g Φ hΦ ↦ ?_
  let l := e.choose - c • Λ' ∘ₗ ⟨⟨fun Ψ ↦ localDatum W V' v' (Ψ ·ᵀ) r', ?_⟩, ?_⟩
  have e {p} m : l _ = _ := congr($((e.choose_spec p m).trans (H (r.isTargetBounded hv m.1.1) :)) - c • $(H' (r'.isTargetBounded hv' m.1.2.transpose_mem_schwartzBruhat)))
  refine ⟨.map (.snd ..) _, _, ⟨fun _ ⟨_, m, e⟩ ↦ e ▸ m.1.2, ?_, ?_, ?_⟩, fun h ⟨p, q, _⟩ ↦ (fun m ↦ ⟨⟨_, m, rfl⟩, e m⟩) (IsPartner.mem_matchingPairs (𝔠.tameLocalChar _) ⟨p, q, by simp_all [intGL, localChar_apply_of_isUnit, ← val_det_apply, GeneralLinearGroup.map_det]⟩ h)⟩ <;> rintro _ ⟨p, m, rfl⟩ <;> erw [e m]
  simpa using (Space.Splitting.centreCoeff_sub (W₀ := W) (p := n) (r.isTargetBounded hv m.1.1).isAutFunction_thetaIntegral (r'.isTargetBounded hv' m.1.2.transpose_mem_schwartzBruhat).isAutFunction_thetaIntegral c 1).1
  intro g hg; have q := matchingPairs.translate_mem _ σ m (atPlaces _ g⁻¹); use ⟨_, q, rfl⟩; erw [e q]
  any_goals simp only [sub_def, Pi.smul_apply, ← thetaIntegral_pairWeil (_, 1, 1)]
  simp +contextual [localDatum, ↓pairWeil_integrated_fin, ↓pairWeil_name_on r.1 (hΨ := r.isSchwartzBruhat q.1.1), ↓pairWeil_name_on r'.1 (hΨ := r'.isSchwartzBruhat q.1.2.transpose_mem_schwartzBruhat), Gf.mem_supportedOn.1 hg, ↓detOn_star, AutChar.spaceChar, ← Pi.smul_def, eq_mul_inv_of_mul_eq (spaceChar_rankTwist hn), -smul_eq_mul, ↓localChar_det, υ_star, -coe_comp]
  simp [sq, mul_pow, ← card_congr σ, field, pow_add, thetaIntegral, pairTheta]
  simp_all [↓r.pairWeil_localDatum_of_mem_Kf m.1.1, ↓r'.pairWeil_localDatum_of_mem_Kf m.1.2.transpose_mem_schwartzBruhat, rankTwist, -coe_comp]
  any_goals simp [localDatum, ← add_def, ← Pi.smul_def, -smul_eq_mul]
  ext x; obtain ⟨⟨k, _, rfl⟩, d, _⟩ := 𝔠.exists_atPlaces_eq g, r.isTargetBounded hv hΦ, r.isSchwartzBruhat hΦ
  erw [H d, ← mul_one x, ← thetaIntegral_pairWeil (1, ↑k⁻¹), ← H (Exists₂.imp (by simp_all [pairTheta, pairWeil, rep_apply_apply, ← map_mul]) d), pairWeil_integrated_fin, pairWeil_name_on] <;> simp_all [r.1, spaceChar_rankTwist]
end
section
open G Gf MatMul Matrix RingHom SemilocalField WeilData Space.Splitting
attribute [local simp] conjTranspose_nonsing_inv isUnit_iff_isUnit_det Matrix.map_neg map_smul' Units.smul_def add_mul mul_add mul_assoc mul_sub smul_smul star_idem star_invDifferentIdele_inv
lemma IsEquivariantLift.apply_stdColDatum_eq_zero {E} [Field E] [CMType E] [H : WeilData E] {n a b m} [Fintype n] [Fintype a] [Fintype b] [Fintype m] {s t r μ} {𝔠 : SplitTameChar E μ} {ρ} {X : Space E m r} {W₁ : Space E n s} {W : Space E a t} {M 𝒟} (h : IsEquivariantLift 𝔠 X ρ M 𝒟) (D : X.Splitting W₁ b) (D₁ : W₁.Splitting W Unit) [IsBaseAdapted D] [IsBaseAdapted D₁] {t'} (V' : Space E b t') (h₀ : ∀ T c z q g, (∃ Y, ∃ k ∈ intGL b (Ô E), scaleIdele E • V'.x * Y = q ∧ Y.map (.snd ..) * k ∈ U 1 ∧ V'.J = T) ∨ IsUnit T ∧ ¬RepresentedBy t' (T.map toAdele) → D.centreCoeff (H.j • T) (𝒟 (stdColDatum 𝔠.χ (adaptedFrame 𝔠.readsAt D).L')) (D.radicalElt c z * D.levi (q, g)) = 0) (hΨ : stdColDatum 𝔠.χ (adaptedFrame 𝔠.readsAt D).L' ∈ M) (σ : b ⊕ b ⊕ n ≃ m) {z} (i : IsIntMatrix O z) : 𝒟 (stdColDatum 𝔠.χ z) = 0 := ((adaptedFrame 𝔠.readsAt D.symm).partner_mem_of_unimodular_vanishing h.comp_mul_mem_ker (fun _ ↦ (h.le_schwartzBruhat ·.1)) (stdColDatum_mem_schwartzBruhat _ i).1 (isPartner_stdRowDatum_stdColDatum σ i) 𝔠.readsAt.hasIntegralConductor_psi (by simpa using! ((h.exists_linear_centreCoeff D 0 1).choose_spec _ hΨ).2 · |>.1) fun Ψ w c ↦
  have k := h.isAutFunction w; ⟨w, funext ((X.weak_approximation 𝔠.S.finite_toSet).eq (fun ⟨γ, g, hg⟩ ↦ .trans (by simp [k.2]) (IsDualFamily.eq_zero_of_coeff (D.isContPeriodic_radicalCentre k (1, g)) (fun T p ↦ (h.exists_linear_centreCoeff ..).elim fun _ L ↦ (L _ w).1.symm.trans (c _ _ (by simpa [-map_smul', atPlaces_of_mem_trivialOn hg, fun x ↦ (id rfl : (mat x).map (componentsAt 𝔠) = (atPlaces _ _).1)] using! (L _ hΨ).2 · |>.2) fun P ↦ (L _ hΨ).1.trans (by
obtain ⟨hT, a, d, A, _, e', -⟩ := eq_neg_of_add_eq_zero_left (isDualFamily_ratMatrices.6 (Tᴴ + T) fun X ↦ by simpa [↓isDualFamily_ratMatrices.2, ↓isDualFamily_ratMatrices.3, ← stdAddChar_half (trace _), ← trace_conjTranspose, add_comm, X.trace_mul_comm, Xᴴ.trace_mul_comm] using p (Xᴴ + X) 1 (by intro; simp; congr! 2; exact (ext_mat (by simp [add_sub_add_comm])))), h.isAutFunction hΨ, (by simpa [← mapMatrix_apply, ← map_det, ·] using (isPrimitiveMatrix_iff_isIntegralUnit_det.1 P).2 : T.det ≠ 0), exists_isBaseAdapted_stage (D.comp D₁) (.sumComm ..)
refine freitag (supportedOn_compl.substr (h.law_off _ hΨ)) a A _ congr(toCols₂ $(congr(_ * ($e').map _).symm.trans (comp_kAdelic ..))) d (.star 𝔠.nonempty) (fun A e g w _ ν _ _ p q ↦ (h.exists_linear_centreCoeff ..).elim fun _ l ↦ have k : (adaptedFrame 𝔠.readsAt D).L' = ((removePlanes b W).lCoord * A.iCoord * (ν * g).mat).map (componentsAt 𝔠) := ?_; .trans (l _ hΨ).1.symm ((h.centreCoeff_shear _ _ hΨ (by simpa [Prod.star_def] using q) p _).elim fun a c ↦ shear_invariant (adaptedFrame _ D).blocks_spec.1 ?_ h.le_schwartzBruhat (fun Ψ a z ↦ ?_) hΨ a ▸ (l _ a).1 ▸ c.trans (by simp))) (fun x γ v ⟨y, _, y', _⟩ ↦ ?_) (by clear * -; aesop (add simp idem_apply)) (supportedOn_compl.ge hg)
funext i j ⟨u, h⟩
simpa [lCoord.eq_1 D, componentsAt, adaptedFrame, 𝔠.star_notMem, *, ↓mat_preserves_stdForm] using
  congr((($wᴴ * stdForm E r * g.mat) i j).2 u)
simp [*, ← Matrix.map_mul, ← mat_mul, ← (mat _).mul_assoc]
simpa [k, trace, mul_apply, comp_kAdelic] using ((l _ a).2 ((fromCols 0 z).fromRows 0)).2
let τ := (invDifferentIdele E)⁻¹ • (GeneralLinearGroup.mkOfDetNeZero T d).map toAdele
obtain ⟨hτ, l, z, q, g, rfl, o⟩ := (by simp [*, τ] : τ.1ᴴ = τ), D.exists_eq_radicalElt_mul_levi v
have i {M N : Matrix b ..} (hN : Nᴴ = N) (a : IsIntMatrix (closureIntegers _) M) (c : IsIntMatrix O (N.map (componentsAt 𝔠))) : let e : 𝔸 E := idemAdele (Set.conjClosure 𝔠.S)ᶜ.conjClosure; IsIntMatrix (Ô E) ((e • M + (1 - e) • N).map Prod.snd) := fun i j ↦ add_mem (a i j) (by simpa [← idem_compl, idem_mul_mem_Ô] using (fun v h _ ↦ by_cases (c i j ⟨v, ·⟩ ⟨⟩) fun l ↦ hN ▸ (v_star_apply ..).trans_le (c j i ⟨_, h l⟩ ⟨⟩)))
have ⟨k, K, e⟩ := exists_orthonormal_Ô ⟨by simp [← conjTranspose_map _ Prod.snd_star, siegelBracket, *], isPrimitiveMatrix_iff.1 ⟨i hτ y P.1, _, i ?_ y' ((isPrimitiveMatrix_iff_mem_intGL (τ.map _)).1 P).isIntMatrix_inv, ?_⟩⟩
rw [show _ + _ = siegelBracket T q.1 by simp [o, siegelBracket, τ, mul_comm], siegelBracket] at e
obtain ⟨⟨β, rfl⟩, q, rfl⟩ := MulAction.surjective₀ H.j_ne_zero T, MulAction.surjective (scaleIdele E) q
simp [show scaleIdele E * (toAdele H.j * star (scaleIdele E).1) = invDifferentIdele E by simp [invDifferentIdele, mul_left_comm]] at d e ⊢
by_cases R : RepresentedBy t' (β.map toAdele)
obtain ⟨c, w, rfl : _ = β, f, -⟩ := V'.exists_eq_move ⟨β, _, gram_mkAdelicGL (b := q.map (.snd ..) * k) (fun v ↦ gram_inv_of_gram_eq (x := (isUnit_of_mul_isUnit_right ((R v).choose_spec.substr (.map (mapMatrix _) (by simpa)))).unit) (R v).choose_spec) (by simpa [← coe_snd] using! e)⟩
rw [← smul_mul, ← mul_smul_comm, ← centreCoeff_rat_mul _ a _ (levi_mem_Γ _ _ (one_mem _)) _ (levi_mul_kAdelic ..), ← mul_assoc, levi_conj_radicalElt, mul_assoc, ← map_mul, h₀]
refine .inl ⟨V'.x⁻¹ * (c.map toAdele * q), _, K, Units.ext (by simp), ?_, rfl⟩
convert w.2.2; simpa using! congr($(inv_mul_eq_of_eq_mul f).map _)
all_goals simp [← coe_snd, ← Matrix.map_mul, sub_mul, *]))) 0)) k.1)⟩).2
end
section
attribute [-simp] map_zero map_neg
open Matrix MatMul MeasureTheory Measure Space Pointwise Pi Fintype MulAction ComplexConjugate ComplexOrder MatrixOrder Heisenberg.IsVacuum Finset CStarAlgebra Kronecker
attribute [local simp] neg_eq_iff_eq_neg vecMulVec_mulVec card_subtype_le vecMulVec_apply blockDiagonal pairSign sum_prod_type mul_vecMulVec vecMulVec_mul neg_mulVec commute_iff_eq star_mulVec rep_apply_apply mulVec Matrix.single_apply negCount RCLike.mul_conj mul_assoc add_mul ite_and vecMul mem_blockDiagAlg_iff_commute pairHomInf pairHom holCoord_eq
attribute [local simp ←] dotProduct_mulVec replicateCol_mulVec
lemma centreCoeff_eq_zero_of_not_negative {E} [Field E] [CMType E] [H : WeilData E] {a b m n}
  [Fintype a] [Fintype b] [Fintype m] [Fintype n] {r ν} {X : Space E m r} {s} {Y : Space E n s} {t}
  {Z : Space E a t} {D : X.Splitting Z b} {μ ψ δ f g T} [AutChar.HasWeight ν μ ψ] i (hγ : ∀ τ, μ τ < negCount (-t)) (ht' : s i = 1) (ht : card b + negCount t = negCount s) (d : δ = ν * H.upsilonU1 ^ card b) (h₀ : IsUnit T) (hR : ¬RepresentedBy (-1) (T.map toAdele)) (hi : D.HasIntegrableTerms Y δ δ f g) : D.centreCoeff (H.j • T) (thetaIntegral X Y δ δ f) g = 0 := by
  obtain ⟨⟨τ, hβ⟩, e | ⟨x, rfl⟩⟩ := not_forall.1 hR, isEmpty_or_nonempty {x : Matrix n b E | xᴴ * Y.J * x = T}
  simpa [tsum_empty] using! D.centreCoeff_integral_eq_tsum hi T
  let x' := Y.x⁻¹.1 * x.map toAdele
  rw [← gram_at_point_eq_map, ← gram_map_real] at hβ
  set w := atRealPlace x' τ with ← e
  obtain ⟨h, M, hM⟩ := isHermitian_conjTranspose_mul_mul w posProj_mul_self.2.2, (hγ τ).dest
  obtain ⟨v, -, hv⟩ := herm_represents_one h ⊤ fun _ ↦ hβ (by simpa [eq_comm] using! (nonneg_iff_eq_star_mul_self.1 (posSemidef_iff_dotProduct_mulVec.2 ⟨h.neg, by simp_all⟩).nonneg))
  have ⟨u, hu⟩ := witt ⟨.I, by simp⟩ (posProj_mul_self (ε := s)).2.2 IsHermInvolution.isUnit
    (.of_ne_zero (x := w *ᵥ v) (by simp [← mulVec_mulVec, ·] at hv))
    (.of_ne_zero ((basisFun ℂ _).ne_zero i)) (by ext; simp_all [← replicateRow_vecMul, signMatrix])
  have K (l : PairFock E t s →L[ℂ] ℂ) (k : ∀ c ∈ maxCompactU s, c.1.1 * (u.1.1 * w) = u.1.1 * w → ∀ v, l (realPairWeil μ 0 (1, mulSingle τ c) v) = l v) : l = 0 := hom_ext fun y ↦ by
    let f := ((u.1.1 * w).vecMulLinear.prod (of fun i (j : {j // t j = -1}) ↦ y (τ, i, j)).vecMulLinear).prod (.funLeft ℂ ℂ (@Subtype.val _ (s · ≠ -1)))
    have : Nonempty {k // s k ≠ -1} := ⟨⟨i, by simp [ht']⟩⟩
    obtain ⟨r, hr, h1⟩ := herm_represents_one isHermitian_one f.ker fun n ↦ have ⟨r, h⟩ := (f.linearEquivOfInjective (.of_ker f (by simpa [(dotProduct_star_self_nonneg _).ge_iff_eq'] using n)) (by simp_all)).surjective (0, 1)
      by simpa [f, by simpa using hu] using congr($h.1.1 ⬝ᵥ v - $h.2 ⟨i, by simp [*]⟩)
    simp [f, funext_iff, dotProduct_comm] at hr h1
    let z := .single τ τ 1 ⊗ₖ (vecMulVec (star r) r ⊗ₖ diagonal 1) *ᵥ y
    let F (η : ℂ) : PairFock E t s := η ^ M.succ • realHeisOp (y + (conj η - 1) • z) vacVector
    have e (L : _ →L[ℂ] _) {f} (h : ∀ η, η * conj η = 1 → L (F η) = f η) d := (L.integral_comp_comm integrable_of_compactSpace).symm.trans (congr(∫ θ, $(h _ (by simp))).trans (@integral_toCircle f d))
    refine (e l (fun η h0 ↦ ?_) (differentiableOn_const _)).symm.trans (.trans (congrArg l (ext fun w ↦ (e (modelEval w) (fun η h0 ↦ by rw [map_smul, valueAt_apply, heisOp_apply, Heisenberg.IsVacuum.vacElem_apply, beta_mul_realVac, (by simp [realVac, z, *]; clear * - h0; grind : realVac (y + _) = realVac y), map_add, (show Function.IsFixedPt (holCoord _) (_ • z) by
           funext p; by_cases s p.2.1 = -1 <;> simp [*, z, dotProduct, ← mul_sum]
           clear * - hr; grind [dotProduct])]) (by simp; fun_prop)).trans (by simp))) l.map_zero)
    have : posProj s *ᵥ star r = 0 ∧ r ᵥ* posProj s = 0 := by simp +contextual [funext_iff, posProj, *]
    convert k (U.of IsHermInvolution.isUnit (1 + (conj η - 1) • vecMulVec (star r) r) ?_)
      (ext ?_) ?_ _
    any_goals simp [← Matrix.ext_iff, signMatrix_eq_posProj_sub, *] <;> clear * - h0 <;> grind
    rw [realPairWeil_apply_apply, weilRep_heisOp, ← map_smul, ← realPairWeil_apply_apply, ← vacVector, ← polyVector_one, realPairWeil_polyVector, Fintype.prod_eq_single τ, map_smul]; congr! 3
    · simp [principalMinor_eq_det, ← posProj.eq_1, *, eq_inv_of_mul_eq_one_right h0, eq_sub_of_add_eq hM]
      rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_mul_comm]
      simp +contextual [*, ite_eq_left_iff.2, ← zpow_natCast]
    all_goals simp [funext_iff] <;> intro w <;> by_cases τ = w <;> simp [*, z, dotProduct, mul_sum, signMatrix_eq_posProj_sub]
  let H := stabilizer (G E s) x'
  obtain ⟨h : IsClosed H.carrier, I, -, J⟩ := isClosed_singleton.preimage (f := (G.mat · * x'))
    (by fun_prop), D.centreCoeff_eq_integral_stabilizer hi h₀ fun _ ↦ (stabilizer ..).mem_map
  let U : G .. := (mulSingle τ u⁻¹, 1)
  let C := (ConjAct.toConjAct U • maxCompact ..).subgroupOf H
  have c : @IsCompact H _ C := (isCompact_maxCompact.smul _).preimage_val
  obtain ⟨⟨_, A, B⟩, _, _⟩ := exists_compact_superset c, c.compactSpace, c.isClosed
  have law (k : H) h := by simpa [← d, x', -coe_units_inv, (id k⁻¹.2 : k.1⁻¹.mat * x' = _)] using D.sourceTerm_levi _ ν δ 1 1 k x' (pairWeil _ _ δ δ (g, h) f)
  let κ := (haar (@.univ C))⁻¹ • haar (G := C)
  have : MeasurableConstSMul Cᵐᵒᵖ C := ⟨fun c ↦ measurable_mul_const c.unop⟩
  have : (haar (G := C)).IsMulRightInvariant := inferInstance
  have : κ.IsMulRightInvariant := isMulRightInvariant_smul _
  simpa using! J.trans (integral_quotMeasure_eq_zero_of_mean _ I (by fun_prop [Splitting.thetaTerm]) (fun _ ⟨_, _, e⟩ ↦ e ▸ (ratMap_mul_toAdele ..).trans (by congr)) κ (fun _ ↦ (↑)) 1 (fun _ k ↦ (one_smul ..).substr (((haarMeasure_unique ..).congr (haarMeasure_unique _ ⟨⟨_, A.mul c⟩, _, subset_interior_mul_left ⟨_, B k.2, k, k.2, rfl⟩⟩)).2 congr($(by simp [Set.preimage, (measurableEmbedding_mulRight _).map_apply, ← QuotientGroup.preimage_image_mk_eq_mul]) • _))) zero_ne_one fun k _ ↦ let T (c : C) := θ _ ∘L pairWeil Z Y ν δ (1, k * (c * U))
    have e := strongIntegral_apply κ T fun _ ↦ integrable_of_compactSpace (by simp [T]; fun_prop)
    by simpa [↓law, e, T, Splitting.thetaTerm] using ext_integrated _ (projOn_empty _ (pairWeil _ _ ν δ (1, U⁻¹) _)) fun _ _ _ ↦ DFunLike.congr_fun (K (strongIntegral κ T ∘L (integrated _).flip _) fun c _ _ v ↦ let p := U * (mulSingle τ c, 1) * U⁻¹
      by simpa [← pairWeil_integrated_right ν δ, e, T, p] using integral_mul_right_eq_self (T
        · _) ⟨⟨p, matrix_ext_𝔸 (fun w ↦ Matrix.map_mul.trans (show (p.1 w).1.1 * atRealPlace x' w = atRealPlace _ w by by_cases w = τ <;> simp [p, U, *])) (Matrix.map_mul.trans (by
          simp [p, U]; apply Matrix.one_mul))⟩, _, ⟨by simpa, by simp⟩, rfl⟩) _)
end
section
open Fintype MatMul Matrix MeasureTheory Prod SemilocalField Space WeilData Splitting
variable {E : Type} [Field E] [CMType E] [WeilData E] {n} {a : Type} {b m} [Fintype n] [Fintype a] [Fintype b] [Fintype m] {s t r} {X : Space E m r} (W₁ : Space E n s) (D : X.Splitting W₁ b) (V : Space E a t) [IsBaseAdapted D] {W : Space E a t} (D₁ : X.Splitting W Unit) {μ} (𝔠 : SplitTameChar E μ)
noncomputable def thetaOnRealData α γ F x p := θ _ ∘L ϱ _ (matToVec x) ∘L pairWeil W₁ V α γ p ∘L (integrated _).flip F
lemma thetaTerm_stdDatum_spec {P A π} [Nontrivial (@LocProd E _ _ P)] (h : ReadsAt A π) {Φ U v β β'}
  γ χ ε (N : Matrix (b ⊕ n) a (LocProd P)) (hΦ : Φ ∈ schwartzBruhat U) (e : Φ = (adaptedFrame h D).stdDatum fun y : Matrix a _ (LocProd P) ↦ ε * invOnUnits χ (y * N).det) (hv : IsRapidDatum v) (hβ : β' = β * upsilonU1 ^ card b) c z q g : let f := localDatum X V v Φ h;
    let p := D.radicalElt c z * D.levi (q, g); (D.HasIntegrableTerms V β' γ f p ∧ ∀ x x' (Y : Matrix a b (𝔸 E)), V.x⁻¹.1 * Matrix.map x toAdele = x' → x' * q.1 = scaleIdele E • Y → ∀ k, let y := k.2⁻¹.1.1 * Y.map snd; (delta% D.thetaTerm V β' γ f p x k) = stdAddChar E (toAdele 2⁻¹ * (z * (xᴴ * V.J * x).map toAdele).trace) * (((γ.spaceChar (card a)).1 q.det : ℂ)⁻¹ * √(ideleAbs q.det) ^ card a * (ite (IsIntMatrix (Ô E) y) (vacuumFactor (isAdapted_homSource D V)).1 0 * thetaOnRealData W₁ V β γ (namedVector _ V (fun y' ↦ ite (IsIntMatrix O y') (ε * invOnUnits χ (fromCols (y.map π) y' * N).det) 0) h) (x' * cᴴ * stdForm E s) (g, k) (realSlice D V (k⁻¹.mat * Y) v)))) ∧ ∀ t' T, ¬RepresentedBy t'
      (T.map toAdele) → (∀ x, realSlice D V x v ≠ 0 → RepresentedBy t' (xᴴ * stdForm E t * x)) → D.centreCoeff ((j : E) • T) (thetaIntegral X V β' γ f) p = 0 := by
  intro f p; refine (fun O ↦ ⟨O, fun _ T hT hv ↦ ?_⟩) ⟨D.hasIntegrableTerms_integrated_name _ _ _ h.1 (h.isSchwartzBruhat hΦ) π hv fun y i ↦ ?_, fun x x' Y hx hY k ↦ ?_⟩
  convert ← D.centreCoeff_integral_eq_tsum O.1 T; simp [thetaIntegral]; convert tsum_zero with ⟨x, ⟨⟩⟩
  convert integral_zero .. with h; obtain ⟨q, ⟨⟩⟩ := MulAction.surjective (scaleIdele E) q
  rw [O.2 x _ _ rfl (Matrix.mul_smul ..), hT.imp_symm fun o u ↦ (hv _ o u).imp' (· * atRealPlace q⁻¹.1 u) fun y e ↦ .trans ?_ congr($(gram_inv_of_gram_eq rfl).map (evalInf u))]; simp; swap
  rw [Matrix.map_mul, Matrix.map_mul, gram_mul, e, gram_mul, G.mat_preserves_stdForm, gram_mul, gram_at_point_eq_map]; rfl
  simp [e, IntegralFrame.stdDatum, invOnUnits, χ.apply_eq_zero_iff, -mul_fromCols] at i
  erw [← fromCols_map, ← (?_ : X.coordMatrix p (D.k.fromCols D.i) * fromBlocks q _ 0 _ = D.kAdelic.fromCols _), Matrix.map_mul] at i
  exact ⟨_, by simpa [← Matrix.mul_assoc] using
                 congr($(mul_nonsing_inv _ i.2.2.choose_spec.2.2.2)ᵀ)⟩
  erw [Matrix.mul_assoc, G.mat, map_inv, coe_units_inv, inv_mul_eq_iff_eq_mul_of_invertible]
  simp [p, G.ofMat, radicalElt, Splitting.levi, ↓mul_fromCols]
  simp [kAdelic, iAdelic, Space.ratMap]; ac_rfl
  rw [hβ, ← one_mul k, ← mk_mul_mk, ← rep_apply_apply, sourceTerm_radicalElt, gram_at_point_eq_map, hx, sourceTerm_levi, k⁻¹.mat.mul_assoc, hY, Matrix.mul_smul, h.sourceTerm_localDatum D V hΦ _ _ (imp_intro congr($e ·))]
  simp_rw [one_mul, map_smul, Matrix.map_mul]; rfl
lemma thetaOnRealData_boxProd_eq_mul {E n b} {s t'} [Field E] [CMType E] [WeilData E] [Fintype n]
  [Fintype b] {W₁ : Space E n s} (V' : Space E b t') α β f F c g u φ v l : thetaOnRealData W₁
  (V'.sum W₁) α (α * β) (Space.boxProd homSigns_sum_target f F) (.fromRows c 0) (g, .sum (u, l))
  (realBoxProd (realSigns_comp_split homSigns_sum_target) φ v) = thetaOnRealData W₁ V' α β f c (g, u) φ * pairTheta W₁ W₁ α α (integrated _ v F) (g, l) := by
  dsimp [thetaOnRealData]; erw [← boxProd_integrated, mul_comm, pairWeil_boxProd_target, rho_boxProd, theta_boxProd_target, Heisenberg.Rep.rho_zero_apply] <;> bound
lemma thetaLarge_eq_apply_one_of_even_rank [IsBaseAdapted D₁] {v} (hn : 2 ∣ card m) (hv : IsRapidDatum v) g : thetaLarge X X 𝔠 v (stdColDatum 𝔠.χ 1) g = thetaLarge X X 𝔠 v (stdColDatum 𝔠.χ 1) 1 := by
  obtain ⟨⟨_, _, _, _, L⟩, _, _, R, H⟩ := exists_constant_term_thetaLarge D₁ D₁ (.emptySum Empty _)
    (.emptySum ..) (by grind [D₁.card_eq]) μ, exists_isEquivariantLift X X (stdSpace E Empty) 𝔠 (.emptySum ..) hn hv isRapidDatum_vacVector 0
  obtain ⟨O, e⟩ := by simpa using H (.of_discrete _) (isPartner_stdRowDatum_stdColDatum (s := 0) _ nofun)
  erw [← e, (R.isAutFunction O).apply_eq_apply_one D₁ 𝔠.nonempty (by convert (R.law_on O · · |>.2) <;> simp [← ext_iff, MulChar.inv_apply_eq_inv']) (R.law_off _ O) fun N ↦ ⟨_, fun t g ↦ by simpa [← e, N, (by ext <;> simp : .scalar _ t.det = t)] using (L 𝔠).choose_spec.2.2 v hv 0 nofun t.det g⟩]
noncomputable def equalRankThetaRatio v := ‖thetaLarge V V 𝔠 v (stdColDatum 𝔠.χ 1) 1‖ ^ 2 / lValueProdInt 𝔠 (card a / 2)
def StdExchange {t' r} (X : Space E m r) (V : Space E n s) (V' : Space E b t') μ σ v y (ℓ : _ → ℝ) := IsRapidDatum v ∧ IsRapidDatum y ∧ ∃ C, ∀ 𝔠 : SplitTameChar E μ, ∃ c : ℂ, C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (card n - card m / 2) * ℓ 𝔠 ∧ ∀ z, IsIntMatrix O z → thetaLarge X V 𝔠 v (stdRowDatum σ 𝔠.χ z) = c • thetaSmall X V' 𝔠 y (stdColDatum 𝔠.χ z)
attribute [local simp] IsIntMatrix blockGL mem_integralBox
attribute [local simp↓] Circle.coe_ne_zero mul_eq_zero ne_eq pow_eq_zero_iff'
variable (X) {W₁} {t'} (D₁ : W₁.Splitting W Unit) (V' : Space E b t')
lemma stdExchange_of_periods [IsBaseAdapted D₁] {σ' v v'} (l : _ → ℂ) (hn : 2 ∣ card n) {ρ : GInf E (t' ⊕ᵥ s) → ℝ} (h₀ : 0 ≤ ρ) (h₁ : ∀ᶠ h in nhds 1, ρ h ≠ 0) (hv : IsRapidDatum v) (hv' : IsRapidDatum v') (hc : ∀ 𝔠 : SplitTameChar E μ, let γ := rankTwist 𝔠.ν⁻¹ n; ∀ h, ∃ p, ∀ (B : GL b _) (z : _ˣ), (det <| atRealPlace B.1 ·) = z.1 → ∀ β f x g y, ∫ l, thetaOnRealData W₁ (V'.sum W₁) γ (γ * β) (boxProd homSigns_sum_target f (namedVector W₁ W₁ (stdColDatum 𝔠.χ 1) 𝔠.readsAt)) (fromRows x 0) (g, .sum (y, l)) (realPairWeil (card n / 2 - μ ·) 0 (1, (G.sum p).1 * h) (realSlice D (V'.sum W₁) (G.mat ((G.sum p).1 * h, 1)⁻¹ * fromRows (m₂ := n) B.1 0) v)) ∂W₁.quotMeasure = ρ h * l 𝔠 / (𝔠.ν.baseChange.1 (z.map (.inl ..)) * √(ideleAbs (z.map (.inl ..))) ^ card n) * thetaOnRealData W₁ V' γ β f x (g, y) (realSlice D V' B v')) (hz : (∀ x, realSlice D (V'.sum W₁) x v ≠ 0 → RepresentedBy t' (xᴴ * stdForm E (t' ⊕ᵥ s) * x)) ∨ t' = -1 ∧ ∃ i, s i = 1 ∧ 2 * negCount s ≤ card n) : StdExchange X (V'.sum W₁) V' μ σ' v v' fun 𝔠 ↦ ‖l 𝔠‖ ^ 2 / lValueProdInt 𝔠 (card n / 2) := by
  obtain ⟨R, hR, H⟩ := exists_integral_stages_eq_mul W₁.Γ volume volume volume _ G.isClosedEmbedding_sum (fun g ↦ ite (∃ l, U.blockSumOne l * g.2 ∈ Kf ..) (ρ g.1) 0) (by bound) ((h₁.prod_nhds (isOpen_Kf.mem_nhds (one_mem _))).mono fun _ ⟨_, _⟩ ↦ by rwa [ite_eq_left ⟨1, by simpa⟩])
  let a := (scaleIdele E • V'.x).det
  let κ : ℂ := vacuumFactor (isAdapted_homSource D (V'.sum W₁)) / vacuumFactor
    (isAdapted_homSource D V') * √(ideleAbs a) ^ card n
  use hv, hv', ‖R * κ‖⁻¹ ^ 2, fun 𝔠 ↦ ?_
  obtain ⟨r, ⟨_, N⟩, ε, _, P⟩ := 𝔠.readsAt, hn, (adaptedFrame 𝔠.readsAt D).exists_stdRowDatum_eq_stdDatum (χ := 𝔠.χ) σ'
  obtain ⟨r', L, _, _, h, K⟩ := r.star, (adaptedFrame r D).blocks_spec.1, exists_isEquivariantLift X
    (V'.sum W₁) V' 𝔠 σ' (D.card_eq ▸ by omega) hv hv' (R * (κ * ε * 𝔠.ν.baseChange.1 a * l 𝔠))
  obtain ⟨S', S, e⟩ := (stdColDatum_mem_schwartzBruhat 𝔠.χ L).transpose_mem_schwartzBruhat, K (stdColDatum_mem_schwartzBruhat _ L).1 (isPartner_stdRowDatum_stdColDatum _ L)
  refine ⟨_, by simp [*, D.card_eq, field]; clear * -; grind [lValueProdInt_pos], fun _ i ↦ sub_eq_zero.1 ((K (stdColDatum_mem_schwartzBruhat _ i).1 (isPartner_stdRowDatum_stdColDatum _ i)).2 ▸ h.apply_stdColDatum_eq_zero D D₁ V' (fun _ c z q g t ↦ .trans (by
    simpa [e] using! (centreCoeff_sub (r.isTargetBounded hv (stdRowDatum_mem ..)).isAutFunction_thetaIntegral (r'.isTargetBounded hv' S').isAutFunction_thetaIntegral _ 1).2 ..) (sub_eq_zero.2 ?_)) S σ' i)⟩
  obtain ⟨⟨⟨i, O⟩, Z⟩, ⟨⟨i', O'⟩, Z'⟩, ⟨Y, k, hk, ⟨⟩, u, ⟨⟩⟩ | ⟨d, T⟩⟩ := thetaTerm_stdDatum_spec _
    D (V'.sum W₁) r _ _ ε 1 (stdRowDatum_mem ..) (by simpa) hv (rankTwist_eq_mul_of_splitting D) c z
    q g, thetaTerm_stdDatum_spec _ D V' r' _ _ 1 (fromRows 1 0) S' (funext fun y ↦ if_congr forall_comm (by rw [← det_transpose]; simp [adaptedFrame, lCoord, stdForm]; congr with; simp; rfl) rfl) hv' (rankTwist_eq_mul_of_splitting D) c z q g, t
  specialize O (fromRows 1 0) (fromRows V'.x.2 0) (fromRows Y 0) (by simp [sum]) (by simp)
  obtain ⟨⟨v, I, H₂⟩, -, -, J⟩ := D.centreCoeff_eq_integral_stabilizer i (x₀ := fromRows 1 0) (by simp) (S := W₁.Γ.map (G.sum.comp (.inr ..))) fun _ ↦ .symm ((exists_congr fun γ ↦ and_congr_left' (.trans (by simp [entrywise]) (U.mem_range_sum rfl (g := γ).2 V'.isUnit_J).symm)).trans (by simp [Γ, sum_ratEmbed, -Subtype.exists])), D.centreCoeff_eq_integral_stabilizer i' (x₀ := 1) (by simp) (S := ⊥) (by simp [eq_comm])
  simp only [mul_one, conjTranspose_one, one_mul, quotMeasure_bot, Splitting.thetaTerm] at *
  erw [J, mul_assoc R, ← H _ (by fun_prop) v I _ fun ⟨h, l⟩ ↦ ?_, ← H₂]; simp; rfl
  split_ifs with hl
  obtain ⟨⟨⟨p, q⟩, hc⟩, ⟨l, m⟩, hl⟩ := hc 𝔠 h, hl; use ((p.1, l), q.1, m)
  simp_rw [← integral_const_mul]; congr with y
  let B := y⁻¹.toUnitary * Y
  let x := y.2⁻¹ * Y.map (.snd ..)
  conv_lhs => enter [2, l']; rw [show (_, _ * _) = ((_ : G ..), G.sum (y, l') * (_, 1)) * (1, 1, _)
    by simp [mul_assoc]; trivial, ← rep_apply_apply, pairWeil_stdRowDatum_eq_self σ' L ‹_›, O, show _ * Matrix.map _ _ = fromRows x 0 by simp [G.sum, U.sum, x], (by simp : IsIntMatrix .. ↔ IsIntMatrix (Ô E) x.1)]
  simp_rw [O' 1 _ Y rfl (by simp), show _ * Y.1.map snd = x by rfl, integral_const_mul]
  split_ifs with i
  have o : x.det ∈ _ := coe_idelesUnitOff_empty.ge ⟨i.det_mem, ((mul_mem_cancel_right hk).1 (mem_Kf (g := ⟨x * k, by simp [x, mul_assoc, mul_mem, u]⟩).2 (i.mul hk.isIntMatrix))).isIntMatrix_inv.det_mem⟩
  rw [(_ : namedVector .. = (ε * invOnUnits 𝔠.χ (evalPlaces _ x.det)) • _), (_ : namedVector .. = invOnUnits 𝔠.χ (evalPlaces _ (star x.det)) • _), rankTwist_eq_mul_of_splitting D]
  conv in (thetaOnRealData ..) _ => rw [thetaOnRealData, ← mul_one g, ← mk_mul_mk]; simp [↓map_mul, ← map_inv, pairWeil_integrated_right, -θ_apply]
  erw [integral_const_mul, hc B (B.det.map (.fst ..)) (funext (evalInf · |>.map_det _)).symm, ← mul_inv_eq_of_eq_mul (_ : B.det = .map _ _ * finIdeleIncl x.det)]
  simp [thetaOnRealData, HeckeChar.finPart, ↓← eq_of_div_eq_one (𝔠.invOnUnits_mul_div_star o), rankTwist, pairWeil, AutChar.spaceChar, (congr(𝔠.ν.1 ⟨_ * $(star_star _), _⟩) : 𝔠.ν.baseChange.1 (Unitary.toUnits _) = 𝔠.ν.1 (_ * _)), (Units.ext rfl : y.toUnitary.1.det = Unitary.toUnits y.det), ideleAbs_eq_one_of_mem_unitary, κ, N, B, G.mat, (ideleAbs_eq_prod_of_v_eq_one (mem_idelesUnitOff.1 o · id) : ideleAbs (finIdeleIncl x.det) = _)]
  field (disch := simp)
  ext : 2 <;> simp; exact ((RingHom.snd ..).map_det B.1).trans congr(det $Matrix.map_mul)
  on_goal 3 => rw [boxProd_name _ r.1 (Ψ := boxIndicator _ 𝔠.S) (hΨ' := r.isSchwartzBruhat (stdColDatum_mem_schwartzBruhat _ .one)) rfl]
  rw [name_boxIndicator r.1, projOn_vacElem, ← projOn_vacElem, ← name_boxIndicator r'.1]
  iterate 2 rw [smul_name, namedVector]; congr with; swap
  simp [r'.mem_iff, -RingHom.coe_comp]
  erw [← RingHom.map_det]; rfl
  simp [← r.mem_iff, stdColDatum, ← ite_and, mul_assoc]
  erw [← fromBlocks_toBlocks (fromCols _ _), det_fromBlocks_zero₂₁', ← (evalPlaces _).map_det x.1]
  exact if_ctx_congr and_comm (congrArg _ <| invOnUnits_mul (evalPlaces_mem_O _ i.det_mem) <| IsIntMatrix.det_mem ·.1) (by simp)
  ring
  use 1; conv_lhs => enter [2, y, 2, _]; rw [O, ite_eq_right fun i ↦ hl (let w := ((y.2⁻¹ * ⟨_, u⟩ :), (1 : U 1)); (witt_Ohat_of_orthonormal (congr($((l⁻¹ * U.blockSumOne w).2).toBlocks₁₁).trans (by simp [← fromBlocks_one'])) (by simp) (by simpa [w, G.sum, U.sum, ← fromCols_fromRows_eq_fromBlocks] using i.mul hk.isIntMatrix) (by simp [ite_mem])).elim fun k ⟨_, e⟩ ↦ ((U.mem_range_sum fromBlocks_one' (g := k * _).2 isUnit_one).2 e).elim fun m f ↦ ⟨(1, m) / w, by simpa [↓map_div, f, ← mul_assoc]⟩)]
  simp [↓zero_mul]
  erw [hz.elim (Z _ _ T) fun ⟨e, _, a, l⟩ ↦ centreCoeff_eq_zero_of_not_negative (.inr _) (by simp [N]; linarith [negCount_neg_add s, 𝔠.weight_pos ·]) a (by simp [e]) (rankTwist_eq_mul_of_splitting D) d (e ▸ T) i, Z' _ _ T fun _ _ ↦ (⟨_, gram_map_real _ ·⟩), mul_zero]
end
section
open Matrix NumberField MeasureTheory Complex Space Filter ContDiff Norms.Elementwise Finset Function Splitting Measure MixedModel GeneralLinearGroup ENNReal IsHermInvolution U MatMul
variable {E n a b m} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype a] [Fintype b] [Fintype m] {s r} {X : Space E m r} {W₁ : Space E n s} (D : X.Splitting W₁ b) [IsBaseAdapted D]
lemma exists_rapid_with_realSlice {t'} (V' : Space E a t') (τ : _ → ℝ) (c : ContDiff ℝ ∞ τ) {v} (hv : IsRapidDatum v) (k : HasCompactSupport τ) (h : 0 ≤ τ) y (o : τ y ≠ 0) : ∃ κ Λ, IsRapidDatum Λ ∧ realSlice D.symm V' 0 Λ = v ∧ ∀ x, (isAdapted_homSource D V').mixedModel.slice x Λ = (τ x • (κ : ℂ)) • realWeil 1 v := by
  peel 1 (ofReal_ne_zero.2 (c.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := realMeasure _) k h o).ne').isUnit.dvd
  refine (exists_section _ (c.smul_const _) k.smul_right contDiff_const hv).imp fun _ ↦ .imp_right fun l ↦ ⟨eq_of_integrated_zeroTerm_eq (isAdapted_homSource D.symm V') fun f ↦ ?_, l⟩
  erw [← zeroTerm_integrated, symm_homSource_zeroTerm_eq_integral, symm_homSource_zeroTerm_eq_integral, ← (integrated _ v).integral_comp_comm (by fun_prop), @isAddLeftInvariant_eq_smul _ _ _ _ _ _ _ _ volume _ (.domSMul (μ := vacuumMeasure) (.mk (star (adaptedHomBasis b V'))))]
  simp [integral_domSMul, star, -coe_units_inv]; simp +singlePass only [mixedTerm_integrated, isAdapted_homSource]
  simp [(adelicSum E 1).integral_eq_integral_prod, adelicSum, realCoord.eq_unfold, l]
  repeat rw [(congrArg _ (funext (by simp; tauto))).trans (integral_prod_smul ..)]
  erw [integral_mul_const, integral_ofReal, ← this]
lemma exists_contDiff_witt {J : Matrix m m ℂ} (hJ : Jᴴ = J) {x : Matrix m b ℂ} (d : (xᴴ * J * x).det ≠ 0) : ∃ k : _ → U J, ContDiff ℝ ∞ (fun y ↦ (k y).1.1) ∧ ∀ᶠ y in nhds x, ∃ c : Matrix b b ℂ, (k y).1.1 * x * c = y := by
  let w := (xᴴ * J * x)⁻¹ * xᴴ; let L a := (a * x * w - x * w * aᴴ) * J; let p y := 1 - (x - y) * w * J
  have ⟨_, i⟩ := (by fun_prop : ContDiff ℝ 1 L).differentiable_one 1
  open Norms.L2Operator in have hT := (HasFDerivAt.comp 1 (by simpa [L] using hasFDerivAt_exp_zero) i).fun_mul' ((hasFDerivAt_id 1).fun_sub i)
  have ⟨A, _, e⟩ := exists_contDiff_eventuallyEq (.to_localInverse (f' := 1) (by fun_prop) (hT.congr_fderiv (by simp [L]; apply sub_add_cancel)) (by simp))
  use (expU ⟨L <| A <| p ·, by simp [unitaryLie, L, w, *, conjTranspose_nonsing_inv]⟩), by fun_prop, .mono ((by fun_prop : Continuous p).tendsto' _ _ (by simp [L, p]) ((e.fun_comp _).trans (HasStrictFDerivAt.eventually_right_inverse _))) fun y e ↦ ⟨_, by simpa +zetaDelta [xᴴ.mul_assoc J x ▸ d] using congr($e * x)⟩
lemma exists_stdExchange_top {t t'} {W : Space E a t} (D₁ : W₁.Splitting W Unit) [IsBaseAdapted D₁] (V' : Space E b t') σ' (hn : 2 ∣ Fintype.card n) μ {v v₁ : PairFock ..} (hv : IsRapidDatum v) (r₁ : IsRapidDatum v₁) : ∃ x x', realSlice D.symm V' 0 x' = v ∧ StdExchange X (V'.sum W₁) V' μ σ' x x' (equalRankThetaRatio W₁ · v₁) := by
  obtain ⟨⟨j, hj⟩, d⟩ := id hn, IsHermInvolution.det_ne_zero (signMatrix t')
  let M := Int.toNat ∘ μ; let J := signMatrix (t' ⊕ᵥ s); let x₀ := @fromRows ℂ b n b 1 0
  have g₁ : x₀ᴴ * J * x₀ = signMatrix t' := by simp [x₀, J, ← signMatrix_sum]
  obtain ⟨⟨γ, _, eg⟩, k, _, N⟩ := exists_contDiff_eventuallyEq (f := (·⁻¹)) (x := signMatrix t') (by simp [Matrix.inv_def, funext₂ (adjugate_apply _), det_apply, updateRow_apply, prod_ite] at *; fun_prop), exists_contDiff_witt isHermitian (g₁ ▸ d)
  set S := (k · |>.1.1) with ← hk
  obtain ⟨σ, sσ, kσ, _, rσ, _⟩ := exists_contDiff_tsupport_subset (nhds_pi.le (eventually_pi fun _ : InfinitePlace E ↦ N.and ((by fun_prop : ContinuousAt (_ * _ * ·) _) (g₁ ▸ eg.and (ContinuousAt.eventually_ne (by fun_prop) d)))))
  let cuL {a} [Fintype a] : _ ≃L[ℝ] InfinitePlace E → Matrix a b ℂ := (LinearEquiv.curry .. ≪≫ₗ .piCongrRight fun v ↦ .curry ..).toContinuousLinearEquiv
  let z (x : type_of% x₀) := x * (γ (xᴴ * J * x) * (xᴴ * J * x₀))
  let w (y x : InfinitePlace E → type_of% x₀) v := (k (y v))⁻¹.1.1 * x v
  have P x (h : σ (z ∘ x) ≠ 0) v : ∃ c, S ((z ∘ x) v) * x₀ * c = x v ∧ cᴴ * signMatrix t' * c = (x v)ᴴ * J * x v := have ⟨⟨_, e⟩, _⟩ := sσ (subset_closure h) v
    (Matrix.mul_assoc ..).symm.trans (congr($e * _).trans (mul_nonsing_inv_cancel_right _ _ (by
    simp_all [z, gram_mul (x v), -conjTranspose_mul]))) ▸ ⟨_, rfl, by rw [gram_mul _ J, U.gram_invariant, g₁]⟩
  have ⟨κ, Λ', r, e', l'⟩ := exists_rapid_with_realSlice D V' ((fun x ↦ σ (x₀ * x ·) * ‖∏ w, (x w).det ^ (j + M w)‖ ^ 2) ∘ cuL) (.mul (by fun_prop) (.norm_sq ℂ (by simp [det_apply]; fun_prop))) hv ((kσ.image_auto (cuL.symm ∘ (x₀ᴴ * · ·))).closure_of_subset fun x h ↦ ⟨_, subset_closure (left_ne_zero_of_mul h), by simp [x₀]⟩) (fun _ ↦ mul_nonneg (rσ ⟨_, rfl⟩).1 (sq_nonneg _)) (cuL.symm 1) (by simp [*])
  let τ y x := ((σ y * σ (w y x)) • ((∏ v, (w y x v).toRows₁ᴴ.det ^ (M v * 2)) * κ)) • realPairWeil
    (j - M ·) 0 (1, k ∘ y) (realBoxProd (realSigns_comp_split homSigns_sum_target) v v₁)
  have ⟨Φ, R, l⟩ : ∃ Φ, IsRapidDatum Φ ∧ ∀ x, (isAdapted_homSource D (V'.sum W₁)).mixedModel.slice (cuL.symm x) Φ = τ (z ∘ x) x := by
    simp [τ, realPairWeil, ← smul_assoc, -real_smul, zpow_sub₀, division_def, inv_eq_conj, reindex_equiv cuL]
    exact exists_section _ (by
      simp [w, ↓U.coe_inv IsHermInvolution.mul_self, congrFun hk, det_apply, -real_smul]
      fun_prop) (((kσ.prod kσ).image_auto (cuL.symm ∘ fun (p, q) v ↦ S (p v) * q v)).closure_of_subset
      fun x h ↦ ⟨(z ∘ cuL x, _), closure_prod_eq.le (subset_closure (mul_ne_zero_iff.1 (left_ne_zero_of_smul h))), by simp [S]⟩) (contDiff_pi' fun _ ↦ contDiff_pi' (by
      simp_intro _ [pairHomInf, blockDiagonal_apply, pairHom, congrFun hk]; split_ifs <;> fun_prop))
      fun N ↦ mul_ne_top (mul_ne_top (isRapidDatum_vacVector N) (r₁ N)) (hv N) ∘ eq_top_mono (by
      (repeat refine (weightedNorm_integral_le _).trans (lintegral_weightedNorm_smul_le fun _ ↦ (weightedNorm_realHeisOp_le ..).trans ?_); rw [mul_comm]; gcongr) <;> simp [realCoordSum, enorm, pi_nnnorm_le_iff, nnnorm_le_pi_nnnorm])
  refine ⟨_, _, e', stdExchange_of_periods _ D D₁ _ _ hn (fun h ↦ (rσ ⟨z ∘ (h⁻¹ · |>.1.1 * x₀), rfl⟩).1) ((Continuous.tendsto (by fun_prop) 1).eventually_ne (by simp_all [comp_def, z, eg.eq_of_nhds])) R r (fun 𝔠 h ↦ ?_) (.inl fun x e w ↦ (P (atRealPlace x) (e <| (l (atRealPlace x)).trans <| by simp [τ, ·]) w).imp (by simp [↓← gram_map_real, J]))⟩
  lift μ to type_of% M using (𝔠.weight_pos · |>.le)
  generalize hy : z ∘ _ = y
  choose! c ec hc using hy ▸ P _
  choose! u hu using (exists_U_coe_eq <| hc · · |>.trans (g₁ ▸ U.gram_invariant ..))
  choose! q hq using fun o v ↦ (mem_range_sum (signMatrix_sum ..) (g := h v * k (y v) * U.sum (signMatrix_sum ..) (u v, 1)).2 isUnit).2 (by simpa [hu o, x₀, U.sum, ← fromCols_fromRows_eq_fromBlocks] using congr((h v).1.1 * $(ec o v)))
  use ((u, 1), q⁻¹, 1); intros
  let x v := (h⁻¹ v).1.1 * x₀ * (u⁻¹ v).1.1 * (‹GL b _›.map (delta% evalInf v)).1
  erw [l (atRealPlace _), l' (cuL.symm (atRealPlace _)), MonoidHom.prod_apply, show atRealPlace _ = x by ext; simp [x, x₀, ↓mul_apply, Prod.fst_sum, U.sum, blockGL], show τ _ x = τ y x by
    by_cases! i : ∀ y, σ (w y x) = 0; simp [τ, i]; congr 1
    simp_rw [← hy, comp_def, z, (by simpa only [w, U.gram_invariant] using sσ (subset_closure i.choose_spec) ·
      |>.2.1), x, gram_mul (_ * _), U.gram_invariant (J := J), g₁, eg.eq_of_nhds]
    simp [-val_map_apply]]
  by_cases o : σ y = 0; simp [τ, o]
  simp +zetaDelta [𝔠.hasWeight.baseChange_apply_inf, ideleAbs_eq_prod_of_v_eq_one, ← conj_mul', ← hu o, rep_apply_apply, ← norm_prod, thetaIntegral, ← map_mul, pow_mul, hj, pow_add, ← thetaLarge_eq_apply_one_of_even_rank D₁ 𝔠 hn r₁ ‹_›, congrFun ‹_ = _›, prod_pow, comp_def, -norm_pow, thetaOnRealData_boxProd_eq_mul, _root_.zpow_mul, div_pow, ↓← ec o, mul_pow, pow_right_comm _ 2, Pi.mul_def, mul_assoc, ← map_inv, ← mul_inv_eq_of_eq_mul (hq o _), ← Pi.one_def]
  field [prod_eq_zero_iff]
end
section
seal Finset.univ Finset.sum Finset.prod
noncomputable section
attribute [-simp] principalMinor_of_forall principalMinor_of_forall_not
open Matrix MeasureTheory Complex WeilData Space Splitting MvPolynomial Finset Fintype MatMul Heisenberg IsVacuum MixedModel Prod
attribute [local simp] div_mul_eq_mul_div slice_vac sum_prod_type fst_sum realVec Splitting.frameAt realMatrix negCount zpow_add₀ mul_div mul_pow prod_ne_zero_iff div_pow pairSign mul_eq_one_iff_eq_inv integral_smul_const blockDiagonal div_eq_iff
variable {E} [Field E] [CMType E] [WeilData E] {n n' r r'} [Fintype n] [Fintype n'] [Fintype r] [Fintype r'] (s : n → ℤˣ) (t : r → ℤˣ) (k) (m : _ → ℕ) (c) (F : Matrix n r (𝔸 E))
abbrev posCoordMatrix u := atRealPlace (vecToMat (realVec (posProj (realSigns E (homSigns s t)) *ᵥ u)) * F)
def detVectorFn u := c * realVac u * star (∏ w, let M := posCoordMatrix s t F u w; principalMinor M (t · = 1) ^ m w * principalMinor M (t · = -1) ^ (m w + 2 * k))
variable {s t k m} {s' t'} {W : Space E n s} {W' : Space E n' s'} {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X] {D : W.Splitting W' r}
def detVectors k m := {v : PairFock E s t | IsRapidDatum v ∧ ∃ c F, ∀ u, v u = detVectorFn s t k m c F u}
omit [WeilData E] in
lemma frameAt_real_unitary {t} (h : D.IsAdapted 1 t) w : let P := atRealPlace (D.frameAt 1 t) w; (Pᴴ * P = 1 ∧ P * Pᴴ = 1) ∧ signMatrix s * P = P * fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s') := by
  intro P; have o := (mul_eq_one_comm_of_card_eq _ _ _ (by simp +arith [D.card_eq])).1 (h.1 w)
  erw [h.1, o, ← Matrix.one_mul (_ * P), ← o, P.mul_assoc, ← Pᴴ.mul_assoc, gram_map_real]; simp [↓gram_frameAt, stdForm, signMatrix]
omit [Fintype n] in
lemma posProj_eq : posProj s = (2⁻¹ : ℂ) • (1 + signMatrix s) := by rw [signMatrix_eq_posProj_sub]; module
lemma PositivePart.exists_slice_eq {t} (h : D.IsAdapted 1 t) a u : ∃ U, posProj (realSigns E s) *ᵥ U = h.mixedModel.L *ᵥ -a + h.mixedModel.I *ᵥ posProj (realSigns E s') *ᵥ u + h.mixedModel.K *ᵥ -a ∧ ∀ P, let v := polyVector _ (rename (@Subtype.val _ (realSigns E s · = 1)) P); h.mixedModel.slice a v u = v U := by
  let J a z b := h.mixedModel.L *ᵥ a + h.mixedModel.I *ᵥ z + h.mixedModel.K *ᵥ b
  have q a z b : posProj (realSigns E s) *ᵥ J a z b = J (midpoint ℂ a b) (posProj (realSigns E s') *ᵥ z) (midpoint ℂ a b) := by
    ext ⟨w, l⟩; have := congr(($((frameAt_real_unitary h w).2) *ᵥ (vecToMat a w ⊕ᵥ vecToMat b w ⊕ᵥ vecToMat z w)) l)
    simp [J, posProj_eq, midpoint_eq_smul_add, signMatrix, ↓mulVec_add, IsAdapted.mixedModel, mulVec, dotProduct, vecToMat] at *; grind
  have n a u c z : star (J a u a) ⬝ᵥ J c z c = 2 * star a ⬝ᵥ c + star u ⬝ᵥ z := by
    rw [(?_ : J = fun a z b ↦ realMatrix (D.frameAt 1 t) *ᵥ fun (w, i) ↦ (vecToMat a w ⊕ᵥ vecToMat b w ⊕ᵥ vecToMat z w) i), star_mulVec_dotProduct, mulVec_mulVec, realMatrix_orthonormal _ h] <;> simp [entrywise, vecToMat, J, IsAdapted.mixedModel, funext_iff] <;> grind
  have ⟨_, _, _, e⟩ := h.mixedModel.exists_decomp; have' he : _ ∘ Equiv.sumCompl (realSigns E s · = 1) = _ := Sum.comp_elim ..
  use J (-a) u (-a), by simp [q, J], fun P ↦ sub_eq_zero.1 (.trans (by simp [← polyVector_one, realBoxProd_polyVector]; rfl) congr($((hom_ext fun y ↦ ?_ : (modelEval u ∘L h.mixedModel.slice a - modelEval _) ∘L (realBoxProd he).flip vacVector = 0)) P))
  simp [realBoxProd, OrthogonalSum.tmul, Rep.left]; erw [(realCoordSum he).tmul_vacElem, (by ext; simp_all [realCoordSum, posProj] : (realCoordSum he).equiv (y, 0) = posProj (realSigns E s) *ᵥ (realCoordSum he).equiv (y, 0)), ← e ((realCoordSum _).equiv _), q, slice_realHeisOp]
  simp [*, realHeis.eq_1, realVac, ← exp_add, signMatrix_eq_posProj_sub, ↓signMatrix_one]; grind
lemma surjOn_cone_integral_detVectors β z (hz : 1 ≤ z) (hn : card n' = 2 * (k + negCount s')) : (detVectors k m).SurjOn (∫ p, coneIntegrand A X (k + m ·) β z · p ∂.prod .haar .haar) (detVectors k m) := fun v ⟨_, c, F, e⟩ ↦ (tsum_lineTerm A X β).2.choose_spec.choose_spec.elim fun _ ⟨hy, l⟩ ↦ by
  let G := ((-(scaleIdele E).1.1⁻¹, 0) : 𝔸 E) • (A.kAdelic * X.kAdelicᴴ + A.lAdelic * X.lAdelicᴴ) + A.iAdelic * F * X.iAdelicᴴ
  let d w σ := det (of fun l i : {i // t' i = σ} ↦ ∑ j, C (star ((scaleIdele E * G j l).1 w)) * if h : _ = 1 then .X (⟨(w, i, j), h⟩ : {c // realSigns E (homSigns s' t') c = 1}) else 0)
  let R x : PairFock E s' t' := polyVector _ (rename (↑) (C x * ∏ w, d w 1 ^ m w * d w (-1) ^ (m w + 2 * k)))
  have K x g (h : ∀ w, g w ∈ blockDiagAlg t') u : realPairWeil (card n' / 2 - (k + m ·) ·) 0 (1, g) (R x) u = detVectorFn s' t' k m x G u := by
    erw [realPairWeil_polyVector _ _ (by simp) h, IsVacuum.smul_apply, polyVector_apply, aeval_bind₁]; set f := fun _ : _ × _ ↦ _
    simp [detVectorFn, pow_add, hn, zpow_sub₀, two_mul k, (by simpa [hn, two_mul, ← add_assoc] using negCount_neg_add s' :), fun w σ ↦ show eval f (rename (↑) (d w σ)) = principalMinor (posCoordMatrix s' t' G u w)ᴴ (t' · = σ) * principalMinor (g w) (t' · = σ) by
      rw [← principalMinor_mul (by clear * - h; grind [mem_blockDiagAlg])]
      simp [f, principalMinor, eval_rename, RingHom.map_det, d]; congr!; ext
      simp +contextual [posProj, mul_apply, vecToMat, toSquareBlockProp, apply_dite (eval _), sum_mul, holCoord_eq, @sum_comm n', mul_sum, ite_sum_zero, -sum_ite_irrel]
      clear * - h; grind [mem_blockDiagAlg]]; ring
  have H x := by simpa using K x 1
  have Φ q : ∃ φ : ℝ, ∀ d : ℝ, coneIntegrand A X (k + m ·) β z (R (d * c)) q = φ.exp • d • v := ?_
  choose φ Φ using Φ
  use R ((∫ q, (φ q).exp ∂.prod .haar .haar)⁻¹ * c), ⟨(weightedNorm_polyVector_ne_top · _), _, _, H _⟩
  by_cases v = 0 <;> simp [↓Φ, *, fun h ↦ (integral_exp_pos ((integrable_smul_const h).1 (funext (Φ · 1) ▸ (integrable_coneIntegrand _ _ _ _ hz (weightedNorm_polyVector_ne_top · _)).1))).ne']
  choose y a₁ a₃ using PositivePart.exists_slice_eq hy _
  use -∑ w, ‖q.2.1 w‖ ^ 2 + .log (ideleAbs (q.2.map (.inl ..)) ^ z * ∏ w, normSq (q.2.1 w) ^ (k + m w)); intro; ext u
  erw [Real.exp_add, Real.exp_log (by simp [Real.rpow_pos_of_pos, prod_pos]), coneIntegrand, ext (K _ _ (mem_maxCompactU.1 <| q.1.2.1 · ⟨⟩) · |>.trans (H ..).symm), lineTermReal, IsVacuum.smul_apply, a₃, H]
  have a w σ : principalMinor (posCoordMatrix s' t' G (y u) w) (t' · = σ) = q.2.1 w * principalMinor (posCoordMatrix s t F u w) (t · = σ) := ?_
  simp [*, ← (by simpa [star_dot_self_eq_sum] using a₃ u 1 :), ← Complex.coe_smul, detVectorFn, pow_add, ← conj_mul', normSq_eq_conj_mul_self, _root_.zpow_mul, prod_pow, pow_right_comm _ 2, prod_eq_zero_iff]; ring
  have := frameAt_real_unitary (by simp [IsAdapted, IsBaseAdapted.isOrthoIntegral] : X.IsAdapted 1 1) w; extract_lets P at this
  rw [(?_ : posCoordMatrix _ _ G _ w = P * (scalar (Unit ⊕ Unit) (q.2.1 w)).fromBlocks 0 0 (posCoordMatrix s t F u w) * Pᴴ)]
  fin_cases σ <;> simp [↓principalMinor_sign_eq_det, principalMinor_eq_det, ← posProj.eq_1, posProj_eq, mul_apply, sub_eq_add_neg, this, ← (signMatrix _).mul_assoc P, ← this.1.elim det_conj_of_mul_eq_one, ↓(det_classical _).symm.trans (det_fin_two _), ← fromBlocks_one', ← Pᴴ.mul_assoc P, fromBlocks_add, fromBlocks_neg, ← det_submatrix_equiv_self (.ofBijective ![.inl (), Sum.inr ()] (by open Calc in decide +kernel)), fromBlocks_smul] <;> ring_nf <;> simp
  rw [Splitting.frameAt, inv_one, _root_.G.mat_one, Matrix.one_mul, fromCols_ext_iff] at l
  simp_rw [posCoordMatrix, a₁, map_add, IsAdapted.mixedModel, realVec_realMatrix_mulVec, l.2, fromCols_inj l.1]
  cases β <;> simp [kronecker_mulVec_eq_matToVec, ← Pi.zero_def, ← matToVec_add, Function.comp_def, mk_zero_zero, G] <;> ext <;> simp [↓← (vecToMat _).mul_assoc, mul_apply, P, vecToMat, -Matrix.mul_assoc, field] <;> ring
end
end
section
section
open Matrix Fintype Space Splitting MeasureTheory MatMul MixedModel
variable {E} [Field E] [CMType E] [WeilData E] {n n' r r' p b} [Fintype n] [Fintype n'] [Fintype r] [Fintype r'] [Fintype p] [Fintype b] {s s' t t' u} {W : Space E n s} {W' : Space E n' s'} (U : Space E b u) (V' : Space E r' t') (A : W'.Splitting W p) (B : W.Splitting V' r) [IsBaseAdapted A]
attribute [-simp] θ_apply Matrix.smul_apply card_unique card_punit
variable (p W) in
lemma exists_isBaseAdapted t (h : card r = card n + 2 * card p) (h' : negCount t = card p + negCount s) : ∃ (W' : Space E r t) (A : W'.Splitting W p), IsBaseAdapted A := (exists_equiv_of_card_neg (by simpa +arith) (by simpa)).rec fun ε hε ↦ ⟨(hypSum p W).reindex ε.symm hε, splittingOfGram (submatrix 1 ε id) (by simp) h, ⟨.of_eq_submatrix_mul .one ε.symm (IsBaseAdapted.isOrthoIntegral (D := removePlanes p W)) (by simp [entrywise, lAdelic, kAdelic, iAdelic, Space.ratMap, removePlanes, splittingOfGram, Space.reindex, reindex_equiv ε.symm])⟩⟩
lemma slice_zero_congr {B : W'.Splitting W r} {e} (k : B.k = A.k.submatrix id e ∧ B.i = A.i) [IsBaseAdapted B] : realSlice A U 0 = realSlice B U 0 := by simp [realSlice, ← Pi.zero_def, IsAdapted.mixedModel, A.zeroTerm_homSource_congr U (k.1 ▸ congr(submatrix $A.gram_kk e _)) k.2]
lemma slice_zero_comp [IsBaseAdapted B] y : realSlice (A.comp B) U 0 y = realSlice B U 0
  (realSlice A U 0 y) := eq_of_integrated_zeroTerm_eq (isAdapted_homSource ..) fun _ ↦ (zeroTerm_integrated ..).symm.trans (by rw [zeroTerm_homSource_comp, zeroTerm_homSource_comp, zeroTerm_integrated, zeroTerm_integrated, ← (by simpa [slice_vac] using zeroTerm_integrated (isAdapted_homSource A U) vacVector :)]; rfl)
lemma exists_stdExchange_removing_planes [Nonempty p] μ {ℓ} k j (V : Space E r t) σ σ'
  (hs : negCount t' = card p + negCount t) (hn : 2 ∣ card n) : ∃ f : _ → _, (∀ x y, StdExchange W' V' U μ σ' x y ℓ → StdExchange W V U μ σ (f x) (realSlice A U 0 y) ℓ) ∧ (card n = 2 * (k + negCount s) → card n' = 2 * (k + negCount s') → μ = ((k : ℤ) + j ·) → (detVectors k j).SurjOn f (detVectors k j)) := by
  induction' hd : card p using Nat.strongRec with d ih generalizing p n n' r r'
  obtain ⟨e, e', l, _ | _ | d⟩ := card_congr σ, card_congr σ', A.card_eq, d
  simp at hd
  obtain ⟨⟨A, _, hk⟩, V₁, X, _⟩ := exists_isBaseAdapted_reindex A (equivOfCardEq (hd ▸ card_unit)), exists_isBaseAdapted Unit V t' (by grind [card_unit, card_sum]) (by bound [card_unit])
  obtain ⟨β, z, h, C, H⟩ := exists_constant_term_thetaLarge A X σ' σ hn μ
  refine ⟨_, fun _ y ⟨_, k, D, R⟩ ↦ ⟨by simp [integrable_coneIntegrand, *], isRapidDatum_slice _ _ k, D * C / ‖(vacuumFactor (isAdapted_homSource A U)).1‖ ^ 2, fun 𝔠 ↦ ?_⟩, fun _ m a ↦ a ▸ surjOn_cone_integral_detVectors A X β z h m⟩
  obtain ⟨⟨γ, o, _, H⟩, ⟨a, M⟩, c, hc, R⟩ := H 𝔠, thetaLarge_move W' W' V₁ V' 1 1 (by simp) 𝔠, R 𝔠
  use c * vacuumFactor (isAdapted_homSource A U) * a / γ, by simp [field]; grind [card_sum], fun z hz ↦ funext fun g ↦ mul_left_cancel₀ o ?_
  have i := hz.mul (adaptedFrame 𝔠.readsAt A).blocks_spec.2.1
  rw [← H (u := 1)] <;> simp [thetaSmall, rankTwist_eq_mul_of_splitting A, field, slice_zero_congr _ _ hk, *]
  clear * - hz k i
  obtain ⟨r, m', m⟩ := 𝔠.readsAt.star, (stdColDatum_mem_schwartzBruhat 𝔠.χ i).transpose_mem_schwartzBruhat, (stdColDatum_mem_schwartzBruhat 𝔠.χ hz).transpose_mem_schwartzBruhat
  have K x := r.sourceTerm_localDatum A U (G := (invOnUnits _ <| det <| z * ·.toCols₂ᵀ)) m' ((WeilData.scaleIdele E)⁻¹ • x) y
    fun _ _ ↦ if_congr forall_comm (by simp [adaptedFrame, iCoord, stdForm]; congr; aesop) rfl
  erw [integral_thetaIntegral_lineRadical A _ _ (r.isTargetBounded k m'), ← integral_const_mul, ← integral_const_mul]
  congr with h; erw [tsum_eq_single 0 fun x o ↦ by_contra fun H ↦ ?_, constTermAt_zero]
  swap; obtain ⟨_, _, _, X, _⟩ := exists_splitting U (.of_ne_zero o) (ite_ne_right_iff.1 H).1
  rcases (constTermAt_smul_k A X one_ne_zero (f := ·)), (name_eq_zero_of_invariant r.1 (hΨ := r.isSchwartzBruhat m) (h⁻¹.mat * X.kAdelic) 1 (ℓ := θ _ ∘L (X.homTarget W).zeroTerm ∘L pairWeil _ _ · · (g, h)) (fun z f ↦ by simp [← zeroTerm_rho_kAdelic (matToVec (vecToMat z * stdForm E s * g⁻¹.mat * W.dualFrame.2)) (pairWeil _ _ _ _ _ f), varrho_pairWeil, homTarget_kAdelic, kronecker_mulVec_eq_matToVec, G.mat]) fun _ ↦ (U.coordMatrix_mul_ne_zero (by aesop) 1 <| m.2.2 ·))
  iterate 2 simp_all [lineTerm, integrated_name, stdColDatum, IsIntMatrix, @forall_comm n, mem_O_locProd, A.sourceTerm_levi, pairTheta, field]
  choose B _ k using exists_isBaseAdapted_stage A (finSumFinEquiv.trans (equivFinOfCardEq hd).symm)
  refine' let Y := hypSum (Fin 1) V; (card_eq.1 _).elim fun τ ↦ (ih _ _ V' B Y τ σ' _ _ rfl).elim
    fun f a ↦ (ih _ _ Y (removePlanes _ W) V σ τ _ _ rfl).elim fun g c ↦ ⟨_, _, fun _ _ _ ↦ .comp (c.2 ..) (a.2 ..)⟩ <;> simp +contextual [slice_zero_congr U A k, slice_zero_comp, *] at e ⊢ <;> omega
end
open Matrix MeasureTheory Fintype Std Weil ExistsContDiffBumpBase
lemma exchange_of_partners {E} [Field E] [CMType E] [WeilData E] {n m r p b} [Fintype n] [Fintype m]
    [Fintype r] [Fintype p] [Fintype b] {s s' t u} {W : Space E n s} {X : Space E m s'} (U : Space E b u) μ [Nonempty p] (A : (hypSum Unit X).Splitting W p) [IsBaseAdapted A] (V : Space E r t) (σ : b ⊕ r ≃ n) {z y} (r₁ : IsRapidDatum z) (hy : IsRapidDatum y) (hs : 1 + negCount s' = card p + negCount t + negCount u := by simp) (hn : 2 ∣ card n := by simp) : ∃ C v, IsRapidDatum v ∧ ∀ 𝔠 :
  SplitTameChar E μ, let γ := rankTwist 𝔠.ν⁻¹ n; ∃ c, C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (card r - card n / 2) * equalRankThetaRatio (hypSum Unit X) 𝔠 z ∧ ∀ Φ Ψ, IsLocallyConstant Ψ → IsPartner
    SemilocalField.O σ 𝔠.χ Φ Ψ → ∀ g, thetaIntegral W V γ 1 (localDatum W V v Φ 𝔠.readsAt) g = c * ∫ h, pairTheta U W γ γ (localDatum U W y Ψ 𝔠.readsAt) (h, g) ∂U.quotMeasure := by
  let f := flipCoords (E := E) (s := s) star_normNegOne_mul_self (t := u) rfl
  have : IsRapidDatum
    (f.realMap y) := by simpa [IsRapidDatum, weightedNorm, enorm, fun x ↦ (eq_of_forall_ge_iff (by
    simp [f, flipCoords, starCoordEquiv, ↓pi_nnnorm_le_iff, nnnorm]; tauto) : ‖f.realEquiv
    x‖₊ = ‖x‖₊), ← (Heisenberg.IsVacuum.measurePreserving_equiv (realHeis 1) (realHeis 1)
    f.vac_realEquiv).lintegral_comp_emb f.realEquiv.measurableEmbedding] using! hy
  obtain ⟨_, w, a, e, -⟩ := exists_rapid_with_realSlice A.symm _ _ (u_smooth _) this
    (u_compact_support _) u_nonneg 0 ((u_support _).ge (by simp))
  obtain ⟨⟨x, u, rfl, H⟩, _, k⟩ := exists_stdExchange_top (removePlanes ..) (removePlanes _ X)
    (flipSpace U) (.symm (.sumAssoc ..)) (by grind [A.card_eq]) μ a r₁, id hn
  choose rv _ C c _ K using e ▸ slice_zero_comp _ _ (removePlanes ..).symm A u ▸ (exists_stdExchange_removing_planes _ _ _ μ 0 0 V σ _ (by simp; grind [negCount_neg_add]) hn).choose_spec.1 _ _ H
  refine ⟨C, _, rv, fun 𝔠 ↦ ?_⟩
  let t := normNegOne.map ((evalPlaces 𝔠.S).restrict _ _ evalPlaces_mem_O).1
  obtain ⟨⟨d, _, H⟩, r, _, 𝒟, h, R⟩ := exists_pairTheta_flip star_normNegOne_mul_self rfl U W
    (flipSpace U) 1 (by simp [flipSpace, ← ext_iff]) _, 𝔠.readsAt, exists_isEquivariantLift W V (flipSpace U) 𝔠 σ hn rv this (c 𝔠)
  use c 𝔠 * 𝔠.χ t ^ card b * d, by simp [*, TameLocalChar.norm_eq_one, isIntegralUnit_iff_isUnit.2], fun Φ Ψ m P g ↦ ?_
  rw [mul_assoc, ← integral_const_mul, ← funext fun l ↦ H _ _ l _ l.neg (by simp)]
  have : localDatum W (flipSpace U) (f.realMap y) (Ψ ·ᵀ) r.star = 𝔠.χ t ^ card b • f.map (localDatum U W y Ψ r) := by
    rw [map_integrated, map_name _ _ _ r.1 r.star.1 (hΨ := r.isSchwartzBruhat (h.le_schwartzBruhat (R m P).1)), ← map_smul, Space.smul_name]
    congr!; dsimp; rw [← P.right_mul _ ⟨.scalar _ t, rfl⟩, mul_comm]; congr
    all_goals (try unfold f flipCoords starCoordEquiv); simp [vecToMat, funext_iff, mul_left_comm, star_idem, starRingEnd_apply, Set.conjClosure, ← ext_iff, field, t]
  convert congr((rankTwist 𝔠.ν⁻¹ n).1 g.det * $(sub_eq_zero.1 ((R m P).2.symm.trans ((isPrimitiveMatrix_firstCols σ (one_mem _)).rec fun j ⟨s, i, e⟩ ↦ (partner_mem_of_stdColDatum h.comp_mul_mem_ker (inf_le_left.trans h.le_schwartzBruhat) m P ((R (stdColDatum_mem_schwartzBruhat _ i).1 (isPartner_stdRowDatum_stdColDatum σ i)).imp_right (by simp [*])) j i e 1 (by simp) _).2))) g) using 1 <;> simp [thetaIntegral, isForm_neg_iff_and_integral_neg U (flipSpace U), pairTheta, pairWeil, rankTwist, ↓this, *, ← integral_const_mul]
  repeat congr with <;> field
open Space Equiv Subsingleton ENNReal MixedModel Heisenberg Sum OrthogonalSum IsIntMatrix Finset
variable {E n} [Field E] [CMType E] [WeilData E] [Fintype n] {s} (W : Space E n s) (μ : _ → ℤ)
lemma name_vacElem_of_isEmpty [IsEmpty n] (𝔠 : SplitTameChar E μ) Φ : W.name 𝔠.S Φ W.vacElem = Φ 0 • W.vacElem := by
  nth_rw 1 [(funext (by simp [eq_zero ·]) : Φ = Φ 0 • boxIndicator _ 𝔠.S)]; simp [name_boxIndicator 𝔠.readsAt.1]
attribute [local simp] name_vacElem_of_isEmpty localDatum stdColDatum pairTheta pairWeil_apply funext_iff vacElem_apply_eq_prod_lineTheta measureReal_univ_ne_zero IsIntMatrix.one lValueProdInt_pos invOnUnits thetaIntegral dvd_add
attribute [-simp] measure_univ_of_isAddLeftInvariant probReal_univ
lemma exists_equalRankThetaRatio_value k (hk : card n = 2 * k + 2 * negCount s) (hm : ∀ v, k ≤ μ v) : ∃ v, IsRapidDatum v ∧ ∃ C ≠ 0, ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hypSum Unit W) 𝔠 v = C := by
  let J := stdSpace E (Fin (2 * k))
  obtain ⟨X, A, _⟩ := exists_isBaseAdapted (Fin _) J s (by simpa) (by simp)
  let Y := hypSum Unit X
  let P := removePlanes Unit X
  let Q := P.comp A
  let Z := stdSpace E Empty
  obtain ⟨o, h₀ | ⟨_, v₁, r₁, h⟩⟩ := (J.isAutomorphic_const 1).mem_rapidFunctions, em' (∃ 𝔠 v, IsRapidDatum v ∧ equalRankThetaRatio Y 𝔠 v ≠ 0)
  simp [equalRankThetaRatio, ne_of_gt, -thetaIntegral] at h₀
  refine (exists_stdExchange_removing_planes J.neg _ ((removePlanes _ Y).symm.comp Q) μ k (μ · - k |>.toNat) Z (sumEmpty ..) (sumAssoc ..).symm ?_ ?_).rec fun f ⟨K, a⟩ ↦ (a ?_ ?_ ?_ ⟨isRapidDatum_vacVector, 1, 0, ?_⟩).rec fun v ⟨⟨r, _⟩, a⟩ ↦ (a ▸ K _ 0 <| stdExchange_of_periods _ (removePlanes _ Y) P _ 0 ?q zero_le_one ?_ r ?_ (fun 𝔠 _ ↦ ⟨1, by
    simp_intro .. [realSlice]; exact And.elim (fun i R ↦ .trans (by
      congr with
      rw [IsVacuum.map_eq_integral]
      convert! (θ _ ∘L (pairWeil ..) _ ∘L (integrated _).flip _).integral_comp_comm i
      rw [map_smul, map_smul]
      convert! congrArg _ (thetaOnRealData_boxProd_eq_mul ..)
      erw [← heisOp_tmul, tmul_vacElem]) ((thetaLarge_eq_apply_one_of_even_rank P _ ?q R _).trans
      (h₀ _ _ R))) (isRapidDatum_integral (by fun_prop) fun _ ↦ (eq_top_mono
      (lintegral_weightedNorm_smul_le fun y ↦ by grw [weightedNorm_smul, weightedNorm_realHeisOp_le, ← ofReal_norm, (thetaOnRealData ..).le_opNorm, Heisenberg.Rep.norm_map, (enorm_le_iff_norm_le.2 (pi_norm_comp_le y _) : ‖Prod.snd _‖ₑ ≤ _), mul_comm, mul_rotate])).mt
      (by simp [mul_eq_top, isRapidDatum_vacVector _, realPairWeil, weightedNorm_smul, isRapidDatum_slice _ _ r _, (eq_top_mono (weightedNorm_realWeil_le ..)).mt]))⟩) ?_).2.2.rec
    fun _ K ↦ ⟨_, isRapidDatum_vacVector, 1, ?_, fun 𝔠 ↦ by simpa [↓isIntegralUnit_iff_v_eq_one, univ_eq_empty, @eq_one (G ..), (id rfl : stdRowDatum (sumEmpty ..) _ 1 _ = stdColDatum _ 1 1)] using (K 𝔠).choose_spec.2 _ .one⟩ <;> simp +arith [IsRapidDatum, weightedNorm, detVectorFn, *]
  choose B y r b hb K using exchange_of_partners Z μ Q J (emptySum ..) r₁ isRapidDatum_vacVector
  choose C x _ c hc H using exchange_of_partners J μ Q Z (sumEmpty ..) r₁ r
  refine have F 𝔠 : equalRankThetaRatio Y 𝔠 v₁ ^ 2 = B * C * ‖integrated _ x (J.hom Z).vacElem 0‖ ^ 2 := ?_
    ⟨_, r₁, _, h, fun 𝔠 ↦ by rw [← sq_eq_sq₀, F, ← F 𝔠, equalRankThetaRatio, (thetaLarge_move _ _ _ Y _ _ (exists_eq_move ..).choose_spec.choose_spec.2.1 𝔠).choose_spec, thetaLarge_eq_apply_one_of_even_rank P] <;>
      simp [Y, *, equalRankThetaRatio, div_nonneg, _root_.le_of_lt, -thetaIntegral]⟩
  have T α φ := (pairThetaKer _ _ α α).integral_lift_eq_integral_descent (φ := φ) o o
  specialize K 𝔠 (stdColDatum _ 1) _ (.of_discrete _)
    (isPartner_stdRowDatum_stdColDatum _ (s := 0) nofun)
  have := congr(‖∫ g, $(H 𝔠 (fun _ ↦ stdColDatum _ 1 1) _ (stdColDatum_mem_schwartzBruhat _ .one).1 (isPartner_stdRowDatum_stdColDatum _ IsIntMatrix.one) g) ∂J.quotMeasure‖)
  simp [↓isIntegralUnit_iff_v_eq_one, ↓IsIntMatrix.one, IsIntMatrix, lift, field, univ_eq_empty, @eq_one (G ..), mul_right_comm _ _⁻¹] at T K this
  simp [*, field] at *
  rw [this]; clear * - hc hb; grind [lValueProdInt, lValueProdInt_pos]
end
section
open RingHom Fintype Modulus IsLinearMap
variable {E} [Field E] [CMType E] [WeilData E] {n a b} [Fintype n] [Fintype a] [Fintype b] {s t t'} (W : Space E n s) (V : Space E a t) (V' : Space E b t')
lemma exchange_theorem σ (hs : negCount s = negCount t + negCount t') {e} (he : card a = card b + 2 * e) (hn : 2 * negCount s + 2 ≤ card n) {μ : _ → ℤ} (hμ : ∀ v, card n ≤ 2 * μ v + 2 * negCount s) {v} (hv : IsRapidDatum v) : ∃ C x, IsRapidDatum x ∧ ∀ 𝔪 ν χ, IsTameFor 𝔪 ν μ χ → let γ := rankTwist ν⁻¹ n; ∃ c ≠ 0, ‖c‖ ^ 2 = C * lValueProd 𝔪.places ν e
    ∧ ∀ Φ Ψ, IsPartner ⊤ σ χ Φ Ψ → ∀ g, thetaIntegral W V γ 1 (modDatum W V 𝔪 Φ x) g = c * ∫ h, pairTheta V' W γ γ (modDatum _ W 𝔪 Ψ v) (h, g) ∂V'.quotMeasure := by
  have ⟨_, r₀, C₀, _⟩ := exists_equalRankThetaRatio_value W μ (card n / 2 - negCount s) ?_ ?_
  have ⟨C, x, r, H⟩ := exchange_of_partners V' μ (removePlanes _ W) V σ r₀ hv ?_ ?_
  use C₀ / C, x, r, fun 𝔪 ν χ ⟨h, ψ, a₁, a₂, a₃⟩ ↦ ?_
  have o := 𝔪.places.toFinite.coe_toFinset
  let 𝔠 := SplitTameChar.mk ν ψ a₁ _ (by simpa using! h) (by simpa using! 𝔪.not_le_star) (o ▸ a₂) ?_
  obtain ⟨⟨c, hc, H⟩, l, _, m, _, ρ, _, k, k'⟩ := H 𝔠, lValueProdInt_pos 𝔠 e, o ▸ 𝔠.readsAt
  simp +arith [*, ← card_congr σ, Int.add_mul_ediv_left] at hc
  simp [lValueProdInt, lValueProd.eq_1 _ _ 0] at *
  use c, by grind [norm_zero], by grind, fun Φ Ψ P ↦ ?_
  let π := ((evalPlaces 𝔠.S).restrict _ _ evalPlaces_mem_O).liftOfRightInverse
    (⟨_, by simpa [← k', *] using m <| ρ ·⟩) (Subtype.ext <| k ·) ⟨𝔪.reduction, fun x hx ↦ (𝔪.reduction_congr (y := 0) (congr($hx.1 ⟨·, o.ge ·⟩))).trans (map_zero _)⟩
  have e i u : modulusResidue _ (o.le i.2) (π u) = residueAt i u := (modulusResidue_reduction ..).trans congr(⟦⟨$(k u) i, _⟩⟧)
  have d {n n' : Type} [Fintype n] [Fintype n'] Φ : 𝔪.liftFn (Φ ∘ @vecToMat n n' _) = (liftIntegralFn π Φ <| vecToMat <| evalPlaces _ ∘ ·) := by ext; erw [liftFn_apply, mk'_apply]; congr! <;> simp [vecToMat, m, ← k']; rfl
  simpa [modDatum, 𝔠, *] using! H _ _ (by simpa [Function.comp_def, *] using (d Ψ ▸ isSchwartzBruhat_liftFn .. :).locally_constant.comp_continuous (f := (ρ ∘ matToVec ·)) (by
    fun_prop [matToVec])) (P.lift_of_reduction π ⟨fun u h ↦ isUnit_iff_residueAt_ne_zero.2
    (e · u ▸ (h.map _).ne_zero)⟩ (𝔪.reduction_surjective.forall.2 fun _ ↦ ⟨_, liftOfRightInverse_comp_apply ..⟩) (by
    simp_intro .. [← finprod_comp_equiv (Set.equivOfEq o), a₃, charOfTamePart, ← e, 𝔠.localChar_apply_of_isUnit, finprod_eq_prod_of_fintype]; rfl))
  repeat grind [card_sum, card_congr σ, card_unit]
end
