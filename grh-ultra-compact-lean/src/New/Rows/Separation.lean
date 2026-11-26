import New.Weil.FockCoeffDecay
import Lib.DiscreteSeries.Holomorphic.NearMaximum
import New.Rows.Carrier
import New.Exchange.GridModuli
import Lib.Weil.Fock.ReproducingFormula
import New.Exchange.AlgebraicPartConjugates
import New.Filling.DegreeBounds
import New.Rows.MemberOrthogonality
import New.Selmer.HeckeStableSubspaces
section
open MeasureTheory Matrix Norms.L2Operator Finset Fintype AddCircle NumberField
variable {E n} [Field E] [NumberField E] [Fintype n] [Nonempty n] {s m} {B : ℝ} (hn : numInfPlaces E * (2 * card n ^ 3) ≤ m) (hm : m ≤ B) (hB : 10 ^ 13 ≤ B) {o} {k w : InfinitePlace E → _} (ho : @IsPosFirstOrder n s o) (hu : ∀ τ, IsKDominant s o (w τ)) (hd : ∀ τ, IsKDominant s o (k τ)) (hw : ∀ τ, HasHolGap s (w τ) (300 * m)) (hk : ∀ τ, HasHolGap s (k τ) (300 * m)) (hk' : ∀ τ i, |↑(k τ i)| ≤ B)
attribute [fun_prop] IsHolOfWeight IsHolOfWeight.continuous
attribute [local simp] maxOpNorm abs_of_pos Measure.real
@[bound] lemma o9 (h : GInf E s) : 1 ≤ maxOpNorm h := (norm_le_pi_norm _ Classical.ofNonempty).trans' (U.one_le_norm _)
include hn hm hB ho hu hd hw hk hk'
private lemma sp_j1 : 0 < ∫ h, ‖holMinorsPi s k h‖ ^ 2 ∧ ∀ A, Continuous A → ∀ᵉ (C)
  (N ≤ 6 * m), (∀ h, ‖A h‖ ≤ C * maxOpNorm h ^ N) → Integrable (A * holMinorsPi s w) ∧ ‖∫ h, A h * holMinorsPi s w h‖ ≤ C * B ^ (7 * m) * ∫ h, ‖holMinorsPi s k h‖ ^ 2 := by
  obtain ⟨_, _, q, _⟩ := @card_pos n _ _, le_of_mul_le_of_one_le_right hn card_pos, (card n).pow_le_pow_right card_pos (2).le_succ, (card n).le_mul_self
  let c := 2 * card n ^ 3 * 5; choose b e using
    (dsCoeff_eq_holMinors ho (8 * m) (300 * m) · · · (by lia))
  choose i t using fun τ ↦ integral_tail_le (hg := b _ (hd τ) (hk τ)) (L := 2 * ⌊B⌋₊ + card n)
    (fun a ↦ by grw [Pi.add_apply, abs_add_le, abs_twoRho_le, ← Nat.le_floor (n := (k τ a).natAbs)]
    <;> simp [*]) c (by lia)
  obtain ⟨_, P⟩ := (isHolOfWeight_holMinorsPi ho hu).continuous, univ.prod_pos fun τ _ ↦ formalDegree_pos (b _ (hd τ) (hk τ))
  refine have I := by simp [holMinorsPi, formalDegree, prod_pow, ← integral_fintype_prod_volume_eq_prod, *]
    ⟨(inv_pos.2 P).trans_eq I, fun A a C N hN H ↦ have := by simpa using (norm_nonneg _).trans (H 1)
      have j := (Integrable.fintype_prod i).const_mul (C * 2 ^ N * ∫ h, ‖holMinorsPi s k h‖ ^ 2)
      (imp_and.2 ⟨j.mono' (by fun_prop), (norm_integral_le_of_norm_le j · |>.trans ?_)⟩) (.of_forall fun h ↦ (IsGreatest.pi_norm (h · |>.1.1)).1.elim fun a z ↦ (norm_mul_le ..).trans ?_)⟩
  grw [integral_const_mul, (integral_fintype_prod_eq_prod _).trans_le (prod_le_prod₀ (by
    intros; rw [formalDegree]; positivity) fun τ _ ↦ t τ), mul_right_comm, mul_assoc C, prod_const, q, pow_mul' 2, le_self_pow₀ (a := 8), ← mul_pow, ← mul_pow, ← pow_mul', card_univ, hn, hN, pow_mul, ← mul_pow, pow_mul B, (?_ : _ + 1 ≤ 5 * B)] <;> try bound
  gcongr; field; bound
  rify at *; grind [Nat.floor_le]
  grw [H, holMinorsPi, norm_prod, fun τ ↦ (e _ (hu τ) (hw τ) _ ▸ norm_dsCoeff_le_pow (by tauto)
    (c := c + ite (τ = a) N 0) (by rify at *; grind) _ :)]
  simp [pow_add, ← z, div_pow, field, -mul_ite, ← I]
lemma isolation [IsCMField E]
    {F z C ε} {K₀ : _ → ℂ} (hF : Continuous F) (c : IsAdelicHol o k F) (ha : F z ≠ 0)
    (h2 : ∀ x, ‖F x‖ ≤ 2 * ‖F z‖) (g : ∀ h, ‖K₀ h‖ ≤ C) (H : Integrable (holMinorsPi s w) → ∀ x, ‖F z‖ ≤ ‖F x‖ → ∃ K, IsHolOfWeight s o (k - w) K ∧ (∀ h, ‖K h - K₀ h‖ ≤ maxOpNorm h ^ (6 * m) * ε) ∧ ∫ h, star (F (x * (h, 1))) * K h * holMinorsPi s w h = 0) : ‖K₀ 1‖ ≤ 4 * ε * B ^ (7 * m) + ε := by
  have ⟨I, i⟩ := sp_j1 hn hm hB ho hu hd hw hk hk'
  choose K hK r _ using fun θ ↦ H (by simpa using i 1 continuous_one 1 0 : _ ∧ _).1
    _ (by simpa using congr(‖$((c z).apply_mul_diagTorus 1 (@toCircle 1 θ ^ o ·))‖).ge)
  refine let W θ h := _; have v h : ∫ θ, W θ h = _ := (c z).circle_mean_holMinorsPi ho hd h ▸ integral_conj; ?_
  have hf := ((i (K 0) (by fun_prop) (C + ε) _ le_rfl fun h ↦ by
    grw [norm_le_insert' _ (K₀ h), r, ← g]; ring; bound).1.comp_snd volume).mul_bdd (g := W.uncurry) (by fun_prop) (.of_forall (by simp [W]; tauto))
  obtain ⟨j, this⟩ := hf.integral_prod_right, integral_prod_symm _ hf ▸ integral_prod _ hf ▸ norm_integral_le_of_norm_le_const (hf.prod_right_ae.mono fun θ X ↦ by
      have ⟨d, q⟩ := i (W θ * (K 0 - K θ)) (by fun_prop) (4 * ε * ‖F z‖) _ le_rfl fun h ↦ by
        simp [W]; grw [h2, ← sub_sub_sub_cancel_right _ _ (K₀ h), norm_sub_le, r, r]; linarith
      rwa [← sub_eq_zero.1 ((integral_sub d X).symm.trans _)]
      simp; ring_nf; simp_all [W, mul_right_comm _ _⁻¹, mul_assoc z, integral_neg])
  simp_all [← mul_assoc, integrable_mul_const_iff, -Pi.mul_apply]
  grw [norm_le_insert (K 0 1), r]
  simpa [↓(sub_add_cancel k w ▸ (hK 0).mul ho.1 (isHolOfWeight_holMinorsPi ho hu)).integral_mul_conj_holMinorsPi ho hd j, I, field] using this
omit hn hm hB ho hu hd hw hk hk'
open BigOperators Circle ComplexConjugate Prod Space WeilData
attribute [local simp] EuclideanSpace.norm_eq Modulus.liftFn_apply Set.indicator firstMinimum_pos move_vecAtPoint vecToMat le_of_lt realCoord traceChar vacuumFn
variable {E n n' : Type} [Field E] [CMType E] [Fintype n] {s : _} [Fintype n'] {s'} [Nonempty n] [Nonempty n'] {S : Space E n s} (T : Space E n' s')
lemma h7 {N} [NeZero N] (hd : ↑N ∈ differentIdeal ℤ (𝓞 E)) :
    S.firstMinimum * T.firstMinimum / (shortBasisConst E n N * Fintype.card n' * Fintype.card n) ≤ (S.hom T).firstMinimum := by
  rw [le_firstMinimum_iff]
  use by grw [firstMinimum_le_one, firstMinimum_le_one] <;> simp [Nat.cast_inv_le_one, ← Nat.cast_mul], fun z _ o ↦ ?_
  choose Y hY hY' using S.exists_short_basis hd
  choose a b using (T.mem_and_norm_le_of_vecAtPoint _ S · (vecToMat (vecAtPoint _ z)) 1 (fun w ↦ l2_opNorm_le_of_apply ((archCoords _ z).norm_apply_le ⟨w, ·, ·⟩)) (by erw [one_smul, vecAtPoint_hom _ _ (vecToMat z), ratMap_mulVec_vecAtPoint]))
  have := S.firstMinimum_pos
  grw [firstMinimum_le (a _ (by simp_all [baseLattice]) (hY _)) (Function.ne_iff.1 fun H : (vecToMat z * Y.1)ᵀ = 0 ↦
    o (by simpa using! congr(matToVec ($Hᵀ * Y.2)))).choose_spec, b, hY']; simp [field]
omit [Nonempty n] [Nonempty n'] in
private lemma b7 [WeilData E] {𝔪} t v w z : dataInner _ (modDatum S T 𝔪 (traceChar t) v)
  (ϱ _ z (modDatum S T 𝔪 (traceChar t) w)) = 𝔪.liftFn (traceChar t ∘ vecToMat) (finCoord z) * (realInner v (realHeisOp (realCoord z) w) * vacuumFn (0, z · |>.2)) := by
  obtain ⟨u, rfl : of _ = _⟩ := 𝔪.reduction_surjective.comp_left.comp_left t
  erw [rho_integrated_realCoord, dataInner_integrated, (_ : _ ∘ vecToMat = _), 𝔪.name_char_eq_translate_projOn _ (matToVec u ∘ swap), ϱ_swap, map_smul] <;> simp +contextual [-Heisenberg.Rep.mul, funext_iff, finVec, ↓← rho_integrated, matToVec, finCoord, trace, adelicHeis, Matrix.mul_apply, ← map_mul, ← map_sum, stdForm, stdAddChar, dotProduct, fst_sum, snd_sum, ← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, two_mul, ← add_mul, ← map_add, mul_mem] <;> simp [stdLattice.psi₀_apply, Finset.mul_sum, sum_prod_type, mul_assoc, mul_left_comm, mul_comm (u ..).1]
private lemma p2 [WeilData E] {a b γ γ' ψ ψ' 𝔪 g} (ha : a.HasWeight γ ψ) (hb : b.HasWeight γ' ψ') {c : E} (c0 : c ≠ 0) (hc : ∀ z, 𝔪.reduction z = 0 → ↑c * (α.1 * ↑z) ∈ Ô E) h m
  q (m0 : 0 < m) (hm : ∀ w, m * ‖Φ w c‖ ≤ √(2 * .pi * (Φ w j).im) * ((S.move g).hom (T.move h)).firstMinimum) (hq : Fintype.card (InfinitePlace E × n' × n) < q) Q {v} (hv : v = polyVector _ Q) (d : ℕ) (hQ : ∀ (c : ℝ) x, Q.eval (c • x) = c ^ d * Q.eval x) : ∃ Ψ, ∀ u u', ‖modKernel S T a b
  𝔪 Ψ Q (g * (u, 1)) (h * (u', 1)) - realInner v (realPairWeil γ γ' (u, u') v)‖ ≤ maxOpNorm u' ^
  (3 * q) * (100 * (d + 2 * q) / m ^ 2) ^ q * ‖realInner v v‖ * maxOpNorm u ^ (3 * q) := by
  use 𝔼 t, conj (modKernel S T a b 𝔪 (traceChar t) Q g h) • traceChar t, fun u u' ↦ ?_
  let L := (S.hom T).move (G.onHom (g, h))
  rw [show hom .. = L by simp [L, move, hom, Units.ext_iff, mul_kronecker_mul, G.onHom]] at hm
  have A (y : {y | c • y ∈ L.baseLattice ∧ y ≠ 0}) : m ≤ ‖WithLp.toLp 2
    (realCoord (L.vecAtPoint y))‖ := by grw [← mul_le_mul_iff_right₀ L.firstMinimum_pos, ← norm_smul_of_nonneg, firstMinimum_le y.2.1, mul_comm, ← norm_smul_of_nonneg] <;> simp [*, abs_of_nonneg, archCoords, val_scaleIdele_fst, ← mul_assoc, ← mul_rotate √_, y.2.2]; grw [hm]
  have ⟨p, r⟩ := tsum_inv_pow_le_of_separated (n := 2 * q) m0 (fun y z h ↦ by simpa [sub_div] using (A ⟨y - z, by grind [smul_sub, sub_mem]⟩)) A (by simp_all; omega)
  have h4 := (hasSum_sum (s := ⊤) fun t _ ↦ let φ := ω _ (G.onHom (g, h)) ∘ modDatum S T 𝔪 (traceChar t); hasSum_dataInner _ (φ (realPairWeil γ γ' (u, u') v)) (φ v)).mul_left
    (Fintype.card (Matrix n n' 𝔪.ResRing) : ℂ)⁻¹
  simp [dataInner_omega_left, ω_ϱ, rep_apply_apply, b7, finCoord, ← Finset.sum_mul, sum_addChar_trace_mul, Modulus.isPrimitive_primAddChar, ← ext_iff] at h4
  refine ((((hasSum_subtype_iff_of_support_subset ?_).2 (hasSum_ite_sub_hasSum h4 0)).norm_le_of_bounded (p.hasSum.mul_left _) fun y ↦ .trans ?_ (norm_realInner_realHeisOp_le
    (pairHomInf (u, u')) hv hQ le_rfl (by simp) (m0.trans_le (A y)))).trans' ?_).trans ?_
  simp_intro y h
  simpa [L, baseLattice] using
    (hc _ <| (𝔪.reduction_idem_mul ⟨_, h.2.1 _ _⟩).symm.trans <| h.2.2.1.2 · ·)
  simp; split_ifs <;> simp [L, realPairWeil]
  rw [← modKernelBilin_apply]; simp [modKernel, pairTheta, ← mk_mul_mk, mul_comm (conj _), modDatum, *, pairWeil_integrated, Finset.expect, NNRat.smul_def, ← ZeroMemClass.zero_def, realCoord.eq_unfold, ← Pi.zero_def]
  simp [pairWeil, mul_mul_mul_comm _ _ (_ * _), ← coe_inv_eq_conj, mul_mul_mul_comm _ _⁻¹]
  nth_grw 1 [Complex.re_le_norm, r, hq, hq, pow_mul, mul_assoc, ← mul_pow, show ‖(pairHomInf _).1.1‖ ≤ maxOpNorm u * _ from (NonUnitalStarAlgHom.norm_apply_le ({ blockMatrix with .. } : _ →⋆ₙₐ[ℂ] Matrix (InfinitePlace E
    × n' × n) _ _) _).trans ((pi_norm_le_iff_of_nonempty _).2 fun w ↦ (norm_pairHom_le ..).trans (by
    gcongr <;> apply norm_le_pi_norm _ w))] <;> simp [U.one_le_norm, submatrix_smul, star]
  linear_combination
end
section
open Finset Fintype Matrix NumberField Sum WeilData Norms.L2Operator
attribute [local simp] prod_smul HasHolGap IsKDominant pairSign smul_pow smul_smul
lemma Data.b0 {P} {D : Data P} (j : D.LiftIndex) :
  ∃ (K₀ : _ → ℂ) (C ε : ℝ), 4 * ε * (5 * D.b) ^ (7 * nStar D) + ε < ‖K₀ 1‖ ∧ (∀ y, ‖K₀ y‖ ≤ C) ∧ ∀ g, (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum → ∃ c : _ → ℂ, ∀ y, ‖∑ a, c a * fNatural j a (g * (y, 1)) - K₀ y‖ ≤ maxOpNorm y ^ (6 * nStar D) * ε := by
  have hr : ((h3 j).Injective ∧ ∀ h, (n6 j h).Injective) ∧ (∀ a, f4 j (h3 j a) = -1) ∧ ∀ h a, f4 j (n6 j h a) = 1 := by
    refine ⟨⟨?_, fun _ ↦ ?_⟩, ?_, ?_⟩ <;> intro <;> intros <;>
      simp_all [h3, n6, basisVec] <;> split_ifs at * <;> simp_all [signsW] <;> grind
  have cSpec : (∀ N, carrierForm D.E D.m ∈ rapidOfLevel (signedSpace ..) N) ∧ ∃ o, IsPosFirstOrder (1 ⊕ᵥ -1) o ∧ IsAdelicHol o (fun _ ↦ 0 ⊕ᵥ 3 * D.m) (carrierForm D.E D.m) := by
    have hc := isTameFor_twistedChi (c := 2) j 1
    obtain ⟨⟨n, _, _, _⟩, _, _, H⟩ := id hc, by simpa [classSum, Rat.smul_def, mul_sum, ← mul_assoc, ← funext_iff] using (stdClassSum_carrierXi_eq_carrierForm D.E D.m_even).choose_spec hc
    use fun _ ↦ H ▸ (one_mul _).subst (mul_sum_mem_rapidOfLevel fun _ ↦ (one_mul _).substr
      ⟨⟨⟨by fun_prop [modKernel], (pairThetaKer ..).theta_rat_mul, ⟨_, isOpen_Kf⟩, ?l⟩, isRapid_modKernel _ _ _ _ n (⟨_, ·.nonsing_inv_mul <| MulChar.apply_ne_zero_iff.1 ·⟩) _ _⟩, (funext <| ?l _ ·.2.1)⟩), (-1 - ·) ⊕ᵥ (·), ?q, H ▸ (.sum _ fun _ ↦ isAdelicHol_pairTheta
      (by simpa +arith using (prod_letterMinor_mem_holomorphicData ?q (@.inl _ (Fin D.m)) 0 _).2) ·)
    simp [↓Subtype.forall', modKernel_mul_Kf_left, hc.apply_det, Pi.smul_def, mul_comm, MulChar.apply_eq_zero_iff]
    simp [IsPosFirstOrder, Function.Injective]; lia
  have cNe : carrierForm D.E D.m ≠ 0 := by
    have c a := (realInner_realPairWeil_eq_holMinorsPi (E := D.E) (-1) (1 ⊕ᵥ -1) (∏ τ, letterMinor τ (@inr (Fin a) (Fin D.m)) id ^ a) (by aesop (add safe [prod_mem,
      sum_mem], simp [letterMinor, det_apply', pairSign])) (ν := 0) · 0 fun _ ↦ by
      simpa [linSubst_letterMinor (κ := -1) (elim_inr _ _) Function.injective_id, smul_pow, -prod_smul] using prod_smul ..)
    have : CompactSpace (@USign (Fin D.m) _ (-1)) := (by simp [U] : USign _ = U 1).substr inferInstance
    apply mt (integral_eq_zero_of_lift_eq_zero (isSharp_modDatum _ 1 ?_ 0 (by subsingleton) ..) _ ?_ ?o ?_ · 0 ?o) <;> simp [Space.IsAutomorphic.mem_rapidFunctions, prod_eq_zero_iff, c, Space.petersson, holMinorsPi, holMinors, Heisenberg.IsVacuum.eq_zero_of_modelInner_self.mt, inr_injective, MeasureTheory.measureReal_univ_ne_zero, Function.injective_id, Space.isAutomorphic_const, NeZero.pos]
  obtain ⟨hm, ⟨h4, n⟩, b2, cl, _, ho, cH⟩ := (by simp [card_neg_signsW, j.2.2, *] :
    negCount (f4 j) = D.m), (by simp [↓card_rowIndex]; grind : card D.CarrierIndex ≤ D.t ∧ card (D.RowIndex ⊕ Q5 j) ≤ D.t), D.nStar_bounds, cSpec
  obtain ⟨⟨e⟩, ⟨eb, he, pb⟩, x, x0, xm, xl⟩ := @Function.Embedding.nonempty_of_card_le D.CarrierIndex D.Q3 _ _
    (by simp; omega), (@exists_eq_left _ (AutChar.HasWeight _ · 1) _).2 (s22_p9 j),
    exists_near_max (5 * D.b) D.x₁ ho (by simp; grind) (by simpa [Real.exp_nonneg] using D.le_of_hasLogBound) D.le_of_hasLogBound D.le_of_hasLogBound P.star_sqrtNegDInE
    (by simpa [P.d_prime.pos] using D.le_of_hasLogBound) (cl _) cH cNe
  let ς (_ : D.Φ) : D.CarrierIndex → ℤ := -D.reducedHalfGap ⊕ᵥ card D.Q3
  have pe := realInner_realPairWeil_eq_holMinorsPi (1 ⊕ᵥ -1) (f4 j) (s22_n8 j) (by
    simp (maxDischargeDepth := 9) [s22_n8, letterMinor, det_apply', prod_mem, mul_mem, pow_mem, sum_mem, hr]) (fun _ ↦ D.m) eb fun _ ↦ by simp [s22_n8, prod_pow_eq_pow_sum, -card_sum, linSubst_letterMinor (hr.2.2 _) inl_injective, linSubst_letterMinor hr.2.1 inr_injective]; rfl
  extract_lets v k C at pe
  let ι y : GInf D.E (f4 j) := (G.sum ((y, 1), 1)).1
  have ⟨J, H⟩ := sp_j1 (m := nStar D) (B := 5 * D.b) (by grw [h4])
    D.le_of_hasLogBound D.le_of_hasLogBound ho (w := ς) (k := k) (by simp [ς]) (by simp [k])
    (by simp [ς, reducedHalfGap]; lia) (by simp [k, -Nat.cast_sum]; grind [reducedHalfGap])
    fun w i ↦ by grw [← two_mul_card_detIndex_add_le j w]; clear * - hm; norm_cast; grind
  obtain ⟨v0, _, _, _, c, hc⟩ := RingOfIntegers.coe_ne_zero_iff.2 (pow_ne_zero 2 D.piGBar_ne_zero), NeZero.ne D.cycloConductor, D.t_odd.pos, ((signedSpace ..).move x).firstMinimum_pos, reproducing_formula_modKernel ho D.ideal_untwistedModulus_eq_span nonempty_modulus_places _
    (hasWeight_upsilonU1_pow D.m) .one (u := ς) (by simp [ς]) (by simpa using H 1 (by fun_prop) 1 0 : _ ∧
    _).1 (by simp; omega) e (prod_letterMinor_mem_holomorphicData ho (.trans .inl e) ..) _ (fun p ↦
    realPairWeil_mem_span_pairedDetProd (Y := D.n0 (p, 0)) _ (by simp [n0]) _ _) x
  have key {A b} N l (h : ∀ u, ‖A u‖ ≤ b * maxOpNorm u ^ N) (a :
    Continuous A := by fun_prop [modKernel]) := H
    _ ((cH x).continuous.fun_mul a) _ N l fun u ↦ by grw [norm_mul, xm, h, mul_comm, mul_right_comm]
  choose _ _ _ l a r using (isUnitaryRep_detTwist (ε := realSigns D.E (homSigns (n := D.CarrierIndex) (1 ⊕ᵥ -1) (f4 j))) (f := .id _) (γ := 0) (one_mul _).ge).exists_innerProductSpace; simp at r
  have k0 y := key (A := (C · y)) 0 bot_le fun _ ↦ by simp [C, realPairWeil, ← a]; grw [norm_inner_le_norm, r]
  have e1 := IsHolOfWeight.integral_mul_conj_holMinorsPi (u := k) ho (by simp [k]) (by
    convert ((cH x).mul ho.1 (isHolOfWeight_holMinorsPi (u := ς) ho (by simp [ς]))).mul ho.1
      (.sum (T := {0}) ![C 1 1] fun _ ↦ isHolOfWeight_holMinorsPi ho (u := v) (by simp [v]))
    ext w (_ | _) <;> simp [ς, v, k, he, hm, ← card_detIndex_add_bigCharExp j] <;> omega)
  simp [mul_assoc _ (C .. * _), ← pe, mul_right_comm _ _ (C ..)] at e1
  refine ⟨_, _, _, ?_, (ι · |> k0 |>.2), fun g hl ↦ (p2 ((D.spaceW j).sum ((stdSpace ..).neg.sum (stdSpace ..))) (hasWeight_upsilonU1_pow _) pb (div_ne_zero (NeZero.ne (D.N₁ : D.E)) v0) ?_ (.sum (g, 1)) (D.b ^ 7 * D.x) (2 * nStar D) (HasLogBound.pos D)
    (fun w ↦ ?_) (by grw [card_prod, card_prod, h4, n]; use D.nat_lt_of_hasLogBound) (s22_n8 j)
    rfl _ fun _ _ ↦ by simp [-sum_add_distrib, -prod_mul_distrib, s22_n8, letterMinor, det_apply', ← Complex.coe_smul, -smul_eq_mul, ← smul_sum, ← pow_mul, ← pow_add, prod_pow_eq_pow_sum]; rfl).elim fun Ψ hΨ ↦ (exists_sum_smul_addChar_trace_eq (D.untwistedModulus
    2).isPrimitive_primAddChar fun x ↦ Ψ x.toRows₁ * (Pi.single (inclMatrix _ e) 1 : _ → ℂ)
    x.toRows₂).imp' (fun f a ↦ c a.2 * f a.1) fun f hf y ↦ (key _ (by omega) (hΨ · (ι y))).elim fun i q ↦ (congrArg _ (sub_eq_of_eq_add (.trans (.trans ?_ ((hc _ (mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (hb := pb) (cl _) ..)).symm.trans
    (by congr with; simp [field]))) (MeasureTheory.integral_add i (k0 _).1)))).trans_le (q.trans
    (by simp_rw [mul_assoc]; grw [← mul_assoc 3, show maxOpNorm _ ≤ maxOpNorm y by simp [ι, G.sum, U.sum, pi_norm_le_iff_of_nonempty, o9, norm_le_pi_norm (y · |>.1.1)]]; rfl))⟩
  grw [show ι 1 = 1 by simp [ι], e1 (k0 _).1, (?_ : _ / _ ≤ (D.b ^ 12)⁻¹)]
  simp [C, abs_of_pos J, field, ← a, s22_n8]
  field_simp [prod_eq_zero_iff, hr, inl_injective, inr_injective]
  use D.lt_of_hasLogBound
    (by clear * -; grind [(D.le_of_hasLogBound : 1 + 7 * |↑(nStar D)| ≤ nStar D * D.logB)])
  grw [Nat.cast_sum, sum_le_card_nsmul _ _ (2 * D.m * (5 * D.b)) fun w _ ↦ by
    grw [← two_mul_card_detIndex_add_le j w]; clear * -; norm_cast; simp [← mul_sum]; lia]; simpa using D.le_of_hasLogBound
  simpa [Modulus.reduction_eq_zero_iff, ideal_untwistedModulus_eq_span, Ideal.mem_span_singleton, ↓dvd_def, -Subtype.forall, ← mul_assoc, mul_right_comm _ α.1, ← map_pow, ← map_mul, -Nat.cast_mul, ↓div_mul_cancel₀ _ v0, -Subtype.exists] using! fun z : Ô _ ↦ mul_right_comm _ _ z.1 ▸ mul_mem P.N₁_mul_α_mem z.2
  · grw [← h7 _ P.cycloConductor_mem_different, Space.shortBasisConst, ← inf_le_firstMinimum_sum, ← G.sum.map_one, ← inf_le_firstMinimum_sum, ← ((stdSpace ..).move _).one_le_firstMinimum, ← ((stdSpace ..).neg.move _).one_le_firstMinimum, inf_idem, inf_of_le_left (by simp), ← hl, ← xl _ le_rfl, h4, n, show ‖_‖ = (D.N₁ : ℝ) / D.gProd by
      simpa [sq, -Nat.cast_mul] using congr(D.N₁ / ‖Φ w $D.piGBar_mul_star‖)]
    simpa [WeilData.j] using D.le_of_hasLogBound
  · simp_rw [sum_prod_type_right (α₂ := _ × _), mul_assoc (c _), ← mul_sum, fNatural, Pi.mul_apply]
    congr! 2; rw [← integral_mul_sum_const_mul fun t ↦ mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (cl _) ..]; congr with
    simp_rw [mul_assoc, ← modKernel_sum_right, ← hf, ← modKernelBilin_apply]; simp [ι, G.sum, ← map_mul]; left; rfl
end
seal Finset.univ Finset.sum Finset.prod
open NumberField Multiset Data Int Fintype Real WeilData Data.Pair Additive Function Matrix Sum
variable {P} {D : Data P}
@[simp] lemma cmSign_star σ : @cmSign D.E _ _ (star σ) = -cmSign σ := by
  grind [cmSign, neg_neg, Φ_eq_or, InfinitePlace.mk_eq_iff]
lemma isRowType_auxPair {j} (hj : j ∈ D.LiftIndex) : IsRowType D D.r D.t fun σ ↦ (Multiset.range
  D.r).map fun q ↦ D.t / 2 - cmSign σ * (D.rowParameter (.mk σ) q + D.w j (.mk σ)) := by
  use ⟨D.nat_le_of_hasLogBound, .refl⟩, .refl, ⟨j, hj.2, by simpa using fun σ p _ ↦ by grind
    [rowParameter, units_natAbs, (mul_le_mul_left (by grind : p + 2 - D.k + j < D.t) D.h).trans (D.nat_le_of_hasLogBound (B := D.h₂ ^ 2))]⟩, fun σ ↦ (mul_le_mul' (?_ : _ ≤ D.r + 1 - D.k)
    D.k_le_r).trans (by grind), fun σ ↦ ?_ <;> induction D.r <;> simp_all [countP_cons] <;> grind
    [rowParameter, units_natAbs, !(D.nat_lt_of_hasLogBound : 2 * D.h₂ ^ 2 + D.h₂ < D.w _ _)]
def Data.eSign {P} (D : Data P) (s : ℤˣ) := ite (s = 1) D.m (D.m / 2)
def Data.y8 {P} (D : Data P) := 7 * (D.m / 2) + D.k / 2
noncomputable def Data.n9 {P : Parameters} {D : Data P} (j : D.LiftIndex) : Option ℤˣ → D.Pair := by
  let n := j + (D.t - 11 * D.m - 1) / 2
  refine' Option.rec (.mk _ (D.w j · - n) _ D.y8 (((D.mu₀_hasWeight j).mul_upsilonU1_pow
    n).of_weight_eq _) ..) fun s ↦ ⟨_ * _ ^ (s.1 * j), fun _ ↦ D.eSign s, _, D.eSign s, by
    simpa using! (WeilData.hasWeight_upsilonU1_pow _).inv.mul (D.chi_hasWeight.zpow _), _, _, _, _⟩
  any_goals refine' fun v ↦ .trans (b := (D.w j v : ℝ)) (Nat.mono_cast _) _
  all_goals grind [y8, eSign, omega_eq_one_of_not_isChosen, _root_.one_zpow, Pi.pow_apply, w_le_two_mul_b]
noncomputable def Data.heckeValueProd {P} {D : Data P} (j : D.LiftIndex) (ϑ : D.Twist) := ∏ i, (lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) ((n9 j i).ν * ϑ.toAutChar ^ (i.getD 1).1)⁻¹ (n9 j i).z : ℂ)
namespace Data
variable {P : _} {D : Data P}
lemma g7 n [Fintype n] (hn : 4 ≤ Fintype.card n ∧ Fintype.card n ≤ D.t ∧ 2 ∣ Fintype.card n := by simp; grind) (χ : AutChar.tameChars D.finite_isChosen.toFinset) :
  ∃ p : D.Pair, (rankTwist p.ν n = χ.1.1 ∧ p.ψ = χ.1.2) ∧ p.IsFlat n := ⟨⟨_, _, _, Fintype.card
  n / 2, by simpa using! χ.2.1.mul (hasWeight_upsilonU1_pow _).inv, by simp_all [χ.2.2], by
    grind, fun _ ↦ le_rfl, fun _ ↦ .trans (mod_cast by lia) (D.le_of_hasLogBound : ↑D.t ≤ _)⟩, by simp [rankTwist]; lia⟩
lemma m2 {j p} (H : @IsRankOne P D p j) :
    HeightLe (D.B₀ - ∑ τ, D.jetSize (D.w 0 τ)) fun _ ↦ ‖trivialLift H.1 .one‖ ^ 2 := by
  obtain ⟨q, -, h⟩ := D.g7 (RankOneIndex p.z) (by grind [IsRankOne]) 1
  refine ⟨q.intAlgPart h.2 .one / ‖trivialLift H.1 .one‖ ^ 2, _, 0, by simp,
    (P.exists_algEquiv_norm_eq · |>.elim fun σ e ↦ (log_norm_map_norm_sq_trivialLift D (RankOneIndex p.z) σ).elim fun _ k ↦ le_exp_of_log_le ?_), by simp [(isIntegralMeasure_intAlgPart ..).norm_apply_one_le], by aesop⟩
  obtain - := k, k _ h.2, k _ H.1, sum_mono fun τ ↦ D.jetSize_le_add
    (by cases j <;> grind [IsRankOne] : D.w 0 τ ≤ p.c τ - p.z + 0)
  simp [h, Pair.intAlgPart, twist_one_spec, denomBound, log_mul, log_div, NeZero.ne, jetSize] at *; rename_i a b _; obtain ⟨⟨_, _, _, _⟩, _, _, -, _⟩ := And.intro a b; simp only [e]
  linarith [(D.le_of_hasLogBound : Real.log D.chosenGroupOrder + D.f * (8 * q.z * Real.log D.gProd + 8) ≤ D.B₀)]
end Data
attribute [local simp] Data.j6 Data.h3 Data.detRows
lemma Data.cosetKernelSum_eq_fNatural {P} {D : Data P} {a} [Fintype a] j : ∃ C, ∃ c : D.Twist → ℂ, ∀ ϑ, ‖c ϑ‖ ^ 2 = C / heckeValueProd j ϑ ∧ ∀ (u : Matrix _ a (D.untwistedModulus 2).ResRing) i g
  (w : Matrix a _ (D.untwistedModulus 2).ResRing), u * w = i.1 → fNatural j i g = c ϑ * cosetKernelSum (D.auxPair ϑ j) (bigChar ϑ j) w (.trans .inl .inl) (lineMultiplier ϑ j i) g := by
  have' hs : _ = blockSigns (.ofBijective (j6 j ∘ Sum.map (D.basisVec ∘ Fin.val (n := D.posRank j)) inr ⊕ᵥ inr ∘ inl ∘ h3 j) _) := _
  have e ϑ : bigChar ϑ j * WeilData.upsilonU1 ^ D.m = twistedChi ϑ j * g4 j := ?_
  have' := (explicit_matching _ (.refl _) · 1 (posEquiv j) _ hs _ _ (DetIndex j))
  choose _ _ _ hK using this
  choose _ _ _ hM using stdClassSum_carrierXi_eq_carrierForm D.E D.m_even
  repeat constructor
  refine fun ϑ ↦ let hν := (isTameFor_twistedChi j ϑ).mul (s22_p9 ..); .symm ⟨fun u i g w H ↦ .symm (.trans ?_ (explicit_matching_of_sum _ _ hν (hM (isTameFor_twistedChi j _)) (D.untwistedModulus 2) levelModulus_ideal_le _ fun _ _ h _ ↦ (hK _ hν
      (by simp [← card_detIndex_add_bigCharExp j]) (detRows j i.2) h (bigChar ϑ j) _ :).trans (by
    congr! <;> simp [← e, matchedPoly, pairedDetProd, letterMinor, ← mul_assoc, s22_n8, prod_sigma, AlgHom.map_det, Matrix.map, ← Finset.prod_mul_distrib]
    congr! 4; omega; rw [← Fin.prod_const]; congr!
    repeat ext; simp [entrywise, inclMatrix, n6] <;> split <;> rfl))), ?_⟩
  simp_rw [@classSum_comm (Gf _ (BigIndex j)), ← mul_classSum]
  refine congrArg _ (.trans ?_ congr(stdClassSum _ fun _ ↦ _ * $(stdClassSum_rowStabilizer_eq hν (by
    rw [hs]; simpa [-j6] using! realPairWeil_stackedDetProd _ _
      (funext (by simp [← card_detIndex_add_bigCharExp j])) (detRows j i.2) 1) (s22_g3 _) w (.trans .inl .inl) (F := fun y ↦ ∑ k : GL _ _, traceChar i.1 (y.map (s22_g3 _) * k.1))
    fun A a ↦ by simp [traceChar, Matrix.mul_assoc, trace_mul_comm (A.1.map _), ← H, a.2])))
  simp_rw [mul_classSum, @classSum_comm (Gf _ D.CarrierIndex), ← e, cosetKernelSum]; congr with h; clear * -
  change modKernelBilin (D.spaceW j) _ _ _ _ _ _ (columnDatum _ (s22_g3 _) _ _) (letterPoly _ _ 1 (untwistedAuxPair j).colsPlus _) = _
  rw [pi_eq_sum_univ' (lineMultiplier ϑ j i h)]; symm
  simp [lineMultiplier, modKernelI, mul_classSum, ← classSum_sum, mul_left_comm (modKernel ..), mul_assoc, -mul_ite, ← Finset.mul_sum, mul_comm (modKernel (.sum ..) ..), ← modKernel_sum_left, -j6]; congr!
  erw [← modKernel_reindex (j6 ..).symm ?_ (.refl _) rfl, ← map_sum ((modKernelBilin ..) _), modKernelBilin_apply]; congr! -closePost 1; rfl
  ext1; simp [GeneralLinearGroup.ext_iff, Space.reindex, Space.sum]
  rfl; grind [pow_sub_mul_pow, card_neg_signsW, auxPair]
  congr! 2; simp [h9, ← ite_and]; congr
  simp [entrywise, inclMatrix, forall_and, -sum_sum_type]; tauto
  simpa [Prod.map_comp_map, ← comp_assoc, -j6] using!
    stdClassSum_carrierXi_eq_lineMultiplier j _ inl (inr ∘ inr)
  apply G.ext_mat; simp [entrywise, Prod.ext_iff, funext_iff, U.sum]; iterate 3 aesop
  simp [← Complex.ofReal_pow, mul_pow, div_pow, heckeValueProd, places_modulus_eq_union, *, n9, eSign, ← division_def, div_right_comm _ (_ * _), div_mul_div_comm]; with_reducible congr
  any_goals clear * -; apply_fun ofMul; simp [bigChar, liftChar, twistedChi, g4, μ₀];
            match_scalars <;> grind [y8]
  all_goals simp [↓card_rowIndex, ↓bijective_iff_injective_and_card, Injective, signsW, funext_iff, ↓Equiv.eq_comp_symm, apply_dite (f4 j), basisVec]; grind [Equiv.injective, y8]
unseal Finset.univ Finset.prod
namespace Data
variable {P : _} {D : Data P} {j : D.LiftIndex} (F : D.goodForms (D.spaceW j))
lemma s22_j4 {a} (d : D.piGBar ∣ a := by simp) :
  F.1.1.1 ∈ rapidOfLevel (D.spaceW j) a := ⟨F.1.1.2.mem_rapidFunctions D.isCuspKernel_paramW, (funext <| Space.mem_levelSpace_formRep_iff.1 F.1.2 _ <| D.principalLevel_le_chosenLevel d ·.2)⟩
lemma mul_fNatural_mem_rapidOfLevel_and_hol i : F * fNatural j i ∈ rapidOfLevel (D.spaceW j)
  (D.piGBar ^ 2) ∧ IsAdelicHol (orderW j) (conjHolWeight j - kernelWeight j) (fNatural j i) := by
  choose _ _ _ e using cosetKernelSum_eq_fNatural (a := D.CarrierIndex) j
  simpa only [Pi.sub_def, conjHolWeight_eq_add_kernelWeight, add_sub_cancel_right, funext (e 1 1 i · _ i.1.one_mul), cosetKernelSum, classSum, finsum_eq_sum_of_fintype, Rat.smul_def, Finset.mul_sum, ← mul_assoc] using have G := D.fitsParams_auxPair ..; ⟨mul_sum_mem_rapidOfLevel fun _ ↦ mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (s22_j4 F) _ _ _ ((auxPair ..).tame_eq_one · <| places_levelModulus.ge.mt ·), (.sum _ fun _ ↦ isAdelicHol_pairTheta
    (mem_holomorphicData_of_highestVector (e' := 0) (_ ∘ₗ _) (by simp [Injective, Fin.val_inj]) (by
      intros; erw [realPairWeil_fockLetters, star_mulVec]; simp [letterPoly, weylRep, ← mulVec_transpose, comp_def, conjTranspose_transpose]) (letterPoly_highestVector_holomorphic isPosFirstOrder_orderW (paramW_lt_of_orderW_lt 1) (G.paramsCorrespond 1).2.1 (G.ord_eq 1) _ G.colsPlus_eq_zero).2) ·)⟩
end Data
open ComplexConjugate AuxPair Parameters
noncomputable def Data.tableTheta {P} {D : Data P} (j : D.LiftIndex) (ζ : D.SmallClasses → _) g := ∑ c, conj (modKernelI (D.spaceW j) (untwistedAuxPair j).a (upsilonU1 ^ (D.m / 2 - j : ℤ)) (D.untwistedModulus 2) (Pi.single (inclMatrix _ .inl) 1) (letterPoly (D.signsW j) (untwistedAuxPair j).ord (-1) (untwistedAuxPair j).colsMinus (star (ζ c))) g c.out)
lemma Data.eq_zero_of_integral_fNatural_tableTheta {P} {D : Data P} {j : D.LiftIndex} (F : D.goodForms (D.spaceW j)) (h : ∀ i ζ, ∫ g, conj (F.1.1 g * fNatural j i g) * tableTheta j ζ
  g ∂(D.spaceW j).quotMeasure = 0) : F = 0 := by
  obtain ⟨o, N, G, _, _, _, ε, C, M⟩ := @isPosFirstOrder_orderW _ D j, rank_bounds_card_bigIndex j, D.fitsParams_auxPair _ j, b0 j
  have H : IsAdelicHol (orderW j) (conjHolWeight j) (star <| F.1.1 ·) := by
    obtain ⟨⟨_, e'⟩, _, J, k, _⟩ := (_ ∘ₗ _).surjective_of_injective
      ((LinearMap.self_comp_adjoint_injective_iff _).2 (D.auxLift_injective .one)) F.1, G.exists_isJointHarmonic
    erw [← e', (exists_theta_to_principalForms ..).choose_spec j.2]
    simpa [θ, AuxPair.conjKernel, classSum, Rat.smul_def] using! (.sum _ fun _ ↦ isAdelicHol_pairTheta (mem_holomorphicData_of_highestVector (_ ∘ₗ _) (J · |>.gap.1) (realPairWeil_harmonicPoly _) (congr(polyVector _ $k).substr (prod_mem_holomorphicData o paramW_lt_of_orderW_lt (J · |>.2) rfl).2)) ·)
  choose w6 w3 w2 w5 w4 using conjHolWeight_kernelWeight_bounds j
  choose lG hG using mul_fNatural_mem_rapidOfLevel_and_hol F
  repeat apply Subtype.ext
  refine star_eq_zero.1 (by_contra (exists_near_max _ _ o (by grind only [HasHolGap, nStar_bounds])
    w6 D.le_of_hasLogBound D.le_of_hasLogBound (by simp [star_sqrtNegDInE]) (by simpa [NeZero.pos] using D.le_of_hasLogBound) (star_mem_rapidOfLevel (s22_j4 F (.mul_right ⟨_, D.piGBar_mul_star.symm⟩ (sqrtNegDInE ..)))) H · |> fun ⟨g, g0, g2, hl⟩ ↦
    ε.not_ge (isolation (by bound) D.le_of_hasLogBound D.le_of_hasLogBound o w2 w3 w4 w5 w6 F.1.1.2.continuous.star H g0 g2 C fun I z a ↦ ⟨_, .sum _ (hG · _), (M _ (hl _ a)).choose_spec, ((reproducing_formula_modKernel o D.ideal_untwistedModulus_eq_span nonempty_modulus_places _ (hasWeight_upsilonU1_pow _) (hasWeight_upsilonU1_zpow _) w2 I
    (by simp [N]; omega) .inl (letterPoly_highestVector_holomorphic o (paramW_lt_of_orderW_lt 1) (G.paramsCorrespond 1).2.1 (G.ord_eq 1) _ G.colsMinus_eq_zero) (fun _ ↦ fockLetters (D.signsW j) (untwistedAuxPair j).ord (-1) ∘ nablaBasis ℂ _ (untwistedAuxPair j).colsMinus)
    (by intros; erw [realPairWeil_fockLetters]; clear * -; aesop (add safe sum_mem,
    simp [toPoly, linearCombination_apply])) z).choose_spec _ (star_star F.1.1.1 ▸ mul_sum_mem_rapidOfLevel lG :)).trans (Fintype.sum_eq_zero _ fun c ↦ ?_)⟩)))
  simp [mul_assoc, Finset.sum_mul]
  refine .inr ((integral_mul_sum_const_mul fun i ↦ (mul_assoc ..).subst (mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (lG i) ..)).trans (Fintype.sum_eq_zero _ fun i ↦ mul_eq_zero_of_right _ ?_))
  let ⟨v, e'⟩ := range_toPoly.ge (prod_tableauPoly_mem_nabla : nablaBasis ℂ _ _ c.2 ∈ _)
  simpa [tableTheta, ← integral_conj, ← modKernelBilin_apply, apply_ite, letterPoly, e', mul_assoc, nablaBasis] using! congr(conj $(h i (Pi.single c.1 (star v))))
