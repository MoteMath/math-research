import New.Exchange.CrudeModularData
import New.Trace.GoodIdempotent
import New.Rows.MemberKernels
section
open Nat Finset Parameters Real
variable {P} {D : Data P} {p : ℕ} (D' : Data P) {e : ℕ}
instance Data.instUbCastRealRrLogLx₁ [hq : Fact p.Prime] :
  D.HasLogUpper (D.ceilLogM p) (log D.logX₁) := D.hasLogUpper_of_le
  (A := D.s) (clog_le_of_le_pow (by grw [← hq.1.two_le]; use D.nat_le_of_hasLogBound))
lemma Data.IsServed.m_dvd_orderOf [hq : Fact p.Prime] (h : D.IsServed p) :
  D.m ∣ orderOf (D.placeOfInt (-p)) := by
  obtain ⟨⟨⟩, i, _⟩ := D.m_pow, h
  have := @two_pow_dvd_or_of_pow_eq_one (-p) _ D.s (orderOf_pos (D.placeOfInt (-p)))
    (placeClass_placeOfInt (d := two_pow_dvd_N₁) (@isCoprime_N₀_of_not_dvd P 0 p _
    (by grind [chiK_eq_one_of_dvd, Fact])).neg_left ▸ mod_cast by simp [← map_pow])
  simp_all [IsShortPrime, ← Int.natAbs_dvd_natAbs, Int.natAbs_mul, padicValNat_dvd_iff]
  grind [padicValNat.mul]
lemma Data.le_loss p : D'.f * D'.logB ^ 2 * (D'.a / p) ≤ D'.loss p := by rw [loss]; bound [D'.le_m]
lemma Data.placeOfInt_mul_mem_tops_iff (o : Odd e) : ∀ τ ∈ D'.tops,
  D'.placeOfInt (-p ^ e) * τ ∈ D'.tops ↔ D'.o₀ p ∣ e := by
  simp_all [o₀, tops, ← o.neg_pow, ← placeOfInt_pow, orderOf_dvd_iff_pow_eq_one]
variable {p : ℕ} [hq : Fact p.Prime] [PadicPlace p] {Λ : Finset (FinPlace D.E)} {l : FinPlace D.E}
lemma Data.p_mem_inducedPlace σ : ↑p ∈ (D'.inducedPlace σ).1 := natCast_mem_placeOfEmb _
lemma Data.inducedPlace_mul σ τ : D'.inducedPlace (σ * τ) =
  τ • inducedPlace σ := by ext; simp [inducedPlace, phi_mul]
attribute [local grind] Data.IsMarked Data.IsServed Data.p_mem_inducedPlace
  Data.inducedPlace_mul Nat.Prime.dvd_mul
  Nat.prime_dvd_prime_iff_eq not_dvd_N₁_mul_d_of_inert smul_eq_star_iff_inert star_star
lemma Data.inducedPlace_neg_pow_mul_of_odd (h : chiK P.d p = -1) (he : Odd e) σ :
    D'.inducedPlace (D'.placeOfInt (-p ^ e) * σ) =
  star (inducedPlace σ) := by grind [mul_comm, placeOfInt_pow, he.neg_pow (p : ℤ)]
lemma Data.exists_isMarked (D : Data P) (hp : p < D.x₁) (h : D.IsServed p) : ∃ Λ,
  D.IsFullMark Λ := by
  cases exists_wellFoundedLT (FinPlace D.E)
  use {l ∈ D.tops.image inducedPlace | l < star l}, by grind, fun τ a ↦ by grind [h.m_dvd_orderOf, →
    Even.trans_dvd, D.inducedPlace_mul τ 1, orderOf_dvd_of_pow_eq_one,
    inducedPlace_neg_pow_mul_of_odd, (D.placeOfInt_mul_mem_tops_iff h.2.2.1 τ a).2 dvd_rfl]
lemma Data.inducedPlace_eq_or_star_iff (h : chiK P.d p = -1) σ τ : D.inducedPlace σ =
  inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ) ↔ ∃ i, σ =
  D.placeOfInt (-p) ^ i * τ := by grind [mul_div_cancel τ σ, mul_comm, smul_eq_iff_inert]
lemma Data.IsMarked.card_le (h : D.IsMarked Λ) : #Λ ≤ D.f :=
  card_le_card_of_surjOn inducedPlace fun _ ↦ by grind
lemma Data.IsMarked.not_dvd_gProd_mul_N (h : D.IsMarked Λ) : ¬p ∣ D.gProd ∧ p ≠ D.N ∧
  ¬p ∣ D.gProd * D.N := by grind [gProd, hq.1, g_prime, N_prime,
  (D.le_of_hasLogBound : D.x₁ ≤ D.N), !(D.le_of_hasLogBound : D.x₁ ≤ D.g _)]
lemma Data.IsMarked.notMem_thick (h : D.IsMarked Λ) σ (a : inducedPlace σ ∈ Λ ∨
  star (inducedPlace σ) ∈ Λ) : σ ∉ D.thick := fun _ ↦ P.pow_d_ne_neg_one 0 (by
  let ⟨i, t, _, _, o, _⟩ : ∃ i, D.placeOfInt (-p) ^ i * σ ∈ D.tops ∧
    D.IsServed p := by grind [inducedPlace_eq_or_star_iff]
  simp_all [tops, placeClass_of_thick]
  simpa [o₀, pow_right_comm _ i, ↓o.neg_pow] using congr((-$t ^ D.o₀ p).1))
lemma Data.IsMarked.sum_inducedPlace_sub_star_eq_zero (h : D.IsMarked Λ) j (G : ℕ → _ → ℝ) : 0 =
  ∑ τ, (ite (inducedPlace τ ∈ Λ) (G (D.w j τ) (inducedPlace τ)) 0 - ite (star (inducedPlace τ) ∈ Λ)
  (G (D.w j τ) (star (inducedPlace τ))) 0) := by
  rw [sum_sub_distrib, Fintype.sum_equiv (.mulLeft (D.placeOfInt (-p))), sub_self]
  simp; grind [notMem_thick, (D.inducedPlace_neg_pow_mul_of_odd · odd_one)]
lemma Data.IsMarked.p_mem (h : D.IsMarked Λ) (a : l ∈ Λ) : ↑p ∈ l.1 := by grind
lemma Data.IsMarked.valuation_p (h : D.IsMarked Λ) (a : l ∈ Λ) : l.valuation D.E p = .exp (-1) := by
  erw [l.valuation_of_algebraMap p, intValuation_p] <;> grind
lemma Data.IsMarked.star_ne (h : D.IsMarked Λ) (a : l ∈ Λ) : l.IsSplit := by grind
lemma Data.IsMarked.maxCompactAt_le_columnLevel (h : D.IsMarked Λ) (a : l ∈ Λ) :
    maxCompactAt _ l ≤ D.columnLevel 0 := (inf_supportedOn_le_principalLevel
  (by grind [not_dvd_gProd_mul_N, =_ l.natCast_mem_iff_dvd, piGBar_mul_star, π_mul_star,
  l.2.mul_mem_iff_mem_or_mem, mem_star_place, star_mul])).trans (principalLevel_le_columnLevel ..)
noncomputable def Data.IsMarked.markOperator (h : D.IsMarked Λ) (l : Λ) :
  Module.End embValRing D.Column := .restrictScalars _
  <| (p : ℂ) ^ markExponent l.1 • (heckeSplit _ (h.star_ne l.2) (D.ceilLogM p)).restrict fun _ a ↦
  heckeSplit_mem_levelSpace _ _ (levelSpace_anti (h.maxCompactAt_le_columnLevel l.2) a) IsLevel.le a
noncomputable def Data.jetExponent p j ev := let n := D.n (j + 1); let N := boxes D.κ n
    (1 / (p - 1) - nonsplitWeight P.d p) * N + (chiK P.d p - 1) / 2 * ∑ e ≤ p.log N with Odd e ∨ p =
      P.d,
      ∑ σ, couplingCount p D.κ n ev σ (D.placeOfInt (-p ^ e) * σ) e - D.f * n ^ 3 * (p.log N + 1)
lemma Data.IsCollision.ne_and_odd_and_dvd {p ev τ} (h : D.IsCollision p ev τ e) : p ≠ P.d ∧ Odd e ∧
  D.o₀ p ∣ e := by grind [IsCollision, tops, ne_d_of_placeClass_eq, placeOfInt_mul_mem_tops_iff]
variable {p : ℕ} [q : Fact p.Prime] {j : ℕ}
lemma Data.collisionSum_le {S o} (h : ∀ {τ e}, D.IsCollision p S τ e → o ≤ e) :
    D.collisionSum p S ≤ 2 * D.f * D.a / p ^ o := by
  grw [collisionSum, ((add_right_injective o).tsum_eq fun e a ↦ le.dest (by
    grind [Function.mem_support])).ge, le_norm_self (tsum _), tsum_of_norm_bounded
    (hasSum_geometric_two' (D.a / p ^ o * 2))]; simp [field]
  intro; split <;> simp [pow_add, ← div_div] <;> bound [cast_le (α := ℝ).2 q.1.two_le]
lemma Data.mul_collisionSum_le_loss (H : D.IsSmallNonsplit p) (h : ¬D.IsServed p) :
  D.m * D.collisionSum p ∅ ≤ D.loss p := by
  grw [loss, ← (D.le_of_hasLogBound : 2 ≤ D.logB ^ 2)]; split; grw [collisionSum_le (·.1.1)]; grind
  grw [collisionSum_le (o := D.ceilLogM p + 1) (by grind [IsServed, IsCollision.ne_and_odd_and_dvd,
    IsCollision, chiK_cases, Odd.of_dvd_nat,
    → le_of_dvd]), le_pow_clog q.1.one_lt D.m, ← ceilLogM]
  have := q.1.ne_zero; simp [pow_succ, field]
lemma Data.IsFullMark.collisionSum_evenPlaces_eq_zero [PadicPlace p] (h : IsFullMark Λ) :
  D.collisionSum p (evenPlaces Λ) = 0 := by
  simp (disch := grind [IsCollision.ne_and_odd_and_dvd, IsCollision,
    inducedPlace_neg_pow_mul_of_odd, IsMarked, IsServed, IsFullMark]) [collisionSum, ite_eq_right]
lemma Data.lowColumns_lowBoxes_bounds (hj : j < D.m) σ : D.k * D.nominalWeight σ ≤ D.lowBoxes j σ ∧
  D.lowColumns j σ ≤ D.nominalWeight σ + D.x ^ 60 ∧
  D.lowBoxes j σ ≤ D.k * D.nominalWeight σ + D.x ^ 60 := by
  obtain ⟨k : D.k ∈ range (D.n (j + 1)), _⟩ := by simp [n], D.hasLogUpper_of_le (D.n_mono hj)
  use by grw [lowBoxes, ← single_le_sum (by simp) k,
    nominalWeight_le_w_sub _ 1]; rify; gcongr; norm_cast; grind [κ]
  grw [lowColumns, lowBoxes, κ_le, κ_le]; simp [k, mul_add, ← sum_mul, sum_range_id]
  grw [D.w_le_nominalWeight_add D.nat_le_of_hasLogBound, Nat.div_le_self, sub_le]; simpa [add_assoc,
    mul_add] using ⟨D.le_of_hasLogBound, D.le_of_hasLogBound⟩
lemma Data.le_jetExponent (hj : j < D.m) (H : D.IsSmallNonsplit p) ev :
  D.gain p / D.m - D.collisionSum p ev + (1 - chiK P.d p) / 2 * #(D.tops ∩ ev) * (D.a / D.x₁) -
  D.f * D.logB ^ 2 * (D.a / p) / D.m ≤ D.jetExponent p j ev := by
  obtain ⟨o, _, hs⟩ := q.1.two_le, D.hasLogUpper_of_le (D.n_mono hj), lowColumns_lowBoxes_bounds hj
  rw [gain, mul_div_cancel_left₀ _ (mod_cast by lia), jetExponent, mul_div_assoc]; set N :=
    boxes D.κ _
  generalize v : (D.a / p / _ : ℝ) = u; have z : N = #D.tops * D.a + ∑ σ, (D.lowBoxes j σ : ℝ) := by
    simp [N, lowBoxes, sum_ite, filter_ne', (by grind [n] : 1 < D.n (j + 1))]; simp [κ]
  have ⟨h3, _⟩ : D.x ^ 60 ≤ u ∧ 0 ≤ u := by grw [← v, H.1]; use D.le_of_hasLogBound; bound
  grw [h3.trans' (D.le_of_hasLogBound (F := D.n _ ^ 3)), ← show 5 * p.log N + 5 ≤ D.logB ^ 2 by
    grw [N.le_succ, natLog_le_logb, logb, ← o, ← one_sub_inv_le_log_of_pos, cast_succ, z, (hs
    _).2.2.trans (D.le_of_hasLogBound (G := D.gProd)),
      card_le_univ] <;> norm_num; use D.le_of_hasLogBound]
  have := Fintype.sum_mono fun σ ↦ hasSum_le (fun e ↦ ?_) ((((hasSum_sum (s := Iic (p.log N)) fun e
    _ ↦ hasSum_ite_eq e (ite (Odd e ∨ p =
    P.d) (couplingCount p D.κ (D.n (j + 1)) ev σ (D.placeOfInt (-p ^ e) * σ)
    e) 0 - 4 * u)).add ((D.summable_localAsk H.2 D.a σ).hasSum.mul_left (ite (σ ∈ D.tops) 1 0))).add
    ((D.summable_localAsk H.2 (D.nominalWeight σ) σ).hasSum.mul_left ↑D.k)).add (hasSum_ite_eq 1
    (ite (σ ∈ D.tops ∩ ev) (D.a / D.x₁) 0))) ((hasSum_live_inv_pow H.2 (D.κ σ 1 + D.lowBoxes j
    σ)).add ((hasSum_live_inv_pow H.2 D.a).summable.indicator {e | D.IsCollision p ev σ e}).hasSum)
  have : 0 ≤ 4 * D.f * u * (p.log N + 1) + D.collisionSum p ev := by rw [collisionSum]; positivity
  obtain ⟨_, h⟩ | ⟨_, h | h⟩ := chiK_cases P.d p <;> simp +contextual [sum_filter, ← mul_sum,
    IsCollision, collisionSum, h, forcedPart, κ, z, @sum_comm ℕ, localAsk, ← sum_mul, -mem_inter,
    Set.indicator, IsSmallNonsplit] at * <;> linarith
  simp [couplingCount, ↓← lowColumns.eq_1, ↓← lowBoxes.eq_1, add_div, ite_div, ite_and,
    posPart_eq_ite, κ, IsCollision, Set.indicator]; wlog h : Odd e ∨ p = P.d; grind; set σ' :=
    _ * σ; cases' e with e
  simp at h; have h6 τ := (hs τ).2.1.trans (D.le_of_hasLogBound.trans (h ▸ v.le))
  have (τ) (_ : τ ∉ D.thick) :=
    (hs τ).2.2.trans (.trans (by simpa [nominalWeight, *] using D.le_of_hasLogBound) v.le)
  grind +splitImp [tops, placeClass_of_thick, @ne_d_of_placeClass_eq _ D p 0 σ]
  have : e = 0 → D.a / D.x₁ ≤ D.a / p ^ e.succ := by bound
  have d := monotone_div_right_of_nonneg (α := ℝ) (p ^ e.succ).cast_nonneg
  grind [d D.a.cast_nonneg, min_le_left, min_le_right, nominalWeight_nonneg, d (hs σ).1,
    D.nominalWeight_mem_Icc σ', d (D.lowBoxes j σ).cast_nonneg,
    (by bound : 0 ≤ D.k * D.nominalWeight σ'), show D.lowColumns _ σ /
    p ^ e.succ ≤ u by grw [← v, (hs σ).2.1, div_right_comm]; gcongr; use D.le_of_hasLogBound; bound]
lemma Data.IsMarked.sum_lowColumns_le (hj : j < D.m) [PadicPlace p] (H :
  IsMarked Λ) : #Λ * D.deltaP p + D.ceilLogM p * ∑ σ
  ∈ evenPlaces Λ, D.lowColumns j σ ≤ D.loss p / D.m + #(D.tops ∩ evenPlaces Λ) * (D.a / D.x₁) := by
  rcases D.hasLogUpper_of_le_of_nonneg H.4.1.le, q.1.pos
  grw [cast_sum, mul_sum, sum_le_sum (g := fun σ ↦ D.a / p / D.m + ite (σ ∈ D.tops)
    (D.a / D.x₁) 0) fun σ a ↦ ?_, ← le_loss, H.card_le, deltaP]
  simp [inter_comm, ← add_assoc, field]; use D.le_of_hasLogBound
  simp at a; grw [(lowColumns_lowBoxes_bounds hj σ).2.1, nominalWeight,
    ite_eq_right (H.notMem_thick σ (.inl a))]
  obtain ⟨⟨_, _, _, e⟩, c | c⟩ := H.2 ⟨_, a⟩, le_total p D.m
  grw [c]; split <;> simpa using D.le_of_hasLogBound
  rw [ceilLogM, clog_eq_one D.nat_le_of_hasLogBound c] at *; grw [ite_eq_left (by
    grind [inducedPlace_eq_or_star_iff, H.3, tops, one_pow, o₀, orderOf_eq_one_iff]),
    add_comm]; simpa using D.le_of_hasLogBound
end
seal Finset.univ Finset.sum Finset.prod
open Module Finset Fintype Matrix MvPolynomial NumberField Representation Space Submodule Valued
variable {E : Type} (n : Type) [Field E] [CMType E] [WeilData E] [Fintype n] (α : AutChar E) (c :
  NumberField.InfinitePlace E → ℕ) (𝔪 : Modulus E) (ψ : (w : FinPlace E) → MulChar (ResField w) ℂ)
noncomputable def detKernel Ψ :=
  (modKernelI (stdSpace E n) α α 𝔪 Ψ (∏ τ, letterMinor τ id id ^ c τ) 1 ·)
noncomputable def detPeriod := stdClassSum (Kf ..) (detKernel n α c 𝔪 (𝔪.charOfTamePart ψ ·.det))
variable {n α c 𝔪 ψ}
lemma detKernel_embFin_mul [h : α.HasWeight (-c ·) ψ] Ψ γ g : detKernel n α c 𝔪 Ψ (stdEmbFin γ * g)
  = detKernel n α c 𝔪 Ψ g := by simpa [stackedDetProd, stackedDet, ← det_submatrix_equiv_self (.symm
  (.emptySum ..)), ← modKernelBilin_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply,
  prod_ne_zero_iff] using! (twoSidedSubst_stackedDetProd
  (ι := (Fin <| c ·)) (.emptySum Empty n) 0 .. ▸ modKernel_embFin_mul h h _ _ _ 1 .. :)
lemma detPeriod_eq_stdClassSum_sum [h : α.HasWeight (-c ·) ψ] (hψ : ∀ w ∉ 𝔪.places, ψ w = 1) :
    detPeriod n α c 𝔪 ψ = stdClassSum (Kf E n) fun g ↦ ∑ y : GL n 𝔪.ResRing,
  detKernel n α c 𝔪 (Pi.single 1 1) (g * liftMod y) := by rw [detPeriod, pi_eq_sum_univ fun _ ↦ _,
  ← sum_of_injective _ Units.val_injective _ _ _ (by tauto)] <;> simp +contextual +unfoldPartialApp
  [detKernel, ← modKernelBilin_apply, ↓modKernel_mul_Kf_right, h.apply_det_eq_charOfTamePart hψ,
  -coe_units_inv, ← IsUnit.eq_1, MulChar.map_nonunit, isUnit_iff_isUnit_det]
open Fint in
lemma detPeriod_insert {𝔪' : Modulus E} [h : α.HasWeight (-c ·) ψ] (hψ : ∀ w ∉ 𝔪.places, ψ w = 1) v
  (hv : v ∉ 𝔪.places) (hS : 𝔪'.places = insert v 𝔪.places) : detPeriod n α c 𝔪' ψ = trivialHecke v.q
  (card n) (α.frobValue n v)⁻¹ * detPeriod n α c 𝔪 ψ := have d := hS ▸ 𝔪'.disjoint_places_star
  have hw := d.notMem_of_mem_left (by simp) ∘ .inl
  have u := h.charUnramifiedAt (hψ v hv) (by simp_all)
  have l 𝔪 := by simpa [← RingHom.mapMatrix_apply, ← RingHom.map_det] using
    (liftFn_eq_residueDatum (𝔪 := 𝔪) Subtype.range_coe.symm fun S ↦ ∏ᶠ w, ψ _ (det (n := n) (S w)))
  have H P := (sum_heckePolyCoeff_smul_pairWeil u u hw (f := modDatum (stdSpace ..) (stdSpace E n) 𝔪
    (𝔪.charOfTamePart ψ ·.det) P) (by grind [modDatum, projOn_integrated, projOn_name_vacElem])
    _).1.trans (c := modDatum _ _ _ (𝔪'.charOfTamePart ψ ·.det) P) (by
    simp [modDatum, integrated_name]
    erw [inv_mul_cancel₀ (by simp [AutChar.frobValue, HeckeChar.atUnif]),
      ← name_union (S := {v}) _ d (by simpa)
      (hΨ := Set.range_const (ι := Unit) ▸ isSchwartzBruhat_residueDatum _ (by simpa)), l, l]
    simp +unfoldPartialApp [residueDatum, hS, Pi.mul_def, ← ite_and, finprod_eq_prod_of_fintype,
      reindex_equiv ((Set.equivOfEq hS).trans (Set.subtypeInsertEquivOption hv)).symm]
    congr!; bound; show _ = ψ v (det (.map _ (residueOrZero ∘ evalAt v)))
    erw [hψ v hv, MulChar.trivial_apply]
    split <;> simp_all [rank_of_isUnit, card_sub_rank, prod_eq_zero (i := 0), zero_lt_iff,
      coe_mulVecLin, LinearMap.ker_eq_bot, mulVec_injective_iff_isUnit, ↓← isUnit_iff_isUnit_det])
  have s {𝔪} (u : ∀ w ∉ 𝔪.places, ψ w = 1) : Kf .. ≤ rightStab
    (detKernel n α c 𝔪 (𝔪.charOfTamePart ψ ·.det)) := Subtype.forall'.2 (by simp [detKernel,
    modKernel_mul_Kf_right, Pi.smul_def, h.apply_det_eq_charOfTamePart u, ←map_mul, ← det_mul])
  by rw [detPeriod, stdClassSum, ← classIntegral_eq_classSum (s (by simp_all)),
    classIntegral_sum univ (.mulLeft <| heckePolyCoeff (α.frobValue n v)⁻¹ ·)
    (atSplit hw <| transposeGL <| basicCosetRep ·) fun _ ↦ ⟨Set.forall_mem_range.2
    (detKernel_embFin_mul _), Subgroup.isOpen_mono (s hψ) isOpen_Kf⟩] <;> simp [detKernel,
    modKernel, ← H, pairTheta, rep_apply_apply, detPeriod, classIntegral_eq_classSum (s hψ),
    ← sum_mul, ← card_ResField, by simpa using q_binomial_submodule n (ResField v) ⊤]
variable {E n : Type} [Field E] [CMType E] [Fintype n] {κ} {e :
  InfinitePlace E → ℤ} {P} (D : Data P) {j : ℕ} (w :
  D.piPlaces) {K} [IsLevel (E := E) (n := n) K] (ϑ)
def IsShort B (φ : AlgForm n κ e) := (∀ p [Fact p.Prime] [PadicPlace p], GaugeLe 1 1 φ) ∧
  ∀ (σ : ℂ ≃+* ℂ) g, weylNormSq (σ ∘ φ.1 g) ≤ B
lemma IsShort.sub_translate {B k} {φ : AlgForm n κ e} (h : IsShort B φ) (hk : k ∈ Kf ..) : IsShort
  (4 * B) (φ - algFormRep _ _ k φ) := ⟨fun p _ _ ↦ ((integralFormsAt ⊤ 1).sub_mem ⟨⟨⟩, h.1 p⟩
  ⟨⟨⟩, fun g ↦ by simpa [weylGauge_mul, Kf_le_localLevel hk] using h.1 p (g * k)⟩).2, fun σ g ↦ by
  have := weylNormSq_nonneg (σ ∘ (φ.1 g + φ.1 (g * k)))
  simp [weylNormSq, mulVec_sub] at *
  linarith! [h.2 σ g, h.2 σ (g * k)]⟩
open Norms.L2Operator in
lemma span_isShort_eq_top [Nonempty n] (free : ∀ g, classAut stdRatPoints K g = ⊥) {N M} [NeZero N]
  (h : ↑N ∈ differentIdeal ℤ (𝓞 E)) (hM : Fintype.card n * Fintype.card (InfinitePlace E) + boxes κ
  (Fintype.card n) ≤ M) {B} (hB : (shortBasisConst E n N : ℝ) ^ (6 * M) ≤ B) :
  span ℂ {φ : levelSpace (algFormRep κ e) K | IsShort B φ.1} =
  ⊤ := top_unique fun φ _ ↦ (freeLevelEquiv _ _ 1 free).3 φ ▸ sum_mem fun c _ ↦ by
  choose Y b hZ using exists_short_basis_stdSpace (n := n) h
  let A {R} [NormedField R] (f : ℂ →+* R) := (∏ τ, ((Y (c.out ^ e τ)).map
    (weightEmbedding f τ)).det) • weylRep κ 0 ((Y c.out).map <| weightEmbedding f ·)
  use (ker_mkQ _).le ((A (.id _)).mulVecLin.range_le_ker_iff (g := mkQ _ ∘ₗ deltaForm ..).2
    (PolyRep.ext_weylEval 0 (fun y o _ ↦ (ker_mkQ _).ge (subset_span ?_))
    ((Set.Ioi_infinite 0).preimage (⟨_, Complex.isPrimitiveRoot_exp · ·.ne' |>.eq_orderOf.symm⟩)))
    (mulVec_surjective_iff_isUnit.2 (((Group.isUnit _).map _).smul _) _))
  have m {R} [NormedField R] (f : ℂ →+* R) : f ∘ (A (.id _) *ᵥ weylEval n κ y) =
    A f *ᵥ weylEval n κ (f ∘ y)
    ∧ ∀ x, ‖f _‖ ≤ 1 := ⟨by simp [funext_iff, A, Units.smul_def, f.map_det, weylRep_map, weylEval,
    mulVec_apply_eq_sum, map_eval], fun x ↦ (f.isOfFinOrder (by simpa using o x)).norm_eq_one.le⟩
  use fun p _ _ g ↦ ?_, fun σ g ↦ ?_
  grw [mul_one, weylGauge_deltaForm_le (by simp)]; erw [weylGauge, (m _).1]; simp [weylRep,
    Units.smul_def, A,
    -map_inv, norm_smul, ← mul_assoc, ← prod_mul_distrib, ← map_zpow, -coe_units_zpow]
  grw [Finset.prod_le_one₀ (by bound) fun τ ↦ ?_, norm_schur_mulVec_le .refl fun τ ↦ by
    simpa [mul_apply] using (norm_adeleExtension_le_one (weightEmbedding ιₚ τ) <| b c.out · ·)]
  simpa [pi_norm_le_iff_of_nonneg, weylEval, ← map_nablaBasis (Int.castRingHom ℂ_[p]),
    -map_nablaBasis] using! fun _ ↦ eval₂_mem (s := NormedField.valuation.integer) (by simp) (m _).2
  simpa [mul_comm, ↓RingHom.map_det, Function.comp_def, -coe_units_zpow] using!
    norm_adeleExtension_le_one (weightEmbedding ιₚ τ) (b _).det_mem
  set R := (shortBasisConst E n N : ℝ)
  have r : Fintype.card n ≤ R :=
    Nat.mono_cast (Nat.le_of_dvd Fin.pos' (by simp [sq, Dvd.dvd.mul_left]))
  have : 1 ≤ R := Nat.one_le_cast.2 Fin.pos'
  choose ρ hρ H using weylNormSq_schur_le (κ := κ) .refl (PolyRep.squarePart (PolyRep.rowPos n) _)
  grw [weylNormSq_deltaForm_le (by simp)]; erw [free, (m σ.toRingHom).1, smul_mulVec,
    weylNormSq_smul]; simp [weylRep]
  grw [schur_mulVec_weylEval_of_detExp_zero .refl (by simp), ← PolyRep.schur_squarePart_mulVec, H,
    PolyRep.weylNormSq_weylEval_permArray, ← hB, ← hM]
  simp [pow_add, ← FitsRanks.refl.sum_diagramWeight_eq_boxes, ← prod_pow_eq_pow_sum, pow_mul,
    ← prod_pow, prod_prod_type, prod_range]
  erw [← prod_const]; gcongr
  grw [norm_det_le_norm_pow, l2_opNorm_le_of_apply (by apply hZ _ (weightEmbedding σ _)), ← sq,
    r]; linear_combination
  grw (transparency := default) [(NNReal.coe_mono (single_le_sum_of_canonicallyOrdered (by
    simp))).trans (hρ _), norm_sum_le, norm_mul_le, hZ _ (weightEmbedding σ _), (m σ.toRingHom).2]
  simp [field]; bound
noncomputable def algFormCentralRep {J χ} := subrepresentation ((algFormRep ..).comp (scalarFin n))
    (levelSpace (algFormRep κ e) J χ) fun _ _ ↦
  (map_mem_levelSpace_of_commute · fun _ ↦ (commute_scalarFin _).symm.map _)
namespace Data
lemma not_isChosen_of_N_mem {w} : ↑D.N ∈ w.1 → ¬D.IsChosen w ∧ ¬D.IsChosen (star w) := by
  grind [isChosen_iff, (D.nat_lt_of_hasLogBound.ne : D.g _ ≠ D.N), q_eq_g,
    P.q_eq_of_modEq_one D.N_modEq_one, q_star]
lemma mem_columnLevel {k} : k ∈ D.columnLevel j ↔ k ∈ chosenLevel ∧ ∀ w ∈ D.piPlaces, ∀ b,
  v (((k.atPlace w).1 - 1) (.inr ()) b) ≤ .exp
  (-1) := and_congr_right fun h ↦ (and_iff_right (levelOf_le_Kf h)).trans ((forall₂_congr fun _ _ ↦
  sub_one_mem_span_iff_atPlace (levelOf_le_Kf h)).trans (by grind [mem_piPlaces, intValuation_pi]))
lemma mem_chosenLevel_of_supportedOn {S} (h : ∀ w ∈ S, ↑D.N ∈ w.1) :
    Kf .. ⊓ Gf.supportedOn (D.X j) S ≤ D.chosenLevel := (inf_supportedOn_le_principalLevel
  (D.not_isChosen_of_N_mem <| h · ·)).trans (D.principalLevel_le_chosenLevel dvd_rfl)
lemma exists_centralGen : ∃ ν : unitary _, (ν.1 ∈ Ô _ ∧ ∀ u ≠ w.1, star u ≠ w → ν.1 u = 1) ∧ ∀ i,
  v (ν.1 w ^ i - 1) < 1 → D.N - 1 ∣ i := ((LocInt _).surjective_unitGroupToResidueFieldUnits
  |>.exists.1 (@IsCyclic.exists_ofOrder_eq_natCard (ResField w.1)ˣ _ _)).elim fun x h ↦
  ⟨divStar (locIdele w x), by
  simp +contextual [coe_divStar, ← map_inv, mem_Ô, ← card_ResField, mem_idelesUnitOff.1
    (locIdele_mem_idelesUnitOff (S := ∅) _), (v.mem_unitGroup_iff ..).1 x.2,
    ← D.isSplitLevel_piPlaces.2 w, ← Nat.card_units,
    ← h, (ne_of_mem_of_not_mem _ (D.isSplitLevel_piPlaces.star_notMem _ w.2)).symm]
  use fun i b ↦ orderOf_dvd_of_pow_eq_one (Units.ext (residue_eq_iff_valuation_sub_lt_one.2 b))⟩
noncomputable def centralGen := (D.exists_centralGen w).choose
lemma scalarFin_centralGen_mem n [Fintype n] : scalarFin n (D.centralGen w) ∈ maxCompactAt n w := by
  have := (D.exists_centralGen w).choose_spec.1
  simp_all [mem_Kf, Units.ext_iff, centralGen]; simp_all [scalarFin, diagonal_apply, ite_mem]
noncomputable def centralRep : Representation ℂ (unitary (𝔸f D.E)) D.Column := algFormCentralRep
noncomputable def ramifyingOp s :=
  D.centralRep.asAlgebraHom (∏ w ∈ s, (1 - .of _ _ (D.centralGen w)))
noncomputable def ramifiedColumns := (D.ramifyingOp univ).range
lemma exists_eq_sub_centralGen {φ} : φ ∈ D.ramifiedColumns → ∃ ψ : D.Column, φ.1 =
  ψ.1 - algFormRep _ _ (scalarFin _ (D.centralGen w)) ψ := fun ⟨_, h⟩ ↦
  ⟨_, by simp [← h, ramifyingOp, ↓prod_eq_mul_prod_compl w]; rfl⟩
lemma sum_height_mul_kappa_le τ : ∑ h ∈ range (Fintype.card (D.X 0)), h * D.κ τ h ≤ D.a := by
  grind [sum_eq_ite 1, card_X, n, κ]
lemma finrank_ker_one_sub_centralGen_le : finrank ℂ (1 - D.centralRep (D.centralGen w)).ker ≤
  (D.N - 1 : ℝ)⁻¹ * finrank ℂ D.Column :=
  let K := D.columnLevel 0 ⊔ .zpowers (scalarFin _ (D.centralGen w))
  have a : K ≤ _ := sup_le inf_le_left (by simp [D.mem_chosenLevel_of_supportedOn _
    (scalarFin_centralGen_mem ..), D.isSplitLevel_piPlaces.natCast_mem])
  have :=
    IsLevel.mk (a.trans levelOf_le_Kf) (Subgroup.isOpen_mono le_sup_left D.isLevel_columnLevel.2)
  (Subgroup.exists_pow_mem_of_relIndex_ne_zero (this.isCompact.relIndex_ne_zero
    D.isLevel_columnLevel.2) (Subgroup.zpowers_le.1 le_sup_right)).elim fun i ⟨o, b, e, _⟩ ↦ by
  grw [le_inv_mul_iff₀ (by simp [Fact.out]), ← Nat.cast_pred Fin.pos', ← finrank_map_subtype_eq,
    finrank_mono (t := levelSpace (smoothFormRep ..) K)
    (map_le_iff_le_comap.2 fun v h k ↦ by ext; simp [sup_le (c := rightStab v.1) (fun _ k ↦
    (by simpa using levelSpace_smoothFormRep_apply v.2 1 · ⟨_, k⟩)) (Subgroup.zpowers_le.2
    (congr($(sub_eq_zero.1 h).1.1 ·).symm)) k.2 _]), Nat.le_of_dvd o
    ((exists_centralGen ..).choose_spec.2 i (by simpa [← map_pow] using!
    ((D.mem_columnLevel.1 e).2 _ w.2 (.inr ())).trans_lt (by decide))), b]
  rify [finrank_levelSpace_smoothFormRep, classAut_columnLevel_eq_bot, card_classes_eq_classSum,
    classSum_one_of_le (K := K) le_sup_left, implies_true,
    D.classAut_eq_bot_of_le_chosenLevel a (by grind [card_X, n]), mul_assoc, le_rfl]
lemma ramifyingOp_finrank_comap_and_short s p : finrank ℂ (Submodule.comap (D.ramifyingOp s) p) ≤
  finrank ℂ p + #s * (D.N - 1 : ℝ)⁻¹ *
  finrank ℂ D.Column ∧ ∀ B φ, IsShort B φ.1 → IsShort (4 ^ #s * B) (D.ramifyingOp s φ).1 := by
  induction' s using cons_induction with w s _ a generalizing p
  rw [(by simp [ramifyingOp] : D.ramifyingOp ∅ = 1)]; simp; rfl
  erw [card_cons, ramifyingOp, prod_cons, map_mul, map_sub, map_one, asAlgebraHom_of,
    p.comap_comp (D.ramifyingOp s)]
  use by grw [(a _).1, (by simpa [↓← finrank_eq_rank, ← Nat.cast_add] using
    (1 - D.centralRep (D.centralGen w)).lift_rank_comap_le :), Nat.cast_add,
    finrank_ker_one_sub_centralGen_le]; grind, by simpa [pow_succ', mul_assoc] using!
    ((a p).2 · · · |>.sub_translate (scalarFin_centralGen_mem ..).1)
lemma span_short_ramifiedColumns : span ℂ {φ : D.ramifiedColumns | IsShort D.budget.exp φ.1.1} =
  ⊤ := comap_injective_of_surjective (D.ramifyingOp _).surjective_rangeRestrict (eq_top_mono
  (span_le.2 fun φ h ↦ subset_span (by simpa [card_piPlaces, mul_div_cancel₀] using!
  (D.ramifyingOp_finrank_comap_and_short univ ⊥).2 _ φ h))
  (span_isShort_eq_top D.classAut_columnLevel_eq_bot P.cycloConductor_mem_different (by grw [boxes,
  sum_height_mul_kappa_le]) (B := _ / 4 ^ D.f)
  (by simpa [le_div_iff₀', ↓card_X, n] using Real.le_exp_of_log_le D.le_of_hasLogBound)))
variable [Fact j.Prime] {Ψ : Data.Translations (P := P) (D := D) →₀ ℂ} (D' : Data P) {D : Data P}
  {p : ℕ} [Fact p.Prime] [PadicPlace p] {ϑ : D.Twist} {Ψ : Data.Translations (P := P) (D := D) →₀ ℂ}
noncomputable def pairTranslates (v : ∀ j, (homX j).finitePart) i :=
  translateSum _ _ D.piPlaces D.N _ (v (2 * i) ⊗ₜ v _)
def admissibleTranslations q := {t : D.Translations | ∀ k, t k ∈ translations _ q (star D.piGBar)}
structure IsGoodDatum (ϑ : D.Twist) (Ψ) extends IsAdmissibleCoeffs
  (admissibleTranslations (ϑ.levelNorm * D.N)) ϑ.levelNorm 1 (ϑ.Q = ∅) (.exp (D.x ^ 60)) Ψ where
  joint_invariant : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support (Ψ · • .id) translateDatum
  chain_at_N φ : chainComb ϑ Ψ translateDatum _ φ = Ψ.sum fun x ↦ (· • chain₂ (D.liftKernel ϑ)
    (D.pairTranslates (projOnFinPart _ D.piPlaces <| D.translateDatum x ·)) (D.ϱ + 1) φ)
lemma notMem_piPlaces_of_ne (hp : j ≠ D'.N) {w} (hw : ↑j ∈ w.1) : ↑D'.N ∉ w.1 ∧
  star w ∉ D'.piPlaces := by simp_all [(D'.isSplitLevel_piPlaces.natCast_mem _).mt,
  Nat.prime_dvd_prime_iff_eq, Fact.out, w.natCast_mem_iff_dvd hw]
lemma mem_integralAfter {q x j δ S} (hx : x ∈ admissibleTranslations q) (h : ∀ w, S w → ↑q ∉ w.1 ∧
  (δ = D'.piG ∨ ¬D'.IsChosen
  (star w))) : x j ∈ Parameters.integralAfter δ S := fun i w a ↦ (hx j i w (h w a).1).trans' (by
  cases (h w a).2 <;> simp_all [IsChosen, w.valuation_eq_one_iff_notMem.2]
  rfl; exact mul_le_of_le_one_left' (w.valuation_le_one (algebraMap _ _ δ)))
lemma projOn_translateDatum (D : Data P) {x j S} (h :
  x j ∈ Parameters.integralAfter 1 (· ∈ Set.conjClosure S)) : projOn _ S (translateDatum x
  j).1 = (D.translateDatum x j).1 := by simp_all [translateDatum, projOn_finHeisOp,
  Parameters.intVacuum, mem_integralBox, idem_mul_mem_Ô, Parameters.integralAfter]
lemma exists_chain_eq_sum {Φ} (H : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support (Ψ · • .id) Φ)
  (N : ∀ _, _ → _ → ℝ) {r} (hr : ∀ j, 0 ≤ r j) (hs : ∀ x ∈ Ψ.support, ∀ j < D.m, ∀ g h v,
  N _ h ((D.liftKernel ϑ j).jetMatrix ((D.liftKernel ϑ j).ω (g, h) (Φ x j)) v) ≤ r j * N j g v) {φ :
  D.Column} {B} (hB : ∀ g, N 0 g (φ.1.1 g) ≤ B) g : ∃ β : Fin (∏ j ∈ range D.m, .card (StdClasses
  (D.columnLevel j))) → _ →ₗ[ℂ] _, (∀ i, ∀ x ∈ Ψ.support, N _ g (β i (TensorChain.pure (Φ x) _)) ≤
  (range D.m).prod r * B) ∧ ∑ i, ∑ x ∈ Ψ.support, Ψ x • β i (TensorChain.pure (Φ x) D.m) =
  (chainComb ϑ Ψ Φ D.m φ).1 g := by simpa [Finsupp.sum, ↓Set.mem_nsmul_iff_sum,
  Set.image, Classical.skolem, forall_and, ← _root_.funext_iff] using!
  (H.sum_chain_mem_nsmul _ (fun j h ↦ D.classAut_eq_bot_of_le_chosenLevel
  inf_le_left (by grind [card_X, D.n_mono h.le])) φ.2 (fun j ↦ (N j · · ≤ (range j).prod r * B))
  (by intros; grw [hs, prod_range_succ_comm, mul_assoc] <;> bound) (by simpa) (Set.mapsTo_image ..))
lemma IsGoodDatum.translateDatum_mem_standardData (H : IsGoodDatum ϑ Ψ) (hQ : p.Coprime ϑ.levelNorm)
  (hp : p ≠ D.N) {x} (hx : x ∈ Ψ.support) j {δ} (h : δ = D.piG ∨ ¬p ∣ D.gProd) :
  (translateDatum x j).1 ∈ Parameters.standardData _ δ := subset_span ⟨_, D.mem_integralAfter
  (H.support_subset x hx) fun w _ ↦ by simp_all [← piGBar_mul_star, IsChosen,
  ← w.natCast_mem_iff_dvd, w.2.mul_mem_iff_mem_or_mem, D.notMem_piPlaces_of_ne hp,
  or_and_left, -Nat.cast_prod, w.2.notMem_of_isCoprime_of_mem hQ.cast], rfl⟩
lemma IsGoodDatum.gaugeLe_chain (H : IsGoodDatum ϑ Ψ) (hQ : p.Coprime ϑ.levelNorm) (t : ∀ _,
  End ℂ _) (ht : ∀ᵉ (j) (x ∈ Ψ.support) (a : D.columnLevel j) (b ∈ D.columnLevel _),
  (D.liftKernel ϑ j).ω (a, b) (t j (translateDatum x j)) = t j ((D.liftKernel ϑ j).ω (a,
  b) (translateDatum x j))) (d : ∀ _, _) {r : ℕ → ℝ} (h : ∀ᵉ (x ∈ Ψ.support) (j < D.m),
  t j (translateDatum x j) ∈ (D.liftKernel ϑ j).raises (d j) (d _) (p ^ r j)) {φ : D.Column} (hφ :
  GaugeLe (d 0) 1 φ.1) : GaugeLe (d _) (p ^ ∑ j ∈ .range D.m,
  r j) (chainComb ϑ Ψ (fun x j ↦ t j (translateDatum x j)) D.m φ) := (exists_chain_eq_sum
  (by simpa +contextual [*] using H.joint_invariant · · <| · ∘ₗ TensorChain.map ..)
  (fun j g ↦ weylGauge _ (D.lastEntry j) (g * d j)) (by simp) h hφ · |>.rec fun _ b ↦ b.2 ▸ by
    repeat grw [weylGauge_sum_le]; bound; intros
    grw [weylGauge_smul, b.1, ← one_nsmul (Ψ _), nsmul_eq_mul, H.integral _ _ hQ] <;>
      simp [Real.rpow_nonneg, Real.rpow_sum_of_pos, NeZero.pos, *])
lemma norm_star_piG_le_one :
    ‖ιₚ (star D.piG)‖ ≤ 1 := norm_le_one_of_isIntegral (ιₚ.comp (starRingEnd _)) D.piG.2.algebraMap
