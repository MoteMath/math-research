import New.Columns.TwistedHeckeType
import New.Columns.SizeEstimates
import New.Rows.RowVolume
import New.Seesaw.SeesawTheorem
import New.Exchange.CrudeRows
import New.Selmer.FitTwistsExist
import New.Rows.LiftVolumeHeight
section
namespace Data
open Finset ZMod Nat Columns Parameters RingHom Module Real IsLocalization AtPrime
theorem IsMarked.hasType_markOperator {P p} {D : Data P} [h₀ : Fact p.Prime] [PadicPlace p] {Λ}
    (hΛ : D.IsMarked Λ) s {l} (hl : l ∈ Λ) :
  HasType ↑p D.integralColumns s (hΛ.markOperator ⟨l, hl⟩) ((128 * D.markExponent l *
  (D.logB / (D.m * p)) + 1 / D.x ^ 14 * s + D.x ^ 40) * finrank ℂ D.Column) := by
  obtain ⟨hL, -, hd, hx⟩ := hΛ.2 ⟨l, hl⟩; set d := D.o₀ p; let c := D.placeOfInt (-p) ^ d
  obtain ⟨hs, ⟨τ, _, e⟩, ⟨z, hz⟩, hm, h', _, _, _, _, hN, hu : ¬IsUnit (p : embValRing), hW, r0⟩ :=
    (hΛ.2 ⟨l, hl⟩).m_dvd_orderOf, hΛ.3 l hl, (Complex.isSquare p).exists_sq, hΛ.p_mem hl,
    hΛ.star_ne hl, P.thirteen_le_of_chiK_ne_one h₀.1 (by lia), NeZero.of_pos (orderOf_pos c),
    D.hasLogUpper_of_le hx, D.hasLogUpper_of_le (orderOf_le_card_univ
    (x := c)), (by grind [o₀, orderOf_map_dvd, orderOf_pow_of_dvd, Nat.mul_div_cancel'] : orderOf
    (D.placeOfInt (-p)) = d * orderOf c), (Valuation.mem_maximalIdeal_iff ..).2 (by simpa using!
    norm_p_lt_one), l.valuationSubringAtPrime_eq_valuationSubring (K := D.E), hd.pos.trans_le hx
  let t (s : ZMod (orderOf c)) := c ^ s.val * τ; have ht s : t (s + 1) =
    D.placeOfInt (-p ^ d) * t s := by simp [t, ← hd.neg_pow, ← placeOfInt_pow, c, _root_.pow_succ',
    val_add, val_one_eq_one_mod, mul_assoc]
  have hi : t.Injective := fun _ _ ↦ by simp [t, pow_inj_mod, ← natCast_eq_natCast_iff']
  have hS σ : σ ∈ Set.range t ↔ σ ∈ D.tops ∧ (inducedPlace σ = l ∨ inducedPlace σ = star l) := by
    simp [t, natCast_zmod_surjective.exists, ← e, inducedPlace_eq_or_star_iff, hL]; simp [c,
      ← pow_mul]
    grind [o₀, tops, =_ orderOf_dvd_iff_pow_eq_one, dvd_def]
  have := CharP.quotient _ p hu; let v s := inducedPlace (t s) == l; have w s :=
    ((hS _).1 ⟨s, rfl⟩).2
  let g s : l.valuationSubringAtPrime D.E →+* embValRing := .restrict (ite (v s) (Φ (t s)) (comp (Φ
    (t s)) (starRingEnd _))) _ _ fun x h ↦ (isEquiv_placeOfEmb (ιₚ.comp _)).le_one_iff_le_one.2
    <| by cases w s <;> simp_all [v, ← comp_assoc, placeOfEmb_comp_star, inducedPlace]
  let ψ s := comp (Ideal.Quotient.mk (.span {↑p})) (g s)
  let T : TwistingData .. :=
    ⟨p, d, g, v, ⟨z, by simpa [hz, pow_le_one_iff] using (p : embValRing).2⟩, h₀.1, by
    grind [le_pow], Subtype.ext hz.symm, fun s x ↦ Ideal.mk_span_eq_iff_dvd_sub.1
    (RingHom.congr_fun (ringHom_ext l.1.primeCompl (ext (star_involutive.surjective.forall.2 fun a ↦
    .trans (congrArg (Quot.mk _) (Subtype.ext (show (_ : D.E →+* ℂ) (star a) = (_ : D.E →+* ℂ)
    (galOfPlaceInt _ a) by cases w s <;> simp [v, *, ← phi_mul, @starRingEnd_apply D.E, mul_comm (t
    s), inducedPlace_neg_pow_mul_of_odd]))) ((frob_ext (by grind [chiK_eq_one_of_dvd, Fact])
    (comp (ψ s) (algebraMap ..)) d (.inr ⟨rfl, rfl⟩)).2 ⟨rfl, by simp [*]⟩ a))) : ψ _ =
    comp (iterateFrobenius ..) (ψ _)) x), by grind [star_star, inducedPlace_neg_pow_mul_of_odd],
    (card_congr (equivQuotMaximalIdeal ..).1).symm.trans ((q_eq_inert hm
    hL).trans (by rw [lcm_eq_left (D.m_even.two_dvd.trans hs), hN, pow_mul]))⟩
  have A : markExponent l =
    D.a * #{s | T.isEven s} := by rw [markExponent, ← card_image_of_injective _ hi]; congr; grind
  have e := card_add_card_compl {s | T.isEven s}
  rw [@card_equiv _ _ _ᶜ {s | T.isEven s} (.addRight 1) (by simp [T.isEven_succ]), ZMod.card] at e
  apply Columns.hasType_markOperator hΛ hl hW T hu rfl (.ofInjective t hi) hS (by tauto) A (⟨r0,
    D.nat_le_of_hasLogBound, D.le_of_hasLogBound, D.le_of_hasLogBound, e, ?_, D.le_of_hasLogBound,
    D.le_of_hasLogBound, ?_, mul_le_mul (mod_cast by nlinarith) ?_ ?_ ?_⟩ : HeckeSizes (p ^ d) ..)
  grw [← (by lia : 3 * 3 ≤ p), mul_pow, mul_pow, ← pow_add, e, ← pow_mul, le_self_add.trans_eq e]
  rify; grw [← exp_one_lt_three.le, exp_one_pow, ← hN, ← le_of_dvd (orderOf_pos _) hs,
    ← (D.le_of_hasLogBound : D.logB * 2 ≤ D.m)]; use D.lt_of_hasLogBound
  grw [p.cast_pow, hΛ.4.1,
    @le_exp_of_log_le ((_ ^ d) ^ _) (D.logB / 2) (by simpa using D.le_of_hasLogBound)]
  use D.le_of_hasLogBound
  grw (transparency := default) [← le_pow hd.pos, ← (lt_two_mul_self r0).nat_succ_le, pow_succ,
    ← p.cast_pow, ← le_pow_clog h₀.1.one_lt]
  field_simp; use D.le_of_hasLogBound; all_goals bound [D.le_m, h₀.1.pos]
end Data
end
section
open Polynomial Finset Gf Kernel Module Parameters Real Submodule
variable {P} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] {Λ} {ϑ : D.Twist} {Ψ}
  (H : Data.IsGoodDatum ϑ Ψ) (hQ : p.Coprime ϑ.levelNorm) {v} (hv : v ∈ Data.integralColumns) (hΛ :
  D.IsMarked Λ)
noncomputable def Data.liftLoss Λ j := D.ceilLogM p * ∑ σ ∈ evenPlaces Λ,
  D.lowColumns j σ - D.jetExponent p j (evenPlaces Λ)
include H hQ
lemma Data.IsGoodDatum.exists_hecke_transfer (hΛ : D.IsMarked Λ) l (hl : l ∈ Λ) (hw : _ ≠ l) j :
  ∃ c : ℕ → ℂ, (j < D.m → ∀ i, c i ∈ embValRing) ∧ ∀ x ∈
  Ψ.support, let C := chain (D.liftKernel ϑ) (translateDatum x) (j + 1); (∀ b ∈ maxCompactAt _ l,
    (D.liftKernel ϑ j).ω (1, b) (translateDatum x j) = D.translateDatum x j) ∧ ∀ φ ∈ levelSpace
    (smoothFormRep ..) (maxCompactAt _ l), ∑ i ≤ D.ceilLogM p, c i • heckeSplit (smoothFormRep ..)
    hw i (C φ) = (p : ℂ) ^ D.deltaP p • C (heckeSplit (smoothFormRep ..) hw (D.ceilLogM p) φ) := by
  obtain ⟨_, N, m, h, o⟩ := hp.1.pos, hΛ.not_dvd_gProd_mul_N, hΛ.p_mem hl,
    D.m_even.two_dvd.trans (hΛ.2 ⟨l, hl⟩).m_dvd_orderOf
  have q : l.q = (p ^ h) ^ 2 := by simp_all [q_eq_inert m (hΛ.2 ⟨l, hl⟩).1, pow_mul']
  have Q := l.2.notMem_of_isCoprime_of_mem hQ.cast m
  simp [← l.natCast_mem_iff_dvd m, ← piGBar_mul_star, l.2.mul_mem_iff_mem_or_mem] at N
  have hu {j k} : CharUnramifiedAt (rankTwist (D.chainChar ϑ j) (D.X k)).baseChange.finPart l := by
    apply D.hasWeight_liftChar.hasWeight_rankTwist.charUnramifiedAt <;> simp_all [liftTamePart, ω,
      IsChosen, TameChar.pow, ϑ.1.5, mt (D.levelNorm_mem_and_notMem_of_mem_Q ϑ ∘ .inl)]
  let y e i : ℂ := ((p ^ h) ^ D.n (j + 1) / (p ^ h) ^ D.n e) ^ i * l.q ^ i.choose 2
  have I e : ‖ιₚ ((D.chainChar ϑ e).baseChange.atUnif l)‖ ≤ 1 := by
    erw [D.hasWeight_liftChar.norm_padic_eq_prod _ _ (unitary _).one_mem.2, ← rpow_zero p,
      hΛ.sum_inducedPlace_sub_star_eq_zero e fun c w ↦
      ite (w = l) (-c) 0, rpow_sum_of_pos (by simpa)]; gcongr with τ
    have f σ : ‖adeleExtension σ (locIdele l (uniformizer l)).1‖ = ‖adeleExtension (F := ℂ_[p]) σ
      (ite (placeOfEmb σ = l) p 1)‖ := by split <;> subst_vars <;> simp [*,
      ↓norm_adeleExtension_eq_iff, ← hΛ.valuation_p hl, ← v_algebraMap_eq_valuation]
    erw [map_mul, adeleExtension_star, inducedPlace, ← placeOfEmb_comp_star]
    simp [f]; split_ifs <;> simp_all [norm_p_eq_inv, NeZero.ne]
  refine ⟨_, fun hj i ↦ ?_,
    fun x i ↦ have z {j} := D.projOn_translateDatum (j := j) (S := {l}) (D.mem_integralAfter
    (H.support_subset x i) (by simp_all [star_eq_iff_star_eq, IsChosen,
      l.2.mul_mem_iff_mem_or_mem])); ⟨by simp_all [Subtype.ext_iff, liftKernel_ω, -Prod.mk_one_one,
      pairWeil_eq_smul_of_projOn_eq {l}, hu.det_maxCompactAt_eq_one], fun φ u ↦ by
    have S e : let F := chain (D.liftKernel ϑ) (D.translateDatum x) e; F φ ∈ levelSpace
        (smoothFormRep ..) (maxCompactAt _ l) ∧ ∀ U X, X = -U * y e 1 →
        heckePolyOp (smoothFormRep ..) hw X (F φ) = (∏ a ∈ range e, ∏ k ∈ range (D.t + 1),
      (1 + .X * l.q ^ k • (p ^ h) ^ D.n j • C ⟨_, I a.succ⟩) : embValRing[X]).aeval U •
      F (heckePolyOp (smoothFormRep ..) hw (-U * y 0 1) φ) := by
      induction' e with e ih; simp [chain, compUpTo, u]
      refine (hecke_transfer_of_pairing (k := D.t + 1) (by clear * -; grind [card_X, n]) hu hu hw z
        _ _ (⟨_, rfl, lift_equivariant _ · · _ · |>.symm⟩) ih.1).imp_right fun E U _ o ↦ (E _).trans
        (.trans (congrArg _ (congrArg _ (ih.2 U _ ?_))) ?_) <;> simp [*, AutChar.frobValue, y, n,
        ↓spaceChar_rankTwist, ↓card_X, mul_smul, HeckeChar.atUnif, prod_range_succ_comm _ e]
      swap; congr! 3; all_goals field [NeZero.ne]
    simp [heckePolyOp, heckePolyEval, mul_smul, mul_pow, -map_prod] at S
    have S := congr((p ^ D.deltaP p / y 0 (D.ceilLogM p)) • $(sum_coeff_invOfUnit_smul_eq (r :=
      D.ceilLogM p) (by simp [coeff_zero_prod]) ?_ (S j.succ).2))
    simp [smul_sum, smul_smul, y, q, NeZero.ne, PowerSeries.coeff_mul_X_pow', apply_ite,
      ← sum_filter] at S ⊢
    convert S; all_goals clear * -; grind [n, (D.nat_le_of_hasLogBound : D.ceilLogM p ≤ D.k)]⟩⟩
  show ‖ιₚ _‖ ≤ 1; simp [norm_p_eq_inv]; grw [fun x : embValRing ↦
      @id (‖ιₚ x‖ ≤ 1) x.2,
    ← log_nonpos_iff (by bound)]
  simp (disch := positivity) [log_mul, log_div, (D.ceilLogM p).cast_choose_two ℝ, deltaP]
  grw [← D.n_mono hj, f, numInfPlaces, ← orderOf_le_card_univ, o,
    ← sub_nonneg]; simp; ring_nf; bound
lemma Data.IsGoodDatum.mem_raises {x} (h : x ∈ Ψ.support) j {g} (hc : ∀ l, ∃ i ≤ D.ceilLogM p,
  g l ∈ basicDoubleCoset _ _ i) : (D.liftKernel ϑ j).ω (1, atSplits hΛ.1 g) (translateDatum x j) ∈
  (D.liftKernel ϑ j).raises 1 1 (p ^ (∑ l ∈ Λ, markExponent l + liftLoss Λ j)) := by
  obtain ⟨N, p1 : 1 ≤ (p : ℝ)⟩ := hΛ.not_dvd_gProd_mul_N, mod_cast hp.1.pos; choose i hi hc using hc
  choose! J _ hJ using fun l h ↦ exists_subset_card_eq (le_card_of_mem_basicDoubleCoset (hc ⟨l, h⟩))
  choose a ha b hb e using fun l : Λ ↦ DoubleCoset.mem_doubleCoset.1
    ((basicDoubleCoset_eq (diagGL_mem_basicDoubleCoset (ϖ := .mk0 p NeZero.out)
    (by simp [← v_algebraMap_eq_valuation, ← hΛ.valuation_p l.2]) _).1).le (hJ _ l.2 ▸ hc l))
  simp [funext e, ← Pi.mul_def]
  refine Parameters.mem_raises_of_jet_bound (δ := 1) (H.translateDatum_mem_standardData hQ N.2.1 h j
    (.inr N.1)) (Kf_le_localLevel ?_) (Kf_le_localLevel ?_) (fun _ ↦ (?_ : ∀ w (f : _ →+* ℂ_[p]),
    (atPlace w _).1.map f = .diagonal fun i ↦ p ^ (ite (w ∈ Λ ∧ i ∈ J w) 1 0 - ite (⟨star w,
    i⟩ ∈ Λ.sigma J) 1 0 : ℤ)) _ _) ?_ <;> first | rwa [atSplits_mem_Kf] | clear * - hΛ p1 hJ hi
  intro w; by_cases w ∈ Λ <;> by_cases star w ∈ Λ <;> simp_all [apply_ite, hΛ.1,
    ← map_inv, atPlace_star (star_star w), atPlace_atSplits _ _ ⟨_, _⟩,
    mem_supportedOn.1 (atSplits_mem_supportedOn _ _)]
  intro _ hf _ _; obtain ⟨_, _, u, v, H⟩ := P.thetaProducts_normal_form _ hΛ.4.2
  grw [show ‖ιₚ (schurJet _ _ _ _)‖ ≤ p ^ (_ - D.jetExponent p j _) from norm_jetSeries_le hf _
    (.proj _ ∘ₗ .proj _ ∘ₗ schurJet _) (r := p ^ (_ : ℝ)) fun Θ h ↦ by
    erw [map_schurJet (isLiftWeight_kappa ..)]; simp_rw [jetExponent,
      ← card_X]; exact norm_schurJet_le (ev := evenPlaces Λ) (isLiftWeight_kappa ..).1 u v
      ((fun w h b ↦ ite (w ∈ Λ ∧ h = 1 ∧ b ∉ J w ∨ ⟨star w, b⟩ ∈ Λ.sigma J) 1 0) ∘ inducedPlace) (by
      grind [IsMarked, IsServed, chiK_cases, inducedPlace_neg_pow_mul_of_odd, star_star]) ((H _ (by
      simpa [P.norm_iota_periodFactor_eq_one _ (hΛ.4.2 ∘ P.chiK_eq_one_of_dvd Fact.out)] using
        norm_star_piG_le_one) _ h).1 _), ← zero_add (Λ.sum _),
    hΛ.sum_inducedPlace_sub_star_eq_zero (j + 1) fun c w ↦ #(J w) * ((D.n j / 2 : ℤ) - c)]
  simp (disch := positivity) only [norm_zpow, norm_p_eq_inv, inv_zpow', ← rpow_sum_of_pos, add_sub,
    markExponent, ← rpow_intCast, lastEntry, sum_filter, ← rpow_mul, placeOfEmb_comp_star,
    ← rpow_add, push_cast, ← inducedPlace.eq_1, liftLoss, lowColumns, mul_sum, card_filter,
    ← sum_ite_mem_eq D.tops, ← sum_add_distrib, Λ.sum_comm]
  clear hf H; gcongr _ ^ (∑ τ, ?_ - _)
  by_cases inducedPlace τ ∈ Λ <;> by_cases star (inducedPlace τ) ∈ Λ <;> simp_all [hΛ.1,
    add_assoc]; norm_cast
  rw [show ite .. = ∑ h ∈ range (D.n (j + 1)), ite (h = 1) (D.κ τ h) 0 by simp [κ, n]; grind]
  simp_rw [mul_sum, ← card_X, sum_range, ← sum_add_distrib]; gcongr
  split <;> simp [*, card_filter_add_card_filter_not]
  exact (sum_le_sum fun _ _ ↦ card_le_card_of_injOn _ (mem_filter_univ · |>.1)
    (tableau_col_injective ..).injOn).trans (by simp [*]; grw [hi]; lia)
lemma Data.IsGoodDatum.exists_move_markOperator j {L : List Λ} (hn : L.Nodup) : ∃ t : End ℂ _,
  ∀ x ∈ Ψ.support, let Φ := t (translateDatum x
    j); let k := D.liftKernel ϑ j; let C := chain (D.liftKernel ϑ) (translateDatum x)
      (∀ a, ∀ b ∈ Kf .., k.ω (a, b) Φ = t (k.ω (a, b) (translateDatum x j))) ∧
        (∀ y, k.lift Φ (C j y.1) = C _ ((L.map hΛ.markOperator).prod y)) ∧ ∀ g, j < D.m →
        (∀ l, ite (l ∈ L) (g l = 1) (∃ i ≤ D.ceilLogM p, g l ∈ basicDoubleCoset _ l.1 i)) →
        k.ω (1, atSplits hΛ.1 g) Φ ∈ k.raises 1 1 (p ^ ((L.map fun l ↦ (D.deltaP p -
        markExponent l.1 : ℝ)).sum + ∑ l ∈ Λ, markExponent l + liftLoss Λ j)) := by
  induction' hn with l L hl _ ih
  use 1, fun x h ↦ ⟨by simp, by tauto, fun _ _ ↦ by simpa using H.mem_raises hQ hΛ h j⟩
  choose t e f ih using ih; have z := hΛ.star_ne l.2
  choose a ha u k using H.exists_hecke_transfer hQ hΛ _ l.2 z j
  let ρ := (D.liftKernel ϑ j).ω.comp (.inr ..); let s : ℂ := p ^ markExponent l.1 / p ^ D.deltaP p
  use (∑ i ≤ D.ceilLogM p, (a i * s) • heckeSplit ρ z i) * t; intro x r
  have h :
    t (D.translateDatum x j) ∈ levelSpace ρ (maxCompactAt _ l.1) := by simp +contextual [ρ, *]
  use fun a b c ↦ ?_, fun y ↦ ?_, fun g hj hc ↦ ?_
  simp [← e x r, c, ρ, by simpa [Kernel.ω_ω] using (map_heckeSplit z · ((D.liftKernel ϑ j).ω (a, 1)) (π' := ρ) (by simp [Kernel.ω_ω]) |>.symm.trans (congrArg _ (heckeSplit_comm_of_atPlace_mem z _ h (mem_Kf_iff.1 c l))))]
  refine .trans ?_ ((k x r _ (levelSpace_anti (hΛ.maxCompactAt_le_columnLevel l.2)
    (s • (L.map hΛ.markOperator).prod y).2)).trans ?_) <;>
    simp [← f x r, smul_smul, s, NeZero.ne, mul_div_cancel₀, IsMarked.markOperator]
  congr!; exact map_heckeSplit _ _ ((D.liftKernel ϑ j).lift.flip _) (by simp [ρ,
    ← lift_equivariant _ 1])
  simp [heckeSplit, heckeGL, heckeFun_sum, smul_sum]; refine sum_mem fun i c ↦ sum_mem fun k h ↦ ?_
  simp at h; simp [h, Kernel.ω_ω, ρ, ← map_mul,
    ← @id (atSplits hΛ.1 _ = _) (MonoidHom.noncommPiCoprod_mulSingle ..)]
  refine smul_mem_raises _ (ih x r _ hj ?_) ?_
  simp [Pi.mulSingle, Function.update]; clear * - hc h hl c; grind
  simp [s, rpow_add, rpow_sub, NeZero.pos, norm_p_eq_inv]
  grw [@id (‖ιₚ (a i)‖ ≤ 1) (ha hj i)]; simp [field]
lemma Data.IsGoodDatum.gaugeLe_markOperator_pow {v} (hv : v ∈ integralColumns) :
  GaugeLe 1 (p ^ ∑ j ∈ range D.m, (#Λ * D.deltaP p + liftLoss Λ j))
  (Bμ ϑ Ψ (((Λ.attach.toList.map hΛ.markOperator).prod ^ D.m) v)) := by
  choose t A B C using (H.exists_move_markOperator hQ hΛ · Λ.attach.nodup_toList)
  have k x (h : x ∈ Ψ.support) j : chain (D.liftKernel ϑ) (fun j ↦ t j (D.translateDatum x j)) j v =
    chain (D.liftKernel ϑ) (D.translateDatum x) j (((Λ.attach.toList.map hΛ.markOperator).prod ^ j)
    v) := j.rec rfl fun j i ↦ by simp [pow_succ', ← B j x h, ← i]; rfl
  apply GaugeLe.restrictToY D hΛ.not_dvd_gProd_mul_N.2.1
  simpa +contextual [Finsupp.sum, k, -sum_add_distrib] using! H.gaugeLe_chain hQ t (by
    simp +contextual [A, (D.isLevel_columnLevel.1 ·)]) 1 (fun x h j ↦ by
    simpa [← Nat.cast_sum, sum_attach, -List.map_subtype] using C j x h 1) hv.2
omit H hQ
lemma Data.weylNormSq_Bmu_le (H : IsGoodDatum 1 Ψ) {σ : ℂ ≃+* ℂ} {φ B} (hB : ∀ g,
  weylNormSq (σ ∘ φ.1.1 g) ≤ exp B) h : weylNormSq (σ ∘ (D.Bμ .one Ψ φ).1 h) ≤
  exp (B + D.heightPerRow + 2 * ∑ p ∈ D.nonsplitPrimes, D.gain p * log p + D.budget) :=
  (D.weylNormSq_restrictToY_le σ ..).trans ((exists_chain_eq_sum H.joint_invariant (fun _ _
  y ↦ √(weylNormSq (σ ∘ y))) (by bound) (fun _ _ _ _ _ _ ↦ (P.norm_jet_le_of_isAdmissibleComb
  (.single _ ⟨⟩) ..).2 D.a.succPNat (isLiftWeight_kappa ..)) (by bound) _).elim fun f e ↦ by
  erw [← sq_sqrt (weylNormSq_nonneg (σ ∘ _)), ← e.2]
  grw [← le_branchExp, sqrt_weylNormSq_sum_le, sqrt_weylNormSq_sum_le]; simp
  grw [e.1 _ _ ‹_›, ← sum_mul, Fin.sum_const, nsmul_eq_mul, (id (H.size_le rfl σ) : Ψ.1.sum _ ≤ _),
    Nat.cast_prod, prod_range, prod_range,
    D.card_stdClasses_le_exp (principalLevel_le_columnLevel ..) (by simp [↓card_X, n])]
  simp [-sum_add_distrib, ← exp_sum, ← exp_half, ← exp_add,
    ← exp_nsmul, ↓card_X, ↓norm_map_star_piG_sq,
    ← inv_div (P.bigOmega _), -inv_div, ← sub_eq_add_neg, ← add_sub, ← jetSize.eq_1, n]
  grw [nonsplitPrimes, ← filter_filter, sum_filter_of_ne fun _ _ ↦
    mt fun h ↦ by simp [gain, forcedPart, localAsk, h],
    ← tsub_le_iff_left, sum_le_sum fun (j : Fin D.m) _ ↦ have := D.hasLogUpper_of_le j.2.le; by
    grewrite [jetSize_le_add _ (D.diagramWeight_le_by_index j.2 ..),
      D.diagramWeight_le_by_index j.2, show ite .. + _ ≤ 2 * D.a by grind [κ,
      (D.nat_le_of_hasLogBound : D.b₁ + D.b₂ + D.h₂ + D.h₂ ^ 2 ≤ D.a)], (?_ : _ - _ ≤ ↑D.m)]
    simp [← mul_sum, ↓apply_ite D.jetSize, jetSize, sum_ite, filter_ne', ← Nat.Ico_zero_eq_range]
    grw [(?_ : _ * _ + _ ≤ D.b), (?_ : D.k + _ ≤ √D.b)]
    repeat use D.le_of_hasLogBound]
  simp [heightPerRow, dirCost, jetSize, (D.le_of_hasLogBound : D.nominalWeight _ ≤ D.a), gain,
    forcedPart, κ, apply_ite, ← mul_sum, sum_mul, add_mul, mul_assoc, (filter ..).sum_comm,
    D.primeSum_eq_sum_localAsk .refl, -tsub_le_iff_right]; ring; use D.le_of_hasLogBound)
seal Space.weightRep Space.embFin
lemma Data.IsMarked.hasType_prod_markOperator_pow : HasType ↑p integralColumns (D.jetCeil p)
  ((Λ.attach.toList.map hΛ.markOperator).prod ^ D.m) (3 * D.loss p * finrank ℂ D.Column) := by
  obtain ⟨_, _, h⟩ := hp.1.pos, D.hasLogUpper_of_le_of_nonneg hΛ.4.1.le, HasType.prod
    (List.replicate D.m Λ.attach.toList).flatten fun l _ ↦ hΛ.hasType_markOperator (D.jetCeil p) l.2
  simp [← sum_mul, ← mul_assoc, ← mul_sum, ← Nat.cast_sum, sum_attach, -List.map_subtype] at h
  refine ⟨h.1, h.2.imp fun _ ↦ .imp_left (le_trans' ?_)⟩; erw [← mul_sum]
  grw [hΛ.card_le, sum_card_fiberwise_eq_card_filter, ← le_loss, jetCeil, Nat.ceil_lt_add_one]
  gcongr ?_ * _; field; use D.le_of_hasLogBound; bound
include H hQ hv
lemma Data.IsGoodDatum.gaugeLe_one (hN : p ≠ D.N) (hd : p ≠ P.d) : GaugeLe 1 1 (Bμ ϑ Ψ v) :=
  GaugeLe.restrictToY D hN
  (by simpa using H.gaugeLe_chain hQ 1 (by simp) 1 (r := 0) (fun _ a _ _ ↦ by
  simpa [((p.coprime_primes hp.1 P.4).2 hd).norm_natCast_eq_one] using! P.mem_raises_of_standardData
    (c := star D.piG) (by simp) (H.translateDatum_mem_standardData hQ hN a _ (.inl rfl))) hv.2)
lemma Data.IsGoodDatum.gaugeLe_Bmu_of_isMarked (hΛ : D.IsFullMark Λ) : GaugeLe 1 (p ^ (2 * D.loss
  p - D.gain p)) (Bμ ϑ Ψ (((Λ.attach.toList.map hΛ.markOperator).prod ^ D.m) v)) := fun g ↦ by
  grw [H.gaugeLe_markOperator_pow hQ hΛ.1 hv g]; simp_rw [liftLoss, add_sub]
  grw [hΛ.sum_lowColumns_le (by grind), ← le_jetExponent (by grind) hΛ.nonsplit,
    le_loss] <;> simp [hΛ.collisionSum_evenPlaces_eq_zero, field, hp.1.one_lt, hp.1.one_le,
    m_eq_two_mul_varrho_add_two, (hΛ.served (by grind [hΛ.2 1 (by simp [tops])])).1]; linarith
lemma Data.IsGoodDatum.gaugeLe_collisionSum (h : D.IsSmallNonsplit p) :
  GaugeLe 1 (p ^ (D.m * D.collisionSum p ∅ + D.loss p - D.gain p)) (Bμ ϑ Ψ v) := fun g ↦ .trans
  (by simpa [liftLoss] using H.gaugeLe_markOperator_pow hQ (Λ := ∅) (by grind [IsMarked]) hv g) (by
  grw [← le_jetExponent (by aesop) h, ← le_loss] <;> simp [hp.1.one_lt, hp.1.one_le, field,
    evenPlaces, m_eq_two_mul_varrho_add_two])
lemma Data.IsGoodDatum.gaugeLe_pow_jetCeil_smul (h : D.IsSmallNonsplit p) :
    GaugeLe 1 (p ^ (D.loss p - D.gain p)) (Bμ ϑ Ψ ((p : ℂ) ^ D.jetCeil p • v)) := fun g ↦ by
  erw [map_smul, weylGauge_smul]; grw [jetCeil, H.gaugeLe_collisionSum hQ hv h g,
    collisionSum_le (·.1.1), Nat.le_ceil (D.m * _ : ℝ)]
    <;> simp [norm_p_eq_inv, add_sub_assoc, rpow_add, hp.1.pos, hp.1.one_le, NeZero.ne]
omit H hQ hv
lemma Data.exists_indexDvd_Bmu_divisible {β : ℤ} (hc : β < ite (p ∈ D.nonsplitPrimes) (D.gain p) 0 -
  D.allowedLoss p + 1) : ∃ l : ℕ, l ≤ D.allowedLoss p * finrank ℂ D.Column ∧ ∃ S,
  IndexDvd integralColumns S (p ^ l) ∧ ∀ ϑ Ψ, IsGoodDatum ϑ Ψ → p.Coprime ϑ.levelNorm → ∀ φ
  ∈ S, φ ∈ D.ramifiedColumns → (p : ℂ) ^ (-β) • Bμ ϑ Ψ φ ∈ integralFormsAt ⊤ 1 := by
  have k {ϑ Ψ φ} {c : ℝ} (h : GaugeLe 1 (p ^ c) (D.Bμ ϑ Ψ φ)) (e : c ≤ -β := by linarith) :
      (p : ℂ) ^ (-β) • Bμ ϑ Ψ φ ∈ integralFormsAt ⊤ 1 := ⟨⟨⟩, fun g ↦ by
    erw [weylGauge_smul]; grw [h g, e] <;> simp [norm_p_eq_inv, rpow_neg, NeZero.one_le, NeZero.ne]⟩
  unfold allowedLoss at *; split_ifs at * with h hN <;> simp [Nat.lt_ceil, hp.1] at h; swap
  · subst hN; have : 1 ≤ D.m * D.f * D.b :=
      D.le_of_hasLogBound; peel D.exists_indexDvd_fourierOp_pow
    exact ⟨_, this.comap _ le_rfl fun _ _ ↦ mem_comap.2, fun _ _ G _ _ c r ↦
      k (D.gaugeLe_Bmu_at_N _ G r c)⟩
  have := D.hasLogUpper_of_le_of_nonneg h.1.le; have :=
    D.le_of_hasLogBound (F := 1).trans (D.le_loss p)
  obtain ⟨Λ, hΛ⟩ | s := (em _).imp (D.exists_isMarked h.1) (mul_collisionSum_le_loss h)
  · peel hΛ.hasType_prod_markOperator_pow.2; refine ⟨_, this, fun _ _ G Q _ e _ ↦ ?_⟩
    obtain ⟨_, ⟨u, U, rfl⟩, _, ⟨v, V, rfl⟩, rfl⟩ := mem_sup.1 e
    simpa using!
      add_mem (k (G.gaugeLe_Bmu_of_isMarked Q U hΛ)) (k (G.gaugeLe_pow_jetCeil_smul Q V h))
  all_goals use 0, mod_cast by bound, D.integralColumns, by simp, fun _ _ G Q φ c _ ↦ ?_
  exact k (G.gaugeLe_collisionSum Q c h)
  exact k (rpow_zero _ ▸ G.gaugeLe_one Q c hN
    (by rintro rfl; simpa [chiK] using h D.lt_of_hasLogBound)) (by norm_cast at *; lia)
end
section
open Finset Module Parameters Real Stirling Submodule LevelPlaces.LevelForm
lemma exists_rat_log_eq_and_padic_norm_eq T (g : ℕ → ℤ) (hT : ∀ l ∈ T, l.Prime) (h : ∀ l ∉ T,
  g l = 0) : ∃ q : ℚ, 0 < q ∧ log q = ∑ l ∈ T, g l * log l ∧
  ∀ l [Fact l.Prime], ‖(q : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ g l := ⟨∏ l ∈ T, l ^ g l, by
  simp (disch := grind [zpow_pos, Nat.Prime.pos, Nat.cast_pos]) [log_prod, prod_pos]
  grind [prod_eq_single, Nat.coprime_primes, _root_.Nat.Coprime.norm_natCast_eq_one, one_zpow,
    zpow_zero, Fact]⟩
variable {P} (D : Data P)
noncomputable def Data.mainHeight := D.m * D.k * D.dirCost
noncomputable def Data.mainAsk :=
  D.a * (log D.a - 1 - chowlaSelbergConst P.d - (∑ τ, (D.nominalWeight τ).log) / D.f)
noncomputable def Data.remainder := ∑ τ ∈ D.tops, (D.primeSum D.a τ - D.mainAsk)
lemma Data.heightPerRow_le : D.heightPerRow ≤ D.mainHeight - D.m * D.remainder + D.budget := by
  set w := (∑ τ, (D.nominalWeight τ).log) / D.f
  set G := (D.gProd * D.rootDisc / (2 * π)).log with hG
  have stirling : log D.a.factorial ≤ D.a * log D.a - D.a + (1 + log D.a / 2) := by
    have S := log_stirlingSeq'_antitone D.a.pred.zero_le
    simp [log_stirlingSeq_formula, log_div, log_mul, log_sqrt, (HasLogBound.pos D).ne',
      (D.nat_le_of_hasLogBound : 1 ≤ D.a)] at S
    bound
  have excess : D.jetSize D.a - D.mainAsk ≤ D.a * (w + G) + (1 + log D.a / 2) := by
    simp [jetSize, mainAsk, hG, bigOmega, log_div, log_mul, (HasLogBound.pos D).ne']
    bound
  have level : D.m * (w + G) - (G + 15 / 2 * D.logB) ≤
    log D.N := by grind [D.log_N_mem_window.1, logLevelTarget]
  calc D.heightPerRow = D.mainHeight - D.m * D.remainder + #_ *
      (D.m * (D.jetSize D.a - D.mainAsk) - D.a * log D.N) := by
        simp [heightPerRow, mainHeight, remainder]
        ring
    _ ≤ D.mainHeight - D.m * D.remainder + #D.tops * (D.m * (_ + (1 + log D.a / 2)) -
        D.a * (_ - (G + _))) := by bound
    _ = _ + #D.tops * (D.m * (1 + log D.a / 2) + D.a * (G + 15 / 2 * D.logB)) := by ring
    _ ≤ _ := add_le_add_right D.le_of_hasLogBound _
lemma Data.abs_mainHeight_add_remainder_le : |D.mainHeight| + D.m * |D.remainder| ≤
  D.b ^ 2 * D.x ^ 99 := by
  have := D.hasLogUpper_of_abs_le (by grind [c, sum_nonneg] : |chowlaSelbergConst P.d| ≤ P.c)
  have {σ y l} [h : D.HasLogUpper (D.a * (2 * y)) l] : D.HasLogUpper (D.primeSum y σ) l :=
    ⟨h.1.trans' (by grw [primeSum, abs_sum_le_sum_abs, sum_le_card_nsmul _ _ |2 *
    y|] <;> simp [posPart, abs_of_nonneg]; grw [(lambdaClass_nonneg_and_abs_le ..).2,
    ← nominalWeight_nonneg, le_abs_self y]; simp_all [field])⟩
  simpa [mainHeight, dirCost, remainder, mainAsk, jetSize] using D.le_of_hasLogBound
lemma Data.remainder_eq : D.remainder = D.a * (#D.thick *
  (primeError P.d P.N₀ D.x - primeError P.d P.N₀ D.x₁) + #D.tops * primeError P.d 1 D.x₁) := by
  have A (ν : ℕ) b : #{τ ∈ D.tops | D.placeOfInt (-ν) * τ ∈ D.thick} * (lambdaClass P.d 1 ν * b) =
      #D.thick * (lambdaClass P.d P.N₀ ν * b) := by
    rw [card_filter, tops, sum_filter, ← (Equiv.divRight (D.placeOfInt (-ν))).sum_comp]
    simp +contextual [← sum_filter, lambdaClass, filter_inter, Unique.eq_default,
      placeClass_of_thick, @eq_comm _ˣ (-1), apply_ite card, div_eq_one, Set.indicator]
  have asks : ∑ τ ∈ D.tops, D.primeSum D.a τ = D.a * (#D.thick * (primeError P.d P.N₀ D.x -
    primeError P.d P.N₀ D.x₁) + #D.tops * primeError P.d 1 D.x₁ + (#D.thick *
    ((D.logX - D.logX₁) / P.N₀.totient) + #D.tops * (D.logX₁ - 1 - chowlaSelbergConst P.d))) := by
    simp [A, @sum_ite D.Φ, filter_not, cast_card_sdiff, sub_mul, re_logDerivMean_one, ← mul_sum,
      primeSum, nominalWeight, D.tops.sum_comm, primeError_eq_sum D.a D.logX₁.exp_pos
      D.le_of_hasLogBound, primeError_eq_sum D.a D.logX.exp_pos D.le_of_hasLogBound, div_ite,
      sub_ite, apply_ite posPart, ← sum_div]
    field [(HasLogBound.pos D).ne']
  have main : #D.tops * D.mainAsk = D.a * (#D.thick * ((D.logX - D.logX₁) / P.N₀.totient) +
      #D.tops * (D.logX₁ - 1 - chowlaSelbergConst P.d)) := by
    simp [mainAsk, nominalWeight, apply_ite, log_div, (HasLogBound.pos D).ne', sum_ite, filter_not,
      cast_card_sdiff, card_infinitePlace_E, show #D.tops = _ by apply card_placeClass_eq]
    field [(HasLogBound.pos D).ne']
  simp [*, remainder]
  ring
noncomputable def Data.scaledInclusion := D.seesaw.choose.1 • D.ramifiedColumns.subtype
noncomputable abbrev Data.projectedPoincare (s : D.G) : D.ramifiedColumns →ₗ[ℂ] D.rows :=
  D.goodProjTranslate s ∘ₗ D.poincare ∘ₗ D.scaledInclusion
abbrev Data.integralRamified :=
  {φ : D.ramifiedColumns | ∀ l [Fact l.Prime] [PadicPlace l], φ.1.1 ∈ integralFormsAt D.Column 1}
def Data.IndexLe {n} (y : Fin n → D.rows) δ := ∃ e : ℕ → ℝ, (∀ U, ∑ l ∈ U, e l ≤ δ) ∧
  ∀ l [Fact l.Prime] (ι : PadicPlace l) ϑ, l.Coprime ϑ.levelNorm → ∃ u :
  Matrix _ _ embValRing, (-e l).exp ≤ ‖ιₚ u.det‖ ∧ ∀ i, D.Θ ϑ (∑ k, u i k • y k) ∈ integralForms ι
lemma Data.short_forms : ∃ q > (0 : ℚ), ∃ B, B = (q : ℂ) • D.projectedPoincare ∧ (∃ S ⊆
  D.integralRamified, span ℂ S = ⊤ ∧ ∀ φ ∈ S, ∀ s σ, (D.Θ 1 (B s φ)).normSqAt σ ≤ exp (D.mainHeight
  - D.m * D.remainder + D.logB * D.budget)) ∧ ∀ (t : Finset D.G) n (y : Fin n → _), (∀ i, y i ∈
  Set.image2 (B ·) t D.integralRamified) → D.IndexLe y (#t * finrank ℂ D.Column * D.budget) := by
  obtain ⟨q, q0, e, v⟩ := exists_rat_log_eq_and_padic_norm_eq (D.nonsplitPrimes ∪ {D.N})
    (fun l ↦ ⌊D.allowedLoss l - ite (l ∈ D.nonsplitPrimes)
    (D.gain l) 0⌋) (by grind [N_prime]) (by grind [allowedLoss, Int.floor_zero])
  choose Ψ G S using D.seesaw.choose_spec
  refine ⟨q, q0, _, rfl, ⟨_, fun φ k l _ _ ↦ ⟨φ.1.2, k.1 l⟩, D.span_short_ramifiedColumns,
    fun φ k s σ ↦ (map_smul (D.projectedPoincare s) .. ▸ normSqAt_goodProjTranslate_le
    (S .. ▸ weylNormSq_Bmu_le (B := 2 * log q + D.budget)
    (G 1) (by simpa [two_mul, exp_add, exp_log, q0, sq] using k.2 σ ·) ·)).trans (by
    grw [e, heightPerRow_le, Int.floor_le]
    simp [sub_mul, -mem_filter, -union_singleton]
    grw [sum_allowedLoss_mul_log_le]; ring; simpa using D.le_of_hasLogBound)⟩, fun t n y h ↦
    ⟨fun l ↦ #t * finrank ℂ D.Column * (_ * log l),
    fun U ↦ by grw [← mul_sum, sum_allowedLoss_mul_log_le], fun l _ ι ϑ c ↦
    (exists_indexDvd_Bmu_divisible (Int.ceil_lt_add_one _)).elim fun n a ↦ a.2.elim fun _ b ↦
    (IndexDvd.sup (N' := (integralForms ι).comap ((D.Θ ϑ).restrictScalars embValRing)) (f :=
    ((q : ℂ) • D.projectedPoincare · |>.restrictScalars embValRing)) (fun s ↦ b.1.comap
    (D.ramifiedColumns.subtype.restrictScalars _) le_rfl fun φ _ h ↦ congr($((D.Θ ϑ).map_smul ..) ∈
    integralForms ι).mpr (goodProjTranslate_mem_integralForms ι (fun g ↦ by
    erw [weylGauge_smul, congr($(S ..).1 g)]
    simpa [v, weylGauge_smul, ← Int.floor_neg] using (b.2 _ _ (G ϑ) c _ h φ.2).2 g) s)) t _ y
    fun k ↦ subset_span (.inl (Set.image2_subset_left (by exact fun _ ↦ (· l)) (h k)))).imp
    fun u ⟨k, h⟩ ↦ ⟨?_, h⟩⟩⟩
  · apply (Valuation.valuationSubring.integers _).le_of_dvd at k
    simp [norm_p_eq_inv, ← NNReal.coe_le_coe] at k
    grw [← k, ← le_log_iff_exp_le] <;> simp [NeZero.pos]
    linarith [mul_le_mul_of_nonneg_right a.1 (mul_nonneg (#t).cast_nonneg (log_natCast_nonneg l))]
lemma Data.enough_forms : 0 < finrank ℂ D.Column ∧ 0 < D.rowDim ∧
  ∃ t, #t * finrank ℂ D.Column ≤ 5 * D.rowDim * log (1 + D.b ^ 2) ∧ (1 - 4 / D.b ^ 2) * D.rowDim ≤
  finrank ℂ ↥(⨆ s ∈ t, (D.projectedPoincare s).range) := have := D.columnCoords.nontrivial
  ⟨finrank_pos, D.finrank_rows_ne_zero.pos, (exists_few_translates (W :=
    D.rows) (HasLogBound.pos D) (D.ramifiedColumns_fill_rows _)).imp fun _ ↦ .imp (by simp)
    (·.trans (mod_cast finrank_mono (iSup₂_mono fun _ _ _ ⟨φ, e⟩ ↦ ⟨⟨_, φ, rfl⟩, e⟩)))⟩
end
open Finset LinearMap Real Submodule LevelPlaces.LevelForm
variable {P} {D : Data P} {n} {y : Fin n → _} {δ V} (i : LinearIndependent ℂ y) (hn :
  (1 - 4 / D.b ^ 2) * D.rowDim ≤ n) (I : D.IndexLe y δ) (hV : ∀ σ, covolumeSq (D.Θ 1 ∘ y) σ ≤ exp V)
lemma Data.heightLe_volume_ratio_sq {θ} (o : D.IsFitFamily θ) : HeightLe (2 * D.rowDim *
  (2 * (D.logB * D.budget) - D.mainHeight)) fun ι ↦ D.𝔷 (1 : D.MFoldTwist) ^ 2 / D.𝔷 (θ ι) ^ 2 := by
  choose c const _ vol using D.volume_iota_eq_prod_liftVolume
  have lifts : HeightLe (D.rowDim * (D.logB * D.budget - D.mainHeight))
      (∏ j ∈ Icc 1 D.m, fun ι ↦ D.liftVolume 1 j / D.liftVolume (θ ι) j) := (HeightLe.prod
    fun j h ↦ by exact heightLe_liftVolume_ratio o ⟨j, mem_Icc.1 h⟩).mono
    (by simp [mainHeight]; field_simp [(HasLogBound.pos D).ne']; rfl) fun _ ↦ le_rfl
  have consts : HeightLe (2 * (D.logB * D.budget)) fun ι ↦ (‖c (θ ι) / c 1‖ ^ 2 :)⁻¹ :=
    (const θ o).mono (by simpa using D.le_of_hasLogBound) fun _ ↦ le_rfl
  exact ((lifts.pow 2).mul (consts.pow D.rowDim)).mono (by grind) fun ι ↦
    (congrArg (‖ι.2 ·‖) (by simp [vol, mul_pow, div_pow, ← pow_mul]; ring)).le
include i hn I hV
lemma Data.heightLe_volume_rows {θ} (o : D.IsFitFamily θ) :
    HeightLe (V + 2 * δ + D.rowDim * D.b) fun ι ↦ D.𝔷 (θ ι) / D.𝔷 (1 : D.MFoldTwist) := by
  obtain ⟨⟨e, he, I⟩, γ, hγ, s⟩ := I, D.crude_rows
  choose k z ψ J c using exists_extend_basis_of_span_eq_top i ((s ▸ span_image
    (D.goodProjTranslate 1)).trans (by simp [range_smul, NeZero.ne, Module.End.one_eq_id]; rfl))
  choose ψ hψ ez using ψ
  refine (one_determinant D.Θ (by simp) J (by simpa) (fun _ ↦ norm_map_det_gram_le fun σ ↦
    Sum.comp_elim .. ▸ covolumeSq_elim_le (ez · ▸ normSqAt_goodProjTranslate_le ((hψ _).2 σ))
    (hV σ)) (by simp) (hγ θ o) he (fun _ j ↦ (integralForms ⟨j⟩).carrier) k (fun ι j _ a _ b ↦ ?_)
    fun ι j ↦ (I _ ⟨j⟩ _ (o.1 ι)).imp' ((algebraMap ..).mapMatrix · |>.fromBlocks 0 0 ((γ (θ ι) /
    γ 1 : ℂ) • 1)) fun _ ↦ .imp (by grw [·]; simp [← RingHom.map_det, -RingHom.mapMatrix_apply])
    (by simpa [Matrix.one_apply] using! And.intro · fun a ↦ ez a ▸
    goodProjTranslate_mem_integralForms ⟨j⟩ ((hψ a).1 _ _ ⟨j⟩ (o.1 ι)) 1)).mono (by
    rw [add_right_comm V, add_assoc]; simp [c, field] at *
    grw [(D.le_of_hasLogBound : _ + _ ≤ 4⁻¹ * D.b ^ 3)]; nlinarith [D.logB.exp_pos]) fun _ ↦ le_rfl
  simpa using (norm_inner_le_one _ _ ⟨j⟩
    (fun g ↦ by erw [D.classAut_eq_bot_of_le_chosenLevel (Subgroup.map_mono fun _ h ↦
    funext fun _ ↦ (h (.inl _) ⟨⟩).2) (by bound [D.card_Y_le .refl])]) a b :)
lemma Data.integral_forms_long : D.rowDim * (D.mainHeight - 3 * (D.logB * D.budget)) ≤
  V + 2 * δ := by
  obtain ⟨⟨θ, o⟩, _, -, Z⟩ := exists_isFitFamily D, D.volume_iota_eq_prod_liftVolume
  have formula : 0 ≤ 2 * (V + _ + _) + _ := ((((heightLe_volume_rows i hn I hV o).pow 2).mul
    (heightLe_volume_ratio_sq o)).mono le_rfl (by simp [field]; simp [(Z _).1])).nonneg
  linarith [(by gcongr; exact D.le_of_hasLogBound : D.rowDim * D.b ≤
    D.rowDim * (D.logB * D.budget))]
omit I hV i hn
lemma Data.exists_family_covolumeSq_le (D : Data P) : ∃ n, ∃ y : Fin n → _, LinearIndependent ℂ y ∧
    (1 - 4 / D.b ^ 2) * D.rowDim ≤ n ∧
  (∃ δ ≤ 5 * D.rowDim * log (1 + D.b ^ 2) * D.budget, D.IndexLe y δ) ∧ ∀ σ,
  covolumeSq (D.Θ 1 ∘ y) σ ≤ exp (n * (D.mainHeight - D.m * D.remainder + D.logB * D.budget)) := by
  obtain ⟨⟨q, q0, B, hB, ⟨S, hS, sp, size⟩, index⟩, -, -, t, ht, big⟩ :=
    D.short_forms, D.enough_forms
  let Y := Set.image2 (B ·) t S
  obtain ⟨y, hy, -, i⟩ := exists_fun_fin_finrank_span_eq ℂ Y
  rw [(by simp [Y, ← Set.iUnion_image_left, span_iUnion₂, sp]
          simp [hB, range_smul, q0.ne'] : iSup _ = span ℂ Y)] at big
  exact ⟨_, y, i, big, ⟨_, mul_le_mul_of_nonneg_right ht (HasLogBound.pos D).le, index t _ y
    (Set.image2_subset_left hS <| hy ·)⟩, fun σ ↦ covolumeSq_le
    (have ⟨s, _, φ, h, e⟩ := hy ·; by simpa [e] using size φ h s σ)⟩
