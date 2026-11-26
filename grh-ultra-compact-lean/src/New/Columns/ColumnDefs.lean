import New.Data.Weights
import New.Curve.JetDivisibility
import Lib.Shimura.IntegralModel.NeatLevel
import New.Seesaw.IndexTypes
import Lib.SiegelWeil.Formula.SiegelWeilFormula
import New.Exchange.LValueRatio
import New.Seesaw.NamesAtSplitLevel
import New.Curve.ConjugatesOfJets
section
open Nat Finset Parameters Real
variable {P} (D : Data P) {p : ℕ}
def IsFrobPacking {s} (p : ℕ) (n i y : P.Φ s → ℕ) := let pr j σ := P.placeOfInt s (-p ^ j) * σ
  (∀ σ, y σ ≠ 0 → Odd (i σ) ∧ chiK P.d p = -1) ∧ (∀ σ t, ∀ j < i σ, y σ ≠ 0 → y t ≠ 0 → Odd j
           → pr j t ≠ pr (i σ) σ) ∧ ∀ t, p ^ i t * y t + ∑ σ with pr (i σ) σ = t, y σ ≤ n t
lemma Data.ne_d_of_placeClass_eq {e σ} (h : P.placeClass ⟨_, rfl⟩ (D.placeOfInt (-p ^ e) * σ) =
  P.placeClass ⟨_, rfl⟩ σ) : p ≠ P.d :=
  (pow_d_ne_neg_one e <| by simpa [·, Units.ext_iff, placeClass_placeOfInt, neg_eq_iff_eq_neg,
  (P.coprime_N₁_d 0).coprime_mul_right.symm.cast.pow_left.neg_left] using h)
lemma Data.summable_localAsk [Fact p.Prime] (h : chiK P.d p ≠ 1) y σ : Summable fun e ↦
  ite (0 < e ∧ (Odd e ∨ p = P.d)) (y / p ^ e - D.nominalWeight (D.placeOfInt (-p ^ e) * σ))⁺ 0 :=
  (hasSum_live_inv_pow h y).summable.norm.of_norm_bounded (by grind [posPart_def,
  nominalWeight_nonneg, norm_eq_abs])
noncomputable def Data.depthLossInt n := let c := ⌈60 * D.b / D.k⌉₊; (n - c + 1).ascFactorial c ^ 2
lemma Data.exists_isFrobPacking {n : _ → ℕ} (hn : ∀ σ, D.nominalWeight σ ≤ n σ ∧ n σ ≤
  D.nominalWeight σ + D.x ^ 42) (hp : p.Prime) (h : chiK P.d p ≠ 1) : ∃ i y,
  IsFrobPacking p n i y ∧ let L := D.forcedPart p + ∑ s, (padicValNat p (D.depthLossInt (n s)) : ℝ)
  chiK P.d p = -1 ∧ i = 1 ∧ ∑ s, (padicValNat p (n s)! - y s : ℝ) ≤ L ∨
               ∑ s, ((1 / (p - 1) - nonsplitWeight P.d p) * n s + D.b₂ * 4 - y s) ≤ L := by
  rcases P.thirteen_le_of_chiK_ne_one hp h, Fact.mk hp,
    (D.le_of_hasLogBound : D.x ^ 42 + 1 ≤ D.a / D.x₁)
  obtain ⟨hl, v⟩ := chiK_cases P.d p, @factorization_le_factorization_of_dvd_right p, D.k_pos
  simp [IsFrobPacking, forcedPart, localAsk, depthLossInt, ← sum_add_distrib,
    factorization_def, *] at v hl ⊢
  set c := ⌈(_ : ℝ)⌉₊
  have w m := @padicValNat_mul_div_factorial p m _ ▸ padicValNat_factorial_mul _
  by_cases! hk : D.k < p
  · have ⟨_, g⟩ := hl.resolve_left (hk.not_ge <| ·.1 ▸ D.nat_le_of_hasLogBound)
    have h0 s : (n s - c) / p ≤ c := by
      grw [← @cast_le ℝ, cast_div_le, sub_le, ← le_ceil, (hn _).2, nominalWeight_add_le, hk]; bound
    use 1, fun s ↦ n (D.placeOfInt (-p) * s) ⊓ (n s - c) / p, ?_,
      .inl ⟨g, rfl, sum_le_sum fun s _ ↦ ?_⟩
    · simp_all [← eq_inv_mul_iff_mul_eq, filter_eq']
      grw [min_le_right, mul_div_le]; grind
    grw [v (factorial_dvd_factorial le_tsub_add), ← factorial_mul_ascFactorial, padicValNat.mul, w,
      v (by grw [h0, (n s - c).succ.factorial_dvd_ascFactorial]), g,
      ← (D.summable_localAsk h ..).le_tsum 1 (by bound)]
    any_goals positivity
    grind [posPart_def, cast_div_le.trans (by grw [show ↑(n s - c) ≤ D.nominalWeight s by
      grind [cast_sub, cast_eq_zero, nominalWeight_nonneg, (D.le_of_hasLogBound : D.x ^ 42 ≤ c)]])]
  have hu e h := Odd.neg_pow h (p : ℤ) ▸ (@placeOfInt_pow P D.s _ e).symm
  have N s := PLift.up fun i j a b c d e f ↦ mt
    (@two_pow_le_of_pow_eq_one (-p) (by lia) i D.s a ∘ by simp [Units.ext_iff, placeClass_placeOfInt
    (isCoprime_N₀_of_not_dvd (h ∘ @chiK_eq_one_of_dvd P p 0 hp)).neg_left]) (by
    simp; grw [b, c, hk]; use D.nat_le_of_hasLogBound) (D.three_term i j a b c s d
    (D.placeOfInt (-p) ^ i * s) e (D.placeOfInt (-p) ^ j * s) f (by simp [pow_right_comm]))
  let Q s e := e < D.s ∧ Odd e ∧ p ≠ P.d ∧ s ∈ D.thick ∧ D.placeOfInt (-p) ^ e * s ∈ D.thick
  choose i y hyn hq H using fun s ↦ @by_cases (Exists (Q s)) (∃ i y, p ^ i * y ≤ n s ∧
    (y ≠ 0 → Q s i) ∧ ∀ e, Q s e → e = i ∧ y = n s / p ^ e) (.imp fun e h ↦
      ⟨_, mul_div_le .., (N s).rec (by grind)⟩) (by simp_all)
  refine have hy s s' β hl _ _ _ e := ?_; ⟨i, y, ⟨by grind, hy, fun t ↦ (forall_or_exists_not
    _).elim (sum_eq_zero (M := ℕ) · ▸ hyn t) fun ⟨s, h⟩ ↦ ?_⟩, .inr (sum_le_sum fun s _ ↦ ?_)⟩
  · rw [hu, hu, ← pow_mul_pow_sub _ hl.le, mul_assoc, mul_right_inj] at e <;> cases N s <;> grind
  · specialize hyn s; grw [← le_pow, ← hp.two_le] at hyn; rw [sum_eq_single s, show y t = 0 by
      grind [by simpa [pow_add, mul_assoc] using (N s).1 (i s) (i t + i s)]]
    rify at *; repeat grind [nominalWeight, D.nominalWeight_mem_Icc t, mul_right_inj]
  have hθ e (h : e ≤ D.s) : (D.b₂ + D.a / D.x₁) * 2 ≤ c / p / 2 / 2 ^ e := by
    grw [hk, h]; simpa using D.le_of_hasLogBound; simp
  have := hasSum_le (fun e ↦ ?_) (hasSum_live_inv_pow h (n s))
    (((D.summable_localAsk h (D.nominalWeight s)
    s).hasSum.add (hasSum_ite_eq (i s) ↑(y s))).add (hasSum_geometric_two' (c / p)))
  · nth_grw 1 [← v (factorial_dvd_ascFactorial ..), w, ← le_add_left, ← @floor_div_eq_div ℝ,
      ← sub_one_lt_floor]
    any_goals positivity
    cases hl <;> simp [And.right ‹_›] at * <;> grind [hθ 0 bot_le]
  clear hy hq hyn; specialize H s e; split <;> try simp; bound
  have h1 := (@div_le_self ℝ _ _ _ · (p ^ e) _ · (by bound))
  by_cases! hL : D.s ≤ e
  · nth_grw 1 [← le_add_of_nonneg_left (by bound), (hn _).2, nominalWeight_add_le,
      ← (by lia : 2 * 2 ≤ p), hk, cast_mul]; simp [field, mul_pow]
    grw [← hL]; simpa using D.le_of_hasLogBound; simp
  grind -ring [=_ @floor_div_eq_div ℝ, posPart_def, sub_one_lt_floor, nominalWeight,
    ne_d_of_placeClass_eq, h1 _ (sub_nonneg.2 (hn s).1), → placeClass_of_thick]
open MvPowerSeries IsLocalRing IsUltrametricDist Finsupp HasAntidiagonal
lemma exists_hasLargeSplit_of_pairs {P s p} [hp : Fact p.Prime] [PadicPlace p] (l :
  chiK (Parameters.d P) p ≠ 1)
  {N Θ i y} {n : _ →₀ ℕ} (A : IsFrobPacking p (fun σ ↦ n (σ, ())) i y) (h0 : IsCarriedBy N 1 Θ)
  (h1 : constantCoeff Θ = 1) (r : IsCarriedBy N 5 Θ⁻¹) (H : Θ ∈ P.thetaProducts s 1 1 _) : ∃ b ≤ n,
  ∃ τ ≤ n, b.degree = ∑ σ, y σ * (p ^ i σ + 1) ∧ τ.degree = ∑ σ, y σ ∧ HasLargeSplit N 6 b (p ^ ((1
  - 1 / (p - 1)) * τ.degree + nonsplitWeight P.d p * b.degree + ∑ x, ↑(padicValNat p (τ x)!))) := by
  obtain ⟨_, ϖ, _, hϖ, -, J⟩ := hp.1.pos, P.thetaProducts_normal_form s l
  let t σ := (P.placeOfInt s (-p ^ i σ) * σ, ())
  let F := Θ.rescale fun _ ↦ ϖ
  let τ (s : Finset (Σ σ, Fin (y σ))) := ∑ x ∈ s, fun₀ | t x.1 => 1
  have ⟨Q, _, u, q, g⟩ := @cons_induction _ (fun s ↦ ∃ Q, ∃ u ≠ 0, IsLowestTerm (if y ·.1 = 0 then
    p ^ iSup i else 1) (.map (residue (valRingCp p)) Q) (∑ x ∈ s, .single (x.1, ()) (p ^ i x.1)) u ∧
    ∀ P, (p ^ (1 - 1 / (p - 1) : ℝ)) ^ (τ s).degree * ‖jet _ P (seriesToCp Q * F)‖ =
    ‖jet _ (P * .monomial (τ s) 1) F‖) ⟨1, 1, by simp [IsLowestTerm, τ]⟩ ?_ ⊤
  have q : _ ≤ ‖(seriesToCp Q).coeff _‖ := (isUnit_integer_iff_norm_eq_one.1
    ((residue_ne_zero_iff_isUnit _).1 ((q _ le_rfl).trans_ne (by simpa)))).ge
  grw [← mul_one (seriesToCp Q), ← map_mul_eq_one (rescale fun _ ↦ ϖ) (Θ.inv_mul_cancel
    (by simp [*])), mul_left_comm, coeff_mul, (nonempty_antidiagonal _).norm_sum_le_sup'_norm] at q
  obtain ⟨γ, β, h, le⟩ := by simpa using q
  refine ⟨_, ?A, _, .trans (le_add_left le_add_self) ?A, ?_, ?_, ((r γ).mul (h0 (β + τ ⊤))).mono ?_⟩
  iterate 3 simp +zetaDelta [Fintype.sum_sigma, mul_add, -single_mul, le_def, h,
    single_apply, ← add_assoc, mul_comm, by simpa [sum_filter, mul_comm] using A.2.2]
  have e := (g (.monomial β 1)).le
  simp [prod_fintype, ← add_choose_mul_factorial_mul_factorial, field, F, mul_add,
    norm_natCast_eq_inv_pow_padicValNat,
    ← cast_sum, rpow_neg, rpow_add, prod_pow_eq_pow_sum, ← degree_eq_sum, rpow_mul, *] at e le ⊢
  grw [norm_natCast_le_one, prod_const_one, one_mul] at e; grw [le, ← e]; linear_combination
  rintro ⟨σ, _, e⟩ z m ⟨Q, _, u, q, g⟩
  obtain ⟨o, κ, Ψ, V, w, Ψ0, H, D⟩ := (A.1 σ e.ne_bot).imp_right ((J 1 le_rfl Θ H).2 · rfl)
  have k :=
    w.trans_gt (by apply one_lt_rpow <;> grw [← P.thirteen_le_of_chiK_ne_one hp.1 l] <;> norm_num)
  have ⟨G, v⟩ := (V.isUnit_iff_constantCoeff.2 (by
    simpa [h1, Ψ0] using congr(‖coeff 0 $H‖).symm)).dvd (a := V.pderiv (t σ))
  let R := Ψ.pderiv (t σ) * Q + C ⟨_, norm_inv κ ▸ inv_le_one_of_one_le₀ k.le⟩ *
    (Q.pderiv (t σ) + Q * G)
  refine ⟨R, _, mul_ne_zero ((D ..).2 (by use i σ, (σ, ()))) u, ?_, by simp [τ, ← mul_assoc, m, w,
    MvPolynomial.monomial_single_add, ← g, jet_mul_X, one_add, pow_succ,
    show (seriesToCp Q * F).pderiv (t σ) = κ • (seriesToCp R * F) by
    simp [R, F, *, PowerSeries.subst, add_mul, mul_add, ← map_pderiv, ← smul_eq_C_mul,
      ← PowerSeries.derivative.eq_def, PowerSeries.derivative_exp, ← norm_pos_iff, rpow_pos_of_pos]
    ring_nf]⟩
  simp [m, R, (residue_eq_zero_iff _).2, k.ne', map_pderiv]; refine .mul ?_ q
  simp +contextual [t, IsLowestTerm, coeff_monomial, eq_ite_iff, (D ..).not_right,
    or_iff_not_imp_left, weight_single, ← pow_add, @forall_comm (_ ≤ _)]
  clear * - A e; grind [IsFrobPacking, Finite.le_ciSup i σ, pow_le_pow_iff_right₀ hp.1.one_lt,
    mul_right_inj]
end
section
noncomputable section
variable {P} {D : Data P} (i : Fin 2) {w : FinPlace D.E} {n : Type} [Fintype n] {K :
  Subgroup (Gf D.E n)}
namespace Data
def chosenEquiv : D.Φ ≃ D.ChosenPlace i :=
  (Parameters.nonempty_infinitePlace_equiv_finPlace (g_modEq_one ..) D.exists_cofactor).some
lemma card_chosenPlace : Fintype.card (D.ChosenPlace i) = D.f :=
  (Fintype.card_congr (D.chosenEquiv i)).symm
lemma v_N_eq_exp_neg_one (h : ↑D.N ∈ w.1) : Valued.v (D.N : LocField w) = .exp (-1) := by
  simp [← Parameters.intValuation_p h (Parameters.not_dvd_N₁_mul_d_of_modEq_one D.N_modEq_one),
    ← v_algebraMap_eq_intValuation]
lemma intValuation_pi (h : D.π ∈ w.1) : w.intValuation D.π = .exp (-1) :=
  Parameters.intValuation_eq_of_mul_star D.N_modEq_one
  (D.π_mul_star ▸ w.1.mul_mem_right _ h) ⟨1, by simp [π_mul_star]⟩ h
def chosenGroupOrder := Nat.card (∀ x, GL (Fin (D.r * D.t)) (ResField (D.chosen x))) deriving NeZero
lemma prod_q_chosenPlace : ∏ x, (D.chosen x).q = D.gProd ^ D.f := by simp [chosen,
  Fintype.prod_sigma, D.q_eq_g (_ : D.ChosenPlace _).2.2, card_chosenPlace, gProd, mul_pow]
abbrev chosenLevel := levelOf (n := n) D.chosen ⊥
lemma isChosen_star_iff {i} : ↑(D.g i) ∈ w.1 → (D.IsChosen (star w) ↔ ¬D.IsChosen w) :=
    (Parameters.star_mem_iff (g_modEq_one ..) · D.exists_cofactor)
lemma card_GL_dvd_chosenGroupOrder (h : Fintype.card n ≤ D.r * D.t) :
  .card (∀ x, GL n (ResField (D.chosen x))) ∣ D.chosenGroupOrder :=
  Subgroup.card_dvd_of_injective (.piMap fun _ ↦ extendGL (Function.Embedding.nonempty_of_card_le
  (by simpa)).some) (by simp [Function.Injective, funext_iff]; grind [extendGL_spec, Units.ext])
instance isConjApart_chosen : IsConjApart D.chosen := ⟨by grind [g_injective, q_eq_g, chosen,
  Function.Injective], fun i ↦ by grind [D.isChosen_star_iff i.2.2.2, chosen, IsChosen]⟩
lemma range_chosen : .range D.chosen =
  {w | D.IsChosen w} := by ext; rw [Set.mem_ofPred, isChosen_iff]; aesop
lemma principalLevel_le_chosenLevel {a} (h : D.piGBar ∣ a) : principalLevel n a ≤ D.chosenLevel :=
  principalLevel_le_levelOf (Ideal.mem_of_dvd _ h ·.2.2.1)
lemma classAut_eq_bot_of_le_chosenLevel (hK : K ≤ chosenLevel) (h : Fintype.card n ≤ 2 * D.n D.m) :
  ∀ g, classAut stdRatPoints K g = ⊥ := classAut_eq_bot D.isConjApart_chosen.1
  (by grw [prod_q_chosenPlace, h, finrank_eq_two_mul_card_infinitePlace,
  pow_mul]; gcongr; use D.nat_lt_of_hasLogBound) hK
lemma card_classAut_dvd_chosenGroupOrder (hn : Fintype.card n ≤ 2 * D.n D.m) (hK : K ≤ Kf _ n) g :
    .card (classAut stdRatPoints K g) ∣ D.chosenGroupOrder := .trans (Subgroup.card_dvd_of_injective
  ((Kf.reduceFamily _).comp (.comp (.subgroupComap ..) (Subgroup.inclusion fun _ ↦ (hK ·.2))))
  ((injective_iff_map_eq_one _).2 (Subtype.ext <| (D.classAut_eq_bot_of_le_chosenLevel le_rfl hn
  _).le ⟨·.2.1, _, ·, rfl⟩))) (D.card_GL_dvd_chosenGroupOrder (hn.trans D.nat_le_of_hasLogBound))
lemma IsChosen.not_star : D.IsChosen w →
  ¬D.IsChosen (star w) := by grind [isChosen_iff, isChosen_star_iff]
lemma omega_zpow_ne_one (n : ℤ) (h : n ≠ 0 ∧ n.natAbs ≤ 8 * D.m := by omega) w : (D.ω ^ n) w ≠ 1 ↔
  D.IsChosen w := by
  by_cases D.IsChosen w <;> simp [*, ← orderOf_dvd_iff_zpow_eq_one, orderOf_ω, Int.natCast_dvd]
  use Nat.not_dvd_of_pos_of_lt (by lia) (h.2.trans_lt D.nat_lt_of_hasLogBound) ∘
    Parameters.N₁_mul_d_dvd_M_omega.trans
instance : D.HasLogUpper (P.Mω D.s) (D.logB / 9) :=
  Parameters.Mω.eq_1 .. ▸ .of_mem_Icc (a := by simpa using D.le_of_hasLogBound)
instance : D.HasLogUpper (.log D.chosenGroupOrder) (32 * D.logX) := ⟨by
  simp; grw [chosenGroupOrder, Nat.card_pi, card_GL_le _] <;> simp [card_ResField, Finset.prod_pow,
    prod_q_chosenPlace, Finset.prod_pos]
  use D.le_of_hasLogBound⟩
end Data
end
end
noncomputable section
open Matrix Finset Subgroup Ideal Fintype
namespace Data
variable {P} (D : Data P) (j) {w}
attribute [local grind] κ keptColumns lastEntry n reducedHalfGap
@[simp] lemma π_ne_zero : D.π ≠ 0 := by grind [π, NeZero.natCast_ne]
def piPlaces : Finset (FinPlace D.E) :=
  (finite_factors (span_singleton_eq_bot.ne.2 D.π_ne_zero)).toFinset
lemma mem_piPlaces : w ∈ D.piPlaces ↔ D.π ∈ w.1 := by simp [piPlaces]
protected lemma isSplitLevel_piPlaces : IsSplitLevel D.piPlaces D.N := by grind [IsSplitLevel,
  mem_piPlaces, mem_star_place, v_N_eq_exp_neg_one, π, mul_comm, P.q_eq_of_modEq_one D.N_modEq_one,
  mul_mem_left, P.star_mem_iff D.N_modEq_one _ ⟨1, by simpa using D.π_mul_star⟩]
lemma card_piPlaces : #D.piPlaces = D.f := by
  simpa [and_iff_left_of_imp (D.isSplitLevel_piPlaces.natCast_mem _), ← mem_piPlaces] using
                (P.nonempty_infinitePlace_equiv_finPlace D.N_modEq_one (a :=
    D.π) ⟨1, by simp [π_mul_star]⟩).some.cardinal_eq.symm
def columnLevel :=
  D.chosenLevel (n := D.X j) ⊓ (congruenceGL (Ô _ ∙ algebraMap _ _ D.π) Sum.inr).subgroupOf _
lemma principalLevel_le_columnLevel : principalLevel _ (D.piGBar * D.π) ≤ D.columnLevel j :=
  fun _ h ↦ ⟨D.principalLevel_le_chosenLevel (by simp) h,
  (principalLevel_le_of_dvd (dvd_mul_left ..) h).imp id (by simp)⟩
instance isLevel_columnLevel {j} : IsLevel (D.columnLevel j) := ⟨inf_le_of_left_le levelOf_le_Kf,
  isOpen_mono (principalLevel_le_columnLevel ..) (isOpen_principalLevel (by simp))⟩
def lastIndexEquiv : D.Y D.m ≃ D.InitIndex D.m := equivOfCardEq (by simp; grind [ϱ])
def branching := Classical.indefiniteDescription _ (exists_branching_matrix (fun _ ↦
  D.lastIndexEquiv.sumCongr (.refl _)) D.columnsY D.k (D.lastEntry D.m) (D.lastEntry D.m)
  (tsub_add_cancel_of_le (by grind [Pi.le_def] : (fun _ ↦ D.keptColumns) ≤ D.κ))
  (by bound) (by grind) (by simp (disch := grind [dvd_mul_left]) [ite_eq_right, card_congr
  D.lastIndexEquiv, keptColumns, reducedHalfGap, n, Nat.sub_right_comm _ 1, Nat.dvd_sub_iff_right]))
lemma card_X : card (D.X j) = D.n j := by simp; grind
lemma classAut_columnLevel_eq_bot : ∀ g, classAut stdRatPoints (D.columnLevel 0) g = ⊥ :=
  D.classAut_eq_bot_of_le_chosenLevel inf_le_left (by grind [card_X])
abbrev Column := levelSpace (algFormRep D.κ (D.lastEntry 0)) (D.columnLevel 0)
abbrev Stage := AlgForm (D.X j) D.κ (D.lastEntry j)
def branchExp τ :=
  diagramWeight (rankAt (D.X D.m)) (D.κ - fun _ ↦ D.keptColumns) (τ, 0) + D.lastEntry D.m τ
lemma le_branchExp τ : D.κ τ 1 - 2 * D.b ≤ D.branchExp τ := by grw [branchExp,
  PolyRep.diagramWeight_eq_succ_add, ← D.w_le_two_mul_b .refl τ]; simp; norm_cast; grind
def borderU := (U.block (R := 𝔸f D.E) (D.lastIndexEquiv.sumCongr (.refl Unit))).comp (.inl ..)
seal Finset.univ Finset.sum Finset.prod in
def restrictToY := (∏ τ, Φ τ (star ↑D.π) ^ (-D.branchExp τ)) •
  ((D.branching.1.map (↑)).mulVecLin.compLeft _ ∘ₗ .funLeft ℂ _ D.borderU).restrict (p :=
  AlgForm ..) (q := AlgForm ..) (id fun ψ ↦ .imp (((rightStab ψ).comap
  D.borderU).isOpen_mono (fun _ ↦ (by simp [· _])) <| ·.preimage ((U.isClosedEmbedding_mat
  isUnit_one).continuous_iff.2 (.matrix_reindex (by simp [U.sum]; fun_prop) ..))) fun k _ _ ↦ by
  simp [stdSpace_weightRep_apply]
  erw [block_embFin, k, stdSpace_weightRep_apply, mulVec_mulVec, D.branching.2.1 _ _ 1,
    Finset.prod_eq_one, one_smul] <;>
    simp [← ext_iff, PolyRep.blockScalar])
