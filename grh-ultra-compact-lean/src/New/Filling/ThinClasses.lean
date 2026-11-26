import New.Filling.AmplitudeSums
import New.RealPlace.VolumeKernel
section
open Subgroup ComplexOrder ENNReal Finset MeasureTheory Real
end
namespace Filling
open Subgroup ComplexOrder ENNReal Finset MeasureTheory Real
variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {V : Type _} {S : Filling E 𝔰}
  [NormedAddCommGroup V] (A : S.Classes → S.GRes → S.Classes → V) (Ω : Set _) (T : Set ↥(S.G E))
  (Ω' : Set _)
noncomputable def energy := ∑ c, ∑ c', ∑ s with s ∈ Ω, ‖A c s c'‖ ^ 2 / S.unipCovolume ^ 2
noncomputable def linkEnergy [Side] (R : Set _) := ∑' (c) (c') (s : Ω') (Λ :
  R), ‖S.amplitudeSum (T ∩ link ⁻¹' {Λ.1}) c s.1 c'‖ₑ ^ 2
variable [StablyUnram E] [S.IsAdmissible] (U : Set ↥(S.G E)) {ε : ℝ}
  {A B : S.Classes → S.GRes → S.Classes → V} {Ω : Set _}
lemma amplitudeSum_split [Side] : S.amplitudeSum T = S.amplitudeSum (T ∩ Uᶜ) + S.amplitudeSum
  (T ∩ U) := funext₃ fun _ _ _ ↦ (tsum_congr_set_coe _ (by grind)).trans
  ((summable_amplitude ..).tsum_union_disjoint (by grind) (summable_amplitude ..))
omit [StablyUnram E] [S.IsAdmissible] in
lemma energy_add_le (hε : 0 < ε) : energy (A + B) Ω ≤
  (1 + ε) * energy A Ω + (1 + ε⁻¹) * energy B Ω := by
  simp [energy, mul_sum, ← sum_add_distrib]
  gcongr; grw [norm_add_le, add_sq, two_mul_le_add_mul_sq hε]; grind
lemma energy_sub_cut_le : energy (S.amplitudeSum U - S.amplitudeSum (σ := .cut) U) Ω ≤
  (S.b ^ 30)⁻¹ * S.besselEnergy := by
  simp [energy, amplitudeSum, summable_amplitude, ← Summable.tsum_sub, ← Finset.sum_div,
    @sum_comm S.GRes, ← toReal_enorm]
  obtain ⟨⟨r, k⟩⟩ := S.ϱ_le_k.dest, S.one_le_b, S.k_le_f, S.unipCovolume_pos
  grw [besselEnergy, columnDim, ← le_mul_of_one_le_right' NeZero.one_le, filter_subset,
    sum_sq_le_sq_sum_of_nonneg, ← Nat.card_pos.succ_le, (toReal_sum _).ge,
    toReal_le_of_le_ofReal _ ∘ (amplitudeAbs_lt_top_and_cut_le U ..).2.trans']
  any_goals simp [field, unipCovolume_pos, le_of_lt]
  grw [Fintype.card_eq_nat_card, Nat.card_pi, Nat.card_pi.le, card_GL_le _]
  simp [card_resField_eq_levelPrime, S.card_chosenPlaces, ← mul_pow, -Nat.cast_mul]
  grw [g_le_b_pow, ← one_le_two]; simp [← pow_mul, ← pow_add, ← k]; gcongr; lia
  simp [amplitude, ← integral_sub, ← smul_sub, -toReal_mul, fun [Side] c s d γ ↦
    integrable_toReal_smul (by fun_prop) (by fun_prop)
    ((ENNReal.le_tsum γ).trans_lt ((amplitudeAbs_lt_top_and_cut_le U c s).1 d).2)]
  grw [enorm_tsum_le_tsum_enorm, enorm_integral_le_lintegral_enorm, enorm_toReal_smul_le]
variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰) (c : S.Classes)
  (γ : ↥(S.G E)) (c' : S.Classes) (γ' : ↥(S.G E))
noncomputable def classSize (j : Fin (𝔰.ϱ + 2)) x := S.tailScale ^ 2 * √(ite (𝔰.ϱ < j) S.mainEnergy
  (S.tailScale ^ 13 / (S.tailScale ^ 32) ^ j.1 * S.besselEnergy) /
  (S.countWeight 0 * S.g ^ (2 * min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) * x ^ (𝔰.k + 1)))
lemma IsNear.le_classSize_and_cellMass_le {S : Filling E 𝔰} {γ} [ok : S.IsAdmissible] (n :
  S.IsNear γ) (N : 1 ≤ S.termDiscNorm γ) : (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ ≤ S.classSize ⊤
  (S.termDiscNorm γ) ∧ ∏ v, cellMass (S.ratToInf γ v) (S.besselSys v).deg S.boxSize (Fintype.card
  (S.besselSys v).I) ≤ (S.unipCovolume * S.classSize ⊤ (S.termDiscNorm γ) / 2) ^ 2 := by
  apply S.of_size_bounds; intros
  obtain ⟨⟨_, e⟩, b, m, Q, q, h, t, K⟩ := S.ϱ_le.dest, S.one_le_b, ok.packetConst_mul_mass_le,
    S.N_le, S.size_le, S.pow_le_k, ‹2 ≤ S.tailScale›,
    univ.one_le_prod₀ fun v _ ↦ S.one_le_abs_kappa v, Nonempty.intro 𝔰.k₀,
    S.besselDegree_pos, mass_pos E 𝔰.r, rootDiscr_pos E, 𝔰.openCellConst_pos
  rw [classSize, termDiscNorm, frameScaleProd, ite_eq_left, min_eq_left] at *; constructor
  grw [countWeight, ← ok.besselEnergy_le, besselEnergy, columnDim, g_le_b_pow, ← S.N_prime.one_le,
    ← t, ← one_le_two, one_pow, ← t, ← one_le_two, fun v ↦ ((n.norm_map_leadingMinor_le ⊤ v).trans'
    (by simp [↓← Complex.real_le_real, ↓← map_termDisc_eq_norm, frameDisc,
    RCLike.mul_conj]; bound) : ‖Φ v (S.termDisc γ)‖ ≤
    _), one_mul, ← @NeZero.one_le (Fintype.card S.BesselCoord), ← le_sqrt_of_sq_le]
  simp [field, ← pow_mul, ← pow_add]; gcongr; exact h.dest.choose_spec ▸ by lia
  simp_rw [cellMass, mainEnergy, besselDegree, gramDiscReal_realFrameGram_ratToInf, frameScaleSq,
    ← pow_abs_two_mul (kappa ..), add_comm 𝔰.k, pow_add] at *
  grw [packetConst, unipOrder, siegelConst, ← two_le_pi, tsub_le_self, Nat.factorial_le_pow, ← b,
    ← S.N_prime.one_le, abs_kappa_le, tsub_le_self, tsub_le_self] at m; set g := S.g
  simp (disch := positivity) only [volÔ_eq, abs_discr_eq_rootDiscr_pow, prod_pow_eq_pow_sum _ _ |_|,
    boxSize, columnDim, tailScale, Finset.prod_div_distrib, prod_const, prod_mul_distrib, card_univ,
    prod_pow, Fintype.card_pi, Fintype.card_fin, ← Real.log_le_log_iff, log_mul, log_div,
    Real.log_pow, Real.log_inv, Real.log_rpow, log_sqrt, Real.log_one, push_cast] at *; rify at *
  linear_combination (norm := rw [← neg_nonneg, ← e]) m + 3 * t + ↑(numInfPlaces E) *
    (((𝔰.k + 𝔰.ϱ + 0.5) * q + Real.log S.b * h) / 1000 + 𝔰.ϱ ^ 7 * Q)
  clear * - b N K; ring_nf; positivity
  repeat simp [one_le_pow₀, b]
noncomputable def boxCutoff := S.boxedPoints.indicator (S.classCutoff c)
noncomputable def schurWeight y := S.boxCutoff c ((S.ratToInf γ)⁻¹ * y) * ∏ v, .ofReal
    ((frameVolume (y v) / frameVolume (((S.ratToInf γ)⁻¹ * y) v)) ^ (𝔰.k + 𝔰.n))
attribute [local instance] Side.cut
noncomputable def schurIntegral := ∫⁻ y,
  S.boxCutoff c y * (∏ v, ‖(S.besselSys v).W .cut (y v)‖ₑ ^ 2) * S.schurWeight c' γ' y
variable [StablyUnram E] {S : Filling E 𝔰} {c c' : S.Classes} {γ : ↥(S.G E)} {X : Type _}
  [MeasurableSpace X]
omit [StablyUnram E] in
lemma inCut_of_besselKernel_ne_zero {y} (h : S.besselKernel γ y ≠ 0) v : InCut (y v) S.b ∧
  InCut (((S.ratToInf γ)⁻¹ * y) v)
  S.b := by simp_all [← enorm_pos, enorm_besselKernel, (S.besselSys v).tail.inCut_of_ne_zero]
@[fun_prop] lemma measurable_boxCutoff [S.IsAdmissible] :
  Measurable (S.boxCutoff c) := by delta boxCutoff boxedPoints frameBox; measurability
@[fun_prop] lemma measurable_schurWeight [S.IsAdmissible] :
  Measurable (S.schurWeight c γ) := by fun_prop [schurWeight]
lemma amplitudeAbs_sq_le [S.IsAdmissible] : S.amplitudeAbs c c' γ ^ 2 ≤
  S.schurIntegral c c' γ * S.schurIntegral c' c γ⁻¹ := by
  rw [mul_comm, schurIntegral, ← lintegral_mul_left_eq_self _ (S.ratToInf γ⁻¹)]
  apply sq_lintegral_le <;> try fun_prop
  by_contra! ⟨_, n⟩; cases by simpa using n.ne_zero
  simp_all [boxCutoff, classCutoff, boxedPoints, ↓inCut_of_besselKernel_ne_zero ‹_›,
    (isBoxPartition_epsilon c).2, ↓(isBoxPartition_epsilon c').2, enorm_besselKernel, schurWeight,
    sq]; ac_nf at n
  simp [← mul_assoc, ← prod_mul_distrib, ← ofReal_mul, ← mul_pow, field,
    frameVolume_pos, le_of_lt, ne_of_gt] at n
lemma lintegral_boxCutoff_le_of_average [S.IsAdmissible] c (m : Measure X) [SFinite m] {s : X → _ →
  _} (ms : Measurable s) (hs : ∀ x v, s x v ∈ besselU0) {F} (mF : Measurable F) (hF :
  ∀ u ∈ S.classUnip₀ c, ∀ y, F (S.ratToInf u * y) = F y) B (hm : 1 ≤ m
  B) {C} (h : ∀ u, (∀ v, u v ∈ besselU0) → ∀ y ∈ S.boxedPoints, ∫⁻ x in B, F (u * s x * y) ∂m ≤
  C) : ∫⁻ y, S.boxCutoff c y * (∏ v, ‖(S.besselSys v).W .cut (y v)‖ₑ ^ 2) * F y ≤
  C * (.ofReal S.unipCovolume * Fintype.card S.BesselCoord) := by
  cases (S.exists_cutoff_classUnip _).choose_spec
  grw [Fintype.card_pi, Nat.cast_prod, ← (S.besselSys _).tail.lintegral_sq_cut_le,
    ← lintegral_classCutoff_mul_prod _ _ c]
  simp (disch := fun_prop) [lintegral_prod, ↓← lintegral_const_mul,
    ← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar₀).lintegral_comp]
  gcongr 1; by_cases x ∈ S.boxedPoints
  any_goals simp +contextual [← ofReal_norm, norm_smul, ((S.besselSys _).tail.isBesselFunction _).2,
    boxCutoff, classCutoff, mul_mem_boxedPoints_iff, *, (isBoxPartition_epsilon c).2, mem_sup_left,
    Subgroup.mem_inf.1 (_ : besselU0).2, ← mul_assoc, mul_right_comm _ _ (F _)]
  set p := Exists.choose _
  have e t := ((Equiv.inv _).tsum_eq _).trans congr(∑' k : (S.classUnip₀ c).subgroupOf (S.classUnip
    c), $(lintegral_mul_left_eq_self (μ := .pi fun _ ↦ 𝔰.besselHaar₀) (fun u ↦ (p * F) (((u *
    t) · |>.1) * x) * p (S.ratToInf k * (u · |>.1) * x)) (⟨_, ratToInf_mem_besselU0 k⁻¹.2.2 ·⟩)))
  simp (disch := first | fun_prop | simp [← mem_subgroupOf]) [mul_assoc, ← Pi.mul_def
    (S.ratToInf _), *, ← lintegral_tsum, ↓lintegral_mul_const, -lintegral_const_mul] at e ⊢
  grw [← mul_one (lintegral ..), hm, ← setLIntegral_const, funext fun x ↦
    (lintegral_mul_right_eq_self _ (⟨_, hs x ·⟩)).symm.trans (e _).symm, lintegral_lintegral_swap]
  gcongr; rw [lintegral_mul_const]; bound
  repeat fun_prop
end Filling
section FoldSeg1
open AddSubgroup Fin DoubleCoset ENNReal Finset Fintype LinearMap MatMul Matrix MeasureTheory Metric
  Pointwise Real Norms.Elementwise
attribute [-simp] Nat.cast_mul
attribute [local simp] frameVolume_mul_left Filling.minorNorm Filling.basisScale prod_eq_zero_iff
  Subgroup.mem_sup_left realFrameGram_mul_invariant div_pow mul_pow unipotentOf_mem_besselU0
variable {E} [Field E] [CMType E] [StablyUnram E] {𝔰} {S : Filling E 𝔰} [S.IsAdmissible] {j :
  Fin (𝔰.ϱ + 2)} {c s c' γ} (hk : γ ∈ S.termsOver c s c') (h : S.HasLevel j γ)
include hk h
omit [StablyUnram E] [S.IsAdmissible] in
lemma Filling.terms_of_class_spec δ (m : δ ∈ doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c')) :
    S.HasLevel j δ ∧ S.frameProducts δ = S.frameProducts γ ∧ δ ∈ S.termsOver c s c' ∧ ∀ i,
  (frameMiddle (S.termPosition c c' δ) - frameMiddle (S.termPosition c c' γ))ᴴ.col
  i ∈ S.gIdele • colLattice (Ô E) (xRows ((S.latMiddle _).frameGram (S.termPosition c c' γ)))ᴴ := by
  obtain ⟨u, ⟨U, hu⟩, x, ⟨X, hx⟩, rfl⟩ := mem_doubleCoset.1 m
  refine ⟨(isStable_hasLevel j _ (inv_mem hu.1) _ hx.1 _).2 h, (frameGram_inv_mul_mul (inv_mem hu.1)
    hx.1).trans (by simp_all [mem_besselU0_iff.1]), by simpa using termsOver.mul (.mul U.2 hk) X.2,
    fun i ↦ ⟨_, ⟨_, (star_mem_Ô <| (S.principalLevel_eq_unitaryLevel.le (x :=
    termPosition ..) U.2).2 (.inr (.inl i)) <| eStar ·), rfl⟩, ?_⟩⟩
  rw [frameMiddle, show frameImage _ = frameImage (S.termPosition c c u * S.termPosition c c' γ) by
    simp [↓frameImage_termPosition, coe_termPosition,
      classCoord, ↓frameImage_mul_of_mem_besselU0 hx, ↓frameImage_mul]]
  simp [funext_iff, mul_apply, mulVec_eq_sum, frameGram, splitGram, apply_inr_of_mem_besselU
    (hu.1.termPosition_mem_besselU c), show star S.gIdele = S.gIdele by ext; simp [gIdele],
    ← Units.smul_def, mul_comm]
set_option synthInstance.maxHeartbeats 200000 in
seal Finset.univ Finset.sum Finset.prod in
lemma Filling.tsum_schurIntegral_le : ∑' δ : doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c'),
  S.schurIntegral c c' δ ≤ .ofReal (S.unipCovolume * (card S.BesselCoord * S.tailScale ^ 2 *
  (S.b ^ 4 * S.g)⁻¹ ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) * (S.xRowsIndex j (S.termPosition c c'
  γ) / √(S.minorNorm j γ)) ^ (𝔰.k + 1))) := S.of_size_bounds fun g τ b t _ _ N ν o _ _ ↦ by
  have D v : _ = _ * Φ v (leadingMinor (S.frameProducts γ) j) :=
    det_submatrix_realFrameGram_ratToInf ..
  let e : IndexBelow j ↪ Fin j := ⟨fun i ↦ ⟨i, i.2⟩, id fun _ ↦ by grind⟩
  let R v := diagonal fun i : IndexBelow j ↦ π * S.g / (S.b * S.basisScale v (.inl i))
  let s (x : _ → Matrix _ (IndexBelow j) ℂ) v :=
    unipotentOf (inclMatrix ℂ (·.1 : IndexBelow j → _) * (x v * R v)ᴴ, 0)
  have := (by fun_prop : Continuous s).measurable
  simp (disch := fun_prop) [schurIntegral, ← lintegral_tsum]
  grw [lintegral_boxCutoff_le_of_average c volume this (by simp [s]) _ (fun u hu y ↦ by
    conv_lhs => rw [doubleCoset, ← smul_coe_set hu, smul_mul_assoc, smul_mul_assoc,
      ← Set.image_smul, tsum_image (S.schurWeight c' · _) (by simp)]
    simp [schurWeight, ratToInf_mem_besselU0 hu.2, doubleCoset]) (ball 0 1) (by
    repeat refine (Measure.pi_ball _ _ one_pos).ge.trans' (one_le_prod'' fun _ ↦ ?_)
    simpa using! one_le_two.trans two_le_pi) fun u hu y hy ↦ ?_]; rotate_right
  set X := @ball _ (_) _ 1
  choose G _ O T using terms_of_class_spec hk h
  grw [lintegral_tsum (by clear_value s; fun_prop), tsum_le_of_colouring _ ((AddSubgroup.relIndex_pointwise_smul
    S.gIdele ..).trans_gt (one_le_xRowsIndex_and_saturationIndex hk h).1).ne' T (∫⁻ x in X,
    S.schurWeight c' · (u * s x * y)) _ fun B (hB : ∀ ⦃_⦄, _) p₀ i r ↦ ?_]
  choose! l _ M using fun p h ↦ (G _ (hB i)).exists_frameImage_toRows₂_eq_add (.subtype (·.1 < ↑j))
    (by simp) (G _ (hB h)) (by simp [*])
    (Submodule.mem_sup_left <| by simpa [*, frameGram_termPosition, Pi.sub_def] using! r p h _ i ·)
  let L (l : type_of% (l p₀)) v := l.map (Φ v · * (S.b / π))
  choose K _ iK hK using fun v ↦ exists_kernel_frameVolume_le (hy v).2 e (R v) (by simp [R, o.ne'])
    ((D v).trans_ne (by simp [h.2]))
    (frameX₀Part ((u v)⁻¹ * S.ratToInf p₀ v) * inclMatrix ℂ (castLE j.is_le))
  apply (mul_le_mul_right ((lintegral_pi_prod ..).trans_le (prod_mono' iK)) _).trans'
  have := IsOpen.measurableSet (s := X) isOpen_ball
  grw [← volume_pi, ← lintegral_const_mul, ← tsum_congr fun p ↦
    (lintegral_sub_right_eq_self _ (L _)).trans (lintegral_indicator ‹_› _), ← lintegral_tsum]
  any_goals fun_prop
  gcongr
  set w := fun _ : B ↦ _
  choose q W using (w.support.pairwise_eq_iff_exists_eq (l ·)).1 fun _ hp _ h _ ↦ sub_eq_zero.1
    (ext fun a _ ↦
    col_eq_zero_of_norm_lt_one (c := c) (by simp [Matrix.map_sub, IsIntMatrix.sub, *]) a fun v ↦ by
    simp [w] at h hp
    have e := X.sub_mem_sub h.1 hp.1
    simp [X, L, pi_norm_lt_iff, norm_lt_iff, ← sub_mul,
      ← lt_div_iff₀ (by positivity : 0 < |S.b| / π)] at e ⊢
    grw [e, pi_le_four] <;> simp [field, Nonempty.intro a]; nlinarith [S.k_le_b])
  grw [tsum_classCutoff_box_le (V := (piMap fun v ↦ ((Fintype.linearCombination ℂ _).restrictScalars
    ℝ).compLeft _).range) (fun _ ↦ Subtype.ext) (fun p hp ↦ ⟨O _ (hB p.2), by simp, by
    exact (by simpa [schurWeight, boxCutoff, W p hp] using hp :).2.1.1, ?_⟩) fun p a r b ↦
    ⟨_, funext₂ fun v _ ↦ (frameVector_sub_eq_sum (by simp [M, W _ a, W _ b]) ..).symm⟩,
    pow_le_tailScale (by grw [finrank_range_le]; simp; lia)]
  swap; grw [X.indicator_le_self .., schurWeight, boxCutoff, Set.indicator_le_self .., W p hp]
  gcongr
  cases mem_besselU0_iff_unipotentOf.1 (hu v)
  grw [← hK v _ _ _ (((G p _).1.ratToInf v).besselU_mul (inv_mem (mul_mem (hu v)
    (unipotentOf_mem_besselU0 _ : s (a - L q) v ∈ _))).1)] <;> simp [mul_assoc, s, *,
    frameX₀Part_unipotentOf_inv_mul, ← ext_iff]
  simpa [↓mul_inclMatrix, ↓basisScale_besselFrame, L, W p hp, by simpa using congrFun₂ (M _ p.2),
    mul_apply, mul_sum, R, *, add_left_comm (_ * _), add_mul, add_sub, e, ← castSucc_mk, sum_mul,
    inclMatrix, frameX₀Part, diagonal_apply, add_assoc, sub_eq_iff_eq_add'] using fun _ _ ↦
    sum_congr _ _ (by have := o.ne'; simp [*, field, ← Complex.ofReal_pow])
  have := (one_le_prod_norm_Φ · h.2.1) (.det fun _ _ ↦ isIntegral_frameProducts hk ..)
  simp (disch := intros; positivity) only [abs_norm_eq_prod_norm_sq, prod_pow, pow_mul', D,
    xRowsIndex, AddSubgroup.relIndex_pointwise_smul, sqrt_sq, ← div_pow, ← ofReal_prod_of_nonneg, ← ofReal_mul,
    pow_add _ 𝔰.k, ← ofReal_natCast, ofReal_le_ofReal_iff, prod_mul_distrib]
  have C (x : ℝ) : x ^ j.1 = x ^ (j - 𝔰.ϱ) * x ^ min 𝔰.ϱ j := by simp [← pow_add, min_comm 𝔰.ϱ]
  apply le_of_le_of_eq
    (by grw [show _ ^ 𝔰.n ≤ S.tailScale / ((∏ v, ‖Φ v _‖) / (S.N ^ numInfPlaces E) ^ (j - 𝔰.ϱ)) by
    simp
    grw [t, ← one_le_abs_kappa, N_le, le_self_pow₀ this, ← N.nat_succ_le]
    simp [field, ← pow_mul, ← pow_add]; grw [j.is_le, pow_le_tailScale]
    repeat lia, C, show _ ^ (_ - _) ≤ (S.g / S.b ^ 6) ^ min 𝔰.ϱ j by
    grw [← le_g, t]; simp [field, ← pow_mul, ← pow_add]
    gcongr; grind [S.ϱ_le], two_le_pi, ← Nat.factorial_le bot_le])
  simp [R, C, Fintype.card_subtype, card_filter_val_lt, pow_right_comm _ _ 2, prod_pow_eq_pow_sum,
    e, ← sum_of_injective e e.2 _ (𝔰.ϱ - ·) (by simp [Fin.forall_iff]; lia) fun _ ↦ rfl]
  field
attribute [local instance] Side.cut
lemma Filling.tsum_amplitudeAbs_class_le (k : S.termDiscNorm γ ≤ S.N ^ numInfPlaces E * S.minorNorm
  j γ) : ∑' δ : doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c'), S.amplitudeAbs c c' δ ≤
  .ofReal (S.unipCovolume * S.classSize j (S.classGauge j c c' γ)) := of_size_bounds (by
  intros; let : MeasurableSpace (S.G E) := ⊤; have := h.minorNorm_pos
  grw [classSize, classGauge, max_eq_right k, ← show S.N ^ numInfPlaces E * S.tailScale ^ 8 /
    (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.besselEnergy ≤ ite .. by
    grw [N_le, ← pow_mul, pow_le_tailScale (by lia), ← pow_succ']; split
    grw [← IsAdmissible.besselEnergy_le, div_le_self]
    any_goals gcongr
    repeat bound, ← ENNReal.pow_le_pow_left_iff, ← lintegral_count, sq_lintegral_le .of_discrete
    .of_discrete fun δ ↦ amplitudeAbs_sq_le, lintegral_count, lintegral_count,
    tsum_schurIntegral_le hk h, ← tsum_image _ (by simp),
    (tsum_schurIntegral_le (.inv hk) h.inv).trans' (tsum_mono_subtype _ (by simp [doubleCoset,
    mul_assoc, -Set.mul_singleton, -Set.singleton_mul])), show S.termPosition _ _ γ⁻¹ =
    (S.termPosition c c' γ)⁻¹ by simp [termPosition, mul_assoc], show S.minorNorm j γ⁻¹ =
    S.minorNorm j γ by simp [abs_norm_eq_prod_norm_sq, leadingMinor, ← conjTranspose_submatrix],
    ← ofReal_mul, ← ofReal_pow, mul_pow, mul_pow, sq_sqrt, ← sq_sqrt this.le, sqrt_sq, pow_mul
    _ 4 2, pow_mul _ 4 8, tailScale_pow_four, IsAdmissible.card_besselCoord_le] <;> try positivity
  congr! 1; push_cast [besselEnergy, columnDim, div_pow, inv_pow]; field)
end FoldSeg1
