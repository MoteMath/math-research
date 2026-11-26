import Lib.General.NumberTheory.ZeroSymmetry
import Lib.Analytic.Landau.PolarLandau
section
open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction Moebius NeZero Nat
attribute [simp] Real.log_mul log_div log_rpow log_sqrt norm_le_one ne pos
  norm_cpow_eq_rpow_re_of_pos
variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √q := by
  simpa [funext hχ.fourierTransform_eq_inv_mul_gaussSum, dft_mul_const, dft_comp_neg,
    fourierTransform_eq_gaussSum_mulShift, ← AddChar.inv_mulShift, ← star_gaussSum_eq] using
    congr(√‖$(dft_dft χ) (-1)‖)
lemma polya_vinogradov (h : χ ≠ 1) (X : ℕ) : ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + .log q) := by
  let ⟨M, ⟨r, hr⟩, ψ, _, hψ, E⟩ := exists_isPrimitive_changeLevel_eq χ
  have e (v : ℕ) : χ v = ∑ e ∈ (v.gcd r).divisors, μ e • ψ v := by
    rw [← sum_smul, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply, ← Int.cast_natCast]
    split <;> grind [Int.cast_natCast, apply_eq_zero_iff, changeLevel_eq_cast_of_dvd',
      coprime_mul_iff_right, isCoprime_iff_coprime]
  grw [funext e, sum_comm' (t' := r.divisors) (s' := fun e ↦ (Ioc 0 (X / e)).image (e * ·)) (by
    rintro v ⟨⟩ <;> simp [Nat.dvd_gcd_iff, le_div_iff_mul_le, dvd_def (b := v), mul_comm]
    aesop), norm_sum_le, sum_le_card_nsmul _ _ (√M * (1 + .log q)) fun d he ↦ ?_, card_le_card
    (t := Ioc 0 r.sqrt ∪ (Ioc 0 r.sqrt).image (r / ·)) fun d he ↦ ?_, card_union_le,
    Finset.card_image_le, congr(√$hr)] <;> clear e <;> simp [zero_lt_iff] at *
  · grw [nat_sqrt_le_real_sqrt]; grind
  · cases he.1; cases le_sqrt_of_eq_mul ‹_› <;> aesop
  simp [← mul_sum, ← Int.cast_abs, ne_zero_of_dvd_ne_zero he.2 he.1]
  let f (n : ℕ) := √M * M / 2 * ((↑n)⁻¹ + (↑(M - n))⁻¹)
  grw [norm_le_one, abs_moebius_le_one, ← dft.symm_apply_apply ψ]
  simp_rw [invDFT_apply, ← nsmul_eq_mul', AddChar.map_nsmul_eq_pow, ← smul_sum, @sum_comm _ _ ℕ,
    ← sum_smul, hψ.fourierTransform_eq_inv_mul_gaussSum]
  grw [norm_smul, ← sum_erase _ (a := 0) (by simp [map_zero', ψ.level_one'.mt (by grind)]),
    norm_sum_le_of_le _ (n := (f ·.val)) fun k hk ↦ ?_, ← sum_image (val_injective M).injOn,
    (by grind : image _ _ ⊆ range (M + 1)), ← le_of_dvd _ ⟨r, hr⟩, ← harmonic_le_one_add_log]
  iterate 3 simp [harmonic, field, sum_range_succ', two_mul, f, ↓sum_flip (·⁻¹ : ℕ → ℝ), ← mul_sum]
  simp_all [norm_gaussSum_of_isPrimitive]
  obtain ⟨x, c, hx, d⟩ : ∃ x > (0 : ℝ), k.val = M * x ∧ 0 < 1 - x := ⟨k.val / M, by
    simp [field, val_lt, -natCast_val, *]⟩
  grw [← Ico_add_one_add_one_eq_Ioc, geom_sum_Ico (injective_stdAddChar.ne hk ∘ by
    simp) (by simp), norm_div, norm_sub_le, ← (?_ : 2 * (2 * x * (1 - x)) ≤ ‖(_ : ℂ) - 1‖)]
  · simp [val_le, field, ← two_mul, *]
  grw [stdAddChar_apply, toCircle_eq_circleExp, Circle.coe_exp, mul_comm _ I, hx,
    norm_exp_I_mul_ofReal_sub_one, ← le_norm_self, (by field : _ / 2 = 2 * (π / 2 * x)),
    Real.sin_two_mul, ← one_sub_mul_le_cos] <;> simp [field, pi_pos] <;> grind [le_sin_mul]
end
section
open Complex Filter HurwitzZeta MeasureTheory Real Set ZMod
noncomputable def gaussianMonomial (j : Fin 2) x := x ^ j.1 * rexp (-π * x ^ 2)
noncomputable def gaussianTheta j (c : ℕ → ℂ) t := ∑' n : ℕ+, c n * gaussianMonomial j (n * t)
noncomputable abbrev thetaTailIntegral j c r := ∫ t in Ioi r, ‖gaussianTheta j c t‖ / √t
noncomputable def gaussianMellin (j : Fin 2) : ℂ → ℂ := mellin (gaussianMonomial j ·)
variable {j : Fin 2} {c : ℕ → ℂ} {q} {t : ℝ} {s : ℂ} [NeZero q] {χ : DirichletCharacter ℂ q}
lemma mellin_differentiableOn_and_bounded {D} {f : ℝ → ℂ} (b : ∀ {t}, 0 < t → ‖f t‖ ≤ D * rexp (-t))
    (m : AEStronglyMeasurable f := by fun_prop (disch := simp) [gaussianTheta, gaussianMonomial]) :
  DifferentiableOn ℂ (mellin f) {z | 0 < z.re} ∧ ∃ G, ∀ z, re z ∈ Icc 2⁻¹ 2 → ‖mellin f z‖ ≤ G := by
  refine (fun o p a ↦ have c s := mellinConvergent_of_isBigO_rpow_exp (s := s) one_pos a o p
    ⟨fun _ ↦ (mellin_differentiableAt_of_isBigO_rpow_exp one_pos a o p · |>.differentiableWithinAt),
    _, fun z _ ↦ norm_integral_le_of_norm_le ((c 2⁻¹ ?_).prodMk (c 2 ?_)).norm
    (ae_restrict_of_forall_mem ?_ fun t ↦ ?_)⟩) ?_ ?_ fun _ _ ↦ (volume.finiteAt_nhdsWithin
    ..).integrableAtFilter ⟨⊤, ?_⟩ ?_ <;> simp_all [Asymptotics.isBigO_iff]
  use D, 1, by grind
  iterate 2 exact ⟨_, mem_inf_of_right fun t k ↦ (b k).trans (by grw [le_abs_self D, ← k.out])⟩
  bound [le_total t 1]
lemma norm_gaussianMonomial_le (h : 0 ≤ t) : ‖gaussianMonomial j t‖ ≤ 3 * rexp (-t) ^ 2 := by
  grw [gaussianMonomial, norm_of_nonneg (by bound), show t ^ j.1 ≤ t + 1 by fin_cases j <;> grind,
    add_one_le_exp, ← exp_one_lt_three, ← pi_gt_three]
  simp [sq, ← Real.exp_add]; grind [sq_nonneg (t - 2⁻¹)]
lemma summable_and_norm_gaussianTheta_le (hc : ∀ n, ‖c n‖ ≤ 1) (ht : 0 < t) : (Summable fun n : ℕ+ ↦
  c n * gaussianMonomial j (n * t)) ∧ ‖gaussianTheta j c t‖ ≤ 3 * rexp (-t) / t := by
  have H := hasSum_pnat_iff_hasSum_succ.2 ((hasSum_nat_add_iff' 1).2
    ((hasSum_geometric_of_abs_lt_one (by simpa : |rexp (-t) ^ 2| < 1)).mul_left 3))
  refine (fun b ↦ ⟨H.summable.of_norm_bounded b, (tsum_of_norm_bounded H b).trans ?_⟩) fun n ↦ ?_
  · grw [norm_mul, hc, norm_real, norm_gaussianMonomial_le] <;> simp [← Real.exp_nat_mul, field,
      ht.le]
  simp [t.exp_neg, field, *]; nlinarith [t.add_one_le_exp]
lemma gaussianMellin_eq (hs : 0 < s.re) : gaussianMellin j s = Gammaℝ (s + j) / 2 := by
  simpa [gaussianMellin, gaussianMonomial, field] using (mellin_cpow_smul _ s j).trans
    ((mellin_comp_rpow _ _ 2).trans (congrArg _ (@hasSum_mellin_pi_mul_sq Unit _ 1 1
    (rexp <| -π * ·) _ (by simp; bound) (by simp) .of_finite).tsum_eq.symm))
lemma mellin_gaussianTheta (hc : ∀ n, ‖c n‖ ≤ 1) (hs : 1 < s.re) :
    mellin (gaussianTheta j c) s = gaussianMellin j s * LSeries c s := by
  rw [gaussianMellin_eq (by bound), LSeries, ← tsum_pnat_eq_tsum_of_eq_zero rfl]
  convert (mellin_cpow_smul _ s j.1).trans ((mellin_comp_rpow _ _ 2).trans (congrArg _
    (@hasSum_mellin_pi_mul_sq ℕ+ _ (fun n ↦ c n * n ^ j.1) (·) _ _ (by simp; bound)
    (fun u (h : 0 < u) ↦ (((@summable_and_norm_gaussianTheta_le j c √u hc ?_).1.div_const
    (√u ^ j.1)).congr ?_).hasSum) ((summable_pnat_iff_summable_nat.2 (summable_nat_rpow_inv.2
    hs)).of_nonneg_of_le ?_ ?_)).tsum_eq.symm)) using 1 <;> simp [← tsum_mul_left, cpow_add,
    rpow_add, field, mellin, gaussianTheta, gaussianMonomial, mul_pow, division_def, mul_assoc,
    mul_left_comm, le_of_lt, ne_of_gt, *]
omit [NeZero q] in
lemma two_mul_gaussianTheta t {Φ : ZMod q → ℂ} {S} (h : ∀ x, Φ (-x) = (-1) ^ j.1 * Φ x) (h0 : Φ 0 =
  0) (H : HasSum (fun n : ℤ ↦ Φ n * gaussianMonomial j (n * t)) S) : 2 * gaussianTheta j (Φ ·) t =
  S := by rw [← H.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat _ H.summable] <;> fin_cases j <;>
  simp [Function.Even, gaussianMonomial, gaussianTheta, *]
lemma poisson_summation_gaussianMonomial a (ht : 0 < t) : ∃ S,
  HasSum (fun n : ℤ ↦ gaussianMonomial j ((n + a) * t)) S ∧ HasSum (fun n : ℤ ↦ cexp
  (2 * π * I * a * n) * gaussianMonomial j (n * t⁻¹)) (I ^ j.1 * t * S) := have h := pow_pos ht 2
  by fin_cases j <;> [obtain ⟨u, v⟩ := hasSum_int_evenKernel a h, hasSum_int_cosKernel a (inv_pos.2
                h); obtain ⟨u, v⟩ := (hasSum_int_oddKernel a h).mul_left t, (hasSum_int_sinKernel a
    (inv_pos.2 h)).mul_left (I / t)] <;> refine ⟨_, u.congr_fun ?_, (v.congr_fun ?_).trans_eq
    (congrArg _ ?_)⟩ <;> simp [gaussianMonomial, mul_pow, mul_assoc, evenKernel_functional_equation,
    ht.ne', oddKernel_functional_equation, ← rpow_natCast_mul ht.le, field, mul_div_cancel₀]
lemma gaussianMellin_differentiableOn_and_bdd : DifferentiableOn ℂ (gaussianMellin j) {z | 0 < z.re}
  ∧ ∃ G, ∀ z, re z ∈ Icc 2⁻¹ 2 → ‖gaussianMellin j z‖ ≤ G := mellin_differentiableOn_and_bounded
  fun h ↦ by grw [norm_real, norm_gaussianMonomial_le, _root_.sq_le] <;> simp [h.le, exp_nonneg]
lemma exists_pos_le_norm_gaussianMellin {K} (hK : IsCompact K) (h : ∀ s ∈ K, 0 < s.re) :
    ∃ c > 0, ∀ s ∈ K, c ≤ ‖gaussianMellin j s‖ :=
  hK.exists_forall_le' (gaussianMellin_differentiableOn_and_bdd.1.continuousOn.mono h).norm
  fun s k ↦ by simp [gaussianMellin_eq, Gammaℝ_ne_zero_of_re_pos, (h s k).trans_le]
variable (h1 : χ ≠ 1) (hp : χ (-1) = (-1) ^ j.1)
include h1 hp
lemma gaussianTheta_poisson_summation (ht : 0 < t) :
  t * ‖gaussianTheta j (χ ·) t‖ = ‖gaussianTheta j (𝓕⁻ χ ·) (q * t)⁻¹‖ := by
  have e (x : ZMod q) := hp ▸ neg_one_mul x ▸ map_mul χ _ x
  choose S h h' using fun a : ZMod q ↦
    @poisson_summation_gaussianMonomial j (q * t) (a.val / q) (by simpa)
  have a := two_mul_gaussianTheta t e (χ.map_zero' (h1 ∘ χ.level_one')) ((hasSum_sum fun a _ ↦
    (Function.Injective.hasSum_iff (g := fun n : ℤ ↦ a.cast + q * n) (fun _ ↦ by simp) (by
    simp_all [intCast_eq_iff, ne_comm])).1 (((hasSum_ofReal.2 (h a)).mul_left (χ a)).congr_fun
    (by simp [← mul_assoc, add_mul]; grind))).congr_fun (Fintype.sum_pi_single' ↑· _ |>.symm))
  have b := @two_mul_gaussianTheta j _ (q * t)⁻¹ (𝓕⁻ χ) _ (fun n ↦ by
    simp_rw [invDFT_apply', ← congr($(dft_comp_neg χ) (-n)), e, dft_const_mul]; ring)
    (by simp [invDFT_apply, χ.sum_eq_zero_of_ne_one h1]) (((hasSum_sum (s := ⊤) fun a _ ↦
    (h' a).mul_left (χ a)).div_const q).congr_fun fun n ↦ by
    simp_rw [invDFT_apply, ← zsmul_eq_mul', AddChar.map_zsmul_eq_zpow, stdAddChar_apply]
    simp [toCircle_apply, ← exp_int_mul, Finset.sum_mul, -natCast_val, field]; grind)
  simp_all [mul_left_comm, ← Finset.mul_sum, ← a, abs_of_pos, field]
lemma norm_gaussianTheta_functional_equation (hχ :
  χ.IsPrimitive) (ht : 0 < t) : √q * t * ‖gaussianTheta j (χ ·) t‖ = ‖gaussianTheta j (χ ·)
  (q * t)⁻¹‖ := by rw [mul_assoc, gaussianTheta_poisson_summation, eq_comm, ← norm_star] <;>
  simp [gaussianTheta, tsum_star, invDFT_apply', hχ.fourierTransform_eq_inv_mul_gaussSum,
  χ.star_apply', mul_assoc, mul_left_comm, tsum_mul_left, norm_gaussSum_of_isPrimitive, *, field]
lemma norm_gaussianTheta_char_le (h : 0 < t) : ‖gaussianTheta j (χ ·) t‖ ≤ 3 * q * rexp 1 * rexp
  (-t) := by
  cases le_total 1 t
  · grw [(summable_and_norm_gaussianTheta_le (by simp) h).2, div_le_self,
      ← @NeZero.one_le q] <;> bound
  grw [← mul_le_mul_iff_right₀ h, gaussianTheta_poisson_summation,
    (summable_and_norm_gaussianTheta_le (fun n ↦ by grw [invDFT_apply, norm_smul,
    norm_sum_le_of_le _ (n := 1)] <;> simp) _).2, exp_le_one_iff.2] <;> simp [field, t.exp_neg, *]
lemma mellin_gaussianTheta_char (hs : 0 < s.re) : mellin (gaussianTheta j (χ ·)) s =
  gaussianMellin j s * χ.LFunction s := have o := isOpen_re_gt
  ((mellin_differentiableOn_and_bounded (norm_gaussianTheta_char_le h1 hp)).1.analyticOnNhd
    (o 0)).eqOn_of_preconnected_of_eventuallyEq
  ((gaussianMellin_differentiableOn_and_bdd.1.mul (by fun_prop)).analyticOnNhd (o 0))
    (convex_halfSpace_re_gt 0).isPreconnected (by simp : 0 < re 2) (.mono ((o 1).mem_nhds (by simp))
  (by simp_all [mellin_gaussianTheta, χ.LFunction_eq_LSeries])) hs
lemma thetaTailIntegral_zero_le_two_mul (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 < T) (h : q ≤ T ^ 2) :
    thetaTailIntegral j (χ ·) 0 ≤ 2 * thetaTailIntegral j (χ ·) T⁻¹ := by_cases (fun i ↦ by
  grw [two_mul, ← sub_le_iff_le_add, ← setIntegral_sdiff _ i, Ioi_sdiff_Ioi, thetaTailIntegral,
    ← show _ '' Ioo 0 T⁻¹ ⊆ Ioi T⁻¹ from forall_mem_image.2 fun t ⟨a, b⟩ ↦ inv_strictAnti₀
    (b := q * t) ?_ (by grw [h, b]; simp [sq]), integral_image_eq_integral_abs_deriv_smul _
    fun t k ↦ (hasDerivAt_const_mul _).hasDerivWithinAt.fun_inv (by simp [k.1.ne']),
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun]
  any_goals simp +contextual [← norm_gaussianTheta_functional_equation, abs_div, field, EqOn,
    le_of_lt, -mul_inv_rev, *]
  exacts [.of_forall fun _ ↦ by positivity, i.mono_measure (by gcongr; bound)]) (integral_undef ·
    |>.trans_le (by positivity))
end
section
attribute [-instance] IdemSemiring.toCanonicallyOrderedAdd IdemSemiring.toMulLeftMono
open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory LSeries Finset Real
  Topology vonMangoldt Chebyshev Polynomial ZMod MulChar
lemma exists_norm_LFunction_le {r} (h0 : 0 < r) (_ : r < 9⁻¹) : ∃ C ≥ 0, ∀ {q} [NeZero q]
    {χ : DirichletCharacter ℂ q} {s}, χ ≠ 1 → dist s 1 ≤ r → ‖χ.LFunction s‖ ≤ C * q ^ (2 * r) := by
  have p s := by simpa [← dist_eq_norm] using abs_re_le_norm (s - 1)
  choose c c0 hc using
    (@exists_pos_le_norm_gaussianMellin · _ (isCompact_closedBall 1 r) (by simp; grind))
  exact ⟨_, norm_nonneg (_ / c ·), @fun q ⟨_⟩ χ s hχ hs ↦ by
    have ⟨j, hp⟩ : ∃ j : Fin 2, χ (-1) = (-1) ^ j.1 := by simpa using! χ.even_or_odd
    grw [← norm_le_pi_norm, ← le_norm_self, div_mul_eq_mul_div, le_div_iff₀' (c0 j), hc j s hs,
      ← norm_mul, ← mellin_gaussianTheta_char hχ hp (by grind), mellin, norm_integral_le_of_norm_le
      (((GammaIntegral_convergent h0).const_mul (3 * rexp 1)).mul_const _)
      (ae_restrict_of_forall_mem (by simp) fun t (k : 0 < t) ↦ ?_), integral_mul_const]
    grw [norm_smul, le_min (summable_and_norm_gaussianTheta_le (by simp) k).2
      (norm_gaussianTheta_char_le hχ hp k), min_def]
    split <;> simp (disch := positivity) [← log_le_log_iff, abs_le] at * <;>
      nlinarith [p s, log_natCast_nonneg q]⟩
lemma eventually_mul_norm_deriv_entireL_lt A {M : ℕ} [NeZero M] (e : 4 ∣ M) : ∀ᶠ η : ℝ in 𝓝[>] 0,
  ∀ k > 1, ∀ χ s,
  M ^ k ≤ (η ^ A)⁻¹ → dist s 1 ≤ η → ¬‖entireL χ s‖ ≤ η * ‖deriv (@entireL (M ^ k) _ χ) s‖ := by
  obtain ⟨⟨r, h0, _⟩, m, f⟩ := exists_pos_mul_lt one_pos (20 * A + 18 : ℝ), e
  have ⟨K, _, hC⟩ := exists_norm_LFunction_le (add_pos h0 h0) (by nlinarith)
  filter_upwards [mem_inf_of_left (eventually_closedBall_subset (by
    simp; intro; and_intros <;> apply ContinuousAt.eventually_lt <;> first
      | fun_prop (disch := grind) | simp (disch := bound) [entireL_ne_zero] : ∀ᶠ x in 𝓝 (0, 1), ∀ f
    ∈ range (@entireL (M ^ 2) _), x.1 * ‖deriv f x.2‖ < ‖f x.2‖ ∧ x.1 ^ (-A * (2 * (r + r)) * 5 + 1)
    * ‖f x.2‖ ^ 3 * (3 / r) ^ 4 * K ^ 5 < 1)), Ioc_mem_nhdsGT h0] with η H ⟨hη, j⟩ k o χ s hk hs h7
  have H {s} hs χ (h : χ ^ 2 = 1) := @H (η, s) (max_le (c := η) (by simp; grind) hs) (entireL χ)
    (((χ.factorsThrough_iff_ker_unitsMap (pow_dvd_pow M o)).2 fun u hu ↦
    ((intCast_eq_intCast_iff_dvd_sub u.1.cast 1 _).1 (by simp; use congr($hu.1))).elim fun t a ↦ by
    obtain ⟨⟨c⟩⟩ := (C (M * m * t) + X ^ 2 + X).existsUnique_nilpotent_sub_and_aeval_eq_zero
      (x := 0 * u.1) ⟨k, by simp [mul_pow, natCast_pow_eq_zero_of_le]⟩ (by simp), congr($a + u.1)
    ext; simpa [show u = (1 + 2 * c) ^ 2 by simp [f, map_ofNat] at *; grind, ← pow_apply', h] using
      one_apply_coe u).2.imp fun g a ↦ by ext s; fun_cases entireL g <;> by_cases s =
    1 <;> simp [LFunction_changeLevel, Nat.primeFactors_pow, *, entireL, o.ne_zero,
    LFunctionTrivChar_eq_mul_riemannZeta] <;>
    simpa [*, Nat.primeFactors_pow] using g.LFunction_changeLevel dvd_rfl)
  have ⟨h, n, h1⟩ : χ ^ 2 ≠ 1 ∧ χ ≠ 1 ∧ dist (1 + η : ℂ) 1 ≤ η := by simp; grind [one_pow]
  have hd (z : ℂ) (b : dist z 1 ≤ η) := norm_deriv_le_of_forall_mem_sphere_norm_le h0
    (differentiable_LFunction n).diffContOnCl fun w a ↦ hC n (by grw [dist_triangle, a.le, b, j])
  apply ((H h1 1 (by simp)).2.trans_le (norm_LFunction_product_ge_one χ hη 0)).not_ge
  simp [entireL, hη.ne', abs_of_pos, rpow_add, rpow_mul hη.le, *, -neg_mul] at h7 ⊢
  nth_grw 1 [norm_le_insert' (χ.LFunction _), h7, hd, (convex_closedBall
    ..).norm_image_sub_le_of_norm_deriv_le (by fun_prop) hd hs h1, ← dist_eq_norm,
    dist_triangle_right, hs, h1, hC h, ← hk] <;> grind
lemma exists_prime_modEq_one_log_mem (M A : ℕ) [NeZero M] (hM : 4 ∣ M) : ∀ᶠ W : ℝ in atTop, ∀ k > 1,
  M ^
  k ≤ W ^ A → ∀ U ∈ Icc W (W ^ A), ∃ p, p.Prime ∧ p ≡ 1 [MOD M ^ k] ∧ .log p ∈ Icc U (U + W) := by
  obtain ⟨t, n, C, hC⟩ := tendsto_sqrt_atTop, (hasDerivAt_term · · · |>.differentiableAt),
    (LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := 3 / 4) (by simpa [sum_filter,
    psi_sub_theta_eq_sum_not_prime, sqrt_eq_rpow] using! isBigO_psi_sub_theta_sqrt.natCast_atTop)
    (by bound) (by simp) (by bound)).norm
  filter_upwards [mem_atTop (C ⊔ 0), t (tendsto_inv_atTop_nhdsGT_zero
    (eventually_mul_norm_deriv_entireL_lt (2 * A) hM)), t (tendsto_exp_mul_div_rpow_atTop (2 *
    A * 2) 4⁻¹ (by simp) (Ioi_mem_atTop (.exp 2))), t (mem_atTop 9)] with W _ h hW g k o hq U hV
  set q := M ^ k; simp_all [← natCast_eq_natCast_iff, rpow_mul, pow_mul]
  have ⟨D, d, p, _⟩ : ∃ D > 0, 0 < W ∧ U * D = 1 := ⟨U⁻¹, by grind [inv_pos]⟩
  let a n : ℂ := @residueClass q 1 n
  let F z := (1 - z * ∑ χ, logDeriv (@entireL q _ χ) (1 + z)) / q.totient
  have e z (h : 0 < z.re) : LSeriesHasSum a (1 + z) (F z / z) := by
    convert (LSeriesHasSum.sum (S := ⊤) fun χ _ ↦ @LSeriesHasSum_mul_vonMangoldt q χ _ _ ?_).smul
      q.totient⁻¹ <;> simp [a, residueClass_eq, h, ite_div]
    field [ne_zero_of_re_pos h]
  have hb {z} (u : ‖z‖ ≤ (√W)⁻¹) : _ ∧ ‖F z‖ ≤ 2 := have h := (h k o · (1 + z) hq (by simpa))
    ⟨(norm_pos_iff.1 <| h · |>.trans_le' (by bound)), by
    grw [norm_div, mul_sum, norm_sub_le, norm_sum_le]; simp [logDeriv, mul_div]
    grw [u, h, div_self_le_one]
    simp [← card_eq_totient_of_hasEnoughRootsOfUnity ℂ, field, mul_two, NeZero.one_le]⟩
  by_contra
  apply (@norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le _ _ _ _ 0 √W⁻¹ U (fun z ↦ (F z - z *
    ∑ n ∈ range ⌈U.exp⌉₊ with .log (n : ℕ) < U, term a (1 + z) n) / (2 - U * z - √W / 4 *
    (1 + √W * z) ^ 2).exp) 0 (by simpa) (DifferentiableOn.diffContOnCl_ball (fun s b ↦
    DifferentiableAt.differentiableWithinAt (by fun_prop (disch := simp_all) [logDeriv])) le_rfl)
    fun z u ↦ ?_).not_gt
  simp [F, field, Real.exp_sub] at *
  grw [hV.2, q.totient_le, M.cast_pow, hq]; grind
  obtain := z.sq_norm_sub_sq_re, z.abs_re_le_norm, sq_sqrt p.le
  simp [div_le_iff₀, exp_pos, -sub_re, sq, abs_le] at *; set E := re _
  obtain ⟨⟨⟩ : ∃ τ ≥ 0, τ ≤ W ∧ 2 - (U + τ) * z.re ≤ E, b : re (F D / D) ≤ 2 * U⟩ :=
    ⟨W / 2 * (1 + √W * z.re), by simp [u, field, E] at *; split_ands <;> nlinarith⟩, by
    grw [re_le_norm, norm_div, (hb _).2] <;> simp [abs_of_pos d, field] <;> nlinarith
  have G := (hasSum_re (e D d)).congr_fun fun n ↦ (re_eq_norm.2 (mod_cast term_nonneg
    (by simp [a, residueClass_nonneg]) _)).symm
  have key (n : ℕ) σ (h : .log n * (σ - z.re) ≤ E) : ‖term a (1 + z) n‖ ≤ E.exp *
      ‖term a (1 + σ) n‖ := by grw [← h]; by_cases n = 0 <;>
    simp [*, ↓cpow_add, cpow_def, field, mul_sub, Real.exp_sub, ← natCast_log]
  obtain ⟨v, x | x⟩ := u ▸ inv_anti₀ (by simp) g, le_or_gt z.re D
  · grw [norm_sub_le, norm_mul, (hb u.le).2, v, norm_sum_le, key, ← mul_sum,
      sum_le_hasSum _ (by simp) G, b] <;> simp at * <;> nlinarith [E.one_le_exp (by nlinarith)]
  grw [← mul_div_cancel₀ (F z) (ne_zero_of_re_pos (d.trans x)), ← mul_sub, norm_mul, v,
    sum_filter, (HasSum.sub (e z (by bound)) (hasSum_sum_of_ne_finset_zero (by grind [Nat.lt_ceil,
    lt_exp_of_log_lt]))).norm_le_of_bounded ((hC.add G).mul_left E.exp) fun n ↦ ?_, b]
  nlinarith [exp_pos E]
  split <;> simp; bound
  by_cases U + W < .log n <;> [grw [key n D (by nlinarith)]; grw [← @norm_term_le a _ _ _
    (by simp [a, indicator]; grind), key n (-4⁻¹) (by nlinarith)]] <;> bound
end
seal Finset.univ Finset.sum Finset.prod
open ArithmeticFunction DirichletCharacter Complex Moebius Finset Real ZMod vonMangoldt LSeries
  Filter jacobiSym legendreSym MeasureTheory Nat NumberTheorySymbols
variable {N : ℕ} [NeZero N] (ξ : DirichletCharacter ℂ N) (j : Fin 2) {η : ℝ}
omit [NeZero N] in
lemma norm_mul_moebius_le_one (n : ℕ) : ‖ξ n * μ n‖ ≤ 1 := by by_cases Squarefree n <;> simp [*]
open Set HadamardThreeLines in
lemma three_lines_bound_of_LFunction_eq_zero : ∃ C,
  ∀ {η T : ℝ} {q} [NeZero q] {χ : DirichletCharacter ℂ q} {s}, 0 < η → χ.IsPrimitive → χ ≠ 1 →
  χ (-1) = (-1) ^ j.1 → 0 < T → q ≤ T ^ 2 → thetaTailIntegral j (χ ·) T⁻¹ + thetaTailIntegral j
  (fun n ↦ χ n * μ n) T⁻¹ ≤ T ^ (2 * η) → χ.LFunction s = 0 → 1 / 2 + 9 * η ≤ s.re → s.re ≤ 1 →
  ‖gaussianMellin j s‖ ^ 2 ≤ C / T ^ (2 * η) := (@gaussianMellin_differentiableOn_and_bdd j).2.imp'
  (9 + · ^ 2) fun G g η T q _ χ s _ hχ h1 hp hT hq J Z _ _ ↦ by
  have T1 := (one_le_sq_iff₀ hT.le).1 (hq.trans' (by simp [succ_le_iff]))
  obtain ⟨n, X⟩ := norm_mul_moebius_le_one χ,
    one_le_pow₀ (one_le_rpow T1 (by bound : 0 ≤ 2 * η)) (n := 2)
  let f := (Ioi T⁻¹).indicator (gaussianTheta j fun n ↦ χ n * μ n)
  obtain ⟨⟨p, _, A⟩, b, _, B⟩ := mellin_differentiableOn_and_bounded
    (norm_gaussianTheta_char_le h1 hp), mellin_differentiableOn_and_bounded (D := 3 * T) (f := f)
    fun {t} k ↦ by
    by_cases i : T⁻¹ < t <;> simp [f, i, hT.le, exp_pos]
    grw [(summable_and_norm_gaussianTheta_le n k).2, mul_right_comm, ← div_inv_eq_mul _ T, i]
  let a := (9 + G ^ 2) * (T ^ (2 * η)) ^ 2
  have e w : mellin f w = _ := @indicator_smul .. ▸ setIntegral_indicator (by simp)
  refine .trans (.trans_eq' (norm_le_interp_of_mem_verticalClosedStrip' (z := s) (a := a) (b := a /
    T) (by bound) ⟨by bound, by bound⟩ (((gaussianMellin_differentiableOn_and_bdd.1.fun_pow
    2).fun_sub (p.fun_mul b)).mono (closure_preimage_re _ ▸ by grind [closure_Ioo])).diffContOnCl
    ⟨_, forall_mem_image.2 fun z k ↦ norm_sub_le_of_le (by simp; grw [g z k]) (norm_mul_le_of_le
    (A z k) (B z k))⟩ ?_ ?_) (by simp [mellin_gaussianTheta_char, *, show 0 < s.re by bound])) ?_
  any_goals intro z (hz : _ = _)
  · have N r g (k : 0 ≤ r) : _ ≤ thetaTailIntegral j g r := (norm_integral_le_integral_norm fun t ↦
      ofReal t ^ (z - 1) • gaussianTheta j g t).trans_eq (setIntegral_congr_fun (by simp) fun t
      i ↦ by norm_num [hz, rpow_neg, k.trans_lt i, le_of_lt, sqrt_eq_rpow]; ring)
    grw [norm_sub_le, norm_mul, norm_pow, g, e, inter_eq_right.2, N, mellin, N,
      thetaTailIntegral_zero_le_two_mul h1 hp hχ
      hT, two_mul_le_add_sq, pow_add_pow_le, J] <;> norm_num [hz] <;> first | positivity | nlinarith
  · have I := (integrableOn_exp_neg_Ioi 0).const_mul 3
    have P {c} h t k : ‖ofReal t ^ (z - 1) • gaussianTheta j c t‖ ≤ 3 * rexp (-t) :=
      (norm_mul_le_of_le
      le_rfl (summable_and_norm_gaussianTheta_le h k).2).trans_eq (by norm_num [k, hz]; field)
    erw [sq, ← mul_one (_ * _), ← mul_mu_eq_one χ, mul_mul_mul_comm, ← mellin_gaussianTheta,
      ← mellin_gaussianTheta n]
    grw [← mul_sub, e, norm_mul, mellin, norm_integral_le_of_norm_le I (ae_restrict_of_forall_mem _
      (P _)), integral_const_mul, integral_exp_neg_Ioi_zero, mellin, ← setIntegral_sdiff _
      (I.mono' (by fun_prop [gaussianTheta, gaussianMonomial]) (ae_restrict_of_forall_mem _ (P n))),
      norm_setIntegral_le_of_norm_le_const _ fun t j ↦ by grw [P n t j.1, ← j.1.out]]
    all_goals simp [hT.le, field] <;> nlinarith
  simp (disch := positivity) [← log_le_log_iff, a, field]
  nlinarith [log_nonneg T1]
lemma norm_sum_jacobiSym_le {m} (hm : m ≠ 0) (h : ¬IsSquare m) (h' : ¬IsSquare (2 * m)) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, (J(-v | m) : ℂ)‖ ≤ 2 * √m * (1 + .log m) := by
  choose ψ E using @induction_on_primes (fun b ↦ ∃ ψ : DirichletCharacter ℂ b, b ≠ 0 → ∀ v : ℤ,
    ψ v = J(v | b)) (by simp) ⟨1, by simp [@Subsingleton.eq_one (ZMod 1)]⟩ fun p _ hp ⟨ψ, _⟩ ↦
    mul_comm _ p ▸ ⟨@quadTwist _ ψ _ ⟨hp⟩, by simp_all [quadTwist_apply, mul_right', to_jacobiSym]⟩
  grw [← @polya_vinogradov m ⟨hm⟩ (ψ m) (fun e ↦ ?_) X]
  · obtain k | k := (ψ m).even_or_odd <;> simp [← E, hm, k.eval_neg]
  obtain ⟨a, c, rfl, ha⟩ := m.sq_mul_squarefree
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, ⟨b, rfl⟩, o⟩ := a.eq_two_pow_or_exists_odd_prime_and_dvd
  exacts [h ⟨c, by ring⟩, h' ⟨2 * c, by ring⟩, by grind [squarefree_pow_iff],
    @quadTwist_ne_one b (ψ b) p ⟨hp⟩ (by grind) (by grind [Nat.squarefree_mul_iff])
    ((@changeLevel_eq_one_iff _ _ _ _ ⟨hm⟩ _ (by simp [mul_comm])).1 (MulChar.ext fun u ↦ by
    have := congr($e (u.1.cast : ℤ))
    rw [changeLevel_eq_cast_of_dvd, ← intCast_cast, quadTwist_apply]
    simp_all [to_jacobiSym, ↓E, mul_right', sq, ← Int.cast_mul]; grind [trichotomy]))]
lemma sum_sq_gaussianTheta_jacobiSym_le (hη : 0 < η) : ∃ C, ∀ T > (0 : ℝ), ∀ t ≥ T⁻¹,
    ∀ X : ℕ, X ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ 1) → ∑ v ∈ Ioc 0 X,
    ‖gaussianTheta j (fun n ↦ c n * J(-v | n)) t‖ ^ 2 ≤ C * (T ^ 2 * t ^ (-1 - 2 * η)) := by
  have b v m : ‖(J(v | m) : ℂ)‖ ≤ 1 := mod_cast by grind [trichotomy]
  have R l (hl : 0 < l) : ∃ C > 0, ∀ x > 0, |gaussianMonomial j x| ≤ C * x ^ (-l : ℝ) :=
    ⟨3 * l ^ l, by bound, fun x hx ↦ (norm_gaussianMonomial_le hx.le).trans (by
    have := log_le_self (div_pos hx hl).le
    simp (disch := positivity) [← log_le_log_iff, le_div_iff₀] at *; linarith)⟩
  obtain ⟨⟨A, _, hA⟩, ⟨B, _, hB⟩, Z, w⟩ := R (1 / 2 + η) (by bound), R (3 / 2 + η) (by bound),
    summable_pnat_iff_summable_nat.2 (summable_nat_rpow.2 (by bound : -1 - η / 2 < _)).norm,
    (fun v ↦ v.mul_norm (v.mul_norm v)) (summable_nat_rpow.2 (by bound : 2 * -(1 / 2 + η) < _)).norm
  refine ((summable_sum (s := {1, 2}) fun (k : ℕ+) _ ↦ ((w.hasSum.tsum_fiberwise fun (a, b, u) ↦
    ((b * (b * a) / k).toPNat', (a * u ^ 2).toPNat')).summable.mul_left (A ^ 2 * k ^ (1 / 2 + η))
    ).norm).add ((Z.mul_norm Z).mul_left ((2 * B) ^ 2 * rexp η / η))).imp
    fun K L T hT t h X hX c hc ↦ ?_
  have ht : 0 < t := by grw [h]; bound
  refine .trans (by simpa [mul_conj'] using mod_cast le_norm_self _) ((hasSum_sum
    (s := Ioc 0 X) fun v _ ↦ (fun s ↦ s.hasSum.mul s.hasSum.star (s.norm.mul_norm s.star.norm
    ).of_norm) (@summable_and_norm_gaussianTheta_le j _ t (fun n ↦ mul_one (1 : ℝ) ▸
    norm_mul_le_of_le (hc n) (b (-v) n)) ht).1).norm_le_of_bounded (L.mul_right _) fun (n, m) ↦ ?_)
  conv_lhs => simp [mul_right_comm _ _ (ofReal _), mul_mul_mul_comm _ (Int.cast _), ← Int.cast_mul,
    ← mul_right, ← mul_sum]
  obtain ⟨k, i, r, e⟩ | k := em (∃ k ∈ ({1, 2} : Finset ℕ+), IsSquare (k * (n * m) : ℕ))
  obtain ⟨g, p, u, o, s, f, rfl⟩ := exists_coprime' (by simp : 0 < gcd (k * n) r)
  obtain ⟨a, rfl⟩ : p ∣ g := (s.pow_right 2).dvd_mul_left.1 ⟨m, Nat.mul_left_cancel o (by grind)⟩
  map_tacs [grw +useKAbstract [hc, hc, hA, hA, norm_sum_le_of_le _ fun _ _ ↦ b .., show ∑ _ ∈ _, _ ≤
    T ^ 2 by simpa, ← norm_nonneg, ← single_le_sum _ i, ← le_norm_self, ← Summable.le_tsum (by apply
    w.subtype) ⟨(a, p, u), by simp [← f, show a * u ^ 2 = m from Nat.mul_left_cancel (mul_pos o o)
    (by grind)]⟩, ← mul_rpow, ← mul_rpow, rpow_mul, show _ ^ (2 : ℝ) = (k * (n * m) : ℝ) by
    rify at e; simp; grind]; (simp at k; grw +useKAbstract [hc, hc, hB, hB,
    norm_sum_jacobiSym_le _ k.1
    k.2, show 1 + _ = (rexp 1 * (n * m)).log by simp, log_le_rpow_div (ε := η / 2), ← sum_nonneg])]
  all_goals simp (disch := positivity) [← log_le_log_iff, mul_nonneg] <;>
    linarith [T.log_inv, log_le_log (by bound) h]
lemma sum_thetaTailIntegral_le (hη : 0 < η) : ∃ C, ∀ T > (0 : ℝ), ∀ X : ℕ, X ≤ T ^ 2 → ∀ c : ℕ → ℂ,
    (∀ n, ‖c n‖ ≤ 1) → ∑ v ∈ Ioc 0 X, thetaTailIntegral j (fun n ↦ c n * J(-v | n)) T⁻¹ ≤ C * T ^
  (2 + η) := (sum_sq_gaussianTheta_jacobiSym_le j hη).imp' (√· / η) fun C H T hT X hX c hc ↦ by
  grw [← sum_filter_of_ne fun _ _ ↦ mt integral_undef, ← integral_finsetSum,
    setIntegral_mono_of_nonneg _ (fun t ht ↦ ?_) ((integrableOn_Ioi_rpow_of_lt (a := -1 + -η)
    ..).const_mul (√C * T ^ 2)), integral_const_mul, integral_Ioi_rpow_of_lt]
  any_goals have := (inv_pos.2 hT).trans ht; nth_grw 1 [filter_subset, ← sum_div,
    le_sqrt_of_sq_le sq_sum_le_card_mul_sum_sq, show #_ ≤ T ^ 2 by simpa, H T hT t ht.le]
  all_goals simp (disch := positivity) [inv_rpow, rpow_sub, rpow_neg, two_mul, rpow_add, field, *]
  intros; positivity
lemma zero_density_quadTwist (hη : 0 < η) (y : ℝ) : (fun x : ℕ ↦ (#{d ∈ Ioc 0 x |
    ∃ _ : Fact d.Prime, d % 8 = 7 ∧ N.Coprime d ∧ ∃ s, 1 / 2 + 9 * η ≤ re s ∧ |im s| ≤ y ∧
    entireL (quadTwist ξ d) s = 0} : ℝ)) =O[atTop] fun x ↦ (x : ℝ) ^ (1 - η / 2) := by
  obtain ⟨M, f, ψ, _, e, rfl⟩ := exists_isPrimitive_changeLevel_eq ξ
  obtain ⟨j, hp⟩ : ∃ j : Fin 2, ψ (-1) = -(-1) ^ j.1 := by simpa using! ψ.even_or_odd.symm
  obtain ⟨⟨K, hK⟩, ⟨C, hC⟩, c, c0, hc⟩ := three_lines_bound_of_LFunction_eq_zero j,
    sum_thetaTailIntegral_le j hη, @exists_pos_le_norm_gaussianMellin j
    (.Icc 2⁻¹ 1 ×ℂ .Icc (-y) y) (isCompact_Icc.reProdIm isCompact_Icc) (by grind [mem_reProdIm])
  refine .of_bound (2 * C * M ^ (1 - η / 2)) ((((tendsto_rpow_atTop hη).eventually_gt_atTop
    (K / c ^ 2)).natCast_atTop.and (Ioi_mem_atTop 0)).mono fun x ⟨hx, x0⟩ ↦ ?_)
  obtain ⟨T, T0, hT⟩ : ∃ T > 0, T ^ 2 = (M * x : ℝ) := ⟨√_, by simpa, sq_sqrt (by simp)⟩
  have hX : x ≤ T ^ 2 := by simp [succ_le_iff, *]
  rw [Real.norm_natCast, ← mul_le_mul_iff_left₀ (rpow_pos_of_pos T0 (2 * η)), ← nsmul_eq_mul,
    ← sum_const, sum_filter]
  refine .trans (sum_le_sum fun d hd ↦ ?_) ((sum_add_distrib.trans_le (add_le_add (hC T T0 x hX
    (ψ ·) (by simp)) (hC T T0 x hX _ (norm_mul_moebius_le_one ψ)))).trans_eq (by simp (disch :=
    bound) [mul_assoc, abs_of_nonneg, ← mul_rpow, ← hT, ← rpow_natCast_mul, ← rpow_add]; ring_nf))
  split <;> [obtain ⟨_, h8, co, s, s₀, s₁, z⟩ := ‹_›; positivity]
  contrapose! hx
  obtain ⟨h, r⟩ := co.of_dvd_left f, le_of_not_ge (entireL_ne_zero _ · z)
  have h1 ξ := quadTwist_ne_one ξ d (by omega) h
  simp [entireL, h1, show quadTwist (ψ.changeLevel f) d = (quadTwist ψ d).changeLevel (by gcongr) by
    simp [quadTwist, ← changeLevel_trans], LFunction_changeLevel,
    prod_euler_factor_ne_zero _ (by bound : s.re ≠ 0)] at z
  grw [hX, ← rpow_natCast_mul, le_div_comm₀, hc s ⟨⟨by bound, r⟩, abs_le.1 s₁⟩, hK hη _ (h1 ψ) (by
    simpa (disch := omega) [hp, legendreSym.at_neg_one, ↓χ₄_nat_three_mod_four] using
    quadTwist_apply ψ d (-1)) T0 (by simp [hT, mem_Ioc.1 hd])] <;> try bound
  · have E {n : ℕ} (h : n ≠ 0) : quadTwist ψ d n = ψ n * J(-d | n) := by
      let ⟨k, m, hm, e⟩ := exists_eq_two_pow_mul_odd h
      simpa [hm.pos.ne', mul_left, pow_left, at_two, qrSign, mul_right', pow_right, mod_left (-d) 2,
        *, Int.odd_iff.1, jacobiSym.neg, to_jacobiSym, quadratic_reciprocity' hm, ← natCast_mod,
        odd_iff, (by omega : d % 2 = 1 ∧ d % 4 = 3)] using quadTwist_apply ψ d n
    simpa [thetaTailIntegral, gaussianTheta, E, mul_right_comm] using hx.le
  clear * - e h h1
  have H B := (conductor_mul_dvd_lcm_conductor (quadTwist ψ d) B⁻¹).trans (Nat.lcm_dvd_mul ..)
  obtain := H (quadTwist 1 d), H (ψ.changeLevel ⟨d, rfl⟩), h1 1,
    (@quadTwist 1 1 d _).conductor_dvd_level, (quadTwist ψ d).conductor_dvd_level.antisymm
  simp_all [quadTwist, dvd_prime Fact.out, mul_comm, h.dvd_mul_left, eq_one_iff_conductor_eq_one,
    h.symm.dvd_mul_left, conductor_inv, h.mul_dvd_of_dvd_of_dvd, conductor_changeLevel, IsPrimitive]
lemma exists_entireL_quadTwist_ne_zero {β} y {a : ZMod N} (hβ : 1 / 2 < β) (ha : IsUnit a) (H :
  ∀ d : Primes, d = a → d.1 % 8 = 7 ∧ N.Coprime d) : ∃ d : Primes, d = a ∧ ∀ ξ s,
  β ≤ re s → |im s| ≤ y → entireL (@quadTwist
  N ξ d _) s ≠ 0 := (exists_pos_mul_lt (lt_min one_pos (sub_pos.2 hβ)) 9).elim fun η ⟨hη, h⟩ ↦ by
  by_contra!
  refine not_summable_residueClass_prime_div ha ((LSeriesSummable_logMul_of_lt_re (s := 1)
    ((LSeriesSummable_of_sum_norm_bigO (s := 1 - η / 2 / 2) (f := fun n ↦ ite (n.Prime ∧ n = a) 1 0)
    (.trans (.of_norm_le fun x ↦ ?_) (.fun_sum (s := ⊤) fun ξ _ ↦ @zero_density_quadTwist N _ ξ _ hη
    y)) (by grind) (by simpa)).abscissaOfAbsConv_le.trans_lt (mod_cast by simpa))
    ).norm.of_norm_bounded (by simp +contextual [Set.indicator, term, apply_ite, ite_and,
    ← natCast_log, vonMangoldt_apply_prime]))
  simp [apply_ite norm, ← cast_sum]
  grw [← card_biUnion_le, card_le_card]
  simp_all [Primes, subset_iff]; grind
