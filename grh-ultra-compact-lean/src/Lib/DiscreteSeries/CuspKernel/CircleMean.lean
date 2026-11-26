import Lib.General.Analysis.ZpowSum
open BoundedContinuousFunction Complex ComplexConjugate ENNReal MeasureTheory ProbabilityTheory
variable {Z W X} [MeasurableSpace Z] [MeasurableSpace W] {μ : Measure Z} {ν : Measure W} [NormedAddCommGroup X] {F : Z → X}
structure IsBoundedMeasurable (F : Z → X) where
 stronglyMeasurable : StronglyMeasurable F
 bounded : ∃ C, ∀ y, ‖F y‖ ≤ C
attribute [fun_prop] IsBoundedMeasurable.stronglyMeasurable
instance : Fact (1 ≠ ∞) := ⟨nofun⟩
lemma IsBoundedMeasurable.of [TopologicalSpace Z] [BorelSpace Z] [SecondCountableTopology Z] (h : ∃ C, ∀ y, ‖F y‖ ≤ C) (c : Continuous F := by fun_prop) : IsBoundedMeasurable F := ⟨c.stronglyMeasurable, h⟩
lemma IsBoundedMeasurable.comp (h : IsBoundedMeasurable F) (j : W → Z) (m : Measurable j := by fun_prop) : IsBoundedMeasurable (F <| j ·) := ⟨by fun_prop, h.2.imp (by tauto)⟩
lemma IsBoundedMeasurable.memLp_top (h : IsBoundedMeasurable F) : MemLp F ∞ μ := memLp_top_of_bound ⟨_, h.1, .rfl⟩ _ (.of_forall h.2.choose_spec)
lemma IsBoundedMeasurable.integrable_mul_comp {F : Z → ℂ} (h : IsBoundedMeasurable F) {c} (i : Integrable c ν) j (m : Measurable j := by fun_prop) : Integrable (fun a ↦ c a * F (j a)) ν := i.mul_of_top_left (h.comp j).memLp_top
lemma sq_lintegral_le {f g h} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (e : ∀ x, h x ^ 2 ≤ f x * g x) : lintegral μ h ^ 2 ≤ lintegral μ f * lintegral μ g := by simp_all [-rpow_ofNat, ← rpow_two, ← le_rpow_inv_iff, mul_rpow_of_nonneg]; grw [e, lintegral_mul_norm_pow_le] <;> bound
variable [SFinite μ] [SFinite ν] {G} [Group G] [TopologicalSpace G] [MeasureSpace G] {e : G → ℂ}
lemma MeasureTheory.MeasurePreserving.fubini {Y} [MeasurableSpace Y] [NormedSpace ℝ X] {ρ T f} (m : MeasurePreserving T (ν.prod μ) ρ) (h : Integrable f ρ) : Integrable (f ∘ T) (ν.prod μ) ∧ ∫ k, ∫ g, f (T (k, g) : Y) ∂μ ∂ν = (integral ρ f : X) := by simp [← m.hasLaw.integral_comp, ↓integral_prod, m.integrable_comp, h, h.1]
lemma integral_skew_product [NormedSpace ℝ X] {T : W → _} (h : ∀ k, μ.map (T k) = μ) {f} (hf : Integrable f (ν.prod μ)) (t : Measurable T.uncurry := by fun_prop) : zeta% let A g : X := ∫ k, f (k, T k g) ∂ν
  Integrable A μ ∧ integral μ A = ∫ k, ∫ g, f (k, g) ∂μ ∂ν := integral_prod _ hf ▸ ((((MeasurePreserving.id ν).skew_product t (by aesop)).comp μ.measurePreserving_swap).fubini hf).imp_left (·.integral_prod_left)
lemma integral_conv [Group Z] [MeasurableMul₂ Z] [MeasurableInv Z] [μ.IsMulLeftInvariant] [NormedSpace ℂ X] [CompleteSpace X] j {k α : _ → ℂ} (hk : Integrable k ν) (hα : Integrable α μ) (hF : IsBoundedMeasurable F) (hj : Measurable j := by fun_prop) : beta% (fun B ↦ B = ∫ g, α g • ∫ x, k x • F (j x * g) ∂ν ∂μ ∧ B = ∫ g, (∫ x, k x * α ((j x)⁻¹ * g) ∂ν) • F g ∂μ) (∫ x, k x • ∫ g, α g • F (j x * g) ∂μ ∂ν) := have i := (hk.mul_prod hα).smul_of_top_left (hF.comp (j · * ·).uncurry).memLp_top
  by simpa [← integral_smul, integral_smul_const, smul_smul, mul_comm] using And.intro
      (integral_integral_swap i) (integral_skew_product (map_mul_left_eq_self μ <| j⁻¹ ·) i).2.symm
structure IsIdempotentKernel (e : G → ℂ) where
 continuous : Continuous e
 integrable : Integrable e
 apply_inv g : e g⁻¹ = conj (e g)
 apply_one_ne_zero : e 1 ≠ 0
 convolution_eq x y : ∫ z, e z * e ((z * x)⁻¹ * y) = e x⁻¹ / e 1 * e y
lemma IsIdempotentKernel.convolution_self (h : IsIdempotentKernel e) y : ∫ z, e z * e (z⁻¹ * y) = e y := by simpa [h.4] using h.5 1 y
attribute [-instance] SubfieldClass.toSubringClass in
attribute [-simp] map_mul norm_pow in
attribute [local simp] norm_coe_le_norm DFunLike.ext_iff Prod.mul_def mul_add mul_assoc mul_le_mul_of_nonneg_left sub_mul in
lemma integral_idem_mul_eq_zero [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [BorelSpace G] [(@volume G _).IsHaarMeasure] (H ℓ : G → ℝ) (D : Subgroup _) (k : IsIdempotentKernel e) (hℓ : Integrable fun g ↦ ‖e g‖ * ℓ g) (hH : Continuous H) (hl : ∀ x g, |H (x * g) - H x| ≤ ℓ g) (hP : ∀ z ∈ D, ∀ g, H (z.1 * g) = -‖z.2.1‖.log + H g) (hb : ∀ W ∈ nhds 1, ∃ c : ℂˣ, ‖c.1‖.log ≠ 0 ∧ ∀ x, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D) (f : G →ᵇ ℂ) (hN : ∀ r, (r, 1) ∈ D → ∀ g, f (r * g) = f g) x : ∫ g, e g * f (x * g) = 0 := by
  have he := k.2
  choose hi hd using fun {k} (hk : Integrable k) (f : G →ᵇ ℂ) x ↦ And.intro ((IsBoundedMeasurable.of ⟨_, f.norm_coe_le_norm⟩).integrable_mul_comp hk (x * ·)) (by
    grw [L1.norm_of_fun_eq_integral_norm, ← integral_mul_const, norm_integral_le_of_norm_le]
    fun_prop; simp : ‖∫ g, k g * f (x * g)‖ ≤ ‖hk.toL1‖ * ‖f‖)
  let T := (⟨⟨fun f ↦ ofNormedAddCommGroup _ (continuous_of_dominated (by fun_prop) (by simp) (he.norm.mul_const ‖f‖) (.of_forall (by fun_prop))) _ (hd he f), by simp [*, integral_add]⟩, by
    simp [mul_left_comm]⟩ : _ →ₗ[ℂ] _).mkContinuous _ (norm_le_of_nonempty.2 <| hd he ·)
  choose τ hτ b hW hb using hb _ ((by fun_prop : ContinuousAt (DomMulAct.mk ·⁻¹ • he.toL1) _) (Metric.ball_mem_nhds _ one_half_pos)); obtain ⟨ha, n, h0, hn⟩ := by simpa using And.intro (hb 1) (exists_nat_gt (0 ⊔ ∫ g, ‖.pi / ‖τ.1‖.log‖ * ‖e g‖ * ℓ g))
  let m := ofNormedAddCommGroup (circleMap 0 1 <| H · * ((↑n)⁻¹ * (.pi * ‖τ.1‖.log⁻¹))) (by
    fun_prop) 1 (by simp)
  let p := T.eqLocus 1 ⊓ ⨅ r ∈ D.comap (.inl ..), (compContinuousCLM _ _ (.mulLeft r)).eqLocus 1; have V f : T (T f) = T f := by simpa [k.convolution_self, T] using fun x ↦ (_root_.integral_conv id he he (.of ⟨_, (f.norm_coe_le_norm <| x * ·)⟩)).2
  let U : p →L[ℂ] p := (compContinuousCLM _ _ (.mulLeft (b 1))).restrict fun f k ↦ by
    simp_all +zetaDelta [← mul_assoc]; intros; convert k.2 _ (by simpa using mul_mem (mul_mem ha ‹_›) (inv_mem ha)) _ using 2; simp
  let S : p →L[ℂ] p := (T * .mul _ _ m).restrict fun f k ↦ ⟨V _, by simp_all +zetaDelta [hP (_, 1)]⟩; have w := (1 - U).opNorm_le_bound one_half_pos.le fun ⟨f, k, l⟩ ↦ norm_le_of_nonempty.2 fun x ↦
    show ‖f x - f _‖ ≤ _ * ‖f‖ by
    simp_all [T]; grw [← hW]; simpa [dist_eq_norm', ← mul_assoc, *, integral_sub, he.comp_mul_left, ← l _ (by simpa using div_mem (hb x) ha) (_ * x), ← integral_mul_left_eq_self (fun g ↦ e (_ * g) * _) (b x)] using! hd (he.sub (he.comp_mul_left (b x)⁻¹)) f x
  have := (by simpa [((by ext; simp [U, S, T, ← integral_const_mul, *, hP _ ha, add_mul, exp_add, m, circleMap, mul_left_comm] : SemiconjBy U S (exp ((↑n)⁻¹ * Real.pi * -I) • S)).pow_right n).eq, mul_sub, smul_pow, ← exp_nat_mul, h0.ne', field, mul_two, SameRay.rfl.norm_add] using norm_add_le_of_le (norm_mul_le_of_le w (refl ‖S ^ n‖)) (norm_mul_le_of_le le_rfl w)); refine congr($((Function.Injective.of_ker S fun ⟨f, k, _⟩ h ↦ Subtype.ext (norm_le_zero_iff.1 (le_imp_le_of_lt_imp_lt (mul_lt_mul_of_pos_right hn) ((le_div_iff₀' (by simpa)).1 (norm_le_of_nonempty.2 fun x ↦ .trans (b := ‖T (m * f - m x • f) x‖) ?_ ?_))))).iterate _ ((this _ ⟨V f, by simp_all [T]⟩).trans (iterate_map_zero ..).symm)).1 x); simpa [(congr($h) : T (m * f) = 0), m] using congr(‖$k x‖).ge; rw [← mul_div, mul_right_comm, ← integral_const_mul]; apply norm_integral_le_of_norm_le; fun_prop; simp [← sub_mul, m]; grw [(lipschitzWith_circleMap 0 1).norm_sub_le, ← hl]; simp [field, ← sub_mul]
lemma integral_eq_of_circle_mean {μ} [SFinite μ] {f g : W → ℂ} {T : UnitAddCircle → _} (hT : ∀ θ, μ.map (T θ) = μ) (hi : Integrable f μ) (h : ∀ x, ∫ θ, f (T θ x) = g x) (c : Measurable T.uncurry := by apply Continuous.measurable; fun_prop) : μ[f] = μ[g] := by simp [← h, integral_skew_product hT (hi.comp_snd _), Measure.real]
lemma integral_toCircle {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.closedBall 0 |1|)) : ∫ θ : UnitAddCircle, f θ.toCircle = f 0 := by simpa [Real.circleAverage, circleMap, AddCircle.toCircle, -Circle.coe_exp, ← AddCircle.intervalIntegral_preimage 1 0, intervalIntegral.integral_comp_mul_left (f <| Circle.exp ·)] using! (hf.diffContOnCl_ball .rfl).circleAverage
lemma le_of_halving {X} {f : X → ℝ} {c B} (hB : ∀ x, f x ≤ B) (hc : 0 ≤ c) (h : ∀ M ≥ 0, (∀ x, f x ≤ M) → ∀ x, f x ≤ M / 2 ∨ f x ≤ c) x : f x ≤ c := have := le_ciSup ⟨B, Set.forall_mem_range.2 hB⟩; by grind [Real.iSup_le (le_max_iff.2 <| h |iSup f| (by simp) (by grind) ·) (by bound)]
