import Lib.General.Algebra.AdicRingHomExt
import Lib.General.Algebra.JetChainRule
section
open Nat PowerSeries WithPiTopology
variable {p : ℕ} [hp : Fact p.Prime] {σ} {c : ℂ_[p]} (a : MvPowerSeries σ ℂ_[p]) {n K : ℕ}
noncomputable abbrev expSubst := (exp ℂ_[p]).subst a
@[simp] lemma constantCoeff_subst_mv (ha : a.constantCoeff = 0) f : (subst a f).constantCoeff =
    constantCoeff f := by simp_all [constantCoeff_subst, finsum_eq_single _ 0]
lemma expSubst_add {b} (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) : expSubst (a + b) =
  expSubst a * expSubst b := by apply inv_unique (x :=
  expSubst (-a - b)) <;> apply MvPowerSeries.pderiv.ext <;> simp [*] <;>
  simp [subst, ← derivative.eq_def, derivative_exp, *] <;> grind
lemma expSubst_sum {I t} {a : I → _} (h : ∀ i, (a i).constantCoeff = 0) : expSubst (t.sum a) =
  ∏ i ∈ t, @expSubst p _ σ (a i) :=
  t.cons_induction (by simp [subst_zero_eq_C_constantCoeff]) (by simp_all [expSubst_add])
lemma norm_natCast_eq_inv_pow_padicValNat : n ≠ 0 → ‖(n : ℂ_[p])‖ = (↑p)⁻¹ ^ padicValNat p n :=
    (by simpa [Padic.norm_eq_zpow_neg_valuation, ·] using PadicComplex.norm_extends' p n)
lemma padicValNat_factorial_mem_Icc (hn : n < p ^ K) : ↑(padicValNat p n !) ∈
    Set.Icc ((n : ℝ) / (p - 1) - K) (n / (p - 1)) := have := hp.1.one_lt; by
  simp_all [div_le_iff₀', le_div_iff₀', ← cast_pred this.le, ← digits_length_le_iff]; norm_cast
  grw [mul_add, sub_one_mul_padicValNat_factorial, List.sum_le_length_nsmul _ (p - 1), hn] <;>
    grind [→ digits_lt_base]
lemma rpow_le_norm_factorial :
  p ^ (-(n / (p - 1)) : ℝ) ≤ ‖(n ! : ℂ_[p])‖ := by grw [norm_natCast_eq_inv_pow_padicValNat,
  ← (padicValNat_factorial_mem_Icc (n.lt_pow_self Fact.out)).2] <;> simp [NeZero.one_le]
@[simp] lemma subst_rescale_eq_subst_smul (h : HasSubst a) f : (rescale c f).subst a = f.subst (c •
  a) := by rw [rescale_eq_subst, subst_comp_subst_apply (.smul_X' c) h, subst_smul h, subst_X h]
variable {d} (C : CMLattice d) {K : Type*} [Field K] (ι : ℂ →+* K) {p : ℕ}
  [Fact p.Prime] {x y : ℂ_[p]} [Fact n.Prime]
namespace CMLattice
@[simp ↓] lemma constantCoeff_taylorVia f :
    constantCoeff (taylorVia ι f) = ι (f 0) := congr(ι $constantCoeff_taylorAtZero)
lemma derivative_taylorVia [CharZero K] f : d⁄dX (taylorVia ι f) = taylorVia ι (deriv f) := ext
    (by simp [coeff_derivative, iteratedDeriv_succ', factorial, field])
attribute [local simp] CMLattice.derivative_taylorVia map_ofNat taylorVia sub_eq_add_neg
lemma taylorAtZero_congr {f g} (h : ∀ z, z + C.t ∉ C.Λ → f z = g z) : taylorAtZero f =
  taylorAtZero g := congr(.mk ($(Set.EqOn.iteratedDeriv_of_isOpen h
  C.isClosed_lattice.1.preimage_of_continuous · (C.t_notMem ∘ by simp)) / _))
lemma taylorVia_curve_eq : taylorVia ι C.translatedWpDeriv ^ 2 + .C (ι C.a₁) * taylorVia ι
  C.translatedWp * taylorVia ι C.translatedWpDeriv = taylorVia ι C.translatedWp ^ 3 + taylorVia ι
  C.translatedWp := by
  simpa (disch := fun_prop) using congr(map ι $(C.taylorAtZero_congr @C.weierstrass_equation))
@[simp] lemma derivative_taylorVia_translatedWp [CharZero K] :
    d⁄dX (taylorVia ι C.translatedWp) = 2 *
  taylorVia ι C.translatedWpDeriv + .C (ι C.a₁) * taylorVia ι C.translatedWp := by
  simp (disch := fun_prop) [funext C.deriv_translatedWp]
@[simp] lemma derivative_taylorVia_translatedWpDeriv [CharZero K] :
    d⁄dX (taylorVia ι C.translatedWpDeriv) =
  1 + 3 * taylorVia ι C.translatedWp ^ 2 - .C (ι C.a₁) * taylorVia ι C.translatedWpDeriv := by
  simp (disch := fun_prop) [← neg_mul, C.taylorAtZero_congr @C.deriv_translatedWpDeriv_eq]
end CMLattice
section
open IsUltrametricDist QuadField NumberField PeriodPair Submodule
lemma CMLattice.norm_disc_eq_one [PrimeSevenModEight d] (ι : ℂ →+* ℂ_[p]) : ‖ι
  C.a₁ ^ 4 - 64‖ = 1 := by
  let v C := (@periodPair d C).G 4 / C.sumInvPow (C.t - quadGen d * C.t) 4 * 240 - 16
  let a x := ‖ι (v x)‖
  refine (Finset.prod_induction_nonempty (fun _ : ClassGroup (𝓞 (QuadField d)) ↦ .mk0 (1 +
    .spanSingleton _ (c₀ d / -2)) (by simp [-map_div₀])) (fun 𝔠 ↦ ∀ C D,
    (∃ u, latticeModule D = scaledIdeal d (u, 𝔠) * latticeModule C) → (a C =
    a D → ‖ι C.a₁ ^ 4 - 64‖ = 1) ∧ (‖ι 4096‖ ≤ a D ∧ a C ∉ Set.Ioo 1 (a D) ↔ a C ∈ Set.Icc (a D) 1))
    (fun _ 𝔠 k _ C D ⟨v, e⟩ ↦ have ⟨E, w, _⟩ := C.exists_latticeModule_eq_scaledIdeal_mul 𝔠
    by grind [map_ofNat, norm_natCast_le_one ℂ_[p] 4096, k E D ⟨v / w, by simp [*, ← mul_assoc,
      ← map_mul]⟩]) Finset.univ_nonempty (fun _ _ C D ⟨u,
    hf⟩ ↦ ?_) C C (exists_eq_scaledIdeal_mul_of_mk_eq_one (by simp [-map_div₀]) _)).1 rfl
  let b := C.a₁ ^ 4 - 64
  suffices H : v D = b * -v C ∧ (48 + v C + b) * -v D = 4096
  simp [a, ← H.2, H, show v C ≠ 0 ∧ b ≠ 0 by grind]
  grind [map_ofNat, norm_add_le_max, norm_add_eq_max_of_norm_ne_norm, norm_natCast_le_one ℂ_[p] 48]
  rcases C.quadGen_mul_t_notMem, @conj_quadGen, C.two_t_mem, C.t_notMem,
    D.mul_mem_or_mul_sub_t_mem (.inr rfl) (u * C.t)
  set T := quadGen _ * _
  replace hf x : u.1 * x ∈ D.Λ ↔ x + T ∈ C.Λ ∨ x ∈ C.Λ := .trans (b := ∃ l ∈ C.Λ, ∃ m ∈ C.Λ,
    l + quadGen d / -2 * m = x) (by simpa [scaledIdeal, map_span, one_eq_span, Submodule.sup_mul,
    mul_assoc, mem_span_singleton_mul, -map_div₀] using! congr(u * x ∈ $hf)) ⟨fun ⟨l, hl, m, _⟩ ↦ by
    grind [→ sub_mem hl, C.mul_mem_or_mul_sub_t_mem (.inl rfl) (m / 2)], by grind [C.Λ.zero_mem]⟩
  have S y z (h : u.1 * y - z ∈ D.Λ) := have k L (y : ℂ) := (Equiv.addLeft y).hasSum_iff.2 ((
    hasSum_subtype_iff_indicator (f := ((· - y) ^ 4 :)⁻¹)).1 (hasSum_sumInvPow L y (by lia)))
    (u.mulLeft.hasSum_iff.2 (k D.1 z)).unique ((((k C.1 (T + y)).add (k C.1 y)).div_const (u ^ 4)
    ).congr_fun (by simp [Set.indicator]; grind [add_mem_cancel_left, =_ add_mem_cancel_left h]))
  simp (disch := grind) [S (C.t - T), by simpa using S 0 0, field]
  grind (ringSteps := 999999) [by simpa [θ_sq, field, *] using C.phiThetaCube_spec (-T) (by grind),
    translatedWp, g₂_eq, derivWeierstrassP_eq_zero_iff, → C.5 quadGen_mem_quadInt, a₁_sq,
    deriv_derivWeierstrassP, weierstrass_disc_ne_zero, g₂,
    → derivWeierstrassP_sq, → derivWeierstrassPExcept_of_notMem, deriv_derivWeierstrassPExcept_self]
lemma norm_lt_one_of_eq_mul_add_mul : ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ∀ {u v z}, z =
  x * u + y * v → ‖u‖ < 1 → ‖v‖ < 1 → ‖z‖ < 1 := by
    simp_all [(norm_add_le_max ..).trans_lt, mul_lt_one_of_nonneg_of_lt_one_right]
attribute [-simp] Asymptotics.isBigO_top sup_of_le_left sup_of_le_right
attribute [local simp] Asymptotics.IsBigO.add Asymptotics.IsBigO.const_mul_left
  Asymptotics.isBigO_zero thetaShift_apply CMLattice.monomialSection CMLattice.t_notMem abs_of_pos
  add_mem_cancel_left map_ofNat mul_assoc pow_le_one_iff_of_nonneg
variable [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p] (w)
lemma CMLattice.norm_a₁_le_one : ‖ιₚ C.a₁‖ ≤ 1 := by
    simpa using Valued.integer.mem_iff.1 (add_mem (C.norm_disc_eq_one _).le (ofNat_mem _ 64))
noncomputable abbrev CMLattice.naiveHeight := max ‖ιₚ (C.σ w)‖ ‖ιₚ (C.θ w)‖
lemma CMLattice.naiveHeight_spec : 0 < C.naiveHeight w ∧ C.naiveHeight (2 * w) =
  C.naiveHeight w ^ 4 ∧ ‖ιₚ (C.phiThetaCube w)‖ ≤ C.naiveHeight w ^ 3 := by
  obtain ⟨c, e, h⟩ : ∃ c ∈ [ιₚ (C.σ w), ιₚ (C.θ w)], C.naiveHeight w ≤ ‖c‖ := by grind
  have : c ≠ 0 := by aesop
  have D n x : c ^ n ∣ ιₚ x := by aesop
  obtain ⟨⟨a, _⟩, ⟨b, _⟩, ⟨g, _⟩, ⟨x, _⟩, u, v⟩ := D 1 (C.σ w), D 1 (C.θ w), D 3 (C.phiThetaCube w),
    D 4 (C.σ (2 * w)), congr(ιₚ $(C.σ_two_mul_sq w)), congr(ιₚ $(C.phiThetaCube_sq_add w))
  rw [h.antisymm (by aesop)]; simp [naiveHeight, *, field, ← mul_max_of_nonneg, mul_pow,
    ← mul_sub] at *
  refine ⟨eq_of_le_of_not_lt ?_ (mt max_lt_iff.1 fun _ ↦
    (norm_lt_one_of_eq_mul_add_mul ?_ ?_ (.refl ((a * b) ^ 2 |> fun
    w ↦ ιₚ C.a₁ ^ 2 - 8 * w |> fun B ↦ B * x * x + (B * (B + 12 * w) - 64) * (1 - w ^ 2))) ?_
    (by grind [norm_sub_rev])).ne (by grind [C.norm_disc_eq_one ιₚ])), by_contra (· ?_)⟩
  rw [max_le_iff, ← sq_le_one_iff₀, ← norm_pow, u]
  any_goals rw [eq_sub_of_add_eq ((eq_inv_mul_iff_mul_eq₀ (by bound)).2 v)]
  repeat' rw [← Valued.integer.mem_iff]
  repeat bound [(norm_inv g).trans_le (c := 1), C.norm_a₁_le_one]
lemma CMLattice.norm_monomialSection_le x w : ‖ιₚ (C.monomialSection x w)‖ ≤
  C.naiveHeight w ^ monomialDeg x := by simp [pow_add, pow_mul']; bound [C.naiveHeight_spec w]
lemma CMLattice.norm_translate_le_naiveHeight_pow {C' a g N m} (h : C.IsIsogeny (@periodPair d C') a
  N) y n (hn : n ≠ 0) (hl : n • y ∈ C'.Λ) (hg : ∀ w, ‖ιₚ (g w)‖ ≤ C'.naiveHeight w ^ m) z : ‖ιₚ
  (C'.twistedTranslate m y g (a * z))‖ ≤ C.naiveHeight z ^ (m * N) := by
  let r (C : CMLattice d) a N z := ‖ιₚ (C'.twistedTranslate 1 y 1 (a * z))‖ * C'.naiveHeight
    (a * z + y) / C.naiveHeight z ^ N
  have K {C a N} (H : r C' 1 1 ≤ 1 ⊔ r C a N) (h : C.IsIsogeny _ a N) : r C a N ≤ 1 :=
    have A {m g} : g ∈ C.sections m → (ιₚ <| g ·) =O[⊤] (C.naiveHeight ^ m) :=
      (span_induction (fun _ ⟨x, k, e⟩ ↦ e ▸ k.2 ▸ .of_norm_le (C.norm_monomialSection_le x))
      (by simp) (by simp_all) (by simp_all) <| sections_le_span_monomialSection _ _ ·)
    have B {f} k : (ιₚ <| C'.twistedTranslate 1 y f <| a * ·) =O[⊤] (C.naiveHeight ^ N) := .of_pow
      (by omega : n * 2 ≠ 0) ((A (C.comp_mul_mem_sections h (IsAppellHumbert.thetaShift_mem_of_dual
      (f := f ^ (n * 2)) (mem_dualLattice_nsmul.2 (isAppellHumbert_hermitianForm.le_dualLattice
      (mul_nsmul y .. ▸ nsmul_mem hl 2))) k))).congr (by simp [↓thetaShift_pow])
      (by simp [pow_mul']))
    le_ciSup (((B (by simpa [← pow_mul'] using monomialSection_mem _ (0, n, 0))).prod_left (B
    (by simpa using monomialSection_mem _ (_, 0)))).bound.imp (by simp [upperBounds, r,
      div_le_iff₀, ↓naiveHeight_spec,
      mul_max_of_nonneg])) |> fun b z ↦ (b z).trans (not_lt.1 fun h ↦ (pow_lt_pow_right₀ h
    (by decide : 2 < 4)).not_ge ((Real.iSup_pow (by bound) 4).trans_le (ciSup_le fun z ↦ by
    grw [sq, ← b (2 * z), ← (H _).trans (max_le h.le (b (a * (2 * z) + y)))]
    simp [(naiveHeight_spec ..).1.ne', field, ← (naiveHeight_spec ..).2.1, pow_right_comm _ N,
      ← norm_pow, ← norm_mul, ← map_pow, ← map_mul, ← Complex.exp_nsmul, ← Complex.exp_add]
    ring; rfl)))
  grw [pow_mul', ← (div_le_one _).1 (K (le_sup_of_le_left (K _ _)) h z), mul_pow, ← hg] <;> simp
    [↓naiveHeight_spec, ← norm_pow, ← map_pow, ← Complex.exp_nsmul, ← mul_div]
end
attribute [-simp] RingHomCompTriple.comp_apply add_eq_zero
def IsSeriesGenerator (A : Subring ℂ_[p]⟦X⟧) T := constantCoeff T = 0 ∧ T.coeff 1 = 1 ∧ ∀ f, f ∈ A ↔
  ∃ g : (valRingCp p)⟦X⟧, f = subst T (seriesToCp g)
variable {a c : ℂ_[p]} {B} {T : ℂ_[p]⟦X⟧} (h : IsSeriesGenerator B T) (k :
  T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧}
@[simp] lemma constantCoeff_rescale : (rescale a f).constantCoeff =
  f.constantCoeff := by simp [rescale]
@[simp] lemma rescale_smul : rescale a (c • f) = c • rescale a f := ext (by simp [field])
@[simp] lemma constantCoeff_subst_eq (k : T.constantCoeff = 0) :
    constantCoeff (f.subst T) = f.constantCoeff := constantCoeff_subst_mv _ k f
attribute [local simp ↓] IsSeriesGenerator HasSubst.of_constantCoeff_zero' coe_substAlgHom
  constantCoeff_substInvOfIsUnit isUnit_iff_constantCoeff map_subst subst_X subst_comp_subst_apply
  subst_smul subst_substInvOfIsUnit_left subst_substInvOfIsUnit_right mul_le_one₀
include k in
@[simp ↓] lemma coeff_one_subst : coeff 1 (f.subst T) = f.coeff 1 * T.coeff 1 := by
  rw [coeff_subst', finsum_eq_single _ 1] <;> simp_all [coeff_one_pow]; lia
lemma rescale_subst (k : T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧} :
    rescale a (f.subst T) = f.subst (rescale a T) := by simp_all [rescale_eq_subst]
@[fun_prop] lemma continuous_subst (h : HasSubst T) : Continuous (subst (R := ℂ_[p]) T) :=
  continuous_pi fun α ↦ .congr (by simp [finsum_eq_sum_of_support_subset_of_finite _ _
    ((@mk ℤ 1).coeff_subst_finite h α)]; fun_prop [coeff]) (coeff_subst h · α |>.symm)
include h
lemma IsSeriesGenerator.exists_subst_inverse : ∃ Z :
    ℂ_[p]⟦X⟧, constantCoeff Z = 0 ∧ subst Z T = X ∧ subst T Z = X ∧ ∀ {f}, f ∈ B ↔ subst Z f ∈
    seriesToCp.range :=
  ⟨T.substInvOfIsUnit (by aesop), h.elim (by aesop (add safe (by apply exists_congr)))⟩
lemma IsSeriesGenerator.generator_mem : T ∈ B := (h.2.2 T).2 ⟨X, by simp_all [← map.eq_def]⟩
lemma IsSeriesGenerator.smul_mem : ‖c‖ ≤ 1 → f ∈ B → c • f ∈ B :=
  h.exists_subst_inverse.elim (by simp_all [↓mem_range_seriesToCp])
lemma IsSeriesGenerator.norm_coeff_le_one : f ∈ B → ‖f.constantCoeff‖ ≤ 1 ∧ ‖f.coeff 1‖ ≤ 1 := by
  simp_all; use fun g _ ↦ ⟨(g 0).2, (g _).2⟩
lemma IsSeriesGenerator.of_mem : f ∈ B → f.constantCoeff = 0 → f.coeff 1 = 1 →
  IsSeriesGenerator B f := by
  simp_all [coeff]; introv _ _ _
  rw [(id (⟨subst (substInvOfIsUnit x _) ·, _⟩) : (subst x).Surjective).exists] <;>
    simp_all [constantCoeff, map]
lemma IsSeriesGenerator.exists_mul_eq_one : f ∈ B → ‖f.constantCoeff‖ = 1 → ∃ v ∈ B, f * v = 1 := by
  simp_all; use fun _ _ _ ↦ (isUnit_iff_exists_inv.1
    (by simpa)).imp (by simp_all [← coe_substAlgHom, ← map_mul])
lemma IsSeriesGenerator.rescale_mem : rescale a T ∈ B → f ∈ B → rescale a f ∈ B := by
  simp_all; use fun u e g _ ↦ ⟨g.subst u, have := e ▸ constantCoeff_rescale
    by simp_all [constantCoeff, map, rescale_subst]⟩
variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p]
noncomputable def CMLattice.phiSeriesRing : Subring ℂ_[p]⟦X⟧ :=
  ((substAlgHom (a := taylorVia ιₚ C.translatedWpDeriv) (by simp)).1.comp (@seriesToCp p ..)).range
omit h
omit [PrimeSevenModEight d] in
lemma CMLattice.isSeriesGenerator_translatedWpDeriv : IsSeriesGenerator C.phiSeriesRing
  (taylorVia ιₚ C.translatedWpDeriv) := by simp [phiSeriesRing, eq_comm]
lemma CMLattice.taylorVia_translatedWp_mem_phiSeriesRing : taylorVia ιₚ C.translatedWp ∈
  C.phiSeriesRing := by apply (HenselianRing.is_henselian (I := .span {X}) _
  (@Cubic.monic_of_a_eq_one' _ 0 (1 - .C ⟨_, C.norm_a₁_le_one⟩ * X) (-X * X) _) 0 ..).imp fun _ h ↦
  IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub h.1.map .. <;> simp_all [translatedWp,
  ← map.eq_def,
  Cubic.toPoly, Ideal.mem_span_singleton'] <;> grind [taylorVia_curve_eq, C, map_X, constantCoeff_X]
lemma CMLattice.deriv_mem_phiSeriesRing : f ∈ C.phiSeriesRing → d⁄dX f ∈ C.phiSeriesRing :=
  fun ⟨_, e⟩ ↦ by aesop (add 1% [taylorVia_translatedWp_mem_phiSeriesRing,
  C.isSeriesGenerator_translatedWpDeriv.generator_mem,
  C.isSeriesGenerator_translatedWpDeriv.smul_mem, norm_a₁_le_one, (by simp [derivative_subst,
  ← smul_eq_C_mul]), (by erw [← map_pderiv, C.isSeriesGenerator_translatedWpDeriv.2.2]; tauto)])
end
section
attribute [local simp] Asymptotics.isBigO_top sup_of_le_left sup_of_le_right RingHomCompTriple.comp_apply add_eq_zero
open CMLattice ComplexConjugate Finset IsAIC IsLocalRing MvPolynomial NormedField PeriodPair
  PowerSeries Submodule Valued.integer
variable {d d'} {C : CMLattice d} (σ : ℂ ≃+* ℂ) {C' : CMLattice d'}
noncomputable def thetaQuotient (C : CMLattice d) (σ : ℂ ≃+* ℂ) (C' : CMLattice d') :=
  taylorAtZero C'.θ * (taylorVia σ C.θ)⁻¹
lemma taylorAtZero_monomialSection (h : C'.a₁ = σ C.a₁) x : taylorAtZero (C'.monomialSection x) =
  thetaQuotient C σ C' ^ monomialDeg x * taylorVia σ (C.monomialSection x) := by
  have A i a : a * taylorVia σ (cond i translatedWp translatedWpDeriv C) = a * taylorVia (.id _)
    (cond i translatedWp translatedWpDeriv C') := by ext n; revert i a; induction n <;> simp_all
    [translatedWp, sq, mul_add, mul_sub, mul_comm (taylorVia _ _),
    ← mul_assoc, mul_right_comm, ← div_eq_of_eq_mul (mod_cast _) (@coeff_derivative ℂ ..)]
  simp (disch := fun_prop) [taylorVia, taylorAtZero_congr _ (monomialSection_eq _ _), by simpa using
    (A · 1)]
  simp [thetaQuotient, ← mul_assoc, ← mul_pow, mul_assoc (taylorAtZero _)]
lemma exists_conjugate_section (h : C'.a₁ = σ C.a₁) z : ∃ y, ∃ μ ≠ 0, (C'.θ z = 0 → y = C.t) ∧ ∀ {m
  f}, f ∈ C.sections m → ∃ g ∈ C'.sections m, taylorAtZero g = thetaQuotient C σ C' ^ m * taylorVia
  σ f ∧ g z = μ ^ m * σ (f y) := by refine Exists₂.imp (fun y μ ↦
  .imp_right (.imp_right fun (_ : (C'.θ z, C'.σ z ^ 2, C'.phiThetaCube z) = (μ * σ (C.θ y),
  μ ^ 2 * σ (C.σ y ^ 2), μ ^ 3 * σ (C.phiThetaCube y))) m f k ↦ @And.right (Differentiable ℂ f) _
  (closure_induction ⟨?_, 0, ?_⟩ (fun _ _ _ _ ⟨_, _, p@⟨_, _⟩, _⟩ ⟨_, _, q@⟨_, _⟩, _⟩ ↦
  ⟨?_, _, add_mem p q, ?_⟩) (fun | c, _, ⟨x, k, rfl⟩ => k.2 ▸ ⟨?_, _, smul_mem _ (σ c)
  (monomialSection_mem ..), ?_, by simp_all [monomialSection, ← k.2]; ring⟩)
  (C.sections_le_span_monomialSection _ k)))) (if k : z + C'.t ∈ C'.Λ then ⟨C.t, C'.phiThetaCube z /
  σ (C.phiThetaCube C.t) / (C'.σ z / σ (C.σ C.t)) ^ 2, by grind [two_t_mem, phiThetaCube_sq_add,
  t_notMem, (sub_mem k).mt, congr(σ $(C.phiThetaCube_sq_add C.t)), θ_eq_zero_iff, sigma_eq_zero_iff,
  map_ne_zero]⟩ else (C.exists_weierstrassP_eq_of_cubic (σ.symm (C'.translatedWp z) + ℘[C.1] C.t)
  (σ.symm (℘'[C'.1] (z + C'.t))) (by grind [CMLattice, g₂_eq, g₃_eq, by
  simpa [translatedWpDeriv, h, map_ofNat] using congr(σ.symm $(C'.weierstrass_equation k))])).elim
  fun w _ ↦ ⟨w - C.t, C'.θ z / σ (C.θ _), by simp_all [phiThetaCube_spec, translatedWpDeriv,
  translatedWp, field, map_ofNat]⟩) <;> simp (disch := fun_prop) [↓zero_mem, Pi.zero_def,
  Pi.add_def, Pi.smul_def, taylorVia, taylorAtZero_monomialSection σ h] <;> grind
variable [PrimeSevenModEight d] (C :
  CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p] [Fact d'.Prime]
section
attribute [local simp] Algebra.smul_def Polynomial.aeval_eq_sum_range Polynomial.hom_eval₂ map_ofNat
lemma exists_val_coeff_le_val_eval {K σ n} [Field K] [IsAlgClosed K] (v : Valuation K NNReal) (f :
  Fin n → _) : ∃ y : σ → v.valuationSubring, ∀ i m, v ((f i).coeff m) ≤ v
  (eval (algebraMap .. ∘ y) (f i)) := by
  choose c g hg h using (f · |> fun f ↦ show ∃ c g,
    MvPolynomial.map (residue v.valuationSubring) g ≠ 0 ∧ f = c • g.map (algebraMap ..) by
    choose! k w _ using Set.exists_upper_bound_image f.support
      (v.valuationSubring.valuation ∘ f.coeff) (by simp)
    use f.coeff k, MvPolynomial.monomial k 1 + ∑ n ∈ f.support \ {k}, MvPolynomial.monomial n (w n)
    simp_all [coeff_sum, MvPolynomial.ext_iff]; use ⟨k, by simp⟩, by grind)
  have := ((of_isIntegrallyClosedIn K).of_surjective
    (@residue_surjective v.valuationSubring _ _)).isAlgClosed
  peel residue_surjective.comp_left.exists.1 (not_forall.1 (finprod_ne_zero hg ∘ funext))
  intros; simp_all [← eval₂_comp, prod_eq_zero_iff, finprod_eq_prod_of_fintype]
  gcongr; use (Valuation.integer.integers _).le_of_dvd (this _).dvd
lemma CMLattice.exists_eq_theta_pow_mul_of_norm_le {f m} (hf : f ∈ C.sections m) (hi :
  ∀ z, ‖ιₚ (f z)‖ ≤ C.naiveHeight z ^ m) : ∃ u ∈ C.phiSeriesRing, taylorVia ιₚ f =
  taylorVia ιₚ C.θ ^ m * u ∧ (f.Even → ∃ P : Polynomial ℂ, (∀ i, ‖ιₚ (P.coeff i)‖ ≤ 1) ∧ u = (P.map
  ιₚ).aeval (taylorVia ιₚ C.translatedWp) ∧ (Even m → f C.t = P.coeff (m / 2) * C.σ C.t ^ m)) := by
  have ⟨R, h, j⟩ : ∃ R : ℕ → Polynomial ℂ, (∀ z, C.θ z ≠ 0 → f z =
    C.θ z ^ m * (R 0 + C.translatedWpDeriv z • R 1).eval (C.translatedWp z)) ∧ (Even m → f C.t =
    (R 0).coeff (m / 2) * C.σ C.t ^ m) := C.sections_le_span_monomialSection m hf |>
    closure_induction ⟨0, by simp⟩ (fun _ _ _ _ ⟨R, _⟩ ↦ .imp' (R + ·) (by simp_all; grind)) (by
    rintro c _ ⟨⟨j, k, e⟩, _, ⟨⟩⟩; use Pi.single e (c • .X ^ k); cases e <;> simp_all
    [monomialSection_eq] <;> simp [monomialSection, C.θ_eq_zero_iff.2, two_t_mem,
      zero_pow_eq] <;> grind [pow_mul])
  let F := ![R 0, R 1, Cubic.toPoly ⟨4, C.a₁ ^ 2, 4, 0⟩]
  obtain ⟨x, hx, H⟩ := by simpa [↓coeff_uniqueAlgEquiv_symm, eval, ← NNReal.coe_le_coe,
    Fin.exists_fin_succ_pi] using (exists_val_coeff_le_val_eval (valuation.comap ιₚ)
    ((uniqueAlgEquiv ℂ (Fin 1)).symm <| F ·)).imp fun _ ↦ (· · <| .single 0 ·)
  obtain ⟨⟨y, hy⟩, l, e⟩ := ((F 2).eval x).isSquare, Subtype.range_coe.ge C.two_t_mem
  obtain ⟨z⟩ : ∃ z, z + C.t ∉ C.Λ ∧ x = C.translatedWp z ∧ C.translatedWp (-z) = x ∧
    C.translatedWpDeriv (-z) = C.translatedWpDeriv z + -y := (C.exists_weierstrassP_eq_of_cubic
    (x + C.weierstrassP C.t) y (by simp_all [F, Cubic.toPoly]; grind [g₃_eq,
    CMLattice])).imp' (-C.t + ·) (by simp [translatedWpDeriv, translatedWp, add_assoc, ← e]; grind)
  have hd h := have k := (H 2 · |>.trans_lt h)
    (norm_lt_one_of_eq_mul_add_mul (k 2).le (intCast_mem (valRingCp p) (-16)) (by simp [F]; ring)
      (k 2) (k 1)).ne (norm_disc_eq_one ..)
  simp [↓hy, eq_div_of_mul_eq _ (phiThetaCube_spec ..).1.symm, field, sq_le_sq, *] at hx hd
  obtain ⟨k, k', l⟩ := hi z, hi (-z), C.naiveHeight_spec z, one_pos.trans_le hd, h (-z), H 1
  simp [phiThetaCube_spec, add_mul, ← mem_iff, *] at k k' l H h
  obtain ⟨q, A⟩ := by simpa [mem_iff] using sub_mem k k', fun i h ↦ sum_mem (t :=
    range (F i).natDegree.succ) fun n _ ↦ C.isSeriesGenerator_translatedWpDeriv.smul_mem
    ((H i n).trans h) (pow_mem C.taylorVia_translatedWp_mem_phiSeriesRing n)
  grw [← hd, one_mul] at q; rw [add_mem_cancel_right (by bound)] at k
  exact ⟨_, add_mem (A 0 k) (mul_mem C.isSeriesGenerator_translatedWpDeriv.generator_mem
    (A 1 q)), by simp (disch := fun_prop) [C.taylorAtZero_congr
    h, F, taylorVia], fun e ↦ ⟨_, (H 0 · |>.trans k), by simp_all [e.eq, F], j⟩⟩
end
noncomputable def congruencePart m r (f : ℂ_[p]⟦X⟧) := PowerSeries.mk fun n ↦ ite (n ≡ r [MOD m])
    (f.coeff n) 0
lemma congruencePart_eq_sum {m} [M : NeZero m] {ζ : ℂ_[d']} (hζ : IsPrimitiveRoot ζ m) r f :
    congruencePart m r f = (m : ℂ_[d'])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • rescale (ζ ^ i) f := by
  ext; simp [congruencePart, ← mul_assoc, ← sum_mul, ← inv_pow, pow_right_comm, ← mul_pow,
    ← hζ.eq_orderOf ▸ (hζ.isOfFinOrder M.1).pow_eq_pow_iff_modEq]
  split <;> simp [*, ↓geom_sum_eq, hζ.1, mul_pow, pow_right_comm, field, hζ.ne_zero M.1]
lemma eq_sum_pow_of_sub_pow_eq {R} [CommRing R] [CharP R d'] {x s : R} {e} (h : s - s ^ d' ^ e =
  x) B : s = ∑ l ∈ range B, x ^ d' ^ (e * l) + s ^ d' ^ (e * B) := by simp [← h, sub_pow_char_pow,
  ← pow_mul', ← pow_add, ← mul_add_one, sum_range_sub', -sum_sub_distrib]
lemma CMLattice.rescale_translate_eq_theta_pow_mul {δ y N} (h : C.IsIsogeny C.1 (conj δ) N) (h0 :
  δ ≠ 0) (hy : δ * y ∈ C.Λ) : ∃ u ∈ C.phiSeriesRing, (taylorVia ιₚ (C.twistedTranslate 1 y
  C.θ)).rescale (ιₚ (conj δ)) = taylorVia ιₚ C.θ ^ N * u := have := by simpa [ne_of_gt] using h.2
  (C.exists_eq_theta_pow_mul_of_norm_le (C.twistedTranslate_comp_mem h h0 hy)
    (one_mul N ▸ C.norm_translate_le_naiveHeight_pow h y N (by aesop) (by grind [h.1 _ hy])
    (by simp))).imp (by simp_all [taylorVia, rescale_map])
lemma CMLattice.rescale_translatedWpDeriv_mem {C' a N} (h : C.IsIsogeny (@periodPair d C') a N) :
  (taylorVia ιₚ C'.translatedWpDeriv).rescale (ιₚ a) ∈ C.phiSeriesRing ∧
  ∃ v ∈ C.phiSeriesRing, (taylorVia ιₚ C'.θ).rescale (ιₚ a) = taylorVia ιₚ C.θ ^ N * v := by
  choose u A B _ using (C.exists_eq_theta_pow_mul_of_norm_le (C.comp_mul_mem_sections h
    (monomialSection_mem ..)) <| by simpa using
    C.norm_translate_le_naiveHeight_pow h 0 1 nofun (by simp) <| C'.norm_monomialSection_le ·)
  simp (disch := fun_prop) [C'.taylorAtZero_congr (monomialSection_eq _ _), taylorVia, pow_mul',
    ← rescale_map] at *
  obtain ⟨_, k⟩ := C.isSeriesGenerator_translatedWpDeriv.exists_mul_eq_one (A ..)
    (by simpa using congr(‖PowerSeries.constantCoeff $(B 1 0 0)‖).symm)
  grind [mul_mem (A 0 0 1) (pow_mem k.1 3), (taylorVia ιₚ C.θ ^ N).inv_mul_cancel (by simp)]
lemma CMLattice.norm_le_one_of_isogeny {C' a} (h : ∀ x ∈ C.Λ, a * x ∈ @Λ d C') : ‖ιₚ a‖ ≤ 1 := by
  simpa using (C.isSeriesGenerator_translatedWpDeriv.norm_coeff_le_one
    (C.rescale_translatedWpDeriv_mem (exists_isIsogeny_of_mul_mem_lattice h).choose_spec).1).2
end
