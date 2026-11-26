import Lib.Shimura.ComplexTheta.CanonicalMultiplier
import Lib.General.NumberTheory.QuadFieldSplitting
import Lib.CM.Sigma.SigmaFunction
section
noncomputable section
open Set Complex ComplexConjugate EisensteinSeries FractionalIdeal IsAppellHumbert QuadField
  ModularForm ModularFormClass Module NeZero NumberField PeriodPair Submodule UpperHalfPlane
  nonZeroDivisors Module.Basis
open scoped Real
variable (L) {z} (hz : z ∉ PeriodPair.lattice L) (d : ℕ)
lemma PeriodPair.exists_weierstrassP_eq_of_cubic x y : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
  ∃ z ∉ L.lattice, ℘[L] z = x ∧ ℘'[L] z =
  y := have T := thetaSpace_two_eq_span sigma_mem_thetaSpace L.σ_ne_zero sigma_apply_zero
  by_contra fun _ ↦ IsPosRiemann.nondegenerate.ne_zero (eq_exp_of_ne_zero
  (T.2.2 ▸ mem_span_pair.2 ⟨1, -x, rfl⟩) (by simp; grind [=_
    weierstrassP_neg, derivWeierstrassP_sq, neg_mem_iff, derivWeierstrassP_neg])).1
include hz
@[fun_prop] lemma analyticAt_℘ : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
@[fun_prop] lemma analyticAt_℘' : AnalyticAt ℂ ℘'[L] z := L.analyticOnNhd_derivWeierstrassP z hz
lemma sigma_two_mul : L.σ (2 * z) = -℘'[L] z * L.σ z ^ 4 := by grind [by simpa (disch := fun_prop)
  [deriv_comp_const_sub] using
  (EqOn.deriv (@sigma_add_mul_sigma_sub L z · hz) L.isClosed_lattice.1 hz)]
lemma derivWeierstrassP_eq_zero_iff : ℘'[L] z = 0 ↔ z + z ∈ L.lattice := by
  grind [sigma_eq_zero_iff, → sigma_two_mul]
lemma deriv_derivWeierstrassP : deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have ⟨o⟩ := L.isClosed_lattice
  have e := (EqOn.deriv · o) L.derivWeierstrassP_sq
  simp +contextual (disch := fun_prop) [EqOn] at e
  rcases EqOn.deriv e o hz, EqOn.deriv (@sigma_two_mul L) o hz
  simp (disch := fun_prop) [deriv_comp_mul_left] at *
  grind [thetaSpace_two_eq_span sigma_mem_thetaSpace L.σ_ne_zero sigma_apply_zero, sigma_two_mul]
def taylorAtZero (f : ℂ → ℂ) := PowerSeries.mk fun n ↦ iteratedDeriv n f 0 / n.factorial
abbrev taylorVia {K} [Semiring K] (ι : ℂ →+* K) f := (taylorAtZero f).map ι
def linearSeries {ι R} [Fintype ι] [CommSemiring R] (c : ι → R) : MvPowerSeries ι R := ∑ i,
  c i • .X i
def quadGen := (1 + Complex.I * √d) / 2
def quadInt := ((algebraMap (QuadField d) ℂ).comp (algebraMap (𝓞 (QuadField d)) _)).range
structure CMLattice (d) extends periodPair : PeriodPair where
  (t a₁) g₂_eq : periodPair.g₂ = 12 * ℘[periodPair] t ^ 2 - 4
  mul_mem_of_quadInt [NeZero d] {a} : a ∈ quadInt d → ∀ ⦃x⦄, x ∈ periodPair.lattice →
    a * x ∈ periodPair.lattice
  two_t_mem : t + t ∈ periodPair.lattice
  t_notMem : t ∉ periodPair.lattice
  quadGen_mul_t_notMem [NeZero d] :
    quadGen d * t ∉ periodPair.lattice ∧ conj (quadGen d) * t ∉ periodPair.lattice
  a₁_sq : a₁ ^ 2 = 12 * ℘[periodPair] t
variable {d : ℕ} (C : CMLattice d) (m : ℕ) (z : ℂ)
abbrev CMLattice.Λ := C.lattice
abbrev CMLattice.twistedTranslate y f := (m • C.hermitianForm).thetaShift y f
def CMLattice.multiplier l := sigmaSign C.1 l * C.hermitianForm.riemannPhase l C.t
abbrev CMLattice.sections := (m • C.hermitianForm).thetaSpace (C.multiplier ^ m)
def CMLattice.θ := C.twistedTranslate 1 C.t C.σ z / C.twistedTranslate 1 C.t C.σ 0
def CMLattice.translatedWp := ℘[C.1] (z + C.t) - ℘[C.1] C.t
def CMLattice.translatedWpDeriv := (℘'[C.1] (z + C.t) - C.a₁ * C.translatedWp z) / 2
def CMLattice.phiThetaCube := C.σ * (deriv C.σ * C.θ - C.σ * (deriv C.θ + (C.a₁ / 2) • C.θ))
omit hz
@[simp] lemma CMLattice.translatedWpDeriv_zero : C.translatedWpDeriv 0 = 0 := by grind
  [translatedWpDeriv, translatedWp, derivWeierstrassP_eq_zero_iff, CMLattice]
lemma conj_quadGen : starRingEnd ℂ (quadGen d) = 1 - quadGen d := by simp [quadGen, map_ofNat]; ring
lemma CMLattice.quadGen_mem_quadInt [PrimeSevenModEight d] : quadGen d ∈ quadInt d := ⟨c₀ d, rfl⟩
lemma conj_mem_quadInt [PrimeSevenModEight d] {x} : x ∈ quadInt d → starRingEnd ℂ x ∈ quadInt d :=
  .imp' star (by aesop)
lemma exists_lattice_eq_mul_tau : ∃ᵉ (a) (τ : ℍ) (e : ℤ × ℤ ≃ PeriodPair.lattice L),
  (∀ p, (e p).1 = a * (p.1 * τ + p.2)) ∧ a ≠ 0 ∧ area L = ‖a‖ ^ 2 * τ.im := have := ↑(L.3.ne_zero 1)
  have ⟨k, _, e⟩ : ∃ k ∈ [1, -1], L.area = _ * ((k : ℤˣ) * L.1 * L.2⁻¹).im := by
    simp [← Complex.sq_norm, field, area]
    grind
  ⟨L.2, ⟨_, by nlinarith [area_pos L]⟩, (k.mulLeft.prodCongr 1).trans
    L.latticeEquivProd.symm.toEquiv, by simp [latticeEquiv_symm_apply, field], this, e⟩
lemma g₂_g₃_eq_eisenstein {L a} {τ : ℍ} {e : ℤ × ℤ ≃ PeriodPair.lattice L} (h : ∀ p, (e p).1 = a *
    (p.1 * τ + p.2)) : L.g₂ = (2 * π / a) ^ 4 * E₄ τ / 12 ∧ L.g₃ = (2 * π / a) ^ 6 * E₆ τ / 216 ∧
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π / a) ^ 12 * discriminant τ := by
  rcases @tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow, @riemannZeta_two_mul_nat 3, riemannZeta_four
  simp_all! +decide [(by cbv : bernoulli 6 = 42⁻¹), eisSummand, g₂, g₃, G, mul_pow, tsum_mul_right,
    ← ((finTwoArrowEquiv _).trans e).tsum_eq, (q_expansion_riemannZeta),
    discriminant_eq_E₄_cube_sub_E₆_sq]
  grind
lemma weierstrass_disc_ne_zero :
  g₂ L ^ 3 - 27 * g₃ L ^ 2 ≠ 0 := have ⟨_, _, _, h⟩ := exists_lattice_eq_mul_tau L
  by simp_all [↓g₂_g₃_eq_eisenstein h.1, discriminant_ne_zero]
lemma exists_lattice_of_g₂_g₃ {a b} (h : a ^ 3 - 27 * b ^ 2 ≠ 0) : ∃ L, g₂ L = a ∧ g₃ L = b := by
  let g := ↑(E₄.pow 3) - ((12 * a) ^ 3 /ₚ .mk0 _ h) • modularForm CuspForm.discriminant
  by_contra!
  refine inv_ne_zero (?n I) (congrFun (levelOne_neg_weight_eq_zero ⟨_⟩ (@ModularForm.mk _ (-12) ⟨_,
    forall_mem_range.2 ?f⟩ (g.2.inv ?n) (OnePoint.isBoundedAt_iff_forall_SL2Z · |>.2 fun γ _ ↦
    ?f γ ▸ ((((tendsto_sub_nhds_zero_iff.1 (IsZeroAtImInfty.of_exp_decay (exp_decay_sub_atImInfty'
    E₄))).pow 3).sub (discriminant_isZeroAtImInfty.const_mul _)).inv₀
    (by norm_num [ModularFormClass.analyticAt_cuspFunction_zero, ← @qExpansion_coeff_zero 1,
    (E_qExpansion_coeff), ↓SlashInvariantFormClass.periodic_comp_ofComplex])).isBigO_one _))) I)
  simp [slash_def, UpperHalfPlane.σ, SlashInvariantForm.slash_action_eqn'' g]
  intro τ
  obtain ⟨⟨c, _⟩, t⟩ := IsSepClosed.exists_pow_nat_eq (12 * a / E₄ τ) 4,
    ((fun w ↦ (this ⟨τ * w, w, ·⟩)) <| 2 * π / ·)
  simp [field, imp_iff_not_or, g, (ModularForm.coe_pow), linearIndependent_fin2,
    latticeEquiv_symm_apply, fun L ↦ @g₂_g₃_eq_eisenstein L L.2 τ L.latticeEquivProd.symm] at *
  grind (ringSteps := 999999) [t (c * .I), I_sq, ne_ofReal, cpow_ofNat_inv_pow (216 * b / E₆ τ) 6,
    discriminant_ne_zero, discriminant_eq_E₄_cube_sub_E₆_sq]
def CMLattice.latticeModule [PrimeSevenModEight d] (C : CMLattice d) :
  Submodule (𝓞 (QuadField d)) ℂ := ⟨C.Λ.1, (@C.5 _ _ ⟨·, rfl⟩)⟩
def QuadField.scaledIdeal : ℂˣ × (FractionalIdeal (𝓞 (QuadField m))⁰ (QuadField m))ˣ →* Submodule
  (𝓞 (QuadField m)) ℂ := .coprod (.comp (Submodule.spanSingleton _).toMonoidHom (Units.coeHom _))
  (.comp ((mapHom (IsScalarTower.toAlgHom ..)).comp (coeSubmoduleHom ..)).1 (Units.coeHom _))
variable [PrimeSevenModEight d] {C : CMLattice d} {x} (h : CMLattice.latticeModule C =
  scaledIdeal d x) {d'} (C' : CMLattice d') {z : ℂ}
omit [PrimeSevenModEight d] in
lemma QuadField.mem_scaledIdeal {z} : z ∈ scaledIdeal d x ↔ ∃ y ∈ x.2.1, ↑x.1 * y =
  z := by simp [scaledIdeal, mem_span_singleton_mul]
attribute [-simp] map_zero
lemma QuadField.exists_latticeModule_eq_scaledIdeal 𝔠 : ∃ C u, CMLattice.latticeModule C =
  scaledIdeal d (u, 𝔠) := by
  have b := finBasisOfFinrankEq ℤ 𝔠 (by rw [fractionalIdeal_rank, RingOfIntegers.rank, finrank_K])
  let L (c : ℂˣ) := PeriodPair.mk (c * b 0) (c * b 1) (by
    simp [linearIndependent_fin2, b.ne_zero, field]; intro a h
    simpa [← h, add_div, quadGen, ← mul_div, b.ne_zero, ne, -sum_repr] using
      (congr(Complex.im ($(b.sum_repr (c₀ d • b 1)) / b 1)) : _ = (quadGen _ * _ / _).im).symm)
  have m c z : z ∈ (L c).lattice ↔ z ∈ scaledIdeal d (c, 𝔠) := by
    erw [mem_scaledIdeal, ← bex_def, Subtype.exists', (reindex_equiv b.equivFun.symm).2.1]
    simp [mem_lattice, field, Fin.exists_fin_succ_pi]
  obtain ⟨k, l, h⟩ := fun c a x ↦ (m c _).2 ∘ smul_mem _ a ∘ (m c x).1, by
    have key {a} (e : a.re = (quadGen d).re) : ¬_ ≤ comap (.mulLeft ℤ (a / 2)) (L 1).lattice :=
      fun h ↦ not_and.1 (by simp +contextual [mul_conj, e, quadGen, normSq_add,
      -map_add, ne_of_gt, field]; exact mod_cast by omega) (exists_isIsogeny_of_mul_mem_lattice h)
      (exists_isIsogeny_of_mul_mem_lattice fun _ x ↦ (add_one_mul ..).substr (add_mem (h x) x))
    simpa [not_subset, mul_comm_div] using
      mt AddSubgroupClass.subset_union.1 (·.rec (key rfl) (key (conj_re _)))
  obtain ⟨_, ⟨c⟩⟩ := mt (k 1 (c₀ d) _) h.2.1,
    IsSepClosed.exists_pow_nat_eq (3 * ℘[L 1] (l / 2) ^ 2 - (L 1).g₂ / 4) 4
  lift c to ℂˣ using .mk0 _ (by grind [weierstrass_disc_ne_zero, derivWeierstrassP_eq_zero_iff,
    → derivWeierstrassP_sq])
  refine ⟨⟨L c, c * (l / 2), _, ?_, (·.choose_spec ▸ k c _), ?_, ?_, ?_, cpow_ofNat_inv_pow ..⟩, _,
    Submodule.ext (m c)⟩ <;> simp [↓m, mem_scaledIdeal, weierstrassP, g₂, L, G,
    latticeEquiv_symm_apply, ← (latticeEquivProd _).symm.tsum_eq, ← mul_add,
    mul_left_comm _ c.1, ← mul_sub, mul_pow, ← sub_mul, tsum_mul_right] at * <;> grind [c.ne_zero]
omit [PrimeSevenModEight d] in
lemma QuadField.exists_eq_scaledIdeal_mul_of_mk_eq_one {𝔠} (h : ClassGroup.mk _ 𝔠 = 1) N : ∃ u, N =
  scaledIdeal d (u, 𝔠) * N := by
  obtain ⟨γ, g⟩ := by simpa using congr(ClassGroup.equiv (QuadField d) $h)
  use γ⁻¹.map (QuadField d).val, by simp [scaledIdeal, ← g, map_span, span_mul_span, ← one_eq_span]
lemma CMLattice.exists_latticeModule_eq_scaledIdeal C : ∃ x, latticeModule C = scaledIdeal d x :=
  have ⟨m, n, h⟩ := mem_lattice.1 (C.5 quadGen_mem_quadInt C.ω₂_mem_lattice)
  ⟨(.mk0 _ (C.indep.ne_zero 0), .mk0 (spanFinset _ {1, ↑m / (⟨quadGen _, (c₀ d).1.2⟩ - ↑n)} id) (by
  simp)), by erw [← C.latticeModule.span_eq, span_span_of_tower]; simp [scaledIdeal, map_span,
    span_mul_span, image_pair]; grind [show quadGen d ≠ n by simp [quadGen, Complex.ext_iff, ne]]⟩
lemma CMLattice.exists_latticeModule_eq_scaledIdeal_mul 𝔠 C : ∃ D u, latticeModule D = scaledIdeal d
  (u, 𝔠) * latticeModule C := have ⟨(v, 𝔞), e⟩ := C.exists_latticeModule_eq_scaledIdeal
  (QuadField.exists_latticeModule_eq_scaledIdeal (𝔠 * 𝔞)).imp fun _ ↦
    .imp' (· / v) (by simp [e, ← map_mul])
def QuadField.latticeEquiv : x.2 ≃+ C.Λ :=
  .ofBijective (AddHom.mk (⟨_, id <| h.ge <| mem_scaledIdeal.2 ⟨_, ·.2, rfl⟩⟩)
  (by aesop)) ⟨by aesop_cat, (by simpa [mem_scaledIdeal, Subtype.ext_iff] using h.le ·.2)⟩
lemma QuadField.area_eq_of_eq_scaledIdeal (h : C.latticeModule = scaledIdeal d x) :
  C.area = ‖x.1.1‖ ^ 2 * absNorm x.2.1 * √d / 2 := by
  obtain ⟨⟨_, _, B⟩, rfl, ⟨⟩⟩ : ∃ P : PowerBasis .., P.1 = c₀ d ∧ P.2 = 2 := ⟨.ofAdjoinEqTop'
    (.of_finite ..) (different_eq_span_and_adjoin_c₀ d).2, by simp [← PowerBasis.finrank,
    RingOfIntegers.rank, finrank_K]⟩
  let f := (latticeEquiv h).symm; rw [area, ← latticeBasis_zero, ← abs_det_basis_change B _ (.map
    C.latticeBasis f.toIntLinearEquiv), ← latticeBasis_one, ← sq_eq_sq₀] <;> try bound
  simp [fun z ↦ (B.localizationLocalization ℚ ℤ⁰ (QuadField d)).sum_repr (f z) ▸ (congr($(f.left_inv
    z)) : _ * _ = z.1).symm, det, det_succ_row_zero', toMatrix, div_eq_mul_inv, field, *,
    normSq, ← one_add_one_eq_two, Rat.smul_def, Complex.sq_norm, -Real.sq_sqrt]; ring
namespace CMLattice
instance isAppellHumbert_multiplier : IsAppellHumbert C'.hermitianForm C'.multiplier := .shift _
lemma θ_mem : C'.θ ∈ C'.sections 1 := ⟨by fun_prop [θ], by
  simp_all [θ, twistedTranslate, (thetaShift_mem sigma_mem_thetaSpace _).2, multiplier, field]⟩
@[fun_prop] lemma differentiable_θ : Differentiable ℂ C'.θ := C'.θ_mem.1
attribute [local simp] thetaShift_apply CMLattice.t_notMem CMLattice.two_t_mem CMLattice.θ exp_add
  exp_neg exp_sub canonicalMultiplier deriv_comp_add_const fieldEq riemannForm_def sigmaSign
@[simp] lemma θ_zero : C'.θ 0 = 1 := by simp
@[simp] lemma θ_eq_zero_iff : C'.θ z = 0 ↔ z + C'.t ∈ C'.Λ := by simp
variable {d : ℕ} (C : CMLattice d) {z : ℂ} (z' : ℂ)
lemma multiplier_eq_neg_sigmaSign : z ∈ C.Λ → C.multiplier z = -sigmaSign C.1 (C.t + C.t + z) := by
  simp_all [↓isAppellHumbert_hermitianForm.3, multiplier, -fieldEq]; grind
@[simp] lemma θ_neg : C.θ (-z') = C.θ z' := by simp [-hermitianForm_apply, ← sigma_neg,
  sub_add_add_cancel z' .. ▸ sigma_mem_thetaSpace.2 _ C.two_t_mem _, neg_add_eq_sub]
lemma θ_sq : z ∉ C.Λ → C.θ z ^ 2 = (℘[C.1] z - ℘[C.1] C.t) * C.σ z ^ 2 := by
  nth_rw 1 [sq, ← θ_neg]; simp; grind [→ sigma_add_mul_sigma_sub, CMLattice]
lemma g₃_eq : C.g₃ = 4 * ℘[C.1] C.t ^ 3 - C.g₂ * ℘[C.1] C.t := by
  grind [→ derivWeierstrassP_sq, CMLattice, derivWeierstrassP_eq_zero_iff]
attribute [local grind! .] CMLattice.a₁_sq CMLattice.g₃_eq CMLattice.quadGen_mul_t_notMem
  CMLattice.g₂_eq CMLattice.translatedWp.eq_1 ofReal_ne_zero derivWeierstrassP_sq area_pos
lemma σ_two_mul_sq : ∀ z, C.σ (2 * z) ^ 2 = (C.σ z * C.θ z) ^ 2 * (4 * (C.θ z ^ 4 + C.σ z ^ 4) +
    (C.a₁ * C.θ z * C.σ z) ^ 2) := C.eq_of_eq_off_lattice 0 (by grind [sigma_two_mul, θ_sq])
lemma disc_eq : C.g₂ ^ 3 - 27 * C.g₃ ^ 2 = C.a₁ ^ 4 - 64 := by grind
@[simp] lemma deriv_translatedWp : deriv C.translatedWp z' = 2 * C.translatedWpDeriv z' + C.a₁ *
  C.translatedWp z' := by simp [translatedWp.eq_unfold, translatedWpDeriv]
lemma deriv_translatedWpDeriv_eq (hz : z + C.t ∉ C.Λ) : deriv C.translatedWpDeriv z = 1 + 3 *
  C.translatedWp z ^ 2 - C.a₁ * C.translatedWpDeriv z := by simp (disch := fun_prop)
  [translatedWpDeriv.eq_unfold, translatedWp, deriv_derivWeierstrassP _ hz]; grind
lemma weierstrass_equation (hz : z + C.t ∉ C.Λ) :
    C.translatedWpDeriv z ^ 2 + C.a₁ * C.translatedWp z * C.translatedWpDeriv z =
  C.translatedWp z ^ 3 + C.translatedWp z := by grind [translatedWpDeriv]
lemma theta_add_mul_theta_sub (hz : z + C.t ∉ C.Λ) : ∀ w, C.θ (z + w) * C.θ (z - w) =
  C.θ z ^ 2 * (C.θ w ^ 2 - C.translatedWp z * C.σ w ^ 2) := C.eq_of_eq_off_lattice 0
  (by simp +contextual [↓θ_sq, -hermitianForm_apply]; grind [→ sigma_add_mul_sigma_sub])
@[fun_prop] lemma analyticAt_translatedWp_zero :
  AnalyticAt ℂ C.translatedWp 0 := by fun_prop (disch := simp) [translatedWp]
@[fun_prop] lemma analyticAt_translatedWpDeriv_zero :
  AnalyticAt ℂ C.translatedWpDeriv 0 := by fun_prop (disch := simp) [translatedWpDeriv]
attribute [-simp] CMLattice.θ hermitianForm_apply map_mul
@[simp] lemma deriv_translatedWpDeriv_zero :
  deriv C.translatedWpDeriv 0 = 1 := by simp [deriv_translatedWpDeriv_eq, translatedWp]
lemma phiThetaCube_spec : ∀ z, z + C.t ∉ C.Λ → C.σ z ^ 2 = C.translatedWp z * C.θ z ^ 2 ∧
  C.phiThetaCube z = C.translatedWpDeriv z * C.θ z ^ 3 := by
  have x := by simpa [θ.eq_1 _ (_ + _), add_assoc, sigma_mem_thetaSpace.2,
    C.θ_eq_zero_iff.2] using (@C.theta_add_mul_theta_sub _ · · (-C.t))
  have e := by simpa +contextual (disch := (try unfold translatedWp); fun_prop) [EqOn] using
    (EqOn.deriv · C.isClosed_lattice.1.preimage_of_continuous) x
  simp [phiThetaCube]; grind [exp_ne_zero, by
    simpa (disch := fun_prop) using
      EqOn.deriv e C.isClosed_lattice.1.preimage_of_continuous (by simp : 0 + C.t ∉ _)]
lemma phiThetaCube_sq_add : ∀ z, C.phiThetaCube z ^ 2 + C.a₁ * C.σ z ^ 2 * C.θ z * C.phiThetaCube
  z = C.σ z ^ 6 + C.σ z ^ 2 * C.θ z ^ 4 := C.eq_of_eq_off_lattice C.t
  (by grind [weierstrass_equation, phiThetaCube_spec]) (by fun_prop [phiThetaCube])
@[simp] lemma θ_two_mul : ∀ z, C.θ (2 * z) = C.θ z ^ 4 - C.σ z ^ 4 := C.eq_of_eq_off_lattice C.t (by
  grind [phiThetaCube_spec, theta_add_mul_theta_sub, θ_zero, two_mul])
lemma multiplier_quadGen_mul [PrimeSevenModEight d] {a} (h : a = quadGen d ∨ a = conj (quadGen d))
  (hl : z ∈ C.Λ) : C.multiplier (a * z) = 1 := @C.5 _ a (by grind [quadGen_mem_quadInt,
  conj_mem_quadInt]) |> fun e ↦ by grind [multiplier_eq_neg_sigmaSign, sigmaSign, conj_quadGen,
  mul_conj, → fun k ↦ sub_mem (sub_mem k (e k)) (nsmul_mem hl (d / 8).succ), show (quadGen d).normSq
  = (2 * (d / 8).succ : ℂ) by simp [quadGen, normSq]; norm_cast; grind [PrimeSevenModEight]]
lemma mul_mem_or_mul_sub_t_mem [PrimeSevenModEight d] (hc : z = quadGen d ∨
  z = conj (quadGen d)) x (hx : x + x ∈ C.Λ) : z * x ∈ C.Λ ∨ z * (x - C.t) ∈ C.Λ := by
  rcases C.multiplier_quadGen_mul hc hx, C.multiplier_quadGen_mul hc C.two_t_mem,
    C.multiplier_quadGen_mul hc (sub_mem hx C.two_t_mem)
  simp [multiplier, mul_sub] at *; grind
lemma multiplier_eq_canonicalMultiplier [PrimeSevenModEight d] (hl : z ∈ C.Λ) : C.multiplier z =
  canonicalMultiplier C.hermitianForm (conj (quadGen d) • 1) z := by
  simpa [↓multiplier_quadGen_mul, *, conj_quadGen, sub_mul, ↓riemannForm_def] using
    C.isAppellHumbert_multiplier.3 _ (C.5 quadGen_mem_quadInt hl) _
    (C.5 (conj_mem_quadInt quadGen_mem_quadInt) hl)
lemma comp_mul_mem_sections [PrimeSevenModEight d] {C' a N} (h :
  C.IsIsogeny (@CMLattice.periodPair d C') a N) {k g} : g ∈ C'.sections k → (g <| a * ·) ∈
  C.sections (k * N) := .imp (by fun_prop) (by simp_all [mul_add, multiplier_eq_canonicalMultiplier,
  mul_left_comm _ a, ← exp_nsmul, -fieldEq, show ∀ u v, C'.hermitianForm (a * u) (a * v) =
  N * C.hermitianForm u v by grind [hermitianForm_apply, IsIsogeny]]; grind)
end CMLattice
end
section
attribute [local simp] map_zero hermitianForm_apply map_mul
open Complex Nat AnalyticAt ComplexConjugate Finset Function IsAppellHumbert PowerSeries Submodule
variable {d} (C : CMLattice d) (x : ℕ × ℕ × ℕ) {f g : ℂ → ℂ} {p : ℕ} [Fact p.Prime] {σ : Type}
@[simp] abbrev CMLattice.monomialDeg := x.1 + x.2.1 * 2 + x.2.2 * 3
@[local simp] noncomputable def CMLattice.monomialSection :=
  C.θ ^ x.1 * ((C.σ ^ 2) ^ x.2.1 * C.phiThetaCube ^ x.2.2)
@[fun_prop] lemma CMLattice.differentiable_monomialSection :
  Differentiable ℂ (C.monomialSection x) := by fun_prop [monomialSection, phiThetaCube]
lemma CMLattice.monomialSection_eq z (hz : z + C.t ∉ C.Λ) :
    C.monomialSection x z = C.θ z ^ monomialDeg x *
  (C.translatedWp z ^ x.2.1 * C.translatedWpDeriv z ^ x.2.2) := by simp [phiThetaCube_spec, *]; ring
lemma CMLattice.monomialSection_mem : C.monomialSection x ∈ C.sections (monomialDeg x) :=
  ⟨by fun_prop, Subtype.forall'.2 fun l ↦
  C.eq_of_eq_off_lattice C.t (by simp_all [↓monomialSection_eq, translatedWpDeriv, translatedWp,
  add_right_comm _ l.1, C.θ_mem.2, ← exp_nsmul, add_mem_cancel_right, mul_pow]; grind)⟩
lemma CMLattice.sections_zero_le_const : C.sections 0 ≤ 1 := fun f k ↦
  ⟨_, .symm (funext (by simpa using apply_smul_of_nonpos k 1))⟩
lemma CMLattice.section_division {e} D y {m k S f g a} (s : C.sections k ≤ S) (hg :
  g ∈ C.sections m) (hf : f ∈ C.sections (m + k)) (a0 : a ≠ 0) (E : g =
  (@twistedTranslate e D 1 y D.θ <| a * ·)) (h : ∀ z, g z = 0 → f z = 0) : ∃ c ∈ S, c * g = f := by
  replace E z : g z = 0 → deriv g z ≠ 0 := E ▸ by simp (disch := fun_prop) [↓deriv_comp_mul_left, θ,
    funext (thetaShift_apply _ _ _), add_assoc, deriv_comp_add_const]; grind [thetaSpace_two_eq_span
    sigma_mem_thetaSpace D.σ_ne_zero sigma_apply_zero, CMLattice, exp_ne_zero]
  obtain ⟨⟨u⟩, ⟨v⟩⟩ := hf, hg; let T z h : ℂ → ℂ := ite (g z = 0) (dslope h z) h
  have A {z h} := ((by simp [T, apply_ite, ← differentiableOn_univ, differentiableOn_dslope] :
    Differentiable ℂ h → Differentiable ℂ (T z h)) · z)
  use fun z ↦ (T z f / T z g) z, s ⟨fun z ↦ ((A u).div (A v) ?n).congr_of_eventuallyEq
    (((A v).continuousAt.eventually_ne ?n).mono ?_), ?_⟩, funext ?_ <;> simp +contextual (disch :=
    first | fun_prop | trivial) [T, dslope, update, slope, *, ite_apply, ← deriv_comp_add_const,
    exp_add, add_div] <;> grind [C.isAppellHumbert_multiplier.ne_zero, exp_ne_zero, pow_ne_zero]
lemma CMLattice.sections_le_span_monomialSection m : C.sections m ≤ span ℂ (C.monomialSection ''
  {x | x.2.2 ≤ 1 ∧ monomialDeg x = m}) := m.twoStepInduction (C.sections_zero_le_const.trans
  (by aesop)) ((eq_span_singleton_of_mem_of_finrank_eq_one finrank_thetaSpace_nsmul C.θ_mem
  (ne_iff.2 ⟨0, by simp⟩)).trans_le (span_mono (by simp; use 1, 0; simp))) fun m _ ih f k ↦ by
  let x := (0, m / 2 + 1 - m % 2, m % 2)
  have F := sub_mem k (smul_mem _ ((f / C.monomialSection x) (-C.t))
    (by convert C.monomialSection_mem x using 2; lia))
  refine (sub_mem_iff_left _ (smul_mem _ _ (subset_span (by grind)))).1 ((map_span_le (.mulRight ..)
    ..).2 ?_ (C.section_division C 0 ih C.θ_mem (add_comm 1 _ ▸ F) one_ne_zero (by simp) ?_))
  use fun _ ⟨x, _⟩ ↦ subset_span ⟨x + (1, 0), by simp_all; grind⟩
  simpa [x, t_notMem, by simpa [C.θ_eq_zero_iff.2]
    using congr(($(C.phiThetaCube_sq_add (-C.t))) = 0)] using fun z ↦ (F.2 (z + C.t) · (-C.t))
lemma CMLattice.twistedTranslate_comp_mem [PrimeSevenModEight d] {δ y N} (h : C.IsIsogeny C.1
  (conj δ) N) (h0 : δ ≠ 0) (hy : δ * y ∈ C.Λ) : (C.twistedTranslate 1 y C.θ <| conj δ * ·) ∈
  C.sections N := by convert (thetaShift_mem_of_dual (a := y / conj δ) (mem_dualLattice_nsmul.2
  (C.isAppellHumbert_multiplier.le_dualLattice (Eq.subst ?_ hy))) (C.comp_mul_mem_sections h
  C.θ_mem)) using 2 <;> simp [thetaShift_apply, ← by simpa [ne_of_gt] using h.2] <;> field [h0]
attribute [fun_prop] Differentiable.analyticAt
@[simp] lemma coeff_taylorAtZero n : coeff n (taylorAtZero f) = iteratedDeriv n f 0 / n ! :=
  coeff_mk ..
@[simp] lemma constantCoeff_taylorAtZero : constantCoeff (taylorAtZero f) =
  f 0 := by simp [taylorAtZero]
@[simp] lemma taylorAtZero_const c :
    (taylorAtZero fun _ ↦ c) = PowerSeries.C c := by ext ⟨⟩ <;> simp [iteratedDeriv_const]
@[simp] lemma taylorAtZero_comp_mul a f : taylorAtZero (f <| a * ·) = rescale a (taylorAtZero f) :=
  PowerSeries.ext fun n ↦ by induction n generalizing f <;> simp_all [iteratedDeriv_succ',
  funext (deriv_comp_mul_left _ f), field, pow_add]
lemma eq_of_taylorAtZero_eq : Differentiable ℂ f → Differentiable ℂ g → taylorAtZero f =
  taylorAtZero g → f = g := by
  simp_all [funext_iff, ← taylorSeries_eq_of_entire' 0, inv_mul_eq_div, ← coeff_taylorAtZero]
@[simp] lemma taylorAtZero_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
  taylorAtZero (fun z ↦ f z + g z) = taylorAtZero f + taylorAtZero g :=
  PowerSeries.ext (by simp [*, field, iteratedDeriv_fun_add, contDiffAt])
@[simp] lemma taylorAtZero_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorAtZero (fun z ↦ f z * g z) = taylorAtZero f * taylorAtZero g := PowerSeries.ext (by
  simp [*, coeff_mul, iteratedDeriv_fun_mul, contDiffAt, sum_div, Nat.antidiagonal_eq_image]
  grind [sum_congr, cast_choose, cast_ne_zero])
@[simp] lemma taylorAtZero_eval (hf : AnalyticAt ℂ f 0) P : taylorAtZero (P.eval <| f ·) =
  Polynomial.aeval (taylorAtZero f)
  P := by apply @P.recOnHorner <;> simp +contextual (disch := fun_prop)
@[simp] lemma taylorAtZero_pow (hf : AnalyticAt ℂ f 0) n :
    taylorAtZero (f · ^ n) = taylorAtZero f ^ n := by simpa using taylorAtZero_eval hf (.X ^ n)
noncomputable abbrev valRingCp (p : ℕ) [Fact p.Prime] := NormedField.valuation (K := ℂ_[p]).integer
noncomputable abbrev seriesToCp := MvPowerSeries.map (σ := σ) (valRingCp p).subtype
@[simp] lemma seriesToCp_smul (k : valRingCp p) f : @seriesToCp p _ σ (k • f) =
  k.1 • seriesToCp f := rfl
end
