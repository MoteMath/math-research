import Lib.Analytic.Landau.PolarLandau
import Lib.ClassField.Places.CyclotomicCharacter
import Lib.ClassField.HeckeCharacter.SplittingCharExists
import Lib.ClassField.HeckeL.AutCharLFunction
import Lib.CM.FormalGroup.FormalHeight
import Lib.Weil.Construction.FockThetaFunctions
import New.Curve.KatzDivisibility
section
noncomputable section
open ArithmeticFunction DirichletCharacter Complex Finset Filter MeasureTheory Nat Real vonMangoldt
variable (d : ℕ) [Fact d.Prime] (M : ℕ)
def lambdaClass ν := @residueClass M 1 ν * (1 - chiK d ν)
def lambdaSum r y := (∑ k ∈ Icc 1 ⌊y⌋₊, lambdaClass d M k / k * k ^ r) / y ^ r
def logDerivMean [NeZero M] s :=
  (∑ ξ, (logDeriv (entireL (quadTwist ξ d)) s - logDeriv (@entireL M _ ξ) s) - 1) / φ M
def primeError [NeZero M]
    x := lambdaSum d M 0 x - lambdaSum d M 1 x - x.log / φ M - (logDerivMean d M 1).re
lemma lambdaClass_nonneg_and_abs_le ν : 0 ≤ lambdaClass d M ν ∧ |lambdaClass d M ν| ≤ 2 * ν := by
  simp [lambdaClass, chiK, Set.indicator, quadraticCharFun, sub_ite]
  grind [vonMangoldt_nonneg, vonMangoldt_le_log, Real.log_le_self]
lemma abs_lambdaSum_exp_le r v : |lambdaSum d M r (rexp v)| ≤ 2 * rexp v := by
  grw [lambdaSum, abs_div, abs_sum_le_sum_abs, sum_le_card_nsmul _ _ (2 * v.exp ^ r)] <;> simp
    +contextual [abs_div, le_floor_iff, exp_nonneg, mul_le_mul, div_le_of_le_mul₀, field,
    lambdaClass_nonneg_and_abs_le, pow_le_pow_left₀, floor_le]
lemma re_logDerivMean_one : (logDerivMean d 1 1).re = -1 - chowlaSelbergConst d := by
  simp [logDerivMean, chowlaSelbergConst, logDeriv, level_one, show @entireL 1 _ 1 = riemannZeta₁ by
    simp_all [entireL, Function.update_eq_iff, riemannZeta_eq_inv_sub_mul]]; ring
variable [NeZero M] {d M}
lemma primeError_eq_sum (A : ℕ) {z : ℝ} (u : 0 < z) (h : z ≤ A) : primeError d M z = ∑ ν ∈ Icc 1 A,
  lambdaClass d M ν * (A / ν - A / z)⁺ / A - z.log / φ M - re (logDerivMean d M 1) := by
  have := u.trans_le h
  simp [primeError, lambdaSum, sum_div, ← sum_sub_distrib]; apply sum_congr_of_eq_on_inter <;>
    simp +contextual [le_floor_iff u.le, field] <;> rify <;> grind
lemma isPolar_primeError (hd : d % 8 = 7) (h : M.Coprime d) : IsPolar (primeError d M ·.exp) fun s ↦
    (∑ ξ, (analyticOrderNatAt (@entireL M _ ξ) s - analyticOrderNatAt (entireL (quadTwist ξ d))
  s : ℂ)) / φ M / (s * (1 - s)) := by
  let κ := (logDerivMean d M 1).re
  have A : AnalyticOnNhd ℂ (fun s ↦ logDerivMean d M s / s - κ) {s | 1 ≤ s.re} := fun _ _ ↦ by
    fun_prop (disch := grind [entireL_ne_zero, zero_re]) [logDerivMean, logDeriv]
  refine ⟨by fun_prop [primeError, lambdaSum], |κ| + 5, fun s ↦ (logDerivMean d M s / s - κ) /
    (s - 1), fun _ ↦ by fun_prop [logDerivMean], fun v a ↦ (abs_sub ..).trans ?_, ?q,
  have := @ext _ 0 (by simp [κ]) ((A.mono (by aesop)
    ).im_ofReal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ici (by simp) (.mono
    (lt_mem_nhds (lt_add_one _)) fun x u ↦ congr(im $((div_eq_iff (by aesop)).1 (?q x u))).trans
    (by norm_cast)) (le_refl (1 : ℝ)))
  ⟨?B, fun ρ _ ↦ have I := (@continuousWithinAt_id _ _ {ρ}ᶜ ρ).sub_const
    if e : 1 = ρ then e ▸ .trans_eq (tendsto_inf_left (?B 1 (by simp)).continuousAt) (by simp) else
    by convert ((((((tendsto_finsetSum ⊤ fun ξ _ ↦ (tendsto_sub_mul_logDeriv_entireL (@quadTwist M ξ
      d _)).2.sub (tendsto_sub_mul_logDeriv_entireL ξ).2).sub (I ρ)).div_const (φ M)).div
      (I 0) ?_).sub ((I ρ).mul_const ↑κ)).div
      (I 1) ?_) using 2 <;> simp [logDerivMean, ← mul_sum] <;> grind [zero_re]⟩⟩
  grw [abs_sub, v.log_exp, ← @NeZero.one_le (φ _), add_mul,
    ← le_mul_of_one_le_right] <;> grind [add_one_le_exp, abs_lambdaSum_exp_le]
  intro s u
  have L := @laplace_pow (s - 1) (by simp [u.trans'])
  have e r : (s + r - 1) * ∫ v in _, lambdaSum d M r (rexp v) * (v - s * v).exp = _ := .trans (by
    congr 1; convert integral_comp_exp_Ioi _ 0 <;> simp [lambdaSum, field, cpow_add, cpow_neg,
      le_of_lt,
    Complex.exp_sub, cpow_def _ s, Complex.log_exp, mul_comm s, pi_pos]) ((@LSeries_eq_mul_integral'
    _ (1 + r) (by bound) _ (by simp; bound) (.of_bound 2 (.mono (Ioi_mem_atTop 0) fun n _ ↦ by
    simpa [lambdaSum, *, div_le_iff₀, abs_div, rpow_add, field, lambdaClass_nonneg_and_abs_le,
      Real.exp_log, abs_of_nonneg] using abs_lambdaSum_exp_le d M r (.log n)))).symm.trans
    (((LSeriesHasSum.sum (S := ⊤) fun ξ _ ↦ (@LSeriesHasSum_mul_vonMangoldt M ξ _ s (by bound)).sub
    (LSeriesHasSum_mul_vonMangoldt (quadTwist ξ d) (by bound))).div_const (φ M)).congr_fun
    fun n ↦ by by_cases n = 0 <;> simp [*, cpow_sub, field, cpow_add, lambdaClass,
    chiK_eq_legendreSym, residueClass_apply, mod_cast (quadTwist_apply · d n), ← sum_mul]).tsum_eq)
  obtain := L 0, L 1, Integrable.of_integral_ne_zero ((L 0).trans_ne (by aesop)),
    Integrable.of_integral_ne_zero ((L 1).trans_ne (by aesop)),
    fun r ↦ integrableOn_laplace_of_abs_le
    (by fun_prop [lambdaSum]) (fun v _ ↦ abs_lambdaSum_exp_le d M r _) u
  simp [primeError, κ, IntegrableOn, sub_mul, div_eq_inv_mul, logDerivMean, mul_assoc,
    quadTwist_ne_one _ d (by lia) h] at *
  simp (disch := fun_prop) [integral_sub, *]
  linear_combination (norm := field (disch := grind [zero_re, one_re])) e 1 / s - e 0 / (s - 1)
  grind [ofReal_one]
end
end
section
noncomputable section
section
open NumberField Polynomial IsCyclotomicExtension jacobiSym InfinitePlace IsAlgClosed cyclotomic
  NeZero IsMulCommutative
@[local grind] structure Parameters where
  (N₀ d : ℕ)
  dvd_N₀ : 18480 ∣ N₀
  d_prime : d.Prime
  d_congr : N₀ ∣ 2 * (d + 1) ∧ ¬N₀ ∣ d + 1
namespace Parameters
variable (P : Parameters) (s) {p : ℕ}
instance : NeZero P.N₀ := ⟨by grind [zero_dvd_iff]⟩
@[local grind! .] instance instHeegD : PrimeSevenModEight P.d :=
  @.mk _ ⟨P.4⟩ (by grind [→ dvd_trans])
def _root_.towerDeg := 3 ^ (.log 3 s + 5) * 2 ^ s deriving NeZero
abbrev N₁ := P.N₀ * towerDeg s
lemma dvd_norm_c₀ {s} (hp : p.Prime) (h : p ∣ P.N₁ s) : p ∣ (P.d + 1) / 4 := (hp.dvd_or_dvd
  (m := 2 ^ 3) (.trans (by grind [hp.dvd_mul, hp.dvd_of_dvd_pow, dvd_trans, towerDeg]) (P.5.1.trans
  ⟨1, by grind [PrimeSevenModEight]⟩))).elim (by grind [hp.dvd_of_dvd_pow ·, dvd_trans,
  PrimeSevenModEight]) id
lemma lt_d : 64 < P.d := by grind [→ dvd_trans]
lemma chiK_eq_one_of_dvd {s} (hp : p.Prime) (h : p ∣ P.N₁ s) : chiK P.d p = 1 := by
  rw [chiK_eq_legendreSym, legendreSym.to_jacobiSym, mod_right', (Nat.mod_eq_sub_iff one_pos _).2,
    ← one_left (4 * p - 1), ← mod_left' (Int.add_emod_right 1 _)] <;>
    grind [hp.pos, Nat.mul_dvd_of_dvd_div, dvd_norm_c₀, =_ div_four_left, PrimeSevenModEight]
lemma thirteen_le_of_chiK_ne_one (hp : p.Prime) : chiK P.d p ≠ 1 → 13 ≤ p := Not.imp_symm fun _ ↦
  P.chiK_eq_one_of_dvd hp (.trans (by interval_cases p <;> trivial) (P.3.mul_right (towerDeg 0)))
abbrev K := QuadField P.d
def Mω := (P.N₀ * P.d) ^ (s + 6) deriving NeZero
lemma N₁_mul_d_dvd_M_omega {P s} : N₁ P s * P.d ∣ P.Mω s := by grw [mul_right_comm, towerDeg,
  Nat.log_le_self, Mω, s.le_add_right, ← mul_pow, (by grind : 3 * 2 ∣ P.N₀ * _), ← pow_succ']
lemma coprime_N₁_d : (P.N₁ s).Coprime P.d :=
  (P.4.coprime_iff_not_dvd.2 ((P.chiK_eq_one_of_dvd P.4).mt (by simp [chiK]))).symm
def E := CyclotomicField (P.N₁ s) P.K deriving Field, Algebra P.K, NumberField
protected abbrev Φ := InfinitePlace (P.E s)
def bigOmega := (chowlaSelbergConst P.d).exp * (2 * .pi / rootDiscr (P.E s))
instance : IsCyclotomicExtension {P.N₁ s} P.K (P.E s) := CyclotomicField.isCyclotomicExtension ..
lemma irreducible_cyclotomic : Irreducible (cyclotomic (P.N₁ s) P.K) := let M := cycloField P.d
  have hζ := zeta_spec (P.N₁ s) M (CyclotomicField (P.N₁ s) M)
  (monic ..).irreducible_of_irreducible_map
    (QuadField.nonempty_algHom_of_isPrimitiveRoot _ (zeta_spec _ ℚ M)).1 _ (by simpa using ((
    associated_of_dvd_of_natDegree_le (minpoly.dvd _ _ (aeval_zeta ..)) (monic ..).ne_zero (by
    simpa [← Module.finrank_mul_finrank ℚ M, (hζ.powerBasis _).finrank, ↓Rat.finrank P.d, pos,
    natDegree_cyclotomic] using
      totient_mul_totient_le_finrank _ _ (coprime_N₁_d ..) hζ ((zeta_spec _ ℚ M).map_of_injective
    (algebraMap ..).injective))).irreducible (minpoly.irreducible (.of_finite ..))))
def toCycloField {P s} : E P s →ₐ[ℚ] cycloField (P.N₁ s * P.d) :=
  have hζ := zeta_spec (P.N₁ s * _) ℚ (cycloField (P.N₁ s * P.d))
  let := (QuadField.nonempty_algHom_of_isPrimitiveRoot P.d (hζ.pow one_le rfl)).toAlgebra
  (SplittingField.lift _ (by simp [cyclotomic_eq_prod_X_sub_primitiveRoots (hζ.pow one_le
    (mul_comm ..))])).toRatAlgHom
instance : IsAbelianGalois ℚ (P.E s) := (isAbelianGalois {P.N₁ s * P.d} ..).of_algHom toCycloField
instance : IsAbelianGalois P.K (P.E s) := .tower_top ℚ ..
instance : IsTotallyComplex (P.E s) := isTotallyComplex_of_algebra P.K _
lemma algHom_eq_of_mk_eq {φ ψ : P.E s →ₐ[P.K] ℂ} (h : InfinitePlace.mk φ.1 = .mk ψ.1) : φ = ψ :=
  (mk_eq_iff.1 h).elim (by grind [AlgHom]) (by simpa using congr($(·).comp (algebraMap P.K _)))
instance : CommGroup (P.Φ s) := (Equiv.ofBijective (fun g : Gal(P.E s/P.K) ↦
  InfinitePlace.mk (lift.comp g.toAlgHom).1) ⟨fun _ _ h ↦ AlgEquiv.ext (lift.injective
  congr($(P.algHom_eq_of_mk_eq s h) ·)), fun _ ↦ (exists_smul_eq_of_comap_eq (w := .mk lift.1)
  (by subsingleton)).elim (⟨·⁻¹, ·⟩)⟩).symm.commGroup
def galOfPlace : P.Φ s ≃* Gal(P.E s/P.K) := Equiv.mulEquiv _
def placeMulEquiv := (P.galOfPlace s).trans (autEquivPow _ (P.irreducible_cyclotomic s))
def placeOfInt ν := if h : IsUnit (Int.cast ν) then (P.placeMulEquiv s).symm h.unit else 1
def placeClass {s m} (d : m ∣ P.N₁ s) := (ZMod.unitsMap d).comp (P.placeMulEquiv s).toMonoidHom
def ζ := zeta (P.N₁ s) P.K (P.E s)
instance : CMType (P.E s) :=
  {Φ v := (lift.comp (P.galOfPlace s v).toAlgHom).1, mk_Φ := (galOfPlace ..).left_inv}
@[simp] lemma phi_algebraMap v x : Φ v (algebraMap P.K (P.E s) x) = x := by simp [Φ]
end Parameters
open Finset Fintype IsCoprime ZMod
lemma Parameters.expand_pow_cyclotomic {p N} (h : p.Prime) (e : p ∣ N) k R [CommRing R] :
    expand R (p ^ k) (cyclotomic N R) = cyclotomic (N * p ^ k) R := by
  induction k <;> simp [*, pow_succ', expand_mul, e.mul_right]; ring
variable {P : Parameters} {s} {ν : ℤ}
lemma Parameters.expand_towerDeg_cyclotomic : expand ℂ (towerDeg s) (cyclotomic P.N₀ ℂ) =
  cyclotomic (P.N₁ s) ℂ := by erw [expand_mul, expand_pow_cyclotomic,
  expand_pow_cyclotomic] <;> norm_num <;> grind [Parameters, towerDeg]
lemma Parameters.card_infinitePlace_E s : numInfPlaces (P.E s) =
  towerDeg s * P.N₀.totient := by simp [mul_comm, card_congr (placeMulEquiv ..).1,
  ← natDegree_cyclotomic _ ℂ, ← expand_towerDeg_cyclotomic, natDegree_expand]
lemma Parameters.card_placeClass_eq d : #{v | @placeClass P s P.N₀ d v = 1} = towerDeg
  s := by simpa [card_infinitePlace_E, ne, placeClass, Subgroup.index_ker, Fintype.card_subtype,
  unitsMap_surjective, ↓MonoidHom.mem_ker] using! (P.placeClass d).ker.card_mul_index
lemma Parameters.isPrimitiveRoot_zeta : IsPrimitiveRoot (P.ζ s) (P.N₁ s) :=
  IsCyclotomicExtension.zeta_spec ..
lemma Parameters.phi_mul v v' x : Φ (v * v') x = Φ v (P.galOfPlace s v' x) := by simp [Φ]
@[simp] lemma Parameters.star_ζ : star (P.ζ s) = (P.ζ s)⁻¹ := (Φ 1).injective (by
  simp [Complex.inv_eq_conj, (isPrimitiveRoot_zeta.map_of_injective (Φ _).injective).norm'_eq_one,
    ne])
lemma Parameters.galOfPlace_zeta v : P.galOfPlace s v (P.ζ s) =
  P.ζ s ^ (P.placeClass dvd_rfl v).1.val := by simp [placeClass, placeMulEquiv, ζ]
lemma Parameters.two_pow_dvd_N₁ : 2 ^ (s + 1) ∣ P.N₁ s := by grind [Parameters, towerDeg,
  mul_dvd_mul, dvd_mul_left]
lemma Parameters.placeOfInt_pow i : P.placeOfInt s ν ^ i =
  P.placeOfInt s (ν ^ i) := by cases i <;> simp [placeOfInt, ← map_pow]; rfl
lemma Parameters.placeClass_placeOfInt (h : IsCoprime ν P.N₀) {m d} :
  (@placeClass P s m d (P.placeOfInt s ν)).1 = ν := by
  simp (disch := grind [Parameters, h.symm.of_isCoprime_of_dvd_left]) [placeClass, placeOfInt,
    unitsMap_val, towerDeg, coe_int_isUnit_iff_isCoprime, mul_left_iff, IsCoprime.pow_left, h.symm]
lemma Parameters.galOfPlace_placeOfInt_zeta (h : IsCoprime ν P.N₀) :
  P.galOfPlace s (P.placeOfInt s ν) (P.ζ s) = P.ζ s ^ ν := by simp [galOfPlace_zeta,
  placeClass_placeOfInt h, ← zpow_natCast, coe_intCast, Int.emod_def, zpow_sub₀,
  isPrimitiveRoot_zeta.ne_zero out, (isPrimitiveRoot_zeta.zpow_eq_one_iff_dvd _).2]
lemma Parameters.pow_d_ne_neg_one n : (P.d : ZMod P.N₀) ^ n ≠ -1 := by
  obtain ⟨⟨⟩⟩ := P.4.odd_iff.2 (by grind [lt_d]), P.5
  simp_all [← natCast_eq_zero_iff]
  induction n using Nat.twoStepInduction <;> grind
@[simp] lemma Parameters.placeClass_placeOfInt_eq_neg_one d :
  @placeClass P s P.N₀ d (P.placeOfInt s ν) = -1 ↔ (ν : ZMod P.N₀) = -1 := Units.ext_iff.trans
  ⟨by simp [placeOfInt, apply_dite, placeClass, unitsMap_val]; grind [P.pow_d_ne_neg_one 0], by
    simp_all [placeClass_placeOfInt (.symm _), ← coe_int_isUnit_iff_isCoprime]⟩
def Parameters.placePerm {P} s (σ : Gal(ℂ/K P)) := Equiv.mulLeft (.mk (.comp σ (Φ 1)) : P.Φ s)
lemma Parameters.placePerm_spec {P s σ} v x : σ (Φ v x) = Φ (@placePerm P s σ v) x := by
  simpa [placePerm,
    Φ] using! congr($(@algHom_eq_of_mk_eq P s _ (.comp σ ⟨Φ 1, by simp⟩) (mk_Φ _)) _).symm
end
variable {P s} {y : Parameters.E P s}
lemma Parameters.exists_zeta_pow_eq (h : IsOfFinOrder y) : ∃ k < P.N₁ s, ζ P s ^ k = y :=
  isPrimitiveRoot_zeta.eq_pow_of_pow_eq_one (by_contra (by grind [lt_d, by
  simpa [finrank_eq_two_mul_card_infinitePlace, Fintype.card_congr (placeMulEquiv ..).1, NeZero.pos,
    d_prime, Nat.totient_prime] using totient_mul_totient_le_finrank _ _ (coprime_N₁_d ..)
    isPrimitiveRoot_zeta <| .iff_orderOf.2 <| orderOf_eq_prime (pow_mul y .. ▸
    orderOf_dvd_iff_pow_eq_one.1 ((IsCyclotomicExtension.Rat.torsionOrder_eq.trans
      (ite_eq_left (by grind
    [Parameters]))).subst (@NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot _ _ _ ⟨by simpa⟩ _
    (.map_of_injective (.orderOf y) toCycloField.injective)))) ·]))
lemma Parameters.prod_phi_eq_norm : ∏ v, Φ v y = Algebra.norm P.K y := by
  simp [← phi_algebraMap _ s 1, Φ, Algebra.norm_eq_prod_automorphisms, ← (galOfPlace ..).prod_comp]
namespace Parameters
open Ideal Finset IntermediateField IsCyclotomicExtension NumberField Polynomial Algebra
  InfinitePlace RingOfIntegers NeZero QuadField algebraMap
variable {P s : _} {z : 𝓞 (E P s)}
abbrev zetaInt P s := (@isPrimitiveRoot_zeta P s).toInteger
@[simp] lemma coe_zetaInt : P.zetaInt s = P.ζ s := rfl
lemma isPrimitiveRoot_zetaInt : IsPrimitiveRoot (P.zetaInt s) (P.N₁ s) :=
  isPrimitiveRoot_zeta.toInteger_isPrimitiveRoot
abbrev c₀InE P s : 𝓞 (E P s) := c₀ P.d
def sqrtNegDInE P s := algebraMap _ (𝓞 (E P s)) (sqrtNegDInt P.d)
attribute [local simp] isPrimitiveRoot_zetaInt pos ne map_ofNat different_eq_span_and_adjoin_c₀
  prod_pow prod_nonneg sqrtNegDInE
@[simp] lemma coe_sqrtNegDInE : (P.sqrtNegDInE s).val = algebraMap _ _ (sqrtNegD P.d) :=
  congr(algebraMap P.K _ $(by simp [two_mul]))
lemma star_sqrtNegDInE : star (P.sqrtNegDInE s) = -P.sqrtNegDInE s :=
  ext (by simp [← map_star_CM, -sqrtNegDInE])
lemma star_zetaInt_pow_mul c : star (P.zetaInt s) ^ c * P.zetaInt s ^ c = 1 :=
  ext (by simp [isPrimitiveRoot_zeta.ne_zero])
lemma sqrtNegDInE_dvd :
  P.sqrtNegDInE s ∣ P.d := by simpa using congr(P.sqrtNegDInE s ∣ $(sqrtNegDInt_sq P.d))
lemma c₀InE_mul_one_sub P s : c₀InE P s * (1 - P.c₀InE s) = ↑((P.d + 1) / 4) := by
  simpa using congr(algebraMap _ (𝓞 _) $(c₀_mul_one_sub P.d))
lemma star_c₀InE P s :
  star (c₀InE P s) = 1 - P.c₀InE s := by grind [by simpa using @star_sqrtNegDInE P s]
instance : StablyUnram (P.E s) := ⟨_,
  isPrimitiveRoot_zeta.pow one_le (Nat.div_mul_cancel (by grw [N₁, ← P.3, towerDeg]; grind)).symm⟩
lemma relDifferent_spec (hz :
  IsPrimitiveRoot z (P.N₁ s)) : let y := (cyclotomic (P.N₁ s) _).derivative.eval z
  y ∣ P.N₁ s ∧ span {y} = differentIdeal (𝓞 P.K) _ ∧ (𝓞 P.K)[z] = ⊤ := by
  have hz' := hz.map_of_injective coe_injective
  have : IsCyclotomicExtension _ ℚ ℚ⟮_⟯ := hz'.intermediateField_adjoin_isCyclotomicExtension _
  have h := IsPrimitiveRoot.coe_submonoidClass_iff (ζ := AdjoinSimple.gen ℚ _).1 hz'
  rcases hz.isRoot_cyclotomic one_le, (cyclotomic_eq_minpoly h one_le).trans (minpoly_coe
    h.toInteger) ▸ conductor_mul_differentIdeal _ ℚ _ _ (adjoin_primitive_root_eq_top h),
    congr($((cyclotomic.dvd_X_pow_sub_one (P.N₁ s) _).choose_spec).derivative.eval z * z)
  refine ⟨?d, have := (coprime_N₁_d ..).symm.cast.mono sqrtNegDInE_dvd ?d; .imp_left .symm
    (differentIdeal_eq_span_of_dvd P.K (adjoin_primitive_root_eq_top hz') (cyclotomic (P.N₁ s)
      _) ?_ ?_ (.trans ?_ (IsDedekindDomain.map_differentIdeal_dvd_differentIdeal ℤ _ _ (𝓞 ℚ⟮z.val⟯)
      ?_)))⟩ <;> simp_all [isCoprime_span_singleton_iff, ← derivative_map, ← eval_map_apply, hz.1,
    ← eval_map_algebraMap, conductor_eq_top_of_adjoin_eq_top, Rat.adjoin_singleton_eq_top,
    derivative_pow, mul_assoc, pow_sub_one_mul, mem_span_singleton] <;> trivial
abbrev relDifferentGen P s := (cyclotomic (N₁ P s) _).derivative.eval (P.zetaInt s)
lemma relDifferentGen_dvd_N₁ : P.relDifferentGen s ∣ P.N₁ s := by simp [↓relDifferent_spec]
@[simp↓] lemma relDifferentGen_ne_zero P s :
  (relDifferentGen P s).val ≠ 0 := mod_cast ne_zero_of_dvd_ne_zero out relDifferentGen_dvd_N₁
lemma different_eq_span_relDifferentGen_mul : differentIdeal ℤ _ =
  span {P.relDifferentGen s * P.sqrtNegDInE s} := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal _ (𝓞 P.K)]
  simp [← (relDifferent_spec isPrimitiveRoot_zetaInt).2, span_mul_span]
lemma cycloConductor_mem_different : ↑(P.N₁ s * P.d) ∈ differentIdeal ℤ (𝓞 (P.E s)) := by
  grw [Nat.cast_mul, different_eq_span_relDifferentGen_mul, mem_span_singleton,
    relDifferentGen_dvd_N₁, sqrtNegDInE_dvd]
lemma exists_unit_mul_relDifferentGen_real : ∃ c, star c * c = 1 ∧ star (c * P.relDifferentGen s) =
  c * P.relDifferentGen s := by
  rw [relDifferentGen, cyclotomic_eq_prod_X_sub_primitiveRoots isPrimitiveRoot_zetaInt,
    ← mul_prod_erase (a := zetaInt ..)]
  refine induction_on' (erase ..) ⟨1, ?_⟩ ?_ <;> simp [isPrimitiveRoot_zetaInt.isPrimitiveRoot_iff]
  rintro _ _ - l - h rfl - _ k _ _
  cases (h.of_dvd_right (by grind [Parameters])).odd_of_right
  use StablyUnram.exists_i_c₀.choose * k * star (zetaInt ..) ^ ‹ℕ›.succ
  repeat simp_all <;> grind [star_zetaInt_pow_mul, pow_mul']
def ϖ P s :=
  (@exists_unit_mul_relDifferentGen_real P s).choose * (P.relDifferentGen s * P.sqrtNegDInE s)
lemma star_ϖ : star (P.ϖ s) = -P.ϖ s := by grind [ϖ, star_mul, star_sqrtNegDInE]
lemma different_eq_span_varpi : differentIdeal ℤ _ = span {P.ϖ s} := by
  grind [ϖ, span_singleton_mul_left_unit, isUnit_iff_exists, different_eq_span_relDifferentGen_mul]
lemma prod_varpi_eq_rootDiscr_pow : ∏ v : P.Φ s, v (P.ϖ s).val =
  rootDiscr (P.E s) ^ numInfPlaces (P.E s) := by
  rcases congr(√$(prod_eq_abs_norm (P.ϖ s).val)), congr(√$(@different_eq_span_varpi P s).absNorm)
  simp_all [← coe_norm_int, absNorm_differentIdeal (P.E s), abs_discr_eq_rootDiscr_pow,
    (rootDiscr_pos _).le]
lemma infinitePlace_apply_varpi (v : P.Φ s) : v (P.ϖ s).val = v (P.relDifferentGen s) * √P.d :=
  mk_Φ v ▸ by simp [ϖ, -sqrtNegDInE, -mk_Φ, by
  simpa using congr(√‖Φ v $(exists_unit_mul_relDifferentGen_real.choose_spec.1).val‖)]
end Parameters
end
end
section
open Algebra Ideal CharP FiniteField QuadField NeZero NumberField Polynomial ZMod
  IsDedekindDomain.HeightOneSpectrum NumberField.RingOfIntegers
namespace Parameters
attribute [local simp] coe_frobeniusAlgHom ne placeOfInt_pow map_ofNat neg_one_pow_eq_ite
variable {P : Parameters} {s} {p : ℕ} [hp : Fact p.Prime] {R} [CommRing R] [CharP R p] {v :
  P.Φ s} {w w' : FinPlace (P.E s)} (h : ¬p ∣ P.N₁ s) (φ : 𝓞 (P.E s) →+* R) (n) {c e} (he : c =
  RingEquiv.refl (𝓞 (P.E s))
  ∧ e = 1 ∨ c = starRingAut ∧ e = -1) (g : p ≡ 1 [MOD P.N₁ s * P.d]) (hw : ↑p ∈ w.1) (hc : ¬p ∣ P.N₁
  s * P.d) (hL : chiK P.d p = -1) {a : 𝓞 (P.E s)} (ha : ∃ c : ℕ, a * star a = p * c ∧ p.Coprime c)
noncomputable def galOfPlaceInt v := MulSemiringAction.toRingHom _ (𝓞 (P.E s)) (P.galOfPlace s v)
@[simp] lemma coe_galOfPlaceInt x : galOfPlaceInt v x = P.galOfPlace s v x := rfl
noncomputable instance : SMul (P.Φ s) (FinPlace (P.E s)) := ⟨(.comap <| P.galOfPlace s ·)⟩
@[simp] lemma mem_smul {x} : x ∈ (v • w).1 ↔ galOfPlaceInt v x ∈ w.1 := .rfl
@[simp] noncomputable def frobElem (p : ℕ) := (P.placeOfInt n (chiK P.d p * p), chiK P.d p)
include h in
lemma isCoprime_N₀_of_not_dvd :
  IsCoprime (p : ℤ) P.N₀ := mod_cast by grind [hp.1.coprime_iff_not_dvd]
include h he in
lemma frob_ext : (∀ x, φ (galOfPlaceInt v x) = φ (c x) ^ p ^ n) ↔ φ (galOfPlaceInt v
  (P.zetaInt s)) = φ (galOfPlaceInt (P.placeOfInt s (e * p ^ n)) (P.zetaInt s)) ∧ chiK P.d p ^ n *
  e * φ (P.sqrtNegDInE s) = φ (P.sqrtNegDInE s) := .trans ⟨fun e ↦ And.intro (e (zetaInt ..))
  (e (c₀InE ..)), fun _ x ↦ by induction (adjoin_eq_adjoin_union ℤ _ _
  (different_eq_span_and_adjoin_c₀ _).2).le ((relDifferent_spec isPrimitiveRoot_zetaInt).2.2.ge
  (x := x) ⟨⟩) using adjoin_induction <;> simp_all [← iterateFrobenius_def]; lia⟩ (by
  erw [← map_pow,
    eq_map_c₀_pow_iff (h <| · ▸ by grind [Parameters] : p ≠ 2) (φ.comp (c.toRingHom.comp _))]
  congrm _ = φ ?_ ∧ ?_ <;> cases he <;> simp [*, RingOfIntegers.ext_iff,
    (isCoprime_N₀_of_not_dvd h).pow_left, galOfPlace_placeOfInt_zeta, IsCoprime.neg_left,
    star_c₀InE, galOfPlaceInt.eq_1 v, sqrtNegDInE] <;> norm_cast <;> grind)
include he hc in
lemma frob_iff_eq_frobElem_pow [IsDomain R] : (∀ x, φ (galOfPlaceInt v x) = φ (c x) ^ p ^ n) ↔
  (v, e) = P.frobElem s p ^ n := by
  rw [hp.1.dvd_mul, not_or] at hc
  rcases of_not_dvd R hc.1, chiK_cases P.d p, (hc.1 <| · ▸ by grind [Parameters] : p ≠ 2),
    em (Even n)
  simp [val_lt, (val_injective _).eq_iff, Units.val_inj, (isRoot_cyclotomic_iff.1 (map_cyclotomic _
    φ ▸ (isPrimitiveRoot_zetaInt.isRoot_cyclotomic one_le).map)).injOn_pow.eq_iff,
    frob_ext hc.1 φ n he, (Subtype.ext (galOfPlace_zeta _) : galOfPlaceInt _ (zetaInt ..) =
    zetaInt .. ^ _), mul_left_eq_self₀, placeClass, mul_pow]
  erw [← sq_eq_zero_iff, map_sqrtNegDInt_sq (.comp ..)]
  casesm* _ ∨ _, _ ∧ _ <;> simp_all [_root_.neg_one_eq_one_iff, ringChar.eq, ringChar.spec]
attribute [local instance] Quotient.field ZMod.algebra
include he hw hc in
lemma smul_eq_iff_exists_frobElem_pow : v • w = comap c c.surjective w ↔ ∃ n, (v, e) =
  P.frobElem s p ^ n := have := w.charP_quotient hw
  ⟨fun H ↦ by
    exact ((bijective_frobeniusAlgHom_pow (ZMod p) _).2 (.mk' (quotientMap _ ((galOfPlaceInt v).comp
      c.symm) ((reindex_equiv c).1.2 (by simpa using! congr($H.1).ge))) (ZMod.map_smul _))).rec fun
      n e ↦ ⟨n, (frob_iff_eq_frobElem_pow _ n he hc).1 fun x ↦ by simpa using congr($e.symm (c x))⟩,
    fun ⟨n, H⟩ ↦ by ext; show _ ↔ c _ ∈ w.1; simp [← @Quotient.eq_zero_iff_mem _ _ w.1,
    (frob_iff_eq_frobElem_pow _ n he hc).2 H]⟩
lemma q_eq_pow (hw : ↑p ∈ w.1) (hc : ¬p ∣ P.N₁ s * P.d) : w.q = p ^ orderOf (P.frobElem s p) := by
  obtain ⟨_, ⟨⟩⟩ := w.charP_quotient hw, w.exists_q_eq_pow hw
  simp [*, galOfPlaceInt, p.pow_right_inj Fact.out, ← Nat.dvd_right_iff_eq, eq_comm,
    -frobElem, orderOf_dvd_iff_pow_eq_one, ← frob_iff_eq_frobElem_pow (Ideal.Quotient.mk w.1)]
include hw hc in
lemma natCast_notMem_sq : ↑p ∉ w.1 ^ 2 := hc ∘ (w.natCast_mem_iff_dvd hw).1 ∘
  (le_of_dvd · cycloConductor_mem_different) ∘ dvd_differentIdeal_of_mem_sq
include hw hc in
lemma intValuation_p : w.intValuation p = .exp (-1) := by simp [*, natCast_notMem_sq,
  intValuation_eq_exp_neg_multiplicity, multiplicity_eq_of_dvd_of_not_dvd (k := 1)]
lemma exists_smul_eq_or_star (hw : ↑p ∈ w.1) (h : ↑p ∈ w'.1) : ∃ v : P.Φ s, v • w = w' ∨
  star (v • w) = w' := (IsInvariant.exists_smul_of_under_eq ℤ _ Gal(P.E s/ℚ) w'.1 w
  (by ext (_ | _) <;> simp [*, -Nat.cast_add, @FinPlace.natCast_mem_iff_dvd _ _ _ p])).rec fun g _ ↦
  ⟨_, by refine (Φ_eq_or ((Φ 1).comp g.toRingHom)).imp ?_ ?_ <;> intro e <;> ext <;> simp <;>
  convert smul_mem_pointwise_smul_iff <;> ext <;> apply (Φ 1).injective <;>
  simpa [← phi_mul] using! congr($e _)⟩
@[local simp] lemma not_dvd_N₁_mul_d_of_inert (hL : chiK P.d p = -1) : ¬p ∣ P.N₁ s * P.d := by
  grind [chiK_eq_one_of_dvd, Fact, chiK_cases, hp.1.dvd_mul, p.prime_dvd_prime_iff_eq]
include hw hL
lemma smul_eq_iff_inert : v • w = w ↔ ∃ n, v = P.placeOfInt s (-p) ^ n ∧ Even n := by
  simpa [*] using! smul_eq_iff_exists_frobElem_pow (.inl ⟨rfl, rfl⟩) hw
lemma smul_eq_star_iff_inert : v • w = star w ↔ ∃ n, v = P.placeOfInt s (-p) ^ n ∧ Odd n := by
  simpa [*] using! smul_eq_iff_exists_frobElem_pow (.inr ⟨rfl, rfl⟩) hw
lemma q_eq_inert : w.q =
  p ^ (orderOf (P.placeOfInt s (-p))).lcm 2 := by simp [q_eq_pow hw, *, Prod.orderOf]
omit hw hL
include g
omit [Fact p.Prime] in
lemma chiK_eq_one_of_modEq_one : chiK P.d p = 1 := by simp [natCast_eq_natCast' _ _ g.of_mul_left]
@[local simp] lemma not_dvd_N₁_mul_d_of_modEq_one : ¬p ∣ P.N₁ s * P.d :=
  g.dvd_iff.mt (by simp [hp.1.ne_one])
omit [Fact p.Prime] in
lemma frobElem_eq_one : P.frobElem s p = 1 := by simp [placeOfInt, chiK_eq_one_of_modEq_one g,
  natCast_eq_natCast' _ _ g.of_mul_right]
include hw
lemma smul_ne_star : v • w ≠ star
  w := by simpa [↓frobElem_eq_one, *] using! smul_eq_iff_exists_frobElem_pow (.inr ⟨rfl, rfl⟩) hw
lemma smul_eq_self_iff_eq_one : v • w = w ↔ v = 1 := by
  simpa [↓frobElem_eq_one, *] using! smul_eq_iff_exists_frobElem_pow (.inl ⟨rfl, rfl⟩) hw
lemma q_eq_of_modEq_one : w.q = p := by simp [q_eq_pow hw, ↓frobElem_eq_one, *]
include ha
lemma star_mem_iff : star a ∈ w.1 ↔ a ∉ w.1 :=
  ha.rec fun _ c ↦ by grind [mul_mem_right, natCast_notMem_sq
  hw (by aesop), sq, mul_mem_mul, w.2.mem_pow_mul, w.2.notMem_of_isCoprime_of_mem c.2.cast hw]
lemma intValuation_eq_of_mul_star (k : a ∈ w.1) : w.intValuation a = .exp (-1) := by
  grind [intValuation_p, not_dvd_N₁_mul_d_of_modEq_one, intValuation_eq_one_iff, star_mem_iff,
    w.natCast_mem_iff_dvd, hp.1.coprime_iff_not_dvd, map_mul w.intValuation a (star a)]
omit hw
lemma nonempty_infinitePlace_equiv_finPlace : Nonempty (P.Φ s ≃ {w : FinPlace _ // a ∈ w.1 ∧
  ↑p ∈ w.1}) := by refine (FinPlace.exists_natCast_mem _ p).rec fun w _ ↦
  ⟨.ofBijective (fun v ↦ ⟨ite (a ∈ (v • w).1) (v • w) (star (v • w)), ?_⟩)
  ⟨fun u v ↦ have : v • w = (u⁻¹ * v) • u • w := by ext; simp [galOfPlaceInt, smul_smul]
  ?_, fun _ ↦ ?_⟩⟩ <;> grind [mem_star_place, star_mem_iff, mem_smul, map_natCast, star_natCast,
  exists_smul_eq_or_star, star_star, smul_ne_star, smul_eq_self_iff_eq_one, inv_mul_eq_one]
end Parameters
variable {P : Parameters} {s}
lemma Parameters.valuation_map_relDifferentGen (f : _ →+* 𝓞 (P.E s)) (h : (⇑f).Injective) (w :
  FinPlace (P.E s)) : w.valuation _ (f (P.relDifferentGen s)).val =
  w.valuation _ (P.relDifferentGen s).val := by simp [↓valuation_of_algebraMap, intValuation_def,
  ← span_singleton_eq_bot, ← eval_map_apply, ← derivative_map, relDifferent_spec,
  isPrimitiveRoot_zetaInt.map_of_injective h, isPrimitiveRoot_zetaInt]
noncomputable def Parameters.α P s := let e := idem {w | c₀InE P s ∈ w.1}
  (Units.mk0 _ (P.relDifferentGen_ne_zero s))⁻¹.map
    ⟨⟨(e * algebraMap _ _ · + (1 - e)), by simp⟩, by grind [idem_mul_self]⟩
attribute [local simp] valuation_le_one Parameters.star_c₀InE Parameters.α idem_apply mem_Ô
  mul_le_one'
lemma Parameters.inv_α_mem : (P.α s)⁻¹.1 ∈ Ô _ := by aesop
lemma Parameters.v_alpha_mul_relDifferentGen w :
  Valued.v ((P.α s * star (P.α s).1 * P.relDifferentGen s) w) = 1 := by
  simp [-star_add]
  split_ifs <;> simp_all [w.1.sub_mem_iff_left, valuation_map_relDifferentGen _ star_injective _ ▸
    valuation_star w _, one_notMem, mt (w.2.2 ∘ (c₀InE_mul_one_sub ..).substr ∘ w.2.mem_of_pow_mem
    (P.N₁ s) ∘ mem_of_dvd _ (.trans relDifferentGen_dvd_N₁
    (mod_cast .natCast (by grind [(N₁ ..).dvd_pow_self_iff out, dvd_norm_c₀, lt_d]))))]
lemma Parameters.N₁_mul_α_mem : P.N₁ s * (P.α s).1 ∈ Ô _ := by simp_all [field, apply_ite,
  ite_apply, by simpa using congr(($((@relDifferentGen_dvd_N₁ P s).choose_spec).val : 𝔸f (P.E s)))]
noncomputable instance Parameters.instWeilDataE : WeilData (P.E s) := by
  have := (nonempty_splittingChar fun (y : P.E s) h ↦
    (exists_zeta_pow_eq h).choose_spec.2 ▸ let m := P.N₁ s / 4
    have N : Algebra.norm P.K (P.zetaInt s ^ m * (P.zetaInt s - 1)).val = 1 := by erw [map_mul,
                isPrimitiveRoot_zeta.sub_one_norm_eq_eval_cyclotomic, map_pow,
      isPrimitiveRoot_zeta.norm_eq_one, one_pow,
      eval_one_cyclotomic_not_prime_pow fun _ _ _ ↦ ?_] <;> grind [Parameters, ne (P.N₁ s),
      Nat.prime_eq_prime_of_dvd_pow, Nat.prime_two, Nat.prime_three, irreducible_cyclotomic]
    ⟨((RingOfIntegers.isUnit_norm _).1 ⟨1, ext N.symm⟩).unit ^
      (exists_zeta_pow_eq h).choose, by simp [↓prod_phi_eq_norm,
      N, -map_mul], congr($(show P.zetaInt s ^ _ * star _ = _ by simp [← mul_pow]; congr 1; grind
      [star_zetaInt_pow_mul 1, (isPrimitiveRoot_zetaInt.pow one_le (by grind [Parameters] :
      P.N₁ s = m * 2 * 2)).eq_neg_one_of_two_right, star_zetaInt_pow_mul, pow_mul']))⟩).some
  use -(P.sqrtNegDInE s).val⁻¹, ?_, ?_, P.α s, fun w ↦ by simpa [field,
    different_eq_span_relDifferentGen_mul, ← v_algebraMap_eq_intValuation,
    v_algebraMap_eq_valuation] using (congr($(v_alpha_mul_relDifferentGen ..) /
    $(w.intValuation_eq_exp_neg_multiplicity (ne_zero_of_differentIdeal_eq_span
    different_eq_span_relDifferentGen_mul)))), by simp [sqrtNegDInE, map_ofNat, isIntegral_coe],
    exists_eq_principalIdele_mul_norm.2.2 <;> simp [← map_star_CM, pos]
end
section
noncomputable def Parameters.vacuumRoot P s := (chiFin (α P s))⁻¹ ^ (numInfPlaces (P.E s) : ℂ)⁻¹
open NumberField Real
lemma Parameters.norm_gal_vacuumRoot P s (σ : Gal(ℂ/K P)) : ‖σ (vacuumRoot P s)‖ ^ 2 =
  rootDiscr (P.E s) / √P.d := by
  obtain ⟨k, h, ⟨⟩⟩ := WeilData.exists_chiFin_pow_eq_prod (P.α s)
  erw [rootDiscr, ← pow_left_inj₀, div_pow, ← prod_varpi_eq_rootDiscr_pow, pow_right_comm,
    ← norm_pow, ← map_pow]
  simp [vacuumRoot, by simpa [h.ne'] using congr(‖$(σ.commutes ⟨chiFin (P.α s) ^ k, by simp_all
    [prod_phi_eq_norm]⟩)‖)]
  simpa [ideleAbs_toAdele, Finset.prod_pow, infinitePlace_apply_varpi, chiFin, Circle.norm_coe,
    ← InfinitePlace.apply, Finset.prod_nonneg, NeZero.ne, chiAdelic, field] using
    (ideleAbs_eq_prod_of_v_eq_one (x := finIdeleIncl _ * star (finIdeleIncl _) * .map toAdele.1
    (.mk0 _ (P.relDifferentGen_ne_zero s))) (by simpa using v_alpha_mul_relDifferentGen) :)
  repeat positivity
noncomputable def Parameters.cmCurve (P : Parameters) :=
  (@QuadField.exists_latticeModule_eq_scaledIdeal P.d _ 1).choose
noncomputable def Parameters.Ω₀ (P : Parameters) :=
  (@QuadField.exists_latticeModule_eq_scaledIdeal P.d _ 1).choose_spec.choose
noncomputable def Parameters.areaScale (P : Parameters) : ℂˣ :=
  .mk0 √(2 * π / √P.d) (by simp [pi_nonneg, NeZero.ne])
noncomputable def Parameters.periodFactor (P : Parameters) s :=
  P.vacuumRoot s / P.cmCurve.chowla_selberg.choose
noncomputable def Parameters.jetScale (P : Parameters) s := P.periodFactor s * P.areaScale / P.Ω₀
end
section
open MvPowerSeries Finset ComplexConjugate LinearTopology NumberField IsLocalRing CharP
attribute [local simp] subst_comp_subst_apply subst_mul subst_smul constantCoeff_subst_eq_zero
  sum_pow_char_pow smul_sum pderiv_X sum_pow_char smul_pow Real.rpow_neg norm_p_eq_inv
variable {p Q J} [fp : Fact p.Prime] [CommRing Q] [CharP Q p] [Fintype J] (P : Parameters) (s)
lemma sum_pow_eq_zero_of_null {B e ρ} {t L : J → Q} (he : e = 1 ∧ ρ ∨ e = 2) (ht : ∀ i,
  t i - t i ^ p ^ e = L i) (t0 : ∀ i, ∀ n ≥ B, t i ^ p ^ n = 0) (hq : ∀ j, Odd j ∨ ρ → ∑ i, L i ^
  p ^ j * L i = 0) : ∑ i, t i ^ (p + 1) = 0 ∧ ∑ i, t i ^ (p + p ^ e) = 0 := by simp (disch := grind)
  [(eq_sum_pow_of_sub_pow_eq (ht _) B).trans ∘ add_eq_left.2, sum_mul_sum, ← pow_mul,
  @sum_comm _ _ J, ← pow_add p, ← pow_succ, ↓pow_add (t _), fun a b (h : Odd (a + b) ∨ ρ) ↦ (by
  induction a, b using Nat.recDiagAux <;> simp (disch := grind [fp.1.pos]) [*, pow_succ, pow_mul,
    ← mul_pow, ← sum_pow_char, mul_comm (L _)] : ∑ i, L i ^ p ^ a * L i ^ p ^ b = 0)]
lemma coeff_sum_frob_ne_zero_iff {Φ I} [Fintype Φ] {r : Φ → J → Q} {t : J → MvPowerSeries (Φ × I) Q}
    (t0 : ∀ i, constantCoeff (t i) = 0) x {c} (ht : ∀ i, t i - t i ^ p ^ 2 = ∑ v, C (r v i) * X
    (v, c)) d : coeff d (∑ i, t i ^ p * C (r x i)) ≠ 0 ↔ ∃ n y,
    ∑ i, r y i ^ p ^ (2 * n + 1) * r x i ≠ 0 ∧ d = .single (y, c) (p ^ (2 * n + 1)) := by
  rcases fp.1.one_lt, charP_of_injective_ringHom (@C_injective (Φ × I) Q _)
  simp (disch := grind [Nat.lt_pow_self]) [congrArg (· ^ p) (eq_sum_pow_of_sub_pow_eq (ht _)
    d.degree), add_pow_char, ← pow_mul, ← pow_succ, ← smul_eq_C_mul, sum_mul, @sum_comm _ _ J,
    coeff_X_pow, coeff_eq_zero_of_constantCoeff_nilpotent (m := 1), ← sum_product']
  use (by grind [exists_ne_zero_of_sum_ne_zero ·]), fun ⟨n, y, _⟩ ↦ by rw [sum_eq_single (n, y)] <;>
    grind [Nat.lt_pow_self, Nat.pow_right_inj, Finsupp.degree_single, Finsupp.single_eq_single_iff]
namespace Parameters
variable [PadicPlace p]
def thetaProducts (δ : 𝓞 P.K) r c [Fintype c] := {Θ | ∃ J, ∃ (_ : Fintype J) (w : J → P.E s), ∃ M n
  b, ∃ y : J × c → ℂ, IsTightFrame w 1 M ∧ Θ = ∏ i, (taylorVia ιₚ (P.cmCurve.twistedTranslate 1 (y
  i) P.cmCurve.θ)).subst (linearSeries fun (τ, k) ↦ ite (k = i.2) (ιₚ (b * conj (Φ τ (w i.1)))) 0) ∧
  (p.Coprime M ∧ p.Coprime n) ∧ ‖ιₚ b‖ = r ∧ ∀ i, n * δ * y i ∈ P.cmCurve.Λ}
lemma exists_frame_rows_frob (hp : chiK P.d p ≠ 1) {w : J → _} {M} (hw : IsTightFrame w 1 M) β :
  ∃ z : _ → _ → valRingCp p, (∀ v i, z v i = β.1 * ιₚ (conj (Φ v (w i)))) ∧ ∀ (Q : Type)
  [CommRing Q] [CharP Q p] (g : _ →+* Q), (∀ x, ‖x.1‖ ≤ p ^ ((chiK P.d p - 1) / 2 : ℝ) → g x = 0) →
  ∀ j, Odd j ∨ p = P.d → ∀ v v', ∑ i, g (z v i) ^ p ^ j * g (z v' i) =
  ite (P.placeOfInt s (-p ^ j) * v = v') (g β ^ p ^ j * g β * M) 0 := by
  let N := P.N₁ s
  let x i := IsIntegralClosure.mk' (𝓞 (P.E s)) (N * w i) (algebraMap_mem_Ô.1 (by
    simpa [N, mul_assoc, finiteImage, WeilData.α] using mul_mem N₁_mul_α_mem (hw.1 i)))
  have hd := hp ∘ @chiK_eq_one_of_dvd P p s fp.1; obtain ⟨α, ⟨⟩⟩ : ↑N ∣ β := IsUnit.dvd (by
    simpa [← residue_ne_zero_iff_isUnit, cast_eq_zero_iff])
  let f v := ((ιₚ.comp (Φ v)).comp (algebraMap _ (P.E s))).codRestrict (valRingCp p)
    (id (norm_ringOfIntegers_le (ιₚ.comp _)))
  use fun v i ↦ f v (star (x i)) * α, by simp [f, x, field], fun Q _ _ g h j _ v v' ↦ ?_
  simpa [by simpa using (frob_ext hd (g.comp (f v)) j (.inr ⟨rfl, rfl⟩)).2 ⟨rfl, by
    obtain ⟨⟨⟨⟩, _⟩ | _⟩ := chiK_cases P.d p, h (f v (P.sqrtNegDInE s)), congr(√‖(f v (algebraMap _
      _ $(QuadField.sqrtNegDInt_sq P.d))).1‖) <;> simp_all [sqrtNegDInE, Real.sqrt_eq_rpow P.d,
      neg_div]⟩, apply_ite, sum_mul, ← iterateFrobenius_def, mul_mul_mul_comm _ (iterateFrobenius Q
    p j _), mul_right_comm _ (M : Q)] using congrArg (g · * (g α ^ p ^ j * g α)) (show
    ∑ i, f v (galOfPlaceInt (P.placeOfInt s (-p ^ j)) (x i)) * f v' (star (x i)) = ite (_ = v') (N *
    N * M) 0 by ext; simpa [f, x, ← phi_mul, mul_comm v, mul_mul_mul_comm _, mul_sum, apply_ite]
    using congr(N * N * ιₚ $(hw.2 ..)))
lemma thetaProducts_normal_form (hp : chiK P.d p ≠ 1) : ∃ ϖ π, ‖ϖ‖ = p ^ (-nonsplitWeight P.d
  p) ∧ ‖π.1‖ = p ^ ((chiK P.d p - 1) / 2 : ℝ) ∧ ∀ {I} [Fintype I], ∀ r ≤ 1, ∀ Θ ∈ P.thetaProducts
  s 1 r I, (∀ B, IsIntegralOnNullCone (fun j v ↦ P.placeOfInt s (-p ^ j) * v) {j ≤ p.log B | Odd j ∨
  p = P.d} ϖ π B Θ) ∧ (chiK P.d p = -1 → r = 1 → ∃ (κ : ℂ_[p]) (Ψ V : MvPowerSeries _
  (valRingCp p)), ‖κ‖ = p ^ (1 - 1 / (p - 1) : ℝ) ∧ constantCoeff Ψ = 0 ∧ Θ.rescale (fun _ ↦ ϖ) =
  expSubst (κ • seriesToCp Ψ) * seriesToCp V ∧ ∀ x d, (pderiv x (Ψ.map (residue _))).coeff d ≠ 0 ↔
  ∃ j y, Odd j ∧ (P.placeOfInt s (-p ^ j) * y.1, y.2) = x ∧ d = .single y (p ^ j)) := by
  obtain ⟨⟨e, ϖ, π, S, E, ⟨-, hϖ, hπ, π1, S0, ε, _⟩, H⟩, hP⟩ := P.cmCurve.exists_formal_parameter,
    fp.1
  obtain ⟨_, _, _, R, _, hπ', he, ⟨⟩, ψ0, hV⟩ := H hp (P.thirteen_le_of_chiK_ne_one hP hp)
  set ψ := _ + π • R; use ϖ, π, hϖ, hπ'; rintro I _ _ ha Θ ⟨J, _, w, M, n, b, y, hw, _, hM, ⟨⟩, hy⟩
  choose N κ hκ v ev using hV n hM.2
  obtain ⟨z, hz, hF⟩ := hπ' ▸ P.exists_frame_rows_frob s hp hw ⟨_, mul_mem hκ.1.le ha⟩
  simp [hP.coprime_iff_not_dvd] at hM S0 ψ0 hy
  let c (i : J × I) := @PowerSeries.substAlgHom (valRingCp p) _ _ (valRingCp p) _ _
    (∑ v, z v i.1 • X (v, i.2)) (by simp); let Ψ := ∑ i, c i ψ
  have cX i : c i .X = _ := substAlgHom_X ..
  refine Exists.elim ?_ fun V (⟨Ψ0, eV, cS⟩ : _ ∧ _ ∧ ∀ i, constantCoeff (c i S) = 0) ↦
    ⟨fun B τ Z Z0 hq m hm ↦ ?_, fun h _ ↦ ⟨κ, Ψ, V, by simp [*], Ψ0, eV, fun x d ↦ ?_⟩⟩
  use ∏ i, c i (v (y i) (hy _ _))
  simp (disch := simp [*]) [c, Ψ, map_subst, expSubst_sum, *, PowerSeries.substAlgHom, -map_mul]
  simp [linearSeries, *, PowerSeries.subst, Fintype.sum_prod_type, mul_smul]
  let σ := substAlgHom (R := valRingCp p) (hasSubst_of_constantCoeff_zero Z0)
  have ⟨Q, φ, K⟩ : ∃ Q : CommRingCat, ∃ φ : _ →+* Q, RingHom.ker φ = (basis τ (valRingCp p)
    ((Valuation.leIdeal _ ‖π.1‖₊).toTwoSided, m)).asIdeal := ⟨.of _, _, Ideal.mk_ker⟩
  simp [Ideal.ext_iff, basis, ← NNReal.coe_le_coe] at K
  have hT := (K (σ Ψ)).1 (by
    nontriviality
    have K0 x := by simpa [coeff_C, apply_ite, ite_apply, @forall_comm (_ ≤ m)] using (K (C x)).2
    have := of_eq_zero hP (by simpa [hπ] using K0 p)
    have t0 f e n hn := (K (f ^ p ^ n)).2 fun d h ↦ by
      rw [coeff_eq_zero_of_constantCoeff_nilpotent e (Nat.one_add_le_iff.2 (((d.degree_mono
        h).trans hm).trans_lt (p.lt_pow_of_log_lt hP.one_lt hn)))]; simp
    obtain ⟨E, hq⟩ := (congr(φ <| σ <| c · $ε)), hq φ
    simp [cX, K0, @smul_eq_C_mul τ, -Prod.forall, Fintype.sum_prod_type_right] at E t0 hq
    obtain ⟨hq⟩ := (iff_self_and.2 (sum_pow_eq_zero_of_null (he.imp_right (·.1)) E fun _ ↦ t0 _ (by
      simp [σ, cS, Z0]))).1 fun j h ↦ by
      simp [σ, ↓substAlgHom_X, mul_pow, sum_mul_sum, by simpa using hF _ (φ.comp C) K0 j h,
        mul_mul_mul_comm _ (φ _ ^ _), @sum_comm _ _ J, ← sum_mul, ← mul_sum, Fintype.sum_prod_type]
      by_cases! j ≤ p.log B <;> simp [*]
    simp [ψ, Ψ, *, ← mul_sum, @smul_eq_C_mul τ, sq]
    cases he <;> simp [by simpa using hq 0, *])
  apply_fun subst (seriesToCp <| Z ·) at eV
  simp [σ, ← map_subst, Ψ0, Z0, rescale_eq_subst, PowerSeries.subst] at eV hT
  refine eV ▸ sum_mem fun d h ↦ mul_mem ((PowerSeries.coeff_subst (by simp [*]) ..).symm.subst
    (finsum_induction _ (by simp) @(valRingCp p).add_mem fun k ↦ ?_)) (by simp)
  simp [coeff_pow, mul_sum]; refine sum_mem fun l e ↦ (?_ : ‖_‖ ≤ 1)
  simp at h e ⊢; grw [← rpow_le_norm_factorial, hT] <;> (try simp [*, hP.pos, ← Real.rpow_add,
            ← Real.rpow_mul_natCast, Real.rpow_pos_of_pos]); ring_nf; simp
  grw [← h, ← e.1, ← single_le_sum _ ‹_›] <;> simp
  obtain ⟨⟨⟩⟩ := he.resolve_left (by simp [·, chiK] at h)
  have K (x : valRingCp p) h := (residue_eq_zero_iff x).2 (π1.not_ge <|
    isUnit_integer_iff_norm_eq_one.1 · ▸ h)
  have E i := congr((fun f ↦ (f, pderiv x f)) (map (residue _) (c i $ε)))
  simp [cX, @smul_eq_C_mul (_ × I), K, ← map_natCast C, cast_eq_zero] at E
  simpa [ψ, cast_eq_zero, Ψ, *, ← mul_sum, @smul_eq_C_mul (_ × I), ← map_natCast C, Odd, ite_and,
    Fintype.sum_prod_type, Prod.ext_iff, cast_eq_zero_iff, hF _ _ K] using
    coeff_sum_frob_ne_zero_iff (by simp [cS]) x.1 (E · x.2 |>.1) d
end Parameters
end
section
open ComplexConjugate Finset Ideal NeZero Polynomial ZMod
variable {P : Parameters} {s} {p : ℕ} [Fact p.Prime] [ι : PadicPlace p]
lemma Parameters.coe_trace_eq_sum z : Algebra.trace P.K (P.E s) z = ∑ τ, Φ τ z := P.phi_algebraMap
  s 1 _ ▸ by simp [← phi_mul, trace_eq_sum_automorphisms, reindex_equiv (P.galOfPlace s)]
lemma Parameters.herm_mem_quadInt {y} x (h : finiteImage id x ∈ Ô (P.E s)) (k :
  finiteImage id y ∈ Ô _) : ∑ τ, Φ τ x * conj (Φ τ y) ∈ quadInt P.d :=
  .imp (by simp_all [coe_trace_eq_sum, Algebra.smul_def]) ((differentialIdeal_le_iff
  (K := P.K) (by simpa using mod_cast P.relDifferentGen_ne_zero s)).1
  (relDifferent_spec isPrimitiveRoot_zetaInt).2.1.ge ⟨x * star y, by
  simpa [Submodule.mem_span_singleton, -map_inv₀] using ⟨⟨_, algebraMap_mem_Ô.1 (by
  convert mul_mem (mem_Ô.2 (v_alpha_mul_relDifferentGen · |>.le))
    (mul_mem h (star_mem_Ô k)); simp [finiteImage, WeilData.α]
  grind [Units.mul_inv, star_mul, star_one])⟩, div_eq_of_eq_mul (by simp) rfl⟩, rfl⟩)
omit [PadicPlace p] in
@[local simp] lemma Parameters.adeleExtension_alpha (φ : _ →+* ℂ_[p]) : adeleExtension φ (P.α s).1 =
  ite (P.c₀InE s ∈ (placeOfEmb φ).1)
  (φ (P.relDifferentGen s))⁻¹ 1 := by split <;> simp [α] <;> simp [adeleExtension, *]
lemma Parameters.norm_iota_periodFactor τ : ‖ιₚ (P.periodFactor s)‖ = ‖adeleExtension
  (weightEmbedding ιₚ τ) (P.α s).1‖⁻¹ := by
  have A u := (isEquiv_placeOfEmb (weightEmbedding ιₚ 1)).eq_iff.2
    (@valuation_map_relDifferentGen P s (galOfPlaceInt u) (MulAction.injective _) _)
  rw [← pow_left_inj₀ _ _ (ne (Fintype.card (P.Φ s))), ← norm_pow, ← map_pow] <;> simp_all
    [periodFactor, div_pow, P.cmCurve.chowla_selberg.choose_spec, NNReal.eq_iff,
    WeilData.norm_map_chiFin, vacuumRoot, apply_ite, @starRingEnd_apply (P.E s), ← phi_mul,
    (show Φ · (P.c₀InE s).val = _ from phi_algebraMap ..)]
lemma Parameters.norm_periodFactor_mul_conj_le_one {y} (h :
  finiteImage id y ∈ Ô (P.E s)) τ : ‖ιₚ (P.periodFactor s * conj (Φ τ y))‖ ≤ 1 := by
  simpa [finiteImage, -adeleExtension_alpha, norm_iota_periodFactor τ, starRingEnd_apply y] using!
    norm_adeleExtension_le_one (weightEmbedding ιₚ _) h
variable (P s)
lemma Parameters.norm_iota_periodFactor_eq_one (h : ¬p ∣ P.N₁ s) : ‖ιₚ
  (P.periodFactor s)‖ = 1 := by simp [norm_iota_periodFactor 1, apply_ite, -RingHom.coe_comp,
  (norm_ringOfIntegers_le ..).eq_of_not_lt (h ∘ (FinPlace.natCast_mem_iff_dvd _
  (natCast_mem_placeOfEmb _)).1 ∘ mem_of_dvd _ relDifferentGen_dvd_N₁ ∘ (mem_placeOfEmb ..).2)]
lemma Parameters.isTightFrame_zeta_pow k :
  IsTightFrame (fun i : Fin (N₁ P s) ↦ P.ζ s ^ i.1) (fun _ ↦ k) (k * P.N₁ s) :=
  ⟨fun _ ↦ mul_mem inv_α_mem (algebraMap_mem_Ô.2 ((zetaInt ..).2.pow _)), fun σ τ ↦ by
  split <;> simp [*, starRingEnd_apply, ← map_star_complex, -inv_pow, ← mul_pow, ↓← mul_sum,
    ← sum_range, isPrimitiveRoot_zeta.ne_zero out]
  erw [geom_sum_eq fun h ↦ ‹¬_›
    (Function.LeftInverse.injective mk_Φ congr($((isPrimitiveRoot_zeta.powerBasis P.K).algHom_ext
    (eq_of_mul_inv_eq_one h)).1))]; simp [mul_pow, ← map_pow, isPrimitiveRoot_zeta.1]⟩
lemma Parameters.exists_cyclotomic_different_factor {R N} [CommRing R] [IsDomain R] [CharZero R] {ζ}
  (hζ : IsPrimitiveRoot ζ N) (l : N.primeFactors) : ∃ r, ∃ M ≤ N, N = l * r ∧ (∀ p ∈ N.primeFactors,
  p ∣ M ↔ p ≠ l) ∧ ∃ V, V ∣ ↑M ∧ (cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1) * M = N * V := by
  have ⟨hl, ⟨r, e⟩, hN⟩ := N.mem_primeFactors.1 l.2
  obtain ⟨⟨q, hq⟩, a, M, hM, rfl⟩ := @X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd R _ r N
    (by simp_all [hl.one_lt, zero_lt_iff]), r.exists_eq_pow_mul_and_not_dvd (by lia) _ hl.ne_one
  have := by simpa [← expand_mul, expand_pow_cyclotomic hl, ← e, M.mul_comm, mul_assoc, hζ.1,
    derivative_expand, (hζ.isRoot_cyclotomic hN.bot_lt).eq_zero, pow_sub_one_mul hN,
    derivative_X_pow, -Nat.cast_mul] using congr(((expand R (l ^ a)
    $(cyclotomic_expand_eq_cyclotomic_mul hl hM R)).derivative.eval ζ, (derivative $hq).eval ζ * ζ))
  refine Dvd.elim ?_ (⟨_, M, by grw [e, ← hl.one_le]; lia, e, by grind [Nat.Prime.dvd_mul,
    Nat.prime_eq_prime_of_dvd_pow, Nat.prime_dvd_prime_iff_eq], ·, ⟨q.eval ζ * ζ,
    nsmul_right_injective hN (by grind)⟩, ·⟩)
  convert mul_dvd_mul_right ((dvd_of_mul_right_dvd (Dvd.intro_left _ this.1)).trans
    (mul_dvd_mul_left _ (eval_dvd (cyclotomic.dvd_X_pow_sub_one ..)))) _ <;> simp [e] <;> ring
lemma Parameters.exists_isTightFrame {m R} (hR : (P.d * P.N₁ s) ^ 6 * (R + 1) ≤ m) :
    ∃ I, ∃ (_ : Fintype I) (v c : I → _), IsTightFrame v c m ∧ (∀ i, R ≤ c i) ∧ ∃ i, ∀ τ, ‖ιₚ
    (P.periodFactor s * conj (Φ τ (v i : P.E s)))‖ = 1 := by
  obtain ⟨hϵ, hζ, h0, hG⟩ := P.c₀InE_mul_one_sub s, @isPrimitiveRoot_zetaInt P s, ne (P.N₁ s),
    P.isTightFrame_zeta_pow s 1
  set N := N₁ ..
  set n := _ / 4
  choose r M hN hr _ V hV _ using exists_cyclotomic_different_factor hζ
  have ⟨f, hf⟩ : N ∣ n ^ N := by grind [N.dvd_pow_self_iff, dvd_norm_c₀, lt_d]
  have ⟨z, hz, e, he⟩ : ∃ z < N, N ∣ n * z ^ 2 + z + 1 := (@Finite.surjective_of_injective
    (ZMod N) _ (fun y ↦ n * y ^ 2 + y) (fun a b h ↦ (IsNilpotent.isUnit_add_one (r := n *
    (a + b)) ⟨N, by simp [mul_pow, ← n.cast_pow, hf]⟩).mul_left_cancel (by linear_combination h))
    (-1)).elim (⟨_, val_lt ·, by simp [← natCast_eq_zero_iff, ·]⟩)
  let t := 1 - P.c₀InE s + n * z
  set c := ∑ l, (N + M l * (1 + 2 * n * (z + l * (M l * e)))) with E
  replace hR : R * (c + N) + N.pred * c.pred ≤
    m := by grw [← hR, c.pred_le, ← (by grind [lt_d] : n + 2 ≤ P.d),
    E.trans_le (by grw [hN, N.le_of_mem_primeFactors (coe_mem _),
    ← he, hz]), sum_const, univ_eq_attach, card_attach, card_le_card fun _ ↦ mem_Iic.2
    ∘ N.le_of_mem_primeFactors, N.card_Iic, N.pred_le]; cases N <;> lia
  have ⟨B, A, _⟩ := N.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le c _ ((N.coprime_of_dvd
    fun p _ _ ↦ by rw [← natCast_eq_zero_iff, Nat.cast_sum, Fintype.sum_eq_single ⟨p, by grind⟩] <;>
    grind [natCast_eq_zero_iff, dvd_norm_c₀]).dvd.trans (one_dvd _)) (le_tsub_of_add_le_left hR)
  let a := (P.zetaInt s ^ r ·)
  let u : (Σ l, Fin (r l) × Fin l × Fin l) → P.E s | ⟨l, ⟨j, _⟩, ⟨k, _⟩, i, _⟩ => P.zetaInt s ^ j *
    (0 ^ k * a l ^ i + t * M l / N * (a l ^ i - a l ^ k))
  refine ⟨_, inferInstance, Sum.elim u _, (cond ·.isLeft A B + R), ⟨Sum.rec (fun ⟨l, j, k, i⟩ ↦
    mem_Ô.2 fun v ↦ ?m) hG.1, fun σ τ ↦ ?_⟩, by simp, by_cases (⟨.inr 0, ·⟩) fun h ↦ ?_⟩
  · simp [← mul_sum, by simpa using hG.2]
    rw [Fintype.sum_sigma, sum_congr rfl fun l ↦ ?_, ← ite_sum_zero (σ = τ), ← Nat.cast_sum, ← E]
    split <;> norm_cast; lia
    have := Fact.mk (N.prime_of_mem_primeFactors l.2)
    have C := (hζ.pow h0.bot_lt (hr l ▸ mul_comm ..)).geom_sum_eq_zero Fact.out
    have := congr((Φ τ $hϵ, ($he : ℂ), Φ τ $(P.star_c₀InE s), $(hr l ▸ hG.2 σ τ), Φ σ $C,
      conj (Φ τ $C)))
    simp [sum_range, pow_add, pow_mul, ← hr, mul_assoc, ← mul_sum, reindex_equiv finProdFinEquiv,
      Fintype.sum_prod_type_right] at this
    simp [*, u, a, Fintype.sum_prod_type, @zero_pow_eq ℂ, apply_ite conj, mul_assoc, -nsmul_eq_mul,
      ← smul_sum, mul_left_comm (_ ^ _) (_ / _), mul_add, add_mul, sub_eq_add_neg,
      ← mul_sum, ← sum_mul]
    split <;> simp [t, field]; grobner
  · let l : N.primeFactors := ⟨p, by grind [norm_iota_periodFactor_eq_one, Fact, by simpa using h]⟩
    use .inl ⟨l, ⟨0, by grind⟩, ⟨1, Fact.out⟩, 0⟩, fun τ ↦ ?_
    simp [norm_iota_periodFactor τ, apply_ite, -mem_placeOfEmb] at h ⊢
    erw [ite_eq_left h.1, ← norm_mul, ← Complex.star_def, ← map_star_complex,
      ← map_mul (weightEmbedding ..)]
    convert! (norm_ringOfIntegers_le (weightEmbedding ιₚ τ) (-t * V l)).eq_of_not_lt fun g ↦ by
      grind [FinPlace.natCast_mem_iff_dvd, natCast_mem_placeOfEmb, mem_of_dvd _ (hV l) (by
    convert sub_mem (mul_mem_right ((1 - z + P.c₀InE s * z) * V l) _ h.1) (by simpa); grind)]
    simpa [field] using mod_cast by grind
  obtain ⟨⟨g, _⟩, w, _⟩ := (sub_one_dvd_pow_sub_one (a l) i).sub (sub_one_dvd_pow_sub_one _ k),
    sub_dvd_pow_sub_pow (P.c₀InE s) (n * -z) N
  have I y : ↑N ∣ y * t * (M l * (a l - 1)) → v.valuation _ (y * u ⟨l, j, k, i⟩) ≤ 1
    | ⟨c,
      _⟩ => by convert v.valuation_le_one (P.zetaInt s ^ j.1 * (y * 0 ^ k.1 * a l ^ i.1 + c * g))
               simpa [field, -coe_zetaInt] using mod_cast by grobner
  by_cases g : P.c₀InE s ∈ v.1 <;> [convert I (relDifferentGen ..) ⟨t * V l, by grind⟩; convert I
    (P.c₀InE s ^ N) (.mul_right ⟨n * e * w + f * (-z) ^ N * t, by grind [mul_pow, congr((t + $he,
    t + $hf))]⟩ _)] <;> simp [finiteImage, WeilData.α, α, g, v.valuation_eq_one_iff_notMem.2]
end
section
open Finset CMLattice Complex ComplexConjugate Fintype MeasureTheory MvPowerSeries NormedSpace
  NumberField Space WeilData
lemma Space.taylor_line_eq_subst_jetSeries {E n} [Field E] [CMType E] [WeilData E] [Fintype n] {V :
  Space E n 1} {f} (hf : f ∈ V.finitePart) a v : taylorAtZero (entireTheta f <| a • · • v) =
  (V.jetSeries a f).subst (linearSeries fun _ ↦ v ·) := by
  ext k
  let L := a • ∑ p, innerSLFlip ℂ (v p) ∘SL .proj p
  rcases (hasFPowerSeriesAt_iff (p := .ofScalars ℂ _) (z₀ := 0).2
    (.of_forall fun t ↦ by simpa [mul_pow, mul_assoc, div_eq_inv_mul, mul_left_comm] using
    hasSum_integral_of_dominated_convergence (μ := realMeasure _) _ (by fun_prop [realVac]) (fun _ ↦
    .of_forall (by simp; grw [L.le_opNorm ·, norm_apply_le])) (by simp [Summable.mul_right,
    expSeries_div_summable]) (by simpa [tsum_mul_right, exp_eq_tsum_div, Real.exp_eq_exp_ℝ,
    mul_assoc] using (integrable_exp_mul_realVac (_ * _)).mul_const _) (.of_forall fun w ↦
    .mul_right
    (realVac w * f (realVec w)) (expSeries_div_hasSum_exp (t * L w))))).choose_spec.factorial_smul 1
    k, (jet_subst_linearSeries (.replicateCol _ v) (.X () ^ k) (V.jetSeries a f)).symm
  simp_all [entireTheta_eq_integral, L, mul_sum, linSubst, MvPolynomial.X_pow_eq_monomial, ↓map_pow,
    mul_assoc, ↓theta_integrated,
    holCoord_eq, iteratedDeriv, mul_left_comm, exp_eq_exp_ℂ, linearSeries]
variable {P s} {E : Type} {n} [Fintype n] {ε} (V : Space (Parameters.E P s) n ε) [i : V.IsStd]
lemma Space.eq_zero_of_jetSeries_eq_zero [Field E] [CMType E] [WeilData E] {V : Space E n 1} {f}
  (hf : f ∈ V.finitePart) {a} (ha : a ≠ 0) (h : V.jetSeries a f = 0) : f = 0 := eq_zero_of_realVec
  fun y ↦ by simpa [entireTheta, realVac, *] using congr($(eq_of_taylorAtZero_eq (g := 0) (by
  fun_prop (disch := aesop)) (by simp) ((taylor_line_eq_subst_jetSeries hf a y).trans
  (h ▸ (subst_coe 0).trans (by aesop)))) a⁻¹)
lemma Space.jetSeries_eq_prod [Field E] [CMType E] [WeilData E] {V : Space E n 1} {f} (hf :
  f ∈ V.finitePart) {I} [Fintype I] {G : I → _} {μ : ℂ → I → _} (hG : ∀ i, Differentiable ℂ (G i))
  (h : ∀ c z, entireTheta f (c • z) = ∏ i, G i (μ c i ⬝ᵥ z)) : V.θ f = ∏ i, G i 0 ∧ ∀ c,
  V.jetSeries c f = ∏ i, (taylorAtZero (G i)).subst (linearSeries (μ c i)) :=
  ⟨by simpa [entireTheta, realVac] using h 0 0, fun c ↦ by
  ext α
  have H {v S} (f := fun _ ↦ ()) : (truncFinset ℂ _ S).eval v = (rename f (rescale v S)).coeff
    (α.mapDomain f)
  simp [truncFinset, coeff_rename, MvPolynomial.eval_monomial]; ac_rfl
  rw [← coeff_truncFinset_of_mem, MvPolynomial.funext fun v ↦ (H.trans ?_).trans H.symm,
    coeff_truncFinset_of_mem] <;> simp
  have := (taylor_line_eq_subst_jetSeries hf c v).symm
  simp_all [← coe_substAlgHom, PowerSeries.subst, substAlgHom_comp_substAlgHom_apply, mul_comm _
    (_ ⬝ᵥ v), linearSeries, -substAlgHom_apply, substAlgHom_X, rename_eq_subst, rescale_eq_subst]
  congr; induction @univ I _ using cons_induction <;> simp (disch := fun_prop) [*, ↓prod_cons,
    smul_smul, ← sum_smul, PowerSeries.rescale_eq_subst]
  tauto⟩
attribute [local simp] Parameters.areaScale WeilData.j dotProduct funext_iff mul_assoc
  thetaShift_prod
lemma Parameters.latticeModule_cmCurve : P.cmCurve.latticeModule =
  QuadField.scaledIdeal _ (P.Ω₀, 1) := by grind [Ω₀, cmCurve]
lemma Parameters.omega₀_mem_cmCurve_lattice : ↑P.Ω₀ ∈ P.cmCurve.Λ :=
  (latticeModule_cmCurve ▸ QuadField.mem_scaledIdeal).2 (by simp)
@[simp] lemma Parameters.norm_map_psi₀ {F R} [NormedField R] [FunLike F ℂ R] [MonoidHomClass F ℂ R]
  (ι : F) z : ‖ι (stdLattice.psi₀ (P.E s) z)‖ = 1 :=
  ((ι : _ →* R).isOfFinOrder (isOfFinOrder_ψf _)).norm_eq_one
lemma Parameters.exists_finitePart_of_isTightFrame {M N : ℕ} {I} [Fintype I] {w m} (δ : 𝓞 P.K) (h0 :
  N ≠ 0) (hN : δ * conj (δ : ℂ) = N) (hw : IsTightFrame w m M) (x : I × n → _) (hx : ∀ i,
  CMLattice.monomialDeg (x i) = m i.1) ⦃C : CMLattice P.d⦄ ⦃a⦄
  (ha : a ∈ C.Λ) (hA : C.area = ‖a‖ ^ 2 / N * M * √P.d / 2) : ∃ F ∈ V.finitePart,
  (∀ γ, let G i := C.twistedTranslate (m i.1) (a / conj ↑δ * -∑ τ,
    Φ τ (γ i.2) * conj (Φ τ (w i.1))) (C.monomialSection (x i))
  V.θ (V.ϱ (finVec (finiteImage γ)) F) = ∏ i, G i 0 ∧ ∀ c, V.jetSeries c (V.ϱ (finVec (finiteImage
    γ)) F) = ∏ i, (taylorAtZero (G i)).subst (linearSeries fun y ↦ if y.2 = i.2 then a / conj ↑δ /
    P.areaScale * c * conj (Φ y.1 (w i.1)) else 0)) ∧ (∀ p [Fact p.Prime] [PadicPlace p] x, ‖ιₚ
  (F (finVec x))‖ ≤ 1) ∧ Nonempty (V.VacuumExpansion (algebraMap P.K _ δ) N F) := by
  generalize e : a / _ = b
  obtain ⟨⟨⟩, ⟨⟩⟩ := (div_eq_iff (by grind [Nat.cast_ne_zero])).1 e, i.1
  exact have hl i {y} h := mul_comm _ (b * _) ▸ C.5 (herm_mem_quadInt y h (hw.1 i)) ha
    let A (i : I × n) : _ →L[ℂ] ℂ := ∑ τ, (b / P.areaScale * conj (Φ τ (w i.1))) • .proj (τ, i.2)
    have B u v : (∑ i, (m i.1 • C.hermitianForm).pullForm (A i)) u v = star u ⬝ᵥ v := by
      have := by simpa [*] using (area_pos C.1).ne'
      convert congr(∑ k, ∑ σ, ∑ τ, conj (u (τ, k)) * v (σ, k) / M * $(hw.2 τ σ)) <;>
        simp [A, *, mul_pow, ← mul_conj', mul_sum, sum_prod_type_right, @sum_comm I]
      congr! 4
      simp [← ofReal_pow √_, field, Real.pi_nonneg, *]
    have R γ i : A i (realImage γ) = b * ∑ τ, Φ τ (γ i.2) * conj (Φ τ (w i.1)) := by
      simp [A, mul_sum, realImage, realCoord, val_scaleIdele_fst, Real.sqrt_div_self]
      have := NeZero.ne P.d; congr; simp [field, *]
    (V.exists_entireTheta_eq (b := conj (quadGen P.d) • 1) (S := ∏ i, C.monomialSection (x i) ∘ A i)
      (by simp [traceOne, quadGen, map_ofNat]) B (by exact coe_mem_Ô (algebraMap _ _ δ)) h0 ((Φ
      1).injective (by simpa)) (by rw [prod_fn]; fun_prop) fun γ hγ ↦ by simp [R, normalizedShift,
      riemannForm_pullForm, ← mul_sum, canonicalMultiplier, multiplier_eq_canonicalMultiplier,
      by simpa using (hl · <| hγ ·), ← Complex.exp_sum, hx _ ▸ thetaShift_of_mem
      (monomialSection_mem ..), ← Complex.exp_nsmul, mul_left_comm (m _ : ℂ)]).imp fun F ⟨hF, _,
      D⟩ ↦ (fun H ↦ ⟨hF, H, fun _ _ _ x ↦ (exists_finiteImage_approx hF x).elim fun γ e ↦
      (exists_forall_mul_mem_Ô (finiteImage γ)).elim fun M h ↦ by
    grw [← θ_ϱ, ← e.2, (H γ).1, map_prod, norm_prod, Finset.prod_le_one₀ (by simp) fun i _ ↦ ?_]
    grw [← hx, ← mul_zero 0, C.norm_translate_le_naiveHeight_pow (N := 0) _ _ (N * M) _ _
      (C.norm_monomialSection_le _)] <;> simp [*]
    simpa [← hN, mul_left_comm b, ← mul_sum] using! C.latticeModule.smul_mem δ (@hl _ (M * _) (by
      simpa [finiteImage, mul_left_comm] using h.2 _)), D⟩) fun γ ↦
      jetSeries_eq_prod (rho_finVec_mem_finitePart _ hF) (by fun_prop) (by
      simp [entireTheta_translate_finiteImage _ V B, *]; simp [A, sum_prod_type, mul_sum]; grind)
end
section
namespace Parameters
open Real NeZero Space CMLattice Finset Submodule MvPowerSeries Fintype Set Notation
lemma bigOmega_pos {P s} : 0 < bigOmega P s := by simp [bigOmega, rootDiscr_pos, pi_pos, exp_pos]
@[simp] lemma jetScale_ne_zero {P s} :
  jetScale P s ≠ 0 := by simpa [jetScale, periodFactor, ne_of_gt, rootDiscr_pos, ne] using
  (congr($(P.norm_gal_vacuumRoot s 1) / $(P.cmCurve.chowla_selberg.choose_spec.2 1) ≠ 0)).mpr
lemma exists_isJetConjugate_generator P : ∃ C : ℕ, ∀ s, ∃ B : _ → 𝔸f (P.E s), ∀ {n} [Fintype n] {ε}
  (V : Space _ n ε) [V.IsStd], (∃ c ≠ 0, (∀ p [Fact p.Prime] [PadicPlace p] x, ‖ιₚ (c * V.vacElem
  (finVec x))‖ ≤ 1) ∧ ∀ (σ : Gal(ℂ/K P)) x, ‖σ (c * V.vacElem (finVec x))‖ ≤ rexp (C * P.N₁ s ^ 2) ^
  card n) ∧ ∃ F ∈ V.finitePart, V.θ F = 1 ∧ V.finitePart ≤ span ℂ (.range fun x ↦ V.ϱ (finVec x)
  F) ∧ ∀ σ : Gal(ℂ/K P), ∃ t, ∃ F' ∈ V.finitePart, ‖t‖ ^ 2 = (P.bigOmega s)⁻¹ ∧ ∀ x, IsJetConjugate
  σ (placePerm s σ) (P.jetScale s) t (V.ϱ (finVec x) F) (V.ϱ (finVec (B σ • x)) F') := by
  choose Ω hA e he β a hb H using (complex_multiplication_theta _ · latticeModule_cmCurve)
  refine (isAlgebraic_of_padic fun _ ↦ @norm_a₁_le_one _ _ P.cmCurve _ _ ⟨_⟩).elim fun p hp ↦
    (isCompact_iUnion fun x : p.rootSet ℂ ↓∩ .range (@a₁ P.d) ↦
    IsAppellHumbert.isCompact_range_norm_thetaShift (x.2.choose.monomialSection_mem
    (1, 0))).bddAbove.imp' (⌈·⌉₊ + 4) fun M hm s ↦ ⟨finAdeleIncl .. ∘ β, fun V _ ↦ ?_⟩
  let N := P.N₁ s
  have fr (e : ℕ+) := exists_finitePart_of_isTightFrame V (N * e) (ne ((N * e) ^ 2)) (by simp [sq])
    (P.isTightFrame_zeta_pow s N).repeat_vectors (fun _ ↦ (1, 0)) (by simp)
  obtain ⟨F, W, hF, hI, K, x, m, -, hJ, hs⟩ := fr 1 omega₀_mem_cmCurve_lattice
    (by simp [QuadField.area_eq_of_eq_scaledIdeal latticeModule_cmCurve, field, N, ne])
  have h1 := by simpa [monomialSection] using (hF 0).1
  obtain ⟨j, hj⟩ := by simpa [h1] using
    (congr(V.dataInner V.vacElem $(hs V.θ)).symm.trans (map_sum ..)).trans ∘ sum_eq_zero
  have hc := (hs ((m⁻¹ : ℂ) • V.dataInner V.vacElem ∘L V.ϱ (finVec (-x j)))).symm
  set c : ℂ := _ * _
  simp [hj, ↓rho_finVec, congr($(V.heisRep_right_rho _) _) ▸ (V.dataInner_rho_of_vacElem _).trans
    ((adelicSum ..).vac_equiv _), realVac, stdLattice.finVac, ← sum_filter] at hc
  refine have c0 := by simp [c, hj]
    (forall_and.1 fun σ ↦ ?_).imp (⟨c, c0, ?_, ·⟩) (⟨F, W, h1, ?_, ·⟩)
  refine (fr (e σ) (he σ) (by simp [hA, field, N, ne])).elim fun _ ⟨W', h', _⟩ ↦ (fun J ↦ ⟨fun _ ↦
    ?_, σ (P.periodFactor s) / Ω σ * P.areaScale, _, W', ?_,
    J⟩) (denseRange_finiteImage.induction_on · ⟨(isLocallyConstant_rho_finVec
    W).comp₂ ((isLocallyConstant_rho_finVec W').comp_continuous (by fun_prop)) (IsJetConjugate _ _ _
    _) Not⟩ fun γ ↦ ?_)
  any_goals simp_rw [← V.smul_apply, hc, ← θ_ϱ, map_sum]
  · grw [norm_sum_le, sum_le_card_nsmul _ _ (M.exp ^ _), card_le_univ, hJ]; swap
    simp_intro .. [↓rho_finVec, by simpa [rho_finVec_mem_finitePart, W, W'] using
      (congrArg constantCoeff <| J ·)]
    rw [← θ_ϱ, ← (exists_finiteImage_approx W' _).choose_spec.2, (h' _).1, norm_prod,
      ← prod_const]; gcongr
    grw [← add_one_le_exp, ← hm
      ⟨_, ⟨⟨σ • ⟨_, p.mem_rootSet.2 hp⟩, exists_galConjugate ..⟩, rfl⟩, _, rfl⟩]; bound
    simp; grw [le_exp_log N, log_le_self, Nat.le_ceil M, ← numInfPlaces, card_infinitePlace_E,
      Nat.totient_le] <;> simp [← exp_add, ← exp_nat_mul]; clear * -; grind
  convert congr($(P.norm_gal_vacuumRoot s σ) * π / $(P.cmCurve.chowla_selberg.choose_spec.2
    σ)) <;> clear * - hA <;> simp [hA, periodFactor, areaScale, bigOmega, div_pow, mul_pow,
    pi_nonneg] <;> field [ne]
  let t i j := -Algebra.trace P.K _ (γ i * star (P.ζ s ^ @Fin.val N j)) / N
  choose T g h₂ using ((hb σ).frequently ((by fun_prop :
    ContinuousAt (finAdeleIncl _ (P.E s) · • finiteImage γ) _).eventually
    ((isLocallyConstant_rho_finVec W').eventually_eq _))).forall_exists_of_atTop (image₂ t ⊤ ⊤)
  erw [← h₂, adeleMap_algebraMap, algebraMap_smul, ← map_smul]
  simp [IsJetConjugate, hF, ↓h', map_subst, PowerSeries.subst, rename_eq_subst,
    subst_comp_subst_apply]
  congr! 3 with i
  · simp [← rename_eq_subst, linearSeries, ↓smul_eq_C_mul]
    apply Fintype.sum_equiv ((placePerm s σ).prodCongr 1); rintro ⟨⟩
    simp [jetScale, starRingEnd_apply, ← map_star_complex, placePerm_spec, apply_ite σ,
      ← smul_eq_C_mul]; field_simp
  convert! H σ T (t i.2 i.1.1) (g (by simp)) using 2 <;>
    simp [t, monomialSection, coe_trace_eq_sum, -star_ζ, mul_assoc, ← mul_sum] <;> field_simp
  iterate 2 simp [IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg, ↓rho_finVec, *, finitePart,
    span_le,
    (eq_inv_smul_iff₀ c0).2 hc, finHeisOp, smul_sum, smul_smul, sum_smul_mem, mem_span_of_mem]
end Parameters
end
section
noncomputable section
open Set NumberField Real
def Parameters.c P := (exists_isJetConjugate_generator P).choose + (2 * P.d + 6) +
  (P.N₀ + |chowlaSelbergConst P.d| + ∑ w ∈ primitiveRoots
  P.N₀ ℂ, |‖(Polynomial.cyclotomic P.N₀ ℂ).derivative.eval w‖.log|)
structure Data (P : Parameters) where
  (logX logB logX₁ : ℝ) (s m r : ℕ) s_le : s ≤ 32 * logX
  thick : Finset _
  g : Fin 2 → ℕ
  piG : 𝓞 P.K
  scale : 1e12 * P.c ≤ log logB ∧ 100 * log logB ≤ logX ∧ 1e6 * logX ≤ logX₁ ∧ 1e6 * logX₁ ≤ logB ∧
    6 * log logX₁ ≤ log logB
  m_mem : ↑m ∈ Icc (exp (logX / 2)) (2 * exp (logX / 2))
  r_mem : ↑r ∈ Icc (exp (5 * logX)) (3 * exp (5 * logX))
  m_pow : ∃ e, m = 2 ^ (e + 1) ∧ s = (e + 1) * 22
  r_pow : ∃ e, r = 3 ^ (e + 1)
  thick_eq_neg_one_mod {m} (d : m ∣ P.N₁ s) : m ∣ P.N₀ * 3 ^ (.log 3 s + 5) → ∀ σ ∈ thick, P.placeClass d σ = -1
  three_term : let φ := P.placeClass P.two_pow_dvd_N₁; ∀ i j, 0 < i → i < j → j ≤ 324 * s →
         ∀ σ ∈ thick, ∀ τ ∈ thick, ∀ ρ ∈ thick, φ (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1
  g_prime i : (g i).Prime
  g_modEq_one i : g i ≡ 1 [MOD P.N₁ s * P.d]
  dvd_g_sub_one i : P.Mω s ^ 2 ∣ g i - 1
  g_injective : g.Injective
  g_mem i : ↑(g i) ∈ Icc (exp logB ^ 10) (exp logB ^ 11)
  norm_piG : piG * star piG = g 0 * g 1
  exists_prime_window : ∀ U ∈ Icc (100 * logB) (2 ^ s), ∃ p, p.Prime ∧ p ≡ 1 [MOD P.Mω s ^ 2] ∧
    log p ∈ Icc U (U + √logB)
namespace Data
variable {P} (D : Data P) (y : ℝ) (j)
abbrev x := D.logX.exp
abbrev x₁ := D.logX₁.exp
abbrev b := D.logB.exp
@[reducible] def E := P.E D.s deriving NumberField, CharZero, IsCMField
protected abbrev Φ := InfinitePlace D.E
abbrev N₁ := P.N₁ D.s
abbrev f := numInfPlaces D.E
protected abbrev cycloConductor := D.N₁ * P.d
abbrev rootDisc := rootDiscr D.E
def k := D.r + 1 - D.m
def t := 5 * D.r
def roundUp := D.N₁ * ⌈y / D.N₁⌉₊
def h₂ := D.r ^ 8
def h := 2 * D.h₂
def reducedHalfGap := D.h₂ - (D.t + 1) / 2
def a := D.roundUp (D.x * D.b)
def b₁ := D.roundUp (D.a / D.x)
def b₂ := D.roundUp (D.a / D.x₁)
abbrev placeOfInt : D.Φ := P.placeOfInt _ j
def n := D.k + j * (D.t + 1)
abbrev posRank := D.k + j - 1
instance : Fact (D.g j).Prime := ⟨g_prime ..⟩
def gProd := D.g 0 * D.g 1 deriving NeZero
def tops : Finset D.Φ := {τ | P.placeClass (P.N₀.dvd_mul_right _) τ = 1}
def w (σ : D.Φ) := ite (σ ∈ D.thick) D.b₁ D.b₂ + j * D.h + D.h₂
def nominalWeight (σ : D.Φ) := D.a / ite (σ ∈ D.thick) D.x D.x₁
def primeSum σ := ∑ ν ∈ .Icc 1 D.a,
  lambdaClass P.d 1 ν * (y / ν - D.nominalWeight (D.placeOfInt (-ν) * σ))⁺
abbrev budget := D.f * D.a * D.logB ^ 3
def jetSize := log (Nat.factorial j) - j * (P.bigOmega D.s / D.gProd).log
def dirCost := ∑ σ, (D.jetSize (D.w 0 σ) - D.primeSum (D.nominalWeight σ) σ)
end Data
end
end
section
noncomputable section
open Real Set Finset Nat NeZero
namespace Data
variable {P} (D : Data P) {F G l l' c : ℝ} {A B : ℕ} {u}
class HasLogBound (D : Data P) (u : Bool) F (l :
  outParam ℝ) where out : ite u (|F| ≤ exp l) (exp l ≤ F)
lemma c_ge : 64 ≤ P.c ∧ P.N₀ ≤ P.c ∧ P.d ≤ P.c ∧ φ P.N₀ ≤ P.c := by
  grw [totient_le]; grind [Parameters.c, sum_nonneg, ofNat_lt_cast, P.lt_d]
attribute [local grind!] HasLogBound NeZero exp_pos exp_log exp_zero add_one_le_exp inv_anti₀
  one_le_cast ceil_lt_add_one le_ceil ceil_eq_zero s_le log_mul
lemma r_odd : Odd D.r := by grind [D.r_pow]
lemma m_even : Even D.m := by grind [D.m_pow]
attribute [grind! .] c_ge r_odd m_even
lemma placeClass_of_thick : ∀ σ ∈ D.thick, P.placeClass ⟨_, rfl⟩ σ = -1 :=
  D.thick_eq_neg_one_mod _ ⟨_, rfl⟩
abbrev HasLogUpper := D.HasLogBound true
abbrev HasLogLower := D.HasLogBound false
lemma HasLogBound.pos [D.HasLogLower F l] : 0 < F := by grind
section
variable {D} [HasLogBound D u F l] [HasLogBound D u G l']
lemma HasLogBound.of_mem_Icc {l} (G H := F) [D.HasLogLower G l] [D.HasLogUpper H l'] (e :
  F ∈ Icc G H := by simp) (a : ite u (l' ≤ c)
  (c ≤ l) := by cases u <;> grind [D.scale]) : HasLogBound D u F c := by grind [=_ exp_le_exp]
instance (priority := low) hasLogBound_natCast [NeZero A] :
  HasLogBound D u A (ite u A 0) := by grind
instance (priority := low) [A.AtLeastTwo] : HasLogBound D u ofNat(A) (ite u ofNat(A) 0) :=
  hasLogBound_natCast
instance : HasLogBound D u 1 0 := by grind
instance : HasLogBound D u c.exp c := by grind
instance hasLogBound_mul : HasLogBound D u (F * G) (l + l') := by grind [exp_add, mul_le_mul]
instance hasLogBound_add : HasLogBound D u (F + G) (max l l' + ite u 1 0) := ⟨by
  split; grw [exp_add, ← exp_one_gt_two, exp_monotone.map_max]; repeat grind⟩
instance [D.HasLogLower F l] : D.HasLogUpper F⁻¹ (-l) := by grind [exp_neg]
instance [D.HasLogUpper F l] [D.HasLogLower F l'] : D.HasLogLower F⁻¹ (-l) := by grind [exp_neg]
instance [HasLogBound D u G⁻¹ l'] : HasLogBound D u (F / G) (l + l') := hasLogBound_mul
instance : HasLogBound D u (F ^ A) (A * l) := by grind [exp_nat_mul, pow_le_pow_left₀]
instance : HasLogBound D u √F (l / 2) := by grind [exp_half, abs_le_sqrt, Real.le_sqrt]
instance [HasLogBound D u (A * B) l] : HasLogBound D u ↑(A * B) l := by simpa
instance [HasLogBound D u (A + B) l] : HasLogBound D u ↑(A + B) l := by simpa
instance [HasLogBound D u (A ^ B) l] : HasLogBound D u ↑(A ^ B) l := by simpa
instance [D.HasLogUpper (|F| + 1) c] : HasLogBound D u ⌈F⌉₊ (ite u c l) := by grind
instance : HasLogBound D u D.logB D.logB.log := by grind [D.scale]
instance : HasLogBound D u D.logX₁ D.logX₁.log := by grind [D.scale]
instance : D.HasLogUpper D.s D.logX₁.log := by grind [D.scale]
variable [D.HasLogUpper F l]
lemma hasLogUpper_of_abs_le : |G| ≤ F → D.HasLogUpper G l := by grind
lemma hasLogUpper_of_le_of_nonneg (e : G ≤ F) (h : 0 ≤ G := by positivity) :
  D.HasLogUpper G l := by grind
instance : D.HasLogUpper |F| l := by grind
instance [D.HasLogUpper G l'] : D.HasLogUpper (F - G) (max l l' + 1) :=
  hasLogUpper_of_abs_le (abs_sub ..)
instance (priority := low) [D.HasLogLower F l'] :
  D.HasLogUpper F.log (max (99 + D.logB.log) (max l (-l') - 99 *
  D.logB) + 1) := hasLogUpper_of_abs_le (F := 99 * D.logB + exp _) (by grind [exp_le_exp])
variable (D) [D.HasLogUpper A l] [D.HasLogLower G l'] [D.HasLogLower B l']
  (e : l < l' := by clear_aux_decl; clear * - D; (repeat clear ‹_›); grind (splits := 99) [D.scale])
lemma hasLogUpper_of_le : B ≤ A → D.HasLogUpper B l := by grind [cast_le]
lemma hasLogLower_of_le : G ≤ F → D.HasLogLower F l' := by grind
include D e
protected lemma lt_of_hasLogBound : F < G := by grind [=_ exp_lt_exp]
protected lemma le_of_hasLogBound : F ≤ G := (D.lt_of_hasLogBound e).le
lemma nat_lt_of_hasLogBound : A < B := cast_lt.1 (D.lt_of_hasLogBound e)
lemma nat_le_of_hasLogBound : A ≤ B := (D.nat_lt_of_hasLogBound e).le
end
instance : HasLogBound D u π (ite u 4 0) := by grind [two_le_pi, pi_le_four]
instance : HasLogBound D u D.m (D.logX / 2 + ite u 2 0) := .of_mem_Icc _ _ D.m_mem
instance : HasLogBound D u D.r (5 * D.logX + ite u 3 0) := .of_mem_Icc _ _ D.r_mem
instance : D.HasLogUpper P.c D.logB.log := by grind [scale]
lemma le_m : 10000 ≤ D.m := D.nat_le_of_hasLogBound
@[grind! .] lemma r_add : D.r + 1 = D.k + D.m := (Nat.sub_add_cancel D.nat_le_of_hasLogBound).symm
lemma k_le_r : D.k ≤ D.r := by grind [le_m]
instance : HasLogBound D u D.k (5 * D.logX + ite u 3 (-2)) := .of_mem_Icc (D.r / 2) D.r
  (by grind [le_m, k, cast_sub, (D.le_of_hasLogBound : D.m ≤ (D.r / 2 : ℝ))])
instance : HasLogBound D u D.t (5 * D.logX + ite u 8 0) := t.eq_1 D ▸ .of_mem_Icc
instance [HasLogBound D u (D.m ^ 22) l] :
  HasLogBound D u (ofNat(2) ^ D.s) l := by cases D.m_pow; simp_all [pow_mul]
instance : HasLogBound D u (towerDeg D.s) (11 * D.logX + ite u (D.logB.log / 5) 0) := by
  have := D.hasLogUpper_of_le (pow_log_le_add_one 3 D.s); rw [towerDeg, pow_add]; exact .of_mem_Icc
instance hasLogBound_f : HasLogBound D u D.f (11 * D.logX + ite u (D.logB.log / 5 + P.c) 0) :=
  f.eq_1 D ▸ P.card_infinitePlace_E _ ▸ .of_mem_Icc
instance {S : Finset D.Φ} [D.HasLogUpper D.f l] : D.HasLogUpper #S l :=
  D.hasLogUpper_of_le (card_le_univ _)
instance : HasLogBound D u (D.n D.m) (5.5 * D.logX + ite u 12 0) := n.eq_1 .. ▸ .of_mem_Icc
instance (i) : HasLogBound D u (D.g i) (ite u 11 10 * D.logB) := .of_mem_Icc _ _ (g_mem ..)
instance : HasLogBound D u D.gProd (ite u 22 20 * D.logB) := gProd.eq_1 D ▸ .of_mem_Icc
lemma roundUp_mem_Icc [D.HasLogLower F l] : ↑(D.roundUp F) ∈ Icc F (F + D.N₁) := by
  simp [roundUp]; grw [ceil_lt_add_one (HasLogBound.pos D).le, ← le_ceil]
  simp [mul_add, mul_div_cancel₀, ne]
instance : HasLogBound D u D.h₂ (40 * D.logX + ite u 25 0) := h₂.eq_1 D ▸ .of_mem_Icc
instance : HasLogBound D u D.h (40 * D.logX + ite u 27 0) := h.eq_1 D ▸ .of_mem_Icc
instance : HasLogBound D u D.a (D.logB + D.logX + ite u 1 0) := .of_mem_Icc _ _ D.roundUp_mem_Icc
instance : HasLogBound D u D.b₁ (D.logB + ite u 2 (-2)) := .of_mem_Icc _ _ D.roundUp_mem_Icc
instance : HasLogBound D u D.b₂ (D.logB - D.logX₁ + D.logX + ite u 2 0) :=
  .of_mem_Icc _ _ D.roundUp_mem_Icc
instance {κ S} {v : κ → ℝ} [D.HasLogUpper #S l] [g : ∀ y, D.HasLogUpper (v y) l'] :
  D.HasLogUpper (∑ y ∈ S, v y) (l + l') :=
  hasLogUpper_of_abs_le (by simpa using norm_sum_le_of_le S (f := v) fun y _ ↦ (g y).1)
instance [D.HasLogUpper (|log F| + |log G|) l] : D.HasLogUpper (F * G).log l := by grind
instance [D.HasLogUpper (A * log F) l] : D.HasLogUpper (F ^ A).log l := by simpa
instance [D.HasLogUpper (A * .log A) l] : D.HasLogUpper (log A !) l :=
  hasLogUpper_of_le_of_nonneg (by grw [factorial_le_pow, cast_pow])
lemma hundred_mul_m_le_k : 100 * D.m ≤ D.k := D.nat_le_of_hasLogBound
@[simp] lemma k_pos : 0 < D.k := D.nat_le_of_hasLogBound
lemma n_mono : Monotone D.n := mul_left_mono.const_add _
lemma k_even : Even D.k := by grind
attribute [grind] t h w
lemma t_odd : Odd D.t := by grind
lemma r_add_six_le_t : D.r + 6 ≤ D.t := by grind [D.r_pow]
lemma k_add_t_add_one_le_h₂ : D.k + D.t + 1 ≤ D.h₂ := D.nat_le_of_hasLogBound
attribute [grind! .] k_add_t_add_one_le_h₂ k_pos hundred_mul_m_le_k k_even t_odd k_le_r
  r_add_six_le_t
end Data
end
end
open Real Set
namespace Data
variable {P} (D : Data P) {j : ℕ} (hj : j ≤ 2 * D.m) (σ : D.Φ)
attribute [local simp] w nominalWeight b₁ b₂
lemma nominalWeight_mem_Icc :
  D.nominalWeight σ ∈ Icc (D.a / D.x₁) (D.a / D.x) := by
  simp [mem_Icc]; split <;> simp_all <;> use D.le_of_hasLogBound
instance {u} : D.HasLogBound u (D.nominalWeight σ) (D.logB + ite u 1 (-D.logX₁)) :=
  .of_mem_Icc _ _ (nominalWeight_mem_Icc ..)
@[simp, bound] lemma nominalWeight_nonneg : 0 ≤ D.nominalWeight σ := (HasLogBound.pos D).le
lemma nominalWeight_add_le : D.nominalWeight σ + D.x ^ 42 ≤ 2 * D.b := by
  grw [(nominalWeight_mem_Icc ..).2, a, D.roundUp_mem_Icc.2, two_mul, add_div,
    add_assoc]; simpa using D.le_of_hasLogBound
lemma nominalWeight_le_w_sub j σ : D.nominalWeight σ ≤
  D.w j σ - D.h₂ := by simp; split <;> grw [← D.roundUp_mem_Icc.1] <;> bound
include hj
lemma w_le_nominalWeight_add : D.w j σ ≤ D.nominalWeight σ + D.x ^ 42 := by
  simp; split <;> grw [hj, D.roundUp_mem_Icc.2] <;> simpa [add_assoc] using D.le_of_hasLogBound
lemma w_le_two_mul_b :
  D.w j σ ≤ 2 * D.b := by grw [w_le_nominalWeight_add _ hj, nominalWeight_add_le]
instance : D.HasLogUpper (D.w 0 σ) (2 + D.logB) :=
  hasLogUpper_of_le_of_nonneg (D.w_le_two_mul_b bot_le _)
instance {l} [D.HasLogLower (D.nominalWeight σ) l] :
  D.HasLogLower (D.w j σ) l := by grind [HasLogBound, D.nominalWeight_le_w_sub j σ]
lemma log_w_le : log (D.w j σ) ≤ log (D.nominalWeight σ) + D.x⁻¹ := by
  grw [log_le_iff_le_exp, w_le_nominalWeight_add _ hj, exp_add, exp_log, ← add_one_le_exp, mul_add,
    add_comm] <;> simp [HasLogBound.pos D, -nominalWeight, -w]
  exact D.le_of_hasLogBound
