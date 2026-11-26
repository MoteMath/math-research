import Lib.Weil.Construction.FiniteMultiplier
import Lib.Adelic.Unitary.SpaceBasic
import Lib.Weil.MixedModel.AdelicSum
noncomputable section
open Set Function MeasureTheory NumberField Submodule Complex ComplexOrder Gf Heisenberg.IsVacuum
variable {E ι : Type*} [Field E] [CMType E] [WeilData E] [Fintype ι]
def stdLattice.finProjAction : Σ c,
  (finHeis E ι).MultiplierAction (latticeMeasure ..) finVac (Gf E ι) c := ⟨_, by simp [finHeis,
  HSMul.hSMul, SMul.smul], fun g ↦ ⟨by fun_prop, (map_mulVec_haar_finAdele ..).trans (by
  obtain := congr(‖$(finMultiplier_inv g)‖), finMultiplier_ne_zero g; simp_all [finMultiplier,
    glMultiplier_inv, chiFin, chiAdelic, finIdeleAbs, Circle.norm_coe, abs_of_nonneg])⟩, _,
  (isLocallyConstant_of_eventually_mul ((isOpen_Kf.eventually_mem (by simp)).mono fun _ h g ↦ by
  simpa using! glMultiplier_mul_of_mem g (one_mem _) h)).continuous,
  finMultiplier_eq_one_of_mem (by simp), finMultiplier_inv, by tauto⟩
lemma stdLattice.exists_gauss_sum_finProjAction (g s : Gf E ι) : ∃ (Q : ModuleCat.{max u_1 u_2} (Ô
  E)) (_ : Fintype Q) (γ : Q → _), finProjAction.1 g s * finMultiplier s⁻¹ * finMultiplier (g * s) =
  (∑ q, stdLattice.psi₀ E (γ q)) * finMultiplier g ∧ ∀ (t : Ô E) q, stdLattice.psi₀ E
  (γ (t • q)) = stdLattice.psi₀ E (Star.star ↑t * t * γ q) ∧ (t.1 • s⁻¹.1.1 ∈ (Ô E).matrix → t • q = 0) := by
  let L := intVectors (Ô E) ι
  let M := L.comap (.coprod 1 1) ⊓ (L.comap (s.1.1 • .id)).prod (L.comap ((g * s).1 • .id))
  have := AddSubgroup.fintypeOfIndexNeZero (IsCompact.relIndex_ne_zero_add
    (K := M.toAddSubgroup) (H := (L.prod L).toAddSubgroup) ?k ?o)
  refine ⟨.of _ (M ⧸ submoduleOf _ M), this, _, by
    dsimp [finProjAction]; erw [integral_integral (((IsCompact.integrableOn ?k _ ((@continuous_psi₀
      E).comp _)).integrable_indicator ?m).congr ?r), ← integral_congr_ae ?r, integral_indicator ?m,
      setIntegral_eq_finsum ?k ?o ?p, inter_comm, inter_assoc, inter_eq_right.2 fun _ ↦ (·.2.rec
      add_mem), prod_inter_prod, measureReal_prod_prod, latticeMeasure_inter_eq_glMultiplier,
      latticeMeasure_inter_eq_glMultiplier]
    simp [↓← finMultiplier.eq_1, ↓finMultiplier_inv, ← Complex.mul_conj']
    field_simp [finMultiplier_ne_zero]; rfl
    rotate_right; filter_upwards with p
    simp only [uncurry, HSMul.hSMul, SMul.smul, finVac, indicator, star_mulVec_dot_mulVec,
      ← semichar.eq_1]
    simp [↓ite_mul, ← ite_and, semichar_add]; congr! with ⟨h⟩
    rw [mul_assoc, semichar_mul_self h, mul_one]
    exacts [fun ⟨_, e, a, b⟩ ⟨_, l, i, j⟩ ⟨m, n⟩ ↦ psi₀_congr 0 (mul_mem
      (star_mem_Ô traceOneAdele_mem) (add_mem (sub_mem (dot_mem m l) (star_mulVec_dot_mulVec s .. ▸
      dot_mem (sub_mem i a :) i)) (sub_mem (dot_mem e n) (star_mulVec_dot_mulVec (g * _) .. ▸
      dot_mem b (sub_mem j b :))))) (by simp; ring), by fun_prop,
      (?k).measurableSet], fun t q ↦ ⟨by exact (?p (t • q.out) (t • q).out ((Submodule.Quotient.eq'
    (submoduleOf (prod ..) M)).1 (by simp))).trans (by simp [Subring.smul_def]; ac_rfl),
    q.inductionOn fun x h ↦ (ker_mkQ _).ge ⟨?h, (add_mem_cancel_left ?h).1 (t • x).2.1⟩⟩⟩
  simpa using! IsIntMatrix.mulVec h x.2.2.1
  exacts [.inter_left (.prod (isCompact_stdLattice.preimage_smul s.1)
    (isCompact_stdLattice.preimage_smul (g * _).1)) (isCompact_stdLattice.isClosed.preimage
    continuous_add), isOpen_stdLattice.prod isOpen_stdLattice]
lemma stdLattice.finProjAction_cocycle_eq_one_of_mem ⦃s : Gf E ι⦄ (hs : s ∈ Kf E ι) g :
  finProjAction.1 g s = 1 := by
  choose M _ γ e h k using exists_gauss_sum_finProjAction g s
  apply mul_right_cancel₀ (finMultiplier_ne_zero g)
  simpa [↓finMultiplier_eq_one_of_mem, *, finMultiplier, ← glMultiplier_mul_of_mem g (one_mem _) hs,
    Fintype.sum_eq_single _ (absurd <| by
    simpa using k 1 · (by simpa using! hs.isIntMatrix_inv)), by simpa using h 0] using e
def finAction : (stdLattice.finHeis E ι).MultiplierAction (latticeMeasure ..) stdLattice.finVac
  (Gf E ι) := {stdLattice.finProjAction.2 with cocycle g s := (s.mem_of_Kf_le_of_supportedOn_le
  (H := cocycleRadical stdLattice.finProjAction.2 (stdLattice.finProjAction_cocycle_eq_one_of_mem (by simp)))
  stdLattice.finProjAction_cocycle_eq_one_of_mem fun w s hs ↦ by
  wlog! h : w.IsSplit → (s⁻¹.atPlace w).1 ∈ (LocInt w).matrix generalizing s
  exact (mul_mem_cancel_left (this _ (atSplit_mem_supportedOn h.1 _⁻¹)
    (by simp_all; exact ((saturatingElem s⁻¹.1).2.map_evalAt w).1))).1 (this _
    (mul_mem (by simp) hs) (by simpa [h] using! ((saturatingElem s⁻¹.1).2.map_evalAt _).2.1))
  intro g; obtain ⟨⟨M, _, γ, e, c⟩, N, a, _, R, hb, rfl, -⟩ :=
    stdLattice.exists_gauss_sum_finProjAction g s, congr((fun v ↦ √‖modelInner v v‖) ($(weilOp_triple
    stdLattice.finProjAction.2 g s) stdLattice.isVacuum_finVac.vacElem)).symm, g.exists_supportedOn_mul_trivialOn {w}
  have := @finMultiplier_ne_zero E ι
  simp [← (commute_supportedOn_trivialOn hs hb).right_comm, *, mul_mem, field,
    stdLattice.finProjAction_cocycle_eq_one_of_mem, -weilOp,
    stdLattice.isVacuum_finVac.2, show finMultiplier (_ * R) =
    finMultiplier _ * finMultiplier _ from glMultiplier_mul (atPlace_eq_one_or _ hb)] at e N
  let t := Subtype.mk _ (idem_mem_Ô (star {w})ᶜ)
  have k q := (c t q).2 (idem_mul_mem_Ô.2 fun u n ↦ (by
    clear c; by_cases u = w <;> aesop : (s⁻¹.atPlace u).1 ∈ (LocInt u).matrix) · ·)
  by_cases! hw : w.IsSplit
  apply N ▸ eq_coe_norm_of_nonneg
  simp [by simpa [sub_smul, k, (by ext1; simp [t, idem_apply]; grind : (1 - star t.1) *
    (1 - t) = 0)] using c (1 - t), finMultiplier_eq_of_supportedOn (S := {w}), mul_mem, *, chiFin,
    chiAdelic, field, by simpa [← eq_div_iff, finMultiplier_ne_zero] using e]; bound
  obtain ⟨⟨r, e', _⟩, i, _, _⟩ := StablyUnram.exists_sq_eq_q_of_inert hw, ‹WeilData E›.exists_i_c₀
  have d t (m : t ∈ supportedOn ι {w}) := by simpa [WeilData.υ_inert, hw, ← e',
    ← finMultiplier.eq_1] using (glMultiplier_eq_pow_of_local
    (mem_supportedOn.1 m · · (by grind [star_star])) ((saturatingElem _).2.map_evalAt _))
  apply eq_one_of_orbits (algebraMap _ (Ô E) i • ·) (stdLattice.psi₀ E ∘ γ) (-r) (by grind [Int.ModEq])
    (by simpa using c 0) (fun q ↦ ⟨isOfFinOrder_ψf _, ?_⟩) N (by
    simpa [*, IsSelfAdjoint, AddChar.map_neg_eq_inv, inv_eq_conj] using
      Weil.normNegOne (E := E).isUnit
      |>.smul_bijective.sum_comp (stdLattice.psi₀ E ∘ γ)) (by simpa [*, mul_mem, mul_assoc, ← pow_add] using e)
  simpa [*, ← map_mul, ← coe_star_ringOfIntegers, smul_smul, sub_smul] using (isUnit_Ô.2 fun u ↦ by
    by_cases u = w <;> norm_num [t, star_injective.eq_iff' hw, *]
    simpa [map_ofNat] using
      v_algebraMap_eq_one (u.2.notMem_of_isCoprime_of_mem (Odd.coprime_two_right (by
    grind)).cast u.1.absNorm_mem) : IsUnit (t - 1 - 1)).smul_eq_zero (x := q)) g}
open Matrix Measure U Heisenberg G WeilData ComplexConjugate IsVacuum
variable {E : Type*} [Field E] [CMType E] [WeilData E] {n : Type*}
  [Fintype n] {s : n → _} (g : G E s)
def weilMultiplier := (∏ w, realMultiplier (g.1 w)) * finMultiplier g.2
set_option synthInstance.maxSize 999
def vacuumMeasure :=
  ((realMeasure _).prod (latticeMeasure E n)).map (adelicSum E 1).equiv deriving IsAddHaarMeasure
instance isVacuum_vacuumFn : (adelicHeis E s).IsVacuum vacuumMeasure vacuumFn :=
  (adelicSum ..).isVacuum
section
variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n] {s : n → _}
  (g : G E s)
instance : DistribMulAction (G E s) (n → 𝔸 E) := .compHom _ toUnitary.toMonoidHom
@[simp] lemma smul_eq_mat_mulVec x : g • x = g.mat *ᵥ x := rfl
instance : ContinuousSMul (G E s) (n → 𝔸 E) := ⟨by simp; fun_prop⟩
end
@[simps Δ] def adelicAction : (adelicHeis E s).MultiplierAction vacuumMeasure vacuumFn (G E s) := by
  use ?_, fun g ↦ .of_semiconj ⟨by fun_prop, rfl⟩ (.prod ((realAction _).2 _) (finAction.2 _))
    (mat_mulVec_adelicSum g · |>.symm) (by fun_prop), weilMultiplier,
    .mul (by fun_prop [realMultiplier]) finAction.4.snd', ?_, ?_, fun g h ↦ (by
    simpa only [weilMultiplier, ← realMultiplier_blockU, ← map_mul, ← map_inv, smul_eq_mat_mulVec,
      ← map_add, OrthogonalSum.beta_equiv, realAction, (adelicSum E s).integral_eq_integral_prod,
      mat_mulVec_adelicSum, OrthogonalSum.vac_equiv, ← integral_prod_mul, mul_mul_mul_comm _ _
      (_ * _), mul_mul_mul_comm _ (realVac _), mul_mul_mul_comm _ (realMultiplier _)] using!
      Submonoid.mul_mem ⊥ ((realAction _).7 (blockU g.1) (blockU h.1)) (finAction.7 g.2 _)) <;>
    simp [adelicHeis, mat, ↓form_mulVec_mulVec, weilMultiplier, realMultiplier,
    finMultiplier_eq_one_of_mem, finMultiplier_inv, ← principalMinor_coe_inv]
namespace Space
variable {E : Type*} [Field E] [CMType E] [WeilData E] {n : Type _} [Fintype n] {s : n → ℤˣ}
  (V : Space E n s) (ℓ ℓ' θ : Model (adelicHeis E s) →L[ℂ] ℂ)
def ratVectors := V.vecAtPoint.toAddMonoidHom.range
omit [WeilData E] in
lemma mem_ratVectors_iff {y} : y ∈ V.ratVectors ↔ V.x *ᵥ y ∈ _root_.ratVectors E n :=
  exists_congr fun _ ↦ inv_smul_eq_iff (g := V.x)
instance : CompactSpace (_ ⧸ V.ratVectors) := (Homeomorph.Quotient.congr (.smul V.x⁻¹) (by simp
  [QuotientAddGroup.leftRel_eq, mem_ratVectors_iff, mulVec_neg, Units.smul_def])).compactSpace (X :=
  _ ⧸ _root_.ratVectors ..)
attribute [local simp↓] add_left add_right modelInner_heisOp_vacElem
lemma beta_vecAtPoint_eq_one x y : (adelicHeis E s).β (V.vecAtPoint x)
  (V.vecAtPoint y) = 1 := by simp [adelicHeis, stdForm_vecAtPoint, ← map_mul]
def IsRatInvariant := ∀ᵉ (γ ∈ V.ratVectors) (v), ℓ (heisOp γ v) = ℓ v
def IsThetaFunctional := V.IsRatInvariant θ ∧
  quotMean V.ratVectors (fun x ↦ θ (heisOp x vacElem) * conj (θ (heisOp x vacElem))) = 1
variable {V ℓ ℓ' θ} (h : V.IsThetaFunctional θ) (h' : V.IsRatInvariant ℓ') (hℓ : V.IsRatInvariant ℓ)
  {c : ℂ}
  (hc : quotMean V.ratVectors (fun x ↦ ℓ (heisOp x vacElem) * conj (ℓ' (heisOp x vacElem))) = c)
  (f' f : Model (adelicHeis E s))
lemma isDualFamily_beta_sq : IsDualFamily V.ratVectors fun γ x ↦
  (adelicHeis E s).β x (V.vecAtPoint γ) ^ 2 := by
  use fun _ ↦ ⟨(adelicHeis E s).6.curry_left.pow 2, ?_⟩, ?_, ?_, ?_, fun x h ↦
    V.mem_ratVectors_iff.2 (mem_ratVectors.2 fun i ↦ mem_ratAdeles_of_psi fun a ↦
    cast ?_ (h (V.J⁻¹ *ᵥ Pi.single i (star (j⁻¹ * a))))), fun x h ↦ V.vecAtPoint_injective
    (star_injective (.trans (dotProduct_eq_zero _ fun w ↦ eq_zero_of_forall_stdAddChar_eq_one
    fun u ↦ cast ?_ (h (stdForm E s *ᵥ toAdele (j⁻¹ : E) • u • w))) (by simp)))
  iterate 4 simp [ratVectors, beta_vecAtPoint_eq_one, mul_pow]
  repeat simp [-Pi.single_apply, adelicHeis, sq, vecAtPoint, comp_def, Circle.ext_iff, ← map_add,
    ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← add_mul, ← map_mul, ← mul_assoc (toAdele j),
    j_ne_zero, mul_assoc, map_J_inv, star_mulVec_dotProduct, RingHom.map_mulVec,
    -mulVec_single, -single_vecMul, Pi.apply_single fun _ ↦ @toAdele E ..]
lemma summable_modelInner : Summable fun γ ↦ modelInner f' (heisOp (V.vecAtPoint γ) f) :=
  (wiener_bound (modelInner f') (u := vacElem) (by simp [vacuumFn]) (.id _) f'.2.1 id
  (by simp [← conj_modelInner])).elim fun _ ⟨k, _, h⟩ ↦ .of_enorm
  ((h V.vecAtPoint.toAddMonoidHom f).trans_lt ((isCovolOneLattice_ratVectors.finite_preimage
  (k.preimage_smul V.x⁻¹)).cast_ncard_eq ▸ by tauto)).ne
namespace IsRatInvariant
include h' hℓ
lemma isContPeriodic : IsContPeriodic V.ratVectors fun x ↦
  ℓ (heisOp x f) * conj (ℓ' (heisOp x f')) := ⟨by fun_prop,
  fun _ g x ↦ by simp [← h' _ g (heisOp x _), ← hℓ _ g (heisOp x _), mul_mul_mul_comm]⟩
include hc
lemma quotMean_eq : quotMean V.ratVectors (fun x ↦ ℓ (heisOp x f) * conj (ℓ' (heisOp x f'))) =
  c * modelInner f' f := hc ▸ integral_form_eq_mul_modelInner (fun _ ↦
  (innerSL ℂ).bilinearComp (ℓ' ∘L _) (ℓ ∘L _)) (h'.isContPeriodic hℓ · · |>.integrable_out)
  (by simpa [mul_mul_mul_comm] using! fun _ _ _ ↦ quotMean_translate (h'.isContPeriodic hℓ ..) _) ..
lemma hasSum_modelInner : HasSum (fun γ ↦ c * modelInner f' (heisOp (V.vecAtPoint γ) f)) (ℓ f * conj
  (ℓ' f')) := by simpa using isDualFamily_beta_sq.fourier_inversion (h'.isContPeriodic hℓ ..)
                   ((summable_modelInner ..).mul_left c) (fun γ ↦ by
  simp [← h'.quotMean_eq hℓ hc]; congr with x
  simp [← hℓ _ ⟨γ, rfl⟩ (heisOp x _), add_comm, field, mul_assoc]) 0
end IsRatInvariant
lemma exists_isThetaFunctional : ∃ θ, V.IsThetaFunctional θ := by
  by_contra! n
  have k ℓ (hℓ : V.IsRatInvariant ℓ) u : ℓ u = 0 := (CStarAlgebra.nonneg_iff_eq_mul_star_self.1
    (integral_nonneg fun _ ↦ mul_star_self_nonneg _)).elim fun s e ↦
    have := And.intro (hℓ.hasSum_modelInner hℓ e u u).tsum_eq (n (s⁻¹ • ℓ))
    by by_cases s = 0 <;> simp_all [IsThetaFunctional, IsRatInvariant, mul_mul_mul_comm]
  let ℓ u := continuousLinearMapOfTendsto (∑ γ ∈ ·, modelInner u ∘L heisOp (V.vecAtPoint γ))
    (by simpa [tendsto_pi_nhds] using! (summable_modelInner u · |>.hasSum))
  simpa [vacuumFn] using (isDualFamily_beta_sq.tsum_coeff_eq_quotMean id (S := {0}) (by simp)
    (summable_modelInner vacElem vacElem)).trans congr(quotMean _ fun a ↦ $((tsum_congr
    (by simp [field])).trans (k (ℓ (heisOp (-a) vacElem)) (fun _ ⟨γ, h⟩ f ↦ .trans (tsum_congr (by
    simp [beta_vecAtPoint_eq_one, ← h])) ((Equiv.addRight γ).tsum_eq _)) (heisOp (-a) vacElem))))
namespace IsThetaFunctional
include h
lemma exists_eq_apply_smul : ∃ u, ∀ ℓ, V.IsRatInvariant ℓ → ℓ = ℓ u • θ :=
  (θ.1.surjective_of_ne_zero (fun _ ↦ by simp_all [DFunLike.ext_iff, IsThetaFunctional]) 1).imp
  fun u _ ℓ hℓ ↦ have k f := ((h.1.hasSum_modelInner hℓ rfl u f).unique
    (by simpa using (h.1.hasSum_modelInner h.1 h.2 ..).mul_left _)); by ext; simp at *; grind
lemma eq_smul (hℓ : V.IsRatInvariant ℓ) : ∃ c : ℂ, ℓ = c • θ :=
  ⟨_, h.exists_eq_apply_smul.choose_spec _ hℓ⟩
lemma injective_apply_heisOp : Function.Injective fun f x ↦ θ (heisOp x f) := fun _ _ e ↦ sub_eq_zero.1 (eq_zero_of_modelInner_self (by simp [← (h.1.quotMean_eq h.1 h.2 ..).trans (one_mul _), congrFun e]))
