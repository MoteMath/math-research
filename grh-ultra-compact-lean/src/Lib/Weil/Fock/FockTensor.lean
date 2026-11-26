import Lib.Weil.Construction.SubmoduleNormedSpace
import Lib.General.LinearAlgebra.HaarUnique
import Lib.DiscreteSeries.Haar.UnitaryNorm
import Lib.General.Measure.HaarModulus
import Lib.General.Analysis.HolomorphicIntegral
noncomputable section
open MeasureTheory ComplexConjugate Subtype LinearMap DFunLike
namespace Heisenberg
variable {W : Type _} [AddCommGroup W] [TopologicalSpace W] (H : Heisenberg W) [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] {μ : Measure W}
  [μ.IsAddHaarMeasure] {e : W → ℂ} [he : IsVacuum H μ e] {X : Type _} [NormedAddCommGroup X]
  [NormedSpace ℂ X] {Y : Type _} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
attribute [local simp] mul_le_of_le_one_right norm_smul mul_le_mul add_left add_right integral_add
  norm_integral_le_of_norm_le Integrable.norm smul_smul
omit [μ.IsAddHaarMeasure] in
lemma IsVacuum.integrable_mul_kernel x {f} : Integrable f μ → Integrable (fun y ↦
  f y * (H.β y x * e (x - y))) μ := (·.mono (he.rec (by fun_prop)) (by simp [he.norm_le_one]))
def IsVacuum.modelSubmodule : Submodule ℂ (W → ℂ) := by
  use! {v | Integrable v μ ∧ ∀ x, ∫ y, v y * (H.β y x * e (x - y)) ∂μ = v x} <;> simp_all
    [add_mul, integrable_mul_kernel, mul_assoc, Integrable.smul]
def IsVacuum.Model := ↥he.modelSubmodule
deriving instance AddCommGroup, Module ℂ for (he.Model)
instance : CoeFun he.Model fun _ ↦ W → ℂ := ⟨val⟩
def IsVacuum.toL1 : he.Model →ₗ[ℂ] W →₁[μ] ℂ := by use! (·.2.1.toL1) <;> tauto
instance : NormedAddCommGroup he.Model := .induced _ _ he.toL1 fun v w h ↦ Subtype.ext (funext
  (v.2.2 · ▸ w.2.2 _ ▸ integral_congr_ae (.mul_right (by simp_all [IsVacuum.toL1, coe]))))
instance : NormedSpace ℂ he.Model := .induced ..
namespace IsVacuum
variable {H} (x : W) (v w : Model H)
section
omit [μ.IsAddHaarMeasure]
@[simp] lemma add_apply : (v + w) x = v x + w x := rfl
@[simp] lemma smul_apply c : (c • v) x = c * v x := rfl
@[simp] lemma zero_apply : (0 : Model H) x = 0 := rfl
@[ext] lemma ext {v w : Model H} : (∀ x, v x = w x) → v = w := Subtype.ext ∘ funext
lemma norm_eq : ‖v‖ = ∫ x, ‖v x‖ ∂μ := L1.norm_of_fun_eq_integral_norm v.2.1
end
omit [μ.IsAddHaarMeasure] in
@[local simp] lemma norm_apply_le : ‖v x‖ ≤ ‖v‖ :=
  v.2.2 x ▸ by simp [norm_eq, v.2.1, he.norm_le_one]
section
omit [μ.IsAddHaarMeasure]
@[fun_prop] lemma continuous : Continuous v := v.2.elim (continuous_of_dominated (he.rec
  (by fun_prop)) (by simp [he.norm_le_one]) ·.norm (.of_forall (he.rec (by fun_prop))) |>.congr)
def heisRep : H.Rep (Model H) :=
  let ρ y : _ →ₗᵢ[ℂ] _ := by
    use! fun v ↦ ⟨fun x ↦ H.β y x * v (x - y), (v.2.1.comp_sub_right y).mono
      (by fun_prop) (by simp), fun x ↦ (integral_add_right_eq_self _ y).symm.trans (by
      simp [↓← v.2.2 (x - _), ← integral_const_mul, sub_eq_add_neg]; ac_nf)⟩
    iterate 2 solve_by_elim [ext, mul_add, mul_left_comm]
    simp [↓norm_eq, coe, integral_sub_right_eq_self fun _ ↦ ‖_‖]
  ⟨(ρ · |>.toContinuousLinearMap), by
    simp [↓he.ext_iff, ↓smul_apply, ρ, coe, sub_eq_add_neg]; grind,
    (ρ · |>.2), continuous_prod_of_continuous_lipschitzWith' _ _ (ρ · |>.lipschitz) fun v ↦
    have h (w : Model H) := w.2.1.norm
    .of_at fun a ↦ tendsto_iff_norm_sub_tendsto_zero.2 (by
      simpa [norm_map, integral_sub, h, ← norm_eq, neg_add_eq_sub] using ((continuous_of_dominated
      (fun t ↦ ((h (ρ t v)).sub (h (-ρ a v + ρ t v))).1) (by simp [(abs_norm_sub_norm_le ..).trans])
      (h (-ρ a v)) (.of_forall (by simp [↓add_apply, ρ, coe]; fun_prop))).tendsto a).const_sub ‖v‖)⟩
abbrev heisOp : Model H →L[ℂ] Model H := heisRep.ρ x
def vacElem : Model H := ⟨e, he.6, by simpa [he.2] using he.5 0⟩
def modelEval : Model H →L[ℂ] ℂ := mkContinuous (by use! (· x) <;> simp) 1 (by simp [coe])
def kernelIntegral (σ : ℂ →+* ℂ) [RingHomIsometric σ] (K : W → X →L[ℂ] Y) (hK : ∀ x,
  Continuous (K · x)) (hC : ∀ y x, ‖K y x‖ ≤ ‖x‖) : Model H →SL[σ] X →L[ℂ] Y :=
  have hi (v : Model H) x := (v.2.1.smul_const x).mono ((σ.isometry.continuous.comp'
    (continuous v)).fun_smul (hK x)).aestronglyMeasurable (by simp_all)
  mkContinuous₂ (by apply mk₂'ₛₗ _ _ fun v x ↦ ∫ y, σ (v y) • K y x ∂μ <;>
    simp_all [add_smul, ← integral_smul, mul_comm]) 1
    (id fun v ↦ by simp_all [norm_eq, ← integral_mul_const, v.2.1.norm.mul_const])
def modelInner : Model H →L⋆[ℂ] Model H →L[ℂ] ℂ :=
  kernelIntegral _ modelEval continuous norm_apply_le
@[simp] lemma valueAt_apply : modelEval x v = v x := rfl
@[simp] lemma vacElem_apply : he.vacElem x = e x := rfl
end
@[simp] lemma heisOp_apply y : heisOp y v x = H.β y x * v (x - y) := rfl
attribute [irreducible] heisRep
omit [μ.IsAddHaarMeasure] in
lemma integrable_norm_sq : Integrable (‖v ·‖ ^ 2) μ :=
  (v.2.1.smul ‖v‖).mono (by fun_prop) (by simp [sq])
omit [μ.IsAddHaarMeasure] in
@[local simp] lemma modelInner_apply : modelInner v w = ∫ x, conj (v x) * w x ∂μ := rfl
omit [μ.IsAddHaarMeasure] in
lemma conj_modelInner : conj (modelInner v w) =
  modelInner w v := by simp [← integral_conj, mul_comm]
lemma modelInner_heisOp : modelInner (heisOp x v) (heisOp x w) = modelInner v w := by
  simp [mul_mul_mul_comm, ← integral_sub_right_eq_self (_ * w ·) x]
@[simp] lemma modelInner_heisOp_vacElem : modelInner (heisOp x vacElem) v = v x :=
  v.2.2 x ▸ by simp [he.4, ← he.3 (_ - x), mul_comm]
omit [μ.IsAddHaarMeasure] in
lemma modelInner_self : modelInner v v = ∫ x, ‖v x‖ ^ 2 ∂μ := by simp [RCLike.conj_mul]; norm_cast
omit [μ.IsAddHaarMeasure] in
lemma eq_zero_of_modelInner_self {v} (h : he.modelInner v v = 0) : v = 0 :=
  norm_eq_zero.1 (by simp_all [↓modelInner_self, norm_eq, integral_eq_zero_iff_of_nonneg, Pi.le_def,
  integrable_norm_sq, v.2.1, Filter.EventuallyEq])
end IsVacuum
instance : CompleteSpace he.Model := NormedAddCommGroup.completeSpace_of_summable_imp_tendsto fun u
  h ↦ have hv := (Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.2 h)).trans ((ae_all_iff.2
    (u · |>.2.1.coeFn_toL1)).mono fun _ ↦ tsum_congr)
  have hi := .congr (by fun_prop) hv; ⟨⟨_, hi, by simp (maxDischargeDepth := 4) [← tsum_mul_right,
    (u _).2.symm, ← integral_tsum_of_summable_integral_norm, he.integrable_mul_kernel,
    h.of_norm_bounded,
    he.norm_eq, -Real.norm_eq_abs, he.norm_le_one]⟩, ((Topology.IsInducing.hasSum_iff ⟨rfl⟩
    ..).1 (Lp.ext (hv.trans hi.coeFn_toL1.symm) ▸ (Summable.of_norm ‹_›).hasSum)).tendsto_sum_nat⟩
variable {H} [CompleteSpace X] (R : H.Rep X) (T : X →L[ℂ] Y) (x : W)
  (v : Heisenberg.IsVacuum.Model H) (w : Heisenberg.IsVacuum.Model H) (f : X) [CompleteSpace Y]
def Rep.integrated := he.kernelIntegral (.id _) R.ρ (by fun_prop) (by simp)
omit [μ.IsAddHaarMeasure] [CompleteSpace X] in
lemma Rep.integrated_apply : R.integrated v f = ∫ y, v y • R.ρ y f ∂μ := rfl
omit [μ.IsAddHaarMeasure] in
lemma Rep.map_integrated_eq_integral : T (R.integrated v f) = ∫ y, v y • T (R.ρ y f) ∂μ := by
  erw [← T.integral_comp_comm (v.2.1.smul_bdd ‖f‖ (by fun_prop) _)] <;> simp
@[simp] lemma Rep.integrated_heisOp : R.integrated (he.heisOp x v) f = R.ρ x (R.integrated v f) :=
  (integral_add_left_eq_self _ x).symm.trans (by simp [map_integrated_eq_integral, mul_comm])
omit [μ.IsAddHaarMeasure] in
lemma Rep.map_integrated {R' : H.Rep Y} (hT : ∀ y f, T (R.ρ y f) = R'.ρ y (T f)) : T (R.integrated v
  f) = R'.integrated v (T f) := by grind [map_integrated_eq_integral, integrated_apply]
namespace IsVacuum
omit [μ.IsAddHaarMeasure] in
lemma integrated_apply_eq_integral (R : H.Rep (Model H)) : R.integrated v w x = ∫ y,
  v y * R.ρ y w x ∂μ := R.map_integrated_eq_integral (modelEval x) ..
lemma integrated_vacElem : he.heisRep.integrated v vacElem = v :=
  ext (by simp [integrated_apply_eq_integral, v.2.2])
lemma map_eq_integral (T : Model H →L[ℂ] Y) : T v = ∫ y, v y •
  T (heisOp y vacElem) ∂μ := by rw [← Rep.map_integrated_eq_integral, integrated_vacElem]
lemma hom_ext {L L' : Model H →L[ℂ] Y} (h : ∀ y, L (heisOp y vacElem) = L' (heisOp y vacElem)) : L =
  L' := by grind +extAll [map_eq_integral]
@[simp] lemma integrated_eq_smul : he.heisRep.integrated v w =
  w 0 • v := congr($(hom_ext (L' := .smulRightL ℂ _ _ (modelEval 0)) fun _ ↦ hom_ext fun _ ↦
  ext (by simp [integrated_apply_eq_integral, he.3, he.5, -add_left, field])) v w)
lemma exists_lift {K} (hK : Continuous K) {C} (hC : ∀ y, ‖K y‖ ≤ C) :
    ∃ L : Model H →L[ℂ] X, ∀ M N : _ →L[ℂ] Y, (∀ y, M (K y) = N (heisOp y vacElem)) → ∀ v, M (L v) =
  N v := have i (v : Model H) := v.2.1.smul_bdd _ (by fun_prop) (.of_forall hC)
  ⟨strongIntegral μ fun y ↦ (modelEval y).smulRight (K y), fun M _ _ _ ↦ by
    rw [strongIntegral_apply, ← M.integral_comp_comm, map_eq_integral] <;> aesop⟩
lemma integral_form_eq_mul_modelInner [LocallyCompactSpace W] {Z m} {ν : @Measure Z m} (B : Z →
  Model H →L⋆[ℂ] _ →L[ℂ] ℂ) (hi : ∀ v w, Integrable (B · v w) ν) (hB : ∀ x f g, ∫ z,
  B z (heisOp x f) (heisOp x g) ∂ν = ∫ z, B z f g ∂ν) v w : ∫ z, B z v w ∂ν = (∫ z,
  B z vacElem vacElem ∂ν) * modelInner v w := have k v := strongIntegral_apply _ _ (hi v)
  have h x f := by simpa using hB x (heisOp (-x) f)
  have t u := strongIntegral_apply _ (fun z ↦
    innerSLFlip ℂ 1 ∘SL (B z).flip u) (hi · _ |>.inner_const _)
  k .. ▸ congr($(hom_ext (L' := (_ : ℂ) • _) fun y ↦ star_injective (by
    rw [k, h, ← k, map_eq_integral, ← integral_neg_eq_self]
    simpa [*, he.3, he.4, conj_modelInner, mul_comm, ← integral_conj] using
      (heisRep.map_integrated_eq_integral _ vacElem (heisOp (-y) v)).symm.trans (t ..))) w)
end IsVacuum
end Heisenberg
end
noncomputable section
namespace Heisenberg.IsVacuum
open MeasureTheory Heisenberg.Rep ContinuousLinearMap
variable {W : Type _} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W} [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] {μ : Measure W}
  [μ.IsAddHaarMeasure] {e : W → ℂ} [he : IsVacuum H μ e] {G : Type _} [Group G] [TopologicalSpace G]
  [DistribMulAction G W] [ContinuousSMul G W] {c : G → G → ℂ} (B : H.MultiplierAction μ e G c)
  (A : H.MultiplierAction μ e G) (g : G) (h : G) (k : G) (x) (v : Heisenberg.IsVacuum.Model H)
  (w : Heisenberg.IsVacuum.Model H)
def weilOp := B.Δ g • (heisRep.moveBy B g).integrated.flip vacElem
lemma integrated_moveBy_integrated : (heisRep.moveBy B g).integrated
  ((heisRep.moveBy B k).integrated w v) x = (heisRep.moveBy B (g * k)).integrated w ((heisRep.moveBy
  B g).integrated v x) := by rw [← flip_apply, map_integrated]; rfl; simp [mul_smul]
lemma map_integrated_moveBy (T : _ →L[ℂ] ℂ) : T ((heisRep.moveBy B g).integrated w v) = ∫ y,
  w (g⁻¹ • y) * T (heisOp y v) ∂μ
  := .trans (by simp [map_integrated_eq_integral]) ((B.2 g).integral_comp' (f := .smul g) _)
lemma weilOp_triple : weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h =
  c g h • 1 := have := (map_integrated_moveBy B (T := modelEval ·))
  hom_ext (by simp_all [← B.7, weilOp, integrated_moveBy_integrated, mul_assoc, smul_smul,
    ← neg_add', he.3, -neg_add_rev, mul_left_comm])
omit [μ.IsAddHaarMeasure] in
lemma norm_integrated_flip_le (R : H.Rep (Model H)) : ‖R.integrated.flip v‖ ≤ ‖v‖ := by
  grw [le_opNorm, opNorm_flip, integrated, kernelIntegral, LinearMap.mkContinuous₂_norm_le] <;> simp
@[simp] lemma modelInner_vacElem : he.modelInner vacElem v =
  v 0 := by simp [← modelInner_heisOp_vacElem]
lemma weilOp_one : weilOp B 1 = 1 := hom_ext (by simp [weilOp, he.2])
lemma weilOp_mul (h1 : ∀ g, c g 1 = 1) h : weilOp B g * weilOp B h = c g h • weilOp B (g * h) := by
  grind [weilOp_triple B (g * h)⁻¹ 1, weilOp_triple, weilOp_one, =_ mul_smul_one, one_smul, inv_inv]
@[simp] lemma modelInner_weilOp (h1 : c g 1 = 1) : modelInner (weilOp B g v) (weilOp B g w) =
  modelInner v w := by
  convert congr(modelInner ($(weilOp_triple B g 1) v) w) using 1 <;> simp_all [weilOp_one,
    ← conj_modelInner w]
  set u := weilOp B g v; simp [weilOp, map_integrated_moveBy _ g, map_integrated_eq_integral,
    conj_modelInner, ← integral_conj, ← conj_modelInner _ u, mul_comm]
def cocycleRadical (h1 : ∀ g, c g 1 = 1) : Subgroup G := by
  have H g h k := congr(modelInner (weilOp B (g * h * k) vacElem)
    ($(mul_assoc (weilOp B g) (weilOp B h) (weilOp B k)) vacElem))
  simp_all [weilOp_mul, he.2]; use! {s | ∀ g, c g s = 1}, ?_, h1 <;> grind [inv_mul_cancel]
def weilRep := MonoidHom.mk ⟨_, weilOp_one A⟩ (by simp [weilOp_mul])
lemma modelInner_weilRep : modelInner (weilRep A g v) (weilRep A g w) =
  modelInner v w := by simp [weilRep]
attribute [simp] weilOp modelInner_weilRep
lemma weilRep_heisOp : weilRep A g (heisOp x v) =
  heisOp (g • x) (weilRep A g v) := by simp [weilRep]
lemma weilRep_eq_integral : weilRep A g v = A.Δ g • ∫ y, v (g⁻¹ • y) • heisOp y vacElem ∂μ := by
  rw [← (A.2 g).integral_comp' (f := .smul g)]; aesop
lemma conj_delta_mul_weilRep_vacElem : starRingEnd _ (A.Δ g) * weilRep A g vacElem 0 = 1 := by
  simpa [integrated_moveBy_integrated, he.2] using! congr($(weilOp_triple A 1 g⁻¹) vacElem 0)
@[fun_prop] lemma continuous_weilRep [FirstCountableTopology G] : Continuous ↿(weilRep A · ·) := by
  refine A.4.fst'.smul (continuous_prod_of_continuous_lipschitzWith' _ _ (lipschitzWith_of_opNorm_le
    <| norm_integrated_flip_le _ <| moveBy _ A ·) fun v ↦ continuous_of_dominated ?_ ?_
    (v.2.1.smul_const he.vacElem).norm (.of_forall ?_)) <;> simp [norm_smul] <;> fun_prop
attribute [irreducible] weilRep
end Heisenberg.IsVacuum
end
namespace Heisenberg
open MeasureTheory Heisenberg.Rep IsVacuum Measure ENNReal Set MultiplierAction
variable {W : Type _} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W} [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W]
  {μ : Measure W} [μ.IsAddHaarMeasure] {e : W → ℂ} {W₁ : Type _} [AddCommGroup W₁]
  [TopologicalSpace W₁] {H₁ : Heisenberg W₁} [MeasurableSpace W₁] [IsTopologicalAddGroup W₁]
  [BorelSpace W₁] [SecondCountableTopology W₁] [LocallyCompactSpace W₁] {μ₁ : Measure W₁}
  [μ₁.IsAddHaarMeasure] {e₁ : W₁ → ℂ} {W₂ : Type _} [AddCommGroup W₂] [TopologicalSpace W₂]
  {H₂ : Heisenberg W₂} [MeasurableSpace W₂] [IsTopologicalAddGroup W₂] [BorelSpace W₂]
  [SecondCountableTopology W₂] [LocallyCompactSpace W₂] {μ₂ : Measure W₂} [μ₂.IsAddHaarMeasure]
  {e₂ : W₂ → ℂ} {X : Type _} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
structure OrthogonalSum H H₁ H₂ (e : W → ℂ) [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂] where
  equiv : W₁ × W₂ ≃ₜ+ W
  beta_equiv x y : β H (equiv x) (equiv y) = β H₁ x.1 y.1 * β H₂ x.2 y.2
  vac_equiv x : e (equiv x) = e₁ x.1 * e₂ x.2
variable (R : Rep H X) [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂] (S : H.OrthogonalSum H₁ H₂ e)
  [he : H.IsVacuum μ e] (v : Heisenberg.IsVacuum.Model H₁) (w : Heisenberg.IsVacuum.Model H₂)
  (x : W) (f : X)
attribute [local simp] IsVacuum.ext_iff OrthogonalSum.beta_equiv weilRep
  integrated_apply_eq_integral
lemma IsVacuum.wiener_bound [LocallyCompactSpace W]
    [T2Space W₁] (T : Model H →L[ℂ] X) {u} (hu : u 0 ≠ 0) (κ : _ →ₜ+ W) {g :
  _ → X} (hg : Integrable g μ₁) (t : W → _) (h : ∀ z x, ‖T (heisOp (z + κ x) u)‖ₑ = ‖g
  (t z + x)‖ₑ) : ∃ B, IsCompact B ∧ ∃ M : NNReal, ∀ {I} [AddGroup I] (φ : I →+ _) v,
  ∑' i, ‖T (heisOp (κ (φ i)) v)‖ₑ ≤ (φ ⁻¹' B).encard * M * ‖v‖ₑ := by
  obtain ⟨m, K, k, o⟩ := (continuous u).enorm.comp κ.2.neg, exists_compact_mem_nhds (0 : W₁)
  let ⟨r, hr⟩ := exists_nat_mul_gt ((setLIntegral_pos_iff m.measurable).2
    (μ₁.measure_pos_of_mem_nhds ((m.continuousAt.eventually_ne (by simpa)).and o))).ne' one_ne_top
  refine ⟨_, k.neg.add k, r * ‖hg.toL1‖₊ + 1, fun φ v ↦ ?_⟩
  cases e : encard _ <;> by_cases v = 0 <;> simp [*]
  grw [← le_self_add, mul_assoc, mul_assoc, show _ * ‖v‖ₑ = ∫⁻ z, ∫⁻ x, ‖v z‖ₑ * ‖T (heisOp (z + κ
    x) u)‖ₑ ∂μ₁ ∂μ by simp [*, v.2.1, ↓lintegral_const_mul', mul_comm, lintegral_add_left_eq_self
    (‖g ·‖ₑ), ← Integrable.enorm_toL1]; exact mul_comm .., lintegral_lintegral_swap (by fun_prop),
    ← nsmul_eq_mul,
    ← mul_smul_comm, ← μ₁.restrict_le_self, ← lintegral_smul_measure, ← sum_restrict_le (fun i ↦
    measurable_sub_const (φ i) k.measurableSet) fun _ ↦ e ▸ encard_le_encard_of_injOn (fun γ h ↦
    ⟨_, neg_mem_neg.2 h, _, (Classical.epsilon_spec_aux ⟨0⟩ _ ⟨_, h⟩ :), by simp; rfl⟩)
    sub_left_injective.injOn, lintegral_sum_measure, ← ENNReal.tsum_mul_left]; gcongr
  grw [← (measurePreserving_add_left ..).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft (φ i)), ← one_mul ‖_‖ₑ, hr, mul_assoc, lintegral_mul_const_le]
  gcongr; simp [preimage]
  simpa [norm_smul, ← ofReal_norm, add_left_comm] using (heisRep.map_integrated_eq_integral
    (T ∘L heisOp ..) v (heisOp _ u) ▸ enorm_integral_le_lintegral_enorm _ :)
attribute [local simp ←] integral_smul map_add map_sub integral_prod_mul
@[local simp] def Rep.left : H₁.Rep X := ⟨(R.ρ <| S.equiv ⟨·, 0⟩), by simp, by simp, by fun_prop⟩
@[local simp] def Rep.right : H₂.Rep X := ⟨(R.ρ <| S.equiv ⟨0, ·⟩), by simp, by simp, by fun_prop⟩
noncomputable def OrthogonalSum.tmul : Model H₁ →L[ℂ] Model H₂ →L[ℂ] Model H :=
  ((heisRep.left S).integrated.flip ∘L (heisRep.right S).integrated.flip vacElem).flip
lemma OrthogonalSum.isVacuum : H.IsVacuum ((μ₁.prod μ₂).map S.equiv) e := by
  unhygienic cases_type* IsVacuum OrthogonalSum; cases (equiv.eq_comp_symm ..).2 (funext ‹_›)
  use (by fun_prop) <;> simp (disch := fun_prop) [*, equiv.surjective.forall, integral_map,
    integrable_map_measure, Function.comp_def, Integrable.mul_prod]
  simp [← twisted_conv, ← twisted_conv_1, mul_mul_mul_comm]
lemma OrthogonalSum.measurePreserving_equiv [LocallyCompactSpace W] :
    MeasurePreserving S.equiv (μ₁.prod μ₂) μ :=
  ⟨by fun_prop,
  addHaar_eq_of_integral_eq_one he.integral_norm_sq_eq_one S.isVacuum.integral_norm_sq_eq_one⟩
omit [CompleteSpace X] in
lemma OrthogonalSum.integral_eq_integral_prod [LocallyCompactSpace W]
    (f : W → X) : ∫ x, f x ∂μ = ∫ x, f
  (S.equiv x) ∂μ₁.prod μ₂ := S.measurePreserving_equiv.2 ▸ S.equiv.isClosedEmbedding.integral_map f
omit [LocallyCompactSpace W₁] [μ₁.IsAddHaarMeasure] [LocallyCompactSpace W₂]
  [μ₂.IsAddHaarMeasure] in
@[local simp] lemma OrthogonalSum.tmul_apply : S.tmul v w x =
  v (S.equiv.symm x).1 * w (S.equiv.symm x).2 := by
  erw [← valueAt_apply, ← v.2.2, ← w.2.2,
    map_integrated_eq_integral _ (modelEval _ ∘L integrated _ v)]
  revert x; simp [map_integrated_eq_integral, S.equiv.surjective.forall, ← integral_const_mul,
    ← integral_mul_const, S.vac_equiv]; grind
lemma OrthogonalSum.weilRep_tmul [LocallyCompactSpace W]
    {G G₁ G₂} [Group G] [TopologicalSpace G] [DistribMulAction G W]
  [ContinuousSMul G W] [Group G₁] [TopologicalSpace G₁] [DistribMulAction G₁ W₁] [ContinuousSMul G₁
  W₁] [Group G₂] [TopologicalSpace G₂] [DistribMulAction G₂ W₂] [ContinuousSMul G₂ W₂] A A₁ A₂ {g :
  G} {g₁ : G₁} {g₂ : G₂} (hΔ : Δ A g = Δ A₁ g₁ * Δ A₂ g₂) (ha : ∀ x, g • S.equiv x = S.equiv (g₁ •
  x.1, g₂ • x.2)) v w : weilRep A g (S.tmul v w) = S.tmul (weilRep A₁ g₁ v) (weilRep A₂ g₂ w) :=
  by simp_all [S.equiv.surjective.forall, S.integral_eq_integral_prod, S.vac_equiv]; grind
lemma Rep.integrated_tmul [LocallyCompactSpace W] : R.integrated (S.tmul v w) f =
  (R.left S).integrated v ((R.right S).integrated w f) :=
  by simp [↓map_integrated_eq_integral, integrated_apply, S.integral_eq_integral_prod, smul_smul,
       mul_comm]
     exact integral_prod_symm _ ((v.2.1.mul_prod w.2.1).smul_bdd ‖f‖ (by fun_prop) (by simp))
omit [LocallyCompactSpace W₁] [μ₁.IsAddHaarMeasure] [LocallyCompactSpace W₂]
  [μ₂.IsAddHaarMeasure] in
lemma OrthogonalSum.tmul_vacElem : S.tmul vacElem vacElem = vacElem := by simp [← S.3]
omit [LocallyCompactSpace W₁] [LocallyCompactSpace W₂] in
lemma OrthogonalSum.heisOp_tmul : heisOp x (S.tmul v w) = S.tmul (heisOp (S.equiv.symm x).1 v)
  (heisOp (S.equiv.symm x).2 w) := by simp [map_sub, mul_mul_mul_comm, ← S.2]
end Heisenberg
section FoldSeg3
open Matrix Fintype Norms.L2Operator Sgn MeasureTheory Complex ComplexOrder Finset MvPolynomial
section
variable {ι} [Fintype ι] {ε : ι → _} (u : USign ε)
attribute [local simp] posProj signMatrix
@[simp] lemma posProj_mul_self : posProj ε * posProj ε = posProj ε ∧ (posProj ε)ᴴ = posProj ε ∧
  (signMatrix ε)ᴴ = signMatrix ε := by simp
omit [Fintype ι] in
lemma signMatrix_eq_posProj_sub : signMatrix ε = posProj ε - (1 - posProj ε) := by aesop
lemma principalMinor_sign_eq_det u : principalMinor u (ε · = -1) = (posProj ε + (1 - posProj ε) *
  u).det := by rw [principalMinor_eq_det, sub_mul, congrArg det]; aesop
attribute [simp] signMatrix_mul_self
noncomputable def realMultiplier := starRingEnd _ (principalMinor u (ε · = -1))
lemma norm_realMultiplier_le : ‖realMultiplier u‖ ≤ ‖u.1.1‖ ^ Fintype.card
  ι := by cases isEmpty_or_nonempty ι <;> simp [realMultiplier, norm_principalMinor_le_pow.trans,
  pow_le_pow_right₀, U.one_le_norm, card_subtype_le]
end
variable {ι} [Fintype ι] {ε : ι → _} (x y) (P : MvPolynomial ι ℂ)
attribute [local simp] holCoord_eq realHeis realVac sum_div signMatrix_eq_posProj_sub
attribute [local simp ←] exp_add sum_neg_distrib integral_const_mul sum_add_distrib sum_sub_distrib
lemma beta_mul_realVac : (realHeis ε).β y x * realVac (x - y) = realVac x * realVac y * exp
  (star (holCoord ε y) ⬝ᵥ holCoord ε x) := by simp [posProj, dotProduct]; grind [conj_conj]
lemma integrable_exp_mul_realVac C : Integrable (fun u ↦ (C * ‖u‖).exp * ‖realVac u‖) (realMeasure
  ι) := .mono (.smul (C * C).exp (.of_integral_ne_zero ((integral_gauss (A := scalar ι 4⁻¹)
  (by norm_num [IsAccretive]) 0).trans_ne (by simp)))) (by fun_prop [realVac]) (.of_forall (by
    simp_intro u [← Real.exp_add]; bound [norm_sq_le_re_star_dot u, sq_nonneg (‖u‖ - 2 * C)]))
instance isVacuum_realVac :
  (realHeis ε).IsVacuum (realMeasure ι) realVac := by refine' ⟨by fun_prop [realVac], _, _, _, fun y
  x ↦ by convert congr(realVac y * realVac x * $((integral_add_right_eq_self _ (y - posProj ε *ᵥ
  (x + y))).trans (integral_gauss PosDef.one.isAccretive (-signMatrix ε *ᵥ (x + y))))) using 1 <;>
  simp [star_mulVec_dotProduct]; grind, (integrable_exp_mul_realVac 0).mono' (by fun_prop [realVac])
  _⟩ <;> simp [star_dot_self_eq_sum, ← exp_conj, map_ofNat]
@[simp] lemma norm_holCoord : ‖holCoord ε y‖ = ‖y‖ ∧ ∀ i, ‖holCoord ε y i‖ = ‖y i‖ := by simp [norm,
  apply_ite]
lemma exists_norm_eval_le_exp : ∃ k C, ∀ l, ‖eval l P‖ ≤ |C| * .exp ((k : ℕ) * ‖l‖) :=
  ⟨_, _, fun l ↦ by
  grw [eval_eq', norm_sum_le, ← le_abs_self, ‖l‖.exp_nat_mul, sum_mul]; simp
  grw [norm_le_pi_norm l, ‖l‖.le_exp_log, Real.log_le_self, P.monomial_le_degreeOf,
    prod_pow_eq_pow_sum] <;> bound⟩
end FoldSeg3
section FoldSeg4
open Complex ComplexOrder Matrix U
attribute [local simp] fromBlocks_add fromBlocks_smul mul_assoc realHeis realVac realMultiplier
variable {ι : Type*} [Fintype ι]
noncomputable def realCoordSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {ε ε₁ ε₂} {e :
  ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) : (realHeis ε).OrthogonalSum (realHeis ε₁) (realHeis ε₂)
  realVac := by use { (.funCongrLeft ℂ ℂ e ≪≫ₗ
  .sumArrowLequivProdArrow ..).symm.toContinuousLinearEquiv with toFun x := (x.1 ⊕ᵥ x.2) ∘
  e.symm } <;> simp_all [← exp_add, ← e.sum_comp, funext_iff, dotProduct, signMatrix] <;> grind
@[simp] lemma unitary_smul_eq_mulVec {ε} (g : USign ε) (x : ι → ℂ) : g • x = g.1.1 *ᵥ x := rfl
noncomputable def realAction ε : (realHeis ε).MultiplierAction (realMeasure ι) realVac (USign ε) :=
  ⟨by simp [↓form_mulVec_mulVec], (⟨by fun_prop, by simp [map_mulVec_haar ·.1.det_ne_zero]⟩),
  realMultiplier, by fun_prop [realMultiplier], by simp, by simp [↓principalMinor_coe_inv],
  fun g h ↦ by
  set k := g * h; let T x := posProj ε + (1 - posProj ε) * x; let J := h.1.1.fromBlocks 0 0 k.1.1
  have := (integral_gauss (A :=
    ofReal 2⁻¹ • (Jᴴ * J + fromBlocks 1 (1 + signMatrix ε) (1 - signMatrix ε) 1)) ?P 0).symm
  rw [(realCoordSum (e := .refl _) (ε ⊕ᵥ ε).comp_id).integral_eq_integral_prod,
    ← mul_eq_one_iff_inv_eq₀ (IsAccretive.det_ne_zero
    ?P), MeasureTheory.integral_prod _ (.of_integral_ne_zero (by aesop))] at *
  convert! this using 6
  rw [show _ • _ = ((T h).fromBlocks (1 - posProj ε) 0 (T ↑k⁻¹ * k.1.1))ᴴ * (posProj ε).fromBlocks
    (posProj ε - 1) 1 1 * fromBlocks 1 1 (-T h) (-T h + T ↑g⁻¹ * k.1.1) by
    linear_combination (norm := (
      simp +zetaDelta [mul_sub, mul_add, add_mul, signMatrix_eq_posProj_sub, sub_mul,
        ← mul_assoc (posProj _) (posProj _)]; split_ands <;> module))
      congr(ofReal 2⁻¹ • fromBlocks $(h.2) 0 0 (-$(k.2)))]
  all_goals simp [J, T, ↓det_mul, -conjTranspose_add, ← principalMinor_coe_inv, field, realCoordSum,
    ← principalMinor_sign_eq_det, IsAccretive, conj_mul', ← exp_add, fromBlocks_mulVec,
    star_mulVec_dotProduct, Function.star_sumElim]
  ring
  convert (PosDef.conjTranspose_mul_self J ?_).add_posSemidef (.submatrix .one (id ⊕ᵥ id)) <;>
    simp [J, ← ext_iff, mulVec_injective_iff_isUnit]; grind⟩
end FoldSeg4
noncomputable section
open Complex MvPolynomial Heisenberg IsVacuum Finset Int MeasureTheory Measure Matrix Sum
  OrthogonalSum Function Fintype
variable {ι} [Fintype ι] {ε : ι → _}
abbrev fockSpace ε := Model (@realHeis ι _ ε)
abbrev realWeil : USign ε →* fockSpace ε →L[ℂ] fockSpace ε := weilRep (realAction ε)
abbrev realHeisOp (x : ι → ℂ) : fockSpace ε →L[ℂ] fockSpace ε := heisOp x
abbrev vacVector : fockSpace ε := vacElem
abbrev realInner : fockSpace ε →L⋆[ℂ] fockSpace ε →L[ℂ] ℂ := modelInner
lemma differentiableAt_superposition ε {E} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
  P (f : E → ℂ × _ → _) {a} (hf : ∀ x, Differentiable ℂ (f · x)) (cf : Continuous f.uncurry)
  (h0 : ∀ y, f a y = (holCoord ε y.2, -(star y.2 ⬝ᵥ y.2) / 2)) (h : ∀ z (r : ℝ) y, f z (r • y) =
  (r • (f z y).1, r ^ 2 • (f z y).2)) : DifferentiableAt ℂ (fun z ↦ ∫ x, (MvPolynomial.eval (f z (1,
  x)).1 P * exp (f z (1, x)).2) • realHeisOp x (vacVector : fockSpace ε) ∂realMeasure ι) a := by
  obtain ⟨_, k, A, hk⟩ := P.continuous_eval, exists_norm_eval_le_exp P
  exact (eventually_differentiableAt_integral (((integrable_exp_mul_realVac (2 * k)).comp_smul
    one_half_pos.ne').const_mul (|A| * .exp 1 * _)) (by fun_prop) (((isCompact_closedBall 0
    1).eventually_forall_mem (fun z y ↦ k * ‖y.1‖ * (‖(f z y).1‖ - ‖y.2‖) + (f z y - f a y).2.re)
    (.Iio 4⁻¹) (by simp [*, Iio_mem_nhds])).mono fun z H x ↦ ⟨by fun_prop, by
  specialize H ((1 ⊔ ‖x‖)⁻¹ • (1, x))
  grw [norm_smul, mul_comm, norm_mul, hk]
  simp [↓h, *, norm_smul, sq, field, realVac, mul_assoc, ← Real.exp_add] at *
  gcongr 2; grind [sq_nonneg, sq, norm_sq_le_re_star_dot]⟩)).self_of_nhds
lemma exists_hasDerivAt_realHeisOp {P} v hu : ∃ h,
  HasDerivAt (fun t : ℝ ↦ realHeisOp (t • v) ⟨(P.eval <| holCoord ε ·) *
  realVac, hu⟩) (⟨((heisDeriv ε v P).eval <| holCoord ε ·) * realVac, h⟩ : fockSpace ε) 0 := by
  let f | t, (s, w) => (holCoord ε w + t • s • -holCoord ε v,
    -(star w ⬝ᵥ w) / 2 + t * s * (star (holCoord ε v) ⬝ᵥ holCoord ε w - s * star v ⬝ᵥ v / 2 * t))
  have e (t : ℝ) w : realHeisOp (t • v) ⟨_, hu⟩ w = P.eval (f t (1, w)).1 * (f t (1, w)).2.exp := by
    erw [heisOp_apply, mul_left_comm, beta_mul_realVac]
    simp [star_trivial, f, realVac, ← exp_add]; ring
  have' H :=
    (differentiableAt_superposition ε P f ..).hasDerivAt.scomp 0 (hasDerivAt_id 0).ofReal_comp
  simp_rw [Function.comp_def, ← e, ← Rep.integrated_apply, integrated_vacElem] at H
  refine (funext fun w ↦
    ((H.map_clm (modelEval ..)).unique (funext (e · w) ▸ (((hasFDerivAt_mvPolynomial_eval P
    _).hasLineDerivAt _).mul (.cexp (.const_add _ (.mul (hasDerivAt_mul_const _) (.const_sub _
    (hasDerivAt_const_mul _)))))).comp_ofReal)).trans ?_ : _ = _ * _) ▸ ⟨_, H⟩
  simp [heisDeriv, realVac, dotProduct, sum_mul, mul_sum, holCoord_eq, neg_add_eq_sub,
    ← sum_sub_distrib]; congr! 1
  split <;> simp_all [units_ne_iff_eq_neg, raiseOp, lowerOp] <;> ring
  repeat fun_prop
  repeat simp [star_trivial, f, funext_iff, field]
def polyVector ε : MvPolynomial ι ℂ →ₗ[ℂ] @fockSpace ι _ ε := .codRestrict _ (.pi fun x ↦
    (aeval (holCoord ε x)).toLinearMap.smulRight (realVac x)) (by
  induction · using induction_on
  convert (‹_› • vacVector).2; ext; simp; aesop
  convert have D c := (IsVacuum.modelSubmodule _).smul_mem (c / 2) (exists_hasDerivAt_realHeisOp
      (holCoord ε (Pi.single ‹_› c)) ‹_›).1
    add_mem (D 1) (D I)
  ext; simp_all [heisDeriv, holCoord_eq, Finset.sum_eq_single ‹ι›]
  split <;> simp_all [units_ne_iff_eq_neg, raiseOp, lowerOp] <;> grind [I_sq])
instance : Coe (MvPolynomial ι ℂ) (fockSpace ε) := ⟨polyVector ε⟩
@[simp] lemma polyVector_apply P x : polyVector ε P x =
  MvPolynomial.eval (holCoord ε x) P * realVac x := rfl
@[simp] lemma polyVector_one : polyVector ε 1 = vacVector := by aesop
lemma hasDerivAt_realHeisOp v P : HasDerivAt (fun t : ℝ ↦
  realHeisOp (t • v) (polyVector ε P)) (heisDeriv ε v P) 0 := (exists_hasDerivAt_realHeisOp ..).2
attribute [irreducible] polyVector
@[simp] lemma polyVector_injective : (⇑(polyVector ε)).Injective :=
  fun _ _ h ↦ funext (by simpa +contextual [realVac, holCoord_eq] using congr($h <| holCoord ε ·))
namespace Heisenberg.IsVacuum
variable {W W' : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W'] [TopologicalSpace W'] [MeasurableSpace W'] [IsTopologicalAddGroup W']
  [BorelSpace W'] [SecondCountableTopology W'] {H μ e H' μ' e'} [IsAddHaarMeasure μ]
  [IsAddHaarMeasure μ'] [he : IsVacuum H μ e] [he' :
  IsVacuum H' μ' e'] {σ : ℂ →+* ℂ} [RingHomIsometric σ]
  {φ : W' ≃ₜ+ W} (hβ : ∀ x y, σ (H.β (φ x) (φ y)) = H'.β x y) (hφ : ∀ x, e (φ x) = e' x)
include he he' hφ
variable (H H') in
omit [SecondCountableTopology W'] in
lemma measurePreserving_equiv : MeasurePreserving φ μ' μ :=
  ⟨by fun_prop, addHaar_eq_of_integral_eq_one he.integral_norm_sq_eq_one
  (he'.integral_norm_sq_eq_one ▸ _root_.funext hφ ▸ φ.isClosedEmbedding.integral_map _)⟩
include hβ
omit [SecondCountableTopology W'] in
lemma map_integral_and_map_vacuum : (∀ f, σ (integral μ f) = ∫ x, σ (f (φ x)) ∂μ') ∧ ∀ x, σ (e
  (φ x)) = e' x := have _ := hβ; by
  cases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous <;> simp_all
  [integral_conj, he'.4, (measurePreserving_equiv H H' hφ).integral_comp φ.measurableEmbedding]
def transport : Model H →SL[σ] Model H' := have m := measurePreserving_equiv H H' hφ
  LinearMap.mkContinuous (by use! fun v ↦ ⟨_, (σ.toSemilinearMap.mkContinuous 1
                (by simp)).integrable_comp (m.integrable_comp_of_integrable v.2.1), by
              simpa [map_integral_and_map_vacuum hβ hφ, ← map_sub, hβ] using
                (congrArg σ <| v.2.2 <| φ ·)⟩ <;> aesop)
    1 fun v ↦ by erw [norm_eq, m.integral_comp φ.measurableEmbedding (‖σ <| v ·‖), norm_eq]; simp
@[simp] lemma transport_apply v x : transport hβ hφ v x = σ (v (φ x)) := rfl
end Heisenberg.IsVacuum
variable {ι : _} [Fintype ι] {ε : _} {ι₁ ι₂ T : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype T] {ε₁ ε₂}
  {e : ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) (u : T → USign ε) (v : T → fockSpace ε)
attribute [local simp] modelInner_apply realVac add_div exp_add dotProduct eval_rename signMatrix
  holCoord_eq integral_map_equiv norm_eq sum_prod_type weilRep integrated_apply_eq_integral comp_def
  tmul_apply realMultiplier
attribute [local simp ←] exp_sum sum_div integral_fintype_prod_eq_prod volume_pi_pi norm_prod
def realBoxProd : fockSpace ε₁ →L[ℂ] fockSpace ε₂ →L[ℂ] fockSpace ε := (realCoordSum he).tmul
@[local simp] lemma pi_realMeasure : .pi (fun _ ↦ realMeasure ι) =
  (realMeasure _).map (MeasurableEquiv.curry T ..) :=
  Measure.pi_eq (by simp [realMeasure, pow_mul', -inv_pow, Measure.map_smul,
    measurePreserving_curry.2, (MeasurableEquiv.measurable _).aemeasurable])
def piTensor :
  ContinuousMultilinearMap ℂ (fun _ : T ↦ fockSpace ε) (fockSpace (ε <| @Prod.snd T _ ·)) :=
  MultilinearMap.mkContinuous (.codRestrict (.pi fun _ ↦ .compLinearMap (.mkPiAlgebra ..) fun _ ↦
  (modelEval _).1) _ fun v ↦ ⟨(integrable_map_equiv ..).1 (pi_realMeasure.subst (.fintype_prod
  (v · |>.2.1))), by simpa [realHeis] using! fun _ ↦ congr(∏ τ, $((v τ).2.2 _))⟩) 1 (by aesop)
@[simp] lemma piTensor_apply x : piTensor v x = ∏ τ, v τ (x ⟨τ, ·⟩) := rfl
lemma piTensor_polyVector (P : T → _) : piTensor (polyVector ε <| P ·) = ∏ τ,
  rename (τ, ·) (P τ) := by aesop
lemma realInner_piTensor w : realInner (piTensor v) (piTensor w) = ∏ τ,
  realInner (v τ) (w τ) := by aesop
abbrev blockMatrix := letI := @instDecidableEqProd ι T _ _
       (reindexRingEquiv ℂ (.prodComm ι T)).toRingHom.comp (blockDiagonalRingHom ..)
@[simps! apply_coe_val] def blockU : (T → USign ε) →* USign (ε <| @Prod.snd T _ ·) :=
  .mk' (fun u ↦ U.of IsHermInvolution.isUnit (blockMatrix (u ·)) (by
  simpa [← submatrix_mul_equiv (e₂ := .prodComm ..), -Equiv.coe_prodComm]
  using congr(blockMatrix $(funext (u · |>.2))))) fun _ _ ↦ by ext : 2; apply map_mul
lemma realMultiplier_blockU : realMultiplier (blockU u) = ∏ τ, realMultiplier (u τ) := by simp
lemma realWeil_piTensor : realWeil (blockU u) (piTensor v) = piTensor fun τ ↦ realWeil (u τ)
  (v τ) := by ext; simp [realAction]; simp [mulVec, blockDiagonal, realHeis, diagonal]; tauto
lemma realBoxProd_polyVector P Q : realBoxProd he (polyVector _ P) (polyVector _ Q) =
  rename (e ∘ inl) P * rename (e ∘ inr) Q
  := by ext; simp [realBoxProd, reindex_equiv e, by simpa using congrFun he]; ring!
end
