import Lib.DiscreteSeries.Haar.UnitaryNorm
import Lib.General.LinearAlgebra.PartialDerivComm
section
open Matrix LinearMap Algebra Fintype IsHermInvolution Topology
variable {n} [Fintype n] {J x : Matrix n n ℂ} [IsHermInvolution J] (y : Matrix n n ℝ)
lemma det_mulLeft_mulRight_real {m} [Fintype m] P Q : (mulRightLinearMap m ℝ Q ∘ₗ mulLeftLinearMap n ℝ P).det = ‖det P‖ ^ (2 * card n) * ‖(det Q : ℂ)‖ ^ (2 * card m) := by erw [(mulRightLinearMap m ℂ Q ∘ₗ mulLeftLinearMap ..).det_restrictScalars, ← det_toMatrix (stdBasis ℂ ..), congrArg det _, det_kronecker' P Qᵀ] <;> simp [← ext_iff, toMatrix_apply, stdBasis, mul_apply, ite_apply, norm_complex_eq, pow_mul, Complex.sq_norm]
lemma exists_U_coe_eq : xᴴ * J * x = J → ∃ g : U J, g = x := (⟨U.of isUnit x ·, rfl⟩)
lemma isClosedEmbedding_U : IsClosedEmbedding (·.1.1 : U J → _) := U.isClosedEmbedding_mat isUnit
lemma continuous_U_iff_matrix {X} [TopologicalSpace X] {f : X → U J} : Continuous f ↔ Continuous (f · |>.1.1) := isClosedEmbedding_U.continuous_iff
section
omit [Fintype n]
@[simp] lemma skewCoords_skewOfReal : skewCoords (skewOfReal y) = y :=
 ext (by simp [skewCoords, skewOfReal]; grind)
@[simp] lemma conjTranspose_skewOfReal : (skewOfReal y)ᴴ = -skewOfReal y :=
 ext (by simp [skewOfReal]; grind)
@[simp] lemma skewOfReal_skewCoords : xᴴ = -x → skewOfReal (skewCoords x) = x := by simp [skewCoords, skewOfReal, Complex.ext_iff, ← ext_iff]; grind
end
end
section
open Matrix MeasureTheory Module Real Complex LinearMap Fintype Norms.L2Operator IsHermInvolution MatMul
variable {n} [Fintype.{0} n] {J : Matrix n n ℂ} {V W} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : V → U J) (p)
abbrev DifferentiableAtU := DifferentiableAt ℝ (Φ · |>.1.1) p
noncomputable def logDerivU := mulLeft ℝ ((Φ p).1.1ᴴ * J) ∘ₗ (fderiv ℝ (Φ · |>.1.1) p).1
variable {Φ p} [FiniteDimensional ℝ W]
lemma conjTranspose_logDerivU [IsHermInvolution J] (h : DifferentiableAtU Φ p) v : (logDerivU Φ p v)ᴴ = -logDerivU Φ p v := by have := congr($(((h.hasFDerivAt.star.mul_const' J).fun_mul' h.hasFDerivAt).fderiv) v); simp_all [logDerivU, isHermitian.eq, star, mem_U.1]; grind
lemma logDerivU_mul {Ψ} (h : DifferentiableAtU Φ p) (h' : DifferentiableAtU Ψ p) v : logDerivU (fun p ↦ Φ p * Ψ p) p v = (Ψ p).1.1ᴴ * logDerivU Φ p v * (Ψ p).1.1 + logDerivU Ψ p v := by simp_all [logDerivU, fderiv_fun_mul']; grind [mem_U]
lemma abs_det_skew_congruence (e : _ ≃ₗ[ℝ] V) C L : |(e.1 ∘ₗ skewCoords ∘ₗ mulLeftRight ℝ (Cᴴ, C) ∘ₗ @skewOfReal n ∘ₗ L).det| = ‖C.det‖ ^ (2 * card n) * |(e ∘ₗ L).det| := by rw [(?_ : _ ∘ₗ _ = _ * e ∘ₗ L), map_mul, abs_mul, (skewCoords ∘ₗ mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal).det_conj e, ← sqrt_mul_self_eq_abs, ← det_prodMap, (((skewOfReal.coprod (I • skewOfReal)).linearEquivOfInjective (by
  simp [Function.Injective, skewOfReal, ↓← ext_iff, Complex.ext_iff]; grind) (by simp +arith [ finrank_matrix])).eq_toLinearMap_symm_comp (prodMap ..) _).2, LinearMap.det_conj, det_mulLeft_mulRight_real Cᴴ C] <;> simp [DFunLike.ext_iff]
lemma Haar.det_eq_mul_of_block_triangular [FiniteDimensional ℝ V] {T : End ℝ (V × W)} (A : End ℝ V) (h : ∀ v, (T v).1 = A v.1) {B} (h' : B = snd .. ∘ₗ T ∘ₗ inr .. := by rfl) : T.det = A.det * B.det := by simp_rw [← det_toMatrix ((finBasis ℝ V).prod (finBasis ℝ W)), ← det_toMatrix (finBasis ..)]; convert det_fromBlocks_zero₁₂' ..; simp_all [← ext_iff, toMatrix_apply]; tauto
variable [IsHermInvolution J] [FiniteDimensional ℝ V]
variable [MeasureSpace V] [BorelSpace V] [(@volume V _).IsAddHaarMeasure] [MeasureSpace W] [BorelSpace W] [(@volume W _).IsAddHaarMeasure] {a b q q'} [h : @HasGaussianIntegral V _ a q]
instance : (@volume (V × W) _).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure ..
instance {m} [Fintype m] : @HasGaussianIntegral (Matrix m n V) _ (a * card n * card m) fun x ↦ ∑ a, ∑ b, q (x a b) := h.pi.pi
noncomputable def circleScalar (t : ℝ) : U J := U.of isUnit ((t * I).exp • 1) (by simp [smul_smul, mul_conj'])
include h
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [(@volume V _).IsAddHaarMeasure] in
lemma lintegral_gaussian_eq_one : ∫⁻ x, ‖rexp (-π * q x)‖ₑ = 1 := by simp [-neg_mul, h.1 pi_pos, ← ofReal_integral_norm_eq_lintegral_enorm (.of_integral_ne_zero _)]
lemma HasGaussianIntegral.measurePreserving (e : V ≃ₗ[ℝ] W) [k : HasGaussianIntegral b q'] (he : ∀ x, q' (e x) = q x) : MeasurePreserving e := have m := isClosedEmbedding_of_injective e.ker; ⟨m.measurable, addHaar_eq_of_integral_eq_one (by simpa using integral_exp_eq pi_pos) ((m.integral_map _).trans (by simpa [he] using integral_exp_eq pi_pos))⟩
lemma HasGaussianIntegral.exists_measurePreserving_equiv (f : Matrix n n ℝ →ₗ[ℝ] V) (hf : ∀ y, q (f y) = ∑ a, ∑ b, y a b ^ 2) (hd : finrank ℝ (Matrix n n ℝ) = finrank ℝ V) : ∃ e : V ≃ₗ[ℝ] _, MeasurePreserving e ∧ ⇑e.symm = f := let e := f.linearEquivOfInjective (.of_ker _ fun _ z ↦ ext (by simpa [← z, hf, Finset.sum_eq_zero_iff_of_nonneg, Finset.sum_nonneg, sq_nonneg] using hf 0)) hd; ⟨e.symm, measurePreserving _ (hf _ ▸ congr(q $(e.4 ·))), rfl⟩
end
section
noncomputable section
open Matrix MeasureTheory Measure Set IsHermInvolution Norms.L2Operator ComplexOrder Fintype Haar MatMul
section
variable {n} [Fintype.{0} n] (J J' : Matrix n n ℂ) [IsHermInvolution J] (y : Matrix n n ℝ)
def cayleyDenom := 1 - (2⁻¹ : ℂ) • (J⁻¹ * skewOfReal y)
attribute [local simp] det_ne_zero inv_smul cayleyDenom Function.comp_def logDerivU InjOn mul_assoc subset_def ENNReal.mul_lt_top_iff isUnit_iff_isUnit_det
@[simps! -isSimp coe_val] def cayleyChart : U J := U.of isUnit ((2 : ℂ) • (cayleyDenom J y)⁻¹ - 1) <| (cayleyDenom J y).nonsing_inv_cancel_or_zero.elim (fun ⟨_, e⟩ ↦ have e := congr((cayleyDenom J y)⁻¹ᴴ * J * $e); by have := congr($eᴴ); simp [isHermitian.eq, two_smul] at *; grind) (by aesop)
abbrev cayleyDensity := ((‖J.det‖ * ‖(cayleyDenom J y).det‖ ^ 2) ^ card n)⁻¹
@[simp] abbrev sphereDensity k (r : ℝ) := 2 * .pi ^ k / (k - 1).factorial * r ^ (k - 1)
def volU j := ∏ i ∈ .range j, sphereDensity (i + 1) 1
def haarU := ((volume.withDensity (.ofReal <| cayleyDensity J · / volU (card n))).comap (↑)).map ({y | (cayleyDenom J y).det ≠ 0}.domRestrict (cayleyChart J))
instance measureSpaceU : MeasureSpace (U J) := ⟨haarU J⟩
@[simp] lemma vUP j : 0 < volU j := by delta volU; positivity
@[simp] lemma det_cayleyDenom_one_ne_zero : (cayleyDenom 1 y).det ≠ 0 := IsAccretive.det_ne_zero (by norm_num [IsAccretive, PosDef.ofNat])
section
variable {J J' y} (g : U J) [IsHermInvolution J'] (a b : GL n ℂ) (ε : ℝˣ) (φ : U J ≃ U J') (hb : b.1ᴴ * ε • J * b = J' := by aesop) (hφ : ∀ g, (φ g).1 = a * g * b := by simp) {V} [NormedAddCommGroup V] [NormedSpace ℝ V] (e : V ≃ₗ[ℝ] Matrix n n ℝ)
@[fun_prop] lemma mCC : Measurable (cayleyChart J) := by simp [measurable_comap_iff, Matrix.inv_def, val_cayleyChart_coe]; fun_prop
omit [IsHermInvolution J] in
@[fun_prop] lemma cCD : Continuous (cayleyDenom J) := by fun_prop [cayleyDenom]
lemma lCC (h : (cayleyDenom J y).det ≠ 0) : DifferentiableAtU (cayleyChart J) y ∧ ∀ v, logDerivU (cayleyChart J) y v = (cayleyDenom J y)⁻¹ᴴ * skewOfReal v * (cayleyDenom J y)⁻¹ := by have d := ((hasFDerivAt_ringInverse (IsUnit.unit (by simpa))).comp y (((skewOfReal.toContinuousLinearMap ).hasFDerivAt.const_mul ((2⁻¹ : ℂ) • J⁻¹)).const_sub 1)).fun_const_smul (2 : ℂ); simp [← nonsing_inv_eq_ringInverse, ← (inv_smul_eq_iff₀ _).2 (add_eq_of_eq_sub (val_cayleyChart_coe ..))] at *; simp [d.fderiv, d.differentiableAt, ← mul_assoc, -Matrix.mul_assoc, mem_U.1]; grind
def cCI := skewCoords ((2 : ℂ) • (J * (1 - (2 : ℂ) • (g.1.1 + 1)⁻¹)))
lemma cayleyChart_injOn : {y | (cayleyDenom J y).det ≠ 0}.InjOn (cayleyChart J) := .of_comp (g := cCI) (by simp_all [cCI, val_cayleyChart_coe])
lemma cCCI (h : IsUnit (g.1.1 + 1)) : (cayleyDenom J (cCI g)).det ≠ 0 ∧ cayleyChart J (cCI g) = g := by obtain _ := h.mul_val_inv, U.gram_invariant g h.unit.2 h.unit.2; erw [Subtype.ext_iff, Units.ext_iff, val_cayleyChart_coe, cayleyDenom, skewOfReal_skewCoords]; aesop; simp_all [isHermitian.eq, two_smul, ← eq_sub_iff_add_eq]; grind
lemma mEC : MeasurableEmbedding ({y | (cayleyDenom J y).det ≠ 0}.domRestrict (cayleyChart J)) := by apply_rules [Measurable.measurableEmbedding, MeasurableSet.standardBorel, cayleyChart_injOn.injective] <;> measurability
lemma lintegral_eq_cayleyChart f : lintegral volume f = ∫⁻ y in {y | (cayleyDenom J y).det ≠ 0}, .ofReal (cayleyDensity J y / volU (card n)) * f (cayleyChart J y) := by erw [mEC.lintegral_map, ← setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable, ← lintegral_subtype_comap] <;>
  measurability
include hb in
lemma cCJ {y p L} (hy : HasFDerivAt y L p) {Φ : V → U J'} (h : (cayleyDenom J (y p)).det ≠ 0) (E : ∀ᶠ q in nhds p, (Φ q).1.1 = a * cayleyChart J (y q) * b := by simp [*]) : DifferentiableAtU Φ p ∧ |(e.symm ∘ₗ skewCoords ∘ₗ logDerivU Φ p).det| =
  |(e.symm ∘ₗ L.1).det| * cayleyDensity J (y p) := by
  obtain ⟨⟨d, l⟩, ⟨⟩⟩ := lCC h, hb, (by simpa using congr(√‖det $(‹IsHermInvolution J'›.2)‖ ^ card n)); have D := (((d.hasFDerivAt.comp p hy).const_mul _).mul_const' _).congr_of_eventuallyEq E; use ⟨_, D⟩; rw [(_ : logDerivU .. = _ ∘ₗ skewOfReal ∘ₗ (ε • L).1), abs_det_skew_congruence _ (_ * _)]; rotate_right; ext1; simpa [D.fderiv, ↓← U.form_mul_inv_eq, E.self_of_nhds] using congr(ε • _ * $(l _) * b); simp_all [mul_pow, cayleyDensity, pow_mul, pow_two, LinearMap.comp_smul, e.finrank_eq, Module.finrank_matrix, ε.smul_def]; grind
lemma abs_det_logDerivU_cayleyChart (h : (cayleyDenom J y).det ≠ 0) : DifferentiableAtU (cayleyChart J) y ∧ |(skewCoords ∘ₗ logDerivU (cayleyChart J) y).det| = cayleyDensity J y := by simpa using cCJ 1 1 1 (by simp) (.refl ..) (hasFDerivAt_id y) h
lemma Haar.lintegral_chart_rotate_le [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V] [(@volume V _).IsAddHaarMeasure] (he : MeasurePreserving e) {A} {Φ : V → U J} (hA : MeasurableSet A) (hi : A.InjOn Φ) {w : V → ℝ} (hΦ : ∀ p ∈ A, DifferentiableAtU Φ p ∧ |(e.symm ∘ₗ skewCoords ∘ₗ logDerivU Φ p).det| = w p) : ∀ᵐ t, ∀ f, ∫⁻ p in A, .ofReal (w p / volU (card n)) * f (circleScalar t * Φ p) ≤ lintegral volume f := .mono ((((volume.restrict A).map Φ).ae_ae_comm (by
 measurability)).1 (.of_forall fun x ↦ (((-x.1.1⁻¹).finite_spectrum.countable.preimage_circleMap 0 one_ne_zero).ae_notMem _).mono fun t h ↦ show IsUnit ((circleScalar t * x :).1.1 + 1) by
 simpa [Algebra.smul_def, circleScalar, circleMap] using (of_not_not h).mul x.1.isUnit)) fun t h
 f ↦ by
 have ⟨O, o, m, h⟩ := ((ae_restrict_mem hA).and (ae_of_ae_map ((isClosedEmbedding_U.continuousOn_iff.2 (hΦ · · |>.1.continuousAt.continuousWithinAt)).aemeasurable hA) h)).exists_measurable_mem; have k p u := cCCI _ (h p u).2; have D p u : HasFDerivAt (cCI <| circleScalar t * Φ ·) _ p := have := (hΦ p (h p u).1).1
  (skewCoords.toContinuousLinearMap.differentiableAt.comp p (by
   simp [nonsing_inv_eq_ringInverse]; fun_prop (disch := aesop))).hasFDerivAt
 grw [lintegral_eq_cayleyChart, ← he.setLIntegral_comp_preimage_emb (he.1.measurableEmbedding e.injective), restrict_mono_ae (s := A) (ae_imp_of_ae_restrict o), setLIntegral_congr_fun m, ← lintegral_image_eq_lintegral_abs_det_fderiv_mul _ m (D · · |> (e.symm.toContinuousLinearEquiv ).hasFDerivAt.comp _ |>.hasFDerivWithinAt) (.of_comp (g := cayleyChart J ∘ e) (by aesop))]; gcongr; aesop; simp +contextual [*, mul_div_assoc, cCCI, EqOn, (hΦ ..).2 ▸ cCJ (circleScalar t : U J)⁻¹ 1 1 _ e (D ..) (k ..).1 (.mono ((((hΦ ..).1.const_mul _).add_const _).continuousAt (h ..).2.unit.nhds) _)]; tauto
include hb hφ
lemma lCH f : lintegral volume f ≥ ∫⁻ g, f (φ g) := by have ⟨t, h, k⟩ := ((lintegral_chart_rotate_le (.refl ..) (.id _) (by measurability) (φ.injective.comp_injOn cayleyChart_injOn) (cCJ a b ε hb _ <| hasFDerivAt_id ·)).and ((quasiMeasurePreserving_neg _).ae (lintegral_chart_rotate_le 1 (.id _) (by measurability) cayleyChart_injOn (@abs_det_logDerivU_cayleyChart _ _ J' _)))).exists; simp_all [lintegral_eq_cayleyChart]; convert! (h (f <| _ * ·)).trans (k f); ext; simp [circleScalar, Complex.exp_neg]
lemma measurePreserving_haarU : MeasurePreserving φ := have c := .subtype_mk (by measurability); ⟨c, ext_of_lintegral _ fun f h ↦ lintegral_map h c ▸ (lCH a b ε φ hb hφ f).antisymm (by simpa using lCH a⁻¹ b⁻¹ ε⁻¹ φ.symm (gram_inv_of_gram_eq (by aesop)) (by simp_all [↓reindex_equiv φ]) (f ∘ φ))⟩
end
instance : (@volume (U J) _).IsHaarMeasure := by
 have : SigmaFinite (haarU J) := by apply_rules [(measurePreserving_subtype_coe _).sigmaFinite, mEC.sigmaFinite_map]; measurability
 have := exists_subset_measure_lt_top .univ (by
  rw [← lintegral_one, @lintegral_eq_cayleyChart _ _ J, setLIntegral_pos_iff, inter_eq_right.2]
  apply cCD.matrix_det.isOpen_support.measure_pos _ ⟨0, _⟩; repeat measurability)
 have : (haarU J).IsMulLeftInvariant := ⟨(measurePreserving_haarU · 1 1 (.mulLeft _) |>.2)⟩; rw [haarMeasure_unique volume Classical.ofNonempty] at *; apply IsHaarMeasure.smul <;> aesop
end
end
end
noncomputable section
open Finset _root_.Int _root_.Matrix _root_.Module ComplexConjugate Equiv Fintype
variable {n : Type} [Fintype n] (J : Matrix n n ℂ) (l : n → ℤ) {ε : n → ℤˣ}
def unitaryLie := (⟨⟨⟨{X | Xᴴ * J + J * X = 0}, by grind [conjTranspose_add, add_mul, mul_add]⟩, by
    simp⟩, by simp_all [star, ← smul_add]⟩ : Submodule ℝ _)
open Norms.Operator in
@[simps! coe_val] def expU {J} (X : @unitaryLie n _ J) : U J := ⟨X.1.isUnit_exp.unit, by
 simpa [U, ← exp_conjTranspose] using! SemiconjBy.exp_neg_mul_mul_exp_eq_self
  (neg_mul _ J ▸ eq_neg_of_add_eq_zero_right X.2 :)⟩
def weightMinors g := ∏ᶠ t, principalMinor g (t ≤ l ·) / ite (t ≤ 0) g.det 1
abbrev gapThreshold n [Fintype n] (A : ℕ) : ℝ := 500 * card n ^ 3 + A
def twoRho r [DecidableRel r] i := (#{j | r i j ∧ l j < l i} - #{j | r i j ∧ l i < l j} : ℤ)
def paramAddRho i := (l i + twoRho l ⊤ i) / 2
def weylDimensionPoly := (∏ i, ∏ j with l j < l i, (l i - l j : ℝ) / 2) / ∏ i ∈ range (card n), ↑i.factorial
def maxCompactU (ε : n → ℤˣ) := (U 1).subgroupOf (U (signMatrix ε))
instance (ε : n → ℤˣ) : CompactSpace (maxCompactU ε) := ((isClosed_U _).isClosedEmbedding_subtypeVal.restrictPreimage _).compactSpace (Y := U 1)
def haarK (ε : n → ℤˣ) : MeasureTheory.Measure (maxCompactU ε) := .haarMeasure ⊤
@[simp] def entryMask r [DecidableRel r] := (⟨⟨(of fun i j ↦ if r i j then · i j else 0), by aesop⟩, by aesop⟩ : Matrix n n ℂ →ₗ[ℂ] _).toContinuousLinearMap
def blockDiagPart (ε : n → ℤˣ) := entryMask (ε · = ε ·)
abbrev HCParam {n : Type*} (_ : n → ℤˣ) := n → ℤ
abbrev toHCParam (ε : n → ℤˣ) (l : n → ℤ) : HCParam ε := l
abbrev HCParam.compactForm (l : HCParam ε) := toHCParam 1 l
abbrev HCParam.kTypeNormSq (l : HCParam ε) := ∫ k, ‖weightMinors l k‖ ^ 2 ∂haarK ε
class HCParam.HasGap (l : HCParam ε) (h : outParam ℝ) where
 injective : l.Injective
 parity i : Even (l i + card n - 1)
 gap i j : ε i ≠ ε j → 2 * h ≤ |l i - l j|
abbrev HCParam.HasLargeGap (l : HCParam ε) A := l.HasGap (gapThreshold n A)
def HCParam.lowestKType (l : HCParam ε) : HCParam ε := fun i ↦ paramAddRho l i - twoRho l (ε · = ε ·) i
def HCParam.casimirValue (l : HCParam ε) := ∑ i, (l i ^ 2 - twoRho l ⊤ i ^ 2 : ℝ) / 4
def HCParam.flenstedJensen (l : HCParam ε) (g z : Matrix n n ℂ) := (∫ k, weightMinors l.lowestKType (g * k) * conj (weightMinors l.lowestKType k) / weightMinors (-paramAddRho l) (k.1.1.1ᴴ * z * k) ∂haarK ε) / l.lowestKType.kTypeNormSq
def HCParam.dsCoeff (l : HCParam ε) (g : Matrix n n ℂ) := l.flenstedJensen (blockDiagPart ε g) ((blockDiagPart ε g)⁻¹ * g)
variable (l : HCParam ε) {α β} [Fintype α] [Fintype β] (a : α → ℤˣ) {b : β → ℤˣ}
def HCParam.formalDegree := (∫ g : USign ε, ‖l.dsCoeff g‖ ^ 2)⁻¹
def HCParam.dsKernel (g : USign ε) := l.formalDegree * conj (l.dsCoeff g)
export HCParam (kTypeNormSq HasGap lowestKType flenstedJensen dsCoeff formalDegree dsKernel)
@[local simp] def negCount := card {x // a x = -1}
lemma negCount_neg_add : negCount (-a) + negCount a = card α := by simp [← units_ne_iff_eq_neg, card_subtype_le]
@[simp] lemma negCount_sumElim : negCount (a ⊕ᵥ b) = negCount a + negCount b := (card_congr subtypeSum).trans card_sum
@[simp] lemma negCount_one_and_neg_one : negCount (1 : α → ℤˣ) = 0 ∧ negCount (-1 : α → _) = card α := by simp
lemma exists_equiv_of_card_neg {a} (h : card α = card β) (h' : negCount a = negCount b) : ∃ e : α ≃ β, b ∘ e = a := ⟨_, funext (ofFiberEquiv_map fun c ↦ equivOfCardEq (by
 fin_cases c <;> simp_all [(@units_ne_iff_eq_neg _ 1).not_right]))⟩
def diagChar (w : n → ℤ) (b : Matrix n n ℂ) := ∏ i, b i i ^ w i
def IsBorelMatrix (o : n → ℤ) (b : Matrix n n ℂ) := b.BlockTriangular o ∧ b.det ≠ 0
def IsKDominant (ε : n → ℤˣ) (o w : n → ℤ) := ∀ i j, ε i = ε j → o i < o j → w j ≤ w i
def IsPosFirstOrder (ε : n → ℤˣ) (o : n → ℤ) := o.Injective ∧ ∀ i j, ε i = 1 → ε j = -1 → o i < o j
def HasHolGap (ε : n → ℤˣ) (w : n → ℤ) (γ : ℕ) := ∀ i j, ε i = 1 → ε j = -1 → w i + γ ≤ w j
def blockDiagAlg (ε : n → ℤˣ) := Subalgebra.centralizer ℂ {signMatrix ε}
open Norms.L2Operator
variable {Φ : Type} (ε : n → ℤˣ) (o : n → ℤ) [Fintype Φ] (b : Matrix n n ℂ)
def IsHolOfWeight (u : Φ → _) (F : _ → ℂ) (ε' : n → ℤˣ := 1) := ∃ F', ∀ h b : Φ → _, (∀ τ, IsBorelMatrix o (b τ)) → (∀ τ, ↑(h τ : USign ε) ∈ blockDiagAlg ε' ∧ b τ ∈ blockDiagAlg ε') → letI z τ := h τ * b τ; AnalyticAt ℂ F' z ∧ F' z = (∏ τ, diagChar (u τ) (b τ)) * F h
def holMinors := letI c i := ite (ε i = 1) (2 * ∑ j, |o j|) 0; weightMinors (fun i ↦ o i + c i) b / weightMinors c b
def holMinorsPi (u : Φ → _) (h : Φ → USign ε) := ∏ τ, holMinors ε (u τ) (h τ)
def diagTorus (t : n → Circle) : USign ε := ⟨IsUnit.unit (a := diagonal (t ·)) (by simp [Pi.isUnit_iff]), by simp [U, signMatrix, field, ← Circle.coe_inv_eq_conj]⟩
structure GlModule (n M) [Fintype n] [AddCommGroup M] [Module ℂ M] where
 ρ : Matrix n n ℂ →ₗ[ℂ] End ℂ M
 map_bracket X Y : ρ (X * Y - Y * X) = ρ X * ρ Y - ρ Y * ρ X
variable {X M} [NormedAddCommGroup X] [NormedSpace ℂ X] [AddCommGroup M] [Module ℂ M] {J : Matrix n n ℂ} (A) (π : U J →* X →L[ℂ] X) {ε : n → ℤˣ} (l : HCParam ε) (ι : M →ₗ[ℂ] X) (ρ : GlModule n M)
structure IsUnitaryRep (B : X →L⋆[ℂ] X →L[ℂ] ℂ) where
 continuous x : Continuous (π · x)
 invariant g x y : B (π g x) (π g y) = B x y
 conj_symm x y : starRingEnd ℂ (B x y) = B y x
 pos : ∀ x ≠ 0, 0 < (B x x).re
 growth : ∃ c, ∀ g, ‖π g‖ ≤ c * ‖g.1.1‖ ^ A
instance : CoeFun (GlModule n M) fun _ ↦ Matrix n n ℂ → End ℂ M := ⟨(·.ρ)⟩
abbrev GlModule.E a b := ρ (.single a b 1)
def GlModule.restrictTo p (h : ∀ X, p ∈ (ρ X).invtSubmodule) : GlModule n p := by use! (.restrict _ <| h ·) <;> aesop (add simp map_bracket)
def IsDerivedAction := ∀ Y v, HasDerivAt (fun t : ℝ ↦ π (expU (t • Y)) (ι v)) (ι (ρ Y v)) 0
@[simp] abbrev GlModule.IsCompactPrimitive x := ∀ a b, ε a = ε b → l b < l a → ρ.E a b x = 0
def HCParam.IsKHighest (ν : n → ℤ) x := (∀ a, ρ.E a a x = (ν a : ℂ) • x) ∧ ρ.IsCompactPrimitive l x
def HCParam.rootCone := {β | ∀ o, (∀ i j, l j < l i → o i < o j) → o ⬝ᵥ β ≤ (0 : ℤ)}
def GlModule.IsCoeffMap (c : U J → M →ₗ[ℂ] X) := ∀ g Y v t, HasDerivAt (fun t : ℝ ↦ c (g * expU (t • Y)) v) (c (g * expU (t • Y)) (ρ Y v)) t
def GlModule.casimir r [DecidableRel r] := ∑ a, ∑ b with r a b, ρ.E a b * ρ.E b a
abbrev GlModule.casimirK (ε : n → ℤˣ) (ρ : GlModule n M) := ρ.casimir (ε · = ε ·)
