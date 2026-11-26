import Lib.General.LinearAlgebra.ExpSurjective
import Lib.GLn.SchurModule.SchurOrthogonality
section
noncomputable section
namespace Orbital
open Matrix Finset Int AddMonoidAlgebra UnitAddTorus AddCircle Equiv Function HCParam
variable {n} [Fintype.{0} n] (ε : n → ℤˣ) (l : n → ℤ)
def tE (x : n → Circle) : ℂ[n → ℤ] →ₐ[ℂ] ℂ := lift ℂ ℂ _ ⟨⟨(∏ a, x a ^ ·.toAdd a), by simp⟩, by simp [zpow_add₀]⟩
def oppositePairs := univ.filter (ε · = 1) ×ˢ univ.filter (ε · ≠ 1)
def alternant : ℂ[n → ℤ] := ∑ w : Perm n, ite (ε ∘ w = ε) (.single (l ∘ w) w.sign) 0
def WA (t : (n → ℤ) → ℂ) := ∀ w : Perm n, ε ∘ w = ε → ∀ γ, t (γ ∘ w) = w.sign * t γ
def lM : Submonoid (Multiplicative (n → ℤ) × ℂ[n → ℤ]) := ⟨⟨{p | p.2.1 p.1.toAdd = 1 ∧ ∀ γ, p.2.1 γ ≠ 0 → 0 ≤ γ ∧ (γ = p.1.toAdd ∨ l ⬝ᵥ γ < l ⬝ᵥ p.1.toAdd)}, @fun a b ↦ by simp; grind
  [by simpa [subset_iff, mem_add] using a.2.support_coeff_mul_subset b.2, UniqueAdd, add_nonneg, coeff_mul_add_of_uniqueAdd, dotProduct_add, dotProduct_add l a.1.toAdd b.1.toAdd]⟩, by simp [← Finsupp.mem_support_iff]⟩
variable {ε} (l : HCParam ε) (r) [DecidableRel r] {ν ν'} {P Q : ℂ[n → ℤ]} (w : Perm n)
def _root_.HCParam.rP : ℂ[n → ℤ] := ∏ a, ∏ b with r (ε a) (ε b) ∧ l b < l a, (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1)
def _root_.HCParam.lC a := (#{b | r (ε a) (ε b) ∧ l b < l a} : ℤ)
attribute [local simp low] lift_apply' Finsupp.sum funext_iff tE IsKDominant WA mFourier rP toCircle_zsmul oppositePairs Finsupp.linearCombination sum_ite Matrix.mul_apply diagonal
lemma rLM o (h : ∀ a b, l b < l a → o b < o a := by simp_all) : (.ofAdd (l.lC r), l.rP r) ∈ lM o := pi_eq_sum_univ' (l.lC r) ▸ by
  simp_rw [rP, lC, cast_card, sum_smul, ofAdd_sum, prod_mk_prod, prod_sigma']; exact prod_mem (by simp [lM, -funext_iff]; grind [=_ dotProduct_single_one o, Pi.single_nonneg])
lemma tRN {x} : Injective x → tE x (l.rP r) ≠ 0 := by simp [prod_eq_zero_iff]; grind [Circle.ext]
lemma aAp γ : (alternant ε ν).1 γ = ∑ w : Perm n, ite (ε ∘ w = ε ∧ ν ∘ w = γ) ↑w.sign 0 := by simp [alternant, ite_and, Finsupp.single_apply]
lemma tAl x : tE x (alternant ε ν) = det (of fun a b ↦ ite (ε a = ε b) ((x a).1 ^ ν b) 0) := .trans (by simp [alternant, det_apply', prod_ite_zero, comm]) (det_transpose _)
@[fun_prop] lemma continuous_torusEval : Continuous (tE · P) := by continuity
lemma eTE (h : ∀ x, tE x P = tE x Q) : P = Q :=
 ext (orthonormal_mFourier.linearIndependent.of_comp _ (by aesop))
lemma dTE : DenseRange fun P ↦ ContinuousMap.mk (@tE n _ · P) := ((Homeomorph.arrowCongr (.piCongrRight fun _ ↦ homeomorphCircle (by simp)) 1).isDenseEmbedding.dense_image.2 fun _ ↦ span_mFourier_closure_eq_top.ge ⟨⟩).mono (by simpa [Set.subset_def, Homeomorph.arrowCongr, ← Finsupp.range_linearCombination] using (⟨⟨·⟩, by ext; simp [← homeomorphCircle_apply]⟩))
lemma tCP x : tE (x ∘ w) P = tE x ⟨P.1.equivMapDomain (w.arrowCongr 1)⟩ := by simp [-Finsupp.sum]; grind [w.prod_comp]
lemma tCM {c} : (∀ x, tE (x ∘ w) P = c * tE x P) ↔ ∀ ν, P.1 (ν ∘ w) = c * P.1 ν := by simpa [↓tCP, ← coeff_inj, Finsupp.ext_iff] using! Iff.intro (eTE (Q := c • P)) (by lia)
lemma wAl : WA ε (alternant ε ν).1 := by simp_all
  [↓tAl, ← tCM, ← det_permute, submatrix]
variable {l w} (hl : l.Injective) (x)
lemma aPC (hw : ε ∘ w = ε) {d f : _ → ℂ} (h : ∀ (y : maxCompactU ε) x, d (y * diagTorusK x * y⁻¹) = f x) : f (x ∘ w) = f x := h ⟨⟨permMatrixHom.toHomUnits w, ext (by simp_all [signMatrix])⟩,
  ext (by simp)⟩ _ ▸ h 1 _ ▸ congr(d $(by ext; simp [diagTorus, ← map_inv]))
include hl
lemma tRNc : tE x (l.rP Ne) = (∏ p ∈ oppositePairs ε, ite (l p.2 < l p.1) 1 (-1)) * ∏ p ∈ oppositePairs ε, (x p.1 - x p.2 : ℂ) := by simp [← prod_mul_distrib, prod_sigma']; apply prod_bij fun ⟨a, b⟩ _ ↦ ite (ε a = 1) (a, b) (b, a) <;> simp <;> grind [units_eq_one_or (ε _)]
lemma tRNcc (hw : ε ∘ w = ε) x : tE (x ∘ w) (l.rP Ne) = tE x (l.rP Ne) := by simp_all [↓tRNc]; rw [prod_equiv (w.prodCongr w)] <;> aesop
lemma aCK (h : IsKDominant ε (-l) ν) (h' : IsKDominant ε (-l) ν') : (alternant ε (ν + l.lC Eq)).1 (ν' + l.lC Eq) = ite (ν' = ν) 1 0 := by rw [aAp, sum_eq_single 1 fun w _ _ ↦ ?_] <;> simp [comm]; have ⟨i, k⟩ := w.support.exists_max_image l (by_contra (by simpa)); have (i j) h : (_ on l.lC Eq) j i := ofNat_lt.2 (card_lt_card ⟨by grind, mt (@· j h) (by simp)⟩); simp_all; grind -ext [w.surjective i]
lemma eSK γ : ∃ᵉ (s : ℤ) (ν), IsKDominant ε (-l) ν ∧ ∀ t, WA ε t → t γ = s * t (ν + l.lC Eq) := by
  obtain ⟨i, j, c⟩ | c := em (∃ i j, ε i = ε j ∧ γ i = γ j ∧ i ≠ j)
  use 0, 0, by simp, fun t h ↦ by
    simpa [*, self_eq_neg, comp_def, apply_swap_eq_self] using (h (swap i j) · γ)
  let := LinearOrder.lift' l hl; have ⟨w, h⟩ := exists_min_image {w : Perm n | ε ∘ w = ε} (toLex <| γ ∘ ·) ⟨1, by simp⟩; have (a b) (e : ε a = ε b ∧ l a ≤ l b) := (h.2 (w * _) (by simp_all [apply_swap_eq_self])).not_gt ∘ Pi.lex_desc (f := γ ∘ w) e.2; use w.sign, γ ∘ w - l.lC Eq; simp_all [lC, ← mul_assoc, ← cast_mul]; intros; grw [sub_add, ← cast_card_sdiff, card_le_card_of_injOn (γ ∘ w), card_Ico_of_le, sub_sub_cancel] <;> (try intro) <;> grind [w.injective]
end Orbital
end
end
section
open Finset Complex Equiv HCParam Matrix
variable {n} [Fintype n] {ε} {l ν : @HCParam n ε} (k : maxCompactU ε)
noncomputable def HCParam.kTypeChar (ν : HCParam ε) : C(maxCompactU ε, ℂ) := ⟨fun g ↦ (∫ y, weightMinors ν (y⁻¹ * g * y).1 ∂haarK ε) / ν.kTypeNormSq, (haarK ε).restrict_univ ▸ (continuous_parametric_integral_of_continuous (by fun_prop (disch := simp)) isCompact_univ).div_const _⟩
attribute [local simp] kTypeChar BlockTriangular blockDiagonal'_apply toBilin'_apply' toSquareBlock_def Orbital.tE Units.smul_def blockHom mem_maxCompactU mem_blockDiagAlg weylRep diagTorus zpow_add₀
lemma Orbital.eMB [DecidableEq ℤˣ] (g : ∀ _, Matrix _ _ ℂ) (h : ∀ τ, (g τ)ᴴ * g τ = 1) : let e := sigmaFiberEquiv ε; ∃ y : maxCompactU ε, y = reindex e e (blockDiagonal' g) ∧ y.1.1.1.toSquareBlock ε = g := by intro e; set y := reindex e e _; have m : y ∈ blockDiagAlg ε := (by aesop); use ⟨U.of IsHermInvolution.isUnit y ?_, mem_maxCompactU.2 m⟩, rfl, (by aesop : (y.submatrix e e).blockDiag' = _); simp [↓Commute.right_comm (m _ rfl), y, ← blockDiagonal'_mul, h, ← Pi.one_def]
lemma Orbital.wCK (hl : l.Injective) (hν : IsKDominant ε (-l) ν) : (∃ P, ∀ x, ν.kTypeChar (diagTorusK x) = tE x P) ∧ ∀ x, tE x (l.rP Eq) * ν.kTypeChar (diagTorusK x) = tE x (alternant ε (ν + l.lC Eq)) := by
  let := Classical.decEq ℤˣ; let m τ := {i // ε i = τ}; choose q hq using (exists_equiv_fin_lt_iff (n := m ·) hl.injOn.injective); let p τ := (q τ).symm.trans Fin.revPerm; let g τ := ((List.ofFn (ν <| q τ ·.rev)).getD · 0); let κ τ k := (g τ (k - 1) - g τ k).toNat; let e τ := g τ 0 - diagramWeight (rankAt m) κ (τ, 0)
  have h τ : ∀ i, ν i.1 = e τ + diagramWeight (rankAt m) κ (τ, p τ i) := (reindex_equiv (p τ).symm).1.2 fun ⟨k, o⟩ ↦ by
    simp [p, IsKDominant] at *; induction k with grind [hq τ (.rev ⟨_, o⟩) (.rev ⟨_ - 1, tsub_lt_of_lt o⟩)]
  let b : maxCompactU ε →* ∀ τ, GL (m τ) ℂ := .pi (blockHom ε · |>.comp (.mk' (⟨·, fun _ ↦ by aesop⟩) (by tauto))); let R := (weylRep κ e).comp b
  have ⟨v, w, M⟩ : ∃ v w, ∀ k, w ⬝ᵥ R k *ᵥ v = weightMinors ν k := ⟨_, _, fun k ↦ by
    erw [← dotProduct_mulVec (weylEval m κ _), weylRep_coeff_eq_prod_weightMinors p, weightMinors_eq_det_zpow_mul_prod (by simp) _ _ (neg_sum_abs_le_and_le_sum_abs _)]; simp_rw [← h, weightMinors_eq_det_zpow_mul_prod (b k _).det_ne_zero _ _ (neg_sum_abs_le_and_le_sum_abs ν ·), principalMinor_eq_det]; rw [prod_mul_distrib, prod_zpow, prod_comm]; clear * -
    congr! <;> rw [BlockTriangular.det_fintype (b := ε)] <;> aesop (add 1% congr)⟩
  have : Continuous (R ·) := by simp [R, b]; fun_prop (disch := try exact (.inl <| b · _ |>.det_ne_zero))
  have ⟨B, hB, hL⟩ := exists_intertwining_mean (haarK ε) R R (vecMulVec v w); obtain ⟨a, d, z, ⟨⟩⟩ := fun k ↦ hL (traceLinearMap .. ∘ₗ .mulRight ℂ (R k)), hL ((toBilin'.1.flip w).flip v), scalar_of_commute_schur
    (eMB · · |>.elim fun y e ↦ by simpa [R, ← e] using! hB y)
  simp [mul_vecMulVec, vecMulVec_mul, vecMulVec_mulVec, ← dotProduct_mulVec, ← map_mul, wUI, M, dotProduct_comm (_ *ᵥ _), conj_mul', ← smul_one_eq_diagonal, by simpa using M 1, -mem_maxCompactU] at a d; simp [a, ← (mod_cast d : ν.kTypeNormSq = z), ne_of_gt, R, b, diagonal_apply, Subtype.val_inj, ← diagonal.eq_1, ← prod_zpow, -UnitsInt.univ, rP, ↓tAl]; use ⟨∑ i : WeylIndexFam m κ, ∏ τ, ∏ a, .single (Pi.single a.1 (e τ + tableauWeight i τ a)) 1, by simp [mul_sum, schur_diagonal, -UnitsInt.univ]⟩, fun x ↦ ?_; have F τ j : ({b | τ = _ ∧ l b < l (q τ j)} : Finset n) = (Iio j).map (q τ).asEmbedding :=
    ext (by simp [← hq, reindex_equiv (q τ).symm, m]; tauto)
  rw [← Fintype.prod_fiberwise ε, Fintype.prod_congr, mul_rotate', weyl_character q, ← prod_mul_distrib, BlockTriangular.det_fintype (by simp; order)]; simp_rw
    [det_classical, ← fun τ ↦ det_submatrix_equiv_self (R := ℂ) (q τ), reindex_equiv (q _), ← det_mul_column]
  rcongr; simp [(q _ _).2, lC, F, h, pow_add, p, field]; simpa [reindex_equiv (q _), (q _ _).2, F, m, (det_classical _).symm.trans (det_vandermonde _)] using fun _ ↦ prod_comm' (by simp)
lemma Orbital.wDn (h : l.Injective) : l.rP Eq = alternant ε (l.lC Eq) := eTE (by simpa [kTypeNormSq, Pi.zero_def, ↓zero_add] using (wCK h (ν := 0) (by tauto)).2)
lemma Orbital.eCD : ∃ y x, y * diagTorusK x * y⁻¹ = k := have ⟨X, e, _⟩ := exists_expU_eq_maxCompactU k
 have h t : ((-Complex.I • X.1).toSquareBlock ε t).IsHermitian := by ext ⟨i⟩ ⟨j⟩; simpa [*, signMatrix, add_eq_zero_iff_eq_neg, field] using congr($(X.2) i j)
 (eMB _ (h · |>.eigenvectorUnitary.2.1)).imp fun _ m ↦ ⟨.exp ∘ _, by
  symm; ext : 3; simp [← e, exp_eq_exp_ℂ, ← Pi.exp_def, ← exp_diagonal, ← Matrix.exp_conj]; convert congr(NormedSpace.exp (Complex.I • (blockDiagonal' $(funext (h · |>.spectral_theorem))).reindexRingEquiv ℂ (sigmaFiberEquiv _))); simp_all [← ext_iff, sigmaFiberEquiv]; grind [Subtype.heq_iff_coe_eq, I_sq]
  simp [m, ↓maxCompactU.coe_inv, map_mul, ← diagonal_mul_diagonal, ← smul_eq_mul_diagonal]; rfl⟩
open ComplexConjugate GlModule InnerProductSpace MeasureTheory Norms.L2Operator
attribute [local simp] IsKHighest inner_sub_left mul_assoc ne_of_gt rep_apply_apply
variable {n : Type} [Fintype n] {ε : _} {ν : @HCParam n ε} {A} {l : HCParam ε}
lemma Orbital.iMK {f : maxCompactU ε → _} (hf : Continuous f := by fun_prop) : ∫ k, f k * conj (ν.kTypeChar k) ∂haarK ε = ∫ y, (∫ k, conj (weightMinors ν k.1) * f (y * k * y⁻¹) ∂haarK ε) / ν.kTypeNormSq ∂haarK ε := by simpa [kTypeChar, ← integral_conj, integral_div, mul_div, mul_comm] using (integral_skew_product (fun y ↦ ((measurePreserving_mul_left _ y⁻¹).mul_right _ y).2) (integrable_of_compactSpace (f := (fun y k ↦ f (y * k * y⁻¹) * conj (weightMinors ν k)).uncurry))).2
lemma Orbital.iCK : ∫ k, 1 * conj (ν.kTypeChar k) ∂haarK ε = ite (ν = 0) 1 0 := .trans iMK (by split_ifs with h <;> simp [*, kTypeNormSq, Pi.zero_def, integral_conj]; contrapose! h; exact AddMonoidAlgebra.single_left_injective h (eTE fun t ↦ by simpa [tE, diagTorus, h] using (integral_mul_left_eq_self (μ := haarK ε) (weightMinors ν ·) (diagTorusK t))))
lemma Orbital.eKM [Nonempty n] [hg : l.HasLargeGap A] (hν : IsKDominant ε (-l) ν) : let R (g : USign ε) := (∫ k : maxCompactU ε, l.dsCoeff (g⁻¹ * k * g :) * conj (ν.kTypeChar k) ∂haarK ε); Integrable R ∧ ∃ m : ℕ, l.formalDegree * ∫ g, R g = m ∧ (ν = l.lowestKType → m = 1) ∧ (m ≠ 0 → ν - l.lowestKType ∈ l.rootCone) := by
  obtain ⟨⟨d, k, j⟩, _, hw, hi, s, hs⟩ := hg.toL2_spec, (@iUR _ _ ε).1, isKHighest_dsGenerator hg, hg.isUnitaryCasimirGe_dsAction.1, exists_nat_ge (l.casimirKValue ν - l.casimirKValue l.lowestKType : ℝ); have := hw.finite_filtration hi; let W := l.dsAction.filtration ε dsGenerator
  let V := .ofLinearComb {v | l.IsKHighest dsAction ν v} ⟨0, by simp⟩ (by
    simp +contextual [smul_smul, mul_comm]) ⊓ W s; let b := stdOrthonormalBasis ℂ V
  have key x := by
    let T := innerSL ℂ (hg.toL2 dsGenerator) ∘L rightRegularL2 x; let φ := strongIntegral (haarK ε) fun k ↦ conj (weightMinors ν k) • T ∘L rightRegularL2 k; have F : ∀ w, φ w = _ := strongIntegral_apply _ _ (fun _ ↦ by simpa using integrable_of_compactSpace); let z t := ((φ.1 ∘ₗ hg.toL2).domRestrict (W t)).adjoint 1; have H {s t y} hy (o : s ≤ t) : ⟪(z t).1, y⟫_ℂ = φ (hg.toL2 y) := (LinearMap.adjoint_inner_left _ (⟨y, filtration_mono o hy⟩ : W t) 1).trans (by simp)
    have hZ t : l.IsKHighest _ ν (z t).1 := .of_E_eq_smul fun f c e h ↦ Subtype.mk.inj (ext_inner_right ℂ (x := ⟨_, E_mem_filtration (z t).2 e⟩) (y := (_ : ℂ) • z t) fun ⟨y, hy⟩ ↦ by
      let Φ b := ∫ k, weightMinors ν (b * k⁻¹) * y.1.1 (x * k) ∂haarK ε; have a : HasFDerivAt Φ _ 1 := (IsAnalyticFamily.analyticAt_integral _ (by apply IsAnalyticFamily.of_analyticAt (.prodMk ..) (fun (b, p, q) ↦ weightMinors ν (b * p) * q) <;> fun_prop (disch := simp))).differentiableAt.hasFDerivAt; have u (j : maxCompactU ε) : φ (rightRegularL2 j (hg.toL2 y)) = Φ j := .trans (by simp [F, ← wUI, T, -map_mul, k]) (integral_mul_right_eq_self _ j)
      simpa +contextual [hi.1 f, e, H (E_mem_filtration hy e.symm), ↓inner_smul_left, H hy, @eq_comm _ c, apply_ite conj, by simpa using u 1] using (fderiv_eq_on_blockDiagAlg a (φ.1 ∘ₗ hg.toL2 ∘ₗ dsAction.ρ.flip y) (fun Y h ↦ by simpa [u ⟨_, h _⟩] using ((d Y y).map_clm φ).deriv) (by clear * - e; grind [mem_blockDiagAlg]) ).symm.trans <| fBE ε a (o := -l) (by simpa) e.symm id (by
        simp +contextual [Φ, hν.weightMinors_oppBorel_mul hg.neg.1]))
    simpa [← congr(hg.toL2 $(b.sum_repr' ⟨_, hZ s, (z s).2⟩)), H (b _).2.2, ← mul_sum, F, T, -map_mul, ↓fun i ↦ (F _).trans ((b i).2.1.integral_conj_weightMinors_smul iUR d hν T), k, ← inner_conj_symm (rightRegularL2 x _), ← inv_mul_eq_iff_eq_mul₀, by
      simpa using iUR.form_apply_eq_form_inv_apply x⁻¹] using hw.coeffMap_eq_zero hi (d.isCoeffMap (φ - innerSL ℂ (hg.toL2 (z s)))) (fun g a ↦ (φ - _).le_opNorm_of_le (by simp [rightRegularL2]; rfl)) (fun t a o ↦ by simpa [H o] using! (congrArg conj (mem_orthogonal_filtration_of_casimirK s hi hw
      (z (s ⊔ t) - z s) (by simp [(hZ _).casimirK_eq_smul, smul_sub]) hs (by simp +contextual [Submodule.mem_orthogonal', @H s]) t a o))) x⁻¹
  have I y := (by simpa [Pi.mul_def] using (hg.memLp y).integrable_mul (hg.memLp y).star); have M := by simpa [← mul_sum, ← integral_finsetSum, I, show ∀ a, ‖hg.toL2 (b a)‖ = 1 from b.norm_eq_one] using congr(∑ i, $(j (b i) (b i) 1))
  intro R; exact (funext fun g ↦ .trans iMK (by simp [← key, div_eq_inv_mul]) : R = _).symm.rec ((integral_skew_product (Measure.map_mul_right_inv_eq_self _ ·.1⁻¹) ((integrable_finsetSum ⊤ fun j _ ↦ I (b j)).comp_snd (haarK ε))).imp_right fun t ↦ ⟨_, .trans (by simp [↓t]) M.symm,
    have N q x := by simpa [↓dsCoeff_inv] using integral_conj_weightMinors_mul_dsCoeff hg x x⁻¹ hν q
    ⟨by rintro rfl; simpa [← key, N, by simpa using dsCoeff_schur_orthogonality hg 1 1] using M, Function.mtr fun q ↦ by
    simpa [← key, N, q, (mt (by simp [·, rootCone]) q : ν ≠ l.lowestKType)] using M⟩⟩)
end
section
seal Finset.univ Finset.sum Finset.prod
open Matrix MeasureTheory Complex ComplexOrder Norms.L2Operator LinearMap Finset U
variable {n} [Fintype n] {o : n → ℤ} (ho : o.Injective) (ε : n → _) {b c}
def oO o := {y | ∃ g : USign ε, ∃ b, IsBorelMatrix o b ∧ y = g.1.1 * b}
include ho
lemma IsBorelMatrix.uEM {g g' : USign ε} (hb : IsBorelMatrix o b) (hc : IsBorelMatrix o c) : g * b = g' * c ∧ (∀ i, 0 < c i i / b i i) → g = g' := by
 obtain ⟨t, rfl⟩ := mul_left_surjective g' g; simp [mul_assoc]; rintro rfl p
 cases (by simpa [hb.2] using hc.mul hb.inv :).exists_eq_diagonal_exp ho; ext : 2; simpa [funext_iff, hb.diag_ne_zero, *] using (eq_coe_norm_of_nonneg <| p · |>.le)
lemma aDL (h : IsBorelMatrix o b) (p : ∀ i, 0 < b i i) ε' :
  |(skewCoords ∘ₗ mulLeft ℝ (signMatrix ε) ∘ₗ lowerLiePart ε 1 o ∘ₗ mulLeftRight ℝ (b, b⁻¹) ∘ₗ mulLeft ℝ (signMatrix ε') ∘ₗ skewOfReal).det| = ‖diagChar (twoRho o ⊤) b‖ ^ 2 := by
  let := LinearOrder.lift' (fun (i, j) ↦ [|o i - o j|, o i, o j]) (by aesop_cat); choose d u e using (RCLike.pos_iff_exists_ofReal.1 <| p ·); let x i j := ε i * ε' i * d i / d j; rw [← det_toMatrix (stdBasis ..)]; show ‖(?T : Matrix (n × n) _ ℝ).det‖ = _; have z i j (y : Matrix n n ℂ) (H : ∀ k l, o i - o j < o k - o l → y k l = 0) : (b * y * b⁻¹) i j = b i i * y i j / b j j := (by simp [entrywise, sum_mul, ← sum_product']; rw [sum_eq_single (j, i)] <;> grind [h.inv, h.inv_apply_diag, IsBorelMatrix, BlockTriangular]); have E p q (H : q ≤ p) : ?T p q = ite (p = q) (ite (o p.1 < o p.2) (x p.2 p.1) (x p.1 p.2)) 0 :=
    by simp [toMatrix_apply, stdBasis, lowerLiePart, skewCoords, signMatrix]; split_ifs <;> (try lia) <;> (repeat rw [z]) <;> simp [skewOfReal, ← e, ite_apply] <;> grind [ofReal_zero, H.imp_right List.head_le_of_lt, abs_unit_intCast (α := ℝ) (ε p.1)]
  rw [det_of_isUpperTriangular fun _ ↦ by grind]; simp [E, ← e, x, sq, diagChar, twoRho, u, ne_of_gt, zpow_sub₀, ← prod_const, prod_filter, apply_ite norm, ← prod_div_distrib, Fintype.prod_prod_type]; nth_rw 2 [prod_comm]; simp_rw [← prod_mul_distrib]; rcongr; grind
lemma oOL ε' : IsOpen {g : USign ε' | ↑g ∈ oO ε o} ∧ ∀ f, (∀ (y : GL n ℂ) b, IsBorelMatrix o b → f (y * b) = ‖diagChar (twoRho o ⊤) b‖ ^ 2 * f y) → ∫⁻ g : USign ε', (oO ε o).indicator (.ofReal ∘ f) g ≤ ∫⁻ g : USign ε, (oO ε' o).indicator (.ofReal ∘ f) g := by
 have ⟨ψ, ⟨d, z⟩, H⟩ := exists_borel_chart 1 o (lowerLiePart ε 1 o) hasStrictFDerivAt_exp_zero
  (by simp [lowerLiePart, signMatrix]; grind)
 choose! Φ B P Q e i using (fun _ ⟨g, b, h, e⟩ ↦ let t := diagTorus ε fun i ↦ ⟨‖b i i‖ / b i i, by
  simp [Submonoid.unitSphere, h.diag_ne_zero ho]⟩; ⟨g * t⁻¹, t * b, .mul ⟨by simp [t, diagTorus],
  by simp⟩ h, by simp [t, diagTorus, h.diag_ne_zero ho], by simp [e, mul_assoc, h.2]⟩ : ∀ y ∈ oO ε o, ∃ g : USign ε, ∃ b, IsBorelMatrix o b ∧ (∀ i, 0 < b i i) ∧ g * b = y ∧ y * b⁻¹ = g)
 have E y h := have u := P y h; let A := ContinuousLinearMap.mulLeftRight ℝ _ (Φ y).1.1⁻¹ (B y)⁻¹
   have a : A y = 1 := (by simp_all [A, mul_assoc]); (Filter.eventually_and.1 (((A.cont.tendsto' _ _ a).eventually (.and (.mp (by simp) H) (d.continuousAt.const_add 1 (IsAccretive.setOf_mem_nhds (by simp [z, PosDef.one.isAccretive]))))).mono fun x ⟨⟨p, _, q⟩, k⟩ ↦ have r : x = (Φ y * expU ⟨_, lowerLiePart_mem_unitaryLie ..⟩).1.1 * _ := (by simpa [mul_assoc, A, u.2] using congr(Φ y * $q * B y)); (fun m ↦ And.intro m congr($((P x m).uEM ho ε (p.mul u) ⟨(e x m).trans r, fun i ↦ by simpa [↓p.mul_apply_diag ho u, Q, h, m, lowerLiePart, lt_def, ← two_mul, signMatrix, mul_right_comm, ← Int.cast_mul] using k.diag_pos⟩).1.1)) ⟨_, _, p.mul u, r⟩)).imp_right (((a ▸ HasFDerivAt.comp 1 (by simpa [z] using hasFDerivAt_exp_zero) ((lowerLiePart ..).hasFDerivAt.comp _ d)).comp _ A.hasFDerivAt).const_mul _).congr_of_eventuallyEq
 refine (fun O ↦ ⟨O, fun F hB ↦ have S := mCC O.measurableSet; ?_⟩)
  (.preimage_of_continuous (isOpen_iff_mem_nhds.2 (E · · |>.1)))
 have ⟨t, h⟩ := (Haar.lintegral_chart_rotate_le (.refl ..) (.id _) (Φ := (Φ <| cayleyChart (signMatrix ε') ·)) (S.inter (by measurability)) (fun _ ⟨p, u⟩ _ ⟨q, v⟩ _ ↦ cayleyChart_injOn u v ((P _ p).inv.uEM ho ε' (P _ q).inv (by simp_all [IsBorelMatrix.inv_apply_diag ho]))) fun y ⟨p, q⟩ ↦ have ⟨c, j⟩ := abs_det_logDerivU_cayleyChart q; .imp_right (.trans · ((abs_mul ..).trans (congrArg₂ _ (aDL ho ε (P _ p) (Q _ p) ε') j))) ?_).exists; grw [lintegral_eq_cayleyChart, ← lintegral_mul_left_eq_self _ (circleScalar t)⁻¹, ← h, ← setLIntegral_indicator S]; gcongr; exact Set.le_indicator_apply (fun p ↦ by simp_all [(oO ε' o).indicator_of_mem ⟨_, _, (P _ p).inv, (i _ p).symm⟩, mul_left_comm, e _ p ▸ hB .., mul_assoc, ← mul_div]) (by aesop); have D := (E _ p).2.comp y c.hasFDerivAt; use ⟨_, D⟩; erw [← map_mul, logDerivU, D.fderiv]; congr 2 with; simp [conjTranspose_logDerivU c, ← congr($(i _ p)⁻¹), (P _ p).2, inv_mat]; simp [logDerivU, ← mul_assoc, mem_U.1]
lemma iHO {F : _ → ℂ} (hB : ∀ (y : GL n ℂ) b, IsBorelMatrix o b → F (y * b) = ‖diagChar (twoRho o ⊤) b‖ ^ 2 * F y) (c : Continuous (F · : GL n ℂ → ℂ)) : Integrable (F · : USign ε → ℂ) ∧ ∫ g : USign ε, F g = (∫ k : USign 1, F k.1.1) - ∫ k in {k : USign 1 | k.1.1 ∈ oO ε o}ᶜ, F k := by
  have ⟨S, L⟩ := (oOL ho ε 1).imp_left (·.measurableSet); have K := integrable_of_compactSpace (X := USign 1) (ν := volume) (c.comp' continuous_subtype_val); have E f h := (((oOL ho ..).2 f h).antisymm (L f h)).trans
    (lintegral_indicator S _)
  simp [fun g : USign ε ↦ (exists_orthonormal_mul o ⟨_, g.1.4⟩).elim (b := ↑g ∈ oO 1 o) (⟨⟨g * ·, by simp_all [U]⟩, _, .inv ⟨·.1, by simp⟩, by simp⟩)] at E; refine (fun i ↦ ⟨i, (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ ↦ ?_⟩)
    ⟨c.comp_aestronglyMeasurable (by fun_prop), by simpa [E (‖F ·‖) (by aesop), ← ofReal_norm, HasFiniteIntegral] using K.restrict.2⟩; simp [← φ.integral_comp_comm, φ.integrable_comp, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, K.restrict, setIntegral_compl, *]
  erw [E (φ ∘ F), E (-φ ∘ F)] <;> simp_all [← ofReal_pow, ← real_smul]
omit ho
open Nat Orbital AddCircle HCParam
lemma wDF {n} [Fintype n] {l : @HCParam n 1} {h} (hg : l.HasGap h) : l.lowestKType.kTypeNormSq⁻¹ = weylDimensionPoly l := by
  have L (a : HCParam 1) := tendsto_finsetProd ⊤ fun i _ ↦ tendsto_finsetProd {j | l j < l i} fun j
    _ ↦ ((hasDerivAt_fourier 1 (a i) 0).sub (hasDerivAt_fourier 1 (a j) 0)).tendsto_slope_zero
  have E (t : ℝ) := ((wCK hg.1 hg.isKDominant_lowestKType).2 (@toCircle 1 t ^ l.lC Eq ·)).trans (by rw [tAl, ← det_transpose]; simp [wDn
    hg.1, tAl, transpose, zpow_comm] : _ = Orbital.tE (@toCircle 1 t ^ (l.lowestKType + l.lC Eq) ·) (l.rP Eq))
  simp [rP, Orbital.tE, toCircle_zsmul, ← mul_sub] at E L; obtain ⟨t, k, e, he⟩ := tendsto_nhds_unique (((L _).mul (by fun_prop : ContinuousWithinAt ..) ).congr ((mul_assoc ..).trans <| congrArg _ <| E ·)) (L _), fun a ↦ congr(($(two_mul_lowestKType hg a) : ℂ) + $(card_lt_add_card_gt_add_one hg.1 a)), exists_equiv_fin_lt_iff hg.1; simp [kTypeChar, diagTorus, prod_eq_zero_iff, mul_assoc, lC, twoRho] at t k; rw [weylDimensionPoly, eq_div_iff (by positivity), ← ofReal_inj, mul_comm]; push_cast; convert t <;> try grind
  simp_rw [← map_univ_equiv e, filter_map, prod_map, prod_range, ← descFactorial_self, descFactorial_eq_prod_range, ← prod_range_natCast_sub]; simp [he, filter_gt_eq_Iio, ← Iio_eq_range, ← Fin.map_valEmbedding_Iio]
variable {n : _} [Fintype n] (h : ℕ) (u : GL n ℂ) (l f : n → ℤ)
@[simp] noncomputable abbrev tPD := u.1ᴴ * diagonal ((2 : ℂ) ^ f ·) * u
attribute [local simp] zpow_nonneg prod_eq_zero_iff PosSemidef.conjTranspose_mul_mul_same
lemma lWM i j m (hu : uᴴ = u.1⁻¹) (k : ∀ a c, l c < l a → f a + |m| ≤ f c) (H : h ≤ |l i - l j|) : ‖weightMinors l (tPD 1 f)‖ * (‖u i j‖ ^ 2 * 2 ^ m) ^ h ≤ ‖weightMinors l (tPD u f)‖ := by
 have P {f g p} [DecidablePred p] (h : f ≤ g) : ‖principalMinor (tPD u f) p‖ ≤ ‖principalMinor (tPD u g) p‖ := norm_det_le_norm_det_of_posSemidef (.submatrix (by simp) _) (.submatrix (M := tPD u g - tPD u f) (by simp [← sub_mul, ← mul_sub, h _]) _); have V f : (tPD u f)⁻¹ = tPD u (-f) := inv_eq_left_inv (by simp [mul_assoc, hu, ← mul_assoc (diagonal _)]); wlog H : l j ≤ l i generalizing l f; convert V f ▸ this (-l) _; simp +contextual [↓← weightMinors_neg, add_comm, k]; grind; obtain ⟨⟨a, A⟩, b, B⟩ := @Finite.exists_min _ _ _ ⟨i⟩ _ l, Finite.exists_le l; rw [show h = #(Ioc (l a) b ∩ Ioc (l i - h) (l i)) by simp [Ioc_inter_Ioc]; grind, ← prod_const]; simp [weightMinors_eq_det_zpow_mul_prod _ (l a) b, ↓← prod_ite_mem, ← prod_mul_distrib, *, mul_zpow, field, -mul_ite]; gcongr with t; have ⟨c, _⟩ := exists_min_image {k | l k < t} f ⟨a, by grind⟩; let q k := t ∈ Ioc (l i - h) (l i) ∧ k = j; have := (k · c); grw [(?_ : ite .. ≤ ‖principalMinor (tPD 1 (f c)) q‖ * ‖principalMinor (tPD u (f ⊓ f c))⁻¹ q‖), jacobi_complementary_minor (by simp), norm_div, fischer_inequality (r := (¬q ·)) (by simp) (fun i ↦ l i < t ∧ ¬q i) (t ≤ l ·), P inf_le_right, P inf_le_left]; simp [principalMinor_eq_det, ← diagonal_one, ← smul_eq_mul_diagonal, hu, ← diagonal_smul, field, sub_ite, ← prod_mul_distrib, apply_ite norm]; rw [mul_comm, prod_congr rfl]; any_goals grind
 nth_grw 3 [← re_le_norm]; split <;> simp [↓V, q, ‹_›, principalMinor.eq_1, diagonal, mul_apply, default, toSquareBlockProp, mul_right_comm _ _⁻¹, conj_mul', ↓re_eq_norm.2, sq]; grw [← single_le_sum (by bound) (mem_univ i)]; simp [field, mul_assoc, ← zpow_add₀]; gcongr <;> grind
end
open Matrix MeasureTheory Finset AddMonoidAlgebra Equiv ConjAct InnerProductSpace ContinuousMap CStarRing Norms.L2Operator Fintype Metric Int HCParam
section
attribute [local simp low] Finsupp.sum mul_sum inner_sum inner_smul_left inner_smul_right inner_toLp prod_ite integral_apply lift_apply'
variable {n} [Fintype n] {ε} (l : @HCParam n ε)
def Orbital.CSM a (D P : ℂ[_]) := ∃ t : _ → ℂ, (∀ γ, P.1 γ = D.1.sum fun β c ↦ c * t (-β + γ)) ∧ t a = 1 ∧ ∀ γ, t γ ≠ 0 → ∃ μ, (alternant ε μ).1 γ ≠ 0 ∧ μ - a ∈ l.rootCone
lemma Orbital.eLO [Nonempty n] (hg : l.HasLargeGap (10 * card n ^ 5)) : let δ := l.lC Eq
  let Vc := l.rP Eq; let N := 4 * card n ^ 2 + 1; let D := (-l).rP Ne ^ N
      ∃ P, WA ε P.1 ∧ (∀ x, tE x P = tE x (Vc * D) * (l.formalDegree * ∫ g, l.dsCoeff (g⁻¹ * diagTorus ε x * g :))) ∧ CSM l (l.lowestKType + δ) D P := by
  intro δ Vc N D; let c (y : maxCompactU ε) := mk (y * diagTorusK · * y⁻¹); let W := {w : Perm n // ε ∘ w = ε}; let ψ := (mk fun p : _ × maxCompactU ε ↦ l.dsCoeffSmooth.1 (p.1⁻¹ * p.2 * p.1)).curry; choose s ν hν hs using eSK hg.1; choose b v bv using eCD (ε := ε); have ac {μ} h γ := aCK hg.1 h (hν γ) ▸ hs γ
    (alternant ε (μ + δ)).1 wAl
  have z {μ} h := aCK hg.1 h h ▸ (ac h (μ + δ)).symm; simp [ite_eq_iff] at z; let X γ := (s γ : ℂ) • (toHCParam ε (ν γ)).kTypeChar; have : Nonempty W := ⟨1, rfl⟩
  choose Y he hA using fun γ ↦ ((wCK hg.1 (hν γ)).elim fun ⟨P, h⟩ k ↦ ⟨s γ * P, fun y x ↦ by simp [X, c, ← h]; exact .inl congr($(.trans (by group) (integral_mul_left_eq_self _
    y⁻¹)) / _), eTE fun x ↦ (hs γ (tE x <| alternant ε ·) (by simp +contextual
    [WA, tAl, ← det_permute', submatrix, funext_iff])).trans
    (by simp [← k, h, field])⟩ : ∃ P, (∀ y x, X γ (c y x) = tE x P) ∧ alternant ε γ = Vc * P)
  let e (i : Subtype (IsKDominant ε (-l))) := X (i + δ); let Φ p := (coeff p).lift _ ℂ _ X; let L := toLp (E := ℂ) 2 (haarK ε) ℂ
  have hX p x : tE x (Vc * p.1.lift _ ℂ _ Y) = ∑ w : W, w.1.sign * tE (x ∘ w.1) p := by simp [← hA, tAl, det_apply', Fintype.prod_ite_zero, ← sum_filter]; simp [tE, mul_left_comm]; rw [sum_comm, sum_subtype]; simp [funext_iff]
  have key p q (H : ∀ x, _) y x : Φ p (c y x) = tE x q := .trans (by simp [Φ, *])
    congr(tE x $(mul_left_cancel₀ (by simpa [*, ·] using ac (hν 0) (ν 0 + δ)) (eTE fun x ↦ (hX p x).trans (H x))))
  have av p := key (Vc * p) (∑ w : W, ⟨p.1.equivMapDomain (w.1.arrowCongr 1)⟩) (by simp [Vc, wDn hg.1, ← tCP, (tCM _).2
    (wAl _ (_ : W).2), ← mul_assoc, ← cast_mul])
  have pair {d D} (hd : ∀ y x, d (c y x) = tE x D) γ ψ : ⟪L (X γ), L (d * ψ)⟫_ℂ = D.1.sum fun β a ↦ a * ⟪L (X (-β + γ)), L ψ⟫_ℂ := by let S : ℂ[n → ℤ] := D.1.sum fun β a ↦ .single (-β) (star a); have hS x : tE x S = star (tE x D) := (by simp [S, tE, ← Circle.coe_inv_eq_conj]); trans ⟪L (Φ (S * .single γ 1)), L ψ⟫_ℂ; simp [L]; congr with k; erw [← bv k, key _ (S * Y γ) fun x ↦ ?_, hd, he]; simp [*, field]; simp [mul_left_comm Vc, by simpa using hX (.single γ 1), hS, aPC _ (_ : W).2 hd]; ac_rfl; simp [Φ, S, sum_mul, sum_inner, -Finsupp.lift_apply]; simp [-Finsupp.sum]
  have xe γ μ : ⟪L (X γ), L (X μ)⟫_ℂ = (alternant ε μ).1 γ := by simpa [hA μ, ↓mul_comm Vc, X, L, Vc, wDn hg.1, coeff_mul_apply_left, δ, zero_add δ ▸ ac (by tauto), ← @iCK _ _ ε] using pair (he μ) γ 1
  have o : Orthonormal ℂ (L ∘ e) := by simp +contextual [orthonormal_iff_ite, e, xe, ac, z]
  have hd y x : _ = tE x D := (av ((card W : ℂ)⁻¹ • D) y x).trans (by
    simp [D, ↓map_sum, ↓← tCP, tRNcc hg.neg.1 (_ : W).2]); generalize Φ _ = d at hd
  have hI : Integrable (d * ψ ·) := .mono' (.const_mul (integral_decay_le _ .monoidHom_id (c := 2 * N) (by omega) 1).1 (2 ^ (#(oppositePairs ε) * N * 2))) (by fun_prop) (.of_forall fun x ↦ (norm_le_of_nonempty _).2 fun k ↦ by
    let u := (b k)⁻¹ * x; let g := u⁻¹ * diagTorus ε (v k) * u; let φ := (MulSemiringAction.toAlgHom ℂ (Matrix n n ℂ) (toConjAct u.1⁻¹)).comp (diagonalAlgHom ℂ)
    have p s : ‖φ (∏ i ∈ s, ((v k · : n → ℂ) - (v k i).1 • 1))‖ ≤ (‖g.1.1‖ + ‖g.1.1‖) ^ #s := by induction s using cons_induction <;> simp [*, show φ _ = g by rfl, pow_succ', norm_mul_le_of_le, norm_sub_le_of_le, U.one_le_norm]
    erw [← bv k, norm_mul, hd]; simp [D, ψ, pow_mul, tRNc hg.neg.1, -norm_prod]
    grw [show _ * _ = g.1.1 by simp [g, u, mul_assoc], norm_dsCoeff_le_pow hg (c := #(oppositePairs
      ε) * N), (le_div_iff₀' (by simp)).2 (?_ : ‖principalMinor (φ _) (ε · = 1)‖ ≥ (‖u.1.1‖ / 2) ^ 2 * ‖_‖), norm_principalMinor_le_pow, Fintype.card_subtype, p {i | ε i ≠ 1}]
    · simp [div_pow, field, oppositePairs, u, norm_mem_unitary_mul, Unitary.mem_iff, star, ← maxCompactU.coe_inv, conjTranspose_nonsing_inv]; ring; rfl
    · grw [sq_le_norm_det_blockDiagPart]; erw [norm_det_blockDiagPart 1, principalMinor_mul, principalMinor_mul, U.principalMinor_coe_inv] <;> simp [principalMinor_eq_det, oppositePairs, prod_product, ← diagonal_one, sub_ite, diagonal_apply, prod_eq_zero_iff] <;> clear * - <;> grind
    grw [card_le_univ]; simp [N, field]; nlinarith [one_le_cast_card n])
  let h := l.formalDegree • ∫ g, d * ψ g
  have hh y x : h (c y x) = h (c 1 x) := by simp [h, *, ← integral_mul_left_eq_self (ψ · (c y x)) y.1]; simp [c, ψ, mul_assoc]
  choose hm m hm' _ _ using (by simpa using eKM <| hν ·); let t γ : ℂ := s γ * m γ
  have ha γ : ⟪L (X γ), L h⟫_ℂ = D.1.sum fun β c ↦ c * t (-β + γ) := by simp [h, inner_smul_right_eq_smul, ← by simpa [pair hd] using (innerSL ℂ (L (X γ)) ∘L L).integral_comp_comm hI]; simp [X, L, t, ψ, ← hm', mul_left_comm (l.formalDegree : ℂ), integral_finsetSum, ((hm _).const_mul _).const_mul]
  have ⟨Z, hZ⟩ : ∃ Z, mapRingHom _ (castRingHom ℂ) Z = D := ⟨(∏ a, ∏ b ∈ _, (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1)) ^ N, by simp; rfl⟩
  let a := Finsupp.ofSupportFinite (⟪L <| e ·, L h⟫_ℂ) (((o.inner_products_summable (L h) ).tendsto_cofinite_zero.eventually_lt_const one_pos).subset fun i ↦ by
    simp [e, ha, ← hZ, t]; exact_mod_cast one_le_abs)
  let A := innerSLFlip ℂ (L (h - a.lift _ ℂ _ e)) ∘SL L; have k i : A (e i) = 0 := by simpa [A] using! (o.inner_right_finsupp a i).symm.trans (inner_sum ..)
  have eq := toLp_injective _ (L.sub_mem_ker_iff.1 (inner_self_eq_zero.1 (sub_mem ((mem_of_closed' A.isClosed_ker).2 fun r q ↦ (dTE.exists_dist_lt (h.comp (c 1)) q).elim fun p o ↦ ⟨Φ (Vc * (card W : ℝ)⁻¹ • p), by clear * - k z hν; simp_all [Φ, X, e], (dist_lt_iff q).2 (by
    erw [← bv ·, av, hh, dist_comm]; simp_rw [map_sum, ← tCP, AlgHom.map_smul_of_tower]; exact (convex_ball ..).sum_mem (by simp) (by simp) fun w _ ↦ aPC _ w.2 hh ▸ mem_ball'.2 ((dist_lt_iff q).1 o _))⟩)
    (by simp [k]))))
  refine ⟨a.lift _ ℂ _ (alternant ε <| ·.1 + δ), by simp +contextual [WA, wAl _, mul_left_comm (a _)], fun x ↦ ?_, t, by simp [↓← ha, e, *], by simp [t, hg.isKDominant_lowestKType, *], fun γ ↦ .intro (ν γ + δ) ∘ by simp +contextual [t, ↓ac, *]⟩; trans tE x Vc * h (c 1 x); simp [e, *]; ac_rfl; simp [h, hI, hd]; simp [c, ψ, field]
open Complex ComplexOrder Filter
attribute [local simp] prod_eq_zero_iff Finsupp.sum IsHermInvolution.det_ne_zero IsAccretive.det_ne_zero integral_div mul_zpow zpow_add₀ _root_.zpow_mul zpow_sub₀ zpow_sum_of_ne_zero
variable {n : Type} [Fintype n] {ε : n → _} {l : HCParam ε} {h : ℕ}
noncomputable def Orbital.oOI (l : HCParam ε) A := ∫ k in {k : USign 1 | k.1.1 ∈ oO ε l}ᶜ, weightMinors (-l.compactForm.lowestKType) (k.1.1ᴴ * signMatrix ε * k) / weightMinors (-paramAddRho l) (k.1.1ᴴ * A * k)
lemma Orbital.oCS (hg : l.HasGap h) : ∃ σ, ‖σ‖ = 1 ∧ ∀ x, let A := signMatrix ε * diagTorus ε x; A.IsAccretive → σ * ∫ g, l.dsCoeff (g⁻¹ * diagTorus ε x * g :) = l.compactForm.lowestKType.kTypeNormSq * l.compactForm.lowestKType.kTypeChar (diagTorusK x) - oOI l A :=
  have K := by simpa [lowestKType_neg hg.signs_one] using hg.signs_one.neg.isKDominant_lowestKType
  ⟨weightMinors (-l.compactForm.lowestKType - l.lowestKType) (signMatrix ε), by simp [signMatrix], by
  intro x A hA
  have ⟨i, O⟩ := iHO hg.1 ε (F := fun y ↦ weightMinors (-l.compactForm.lowestKType) (yᴴ * signMatrix ε * y) / weightMinors (-paramAddRho l) (yᴴ * A * y)) (fun y b hb ↦ by simp [← mul_assoc _ y.1, mul_assoc bᴴ, hb.2, hb.diag_ne_zero hg.1, lowestKType, twoRho, *, IsKDominant.weightMinors_oppBorel_mul (ε := 1) hg.1, IsKDominant.weightMinors_mul_borel (ε := 1) hg.1, hg.iKN, diagChar,
    field,
    show IsBorelMatrix (-l) bᴴ by simp_all [IsBorelMatrix, BlockTriangular], ↓← conj_mul']) ?_
  rw [← ((maxCompactU 1).subtype.measurePreserving (by fun_prop) (μ := haarK 1) (fun _ ↦ by
    simp [mem_maxCompactU]) (by simp)).hasLaw.integral_comp (integrable_of_compactSpace ?_).1] at O
  erw [← integral_const_mul, ContinuousMap.coe_mk, congrArg (integral _) (funext fun y : @maxCompactU n _ 1 ↦ (?_ : _ = l.compactForm.flenstedJensen (y⁻¹ * (signMatrix ε)⁻¹ * y) (y⁻¹ * A * y))), integral_div, integral_integral (integrable_of_compactSpace ?_), ← (((measurePreserving_mul_prod_inv ..).comp Measure.measurePreserving_swap).fubini (integrable_of_compactSpace ?_)).2]
  any_goals fun_prop (disch := simp (disch := simp [*]) [maxCompactU.coe_inv])
  convert! (integral_skew_product (map_mul_right_eq_self _ ·.1) (integrable_of_compactSpace (ν := haarK ε) (f := (ofReal <| ‖weightMinors l.lowestKType ·‖ ^ 2 / l.lowestKType.kTypeNormSq)).mul_prod i)).2 with _ g; rw [dsCoeff_eq_flenstedJensen hg (mem_blockDiagAlg_iff_commute.2 rfl), flenstedJensen, ← integral_div, ← integral_const_mul]; congr with k; simp [↓mem_U.1 (g * k).2, U.inv_mat, ↓A, mul_assoc, signMatrix, field, mul_conj']; simpa [mul_assoc, U.inv_mat, A] using hA.conjTranspose_mul_mul (k := g); have H a h := (isHolOfWeight_weightMinors hg.1 a⁻¹ (fun _ ↦ K) h).integral_mul_conj_weightMinors hg.1; simp_all [-ofReal_pow, integral_complex_ofReal, oOI, wUI, kTypeNormSq, mul_assoc, ↓← maxCompactU.coe_inv, weightMinors_neg, mul_div_cancel₀, ← mul_div (ofReal _), ne_of_gt]; rw [← dsCoeff_of_mem_maxCompactU hg.signs_one, dsCoeff_eq_flenstedJensen hg.signs_one] <;> congr 1 <;> simp [A, diagTorus, mul_assoc, mem_maxCompactU, maxCompactU.coe_inv]
  simpa [A, diagTorus, mul_assoc, maxCompactU.coe_inv] using hA.conjTranspose_mul_mul (k := y)⟩
attribute [local fun_prop] AnalyticAt.fun_zpow
lemma Orbital.cZL (hg : l.HasGap h) {P Q} (hP : ∀ x,
    let A := signMatrix ε * diagTorus ε x; A.IsAccretive → tE x P = tE x Q * oOI l A) {o} (ho : ∀ i j, l j < l i → o i < o j) γ (hk : ∀ β, Q.1 β ≠ 0 → o ⬝ᵥ γ < o ⬝ᵥ paramAddRho l + o ⬝ᵥ β + h) : P.1 γ = 0 := by
  by_contra; have ⟨β, m, H⟩ := P.1.support.exists_min_image (o ⬝ᵥ ·) ⟨γ, by simpa⟩; let S e (R : ℂ[_]) m z t := ∑ γ ∈ R.1.support, R.1 γ * weightMinors γ (signMatrix ε) * t ^ (o ⬝ᵥ γ - (o ⬝ᵥ β - m)) * z ^ (e ⬝ᵥ γ); have z : 0 < circleMap 0 1 0 := by simp [circleMap]
  refine absurd (_root_.linearIndependent_iff'.1 ((linearIndependent_monoidHom (Multiplicative _) ℂ).comp (fun γ ↦ ⟨⟨fun e ↦ 2⁻¹ ^ (e.toAdd ⬝ᵥ γ), by simp⟩, by simp⟩) fun a b h ↦
    funext fun i ↦ by simpa using congr(‖$h (.ofAdd (Pi.single i 1))‖)) _ _ (funext fun e : n → ℤ ↦ (Finset.sum_apply ..).trans (?_ : S e P 0 _ 0 = 0)) β m) (by simp_all [signMatrix])
  have ⟨C, _⟩ := Finite.exists_le (2 * |e ·|); let L := o ⬝ᵥ paramAddRho l + h
  have ⟨r, _, hr⟩ := ((oOL hg.1 ε 1).1.isClosed_compl.isCompact.eventually_forall_of_forall_eventually (P := fun r k ↦ ∃ i j, ε i ≠ ε j ∧ r * ‖weightMinors (-l.compactForm.lowestKType) (k.1.1ᴴ * signMatrix ε * k)‖ < ‖k.1 i j ^ 2‖ ^ h / 2 ^ (C * h - e ⬝ᵥ paramAddRho l)) fun k ↦ Not.imp_symm fun y ↦
    have c := mem_blockDiagAlg_iff_commute.1 (mem_blockDiagAlg (x := k).2 fun i j p ↦ y.imp_symm fun _ ↦ (ContinuousAt.eventually_lt ?_ ?_ (by simp; positivity)).mono fun _ h ↦ ⟨i, j, p, h⟩);
      ⟨⟨k, by simp [U, c.right_comm, by simpa [U] using k.2]⟩, 1, by simp [IsBorelMatrix]⟩).exists_gt (a := 0)
  refine norm_le_zero_iff.1 (((isClosed_le ?_ ?_ : IsClosed {t : ℝ | ‖S e P 0 _ t‖ ≤ ‖S e Q L 2⁻¹ t‖ / r}).mem_of_tendsto summable_geometric_two.tendsto_atTop_zero ((eventually_gt_atTop C.toNat ).mono fun s u ↦ ?_)).trans_eq (by simp [S, _root_.zero_zpow_eq]; grind [Finset.sum_eq_zero])); rotate_left 2; let D (z : ℂ) := diagonal (z ^ (s • o + e) ·); have A {z} h := (PosDef.diagonal fun _ ↦ zpow_pos h _).isAccretive.setOf_mem_nhds (z := D z); have E := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (f := fun z ↦ S e P 0 z (z ^ s)) (g := (fun z ↦ S e Q L z (z ^ s) / z ^ (s * L)) * oOI l ∘ D) (fun _ z ↦ ?_) (fun _ z ↦ .mul ?_ (((isAnalyticFamily_of_differentiable (.mono (A z) fun _ _ _ ↦ ⟨?_, ?_⟩)).analyticAt_integral _).comp (((diagonalLinearMap n ℂ ℂ).toContinuousLinearMap.analyticAt _).comp (.pi ?_)))) (convex_Ioi _).isPreconnected z
    (((hasDerivAt_circleMap ..).tendsto_nhdsNE (by simp)).frequently (.mono (Eventually.frequently ((?_ : ContinuousWithinAt (D ∘ _) ..) (A z))) fun z _ ↦ ?_)) (one_half_pos (α := ℂ))
  any_goals fun_prop (disch := first | grind | simp [ne_zero_of_re_pos z.1, *])
  simp [D] at E; simp [E]; grw [oOI, norm_setIntegral_le_of_norm_le_const (C := 2 ^ (-s * L) / r) (by simp) fun k ↦ ?_ ∘ hr k, measureReal_le_one]; simp [field]; rintro ⟨i, j, p, q⟩; grw [le_div_iff₀', norm_div, mul_div, q, div_le_of_le_mul₀] <;> try positivity
  have := lWM h k (-paramAddRho l) (-(s • o + e)) i j (s - C)
    (by simp [U.inv_mat]) (by simp [hg.paramAddRho_lt_iff]; intro a c k; grind
    [Int.mul_le_mul_of_nonneg_left (ho _ _ k) s.cast_nonneg])
    (by simp; grind [paramAddRho, by exact_mod_cast hg.3 i j p])
  simp [L, mul_pow, div_pow, field, dotProduct] at *; grind; specialize hP fun i ↦ ⟨ε i * circleMap 0 1 z ^ (s • o + e) i, by simp [Submonoid.unitSphere]⟩; simp_all [tE, signMatrix, diagTorus, ← mul_assoc, ← Int.cast_mul, S, D, dotProduct, mul_div, ← sum_div, lift_apply', div_mul_eq_mul_div, field]
end
attribute [-instance] FiniteField.instGrindPowIdentity IsOrderedRing.toIsStrictOrderedRing instIsCharPOfIsLeftCancelAddOfCharP
lemma Orbital.dAG {n} [Fintype n] (o b : n → ℤ) (ho : ∀ i j, b j < b i → o i < o j) (w : Perm n) i : o ⬝ᵥ b + |b i - b (w i)| ≤ o ⬝ᵥ b ∘ w := by have p s : (o + Pi.single i (cond s 1 (-1))) ⬝ᵥ b ≤ _ ⬝ᵥ b ∘ w := Antivary.sum_mul_le_sum_mul_comp_perm (fun x y z ↦ by grind [ho y x z, Pi.add_apply]); simp_all; grind
lemma Orbital.harish_chandra_degree_and_orbital {n : Type} [Fintype n] {ε} {l : HCParam ε} [Nonempty n] (hg : l.HasLargeGap (10 * Fintype.card n ^ 5)) : l.formalDegree = weylDimensionPoly l ∧ ∀ x, x.Injective → (-1) ^ #(oppositePairs ε) * ∑ σ : Perm n, ∫ g, l.dsKernel (g⁻¹ * diagTorus ε (x ∘ σ) * g) = #{σ : Perm n | ε ∘ σ = ε} * star (l.compactForm.lowestKType.kTypeChar (diagTorusK x)) := by
  let h := 500 * Fintype.card n ^ 3 + 10 * Fintype.card n ^ 5; have g : l.HasGap h := (by lia); let o := (-l).compactForm.lC Eq; let κ := paramAddRho l + o
  have hκ a : l a + Fintype.card n - 1 = 2 * κ a := by simp [κ, o, lC]; grind [two_mul_paramAddRho, twoRho, card_lt_add_card_gt_add_one g.1 a]
  have k s : (toHCParam s l).lowestKType + (toHCParam s l).lC Eq = κ - (-toHCParam s l).lC Ne := (by simp [κ, o, lowestKType, twoRho, lC, filter_and, filter_not, sdiff_inter_right_comm, funext_iff]; grind); have vt : l.rP Eq * l.rP Ne = l.compactForm.rP Eq := (by simp [rP, prod_filter, ← prod_mul_distrib]; grind); obtain ⟨W, G, ⟨P, aP, eP, ht⟩, σ, s1, lk⟩ := (by simpa [↓k, lC, Pi.sub_def] using (wCK g.signs_one.1 g.signs_one.isKDominant_lowestKType).2), (by exact_mod_cast g.3), eLO l hg, oCS g; set N := 4 * Fintype.card n ^ 2
  set D := (-l).rP Ne; let δ := (-l).lC Ne; let s : ℂ := (-1) ^ #(oppositePairs ε)
  have e : D = s • l.rP Ne := eTE fun x ↦ by
    simp [D, s, tRNc, g.1, g.neg.1, ← mul_assoc, ← prod_neg]; left; congr! 1; grind [HasGap, oppositePairs]
  let c := l.formalDegree * l.compactForm.lowestKType.kTypeNormSq * s / σ; let E ε := D ^ N * alternant ε κ; let b := κ + N • δ
  have nn r [DecidableRel r] x γ (c : (l.compactForm.rP r * D ^ N).1 γ ≠ 0) : o ⬝ᵥ (x + (-l).compactForm.lC r + N • δ) < o ⬝ᵥ x + o ⬝ᵥ γ + h := by simp [add_assoc, ↓dotProduct_add, dotProduct, δ, o, lC]; grw [← ((mul_mem (rLM l.compactForm r l) (pow_mem (rLM l Ne l) N)).2 γ (by simpa [e, smul_pow, s] using c)).1 _]; (repeat grw [card_le_univ]); simp [N, h]; rw [← sub_pos]; ring_nf; positivity
  have m i j (p : l j < l i) : o i < o j ∧ b j < b i := ⟨by grind [two_mul_paramAddRho g, Pi.add_apply], by
    simp [b, δ, lC]; by_cases N * Fintype.card n < κ i - κ j; grw [card_le_univ]; lia
    apply add_lt_add_of_lt_of_le <;> (try gcongr 3) <;> grind⟩
  have lev {k a} P : CSM l a (D ^ k) P → a + k • δ = b → P.1 b = 1 ∧ ∀ γ, P.1 γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ b := fun ⟨t, hf, ht⟩ d ↦ by
    simp [hf]; clear * - m g ht d; have := by simpa [lM] using pow_mem (rLM (-l) Ne o) k
    have e γ β (c : (D ^ k).1 β * t (-β + γ) ≠ 0) : ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w + ite (β ∘ w = k • δ) 0 1 ≤ o ⬝ᵥ b := (ht.2 _ (right_ne_zero_of_mul c)).elim fun μ ⟨j, p⟩ ↦ by
      obtain ⟨w, q, rfl⟩ := (by simpa [comp_symm_eq] using inv_surjective.exists.1 ( exists_ne_zero_of_sum_ne_zero (j ∘ (aAp _).trans))); simp [rootCone, Pi.add_comp, Pi.neg_comp, ← d] at *; grind [(@tCM _ _ (D ^ k) w 1).1 (by simp [D, tRNcc g.neg.1, ← q])]
    refine ⟨(Finset.sum_eq_single (k • δ) (fun _ _ n ↦ by_contra (e _ _ · |>.elim fun w _ ↦ ?_)) (by grind)).trans (by grind), by grind [exists_ne_zero_of_sum_ne_zero, Finsupp.sum]⟩; simp [imp_iff_not_or] at m; simp_all [show ⇑w = id by ext i; grind [m i (w i), m (w i) i, HasGap, dAG o b (fun i j ↦ by grind [m j i, HasGap]) w i]]
  obtain ⟨⟨p1, p2⟩, q1, q2⟩ := lev _ ht (by grind), lev (E ε) ⟨_, AddMonoidAlgebra.coeff_mul_apply_left _ _, by
    rw [aAp, Fintype.sum_eq_single 1] <;> simp [funext_iff, Perm.ext_iff]
    grind [HasGap], by simp [rootCone]; grind⟩ rfl
  suffices R : P = c • E ε by
    simp [*] at p1; refine ⟨by simpa [c, s, abs_of_pos, formalDegree_pos hg, s1, ← wDF g.signs_one, field, ne_of_gt] using congr(‖$p1‖), fun x u ↦ star_injective (mul_left_cancel₀ (tRN l.compactForm Eq u) ?_)⟩; have a τ := congr(Perm.sign τ * tE (x ∘ τ) $R); have := @tRN; simp [↓eP, *, E, pow_succ', ← mul_assoc, ← Int.cast_mul, mul_comm s, field, s, wDn g.signs_one.1 ▸ (tCM _).2 (wAl _ rfl)] at a; simp [dsKernel, integral_conj, mul_sum, ← mul_assoc, *, mul_left_comm _ (#_ : ℂ)]; simp [alternant, tE, mul_sum, ← sum_filter, mul_left_comm, sum_comm, ← by simpa [det_apply', mul_sum] using (fun w ↦ (det_transpose _).trans (det_permute' w⁻¹ (Matrix.of fun a b ↦ (x a).1 ^ κ (w b))))]
  ext γ; by_contra z; have ⟨w, hw, u⟩ := by_cases (fun _ ↦ q2 γ <| by simp_all) (p2 γ); have y : (E 1).1 (γ ∘ w) = w.sign * (E ε).1 γ := .trans ?_ ((tCM w).1 (by simp [E, *, tRNcc g.1, (tCM w).2, wAl w, field]) _)
  apply z; simpa [aP w, *, field] using cZL g (P := P - c • E 1) (Q := -(l.formalDegree * s / σ) • _) (by
    simp_all [E]; grind [norm_zero]) (m · · · |>.1) _ (u.trans_lt ∘ nn _ _ · ∘ right_ne_zero_of_mul)
  simp [E, AddMonoidAlgebra.coeff_mul_apply_left, aAp, Finsupp.sum]; congr! with β B v; specialize nn Ne κ β; simp [rP, lC.eq_unfold] at nn ⊢; intro; funext i; grind [dAG o κ (by grind [Pi.add_apply]) v i, dotProduct_add, dotProduct_neg]
