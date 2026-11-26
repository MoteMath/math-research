import Lib.DiscreteSeries.Theta.JointHarmonicExists
import Lib.Weil.Fock.OscillatorPair
import Lib.DiscreteSeries.Rigidity.KernelFixes
namespace OscillatorPair
variable {R C I} [Fintype R] [Fintype C] [Fintype I] {η} {ε ε' l l' Φ} {T : @FockDualPair R C ε ε' I} {π π'} (hp : OscillatorPair (η := η) T π π') [Nonempty R] (hΦ : IsJointHarmonic T l l' Φ)
open Finset MeasureTheory Fintype GlModule Matrix.Norms.L2Operator
include hp
omit [Nonempty R] in
lemma swap : OscillatorPair T.swap π' π := by grind [OscillatorPair, T.sw2]
include hΦ
lemma re_inner_integratedRep_pos : 0 < (realInner Φ (integratedRep π l.dsKernel Φ)).re := re_integratedRep_dsKernel_pos hΦ.hasLargeGap hp.unitary_rep hp.derives hΦ.2.2.2.2.1
 (hp.inner_pos Φ · hΦ.2.1 hΦ.2.2.2.1)
lemma iDA : IsDerivedAction π' ((integratedRep π l.dsKernel).1 ∘ₗ polyVector η) T.swap.oscRows :=
 let m := map_integratedRep hp.unitary_rep hΦ.hasLargeGap.integrable_norm_pow_smul_dsKernel; fun _
  _ ↦ funext (fun _ ↦ (m ..).trans ((m 1 _).trans congr(∫ _, _ • $(hp.3 ..) _)).symm) ▸ (hp.column_rep.derives ..).map_clm _
variable [Nonempty C]
attribute [-simp] nsmul_eq_mul zsmul_eq_mul ite_smul in
attribute [local simp] E smul_smul glOp DFunLike.ite_apply in
lemma integratedRep_fix {f : _ → ℂ} (hf : Integrable fun g ↦ f g * ‖g.1.1‖ ^ card I) (hr : ∀ g, ∫ y, f y * l'.dsKernel (y⁻¹ * g) = l'.dsKernel g) : letI v := integratedRep π l.dsKernel Φ; integratedRep π' f v = v := by
 obtain ⟨q, Q, -, u, -, w, -⟩ := hp.swap, hΦ.swap, hΦ.2; have := sum_congr _ _ w.1; apply fun κ k ↦ iRFH Q.hasLargeGap q.unitary_rep
  (hp.iDA hΦ) hf u ((congrArg _ (eq_sub_of_add_eq' (c := κ • Φ) k)).trans (by simp [iRDC hΦ.hasLargeGap hp.unitary_rep hp.derives, sub_smul])) (le_sub_left_of_add_le (a := κ) ((le_total ..).elim id (eCV
  hΦ.hasLargeGap hp.unitary_rep (T.sw2 ▸ q.iDA Q) w (.trans (congrArg _ k.symm) (by simp [iRDC Q.hasLargeGap q.unitary_rep
  q.derives, add_smul])) · ((q.re_inner_integratedRep_pos Q).ne ∘ by aesop) |>.le))) hr
 simp [↓casimir.eq_1, oscRows, ↓swap_oscRows_E, @eq_comm ℤˣ, apply_ite (raiseOp ..), apply_ite (lowerOp ..), ← smul_sum, ← Int.cast_mul, (canonical_commutation ..).2.2]; rw [@sum_comm C _ C]; simp_all [oscRows, ← smul_sum, ← sum_smul, ← eq_sub_iff_add_eq, @sum_comm R _ C, -LinearMap.coe_add, (canonical_commutation ..).2.1]; match_scalars <;> simp; norm_cast
open MvPolynomial Submodule Int Fischer in
lemma exists_bump_integratedRep_eq P : ∃ α : Bumps ε', integratedRep π l.dsKernel (polyVector η P) = integratedRep π' (α.1.1 ·⁻¹) (integratedRep π l.dsKernel Φ) := by
  obtain ⟨d, v, ⟨⟩, ⟨⟩⟩ := hp.iDA hΦ, hp.column_rep.unitary_rep, exIP hΦ.hasLargeGap hp.unitary_rep hp.derives, isKHighest_dsGenerator hΦ.gap.neg, hΦ.gap; set ι := (integratedRep π _).1 ∘ₗ polyVector η; let G := .proj 1 ∘ₗ smear _ (v.1 (ι Φ)); have a α : _ = G α := (map_integratedRep v (integrable_bump_inv_smul _ α) 1 (ι Φ)).trans (by aesop); have howe (M : Submodule ℂ (MvPolynomial I ℂ)) (hG : ∀ Y, M ∈ (T.swap.oscRows Y).invtSubmodule) (h0 : Φ ∈ M) (hc : ∀ {ν} Q Y, l.IsKHighest T.oscRows ν Q → ν - l.lowestKType ∉ l.rootCone → T.oscRows Y Q ∈ M) (K : ∀ a b {Q}, ε a = ε b → l b < l a → T.oscRows.E b a Q ∈ M) (L : ∀ a {Q}, T.oscRows.E a a Q - (l.lowestKType a : ℂ) • Q ∈ M) : M = ⊤ := eq_top_iff'.2 fun _ ↦ (@Int.strongRec 0 (pDeg · ≤ M) (by
    grind [pDeg, restrictSupport_eq_span, span_le]) (fun j _ ih ↦ by
    by_contra; choose _ y hy o _ k using l'.exHV (pInD j M) (by grind
      [left_eq_inf, inf_le_left, sup_orthogonal_inf_of_hasOrthogonalProjection, sup_bot_eq]) fun _ _ ↦ (mTP · (hG _))
    have w a := sub_eq_zero.1 (ezP (sub_mem (mTP rfl
      (fun _ h ↦ (M.sub_mem_iff_left (M.smul_mem _ h)).1 (L a)) hy) (smul_mem _ _ hy)) (L a))
    have t a b e f := ezP (mTP e (fun _ _ ↦ K a b e f) hy) mem_top
    have D : T.swap.IRH y := fun _ _ ↦ (fLz ih hy · rfl (hG _ ·))
    have V c s := (polCP hΦ.gap.1 t D ..).2 (w c) ∘ hΦ.smLN c s
    grind [smul_mem, ezP, hΦ.unique ⟨o, k, fLzH ⟨w, t⟩ fun a b k H ↦ fLz ih hy k
      rfl fun _ ↦ by_cases (fun h ↦ by cases Or.imp (V b (-1)) (V a 1) (by simp; grind [hΦ.1, IsMatch, iuV, by simpa using h (-l)]) <;> simp_all [glOp, _root_.pderiv_comm (T.varEquiv _), Finset.sum_eq_zero])
      (hc _ _ H), ⟨w, t⟩, D⟩ hΦ.2.isPreJointHarmonic]) _) fun _ ↦ ofNat_le.2 ∘ le_totalDegree
  refine ((howe (G.range.comap ι) (fun Y y ⟨β, e⟩ ↦ ⟨bumpDeriv Y β, eq_unitaryLiePart_add_I_smul ε' Y ▸ by simp [G, map_add, fun Y ↦ (d Y y).unique (by simpa [map_integratedRep v (integrable_bump_inv_smul ..) (π' _), ← e, ← a] using (hasDerivAt_smear _ β (v.1 _) (hasDerivAt_expU Y 1 0)))]⟩) ((hΦ.swap.hasLargeGap le_rfl).exists_bump_conv_dsKernel.imp (a · ▸ hp.integratedRep_fix hΦ (integrable_bump_inv_smul ..) ·)) (fun Q Y h k ↦ eq_unitaryLiePart_add_I_smul ε Y ▸ by simp [ι, iR0 hΦ.hasLargeGap hp.unitary_rep hp.derives h k, ← ((hp.derives ..).map_clm _).deriv]) ?_ ?_).ge (x := P) ⟨⟩).imp (a · ▸ symm) <;> simp +contextual [ι, *]
end OscillatorPair
