import Lib.DiscreteSeries.Rigidity.CasimirBound
import Lib.General.LinearAlgebra.ExpSurjective
open Int InnerProductSpace Fintype
section
open Calc Complex ComplexOrder Finset GlModule Module Sgn Submodule
variable {n} [Fintype n] {H I} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype I] (ε : n → ℤˣ) (ρ : GlModule n H) (J : I → End ℂ H) {ν : n → ℤ} {l : HCParam ε} {x : H} {y s A} [hg : l.HasGap A]
def KInv := ∃ D, (∀ c d, ε c = ε d → Commute (ρ.E c d) D) ∧ ∀ u v, ∑ i, ⟪J i u, J i v⟫_ℂ = ⟪u, D v⟫_ℂ
variable {ε} {ρ : GlModule n H} {J : I → End ℂ H} {x : H} {y : _} {s : ℕ} {A : ℝ}
lemma KInv.mul_E (h : IsUnitaryCasimirGe l ρ) : KInv ε ρ J → KInv ε ρ fun (p, q, i) ↦ J i * ρ.E q p := fun ⟨_, k, i⟩ ↦ ⟨_, (ρ.cES (· * ·) ‹_› <| k · · ·), by simp_all [sum_prod_type, h.1, mul_comm]⟩
lemma KInv.sICK (h : IsUnitaryCasimirGe l ρ) : KInv ε ρ J → ∀ u v, ∑ i, ⟪J i u, J i (ρ.casimirK ε v)⟫_ℂ = ∑ i, ∑ c, ∑ d with ε c = ε d, ⟪J i (ρ.E d c u), J i (ρ.E d c v)⟫_ℂ := fun ⟨D, k, i⟩ ↦ by simp [@sum_comm _ _ I, GlModule.casimir]; congr! 2; simp_all [h.1, ← (k ..).eq, ← D.mul_apply]
lemma HCParam.IsKHighest.cKBH {J : I → End ℂ H} (hx : l.IsKHighest ρ ν x) (h : IsUnitaryCasimirGe l ρ) [hg : l.HasGap A] (α β : ℝ) {U} (hs : U ≤ ρ.filtration ε x s) [Module.Finite ℂ U] (hU : ∀ a b, ε a = ε b → U ∈ (ρ.E a b).invtSubmodule) (hJ : KInv ε ρ J) (hy : y ∈ U) (H : ∀ w, (∃ z ∈ U, l.IsKHighest ρ (wWt ν w) z ∧ ⟪ρ.word w x, z⟫_ℂ ≠ 0) → w.length ≤ s → β ≤ α * l.casimirKValue (wWt ν w)) : β * ∑ i, ‖J i y‖ ^ 2 ≤ α * re (∑ i, ⟪J i y, J i (ρ.casimirK ε y)⟫_ℂ) := hJ.elim fun D ⟨k, i⟩ ↦ by
  let A := α • D * ρ.casimirK ε - β • D; let B := U.orthogonalProjectionOnto.1 ∘ₗ A.domRestrict U; have S : B.IsSymmetric := fun _ ↦ by simp [B, A, ← inner_conj_symm (D _), ← i, hJ.sICK h]
  suffices B.IsPositive by simpa [B, A, ← i, sq] using this.re_inner_nonneg_right ⟨_, hy⟩
  simp [← B.posSemidef_toMatrix_iff (S.eigenvectorBasis rfl), S.toMatrix_eigenvectorBasis]; intro t; obtain ⟨μ, z, ⟨u, f⟩, o, _, T⟩ := l.exHV (U ⊓ Uᗮ.comap (A - ofReal _ • 1))
    ((S.hasEigenvalue_eigenvalues rfl t).imp bot_unique fun u ↦ by
    simpa [B, ← orthogonalProjectionOnto_eq_zero_iff] using ·.le (x := u))
    fun a b f y ↦ .imp (by tauto) fun t u v ↦ by simpa [A, h.1, ← End.mul_apply, (k ..).eq, f, ((k ..).mul_right (cECK ..)).eq] using t _ (hU b a f.symm v)
  have ⟨w, hw, e⟩ := not_forall₂.1 (inner_self_ne_zero.2 o <| hx.fLWM (innerSLFlip ℂ z).ker (by simp_all [h.1]) · (hs u))
  have p : l.IsKHighest ρ (wWt ν w) z := ⟨fun a ↦ by
    have := h.1 a a (ρ.word w x) z; simp_all [field, hx.eWW], T⟩
  nlinarith [H w (by tauto) hw, pow_pos (norm_pos_iff.2 o) 2, univ.sum_nonneg'
    (mul_self_nonneg ‖J · z‖), by simpa [A, p.casimirK_eq_smul, sq, ← i] using congr(re $(f z u))]
open Matrix.Norms.L2Operator in
lemma HCParam.IsKHighest.norm_apply_le_of_mem_filtration {L : ℕ} (hx : l.IsKHighest ρ ν x) (h : IsUnitaryCasimirGe l ρ) [hg : l.HasGap A] (hR : ∀ a, |ν a| ≤ L) (hy : y ∈ ρ.filtration ε x s) X : ρ X y ∈ ρ.filtration ε x (s + 1) ∧ ‖ρ X y‖ ≤ (card n + 1) ^ 4 * (L + 1 + s) * ‖X‖ * ‖y‖ := by
  have := hx.finite_filtration h; have f := hx.cKBH h (-1) _ le_rfl (by grind [E_mem_filtration]) (J := ![1])
    ⟨1, by simp⟩ hy fun w _ _ ↦ antitone_mul_left (by simp) (cast_mono (sum_mono fun a ↦ by
    apply @mul_le_mul_of_natAbs_le _ _ (L + s) (L + s + card n) <;> grind [twoRho, hx.eWW w a]))
  simp [ρ.apply_eq_sum X, ← sum_product', sum_smul_mem, eMFS hy] at *; grw [← sq_le_sq₀ ?_ (by bound), norm_sum_le, norm_smul_le, norm_apply_le_l2_opNorm, ← mul_sum, mul_pow, sq_sum_le_card_mul_sum_sq, le_trans (a := ∑ _, _) ?_ (add_le_add_three f f (_root_.neg_le_neg
    (h.2 y)))] <;> simp [h.inC, sq, sum_filter, sum_prod_type_right, ← sum_add_distrib]
  grw [casimirValue, (sq_abs _).ge, cast_abs.ge, abs_twoRho_le, ← sub_nonneg]; simp [sub_div, -sub_nonneg]; ring_nf; positivity; congr! 2; split <;> simp_all [← cast_mul]
attribute [-simp] Module.End.ofNat_apply
attribute [local simp ←] ofReal_pow mul_sum
attribute [local simp] sum_prod_type E_mem_filtration Ring.lie_def add_mul mul_add mul_sub
lemma mem_orthogonal_filtration_of_casimirK {n} [Fintype n] {H} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε A} {l : HCParam ε} {ρ : GlModule n H} {x θ} (s : ℕ) [hg : l.HasLargeGap A] (h : IsUnitaryCasimirGe l ρ) (hx : l.IsKHighest ρ l.lowestKType x) a (ha : ρ.casimirK ε a = ofReal θ • a) (hs : θ - l.casimirKValue l.lowestKType ≤ s) (h0 : a ∈ (ρ.filtration ε x s)ᗮ) t : a ∈ (ρ.filtration ε x t)ᗮ := by
  let F := ρ.filtration ε x; have r {s a X} : a ∈ (F (s + 1))ᗮ → ρ X a ∈ (F s)ᗮ := by simp_all [F, ρ.apply_eq_sum X, mem_orthogonal', h.1, eMFS]
  have := hx.finite_filtration h; let P := (F 0).starProjection.1; have pc c d (e : ε c = ε d) v : P (ρ.E c d v) = ρ.E c d (P v) := by
    apply eq_starProjection_of_mem_of_inner_eq_zero <;>
      simp_all [P, F, ← map_sub, h.1, ↓starProjection_inner_eq_zero]
  have pk {a} : P a = 0 ↔ _ := starProjection_apply_eq_zero_iff _; have hj : KInv ε ρ ![P] := ⟨P * P, by
    simp_all [commute_iff_eq, DFunLike.ext_iff, P, inner_starProjection_left_eq_right]⟩
  have g a := by simpa +contextual [h.inC, sum_filter, -Units.val_mul] using (congr(re
    ⟪P a, $(cKMF (y := P a) (coe_mem _) hx.casimirK_eq_smul)⟫_ℂ))
  have w k : ∃ I, ∃ _ : Fintype I, ∃ J : I → _, KInv ε ρ J ∧ (∀ a ∈ (F k)ᗮ, ∀ i, J i a = 0 ∧ ∑ p, ∑ q, 2 * ‖J i (ρ.E q p a)‖ ^ 2 ≤ ∑ p, ∑ q, ∑ c, ∑ d with ε c = ε d, 2 * re ⟪ρ.E d c (J i (ρ.E q p a)), J i (⁅ρ.E q p, ρ.E d c⁆ a)⟫_ℂ) ∧ ∀ a, (∀ m < k, a ∈ (F m)ᗮ) → (¬0 < ∑ i, ‖J i a‖ ^ 2 → a ∈ (F k)ᗮ) ∧ (l.casimirKValue l.lowestKType + 2 * k) * ∑ i, ‖J i a‖ ^ 2 ≤ ∑ i, ∑ c, ∑ d with ε c = ε d, (‖J i (ρ.E d c a)‖ ^ 2 - ‖⁅ρ.E d c, J i⁆ a‖ ^ 2); refine k.rec ⟨_, _, _, hj, fun a h0 0 ↦ ⟨pk.2 h0, ?_⟩, by simp_all [sum_filter]⟩ fun k ⟨I, _, J, h1, h2, h3⟩ ↦ ⟨_, _, _, h1.mul_E h, fun a o (p, q, i) ↦ by simpa [r o, ρ.aaB (.single q p 1), h2, ← map_bracket] using (h2 _ (r o) i), fun a o ↦ have v p q := h3 (ρ.E q p a) (by bound); ⟨by
      simp! +contextual [o, h.1, (v ..).1 _ _, F, ← inf_orthogonal, ← iInf_orthogonal, mem_orthogonal, ↓Finset.sum_pos_iff_of_nonneg], by simpa [↓@sum_comm I, add_assoc, @norm_sub_sq ℂ] using (add_le_add (sum_mono fun p ↦ sum_mono (v p · |>.2)) (sum_mono (h2 a (by tauto) · |>.2)))⟩⟩
  obtain ⟨y, u, z, q, rfl⟩ := (F 1).exists_add_mem_mem_orthogonal a; simp [-map_sub, ← map_bracket, pk.2, r q]; have := hx.cKBH h 1 (l.casimirKValue l.lowestKType + 4 * card n + 2)
    inf_le_left (by simp_all [← pk])
    (hj.mul_E h) ⟨u, (add_mem_cancel_right (orthogonal_le le_sup_left q)).1 h0⟩ ?_
  have := show ∑ p, ∑ q, ∑ c, ∑ d with ε c = ε d, ‖P (⁅ρ.E d c, ρ.E q p⁆ y)‖ ^ 2 ≤ _ by
    simp [← map_bracket, mSMS]; grw [filter_subset, norm_sub_le, add_sq_le]
  rw [(hj.mul_E h).sICK h] at *; simp +contextual [pc, g, ↓re_sum, @norm_sub_sq ℂ, map_bracket, sum_filter, DFunLike.ite_apply, apply_ite (‖P ·‖)] at *; rw [sum_comm] at *; linarith; rintro (_ | ⟨⟨a, b⟩, ⟨⟩⟩) ⟨z, ⟨_, v⟩, hν, k⟩ (_ | ⟨⟨⟩⟩)
  cases k (v _ self_mem_filtration)
  obtain ⟨e, t⟩ := hg.gap a b (k ∘ v _ ∘ E_mem_filtration self_mem_filtration), hν.cBnd h (by bound); simp [HCParam.casimirKValue, sub_mul, wWt] at *; norm_cast at *; grind [two_mul_lowestKType, twoRho, card_pos_iff.2 ⟨a⟩, le_self_pow₀]; refine t.strongRec fun t hm ↦ have ⟨_, _, W, h2, _, h4⟩ := w t; have ⟨q, p⟩ := h4 a hm
      by_cases (fun n ↦ orthogonal_le (filtration_mono ?_) h0) q
  rify; grw [sub_le_self] at p <;> nlinarith
    [by simpa [ha] using congr(re $(h2.sICK h a a))]
end
section
open Matrix Norms.L2Operator Real
variable {n} [Fintype n] {M X H} [AddCommGroup M] [Module ℂ M] {ε} {l : @HCParam n ε} {ρ : GlModule n M} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup H] {ϖ : USign ε →* X →L[ℂ] X} {ι B A} (hp : IsUnitaryRep A ϖ B) (hd : IsDerivedAction ϖ ι ρ)
lemma HCParam.IsKHighest.coeffMap_eq_zero [InnerProductSpace ℂ H] {ρ ν} {x : H} {D h} [l.HasGap h] (hx : l.IsKHighest ρ ν x) (i : IsUnitaryCasimirGe l ρ) {c : USign ε → _ →ₗ[ℂ] ℂ} (hd : ρ.IsCoeffMap c) (hb : ∀ g v, ‖c g v‖ ≤ D * ‖v‖) (hy : ∀ s, ∀ v ∈ ρ.filtration ε x s, c 1 v = 0) g : c g x = 0 := by
  obtain ⟨⟨R, r⟩, X, Y, rfl⟩ := Finite.exists_le (|ν ·|.toNat), exists_eq_expU_mul_expU g
  have k (Y : unitaryLie _) g (hy : ∀ s, ∀ v ∈ ρ.filtration ε x s, c g v = 0) :=
    let rec f (m s : ℕ) v (hv : v ∈ ρ.filtration ε x s) : ∀ t ∈ unitInterval, ‖c (g * expU (t • Y))
      v‖ ≤ exp (m * -exp (-exp 1 * ((card n + 1) ^ 4 * ‖Y.1‖ + 1) * t)) * (exp (R + 1 + s) * (|D| * ‖v‖ + 1)) := have ⟨p, q⟩ := hx.norm_apply_le_of_mem_filtration i (toNat_le.1 <| r ·) hv Y
      image_norm_le_of_norm_deriv_right_lt_deriv_boundary (HasDerivAt.continuousOn (by tauto))
      (fun t _ ↦ (hd ..).hasDerivWithinAt) (by simp [hy s v hv]; bound)
      (fun _ ↦ hasDerivAt_deriv_iff.2 (by fun_prop)) fun t ⟨a, b⟩ ↦ (fun u ↦ by
      grw [hb, le_abs_self D, lt_add_one (_ * _)] at u; simp [← exp_add, field] at u
      have : s < m := by rify; grw [neg_nonpos.2, exp_zero] at u <;> bound
      grw [IsKHighest.coeffMap_eq_zero.f m _ _ p t ⟨a, b.le⟩, q]
      simp (disch := fun_prop) [exp_add, field]; grw [← u, ← sub_nonneg]; ring; bound) ∘ Eq.ge
    fun s v hv ↦ (summable_const_iff _).1 (.of_norm_bounded (.mul_right _ (summable_exp_nat_mul_iff.2 (by simp; bound)))
      (IsKHighest.coeffMap_eq_zero.f · s v hv 1 (by simp)))
  simpa using k Y _ (k X 1 hy) 0 _ ρ.self_mem_filtration
include hd in lemma IsDerivedAction.isCoeffMap [NormedSpace ℂ H] (φ : X →L[ℂ] H) : ρ.IsCoeffMap fun g ↦ (φ ∘L ϖ g).1 ∘ₗ ι := by intro _ _ _ t; convert! ((sub_self t ▸ hd ..).comp_sub_const ..).map_clm (φ ∘L _); simp [rep_apply_apply, mul_assoc, -map_mul]; rcongr; simp [← exp_add_of_commute, ← add_smul, commute_iff_eq, smul_comm t]
include hp
lemma IsUnitaryRep.exists_innerProductSpace : ∃ (H : type_of% X) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (j : X ≃ₗ[ℂ] H), (∀ x y, ⟪j x, j y⟫_ℂ = B x y) ∧ ∀ g x, ‖j (ϖ g x)‖ = ‖j x‖ := by refine' ⟨X, (Core.mk (.mk ⟨(B ·)⟩ ..) _).toNormedAddCommGroup, .ofCore _, 1, _, (congr(√$(hp.2 · · _).re))⟩ <;> simp [inner] <;> grind [IsUnitaryRep, Complex.zero_re]
lemma IsUnitaryRep.form_apply_eq_form_inv_apply g x y : B x (ϖ g y) = B (ϖ g⁻¹ x) y := by simp [← hp.2 g⁻¹ x, rep_apply_apply]
include hd
lemma IsDerivedAction.form_E_eq_sign_mul a b v w : B (ι (ρ.E a b v)) (ι w) = (ε a * ε b).1 * B (ι v) (ι (ρ.E b a w)) := have k Y := ((hd Y v).map_clm (B _)).star.unique (by
  convert (hd (-Y) w).map_clm (B (ι v)); simp [hp.form_apply_eq_form_inv_apply, hp.3]; rcongr; simp [← Matrix.exp_neg])
 have m z := k ⟨(z * ε b : ℂ) • single a b 1 - (star z * ε a) • single b a 1,
  ext (by simp [signMatrix]; grind)⟩; by rcases m (ε b), m (.I * ε b); simp_all
  [hp.3, -smul_single, mul_assoc, ← cast_mul]; grind [Complex.I_sq]
end
