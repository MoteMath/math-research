import Lib.Adelic.CuspForms.RealConvolution
open Matrix Submodule U Norms.L2Operator MatMul Space G Prod
private lemma ex_dil {n m : Type} [Fintype n] {J} {A : Matrix n m ℂ} [H : IsHermInvolution J] (hA : Aᴴ * (J * A) = 0) x {c} (hc : 0 < c) : ∃ y : U J, dist y.1.1 1 ≤ c ∧ (x * y * x⁻¹, .mk0 (1 + c) (mod_cast by positivity)) ∈ dilationGroup A := by
 let B := Aᴴ * (J * x.1.1 * J)
 let p := toEuclideanCLM (𝕜 := ℂ).symm B.toEuclideanLin.kerᗮ.starProjection
 have hp : IsStarProjection p := .map (by simp) _
 have k {l} (v : Matrix n l ℂ) : B * v = 0 ↔ p * v = 0 := by simpa [Matrix.ext_col_iff, p, starProjection_eq_self_iff] using! congr(∀ j, -$(p.toEuclideanCLM_toLp (vᵀ j)) = 0)
 have e z l (w : Matrix n l ℂ) h := congr($((k (x.1.1ᴴ * J * w)).1 h)ᴴ * (p * z))
 rcases e 1, congr(-$((k _).2 hp.mul_one_sub_self)ᴴ)
 use of H.isUnit (1 + c • (p - (1 + c)⁻¹ • (J * p * J))) ?_
 grw [val_of_coe, dist_self_add_left, norm_smul, hp.2.norm_sub_eq_max, norm_smul, hp.norm_le, IsStarProjection.norm_le (_ * _)]
 all_goals simp_all [H.2, B, dilationGroup, ← form_mul_inv_eq, hp.1.mul_self_mul, H.1.eq, ← J.mul_assoc J, add_smul, star, ↓conjTranspose_mul, field, IsSelfAdjoint, add_pos, hc.le, abs_of_pos, isStarProjection_iff', (k _).1, Subgroup.ofDiv]
 match_scalars <;> field
namespace ThetaKernel
variable {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] {s t X} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {S : Space E n s} {V : Space E n' t} (Θ : ThetaKernel X S V)
lemma exists_norm_le_of_isCompact {K} (hK : IsCompact K) : ∃ C, ∀ k ∈ K, ‖Θ.ω k‖ ≤ C := .imp (fun _ ↦ SetCoe.forall'.2) (banach_steinhaus fun φ ↦ by simpa using hK.exists_bound_of_continuousOn (f := (Θ.ω · φ)) (by fun_prop))
lemma exists_rat_norm_le_height g₀ : ∀ᶠ a in .atTop, ∀ g, ∃ γ ∈ V.Γ, ‖Θ.ω (g₀, γ * g)‖ ≤ 2 ^ a * V.height g ^ a := by
 choose Ω hΩ H using V.mahler_criterion 2
 choose C c using Θ.exists_norm_le_of_isCompact ((isCompact_singleton.insert g₀).prod (hΩ.union ((isCompact_univ_pi fun _ ↦ isCompact_U_norm_le _).prod isCompact_singleton)))
 filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop C] with a ha g
 choose k b using exists_nat_pow_near (one_le_height g) one_lt_two; grw [← b.1, pow_right_comm]
 replace b := (le_firstMinimum_iff.1 (inv_le_of_inv_le₀ firstMinimum_pos b.2.le)).2
 induction' k with k ih generalizing g
 peel H g (inv_le_of_inv_le₀ two_pos (by grind [le_firstMinimum_iff])); grw [c] <;> simp [*]
 let W := V.move g
 choose y hy K _ using fun w ↦ ex_dil (A := fun i (ξ : {ξ ∈ W.baseLattice | ‖W.archCoords ξ‖ < 1}) ↦ W.archCoords ξ (w, i)) (Matrix.ext fun ⟨_, a, h⟩ ⟨_, b, k⟩ ↦ (stdForm_dotProduct_fst ..).symm.trans (by rw [stdForm_vecAtPoint, form_eq_zero_of_norm_mul_lt_one a b (by grw [k.le, mul_one, h])]; simp)) 1 one_pos
 apply_rw [norm_le_norm_add_const_of_dist_le] at hy
 peel 2 ih (g * (y⁻¹, 1)) fun ξ h₁ _ ↦ by_cases id fun l ↦ by
  have ⟨h₁, q⟩ := (W.mem_and_norm_le_of_vecAtPoint ξ _ ξ (mat (y⁻¹, 1)) 1 ((U.norm_inv _).trans_le <| hy ·) (by simp [W, -inv_mk, move_vecAtPoint, mat])).imp_left (· (by simp [ite_mem]) h₁)
  norm_num [pow_succ] at *
  grw [(PiLp.ext _ : archCoords _ ξ = (2 : ℂ) • W.archCoords ξ), norm_smul, ← b] <;> simp_intro .. [*, W, archCoords, move_vecAtPoint, ← mulVec_mulVec]
  erw [fst_sum]; simpa [W, archCoords, move_vecAtPoint] using! congrFun₂ (K _) _ ⟨ξ, h₁, by grw [q, l, (IsStarProjection.one _).norm_le, ← one_le_pow₀] <;> norm_num⟩
 grw [pow_succ, ← mul_assoc, ← this, ← ha, ← c (1, y, 1) ⟨.inr rfl, by tauto⟩, ← norm_mul_le]; simp [Prod.mul_def, mul_assoc, ← map_mul]
end ThetaKernel
open Subgroup MeasureTheory Real Set Classical Metric ComplexConjugate InnerProductSpace
lemma Space.IsForm.norm_le_dist {E n s} [Field E] [CMType E] [Fintype n] [Nonempty n] {V : Space E n s} {F B e a K g D} (he : IsCuspKernel B e) (hA : aᴴ * (stdForm E s * a) = 0) (z : ∀ w, a.map (evalInf w) ≠ 0) (hK : IsCompact K) (d : ∀ x ∈ K, dist (F (g * x)) (F g) ≤ D) (k : V.IsForm e F) : let N := (dilationGroup (m := n) a).comap (_root_.G.toUnitary.toMonoidHom.prod 1); (∀ u : N, ∃ γ ∈ (V.move g).Γ.subgroupOf N, γ.1 * u ∈ K) → ‖F g‖ ≤ D := by
 intro N hK'
 have p γ i x := by simpa [mul_assoc] using k.rat_mul _ (V.mem_move_Γ g (g := γ).1 i) (g * x)
 have : IsClosed N.carrier := by repeat' first | (intro) | fun_prop | apply_rules only [IsClosed.and, isClosed_eq, isClosed_iInter] | simp [← G.mat.eq_1, ofPred_forall]
 obtain ⟨c, m, C, b⟩ := k.1.1, isFiniteMeasure_quotMeasure_of_cocompact (G := N) .haar ⟨_, hK.preimage_val, hK'⟩, k.2
 have := isMulRightInvariant_of_finite_covolume m
 have u w x y : (x.map (evalInf w))ᴴ * (signMatrix s * .map y (evalInf w)) = (xᴴ * (stdForm E s * y)).map (evalInf w) := by simp [stdForm]; rfl
 convert (convex_closedBall ..).average_mem isClosed_closedBall (.of_forall (hK' · |>.elim fun γ ⟨i, j⟩ ↦ p _ i _ ▸ d _ j)) (IntegrableOn.of_bound m.1 (by fun_prop) C (by simp [b]))
 rw [average_eq, smul_eq_zero_of_right]; simp
 refine .trans (by simpa [mul_assoc, k.3 he.1.2] using (integral_mul_realConv k.isBoundedMeasurable he.1.2 (integrable_const 1) (g * · : N → _))) (integral_idem_mul_eq_zero (fun g ↦ log ‖(g ofNonempty)⁻¹.1.1 * a.map _‖) _ (⨅ w, (dilationGroup (a.map (evalInf w))).comap (.prodMap (Pi.evalMonoidHom _ w) (.id _))) he.1 he.2 (.log ?_ ?_) (fun x g ↦ (abs_sub_le_iff.2 ⟨.trans_eq ?_ (U.norm_inv (g ofNonempty)), ?_⟩).trans ?_) (fun _ h g ↦ .trans (by erw [mul_assoc, (inv_mem (Subgroup.mem_iInf.1 h _)).1]) ?_) ((nhds_basis_closedBall.forall_iff (by introv _; gcongr)).2 fun δ h ↦ ⟨_, (log_pos ((Complex.re_le_norm _).trans_lt' ?_)).ne', fun x ↦ (skolem.1 fun w ↦ ex_dil ?_ _ h).imp fun _ _ ↦ by simpa [dist_pi_le_iff', ← forall_and]⟩) (.ofNormedAddCommGroup (fun x ↦ ∫ v : N, F (g * (v.1 * (x, 1))) ∂_) (continuous_of_dominated ?_ ?_ (integrable_const C) (.of_forall ?_)) (C * _) fun _ ↦ norm_integral_le_of_norm_le_const ?_) (fun r h _ ↦ .trans ?_ (identDistrib_orbitMeasure_mul_right ⟨(r, 1), ?_, ?_⟩ ?_).integral_eq) 1)
 repeat first | fun_prop | grw [← log_div, log_le_self, div_le_iff₀, ← norm_mul_le] | simp +contextual [log_mul, norm_smul, le_prod_opNorm, *, mul_assoc, -coe_units_inv, Units.smul_def, div_nonneg, Subgroup.smul_def] | grw [← le_self_pow₀]
 all_goals intros; apply matrix_ext_𝔸 _ (by simp [↓Matrix.map_mul]; erw [one_mul])
 simpa using! (Subgroup.mem_iInf.1 h · |>.1)
 simp_intro _ [← u]; apply (Subgroup.mem_iInf.1 h _).2 <;> simp [*]
namespace Space
variable {E n} [Field E] [CMType E] [Fintype n] {s} {V : Space E n s} {e F F' B} (he : IsCuspKernel B e) (h : V.IsForm e F) (h' : V.IsForm e F') {α β}
attribute [local simp ←] integral_conj integral_const_mul integral_mul_const
lemma integral_comp_mul_right x (a : V.Γ.FixesLeft F) (c : Continuous F := by fun_prop) : ∫ g, F (g * x) ∂V.quotMeasure = ∫ g, F g ∂V.quotMeasure ∧ (Integrable (F <| · * x) V.quotMeasure ↔ Integrable F V.quotMeasure) := identDistrib_orbitMeasure_mul_right x (a _ ·.2) |> fun i ↦ ⟨i.integral_eq, i.integrable_iff⟩
lemma inner_eq_petersson (y y' : V.Form e) : ⟪y, y'⟫_ℂ = V.petersson y y' := rfl
private lemma IsAutomorphic.pmr : V.IsAutomorphic F → V.IsAutomorphic F' → ∀ x, V.petersson (F <| · * x) F' = V.petersson F (F' <| · * x⁻¹) | {..}, {..}, x => .trans (by simp [petersson]) (integral_comp_mul_right x (by grind [mul_assoc])).1
lemma inner_formRep k y y' : ⟪V.formRep e k y, V.formRep e k y'⟫_ℂ = ⟪y, y'⟫_ℂ := by simpa [-Prod.inv_mk] using! y.2.pmr (y'.2.comp_mul_right k).1 k
@[simp] lemma conj_petersson : conj (V.petersson F F') = V.petersson F' F := by simp [petersson, mul_comm]
namespace IsForm
include h
lemma «conj» : V.IsForm (star e) (star F) := ⟨h.1.conj, h.2.imp (by simp), by simpa [realConv, ↓funext_iff] using! congrArg star ∘ h.3 ∘ (starL' ℝ).integrable_comp_iff.1⟩
include he
lemma realConv_translate x g : ∫ z, e z * F (g * (z, 1) * (x, 1)) = conj (e x) / e 1 * F g := h.3 he.1.2 ▸ by simpa [realConv, ↓he.convolution_eq, he.apply_inv, mul_assoc] using congr($(realConv_realConv h.isBoundedMeasurable he.1.2 he.1.2 x) g)
include h'
lemma petersson_real_translate x : V.petersson F (F' <| · * (x, 1)) = conj (e x) / e 1 * V.petersson F F' := by
 have t := h'.isBoundedMeasurable.comp (· * (x, 1))
 nth_rw 1 [← conj_petersson, ← h.3, petersson_realConv_right, ← integral_inv_eq_self] <;> simp [he.apply_inv, h.pmr, h'.1.comp_mul_right, ← petersson_realConv_right t, he.1.2, h.isBoundedMeasurable, t]
 simp [petersson, realConv, h'.realConv_translate he]; ac_rfl
lemma petersson_realConv_realConv (hα : Integrable α) (hβ : Integrable β) : V.petersson (realConv α F) (realConv β F') = (∫ x, ∫ y, conj (α x) * β y * (conj (e (x⁻¹ * y)) / e 1)) * V.petersson F F' := V.conj_petersson ▸ by simp [↓petersson_realConv_right, h.pmr, mul_assoc, h.petersson_real_translate he, *, h'.1.comp_mul_right, h'.isBoundedMeasurable, h.isBoundedMeasurable, fun x ↦ h.isBoundedMeasurable.comp (· * x), isAutomorphic_realConv _ _ h'.rat_mul h'.exists_level.choose_spec]
end IsForm
