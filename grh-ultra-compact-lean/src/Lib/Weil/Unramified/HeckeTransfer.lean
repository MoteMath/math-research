import Lib.Weil.DualPair.DatumLevel
import Lib.Weil.Lift.Edge
import Lib.Weil.Unramified.UniformiserScalar
import Lib.Weil.DualPair.PairSumNegation
noncomputable section
open ComplexConjugate Space InnerProductSpace Submodule LinearMap
variable {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] {s t X} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {S : Space E n s} {T : Space E n' t} (K : ThetaKernel X S T) (e e') {φ φ'}
def formLift : X →ₗ[ℂ] S.Form e →ₗ[ℂ] T.Form e' := (K.liftBilin.compl₂ (S.rapidFunctions.1.subtype.leftInverse ∘ₗ Submodule.subtype _)).compr₂ (Submodule.subtype _).leftInverse
def IsArrow φ := ∀ y : S.Form e, ↑y ∈ S.rapidFunctions ∧ T.IsForm e' (lift K φ y)
variable {K e e'}
def conjForm (h : e' = star e) : S.Form e →ₗ⋆[ℂ] S.Form e' := (starLinearEquiv _).1.restrict fun _ ↦ h ▸ .conj
@[simp] lemma coe_conjForm h (y : S.Form e) : (conjForm h y : S.Form e') = (conj <| y ·) := rfl
lemma IsEdge.isArrow [WeilData E] {γ γ' Φ ψ ψ' f} (h : IsEdge (realPairWeil γ γ') e e' Φ) (a b : AutChar E) [a.HasWeight γ ψ] [b.HasWeight γ' ψ'] (hf : f ∈ (S.hom T).finitePart) : IsArrow (pairThetaKer S T a b) e e' (integrated _ Φ f) ∧ IsArrow (pairThetaKer S T a b).swap (star e') (star e) (integrated _ Φ f) := (exists_level_pairWeil a b hf).elim fun K ⟨L, _⟩ ↦ by use fun y ↦ ⟨y.2.mem_rapidFunctions h.isCuspKernel_source, ((h.lift_isForm_and_eq_realConv _ ⟨0, rfl⟩).choose_spec _ ?_ y.2).1 L ?_⟩, fun y ↦ ⟨y.2.mem_rapidFunctions h.2.1, ((h.2.3 _ ⟨0, rfl⟩).choose_spec _ ?_ y.2).1 K ?_⟩ <;> simp_all [lift_mul_right, ← Prod.mk_one_one, pairWeil_integrated]
namespace IsArrow
variable (h : IsArrow K e e' φ) {ε ε'} (h' : IsArrow K.swap ε' ε φ)
include h
lemma eq_formLift_of_coe_eq {y} z (a : z.1 = lift K φ' y.1) : z = formLift K e e' φ' y := have l := @leftInverse_apply_of_inj; l (ker_subtype _) z ▸ congrArg _ (a.trans congr(K.liftBilin φ' $(l (by simp) ⟨_, (h y).1⟩)).symm)
attribute [irreducible] formLift
lemma coe_formLift y : formLift K e e' φ y = lift K φ y := h.eq_formLift_of_coe_eq ⟨_, (h _).2⟩ rfl ▸ rfl
lemma formRep_formLift k k' y : T.formRep _ k' (formLift K e _ φ y) = formLift K e e' (K.ω ((1, k), 1, k') φ) (S.formRep e k y) := h.eq_formLift_of_coe_eq _ (h.coe_formLift y ▸ funext (K.lift_equivariant y.2.1 _ _ _) :)
lemma formRep_formLift_of_eq_smul {k k'} {c : ℂ} (H : K.ω ((1, k), 1, k') φ = c • φ') y : T.formRep _ k' (formLift K e _ φ y) = c • formLift K e e' φ' (S.formRep e k y) := by simp [h.formRep_formLift k, *]
include h'
lemma integral_mul_formLift_swap y z : ∫ g, z g * formLift K e e' φ y g ∂T.quotMeasure = ∫ g, y g * formLift K.swap ε' ε φ z g ∂S.quotMeasure := by simp [coe_formLift, K.integral_lift_eq_integral_descent, h _, h' _, *]
lemma inner_formLift_adjoint b b' x y : ⟪formLift K e e' φ y, x⟫_ℂ = ⟪y, conjForm b' (formLift K.swap ε' ε φ (conjForm b x))⟫_ℂ := star_inj.1 (by simp [inner, petersson, ← integral_conj, mul_comm, ← h.integral_mul_formLift_swap h'])
end IsArrow
end
open Matrix Fintype WeilData AutChar HeckeChar Valued Space G CharUnramifiedAt
open Finset hiding card
lemma maximum_principle {G ι : Type*} [Fintype ι] {v} (hb : BddAbove (.range v)) {l} (a : ι → ℂ) (r : G → ι → G) (hl : ∑ i, ‖a i‖ < l) (h : ∀ g, l * v g ≤ ∑ i, ‖a i‖ * v (r g i)) g : v g ≤ 0 := by nlinarith [le_ciSup hb g, Real.mul_iSup_of_nonneg (hl.le.trans' (by positivity)) v ▸ @ciSup_le _ _ _ ⟨g⟩ _ _ (by grw [h ·, le_ciSup hb, ← sum_mul])]
variable {E n m W Z : Type} [Field E] [CMType E] [Fintype n] [Fintype m] {w} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z] {π : Representation ℂ (Gf E n) W} {a b : AutChar E} {k} (hk : card m = card n + k) (ha : CharUnramifiedAt a.baseChange.finPart w) (hb : CharUnramifiedAt b.baseChange.finPart w) (hw : w.IsSplit)
lemma FinPlace.q_eq_sqrt_sq : (w.q : ℂ) = √w.q ^ 2 := mod_cast by simp
lemma CharUnramifiedAt.apply_locFullIdele {χ} (h : CharUnramifiedAt (finPart χ) w) x : χ.1 (locFullIdele w x) = χ.atUnif w ^ (-(v x.1).log) := by simpa using! congr($(h.apply_locIdele_eq_zpow x).1)
lemma heckePolyOp_eq_sum {v} (hv : v ∈ sphericalAt π w) X : heckePolyOp π hw X v = ∑ U, heckePolyCoeff X U • π (atSplit hw (transposeGL (basicCosetRep U))) v ∧ heckePolyOp π hw.star X v = ∑ U, heckePolyCoeff X U • π (atSplit hw (basicCosetRep U)⁻¹) v := by simp [heckePolyOp, heckePolyEval, ↓← mem_sphericalAt_iff, heckeSplit_star, *, heckeFun_basicDoubleCoset_inv, heckeSplit.eq_1 _ hw, heckeGL_eq_sum, sum_filter, smul_sum, sum_comm, heckePolyCoeff, card_ResField, le_card_of_mem_basicDoubleCoset (basicCosetRep_spec _).1]
@[simp] lemma HeckeChar.norm_atUnif (χ : HeckeChar E) w : ‖χ.atUnif w‖ = 1 := Circle.norm_coe _
lemma isSphericalWith_trivialHecke {v} (hv : ∀ g, π g v = v) : IsSphericalWith π hw (trivialHecke w.q (card n)) v := by simp [IsSphericalWith, heckePolyOp_eq_sum, *, ← sum_smul, by simpa [card_ResField] using q_binomial_submodule n (ResField w) ⊤]
include ha hw
lemma CharUnramifiedAt.det_maxCompactAt_eq_one {g s} (hg : g ∈ maxCompactAt n w) : a.1 (detFin s g) = 1 := by ext; erw [det_of_supportedOn, detOn_eq_prod, prod_singleton, ha.apply_locFullIdele] <;> simp_all [mem_intGL_iff_det.1 (mem_Kf_iff.1 ..)]
variable [WeilData E] {s t} {S : Space E n s} {T : Space E m t} {f p} (hf : (S.hom T).projOn {w} f = f)
include hb hf
lemma sum_heckePolyCoeff_smul_pairWeil X : let N d c := (name _ {w} (residueDatum (fun _ ↦ w) fun x ↦ trivialHecke w.q (d - (x ()).rank) (X * c)) f); ∑ U, heckePolyCoeff X U • pairWeil S T a b ((1, 1), 1, atSplit hw (transposeGL (basicCosetRep U))) f = N (card m) (a.frobValue n w) ∧ ∑ U, heckePolyCoeff X U • pairWeil S T a b ((1, atSplit hw (basicCosetRep U)⁻¹), 1, 1) f = N (card n) (b.frobValue m w) := by nth_rw 2 3 [← hf]; simp (disch := simp [*]) only [← name_boxIndicator, pairWeil_name_on, smul_name, ← _root_.sum_apply, ← map_sum, ← coe_singleton, detOn_eq_prod, frobValue, AutChar.spaceChar]; constructor <;> congr with <;> simp [*, apply_locFullIdele, atUnif, ideleAbs_locFullIdele, charUnramifiedAt_upsilon, norm_locField_eq_q_zpow, basicCosetRep_spec, (basicCosetRep_spec _).1.2, -coe_units_inv, Real.sqrt_eq_rpow, ← Real.rpow_pow_comm, mem_integralBox, Real.inv_rpow, idem_mul_mem_Ô, ← evalAt_apply, matToVec, RingHom.map_matrix_mul, ite_and, ← transpose_apply (_ * Matrix.map _ _), -transpose_apply, @forall_comm m, ← card_ResField, residueDatum, v_mul_inv_le_one_iff (basicCosetRep_spec _).1, -rank_transpose, -mulVecLin_transpose, sum_filter, ↓card_sub_rank, ← rank_transpose (.map _ _), ← q_binomial_submodule, atSplit, Gf.atPlace, evalAt_star_locGL, ← GeneralLinearGroup.val_map_apply, -Units.coe_star] <;> congr! 3 <;> ring
include hk
lemma hecke_transfer_of_equivariant (Λ : _ →ₗ[ℂ] W) π ρ (hΛ : ∀ g h, Λ (pairWeil S T a b ((1, g), 1, h) f) = π g (ρ h (Λ f))) : Λ f ∈ sphericalAt π w ∧ Λ f ∈ sphericalAt ρ w ∧ ∀ X, heckePolyOp ρ hw X (Λ f) = trivialHecke w.q k (a.frobValue n w * X) • heckePolyOp π hw.star (w.q ^ k * a.frobValue n w / b.frobValue m w * X) (Λ f) := by simp [heckePolyOp_eq_sum, *, -hΛ, -map_inv, -map_smul, ← by simpa using And.intro (hΛ · 1) (hΛ 1), ← Prod.mk_one_one, pairWeil_eq_smul_of_projOn_eq {w}, det_maxCompactAt_eq_one _ hw, -LinearMap.map_smulₛₗ, ← map_sum, sum_heckePolyCoeff_smul_pairWeil, smul_name, ← LinearMap.map_smul_of_tower]; congr!; simp [funext_iff, residueDatum, add_comm, prod_range_add, Nat.add_sub_assoc, rank_le_card_width]; congr! 4 <;> simp [frobValue, atUnif, field, pow_add]
lemma hecke_transfer_of_pairing {ρ} {M : Submodule ℂ _} (B : M →ₗ[ℂ] W →ₗ[ℂ] Z) o (hB : ∀ g h v, ∃ Ψ, Ψ.1 = pairWeil S T a b ((1, g), 1, h) f ∧ ρ h (B ⟨f, o⟩ v) = B Ψ (π g v)) {v} (hv : v ∈ sphericalAt π w) : B ⟨f, o⟩ v ∈ sphericalAt ρ w ∧ ∀ X, heckePolyOp ρ hw X (B ⟨f, o⟩ v) = trivialHecke w.q k (a.frobValue n w * X) • B ⟨f, o⟩ (heckePolyOp π hw (w.q ^ k * a.frobValue n w / b.frobValue m w * X) v) := by obtain ⟨B, ⟨⟩⟩ := B.exists_extend; have ⟨h, K, H⟩ := hecke_transfer_of_equivariant hk ha hb hw hf B (π.linHom 1) (.linHom 1 ρ) (by simp [DFunLike.ext_iff, by simpa using hB ·]); use (congr($(K ·) v)), (by erw [← map_heckePolyOp (.applyₗ v) _ ?_, H ·, heckePolyOp_adjoint _ .applyₗ hv h] <;> simp)
lemma isSphericalWith_formLift {e e' y} (A : IsArrow (pairThetaKer S T a b) e e' f) (h : IsSphericalWith (S.formRep e) hw p y) : IsSphericalWith (T.formRep e') hw (fun X ↦ trivialHecke w.q k (a.frobValue n w * X) * p (w.q ^ k * a.frobValue n w / b.frobValue m w * X)) (formLift (pairThetaKer S T a b) e _ f y) := (hecke_transfer_of_pairing hk ha hb hw hf (.domRestrict _ ⊤) ⟨⟩ (by simp [← A.formRep_formLift]) h.1).imp_right (by simp [h.2, mul_smul])
