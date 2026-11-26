import Lib.Weil.Lift.Staircase
import New.Rows.StackedDeterminants
open Finset Kf MatMul Matrix MulChar Fintype PolyRep
abbrev LevelPlaces.TwistGL {E} [Field E] [CMType E] (S : LevelPlaces E) n [Fintype n]:=∀ i,GL n (ResField (S.placeAt (.inr i)))
variable {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] [WeilData E] (O : AuxPair E n n')
noncomputable instance (S : LevelPlaces E) : Fintype (S.TwistGL n) := .ofFinite _
noncomputable def LevelPlaces.twistLift (S : LevelPlaces E) (A : TwistGL S n):=liftResidue (Sum.rec 1 A⁻¹)
noncomputable def AuxPair.levelIndicator
  y := let X i := map y (levelResidueAt (S := O.1) (c := 1) i)
  (ite ((∀ i,X (.inl i)=inclMatrix _ O.incl)∧∀ i,(X (.inr i)).submatrix O.incl id=1) 1 0 : ℂ)
attribute [-simp] Sum.elim_inl Sum.elim_inr
lemma AuxPair.upsilon_eq_sum : ↑O.auxDatum=∑ A,O.pairThetaKernel.ω ((1,(O.twistLift A).1),1) (modDatum _ _ _ O.levelIndicator vacVector):=by
  simp_rw [← Prod.mk_one_one,← (Kf ..).coe_one,auxDatum,liftFn_eq_residueDatum places_levelModulus,← liftFn_eq_residueDatum (places_levelModulus (c:=1)),pairWeil_modDatum_Kf,modDatum_vacVector,places_levelModulus,← _root_.smul_apply,← _root_.sum_apply,← map_smul,← map_sum];congr 3 with x
  simp [O.hasWeight.hasWeight_rankTwist.apply_det_eq_prod O.apart.1 O.tame_eq_one,levelIndicator,LevelPlaces.twistLift,resDetDatum,submatrix_mul (e₂:=id),← inv_apply',(congrFun (reduceFamily_liftResidue ..) : ∀ _,Kf.reduceAt _ _=_),mul_inv_eq_iff_eq_mul_of_invertible];by_cases z : ∀ i,IsUnit (((vecToMat x).map (levelResidueAt (.inr i))).submatrix O.incl id);choose A e using z;simp [← e,Units.val_inj,← funext_iff,ite_and,inv_apply_eq_inv'];grind [Finset.sum_eq_zero,prod_eq_zero_iff,apply_eq_zero_iff,isUnit_iff_isUnit_det]
lemma AuxPair.pairWeil_upsilon k k' j (h : reduceFamily _ k'=firstBlockHom _ O.incl (reduceFamily O.chosenPlace k) * j.1) : O.pairThetaKernel.ω (k,k') O.auxDatum.1=((∏ i,O.ψ _ (reduceFamily O.chosenPlace k i).1.det)⁻¹ * O.auxLevelChar j)•O.auxDatum:=by
  simp_rw [auxDatum,← modDatum_vacVector,pairWeil_modDatum_Kf,modDatum_vacVector,← map_inv _ k',← _root_.smul_apply,← map_smul]
  erw [map_inv _ j⁻¹];congr 3 with
  simp [inv_apply_eq_inv',submatrix_mul_of_mem_rangeParabolic _ (inv_mem (j.2 (.inr _) ⟨⟩)),resDetDatum,firstBlockHom, -coe_units_inv,↓reductionK₀_map_modulusResidue,
    submatrix_mul (e₂:=id),↓Matrix.map_mul,by simpa [reduceFamily,funext_iff] using h,
    auxLevelChar,O.hasWeight.hasWeight_rankTwist.apply_det_eq_prod O.apart.1 O.tame_eq_one]
  congr! 1;simp [inv_mul_eq_iff_eq_mul_of_invertible,mem_stabilizer_col_iff.1 (j.2 (.inl _) ⟨⟩)];congr! 1;erw [extendGL_mul_inclMatrix,Matrix.mul_left_inj_of_invertible];simp [field,prod_eq_zero_iff,apply_eq_zero_iff];tauto
variable {E : _} {r} {n : _} [Field E] [CMType E] [Fintype r] [Fintype n] (O : AuxPair E r n)
noncomputable def AuxPair.paramV w i:=hcParameter O.κ O.detExp (card n) w (equivFin n i)
lemma AuxPair.isHCParam_paramV : IsHCParam O.κ O.detExp O.paramV:=isHCParam_hcParameter _ _ _
structure AuxPair.FitsParams l where
  paramsCorrespond :
    ParamsCorrespond (fun _↦negCount O.signs) ((card n / 2 : ℕ) + O.weight ·) l O.paramV O.signs 1
  ord_eq w c : O.ord c = #{c' | O.signs c'=O.signs c∧O.signs c * l w c < O.signs c * l w c'}
  colsPlus_eq_zero τ i : card {c // O.signs c=1} < i→O.colsPlus τ i=0
  colsMinus_eq_zero τ i : negCount O.signs < i→O.colsMinus τ i=0
attribute [local simp] negCount
lemma realPairWeil_fockLetters (s : r→_) ord γ' (y : GInf E 1) c F : realPairWeil (n':=n) (s:=s) (fun _↦negCount s) γ' (1,y) (fockLetters s ord c F)=fockLetters s ord c (rowSubst (fun τ↦ite (c=1) (y τ).1.1ᵀ (y τ)⁻¹.1.1) F):=by simp [realPairWeil_polyVector,fockLetters,rowSubst,MvPolynomial.bind₁_bind₁,smul_sum];congr!;convert sum_comm;aesop
lemma AuxPair.realPairWeil_harmonicPoly {γ'} y ξ : realPairWeil (s:=O.signs) (s':=1) (fun _↦negCount O.signs) γ' (1,y) (O.harmonicPoly (star ξ))=O.harmonicPoly (star (conjWeylRep _ O.detExp y ξ)):=by
  erw [star_mulVec,weylRep_map,← mulVec_transpose];simp [harmonicPoly,conjTranspose_transpose,Function.comp_def,MixedCartanEmbedding.intertwines, -mulVec_mulVec]
  open Calc in rw [pi_eq_sum_univ' (_ *ᵥ _)]
  simp [by simpa [realPairWeil_polyVector,polyVector_injective.eq_iff] using realPairWeil_fockLetters O.signs O.ord γ' y,mulVec_sum,sum_prod_type,← vec_single,
    realPairWeil_polyVector,single_eq_single_vecMulVec_single,letterPoly, -mulVec_single]
lemma AuxPair.FitsParams.exists_isJointHarmonic {l} (h : O.FitsParams l) : ∃ Φ : _→_,(∀ w,IsJointHarmonic (.std 1 O.signs (negCount O.signs) (-((card n / 2 : ℕ) + O.weight w))) (O.paramV w) (-l w) (Φ w))∧O.harmonicPoly (highestVector _ O.paramV)=∏ w,(Φ w).rename (w,·)∧∀ w c,(toHCParam O.signs (-l w)).lowestKType c=staircaseWeight n O.signs O.ord (if · = 1 then O.colsPlus w else O.colsMinus w) (-((card n / 2 : ℕ) + O.weight w)) c:=by
  obtain ⟨⟨p,o⟩,t⟩:=h,O.isHCParam_paramV;choose f u _ using (exists_equiv_decrPosition <| t · |>.1)
  exact (fun S↦(fun J↦⟨_,fun w↦⟨p w,funext (J w)▸S w⟩,by
    simp [*,← (hcParameter_strictAnti.injective <| u _ _▸t.eq_hcParameter · ·),harmonicPoly,highestVector,MixedCartanEmbedding.top]
    simp [letterPoly,weylKernel,highestPoly,permArray,Matrix.map,tableauPoly,minor,AlgHom.map_det,rowSubst,ite_and,fockLetters,apply_ite,sum_filter],J⟩) fun w a ↦
    (p w).exists_isJointHarmonic.elim fun _ J↦by
    rw [← @Int.cast_inj ℂ,← smul_left_inj J.2.1,← J.2.2.1.1,(J.unique J.2.isPreJointHarmonic (S w).isPreJointHarmonic).choose_spec,map_smul,(S w).2.1.1,smul_comm]) fun w ↦
    staircase_harmonic_highest (p w).2.1 (t w).1 (o w) _ (by fin_cases · <;> tauto) (by grind
    [O.rank_lt,negCount,neg_units_ne_self,by simpa using card_congr (.sigmaFiberEquiv O.signs)])
    (by simp [subtype_card,Int.units_ne_iff_eq_neg,vacuumWeight,detExp,sum_Ico_reflect,diagramWeight_apply,← Ico_succ_left_eq_Ioo,t.lowestKType_eq];grind [sum_Ico_eq_sub])
variable [WeilData E]
lemma AuxPair.FitsParams.isEdge [Nonempty r] {l} (h : O.FitsParams l) : IsEdge (realPairWeil (fun _↦negCount O.signs) ((card n / 2 : ℕ) + O.weight ·)) (typeKernel l O.signs) (typeKernel O.paramV 1) (O.harmonicPoly (highestVector _ O.paramV)):=h.exists_isJointHarmonic.elim (by simp_all [isEdge_of_isJointHarmonic,Nonempty.map O.incl])
lemma AuxPair.pairWeil_fockDatum x k ξ : O.pairThetaKernel.ω (1,x,k.1) (O.fockDatum (star ξ)) =
  O.levelChar k•O.fockDatum (star (conjWeylRep _ O.detExp x ξ)):=by erw
  [pairWeil_integrated_all,realPairWeil_harmonicPoly,O.pairWeil_upsilon 1 ⟨k,_⟩] <;> aesop
lemma AuxPair.conjKernel_equivariant γ k v g x : O.conjKernel g (stdEmbFin γ * x * k.1) (O.levelChar
  k•(stdSpace ..).weightRep _ O.detExp γ v)=O.conjKernel g x v:=congrArg star (.trans (by
  simpa [← pairTheta_mul,↓Complex.inv_eq_conj (LevelPlaces.isOfFinOrder_level_char k).norm_eq_one,map_inv,Prod.mul_def] using! congr(pairTheta _ _ O.a O.b $(O.pairWeil_fockDatum _ k⁻¹ _) (_,1,_ * k)).symm) (O.pairThetaKernel.swap.theta_rat_mul _ ⟨_,rfl⟩ _))
lemma AuxPair.theta_eq_smul_star_lift_swap Ξ : O.θ Ξ = (card (WeylIndex n O.κ) * stdLevelIndex O.levelGroup : ℂ)•star (Space.lift O.pairThetaKernel.swap (O.fockDatum (highestVector _ O.paramV)) (star (ofAlgForm O.paramV 1 Ξ.1))):=by
  ext y;simp [Space.lift,← integral_conj, -Fintype.card_pi];have H k g:=levelSpace_smoothFormRep_apply Ξ.2 1 g k▸O.conjKernel_equivariant _ _ _ y g
  erw [← star_highestVector,Space.integral_mul_eq_classIntegral O.isHCParam_paramV O.levelGroup
    ((O.pairThetaKernel.swap.isAutomorphic _ (by erw [pairWeil_integrated_fin O.W,(exists_level_pairWeil _ _ O.auxDatum.2).choose_spec.choose_spec _ (one_mem _) · ·]) y).conj)
    (O.conjKernel y) (by simpa [← pairTheta_mul] using! congr(star <| pairTheta _ _ O.a O.b $(O.pairWeil_fockDatum · 1 _) ⟨_,1,·⟩)),classIntegral_eq_classSum (by simpa using! H)];simp [field, θ, -Fintype.card_pi]
