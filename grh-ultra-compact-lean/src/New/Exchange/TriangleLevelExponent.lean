import Lib.Weil.CompactLift.RallisFormula
import New.Seesaw.GradingsOfY
import New.Selmer.FitTwists
import New.Exchange.ExchangeTheorem
import New.Rows.LineArithmetic
import New.Seesaw.PairTensorData
section
seal Finset.univ Finset.sum Finset.prod
open Fin AutChar Finset Fint Fintype Function Matrix AuxPair LevelPlaces Space Sum
seal algFormCoeff
seal petersson
variable {E r n} [Field E] [CMType E] [Fintype n] [Fintype r] [WeilData E] (O : AuxPair E r n) {P} (D : Data P) (ϑ : D.TameChar) {s} {j : D.LiftIndex}
lemma AuxPair.adjoint_theta_eq_formLift [Nonempty r] {l} (h : O.FitsParams l) {y : O.W.Form _} {z} (a : ∀ Ξ, inner ℂ z Ξ = O.W.petersson y (O.θ Ξ)) : z.1 = (stdSpace ..).toAlgForm O.isHCParam_paramV (formLift O.pairThetaKernel (typeKernel l _) _ (O.fockDatum (highestVector _ O.paramV)) y) := (h.isEdge.isArrow O.a O.b O.auxDatum.2).elim fun A
  B ↦ congrArg _ (ext_inner_right ℂ fun Ξ ↦ by erw [a, LevelForm.inner_eq_petersson (stdSpace ..) O.isHCParam_paramV, ofAlgForm_toAlgForm, ← inner_eq_petersson _ ⟨_, isForm_ofAlgForm O.isHCParam_paramV Ξ.1⟩, A.inner_formLift_adjoint B rfl (by simp), ← inner_smul_right, O.theta_eq_smul_star_lift_swap, mul_comm, ← B.coe_formLift ⟨_, _⟩]; rfl : z = ⟨_, fun k ↦ by
  erw [← toAlgForm_formRep, A.formRep_formLift, ← star_highestVector, O.pairWeil_fockDatum]; simp⟩)
lemma AuxPair.lift_auxDatum_eq_lift_modDatum v {y} (hy : y ∈ O.W.rapidFunctions) (h : HasLevel y (levelOf O.chosenPlace ⊥)) : lift O.pairThetaKernel (integrated _ v O.auxDatum) y = lift
  O.pairThetaKernel (modDatum _ _ _ ((Nat.card (O.TwistGL r) : ℂ) • O.levelIndicator) v) y := by
  have e A f g := (O.pairThetaKernel.lift_equivariant hy.1 (integrated _ v f) (1, (O.twistLift A).1) 1 g).symm
  simp_all [upsilon_eq_sum, ← Prod.mk_one_one, fun A ↦ h _ (mem_levelOf.2 ⟨(O.twistLift A).2, funext (congrFun (reduceFamily_liftResidue (w := O.placeAt) _) <| inl ·)⟩), (O.pairThetaKernel.exists_clm_lift hy).choose_spec, funext_iff, modDatum, Pi.smul_comp]
omit [WeilData E] in
lemma AuxPair.levelIndicator_support_and_normSq : let F := (Nat.card (O.TwistGL r) : ℂ) • O.levelIndicator
  (∀ y, F y ≠ 0 → (inclMatrix (O.levelModulus 1).ResRing O.incl)ᵀ * y = 1) ∧ star F ⬝ᵥ F = Nat.card (O.TwistGL r) ^ 2 * (∏ i, (O.twistPlace i).q) ^ (O.rankDiff * card r) := by
  let e := Equiv.ofBijective (fun (y : Matrix n r _) i ↦ (y.map (levelResidueAt i) ·))
    (Injective.bijective_of_nat_card_le (fun _ _ ↦ ((O.levelModulus 1).matrix_ext_modulusResidue O.apart.1).2 ∘ congrFun) (by simp [Matrix, ↓Nat.card_pi, O.card_levelModulus_resRing, ↓card_ResField, prod_pow]))
  use ?_, (?_ : O.levelIndicator = (if e · ∈ piFinset fun i ↦ piFinset fun a ↦ ite (i.isRight ∧ a ∈ (univ.map O.incl)ᶜ) univ {inclMatrix _ O.incl a} then 1 else 0)) ▸ by simp [dotProduct, ← e.symm.sum_comp, prod_pow, apply_ite, ← card_ResField, card_compl, -mem_compl, -mem_piFinset]; ring!
  repeat simp_all [levelIndicator, (O.levelModulus 1).matrix_ext_modulusResidue O.apart.1, e, mem_ite, ← ext_iff, funext_iff, mul_apply, inclMatrix, -elim_inl, -elim_inr]
noncomputable def AuxPair.gramFactor : ℂ := stdLevelIndex O.levelGroup * Nat.card (O.TwistGL r) ^ 2
  * (∏ w, (O.twistPlace w).q) ^ (O.rankDiff * card r) / card (GL r (O.levelModulus 1).ResRing)
noncomputable abbrev Data.rallisTerm j (V : Space _ _ s) (y' y : D.principalForms V) γ := cosetTerm (card (D.Y 1)) (D.auxPair ϑ j).b (D.𝔪 ϑ 1).places.conjClosureᶜ y'.1 y γ / card
  (D.Y 1 × D.RowIndex → (D.𝔪 ϑ 1).ResRing)
lemma Data.exists_isSphericalWith_iota p : ∃ F : _ → _, ∀ y ∈ D.eigenPart _ p, ∀ w (h : D.IsSplitOffLevel w), IsSphericalWith (rightRegular ..) h.1 (F w) (D.ι .one y).1 := by
  simp [ι, isSphericalWith_toAlgForm_iff, -Subtype.forall]
  rw [← val_last D.m]
  induction' last _ using
    induction with i ih; exact ⟨_, fun _ h _ ↦ D.isSphericalWith_of_mem_eigenPart _ h⟩
  refine ⟨_, fun y a w h ↦ (isSphericalWith_formLift card_sum ?_ ?_ h.1 ((projOn_integrated ..).trans (congrArg _ (projOn_name_vacElem _ ?_))) (D.isArrow_datumY _ i.2).1 (ih.choose_spec y a w h)).smul⟩
  any_goals apply HasWeight.charUnramifiedAt <;> apply (auxPair ..).tame_eq_one
  all_goals simp_all [places_levelModulus, IsSplitOffLevel, auxPair, levelPlaces]; tauto
lemma Data.inner_auxLift y Ξ : inner ℂ (D.auxLift ϑ j y) Ξ = (D.spaceW j).petersson y ((D.auxPair ϑ j).θ Ξ) := (exists_theta_to_principalForms ..).choose_spec j.2 Ξ ▸ LinearMap.adjoint_inner_left ..
lemma Data.auxLift_injective_and_hasSum_inner : ∃ A ≠ 0, ∀ ϑ, Injective (D.auxLift ϑ j) ∧ ∀ x y, HasSum (A * (D.auxPair ϑ j).gramFactor * D.rallisTerm ϑ j _ x y ·)
  (inner ℂ (D.auxLift ϑ j x) (D.auxLift ϑ j y)) := by
  obtain ⟨C, hC, H⟩ := rallis_inner_product_euler (S := D.spaceW j) (D.fitsParams_auxPair .one j).isEdge (by grind [card_rowIndex, card_V])
  use C * card (WeylIndex (D.Y 1) (D.auxPair .one j).κ), mul_ne_zero hC NeZero.out, fun ϑ ↦ ?_
  let O := D.auxPair ϑ j
  obtain ⟨A, f, c⟩ := ((D.fitsParams_auxPair ..).isEdge.isArrow O.a O.b O.auxDatum.2).1, O.levelIndicator_support_and_normSq
  have U y := (congrArg _ (O.adjoint_theta_eq_formLift (D.fitsParams_auxPair ϑ j) (D.inner_auxLift ϑ y))).trans ((ofAlgForm_toAlgForm ..).trans (congrArg _ (A.eq_formLift_of_coe_eq _ (A.coe_formLift _ ▸ O.lift_auxDatum_eq_lift_modDatum _ (A y.1).1 (mem_levelSpace_formRep_iff.1 y.2)))))
  replace H (y : D.principalForms _) := H O.a O.b (isSharp_modDatum (stdSpace ..) _ (.inr (by apply nonempty_modulus_places)) _ f (O.tame_eq_one · <| places_levelModulus.ge.mt ·) (by simp [↓c, prod_eq_zero_iff])) _ (mem_levelSpace_formRep_iff.1 y.2 · ∘ by simp [O.ker_reductionK₀_eq, levelOf, funext_iff]; tauto)
  use .of_ker _ fun y z ↦ Subtype.ext ((H y).1 (Subtype.ext (U y ▸ z ▸ map_zero _))), fun x y ↦ ?_
  rw [LevelForm.inner_eq_petersson (stdSpace ..) O.isHCParam_paramV, U, U]
  exact (((H y).2 _).mul_left _).congr_fun fun _ ↦ by push_cast [gramFactor, c]; ring!
lemma Data.lifts_auxLift {p y} (hy : y ∈ D.eigenPart _ p) : (D.auxPair ϑ j).Lifts (D.auxLift ϑ j y)
  (p ⟨·, ·⟩) := fun w hw hS ↦ adjoint_theta_eq_formLift _ (D.fitsParams_auxPair ϑ j)
  (D.inner_auxLift ϑ y) ▸ (isSphericalWith_toAlgForm_iff ..).2 (isSphericalWith_formLift (by
    simp [AuxPair.rankDiff]) (HasWeight.charUnramifiedAt rfl rfl) (by grind
  [HasWeight.charUnramifiedAt, tame_eq_one]) hw (by simp_all [auxDatum, projOn_name_vacElem, places_levelModulus]) ((D.fitsParams_auxPair ϑ j).isEdge.isArrow _ _ (auxDatum _).2).1
  (D.isSphericalWith_of_mem_eigenPart _ hy ⟨hw, by simp_all [auxPair, levelPlaces]⟩))
lemma Data.auxLift_injective : Injective (D.auxLift ϑ j) := (D.auxLift_injective_and_hasSum_inner.choose_spec.2 ϑ).1
lemma Data.auxLift_principalRep s y : D.auxLift ϑ j (D.principalRep _ s y) = (D.auxPair ϑ j).formAction s (D.auxLift ϑ j y) := ext_inner_right ℂ
  (((formAction _).apply_bijective s).2.forall.2 fun Ξ ↦ by
  rw [inner_auxLift, ← funext (theta_mul_eq_theta_formAction _ _ (reduceFamily_liftResidue s) Ξ), ← (exists_theta_to_principalForms ..).choose_spec j.2]; exact
    (inner_formRep ..).trans ((innerAt_formAction ..).trans ((exists_theta_to_principalForms ..).choose.adjoint_inner_left ..)).symm)
open ComplexConjugate MeasureTheory Complex MulAction Subgroup
attribute [-simp] Nat.card_eq_fintype_card mem_classAut
variable {E n : _} [Field E] [CMType E] [WeilData E] [Fintype n] (X : LValueData E n)
attribute [local simp] prod_eq_zero_iff card_ResField places_levelModulus classSum apply_eq_evalForm AuxPair.rankDiff
unseal univ in
lemma LValueData.auxPair_lifts_trivialLift : X.auxPair.Lifts X.trivialLift 1 := fun _ hw h ↦ by
  have := hecke_transfer_of_equivariant (k := X.auxPair.rankDiff) (by simp [X.one_lt_card.le]) (X.a_hasWeight.charUnramifiedAt rfl rfl) (by
    apply X.b_hasWeight.charUnramifiedAt <;> grind [unramified]) hw (f := X.auxPair.auxDatum.1) (projOn_name_vacElem _ (by aesop)) (stdClassSum X.chosenLevel
    fun g ↦ by use ⟨(X.kernelValue 1 · g), ?_⟩ <;> simp [kernelValue, funext_iff]) 1 (rightRegular
    ..) fun g _ ↦ by ext1; simpa [trivialLift, kernelValue, rep_apply_apply] using! congr($(X.trivialLift_eq_stdClassSum_translate g) _).symm
  rw [show (_ : _ →ₗ[ℂ] _) _ = ↑X.trivialLift by ext1; simp [trivialLift]; rfl] at this
  simpa [IsSphericalWith, (isSphericalWith_trivialHecke _ _).2, heckePolyEval, smul_smul, sum_range_succ]
lemma LValueData.inner_trivialLift_self_eq_L {k} (hM : 2 * k = card n) (hk : 1 < k) :
    let C := (stdSpace E n).quotMeasure.real ⊤ * (stdSpace E Unit).quotMeasure.real ⊤ / eulerProd
      (K := E) realZetaCoeff (card n / 2 :); C ≠ 0 ∧ inner ℂ X.trivialLift X.trivialLift = C * (∏ i, ((X.chosenPlace i).q - 1) :) * hookNumber X.auxPair.κ (rankAt n) * card (WeylIndex n X.auxPair.κ) * X.μ⁻¹.L X.places k * (∏ i, (X.twistPlace i).q :) ^ (card n - 1) := by
  let O := X.auxPair
  have G (w : FinPlace E) := And.intro
    ((index_rangeParabolic (R := ResField w) O.incl).trans (index_stabilizer_line (O.incl ()) fun _ ↦ forall_congr' (by grind [lt_iff_le_not_ge, le_Prop_eq]))) ((congrArg _ (ext fun _ ↦ funext_iff.trans Unique.forall_iff : stabilizer (GL n (ResField w)) (inclMatrix (ResField w) O.incl).col = _)).trans (index_stabilizer_GL_vector (by simp [inclMatrix, funext_iff])))
  obtain ⟨⟨f, c⟩, ⟨A, B⟩, ⟨⟩⟩ := O.levelIndicator_support_and_normSq, (by simpa [realZetaCoeff, apply_ite] : (∀ w : FinPlace E, ‖realZetaCoeff w‖ ≤ 1) ∧ 1 < (k : ℝ)), (by lia : k = card n / 2)
  let S := univ.map ⟨_ ∘ X.placeAt ⊕ᵥ X.placeAt, (star_injective.comp X.apart.1).sumElim X.apart.1 X.apart.2⟩
  let D := X.places.conjClosure
  have a w : w ∈ S ↔ w ∈ D := by simp [S, D]; grind [star_star]
  obtain ⟨o, U⟩ := ((stdSpace E Unit).isAutomorphic_const 1).mem_rapidFunctions, places_levelModulus (S := X.1) (c := 1) ▸ isSharp_modDatum (stdSpace ..) O.b (by simp) _ f (by simp_all [unramified, O]) (by simp [↓c, NeZero.ne])
  have p := by simpa [heckeCoeff, Set.indicator, cpow_neg, ← HeckeChar.atUnif.eq_1] using
    (hasProd_eulerProd (X.hasWeight.inv.isHeckeOfType.norm_heckeCoeff_le (S := D)) B).div₀
                 (hasProd_eulerProd A B) (by simp [eulerProd_eq_exp, *])
  obtain ⟨⟨i, P⟩, F⟩ := inner_product_formula (hM ▸ by simpa) O.a O.b (U.clean (O.harmonicPoly (highestVector _ O.paramV))) o o, (fockPairing_toPoly_toPoly (conj ∘ highestVector O.κ _) _).trans (congrArg _ (gramForm_highestVector_self (O.isHCParam_paramV ·|>.1)))
  let T R := S ∪ R.image star ∪ R
  have Q := tendsto_nhds_unique_of_frequently_eq (.mul p (tendsto_partialIntegral D i))
    tendsto_const_nhds (Filter.frequently_atTop.2 fun R ↦ ⟨T R, le_sup_right, R.induction (by
    simp [-prod_mul_distrib, T, a, partialIntegral, localLevel]; rw [prod_map, prod_sum_type]) fun w
    R _ ↦ .trans ?_⟩)
  by_cases e : w ∈ T R; rw [(?_ : T _ = T R)]; swap
  have ⟨_, t, ht, r⟩ := exists_hasSum_vacuumCoeff_at_place X.hasWeight (X.unramified w ?_) (X.unramified _ ?_) hk
  rw [(?_ : T _ = T R ∪ {w, star w}), prod_union, mul_assoc]
  refine congrArg _ (.trans congr($(Finset.prod_congr rfl ?_) * _) (((hM ▸ r).mul_right _).unique (hasSum_partialIntegral_coset _ t (U.vacuum_off _ _ ?_) i (fun _ ↦ ?_) (SetLike.ext ?k) ht :)))
  case' k => simp [localLevel]
  any_goals clear * - e a; grind (gen := 9) [star_star, disjoint_left, mem_localLevel, Gf.mem_supportedOn, one_mem]
  erw [(U.partialIntegral_eq _ (y := 1) (by simp) O.detExp 1 1).2] at Q
  have Y := (eq_inv_smul_iff₀ (by simp)).1 ((O.lift_auxDatum_eq_lift_modDatum (O.harmonicPoly (highestVector _ O.paramV)) o (by simp)).symm.trans (funext fun _ ↦ (integral_quotMeasure_eq_classSum (by simpa using! (pairThetaKer ..).theta_rat_mul) (by
    simp_intro _ [X.theta_pairWeil_fockDatum, O]; rfl) _ (X.kernelForm_invariant.2.trans fun _ ↦ by
    simp_intro ..)).trans (congrArg _ ?_) : _ = (_ : ℂ)⁻¹ • ofAlgForm O.paramV 1 X.trivialLift.1))
  erw [← map_toPoly, toPoly_eq_rename_harmonicPoly, MvPolynomial.map_rename, show _ = fockPairing ℂ _ _ from (congrArg _ (MvPowerSeries.rename_coe ..).symm).trans (jet_rename ⟨_, ?_⟩ rfl _)] at F
  simp +instances [↓← prod_mul_distrib, ↓X.trivialLift.inner_eq_petersson (stdSpace ..) O.isHCParam_paramV, mul_left_comm (conj _), ← Y, O, ↓c, AutChar.L, hM, ← Set.Sum.elim_range, realPairWeil_schurCoeffPoly X.isLiftWeight, D, X.card_GL_levelModulus Unit, X.card_levelModulus_resRing, Nat.card_pi, X.apart.2, petersson, mul_assoc, ← pow_mul', realInner_polyVector, ↓relIndex_levelOf, index_pi_univ, auxLevel, HeckeChar.atUnif, mul_pow, realZetaCoeff_factor_mul, harmonicPoly_eq_schurCoeffPoly, modDatum, heckeCoeff, G, Nat.card_units, Nat.card_congr (Units.mapEquiv (@uniqueRingEquiv Unit (ResField _) ..).toMulEquiv).1] at P Q F ⊢
  simp (disch := simp) only [F, P, ← geom_sum_mul, ← one_div, one_sub_div, prod_mul_distrib, eulerProd_eq_exp A B, prod_div_distrib, prod_pow] at Q ⊢
  use by simp [measureReal_univ_ne_zero]
  field_simp (disch := norm_cast; simp [ne_of_gt]) at Q ⊢; rw [Q]
  simp_intro _ [Prod.ext_iff]
  simp [O, algFormCoeff_apply, trivialLift, star_highestVector]
end
section
open Circle Complex Finset Fintype LValueData Parameters LevelPlaces
variable {P D} (ϑ : D.TameChar) {p : @Data.Pair P D}
def Data.TameChar.IsIntegralMeasure (F : D.TameChar → ℂ) := ∃ (α : Type) (_ : Fintype α) (u c : α → _), (∀ a, c a ∈ integralAway ϑ.levelNorm) ∧ ∀ ϑ', ϑ'.Q = ϑ.Q → F ϑ' = ∑ a, c a * ϑ'.toAutChar.1 (u a)
lemma Data.TameChar.IsIntegralMeasure.norm_sq {F} : ϑ.IsIntegralMeasure F → ϑ.IsIntegralMeasure (‖F ·‖ ^ 2) := fun ⟨α, _, u, c, a, b⟩ ↦ ⟨_, inferInstance, fun (x, y) ↦ u x * (u y)⁻¹, _, fun x ↦ mul_mem (a x.1) fun l ↦ (a x.2 l · <| ·.comp _), fun _ e ↦ by simp [*, ← mul_conj', univ.sum_mul_sum, sum_prod_type, ↓coe_inv_eq_conj]; ac_rfl⟩
lemma Data.TameChar.IsIntegralMeasure.norm_apply_one_le {F l} [Fact l.Prime]
  (ι : ℂ ≃+* PadicAlgCl l) : (@one P D).IsIntegralMeasure F → ‖ι (F one)‖ ≤ 1 := fun ⟨_, _, _, _, a, b⟩ ↦ by simpa [b, twist_one_spec, ← map_sum] using!
    ((@embValRing l _ ⟨complexToCp ι⟩).sum_mem fun _ _ ↦ a _ l (by simp [levelNorm, twist_one_spec]) (complexToCp ι))
namespace Data.Pair
instance {l} [D.HasLogUpper D.t l] : D.HasLogUpper p.z l := D.hasLogUpper_of_le p.7.2
variable {n} [Fintype n] (H : p.HasLiftRank n) (ϑ : D.TameChar) (s : ℤˣ)
noncomputable def pointDatum := P.vacuumScale D.s ^ card (n × Unit) • vacuumDatum (stdSpace ..)
  (stdSpace ..) _ (lValueData H ϑ).auxPair.levelIndicator
noncomputable abbrev pointKernel := (lValueData H ϑ).kernelValue (star ↑D.piG * P.jetScale D.s) (pointDatum H ϑ)
lemma trivialLift_apply h : trivialLift H ϑ h = ∑ c : StdClasses (n := Unit) D.chosenLevel × TwistGL _ Unit, pointKernel H ϑ (c.1.out * (D.levelPlaces ϑ).twistLift c.2)
  h := by erw [apply_eq_evalForm, map_smul, map_classSum, classSum,
  funext (D.classAut_eq_bot_of_le_chosenLevel le_rfl (by simpa using D.nat_le_of_hasLogBound))]; simp [smul_sum, kernelValue, pointDatum, schurJet_jetSeries_eq_smul (isLiftWeight _) (_ * _), sum_prod_type, smul_smul, rep_apply_apply, kernelForm, Matrix.sum_mulVec, boxes, AuxPair.upsilon_eq_sum, ↓← apply_eq_evalForm]; simp [AuxPair.κ, mixedWeight, (lValueData H ϑ).one_lt_card]; rfl
lemma weylGauge_pointKernel_le_one {l} [Fact l.Prime] {j : PadicPlace l} g h (hl : l.Coprime ϑ.levelNorm) : weylGauge _ 0 h ((p.denomBound : ℂ) • pointKernel H ϑ g h) ≤ 1 := by simpa +contextual [weylGauge, weylRep, schur_eq_one] using!
  (mem_raises_of_dvd (pointDatum H ϑ) (hκ := isLiftWeight _) (ha := a_hasWeight _) (hb := b_hasWeight _) (K := ⊤) (smul_vacuumDatum_mem_standardData norm_mul_gProd_pow_mem_modulus (by grind [AuxPair.levelIndicator, one_mem, zero_mem]) hl) norm_star_piG_le_one (by simp [denomBound, boxes, AuxPair.κ, mixedWeight, (lValueData H ϑ).one_lt_card, ← H.1]) _ _ 1)
lemma isIntegralMeasure_intAlgPart : ϑ.IsIntegralMeasure (intAlgPart H) := let g (a : StdClasses (n := Unit) D.chosenLevel × TwistGL _ Unit) := a.1.out * (D.levelPlaces ϑ).twistLift a.2
  ⟨_ × _, _, fun x ↦ G.det (s := 1) ((1, g x.2) / (1, g x.1)), _, fun x l _ hl j ↦ (@embValRing _ _ ⟨j⟩).1.mul_mem (smul_classSum_mem _ (D.card_classAut_dvd_chosenGroupOrder (K := (lValueData H ϑ).auxPair.levelGroup) (H.1.trans_le D.nat_le_of_hasLogBound) levelOf_le_Kf) (gramForm_mem_embValRing _ (weylGauge_pointKernel_le_one H (ϑ.pow 0) (g x.2) _ hl) <| weylGauge_pointKernel_le_one H _ (g x.1) · hl)) (by simp [hl.norm_natCast_eq_one, -Nat.cast_prod] : ‖j (ϑ.levelNorm ^ (card n - 1))⁻¹‖ ≤ 1), by
  rintro ⟨⟩ rfl
  rw [sum_prod_type]; simp [intAlgPart, ← coe_algebraMap, ← inner_self_eq_norm_sq_to_K, inner, LevelForm.innerAt_eq_stdClassSum, mul_sum, sum_div, classSum_sum, ← coe_inv_eq_conj, ← mul_classSum, trivialLift_apply, TameChar.pow, kernelValue, pairWeil_apply, rankTwist, ↓map_div]
  congr with; congr with; ring!⟩
attribute [local simp] intAlgPart denomBound finite_isChosen twist_one_spec Finset.prod_eq_zero_iff NeZero.ne mul_div_mul_left
lemma intAlgPart_eq_mul_L : ∃ A ≠ 0, ∀ ϑ, intAlgPart H ϑ = A * (p.ν * ϑ.toAutChar)⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) p.z := by
  have h ϑ := (lValueData H ϑ).inner_trivialLift_self_eq_L H.1.symm H.2
  refine ⟨_, ?_, fun ϑ ↦ by simp_all [trivialLift, norm_smul, div_eq_iff, mul_pow, range_chosen, levelPlaces, ← ϑ.Q.prod_coe_sort, ← mul_assoc, -Fintype.card_pi]; dsimp +instances [levelPlaces, AuxPair.κ]⟩
  simpa [ne_of_gt, -Fintype.card_pi, H] using (h .one).1
lemma ratio_ne_zero_and_real : let r := p.ratio ϑ s; r ≠ 0 ∧ star r = r := by simp (disch := simp [funext_iff] <;> grind [p.8 1, Pair]) [ratio, ((ϑ.4.zpow s).inv.mul p.hasWeight.inv).L_ne_zero, p.hasWeight.inv.L_ne_zero]
lemma ratio_eq_intAlgPart_div : p.ratio ϑ = intAlgPart H ϑ / intAlgPart H .one := (intAlgPart_eq_mul_L H).elim fun _ ⟨_, h⟩ ↦ by
    simpa [*, ratio] using congr((‖$(h ϑ) / $(h .one)‖ : ℂ)).symm
@[simp] lemma intAlgPart_ne_zero : intAlgPart H ϑ ≠ 0 := by grind [ratio_eq_intAlgPart_div H ϑ, ratio_ne_zero_and_real]
@[simp] lemma trivialLift_ne_zero : trivialLift H ϑ ≠ 0 := by simpa using intAlgPart_ne_zero H ϑ
end Data.Pair
namespace Data
lemma IsFitFamily.heightLe_of_eq_zpow_mul {c c' y y' θ} (o : D.IsFitFamily θ) (h : HeightLe c y) (hc : c ≤ c') (hy : ∀ ι, y' ι ≠ 0 → ∃ k : ℤ, y' ι = (θ ι).levelNorm ^ k * y ι) : HeightLe c' y' := h.mono hc fun ι ↦ (not_or_of_imp (hy ι)).elim (by aesop) (by simp_all [(o.1 ι).norm_natCast_eq_one, -Nat.cast_prod])
variable (p)
def Pair.lowerPoint z := {p with z := 1 ⊔ z ⊓ p.z, z_mem := by grind [Pair], le_c := by grind [Pair, le_c]}
lemma Pair.lValueProd_eq (s : ℤˣ) (ϑ : D.TameChar) : lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) (p.ν * ϑ.toAutChar ^ s.1)⁻¹ p.z = ϑ.levelNorm ^ p.z ^ 2 * (lValueProd {w | D.IsChosen w} p.ν⁻¹ p.z * ∏ z ∈ .Icc 1 p.z, (p.lowerPoint z).ratio ϑ s ^ 2) :=
  by rw [lValueProd, lValueProd, finprod_mem_union, finprod_mem_coe_finset, Nat.mul_comm]
     push_cast [mul_pow, mul_assoc, ← prod_mul_distrib]; congr!
     cases (p.lowerPoint ‹_›).ratio_ne_zero_and_real ϑ s
     repeat simp_all [ratio, lowerPoint, field, Set.disjoint_right, IsChosen, levelNorm_mem_and_notMem_of_mem_Q _ ϑ, ↓finite_isChosen]
instance (D : Data P) (z) : NeZero (cond z D.b₁ 1) := z.rec .one D.instNeZeroNatB₁
end Data
end
