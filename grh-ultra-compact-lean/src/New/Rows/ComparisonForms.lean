import New.Rows.RowVolume
import New.Filling.FillingTheorem
import New.Rows.MemberOrthogonality
section
seal Finset.univ Finset.sum Finset.prod
namespace DividedSplitting
open Matrix ComplexConjugate Finset Fintype IsUltrametricDist Ideal Modulus
attribute [local simp ←] map_inv coe_units_inv
variable {E r n N m a l} [Field E] [CMType E] [Fintype r] [Fintype n] [Fintype N] [Fintype m] [Fintype a] [Fintype l] {O:AuxPair E r n} {z} (V:DividedSplitting N m a O z) {p} [Fact p.Prime] [ι:PadicPlace p] {M:ℕ} [NeZero M] (hM : ↑M∈(O.levelModulus 1 false).ideal)
noncomputable def loss := ∑ τ,(#(univ.map V.dividedEmb)*(range (card N)).sum (O.colsPlus τ)+card m*(range (card m)).sum (O.colsMinus τ ·))
include hM
omit [Fintype a] in
lemma q2 (L:DividedLattice O) {κ h v g S} {f:l→ n} (hl:HasColumnsBelow n l κ) (hS:∃ K:GL l O.chosenModulusSq.ResRing,∀ i,∀ j∉S,V.genResidue*(L.reducedInverse.submatrix id f*K.1) i j=0) (e:g⁻¹.1.1.submatrix id f=inclMatrix _ f*h⁻¹.1.1):‖schur κ (fun τ↦((g*L.γ)⁻¹.1.1.submatrix id f).map (adeleExtension (weightEmbedding ιₚ τ))) *ᵥ ιₚ∘v‖≤ ‖(M:ℂ_[p])‖⁻¹^(∑ τ,#S*(range (card l)).sum (κ τ))*weylGauge κ 0 h v:=by
 let ⟨k,_⟩:=reductionK₀_surjective.exists.1 hS
 obtain ⟨h,rfl⟩:=mul_right_surjective k⁻¹.1 h;rw [weylGauge_mul h (Kf_le_localLevel k⁻¹.2)];simp_all [weylGauge,weylRep,← Matrix.mul_assoc,mul_inclMatrix,submatrix_mul (e₂:=id)];grw [← norm_mulVec_le (M:=schur κ fun _↦diagonal (S.piecewise M⁻¹ 1)),← norm_schur_mulVec_le hl.1 fun τ i j↦norm_adeleExtension_le_one (weightEmbedding ιₚ τ) (reduction_levelModulus_eq_zero_iff.1 (?_:(O.levelModulus 1 false).reduction ((∑ c,⟨_,L.integral i (f c)⟩*⟨_,k.2.isIntMatrix c j⟩)*ite (j∈S) ↑M 1)=0))];erw [mulVec_mulVec,mulVec_mulVec,hl.schur_mul_schur,hl.schur_mul_schur];congr! 5;ext;erw [mul_apply,mul_apply];swap;split;simp_all [← Quotient.eq_zero_iff_mem];simp_all [mul_apply,DividedLattice.reducedInverse,reductionK₀,← map_mul,← map_sum,reduction_levelModulus_eq_zero_iff,sq,mul_assoc]
 all_goals simp +contextual [schur_diagonal,piecewise,diagonal_apply,apply_ite (GE.ge _),apply_ite,prod_pow_eq_pow_sum,← inv_pow,mul_assoc,← mul_sum]
 intro i;gcongr;simp [one_le_inv₀,NeZero.ne,norm_natCast_le_one];grw [(sum_tableauWeight_le i ..).1,(diagramWeight_apply ..).le,Ioo_subset_Iio_self];simp [Iio_eq_Ico,mul_sum]
lemma kO {s L} (H:V.IsGlued s L) h y η:weylGauge O.κ O.detExp (U.block V.ε h*L.γ) (cartanProduct V.ε 1 y η)≤ ‖(M:ℂ_[p])‖⁻¹^V.loss*(weylGauge _ 0 h.1 y*weylGauge (ι:=⟨ιₚ.comp conj⟩) _ 0 h.2 (star η)):=by
 unfold loss weylGauge;grw (transparency:=default) [sum_add_distrib,pow_add,mul_mul_mul_comm,map_cartanProduct,(by aesop:ιₚ∘η=ιₚ.comp conj∘star η),weylRep_cartanProduct,@norm_mulVec_le,one_mul]
 apply norm_mul_le_of_le <;> apply (pi_norm_comp_le (_ *ᵥ _) _).trans
 apply V.q2 hM L _ H.exists_cols_eq_zero
 any_goals
   convert! ← V.q2 (ι:=⟨ιₚ.comp conj⟩) hM L ..;rw [U.inv_val_eq_conjTranspose];ext
   apply (adeleExtension_star ..).trans congr(adeleExtension $(RingHom.ext _) _)
 all_goals simp [reindex_equiv V.ε,entrywise,inclMatrix,V.low,HasColumnsBelow,norm_intCast_le_one,@starRingEnd_apply E]
end DividedSplitting
end
noncomputable section
open Finset Real ComplexConjugate Data WeilData Submodule Function.Embedding MeasureTheory LinearMap Fintype LevelPlaces AuxPair
variable {P} {D:Data P} (j:D.LiftIndex)
seal Subgroup.one levelSpace weylGauge
abbrev smallHookNumber:=hookNumber (untwistedAuxPair j).colsMinus (rankAt D.SmallIndex)
@[implicit_reducible] def SmallFormValues:=WeylIndex D.SmallIndex (untwistedAuxPair j).colsMinus→ ℂ
instance:NormedAddCommGroup (SmallFormValues j):=Matrix.toNormedAddCommGroup _ weylGram_posDef
instance:InnerProductSpace ℂ (SmallFormValues j) := .ofCore (F:=_→ ℂ) _
instance:Module.Finite ℂ (SmallFormValues j) := .pi
abbrev Data.Tables:=PiLp 2 fun _:MemberIndex j × D.SmallClasses↦SmallFormValues j
variable (ϑ:D.Twist)
def zV:DividedSplitting (BigIndex j) D.SmallIndex D.CarrierIndex (D.auxPair ϑ j) inl:=have:=rank_bounds_card_bigIndex j;⟨.trans (.sumComm ..) (.trans (.sumAssoc ..) (.sumCongr 1 (equivFinOfCardEq (by simp [*];lia)))),by tauto,inl.trans inl,
   (nonempty_of_card_le (by simp;lia)).some,by
   simp [HasColumnsBelow,schurDetExp,FitsRanks,funext_iff, *];grind [auxPair]⟩
lemma zS s:∀ g,classAut (stdSpace ..).embFin.range (rowFixingLevel _ ((zV j ϑ).zD s) (zV j ϑ).fixedEmb) g = ⊥ := D.classAut_eq_bot_of_le_chosenLevel (kQ ..)
 (by grind [rank_bounds_card_bigIndex j])
private def cf_v9 (i:MemberIndex j):{L // (zV j ϑ).IsGlued i.1 L} :=
 have H:=(zV j 1).wO _;⟨{H.choose with},{H.choose_spec with}⟩
private def v5:=Classical.indefiniteDescription _ (lineMultiplier_integral_and_small j)
attribute [local simp] apply_eq_evalForm map_classSum levelOf_le_Kf classSum
attribute [-simp] star_smul sum_ite_irrel ite_smul Sum.elim_inl isUnit_map_iff
set_option backward.isDefEq.respectTransparency false in
@[simps -isSimp] def comparisonForm:Tables j →ₗ[ℂ] (D.auxPair ϑ j).FormV where
 toFun ζ:=(D.gProd^(zV j ϑ).loss:ℂ) • ∑ b,stdClassSum (rowFixingLevel _ ((zV j ϑ).zD b.1.1) (zV j ϑ).fixedEmb) fun h↦(zV j ϑ).productForm
   (cf_v9 j ϑ b.1) (h,b.2.out) (star ((v5 j).1•lineMultiplier ϑ j b.1 h)) (ζ b)
 map_add':=by simp [↓zS]
 map_smul' a:=by simp [↓zS,smul_comm a,← smul_sum]
lemma kG {κ} (e:∀ i g,D.fNatural j i g=κ*cosetKernelSum _ (bigChar ϑ j) ((zV j ϑ).zD i.1) (.trans inl inl) (lineMultiplier ϑ j i) g) F ζ:conj κ*inner ℂ F ((D.goodLift ϑ j).adjoint (comparisonForm j ϑ ζ))=Nat.card (zV j 1).qC*D.gProd^(zV j 1).loss*conj (v5 j).1 * ∑ i,conj (cf_v9 j 1 i).1.weilScalar * ∫ g,conj (F.1.1 g*D.fNatural j i g)*tableTheta j (ζ ⟨i,·⟩) g ∂(D.spaceW j).quotMeasure:=by
 obtain _:=rank_bounds_card_bigIndex j,D.card_V,D.m_eq_two_mul_varrho_add_two
 let V:=zV j 1
 have k b h Q:=star_mul' (_*D.fNatural j b) _▸star_mem_rapidOfLevel
   (mul_modKernel_mem_rapidOfLevel (T:=stdSpace _ D.SmallIndex) (a:=(untwistedAuxPair j).a) D.ideal_untwistedModulus_eq_span (hb:=hasWeight_upsilonU1_zpow (D.m/2-j)) (mul_fNatural_mem_rapidOfLevel_and_hol F b).1 (Pi.single (inclMatrix _ inl) 1) Q (1,h))
 have i Y:=Space.mem_levelSpace_formRep_iff.1 F.1.2 _ (mem_levelOf.2 ⟨(liftMod _).2,funext (V.q5 Y)⟩)
 have R (x:(_ × _) × V.qC):=(k x.1.1 x.1.2.out (letterPoly (D.signsW j) (untwistedAuxPair j).ord (-1) _ (star (ζ x.1)))).1.elim fun A r↦(Space.integral_comp_mul_right (liftMod x.2.1) A.2 A.1).imp_right (·.2 (r.integrable A.1))
 erw [adjoint_inner_right,inner_auxLift,← integral_const_mul];refine (congrArg _ (funext fun g ↦ ?_)).trans ((integral_finsetSum univ fun x _↦(R x).2.const_mul (D.gProd^V.loss*conj ((cf_v9 j 1 x.1.1).1.weilScalar*v5 j))).trans ?_);erw [comparisonForm_apply,map_smul,map_sum,Pi.smul_apply,Finset.sum_apply,funext fun _↦DividedSplitting.kF _ (cf_v9 j ϑ _).2 ..];simp [*,mul_assoc,mul_sum,← sum_prod_type',mul_left_comm (conj (F.1.1 _)),mul_left_comm _ (conj κ)];rfl;simp [bigChar,bigCharExp,rankTwist,mul_assoc,← zpow_natCast,← zpow_add, *];congr;omega;simp [↓R,↓integral_const_mul,@sum_prod_type _ _ V.qC,@sum_prod_type _ _ D.SmallClasses,← mul_sum,mul_assoc,mul_left_comm _ (conj (v5 j).1)];left;congr!;simpa [tableTheta,mul_assoc] using! (integral_mul_sum_const_mul (c:=1) fun _↦k ..).symm
lemma exists_comparison_forms:∃ (γ:_→ ℂ) (A:Tables j →ₗ[ℂ] D.goodForms _) (gl:∀ _,_ →ₗ[ℂ] _),(∀ ϑ,γ ϑ≠0∧‖γ ϑ/γ 1‖^2=Data.heckeValueProd j ϑ/Data.heckeValueProd j 1)∧(∀ ϑ:D.Twist,(D.goodLift ϑ j).adjoint∘ₗgl ϑ=γ ϑ•A)∧Function.Surjective A∧(∀ (ϑ:D.Twist) y,AuxPair.IsTested _ D.e₀ (D.goodLift ϑ j).rangeᗮ (gl ϑ (A.adjoint y)))∧(∀ ϑ ζ l [Fact l.Prime] (φ:PadicPlace l),l.Coprime ϑ.levelNorm→ (∀ a,weylGauge (ι:=⟨φ.ιₚ.comp conj⟩) _ 0 a.2.out (star (ζ a))≤ 1)→ gl ϑ ζ∈LevelForm.integralForms φ)∧∀ ζ σ,smallHookNumber j*(gl 1 ζ).normSqAt σ≤ exp (2*(D.r*D.B₀)) * ∑ a,weylNormSq (σ∘ζ a):=by
 choose _ κ hn e using cosetKernelSum_eq_fNatural (a:=D.CarrierIndex ⊕ BigIndex j) j
 replace e ϑ i g:=e ϑ (.fromCols 1 0) i g ((zV j ϑ).zD i.1)
   (by erw [Matrix.fromCols_mul_fromRows,Matrix.zero_mul];simp)
 have hκ ϑ:κ ϑ≠0:=fun h↦D.finrank_rows_ne_zero ((D.finrank_rows_eq_finrank_goodForms j).trans (finrank_zero_iff_forall_zero.2 (eq_zero_of_integral_fNatural_tableTheta · (by simp [e ϑ,h]))))
 have U ϑ:=kG j ϑ (e ϑ)
 refine ⟨(conj <| κ 1/κ ·),(D.goodLift _ j).adjoint∘ₗcomparisonForm j 1,_,fun ϑ ↦ ?_,fun ϑ↦ext fun ζ↦ext_inner_left ℂ fun F↦by simpa [inner_smul_right,hκ,field,mul_comm] using (U ϑ ..).trans (U 1 ..).symm,range_eq_top.1 (orthogonal_eq_bot_iff.1 (bot_unique fun F m↦eq_zero_of_integral_fNatural_tableTheta F fun i ζ ↦ ?_)),
   fun ϑ F _ _ _ Ξ m ↦ ?_,fun ϑ ζ p _ φ q hζ ↦ ?_,fun ζ σ ↦ ?_⟩
 · simp;clear * - hn hκ
   grind [Complex.ofReal_eq_zero,norm_eq_zero]
 · have:=(U ..).symm.trans (mul_eq_zero_of_right _ (inner_eq_zero_symm.1 (m _ ⟨.toLp 2 fun b↦ite (b.1=i) ζ 0 b.2,rfl⟩)))
   rw [Fintype.sum_eq_single i (by simp +contextual [tableTheta,← modKernelBilin_apply])] at this
   simpa [(v5 j).2.1,DividedLattice.weilScalar,NeZero.ne]
 · set_option backward.isDefEq.respectTransparency false in
   have T i g:tableTheta j ((comparisonForm j ϑ).adjoint Ξ ⟨i,·⟩) g=0:=by
     obtain ⟨⟨⟨x,a⟩,z⟩,N,_⟩:=m,rank_bounds_card_bigIndex j,D.card_V
     have H:=(zV j ϑ).stdClassSum_inner_productForm_eq_zero (D.fitsParams_auxPair _ j)
       ((liftTamePart_eq_of_mem_Q ..).trans_ne <| ϑ.psi_ne_one _ ·.2) (fun i _ h↦range_le_ker_iff.2 ((map_mul ..).symm.trans (by erw [D.reflectionSum_mul_e₀ i (D.omega_zpow_mul_pow_eq_one j (ϑ.1.5 _ fun h↦(D.levelNorm_mem_and_notMem_of_mem_Q ϑ (.inl h)).2.1 i.2.2.1)) h rfl,map_zero])) x)
       (by rw [← (exists_theta_to_principalForms ..).choose_spec j.2,inner_self_eq_zero.1 ((adjoint_inner_left ..).symm.trans ((D.isCentralProj_e₀.1.map _).mem_range_iff.1 x▸(innerAt_groupAlgAction _ D.isCentralProj_e₀ ..).symm.trans (z _ ⟨⟨_,_,rfl⟩,groupAlgAction_auxLift ..⟩)))];rfl) a (by omega) D.ideal_untwistedModulus_eq_span
     simp [↓D.classAut_eq_bot_of_le_chosenLevel (n:=D.SmallIndex) (D.principalLevel_le_chosenLevel ⟨_,sq _⟩) (by simp [N];omega)] at H;refine .trans ?_ ((adjoint_inner_right (comparisonForm j ϑ) (.toLp 2 fun b↦ite (b.1=i) (star∘kernelVector (untwistedAuxPair j) (upsilonU1^(D.m/2-j:ℤ)) (D.untwistedModulus 2) (Pi.single (inclMatrix _ .inl) 1) _ g b.2.out) 0) Ξ).trans ?_)
     · rw [PiLp.inner_apply,sum_prod_type,Fintype.sum_eq_single i (by simp +contextual)]
       simp [tableTheta,kernelVector,inner,letterPoly,toPoly,linearCombination_apply,← modKernelBilin_apply,entrywise];rfl
     simp [comparisonForm_apply,@sum_prod_type _ _ D.SmallClasses,← classSum_sum,-classSum]
     simpa [↓zS,inner_smul_left,sum_inner] using .inr (sum_eq_zero fun _ _↦sum_eq_zero fun _ _↦by split_ifs;exacts [H ..,by simp])
   rw [← adjoint_inner_left,adjoint_inner_right,inner_eq_zero_symm];simpa [hκ,T] using U 1 F ((comparisonForm j ϑ).adjoint Ξ)
 · simp_rw [comparisonForm_apply,classSum,finsum_eq_sum_of_fintype,smul_sum]
   refine sum_mem fun b _↦sum_mem fun _ _ _ ↦ ?_;simp [↓zS j ϑ b.1.1]
   grw (transparency:=default) [weylGauge_smul,weylGauge_deltaForm_le isOfFinOrder_level_char,weylGauge_mul,(zV j ϑ).kO (M:=D.gProd) (D.ideal_untwistedModulus_eq_span.ge (by simp [← piGBar_mul_star,Ideal.mul_mem_right])) (cf_v9 ..).2,((v5 j).2.2 ..).1 _ q,hζ] <;> simp [Kf_le_localLevel _,mul_inv_le_one];simp [weylGauge]
 · rw [two_mul,exp_add,mul_assoc];set S:=exp _*Finset.sum ..
   obtain ⟨_,M,g,this⟩:=(by simp [S,exp_pos,Finset.sum_nonneg]:0≤ S),NeZero.pos D.chosenGroupOrder,NeZero.pos D.gProd,rank_bounds_card_bigIndex j
   have hm τ i:(untwistedAuxPair j).colsMinus τ i≤ D.h:=by grind [add_mul,auxPair,rowParameter]
   have c {n} [Fintype n] {K} (h:principalLevel n (D.piGBar^2)≤ K) hn:=(D.card_stdClasses_le_exp_mul_log (D.gProd^2) hn ((principalLevel_le_of_dvd (by simp [← piGBar_mul_star])).trans h)).trans (exp_le_exp.2 (D.le_of_hasLogBound (G:=D.b)))
   simp [comparisonForm_apply,LevelForm.normSqAt,← mul_classSum,-classSum]
   grw [← exp_log (Int.cast_pos.2 hookNumber_pos),classSum_le_card_mul_sq fun _↦(sqrt_weylNormSq_sum_le ..).trans (sum_le_card_nsmul _ _ _ fun _ _↦(sqrt_weylNormSq_classSum_le σ (B := √(D.chosenGroupOrder^2*S)) fun _↦sqrt_le_sqrt ?_).trans (by grw [c (by
     with_unfolding_all use Modulus.principalLevel_le_levelOfSubgroup (D.ideal_untwistedModulus_eq_span.ge (by simp))) (by lia)]))]
   simp (disch:=positivity) only [card_univ,card_eq_nat_card,Nat.card_prod,Matrix,Nat.card_fun,nsmul_eq_mul,Nat.cast_mul,mul_pow,sq_sqrt,← mul_assoc];grw [c (principalLevel_le_levelOf (Sum.rec (Ideal.pow_mem_of_mem _ ·.2.2.1 2 two_pos) nofun)),c le_rfl,c le_rfl,Modulus.card_resRing_le (levelModulus_ideal_le norm_mul_gProd_pow_mem_modulus),DividedSplitting.loss,(card_detIndex j _).elim (·.ge.trans),hm,hookNumber_le (sum_le_sum fun _ _↦sum_le_sum fun _ e↦mul_le_mul' (mem_range_le e) (hm ..)),← le_exp_of_log_le];simp (disch:=positivity) [log_mul,this,twist_one_spec,add_assoc];grw +useKAbstract [@log_le_self (_+_),@log_le_self (_*_),← sq,Nat.sub_sub,Nat.sub_sub,reducedHalfGap,Nat.sub_le,Nat.sub_le]
   simpa using D.le_of_hasLogBound;any_goals first | positivity | simp [*,twist_one_spec] <;> lia
   simp [DividedSplitting.productForm]
   grw (transparency:=default) [weylNormSq_deltaForm_le isOfFinOrder_level_char,map_cartanProduct (f:=σ.toRingHom),weylNormSq_cartanProduct,((v5 j).2.2 ..).2 rfl,single_le_sum (f:=(weylNormSq <| σ∘ζ ·)) (by simp),Nat.le_of_dvd M (card_classAut_dvd_chosenGroupOrder ..)] <;>
     simp [this,(zV j 1).low,HasColumnsBelow];lia
end
