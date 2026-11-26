import New.RealPlace.LocalTheorem
import Lib.DiscreteSeries.Bruhat.ComplexFloorMeasure
import New.Filling.StableCells
import New.RealPlace.BesselOrthonormal
section
open Fin Sum Complex ComplexOrder ENNReal EuclideanSpace Filling Fintype Level Matrix MeasureTheory Metric ProbabilityTheory Real Set Shape Size WithLp Fin.NatCast MeasureTheory.Measure Norms.L2Operator
structure RealPlaceSizes (𝔰:Shape) ρ s (b:ℝ) where
 rho_eq:ρ=b^(6*𝔰.n+2)
 eight_mul_r_le_rho:8*𝔰.r≤ ρ
 k_eq:𝔰.k=s+3*𝔰.n+2
 mul_cube_lt_s:10^9*𝔰.n^3< s
 pow_seven_le_k:𝔰.n^7≤ 𝔰.k
 ten_pow_le_varrho:10^8≤ 𝔰.ϱ
 two_le_b:2≤ b
variable {𝔰 ρ s b} (hF:RealPlaceSizes 𝔰 ρ s b) {L:ℝ}
@[simps toHyperbolicBasis θ measureH g 𝔅 boxSet positions] noncomputable def RealPlaceSizes.complexLevel:Level {i // i≠𝔰.k₀} (𝔰.middleGram (1:ℂ)) 0:=by
 refine ⟨complexBasis 𝔰,cellLaw 𝔰.ϱ∗ₘvolume.map embedH,volume.map embedH,1,toLp 2 ⁻¹' Metric.ball 0 4⁻¹,{x | ‖x.1.1‖≤ ρ},.univ,⟨ae_mem_mconv ?_ ?_,map_orbitPoint_cellLaw_top ?_⟩,?_,?_,⟨isOpen_ball.preimage (by fun_prop),?_,((PiLp.antilipschitzWith_toLp 2 _).isBounded_preimage isBounded_ball).isCompact_closure⟩,isCompact_U_norm_le _,.univ⟩ <;>
   simp +contextual (disch:=with_unfolding_all first | fun_prop | exact measurableSet_floorGroup)
   [↓ae_map_iff,cellChart_mem,embedH_mem_floorGroup,prob_le_one,hF.k_eq]
 intro _ _ h;erw [(exists_toBesselH_eq h).choose_spec,← map_dirac,← map_mconv_monoidHom (toBesselH 𝔰 1),mconv_dirac,map_mul_right_eq_self];fun_prop
noncomputable def RealPlaceSizes.j9:=(exists_eq_smul_haar volume hF.complexLevel.isMulRightInvariant_groupMeasure).choose
lemma RealPlaceSizes.vX:(hF.j9≠0∧hF.j9 ≠ ∞)∧hF.complexLevel.groupMeasure=hF.j9•ℙ∧(∀ f,Measurable f→ besselU.FixesLeft f→ ∫⁻ g,f g ∂hF.complexLevel.upperMeasure 0=hF.j9 * ∫⁻ g,f g ∂besselQuotMeasure) ∧ .ofReal (volU 𝔰.k/volU 𝔰.r)*hF.j9≤ 1:=by
 obtain ⟨s,e:_=hF.j9•_,_,g,_,eg,ig⟩:=isCompact_U_norm_le (J:=𝔰.J₁) 2,(exists_eq_smul_haar volume hF.complexLevel.isMulRightInvariant_groupMeasure).choose_spec,hF.k_eq,@exists_chart_ascConv_cellLaw 𝔰 𝔰.n
 have w l:l≤ 𝔰.ϱ→ descConv hF.complexLevel.floorMeasure 0 𝔰.n=ascConv cellLaw l∗ₘdescConv hF.complexLevel.floorMeasure l (𝔰.ϱ-l+1)∗ₘascConv complexPlace.heisenbergMeasure l:=l.rec (by simp [ascConv]) fun l ih h↦by
   rw [ih,s21_j8,ascConv,ascConv_heisenbergMeasure_succ];delta cellLaw cellChart cellDensity;simp [Place.weylLaw,mconv_assoc,← pow_mul];all_goals grind
 have n:=by simpa [stackMeasure_zero_eq,ascConv,ascConv_heisenbergMeasure_eq_besselHaar] using e
 suffices _ from ⟨⟨(by simp [·,stackMeasure_ne_zero] at e),(by simp [·] at this)⟩,e,fun F f j↦by simpa using (identDistrib_orbitMeasure_of_unfold (.id _) (.comp ⟨measurable_mul,n⟩ (.comp (.prod ⟨by fun_prop,rfl⟩ (.id _)) measurePreserving_swap)) f measurable_id (j _ ·.2)).lintegral_eq.symm,this⟩
 rw [← ENNReal.mul_le_mul_iff_left (measure_sublevel_ne_zero volume) s.measure_ne_top,one_mul,← lintegral_indicator_one s.measurableSet,← smul_eq_mul,mul_smul,← lintegral_smul_measure,← n,← map_inv_eq_self besselHaar,descConv_succ,w _ le_rfl]
 set f := @indicator _ ℝ≥0∞ _ _ 1
 have:Measurable f:=by measurability
 have j h k g:f (embedH h*(embedH k*g)⁻¹)=f g:=by
   simp [f,indicator,↓U.norm_inv,↓norm_embedH_mul,-_root_.mul_inv_rev]
 refine jX ‹_› fun k↦(lintegral_indicator_le ..).trans' ?_;erw [← lintegral_bruhat_coords,lintegral_mconv_symm];simp [descConv,floorMeasure,← mconv_assoc,ascConv_heisenbergMeasure_eq_besselHaar,besselHaar,← ascConv.eq_2,← lintegral_const_mul'];simp (disch:=with_unfolding_all fun_prop) only [ig,lintegral_mconv,lintegral_map];refine lintegral_le_const (.of_forall fun t↦lintegral_mono_ae ((ae_all_iff.2 (ae_eval_ne _ · 0)).mono fun c z ↦ ?_))
 by_cases! h:‖c (last _)‖≤ 1;simp [cellDensity,prod_univ_castSucc, *]
 have D x h b := @(((measurePreserving_conj_bessel mem_besselU0_iff_apply besselS_le_normalizer_besselU0 (mem_besselS.2 ⟨_,liftUnitri_mem_besselU x,_,toBesselH_mem h,rfl⟩)).mul_left 𝔰.besselHaar₀ ⟨_,(besselS_le_normalizer_besselU0 (mem_unitriGroup_of_mem_besselU (liftUnitri_mem_besselU x)) _).1 (unipotentOf_mem_besselU0 b)⟩).comp (measurePreserving_inv _)).lintegral_comp
 have e:=by simpa using eg (.mk0 _ <| z ·)
 have Z γ (v:realFrameGram γ=realFrameGram (g c)) x y :
   realFrameGram ((liftUnitri x)⁻¹*γ*liftUnitri y)=(unitriMatrix x)ᴴ*Matrix.diagonal
   c*unitriMatrix y:=by simp [↓frameGram_inv_mul_mul,↓frameGram_weylElem_mul,realFrameGram_cellChart,cellChart_mem,liftUnitri_mem_besselU,← init_def, *]
 have B x y:=congr($((frameDisc_frameGram_besselU_mul (liftUnitri_mem_besselU x) (liftUnitri_mem_besselU y) 1).trans (e▸frameDisc_weylElem_mul cellChart_mem 1)).re)
 simp only [Z,realFrameGram_cellChart h,RCLike.star_def,mul_conj'] at B;norm_cast at B
 have o x y:=jD.2 ((B x y).trans_gt (by simpa [-Units.coe_prod]))
 simp [lintegral_const_mul',← mul_assoc,row,gramDiscReal,B,o];gcongr 1;clear * - h;simp (disch:=bound) [cellDensity,prod_univ_castSucc,ENNReal.ofReal_mul',openCellConst,pow_add,← norm_prod,enorm,Finset.prod_pow];ring;rfl
 erw [@lintegral_lintegral_swap (_ × _)];gcongr with w
 repeat erw [lintegral_prod]
 gcongr with x;rw [lintegral_lintegral_swap,lintegral_prod];gcongr 1 with y
 obtain ⟨q,p,b,r,e⟩:=jK (o x y) (Z (embedH w⁻¹*g c*embedH t⁻¹) (by simp [realFrameGram_mul_invariant,Subgroup.mem_sup_right]) ..)
 rw [← D y (r*w⁻¹) b];gcongr 1;rw [← D x (p*k⁻¹) q];simp [← j (r*w⁻¹) (p*k⁻¹) (_*a.1⁻¹),eq_inv_mul_of_mul_eq e];group;rfl
 all_goals fun_prop (disch:=exact jO.measurableSet)
instance :
 hF.complexLevel.groupMeasure.IsHaarMeasure:=by simp [hF.vX,IsHaarMeasure.smul]
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
attribute [local simp ←] ofReal_coe_nnreal ENNReal.ofReal_mul ENNReal.ofReal_pow dotProduct_mulVec
attribute [local simp] star_mulVec MeasureTheory.volume_pi_closedBall Size.vecsOfSize inclMatrix pi_norm_le_iff_of_nonneg
lemma vM {m ι:Type} [Fintype m] [Fintype ι] (C:Matrix m ι ℂ) (_:card ι=s+1+3*𝔰.n) (h4:4≤ L) (_:C.rank≤ 3*𝔰.n) (c:card ι≤ L):∃ (D:Finset ι) (O:Matrix ι D ℂ),C*O=0∧Oᴴ*O=1∧∀ j,∫⁻ u in {u | ∀ i,‖u i‖≤ L^j},(.ofReal (‖star (Oᴴ *ᵥ u)⬝ᵥOᴴ *ᵥ u‖/36))⁻¹^s≤ (.ofReal L^2)^(99*𝔰.n*(j+1)):=by
 have H:=C.isHermitian_conjTranspose_mul_self;let Q:=H.eigenvectorUnitary
 let ⟨D,hD,d⟩ := @Finset.exists_subset_card_eq _ {i | H.eigenvalues i=0} s.succ (by grind [card_subtype_compl,card_subtype,H.rank_eq_card_non_zero_eigs,rank_conjTranspose_mul_self])
 use D,Q.1.submatrix id (↑),(conjTranspose_mul_self_mul_eq_zero ..).1 (ext fun a i↦congr($(H.mulVec_eigenvectorBasis i) a).trans (by simp;grind)),ext (congr($(Q.2.1) · ·).trans (by simp)),fun j ↦ .trans' ?_ ((lintegral_mono_set fun u h ↦ ?_).trans_eq (((((@measurePreserving_normSq_sphereDensity _ _ (D.card_pos.1 ?_).coe_sort).prod (.id _)).comp (volume_preserving_piEquivPiSubtypeProd ..)).comp (complexPlace.measurePreserving_mulVec Q.1ᴴ (det_of_mem_unitary (star Q).2).1)).setLIntegral_comp_preimage (f:=fun p↦(.ofReal (p.1/36))⁻¹^s) (s:=Iic (L*(L*L^j)^2) ×ˢ closedBall 0 (L*L^j)) ?_ ?_))
 erw [setLIntegral_prod_symm];simp [restrict_withDensity,Iic_inter_Ioi];grw [lintegral_withDensity_le_lintegral_mul,setLIntegral_le_iSup_mul,iSup₂_le (a := .ofReal (4*3^144))]
 · simp (disch:=positivity) [*]
   grw [pi_gt_three,pi_le_four,pi_le_four,h4,h4,h4];ring;gcongr <;> bound
 simp;intros
 grw [← exp_one_lt_three,exp_one_pow,← pow_div_factorial_le_exp _ _ s,pi_le_four];simp (disch:=finiteness) [← toReal_le_toReal,field,pow_succ,div_pow,d,← mul_pow];bound
 any_goals measurability
 have k i:‖(Q.1ᴴ *ᵥ u) i‖≤ L*L^j:=(norm_sum_le ..).trans (by
   simp;grw [entry_norm_bound_of_unitary Q.2,h _,← c];simp)
 simp (disch:=positivity) [k,↓star_dot_self_eq_norm_sq,norm_sq_eq];grw [k,← c,← D.card_le_univ];simp
lemma RealPlaceSizes.wA (hF:RealPlaceSizes 𝔰 ρ s b):4≤ ρ:=hF.eight_mul_r_le_rho.trans' (by simp;bound)
noncomputable def RealPlaceSizes.gauge (hF:RealPlaceSizes 𝔰 ρ s b) (hρ:ρ≤ L:=by rfl) :
 Gauge hF.complexLevel:=by
 obtain ⟨hk,_,h4⟩:=hF.k_eq,hF.eight_mul_r_le_rho,hF.wA.trans hρ
 refine ⟨⟨fun j↦{x | ‖x‖≤ L^j},?_,fun c k↦by
   rify at c;simp_all [pow_succ'];grw [norm_sum_le,k];simp;bound,?_,?_,by simp [inv_eq_left_inv IsHermInvolution.mul_self,(entry_norm_bound_of_unitary IsHermInvolution.mem_unitary ..).trans,h4.trans']⟩,
   .ofReal L^2,fun _↦by simpa [closedBall] using isCompact_closedBall (0:ℂ) _,?_,?_,by
   simp [HasMatSize,apply_ite,complexBasis]
   grind [norm_add_le,norm_one,norm_I],by simp +contextual [HasMatSize,(norm_apply_le_l2_opNorm ..).trans,hρ.trans'],fun u h i↦by simp_all;grind [PiLp.norm_apply_le (toLp 2 u) i],?_,by
   simp (disch:=positivity) [← mem_closedBall_zero_iff,-mem_closedBall]
   grw [pi_le_four,h4];ring;bound,fun σ _ j _ h ↦ .trans_eq ?_ (mul_one _),?_⟩
 iterate 6 simp (disch:=positivity) [pow_add,← ofReal_norm,pow_right_comm,abs_of_pos] <;>
   bound [two_le_pi,sq_nonneg (L-1)]
 · grw [Measure.map_apply,prod_apply_symm,complexPlace_skewMeasure,lintegral_map_le,← lintegral_cauchyPDF_eq_one 0 one_ne_zero,← lintegral_const_mul]
   gcongr with r;grw [measure_mono (t:=closedBall 0 (2*L^j/‖r+Complex.I‖) ×ˢ closedBall 0 (L^j)) fun p h ↦ ?_]
   · simp (disch:=positivity) [norm_eq_sqrt_sq_add_sq,volume_eq_prod,cauchyPDF,cauchyPDFReal,field]
     ring;grw [pi_le_four,pi_le_four,h4,h4,h4];ring;bound
   simp (disch:=positivity) [Place.flatChart,neg_add_eq_sub,mul_assoc,inv_def (starRingEnd ℂ _),← mul_sub] at h ⊢;nth_grw 1 [← abs_im_le_norm (_-_),le_div_iff₀ (by simp [Complex.ext_iff]),norm_add_le] at *
   simp_all [entrywise,← Finset.sum_add_distrib,mul_comm];linarith
   all_goals measurability
 let N:=(1-𝔰.J₁).submatrix (.map id (inl∘inr)) id
 set e:=hF.complexLevel.orthonormalPart
 intro x _ y _ v W
 refine (vM (fromRows v (fromRows (N*x⁻¹.1.1*e) (N*(x*y)⁻¹.1.1*e))) (by simp [volumeExponent,hk];lia) h4 (by grw [rank_le_card_height];simp;lia) (by simp_all;bound)).elim fun _ ⟨O,z,o,I⟩↦⟨_,by fun_prop,fun u ↦ ?_,I⟩
 clear * - z o;generalize hr:star _⬝ᵥOᴴ *ᵥ u=r
 by_cases r=0;simp [*]
 have B:closedBall 0 (|√‖r‖| / 9)⊆(star u⬝ᵥ·) '' W:=fun t h↦by
   let w:=O *ᵥ (t/r)•Oᴴ *ᵥ u
   have k {g:𝔰.G₁} (a:N*g.1.1*e*O=0):‖toLp 2 (g.1.1 *ᵥ e *ᵥ w)‖≤ 9⁻¹:=by
     have n:=congr(‖$(U.form_mulVec_mulVec g (e *ᵥ w) (e *ᵥ w))‖)
     rw [(by clear * -;simp [mulVec_eq_sum,funext_iff,N,splitGram,middleGram];grind:∀ z,
       N *ᵥ z=0 →
       𝔰.J₁ *ᵥ z=z) _ (by simp [w,← Matrix.mul_assoc,a]),star_dot_self_eq_norm_sq] at n
     simp [show eᴴ*(𝔰.J₁*e)=1 by ext;simp [e,complexBasis,mul_apply,splitGram,middleGram];grind] at n
     simp_all [-mulVec_smul,w,← Matrix.mul_assoc];grw [← sq_le_sq₀,n,h,h] <;> simp [field]
   use w,⟨by simp [-mulVec_smul,w,show v*O=0 from congr(toRows₁ $z)],(by simp;grind [norm_sub_le]:_→ _→ _) (k congr($z∘inr∘inl)) (k congr($z∘inr∘inr))⟩;simp_all [w]
 grw [← B,measure_mono (t:=closedBall 0 (3 / |√‖r‖|)) fun t h ↦ ?_];simp (disch:=positivity) [field];bound [pi_le_four,pi_gt_three]
 obtain ⟨c,w,⟨z,a,y,b,o⟩,e⟩ := @norm_inner_J₁_le 𝔰,(@B (|√‖r‖| / 9) (by simp)).imp (And.imp_left <| h ·)
 replace o:=congr(‖$o‖).le
 simp [e,← mem_ball_iff_norm',dotProduct_comm (star _),inner_toLp_toLp,(toLp_surjective 2).forall] at *
 grw [norm_sub_le,c,c,(norm_lt_of_mem_ball a.2).le,a.1.le,norm_lt_of_mem_ball b.2] at o;simp [field];bound
end
noncomputable section
open MeasureTheory Size Fintype Real Level Shape ENNReal Finset Gauge RealPlaceSizes
variable {j s:ℕ} {𝔰:Shape} {I:Type} [Fintype I] (F:C(𝔰.G₁,EuclideanSpace ℂ I)) {p q:ℕ→ ℂˣ} {ρ L t ε b:ℝ} {rep F₀ n W}
structure IsCutBessel rep ρ s b F₀ n extends IsCutPair b n rep (·.rec F₀ F),RealPlaceSizes 𝔰 ρ s b
namespace IsCutBessel
variable {F} (hF:IsCutBessel F rep ρ s b F₀ n) (hj:j≤ 𝔰.ϱ)
def v6:=volU 𝔰.k/volU 𝔰.r/(hF.j9.toReal*card I)^2
lemma z2:hF.complexLevel.IsCut F:=have h:=hF.isBesselFunction .cut
 ⟨⟨h.1,by simpa using h.2⟩,(_root_.exists_norm_le_of_besselSize_le <| hF.rho_eq▸hF.inCut_of_ne_zero _ ·)⟩
lemma vY:hF.complexLevel.volumeExponent=s:=by simp [Level.volumeExponent,hF.k_eq]
lemma exists_gauge_isHead j p q K:∃ L,∃ h:ρ≤ L,(hF.gauge h).IsHead j p∧(hF.gauge h).IsHead j q∧∀ R≥ ρ,(∀ l≤ j,‖(∏ a∈range l,p a).1‖≤ R∧‖(∏ a∈range l,q a).1‖≤ R)→ L^K≤ R^((K+6)*(2*j+1))*(headWeight K j p*headWeight K j q):=by
 have n {L B R} {x:ℂˣ} (c:L^K≤ B) (h:‖x.1‖≤ R) (_:1≤ L) (_:1≤ R) :
     max L ‖x.1‖⁻¹^K≤ B*(R^(K+6)*dampedPower K ‖x.1‖⁻¹):=by
   grw [dampedPower,← c,max_def,min_def]
   split_ifs <;> simp [field,pow_add] <;> (try grw [h]) <;> bound
 simp [IsHead,RealPlaceSizes.gauge,headWeight,-Units.coe_prod]
 refine' j.rec ⟨ρ,by simp;grw [← le_self_add];bound [hF.wA]⟩
   fun j ⟨L,a,b,h,c⟩↦⟨_,_,_,_,fun R r z↦(n (n (c R r _) (z _ .refl).1 ..) (z _ .refl).2 ..).trans_eq (by simp [prod_range_succ];ring)⟩ <;> clear n <;> grind [hF.wA]
include hj
lemma qS [Nonempty I] (hW:Place.IsBessel W 1) (hε : ∫⁻ y,‖W y‖ₑ^2 ∂besselQuotMeasure≤ .ofReal ε^2*card I) (ε0:0≤ ε) {hL:ρ≤ L} (hp:(hF.gauge hL).IsHead j p) (hq:(hF.gauge hL).IsHead j q) (hs:∀ {y},W y≠0→ hF.complexLevel.IsNear j y) {f} (ht:1≤ t) (hf:f≤ hF.complexLevel.formMajorant j p q F W) (h:∀ {x},1< t→ f x^2≤ .ofReal ((π*ρ^24)^𝔰.k/t^s)^2*(hF.gauge hL).selfNormProduct j p q F W x):‖(hF.v6:ℂ)‖ₑ*(hF.complexLevel.headDensity j p q * ∫⁻ x,f x ∂hF.complexLevel.groupMeasure)≤ .ofReal (𝔰.bandConst*L^(10^9*𝔰.n^4)*ρ^(24*𝔰.k)*t^(9900000*𝔰.n^3)/t^s*ε):=by
 obtain ⟨⟨l,_,_⟩:2≤ L∧1≤ ρ∧1≤ L,c,_,⟨_,_⟩,-,N,-⟩:=by bound [hF.wA],hF.z2,one_le_two.trans two_le_pi,hF.vX
 let T i:=t*L^(11*𝔰.n*i)
 have o i a b (h:a≤ 11*𝔰.n*i*b:=by lia):L^a≤ T i^b:=by
   grw [h,pow_mul,← one_mul (L^_),ht]
 have g i b:=hL.trans (pow_one L▸o (.succ i) 1 (.succ b))
 grw [← mul_one (ENNReal.ofReal _),← setLIntegral_univ,← Set.iUnion_eq_univ_iff (f:=fun i↦(hF.gauge (g i (99*𝔰.ϱ+98))).positionsOfSize).2 fun x↦(pow_unbounded_of_one_lt _ (by linarith)).imp fun i e↦⟨⟨⟩,fun _ _↦(norm_apply_le_l2_opNorm ..).trans (e.le.trans ((o _ i _).trans_eq (pow_mul ..)))⟩,← iUnion_disjointed,lintegral_iUnion_le,← tsum_two_zpow_neg_add_one]
 simp [← ENNReal.tsum_mul_left,disjointed];gcongr 1 with i;grw [lintegral_positions_le _ _ c hW hj hq (Θ := .ofReal ε*(hF.j9*card I)^2) ?_ sdiff_le (e := .ofReal ((π*ρ^24)^𝔰.k*ρ^(9999*𝔰.n)/T i^s)) fun x m ↦ ?_]
 have := @toReal_ne_zero
 simp (disch:=finiteness) [RealPlaceSizes.gauge,floorModulus,← toReal_le_toReal, *,T,v6,bandConst,volU,field,mul_pow,← pow_mul,abs_of_nonneg,ENNReal.zpow_sub,ENNReal.zpow_neg]
 nth_grw 1 [tsub_le_self,l,l,hL,← hF.mul_cube_lt_s];ring_nf;gcongr <;> omega
 repeat grw [Level.pairingNorm,(ofReal_norm _).ge,norm_inner_le_norm]
 simp +contextual [mul_pow,lintegral_mul_const,N,hW.2,c.law,-upperMeasure,enorm_smul,← ofReal_norm (wave _),hW.stronglyMeasurable.enorm.pow,c.stronglyMeasurable.enorm.pow];grw [hε,hF.lintegral_sq_cut_le];ring_nf;rfl
 by_cases i=0∧1< t;grw [h] <;> bound
 grw [hf x,formMajorant_sq_le _ c hW hj hp ⟨⟩ (by grw [hF.gauge.floorMassLe_one ⟨j,by lia⟩ hasFibreBound_floorQuadric ·,volume_le]) (σ:=volume (Metric.ball (0:ℂ) (T i)⁻¹)) (by bound) hs fun z _ a b d ↦ ?_,hF.vY]
 gcongr;simp (disch:=finiteness) [RealPlaceSizes.gauge,← toReal_le_toReal];ring_nf;gcongr <;> grind [RealPlaceSizes]
 cases i;simp_all [T,ht.antisymm',← NNReal.coe_lt_one,not_lt_of_ge]
 contrapose m
 simpa using fun _↦⟨_,le_rfl,⟨⟩,by simpa [RealPlaceSizes.gauge,HasMatSize] using! ((hF.gauge (g _ 0)).hasMatSize_sub_one_of_floorValues _ hj hp hq (by
   simpa [RealPlaceSizes.gauge] using fun _ _↦(o _ _ 1).trans') ((c.2 (by aesop)).imp fun u ⟨h,j⟩↦⟨h,(c.2 (by aesop)).imp fun v ⟨k,l⟩↦⟨k,j,l,by simpa using (hasMatSize_box _ l).sub (hasMatSize_box _ j)⟩⟩)
   b d fun a h↦(Set.not_subset.1 (m ⟨a,h,measure_mono ·⟩)).elim fun c ⟨d,r⟩↦⟨.mk0 c (r <| by simp [·];bound),d,by simp [RealPlaceSizes.gauge] at r ⊢;grw [← r,inv_inv]⟩)⟩
lemma lintegral_formMajorant_ne_top [Nonempty I] : ∫⁻ x,hF.complexLevel.formMajorant j p q F F x ∂hF.complexLevel.groupMeasure ≠ ∞ := (hF.exists_gauge_isHead j p q 0).elim fun _ ⟨_,a,b,_⟩ z↦(z▸hF.qS hj hF.z2.1 (by simp [hF.lintegral_sq_cut_le]) zero_le_one a b hF.z2.isNear_of_ne_zero le_rfl le_rfl (by simp)).not_gt
 (by simp [headDensity,v6,prod_eq_zero_iff,toReal_ne_zero,ne_of_gt,vX])
lemma kT [Nonempty I] (y:ℂˣ) {ω} (hω:∀ x,‖ω x‖≤ 1) (h:∀ Γ:Gauge hF.complexLevel,Γ.IsHead j p→ ∀ {x},hF.complexLevel.formModulus j p q F x ω^2≤ (complexPlace.c/complexPlace.md y)^card {i // i≠𝔰.k₀}*Γ.selfNormProduct j p q F F x):‖hF.v6*hF.complexLevel.floorForm j p q F ω‖≤ 𝔰.bandConst*b^(2000*𝔰.n^9)*dampedPower (𝔰.k-𝔰.n^7) ‖y.1‖⁻¹*(headWeight (𝔰.n^6) j p*headWeight (𝔰.n^6) j q):=by
 obtain ⟨⟨_,_,hp,hq,Z⟩,c,_,_,_,⟨_,N⟩,K,k⟩:=hF.exists_gauge_isHead j p q (𝔰.n^6),hF.z2,hF.wA,y.norm_pos,hF.two_le_b,exists_add_of_le hF.ten_pow_le_varrho,exists_add_of_le hF.pow_seven_le_k;grw [← ofReal_le_ofReal_iff,ofReal_norm,enorm_mul,enorm_floorForm_le]
 obtain z | Z:=not_or_of_imp (Z (ρ^(9*𝔰.n)) (by bound))
 have:=(formMajorant_sq_le _ c c.1 hj hp (x := ·) ⟨⟩ (σ:=0) (by tauto) le_top c.isNear_of_ne_zero fun _ _ _ u v↦z.elim fun l m↦⟨minors_mem_ofSize hF.gauge.hasMatSize_box hj u (c.isNear_of_ne_zero (by aesop)).choose_spec l m,minors_mem_ofSize hF.gauge.hasMatSize_box hj v (c.isNear_of_ne_zero (by aesop)).choose_spec l m⟩)
 simp_all [hF.vY,hF.mul_cube_lt_s.ne_zero,(c.formModulus_le_formMajorant _).antisymm]
 let t:=1⊔ρ^24*‖y.1‖
 grw [hF.qS hj c.1 (by simp [hF.lintegral_sq_cut_le]) zero_le_one hp hq c.isNear_of_ne_zero le_sup_left (fun _↦c.formModulus_le_formMajorant hω) fun m ↦ ?_,(?_:_*_≤ 𝔰.n^6),Z,← (?_:9900000*𝔰.n^3+(K+6)≤ s),hj,dampedPower,k,← (by simp [field,t]:ρ^24/t≤ _⁻¹),← (by simp [field,t];bound:t⁻¹≤ 1⊓_)];gcongr 1;simp [field,pow_add,div_pow,hF.rho_eq];ring_nf;simp [mul_assoc,← pow_add];gcongr
 any_goals first | clear Z;delta headWeight dampedPower bandConst volU;positivity
                 | rw [hF.k_eq,Shape.n,N] at *;lia | bound
 grw [h _ hp,hF.vY.ge.trans tsub_le_self,max_eq_right (by grind)]
 gcongr 1;simp (disch:=finiteness) [← ofReal_norm,← toReal_le_toReal,div_pow,field];ring_nf;repeat bound [two_le_pi]
end IsCutBessel
end
section
open Matrix MeasureTheory Measure Fintype Real ENNReal InnerProductSpace Finset IsCutBessel Function Norms.L2Operator Level Gauge
variable {𝔰:Shape} {s I} [Fintype I] {rep ρ b n} {F W:C(𝔰.G₁,EuclideanSpace ℂ I)} (hF:IsCutBessel F rep ρ s b W n) {p}
variable (F) in
private noncomputable def j2 p:=normCorrelation (cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ)) F p
include hF
attribute [local simp] weylRatio ContinuousLinearMap.inner_map_map_of_mem_unitary upperPairing Unitary.map_mem cellDensity sqrt_eq_zero' abs_of_pos normCorrelation embedH_mem_floorGroup cellChart_mem weylElem_mul_left_comm
lemma IsCutBessel.v1:Continuous (j2 F) := .of_at fun p↦by
 choose L _ a _ using hF.exists_gauge_isHead _ p p 0
 refine have:Continuous fun c:(_→ ℂˣ) × 𝔰.G₁↦cellChart 𝔰 𝔰.ϱ (c.1 𝔰.ϱ):=continuous_U_iff_matrix.2 (.congr ?_ fun _↦by simp [cellChart,field];rfl);.smul
     (M:=ℝ) ?_ (((PiLp.continuous_toLp ..).comp_continuousOn (continuousOn_pi.2 fun i↦continuousOn_integral_of_compact_support (hF.gauge (by grind:_≤ L+1)).isCompact_hasMatSize ?_ fun c y m↦not_imp_comm.1 fun n↦hasMatSize_of_ne_zero _ hF.z2 m cellChart_mem (n <| ·▸by simp) (n <|
   ·▸by simp))).continuousAt ((Set.finite_Iic _).eventually_all.2 fun i l↦(ContinuousAt.norm ?_).eventually_le_const ((a i l).trans_lt (by simp)))) <;> fun_prop (disch:=simp [ne_of_gt])
lemma hasBandLimits_of_isCutBessel [Nonempty I] {deg} (hd:0< deg) (hS:SchurLe W (.ofReal deg⁻¹*card I)) (hD:deg*𝔰.bandConst≤ b^(4*𝔰.r^2)):∃ J,HasBandLimits b F deg J:=by
 let δ:=hF.complexLevel.upperPairing 0 (translatePairing F W 1) 1
 obtain ⟨c,Γ,⟨_,_,a⟩,⟨_,_,d⟩,hW,b2,_,B,_,v,H,l⟩:=hF.z2,hF.gauge,hF.z2.1.1,(hF.isBesselFunction .full).1,hF.isBesselFunction .full,hF.two_le_b,hF.k_eq,hF.isBesselFunction .cut,hF.vX;choose _ _ x y _ using (hF.exists_gauge_isHead 𝔰.ϱ · · 0)
 refine ⟨fun i p q↦ite (i≤ 𝔰.ϱ) (hF.v6*hF.complexLevel.floorForm i p q F 1) ⟪j2 F p,j2 F q⟫_ℂ,⟨by simp [wave],fun i p q ξ hi ↦
   .imp_right (fun e↦⟨(e.trans <| by simp [·,hi,Pi.one_def]),((congrArg _ e).trans_le <| hF.kT hi ·.unit (by simp) (·.formModulus_sq_le_of_char c hi · ⟨⟩ fun _ _↦rfl))⟩) ?_,fun _ _ _↦by simpa using! posSemidef_gram ..,by
   simpa using! hF.v1.fst'.inner hF.v1.snd',fun p q ↦ ?_,
   fun i p q h y↦ite_eq_left h▸hF.kT h y.unit (by simp)
   (·.formModulus_sq_le_of_heads c h · ⟨⟩ rfl (by simp))⟩,fun σ h p q e f↦by
   by_cases! t:‖(p 𝔰.ϱ).1‖≤ 1
   simp [j2, *]
   obtain ⟨k,k',rfl⟩:=cartan_decomposition h e t;simp [j2, *,inner_besselCorrelation _ c F.2 (x p q)]
   nth_rw 2 [← integral_mul_left_eq_self _ (embedH k,embedH k)];simp [mul_assoc,← map_inv _ k',-map_inv,B.3,weylElem_mul_left_comm]⟩
 obtain h | rfl:=hi.lt_or_eq;simpa [h] using Γ.integral_floorForm_succ c ⟨i,h⟩ _ ξ (hF.lintegral_formMajorant_ne_top hi)
 refine v0 Γ c 𝔰.top ξ (hF.lintegral_formMajorant_ne_top hi)
   (hF.complexLevel.measureH_spec.1.mono unitriGroup_inf_floorGroup_last.ge) (by simp)
   ((ite_eq_right (by simp)).trans (ite_eq_left rfl)) (Place.ae_isUnit.mono fun
     | _,⟨z,rfl⟩ => ?_)
 by_cases! hl:‖z.1‖≤ 1;simp [j2, *]
 erw [← stackMeasure_top,(by simp [descConv_add]:_∗ₘ_=hF.complexLevel.groupMeasure),v]
 simp [j2,inner_besselCorrelation _ c F.2 (x p q) (y p q),prod_smul_left,prod_smul_right,realFrameGram_cellChart hl,mul_left_comm _ (wave _),← mul_assoc _ _ (integral ..)]
 rw [← (measurePreserving_prod_mul_swap ..).hasLaw.integral_comp (by fun_prop)]
 norm_cast;congr 3
 simp [headDensity,prod_range,ne_of_lt,← toReal_rpow,← one_div,← sqrt_eq_rpow,mul_pow,posPart_def];rw [toReal_ofReal (by positivity)]
 grind [v6,toReal_ne_zero,Shape.openCellConst,𝔰.openCellConst_pos,pow_right_comm]
 simp (disch:=fun_prop) [formIntegrandOne,descConv,integral_map];simp [mul_assoc,weylElem_mul_left_comm,B.3]
 have K {B} h:=by simpa using Γ.zB (W':=B) c h 0 1 1
 obtain ⟨k,k',V⟩:=K c.1,@K W ⟨hW.1,by simpa using hW.2⟩,(⟨⟨by fun_prop,_,
   (norm_sub_le_of_le (a _) <| d ·)⟩,by simp_all [hW.2,B.2,smul_sub]⟩ :
   Place.IsBessel (⇑F - ⇑W) 1)
 grw [ite_eq_left,add_div,one_div,← ofReal_le_ofReal_iff,ofReal_add,← (?_:2*_≤ _/deg),ofReal_mul,← hF.qS zero_le V hF.lintegral_sq_sub_le _ _ _ (fun {y} _↦⟨y⁻¹,by simp [hF.wA.trans']⟩) le_rfl le_rfl,ofReal_norm,enorm_mul,enorm_floorForm_le,lintegral_mono fun x↦(?_:_≤ ‖δ x‖ₑ^2+2*hF.complexLevel.formMajorant 0 p q F (F-W) x),lintegral_add_left,lintegral_const_mul',headDensity,prod_range_zero,one_mul,mul_add,mul_left_comm _ 2,v,lintegral_smul_measure,lintegral_le_of_forall_fin_meas_le (hF.j9^2*card I*(.ofReal deg⁻¹*card I)) fun s hs h ↦ ?_,show _*_≤ .ofReal deg⁻¹ by simpa [← toReal_le_toReal,field,v6,mul_eq_top,le_of_lt, *] using l]
 any_goals first | finiteness | fun_prop | simp [Size.IsHead,Size.zero_one_mem_ofSize]
 obtain ⟨⟨D,d,f⟩,_⟩:=k'.exists_lintegral_le 0,Fact.mk h.lt_top;let β:=s.indicator (star δ)
 have m q:MemLp β q:=(memLp_indicator_iff_restrict hs.nullMeasurableSet).2
   (.star (.of_enorm_bound (by fun_prop) d.ne (.of_forall ((enorm_integral_le_lintegral_enorm _).trans <| f 1 ·))));have i:=memLp_one_iff_integrable.1 (m 1);have e:=lintegral_enorm_sq i (m ⊤)
 grw [setLIntegral_mono' hs (g:=(‖β ·‖ₑ^2)) (by simp +contextual [β]),restrict_le_self,← ENNReal.mul_div_cancel_right' id (e.trans_ne coe_ne_top).elim,div_le_of_le_mul]
 grw [← sq,mul_assoc,mul_assoc,← hS _ i,← hF.lintegral_sq_cut_le,← sq_lintegral_le (by fun_prop) (Measurable.aemeasurable (by fun_prop)) fun z↦(mul_pow ..).le,← mul_pow,← H _ (by fun_prop) (by simp +contextual [B.enorm_besselS_mul (mem_unitriGroup_of_mem_besselU _),hW.enorm_integral_besselS_mul (mem_unitriGroup_of_mem_besselU _)]),e,ofReal_le_enorm,← Complex.ofRealLI.enorm_map,← LinearIsometry.integral_comp_comm,integral_congr_ae (.of_forall fun x ↦ .trans (b:=β x*δ x) (by by_cases x∈s <;> simp [β, *,RCLike.conj_mul]) (integral_const_mul ..).symm),integral_integral_swap ⟨by fun_prop,
   (lintegral_prod_le _).trans_lt ?_⟩,enorm_integral_le_lintegral_enorm]
 gcongr;simp [← inner_smul_right,integral_inner,hW.integrable_smul i,enorm,← ENNReal.coe_mul,nnnorm_inner_le_nnnorm]
 simp_rw [uncurry,enorm_mul,lintegral_const_mul' _ _ enorm_ne_top]
 grw [f,lintegral_mul_const'] <;> finiteness [i.2]
 simp [formModulus,formMajorant,descConv,← formIntegrandOne_eq Γ c]
 grw [← k.enorm_upperPairing_le,← (K V).enorm_upperPairing_le,Eq.trans (a:=δ x) (by simp [δ]) (integral_sub (k.jE 0 1 x) ((K V).jE 0 1 x)),← toReal_le_toReal,toReal_add] <;> simp [formIntegrandOne,mul_ne_top]
 grw [← abs_norm_sub_norm_le,sq_abs,sub_sq];nlinarith
 grw [(le_div_iff₀' hd).2 hD,b2];simp [hF.rho_eq,field,← pow_mul,← pow_add, *];gcongr;any_goals bound [hF.wA]
 clear * - hF;obtain ⟨_,rfl⟩:=hF.mul_cube_lt_s.dest;lia
end
