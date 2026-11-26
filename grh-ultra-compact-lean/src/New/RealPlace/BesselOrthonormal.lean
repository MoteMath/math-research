import Lib.General.Analysis.HolomorphicIntegral
import New.RealPlace.FrameNorm
import Lib.DiscreteSeries.Bessel.BesselNormInvariance
import Lib.DiscreteSeries.Bessel.RealMeasures
noncomputable section
open Matrix Function Fin Metric Real Complex Norms.L2Operator Shape
variable {𝔰:Shape} (x) (Z:𝔰.FrameMat)
def jU:=Z⁻¹ 𝔰.top 𝔰.top
def Shape.j1:={Z:𝔰.FrameMat | det Z≠0∧‖jU Z‖< 1}
def zM:=1-‖jU Z‖^2
def jP P:=Z∈j1∧‖Z⁻¹‖≤ P∧‖Z‖≤ P∧(√(zM Z))⁻¹≤ P
def s21_z3:𝔰.FrameMat:=diagonal (snoc 1 x)
variable (W:=Zᴴ) (s:=(1-jU Z*jU W).sqrt)
def s21_z6:=s21_z3 (𝔰:=𝔰) 0-1-s21_z3 (𝔰:=𝔰) 0*W⁻¹*(1-s21_z3 (𝔰:=𝔰) 2⁻¹)*Z⁻¹*s21_z3 (𝔰:=𝔰) 2
def qY:=(𝔰.frameCols*s21_z6 Z W+𝔰.dualFrameCols * @s21_z3 𝔰 s)*Z
def zG:=1+(qY Z W-𝔰.frameCols)*𝔰.frameColsᴴ+((𝔰.frameCols*W⁻¹-qY Z W*s21_z6 W Z) * @s21_z3 𝔰 s⁻¹-𝔰.dualFrameCols)*𝔰.dualFrameColsᴴ
variable {Z} (h:Z∈𝔰.j1)
attribute [local simp] gramDiscReal frameDisc zM mul_conj' forall_fin_succ' s21_z3 l2_opNorm_conjTranspose j1 jU dist_eq_norm isUnit_iff_isUnit_det slitPlane_ne_zero mem_slitPlane_of_norm_lt_one Complex.sqrt
attribute [local simp ←] conjTranspose_nonsing_inv ofReal_pow
lemma vP (h:det Z≠0):gramDiscReal Z=‖det Z‖^2*zM Z:=by
 simp [Z.inv_def,adjugate_fin_succ_eq_det_submatrix',field];rfl
lemma jD:Z∈j1↔0< gramDiscReal Z:=by by_cases Z.det=0 <;> simp_all [↓vP]
@[fun_prop] lemma kY:Continuous (@gramDiscReal 𝔰):=by fun_prop [gramDiscReal,frameDisc,leadingMinor]
lemma jO:IsOpen 𝔰.j1:=Set.ext (@jD 𝔰)▸isOpen_Ioi.preimage kY
include h
lemma qI (o:W∈j1):DifferentiableAt ℂ (zG · ·).uncurry (Z,W):=by
 repeat erw [differentiableAt_pi] <;> intro
 have:∀ i j,Differentiable ℂ (@s21_z3 𝔰 · i j):=by simp [diagonal,eq_comm]
 have:=mul_lt_mul'' h.2 o.2
 simp_all only [uncurry,zG,qY,s21_z6,jU,nonsing_inv_eq_ringInverse,mul_apply,Matrix.add_apply,sub_eq_add_neg,Matrix.neg_apply];fun_prop (disch:=simp_all)
lemma vA:0< zM Z:=by aesop
@[simp] lemma wP:(1-jU Z*jU Zᴴ).sqrt = √(zM Z):=by simp_all [sqrt_eq_rpow,ofReal_cpow,le_of_lt]
lemma qF:DifferentiableAt ℝ zG Z := .comp Z (f:=fun Z↦(Z,star Z))
 ((qI Zᴴ h (by simpa)).restrictScalars ℝ) (by fun_prop)
omit h in
private lemma k6 {P r} (hr:0< r) (hP:8≤ P) (H:∀ y∈ball Z r,jP y P):‖zG Z‖≤ P^12∧‖fderiv ℝ zG Z‖≤ 2*P^12/r :=
 have b {x y} (hp:(x,y)∈ball (Z,Zᴴ) r):_∧‖zG x y‖≤ P^12:=by
   simp [jP,← (y-_).l2_opNorm_conjTranspose] at hp H
   obtain ⟨⟨o,_,_,q⟩,_,o',_,-⟩:=H _ hp.1,(by simp [pi_norm_le_iff_of_nonempty] :
     ∀ s,‖s21_z3 (𝔰:=𝔰) s‖≤ 1+‖s‖),by simpa using H _ hp.2
   use qI _ o o';delta zG qY
     s21_z6;trans;repeat' first
     | apply_assumption (transparency := .reducible) [mul_le_mul_of_nonneg,norm_add_le_of_le,norm_sub_le_of_le,jM,(l2_opNorm_mul ..).trans] | positivity | simp [Injective,norm_cpow_of_imp,← by simpa using sqrt_eq_rpow] | rfl
   grw [← (_:4⁻¹*zM x≤ ‖_‖),norm_sub_le,norm_mul,o.2,o'.2,sqrt_le_self_iff.2] <;> simp [o];grw [q,← sub_nonneg]
   obtain ⟨t,_,rfl⟩:=exists_nonneg_add_of_le hP;ring;bound;grw [← norm_sub_norm_le,norm_mul,o'.2,norm_one];nlinarith
 ⟨(b (by simpa)).2,norm_fderiv_le_of_lip' ℝ (by bound) (.mono (ball_mem_nhds Z hr) fun y ↦
   by simpa [two_mul,← conjTranspose_sub] using norm_sub_le_of_holomorphic_bdd (Prod.rec @b) (y,yᴴ))⟩
end
section
open Matrix Complex Fin IsHermInvolution MatMul
variable {𝔰:Shape} {Z:𝔰.FrameMat} (h:Z∈𝔰.j1)
attribute [local simp] sum_univ_castSucc diagonal_apply Matrix.mul_apply actOnCols s21_z3 splitGram middleGram inclMatrix vA Real.sqrt_eq_zero' frameGram prod_univ_castSucc conjTranspose_nonsing_inv Fin.ne_of_gt isUnit_iff_isUnit_det forall_fin_succ'
attribute [local simp ←] ext_iff
attribute [-simp] fromCols_mul_fromBlocks conjTranspose_fromCols_eq_fromRows_conjTranspose
lemma jW:zG Z*𝔰.frameCols=qY Z:=by simp [zG]
lemma jS:𝔰.frameColsᴴ*𝔰.J₁*(zG Z*𝔰.frameCols)=Z:=by simp [↓jW,qY];simp [s21_z6]
noncomputable def zL (Z:𝔰.FrameMat):𝔰.G₁:=U.of isUnit (if Z∈𝔰.j1 then zG Z else 1) (by
 split_ifs with h;swap;simp
 let C:=fromCols 𝔰.frameCols 𝔰.dualFrameCols;let J:=Cᴴ*𝔰.J₁*C;let Δ := @s21_z3 𝔰 (√(zM Z))⁻¹
 obtain ⟨d,a,b⟩:=vA h,(by simp [C,J];lia:Cᴴ*C=1∧𝔰.J₁=actOnCols C J)
 let x:=fromBlocks Z⁻¹ (s21_z6 Zᴴ Z*Δ) 0 (1:𝔰.FrameMat)
 let y:=fromBlocks (s21_z6 Z) (Zᴴ⁻¹*Δ) (s21_z3 √(zM Z)) 0;have e :
   yᴴ*J*y=xᴴ*J*x:=by
                          simp +zetaDelta [s21_z6,map_ofNat,← ofReal_pow,d.le,d.ne',← conjTranspose_nonsing_inv,field];simp [zM,jU];grind [conj_mul']
 rw [(by simp [x,y,C,Δ,inv_fromBlocks_zero₂₁_of_isUnit_iff',h,h.1,-ext_iff,zG,qY,conjTranspose_fromCols_eq_fromRows_conjTranspose];abel:zG _ =
   actOnCols C (y*x⁻¹))]
 simpa [↓b,mul_mul_eq_of_mul_eq a,x,h.1,-ext_iff] using congr(actOnCols C (x⁻¹ᴴ * $e*x⁻¹)))
@[fun_prop] lemma wR:Measurable (@zL 𝔰) := .subtype_mk (measurable_comap_iff.2 (by
 exact ContinuousOn.measurable_piecewise (@qF _ · · |>.continuousAt.continuousWithinAt) (by fun_prop) jO.measurableSet))
include h
private lemma v3 : @s21_z3 𝔰 √(zM Z)*s21_z3 (√(zM Z))⁻¹=1:=by aesop
lemma qM:(zL Z).1.1=zG Z:=ite_eq_left h
lemma vK:(zL ·|>.1.1) =ᶠ[nhds Z] zG := .mono (jO.mem_nhds h) (@qM _)
lemma zN:realFrameGram (zL Z)=Z:=by simpa [qM h] using jS (Z:=Z)
lemma jK {γ} (y:realFrameGram γ=Z):∃ q k r l,γ=unipotentOf q*embedH k*zL Z*(unipotentOf r*embedH l)⁻¹:=by
 have A {s} (z:realFrameGram s=Z):(framePair s)ᴴ*𝔰.J₁*framePair s=fromBlocks (s21_z3 0-1) Z Zᴴ
   (s21_z3 0-1):=by simpa [← z] using congr(submatrix $(s.2) 𝔰.besselFrame 𝔰.besselFrame)
 have B {s} z:=HasLeftInv.of_isUnit_gram (isUnit_of_mul_isUnit_right (x:=fromBlocks 0 Zᴴ⁻¹ Z⁻¹ 0) (by rw [@A s z];simp [h.1];rw [det_of_isUpperTriangular] <;> simp [BlockTriangular,conj_mul',← conjTranspose_nonsing_inv] <;> norm_cast <;> grind [vA h,zM,jU]))
 obtain ⟨g,e⟩:=witt ⟨I,by simp⟩ isHermitian isUnit (B y) (B (zN h)) (A (zN h)▸A y)
 simp [fromCols_ext_iff,← mul_inclMatrix,-inclMatrix,-ext_iff] at e
 obtain ⟨⟨q,k,a⟩,p,l,b⟩:=exists_embedH_eq_of_fix_frameCols e.1,@exists_embedH_eq_of_fix_frameCols _ ((zL Z)⁻¹*g*γ) (by simp [e,-inclMatrix])
 use q,k⁻¹,p,l⁻¹,by simp_rw [map_inv,← a,← b];group
end
section
open Fin Module Complex Finset HasGaussianIntegral Haar MatMul Matrix MeasureTheory Sum Norms.L2Operator
private noncomputable def z5 {𝔰:Shape}:=fun (Z,θ,q,η,r)↦unipotentOf q*embedH
   (cayleyChart 1 (skewColumnEquiv 𝔰.k₀ (θ,0)))*zL Z *
 (unipotentOf r*embedH (cayleyChart 1 η))⁻¹
set_option synthInstance.maxSize 999
attribute [-simp] Prod.forall map_mul _root_.mul_inv_rev
attribute [local simp] forall_fin_succ' coe_embedH inclMatrix_gram_eq_zero inclMatrix_gram_mul_eq_zero inclMatrix_gram_eq_one inclMatrix_gram_mul_eq_self actOnCols
 qY zG val_unipotentOf_coe
noncomputable def kS {𝔰:Shape}:=let r i:=inr (inl (ite (i=𝔰.k₀) (inr ()) (inl i)))
 let R S w d:=((skewCoords S).submatrix w w,S.submatrix d w,(skewCoords S).submatrix d d)
 (⟨⟨fun S↦(𝔰.dualFrameColsᴴ*S*𝔰.frameCols,((skewColumnEquiv 𝔰.k₀).symm (R S r inl).1).1,(R S r inl).2,-R S 𝔰.indexX₀ eStar),by simp [R,submatrix_add,↓neg_add,-skewColumnEquiv_spec]⟩,by simp [R,submatrix_smul,-skewColumnEquiv_spec]⟩:_ →ₗ[ℝ] _)
noncomputable def qG {𝔰:Shape}:=(.mk ⟨⟨fun (η,b,c)↦(𝔰.definiteCols*η+𝔰.dualCols*b)*𝔰.definiteColsᴴ+(𝔰.dualCols*skewOfReal c-𝔰.definiteCols*bᴴ)*𝔰.dualColsᴴ,by
   simp;grind⟩,by simp [star_trivial,smul_sub]⟩:Matrix 𝔰.κ _ ℂ × 𝔰.UnipotentParams →L[ℝ] _)
private lemma q3 {𝔰:Shape} {V} [NormedAddCommGroup V] [NormedSpace ℝ V] {z':V →L[ℝ] _ × 𝔰.UnipotentParams} {z p} (hz:HasFDerivAt z z' p):let F p:=unipotentOf (z p).2*embedH (cayleyChart 1 (z p).1);DifferentiableAtU F p∧∀ v,
   let (η,b,c):=z' v;logDerivU F p v=qG (logDerivU (cayleyChart 1) (z p).1 η,b*(cayleyChart 1 (z p).1).1.1,c+skewCoords (skewAdjointPart ℝ ((z p).2.1*bᴴ))):=by
 have h:=(qG ∘L .inr ..).hasFDerivAt.comp p hz.snd |>.const_mul 𝔰.J₁
 refine (fun h↦⟨⟨_,h⟩,(congr(_ * $h.fderiv ·).trans ?_)⟩) ((((h.add ((h.mul' h).const_smul (2⁻¹:ℂ))).const_add 1).mul' (((qG ∘L .inl ..).hasFDerivAt.comp p (((abs_det_logDerivU_cayleyChart (det_cayleyDenom_one_ne_zero _)).1.hasFDerivAt.comp p hz.fst).sub_const 1)).const_add 1)).congr_of_eventuallyEq (.of_forall fun _ ↦ ?_)) <;> simp [qG,-map_sub,star,J₁_eq,logDerivU] <;> module
lemma vC {𝔰}:∃ e:_ ≃ₗ[ℝ] _,MeasurePreserving e ∧ ⇑e.symm = @kS 𝔰∘ₗskewOfReal:=by
 apply exists_measurePreserving_equiv;simp_intro _ [kS,mul_inclMatrix,conjTranspose_inclMatrix_mul];simp [skewOfReal,sum_univ_castSucc,div_pow,Fintype.sum_eq_add_sum_subtype_ne _ 𝔰.k₀,RCLike.norm_sq_eq_def];ring_nf;simp [sum_add_distrib,@sum_comm (Fin _) _ (@Subtype 𝔰.κ _)];nth_rw 2 [sum_comm];ring;simp [finrank_matrix];grind [@Fintype.card_pos _ _ ⟨𝔰.k₀⟩]
lemma kZ {𝔰:Shape}:∃ e:_ ≃ₗ[ℝ] _,MeasurePreserving e∧∀ p∈𝔰.j1 ×ˢ Set.univ,DifferentiableAtU (@z5 𝔰) p ∧
 |(e.symm.1∘ₗskewCoords∘ₗlogDerivU z5 p).det| = gramDiscReal p.1^(𝔰.k-1) *
 (cayleyDensity 1 (skewColumnEquiv 𝔰.k₀ (p.2.1,0))*cayleyDensity 1 p.2.2.2.1):=by
 cases Nat.exists_eq_add_of_lt (@Fintype.card_pos _ _ ⟨𝔰.k₀⟩)
 refine vC.imp fun e ↦ .imp_right fun _ p ⟨hp@⟨_,_⟩,_⟩ ↦ ?_;obtain ⟨⟨_,hγ⟩,s⟩:=qF hp,hasStrictFDerivAt_snd (𝕜:=ℝ) (p:=p);obtain ⟨⟨a⟩,b,γ,d⟩:=q3 (((skewColumnEquiv _).hasStrictFDerivAt.comp p (s.fst.prodMk (hasStrictFDerivAt_const ..))).prodMk s.snd.fst).hasFDerivAt,q3 s.snd.snd.hasFDerivAt,(hγ.congr_of_eventuallyEq (vK hp)).comp p hasFDerivAt_fst,vA hp;extract_lets F at b
 have h:DifferentiableAtU z5 p:=(a.mul ⟨_,γ⟩).mul
   (by simpa only [Ring.inverse_unit] using! b.1.inverse ⟨_,rfl⟩)
 let Δ := @s21_z3 𝔰 (√(zM p.1))⁻¹;let R:=1+𝔰.dualFrameCols*(𝔰.frameCols-𝔰.dualFrameCols)ᴴ
 let M A B:=𝔰.frameCols*((A*Δ-1)*𝔰.frameColsᴴ+B*Δ*𝔰.dualFrameColsᴴ)
 let K:=1+M p.1⁻¹ (s21_z6 p.1ᴴ)
 have:(zL p.1).1.1*K=R+M (s21_z6 p.1) p.1ᴴ⁻¹:=by
   simp +zetaDelta [qM, *,mul_mul_eq_of_mul_eq (v3 _)];abel
 have q v A B:qG v*M A B=0∧(M A B)ᴴ*qG v=0:=by simp [M,qG]
 have t:=abs_det_skew_congruence e.symm (F p*K) (skewCoords∘ₗlogDerivU z5 p)
 generalize hT:(e.symm.1∘ₗ_:End ..)=T at t
 have hT w:T w=_ := .trans (by simp [← hT,conjTranspose_logDerivU, *])
   congr(kS (Kᴴ * $(sub_eq_of_eq_add (logDerivU_mul h b.1 w))*K)).symm
 simp [z5,logDerivU_mul a ⟨_,γ⟩, *,F,(logDerivU.eq_1 ..).trans congr(_ ∘ₗ $γ.fderiv.1),mul_mul_eq_of_mul_eq (conjTranspose_mul _ K).symm,mul_mul_eq_of_mul_eq (q ..).2] at hT;rw [det_mul,det_one_add_mul_comm,det_eq_mul_of_block_triangular,det_eq_mul_of_block_triangular,abs_mul,abs_mul,det_mulLeft_mulRight_real (p.1ᴴ⁻¹*Δ)ᴴ (p.1⁻¹*Δ),abs_det_logDerivU_col_eq_cayleyDensity,← LinearMap.det_conj _ (.prodAssoc ..),det_eq_mul_of_block_triangular,det_mulLeft_mulRight_real 1 (cayleyChart 1 (skewColumnEquiv _ (p.2.1,0))).1.1,det_eq_mul_of_block_triangular 1,det_eq_mul_of_block_triangular (skewCoords∘ₗlogDerivU (cayleyChart 1) p.2.2.2.1),det_eq_mul_of_block_triangular _ _ (LinearMap.id.ext _),det_mulLeft_mulRight_real 1 (cayleyChart 1 p.2.2.2.1).1.1] at t;simpa [abs_det_logDerivU_cayleyChart,mul_pow,pow_mul,Δ,s21_z3,d.le,abs_of_pos, *,vP,prod_univ_castSucc,pow_add,field] using t.symm
 all_goals simp [*,K,kS,Prod.mk_zero_zero,LinearEquiv.prodAssoc]
 rotate_right;exact fun _ ↦ .trans (by simp [R,M,qG]) congr(_*(_*($(((mulLeftLinearMap .. ∘ₗ mulRightLinearMap ..).toContinuousLinearMap.hasFDerivAt.comp _ hγ).unique ((hasFDerivAt_id _).congr_of_eventuallyEq (.of_forall (@jS _)))) _*_)))
 all_goals simp [entrywise,@skewCoords.eq_1 𝔰.BesselIndex,inclMatrix,-re_sum,-im_sum,R,skewOfReal,sum_univ_castSucc,-Matrix.mul_sub,-Matrix.add_mul];clear * -;simp [qG,inclMatrix,mul_apply,-map_add] <;> first | (intros;simp [skewOfReal];grind) |
   aesop (add simp skewCoords)
private lemma k7 {𝔰:Shape}:(𝔰.j1 ×ˢ Set.univ).InjOn z5:=by
 have u:(fun q↦(@unipotentOf 𝔰 q).1.1*𝔰.dualCols).Injective:=fun _ _ e↦by
   simpa [by simpa using congr(𝔰.definiteColsᴴ * $e),
     Prod.ext_iff] using congr(skewCoords (𝔰.isotropicColsᴴ * $e))
 rintro ⟨Z,_,q,_,r⟩ ⟨hZ⟩ ⟨_,_,p,_,s⟩ ⟨⟩ e
 cases by simpa [z5,realFrameGram_mul_invariant,zN,Subgroup.mul_mem_sup,unipotentOf_mem_besselU0, *] using congr(realFrameGram $e)
 have c {x g} (e:z5 (Z,x)=g):=by
   simpa [qM,hZ.1,hZ,v3] using congr($(eq_mul_of_mul_inv_eq e).1.1*(𝔰.frameCols*Z⁻¹ * @s21_z3 𝔰 (√(zM Z))⁻¹))
 obtain ⟨this,e1⟩ := @u q p,(c e).trans (c rfl).symm;simp [entrywise,inclMatrix,forall_and] at e1 this;simp [z5,cayleyChart_col_injective _ (funext e1.2.2),e1.1.elim this] at e ⊢
 simp_all [@u r s,by simpa [Units.val_inj,cayleyChart_injOn.eq_iff] using congr(𝔰.definiteColsᴴ * $e.1.1*𝔰.definiteCols)]
open Real Fintype Metric
lemma s21_q8 {𝔰 M P Z Z'} (hg:M⁻¹≤ @gramDiscReal 𝔰 Z) (hM:8*(𝔰.ϱ+1)≤ M) (hZ:∀ a b,‖Z a b‖≤ M^2) (hP:M^(9*𝔰.n)≤ P) (h:Z'∈ball Z (P^6)⁻¹):gramDiscReal Z/2≤ gramDiscReal Z'∧jP Z' P:=by
 have ⟨r,m,_,_⟩:𝔰.n≤ M∧2≤ M∧M≤ P∧1≤ P:=by grind [le_self_pow₀]
 have p n:=hP.trans'∘pow_le_pow_right₀ (m:=n) (by grind)
 have k:=h.out.trans_le (c:=1) (by bound)
 have z {Y} (h:dist Y Z< 1) a b:‖Y a b‖≤ M^3:=by
   grw [norm_le_insert',hZ,← Y.sub_apply,norm_apply_le_l2_opNorm,← dist_eq_norm];nlinarith
 have s l:=(abs_norm_sub_norm_le ..).trans ((norm_sub_le_of_holomorphic_bdd (f:=(leadingMinor · l^2)) (fun _ _↦⟨by simp [leadingMinor,det_apply];fun_prop,by grw [norm_pow,leadingMinor,norm_det_le_norm_pow,l2_opNorm_le_of_apply (by tauto),← sq,Fintype.card_fin,mul_pow,← pow_mul,← pow_mul,p,l.is_le,r,p] <;> lia⟩) _ k).trans (c:=M⁻¹/4) (by grw [mem_ball_iff_norm.1 h];field;nlinarith))
 have ⟨g,a⟩:gramDiscReal Z≤ 2*gramDiscReal Z'∧0< gramDiscReal Z':=by
   simp_all [Fin.forall_fin_succ',gramDiscReal,leadingMinor,frameDisc,mul_conj',← ofReal_pow];grind [inv_pos]
 have ⟨n,_⟩:=jD.2 a
 grw [g,m,← inv_mul_le_iff₀,← sq,← le_sqrt',vP n,sqrt_mul,sqrt_sq,inv_le_comm₀] at hg
 have d:=hg;grw [mul_le_of_le_one_right] at d;rw [mul_inv,inv_mul_le_iff₀] at hg
 simp [jP,Z'.inv_def,norm_smul,jD];grw [d,l2_opNorm_le_of_apply (by
   simp_intro .. [adjugate_fin_succ_eq_det_submatrix']
   grw [norm_det_le_norm_pow,l2_opNorm_le_of_apply (by tauto),← sq,Fintype.card_fin,𝔰.ϱ.le_succ,r]),
   hg,norm_det_le_norm_pow,l2_opNorm_le_of_apply (z k),← sq,Fintype.card_fin,r]
 ring;repeat first | bound | simp [*,zM,← pow_add]
lemma euclidean_enorm_sq_eq_sum {I} [Fintype I] (u:EuclideanSpace ℂ I):‖u‖ₑ^2 = ∑ i,‖u i‖ₑ^2:=by simp [enorm,u.nnnorm_eq,← ENNReal.coe_pow]
end
section
open Matrix MeasureTheory Complex Subgroup ComplexConjugate
lemma BesselSystem.orthonormal {𝔰 b f} (B:BesselSystem 𝔰 b f) i j : ∫ y,B.W .full y i*conj (B.W .full y j) ∂besselQuotMeasure=ite (i=j) 1 0:=by
 obtain ⟨⟨a,h2,_⟩,⟨⟩⟩:=B.tail,B.tail.isBesselFunction .full
 have {i j}:=(h2.eval_piLp i).mul_of_top_left ((a .full).memLp_top.eval_piLp j).star
 simp [Pi.mul_def] at this
 apply (B.irreducible (of _) fun s ↦ .symm ((commute_unitary_iff_star_right_conjugate (by simp)).2 (ext fun i j ↦ .trans ?_ (identDistrib_orbitMeasure_comp (measurePreserving_conj_bessel mem_besselU besselS_le_normalizer_besselU (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem s))) (measurePreserving_mul_left _ (embedH s)) ?_ ?_).integral_eq))).elim fun c hc↦congr($hc i j).symm.trans (by
     apply_fun trace at hc
     simp_all [← mul_conj',trace,integral_finsetSum,PiLp.norm_sq_eq_of_L2,← ofReal_inj,lintegral_enorm_sq _ (a _).memLp_top,← integral_complex_ofReal]) <;> generalize ⇑(B.W .full) =
   F at *
 simp (disch:=fun_prop) [mul_apply,↓← integral_const_mul,← integral_finsetSum,↓mul_comm]
 repeat simp [smul_def, *,mulVec_eq_sum,mul_conj',← Finset.sum_mul,← mul_assoc,mul_comm,mul_right_comm _ (F _ i)]
end
section
attribute [-instance] MeasurableSingletonClass.toDiscreteMeasurableSpace
open MeasureTheory Measure Shape ENNReal Matrix.Norms.L2Operator Subgroup
set_option synthInstance.maxSize 999
lemma jX {𝔰:Shape} {f L} (hf:Measurable f) (h:∀ k,L≤ ∫⁻ Z in j1,.ofReal (𝔰.openCellConst*gramDiscReal Z^(𝔰.k-1)) * ∫⁻ h,∫⁻ v,∫⁻ u,f (u.1*(embedH k*(zL Z*(v.1*embedH h)⁻¹))) ∂besselHaar₀ ∂𝔰.besselHaar₀):L≤ ∫⁻ γ,f γ:=have ⟨e,he,h_jac⟩ := @kZ 𝔰
 (Haar.lintegral_chart_rotate_le e he (jO.measurableSet.prod .univ) (@k7 𝔰) h_jac).exists.elim fun t e↦by
 grw [← lintegral_mul_left_eq_self f (circleScalar t)⁻¹,← e,← one_mul L,← (by simpa [cayleyDenom] using (lintegral_cayleyDensity_skewColumnEquiv 𝔰.k₀ 0 one_pos) :),← lintegral_mul_const,h (cayleyChart 1 (skewColumnEquiv _ (‹_›,0)))]
 simp (disch:=first | finiteness | with_unfolding_all fun_prop) [volume_eq_prod _ (_ × _),z5,← prod_restrict,lintegral_prod,@lintegral_prod_symm 𝔰.UnipotentParams,lintegral_eq_cayleyChart,besselHaar₀,volU,lintegral_map,← lintegral_const_mul,← mul_assoc,← ofReal_mul,← ofReal_mul',openCellConst];rw [lintegral_lintegral_swap];gcongr;simp [field];repeat fun_prop
lemma qT {𝔰:Shape} {w φ:𝔰.G₁→ _} {K R} (hw:Measurable w) (hφ:Measurable φ) (hwU:besselS.FixesLeft w) (h:∀ y,∫⁻ u,φ (u*y) ∂𝔰.besselHaar₀≤ K) (hR:∀ y,φ y≠0→ ∀ s∈besselU,φ (s*y)≠0→ ∀ a b,‖frameMatrix s a b‖≤ R) (h1:1≤ R) : ∫⁻ y,φ y*w y≤ K * .ofReal ((2*R)^(2*𝔰.n^2)) * ∫⁻ y,w y ∂besselQuotMeasure:=by
 grw [← lintegral_orbitMeasure_lintegral (ν:=𝔰.besselHaar),← lintegral_const_mul];gcongr with y;simp [Subgroup.smul_def,hwU]
 by_cases! e:∀ u:besselU,φ (u.1*y)=0;simp [e]
 rw [lintegral_mul_const,← lintegral_mul_right_eq_self _ e.choose,Shape.besselHaar,lintegral_map,lintegral_prod,← setLIntegral_eq_of_support_subset (s := .pi ⊤ fun _↦Metric.closedBall 0 R) fun x c p _↦(not_forall.1 (c∘lintegral_eq_zero_of_ae_eq_zero ∘ .of_forall)).elim fun u _ ↦ ?_]
 simp [mul_assoc];grw [h,setLIntegral_const,mul_assoc];gcongr;simp (disch:=finiteness)
   [volume_pi,pow_mul,← ENNReal.toReal_le_toReal]
 grw [Real.pi_le_four,Fintype.card_subtype_le];simp [sq];grind;bound
 simpa [frameMatrix_mul,liftUnitri_mem_besselU,mem_besselU0_iff.1,unitriMatrix,p.2] using hR _ e.choose_spec _ (mul_mem u.2.1 (liftUnitri_mem_besselU x)) (by simp_all [mul_assoc]) p.1.1
   p.1.2;repeat fun_prop
open Complex ComplexOrder Fintype Matrix Metric Real Set Norms.L2Operator
lemma vU {𝔰:Shape} {I} [Fintype I] {P c:ℝ} {D rep F} {Z:𝔰.FrameMat} (hP:8*𝔰.r≤ P) (hV:HasSchurBound (I:=I) F rep P D) (hc:0< c) (B:∀ {y},y∈ball Z (P^6)⁻¹→ c≤ gramDiscReal y∧jP y P) {φ:_→ ℂ} (hφ:Measurable φ) (hi:Integrable φ) (hφ':∀ y,φ y≠0→ ‖y.1.1‖≤ P^20) : ∫⁻ ω in {ω | ‖ω.2.1.1.1‖≤ P^20},‖∫ y,φ y•F (zL Z*(ω.2.1*embedH ω.1)⁻¹*y)‖ₑ^2 ∂ENNReal.ofReal (𝔰.openCellConst*c^(𝔰.k-1))•volume.prod 𝔰.besselHaar₀≤ .ofReal (P^(2000*𝔰.n^2))*D * ∫⁻ y,‖φ y‖ₑ^2:=by
 simp [mul_comm] at hP;have ⟨h1,h8,_⟩:1≤ P∧8≤ P ∧ |P| = P:=by grind
 let e:=(basisOneI.smulTower (A:=𝔰.FrameMat) (stdBasis ..)).equivFun.symm.toContinuousLinearEquiv
 obtain ⟨he,he'⟩:MeasurePreserving (Z+e ·)∧∀ x,‖e x‖≤ _*(‖x‖+‖x‖):=by
   use (HasGaussianIntegral.measurePreserving e.1 ?_).add_left ..,fun _↦l2_opNorm_le_of_apply ?_
     <;> simp [e,ite_and,sum_prod_type,stdBasis_eq_single,Matrix.sum_apply,norm_le_pi_norm,← sq,-norm_eq_abs,RCLike.norm_sq_eq_def,norm_add_le_of_le,single_apply]
 choose bg o bi bn _ using fun {y} h↦B (ball_half_subset y h (mem_ball_self (by bound)))
 set Q:=ball Z _
 have hx {x} (h:x∈Icc 0 fun _↦(P^8)⁻¹):Z+e x∈Q:=by
   grw [add_mem_ball_iff_norm,he',← dist_zero_right,dist_le_of_mem_pi_Icc h (by grind)]
   simp [*,field];nlinarith
 let ψ:=List.foldr (fun ((a,b),c,d) ψ y↦ψ y*(y⁻¹.1 a d*y.1 c b/P^40)) φ
 choose _ hψ using (List.rec (by tauto) fun _ _ ⟨h,k⟩↦⟨h.mul (by fun_prop),fun y↦(norm_mul_le_of_le (k y) le_rfl).trans ((em' (φ y=0)).elim (by grw [norm_div,norm_mul,norm_apply_le_l2_opNorm,norm_apply_le_l2_opNorm,U.norm_inv,hφ' _ ·];simp [*,field]) (by simp [·]))⟩:∀ i,Measurable (ψ i)∧∀ y,‖ψ i y‖≤ ‖φ y‖)
 have iψ i:=hi.mono (by fun_prop) (.of_forall (hψ i));choose V v hW hd hs using hV
 let T i g y:=ψ i y•V (i.map (·.1)) (g*y)
 refine' (lintegral_congr (by simp [T,ψ,v])).trans_le ((sobolev_chain (fun i x (a,b) ↦ ∫ y,T i (zL (Z+e x)*(embedH a⁻¹*b.1⁻¹)) y) (by fun_prop) _ _ (ae_restrict_of_forall_mem (by simp;fun_prop) fun ω h i j x _ k↦_) fun i hi↦_).trans _);rotate_left 5
 · let p t:=Z+e (Function.update x j t)
   let g t:=zL (p t)*(embedH ω.1⁻¹*ω.2.1⁻¹)
   choose! A hA' hA using fun {t} (q:p t∈Q)↦show ∃ A,HasDerivAt (g · |>.1.1) (g t*A) t∧‖P^40•A‖≤ P^112 by
     have ⟨a,b⟩:=k6 (by positivity) h8 fun _ k↦(B (ball_half_subset _ q k)).2
     refine ⟨_,((((vK (o q)).hasFDerivAt_iff.2 (qF (o q)).hasFDerivAt).comp_hasDerivAt _ ((e.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_update ..)).const_add Z)).mul_const _).congr_deriv (by rw [Units.mul_inv_cancel_left]),?_⟩
     grw [norm_smul,norm_mul_le,← Subgroup.coe_inv,U.norm_inv,Subgroup.coe_mul,Units.val_mul,norm_mul_le,norm_mul_le,norm_embedH_mul,U.norm_inv,h.out,h.out,qM,(fderiv ..).le_opNorm,e.coe_coe,he',a,b] <;> simp [Pi.norm_single, *,field];nlinarith
   have s i j:=(hW j).integrable_smul (iψ i)
   refine ⟨_,(hasDerivAt_integral_of_dominated_loc_of_deriv_le (F':=fun t y ↦ ∑ l,(P^40•A) l.2.2 l.2.1•T (l :: i) (g t) y) ((isOpen_ball.preimage (f:=p) ?_).mem_nhds (hx k)) (.of_forall (by fun_prop)) ?_ ?_ (.of_forall fun y t↦(by grw [norm_sum_le,norm_smul_le,norm_apply_le_l2_opNorm,hA ·,norm_smul_le,(hW _).bounded.choose_spec])) ?_ (.of_forall fun y t q ↦ .congr_deriv (.fun_const_smul _ (hd _ (g · * y) (y⁻¹*A*y) _ (by simpa [mul_assoc] using (hA' q).mul_const _))) ?_)).2,by
     grw [integral_finsetSum,norm_sum_le,congr(‖$(integral_smul ..)‖).le,norm_smul_le,norm_apply_le_l2_opNorm,hA (hx k)];fun_prop⟩ <;> try fun_prop
   simp [-sum_sum_type,T,ψ,Finset.smul_sum,smul_smul,sum_prod_type,mul_apply,Finset.sum_mul,Finset.sum_smul];congr! 5;field
 · have ⟨χ,mχ,v⟩:=(@isUnimodularHaar_besselHaar₀ 𝔰).out
   simp [← sq,Subgroup.smul_def] at hi v ⊢;grw [setLIntegral_le_lintegral {x | _}]
   have m:=mχ.indicator (s:=realFrameGram ⁻¹' Q) (measurableSet_ball.preimage (by fun_prop [frameGram]))
   exact .trans (jX (by fun_prop) fun _ ↦ .trans_eq (.trans (setLIntegral_mono' (by simp) fun x h↦by grw [bg (hx h),lintegral_prod_le] <;> simp [𝔰.openCellConst_pos.le,indicator,mem_sup_left,mem_sup_right,zN,realFrameGram_mul_invariant,lintegral_mul_const',hx h,T,← mul_assoc (zL _), *,(hW _).enorm_integral_besselS_mul,fun u:besselU0↦mem_inf.1 u.2]) (lintegral_mono_set (by tauto))) (he.setLIntegral_comp_preimage jO.measurableSet (by fun_prop)))
     ((qT (w:=(‖∫ y,T i · y‖ₑ^2)) (by fun_prop) m (by simp +contextual [T,(hW _).enorm_integral_besselS_mul]) (by grw [indicator_le_self ..,v ·]) (by simp_intro y i s j k ..;simpa [s21_q1 y j,(o k.1).1] using (norm_apply_le_l2_opNorm ..).trans (norm_mul_le_of_le (bn i.1) (bi k.1))) (by
     bound)).trans (by grw [hs ..,i.length_map,hi,enorm_le_iff_norm_le.2 (hψ ..)] <;> simp [*]))
 simp (disch:=bound) [← sq,← mul_assoc,pow_mul,← ENNReal.ofReal_mul,← mul_pow,-ENNReal.ofReal_pow];grw [le_of_mul_le_of_one_le hP,one_le_pow₀ h1 (n:=232)];gcongr;field;grw [← h8];grind;repeat bound
end
