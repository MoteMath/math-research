import New.RealPlace.WeightPlancherel
import New.Filling.BesselSystem
noncomputable section
open Matrix MeasureTheory Measure ENNReal Fintype ComplexConjugate InnerProductSpace Level Finset Function RCLike Place
attribute [-simp] Subtype.forall Subtype.exists inv_mul_cancel₀
variable {A} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P:Place A] {ι} [Fintype ι] {m} {𝔰:Shape} (j:ℕ) {T:𝔰.Form A} [IsHermUnit T.splitGram] {F:Level ι T m} (p q:ℕ→ Aˣ) {ξ:Aˣ} {I:Type} [Fintype I] (W W':T.G→ EuclideanSpace ℂ I) (x:T.G) (Γ Γ':Gauge F)
def Level.headDensity (_:Level ι T m) := ∏ a ∈ .range j,(P.md (p a*q a)^(2⁻¹:ℝ))^(𝔰.k+1+2*(𝔰.ϱ-(a+1)))
@[simp] abbrev translatePairing d x y := ⟪W x,W' (d*y)⟫_ℂ
structure Place.IsBessel (η:Aˣ):Prop extends IsBoundedMeasurable W where
 law:∀ u∈T.besselU,∀ x,W (u*x)=ψ (η*simpleRootSum u)•W x
structure Level.IsCut:Prop extends P.IsBessel W F.g⁻¹ where
 exists_mul_mem_box:∀ {x},W x≠0→ ∃ u∈T.besselU,u*x∈F.boxSet
def Level.pairingNorm := ∫⁻ x,∫⁻ y,‖⟪W x,W' y⟫_ℂ‖ₑ^2 ∂F.upperMeasure 0 ∂F.upperMeasure 0
def Level.formIntegrandOne d w g:=F.upperPairing j (translatePairing W W 1) g (g*x)*conj
 (F.upperPairing j (translatePairing W W d) (w⁻¹*g) (w⁻¹*g*x))
def Level.formIntegrand (ω:_→ ℂ) g := ∫ σ,∫ τ,ω (σ*τ⁻¹)*F.formIntegrandOne (j+1) W x
 (weylRatio j p q) (σ*weylElem j p*τ⁻¹) (σ*g) ∂F.floorMeasure j ∂F.floorMeasure j
def Level.floorForm ω:=(F.headDensity j p q).toReal * ∫ z,F.formIntegrand j p q W z.1 ω z.2 ∂F.groupMeasure.prod (F.stackMeasure 0 j)
def Level.formModulus ω := ∫⁻ g,‖F.formIntegrand j p q W x ω g‖ₑ ∂F.stackMeasure 0 j
def Level.formMajorant := ∫⁻ g,F.pivotModulus j (translatePairing W W 1) g (g*x)*F.pivotModulus j (translatePairing W W' (weylRatio j p q)) ((weylElem j p)⁻¹*g)
 ((weylElem j p)⁻¹*g*x) ∂F.stackMeasure 0 j
def Gauge.selfNormProduct:=(∏ a ∈ .range j,F.floorModulus a (p a)⁻¹)^2*Γ.vR^3*F.selfNorm 0 (translatePairing W W 1) x*F.selfNorm j (translatePairing W W' (weylRatio j p q)) x
attribute [local simp] mul_assoc div_eq_mul_inv formIntegrand formIntegrandOne Fin.prod_univ_castSucc floorModulus floorForm lintegral_prod lintegral_mconv_symm ENNReal.inv_mul_cancel_left ENNReal.mul_inv_cancel prod_range s21_k8 wQ
variable {j p q W W' x} (hk:F.IsCut W) (hk':IsBessel W' F.g⁻¹) (hj:j≤ 𝔰.ϱ) (hp:Γ.IsHead j p) (hx:x∈F.positions)
omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermUnit T.splitGram] in
lemma frameGram_diag_mul {b:Fin 𝔰.n} (h:x∈unitriGroup (b+1)⊓GT b) y:T.frameGram (x*y).1.1 b b=T.frameGram y b b∧T.frameGram (y*x).1.1 b b=T.frameGram y b b:=have e:=orbitPoint_eq_iff.1 ((mem_unitriGroup_succ_iff h.2).1 h.1);by simpa [↓mulVec_mulVec] using! (And.intro (e▸U.form_mulVec_mulVec x _ (y.1.1 *ᵥ Pi.single _ 1) :) congr((T.splitGram *ᵥ y *ᵥ $e) (𝔰.besselFrame b)))
lemma Gauge.pivotModulus_sq_le_of_capped {k d ε l g} (hK:F.IsPairingKernel j k d) (hx:x∈F.positions) (hc:∀ σ∈GT l,k (σ*g) (σ*(g*x))≠0→ ∃ a:Fin _,l≤ a∧volume (F.floorValues a (σ*g) x)≤ ε):F.pivotModulus l k g (g*x)^2≤ ε^F.volumeExponent*(Γ.Λ^(10^4*𝔰.n))^(𝔰.ϱ-l)*(F.weightedSquareSum k x l g/F.floorWeight l g x):=by
 induction' e:_-l with i ih generalizing l g
 rw [of_not_not (mt exists_ne_zero_of_pivotModulus (by grind))];simp
 rw [weightedSquareSum,ite_eq_left (by lia),div_eq_mul_inv,← lintegral_mul_const,pow_succ' (_^_),mul_left_comm,mul_assoc,← lintegral_const_mul] <;> try fun_prop
 lift l to Fin 𝔰.ϱ using (by lia);refine hK.jL (Γ.kK l hx) fun σ s ↦ ?_
 by_cases e:volume (F.floorValues l (σ*g) x)≤ ε <;> [grw [← e,← Γ.one_le_Lambda,← le_self_add (a:=F.z7 ..)];grw [hK.enorm_upperPairing_le,← mul_assoc,ih (fun τ a n↦by grind [mul_mem (by grind:τ∈_) s,k3 (mem_unitriGroup_of_mem_floorGroup a)]) (by lia)]] <;>
   simp [vB,s,ENNReal.mul_inv,ENNReal.mul_inv_cancel_left] <;> ring_nf <;> simp
lemma Gauge.v4 [F.groupMeasure.IsHaarMeasure] {k d c} (hK:F.IsPairingKernel j k d) (hj:j≤ 𝔰.ϱ) (e:(∏ l ∈ .range 𝔰.ϱ,Γ.wB l) * ∫⁻ g,∫⁻ y,‖k g y‖ₑ^2 ∂F.upperMeasure 0 ∂F.upperMeasure 0=c) : ∫⁻ x in Γ.positionsOfSize,F.selfNorm j k x ∂F.groupMeasure≤ 𝔰.n*c:=by
 obtain ⟨hB,I⟩:=Γ.jJ,fun {l n}↦by simpa using @hK.law l 1 n
 let W l g y := ∫⁻ ν,Γ.positionsOfSize.indicator 1 (g⁻¹*(ν*y)) ∂ascConv heisenbergMeasure l
 let Φ l g y := ∞ * W l g y⊓‖F.upperPairing (l+1) k g y‖ₑ^2
 have V {l g y σ t} h:W l g y=W l (σ*g) (t*y):=(lintegral_eq_of_dirac_mconv_eq (s:=σ) (t:=t) h).trans (by simp [W])
 apply le_add_self.trans (Nat.decreasingInduction' (P:=fun l↦∃ ρ,SFinite ρ∧l*c + ∫⁻ x in Γ.positionsOfSize,F.selfNorm l k x ∂F.groupMeasure≤ 𝔰.n*c∧F.groupMeasure=ascConv heisenbergMeasure l∗ₘρ∧(∏ a∈range l,if a< 𝔰.ϱ then Γ.wB a else 1) * ∫⁻ g,∫⁻ y,Φ l g y ∂ρ ∂descConv F.floorMeasure 0 (l+1)≤ c) (fun l h _ ⟨ρ,_,z,e,i⟩↦(fun a↦⟨_,inferInstance,.trans ?_ z,a⟩) ⟨e▸mconv_assoc ..,.trans ?_ i⟩) hj.step ⟨F.upperMeasure 0,inferInstance,by simp [selfNorm,weightedSquareSum],by simp [stackMeasure_zero_eq,ascConv],
   e▸by gcongr ?_ * ∫⁻ g,∫⁻ y,?_ ∂_ ∂_ <;> simp [upperPairing,descConv]⟩).choose_spec.2.1
 · simp [hK.j3 h.le_pred,z7,add_one_mul,add_assoc]
   grw [lintegral_add_left,← add_le_add_left a.2,lintegral_lintegral_swap,← lintegral_const_mul];gcongr with g;grw [← lintegral_indicator hB,← lintegral_mul_left_eq_self _ g⁻¹,a.1,lintegral_mconv_symm,← lintegral_const_mul]
   any_goals fun_prop
   exact lintegral_mono fun y↦not_lt.1 fun n↦n.not_ge ((lintegral_le_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν h↦by simp [I h,Set.indicator,← ofReal_norm]).trans ((lintegral_mul_const _ (by fun_prop)).trans_le (mul_le_mul' ((Γ.kV (by lia) g y ((exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow n.ne_bot).elim (by simp;grind [→ IsPairingKernel.isNear_of_upperPairing_ne_zero,IsNear]))).trans (by gcongr;grind)) (le_min ((top_mul fun z↦(exists_ne_zero_of_ae ((lintegral_eq_zero_iff (by fun_prop)).1 z) n.ne_bot).elim (by simp_all)).ge.trans' le_top) le_rfl))))
 grw [prod_range_succ,mul_assoc,descConv_succ (l+1),lintegral_mconv_symm,← lintegral_const_mul (ite ..)];gcongr with g
 grw [← qN rfl fun σ a↦jA e ae_ascConv_mem_unipotentBelow (by grind [ascConv_heisenbergMeasure_invariant]) (ascConv_heisenbergMeasure_dirac_comm _ a) _ fun s o y↦by simp [Φ,@V (l+1) _ y 1 s (by simp [ascConv_heisenbergMeasure_invariant o]),I o,← ofReal_norm],
   lintegral_lintegral_swap,← lintegral_const_mul,lintegral_mconv_symm,lintegral_mono fun y ↦
   if z:W (l+1) g y=0 then ((lintegral_mono fun n↦inf_le_left).trans_eq (by simpa (disch:=with_unfolding_all fun_prop) [W,ascConv] using z)).trans zero_le else ?_]
 any_goals fun_prop
 simp +contextual only [Φ,← V (ascConv_heisenbergMeasure_dirac_comm _ _),top_mul z];split
 grw [Γ.qW ⟨l,‹_›⟩ F.g⁻¹ F.g 0 1 (hK.mono (by lia)) g y (fun s c↦by simp [hK.3 _ (floorGroup_anti ‹_› c.1),simpleRootSum_eq_zero_of_mem_besselH]) (fun n a H↦⟨And.intro a (by simp at H;simpa using And.imp (exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow) hK.isNear_of_upperPairing_ne_zero H),by simp⟩) (by
   rintro _ ⟨u,⟨_,h₁,e₀⟩,_,o,k⟩;obtain ⟨t,ht,ν,hν,rfl⟩:=exists_floorGroup_mul_unipotentBelow (unitriGroup_anti l.le_succ o)
   exact ⟨t,⟨(mul_mem_cancel_right (unipotentBelow_le_unitriGroup hν)).1 o,ht⟩,_,by grind,
     Γ.hasMatSize_box k,fun n ⟨hn,⟨μ,hμ,e⟩,_⟩↦⟨_,conj_mem_unipotentBelow ht (mul_mem (mul_mem hν h₁) (conj_mem_unipotentBelow (mul_mem u (inv_mem hn)).1 (inv_mem (mul_mem hν hμ)))),(vG k e₀ e (by group) · _)⟩⟩)]
 simp;ring_nf;rfl
 grw [heisenbergMeasure_eq_dirac_one (by lia),← hK.jL (u:=1) (by simp [FloorMassLe,IsNear,measureH_spec,(by lia:l=𝔰.ϱ)]),← hK.enorm_upperPairing_le];simp
lemma Level.enorm_floorForm_le ω:‖F.floorForm j p q W ω‖ₑ≤ F.headDensity j p q * ∫⁻ x,F.formModulus j p q W x ω ∂F.groupMeasure:=by
 grw [floorForm,enorm_mul,enorm_integral_le_lintegral_enorm,lintegral_prod_le,← ofReal_norm];simp [formModulus];grw [ofReal_toReal_le]
lemma Level.stackMeasure_top:F.stackMeasure 𝔰.ϱ 2=F.measureH∗ₘF.floorMeasure 𝔰.ϱ:=by simp [descConv]
lemma Gauge.isCompact_hasMatSize:IsCompact {y:T.G | Γ.HasMatSize j y.1.1}:=isClosedEmbedding_unitary_coe.isCompact_preimage (Γ.isCompact_ofSize _).matrix
include hk
lemma Level.IsCut.isNear_of_ne_zero (h:W x≠0):F.IsNear j x:=(hk.2 h).imp fun _ ↦ .imp_left mem_unitriGroup_of_mem_besselU
lemma Level.IsCut.formModulus_le_formMajorant {ω} (h:∀ x,‖ω x‖≤ 1):F.formModulus j p q W x ω≤ F.formMajorant j p q W W x:=lintegral_mono fun _↦by
 delta formIntegrand pivotModulus
 repeat grw [enorm_integral_le_lintegral_enorm]
 grw [(ofReal_norm _).ge,norm_mul_le,h,← lintegral_mul_const _ (hk.1.1.rec (by fun_prop [upperPairing]))]
 simp [lintegral_const_mul']
include Γ
lemma Gauge.hasMatSize_of_ne_zero {y} (hp:Γ.IsHead 𝔰.ϱ p) (t:x∈GT 𝔰.ϱ) (h:W y≠0) (n:W ((weylElem 𝔰.ϱ p*x)⁻¹*y)≠0):Γ.HasMatSize (60*𝔰.n^2) y.1.1:=(hk.2 h).elim fun u ⟨hu,v⟩↦(Size.kB Γ.hasMatSize_box .refl (IsNear.of_floorGroup_mul (by simpa using hk.isNear_of_ne_zero n) (inv_mem t)) ⟨mem_unitriGroup_of_mem_besselU hu,v⟩ hp ((unipotentBelow_eq_besselU .refl).ge hu)).1
lemma Gauge.inner_besselCorrelation {μ} [IsHaarMeasure μ] (hW:Continuous W) (hp:Γ.IsHead 𝔰.ϱ p) (hq:Γ.IsHead 𝔰.ϱ q) (t:x∈GT 𝔰.ϱ) : ⟪besselCorrelation μ W (weylElem 𝔰.ϱ p*x),besselCorrelation μ W (weylElem 𝔰.ϱ q*x)⟫_ℂ = ∫ z,⟪W z.1,W z.2⟫_ℂ*conj ⟪W ((weylElem 𝔰.ϱ p*x)⁻¹*z.1),W ((weylElem 𝔰.ϱ q*x)⁻¹*z.2)⟫_ℂ ∂μ.prod μ:=by
 simp_rw [PiLp.inner_apply,besselCorrelation,inner_apply',← integral_conj,← integral_prod_mul]
 rw [← integral_finsetSum _ fun i _↦HasCompactSupport.integrable (.intro (Γ.isCompact_hasMatSize.prod Γ.isCompact_hasMatSize) fun y↦not_imp_comm.1 fun z↦by
   use Γ.hasMatSize_of_ne_zero hk hp t ?_ ?_,Γ.hasMatSize_of_ne_zero hk hq t ?_ ?_ <;> exact (z <| ·▸by simp))]
 simp [sum_prod_type,Finset.sum_mul_sum,mul_left_comm]
lemma Gauge.zB (hk':P.IsBessel W' F.g⁻¹) j p q:F.IsPairingKernel j (translatePairing W W' (weylRatio j p q)) (weylRatio j p q):=by
 obtain ⟨⟨_,C,b⟩,_,_,b'⟩:=hk.1.1,hk'.1
 refine ⟨by fun_prop,@fun l u v a b g y ↦ .trans (integral_congr_ae ((ae_descConv_mem ae_floorMeasure_mem).mono fun σ c ↦ ?_)) (integral_const_mul ..),
   fun s a↦by simp [weylRatio,weylElem_mul_left_comm a],fun l↦⟨_,?_,fun g y↦by
   grw [← setLIntegral_eq_of_support_subset,(ofReal_norm _).ge,norm_inner_le_norm,b,le_abs_self C,b',setLIntegral_const,upperMeasure_isNear_le (Γ.floorMassLe_one · Γ.hasFibreBound_floorQuadric) l g,Γ.volume_le]
   exact fun _ _↦hk.isNear_of_ne_zero (by aesop)⟩,Not.imp_symm fun n↦integral_eq_zero_of_ae
   ((ae_descConv_mem ae_floorMeasure_mem).mono fun _ a↦by simp [by_contra (n <| hk.isNear_of_ne_zero · |>.of_floorGroup_mul a)])⟩
 dsimp
 rw [(congrArg W (by simp)).trans (hk.law _ (unipotentBelow_le_besselU (conj_mem_unipotentBelow c (by grind:u∈_))) (σ*g)),(congrArg W' (by simp [weylRatio])).trans (hk'.law ((weylRatio j q p)⁻¹*(σ*v*σ⁻¹)*_) (conj_mem_unitriangular (by simp) (unipotentBelow_le_besselU (conj_mem_unipotentBelow c (by grind)))) (weylRatio j p q*(σ*y)))]
 simp [mul_sub,ψ.map_sub_eq_div,← inv_eq_conj,simpleRootSum,← superdiag_conj_eq _ c, *,-besselFrame_castSucc,-mul_assoc];ring
 finiteness [Γ.one_le_c_and_ne_top.2]
lemma Gauge.isPairingKernel_self j:F.IsPairingKernel j (translatePairing W W 1) 1:=by simpa [weylRatio] using Γ.zB hk hk.1 j 1 1
lemma Level.formIntegrandOne_eq:F.formIntegrandOne j W x (weylRatio j p q) (weylElem j p)=F.formIntegrand j p q W x 1:=funext (by simp [← (Γ.isPairingKernel_self hk j).zI.2,← (Γ.zB hk hk.1 ..).zI.2,integral_conj])
lemma Level.v0 (b:Fin 𝔰.n) {ζ} [SFinite ζ] {v:A→ _} {ρ Ψ t} (η:A) (hm : ∫⁻ x,F.formMajorant b p q W W x ∂F.groupMeasure ≠ ∞) (z:∀ᵐ n ∂ζ,n∈unitriGroup (b+1)⊓GT b) (hρ:∀ᵐ c,ρ c< ∞) (hc:F.floorMeasure b=(volume.withDensity ρ).map (fun c↦(v c)⁻¹)∗ₘζ) (hΨ:∀ᵐ c,Ψ c=t*(F.headDensity b p q*ρ c).toReal•(ψ (η*T.frameGram (v c).1.1 b b) * ∫ z,F.formIntegrandOne (b+1) W z.1 (weylRatio b p q) (weylElem b p*v c) z.2 ∂F.groupMeasure.prod ((ζ∗ₘF.floorMeasure b)∗ₘF.stackMeasure 0 b))) (mv:Measurable v:=by fun_prop) (mρ:Measurable ρ:=by fun_prop) :
 Integrable Ψ ∧ ∫ c,Ψ c=t*F.floorForm b p q W fun x↦P.ψ (η*T.frameGram x b b):=by
 let ψ (x:T.G):=P.ψ (η*T.frameGram x b b)
 obtain ⟨k,k',_⟩:=Γ.isPairingKernel_self hk b,Γ.zB hk hk.1 b p q,(by fun_prop [frameGram]:Measurable ψ)
 have E:ProbabilityTheory.IdentDistrib (fun (z,c)↦ψ (v c)*F.formIntegrandOne (b+1) W z.1 (weylRatio b p q) (weylElem b p*v c) z.2) (fun (((x,g),σ),τ)↦ψ (σ*τ⁻¹)*F.formIntegrandOne (b+1) W x (weylRatio b p q) (σ*weylElem b p*τ⁻¹) (σ*g)) ((F.groupMeasure.prod ((ζ∗ₘF.floorMeasure b)∗ₘF.stackMeasure 0 b)).prod (volume.withDensity ρ)) (((F.groupMeasure.prod (F.stackMeasure 0 b)).prod (F.floorMeasure b)).prod (F.floorMeasure b)):=⟨by fun_prop [formIntegrandOne],by fun_prop [formIntegrandOne],ext_of_lintegral _ fun φ _↦by
   simp (disch:=with_unfolding_all fun_prop) [lintegral_map];congr! 5 with _ _ σ hσ
   rw [← zK le_rfl (fun s _↦by simp [-mul_assoc,mul_assoc s,k'.z8,← mul_assoc σ,ψ,↓frameGram_diag_mul, *]) ⟨mem_unitriGroup_of_mem_floorGroup hσ,hσ⟩,hc,lintegral_mconv_symm,lintegral_congr_of_ae_imp z fun _ ↦ ?_] <;> try rw [lintegral_map]
   any_goals fun_prop
   simp_all [weylElem_mul_left_comm,k.z8,ψ,↓frameGram_diag_mul]⟩
 have K:Integrable _ _:=⟨E.2.aestronglyMeasurable,hm.lt_top.trans_le' (by
   grw [(enorm_mul ..).le,(ofReal_norm _).ge,(P.norm_psi _).le]
   simp (disch:=with_unfolding_all fun_prop) [formMajorant,pivotModulus,lintegral_mul_const])⟩
 have J:=E.integrable_iff.2 K
 simpa [↓integral_prod_symm _ J,↓integral_prod,↓K,integrable_congr hΨ,↓K.integral_prod_left,integral_congr_ae hΨ,ψ,integral_withDensity_eq_integral_toReal_smul, *] using And.intro
   ((((integrable_withDensity_iff_integrable_smul' mρ hρ).1 J.integral_prod_right).const_mul _).const_mul t) (Or.inl (Or.inl E.integral_eq))
lemma Gauge.integral_floorForm_succ (a:Fin _) t η (hm : ∫⁻ x,F.formMajorant a p q W W x ∂F.groupMeasure ≠ ∞):let f c:=ψ (η*c)*(t*F.floorForm (a+1) (update p a (unitOrOne c)) (update q a (unitOrOne c)) W 1)
 Integrable f ∧ ∫ c,f c=t*F.floorForm a p q W (ψ <| η*T.frameGram ·.1.1 a.castSucc a.castSucc):=v0 Γ hk a.castSucc η hm (ae_mem_floorUnipotent.mono fun _ h↦⟨unipotentBelow_le_unitriGroup h.2,h.1⟩) (ae_isUnit.mono fun
   | _,⟨c,rfl⟩ => by simp [Ne.lt_top]) (ite_eq_left a.2) (ae_isUnit.mono fun _ ⟨c,h⟩↦by simp [← h,↓← formIntegrandOne_eq Γ hk,weylRatio,weylElem_succ,(commute_weylElem _).eq,descConv_succ,frameGram_floorWeyl,headDensity,← sq,LT.lt.ne,← rpow_two,-rpow_ofNat,field])
variable [F.groupMeasure.IsHaarMeasure]
include hk' hj
lemma Gauge.lintegral_positions_le (hq:Γ.IsHead j q) {Θ S e} {f:_→ _} (hΘ:F.pairingNorm W W*F.pairingNorm W W'≤ Θ^2) (hS:S⊆Γ'.positionsOfSize) (h:∀ x∈S,f x^2≤ e^2*selfNormProduct j p q W W' x Γ):F.headDensity j p q * ∫⁻ x in S,f x ∂F.groupMeasure≤ (e * ∏ l∈range 𝔰.ϱ,F.floorModulus l)*P.c^(card ι*𝔰.ϱ)*Γ.Λ^(1500000*𝔰.n^3)*Γ'.Λ^(50000*𝔰.n^2)*Θ*Γ.Λ:=by
 obtain ⟨k,k',_,_⟩:=Γ.isPairingKernel_self hk _,Γ.zB hk hk' ..,hk.stronglyMeasurable,hk'.stronglyMeasurable
 grw [← ENNReal.pow_le_pow_left_iff two_ne_zero,mul_pow,mul_pow,mul_pow,← hΘ,← Γ.md_le 2 _ (Γ.mem_ofSize_mono (hq j .refl)),setLIntegral_mono _ fun x m↦(le_rpow_inv_iff two_pos).2 (mod_cast h x m),lintegral_mono_set hS,sq_lintegral_le _ _ fun x↦by exact
   ((rpow_inv_natCast_pow two_ne_zero _).trans_le (mul_assoc ..).ge),lintegral_const_mul,
   lintegral_const_mul,Γ'.v4 k zero_le rfl,Γ'.v4 k'
   hj congr(_ * ∫⁻ g,$(kX (Φ:=(‖⟪W g,W' ·⟫_ℂ‖ₑ^2)) hj ?_) ∂_),
   lintegral_const_mul,𝔰.n.lt_two_pow_self] <;> try fun_prop [selfNormProduct,selfNorm]
 simp [Level.pairingNorm,-md_inv];grw [Γ'.two_le_and_pairs_le.1,← ge_iff_le];ring_nf
 simp_rw [mul_assoc];gcongr <;> simp [headDensity,← map_mul,← prod_pow,← prod_mul_distrib,← map_pow,pow_right_comm _ _ 2,← Finset.prod_inv_distrib,← rpow_two,-md_inv,-rpow_ofNat]
 convert le_rfl;norm_cast;apply Additive.ofMul.injective;simp;match_scalars <;> grind
include hp hx
lemma Gauge.jB {f:_→ _} {K} (hf:∀ g,f g≠0→ f g^2≤ K*Γ.vR*(F.weightedSquareSum (translatePairing W W 1) x j g/F.floorWeight j g x)*(F.weightedSquareSum (translatePairing W W' (weylRatio j p q)) x j ((weylElem j p)⁻¹*g)/F.floorWeight j ((weylElem j p)⁻¹*g) x)):(∫⁻ g,f g ∂F.stackMeasure 0 j)^2≤ K*Γ.selfNormProduct j p q W W' x:=by
 obtain ⟨k,k'⟩:=Γ.isPairingKernel_self hk _,Γ.zB hk hk' ..;obtain ⟨b,c⟩:=k.zY x,k'.zY x
 nth_grw 1 [selfNormProduct,← k.vD hj.step,sq_lintegral_le,s21_q9 p,stackMeasure_zero_eq,Γ.z9 hj hp hx .refl c,lintegral_const_mul (K*Γ.vR),stackMeasure_zero_eq,Γ.z9 hj hp.wG hx .refl b] <;> try fun_prop
 simp [selfNorm];ring_nf;rfl
 simp +contextual [weylElem_mul_left_comm,c.1]
 intro g;by_cases e:f g=0;simp [e]
 grw [hf g e];simp [qJ,Set.indicator];split_ifs;ring_nf;repeat simp [*]
lemma Gauge.formMajorant_sq_le {σ V} (v:F.FloorMassLe j V 1) (u:1≤ V) (n:∀ {y},W' y≠0→ F.IsNear j y) (c:σ< 1→ ∀ y,⟪W y,W (y*x)⟫_ℂ≠0→ F.IsNear j ((weylElem j p)⁻¹*y)→ F.IsNear j ((weylElem j q)⁻¹*(y*x))→ ∃ a:Fin _,j≤ a∧volume (F.floorValues a y x)≤ σ):F.formMajorant j p q W W' x^2≤ σ^F.volumeExponent*V^2*Γ.selfNormProduct j p q W W' x:=Γ.jB hk hk' hj hp hx fun y e↦by
 obtain ⟨⟨τ,b,_⟩,k,k'⟩:=exists_ne_zero_of_pivotModulus (right_ne_zero_of_mul e),Γ.isPairingKernel_self hk j,Γ.zB hk hk' ..
 grw [mul_pow,k'.jL v,s21_z1 hj];by_cases! l:1≤ σ <;>
   [grw [k.jL v,s21_z1 hj,vR,← Γ.one_le_Lambda,← l];grw [Γ.pivotModulus_sq_le_of_capped k hx fun ρ a e↦c l _ ?_ (.of_floorGroup_mul (hk.isNear_of_ne_zero ?_) (div_mem b a)) (.of_floorGroup_mul (n ?_) (div_mem b a)),(by lia:_-j≤ 100*𝔰.n^2),← le_self_pow u two_ne_zero]] <;>
   first | ring_nf;rfl | intro;simp_all [weylRatio,← (weylElem_mul_left_comm _).2] | bound
omit hk'
lemma Gauge.formModulus_sq_le_of_char {η} (hφ:∀ z∈Γ.ofSize (200*𝔰.n^2),ψ (η*z)=ψ (ξ*z)):F.formModulus j p q W x (fun x↦ψ (η*(T.frameGram x).diag ⟨j,by lia⟩))^2≤ (P.c/P.md ξ)^card ι*Γ.selfNormProduct j p q W W x:=Γ.jB hk hk.1 hj hp hx fun g H↦by
 lift j to Fin 𝔰.n using (by lia);repeat grw [← s21_z1 hj]
 simp [Matrix.diag,↓frameGram_eq_form_orbitPoint] at H ⊢
 obtain ⟨hf,K,σ,a,τ,b,-,h⟩:=Γ.isPairingKernel_self hk _,Γ.zB hk hk.1 ..,by
   simpa using H∘integral_eq_zero_of_ae∘ae_floorMeasure_mem.mono∘forall₂_imp fun _ _↦integral_eq_zero_of_ae∘ae_floorMeasure_mem.mono
 obtain ⟨t,ht,k,k'⟩:=jZ hj hp ((hf.isNear_of_upperPairing_ne_zero h.1).of_floorGroup_mul a) ((K.isNear_of_upperPairing_ne_zero h.2).of_floorGroup_mul b);obtain ⟨⟨e,-⟩,v,l⟩:=Γ.qB ht k hf (g*x),Γ.qB ht k' K ((weylElem j p)⁻¹*(g*x))
 grw [integral_congr_ae (e.mono fun σ s↦(integral_congr_ae (v.mono fun τ s' ↦ ?_)).trans ((integral_const_mul ..).trans (congrArg _ integral_conj))),← setIntegral_eq_integral_of_ae_compl_eq_zero (e.mono fun _ h↦not_imp_comm.1 (h∘left_ne_zero_of_mul)),enorm_integral_le_lintegral_enorm,sq_lintegral_le _ (Measurable.aemeasurable _) fun _↦by rw [enorm_mul,mul_pow,enorm_conj]]
 refine (mul_le_mul' (setLIntegral_le_lintegral ..) (((zZ j ht).setLIntegral_comp_preimage zE (by fun_prop)).trans_le (l (-ξ) 0 hasFibreBound_floorQuadric))).trans ?_
 simp;ring_nf;gcongr <;> simp
 repeat fun_prop
 simp [ψ.map_neg_eq_inv,inv_eq_conj,mul_left_comm _ (ψ _),-mulVec_mulVec,U.form_mulVec_mulVec];exact or_iff_not_imp_right.2 fun n↦hφ _ (U.form_mulVec_mulVec t .. ▸ Γ.mem_ofSize_mono (Γ.qV (fun a _↦Γ.neg_star_mem_ofSize.2.2 (s (n ∘ .inl) a)) (Size.HasMatSize.mulVec Γ.gram_mem_ofSize.1 (s' (n ∘ .inr)))))
lemma Gauge.formModulus_sq_le_of_heads {i} (hi:j=i+1) (h:ξ=F.g⁻¹*((p i)⁻¹.1-(q i)⁻¹.1)):F.formModulus j p q W x 1^2≤ (P.c/P.md ξ)^card ι*Γ.selfNormProduct j p q W W x:=by
 let r g:=F.floorWeight j g x*F.qJ i x (weylElem i p*g)
 let u g := ∞ * F.qJ j x (weylElem j p*g)⊓r g*‖F.upperPairing j
   (translatePairing W W (weylRatio j p q)) g (g*x)‖ₑ^2
 subst hi;obtain ⟨k,k'⟩:=Γ.isPairingKernel_self hk _,Γ.zB hk hk.1 (i+1) p q
 grw [formModulus,← formIntegrandOne_eq Γ hk,selfNormProduct,← k.vD (by lia:i≤ _),← le_self_add.trans (k.j3 (by lia)).ge,sq_lintegral_le _ _ fun g↦not_lt.1 fun z:u ((weylElem _ p)⁻¹*g)*(F.z7 i _ x g*_)< _↦z.not_ge ?_,s21_q9 p _ fun s a g↦by simp [r,u,weylElem_mul_left_comm,k'.z8,a,(by grind:s∈GT i)],stackMeasure_zero_eq,Γ.z9 hj hp.wG hx
   .refl k.qA,ascConv_heisenbergMeasure_succ,mconv_assoc,
   lintegral_mconv_symm,lintegral_mono fun g↦by grw [Γ.qW ⟨i,hj⟩ (-ξ*p i) (p i)⁻¹ 1 (r g) k' g (g*x) (fun s c↦by
   simp_rw [simpleRootSum,← sum_sub_distrib,mul_sum];congr with b
   simp [-besselFrame_castSucc];grind [floorUnipotent_superdiag_eq_zero b c,Units.mul_inv])
   (fun n a e↦⟨by
   simp [qJ,u] at e;have N {w}:=inv_mul_cancel_left w (n*g)▸k'.isNear_of_upperPairing_ne_zero e.2.2
   exact And.intro (Γ.jZ hj hp e.1 N) (And.intro a (Size.zQ (a:=⟨i,hj⟩) Γ.hasMatSize_box hj N e.1.choose_spec hp .refl).1),by simp [u,r,weylElem_mul_left_comm a.1,unipotentBelow_le_unitriGroup a.2]⟩) (by
   exact fun _ ⟨⟨τ,t,_,h⟩,a,L⟩↦⟨τ,by simp;grind,_,a.2,by simpa using h,
     fun _ ⟨⟨_,s,_,e⟩,_⟩↦⟨1,one_mem _,fun c↦Γ.mul_mem_ofSize L (by
     rw [← inv_mem_iff,mem_floorGroup] at s t;simp at s t
     simpa [mul_apply,s,t] using (h.mul e.inv).sub .one c (eStar ⟨i,hj⟩))⟩⟩),
   s21_z1 hj,mul_left_comm,mul_right_comm (F.floorWeight ..),
   ENNReal.mul_div_cancel] <;> simp,lintegral_const_mul,Γ.z9 (by lia)
   (hp · ·.step) hx i.le_succ (k'.zY x)] <;> try fun_prop
 simp [selfNorm];ring_nf;gcongr <;> simp
 cases And.imp k.isNear_of_upperPairing_ne_zero k'.isNear_of_upperPairing_ne_zero (by simpa using z.ne_zero)
 simp_all [u,r,qJ,↓weylElem_star,weylElem_succ,mem_unitriGroup_of_mem_floorGroup floorWeyl_mem_floorGroup,inf_of_le_right,IsNear.of_floorGroup_mul (x:=1) _ _ i.le_succ];ring_nf;simp
