import Lib.LocalGL.Iwahori.HeckeOnLineStabiliser
import New.Selmer.RibetFirstOrder
import Lib.GaloisRep.LocalGlobal.TypeFrobenius
import Lib.LocalGL.TaylorWiles.AuxPlaceOperators
section
open Nat Valued Finset IsLocalRing Units Matrix Pi GeneralLinearGroup SpecialLinearGroup
lemma kP {E} [Field E] [NumberField E] {w:FinPlace E} N [NeZero N] {m} (hm:m∣w.q-1) {u h} (hu:∀ z,z∈Subgroup.zpowers ((LocInt w).unitGroupToResidueFieldUnits ⟨u,h⟩)):∃ (H:Subgroup (GL (Fin N) (ResField w))) (a:H →* Multiplicative (ZMod m)) (lg d:_→ _),∃ γ,(∀ g:Kw _ w,(reduceGL g∈H↔g.1∈blockParahoric (min 1))∧(∀ h,a ⟨reduceGL g,h⟩=lg (g.1 0 0))∧a.transfer (reduceGL g)=d g.1.1.det∧(g.1∈proIwahori→ a.transfer (reduceGL g)=1∧∀ h,a ⟨reduceGL g,h⟩=1))∧lg u = .ofAdd 1∧a.transfer γ=d u∧N ! * (a.transfer γ).toAdd=N ! := by
 let H:=parabolic (R:=ResField w) (min 1 ∘ @Fin.val N)
 choose! Λ L using (@id <| IsUnit <| residueOrZero (w:=w) ·)
 have K {x y z}:residue _ y=x.1→ ↑y=z→ x=Λ z:=by grind [residueOrZero_coe,x.ext,IsUnit]
 have ⟨l,hz⟩:∃ l:_ →* Multiplicative (ZMod m),l (Λ u) = .ofAdd 1:=⟨_,(@K _ _ u rfl rfl).rec (monoidHomOfForallMemZpowers_apply_gen hu (by simpa [orderOf_eq_card_of_forall_mem_zpowers hu,card_units,← card_ResField] using! hm))⟩
 let a:=l.comp (⟨⟨(·.1 0 0),by simp⟩,fun _ h↦mul_apply.trans (Fintype.sum_eq_single 0 fun x hx↦by
   simp [@h.2 x 0 (by simpa [Fin.pos_iff_ne_zero] using hx)])⟩:H →* _).toHomUnits;let d:=a.transfer.comp (diagGL.comp (.mulSingle _ 0))
 simp [← card_ResField,← ZMod.natCast_eq_zero_iff] at hm
 have D {g}:g∈a.transfer.eqLocusM (d.comp det):=(Submonoid.mem_map_iff_mem coeHom_injective).1 (diagonal_transvection_induction_of_det_ne_zero _ _ g.det_ne_zero (fun D h↦⟨_,mulSingle_induction (diagGL ·∈_) (fun i↦mk0 (D i) (by simp_all [prod_eq_zero_iff])) (by
   simp) (by simp_all) fun i x ↦ .trans (by simp [mul_assoc,d,mulSingle_comp_equiv,eq_mul_inv_of_mul_eq (diagGL_mul_permGL (mulSingle i _) (.swap 0 i))]) congr(d $(x.ext (by
   simp [← Units.coe_prod]))),rfl⟩) (fun t↦⟨t.toSpecialLinearGroup,by simpa [*,↓map_nsmul] using! (congr(AddMonoidHom.mk' (fun c↦(a.transfer (toGL (transvection t.3 c))).toAdd) (by
   simp [transvection_add]) $card_nsmul_eq_zero')),rfl⟩) (by bound))
 refine ⟨_,a,l∘Λ,d∘Λ,_,fun g↦by
   simpa [blockParahoric,proIwahori,residuePreimage,↓Subgroup.copy_eq] using ⟨by bound,fun _ ↦
     congrArg l (K rfl rfl),D.trans (congrArg d (K (RingHom.map_det ..) (𝒪[_].subtype.map_det _))),fun _ k↦⟨D.trans (d.map_one▸congrArg d (ext (det_eq_one_of_unitriangular k))),fun _↦l.map_one▸congrArg l (ext (by simpa using! k 0 0))⟩⟩,hz,rfl,?_⟩
 simpa [*,index_stabilizer_line 0 (H:=H) fun _↦forall_congr' (by grind),mul_assoc,← mul_factorial_pred NeZero.out,mul_comm N] using! congr(_*($(D.symm.trans ((a.transfer_eq_pow (scalar _ _) (by simp [← map_pow,← GeneralLinearGroup.scalar_commute])).trans congr(l $(ext (v:=Λ u^H.index) (by simp [← map_pow])))))).toAdd)
open Subgroup IsComplement MulAction leftTransversals ZMod
attribute [-simp] zsmul_eq_mul zsmul_one
variable {Γ R} [Group Γ] [Fintype Γ] [Ring R] {m} [NeZero m] (ρ:Γ →* R) {H:Subgroup Γ} (c:Γ →* Multiplicative (ZMod m)) {S} [Ring S] (σ:R →+* S) (hm:(m:S)=0)
def zO:(ZMod m→ ℤ) →+ R := .mk' (∑ g,· (c g).toAdd•ρ g) (by simp [add_smul])
omit [NeZero m] in
lemma vO f g:ρ g*zO ρ c f=zO ρ c (f <| · - (c g).toAdd):=(mul_sum ..).trans (sum_equiv (.mulLeft g) (by simp) (by simp))
include hm
omit [NeZero m] in
lemma qK {ι} (B:_ →+ R) (f g:ι→ ℤ) (h:∀ x,(g x:ZMod m)=f x):σ (B f)=σ (B g):=by simpa [hm,↓map_nsmul] using congr(σ (B $((funext (h · |> (intCast_eq_intCast_iff ..).1 |>.dvd.choose_spec):f-g=m•_))))
omit [NeZero m] in
private lemma k5 (a:H →* Multiplicative (ZMod m)) (B:_ →+ R) (hB:∀ f (p:H),B f*ρ p=B (f <| · - (a p).toAdd)) (𝒜:Subring R) (hρ:∀ g,ρ g∈𝒜) (h𝒜:∀ f,B f∈𝒜) {A} {ac:A→ R} (hc:∀ {x},x∈𝒜→ ∀ t,Commute (ac t) x) {Ψ L γ} {n k:ℕ} (hΨ : ∑ p:H,ρ ↑p⁻¹*Ψ*ρ p=n) (hX:∀ p∈H,ρ p*B 1=B 1) (h:L*B 1=0) (hL:∀ g,L*ρ g=L) (tf:IsSMulRegular R (Fintype.card Γ)) (hn:k*(a.transfer γ).toAdd=k):∃ F∈𝒜,(∀ g,∃ Z,σ (n•(F*(ρ g-1)))=σ ((∑ g,ρ g)*Z)∧L*Z=0)∧∀ {t t' r},(∀ f:ZMod m→ ℤ,B ((f <| · - k)-f)*ac t=zO (ρ.comp H.subtype) a ((f <| · - k)-f)*ac t')→ (∀ f,zO ρ a.transfer f*ac t'=(ρ γ-1)*zO ρ a.transfer f*r)→ (2*k)•(σ F*σ (ac t))=(2*k)•(σ (∑ g,ρ g)*σ r):=by
 let T := ∑ η:Γ⧸H,ρ η.out
 let U := ∑ η:Γ⧸H,ρ η.out⁻¹
 let v := @valMinAbs m
 let w (g x:Γ):H:=⟨_,QuotientGroup.eq.1 (g•x:Γ⧸H).out_eq⟩
 have key (f:H→ ℤ) x:T*(∑ p,f p•ρ p)*ρ x⁻¹ = ∑ g,f (w g x)•ρ g:=by
   rw [sum_mul_sum,← sum_product',sum_mul,sum_nbij' (fun (η,p)↦η.out*p*x⁻¹) fun g↦(↑(g*x),w g x)] <;> simp [w]
 have e:(∑ g,ρ g)*(Ψ*B 1)=n•T*B 1:=by simpa [← by simpa using key 1 1,hX,←
   (Equiv.sum_comp (.inv H) (ρ ·)),sum_mul,mul_assoc,← nsmul_eq_mul] using congr(T * $hΨ*B 1)
 use T*B (-v)*U,by grind [mul_mem,sum_mem],fun g↦⟨Ψ*B 1 * ∑ η:Γ⧸H,v (a (w g η.out)).toAdd•ρ η.out⁻¹,?_,by simp [← mul_assoc,@tf _ 0 (by simpa [T,mul_sum,← mul_assoc,hL,h,-nsmul_eq_mul] using congr(L * $e))]⟩,fun h₁ h₂ ↦ .trans ?_ (congr(-σ $(h₂ ((2*k)•v))).trans ?_)
 · rw [← mul_assoc,e,mul_sub,mul_assoc,sum_mul _ _ (ρ g),← Fintype.sum_equiv (toPerm g) (fun η↦ρ (w g η.out*η.out⁻¹)) _ (by simp [w,mul_assoc])]
   simp [mul_sum,mul_assoc,← mul_assoc (B _),hB,sub_mul,mul_sub,U,v,fun y↦qK σ hm B (v <| · - y) (v-v y•1)]
 · have e₂:σ (T*zO (ρ.comp H.subtype) a v*U)=σ (zO ρ a.transfer v):=by
     erw [mul_sum,funext fun _↦key ..,← map_sum (Fintype.linearCombination ..).toAddMonoidHom];apply qK σ hm;simp [v,diff,fun g↦a.transfer_def (g⁻¹•default) g,mul_assoc,smul_apply_eq_smul_apply_inv_smul,leftQuotientEquiv_apply _];congr!;simp
   simpa (disch:=simp_intro x [v];ring) [← e₂,mul_assoc,(@hc U (sum_mem (by tauto)) _).eq,-map_sub,-nsmul_eq_mul,qK σ hm _ _ ((2*k)•v)] using congr(σ (T * $(h₁ fun x ↦ -v x*(v x+k))*U))
 rw [sub_one_mul,vO,← map_sub,map_mul,qK σ hm _ _ (-2*k)] <;> simp [zO,v,← mul_sum,mul_sub,mul_assoc,@zsmul_eq_mul S,hn]
end
section
open Function Nat Algebra ComplexOrder Fint Fintype Group Module MonoidHom Pi Polynomial Submodule
attribute [-instance] LinearMap.instLoewnerPartialOrder SetLike.GradeZero.instCommRing Subalgebra.normedCommRing SubfieldClass.toSubringClass
attribute [-simp] _root_.mul_apply
variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [CMType E] [Algebra E Ω] {n} [Fintype n] [Nonempty n] {V κ J} [Fintype J] {ν c} {D:BaseLevel V κ c} (Q:TaylorWilesPlaces E J (ℓ^ν)) (hQ:∀ j,D.IsOffLevel ![] (Q.w j)) {N:Isotypic V κ→ GalRep ℓ E n} {L:J→ FinPlace E} [V.IsStd] [WeilData E] {a:_ →* EllAdicIntegers} (hN:∀ x g,(N x g).1=algebraMap EllAdicIntegers (PadicAlgCl ℓ) (a g)•(x.galRep g).1) (ha:∀ j,a (Q.frobData j).isPlaceOver.tameGenerator=1)
omit [Nonempty n] [V.IsStd] [WeilData E] in
lemma BaseLevel.k4 {j} {r s:D.heckeAlgebra Q.w} {Γ} [Group Γ] [Fintype Γ] {ρ:Γ →* D.integralEnd Q.w} {c g b} k i (B:_ →ₗ[ℂ] _) (hρ:∀ g,ρ g∈D.localOps Q j) (hb:∀ y,b.1 y=B ((zO ρ c g).1 y)) (f:ZMod (ℓ^ν)→ ℂ) (h:∀ x (ψ:AddChar _ ℂ) z,z.1∈x.1.1→ (∀ g,(ρ g).1 z=ψ (c g).toAdd•z)→ z.1≠0→ ψ k≠i→ ιℓ.symm (r.1 x)•z.1=ιℓ.symm (s.1 x)•B z) (e:∀ x,f (x-k)-i*f x=g x:=by simp) :
 zO ρ c g*heckeAction r=b*heckeAction s:=Subtype.ext (formEnd_ext fun x y hy↦by
 let T := ∑ g,(.proj ((c g).toAdd-k)-i • .proj (c g).toAdd:(_→ ℂ) →ₗ[ℂ] ℂ).smulRight
   ((ρ g).1 y);ext1
 simpa [T,hb,zO,e,Int.cast_smul_eq_zsmul,heckeAction,systemAction,diagOp_apply _ x hy,← SetLike.mk_smul_mk,LinearMap.restrict_apply] using congr($(((AddChar.complexBasis _).ext fun ψ↦dite _ _root_.id fun o↦h x ψ⁻¹ _ (by choose a q using hρ;simp [T,q,sum_mem,smul_mem,Isotypic.map_mem (a _).2 hy]) (fun g↦by simpa [T,Finset.smul_sum] using sum_equiv (.mulLeft g) _ _ (by simp [← ψ.map_add_eq_mul,smul_smul,mul_left_comm,mul_sub,add_sub])) (o∘by simp +contextual) (o <| by simp [← ·,T,sub_eq_neg_add,ψ.map_add_eq_mul]):ιℓ.symm _•(formsOfLevel _).subtype∘ₗT=ιℓ.symm _•B∘ₗT)) f))
include hN
lemma BaseLevel.charpoly_mem_heckeAlgebra g i:(N ·.1 g |>.1.charpoly.coeff i)∈D.heckeAlgebra L:=by
 simp_rw [hN,charpoly_smul_coeff];refine mul_mem (pow_mem (algebraMap_mem _ (a g)) _) (isClosed_heckeAlgebra.mem_of_tendsto (tendsto_pi_nhds.2 (·.2.elim fun _ ⟨m,h⟩↦(Isotypic.attached_galRep m.1 h).tendsto_charpoly_coeff ..)) (Filter.mem_inf_of_left (eventually_mostFrobenii (D.eventually_isOffLevel (L:=L)) fun w ⟨_,_,k,h⟩ ↦ ?_)));simp [-Int.cast_ite]
 exact mul_mem (intCast_mem ..) fun y e↦(formsOfLevel_le_of_eigensystem (N:=(heckeSplit (V.formTranslation κ) (isSplit_of_q_prime w.prime_q) _).eqLocus (diagOp _)) (fun x f m↦by simp [diagOp_apply _ x m.1,by simpa [eigenformsAt] using h _ x.2 m];rfl) y.2).subst (localGroupAlgebra_le_endPreserving k (heckeFun_mem_localGroupAlgebra _ (.id _)) _ e)
noncomputable def BaseLevel.jC (P:EllAdicIntegers[X]) (h g:Gal(Ω/E)):D.heckeAlgebra L:=⟨fun x↦(aeval (N x h).1 P*(N x g).1).trace,by simpa [aeval_eq_sum_range,Finset.sum_mul,Finset.sum_fn,neg_def,← Matrix.trace_eq_neg_charpoly_coeff] using (sum_mem fun k _↦(heckeAlgebra L).smul_mem (neg_mem (charpoly_mem_heckeAlgebra hN (h^k*g) (card n-1))) (P.coeff k))⟩
include hQ ha
seal zO in
attribute [-instance] Subalgebra.toCommRing in
lemma BaseLevel.wY j {e t} (ht:t≠0) T (H:∀ x,x.1∈D.Eigensystem ![]→ T.1 x≠0→ HasRootString (x.1.heckePolyAt (Q.w j)) (e.map (algebraMap EllAdicIntegers ℂ)) (Q.w j).q (algebraMap EllAdicIntegers ℂ (a (Q.frobData j).frob))⁻¹ t) {R} [Ring R] (σ:_ →+* R) (hm:((ℓ^ν:ℕ):R)=0):let ρ:=(D.residueRep Q).comp (.mulSingle _ j);let N := ∑ g,ρ g;∃ F ∈
     D.localOps Q j,(∀ g,∃ Z,σ (c•(F*(ρ g-1)))=σ (N*Z)∧heckeAction T*(∑ g,D.residueRep Q g)*Z=0)∧∀ g,let r:=σ (heckeAction (jC hN (X-1) (Q.frobData j).isPlaceOver.tameGenerator g));σ N*r=0∧(2*(card n)!)•(σ F*r)=(2*(card n)!)•(σ N*σ (heckeAction (jC hN ((X-1)*e) (Q.frobData j).frob g))):=by
 intro ρ
 set θ:=Q.frobData j
 obtain ⟨⟨ε,_,q,A,U⟩,⟨_,_,l,W⟩,ϖ,vϖ,s⟩:=θ.isPlaceOver.exists_localArtin_eq_tameGenerator,hQ j,θ.isPlaceOver.exists_localArtin_eq θ.isFrob 1
 let p:=X*e-(Q.w j).q^t.pred•e
 choose K b lg d γ hK hu hγ bu using kP (card n) (Q.dvd_q_sub_one j) A
 let π:=localFormRep V κ (Q.apart.2 j j);let ρ':=ρ.comp K.subtype;let G:=p.comp (C (a θ.frob)*X)
 have act {k} (m:k∈blockParahoric _) y:π k _=(ρ' ⟨_,(hK ⟨k,m.1⟩).1.2 m⟩).1 y:=(residueRep_mulSingle hQ ⟨k,_⟩ y).symm
 have k0 y (h:∀ p,b p=1→ b.transfer p=1→ (ρ' p).1 y=y) :
   ↑y∈levelSpace π.ρ proIwahori :=
   fun g↦by simp [act (proIwahori_le_blockParahoric (by omega) g.2),h,(hK _).2.2.2]
 have k1 f y:=k0 _ fun p h _↦congr($(vO ρ' b f p).1 y).trans (by simp [h])
 choose B hB eB using (exists_localOps_aeval_hecke hQ (by simp [zO,ρ',ρ,sum_mem,mul_mem,residueRep_mem_localOps hQ]) (diagGL (Pi.mulSingle 0 ϖ)) G <| k1 ·)
 refine (k5 ρ σ hm b (.mk' B fun _ _↦by ext;simp [eB]) (fun _ p↦by
   ext;simpa [eB,zO,-zsmul_eq_mul] using sum_equiv (.mulRight p) _ _ (by simp [ρ']))
   (D.localOps Q j).toSubring (residueRep_mem_localOps hQ) hB localOps.commute_heckeAction
   (exists_higman_operator hQ (.comp (.mulSingle _ j) K.subtype) fun _↦by simp).choose_spec (reduceGL_surjective.forall.2 fun k m↦by
   ext y:3;simpa [eB,ρ,residueRep_mulSingle hQ k] using! (aeval_apply_smul_mem_of_le_comap (by
     use k1 1 y,fun c m↦by simpa [act m] using! congr($(vO ρ' b 1 _).1 y)) (G.map (algebraMap ..)) _ (heckeCoset_mem_parahoricEigenspace π vϖ (χ:=1))).2 _ ((hK _).1.1 m)) ?_
   (by simp [ρ,mul_assoc,← map_mul,Finset.sum_mul,(mulRight_bijective _).sum_comp]) (fun _ _ h↦Subtype.ext (smul_right_injective _ card_ne_zero congr($h))) bu).imp fun F ↦ .imp_right (.imp_right ?_)
 ·
   obtain ⟨F,hF,hF'⟩:=V.exists_isUnitary_formTranslation κ;ext y:3
   refine by_contra (hF _ · |>.ne' (congr(F _ ($((Commute.sum_right _ _ _ fun g _↦Submonoid.pi_mem_of_mulSingle_mem (H:=(Submonoid.centralizer {_}).comap _) g (fun _↦forall_eq.2 (localOps.commute_heckeAction (residueRep_mem_localOps hQ _) T)) _ rfl).mul_right (localOps.commute_heckeAction (hB _) _)).1 y).1).trans (formsOfLevel_le_of_eigensystem (N:=(F.flip _ ∘ₛₗ diagOp _).ker) (fun x w m↦by_contra fun h ↦ ?_) (mem_baseLevel_iff_residueRep_fixed.2 fun g↦by simpa using sum_equiv (.mulLeft g) _ _ (by simp)))))
   let ξ:Eigensystem Q.w:=⟨x.1,x.2.imp fun _ ↦ .imp_left (.imp_right (formsOfLevel_base_le _ ·))⟩
   simp [diagOp_apply _ ξ m.1,← Finset.mul_sum] at h;obtain ⟨hK,_,i,o⟩:=hasHeckePolyAt_iff_localFormRep.1 (hasHeckePolyAt_of_mem_eigenformsAt (W _ x.2 m) _);refine h.2 (sum_eq_zero _ fun g↦congr(F $(mem_baseLevel_iff_residueRep_fixed (y:=⟨_,formsOfLevel_base_le _ m.2⟩).1 m.2 g).1 _).symm.trans ((hF' ..).trans ?_));erw [coe_subtype,eB,← aeval_map_algebraMap ℂ]
   simpa [G,p,e.map_comp] using (chain_lemma ⟨hF,by tauto⟩ hK (h.2 <| by simp [·]) i o vϖ).2 _
     (((isUnit _).map a).map _).ne_zero _ _ (succ_pred ht▸H ξ x.2 h.1 :) _ (k1 1 _)
 intro h g u
 let P g:_ →+ D.heckeAlgebra Q.w := .mk' (jC hN · θ.frob g) (by simp [jC,add_mul,add_def])
 let r:=P (θ.isPlaceOver.tameGenerator*g)-P g
 rw [(congr(σ (heckeAction $(by ext;simp [r,P,jC,sub_mul]))):u=σ (heckeAction (r 1)))]
 have hS p f:zO ρ b.transfer f*heckeAction (r p)=(ρ γ-1)*_*heckeAction (P g p):=k4 Q 0 0
   ((formsOfLevel _).subtype∘ₗ(ρ γ-1).1) (residueRep_mem_localOps hQ) (by tauto) (f ·) fun x ψ
   z m h o _↦by simp [h,r,P,jC,hN _ θ.isPlaceOver.tameGenerator,ha,hγ,by simpa [← Units.coe_prod] using ((galRep_of_parahoric_type θ.isPlaceOver vϖ s θ.isFrob U q (by simp) l m o 0 ⟨k0 z (by simp +contextual [h,ρ']),fun k m ↦
   by simpa [hK] using (residueRep_mulSingle hQ ⟨k,m.1⟩ _).symm.trans congr($(h _))⟩ (by simp)).1
   (X-ιℓ (ψ (d ε).toAdd)•1) :)];module
 exact ⟨by simpa [↓sub_mul,↓vO,zO] using congr(σ $(hS 1 1)),(h (fun f ↦ .symm (k4 Q (card n)! 1 (ρ:=ρ') (.domRestrict ..) (residueRep_mem_localOps hQ ·.1) (eB _) (f ·) fun x ψ z m h _ o↦by
   simpa [r,P,jC,G,ha,hN _ θ.isPlaceOver.tameGenerator,hN _ θ.frob,mul_sub,sub_mul,mul_assoc,aeval_comp,← Algebra.smul_def,map_map,(RingHom.ext iota_ell_algebraMap:ιℓ.toRingHom.comp _=_),-RingEquiv.toRingHom_eq_coe] using (hecke_eq_frob_on_parahoricEigenspace θ.isPlaceOver vϖ s θ.isFrob U q (by simp) l m (ψ <| lg · |>.toAdd) (ψ.val_isUnit _).ne_zero (by simp [*,← ψ.map_nsmul_eq_pow]) (G.map (algebraMap ..)) ⟨k0 z (by simp +contextual [h]),fun k o↦(act o z).trans (by simp [h,hK])⟩).symm)) (hS p)).trans congr(_•(_ * $(show _=σ (heckeAction (P g _)) by simp [↓p,↓sub_mul,-nsmul_eq_mul,↓nsmul_eq_mul _ (σ _),-map_smul,by simpa using hm.symm.dvd.trans (Q.dvd_q_sub_one j).natCast])))⟩
attribute [-instance] Ideal.Quotient.isScalarTower IsScalarTower.to_smulCommClass Module.End.instDivisionRing Subalgebra.seminormedCommRing Subalgebra.smulCommClass_left
attribute [-simp] CompTriple.comp_eq map_pow map_smul _root_.mul_eq_zero smul_eq_zero
lemma BaseLevel.exists_diagOp_mem_ellIntegralForms (b:D.Eigensystem Q.w→ PadicAlgCl ℓ) (p:EllAdicIntegers[X]) (𝓧:Set (D.Eigensystem Q.w)) (π:𝓧) e {t} (ht:t≠0) (he:∀ j (x:D.Eigensystem Q.w),x.1∈D.Eigensystem ![]→ aeval (b x) p≠0→ (∀ u:D.heckeAlgebra Q.w,u.1 x=0→ ‖u.1 π‖< 1)→ HasRootString (x.1.heckePolyAt (Q.w j)) ((e j).map (algebraMap EllAdicIntegers ℂ)) (Q.w j).q (algebraMap EllAdicIntegers ℂ (a (Q.frobData j).frob))⁻¹ t) (hν:(2*(card n)! : ℕ)*(p.coeff 0*c^2)^(card J+1)∣ℓ^ν) {m γ} (rib:∀ S 𝒥,IsTraceIdeal (S:=S) (Y:=D.Eigensystem Q.w) 𝒥 (N ·.1 · |>.1) (ℓ^ν:EllAdicIntegers) (Q.frobData · |>.isPlaceOver.tameGenerator) (Q.frobData · |>.frob) (·) e→ ∃ d,IsRibetElement 𝒥 b π d∧ellVal (m*d)≤ γ):∃ s,ellVal (m*s π.1)≤ γ∧∀ l∈D.formsOfLevel ![],∀ d:ℕ,d•l∈ellIntegralForms→ ∀ y∈D.formsOfLevel ![],(∀ s,(∀ x∈𝓧,s x=0)→ diagOp s y=0)→ (∀ s,(∀ x,aeval (b x) p=0→ s x=0)→ diagOp s l=diagOp s y)→ d•c•diagOp s y∈ellIntegralForms:=by
 choose u u₀ u₁ using @Subtype.prop _ (∃ u:heckeAlgebra _,u.1 · = 0∧1≤ ‖u.1 π.1‖)
 set k:=_+1;let ψ:=AlgHom.pi fun x:Eigensystem _↦MvPolynomial.mapAlgHom (σ:=J)
   ((evalAlgHom _ _ x).comp (D.heckeAlgebra Q.w).val)
 obtain ⟨_,⟨⟨β,hβ⟩,⟨_,f,rfl⟩,⟨F,hI,hf⟩,h₅,rfl⟩,hP⟩:=rib ψ.range ⟨(span _ {z:MvPolynomial J (D.heckeAlgebra Q.w) | ∃ g,z=ℓ^ν • .C (jC hN 1 1 g)∨∃ j,z = .C (jC hN (X-1) (Q.frobData j).isPlaceOver.tameGenerator g) - .X j * .C (jC hN ((X-1)*e j) (Q.frobData j).frob g)}).1.map ψ,by
   rintro ⟨_,a,rfl⟩ _ ⟨b,h,rfl⟩;use a*b,smul_mem _ a h,map_mul ..⟩ (by refine ⟨(⟨.X ·,?_⟩),(⟨.C ⟨_,charpoly_mem_heckeAlgebra hN · ·⟩,?_⟩),fun g↦⟨⟨_,subset_span ⟨g,.inl rfl⟩,?_⟩,(⟨_,subset_span ⟨g,.inr ⟨·,rfl⟩⟩,?_⟩)⟩⟩ <;> simp [ψ,jC,map_pow,Algebra.smul_def,funext_iff])
 lift b to D.heckeAlgebra Q.w using (funext (by simpa [ψ] using congr($hβ · |>.constantCoeff))).subst β.constantCoeff.2
 obtain rfl:F = .C b*f:=by ext;simpa [ψ,mul_comm (f.map _)] using! congr(($hf _).coeff _)
 set o:J →₀ ℕ:=Finset.sum ..
 let A := ∏ x,u x;let T:=A*aeval b p;let P:=c^2•T
 refine ⟨(A^k*f.coeff o :),(ellVal_le_ellVal (by
   simp [A];grw [← u₁];simp;rfl)).trans hP,fun l hl d il y hy m ey ↦ ?_⟩
 obtain ⟨⟨w,hw⟩,⟨Ψ,hΨ⟩,v,hv⟩:=hν,exists_higman_operator hQ (.id _) injective_id,(Ideal.Quotient.eq_zero_iff_dvd b (P^k-(p.coeff 0*c^2)^k•A^k)).1 (by
   simp [P,T,map_pow,aeval_def,hom_eval₂,Algebra.smul_def]
   ring)
 lift l to D.formsOfLevel Q.w using formsOfLevel_base_le _ hl;lift y to D.formsOfLevel Q.w using formsOfLevel_base_le _ hy
 obtain ⟨B,σ,z,hm,ker⟩:∃ (B:ModuleCat EllAdicIntegers) (σ:_ →ₐ[EllAdicIntegers] End EllAdicIntegers B),∃ z,((ℓ^ν:ℕ):End EllAdicIntegers B)=0∧∀ s,T∣s→ (σ (heckeAction s) (σ (∑ g,D.residueRep Q g) z)=0↔∃ V:integralEnd _,ℓ^ν•V.1 l=c•(heckeAction s).1 y):=let:=Module.compHom (D.formsOfLevel Q.w) (D.integralEnd Q.w).val.1
   let e:=LinearMap.toSpanSingleton ..
   ⟨.of EllAdicIntegers (_⧸(ℓ^ν•e).range.comap e),lsmul ..,mkQ _ Ψ,LinearMap.ext (Quot.ind ((Quotient.mk_eq_zero _).2 ⟨·,rfl⟩)),fun s ⟨_,h⟩↦(Quotient.mk_eq_zero _).trans (exists_congr fun _↦Eq.congr_right ((congrArg (heckeAction s).1 (by
     simpa [← Equiv.sum_comp (.inv _) (D.residueRep Q),mem_baseLevel_iff_residueRep_fixed.1 hl] using congr(($hΨ).1 l):_=c•l)).trans ((map_nsmul ..).trans (congrArg _ (Subtype.ext (ey _ (by simp +contextual [h,T,aeval_eq_sum_range])))))))⟩
 choose F hF h hu using fun j↦wY Q hQ hN ha j ht T (fun x h↦by
   simpa [T,A,_root_.mul_eq_zero,Finset.prod_eq_zero_iff,aeval_eq_sum_range,-not_exists,-Subtype.exists] using fun e f↦he j x h f fun v a↦not_le.1 (e ⟨_,u₀ ⟨x,v,a,·⟩⟩)) σ hm
 generalize 2*_=κ at hw hu
 let Φ:=noncommPiCoprod (fun j↦(σ.comp (D.localOps Q j).val).toMonoidHom) fun i j h ⟨_,p,a⟩ ⟨_,q,b⟩ ↦ .map (by
   ext y:3;simpa [*] using congr($(commute_of_mem_adjoin_of_forall_mem_commute q.2 fun _ ⟨_,m,e⟩↦e▸(commute_of_mem_localGroupAlgebra p.2 (by simp [Gf.mem_supportedOn.1 m,Q.apart.1.ne h,Q.apart.2])).symm) y)) σ
 have U j x:Φ x=_*σ (x j):=(by simpa [Φ,← Pi.mulSingle.eq_1] using congr(Φ $(update_mul x 1 j 1 (x j))))
 let M j:D.localOps Q j := ∑ g,⟨_,residueRep_mem_localOps hQ g⟩
 let S (d:J →₀ ℕ) j:=[⟨_,hF j⟩,M j].getD (d j) 0
 let Θ:=Φ∘S
 have cm t d z:=by simpa using congr($(Commute.eq (b:=Θ d) (commute_noncommPiCoprod _ (fun _ ⟨_,x⟩↦(localOps.commute_heckeAction x t).map σ) _)) z)
 have top:Θ o = ∑ g,σ (D.residueRep Q g):=by
   refine .trans congr(Φ $(by simp [o,M])) (((MultilinearMap.mk' (R:=EllAdicIntegers) Φ ?_ ?_).map_sum fun _ g↦⟨_,residueRep_mem_localOps hQ g⟩).trans congr(∑ g,$(noncommPiCoprodEquiv.4 (σ.toMonoidHom.comp (D.residueRep Q))) g)) <;> intro _ i _ _ <;> simp [U i,mul_add,σ.map_smul_of_tower]
 have zero d (hd:¬d≤ o):Θ d=0:=(not_forall.1 hd).rec (by simp +contextual [Θ,U ·,S,o])
 have step {j t r d}:σ (F j)*t=σ (M j)*r→ σ (M j)*t=0→ Θ d*t=Θ (d + .single j 1)*r:=by rcases h:d j with _ | _ | n <;> simp +contextual +unfoldPartialApp
     [Θ,S,U j,Function.update,mul_assoc,h]
 have F2 n d z (e:k≤ d.degree+n) (H:Θ o (σ (heckeAction T) z)=0) :
   σ (heckeAction (P^n)) (Θ d z)=0:=by
   induction' n with n ih generalizing d z
   · simp [zero d (mt (Finsupp.degree_mono ·) (by simpa [o]))]
   let W:=σ (heckeAction (P^n))*Θ d*c
   have inv g:_=_:=Submonoid.pi_mem_of_mulSingle_mem (H:=Submonoid.mk ⟨{g | W*σ (D.residueRep Q g)=W},by simp +contextual [← mul_assoc]⟩ (by simp)) g fun j↦sub_eq_zero.1 (by
     obtain ⟨Z,k,l⟩:=h j (g j)
     rw [← _root_.mul_sub_one,mul_assoc,mul_assoc,step (by simpa [M,← nsmul_eq_mul] using k) (by simp [M,mul_sub,Finset.sum_mul,← map_mul,← mulSingle_mul,↓← nsmul_eq_mul,(mulRight_bijective _).sum_comp fun g↦σ (D.residueRep Q _)])]
     ext;exact ih _ _ (by simpa [add_right_comm]) (by simpa [← top,cm] using congr(σ $l _)))
   simpa [W,H,P,pow_succ,cm] using congr($(show W*σ c=W*σ Ψ*Θ o by
     simp [← hΨ, *,Finset.mul_sum,← mul_assoc]) (σ (heckeAction T) z))
 let L := ∑ d≤ o,Θ d•(σ.comp heckeAction).toAddMonoidHom.comp (MvPolynomial.coeffAddMonoidHom d)
 have Lm e s:L (.monomial e s)=Θ e*σ (heckeAction s):=by simp +contextual [L,apply_ite,zero]
 simp [sub_mul] at hu
 have K:=closure_induction (p:=fun F _↦κ•L F=0) (by simp) (by simp +contextual)
   (·.induction_on' (by
   rintro e s _ ⟨g,rfl | ⟨j,rfl⟩⟩ <;> simp [← MvPolynomial.monomial_zero',mul_sub,hm,Lm,MvPolynomial.X,mul_assoc,mul_comm s,sub_mul,↓nsmul_eq_mul' (_:End ..),-nsmul_eq_mul]
   apply step <;> simp [M,↓hu,← κ.cast_comm,↓← mul_assoc]) (by simp +contextual [add_mul,-Set.mem_ofPred_eq])) (smul_mem _ (.C v) hI)
 have mx s h:(heckeAction s).1 y=0:=Subtype.ext (m s h)
 obtain ⟨V,e⟩:=(ker (P^k*w•κ•_) (.mul_right (by simp [P,dvd_pow]) _)).1 (by
   simpa [↓L,↓← top,↓cm,↓by simpa [cm] using (Finset.sum_eq_single_of_mem o (Finset.mem_Iic.2 le_rfl) fun d h e↦F2 k d _ le_add_self (by simpa [← top,cm] using (ker _ ⟨f.coeff d,rfl⟩).2 ⟨0,by
     simp [mx (f.coeff d) (h₅ ⟨·,·⟩ |>.2 d ((Finset.mem_Iic.1 h).lt_of_ne e))]⟩)),↓← mul_assoc v,
     ↓mul_comm v b,↓← hv,↓← Finset.smul_sum,smul_sub,AlgHom.map_smul_of_tower,by
     simpa [hw,mul_comm _ w,← cast_smul_eq_nsmul EllAdicIntegers,↓End.natCast_apply] using (congr($hm ·)),smul_smul,← cast_smul_eq_nsmul EllAdicIntegers] using congr(w • $K z))
 simpa [-map_mul,show _=c•(heckeAction (A^k*f.coeff o)).1 y from smul_right_injective _ NeZero.out (e.trans (by simp [eq_add_of_sub_eq hv,add_mul,mul_rotate b,mx _ (h₅ ⟨·,·⟩ |>.1),AlgHom.map_smul_of_tower,↓← cast_smul_eq_nsmul EllAdicIntegers,hw];module))] using! V.2 (d•l) il
end
