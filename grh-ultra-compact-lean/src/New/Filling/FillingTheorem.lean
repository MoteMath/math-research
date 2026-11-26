import New.Heights.Heights
import Lib.SiegelWeil.OneVector.OneVector
import New.Filling.BlockBound
import New.Trace.BadShare
import New.Seesaw.UnfoldingStages
import New.Filling.RowDimension
section
open Module InnerProductSpace Finset EuclideanSpace Complex Matrix WithLp Fintype AddChar Submodule OrthonormalBasis LinearMap
variable {G H k n m} [Group G] [Fintype G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Field k] [Fintype n] [Fintype m] (b : OrthonormalBasis m ℂ H) {u v : G→H}
lemma zk f (h : ∀ a b, ⟪u a,v b⟫_ℂ=f (a⁻¹ * b)) : ⟪∑ a,u a,∑ a,v a⟫_ℂ =
  card G * univ.sum f:=by simp [↓sum_inner,inner_sum,h,(Group.mulLeft_bijective _).sum_comp]
lemma zl [Fintype k] (π : G →* GL n k) (A : _→Matrix n m k) {Θ} (h0 : ∀ s,0 ≤ Θ s) (hu : ∀ a b, ⟪u a,u b⟫_ℂ = Θ (a⁻¹ * b)) Y (hY : 0≤Y) (h : ∀ b,∀ v≠0,∑ s with A b *ᵥ v=cond b invTransposeGL 1 (π s)•A b *ᵥ v, Θ s≤Y) : card k * ∑ s with ((A true)ᵀ * (π s).1 * A false).det=0, Θ s≤2 * univ.sum Θ + card k ^ card m * √(card k ^ card n) * Y:=by
  set r:=√_;obtain ⟨ψ,p⟩ : ∃ _,_:=⟨_,FiniteField.primitiveChar_to_Complex_isPrimitive k⟩
  have N {c : (n→k)→EuclideanSpace ℂ (n→k)} (h : Orthonormal ℂ c) {σ : MulAut _} x :
      ∑ s with x = σ (π s)•x, Θ s=‖∑ a,c (σ (π a)•x) ⊗ₜ[ℂ] u a‖ ^ 2 / card G
  rw [@norm_sq_eq_re_inner ℂ,zk (ofReal∘_)];simpa using sum_filter ..;simp [*,orthonormal_iff_ite.1,apply_ite ofReal,mul_smul,eq_inv_smul_iff];let W y v s := ψ (y ᵥ* (A true)ᵀ ᵥ* π s ᵥ* A false ⬝ᵥ v) * Θ s;apply ((sum_mono fun y↦univ.expect_le_expect fun v _↦(?_ : re (∑ s,W y v s) ≤ ite (y=0) (∑ s, Θ s) 0 + ite (v=0) (∑ s, Θ s) 0 + r * Y)).trans _).trans';simp [W, -ite_mul,sum_comm,mul_sum,sum_filter,apply_ite,↓← re_expect,← sum_mul,← mul_assoc,expect,NNRat.smul_def,sum_addChar_dotProduct p];gcongr;repeat' split;cases exists_vecMul_eq_zero_iff.2 ‹_›;grw [← card_univ,card_le_card_of_injOn _ _ (smul_left_injective _ (by tauto)).injOn]
  on_goal -1 => split_ifs; on_goal -1 =>
    apply flip id (add_le_add (h true y _) (h false v _));grw [@N fun x↦toLp 2 fun ζ↦ψ (-x ⬝ᵥ ζ) / r,N orthonormal_single,← add_div,← two_mul_le_add_sq,mul_assoc,← @re_inner_le_norm ℂ,zk (W y v · / r)]
  all_goals simp [*,smul_vecMul,mul_nonneg,expect_add_distrib,NNRat.smul_def,W,r,add_nonneg,sum_nonneg',inner,field,vecMul_mulVec,← Matrix.mul_assoc,orthonormal_iff_ite,two_mul,invTransposeGL,dotProduct_mulVec,div_mul_div_comm,← map_neg_eq_conj,← map_add_eq_mul,← ofReal_mul,transposeGL,add_assoc,← sum_div,neg_add_eq_sub,← sub_dotProduct,sum_addChar_dotProduct,Units.smul_def]
noncomputable def zm (v : n→H):=∑ x,toLp 2 (⟪v x,b ·⟫_ℂ) ⊗ₜ[ℂ] v x
@[simp] lemma inner_dyadSum {l} [Fintype l] (v : n→H) (w : l→H) : ⟪zm b v,zm b w⟫_ℂ =
  ∑ x,∑ y,‖⟪w y,v x⟫_ℂ‖ ^ 2:=by simp [zm,← mul_conj',inner,b.sum_inner_mul_inner, @sum_comm n]
lemma zn [FiniteDimensional ℂ H] (P : EuclideanSpace ℂ n →ₗ[ℂ] H) (R : End ℂ H) (U A : Submodule ℂ _) {ε} (k : ∑ x,‖(P.adjoint ∘ₗ P - 1) (.single x 1)‖ ≤ ε) (h : ∀ v∈U,P v - R (P v)∈A) : finrank ℂ U - ε - ∑ x,‖R (P (.single x 1))‖ ^ 2≤re ⟪zm b (P <| .single · 1),zm b (stdOrthonormalBasis ℂ A ·)⟫_ℂ:=by
  obtain u:=stdOrthonormalBasis ℂ U,congrArg re (trace_comp_comm' U.subtype (U.orthogonalProjectionOnto ∘ₗ (1 - P.adjoint ∘ₗ P))),
    ((stdOrthonormalBasis ℂ A).sum_sq_norm_inner_right <| orthogonalProjectionOnto _ ·)
  have B (T : End ℂ H) : ∑ i,‖T (P (basisFun n ℂ i))‖ ^ 2≥∑ j,‖T (P (u j))‖ ^ 2;simp_rw [← b.sum_sq_norm_inner_left,← adjoint_inner_right, @sum_comm m,sum_sq_norm_inner_right];grw [Orthonormal.sum_inner_products_le];exact u.orthonormal;simp_all [trace_eq_sum_inner _ (basisFun ..),trace_eq_sum_inner _ u,← ofReal_pow,norm_sub_rev,norm_coe,inner_sub_right,inner_single_left,adjoint_inner_right, -map_sub,sub_eq_iff_eq_add'];grw (transparency := .all) [re_le_norm,PiLp.norm_apply_le,norm_starProjection_apply_le,← B,← B A.starProjection,← sum_add_distrib,← Aᗮ.norm_starProjection_apply_le (R _)];gcongr;erw [← Aᗮ.starProjection.sub_mem_ker_iff.1 (by aesop),← norm_sq_eq_add_norm_sq_projection]
open Real NormedField
variable {Θ V W S : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Module.Finite ℂ V] [Module.Finite ℂ W]
def IsSpread {W} [AddCommMonoid W] [Module ℂ W] (B : S→V →ₗ[ℂ] W) η :=
  ∀ F : Submodule ..,let φ : ℝ := finrank ℂ F / finrank ℂ W
  ∃ s,finrank ℂ (comap (B s) F)≤((1 + φ) / 2 + η) * finrank ℂ V
lemma exists_few_translates {B : Θ → V →ₗ[ℂ] W} {η} (hη : 0 < η) (h : IsSpread B η) [Nontrivial V] : ∃ t, #t * finrank ℂ V≤5 * finrank ℂ W * Real.log (1 + η⁻¹)∧(1 - 4 * η) * finrank ℂ W≤finrank ℂ ↥(⨆ s∈t,(B s).range):=by
  let T (t : Finset Θ) := ⨆ s∈t,(B s).range;let ψ (F : Submodule ℂ W) := 5 * finrank ℂ W * Real.log (1 + finrank ℂ (W ⧸ F) / finrank ℂ W / η)
  refine (exists_maximalFor_of_wellFoundedGT (fun t↦#t * finrank ℂ V + ψ (T t)≤_) T ⟨∅,by
    simp [ψ];grw [finrank_quotient_le,div_self_le_one];simp⟩).imp fun t ⟨ht,m⟩ ↦
    (h (T t)).rec fun s _↦⟨ht.trans' (by bound), ?_⟩;by_contra
  obtain ⟨_ | _,m⟩:=em (finrank ℂ W=0), @m (insert s t),(T t).finrank_quotient_add_finrank,
    ((T t).mkQ ∘ₗ B s).index_eq_of_finiteDimensional <;> simp_all [T,index,t.iSup_insert]
  grw [range_comp,ker_comp,ker_mkQ,card_insert_le] at *;have : ψ (T t ⊔ (B s).range) - ψ (T t) ≤ -finrank ℂ V
  grw [← mul_sub,← log_div,log_le_sub_one_of_pos] <;> try positivity
  rify [field,(quotientQuotientEquivQuotientSup ..).finrank_eq] at *;nlinarith;simpa [T,m (by grind),finrank_pos.ne']
lemma exists_extend_basis_of_span_eq_top {n S} {y : Fin n→V} (i : LinearIndependent ℂ y) (h : span ℂ S = ⊤) : ∃ k z,(∀ a : Fin k,z a∈S)∧LinearIndependent ℂ (y ⊕ᵥ z)∧finrank ℂ V=n + k:=by choose w a _ j using exists_fun_fin_finrank_span_eq ℂ ((span ℂ (.range y)).mkQ '' S);choose z hz e using a;exists _,z,hz,(linearIndependent_span i).sumElim_of_quotient z (funext e▸j :);rw [span_image,h,← range_eq_map,range_mkQ,← finrank_quotient_add_finrank,finrank_span_eq_card i];simp;lia
lemma one_determinant {θ : _ → Θ} {H : Θ → Type} [∀ ϑ,NormedAddCommGroup (H ϑ)] [∀ ϑ,InnerProductSpace ℂ (H ϑ)] (u : ∀ ϑ,W →ₗ[ℂ] H ϑ) {o} (hu : (⇑(u o)).Injective) [Fintype S] {x : S→W} (i : LinearIndependent ℂ x) (hk : finrank ℂ W=card S) {α δ g} (hα : ∀ σ : ℂ ≃+* ℂ,‖σ (gram ℂ (u o∘x)).det‖ ≤ Real.exp α) {γ : _ → ℂ} (γ0 : ∀ ι, γ ι ≠ 0) (hγ : HeightLe g fun ι↦(‖γ ι‖ ^ 2 :)⁻¹) {e : ℕ → ℝ} (he : ∀ U,∑ l∈U,e l ≤ δ) (Λ : ∀ ι : PrimePadicIso,(ℂ →+* ℂ_[ι.1])→Set (H (θ ι))) (k : ℕ) (w : ∀ ι j,∀ x ∈ Λ ι (j.comp (starRingEnd ℂ)),∀ y ∈ Λ ι j,‖j ⟪x,y⟫_ℂ‖ ≤ 1) (l : ∀ ι j,∃ m,Real.exp (-e ι.1) * ‖j (γ ι)‖ ^ k≤‖j (det m)‖ ∧ ∀ i,∑ l,m i l•u _ (x l) ∈ Λ ι j) : HeightLe (α + 2 * δ + k * g) fun ι↦(u (θ ι)).normDet ^ 2 / (u o).normDet ^ 2:=by
  have Z:=det_gram_ne_zero_iff_linearIndependent.2 (i.map_injOn _ hu.injOn)
  refine (IsUnit.div_mul_cancel (by simp [Pi.isUnit_iff, *]) _).subst
    (.mul ⟨_, α,2•e,Z,hα,fun ι↦?_,by simp [← mul_sum, *]⟩ (hγ.pow k))
  choose m a b using l ι;let j := complexToCp ι.2
  have : ‖j (_ᴴᵀ * (_ * (m j)ᵀ)).det‖ ≤ 1:=IsIntMatrix.det_mem (R:=valuation.integer.comap j)
    fun i k↦star_dotProduct_gram_mulVec (u _∘x) (m _ i) _▸w ι j _ (b ..) _ (b ..)
  simp [gram,← by simpa [normDet_comp_of_finrank_eq,gram, *] using (u · ∘ₗ (PiLp.basisFun 2 ..).constr ℂ x |>.normDet_sq_eq_det_gram ⟨.neg _⟩),← (γ ι).conj_mul'] at *;grw [← j.comp_apply,← a,← a] at *;simp [j,Z,field,mul_pow,Real.exp_neg,← Real.exp_nsmul] at *;bound
end
section
open Pi Subgroup Classical ENNReal Finset Fintype Matrix MeasureTheory IntegralPlace
namespace Filling
variable {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} [S.IsAdmissible] {T T₀ : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)] {F} [h : S.IsFillingLevel T F] (Sg : Finset (S.chosenPlaces 0))
omit [S.IsAdmissible] in
lemma qb (k : T⊆univ.biUnion fun p : Σ i,S.chosenPlaces i↦{p.2.1,star p.2.1}) : 2≤ENNReal.ofReal (S.b ^ 9)∧volume (P.R \ P.intUnits)≤(.ofReal (S.b ^ 9))⁻¹ := by
  have b:=S.thousand_le_b
  refine ⟨by grw [← b];bound,.trans' ?_ (measure_mono_ae (t := ⋃ w,{x | (MulEquiv.piUnits.symm (mulSingle w (uniformizer _)) : (LocProd T)ˣ)⁻¹.1 * x∈R}) (P.ae_isUnit.mono fun x ⟨y,u⟩ ⟨a,n⟩↦by_contra (n ⟨a,y,mem_O_locProd.2 fun j↦by_contra fun _↦· ⟨_,⟨j,rfl⟩,
    mem_O_locProd.2 fun i↦by obtain rfl | _:=(eq_or_ne i j) <;> simp_all [mem_O_locProd,v_uniformizer_inv_mul_le_one_iff, -map_mul,one_lt_inv_iff₀]⟩,u⟩)))⟩
  grw [measure_iUnion_fintype_le,sum_le_card_nsmul _ _ (.ofReal (S.b ^ 10)⁻¹) fun w _↦?_,card_univ,card_coe,k,card_biUnion_le_card_mul _ _ 2 (by grind),← ofReal_nsmul,← ofReal_inv_of_pos (by bound)];gcongr;simp [S.card_chosenPlaces,field];bound [S.f_le_b]
  rw [volume_setOf_mul_mem,md_eq_inv_genIndex,genIndex_eq_inv_prod_norm,Fintype.prod_eq_single w] <;> simp +contextual [norm_locField_eq_q_zpow, -FinPlace.q_bounds]
  cases' mem_biUnion.1 (k w.2) with p;grw [S.le_levelPrime p.1];grind [chosenPlaces_q,q_star]
lemma IsFillingLevel.qc (o : Option Sg) d (hT : ↑S.gIdele⁻¹ ∈ integralOff T₀) (f : ∀ w∈o,∀ j,j∈T↔j∈T₀∧(j=w∨star j=w)) : ∃ Z : F.IntermediateGroup,
  (∀ k,S.reduction k∈S.fixingSet Sg d→S.toPlaces T k∈Z.1)∧let K := unitaryLevel R 1 _
  F.jw Z * F.groupMeasure K * o.elim 1 (fun _↦.ofReal (S.b ^ (6 * 𝔰.k))) ≤
    F.jw K * F.groupMeasure Z:=by
  let p := (S.toPlaces T).comp S.latStabilizer.subtype
  have r : p.range=unitaryLevel R 1 _ :=
    ext (qp · |>.elim (by simp [p,qr (T:=T)];aesop))
  obtain _ | ⟨w,m⟩:=o
  use ⟨_,ju,le_rfl⟩;simp [← r,p]
  obtain ⟨c,o,B⟩:=S.pow_chain,S.one_le_b,S.qb (by aesop_cat : T⊆_)
  let H := (vectorFixer w (d w)).comap S.reduction
  have z r:=by simpa [-reduceAt_eq_zero,← mul_smul_comm,idem_mul_mem_Ô,reduceAboveG] using ((S.inv_gIdele_smul_mem_iff (⟨_,idem_mem_Ô {w.1}⟩ * r)).1 · (⟨0,w⟩,false))
  have q : F.congGroup.comap p≤H :=
    fun k e↦by simp [H,vectorFixer,show S.reduction k .. = 1 from intGL.map_eq_one.2 fun i j ↦
    z _ (by simpa [h.g_eq,apply_ite,ite_apply] using! e.2 i j ⟨w,by_contra fun _↦by simpa [Units.smul_def,(mem_integralOff _).1 hT w (by aesop)] using z 1⟩ ⟨⟩)]
  let Z : F.IntermediateGroup := ⟨H.map p,by grw [← q,map_comap_eq_self (r▸ju)],r▸H.map_le_range _⟩
  use Z,(⟨·,·.1 w m,rfl⟩)
  intro K
  nth_grw 1 [Option.elim,pow_le_pow_right₀ o (?_ : _≤9 * _),pow_mul,ofReal_pow (by bound),h.zc Z (𝔰.k - 10 ^ 10 * 𝔰.n ^ 4) (by omega),B.2,h.z7 B,mul_right_comm,mul_assoc _ (_ + _),(?_ : (_ + _) * _≤F.groupMeasure K),Level.jw,← setLIntegral_le_lintegral,h.z2 ⟨K,ju,le_rfl⟩]
  ring;rfl
  grw [← ENNReal.mul_le_mul_iff_left two_ne_zero (by simp),mul_two (F.groupMeasure K),B.1,mul_assoc,← pow_succ,add_mul,mul_comm,(?_ : _ * _≤F.groupMeasure K),mul_right_comm,← mul_pow,ENNReal.inv_mul_le_one,one_pow,one_mul]
  grw [← relIndex_mul_measure_inf unitaryLevel_open_compact.2 Z.isOpen,inf_of_le_left Z.2.2,← (r▸index_comap _ p :),comap_map_eq_self (q.trans' (p.ker_le_comap _)),index_comap_of_surjective _ IsAdmissible.reduction_surjective,vectorFixer,index_comap_of_surjective _ fun g↦⟨mulSingle 0 (mulSingle w ((S.idOrInvAdjoint (d w).1).symm g)),by simp⟩,index_stabilizer_GL_vector (by simpa using (inclMatrix_mulVecLin_injective ⟨_,besselFrame_injective⟩ _).ne (d w).2.2),card_resField_eq_levelPrime,Nat.le_succ 9,le_levelPrime];gcongr
  exact_mod_cast
    (pow_lt_pow_right₀ (S.levelPrime_prime 0).1.one_lt (by simp;clear * - c;lia)).le_pred
  omega
lemma IsFillingLevel.qd [WeilData E] d [hT : Fact (↑S.gIdele⁻¹ ∈ integralOff T)] : ∃ Z : F.IntermediateGroup,
  (∀ k,S.reduction k∈S.fixingSet Sg d→S.toPlaces T k∈Z.1)∧let K := unitaryLevel R 1 _
  F.jw Z * F.groupMeasure K * .ofReal (S.b ^ (6 * 𝔰.k)) ^ #Sg ≤
    F.jw K * F.groupMeasure Z:=by
  choose f hf using show ∀ w,∃ o,∀ s : Sg,o=some s↔w=s.1.1∨star w=s by
    simp [Option.exists];grind [star_notMem_chosenPlaces]
  let T' i := {w∈T | f w=i};have _ i : (T' i).StarStable :=
    ⟨by simp +contextual [T',fT.1,hf,or_comm, @Option.ext_iff _ _ i]⟩
  let e i : LocProd T →+* LocProd (T' i) := .pi fun w↦evalRingHom _ (⟨w,by grind⟩ : T)
  have A {p : T→Prop} : (∀ w,p w)↔∀ i (w : T' i),p ⟨w,by grind⟩:=by aesop
  choose P' F' h' using (S.qs <| T' ·)
  choose Z b c using fun i↦(h' i).qc Sg i d hT.1 (by aesop)
  let φ := MonoidHom.pi fun i↦U.map (e i) (by tauto) (S.map_splitGram_latMiddle _)
  have ψ x : S.qe T x=∏ i,S.qe _ (e i x):=by
    with_unfolding_all refine
      (congrArg S.selfDualChar ?_).trans (map_sum S.selfDualChar.toAddMonoidHom ..)
    ext1 w;erw [map_sum (evalAt w)];show dite .. = ∑ i,dite ..;split <;> simp [T',e, *]
  have su : (⇑φ).Surjective:=fun y↦by
    let M := of fun a b (w : T)↦(y (f w)).1.1 a b ⟨w,by simp [T']⟩
    have k i : M.map (e i)=(y i).1.1:=by ext a b ⟨w,k⟩;cases (mem_filter.1 k).2;rfl
    refine ⟨U.of IsHermUnit.isUnit M (funext₃ fun a b↦A.2 fun i w↦?_),by ext : 3;apply k⟩
    simpa [← k,← S.map_splitGram_latMiddle (e i),← map_conjTranspose_mul_mul (e i) (by tauto)] using! congr($((y i).2) a b w)
  have em:=(continuous_pi (f := φ) fun i↦by
    simpa [φ] using! U.continuous_map (continuous_precomp' _)).measurableEmbedding
    fun x y k↦by ext : 3;exact funext (A.2 fun i w↦congr(($k i).1.1 _ _ w))
  let Q Z := (Subgroup.pi .univ Z).comap φ
  have K u : unitaryLevel R u _=Q fun i↦unitaryLevel R (u.map (e i)) _:=by
    ext;simp [Q,unitaryLevel,Subgroup.mem_pi,mem_intGL,IsIntMatrix,mem_O_locProd,↓A,Units.smul_def,forall_and,ite_apply, -coe_units_inv, -Sum.forall,↓@forall_comm (Option _)]
    rfl
  have B x : x∈besselU↔∀ i, φ x i∈besselU:=by simp [mem_besselU, φ,U.map,funext_iff,↓A,e,ite_apply, @forall_comm (Option _), -Sum.forall]
  have w a x : phase a x=∏ i,phase (a.map (e i)) (φ x i):=by
    by_contra! n;obtain ⟨u,hu,k⟩:=(n.ne_or_ne 0).elim jp
      fun k↦by simpa [*,Q,Subgroup.mem_pi,forall_and,↓skolem,su.exists] using!
      (jp <| prod_ne_zero_iff.1 k · (by simp))
    simp [phase_eq hu k,h.psi_eq,(h' _).psi_eq, ψ,simpleRootSum, φ,U.map, -Units.val_inv_eq_inv_val,↓fun i↦phase_eq (y := φ x i) ((B u).1 hu i) (by simpa using! (K _).le k i ⟨⟩)] at n
  have _ i:=(h' i).isHaarMeasure_groupMeasure.sigmaFinite
  obtain ⟨t,ht⟩:=exists_eq_smul_haar (.pi (F' · |>.groupMeasure)) ⟨su.forall.2 fun g↦((em.2.measurePreserving F.groupMeasure).of_semiconj (measurePreserving_mul_right _ g) (map_mul _ · g) (by fun_prop)).2⟩
  have H Z : F.jw (Q Z)=‖t.toReal‖ₑ ^ 2 * t * ∏ i,(F' i).jw (Z i) ∧
      F.groupMeasure (Q Z)=t * ∏ i,(F' i).groupMeasure (Z i):=by
    simp [Q,← em.map_apply,ht,coe_pi,Level.jw,enorm, -prod_option]
    rw [← lintegral_pi_prod _ (by fun_prop),mul_assoc,← smul_eq_mul t,← lintegral_smul_measure,← ht,em.lintegral_map,← lintegral_const_mul' _ _ (by simp)]
    norm_cast
    simp_rw [prod_pow,← mul_pow,← nnnorm_prod,← nnnorm_smul,← integral_fintype_prod_eq_prod,← integral_smul_measure,← Measure.restrict_pi_pi,← Measure.restrict_smul,← ht]
    simp [em.setIntegral_map,w,g_eq];rfl
  use ⟨Q (Z ·), ?_⟩ <;> simp only [K,map_one,H,mul_mul_mul_comm _ _ t,← prod_mul_distrib]
  use fun k j i _↦b i k j,by grw [← prod_le_prod fun i _↦c i];simp [mul_assoc]
  constructor <;> intro _ k i <;> cases (Z i).2 <;> simp only [Level.congGroup,g_eq] at * <;> tauto
end Filling
end
section
seal Finset.univ Finset.sum Finset.prod
open Complex ENNReal Filter Finset Matrix MeasureTheory NNReal OpenAddSubgroup IntegralPlace Topology IsStdLevel
lemma Filling.q7 {A n : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype n] {G H ι} {p : ι → _} {f : _ → ℝ≥0∞} {s : Finset ι} {c : ι → ℝ≥0} (hf : ∀ z∈s,∀ᶠ x in 𝓝 (p z),∀ k∈H,∀ y,k.1.1 *ᵥ y=x→c z≤f y) (i : H≤(intGL n P.R).subgroupOf G) : ∃ Φ : _ → ℝ≥0,HasCompactSupport Φ ∧ (∀ᶠ v in 𝓝 0,∀ x, Φ (x + v) = Φ x)∧(∀ k∈H,∀ x, Φ (k.1.1 *ᵥ x) = Φ x)∧(∀ x, Φ x≤f x)∧∀ z∈s,c z ≤ Φ (p z):=by
  obtain ⟨_,e,u,rfl⟩:=mem_closure_iff_nhds.1 (Measure.dense_of_ae P.ae_isUnit 0) _
    (s.eventually_all.2 fun z k↦P.intVectors_open_compact_vol.2.1.eventually_forall_mem (fun b r↦(_ + b•r,b•(p z + b•r))) _ fun _ _↦prod_mem_nhds (by simpa using! hf z k) (P.intVectors_open_compact_vol.1.mem_nhds (by simp)))
  replace e z k x:=e z k (u⁻¹ • (x - p z));have M (k : H) (b : Aˣ) x:=k.1.1.1.mulVec_smul b x▸mulVec_mem_intVectors_iff (i k.2);simp [← Units.smul_def] at e M
  use fun x↦{z∈s | ∃ k : H,u⁻¹ • (k.1.1.1 *ᵥ x - p z)∈intVectors R n}.sup c,.intro
    (P.intVectors_open_compact_vol.2.1.smul u⁻¹) ?_,
    ((P.intVectors_open_compact_vol.1.preimage (continuous_const_smul u⁻¹)).eventually_mem ?_).mono
    (by simp +contextual [add_sub_right_comm,add_mem_cancel_right,M]),fun k l x↦sup_congr
    (s.filter_congr fun z _↦(Equiv.mulRight ⟨k,l⟩).exists_congr ?_) ?_, ?_,fun z k↦le_sup
    (s.mem_filter.2 ⟨k,1, ?_⟩) <;> simp_all [Set.mem_inv_smul_set_iff] <;> grind
namespace Filling.IsFillingLevel
variable {E 𝔰} [Field E] [CMType E] [WeilData E] {S : Filling E 𝔰} [ok : S.IsAdmissible] {T : Finset _} [T.StarStable] [Fact (↑S.gIdele⁻¹ ∈ integralOff T)] (hT : S.latBasis∈intGL _ (integralOff T)∧(↑S.N)⁻¹ ∈ ratIntegralOff T) [P : IntegralPlace (LocProd T)] {F} (hF : S.IsFillingLevel T F) {π : Side} {Z : F.IntermediateGroup}
include hT hF
lemma q8 {f s} {t : E} (ht : ∀ v,S.N ^ 2 < ‖Φ v t‖ ^ 2) {c :
  _ → ℝ≥0} : let x (z : S.Classes × _) := z.1.out⁻¹.1.1 *ᵥ (↑)∘z.2
  (∀ z∈s,(S.N * star z.2 ⬝ᵥ z.2=t * star t - S.N ^ 2∧∀ i,x z i∈integralOff T)∧∀ᶠ e in 𝓝 (evalPlaces T∘ji S.piBar t (x z)),∀ k∈besselH ⊓ F.congGroup,∀ y,k *ᵥ y=e→↑(c z)≤f y)→∀ᶠ L in (𝓝 0).smallSets,IsClopen L→(∑ z∈s,↑(c z)) * volume L ≤ .ofReal
    ((1 + S.b⁻¹ ^ 6) * Fintype.card S.Classes * S.siegelConst * (∏ v,(‖Φ v t‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) * ∫⁻ e,
    {e | ((S.latMiddle _).splitGram *ᵥ e) (𝔰.besselFrame 𝔰.top) - ratToPlaces T t∈L}.indicator f e
    ∂F.floorQuadric 𝔰.top:=fun hs↦if y0 : ∑ z∈s,(c z : ℝ≥0∞)=0 then by simp [y0] else by
  obtain ⟨N0,⟨_,d⟩⟩:=S.N_prime.pos,S.ϱ_le_k.dest
  set β := (t * star t - S.N ^ 2) / S.N
  set t':=evalPlaces T t
  let π : (LocProd T)ˣ := S.piBar.map (evalPlaces T)
  have sβ : star β = β := by simp [β,field]
  obtain ⟨u,hN : π * star π.1=_⟩:=P.qw (x := .mk0 _ (by simp)) ⟨by simp,
    hT.2⟩,by simpa using! congr(evalPlaces T $S.piBar_mul_star)
  have p v : 0 < (Φ v β).re:=by simpa [β,mul_conj',sq,N0] using ht v
  obtain ⟨Ψ,cf,uf,hk,h2,hy⟩:=q7 (hs · · |>.2) fun _↦(·.2.1)
  let n := LocallyConstant.indicator ⟨(Ψ <| ji π t' <| evalPlaces T∘·),.comp_continuous (isLocallyConstant_of_eventually_add uf) (by fun_prop)⟩ (isClopen ⟨(intVectors ..).toAddSubgroup,isOpen_intVectors (isOpen_integralOff T)⟩)
  have cs : HasCompactSupport n := .of_support_subset_isCompact ((cf.image (f:=fun e i↦adeleOfLocal T (((besselLatticeBasis 𝔰 π).1 *ᵥ e) (𝔰.indexX₀ i))) (by fun_prop)).add stdLattice.isCompact_stdLattice)
    (Set.support_indicator.trans_le fun x ⟨a,h⟩↦⟨_,⟨_,subset_closure h,rfl⟩,_,(by simpa [ji,sub_adeleOfLocal_mem_iff] using a ·),add_sub_cancel ..⟩)
  obtain ⟨sm,key⟩:=classSum_norm_eq (by lia) S.columnLevel n (fun k l x ↦
    if_congr (mulVec_mem_intVectors_iff (by clear * - l;grind [mem_intGL,mem_Ô_iff T,show k.1∈intGL _ _ from S.hasFiniteType_columnLevel.1 l])) (.trans
    (congrArg Ψ (by rw [qv,qv];ext1;erw [← RingHom.map_mulVec];simp [ji,inclHFin,toLatBasis,← mulVec_mulVec,mulVec_mulVec _ (besselLatticeBasis ..).1,toBesselH,fromBlocks_mulVec])) (hk (S.toPlaces T _) ⟨(inclHFin_mem_besselH k).map_mem_unitriangularOn _,(hF.mem_principalLevel_iff.1 (ok.columnLevel_eq.le l)).2⟩ _)) rfl) cs sβ p
  generalize eC : ofReal (_ * _)=C at key
  let r := ENNReal.ofReal ((1 + S.b⁻¹ ^ 6) / (1 + 2⁻¹ ^ 𝔰.n))
  replace hy:=(ENNReal.mul_lt_mul_left y0 (by simp) (by
    grw [one_lt_ofReal,one_lt_div (by positivity),← pow_six_le,pow_succ]
    bound)).trans_le (mul_le_mul_right (congr(‖$key‖ₑ).le.trans' (by
    simp_rw [classSum_eq_sum,← NNReal.coe_sum,enorm_eq_nnnorm,nnnorm_real,nnnorm_eq,coe_finsetSum,ENNReal.coe_tsum (sm _)]
    grw [← ENNReal.tsum_prod.trans (tsum_fintype _),← ENNReal.sum_le_tsum s]
    gcongr with z k
    grw [ite_eq_left (by simp [β,← (hs z k).1.1]),hy z k,← qv]
    exact (ite_eq_left (hs z k).1.2).ge)) r)
  obtain ⟨nz,K0 : r * ‖C‖ₑ * (.ofReal (1 + 2⁻¹ ^ 𝔰.n) * volÔ E ^ 𝔰.k) * P.md π ≠ ∞⟩:=by
    simpa using hy.ne_zero,by simp [r,mul_eq_top]
  have iF:=Integrable.of_integral_ne_zero nz.2.2
  let b τ := (π * star π)⁻¹.1 * τ * star τ - S.N - ratToPlaces T β
  obtain ⟨_,_,ha,_,hb,h⟩:=(isLocallyConstant_of_eventually_add uf).continuous,
    eventually_prod_iff.1
    (nhds_prod_eq.ge ((ENNReal.Tendsto.const_mul ((tendsto_integral_filter_of_dominated_convergence (l := 𝓝 (0,t')) _ (.of_forall fun p↦(iF.1.mul (Continuous.aestronglyMeasurable (.subtype_val (f:=fun z : selfAdjoint _↦ψf E ((2⁻¹ : E) * (z.1 * -adeleOfLocal T (b p.2)))) (by fun_prop))
    )).indicator (isOpen_codifferent E p.1).measurableSet) (by simp [(norm_indicator_le_norm_self .. ).trans_eq]) iF.norm (.of_forall fun z↦.congr' (((isOpen_Ô.preimage (by fun_prop) ).eventually_mem (by simp)).mono fun p l↦.symm (ite_eq_left fun _↦ψf_of_mem∘mul_mem l))
    (Continuous.tendsto' (.const_mul (.subtype_val (by fun_prop)) _) _ _ (by simp [show b t'=0 by
      rw [sub_eq_zero,sub_eq_iff_eq_add,mul_assoc,Units.inv_mul_eq_iff_eq_mul]
      simpa [t',hN] using congrArg (ratToPlaces T) (by field :
      t * star t=S.N * (β + S.N))])))).const_mul _).enorm (by simp [r])).eventually_const_lt hy))
  simp only [integral_indicator (isOpen_codifferent ..).measurableSet,Pi.mul_apply,← integral_mul_const,← Circle.coe_mul,← AddChar.map_add_eq_mul,← mul_add,sub_add,sub_neg_eq_add,one_mul] at h
  filter_upwards [eventually_smallSets_forall.2 (.and ((map_add_left_nhds_zero t').le hb) ((by
    fun_prop : Continuous (ji π · 0)).tendsto' 0 0 (by simp [ji,← Pi.zero_def]) uf))] with L hL oL
  refine (le_mul_of_forall_lt (by simp [add_pos,nz]) (.inl K0) fun a k c hc↦?_).trans (mul_le_mul' (ofReal_toReal K0▸ofReal_le_ofReal (le_of_eq ?_)) (lintegral_mono fun e↦(ENNReal.coe_indicator ..).trans_le (Set.indicator_le_indicator (h2 e))))
  · obtain ⟨V,hV,d⟩:=eventually_smallSets.1 (F.jk hN ((oL.preimage (by fun_prop)).continuous_indicator ‹_›) (cf.mono (by simp)) hc)
    choose M M0 ha hV using mem_nhds_zero_finAdele_iff.1 (ha.and ((continuous_evalPlaces T).tendsto 0 hV))
    obtain ⟨⟨u,i⟩,o,z⟩:=(isUnit_natCast_finAdele (E:=E) M0).exists_right_inv,
      Fact.mk ((isCompact_codifferent E (isUnit_natCast_finAdele M0)).measure_lt_top (μ := volume)),
      idealZeta_intAdeles_pow_le 𝔰.ϱ.succ (S.degree_le.trans' (Nat.mul_le_mul_right _ 𝔰.ϱ.succ_pos))
    obtain ⟨v,_,hv,sp⟩:=P.mass_near_quadric_off_places_le i (sβ ▸ star_algebraMap_finAdele β :)
      (le_two_of_pow_le_ofReal z) (by omega : _ ≤ 𝔰.k)
    grw [← k.le,← setLIntegral_const,setLIntegral_mono' oL.2.measurableSet fun τ l↦?_,setLIntegral_le_lintegral,lintegral_const_mul',(lintegral_add_left_eq_self _ t').trans_le
      (d _ (fun a l↦by simpa [↓adeleOfLocal_evalPlaces_mul,← mul_assoc,i] using hV (adeleOfLocal T (evalPlaces T u * a)) (by simpa [↓mem_Ô_iff T,↓adeleOfLocal_mem_integralOff])) (measurable_const_mul (evalPlaces T u) SemilocalField.isCompact_O.measurableSet))]
    rotate_right
    grw [(h (ha 1 (by simp)) (hL _ l).1).le,enorm_mul,mul_one]
    erw [enorm_integral_codifferent i ?_
      (by simpa using isFiniteMeasure_withDensity_ofReal ((n.2.comp toReal).continuous.integrable_of_hasCompactSupport (cs.comp_left rfl)).2),
      withDensity_apply',funext (ENNReal.coe_indicator _ _),sp _ (Ψ <| ji π t' ·) (by
      fun_prop),add_sub_cancel,lintegral_congr fun y↦?_]
    · simp_rw [← mul_assoc];rfl
    · rw [← (hL _ l).2,Set.indicator_of_mem (by simpa [t',jj hN]),ji,ji,← mulVec_add];congr;simp [funext_iff,mul_add]
    simp [b,sβ,← adeleOfLocal_star, -Units.val_inv_eq_inv_val,← Units.coe_star_inv];ring_nf
    grw [← z,pow_one,← hv];simp;ring_nf;rfl
    simp [r,mul_eq_top,o.1.ne, *]
  simp [← hN,← sq,← ENNReal.rpow_natCast_mul] at u
  clear * - p eC d N0 u
  simp (disch:=positivity) [r,u,← eC,classSum_eq_sum,abs_of_nonneg,abs_of_pos (p _)]
  simp [siegelConst, β,mul_conj',sq,div_pow,← d,mul_add,prod_pow]
  field
lemma q9 {T₀ : Finset _} {j} [Fintype j] {c c' : j→_} {γ : j→S.G E} {n : j→_} {t : Eˣ} (h : (fun i↦(c i,c' i,S.reduction (n i), γ i)).Injective) (hu : ∀ i, γ i∈GT 𝔰.ϱ) (hs : ∀ i,S.frameProducts (γ i) 𝔰.top 𝔰.top=t) (ht : ∀ v,S.N ^ 2 < ‖Φ v t.1‖ ^ 2) (hn : ∀ i,S.toPlaces T (n i)∈Z.1) (ho : ∀ i,S.IsIntegralOff T (S.termPosition (c i) (c' i) (γ i)))
  (i : j) {R : Matrix _ _ ℂ} {ρ : _ → ℝ} {r} : let a (p : Fin 𝔰.ϱ → T₀) := padTuple (p · |>.1) t
  let ω p := Units.map (ratToPlaces T)∘a p
  let y i := r ^ 2 * ‖∑ p,
    S.qk T (c i) (S.reduction (n i)) (c' i) (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2
  let G := (∏ v,(‖Φ v t.1‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)
  (∀ i,R = .gram ℂ fun p↦ρ p•besselCorrelation volume (.toLp 2 <| S.besselFn ·) (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ i)))→(∀ p, ρ p * (F.headDensity 𝔰.ϱ (ω p) 1).toReal=r * √G) →
    (∀ i p,S.IsIntegralOff T (S.termPosition (c i) (c' i) (weylElem 𝔰.ϱ (a p) * γ i)))→∀ᶠ L in
    (𝓝 0).smallSets,IsOpen L∧IsCompact L∧0∈L→∑ i,y i≤(1 + S.b⁻¹ ^ 6) * S.packetConst *
    (∑ p,∑ q,R p q * (F.ze L Z (ω p) (ω q) / volume.real L / Z.massRatio.toReal)).re:=by
  intro a ω y G hR w hw
  choose A hA using fun i (b : Z.Cosets)↦Z.jy (mul_mem (inv_mem (hn i)) b.out.2)
  choose hL hv hN _ using fun i↦hs i▸qt (hu i) (c i) (c' i)
  obtain ⟨D,_,eD,f⟩ : ∃ D > 0,S.packetConst=D * _ * _∧Z.massRatio ≤
    F.measureH F.congGroup * (F.groupMeasure F.congGroup ^ 2 * Fintype.card Z.Cosets) * .ofReal D :=
    ⟨_,S.of_size_bounds (by intros;positivity),rfl,div_le_of_le_mul (by
    grw [measure_mono (t := ⋃ c : Z.Cosets,(· * c.out.1⁻¹) ⁻¹' F.congGroup) fun _ h↦(Z.jy h).elim (by simp +contextual),measure_iUnion_fintype_le,← mul_one (F.groupMeasure _),one_le_pow₀ hF.qy.ge,← mul_one (_ * _ ^ 2),hF.box_eq.2.2.1.ge,hF.box_eq.2.1,← hF.qz (B:=besselH ..) (F.measureH_spec.1.mono fun z a↦(qp z).imp (by clear * - a;grind)) fun _ h↦F.measureH_spec.2.1 _ (h.map_mem_unitriangularOn _)]
    simp [-Nat.cast_mul,↓j0];push_cast;ring_nf;rfl)⟩
  have : 0 < G:=by simp [G, *,prod_pos]
  let g i := (c i,fun j↦(γ i).1.1 (𝔰.indexX₀ j) 𝔰.z)
  refine (hF.q8 hT ht (s:=univ.image g) (c:=fun z↦(.ofReal G * (Z.massRatio / .ofReal D) * ∑ k with g k=z,.ofReal (y k)).toNNReal) (forall_mem_image.2 fun k₀ _↦⟨⟨hN _,((mulVec_mem_intVectors_iff (inv_mem hT.1)).1 (Set.mem_of_eq_of_mem (hv _).symm (by simpa [orbitPoint] using (ho k₀).isIntMatrix · _)) <|
    𝔰.indexX₀ ·)⟩, ?_⟩)).mono fun L k ⟨p,q,z⟩↦by
    obtain ⟨⟨⟨o⟩,l⟩⟩:=zi Z ω p (hR i▸posSemidef_gram ..)
      (fun _↦by simp [ω,a,padTuple];rfl),(s20_z1 Z).elim toReal_pos,
      toReal_pos (p.measure_ne_zero volume ⟨_,z⟩) q.measure_ne_top
    replace k:=toReal_mono (by finiteness) ((k ⟨q.isClosed,p⟩).trans (mul_le_mul_right l _))
    simp (disch:=finiteness) only [toReal_sum,toReal_mul,coe_toReal,coe_toNNReal_eq_toReal,toReal_ofReal,toReal_div,siegelConst,← mul_sum] at k
    rw [sum_fiberwise_of_maps_to (by simp),mul_right_comm,← siegelConst] at k
    exact le_of_mul_le_mul_left
      (k.trans_eq (by simp [← mul_div_assoc,← Finset.sum_div,eD,Measure.real];field))
        (by positivity)
  refine zg Z ω Units.isOpen (NormedRing.inverse_continuousAt 1) ⟨⟨k₀,rfl⟩, ⟦1⟧⟩ (n:=fun (i,b)↦(b,A i b)) (fun θ : {k // g k=g k₀} × Z.Cosets↦⟨inv_mem (x:=S.toPlaces T _) (.map_mem_unitriangularOn _ (hL θ.1)), ?_⟩) ?_ |> fun z↦by
    peel z
    grw [← this,coe_toNNReal_le_self,div_le_of_le_mul f,sum_subtype _ mem_filter_univ,Fintype.sum_prod_type,mul_sum,mul_sum]
    congr! 1 with k
    simp only [ω,hR k,star_dotProduct_gram_mulVec, @smul_comm ℂ ℝ,hF.j1 (hu k) (hw ..) ((hA ..).2 rfl),y,smul_smul (ρ _),w,← smul_sum]
    simp (disch:=positivity) [norm_smul,← Complex.ofReal_pow,mul_pow,Measure.real,ofReal_toReal (hF.z0 ju)];ring
  · simp_rw [← θ.1.2,g,← hv];simp [orbitPoint];rfl
  rintro ⟨⟨i,q⟩,b⟩ ⟨⟨k,q'⟩⟩ l e
  obtain ⟨⟨rfl,f⟩,q,e⟩:=by simpa [g,funext_iff] using And.intro e (q.trans q'.symm)
  have x:=unitriGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq (hu i) (hu k)
    (by simpa [funext_iff,Unique.forall_iff,orbitPoint,floorGroup_apply (hu _),e,frameGram,splitGram,mul_apply,middleGram] using (hs k▸hs i :)))
  obtain ⟨z,⟨m⟩⟩:=eq_and_mem_classUnip_of_besselS (mem_unitriGroup_of_mem_floorGroup x)
    (by simpa [termPosition,q,mul_assoc] using
    (hF.mem_principalLevel_iff (x:=_⁻¹ * _).2 ⟨mul_mem (inv_mem (ho i)) (ho k),by simpa⟩))
  simpa using h congr(($q, $z, $((hF.reduction_eq_iff ..).2 (by simpa using div_mem ((hA i b _).2 rfl) ((hA k b _).2 f))), $(inv_mul_eq_one.1 (eq_one_of_mem_floorGroup_inf ⟨x,(unipotentBelow_eq_besselU le_rfl).ge m⟩ (by simp)))))
end Filling.IsFillingLevel
open ComplexOrder Level
lemma Filling.IsFillingLevel.qa {E 𝔰} [Field E] [CMType E] [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset _} [T.StarStable] {P : IntegralPlace (LocProd T)} {F} (hF : S.IsFillingLevel T F) Sg d [Fact (↑S.gIdele⁻¹ ∈ integralOff T)] : ∃ Z,(∀ k,S.reduction k∈S.fixingSet Sg d→S.toPlaces T k∈Z.1)∧∀ L : OpenAddSubgroup (LocProd T),IsCompact L.carrier→SieveSystem unitOrOne (ratToPlaces T S.g⁻¹ * ·⁻¹.1) 𝔰.ϱ (fun j p q↦(if j ≤ 𝔰.ϱ then F.floorForm j p q Z.besselVector 1 else F.ze L Z p q / volume.real L.carrier) / Z.massRatio.toReal) (S.qe T) ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg) (finHeadWeight
  (𝔰.n ^ 6)) (S.qg T):=(hF.qd Sg d).imp fun Z ⟨hm,hk⟩↦by
  obtain ⟨n,_,_, Γ,C⟩:=S.pow_chain,S.k_le_f,S.one_le_b,hF.gauge,s20_z3 Z
  have N {x : ℂ} {D} d h : ‖x / Z.massRatio.toReal‖ ≤ _ :=
    (toReal_mono d (@ENNReal.div_le_of_le_mul' ‖x‖ₑ Z.massRatio D h)).trans' (by simp)
  have Er {j p q ξ ω} hj (k : IsUnit ξ) H : ‖F.floorForm j p q _ ω / _‖ ≤ S.qg T ξ * _ :=
    .trans' (by
    simp (disch:=positivity) [-Nat.cast_mul,md_g,qg,finHeadWeight, -map_prod]
    gcongr _ * ?_ * _
    grw [g_le_b_pow,(by linarith [S.thousand_le_b] : 2≤S.b),pow_add _ 6 3,mul_assoc,pow_mul',← pow_mul,← pow_mul,← pow_succ']
    gcongr;grw [Shape.n,← S.ϱ_le];omega) (N (by simp [denomIndex_ne_zero,mul_eq_top,div_eq_top]) (IsStdLevel.enorm_floorForm_le (ξ := k.unit) Z _ hj (by omega) n.1 H))
  refine hF.psi_eq▸⟨hm,fun L hl↦⟨by simp,fun j p q ξ a↦?_,by
    simp [div_eq_inv_mul,← mul_assoc]
    exact fun a t e↦.smul (α := ℂ) ⟨.ext (by simp [ze,← integral_conj,e]),
      fun x↦by simpa [x.sum_fintype,mul_right_comm] using!
      (zi Z _ L.2 (Matrix.posSemidef_vecMulVec_star_self x) e).1⟩ (by positivity),by simpa [div_div] using! (zj ..).div_const _,
    fun p q↦(N ofReal_ne_top ?_).trans_eq (toReal_ofReal (by positivity)),fun j p q a ↦
    (ite_eq_left a▸Er a · (.inr ⟨j,rfl,rfl,hF.g_eq▸(mul_sub ..).symm⟩))⟩⟩
  split_ifs with b <;> [simp_rw [div_eq_inv_mul] at *;simp_rw [← mul_div_assoc,integral_div]]
  exact (Γ.integral_floorForm_succ C ⟨j,b⟩ _ ξ (hF.lintegral_formMajorant_ne_top Z 0 a (by omega))).rec fun i s↦s.symm▸⟨i,(by simp [·,Pi.one_def]),(Er a · (.inl rfl))⟩
  obtain ⟨rfl,⟨i,e⟩,o⟩:=a.eq_of_not_lt' b,hF.1.zh Z p q ξ,
    L.2.measurableSet
  have ⟨I,s⟩:=integral_skew_product (volume.map_sub_left_eq_self <|
    (S.latMiddle _).frameGram ·⁻¹.1 𝔰.top 𝔰.top) (i.mul_prod (((by fun_prop : ContinuousOn
    (P.ψ <| -ξ * ·) L).integrableOn_compact hl).integrable_indicator o)) (by fun_prop [frameGram])
  refine (fun k↦⟨((I.congr k).div_const _).div_const _,.symm ⟨fun u↦?_, ?_⟩⟩)
    (P.ae_isUnit.mono fun | _,⟨t,rfl⟩ => ?_)
  any_goals simp_rw [← integral_congr_ae k,s,integral_const_mul,integral_mul_const,← e]
  grw [div_right_comm,mul_div_right_comm,norm_div,norm_mul,norm_integral_le_integral_norm,Er a u (by left;rfl)]
  iterate 2 simp +contextual [norm_indicator_eq_indicator_norm,o,Pi.one_def,finHeadWeight,Measure.real,toReal_eq_zero_iff,hl.measure_ne_top,L.2.measure_ne_zero _ ⟨0,L.zero_mem⟩]
  erw [ze,← integral_indicator (o.preimage (by fun_prop [frameGram]))]
  simp [← integral_const_mul,Set.indicator,mul_sub,mul_right_comm _ _ (P.ψ _),← P.ψ.map_add_eq_mul,zd,Level.headDensity,prod_range,ne_of_lt]
  grw [ite_eq_left zero_le,ofReal_div_of_pos (by bound),IntermediateGroup.massRatio,← ENNReal.mul_div_mul_comm,ENNReal.le_div_iff_mul_le (by simp;left;bound),← ENNReal.mul_le_mul_iff_left (P.unitaryLevel_open_compact.1.measure_ne_zero _ ?_) (hF.z0 le_rfl),← mul_assoc,Level.enorm_floorForm_le,Level.headDensity,prod_range_zero,one_mul,lintegral_mul_const_le,(?_ : lintegral .. ≤ F.jw Z),mul_right_comm,ENNReal.ofReal_pow (by bound),← hk.ge,zc ⟨_,P.ju,le_rfl⟩ 0 (by omega),sdiff_le,SemilocalField.volume_O,← hF.box_eq.2.1,add_le_add_left hF.groupMeasure_boxSet_le,← pow_six_le]
  any_goals simp [ENNReal.ofReal_add,pow_succ,add_assoc,← mul_add,inv_two_add_inv_two, -inv_pow,mul_eq_top]
  ring;rfl
  simp [Level.jw,s20_z6,formModulus,descConv.eq_1,weylRatio,← formIntegrandOne_eq Γ C,formIntegrandOne,← sq,mul_pow]
end
section
open Fin Classical ENNReal Matrix MeasureTheory MulAction Set
variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰}
lemma Filling.q0 [StablyUnram E] [S.IsAdmissible] [Side] {T} (hT : S.IsStable T) (h : ∀ γ ∈ T,¬S.CharsAgree γ) c s c' : S.amplitudeSum T c s c'=0:=by
  choose φ _ w _ q using (S.exists_cutoff_classUnip <| stabilizer _ (α := _ ⧸ S.classUnip c') ·);choose a e using @Quotient.mk_out _ (orbitRel (S.classUnip c) (_ ⧸ S.classUnip c'));refine (hasSum_amplitudeSum_change_of_weight hT c s _ (fun γ↦(S.classCutoff c' (S.ratToInf γ)⁻¹ * indicator {x | x=a x•x} 1 γ) • φ γ) fun γ _ y↦?_).1.unique (hasSum_zero.congr_fun fun γ↦(h _ γ.2.1).imp_symm fun n _ a _ b e↦eq_of_inv_mul_eq_one (n.imp_symm fun z↦?_));simp [tsum_classCutoff_eq_one,show ∀ u : S.classUnip c,↑(u * γ)=u•(γ : _ ⧸ S.classUnip c') by tauto];erw [← (Equiv.mulRight (a γ)).tsum_eq,← w (a γ • γ) (S.ratToInf (a γ) * y),tsum_subtype _ fun u : S.classUnip c↦φ _ (S.ratToInf u * _)];simp +contextual [indicator, *,mul_assoc,mul_smul]
  simp [mul_smul,integral_smul,(fun i↦((q γ).integral_orbitMeasure i).symm.trans (integral_quotMeasure_eq_zero_of_twist volume (i ⟨·,·⟩) continuous_besselKernel (by simp [unipotentChar]) z (mul_inv_eq_of_eq_mul e▸besselKernel_besselU_mul a b γ))) fun ⟨_,
    u,h,rfl⟩ y↦by simp [besselKernel,mul_assoc,besselFn_mul_of_mem_classUnip u,← besselFn_mul_of_mem_classUnip ⟨_,QuotientGroup.eq.1 h.symm⟩ (_ * y)]]
lemma Filling.CharsAgree.q1 {γ} (hr : S.CharsAgree γ) (h : S.termDisc γ = 0) : ∃ j,S.HasLevel j γ :=
  have hc a c c' (h : HasCommonFlagVector γ c c' a) :
      c * star c=c' * star c'∧∀ b≥a,HasCommonFlagVector γ c c' b:=by
    induction' a using reverseInduction with a i <;> have ⟨x,y,_⟩:=h
    grind [star_mul_last_eq_of_frameImage_eq]
    have:=exists_mulVec_eq_of_annihilator (frameImage 1) (frameImage γ) (Iio a.succ) (Iio a.succ)
      (cons 0 (init x)) (cons 0 (init y)) fun l h k ↦
      (algebraMap E (𝔸f E)).injective (eq_of_ψf (denseRange_algebraMap_finAdele.eq fun t↦?_))
    grind [i (this.imp (by simp [forall_fin_succ,init];grind))]
    have ⟨v,Z⟩:=exists_star_vecMul_eq S.ratGram (l ᵥ* γ)
    let r := S.g * S.ϖ * -t
    obtain ⟨⟨u,a,_⟩,w,b,_⟩:=exists_mem_besselU_eq_eichlerMap _ x r (by simp [star_mulVec,← U.form_mul_inv_eq,← Z▸vecMul_vecMul ..] : star (γ *ᵥ v) ᵥ* S.ratGram =
      l ᵥ* 1) (by grind) h,exists_mem_besselU_eq_eichlerMap _ y r Z (by grind) k
    simpa [*,r,unipotentChar,gIdele,selfDualChar,ratToFin,simpleRootSum_adelicToFin,← map_mul,
      mul_assoc,Circle.ext_iff, -vecMul_one] using! hr u a w b (by ext : 2;simp [*,ext_iff_mulVec,U.form_mulVec_mulVec,← mulVec_mulVec,frameImage_mulVec γ.1.1,eichlerMap_mulVec,mulVec_sub])
  (exists_minimal_of_wellFoundedLT (IsNormalForm ·.1 γ) ⟨⊤,1,by simp;lia⟩).imp
  fun j m↦have M x y (e : frameImage 1 *ᵥ x=frameImage γ.1.1 *ᵥ y) (z : ∀ i,j ≤ i.castSucc→y i=0) : ∀ a,x a=0∧y a=0 :=
    WellFoundedGT.fix fun a _↦by grind [IsNormalForm,Minimal,star_one,star_eq_zero,fun s↦hc a (s⁻¹ * x a) (s⁻¹ * y a) ⟨s⁻¹ • x,s⁻¹ • y,by aesop⟩]
  (fun d↦⟨m.1,d,iff_of_false ((exists_mulVec_eq_single_det (S.frameProducts γ)).elim fun y a e ↦
    d (last_le_iff.1 e▸(by grind [frameDisc,star_eq_zero,(norm_sq_middle_part_eq a.1 rfl).2 _,by simpa using congr(‖Φ ofNonempty $(sub_eq_zero.1 h)‖)] : (S.frameProducts γ).det=0)))
    (· h)⟩) ((exists_mulVec_eq_zero_iff.2∘det_paddedLeading.trans).mt fun ⟨y,Z⟩↦by
  simp [funext_iff,paddedLeading,(of _).mulVec_apply_eq_sum,← mulVec_apply_eq_sum] at Z
  grind [sq_nonneg,by simpa using (norm_sq_middle_part_eq (D:=0) (.trans (dotProduct_eq_zero (S.frameProducts γ *ᵥ y) fun w↦(exists_frameImage_eq_of_isNormalForm m.1.inv (star w)).elim
    fun _ ⟨_,_,e⟩↦by grind [dotProduct,Pi.star_apply,star_star,Finset.sum_eq_zero,by
    simpa [star_mulVec_dotProduct] using congr(star $(frameProducts_mulVec_of_frameImage_eq e) ⬝ᵥ y)]) (by simp)) rfl).2 ofNonempty])
attribute [-instance] IdemSemiring.toCanonicallyOrderedAdd IdemSemiring.toMulLeftMono IdemSemiring.toMulRightMono
attribute [local instance high] Side.cut
attribute [local irreducible] Filling.classGauge Filling.mainEnergy Filling.saturationIndex Filling.termPosition Filling.frameValueIndex link
variable [StablyUnram E]
variable [ok : S.IsAdmissible] {C w : ℝ} (hC : 0≤C) {Ω : Set _} {T X} (hT : S.IsStable T) (h₁ : (∃ γ ∈ T,∃ c c',∃ s ∈ Ω, γ ∈ S.termsOver c s c'∧IsNormalForm 0 γ)→S.tailScale ^ 20 * S.besselEnergy≤C) (hx : X≠0) (hq : ∀ s ∈ Ω,S.FixesNormAtLeast s X) (hw : 0≤w) (hz : S.besselEnergy≤C)
include hC hT h₁ hx hq hw hz
lemma Filling.q2 j R (hc : ∀ γ ∈ T,S.HasLevel j γ) (h₂ : 𝔰.ϱ < j→(∃ Λ, Λ ∉ R)→S.tailScale ^ 12 / X ^ 𝔰.k * S.mainEnergy≤C) (h : linkEnergy T Ω R ≤ .ofReal (w * S.unipCovolume ^ 2)) : energy
  (S.amplitudeSum T) Ω ≤ w + C / S.b ^ 30 / 4 ^ j.rev.1:=S.of_size_bounds fun g t u z v y↦by
  intros;simp_rw [energy,← Finset.sum_div];grw [div_le_iff₀,← ofReal_le_ofReal_iff,add_mul,ofReal_add,← h,← (?_ : ∑ c,∑ c',∑' (a) (b),.ofReal (C / S.tailScale ^ 3 * S.unipCovolume ^ 2) * (S.pairWeight j c c' b a + S.pairWeight j c c' a b) ≤ .ofReal _),linkEnergy] <;> try positivity
  simp (disch:=intros;positivity) [← Finset.sum_subtype_eq_sum_filter,ofReal_sum_of_nonneg]
  have m {α β : Type} (f : α → ℝ≥0∞) g : tsum f * tsum g=∑' p : α × β,f p.1 * g p.2:=by simp
  have B Λ := enorm_amplitudeSum_le_classSize (T:=T ∩ link ⁻¹' {Λ}) (by grind [IsStable,link_besselU_mul]) (hc · ·.1)
  simp_rw [amplitudeSum,← ((summable_amplitude T ..).hasSum.tsum_fiberwise (link∘(·.1))).tsum_eq]
  grw [enorm_tsum_le_tsum_enorm];simp_rw [← tsum_image _ injOn_subtype_val,tsum_subtype (_ '' _),preimage_comp,Subtype.image_preimage_coe,T.inter_right_comm _ (_ ⁻¹' _),← tsum_subtype,← amplitudeSum.eq_1,sq,m,← ENNReal.summable.tsum_add_tsum_compl (s:=Function.diag '' R) (by simp),Finset.sum_add_distrib]
  gcongr;exact ((Equiv.Set.image _ R fun _ _↦by simp).tsum_eq _).ge
  grw [ENNReal.sum_le_tsum,B,B];simp_rw [m,← ENNReal.tsum_mul_left,← ENNReal.tsum_sigma]
  refine (ENNReal.tsum_le_tsum fun ⟨s, π,⟨γ,⟨⟨m,e⟩,a⟩,n⟩, γ',⟨⟨m',e'⟩,a'⟩,_⟩↦?_).trans
    (tsum_comp_le_tsum_of_injective (f:=fun ⟨_,_,a,b⟩↦⟨a,b⟩) ?_ _);
  (iterate 2 rintro ⟨⟨⟩,⟨⟨⟩⟩,⟨_,⟨⟨⟨_,⟨⟩⟩,⟨⟩,⟨⟩,⟨⟩⟩⟩⟩,_,⟨⟨⟨_,⟨⟩⟩⟩⟩⟩);rintro ⟨⟩;rfl;dsimp
  have k:=hc _ m;apply hc at m';specialize hq _ s.2;obtain ⟨⟨i,r,l,L⟩,⟨-,⟨d⟩⟩,⟨-,⟨d'⟩⟩,⟨⟨_,p⟩, -⟩,⟨⟨-,q⟩⟩⟩:=s20_j9 n.1 a k hq a' m',
    one_le_xRowsIndex_and_saturationIndex a k,one_le_xRowsIndex_and_saturationIndex a' m',
    s20_j8 n.1 a k hq γ',s20_j8 n.1 a' m' hq γ
  unfold pairWeight termWeight invPowWeight pairInvariant commonLink classSize countWeight at *;set
    D:=ite (𝔰.ϱ < j) S.mainEnergy _
  have H : S.tailScale ^ 4 * D * (2 * S.tailScale ^ 2) ^ (j - 𝔰.ϱ) * S.codimFactor ^ i / ite
    (𝔰.ϱ < j∧i=0) X 1 ^ 𝔰.k≤C / S.tailScale ^ 3
  · clear * - t u v y h₂ h₁ l k m a e e' hz
    induction' j using lastCases with j <;> simp [Nat.sub_eq_zero_of_le,D,is_le,← not_le]
    · cases i;· grw [← h₂ (by simp) ⟨π.1.1,by grind⟩,t];simp [field];bound
      grw [pow_le_of_le_one _ codimFactor_le_one,← hz,← ok.mainEnergy_le,t] <;> simp [field] <;> bound
    grw [codimFactor_le_one];rcases j with ⟨⟨⟩⟩
    · grw [← h₁ ⟨_,m,_,_,_,s.2,a,k.1⟩];simp [field]
    grw [← hz,← le_self_pow₀] <;> simp [field] <;> bound
  repeat rw [ite_eq_left (by simp [*];use s)]
  rw [inf_comm (link γ')] at *;have M:=L;grw [z] at L
  nth_grw 1 [← show 1 ≤ ite _ X 1 by lia,← d,← d',← g,← p,← q] at M;grw [tsub_le_iff_left.2 (r.trans_eq (add_assoc ..)),← H,mul_add,← (ENNReal.pow_le_pow_left_iff (by simp)).1 (.trans ?_ ((mul_le_mul' le_self_add le_add_self).trans (sq _).ge))];simp (disch:=positivity) only
    [D,← ofReal_mul,← ofReal_pow,← div_le_iff₀'] at *;nth_grw 2 [pow_succ _ 𝔰.k,← M]
  grw +useKAbstract [← L];simp (disch:=positivity) only [mul_pow,div_pow,Real.sq_sqrt,(submoduleIndex ..).cast_mul,submoduleIndex_smul_intVectors S.gIdele_mem,Fintype.card_subtype,card_filter_val_lt,S.gIdele_val▸genIndex_natCast _];congr! 1;field;any_goals nlinarith only [t]
  simp [ENNReal.tsum_add,← Finset.mul_sum]
  grw [ENNReal.tsum_comm.le,sum_pairWeight_le]
  simp (disch:=positivity) only [← ofReal_mul,← ofReal_add,ofReal_le_ofReal_iff,field]
  ring_nf;grw +useKAbstract [show 4≤S.b by linarith,← pow_le_tailScale (e := 𝔰.ϱ + 1 - j + 31)
    (le_mul_of_le_of_one_le (by lia) NeZero.one_le)];ring_nf;rfl
lemma Filling.q3 R (h₂ : (∃ Λ, Λ ∉ R)→S.tailScale ^ 12 / X ^ 𝔰.k * S.mainEnergy≤C) (h : linkEnergy (T ∩ {γ | S.termDisc γ ≠ 0}) Ω R ≤ .ofReal (w * S.unipCovolume ^ 2)) : energy (S.amplitudeSum (σ := .full) T) Ω ≤ (1 + (S.b ^ 4)⁻¹) ^ 2 * w + (S.b ^ 12)⁻¹ * C:=by
  have hlt {T} (hT : S.IsStable T) (h₁ : (∃ γ ∈ T,∃ c c',∃ s ∈ Ω, γ ∈ S.termsOver c s c'∧IsNormalForm 0 γ)→S.tailScale ^ 20 * S.besselEnergy≤C) n
      (h : ∀ γ ∈ T,S.CharsAgree γ → ∃ j < n,S.HasLevel j γ) :
      energy (S.amplitudeSum T) Ω ≤ C / S.b ^ 30 / 4 ^ n.rev.1:=by
    induction' n using induction with j ih generalizing T
    · simp [energy,q0 hT (by grind)];positivity
    grw [amplitudeSum_split _ {γ | S.HasLevel j.castSucc γ},energy_add_le one_pos,ih,q2 hC _ _ hx _ le_rfl _ j.castSucc ∅ (h:=by simp [linkEnergy])];simp [rev_castSucc,pow_succ,field];all_goals grind [IsStable,S.isStable_hasLevel j.castSucc]
  obtain ⟨⟨y,_,e⟩,p⟩:=exists_nonneg_add_of_le S.thousand_le_b,
    (by bound [S.thousand_le_b] : 0 < S.b ^ 4)
  grw [← sub_add_cancel (S.amplitudeSum (σ := _) T) (S.amplitudeSum T),energy_add_le p,energy_sub_cut_le,amplitudeSum_split,energy_add_le p,q2 hC _ _ hx _ _ _ (last _) R _ _ h,hlt _ _ (last _),hz,← e,← sub_nonneg];simp [field, -sub_nonneg];ring_nf;positivity
  all_goals grind [CharsAgree.q1,HasLevel,IsStable,frameDisc_frameGram_besselU_mul,hasLevel_last]
end
section
open Module Classical Complex EuclideanSpace Finset Fint Fintype InnerProductSpace Matrix MeasureTheory IntegralPlace Real Matrix.Module
namespace Filling
variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} [ok : S.IsAdmissible] {V} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
lemma ja [WeilData E] {𝔰} (S : Filling E 𝔰) [ok : S.IsAdmissible] {i x} (hx : IsCentralProj x) (b : (x.coeff 1).re≤(S.b ^ 8)⁻¹ / 2) : (∑ s,x.coeff s * ∑ y : _ × _,S.amplitudeSum (S.ratMiddle E).besselS y.1 (Pi.mulSingle i s)⁻¹ y.1 (y.2,y.2) / S.unipCovolume).re≤(S.b ^ 4)⁻¹ * S.columnDim:=by
  let T := univ.biUnion fun p : Σ i,S.chosenPlaces i↦{p.2.1,star p.2.1};have : T.StarStable := ⟨by aesop⟩;have := Fact.mk ((mem_integralOff T).2 (idem_mul_mem_Ô.1 ((mul_comm ..).subst ((S.inv_gIdele_smul_mem_iff ⟨idem Tᶜ,idem_mem_Ô _⟩).2 (by simp [reduceAboveG, -reduceAt_eq_zero];grind [reduceAt_idem,star_idem,coe_star_Ô])))));have ⟨P,F,hF⟩ := S.qs T
  obtain ⟨G,B, σ,_⟩:=hF.reduction_eq_iff,
    hF.zc ⟨_,ju,le_rfl⟩ 0
    (by grind [S.pow_chain]),axiomOfChoice (ok.reduction_surjective <| Pi.mulSingle i ·)
  have z g:=ENNReal.toReal_pos (unitaryLevel_open_compact.1 (g:=g).measure_ne_zero _ (by simp))
    (hF.z0 ju)
  grw [Level.jw,← setLIntegral_le_lintegral,lintegral_iUnion (fun s↦measurable_const_mul (S.toPlaces T (σ s))⁻¹ (measurableSet_unitaryLevel (g:=F.g))) fun s t n↦Set.disjoint_left.2 fun z u↦mt (div_mem u.out) (by simp [← G, *]),
    ← setLIntegral_mono' (measurable_const_mul _ measurableSet_unitaryLevel) fun z e↦by
    rw [setIntegral_congr_fun measurableSet_unitaryLevel fun y a↦(js (unitaryLevel_one_le_normalizer a (inv_mem e))).symm.trans (by rfl)],sdiff_le,
    SemilocalField.volume_O,hF.z7 (qb le_rfl)] at B
  grw [re_le_norm,← mul_le_mul_iff_right₀ (z 1),← norm_smul_of_nonneg,← measureReal_def,← sq_le_sq₀,← setIntegral_const,← setIntegral_congr_fun measurableSet_unitaryLevel (f:=fun y↦S.columnDim * ∑ s,x.coeff s * phase F.g (y * S.toPlaces T (σ s) * y⁻¹)) fun y a↦?_,integral_const_mul,integral_finsetSum _ fun s _↦ContinuousOn.integrableOn_compact unitaryLevel_open_compact.2 (by fun_prop)];simp [mul_pow]
  grw [norm_sum_le,norm_mul_le,sum_mul_sq_le_sq_mul_sq,(by simpa [by simpa [-Fintype.card_pi] using hx.isChar.apply_inv,x.coeff_mul_apply_left,Finsupp.sum_fintype,mul_conj',
    ← ofReal_pow] using (hx.1.eq▸b :) :),(by simpa [← sum_mul,ENNReal.toReal_sum,← le_div_iff₀,
    z,← two_mul] using (ENNReal.toReal_mono (by simp [ENNReal.mul_ne_top,hF.z0 ju]) B) :)]
  have:=(z F.g).ne';simp [field,Measure.real]
  any_goals positivity
  obtain ⟨k,rfl,o, -⟩:=qp y;lift k to S.latStabilizer using qr.2 ⟨o,a⟩
  rw [← (MulAut.conj (S.reduction k i)).sum_comp];simp [mul_sum];congr with s
  let l := k * σ s * k⁻¹
  erw [hx.2,show _ * _=S.toPlaces T l by simp [l],Pi.mulSingle,Function.update_eq_iff
    (g:=S.reduction l).2 (by simp_all [l]),phase]
  split_ifs with hs
  · obtain ⟨⟨k,r,o⟩,b,e⟩:=qp hs.choose,hs.choose_spec;rw [← r] at *
    lift k to S.latStabilizer using qr.2 ⟨o.1,by
      simpa using div_mem (qr.1 l.2).2 (ju e)⟩
    simp [↓hF.qx,o,by simpa [(G ..).2 e] using (amplitudeSum_besselU_mul isStable_besselS (u:=1) (one_mem _) (o.2.1 b) · 1),amplitudeSum_besselS_one,S.unipCovolume_pos.ne',columnDim]
  have {c} : IsEmpty ↥(_ ∩ S.termsOver c (S.reduction l)⁻¹ c) :=
    ⟨fun ⟨_,a,k,e,f⟩↦have ⟨_,hu, δ,_⟩:=exists_besselU_mul_toBesselH a;hs ?_⟩
  simp [amplitudeSum,tsum_empty];let y := c.out⁻¹ * stdEmbFin δ * c.out
  have f : k * (S.inclHFin y)⁻¹ ∈ besselU:=by simpa [*,y,termPosition,ratToFin_toBesselH,mul_assoc] using hu.termPosition_mem_besselU _
  cases eq_one_of_reduceAt_eq_one le_rfl _ _ ((forall_congr' (S.reduction_inclHFin_eq_one_iff (mem_unitaryLevel_of_besselU_mul f (inclHFin_mem_besselH y) (unitaryLevel_one.ge (by simpa [latStabilizer] using k.2))).1 (i + 1))).1
    fun _↦by ext a b;cases (besselH_apply_eq_or f (inclHFin_mem_besselH y) a b) <;> simp [*,l,reduction_apply_congr k,reduction_apply_congr 1, -Matrix.one_apply])
  exact ⟨_,(by simpa [y] using f : k⁻¹.1∈besselU).map_mem_unitriangularOn _,(G k⁻¹ _).1 (by simp [*])⟩
lemma jb [WeilData E] {𝔰} {S : Filling E 𝔰} [S.IsAdmissible] Sg D : energy (S.amplitudeSum .univ) (fixingSet Sg D)≤(1 - (S.b ^ 4)⁻¹) *
  ((1 + 9 / S.b ^ 4) * S.mainEnergy * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg):=S.of_size_bounds (by
  intros;set y : ℝ:=_ ^ #Sg
  obtain ⟨⟨x,u,e⟩,a,c⟩:=exists_nonneg_add_of_le S.thousand_le_b,S.ϱ_le_k,
    S.card_chosenPlaces 0▸Sg.card_le_univ
  have hy : S.tailScale ^ 20 * S.besselEnergy≤y * S.mainEnergy:=by
    grw [← IsAdmissible.besselEnergy_le];simp [y,field];grw [c,pow_mul _ 4 6,tailScale_pow_four];ring_nf;rfl;bound
  grw [q3 _ (by tauto) (by tauto) (by simp) (fun s k↦⟨Sg.image fun w↦(⟨0,w⟩,(D w).1),(prod_image (by simp)).ge,forall_mem_image.2 (⟨_,k.1 · ·⟩)⟩) (w:=(1 + (S.b ^ 4)⁻¹) * y * S.mainEnergy) _ (by grw [← hy,← ‹2≤S.tailScale›];bound)
    {_Λ | Sg≠univ} (by
    simp;intro;grw [← le_levelPrime,pow_mul _ 4 3,tailScale_pow_four];simp [y,field,S.card_chosenPlaces, *]
    ring_nf;gcongr;lia),← e,← sub_nonneg];field_simp;ring_nf;any_goals positivity
  simp_rw [linkEnergy,Set.univ_inter,← ENNReal.tsum_prod]
  refine (tsum_subtype_support _).ge.trans (ENNReal.summable.tsum_le_of_sum_le fun F↦?_)
  choose t σ n ht L H H' using fun j : F↦S.qu (j.1.2∘sq_eq_zero_iff.2
    ∘ enorm_eq_zero.2) fun _ ⟨k,r,f⟩ l e↦j.1.1.2.2.1.2.2.elim j.1.1.2.2.2.2 fun ⟨w,z⟩↦z l (by
    erw [← r,leadingMinor,submatrix_submatrix,← map_splitGram_latMiddle (reduceAt _),← Matrix.map_mul,submatrix_map,← RingHom.map_det,Subtype.ext (((Ô E).subtype.map_det _).trans _),map_zero]
    erw [RingHom.mapMatrix_apply,← submatrix_map,Matrix.map_mul,map_splitGram_latMiddle,← submatrix_submatrix,← frameGram,congr(frameGram _ ($f).1.1),frameGram_termPosition,submatrix_map,← RingHom.map_det];simpa)
  simp (disch:=bound) only [← ofReal_norm,← ENNReal.ofReal_pow,← F.sum_coe_sort,← ENNReal.ofReal_sum_of_nonneg];gcongr;cases' hk : 𝔰.k with k;omega
  let r := (∏ v,√𝔰.openCellConst * ∏ a : Fin 𝔰.n,S.frameScaleSq v a ^ (k + 2 * a.rev)) / Fintype.card S.BesselCoord
  have c0 := 𝔰.openCellConst_pos;choose τ hτ using (Real.range_exp.ge <| S.frameScaleSq_pos · ·)
  refine le_of_tendsto_of_frequently (tendsto_finsetSum _ fun j _↦(H j).norm.pow 2)
    (Filter.frequently_atTop.2 fun A↦let T₀ := A.biUnion univ.image ∪ univ.image t
    ⟨univ.map (.arrowCongrRight (.subtype (· ∈ T₀))),fun p h↦mem_map.2 ⟨(⟨p ·,by grind⟩),by simp,rfl⟩,le_of_mul_le_mul_left (a:=r ^ 2) ?_ (by simp [r,← hτ];positivity)⟩)
  apply le_of_tendsto_of_frequently ((tendsto_finsetSum _ fun j _↦(tendsto_finsetSum _ fun p _↦H' j p).norm.pow 2).const_mul _) ((S.qn T₀).mp (.mono _ _));rotate_right
  rintro T (o : ∀ i j,_∧_) ⟨_,h₀,g,hT⟩;obtain ⟨P,G,hG⟩:=S.qs T
  obtain ⟨Y,hm,K⟩:=hG.qa Sg D
  apply ((Filter.Eventually.all fun i↦hG.q9 hT (j:={j // t j=t i}) _ (ht
    · |>.1) (fun j↦(ht j).2.1.trans congr($(j.2))) (ht i).2.2.1 (fun j↦hm (n j) (by simp [ht])) (o i · |>.1) ⟨i,rfl⟩ («π» := .cut) _ _ (o i · |>.2) ).exists_mem_basis_of_smallSets Metric.nhds_basis_closedBall).elim
  rintro ε ⟨p,M⟩;let V := IsUltrametricDist.closedBall_openAddSubgroup (LocProd T) p
  apply ((mul_le_mul_of_nonneg_left (S.sieve T h₀ g.1 (K V (isCompact_closedBall ..)) le_sup_right) _).trans _).trans'
  · rw [mul_sum,← sum_fiberwise_of_maps_to fun i↦mem_image_of_mem t,re_sum,mul_sum]
    use sum_le_sum (forall_mem_image.2 fun i _↦by
      simpa only [← sum_subtype_eq_sum_filter,ht,subtype_univ,Subtype.prop (p:=(t · = _)),sum_map,Nat.not_succ_le_self] using! M i ⟨V.2,isCompact_closedBall ..,zero_mem V⟩)
  · unfold packetConst siegelConst;positivity
  · obtain D := ‹0≤S.mainEnergy›,S.besselDegree_pos,volÔ_ne_zero (E:=E)
    simp [prod_range]
    grw [← besselDegree,prod_comm,IsAdmissible.packetConst_mul_mass_le,← sq_sqrt c0.le,(?_ : (1 + _) ^ _≤1 + S.b⁻¹ ^ 9),← c]
    simp only [y,frameScaleProd,hk,pow_add,prod_mul_distrib,prod_pow,fieldLe,← e,inv_pow,← hτ,card_univ,prod_const,Fin.val_rev,Nat.succ_sub_succ,pow_mul]
    clear * - u D;rw [← sub_nonneg];ring_nf;positivity
    grw [add_comm,add_one_le_exp,← Real.exp_nat_mul,S.f_le_b,Real.exp_bound' _ _ one_pos] <;>
      simp [field] <;> bound
  intro i j l e;ext <;> simp only [ht,by simpa [ht] using e];swap
  ·
    intro i j;ext
    rw [Finset.prod_congr rfl fun v _↦(S.besselSys v).band_limits.2 _ ((ht j).1.ratToInf_mem_unitriangularOn v) _ _ ?_ ?_]
    simp_rw [normCorrelation,gram_apply,inner_smul_left_eq_smul,inner_smul_right_eq_smul,real_smul]
    simp only [inner,besselFn,besselCorrelation,Pi.mul_apply,Pi.inv_apply,star_def,prod_univ_sum,qo,prod_mul_distrib,← map_prod,sum_prod_type,← integral_fintype_prod_volume_eq_prod,← ofReal_prod];rfl'
    repeat simp [ht,frameScaleSq,padTuple,unitOrOne,j.2]
  · intro i p
    simp [frameScaleSq.eq_1 S _ 𝔰.ϱ,div_pow,div_mul_eq_mul_div,div_sub_one, -one_div,hk,mul_add,unitOrOne,↓Fin.prod_univ_castSucc,mul_pow,abs_of_pos,pow_add,Fin.rev_castSucc,padTuple,prod_pow,prod_range,(S.frameScaleSq_pos ..).ne',Level.headDensity,P.qw (h₀ _ (p _).2), @prod_comm (Fin 𝔰.ϱ),prod_eq_zero_iff,field]
    simp [sqrt_eq_rpow,rpow_pow_comm,finsetProd_rpow,((ht i).2.2.1 _).le,prod_nonneg]
  simp [↓Filter.eventually_all,qm, -Filter.eventually_atTop])
attribute [-simp] mul_re univ_unique Fintype.card_pi
lemma jc [StablyUnram E] i : energy (S.amplitudeSum (S.ratMiddle E).besselSᶜ) {s | ∃ t∈S.reducedImage besselS,s i=t i} ≤
  (S.b ^ 12)⁻¹ * S.besselEnergy:=S.of_size_bounds (by
  intros;obtain _:=S.ϱ_le_k, @besselFrame_castSucc 𝔰 ⟨0,pos_of_gt S.ϱ_le⟩
  grw [q3 (by bound) (by grind [IsStable,S.isStable_besselS]) ?_ (by simp) (fun s h↦⟨image (.map (.mk i) id) ⊤,(prod_image (by intro;grind)).ge,forall_mem_image.2 fun p _↦⟨⟨Pi.single (0 : Fin (𝔰.ϱ + 1)) 1,by simp⟩,
    .symm ?_⟩⟩) le_rfl le_rfl ∅ (by
    simp [S.card_chosenPlaces];grw [← ok.mainEnergy_le,codimFactor,g_le_b_pow,← le_levelPrime]
    simp [div_pow,field,pow_mul _ 4 2,tailScale_pow_four];ring_nf;bound) (by simp [linkEnergy])];simp
  · rintro ⟨γ,n,c,c',_,⟨_,⟨t,ht,rfl⟩,hs⟩,⟨k,rfl,hk⟩, ζ,hζ,h⟩
    choose X Y e h using (h · bot_le)
    have h3 : (1⁻¹ * stdEmbFin (U.of isUnit_one (scalar Unit ζ) (by simp [mul_comm,hζ])) * 1).1 () ()=k.1.1 (𝔰.besselFrame 0) (𝔰.besselFrame 0):=by
      obtain _:=congrFun (e 0) (𝔰.besselFrame 0),
        congrFun₂ (hk▸frameImage_termPosition) (𝔰.besselFrame 0) 0
      simp_all [classCoord_eq_fromBlocks,mul_apply,U.of,mulVec_eq_sum,Fin.sum_univ_succ]
    have:=S.eq_one_of_reduceAt_eq_one (by simp;omega) _ (mem_Kf.2 fun _ _↦h3▸k.2.isIntMatrix _ _) fun w↦by
      ext;convert hs▸reduction_apply_congr 1 i w
        (mem_besselS_iff_frameImage.1 ht (𝔰.besselFrame 0) 0 bot_le)
      use congr(reduceAt _ ⟨$h3,_⟩);simp
    cases (by simpa [U.of] using congr($this.1 () ()) : ζ = 1)
    cases n (mem_besselS_iff_frameImage.2 fun j ↦
      wellFounded_lt.fix fun b↦by clear * - e h;grind [congrFun (e b) j,mulVec_apply_eq_sum,Fintype.sum_eq_single b,Matrix.one_apply,submatrix_apply])
  obtain ⟨_,⟨k,hk,rfl⟩,h⟩:=h;have:=(mem_besselS_iff_frameImage.1 hk · 0)
  simp [h,← intGL_map_reduceAboveG,Units.smul_def];simp_all [funext_iff,mulVec_eq_sum,inclMatrix, -Sum.forall,ite_eq_iff',← Submonoid.one_def,← ZeroMemClass.zero_def])
attribute [local simp] Filling.ratToFin_toBesselH Filling.termPosition mul_assoc in
private lemma exists_besselS_mem_termsOver [ok : S.IsAdmissible] c {σ} : σ ∈ S.reducedImage besselS → ∃ d, ∃ γ ∈ besselS, γ ∈ S.termsOver c σ d := fun ⟨k, hk, _⟩ ↦ by
  obtain ⟨u, hu, _, ⟨g, ⟨⟩⟩, e⟩ := S.range_inclHFin ▸ mem_besselS.1 (mul_mem (mem_unitriGroup_of_mem_floorGroup (inclHFin_mem_besselH c.out)) hk)
  obtain ⟨⟨x, hx, l⟩, d, η, a, rfl⟩ := exists_besselU_approx hu (S.inclHFin g), exists_eq_map_mul_rep_mul stdEmbFin S.columnLevel (·.out_eq) g
  exact ⟨d, x * toBesselH _ _ η, mem_besselS.2 ⟨_, hx, _, toBesselH_mem η, rfl⟩, (div_mem l (ok.1.le a.2)).imp' (k * ·) (by simp_all [division_def, ← mul_inv_eq_of_eq_mul e, ratToFin_toBesselH η])⟩
lemma jd [WeilData E] {Θ : _ → ℝ} (h0 : ∀ s,0 ≤ Θ s) (u : _→V) (hu : ∀ a b, ⟪u a,u b⟫_ℂ = Θ (a⁻¹ * b)) A (D : ∀ _,_) (hB : ∀ Ω,∑ s with s ∈ Ω, Θ s≤energy (S.amplitudeSum .univ) Ω) (hA : ∀ s, Θ s≠0→∀ w∈A,s∈S.vectorFixer (i:=0) w (D w)) : ∑ s, Θ s≤(1 + 9 / S.b ^ 4) * S.mainEnergy * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #A:=by
  induction' A using WellFoundedGT.induction with A ih generalizing V Θ D
  obtain ⟨hq,q,_⟩:=S.levelPrime_le 0,S.le_levelPrime 0,S.thousand_le_b,
    univ.sum_nonneg' h0,S.ϱ_le_k;by_contra! hK
  apply hK.not_ge
    (le_of_mul_le_mul_left (.trans _ (jb A D)) (by bound [@one_lt_pow₀ ℝ]))
  grw [← hB,one_sub_mul,sub_le_comm,← sum_sdiff_eq_sub (by simp),← sum_filter_ne_zero]
  obtain hw | ⟨w,hw⟩:=em' (Exists (· ∉ A))
  · rw [Finset.sum_eq_zero (by simp;grind [fixingSet])];bound
  choose! L hL using fun s (e : s∉S.fixingSet A D) h↦by simpa using (e ⟨hA s h,.inr ⟨w,·⟩⟩)
  grw [← Finset.sum_fiberwise _ L,sum_le_card_nsmul _ _ (3 * univ.sum Θ / S.b ^ 10)
    fun l _↦let F b := frameImage (cond b (S.latMiddle (ResField w.1)).splitGram 1) *
      inclMatrix (ResField w.1) (Fin.castLE l.is_le)
    (le_div_iff₀' (by bound)).2 (.trans ?_ ((zl (.mk' (· 0 w) (by simp)) F h0 hu
    (univ.sum Θ / S.b ^ (6 * 𝔰.k)) (by bound) fun b v hv↦by
    grw [sum_filter,ih _ (ssubset_insert hw) _ (fun a↦basisFun _ ℂ (cond b invTransposeGL 1 (a 0 w)•F b *ᵥ v) ⊗ₜ[ℂ] u a) _ (Function.update D w ⟨b,_,(map_ne_zero_iff _ (inclMatrix_mulVecLin_injective (Fin.castLEEmb l.is_le) _)).2 hv⟩) (.trans (by gcongr;bound) <| hB ·),← hK] <;> simp [*,apply_ite ofReal,ite_nonneg,pow_succ,field,inner,smul_smul,← eq_inv_smul_iff]
    · exact fun s h _↦⟨by cases b <;> simp [vectorFixer] <;> (repeat erw [mul_smul]) <;>
        simpa [F,← mul_inclMatrix,← mulVec_mulVec,inv_smul_eq_iff] using! h.symm,by grind⟩
    tauto).trans ?_))]
  · simp [field];grw [← le_self_pow₀,← k_le_b,← S.ϱ_le_k] <;> push_cast <;> nlinarith
  · gcongr <;> simp [*,sum_nonneg',subset_iff,F,transpose_splitGram,mul_inclMatrix,← inclMatrix.eq_1,card_eq_nat_card,↓card_resField_eq_levelPrime];bound
  grw [mul_div_left_comm,div_le_one_of_le₀];linarith;grw [← sq_le_sq₀,mul_pow,sq_sqrt,card_eq_nat_card,card_resField_eq_levelPrime,hq,hq];simp [← pow_mul,← pow_add];repeat bound [l.2]
lemma je [StablyUnram E] i {x} (hx : IsCentralProj x) : ∑ a : _ × _,‖WithLp.toLp 2 fun b : _ × _↦∑ t,x.coeff t * (S.amplitudeSum (S.ratMiddle E).besselSᶜ a.1 (Pi.mulSingle i t)⁻¹ b.1 (a.2,b.2) / S.unipCovolume)‖ ≤ (S.b ^ 4)⁻¹ * S.columnDim:=by
  let φ : _ →* S.GRes := .mulSingle _ i;have := S.thousand_le_b
  let Y s := ∑ c,∑ c',‖∑ t,
    x.coeff t•S.amplitudeSum (S.ratMiddle E).besselSᶜ c ((φ t)⁻¹ * s) c'‖ ^ 2 / S.unipCovolume ^ 2
  have h:=((card_nsmul_le_sum {s | s∈S.reducedImage besselS} Y (Y 1) fun σ h↦?_).trans ?_).trans (S.jc (i + 1))
  · simp [besselEnergy,← card_subtype,field] at h
    grw [← sq_le_sq₀,sq_sum_le_card_mul_sum_sq,show ∑ _,_=Y 1 by simp [Y, φ,norm_sq_eq,sum_prod_type,← sum_div,div_pow,mul_div, @sum_comm S.Classes _ S.BesselCoord],
      (le_div_iff₀ _).2 h] <;> simp [columnDim,field,sum_nonneg'] <;> bound
  choose p σ₀ h₀ h₁ using (exists_besselS_mem_termsOver · (mem_filter.1 h).2);apply congr(∑ c, $(sum_bijective p (Finite.injective_iff_bijective.1 fun c d h↦(eq_and_mem_classUnip_of_besselS (by aesop) (mul_inv_cancel σ ▸ termsOver.mul (h₁ c) (.inv (h▸h₁ d)))).1) _ _ fun d↦.symm ?_)).le;obtain ⟨u,hu, η,hη,e⟩ := mem_besselS.1 (h₀ d);choose k hk using fun v↦exists_toBesselH_eq (hη.ratToInf_mem_unitriangularOn v);let A v := (S.besselSys v).rep (k v);let := @instDecidableEqProd
  rw [← Unitary.norm_map ⟨_,Unitary.map_mem (toEuclideanCLM (𝕜 := ℂ)) (kronecker_mem_unitary
    (one_mem _) (UnitaryGroup.map_star ⟨(S.unipotentChar (S.ratToFin u))⁻¹ • kroneckerPi (A ·),by
    erw [mem_unitaryGroup_iff,star_smul,smul_mul_smul,← kroneckerPi_one,← funext (A · |>.2.2),kroneckerPi_mul,mul_conj',norm_inv,norm_selfDualChar]
    ext;simp [mul_apply,kroneckerPi]⟩).2)⟩,map_sum]
  congr! 4;rw [map_smul,← amplitudeSum_move (by grind [IsStable,S.isStable_besselS]) _ (S.classUnip _).one_mem.2 _ (h₁ _)] <;> simp [h₀,mul_mem_cancel_right]
  intros;ext;simp [e,besselKernel,mul_assoc,besselFn_ratToInf_mul hu,mulVec_apply_eq_sum,sum_prod_type]
  simp [besselFn,hk,((besselSys ..).tail.isBesselFunction _).3,kroneckerPi,↓mulVec_eq_sum,Fintype.prod_sum,mul_sum];ac_rfl;simp_rw [Y,energy,← @sum_comm S.GRes,← sum_div];gcongr;refine .trans ?_ (by simpa [apply_ite,sum_ite] using hx.sum_norm_conv_le φ fun s↦ite (∃ t,_) (S.amplitudeSum ..) 0);grw [← subset_univ];congr!;aesop
lemma Fits.jf [WeilData E] {g c} [Module.Finite ℂ V] {ρ : Representation ℂ _ V} (hρ : ∀ s x y, ⟪ρ s x, ρ s y⟫_ℂ = ⟪x,y⟫_ℂ) {Q : EuclideanSpace ℂ (_ × _) →ₗ[ℂ] V} (hQ : ∀ s x y, ⟪ρ s (Q (.single y 1)),Q (.single x 1)⟫_ℂ=ofReal c * S.amplitudeSum .univ x.1 s y.1 (x.2,y.2)) (hg : ∀ i,IsCentralProj (g i)) (hb : ∀ i,((1 - g i).coeff 1).re≤(S.b ^ 8)⁻¹ / 2) (hc : 0 < c) (hD : finrank ℂ (ρ.asAlgebraHom (piTensorElem g)).range≤Nat.card S.GRes * S.besselDegree * mass E 𝔰.r) : IsSpread ((ρ.asAlgebraHom (piTensorElem g)).rangeRestrict ∘ₗ ρ · ∘ₗ Q) (19 / 2 * (S.b ^ 4)⁻¹):=by
  set R := ρ.asAlgebraHom (piTensorElem g);intro F φ;apply S.of_size_bounds;intros
  obtain ⟨⟨t,ht⟩,G,B,o⟩:=(isSquare_iff.2 (mul_pos hc S.unipCovolume_pos).le).inv,
    IsCentralProj.piTensorElem hg,S.amplitudeSum_split .univ (S.ratMiddle E).besselSᶜ,
    (hg · |>.one_sub);let P := t•Q
  have hu a b x y : ⟪ρ b (P (.single y 1)), ρ a (P (.single x 1))⟫_ℂ =
      S.amplitudeSum .univ x.1 (a⁻¹ * b) y.1 (x.2,y.2) / S.unipCovolume:=hρ a⁻¹ .. ▸ by
    simp [← End.mul_apply,← map_mul,P,← mul_assoc,← ofReal_mul,← ht,hQ,field,hc.ne']
  have pr {z} (hz : IsCentralProj z) y : ⟪_,_⟫_ℂ=_ :=
    (hz.self_adjoint ρ 1 (innerₛₗ ℂ) hρ y _).trans congr(⟪y, $(hz.1.map ρ.asAlgebraHom) y⟫_ℂ)
  have hb' i:=add_le_add (S.ja (o i) (hb i)) ((je i (o i)).trans' (sum_le_sum fun a _↦(PiLp.norm_apply_le _ a).trans' (re_le_norm _)));refine (exists_le_of_sum_le univ_nonempty (g:=fun _↦S.columnDim / 2 * (1 + 9 * (S.b ^ 4)⁻¹ + φ)) ((sum_le_sum fun s _↦zn (stdOrthonormalBasis ..) (ρ s ∘ₗ P) (ρ.asAlgebraHom (1 - piTensorElem g)) (F.comap (R.rangeRestrict ∘ₗ ρ s ∘ₗ Q)) (F.map R.range.subtype) (Eq.trans_le ?_ (S.je 0 (.one_sub ⟨.zero,by simp⟩))) fun _↦(⟨_,F.smul_mem t ·,by simp [P,R]⟩)).trans ?_)).imp fun s h↦?_
  · congr! 2;ext;rw [← basisFun_inner]
    simp [inner_sub_right,LinearMap.adjoint_inner_right,inner_single_left,hu,amplitudeSum_besselS_one,ite_div,add_div,B,apply_ite,S.unipCovolume_pos.ne',Finsupp.single_apply,MonoidAlgebra.one_def];grind
  · grw [← re_sum,← sum_inner,re_le_norm,norm_inner_le_norm,← sq_le_sq₀,mul_pow, @norm_sq_eq_re_inner ℂ,zk (energy (S.amplitudeSum .univ) {·}) ?H]
    simp [@norm_sq_eq_re_inner ℂ,↓inner_dyadSum,apply_ite,← Submodule.coe_inner,mul_pow,← show φ * _=_ from div_mul_cancel_of_imp (mod_cast by bound [F.finrank_le]),orthonormal_iff_ite.1];grw [jd (fun _↦by unfold energy;positivity) _ ?H ∅ (fun _↦⟨⊤,1,by simp⟩) _ nofun,hD,← four_mul_le_sq_add];simp [mainEnergy];field_simp [mass_pos,besselDegree_pos,ne_of_gt];any_goals positivity
    repeat norm_num [energy,sum_filter,norm_sq_eq,sum_prod_type,sum_div,hu,div_pow, @sum_comm S.Classes _ S.BesselCoord, @sum_comm S.GRes]
  have k:=univ.sum_nonneg fun y _↦pr (.piTensorElem o) (P (.single y 1))▸inner_self_nonneg
  simp [add_div,show piTensorElem (1 - g ·)=∑ i,
    piTensorElem (Pi.mulSingle i (1 - g i)) - (1 - piTensorElem g) by
    ext;simp [← map_one piTensorElem, -map_one];ring,↓@norm_sq_eq_re_inner ℂ,↓hρ,columnDim,
    ↓pr G.one_sub,mul_add,mul_sum, @sum_comm (_ × _),asAlgebraHom_piTensorElem_mulSingle,B,(by
    simpa using congr(ρ.asAlgebraHom $(G.2.commute (.single s 1)) ·).symm),
    asAlgebraHom_eq_sum (ρ.comp _),by simpa using (hu · 1)] at *
  linarith
end Filling
end
open Filling Module Submodule
variable {P} (D : Data P) (c : ℂˣ)
noncomputable def Data.poincare : D.Column →ₗ[ℂ] D.principalForms (D.spaceY 0):=D.filling_fits.poincareMap.1 ∘ₗ D.columnCoords
private lemma Data.finrank_rows_le_mass : D.rowDim ≤ Nat.card D.G * D.filling.besselDegree * mass D.E D.r := by
  obtain ⟨⟨_, _, h⟩, A⟩ := exists_isHCParam_of_hasGap D.hasGap_signsY_paramW, D.classAut_eq_bot_of_le_chosenLevel (n := D.RowIndex) le_rfl D.nat_le_of_hasLogBound
  grw [D.finrank_rows_eq_finrank_goodForms ⟨_, D.nat_le_of_hasLogBound, le_rfl⟩, Submodule.finrank_le]
  erw [← (Space.algFormEquiv _ h _).finrank_eq, finrank_levelSpace_smoothFormRep A, Nat.cast_mul, card_classes_eq_classSum A, classSum_one_of_le levelOf_le_Kf, relIndex_levelOf, classSum_stdRatPoints_eq_mass, Module.finrank_pi, ← h.prod_formalDegree]
  simpa [Filling.besselDegree, (D.filling_fits.1 _).1, ↓card_rowIndex, Orbital.harish_chandra_degree_and_orbital, h.hasGap] using by linarith
lemma Data.ramifiedColumns_fill_rows : IsSpread (D.goodProjTranslate · ∘ₗ D.poincare ∘ₗ (c.1•D.ramifyingOp .univ)) (D.b ^ 2)⁻¹ := by
  have:=D.hasLogLower_of_le (le_sub_iff_add_le.2 D.le_of_hasLogBound : D.b ^ 9≤D.N - 1);have h:=Fits.jf (ρ := .comp (D.principalRep _) (.mk' _ (by tauto))) (fun _ _ _↦Space.inner_formRep ..) (fun _↦(D.filling_fits.jg · · (@reduceFamily_liftResidue ..))) (fun _↦isCentralProj_sum_tupleIdem) (fun i↦(bad_share_le (M:=P.Mω D.s) (q:=D.g i) _ (9 * D.logB) (card_resField_eq_levelPrime _ i) rfl (card_chosenPlaces _ i) D.nat_lt_of_hasLogBound D.nat_lt_of_hasLogBound D.le_of_hasLogBound le_rfl D.le_of_hasLogBound).trans (filling.eq_1 D▸D.le_of_hasLogBound)) (measureReal_pos_of_isLevel (K:=D.chosenLevel));erw [(?_ : Representation.asAlgebraHom _ _=(principalRep ..).asAlgebraHom D.e₀),Shape.r,card_rowIndex,← Nat.card_congr (.piCurry _)] at h;simp_rw [IsSpread,← D.columnCoords.finrank_eq,← (D.columnCoords.ofSubmodule' _).finrank_eq] at h
  refine fun F↦(h D.finrank_rows_le_mass F).imp' Sigma.uncurry fun _ h ↦
    .trans (mod_cast finrank_mono fun _↦by simpa using!
    id) (((D.ramifyingOp_finrank_comap_and_short .univ _).1.trans (add_le_add h le_rfl)).trans ?_)
  simp [← add_mul,add_assoc,card_piPlaces,filling];gcongr;use D.le_of_hasLogBound
  open Fint in simp_rw [asAlgebraHom_eq_sum,reindex_equiv (Equiv.piCurry _)]
  simp [e₀,goodTupleFamilies,tupleIdem,Finset.prod_univ_sum,Fintype.prod_sigma];rfl
lemma Data.finrank_rows_ne_zero : finrank ℂ D.rows≠0:=fun e↦(D.ramifiedColumns_fill_rows 1
  ⊤).rec fun _↦by erw [finrank_top,e];norm_num [finrank_pos_iff.2 D.columnCoords.nontrivial,← lt_tsub_iff_left];use D.lt_of_hasLogBound
