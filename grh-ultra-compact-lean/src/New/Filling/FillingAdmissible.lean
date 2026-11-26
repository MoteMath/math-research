import New.Filling.EichlerFlag
import New.RealPlace.WeightPlancherel
import Lib.Adelic.Adeles.FinitePlaceDensity
import New.RealPlace.LocalTheorem
import New.Filling.NearTerms
import Lib.Adelic.CuspForms.RealConvolution
import New.Filling.AmplitudeSums
import New.Filling.DegreeBounds
section
open Filter Fintype Level MatMul Matrix MeasureTheory NNReal Place Pointwise SemilocalField Sum Topology MeasureTheory.Measure
attribute [local simp] HyperbolicBasis.floorBasis Finset.mul_sum IsIntMatrix mul_mem IntegralPlace.data_mem flatChart IsStarStable.star_mem Size.HasMatSize Size.vecsOfSize ascConv funext_iff inclMatrix intVectors ite_mem mul_add mul_assoc sub_mem sum_mem
noncomputable def ji {A : Type} {𝔰} [CommRing A] [StarRing A] (π : Aˣ) t x:=(besselLatticeBasis 𝔰 π)⁻¹.1 *ᵥ (0 ⊕ᵥ ((x ⊕ᵥ fun _↦-(π * star π)⁻¹ * t) ⊕ᵥ 0))
variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [Fintype ι] {m : ℕ} {π : Aˣ} {N : A} [P : Place A] {t : A} {x : 𝔰.κ → A}
omit [TopologicalSpace A] [MeasureSpace A] [Place A] in
lemma jj (hN : π * star ↑π = N) : let J :=
    (latMiddleGram 𝔰 N).splitGram;let e := ji π t x;star e ⬝ᵥ
      J *ᵥ e=star x ⬝ᵥ x - (π * star π)⁻¹.1 * t * star t∧(J *ᵥ e) 𝔰.z=t:=by
  simp [← gram_besselLatticeBasis π N hN,← mulVec_mulVec,← star_mulVec_dotProduct,ji]
  simp [besselLatticeBasis,splitGram,middleGram,entrywise];grind [π.mul_inv,star_mul,star_one]
@[fun_prop] lemma continuous_tailVector : Continuous fun z : A × (𝔰.κ → A) ↦
  ji π z.1 z.2:=by simp [ji,mulVec_eq_sum];fun_prop
lemma HyperbolicBasis.jk [IsHermUnit (latMiddleGram 𝔰 N).splitGram] (F : HyperbolicBasis ι (latMiddleGram 𝔰 N) m) (hN : π * star ↑π = N) {Φ : _ → ℝ≥0} (hΦ : Continuous Φ) (cΦ : HasCompactSupport Φ) {c} (hc : ∫⁻ e, Φ e ∂F.floorQuadric 𝔰.top < c) : ∀ᶠ S in
  (𝓝 0).smallSets,MeasurableSet S→∫⁻ τ,∫⁻ y in {y | star y ⬝ᵥ y - ((π * star π)⁻¹ * τ * star τ - N)∈S}, Φ (ji π τ y)≤P.md π * P.skewMeasure {Γ | P.skewUnit⁻¹.1 * Γ ∈ S} * c:=by
  filter_upwards [eventually_smallSets_forall.2
    (((continuous_sub_right N).const_mul skewUnit.1).tendsto' 0 _ (by simp [splitGram,latMiddleGram]) (eventually_comap.1 ((nhds_subtype ..).ge (((F.isDisintegration_floorVolume _ rfl).continuousOn_lintegral hΦ cΦ).1.upperSemicontinuous _ _ hc))))] with S k mS
  grw [mul_right_comm,mul_assoc,← measure_preimage_add_right _ (P.skewUnitMul _ (star_mul_star π.1 π)),← lintegral_indicator_const_le,← lintegral_mono fun Γ↦?_,← (F.isDisintegration_floorVolume 𝔰.top (map_inclMatrix_eq_floorVolume (inr∘inl))).lintegral_eq fun p↦S.indicator 1 (p.1 + N) * Φ p.2,lintegral_map,lintegral_eq_mul_lintegral_map ((P.map_mulVec_volume _ ((middleBaseChange 𝔰 π).fromCols (fromRows 0 (-(π * star π)⁻¹.1•1))) _).trans _),lintegral_map,ENNReal.mul_inv_cancel_left,← measurePreserving_sumElim.lintegral_comp,volume_eq_prod,lintegral_prod_symm,← (volume_preserving_funUnique ..).symm.lintegral_comp] <;> try fun_prop
  simp (disch:=measurability) only [← lintegral_indicator]
  gcongr with τ y;rw [(?_ : _ *ᵥ _ *ᵥ _=ji π τ y)]
  any_goals simp +contextual [↓jj,ji,besselLatticeBasis,middleBaseChange,entrywise,apply_ite,← mul_assoc,ENNReal.mul_inv_cancel,Set.indicator,sub_add, *]
  grind [skewUnit.mul_inv]
attribute [-simp] splitGram_eq_ite_oppositeIndex
variable {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] {T : 𝔰.Form A} [IsHermUnit T.splitGram] (F : Level ι T m)
noncomputable abbrev Level.congGroup:=unitaryLevel O F.g T.splitGram
structure IntegralPlace.IsLatticeLevel where
  integral_data : IsUnimodular R T.splitGram∧IsIntMatrix R F.basisMatrix∧F.g.1∈R ∧
    star F.g.1=F.g
  box_eq : volume P.intUnits≤F.θ F.boxSet∧F.boxSet=unitaryLevel R 1 T.splitGram ∧
    F.measureH F.boxSet=1∧F.𝔅 = intVectors P.R 𝔰.BesselIndex∧F.positions =
    {y⁻¹ * u * y | (y) (u∈T.besselU)} * F.congGroup
  exists_isotropic : ∃ u,star u ᵥ* T.splitGram=Pi.single (𝔰.besselFrame 𝔰.top) 1 ∧
    u (𝔰.besselFrame 𝔰.top)=0
class IntegralPlace.IsStdLevel (F : Level ι T (m + 1)) extends P.IsLatticeLevel F where
  zeta_rank : idealZeta P.R m ^ 𝔰.n ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n)∧m < 9 * 𝔰.n∧13 * 𝔰.n≤card ι
  unimodular : ∃ ν : Measure T.G, ν.IsHaarMeasure ∧ ν.IsMulRightInvariant
variable {g : Aˣ} {F : Level ι T (m + 1)} [h : P.IsStdLevel F]
lemma IntegralPlace.jl {N} [IsHermUnit (latMiddleGram 𝔰 N).splitGram] (hN : N∈R∧star N=N) (hg : g.1∈R∧star g.1=g) (hm : 𝔰.k=card ι + 2 * m + 1) : ∃ F : Level ι (latMiddleGram 𝔰 N) m,P.IsLatticeLevel F∧F.g=g:=by
  obtain ⟨⟨c,hc,e⟩,u,f⟩:=P.isAdelic.exists_norm_neg_one,isUnimodular_latMiddleGram 𝔰 hN,
    (equivOfCardEq (by simp +arith [hm]) : SplitIndex m ι ≃ {i // 𝔰.k₀≠i})
  let E := inclMatrix A (![inl 𝔰.k₀,inr ()] ⊕ᵥ (inl <| f ·)) * @fromBlocks _ (SplitIndex m ι) _
    (SplitIndex m ι) A !![-1, -N * P.τ;0,1] 0 0 (fromBlocks 1 (fromCols 0 (P.τ • 1)) (fromRows 0 (c•1)) (fromBlocks 1 0 0 ((-star P.τ * c)•1)))
  have hE : IsIntMatrix R E := .mul (by simp) (by simp [*])
  let F : HyperbolicBasis ι (latMiddleGram 𝔰 N) m := ⟨E,by
    rw [gram_mul,gram_inclMatrix];simp [entrywise,latMiddleGram,diagonal,(f _).2.symm,Subtype.val_inj]
    grind,by lia,by grind [md_det_eq_one,u.2]⟩
  let l := 𝔰.besselFrame 𝔰.top;let x : 𝔰.BesselIndex→A := Pi.single (𝔰.indexX₀ 𝔰.k₀) (-1)
  let J := (latMiddleGram 𝔰 N).splitGram;let φ p :=
    F.floorBasis 𝔰.top *ᵥ flatChart (hyperbolicGram _ 1) (P.skewUnitMul (J l l)) p
  obtain ⟨t,hx⟩ : (∀ p, φ p 𝔰.z=p.1.1)∧star x ᵥ* J=Pi.single l 1∧x l=0 :=
    by simp +zetaDelta [entrywise,splitGram,latMiddleGram,diagonal]
  have M := measurable_unitary_of_coe (f := fun p↦U.of IsHermUnit.isUnit _ (exists_eichler_orbitPoint_eq (e := φ p) hx).1) (by fun_prop);have C := isClosed_of_entries_eq_one (J := J) (mem_floorGroup (l := 𝔰.n));have w := MeasurableEmbedding.subtype_coe C.measurableSet;let ν : Measure besselH := .inv (haarMeasure ⟨⟨_,unitaryLevel_open_compact.2.inv.preimage_val C⟩,1,by simp [unitaryLevel_open_compact.1.preimage_val.interior_eq]⟩);have n := (w.map_apply ν (unitaryLevel R 1 J)).trans ((inv_apply ..).trans haarMeasure_self)
  refine ⟨.mk F _ _ g _ _ _ (neZero_measureH:=⟨(by simp [·] at n)⟩) ⟨(ae_map_iff M.aemeasurable measurableSet_floorGroup).2 (.of_forall fun _↦(exists_eichler_orbitPoint_eq hx).2.1 fun i k↦by simp [φ,← mulVec_mulVec];exact Finset.sum_eq_zero (by simp;grind [floorOf])),(Measure.map_map (by fun_prop) M).trans (.trans (Measure.map_congr ((quasiMeasurePreserving_fst.ae (quasiMeasurePreserving_fst.ae ae_isUnit)).mono fun p k↦(exists_eichler_orbitPoint_eq hx).2.2 ?_ (by simpa [t]))) (Measure.map_map (g:=mulVec _) (by fun_prop) (by fun_prop)).symm)⟩ ⟨w.ae_map_iff.2 (by simp),fun s k↦(mconv_dirac ..).trans ((w.2.measurePreserving _).of_semiconj
    (measurePreserving_mul_right ν ⟨s,k⟩) (by tauto) (by fun_prop)).2,fun y↦by
    simp_rw [← n,w.map_apply];exact measure_le_of_div_mem fun x ⟨v,b,c⟩↦⟨x,fun k ⟨w,e,f⟩↦mem_unitaryLevel_of_besselU_mul (mul_mem e ((besselS_le_normalizer_besselU
      (mem_unitriGroup_of_mem_floorGroup (k / x).2) _).1 (inv_mem b))) (k / x).2 (by
      simpa [div_eq_mul_inv] using div_mem f c)⟩⟩ hg.2 ⟨intVectors_open_compact_vol.1,by simp,
    intVectors_open_compact_vol.2.1.closure⟩ ⟨unitaryLevel_open_compact.2,
    unitaryLevel_open_compact.1.mul_left.measurableSet⟩,⟨⟨u.splitGram,hE,hg⟩,⟨.trans (by
    simp [intVectors_open_compact_vol, -intVectors]) ((measure_mono (s:=(intUnits ×ˢ intVectors R _) ×ˢ {b | b.1∈R}) ?_).trans (le_map_apply M.aemeasurable _)),by tauto⟩,x,hx⟩,rfl⟩
  · dsimp;erw [star_mulVec_dotProduct,mulVec_mulVec,mulVec_mulVec,F.gram_floorBasis,form_flatChart] <;> simp +zetaDelta [k]
  rintro ⟨⟨_,w⟩,b⟩ ⟨⟨⟨d,v,r,rfl⟩,y⟩,a⟩
  refine (fun c : ∀ i, φ ((v,w),b) i∈R↦u.splitGram.mem_unitaryLevel ?_ ?_) (IsIntMatrix.mulVec ?_ ?_) <;> simp (maxDischargeDepth:=19) [-sum_sum_type,entrywise,vecMulVec_apply,add_mem,vecMul,x,u.splitGram.isIntMatrix _,F,hE _,J,y _,a.out, *]
namespace IntegralPlace.IsStdLevel
@[simp] noncomputable def gauge (α : Aˣ := 1) (hα : α.1∈R:=by simp) (sα : star α.1 = α := by simp [*] <;> ring) : Gauge F:=by
  have l:=by simpa using ENNReal.div_le_div_left (md_le_one α hα) 2
  obtain ⟨J,c,_,G,o⟩:=h.integral_data.1.isIntMatrix,le_two_of_pow_le_ofReal h.zeta_rank.1,
    h.zeta_rank,h.integral_data.2,one_le_two.trans l
  have L j : (md (α ^ j).1)⁻¹ ≤ (2 / P.md α) ^ j:=by grw [← one_le_two];simp [ENNReal.inv_pow]
  have Z {j n k} (e : j * n + 1≤k):=(mul_le_mul' (c.trans l) (pow_le_pow_left' (L j) n)).trans
    ((pow_le_pow_right' o e).trans_eq' (by ring))
  refine' { ofSize j:={x | α ^ j * x∈R}, Λ := 2 / P.md α,.. };rotate_right;simp_rw -zeta [closePairs,h.box_eq];rintro x hx _ ⟨_,⟨y,u,hu,rfl⟩,k,hk,rfl⟩ v W
  have σ : SplitIndex 𝔰.ϱ (Fin 𝔰.ϱ) ⊕ Fin (F.volumeExponent + (m + 5)) ≃ ι :=
    equivOfCardEq (by simp;lia)
  let N := (y * x⁻¹).1.1 * F.orthonormalPart;obtain ⟨V,hV,z⟩ := valPair.exists_mul_clear_cols (v.fromRows (N∘inr∘inr ⊕ᵥ ((u⁻¹.1.1 - 1) * N)∘inl)) (.trans .inl σ.toEmbedding);let Y := V.1.submatrix id (σ ∘ inr)
  have w t (a : t∈intVectors R _) : Y *ᵥ t∈W:=by
    have z a j:=z a (σ (inr j)) (by simp);have r:=hx.1.isIntMatrix_inv.mul (N:=F.orthonormalPart * Y) (by simp [mul_apply,G.1 _,Y,hV.isIntMatrix _])
    have : (u⁻¹.1.1 - 1) * N * Y=0:=Matrix.ext (Sum.rec (z <| inr <| inr ·) fun i j↦by
      rw [Matrix.mul_assoc,mul_apply]
      simp [apply_inr_of_mem_besselU (inv_mem hu), -Subgroup.coe_inv, -InvMemClass.coe_inv,fun a↦show (N * Y) (eStar a) j=0 from z (inr (inl a)) j])
    simp [N] at this;simpa [*,W,← smul_neg,(Matrix.ext (z <| inl ·) : v * Y=0), -fromRows_mulVec] using! And.intro (r.mulVec a) (((inv_mem hk).2.mul r).neg.mulVec a)
  refine ⟨P.contentIndex 0∘Yᴴ.mulVec,by fun_prop,fun u↦⟨le_iInf (exists_content · |>.elim fun t ⟨r,a,b,f⟩↦.trans_eq (ENNReal.inv_le_inv.2 (md_le_volume (u:=star t) fun x k ↦
    ⟨_,w (x•star r) (by simp [k,a _]),by simp [← b,← star_dotProduct_star,dotProduct_mulVec,star_vecMul,mul_comm]⟩)) (by simp [f])),le_iInf fun _↦measure_mono fun c a i↦?_⟩,fun j ↦
    (lintegral_contentIndex_pow_le c σ 0 _ hV ⟨rfl,card_fin _,by lia⟩).trans
    (Z (by simp;nlinarith))⟩
  have H {v w} (a : v∈intVectors R _) b : star v ⬝ᵥ T.splitGram *ᵥ w∈R :=
    sum_mem fun i _↦mul_mem (isAdelic.1.1 (a i)) (J.mulVec b i)
  obtain ⟨_,⟨a,b⟩,_,⟨c,d⟩,e⟩:=a _ (w _ (single_mem_intVectors i))
  simpa [entrywise,mul_comm] using isAdelic.1.1
    ((e.trans (by simp [mulVec_sub,← inverse_star_unit,G];grind)).symm.subst (sub_mem (add_mem (H a d) (H b c)) (mul_mem G.2.1 (H b d))))
  exacts [(by grind [R.mul_mem · ·]),by simp_all [pow_succ'],⟨by simp,by constructor <;> exact (by simpa [*] using isAdelic.1.1 ·)⟩,by simp [pow_mem hα],by simp_all [h.integral_data.1.isUnit_det_and_isIntMatrix_inv.2 _],(isCompact_O.preimage_smul <|
    α ^ ·),by lia,by simp [ENNReal.div_eq_top],by simp [*,G.1 _],by
    simp_all [h.box_eq,unitaryLevel,mem_intGL, -Sum.forall],by simp_all [h.box_eq],fun j u k ↦
    (L j).trans' (by simpa [mul_comm] using md_le_one (α ^ j * u) k),
    (L · |>.trans (by bound) |> (volume_setOf_mul_mem _).trans_le),
    fun σ _ j k n↦(quadricMeasure_cone_le c k _).trans (Z (by nlinarith))]
lemma jm (hg : g.1∈R∧star g.1=g) (a : Fin 𝔰.ϱ) {S} (hS : S≤unipotentBelow a) : heisenbergMeasure a {y | ∃ u∈S,u * (y * 1)∈unitaryLevel R g T.splitGram}=F.floorModulus a g:=by
  rw [heisenbergMeasure,dite_eq_left a.2,map_apply (by fun_prop) measurableSet_exists_mul_mem_level,(Set.ext fun p↦?_ : _ ⁻¹' _=Set.univ.pi (fun _↦{x | g⁻¹.1 * x∈R}) ×ˢ _),prod_prod,skewMeasure_setOf_mul_mem g⁻¹ (by simp [← inverse_star_unit, *])];simp [volume_pi_pi,floorModulus,↓card_succ_le_floorOf,ENNReal.inv_rpow];obtain ⟨w,e⟩:=MulAction.surjective g (inclMatrix A Subtype.val *ᵥ p.1);rw [Set.mem_prod,show p.1∈_↔g⁻¹.1•g•w∈intVectors R _ by simp [e,inclMatrix_val_mulVec,dite_mem, -inclMatrix]]
  refine ⟨fun ⟨u,b,k⟩↦(h.gauge.mem_vecsOfSize_of_heisenbergElem (i:=0) ⟨u,hS b,(by simpa using! k.2 · _)⟩).elim ?_,(⟨1,S.one_mem,h.integral_data.1.mem_unitaryLevel hg.1 <| ·.elim ?_⟩)⟩ <;> simp +contextual
    (maxDischargeDepth:=19) [-Sum.forall, -sum_sum_type,TraceOne.heisenbergElem,eichlerMap,vecMulVec,Units.smul_def,← mul_assoc,↓← e,hg,mul_right_comm _ _ g.1,sub_eq_add_neg,add_mem_cancel_right,vecMul,mulVec,dotProduct,add_assoc,h.integral_data.1.isIntMatrix _]
lemma jn (hg : g.1∈R∧star g.1=g) j : j ≤ 𝔰.ϱ → ascConv heisenbergMeasure j (SetLike.coe (unitaryLevel R g T.splitGram))=∏ l ∈ .range j,
  F.floorModulus l g:=j.rec (by simp) fun j i a↦by rw [Finset.prod_range_succ,← i (by lia),← jm hg ⟨j,a⟩ le_rfl,← ascConv_mconv_unfolding];simp
lemma jo {c} {θ : Measure T.G} [SFinite θ] (hg : g.1∈R∧star g.1=g) : (ascConv heisenbergMeasure (𝔰.ϱ + 2) ∗ₘ θ) {y | y * c∈unitaryLevel R g _}=(∏ l ∈ .range 𝔰.ϱ,F.floorModulus l g) * θ {y | ∃ u∈T.besselU,u * (y * c)∈unitaryLevel R g
  _}:=by simp [↓ascConv_mconv_unfolding,unipotentBelow_eq_besselU,h.jn hg]
lemma groupMeasure_boxSet_le : F.groupMeasure F.boxSet ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n) :=
  h.zeta_rank.1.trans' (.trans (by simpa [h.box_eq,floorModulus,IsNear,stackMeasure_zero_eq] using (h.jo (g:=1) (c:=1) (by simp)).le) (F.upperMeasure_isNear_le (h.gauge.floorMassLe_one · (Gauge.hasFibreBound_floorQuadric_of_le (quadricMeasure_cone_le (le_two_of_pow_le_ofReal h.zeta_rank.1) (by simp) (1 ^ _))) ·
  |>.trans_eq (by simp [volume_O])) 0 1))
instance isHaarMeasure_groupMeasure : F.groupMeasure.IsHaarMeasure:=h.unimodular.elim fun ν ⟨_,
  _⟩↦(exists_eq_smul_haar ν F.isMulRightInvariant_groupMeasure).elim fun d e↦e ▸ .smul _ (by
  simp [·,stackMeasure_ne_zero] at e) (by simpa [e,·,h.box_eq,unitaryLevel_open_compact.1.measure_ne_zero ν] using h.groupMeasure_boxSet_le)
end IntegralPlace.IsStdLevel
end
noncomputable section
open Finset Subgroup ENNReal InnerProductSpace Level Matrix MeasureTheory IntegralPlace Place QuotientGroup SemilocalField Set Size MeasureTheory.Measure Measure ComplexOrder Function Filter
attribute [local simp] div_eq_top mul_eq_top mul_mem indicator Units.smul_def weylRatio intVectors le_of_lt mul_assoc mul_pow genIndex_pos prod_mem
variable {A ι} {𝔰 : Shape} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype ι] {m} {T : 𝔰.Form A} [IsHermUnit T.splitGram] {F : Level ι T (m + 1)} {x y u k : T.G} {g : Aˣ} {u' : T.G} {g' : Aˣ}
def IntegralPlace.phase g z:=if h : ∃ u∈T.besselU,u⁻¹ * z∈unitaryLevel R g _ then P.ψ (g⁻¹.1 * simpleRootSum h.choose) else 0
section
omit [IsHermUnit T.splitGram]
lemma IntegralPlace.jp : phase g y≠0→∃ u∈besselU,u⁻¹ * y∈unitaryLevel R g _:=Not.imp_symm (dite_eq_right ·)
lemma IntegralPlace.jq : ‖phase g y‖ ≤ 1:=by fun_cases phase <;> simp
lemma IntegralPlace.phase_eq (hu : u∈besselU) (e : u⁻¹ * y∈unitaryLevel R g _) : phase g y=P.ψ (g⁻¹.1 * simpleRootSum u):=by
  rw [phase,dite_eq_left ⟨u,hu,e⟩];generalize_proofs k;have:=k.choose_spec
  rw [← mul_one (P.ψ _),← (self_dual _).2 (inv_mul_simpleRootSum_mem (div_mem this.2 e)) 1 (one_mem _),one_mul,← P.ψ.map_add_eq_mul,← mul_add,← simpleRootSum_mul] <;> simp [*]
lemma IntegralPlace.jr (hx : x∈besselS) (hu : u∈besselU) (f : u⁻¹ * x∈unitaryLevel R g _) : phase g (x * y) = ψ (g⁻¹ * simpleRootSum u) * phase g y:=by
  fun_cases phase g y <;> rename_i H
  · rw [phase_eq (mul_mem ((besselS_le_normalizer_besselU hx _).1 H.choose_spec.1) hu) (by
      simpa using mul_mem f H.choose_spec.2),← P.ψ.map_add_eq_mul]
    grind -ac [simpleRootSum_mul,mul_mem,inv_mem,inv_mul_cancel_left,mem_unitriGroup_of_mem_besselU]
  rw [phase,mul_zero,dite_eq_right fun ⟨v,hv,q⟩↦H ⟨_,(besselS_le_normalizer_besselU (inv_mem hx) _).1 (mul_mem hv (inv_mem hu)),by simpa using mul_mem (inv_mem f) q⟩]
lemma IntegralPlace.js (hk : k∈unitaryLevel R g _) : phase g (y * k) =
  phase g y:=by simp [phase,← mul_assoc,mul_mem_cancel_right hk]
lemma IntegralPlace.jt (hu : u∈besselU) : phase g (u * y) = ψ (g⁻¹ * simpleRootSum u) * phase g y:=jr (mem_unitriGroup_of_mem_besselU hu) hu (by simp)
@[fun_prop] lemma IntegralPlace.continuous_phase : Continuous (phase (T:=T) g):=(isLocallyConstant_of_eventually_mul (.mono (unitaryLevel_open_compact.1.mem_nhds (one_mem _)) fun _ k _↦js k)).continuous
lemma IntegralPlace.ju : unitaryLevel R g T.splitGram≤unitaryLevel R 1 _:=fun _↦(unitaryLevel_one.ge ·.1)
end
abbrev Level.IntermediateGroup (F : Level ι T (m + 1)) := ↥(Icc F.congGroup (unitaryLevel R 1 _))
abbrev Level.jv (F : Level ι T (m + 1)):=∏ l ∈ .range 𝔰.ϱ,F.floorModulus l
variable (F) in
def Level.jw (Z : Subgroup T.G):=∫⁻ x,‖∫ y in Z,phase F.g (y * x * y⁻¹) ∂F.groupMeasure‖ₑ ^ 2 ∂F.groupMeasure
def Level.IntermediateGroup.Cosets (Z : F.IntermediateGroup):=Quotient (rightRel (F.congGroup.subgroupOf Z))
instance (Z : F.IntermediateGroup) : Fintype Z.Cosets := @fintypeQuotientRightRel _ _ _ (fintypeOfIndexNeZero (unitaryLevel_open_compact.2.relIndex_ne_zero unitaryLevel_open_compact.1 <|
  relIndex_eq_zero_of_le_right Z.2.2 ·))
def Level.IntermediateGroup.massRatio (Z : F.IntermediateGroup):=F.groupMeasure Z * F.groupMeasure F.congGroup / F.jv ^ 2
def Level.IntermediateGroup.besselVector (Z : F.IntermediateGroup) (y : T.G) : EuclideanSpace ℂ Z.Cosets := .toLp 2 fun c↦phase F.g (y * c.out.1⁻¹)
@[simp] lemma Level.unipotentMass_ne_zero_and_ne_top : F.jv≠0 ∧
  F.jv ≠ ∞:=by simp [jv,floorModulus,prod_eq_zero_iff,prod_ne_top]
lemma Level.jx (Z : F.IntermediateGroup) (e : ⟪Z.besselVector x,Z.besselVector y⟫_ℂ≠0) : ∃ u∈besselU,∃ v∈besselU,u * x∈unitaryLevel R 1 _ ∧
  (u * x)⁻¹ * (v * y)∈F.congGroup:=have ⟨c,_,f⟩:=exists_ne_zero_of_sum_ne_zero e
  have ⟨⟨v,q,f⟩,u,p,g⟩:=(mul_ne_zero_iff.1 f).imp jp
    (jp∘star_ne_zero.1)
  ⟨_,inv_mem p,_,
    inv_mem q,by simpa using mul_mem (ju g) (Z.2.2 c.out.2),
    by simpa using unitaryLevel_one_le_normalizer (Z.2.2 c.out⁻¹.2) (mul_mem (inv_mem g) f)⟩
lemma Level.IntermediateGroup.isOpen (Z : F.IntermediateGroup) : Z.1.IsOpen:=isOpen_mono Z.2.1 unitaryLevel_open_compact.1
variable (Z : F.IntermediateGroup) [h : IsStdLevel F] {j K : ℕ} (r t) {p q : ℕ→Aˣ} {ξ : Aˣ} {Γ : Gauge F} (hj : j ≤ 𝔰.ϱ) (hr : r + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) (ht : t + 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.k)
lemma Level.IntermediateGroup.jy {F : Level ι T (m + 1)} (Z : F.IntermediateGroup) (a : y∈Z.1) : ∃ d,∀ c : Z.Cosets,y * c.out.1⁻¹ ∈ F.congGroup↔c=d:=⟨⟦⟨y,a⟩⟧,fun _↦.symm (.trans Quotient.eq_mk_iff_out rightRel_apply)⟩
lemma IntegralPlace.jz (u : Aˣ) : (P.md u)⁻¹ =
  .ofReal √(_root_.genIndex u.1) ^ 2:=by simp [md_eq_inv_genIndex,← ofReal_pow]
namespace IntegralPlace.IsStdLevel
lemma z0 {S} (e : S≤unitaryLevel R 1 T.splitGram) : F.groupMeasure S ≠ ∞:=(measure_lt_top_mono e (isHaarMeasure_groupMeasure.1.1 unitaryLevel_open_compact.2)).ne
lemma s20_z1 : Z.massRatio≠0∧Z.massRatio ≠ ∞:=by simp [IntermediateGroup.massRatio,z0,Z.2.2,ju,Z.isOpen,unitaryLevel_open_compact,IsOpen.measure_ne_zero]
lemma z2 : ∫⁻ x in F.congGroup,‖∫ y in Z,phase F.g (y * x * y⁻¹) ∂F.groupMeasure‖ₑ ^ 2 ∂F.groupMeasure=F.groupMeasure Z ^ 2 * F.groupMeasure F.congGroup:=by rw [setLIntegral_congr_fun measurableSet_unitaryLevel fun x e↦by rw [setIntegral_congr_fun Z.isOpen.measurableSet fun y a↦phase_eq (one_mem _) (by simpa using unitaryLevel_one_le_normalizer (Z.2.2 a) e)]];simp [Measure.real,← ofReal_norm,z0 Z.2.2]
lemma s20_z3 : F.IsCut Z.besselVector :=
  ⟨⟨⟨by fun_prop [IntermediateGroup.besselVector],_,fun x↦by
    grw [EuclideanSpace.norm_eq,IntermediateGroup.besselVector,jq]⟩,by simp_all
  [IntermediateGroup.besselVector,jt,PiLp.ext_iff]⟩,fun e↦(jx Z (inner_self_ne_zero.2 e)).imp (by simp_all [h.box_eq])⟩
lemma s20_z4 y x : F.jv.toReal * ⟪Z.besselVector y,Z.besselVector (y * x)⟫_ℂ=∫ u,indicator Z (fun z↦phase F.g (z * x * z⁻¹)) (u * y) ∂ascConv heisenbergMeasure (𝔰.ϱ + 2):=by
  have A c:=by simpa only [mconv_dirac_one] using h.jo (θ := dirac 1) (c:=c) h.integral_data.2.2
  rw [integral_congr_ae (g:=fun u↦∑ c : Z.Cosets,{u | u * (y * c.out.1⁻¹)∈F.congGroup}.indicator (fun _↦Z.besselVector (y * x) c * star (Z.besselVector y c)) u) (ae_ascConv_mem_unipotentBelow.mono fun u hu↦?_),integral_finsetSum _ fun c _↦(integrableOn_const ((A _).trans_ne (by simp [-dirac_apply]))).integrable_indicator (measurable_mul_const _ measurableSet_unitaryLevel),PiLp.inner_apply,mul_sum]
  · congr! with c;by_cases e : Z.besselVector y c=0;simp [e]
    erw [integral_indicator_const _ (measurable_mul_const _ measurableSet_unitaryLevel),Measure.real,A,dirac_apply_of_mem (by exact (jp e).imp' (·⁻¹) (by simp)),mul_one];rfl
  by_cases! a : u * y∉Z.1
  · exact (ite_eq_right a).trans (Fintype.sum_eq_zero _ fun c↦ite_eq_right fun b↦a (by simpa using mul_mem (Z.2.1 b) c.out.2)).symm
  obtain ⟨⟨d,e⟩,i⟩:=Z.jy a,inv_mem (unipotentBelow_le_besselU hu);have:=(jt (y:=u * y * x * (u * y)⁻¹ * _) i).trans congr(_ * $(js ((e d).2 rfl)));simp at e this;simp [IntermediateGroup.besselVector,phase_eq i ((e d).2 rfl),mul_left_comm (ψ _),Complex.mul_conj', *]
lemma s20_z5 : F.pairingNorm Z.besselVector Z.besselVector * F.jv≤Z.massRatio:=by
  have β x y:=congr(‖$(s20_z4 Z x (x⁻¹ * y))‖ₑ).trans_le
    ((enorm_integral_le_lintegral_enorm _).trans ((lintegral_indicator_one_le {u | u * x∈Z.1}).trans' (lintegral_mono_ae (by simp_all [apply_ite,← ofReal_norm,jq]))))
  simp [← ofReal_norm,mul_comm F.jv, -toReal_prod] at β;grw [IntermediateGroup.massRatio,ENNReal.le_div_iff_mul_le (by simp) (by simp),groupMeasure,stackMeasure_zero_eq,mconv_apply_eq_lintegral Z.isOpen.measurableSet,← stackMeasure_zero_eq,Level.pairingNorm,upperMeasure,tsub_zero,mul_right_comm,mul_assoc,lintegral_mul_const_le,← lintegral_mul_const' _ _ (z0 ju),lintegral_mono fun x↦?_]
  refine if a : Z.besselVector x=0 then by simp [a] else
    ((s20_z3 Z).exists_mul_mem_box a).elim fun u b↦?_
  erw [← measure_preimage_mul_right F.groupMeasure (u * x)⁻¹,groupMeasure,stackMeasure_zero_eq,h.jo h.integral_data.2.2];grw [lintegral_mul_const_le,← mul_assoc,← lintegral_indicator_const_le,lintegral_mono fun y↦le_indicator_apply (fun _↦?_) fun n↦?_]
  · grw [← mul_assoc,← mul_pow,← ofReal_norm, β,pow_le_of_le_one bot_le _ two_ne_zero];rfl
    grw [Z.2.2,← mconv_dirac_one (ascConv ..),h.jo (by simp),prob_le_one];simp [floorModulus]
  rw [by_contra fun e↦(jx Z e).elim fun v ⟨c,w,d,_,e⟩ ↦
    n ⟨_,mul_mem (div_mem b.1 c) d,by simpa [div_eq_mul_inv] using unitaryLevel_one_le_normalizer (h.box_eq.2.1.le b.2) e⟩];simp
lemma s20_z6 : ‖∫ y in Z,phase F.g (y * x * y⁻¹) ∂F.groupMeasure‖ₑ = ‖F.upperPairing 0 (translatePairing Z.besselVector Z.besselVector 1) 1 x‖ₑ * F.jv:=by have I:=(integrableOn_of_bounded (h.z0 Z.2.2) (by fun_prop) (.of_forall fun z↦jq (g:=F.g) (y:=z * x * z⁻¹))).integrable_indicator Z.isOpen.measurableSet;rw [← integral_indicator Z.isOpen.measurableSet,groupMeasure,stackMeasure_zero_eq] at *;simp [↓(integral_mconv I).trans (integral_integral_swap (I.comp_measurable measurable_mul)),↓← s20_z4 Z,upperPairing,mul_comm,← ofReal_norm, -toReal_prod]
lemma z7 {B} (hB : 2≤B∧volume (P.R \ P.intUnits)≤B⁻¹) : 2⁻¹ ^ 𝔰.n≤F.groupMeasure (unitaryLevel R 1 T.splitGram):=by
  have hl i l (c : l + i = 𝔰.ϱ) : volume P.intUnits ^ (i + 1)≤F.stackMeasure l (i + 2) F.boxSet :=
    h.box_eq.elim fun v ⟨B,n,_⟩↦by
      have k σ θ [SFinite θ] : σ F.boxSet * θ F.boxSet≤(σ ∗ₘ θ) F.boxSet:=(prod_prod ..).ge.trans
        ((measure_mono fun _↦by simp_all).trans (le_map_apply (by fun_prop) _))
      induction' i with i ih generalizing l
      simpa [descConv,floorMeasure,← c] using (mul_le_mul' n.ge v).trans (k ..)
      have:=by simpa [floorModulus,← B] using h.jm (g:=1) (by simp) ⟨l,by lia⟩ bot_le
      grw [pow_succ,stackMeasure,descConv,← k,← ih _ (by lia),← k,floorMeasure,ite_eq_left (by lia),← k,this,one_mul,mul_one,← le_map_apply (by fun_prop),B,← withDensity_apply_le,← meas_le_lintegral₀ (by fun_prop),restrict_eq_self] <;> rintro _ ⟨d,c,b,rfl⟩
      exacts [inv_mem (h.integral_data.1.mem_unitaryLevel R.one_mem (by simp [IsIntMatrix, IsStarStable.star_mem, ite_mem, sub_mem, IntegralPlace.data_mem, floorWeyl, weylOn, *]; try (split_ifs <;> simp [IsStarStable.star_mem, IntegralPlace.data_mem, *]))),one_le_pow₀ (by simpa using md_le_one _ b)]
  grw [← h.box_eq.2.1,← hl _ _ (zero_add _),← one_sub_inv_two,hB.1,← hB.2,← @volume_O A,le_measure_sdiff,sdiff_sdiff_le]
lemma s20_z8 a {z} y (e : ⟪Z.besselVector x,Z.besselVector z⟫_ℂ≠0) : ∃ c : Aˣ,c.1∈R∧↑c∈F.floorValues a x y∧volume (F.floorValues a x y)≤P.md c:=by
  let X := fromRows x⁻¹.1.1 (F.g⁻¹.1•(x⁻¹.1.1 - (x * y)⁻¹.1.1));let i : 𝔰.BesselIndex := eStar a
  obtain ⟨⟨u,hu, -, -,hx, -⟩,b,t,I,L,l,k⟩:=jx Z e,
    valPair.exists_isPrimitiveMatrix_mul (X:=X) ⟨fromCols x.1 0,by simp [X]⟩ FI.level
  have z c (l : c < a) : b.1.col i (eStar c)=0:=t (by simp [FI.level,i];omega)
  have r w (z : ∀ c < a,w (eStar c)=0) : (b⁻¹.1 *ᵥ w) i=_ :=
    Fintype.sum_eq_single i fun x n↦by
    by_cases l : FI.level x < FI.level i;simp [blockTriangular_inv_of_blockTriangular t l]
    obtain c | c | c:=x <;> simp [FI.level,i] at l n <;> first | omega | rw [z,mul_zero];omega
  let c := Units.mkOfMulEqOne _ _ ((r _ z).symm.trans (congr($b.inv_mul i i).trans (by simp)))
  use c⁻¹,(unitriGroup_mulVec_dual (mem_unitriGroup_of_mem_besselU hu) a.2 z).subst
    (by simpa using! (hx.1.isIntMatrix.mul (N:=x⁻¹.1.1 * b.1) (I <| .inl ·) i i)),⟨_,⟨by simpa [h.box_eq,X,sub_mul, -mul_assoc] using! (I · i),z⟩,rfl⟩,md_inv c ▸
    volume_setOf_mul_mem c▸measure_mono fun _ ⟨w,⟨j,n⟩,e⟩↦e▸(r w n).subst (motive:=(·
    ∈ R)) (by simpa [← inv_eq_left_inv ((L.mul_assoc ..).trans k)] using (l.mulVec (v:=X *ᵥ w) (by simpa [h.box_eq,X] using j) i))
lemma s20_z9 (e : ⟪Z.besselVector x,Z.besselVector y⟫_ℂ≠0) : ∃ u∈besselU,∃ v∈besselU,u * x∈F.boxSet∧v * y∈F.boxSet ∧ Γ.HasMatSize 2 (F.g⁻¹.1•((v * y).1.1 - (u * x).1.1)):=h.box_eq.2.1▸(jx Z e).imp fun u ⟨a,v,b,k,l⟩↦⟨a,v,b,
  k,by simpa using mul_mem k (ju l),fun i j↦mem_ofSize_mono (by
    simpa [mul_sub] using Γ.hasVecSize_ball (h.box_eq.2.2.2.1.ge (k.1.isIntMatrix.mul l.2 · j)) i)⟩
lemma za (hj : j ≤ 𝔰.ϱ) K p q (e : ∃ x,F.formMajorant j p q
  Z.besselVector Z.besselVector x≠0) : ∃ α a b,let Γ := (h.gauge α a b);(Γ.IsHead j p ∧ Γ.IsHead j q∧(j≠0→↑F.g⁻¹ ∈ Γ.ofSize 1))∧(∀ i < j,(p i)⁻¹.1 - (q i)⁻¹.1 ∈ Γ.ofSize 1)∧∀ E,4 *
    E≤K → Γ.Λ ^ E≤(2 / P.md F.g) ^ K * .ofReal (finHeadWeight K j p * finHeadWeight K j q):=by
  obtain ⟨g,c,x,y,⟨σ,hσ,a⟩, τ,hτ,b⟩:=h.integral_data.2.2.1,s20_z3 Z,
    e.imp fun _ e↦(exists_ne_zero_of_ae ae_stackMeasure_mem e).imp fun _ k ↦
    (mul_ne_zero_iff.1 k.2).imp exists_ne_zero_of_pivotModulus exists_ne_zero_of_pivotModulus
  have H p y a b : ∃ β : Aˣ,((β.1∈R∧∀ l≤j,(β / ∏ a ∈ .range l,p a).1∈R)∧∀ i < j,(β / p i).1∈R)∧finHeadWeight K j p=√(_root_.genIndex β.1) ^ K:=have H :=
      (minors_mem_ofSize (p:=p) h.gauge.hasMatSize_box hj ((c.isNear_of_ne_zero b).of_floorGroup_mul hτ) ((c.isNear_of_ne_zero a).of_floorGroup_mul (g:=y) hσ).choose_spec)
    ⟨∏ l ∈ .range (j + 1),∏ a ∈ .range l,p a,suffices _ from ⟨this,fun i l↦by
        simpa [prod_range_succ,div_eq_mul_inv, -Units.coe_prod] using mul_mem (this.2 _ l) (H i l.le)⟩;by simp_all [← prod_erase_eq_div],by clear * - H;induction j <;> simp_all
      [finHeadWeight,prod_range_succ _ (_ + 1),prod_range_succ (M := ℝ),← Units.coe_prod]⟩
  refine (H p y ?_ ?_).elim fun β ⟨u,_⟩↦(H q (y * x) ?_ ?_).elim fun γ ⟨v,_⟩ ↦
    ⟨F.g * star (β * γ) * β * γ, ?_,by simp [star_g];ring, ?_, ?_,fun E _↦?_⟩
  iterate 4 intro;simp_all [← (weylElem_mul_left_comm hτ).2]
  all_goals simp [IsHead, *,div_eq_mul_inv,ENNReal.mul_inv,jz,mul_sub]
  iterate 3 simp_all (maxDischargeDepth:=9) [↓mul_mem,mul_left_comm β.1,mul_left_comm F.g.1,isAdelic.1.1,div_eq_mul_inv,↓sub_mem]
  ring_nf;gcongr <;> first | lia | simp [one_le_genIndex, *]
lemma zb (hj : j ≤ 𝔰.ϱ) (hr : t + 10 ^ 8 * 𝔰.n ^ 4 ≤ 𝔰.k) {α a sα} (hΓ : Γ = gauge α a sα) (H : Γ.IsHead j p ∧ Γ.IsHead j q∧(j≠0→↑F.g⁻¹ ∈ Γ.ofSize 1)) {f : _→_} {e} (hf : ∀ {x},f x≤F.formMajorant j p q Z.besselVector Z.besselVector x) (he : e < 1→∀ x∈F.positions,f x ^ 2≤(e ^ F.volumeExponent) ^ 2 * Γ.selfNormProduct j p q Z.besselVector Z.besselVector x) : F.headDensity j p q * ∫⁻ x,f x ∂F.groupMeasure ≤ min 1 e ^ t * Z.massRatio * Γ.Λ ^ (10 ^ 9 * 𝔰.n ^ 4):=by
  obtain ⟨hk,_,_, ζ,V⟩:=s20_z3 Z,h.zeta_rank,F.card_eq,
    le_two_of_pow_le_ofReal h.zeta_rank.1,by
    simpa [volume_O] using h.gauge.floorMassLe_one ⟨j,by lia⟩ h.gauge.hasFibreBound_floorQuadric
  let D (x : T.G) := (Option.elim · 1 (F.g⁻¹.1•(x.1.1 - 1)).uncurry);grw [← setLIntegral_eq_of_support_subset fun x hx↦?_,← withDensity_apply',← setLIntegral_const F.positions,lintegral_le_idealZeta_mul ζ (V := min 1 e ^ t * Z.massRatio * Γ.Λ ^ (9 * 10 ^ 8 * 𝔰.n ^ 4) * 2 ^ (10 ^ 5 * 𝔰.n ^ 2)) ({x∈F.positions | {ε | ∀ i, ε * D x i∈R}=R.subtype '' ·}) (.of_forall fun x y↦?_), ζ, Γ.two_le_and_pairs_le.1];rotate_left
  obtain ⟨c, -, -, -,E⟩ :=
    inv_surjective.exists.1 (exists_content (p:=D x) (i:=none) isUnit_one)
  have hc:=mul_one c.1▸(E c).2 (by simp) none;obtain ⟨z,I,i,b,l⟩:=isAdelic.1.1 hc,exists_ideal_cardQuot_eq c hc;use I,i,⟨y,b▸ext E⟩
  let ⟨σ,eσ⟩ : ∃ σ, σ ^ (400 * 𝔰.n ^ 2)=P.md c * Γ.Λ ^ ((10 * 𝔰.n + 1) * (99 * 𝔰.n)) :=
    ⟨_,rpow_inv_natCast_pow (by lia) _⟩
  let Γ' := h.gauge (star c * c) (mul_mem z hc)
  grw +useKAbstract [l,b,← md_inv, Γ'.md_le 1 _ (by simp [Γ',z]),pow_le_pow_right₀ (by simp) (by lia : m≤50000 * 𝔰.n ^ 2),withDensity_apply', Γ.lintegral_positions_le Γ' hk hk.1 hj H.2.1 (e:=min (min σ 1) e ^ F.volumeExponent * Γ.Λ ^ (9999 * 𝔰.n)) (sq _).ge (fun x k↦⟨k.1,fun _ _↦by simpa [Γ'] using! mul_mem z (k.2.ge (by simp) (some (_,_)))⟩)
    fun x hx↦?_,min_assoc,pow_le_pow_right_of_le_one' (by simp) (by lia : 400 * 𝔰.n ^ 2 *
    (200000 * 𝔰.n ^ 2) + t≤F.volumeExponent),pow_add,pow_le_pow_left' inf_le_right t,inf_le_left,pow_mul σ,eσ,← s20_z5 Z,← (md_ne_zero_and_ne_top (star c * c)).elim (@ENNReal.mul_div_cancel _ 2)]
  simp [Γ',data_mem];rotate_left;rw [min_def_lt'];split;grw [he (by order) x hx.1,← Γ.one_le_Lambda];simp;grw [hf, Γ.formMajorant_sq_le (σ := min σ 1 ^ 2) hk hk.1 hj H.1 hx.1 V (by bound) hk.isNear_of_ne_zero fun o _ z N N'↦?_, Γ.two_le_and_pairs_le.1];rotate_left;simp [sq] at o;by_contra! n
  choose d hd E V using (s20_z8 Z · x z);let C := ∏ i with j ≤ i.1,d i
  have ⟨hC,u⟩ : C.1∈R∧∀ i,j ≤ i.1→(C / d i).1∈R:=by simp_all [C,← prod_erase_eq_div]
  have w := mul_mem (pow_mem a (10 * 𝔰.n + 1)) (isAdelic.1.1 hC);let Γ' := h.gauge (α ^ _ * star C * C) (mul_mem w hC)
  have K:=hx.2.le (Option.rec (Γ'.zero_one_mem_ofSize _).2 (Prod.rec (Γ'.hasMatSize_sub_one_of_floorValues Γ hj H.1 H.2.1 (fun a c m ↦
    by simpa +arith [Γ',mul_left_comm] using mul_mem hC (mul_mem (isAdelic.1.1 hC) (hΓ ▸ Γ.mul_mem_ofSize (H.2.2 a) m :))) (s20_z9 Z z) N N' fun i l↦⟨_,E i,by simpa [Γ'] using! mul_mem w (u i l)⟩)))
  apply ((md_ne_zero_and_ne_top (C ^ (99 * 𝔰.n * 2))).elim ENNReal.mul_lt_mul_left o).not_ge;simp [C];grw [← V,← n,min_eq_left o.le,prod_const,← pow_mul,← pow_mul,← pow_succ',← pow_le_pow_right_of_le_one' o.le (by grw [card_finset_fin_le];lia : _≤400 * 𝔰.n ^ 2),eσ,← Γ.md_le _ (c⁻¹ * (star C * C) ^ _) (by simpa [hΓ,← pow_mul,mul_left_comm] using K),← map_mul];simp [C,pow_mul,sq];simp_all;obtain ⟨y, -,a⟩:=exists_ne_zero_of_ae ae_stackMeasure_mem (ne_bot_of_le_ne_bot hx hf);obtain ⟨σ, -,a⟩:=exists_ne_zero_of_pivotModulus (left_ne_zero_of_mul a);obtain ⟨u,_,v,_, -,k⟩:=jx Z a;exact h.box_eq.2.2.2.2▸⟨_,⟨σ * y,v⁻¹ * u,by bound,rfl⟩,_,k,by simp⟩
  all_goals ring_nf;clear * - m;gcongr <;> simp
include hj hr in
lemma lintegral_formMajorant_ne_top : ∫⁻ x,
  F.formMajorant j p q Z.besselVector Z.besselVector x ∂F.groupMeasure ≠ ∞:=fun e↦by
  obtain ⟨_,_,_,H, -⟩:=za Z hj 0 p q (by by_contra;simp_all)
  simpa [e,headDensity,prod_eq_zero_iff,s20_z1] using zb Z r hj hr rfl H le_rfl (e:=1) (by simp)
include ht
lemma enorm_floorForm_le {ω} (hK : 10 ^ 10 * 𝔰.n ^ 4≤K) (H : (ω = fun x↦P.ψ (ξ * (T.frameGram x.1.1).diag ⟨j,by lia⟩))∨∃ i,j=i + 1 ∧ ω = 1 ∧ ξ = F.g⁻¹ * ((p i)⁻¹.1 - (q i)⁻¹.1)) : ‖F.floorForm j p q Z.besselVector ω‖ₑ ≤ Z.massRatio * (.ofReal √(_root_.genIndex ξ.1) ^ t * (denomIndex R ξ.1 : ℝ≥0∞)⁻¹ ^ 6 * (2 / P.md F.g) ^ K * .ofReal (finHeadWeight K j p * finHeadWeight K j q)):=by
  obtain ⟨C,n | ⟨α,a,_,D,L,E⟩⟩:=s20_z3 Z,
    not_or_of_imp (za Z hj K p q) <;> have hf {x} : formModulus j p q _ x ω ≤ _:=C.formModulus_le_formMajorant (by bound)
  grw [Level.enorm_floorForm_le];simp_all;set Γ := h.gauge α a _;let β := α ^ (200 * 𝔰.n ^ 2)
  obtain ⟨η,w,u,v,e,i,d⟩ : ∃ η w : Aˣ,w.1∈R ∧ ξ * w.1∈R ∧
    (∀ x∈F.positions,formModulus j p q Z.besselVector x ω ^ 2≤(P.c / P.md η) ^ Fintype.card ι * Γ.selfNormProduct j p q Z.besselVector Z.besselVector x) ∧ ξ * η⁻¹.1∈R ∧
    min 1 (.ofReal √(_root_.genIndex η.1)) ^ 2≤P.md w * md β⁻¹.1:=by
    obtain ⟨i,hi,rfl,e⟩ | rfl:=H.symm
    exact ⟨ξ, β,pow_mem a _,e▸mul_comm β.1 _▸mem_ofSize_mono (Γ.mul_mem_ofSize (D.2.2 (by omega)) (L i hi.ge)),fun _↦(Γ.formModulus_sq_le_of_heads C hj D.1 · hi e),by simp [ENNReal.mul_inv_cancel];bound⟩
    obtain ⟨_,e,_,⟨x,hx,_⟩,he,_,_,_⟩ := ξ.mul_inv,by simpa using valPair ξ.1 β
    let η : Aˣ := ⟨ξ + (e - x * e) * β, ξ⁻¹.1 * x,by grind,by grind⟩
    use η, η⁻¹ * β,by simp [η];grind,by simp [η, β,pow_mem,hx,a],fun z hz ↦
      Γ.formModulus_sq_le_of_char C hj D.1 hz fun z m↦by simp [η,add_mul,P.ψ.map_add_eq_mul,(self_dual (β * z)).2 m _ (sub_mem he (mul_mem hx he))],by
      simpa [η],by grw [min_le_right,← jz,← map_mul];simp
  grw +useKAbstract [Level.enorm_floorForm_le,zb Z (t + 12) hj (by lia) (.refl Γ)
    D hf fun l x hx↦by grw [e x hx,data_mem.2.2.2.1,one_div,jz,pow_right_comm,pow_le_pow_right_of_le_one' l.le (tsub_le_self : F.volumeExponent≤_)],
    mul_assoc (_ * _),← E (2 * 10 ^ 9 * 𝔰.n ^ 4) (by omega),pow_add,pow_mul _ 2 6,d,
    min_le_right,le_mul_of_one_le_left (genIndex_pos η).le (one_le_genIndex i (by
    simp)),← map_mul, η.inv_mul_cancel_right, Γ.md_le _ β⁻¹ (β.3▸R.one_mem),denomIndex,
    ← measure_inter_eq_inv_relIndex_add isCompact_O (isOpen_O.preimage (continuous_const_mul _)) _
    volume_O,← md_le_volume (u:=w) (by simp_all [← mul_assoc])]
  ring_nf;gcongr <;> simp
lemma zc : F.jw Z≤F.groupMeasure Z * F.groupMeasure F.congGroup * (F.groupMeasure Z + volume (P.R \ P.intUnits) ^ (t + 1) * 2⁻¹ ^ 𝔰.n):=by
  let Γ := h.gauge;have H : Γ.IsHead 0 1 := by simp [IsHead, Γ]
  have k := Γ.isPairingKernel_self (s20_z3 Z) 0;let e :=
    min (volume (P.R \ P.intUnits)) 2⁻¹
  have h_meas : MeasurableSet (SetLike.coe F.congGroup):=measurableSet_unitaryLevel;grw [jw,← lintegral_add_compl _ h_meas,z2,(s20_z6 Z).le,k.enorm_upperPairing_le,(mul_pow ..).le];with_unfolding_all grw +useKAbstract [lintegral_mul_const' _ _ (by simp),← lintegral_indicator h_meas.compl,(one_mul (lintegral ..)).ge.trans (zb Z (t + 1 + (𝔰.n + 10 ^ 9 * 𝔰.n ^ 4)) bot_le (by lia) (.refl Γ) ⟨H,H,by simp⟩ (indicator_apply_le ?_) fun _ x hx↦?_),inf_le_right,IntermediateGroup.massRatio,mul_right_comm (e ^ _),mul_assoc,ENNReal.div_mul_cancel (by simp) (by simp),pow_add e,pow_le_pow_left' inf_le_left,pow_le_pow_left' inf_le_right];simp [Γ,pow_add,← mul_pow,ENNReal.inv_mul_cancel];ring_nf;rfl;simp [formMajorant,descConv,sq];by_cases n : x∈F.congGroup;simp_all;have M {y} : F.IsNear 0 y:=⟨y⁻¹,by simp [h.box_eq]⟩
  have C := Γ.pivotModulus_sq_le_of_capped (g:=1) (ε := e) k hx fun _ _ a↦by_contra fun b ↦
    n (h.integral_data.1.mem_unitaryLevel h.integral_data.2.2.1 (by simpa [Γ] using!
    (Γ.hasMatSize_sub_one_of_floorValues Γ bot_le H H (by simp) (s20_z9 Z (by simp_all)) M M fun i l↦(s20_z8 Z i x a).imp fun u k↦⟨k.2.1,by_contra fun m↦b ⟨i,l,k.2.2.trans (le_min (md_le_volume fun r a↦⟨mul_mem k.1 a,fun ⟨_,v,b,e⟩↦m (by simp [Γ];grind [mul_mem a b,Units.mul_inv])⟩)
    ((exists_ideal_cardQuot_eq u k.1).elim fun I ⟨a,b,e⟩↦by simpa [le_inv_iff_le_inv,← e,Nat.two_le_iff,a] using (m <| by simpa [·, Γ] using congr(1 ∈ $b))))⟩⟩)))
  simp_all [descConv,Gauge.selfNormProduct,Level.selfNorm,floorWeight,← pow_mul Γ.Λ]
  grw [C,(by lia : 10000 * _≤1500000 * 𝔰.n ^ 3)] <;> ring_nf <;> simp
end IntegralPlace.IsStdLevel
variable {A ι j : _} {𝔰 : Shape} [SemilocalField A] [StarRing A] {m : _} {T : 𝔰.Form A} (L : Set A) [P : IntegralPlace A] [IsHermUnit T.splitGram] [Fintype ι] {F : Level ι T (m + 1)} (Z : F.IntermediateGroup) (p q : _) [Fintype j] (R : Matrix j j ℂ) (ω : j → ℕ→Aˣ) (e)
def Level.zd l:=(F.headDensity 𝔰.ϱ p 1).toReal•besselCorrelation F.groupMeasure Z.besselVector (weylElem 𝔰.ϱ p * l⁻¹)
def Level.ze:=∫ l in {l | T.frameGram ↑l⁻¹ 𝔰.top 𝔰.top - p 𝔰.ϱ ∈ L}, ⟪zd Z p l,zd Z q l⟫_ℂ ∂F.stackMeasure 𝔰.ϱ 2
def Level.energy := ⨅ (l) (_ : l∈GT 𝔰.ϱ ∧ orbitPoint 𝔰.top l=e),∫⁻ h,∑ x,
  let v p := zd Z (ω p) (h * l) x; .ofReal (star v ⬝ᵥ R *ᵥ v).re ∂F.measureH
variable {L R e} [h : P.IsStdLevel F]
namespace IntegralPlace.IsStdLevel
attribute [local simp] mul_assoc
lemma exists_gauge_isHead : ∃ Γ : Gauge F,∀ j,∀ᶠ r in nhds (![p,q] j), Γ.IsHead 𝔰.ϱ r:=match
    (dense_of_ae P.ae_isUnit).inter_nhds_nonempty (Eventually.all fun j↦((finite_le_nat 𝔰.ϱ).eventually_all.2 fun i _↦isOpen_O.preimage_of_continuous (f:=fun (z,r)↦(star z * z) ^ 1 * (∏ i∈range i,r i)⁻¹.1).eventually_mem (x:=(0, ![p,q] j)) (by simp)).curry_nhds) with
    | ⟨_,⟨α,rfl⟩,e⟩ => ⟨gauge (star α * α) (by simpa using (e 0).self_of_nhds 0),e⟩
lemma zf : ∀ᶠ z in nhds (p,1),z.2∈GT 𝔰.ϱ → ∀ l∈GT 𝔰.ϱ,
    zd Z z.1 (l * z.2)=zd Z p l:=(h.exists_gauge_isHead p 1).elim fun Γ e↦by
  filter_upwards [Γ.isCompact_hasMatSize.eventually_forall_of_forall_eventually (P:=fun z y↦y⁻¹ * weylElem 𝔰.ϱ p * z.2 * (weylElem 𝔰.ϱ z.1)⁻¹ * y∈F.congGroup) fun y _↦unitaryLevel_open_compact.1.preimage_of_continuous.mem_nhds (by simp),continuousAt_fst ((e 0).and ((range 𝔰.ϱ).eventually_all.2 fun j _↦(continuousAt_apply j p).const_mul (p j)⁻¹ ((O.isOpen_units isOpen_O).mem_nhds (by simp))))] with z b ⟨s,d⟩ n l hl
  delta zd besselCorrelation headDensity;congr! 5 with j n _ y
  · simpa [← map_mul] using congr(P.md (p j) * $((md_le_one (_ * _) (d j n).1).antisymm (ENNReal.inv_le_one.1 (P.md_inv _▸md_le_one _ (d j n).2))))
  refine if o : Z.besselVector y=0 then ?_ else congr(_ * star ($(by_contra fun t↦t (PiLp.ext fun c↦.trans ?_ (js (unitaryLevel_one_le_normalizer (Z.2.2 c.out.2) (b y ((Ne.ne_or_ne 0 t).rec (Γ.hasMatSize_of_ne_zero (s20_z3 Z) s ?_ o) (Γ.hasMatSize_of_ne_zero (s20_z3 Z) (e 0).self_of_nhds ?_ o))))))) _)) <;> simp [mul_mem,↓o,IntermediateGroup.besselVector, *]
lemma zg (hi : IsOpen {x : A | IsUnit x}) (hc : ContinuousAt Ring.inverse (1 : A)) {i} [Fintype i] {l : i→_} (o : i) (hl : ∀ θ,l θ ∈ GT 𝔰.ϱ ∧ orbitPoint 𝔰.top (l θ)=e) {n : i→_} (hn : ∀ θ θ',l θ * (l θ')⁻¹ ∈ F.congGroup→n θ = n θ' →
  θ = θ') : let v θ p := zd Z (ω p) (l θ) (n θ)
  ∀ᶠ x in nhds e,∀ k∈besselH ⊓ F.congGroup,∀ y,k *ᵥ y=x →
            F.measureH F.congGroup * ∑ θ,.ofReal (star (v θ) ⬝ᵥ R *ᵥ v θ).re≤energy Z R ω y:=by
  have hH k (e : k∈besselH ⊓ F.congGroup) x : Z.besselVector (k * x)=Z.besselVector x:=by
    simp [IntermediateGroup.besselVector,simpleRootSum_eq_zero_of_mem_besselH,jr (mem_unitriGroup_of_mem_floorGroup e.1) (one_mem _) (by simpa using e.2)]
  obtain ⟨⟨u,hu⟩,he,f,rfl⟩:=h.exists_isotropic,orbitPoint_eq_iff.1 (hl o).2,hl o
  simp_rw [energy,le_iInf_iff,mul_sum,← (hasSum_fintype _).tsum_eq]
  filter_upwards [((isClosedEmbedding_unitary_coe.continuousAt_iff (f:=fun x↦(l o)⁻¹ *
    U.of IsHermUnit.isUnit _ (exists_eichler_orbitPoint_eq hu).fst * l o)).2 (by
    have:=congr($he _).trans (Pi.single_eq_same ..)▸hc;simp [comp_def, -besselFrame_last]
    fun_prop)).trans_eq (by congr with;simp [he]) (Eventually.all fun p↦(zf Z (ω p)).curry_nhds.self_of_nhds),(hi.preimage_of_continuous (f:=(mulVec (l o) · (𝔰.besselFrame 𝔰.top)))).mem_nhds (by simp [he])] with _ r t a ha y rfl z s
  obtain ⟨g,⟨m,q⟩,hz,rfl⟩:=floorGroup_anti 𝔰.ϱ.le_succ ha.1,
    (exists_eichler_orbitPoint_eq (e:=l o *ᵥ a.1.1 *ᵥ y) hu).2,s
  have m:=mul_mem (mul_mem (inv_mem f) (m fun i
    k↦by simpa [orbitPoint, -besselFrame_last,← mul_assoc] using! (floorGroup_apply_besselFrame (mul_mem (mul_mem f g) (inv_mem hz)) (one_mem _) i).trans (ite_eq_left k))) f
  have b θ := unitriGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq (inv_mem hz) (inv_mem (mul_mem (mul_mem (hl θ).1 m) g)) (.symm (orbitPoint_eq_iff.2
    (by push_cast [-coe_units_inv,← mulVec_mulVec,inv_inv,orbitPoint_eq_iff.1 (q (by
      simp_rw [orbitPoint,U.form_mulVec_mulVec]) t)];exact orbitPoint_eq_iff.1 (hl θ).2))))
  rw [tsum_congr fun θ↦by rw [mul_comm,← lintegral_indicator_const measurableSet_unitaryLevel,← F.measureH_spec.2.1 _ (b θ),lintegral_mconv_dirac],
    ← lintegral_tsum (by fun_prop (disch:=exact measurableSet_unitaryLevel))]
  refine lintegral_le_of_ae_imp F.measureH_spec.1 fun k g'↦(_root_.tsum_subtype ..).ge.trans
    ((tsum_congr fun ⟨θ,t⟩↦?_).trans_le (tsum_comp_le_tsum_of_injective (fun a b↦Subtype.ext∘hn _ _ (by simpa using mul_mem (inv_mem a.2) b.2)) _))
  simp_rw [← r _ m _ (hl θ).1,zd,besselCorrelation]
  conv_lhs => simp +singlePass [← integral_mul_left_eq_self _ a]
  simp [weylElem_mul_left_comm, *,← hH _ ⟨mul_mem g' (b θ),t⟩ (l θ * _)]
lemma zh ξ : let φ x := P.ψ (ξ * T.frameGram x.1 𝔰.top 𝔰.top)
  let f l := φ l⁻¹ * ⟪zd Z p l,zd Z q l⟫_ℂ;Integrable f (F.stackMeasure 𝔰.ϱ 2) ∧
  F.floorForm 𝔰.ϱ p q Z.besselVector φ = ∫ l,f l ∂F.stackMeasure 𝔰.ϱ 2 :=
  (h.exists_gauge_isHead p q).rec fun Γ k↦by
  intro ω;have c:=s20_z3 Z;set W:=Z.besselVector
  obtain ⟨hW,_,⟨e,n,b⟩,u,v⟩:=(by fun_prop [IntermediateGroup.besselVector] : Continuous W),
    (by fun_prop [frameGram] : Measurable ω),
    (Γ.isPairingKernel_self c 0).exists_lintegral_le 𝔰.ϱ,by simpa using (k · |>.self_of_nhds)
  have:=hW.measurable
  have E : ProbabilityTheory.IdentDistrib (fun (l,x,y)↦ω l⁻¹ * (⟪W x,W y⟫_ℂ * ⟪W ((weylElem 𝔰.ϱ q * l⁻¹)⁻¹ * y),W ((weylElem 𝔰.ϱ p * l⁻¹)⁻¹ * x)⟫_ℂ)) (fun (k, τ,h, σ,x,y) ↦
    let z := k * τ * (weylElem 𝔰.ϱ p)⁻¹ * y; ω (σ * τ⁻¹) * ⟪W (h * σ * y),W (h * σ * y * x)⟫_ℂ *
      ⟪W (weylRatio 𝔰.ϱ p q * z * x),W z⟫_ℂ) ((F.stackMeasure 𝔰.ϱ 2).prod (F.groupMeasure.prod F.groupMeasure)) (F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod (F.measureH.prod ((F.floorMeasure 𝔰.ϱ).prod (F.groupMeasure.prod (F.stackMeasure 0 𝔰.ϱ)))))) :=
    ⟨by fun_prop,by fun_prop,ext_of_lintegral _ fun φ hφ↦by
    rw [← (measurePreserving_prod_mul_swap ..).2,congrArg F.groupMeasure.prod ((descConv_add _ 2 0).trans (by simp!;rfl))]
    simp (disch:=with_unfolding_all fun_prop) only [mconv,lintegral_map,lintegral_prod_symm',↓lintegral_prod (μ := F.groupMeasure),← floorMeasure_top]
    congr! 6 with x _ y σ hσ h hh
    rw [← stackMeasure_mconv_dirac rfl (inv_mem (mul_mem (unitriGroup_inf_floorGroup_last.ge hh).2 hσ)),lintegral_mconv_dirac,stackMeasure_top,lintegral_mconv_symm (by fun_prop),← floorMeasure_top]
    congr! 2 with τ hτ k hk
    simp [weylRatio, ω,↓← (frameGram_diag_mul (unitriGroup_inf_floorGroup_last.ge hh) _).1.trans (frameGram_diag_mul (unitriGroup_inf_floorGroup_last.ge (inv_mem hk)) (σ * τ⁻¹)).2, *,← (weylElem_mul_left_comm _).2,floorGroup_anti 𝔰.ϱ.le_succ _]⟩
  have J : Integrable _ _:=⟨E.1.aestronglyMeasurable,(lintegral_prod_symm _ E.1.enorm).trans_lt
    ((setLIntegral_eq_of_support_subset fun y z↦by
    have ⟨l,h,n⟩:=exists_ne_zero_of_ae ae_stackMeasure_mem z
    use Γ.hasMatSize_of_ne_zero c u (inv_mem h) ?_ ?_, Γ.hasMatSize_of_ne_zero c v
      (inv_mem h) ?_ ?_ <;> contrapose! n <;> simp [↓n]).ge.trans_lt ((lintegral_mono fun _↦by
    simpa [ω,descConv,n.ne,← ofReal_norm,lintegral_const_mul'] using mul_le_mul_right (b ..)
      _).trans_lt ((Γ.isCompact_hasMatSize.prod Γ.isCompact_hasMatSize).integrableOn fun (x,y)↦⟪W x,W y⟫_ℂ * e.toReal).2))⟩
  refine (fun H↦⟨(J.integral_prod_left.const_mul _).congr H,integral_congr_ae H▸((integral_const_mul ..).trans (congrArg _ ?_)).symm⟩) (ae_stackMeasure_mem.mono fun l h↦?_)
  · simp [Γ.inner_besselCorrelation c, *,W,zd,headDensity,mul_rpow_of_nonneg,mul_pow];ring
  rw [← integral_prod _ J,E.integral_eq,E.integrable_iff] at *
  iterate 4 rw [integral_prod_symm _ J];replace J:=J.integral_prod_right
  simp [← integral_conj,formIntegrand,formIntegrandOne,upperPairing,descConv,mul_left_comm (ω _)]
lemma zi (o : IsOpen L) (hR : R.PosSemidef) {t} (ht : ∀ p, ω p 𝔰.ϱ = t) :
    let Q := ∑ p,∑ q,R p q * ze L Z (ω p) (ω q)
    0≤Q∧∫⁻ e,{e | (T.splitGram *ᵥ e) (𝔰.besselFrame 𝔰.top) - t∈L}.indicator (energy Z R ω) e
      ∂F.floorQuadric 𝔰.top ≤ .ofReal Q.re:=by
  obtain ⟨_,r,_⟩:=(s20_z3 Z).stronglyMeasurable,hR.dotProduct_mulVec_nonneg,by
    simpa using (zh Z · · 0 |>.1.restrict (s:=·))
  have e (v : j→EuclideanSpace ℂ (Z.Cosets × Z.Cosets)) : ∑ p,∑ q,R p q * ⟪v p,v q⟫_ℂ=∑ x,
    star (v · x) ⬝ᵥ R *ᵥ (v · x):=by simp [inner,entrywise,mul_sum, @Finset.sum_comm _ _ (_ × _),mul_comm]
  have p {l}:=(e l).trans_ge (sum_nonneg fun _ _↦r _)
  simp (disch:=fun_prop) only [ze,ht,← integral_const_mul,← integral_finsetSum]
  grw (transparency:=default) [and_iff_right (integral_nonneg fun _↦p),← RCLike.re_to_complex,← integral_re,ofReal_integral_eq_lintegral_ofReal (.re ?_) (.of_forall fun _↦p.1),← (measurePreserving_orbitPoint ..).2,lintegral_map_le,← lintegral_indicator_le,stackMeasure_top,lintegral_mconv_symm (.indicator ?_ (o.preimage_of_continuous ?_).measurableSet)] <;> try fun_prop [frameGram,zd,besselCorrelation]
  refine lintegral_le_of_ae_imp ae_floorMeasure_mem fun x a↦indicator_apply_le' (fun k↦iInf₂_le_of_le x ⟨a,rfl⟩ (lintegral_le_of_ae_imp F.measureH_spec.1 fun y s↦?_)) (by simp)
  rw [indicator_of_mem
    (by rw [Set.mem_preimage,← (frameGram_diag_mul (unitriGroup_inf_floorGroup_last.ge s) _).2];simpa [orbitPoint, -besselFrame_last] using! k),e]
  simp [ofReal_sum_of_nonneg fun _ _↦(r _).1]
lemma zj (L : OpenAddSubgroup A) : Continuous (ze L Z).uncurry :=
  .of_at fun x↦tendsto_const_nhds.congr' (by
  have A p:=(Continuous.prodMk_left 1).continuousAt (zf Z p)
  filter_upwards [prod_mem_nhds (A _) (A _),(L.2.preimage_of_continuous (f:=((x.1 𝔰.ϱ).1 - ·.1 𝔰.ϱ))).mem_nhds (by simp)] with _ a (d : _∈L)
  simpa [uncurry,ze,← add_mem_cancel_right (y:=_ - _) d] using integral_congr_ae (ae_restrict_of_ae (ae_stackMeasure_mem.mono (by simp_all))))
end IntegralPlace.IsStdLevel
end
section
namespace Filling
open NumberField ENNReal Finset Fintype MeasureTheory Measure Real AddSubgroup Matrix ComplexOrder SemilocalField Complex
variable {E} [Field E] [CMType E] {𝔰} (S : Filling E 𝔰) (T : Finset (FinPlace E))
noncomputable def qe : AddChar (LocProd T) ℂ:=S.selfDualChar.compAddMonoidHom (adeleOfLocal T)
lemma qf {x} (h : x∈integralOff T) : S.qe T (evalPlaces T x)=S.selfDualChar x := .symm (eq_of_div_eq_one (S.selfDualChar.map_sub_eq_div .. ▸ S.selfDualChar_eq_one_of_mem _ ((sub_adeleOfLocal_mem_iff T).2 h)))
noncomputable def qg (ξ : LocProd T):=√(genIndex ξ) ^ (𝔰.k - 𝔰.n ^ 7) / denomIndex O ξ ^ 6 * S.b ^ (𝔰.n ^ 9 * numInfPlaces E)
noncomputable def qh (l : _ → ℂ) t:=(fun v↦l v * Φ v t,ratToPlaces T t)
attribute [local simp] frameScaleSq qh unitOrOne intVectors funext_iff wave IsUnit.map prod_eq_zero_iff entrywise pi_pos Prod.isUnit_iff Pi.isUnit_iff toAdele Units.val_inj padTuple selfDualChar stdAddChar mul_mem mul_sum
lemma qi [WeilData E] B k X (c : _ → ℂ) (x : _ → ℝ) (hB : 1≤B) (hx : ∀ v,‖c v‖⁻¹ ≤ |x v| ∧
  |x v| ≤ B) (h : ∀ y∈X,y≠0∧y∈ratIntegralOff T) : ∑ y∈X,(∏ v,dampedPower k ‖c v * Φ v y‖⁻¹) * (√(genIndex (ratToPlaces T y)) ^ k / denomIndex O (ratToPlaces T y) ^ 6) ≤
  (∏ v, |x v| ^ k * (S.b * B ^ 2) ^ 3) * (S.b * rootDiscr E) ^ (numInfPlaces E * 3):=by
  obtain ⟨Z,_,b⟩:=by simpa using tsum_sublatticeDisc_inv_le (1 : Gf E (Fin 2)) 1,
    rootDiscr_pos E,S.thousand_le_b
  simp_rw [dampedPower,norm_mul,mul_inv];grw [← b,← show 200 * (numInfPlaces E * 2)≤S.b by
    bound [S.f_le_b],← ofReal_le_ofReal_iff,ENNReal.ofReal_mul,← Z,← ENNReal.sum_le_tsum
    (X.image (colSpan !![1;·])),sum_image fun y _ u _ e↦(e.le ⟨1,rfl⟩).elim (by
    simp +contextual),mul_sum,ofReal_sum_of_nonneg,sum_le_sum fun y hy↦?_]
  obtain ⟨⟨a,e,p, -⟩,u,w,f⟩:=exists_preimageLattice_eq_colLattice (m:=finAdeleMat !![1;y])
    ⟨!![1,0],by simp [vecMul]⟩,(denomIndex_ne_zero T _).pos,h y hy,show 1 = !![1;y].rank by
    simp [rank_eq_finrank_span_cols,finrank_span_eq_card]
  have : 0 < genIndex a.1.det:=genIndex_pos a.det
  obtain ⟨D,_, -⟩:=sublatticeDisc_mul_index_sq_le (one_mul 1) _ !![,,] f le_rfl a (K := ⊤) (D:=((∏ v,(1 + ‖Φ v y‖ ^ 2)) * genIndex a.1.det) ^ 2)
    (by erw [det_unique,genIndex_algebraMap];simp [abs_norm_eq_prod_norm_sq,conj_mul',mul_pow,← prod_pow];norm_cast;simp) (by positivity) (.mul .one p) (by simp)
  simp [submoduleIndex, -det_unique] at D;grw [ite_eq_left (by tauto),le_of_sq_le_sq D,← ENNReal.ofReal_mul,sqrt_genIndex_le_prod_norm T w,← pow_le_pow_right₀ (mod_cast u) (by simp : 3≤6),← (?_ : genIndex a.1.det≤denomIndex ..),fun v↦(?_ : min 1 (‖c v‖⁻¹ * _) ^ 6≤(1000 * B ^ 2 / (1 + ‖Φ v y‖ ^ 2)) ^ 3),(hx _).1]
  any_goals intros;positivity
  · gcongr 1;simp [field,prod_pow,div_pow,mul_pow, *]
  · grw [pow_mul _ 2 3,(hx v).1,(hx v).2,min_def];gcongr
    clear * - w hB;split <;> simp [*,field] at * <;> nlinarith [norm_nonneg (Φ v y)]
  grw [← submoduleIndex_colLattice_div,div_nat_le_self_of_nonneg (by simp),← e,Nat.cast_le]
  exact Nat.le_of_dvd u ((relIndex_dvd_of_le_left _ fun z↦by simp_all [preimageLattice,mem_Ô_iff T, -e]).trans (dvd_of_eq ((inf_relIndex_right ..).trans ((relIndex_comap _ (.mk' (evalPlaces T <| · 0) (by simp)) _).trans (congrArg _ (by ext;simp [locProd_O_eq_map_evalPlaces,Fin.exists_fin_succ_pi]))))))
variable [S.IsAdmissible] {A : Finset Eˣ} (hA : ∀ t∈A,↑t∈ratIntegralOff T∧↑t⁻¹ ∈ ratIntegralOff T) (hg : (↑S.g)⁻¹ ∈ ratIntegralOff T)
include hA hg
lemma qj {n J En Λ β} (K : SieveSystem (.map (unitOrOne∘·) unitOrOne) (.map ((·⁻¹.1)∘·) (ratToPlaces T S.g⁻¹ * ·⁻¹.1)) n J (fun x↦(∏ v,wave (x.1 v)) * S.qe T x.2) En Λ β) {Γ ε} (hP : ∀ a (c : _ → ℂ),(∀ v,‖c v‖⁻¹ ≤ |S.kappa v| / S.g)→∀ X,(∀ y∈X,y≠0∧y∈ratIntegralOff T)→∑ y∈X, β (qh T (fun v↦c v / S.frameScaleSq v a) y) ≤ ε) (hε : 0 ≤ ε) (hΛ : ∀ i p,0 ≤
  Λ i p) : let hd i (p : Fin i→A) t a := .map (unitOrOne∘·) unitOrOne (qh T (S.frameScaleSq · a) (padTuple (p · |>.1) t a).1)
  let c a := volÔ E / ∏ v,S.frameScaleSq v a ^ 2
  (∀ i≤n,(∑ p, Λ i (hd i p 1)) ^ 2 ≤ Γ * ∏ a∈range i,c a)→∀ i≤n,∀ V⊆A,
  (∑ t∈V,∑ p,∑ q,J (i + 1) (hd i p t) (hd i q t)).re ≤
    (∏ a∈range (i + 1),c a) * (En + (2 * i + 1) * Γ * ε):=by
  intro hd c hΓ
  refine Nat.strongRec fun i ih hi V hV↦?_
  have:=K.q4 hi (hd i · 1)
  extract_lets F at *
  obtain ⟨⟨N,L⟩,o,⟨hF,e,hM⟩,c0,d⟩:=show 0≤F∧_ from K.q5 hi
    _ fun _ _↦dite_eq_left rfl,(isOpen_univ.prod (isOpen_integralOff T) : @IsOpen (𝔸 E) _ _),this,
    (by positivity : 0≤c i),LinearMap.det_pi (S.frameScaleSq · i•(1 : ℂ →ₗ[ℝ] ℂ))
  set U := _ ×ˢ _;let m (z : 𝔸 E) := (fun v↦S.frameScaleSq v i * z.1 v,evalPlaces T z.2)
  have P : MeasurePreserving m (volume.restrict U) (ENNReal.ofReal (c i)•volume):=by simpa [d,U,volume_eq_prod,← prod_restrict,prod_smul_left,prod_smul_right,abs_prod,div_eq_mul_inv,c,mul_smul, -frameScaleSq] using! MeasurePreserving.prod ⟨by fun_prop,map_linearMap_addHaar_eq_smul_addHaar _ (d.trans_ne (by simp))⟩ ⟨by fun_prop,map_evalPlaces_restrict_volume T⟩
  have I:=U.indicator_nonneg fun x _↦(N (m x)).1
  refine (le_of_eq_of_le ?_ (IsDualFamily.sum_le_of_fourier ((integrable_indicator_iff o.measurableSet).2 (P.integrable_comp_of_integrable hF.re.smul_measure_nnreal)) I (V.map ⟨(⟨_,·.1,rfl⟩),fun _↦by simp⟩) (forall_mem_map.2 fun t h↦.of_frequently fun y k↦(ite_eq_left ⟨trivial,(hA t (hV h)).1⟩).trans_le ((ofReal_le_ofReal_iff (k.exists.elim (I · |>.trans))).1 (((L _ fun _↦continuousAt_const.update _ (.prodMap (.piMap fun v↦continuousAt_unitOrOne (.mk0 _ (by simp [m]))) (continuousAt_unitOrOne (t.map (ratToPlaces T).1)))).comp (g:=m) (by fun_prop)).frequently _
    (k.mp (.mono (o.eventually_mem ⟨trivial,(hA t (hV h)).1⟩) (by simp +contextual [F,ofReal_le_ofReal])))))) ((reindex_equiv (Equiv.divRight₀ _ S.varpi_ne_zero).finsetCongr).1.2 fun Y↦?_))).trans (?_ : c i * (‖∫ x,F x‖ + ε * (∑ p, Λ i (hd i p 1)) ^ 2)≤_)
  simp +contextual [m,U,F,← Subring.mem_comap,hA _ (hV _)]
  congr! <;> simp +contextual [hd,↓Function.eq_update_iff]
  · erw [sum_map]
    grw [Y.insert_erase_subset 0,sum_insert (by simp),← sum_filter_of_ne (p:=(· ∈ ratIntegralOff T)),← hP i (2 * π * .I / Φ · S.ϖ) (by simp [abs_kappa_eq,field,abs_of_pos]),mul_add,sum_mul,mul_sum]
    · gcongr with y h;any_goals simp at h;grw [← hM _ (by simp [h])]
      all_goals grw [← norm_smul_of_nonneg c0,← toReal_ofReal c0,← integral_smul_measure,← P.hasLaw.integral_comp (by cases hF;simp [qe,c];fun_prop),← integral_indicator o.measurableSet];simp [m,U,← eq_re_of_ofReal_le (N _),Set.indicator,apply_ite,↓sub_conj,← Complex.exp_sum,div_eq_mul_inv, -neg_sub, -frameScaleSq]
      congr! 8;field;erw [S.qf T (mul_mem h.2 ‹_›)];simp;ac_rfl
    simp +contextual
    refine fun y _ n↦(sub_adeleOfLocal_mem_iff T).1 ((S.forall_selfDualChar_mul_eq_one_iff _).1 fun ⟨r,hr⟩↦(mul_eq_right₀ (norm_ne_zero_iff.1 n)).1 (.trans ?_ (integral_add_left_eq_self _ (0,r - adeleOfLocal T (evalPlaces T r)))))
    rw [← integral_const_mul];congr with;simp [Set.indicator,U,m,add_mem_cancel_left,sub_mem,(mem_Ô_iff T).1 hr,mul_add,AddChar.map_add_eq_mul,div_eq_mul_inv, -frameScaleSq]
    simp_rw [adeleOfLocal_evalPlaces];ring_nf!
  grw [← re_eq_norm.2 (integral_nonneg N),e,hΓ,prod_range_succ_comm,mul_assoc]
  gcongr;cases i <;> simp
  grw [re_le_norm,K.norm_bot_le,mul_comm]
  linear_combination (norm:=ring_nf) ih _ .refl (by omega) A le_rfl + ε * hΓ _ hi
  simp [↓sum_mul,reindex_equiv (Fin.snocEquiv _),sum_prod_type,Fin.snocEquiv,sq,←
    sum_add_distrib,← A.sum_attach,show ∀ i p t,hd _ (Fin.snoc p t) 1=hd i p t by
    grind [padTuple,Fin.snoc,Fin.castLT]]
  gcongr with t
  grw [sum_eq_add_sum_sdiff_singleton_of_mem ‹_›,← A.attach.sdiff_subset];gcongr with v
  let y := (S.g : E)⁻¹ * (t.1⁻¹ - v.1⁻¹)
  have : y≠0:=by simp [y];grind
  grw [re_le_norm,add_comm,K.off_diagonal,← hP ‹_› S.g (by grw [← one_le_abs_kappa];simp) {y} (by grind [mul_mem,sub_mem])]
  any_goals rw [show _ - _=qh T (S.g / S.frameScaleSq · ‹_›) y by
    simp [hd,y,field,↓map_sub,↓map_mul,↓map_units_inv]]
  any_goals simp [*]
  all_goals grind [Finset.sum_nonneg,mul_nonneg]
lemma sieve [WeilData E] [T.StarStable] {J' e U} (h' : SieveSystem unitOrOne (ratToPlaces T S.g⁻¹ * ·⁻¹.1) 𝔰.ϱ J' (S.qe T) e (finHeadWeight (𝔰.n ^ 6)) (S.qg T)) (hU : U⊆A) :
  let x v (p : Fin 𝔰.ϱ → A) t i := unitOrOne (S.frameScaleSq v i * Φ v (padTuple (p · |>.1) t i).1)
  let y p t := Units.map (ratToPlaces T)∘padTuple (p · |>.1) t
  (∑ t∈U,∑ p,∑ q,(∏ v,(S.besselSys v).bandLimit 𝔰.n (x v p t) (x v q t)) * J' 𝔰.n (y p t) (y q t)).re≤(∏ i∈range 𝔰.n,volÔ E / ∏ v,S.frameScaleSq v i ^ 2) * ((∏ v,(1 + S.b⁻¹ ^ 10) / (S.besselSys v).deg) * e + S.besselDegree⁻¹ / S.b ^ (6 * 𝔰.k * numInfPlaces E + 10)):=by
  obtain ⟨b,r,_,N,K,Z,h, θ⟩:=S.one_le_b,rootDiscr_pos E,(by simp : S.g≠0).pos,
    S.N_prime.pos,S.one_le_abs_kappa,S.qi T,(S.besselSys · |>.band_limits.1),
    (by simp [Shape.bandConst] : 0 < 𝔰.bandConst)
  unfold headWeight finHeadWeight dampedPower at *
  refine ((S.qj T hA hg (h'.pi h) (fun a c hc X hy↦by
    simp_rw [qg,qh,prod_mul_distrib,mul_assoc,← mul_sum,← mul_assoc,← sum_mul] at *
    grw [Z _ _ _ _ (S.kappa · ^ (2 * 𝔰.ϱ + 1) / (S.g * S.N)) _ (fun v↦⟨by
      simp [div_eq_mul_inv];grw [hc,Nat.sub_le] <;> simp [pow_succ,field,K],by
      grw [abs_div,abs_pow,abs_kappa_le,div_le_self] <;> norm_cast <;> bound⟩) hy];bound)
    (by positivity) (by intros;positivity) (Γ := S.b ^ _) (fun i hi↦by
    let m (p : Fin i→A) j := ∏ a∈range j,(padTuple (p · |>.1) 1 a).1
    have L v a:=(by grw [frameScaleSq,← pow_abs_two_mul,Nat.sub_le,abs_kappa_le,div_le_self] <;> bound : S.frameScaleSq v a≤_)
    beta_reduce
    grw [(.trans ?_ ((prod_univ_sum ..).ge.trans (prod_le_prod₀ (by intros;positivity) fun (j : Fin i) _↦Z (S.N ^ i) (𝔰.n ^ 6) (image (m · j.succ) univ) (∏ a∈range j.succ,S.frameScaleSq
      · a) (fun _↦S.N ^ i) (by bound) (by simp;grw [← K];simp;bound) (by simp [m,hA,prod_mem,apply_dite,dite_eq_iff, -Subring.mem_comap]))) : ∑ p,_≤_),volÔ_eq,abs_of_pos (by bound),N_le,N_le,L,half_le_self,S.rd_le_b]
    simp [field,← pow_mul,← pow_add,mul_pow];grw [hi]
    iterate 3 simp [r, -frameScaleSq,le_of_lt,prod_pos]
    grw [← image_subset_iff.2 fun p h↦mem_piFinset.2 fun _↦mem_image_of_mem _ h,sum_image fun p _ q _ e↦funext fun j↦?_]
    · simp_rw [@prod_range _ _ i, @prod_comm (Fin i),← prod_mul_distrib]
      gcongr 3 <;> simp [m]
      split <;> simp +contextual [denomIndex,relIndex_eq_one.2,IsConcreteLE.le_iff,div_nonneg, *]
    simpa [m,prod_range_succ] using congr($e j / $(@Fin.cases i (fun k↦m p k=m q k) (by bound) (congrFun e) j.castSucc))) 𝔰.ϱ le_rfl U hU).trans_eq' (by congr! <;> ext <;> simp)).trans ?_
  gcongr
  grw [← IsAdmissible.prod_band_le_inv_deg,show _ + 1≤S.b by grw [← k_le_b,← S.ϱ_le_k];grind,
    S.rd_le_b]
  simp [abs_div,field,mul_pow,← pow_mul,← pow_add,← pow_succ',mul_comm _ (∏ _,_),mul_assoc]
  gcongr;grind [Fintype.card_pos,mul_le_mul_right S.pow_le_k (numInfPlaces E)]
end Filling
end
section
open Complex Subgroup Classical ComplexOrder ENNReal Function Matrix MeasureTheory SemilocalField Set Valued
namespace Filling
attribute [-instance] NumberField.IsCMField.of_isAbelianGalois
attribute [-simp] Filter.eventually_atTop splitGram_eq_ite_oppositeIndex coe_units_inv Nat.card_eq_fintype_card Nat.cast_mul Sum.forall Unitary.mul_star_self_of_mem inv_mul_cancel₀ star_ofNat
variable {E} [Field E] [CMType E] {𝔰} (S : Filling E 𝔰) (T : Finset (FinPlace E))
abbrev IsIntegralOff (x : S.GFin):=x.1∈intGL _ (integralOff T)
noncomputable def qk [Side] c s c' γ := ∑' x : besselU .. × besselU ..,ite (S.IsIntegralOff T (S.termPosition c c x.1.1)∧x.1.1 * γ * x.2.1⁻¹ ∈ S.termsOver c s c') (S.amplitude c c' (x.1.1 * γ * x.2.1⁻¹)) 0
variable {𝔰 : Shape} (S : Filling E 𝔰) (T : Finset (FinPlace E)) [T.StarStable] (x : S.GFin)
noncomputable def toPlaces:=U.map (evalPlaces T) (star_evalPlaces T · |>.symm) (S.map_splitGram_latMiddle _)
class IsFillingLevel [P : IntegralPlace (LocProd T)] (F : Level (Fin (𝔰.k - (6 * 𝔰.ϱ + 13)))
  (S.latMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)) : Prop extends P.IsStdLevel F where
  psi_eq : P.ψ = S.qe T
  g_eq : F.g=S.gIdele.map (evalPlaces T)
lemma ql (a : 𝔸f E) : ∀ᶠ T in .atTop,a∈integralOff T:=Filter.eventually_atTop.2 ⟨a.2.toFinset,by simp [integralOff,compl_subset_comm];tauto⟩
lemma qm : ∀ᶠ T in .atTop,
  S.IsIntegralOff T x:=by simp [mem_intGL,ql]
lemma qn (T₀ : Finset Eˣ) : ∃ᶠ T in .atTop,T.StarStable∧(∀ t∈T₀,↑t∈ratIntegralOff T∧↑t⁻¹ ∈ ratIntegralOff T)∧Fact (↑S.gIdele⁻¹ ∈ integralOff T)∧S.latBasis∈intGL _ (integralOff T)∧(S.N : E)⁻¹ ∈ ratIntegralOff T:=(Filter.frequently_atTop.2 fun T↦⟨T ∪ T.image star,by simp,⟨by aesop⟩⟩).and_eventually (by simp [mem_intGL,ql,fact_iff])
variable {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable] {x : S.GFin}
lemma qo {σ p} v : S.ratToInf (weylElem 𝔰.ϱ p * σ) v=weylElem 𝔰.ϱ (fun i ↦
  unitOrOne (S.frameScaleSq v i * Φ v (p i))) * S.ratToInf σ v:=by simp;ext i (_ | (_ | _) | _) <;> simp [weylElem,weylOn,FI.level,basisScale,frameScaleSq,unitOrOne,two_mul,pow_add,Nat.add_sub_assoc] <;> split <;> simp [field,← Complex.ofReal_pow, *]
lemma qp y : ∃ x,S.toPlaces T x=y∧S.IsIntegralOff T x∧(y∈besselU→x∈besselU)∧(y∈besselH →
  x∈besselH) := let f : GL 𝔰.BesselIndex _ →* _ :=
    unitsMapNonUnital ⟨⟨(Matrix.map · (adeleOfLocal T)),by simp⟩,by simp,by aesop⟩
  ⟨⟨f y,have ⟨z,k⟩:=add_left_surjective 1 y.1.1
    by simpa [mem_U,← k,← S.map_splitGram_latMiddle (evalPlaces T),mul_add,add_mul,add_assoc,f,← ext_iff,mul_apply,adeleOfLocal_evalPlaces_mul,adeleOfLocal_star,mul_comm (star _), -Fintype.sum_sum_type] using! congr(Matrix.map $(mem_U.1 y.2) (adeleOfLocal T))⟩,by ext : 3;show evalPlaces T (_ + adeleOfLocal T _)=_;simp,mem_intGL.2
    (by constructor <;> exact IsIntMatrix.one.add fun _ _↦adeleOfLocal_mem_integralOff T _),by
       constructor <;> simpa [mem_besselU,mem_floorGroup,f] using! (congrArg (adeleOfLocal T) <| · · · ·)⟩
lemma qq {u} (h : ↑u⁻¹ ∈ integralOff T) : x∈unitaryLevel (Ô E) u _↔S.IsIntegralOff T x∧S.toPlaces T x∈unitaryLevel O (u.map (evalPlaces T)) _:=by have i (k : x.1∈_):=(k.isIntMatrix.sub .one).smul h;simp [unitaryLevel,mem_intGL,IsIntMatrix,mem_Ô_iff T,Units.smul_def,forall_and] at i ⊢;tauto
lemma qr : x∈S.latStabilizer↔S.IsIntegralOff T x∧S.toPlaces T x ∈
  unitaryLevel O 1 _:=by simp [latStabilizer,← unitaryLevel_one,qq (T:=T)]
lemma qs [WeilData E] (T : Finset _) [T.StarStable] : ∃ _ : IntegralPlace (LocProd T),∃ F,S.IsFillingLevel T F:=by
  obtain ⟨y,a, τ,b,e,s,t⟩ := IsAdelic.exists_skew_unit (A := LocProd T);let B := {b : skewAdjoint (LocProd T) | b.1∈O};let ν := Measure.addHaarMeasure ⟨⟨B,isCompact_O.preimage_val isClosed_skewAdjoint⟩,0,isOpen_O.preimage_val.interior_eq.ge O.zero_mem⟩;let := TraceOne.mk τ t
  have sp:=(map_restrict_addHaar_eq (ν.prod ν) volume (.mk' (fun p↦τ * y * p.1.1 + p.2.1) (by
    simp;grind)) (by measurability) .univ (fun x↦⟨(skewPart (-y * x),skewPart (star τ * x)),by
    simp;grind⟩) isCompact_O.measurableSet (C :=
    B ×ˢ B) (Set.ext fun ⟨a,b⟩↦let x := τ * y * a + b
    by simp;grind [(by simp [x];grind : -y * (x + star x)=a),mul_mem,IsStarStable.star_mem,add_mem_cancel_left])).1
  obtain ⟨n : ν B=1,_⟩:=Measure.addHaarMeasure_self,S.ϱ_le_k;simp [volume_O,n] at sp
  have d a : (∀ r∈O,S.qe T (r * a)=1)↔a∈O := .trans
    (by simp [locProd_O_eq_map_evalPlaces,qe,adeleOfLocal_evalPlaces_mul, -map_mul])
    ((S.forall_selfDualChar_mul_eq_one_iff (adeleOfLocal T a)).trans (by simp [mem_Ô_iff T]))
  choose _ m i using fun x : LocProd T↦(locallyIntegrable_sqrt_inv_norm _ <| x ·)
  let P := IntegralPlace.mk (toPlace := ⟨.mkOfMulEqOne _ _ e, ν,⟨⟨fun x↦(.ofReal (genIndex x))⁻¹,by simp⟩,by simp [↓map_mul,ENNReal.mul_inv,genIndex_eq_inv_prod_norm,Finset.prod_nonneg]⟩,S.qe T,1,continuous_ψf.subtype_val.comp ((continuous_adeleOfLocal T).const_mul
    _),by simp [genIndex_eq_inv_prod_norm];fun_prop,by simp [s],⟨by fun_prop,sp⟩,by
    simp;simp [genIndex_eq_inv_prod_norm],fun _ _ g u↦(map_smul_eq_inv_distribHaarChar_smul
    (GeneralLinearGroup.mk'' g u)).trans (by simp [distribHaarChar_GL_eq_det isOpen_O isCompact_O valPair]),by simpa [Pi.isUnit_iff, -Subtype.forall] using! (Measure.ae_eval_ne _ · _),⟨_,fun
    x↦⟨_,by simp [set_pi_mem_nhds,m],(Integrable.fintype_prod_dep (i x)).mono_measure
    (Measure.restrict_pi_pi ..).le⟩,fun _↦by
    erw [inv_inv,genIndex_eq_inv_prod_norm,← enorm_pow,← Finset.prod_pow,← Finset.prod_inv_distrib];clear * -
    grw [← Real.ofReal_le_enorm];gcongr;grind [Real.sqrt_nonneg]⟩,by simp [qe],
    by
    have q z:=setIntegral_char (ν := volume) (M:=O.toAddSubgroup) isOpen_O (χ := S.qe T∘(star · * z))
    clear * - d q;refine ⟨_,IsClopen.continuous_indicator ⟨isCompact_O.isClosed,isOpen_O⟩ continuous_one, ?_, ?_, ?_,(lintegral_mono ?_).trans ((lintegral_indicator_one_le _).trans_eq volume_O)⟩ <;> simp_all [integrable_indicator_iff,isCompact_O.measurableSet,Pi.one_def,Pi.le_def,Measure.real_def,volume_O,← integral_indicator,indicator_apply,AddChar.map_add_eq_mul,add_mul,apply_ite ofReal,apply_ite enorm] <;> grind [IsStarStable.star_mem,star_star]⟩) ⟨b,neg_mem a,a,rfl,n⟩ d (congrFun rfl)
  have ⟨k,l,h⟩ := exists_orthonormal_Ô (E := E) S.isUnimodular_latMiddle.splitGram;let c := U.conj k h;have t : Continuous c := .subtype_mk (by fun_prop) _;refine ⟨P,.imp (fun F h↦.mk (toIsStdLevel := ⟨h.1,⟨by grw [idealZeta_locProd_le,idealZeta_intAdeles_pow_le _ S.degree_le],by simp;lia⟩,Measure.haar.inv,{ toIsMulLeftInvariant := ?_ },inferInstance⟩) rfl h.2) (P.jl (by simp) (by simp [gIdele_val]) (by simp;omega))⟩
  simpa using (map_restrict_haar_eq (Z:=Gf ..) volume _ ((S.toPlaces T).comp c.toMonoidHom) ((U.continuous_map : Continuous (S.toPlaces T)).comp t).measurable ((isOpen_intGL (isOpen_integralOff T)).preimage_val.preimage t ).measurableSet
    (qp · |>.elim fun g h↦⟨c.symm g,by simp [mul_mem_cancel_left,mul_mem_cancel_right,h]⟩) P.measurableSet_unitaryLevel (C:=Kf E 𝔰.BesselIndex) (Set.ext fun g↦(and_comm.trans qr.symm).trans (le_normalizer l _).symm)).2
attribute [local simp] classBasis coe_termPosition besselLatticeBasis frameGram entrywise toBesselH in
lemma qt {σ} (u :
  σ ∈ GT 𝔰.ϱ) c c' : let L := S.termPosition c c' σ;let φ := algebraMap E (𝔸f E)
    let ω j := σ.1.1 (𝔰.indexX₀ j) 𝔰.z
    let t := S.frameProducts σ 𝔰.top 𝔰.top;L∈GT 𝔰.ϱ ∧ orbitPoint 𝔰.top L⁻¹ = ji S.piBar
      (φ t) (c.out⁻¹.1.1 *ᵥ φ ∘ ω)∧S.N * star ω ⬝ᵥ ω = t * star t - S.N ^ 2∧∀ p,
      S.termPosition c c' (weylElem 𝔰.ϱ p * σ)=weylElem 𝔰.ϱ (Units.map φ ∘ p) * L:=by
  have:=floorGroup_apply u;simp [Sum.forall] at this
  refine ⟨by simp [mem_floorGroup,Sum.forall,this], ?_, ?_, ?_⟩
  · simp [orbitPoint,ji,← mulVec_mulVec, -mulVec_single, -besselLatticeBasis]
    congr;simp [funext_iff,Sum.forall,splitGram,middleGram,mulVec,← piBar_mul_star,← mul_assoc,← star_mul,this]
  · have:=congr(diag $(σ.2) 𝔰.z)
    simp_all [middleGram,splitGram];grind
  simp [Subtype.ext_iff,← mul_assoc,Units.ext_iff,Sum.forall,weylElem,weylOn]
  bound
lemma qu [WeilData E] [S.IsAdmissible] {π : Side} {c s c' Λ} (h : S.amplitudeSum (S.termsOfLink Λ) c s c'≠0) (hs : ∀ γ ∈ S.termsOver c s c',∀ l,leadingMinor (S.frameProducts γ) l≠0) : ∃ (t : Eˣ) (σ : S.G E),∃ k,(σ ∈ GT 𝔰.ϱ ∧ S.frameProducts σ 𝔰.top 𝔰.top=t∧(∀ v,S.N ^ 2 < ‖Φ v t.1‖ ^ 2)∧S.reduction k=s ∧ Λ = link (weylElem 𝔰.ϱ 1 * σ))∧∃ L,HasSum L (S.amplitudeSum (S.termsOfLink Λ) c s c')∧∀ p : Fin 𝔰.ϱ → _,Filter.Tendsto (fun T↦S.qk T c s c' (weylElem 𝔰.ϱ (padTuple p t) * σ)) .atTop (nhds (L p)):=by
  obtain ⟨γ₀,⟨h₀,l⟩,h⟩:=not_isEmpty_iff.1 (h∘by apply @tsum_empty);obtain ⟨v,m,v',n,r, σ,hσ,e⟩:=exists_big_cell_decomp (hs _ h)
  have L p : Λ = link (weylElem 𝔰.ϱ p * σ) :=
    l▸by simp [link_besselU_mul,link_big_cell_eq_iff, *]
  have T := e▸hs _ h ⊤;simp [-sub_eq_zero,frameDisc_frameGram_besselU_mul,↓leadingMinor_frameGram_besselU_mul,↓frameDisc_weylElem_mul hσ,↓frameGram_weylElem_mul hσ,leadingMinor, *] at T h₀;let t := Units.mk0 _ T.2
  let δ (i : (Fin 𝔰.ϱ → _) × besselU × besselU) :=
    i.2.1.1 * (weylElem 𝔰.ϱ (padTuple i.1 t) * σ) * i.2.2.1⁻¹
  have A : HasSum ((S.termsOfLink Λ ∩ S.termsOver c s c').indicator (S.amplitude c c') ∘ δ) _ :=
    (Injective.hasSum_iff (fun _ _↦(by simpa [Prod.ext_iff,funext_iff,padTuple] using big_cell_unique hσ ·)) fun γ n↦ite_eq_right fun o↦?_).2 (hasSum_subtype_iff_indicator.1 (summable_amplitude ..).hasSum)
  · have D i : δ i∈S.termsOfLink Λ := by simp [δ,termsOfLink];rw [← inv_inv i.2.1.1,termDisc,frameDisc_frameGram_besselU_mul,link_besselU_mul,frameDisc_weylElem_mul] <;> simp [Finset.prod_eq_zero_iff,← L, *]
    refine ⟨t, σ,_,⟨hσ,rfl,fun v↦by simpa [mul_conj',sq] using! (((map_ne_zero (Φ v)).2 h₀.2).lt_of_le' ((qt hσ c c').2.2.1▸by simp [dotProduct,conj_mul'];positivity)).1,
      h.choose_spec.1,L _⟩,_,A.prod_fiberwise (A.summable.prod_factor · |>.hasSum),fun p↦tendsto_tsum_of_dominated_convergence (A.summable.prod_factor p).norm (fun q↦tendsto_const_nhds.congr' ((S.qm (S.termPosition c c q.1)).mono ?_)) (.of_forall fun _ q↦?_)⟩ <;> clear * - D <;> grind -ac [indicator,D (p,q),norm_zero]
  obtain ⟨w,hw,w',hw',p, τ,hτ,rfl⟩:=exists_big_cell_decomp (hs _ o.2);cases (link_big_cell_eq_iff hτ hσ).1 (L 1▸link_besselU_mul hw hw'▸o.1.2);exact n ⟨((p ·),⟨w,hw⟩⁻¹,⟨w',hw'⟩⁻¹),by simp [δ];ext;simp [weylElem,weylOn,padTuple];grind⟩
lemma qv t (x : 𝔰.κ → _) : ji (S.piBar.map (evalPlaces T)) (evalPlaces T
  t) (evalPlaces T∘x)=evalPlaces T∘ji S.piBar t x:=funext (by simp [Sum.forall,ji,besselLatticeBasis,middleBaseChange,mulVec,dotProduct,Matrix.diagonal,apply_ite (evalPlaces T),← star_evalPlaces, -Units.val_inv_eq_inv_val])
variable [P : IntegralPlace (LocProd T)] {F} [hF : S.IsFillingLevel T F] [hT : Fact (↑S.gIdele⁻¹ ∈ integralOff T)] (k l : S.latStabilizer)
lemma _root_.IntegralPlace.qw {x : Eˣ} (h : ↑x∈ratIntegralOff T∧↑x⁻¹ ∈ ratIntegralOff T) : P.md (evalPlaces T x) ^ (2⁻¹ : ℝ)=(∏ v,‖Φ v x.1‖ₑ)⁻¹ := by
  let u := x.map (ratToPlaces T).1
  erw [inv_eq_iff_eq_inv.1 (P.jz u),
    (sqrt_genIndex_le_prod_norm T ⟨x.ne_zero,h.1⟩).antisymm (by
    simpa [u,genIndex_eq_inv_prod_norm] using inv_anti₀ (Real.sqrt_pos.2 (genIndex_pos u⁻¹)) (sqrt_genIndex_le_prod_norm T ⟨by simp,h.2⟩))]
  simp [inv_rpow,← rpow_natCast_mul,ofReal_prod_of_nonneg]
lemma IsFillingLevel.mem_principalLevel_iff : x∈S.principalLevel↔S.IsIntegralOff T x ∧
  S.toPlaces T x∈F.congGroup:=by rw [principalLevel_eq_unitaryLevel,qq hT.1,← hF.g_eq]
lemma IsFillingLevel.reduction_eq_iff : S.reduction k=S.reduction l↔(S.toPlaces T k)⁻¹ * S.toPlaces T l∈F.congGroup:=by obtain ⟨l,rfl⟩:=mul_left_surjective k l;simpa [principalLevel,qr.1 l.2] using hF.mem_principalLevel_iff (x:=l)
lemma IsFillingLevel.qx (h : S.IsIntegralOff T x) :
  P.ψ (F.g⁻¹ * simpleRootSum (S.toPlaces T x))=S.unipotentChar x := .trans (by simp
  [hF.g_eq,hF.psi_eq,simpleRootSum,toPlaces,U.map])
  (S.qf T (mul_mem hT.1 (sum_mem fun _ _↦h.isIntMatrix _ _)) :)
lemma IsFillingLevel.md_g : P.md F.g=(S.g ^ numInfPlaces E : ℝ≥0∞)⁻¹ ^ 2:=by simpa [hF.g_eq,gIdele_val,↓rpow_inv_rpow,← ofReal_norm] using congr($(P.qw ⟨((mem_Ô_iff T).1 S.gIdele_mem).2,hT.1⟩) ^ (2 : ℝ))
lemma IsFillingLevel.qy : S.unipOrder * F.jv=1:=by simp [-Finset.sum_add_distrib,Level.jv,Level.floorModulus,hF.md_g,← rpow_natCast_mul,← pow_mul _ 2,← pow_succ,Finset.prod_pow_eq_pow_sum];rw [pow_mul,(?_ : Finset.sum .. = _),← mul_pow];simp [ENNReal.mul_inv_cancel];exact 𝔰.ϱ.rec (by simp) (by grind [Finset.sum_range_succ'])
lemma IsFillingLevel.qz {B μ} [SFinite μ] (a : ∀ᵐ z ∂μ,∃ x∈B,S.toPlaces T x=z∧S.IsIntegralOff T x) (r : ∀ x∈B, μ ∗ₘ .dirac (S.toPlaces T x) = μ) : Nat.card (S.reducedImage B) * μ F.congGroup = μ (unitaryLevel P.R 1 (S.latMiddle _).splitGram):=by
  choose k c b using fun s : S.reducedImage B↦s.2
  refine .trans ?_ ((measure_iUnion (fun s t n↦disjoint_left.2 fun z u v↦n (by
    ext1;simpa [← b,hF.reduction_eq_iff] using mul_mem (inv_mem u.out) v)) fun s↦measurable_mul_const (S.toPlaces T (k s)) (P.measurableSet_unitaryLevel (g:=F.g))).symm.trans (measure_congr (a.mono fun | _,⟨x,a,rfl,o⟩ => propext (mem_iUnion.trans ⟨fun ⟨s,n⟩↦(mul_mem_cancel_right (qr.1 (k s).2).2).1 (P.ju
    n),fun n↦⟨_,by simpa using (hF.reduction_eq_iff ..).1 (b ⟨_,⟨x,qr.2 ⟨o,n⟩⟩⁻¹,inv_mem a,rfl⟩).symm⟩⟩))))
  simp_all [← (measurableEmbedding_mulRight _).map_apply,← μ.mconv_dirac,Nat.card_eq_fintype_card]
variable [WeilData E]
lemma j0 : .card (S.reducedImage besselS) = .card (S.reducedImage besselH) * S.unipOrder:=by
  obtain ⟨T,_, -,_, -⟩:=(S.qn ∅).exists;obtain ⟨P,F,hF⟩ :=
    S.qs T
  have:=hF.qz (B:=besselU ..) (ae_ascConv_mem_unipotentBelow.mono fun z h ↦
    (qp z).imp (by
    simp_all [unipotentBelow_eq_besselU])) fun _ h↦(ascConv_heisenbergMeasure_invariant ((unipotentBelow_eq_besselU le_rfl).ge (h.map_mem_unitriangularOn _))).1
  simp [-Finset.prod_mul_distrib,hF.jn,hF.integral_data,Level.floorModulus] at this;erw [← Nat.card_eq_of_bijective _ ⟨(mul_injective_of_disjoint (disjoint_def.2 ?_)).codRestrict fun ⟨p,q⟩↦mul_mem (map_mono (comap_mono fun _↦mem_unitriGroup_of_mem_besselU) p.2) (map_mono (comap_mono fun _↦mem_unitriGroup_of_mem_floorGroup) q.2), ?_⟩,Nat.card_prod,mul_comm];congr
  exact_mod_cast (F.unipotentMass_ne_zero_and_ne_top.elim ENNReal.mul_left_inj).1
    (this.trans hF.qy.symm)
  rintro _ ⟨u,a,_⟩ ⟨k,b,rfl⟩
  simpa [← principalLevel_eq_unitaryLevel,principalLevel] using mem_unitaryLevel_of_besselU_mul
    (inv_mem a) b (S.principalLevel_eq_unitaryLevel.le ⟨u⁻¹ * k,by simp_all⟩)
  rintro ⟨_,⟨_,m⟩,j,rfl⟩;obtain ⟨u,a,h,b,rfl⟩:=mem_besselS.1 j;lift h to S.latStabilizer using (mem_unitaryLevel_of_besselU_mul a b (unitaryLevel_one.ge m)).1;use ⟨⟨_,⟨_,m⟩ / h,by simpa,rfl⟩,_,h,b,rfl⟩;ext1;simp
lemma IsFillingLevel.j1 [S.IsAdmissible] [Side] {σ p c c'} {Z : F.IntermediateGroup} {k : S.latStabilizer} (u : σ ∈ GT 𝔰.ϱ) (o : S.IsIntegralOff T (S.termPosition c c' (weylElem 𝔰.ϱ p * σ))) {a b : Z.Cosets} (e : (S.toPlaces T k)⁻¹ * a.out.1 *
  b.out.1⁻¹ ∈ F.congGroup) : let q := Units.map (ratToPlaces T)∘p;let γ := weylElem 𝔰.ϱ p * σ
    F.zd Z q (S.toPlaces T (S.termPosition c c' σ))⁻¹ (a,b)•besselCorrelation volume
      (.toLp 2 <| S.besselFn ·) (S.ratToInf γ)=(F.headDensity 𝔰.ϱ q 1).toReal •
      F.groupMeasure.real F.congGroup•S.qk T c (S.reduction k) c' γ := by
  intro q γ
  let δ (x : besselU × besselU) := x.1.1 * γ * x.2.1⁻¹
  let B c x u y :=
    ite (S.termPosition c c u * x∈S.principalLevel) (S.classCutoff c (S.ratToInf u * y)) 0
  have val {c} {u : besselU} {x} (t : S.IsIntegralOff T x) (h : S.termPosition c c u * x∈S.principalLevel) : P.phase F.g (S.toPlaces T x) =
    (S.unipotentChar (S.ratToFin u.1))⁻¹ := eq_inv_of_mul_eq_one_right (by
    obtain ⟨⟨d,h⟩,j⟩:=hF.mem_principalLevel_iff.1 h,u.2.termPosition_mem_besselU c
    rw [unipotentChar_eq_of_mem_principalLevel j (ratToFin_mem_besselU.2 u.2) c.out (by simp [termPosition,mul_assoc]),← hF.qx ((mul_mem_cancel_right t).1 d),← P.jt (j.map_mem_unitriangularOn _),P.phase_eq (one_mem _) (by simpa using h)];simp [simpleRootSum_eq_zero_of_mem_besselH])
  have ex {c x} (t : S.IsIntegralOff T x) (h : P.phase F.g (S.toPlaces T x)≠0) y : ∑' u : besselU,
    B c x u.1 y=1:=by
    have ⟨u,hu,h⟩:=P.jp h;obtain ⟨u,rfl,s,d⟩ :=
      qp u
    obtain ⟨v,hv,d, -⟩:=exists_rat_approx_unipotentChar_eq c (d.1 hu)
    erw [← tsum_classCutoff_eq_one c ((S.ratToInf v)⁻¹ * y),tsum_subtype _ (B c x · y),tsum_subtype _ (S.classCutoff c <|
      S.ratToInf · * _),← (Equiv.mulRight v⁻¹).tsum_eq];congr with w
    simp [indicator,B,classUnip,mul_mem_cancel_right,hv,termPosition,mul_assoc,ite_and,by
      simpa [termPosition,mul_assoc] using mul_mem_cancel_right (y:=S.termPosition c c w) (mul_mem (inv_mem d) (by simp [hF.mem_principalLevel_iff,IsIntegralOff,mul_mem, *] : u⁻¹ * x∈_))]
  let Q x := S.IsIntegralOff T (S.termPosition c c x.1) ∧ δ x∈S.termsOver c (S.reduction k) c'
  let h x y := ite (Q x) ((S.classCutoff c y * S.classCutoff c' ((S.ratToInf (δ x))⁻¹ * y)).toReal•S.besselKernel (δ x) y) 0
  let g x := (((S.toPlaces T (S.termPosition c c x.1) * ·) ⁻¹' F.congGroup) ×ˢ univ).indicator
    fun w↦h x (S.ratToInf x.1 * w.2)
  rw [Level.zd,show weylElem 𝔰.ϱ q * _=S.toPlaces T (S.termPosition c c'
    γ) by simp [γ,qt u c];ext : 3;simp [toPlaces,U.map,weylElem,weylOn,apply_ite (evalPlaces T), -star_algebraMap_finAdele, -Units.val_inv_eq_inv_val];rfl,
    PiLp.smul_apply,smul_assoc,qk,← tsum_const_smul'',
    tsum_congr (g:=(∫ w,g · w ∂F.groupMeasure.prod volume)) fun x↦by
    rw [integral_indicator ((measurable_const_mul _ P.measurableSet_unitaryLevel).prod .univ),← Measure.restrict_prod_eq_prod_univ,integral_fun_snd (h x <| _ * ·),integral_mul_left_eq_self];split <;> simp [h,Q,amplitude, δ,Measure.real, *]]
  congr 1 with i;rw [tsum_integral_apply fun x↦.indicator (by unfold h;split <;> fun_prop) ((measurable_const_mul _ P.measurableSet_unitaryLevel).prod .univ)]
  · simp [besselCorrelation];rw [← integral_mul_right_eq_self _ a.out.1,← integral_prod_mul]
    congr with ⟨z,y⟩;obtain ⟨x,rfl,t, -⟩:=qp z
    let ξ := (S.termPosition c c' γ)⁻¹ * x * k
    have s : ξ.1∈_:=mul_mem (mul_mem (inv_mem o) t) (qr.1 k.2).1
    have C w : S.toPlaces T (S.termPosition c c w.1) * S.toPlaces T x∈F.congGroup∧Q w ↔
      S.termPosition c c w.1 * x∈S.principalLevel∧S.termPosition c' c' w.2 * ξ ∈
      S.principalLevel:=and_assoc.symm.trans (.trans (and_congr_left' (by
      simp [hF.mem_principalLevel_iff,mul_mem_cancel_right t,IsIntegralOff,and_comm]))
      (and_congr_right fun ⟨l,L⟩↦by
      clear * - L
      use .imp' (·⁻¹ * l * k) ?_,
        .imp' (l * k * ·⁻¹) ?_ <;> simp_all [δ, ξ,termPosition,mul_assoc]))
    have j:=P.js (y:=S.toPlaces T ξ) e
    set r : ℂ:=_ * _;conv_lhs at j => simp [ξ,mul_assoc]
    rw [tsum_congr (g:=fun w ↦
      (B c x w.1 y * B c' ξ w.2 ((S.ratToInf γ)⁻¹ * y)).toReal•r) fun w↦by
      simp [h,B, δ,indicator,← ite_and,C,↓ite_zero_mul_ite_zero];split_ifs with q
      simp [↓besselKernel_besselU_mul,val t q.1,val s q.2,r,Level.IntermediateGroup.besselVector,j,besselKernel,mul_assoc,unipotentChar,inv_eq_conj];simp]
    by_cases r=0;simp [*]
    simp_all [↓tsum_toReal_smul_of_tsum_eq_one,r,Level.IntermediateGroup.besselVector,mul_assoc]
  grw [← mul_lt_top ((amplitudeAbs_lt_top_and_cut_le univ c _).1 c').2 (hF.z0 P.ju).lt_top,tsum_subtype,← tsum_comp_le_tsum_of_injective fun _ _ e↦(big_cell_unique u e).2,← ENNReal.tsum_mul_right]
  gcongr with x;simp [enorm_indicator_eq_indicator_enorm]
  grw [lintegral_indicator_le,← Measure.prod_restrict,lintegral_prod_le]
  simp [lintegral_mul_left_eq_self (‖h x ·‖ₑ)]
  unfold h;split_ifs with q;grw [enorm_toReal_smul_le,indicator_of_mem q.2,amplitudeAbs];simp
end Filling
end
section
attribute [-simp] Fintype.card_pi
open Space Fintype Matrix Grading ProbabilityTheory Nat Finset Real
namespace Data
variable {P} (D : Data P)
private lemma card_besselCoord_mul_factorial_le : Fintype.card D.filling.BesselCoord * (D.k - 1)! ^ D.f ≤
  ((√√D.b ^ 5) ^ D.k) ^ D.f := by
  grw [Fintype.card_pi, prod_le_pow_card _ _ ((D.k + D.a) ^ D.k) fun v _ ↦ ?_, sub_le,
    factorial_le_pow]; simp [← mul_pow]; gcongr; use D.le_of_hasLogBound
  obtain ⟨_, A, h, ⟨⟩⟩ := (D.filling_fits.1 v).2
  grw [A.square_of_invertible _ ‹_› h,
    ← card_eq_of_equiv_fintype (schur_one_row_eq_symPowMatrix (a := D.κ v 1) (.refl _)
    ..).choose.symm, card_finsuppAntidiag_nat_eq_choose, sub_le, ← choose_symm_add, choose_le_pow]
  gcongr; all_goals grind [card_X₀, D.le_m, κ]
private lemma rowParameter_sub_mem v {i l} (h : i < l) :
  (D.rowParameter v i - D.rowParameter v l : ℝ) ∈ Set.Icc 1 ↑(D.w (l + 2 - D.k) v) :=
  by simp; norm_cast; grind [D.varsigma_strictAnti v h, rowParameter]
local grind_pattern rowParameter_sub_mem => D.rowParameter v i, D.rowParameter v l
private lemma log_filling_besselDegree_mem_Icc : log D.filling.besselDegree + D.f * ∑ l ∈ Ico (D.k - 1) D.r,
  .log l ! ∈ Set.Icc (∑ v, D.m * ((D.k - 1) * log (D.nominalWeight v))) (∑ v,
  D.m * (D.r * (log (D.nominalWeight v) + D.x⁻¹))) := by
  rw [(?_ : D.filling.besselDegree = exp (∑ v, ∑ l ∈ Ico (D.k - 1) D.r,
    (∑ i ∈ range l, log (D.rowParameter v i - D.rowParameter v l) - .log l !)))]
  · simp; constructor <;> gcongr
    grw [← @range_mono (D.k - 1),
      ← (D.nominalWeight_le_w_sub 0 ‹_›).trans (c := _ - _)] <;> norm_cast
    any_goals grw [(rowParameter_sub_mem ..).2, @range_mono _ D.r, log_w_le]
    any_goals simp [(by grind : D.r - (D.k - 1) = D.m), HasLogBound.pos D]
    all_goals grind [log_nonneg, rowParameter]
  push_cast [Filling.besselDegree, (D.filling_fits.1 _).1, ↓card_rowIndex, exp_sum, exp_sub,
    weylDimensionPoly, ↓paramW_lt_iff, paramW]; congr!
  simp [prod_comm, prod_filter, reindex_equiv D.basisNumber.symm, prod_fin_eq_prod_range,
    ← mem_range, ← prod_div_distrib]
  apply prod_congr_of_eq_on_inter
  field_simp; norm_cast; simp [← prod_range_add_one_eq_factorial]
  all_goals grind [rowParameter, prod_range_reflect, Finset.prod_congr, exp_log, cast_pos]
end Data
end
namespace Data
open Finset Real Filling Subgroup MulAction Fintype Shape NeZero NumberField
variable {P} (D : Data P)
private lemma relIndex_latStabilizer : (comap D.filling.inclHFin D.filling.latStabilizer).relIndex (Kf ..) =
  (D.N ^ D.k - 1 : ℝ) ^ D.f := by
  rw [(?_ : comap .. = levelOf (↑) (pi ⊤ fun w : D.piPlaces ↦
    (stabilizer _ (Pi.single D.shape.k₀ 1 : _ → ResField w.1)).comap invTransposeGL.toMonoidHom)),
    relIndex_levelOf (h := ⟨by simp, by simp [D.isSplitLevel_piPlaces.star_notMem]⟩)]
  simp [index_pi_univ, index_comap, index_stabilizer_GL_vector, card_ResField,
    D.isSplitLevel_piPlaces.q_eq, ↓card_X₀, card_piPlaces, Fin.pos']
  ext; erw [inclHFin_mem_latStabilizer, mem_levelOf]
  refine exists_prop.symm.trans (exists_congr fun h ↦
    (?_ : _ ↔ ∀ w _, (transposeGL _)⁻¹ ∈ stabilizer ..))
  simpa [funext_iff, Units.smul_def, ↓dvd_def, ← mem_piPlaces, Subtype.ext_iff, -reduceAt_eq_zero]
    using! (forall₂_congr fun (_ : Unit) j ↦ dvd_iff_reduceAt_eq_zero D.intValuation_pi (⟨_,
    h.isIntMatrix (.inr ()) j⟩ - ite (j = D.shape.k₀) 1 0)).trans forall₂_comm
private lemma card_classes_filling : card D.filling.Classes =
  Nat.card (D.filling.reducedImage besselH) * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k := by
  erw [card_eq_nat_card, card_classes_eq_classSum D.classAut_columnLevel_eq_bot,
    classSum_one_of_le IsLevel.le, columnLevel_zero_eq_comap, ← relIndex_mul_relIndex _ _ _
    (comap_mono (map_subtype_le _)) fun _ ↦ ((inclHFin_mem_latStabilizer _).1 · |>.1),
    relIndex_comap, map_comap_eq, ← subgroupOf_map_subtype, relIndex_map_map_of_injective _ _ (by
    simp), relIndex_ker, range_inclHFin, classSum_stdRatPoints_eq_mass,
    card_X₀]; simp [D.relIndex_latStabilizer, reducedImage]
instance : D.filling.IsAdmissible := by
  obtain ⟨m, f, p, _⟩ := @mass_pos D.E, @nsmul_le_nsmul_right ℝ, sub_pos.2 (one_lt_pow₀
    (D.lt_of_hasLogBound (G := D.N)) D.k_pos.ne'), pos D.gProd, D.filling.besselDegree_pos,
    rootDiscr_pos D.E, D.filling.frameScaleProd_pos, @Nat.card_pos (D.filling.reducedImage besselH)
    _ _, @card_pos D.filling.BesselCoord _ _, D.N_prime.two_le, Nat.le_self_pow D.k_pos.ne'
    D.N, D.log_N_mem_Icc, D.k_le_r, D.k_pos, log_natCast_nonneg (card D.filling.BesselCoord),
    congr(D.k * D.m * $(mul_div_cancel₀ (∑ v, log (D.nominalWeight v)) (ne ↑D.f)))
  obtain _ := D.card_besselCoord_mul_factorial_le, m D.k, m D.r,
    f (log_natCast_nonneg (D.k - 1).factorial) D.f, f (log_le_log (by positivity)
    (D.le_of_hasLogBound : D.b ^ 19 ≤ D.gProd)) (D.f * D.k), f (log_le_log p (sub_one_lt
    _).le) D.f, (nsmul_right_mono D.f).mapsTo_Icc ⟨(log_le_sub_one_of_pos (div_pos (p.trans
    (sub_one_lt _)) p)).trans (by field_simp; norm_cast; lia),
    (D.le_of_hasLogBound : 2 / D.N ≤ D.logB)⟩, D.log_filling_besselDegree_mem_Icc,
    congr(D.f * ∑ i ∈ $(D.k.Ico_pred_singleton ‹_›), log i.factorial), (nsmul_right_mono (D.f *
    D.k)).mapsTo_Icc D.log_N_mem_window, ((abs_sum_le_sum_abs _ (Ico D.k D.r)).trans (sum_le_sum
    fun i _ ↦ abs_log_mass_ratio_sub_le D.E i D.ϱ D.nat_le_of_hasLogBound (by grind))).trans (by
    grw [le_sub_iff_add_le, ← le_log_one_add_of_nonneg (by positivity)]; simp [*]; use
      D.le_of_hasLogBound : _ ≤ log (1 + D.b⁻¹ ^ 9) - D.f * (2 / D.N)),
    le_sub_iff_add_le.2 (D.le_of_hasLogBound : |D.f * (D.m - 1) * (D.ϱ *
    log (D.gProd * D.rootDisc / 2 / π) + log (√D.rootDisc / 2 / π)) - D.m * ∑ v,
    log (D.nominalWeight v)| + (log 2 + log (1 + D.b⁻¹ ^ 9) + D.m * (D.m * ∑ v, log (D.nominalWeight
    v) + D.f * D.r * D.x⁻¹) + D.f * D.k * √D.logB) ≤ D.f * D.k * D.logB / 4), (D.le_of_hasLogBound :
    D.f * ((D.m - 1) * (D.ϱ * log (2 / D.rootDisc / D.gProd) - log √D.rootDisc) - (D.ϱ + 1) ^ 7 *
    ((D.m - 1) * log (D.gProd * D.rootDisc / 2 / π) - log (D.gProd * D.N))) ≤ D.f * D.k * D.logB)
  apply (by simpa only [← and_imp] using IsAdmissible.mk D.columnLevel_zero_eq_comap (⟨_,
    D.filling_fits.reduction_finiteEquiv_iff _ · |>.2 ⟨_, reduceFamily_liftResidue
    (w := D.chosen) _⟩ |>.2⟩) : _ → _)
  rify [card_X₀, @id (D.filling.g = D.gProd) rfl, abs_kappa_eq, ← InfinitePlace.apply, mk_Φ,
    besselEnergy, codimFactor, columnDim, tailScale, packetConst, j0,
    card_classes_filling, D.relIndex_latStabilizer, siegelConst, Filling.unipCovolume,
    openCellConst, bandConst, ↓card_rowIndex, volU, Shape.k, mainEnergy, volÔ_eq,
    abs_discr_eq_rootDiscr_pow, prod_mul_distrib, prod_div_distrib, prod_pow, prod_pow_eq_pow_sum]
  simp only [filling, P.prod_varpi_eq_rootDiscr_pow, eq_tsub_of_add_eq D.r_add] at *
  iterate 3 use fun _ ↦ D.le_of_hasLogBound
  simp (disch := intros; first | positivity | omega) only [← log_le_log_iff, log_div, log_mul,
    log_pow, log_sqrt, log_rpow, log_exp, log_inv, log_prod, log_one, sum_add_distrib, sum_const,
    Finset.card_range, nsmul_eq_mul, sum_range_id, ← Nat.choose_two_right, card_univ, logLevelTarget,
    abs_le, ↓sum_Ico_eq_sub, Set.mem_Icc, sum_sub_distrib, ← mul_sum, sum_singleton, ← sum_mul, ←
    Nat.cast_sum _ (·), ↓sum_range_sub (log <| mass D.E ·)] at *
  push_cast (disch := apply D.nat_le_of_hasLogBound) [Nat.cast_choose_two, ← add_assoc,
    m_eq_two_mul_varrho_add_two] at *
  and_intros <;> linarith [log_two_gt_d9]
end Data
