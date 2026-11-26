import Lib.DiscreteSeries.Bruhat.FloorGroups
import Lib.DiscreteSeries.Bruhat.BigCell
import Lib.DiscreteSeries.CuspKernel.CircleMean
section
open Matrix FI Sum Fintype MatMul Finset Fin
variable {A l n:Type} [CommRing A] [StarRing A] {𝔰:Shape} (T:𝔰.Form A) {α β}
structure Size where
 ofSize:ℕ→ Set A
 mul_mem_ofSize {i j x y}:x∈ofSize i→ y∈ofSize j→ x*y∈ofSize (i+j)
 sum_mem_ofSize {i} {n:Type} [Fintype n] {f:n→ A} :
   card n≤ 𝔰.r+1→ (∀ a,f a∈ofSize i)→ ∑ a,f a∈ofSize (i+1)
 neg_star_mem_ofSize {i x}:(-x∈ofSize i↔x∈ofSize i)∧(star x∈ofSize i↔x∈ofSize i)
 zero_one_mem_ofSize i:0∈ofSize i∧1∈ofSize i
 gram_mem_ofSize:(∀ i j,T.splitGram i j∈ofSize 1)∧∀ i j,T.splitGram⁻¹ i j∈ofSize 1
variable {T} {c d i j} {s g x u:T.G} {v w:𝔰.BesselIndex→ A} {a:Fin 𝔰.ϱ} {p q} {r:Aˣ} {S:Size T} {X Z:Matrix l 𝔰.BesselIndex A}
noncomputable def weylRatio j p q:=(weylElem j q)⁻¹*(weylElem j p:T.G)
lemma s21_k8:(weylRatio j p q:T.G).1.1=diagonal fun i↦ite (floorOf i< j⊓𝔰.ϱ) (ite (level i< 𝔰.ϱ) (p (floorOf i)/q (floorOf i)).1 (star (q (floorOf i)/p (floorOf i)).1)) 1:=by ext;simp [weylRatio,weylElem,mul_apply,diagonal,weylOn,division_def];grind [oppositeIndex_spec]
lemma wQ:(weylRatio j p q:T.G)⁻¹=weylRatio j q p:=rfl
lemma card_succ_le_floorOf:card {i:𝔰.BesselIndex // a+1≤ floorOf i}=𝔰.k+1+2*(𝔰.ϱ-(a+1)):=by simp [card_congr .subtypeSum,Fintype.card_subtype,filter_lt_eq_Ioi];lia
namespace Size
def vecsOfSize i:={v:n→ A | ∀ a,v a∈S.ofSize i}
def HasMatSize i (X:Matrix l n A):=∀ a b,X a b∈S.ofSize i
def IsHead j (p:ℕ→ Aˣ):=∀ l≤ j,(∏ a ∈ .range l,p a)⁻¹.1∈S.ofSize 1
attribute [local simp] mul_sub zero_one_mem_ofSize neg_star_mem_ofSize level ite_mem ne_of_gt weylOn weylElem HasMatSize val_lt_of_le
lemma IsHead.wG:S.IsHead j p→ S.IsHead j (star p):=by simp [IsHead,← star_prod]
lemma mem_ofSize_mono (h:α∈S.ofSize i) (e:i≤ j:=by lia) :
 α∈S.ofSize j:=by grind [S.mul_mem_ofSize h (S.zero_one_mem_ofSize (j-i)).2]
lemma zJ:α∈S.ofSize i→ β∈S.ofSize i→ α-β∈S.ofSize (i+1):=by
 simpa [sub_eq_add_neg] using S.sum_mem_ofSize (f := ![α,-β]) (by simp +arith)
lemma HasMatSize.mono (h:S.HasMatSize i X) (e:i≤ j:=by lia):S.HasMatSize j X:=(S.mem_ofSize_mono <| h · ·)
lemma HasMatSize.one:S.HasMatSize i (1:Matrix 𝔰.BesselIndex 𝔰.BesselIndex A):=by simp
lemma HasMatSize.sub:S.HasMatSize i X→ S.HasMatSize i Z→ S.HasMatSize (i+1) (X-Z):=by simp_all [zJ]
lemma qV (h:∀ a,v a≠0→ w a∈S.ofSize i) (k:v∈S.vecsOfSize j):w⬝ᵥv∈S.ofSize (i+j+1):=S.sum_mem_ofSize le_self_add (by grind [mul_mem_ofSize,zero_one_mem_ofSize,vecsOfSize])
lemma HasMatSize.mulVec:S.HasMatSize i X→ v∈S.vecsOfSize j→ X *ᵥ v∈S.vecsOfSize (i+j+1):=fun h k _↦qV (by tauto) k
lemma HasMatSize.mul {Y:Matrix 𝔰.BesselIndex n A}:S.HasMatSize i X→ S.HasMatSize j Y→ S.HasMatSize (i+j+1) (X*Y):=fun h k _ b↦h.mulVec (k · b) _
lemma wN:∀ Z:Matrix (Fin j) _ A,j≤ 𝔰.ϱ→ S.HasMatSize 7 Z→ Z.det∈S.ofSize (8*j):=j.rec (by simp) fun _ k Z _ h↦det_succ_row_zero' Z▸mem_ofSize_mono (S.sum_mem_ofSize (by simp;lia) fun _↦S.mul_mem_ofSize (i:=7) (by simp_all [neg_one_pow_eq_ite]) (k _ (by lia) (by tauto)))
lemma vL [IsHermUnit T.splitGram] {X Y} (e:T.splitGram*X=Yᴴ*T.splitGram) a b (h:∀ n,T.splitGram n b≠0→ Y n∈S.vecsOfSize i):X a b∈S.ofSize (i+4):=nonsing_inv_mul_cancel_left _ X (‹IsHermUnit _›.2.map detMonoidHom)▸e▸mem_ofSize_mono
 (HasMatSize.mulVec S.gram_mem_ofSize.2 (fun m↦qV (by simpa using h · · m) (S.gram_mem_ofSize.1 · b)) a)
lemma HasMatSize.inv [IsHermUnit T.splitGram] (h:S.HasMatSize i x.1.1):S.HasMatSize (i+4) x⁻¹.1.1:=(vL (U.form_mul_inv_eq _) · · (by tauto))
lemma jQ m (h:∀ a,a.1< j→ ∃ w,(∀ b≤ a,w (eStar b)=ite (b=a) 1 0)∧w∈S.vecsOfSize c∧X *ᵥ w∈S.vecsOfSize d) (z:∀ k,j≤ floorOf k∨level k≤ 𝔰.ϱ→ X m k∈S.ofSize d) i:∀ k,j≤ floorOf k+i∨level k≤ 𝔰.ϱ→ X m k∈S.ofSize (d+(c+3)*i):=i.rec z fun i ih k l↦by_cases (mem_ofSize_mono <| ih k ·) fun _↦(h ⟨floorOf k,by grind⟩ (by lia)).rec fun w ⟨_,hw,e⟩↦mem_ofSize_mono
 (by simpa [entrywise] using zJ (mem_ofSize_mono (e m)) (qV (fun k l↦ih k (by grind [level_le_or_exists_dual,Matrix.one_apply,-Sum])) fun l↦zJ (hw l) (HasMatSize.one l k)))
lemma vZ [IsHermUnit T.splitGram] (hu:u∈unipotentBelow j) (hr:star r.1=r ∧ ↑r∈S.ofSize 1) (h:∀ a:Fin 𝔰.ϱ,a.1< j→ ∃ w,(∀ b≤ a,w (eStar b)=ite (b=a) 1 0)∧w∈S.vecsOfSize c∧(r⁻¹.1•(1-u.1.1)) *ᵥ w∈S.vecsOfSize c):S.HasMatSize (c+4+(2*c+8)*j) (r⁻¹.1•(1-u⁻¹.1.1)):=fun i k↦mem_ofSize_mono (jQ i (h · · |>.elim fun w ⟨e,m,n⟩↦⟨u *ᵥ w,by grind [unitriGroup_mulVec_dual (unipotentBelow_le_unitriGroup hu) .refl],fun k↦by simpa using (zJ (mem_ofSize_mono (m k)) (S.2 hr.2 (n k))),
 (mem_ofSize_mono <| by simpa using S.4.1.2 <| n ·)⟩) (fun k e↦vL (by simp [*,← inverse_star_unit,← U.form_mul_inv_eq]) i k fun n l↦(jQ n h (fun m _↦by simp [mem_unipotentBelow.1 hu n m (by grind [splitGram_eq_ite_oppositeIndex,oppositeIndex_spec,-Sum])]) j · (by lia))) j k (by lia))
variable {K:Set (U _)} (o:∀ ⦃x⦄,x∈K→ S.HasMatSize 1 x.1.1) (hj:j≤ 𝔰.ϱ) (h':∃ η∈unitriGroup j,η*((weylElem j p)⁻¹*g)∈K) (h:s∈unitriGroup j∧s*g∈K)
include o hj h' h
lemma vF [IsHermUnit T.splitGram] (ha:a< j) i:(∏ b ∈ .range (a+1),p b).1*s.1.1 i (eStar a)∈S.ofSize (9*𝔰.n):=h'.rec fun η ⟨r,h'⟩↦mem_ofSize_mono (by
 have y m d l:=inv_mem r m (inl (.castLE a.2 d)) ⟨l,by simp [ha]⟩
 convert wN _ a.2 fun b d↦(o h.2).mul (o h').inv (ite (b = .last _) i (eStar (b.castLE a.2))) (inl (d.castLE a.2))
 simp [-coe_units_inv]
 erw [← mul_assoc,det_eq_of_eq_mul_det_one _ (det_eq_one_of_unitriangular fun _↦(y _ · · |>.trans (by simp))) (ext fun b d ↦ .symm (sum_of_injective _ (inl_injective.comp (castLE_injective a.2)) _ _ (fun m _↦by dsimp;erw [y] <;> revert m <;>
   simp [Fin.exists_iff] <;> grind) fun _↦rfl)),det_of_isLowerTriangular _ fun b
   d↦by simp [mul_apply, *];grind [unitriGroup_dual_row,one_apply_ne]]
 simp +contextual [prod_univ_castSucc,prod_range,unitriGroup_dual_row h.1,ha.le,mul_apply, *]
 ac_rfl)
lemma minors_mem_ofSize [IsHermUnit T.splitGram]:∀ l≤ j,(∏ a ∈ .range l,p a).1∈S.ofSize (9*𝔰.n):=by
 rintro (_ | l) e;simp;lift l to Fin 𝔰.ϱ using by lia
 simpa +contextual [unitriGroup_dual_row h.1 e] using vF o hj h' h e (eStar l)
lemma zQ [IsHermUnit T.splitGram] (hp:S.IsHead j p) (ha:a< j):let N:=S.ofSize (10*𝔰.n)
 (p a).1∈N∧(p a)⁻¹.1∈N∧∀ i,s.1.1 i (eStar a)∈N:=by
 obtain _:=S.mul_mem_ofSize (hp _ ha.le) (minors_mem_ofSize o hj h' h _ ha),S.mul_mem_ofSize (hp _ ha) (minors_mem_ofSize o hj h' h _ ha.le),(S.mul_mem_ofSize (hp _ ha) <| vF o hj h' h ha ·);simp [prod_range_succ,mul_assoc,-Units.coe_prod] at *;grind [mem_ofSize_mono]
lemma kB [IsHermUnit T.splitGram] (hp:S.IsHead j p) (hν:s∈unipotentBelow j):S.HasMatSize (60*𝔰.n^2) g.1.1∧S.HasMatSize (99*𝔰.n^2) ((weylElem j p)⁻¹*g).1.1:=(fun a↦⟨a,.mono (.mul (i:=10*𝔰.n) (by simp_all [zQ o _ h' h]) a)⟩) (.mono (by simpa using (HasMatSize.one.sub (vZ (r:=1) hν (by simp) fun a e↦⟨Pi.single (eStar a) 1,by simpa [-Sum.forall,vecsOfSize] using (zJ (by simp) <| (zQ o hj h' h hp e).2.2 ·)⟩)).mul (o h.2)) (by nlinarith))
end Size
end
noncomputable section
open Matrix MeasureTheory Measure FI ENNReal Fintype Place TraceOne Function Filter
variable {A} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P:Place A] (ι) [Fintype ι] {𝔰:Shape} (T:𝔰.Form A) (m) [IsHermUnit T.splitGram] {l i j}
structure Level extends HyperbolicBasis ι T m where
 (θ measureH:Measure T.G) (g:Aˣ) (𝔅:Set (𝔰.BesselIndex→ A))
 (boxSet positions:Set T.G) [sFinite_theta:SFinite θ] [sFinite_measureH:SFinite measureH] [neZero_measureH:NeZero measureH]
 theta_spec:(∀ᵐ x ∂θ,x∈GT 𝔰.ϱ)∧θ.map (orbitPoint 𝔰.top)=toHyperbolicBasis.floorQuadric 𝔰.top
 measureH_spec:(∀ᵐ x ∂measureH,x∈besselH)∧(∀ s∈besselH,measureH∗ₘdirac s=measureH)∧∀ g,measureH {h | ∃ u∈besselU,u*(h*g)∈boxSet}≤ 1
 star_g:star g.1=g
 ball_spec:IsOpen 𝔅∧0∈𝔅∧IsCompact (closure 𝔅)
 box_spec:IsCompact boxSet∧MeasurableSet positions
variable {ι T m} {ν ρ} [SFinite ν] [SFinite ρ] {s:T.G} {S:Subgroup T.G} {f Φ:T.G→ ℝ≥0∞} (F:Level ι T m) (b:Fin 𝔰.n)
namespace Level
attribute [instance] sFinite_theta sFinite_measureH neZero_measureH
def floorMeasure l:=if l< 𝔰.ϱ then weylLaw l∗ₘheisenbergMeasure l else if l=𝔰.ϱ then F.θ else if l=𝔰.n then F.measureH else dirac 1
instance:SFinite (F.floorMeasure l):=by fun_cases floorMeasure <;> infer_instance
abbrev stackMeasure:=descConv fun a↦heisenbergMeasure a∗ₘF.floorMeasure a
abbrev groupMeasure:=F.stackMeasure 0 (𝔰.ϱ+2)
@[simp] abbrev upperMeasure l:=descConv F.floorMeasure l (𝔰.ϱ+2-l)
def IsNear j g:=∃ ξ∈unitriGroup j,ξ*g∈F.boxSet
abbrev orthonormalPart:Matrix 𝔰.BesselIndex ι A:=fromRows 0 (F.basisMatrix.toCols₂.toCols₂.toCols₁.fromRows 0)
abbrev closePairs:={u:_ × _ | u.1∈F.𝔅∧F.g⁻¹.1•(u.1-u.2)∈F.𝔅}
def floorValues a (x y:T.G):=(· (eStar a)) ''
 {w | (x⁻¹.1.1 *ᵥ w,(x*y)⁻¹.1 *ᵥ w)∈F.closePairs∧∀ b< a,w (eStar b)=0}
abbrev volumeExponent (_:Level ι T m):=card ι-(3*𝔰.n+1+m)
def floorWeight j x y := ∏ a with a.1< j,volume (F.floorValues a x y)^F.volumeExponent
def floorModulus l (g:=F.g):=P.md g^(𝔰.k+1+2*(𝔰.ϱ-(l+1)))*P.md g^(2⁻¹:ℝ)
variable {F}
lemma measurePreserving_orbitPoint:MeasurePreserving (orbitPoint b) (F.floorMeasure b) (F.floorQuadric b):=⟨by fun_prop,b.lastCases
 (by simp [floorMeasure,theta_spec]) fun a↦ext_of_lintegral _ fun Φ _↦by
 rw [← ((isDisintegration_quadricMeasure (IsHermitian.submatrix ‹IsHermUnit _›.1 (·.1))).map _ ((gram_inclMatrix (![.inl a,eStar a] ⊕ᵥ @Subtype.val _ (a+1≤ floorOf ·)) 1).trans _)).unique (F.isDisintegration_floorVolume _ (map_inclMatrix_eq_floorVolume _ _ _))]
 any_goals simp [gram_inclMatrix,← ext_iff];grind
 simp (disch:=with_unfolding_all fun_prop) [floorMeasure,heisenbergMeasure,lintegral_map,mconv,lintegral_prod,lintegral_withDensity_eq_lintegral_mul,volume_eq_prod];rw [lintegral_congr_of_ae_imp ae_isUnit];rintro _ ⟨t,rfl⟩
 rw [← lintegral_neg_eq_self,eq_comm,lintegral_eq_mul_lintegral_map (map_mulVec_volume _ (t.1•1) _),lintegral_map] <;> first | fun_prop | simp [↓card_succ_le_floorOf,orbitPoint,heisenbergElem_inv,← mulVec_mulVec,-mulVec_single]
 congr! 3;rw [lintegral_sub_left_eq_self (Φ <| heisenbergElem a ⟨_,·⟩ |>.1.1 *ᵥ _)];congr!;simp [↓heisenbergElem_mulVec,flatChart,inclMatrix_val_mulVec,-inverse_star_unit,floorWeyl,weylOn,level,← Pi.single_apply,col_apply',↓splitGram_col,← gram_inclMatrix];simp [funext_iff,inclMatrix,mulVec_apply_eq_sum,← mulVec_smul,star_mulVec_dotProduct]
 grind [invOf_mul_self,Matrix.mul_assoc]⟩
lemma zZ (hs:s∈GT b):MeasurePreserving (s *ᵥ orbitPoint b ·) (F.floorMeasure b) (F.floorQuadric b) := .comp ⟨by fun_prop,
 ((F.isDisintegration_floorVolume b rfl).map s.2 s.1.4).unique (F.isDisintegration_floorVolume b ((measurePreserving_floor_block_mulVec hs).of_semiconj (hfm:=⟨by fun_prop,rfl⟩) (inclMatrix_mulVec_floor_block b.is_le hs) (by fun_prop)).2)⟩ (measurePreserving_orbitPoint b)
lemma ae_floorMeasure_mem:∀ᵐ x ∂F.floorMeasure l,x∈GT l:=by
 fun_cases floorMeasure <;> simp [theta_spec,measureH_spec,ae_mem_mconv _ (eventually_and.1 ae_mem_floorUnipotent).1 measurableSet_floorGroup,ae_map_iff measurable_floorWeyl.fun_inv.aemeasurable,measurableSet_floorGroup, *]
@[congr] lemma qN {μ} (e:F.floorMeasure l=μ) (h:∀ σ∈GT l,f σ=Φ σ):lintegral (F.floorMeasure l) f=lintegral μ Φ:=e▸lintegral_congr_of_ae_imp ae_floorMeasure_mem h
@[simp] lemma floorMeasure_top:F.floorMeasure 𝔰.n=F.measureH:=by simp [floorMeasure]
lemma s21_j6:F.upperMeasure l=F.upperMeasure (l+1)∗ₘF.floorMeasure l:=by grind [descConv.eq_def,floorMeasure,mconv_dirac_one]
lemma s21_j8 (h:l< 𝔰.ϱ):descConv F.floorMeasure l (i+1)=(weylLaw l∗ₘdescConv F.floorMeasure (l+1) i)∗ₘheisenbergMeasure l:=by rw [descConv,floorMeasure,ite_eq_left h,← mconv_assoc,mconv_comm_of_ae ((ae_descConv_mem ae_floorMeasure_mem).mono fun s k↦by simp (disch:=first | fun_prop | lia) [dirac_mconv,mconv_dirac,Measure.map_map,comp_def,floorWeyl,(commute_weylOn _ k).inv_left.eq])]
lemma kX {p q}:j≤ 𝔰.ϱ→ Measurable Φ→ ∫⁻ x,Φ (weylRatio j p q*x) ∂F.upperMeasure 0=(∏ a ∈ .range j,md (p a/q a).1^(𝔰.k+2*(𝔰.ϱ-a))) * ∫⁻ x,Φ x ∂F.upperMeasure 0:=j.rec (by simp [weylRatio]) fun j ih hj _↦by
 rw [Finset.prod_range_succ_comm,mul_assoc,← ih,upperMeasure,(by lia:_-0 =
   j+(𝔰.ϱ-j+2)),descConv_add,s21_j8,mconv_assoc,mconv_assoc]
 repeat rw [lintegral_mconv,lintegral_map,lintegral_withDensity_eq_lintegral_mul]
 rw [lintegral_eq_mul_lintegral_map (map_mul_volume (p j/q j)),lintegral_map,← lintegral_const_mul,← lintegral_const_mul,lintegral_congr_of_ae_imp ae_isUnit]
 all_goals first | fun_prop | lia | simp [mul_pow,← mul_assoc]
 congr! 5;grind [=_ pow_succ'];ext;simp [s21_k8,floorWeyl,weylOn,division_def,Ring.mul_inverse_rev];grind [Units.inv_mul,=_ star_mul,oppositeIndex_spec]
lemma zK (hS:GT l≤ S) (hi:(unitriGroup (l+1)⊓S).FixesLeft f) (hs:s∈unitriGroup l⊓S) (hf:Measurable f:=by fun_prop) : ∫⁻ x,f (x*s) ∂F.floorMeasure l = ∫⁻ x,f x ∂F.floorMeasure l:=by
 obtain ⟨γ,a,ν,n,rfl⟩:=exists_floorGroup_mul_unipotentBelow hs.1
 rw [qN rfl fun x k ↦ .trans (by group) (hi _ ⟨unipotentBelow_le_unitriGroup (conj_mem_unipotentBelow (mul_mem k a) n),by simp_all [mul_assoc x γ,mul_mem,hS k,hS a]⟩ (x*γ))]
 obtain h | _ | _:=lt_or_ge l 𝔰.n
 have ⟨A,m,e⟩:=exists_factor_orbitPoint ⟨l,h⟩ hf (hi ·∘by gcongr)
 simpa +contextual [mul_mem,orbitPoint, *,-mulVec_single,← (measurePreserving_orbitPoint ..).lintegral_comp] using (zZ ⟨l,h⟩ (inv_mem a)).lintegral_comp m
 repeat simp_all [← lintegral_mconv_dirac,measureH_spec,floorGroup_eq_bot]
lemma ae_stackMeasure_mem:∀ᵐ x ∂F.stackMeasure l i,x∈GT l:=ae_descConv_mem (ae_mem_mconv (eventually_and.1 ae_mem_floorUnipotent).1 ae_floorMeasure_mem)
lemma stackMeasure_mconv_dirac (h:l+i=𝔰.ϱ+2) (hs:s∈GT l):F.stackMeasure l i∗ₘdirac s=F.stackMeasure l i:=by
 induction i generalizing l s;simp_all [floorGroup_eq_bot];apply ext_of_lintegral;intros
 rw [eq_comm,stackMeasure,descConv,← mconv_assoc,lintegral_mconv_symm,← zK le_rfl _ ⟨mem_unitriGroup_of_mem_floorGroup hs,hs⟩,mconv_assoc,lintegral_mconv_symm,lintegral_mconv_dirac] <;> try fun_prop
 simp_rw [← lintegral_mconv_dirac];grind [_=_ mconv_assoc,dirac_mconv_heisenbergMeasure_comm,heisenbergMeasure_mconv_dirac,exists_floorGroup_mul_floorUnipotent,=_ dirac_mconv_dirac]
instance isMulRightInvariant_groupMeasure:F.groupMeasure.IsMulRightInvariant:=⟨by simp [← mconv_dirac,stackMeasure_mconv_dirac]⟩
lemma stackMeasure_zero_eq:F.stackMeasure 0 j=ascConv heisenbergMeasure j∗ₘdescConv F.floorMeasure 0 j:=j.rec (by simp! [descConv])
 (by grind [descConv_succ,ascConv_heisenbergMeasure_succ,_=_ mconv_assoc,mconv_comm_of_ae (F.ae_floorMeasure_mem.mono ascConv_heisenbergMeasure_dirac_comm)])
lemma stackMeasure_ne_zero:F.stackMeasure l i≠0:=measure_univ_pos.1 (by
 induction i generalizing l <;> simp [descConv,mconv_apply_eq_lintegral, *]
 grind [floorMeasure,mconv_zero,heisenbergMeasure,dirac_ne_zero,F.neZero_measureH.1,fun e↦by simpa (disch:=fun_prop) [NeZero.ne] using congr($((F.measurePreserving_orbitPoint ⟨l,e⟩).2)=0)])
variable [F.groupMeasure.IsHaarMeasure]
lemma jA (e:F.groupMeasure=ρ∗ₘν) (a:∀ᵐ y ∂ρ,y∈S) (r:∀ s∈S,ρ∗ₘdirac s=ρ) (c:dirac s∗ₘρ=ρ∗ₘdirac s) (m:Measurable Φ) (i:S.FixesLeft Φ) : ∫⁻ g,Φ (s*g) ∂ν=lintegral ν Φ:=by
 have ⟨f,f0,_,f1⟩:=exists_pos_lintegral_lt_of_sigmaFinite F.groupMeasure top_ne_zero
 have E ν [SFinite ν] (e:F.groupMeasure=ρ∗ₘν) : ∫⁻ x,Φ x/(∫⁻ y,f (y*x) ∂ρ)*f x ∂F.groupMeasure=lintegral ν Φ:=by
   rw [e,lintegral_mconv_symm] at f1 ⊢;rw [lintegral_congr_of_ae_imp (ae_lt_top _ f1.ne)];intro g k
   rw [lintegral_congr_of_ae_imp a,lintegral_const_mul,ENNReal.div_mul_cancel (stackMeasure_ne_zero∘e.trans∘by
     simp +contextual (disch:=fun_prop) [EventuallyEq,(f0 _).ne']) k.ne]
   repeat first | fun_prop | simp_all [← mul_assoc,i _,← lintegral_mconv_dirac (f <| · * g)]
 rw [← lintegral_dirac_mconv];grind [_=_ mconv_assoc,dirac_mconv,map_mul_left_eq_self F.groupMeasure]
lemma s21_q9 p (hΦ:Measurable Φ) (hi:(GT j).FixesLeft Φ) (hj:j≤ 𝔰.ϱ+2:=by lia) : ∫⁻ g,Φ ((weylElem j p)⁻¹*g) ∂F.stackMeasure 0 j = ∫⁻ g,Φ g ∂F.stackMeasure 0 j:=by apply (jA (Nat.add_sub_of_le hj▸descConv_add ..) ae_stackMeasure_mem _ (mconv_comm_of_ae (ae_stackMeasure_mem.mono _)).symm) <;> simp_all [stackMeasure_mconv_dirac,commute_weylElem,Commute.eq]
variable (F) (j:ℕ) (k:T.G→ T.G→ ℂ) (w x g y:T.G) (K:ℝ≥0∞)
def FloorMassLe (c:_→ _):=∀ g,∫⁻ σ in {σ | F.IsNear (j+1) (σ*g)},c (σ*g) ∂F.floorMeasure j≤ K
def upperPairing := ∫ x,k (x*g) (x*y) ∂F.upperMeasure j
structure IsPairingKernel where
 measurable:Measurable ↿k
 law {l n n'}:n∈unipotentBelow l→ n'∈unipotentBelow l→ ∀ g y,F.upperPairing (l+1) k (n*g) (n'*y)=ψ (F.g⁻¹.1*(simpleRootSum (w*n'*w⁻¹)-simpleRootSum n))*F.upperPairing (l+1) k g y
 conj_eq_self:∀ s∈GT j,w*s*w⁻¹=s
 exists_lintegral_le l:∃ c< ∞,∀ g y,∫⁻ x,‖k (x*g) (x*y)‖ₑ ∂F.upperMeasure l≤ c
 isNear_of_upperPairing_ne_zero:∀ {l g y},F.upperPairing l k g y≠0→ F.IsNear l g
def qJ:={z | F.IsNear j z}.indicator fun z↦(F.floorWeight j z x)⁻¹
def pivotModulus := ∫⁻ σ,‖F.upperPairing (j+1) k (σ*g) (σ*y)‖ₑ ∂F.floorMeasure j
abbrev z7:=F.floorWeight j g x*‖F.upperPairing (j+1) k g (g*x)‖ₑ^2
def weightedSquareSum x j g:=if j< 𝔰.n then ∫⁻ σ,F.z7 j k x (σ*g)+weightedSquareSum x (j+1) (σ*g) ∂F.floorMeasure j else 0
def selfNorm := ∫⁻ g,F.weightedSquareSum k x j g ∂descConv F.floorMeasure 0 j
end Level
structure Gauge extends Size T where
 Λ:ℝ≥0∞
 isCompact_ofSize j:IsCompact (ofSize j)
 two_le_and_pairs_le:2≤ Λ∧m≤ 9*𝔰.n
 one_le_c_and_ne_top:1≤ c A∧Λ ≠ ∞
 data_mem_ofSize : ↑F.g∈ofSize 1∧toSize.HasMatSize 1 F.basisMatrix∧τ*skewUnit⁻¹.1∈ofSize 1
 hasMatSize_box ⦃x⦄ : x∈F.boxSet→ toSize.HasMatSize 1 x.1.1
 hasVecSize_ball:F.𝔅⊆Size.vecsOfSize 1
 md_le j (u:Aˣ) : ↑u∈ofSize j→ P.md u≤ Λ^j
 volume_le j:volume (ofSize j)≤ Λ^(j+1)
 fib σ [Fintype σ] j:m≤ card σ→ card σ≤ m+𝔰.ϱ→ quadricMeasure
   (hyperbolicGram σ (0:Matrix _ Empty A)) 0 (Size.vecsOfSize j)≤ Λ^(99*𝔰.n*(j+1))
 com:∀ x∈F.boxSet,∀ y∈F.positions,∀ v:Matrix (Fin 𝔰.ϱ) _ A,let W:={w | v *ᵥ w=0∧(x⁻¹.1.1 *ᵥ F.orthonormalPart *ᵥ w,(x*y)⁻¹.1.1 *ᵥ F.orthonormalPart *ᵥ w)∈F.closePairs};∃ φ,Measurable φ∧(∀ u,(volume ((star u⬝ᵥ·) '' W))⁻¹≤ φ u∧volume {c:A | ∀ w∈W,∃ z∈F.closePairs,∃ z'∈F.closePairs,star (c•u)⬝ᵥw=F.g⁻¹*(star z.1⬝ᵥT.splitGram *ᵥ z'.1-star z.2⬝ᵥT.splitGram *ᵥ z'.2)}≤ φ u)∧∀ j,∫⁻ u in toSize.vecsOfSize j,φ u^F.volumeExponent≤ Λ^(99*𝔰.n*(j+1))
@[simp] lemma Gauge.one_le_Lambda (Γ:Gauge F):1≤ Γ.Λ:=one_le_two.trans Γ.two_le_and_pairs_le.1
def Gauge.positionsOfSize (Γ:Gauge F):={x∈F.positions | Γ.HasMatSize 1 (F.g⁻¹.1•(x.1.1-1))}
end
section
open Finset Sum HyperbolicBasis ENNReal Function Level Matrix MeasureTheory Place Set Size TraceOne MeasureTheory.Measure
attribute [local simp] mul_eq_top Fintype.card_subtype IsUnit.pow fromBlocks_mulVec mulVec_sub vecsOfSize Size.neg_star_mem_ofSize Size.zero_one_mem_ofSize inclMatrix ite_mem mul_assoc mul_sub smul_sub sub_mul
variable {A ι} {𝔰:Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [Place A] [Fintype ι] {C K M m i j p q} {a:Fin 𝔰.ϱ} {T:𝔰.Form A} [IsHermUnit T.splitGram] {F:Level ι T m} {Γ:Gauge F} {b:Fin 𝔰.n} {g x y σ ξ:T.G} (h:ξ∈unitriGroup j)
lemma Size.mem_vecsOfSize_of_heisenbergElem {S:Size T} {u:Aˣ} {t}:let v:=inclMatrix A (↑) *ᵥ t.1;(∃ ν∈T.unipotentBelow a,u⁻¹.1•(((ν*heisenbergElem a t).1.1-1) · (eStar a))∈S.vecsOfSize i)→ u⁻¹.1•v∈S.vecsOfSize i∧u⁻¹*(t.2-τ*star v⬝ᵥT.splitGram *ᵥ v)∈S.ofSize i:=fun ⟨ν,hν,h⟩↦by
 have E n k l:=congr(_*($(unipotentBelow_mulVec_apply hν n k l)-_)∈_).mp (h k)
 simp [heisenbergElem,eichlerMap,vecMulVec,inclMatrix_val_mulVec,-inclMatrix] at *;grind
@[simp] lemma Level.kL (h:ξ∈unitriGroup j):F.IsNear j (ξ*g)↔F.IsNear j g:=(Equiv.mulRight ξ).exists_congr (by simp_all [mul_mem_cancel_right])
lemma Level.IsNear.of_floorGroup_mul (h:F.IsNear i (x*g)) (hx:x∈GT j) (ha:j≤ i:=by first | rfl | lia) :
 F.IsNear j g:=(kL (mem_unitriGroup_of_mem_floorGroup hx)).1 (by grind [IsNear])
lemma Level.j4:MeasurableSet {g | F.IsNear j g}:=((isClosed_of_entries_eq_one (S:=unitriGroup j) .rfl).mul_right_of_isCompact F.box_spec.1).measurableSet.congr
 (ext fun _↦inv_surjective.exists.trans (by simp [IsNear,inv_mul_eq_iff_eq_mul]))
lemma Level.upperMeasure_isNear_le {V} (hV:∀ a:Fin 𝔰.n,F.FloorMassLe a V 1) l c:F.upperMeasure l {g | F.IsNear (𝔰.ϱ+2) (g*c)}≤ V^(𝔰.n-l):=by
 induction' e:_-l with i ih generalizing l c
 cases (by lia:l=𝔰.n∨𝔰.ϱ+2-l=0) <;>
   simp [*,descConv,IsNear,measureH_spec,indicator_apply_le',-Subtype.exists]
 erw [s21_j6,mconv_apply_eq_lintegral (measurable_mul_const c j4)]
 simp [-upperMeasure,FloorMassLe] at *
 grw [← setLIntegral_eq_of_support_subset,ih,setLIntegral_const,hV ⟨l,by lia⟩ _ c.2,pow_succ]
 exacts [by lia,support_subset_iff'.2 fun _ _ ↦
   mono_null (by grind [IsNear.of_floorGroup_mul]) (ae_descConv_mem ae_floorMeasure_mem)]
lemma Level.kN:IsOpen {((x,y),c):_ × A | c∈F.floorValues a x y}:=isOpen_iff_forall_mem_open.2 fun _ ⟨w,_⟩↦⟨ofPred _,fun _↦(⟨_,⟨·,by grind⟩,update_self _ _ w⟩),by apply_rules [IsOpen.and,F.ball_spec.1.preimage] <;> fun_prop,by aesop⟩
lemma Level.k3 (h:ξ∈unitriGroup (a+1)):F.floorValues a (ξ*x) y=F.floorValues a x y:=by
 ext
 use .imp' (mulVec ξ⁻¹) ?_,.imp' (mulVec ξ) ?_ <;> simp <;>
   grind [unitriGroup_mulVec_dual,inv_mem h,coe_units_inv,Subgroup.coe_inv]
@[simp] lemma Level.wC:volume (F.floorValues a x y)≠0∧volume (F.floorValues a x y) ≠ ∞ := ⟨(kN.preimage (.prodMk_right (x,y))).measure_ne_zero _ ⟨0,0,by simp [ball_spec]⟩,(((F.ball_spec.2.2.preimage_smul x⁻¹).image (by fun_prop)).measure_ne_top <| measure_mono_top (image_mono fun _↦(subset_closure ·.1.1)) ·)⟩
lemma Level.vB:F.floorWeight (a+1) x y=F.floorWeight a x y*volume (F.floorValues a x y)^F.volumeExponent:=by
 simp [floorWeight,filter_gt_eq_Iio,prod_Iio_mul_eq_prod_Iic,filter_ge_eq_Iic]
@[simp] lemma Level.wI:F.floorWeight j x y≠0∧F.floorWeight j x y ≠ ∞ := by simp [floorWeight,prod_ne_top,prod_eq_zero_iff]
include h in
@[simp] lemma Level.kD:F.floorWeight j (ξ*x) y=F.floorWeight j x y:=prod_congr rfl (by grind [k3])
include h in
@[simp] lemma Level.w0:F.qJ j x (ξ*g)=F.qJ j x g:=by simp [qJ,indicator,h]
seal Finset.univ Finset.sum Finset.prod in
@[fun_prop] lemma wS:Measurable ↿(F.floorWeight j):=measurable_prod _ fun _
 _↦(measurable_measure_prodMk_left kN.measurableSet).pow_const _
@[fun_prop] lemma Level.wW:Measurable (F.qJ j x) := .indicator (by fun_prop) j4
namespace Gauge
lemma zE {n} [Fintype n]:MeasurableSet (Γ.vecsOfSize (n:=n) j) := .univ_pi' fun _↦(Γ.isCompact_ofSize j).measurableSet
lemma qR {x} (h:F.floorBasis b *ᵥ x∈Γ.vecsOfSize j):x∈Γ.vecsOfSize (j+4):=by
 have:=((by simp [HasMatSize,floorBasis,mul_apply,-ite_mul,sum_boole_mul,-star_sum,Γ.data_mem_ofSize.2.1 _]:Γ.HasMatSize 1 (F.floorBasis b)ᴴ).mul Γ.gram_mem_ofSize.1).mulVec h
 simp_all +arith [gram_floorBasis,dotProduct]
def HasFibreBound (Γ:Gauge F) b q j M:=∃ (Z:Type) (_:MeasurableSpace Z)
 (ζ:Measure Z),∃ ρ k μ,SFinite ζ∧MeasurePreserving k ((volume.prod volume).prod ζ) ρ∧ρ.map
 (F.floorBasis b *ᵥ ·)=q∧(∀ r,r.1=((k r (inl 1),k r∘inr∘inl),k r∘inr∘inr∘inl))
 ∧ Measurable μ∧(∀ p w,ζ {z | k ((p,w),z)∈Γ.vecsOfSize (j+4)}≤ μ p) ∧ ∫⁻ p,μ p≤ M
lemma q0 {Φ G:_→ _}:Γ.HasFibreBound b q j M→ (∀ p,Measurable (G p) ∧ ∫⁻ w,G p w≤ K)→ (∀ x∈Γ.vecsOfSize (j+4),Φ (F.floorBasis b *ᵥ x)≤ G (x (inl 1),x∘inr∘inl) (x∘inr∘inr∘inl))→ ∫⁻ x in Γ.vecsOfSize j,Φ x ∂q≤ M*K:=by
 rintro ⟨Z,_,ζ,_,k,μ,_,⟨_,rfl⟩,rfl,_,_,hμ,hM⟩ hG _
 grw [← lintegral_indicator,lintegral_map_le _ (by fun_prop),lintegral_map_le _ (by fun_prop),← hM,lintegral_prod_le,lintegral_prod_le,← lintegral_mul_const]
 gcongr;grw [mul_comm,← (hG ‹_›).2,← lintegral_mul_const,← hμ _ ‹_›,← lintegral_indicator_const_le];gcongr;repeat grind [indicator,qR,zero_le,zE]
lemma hasFibreBound_floorQuadric_of_le (e:quadricMeasure (hyperbolicGram (FloorPairs b m) (0:Matrix Empty ..)) 0 (Γ.vecsOfSize (j+5))≤ M):Γ.HasFibreBound b (F.floorQuadric b) j M :=
 have N:=MeasurePreserving.comp ⟨by fun_prop,rfl⟩ (measurePreserving_shuffle_coords.comp (.prod ⟨measurable_prodMk_right,by rw [volume_pi_eq_dirac,prod_dirac]⟩ (.id _)))
 ⟨_,_,_,_,_,_,inferInstance,.comp ⟨by fun_prop,rfl⟩ measurePreserving_shuffle_coords,rfl,by tauto,measurable_measure_prodMk_left (N.1 zE),fun p w ↦
   measure_le_of_sub_mem fun y k↦⟨y,fun z h↦by simp [flatChart,star_sumElim] at *;grind [mem_ofSize_mono,Size.zJ,zJ h.1.1 k.1.1]⟩,((N.measure_preimage_le _).trans e).trans_eq' (Measure.prod_apply (N.1 zE))⟩
lemma hasFibreBound_floorQuadric:Γ.HasFibreBound b (F.floorQuadric b) j (Γ.Λ^(99*𝔰.n*(j+6))):=hasFibreBound_floorQuadric_of_le (by apply fib <;> simp [card_finset_fin_le])
lemma qX:Γ.HasFibreBound b (floorVolume b) j (Γ.Λ^(99*𝔰.n*(j+6))):=have K:=((Γ.isCompact_ofSize _).measurableSet.prod zE).prod (zE.prod (Γ.isCompact_ofSize _).measurableSet)
 ⟨_,_,_,_,_,_,inferInstance,measurePreserving_pair_sumElim.comp (measurePreserving_swap.comp measurePreserving_shuffle_coords),map_floorBasis_volume ..,
   by tauto,measurable_measure_prodMk_left K,fun p w↦measure_mono fun _↦by simp;tauto,by
   simp [↓← Measure.prod_apply K,volume,← mem_univ_pi,-Set.mem_pi]
   grw [volume_le,card_finset_fin_le,Γ.two_le_and_pairs_le.2] <;> ring_nf <;> bound⟩
lemma qE {Φ Ψ:_→ _} (u:Aˣ) (k : ∫⁻ x in Γ.vecsOfSize j,Ψ x ∂floorVolume a.succ≤ M) (h:∀ t,let n:=heisenbergElem a t;Φ n≠0 →
   (∃ ν∈T.unipotentBelow a,u⁻¹.1•(((ν*n⁻¹).1.1-1) · (eStar a))∈Γ.vecsOfSize j) ∧
 Φ n≤ C*Ψ (u⁻¹.1•inclMatrix A (·.1) *ᵥ t.1)) (e:F.floorModulus a u*(Γ.Λ^(j+2)*M)≤ K:=by simp [floorModulus];ring_nf;gcongr <;> simp) (m:Measurable Ψ:=by fun_prop) : ∫⁻ n,
 Φ n ∂heisenbergMeasure a≤ C*K:=by
 grw [← e,mul_rotate',mul_rotate,floorModulus,mul_mul_mul_comm,mul_assoc,heisenbergMeasure,dite_eq_left,← k,← lintegral_mul_const,setLIntegral_map,← lintegral_indicator_le,lintegral_map_le,← lintegral_mul_const',lintegral_prod_le,lintegral_eq_mul_lintegral_map (map_mulVec_volume _ (u.1•1) _),lintegral_map_le];gcongr;simp [↓card_succ_le_floorOf];choose V E using fun {t} n↦mem_vecsOfSize_of_heisenbergElem (heisenbergElem_inv (T:=T)▸(h t n).1)
 grw [← setLIntegral_eq_of_support_subset .rfl,setLIntegral_mono _ fun t n ↦ ?_,setLIntegral_const,skewMeasure_le_of_sub_mem u⁻¹ fun z h y k↦Eq.subst (by simp;ring) (zJ (Γ.mul_mem_ofSize Γ.data_mem_ofSize.2.2 (zJ (E k.1) (E h.1))) (mem_ofSize_mono (zJ (E h.2) (E k.2))))]
 any_goals grw [(h _ n).2,mul_comm,indicator_of_mem (by simpa [mulVec_neg] using V n)]
 repeat' first | fun_prop | simp [one_le_c_and_ne_top,↓zE,smul_smul,mul_pow,← pow_mul,← rpow_mul_natCast]
 grw [volume_le];bound
lemma zR {φ} (h:Γ.HasFibreBound b q j M) (k : ∫⁻ w in Γ.vecsOfSize (j+4),φ w≤ K) (m:Measurable φ:=by fun_prop) : ∫⁻ x in Γ.vecsOfSize j,φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ x) ∂q≤ M*K:=q0 h
 (fun _↦⟨m.indicator zE,by grw [lintegral_indicator_le,k]⟩) fun x e↦by
 simpa [← mulVec_mulVec,comp_def,e _,show F.orthonormalPart=(F.floorBasis b).toCols₂.toCols₂.toCols₁ by simp [entrywise,floorBasis]] using! congr(φ (($(gram_floorBasis ..) *ᵥ x)∘inr∘inr∘inl)).le
lemma jJ:MeasurableSet Γ.positionsOfSize:=F.box_spec.2.inter ((Γ.isCompact_ofSize 1).matrix.measurableSet.preimage (by fun_prop))
lemma vG (hg:g∈F.boxSet) (h:x∈Γ.positionsOfSize) (k:y∈Γ.positionsOfSize) (e:σ=g*x*(g*y)⁻¹):Γ.HasMatSize 14 (F.g⁻¹.1•(σ.1.1-1)):=by
 simpa [e] using ((Γ.hasMatSize_box hg).mul (h.2.sub k.2)).mul (((Γ.hasMatSize_box hg).mul fun a b↦by simpa using zJ (Γ.mul_mem_ofSize Γ.data_mem_ofSize.1 (k.2 a b)) (Γ.neg_star_mem_ofSize.1.2 (HasMatSize.one a b))).inv (x:=g*y))
lemma vE (hσ:σ∈GT b) (hg:Γ.HasMatSize i g.1.1):F.IsNear (b+1) (σ*g)→ orbitPoint b σ∈Γ.vecsOfSize (i+6):=fun ⟨ξ,a,c⟩ k↦by
 simpa [orbitPoint,by simpa using floorGroup_apply_besselFrame (inv_mem hσ) (inv_mem a) k] using fun _↦hg.mul (Γ.hasMatSize_box c).inv ..
lemma jZ (hj:j≤ 𝔰.ϱ) (hp:Γ.IsHead j p):F.IsNear j g→ F.IsNear j ((weylElem j p)⁻¹*g)→ ∃ σ∈GT j,Γ.HasMatSize (60*𝔰.n^2) (σ*g).1.1∧Γ.HasMatSize (99*𝔰.n^2) (σ*((weylElem j p)⁻¹*g)).1.1:=fun ⟨_,a,c⟩ h↦(exists_floorGroup_mul_unipotentBelow a).imp fun σ ⟨b,ν,n,_⟩↦⟨b,((weylElem_mul_left_comm b).2▸(kB Γ.hasMatSize_box hj · ⟨unipotentBelow_le_unitriGroup (conj_mem_unipotentBelow b n),by aesop⟩ hp (conj_mem_unipotentBelow b n))) ((kL (mem_unitriGroup_of_mem_floorGroup b)).2 h)⟩
lemma hasMatSize_sub_one_of_floorValues {q} (S:Gauge F) (hj:j≤ 𝔰.ϱ) (hp:S.IsHead j p) (hq:S.IsHead j q) (hS:j≠0→ ∀ c∈S.ofSize (10*𝔰.n),F.g⁻¹*c∈Γ.ofSize 1):(∃ u∈T.besselU,∃ v∈T.besselU,u*x∈F.boxSet∧v*(x*y)∈F.boxSet∧Γ.HasMatSize 2 (F.g⁻¹.1•((v*(x*y)).1.1-(u*x).1.1)))→ F.IsNear j ((weylElem j p)⁻¹*x)→ F.IsNear j ((weylElem j q)⁻¹*(x*y))→ (∀ a,j≤ a.1→ ∃ c:Aˣ,↑c∈F.floorValues a x y ∧ ↑c⁻¹∈Γ.ofSize 1)→ Γ.HasMatSize (99*𝔰.n) (F.g⁻¹.1•(y.1.1-1)):=fun ⟨u,hu,v,hv,k,n,d⟩ l o hc ↦ .mono
 (by simpa using (Γ.hasMatSize_box k).inv.mul (d.mono.sub (.mul (vZ (c:=6) ((unipotentBelow_eq_besselU .refl).ge (mul_mem hv (inv_mem hu))) ⟨F.star_g,Γ.data_mem_ofSize.1⟩ fun a _↦if e:a< j then have z:=(hS e.ne_bot _ <| (zQ S.hasMatSize_box hj l ⟨mem_unitriGroup_of_mem_besselU hu,k⟩ hp e).2.2 ·)
 ⟨u.1.1 *ᵥ Pi.single (eStar a) 1,by grind [unitriGroup_mulVec_dual (mem_unitriGroup_of_mem_besselU hu)],(mem_ofSize_mono <| by simpa using Γ.mul_mem_ofSize Γ.data_mem_ofSize.1 <| z ·),
   fun i↦by simpa [↓mulVec_mulVec] using mem_ofSize_mono (zJ (z i) (hS e.ne_bot _ ((zQ S.hasMatSize_box hj o ⟨mem_unitriGroup_of_mem_besselU hv,n⟩ hq e).2.2 i)))⟩ else (hc a (by lia)).elim fun c ⟨⟨w,⟨⟨m,r⟩,z⟩,e⟩,h⟩↦⟨c⁻¹.1•u *ᵥ w,by simp;grind [c.inv_mul,unitriGroup_mulVec_dual (mem_unitriGroup_of_mem_besselU hu)],(mem_ofSize_mono <| by
 simpa using Γ.mul_mem_ofSize h <| (Γ.hasMatSize_box k).mulVec (Γ.hasVecSize_ball m) ·),
 fun i↦by simpa using (Γ.mul_mem_ofSize h (zJ (mem_ofSize_mono ((Γ.hasMatSize_box n).mulVec (Γ.hasVecSize_ball r) i)) (d.mulVec (Γ.hasVecSize_ball m) i)))⟩) (Γ.hasMatSize_box n))))
end Gauge
end
section
namespace Level
open MeasureTheory Measure ProbabilityTheory Set
attribute [-simp] Subtype.forall
attribute [local simp] ite_eq_right mul_assoc
variable {R ι} {𝔰:Shape} [CommRing R] [StarRing R] [TopologicalSpace R] [MeasureSpace R] [Place R] [Fintype ι] {m j l K} {T:𝔰.Form R} [IsHermUnit T.splitGram] {F:Level ι T m} {x g y s k d} (hk:F.IsPairingKernel j k d)
lemma exists_ne_zero_of_pivotModulus (h:F.pivotModulus l k g y≠0):∃ x∈GT l,k (x*g) (x*y)≠0:=(exists_ne_zero_of_ae ae_floorMeasure_mem h).elim fun σ
 h↦by grind [exists_ne_zero_of_ae (ae_descConv_mem ae_floorMeasure_mem) (ne_bot_of_le_ne_bot h.2 (enorm_integral_le_lintegral_enorm _)),mul_mem,=_ mul_assoc,enorm_zero]
lemma s21_z1 (hl:l≤ 𝔰.ϱ) : ∫⁻ σ,‖F.upperPairing (l+1) k (σ*g) (σ*(g*x))‖ₑ^2 ∂F.floorMeasure l≤ F.weightedSquareSum k x l g/F.floorWeight l g x:=by rw [weightedSquareSum];simp_all [← lintegral_const_mul',ENNReal.le_div_iff_mul_le,mul_comm,lintegral_mono_fn',z7]
namespace IsPairingKernel
include hk
@[fun_prop] lemma wF:StronglyMeasurable ↿(F.upperPairing l k) := .integral_prod_right (hk.rec (by fun_prop))
lemma mono (h:j≤ l):F.IsPairingKernel l k d:={hk with conj_eq_self:=(hk.conj_eq_self · <| floorGroup_anti h ·)}
lemma jE l g y:Integrable (fun x↦k (x*g) (x*y)) (F.upperMeasure l):=(hk.exists_lintegral_le l).elim fun _ ⟨a,b⟩↦⟨⟨_,hk.rec (by fun_prop),.rfl⟩,(b ..).trans_lt a⟩
lemma zI:Integrable (fun σ↦F.upperPairing (l+1) k (σ*g) (σ*y)) (F.floorMeasure l)∧F.upperPairing l k g y = ∫ σ,F.upperPairing (l+1) k (σ*g) (σ*y) ∂F.floorMeasure l:=by
 have I:=hk.jE l g y
 simp [upperPairing,s21_j6,← mul_assoc] at *
 have J:=I.comp_measurable measurable_mul
 use J.integral_prod_right,integral_mconv I▸integral_integral_swap J
lemma enorm_upperPairing_le:‖F.upperPairing l k g y‖ₑ≤ F.pivotModulus l k g y:=hk.zI.2▸enorm_integral_le_lintegral_enorm _
lemma z8 (hl:j≤ l) (hs:s∈unitriGroup l⊓GT j):F.upperPairing l k (s*g) (s*y)=F.upperPairing l k g y:=by
 induction' e:𝔰.ϱ+2-l generalizing l s g y
 have := @hk.law 𝔰.n s s;simp_all [upperPairing,descConv,unipotentBelow_eq_besselU,hk.conj_eq_self,unitriGroup_top_eq_besselU.le (unitriGroup_anti (by lia) hs.1)]
 repeat rw [hk.zI.2]
 apply IdentDistrib.integral_eq ⟨_,_,ext_of_lintegral _ fun _ _↦by rw [lintegral_map,eq_comm,lintegral_map,← zK (floorGroup_anti hl) _ hs] <;> first
   | fun_prop | grind [mul_assoc]⟩ <;> fun_prop
@[fun_prop] lemma wM:Measurable ↿(F.weightedSquareSum k · l ·):=by
 fun_induction F.weightedSquareSum k 1 l 1 <;> unfold weightedSquareSum <;> simp_all <;> fun_prop
lemma qA:(unitriGroup (j+1)).FixesLeft (F.z7 j k x)∧∀ g,¬F.IsNear (j+1) g→ F.z7 j k x g=0:=⟨fun s h↦(exists_floorGroup_mul_unipotentBelow (unitriGroup_anti le_self_add h)).elim fun _ ⟨_,_,b,_⟩↦by simp_all [z7,hk.z8,mul_mem_cancel_right,unipotentBelow_le_unitriGroup b,hk.law,← ofReal_norm],by simp;grind [isNear_of_upperPairing_ne_zero]⟩
lemma zY x:(unitriGroup j).FixesLeft (F.weightedSquareSum k x j)∧∀ g,¬F.IsNear j g→ F.weightedSquareSum k x j g=0:=by
 fun_induction F.weightedSquareSum k x j 1 <;> simp <;> unfold weightedSquareSum <;> simp_all
 use fun s h g ↦ .trans (by simp) (zK le_top (by simp_all [hk.qA,hk.mono]) ⟨h,⟨⟩⟩)
 grind [exists_ne_zero_of_ae F.ae_floorMeasure_mem,hk.qA.2,mono,add_zero,IsNear.of_floorGroup_mul]
lemma jL {u v} (hK:F.FloorMassLe l K u) (h:∀ σ∈GT l,‖F.upperPairing (l+1) k (σ*g) (σ*y)‖ₑ^2≤ u (σ*g)*v σ:=by exact fun _ _↦(one_mul _).ge) (hu:Measurable u:=by fun_prop) (hv:Measurable v:=by fun_prop):F.pivotModulus l k g y^2≤ K * ∫⁻ σ,v σ ∂F.floorMeasure l:=by
 nth_grw 1 [pivotModulus,← qN rfl eqOn_indicator,← setLIntegral_eq_of_support_subset,sq_lintegral_le,hK g,restrict_le_self]
 repeat first | fun_prop | simp [indicator,subset_def];grind [isNear_of_upperPairing_ne_zero,zero_le]
lemma j3 (hl:l≤ 𝔰.ϱ):F.selfNorm l k x = ∫⁻ g,F.z7 l k x g ∂descConv F.floorMeasure 0 (l+1)+F.selfNorm (l+1) k x:=by erw [← lintegral_add_left,descConv_succ,lintegral_mconv_symm] <;> first | fun_prop | grind [weightedSquareSum,selfNorm]
lemma vD (hl:l≤ 𝔰.n):F.selfNorm l k x≤ F.selfNorm 0 k x:=by
 induction' l with l <;> grind [j3 (l:=l),le_add_self]
end IsPairingKernel
end Level
end
section
open ENNReal FI Fintype Level Matrix MeasureTheory Place ProbabilityTheory Set Size U
attribute [-simp] conjTranspose_fromRows_eq_fromCols_conjTranspose
attribute [local simp] AddChar.map_add_eq_mul IsHermUnit.conjTranspose_eq mulVec_neg indicator_apply_le' ascConv heisenbergElem_mulVec mul_add mul_assoc star_mulVec_dotProduct
variable {A ι} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P:Place A] {𝔰:Shape} [Fintype ι] {m j} {T:𝔰.Form A} [IsHermUnit T.splitGram] {F:Level ι T m} (Γ:Gauge F) {x t q:T.G} {b:Fin 𝔰.n} (a:Fin 𝔰.ϱ) {k d p}
lemma Gauge.kE {f K} (hi:(unitriGroup (b+1)).FixesLeft f) (h:∀ g∈F.boxSet,∃ Ψ,∫⁻ v in Γ.vecsOfSize 7,Ψ v ∂F.floorQuadric b≤ K∧Measurable Ψ∧∀ σ∈GT b,f (σ*g)≤ Ψ (orbitPoint b σ)) (hf:Measurable f:=by fun_prop):F.FloorMassLe b K f:=fun g↦have:=measurable_mul_const g j4
 lintegral_indicator this _▸by
   obtain n | ⟨ξ,c,k⟩:=em' (F.IsNear b g);simp +contextual [mt (IsNear.of_floorGroup_mul · _ le_self_add) n];obtain ⟨φ,l,n,h⟩:=h _ k
   grw [← l,← (measurePreserving_orbitPoint b).setLIntegral_comp_preimage zE n,← lintegral_indicator_le,← zK le_top (by simp +contextual [indicator,hi]) ⟨c,⟨⟩⟩,lintegral_le_of_ae_imp ae_floorMeasure_mem]
   grind [vE,hasMatSize_box,indicator,zero_le]
lemma Gauge.kK (hx:x∈F.positions):F.FloorMassLe a (Γ.Λ^(10^4*𝔰.n)) fun g↦F.floorWeight a g x/F.floorWeight (a+1) g x:=Γ.kE (b:=a.castSucc) (by grind [kD])
 (Γ.com · · x hx 0 |>.elim fun φ ⟨_,k,e⟩↦⟨_,(zR hasFibreBound_floorQuadric (e _)).trans (by rw [← pow_add];bound),by fun_prop,fun σ l↦by
 simp [vB,division_def,ENNReal.mul_inv,ENNReal.mul_inv_cancel_left,ENNReal.inv_pow];grw [← (k _).1,image_subset_iff.2 fun w h ↦ ?_]
 use σ *ᵥ F.orthonormalPart *ᵥ w,by simpa +contextual [↓mem_ofPred,↓unitriGroup_mulVec_dual (mem_unitriGroup_of_mem_floorGroup l)] using h.2
 simp [← mulVec_mulVec,← form_mulVec_mulVec σ,orbitPoint_eq_iff.1 rfl]⟩)
lemma Gauge.floorMassLe_one b {M} (e:Γ.HasFibreBound b (F.floorQuadric b) 7 M):F.FloorMassLe b (M*ℙ (Γ.ofSize 11)^card ι) 1:=Γ.kE (by simp) fun _ _↦⟨1,by simpa [vecsOfSize,measurable_one,← mem_univ_pi,volume_pi_pi,-mem_pi] using (zR e le_rfl measurable_one)⟩
noncomputable abbrev Gauge.wB l:=F.floorModulus l*P.c^card ι*Γ.Λ^(4600*𝔰.n)
attribute [-simp] InvMemClass.coe_inv Subgroup.coe_inv in
lemma Gauge.kV (hj:j≤ 𝔰.ϱ) g y:F.IsNear j g→ ∫⁻ ν,Γ.positionsOfSize.indicator (F.floorWeight j g) (g⁻¹*(ν*y)) ∂ascConv heisenbergMeasure j≤ ∏ l ∈ .range j,Γ.wB l:=fun ⟨ξ,h,hg⟩↦by
 obtain ⟨⟨γ,k,n,l,rfl⟩,_⟩:=exists_floorGroup_mul_unipotentBelow h,Γ.jJ;rw [← indicator_congr fun _ _↦kD h,← (ascConv_heisenbergMeasure_invariant (inv_mem l)).2,lintegral_dirac_mconv,lintegral_eq_of_dirac_mconv_eq (ascConv_heisenbergMeasure_dirac_comm _ k)];simp [-Finset.prod_mul_distrib];grw [← Γ.one_le_c_and_ne_top.1]
 refine j.rec (by simp [floorWeight]) (fun j ih hj y↦le_of_not_gt fun c↦c.not_ge ?_) hj (γ*y)
 lift j to Fin 𝔰.ϱ using hj
 obtain ⟨τ,_,hτ,z⟩:=by simpa using exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow c.ne_bot
 obtain ⟨φ,_,k,e⟩:=Γ.com _ hg _ z.1 0;rw [← (ascConv_heisenbergMeasure_invariant hτ).1,lintegral_mconv_dirac,ascConv,lintegral_mconv_symm,Finset.prod_range_succ]
 refine qE _ (zR qX (e _)) fun t n↦have ⟨ν,a,b⟩:=exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow n
   ⟨⟨_,conj_mem_unipotentBelow (inv_mem (heisenbergElem_mem_floorUnipotent j t).1) (inv_mem a),(vG hg z (by simpa using b) (by simp) · _)⟩,?_⟩
 grw [← ih j.2.le,← lintegral_mul_const,lintegral_le_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν a ↦ ?_];simp [-mulVec_smul,← indicator_mul_const];gcongr;grw [vB,← (k _).2,measure_mono];rintro _ ⟨w,⟨hw,o⟩,rfl⟩ u hu;exists _,hw,_,hu.2;rw [← mulVec_smul,star_mulVec_dotProduct];simp [-mulVec_smul,← mulVec_mulVec,form_mulVec_mulVec,heisenbergElem_inv,← inverse_star_unit,star_g,-star_mulVec_dotProduct];simp [dotProduct,unipotentBelow_mulVec_apply (inv_mem a) o,j.2.le.trans];ring
 repeat fun_prop
noncomputable abbrev Gauge.vR:=Γ.Λ^(10^6*𝔰.n^3)
lemma Gauge.z9 {b Φ ρ} [SFinite ρ] (hj:j≤ 𝔰.ϱ) (hp:Γ.IsHead j p) (o:x∈F.positions) (n:j≤ b) (k:(unitriGroup b).FixesLeft Φ∧∀ g,¬F.IsNear b g→ Φ g=0) (l:Measurable Φ) : ∫⁻ g,Φ g*F.qJ j x (weylElem j p*g) ∂ascConv heisenbergMeasure j∗ₘρ≤ (∏ a ∈ .range j,F.floorModulus a (p a)⁻¹)*Γ.vR * ∫⁻ g,Φ g ∂ρ:=by
 rw [lintegral_mconv_symm,mul_comm,← lintegral_mul_const];gcongr
 rw [lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν e↦by rw [k.1 ν (unipotentBelow_le_unitriGroup e)],lintegral_const_mul]
 obtain z | ⟨_,hξ,hg⟩:=em' (F.IsNear b y);simp_all;obtain ⟨γ,k,u,l,rfl⟩:=exists_floorGroup_mul_unipotentBelow (unitriGroup_anti n hξ);gcongr;grw [← (ascConv_heisenbergMeasure_invariant l).1,lintegral_mconv_dirac,lintegral_eq_of_dirac_mconv_eq (ascConv_heisenbergMeasure_dirac_comm _ k),vR,pow_three,← Nat.mul_le_mul_left _ hj.step];simp [weylElem_mul_left_comm,k,pow_mul]
 refine j.rec (by simp [qJ,floorWeight]) (fun a ih hj hp ↦ ?_) hj hp
 lift a to Fin 𝔰.ϱ using hj;grw [ascConv_heisenbergMeasure_succ,lintegral_mconv_symm,Finset.prod_range_succ,pow_succ,mul_mul_mul_comm,← ih _ (hp · ·.step),← lintegral_mul_const,lintegral_le_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν l ↦ ?_]
 refine (Γ.com _ hg x o (ν.1.1*F.orthonormalPart).toRows₁).elim fun φ ⟨_,h,e⟩↦qE (-star p a)⁻¹
   (zR qX (e _)) fun t n↦⟨⟨_,inv_mem l,(zQ Γ.hasMatSize_box a.2 (by simpa [IsNear,qJ] using n) ⟨inv_mem (mul_mem (unipotentBelow_le_unitriGroup (heisenbergElem_mem_floorUnipotent a t).2) (unipotentBelow_le_unitriGroup l)),by simpa using hg⟩ hp.wG .refl).elim fun L k i↦by simpa [Γ.neg_star_mem_ofSize] using Γ.mul_mem_ofSize L (zJ (k.2 i) (HasMatSize.one ..))⟩,?_⟩
 grw [qJ,indicator_le_self ..,vB,ENNReal.mul_inv,ENNReal.inv_pow,← (h _).1,← show qJ .. = (floorWeight ..)⁻¹ from ite_eq_left ((mem_of_indicator_ne_zero n).imp (by grind))];gcongr;simp [weylElem_succ,weylElem_mul_left_comm,Subgroup.mem_inf.1 (heisenbergElem_mem_floorUnipotent ..)];rintro _ ⟨u,⟨k,c⟩,rfl⟩
 use (weylElem a.succ p*(P.heisenbergElem a t*ν)).1.1 *ᵥ F.orthonormalPart *ᵥ u,⟨by simpa using c,?_⟩ <;> simp [-mulVec_add,← mulVec_mulVec,-fromRows_mulVec,funext (g:=F.orthonormalPart *ᵥ u) (Sum.rec (by simpa [↓mulVec_mulVec] using! (congrFun k)) fun i↦unipotentBelow_mulVec_apply l (by simp) _ (by
     revert i;simp [level];lia))] <;> simp [mulVec_apply_eq_sum,weylElem,weylOn,level];lia
 repeat first | fun_prop | simp
lemma Gauge.qB (ht:t∈GT b) (h:Γ.HasMatSize j (q*x).1.1) (hk:F.IsPairingKernel b k d) y (hq:t⁻¹*q∈unipotentBelow b:=by simp):let f σ:=F.upperPairing (b+1) k (σ*x) (σ*y);(∀ᵐ σ ∂F.floorMeasure b,f σ≠0→ t.1.1 *ᵥ orbitPoint b σ∈Γ.vecsOfSize (j+6))∧∀ (ξ:Aˣ) y {q i M},Γ.HasFibreBound b q i M→ ∫⁻ v in Γ.vecsOfSize i,‖∫ σ,ψ (ξ*star (v+y)⬝ᵥT.splitGram *ᵥ t *ᵥ orbitPoint b σ)*f σ ∂F.floorMeasure b‖ₑ^2 ∂q≤ M*(Γ.Λ^(99*𝔰.n*(j+12))*((P.c/P.md ξ)^card ι * ∫⁻ σ,‖f σ‖ₑ^2 ∂F.floorMeasure b)):=by
 intro f
 refine (fun s↦⟨s,fun ξ y _ _ _ k ↦ ?_⟩) (ae_floorMeasure_mem.mono fun σ l k↦by
   simpa [orbitPoint,-mulVec_single] using vE (mul_mem l (inv_mem ht)) h
     (by simpa using (kL (unipotentBelow_le_unitriGroup (conj_mem_unipotentBelow l hq))).2 (hk.isNear_of_upperPairing_ne_zero k)))
 obtain ⟨⟨Z,_,ζ,_,K,μ,_,⟨_,rfl⟩,o,c,_,hμ,l⟩,A,_,e⟩:=Γ.hasFibreBound_floorQuadric,exists_factor_orbitPoint b (Φ:=f) (by fun_prop) (by simp +contextual [f,hk.z8])
 let r v:=(v,(Γ.vecsOfSize (j+6)).indicator (A <| t⁻¹.1.1 *ᵥ ·) v)
 have:Measurable r:=by fun_prop (disch:=apply zE)
 have H:=(IdentDistrib.of_ae_eq (f:=fun σ↦(t *ᵥ orbitPoint b σ,f σ)) (by fun_prop) (s.mp (ae_floorMeasure_mem.mono (by simp +contextual [r,indicator,not_imp_comm, *])))).trans
   (((zZ b ht).hasLaw.identDistrib (.comp {map_eq:=o} {map_eq:=rfl})).comp this)
 let g v (z:_ × _):=ψ (ξ*star (F.floorBasis b *ᵥ v+y)⬝ᵥT.splitGram *ᵥ z.1)*z.2
 have J v:=H.comp (u:=g v) (by fun_prop)
 have i v:=(J v).integrable_snd
   (hk.zI.1.bdd_mul (c:=1) (by fun_prop) (by simp))
 let N (p x:_ × _):=‖∫ w,P.ψ (ξ*star x.2⬝ᵥw) * ∫ z,(g (![0,p.1] ⊕ᵥ (p.2 ⊕ᵥ 0))∘r∘(F.floorBasis b *ᵥ ·)∘K) ((x.1,w),z) ∂ζ‖ₑ
 refine q0 k (G:=fun p w↦(∫⁻ x,N p (x,w))^2) (fun p↦⟨by fun_prop,?_⟩) fun v _ ↦ ?_
 · erw [funext fun _↦(sq _).trans (lintegral_prod_mul ..).symm,(H.comp (u:=(‖·.2‖ₑ^2)) _).lintegral_eq,lintegral_prod,lintegral_lintegral_swap]
   apply (lintegral_mono fun _↦lintegral_mul_le_Lp_mul_Lq _ .two_two ?_ ?_).trans;grw [lintegral_prod,lintegral_prod,← l,← lintegral_const_mul,← sq_lintegral_le _ _ fun _↦(rpow_inv_natCast_pow ..).le];simp;grw [lintegral_lintegral_mul,sq,lintegral_le_of_ae_imp (i _).integral_prod_left.prod_right_ae];intro x i;grw [plancherel_inequality ξ i,mul_left_comm,← lintegral_const_mul (μ x)];gcongr;grw [← hμ x w,← setLIntegral_le_lintegral,← setLIntegral_one,← sq_lintegral_le,setLIntegral_eq_of_support_subset,enorm_integral_le_lintegral_enorm]
   repeat first | fun_prop | simp +contextual [g,r,← ofReal_norm,qR]
 erw [(J _).integral_eq,integral_prod _ (i _),integral_prod _ (i _).integral_prod_left];grw [enorm_integral_le_lintegral_enorm];gcongr;rw [enorm_le_iff_norm_le,← ge_iff_le,← one_mul ‖_‖,← norm_psi (ξ*star v⬝ᵥ(![a.1,0] ⊕ᵥ (0 ⊕ᵥ (0 ⊕ᵥ a.2)))),← norm_mul];simp [← integral_const_mul];congr! 5;generalize e:K _=k;cases e▸c _;simp [g,r,F.gram_floorBasis];simp [fromBlocks_mulVec,dotProduct];grobner
lemma Gauge.qW {S:Set _} {i} {Φ:_→ _} (ξ u:Aˣ) (ε:ℕ) C (hk:F.IsPairingKernel (a+1) k d) x y (e:∀ s∈floorUnipotent a,F.g⁻¹.1*(simpleRootSum (d*s*d⁻¹)-simpleRootSum (s^ε))=ξ*simpleRootSum s) (o:∀ n∈floorUnipotent a,Φ n≠0→ n∈S∧Φ n≤ C*‖F.upperPairing (a+1) k (n^ε*x) (n*y)‖ₑ^2) (h:∀ m∈S,∃ t∈unitriGroup (a+1)⊓GT a,∃ q∈unipotentBelow (a+1),Γ.HasMatSize i (t*q*x).1.1∧∀ n∈S,∃ ν∈unipotentBelow a,u⁻¹.1•(((ν*(t*m*(t*n)⁻¹)).1.1-1) · (eStar a))∈Γ.vecsOfSize j) : ∫⁻ n,Φ n ∂heisenbergMeasure a≤ C*((P.c/P.md (ξ*u))^card ι*F.floorModulus a u*Γ.Λ^(100*𝔰.n*(i+j+31)) * ∫⁻ σ,‖F.upperPairing (a+1+1) k (σ*x) (σ*y)‖ₑ^2 ∂F.floorMeasure (a+1)):=le_of_not_gt fun H↦H.not_ge <| (exists_ne_zero_of_ae ae_mem_floorUnipotent H.ne_bot).rec fun n ⟨hn,k⟩↦(h n (by grind)).elim fun _ ⟨s,q,hq,h,hc⟩↦by
 obtain ⟨t,ht,r,hr,rfl⟩:=exists_floorGroup_mul_floorUnipotent s;obtain ⟨⟨_,rfl⟩,z,rfl⟩:=exists_eq_heisenbergElem_of_mem hr,exists_eq_heisenbergElem_of_mem hn;rw [lintegral_eq_of_dirac_mconv_eq ((heisenbergMeasure_mconv_dirac hr).2.trans (heisenbergMeasure_mconv_dirac (mul_mem hr hn)).1.symm),lintegral_eq_of_dirac_mconv_eq (dirac_mconv_heisenbergMeasure_comm ht)]
 refine qE u ((Γ.qB (b:=a.succ) ht h hk y (by simpa using mul_mem hr.2 hq)).2 (-ξ*star u) (u⁻¹.1•t.1.1 *ᵥ inclMatrix A (↑) *ᵥ z.1) qX) fun v k↦(o _ ?N k).imp (by simpa using hc _ ·) (le_trans' ?_)
 any_goals rw [a.val_succ,hk.zI.2,integral_congr_ae (ae_floorMeasure_mem.mono fun σ l↦have c:=conj_mem_floorUnipotent ?N σ l
   .trans (by simp [↓conj_pow]) ((hk.law (pow_mem c.2 ε) c.2 (σ*x) (σ*y)).trans ?_))]
 all_goals simp only [↓e _ ‹_›,mul_heisenbergElem (inv_mem ht),inv_mul_cancel_right,heisenbergElem_inv,← add_assoc,heisenbergElem_mul,heisenbergElem_mem_floorUnipotent,simpleRootSum_conj_heisenbergElem,← form_mulVec_mulVec t _ (orbitPoint _ _),mulVec_add,inclMatrix_mulVec_floor_block a.2,inv_mem, *]
 simp [← inverse_star_unit];ring
end
