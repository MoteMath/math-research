import Lib.PadicHodge.Crystalline.GoodCriterion
import New.Lift.CokernelKillers
section
open Algebra Finset IsDiscreteValuationRing LinearMap Module Polynomial Submodule Lift.Pairing Lift.KummerChart.JumpLattice
noncomputable abbrev Lift.KummerChart.wK {p:ℕ} [ThePrime p] [Γ:GroupOverGp p] {k:KummerChart Γ} O:JumpLattice O:=⟨⟨O,actionRep O O χ⟩,fun _↦{-1},_,.of_cyclotomic_pow 1 (by simp),by simp⟩
namespace Lift.KummerChart.PairingSide
attribute [-simp] Equiv.Perm.coe_inv map_mul map_one smul_right_inj
variable {p:ℕ} [ThePrime p] [Γ:GroupOverGp p] {k:KummerChart Γ} {O} {S S':PairingSide O} {c:S.C} {i:Letter} (S:PairingSide O) (i:Letter) (S':PairingSide O) (c':S.C) (i':Letter) (e:ℕ) (o₁ o':ℕ→ ℤ→ ℤ)
lemma kU (i:Letter):i.stepBack 0=i:=rfl
abbrev kJ:S.Hom S.extLattice:=⟨.inl ..,by aesop (add simp extensionRep)⟩
noncomputable abbrev wJ:=S.projTriv.wittMap.restrictScalars ℤ_[p]∘ₗS.extLattice.kisinLoc.subtype.restrictScalars _
noncomputable def qZ o:=(S.constantAt i).range.comap S.wJ⊓(s21_q6 (S.extLattice.withExponents i o)).comap (S.extLattice.kisinLoc.subtype.restrictScalars _)
noncomputable def zH o:=S.extLattice.withExponents i o⊓(S.projTriv.wittMap.restrictScalars _).ker
def wD (e:ℕ) (A:S.extLattice.kisinLoc →+ S.extLattice.kisinLoc):=∀ ⦃i o x⦄,x∈S.qZ i o→ A x-p^e•x∈s21_z0 (S.zH i o)
abbrev SidePairing:=Pairing S.toGalLattice S'.toGalLattice
def zW:={x∈S.extLattice.kisinLoc | S.projTriv.wittMap x=p^e•S.constantAt i' c'∧x∈S.extLattice.withExponents i' o₁∧x∈s21_q6 (S.extLattice.withExponents i' o')}
def vW (cut:_→ Prop) l (o o' z:_→ ℕ→ ℤ→ ℤ) (Q:Prop):=∃ d r,(S.zW c' i' e (o i') d).Nonempty∧cut (i'.stepBack r)∧∀ a,∀ u∈S.U (i'.stepBack a),∀ v∈S'.U (i'.stepBack a),-z i' a (-u-v-1)-d a u< min (-v) (o' i' a v)∧(Q→ stdExponent l a u≤ o i' a u ∧ -frobExponent r 0 (z (i'.stepBack r)) a (-u-v-1)-d a u< min (o' i' a v) (frobExponent l 0 (o' (i'.stepBack l)) a v))
variable {S S':PairingSide O} {c:S.C} {i:Letter} {c':S'.C} {l κ s e e':ℕ} {o} {o' o₁:ℕ→ ℤ→ ℤ} {o₂ o₃ x w y} {P:S.SidePairing S'} {n} (hK:n∈P.thirdSide.zW 1 (i.stepBack l) κ o₂ o₃∧∀ a,Antitone (o₂ a)) (hx:x∈S.zW c i e o₁ o) (hw:w∈S.zH i o) (hy:y∈S'.zH i o') (H:∀ a,∀ u∈S.U (i.stepBack a),∀ u'∈S'.U (i.stepBack a),0< frobExponent l 0 o₂ a (-u-u'-1)+o a u+o' a u') (g:galMonoid) (I:Finset ((_:ℕ) × ℤ))
@[simp] lemma wL:∀ y,wittFst _ (S.kJ.wittMap y)=y∧S.projTriv.wittMap (S.kJ.wittMap y)=0:=diagTensor_induction (by simp)
lemma wX {u v:_→ _} (h:∀ i,u i∈S.extLattice.letterPart i∧v i∈S'.extLattice.letterPart i) (f:∀ i,P.IsSafe κ (u i) (v i)):P.IsSafe κ (∑ i,u i) (∑ i,v i):=by
 have Z i:=Fintype.sum_eq_single i fun l n↦show P.wittPairing (wittFst _ (u l))
   (wittFst _ (v i))=0 from (isUnit_teichmuller_sub (Units.ext.mt n)).smul_eq_zero.1
   (by simpa [by simpa [mem_letterPart_iff_mulZeta] using h,sub_smul] using! (diagTensor_induction fun _ _↦diagTensor_induction (by simp [mulZeta,modPairing]):∀ u v,P.wittPairing (wittFst _ (S.extLattice.mulZeta.wittMap u)) (wittFst _ v)=P.wittPairing (wittFst _ u) (wittFst _ (S'.extLattice.mulZeta.wittMap v))) (u l) (v i))
 simp_all [IsSafe,smul_sum,sum_mem]
lemma kM (W:Submodule BdRPlus _) {μ} (h:μ∈S.forms) (m:∀ t,μ (.mk 1 t)∈W):∃ ν∈S.extLattice.forms,S.extLattice.ainfLattice≤ (W.restrictScalars _).comap ν∧ν∘ₗS.kJ.wittMap=μ:=by
 let Λ:=(μ.restrictScalars _∘ₗDiagTensor.mk 1).liftBaseChange Bcris
 have H (g:k.Γ') y:Λ (tensorAction _ (toGp g.1) (S.ρ g) y)=toGp g.1•Λ y:=by
   induction y <;> simp_all [Λ,tensorAction,h _,smul_def']
 choose v F using (S.α · |>.2)
 have f c (g:k.Γ'):=by simpa [↓H,Λ] using congr(Λ $(F c g))
 choose a b d using fun c↦by simpa using BdR.exists_sub_mem_of_smul_sub_mem k.Γ' W (f c ·▸m _)
 let e:=finBasis ℤ_[p] S.C
 let ⟨ν,q⟩:=S.trivLattice.exists_functional_extend (e.constr ℕ ((Λ∘v-algebraMap _ _∘a)∘e))
 use μ ∘ₗ ↑S.wittFst+ν∘ₗS.projTriv.wittMap,fun (t,c) g ↦ ?_,span_le.2 ?_,LinearMap.ext
   (diagTensor_induction ?_) <;> simp [Λ,sum_mem,smul_of_tower_mem,add_mem_cancel_left, *]
 rw [← e.sum_repr c];simp [*,extensionRep,-Basis.sum_repr,smul_sum,smul_sub,smul_comm,h t,add_assoc]
lemma wD.jV {A P x} (H:S.wD e A) (l:s21_z0 (S.zH i o)≤ P) (m:x∈P) (y:x∈S.qZ i o):A x∈P:=(sub_mem_iff_left _ (nsmul_mem m _)).1 (l (H y))
lemma zF:s21_z0 (S.zH i o)≤ S.qZ i o:=fun _ m↦⟨ker_le_comap _ m.2,smul_sub_mem_withExponents m.1⟩
lemma zT (hw:w∈S.zH i o):∃ y∈S.withExponents i o,S.kJ.wittMap y=w∧(w∈S.extLattice.kisinLoc→ y∈S.kisinLoc):=by
 obtain ⟨y,rfl⟩:w∈S.kJ.wittMap.range:=(lTensor_exact _ .inl_snd snd_surjective _).1 hw.2
 have l:=mem_letterPart_iff_letterProj.2
   (by simpa [← Hom.wittMap_letterProj] using congr(wittFst _ $(mem_letterPart_iff_letterProj.1 hw.1.1.2)))
 use y,⟨⟨?y,l⟩,fun a u hu μ hμ ↦ ?_⟩,rfl,fun m↦(wL y).1▸coordRetract_of_mem_kisinLoc m hw.1.1.1▸S.kJ.map_coordRetract
   ⟨y,?y⟩ ⟨_,_⟩ rfl▸by simp
 exact hw.1.1.1.imp fun _ ↦ .imp_right (.imp (.imp fun _ ↦ .imp_right (by
   simpa using wittMap_mem_ainfLattice (.fst ..) ·)) fun e a μ m ↦
   (kM ⊤ m (by simp)).elim (by simp_all [eq_comm]))
 obtain ⟨ν,e,f,g⟩:=kM _ (comp_letterProj_mem_forms hμ.1) hμ.2;simpa [↓← valueAt_comp_wittMap,JumpLattice.valueAt,mem_letterPart_iff_letterProj.1,← phi_pow_smul_mem_letterPart_iff, *] using hw.1.2 a u hu ν ⟨e,(f <| letterProj_mk_mem_ainfLattice ·)⟩
lemma zA (hK:S.KillsCokernel i κ s) c:(S.zW c i κ (raisedAtE (-s)) (raisedAtE (-s))).Nonempty:=have ⟨x,⟨m,t⟩,e⟩:=(exists_lift_of_mem_liftIdeal hK).choose_spec _ (constantAt_mem_locLetterPart c)
 ⟨_,frobEUnit_zpow_smul_mem_kisinLoc.2 m,by simp [e,inv_smul_eq_iff,frobEUnit_pow_smul,frobE_eq];module,
   frobEUnit_zpow_mem_withExponents 0 (-s) t,
   smul_sub_mem_withExponents (frobEUnit_zpow_mem_withExponents _ _ t)⟩
lemma vH:∃ A,S.wD (∑ q∈I,cost q.1 q.2) A∧∀ ⦃i c x⦄,x∈S.qZ i c→ ∀ c',(∀ a,∀ u∈S.U (i.stepBack a),∀ n,c a u≤ n→ n< c' a u→ ⟨a,n⟩∈I)→ A x∈S.qZ i c':=I.induction_on_max_value (·.2) ⟨.id _,by simp [wD],fun _ _ _ m _ J ↦
 m.imp_right fun m g↦mem_withExponents_of_le (m g) (by simp_all)⟩ fun ⟨a,n⟩ I q N ⟨A,R,Y⟩↦by
 obtain ⟨_,t,υ,Z⟩:=S.extLattice.kR a n
 let B:=p^cost a n • .id _ + ∑ l,AddMonoidHom.mk' (S.extLattice.coordRetract <| υ•⟨_,smul_sub_mem_zTau_kisinLocAinf (t l) ·.2⟩) (by simp [← map_add,add_sub_add_comm])
 have T:S.wD (cost a n) B:=fun i c x ⟨⟨_,f⟩,m⟩↦by
   simp [B] at f ⊢
   exact sum_mem fun l _↦⟨coordRetract_mem_withExponents _ (smul_mem _ υ (smul_sub_mem_zTauUnit_smul_of_deep x.2 (m _))),by simp [S.projTriv.map_coordRetract _ 0,← f,constantAt,gal_smul_letterProj,k.galMonoid.smul_def]⟩
 refine ⟨B.comp A,fun i c x m↦(sub_mem_iff_left _ (T (R.jV zF m m))).1 (by
   simp [← smul_sub,R m,q,pow_add,mul_smul,nsmul_mem]),fun i c x m d J ↦ ?_⟩
 have Y:=Y m (fun b u↦ite (b=a∧d b u=n+1) n (d b u))
   (have:=(J · · · (n+1));by clear * - this J N q;grind)
 refine (T.jV zF Y Y).imp_right fun H g↦mem_withExponents_of_mem_hodgeFil (H g) fun b u v l μ m ↦ ?_;obtain ⟨y:(A x).1∈s21_q6 _,rfl,e⟩:=Y.2,(ite_ne_right_iff.1 l.ne).1
 obtain ⟨c,f⟩:=Z _ (A x).2 μ m.1 (BdR.exists_sub_mem_of_smul_sub_mem _ _ (by
   simpa [e,↓valueAt_smul_sub (A x).2.1 m.1] using! y ⟨_,·,rfl⟩ |>.2 _ u v μ m))
 have F:=qL m.1 (p^_•⟨_,(A x).2.1⟩ + ∑ l,υ•⟨_,smul_sub_mem_zTau_kisinLocAinf (t l) (A x).2⟩) ((valueField _).1.2 c) (by simpa using f)
 erw [e,valueAt_smul_sub (B _).2.1 m.1];simpa [B,coordRetract_of_mem_kisinLoc,nsmul_mem,smul_sub,jY] using sub_mem (galMonoid_smul_mem_hodgeFil g F) F
include hx in
lemma jR (H:∀ a,∀ u∈S.U (i.stepBack a),∀ n,o a u≤ n→ n< o' a u→ ⟨a,n⟩∈I) (he:e + ∑ n∈I,cost n.1 n.2≤ e'):(S.zW c i e' (s21_v7 o₁ o') o').Nonempty:=by
 obtain ⟨⟨s,rfl⟩,A,R,D⟩:=he.dest,S.vH I
 have y {o} H:p^s•⟨x,hx.1⟩∈S.qZ i o:=smul_of_tower_mem _ _ ⟨⟨p^e•c,by simp [hx.2]⟩,H⟩
 obtain ⟨z,-,D⟩:=y (smul_sub_mem_withExponents hx.2.2.1),D (y hx.2.2.2) o' H
 exact ⟨A _,(A _).2,(sub_mem_ker_iff.1 (R z).2).trans (by simp [hx.2];module),zU (R.jV (P:=s21_z0 (withExponents ..)) (fun _↦(·.1)) (nsmul_mem hx.2.2.1 _) z) D,D⟩
lemma zX (hx:x∈S.zW c i e o₁ o) (g:galMonoid):k.zTauUnit⁻¹•(g•x-x)∈S.zH i o:=⟨JumpLattice.smul_sub_mem_zTauUnit_smul_of_deep hx.1 (hx.2.2.2 g),by simp [k.galMonoid.smul_def,hx.2,smul_comm,constantAt,gal_smul_letterProj]⟩
lemma qH (hx:x∈S.zW c i e o₁ o) (hw:w∈S.zW c i e o₂ o₃):w-x∈S.zH i (o₁⊓o₂):=⟨sub_mem (mem_withExponents_of_le hw.2.2.1 (by simp)) (mem_withExponents_of_le hx.2.2.1 (by simp)),by simp_all [zW]⟩
lemma zP (hw:w∈S.zW c (i.stepBack l) e o o'):FrobGroup.φ^l•w∈S.zW c i e (frobExponent l 0 o) (frobExponent l 1 o'):=⟨phi_pow_mem_kisinLoc hw.1,by simp [hw.2.1,smul_comm,phi_pow_smul_constantAt,Equiv.Perm.coe_inv],qD hw.2.2.1,
 fun g↦have Y:=qD (zX hw g).1
 Eq.subst (by simp [← frobGroup_smul_smul,← zTauUnit_smul,smul_sub,smul_phi_pow_comm])
   (mem_withExponents_of_mem_hodgeFil (smul_mem _ (FrobGroup.φ^l•k.zTau) Y) fun a u v c μ e↦have c:a< l:=by lia
   by simpa [c,zTau] using mul_mem_hodgeFil (phiInvToBdR_mem_hodgeFil_one_iff.2 ((frobE_dvd_phi_pow_tau c).mul_right _)) (Y.2 a u v μ e))⟩
lemma s21_j0 i:letI B:=JumpLattice.wittPairing (C:=S.kerLattice) (.lsmul O _);(∀ w,B (P.thirdSide.constantAt i 1) w=S.letterProj i w)∧∀ n w y,DiagTensor.map (mkQ _∘ₗP.toZp)
   (JumpLattice.wittPairing (C:=wK O) P.thirdPairing n (JumpLattice.wittPairing (C:=S.tensorLattice S') (TensorProduct.mk ..) w y))=P.wittPairing (B ((projTriv _).wittMap n) w)
   y:=⟨diagTensor_induction (by simp [constantAt,qO]),diagTensor_induction fun _ _↦diagTensor_induction fun _ _↦diagTensor_induction (by simp [thirdPairing,modPairing,mul_assoc,-nsmul_eq_mul];simp [← map_nsmul,↓nsmul_quot_eq_zero])⟩
include hK hw hy H in
lemma SidePairing.kI:IsSafe P κ (zTauUnit•w) y∧IsSafe P κ w (zTauUnit•y):=by
 obtain ⟨⟨w,a,⟨⟨⟩⟩⟩,⟨⟨-,N,M⟩,A⟩,y,b,⟨⟨⟩⟩⟩:=zT hw,hK.imp zP (· <| · - l),zT hy
 refine (by simpa [smul_comm _ k.zTauUnit,mem_letterPart_iff_letterProj.1 a.1.2,s21_j0 i,N,IsSafe,smul_smul,-nsmul_eq_mul] using! ·) (mem_span.1 ((wK O).tau_pow_smul_mem_ainfLattice_of_chi 1 ((S.tensorLattice S').jI P.thirdPairing_equivariant M.1 (jI (b:=TensorProduct.mk ..) (c'':=fun a v↦1-frobExponent l 0 o₂ a (-v-1)) (by simp) a b ?_) ?_)) (comap (k.z.1•(DiagTensor.map (mkQ _∘ₗP.toZp)).restrictScalars _) (smallPart P.m)) fun _ ⟨t,e⟩↦e▸⟨_,smul_of_tower_mem _ (P.toZp t) (teichmuller_mem_wittMaxIdeal (k.chart.4 <| k.seriesMap_X▸·.map _)),by
   simp [k.z_eq_teichmuller,mul_smul,← map_smul,smul_def',smul_comm]⟩)
 all_goals
   clear * - A H;intro a u _ t _ v;obtain _ := @A a (-v-1),@A a u;grind
include hK hx hy H in
lemma SidePairing.k2:P.IsSafe κ (g•x-x) (g•y):=by simpa using (P.kI hK (zX hx g) (add_mem ⟨smul_sub_mem_withExponents hy.1 g,by simp_all [zH,k.galMonoid.smul_def]⟩ hy) H).1
lemma SidePairing.z4 (cut Q:_→ Prop) (l:k.Letter→ ℕ) {o o' z z':_→ _} (hl:∀ i,IsLeast {a | 0< a∧cut (i.stepBack a)} (l i)) (H:∀ i,cut i→ S.vW S' c i e cut (l i) o o' z (Q i)∧S'.vW S c' i e' cut (l i) o' o z (¬Q i)∧(P.thirdSide.zW 1 i κ (z i) (z' i)).Nonempty∧∀ a,Antitone (z i a)) {E} (he:e+e'+κ≤ E:=by omega):P.ScaledCupBounds E c c':=by
 simp only [vW,Set.Nonempty,and_assoc,← exists_and_right,← exists_and_left] at H
 choose! v _ r' x' _ r x a s f b t f' K using H
 let d P i:=ite ((P⊓cut) i) 0 (l i)
 have q i:(∀ P,cut (i.stepBack (d P i)))∧d ⊥ i=d ⊤ (k.letterFrob⁻¹ i)+1:=by
   have z a:(k.letterFrob⁻¹ i).stepBack a=i.stepBack (a+1):=rfl
   clear * - hl z;simp [d,IsLeast,lowerBounds,-pow_ite] at *
   grind [z (l i-1),z 0,kU]
 let u {L:JumpLattice O} (y:_→ L.Ambient) P := ∑ i,FrobGroup.φ^d P i•y (i.stepBack (d P i))
 have B i l a h:(Letter.stepBack i l).stepBack (a-l) =
   _:=congr($(pow_mul_pow_sub k.letterFrob h)⁻¹ i)
 replace a P i:=zP (a _ ((q i).1 P));replace b P i:=zP (b _ ((q i).1 P))
 have Y:=by simpa [zW,withExponents] using And.intro a b
 have F L y:FrobGroup.φ • @u L y ⊤ = u y ⊥ := by
   rw [smul_sum,← Equiv.sum_comp k.letterFrob⁻¹];simp [u,q,pow_succ',mul_smul]
 refine .of_isSafe _ (u x ⊤) (u x Q) (u x' ⊤) he ?_ ?_ ?_ fun g↦⟨fun h ↦ ?_,?_,?_,?_⟩ <;>
   simp only [↓F,u,smul_sum,← sum_sub_distrib]
 iterate 3 simp [Y,← smul_sum,constantAt,sum_letterProj]
 all_goals refine wX (by simp [sub_mem,gal_smul_mem_letterPart,Y]) fun i↦have c:=(hl i).1.2
   have G {j} m:=P.k2 (K (.stepBack i j) m) (a Q i)
     (qH (b ⊤ i) (b ⊥ i))
   have T {j} m U V W H:=(P.kI (K (.stepBack i j) m) (qH (a U i) (a V i)) (zX (b W i) g) H).2;?_
 apply P.k2 (K _ ((q i).1 ⊤)) (a ..) ⟨smul_sub_mem_withExponents (b ..).2.2.1 h,by simpa [inv_smul_eq_iff] using (zX (b ⊤ i) h).2⟩
 clear * - B f q;grind
 all_goals by_cases hi:cut i <;> by_cases n:Q i <;> try simp [d,IsSafe, *];done
 map_tacs [convert T (t i hi) ⊤ Q ⊤ _;apply G (s i hi);apply G c;convert T c Q ⊥ ⊥ _]
 all_goals clear * - f f' B c hi n;simp [d, *] <;> grind
variable (h:S.SidePairing S') {a κ η H W:ℕ} {b:Letter→ ℕ} {ε:Letter→ ℤˣ} {i:Letter} {c:S.C}
lemma zC {lo o n b} (hx:(S.zW c i κ lo o).Nonempty) (hs:NoMultipleNear p n b) hi (H:∀ a,∀ u∈S.U (i.stepBack a),∀ y,o a u≤ y→ y< hi a u→ a=0∧y∈twoWindows n b ∪ twoWindows n (-b)):(S.zW c i (κ+(8*n+4)*differentExp) (s21_v7 lo hi) hi).Nonempty:=jR hx.some_mem
 (.image (.mk 0) (twoWindows n b ∪ twoWindows n (-b))) (by grind) (by
   grw [sum_le_card_nsmul _ _ k.differentExp,card_image_le];repeat grw [card_union_le]
   all_goals grind [cost,NoMultipleNear,padicValInt.eq_zero_iff,Int.card_Icc])
lemma SidePairing.q4 (hK:∀ i,h.thirdSide.KillsCokernel i κ a∧S.KillsCokernel i κ a∧S'.KillsCokernel i κ a) (hs:∀ i,NoMultipleNear p (6*(a+η+W)) (b i)) (hU:∀ i,IsInJumpWindow η (-ε i) (b i) W (S.U i)∧IsInJumpWindow η (ε i) (b i) W (S'.U i)) (h₀:(∀ i u,u∈S.U i∨u∈S'.U i→ u∉Ico (-↑a) 0)∨IsUnramified∧5≤ p∧1≤ η∧∀ i,S'.U i ⊆ .Icc (-η) 0) (hH:3*(κ+(8*(6*(a+η+W))+4)*differentExp)≤ H) c c':h.ScaledCupBounds H c c':=by
 let D:=raisedAtE (2*a+η)
 obtain t | ⟨hk,hp,t⟩:=h₀
 have y i:=zC
   (zA (hK i).2.2 c') (hs i) D ?_
 let l:=0;rotate_right;let l:=1
 have y i:=zC (i:=i) ⟨_,zP (l:=1) (zC (zA (killsCokernel_of_isUnramified 0 0 ?_ hk hp) c') (hs i) D ?_).some_mem⟩ (hs i) (D ·.pred) ?_
 any_goals refine h.z4 ⊤ (ε · = 1∧l=0) 1 (by
   simp;tauto) fun i _↦⟨⟨_,0,zC (zA (hK i).2.1 c) (hs i) D ?_,⟨⟩,?_⟩,⟨_,ite (ε i=1) l 0,y i,⟨⟩,?_⟩,zA (hK i).1 1,?_⟩
 all_goals clear * - t hU;rintro ⟨⟩ <;> simp +zetaDelta [Antitone,← Units.val_eq_one,raisedAtE] <;> intros <;> and_intros <;> grind
end Lift.KummerChart.PairingSide
namespace Lift.KummerChart.JumpLattice
attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule
@[grind] def vJ (o:ℕ→ ℤ→ ℤ) a u b v:=o b v+ite (b=a∧v=u) 1 0
seal Finset.univ Finset.sum Finset.prod in
lemma qU {p} [ThePrime p] [Γ:GroupOverGp p] {k:KummerChart Γ} {O} {L:JumpLattice O} o (hk:IsUnramified) {i u n} (hn:L.jumpMultiplicity i u≤ n) b l (f : .stepBack l b=i) (ho:∀ v∈L.U i,v< u→ o b u< o b v) (x:Fin (k.f*n+1)→ kisinLoc) (X:∀ j,↑(x j)∈L.withExponents l o):∃ᵉ (c:_→ ℤ_[p]) (j),c j=1 ∧ ∑ j,c j•x j∈s21_z0 (L.withExponents l fun a v↦o a v+ite (0=a) 1 0)⊔s21_z0 (withExponents l (vJ o b u)):=by
 obtain ⟨⟨r,q,ν,R⟩,rfl⟩:=exists_span_formsOfType_mod_pred i u,f;choose t ht using fun l m↦mem_hodgeFil (n:=o b u).1 (valueAt_mem_of_hodgeFil_le _ (X l) (ν m).2)
 let U:=(Matrix.of (thetaBdR <| t · ·)).toLin'.range
 choose s z H B using exists_auerbach (finBasis _ U) (.proj ·∘ₗU.subtype)
   (by bound) (.id _) fun _↦continuous_bot
 choose A hA using fun l m↦theta_surjective ⟨(z m).1 l,by simpa using B l m⟩
 choose w y hw using fun l m↦by simpa [Chart.frobE,Fin.exists_fin_succ_pi] using (k.exists_dvd_sub_sum_z_pow 0 (by simp [hk.2]:_=1) (k.coord₀ (FrobGroup.φ^b•A l m)))
 have S r:=sum_smul_mem _ r (t:=univ) fun m _↦X (s m)
 obtain ⟨a,e,n⟩:=Fintype.not_linearIndependent_iff.1 (mt (·.fintype_card_le_finrank (b:=w) (R:=ℤ_[p])) (by simp [finrank_wittFq];grw [finrank_range_le,finrank_fin_fun,q,hn,mul_comm]))
 choose l c g using by simpa [addVal_le_iff_dvd] using Finite.exists_min (addVal _∘a)
 rw [_root_.funext g] at e n;simp [mul_smul,← smul_sum,funext_iff] at e n
 refine ⟨c,l,by simpa [n] using g l,
   Eq.subst (by ext;simp [-sum_add_distrib,coordRetract_of_mem_kisinLoc,smul_sum,← hw,coordRetract_sum (y:=⟨_,(S _).1.1⟩) _ rfl,sub_smul,smul_sub,@sum_comm (Fin (finrank _ U)),← smul_assoc,← sum_smul,e.resolve_left n.1,S_smul]) (sum_smul_mem _ c (t:=univ) fun l _↦have T:=sub_mem (X l) (S (FrobGroup.φ^b•A l ·));add_mem_sup
   (s:=k.E • ∑ m,y l m•x (s m)) (t:=coordRetract (⟨_,(X l).1.1⟩-⟨_,(S _).1.1⟩))
   (by simpa using! frobEUnit_zpow_mem_withExponents 0 1 (S _)) (coordRetract_mem_withExponents _ (mem_withExponents_of_mem_hodgeFil T fun d v _ e μ m ↦ ?_)))⟩
 obtain ⟨rfl,rfl⟩:=by simpa [vJ] using e.ne
 refine (sub_mem_iff_left _ (sum_mem fun m _↦smul_of_tower_mem _ _ ?_)).1 (by simpa [valueAt] using! (valueAt_mem_of_hodgeFil_le _ T (R μ m).choose_spec))
 simpa [ht,vJ,algebraMap.smul,sub_mul,sum_mul,add_comm,smul_distrib_smul,smul_sub,smul_sum,-Units.val_zpow_eq_zpow_val] using! mul_mem_hodgeFil (n:=o d v) (algebraMap_mem_hodgeFil_one_iff (y:=t l m - ∑ i,A l i•t (s i) m).2 (by simpa [smul_def',← z.coord_apply,mul_comm, *] using! congr($(z.sum_repr ⟨_,Pi.single m 1,rfl⟩).1 l).symm)) (subset_span rfl)
end Lift.KummerChart.JumpLattice
namespace Lift.KummerChart
attribute [-instance] LieRinehartAlgebra.toIsScalarTower
variable {p:ℕ} [ThePrime p] [Γ:GroupOverGp p] {k:KummerChart Γ} {O} {L:JumpLattice O} {x:L.Ambient} {l A:ℕ} {i:Letter} {o:ℤ→ ℤ} {S:PairingSide O} (hl:0< l) (l:ℕ)
abbrev JumpLattice.vQ (o:ℤ→ ℤ) a u:=stdExponent l a u+ite (0=a) (o u) 0
noncomputable def JumpLattice.v8 (A:ℕ) i:=(L.locLetterPart l i).restrictScalars ℤ_[p]⊓s21_q6 (withExponents i (vQ l fun _↦A))
open algebraMap
lemma JumpLattice.vT {l A:ℕ} {i:Letter} {o:ℤ→ ℤ} (hl:0< l) {w:_→ WittFq k.f} {t} (e:∀ s,s-w s=k.E*t s) {m} {v:Fin m→ _} (hv:∀ a,v a∈L.v8 l A i) {c} (hc:c∈L.v8 l A i) n (s:_→ _) (f:ℤ[X]) (ho:∀ u,o u≤ A) (H : ∑ a,s a•v a-aeval k.E f•c∈withExponents i (vQ l o)):let d := ∑ a,(w (t^[n] (s a)):k.S)•v a-f.coeff n•c
 d∈L.v8 l A i∧d∈withExponents i (vQ l (if o ·≤ n then 0 else A)):=by
 induction' n using Nat.caseStrongRecOn with n ih generalizing s f o <;> have K:=by simpa [add_smul,mul_smul,← smul_sum,add_sub_add_comm,← smul_sub,Int.cast_smul_eq_zsmul] using (funext (eq_add_of_sub_eq <| e <| s ·)▸f.X_mul_divX_add▸H :)
 refine ⟨?a,mem_withExponents_of_le (zU (lo:=vQ l (1⊓o ·)) ((add_mem_cancel_left (by simpa using! (frobEUnit_zpow_mem_withExponents 0 1 (sub_mem (sum_smul_mem _ _ fun a _↦(hv a).1.2) (smul_mem _ _ hc.1.2))))).1 (mem_withExponents_of_le K)) ?a.2)⟩
 exact sub_mem (sum_mem fun a _↦⟨smul_mem (locLetterPart ..) _ (hv a).1,fun ⟨_,γ,rfl⟩↦by simpa [fixes,S_smul,frobGroup_smul_smul,smul_sub] using (smul_mem _ _ ((hv a).2 ⟨_,γ,rfl⟩))⟩) (by bound)
 simpa using ih _ .refl _ f.divX ((sub_one_lt _).le.trans <| ho ·) (Eq.subst (by
   simp [inv_smul_eq_iff];rfl) (frobEUnit_zpow_mem_withExponents 0 (-1) (sub_mem K (mem_withExponents_of_le (ih 0 bot_le _ _ ho H).2))))
lemma JumpLattice.jT {l:ℕ} (hl:0< l) i (H:x∈L.valueFieldPoints (frobKisinAinf l)∧∀ μ∈L.forms,∀ g:k.Γ',toGp g•μ x-μ x∈hodgeFil A):L.letterProj i x∈L.v8 l A i:=(fun y↦⟨y,fun ⟨_,γ,rfl⟩↦mem_withExponents_of_mem_hodgeFil (smul_sub_mem_withExponents y.2 _) (·.rec (fun _ _ _ _ m↦by
 simpa [vQ,stdExponent,hl,↓valueAt_smul_sub y.1.1 m.1] using! H.2 _ (comp_letterProj_mem_forms m.1) γ) (by simp))⟩) (letterProj_mem_of_valueFieldPoints H.1)
lemma PairingSide.v2 {l:ℕ} (hl:0< l) (hk:IsUnramified) {κ s g δ N:ℕ} (hK:S.KillsCokernel (i.stepBack l) κ 0) (hz:S.KillsCokernel i 0 s) (hN:s+g * ∑ t∈Finset.range l,p^t=N) (hg:∀ t< l,∀ u∈S.U (i.stepBack t),u≤ g) (hA:N< A) (hq:3*k.e≤ p^l) (hδ:k.e*A≤ p^l*δ) c:(S.zW c i (κ+4*δ) (vQ l fun u↦min A (-u-N)) (vQ l fun _↦A)).Nonempty:=by
 have ⟨y,hy,F,H,_⟩:=zA hz c
 have ⟨f,hf,H⟩:∃ f:ℤ[X],f.IsMonicOfDegree N∧aeval k.E f•y∈withExponents i fun a↦(ite (a< l) g 0 - ·):=hN▸l.rec ⟨_,isMonicOfDegree_X_pow ..,by
   simpa [frobEUnit_pow_smul] using! frobEUnit_zpow_mem_withExponents 0 s H⟩ fun l ⟨f,hf,H⟩↦⟨_,Eq.subst (by grind [sum_range_succ]) (((((isMonicOfDegree_X_sub_one ↑p).pow (p^l)).add_right (q:=p) (by simp [NeZero.pos])).pow g).mul hf),by simpa [frobEUnit_pow_smul,frobE_eq,phi_pow_smul_z,hk.1,mul_smul] using! frobEUnit_zpow_mem_withExponents l g H⟩
 have ⟨_,r,v,E⟩:=mem_span_set'.1 (frame_theorem.1.2.1 l A δ hq hδ _ ⟨(mem_withExponents_stdExponent_iff.1 (mem_withExponents_of_le H)).1,(smul_mem _ _ hy).2⟩)
 apply_fun letterProj i at E;simp [mem_letterPart_iff_letterProj.1 H.1.2] at E
 choose w t et using (by simpa [Algebra.smul_def] using k.exists_dvd_sub_sum_z_pow 0 (by simp [hk.2]:_=1) ·)
 obtain ⟨⟨⟨b,d⟩,d₁⟩,a,d₂⟩:=vT hl et
   (jT hl i <| v · |>.2) (ZeroMemClass.zero_mem _) N r 0
   (min_le_left _ <| g - ·) (by simpa [E] using nsmul_mem (mem_withExponents_of_le H) _),
   vT hl et (jT hl i <| v · |>.2.imp (.imp S.projTriv.wittMap_mem_frobKisinAinf fun H _↦H _∘S.projTriv.comp_wittMap_mem_forms) fun H _↦H _∘S.projTriv.comp_wittMap_mem_forms) ⟨constantAt_mem_locLetterPart c,(by simp [k.galMonoid.smul_def,constantAt,gal_smul_letterProj ·])⟩ N r (p^(4*δ)•f) (fun _↦le_rfl) (by simp [by simpa using congr(S.projTriv.wittMap $E),F,-nsmul_eq_mul])
 obtain ⟨v,⟨hv,n⟩,q⟩:=(exists_lift_of_mem_liftIdeal (f:=p^κ) (by simpa using (phi_pow_mem_liftIdeal_iff l).2 hK)).choose_spec _
   ⟨frobEUnit_zpow_smul_mem_kisinLoc.2 a.1.1,frobEUnit_zpow_mem_withExponents 0 (-A) d₂ (by clear * - hA;grind)⟩
 exact ⟨_,sub_mem (nsmul_mem b.1 (p^κ)) (frobEUnit_zpow_smul_mem_kisinLoc.2 hv),by
   simp [q,smul_comm (_^A),← hf.1,hf.2,-nsmul_eq_mul];module,sub_mem (nsmul_mem (mem_withExponents_of_le d₁ (by clear * - hA;grind)) _)
   (frobEUnit_zpow_mem_withExponents 0 _ n),
   sub_mem (nsmul_mem d _) (smul_sub_mem_withExponents (frobEUnit_zpow_mem_withExponents 0 A n))⟩
end Lift.KummerChart
end
section
open Int Finset Submodule Lift.KummerChart JumpLattice
namespace Lift.KummerChart.PairingSide
attribute [-instance] NormedAlgebra.toAlgebra
variable {p} [ThePrime p] [Γ:GroupOverGp p] {k:KummerChart Γ} {O} (S:PairingSide O) (i:Letter)
noncomputable def q7 t c:=(s21_z0 (withExponents i (raisedAtE t))⊓S.qZ i c).map S.wJ
attribute [local grind =] kU
variable {S:PairingSide O} {i:Letter} {c:ℕ→ ℤ→ ℤ} (c':ℕ→ ℤ→ ℤ) (hk:IsUnramified) (hp:5≤ p) {a η W:ℕ} {b n r:_→ ℕ} {ε:_→ _} (ha:∀ i,b i+W+η≤ (p-3)*a) (hb:∀ i,6*(a+η+W)< b i) (hs:∀ i,NoMultipleNear p (6*(a+η+W)) (b i)) (hU:∀ i,IsInJumpWindow η (ε i) (b i) W (S.U i)) (hn:∀ i,∑ u∈Icc (-↑η) ↑η,k.f*S.jumpMultiplicity i u≤ n i) (hr:∀ i,∑ u∈S.U i,k.f*S.jumpMultiplicity i u≤ r i)
include hk hn hr in
lemma s21_j7 {i'} a A B (f:i.stepBack a=i') (ha:∀ v,∀ n∈Ioo (c 0 v) (c 0 v+p^a),¬↑p∣n) (hc:∀ b,∀ u∈S.U (i.stepBack b),-u≤ c b u∧(b≠a→ c' b u≤ c b u)) (ho:AntitoneOn (c' a) (S.U i')) (hA:∀ u∈S.U i',∑ n∈Ico (c a u) (c' a u),cost a n≤ A+ite (u∈Icc (-↑η) ↑η) B 0):relLength (S.q7 i 0 c) (S.q7 i 0 c')≤ ↑(A*r i'+B*n i'):=by
 replace hA:=sum_le_sum fun u m↦mul_le_mul_left (hA u m) (k.f*S.jumpMultiplicity i' u);simp [add_mul,-mem_Icc,sum_mul,sum_sigma'] at hA;grw [← mul_sum,hr,← mul_sum,inter_subset_right,hn] at hA;grw [← hA];clear hA
 induction' E:(S.U i').sigma fun u↦Ico (c a u) (c' a u) using eraseInduction with I ih
   generalizing c
 subst E
 obtain w | ⟨u,hu⟩:=by
   simpa using not_or_of_imp (exists_min_image {v∈S.U i' | c a v< c' a v} id)
 exact (relLength_eq_zero.2 (map_mono fun _↦And.imp id (.imp id (mem_withExponents_of_le <| · ·)))).trans_le bot_le
 have M:s21_z0 (S.zH i c)≤ s21_z0
   (S.extLattice.withExponents i (raisedAtE 0)):=fun _↦(mem_withExponents_of_le ·.1)
 grw [← add_sum_erase (a:=⟨u,c a u⟩),relLength_trans _ (ih (c:=vJ c a u) ..)]
 grw [q7,q7,← relLength_comap,comap_map_eq,relLength_mono le_rfl (sup_le_sup_left (fun _↦(·.2):s21_z0 (S.zH i c)≤ _) _),relLength_le_of_relations] <;> intro x hx
 refine (S.vH {⟨a,c a u⟩}).rec fun A ⟨R,d⟩↦mem_sup.2 ⟨_,⟨R.jV M hx.1 hx.2,d hx.2 _ ?_⟩,_,neg_mem (R hx.2),by simp⟩
 swap;choose x' n m b e using (mem_sup.1 <| hx · |>.2);choose y d q B using (zT <| b ·)
 peel 3 qU c hk .refl a i f
   (by clear * - hu ho;grind [AntitoneOn]) (⟨_,B · (m _).2⟩) d with b t
 obtain ⟨w,m,z,o,s⟩:=mem_sup.1 t
 have t:=sum_smul_mem (t:=univ) _ b fun l _↦(hx l).1
 have m:⟨_,S.kJ.wittMap_mem_kisinLoc w.2⟩∈s21_z0 (S.zH i _):=⟨S.kJ.map_mem_withExponents le_rfl m,by simp⟩
 have e:_∈S.qZ i (vJ c a u):=⟨sub_mem (smul_mem _ ↑p t.2.1) (zF m).1,by
   simpa -implicitDefEqProofs [eq_sub_of_add_eq' s,smul_sum,smul_comm _ (b _),← e,q,add_sub] using (s21_q6 _).add_mem (sum_smul_mem _ b fun l _↦(n l).2.2) (smul_sub_mem_withExponents (S.kJ.map_mem_withExponents le_rfl o))⟩
 obtain ⟨A,R,d⟩:=S.vH (.image (.mk 0) ((S.U i).biUnion fun v↦Ioo (c 0 v) (c 0 v+p^a)));rw [sum_eq_zero] at R;obtain ⟨y,z⟩:=R.jV le_rfl m (zF m)
 have m₂:=frobEUnit_zpow_mem_withExponents (c':=c) 0 (-p^a)
   (zU y (d (zF m) (fun b v↦c b v+raisedAtE (p^a) b 0) ?_).2) fun _ v _↦by clear * - ha;grind [ha v 0,dvd_zero]
 obtain ⟨r,f⟩ : ↑p∣k.frobE 0^p^a-k.frobE a:=by simpa [k.dvd_iff_coe_dvd,frobE_eq,hk.1,phi_pow_smul_z,← sub_sub,dvd_sub_left] using sub_dvd_pow_sub_pow (k.z+p) k.z _
 have n:=(s21_z0 (S.zH i c)).sub_mem (x:=r•⟨_,frobEUnit_zpow_smul_mem_kisinLoc.2 (A _).2⟩) ⟨smul_mem _ r.1 m₂,by
   simp [by simpa using z]⟩ (R t.2)
 refine mem_sup.2 ⟨_,⟨sub_mem t.1 (M n),(sub_mem t.2 (zF n)).imp_right fun m g↦mem_withExponents_of_smul not_frobE_dvd_p (m g).1.1 ?_⟩,_,n,by simp⟩
 convert (s21_q6 _).add_mem (R.jV zF e e).2
   (smul_sub_mem_withExponents (frobEUnit_zpow_mem_withExponents a 1 m₂)) g
 simp [S_smul,← sub_eq_iff_comm.1 f,← frobEUnit_pow_smul,← zpow_natCast (k.frobEUnit 0),sub_smul,mul_smul,smul_sub,smul_comm g,Nat.cast_smul_eq_nsmul,-map_smul];abel
 all_goals clear * - hu ha hc hk;cases a <;> grind [jF]
include hk hp ha hb hs hU hn hr
lemma vV i:relLength (S.constantAt i).range (S.q7 i 0 (if ε i=1 then raisedAtE (2*a+η) else fun l u↦if l=1 then W+1-u+if |u| ≤ η then 2*a else 0 else if l=0 then b i+W+2*a else -u))≤ ↑((2*a+1)*n i+(3*(W+1)*r (i.stepBack 1)+6*a*n (i.stepBack 1))):=by
 have U (n:ℕ) : ∑ m∈Ico (0:ℤ) (n+1),cost 0 m=padicValNat p n.factorial:=by
   induction n <;> simp_all [↓← insert_Ico_right_eq_Ico_add_one,add_nonneg,cost,IsUnramified,Nat.factorial,padicValNat.mul];rfl
 have h₁:∀ t,-↑η≤ t→ t≤ 0→ relLength (S.constantAt i).range (S.q7 i t (raisedAtE (2*a+η)))≤ ↑(a * ∑ u∈Ico (-↑η) t,k.f*S.jumpMultiplicity i u):=by
   have X s d m H:p^s•S.constantAt i d∈S.q7 i m (raisedAtE (2*a+η)):=(zC (zA (killsCokernel_of_isUnramified s (a-s) (by grw [← le_add_tsub];grind) hk hp) d) (hs i) _ (by grind)).rec fun x ⟨a,b,c,d⟩↦⟨⟨x,a⟩,⟨mem_withExponents_of_le c H,by simp [b,nsmul_mem],d⟩,by simp [b,hk.2]⟩
   refine Int.leInduction (fun _↦by simpa [IsConcreteLE.le_iff] using (X 0 · _ (by grind))) fun t ht ih h₀ ↦ ?_
   rw [← sum_Ico_add_eq_sum_Ico_add_one ht,mul_add]
   refine relLength_trans (ih (by lia))
     ((relLength_comap ..).ge.trans (relLength_le_of_relations _ (fun x ⟨_,⟨d,e⟩,_⟩ ↦
     by simpa [e] using X a d _ (by clear * - h₀;simp;grind)) fun x l ↦ ?_))
   peel 3 qU _ hk (sum_le_sum fun _ _↦jump_extension_le _ (by omega)) 0 i rfl (by simp [raisedAtE]) x (l · |>.1.1) with b m
   rw [sup_of_le_right fun _ e↦mem_withExponents_of_le e (by clear * -;grind)] at m
   exact ⟨_,(sum_smul_mem _ b fun j _↦(l j).1.2).rec fun x s↦⟨mem_withExponents_of_le (zU m s) (by clear * - h₀;grind),x,s⟩,rfl⟩
 specialize h₁ 0 (by lia) le_rfl
 grw [Ico_subset_Icc_self,η.cast_nonneg,hn] at h₁
 split
 exact h₁.trans (mod_cast by lia)
 obtain ⟨q,h₀,-⟩:=existsUnique_add_zsmul_mem_Ico (natCast_pos.2 p.pos_of_neZero) 0
   (b i+W+2*a)
 simp [IsInJumpWindow] at hU h₀
 refine relLength_trans ((relLength_trans h₁ (s21_j7 (fun l u↦raisedAtE (q*p+u) l u) hk hn hr 0 0 (a+1) rfl ?_ ?_ ?_ fun u hu ↦ ?_)).trans (mod_cast ?_)) (s21_j7 _ hk hn hr _ _ _ rfl (fun _ n x↦(not_dvd_iff_lt_mul_succ _ ?_).2 ⟨q,?_⟩) ?_ ?_ fun u hu↦(sum_le_card_nsmul _ _ _ fun y e↦jF hk (hs (i.stepBack 1) y ?_)).trans ?_) <;> clear h₁
 any_goals grind [card_Ico,AntitoneOn]
 split
 exact (sum_le_sum_of_subset (by grind)).trans ((U (q*p).toNat).trans_le (le_of_mul_le_mul_left (by rw [sub_one_mul_padicValNat_factorial];grind [tsub_mul]) (by lia)))
 exact sum_nonpos fun y e↦jF hk fun d↦hs i y (by
   grind [le_of_dvd (by grind) ((dvd_mul_left _ q).sub d)]) d
lemma vI (hη:1≤ η):∃ V:Submodule ℤ_[p] _,relLength ⊤ V≤ ↑(11 * ∑ i,(n i*(a+1)+r i*(W+1)))∧∀ T (P:SidePairing T S) c,(∀ i,IsInJumpWindow η (-ε i) (b i) W (T.U i))→ ∀ d∈V,P.ScaledCupBounds 0 c d:=by
 refine ⟨_,(relLength_iInf_le ..).trans ((sum_le_sum fun i _↦(relLength_comap ..).trans_le (map_top (S.constantAt i)▸vV hk hp ha hb hs hU hn hr i :)).trans (mod_cast by simp [← mul_sum,← sum_mul,Equiv.sum_comp];lia)),fun _ P c V d h↦P.z4 (e':=0) ⊤ (ε · = 1) 1 (by simp;tauto) (fun i _↦((mem_iInf _).1 h i).rec fun x ⟨⟨s,_,t⟩,e⟩↦⟨⟨_,0,zC (zA (killsCokernel_of_isUnramified 0 a ?_ hk hp) c) (hs i) (raisedAtE (2*a+η)) ?_,⟨⟩,?x⟩,⟨_,1,⟨_,x.2,by simpa,zU
   s t,t⟩,⟨⟩,?y⟩,zC (zA (killsCokernel_of_isUnramified 0 a ?_ hk hp) 1) (hs i) (raisedAtE a) ?_,?_⟩) (by simp [hk.2])⟩
 case x | y => rintro (_ | _ | _) u _ v _ <;> obtain ⟨w,x,_,_,e | e⟩:=V _ _ ‹_›,hU _ _
                 ‹_›,hb (k.letterFrob.symm i),hb i,units_eq_one_or (ε i) <;> simp [e,raisedAtE,stdExponent,abs_le,ite_apply] at w x ⊢ <;> omega
 all_goals clear * - ha hb hU V hη;grind (splits:=15) [mem_image₂,Antitone]
end Lift.KummerChart.PairingSide
end
section
namespace Lift
open KummerChart JumpLattice WittVector Submodule FrobGroup Module Finset Polynomial LinearMap PairingSide algebraMap
variable {p:outParam ℕ} [ThePrime p] (Γ:outParam (GroupOverGp p))
class TameChart extends KummerChart Γ where
 (zetaE:WittFq f) (tameGen:Γ) primitive:IsPrimitiveRoot (zetaE.coeff 0) e
 tameGen_pow_smul_z k:toGp (tameGen^k)•chart.z.1 = ↑(zetaE^k)*chart.z
 (isWeilPair_tameGen:IsWeilPair (toGp tameGen) 0) fixesLambda_tameGen_pow k :
   FixesLambda f (toGp (tameGen^k))
 (ϖ) apply_varpi (g:Γ'):toGp g.1 ϖ=ϖ
 (varpi_pow_eq:ϖ^e=p) (tame:¬p∣e) [normal:Γ'.Normal]
namespace TameChart
variable [Γ] {d:TameChart Γ} {O} {L:d.JumpLattice O} {n m:ℕ} {q:ℤ_[p][X]} {S:PairingSide O} (hK:IsKilledBy S.ρ d.tameGen 0 (q.map (algebraMap _ O)))
lemma kH (r:aeval (linearFrob L.ρ d.tameGen 0) q=0) {x} (hx:x∈L.kisinModule):∃ y∈L.kisinAinf,d.z.1•y = ∑ k∈range (q.natDegree+1),q.coeff k•inr (d.tameGen^k)•x :=
   have n g:=(d.normal.1 · · g)
   frame_theorem.1.2.2.2.elim fun u v↦v _ d.z_dvd_of_dvd_E_pow_mul _ (by
   simp [↓sum_mem,↓smul_of_tower_mem,↓smul_mem_kisinAinf (n _) hx.1]) fun μ ⟨hl,l,E⟩↦by
 let Λ g:=(DistribSMul.toLinearMap _ _ (toGp g)⁻¹∘ₗl∘ₗoverZp L.ρ g).liftBaseChange Bcris
 have A g g' y:Λ g' (tensorAction _ (toGp g) (L.ρ g) y)=toGp g•Λ (g'*g) y:=by
   clear * -;induction y <;> simp_all [Λ,tensorAction,mul_smul]
 have S : ∑ k∈_,q.coeff k•Λ _=0:=ext_on L.inClass.isPotCrys fun y b↦by
   simpa [← linearFrob_pow L.inClass.isPotCrys d.isWeilPair_tameGen,fun k↦linearFrob_apply (m:=0) L.inClass.isPotCrys (d.isWeilPair_tameGen.pow k) b▸(A _ 1 _).trans ((d.isWeilPair_tameGen.pow k).smul_eq_of_fixed_nearOne (.mp b (d.nearOne_le fun g b ↦ .trans (by
     rw [A];congr 2 with _
     simpa [Λ,E,mul_smul,eq_inv_smul_iff,-map_pow] using (conjForm_mem_forms (n _) hl _ g).symm)
     (congrArg _ b)))),aeval_eq_sum_range] using congr(Λ 1 ($r y))
 simpa [smul_sub,smul_comm (q.coeff _),← smul_sum,by
   simpa using apply_eq_of_mem_fracSpan (∑ k∈_,q.coeff k•conjForm μ (d.tameGen^k)) 0 (by ext;simpa [basisValues,Λ,E,smul] using congr(($S (1 ⊗ₜ _):BdR))) (kisinAinf_le_fracSpan hx.1)] using! sum_mem (t:=range q.natDegree.succ) fun k _↦smul_of_tower_mem _ (q.coeff k) (pow_smul_gal_sub_mem_span_of_dvd (d.z_dvd_sub (d.fixesLambda_tameGen_pow k)) (u _ ⟨conjForm_mem_forms (n (d.tameGen^k)) hl,(liftBaseChangeEquiv _).2 (Λ (d.tameGen^k)),by simp [Λ,E]⟩ _ hx))
include hK
lemma vN:aeval (linearFrob S.extLattice.ρ d.tameGen 0) (q*(X-1))=0:=LinearMap.ext fun y↦by
 obtain ⟨x,e⟩:=(lTensor_exact _ .inl_snd snd_surjective (_-y)).1 (by
   simpa [IsCrystalline.linearFrob_eq_one,isAdmissible_of_cyclotomicGp_zpow 0,isWeilPair_tameGen] using! baseChange_linearFrob S.extLattice.inClass.isPotCrys
     d.isWeilPair_tameGen S.trivLattice.inClass.isPotCrys _ (by simp [extensionRep]) y)
 simpa [← e,eval₂_map,coefEnd,aeval_def,q.eval₂_eq_sum_range,End.pow_apply,Function.Semiconj.iterate_right (baseChange_linearFrob hK.1 d.isWeilPair_tameGen S.extLattice.inClass.isPotCrys (inl ..) (by simp [extensionRep])) _ _] using! congr((inl _ _ S.C).baseChange _ ($(hK.2) x))
lemma qQ (hn:∀ i,∀ u∈S.U i,u≤ n) (hq:q.Monic) (hm:d.e≤ p^m) {κ i} (hp:n+κ+2< p) (hc:m*(q.natDegree+1)≤ κ):S.KillsCokernel i κ 0:=by
 obtain ⟨⟨ν,h₀,hν⟩,M⟩:=exists_z_pow_mem_liftIdeal hn κ.succ,hq.mul (monic_X_sub_C 1)
 replace hν:ν< d.e:=by nlinarith [NeZero.pos d.e]
 set Q:=q*_
 replace h₀:=smul_mem _
   (p.cast^(m * #{k∈Ico ν.succ d.e | (aeval (d.zetaE^k) Q).coeff 0=0})) (h₀ i)
 induction' ν with n ih
 · apply liftIdeal_le_of_p_pow_mem <;> simpa using mem_liftIdeal_zero_of_mem_one _ _ le_rfl
     (p_pow_mul_z_pow_mem_liftIdeal_iff.2 h₀) (by grw [← card_image_iff.2 (d.primitive.injOn_pow.mono (by grind)),card_le_degree_of_subset_roots (p:=Q.map _) (forall_mem_image.2 (by
     simp [aeval_def,hom_eval₂,eval_map,← WittVector.constantCoeff_apply,map_monic_ne_zero M]
     tauto)),natDegree_map_le,natDegree_mul_le,natDegree_X_sub_C,hc])
 apply ih hν.le
 rw [card_filter,sum_eq_sum_Ico_succ_bot hν] at *
 split
 · exact mem_liftIdeal_zero_of_mem_one _ _ (by lia) (p_pow_mul_z_pow_mem_liftIdeal_iff.2 h₀)
     (by grind [padicValNat_factorial_mul,padicValNat.mul,Nat.log_lt_of_lt_pow (by omega) (hν.trans_le hm),Nat.factorial,padicValNat_le_nat_log])
 obtain ⟨u,K⟩:=S.exists_lift_of_mem_liftIdeal (f:=p^_*d.z^_) h₀;obtain ⟨w,t,rfl⟩:=d.exists_z_dvd_sub_const u
 refine (smul_mem_iff_of_isUnit _ ((isUnit_of_coeff_zero_ne_zero _ ‹_›).map (algebraMap ..))).1
   (mem_liftIdeal_iff.2 ⟨Q.sum fun k a↦a•toGp (d.tameGen^k)•t.1*d.zetaE^k,fun c↦(K _ (constantAt_mem_locLetterPart c)).rec fun x ⟨m,f⟩↦have ⟨X,v,b⟩:=kH (q:=Q) (vN hK) ⟨frobKisinAinf_zero.le (mem_withExponents_stdExponent_iff.1 m.2).1,m.1.2⟩
   ⟨_,letterProj_mem_withExponents (frobKisinAinf_zero.ge v),(isUnit_WittCFlat_of_not_p_dvd d.not_p_dvd_z).smul_left_cancel.1 ?_⟩⟩)
 linear_combination (norm:=simp [f,-map_pow,tameGen_pow_smul_z,fixesLambda_tameGen_pow,smul,smul_letterProj (m:=inr _) (fixesLambda_tameGen_pow ..),aeval_eq_sum_range,mem_letterPart_iff_letterProj.1 letterProj_mem_letterPart,sum_over_range,smul_sub,smul_sum,sum_mul,sub_smul,constantAt,← sum_sub_distrib,sub_add_eq_sub_sub_swap,← sum_add_distrib,frobGroup_smul_smul,sum_smul]) congr(letterProj i (S.projTriv.wittMap $b) - $(Q.eval_eq_sum_range 1▸eval_mul_X_sub_C _)•p^κ.succ•(w:Ainf)•S.constantAt i c)
 exact sum_eq_zero fun _ _↦by module
end TameChart
end Lift
lemma Lift.wH {p e} [hp:ThePrime p] [Γ:GroupOverGp p] (hj:Function.Surjective Γ.overGp.toGp) (f:ℕ+) (hf:¬p∣f) (he:e∣p^f.val-1):∃ d:TameChart Γ,d.e=e:=by
 obtain n := @not_dvd_pow_sub_one p _ f,NeZero.mk (ne_zero_of_dvd_ne_zero NeZero.out he);obtain ⟨⟨ϖ,hϖ⟩,a,Z⟩:=IsSepClosed.exists_pow_nat_eq (p:PadicAlgCl p) e,(HasEnoughRootsOfUnity.of_dvd (flatFq f) he).1
 obtain ⟨c,rfl,_,_,⟨⟨⟩⟩⟩:=(@exists_chart_of_pow_mul_eq_neg p _ f ⟨ϖ,by
   simp [le_of_pow_le_pow_left₀ (NeZero.ne e),← norm_pow, *,norm_p_lt_one.le]⟩ e (-1)
   (Subtype.ext (by simp [PadicComplex.coe_eq,← map_pow, *]))).choose_spec.2 (-1) (by simp)
 set N:=_-1
 obtain ⟨T,q,K⟩:=(hj.exists.1 <| exists_smul_teichmuller_eq _ (isLocalGalois_padic.exists_inertia_smul_eq_of_pow_eq isUniformiser_ell) c.varpiFlat · c.e (by
   simp [PadicComplex.coe_eq,← map_pow, *]) ·),(he.rec (by simp_all [pow_mul,div_pow,← map_pow]):∀ g:Gp p,(g ϖ/ϖ)^N=1),fun {g}↦by simpa using (@cycCharMod_eq_iff (Gp p) (PadicAlgCl p) _ _ _ N g _ _ _ 1),(fixes_roots_iff_fixesLambda · |>.1 <| apply_eq_self_of_mem_inertiaGroup n ·),ne_zero_pow NeZero.out (hϖ.trans_ne NeZero.out)
 let U:OpenSubgroup _:=⟨(cycCharMod _ N).ker,isOpen_ker_cycCharMod.1⟩⊓⟨_,isLocalGalois_padic.1.6 ϖ⟩
 have M {g}:g∈U↔c.FixesThetaZ g:=(K.trans (fixes_roots_iff_fixesLambda g)).and (by simp [*,c.z_eq_teichmuller,Subtype.ext_iff])
 have Pe {g} h:g^N∈U:=⟨pow_mem h _,by
   simp [*,@Function.Commute.iterate_eq_of_map_eq _ g (g ϖ/ϖ * ·) fun _↦by aesop]⟩
 have:U.Normal:=⟨fun n c g↦by have:=K.1 c.1 _ (q g⁻¹);simp_all [U,-K]⟩
 exact (T (a*c.varpiFlat) (by simp [mul_pow,← map_pow,← Subring.coe_pow,Z.1])).rec fun s i↦⟨@.mk _ _ _ ⟨c,.comap toGp U,U.index_comap_of_surjective hj ▸ .of_dvd_left (IsPGroup.exists_card_dvd_pow (⟨1,·.ind' fun g↦by simpa [← QuotientGroup.mk_pow,pow_mul] using Pe (K.2 fun _ e↦by simp [Function.Commute.iterate_eq_of_map_eq (map_pow g · _) _ (exists_apply_eq_pow n e g).choose_spec,pow_right_comm,pow_eq_pow_of_modEq ((Nat.modEq_sub NeZero.one_le).pow _) e])⟩)).choose_spec (.pow_left _ (hp.out.coprime_iff_not_dvd.2 (hp.out.not_dvd_mul hf n)).symm),
   by simp [M],hj.forall.2 (⟨⟨·,M.2 ·⟩,rfl⟩),by simpa using ⟨_,U.mem_nhds_one,.rfl⟩,fun l ↦
   by simpa using (T (epsTilt^l*c.varpiFlat) (by simp)).imp (by simp_all [↓← theta_smul,FixesLambda,c.z_eq_teichmuller,Chart.FixesThetaZ])⟩ _ s Z (by
   induction · <;> simp_all [pow_succ',mul_smul,c.z_eq_teichmuller]
   erw [WittVector.map_teichmuller];ring!)
   (isWeilPair_zero_iff.2 i.1) (by simp [FixesLambda, *,pow_mem]) ϖ (·.2.2)
   hϖ (n∘(.trans · he)) (this.comap _),rfl⟩
namespace Lift.KummerChart.PairingSide
open Finset
variable {p} [j:ThePrime p] [Γ:GroupOverGp p] {k:KummerChart Γ} {O} {S S':PairingSide O} (h:S.SidePairing S') {cut T:Letter→ Prop} [DecidablePred T] {ε:Letter→ ℤˣ} {s β:Letter→ ℕ} {η V W X κ b n J s₀ G e K:ℕ} (hW:V+4*η≤ W) (hU:∀ i,IsInJumpWindow η (-ε i) (β i) V (S.U i)∧IsInJumpWindow η (ε i) (β i) V (S'.U i)) (hX:(J+1+k.differentExp+p.log (2*b))*n+k.differentExp*G≤ X) (hκ:12*(J+1)*X< κ) (hδ:k.e*(2*b)≤ p^(J+1)*X) (h₈:8*k.e≤ p^(J+1)) (hη:1≤ η) (hs:W≤ n∧W≤ G∧∀ i,β i+s i+W≤ 2*b) (hy:G≤ (p-1)*n) (hK:∀ i,cut i→ s i=0∧(∀ t∈Icc 1 J,β ((k.letterFrob^t) i)+W≤ G)∨s i< β i∧IsUnramified∧5≤ p∧s₀≤ κ+s i) (hz:5≤ p→ ∀ i,β i+W≤ (p-3)*s₀) (hβ:β=fun i↦ite (T i) b G)
include hs hz hy hδ h₈ hX hκ hK
lemma kA (w:∀ i n,β i+W≤ n→ ∀ u∈S.U i,u≤ n) i (c:cut i):S.KillsCokernel i κ (s i):=by
 obtain ⟨⟨e,t⟩ | ⟨_,hk,q,e⟩,⟨a,H,f⟩,hp⟩:=hK i c,exists_z_pow_mem_liftIdeal (w · (2*b) (by grind)) κ.succ,j.out.one_lt
 have K x (l:p*a≤ p^(J+1)*x) :
     p^(J*X)*k.z.1^(x+n)∈S.liftIdeal (p^κ.succ) 0 i:=by
   clear hδ h₈ hκ hK c e;induction' J with s ih generalizing i x
   exact Ideal.mem_of_dvd _ (by simp_all [pow_dvd_pow,hp.pos,le_add_right]) (H i)
   apply p_pow_mul_z_pow_mem_liftIdeal_iff.1 (mem_liftIdeal_of_mul_E_pow (mul_E_pow_mem_liftIdeal_one (ih (by lia) _ (t ·.succ∘by simp) _ (by rwa [← mul_assoc])) (by tauto)) ⟨?_,?_⟩) <;> nlinarith [(@sub_one_mul_padicValNat_factorial p _ G).trans_le tsub_le_self,p.sub_add_cancel hp.le]
 apply liftIdeal_le_of_p_pow_mem <;> simpa [e] using mem_liftIdeal_zero_of_mem_one _ κ (a:=0)
   bot_le (p_pow_mul_z_pow_mem_liftIdeal_iff.2 (K (2*X+κ/4).succ (by nlinarith [κ.lt_div_mul_add four_pos]))) (by grw [padicValNat_factorial_mul,Nat.le_sub_one_of_lt (padicValNat_factorial_lt_of_ne_zero ..)] <;> lia)
 exact killsCokernel_of_isUnramified _ _ (w · _ (by grw [hz q,e])) hk q
include hW hη hU
variable (cut s b n J s₀ G) in
lemma SidePairing.jH (hd:∀ i,s i+W≤ p*n) (he:51*κ≤ e) (hL:∀ i:k.Letter,∃ l∈Set.Ioc 0 (2*J+1),cut (i.stepBack l)) (H:∀ i l,cut (i.stepBack l)→ (∀ a∈Set.Ioo 0 l,¬cut (i.stepBack a))→ ∃ t,(∀ a< l,ε (i.stepBack a)=ε (i.stepBack t)∨β (i.stepBack a)+V≤ η)∨k.IsUnramified∧5≤ p∧s (i.stepBack l)=0∧t+(J+1)=l∧(s i=0∨t=0)∧s₀+G * ∑ a∈range (J+1),p^a< β (i.stepBack t)∧∀ a< l,a≠t→ (ε (i.stepBack a)≠ε (i.stepBack t)∨β (i.stepBack a)+V≤ η)∧(t< a→ β (i.stepBack a)+W≤ G)) c c':h.ScaledCupBounds e c c':=by
 let A a:=ite (a≤ 2*J) η 0
 choose l hl hn using (hL · |> Nat.findX |>.exists_of_subtype)
 choose t hc using (H · _ (hl _).2 (by grind))
 let R ρ i a u:=ite (ε (.stepBack i (t i))=ρ) (stdExponent (l i) a u) (-u-A a)⊔(-u-A a)
 have pt {T T':PairingSide O} ρ {σ} (hU:∀ i,IsInJumpWindow η (ε i / -ρ) (β i) V (T.U i)∧IsInJumpWindow η (ε i/ρ) (β i) V (T'.U i)) {c i} (hi:cut i):T.vW T' c i
   (25*κ) cut (l i) (R ρ) (R σ) (raisedAtE <| -s ·) (ε (i.stepBack (t i))=ρ):=by
   obtain ⟨⟨hL,hl⟩,hc,ht,h₀,q,z⟩:=hl i,hc i,hK i hi,(hK i hi).imp (·.1) (·.2.1.2.2),(show _≤ R σ · · · from le_sup_right),kU i
   generalize R σ=w at *;unfold vW R;generalize l i=l,t i=t at *
   simp [IsInJumpWindow,div_eq_one,← Int.units_ne_iff_eq_neg] at hU
   have kl:=T.kA hX hκ hδ h₈ hs hy hK hz ?_
   let o a u:=raisedAtE (s i) a u+A (a/2)
   obtain ⟨⟨_,hx⟩,⟨hi,hk,hp,hy,rfl,ht,he,hc⟩ | ⟨hl,hc⟩⟩:=zA (kl i hi) c,(em (ε (i.stepBack t)=ρ∧¬_)).imp (·.imp_right hc.resolve_left) (And.intro (z▸hi))
   have y a:(i.stepBack t).stepBack a=i.stepBack (t+a):=by simp [pow_add]
   have hx:=zP (v2 J.succ_pos hk (y _▸hy▸kl _ hl) (killsCokernel_of_isUnramified _ _ (by clear * - hU hz hp hW;grind) hk hp) rfl (y ·▸by clear * - hU hc hs hW hi;grind) (he.trans_le ?_) (by lia) hδ c).some_mem
   let o a u:=ite (a≠t) (stdExponent (t+J.succ) a u+3*A (a/2)) (2*b)
   all_goals try refine ⟨o,_,(jR hx ((range (4*J+2)).sigma fun a↦twoWindows (ite (a=0) (s i) 0+W) (ite (ε (i.stepBack a)=ρ) 1 (-1)*β (i.stepBack a))) ?_ (by
     clear * - hd h₀ hs z hη hW hX hκ;grw [← sum_sigma',sum_le_card_nsmul _ _ (72*X),card_range];lia
     refine fun a ha↦(sum_twoWindows_le n (2*b) ?_ ?_).trans ?_ <;> grind [mul_le_mul' hs.1 (add_le_add_left (mem_range_le ha) k.differentExp),le_of_mul_le_of_one_le_left (le_of_add_le_left hX) (by lia)])).imp fun _ ↦
     .imp_right (.imp_right (.imp_left (JumpLattice.mem_withExponents_of_le · ?_))),hl,?_⟩
   all_goals
     try intro a;specialize hc a
     clear * - hU hc hi hL hs hW ht hη z hy he q;generalize i.stepBack=f at *
     (try simp [raisedAtE,-Nat.cast_sum]);grind (splits:=15)
 refine h.z4 _ _ l (by grind [IsLeast,lowerBounds]) fun i e↦⟨pt 1 ?_ e,Int.units_ne_iff_eq_neg.eq▸pt (-1) ?_ e,zA (kA hX hκ hδ h₈ hs hy hK hz ?_ i e) 1,?_⟩ <;>
   clear * - hU hW <;> simp [div_neg,Antitone] <;> grind
omit hs hz hy hX hκ hK
include hβ
lemma SidePairing.scaledCupBounds_sparse_thick (hε:IsUnramified∧7≤ p∨∀ i i',ε i=ε i') (hG:G+V≤ η) (hb:11*(p^J+1)*W≤ b) (hth:∀ i,∀ s∈Icc 1 J,∀ t∈Icc 1 J,T i→ T ((k.letterFrob^s) i)→ ¬T ((k.letterFrob^(s+t)) i)) (he:4*(J+1+k.differentExp+p.log (2*b))*W≤ X) c c':h.ScaledCupBounds (10^4*(X*(J+1))) c c':=by
 let C i:=∀ t≥ 1,t≤ J→ ¬T ((k.letterFrob^t) i)
 replace hth i a (c:¬C (.stepBack i a)) (t:T (i.stepBack a)):C (i.stepBack (a+J.succ)):=fun n _ hn tn↦c (by simp at t;simpa [t,pow_add,add_comm (_-_),pow_sub _ hn.step] using (hth _ (J.succ-n) (by simp;lia) · · tn))
 apply h.jH _ (fun _↦0) b (2*W) _ (3*b/5) (2*W) hW hU _ .refl
   hδ h₈ hη _ _ _
   (by grw [← ·];grind) _ _ (by_contra fun h↦h ⟨J+1,by grind,fun n _ hn t↦h ⟨_,by grind,
   hth · (J+1-n) (h ⟨_,by simp;lia,·⟩) (by simpa [pow_sub _ hn.step])⟩⟩) fun i n hl h ↦ ?_
 iterate 6 grind [mul_le_mul_left j.out.one_lt W,tsub_mul]
 replace hth a ha t:=(eq_zero_or_pos a).imp_right fun a₀↦(not_lt.1 fun e↦hl (n-a) (by lia) (by lia) (by simpa [← pow_mul_pow_sub _ ha.le])).eq_of_not_lt (h _ ⟨by lia,·⟩ (hth i a (h a ⟨a₀,ha⟩) t))
 exact (forall_or_exists_not _).elim (⟨0,.inl ·⟩) (.imp (by
   grw [sum_range_succ,@Nat.geomSum_lt _ J _ j.out.one_lt] <;> grind))
omit hδ h₈ in
lemma SidePairing.scaledCupBounds_two_sizes (hk:IsUnramified) (hp:7≤ p) (h₀:5*W≤ G) (hG:G≤ b) (hb:b< K*p^2∧2*G< K*p∧W≤ K) c c':h.ScaledCupBounds (10^4*(K*(p.log (2*b)+1))) c c':=by
 obtain _:=pow_le_pow_left' hp 2,mul_le_mul_right hp (K-1),mul_le_mul_right hp (b/p),b.div_mul_le_self p,@b.lt_div_mul_add p,@b.div_lt_of_lt_mul p (K*p)
 have z i:k.letterFrob (i.stepBack 2)=i.stepBack 1∧k.letterFrob (i.stepBack 1)=i:=by simp [sq]
 let s i:=ite (T (k.letterFrob i)) (b/p-7*K) 0
 apply h.jH (fun i↦s i< β i) s b K 1 (b/p+12*K) (G+W) hW hU .refl .refl <;> clear hU
 iterate 10 grind [tsub_mul,pow_one,hk.2]
 rintro i (_ | _ | _ | l) _ u <;> use 0 <;> try grind
 refine (em _).imp_right fun _↦⟨hk,?_⟩;and_intros <;> try grind
 simp;nlinarith [(by grind:G+7*K≤ b/p∧β i=b)]
end Lift.KummerChart.PairingSide
end
section
namespace Lift
open Polynomial Module Finset KummerChart JumpLattice Function IsLocalRing Topology Filter
variable {p} [l:ThePrime p] [Γ:GroupOverGp p] {O:Type} [CommRing O] {r N:ℕ} [PadicIntegerRing O p] [TopologicalSpace Γ] {L:GalLattice O Γ} {U U':_→ Finset ℤ} (k:KummerChart Γ) (ζ:LetterRoot O) (ho:IsOpenEmbedding Γ.overGp.toGp) {F} (hF:map k.Γ'.subtype ⊤ ≤ F)
variable (p r N) in
def IsTameType (K:O[X]→ _):=K (X^(Icc 1 r).lcm (p ^ · - 1)-1)∧∃ q:ℤ_[p][X],q.Monic∧q.natDegree≤ N∧K (q.map (algebraMap ..))
noncomputable def KummerChart.letterJumps (U:(O →ₐ[ℤ_[p]] ℂ_[p])→ Finset ℤ) i:=insert 0 (Finset.biUnion {g | g ζ = ↑(theta (k.letterTeich i))} U)
noncomputable abbrev KummerChart.universalSide (h:InClass F ⊥ U L):PairingSide ⟨O,ζ⟩:=have:=crysCocycles.fg h.isPotCrys;⟨⟨L,k.letterJumps ζ U,U,h.imp_left (.mono · (by
   gcongr)),by grind [letterJumps]⟩,⟨crysCocycles L.ρ,1⟩,.id,by simp [letterJumps]⟩
include ho
lemma KummerChart.mem_cupOrthogonal_of_scaledCupBounds {Q} (hc:Q≤ InClass F ⊥ U) (hL:InClass F ⊥ U' L) e x (H:∀ Y a (P:(k.universalSide ζ hF (hc Y a)).SidePairing (k.universalSide ζ hF hL)) c,P.ScaledCupBounds e c x):(p:O)^e•x.1∈cupOrthogonal Q L:=fun Y P b y c↦mod_cast H Y b P ⟨y,c⟩ ho
lemma KummerChart.few_low_jumps (hk:IsUnramified) (hp:5≤ p) {a η W} {b:_→ ℕ} {ε:_→ _} (ha:∀ n,b n+W+η≤ (p-3)*a) (hη:1≤ η) (hb:∀ n,6*(a+η+W)< b n) (hs:∀ n,NoMultipleNear p (6*(a+η+W)) (b n)) (hL:InClass ⊤ ⊥ U' L) (hV:∀ i,IsInJumpWindow η (-ε i) (b i) W (k.letterJumps ζ U i)∧IsInJumpWindow η (ε i) (b i) W (k.letterJumps ζ U' i)):((∀ g u,u∈U g∨u∈U' g→ u∉Ico (-↑a) 0)∨(∀ g,U' g⊆Icc (-η) 0)→ crysCocycles L.ρ≤ cupOrthogonal (InClass ⊤ ⊥ U) L)∧∀ m,(∀ g,∑ u∈Icc (-↑η) ↑η,jump L.ρ g u≤ m)→ relLength (crysCocycles L.ρ) (cupOrthogonal (InClass ⊤ ⊥ U) L)≤ ↑(11*(k.f*(m*(a+1)+finrank O L*(W+1))))*length O (O⧸Ideal.span {(p:O)}):=by
 obtain M:=k.mem_cupOrthogonal_of_scaledCupBounds ζ ho le_top le_rfl hL 0;refine ⟨fun h₀ x m ↦ ?_,fun m hm↦(ENat.mul_le_mul_right_iff length_pos.ne' length_ne_top).1 ((length_restrictScalars ℤ_[p] ..).ge.trans ?_)⟩
 · simpa using M ⟨x,m⟩ fun _ _ Q
     _↦by apply Q.q4 (κ:=0) _ hs hV <;> (try intro <;> and_intros <;> apply PairingSide.killsCokernel_of_isUnramified) <;> simp [*,hk.2] <;> clear * - h₀ ha hb hV <;> grind [letterJumps]
 rw [mul_assoc,← length_restrictScalars,← map_natCast (algebraMap ℤ_[p] O),← Set.image_singleton,← Ideal.map_span,← PadicInt.maximalIdeal_eq_span_p,length_eq_of_surjective residue_surjective (R:=_⧸_) (M:=O⧸_),@length_eq_finrank _ _ (Ideal.Quotient.divisionRing _),finrank_quotient_map]
 refine ((k.universalSide ζ le_top hL).vI hk hp ha hb hs (hV · |>.2) (by intro;grw [← mul_sum,sum_comm,hm]) (by intro;grw [← mul_sum,sum_comm,sum_le_sum fun g _↦(hL.isPotCrys.exists_hasJumps g).rec fun J ⟨a,e⟩↦funext e▸a▸(sum_le_sum_of_ne_zero (by simp)).trans_eq J.toFinset_sum_count_eq]) hη).rec fun V H↦((relLength_mono le_rfl (T:=((cupOrthogonal ..).submoduleOf _).restrictScalars _) fun x y↦by
   simpa using! M x fun _ _ a _↦H.2 _ a _ (hV · |>.1) _ y).trans (H.1.trans (mod_cast ?_))).trans_eq'
   (by rw [relLength_eq_length_map_mkQ,Submodule.map_top,Submodule.range_mkQ,length_top];rfl)
 simp [← mul_sum,← sum_mul]
 grw [← card_biUnion fun _ _ _ _ h↦disjoint_filter.2 fun _ _ a↦by simpa [a] using! (((isUnit_teichmuller_sub (Units.ext.mt h)).map (algebraMap ..)).map theta).ne_zero,
   card_le_univ,card_algHom_eq_finrank];lia
lemma tame_types_exponent (hj:Surjective Γ.overGp.toGp) {F K} (hL:InClass F (K ·⁻¹) U' L) (hK:∀ s,IsWeilPair (toGp s) 0→ IsTameType p r N (K s)) {η W b ε} (hU:∀ g,IsInJumpWindow η (-ε) b W (U g)∧IsInJumpWindow η ε b W (U' g)) (hp:b+6*(W+η)+r^2*(N+1)^2+2< p):∀ a∈crysCocycles L.ρ,(p:O)^(3*(r^2*(N+1)^2)+150*(η+W+1))•a∈cupOrthogonal (InClass F K U) L:=(wH hj ⟨_,r.factorial_pos⟩ (l.out.dvd_factorial.1.mt (by grind [le_self_pow])) (lcm_dvd fun _↦Nat.pow_sub_one_dvd_pow_sub_one p∘And.elim Nat.dvd_factorial∘mem_Icc (b:=r).1)).rec fun d he↦by
 obtain ⟨t,hm⟩:=d.isWeilPair_tameGen,show d.e≤ p^r^2 by
   grw [he,Nat.le_of_dvd _ (lcm_dvd_prod ..),prod_le_pow_card _ _ (p^r)] <;> simp_all [← pow_mul,sq,l.out.one_lt,le_add_right,pow_le_pow_iff_right₀,Nat.one_le_iff_ne_zero]
 let J:=MulEquiv.ofBijective toGp ⟨ho.1.2,hj⟩
 have w (g:inertiaGroup ..):=isWeilPair_zero_iff.2 ((J.apply_symm_apply g.1).symm▸g.2)
 have A {K U} (hK:∀ s,IsWeilPair (toGp s) 0→ IsTameType p r N (K s)) L (H:InClass F K ..) :
   InClass (O:=O) _ ⊥ U L:=⟨.mono ((isAdmissible_comp_iff ..).1 ((H.isPotCrys.comp _).isCrystalline_of_inertia_fixes fun s u↦by
   simpa [linearFrob,Dpcris,← map_nearOne _ ho.1.2 (@OverGp.isOpen_range d.Γ' ..)] using! (isLocalGalois_padic.tame_inertia isUniformiser_ell (valuation_natCast_eq_one d.tame) d.varpi_pow_eq ⟨⟨(linearFrob _ · 0)∘_,by simpa using (linearFrob_pow H.isPotCrys t 0)⟩,by simp [linearFrob_mul H.isPotCrys (w _) (w _)]⟩ (Subgroup.isOpen_of_mem_nhds _ ((nhds _).3 (continuous_subtype_val.tendsto 1 (mem_comap'.1 H.isPotCrys.eventually_linearFrob_eq_one)) fun g↦(· (J.right_inv _) (w g)))) fun g↦by simpa [he] using (H.2.2 _ _ (hK _ (w g)).1 (w g)).2).1 (x:=⟨J s,isWeilPair_zero_iff.1 u⟩) (d.apply_varpi s))) (sup_le nearOne_le le_rfl),H.2.1,nofun⟩
 obtain ⟨⟨-,q,m,n,k⟩,-,q',m',n',k'⟩:=hK _ t,hK _ t.inv
 refine (d.1.mem_cupOrthogonal_of_scaledCupBounds ⟨1,by simp⟩ ho le_rfl (A hK) (A (hK ·⁻¹ ·.inv) _ hL) _ ⟨·,·⟩ fun S hY h c↦(exists_isKilledBy_tateDual_tensor hY hL t.inv m' m k' ?_).rec fun _ ⟨M,u,v⟩↦h.q4 (fun _↦⟨d.qQ ?_ ?_ M hm hp (by grw [u,n,n'];lia),d.qQ ?_ ?_ m hm hp ?_,d.qQ ?_ ?_ m' hm hp ?_⟩) ?_ (fun _↦(?_:IsInJumpWindow η (-ε) b W _∧_)) ?_ ?_ c _) <;> (first | gcongr | simp_all [hY.2.2,hL.2.2,KummerChart.differentExp,↓padicValNat.eq_zero_of_not_dvd d.tame]) <;> clear * - hp n n'
   hU <;> grind [NoMultipleNear,→ Int.le_abs_of_dvd,KummerChart.letterJumps]
end Lift
end
