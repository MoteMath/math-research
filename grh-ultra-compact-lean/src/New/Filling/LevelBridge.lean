import New.Filling.BesselSystem
import Lib.Adelic.Transference.MassBasic
noncomputable section
open Finset Set NumberField MeasureTheory Matrix Real Fintype Fin Complex Classical Valued
variable (E : Type) [Field E] [CMType E] (𝔰 : Shape)
structure Filling where
  (N : ℕ) (levelPrime : _ → ℕ) (piBar : (𝔸f E)ˣ) (ϖ : 𝓞 E) (b) chosenPlaces : Fin 2→Set (FinPlace E)
  [fintypeChosen (i) : Fintype (chosenPlaces i)]
  (columnLevel) (aut_columnLevel (g) : classAut (stdSpace E 𝔰.κ).Γf columnLevel g = ⊥) [hasFiniteType_columnLevel : IsLevel columnLevel]
  besselSys : InfinitePlace E→BesselSystem 𝔰 b (numInfPlaces E)
  piBar_mul_star : piBar * star piBar.1=N
  N_prime : N.Prime
  N_split (w : FinPlace E) : v (piBar.1 w)=1∨w.q=N∧v (piBar.1 (star w))=1
  piBar_mem : ↑piBar ∈ Ô E
  levelPrime_prime i : (levelPrime i).Prime∧levelPrime i≠N
  le_levelPrime i : b ^ 10≤levelPrime i
  levelPrime_le i : levelPrime i≤b ^ 11
  chosenPlaces_q i : ∀ w∈chosenPlaces i,w.q=levelPrime i
  chosenPlaces_injective : (·.2.1 : (Σ i,chosenPlaces i)→_).Injective
  star_notMem_chosenPlaces {i j w} : w∈chosenPlaces i→star w∉chosenPlaces j
  g_dvd_iff r : ↑(levelPrime 0 * levelPrime 1) ∣ r↔∀ p : Σ i,chosenPlaces i,reduceAt p.2 r=0∧reduceAt p.2.1 (star r)=0
  card_chosenPlaces i : card (chosenPlaces i)=numInfPlaces E
  star_ϖ : star ϖ = -ϖ
  span_ϖ : differentIdeal ℤ _ = .span {ϖ}
  ϱ_le : 10 ^ 5 ≤ 𝔰.ϱ
  pow_six_le : 2⁻¹ ^ 𝔰.ϱ ≤ b⁻¹ ^ 6
  degree_le : (𝔰.ϱ + 1) * Module.finrank ℚ E≤2 ^ (2 * 𝔰.ϱ)
  pow_le_k : 1000 * (2 * 𝔰.ϱ + 2) ^ 9 ≤ 𝔰.k
  ϱ_le_k : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k
  k_le_f : 𝔰.k≤numInfPlaces E
  size_le : (200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ 1000≤b
  f_le_b : numInfPlaces E≤b / 1000
  k_le_b : 𝔰.k≤b
  rd_le_b : rootDiscr E≤b
  succ_le_b : ↑(𝔰.ϱ + 1)≤b
  thousand_le_b : 1000≤b
  one_le_b : 1≤b
  g_le_b_pow : ↑(levelPrime 0 * levelPrime 1)≤b ^ 23
  le_g : b ^ 19≤↑(levelPrime 0 * levelPrime 1)
  le_N : (5 : ℝ)≤N
  pow_chain : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6∧3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k
variable {E 𝔰} (S : Filling E 𝔰) (R : Type) [CommRing R]
namespace Filling
attribute [instance] fintypeChosen hasFiniteType_columnLevel
attribute [scoped simp] Nat.Prime.ne_zero N_prime levelPrime_prime
abbrev g:=S.levelPrime 0 * S.levelPrime 1
abbrev ratMiddle := 𝔰.middleGram (S.N : R)
abbrev latMiddle:=latMiddleGram 𝔰 (S.N : R)
abbrev G [StarRing R]:=(S.ratMiddle R).G
abbrev GFin:=(S.latMiddle (𝔸f E)).G
abbrev GRes:=∀ i (w : S.chosenPlaces i),GL 𝔰.BesselIndex (ResField w.1)
abbrev BesselCoord:=∀ v,(S.besselSys v).I
def Classes:=DoubleCosets (stdSpace ..).Γf S.columnLevel deriving Nonempty
variable [σ : Side] (T : Set (S.G E)) (c : S.Classes) (s : S.GRes) (c' γ v a i j) (y : InfinitePlace E → 𝔰.G₁)
omit σ
abbrev frameProducts (γ : S.G E):=(S.ratMiddle E).frameGram γ
def latStabilizer:=(intGL _ (Ô E)).subgroupOf S.GFin
protected def reduction : S.latStabilizer →* S.GRes := .pi fun _↦.pi (reduceAt · |> intGL.map |>.comp (S.GFin.subtype.subgroupComap _))
def principalLevel:=S.reduction.ker.map S.latStabilizer.subtype
def reducedImage A:=(Subgroup.subgroupOf A _).map S.reduction
def kappa:=(S.g * Φ v S.ϖ.val / (2 * π * .I)).re
def basisScale : 𝔰.BesselIndex → ℂ := let s a := S.kappa v ^ (𝔰.ϱ - a) / √S.N;(s ·) ⊕ᵥ
    ((1 ⊕ᵥ fun _↦s 𝔰.ϱ) ⊕ᵥ (s ·)⁻¹)
attribute [local simp] zero_lt_iff forall_fin_succ' splitGram middleGram pow_mul' fieldEq discr_ne_zero
lemma map_splitGram_ratMiddle {R'} [CommRing R'] (f : R →+* R') : (S.ratMiddle R).splitGram.map f =
  (S.ratMiddle _).splitGram:=by aesop
def selfDualChar:=(Circle.coeHom.compAddChar (ψf E)).mulShift ↑(-S.ϖ.val⁻¹)
@[simp high] lemma varpi_ne_zero : S.ϖ.val≠0:=mod_cast ne_zero_of_differentIdeal_eq_span S.span_ϖ
def frameScaleSq:=S.kappa v ^ (2 * (𝔰.ϱ - a)) / S.N
def frameScaleProd:=∏ v,∏ a : Fin (𝔰.ϱ + 1),S.frameScaleSq v a ^ (𝔰.k + 2 * (𝔰.ϱ - a))
def unipCovolume := let d := ∑ a ∈ .range 𝔰.ϱ,(a + (𝔰.k + 1) + a);(S.g ^ (2 * d + 𝔰.ϱ) / S.N ^ 𝔰.k) ^ numInfPlaces E / volÔ E ^ d * √√|discr E| ^ 𝔰.ϱ / S.frameScaleProd
def siegelConst:=(π ^ 𝔰.k / (𝔰.k - 1).factorial / S.N ^ 𝔰.k) ^ numInfPlaces E * √√|discr E| * volÔ E ^ 𝔰.k
abbrev termDisc:=frameDisc ↑S.N (S.frameProducts γ)
lemma basisScale_besselFrame : ∀ b,S.basisScale v (𝔰.besselFrame b) =
  S.kappa v ^ (𝔰.ϱ - b) / √S.N:=by simp [basisScale]
lemma coe_kappa : S.kappa v=S.g * Φ v S.ϖ / (2 * π * .I):=conj_eq_iff_re.1 (by
  simpa [map_ofNat] using congr(-Φ v $S.star_ϖ))
@[simp] lemma kappa_ne_zero : S.kappa v≠0:=by simp [← ofReal_ne_zero,coe_kappa]
@[simp] lemma frameScaleSq_pos : 0 < S.frameScaleSq v a:=by simp [frameScaleSq,sq]
lemma frameScaleProd_pos : 0 < S.frameScaleProd:=prod_pos (by simp [prod_pos])
@[simp] lemma basisScale_ne_zero : ∀ i,S.basisScale v i≠0:=by simp [basisScale]
def basisScaleGL:=diagGL (.mk0 _ <| S.basisScale_ne_zero v ·)
lemma gram_basisScaleGL : (S.basisScaleGL v).1ᴴ * (S.ratMiddle ℂ).splitGram * (S.basisScaleGL v).1 =
  (𝔰.middleGram 1).splitGram:=by simp_all [basisScaleGL,basisScale,← ext_iff,← ofReal_pow]
abbrev latBasis:=besselLatticeBasis 𝔰 S.piBar
def toLatBasis : S.G (𝔸f E) ≃* S.GFin:=(U.conj _ (gram_besselLatticeBasis _ _ S.piBar_mul_star)).symm
def ratToAdelic : S.G E →* S.G (𝔸 E):=U.map toAdele (h:=map_splitGram_ratMiddle ..)
def adelicToInf : S.G (𝔸 E) →* type_of% y := .pi fun v↦.comp (U.conj _ (S.gram_basisScaleGL v)).symm (U.map (evalInf v) (h:=map_splitGram_ratMiddle ..))
def adelicToFin : S.G (𝔸 E) →* S.GFin := .comp S.toLatBasis (U.map (.snd ..) (h:=map_splitGram_ratMiddle ..))
def ratToInf:=S.adelicToInf.comp S.ratToAdelic
def ratToFin:=S.adelicToFin.comp S.ratToAdelic
def inclHFin:=S.toLatBasis.toMonoidHom.comp (toBesselH ..)
instance : Fintype S.Classes := @ofFinite _ HasFiniteType.finite_classes
abbrev h:=S.inclHFin c.out
def termPosition:=(S.h c)⁻¹ * S.ratToFin γ * S.h c'
def termsOver:={γ | ∃ k,S.reduction k=s∧k=S.termPosition c c' γ}
def classUnip : Subgroup (S.G E):=besselU ⊓ (S.principalLevel.comap (MulAut.conj (S.h c)⁻¹)).comap S.ratToFin
def classUnip₀:=S.classUnip c ⊓ besselU0
def boxSize:=S.b ^ (2 * 𝔰.n ^ 2)
def IsBoxPartition (ω : _→ENNReal):=Measurable ω ∧ (∀ y v, ω y≠0→InCut (y v) S.b→y v∈frameBox S.boxSize)∧(∀ y (a : S.classUnip c→_),(∀ γ,∑' u : (S.classUnip₀ c).subgroupOf _,a (u.1 * γ)=1)→∑' γ,a γ * ω (S.ratToInf γ * y)=1)∧(∀ y, ω y≤1)∧∀ s y,(∀ v,s v∈besselU0 ⊔ besselH) → ω (s * y) = ω y
def besselFn (i : S.BesselCoord):=∏ v,(S.besselSys v).W σ (y v) (i v)
def besselKernel : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) := .toLp 2 fun i↦S.besselFn y i.1 * star (S.besselFn ((S.ratToInf γ)⁻¹ * y) i.2)
def columnDim:=card S.Classes * card S.BesselCoord
def besselDegree:=∏ v,(S.besselSys v).deg
lemma besselDegree_pos : 0 < S.besselDegree:=prod_pos fun _ _↦(besselSys ..).deg_pos
def mainEnergy:=S.columnDim ^ 2 / (S.besselDegree * mass E 𝔰.r)
abbrev unipOrder:=S.g ^ (numInfPlaces E * (𝔰.ϱ * (2 * 𝔰.k + 2 * 𝔰.ϱ + 1)))
def packetConst:=Nat.card (S.reducedImage besselS) * S.unipOrder * card S.Classes * S.siegelConst
def besselEnergy : ℝ:=Nat.card (S.reducedImage besselS) * S.columnDim
def tailScale:=S.b ^ (𝔰.k * numInfPlaces E / 4 : ℝ)
abbrev codimFactor:=(S.b / S.g) ^ (𝔰.k * numInfPlaces E) * (2 * S.tailScale ^ 2)
class IsAdmissible where
  columnLevel_eq : S.columnLevel=S.principalLevel.comap S.inclHFin
  reduction_surjective : Function.Surjective S.reduction
  ϖ_le v : ‖Φ v S.ϖ.val‖ ≤ S.b
  one_le_abs_kappa v : 1 ≤ |S.kappa v|
  abs_kappa_le v : |S.kappa v| ≤ S.b ^ 23
  N_le : S.N≤S.b ^ (60 * 𝔰.n)
  prod_band_le_inv_deg : ∏ v, 𝔰.bandConst * S.b ^ (7 * 𝔰.k) *
    (|S.kappa v| ^ (2 * 𝔰.ϱ + 1) / (S.g * S.N)) ^ (𝔰.k - 𝔰.n ^ 7)≤S.besselDegree⁻¹
  besselEnergy_le : S.tailScale ^ 44 * S.besselEnergy≤S.mainEnergy
  mainEnergy_le : S.tailScale ^ 18 * S.codimFactor * S.mainEnergy≤S.besselEnergy
  codimFactor_le_one : S.codimFactor≤1
  card_besselCoord_le : card S.BesselCoord≤S.b ^ (2 * 𝔰.k * numInfPlaces E)
  le_relIndex : (S.N ^ 𝔰.k / S.b) ^ numInfPlaces E ≤
    (S.latStabilizer.comap S.inclHFin).relIndex (Kf E _)
  packetConst_mul_mass_le : S.packetConst ≤
    (1 + S.b⁻¹ ^ 9) * S.mainEnergy * S.besselDegree * 𝔰.openCellConst ^ numInfPlaces E /
    volÔ E ^ 𝔰.n * (S.unipCovolume * S.frameScaleProd / card S.BesselCoord) ^ 2
lemma adelicToInf_apply : (S.adelicToInf γ v).1 i j=(γ.1 i j).1 v *
  (S.basisScale v j / S.basisScale v i):=by simp! [adelicToInf,basisScaleGL,U.map,diagGL]
@[simp] lemma ratToInf_apply : (S.ratToInf γ v).1 i j = Φ v (γ.1 i j) * (S.basisScale v j / S.basisScale v i):=adelicToInf_apply ..
private lemma coe_ratToFin : S.ratToFin γ = S.latBasis⁻¹ * .map (algebraMap E _) γ * S.latBasis:=rfl
instance : Countable (S.G E):=Units.val_injective.injOn.injective.countable
lemma finite_classUnip_inter_compact {m} [Finite m] (f : m→_) {C} (hC : IsCompact C) : (C ∩ range fun (u : S.classUnip c) v↦(S.ratToInf u v).1.1.submatrix f f).Finite := .subset (.pi' fun v↦.pi' fun i↦.pi' fun j↦(isCovolOneLattice_ratAdeles.finite_preimage ((hC.prod (isCompact_intGL isCompact_Ô)).image_auto fun p↦((p.1 · i j) * (S.basisScale · (f i)) / (S.basisScale · (f j)),(S.latBasis * (S.h c).1 * p.2 / (S.latBasis * (S.h c).1) :) (f i) (f j)))).image (Φ v · * _))
  (by rintro _ ⟨h,⟨u,_,k,_⟩,⟨⟩⟩ v i j
      exact ⟨_,⟨(_,_),⟨h,k.2⟩,by aesop (add simp [coe_ratToFin,mul_assoc])⟩,(ratToInf_apply ..).symm⟩)
lemma exists_cutoff_classUnip {c}
  K : let Γ := Subgroup.map (S.ratToInf.domRestrict (S.classUnip c)) K;∃ β,Measurable β
    ∧ (∀ y,∑' u : K, β (S.ratToInf u * y)=1)∧DiscreteTopology Γ ∧ IsCutoff (H := Γ) .count β :=
  have:=Continuous.discrete_of_tendsto_cofinite_cocompact (by fun_prop)
    (tendsto_cofinite_cocompact_iff.2 fun _↦.of_injOn (fun ⟨_,u,_,rfl⟩↦(⟨·,u,rfl⟩)) Units.val_injective.injOn.injective.comp_left.injOn.injective.injOn∘S.finite_classUnip_inter_compact c id)
  (hasCutoff_count _).1.imp fun _ h↦⟨h.1,((((K.equivMapOfInjective _ fun _↦by simp [funext_iff,↓Subtype.ext_iff,↓Units.ext_iff,← ext_iff,(RingHom.injective _).eq_iff]).tsum_eq _).trans (lintegral_count _).symm).trans <| h.2 ·),this,h⟩
@[irreducible] def classCutoff:=(S.exists_cutoff_classUnip ((S.classUnip₀ c).subgroupOf (S.classUnip c))).choose * epsilon (S.IsBoxPartition c)
def amplitude:=∫ y,(S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y)).toReal•S.besselKernel γ y
def amplitudeAbs:=∫⁻ y,S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) * ‖S.besselKernel γ y‖ₑ
def amplitudeSum:=∑' γ : ↥(T ∩ S.termsOver c s c'),S.amplitude c c' γ
lemma abs_kappa_eq : |S.kappa v| = S.g * ‖Φ v S.ϖ‖ / (2 * π) :=
  by simpa [abs_of_pos pi_pos] using congr(‖$(S.coe_kappa v)‖)
@[simp] lemma realFrameGram_ratToInf : ∀ a b,realFrameGram (S.ratToInf γ v) a b=↑(S.kappa v ^ (𝔰.ϱ - a) * S.kappa v ^ (𝔰.ϱ - b) /
  S.N) * Φ v (S.frameProducts γ a b):=by simp [frameGram,mul_apply,basisScale,← ofReal_pow]
lemma det_submatrix_realFrameGram_ratToInf {n} [Fintype n] (e : n→_) : ((realFrameGram (S.ratToInf γ v)).submatrix e e).det=(∏ a,delta% S.frameScaleSq v (e a)) * Φ v
  ((S.frameProducts γ).submatrix e e).det:=by simp [det_apply,sq,mul_sum,mul_smul_comm,prod_pow_eq_pow_sum,Equiv.sum_comp _ (𝔰.ϱ - e ·)]
lemma unipCovolume_pos : 0 < S.unipCovolume:=div_pos (by bound) S.frameScaleProd_pos
def gIdele : (𝔸f E)ˣ := .map (algebraMap E _).1 (.mk0 S.g (by simp))
def unipotentChar (u : S.GFin):=S.selfDualChar (S.gIdele⁻¹ * simpleRootSum u)
def Agrees:=∀ u u',u.1∈besselU→u'.1∈besselU→S.reduction u * s=s * S.reduction u'→S.unipotentChar u=S.unipotentChar u'
def IsStable:=∀ᵉ (u∈besselU) (u'∈besselU) (γ),u⁻¹ * γ * u'∈T ↔ γ ∈ T
def termsOfLink Λ := {γ | S.termDisc γ ≠ 0∧link γ = Λ}
export Filling.IsAdmissible (one_le_abs_kappa abs_kappa_le N_le codimFactor_le_one)
end Filling
end
noncomputable section
namespace Filling
open NumberField Matrix Complex Circle Finset Real Prod intGL IsHermUnit
section
variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
attribute [local simp] BlockTriangular coe_ratToFin GT unipotentChar toLatBasis h termPosition val_toBesselH_apply_coe mul_assoc fourierChar_apply inclHFin funext_iff
attribute [-simp] Sum.forall
attribute [local aesop simp] selfDualChar gIdele splitGram middleGram latMiddleGram besselLatticeBasis FI.level
lemma map_splitGram_latMiddle : (S.latMiddle R).splitGram.map f =
  (S.latMiddle _).splitGram:=by aesop
lemma _root_.Membership.mem.map_mem_unitriangularOn {r h} {H : Subgroup (GL 𝔰.BesselIndex _)} {γ} :
    γ ∈ (agreeWithOneOn r _ h).subgroupOf H → .map f γ.1∈agreeWithOneOn r _ h:=by aesop
instance : IsHermUnit (S.ratMiddle E):=⟨by aesop,by simp [isUnit_iff_isUnit_det,middleGram]⟩
variable {c s c' t c'' x} {γ δ : S.G E} (u)
lemma toLatBasis_mem_besselU : S.toLatBasis x∈besselU↔x∈besselU:=⟨(by
  simpa using! conj_mem_unitriangular (d:=S.latBasis⁻¹) (by aesop) ·.out),(conj_mem_unitriangular (by aesop) ·.out)⟩
@[simp] lemma ratToFin_mem_besselU : S.ratToFin γ ∈ besselU ↔ γ ∈ besselU:=toLatBasis_mem_besselU.trans (by simp [mem_besselU,← algebraMap.coe_inj E (𝔸f E)];rfl)
lemma inclHFin_mem_besselH k : S.inclHFin k∈besselH:=by simp [besselLatticeBasis,Sum.forall]
lemma range_inclHFin : S.inclHFin.range=besselH:=le_antisymm (fun _ ⟨k,e⟩↦e▸inclHFin_mem_besselH k) fun _ h↦.imp (fun _↦S.toLatBasis.eq_symm_apply.1 ∘ .symm) (exists_toBesselH_eq (by apply mul_mem (mul_mem _ h.out) <;> aesop) (by simp [← piBar_mul_star]))
lemma ratToFin_toBesselH γ : S.ratToFin (toBesselH _ _ γ) =
  S.inclHFin (stdEmbFin γ):=by ext;simp [stdSpace_embFin γ]
def classBasis (c : S.Classes):=(toBesselH _ ↑S.N c.out).1 * S.latBasis
lemma coe_termPosition c c' γ : (S.termPosition c c' γ).1 =
  (classBasis c)⁻¹ * .map (algebraMap E _) γ * classBasis c':=by simp [classBasis]
lemma _root_.Membership.mem.termPosition_mem_besselU c : γ ∈ besselU→S.termPosition c c γ ∈ besselU:=(besselS_le_normalizer_besselU (mem_unitriGroup_of_mem_floorGroup (inv_mem (inclHFin_mem_besselH _))) _).1∘ratToFin_mem_besselU.2
lemma termsOver.mul : γ ∈ S.termsOver c s c' → δ ∈ S.termsOver c' t c'' → γ * δ ∈ S.termsOver c (s * t) c'' | ⟨k,_⟩ => .imp' (k * ·) (by aesop)
lemma termsOver.inv : γ ∈ S.termsOver c s c' → γ⁻¹ ∈ S.termsOver c' s⁻¹ c := .imp' (·⁻¹) (by aesop)
@[local simp] lemma simpleRootSum_adelicToFin : simpleRootSum (S.adelicToFin u)=(simpleRootSum u).2:=by
  simp [-sum_add_distrib,simpleRootSum,snd_sum,adelicToFin,besselLatticeBasis,mul_apply,U.map];congr with a
  refine a.succ.lastCases ?_ ?_ <;> simp
@[simp] lemma simpleRootSum_ratToAdelic : simpleRootSum (S.ratToAdelic u)=simpleRootSum u := .symm (map_sum ..)
@[simp] lemma norm_selfDualChar : ‖S.selfDualChar x‖ = 1:=norm_coe _
lemma _root_.Membership.mem.ratToInf_mem_unitriangularOn {r h} (k : γ ∈ (agreeWithOneOn r _
  h).subgroupOf _) v : S.ratToInf γ v∈(agreeWithOneOn r _ h).subgroupOf _:=by aesop
lemma besselFn_adelicToInf_mul [Side] (h : x∈besselU) y : S.besselFn (S.adelicToInf x * y)=(stdAddChar E (↑(-(S.g * S.ϖ : E)⁻¹) * simpleRootSum x) / S.unipotentChar (S.adelicToFin x))•S.besselFn y:=by
  set z : 𝔸 E:=_ * _;rw [show unipotentChar .. = ψf E z.2 by aesop]
  simp [besselFn,fun v↦(by simp [z,simpleRootSum,fst_sum,← sum_mul,↓adelicToInf_apply,↓basisScale_besselFrame,pow_sub₀,pow_succ',div_eq_inv_mul,coe_kappa,field] : simpleRootSum
    (S.adelicToInf x v) = -π * 2 * .I * z.1 v),stdAddChar,wave,↓sub_conj,← Complex.exp_sum,mul_sum,sum_mul,((besselSys ..).tail.isBesselFunction _).2 (S.adelicToInf x _) (conj_mem_unitriangular (blockTriangular_diagonal _) (h.map_mem_unitriangularOn _))]
lemma besselFn_ratToInf_mul [Side] (h : γ ∈ besselU) y : S.besselFn (S.ratToInf γ * y)=(S.unipotentChar (S.ratToFin γ))⁻¹ • S.besselFn y:=(besselFn_adelicToInf_mul (h.map_mem_unitriangularOn _) y).trans (by simp [← map_mul, -map_neg,ratToFin])
end
variable {E} [Field E] [CMType E] {𝔰} (S : Filling E 𝔰) {F} [CommRing F]
attribute [local instance 0] starRingOfComm
lemma isUnimodular_latMiddle [StarRing F] {R} :
  IsUnimodular R (S.latMiddle F):=by simp [isUnimodular_latMiddleGram]
instance [StarRing F] : IsHermUnit (S.latMiddle F):=S.isUnimodular_latMiddle (R := ⊤).rec (⟨·,·.imp (by simp)⟩)
lemma transpose_splitGram : (S.latMiddle F).splitGramᵀ = (S.latMiddle F).splitGram := .trans (by rfl) conjTranspose_eq
def idOrInvAdjoint b:=cond b (MulAut.conj (isUnit (J:=(S.latMiddle F).splitGram)).unit⁻¹ * invTransposeGL) 1
def reduceAboveG (x : (Σ i,S.chosenPlaces i) × _):=(reduceAt x.1.2.1).comp (cond x.2 starRingAut 1).toRingHom
lemma intGL_map_reduceAboveG (k : S.latStabilizer) i w b : intGL.map (S.reduceAboveG (⟨i,w⟩,b))
  ⟨k,k.2⟩=S.idOrInvAdjoint b (S.reduction k i w):=b.rec rfl (k.rec fun k ⟨g,e⟩↦by
  obtain ⟨g, -,⟨⟩⟩ :=
    U.mem_range_map (by simp) (Ô E).subtype_injective isUnit (S.map_splitGram_latMiddle _) congr($e)
  simpa [idOrInvAdjoint,mul_assoc,eq_inv_mul_iff_mul_eq,Units.ext_iff,map_splitGram_latMiddle,transpose_splitGram, -coe_units_inv] using! congr($(U.form_mul_inv_eq g)ᵀ.map (reduceAt w)).symm)
lemma gIdele_val : S.gIdele.1=S.g:=by simp [gIdele]
lemma gIdele_mem : ↑S.gIdele ∈ Ô E:=by simp [gIdele,mul_mem]
lemma forall_selfDualChar_mul_eq_one_iff a : (∀ r : Ô E,S.selfDualChar (r * a)=1)↔a ∈ Ô E:=by simpa [selfDualChar,map_eq_one_iff coeHom @Circle.ext,← Algebra.smul_def,← mul_neg,forall_ψf_mul_eq_one,← Algebra.mul_smul_comm,S.span_ϖ,Ideal.mem_span_singleton', -algebraMap_smul] using ⟨(one_mul a▸· 1),fun h _↦mul_mem (coe_mem_Ô _) h⟩
lemma selfDualChar_eq_one_of_mem : ∀ x ∈ Ô E,
  S.selfDualChar x=1:=by simpa using S.forall_selfDualChar_mul_eq_one_iff 1
lemma inv_gIdele_smul_mem_iff r : S.gIdele⁻¹ • r.1 ∈ Ô E↔∀ x,S.reduceAboveG x
  r=0:=by simpa [dvd_def,Subtype.ext_iff,← gIdele_val, -Nat.cast_mul,reduceAboveG,← S.gIdele.inv_mul_eq_iff_eq_mul] using! S.g_dvd_iff r
lemma principalLevel_eq_unitaryLevel : S.principalLevel=unitaryLevel (Ô E) S.gIdele _:=le_antisymm (fun _ ⟨k,h,e⟩↦e▸⟨k.2,((S.inv_gIdele_smul_mem_iff ⟨_,_⟩).2 fun _↦map_eq_one.1 ((intGL_map_reduceAboveG ..).trans (by aesop)) · ·)⟩) fun k ⟨m,h⟩↦⟨⟨k,m⟩,funext₂ (map_eq_one.2 fun _ _↦(inv_gIdele_smul_mem_iff ..).1 (by apply h) ⟨⟨·,·⟩,false⟩),rfl⟩
