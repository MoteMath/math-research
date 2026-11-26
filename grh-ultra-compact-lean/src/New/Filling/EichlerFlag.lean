import Lib.General.Topology.LocalDefs
import Lib.DiscreteSeries.Bruhat.BigCell
seal Finset.univ Finset.sum Finset.prod
noncomputable section
open Fin ComplexOrder Filling Finset Function Matrix MeasureTheory Sum
def latMiddleGram {R} [CommRing R] (𝔰 : Shape) (N : R)
    : 𝔰.Form R := let c := of fun i _↦ite (i = 𝔰.k₀) (-1) 0
  (scaleAt 0 𝔰.k₀).fromBlocks c cᵀ (of fun _ _↦-N)
section
attribute [local simp] diagonal entrywise latMiddleGram
variable {R} [CommRing R] (𝔰 : Shape) [StarRing R] (p : Rˣ)
def middleBaseChange:=(scaleAt (star p.1) 𝔰.k₀).fromRows (of fun () j↦ite (j = 𝔰.k₀) (-p⁻¹) 0)
def besselLatticeBasis : GL 𝔰.BesselIndex
  R:=by use fromBlocks 1 0 0 (((scaleAt (star p⁻¹.1) 𝔰.k₀).fromBlocks 0 (of fun _ j↦ite (j = 𝔰.k₀) ↑(p * star p)⁻¹ 0) 1).fromBlocks 0 0 1),fromBlocks 1 0 0 (((middleBaseChange 𝔰 p).fromCols (fromRows 0 1)).fromBlocks 0 0 1) <;> simp [middleBaseChange,← star_mul,mul_right_comm _ p⁻¹.1] <;> grind
variable {𝔰} (N : R) {T : 𝔰.Form R} (γ : T.G)
def frameDisc Z := let d := leadingMinor Z 𝔰.top.castSucc;Z.det * star Z.det - N ^ 2 * (d * star d)
lemma gram_besselLatticeBasis : p * star ↑p=N→(besselLatticeBasis 𝔰 p).1ᴴ * (𝔰.middleGram N).splitGram * besselLatticeBasis 𝔰 p=(latMiddleGram 𝔰 N).splitGram:=by simp [besselLatticeBasis,splitGram,middleGram];grind [p.mul_inv,star_mul,star_one,star_star,star_zero]
abbrev framePair:=(frameImage 1).fromCols (frameImage γ.1.1)
abbrev isotropicFramePair:=(framePair γ).submatrix id (.map castSucc castSucc)
def linkMatrix := let m (x : T.G) := x.1.1.toRows₂.toRows₁;(m 1).fromRows (m γ⁻¹)
def link:=((isotropicFramePair γ)ᴴ * T.splitGram).mulVecLin.ker.map (linkMatrix γ).mulVecLin
end
def dampedPower k (r : ℝ):=r ^ k * min 1 r ^ 6
def headWeight K i (p : ℕ → ℂˣ):=∏ l∈range i,dampedPower K ‖∏ a∈range (l + 1),(p a).1‖⁻¹
variable {C U τ : Type} [CommRing C] [MeasureSpace C] [TopologicalSpace U] [Fintype τ] {u : C→U} {ι : U→C} {n J} {ψ : C → ℂ} {En Λ} {β : C → ℝ} {A} [CommRing A] {R} {𝔰 : Shape} {i'}
structure SieveSystem (u : C→U) (ι : U→C) (n : ℕ) (J : ℕ→_→_ → ℂ) (ψ : C → ℂ) (En : ℝ)
    (Λ : ℕ→_ → ℝ) (β : C → ℝ) where
  psi_zero : ψ 0=1
  step i p q ξ : i≤n→let f c := ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c))
    Integrable f∧(ξ = 0→∫ c,f c=J i p q)∧(IsUnit ξ → ‖∫ c,f c‖ ≤ β ξ * (Λ i p * Λ i q))
  posSemidef {κ : Type} [Fintype κ] (a : κ → ℕ→U) t : (∀ i,a i n=t) →
    (of fun i j↦J (n + 1) (a i) (a j)).PosSemidef
  continuous : Continuous (J (n + 1)).uncurry
  norm_bot_le p q : ‖J 0 p q‖ ≤ En
  off_diagonal i p q : i < n→let ξ := ι (p i) - ι (q i)
              IsUnit ξ → ‖J (i + 1) p q‖ ≤ β ξ * (Λ (i + 1) p * Λ (i + 1) q)
lemma SieveSystem.pi (K : SieveSystem u ι n J ψ En Λ β) [SFinite (@volume C _)] {ι' Λ'} {J' En' γ : τ → _} (H : ∀ v,SieveSystem unitOrOne ι' n (J' v) wave (En' v) Λ' (γ v)) : SieveSystem (Prod.map (unitOrOne∘·) u) (.map (ι'∘·) ι) n (fun i p q↦(∏ v,J' v i ((·.1 v)∘p) ((·.1 v)∘q)) * J i ((·.2)∘p) ((·.2)∘q)) (fun x↦(∏ v,wave (x.1 v)) * ψ x.2) ((∏ v,En' v) * En) (fun i p↦(∏ v, Λ' i ((·.1 v)∘p)) * Λ i ((·.2)∘p)) fun x↦(∏ v, γ v (x.1 v)) * β x.2:=by
  use (by simp [K.1,wave]) <;> (try simp only [Pi.isUnit_iff,Prod.isUnit_iff,comp_update,← prod_mul_distrib,mul_mul_mul_comm _ _ (∏ _,_),and_imp]) <;> intros
  choose A B C using (H · |>.step);choose a b c using K.step
  use .mul_prod (.fintype_prod (by tauto)) (a _ _ _ _ ‹_›), ?_,fun _ _↦.trans ?_
    (norm_mul_le_of_le (by grw [← C,← norm_prod] <;> tauto) (by tauto)) <;> simp +contextual [*, -integral_const_mul,← B,← b,← integral_fintype_prod_eq_prod,← integral_prod_mul] <;> tauto
  next t e => exact univ.induction (by simp [K.3,e]) (fun v _ _↦by
    simpa [mul_assoc, *] using! ((H v).3 _ (t.1 v) (by simp [e])).hadamard)
  obtain _:=(H · |>.4),K.4;fun_prop;solve_by_elim* (maxDepth:=40) [norm_mul_le_of_le,(norm_prod ..).trans_le,prod_le_prod₀,off_diagonal,norm_bot_le,norm_nonneg]
lemma SieveSystem.q4 (K : SieveSystem u ι n J ψ En Λ β) {i} (hi : i≤n) (a : τ → _) :
  let F c := ∑ p,∑ q,J (i + 1) (update (a p) i (u c)) (update (a q) i (u c))
  Integrable F∧∫ c,F c=∑ p,∑ q,J i (a p) (a q)∧∀ ξ,IsUnit ξ → ‖∫ c, ψ (ξ * c) * F c‖ ≤
    β ξ * (∑ p, Λ i (a p)) ^ 2:=by obtain ⟨⟨⟩⟩:=K,K.2 (ξ := 0);simp_all [integrable_finsetSum,integral_finsetSum,sq,mul_sum,↓sum_mul,← sum_product',norm_sum_le_of_le]
lemma SieveSystem.q5 [TopologicalSpace C] [FirstCountableTopology C] (K : SieveSystem u ι n J ψ En Λ β) {i} (h : i≤n) (b : C → τ → ℕ→U) {c : C→U}
  (e : ∀ x p,b x p i=c x) : let F x := ∑ p,∑ q,J (i + 1) (b x p) (b x q);0≤F∧∀ x,(∀ p,ContinuousAt (b · p) x)→LowerSemicontinuousAt (ENNReal.ofReal <| RCLike.re <| F ·) x := by
  induction' h using Nat.decreasingInduction with i hi ih generalizing b c
  choose N L using fun z↦ih _ (update_self _ _ <| b · ·)
  choose I e _ using (K.q4 hi <| b ·)
  simp_rw [← e,← integral_re (I _),lowerSemicontinuousAt_iff_le_liminf,ofReal_integral_eq_lintegral_ofReal (I _).re (.of_forall (N · _ |>.1))] at *
  use (integral_nonneg <| Function.swap N ·),fun x _↦by
    grw [← lintegral_liminf_le' (I · |>.re.aemeasurable.ennreal_ofReal),L];fun_prop
  use by simpa [entrywise] using! (e · |> K.3 _ _ |>.dotProduct_mulVec_nonneg 1),
    fun x _↦ContinuousAt.lowerSemicontinuousAt (ENNReal.continuous_ofReal.continuousAt.comp (by cases K;fun_prop))
attribute [-simp] Finset.sum_sub_distrib
def finHeadWeight {A} [SemilocalField A] K i (p : ℕ→Aˣ):=∏ l ∈ .range i,
  let D := ∏ a ∈ .range (l + 1),(p a).1;if D∈SemilocalField.O then √(genIndex D) ^ K else 0
lemma isUnimodular_latMiddleGram [StarRing A] 𝔰 {N : A} (h : N∈R∧star N=N) : IsUnimodular R
  (latMiddleGram 𝔰 N):=by use ?_,⟨latMiddleGram 𝔰 N,latMiddleGram 𝔰 0 + diagonal (Pi.single (inl 𝔰.k₀) N), ?_, ?_⟩ <;> aesop (add simp [latMiddleGram,mul_apply,diagonal,mem_intGL])
lemma frameImage_one_mulVec : @frameImage A 𝔰 1 *ᵥ i'=init i' ⊕ᵥ ((0 ⊕ᵥ fun _↦i' 𝔰.top) ⊕ᵥ 0):=funext (by simp [init,mulVec_eq_sum,sum_univ_castSucc])
lemma frameImage_mulVec γ x : @frameImage A 𝔰 γ *ᵥ x =
  γ *ᵥ frameImage 1 *ᵥ x:=by simp [← mul_inclMatrix]
lemma exists_star_vecMul_eq [StarRing A] (J : Matrix 𝔰.BesselIndex _ A) [h : IsHermUnit J] l : ∃ v,star v ᵥ* J=l:=⟨star (l ᵥ* ↑h.2.unit⁻¹),by simp [-coe_units_inv]⟩
variable {A : Type} [CommRing A] [StarRing A] {T : Shape.Form 𝔰 A} {v} in
lemma exists_mem_besselU_eq_eichlerMap [h : IsHermUnit T.splitGram] [TraceOne A] a j r {m} (Z : star v ᵥ* T.splitGram=m) (l : ∀ b≥a,j b=0) (H : ∀ b < a,m (𝔰.besselFrame b)=0) : ∃ u∈T.besselU,simpleRootSum u=r * m ∘ 𝔰.besselFrame ⬝ᵥ cons 0 (init j)∧u.1.1=eichlerMap T.splitGram (r•frameImage 1 *ᵥ j) v (TraceOne.τ * star v ⬝ᵥ T.splitGram *ᵥ v):=by
  refine (exists_unitary_eq_eichlerMap h.1 ?_ ?_ (by simp [star_form h.1,← add_mul])).imp fun u e ↦
    ⟨?_, ?_,e⟩ <;> simp_all [← Z,eichlerMap,frameImage_one_mulVec,le_last,simpleRootSum,vecMulVec,FI.level,mem_besselU,init,splitGram,vecMul,entrywise,forall_fin_succ',sum_univ_succ,mul_sum]
  iterate 2 grind [sum_eq_zero,star_zero]
  congr with x
  cases h : x.succ using lastCases <;> simp <;> grind
