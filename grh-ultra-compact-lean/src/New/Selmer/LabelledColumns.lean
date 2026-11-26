import Lib.ClassField.GaloisCohomology.TameCocycles
import New.Rows.Carrier
import Lib.GaloisRep.LocalGlobal.LabelCompatibility
import New.Selmer.HeckeStableSubspaces
section
open Fintype IsDiscreteValuationRing Module Multiplicative NonarchimedeanGroup QZ QuotientGroup Set Subgroup Submodule Matrix.Module
variable (E) [Field E] [UnramCMField E] {E'} [Field E'] [UnramCMField E'] (S I' : Finset (FinPlace E')) {q ℓ : ℕ}
structure AuxPrimeData (q) where
  place : ClosurePlace
  (γ φ : Gal(Ω/E)) h : Gal(Ω/E) →* Multiplicative (ZMod q)
variable {E : Type} [Field E] [UnramCMField E]
structure IsAnticyclotomicAt (T P) {q : ℕ} (l : AuxPrimeData E q) extends IsFromU1 T {P} l.h where
  norm_modEq : P.q ≡ 1 [MOD q]
  isPlaceOver : IsPlaceOver l.place P
  isFrob : IsFrob l.place P.q l.φ
  notMem : P ∉ T
  tame_gen : l.γ ∈ inertiaGroup _ l.place ∧ l.h l.γ = .ofAdd 1 ∧ isPlaceOver.tameGenerator = l.γ
@[grind] def IsAuxiliary := ∀ v ∈ I', v ∉ S ∧ v.q.Prime ∧ star v ∉ I' ∧ star v ∉ S
structure IsFamily (S : Finset (FinPlace E)) {ℓ : ℕ} {T} [ThePrime ℓ] (ν :
  T → Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) (val : _ → (Gal(Ω/E) →* PadicAlgCl ℓ) → _) where
  continuous_unitary i : Continuous (ν i)
  exists_interp I : IsAuxiliary S I → ∃ (α : Type) (_ : Fintype α) (g c : α → _),
    (∀ a, ‖c a‖ ≤ 1) ∧ ∀ χ, val I χ = ∑ a, c a * χ (g a)
  val_insert_le I : ∀ P ∉ I, IsAuxiliary S (insert P I) → ∀ χ, IsFromU1 (placesDividing E ℓ) I χ →
    ∀ (A : ClosurePlace) φ, IsPlaceOver A P → IsFrob A P.q φ → ∀ c : NNReal, (∀ i (t : ℤˣ),
    ellVal (1 - (ν i φ).1 * χ φ ^ t.1) ≤ c) → ellVal (val (insert P I) χ) ≤ ellVal (val I χ) + 8 * c
  val_empty_ne_zero : val ∅ 1 ≠ 0
variable {E₁ : Type} [Field E₁] [UnramCMField E₁] {ℓ' : ℕ} [ThePrime ℓ] {E Λ J : Type} [Field E] [UnramCMField E] [CommRing Λ] {e'} (ν) (w' : J → FinPlace E) (τ φ : J → Gal(Ω/E)) (a' : Gal(Ω/E)) (S Q : Finset (FinPlace E))
lemma p3 [ThePrime ℓ'] N (S : Finset (FinPlace E₁)) {R} (h₀ : R.Finite) {z W} (h : z ∈ normalClosure (inertiaAbove (R \ (.conjClosure S ∪ placesDividing E₁ ℓ')))) (hW : W ∈ nhds z) : ∃ P ∉ R.conjClosure, P.q.Prime ∧ ∃ l : AuxPrimeData E₁ (ℓ' ^ N), l.φ ∈ W ∧ l.h l.φ = 1 ∧ ∀ T ⊆ ↑S ∪ placesDividing E₁ ℓ', IsAnticyclotomicAt T P l := by
  choose T hS _ B _ using exists_sup_idelesUnitOff_eq_top (star '' S ∪ S ∪ placesDividing E₁ ℓ').toFinite _ h₀; choose s hs using (SUnit.dirichlet_unit_theorem hS).1.1; choose y hy using (IsAIC.exists_pow_eq (ℓ' ^ N) <| algebraMap E₁ Ω ·)
  choose P hP hp A hA σ H F G using chebotarev ((isOpen_ker_cycCharMod.1.inter (by simp
    [isOpen_iInter_of_finite, stabilizer_isOpen_of_isIntegral])).inter isOpen_setOfPred_eventually_nhds) ⟨z, ((cycCharMod Ω (ℓ' ^ N)).ker ⊓ ⨅ u : s, MulAction.stabilizer _ (y u.1.1)).normalCore.normalClosure_le_normal (by
    rintro g ⟨v, r, A, a, hg⟩ b; refine
    ⟨cycCharMod_of_mem_inertiaGroup (hg.conj b) ?z, Subgroup.mem_iInf.2 fun u ↦ inertia_fixes_root_of_unit (hg.conj b) ?z (hy _) ((a.smul b).valuationVia_eq_one_iff.2 (u.1.2 _ ?_)) ?_⟩ <;> simp_all [(a.smul b).valuation_natCast_eq_one_iff, placesDividing, (B v _).mt]) h 1, hW⟩ (hS.union h₀.cj)
  choose k hk using (Nat.modEq_iff_exists_eq_add hp.pos).1 ((F.mem_ker_cycCharMod_iff (by simp [hA.valuation_natCast_eq_one_iff]; grind [placesDividing])).1 H.1.1).symm; choose _ _ e o _ using hA.exists_localArtin_eq_tameGenerator; let r := (LocInt P).unitGroupToResidueFieldUnits.comp (.mk' (fun t ↦ ⟨t * uniformizer P ^ (Valued.v t.1).log, (Valued.v.mem_unitGroup_iff ..).2 (by simp [WithZero.exp_neg, -WithZero.inv_exp])⟩) (by simp [Subtype.ext_iff, zpow_add]; grind))
  have R t (h : Valued.v (t.1 - 1) < 1) : r t = 1 := Units.ext
    (residue_eq_iff_valuation_sub_lt_one.2 (by simpa [by simpa using Valued.v.map_one_add_of_lt h]))
  have n := (orderOf_eq_card_of_forall_mem_zpowers o).trans (card_ResField P ▸ Nat.card_units _); let f := (monoidHomOfForallMemZpowers o (g' := ofAdd (1 : ZMod (ℓ' ^ N))) (by simp [*])).comp r
  have L t : r (t ^ k) = 1 → f t = 1 := (o (r t)).elim fun _ e ↦ by
    simpa [f, ← e, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, n, hk] using Int.dvd_of_mul_dvd_mul_right (by grind [hp.one_lt])
  choose η hθ using (((mk' (principalIdele (K := E₁)).range).domRestrict (idelesUnitOff T)).liftOfSurjective (MonoidHom.range_eq_top.1 (comap_injective (mk'_surjective _) (by simpa)))).symm.surjective ⟨(f.comp _).domRestrict _, by
    simp; rintro ⟨_, b⟩ ⟨_, ⟨⟩⟩
    exact mem_span.1 (hs.ge (x := ⟨_, principalIdele_mem_idelesUnitOff.1 b⟩) ⟨⟩)
      ((f.comp (ideleAt P)).comp (principalIdele.domRestrict _)).ker.toAddSubgroup.toIntSubmodule fun u hu ↦ L _ (R _ (by
    have v := by simpa [NeZero.ne, ← hy, valuationVia] using hA.valuationVia_eq_one_iff.2 (u.2 P (by grind))
    simpa using! (v_algebraMap_eq_valuation (u.1.1 ^ k - 1)).trans_lt
      (hA.isEquiv.lt_one_iff_lt_one.1 (by simpa [← (Subgroup.mem_iInf.1 H.1.2 ⟨_, hu⟩).symm, pow_add, pow_mul, *, ← mul_one_sub, Valuation.map_sub_swap] using F.2 _ v.le))))⟩
  let θ := η.comp (mk' _); have V a h : θ a = f (ideleAt P a) := congr($hθ.1 ⟨a, h⟩)
  choose h hh d using exists_comp_artinMap Gal(Ω/E₁) (θ.comp (.id _ / starMulAut.toMonoidHom))
    ((continuous_of_continuousAt_one _ ((((Continuous.of_isOpen_ker f (isOpen_of_forall_pow_mem (by simp) (pow_index_mem _))).comp_continuousOn (by fun_prop)).congr V).continuousAt ((isOpen_idelesUnitOff T).mem_nhds (by simp)))).comp (continuous_id.div' continuous_star)) fun x ↦ le_comap_mk' _ η.ker ⟨x / star x, by aesop⟩
  have g := d _ _ (hA.artinAt_eq_of_localArtin_eq e ▸ artinMap_locIdele ..); simp [star_locIdele, ↓locIdele_mem_idelesUnitOff, *, f, r, (isSplit_of_q_prime hp).symm] at g; have F := by simpa using F.mul_iff.2 (hA.tameGenerator ^ (h σ⁻¹).toAdd.val).2
  exact ⟨P, hP ∘ .inr, hp, ⟨A, _, _, h⟩, (G _ F).2.self_of_nhds, by ext; simp [g], fun _ t
    ↦ ⟨⟨(hh.1 · ⟨⟩), θ, (le_comap_mk' _ η.ker ⟨·, rfl⟩), by grind [mem_idelesUnitOff, star_star, MonoidHom.comp_apply], d⟩, by simp [*], hA, F, by grind, hA.tameGenerator.2, g, rfl⟩⟩
def s23_m5 (O : CoeffRing ℓ) S ν e := {c ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ ∪ .conjClosure S) ∅ (QuotSpan (ℓ ^ ν : ↑O)) | (∀ g, c (conjGal g) = c g) ∧ ∀ g ∈ shaLocalSet ℓ E 1, c g = 0}
def s23_q3 (w : J → FinPlace E) (τ φ : J → Gal(Ω/E)) := ∀ j, w j ∉ placesDividing E ℓ ∧ cycCharMod Ω (ℓ ^ ν) (φ j) = 1 ∧ ∃ A, ∃ h : IsPlaceOver A (w j), h.tameGenerator = τ j
noncomputable abbrev s23_q1 (k : J × _) := idOrConjInv k.2 (τ k.1)
structure IsPrimeTriangle (w : J → FinPlace E) (τ φ : J → Gal(Ω/E)) (a : Gal(Ω/E)) [LinearOrder J]
  [Fintype J] (t) (ty : J →o {e : Fin t // 0 < e.1}) (h c) where
  isNewPlaces : s23_q3 ν w τ φ
  detect : ∃ s : Finset _, (card J + s.card) * h ≤ c ∧ ∀ (O : CoeffRing ℓ) e, ∀ z ∈ selmerModule
    (tateTwist ℓ E O e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : ↑O)), (∀ g ∈ s, z g = 0) → z = 0
  prod_dvd (e : Fin t) : ∏ k ∈ {e}ᶜ, ((cycChar Ω ℓ a⁻¹ ^ e.1).1 - (cycChar Ω ℓ a⁻¹ ^ k.1).1) ∣ ℓ ^ h
  step O j : ∀ z ∈ s23_m5 O (.range w) ν (ty j).1, (∀ i < j,
    z (τ i) = 0 ∧ ((ty i).1 = (ty j).1 → z (φ i) = 0)) → ℓ ^ h • z (τ j) = 0
  coboundary (O : CoeffRing ℓ) e : let d g := cycInv ℓ E O g ^ e.1.1 - 1
    2 ^ 2 * d a ^ 2 ∣ (ℓ ^ h : ↑O) ∧ ∀ z ∈ s23_m5 O ∅ ν e.1, (∀ j, ty j = e → z (φ j) = 0) →
               ∀ g, d a • (z + z) g = d g • (z + z) a
def s23_g7 (ψ : Gal(Ω/E) →* PadicAlgCl ℓ) c := IsAuxiliary S Q ∧ IsFromU1 (placesDividing E ℓ) Q
  ψ ∧ ∃ σ, s23_q3 0 ((↑) : Q → _) σ 1 ∧ ∑ k, ellVal (ψ (σ k) - 1) ≤ c
lemma s23_p7 (a : Gal(Ω/E₁)) : 2 ^ 2 ∣ (cycChar Ω ℓ a).1 - 1 := by
  obtain rfl | n := ‹ThePrime ℓ›.out.eq_two_or_odd'; exacts [(pow_dvd_cycChar_sub_iff 2).2 (cycCharMod_eq_of_dvd (by lia) (cycCharMod_eq_of_isPrimitiveRoot (StablyUnram.exists_primitive_root.choose_spec.map_of_injective (algebraMap E₁ _).injective) (by
    simp))), ((PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 (by simpa))).pow 2).dvd]
variable {e} {ν : ℕ} {w₁ : J → FinPlace E} {τ φ : J → Gal(Ω/E)} (hw : s23_q3 ν w₁ τ φ) {n : Type} [Fintype n]
lemma s23_q3.v7 {w : J → FinPlace E₁} {τ φ : J → Gal(Ω/E₁)} (hw : s23_q3 ν w τ φ) (O : CoeffRing ℓ) k : cycInv ℓ _ O (s23_q1 τ k) = 1 ∧ ∀ e, (ℓ ^ ν : ↑O) ∣ cycInv ℓ _ O (s23_q1 φ k) ^ e - 1 := ⟨by
  cases hk : k.2 <;> simp [idOrConjInv, cycInv, hk, cycChar_eq_one_of_mem_inertiaAbove (g := τ k.1) (by grind [inertiaAbove, hw k.1])], fun e ↦ by
  simpa using! map_dvd (algebraMap _ O) ((pow_dvd_cycChar_sub_iff (σ := (s23_q1 ..)⁻¹ ^ e) ν).2 (by
      cases hk : k.2 <;> simp_all [idOrConjInv, s23_q3, cycCharMod_prime_pow_eq]))⟩
lemma s23_q3.z4 {w : J → FinPlace E} {τ φ : J → Gal(Ω/E)} (hw : s23_q3 ν w τ φ) {n : Type} [Fintype n] {ρ : _ →* Matrix n n Λ} {c S T L} (k : c ∈ selmerModule ρ T L (QuotSpan (ℓ ^ e : Λ))) (h : ∀ k, c (s23_q1 τ k) = 0) (l : T ⊆ S ∪ .conjClosure (.range w) := by clear * -; intro; simp <;> grind) (hu : ∀ g ∈ inertiaAbove Sᶜ, cycChar Ω ℓ g = 1 → ρ g = 1 := by simp +contextual [tateTwist, cycInv]) : c ∈ selmerModule ρ S L _ := selmerModule_mono k .rfl fun v
  _ ↦ have ⟨j, o⟩ : ∃ j, v = w j ∨ v = star (w j) := by grind [star_star]
  ((exists_conj_side_detects nsmul_quot_eq_zero _ (hw j).2.2.choose_spec.2 (hw j).1 (by grind [inertiaAbove, cycChar_eq_one_of_mem_inertiaAbove, s23_q3]) o).choose_spec.choose_spec.2 c k (h (j, _))).1
variable (ℓ : ℕ) [ThePrime ℓ] {E ι G O O' n σ : Type} [Field E] [UnramCMField E] [CommRing O] [CommRing O'] [Fintype n] [Fintype σ] [Monoid G] {q : ℕ} [NeZero q] (h : σ → G →* Multiplicative (ZMod q)) (y : σ → O) (hy : ∀ j, y j ^ q = 1) (S S₀ J : Finset (FinPlace E)) (l M : ℕ)
@[grind] noncomputable def unionWithConj := S ∪ (J ∪ J.image star)
@[simps] def pointChar : G →* O := ⟨⟨fun g ↦ ∏ j, y j ^ (h j g).toAdd.val, by simp⟩, by
  simp [ZMod.val_add, ← pow_eq_pow_mod, *, pow_add]⟩
def twistAtPoint (e : O' →+* O) (ρ : G → Matrix n n _) g := (∏ j, y j ^ (h j g).toAdd.val) • (ρ g).map e
noncomputable def s23_z5 (ρ : G →* Matrix n n O) := (algebraMap O (QuotSpan (l ^ M : O))).mapMatrix.1.comp ρ
structure IsBalanced [PadicIntegerRing O ℓ] (ρ : Gal(Ω/E) →* Matrix n n O) (L γ β M) where
  isLocallyConstant : IsLocallyConstant (s23_z5 ℓ M ρ)
  unramified : ∀ g ∈ inertiaAbove Sᶜ, ρ g = 1
  span_eq_top : span O (.range ρ) = ⊤
  scalar_inertia : γ ∈ inertiaAbove (S \ placesDividing E ℓ) ∧
    ∃ s : O, (ρ (conjGal γ)⁻¹ = s • 1 ∧ ρ γ = s • 1) ∧ IsUnit (s + 1) ∧ IsUnit (s - 1)
  lt_card_residue : 4 * card n + 2 < .card (IsLocalRing.ResidueField O)
  coboundary_mem (a : O) (b : n → QuotSpan a) : (ρ · • b - b) ∈ obeying (O := O) L _
  local_length_le : ∃ g α α', (ρ g = α • 1 ∧ ρ (conjGal g)⁻¹ = α' • 1) ∧ ∀ a : O, a ∣ ℓ ^ M →
    ∑ v ∈ S, (⨅ A : {A // IsPlaceOver A v},
    length O (localCocycles ρ L A.1 (QuotSpan a))) + card n * addVal O (α - cycCharIn O Ω
    ℓ (conjGal g) * α') ≤ (S.card + numInfPlaces E) • length O (n → QuotSpan a) + β
structure IsPencil (U : ι → _ → Prop) (W : Set _) (N P₀ J) (x : _ →
  AuxPrimeData E (ℓ ^ N) × (ι → O)) where
  auxiliary : IsAuxiliary S₀ J
  helper_mem : P₀ ∈ J
  anticyclotomic : ∀ v ∈ J, IsAnticyclotomicAt (placesDividing E ℓ) v (x v).1
  char_frob : ∀ v ∈ J, v ≠ P₀ → ∀ w ∈ J, (x w).1.h (x v).1.φ = ite (w = P₀) (.ofAdd 1) 1
  helper_near : (x P₀).1.φ ∈ W
  frob_trivial : ∀ v ∈ J, ∀ i, (x v).2 i ≠ 0 → ∀ b, U i (idOrConjInv b (x v).1.φ)
def s23_v1 (x : FinPlace E → AuxPrimeData E q × (ι → O)) i := range fun p : J × _ ↦ (.single (idOrConjInv p.2 (x p.1).1.γ) 1 - .single (idOrConjInv p.2 (x p.1).1.φ) ((x p.1).2 i • 1) : _ →₀ Matrix n n O)
lemma s23_z6 {A : ClosurePlace} {P S τ} (hA : IsPlaceOver A P) (hτ : τ ∈ inertiaGroup Gal(Ω/E) A) (h : P ∈ S ∧ star P ∈ S) b : idOrConjInv b τ ∈ inertiaAbove S := b.rec ⟨_, h.2, _, hA.conjPlace_star, inv_mem hτ.conjPlace_conjGal⟩ ⟨P, by tauto⟩
attribute [local simp] Quotient.forall funext_iff mul_assoc
lemma s23_k3 {E n Λ : Type} [Field E] [EmbeddedNumberField E] [Fintype n] [CommRing Λ] (m : ℕ) [NeZero m] (ρ : Gal(Ω/E) → Matrix n n Λ) {W} (hW : W ∈ nhds 1) {S} (hS : S.Finite) L : ∃ (ι : Type) (_ : Fintype ι), ∃ γ R, (∀ v : ι → Λ, m • v ∈ R) ∧ ∀ (B : Type) [AddCommGroup B] [Module Λ B], (∀ b : B, m • b = 0) → (∀ g ∈ W, ∀ b : n → B, ρ g • b = b) → BijOn (↿· ∘ γ) (selmerModule ρ S L B).carrier {w | R ≤ (Fintype.linearCombination Λ w).ker} := (is_nonarchimedean _ hW).rec fun U hU ↦ by
  choose V hV using is_nonarchimedean _ ((selmerZ1.finite_unramified_cocycles (.funModule (.of (.trivial ℤ _ (ZMod m))) U) hS).eventually_all.2 fun z h ↦ (h.1.1.1 {_} (by simp)).mem_nhds rfl); use (_ ⧸ V.1) × n, .ofFinite _, .map (·.out) id, .span Λ (image2 (relEval _ · (Pi.single ⟨QuotientGroup.mk ·, ·⟩ 1)) (cocycleRels ρ ∪ (.single · 1) '' inertiaAbove Sᶜ ∪ L) univ ∪ range (m • ·)), (subset_span <| .inr ⟨·, rfl⟩), fun _ _ _ hm hρ ↦ ?_; simp [span_le, -relEval, -mem_union, ← comp_mem_obeying_iff, -nsmul_eq_mul, *]
  refine InvOn.bijOn ⟨?F, by simp [LeftInvOn, (↿·)]⟩ (fun _ H ↦ (?F H ▸ H.1 :))
    fun w ↦ (⟨·, .of_discrete w.curry⟩)
  exact fun c H ↦ funext₂ fun x i ↦ sub_eq_zero.1 (eq_zero_of_forall_hom_eq_zero ((bijective_ofZMod_comp hm).2.forall.2 fun χ ↦ by simpa using! congr(ofZMod m ($(hV (QuotientGroup.eq.1 (out_eq' ⟦x⟧).symm) (fun g ↦ Quotient.lift (fun a ↦ χ ((_ - c a⁻¹) i)) (by rintro _ _ ⟨u, rfl⟩; simp [Subgroup.smul_def, mem_selmerModule_iff.1 H, hρ _ (hU (inv_mem u.2))])) ⟨⟨continuous_pi (Quotient.ind ((H.2.comp (χ <| · i - _)).continuous.comp <| continuous_const_mul ·⁻¹)), by simp⟩, by simp_all [mem_selmerModule_iff.1 H]⟩) ⟦x⁻¹⟧))))
end
section
open AutChar AlgHeckeChar Complex Data Finset HeckeChar Matrix
variable {P} {D : Data P} {ℓ} [ThePrime ℓ]
lemma Data.Pair.j0 (p : D.Pair) (r : p.IsRamified) : ∃ F K m, F .one ≠ 0 ∧ (∀ ϑ : D.TameChar, ϑ.IsIntegralMeasure F) ∧ (∀ ϑ ϑ', ∀ v ∉ ϑ.Q, ϑ'.Q = insert v ϑ.Q → ϑ'.toAutChar = ϑ.toAutChar → ϑ'.ψ = ϑ.ψ → F ϑ' = F ϑ * ∏ k ∈ K, ∏ ε : ℤˣ, (1 - (p.ν * ϑ.toAutChar).baseChange.atUnif v ^ ε.1 / v.q ^ (p.z - @Fin.val 2 k))) ∧ ∀ ϑ : D.Twist, F ϑ = F .one * (ϑ.levelNorm ^ m * p.ratio ϑ ^ (m + 1)) := by
  have s ϑ : ∀ w ∉ (D.𝔪 ϑ 2).places, (p.ψ * ϑ.ψ) w = 1 := by simp_all [places_modulus_eq_union, p.6, ϑ.5]
  cases' p.z_mem.1.lt_or_eq' with hz hz
  · use p.intAlgPart ⟨card_fin _, hz⟩, {0}, 0, by simp, isIntegralMeasure_intAlgPart _, ?_, by grind [ratio_eq_intAlgPart_div, intAlgPart_ne_zero]
    introv _ _ _ _
    obtain ⟨⟨_, ⟨⟩⟩⟩ := p.intAlgPart_eq_mul_L ⟨card_fin _, hz⟩, ϑ'.6 v, @levelNorm_mem_and_notMem_of_mem_Q _ D ϑ' v, @levelNorm_mem_and_notMem_of_mem_Q _ D ϑ'
      (star v), (p.hasWeight.mul ϑ.hasWeight).atUnif_star (w := v)
    simp [mul_assoc, L, *]; convert (eulerProd_erase (p.hasWeight.mul ϑ.hasWeight).inv.isHeckeOfType.norm_heckeCoeff_le {v, star v}).2.2 p.z (mod_cast hz)
    · simp [funext_iff, heckeCoeff, Set.indicator]; grind [star_star]
    repeat simp_all [atUnif, heckeCoeff, cpow_neg, Ne.symm, places_modulus_eq_union, IsChosen] <;> grind
  let c := (p.c · - 1); have h ϑ := ((p.hasWeight.mul (TameChar.hasWeight ϑ)).mul_upsilonU1_pow 1).of_weight_eq (e' := (-c ·)) (by grind [le_c, add_zero]); obtain ⟨⟨N, _, J⟩, C, K⟩ := exists_modKernel_integral_bound (Fin 2) (Fin 2) D (univ.sum c * 2), stdClassSum_det_modKernel_eq _ even_two c; let Λ ϑ := detPeriod (Fin 2) (p.ν * ϑ.toAutChar * WeilData.upsilonU1 ^ 1) c (D.𝔪 ϑ 2) (p.ψ * ϑ.ψ); choose γ b e using (K <| isTameFor_of_hasWeight (c := 2) · (h _) r); have a ϑ : ‖_ * Λ _‖ = _ := congr(‖$(e ϑ 1)‖); simp [places_modulus_eq_union, inv_mul_cancel_comm] at a b
  refine ⟨(‖D.chosenGroupOrder * N * Λ ·‖ ^ 2), univ, 1, by simp [NeZero.ne]; grind [norm_zero], fun ϑ ↦ let g (x : StdClasses (Kf ..) × GL _ (D.𝔪 ϑ 2).ResRing) := x.1.out * (liftMod x.2).1
    .norm_sq _ ⟨_, inferInstance, (detFin 1 <| g ·), _, fun x ↦ mul_mem (div_mem_integralAway ((D.card_classAut_dvd_chosenGroupOrder (by simpa using D.nat_le_of_hasLogBound) le_rfl x.1.out).mul_right (_ ^ 0))) fun l _ k j ↦ congr(‖j (N * $(detKernel_embFin_mul (Pi.single 1 1) ..))‖).ge.trans (@(J _ _ _ (h .one) (h _) D.norm_mul_gProd_pow_mem_modulus (by simp [ite_mem]) _ _ _ (by simp [letterMinor, det_apply', prod_pow_eq_pow_sum, prod_smul, ← smul_sum, smul_pow, pow_mul, sq, mul_smul])).1 l _ ⟨j⟩ k (by simp) (exists_mul_mem_integralAbove l (g x) 1).choose_spec.1 ⟨∏ τ, det (of (.X ⟨τ, ·, ·⟩)) ^ c τ, by simp [letterMinor, det_apply]⟩), by
    rintro ⟨⟩ rfl; simp [Λ, ↓detPeriod_eq_stdClassSum_sum (s _), classSum, detKernel, mul_sum, modKernel_twist, Fintype.sum_prod_type, Rat.smul_def, division_def]; ac_rfl⟩, ?_, fun ϑ ↦ ?_⟩
  · introv _ _ _ c
    simp [Λ, ↓← mul_conj', ↓detPeriod_insert (c ▸ s ϑ) v, AutChar.frobValue, AutChar.spaceChar, IsChosen, *, ← ofReal_pow, prod_range, inv_eq_conj, places_modulus_eq_union, D.levelNorm_mem_and_notMem_of_mem_Q ϑ']; ring
  have := And.intro (p.lValueProd_eq 1 ϑ) (b 1); simp [ratio, lowerPoint, hz, twist_one_spec] at this ⊢; norm_cast at *; grind
lemma s23_q9 {I} (c : IsAuxiliary (badPlaces D ℓ) I) : ℓ.Coprime (∏ w ∈ I, w.q) ∧ (D.gProd * D.N).Coprime (∏ w ∈ I, w.q) := Nat.coprime_mul_iff_left.1
    (.symm (.prod_left fun w h ↦ (c w h).2.1.coprime_iff_not_dvd.2 ((c w h).1 <| by
    simpa [badPlaces] using w.1.mem_of_dvd ·.natCast w.1.absNorm_mem)))
@[simp] noncomputable def tameCharOfAuxiliary I (c : IsAuxiliary (badPlaces D ℓ) I) (χ : tameChars I) : D.TameChar := ⟨_, I, _, χ.2.1, χ.2.2, by grind, (s23_q9 c).2⟩
lemma q4 [PadicIso ℓ] {τ : D.TameChar} {x} {g : AbsGal D} (H : artinMap (AbsGal D) x = g) : τ.invAvatar g = ιℓ (τ.toAutChar.baseChange.finPart x)⁻¹ := ((exists_avatar.choose_spec _).2 x g H).trans
  (by simp [HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic])
lemma s23_k2 [PadicIso ℓ] {I} (hI : IsAuxiliary (badPlaces D ℓ) I) {ψ} (h : IsFromU1 (placesDividing _ ℓ) I ψ) : ∃ τ : D.TameChar, τ.Q = I ∧ ψ = τ.invAvatar := have ⟨_, φ, a, b, c⟩ := h
  (AutChar.exists_mem_tameChars (.comp ιℓ.symm (QuotientGroup.lift _ (φ.comp (.comp (Units.map (.snd ..)) Unitary.toUnits)) (sup_le (fun u h ↦ (exists_unitary_of_mem_rationalU1 h).elim fun y h ↦ congr(φ $(Units.ext (by simp [← h]))).trans (a (Unitary.toUnits y))) fun u ⟨h, k⟩ ↦ b _ (idelesUnitOff_mono bot_le (coe_idelesUnitOff_empty.ge ⟨h, star_mem_Ô h⟩)) (residue_eq_iff_valuation_sub_lt_one.1 <| k · ·.1))))).elim fun μ e ↦ ⟨tameCharOfAuxiliary _ hI μ⁻¹, rfl, MonoidHom.ext ((artinMap_surjective ..).elim fun x k ↦ q4 k ▸ c x · k ▸ congr(φ $(by bound)).trans (ιℓ.symm_apply_eq.1 ((inv_inv _).trans (e _)).symm))⟩
lemma s2 [PadicIso ℓ] {w} (hw : D.IsChosen w) (hℓ : w ∉ placesDividing _ ℓ) (p : D.Pair) s (hp : p.IsRamified) : ∃ ν val, IsFamily (T := Fin 2 × ℤˣ) (badPlaces D ℓ) ν val ∧ (∀ i, ellVal ((ν i w.isPlaceOver_placeOver.tameGenerator).1 - 1) ≤ @ellVal ℓ _ (w.q - 1)) ∧ ∀ τ : D.Twist, IsAuxiliary (badPlaces D ℓ) τ.Q → ∀ c : NNReal, ellVal (val τ.Q τ.invAvatar) ≤ c + ellVal (val ∅ 1) → ellVal (ιℓ (p.ratio τ s)) ≤ c := by
  obtain ⟨⟨_, U, h₀, o, hu⟩, F, K, m, n, H, law, hF⟩ := w.isPlaceOver_placeOver.exists_localArtin_eq_tameGenerator, p.j0 hp; set γ : (ResField w)ˣ := (LocInt w).unitGroupToResidueFieldUnits _; choose α _ u c hc b using (H <| tameCharOfAuxiliary · · 1⁻¹)
  choose y k using fun u ↦ (exists_divStar u).imp fun y k (τ : D.TameChar) ↦ show τ.toAutChar.1 u =
    (τ.toAutChar.baseChange.finPart y).1 by simpa [field] using! eq_of_mem_integralU1 τ.5 τ.4.2 _ (mem_integralU1_of_snd_eq_one _ k)
  let val I (χ : AbsGal D →* _) := ∑ᶠ h, ∑ a, ιℓ (c I h a) * χ ((artinMap _ (y (u I h a))).out ^ (-s.1))
  have key {I} h {τ} e : val I (TameChar.invAvatar τ) =
    ιℓ (F (tameCharOfAuxiliary I h (⟨(_, _), τ.4, e⟩ ^ s.1))) := by simp [val, h, b I, ↓k, q4 (Quotient.out_eq _).symm]
  have k : val ∅ 1 = ιℓ (F .one) := by simp [val, IsAuxiliary, b ∅ nofun, twist_one_spec]
  refine ⟨fun i ↦ ((p.hasWeight.zpow i.2).toAlgebraic 0 (-↑(p.z - i.1))).avatar, val, ⟨by fun_prop, fun I h ↦ ⟨_, _, _, _, by simpa using (hc I h · ℓ (s23_q9 h).1 (complexToCp ιℓ)), fun _ ↦ finsum_eq_single _ h nofun⟩, ?_, by simpa [k]⟩, fun (i, e) ↦ ?_, fun τ c _ ↦ ?_⟩
  · introv _ hI hχ hA _ hc
    obtain ⟨J, _⟩ : IsAuxiliary (badPlaces D ℓ) I ∧ ↑ℓ ∉ P.1 ∧ ¬D.IsChosen P ∧ ¬D.IsChosen
      (star P) ∧ star P ∉ I := by clear * - hI; grind [isChosen_iff, placesAboveG, placesDividing]
    obtain ⟨⟨τ, rfl, rfl⟩, φ, rfl⟩ := s23_k2 J hχ, inv_surjective φ
    grw [key hI, law (tameCharOfAuxiliary _ J (⟨(_, _), τ.4, τ.5⟩ ^ s.1)), ← prod_product', map_mul, map_prod, ellVal_mul_le, apply_prod_le_sum_apply _ _ (by simp [ellVal]) (@ellVal_mul_le _ _), sum_le_card_nsmul _ _ _ fun (k, ε) _ ↦ (hc (k, -ε) (s * ε)).trans_eq' (by
     simp (maxDischargeDepth := 5) [TameChar.invAvatar, avatar_frob _ hA, HasWeight.charUnramifiedAt_toAlgebraic, τ.5, p.6, *]; simp [atUnif, heckeCoeff, HasWeight.toAlgebraic, mul_zpow, _root_.zpow_mul, ↓← ofReal_zpow]; ring), card_le_univ] <;> norm_num +contextual [τ.5, add_le_add, mul_le_mul', *]
  · apply ellVal_le_ellVal; simp [hu, HasWeight.toAlgebraic, avatar_localArtin _ w.isPlaceOver_placeOver (.inl hℓ) h₀, p.6, hw.not_star, p.hasWeight.baseChange_finPart_locIdele (hw.not_star <| ·.substr hw)]
    refine .trans (by simp [card_ResField, Nat.card_units])
      (s23_z8 (x := ιℓ (p.ψ w γ) ^ _) ?_ (one_pow (.card (ResField w)ˣ)) ?_) <;> fin_cases e <;> simp [← map_pow, ← γ.val_pow_eq_pow_val, ιℓ.map_eq_one_iff, by simpa [MulChar.eq_iff o] using (hp w).2 hw]
  rw [ellVal_le_add_iff (k ▸ (H _).norm_apply_one_le _), key c τ.1.5, hF ⟨_, by fin_cases s <;> simpa using τ.2⟩]; simp [k, (s23_q9 c).1.norm_natCast_eq_one, -Nat.cast_prod]; field_simp [n]; simpa [← norm_pow, ← ellVal_le_iff, add_mul, Pair.ratio, -map_div₀] using le_of_add_le_right
end
seal Finset.univ Finset.sum Finset.prod
open Matrix Polynomial Fintype Fact IsAlgClosed Fint NumberField
open Multiset hiding card
section
variable {ℓ} [hp : ThePrime ℓ] {P} {D : Data P} {r n} [Fintype r] [Fintype n]
attribute [local simp] Algebra.smul_def Units.ext_iff NeZero.pos eval_multiset_prod Data.TameChar.invAvatar
private lemma t4 {x : PadicAlgCl ℓ} (h : IsOfFinOrder x) a b (H : ∀ u, (x ^ a) ^ ℓ ^ u ≠ (x ^ b) ^ ℓ ^ u) : ‖x ^ a - x ^ b‖ = 1 := by choose u k c e using WfDvdMonoid.max_power_factor h.orderOf_pos.ne' hp.out; let z : intQpBar ℓ := ⟨x, h.norm_eq_one.le⟩; refine (z ^ a - z ^ b).2.antisymm ((not_lt.1 ((valuation_natCast_eq_one c).not_lt ∘ valuation_intQpBar_lt_one_iff.2)).trans ((s23_z8 ?_ ?_ (H u)).trans ((Valuation.integer.integers _).le_of_dvd (sub_dvd_pow_sub_pow (z ^ a) (z ^ b) _)))) <;> rw [← pow_mul, ← e, pow_right_comm] <;> simp
variable [PadicIso ℓ] {O : AuxPair D.E r n} {ϑ c} (m) [Fintype m]
lemma s23_v6 (hc : IsApt O c ϑ) {l} {v : FinPlace _} (hv : ↑(D.g l) ∈ v.1) {A : ClosurePlace} (hA : IsPlaceOver A v) t : ∃ γ, (D.IsChosen v → γ = hA.tameGenerator) ∧ ∀ s ∈ inertiaGroup _ A, ∃ μ, Multiset.card μ = card r + t ∧ (∀ y ∈ μ, (t = 0 → s = ↑γ → y ≠ 1) ∧ y ^ (D.g l ^ (card r).factorial - 1) = 1 ∧ ∃ d ∈ Set.Icc 1 D.r, y ^ (D.g l ^ d - 1) = 1) ∧ ∀ {R k J S}, IsLabelledColumn (m := m) O k J (twistedLabel O c · * (X - 1) ^ t) S R → let P := (μ.map (X - C ·)).prod; PolyKillsAt R A s P ∧ PolyKillsAt R (conjPlace A) (conjGal s⁻¹) P := by
  wlog h : D.IsChosen v generalizing v A
  exact (this (by simpa) hA.conjPlace_star ((D.isChosen_star_iff hv).2 h)).elim fun γ w ↦ ⟨⟨_, conjPlace_conjPlace ▸ γ⁻¹.2.conjPlace_conjGal⟩, h.elim, fun s u ↦ (w.2 _ (inv_mem u).conjPlace_conjGal).imp (by simp +contextual; grind)⟩; obtain ⟨i, rfl⟩ : ∃ i, O.chosenPlace i = v := hc.1 ▸ D.range_chosen.ge h; have l : IsLabel _ (twistedLabel ..) := (hc.isLabel i).scaleRoots _
  refine ⟨_, by tauto, fun s u ↦ ((exists_isTameExponent _ hA _).2 s u).elim fun y ⟨H, F⟩ ↦ ⟨_, by
    simp [l.2, card_aroots_eq_natDegree, l.1.natDegree_mul', ← C_1, -map_one, X_ne_C], forall_mem_map_iff.2 fun x hx ↦ ?_, fun N ↦ (fun k ↦ ⟨k, ((conjPlace_conjPlace ▸ s23_v4 N.1.1) (N.local_conditions _ (by grind
    [placesAboveG]) hA).1).2.2 s u _ k⟩) ((congrArg prod (map_map ..)).substr (N.labelled H))⟩⟩
  obtain ⟨-, p | ⟨rfl, z⟩⟩ := by simpa using hx
  refine ⟨fun _ e u ↦ hc.isLabel_twistedLabel i (by simp_all [aeval_def, (pow_eq_one_iff_of_coprime (F e)).1 ⟨IsFaithfulMulChar.injective (by cases y <;> simp_all [ιℓ.map_eq_one_iff, MulChar.pow_apply', ← map_pow]), (l.root_pow_eq_one p).1⟩]), (l.root_pow_eq_one p).imp ?_ (.imp fun d ↦ .imp (by grind [IsApt]) ?_)⟩ <;> simp_all [D.q_eq_g hv, ← map_pow]; simpa [z] using ⟨1, .refl, D.nat_le_of_hasLogBound⟩
lemma IsLabelledColumn.isRow (hc : IsApt O c ϑ) {R k J} (h : IsLabelledColumn (m := r) O k J (twistedLabel O c) ∅ R)
  (hJ : IsRowType D (card r) k J) : IsRow D k J R := (D.g_injective.exists_ne ℓ).elim fun l hl ↦ by
  choose i L g using hc.exists_primitive l
  obtain ⟨⟨_, n, p, d⟩, ⟨A, B, -⟩, ⟨G, v, S⟩, hA, hℓ, j, ⟨J, hj⟩, b⟩ := (by grind [Parameters, Nat.prime_two, Nat.prime_five] : ∃ p ≠ ℓ, p.Prime ∧ p ∣ P.N₀ * P.d), (D.range_chosen.ge (s23_q2 hc.1 i).1).choose_spec ▸ D.dvd_card_resField_sub_one _, s23_q2 hc.1 i, (O.chosenPlace i).isPlaceOver_placeOver, hl ∘ (FinPlace.charP_quotient _ L).eq _ ∘ FinPlace.charP_quotient _, hc.tame_part_eq
  obtain ⟨⟨e, y, E, Y⟩ : ∃ e y, (∀ ξ, (twistedLabel O c i).aeval ξ = 0 → ξ ^ e = y ∧ ξ ^ (O.chosenPlace i).q ^ card r = ξ ∧ ∀ u, (Set.Iio (card r)).InjOn fun a ↦ (ξ ^ (O.chosenPlace i).q ^ a) ^ ℓ ^ u) ∧ ∀ x, y ^ x = 1 → _ ∣ j * x, F, hv, ⟨s, H⟩, φ, hφ⟩ := g.elim (fun ⟨R, h⟩ ↦ have z@⟨L, I, y, h⟩ := h.scaleRoots _ (charName_pow_eq_one (by simp [b ▸ D.omega_zpow_mul_pow_eq_one j v])) B; z.isPrimitiveRoot_prod_roots.2.imp fun _ N ↦ ⟨_, fun x o ↦ ⟨N x (mem_aroots.2 ⟨I.ne_zero, o⟩), by rw [← card_ResField, root_pow_card_pow_eq_self_iff I o, L.2.2.1], fun a _ _ _ _ _ ↦ by
    apply frobenius_conj_pow_injOn a A (R.trans D.r_pow.choose_spec ▸ h.2) hp.out <;> grind
      [card_ResField, pow_right_comm, exists_pow_card_pow_eq_of_root I o]⟩, (z.isPrimitiveRoot_prod_roots.1.2 · · |> B.trans |> dvd_of_mul_left_dvd |>.mul_left _)⟩)
    (fun _ ↦ ⟨1, by simp [MulEquiv.map_eq_one_iff, *, twistedLabel, ← card_ResField, ← map_pow, ← C_1, -map_one, FiniteField.pow_card, pow_mul, ← D.orderOf_ω G, orderOf_dvd_iff_pow_eq_one, ← Units.val_pow_eq_pow_val]⟩), (h.local_conditions _ nofun hA).1, hA.valuation_natCast_eq_one_iff.2 hℓ, (exists_isTameExponent _ hA _).1.imp fun _ t ↦ h.labelled t, hA.exists_isFrob (AbsGal D)
  obtain ⟨ζ, z⟩ := IsAlgClosed.exists_root (R s).1.charpoly (by simp; grind)
  obtain ⟨ξ, ⟨-, hξ⟩, rfl⟩ := by simpa using isRoot_of_isRoot_charpoly (H.1 hv) z
  have o := ((hc.isLabel i).scaleRoots _).root_pow_eq_one hξ
  simp_rw [Set.InjOn, ← IsFaithfulMulChar.injective.eq_iff, ← ιℓ.injective.eq_iff, map_pow, map_one] at *; obtain ⟨o, T⟩ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, by simp, o.1⟩, F.aeval_eq_zero_of_roots hv s.2 H
  refine ⟨h.1, hJ, ?r, (?r _ ⟨S, hℓ⟩ hA).elim fun _ ⟨M, _, v, w, _⟩ ↦ (CoeffRing.eventually_mem o.norm_eq_one.le).mono fun _ h _ a ↦ (a.span_eq_top_of_tame_pair (ζ := ⟨_, h⟩) ((hA.tame_inertia R (F.1 hv) v (by simpa using w) s).2 _ _ hφ).symm (fun _ p _ q n ↦ t4 o _ _ (n ∘ (E ξ hξ).2.2 · p q)) z (by simpa +contextual [E] using (T (X ^ (O.chosenPlace i).q ^ card r - X) :))).imp_right (.rec (⟨_, l, ·, by simp [hφ.cycChar_eq ℓ hv, D.q_eq_g L], ·⟩)), _, ⟨_, ⟨S, hℓ⟩, _, hA, (s ^ e).2⟩, _, by simpa +contextual [E] using (T (X ^ e - C (ιℓ (faithfulChar _ y))) :), fun a t U ↦ by simpa [pow_mul, *] using t4 o (e * _ * t) 0 fun c f ↦ (Nat.le_of_dvd (mul_pos J U.1) ((Nat.coprime_pow_primes _ (a + c) p out n).dvd_mul_right.1 (by grw [d, mul_assoc, ← Y _ (by simpa [pow_mul, pow_add, pow_right_comm, *] using f), Parameters.Mω, ← le_self_add]))).not_gt (by grw [hj, U.2, hc.rank_le.1, ← p.two_le]; use D.nat_lt_of_hasLogBound)⟩
  rintro w ⟨⟨i, b⟩, v⟩ A a
  choose s t _ _ d H using s23_v6 r hc b a 0; simp at d H
  refine ⟨s, _, t, ?_, fun t c ↦ by simpa +contextual [d t c] using ((h.local_conditions _ nofun a).1.aeval_eq_zero_of_roots (a.valuation_natCast_eq_one_iff.2 v) c (H t c h).1 (X ^ (D.g i ^ (card r).factorial - 1) - 1) :), fun b ↦ ?_⟩
  simp [↓a.valuation_natCast_eq_one_iff, ← algebraMap_ResField_eq_zero, ← D.q_eq_g b, ← card_ResField]
  grw [(by simpa using (det_aeval_neg_eq_prod_roots (R (idOrConjInv b s)).1 (-X - 1) :) :), apply_prod_le_sum_map _ _ (by simp [ellVal]) (@ellVal_mul_le _ _), sum_map_le_sum_map ellVal (fun _ ↦ crudeUnit ℓ D) (forall_mem_map_iff.2 fun x u ↦ ?_)]
  simp [card_roots_eq_natDegree]
  choose b _ j u e using d s s.2 x (by simpa using ((isRoot_of_isRoot_charpoly · (isRoot_of_mem_roots u)) (b.rec (·.2.1 (by simpa [a.conjPlace_star.valuation_natCast_eq_one_iff])) (·.1.1 (a.valuation_natCast_eq_one_iff.2 v)) (H s s.2 h))))
  grw [← ellVal_le_crudeUnit D ℓ i (u.imp_right D.nat_le_of_hasLogBound.trans'), ellVal_le_ellVal]
  simpa using s23_z8 e (one_pow _) (b rfl)
lemma normalisedRep_quadratic_on_inertia [Nonempty n] (hc : IsApt O c ϑ) (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) {f : (stdSpace _ n).forms (O.κ, O.detExp)} {H R} (he : IsEigenform f.1 H) (h : Attached H R) (p : ∀ i, HasParahoricType f.1 (O.apart.2 _ (.inr i)) (ρ := Empty) .ofIsEmpty (if · ∈ Set.range O.incl then 2 else 1) 1 ![1, (O.ψ _)⁻¹] fun _ ↦ f) : ∀ g ∈ inertiaAbove (.conjClosure ϑ.Q), ((normalisedRep O R g).1 - ϑ.invAvatar g • 1) * ((normalisedRep O R g).1 - 1) = 0 := by
  rintro s ⟨w, hv, A, hA, hs⟩; have : ↑ℓ ∉ w.1 := by grind [placesDividing]
  suffices IsFiniteTypeAt R A ∧ PolyKillsAt R A s ((X - C (ϑ.invAvatar s)) * (X - 1)) by
    simp_all [Units.smul_def, chiOneInv_spec hA _ 0 (inv_mem hs), PolyKillsAt, hA.valuation_natCast_eq_one_iff]
  wlog hw : w ∈ ϑ.Q generalizing w A s
  refine (this (conjGal s⁻¹) _ ?_ _ hA.conjPlace_star ?_ ?_ ?_).elim fun a q ↦ cast ?_ ((s23_v4 (s23_v5 he h) a).imp_right (·.2 _ ?_ _ q)) <;> simp_all [eq_inv_of_mul_eq_one_left (g6 _ 0 0 s)]; obtain ⟨⟨i, rfl⟩ : ∃ i, O.twistPlace i = w, y, G, -⟩ := hc.1 ▸ ⟨⟨_, hw⟩, rfl⟩, (exists_isTameExponent (faithfulChar (ResField w)) hA _).2 s hs; have := f7 ϑ.hasWeight.inv 0 0 (by simp_all [ϑ.1.5, ϑ.1.6]) (by grind) G; refine (h.isLabelledAt f.2 he (HasParahoricType.hasProductLabel (χ := ![1, _⁻¹]) (σ := 1) (c := 1) 1 (by tauto) ?_ (by simpa [congrFun hc.tame_part_eq.choose_spec.2 _, D.omega_eq_one_of_not_isChosen (D.levelNorm_mem_and_notMem_of_mem_Q _ ‹_›).2.1] using! p i) ?_ ?_) hA).elim fun F b ↦ ⟨F, (F.aeval_eq_zero_of_roots · hs (b.2 G).1 _ ?_), absurd ?_ (‹PadicPlaceEmbedding ..›.inducesPlace.1.1 ▸ valuation_comap_intQpBar_lt_one _).ne⟩ <;> open Calc in simp_all [or_imp, hA.valuation_natCast_eq_one_iff, PolyKillsAt, he.1, algebraMap_eq_diagonal, funext_iff, labelIdem, IsLabel, asAlgebraHom_eq_sum, Hall.evalGL, ϑ.psi_ne_one]
end
variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {P} {D : Data P} {r n m : Type} [Fintype r] [Fintype n] [Fintype m] {O : AuxPair D.E r n} {ϑ} {c : ∀ _, _} {R : GalRep ℓ D.E m} {k S} {A : ClosurePlace}
attribute [local simp] Units.smul_def Units.ext_iff cycInv
lemma IsLabelledColumn.twist_avatar {J a e ψ b} (h : IsLabelledColumn O k J c S R) (hμ : AutChar.HasWeight a e ψ) (k' j : ℤ) (hb : (b - 1 : ℕ) + (2 * j - k') = (k - 1 :)) {d} (hc : IsApt O d ϑ) (hH : ∀ v, ¬D.IsChosen v → ψ v = 1) : IsLabelledColumn O b (fun σ ↦ (J σ).map (· + -(hμ.toAlgebraic k' j).1.2.toAdd σ)) (fun i ↦ (c i).scaleRoots (charName (faithfulChar (ResField (O.chosenPlace i))) (ψ _)).1) S (twistByChar (hμ.toAlgebraic k' j).avatar R) := by
  choose x u z w using fun {A μ} ↦ local_clauses_twist A (r' := twistByChar μ R) (by tauto)
  use ⟨⟨.of_coeHom_comp (.smul (by fun_prop) (.comp (by fun_prop) h.continuous)), h.nondeg.twist _, by simp [eq_sub_of_add_eq' hb, h.trace_conj, zpow_sub₀, field, eq_mul_inv_of_mul_eq (g6 ..)]⟩, fun v hv A a ↦ (h.local_conditions v hv a).imp (x · (avatarCompatAt_of_stablyUnram _ a).1) (.imp (z · (avatarCompatAt_of_stablyUnram _ a).2.1) fun f n ↦ u (f n) ((avatarCompatAt_of_stablyUnram _).sphericalClause_of_unramified (by simp_all
    [hμ.charUnramifiedAt_toAlgebraic, placesAboveG, D.isChosen_iff.not]) a).1)⟩, fun i A s y hy ↦ w ((h.labelled hy).of_dvd ?_) (by simpa using f7 hμ _ _ (hH _ (s23_q2 hc.1 i).1.not_star) (O.isConjApart_chosenPlace.2 i i) hy)
  by_cases c i = 0 <;> simp_all [aroots, map_scaleRoots, roots_scaleRoots, multiset_prod_comp, Multiset.prod_dvd_prod_of_dvd, dvd_iff_isRoot]
lemma isLabelledColumn_of_hasProductLabel {d} (hc : IsApt O d ϑ) {κ f s H} (hf : f ∈ (stdSpace _ m).forms κ) (he : IsEigenform f H) (hR : Attached H R) (hK : ∀ v ∉ S \ (placesDividing _ ℓ ∪ placesAboveG D), v ∉ (Set.range O.chosenPlace).conjClosure → f ∈ sphericalAt (rightRegular ℂ ..) v) {t : Fin s → ℕ} (h : ∀ i, HasProductLabel f (O.isConjApart_chosenPlace.2 i i) (faithfulChar (ResField (O.chosenPlace i))) (card r) (c i) 1 t) [Nonempty m] : IsLabelledColumn O (card m) (jumps κ (card m)) (c · * (X - 1) ^ (card m - card r)) S R := have L i := (hR.isLabelledAt (A := ·) hf he (h i))
  ⟨⟨s23_v5 he hR, fun v k A hA ↦ by grind [(sphericalCompat_std v hf he).2 hR, s23_v4 (s23_v5 he hR), !s23_q2 hc.1, hA.conjPlace_star, isGoodAt_iff]⟩, fun i A _ _ H ↦ by simpa [Finset.prod_pow_eq_pow_sum, ← (h i).2.2.1] using ((L i A H.1).2.2 H).1⟩
