import Lib.Adelic.Adeles.CoprimeValuation
import Lib.General.Analysis.OstrowskiTaussky
noncomputable section
open Nat Set Fact IsIntegralClosure IsLocalRing NumberField RestrictedProduct Valued WithZero WithZeroTopology IsDedekindDomain.HeightOneSpectrum integer StarSubsemiring Ideal
variable {E : Type*} [Field E] [NumberField E]
section
variable (w : FinPlace E) (x : 𝔸f E) {a : 𝓞 E}
lemma residue_eq_iff_valuation_sub_lt_one {F Γ} [Field F] [LinearOrderedCommGroupWithZero Γ] {v : Valuation F Γ} {a b : v.valuationSubring} : residue _ a = residue _ b ↔ v (a - b) < 1 := Ideal.Quotient.eq.trans v.mem_maximalIdeal_iff
@[simp] lemma algebraMap_ResField_eq_zero {w x} : algebraMap (𝓞 E) (ResField w) x = 0 ↔ x ∈ w.1 := residue_eq_iff_valuation_sub_lt_one.trans (by simp [valuation_lt_one_iff_mem])
lemma isOpen_v_lt γ : IsOpen {x : LocField w | v x < γ} := isOpen_lt continuous_v (by fun_prop)
private lemma approx (x : LocInt w) n : ∃ a : 𝓞 E, v (algebraMap E _ a - x.1) < exp n := by have ⟨y, hy, h⟩ := (w.denseRange_algebraMap E).exists_mem_open (((isOpen_v_lt w (exp n)).preimage (continuous_sub_right ↑x)).inter (isOpen_integer _)) ⟨x, by aesop⟩; peel w.exists_valuation_sub_lt_of_integer ((v_algebraMap_eq_valuation _).ge.trans h) (expEquiv _); simpa using v.map_add_lt ((v_algebraMap_eq_valuation _).substr this) hy
lemma algebraMap_ResField_surjective : (⇑(algebraMap (𝓞 E) (ResField w))).Surjective := Quot.ind (approx w · 0 |>.imp fun _ ↦ residue_eq_iff_valuation_sub_lt_one.2)
lemma card_ResField : .card (ResField w) = w.q := card_congr (RingHom.quotientKerEquivOfSurjective (algebraMap_ResField_surjective w)).1 ▸ by rcongr; simp
instance instFiniteResField : Finite (ResField w) := finite_of_card_ne_zero (by simp [card_ResField])
instance : ProperSpace (LocField w) := properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2 ⟨inferInstance, v.valuationSubring_isDiscreteValuationRing, instFiniteResField w⟩
instance compactSpace_LocInt : CompactSpace (LocInt w) := properSpace_iff_compactSpace_integer.1 inferInstance
lemma isCompact_LocInt : IsCompact (LocInt w : Set (LocField w)) := isCompact_iff_compactSpace.2 (compactSpace_LocInt w)
instance : CharZero (LocField w) := algebraRat.charZero _
deriving instance PolishSpace for LocField
instance (priority := low) : Countable E := (integralBasis E).1.injective.countable
instance : Countable (FinPlace E) := .of_preimage_singleton (Ideal.finite_setOfPred_absNorm_eq · |>.countable.preimage asIdeal_injective)
instance : Fact (∀ w : FinPlace E, IsOpen (LocInt w).carrier) := ⟨(isOpen_integer <| LocField ·)⟩
deriving instance T0Space, LocallyCompactSpace for 𝔸f E
lemma isCompact_Ô : IsCompact (Ô E : Set (𝔸f E)) := (Set.ext fun _ ↦ mem_Ô).substr ((range_structureMap ..).subst (isCompact_range (X := ∀ w, LocInt w) isEmbedding_structureMap.continuous))
lemma isOpen_Ô : IsOpen (Ô E : Set (𝔸f E)) := (Set.ext fun _ ↦ mem_Ô).substr (isOpen_forall_mem out)
@[fun_prop] lemma continuous_evalAt : Continuous (evalAt w) := continuous_eval w
@[fun_prop] lemma continuous_singleAdele : Continuous (singleAdele w) := by exact (continuous_dom.1 (@continuous_id (𝔸f E) _) {w}ᶜ (by simp)).comp (f := (⟨singleAdele w ·, by aesop⟩)) (continuous_rng_of_principal.2 (continuous_single w))
@[simp] lemma algebraMap_mem_Ô {x : E} : ↑x ∈ Ô E ↔ IsIntegral ℤ x := by simpa [mem_Ô] using ⟨isIntegral_iff.2 ∘ mem_integers_of_valuation_le_one E x, fun h w ↦ w.valuation_le_one ⟨x, h⟩⟩
lemma coe_mem_Ô (a : 𝓞 E) : ↑a ∈ Ô E := by simpa using! a.2
lemma isUnit_natCast_finAdele {d : ℕ} (hd : d ≠ 0) : IsUnit (d : 𝔸f E) := mod_cast (cast_ne_zero.2 hd).isUnit.map (algebraMap E _)
lemma exists_natCast_smul_mem_of_isCompact E [Field E] [NumberField E] {M} [AddCommMonoid M] [Module (𝔸f E) M] [TopologicalSpace M] [ContinuousSMul (𝔸f E) M] {K U} (hK : @IsCompact M _ K) (hU : U ∈ nhds 0) : ∃ N ≠ 0, ∀ x ∈ K, (N.cast : 𝔸f E) • x ∈ U := by simpa [one_le_iff_ne_zero] using! ((@mapClusterPt_zero_atTop_nsmul (Ô E) _ _ isCompact_Ô.compactSpace _ 1).frequently (hK.eventually_forall_mem (· • ·) _ (by aesop))).forall_exists_of_atTop 1
lemma mem_nhds_zero_finAdele_iff {U} : U ∈ nhds 0 ↔ ∃ N ≠ 0, ∀ x ∈ Ô E, N.cast * x ∈ U := ⟨exists_natCast_smul_mem_of_isCompact E isCompact_Ô, fun ⟨_, n, _⟩ ↦ mem_nhds_iff.2 ⟨_, by simpa, (isUnit_natCast_finAdele (E := E) n).isOpenMap_smul _ isOpen_Ô, by aesop⟩⟩
lemma exists_forall_mul_mem_Ô {ι} [Finite ι] (x : ι → _) : ∃ N ≠ 0, ∀ i, N.cast * x i ∈ Ô E := by simpa using exists_natCast_smul_mem_of_isCompact E (finite_range x).isCompact (isOpen_Ô.mem_nhds (by simp))
@[simp] lemma finAdele_mul_apply y w : (x * y) w = x w * y w := rfl
lemma exists_eq_mul_iff_v_le {x c} : (∃ y ∈ Ô E, x = c * y) ↔ ∀ w, v (x w) ≤ v (c w) := ⟨by simp_all [mul_le_of_le_one_right, mem_Ô], fun h ↦ by choose a e using (v.isEquiv_valuation_valuationSubring .. |>.1 <| h ·); use structureMap _ _ _ a, mem_Ô.2 (a · |>.2), RestrictedProduct.ext _ _ (e · ▸ mul_comm ..)⟩
instance : Algebra (𝓞 E) (Ô E) := ((algebraMap ..).codRestrict _ coe_mem_Ô).toAlgebra
@[simp] lemma coe_algebraMap_Ô x : (algebraMap (𝓞 E) (Ô E) x).1 = x := rfl
lemma exists_dvd_sub_algebraMap (h : a ≠ 0) x : ∃ b, algebraMap _ (Ô E) a ∣ algebraMap (𝓞 E) _ b - x := by
  choose c A using (approx _ ⟨_, mem_Ô.1 x.2 ·⟩ _)
  peel IsDedekindDomain.exists_forall_sub_mem_ideal (s := (Ideal.finite_factors (I := .span {a}) (by simpa)).toFinset) asIdeal _ (by simp [prime]) (by grind +extAll) (c ·)
  simpa [dvd_def, Subtype.ext_iff, exists_eq_mul_iff_v_le, intValuation_eq_exp_neg_multiplicity, h, valuation_of_algebraMap] using! fun w ↦ v.map_add_le (A w).le ((v_algebraMap_eq_intValuation (_ - _)).substr ((intValuation_le_pow_iff_mem ..).2 (by_cases (this w) (by simp_all [multiplicity_eq_zero_of_not_dvd]))))
lemma dense_Ô : DenseRange (algebraMap (𝓞 E) (Ô E)) := fun x ↦ by simpa [↓closure_subtype, mem_closure_iff_nhds_zero, mem_nhds_zero_finAdele_iff] using fun U N h ↦ (exists_dvd_sub_algebraMap N.cast_add_one_ne_zero x).imp (by simp_all [dvd_def, Subtype.ext_iff])
lemma denseRange_algebraMap_finAdele : DenseRange ((↑) : E → 𝔸f E) := (exists_forall_mul_mem_Ô ![·] |>.rec fun N n ↦ ((Algebra.linearMap ..).range.closure.smul_mem_iff (S := E) (cast_ne_zero.2 n.1)).1 (closure_mono (by simp) (Subtype.dense_iff.1 dense_Ô (mod_cast by aesop))))
lemma exists_sub_mem_Ô : ∃ a : E, x - a ∈ Ô E := denseRange_algebraMap_finAdele.exists_mem_open (isOpen_Ô.preimage (by fun_prop)) ⟨x, by simp⟩
attribute [local instance] IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace IsTopologicalAddGroup.rightUniformSpace isUniformAddGroup_of_addCommGroup
variable [IsCMField E] (x : E)
instance : PolishSpace (𝔸f E) := have := (@denseRange_algebraMap_finAdele E _ _).separableSpace'; have := @IsUniformAddGroup.uniformity_countably_generated (𝔸f E) _ _ _ ((nhds_zero_eq_map_structureMap _ out).substr (Filter.map.isCountablyGenerated ..)); {}
instance : StarRing (𝔸f E) := starRingOfInvolution (adeleMap (starRingEnd E)) denseRange_algebraMap_finAdele.eq
@[simp] lemma finAdele_star_apply (x : 𝔸f E) : star x w = conjLoc (star_star w) (x (star w)) := rfl
instance : ContinuousStar (𝔸f E) := ⟨continuous_adeleMap _⟩
@[simp] lemma star_algebraMap_finAdele : star (x : 𝔸f E) = star x := adeleMap_algebraMap ..
@[simp] lemma star_toAdele [PlaceEmbedding E] : star (toAdele x) = star x := by aesop
lemma star_mem_Ô {x} (h : x ∈ Ô E) : star x ∈ Ô E := by simp_all [mem_Ô]
end
variable (S : Set (FinPlace E)) (x y : 𝔸f E) (w : FinPlace E)
@[simp] lemma finAdele_add_apply : (x + y) w = x w + y w := rfl
@[simp] lemma finAdele_sub_apply : (x - y) w = x w - y w := rfl
@[simp] lemma finAdele_neg_apply : (-x) w = -x w := rfl
@[simp] lemma finAdele_one_apply : (1 : 𝔸f E) w = 1 := rfl
@[simp] lemma finAdele_pow_apply k : (x ^ k) w = x w ^ k := rfl
@[simp] lemma finAdele_natCast_apply (k : ℕ) : (k : 𝔸f E) w = k := rfl
@[simp] lemma finAdele_zero_apply : (0 : 𝔸f E) w = 0 := rfl
lemma v_inv (x : (𝔸f E)ˣ) : x⁻¹.1 w = (x.1 w)⁻¹ ∧ x.1 w ≠ 0 := by simp [← evalAt_apply, x.isUnit.map _ |>.ne_zero]
def idem : 𝔸f E := ⟨(if · ∈ S then 1 else 0), by simp [ite_mem]⟩
@[simp] lemma reduceAt_algebraMap x : reduceAt w (algebraMap (𝓞 E) _ x) = algebraMap _ _ x := rfl
@[local simp] lemma idem_apply : idem S w = ite (w ∈ S) 1 0 := rfl
@[simp] lemma idem_mem_Ô : idem S ∈ Ô E := by aesop_cat
@[simp] lemma reduceAt_idem : reduceAt w ⟨_, idem_mem_Ô S⟩ = ite (w ∈ S) 1 0 := by split <;> congrm ⟦⟨$(by simpa), _⟩⟧
lemma idem_mul_self : idem S * idem S = idem S := by aesop
lemma idem_compl : idem Sᶜ = 1 - idem S := by aesop
lemma exists_idele_eq_uniformizer_zpow (d : _ → ℤ) (hd : d.HasFiniteSupport) : ∃ x : (𝔸f E)ˣ, ∀ w, x.1 w = ↑((uniformizer w)⁻¹ ^ d w) := ⟨mkUnit _ (hd.subset (by aesop_cat)), fun _ ↦ rfl⟩
variable {S x w}
@[simp] lemma idem_of_mem : w ∈ S → idem S w = 1 := (ite_eq_left ·)
@[simp] lemma idem_of_notMem : w ∉ S → idem S w = 0 := (ite_eq_right ·)
lemma idem_mul_mem_Ô : idem S * x ∈ Ô E ↔ ∀ w ∈ S, v (x w) ≤ 1 := by simp [Ô, ite_mem]; rfl
@[simp] lemma reduceAt_eq_zero {x} : reduceAt w x = 0 ↔ v (x.1 w) < 1 := sub_zero (x.1 w) ▸ residue_eq_iff_valuation_sub_lt_one
@[simp] lemma isUnit_Ô {x : Ô E} : IsUnit x ↔ ∀ w, v (x.1 w) = 1 := by simp [isUnit_iff_dvd_one, dvd_def, Subtype.ext_iff, exists_eq_mul_iff_v_le, le_antisymm_iff, mem_Ô.1]
variable [IsCMField E] (x : 𝔸f E) (w : FinPlace E)
instance : StarRing (Ô E) := starRing ⟨_, star_mem_Ô⟩
@[simp, norm_cast] lemma coe_star_Ô x : (star x : Ô E) = star x.1 := rfl
@[simp] lemma v_star_apply : v (star x w) = v (x (star w)) := by simp
@[simp] lemma q_star : (star w).q = w.q := Nat.card_congr (quotientEquiv _ _ _ (comap_symm starRingAut)).1.symm
lemma star_idem S : star (idem S : 𝔸f E) = idem (star ⁻¹' S) := by aesop
lemma star_singleAdele {u w : FinPlace E} h x : star (singleAdele u x) = singleAdele w (conjLoc h x) := by cases h ▸ star_star u; ext v; by_cases v = w <;> aesop
