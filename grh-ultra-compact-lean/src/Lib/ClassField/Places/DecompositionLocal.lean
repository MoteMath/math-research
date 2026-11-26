import Lib.ClassField.Places.FrobeniusOnRoots
open Valued Valuation MulSemiringAction Classical Fact
class EmbeddedNumberField K [Field K] extends NumberField K, Algebra K Ω
instance {K} [Field K] [NumberField K] [Algebra K Ω] : EmbeddedNumberField K where
variable {K} [Field K] [EmbeddedNumberField K] (v : FinPlace K) (p) [f : Fact (Nat.Prime p)] (Γ) [Group Γ] [TopologicalSpace Γ] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] (A : ClosurePlace) [a : Algebra (LocField v) (PadicAlgCl p)] (j : Ω →+* PadicAlgCl p)
structure IsPadicAt where
  continuous : Continuous a.algebraMap
  valRingBelow_eq : valRingBelow _ (intQpBar p) = LocInt v
  comap_eq : (intQpBar p).comap j = A
  map_algebraMap x : j (algebraMap K Ω x) = a.algebraMap (algebraMap K _ x)
class IsCompletionEmb extends MulSemiringAction (decompGroup Γ A) (PadicAlgCl p), IsLocalGalois (decompGroup Γ A) (LocField v) (intQpBar p), IsPadicAt v p A j where equivariant (g : decompGroup Γ A) x : j (g • x) = g • j x
variable {v p A}
lemma isPlaceOver_placeOfEmb : IsPlaceOver ((intQpBar p).comap j) (placeOfEmb (j.comp (algebraMap K Ω))) := by simp [IsPlaceOver, val_comap_lt_one]
lemma exists_comap_intQpBar_eq (h : A p < 1) : ∃ e, (intQpBar p).comap e = A := (exists_rat_place_of_prime out).rec fun _ ⟨_, _, H⟩ ↦ ((H _ (valuation_comap_intQpBar_lt_one ofNonempty)).exists_smul Gal(Ω/ℚ) (H _ h)).rec fun _ e ↦ ⟨.comp .., smul_eq_comap.symm.trans e⟩
lemma nonempty_isCompletionEmb_of_isPadicAt (H : IsPadicAt v p A j) : Nonempty (IsCompletionEmb v p Γ A j) := have := continuousSMul_of_algebraMap _ _ H.1
  let C := a.2.fieldRange.toIntermediateField (a.linearMap.range.closed_of_finiteDimensional.closure_eq.le <| pClos a.2.fieldRange ·)
  (exists_inducesPlace K Γ H.3).rec fun J ⟨⟨_, e⟩, o, r⟩ ↦ let := compHom ..
    ⟨{ this, H, isGalois_iff_isGalois_bot.1 (.tower_top_intermediateField C), isLocalGalois_localFieldOf o with commutes.1 g y _ := by simpa [a.smul_def] using .inl ((v.denseRange_algebraMap K).eq (by simp [← H.4, e]) (H.1.const_smul _) ..), dvr := H.2 ▸ inferInstance, finite_residue := H.2 ▸ inferInstance, isInvariant.1 _ h := (fixedFieldOf_fixingSubgroup C).le fun ⟨g, G⟩ ↦ ((r g).2 (H.4 · ▸ G ⟨_, _, rfl⟩)).rec (by bound), equivariant := (symm ∘' e ·) }⟩
lemma IsPadicAt.residueCard_eq (H : IsPadicAt v p A j) : _root_.residueCard (LocField v) (intQpBar p) = v.q := by rw! [_root_.residueCard, H.2]; apply card_ResField
lemma IsPadicAt.isUniformiser_iff {π : LocField v} (H : IsPadicAt v p A j) : IsUniformiser (intQpBar p) π ↔ Valued.v π = .exp (-1) := uEqv ((isEquiv_iff_valuationSubring ..).2 H.2) ⟨_, v_uniformizer _⟩
lemma IsPlaceOver.exists_isCompletionEmb (h : IsPlaceOver A v) : ∃ p f a j, Nonempty (IsCompletionEmb (f := f) (a := a) v p Γ A j) := by choose p _ _ l P using v.1.exists_prime_and_absNorm_eq_pow; have := mk P.1; obtain ⟨j, rfl⟩ := exists_comap_intQpBar_eq (h.valuation_natCast_lt_one_iff.2 l); obtain ⟨φ, a, b, c⟩ := (isPlaceOver_placeOfEmb j).unique h ▸ exists_placeOfEmb_extension _; algebraize [φ]; grind [nonempty_isCompletionEmb_of_isPadicAt Γ j ⟨a, SetLike.ext (by simpa using! c.2 · 1), rfl, symm ∘' b⟩]
variable {G R M} [Group G] [AddCommGroup M] {a : G → R} {x : G → M}
def cocycleKer [Monoid R] [DistribMulAction R M] (a : G →* R) (c : ∀ g k, x (g * k) = x g + a g • x k) := Subgroup.ofDiv (x ⁻¹' {0}) ⟨1, by simpa using c 1 1⟩ (by grind [inv_mul_cancel_right, smul_zero])
variable [Ring R] [Module R M] (c : ∀ g k, x (g * k) = x g + a g • x k)
include c
lemma sah γ g : x ((γ * g)⁻¹ * (g * γ)) = 0 → (a γ - 1) • x g = (a g - 1) • x γ := by grind [mul_inv_cancel_left, smul_zero, sub_smul, one_smul]
lemma cocycle_conj_eq_smul {g γ} : a g • x γ⁻¹ = x γ⁻¹ → x (γ * g * γ⁻¹) = a γ • x g := by grind [smul_add, mul_assoc, mul_inv_cancel, c 1 g, c 1 γ⁻¹]
omit c
namespace IsPlaceOver
open NumberField Pointwise Rat Units DiscreteUnits Ideal WithZero IsLocalRing RingHom Valuation
variable (Γ : _) {K : _} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] {A : ClosurePlace} {v : FinPlace K} (h : IsPlaceOver A v)
include h
lemma decompGroup_spec : IsLocalGalois (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A ∧ residueCard (fixedFieldOf (decompGroup Γ A)) A = v.q ∧ ∀ {π : Kˣ}, IsUniformiser A π.1 → IsUniformiser A (π.map (algebraMap K (fixedFieldOf (decompGroup Γ A))).1).1 := by
  let ⟨p, _, _, j, ⟨F⟩⟩ := h.exists_isCompletionEmb Γ
  let φ := comp F.ringEquivFixedPoints.symm.toRingHom (j.restrict (fixedFieldOf (decompGroup Γ A)) _
    fun _ e ↦ (by simp [← F.4, e ·]))
  have c x : φ (Algebra.cast x) = _ := RingHom.injective _ (.trans (by aesop) (F.map_algebraMap x))
  obtain ⟨O⟩ := (by ext; simpa [← F.comap_eq, φ] using! congr(φ _ ∈ $F.valRingBelow_eq) : valRingBelow _ A = (Valued.v.comap φ).valuationSubring), (⟨(v.valuation_exists_uniformizer K).imp'
    Algebra.cast (by simp_all [v_algebraMap_eq_valuation])⟩ : (Valued.v.comap φ).IsNontrivial)
  have s : ((residue _).comp (φ.restrict _ _ O.le) ·).Surjective := (algebraMap_ResField_surjective
    v).forall.2 (⟨⟨_, algebraMap_ringOfIntegers_mem _ ·⟩, congr(residue _ ⟨$(c _), _⟩)⟩)
  have q := ker_eq_maximalIdeal _ s ▸ (quotientKerEquivOfSurjective s).1
  use ⟨(·.2), O ▸ inferInstance, .of_equiv _ q.symm⟩, card_ResField v ▸ Nat.card_congr
    q, by simp; grind [uEqv ((isEquiv_iff_valuationSubring ..).2 O), v_algebraMap_eq_valuation, comap_apply, isUniformiser_iff]
lemma exists_uniformiser : ∃ π : Kˣ, v.valuation K π = exp (-1) ∧ IsUniformiser A (π.map (algebraMap K (fixedFieldOf (decompGroup Γ A))).1).1 := have ⟨π, e⟩ := v.valuation_exists_uniformizer K
  ⟨mk0 π (by grind [exp_pos]), e, (h.decompGroup_spec Γ).2.2 (h.isUniformiser_iff.2 e)⟩
lemma ordD : ordRat (fixedFieldOf (decompGroup Γ A)) A = ordRat K A := have ⟨_, c, d⟩ := h.exists_uniformiser Γ
  by delta ordRat; congr!; use (· _ ∘ @(h.decompGroup_spec Γ).2.2 ·), (fun _ a ↦ ((a _).1 d.val_lt_one).antisymm ((d _).1 a.val_lt_one) ▸ · _ (h.isUniformiser_iff.2 c))
lemma exists_isFrob : ∃ φ : Γ, IsFrob A v.q φ := (h.decompGroup_spec Γ).rec fun L e ↦ L.frobenius_spec.1.rec (⟨·, e.1 ▸ ·⟩)
lemma ordRat_eq_zero_iff {x} : ordRat K A x = 0 ↔ A x.toMul = 1 := h.ordD Gal(Ω/K) ▸ (h.decompGroup_spec _).1.ordRat_eq_zero
lemma ordRat_nonneg_iff x : 0 ≤ ordRat K A x ↔ ↑x.toMul ∈ A := (h.exists_uniformiser Gal(Ω/K)).rec fun _ H ↦ by simpa [h.ordD _, pow_le_one_iff] using ((H.2.val_pow_eq_iff_mul_ordRat (h.decompGroup_spec _).1 ..).2 (den_mul_eq_num _) ▸ zpow_le_one_iff_right_of_lt_one₀ (by simp [pos_iff]) H.2.val_lt_one :).symm
variable {Γ}
lemma ordRat_ofBase (x : Kˣ) : ordRat K A (ofBase Γ Ω (.ofMul x)) = -(v.valuation K x).log := (h.exists_uniformiser Γ).rec fun π H ↦ by simpa [h.ordD Γ] using ((H.2.val_pow_eq_iff_mul_ordRat (h.decompGroup_spec Γ).1 1 (-_)).1 (by simpa using! h.isEquiv.eq_iff (s := π ^ (-_ :)).2 (by aesop)))
lemma ordRat_smul (g : Γ) x : ordRat K (g • A) (unitsRep g x) = ordRat K A x := (h.exists_uniformiser Γ).rec fun π _ ↦ eq_of_forall_le_iff fun q ↦ by simpa [(ofBase Γ Ω _).2 g, ordRat_ofBase (v := v), smul, *, pos, ← den_mul_eq_num] using ((h.smul g).ordRat_nonneg_iff (unitsRep g _)).trans (.trans A.smul_mem_pointwise_smul_iff (h.ordRat_nonneg_iff (q.den • x - q.num • ofBase Γ Ω (.ofMul π))).symm)
lemma ordRat_int_of_inertia_fixed {x} (hx : ∀ g ∈ inertiaGroup Γ A, unitsRep g x = x) : ∃ n : ℤ, ordRat K A x = n := h.ordD Γ ▸ (h.decompGroup_spec Γ).1.exists_ordRat_eq_intCast (hx ·)
lemma ramification_in_tower (U : Subgroup Γ) [O : Fact U.IsOpen] {L} [Field L] [EmbeddedNumberField L] [IsProGalois U L Ω] [Algebra K L] [IsScalarTower K L Ω] {w : FinPlace L} (h' : IsPlaceOver A w) : let e := w.1.ramificationIdx (𝓞 K); (decompGroup Γ A ≤ U → w.q = v.q ∧ ordRat L A = ordRat K A) ∧ (inertiaGroup Γ A ≤ U → e = 1) ∧ U.relIndex (decompGroup Γ A) = e * w.1.inertiaDeg (𝓞 K) := by
  obtain ⟨⟨G, ⟨a⟩⟩, ⟨π⟩⟩ := h.decompGroup_spec Γ, h.exists_uniformiser Γ, LiesOver.mk congr($(h.unique h'.isPlaceOver_below).1)
  obtain ⟨_, _, ⟨⟨n, ⟨q⟩⟩⟩⟩ := (G.of_finite (id ⟨U.subgroupOf _, O.1.preimage_val⟩)).2.1
  erw [← (fixedFieldOf (U.subgroupOf _)).copy_eq (fixedFieldOf (decompGroup U A)) (by aesop), a, (h'.decompGroup_spec U).2.1, FinPlace.q, h.ordD Γ, h'.ordD U, ← absNorm_pow_inertiaDeg v.1, Nat.pow_right_inj v.one_lt_q] at *; cases by simpa [*, h.ordRat_ofBase, ← v.valuation_liesOver L, ramificationIdx'_eq_ramificationIdx, v.3] using (congrArg _ (ext (u := (ofBase Γ Ω (.ofMul π)).1) (IsScalarTower.algebraMap_apply ..))).trans (h'.ordRat_ofBase (Γ := U) (π.map _))
  exact ⟨(by simp_all [U.subgroupOf_eq_top.2 ·]), q ▸ by tauto⟩
lemma decompGroup_le {φ} (hφ : IsFrob A v.q φ) {U} (hU : U.IsOpen) (hI : inertiaGroup Γ A ≤ U) (m : φ ∈ U) : decompGroup Γ A ≤ U := (isClosed_property (@(h.decompGroup_spec Γ).1.frobenius_spec.2.1 ⟨_, hφ.1⟩ (by simpa [h.decompGroup_spec Γ])) (U.isClosed_of_isOpen hU).preimage_val (by aesop) ⟨·, ·⟩)
