import Lib.Adelic.Cartan.ProjectiveModules
import Lib.ClassField.GaloisCohomology.CyclicNorm
import Lib.ClassField.Places.TameInertia
import Lib.ClassField.Places.DecompositionLocal
import Lib.ClassField.Places.AdeleNorm

section
/-! Part of: Local Tate duality in degree 1, as an upper bound for orthogonal groups of cocycles
(known result; see Lib.ClassField.LocalDuality.CrystallineDuality).

Part of: Local class field theory: invariant of the Brauer group, Artin map, norms, tame symbol
(known result; see Lib.ClassField.Local.ArtinMapAtPlace).

This file: Invariant map Br(k) ≅ Q/Z of a henselian local field and its functoriality. Number of
Kummer cocycles; finiteness of local 1-cocycles of finite modules. The local Artin map sends
uniformisers to geometric Frobenius elements. Order bound for orthogonal cocycle groups, the
inequality for local Tate duality. Complex conjugations; symbol of a totally positive element dies
keeping real places real. -/

namespace IsLocalGalois

open Function DiscreteModule Subgroup QZChar QuotientGroup QZ Classical DiscreteUnits AddMonoidHom
variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] (V : OpenSubgroup Γ) {A : ValuationSubring Ω} [L : IsLocalGalois Γ k A]

attribute [-simp] map_smul

/-- Over a local field k, let V be open normal in Γ and β in H²(Γ, Ω^×) die on V, with nβ = 0 only
for n divisible by [Γ : V]. Then every class that dies on V is a multiple of β. -/
lemma mem_zmultiples_of_resH2_eq_zero [V.Normal] {β x} (b : (unitsModule Γ).resH2 V β = 0) (H : ∀ n,
    n • β = 0 → V.index ∣ n) (a : resH2 _ V x = 0) : x ∈ AddSubgroup.zmultiples β := by
  wlog h : Fact V.index.Prime
  · exact mem_of_prime_step _ a fun U W _ hU v hl s m e ↦
     let V' := (V.comap _ (subgroupIncl U).2).comap _ (subgroupIncl W).2
     (this W (L := (of_finite _).1) ((map_nsmul ..).trans (index_smul_eq_zero_of_resH2 V'
       (resH2_swap congr(resH2 _ _ $(resH2_swap (congrArg _ b)))))) (fun n h ↦ by
     erw [← mul_dvd_mul_iff_left (a := V'.index * U.index) (by simp), mul_right_comm,
       relIndex_mul_index v, relIndex_mul_index hU, mul_right_comm]
     apply H; simpa [mul_nsmul] using index_smul_eq_zero_of_resH2 U (by simpa)) e ⟨hl⟩).elim fun j
       e ↦ ⟨s + j • V'.index • β, by bound, by simpa [← sub_sub] using! e.symm⟩
  obtain ⟨⟨F⟩, ⟨⟩, ψ, rfl⟩ := of_finite V, V,
    exists_ker_eq_of_isCyclic V (isCyclic_of_prime_card (hp := h) rfl)
  rw [(cyclicClass_spec ψ).1] at *
  obtain ⟨⟨y, rfl⟩, ⟨x, rfl⟩, e⟩ := b, a,
    cokerKerIndex_local_units F (ker ψ).index topEquiv.toAdditive
  let f := lift (map _ ⊤) ((cyclicClass _ ψ).comp (ofBase Γ Ω)).toMultiplicativeRight fun _ ⟨_, _,
    e⟩ ↦ (cyclicClass_eq_zero_iff_norm _).2 ⟨_, e⟩
  exact (f.map_zpowers y).le ⟨x, mem_zpowers_of_prime_card (hp := h) (pow_left_injective
    h.1.pred_pos.ne' (by qify; erw [← mul_left_inj' e.1, ← index, ← relIndex_top_right,
    tate_index_formula_norm (index _)] <;> simp [*, finrank_fixedFieldOf,
    Ne, ↓cokerKerIndex_local_units L _ topEquiv.toAdditive, mul_pow, ← mul_assoc,
    pow_sub_one_mul NeZero.out])) (h.1.not_dvd_one <| H 1 <| by simpa using! congrArg f ·), rfl⟩

/-- For a local field k, the map c = `classOfInv` from ℚ/ℤ to H²(Γ, Ω^×) is injective, and
the symbol (χ, w) equals n·c(χ(φ)) for unramified χ, any Frobenius φ and any Γ-invariant w
of order n. -/
lemma isClassOfInv_classOfInv : IsClassOfInv Γ k A (classOfInv Γ k A) := epsilon_spec (by
  have hp := L.exists_isUniformiser.choose_spec.ordRat_eq_one L; set p := ofBase (K := k) Γ Ω _
  choose c hc hu using existsUnique_unramified_char L.frobenius_spec.1.choose_spec
  have d {χ} (u : inertiaGroup Γ A ≤ QZChar.ker χ) w (n : ℤ) (e : ordRat k A w.1 = n) h :
    ↑(ker χ).index ∣ n := (((cyclicClass_spec χ).2 w).1 h).elim fun y h ↦
    (exists_ordRat_eq_intCast (y.2 ⟨·, u ·⟩)).imp fun j hj ↦ by qify; erw [← e, ← h, corestrictH0,
    LinearMap.sum_apply, map_sum, Finset.sum_eq_card_nsmul (b := ↑j)] <;> simp [index,
    Fintype.card_eq_nat_card, ← hj, eq_iff, ↓L.ordRat_eq_zero, decompGroup.val_smul, L.4]
  use ((cyclicClass _).flip p).comp (.mk' c fun a b ↦ (hu _ _ (by simp_all)).symm),
    .of_ker _ fun r h ↦ (hc r).2 ▸ (index_eq_one.1 (Nat.dvd_one.1
    (mod_cast d (hc r).1 p 1 hp h))).ge ⟨⟩, fun χ u φ f w n hn ↦ ?_
  have s w := ((ofBase_bijective Γ).2 w).choose_spec ▸ ((cyclicClass_spec χ).1 _).2 ⟨_, rfl⟩
  obtain ⟨j, e⟩ :=
    mem_zmultiples_of_resH2_eq_zero _ (s p) (fun n _ ↦ by zify; simp [d u (n • p), *]) (s w)
  simp [← hu (χ.1 φ) χ ⟨u, (toHom χ).eq_iff.2 (u _ (f.inv_mul (choose_spec _)))⟩, ← e,
    ← addOrderOf_dvd_sub_iff_zsmul_eq_zsmul]
  grw [addOrderOf_dvd_of_nsmul_eq_zero (index_smul_eq_zero_of_resH2 _ (s p)),
    d u (j • p - w)] <;> simp [*])

/-- Let k, k' be local, j : Ω → Ω' equivariant along φ : Γ' → Γ, j⁻¹A' = A, q' = q^f, and ord w
= 1, ord' j(w) = e for a Γ-fixed w. Then (φ, j) sends the class in H²(Γ, Ω^×) of invariant r
to that of invariant ef·r. -/
lemma pairMapH2_classOfInv {Γ' k' Ω' : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k'] [Field Ω']
  [Algebra k' Ω'] [MulSemiringAction Γ' Ω'] {A'} [L' : IsLocalGalois Γ' k' A'] (φ : Γ' →ₜ* Γ) (j :
  Ω →+* Ω') (hA : A'.comap j = A) (H : ∀ g x, j (φ g • x) = g • j x) {e f : ℕ} {w :
  (unitsModule Γ).H0} (he : ordRat k A w = 1 ∧ ordRat k' A' ((Units.map j).toAdditive w.1) =
  e) (hf : residueCard k' A' = residueCard k A ^ f) r : (pairMapH2 φ (Units.map
  j).toAdditive.toIntLinearMap) (classOfInv Γ k A r) = classOfInv _ k' A' ((e * f) • r) := by
  obtain ⟨rfl, ⟨_, s⟩, _, t⟩ := hA, L.frobenius_spec.1, L'.frobenius_spec.1
  obtain ⟨χ, ⟨⟨c, rfl⟩⟩⟩ := existsUnique_unramified_char s r
  rw [mul_smul, map_nsmul, ← (isClassOfInv_classOfInv.2 _ c _ s _ 1 he.1).trans (one_zsmul _)]
  convert! isClassOfInv_classOfInv.2 (comap φ χ) (fun _ ↦ c _ ∘ .map H) _ t ⟨_, _⟩ e he.2
  exacts [congr(⟦⟨fun _ ↦ $(map_zsmul ..), _⟩⟧), (map_pow ..).symm.trans ((toHom χ).eq_iff.2 (c _
    ((hf ▸ t.map H).inv_mul (s.pow f)))), fun g ↦ ext (H .. ▸ congr(j $(w.2 _).1):)]

/-- Restriction multiplies the invariant by the degree: for k local and V open in Γ with fixed
field k'', the Brauer class `classOfInv` of r ∈ ℚ/ℤ for k restricts to the class of
[Γ:V]·r for k''. -/
lemma _root_.resH2_classOfInv {r} : (unitsModule Γ).resH2 V (classOfInv Γ k A r) = classOfInv _
  (fixedFieldOf V.1) A (V.index • r) := have p :=
    L.exists_isUniformiser.choose_spec.ordRat_eq_one L; (of_finite V).rec fun _ ⟨⟨_, _,
  ⟨h, q, _⟩, _⟩, _⟩ ↦ h ▸ pairMapH2_classOfInv _ (.id _) rfl (by tauto) ⟨p, by simp [*]⟩ q _

lemma resH2_classOfInv_eq_zero {r} (h : V.index • r = 0) : (unitsModule Γ).resH2 V
    (classOfInv Γ k A r) = 0 := resH2_classOfInv V ▸ h ▸ map_zero _

/-- Brauer group of a local field, ℚ/ℤ ≅ Br(k): for a henselian local field k of characteristic
0 with absolute Galois group Γ, the map `classOfInv` from ℚ/ℤ to H²(Γ, Ω^×) is bijective.

Known result: Local class field theory: invariant of the Brauer group, Artin map, norms, tame
symbol. -/
lemma classOfInv_bijective : Bijective (classOfInv Γ k A) := ⟨isClassOfInv_classOfInv.1, Quot.ind
  fun ⟨_, c, q⟩ ↦ (exists_openNormalSubgroup_apply_eq (c.comp continuous_swap)).elim fun W w ↦
  (range _).zmultiples_le_of_mem ⟨@ofZMod W.index ⟨by simp⟩ 1, rfl⟩ (mem_zmultiples_of_resH2_eq_zero
  _ (resH2_classOfInv_eq_zero _ (by simp [← map_nsmul])) (by simp [← map_nsmul, map_eq_zero_iff,
  isClassOfInv_classOfInv.1, ZMod.natCast_eq_zero_iff]) ((Submodule.ker_mkQ
  _).ge ⟨_, continuous_const, fun g k ↦ (w k k.2 g).trans (by simpa using! q g 1 1)⟩))⟩

/-- For a local field k and an open subgroup V of its Galois group Γ, every class in H²(V, Ω^×)
is the restriction of the class in H²(Γ, Ω^×) with invariant r, for some r in ℚ/ℤ. -/
lemma exists_resH2_classOfInv_eq y : ∃ r, (unitsModule Γ).resH2 V (classOfInv Γ k A r) = y :=
  ((of_finite V).1.classOfInv_bijective.2.comp
  (DivisibleBy.surjective_smul _ ℤ (by simp)) y).imp fun _ ↦ (resH2_classOfInv V).trans

open Nat HasEnoughRootsOfUnity NeZero LinearMap CommGroup Ideal
variable {A : ValuationSubring Ω} [h : IsLocalGalois Γ k A]
include h

/-- Kummer theory: for a local field k with integers O and n ≥ 1, the continuous 1-cocycles Γ →
Ω^× killed by n, that is Z¹(Γ, μ_n), form a finite group of order n²·#(O/n). -/
lemma card_kummer_cocycles (n : ℕ) [NeZero n] : let c := .card (n :
    Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker
  0 < c ∧ c = n ^ 2 * .card (_ ⧸ span {(n : valRingBelow k A)}) := by
  have s : Surjective (unitsModule Γ).coboundary := (hilbert90_unitsRep · |>.imp (by aesop))
  have ⟨a, b⟩ :=
    cokerKerIndex_local_units h n (.symm (.ofBijective _ (DiscreteUnits.ofBase_bijective Γ)))
  have H := cokerKerIndex_mul_of_exact _ _ (Submodule.subtype_injective _) (by
    simp [Exact, Subtype.ext_iff, funext_iff]) s a
  erw [b, cokerKerIndex, cokerKerIndex, LinearMap.range_eq_top.2 (·.exists_nsmul out),
    LinearMap.range_eq_top.2 (.of_comp
    ((funext (map_nsmul _ n)).subst (s.comp (·.exists_nsmul out)))), natCard_rootsOfUnity] at H
  qify [card_unique] at *; grind

/-- If k is a local field with absolute Galois group Γ (`IsLocalGalois`), then for every finite
discrete Γ-module M over a commutative ring R, the module Z¹(Γ, M) of continuous 1-cocycles
is finite. -/
lemma finite_Z1_local ⦃R⦄ [CommRing R] (M : DiscreteModule R Γ) [Finite M] : Finite (Z1 M.ρ) := by
  have ⟨⟨U, _⟩, w⟩ := exists_openNormalSubgroup_apply_eq M.cartierDual.continuous
  have e := equivFinOfCardPos ((of_finite U).1.card_kummer_cocycles (.card M)).1.ne'
  refine .of_injective (fun ⟨z, _, d⟩ ↦ ((z ·.out : _ ⧸ U.1 → _), fun f : _ →+ _ ↦ e ⟨⟨(f <| z ·),
    by fun_prop, fun g h ↦ by simpa [d] using! congr($(w _ g.2 f) (M.ρ g _)).symm⟩,
    by ext; simp [← map_nsmul]⟩)) ?_
  rintro ⟨_, _, a⟩ ⟨_, _, b⟩ h; ext g; have ⟨u, v⟩ := QuotientGroup.mk_out_eq_mul U g
  simpa [a, b, v, Equiv.injective _ ((forall_apply_eq_apply_iff (Multiplicative M)).1
    (congr($(e.injective congr($h.2 ·.toAdditiveRight)).1.1 u)))] using congr($h.1 g)

end IsLocalGalois

open QuotientGroup Units QZChar Complex NeZero NumberField DiscreteUnits

lemma IsLocalArtin.exists_frob_of_isUniformiser {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ]
  [Field k] [Field Ω] [Algebra k Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [L :
  IsLocalGalois Γ k A] {π : kˣ} {F} (hF : IsLocalArtin Γ k A F) (h : IsUniformiser A π.1) : ∃ φ : Γ,
  IsFrob A (residueCard k A) φ ∧ F π = φ⁻¹ := L.frobenius_spec.1.elim fun φ f ↦
  (QZChar.mem_of_forall_abelianLift (continuous_mk.isClosedMap _ isClosed_inertiaGroup) (H := .map
  (mk' _) (inertiaGroup Γ A)) (φ⁻¹ / F π) fun _ _ ↦ Multiplicative.ext (L.isClassOfInv_classOfInv.1
  (by simp_all [IsLocalArtin, h.ordRat_eq_one, L.isClassOfInv_classOfInv.2
  _ _ _ f _ 1]))).rec fun _ e ↦ ⟨_, by simpa using f.mul_iff.2 e.1, by aesop⟩

section


open DiscreteUnits DFunLike DiscreteModule QZChar NeZero QZ Ideal AddSubgroup IsLocalGalois Nat
  Function
variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [J : IsLocalGalois Γ k A] {l r : ℕ}
  [Fact l.Prime] {R S} [CommRing R] [CommRing S] {M : DiscreteModule R Γ} {N : DiscreteModule S Γ}

lemma char_eq_zero_of_cyclicClass_eq_zero {χ} (h : ∀ w : Additive kˣ,
  cyclicClass _ χ (ofBase Γ Ω w) = 0) g : χ.1 g = 0 :=
  isClassOfInv_classOfInv.1 ((((cyclicClass_spec χ).1 _).1 (resH2_classOfInv_eq_zero _ (by
    simpa using! (ker χ).pow_index_mem g))).choose_spec.trans (by simp [h]))

/-- Let k be local, b : M × N → Ω^× equivariant, i·[Γ:U] act as the identity on M, and X, Y
contain the coboundaries and a corestriction of each cocycle of X', Y'. If X' contains the
cup product annihilator of Y' over U, then X contains that of Y. -/
lemma DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le {U X X' Y Y'} {i : ℤ} (g :
  HoldsCorestrictions U X' X) (h : HoldsCorestrictions U Y' Y) (c : ∀ m : M, i • U.index • m =
  m) {b} e (a : pairingAnnihilator (cupProduct (unitsModule _) _ _ b (e ·)).flip Y' ≤ X') :
  pairingAnnihilator (cupProduct (unitsModule Γ) M N b e).flip Y ≤ X := fun z hz ↦ (g.2 ((pairMapZ1
  _ .id) z) (a fun y hy ↦ (h.2 _ hy).rec fun F ⟨f, o⟩ ↦ (exists_resH2_classOfInv_eq U (shapiroH2 U
  (cupProduct _ _ (N.funModule _) (.mk' (b · |>.compLeft _) (by bound)) (by simp [funext_iff, e]) z
  F))).elim fun _ s ↦ (s.trans congr(⟦⟨fun _ ↦ b _ $(f ▸ funModule_apply_one ..), _⟩⟧)).symm.trans
  (resH2_classOfInv_eq_zero U (isClassOfInv_classOfInv.1 (by
    rw [map_zero, ← hz _ o, map_nsmul, ← mapH2_sum_eq_index_smul U _ _ s]
    exact congr(⟦$(by simp [← (sum ..).isIntertwining]; simp [sum])⟧)))))).rec fun F ⟨f, o⟩ ↦ by
  have ⟨n, e⟩ := shapiro_H1 U (F - (const ..).mapZ1 z) 0 (by simpa using! congr($f.1 ·))
  convert zsmul_mem (sub_mem o (g.1 (M.sum _ n))) i
  ext g; rw [← c (z.1 g), index_smul_eq_sum_const]
  simpa [← (sum ..).isIntertwining] using! congr(i • M.sum _ (F.1 g - $(e g)))

/-- Let k be local, #(O/l) = l^d, and M finite, killed by l^r and fixed by Q, every g having
some g^(l^i) in Q. Then groups X ⊂ Z¹(Hom(M, Ω^×)) and W ⊂ Z¹(M), orthogonal under the cup
product, have #X·#W ≤ (#M)^(2+d).

Known result: Local Tate duality in degree 1, as an upper bound for orthogonal groups of
cocycles. -/
lemma card_mul_card_le_of_orthogonal {d} Q (hd : .card (_ ⧸ span {(l : valRingBelow k A)}) = l ^ d)
  (c : FiniteKilledFixedInj (l ^ r) Q 1 0 M) (p : ∀ g, ∃ i, g ^ l ^ i ∈ Q) : have := c.1; ∀ X W, X ≤
    pairingAnnihilator M.evalCup.flip W → Nat.card X * .card W ≤ .card M ^ (2 + d) := by
  obtain ⟨⟨⟨⟩, b⟩⟩ := (J.card_kummer_cocycles l).imp_left card_pos_iff.1, J.finite_Z1_local,
    (unitsModule Γ).continuous
  refine M.devissage_induction rfl ⊤ Q (by simpa) (fun M _ ⟨_, c, t,
    _⟩ X W h ↦ have := AddCommGroup.zmodModule c
    have e := Module.finBasis (ZMod l) M; ?_) (fun {_ _ _ ι π} s c H G X W h ↦ ?_) c
  grw [card_le_of_le h, card_pairingAnnihilator_mul_card _ (.ofBijective _ classOfInv_bijective),
    card_eq_one.2 (bot_unique fun y hy ↦ Subtype.ext (funext ?_)), mul_one, card_congr
    e.equivFun.toEquiv, card_fun, card_zmod, pow_right_comm, pow_add, ← hd, ← b, ← card_fun]
  exact card_le_card_of_injective (fun z j ↦ ⟨pairMapZ1 (.id _) ⟨⟨(· (e j)), by simp⟩, by simp⟩ (by
    simp [t]) z, by ext; simp [← map_nsmul, c]⟩) fun x y h ↦ by ext g : 3; exact (((((x.1 g).eqLocus
    _).toZModSubmodule l).eq_top_iff_forall_basis_mem e).2 fun j ↦ congr(($h j).1.1 g)).ge ⟨⟩
  exact (eq_zero_of_forall_hom_eq_zero <| (bijective_ofZMod_comp c).2.forall.2 fun j ↦
    char_eq_zero_of_cyclicClass_eq_zero (χ := ofZModCocycle l ⟨j ∘ y.1,
    y.2.imp (by fun_prop) (by simp_all)⟩) (fun x ↦ (exists_nsmul _ out).rec fun a u ↦ neg_eq_zero.1
    ((kummer_cup_eq_neg_cyclicClass u _ _ (by simp [t])).symm.trans (ext_iff.1 hy.1 ⟨fun g ↦ .mk'
    (fun m ↦ (j m).val • (unitsRep g a - a)) (by simp [ZMod.val_add, add_smul, ← nsmul_eq_mod_nsmul,
    smul_sub l, ← map_nsmul, u, DiscreteUnits.ext_iff]), .congr (by simp; fun_prop)
    (leftInverse_invFun coe_injective ∘' _), by simp [ext_iff, t, smul_sub]⟩))) ·)
  obtain ⟨⟨⟩, ⟨⟩, ⟨⟩⟩ := c, c.of_isShortExact s
  grw [(π.cartierDualMap.card_eq_card_comap_mul_card_map (π := ι.cartierDualMap) ?_
    (.of_comp_of_mem_range ?_ (.imp (fun _ ↦ DFunLike.ext _ _) ∘ exists_extend _ · ∘ ?_)) X).trans
    (mul_comm ..), ι.card_eq_card_comap_mul_card_map s.1 s.2.1 W, mul_mul_mul_comm, G, H,
    s.card_eq_mul, mul_pow] <;> simp [s.2.2.forall, s.2.1 _, Injective, ext_iff, LE.le, (s.2.1 _).2,
    funext_iff, pairingAnnihilator, -Subtype.forall, -Subtype.exists] <;> exact fun _ o _ m ↦
    .trans congr(⟦$(by simp [ι.isIntertwining, π.isIntertwining])⟧) (h o _ m)

/-- Local field, M finite, [Γ:U] prime to #M. Let X' ⊂ Z¹(U, M^*), W' ⊂ Z¹(U, M) be orthogonal
with #X'·#W' maximal among orthogonal pairs; let X, W contain the coboundaries and a
corestriction of each member. Then #L^⊥·#L divides #W·#X for all L ⊂ Z¹(Γ, M^*).

Known result: Local Tate duality in degree 1, as an upper bound for orthogonal groups of
cocycles. -/
lemma DiscreteModule.local_duality_card_dvd [Finite M] {U X W X' W'} (hX :
  M.cartierDual.HoldsCorestrictions U X' X) (hW : M.HoldsCorestrictions U W' W) (c :
  (Nat.card M).Coprime U.index) (o : W' ≤ pairingAnnihilator (M.restrictTo U).evalCup X') (H :
  ∀ Y Z, Y ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip Z → Nat.card Y * .card Z ≤ .card X' *
  .card W') L : Nat.card (pairingAnnihilator M.evalCup L) * .card L ∣ .card W * .card X := by
  obtain ⟨e, k⟩ := AddEquiv.ofBijective _ J.classOfInv_bijective, (nsmulCoprime c).left_inv,
    (of_finite U).1.finite_Z1_local
  grw [card_pairingAnnihilator_mul_card _ e, card_dvd_of_le (inf_le_of_left_le (le_inf le_rfl fun x
    e ↦ hX.pairingAnnihilator_le hW (fun m ↦ DFunLike.ext _ _ (by simpa using congr(m $(k ·))))
    (by simp) (eq_of_le_of_card_ge (by tauto) (le_of_mul_le_mul_right (H _ _ le_rfl) card_pos)).ge
    fun _ _ ↦ ext_iff.1 e _)), ← card_pairingAnnihilator_mul_card _ e, card_dvd_of_le fun w e ↦
    hW.pairingAnnihilator_le hX k (by simp) (fun w e ↦ (eq_of_le_of_card_ge o
    (le_of_mul_le_mul_left (H _ _ (by tauto)) (@card_pos X' _ _))).ge (neg_eq_zero.1 <|
    (cupProduct_flip ..).symm.trans <| e · ·)) ((cupProduct_flip ..).trans <| by simpa using e · ·)]

end

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] {K' : Type} [Field K'] [t :
  IsTotallyComplex K'] (x : K') {c : Γ} [Algebra K Ω] [MulSemiringAction Γ Ω] [G :
  IsProGalois Γ K Ω]

lemma isTotallyPositive_of_isTotallyComplex : IsTotallyPositive x :=
  (absurd (by ext; simp) <| t.complexEmbedding_not_isReal <| ofRealHom.comp ·)

lemma isReal_comp_algebraMap {j} (h : ∀ x, j (c • x) = star (j x)) :
    ComplexEmbedding.IsReal (.comp j (algebraMap K Ω)) := by ext; simp [← h, ← star_def]

variable (Γ) in
lemma exists_isComplexConj [NumberField K] {w : InfinitePlace K} (h : w.IsReal) : ∃ c : Γ,
  IsComplexConj c :=
  (exists_smul_emb_eq Γ (ComplexEmbedding.lift Ω w.embedding) (star _) (by aesop)).rec (⟨·, _, ·⟩)

include K in
lemma IsComplexConj.mul_self (h : IsComplexConj c) :
    c * c = 1 := h.rec (G.faithful.1 <| by simp [mul_smul, ← ·.injective.eq_iff, ·])

/-- For x ∈ K^× totally positive and a character χ, the symbol (χ, x) ∈ H²(Γ, Ω^×) restricts to
zero on some open subgroup containing all complex conjugations. -/
lemma IsTotallyPositive.exists_resH2_cyclicClass_eq_zero {χ} {x : Kˣ} (p : IsTotallyPositive x.1) :
  ∃ U : OpenSubgroup Γ, (∀ c, IsComplexConj c → c ∈ U) ∧ (unitsModule Γ).resH2 U
  (cyclicClass _ χ (ofBase Γ Ω (.ofMul x))) = 0 := (exists_nsmul _ out).elim (⟨⟨_, G.6 ·.toMul.1⟩ ⊓
  ⟨_, isOpen_ker (χ + χ)⟩, fun c h@⟨j, hj⟩ ↦ ⟨j.injective (by simpa [*, conj_eq_iff_im, ←
  sq_nonneg_iff, ← zero_le_real, ← map_pow, ← val_pow_eq_pow_val, ← toMul_nsmul] using
  (p (isReal_comp_algebraMap hj).embedding).le), map_mul_eq_one (toHom χ) h.mul_self⟩,
  DiscreteModule.resH2_cyclicClass_eq_zero · (·.2.imp DiscreteUnits.ext (two_nsmul _).trans)⟩)

lemma IsComplexConj.false_of_isTotallyComplex (h : IsComplexConj c) [t : IsTotallyComplex K] :
    False := t.complexEmbedding_not_isReal _ (isReal_comp_algebraMap h.choose_spec)

omit [TopologicalSpace Γ] in
lemma IsComplexConj.cycCharMod_eq_neg_one (h : IsComplexConj c) {N} [NeZero N] :
  _root_.cycCharMod Ω N c = -1 := h.rec fun j _ ↦ Units.ext
  (.trans (cycCharMod_eq_iff.2 fun ζ e ↦ left_inv_eq_right_inv (j.injective (by simp_all [conj_mul',
  ← map_pow, norm_eq_one_of_pow_eq_one _ (ne N)])) (e ▸ mul_pow_sub_one out _)) (by simp [pos]))

omit [TopologicalSpace Γ] in
/-- If σ ∈ Γ acts as a complex conjugation on the algebraically closed field Ω of characteristic
zero, then the ℓ-adic cyclotomic character takes the value −1 at σ. -/
lemma IsComplexConj.cycChar_eq_neg_one (h : IsComplexConj c) l [Fact (Nat.Prime l)] :
  _root_.cycChar Ω l c = -1 := Units.ext (PadicInt.ext_of_toZModPow.1
  (by simpa [cycCharMod_prime_pow_eq, ← val_inj] using h.cycCharMod_eq_neg_one (N := l ^ ·)))
end

/-! Known result: Local class field theory, covering the invariant of the Brauer group, the Artin
map, norms and the tame symbol. It is proved here for henselian fields such as fixed fields of
decomposition groups, and the norm index in prime degree comes from Tate's lemma on the Herbrand
quotient. The Artin map sends uniformisers to geometric Frobenii. Source: J.-P. Serre, Local Fields
(1979), XII–XIV; J. S. Milne, Class Field Theory (v4.03), I and III 2.

This file: Local Artin map: norm functoriality, density, units to inertia, tame symbol, tame
generator. -/

attribute [-simp] map_smul one_apply


open Filter WithZero Units Module LinearMap Classical Subgroup DFunLike QZChar IsProGalois Valued
variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] {w : FinPlace K}

/-- For a finite place w of a number field K and n ≠ 0, every subgroup T of K_w^× that contains all
n-th powers is open. -/
lemma isOpen_of_forall_pow_mem {n} (hn : n ≠ 0) {T : Subgroup (LocField w)ˣ} (h : ∀ y, y ^ n ∈ T) :
    T.IsOpen := let := toNontriviallyNormedField (LocField w) _
  T.isOpen_of_mem_nhds ((nhds _).3 (continuous_val.tendsto (1 ^ n) (((hasStrictDerivAt_pow
  ..).map_nhds_eq (by simpa)).ge range_mem_map)) fun x ⟨y, e⟩ ↦ (ext e).subst (h (x.ofPow y hn e)))

/-- Every homomorphism from K_w^× to the topological abelianisation of a profinite group is
continuous. -/
lemma continuous_hom_locField_units [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] (f : (LocField w)ˣ →* TopologicalAbelianization Γ) : Continuous f :=
  continuous_iff_isOpen_ker.2 fun χ ↦
  isOpen_of_forall_pow_mem (quotient_finite_of_isOpen _ ((continuous_abelianLift χ).1 {1} ⟨⟩)
  ).card_pos.ne' (f.map_pow · _ ▸ (abelianLift χ).ker.pow_index_mem _)

variable [Algebra K Ω]

/-- The union of the inertia groups in Gal(Ω/K) of all valuation subrings of Ω lying over a
prime of the set S of primes of K. -/
def inertiaAbove (S : Set (FinPlace K)) :=
  {g | ∃ v ∈ S, ∃ A : ClosurePlace, IsPlaceOver A v ∧ g ∈ inertiaGroup Gal(Ω/K) A}

namespace IsPlaceOver

variable [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] {A : ClosurePlace} (h : IsPlaceOver A w)

include h

/-- For A over w and an embedding of Ω in ℚ̄_p inducing A, f = `localArtin` satisfies χ(f
x) = −inv(χ, x): on K_w^× for the invariant of K_w, and on K^× for the invariant of the
decomposition field of A. -/
lemma isLocalArtin_localArtin {p} [Fact p.Prime] [Algebra (LocField w) (PadicAlgCl p)] {j}
    (F : IsCompletionEmb w p Γ A j) : let f := localArtin Γ A w
  IsLocalArtin _ (LocField w) (intQpBar p) f ∧
    IsLocalArtin _ (fixedFieldOf (decompGroup Γ A)) A (f.comp (map (algebraMap K _).1)) := by
  obtain ⟨⟨L⟩, ⟨f, e⟩, π, hπ, u⟩ := h.decompGroup_spec Γ, exists_hom_abelianLift_eq (((-cyclicClass
    _).compr₂ (AddEquiv.ofBijective _ F.classOfInv_bijective).symm.toAddMonoidHom).flip.comp
    (DiscreteUnits.ofBase (K := LocField w) ..)), h.exists_uniformiser Γ
  suffices _ from have G := @epsilon_spec _ (IsLocalArtin _ _ A <| .comp · _) ⟨f, this⟩
    ⟨by simp [IsLocalArtin, e, (continuous_hom_locField_units (localArtin ..)).ext_on
      ((w.denseRange_algebraMap K).preimage isOpenMap_val) (continuous_hom_locField_units f) fun y
      ⟨x, e⟩ ↦ abelianization_ext (L.isClassOfInv_classOfInv.1 <| by
      erw [← ext (u := .map _ (mk0 x (by grind [ne_zero]))) e, G ·, this])], G⟩
  refine fun χ x ↦ (L.classOfInv_bijective.2 _).rec fun s t ↦
    .trans (congrArg _ (F.isClassOfInv_classOfInv.1 ?_)) t
  simp [*, ← one_nsmul s ▸ L.pairMapH2_classOfInv (L' := F.2) (f := 1) (.id _) j F.comap_eq
    F.equivariant ⟨u.ordRat_eq_one L, (congrArg _ (ext (F.map_algebraMap π))).trans
    ((F.isUniformiser_iff.2 (hπ ▸ v_algebraMap_eq_valuation _)).ordRat_eq_one F.2
    (π := π.map _))⟩ (by bound [F.residueCard_eq]) s]
  exact congr(⟦$(by ext; simp [F.map_algebraMap])⟧)

/-- Let A lie over w in K, j: Ω → Ω extend k → K. If jg = g'j and Art_w y = g', the local norm of y
has symbol g. If ker χ consists of the g admitting such g', χ(Art x) = 0 makes x a local norm from
K_w.

Known result: Local class field theory: invariant of the Brauer group, Artin map, norms, tame
symbol. -/
lemma localArtin_adeleNorm {Γ' k : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k]
  [EmbeddedNumberField k] [MulSemiringAction Γ' Ω] [IsProGalois Γ' k Ω] [Algebra k K] (ψ : Γ →* Γ')
  (j : Ω →+* Ω := 1) (hψ : ∀ g x, j (ψ g • x) = g • j x := by tauto) (hj : ∀ x, j (algebraMap k Ω
  x) = algebraMap K Ω (algebraMap k K x) := by simp) : (∀ {y} {g : decompGroup Γ A}, localArtin Γ A
  w y = g → localArtin Γ' (A.comap j) _ (localNorm k w y) = (⟨_, decompGroup.map hψ g.2⟩ :
  decompGroup ..)) ∧ ∀ {χ x}, (∀ g' : decompGroup Γ' (A.comap j), χ.1 g' = 0 ↔ ∃ g : decompGroup Γ
  A, ψ g = g') → abelianLift χ (localArtin Γ' _ _ x) = 1 → ∃ y, localNorm k w y = x := by
  set u := w.below k
  algebraize [locMap _ (refl u), evalAt u, (locMap _ rfl).comp (evalAt u)]
  let π := (⟨evalAt w, by aesop⟩ : _ →ₐ[𝔸f k] _).toLinearMap.liftBaseChange (LocField u)
  let ε := π.quotKerEquivOfSurjective (⟨1 ⊗ₜ singleAdele w ·, by aesop⟩)
  have N {y} : localNorm k w y = y.map (Algebra.norm (LocField u)) :=
    let M := (mulLeft (𝔸f k) (locIdele w y).1).baseChange (LocField u)
    have : ∀ x ∈ π.ker, M x = x := (TensorProduct.mk_surjective _ _ _
      (⟨singleAdele u ·, dite_eq_left
      rfl⟩)).forall.2 fun z h ↦ congr(1 ⊗ₜ $(ext_iff.2 ((and_forall_ne w).1 (by aesop))))
    ext ((det_baseChange _).symm.trans ((det_conj _ ε.symm).subst (by
    erw [M.det_eq_det_mul_det π.ker (by aesop_cat), (by bound : M.restrict _ = 1)]
    simp; congr with
    exact ε.eq_symm_apply.2 (by aesop : π (1 ⊗ₜ _) = _ * π (1 ⊗ₜ _)))))
  obtain ⟨_, _, _, a, i, ⟨F⟩⟩ := Finite.equiv ε, h.exists_isCompletionEmb Γ
  algebraize [a.2.comp (locMap _ (refl u))]
  obtain ⟨_, ⟨f⟩⟩ := F.2.1, nonempty_isCompletionEmb_of_isPadicAt Γ' (v :=
    u) (i.comp j) ⟨F.continuous.comp (by fun_prop), congr(($F.valRingBelow_eq).comap _).trans
    (by ext; apply v_locMap_le_one), congr(($F.comap_eq).comap j),
    by simp_all [F.map_algebraMap, ← locMap_algebraMap]; tauto⟩
  obtain ⟨_, ⟨φ, hφ⟩, E, -⟩ := f.2.1, exists_galois_restrict _ (G :=
    f.2.1) (decompGroup Γ A) (.id _) fun g _ ↦ smul_algebraMap g (_ : LocField w),
    isLocalArtin_localArtin (by simp [hj ·, ← h _, u, val_comap_lt_one]) f
  have o := Fact.mk (φ.coe_range ▸ (isOpenEmbedding_galois_restrict _ hφ).2)
  have := of_fixingSubgroup_eq (isClosedEmbedding_galois_restrict _ hφ).2.1.symm
  simp_rw [fun g : decompGroup Γ A ↦ show ψ g = φ g from (IsGaloisGroup.faithful k).1 fun _ ↦
    j.injective (i.injective (by erw [hψ, F.equivariant, f.equivariant, ← hφ]; rfl))]
  use fun hy ↦ abelianization_ext fun χ ↦ f.isClassOfInv_classOfInv.1 ?_, fun h hx ↦
    ((cyclicClass_eq_zero_iff_norm (J := (ext (by simpa using! h) : QZChar.ker _ =
    φ.range) ▸ this) _).1 (neg_eq_zero.1 (E .. ▸ hx ▸ map_zero _))).imp fun _ ↦ N.trans
  obtain ⟨⟨_, ⟨⟨_, _, ⟨⟨b, q, _⟩⟩⟩⟩⟩, P⟩ := f.of_finite ⟨_, o.1⟩ _,
    (f.isUniformiser_iff.2 (v_uniformizer _)).ordRat_eq_one f.2
  choose r s using f.exists_resH2_classOfInv_eq ⟨_, o.1⟩
  erw [N, E, DiscreteModule.cyclicClass_corestrictH0 _ χ _ (corestrictH0_ofBase_eq_norm ..) _ (s _),
    ← map_nsmul, ← map_neg, f.isClassOfInv_classOfInv.1.eq_iff,
    ← F.isClassOfInv_classOfInv.1.eq_iff, map_neg, ← (b ▸ f.pairMapH2_classOfInv φ (.id _) rfl hφ
    ⟨P, by simp [*]⟩ q :), (Quot.ind (by bound) : ∀ x y, (unitsModule _).resH2 _ x = y →
    pairMapH2 φ _ _ x = pairMapH2 ⟨φ.rangeRestrict, φ.2.subtype_mk _⟩ .id _ y) _ _ (s _),
    ← (h.isLocalArtin_localArtin F).1 (comap φ _), hy]; bound

/-- For A lying over w, the local Artin map from K_w^× to the abelianised decomposition group of A
has dense image. -/
lemma denseRange_localArtin :
  DenseRange (localArtin Γ A w) := have ⟨p, _, _, _, ⟨F⟩⟩ := h.exists_isCompletionEmb Γ
  Quot.ind (mem_of_forall_abelianLift (MonoidHom.range _).isClosed_topologicalClosure _ fun χ H ↦
    char_eq_zero_of_cyclicClass_eq_zero
    (by simpa [H _ (subset_closure ⟨_, rfl⟩)] using (h.isLocalArtin_localArtin F).1 χ) ·)

/-- For A lying over w and a uniformiser x of K_w, the local Artin symbol of x is the class of s⁻¹
for some arithmetic Frobenius s in the decomposition group of A. -/
lemma exists_frob_inv_eq_localArtin {x} (hx : v x.1 = exp (-1)) : ∃ s : decompGroup Γ A, IsFrob A
  w.q s.1 ∧ localArtin Γ A w x = s⁻¹ := (h.exists_isCompletionEmb Γ).elim fun _ ⟨_, _, _, ⟨F⟩⟩ ↦
  ((h.isLocalArtin_localArtin F).1.exists_frob_of_isUniformiser (F.isUniformiser_iff.2 hx)).imp
  fun _ ↦ .imp_left (F.residueCard_eq ▸ F.comap_eq ▸ ·.map F.equivariant)

/-- The local Artin map sends units into inertia: for A over w and a unit x of K_w, the Artin image
of x is the class of an element of the inertia group of A. -/
lemma exists_inertia_eq_localArtin {x} (hx : v x.1 = 1) : ∃ s : decompGroup Γ A, ↑s ∈ inertiaGroup Γ
  A ∧ localArtin Γ A w x = s := (h.exists_frob_inv_eq_localArtin (v_uniformizer w)).rec fun φ H ↦
  (h.exists_frob_inv_eq_localArtin (x := x * uniformizer w) (by simpa)).imp'
  (·⁻¹ * φ) (by simp_all [← eq_div_iff_mul_eq', IsFrob.inv_mul _ H.1])

/-- For A lying over w, if s in the decomposition group acts on residues as the (N w)^n-th
power, n ≥ 0, then its class is the local Artin symbol of some x ∈ K_w^× of order −n. -/
lemma exists_localArtin_eq {q g} (hs : IsFrob A q g⁻¹) (n : ℕ) (e : q = w.q ^ n := by simp) : ∃ x,
    v x.1 = exp (-↑n) ∧ localArtin Γ A w x = ⟦⟨g, inv_mem_iff.1 hs.1⟩⟧ := by
  obtain ⟨⟨_, ⟨q⟩⟩, φ, hφ, H⟩ := h.decompGroup_spec Γ,
    h.exists_frob_inv_eq_localArtin (Γ := Γ) (v_uniformizer w)
  exact (mem_of_forall_abelianLift (H := .map _ (.map _ _)) ((isCompact_idelesUnitOff_empty.image
    (by fun_prop)).image (continuous_hom_locField_units _)).isClosed ⟦⟨_, inv_mem hs.1⟩ * φ ^ n⟧
    fun χ hχ ↦ have ⟨ψ, ⟨hψ, k⟩, _⟩ := existsUnique_unramified_char (q ▸ hφ) _
    (h.denseRange_localArtin.eq fun x ↦ (mul_mem_cancel_right (zpow_mem (by simpa [H] :
      uniformizer w ∈ ((abelianLift ψ).eqLocus _).comap _) (v x.1).log)).1
      (.trans ((h.exists_inertia_eq_localArtin (by simp [exp_neg, -inv_exp])).rec fun t a ↦ a.2 ▸ hψ
        t a.1) (hχ _ ⟨_,
      ⟨_, locIdele_mem_idelesUnitOff (by simp [exp_neg, -inv_exp]), ideleAt_locIdele ..⟩,
      rfl⟩).symm)) _ ▸
    hψ _ (hs.inv_mul (e ▸ hφ.pow n))).imp' (· * uniformizer w ^ n) (by aesop)

/-- For A lying over w, if the local Artin symbol of x is the class of g in the abelianised
decomposition group of A, then `artinAt` sends x to the class of g in the abelianisation of Γ. -/
lemma artinAt_eq_of_localArtin_eq {x} {g : decompGroup Γ A} (hg : localArtin Γ A w x = g) :
  artinAt Γ w x = g := by
  choose t e using h.exists_smul Γ w.isPlaceOver_placeOver
  rw! [artinAt, ← e, smul_eq_comap]
  exact .trans (by exact congrArg _ (.trans (congrArg _ (Units.ext (by
    simpa [finAdeleIncl] using! congr($(adeleNorm_finAdeleIncl K K (locIdele w x)) w).symm)))
    ((h.localArtin_adeleNorm
    (MulAut.conj t).toMonoidHom _ (by simp [mul_smul])).1 hg))) (mul_inv_cancel_comm ↑t _)

lemma abelianLift_artinAt χ x : abelianLift χ (artinAt Γ w x) =
  abelianLift (comap (subgroupIncl _) χ) (localArtin Γ A w x) :=
  (Quot.exists_rep _).rec fun _ e ↦ (h.artinAt_eq_of_localArtin_eq e.symm).substr (e ▸ rfl)

lemma abelianLift_artinAt_principal χ x : classOfInv _ (fixedFieldOf (decompGroup Γ A)) A
  (abelianLift χ (artinAt Γ w (ideleAt w (principalIdele x)))).toAdd = -(unitsModule Γ).resH2
  (decompGroup Γ A) (cyclicClass _ χ (DiscreteUnits.ofBase Γ Ω (.ofMul x))) :=
  (h.exists_isCompletionEmb Γ).rec fun _ ⟨_, _, _, ⟨F⟩⟩ ↦
  h.abelianLift_artinAt χ _ ▸ (h.isLocalArtin_localArtin F).2 ..

lemma abelianLift_artinAt_eq_one_iff {χ x} : abelianLift χ (artinAt Γ w
  (ideleAt w (principalIdele x))) = 1 ↔ (unitsModule Γ).resH2 (decompGroup Γ A) (cyclicClass _ χ
  (DiscreteUnits.ofBase Γ Ω (.ofMul x))) = 0 := (map_eq_zero_iff _ (h.decompGroup_spec
  Γ).1.isClassOfInv_classOfInv.1).symm.trans (h.abelianLift_artinAt_principal χ x ▸ neg_eq_zero)

open Valuation

attribute [-simp] _root_.valuation_intQpBar_lt_one_iff in
/-- Tame symbol: let π ∈ K be a uniformiser at A over w, y^(N w − 1) = π, and u a unit of K_w with
local Artin symbol s. Then for x ∈ K, u ≡ x at w iff sy/y ≡ x at A. -/
lemma localArtin_tame_symbol {π} (hπ : IsUniformiser A π) {s : decompGroup Γ A} {u} (hu :
  v u.1 = 1) (e : localArtin Γ A w u = s) {y} (hy : y ^ (w.q - 1) = algebraMap K Ω π) {x} :
  v (u.1 - algebraMap K _ x) < 1 ↔ A.valuation (s.1 • y / y - algebraMap K Ω x) < 1 := by
  obtain ⟨a, p, _, b, j, ⟨F⟩⟩ := v_algebraMap_eq_valuation π ▸ h.isUniformiser_iff.1 hπ,
    h.exists_isCompletionEmb Γ
  obtain ⟨_, hF, q, hv, rfl, d⟩ := F.2.1, (h.isLocalArtin_localArtin F).1, F.residueCard_eq,
    map_one_sub_of_lt _ (F.residueCard_eq ▸ valuation_residueCard_lt_one), F.comap_eq,
    (isEquiv_iff_valuationSubring ..).2 F.valRingBelow_eq
  refine ((((intQpBar p).valuation.ltAddSubgroup 1).add_mem_cancel_left (x := j (s.1 • y / y) - b.2
    u.1) ?_).trans d.lt_one_iff_lt_one).symm.trans (by simp [F.map_algebraMap, val_comap_lt_one])
  let ϖ := mk0 _ (ne_zero_of_map (a ▸ exp_ne_zero))
  apply_fun j at hy
  cases' _ : w.q with n <;> simp_all [F.map_algebraMap]
  obtain ⟨⟨_, n0⟩, φ, ⟨hφ⟩⟩ := ne_zero_of_tame_root (π := ϖ) hv hy,
    hF.exists_frob_of_isUniformiser (π := ϖ) (F.isUniformiser_iff.2 a)
  have e : ∀ g, cycCharMod _ n g = 1 := (F.frobenius_spec.2.1 hφ).eq
    (by simp_all [cycCharMod_of_mem_inertiaGroup _ hv, hφ.cycCharMod_eq,
    ← val_inj]) (.of_isOpen_ker _ isOpen_ker_cycCharMod.1)
  choose a f ha hf using
    (exists_kummer_cocycle e <| DiscreteUnits.ofBase (K := LocField w) _ _ <| .ofMul ·)
  have := (kummer_cup_eq_neg_cyclicClass (ha u) (f ϖ) _ ?_).symm.trans ((cupProduct_flip (W :=
    unitsModule _) (M := .of (.trivial ..)) (.compr₂ .mul (rootPowHom _ n).1) ?_ (f ϖ) (f u)).trans
    (neg_inj.2 (kummer_cup_eq_neg_cyclicClass (ha ϖ) (f u) _ ?_)))
  all_goals simp_all [← map_cycCharMod_mul, ← hf _ _ (ha _), ← map_nsmul, mul_comm, ← hF _,
    DiscreteUnits.ext_iff,
    F.isClassOfInv_classOfInv.1.eq_iff, QZ.ofZMod_injective.eq_iff, -Subtype.forall]
  simp [← d.eq_one_iff_eq_one, ← ha, n0.1] at hu
  erw [F.equivariant, ← hf ϖ (.mk0 _ (by simpa)) hy, this, hf _ _ (ha _)]
  simpa [div_sub', pow_succ', *] using hφ.2 _ hu.le

end IsPlaceOver

namespace IsPlaceOver

open Valuation

variable {A : ClosurePlace} (h : IsPlaceOver A w) [IsGalois K Ω]

include h

/-- A tame generator exists: for A over w, some γ in the inertia group has, for every n prime to w,
a uniformiser π ∈ K and y with yⁿ = π and γy/y a primitive n-th root of unity. -/
lemma exists_tameGenerator : ∃ γ : inertiaGroup Gal(Ω/K) A, ∀ n : ℕ, A.valuation n = 1 → ∃ π : Kˣ,
  ∃ y, IsUniformiser A π.1 ∧ y ^ n = algebraMap K Ω π ∧ IsPrimitiveRoot (γ • y / y) n := by
  obtain ⟨⟨G⟩, π, a, u⟩ := h.decompGroup_spec Gal(Ω/K), h.exists_uniformiser Gal(Ω/K)
  choose y O using fun n : {n : ℕ // A n = 1} ↦ (@IsAIC.exists_pow_eq _ _ _ _ ⟨by aesop⟩
    (algebraMap K Ω π)).imp fun _ h ↦ And.intro h (ne_zero_of_tame_root n.2 h)
  exact (isClosed_inertiaGroup.isCompact.inter_iInter_nonempty _ (fun n ↦ isClosed_setOf_smul (y n)
    ((IsPrimitiveRoot · n) ∘ (· / y n))) fun T ↦ (O ⟨T.prod (↑), by simp_all [T.prod_eq_one]⟩).rec
    fun Y ⟨_, n⟩ ↦ HasEnoughRootsOfUnity.prim.rec fun ζ hζ ↦ (G.exists_inertia_smul_eq_of_pow_eq u
    n.pos Y ((mul_pow ζ ..).trans (hζ.1 ▸ one_mul _))).rec fun s ⟨e, _⟩ ↦ ⟨s,
    e, by simp_all [fun p h ↦ show s.1 _ = _ from smul_root_eq_ratio_mul e p.2 (by rwa [← pow_mul,
    T.prod_erase_mul _ h]) (O p).1, mul_pow, hζ.pow n.pos, T.prod_erase_mul]⟩).elim fun g ⟨H, _⟩ ↦
    ⟨⟨g, H⟩, (⟨π, y ⟨·, ·⟩, by simp_all [h.isUniformiser_iff]⟩)⟩

/-- A chosen generator of tame inertia at the place A above w, as an element of the inertia
group. -/
noncomputable def tameGenerator := h.exists_tameGenerator.choose

/-- Let n be prime to w and f a homomorphism on Gal(Ω/K), trivial near 1 in inertia, with fⁿ = 1 on
inertia. For s in inertia, f(s) is a power of f at the chosen tame generator, and f(φsφ⁻¹) = f(s)^q
for a q-Frobenius φ. -/
lemma tame_inertia {P} [Monoid P] (f : Gal(Ω/K) →* P) (hf : ∀ᶠ g in nhds 1, g ∈ inertiaGroup _ A →
  f g = 1) {n : ℕ} (hn : A.valuation n = 1) (hP : ∀ g ∈ inertiaGroup _ A, f g ^ n = 1) (s :
  inertiaGroup Gal(Ω/K) A) : (∃ i, f s = f h.tameGenerator ^ i) ∧ ∀ q φ, IsFrob A q φ →
  f (φ * s * φ⁻¹) = f s ^ q := (h.exists_tameGenerator.choose_spec n hn).rec fun π ⟨y, u, e,
  p⟩ ↦ have H (g : inertiaGroup ..) := ((h.decompGroup_spec _).1.tame_inertia ((h.decompGroup_spec
    _).2.2 u) hn e ((f.domRestrict _).domRestrict _) (isOpen_of_mem_nhds _ ((nhds _).3
  (continuous_subtype_val.subtype_val.tendsto 1 hf) (by aesop_cat))) (by bound)).2 ⟨⟨_, g.2.1⟩, g.2⟩
  ⟨(H _).1 p ⟨⟨_, s.2.1⟩, s.2⟩, fun q φ a ↦ ((H s).2 q ⟨φ, a.1⟩ a).2⟩

/-- For A above w, there is a unit u of K_w whose local Artin image is the class of the chosen tame
generator of inertia and whose residue generates the multiplicative group of the residue field. -/
lemma exists_localArtin_eq_tameGenerator : ∃ u a, localArtin _ A w u = ⟦⟨_, h.tameGenerator.2.1⟩⟧ ∧
  (∀ z, z ∈ zpowers ((LocInt w).unitGroupToResidueFieldUnits ⟨u, a⟩)) ∧ v u.1 = 1 := by
  have ⟨g, hg, e⟩ := h.exists_localArtin_eq (inv_mem h.tameGenerator.2) 0
  have ⟨π, y, u, Y, p⟩ := h.exists_tameGenerator.choose_spec (w.q - 1) ?N
  use g, (mem_unitGroup_iff ..).2 hg, e, (eq_top_iff' _).1 (eq_top_of_le_card _ (by
    erw [Nat.card_zpowers, Nat.card_units, card_ResField]
    exact let r := _; Nat.le_of_dvd (orderOf_pos r) (p.2 _ ((eq_of_val_sub_lt_one ?N (by rw
        [pow_right_comm, p.1, one_pow]) (by simp [exp_neg, -inv_exp])
        (inertia_pow_smul_div h.tameGenerator.2 ?N Y _ ▸ (h.localArtin_tame_symbol u
      (by aesop) (e ▸ map_pow ..) Y).1 (residue_eq_iff_valuation_sub_lt_one.1 (val_inj.2
      (pow_orderOf_eq_one r))))).trans (map_one _))))), hg
  simp [map_sub_eq_of_lt_right, h.valuation_q_lt_one]
