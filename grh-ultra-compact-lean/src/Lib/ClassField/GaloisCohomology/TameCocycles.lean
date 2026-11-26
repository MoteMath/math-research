import Lib.ClassField.GreenbergWiles.SelmerMembership
open Equiv.Perm Matrix Module MulAction LinearMap
variable {ℓ E O n} [Field E] [EmbeddedNumberField E] [CommRing O] [Fintype n] {ρ : Gal(Ω/E) →*
  Matrix n n O} {L} {A : ClosurePlace} {B} [AddCommGroup B] [Module O B] {M} (hB : ∀ b : B,
  ℓ ^ M • b = 0) {P : FinPlace E} (hA : IsPlaceOver A P) {c : _ → n → B} (hc : ∀ g h, c (g * h) =
  c g + ρ g • c h) {m} (hm : ∀ i ∈ inertiaGroup _ A, ρ (i ^ m) = 1) (ho : ∀ᶠ g in nhds 1, g ∈
  inertiaGroup _ A → ρ g = 1) (γ : inertiaGroup Gal(Ω/E) A) (hq : A.valuation (m * ℓ ^ M : ℕ) = 1)
variable (ρ L A B) in
noncomputable def localCocycles :=
  (selmerModule ρ .univ L B).map (funLeft O _ (decompGroup _ A).subtype)
attribute [local simp] Equiv.ext_iff Units.smul_def coe_pow
noncomputable def affineAction := MonoidHom.mk' (fun g ↦
  .addLeft (c g) * toPerm (ρ.toHomUnits g)) (by simp [*, mul_smul, add_assoc])
include hc in
lemma cocycle_apply_inv g :
  c g⁻¹ = -(ρ g⁻¹ • c g) := by simpa [eq_neg_iff_add_eq_zero, ← hc] using hc 1 1
include hA hB hm ho hq
lemma tame_affineAction (hl : IsLocallyConstant c) : (c hA.tameGenerator = 0 → c γ = 0) ∧ ∀ ⦃k⦄,
  k ≡ 1 [MOD m * ℓ ^ M] → ∀ φ, IsFrob A k φ → Commute (affineAction hc φ) (affineAction hc γ) :=
  (fun K ↦ (hA.tame_inertia (affineAction hc) ((hl.eventually_eq 1).mp
  (ho.mono (by simp_all [← (affineAction hc).map_one, affineAction]))) hq K γ).imp
  (fun ⟨a, H⟩ z ↦ by simpa [affineAction, z, Function.iterate_fixed] using congr($H 0)) fun F k
  e ↦ by simpa [pow_eq_pow_of_modEq e, K, mul_inv_eq_iff_eq_mul, commute_iff_eq] using F k)
  (by simp_all [↓pow_mul, ↓← map_pow, affineAction, Function.comp_def, funext_iff])
lemma length_localCocycles_le : length O (localCocycles ρ L A B) ≤ length O (n →
  B) + length O (ker ((ρ γ - 1) • 1 : End O (n → B))) := (hA.exists_isFrob _).rec fun φ hφ ↦ by
  grw [← relLength_add_length_inf _ (proj ⟨_, hA.tameGenerator.2.1⟩).ker, relLength_ker,
    length_mono le_top, length_top, ← relLength_bot, relLength_le_of_inj (proj ⟨φ, hφ.1⟩),
    relLength_bot] <;> rintro _ ⟨⟨y, Y, rfl⟩, h⟩ <;> have C := (mem_selmerModule_iff.1
    Y).1 <;> have Z := (tame_affineAction hB hA C hm ho ⟨·, ·⟩ hq Y.2 |>.1 h)
  exacts [by simpa [*, sub_smul] using (Z _ (.inv_mul (by simpa) (γ.2.mul_iff.2 hφ)) ▸ C φ _ :),
    funext ∘ (hA.decompGroup_le hφ (U := cocycleKer _ C) (Y.2 {0}) Z · ·.2)]
omit hm ho hq
lemma exists_conj_side_detects [NumberField.IsCMField E] {γ} (t : ↑hA.tameGenerator = γ) {v} (l :
  P ∉ placesDividing E ℓ) (u : ∀ g ∈ inertiaAbove {v}, ρ g = 1) (hv : v = P ∨ v = star P) : ∃ b A',
  IsPlaceOver (Ω := Ω) A' v ∧ ∀ {S L}, ∀ c ∈
  selmerModule ρ S L B, c (idOrConjInv b γ) = 0 → (∀ g ∈ inertiaAbove {v}, c g = 0) ∧ ∀ φ,
  IsFrob A P.q φ → c (idOrConjInv b φ) = 0 → ∀ g : decompGroup _ A', c g.1 = 0 := by
  have T θ {c} C u j g := (tame_affineAction hB hA (ρ := ρ.comp θ) (c := c) C (m := 1) (by simpa)
    (.of_forall u) g (by simp [hA.valuation_natCast_eq_one_iff.2 l]) j).1
  simp_rw [mem_selmerModule_iff, ← t]
  obtain rfl | ⟨hA, rfl⟩ := hv.imp_right (And.intro hA.conjPlace_star) <;> refine ⟨?_, _, hA,
    fun c ⟨C, _, _, j⟩ z ↦ (fun H ↦ ⟨fun g ⟨_, rfl, _, b, i⟩ ↦ (b.exists_smul _ hA).rec fun s k ↦ by
    simpa [*, mul_assoc] using (H (k ▸ i.conj s) ▸ C s⁻¹ _ :), fun φ f k ↦
    (hA.decompGroup_le ?_ (j {0}) H (?_ : ?_ ∈ cocycleKer _ C) ·.2)⟩) ?_⟩
  exacts [true, (T (.id _) C (u · ⟨_, rfl, _, hA, ·⟩) j ⟨·, ·⟩ z), f, k, false, (conjGal_conjGal · ▸
    T conjGal (by simp [C]) (fun _ ↦ (u _ ⟨_, rfl, _, hA, ·.conjPlace_conjGal⟩))
    (j.comp_continuous (by fun_prop)) ⟨_, @conjPlace_conjPlace A ▸ ·.conjPlace_conjGal⟩
    ((cocycleKer _ C).inv_mem z)), by simpa using f.conjPlace_conjGal, inv_mem_iff.1 k]
