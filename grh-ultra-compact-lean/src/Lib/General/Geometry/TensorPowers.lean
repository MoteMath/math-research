import Lib.General.Geometry.ReducedClosure
section
open CategoryTheory AlgebraicGeometry TopologicalSpace.Opens Scheme TopCat.Presheaf Hom Spec Limits.pullback EffectiveEpi Category IsLocalRing IsOpenImmersion
variable {X Y κ U A B x} {f g : PointFn X} {t : Spec A ⟶ X} {V : κ → X.Opens} (hU : IsAffineOpen U) (p : Y ⟶ X) (s : Γ(X, U)) (hf : f.IsRegularOn U) (hg : g.IsRegularOn U) (M : LineBundle Y κ) {z : Spec B ⟶ X} [IsLocalRing B]
lemma LandsIn.mono {t V} : @LandsIn X Y t U → U ≤ V → LandsIn t V := by tauto
lemma landsIn_iff_mem : LandsIn z U ↔ z (closedPoint B) ∈ U := top_le_iff.trans closed_point_mem_iff.symm
lemma LineBundle.exists_landsIn t : ∃ i, @LandsIn Y (Spec B) t (M.opens i) := by simp [landsIn_iff_mem, ← mem_iSup, M.3]
lemma landsIn_fromSpec t : @LandsIn X Y (t ≫ hU.fromSpec) U := by aesop_cat
lemma landsIn_opensRange {R c} [@IsOpenImmersion (Spec R) X c] : LandsIn t c.opensRange ↔ ∃ φ, map φ ≫ c = t := ⟨fun h ↦ ⟨preimage (lift c t (by aesop)), by simp⟩, by aesop_cat⟩
lemma landsIn_comp_incl {t} : @LandsIn X Y (t ≫ U.ι) U := by aesop_cat
lemma landsIn_iInf [Finite κ] : LandsIn p (iInf V) ↔ ∀ a, LandsIn p (V a) := by simp [LandsIn, ← coe_inj, coe_iInf]
lemma hom_ext_of_cover {f g : Y ⟶ X} (h : ∀ i A t, @LandsIn Y (Spec A) t (M.opens i) → t ≫ f = t ≫ g) : f = g := (Y.openCoverOfIsOpenCover _ M.3).affineRefinement.openCover.hom_ext _ _ fun _ ↦
 h _ _ _ landsIn_comp_incl
lemma exists_hom_of_cover (F : ∀ i _ t, LandsIn t (M.opens i) → (_ ⟶ X)) (h : ∀ i j A B φ t hi hj, F j B (@map A B φ ≫ t) hj = map φ ≫ F i A t hi) : ∃ f, ∀ i A t hi, t ≫ f = F i A t hi :=
 have K {i j A B t s} hi hj : fst t s ≫ F i A t hi = snd .. ≫ F j B s hj := hom_ext_of_cover .one (by simp_all [homEquiv.surjective.forall]; grind [LandsIn.comp, condition, =_ h _ j])
 ⟨_, fun _ _ t _ ↦ Cover.hom_ext (.pullback₁ t _) _ _ fun _ ↦ by
  erw [condition_assoc, (Y.openCoverOfIsOpenCover _ M.3).affineRefinement.openCover.ι_glueMorphisms _ fun _ _ ↦ K landsIn_comp_incl _, K]; rfl⟩
lemma le_of_cover {U W} (h : ∀ i A t, @LandsIn Y (Spec A) t (M.opens i) → LandsIn t U → LandsIn t W) : U ≤ W := fun x ↦ (M.exists_landsIn (fromSpecStalk ..)).rec (by simpa [landsIn_iff_mem] using h · _ _ ·)
instance [EffectiveEpi p] [QuasiCompact p] : IsSchemeTheoreticallyDominant p := ⟨by simpa using @ker_eq_bot_of_isIso _ _ _ (ExtremalEpi.isIso _ _ _ p.toImage_imageι)⟩
namespace PointFn
lemma ofSection_eq h s : @ofSection X U s A t = evalSection t h s := dite_eq_left h
lemma ofSection_appLE {W} e s (h : LandsIn x W) : ofSection (p.appLE U W e s) A x = ofSection s A (x ≫ p) := by rw [ofSection_eq, ofSection_eq, evalSection, evalSection, ← appLE_comp_appLE] <;> tauto
lemma isRegularOn_ofSection : (ofSection s).IsRegularOn U := by (repeat intro); erw [← ofSection_appLE, ofSection_eq, evalSection, ΓSpecIso_naturality, ofSection_eq] <;> tauto
lemma ofSection_map {V} i : LandsIn t V → @ofSection X V (X.presheaf.map i s) A t = ofSection s A t := ofSection_appLE (𝟙 X) _ s
lemma landsIn_fromSpecStalk : x ∈ U → LandsIn (X.fromSpecStalk x) U := by simp [landsIn_iff_mem]
lemma map_evalSection_fromSpec h : map (evalSection t h) ≫ hU.fromSpec = t := by simp [evalSection, hU.SpecMap_appLE_fromSpec t (isAffineOpen_top _) h, IsAffineOpen.fromSpec_top]
include hU in lemma point_eq_of_ofSection_eq (h : LandsIn t U) (k : LandsIn x U) (e : ∀ s, @ofSection X U s A t = ofSection s A x) : t = x := map_evalSection_fromSpec hU h ▸ map_evalSection_fromSpec hU k ▸ by congr 2 with; simp [← ofSection_eq, e]
@[simp] lemma ofSection_map_fromSpec φ : ofSection s A (map φ ≫ hU.fromSpec) = φ s := by rw [ofSection_eq, map_injective ((cancel_mono _).1 (map_evalSection_fromSpec ..))]; aesop_cat
lemma ofSection_fromSpecStalk hx s : ofSection s _ (X.fromSpecStalk x) = X.presheaf.germ U x hx s := by erw [ofSection_eq (landsIn_fromSpecStalk hx), evalSection, appLE, fromSpecStalk_app, (ΓSpecIso _).inv_hom_id_apply] <;> tauto
lemma landsIn_basicOpen (h : LandsIn t U) s : LandsIn t (X.basicOpen s) ↔ IsUnit (@ofSection X U s A t) := by
 rw [LandsIn, ← inf_eq_left, ← basicOpen_appLE, ofSection_eq h]
 simpa using! PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := ![_])
lemma ofSection_appTop c A t : ofSection (p.appTop c) A t = ofSection c A (t ≫ p) := rfl
lemma exists_ofSection_glue [Flat p] [Surjective p] [QuasiCompact p] (f : _ → _) (hf : ∀ a, IsRegularOn (f a) (p ⁻¹ᵁ U ⊓ M.opens a)) (h : ∀ a b A t s, t ≫ p = s ≫ p → LandsIn (t ≫ p) U → LandsIn t (M.opens a) → LandsIn s (M.opens b) → f a A t = f b A s) : ∃ s, ∀ a A t, LandsIn (t ≫ p) U → LandsIn t (M.opens a) → @ofSection X U s A (t ≫ p) = f a A t := (exists_hom_of_cover (M.pull (fst ..)) (fun a A t _ ↦ specMap (FreeCommRing.lift ![f a A (t ≫ fst ..)])) (by simp_rw [← map_comp]; congr!; ext; simp; rw [← hf, h] <;> simp_all [LandsIn.comp, condition, landsIn_comp_incl])).elim fun q e ↦ ⟨inv (appLE ..) (appTop (desc (snd p U.ι) q fun a b E ↦ hom_ext_of_cover ((M.pull (a ≫ fst ..)).mul (M.pull (b ≫ fst ..))) (by simp_all [← assoc]; grind [condition, landsIn_comp_incl])) ((ΓSpecIso _).2 (.of 0))), fun a A t _ _ ↦ by erw [← lift_fac U.ι (t ≫ p) (by aesop), ← ofSection_appLE, IsIso.inv_hom_id_apply, ofSection_appTop, ← lift_snd_assoc (f := p) t, fac, e a, ofSection_eq, evalSection, ΓSpecIso_naturality] <;> simp [*]⟩
include hf
namespace IsRegularOn
lemma exists_ofSection : ∃ s, ∀ A t, LandsIn t U → @ofSection X U s A t = f A t := by simpa using exists_ofSection_glue (𝟙 X) .one (fun _ ↦ f) (by simpa [IsRegularOn])
lemma pull : (f.pull p).IsRegularOn (p ⁻¹ᵁ U) := by aesop_cat
lemma mono {V} : V ≤ U → f.IsRegularOn V := by aesop_cat
lemma mul {V} : g.IsRegularOn V → (f * g).IsRegularOn (U ⊓ V) := by simp_all [IsRegularOn]
include hg
lemma ext_of_dominant [IsSchemeTheoreticallyDominant p] [QuasiCompact p] (h : ∀ a A t, LandsIn (t ≫ p) U → LandsIn t (M.opens a) → f A (t ≫ p) = g A (t ≫ p)) A t : LandsIn t U → f A t = g A t := by grind [(p.app_injective _ (section_ext Y.sheaf _ _ _ fun x k ↦ have := landsIn_fromSpecStalk k; by (repeat erw [← ofSection_fromSpecStalk]); simp_all [app_eq_appLE, ofSection_appLE]; grind [M.exists_landsIn (Y.fromSpecStalk x)]) : hf.exists_ofSection.choose = hg.exists_ofSection.choose)]
end IsRegularOn
end PointFn
end
section
open Int Localization Quotient AlgebraicGeometry CategoryTheory CommRingCat Finset PointFn HomogeneousLocalization LandsIn IsLocalization LineBundle MvPolynomial Ring Proj CategoryTheory.Limits MorphismProperty Limits.prod
section
attribute [local grind! .] isRegularOn_ofSection regular LineBundle.transition_trans landsIn_inf
attribute [local simp] IsRegularOn IsFrame IsSection
variable {X Y Z ι κ A} {L : LineBundle X ι} {M : LineBundle X κ} {u s} (hu : L.IsFrame u) (hs : L.IsSection s) (K : LineBundle X ι) (p π : Y ⟶ X) (q : Z ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π] {i j : ι}
lemma LineBundle.isUnit_transition {t} : LandsIn t (K.opens i) → LandsIn t (K.opens j) → IsUnit (K.transition i j A t) := by grind [K.5, → K.6]
@[simp] lemma LineBundle.pull_comp : K.pull (q ≫ p) = (K.pull p).pull q := rfl
@[simp] lemma LineBundle.pull_id : K.pull (𝟙 X) = K := rfl
lemma LineBundle.exists_section_mul {u} (hu : ((M.mul L.inv).pull π).IsSection u) (hs : L.IsSection s) (H : ∀ i B t s, t ≫ π = s ≫ π → LandsIn (t ≫ π) ((M.mul L.inv).opens i) → u i B t = u i B s := by simp) : ∃ r, (M.IsSection r ∧ ∀ i A t, ¬LandsIn t (M.opens i) → r i A t = 0) ∧ (∀ i a A t, LandsIn (t ≫ π) (M.opens i) → LandsIn (t ≫ π) (L.opens a) → r i A (t ≫ π) = u (i, a) A t * s a A (t ≫ π)) ∧ (((M.mul L.inv).pull π).IsFrame u → L.IsFrame s → M.IsFrame r) :=
 (Classical.skolem.1 fun i ↦ exists_ofSection_glue π (L.pull π) (u.curry i * PointFn.pull π ∘ s) (by simp_all) (by simp_all; grind)).imp' (ofSection <| · ·) fun r K ↦
 (fun e ↦ ⟨⟨e, fun _ _ _ ↦ (dite_eq_right ·)⟩, K, fun _ _ ↦ ⟨e, fun i _ _ h ↦ (landsIn_basicOpen h _).1 (h.mono (π.surjective.forall.2 (le_of_cover (L.pull π) (by simp_all [↓landsIn_preimage]; grind
 [landsIn_basicOpen]) : π ⁻¹ᵁ _ ≤ π ⁻¹ᵁ X.basicOpen _)))⟩⟩) ⟨by grind, by
 intros; apply (((isRegularOn_ofSection _).mono _).ext_of_dominant π ((regular ..).mul (isRegularOn_ofSection _)) (L.pull π)) <;> simp_all [inf_assoc]; grind⟩
lemma LineBundle.exists_isFrame_of_fpqc {u} (hu : (L.pull π).IsFrame u) (H : ∀ i B t s, t ≫ π = s ≫ π → LandsIn (t ≫ π) (L.opens i) → u i B t = u i B s) : ∃ s, L.IsFrame s := by apply (@exists_section_mul _ _ _ _ one _ 1 π _ _ _ (u ·.1) ..).imp fun _ e ↦ e.2.2 ?_ ?_ <;> aesop
lemma LineBundle.IsIsomorphic.refl : K.IsIsomorphic K := ⟨K.transition.uncurry, by simp; grind [isUnit_transition, IsRegularOn]⟩
lemma LineBundle.IsIsomorphic.exists_isFrame : L.IsIsomorphic M → Exists M.IsFrame → Exists L.IsFrame | ⟨_, h⟩, ⟨_, k⟩ => (exists_section_mul (𝟙 _) h.1 k.1).imp (by tauto)
lemma LineBundle.IsIsomorphic.mul {μ ν N P} : L.IsIsomorphic M → @IsIsomorphic X μ ν N P → (L.mul N).IsIsomorphic (M.mul P)
 | ⟨u, _⟩, ⟨v, _⟩ => ⟨fun ((a, b), c, d) ↦ u (a, c) * v (b, d), by simp_all; grind⟩
lemma LineBundle.IsSection.pull (hs : L.IsSection s) (p : Y ⟶ X) : (L.pull p).IsSection (s · |>.pull p) := by aesop
namespace LineBundle.IsFrame
include hu
lemma pull : (L.pull p).IsFrame (u · |>.pull p) := by aesop
lemma inv : L.inv.IsFrame (inverse <| u · · ·) := by simp_all; grind
lemma mul {v} : M.IsFrame v → (L.mul M).IsFrame fun i ↦ u i.1 * v i.2 := by simp_all; grind
include hs
lemma exists_eq_mul : ∃ c, ∀ i A t, LandsIn t (L.opens i) → s i A t = (@ofSection X ⊤ c * u i) A t := by apply (exists_ofSection_glue (𝟙 _) L ((inverse <| u · · ·) * s) ..).imp <;> simp_all <;> grind
end LineBundle.IsFrame
def Pic X := @Quotient (Sigma (LineBundle X)) ⟨(·.2.IsIsomorphic ·.2), (.refl ·.2), (flip LineBundle.IsIsomorphic.exists_isFrame (LineBundle.IsIsomorphic.refl _) <| (LineBundle.IsIsomorphic.refl _).mul ⟨_, ·.choose_spec.inv⟩), (·.mul (.refl _) |>.exists_isFrame)⟩
def LineBundle.picClass : Pic X := ⟦⟨ι, K⟩⟧
lemma LineBundle.picClass_eq_of_le (e : κ → ι) (hU : ∀ a, M.opens a ≤ L.opens (e a)) (h : ∀ a b A t, LandsIn t (M.opens a) → M.transition a b A t = L.transition (e a) (e b) A t) : L.picClass = M.picClass := sound ((IsIsomorphic.refl L).imp' (· ∘ .map id e) (by simp; grind [mono]))
instance : AddCommGroup (Pic X) := by apply @AddCommGroup.mk _ (@.ofRightAxioms _ ⟨.map₂ (⟨_,
 ·.2.mul ·.2⟩) fun _ _ h _ _ ↦ h.mul⟩ ⟨.map (⟨_, ·.2.inv⟩) fun _ _ ⟨_, h⟩ ↦ ⟨_, h.inv⟩⟩ ⟨one.picClass⟩ ..) <;> (repeat rintro ⟨_, _⟩) <;> (first
 | apply picClass_eq_of_le (by simp; bound) | refine sound ((LineBundle.IsIsomorphic.refl ‹_›).imp' (· ∘ .fst) ?_)) <;> simp [inf_assoc] <;> grind
lemma LineBundle.picClass_eq_iff : L.picClass = M.picClass ↔ L.IsIsomorphic M := eq
@[simp] lemma LineBundle.picClass_mul : (L.mul M).picClass = L.picClass + M.picClass := rfl
lemma LineBundle.exists_isFrame_of_picClass_eq_zero : L.picClass = 0 → Exists L.IsFrame := (exact · |>.exists_isFrame ⟨1, by simp⟩)
noncomputable def Pic.pull : Pic X →+ Pic Y := .mk' (.map (⟨_, ·.2.pull p⟩) fun _ _ ⟨_, h⟩ ↦ ⟨_, h.pull p⟩) (by rintro ⟨⟩ ⟨⟩; rfl)
@[simp] lemma Pic.pull_picClass : pull p K.picClass = (K.pull p).picClass := rfl
lemma Pic.pull_comp c : pull (q ≫ p) c = pull q (pull p c) := c.out_eq ▸ rfl
@[simp] lemma Pic.pull_id c : pull (𝟙 X) c = c := c.out_eq ▸ rfl
lemma Pic.eq_zero_of_isLocalRing (c : Pic (Spec A)) [IsLocalRing A] : c = 0 := c.ind' fun _ ↦
  (exists_landsIn _ (𝟙 _)).elim fun i h ↦
 picClass_eq_of_le _ (by tauto) (by simp [transition_self _ _ _ _ (mono _ h)])
end
lemma eval₂_mul_of_isHomogeneous {σ R S} [CommRing R] [CommRing S] {n a} (h : @IsHomogeneous σ R _ a n) f (c : S) v : eval₂ f (c * v ·) a = c ^ n * eval₂ f v a := by simp +contextual [eval₂_eq, mul_sum, mul_pow, mul_left_comm, prod_pow_eq_pow_sum, ← h.degree_eq_sum_deg_support]
lemma ProjSpace.X_mem_homogeneousSubmodule {ι : Type} (i : ι) : .X i ∈ homogeneousSubmodule ι ℤ 1 := isHomogeneous_X ..
attribute [local instance] gradedAlgebra
noncomputable abbrev ProjSpace ι := Proj (homogeneousSubmodule.{0} ι ℤ)
variable {X ι A} (L : LineBundle X ι) (t : Spec A ⟶ X) (v : ι → A) (i j : ι) {L' M : LineBundle X ι}
noncomputable abbrev ProjSpace.coordRatio := ofSection (awayToSection _ _ (.isLocalizationElem (X_mem_homogeneousSubmodule i) (X_mem_homogeneousSubmodule j)))
@[simp] lemma ProjSpace.coordRatio_mul (k : ι) t (h : LandsIn t (basicOpen _ (.X i) ⊓ basicOpen _ (.X j))) : coordRatio i j A t * coordRatio j k A t = coordRatio i k A t := by simpa [← ofSection_map _ ⟨⟨⟨_⟩⟩⟩ h, ↓ofSection_eq h, ← map_mul] using congrArg _ (Subtype.ext (by ext; exact mk_eq_mk_iff.2 (r_of_eq (by simp [mul_assoc]))))
noncomputable def ProjSpace.hyperplaneBundle ι : LineBundle (ProjSpace ι) ι :=
 .mk _ coordRatio (iSup_basicOpen_eq_top' _ _ (⟨1, X_mem_homogeneousSubmodule ·⟩) (by rw [← Algebra.adjoin_adjoin_of_tower ℤ]; simp)) (by simp [(isRegularOn_ofSection _).mono])
 fun i ↦ by simp_all [ofSection_eq, (by aesop :
 Away.isLocalizationElem (X_mem_homogeneousSubmodule i) (X_mem_homogeneousSubmodule i) = 1)]
lemma ProjSpace.isAffineOpen_chart : IsAffineOpen ((hyperplaneBundle ι).opens i) := isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule i) .refl
def LineBundle.IsHomogCoords := ∀ j, (LandsIn t (L.opens j) ↔ IsUnit (v j)) ∧ ∀ k, IsUnit (v j) → L.transition j k A t = v k * (v j)⁻¹ʳ
def LineBundle.IsLinearSystem := (∀ i j, (L.transition i j).IsRegularOn (L.opens i) ∧ ∀ A t, ¬LandsIn t (L.opens i) → L.transition i j A t = 0) ∧ ∀ {i A t}, LandsIn t (L.opens i) → L.IsHomogCoords t (L.transition i · A t)
lemma ProjSpace.isLinearSystem_hyperplaneBundle : (hyperplaneBundle ι).IsLinearSystem :=
 ⟨fun _ _ ↦ ⟨isRegularOn_ofSection _, fun _ _ ↦ (dite_eq_right ·)⟩, fun {i _ _} h _ ↦ (⟨·, by simp_all [hyperplaneBundle, eq_mul_inverse_iff_mul_eq, mul_comm _ (coordRatio i ..)]⟩) ⟨isUnit_transition _ h, fun u _ hx ↦ by simpa using!
 ((ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply _ ⟨_, h hx⟩ _).2.mt ((((hyperplaneBundle
 ι).opens i).toSpecΓ_preimage_basicOpen _).ge ((landsIn_basicOpen h _).2 u hx)))⟩⟩
attribute [local simp, local grind] IsRegularOn LandsIn.comp IsLinearSystem IsSection IsHomogCoords
namespace LineBundle.IsLinearSystem
lemma ext_of_transition_eq_mul (h : L'.IsLinearSystem) (hM : M.IsLinearSystem) (H : ∀ i j k A t, LandsIn t (L'.opens i) → LandsIn t (M.opens j) → M.transition j k A t = M.transition j i A t * L'.transition i k A t) : M = L' := (LineBundle.ext · (by grind)) (by ext1; apply le_antisymm <;> grind [le_of_cover L', le_of_cover M])
lemma isSection (h : M.IsLinearSystem) : M.IsSection (M.transition · j) := by grind
variable {Y} {ι : Type} {A : CommRingCat} {L : LineBundle X ι} {v : ι → A} {p : Y ⟶ X} (p : Y ⟶ X)
lemma pull (h : L.IsLinearSystem) : (L.pull p).IsLinearSystem := by simp; grind
variable {κ} {A : CommRingCat} {L : LineBundle X ι} {N : LineBundle X κ} {t : Spec A ⟶ X} {v : ι → A} {S} {s : X ⟶ S} (p : Y ⟶ X)
lemma mul (h : L.IsLinearSystem) : N.IsLinearSystem → (L.mul N).IsLinearSystem := by simp; grind
end LineBundle.IsLinearSystem
variable {Y} {ι : Type} {κ} {A : CommRingCat} {L : LineBundle X ι} {N : LineBundle X κ} {t : Spec A ⟶ X} {v : ι → A} {S} {s : X ⟶ S} (p : Y ⟶ X)
namespace LineBundle.IsHomogCoords
lemma pull_iff {p : Y ⟶ X} {t} : (L.pull p).IsHomogCoords t v ↔ L.IsHomogCoords (t ≫ p) v := .rfl
lemma smul (l : L.IsHomogCoords t v) {u : A} : IsUnit u → L.IsHomogCoords t (u • v) := by simp; grind
lemma map {i : ι} {L : LineBundle X ι} {t : Spec A ⟶ X} {v : ι → A} (l : L.IsHomogCoords t v) {R} : L.IsLinearSystem → IsUnit (v i) → ∀ φ, L.IsHomogCoords (@Spec.map A R φ ≫ t) (φ ∘ v) := by grind
lemma mul (l : L.IsHomogCoords t v) {w} : N.IsHomogCoords t w → (L.mul N).IsHomogCoords t fun i ↦ v i.1 * w i.2 := by simp; grind
lemma ne_zero (l : L.IsHomogCoords t v) [IsLocalRing A] : ∃ i, v i ≠ 0 := (L.exists_landsIn t).imp (by aesop)
end LineBundle.IsHomogCoords
lemma ProjSpace.exists_isHomogCoords {S : Scheme} {ι : Type} {A : CommRingCat} {i : ι} {v : ι → A} (b : _ ⟶ S) (h : IsUnit (v i)) : ∃ s, s ≫ snd = b ∧ ((hyperplaneBundle ι).pull fst).IsHomogCoords s v := ⟨_, lift_snd .., by
 rw [IsHomogCoords.pull_iff, lift_fst]; convert! (isLinearSystem_hyperplaneBundle.2 (landsIn_fromSpec (isAffineOpen_chart i) (Spec.map ((basicOpenIsoAway _ _ (X_mem_homogeneousSubmodule i) .refl).2 ≫ ofHom ((awayLift (eval₂Hom (castRingHom _) v) (X i) (by simpa)).comp (algebraMap ..)))))).smul h; ext; dsimp [hyperplaneBundle, coordRatio]; erw [ofSection_map_fromSpec, comp_apply, Iso.hom_inv_id_apply, awayLift_mk (v := h.unit.2), mul_left_comm] <;> simp⟩
def LineBundle.IsProjEmbedding {S ι} L (s : X ⟶ S) := IsLinearSystem L ∧ IsProper s ∧ ∀ {i : ι} {A a b}, (LandsIn a (L.opens i) ∧ LandsIn b (L.opens i) ∧ ∀ j, L.transition i j A a = L.transition i j A b) → a ≫ s = b ≫ s → a = b
lemma LineBundle.IsProjEmbedding.eq_of_isHomogCoords {a} (h : L.IsProjEmbedding s) (o : a ≫ s = t ≫ s) (x : L.IsHomogCoords a v) (y : L.IsHomogCoords t v) (u : ∃ i, LandsIn a (L.opens i) := by apply LineBundle.exists_landsIn) : a = t := by grind [IsProjEmbedding]
protected lemma LineBundle.IsProjEmbedding.of_isPullback {T p t b} : L.IsProjEmbedding s → IsPullback p t s b → @IsProjEmbedding Y T _ (L.pull p) t | ⟨l, o, h⟩, H => ⟨l.pull _, of_isPullback H o, by simp; grind [H.hom_ext, H.w]⟩
lemma isProjEmbedding_projSpace [Finite κ] : @IsProjEmbedding _ S _ ((ProjSpace.hyperplaneBundle κ).pull fst) snd := .of_isPullback ⟨ProjSpace.isLinearSystem_hyperplaneBundle, (specZIsTerminal.hom_ext ..).subst (comp_mem _ _ _ (@instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat _ _ _ _ _ _ _ (.of_restrictScalars_finiteType ℤ ..)) (@instIsProperOfIsFinite _ _ _ ((IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 (.of_fg (homogeneousSubmodule_fg ..)))))), fun ⟨h, k, e⟩ _ ↦ map_evalSection_fromSpec (ProjSpace.isAffineOpen_chart _) h ▸ map_evalSection_fromSpec _ k ▸ by
 congr 2; erw [← cancel_epi (basicOpenIsoAway _ _ (ProjSpace.X_mem_homogeneousSubmodule _) .refl).1, CommRingCat.hom_ext_iff, ← RingHom.cancel_right (f :=
  eval₂Hom (castRingHom _) _)]; ext <;> simp; repeat erw [← ofSection_eq]
 apply e; intro x; obtain ⟨n, a, ha, rfl⟩ :=
  x.mk_surjective _ (ProjSpace.X_mem_homogeneousSubmodule _)
 use a; ext; rw [← HomogeneousLocalization.algebraMap_apply, map_eval₂Hom]
 simp [mk_eq_mk', eq_mk'_iff_mul_eq, mul_comm, ← eval₂_mul_of_isHomogeneous (by simpa using ha)]
 apply eval₂Hom_X⟩ (.of_is_product' (prodIsProd ..) specZIsTerminal)
lemma LineBundle.exists_picClass_eq_pull_hyperplane [Finite κ] [o : Surjective p] {s : κ → _} (h : ∀ j, L.IsSection (s j)) (k : ∀ i K [Field K] t, LandsIn (t ≫ p) (L.opens i) → ∃ j, s j i ⟨K⟩ (t ≫ p) ≠ 0) : ∃ f, L.picClass = ((ProjSpace.hyperplaneBundle κ).pull f).picClass ∧ ∀ i A t, LandsIn t (L.opens i) → ((ProjSpace.hyperplaneBundle κ).pull f).IsHomogCoords t (s · i A t) := by
 choose W N using fun {j i} ↦ (((h j).1 i).exists_ofSection.imp' X.basicOpen (by grind [landsIn_basicOpen, mono, X.basicOpen_le]) : ∃ W, ∀ {A t}, LandsIn t W ↔ LandsIn t (L.opens i) ∧ IsUnit (s j i A t)); choose F e r using fun {p A t} h ↦
  @ProjSpace.exists_isHomogCoords X _ _ (Prod.snd p) (s · p.1 A t) t (N.1 h).2; refine
  (exists_hom_of_cover (mk _ 1 ?c) @F fun _ q _ _ φ _ a _ ↦ isProjEmbedding_projSpace.2.2 (i := q.2) (have := (r a).map (ProjSpace.isLinearSystem_hyperplaneBundle.pull _) (N.1 a).2 φ; ?_) ?_).imp' (· ≫ fst) fun _ _ ↦ (⟨picClass_eq_iff.2 ⟨s.uncurry ∘ .swap, ?_, ·⟩, ?_⟩) fun _ _ _ a ↦ (N.1 (a.mono (le_of_cover (mk _ 1 ?c) ?_))).2
 simpa [SetLike.ext_iff, o.1.forall] using fun x ↦ flip Exists.imp (L.exists_landsIn (Y.fromSpecResidueField x ≫ p)) fun i a ↦ (k i _ _ a).imp fun j ↦ (@N.2 ⟨a, ·.isUnit⟩ default)
 all_goals simp at *; grind
lemma LineBundle.IsLinearSystem.exists_hom_projSpace [Finite κ] (h : N.IsLinearSystem) (s : X ⟶ S) : ∃ j, j ≫ snd = s ∧ ((ProjSpace.hyperplaneBundle κ).pull fst).pull j = N :=
 (exists_picClass_eq_pull_hyperplane (𝟙 _) h.isSection (by grind [transition_self])).imp'
 (prod.lift · s) (by grind [pull_comp, lift_fst, lift_snd, ext_of_transition_eq_mul, pull,
 ProjSpace.isLinearSystem_hyperplaneBundle])
@[mk_iff] class inductive HasProjEmbedding (s) : Prop
 | mk {I P} [Finite I] (h : @IsProjEmbedding X S I P s)
end
open AlgebraicGeometry CategoryTheory CommRingCat Finset PointFn Function MvPolynomial ProjSpace TopologicalSpace Over
variable {X Y S ι κ} {L : LineBundle X ι} {s : X ⟶ S} {Λ : Type} [Fintype Λ] {ν : Λ → _} (N : ∀ l, LineBundle X (ν l))
instance [h : HasProjEmbedding s] : IsProper s := h.rec (·.2.1)
namespace LineBundle
namespace IsProjEmbedding
lemma ext (h : L.IsProjEmbedding s) {a b : Y ⟶ X} (e : L.pull a = L.pull b) (o : a ≫ s = b ≫ s) : a = b := hom_ext_of_cover (L.pull a) fun i A t x ↦
 h.2.2 ⟨x, (e ▸ x :), (congr(($e).transition i · A t))⟩ (t ≫= o)
lemma comp : L.IsProjEmbedding s → ∀ p [@IsClosedImmersion Y X p], (L.pull p).IsProjEmbedding (p ≫ s)
 | ⟨l, _, H⟩, p, _ => ⟨l.pull p, {}, ((cancel_mono p).1 <| H · ·)⟩
lemma mul {N b} : L.IsProjEmbedding s → @IsProjEmbedding S Y κ N b → (L.mul (N.pull s)).IsProjEmbedding (s ≫ b)
 | ⟨l, _, H⟩, ⟨k, _, G⟩ => ⟨l.mul (k.pull _), {}, by simp_all; grind [→ transition_self]⟩
lemma exists_isClosedImmersion [Finite ι] (h : L.IsProjEmbedding s) : ∃ j, IsClosedImmersion j ∧ j ≫ Limits.prod.snd = s ∧ ((hyperplaneBundle ι).pull Limits.prod.fst).pull j = L := (h.1.exists_hom_projSpace s).imp fun j a ↦ ⟨(IsClosedImmersion.iff_isProper_and_mono _).2 ⟨@.of_comp _ _ _ _ _ (a.1 ▸ h.2.1) isProjEmbedding_projSpace.2.1.1, ⟨by intros; apply h.ext <;> grind [=_ pull_comp]⟩⟩, a⟩
lemma exists_affine_chart [Finite ι] {R s} (h : @IsProjEmbedding X (Spec R) ι L s) i : ∃ u : IsAffineOpen _, ∃ φ : MvPolynomial ι R →+* Γ(X, L.opens i), Surjective φ ∧ specMap (φ.comp C) = u.fromSpec ≫ s ∧ ∀ {A t}, LandsIn t (L.opens i) → ∀ P, ofSection (φ P) A t = eval₂Hom (Spec.preimage (t ≫ s)).hom (L.transition i · A t) P := by
 obtain ⟨⟨f, _, _, e⟩, W⟩ := h.exists_isClosedImmersion, @(isAffineOpen_chart i).preimage _ _ _ _ (MorphismProperty.of_isPullback (.flip (.of_hasBinaryProduct' _ (Spec R))) inferInstance)
 refine have u := e ▸ W.preimage f; have I := (by simpa using landsIn_fromSpec u (𝟙 _)); ⟨u, eval₂Hom (Spec.preimage (u.fromSpec ≫ s)).hom (L.transition i · _ u.fromSpec), ?_, by simp [specMap], (map_evalSection_fromSpec u · ▸ by simp [(h.1.1 ..).1 _, I, hom_eval₂])⟩
 obtain ⟨⟨⟩, t, _, k⟩ := e, @exists_isHomogCoords (Spec R) _ ⟨_⟩ i (update .X i 1) (specMap C) (by simp)
 use have T := (k i).1.2 (by simp); (f.app_surjective _ W).forall.2 fun s ↦ ⟨_, (isRegularOn_ofSection s (ofHom (eval₂Hom ..)) t T).symm.trans ((congrArg _ (?_ : _ = _ ≫ f)).trans (ofSection_map_fromSpec u _ (𝟙 _)))⟩
 refine isProjEmbedding_projSpace.2.2 ⟨T.comp _, I, ?_⟩ ?_ <;> simp_all [↓((isLinearSystem_hyperplaneBundle.pull _).1 ..).1 _, ↓k i, ← Spec.map_comp, ← ofHom_comp, update, apply_ite, transition_self]
end IsProjEmbedding
attribute [local simp] IsRegularOn transition_self landsIn_iInf
@[simps -fullyApplied] noncomputable def pi (s : _ := @univ Λ _) := mk (fun i : ∀ l, _ ↦ ⨅ a, (N a).opens (i a)) fun i j ↦ ∏ a ∈ s, (N a).transition (i a) (j a)
noncomputable def pow (L : LineBundle X ι) m := pi fun _ : Fin m ↦ L
variable {S : _} {Λ : Type} [Fintype Λ] {ν : Λ → _} {N : ∀ l, LineBundle X (ν l)} {ι : Type} {L : LineBundle X ι} {Y : Scheme} (p : Y ⟶ X) (m)
@[simp] lemma picClass_pi s : (pi N s).picClass = ∑ l ∈ s, (N l).picClass :=
 .symm (by induction s using
 cons_induction <;> simp [*] <;> (apply picClass_eq_of_le (by tauto)) <;> simp [iInf_le, *])
lemma IsLinearSystem.pi (h : ∀ a, (N a).IsLinearSystem) : (pi N).IsLinearSystem := by
 simp_all [IsLinearSystem, IsHomogCoords, forall_and, Ring.eq_mul_inverse_iff_mul_eq, ← prod_mul_distrib]
 use fun _ _ _ _ a _ ↦ prod_eq_zero (mem_univ a) (by grind), by grind
lemma pull_pi : (pi N).pull p = pi (N · |>.pull p) := by ext <;> simp [Opens.coe_iInf]
lemma isProjEmbedding_pi {W : Over S} [IsProper W.hom] {Z : Λ → _} (π : ∀ l, W ⟶ Z l) {N : ∀ l, LineBundle _ (ν l)} (h : ∀ l, (N l).IsProjEmbedding (Z l).hom) (H : ∀ {T} {x y : T ⟶ W}, (∀ l, x ≫ π l = y ≫ π l) → x = y) : (pi fun l ↦ (N l).pull (π l).left).IsProjEmbedding W.hom :=
 ⟨.pi (h · |>.1.pull _), {}, fun {c A a b} g o ↦ congr($(@H (.mk _) (homMk a o) (homMk b) fun l ↦ by ext; exact (@(h l).2.2 (c l) A (a ≫ _)
 (b ≫ _) (have := (g.2.2 <| update c l ·); by simp_all [prod_eq_single l]) (by simpa))).1)⟩
@[simp] lemma picClass_pow : (L.pow m).picClass = m • L.picClass := by simp [pow]
lemma IsProjEmbedding.pow {s} (h : @IsProjEmbedding X S _ L s) {m} (hm : m ≠ 0) : (L.pow m).IsProjEmbedding s := @isProjEmbedding_pi _ _ _ _ (.mk s) h.2.1 _ (fun _ ↦ 𝟙 _) _ (by tauto) (· ⟨_, hm.pos⟩)
end LineBundle
