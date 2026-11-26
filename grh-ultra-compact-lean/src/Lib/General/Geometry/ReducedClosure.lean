import Lib.General.LinearAlgebra.Base
open AlgebraicGeometry CategoryTheory IsLocalRing RingHom Spec Scheme.IdealSheafData
variable {X Y Z : Scheme.{0}} {ι κ : Type} {t : Y ⟶ X} {U' : X.Opens} (ξ : κ → (Spec ⟨ℂ⟩ ⟶ X))
noncomputable abbrev specMap [CommRing ι] [CommRing κ] (φ : ι →+* κ) := Spec.map (CommRingCat.ofHom φ)
def LandsIn (t : Y ⟶ X) (U : X.Opens) := ⊤ ≤ t ⁻¹ᵁ U
abbrev PointFn X := ∀ A, (Spec.{0} A ⟶ X) → A
@[simp] lemma landsIn_inf {V} : LandsIn t (U' ⊓ V) ↔ LandsIn t U' ∧ LandsIn t V := forall₂_and
@[simp] lemma landsIn_top : LandsIn t ⊤ := le_rfl
@[simp] lemma landsIn_preimage {s} : @LandsIn _ Z s (t ⁻¹ᵁ U') ↔ LandsIn (s ≫ t) U' := .rfl
lemma LandsIn.comp {U : X.Opens} : LandsIn t U → ∀ a, @LandsIn _ Z (a ≫ t) U := by tauto
def PointFn.IsRegularOn (f : PointFn X) U := ∀ ⦃A B⦄ φ t, LandsIn t U → f B (Spec.map φ ≫ t) = φ (f A t)
noncomputable def PointFn.evalSection {A} t (h : LandsIn t U') := t.appLE U' ⊤ h ≫ (Scheme.ΓSpecIso A).1
noncomputable def PointFn.ofSection {U : X.Opens} : Γ(X, U) →ₙ+* PointFn X := by use! fun s _ t ↦ if h : _ then evalSection t h s else 0 <;> aesop
@[ext] structure LineBundle (X : Scheme.{0}) (ι : Type) where
 opens : ι → X.Opens
 transition : ι → ι → PointFn X
 cover : ⨆ i, opens i = ⊤ := by simp [← iSup_inf_iSup, ← iInf_iSup_eq_of_finite, LineBundle.cover]
 regular i j : (transition i j).IsRegularOn (opens i ⊓ opens j) := by simp_all [PointFn.IsRegularOn, LineBundle.regular _ _ _ _]
 transition_self i A t : LandsIn t (opens i) →
  transition i i A t = 1 := by simp +contextual [LineBundle.transition_self]
 transition_trans i j k A t : LandsIn t (opens i) → LandsIn t (opens j) → LandsIn t (opens k) →
  transition i j A t * transition j k A t = transition i k A t := by (try simp +contextual [LineBundle.transition_trans, ← Finset.prod_mul_distrib]) <;> grind [LineBundle.transition_trans]
variable (L : LineBundle X ι) (M : LineBundle X κ) (R) [CommRing R] [X.Over (Spec ⟨R⟩)] (p : Y ⟶ X) (s : ι → PointFn X)
@[simp] noncomputable def PointFn.pull (f : PointFn X) : PointFn Y := (f · <| · ≫ p)
noncomputable instance : Algebra R (PointFn X) := toAlgebra (.pi fun _ ↦ .pi (· ≫ X ↘ Spec ⟨R⟩ |> preimage |>.hom))
namespace LineBundle
@[simps] noncomputable def pull := mk _ (L.transition · · |>.pull p) (p.iSup_preimage_eq_top L.3)
@[simps] def one : LineBundle X Unit where opens _ := ⊤; transition _ _ := 1
@[simps] def inv := mk L.opens fun i ↦ (L.transition · i)
@[simps] def mul := mk (fun i : ι × κ ↦ L.opens i.1 ⊓ M.opens i.2) fun i j ↦
 L.transition i.1 j.1 * M.transition i.2 j.2
def IsSection := (∀ i, (s i).IsRegularOn (L.opens i)) ∧ ∀ i j A t, LandsIn t (L.opens i) → LandsIn t (L.opens j) → s i A t = L.transition i j A t * s j A t
def IsFrame := L.IsSection s ∧ ∀ i A t, LandsIn t (L.opens i) → IsUnit (s i A t)
def IsIsomorphic := ∃ u, (L.mul M.inv).IsFrame u
def H0 : Submodule R (ι → PointFn X) := by use! {s | L.IsSection s ∧ ∀ i A t, ¬LandsIn t (L.opens i) → s i A t = 0} <;> simp [IsSection, PointFn.IsRegularOn, HSMul.hSMul, SMul.smul] <;> grind
end LineBundle
lemma exists_lift_of_dense_preimage {X Y Z} [IsReduced X] i [@IsClosedImmersion Y Z i] (f : X ⟶ Z) (h : Dense (f ⁻¹' .range i)) : ∃ g, g ≫ i = f :=
 ⟨_, IsClosedImmersion.lift_fac i _ (map_bot f ▸ (map_gc f).le_u (support_eq_top_iff.1 (by
 ext; simp [i.support_ker, f.continuous.closure_preimage_subset _ (h _)])).le)⟩
abbrev IsDenseFamily {Z : Type} {X} (ξ : Z → (Spec ⟨ℂ⟩ ⟶ X)) := DenseRange (ξ · (closedPoint ℂ))
def IsSeparatingFamily {Z : Type} {X} (ξ : Z → (Spec ⟨ℂ⟩ ⟶ X)) := IsReduced X ∧ IsDenseFamily ξ
lemma exists_reduced_closure : ∃ Y i e, IsClosedImmersion i ∧ (∀ z, e z ≫ i = ξ z) ∧ @IsSeparatingFamily κ Y e := let h z := (exists_lift_of_dense_preimage (vanishingIdeal (.closure (.range (ξ · (closedPoint ℂ))))).subschemeι (ξ z) (dense_indiscrete ⟨_, ⟨_, subset_closure ⟨z, rfl⟩⟩, rfl⟩)).choose_spec; ⟨_, _, _, inferInstance, h, @.of_openCover _ (subschemeCover _).cover fun _ ↦ (affine_isReduced_iff _).2 ((Ideal.isRadical_iff_quotient_reduced _).1 (PrimeSpectrum.isRadical_vanishingIdeal _)), (subschemeι _).isEmbedding.dense_iff.2 (closure_mono (by grind [Scheme.Hom.comp_apply]) ·.2)⟩
