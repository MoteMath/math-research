import Lib.Cohomology.Etale.Functoriality
open AlgebraicGeometry CategoryTheory Polynomial LaurentPolynomial CommAlgCat TrivSqZeroExt Module
variable {k} [CommRing.{0} k] {C} [Category.{0,1} C] (F : C ⥤ ModuleCat k)
def moduleCoeff := liftCoeff (F ⋙ forget₂ ..)
instance : CoeffAction k (moduleCoeff F) := ⟨.comp ⟨((Functor.whiskeringRight ..) (forget₂ .. ⋙ AddCommGrpCat.uliftFunctor)).mapEnd F, rfl, by tauto⟩ (algebraMap ..)⟩
abbrev CommAlg k [CommRing k] := CommAlgCat.{0,0} k
abbrev CommAlg.homOfRingHom {A T : CommAlg k} f e := (ConcreteCategory.ofHom ⟨f, e⟩ : A ⟶ T)
variable (k k') [CommRing.{0} k'] [Algebra k k'] (R : CommRingCat.{0}) [Algebra R k]
def restrictAlg : CommAlg k' ⥤ CommAlg k := .mk (id (@.of _ _ · _ {Algebra.restrictScalars .. with smul := (algebraMap k k' · • ·)})) (@id _ fun f ↦ CommAlg.homOfRingHom _ fun _ ↦ f.1.2 _)
noncomputable def specAlg : CommAlg k ⥤ (Over (Spec R))ᵒᵖ := { restrictAlg .. ⋙ (algSpec R).rightOp with obj A := ⟨.mk (Spec.map (CommRingCat.ofHom ((algebraMap k A).comp _)))⟩ }
noncomputable def algPoints := uliftYoneda.{1} ⋙ restrictAlong (specAlg k R)
noncomputable abbrev algPointsOf := (algPoints k R).obj
lemma eq_C_of_toLaurent_eq {k : Type} [CommRing k] (P Q : k[X]) (h : toLaurent P = invert Q.toLaurent) : ∃ c, (P, Q) = (.C c, .C c) := have := congr(trunc $(Q.as_sum_range ▸ h)); by simp_all [← invert.symm_apply_eq, ← Q.toLaurent_inj]
variable {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] {R : CommRingCat} [Algebra R k] {Z W : Over (Spec R)} {A B : CommAlg k} (c : W ⟶ Z)
lemma fst_surjective_and_kerIdeal_sq : (@fst k M).Surjective ∧ kerIdeal k M ^ 2 = ⊥ := ⟨fst_surjective, by simp⟩
def SqZeroExt.fst := ofHom (fstHom k k M)
abbrev PointsIn X A := algPointsOf k R X A
noncomputable abbrev PointsIn.map (φ : A ⟶ B) : PointsIn W A → PointsIn W B := (algPointsOf ..).map φ
def IsTangentPoly {W Z : CommAlg k ⥤ Type 1} d (c u : W ⟶ Z) y P := ∃ᵉ (T : FGModuleCat k) (v) (A : End k T), let f x := W.map (ofHom (TrivSqZeroExt.map (Dual.eval k T x))) v; finrank k T = d ∧ W.map SqZeroExt.fst v = y ∧ (c _ ∘ f).Injective ∧ (∀ φ, u _ (f φ) = c _ (f (A φ))) ∧ ∀ t, Polynomial.eval t P = P.eval 0 * (1 - t • A).det
def IsNullFamily {k I : Type} [Field k] [Algebra R k] (u : I → (W ⟶ Z)) (a : I →₀ k) d h := ∀ c,
 let S := {y : Σ _ : a.support, PointsIn .. | y.2.1 ≫ c = y.2.1 ≫ u y.1}; ∀ P : _ → _, (∀ y ∈ S, IsTangentPoly d ((algPoints k R).map c) ((algPoints ..).map (u y.1)) y.2 (P y) ∧ (P y).eval 1 ≠ 0) → S.Finite ∧ ∑ᶠ y ∈ S, a y.1 * (P y).coeff h / (P y).eval 1 = 0
def CongruenceRelation {I} [Fintype I] m (𝔭 : Set R) p [Fact (Nat.Prime p)] (a : I → ℕ) (u : _ → (W ⟶ Z)) := ∀ k [Field k] [CharP k p] x, (∀ r ∈ 𝔭, (Spec.preimage (x ≫ W.hom)).hom r = 0) → Cancels m fun i ↦ Spec.map (CommRingCat.ofHom (iterateFrobenius k p (a i))) ≫ x ≫ (u i).left
structure IsGaloisCovering {Δ : FiniteGrp.{0}} (a : Δ →* End W) where
 comp_eq δ : (a δ).asHom ≫ c = c
 onto_geometric : Surjective c.left
 torsor k [Field k] [CharZero k] (x y : Spec ⟨k⟩ ⟶ _) : x ≫ c.1 = y ≫ c.1 → ∃! g,
  x ≫ (a g).asHom.1 = y
