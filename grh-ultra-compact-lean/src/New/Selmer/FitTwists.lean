import New.Heights.Heights
import Lib.LocalGL.TraceFormula.ChangingSigns
import New.Exchange.AlgebraicPartDefs
seal Finset.univ Finset.sum Finset.prod
lemma LevelPlaces.LevelForm.p6 {E r n} [Field E] [CMType E] [Fintype r] [Fintype n] {O : AuxPair E r n} σ φ φ' {w} (hw : _ ≠ w) hS hS' X : innerAt σ (O.heckePolyOnForms hw hS X φ) φ' = innerAt σ φ (O.heckePolyOnForms (star_injective.ne hw) hS' (σ.symm (star (σ X))) φ') := by
  simpa [innerAt] using! heckePolyOp_adjoint hw _ (mem_sphericalAt _ hS) (mem_sphericalAt _ hS)
    (smoothPairing_formTranslation _) _
open Module Complex Fint LinearMap Matrix MonoidHom Submodule LevelPlaces.LevelForm ComplexOrder Gf Representation
variable {E r n} [Field E] [CMType E] [WeilData E] [Fintype r] [Fintype n] {ℓ : ℕ} [Fact ℓ.Prime] (ι : ℂ ≃+* PadicAlgCl ℓ) (O : AuxPair E r n) {w} (hw : _ ≠ w) (hS : w ∉ O.places.conjClosure) (e₀ : MonoidAlgebra ℂ (O.ChosenGL r)) (Z : Submodule ℂ O.FormV) {e₀' : MonoidAlgebra ℂ (O.ChosenGL r)} {Z' : Submodule ℂ O.FormV}
noncomputable abbrev AuxPair.groupAlgAction := O.formAction.asAlgebraHom e₀
def AuxPair.IsTested y := ∀ w hw hS, y ∈ ((O.groupAlgAction e₀).range ⊓ (O.heckePolyOnForms (w := w) hw hS (O.testValue w)).ker ⊓ Z)ᗮ
def AuxPair.IsTestForm l [Fact (Nat.Prime l)] Ξ := (∀ j : PadicPlace l, Ξ ∈ integralForms j) ∧ O.IsTested (tupleIdem r fun _ ↦ .X - 1) O.θ.ker Ξ
def DenominatorLe β := ∀ d, finrank ℂ Z = d → ∀ y y' : Fin d → _, (∀ a (j : PadicPlace ℓ), y a ∈ integralForms j) → (∀ b, y' b ∈ integralForms ⟨(algebraMap _ ℂ_[ℓ]).comp ι.toRingHom⟩ ∧ O.IsTested e₀ Zᗮ (y' b)) → ‖ι
  (of fun a b ↦ inner ℂ (y a) (Z.starProjection (y' b))).det‖ ≤ .exp (d * (Fintype.card r * β))
section
omit [WeilData E]
lemma AuxPair.isOfFinOrder_prod_psi_det (g : O.ChosenGL r) : IsOfFinOrder (∏ i, O.ψ _ (g i).1.det) := (CommMonoid.torsion _).prod_mem fun _ _ ↦ isOfFinOrder _ (by simp [IsUnit.isOfFinOrder])
lemma AuxPair.innerAt_formAction σ g x y : innerAt σ (O.formAction g x) (O.formAction g y) = innerAt σ x y := σ.injective (by
  erw [map_smulₛₗ₂, LinearMap.map_smul, smul_smul, map_mul, map_mul, σ.apply_symm_apply, conj_mul', (isOfFinOrder _ (isOfFinOrder_prod_psi_det ..)).norm_eq_one]; simp; with_unfolding_all exact congr(_ * $(smoothPairing_formTranslation ..)))
lemma AuxPair.range_groupAlgAction_mem_invtSubmodule {f} (h : ∀ g y, (f (O.formAction g y)).1 = (O.formAction g (f y)).1) : (O.groupAlgAction e₀').range ∈ End.invtSubmodule f := fun _ ⟨k, e⟩ ↦ e ▸ ⟨f k, by simp [asAlgebraHom_eq_sum, Subtype.ext (h ..)]⟩
lemma AuxPair.k6 {u} (h : star u ≠ u) s X Y y : O.heckePolyOnForms hw hS X (O.heckePolyOnForms h s Y y) = O.heckePolyOnForms h s Y (O.heckePolyOnForms hw hS X y) := Subtype.ext (by (repeat erw [coe_restrict_apply]); simpa [heckeSplit_comm hw, heckePolyOp, heckePolyEval, Finset.smul_sum, smul_smul, *, mul_comm, ↓mem_sphericalAt, -Set.Sum.elim_range]
  using Finset.sum_comm)
lemma AuxPair.innerAt_groupAlgAction (he : IsCentralProj e₀') σ x y : innerAt σ (O.groupAlgAction e₀' x) y = innerAt σ x (O.groupAlgAction e₀' y) := he.self_adjoint _ σ _ (O.innerAt_formAction σ) ..
end
lemma AuxPair.normSqAt_starProjection_le (he : IsCentralProj e₀') (hZ : Z' ≤ (O.groupAlgAction e₀').range ⊓ (O.heckePolyOnForms hw hS (O.testValue w)).ker) {y} (h : O.IsTested e₀' Z'ᗮ y) σ : normSqAt (Z'.starProjection y) σ ≤ normSqAt y σ := by
  have a := (p6 · · · hw hS (by grind [star_star]) (O.testValue w))
  obtain ⟨z, p, x, q, rfl⟩ := mem_sup.1 ((Z' ⊔ ((O.groupAlgAction e₀').ker ⊔ (O.heckePolyOnForms hw hS (O.testValue w)).range)).orthogonal_orthogonal.le fun u m ↦ h _ hw hS u (by
    simp_all [← inf_orthogonal, mem_orthogonal', ← IsSymmetric.orthogonal_range (innerAt_groupAlgAction _ he 1)]; apply eq_zero_of_innerAt_self 1; rw [a, k6]; tauto))
  have d σ z (p : z ∈ Z') : x.innerAt σ z = 0 := by obtain ⟨⟨⟨u, rfl⟩, t⟩, x, k, _, ⟨v, rfl⟩, rfl⟩ := hZ p, mem_sup.1 q; simp_all [eq_zero_of_innerAt_self σ _ (by rw [← a, k6, t]; simp) ▸ a σ v _, ← innerAt_groupAlgAction]
  have e x : normSqAt x σ = (σ (x.innerAt σ (x : O.FormV))).re := by simpa [innerAt_eq_stdClassSum] using! (map_classSum reLm _).symm
  simpa +contextual [eq_starProjection_of_mem_of_inner_eq_zero p, inner, ← z.conj_innerAt σ x, *]
    using e x ▸ finsum_nonneg (by simp [smul_nonneg])
variable {P} (D : Data P) {s} (V : Space D.E D.RowIndex s) {p y} {w : _}
def Data.IsSplitOffLevel w := w.IsSplit ∧ w ∉ (Set.range D.chosen).conjClosure
def Data.heckeAlgebra : Subalgebra ℂ (∀ {s} (V : Space _ _ s), End ℂ (D.principalForms V)) where
  carrier := {p | ∃ a, ∀ s V y, asAlgebraHom ((V.formRep _).comp (trivialOn _ (.range D.chosen)).subtype) a y.1 = @p s V y}
  mul_mem' | ⟨a, _⟩, ⟨b, _⟩ => ⟨a * b, by simp [*]⟩
  add_mem' | ⟨a, _⟩, ⟨b, _⟩ => ⟨a + b, by simp [*]⟩
  algebraMap_mem' := (⟨· • 1, by simp⟩)
noncomputable def Data.w2 (x : FinPlace D.E × ℕ) : D.heckeAlgebra := if h : D.IsSplitOffLevel x.1 then ⟨fun _ ↦ .restrict _ fun _ m ↦ heckeSplit_mem_levelSpace h.1 x.2 (levelSpace_anti (maxCompactAt_le_levelOf h.2) m) levelOf_le_Kf m, heckeGL ((leftRegular ℂ _).comp ((atSplit h.1).codRestrict _ (by grind [mem_trivialOn, atPlace_atSplit_of_ne, star_star, IsSplitOffLevel]))) x.2 1, by simp [heckeSplit, heckeGL, heckeFun_sum, MonoidAlgebra.one_def]⟩ else 0
noncomputable def Data.eigenPart (p : _ → ℂ) := ⨅ x, ((D.w2 x).1 V).eigenspace (p x)
lemma Data.isSphericalWith_of_mem_eigenPart (hy : y ∈ D.eigenPart V p) (h : D.IsSplitOffLevel w) : IsSphericalWith (V.formRep _) h.1 (heckePolyEval D.RowIndex w (p ⟨w, ·⟩)) y.1 := isSphericalWith_of_heckeSplit (levelSpace_anti (maxCompactAt_le_levelOf h.2) y.2)
  (by simpa [w2, h, Subtype.ext_iff] using (mem_iInf _).1 hy ⟨w, ·⟩)
def Data.occurringLabels p x := {c | IsPrimitiveLabel (Fintype.card D.RowIndex) c ∧ ∃ y ∈ D.eigenPart V p, asAlgebraHom ((D.principalRep V).comp (.mulSingle _ x)) (labelIdem _ c) y ≠ 0}
lemma Data.dvd_card_resField_sub_one x : let q := .card (ResField (D.chosen x)); 3 ^ 2 ∣ q - 1 ∧ P.Mω D.s ^ 2 ∣ q - 1 ∧ P.Mω D.s + 1 < q := (card_ResField _).trans (D.q_eq_g x.2.2.2) ▸ ⟨by grw [← dvd_g_sub_one, Parameters.Mω, ← P.3, pow_add]; lia, D.dvd_g_sub_one _, D.nat_lt_of_hasLogBound⟩
lemma Data.k9 q (F : Finset _) : ∃ b : D.heckeAlgebra, ∀ d ∈ insert q F, ∀ {s} {V : Space _ _ s}, ∀ y ∈ D.eigenPart V d, b.1 V y = if d = q then y else 0 := F.induction
  ⟨1, by simp⟩ fun e F _ ⟨b, h⟩ ↦ (forall_imp_iff_exists_imp.1 (@funext _ _ e q)).elim fun x m ↦ ⟨b - (e x - q x)⁻¹ • (b * D.w2 x - q x • b), fun d k _ _ y l ↦ by
    by_cases n : d ∈ insert q F <;> simp +contextual [by simpa [eigenPart] using l, h d, *]
    clear * - k n m; simp_all [← sub_smul]⟩
lemma Data.s23_v9 (p : D.heckeAlgebra) x : Commute (p.1 V) ((D.principalRep V).asAlgebraHom x) := p.2.elim fun a h ↦ by
  ext; simp [← h, asAlgebraHom_eq_sum_support, principalRep, levelRep]; simp [← End.mul_apply, ((commute_supportedOn_trivialOn (liftResidue_mem_supportedOn _) _).map _).eq]
noncomputable def Data.heckeOnGood : D.heckeAlgebra →* End ℂ (D.goodForms V) := ⟨⟨fun p ↦ (p.1 V).restrict fun
  | _, ⟨y, rfl⟩ => ⟨_, congr($(s23_v9 ..) y).symm⟩, rfl⟩, fun _ _ ↦ rfl⟩
lemma Data.principalRep_mem_eigenPart (hy : y ∈ D.eigenPart V p) x : (D.principalRep V).asAlgebraHom x y ∈ D.eigenPart V p := by simp_all [eigenPart, ← End.mul_apply, (s23_v9 ..).eq]; aesop
variable [Module.Finite ℂ (D.principalForms V)]
lemma Data.m8 N : {p | N ⊓ D.eigenPart V p ≠ ⊥}.Finite := finite_ne_bot_of_iSupIndep
    (.mono (.iInf _ fun _ ↦ End.eigenspaces_iSupIndep _) inf_le_right)
lemma Data.iSup_eigenPart : ⨆ p, D.eigenPart V p = ⊤ := (_root_.map_eq_top_iff (mapIic _)).1
  (top_unique ((IsUnitary.le_span_hecke_eigenvectors (B := innerₛₗ ℂ) ⟨by simp_all, V.inner_formRep⟩ (p := D.IsSplitOffLevel) (by grind [IsSplitOffLevel, star_star]) (fun _ h ↦ levelSpace_anti (maxCompactAt_le_levelOf h.2)) fun w h j ↦ by simpa [w2, h] using ((D.w2 (w, j)).1 V · |>.2)).trans (span_le.2 fun z ⟨h, c, a⟩ ↦ ⟨⟨z, h⟩, mem_iSup_of_mem (∑ᶠ h, c ⟨⟨·, h⟩, ·⟩).uncurry (by aesop (add simp [eigenPart, w2])), rfl⟩)))
open Set MulChar Space Kf AuxPair
variable {E r n : _} [Field E] [CMType E] [WeilData E] [Fintype r] [Fintype n] (O : AuxPair E r n) {P : _} (D : Data P) (ϑ : D.TameChar) (j)
lemma AuxPair.theta_mul_eq_theta_formAction k {s} (hk : reduceFamily _ k = s) Ξ g : O.θ Ξ (g * (1, k.1)) = O.θ (O.formAction s Ξ) g := by simp [← hk, theta_eq_smul_star_lift_swap]; left; erw [O.pairThetaKernel.swap.lift_equivariant (isAutomorphic_algFormCoeff Ξ.1).conj, map_smul, pairWeil_integrated_fin O.W, O.pairWeil_upsilon k _ 1 (reduceFamily_liftResidue _)]; simp [Space.lift, ← algFormCoeff_algFormRep, ← Finset.prod_inv_distrib, ← inv_apply_eq_inv', ← star_apply']; ac_rfl
lemma Data.exists_theta_to_principalForms : ∃ L : _ →ₗ[ℂ] D.principalForms (D.spaceW j), j ∈ D.LiftIndex → ∀ Ξ, (L Ξ).1.1 = (D.auxPair ϑ j).θ Ξ := by_cases (fun h ↦ ⟨.codRestrict _ ((AuxPair.θ _).codRestrict _ (theta_eq_smul_star_lift_swap _ · ▸ SMulMemClass.smul_mem _ (by simpa using! (((D.fitsParams_auxPair ϑ ⟨j, h⟩).isEdge.isArrow _ _ (auxDatum _).2).2 ⟨_, (isForm_ofAlgForm (isHCParam_paramV _) _).conj⟩).2.conj))) fun Ξ ↦ mem_levelSpace_formRep_iff.2 fun | _, ⟨k, _, rfl⟩ => by simpa using! theta_mul_eq_theta_formAction (s := 1) _ k ‹_› Ξ, by tauto⟩) (by simp [·])
noncomputable def Data.auxLift : D.principalForms (D.spaceW j) →ₗ[ℂ] (D.auxPair ϑ j).FormV := (exists_theta_to_principalForms ..).choose.adjoint
abbrev Data.RankOneIndex z := (Fin 12 ⊕ Fin 4 ⊕ Fin 4) ⊕ Fin (2 * z - 20)
variable {P : _} (D : Data P)
noncomputable abbrev Data.goodLift ϑ j := D.auxLift ϑ j ∘ₗ (D.goodForms _).subtype
def Data.Pair.IsRamified {D} (p : @Pair P D) := ∀ w, p.ψ w ≠ 1 ↔ D.IsChosen w
def Data.Pair.IsRankOne {D} (p : @Pair P D) j := p.HasLiftRank (RankOneIndex p.z) ∧ p.z ∈ Set.Ioc D.m D.r ∧ (j ∈ D.LiftIndex ∧ p.ψ = D.ω ^ (j : ℤ)) ∧ ∀ v, p.c v ≤ D.w j v ∧ D.w j v + D.r ≤ p.c v + D.t
noncomputable abbrev Data.B₀ := D.budget / (D.m * D.k)
structure Data.IsFitFamily (θ : PrimePadicIso → D.MFoldTwist) where
  coprime ι : Nat.Coprime ι.1.1 (θ ι).levelNorm
  denominator_le j : ∃ γ, (∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → T.sum γ ≤ D.B₀) ∧ ∀ ι, DenominatorLe
    ι.2 _ D.e₀ (D.goodLift ((θ ι).powTwist j) j).range (γ ι.1) ∧ ∀ p : D.Pair, ∀ H : p.IsRankOne j,
    DenominatorLe ι.2 _ (tupleIdem _ fun _ ↦
    .X - 1) (ℂ ∙ (p.lValueData H.1 ((θ ι).powTwist j)).trivialLift) (γ ι.1)
  height_le j (p : D.Pair) s : p.IsRamified → HeightLe (D.x ^ 999) fun ι ↦
    (p.ratio ((θ ι).powTwist j) s)⁻¹
