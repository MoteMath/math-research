import Lib.GLn.SchurModule.RationalRep
import Lib.Weil.Construction.PairDefs
seal Finset.univ Finset.sum Finset.prod
noncomputable section
open NumberField MvPolynomial Nat Finsupp Finset Function G Matrix Sum Heisenberg.Rep Heisenberg.OrthogonalSum
variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} (V : Space E n s)
class Space.IsStd where
  signs_eq_one : s = 1
  point_eq_one : V.x = 1
instance : (stdSpace E n).IsStd := ⟨rfl, rfl⟩
instance : ((stdSpace E n).hom (stdSpace E n')).IsStd := ⟨rfl, by ext1; simp [Space.hom]⟩
@[simps! -isSimp apply] def Space.jetSeries (a : ℂ) : 𝒮 V →ₗ[ℂ] MvPowerSeries (InfinitePlace E × n) ℂ := .pi fun α ↦ (a ^ α.degree / α.prod fun _ ↦ (↑·!)) • (V.θ ∘L V.integrated (polyVector _ (monomial α 1))).1
@[simp] lemma Space.jet_jetSeries_eq_theta f P a : jet ℂ P (V.jetSeries a f) = V.θ (V.integrated (polyVector _ (aeval (a • X ·) P)) f) := P.induction_on' (by simp [jetSeries_apply, jet_monomial, bind₁_monomial, smul_pow, field, C_mul', prod_smul, prod_pow_eq_pow_sum, degree_apply, MvPowerSeries.coeff_apply]) (by aesop)
abbrev boxes {Φ : Type} [Fintype Φ] (κ : Φ → ℕ → ℕ) N := ∑ τ, ∑ h ∈ .range N, h * κ τ h
def schurJet {Φ R} [Fintype Φ] [CommRing R] κ := (.mapMatrixLinear R ∘ₗ (jet R).flip).flip
  (schur κ fun τ : Φ ↦ .of fun (b : n') (c : n) ↦ X (τ, b, c))
variable {E : Type*} [Field E] [CMType E] {n : Type*} [Fintype n] {s : n → ℤˣ} {n₂ : Type*} [Fintype n₂] {s₂ : n₂ → ℤˣ} {n₁ : Type*} [Fintype n₁] {s₁ : n₁ → ℤˣ} {e : _ ⊕ _ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂) {V : Space E n s} {V₁ : Space E n₁ s₁} {V₂ : Space E n₂ s₂}
def G.blockEmb {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*} [Fintype n] {s : n → ℤˣ} {n₂ : Type*} [Fintype n₂] {s₂ : n₂ → ℤˣ} {n₁ : Type*} [Fintype n₁] {s₁ : n₁ → ℤˣ} {e : _ ⊕ _ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂) : G E s₁ × G E s₂ →* G E s := (reindex e (hs ▸ by grind)).toMonoidHom.comp sum
@[simp] lemma blockEmb_mem_Gamma_iff hs {g} : blockEmb (e := e) hs g ∈ (stdSpace E n).Γ ↔ g.1 ∈ (stdSpace E _).Γ ∧ g.2 ∈
  (stdSpace E _).Γ := by simp [Space.mem_Γ_iff_range, blockEmb, reindex_equiv e]
@[fun_prop] lemma G.isClosedEmbedding_blockEmb : Topology.IsClosedEmbedding (blockEmb (E := E) hs) := ((reindex _ hs).1.4.isClosedEmbedding (continuous_reindex ..) (continuous_reindex e (hs ▸ by grind))).comp (by fun_prop)
omit [Fintype n] [Fintype n₂] [Fintype n₁] in
lemma realSigns_comp_split (hs : s ∘ e = s₁ ⊕ᵥ s₂) [WeilData E] : realSigns E s ∘ (Equiv.prodSumDistrib ..).symm.trans (.prodCongr (.refl _) e) = realSigns E s₁ ⊕ᵥ realSigns E s₂ := by simp_all [_root_.funext_iff]
def Space.boxProd [WeilData E] : 𝒮 V₁ →L[ℂ] 𝒮 V₂ →L[ℂ] 𝒮 V := tmul (by
  use .trans (.symm (.mk' .sumArrowHomeomorphProdArrow ?_)) (.mk (by use! (· ∘ e.symm), (· ∘ e) <;>
    cat_disch)) <;> simp +singlePass [adelicHeis_beta_eq_prod, vacuumFn_eq_prod] <;> simp_all [funext_iff, reindex_equiv e] <;> tauto)
variable [WeilData E] {g : G E s} {g₁ : G E s₁} {g₂ : G E s₂} (h : g.mat.submatrix e e = fromBlocks g₁.mat 0 0 g₂.mat)
lemma Space.rho_boxProd x f₁ f₂ : V.ϱ x (boxProd hs f₁ f₂) = boxProd hs (V₁.ϱ (x ∘ e ∘ inl) f₁) (V₂.ϱ (x ∘ e ∘ inr) f₂) := heisOp_tmul ..
lemma Space.boxProd_rho y₁ y₂ f₁ f₂ : boxProd hs (V₁.ϱ y₁ f₁) (V₂.ϱ y₂ f₂) = V.ϱ ((y₁ ⊕ᵥ y₂) ∘ e.symm) (boxProd hs f₁ f₂) := by simp [rho_boxProd, comp_def]
@[simp] lemma Space.boxProd_vacElem : boxProd hs V₁.vacElem V₂.vacElem = V.vacElem := tmul_vacElem ..
lemma Space.boxProd_integrated v₁ v₂ f₁ f₂ : boxProd hs (V₁.integrated v₁ f₁) (V₂.integrated v₂ f₂) = V.integrated (realBoxProd (realSigns_comp_split hs) v₁ v₂) (boxProd hs f₁ f₂) := by erw [map_integrated _ ((boxProd hs).flip _), map_integrated _ (boxProd hs _), eq_comm, integrated_tmul] <;>
  simp [left, right, rho_boxProd, realVec, realCoordSum, comp_def, ← Pi.zero_def, ← Prod.zero_eq_mk]
include hs h
lemma weilMultiplier_fromBlocks : weilMultiplier g = weilMultiplier g₁ * weilMultiplier g₂ := by
  erw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← glMultiplier_fromBlocks _ _ e.symm]; simp [weilMultiplier, realMultiplier, ← principalMinor_submatrix e, ← map_mul]; congr!; convert principalMinor_fromBlocks <;> try infer_instance
  repeat simp_all [← ext_iff, Prod.ext_iff, _root_.funext_iff, reindex_equiv e]
lemma Space.omega_boxProd f₁ f₂ : V.ω g (boxProd hs f₁ f₂) = boxProd hs (V₁.ω g₁ f₁) (V₂.ω g₂ f₂) := by apply_rules [weilRep_tmul, weilMultiplier_fromBlocks]; ext1; erw [e.eq_comp_symm, ← submatrix_mulVec_equiv, h, fromBlocks_mulVec]; aesop
