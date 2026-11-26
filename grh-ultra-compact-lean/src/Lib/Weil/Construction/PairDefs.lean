import Lib.DiscreteSeries.Theta.OscillatorDefs
import Lib.Weil.Construction.ThetaFunctional
noncomputable section
open Circle Classical Complex Equiv Heisenberg Matrix NumberField Space WeilData IsVacuum Kronecker
variable {E : Type*} [Field E] [CMType E] [WeilData E] {n : Type _}
  [Fintype n] {s : n → ℤˣ} (V : Space E n s) (x y : n → 𝔸 E) {n' : Type _} [Fintype n']
  {s' : n' → ℤˣ}
def 𝒮 (_ : Space E n s) := Model (adelicHeis E s) deriving NormedAddCommGroup, NormedSpace ℂ,
  CompleteSpace
def realVec : (InfinitePlace E × n → ℂ) →+ n → 𝔸 E :=
  .mk' (fun y i ↦ ((scaleIdele E).1.1 * (y ⟨·, i⟩), 0)) (by simp [mul_add, funext_iff])
def realCoord (p : _ × _) := (y p.2).1 p.1 / (scaleIdele E).1.1 p.1
abbrev finCoord i := α⁻¹.1 * (y i).2
def finVec (x : n → _) i := ((0, α.1 * x i) : 𝔸 E)
attribute [local simp] Finset.mul_sum Space.vecAtPoint adelicSum dotProduct realCoord realVec
omit [Fintype n] in
lemma realVec_realCoord_add : realVec (realCoord y) + (0, y · |>.2) =
  y := by ext <;> simp; grind [conj_scaleIdele_mul]
@[simp] lemma adelicSum_real_eq_realVec s y : (adelicSum E (n := n) s).equiv (y, 0) =
  realVec y := by bound
lemma adelicHeis_beta_eq_prod : (adelicHeis E s).β x y = ∏ i, (adelicHeis E fun _ : Unit ↦
  s i).β (fun _ ↦ x i) fun _ ↦ y i := by simp [adelicHeis, stdForm]; erw
  [← map_prod (coeHom.comp (stdAddChar E).toMonoidHom)]; rfl'
lemma vacuumFn_eq_prod : vacuumFn x = ∏ i, vacuumFn fun _ : Unit ↦ x i := by
  simp [vacuumFn, Finset.prod_ite_zero, ← exp_sum]
  congr; erw [← map_prod (coeHom.comp (ψf E).toMonoidHom)]; rfl'
def lineTheta c a :=
  (signedSpace E fun _ ↦ c).exists_isThetaFunctional.choose (heisOp (fun () ↦ a) IsVacuum.vacElem)
lemma exists_isThetaFunctional_signedSpace : ∃ θ, (signedSpace E s).IsThetaFunctional θ ∧ ∀ x,
  θ (heisOp x IsVacuum.vacElem) = ∏ i,
  lineTheta (s i) (x i) := have ⟨θ, h, m⟩ := (signedSpace E s).exists_isThetaFunctional
  let a x := θ (heisOp x IsVacuum.vacElem)
  have k x y : ∏ i, lineTheta _ (x i) * star (lineTheta _ (y i)) = a x * star (a y) :=
    tendsto_nhds_unique (tendsto_finsetProd _ fun i _ ↦ (piUnique _).symm.hasSum_iff.2
    (exists_isThetaFunctional.choose_spec.elim (fun p ↦ p.hasSum_modelInner p) _ _))
    (.congr (Finset.sum_prod_piFinset · _) (((h.hasSum_modelInner h m ..).congr_fun fun _ ↦ by
    simp [adelicHeis_beta_eq_prod (s := s), vacuumFn_eq_prod (n := n), signedSpace,
      ← map_inv]; rfl).comp
    (Filter.tendsto_atTop_finset_of_monotone (by aesop_cat) (⟨Finset.univ.image ·, by simp⟩))))
  have ⟨y, _⟩ : ∃ y, a y ≠ 0 := by_contra (by aesop)
  ⟨((∏ i, lineTheta (s i) (y i)) / a y) •
    θ, by simp_all [IsThetaFunctional, Space.IsRatInvariant]; grind [map_ne_zero]⟩
namespace Space
lemma IsThetaFunctional.comp {V₁ : Space E _ s'} {θ σ} [RingHomIsometric σ] [RingHomInvPair σ σ]
  (h : V.IsThetaFunctional θ) (T : _ →SL[σ] _) (φ : _ ≃ₜ+ _) (hφ : ∀ x ∈ V₁.ratVectors,
  φ x ∈ V.ratVectors) (hρ : ∀ x v, T (heisOp x v) = heisOp (φ x) (T v)) (h1 :
  modelInner (T IsVacuum.vacElem) (T IsVacuum.vacElem) = 1) : V₁.IsThetaFunctional
  (σ.toSemilinearMap.mkContinuous 1 (by simp) ∘SL θ ∘SL T) := ⟨by simp_all [IsRatInvariant,
  IsThetaFunctional], by rw [← (one_mul _).trans h1, ← h.1.quotMean_eq _ h.2, ← quotMean_comp _
  (.mk' φ _) _ hφ φ.surjective] <;> simp [*, mul_conj', ↓IsRatInvariant.isContPeriodic, h.1]⟩
def heisRep : (adelicHeis E s).Rep (𝒮 V) := IsVacuum.heisRep
abbrev ϱ := V.heisRep.ρ y
def ω : G E s →* 𝒮 V →L[ℂ] 𝒮 V := weilRep adelicAction
def dataInner : 𝒮 V →L⋆[ℂ] 𝒮 V →L[ℂ] ℂ := modelInner
def vacElem : 𝒮 V := IsVacuum.vacElem
def rawTheta : 𝒮 V →L[ℂ] ℂ := if h : ∃ g, ∀ γ ∈ V.ratVectors,
  G.mat g *ᵥ γ ∈ (signedSpace E s).ratVectors then exists_isThetaFunctional_signedSpace.choose ∘L
  V.ω h.choose else V.exists_isThetaFunctional.choose
def θ := V.rawTheta ∘L V.ϱ 0
lemma theta_eq_rawTheta : V.θ = V.rawTheta := by ext; simp [θ]
lemma isThetaFunctional_rawTheta : V.IsThetaFunctional V.rawTheta :=
  dite_mem (s := {θ | V.IsThetaFunctional θ}).2 ⟨fun h ↦ exists_isThetaFunctional_signedSpace (E :=
  E) (s := s).choose_spec.1.comp _ _ (.mk' (.smul h.choose) (by simp))
  h.choose_spec (weilRep_heisOp adelicAction _) (by simp [vacuumFn]), fun _ ↦ choose_spec _⟩
instance : FunLike (𝒮 V) (n → 𝔸 E) ℂ :=
  ⟨fun f x ↦ V.rawTheta (V.ϱ x f), V.isThetaFunctional_rawTheta.injective_apply_heisOp⟩
def integrated : Model (realHeis (realSigns E s)) →L[ℂ] 𝒮 V →L[ℂ] 𝒮 V :=
  (V.heisRep.left (adelicSum ..)).integrated
def finHeisOp x := stdLattice.semichar x • V.ϱ (finVec x)
def projOn (S : Set (FinPlace E)) := strongIntegral ((latticeMeasure E n).restrict (stdLattice E n))
  fun y ↦ V.finHeisOp (idem S.conjClosure • y)
abbrev projReal := V.integrated vacVector
def ratMap (V' : Space E _ s') (i : Matrix n n' _) := V.x⁻¹.1 * i.map (toAdele (E := E)) * V'.x.1
open ComplexConjugate IsVacuum
variable {E : Type _} [Field E] [CMType E] [WeilData E]
  {n : Type _} [Fintype n] {s : n → ℤˣ} (V : Space E n s) (g : G E s) (c : ℂ) (x : n → 𝔸 E)
  (y : n → 𝔸 E) (f f' : 𝒮 V)
lemma ϱ_apply : V.ϱ y f x = (adelicHeis E s).β x y * f (x + y) := (by aesop : V.rawTheta _ = _)
lemma θ_apply : V.θ f = f 0 := rfl
lemma add_apply : (f + f') x = f x + f' x := map_add (_ ∘L _) ..
lemma smul_apply : (c • f) x = c * f x := map_smul (_ ∘L _) ..
lemma zero_apply : (0 : 𝒮 V) x = 0 := map_zero (_ ∘L _)
@[ext] lemma data_ext {f f' : 𝒮 V} : (∀ x, f x = f' x) → f = f' := DFunLike.ext _ _
instance : ContinuousEval (𝒮 V) _ ℂ := ⟨V.rawTheta.2.comp (by fun_prop)⟩
lemma apply_vecAtPoint_add γ x : (adelicHeis E s).β (V.vecAtPoint γ) x * f (V.vecAtPoint γ + x) =
  f x := V.ϱ_apply .. ▸ V.isThetaFunctional_rawTheta.1 _ ⟨γ, rfl⟩ _
@[fun_prop] lemma continuous_ω : Continuous fun p ↦ V.ω (.fst p) p.2 := continuous_weilRep ..
lemma ω_ϱ : V.ω g (V.ϱ x f) = V.ϱ (g.mat *ᵥ x) (V.ω g f) := weilRep_heisOp ..
lemma dataInner_eq_quotMean : V.dataInner f f' = quotMean V.ratVectors fun x ↦ f' x * conj (f x) :=
  V.isThetaFunctional_rawTheta.elim (·.quotMean_eq ‹_›) _ _ ▸ (one_mul _).symm
lemma dataInner_rho : V.dataInner (V.ϱ x f) (V.ϱ x f') = V.dataInner f f' := modelInner_heisOp ..
lemma dataInner_omega : V.dataInner (V.ω g f) (V.ω g f') = V.dataInner f f' := modelInner_weilRep ..
lemma eq_zero_of_dataInner_self {f} : V.dataInner f f = 0 → f = 0 := eq_zero_of_modelInner_self
lemma dataInner_vacElem_vacElem : V.dataInner V.vacElem V.vacElem = 1 :=
  (modelInner_vacElem ..).trans (by simp [vacElem, vacuumFn])
lemma dataInner_rho_of_vacElem : V.dataInner V.vacElem (V.ϱ y V.vacElem) = vacuumFn y := by
  erw [← conj_modelInner, modelInner_heisOp_vacElem, (adelicSum E s).isVacuum.4]
lemma dataInner_omega_of_vacElem : V.dataInner V.vacElem (V.ω g V.vacElem) =
  (conj (weilMultiplier g))⁻¹ := by erw [modelInner_vacElem,
  eq_inv_of_mul_eq_one_right (conj_delta_mul_weilRep_vacElem ..), adelicAction]
attribute [simp] ϱ_apply θ_apply add_apply smul_apply zero_apply dataInner_rho dataInner_omega
  dataInner_vacElem_vacElem dataInner_rho_of_vacElem dataInner_omega_of_vacElem Prod.mk_one_one
  Circle.norm_coe WeilData.j_ne_zero v_uniformizer U.norm_det
lemma θ_ϱ : V.θ (V.ϱ y f) = f y := by simp
lemma norm_apply_le : ‖f x‖ ≤ ‖V.θ‖ * ‖f‖ := by simpa using V.θ.le_opNorm (V.ϱ x f)
lemma hasSum_dataInner : HasSum (fun γ ↦ V.dataInner f' (V.ϱ (V.vecAtPoint γ) f)) (V.θ f * conj
  (V.θ f')) := by simpa [θ] using! V.isThetaFunctional_rawTheta.elim (·.hasSum_modelInner ‹_›) _ f
lemma ext_of_vacElem {Y} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] {T T' :
  _ →L[ℂ] Y} (h : ∀ y, T (V.ω g (V.ϱ y V.vacElem)) = T' (V.ω g (V.ϱ y V.vacElem))) : T = T' :=
  (ContinuousLinearEquiv.arrowCongr (.ofUnit (V.ω.toHomUnits g⁻¹)) 1).injective (hom_ext h)
end Space
variable {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s)
  (T : Space E n' s') {m m' R : Type*} (a b : AutChar E) {E' : Type*} [Field E'] [NumberField E']
abbrev homSigns s s' := (pairSign 1 s' s : n' × n → _)
def matToVec (x : Matrix m' m R) p := x (Prod.fst p) p.2
def vecToMat (y : m' × m → R) := of fun i j ↦ y (i, j)
omit [Fintype n] [Fintype n'] in
@[simp] lemma stdForm_homSigns : stdForm _ (homSigns s s') = stdForm E' s' ⊗ₖ (stdForm _ s)ᵀ := by
  aesop (add simp [stdForm, pairSign, diagonal])
section
variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n n' : Type} [Fintype n] [Fintype n']
  {s : n → ℤˣ} {s' : n' → ℤˣ}
def G.onHom := (toUnitary : G E (homSigns s s') ≃* _).symm.toMonoidHom.comp ((U.kron
  stdForm_mul_self stdForm_homSigns).comp (toUnitary.toMonoidHom.prodMap toUnitary.toMonoidHom))
def G.det := (U.det (isUnit_stdForm.map detMonoidHom)).comp (toUnitary : G E s ≃* _).toMonoidHom
@[simp] abbrev detFin s (g : Gf E n) := G.det (s := s) (1, g)
end
@[simps -isSimp J] def Space.hom : Space E _ (homSigns s s') := by
  use! T.J ⊗ₖ S.J⁻¹ᵀ, T.x ⊗ₖ S.x⁻¹.1ᵀ, ↑T.x⁻¹ ⊗ₖ S.xᵀ
  repeat simp [gram_point, map_J_inv, map_kronecker, conjTranspose_nonsing_inv]
def WeilData.upsilonU1 :
    AutChar E := ⟨υ.1.comp ⟨Unitary.toUnits, .of_coeHom_comp (by fun_prop)⟩, fun _ ↦ (υ.2 _ ·)⟩
def AutChar.spaceChar (k : ℕ) := a.baseChange * SplittingChar.υ⁻¹ ^ k
def rankTwist n [Fintype n] := a * WeilData.upsilonU1 ^ (Fintype.card n / 2)
def pairChar : G E s × G E s' →* ℂ :=
  Circle.coeHom.comp ((b⁻¹.1.1.comp G.det).coprod (a.1.1.comp G.det))
def pairWeil := MonoidHom.mk ⟨fun p ↦ pairChar a b p • (S.hom T).ω (.onHom p), by simp⟩
    (by simp [← smul_mul_smul])
def pairTheta f p := Space.θ _ (pairWeil S T a b p f)
