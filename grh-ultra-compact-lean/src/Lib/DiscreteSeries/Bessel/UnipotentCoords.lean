import Lib.Adelic.Poincare.MiddleGroupEmbedding
import Lib.DiscreteSeries.Haar.HaarMass
noncomputable section
section
open Matrix
variable (𝔰 : Shape)
abbrev Shape.G₁ := (𝔰.middleGram (1 : ℂ)).G
abbrev Shape.FrameMat := Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℂ
abbrev Shape.J₁ := (𝔰.middleGram (1 : ℂ)).splitGram
abbrev Shape.frameCols := inclMatrix ℂ 𝔰.besselFrame
abbrev Shape.dualFrameCols := inclMatrix ℂ (Fin.snoc eStar (𝔰.indexX₀ 𝔰.k₀))
abbrev Shape.isotropicCols := inclMatrix ℂ (.inl : _ → 𝔰.BesselIndex)
abbrev Shape.definiteCols := inclMatrix ℂ 𝔰.indexX₀
abbrev Shape.dualCols := inclMatrix ℂ (eStar : _ → 𝔰.BesselIndex)
abbrev Shape.zCol := inclMatrix ℂ fun _ : Unit ↦ 𝔰.z
abbrev Shape.UnipotentParams := Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ × Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ
variable {𝔰} (y : 𝔰.G₁) (a : Fin (𝔰.ϱ + 1)) {j}
def frameVector : EuclideanSpace ℂ 𝔰.BesselIndex := .toLp 2 (y⁻¹.1 · (𝔰.besselFrame a))
abbrev realFrameGram := (𝔰.middleGram 1).frameGram y.1.1
@[simps apply_fst apply_snd] def freeEntries (p : Fin 𝔰.ϱ × 𝔰.BesselIndex → _) :
    Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ →L[ℝ] (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ) where
  toFun M := (fun x ↦ M (.inl x.1.1) x.1.2, fun a ↦ (M (.inl a) (eStar a)).im)
  map_add' := by simp [funext_iff]
  map_smul' := by simp [funext_iff]
@[simp] def IsFreeEntry₀ (x : _ × _) := (∃ i, x.2 = 𝔰.indexX₀ i) ∨ ∃ b > x.1, x.2 = eStar b
def IsFreeEntry :
  Fin 𝔰.ϱ × 𝔰.BesselIndex → Prop | (a, .inl b) | (a, eStar b) => a < b | (_, .inr (.inl _)) => True
attribute [simp] IsFreeEntry.eq_1 IsFreeEntry.eq_2 IsFreeEntry.eq_3
def actOnCols {m} [Fintype m] (C : Matrix 𝔰.BesselIndex m ℂ) (h :
  Matrix m m ℂ) := 1 - C * Cᴴ + C * h * Cᴴ
abbrev UpperEntries j := {p : Fin j × _ // p.1 < p.2} → ℂ
def unitriMatrix (x : UpperEntries j) := of fun a b ↦ dite (a < b) (x ⟨(a, b), ·⟩) fun _ ↦
  ite (a = b) 1 0
@[fun_prop] lemma continuous_unitriMatrix :
  Continuous (@unitriMatrix j) := by unfold unitriMatrix; continuity
instance isHermInvolution_J₁ : IsHermInvolution 𝔰.J₁ := by constructor <;> apply
  ext <;> simp [eq_comm, splitGram, middleGram, mul_apply]
instance : IsHermUnit 𝔰.J₁ := ⟨IsHermInvolution.isHermitian, IsHermInvolution.isUnit⟩
end
open Matrix MeasureTheory Measure Complex MeasurableEquiv Fin
attribute [local instance] sigmaFinite_map
lemma lintegral_bruhat_coords {n f} (hf : Measurable f) : ∫⁻ c : Fin n → ℂ,
  (∏ a : Fin n, ‖c a‖ₑ ^ (4 * a.rev.1))
  * ∫⁻ q : _ × _, f ((unitriMatrix q.1)ᴴ * diagonal c * unitriMatrix q.2).row = ∫⁻ Z, f Z := by
  have A := volume_measurePreserving_arrowProdEquivProdArrow ℂ ℂ
  induction' n with n ih <;> simp (disch := with_unfolding_all fun_prop [row]) only [volume,
    lintegral_map, lintegral_prod, ← (measurePreserving_piFinSuccAbove _ 0).symm.2,
    ← pi_map_pi, ← (measurePreserving_arrowProdEquivProdArrow ..).symm.2]
  simp [empty_eq]
  apply lintegral_congr_ae ((ae_ne _ 0).mono fun c _ ↦ .symm ?_)
  erw [lintegral_eq_det_mul (c • 1), lintegral_lintegral_swap, lintegral_eq_det_mul
    (c • 1), lintegral_lintegral, ← funext fun u ↦ lintegral_add_left_eq_self _
    (u.1 · • c • u.2), lintegral_lintegral_swap, ← ih]
  simp [consEquiv, prod_univ_succ, ← lintegral_const_mul']
  ring_nf; congr!
  erw [lintegral_lintegral, lintegral_lintegral, ← (((A _).prod ((A _).comp (volume_preserving_pi
    fun _ ↦ conjLIE.measurePreserving.prod (.id _)))).comp ((measurePreserving_sumPiEquivProdPi
    _).comp ((measurePreserving_piCongrLeft _ (.ofBijective ((⟨·.1.map succ succ, by grind⟩) ⊕ᵥ
    (⟨⟨0, succ ·⟩, by simp⟩)) (.of_existsUnique _ ?_))).trans (A _)).symm)).lintegral_comp
    (α := UpperEntries _ × _)]
  congr!
  all_goals first | fun_prop [row] | simp [funext_iff, diagonal, sumPiEquivProdPi, mul_apply,
    unitriMatrix,
    piCongrLeft, arrowProdEquivProdArrow, forall_fin_succ, sum_univ_succ, ExistsUnique]; grind
open MatMul Norms.L2Operator
attribute [local simp] forall_fin_succ' Matrix.mul_apply frameMatrix inclMatrix
  val_toBesselH_apply_coe
variable {𝔰 : Shape} {s u : 𝔰.G₁} {l m n o : Type} [Fintype n] {e : m → n} {e' : l → n}
  (q : 𝔰.UnipotentParams) {M : Matrix m o ℂ} (x : UpperEntries 𝔰.n) {A : Matrix l n ℂ} {B :
  Matrix n m ℂ}
lemma conjTranspose_inclMatrix_mul (M : Matrix _ l ℂ) : (inclMatrix ℂ e)ᴴ * M =
  M.submatrix e id := by aesop
lemma inclMatrix_gram_eq_zero : (∀ i j, e' i ≠ e j) →
  (inclMatrix ℂ e')ᴴ * inclMatrix ℂ e = 0 := by aesop
lemma inclMatrix_gram_eq_one : (∀ i j, e i = e j → i = j) →
  (inclMatrix ℂ e)ᴴ * inclMatrix ℂ e = 1 := by aesop
variable [Fintype m]
lemma mul_mul_eq_of_mul_eq {C} : A * B = C → A * (B * M) = C * M := by aesop
lemma inclMatrix_gram_mul_eq_zero : (∀ i j, e' i ≠ e j) →
  (inclMatrix ℂ e')ᴴ * (inclMatrix ℂ e * M) = 0 := by aesop
lemma inclMatrix_gram_mul_eq_self (h : ∀ i j, e i = e j → i = j) : (inclMatrix ℂ e)ᴴ *
  (inclMatrix ℂ e * M) = M := by simp [↓mul_mul_eq_of_mul_eq (inclMatrix_gram_eq_one h)]
lemma J₁_eq : 𝔰.J₁ = 𝔰.isotropicCols * 𝔰.dualColsᴴ + 𝔰.dualCols * 𝔰.isotropicColsᴴ +
  𝔰.definiteCols * 𝔰.definiteColsᴴ - 𝔰.zCol * 𝔰.zColᴴ := by aesop
attribute [local simp] FI.level Fin.ne_of_gt J₁_eq inclMatrix_gram_mul_eq_zero
  inclMatrix_gram_mul_eq_self mem_besselU mem_besselU0_iff unitriMatrix
def unipotentOf : 𝔰.G₁ := U.of IsHermUnit.isUnit (1 + 𝔰.isotropicCols * q.1 * 𝔰.definiteColsᴴ -
  𝔰.definiteCols * q.1ᴴ * 𝔰.dualColsᴴ + 𝔰.isotropicCols *
  (skewOfReal q.2 - (2⁻¹ : ℂ) • (q.1 * q.1ᴴ)) * 𝔰.dualColsᴴ) (by simp [-inclMatrix]; module)
abbrev embedH h := (toBesselH 𝔰 1 h : 𝔰.G₁)
lemma norm_embedH_mul h : ‖(embedH h * u).1.1‖ = ‖u.1.1‖ := CStarRing.norm_mem_unitary_mul _
    (by simp [unitary, star, ← U.inv_val_eq_conjTranspose])
def liftUnitri : 𝔰.G₁ := let v := (unitriMatrix x).submatrix castSucc fun _ : Unit ↦ 𝔰.top
  let a := (unitriMatrix x).submatrix castSucc castSucc
  U.of IsHermUnit.isUnit (𝔰.definiteCols * 𝔰.definiteColsᴴ + 𝔰.zCol * 𝔰.zColᴴ + 𝔰.isotropicCols *
    (a * 𝔰.isotropicColsᴴ + v * 𝔰.zColᴴ) + (𝔰.dualCols + 𝔰.zCol * vᴴ + (2⁻¹ : ℂ) •
    (𝔰.isotropicCols * v * vᴴ)) * a.adjugateᴴ * 𝔰.dualColsᴴ) (by simp [det_eq_one_of_unitriangular
    (lev := id) (Z := a) (by simp [a]; lia), adjugate_conjTranspose, mul_mul_eq_of_mul_eq
    (mul_adjugate _), mul_mul_eq_of_mul_eq (adjugate_mul _), -inclMatrix]; module)
attribute [local simp ←] ext_iff
attribute [simps (attr := local simp) (rhsMd := .default) -isSimp coe_val,
  irreducible] liftUnitri unipotentOf
lemma coe_embedH h : (embedH h).1.1 = actOnCols 𝔰.definiteCols h := by simp [actOnCols]
lemma unipotentOf_mem_besselU0 : unipotentOf q ∈ besselU0 := by simp; lia
@[simp] lemma frameMatrix_liftUnitri : frameMatrix (liftUnitri x) = unitriMatrix x := by simp; grind
lemma liftUnitri_mem_besselU : liftUnitri x ∈ besselU := by simp; grind [by simpa using
  (unitriGroup_dual_row (s := liftUnitri x) (by simp [mem_unitriGroup]; lia) <| isLt ·)]
lemma exists_mul_unipotentOf_dualCols_eq {B} (a : (s.1.1 * 𝔰.frameCols)ᴴ * 𝔰.J₁ * B = inclMatrix ℂ
  castSucc) (b : Bᴴ * 𝔰.J₁ * B = 0) : ∃ q, (s * unipotentOf q).1.1 * 𝔰.dualCols = B := by
  obtain ⟨B, rfl⟩ : ∃ C, B = s.1.1 * C := ⟨s⁻¹.1.1 * B, by simp⟩
  use (-Bᴴ * 𝔰.definiteCols, skewCoords (skewAdjointPart ℝ B.toRows₁)); convert! Matrix.mul_assoc ..
  simp_all [↓U.gram_invariant, -map_sub]; grind
lemma exists_embedH_eq_of_fix_frameCols (H : s.1.1 * 𝔰.frameCols = 𝔰.frameCols) : ∃ q h,
  s * unipotentOf q = embedH h := (@exists_mul_unipotentOf_dualCols_eq _ s 𝔰.dualCols
  (by simp [↓H]) (by simp)).imp fun q _ ↦ have := (unipotentOf_mem_besselU0 q).2
  exists_toBesselH_eq (by simp_all [mem_floorGroup, -val_unipotentOf_coe])
lemma mem_besselU0_iff_unipotentOf : u ∈ besselU0 ↔ ∃ q, u = unipotentOf q :=
  ⟨(fun H ↦ (exists_embedH_eq_of_fix_frameCols (by simp_all [-inv_mem_iff]; grind)).imp fun q ⟨_,
  e⟩ ↦ inv_mul_eq_one.1 (e ▸ by ext : 2; simpa [e] using mul_mem H (unipotentOf_mem_besselU0 q))) ∘
  inv_mem, by grind [unipotentOf_mem_besselU0]⟩
def Shape.besselHaar₀ := volume.map (β := besselU0) (⟨_, @unipotentOf_mem_besselU0 𝔰 ·⟩)
def Shape.besselHaar := (volume.prod 𝔰.besselHaar₀).map (β := besselU) fun q ↦
  ⟨_, mul_mem q.2.2.1 (liftUnitri_mem_besselU q.1)⟩
abbrev besselQuotMeasure : Measure 𝔰.G₁ := orbitMeasure 𝔰.besselHaar volume
