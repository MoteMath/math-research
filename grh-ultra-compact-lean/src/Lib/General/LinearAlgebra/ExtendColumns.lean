import Lib.General.Groups.ValuationPair
noncomputable section
open Fin Finset LinearEquiv Matrix
structure Shape where (ϱ : ℕ) (κ : Type) [fintypeIndex : Fintype κ] (k₀ : κ)
attribute [instance] Shape.fintypeIndex
variable {R : Type*} [CommRing R] (𝔰 : Shape) {S} [Fintype S] {a b c : S → Type} (A : ∀ s, Matrix (a s) (b s) R) {R'} [CommRing R'] (φ : R →+* R') {μ}
def kroneckerPi := of fun β α : ∀ _, _ ↦ ∏ s, A s (β s) (α s)
lemma kroneckerPi_mul [∀ s, Fintype (b s)] (B : ∀ s, Matrix (b s) (c s) R) : kroneckerPi (fun s ↦ A s * B s) = kroneckerPi A * kroneckerPi B := by simp [kroneckerPi, entrywise, prod_univ_sum]
@[simp] lemma kroneckerPi_one : @kroneckerPi R _ S _ a a (fun _ ↦ 1) = 1 := Matrix.ext (by simp [kroneckerPi, prod_boole, funext_iff])
lemma kroneckerPi_map : kroneckerPi (A · |>.map φ) = (kroneckerPi A).map φ := Matrix.ext (by simp [kroneckerPi])
def wave c := (c - starRingEnd ℂ c).exp
@[simp] lemma norm_wave c : ‖wave c‖ = 1 := by simp [wave]
abbrev SplitIndex ϱ (μ : Type) := Fin ϱ ⊕ μ ⊕ Fin ϱ
abbrev Shape.MiddleIndex := 𝔰.κ ⊕ Unit
abbrev Shape.BesselIndex := SplitIndex 𝔰.ϱ 𝔰.MiddleIndex
abbrev Shape.n := 𝔰.ϱ + 1
abbrev Shape.indexX₀ (j : 𝔰.κ) : 𝔰.BesselIndex := .inr (.inl (.inl j))
abbrev Shape.z : 𝔰.BesselIndex := .inr (.inl (.inr ()))
abbrev Shape.top := last 𝔰.ϱ
abbrev Shape.Form R := Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex R
abbrev Shape.k := Fintype.card 𝔰.κ
abbrev Shape.r := Fintype.card 𝔰.BesselIndex
def FI.level {ϱ μ} : SplitIndex ϱ μ → ℕ := (↑) ⊕ᵥ ((fun _ ↦ ϱ) ⊕ᵥ (2 * ϱ - ·))
@[match_pattern] abbrev eStar {ϱ} (a : Fin ϱ) : SplitIndex ϱ μ := .inr (.inr a)
abbrev hyperbolicGram σ (T : Matrix μ μ R) : Matrix (σ ⊕ μ ⊕ σ) (σ ⊕ μ ⊕ σ) R := fromBlocks 0 (fromCols 0 1) (fromRows 0 1) (T.fromBlocks 0 0 0)
def Shape.besselFrame : Fin (𝔰.ϱ + 1) → 𝔰.BesselIndex := snoc .inl 𝔰.z
variable {n : Type*} [Fintype n] {α : Type*} [LinearOrder α] (lev : n → α) {r : n → n → Prop}
def Shape.middleGram (N : R) : 𝔰.Form R := fromBlocks 1 0 0 (of fun _ _ ↦ -N)
def Shape.Form.splitGram {𝔰 : Shape} (T : 𝔰.Form R) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R := hyperbolicGram _ T
def parabolic : Subgroup (GL n R) := ⟨⟨⟨{g | g.1.BlockTriangular lev}, .mul⟩, blockTriangular_one⟩, by simp_all [blockTriangular_inv_of_blockTriangular]⟩
def blockHom a : parabolic (R := R) lev →* GL {i // lev i = a} R := .toHomUnits ⟨⟨(·.1.1.toSquareBlock _ a), (toBlock_one_self _).trans one_classical⟩, fun g h ↦ Matrix.ext fun i j ↦ sum_congr_set {x | _} _ _ (by tauto) (by grind [@g.2 i, @h.2 ·, not_lt])⟩
variable {lev : n → α} {𝔰 : Shape} {Z : Matrix n n R} (T : 𝔰.Form R) {T' : 𝔰.Form R'} [StarRing R'] {k} (W : Type) [CommRing W] [IsLocalRing W] (τ : Fin k → ℕ) (ι : S ↪ n)
def agreeWithOneOn (r : n → n → Prop) R [CommRing R] (h : ∀ i k j, r i j → r i k ∨ r k j := by grind) := Subgroup.ofDiv {u : GL n R | ∀ i j, r i j → u i j = (1 : Matrix ..) i j} ⟨1, by simp⟩ fun x a y b i j e ↦ have := (parabolic (if r i · then 0 else 1)).2 (x := y) fun _ ↦ (by grind [one_apply_ne]); (sum_congr rfl fun k _ ↦ by grind [@this k j]).trans congr($y.mul_inv i j)
abbrev unitriangular (lev : n → α) R [CommRing R] := agreeWithOneOn (lev · ≥ lev ·) R
lemma mem_agreeWithOneOn {h x} : x ∈ agreeWithOneOn r R h ↔ ∀ a b : n, r a b → x a b = (1 : Matrix ..) a b := .rfl
attribute [simp] Subgroup.copy mem_agreeWithOneOn
lemma conj_mem_unitriangular {u d} (t : d.1.BlockTriangular lev) (a : u ∈ unitriangular lev R) : d⁻¹ * u * d ∈ unitriangular lev R := fun i j e ↦ by simp_rw [← d.inv_mul, ← congr($(d⁻¹.1.mul_one) * d.1), Units.val_mul, Matrix.mul_apply, sum_mul]; congr! 2 with l _ k; grind [(parabolic _).2 t (j := k), @t l, a k, not_le]
lemma det_eq_one_of_unitriangular (h : ∀ a b, lev b ≤ lev a → Z a b = (1 : Matrix ..) a b) : Z.det = 1 := by simp [show Z.BlockTriangular lev by grind [BlockTriangular, one_apply_ne].det, show Z.toSquareBlock lev = 1 by aesop (add simp toSquareBlock_def)]
def leadingMinor {i} Z l := ((submatrix Z (castLE (@is_le i l)) (castLE l.is_le)).det : R)
abbrev Filling.scaleAt (p : R) (k₀ : μ) := diagonal (if · = k₀ then p else 1)
abbrev frameImage (γ : Matrix 𝔰.BesselIndex _ R) := γ.submatrix id 𝔰.besselFrame
def Shape.Form.frameGram (γ : Matrix 𝔰.BesselIndex _ R) := (T.splitGram * γ).submatrix 𝔰.besselFrame 𝔰.besselFrame
abbrev Shape.Form.G [StarRing R] := U T.splitGram
def frameMatrix (γ : T'.G) := γ.1.1.submatrix 𝔰.besselFrame 𝔰.besselFrame
def Shape.Form.besselU := (unitriangular FI.level R').subgroupOf T'.G
def Shape.Form.besselU0 := T'.besselU ⊓ (agreeWithOneOn (fun _ j ↦ j ∈ Set.range 𝔰.besselFrame) R').subgroupOf _
export Shape (besselFrame middleGram)
export Shape.Form (splitGram frameGram besselU besselU0)
def levi := (agreeWithOneOn (τ · ≠ τ ·) W).copy {g | ∀ i j, τ i ≠ τ j → g i j = 0} (by ext; simp; grind)
def parahoric := (parabolic (OrderDual.toDual ∘ τ)).comap (GeneralLinearGroup.map (IsLocalRing.residue W))
lemma inclMatrix_mulVecLin_injective k [Field k] : (⇑(inclMatrix k ι).mulVecLin).Injective := mulVec_injective_iff.2 ((linearIndependent_cols_of_isUnit isUnit_one).comp ι ι.2)
lemma exists_GL_mul_inclMatrix {k} [Field k] {b} (h : (⇑b.mulVecLin).Injective) : ∃ u : GL n k, u.1 * inclMatrix k ι = b := (Submodule.exists_linearEquiv_restrict_eq ((ofInjective _ (inclMatrix_mulVecLin_injective ι k)).symm ≪≫ₗ ofInjective _ h)).imp' (.mk'' ·.toMatrix' (by simp [← coe_det])) (by simp_all [ext_iff_mulVec, ← mulVec_mulVec, ↓reindex_equiv (ofInjective ..), inclMatrix_mulVecLin_injective])
