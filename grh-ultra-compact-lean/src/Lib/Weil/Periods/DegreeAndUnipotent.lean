import Lib.Adelic.Unitary.SpaceBasic
noncomputable section
open Matrix
variable {R X X' ι ι' : Type _} {s : ℕ} {s' : ℕ} (a) [CommRing R] {E : Type*} [Field E] [CMType E] [Fintype ι] [Fintype X] (e' : X' ⊕ Fin s' ≃ ι') (e : X ⊕ Fin s ≃ ι) {ε : ι → ℤˣ} {N : E} (V : Space E ι ε)
abbrev gradedBlocks A B := (fromBlocks (α := R) A 0 0 B).submatrix e'.symm e.symm
def gradedGram (N : R) := gradedBlocks e e 1 (of fun a b ↦ ite (a = b.rev) (ite (a = b) (-N) 1) 0)
attribute [simp] stdForm_one
def Space.ratCoordMatrix : G E ε →* Matrix ι ι (𝔸 E) := by use! (V.toRatCoords ·) <;> simp
structure Grading N X s where
 indexEquiv : X ⊕ Fin s ≃ ι
 gram_eq : V.J = gradedGram indexEquiv N
 N_spec : N ≠ 0 ∧ star N = N
 c : {c : E // c ≠ 0 ∧ star c = c}
namespace Grading
variable {V} (Y : Grading V N X s)
@[local simp] def gradeOf i := ((Y.indexEquiv.symm i).elim 0 (s - 1 - 2 * ·.1) : ℤ)
omit [Fintype X] in
@[simp] lemma gradeOf_inl a (Y : Grading V N X s) : Y.gradeOf (Y.indexEquiv (.inl a)) = 0 := by simp
omit [Fintype X] in
@[simp] lemma gradeOf_inr a (Y : Grading V N X s) : Y.gradeOf (Y.indexEquiv (.inr a)) = s - 1 - 2 * a := by simp
def unipotent := (unitriangular (-Y.gradeOf ·) _).comap V.ratCoordMatrix.toHomUnits
def inclX := ((U.reindex Y.indexEquiv (by erw [Y.2, ← submatrix_map]; aesop)).trans V.toRatCoords.symm).toMonoidHom.comp ((U.sum rfl).comp (G.toUnitary (s := 1).toMonoidHom.prod 1))
lemma ratCoordMatrix_inclX h : V.ratCoordMatrix (Y.inclX h) = gradedBlocks Y.indexEquiv Y.indexEquiv h.mat 1 := by simp [Space.ratCoordMatrix, inclX]; rfl
def besselGroup := (agreeWithOneOn (fun i k ↦ ite (Y.indexEquiv.symm k).isRight 0 1 ≤ Y.gradeOf k ∧ Y.gradeOf i ≤ Y.gradeOf k) _).comap V.ratCoordMatrix.toHomUnits
abbrev ratBessel := V.Γ ⊓ Y.besselGroup
end Grading
variable {E : Type*} [Field E] [CMType E] {ι X : Type _} [Fintype ι] [Fintype X] {s : ℕ} {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} (Y : Grading V N X s) {g : G E ε} {ι' : Type _} [Fintype ι']
def HasDegreeGe {R ι ι'} [Zero R] (w' w : _ → ℤ) d (x : Matrix ι' ι R) := ∀ b a, w' b < w a + d → x b a = 0
lemma HasDegreeGe.mul {R ι κ} [CommRing R] {w'' w' w d d' y x} (h : @HasDegreeGe R ι' κ _ w'' w' d x) (h' : @HasDegreeGe R ι ι' _ w' w d' y) {e} (he : e ≤ d + d' := by omega) : HasDegreeGe w'' w e (x * y) := by grind [HasDegreeGe, Matrix.mul_apply, Finset.sum_eq_zero]
@[fun_prop] lemma Space.isEmbedding_ratCoordMatrix : Topology.IsEmbedding V.ratCoordMatrix := (isHomeomorph_smul (ConjAct.toConjAct V.x)).isEmbedding.comp G.isClosedEmbedding_mat.1
lemma Space.mem_Gamma_iff_ratCoordMatrix : g ∈ V.Γ ↔ ∀ i k, V.ratCoordMatrix g i k ∈ toAdele.range := mem_Γ_iff_range _
@[simp] lemma ratCoordMatrix_stdSpace g : (stdSpace E X).ratCoordMatrix g = g.mat := (mul_one _).trans (one_mul _)
namespace Grading
attribute [local simp] HasDegreeGe ratCoordMatrix_inclX Space.mem_Gamma_iff_ratCoordMatrix
omit [Fintype X] in
@[simp] lemma mem_unipotent : g ∈ Y.unipotent ↔ HasDegreeGe Y.gradeOf Y.gradeOf 1 (V.ratCoordMatrix g - 1) := forall₂_congr (by simp)
omit [Fintype X] in
lemma hasDegreeGe_two_of_odd : Odd s → g ∈ Y.unipotent → HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix g - 1) := by simp [reindex_equiv Y.indexEquiv]; grind
omit [Fintype X] in
@[local simp] lemma mem_besselGroup_iff_sub_one : g ∈ Y.besselGroup ↔ ∀ i k, ite (Y.indexEquiv.symm k).isRight 0 1 ≤ Y.gradeOf k → Y.gradeOf i ≤ Y.gradeOf k → (V.ratCoordMatrix g - 1) i k = 0 := forall₂_congr (by simp)
lemma inclX_mem_besselGroup a : Y.inclX a ∈ Y.besselGroup := by simp [reindex_equiv Y.indexEquiv]
omit [Fintype X] in
lemma unipotent_le_besselGroup : Y.unipotent ≤ Y.besselGroup := by aesop_cat
instance instIsClosedGCoeSubgroupRg : IsClosed (SetLike.coe Y.besselGroup) := isClosed_of_closure_subset fun _ h i k e ↦ closure_singleton.le (map_mem_closure (f := (V.ratCoordMatrix · i k)) (by fun_prop) h fun _ ↦ (· i k e))
@[fun_prop] lemma continuous_inclX : Continuous Y.inclX := V.isEmbedding_ratCoordMatrix.continuous_iff.2 (by simp [Function.comp_def]; fun_prop)
lemma inclX_mem_ratBessel {a} : a ∈ (stdSpace ..).Γ → Y.inclX a ∈ Y.ratBessel := by aesop (add simp (reindex_equiv Y.indexEquiv))
