import Lib.General.NumberTheory.UpsilonValues
import Lib.Weil.Periods.DegreeAndUnipotent
seal Finset.univ Finset.sum Finset.prod
noncomputable section
open Fintype Matrix
variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] {s s' ε ε' N} {V : Space E ι ε} {V' : Space E ι' ε'} (Y : Grading V N X s) (Y' : Grading V' N X' s') (d : ι' → ℤ)
def Grading.stringReversal i := Y.indexEquiv ((Y.indexEquiv.symm i).map id .rev)
def Grading.stringMap := (gradedBlocks Y'.indexEquiv Y.indexEquiv 0 (.of fun b a ↦ ite (b.1 = a) (ite (Odd s ↔ 2 * a + 1 < s) 1 ↑Y.c * ite (2 * a + 1 = s) (-N) 1) 0)).map toAdele
abbrev Grading.AgreesWithT (w : Matrix ..) := ∀ b a, 0 < Y.gradeOf a → Y'.gradeOf b < Y.gradeOf a → w b a = Y.stringMap Y' b a
abbrev Grading.mapDegree (r : _ × _) := d r.1 - Y.gradeOf r.2
def Grading.nonnegMaps : AddSubgroup (ratMatrices E ι' ι) := by use! {w | HasDegreeGe d Y.gradeOf 0 w.1} <;> simp_all [HasDegreeGe]
def Grading.shift := (gradedBlocks Y.indexEquiv Y.indexEquiv 0 (.of fun a b ↦ ite (a.1 = b + 1) (Y.c * ite (2 * b + 1 = s) (-N) (ite (2 * a = s) (-N * Y.c) 1)) 0)).map toAdele
structure Grading.IsGeneric [WeilData E] (P : G E ε → ℂ) where
 continuous : Continuous P
 rat_mul : Y.ratBessel.FixesLeft P
 unipotent_mul g : ∀ n ∈ Y.unipotent, HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix n - 1) → P (n * g) = stdAddChar E ((WeilData.j / 2 : E) * (Y.shift * V.ratCoordMatrix n).trace) * P g
section
open MatMul
variable [Fintype X] [Fintype X'] (V₁ : Space E ι ε) (V'' : Space E ι' ε') (Y₁ : Grading V N X s) {g}
def Space.formAdjoint (y : Matrix ι' ι (𝔸 E)) := V₁.J⁻¹.map toAdele * yᴴ * V''.J.map toAdele
attribute [local simp] HasDegreeGe Grading.stringReversal Space.formAdjoint Space.map_J_inv_mul_map_J mul_sub sub_mul
lemma Space.formAdjoint_formAdjoint x : V''.formAdjoint V₁ (V₁.formAdjoint V'' x) = x := by simp [conjTranspose_nonsing_inv, conjTranspose_J, ← Matrix.mul_assoc, x.mul_assoc]
lemma Space.formAdjoint_ratCoordMatrix_mul g y : V''.formAdjoint V₁ (V₁.ratCoordMatrix g * y) = V''.formAdjoint V₁ y * V₁.ratCoordMatrix g⁻¹ := by simp [ratCoordMatrix, ← U.form_mul_inv_eq]
omit [Fintype X] in
@[simp] lemma Grading.gradeOf_stringReversal : ∀ i, Y₁.gradeOf (Y₁.stringReversal i) = -Y₁.gradeOf i := by simp +arith [reindex_equiv Y₁.indexEquiv]
lemma Grading.map_gradedGram_mul_apply {R κ : Type} {M} [CommRing R] (f : E →+* R) (A : Matrix ι' κ R) : ∀ i p, ((gradedGram Y'.indexEquiv M).map f * A) i p = f (gradedGram Y'.indexEquiv M i (Y'.stringReversal i)) * A (Y'.stringReversal i) p := by simp [gradedGram, mul_apply, reindex_equiv Y'.indexEquiv, apply_ite f, ← Fin.rev_eq_iff]
lemma Grading.vecMul_J_apply y : ∀ a, (y ᵥ* V.J.map toAdele) a = y (Y.stringReversal a) * gradedGram Y.indexEquiv N (Y.stringReversal a) a := by simp [Y.2, gradedGram, vecMul_apply_eq_sum, reindex_equiv Y.indexEquiv, apply_ite toAdele]
@[simp] lemma Grading.J_inv_eq_gradedGram : V.J⁻¹ = gradedGram Y.indexEquiv N⁻¹ := inv_eq_left_inv (by simp [Y.2, gradedGram, entrywise, reindex_equiv Y.indexEquiv]; grind [Grading])
lemma Grading.formAdjoint_apply y a b : V.formAdjoint V' y a b = gradedGram Y.indexEquiv N⁻¹ a (Y.stringReversal a) * star (y (Y'.stringReversal b) (Y.stringReversal a)) * gradedGram Y'.indexEquiv N (Y'.stringReversal b) b := (Y'.vecMul_J_apply ..).trans (by simp [Y.J_inv_eq_gradedGram, map_gradedGram_mul_apply])
lemma Grading.mem_besselGroup_iff : g ∈ Y₁.besselGroup ↔ ∀ i k, Y₁.gradeOf i ≤ Y₁.gradeOf k → (Y₁.indexEquiv.symm i).isRight ∨ (Y₁.indexEquiv.symm k).isRight → V.ratCoordMatrix g i k = (1 : Matrix ..) i k := ⟨(by grind [inv_mem ·, congrFun₂ (by
 simpa using V.formAdjoint_ratCoordMatrix_mul V g⁻¹ 1 : V.formAdjoint V (_ - 1) = _ - 1) · ·,
 stringReversal, formAdjoint_apply, star_zero,
 gradeOf_stringReversal, Matrix.sub_apply, ← Y₁.mem_besselGroup_iff_sub_one.1]), by simp_all
 [mem_besselGroup_iff_sub_one, reindex_equiv Y₁.indexEquiv]⟩
lemma Grading.hasDegreeGe_zero_of_mem_besselGroup : g ∈ Y₁.besselGroup → HasDegreeGe Y₁.gradeOf Y₁.gradeOf 0 (V.ratCoordMatrix g) := by simp [mem_besselGroup_iff, reindex_equiv Y₁.indexEquiv]; grind
lemma Grading.exists_besselGroup_proj : ∃ p : Y.besselGroup →* _, Continuous p ∧ (∀ r, r * (Y.inclX (p r))⁻¹ ∈ Y.unipotent) ∧ (∀ a, p ⟨_, Y.inclX_mem_besselGroup a⟩ = a) ∧ (∀ r, ↑r ∈ Y.unipotent ↔ p r = 1) ∧ ∀ r, r.1 ∈ Y.ratBessel → p r ∈ (stdSpace ..).Γ := by refine ⟨.mk' (fun r ↦ G.toUnitary.symm (U.of ?_ (toBlocks₁₁ ((V.ratCoordMatrix r).onFun Y.indexEquiv)) (flip .trans (congr(toBlocks₁₁ ($((V.toRatCoords r).2).onFun Y.indexEquiv)).trans ?_) (r.rec ?_)))) ?_, G.continuous_iff.2 ?_, .symm ⟨?h, fun _ ↦ ((?h.2.1 _).2 ((MonoidHom.div_mem_ker_iff _).2 (?h.1 _).symm) :)⟩⟩ <;> simp +contextual [G.mat, gradedGram, entrywise, Space.mem_Gamma_iff_ratCoordMatrix, reindex_equiv Y.indexEquiv, ← (stdSpace ..).isEmbedding_ratCoordMatrix.2.eq_iff, mem_besselGroup_iff, Y.2, ratCoordMatrix_inclX, toBlocks₁₁] <;> first | fun_prop | simp [Space.ratCoordMatrix]; grind -funext [star_zero, sum_eq_zero]
lemma Grading.exists_unipotent_mul_inclX : g ∈ Y.besselGroup → ∃ n ∈ Y.unipotent, ∃ a, g = n * Y.inclX a := (⟨_, Y.exists_besselGroup_proj.choose_spec.2.1 ⟨g, ·⟩, _, eq_mul_of_div_eq rfl⟩)
end
def Space.ratCoordMatrixFin (g : Gf E ι) := V.xFin.1 * g * V.xFin⁻¹
lemma Space.ratCoordMatrix_eq g : V.ratCoordMatrix g = V.x * g.mat * V.x⁻¹ := rfl
lemma Space.ratCoordMatrixFin_snd g : V.ratCoordMatrixFin g.2 = (V.ratCoordMatrix g).map (RingHom.snd ..) := by simp_rw [ratCoordMatrix_eq, Matrix.map_mul]; rfl
lemma Space.ratCoordMatrix_inr g a b : V.ratCoordMatrix (1, g) a b = ((1 : Matrix ..) a b, V.ratCoordMatrixFin g a b) := by simpa [ratCoordMatrix_eq, mul_apply, Prod.fst_sum, funext_iff, apply_ite, Prod.ext_iff, ratCoordMatrixFin_snd (1, g)] using congr(($V.x.mul_inv a b).1)
lemma Space.gram_xFin : V.xFin.1ᴴ * V.J.map (↑) * V.xFin.1 = 1 := by simpa [stdForm, -RingHom.coe_snd] using! congr(map $V.gram_point (RingHom.snd ..))
variable (Y₁ : Grading V N ι' s) (h)
namespace Grading
def besselFin := Y.besselGroup.comap (.inr ..)
variable [Fintype X] in
def inclXFin := (MonoidHom.snd ..).comp (Y.inclX.comp (.inr ..))
attribute [local simp] besselFin inclXFin ratCoordMatrix_inclX mem_besselGroup_iff Space.ratCoordMatrix_inr Space.ratCoordMatrixFin_snd
lemma ratCoordMatrixFin_inclXFin : V.ratCoordMatrixFin (Y₁.inclXFin h) = gradedBlocks Y₁.indexEquiv Y₁.indexEquiv h 1 := ext (by simp [reindex_equiv Y₁.indexEquiv, apply_ite])
lemma inclX_inr : Y₁.inclX (1, h) = (1, Y₁.inclXFin h) := V.isEmbedding_ratCoordMatrix.2 (ext (by simp [reindex_equiv Y₁.indexEquiv]; aesop))
open MatMul
lemma snd_mem_besselFin {g} : g ∈ Y₁.besselGroup → g.2 ∈ Y₁.besselFin := by aesop
instance : IsClosed (SetLike.coe Y.besselFin) := Y.instIsClosedGCoeSubgroupRg.preimage_of_continuous (f := (1, ·))
