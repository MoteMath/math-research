import Lib.General.LinearAlgebra.ExtendColumns
import Lib.General.Analysis.ZpowSum
open Matrix Pi Submodule
variable {k l m n} [Field k] [Fintype l] [Fintype m] [Fintype n] {x : Matrix m n k}
lemma exists_generalized_inverse {M N} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N] (f : M →ₗ[k] N) : ∃ s : N →ₗ[k] M, ∀ x, f (s (f x)) = f x := (f.rangeRestrict.exists_rightInverse_of_surjective (by simp)).rec fun g h ↦ g.exists_extend.imp fun | _, rfl => (congr($h ⟨_, ·, rfl⟩))
omit [Fintype l] [Fintype m] in
lemma Filling.exists_mul_eq_of_col_mem_range {y} (h : ∀ b, y.col b ∈ x.mulVecLin.range) : ∃ s : Matrix n l k, x * s = y := ⟨_, ext_col (h · |>.choose_spec)⟩
lemma exists_mul_add_mul_eq {y : Matrix n l k} (h : x.mulVecLin.ker ≤ y.mulVecLin.range) : ∃ (e : Matrix l n k) (b : Matrix n m k), y * e + b * x = 1 := (exists_generalized_inverse x.toLin').rec fun b _ ↦ (Filling.exists_mul_eq_of_col_mem_range (by simp_all [LE.le, ← toLin'_apply, ← mulVec_single_one])).imp fun _ ↦ (⟨b.toMatrix', add_eq_of_eq_sub ·⟩)
lemma exists_mulVec_eq_of_annihilator {F ι α} [Field F] [Fintype ι] [Fintype α] (P P' : Matrix ι α F) (s s' : Set α) X Y (H : ∀ l, (∀ b ∈ s, (l ᵥ* P) b = 0) → (∀ b ∈ s', (l ᵥ* P') b = 0) → l ᵥ* P ⬝ᵥ X = l ᵥ* P' ⬝ᵥ Y) : ∃ x y, P *ᵥ x = P' *ᵥ y ∧ (∀ b ∉ s, x b = X b) ∧ ∀ b ∉ s', y b = Y b := have ⟨(u, v), _⟩ : P *ᵥ X - P' *ᵥ Y ∈ map (P'.toLin'.coprod (-P).toLin') ((spanSubset F s').prod (spanSubset F s)) := Not.imp_symm exists_le_ker_of_notMem (by simp [(dotProductEquiv ..).surjective.forall, map_span_le, spanSubset, dotProduct_mulVec]; grind [vecMul_apply]); ⟨v + X, u + Y, by simp_all [mem_spanSubset_iff]; grind⟩
variable {A} [CommRing A] {R : Subring A} {l : _} {m n : Type*} {M N : Matrix m n A} (R' : Subring A) {g : Aˣ}
def intVectors n : Submodule R' (n → A) := ⟨⟨⟨{v | ∀ i, v i ∈ R'}, by aesop⟩, by simp⟩, by simp_all [mul_mem, R'.smul_def]⟩
def IsIntMatrix (R : Subring A) {m n} (M : Matrix m n A) := ∀ i j, M i j ∈ R
noncomputable abbrev submoduleIndex (M M' : Submodule R (m → A)) := M.toAddSubgroup.relIndex M'.toAddSubgroup
attribute [local simp] IsIntMatrix mulVec_eq_sum Matrix.mul_apply mul_mem intVectors sum_mem
lemma IsIntMatrix.add : IsIntMatrix R M → IsIntMatrix R N → IsIntMatrix R (M + N) := by aesop
lemma IsIntMatrix.sub : IsIntMatrix R M → IsIntMatrix R N → IsIntMatrix R (M - N) := by aesop
lemma IsIntMatrix.smul {a} : a ∈ R → IsIntMatrix R M → IsIntMatrix R (a • M) := by aesop
lemma IsIntMatrix.isInt_transpose : IsIntMatrix R M → IsIntMatrix R Mᵀ := by aesop
lemma IsIntMatrix.one : @IsIntMatrix A _ R n n 1 := by aesop
lemma Filling.mem_span_unit_iff {x} : x ∈ R ∙ g.1 ↔ g⁻¹ * x ∈ R := by aesop
lemma IsIntMatrix.mulVec [Fintype n] {v} : IsIntMatrix R M → v ∈ intVectors R n → M *ᵥ v ∈ intVectors R m := by aesop
lemma IsIntMatrix.mul [Fintype n] {N} : IsIntMatrix R M → @IsIntMatrix A _ R n l N → IsIntMatrix R (M * N) := by aesop
class IsStarStable (R : Subring A) [StarRing A] where star_mem {a} : a ∈ R → star a ∈ R
variable {m n : Type*} (M : Matrix m n A) [Fintype n] [StarRing A]
class IsAdelic [TopologicalSpace A] (R : outParam (Subring A)) extends IsStarStable R where (exists_topology : @IsOpen A _ R ∧ @IsCompact A _ R) (isValuationPair : IsValuationPair R) (exists_skew_unit : ∃ i ∈ R, ∃ τ ∈ R, -i * i = 1 ∧ star i = -i ∧ τ + star τ = 1) (exists_norm_neg_one : ∃ c ∈ R, star c * c = -1)
noncomputable def denomIndex a := (R'.toAddSubgroup.comap (.mulLeft a)).relIndex R'.toAddSubgroup
def colLattice := (intVectors ..).map (M.mulVecLin.restrictScalars R')
def preimageLattice := (intVectors ..).comap (M.mulVecLin.restrictScalars R')
noncomputable def unitaryLevel (g : Aˣ) J := ((congruenceGL (R' ∙ ↑g) id).subgroupOf (U J)).copy {k | k.1 ∈ intGL n R' ∧ IsIntMatrix R' (g⁻¹ • (k.1.1 - 1))} (by simp [congruenceGL, ↓Filling.mem_span_unit_iff]; rfl)
def IsUnimodular T := Tᴴ = T ∧ ∃ u ∈ intGL n R', u.1 = T
class IsHermUnit (J : Matrix n n A) where (conjTranspose_eq : Jᴴ = J) (isUnit : IsUnit J)
