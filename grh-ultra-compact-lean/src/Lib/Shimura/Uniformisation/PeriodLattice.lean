import Lib.Shimura.ComplexTheta.CanonicalMultiplier
import Lib.Shimura.Uniformisation.Frames
import Lib.Adelic.Adeles.MatrixApprox
import Lib.Adelic.Unitary.SpaceBasic
noncomputable section
section
open Matrix NumberField QuotientAddGroup
section
variable {E n : Type} [Field E] [NumberField E] {x y : n → 𝔸f E} [Fintype n] (g : GL n (𝔸f E))
section
omit [Fintype n]
lemma torsionClass_eq_iff : torsionClass x = torsionClass y ↔ ∀ i, x i - y i ∈ Ô E := eq_iff_sub_mem.trans (by aesop)
@[simp] lemma torsionClass_eq_zero : torsionClass x = 0 ↔ ∀ i, x i ∈ Ô E := torsionClass_eq_iff.trans (by simp)
lemma torsionClass_induction {p : AdelicTorsion E n → Prop} : (∀ y, p (torsionClass y)) → ∀ s, p s := Quot.ind
end
lemma exists_nsmul_adelicTorsion_eq_zero : ∀ s : AdelicTorsion E n, ∃ m ≠ 0, m • s = 0 := torsionClass_induction (by simp [← map_nsmul, exists_forall_mul_mem_Ô _])
lemma isOpen_preimage_torsionClass s : IsOpen (@torsionClass E _ _ n ⁻¹' s) := (discreteTopology (isOpen_set_pi (by simp) fun _ _ ↦ isOpen_Ô)).1.le s ⟨⟩
lemma torsionClass_mulVec_eq_zero {h : Matrix n n _} : (∀ i j, h i j ∈ Ô E) → torsionClass x = 0 → torsionClass (h *ᵥ x) = 0 := by simp_all [mulVec_apply_eq_sum, sum_mem, mul_mem]
abbrev RealVectors E (n : Type) [Field.{0} E] := n → InfinitePlace E → ℂ
structure ModuliPoint (E n) [Field.{0} E] [CMBase E] [Fintype.{0} n] (ν) where
  (x : GL n (𝔸f E)) (reflection) P : Fin ν → RealVectors E n
  isSignedFrame : IsSignedFrame x reflection
  isReflection : IsReflection reflection
abbrev cmEmbedding {E : Type} [Field E] [CMType E] := RingHom.pi ‹CMType E›.Φ
def frameCoords := g⁻¹.1.mulVecLin.restrictScalars E ∘ₗ (Algebra.linearMap ..).compLeft n
@[simps! -isSimp apply] def frameTorsionClass := torsionClass ∘ₗ (frameCoords g).restrictScalars _
end
section
variable {E n : Type} [Field E] [CMType E] [Fintype n]
abbrev realVecAction (β : Matrix n n E) := (β.map cmEmbedding).mulVecLin
@[simps!] def toRealVectors := (@cmEmbedding E _ _).toAddMonoidHom.compLeft n
def classLattice {V} [FinComplexSpace.{0} V] (g : GL n (𝔸f E)) (S : AddSubgroup (AdelicTorsion E n)) (Q : RealVectors E n ≃L[ℝ] V) := ((S.comap (frameTorsionClass g)).map ((Q : RealVectors E n →+ V).comp toRealVectors)).toIntSubmodule
def frameLattice (g : GL n (𝔸f E)) := (classLattice g ⊥ (.refl ..)).toAddSubgroup
end
variable {E n : Type} [Field E] [CMBase E] {x : n → 𝔸f E} [Fintype n] (g : GL n (𝔸f E)) {V} [FinComplexSpace.{0} V] (ℓ : Matrix n n ℂ) (Q : RealVectors E n ≃L[ℝ] V) {ν : ℕ}
def IsPeriodMap := ∀ w, Q (Complex.I • fun i v ↦ (ite (v = v₀) ℓ 1 *ᵥ (w · v)) i) = Complex.I • Q w
def ModuliPoint.act (a : ModuliPoint E n ν) (g : GUPlus E n) (α : Fin ν → 𝓞 E := 1) :
  ModuliPoint E n ν := { a with x := _ * g, P i := cmEmbedding (α i).val • a.P i, isSignedFrame := by simpa [ratConj] using a.4.mul 1 g.2.1 }
@[mk_iff] structure ModuliPoint.IsLevelIso (K : Subgroup (GL n (𝔸f E))) (z : GL n E) (a b : ModuliPoint E n ν) where
  mem_level : b.x⁻¹ * toFinGL z * a.x ∈ (K : Subgroup _)
  reflection_eq : ratConj z a.reflection = b.reflection
  sub_mem_lattice i : realVecAction z (a.P i) - b.P i ∈ frameLattice b.x
end
open NumberField Matrix Function Submodule Set
attribute [local simp] frameTorsionClass frameCoords LinearMap.compLeft comp_def RingHom.map_mulVec
variable {E n : Type} [Field E] [Fintype n] {V : Type} {A : Matrix n n E} {y : n → E} [FinComplexSpace V] {Q : RealVectors E n ≃L[ℝ] V}
section
variable [NumberField E] {g : GL n (𝔸f E)}
lemma kerFTC : (frameTorsionClass (1 : GL n (𝔸f E))).ker = .pi ⊤ 1 := by simp [SetLike.ext_iff, @IsIntegralClosure.isIntegral_iff (𝓞 E)]
lemma denseRange_frameCoords : DenseRange (frameCoords g) := (MulAction.surjective g⁻¹).denseRange.comp (.piMap (const _ denseRange_algebraMap_finAdele)) (by fun_prop)
lemma frameTorsionClass_surjective : Surjective (frameTorsionClass g) := (denseRange_frameCoords.exists_mem_open (isOpen_preimage_torsionClass {_}) <| Quot.exists_rep ·)
end
variable [CMType E] {g g' : GL n (𝔸f E)} {S : AddSubgroup (AdelicTorsion E n)}
omit [Fintype n] in
lemma toRealVectors_injective : Injective (@toRealVectors E n _ _) := (@cmEmbedding E ..).injective.comp_left
omit [Fintype n] in
@[simp] lemma toRealVectors_smul (c : 𝓞 E) : toRealVectors (c • y) = cmEmbedding c.val • toRealVectors y := funext (cmEmbedding.map_mul _ <| y ·)
lemma mem_classLattice {x} : x ∈ classLattice g S Q ↔ ∃ y, frameTorsionClass g y ∈ S ∧ Q (toRealVectors y) = x := .rfl
@[simp↓] lemma realVecAction_toRealVectors : realVecAction A (toRealVectors y) = toRealVectors (A *ᵥ y) := (funext (cmEmbedding.map_mulVec _ _)).symm
lemma realVecAction_mem_frameLattice {P} (h : ∀ i j, (g'⁻¹.1 * A.map (algebraMap ..) * g.1 :) i j ∈ Ô E) : P ∈ frameLattice g → realVecAction A P ∈ frameLattice g' | ⟨_, k, e⟩ => e ▸ ⟨_, by simpa using torsionClass_mulVec_eq_zero h k, realVecAction_toRealVectors.symm⟩
@[simp] lemma realVecAction_apply w i v : (A.map cmEmbedding *ᵥ w) i v = (A.map (Φ v) *ᵥ (w · v)) i := Finset.sum_apply ..
omit [Fintype n] in
lemma drTRV : DenseRange (@toRealVectors E n _ _) := .piMap (const _ denseRange_Φ)
instance : DiscreteTopology (classLattice g ⊥ Q) := continuous_subtype_val
  |>.discrete_of_tendsto_cofinite_cocompact (tendsto_cofinite_cocompact_iff.2 fun _ K ↦ (((isCovolOneLattice_ratVectors.finite_preimage ((K.prod (isCompact_pi_infinite (const _ isCompact_Ô))).image_auto fun p i ↦ (Q.symm p.1 i, mulVec g p.2 i))).image _).preimage injOn_subtype_val ).subset fun ⟨_, y, h, e⟩ H ↦ ⟨_, ⟨(_, _), ⟨H, torsionClass_eq_zero.1 h⟩, by aesop⟩, e⟩)
instance [DiscreteTopology (classLattice g S Q)] : IsZLattice ℝ (classLattice g S Q) := ⟨eq_top_iff'.2 ((reindex_equiv Q).1.2 (isClosed_property drTRV (comap .. ).closed_of_finiteDimensional fun y ↦ (exists_nsmul_adelicTorsion_eq_zero (frameTorsionClass g y)).elim fun m _ ↦ (smul_mem_iff (s := (m : ℝ)) _ (by aesop)).1 (subset_span ⟨m • y, mod_cast by simp_all [-nsmul_eq_mul, -frameTorsionClass]⟩)))⟩
