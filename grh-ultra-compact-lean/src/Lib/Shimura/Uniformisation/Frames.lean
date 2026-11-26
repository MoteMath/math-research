import Lib.Adelic.Adeles.AdeleIdempotent
import Lib.General.LinearAlgebra.ValuedMatrix
noncomputable section
open NumberField ConjAct Matrix GeneralLinearGroup ComplexOrder Pointwise
class CMBase E [Field E] extends CMType E, Nontrivial (InfinitePlace E) where v₀ : InfinitePlace E
export CMBase (v₀)
section
variable (E : Type) [Field.{0} E] [NumberField E] (n : Type) [Fintype.{0} n] [IsCMField E]
def AdelicTorsion := _ ⧸ Submodule.pi .univ fun _ : n ↦ Subalgebra.toSubmodule (R := 𝓞 E)
  ⟨(Ô E).1, (algebraMap_mem_Ô.2 ·.2)⟩ deriving AddCommGroup, Module (𝓞 E)
variable {E n} (β : Matrix n n E) (x : GL n (𝔸f E))
def IsFrameFor := ∃ ε : (Ô ℚ)ˣ, xᴴ * β.map (algebraMap ..) * x.1 = finAdeleIncl ℚ E ε • 1
@[simp] abbrev IsScalarFrame (c : ℚ) := 0 < c ∧ IsFrameFor ((c : E) • 1) x
lemma IsFrameFor.mul_iff {c : E} {g} : IsFrameFor β x → (IsFrameFor (c • β) (x * g) ↔ IsFrameFor (c • 1) g) | ⟨ε, h⟩ => (Equiv.mulLeft ε⁻¹).exists_congr' fun _ ↦ by simpa [map_smul', gram_mul, -conjTranspose_mul, h, mul_smul, smul_comm c] using ((ε.isUnit.map (Ô ℚ).subtype).map _).smul_left_cancel
variable (E n)
def abelianDim := Fintype.card n * Fintype.card (InfinitePlace E)
def GU := Subgroup.ofDiv {g : GL n (𝔸f E) | ∃ c, IsScalarFrame g c} ⟨1, 1, rfl, 1, by simp⟩ fun _ ⟨c, _, h⟩ _ ⟨d, b, k⟩ ↦ ⟨d⁻¹ * c, by bound, by simpa [mul_smul, h.mul_iff, ← k.mul_iff, b.ne'] using ⟨1, by simp⟩⟩
def GUPlus := @Submonoid.copy (GL n _) _ (_ ⊓ ((Ô E).matrix.1.1.comap (Units.coeHom _))⁻¹)
  {g ∈ GU .. | ∀ i j, g⁻¹ i j ∈ Ô E} rfl
end
variable {E : Type} [Field.{0} E] [CMBase E] {n : Type} [Fintype.{0} n] {β : Matrix n n E} (x : GL n (𝔸f E)) (z : GL n E) (J : Matrix n n ℂ)
def torsionClass {E : Type} [Field.{0} E] [NumberField E] {n : Type} : (n → 𝔸f E) →ₗ[𝓞 E] AdelicTorsion E n := Submodule.mkQ _
instance : Algebra E ℂ := (Φ v₀).toAlgebra
abbrev toFinGL {E : Type} [Field.{0} E] [NumberField E] {n : Type} [Fintype.{0} n] : GL n E →* GL n (𝔸f E) := map (algebraMap ..)
def IsReflection := ∃ u w, w ⬝ᵥ u = 2 ∧ J = vecMulVec u w - 1
abbrev IsSignedFrameFor β := IsFrameFor β x ∧ ∀ w, (β.map (Φ w) * ite (w = v₀) J 1).PosDef
def IsSignedFrame := ∃ β, IsSignedFrameFor x J β
def ratConj := toConjAct (z.map (Φ v₀)) • J
lemma IsReflection.conj {J} (z : GL n ℂ) : IsReflection J → IsReflection (z.1 * J * z⁻¹.1) | ⟨u, w, _⟩ => ⟨z *ᵥ u, w ᵥ* z⁻¹, by simp [dotProduct_mulVec, mul_sub, sub_mul, mul_vecMulVec, vecMulVec_mul, *]⟩
lemma IsFrameFor.conj_iff : IsFrameFor (zᴴ * β * z.1) x ↔ IsFrameFor β (toFinGL z * x) := by simp [IsFrameFor, ↓map_conjTranspose_mul_mul, mul_assoc]
lemma IsSignedFrame.mul {x J} (h : IsSignedFrame x J) z {g} : g ∈ GU E n → IsSignedFrame (toFinGL z * x * g) (ratConj z J) | ⟨c, a, k⟩ => h.rec fun _ ⟨h, H⟩ ↦ ⟨_, ((IsFrameFor.conj_iff _ z⁻¹).2 (by simpa)).mul_iff.2 k, fun w ↦ by split <;> simpa [ratConj, units_smul_def, mul_assoc, ↓map_smul', ↓map_conjTranspose_mul_mul, *, ↓← val_map_apply] using! (z⁻¹.map _).isUnit.posDef_star_left_conjugate_iff.2 ((H w).smul a)⟩
