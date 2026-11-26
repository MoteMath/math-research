import Lib.General.NumberTheory.UpsilonValues
import Lib.Adelic.Adeles.AdeleSelfDual
import Lib.General.LinearAlgebra.ElementOfMatrix
noncomputable section
section
open Matrix Real WeilData
def vacuumFn {E} [Field E] [CMType E] [WeilData E] {n} [Fintype n] (x : n → 𝔸 E) := (-∑ i, ∑ w, π * (Φ w j).im * ‖(x i).1 w‖ ^ 2).exp * ite (∀ i, α⁻¹.1 * (x i).2 ∈ Ô E) (ψf E ((traceOne * j / 2 : E) * ∑ i, star (x i).2 * (x i).2)).1 0
def adelicHeis E [Field E] [CMType E] [WeilData E] {n} [Fintype n] (s : n → ℤˣ) : Heisenberg (n → 𝔸 E) := by refine ⟨fun x y ↦ stdAddChar E (toAdele (j / 2) * star y ⬝ᵥ stdForm E s *ᵥ x), ?_, ?_, fun x ↦ stdAddChar_half (_ : 𝔸 E) ▸ ?_, ?_, .subtype_val (by fun_prop)⟩ <;> simp [mul_add, neg_div, AddChar.map_add_eq_mul, ← star_dotProduct, star_mulVec_dotProduct, Circle.norm_coe]
end
namespace stdLattice
open NumberField Matrix AddChar Circle WeilData
variable (E ι : Type _) [Field E] [CMType E] [WeilData E] [Fintype ι]
def _root_.stdLattice (E ι : Type _) [Field E] [NumberField E] : AddSubgroup (ι → 𝔸f E) := (intVectors (Ô E) ι).toAddSubgroup
def psi₀ := coeHom.compAddChar ((ψf E).mulShift (algebraMap E _ j * α.1 * star α.1))
variable {E ι}
def traceOneAdele : 𝔸f E := (WeilData.traceOne : E)
def half {E : Type _} [Field E] [NumberField E] : 𝔸f E := (2⁻¹ : E)
lemma psi₀_apply z : psi₀ E z = ψf E (algebraMap E _ j * α.1 * star α.1 * z) := rfl
@[simp] lemma norm_psi₀ z : ‖psi₀ E z‖ = 1 := norm_coe _
@[fun_prop] lemma continuous_psi₀ : Continuous (psi₀ E) := continuous_ψf.subtype_val.comp (continuous_const_mul _)
lemma psi₀_star z : psi₀ E (star z) = psi₀ E (-z) := by simp [psi₀, ψf_star (-_), mul_right_comm]
lemma forall_psi₀_mul_eq_one_iff z : (∀ u ∈ Ô E, psi₀ E (z * u) = 1) ↔ z ∈ Ô E := by simpa [psi₀_apply, ← mul_rotate' _ _ z, coe_eq_one, forall_ψf_mul_eq_one] using
  ((exists_reduction_and_idele_generator differentIdeal_ne_bot).elim fun _ ⟨_, _, t, _, h, H⟩ ↦ (H _).trans (by simp [mem_Ô, h, -WithZero.inv_exp, WithZero.exp_neg, by simpa using ‹WeilData E›.self_dual]))
lemma traceOneAdele_mem : traceOneAdele ∈ Ô E := algebraMap_mem_Ô.2 isIntegral_traceOne
@[simp] lemma traceOneAdele_add_star : traceOneAdele + star traceOneAdele = (1 : 𝔸f E) := by simp [traceOneAdele, WeilData.traceOne, ← map_add, ← add_div]
omit [WeilData E] in
lemma two_mul_half : 2 * half = (1 : 𝔸f E) := by norm_num [half, two_mul, ← map_add]
omit [WeilData E] in
lemma star_half : star half = @half E .. := by simp [half]
attribute [grind .] traceOneAdele_add_star two_mul_half star_half
lemma psi₀_eq_one_of_mem {o} : o ∈ Ô E → psi₀ E o = 1 := by grind [forall_psi₀_mul_eq_one_iff, (Ô E).one_mem]
lemma psi₀_congr {a b o} t : o ∈ Ô E → a = b + (t + star t) + o → psi₀ E a = psi₀ E b := by simp_all [map_add_eq_mul, psi₀_star, ← map_add_eq_mul _, psi₀_eq_one_of_mem]
def semichar (x : ι → _) := psi₀ E (traceOneAdele * half * star x ⬝ᵥ x)
def finVac x := ite (x ∈ stdLattice E ι) (delta% semichar x) 0
variable (E ι)
def finHeis : Heisenberg (ι → 𝔸f E) := by refine ⟨fun x y ↦ psi₀ E (half * star y ⬝ᵥ x), ?_, ?_, fun x ↦ (psi₀ E).2 ▸ psi₀_congr (traceOneAdele * half * star x ⬝ᵥ x) (zero_mem _) ?_, ?_, by fun_prop⟩ <;> simp [mul_add, map_add_eq_mul, half, ← star_dotProduct, ← add_mul]
