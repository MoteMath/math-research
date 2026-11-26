import Lib.Weil.MixedModel.AdelicSum
import Lib.General.NumberTheory.LocalProduct
noncomputable section
open RestrictedProduct
variable {E : Type} [Field E] [NumberField E] (P : Finset (FinPlace E))
@[simps!] def evalPlaces : 𝔸f E →+* LocProd P := .pi (evalAt ·.1)
def adeleOfLocal : LocProd P →ₙ+* 𝔸f E := by use! fun y ↦ inclusion _ _ (𝓖 := .principal Pᶜ) ?_ (.mk (fun w ↦ if h : w ∈ P then y ⟨w, h⟩ else 0) ?_) <;> aesop (add safe (by congrm ⟨?_, _⟩))
@[fun_prop] lemma continuous_adeleOfLocal : Continuous (adeleOfLocal P) := (continuous_inclusion (R := _) (by simp)).comp (continuous_rng_of_principal.2 (continuous_pi fun _ ↦ by simp; split <;> fun_prop))
@[fun_prop] lemma continuous_evalPlaces : Continuous (evalPlaces P) := continuous_pi (continuous_evalAt ·.1)
@[simp] lemma evalPlaces_adeleOfLocal x : evalPlaces P (adeleOfLocal P x) = x := funext (dite_eq_left ·.2)
lemma adeleOfLocal_evalPlaces x : adeleOfLocal P (evalPlaces P x) = idem P * x := by aesop (add simp idem_apply)
