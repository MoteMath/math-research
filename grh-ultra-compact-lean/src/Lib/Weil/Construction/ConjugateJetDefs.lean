import Lib.Weil.MixedModel.NameWeilAction
variable {E I : Type} [Field E] [CMType E] [WeilData E] (w : I → E) [Fintype I]
noncomputable def finiteImage := (‹WeilData E›.α⁻¹.1 • Algebra.linearMap E (𝔸f E)).compLeft I
def IsTightFrame (m : I → ℕ) (M : ℕ) := (∀ i, finiteImage w i ∈ Ô E) ∧ ∀ σ τ, ∑ i, m i * (Φ σ (w i) * starRingEnd ℂ (Φ τ (w i))) = ite (σ = τ) ↑M 0
lemma IsTightFrame.repeat_vectors {m M} (h : IsTightFrame w m M) : IsTightFrame (fun x : Σ i, Fin (m i) ↦ w x.1) 1 M := by simp_all [IsTightFrame, finiteImage, Fintype.sum_sigma]
structure Space.VacuumExpansion {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] {s} (V : Space E n s) (δ : E) (N F) where
  (Index) [fintypeIndex : Fintype Index] [nonempty : Nonempty Index] (shift : Index → n → 𝔸f E) (multiplier : ℕ) mul_shift_mem j i : δ * shift j i ∈ Ô E
  card_dvd : Fintype.card Index = N ^ (2 * Fintype.card (NumberField.InfinitePlace E × n))
  sum_eq (ℓ : _ →ₗ[ℂ] ℂ) : ∑ j, (multiplier * ℓ (V.ϱ (finVec (shift j)) V.vacElem)) • V.ϱ (finVec (-shift j)) F = (Fintype.card Index * ℓ F) • V.vacElem
abbrev Space.IsJetConjugate [Field I] [CMType I] [WeilData I] {n : Type} [Fintype n] {s} {V : Space I n s} σ (π : Equiv.Perm _) t t' f f' := (V.jetSeries t f).map σ = (V.jetSeries t' f').rename (.map π.symm id)
@[simp] lemma Space.constantCoeff_jetSeries {s} {V : Space E I s} t f : (V.jetSeries t f).constantCoeff = V.θ (V.projReal f) := (jetSeries_apply ..).trans (by simp)
