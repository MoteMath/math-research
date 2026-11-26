import Lib.Adelic.Adeles.CoprimeValuation
open NumberField Polynomial ComplexEmbedding InfinitePlace Finset IsTotallyComplex
variable {E} [Field E] [IsTotallyComplex E]
@[simp, grind] lemma s11_d2 σ : @conjugate E _ σ ≠ σ := complexEmbedding_not_isReal _
@[to_additive] lemma prod_embeddings_eq_prod_pairs [NumberField E] [PlaceEmbedding E] {M} [CommMonoid M] (F : (E →+* ℂ) → M) : ∏ σ, F σ = ∏ v, F (Φ v) * F (conjugate (Φ v)) := prod_fiberwise _ mk F ▸ by congr!; apply prod_eq_mul <;> grind [mk_Φ, mk_eq_iff]
omit [IsTotallyComplex E] in
lemma s11_p6 (P : E[X]) σ : (P.map (conjugate σ)).roots = (P.map σ).roots.map star := (P.map_map ..).rec ((IsAlgClosed.splits _).roots_map _)
