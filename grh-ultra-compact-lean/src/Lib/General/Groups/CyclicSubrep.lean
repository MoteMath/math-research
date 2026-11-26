import Lib.Adelic.Unitary.CongruenceLevel
variable {G V} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
abbrev cyclicSpan y := Submodule.span ℂ (.range (ρ · y))
def smoothVectorRep [TopologicalSpace G] [IsTopologicalGroup G] := ρ.subrepresentation ⟨⟨⟨{x | ∀ᶠ g in _, ρ g x = x}, (·.mp <| ·.mono (by grind))⟩, by simp⟩, fun _ _ ↦ (·.mono (by simp_all))⟩ fun a _ _ ↦ .mono ((continuous_const_mul a⁻¹).mul_const a |>.tendsto 1 (by simpa)) (by simp)
instance [TopologicalSpace G] [IsTopologicalGroup G] : IsSmoothRep (smoothVectorRep ρ) := ⟨(·.2.mono (by aesop))⟩
variable {ρ} {y}
lemma self_mem_cyclicSpan : y ∈ cyclicSpan ρ y := Submodule.subset_span ⟨1, by simp⟩
lemma apply_mem_cyclicSpan g : ∀ x ∈ cyclicSpan ρ y, ρ g x ∈ cyclicSpan ρ y := Submodule.mapsTo_span fun _ ⟨h, _⟩ ↦ ⟨g * h, by simp [*]⟩
lemma compactMean_mem_cyclicSpan {K : Subgroup G} [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep ρ] [CompactSpace K] g {x} (h : x ∈ cyclicSpan ρ y) : compactMean ρ K (ρ g x) ∈ cyclicSpan ρ y := (Submodule.ker_mkQ _).le (map_compactMean_of_const _ (by simp_all [apply_mem_cyclicSpan]))
