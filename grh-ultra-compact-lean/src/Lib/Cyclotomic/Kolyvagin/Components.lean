import Lib.ClassField.Places.Conjugation
variable {O} [CommRing O] {N} (l e : ℕ) [NeZero N] [Fact l.Prime] [Algebra ℤ_[l] O]
  (ψ : DirichletCharacter O N)
noncomputable def cycPowDirichlet :=
  cycCharIn (Γ := Gal(Ω/ℚ)) O Ω l ^ e * ψ.toUnitHom.comp (cycCharMod Ω N)
noncomputable def vanishingCocycles (χ : Gal(Ω/ℚ) →* Oˣ) B [AddCommGroup B] [Module O B] (s :
  Set _) := locConst (O := O) B ⊓ ⟨⟨⟨{x | (∀ g h, x (g * h) = x g + (χ g).1 • x h) ∧ ∀ g ∈ s,
  x g = 0}, by simp_all; grind⟩, by simp⟩, by simp_all [smul_comm (χ _).1]⟩
def inertiaOff (N l : ℕ) [NeZero N] (T : Finset Nat.Primes) := {i | ∃ A, (i ∈ cycloGalGroup N ∧
  A.valuation l = 1 ∧ i ∈ inertiaGroup _ A) ∧ ∀ r ∈ T, ¬A.valuation (r : Ω) < 1}
noncomputable abbrev component ν := vanishingCocycles (cycPowDirichlet l e ψ)⁻¹ (QuotSpan (l ^ ν :
  O)) (insert cmConj (cycloGalGroup N ∩ (inertiaAbove (placesDividing ℚ l)ᶜ ∪ shaLocalSet l ℚ 1)))
