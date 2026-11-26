import New.Filling.LevelBridge
noncomputable section
open Fintype Function Matrix
variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰}
lemma Filling.reduction_apply_congr {k} l i w {a b} (h : k.1.1 a b = l.1.1 a b) : S.reduction k i w a b = S.reduction l i w a b := congr(⟦⟨$h _, _⟩⟧)
def Filling.vectorFixer {i} (w : S.chosenPlaces i) (d : _ × {v : _ → ResField w.1 // v ≠ 0}) := (MulAction.stabilizer _ (inclMatrix _ 𝔰.besselFrame *ᵥ d.2.1)).comap (.mk' (fun s : S.GRes ↦ S.idOrInvAdjoint d.1 (s i w)) (by simp))
def Filling.FixesNormAtLeast s x := ∃ A : Finset ((Σ i, S.chosenPlaces i) × _), x ≤ ∏ p ∈ A, S.levelPrime p.1.1 ∧ ∀ p ∈ A, ∃ v, s ∈ S.vectorFixer p.1.2 (p.2, v)
def Filling.fixingSet Sg (d : ∀ _, _) := {s | (∀ w ∈ Sg, s ∈ S.vectorFixer (i := 0) w (d w)) ∧ (Sg = Finset.univ ∨ ∃ w, ∀ l, leadingMinor ((S.latMiddle _).frameGram (s 0 w).1) l ≠ 0)}
variable {R} [CommRing R] {𝔰 : Shape} (T : 𝔰.Form R)
abbrev Filling.zFormPair := T.toRows₂.fromBlocks 0 0 T.toRows₂
variable [StarRing R] {T : 𝔰.Form R} (γ γ' : T.G) (c c')
def commonLink := (link γ ⊓ link γ' ⊓ (Filling.zFormPair T).mulVecLin.ker).map (.funLeft R R (.inl ∘ .inl))
def HasCommonFlagVector a := ∃ x y, frameImage 1 *ᵥ x = frameImage γ.1.1 *ᵥ y ∧ x a = c ∧ y a = c' ∧ ∀ b > a, x b = 0 ∧ y b = 0
def IsNormalForm (j : ℕ) (γ : T.G) := ∃ c, c * star c = 1 ∧ ∀ a, j ≤ a.1 → HasCommonFlagVector γ c 1 a
variable (S : Filling E 𝔰) (c : _)
abbrev Filling.ratGram := (S.ratMiddle E).splitGram
abbrev Filling.linkForm := (S.ratMiddle E).fromBlocks 0 0 (-S.ratMiddle E)
def Filling.classCoord := (S.classBasis c)⁻¹.1
def Filling.classCoordX₀ (c : S.Classes) := middleBaseChange 𝔰 S.piBar * c.out⁻¹.1.1
abbrev Filling.countWeight i := Nat.card (S.reducedImage besselS) * card S.Classes / S.N ^ (𝔰.k * numInfPlaces E) * (2 * S.tailScale ^ 2) ^ i
variable (j) (γ : S.G E)
def Filling.HasLevel := IsNormalForm j.1 γ ∧ leadingMinor (S.frameProducts γ) j ≠ 0 ∧ (𝔰.ϱ < j ↔ S.termDisc γ ≠ 0)
def Filling.CongruentTerms (c' : S.Classes) (γ γ' : S.G E) := ∃ s, γ ∈ S.termsOver c s c' ∧ γ' ∈ S.termsOver c s c'
def Filling.termDiscNorm := ∏ v, ‖Φ v (S.termDisc γ)‖
def Filling.boxedPoints := {y : NumberField.InfinitePlace E → 𝔰.G₁ | ∀ v, y v ∈ frameBox S.boxSize ∧ InCut (y v) S.b}
def Filling.IsNear := ∃ y ∈ S.boxedPoints, (S.ratToInf γ)⁻¹ * y ∈ S.boxedPoints
def Filling.CharsAgree := ∀ u ∈ besselU, ∀ u' ∈ besselU, u * γ = γ * u' → S.unipotentChar (S.ratToFin u) = S.unipotentChar (S.ratToFin u')
