import Lib.General.Geometry.ProperAtlas
import Lib.PadicComparison.Descent.AlmostAcyclic
open CategoryTheory Functor AlgebraicGeometry
variable {C C' D} [Category C] [Category C'] [Category D] {F F'} (c : Comparison F F') {ψ : C ⥤ D} {ψ' : C' ⥤ D} (η : ψ' ⟶ c.φ ⋙ ψ)
lemma Comparison.isClosedClass : IsClosedClass fun N ↦ c.IsBijective (N := ψ ⋙ N) (whiskerRight η N) := (c.devissage ((whiskeringLeft ..) ψ) ((whiskeringLeft ..).map η)).2
abbrev Comparison.IsBijectiveOn P := c.IsBijective (freeAbMap (Y := ψ ⋙ P) (whiskerRight η P))
class IsCharted {R} (Y : Over (Spec R)) k [CommRing k] [Algebra R k] where
 exists_isCharting : ∃ V, @IsCharting k _ (algPointsOf k R Y) V
