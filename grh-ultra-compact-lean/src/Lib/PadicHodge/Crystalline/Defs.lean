import Lib.PadicHodge.PeriodRings.BdR
noncomputable section
open TensorProduct Module DistribSMul RingHomClass
class OverGp Γ (p : outParam ℕ) [Fact p.Prime] [Group Γ] where
  (toGp : Γ →* Gp p) isOpen_range : Fact (IsOpen (SetLike.coe toGp.range))
class GroupOverGp (p : outParam ℕ) [Fact p.Prime] where (G) [group : Group G] [overGp : OverGp G p]
attribute [instance_reducible] GroupOverGp.group GroupOverGp.overGp
attribute [instance] OverGp.isOpen_range GroupOverGp.group GroupOverGp.overGp
export OverGp (toGp)
variable {p} [ThePrime p] {Γ R T} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [𝒥 : OverGp Γ p] (ρ : Representation R Γ T) (B) [CommRing B] [Algebra ℤ_[p] B] (γ : R →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ) (s m)
instance : CoeSort (GroupOverGp p) Type := ⟨(·.G)⟩
def tensorAction {M} [Monoid M] [MulSemiringAction M B] [SMulCommClass M ℤ_[p] B] (m : M) (f : End R T) : End ℤ_[p] (B ⊗[ℤ_[p]] T) := map (toLinearMap _ _ m) f
def fixedPeriods [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B] F := {x | ∀ᶠ g in F, tensorAction B (toGp g) (ρ g) x = x}
def IsAdmissible F := Submodule.span Bcris (fixedPeriods ρ Bcris F) = ⊤
abbrev IsCrystalline := IsAdmissible ρ ⊤
def crysCocycles : Submodule R (Γ → T) := ⟨⟨⟨{c | ∃ y, ∀ g, 1 ⊗ₜ c g = tensorAction Bcris (toGp g) (ρ g) y - y}, fun ⟨y, _⟩ ↦ .imp' (y + ·) (by simp [tmul_add]; grind)⟩, 0, by simp⟩, fun a _ ⟨y, e⟩ ↦ ⟨y.map 1 (a • .id), (congr(map 1 (a • .id) $(e ·)).trans (by simp [tensorAction, map_map, LinearMap.comp]))⟩⟩
def IsWeilPair (s : Gp p) m := IsFrob (intQpBar p) (p ^ m) s⁻¹
lemma isWeilPair_zero_iff {s} : IsWeilPair s 0 ↔ s ∈ inertiaGroup _ (intQpBar p) := (inertiaGroup ..).inv_mem_iff
abbrev χ := cyclotomicGp.comp 𝒥.toGp
variable (Γ) in def nearOne := (nhds 1).comap 𝒥.toGp
variable (Γ) in lemma eventually_nearOne_apply_eq c : ∀ᶠ g in nearOne Γ, toGp g c = c := ⟨_, (isLocallyConstant_smul c {c}).mem_nhds rfl, .rfl⟩
abbrev Dpcris := fixedPeriods ρ Bcris (nearOne Γ)
abbrev IsPotCrys := IsAdmissible ρ (nearOne Γ)
def HasHodgeTateWeight y := ∀ g, tensorAction ℂ_[p] (toGp g) (ρ g) y = (cyclotomicGp (toGp g) ^ (-u)).1 • y
def hodgeTateMaps : Submodule (PadicAlgCl p) (T →ₛₗ[toRingHom γ] ℂ_[p]) := ⟨⟨⟨{f | ∀ x, ∀ᶠ g in _, f (ρ g x) = (χ g ^ (-u)).1 • toGp g • f x}, fun h k x ↦ (h x).mp ((k x).mp (by simp_all))⟩, by simp⟩, fun c _ h x ↦ (h x).mp ((eventually_nearOne_apply_eq Γ c).mp (by simp_all [Algebra.smul_def c, ← PadicComplex.coe_eq]))⟩
def jump := finrank (PadicAlgCl p) (hodgeTateMaps ρ γ u)
def HasJumps J := ∀ u, jump ρ γ u = Multiset.count u J
def linearFrob := Classical.epsilon fun β : End Bcris _ ↦ ∀ d ∈ Dpcris ρ, β d = tensorAction _ (⟨.ofAdd m, toGp s⟩ : FrobGal) (ρ s) d
variable (R T) in def coefEnd := toRingHom ((End.baseChangeHom ℤ_[p] Bcris T).comp (Algebra.lsmul (A := R) ..))
def IsKilledBy P := IsPotCrys ρ ∧ Polynomial.eval₂ (coefEnd R T) (linearFrob ρ s m) P = 0
abbrev matrixRep {n} [Fintype n] (r : Γ →* GL n R) := actionRep R (n → R) ((Units.coeHom _).comp r)
