import Lib.General.LinearAlgebra.Base
import Lib.ClassField.Places.GaloisDefs
noncomputable section
open Submodule DistribMulAction
variable {R G M H N} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M) [Group H] [TopologicalSpace
  H] [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N] {ρ' : Representation R
  H N} (φ : H →ₜ* G) (u : M →ₗ[R] N) (h : ∀ g m, u (ρ (φ g) m) = ρ' g (u m) := by bound)
instance (priority := 100) : ContinuousConstSMul R M := ⟨by fun_prop⟩
def Z1 := mk (R := R) ⟨⟨{f | Continuous f ∧ ∀ g h, f (g * h) = f g + ρ g (f h)},
  by simp_all [Continuous.add, add_add_add_comm]⟩, by continuity⟩ (by continuity)
abbrev d0 := LinearMap.pi (ρ · - .id)
def Z2 := ofLinearComb (R := R) {f | Continuous f ∧ ∀ g h k, f (g * h, k) = f (g, h * k) - f (g, h)
  + ρ g (f (h, k))} ⟨0, by continuity⟩ fun _ ⟨_, _⟩ _ ⟨_, _⟩ _ _ ↦
  ⟨by fun_prop, by intros; simp [*]; module⟩
def B2 := ofLinearComb (R := R) {f : G × G → M | ∃ c, Continuous c ∧ ∀ g h, f (g, h) = ρ g (c h) -
  c (g * h) + c g} ⟨0, 0, by continuity⟩ fun _ ⟨c, _, _⟩ _ ⟨d, _, _⟩ a b ↦
  ⟨a • c + b • d, by fun_prop, by intros; simp [*]; module⟩
@[instance_reducible] def H2 := _ ⧸ (B2 ρ).comap (Z2 ρ).subtype deriving AddCommGroup, Module R
variable {ρ}
abbrev pairMapZ1 : Z1 ρ →+ Z1 ρ' := ⟨⟨fun f ↦ ⟨(u <| f.1 <| φ.1 ·), f.2.imp (by continuity)
  (by aesop)⟩, by bound⟩, by bound⟩
def pairMapH2 : H2 ρ →ₗ[R] H2 ρ' := mapQ _ _ ⟨⟨fun f ↦ ⟨(u <| f.1 <| ·.map φ φ), f.2.imp (by
  fun_prop) (by aesop)⟩, by bound⟩, by bound⟩ fun f ⟨c, _, _⟩ ↦ ⟨u ∘ c ∘ φ, by fun_prop, by aesop⟩
variable (R) in
abbrev actionRep M [AddCommMonoid M] [Module R M] {G S} [Monoid G] [Monoid S] [DistribMulAction S M]
  [SMulCommClass S R M] (χ : G →* S) : Representation R G M := (toModuleEnd ..).comp χ
def charRep M [AddCommGroup M] [Module R M] (χ : G →* Rˣ) := actionRep R M ((Units.coeHom R).comp χ)
end
noncomputable section
def QZ := AddCircle (1 : ℚ) deriving AddCommGroup, DivisibleBy _ ℤ
instance : TopologicalSpace QZ := ⊥
instance : DiscreteTopology QZ := ⟨rfl⟩
def QZ.mk : ℚ →+ QZ := QuotientAddGroup.mk' _
variable (a : QZ) {R} (G) {M} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M)
def QZ.fracRep := (a.equivIco 1 0).1
def QZ.carry b := ⌊fracRep a + fracRep b⌋
@[simp] lemma QZ.mk_fracRep : mk a.fracRep = a := a.coe_equivIco
lemma QZ.fracRep_mk r : fracRep (mk r) = Int.fract r := toIcoMod_zero_one r
@[push_cast] lemma QZ.cast_carry b : carry a b = fracRep a + fracRep b - fracRep (a + b) := by
  simp [carry, ← Int.self_sub_fract, ← fracRep_mk]
abbrev QZChar := Z1 (.trivial ℤ G QZ)
variable {G}
def cyclicClass : QZChar G →+ ρ.invariants →+ H2 ρ := by refine (.mk' (fun χ ↦ .mk' (fun w ↦
  ⟦⟨fun p ↦ (χ.1 p.1).carry (χ.1 p.2) • w, χ.2.imp (by fun_prop) ?_⟩⟧) ?_) fun ⟨χ, _, _⟩ ⟨ψ, _, _⟩ ↦
  AddMonoidHom.ext fun w ↦ QuotientAddGroup.eq_iff_sub_mem.2 ⟨fun g ↦
  (χ g).carry (ψ g) • -w, by fun_prop, ?_⟩) <;> intros <;>
  simp_all [(ρ.mem_invariants _).1 (Subtype.prop _)] <;>
  first | rfl | (match_scalars; qify; grind)
end
