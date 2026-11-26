import Lib.ClassField.GaloisCohomology.DiscreteUnits
noncomputable section
open Function AddSubgroup QuotientAddGroup AddMonoidHom DFunLike Nat DiscreteModule
variable {R R' S} (Γ) [CommRing R] [CommRing R'] [CommRing S] [Group Γ] [TopologicalSpace Γ]
  {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω] [IsAlgClosed Ω]
  {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
abbrev unitsModule [IsProGalois Γ K Ω] := of (@unitsRep Γ ..) (continuous_prod_of_discrete_right.2
  fun x ↦ ((isLocallyConstant_smul _).desc (unitsRep · x) _ Units.val_injective).continuous)
instance [Finite A] : Finite (A →+ DiscreteUnits Ω) := .of_equiv _ toMultiplicativeLeft.symm
instance : DivisibleBy (DiscreteUnits Ω) ℤ := @AddGroup.divisibleByIntOfDivisibleByNat _ _
  (divisibleByOfSMulRightSurj _ _ (swap (·.exists_nsmul)))
variable {Γ} (b : A →+ B →+ C)
attribute [local simp] ext_iff LE.le forall_mk funext_iff continuous_prod_of_discrete_right
def pairingAnnihilator L :=
  (b.comp (AddSubgroup.subtype L)).flip.ker.copy {y | ∀ x ∈ L, b x y = 0} (by aesop)
instance : TopologicalSpace (A →+ B) := ⊥
instance : DiscreteTopology (A →+ B) := ⟨rfl⟩
lemma card_pairingAnnihilator_mul_card (e : QZ ≃+ C) L : .card (pairingAnnihilator b L) * .card L =
  .card B * Nat.card ↥(b.ker ⊓ L) := let β := b.comp L.subtype
  by erw [pairingAnnihilator, β.flip.ker.copy_eq, ← addSubgroupOf_map_subtype, card_subtype _ β.ker]
     grind [show β.flip.ker.index = β.ker.index by apply dvd_antisymm <;> exact (by_cases (⟨0, ·⟩)
       fun h ↦ (index_dvd_of_le (by simp)).trans (@card_hom_QZ _ _ (finite_of_card_ne_zero h) ▸
       card_dvd_of_injective _ (kerLift_injective ((kerLift _).flip.compr₂ e.symm)))),
       card_mul_index]
section
variable (W : DiscreteModule S Γ) (M : DiscreteModule R Γ) (N :
  DiscreteModule R' Γ) (b : M →+ N →+ W) (e : ∀ g x y, b (M.ρ g x) (N.ρ g y) = W.ρ g (b x y))
def cupProduct : Z1 M.ρ →+ Z1 N.ρ →+ W.H2 := (mk' (fun x ↦ mk' (fun y ↦ (⟨fun p ↦ b (x.1 p.1)
    (N.ρ p.1 (y.1 p.2)), y.2.rec fun _ _ ↦ x.2.imp (by fun_prop) (by aesop)⟩ : Z2 W.ρ)) (by simp))
    (by simp)).compr₂ (mk' _)
variable {W M N}
lemma cupProduct_flip : ∀ x y, cupProduct _ _ _ b.flip (swap <| e ·) y x = -cupProduct W M N b e x y
  | ⟨x, _, _⟩, ⟨y, _, _⟩ => eq_iff_sub_mem.2 ⟨fun g ↦ -b (x g) (y g), by fun_prop, by
    simp_all; intros; abel⟩
end
variable [IsProGalois Γ K Ω] (M : DiscreteModule R Γ)
abbrev DiscreteModule.cartierDual [Finite M] := let W := unitsModule Γ; of ⟨⟨fun g ↦ toIntLinearMap
    (mk' (comp (W.ρ g) <| comp · (M.ρ g⁻¹) : _ → M →+ W) (by simp)), by simp⟩, by simp⟩ (.congr (by
                     simp; fun_prop) (leftInverse_invFun coe_injective ∘' _))
abbrev DiscreteModule.evalCup [Finite M] := cupProduct _ M.cartierDual M (.id _) (by simp)
variable {M} {N : DiscreteModule R Γ} [Finite M] [Finite N]
abbrev DiscreteModule.Hom.cartierDualMap (u : M.Hom N) : N.cartierDual.Hom M.cartierDual :=
  ⟨(compHom' u).toIntLinearMap, by simp [u.isIntertwining]⟩
