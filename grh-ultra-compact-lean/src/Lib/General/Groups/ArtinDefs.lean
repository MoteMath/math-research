import Lib.General.Groups.RatModInt
import Lib.ClassField.HeckeL.EulerProduct
open Nat Subgroup Fact QuotientGroup MonoidHom QZ DFunLike
variable {G C} [Group G] [CommGroup C] [TopologicalSpace G] [IsTopologicalGroup G]
attribute [instance] isClosed_topologicalClosure
namespace QZChar
noncomputable abbrev ofZModCocycle n [NeZero n] : Z1 (.trivial ℤ G (ZMod n)) →+ QZChar G := pairMapZ1 (.id G) (ofZMod n).toIntLinearMap
variable (χ : QZChar G)
instance : Fact (toHom χ).ker.IsOpen := ⟨χ.2.1.1 {0} ⟨⟩⟩
@[simp] lemma abelianLift_mk (g : G) : abelianLift χ g = .ofAdd (χ.1 g) := rfl
@[fun_prop] lemma continuous_abelianLift : Continuous (abelianLift χ) := χ.2.1.quotient_lift _
omit [IsTopologicalGroup G] in lemma isOpen_ker : (ker χ).IsOpen := out
lemma exists_apply_ne_zero_of_notMem_ker {G} [Group G] [TopologicalSpace G] [N : NonarchimedeanGroup G] (f : G →* C) σ (h : @IsClosed G _ f.ker) (n : σ ∉ f.ker) : ∃ χ : QZChar G, (∀ g ∈ f.ker, χ.1 g = 0) ∧ χ.1 σ ≠ 0 :=
 (N.2 _ ((map_mul_left_nhds_one σ).le (h.compl_mem_nhds n))).elim fun V e ↦
 (not_forall.1 (mt (@eq_zero_of_forall_hom_eq_zero _ _ (Additive.ofMul (mk' (V.map f) (f σ)))) (by aesop))).elim fun u d ↦ ⟨⟨_, .of_isOpen_ker ((u.toMultiplicativeRight.comp _).comp f) (isOpen_mono (le_comap_mk' _ u.ker.toSubgroup' ⟨·, ·, rfl⟩) V.2), by aesop⟩, by aesop⟩
variable [CompactSpace G] [TotallyDisconnectedSpace G]
instance : NonarchimedeanGroup G := ⟨((nhds_basis_clopen 1).forall_iff (by tauto)).2 fun _ h ↦ IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one h.2 h.1⟩
lemma mem_of_forall_abelianLift {H : Subgroup _} (c : IsClosed H.carrier) : ∀ σ, (∀ χ : QZChar G, (∀ g ∈ H, abelianLift χ g = 1) → abelianLift χ σ = 1) → σ ∈ H := by simpa [forall_mk, ↓not_exists] using (exists_apply_ne_zero_of_notMem_ker ((mk' H).comp (mk' _)) · ((ker_mk' H ▸ c).preimage continuous_mk) |>.mt)
@[ext] lemma abelianization_ext {g g'} (h : ∀ χ : QZChar G, abelianLift χ g = abelianLift χ g') : g = g' := div_eq_one.1 (mem_of_forall_abelianLift (H := ⊥) isClosed_singleton _ (by aesop))
lemma exists_hom_abelianLift_eq {X} [Group X] (s : Additive X →+ QZChar G →+ QZ) : ∃ f : X →* _, ∀ χ x, abelianLift χ (f x) = .ofAdd (s (.ofMul x) χ) := by
 choose g H using fun x ↦ CompactSpace.iInter_nonempty (fun χ ↦ (isClosed_discrete {s (.ofMul x) χ}).preimage χ.2.1) fun S ↦ let T := AddSubgroup.closure (SetLike.coe S)
  have := AddCommGroup.finite_of_fg_isAddTorsion T fun χ ↦ ⟨_, (quotient_finite_of_isOpen _ out).card_pos, by ext; simpa using! (ker χ.1).pow_index_mem _⟩
  let e := ((AddMonoidHom.mk' (toAdditiveLeft ∘ toHom) (by tauto)).domRestrict T).flip.range
  (e.eq_top_of_le_card (by simpa using card_le_card_of_injective e.subtype.flip (by
 intro; simp [ext_iff]; aesop))).ge ⟨⟩ (x := (s x).domRestrict T).imp (by aesop (add simp ext_iff))
 use .mk' (g ·) ?_ <;> aesop
lemma continuous_iff_isOpen_ker [TopologicalSpace C] [IsTopologicalGroup C] {f : C →* _} : Continuous f ↔ ∀ χ : QZChar G, ((abelianLift χ).comp f).ker.IsOpen := ((continuous_pi continuous_abelianLift).isClosedEmbedding fun _ _ ↦ abelianization_ext ∘ congrFun).continuous_iff.trans (continuous_pi_iff.trans (forall_congr' fun _ ↦ ⟨(·.1 {1} ⟨⟩), .of_isOpen_ker _⟩))
end QZChar
lemma star_locIdele {E} [Field E] [NumberField E] [NumberField.IsCMField E] {v : FinPlace E} x : star (locIdele v x) = locIdele _ (x.map (conjLoc rfl).1) := Units.ext (by simp [locIdele, star_singleAdele])
variable (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K]
noncomputable def algHeckeChars : Subgroup (((𝔸f K)ˣ →* ℂˣ) × Multiplicative ((K →+* ℂ) → ℤ)) :=
 .ofDiv {θ | IsOpen (SetLike.coe _) ∧ ∀ x, θ.1 (principalIdele x) = ∏ σ, σ x ^ (-θ.2.toAdd σ)} ⟨1, by simp⟩ fun a h
 _ k ↦ ⟨(a.1.ker ⊓ _).isOpen_mono (by aesop_cat) (h.1.inter k.1), by simp_all [zpow_add₀, field]⟩
abbrev AlgHeckeChar := ↥(algHeckeChars K)
variable {K} [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
noncomputable def artinAt (v : FinPlace K) := (QuotientGroup.map _ (_root_.commutator Γ).topologicalClosure (decompGroup ..).subtype (Set.MapsTo.closure (map_derivedSeries_le_derivedSeries _ 1 ⟨·, ·, rfl⟩) (by fun_prop))).comp (localArtin Γ (placeOver v) v)
noncomputable def artinMap := Classical.epsilon fun f : _ →* _ ↦ ∀ χ a, QZChar.abelianLift χ (f a) = ∏ᶠ v, QZChar.abelianLift χ (artinAt Γ v (ideleAt v a))
