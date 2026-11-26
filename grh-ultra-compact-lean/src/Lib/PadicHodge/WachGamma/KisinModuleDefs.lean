import Lib.PadicHodge.Limit.LocalLimit
import Lib.PadicHodge.Crystalline.RegularityFrobenius
noncomputable section
section
namespace Lift
variable {p} [ThePrime p] (O Γ : Type) [CommRing O] [Algebra ℤ_[p] O] [Group Γ]
structure GalLattice where
  (Carrier) [addCommGroup : AddCommGroup Carrier] [moduleO : Module O Carrier] [moduleZp :
    Module ℤ_[p] Carrier]
  [isScalarTower : IsScalarTower ℤ_[p] O Carrier] [free : Module.Free O Carrier] [module_finite :
    Module.Finite O Carrier]
  ρ : Representation O Γ Carrier
open Module Submodule GalLattice TensorProduct Polynomial AdjoinRoot
attribute [instance] GalLattice.addCommGroup moduleO moduleZp GalLattice.isScalarTower free module_finite
instance : CoeSort (GalLattice O Γ) Type := ⟨Carrier⟩
variable {O Γ} [OverGp Γ p] (F) (K : Γ → _ → Prop) (U : _ → Finset ℤ) (Y L : GalLattice O Γ)
abbrev GalLattice.tateDual := mk _ (L.ρ.linHom (actionRep O O χ))
def InClass := IsAdmissible Y.ρ (nearOne Γ ⊔ F) ∧ (∀ g u, jump Y.ρ g u ≠ 0 → u ∈ U g) ∧ ∀ s Q, K s Q → IsWeilPair (toGp s) 0 → IsKilledBy Y.ρ s 0 Q
lemma InClass.isPotCrys (h : InClass F K U Y) : IsPotCrys Y.ρ := h.1.mono (by simp)
abbrev GalLattice.tensor := mk _ (Y.ρ.tprod L.ρ)
structure Pairing where
  (m) (integralForm) (toZp : Dual ℤ_[p] O) (thirdClass : crysCocycles (Y.tensor L).tateDual.ρ)
  pow_smul_thirdClass g : p ^ m • thirdClass.1 g = ρ _ g integralForm - integralForm
variable {Y L} (P : Pairing Y L) [Free ℤ_[p] O]
def Pairing.modPairing := ((curry P.integralForm).restrictScalars₁₂ ℤ_[p] ℤ_[p]).compr₂ (Qₗ := QuotSpan (p ^ P.m : ℤ_[p])) (mkQ _ ∘ₗ P.toZp)
def Pairing.CupBounds [TopologicalSpace Γ] (a c : Γ → _) := (fun q ↦ zmodPowToUnits _ (P.modPairing (a q.1) (L.ρ q.1 (c q.2)))) ∈ B2 (unitsRep.comp toGp)
attribute [-simp] nsmul_eq_mul
attribute [local simp] Pairing.CupBounds extensionRep Units.smul_def
def cupOrthogonal [TopologicalSpace Γ] (𝒬 : GalLattice O Γ → Prop) L := Submodule.mk ⟨⟨{c | ∀ Y (P : Pairing Y L), 𝒬 Y → ∀ a ∈ crysCocycles Y.ρ, P.CupBounds a c}, by simp_all [← Pi.add_def, add_mem]⟩, by simp [← Pi.zero_def]⟩ fun (o : O) ↦ (fun _ ↦ by simpa [Pairing.modPairing] using · · · · _ ∘ smul_mem _ o)
instance : Free ℤ_[p] L := .trans (S := O)
def Pairing.thirdPairing := LinearMap.coprod (p ^ P.m • .id) (.toSpanSingleton O _ P.integralForm)
lemma Pairing.thirdPairing_equivariant g x t : P.thirdPairing (extensionRep (.toSpanSingleton _ _ P.thirdClass) g x) (ρ _ g t) = χ g • P.thirdPairing x t := by simp [thirdPairing, smul_comm (p ^ _), P.pow_smul_thirdClass, -Representation.tprod_apply, smul_sub]; abel
lemma Pairing.modPairing_rho g y l : P.modPairing (Y.ρ g y) (L.ρ g l) = χ g • P.modPairing y l := by simpa [thirdPairing, nsmul_quot_eq_zero] using!
  congr((P.toZp $(P.thirdPairing_equivariant g (0, 1) (y ⊗ₜ l)) : QuotSpan (p ^ P.m : ℤ_[p])))
variable [Module.Finite ℤ_[p] O] [IsDomain O] {F K U K' U'} (h : InClass F K U Y) (h' : InClass F K' U' L)
instance : Module.Finite ℤ_[p] L := .trans O _
end Lift
end
section
open Algebra Finset Submodule IntermediateField.algebraAdjoinAdjoin Lift.FrobGroup
variable {p} [ThePrime p] [Γ : GroupOverGp p]
def Lift.phiInvToBdR a := (algebraMap _ BdR).comp (MulSemiringAction.toRingHom _ Ainf (φ ^ a)⁻¹)
variable [k : Lift.KummerChart Γ] {a : ℕ} {r : Ainf} {n : ℤ} (g : k.galMonoid) {x : BdR}
def Lift.KummerChart.valueField a := IntermediateField.adjoin (localFieldOf Γ') (.range fun x : k.bicommutant × k.S ↦ algebraMap _ _ x.1 * phiInvToBdR a x.2)
attribute [-simp] LinearMap.map_smul_of_tower map_smul
omit [Lift.KummerChart Γ] in
@[simp] lemma Lift.b5 : phiInvToBdR a r = 0 ↔ r = 0 := by simp [phiInvToBdR, inv_smul_eq_iff]
lemma Lift.k7 [ThePrime a] {x} (g : Gp a) (h : x ∈ hodgeFil n) : g • x ∈ hodgeFil n := (mem_hodgeFil.1 h).choose_spec ▸ by simp [↓smul_mul', ↓y6, smul_of_tower_mem, mem_hodgeFil]
namespace Lift.KummerChart
instance : MulSemiringAction k.galMonoid BdR := .compHom _ ((toGp.comp snd).domRestrict _)
instance : SMulDistribClass k.galMonoid Ainf BdR := ⟨fun ⟨_, γ, rfl⟩ ↦ smul_distrib_smul (toGp γ)⟩
@[simp] lemma d2 : g • phiInvToBdR a r = phiInvToBdR a (g • r) := by simp [phiInvToBdR, eq_inv_smul_iff, ← smul_phi_pow_comm]
lemma galMonoid_smul_mem_hodgeFil : x ∈ hodgeFil n → g • x ∈ hodgeFil n := k7 _
lemma phiInvToBdR_mem_hodgeFil_one_iff : phiInvToBdR a r ∈ hodgeFil 1 ↔ ↑(k.frobE a) ∣ r := algebraMap_mem_hodgeFil_one_iff.trans (by simp [frobE_dvd_iff, ← thetaPhiInv_phi_pow a])
lemma mul_mem_hodgeFil_iff_of_not_frobE_dvd (hr : ¬↑(k.frobE a) ∣ r) (m : ℤ) : phiInvToBdR a r ^ m * x ∈ hodgeFil n ↔ x ∈ hodgeFil n := .trans
  (by cases m <;> simp [Units.smul_def, smul_def'] <;> rfl) (smul_mem_iff' _ ((BdRPlus.isUnit_iff.2 (hr ∘ phiInvToBdR_mem_hodgeFil_one_iff.1 ∘ algebraMap_mem_hodgeFil_one_iff.2)).unit ^ m))
lemma frobE_zpow_mem_hodgeFil a m : phiInvToBdR a (k.frobE a) ^ m ∈ hodgeFil m := ((k.associated_E_xi.map _).trans BdRPlus.j6).rec fun w e ↦ mem_hodgeFil.2
  ⟨↑(w ^ m)⁻¹, by cases m <;> simp [phiInvToBdR, frobE_eq, tUnit, ← e, mul_pow, field] <;> rfl⟩
lemma phiInvToBdR_mem_valueField (s : k.S) : phiInvToBdR a s ∈ valueField a := IntermediateField.subset_adjoin _ _ ⟨(1, s), by simp⟩
lemma valueField_zero_le : valueField 0 ≤ valueField a := IntermediateField.gc.monotone_l fun _ ⟨s, e⟩ ↦ ⟨(_ * ⟨_, k.q1 _⟩, 1), by simpa [phiInvToBdR] using! e⟩
lemma mem_valueField_of_fixed (h : ∀ g : Γ', x = toGp g.1 • x) : x ∈ hodgeFil 0 ∧ x ∈ valueField 0 := (BdR.exists_sub_mem_of_smul_sub_mem _ ⊥ (sub_eq_zero.2 <| h · |>.symm)).rec
  fun _ e ↦ sub_eq_zero.1 e ▸ ⟨algebraMap_mem_hodgeFil_zero, IntermediateField.algebraMap_mem ..⟩
@[simp] lemma d8 : k.coord₀ 1 = 1 := k.coord₀_coe 1
lemma sum_map_mem_of_valueField (f : _ →ₗ[k.S] k.S) {ι} [Fintype ι] (v r : ι → _) (hv : ∀ l, v l ∈ valueField a) {W : Submodule BdRPlus _} (h : ∑ l, phiInvToBdR a (r l) * v l ∈ W) : ∑ l, phiInvToBdR a (f (r l)) * v l ∈ W := by
  choose d w hw using (instIsFractionRingSubtypeMemSubalgebraAdjoinAdjoin ..).exist_integer_multiples_of_finite _ (⟨_, hv ·⟩); choose q _ c e using fun l ↦ mem_span_image_iff_exists_fun _ (s := ⊤).1 (by simpa using (adjoin_eq_span _ (.range ((algebraMap ..).1.coprod ((phiInvToBdR a).domRestrict _).1))).le (w l).2)
  obtain ⟨u, E⟩ := isChartOf.k8 _ (Sigma.uncurry c · |>.2) ⟨⟨fun x ↦ («φ» ^ a)⁻¹ • f («φ» ^ a • x), by simp⟩, fun s
    x ↦ by simpa [smul_def', inv_smul_eq_iff, Subtype.ext_iff] using f.2 ⟨_, by simp [phi_pow_smul, ← k.coe_φ_pow]⟩ _⟩ fun ⟨l, ⟨b, s⟩, _⟩ ↦ b * Chart.ainfToBPlus ((«φ» ^ a)⁻¹ • s • r l)
  simp [k.extendToBPlus_mul, k.extendToBPlus_ainfToBPlus, Subtype.ext_iff, smul_def' d.1, ← inv_mul_eq_iff_eq_mul₀] at E hw; convert smul_mem _ u h; with_unfolding_all simpa [↓mul_comm _ (v _), ← hw, ← e, sum_mul, ← mul_sum, sum_sigma', smul_def', commutes u, mul_assoc] using! congr(algebraMap _ BdR $E)
lemma smul_sub_mem_hodgeFil_of_valueField (g : galMonoid) {m} (t : Fin m → galMonoid) (hx : x ∈ valueField a) (h : x ∈ hodgeFil 0) (hg : ∀ s : k.S, (k.frobE a).1 ∣ g • ∑ l, t l • s.1 - ∑ l, t l • s.1) : g • ∑ l, t l • x - ∑ l, t l • x ∈ hodgeFil 1 := (mem_hodgeFil.1 h).rec fun y E ↦ (y.q0 1).rec fun m ⟨r, e⟩ ↦ (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_p a) m).1 (by
  have F := sum_mem (t := univ) fun l _ ↦ galMonoid_smul_mem_hodgeFil (t l)
    (sum_map_mem_of_valueField k.coord₀ ![p ^ m • x, -1] ![1, «φ» ^ a • r] (by simp; bound)
    (by simpa [phiInvToBdR, ← E] using! algebraMap_mem_hodgeFil_iff_xi_pow_dvd.2 e))
  simpa [mul_sub, mul_sum, smul_sum, smul_sub, ← sub_eq_add_neg] using sub_mem (add_mem (galMonoid_smul_mem_hodgeFil g F) (phiInvToBdR_mem_hodgeFil_one_iff.2 (hg (k.coord₀ («φ» ^ a • r))))) F)
end Lift.KummerChart
end
section
section
open TensorProduct
variable {p} [ThePrime p] [Γ : GroupOverGp p] {ρ ρ' ρ'' : Rep ℤ_[p] Γ} (f : ρ →ₗ[ℤ_[p]] ρ') (b : ρ →ₗ[ℤ_[p]] ρ' →ₗ[ℤ_[p]] ρ'') {R R'} [Semiring R] [Module R WittCFlat] [SMulCommClass ℤ_[p] R WittCFlat] [Semiring R'] [Module R' WittCFlat] [SMulCommClass ℤ_[p] R' WittCFlat] [SMul R R'] [IsScalarTower R R' WittCFlat]
def Lift.DiagTensor (T : Rep ℤ_[p] Γ) := WittCFlat ⊗[ℤ_[p]] T deriving AddCommGroup
namespace Lift.DiagTensor
instance : Module R (DiagTensor ρ) := leftModule
deriving instance IsScalarTower R R' for DiagTensor ρ
instance : DistribMulAction (FrobGroup Γ) (DiagTensor ρ) := .compHom (_ ⊗ ρ) ((actionRep _ WittCFlat (.id _)).tprod (ρ.ρ.comp FrobGroup.snd))
instance : SMulCommClass (FrobGroup Γ) ℤ_[p] (DiagTensor ρ) := ⟨fun _ ↦ (TensorProduct.map ..).2⟩
def map : DiagTensor ρ →ₗ[WittCFlat] DiagTensor ρ' := f.baseChange _
def pair : DiagTensor ρ →ₗ[WittCFlat] DiagTensor ρ' →ₗ[WittCFlat] DiagTensor ρ'' := baseChangePairing b
def mk : WittCFlat →ₗ[WittCFlat] ρ →ₗ[ℤ_[p]] DiagTensor ρ := AlgebraTensorModule.mk ..
lemma _root_.Lift.diagTensor_induction {P : DiagTensor ρ → Prop} (h : ∀ a t, P (mk a t)) (k : ∀ x y, P x → P y → P (x + y) := by simp +contextual <;> grind) x : P x := x.induction_on (by simpa using! h 0) h k
@[simp] lemma smul_mk m a t : m • no_index (mk a t) = mk (m • a) (ρ.ρ (FrobGroup.snd m) t) := rfl
instance [SMul (FrobGroup Γ) R] [SMulDistribClass (FrobGroup Γ) R WittCFlat] : SMulDistribClass (FrobGroup Γ) R (DiagTensor ρ) := ⟨fun _ _ ↦ diagTensor_induction fun _ _ ↦ congr($(smul_distrib_smul ..) ⊗ₜ _)⟩
@[simp] lemma e2 a t : map f (no_index (mk a t)) = mk a (f t) := rfl
@[simp] lemma e0 a a' t t' : pair b (no_index (mk a t)) (no_index (mk a' t')) = mk (a * a') (b t t') := rfl
end Lift.DiagTensor
end
namespace Lift
section
open Algebra TensorProduct Ideal Ideal.Quotient FrobGroup algebraMap WittVector Witt
variable {p} [ThePrime p] [Γ : GroupOverGp p]
def smallPart m := Submodule.map (.toSpanSingleton _ (DiagTensor (.of (charRep (QuotSpan (p ^ m : ℤ_[p])) χ))) (.mk 1 1)) wittMaxIdeal
@[simp] lemma FrobGroup.e1 g : snd (.inr g) = g := rfl
@[simp] lemma FrobGroup.e3 : snd φ = 1 := rfl
lemma FrobGroup.phi_mul_comm n : Commute φ n := .prod (.all ..) (.one_left _)
lemma smul_mem_smallPart {m} (g : Γ) {x} : x ∈ smallPart m → inr g • x ∈ smallPart m | ⟨a, h, e⟩ => e ▸ ⟨_, wittMaxIdeal.smul_of_tower_mem (χ g) (mem_wittMaxIdeal.2 (mem_wittMaxIdeal.1 h · ∘ .of_map (MulDistribMulAction.toMulEquiv ..) _)), by simpa [smul_distrib_smul] using! smul_tmul ..⟩
lemma TateTwist.smallPart_spec {m} {ρ : Rep ℤ_[p] Γ} (h : ∀ y, ∀ᶠ h in nearOne Γ, ∃ w, ρ.ρ h y - y = p ^ m • w) (L : DiagTensor ρ →ₗ[WittCFlat] _) : let S := smallPart m
  (∀ d, p ^ m • d = 0 ∧ (∃ e, d = φ • e - e) ∧ (φ • d - d ∈ S → ∃ k, d - .mk 1 k ∈ S))
                  ∧ (∀ k, .mk 1 k ∈ S → k = 0) ∧ ∀ v, ∀ᶠ h in nearOne Γ, L (inr h • v - v) ∈ S := by
  let : ∀ d, p ^ m • d = L 0 := diagTensor_induction (by simp [← map_nsmul, ↓nsmul_quot_eq_zero])
  have s : (.mk · 1 : _ → type_of% (L 0)).Surjective := flip_mk_surjective _ mk_surjective
  have M x : .mk x 1 ∈ smallPart m ↔ _ := exists_congr fun _ ↦ and_congr_right'
    ((tensorQuotEquivQuotSMul ..).apply_eq_iff_eq.symm.trans (comm.trans SModEq.sub_mem))
  simp_all [s.forall, s.exists, mk_surjective.forall, mk_surjective.exists, -map_sub, show ∀ c, (.mk 1 (mk _ c) : type_of% (L 0)) = .mk _ 1 from includeRight.commutes, eq_zero_iff_dvd, r6, ← DiagTensor.mk.map_sub₂, mem_span_singleton, ← algebraMap_eq_smul_one, sub_eq_iff_eq_add]
  use fun x ↦ ⟨(y0 1 x).imp (by aesop), fun a _ ⟨w, _⟩ ↦ ?_⟩, fun _ _ ha h ↦ by
    erw [mem_wittMaxIdeal, ← q9 (R := OFlat), ← map_dvd_iff (equiv p).symm, map_pow, map_natCast, ← sub_zero ((equiv p).symm _), y3] at *
    peel h
    simpa using ha _ ∘ ((coe_inj ..).1 this).subst ∘ .map _, diagTensor_induction (fun x y ↦ (s (L (.mk 1 y))).rec fun d _ ↦ ((WittCFlat.m2 x d m).comap _).mp ((h y).mono fun _ ⟨_, _⟩ ↦ by
    erw [← M, DiagTensor.mk.map_smul₂]
    simpa [*, ← map_smul, ← DiagTensor.mk.map_smul₂] using! (·)))
    fun _ _ ↦ (·.mp <| ·.mono (by simp_all [add_sub_add_comm, add_mem]))
  obtain ⟨⟨e, rfl⟩, w, rfl⟩ := a.exists_frobEnd_sub_xi_pow_mul_eq 0, y0 1 w
  obtain ⟨c⟩ := exists_algebraMap_eq_of_frobenius_eq (toWittResidue e) (by simp_all [wittMaxIdeal, toWittResidue, frobEnd_eq_frobenius, WittVector.ext_iff])
  peel exists_algebraMap_eq_of_frobenius_eq (x - (p ^ m * w + ↑(e - c)) : WittCFlat) (by
    simp_all [← r6, j4, smul_sub, sub_eq_iff_eq_add]; ring)
  exact ⟨e - c, by simp_all [WittCFlat, wittMaxIdeal]⟩
end
open WittVector Submodule Set FrobGroup Module Fintype Algebra
variable {p} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ] {R X} [CommRing R] [AddCommGroup X] [Module R X] {Q : Submodule R X}
instance : SMulCommClass ℤ_[p] Ainf WittCFlat := inferInstance
def saturateBy (M : Submonoid R) (P : Submodule R X) := ((torsion' _ _ M).comap P.mkQ).copy
  {x | ∃ r ∈ M, r • x ∈ P} (by simp [← Quotient.mk_smul])
lemma le_saturateBy {M x} (h : x ∈ Q) : x ∈ saturateBy M Q := ⟨1, by simpa⟩
lemma mem_saturateBy_of_smul {M r s x} (d : r ∣ s) (h : s ∈ M) : r • x ∈ saturateBy M Q → x ∈
  saturateBy M Q := fun ⟨a, _⟩ ↦ ⟨a * s, by grind [dvd_def, mul_smul, smul_comm, smul_mem, mul_mem]⟩
@[elab_as_elim] lemma saturateBy_induction {ι x} {f : ι → R} {C : X → Prop} (hx : x ∈ saturateBy (.closure (range f)) Q) (h₀ : ∀ x ∈ Q, C x) (h₁ : ∀ a x, C (f a • x) → C x) : C x := by obtain ⟨_, hr, _⟩ := hx; induction hr using Submonoid.closure_induction_right generalizing x <;> grind [mul_smul, one_smul]
namespace KummerChart
def Letter := (flatFq k.f)ˣ deriving CommGroup, Finite, IsCyclic
instance : Fintype Letter := .ofFinite _
instance : Invertible (card Letter : ℤ_[p]) := IsUnit.invertible (.of_map PadicInt.toZMod _ (by
  simp [↓card_eq_nat_card, Letter, Nat.card_units, NeZero.pos]))
def letterFrob : Equiv.Perm Letter := (Units.mapEquiv (frobeniusEquiv _ p).toMulEquiv).1
def letterTeich : Letter →* k.S := (algebraMap ..).1.comp ((teichmuller p).comp (Units.coeHom _))
abbrev LetterRoot O [Monoid O] := {ζ : O // ζ ^ .card Letter = 1}
structure Coeffs where (O) [commRing : CommRing O] [algebraZp : PadicIntegerRing O p]
                       (ζ : LetterRoot O)
attribute [instance] Coeffs.commRing Coeffs.algebraZp
instance : CoeSort Coeffs Type := ⟨Coeffs.O⟩
structure JumpLattice (O : Coeffs) extends toGalLattice : GalLattice O Γ where
  (U : _ → _)  (embJumps)
  inClass : InClass (.map Γ'.subtype ⊤) ⊥ embJumps toGalLattice
  embJumps_subset {g i} : g O.ζ = (theta (letterTeich i)).1 → embJumps g ⊆ U i
variable {k O} {L : JumpLattice O} (L' : JumpLattice O) (i : Letter) (l a : ℕ) (u : ℤ)
@[simp] abbrev Letter.stepBack := (k.letterFrob ^ a)⁻¹ i
@[grind] def stdExponent := if a < l then 0 else -u
namespace JumpLattice
abbrev Ambient := DiagTensor (.of (overZp L.ρ))
abbrev wittMap (F : L.Carrier →ₗ[O] L'.Carrier) : L.Ambient →ₗ[WittCFlat] L'.Ambient := DiagTensor.map F
def ainfLattice := span Ainf (M := L.Ambient) (range (DiagTensor.mk 1))
abbrev Functional := L.Ambient →ₗ[Ainf] BdR
def forms := {μ : L.Functional | ∀ t (g : k.Γ'), μ (.mk 1 (L.ρ g t)) = toGp g.1 • μ (.mk 1 t)}
lemma frobGroup_smul_smul (m : FrobGroup Γ) (r : Ainf) (x : L.Ambient) : m • r • x = (m • r) • m • x := smul_distrib_smul ..
@[simps] def semilinearAct (m : FrobGroup Γ) : L.Ambient →ₛₗ[MulSemiringAction.toRingHom _ Ainf m] L.Ambient := ⟨⟨_, smul_add m⟩, frobGroup_smul_smul m⟩
def kisinAinf := saturateBy (.powers tau) L.ainfLattice ⊓ ⟨⟨⟨{x | ∀ n, ∀ μ ∈ L.forms, μ (φ ^ (n + 1) • x) ∈ hodgeFil 0}, by aesop⟩, by simp⟩, by simp_all [frobGroup_smul_smul, smul_of_tower_mem]⟩
def crysForms := {μ ∈ L.forms | ∃ l : _ →ₗ[ℤ_[p]] Bcris, ∀ t, μ (.mk 1 t) = algebraMap _ _ (l t)}
def valueFieldPoints (Q : Submodule Ainf L.Ambient) : Submodule k.S L.Ambient := ⟨⟨⟨{x ∈ Q | ∀ μ ∈ forms, μ x ∈ valueField 0}, by aesop⟩, by simp⟩, fun s _ ↦ .imp (smul_mem _ _) (by
  simpa [phiInvToBdR, smul_def'] using! mul_mem (phiInvToBdR_mem_valueField s) <| · · ·)⟩
abbrev kisinModule := valueFieldPoints L.kisinAinf
def frobKisinAinf := L.kisinAinf.comap (semilinearAct (φ ^ l)⁻¹)
def kisinLocAinf := saturateBy (.closure (range (k.frobE · |>.1))) L.kisinAinf
def kisinLoc := L.valueFieldPoints kisinLocAinf
abbrev Hom := L.ρ.IntertwiningMap L'.ρ
abbrev Hom.wittMap {L'} (F : Hom L') := L.wittMap _ F.1
def mulZeta : L.Hom L := ⟨.lsmul _ _ O.ζ, by aesop⟩
def letterOp := k.letterTeich i⁻¹ • L.mulZeta.wittMap
def letterPart := (L.letterOp i - 1).ker.restrictScalars Ainf
def letterProj := ⅟(card Letter : ℤ_[p]) • ∑ n ∈ .range (card Letter), L.letterOp i ^ n
def formsOfType := {μ ∈ L.forms | ∀ t, μ (L.letterProj i (.mk 1 t)) ∈ hodgeFil (-u)}
abbrev jumpMultiplicity := ∑ γ with γ O.ζ = ↑(theta (k.letterTeich i)), jump L.ρ γ u
abbrev fracSpan := saturateBy (nonZeroDivisors _) L.ainfLattice
def jumpBound := sInf {a : ℕ | ∀ u, jump ((overZp L.ρ).comp k.Γ'.subtype) (ofId ..) u ≠ 0 → -a ≤ u ∧ u ≤ a}
def valueAt (μ : L.Functional) : L.Ambient →ₛₗ[phiInvToBdR a] BdR := ⟨μ.1.comp (semilinearAct (φ ^ a)⁻¹).1, by simp [phiInvToBdR, smul_def']⟩
