import Lib.PadicComparison.Crystalline.PeriodLifting
import Lib.Cohomology.Duality.Contraction
noncomputable section
attribute [local instance 2000] Algebra.toSMul Algebra.toModule Algebra.FormallyEtale.of_isSeparable
attribute [-simp] mul_eq_zero isUnit_map_iff
open CategoryTheory Function Ideal WittVector Algebra IsLocalization RingHom PadicTest Functor CommAlgCat Quot FormallySmooth FormallyUnramified
class EmbeddedInQpBar (p : outParam ℕ) (k : outParam Type) [Field k] extends
  ThePrime p, Algebra k (PadicAlgCl p), CharZero k
section
variable {p} [ThePrime p] (c : PadicTest)
namespace PadicTest
instance algebraGenericRing : ∀ c : PadicTest, Algebra ℂ_[p] c.GenericRing := (@exists_eq _ (map _ ·.structureMap (powers_le_comap_powers p _) |>.toAlgebra)).choose
def structMap := algebraMap ℂ_[p] c.GenericRing
lemma structMap_coe x : c.structMap x.1 = algebraMap _ _ (c.structureMap x) := by simpa +instances [structMap, algebraGenericRing] using! map_eq ..
instance : IsScalarTower OC ℂ_[p] c.GenericRing := .of_algebraMap_eq (c.structMap_coe · |>.symm)
def thetaGeneric : Localization.Away (p : WittVector p c.TiltRing) →+* c.GenericRing := map _ (fontaineTheta c.ProdRing p) (powers_le_comap_powers p _)
lemma thetaGeneric_algebraMap_ainf a : c.thetaGeneric (algebraMap _ _ a) = c.structMap (theta a) := by erw [map_eq, fontaineTheta_map_tiltMap, structMap_coe]
lemma thetaGeneric_mu : c.thetaGeneric (algebraMap _ _ mu) = 0 := by simp [thetaGeneric_algebraMap_ainf, mu]
abbrev Thickening := _ ⧸ ker c.thetaGeneric ^ 2
def thickeningProj := Ideal.Quotient.lift (ker c.thetaGeneric ^ 2) _ (pow_le_self (by simp))
instance isLocalization_generic {S} [CommRing S] (f : S →+* c.ProdRing) : IsLocalization (.map f (.powers ↑p)) c.GenericRing := by simp; infer_instance
lemma thetaGeneric_spec : Surjective c.thickeningProj ∧ ker c.thetaGeneric = span {algebraMap _ _ xi} := ⟨(surjective_lift _).2 (map_surjective_of_surjective _ _ _ fontaineTheta_surjective_of_isAIC), by simp [thetaGeneric, ker_map]; rfl⟩
lemma ker_thickeningProj_sq : ker c.thickeningProj ^ 2 = ⊥ := by simp [thickeningProj, ker_quotient_lift, ← Ideal.map_pow]
@[instance_reducible]
def uniqueLift := ((unique_subtype_iff_existsUnique (fun ρ : PadicAlgCl p →ₐ[ℤ_[p]] _ ↦ ∀ z, c.thickeningProj (ρ z) = c.structMap z)).2 (let := restrictScalars ℤ_[p] ℂ_[p] c.GenericRing
  have := (FormallyEtale.of_isLocalization (nonZeroDivisors ℤ_[p])).comp _ ℚ_[p] (PadicAlgCl p)
  existsUnique_of_exists_of_unique ⟨_, liftOfSurjective_apply ⟨.comp _ (algebraMap ..), by tauto⟩ ⟨_, (IsScalarTower.algebraMap_apply _ Ainf c.Thickening · ▸ (thetaGeneric_algebraMap_ainf ..).trans (congrArg _ ((OC.toPadicIntAlgHom _).2 _)))⟩ c.thetaGeneric_spec.1 ⟨2, c.ker_thickeningProj_sq⟩⟩ (ext' _ ⟨2, c.ker_thickeningProj_sq⟩ · · <| by simp [·, ·]))).some
variable {c d} (f : c ⟶ d)
def mapGeneric : c.GenericRing →ₐ[ℂ_[p]] d.GenericRing := ⟨map _ f.1 (powers_le_comap_powers p _), fun _ ↦ by
  simp +instances [algebraMap_toAlgebra, algebraGenericRing, IsLocalization.map_map]; congr
  exact f.comp_algebraMap⟩
lemma mapGeneric_algebraMap x : mapGeneric f (algebraMap _ _ x) = algebraMap _ _ (f.1 x) := lift_eq ..
def mapThickening : c.Thickening →ₐ[Ainf] d.Thickening := quotientMapₐ _ ⟨map _ (_ : WittVector p c.TiltRing →+* WittVector p d.TiltRing) (powers_le_comap_powers p _), ((map_eq ..).trans <| congrArg _ <| ((tilt ⋙ wittFunctor).map f).1.2 ·)⟩ (by simp [thetaGeneric_spec, span_singleton_pow, -AlgHom.coe_mk])
lemma thickeningProj_mapThickening : ∀ x, d.thickeningProj (mapThickening f x) = mapGeneric f (c.thickeningProj x) := ind fun x ↦ show d.thetaGeneric _ = mapGeneric f (c.thetaGeneric _) by simp [thetaGeneric, mapGeneric, IsLocalization.map_map, RingHom.comp, fontaineTheta_map_tiltMap, tilt, wittFunctor]
def genericAlg : PadicTest ⥤ CommAlg ℂ_[p] := .mk _ (ofHom <| mapGeneric ·) (fun _ ↦ hom_ext (AlgHom.ext map_id)) (by aesop (add simp [mapGeneric, IsLocalization.map_map]))
def genericTest : PadicTest ⥤ TestRing := ObjectProperty.lift _ {genericAlg ⋙ forget₂ _ CommRingCat with obj := _, map f := CommRingCat.ofHom (mapGeneric f).1} (·.isTest.localization)
end PadicTest
abbrev genericCoeff := moduleCoeff (asModules genericAlg)
lemma exists_periodAlg_iso_genericAlg : ∃ θ : asModules (tilt ⋙ periodAlg OC) ⋙ tensorWith _ _ ≅
  asModules genericAlg, ∀ c a w, θ.hom c (a ⊗ₜ .of _ _ (1 ⊗ₜ w)) = c.structMap a * algebraMap _ _
  (fontaineTheta _ p w) := let j := isoOfAppBijective (algFunctor.whiskerLeft (algCompletion.of ..))
                             (AdicCompletion.of_bijective_iff.2 ·.isAdicComplete_prodRing)
  ⟨isoWhiskerRight (isoWhiskerRight thetaIso _ ≪≫ j.symm) (asModules (𝟭 _) ⋙ tensorWith ..)
    ≪≫ NatIso.ofComponents (·.isLocalization_generic _ |> (isLocalization_iff_isPushout _ ℂ_[p]).1
    |>.symm.out.equiv.toModuleIso) fun f ↦ ModuleCat.hom_ext (tmul_ext fun _ _ ↦ by
    erw [map_smul (mapGeneric f), mapGeneric_algebraMap]; rfl), fun c a w ↦ .trans
    (congrArg (a • algebraMap c.ProdRing c.GenericRing ·) (c.thetaIso_hom_one_tmul w ▸ (congrArg _
    (adicMap_algebraMap ..)).trans (j.hom_inv_id_app_apply ..))) (c.algebraGenericRing.4 ..)⟩
end
variable {p k} [Field k] [EmbeddedInQpBar p k] (c : PadicTest)
instance : Algebra k ℂ_[p] := .restrictScalars k (PadicAlgCl p) _
instance : CoeffAction k genericCoeff := ⟨CoeffAction.act.comp (algebraMap k ℂ_[p])⟩
def genericOver := genericAlg ⋙ restrictAlg k _
instance : Algebra k c.Thickening := (c.uniqueLift.1.1.1.1.comp (algebraMap ..)).toAlgebra
def thickeningOver : PadicTest ⥤ CommAlg k := by
  refine ⟨(.of k ·.Thickening), fun {c d} f ↦ ofHom ⟨mapThickening f, fun _ ↦ congr($(d.uniqueLift.2 ⟨.comp ((mapThickening f).restrictScalars _) _, ((thickeningProj_mapThickening f _).trans <| c.uniqueLift.1.1.2 · ▸ (mapGeneric f).2 _)⟩).1 _)⟩, ?_, ?_⟩ <;> intros <;> ext ⟨⟩ <;>
    congrm ⟦?_⟧ <;> simp; exacts [map_id _, .symm (IsLocalization.map_map ..)]
lemma hasZariskiDescent_genericOver {C} [Category C] Θ {F} (h : @HasPartitions C _ (Θ ⋙ ringFunctor) F) : HasZariskiDescent (Θ ⋙ genericOver ⋙ forget₂ ..) F := h.hasZariskiDescent ⟨_, by intros; ext; symm; apply mapGeneric_algebraMap⟩ (eq_zero_of_algebraMap_genericRing <| Θ ·) fun _ ↦ (PadicTest.isTest _).isComparableRing_of_associated exists_associated_localization
namespace thickeningOver
def proj : thickeningOver ⟶ genericOver := ⟨(CommAlg.homOfRingHom _ <| ·.uniqueLift.1.1.2 ∘' _), by intros; ext; apply thickeningProj_mapThickening⟩
def mulMu : genericOver c →+ thickeningOver c := c.thickeningProj.toAddMonoidHom.liftOfSurjective c.thetaGeneric_spec.1 ⟨.mulLeft ⟦_⟧, fun _ h ↦ (sq _).ge.trans_eq c.ker_thickeningProj_sq (mul_mem_mul c.thetaGeneric_mu h)⟩
lemma mulMu_thickeningProj b : mulMu c (c.thickeningProj b) = (algebraMap _ _ mu * b :) := AddMonoidHom.liftOfRightInverse_comp_apply ..
lemma proj_mulMu : ∀ t, proj c (mulMu c t) = 0 := c.thetaGeneric_spec.1.forall.2 fun _ ↦ by
  erw [mulMu_thickeningProj, map_mul, thetaGeneric_mu, zero_mul]
lemma mulMu_proj_mul b : ∀ t, mulMu c (proj c b * t) = b * mulMu c t := c.thetaGeneric_spec.1.forall.2 fun _ ↦ by
  erw [← map_mul, mulMu_thickeningProj, mulMu_thickeningProj, mul_left_comm]; rfl
lemma map_mulMu d (f : c ⟶ d) : ∀ t, thickeningOver.map f (mulMu c t) = mulMu d (genericOver.map f t) := c.thetaGeneric_spec.1.forall.2 fun _ ↦ by erw [← thickeningProj_mapThickening, mulMu_thickeningProj, mulMu_thickeningProj, map_mul (mapThickening f), AlgHom.commutes]
lemma exact_mulMu_proj : Surjective (proj c) ∧ Injective (mulMu c) ∧ Exact (mulMu c) (proj c) := by
  obtain ⟨⟨s, z⟩, t, u⟩ := c.thetaGeneric_spec, (IsUnit.mk0 (theta tau).1 (by simp)).map c.structMap
  have e y (a : c.GenericRing) : mulMu c a = ⟦algebraMap _ _ xi * y⟧ ↔ t * a =
    c.thetaGeneric y := by
    obtain ⟨⟨⟩, ⟨⟩⟩ := s a
    erw [mulMu_thickeningProj, Ideal.Quotient.eq, u, ← thetaGeneric_algebraMap_ainf, ← map_mul, ← sub_mem_ker_iff, z, span_singleton_pow]
    simp [← xi_mul_tau, mul_assoc, ← mul_sub, mem_span_singleton, sq]
    exact IsLeftRegular.dvd_cancel_left (IsSMulRegular.of_flat (R := WittVector p c.TiltRing) (.of_right_eq_zero_of_smul fun x h ↦ by_contra (verschiebung_nonzero · |>.elim fun j ⟨y, m, e⟩ ↦ m (IsLeftRegular.pow (R := c.TiltRing) (p ^ j) c.isPerfectTorsionFree_tilt.2 (by
      subst e; simpa using! (iterate_verschiebung_mul_coeff _ y 0 j).symm.trans congr(($h).1 _))))))
  use s, by simpa [injective_iff_map_eq_zero'] using! e 0, ind fun x ↦ ⟨fun h ↦ mem_span_singleton.1 (z.le h) |>.elim fun _ ↦ (⟨_, · ▸ (e ..).2 (t.mul_inv_cancel_left _)⟩), by grind [proj_mulMu]⟩
def teichmullerLift : tilt c →* thickeningOver c := (algebraMap _ c.Thickening).1.comp (@teichmuller p c.TiltRing ..)
end thickeningOver
end
noncomputable section
section
open CategoryTheory TensorProduct Functor Ideal PadicTest MonoidalCategory Quotient Submodule ZMod
variable {p} [ThePrime p] (c : PadicTest) (I : Ideal c.GenericRing) {S X} [CommRing S] [AddCommMonoid X]
instance (F : ModuleCat S ⥤ ModuleCat S) [F.Additive] : (moduleCoeff F).Additive := instAdditiveComp ..
def PadicTest.nearZeros [Module S X] (κ : ∀ {d}, (c ⟶ d) → Submodule S X) : Submodule S X := ⟨⟨⟨{y | ∃ a ∈ I, ∀ d f, IsUnit (mapGeneric f (1 - a)) → y ∈ @κ d f}, fun ⟨a, _⟩ ⟨b, _⟩ ↦ ⟨1 - (1 - a) * (1 - b), by simp_all [← eq_zero_iff_mem, add_mem]⟩⟩, by aesop⟩, by aesop⟩
variable (Ω) [CommRing.{0} Ω] [Algebra Ω ℂ_[p]]
def genericTestOver : PadicTest ⥤ TestOver Ω := ObjectProperty.lift _ (genericAlg ⋙ restrictAlg ..) (·.isTest.localization)
end
open AddCommGrpCat thickeningOver CategoryTheory CliffordAlgebra ExteriorAlgebra HodgeTest TotalH
set_option backward.isDefEq.respectTransparency false
structure HodgeTatePair {p k} [Field k] [EmbeddedInQpBar p k] where (test : PadicTest) (rank : ℕ)
seal thickeningOver PadicTest.genericAlg
variable {p k} [Field k] [EmbeddedInQpBar p k] (X : HodgeTatePair) (t : k)
abbrev HodgeTatePair.GenericRing := genericOver X.test
@[simps] instance HodgeTatePair.instCategory : Category HodgeTatePair := by refine' @.mk _ { Hom X Y := Σ f : X.test ⟶ Y.test, (Fin X.rank → X.GenericRing) →ₛₗ[((genericOver.map f).hom : X.GenericRing →+* Y.GenericRing)] Y.GenericRing × (Fin Y.rank → Y.GenericRing), id _ := ⟨𝟙 _, ⟨(0, ·), by simp⟩, by simp⟩, comp f g := ⟨f.1 ≫ g.1, ⟨fun m ↦ (genericOver.map g.1 (f.2 m).1, 0) + g.2 (f.2 m).2, by simp [ add_add_add_comm]⟩, by simp⟩} .. <;> intros <;> exact congr(⟨_, $(by ext <;> simp [add_assoc])⟩)
def HodgeTatePair.toTest : HodgeTatePair ⥤ PadicTest := .mk test (·.1)
def HodgeTatePair.toHodgeTest : HodgeTatePair ⥤ HodgeTest k := by refine ⟨(⟨·.GenericRing, _⟩), (⟨_, .snd .. ∘ₛₗ ·.2⟩), ?_, ?_⟩ <;> intros <;> apply HodgeTest.hom_ext <;> aesop
abbrev HodgeTatePair.PairRing := (thickeningOver.proj X.test).1.pullback (TrivSqZeroExt.fstHom k _ (Fin X.rank → X.GenericRing))
def HodgeTatePair.pairAlg : HodgeTatePair ⥤ CommAlg k := by refine ⟨(.of k ·.PairRing), @fun X _ f ↦ CommAlgCat.ofHom (by
  have e (x : X.PairRing) := x.2 ▸ thickeningOver.proj.naturality_apply f.1 x.1.1
  refine' .codRestrict (.prod { toFun (x : X.PairRing) := thickeningOver.map f.1 x.1.1 + thickeningOver.mulMu _ (f.2 x.1.2.snd).1, .. } (((toHodgeTest ⋙ sqZeroExt).map f).1.comp (.pullbackSnd ..))) _ fun x ↦ (map_add ..).trans
    ((add_eq_left.2 (proj_mulMu ..)).trans (e x)) <;> as_aux_lemma => intros; simp [*, add_mul, mul_add, ← mulMu_proj_mul _, proj_mulMu, TrivSqZeroExt.algebraMap_eq_inl', mul_comm (mulMu _ _)] <;> abel), ?_, ?_⟩ <;> intros <;> ext : 4 <;>
  (try show _ = thickeningOver.map _ (_ + _) + _) <;> simp [← map_mulMu, add_assoc] <;> rfl
def HodgeTatePair.toSqZero :
  pairAlg ⟶ toHodgeTest ⋙ sqZeroExt where app _ := CommAlgCat.ofHom (.pullbackSnd ..)
def HodgeTatePair.toGeneric : pairAlg ⟶ toTest ⋙ genericOver := toSqZero ≫ {app _ := baseProj _}
abbrev HodgeTatePair.formCoeff := toHodgeTest ⋙ hodgeCoeff
abbrev HodgeTatePair.scalarCoeff := toTest ⋙ genericCoeff
instance HodgeTatePair.instActF : CoeffAction k scalarCoeff := ⟨.comp ⟨(restrictAlong _).mapEnd _, rfl, by tauto⟩ CoeffAction.act⟩
attribute [local simp] Algebra.algebraMap_eq_smul_one mul_add
def HodgeTatePair.contractionCocycle : Cocycle formCoeff formCoeff := ⟨(AddCommGrpCat.uliftFunctor.map <| ofHom <| contraction ·.2 |>.toAddMonoidHom), fun f g ↦
  have h x : contraction _ x = exteriorMapSnd g.2 (contraction _ x) + contraction _ (exteriorMapSnd f.2 x) ∧ exteriorMapSnd (f ≫ g).2 x = exteriorMapSnd g.2 (exteriorMapSnd f.2 x) := by induction x using left_induction <;> simp_all <;> module
  ext (congrArg _ <| h ·.1 |>.1)⟩
def HodgeTatePair.contractionPow : ℕ → TotalH formCoeff scalarCoeff
  | 0 => .homClass ⟨fun X ↦ AddCommGrpCat.uliftFunctor.map (ofHom (@algebraMapInv _ _ (_ →
    X.GenericRing) ..).toAddMonoidHom), fun _ _ f ↦ ext (congr(⟨$(algebraMapInv_exteriorMap
    (toHodgeTest.map f).2 ·.1)⟩))⟩ | h + 1 => .comp contractionCocycle.cohomClass (contractionPow h)
abbrev HodgeTatePair.wedgePairing : abTensor formCoeff formCoeff ⟶ formCoeff := toHodgeTest.whiskerLeft exteriorAlg.mulPairing
lemma HodgeTatePair.act_comp_contractionPow h : comp (.homClass (toHodgeTest.whiskerLeft (End.asHom (CoeffAction.act t)))) (contractionPow h) = t • contractionPow h := by
  induction' h with _ e; simp [smul_eq_comp, contractionPow, ← homClass_comp]; congr 1 with X
  exact congr(⟨$((@algebraMapInv X.GenericRing ..).map_smul_of_tower t _)⟩)
  rw [contractionPow, ← TotalH.comp_assoc_of_sq (contractionCocycle.cohomClass_naturality ..), e, comp_smul]
  intro _ _ f; ext; exact congr(⟨$(by simpa using! (contraction f.2).2 (t • 1) _)⟩)
lemma HodgeTatePair.scaleModule_comp_contractionPow h : pullbackAlong (toHodgeTest.whiskerLeft (scaleModule t _)) (contractionPow h) = t ^ h • contractionPow h := by
  induction' h with _ e
  simp [contractionPow, ← homClass_comp]; congr with _
    x; exact congr(⟨$(algebraMapInv_exteriorMap (scaleModule t (𝟭 _) _).2 x.1)⟩)
  rw [contractionPow, ← TotalH.comp_assoc_of_sq (contractionCocycle.cohomClass_naturality ..), ← homClass_comp_homClass_comp, act_comp_contractionPow, comp_smul, e, smul_smul, comp_smul, pow_succ']
  intro _ _ f; have := f.2.2 (t • 1)
  refine ext (congrArg _ <| (fun x ↦ ?_ : ∀ x, contraction f.2 (exteriorMap (t • .id) x) = t • exteriorMap (t • .id) (contraction f.2 x) ∧ exteriorMapSnd f.2 (exteriorMap (t • .id) x) = exteriorMap (t • .id) (exteriorMapSnd f.2 x)) ·.1 |>.1)
  induction x using left_induction <;> simp_all [-LinearMap.map_smul_of_tower]; module
