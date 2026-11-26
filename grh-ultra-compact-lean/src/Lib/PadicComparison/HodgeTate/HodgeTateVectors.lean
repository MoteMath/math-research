import Lib.General.Geometry.ChartedSchemes
import Lib.Shimura.AbelianScheme.Specialisation
import Lib.Cohomology.Etale.EllAdicCohomology
import Lib.Cohomology.ProjectiveLine.NormalizationPullback
import Lib.Cohomology.SmoothBaseChange.SmoothBaseChange
import Lib.PadicComparison.HodgeTate.GaloisTwist
import Lib.PadicHodge.Crystalline.RegularityFrobenius
section FoldSeg0
noncomputable section
section
open CategoryTheory Ideal Quotient Amax WittVector Algebra Lift
variable {p} [ThePrime p]
instance : Module.Flat Amax Bcris := by apply_rules +allowSynthFailures [Localization.flat]
abbrev crysPeriodCoeff : AbFunctor (CrysTest Amax) :=
  moduleCoeff (asModules (ObjectProperty.ι _) ⋙ tensorWith Bcris Bcris)
class CrysPeriodAlgebra extends Algebra Ainf Amax, IsPeriodRingPair p Amax Bcris where
  p_cube_dvd_mu : p.cast ^ 3 ∣ algebraMap mu
  isUnit_mu : IsUnit (ofId _ Bcris (algebraMap mu))
def ocToAmaxModPd [h : CrysPeriodAlgebra] : OC →+* _ ⧸ pdIdeal Amax :=
  .liftOfSurjective _ theta_surjective ⟨algebraMap .., fun _ a ↦ eq_zero_iff_mem.2
  (mem_of_dvd _ (by grw [h.dvd_xi, theta_eq_zero_iff_xi_dvd.1 a]) h.p_mem_pdIdeal)⟩
lemma ocToAmaxModPd_untilt [h : CrysPeriodAlgebra] t : ocToAmaxModPd t.untilt =
  h.algebraMap (teichmuller p t) := theta_teichmuller t ▸ theta.liftOfSurjective_comp_apply ..
lemma exists_crysPeriodAlgebra {N} {y : OC} (hy : ↑p ∣ y ^ N) : ∃ h : CrysPeriodAlgebra,
  IsScalarTower ℤ_[p] Ainf
  Amax ∧ (∀ (m : FrobGal) a, m • h.algebraMap a = h.algebraMap (m • a)) ∧ ocToAmaxModPd y = 0 := by
  obtain ⟨⟨t, rfl⟩, mem⟩ := untilt_surjective_of_isAIC (p := p) y, @p_pow_dvd_of_mem_pow p _ 1
  simp at mem
  let := compHom Amax (MulSemiringAction.toRingHom FrobGal Ainf (.ofAdd (N ⊔ 3), 1))
  let h : CrysPeriodAlgebra := ⟨⟨⟨.of_ne_zero NeZero.out, {}⟩, mem (smul_xi_mem_span _),
    isUnit_smul_of_dvd_mu _ (by simp [← xi_mul_tau])⟩,
    p_pow_dvd_of_mem_pow (pow_le_pow_right le_sup_right (by simpa [mu, FrobGal.smul_def]
    using (pow_p_pow_sub_mem_of_xi_dvd ⟨_, xi_mul_tau.symm⟩ _))), isUnit_smul_of_dvd_mu _ dvd_rfl⟩
  use h, .of_algebraMap_eq (by rw [compHom_algebraMap_eq]; aesop), by simp [compHom_algebraMap_eq,
    smul_smul, mul_comm],
    ocToAmaxModPd_untilt t ▸ eq_zero_iff_mem.2 (mem_of_dvd _ (mem ?_) h.p_mem_pdIdeal)
  grw [Witt.mem_span_pair_iff, ← untilt_dvd_iff, untilt_constantCoeff_xi_dvd_p, hy]
  simp [untilt_frobGal_smul, smul_teichmuller, pow_dvd_pow, (Nat.lt_pow_self Fact.out).le.trans']
end
open Function Algebra RingHom NeZero TensorProduct FormallyUnramified Etale IsLocalization Away
variable {p} [ThePrime p] (C D) [CommRing.{0} C] [CommRing.{0} D] [Algebra C D]
lemma exists_etale_lift B [CommRing B] [Algebra D B] [e : Etale D B] (s : Surjective
    (algebraMap C D)) : ∃ T : CommAlg C, Etale C T ∧ Nonempty (D ⊗[C] T ≃ₐ[D] B) := by
  algebraize [(algebraMap D B).comp (algebraMap C D)]
  simp [iff_isStandardSmoothOfRelativeDimension_zero] at *
  let ⟨_, _, _, _, P, d⟩ := e
  have : P.HasCoeffs C := ⟨by tauto⟩
  let Q := P.1.ofHasCoeffs C
  let e := P.tensorModelOfHasCoeffsEquiv C
  exact ⟨.of _ (Localization.Away Q.jacobian), ⟨_, _,
    _, .instSum, ⟨.comp (.localizationAway _ Q.jacobian) Q, by
      simp [algebraMap_isUnit, smul_def, -isUnit_map_iff]⟩,
    by simp_all +arith [Presentation.dimension]⟩, ⟨(tensorProductEquivTMulRight _ _ Q.jacobian
    _).trans (((atUnit _ _ _ (.of_map e (1 ⊗ₜ Q.jacobian) (@Q.jacobian_eq_jacobiMatrix_det .. ▸
    .mul (by simp) (P.aeval_jacobianOfHasCoeffs C ▸ P.2)))).symm.restrictScalars _).trans e)⟩⟩
lemma perfectRing_of_etale [Etale C D] [k : PerfectRing C p] (h : (p : C) = 0) : PerfectRing D p :=
  (k.pow ..).rec fun k ↦ pow_one p ▸ let := (frobPow (natCast_eq_zero_of_algebra h D) 1).toAlgebra
  let := @of_restrictScalars C D D _ _ _ _ (_) _ (by use by simp [smul_toAlgebra, smul_def, mul_pow,
    mul_assoc]) _ ((of_bijective k).stableUnderComposition (frobPow h 1) _ (etale_algebraMap.2 ‹_›))
  have := @Module.FaithfullyFlat.of_comap_surjective D D _ _ _ _ fun x ↦ ⟨x, by
    ext; exact x.2.pow_mem_iff_mem _ (pos _)⟩
  ⟨FaithfulSMul.algebraMap_injective .., fun _ ↦ (IsEffective.of_faithfullyFlat ..).1 (sub_eq_zero.2
    ((IsUnit.of_pow_eq_one (.trans congr($(show frobPow (natCast_eq_zero_of_algebra h _) 1 =
    (algebraMap D _).comp (lmul' D).1 by
    ext <;> simp <;> erw [← pow_one p, tmul_one_eq_one_tmul]; rfl) _)
    (by simp [lmul_elem, map_one])) out).mul_right_cancel (one_tmul_mul_elem _).symm))⟩
open CategoryTheory ConcreteCategory Ideal ObjectProperty CommAlgCat ULift PadicTest
open WittVector hiding map_surjective
variable {p : _} [ThePrime p] [h : CrysPeriodAlgebra]
def crysThickening : PadicTest ⥤ CrysTest Amax :=
  ObjectProperty.lift _ (_ ⋙ periodAlg ..) (isCompleteTorsionFree_completion <|
  isSMulRegular_tensor_witt h.regular ·.isPerfectTorsionFree_tilt)
def toPdReduction : ι _ ⋙ restrictAlg Ainf _ ⟶ pdReduction ocToAmaxModPd ⋙ restrictAlg _ _ :=
  .mk fun E ↦ CommAlg.homOfRingHom (pdQuotientMk _)
  fun _ ↦ by erw [eq_comm, RingHom.comp_apply, RingHom.comp_apply, liftOfSurjective_comp_apply]; rfl
@[irreducible] def testToThickening : algFunctor ⟶ crysThickening ⋙ pdReduction ocToAmaxModPd :=
  thetaIso.2 ≫ (baseChangeTranspose ..).2 (tilt.whiskerLeft (baseChangeTranspose _
  (periodAlg ..) (wittFunctor.whiskerLeft ((algBaseChange _).whiskerLeft
  (algCompletion.of ..)))) ≫ by exact crysThickening.whiskerLeft toPdReduction)
lemma testToThickening_theta c x : testToThickening c (fontaineTheta c.ProdRing p x) =
  Quot.mk _ (.of _ _ (1 ⊗ₜ x)) := .trans (by erw [← thetaIso_hom_one_tmul, testToThickening,
  ← NatTrans.comp_app_apply, Iso.hom_inv_id_assoc]; rfl) (one_smul OC _)
def HasCrysComparison :=
  (Comparison.restrict crysThickening crysPeriodCoeff).IsBijectiveOn testToThickening
lemma hasCrysComparison_of_witt (b : FullSubcategory IsPerfectTorsionFree) {T} (k :
  T ⟶ wittFunctor.obj b.1) (hk : IsBijOnCompletion p k.hom.toLinearMap) :
  HasCrysComparison (restrictAlg Ainf _ ⋙ reprBy T) := have := b.2.1
  Iff.mpr (Comparison.isBijective_congr (p := pointMap ⟨k ≫ algBaseChangeAdj.homEquiv _ _
    ((algCompletion.of ..).1 _) ≫ toPdReduction.1 ⟨_, isCompleteTorsionFree_completion
    (isSMulRegular_tensor_witt h.regular b.2)⟩⟩) (p' := homTiltIso.1 ≫ algFunctor.whiskerLeft
    (pointMap ⟨k ≫ algBaseChangeAdj.1.1 _⟩)) (v := tilt.whiskerLeft (pointMap (Y := periodAlg .. ⋙
    reprBy _) ⟨𝟙 _⟩) ≫ .mk fun _ ↦ by exact ↾(⟨⟨·.1⟩⟩)) (by ext; exact up_inj.2 (ext_apply fun _ ↦
    (congrArg _ (thetaIso_hom_one_tmul ..)).trans ((testToThickening_theta ..).trans
    (congrArg _ (.symm (adicMap_algebraMap ..)))))) (.of_bijective fun E ↦ ULift.map_bijective.2
    ((hk.comp_bijective _ (by erw [E.p_eq_zero_mod_pdIdeal, span_zero]; tauto)).comp
    ((Bijective.of_existsUnique (· ≫ toPdReduction E) (by
    rintro ⟨f, c⟩
    obtain ⟨F, ⟨⟩⟩ := (constantCoeff.liftOfRightInverse (teichmuller p) .refl).symm.surjective
      ⟨f, by simpa [witt_reduction_spec OFlat] using!
      (map_natCast ..).trans E.p_eq_zero_mod_pdIdeal⟩
    let ⟨w, a, H⟩ := E.2.existsUnique_witt_lift p_eq_zero_of_algebra_oFlat F
    use! w, (w.comp _).congr_fun ((E.2.existsUnique_witt_lift p_eq_zero_of_algebra_oFlat
      (F.comp _)).unique (a <| ·.map _) ((toPdReduction _).1.2 · |>.trans (c _).symm)), ext_apply a,
      fun g k ↦ ext_apply (RingHom.congr_fun (H _ (congr($k.1 ·)))))).comp
    ((algBaseChangeAdj.homEquiv ..).bijective.comp ((isBijOnCompletion_completion.comp_bijective
    ((algCompletion.of ..).1 _) E.2.2).comp InducedCategory.homEquiv.bijective)))))
    (.of_bijective fun c ↦ ((ULift.map_bijective.2 (hk.comp_bijective _
    c.isAdicComplete_prodRing)).comp (pointMap_algBaseChange_unit_bijective ..)).comp
    (homTiltIso.app _).toEquiv.bijective)) (.transfer (CoeffCompBij.periodAlg_of_almostCoeff
    (β := 𝟙 (ObjectProperty.lift _ _ isPerfectTorsionFree_tilt ⋙ ι _)) (α :=
    freeAbMap (.mk fun _ ↦ by exact ↾(⟨⟨·.1⟩⟩))) (hasFlatBaseChange_reprFunctor _) h.2 (fun _ _ ↦
    hasFlatBaseChange_of_iso_reprBy homTiltIso.symm ..) (·.2) isPerfectTorsionFree_tilt
    ((isAcyclicAt_almostCoeff h.pFlat_smul_eq_zero _).transfer bijective_id)) bijective_id)
open AddMonoidAlgebra Algebra TensorProduct AlgebraMonoidAlgebra in
lemma hasCrysComparison_of_etale G [AddCommMonoid.{0} G] [Module ℚ≥0 G] (B : CommAlg _) [Algebra
  OC[G] B] [IsScalarTower OC OC[G] B] [Etale OC[G] B] : HasCrysComparison (reprBy B) := by
  let W := Ainf[G]
  have ⟨T, _, ⟨E⟩⟩ := exists_etale_lift W OC[G] B (map_surjective _ theta_surjective)
  algebraize [T.3.2.comp (algebraMap Ainf _)]
  let a S [CommRing S] [Algebra Ainf S] := IsPushout.cancelBaseChangeAlg Ainf S W S[G] T
  let b := CommAlgCat.of OFlat (OFlat[G] ⊗[W] T)
  have := perfectRing_of_etale _ b (k := perfectRing_monoidAlgebra G) p_eq_zero_of_algebra_oFlat
  have ⟨c, w, z, _⟩ := witt_reduction_spec OFlat b
  let := (liftNCRingHom (WittVector.map b.3.2) ((teichmuller p).comp
    (includeLeftRingHom.1.comp (of ..))) fun _ _ ↦ .all ..).toAlgebra
  let e := quotientKerAlgEquivOfSurjective (f := ⟨constantCoeff, (constantCoeff.comp (algebraMap W
    _)).congr_fun (by ext <;> simp [*, b, W, algebraMap_toAlgebra, map_one])⟩) c.1
  obtain ⟨κ, hκ⟩ := @FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete _ _ _ _ _ _ _ _ _ _
    (z ▸ w.2 :) (e.symm.toAlgHom.comp includeRight)
  exact ((Comparison.isClosedClass (.restrict ..) testToThickening).iff_of_isIso (freeAb.map
    (reprFunctor.mapIso (isoMk ((a _).symm.trans (E.restrictScalars _))).op ≪≫ isoOfAppBijective _
    (pointMap_algBaseChange_unit_bijective _)).1)).2 (hasCrysComparison_of_witt (T := .of _ T) ⟨b,
    ‹_›, (Module.Flat.trans _ OFlat[G] _).isTorsionFree.1 (.of_ne_zero pFlat_ne_zero)⟩
    (CommAlg.homOfRingHom κ.1 fun _ ↦ by erw [κ.2, liftNC_single, map_one, mul_one]; rfl)
    (.of_dvd_sub_of_pow_dvd _ (fun y ↦ (mk_surjective W T OFlat[G]
    (map_surjective _ (constantCoeff_surjective p)) (y.1 0)).imp fun t u ↦ mem_span_singleton.1 (z ▸
    (sub_mem_ker_iff _).2 ((e.eq_symm_apply.1 congr($hκ t)).trans u).symm)) fun _ _ ↦ pow_dvd_of_map
    (by simp) (by simpa [mem_nonZeroDivisors_iff_left] using! @w.1.right_eq_zero_of_smul) fun t u ↦
    ((((witt_reduction_spec OFlat _).1.lTensor (Algebra.linearMap Ainf OFlat)).2 (t ⊗ₜ 1)).1
    ((TensorProduct.comm
    ..).injective ((a _).symm.injective (by simpa [a] using!
    (e.eq_symm_apply.1 congr($hκ t)).symm.trans (z.ge (mem_span_singleton.2 u)))))).elim fun y h ↦
    ⟨_, by simpa [← nsmul_eq_mul] using congr(TensorProduct.rid _ _ $h).symm⟩))
end
end FoldSeg0
section FoldSeg1
open Finset _root_.Nat AddConstMapClass AddMonoidAlgebra CategoryTheory CommAlgCat Envelope Equiv
  Filter Fin Function IsScalarTower Multiplicative NNRat PreTilt Submonoid MonoidalCategory
  ShortComplex
open scoped ModuleCat
def periodicSeq R [CommRing R]
    : Subalgebra R (ℕ → R) := by refine' {carrier := {f | ∀ᶠ n in atTop, Periodic f n !}, ..} <;>
  first | exact (·.mp <| ·.mono (by aesop)) | simp
variable {p : ℕ} [ThePrime p] {R} [CommRing R] {D} [CommRing D] [IsDomain D]
@[local simp] def periodicSeq.shift R [CommRing R] [Algebra OFlat R] :
  periodicSeq R →ₐ[OFlat] periodicSeq R := by
  refine' { toFun f := ⟨f.1 ∘ succ, f.2.mono (by grind [Periodic])⟩, .. } <;> aesop
instance {n} : NeZero n ! := ⟨by grind⟩
lemma periodicSeq.mem_of_periodic {f} n (k : 0 < n) (h : Periodic f n) :
  f ∈ periodicSeq R := .mono (by aesop) fun _ l ↦ Nat.div_mul_cancel (dvd_factorial k l) ▸ h.nsmul _
lemma periodicSeq.koszulExact_shift {R} [CommRing R] [Algebra OFlat R] {M} :
    KoszulExact ((moduleCoeff (tensorCoeff M)).map (ofHom (toAlgHom _ R _))) ((moduleCoeff
  (tensorCoeff M)).map (ofHom (shift R))) := have s := (Splitting.map (S :=
    .mk (↟(toAlgHom _ R _).toLinearMap) (↟(shift R).toLinearMap - 𝟙 _)) (by refine' ⟨↟⟨⟨(·.1 0), by
    simp⟩, by simp⟩, ↟{ toFun f := ⟨(range · |>.sum f.1), f.2.exists.elim fun n h ↦ mem_of_periodic
    _ pos' (by simpa [p_eq_zero_of_algebra_oFlat] using (map_add_nsmul (AddConstMap.mk (a := n !)
    (range · |>.sum f.1) fun k ↦ by simp_rw [add_comm k, sum_range_add, add_comm, h _]; rfl) ·
    p))⟩, .. }, _, _, _⟩ <;> intros <;> ext <;> simp [sum_range_succ, sum_range_sub, smul_sum,
    ← sum_sub_distrib]) (tensorRight M ⋙ forget₂ .. ⋙ AddCommGrpCat.uliftFunctor)).shortExact
  by simp [ShortComplex.map] at s
     use s.ab_injective_f, ((ab_exact_iff _).1 s.1 · ∘ sub_eq_zero.2), s.ab_surjective_g
lemma periodicSeq.exists_eq_eval {ι} [Finite ι] (ψ : _ →+* D) (w : ι → periodicSeq R) : ∃ k, ∀ i,
  ψ (w i) = ψ (algebraMap _ _ ((w i).1 k)) := (eventually_all.2 (w · |>.2)).exists.elim fun N h ↦ by
  by_contra! E; choose f E using E
  apply (range N !).prod_ne_zero_iff.2 fun k _ ↦ sub_ne_zero.2 (E k)
  simp [← map_sub, ← map_prod]; convert ψ.map_zero; ext x
  simp [prod_eq_zero (mem_range.2 (x.mod_lt pos')), (h _).map_mod_nat]
lemma periodicSeq.existsUnique_hom {E} [CommRing E] [IsDomain E] f (s : D → E) (ζ r u :
  Multiplicative ℚ≥0 →* E) (x : _ → _) (hx : ∀ n k, s (f ((x n).1 k)) = (ζ ^ k * r) n) (h :
  r (ofAdd 1) ≠ 0) (z : ∀ a, IsPrimitiveRoot (ζ a) a.toAdd.den) (hu : u (ofAdd 1) = r
  (ofAdd 1)) : ∃! ϕ : periodicSeq R →+* D, ϕ.comp (algebraMap ..) = f ∧ ∀ n, s (ϕ (x n)) = u n := by
  have e n : ofAdd 1 = ofAdd (n ! : ℚ≥0)⁻¹ ^ n ! := by bound
  replace z {n} := by simpa [den_inv_of_ne_zero] using z (ofAdd (n !)⁻¹)
  choose a b ha using fun n : ℕ ↦ by
    simpa [e n, ← Polynomial.mem_nthRoots pos', z.nthRoots_eq rfl] using hu
  choose N m using fun y : periodicSeq R ↦ y.2.exists.imp fun n i k H ↦ z.pow_inj (b n)
    (mod_lt k pos') (pow_eq_pow_mod k z.1 ▸ mul_right_cancel₀ (by grind [ne_zero_pow])
    ((ha _).trans (.symm H))) ▸ i.map_mod_nat k
  have d {n} : ∀ᶠ m in _, ofAdd n ∈ (ζ ^ a m * r).eqLocusM u := .mono (mem_atTop n.den) fun m h ↦
    powers_le.2 (ha m) ⟨n.num * (m ! / n.den), by simp [← ofAdd_nsmul, field, dvd_factorial, h]⟩
  have hL {x} : _ =ᶠ[_] _ := d.mono (m x <| a ·)
  refine' ⟨f.comp { toFun x := x.1 (a (N x)), .. }, ⟨rfl, fun _ ↦ eventually_const.1
    ((hL.fun_comp (s ∘ f)).trans (d.mono (by solve_by_elim [Eq.trans])))⟩, by
    rintro ψ ⟨rfl, H⟩; ext y
    exact (exists_eq_eval ψ ![y, _]).elim fun k l ↦ m y k ((hx ..).symm.trans (l 1 ▸ H _)) ▸ l 0⟩
  <;> intros <;> first | rfl | exact eventually_const.1 (hL.trans (hL.comp₂ _ hL).symm)
lemma PadicTest.isLine_rootSystems {M} (ac : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))) c
  (v : (algFunctor ⋙ underlyingSet) c) (h : IsUnit v.1) :
  FP (freeAb (TimesBNat.incl _ ⋙ rootSystemsAt _ v)) ∧
  IsLine (tilt ⋙ moduleCoeff (tensorCoeff M)) (Y := rootSystemsAt _ v) (fibreProd.snd ..) := by
  choose σ H using untilt_surjective_of_isAIC (R := c.ProdRing) (p := p)
  have ⟨s, e⟩ := exists_compatible_roots (S := c.ProdRing) h.unit
  let r := (Units.coeHom _).comp (s.comp coeHom.toAddMonoidHom).toMultiplicativeLeft
  cases (congr(⟨$e.1⟩) : ⟨r (ofAdd 1)⟩ = v)
  have : PerfectRing (periodicSeq _) p := ⟨((piCongrRight fun _ ↦ (powMulEquiv c.TiltRing
    p).1).subtypeEquiv (by simp [periodicSeq, powMulEquiv])).bijective⟩
  let ζ := c.structureMap.1.comp (untilt.comp epsNonneg)
  let x n : periodicSeq _ := ⟨fun k ↦ σ ((ζ ^ k * r) n), periodicSeq.mem_of_periodic _ n.den_pos
    (by simp [pow_add, show ζ n ^
    n.den = 1 by simpa using! congr(c.structureMap $((isPrimitiveRoot_untilt_epsPow ..).1))])⟩
  let F {D} (ϕ : periodicSeq c.TiltRing →ₐ[_] TiltRing D) := tilt.preimage (X :=
    c) (ofHom (ϕ.comp (toAlgHom ..)))
  have U {D ϕ y} : tiltMap (@F D ϕ).1 y = ϕ (algebraMap _ _ y) :=
    ConcreteCategory.congr_hom (tilt.map_preimage _) y
  have Q {D ϕ w} t w' (h : ∀ k, (w.1 k).untilt = t * (w'.1 k).untilt := by simp [x, H, ↓map_mul, ζ,
      _root_.pow_succ', mul_assoc]) : (ϕ w).untilt = (@F D ϕ).1 t * (ϕ w').untilt :=
    funext fun j ↦ (periodicSeq.exists_eq_eval ((tiltMap (Pi.evalRingHom _ j)).comp ϕ.1) ![w,
    w']).elim fun k l ↦ by simpa [← U, h] using congr(untilt $(l 0) = (F ϕ).1 t j * untilt $(l 1))
  let t {D} (ϕ : _ →ₐ[_] TiltRing D) : _ →* _ := ⟨⟨untilt ∘ ϕ ∘ x, by simpa using Q 1 1⟩,
    fun a b ↦ by simpa using Q 1 (_ * _)⟩
  exact let e := by exact (NatIso.ofComponents (fun D ↦ toIso (.ofBijective (fun ϕ ↦ ⟨(⟨t ϕ.1.1⟩,
      ⟨F ϕ.1.1⟩), congr(⟨$(by simpa using! Q _ 1)⟩)⟩) (.of_existsUnique _ fun ⟨⟨⟨u⟩, ⟨f⟩⟩, hu⟩ ↦ by
      choose ϕ a W using fun j ↦ let g :=
          (Pi.evalRingHom _ j).comp f.1; periodicSeq.existsUnique_hom
          (tiltMap g) untilt (.comp g ζ) (g.1.comp r) ((Pi.evalMonoidHom _ j).comp u) x (by simp [x,
          H]) (h.map g).ne_zero (fun _ ↦ (isPrimitiveRoot_untilt_epsPow ..).map_of_injective
          (.of_ker (g.comp c.structureMap) fun _ e ↦ by simpa [IsCell.p_ne_zero] using fun h ↦
          (e ▸ map_dvd _ (OC.exists_dvd_pow (s := p) Fact.out h).choose_spec :))) congr($hu.1 j)
      let k {y} :=
        D.tiltPiEquiv.symm_apply_eq.2 (funext (congr($(a · |>.1) y).trans (tiltMap_comp ..)))
      use ⟨ofHom ⟨D.tiltPiEquiv.symm.toRingHom.comp (.pi ϕ), (k.trans <| (tilt.map f).1.2 ·)⟩⟩,
        congr(⟨(⟨$(by ext n j; exact (untilt_tiltMap ..).symm.trans (congrFun (D.tiltPiEquiv.1.4
        (ϕ · _)) j ▸ (a j).2 n))⟩, ⟨$(tilt.map_injective (by ext; exact k ▸ U))⟩), _⟩)
      rintro ⟨⟨ψ⟩⟩ ⟨⟩; congr; ext
      exact D.tiltPiEquiv.eq_symm_apply.2 (funext (congr($(W · ((tiltMap _).comp ψ.1) ⟨RingHom.ext
        fun y ↦ .symm ((tiltMap_comp ..).trans (U ▸ rfl)), fun _ ↦ untilt_tiltMap ..⟩) _))))))
      fun f ↦ by ext; exact congr(⟨(⟨$(MonoidHom.ext fun _ ↦ untilt_tiltMap f.1 _)⟩, ⟨$(.symm
      (tilt.preimage_map f ▸ (tilt.preimage_comp _ (tilt.map f)).symm :))⟩), _⟩))
    ⟨hasFlatBaseChange_of_iso_reprBy (homTiltIso.symm ≪≫ e), .of_acyclic e (ac _) _ _ (by
    intros; apply tilt.map_preimage) ⟨by ext; exact congr(⟨(⟨$(MonoidHom.ext fun n ↦
      Q (ζ n) _ (w := periodicSeq.shift _ _).trans congr($((F _).2 _) * _))⟩, _),
      _⟩)⟩ periodicSeq.koszulExact_shift⟩
attribute [local simp] Algebra.smul_def floor_add_natCast floor_le lt_floor_add_one mu
  ocToAmaxModPd_untilt
lemma rootSystemsAreLines_crysTest {p} [ThePrime p] [h : CrysPeriodAlgebra] :
  RootSystemsAreLines crysPeriodCoeff (pdReduction ocToAmaxModPd) := fun A ⟨y⟩ ↦ y.ind' fun t hy ↦
  let z : A[ℚ≥0] := single 0 t - single 1 1
  have o := (exists_preEnvelope_basis A (I := Set.Ico 0 1) z (.reindex (basis ..) ⟨fun c ↦
    (⟨c - ⌊c⌋₊, by simp [tsub_lt_iff_left]⟩, ⌊c⌋₊), fun (a, n) ↦ a + n, by aesop_cat, by aesop_cat⟩)
    (single · 1) (by simp) rfl).choose_spec.choose_spec
  let E := Envelope _ {z}
  let v := (algebraMap _ E).1.comp (AddMonoidAlgebra.of A _)
  have hw := (Ideal.Quotient.eq.2 (by simpa [z] using! algebraMap_mem_pdIdeal _ {z} rfl)).symm
  let x : (TimesBNat.incl _ ⋙ rootSystemsAt (pdReduction _) ⟨⟦t⟧⟩) E :=
    ⟨(⟨(pdQuotientMk _).1.comp v⟩, ⟨⟨ofHom (Algebra.algHom ..)⟩⟩), congr(⟨$hw⟩)⟩
  have hx B := Bijective.of_existsUnique (pointMap x B) fun ⟨(⟨w⟩, ⟨f⟩), hw⟩ ↦ by
    obtain ⟨χ, rfl⟩ := B.2.monoidHom_lift_bijective.2 w
    obtain ⟨g, c, H⟩ := existsUnique_lift _ {z} (liftNCAlgHom f.1.hom χ fun _ _ ↦ .all ..)
      (by simpa [z] using! SModEq.sub_mem.1 congr($hw.1).symm)
    obtain ⟨rfl, rfl⟩ : .comp g.1.1 v = χ ∧ x.1.2.1 ≫ g = f := by
      constructor <;> ext <;> exact congr($c _).trans (by simp)
    use ⟨g⟩, rfl, fun ⟨g⟩ e ↦ H g (c ▸ algHom_ext' (B.2.monoidHom_lift_bijective.1 congr($e.1.1.1))
      congr($e.1.2.1.1.1)) ▸ rfl
  ((hx E).2 _).elim fun ⟨γ⟩ hγ ↦ .of_acyclic (ψ := 𝟭 _) (F' := crysPeriodCoeff) (isoOfAppBijective _
    hx) (IsCohomEquiv.of_isIso _).bij x.1.2.1 γ (by tauto) ⟨uliftCoyonedaEquiv.injective hγ⟩ (by
  let e := (algebraMap _ Amax).1.comp ((WittVector.teichmuller p).comp epsNonneg)
  have hv :=
    @E.2.monoidHom_lift_bijective.1 (.comp γ.1.1 v) ((algebraMap _ E).1.comp e * v) (MonoidHom.ext
    (congr($hγ.1.1.1 ·).trans (congrArg (pdQuotientMap _ · * _) (ocToAmaxModPd_untilt _))))
  refine koszulExact_pd_line A E isBijOnCompletion_completion (congr(algebraMap _
    _ $(o.1 · ·)).trans (map_mul ..)) (by simpa [z] using! congr(algebraMap _ _ $(o.2 ·)))
    (E.2.isLocalHom_pdQuotientMk.1 _ (hw ▸ hy.map (pdQuotientMap _))) rfl h.3
    h.4 ⟨γ.1.1, (congr($hγ.1.2.1.1.1 ·))⟩ (by simpa [← epsPow_one] using! congr($hv _))
    fun a ha ↦ ⟨_ - 1, by simpa using! congr($hv _), ?_⟩
  let x := e (.ofAdd a.1.den⁻¹)
  have t := Nat.lt_of_le_of_ne a.1.den_pos (ha <| by simpa [← ·, NNRat.lt_def, num] using a.2.2)
  have m := by simpa using isPrimitiveRoot_untilt_epsPow (.ofAdd a.1.den⁻¹)
  have := mul_dvd_mul (h.2.2.trans (map_dvd _ (theta_eq_zero_iff_xi_dvd.1 ((theta.map_geom_sum
    ..).trans (theta_teichmuller _ ▸ m.geom_sum_eq_zero t))))) ((h.isLocalHom_pdQuotientMk.1 (∑ i ∈
    _, x ^ i) (by simpa using!
    (m.geom_sum_isUnit t a.1.coprime_num_den).map ocToAmaxModPd)).mul_left_dvd.2 (refl (x - 1)))
  simp [geom_sum_mul, e, x] at this
  simpa [← map_pow, ← ofAdd_nsmul, ← cast_def, ← division_def])
end FoldSeg1
section FoldSeg2
open Algebra.TensorProduct ULift TimesBNat CategoryTheory Comparison CommRingCat Envelope Fin
  IsDiscreteValuationRing LinearEquiv MvPolynomial RingHom Submodule TensorProduct
  CategoryTheory.Functor ObjectProperty Ideal.Quotient Module.Flat
variable {p : ℕ} [ThePrime p] {C C'} [Category C] [Category C'] {F F'} {c :
  @Comparison C C' _ _ F F'} {ψ : C ⥤ CommAlg OC} {ψ'} {η : ψ' ⟶ c.φ ⋙ ψ} {S : Type}
lemma Comparison.IsBijective.isBijectiveOn_of_rootSystems {n U T} (l : RootSystemsAreLines F ψ)
  (l' : RootSystemsAreLines F' ψ') (k : c.IsBijectiveOn η (reprBy T)) (t : Fin n → (U ⟶
  underlyingSet)) x (r : _ → _ →* T) (u : ∀ i A y, IsUnit (t i A y).1) (e : ∀ i, ⟨r i (.ofAdd 1)⟩ =
  t i T x) (H : ∀ (A : CommAlg _) y (s : _ → Multiplicative ℚ≥0 →* A), (∀ i, ⟨s i (.ofAdd 1)⟩ =
  t i A y) → ∃! f, pointMap x A f = y ∧ ∀ i, .comp f.1.hom (r i) = s i) : c.IsBijectiveOn η U := by
  induction' n with _ ih generalizing U
  exact (c.isClosedClass η).of_bijective (pointMap x) (by simp_all [AllBijective,
    Function.bijective_iff_existsUnique]) k
  let a := fibreProd.snd rootSystems.atOne (whiskerLeft _ (t 0))
  have L {C} [Category C] {F : AbFunctor C} {ψ} (h : RootSystemsAreLines F ψ) :
    IsLine F ((ψ.prod _).whiskerLeft a) :=
    isBijective_of_fibres (ψ.whiskerLeft _) (isPullback_fibreProd.map (restrictAlong _)) (by tauto)
  refine (L l').trans_iff.1 ((L l).trans ((forall_congr' ((isClosedClass ⟨.prod _ (𝟭 _),
    _⟩ (η.prod (𝟙 _))).2 _ (shortExact_induced (fibreProd ..)).2)).1 (·)
    (((ih ((incl _).whiskerLeft a ≫ t ·.succ) ⟨(_, _), e 0⟩ _ (by bound) (tail e) fun A ⟨(⟨a⟩, y),
    k⟩ s l ↦ ?_).trans isBijective_induced) · |> (funext pull_trans).symm.subst |>
    ((isBijective_induced (X := ψ ⋙ _ ⋙ fibreProd ..) _).of_comp_iff _).1)) rfl)
  convert H A y (cons a s) (cases k l) using 2
  erw [Subtype.ext_iff, Prod.mk_inj, up_inj, forall_fin_succ]; tauto
lemma hasCrysComparison_chart [h : CrysPeriodAlgebra] {R} [CommRing R] [Algebra R OC] {d} {B :
  CommAlg R} (t : Fin d → B) (ht : Etale (polyEval t)) (hu : ∀ i, IsUnit (t i)) :
  HasCrysComparison (restrictAlg R _ ⋙ reprBy B) := by
  let G := Fin d → ℚ≥0
  let g := aeval (R := R) (AddMonoidAlgebra.of OC G <| Pi.single · 1)
  algebraize [g.1, polyEval t]
  have w x : g x ⊗ₜ 1 = 1 ⊗ₜ polyEval t x := tmul_one_eq_one_tmul x
  let e (A : CommAlg OC) := (AddMonoidAlgebra.lift OC A G).symm.trans (Pi.monoidHomMulEquiv (fun _ ↦
    Multiplicative _) _).1
  exact .isBijectiveOn_of_rootSystems rootSystemsAreLines_crysTest
    (·.isLine_rootSystems (isAcyclicAt_almostCoeff h.pFlat_smul_eq_zero) · · |>.rec fun a b ↦
    ((coeffCompBij_id_iff_restrict (.refl _)).1 (.periodAlg_of_almostCoeff
    (hasFlatBaseChange_reprFunctor _) h.2 (fun G ↦ (forall_congr' (Ten.devissage.isClosedClass.2 _
    (shortExact_induced _).2)).1 (·) ((isBijective_induced.baseChangeMap_bijective_iff
    (β := 𝟙 (_ ⋙ _ ⋙ G)) a).2 ((coeffCompBij_id_iff_restrict (.refl _)).2 isBijective_induced)))
    PadicTest.isPerfectTorsionFree_tilt (·.1.isPerfectTorsionFree_tilt)
    ((coeffCompBij_id_iff_restrict (.refl _)).2 b)) :)) (hasCrysComparison_of_etale G
    (.of _ (_ ⊗[MvPolynomial (Fin d) R] B))) (fun i ↦ {app _ := ↾(⟨·.1.1 (t i)⟩)})
    ⟨CommAlg.homOfRingHom includeRight.1 (by simpa using! C · |> w |>.symm)⟩ (e _ includeLeft)
    (fun i _ _ ↦ (hu i).map _) (up_inj.2 <| by simpa [g] using! w <| X ·) fun A ⟨y⟩ ↦ (e
    A).forall_congr_right.1 fun F k ↦ ((isPushout_tensorProduct ..).exists_desc (ofHom F.1) (ofHom
    y.1.1) (by ext <;> simp [g, algebraMap_toAlgebra]; exacts [(F.2 _).trans (y.1.2 _).symm,
                 up_inj.1 (k _)])).rec fun x ⟨a, c⟩ ↦ ⟨⟨CommAlg.homOfRingHom x.1 (F.2 · ▸ congr($a
    _))⟩, ⟨congr(⟨CommAlg.homOfRingHom $c.1 _⟩), fun _ ↦ by ext; exact congr($a _)⟩, by
    rintro ⟨z⟩ ⟨⟨⟩, n⟩
    cases (e A).injective (a₁ := z.1.comp includeLeft) (funext n)
    exact (isPushout_tensorProduct ..).hom_ext a c ▸ rfl⟩
lemma FP.pdReduction_reprBy [CommRing S] G :
  FP (freeAb.obj (pdReduction (.id (S ⧸ _)) ⋙ reprBy G)) := let L : CrysTest S ⥤ _ :=
    (.mk (fun B ↦ {x : ULift (G ⟶ _) × (G → B) // ∀ g, (x.2 g : _ ⧸ pdIdeal B) = x.1.1 g}) fun f ↦
    ↾fun x ↦ ⟨(⟨_ ≫ (pdReduction (.id _)).2 f⟩, _), (congr((pdReduction _).2 f $(x.2 ·)))⟩)
  isClosedClass.of_bijective (Subfunctor.range (.mk fun _ ↦ ↾(·.1.1) : L ⟶ _)).ι (fun B ↦
    (Equiv.subtypeUnivEquiv
    fun y ↦ ⟨⟨(y, _), (Quot.out_eq <| y.1.1 ·)⟩, rfl⟩).bijective) fun _ _ _ ↦ fun _ ↦ by
    refine Ten.devissage.bijective_range_of_cech _ fun m ↦ have hy :=
        ((eval₂Hom (G.3.2.comp (pdQuotientMk S)) Prod.snd).liftOfSurjective_comp_apply
        (⟨.X ⟨0, ·⟩, by simp⟩) ⟨(pdQuotientMk _).comp _, fun _ ↦
        eq_zero_iff_mem.2 ∘ algebraMap_mem_pdIdeal S _⟩); Ten.devissage.isClosedClass.of_bijective
        (pointMap ⟨fun i ↦ ⟨(⟨CommAlg.homOfRingHom _ (Quot.ind (by simpa using! hy <| C ·))⟩, _),
        (.X ⟨i, ·⟩ |> hy |>.symm.trans (congrArg _ (by simp)))⟩, by tauto⟩) (fun B ↦
        .of_existsUnique _ fun e ↦ (Equiv.ulift.existsUnique_congr fun g ↦ ?_).2 (existsUnique_lift
        _ _ (aeval fun (i, g) ↦ (e.1 i).1.2 g) fun f h ↦ ?_)) (Ten.freeAb_reprBy _)
    have h : Function.Injective (·.1.2 : L B → _) := fun a b h ↦ by ext <;> simp_all [← a.2, b.2]
    erw [Subtype.ext_iff]; simp [← h.eq_iff, funext_iff, MvPolynomial.algHom_ext_iff]; rfl
    erw [← eq_zero_iff_mem, ← map_zero (e.1 0).1.1.1.1, ← h]; apply f.induction_on <;>
      simp_all [(e.1 _).2, show ∀ i, (e.1 i).1.1 = _ from (e.2 · 0)] <;> tauto
variable {R} [CommRing S] [CommRing R] {r : R →+* _ ⧸ pdIdeal S} {X : CommAlg R ⥤ Type 1} (V :
  Subfunctor X) [h : CrysPeriodAlgebra] [Algebra R OC] [Algebra S Amax] (i :
  pdReduction ocToAmaxModPd ⋙ restrictAlg R OC ⟶ CrysTest.restrictScalars S ⋙ pdReduction r)
noncomputable abbrev crysComparison :=
  Comparison.of (F := moduleCoeff (asModules (ι _))) (crysThickening ⋙ CrysTest.restrictScalars S :)
  (tensorWith.mk Bcris (1 : Bcris) (asModules (crysThickening ⋙ ι _)))
noncomputable def toCrysPoints : PadicTest.algFunctor ⋙ restrictAlg R _ ⋙ V.toFunctor ⟶
  (crysThickening ⋙ CrysTest.restrictScalars _) ⋙ pdReduction r ⋙ V.toFunctor := whiskerRight
  (whiskerRight testToThickening (restrictAlg ..) ≫ crysThickening.whiskerLeft i) V.toFunctor
attribute [-instance] addCommGroupH
lemma span_range_crysComparison_pull_eq_top (_ : IsIso i) [IsDomain S] [IsDiscreteValuationRing S]
  (hS : IsCompleteTorsionFree S) (hV : IsCharting V) (hp : Irreducible (p : S)) (F : ∀ n,
  Module.Finite Bcris (H (freeAb.obj (PadicTest.algFunctor ⋙ restrictAlg R _ ⋙ V.toFunctor))
  (moduleCoeff (asModules (crysThickening ⋙ ι _) ⋙ tensorWith Bcris Bcris)) n)) n :
  span Bcris (.range (crysComparison.pull (freeAbMap (toCrysPoints V i)) n)) = ⊤ := by
  obtain ⟨_, ⟨l⟩⟩ :=
    isTorsionFree_of_dvd_pow h.isSMulRegular_natCast (associated_pow_irreducible · hp |>.imp fun _ ↦
    (·.dvd)), @Amax.nonempty_adicBasis _ _ S _ _ _ rfl hp.prime.isMaximal_span_singleton hS.2
  algebraize [r, (algebraMap _ Bcris).comp (algebraMap S Amax)]
  let N := freeAb (pdReduction r ⋙ V.toFunctor)
  let L : CrysTest S ⥤ _ :=
    ObjectProperty.lift (IsCompleteTorsionFree ·.1) (ι _ ⋙ algBaseChange _ ⋙ algCompletion Amax _)
    (isCompleteTorsionFree_completion fun _ _ e ↦ ·.2.isSMulRegular_natCast.lTensor _ (mod_cast e))
  let o : _ ⟶ L ⋙ ι _ := (ι _ ⋙ algBaseChange _).whiskerLeft (algCompletion.of ..)
  let E A B : (L A ⟶ B) ≃ (A ⟶ CrysTest.restrictScalars _ B) := .trans (.mk _ .mk)
    (.trans (.ofBijective _ (isBijOnCompletion_completion.comp_bijective (o.1 A) B.2.2))
    ((algBaseChangeAdj.homEquiv ..).trans (.mk (⟨·⟩) (·.1))))
  let a : L ⊣ _ := .mkOfHomEquiv ⟨E, fun f ↦ (E ..).surjective.forall.2 fun g ↦ by
    simp [Equiv.symm_apply_eq]; ext; exact congrArg _ (o.naturality_apply f (1 ⊗ₜ _)), by tauto⟩
  have hN : FP N := hV.2 _ (FP.isClosedClass.comap (restrictAlong _)) fun b _ ↦
    ((FP.isClosedClass.comap (restrictAlong (@pdReduction p _ S ..))).of_bijective _
    (pointMap_algBaseChange_unit_bijective b.R) (.pdReduction_reprBy _) :)
  have b : CoeffCompBij (Ψ := (L ⋙ ι _) ⋙ asModules (𝟭 _))
    (by exact crysThickening.whiskerLeft (whiskerRight a.2 (asModules (ι
    _)))) (freeAbMap (toCrysPoints V i)) _ := (isBijective_of_adj (F := crysPeriodCoeff) a).trans
    (((Comparison.restrict ..).isBijective_congr (show 𝟙 _ ≫ toCrysPoints V i = whiskerRight
    testToThickening _ ≫ crysThickening.whiskerLeft (whiskerRight i _) by simp [toCrysPoints]; rfl)
    (.of_isIso _) (.of_isIso _)).2 (by exact hV.2 _ ((isClosedClass (.restrict ..)
    testToThickening).comap (restrictAlong _)) (hasCrysComparison_chart _ ·.etale)))
  let θ n := ofBijective _ (hN ..) ≪≫ₗ ofBijective (pullₗ ..) (b n)
  let t n := ofBijective _ (hN _ Amax Amax (asModules (ι _)) n)
  let u := pullₗ (φ := 𝟭 _) (Φ := asModules (ι _) ⋙ tensorWith ..) (N :=
    N) (whiskerRight o (asModules (𝟭 _))) (𝟙 N)
  refine (orderIsoMapComap ((t n ≪≫ₗ ofBijective (u n)
    (hN.isBijective_of_isReductionMod hS h.isCompleteTorsionFree (·.2) hp _
    (fun n v ↦ (exists_set_linearIndependent ..).elim fun s ⟨e, c⟩ ↦ have := (F n).equiv (θ n).symm
    e.ge.trans_lt (linearIndependent_one_tmul (S := Bcris) (linearIndependent_iff'.2 fun w a e d k ↦
    l.eq_zero_of_coord fun i ↦ linearIndependent_iff'.1 c w _ (((IsDerivedComplete.cohomology
      (·.2.isDerivedComplete) ..).exists_eq_of_approx hS.isDerivedComplete 0 (TensorProduct.lift
    (.lsmul .. ∘ₗ l.coord i) <| (t n).symm <| (u n).ker.subtype ·) (⟨0, v · |>.imp fun y e ↦ by
    simp [← e, Nat.cast_smul_eq_nsmul]⟩) ⟨∑ d ∈ w, a d • t n (1 ⊗ₜ d), by simpa⟩).elim fun _ e ↦ by
    simpa [smul_tmul'] using e.symm) d k)).lt_aleph0_of_finite) (L · |>.2) (fun _ _ _ _ ↦
    .comp_algebraMap)
    n)).baseChange .. ≪≫ₗ θ n)).symm.injective ((ker_mkQ _).symm.trans (LinearMap.ker_eq_top.2 ?_))
  ext z; exact (Quotient.mk_eq_zero _).2 (subset_span ⟨z, .symm (by
    simp [u, t, θ, ← H.push_comp, pullₗ, pull_id_eq_push]; exact (crysComparison.pull_push _ _ _ (by
    ext; exact congr(⟨_ ⊗ₜ $(a.4 _) _⟩)) ..).trans (Abelian.Ext.comp_mk₀_id _))⟩)
end FoldSeg2
section FoldSeg3
open CategoryTheory AlgebraicGeometry Fintype Set Fint
lemma ellAdicCohom.transfer {R} [Algebra R.1 Ω] {W Y c Δ a} [IsProper W.hom] [IsProper Y.hom]
    (h : @IsGaloisCovering R Y W c Δ a) ℓ [ThePrime ℓ] n : let V := ellAdicCohom R Ω n
  (⇑(V.map c.op)).Injective ∧
    ∀ y, (∀ g, V.map (a g).asHom.op y = y) → y ∈ range (V.map c.op) := by
  obtain ⟨_, m, l, ν, e, _, _, k⟩ :=
    exists_transfer_map (h.1 · ▸ ((geomPoints _ Ω ⋙ onTests).4 ..).symm)
  dsimp [ellAdicCohom] at *
  let N := (card Δ : ℚ)⁻¹ • ellAdicPull n ν
  refine (k _ (((isProperOver_pointsToBase _).baseChange _).hasCohomDenseImage_of_surjective
    ((isProperOver_pointsToBase _).baseChange _) fun k _ _ y ↦ (exists_point_over _ (h.2.1 _)).rec
    fun x hx ↦ ⟨⟨(_, _), .trans congr(⟨Spec.preimage $(hx ▸ by simp)⟩) y.2⟩, congr(⟨(⟨$hx⟩, _),
    _⟩)⟩) (((isProperOver_pointsToBase _).baseChange _).isCohomDense_of_coincidences (fun g ↦
    cech.proj ((geomPoints ..).2 c) 1 g.1 ≫ (geomPoints ..).2 (a g.2).asHom) fun z B x H ↦
    (@h.3 _ _ (z.1
    0).1.2.1.1.toAlgebra.charZero_of_charZero _ _ congr($(z.2 ..).1.1.1)).exists.imp' .mulRight fun
    d h i ↦ (@H (0, _) (1, i) congr(⟨(⟨$(a.map_mul .. ▸ h =≫ _)⟩, $(z.2 ..).1.2),
    _⟩)).symm)).bijective_ellAdicPull.imp (.of_comp (f := N) ∘ (funext ?_).subst) fun C y _ ↦
    (C (N y)).imp fun _ _ ↦ (e ▸ ellAdicPull.comp
    ..).symm.trans ?_ <;> simp [N, ellAdicPull.comp, ← Nat.cast_smul_eq_nsmul ℚ, *]
open Ideal CommRingCat Finset Quotient Spec ULift Fact Pi
lemma exists_cancels_frobPow_locally {p} [ThePrime p] {R} [CommRing R] [Algebra R OC] {W Y : Over
  (Spec ⟨R⟩)} {I} [Fintype I] n a (u : I → (W ⟶ Y)) [IsNoetherianRing R] [IsProper Y.hom] [IsProper
  W.hom] (𝔴 : Ideal R) (hp : ↑p ∈ 𝔴) (h : CongruenceRelation n 𝔴 p a u) : ∃ M, ∀ z j,
  (p : OC) ∣ z ^ j → (∀ c ∈ 𝔴, z ^ (M + 1) ∣ algebraMap R _ c) →
  ∀ c (x : (testPoints.obj W).obj c) m, IsMaximal m → ∃ b ∉ m, ∀ D [CommRing D] e ρ, IsUnit (ρ b) →
  ρ (c.structureMap z) = 0 → Cancels n fun i ↦ map (ofHom ((@frobPow p D _ _ e
  (a i)).comp ρ)) ≫ x.1.left ≫ (u i).left := have ⟨T, t, _, ht⟩ := exists_finiteType_atlas W.hom
  have := isLocallyNoetherian_Spec.1 (LocallyOfFiniteType.isLocallyNoetherian (t ≫ W.hom))
  let α := 𝔴.map (Spec.preimage (t ≫ W.hom)).1
  have ⟨Z, hZ⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le (T ⧸ α) ⊥
  let q (l : Z) := l.1.1.under T
  ⟨_, fun z j hj hw c x m _ ↦ (ht _ c.isTest.2 x.1.1).elim fun β hb ↦ by
  choose τ hτ using fun i ↦ show ∃ l, ∀ r ∈ q l, c.structureMap z i ∣ β r i by
    let σ := (evalRingHom _ i).comp c.structureMap
    by_contra! r; choose r h₁ h₂ using r
    exact Nat.lt_irrefl _
      ((pow_dvd_pow_iff (by simpa [·, IsCell.p_ne_zero] using map_dvd σ (hw _ hp))
      (mt (isUnit_of_dvd_unit (by simpa using map_dvd σ hj) ∘ .pow _) out)).1 ((mem_span_singleton.1
      (map_le_of_le_comap (K := (span {_}).comap ((evalRingHom ..).comp β.1)) (fun r hr ↦
      mem_span_singleton.2 ((map_pow σ .. ▸ map_dvd σ (hw r hr)).trans congr($(map_injective (a₁ :=
      _ ≫ _) (.trans (by simp) ((hb =≫ _).trans x.1.w))) r i).symm.dvd)) (eq_zero_iff_mem.1 (by
      with_unfolding_all exact (map_prod ..).trans ((Z.map_univ _ ▸ hZ) (prod_mem_prod
        fun _ _ ↦ h₁ _)))))).trans (by simpa using! prod_dvd_prod_of_dvd _ _ fun _ _ ↦
      (ValuationRing.dvd_total ..).resolve_left (h₂ _))))
  refine by_contra fun N ↦ m.one_notMem ((funext (by simp) : ∑ t, ((if τ · = t then 1 else 0) :
    c.ProdRing) = 1) ▸ sum_mem fun l _ ↦ by_contra (N ⟨_, ·, fun _ _ e ρ hk hρ ↦ ?_⟩))
  have h𝔴 : α ≤ q l := le_comap_of_map_le (by simp)
  have E := by simpa using eq_zero_iff_mem.2 (h𝔴 (mem_map_of_mem _ hp))
  convert ((@h (q l).ResidueField _ (.of_eq_zero out (natCast_eq_zero_of_algebra
    E _)) (map (ofHom (algebraMap ..)) ≫ t) (by simpa using! le_comap_of_map_le h𝔴)).mono (v' := fun
    i ↦ map (ofHom ((frobPow E (a i)).comp (Ideal.Quotient.mk _))) ≫ t ≫ (u i).left) fun _ _ j ↦
    up_injective ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective ![ofHom
    (algebraMap _ (q l).ResidueField)] (by simp) fun _ ↦
    up_inj.2 ?_)).mono fun _ _ ↦ (map (ofHom (lift _ (ρ.comp β.hom) fun r hr ↦ zero_dvd_iff.1 (hρ ▸
    hk.dvd_mul_left.1 (map_mul ρ .. ▸ map_dvd _ (pi_dvd_iff.2 fun i ↦ by
      erw [Pi.mul_apply]
      split <;> simp [*, hτ i r]))))) ≫= ·) using 2
  all_goals (try convert j) <;> simp [← hb, ← map_comp_assoc, -map_comp] <;> congr 2 with <;> aesop⟩
end FoldSeg3
section FoldSeg4
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor
open CategoryTheory TensorProduct Functor AlgebraTensorModule AlgebraicGeometry TotalH Function
  PadicTest Abelian.Ext ConcreteCategory Comparison DirectSum ULift CommRingCat Over
variable {p} [ThePrime p] {M} {R : CommRingCat} (Ω) [Field.{0} Ω] [Algebra R Ω] [Algebra Ω ℂ_[p]]
lemma PadicTest.bijective_generic_points {Y : Over (Spec R)} [IsProper Y.hom] (c :
  PadicTest) {a b r w} : Bijective ((uliftYoneda.{1} Y).map (.op (X := .mk b) (Y := .mk a) ⟨Spec.map
  (ofHom (algebraMap c.ProdRing c.GenericRing)), r,
  w⟩)) := have := QuasiCompact.compactSpace_of_compactSpace Y.hom
  ⟨fun x y h ↦ down_injective
    (OverMorphism.ext (up.inj ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective
    _ (c.eq_zero_of_algebraMap_genericRing · <| · ()) fun _ ↦ congr(⟨$h.1.1⟩)))), fun z ↦ by
    have H i := (CommSq.mk ((ofHom_comp ..).symm.trans (congr(ofHom $(IsLocalization.Away.lift_comp
      (S := c.GenericRing) (g :=
      (algebraMap _ (FractionRing (c.Cell i))).comp (Pi.evalRingHom _ i)) (p : c.ProdRing)
      (by simp [-map_natCast, IsCell.p_ne_zero]))).symm.trans (ofHom_comp ..)))).op.map Scheme.Spec
    have l i := ((UniversallyClosed.eq_valuativeCriterion.le _ _ _ inferInstance).1 ⟨_, _, _, _,
      (H i).horiz_comp ⟨z.1.w.trans w.symm⟩⟩).1.some
    refine (pointsPi_surjective (of <| c.Cell ·) _ (l · |>.l)).elim fun x e ↦ ⟨⟨homMk x
      (pointsPi_injective _ _ (funext fun i ↦ by simpa [pointsPi, ← congrFun e] using (l i).3))⟩,
      down_injective (OverMorphism.ext
      (up.inj ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective _ (fun t h ↦
      ?_) fun i ↦ down_injective (((H i).w_assoc x).trans (congrFun e i ▸ (l i).2 :)))))⟩
    obtain ⟨r, u, rfl⟩ := exists_associated_localization t
    simp_all [← funext_iff, ← Pi.zero_def, (u.isUnit.map _).ne_zero]⟩
noncomputable def toGenericPoints [Algebra R OC] (he : ∀ r, algebraMap Ω ℂ_[p] (algebraMap R Ω r) =
  algebraMap R OC r) Y : testPoints Y ⟶ genericTestOver Ω ⋙ ObjectProperty.ι _ ⋙ algPointsOf Ω R
  Y := whiskerRight (H := _ ⋙ restrictAlg .. ⋙ restrictAlg R Ω) ⟨fun c ↦
  CommAlg.homOfRingHom _ (he · ▸ c.structMap_coe _ |>.symm), by
  intros; ext; symm; apply mapGeneric_algebraMap⟩ (algPointsOf R R Y)
set_option backward.isDefEq.respectTransparency false
lemma finite_and_primitive_comparison [IsAlgClosed Ω] (ac : IsAcyclicOnPerfect (moduleCoeff
  (tensorCoeff M))) Y [IsCharted Y Ω] [IsProper Y.hom] : let X := testIncl ⋙ geomPoints R Ω Y; FP
    (freeAb X) ∧ (∀ n, Finite (H (freeAb X) (locConstCoeff ⟨ZMod p⟩) n)) ∧
  ∀ [Algebra R OC] he, CoeffCompBij primitiveMap (freeAbMap (Y :=
    X) (toGenericPoints Ω he Y ≫ whiskerLeft _ (whiskerLeft _ (algToBaseChange Ω Y))))
    (tensorCoeff M) := have := InvertsPrime.mk (NeZero.nat_of_neZero (algebraMap Ω ℂ_[p])).1.isUnit
  let := Module.restrictScalars (ZMod p) OFlat M
  let γ := isoWhiskerRight (NatIso.ofComponents (fun _ ↦ ((cancelBaseChange ..).symm ≪≫ₗ
    TensorProduct.comm ..).toModuleIso) fun _ ↦ ModuleCat.hom_ext tmul_ext :
    asModules (TestOver.toTest Ω ⋙ testIncl ⋙ locConstAlg) ⋙ tensorWith .. ≅ (_ ⋙ oFlatLocConst) ⋙
    tensorCoeff M) (moduleCoeff (𝟭 _))
  let b := Module.Free.chooseBasis (ZMod p) M
  let c : Comparison (TestOver.toTest Ω ⋙ oFlatLocConst ⋙ moduleCoeff (tensorCoeff M)) _ :=
    ⟨genericTestOver .., whiskerRight primitiveMap (moduleCoeff _)⟩
  let θ i := mk₀ (whiskerLeft _ (tensorWith.mk _ (b i) _ ≫ γ.1) ≫ c.2)
  let D :=
    ComparedTheory.mk _ _ θ (hasLineFormula_tiltTheory _ ac) (hasLineFormula_locallyConstant Ω)
  have i {Y Y'} (h : FP (freeAb Y)) (u : Y' ≅ _ ⋙ Y) : IsLerayHirschBasis D.b (freeAb Y) ↔
    c.IsBijective (freeAbMap u.1) := by
    let E := ((equivFinsuppOfBasisLeft b).symm ≪≫ₗ directSumRight ..).toAddEquiv.trans
      (congrAddEquiv (.trans (.ofBijective _ (h ..)) <| .ofBijective _ <|
      H.push_bijective_of_isIso γ.isIso_hom ·))
    erw [← bijective_total_iff_isBijective, (IsCohomEquiv.of_isIso _).bijective_totalH.of_comp_iff',
      ← E.bijective.of_comp_iff]
    refine .of_eq congr(Bijective $((?_ : (lerayHirsch ..).toAddMonoidHom =
      (mapThenComp ..).comp E.toAddMonoidHom)))
    ext
    simp [E, ← lof_eq_of (ZMod p)]
    erw [DirectSum.map_of, ← of_comp_homClass, ← of_comp_homClass, lerayHirsch_single,
      TotalH.map_comp_assoc, TotalH.map_comp_assoc]
    simp_rw [map_homClass, ← homClass_comp]; rfl
  have k := D.mem_of_isClosedClass_of_isCharting D.isClosedClass_isGood (@fun Y ↦
    D.isClosedClass_isGood.2 _ (relFreeAb.shortExact _).2 ((D.isGood_iff_of_isCohomEquiv (freeAb.map
    (Subfunctor.ι ⊥)) fun _ z ↦ (z (U := .whisker (Y := (offClosedFibre Y).toFunctor) ⊥ _) fun _ y
    _ ↦ (·.1.1.elim (eq_top_mono (by simp [IdealFamily.ofMaximalIdeal,
    IsLocalRing.maximalIdeal_eq_bot]) y.2))).isCohomEquiv).1 (D.isClosedClass_isGood.1 _
    (freeAb.hom_ext nofun)))) ‹IsCharted ..›.1 ⟨(i (hasFlatBaseChange_reprFunctor _)
    (isoOfAppBijective (toUnit _) (fun _ ↦ by exact ⟨fun _ _ _ ↦ congr(⟨$(CommAlgCat.hom_ext
    (by ext))⟩), (⟨⟨_root_.structureMap⟩, .refl ·⟩)⟩) ≪≫ isoWhiskerLeft _ (isoOfAppBijective _
    pointMap_ofSelf_bijective).symm)).2 (.transfer (ac _) (bijective_of_isIso ((moduleCoeff _).map
    (CommAlgCat.isoMk (.ofBijective _ (Algebra.TensorProduct.includeLeft_bijective
    ((bijective_const_of_isDomain (B := .of Ω)).of_comp_left up_injective)))).1))
    (by intros; erw [← (moduleCoeff
    _).map_comp_apply, ← map_comp_apply, CommAlgCat.isInitialSelf.hom_ext (_ ≫ _)]; rfl)),
    .of_surjective _ ((sectionEquiv ..).surjective.comp
    (bijective_const_of_isDomain (B := .of Ω)).2)⟩
  have h := (isAffinelyCovered_algPoints (·.2.2) Y).hasFlatBaseChange
  ⟨fun _ _ _ ↦ fun Φ n ↦ (bijective_iff_of_comm_sq (baseChangeMap_pull (𝟙 _) _) (map_bijective
    bijective_id (isBijective_algToBaseChange Ω Y (moduleCoeff
    Φ) n)) (by simpa using! isBijective_algToBaseChange ..)).2 (h ..),
    ((isBijective_algToBaseChange ..).finite_iff.2 <| k.2.of_injective _ <|
    of_injective ·), fun e ↦ (isBijective_algToBaseChange Ω Y _).trans ((i h
    (isoOfAppBijective (toGenericPoints Ω e Y) (·.bijective_generic_points))).1 k.1)⟩
end FoldSeg4
section FoldSeg5
open CategoryTheory Functor TotalH HodgeTatePair
variable {p k E} [Field k] [EmbeddedInQpBar p k] {g : Gp p} [Field E] [Algebra E k]
  (hg : ∀ z : E, g (algebraMap k _ (algebraMap E k z)) = algebraMap k _ (algebraMap E k z))
theorem hodgeTateMap_galois_twist {N : AbFunctor (CommAlg E)} {q h n} {x : HodgeH N q} {t ξ} (hξ :
  hodgeTateMap h x.baseChange = restrictToPairs ξ)
  (ht : algebraMap k (PadicAlgCl p) t = algebraMap _ _ (cyclotomicGp g⁻¹).1) :
  let τ : genericOver ⋙ restrictAlg E k ⟶ PadicTest.twist g ⋙ genericOver ⋙ restrictAlg E k :=
    .mk fun c ↦ CommAlg.homOfRingHom (.id c.GenericRing)
    fun z ↦ by symm; erw [c.structMap_twist, smul_coe_Cp, hg]; rfl
  restrictToPairs ((Comparison.of _ (twistGenericCoeff g)).pull (whiskerRight τ N) n ξ : type_of%
    ξ) = restrictToPairs (t ^ h • ξ) := by
  intro τ
  let φ := (@HodgeTest.baseComparison k _ E _ _).φ
  let σ : _ ⟶ HodgeTatePair.galTwist g ⋙ toHodgeTest ⋙ φ :=
    toHodgeTest.whiskerLeft (HodgeTest.scaleModule t φ) ≫ .mk (⟨τ ·.test, .id⟩)
  let S := whiskerRight σ HodgeTest.sqZeroExt
  obtain ⟨T, hT⟩ : ∃ T : pairAlg ⋙ restrictAlg E k ⟶ HodgeTatePair.galTwist g ⋙ pairAlg ⋙
    restrictAlg .., ∀ X x, (T X x).1.2 = S X x.1.2 := ⟨⟨fun X ↦ CommAlg.homOfRingHom
    ((RingHom.prodMap (.id _) (S X).1.1).restrict _ _ (by tauto)) fun z ↦ Subtype.ext
    (Prod.ext ((congrArg _ (hg z).symm).trans congr($((PadicTest.twist g X.test).uniqueLift.2
    ⟨X.test.uniqueLift.1.1.1.comp (.restrictScalars _ g.toAlgHom), fun _ ↦ (X.test.uniqueLift.1.1.2
    _).trans (smul_coe_Cp g _ ▸ X.test.structMap_twist ..).symm⟩).1 _)) ((S X).1.2 z)), fun X Y
    f ↦ by ext; exact Subtype.ext (Prod.ext (congrArg (_ + ·) ((thickeningOver.mulMu_twist g Y.test
    _).trans (congrArg _ (show _ = (f.2 (t • _)).1 by
    erw [← ht, ← algebraMap_smul X.GenericRing, map_smulₛₗ, RingHom.coe_coe, AlgHom.commutes]
    rfl)))) congr($(S.2 f) _))⟩, by tauto⟩
  rw [restrictToPairs.map_smul]; erw [← hξ, ← comp_smul, ← scaleModule_comp_contractionPow,
    ← contractionPow_galTwist g, homClass_comp_homClass_comp]
  refine .trans ?_ ((congrArg _ ((TotalH.map_comp_assoc (restrictAlong _) _).symm.trans
    congr(comp (.map _ $hξ) _))).symm.trans
    (comp_assoc_of_sq (pull_twist (Comparison.pull_trans _) σ (whiskerRight T N) (by ext; rfl) (by
    ext : 2; simpa using! (N.map_commSq ⟨by ext; apply hT⟩).w)) _))
  erw [map_of, of_comp_homClass, homClass_comp_of]; simp [restrictToPairs, Comparison.pull, H.map,
    H.push, mapExactFunctor_mapExactFunctor]; congr 3 with : 2
  exact (N.map_commSq ⟨by ext; apply congr($(hT ..).1)⟩).w.symm
end FoldSeg5
section
open CategoryTheory ModuleCat.Algebra
variable {p} [ThePrime p] {R : CommRingCat} [Algebra R Ω] {Y} [@IsCharted R Y Ω _ _]
  [AlgebraicGeometry.IsProper Y.hom]
lemma finite_padic_cohomology n : Module.Finite ℤ_[p] (H (freeAb (testIncl ⋙ geomPoints R Ω Y))
  ellAdicCoeff n) := let := (IsAlgClosed.lift : Ω →ₐ[ℚ] ℂ_[p]).toAlgebra
  finite_H_ellAdicCoeff ((finite_and_primitive_comparison Ω (isAcyclicAt_almostCoeff (N :=
    Unit) (by simp)) Y).2.1 n)
instance {n} : Module.Finite ℚ_[p] (ellAdicCohom R Ω n ⟨Y⟩) :=
  (finite_padic_cohomology n).base_change ..
lemma ellAdicCohom.continuous_galoisAction n K [Field K] [Algebra K Ω] [Algebra R K] [IsScalarTower
  R K Ω] [G : IsProGalois Gal(Ω/K) K Ω] x {N} (l : _ →ₗ[ℚ_[p]] Fin N → PadicAlgCl p) :
  Continuous fun g ↦ l (galoisAction R Ω Gal(Ω/K) Y n g x) := by
  obtain ⟨S, rfl⟩ := x.exists_finset; erw [funext fun _ ↦ map_sum (l ∘ₗ _) ..]
  refine continuous_finsetSum S fun ⟨a, t⟩ _ ↦ .of_at fun g₀ ↦
    tendsto_sub_nhds_zero_iff.1 fun U hU ↦ (map_mul_left_nhds_one _).ge (Filter.mem_map.2 ?_)
  let L := (l ∘ₗ (galoisAction ..) g₀).restrictScalars ℤ_[p] ∘ₗ (TensorProduct.mk ..) a
  obtain ⟨k, b, q, w⟩ := (((tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    ).eventually (((Submodule.isCompact_of_fg
    (.map L (finite_padic_cohomology n).1)).isVonNBounded ℚ_[p] hU).eventually_nhds_zero
    (mem_of_mem_nhds hU))).and (.of_forall exists_ellAdicCoeff_modShortExact_pow)).exists
  obtain ⟨s, z, ht⟩ := ((isProperOver_pointsToBase Y.hom).isCohomContinuous.isFilteredColimit_adjoin
    _ Ω (𝟙 _) n).2 (t.push _ q n)
  filter_upwards [s.eventually_all.2 fun b _ ↦ (G.6 b).mem_nhds rfl] with g hg
  simp; refine (w.exists_smul_eq_of_push_eq_zero _ ?_).elim fun _ e ↦
    map_sub L .. ▸ congr(L $e) ▸ by simpa using! b (by simp)
  erw [map_sub, sub_eq_zero, ← H.map_push, ← ht, ← HV.map_comp, ← Functor.map_comp, ← op_comp]
  congr with a; exact (g.toAlgHom.restrictScalars R).adjoin_le_equalizer 1 hg a.2
open TensorProduct Function AlgebraicGeometry Functor AlgebraTensorModule Comparison PadicTest
  Module
variable {p : _} [ThePrime p] {R : CommRingCat} [Algebra R OC] [Algebra R Ω] {e : Ω →+* PadicAlgCl
  p} (he : ∀ r, e (algebraMap R Ω r) = (algebraMap R OC r).1) {S} [CommRing S] [Algebra Ainf S]
  [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (K) [CommRing K] [Algebra S K] [Algebra ℚ_[p] K]
  [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [IsScalarTower ℤ_[p] S K] {Ψ} (θ :
  asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) (n) {Γ} [Group Γ] [MulSemiringAction Γ Ω]
  [SMulCommClass Γ R Ω] {j : Γ → Gp p} (hj : ∀ g x, j g (e x) = e (g • x))
noncomputable def toTwistAlg g :
  algFunctor ⋙ restrictAlg R _ ⟶ PadicTest.twist (j g) ⋙ algFunctor ⋙ restrictAlg R _ :=
  .mk (CommAlg.homOfRingHom (.id _) fun z ↦ congrArg ·.structureMap (by ext; simp [← he, hj]))
instance (M : ModuleCat ℚ_[p]) : CompatibleSMul ℤ_[p] ℚ_[p] K M :=
  IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors _) ..
lemma exists_period_map [Flat S K] (h : IsPeriodRingPair p S K) : ∃ J : ∀ Y,
  K ⊗[ℤ_[p]] ellAdicCohom R Ω n ⟨Y⟩ →ₗ[K] H _ _ n, (∀ W Y (f : W ⟶ Y) x,
  J W ((((ellAdicCohom ..).map f.op).hom.restrictScalars _).baseChange _ x) = .map _ (freeAb.map
  (testPoints.map f)) n (J Y x)) ∧ (∀ Y g σ (β : PadicTest.twist (j g) ⋙ moduleCoeff Ψ ⟶ moduleCoeff
  Ψ), (∀ c a (w : WittVector p (TiltRing c)), (∀ i, w.coeff i ^ p = w.coeff i) → β c ⟨θ.1 _
  (a ⊗ₜ .of _ _ (1 ⊗ₜ w))⟩ = ⟨θ.1 c (σ a ⊗ₜ .of _ _ (1 ⊗ₜ w))⟩) → ∀ x, J Y (.map σ (.restrictScalars
  _ ((ellAdicCohom.galoisAction ..) g)) x) = (of _ β).pull (freeAbMap (whiskerRight
  (toTwistAlg he hj g) _)) n (J Y x)) ∧ ∀ Y [IsCharted Y Ω] [IsProper Y.hom], Bijective (J Y) := by
  let E Y := equivOfCompatibleSMul ℚ_[p] ℤ_[p] K K (ellAdicCohom R Ω n ⟨Y⟩) ≪≫ₗ cancelBaseChange ..
  obtain ⟨⟨b, hb, hB⟩, _⟩ := exists_primitive_period_comparison K θ h, Flat.trans ℤ_[p] ℚ_[p] K
  algebraize [(algebraMap _ ℂ_[p]).comp e]
  let J Y (α : freeAb (testPoints Y) ⟶ _) := pullₗ b α n ∘ₗ baseChangeMap .. ∘ₗ (E Y).1
  have hT Y α a x : J Y α ((E Y).symm (a ⊗ₜ x)) = pull ⟨_,
    whiskerLeft _ (tensorWith.mk _ a _) ≫ coeffMap b⟩ α
    n x := by simpa [J] using! (pull_push ⟨_, _⟩ (h := rfl) ..).trans (Abelian.Ext.comp_mk₀_id _)
  refine ⟨(J · _), fun _ _ _ ↦ ?_, fun _ _ _ β hβ ↦ ?_, fun Y ↦
    (finite_and_primitive_comparison Ω (isAcyclicAt_almostCoeff h.pFlat_smul_eq_zero)
    Y).elim fun hN P ↦ (hB hN (isAffinelyCovered_algPoints (ι := algFunctor) (·.isTest.2)
    _).hasFlatBaseChange finite_padic_cohomology (P.2 he) n).comp ((hN ..).comp (E Y).bijective)⟩
  all_goals refine (reindex_equiv (E _).symm).1.2 (·.inductionOn (fun a x ↦ (hT _ _ _
    (x.map _ _ n)).trans ?_) (by simp_all))
  · simpa [hT] using (map_pull_eq_pull_map ..).symm
  simp [hT, pull_trans, ← map_pull_eq_pull_map (Category.id_comp _)]
  refine (congrArg (pull _ · n x) (freeAb.hom_ext fun _ _ ↦ congrArg FreeAbelianGroup.of
    (baseChangeOf.ext (congrArg ULift.up (Spec.map_comp_assoc (𝟙 _) ..)) fun x ↦ by
    erw [eq_comm, structMap_twist, smul_coe_Cp,
      hj]; rfl))).trans congr(pull ⟨_, $(?_)⟩ _ n x); ext d ⟨y⟩
  exact .trans congr(⟨$(hb ..)⟩) (congr(β d ⟨$(hb ..)⟩).trans (hβ _ _ _ fun i ↦
    (map_pow ..).symm.trans (congrArg _ (LocallyConstant.ext fun _ ↦ ZMod.pow_card _)))).symm
end
namespace ellAdicCohom
open CategoryTheory AlgebraicGeometry CommRingCat ellAdicPull Comparison
variable {ℓ} [ThePrime ℓ] {R : CommRingCat} [Algebra R Ω] {Γ} [Group Γ] [MulSemiringAction Γ
  Ω] [SMulCommClass Γ R Ω] {A : ClosurePlace} (hR : ∀ r, algebraMap R Ω r ∈ A) (hℓ : IsUnit (ℓ : A))
  {W Y : Over (Spec R)} [IsCharted Y R] [IsProper Y.hom] {n p f : ℕ} [Fact p.Prime] (hp :
  A.valuation p < 1) {U : PointFunctor} (hX : ∀ B, U B → (p : B) = 0) (j)
def frobEnd : U ⟶ U := ⟨fun B ↦ ↾fun x ↦ U.map (ofHom (frobPow (hX B x) j)) x,
  by intros; ext; dsimp; simp_rw [← U.map_comp_apply]; congr 3; aesop⟩
lemma ellAdicPull_frobEnd : ellAdicPull n (freeAb.map (mapOnTests (frobEnd hX j))) = 1 := by
  ext; exact congrArg (_ ⊗ₜ ·) ((hasUnivPoints_elements.isBijective n).1 ((map_pull_eq_pull_map
    (by rfl) ..).symm.trans ((H.map_id _).trans (congr($(pull_whiskerRight (⟨fun A ↦
    ⟨ofHom (frobPow (hX _ A.2) _)⟩, by intros; ext; exact (map_pow ..).symm⟩ : elementsProj
    (testIncl ⋙ U) ⟶ _) ..) _).symm.trans congr(pull ⟨_, $(by ext A ⟨⟨⟩⟩; congrm ⟨⟨fun i ↦ ⟨_ ∘
    $(by ext q; simp [q.2.pow_mem_iff_mem, NeZero.pos]), _⟩⟩⟩)⟩ _ n _)))))
include hR hℓ hp
lemma congruence_relation [IsProper W.hom] {g} (hg : IsFrob A (p ^ f) g) {I : Type} [Fintype I] (u :
  I → (W ⟶ Y)) (e : I → ℕ) m (h : CongruenceRelation m (algebraMap R Ω ⁻¹' A.nonunits) p (e · * f)
  u) x : ∑ i, m i • (ellAdicCohom ..).map (u i).op (galoisAction R Ω Γ Y n (g⁻¹ ^ e i) x) = 0 := by
  algebraize [RingHom.codRestrict _ A hR]
  obtain ⟨y, rfl⟩ := (isCohomEquiv_generic_fibre hp hℓ Y).bijective_ellAdicPull.2 x
  let σ i := (MulSemiringAction.toRingHom ..).restrict A A (mem_decompGroup_iff.1
    (pow_mem (inv_mem hg.1) (e i)) · |>.2)
  let mv i : baseChangeOf .. ⟶ (geomPoints ..) Y := (geomPoints ..).2 (u i) ≫ baseChangeTransition _
    (ofHom (σ i)) (by ext r; exact smul_algebraMap _ r)
  let F i := frobEnd (fun _ x ↦ by simpa using x.2 p hp) (e i * f) ≫
    (zeroPoints (fibreProd.snd ..) (A · < 1)).ι ≫ mv i
  conv_lhs => enter [2, i]; erw [comp, ← freeAb.4, comp, ← freeAb.4, freeAb.4 (mapOnTests
    (baseChangeTransition _ (ofHom A.subtype) rfl)) (mapOnTests (mv i)), ← comp, ← map_zsmul]
  have := by
    simpa [← comp] using congr(ellAdicPull n $(relationLocus_sum_eq_zero m (mapOnTests <| F ·)) y)
  refine (map_sum ..).symm.trans ((congrArg _ ((Set.ext A.valuation_lt_one_iff ▸
    ((isProperOver_pointsToBase _).baseChange _).proper_base_change hℓ :
    IsCohomEquiv ..).bijective_ellAdicPull.1 ((((isProperOver_pointsToBase _).baseChange
    _).isCohomDense_of_coincidences F fun z B x H ↦ ?_).isCohomEquiv.bijective_ellAdicPull.1
    (by simpa [F, ← comp, ellAdicPull_frobEnd])))).trans (map_zero _))
  have hP i a := z.2 (a - σ i a ^ _) (by simpa [σ] using! (hg.pow (e i)).2 (σ i a) (by simp))
  exact (@h _ _ (.of_eq_zero Fact.out (by simpa using z.2 p hp)) _ (congr($(z.1.2).1.1 ·).trans <|
    z.2 _ ·)).mono fun i j h ↦ H (baseChangeOf.ext congr(⟨$h⟩) fun a ↦ by
    simpa [← pow_mul'] using! (hP i a).trans (hP j a).symm)
lemma galoisAction_eq_one_of_inertia {g} (hg : g ∈ inertiaGroup Γ A) :
  galoisAction R Ω Γ Y n g = 1 := by ext; simpa [neg_add_eq_iff_eq_add] using (congruence_relation
  hR hℓ hp (f := 0) (inv_mem hg) ![𝟙 _, 𝟙 _] (↑) ![-1, 1] (by simp [CongruenceRelation, Cancels]) _)
end ellAdicCohom
section
open CategoryTheory AlgebraicGeometry TensorProduct Ideal WittVector Fact CharP Comparison
  Algebra.TensorProduct ConcreteCategory PadicTest ModuleCat.Algebra MulSemiringAction Function
  ULift Set
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
lemma ellAdicCohom.isCrystalline_and_linearFrob_rel {p} [ThePrime p] {R :
  CommRingCat} K [Field K] [Algebra R Ω] [Algebra K Ω] [Algebra R K] [IsScalarTower R K Ω] {A} [I :
  PadicPlaceEmbedding K A p] (hR : ∀ r, algebraMap R Ω r ∈ A) {W Y} [IsNoetherianRing R] [sm :
  IsCharted Y R] [IsCharted Y Ω] [IsProper Y.hom] n [IsProper W.hom] [IsCharted W Ω] {ι}
  [Fintype.{0} ι] (u : ι → (W ⟶ Y)) (a γ : ι → _) m (h : CongruenceRelation m
  {r | A.valuation (algebraMap R Ω r) < 1} p a u) (hW : ∀ i, IsWeilPair (I.toGp (γ i))
  (a i)) : let ρ := galoisAction R Ω _ Y n; IsCrystalline ρ ∧ ∑ i, m i • (((ellAdicCohom ..).map
    (u i).op).hom.restrictScalars _).baseChange _ ∘ₗ linearFrob ρ (γ i) (a i) = 0 := by
  intro ρ
  obtain ⟨⟨_, -, -, -, _, ⟨g, rfl⟩, w⟩, @⟨I, e, ⟨⟨⟩, hj⟩, _⟩⟩ :=
    Lift.exists_kummer_chart (decompGroup Gal(Ω/K) A), I
  let σ := ((algebraMap ..).comp (e.comp _)).codRestrict 𝓞_ℂ_[p] (by simpa)
  have hσ r : (e (algebraMap R Ω r) : ℂ_[p]) = σ r := rfl
  let := σ.toAlgebra
  let 𝔭 := (IsLocalRing.maximalIdeal _).comap σ
  let k := R ⧸ 𝔭
  have hk r :
    r ∈ 𝔭 ↔ ‖e (algebraMap _ Ω r)‖ < 1 := by simp [𝔭, OC.dvd_iff_norm_le, isUnit_iff_dvd_one, ←hσ]
  have hf {s f} (w : IsWeilPair (I.toGp s) f) : ∀ z : k, z ^ _ = z := Quot.ind fun r ↦
    Ideal.Quotient.eq.2
    (by simpa [← map_inv, *, norm_sub_rev] using w.2 _ ((intQpBar p).valuation_le_one ⟨_, hR r⟩))
  have : Finite k := .of_not_infinite fun _ ↦ absurd (Polynomial.funext (R := k) (by
    simpa using @hf g⁻¹ _ (by simpa)))
    (Polynomial.monic_X_pow_sub (p := .X) (by simp [one_lt_pow₀, out])).ne_zero
  let := (Finite.isField_of_domain k).toField
  have : CharP k p := .of_eq_zero out (Quotient.eq_zero_iff_mem.2 (by simp [𝔭, out]))
  obtain ⟨⟨M, hM⟩, y, hy⟩ := exists_cancels_frobPow_locally m a u 𝔭 (by simp [𝔭,
    out]) (by simpa [← hk,
    val_comap_lt_one] using h), IsBezout.isPrincipal_of_FG _ (𝔭.fg_of_isNoetherianRing.map σ)
  obtain ⟨⟨V, hV⟩, x, rfl⟩ := sm.1, IsAIC.exists_pow_eq (M + 1) y
  obtain ⟨⟨N, hN⟩, hy⟩ := OC.exists_dvd_pow (mt (.pow _) (map_comap_le (hy.ge (subset_span rfl))))
    (NeZero.ne ↑p), (mem_span_singleton.1 <| hy ▸ mem_map_of_mem σ (x := ·) ·)
  obtain ⟨hP, _, hA, h0⟩ := exists_crysPeriodAlgebra hN
  obtain ⟨g, hg', G'⟩ := hP.existsUnique_witt_lift (cast_eq_zero ..) (Ideal.Quotient.lift 𝔭
    (ocToAmaxModPd.comp σ) (hy · · |>.elim (by simp +contextual [h0])))
  algebraize [g]
  let v a (hf : ∀ z : k, z ^ p ^ a = z) := toCrysPoints V (r :=
    .comp (constantCoeff.liftOfRightInverse (teichmuller p) .refl ⟨pdQuotientMk
    _, by simp [IsCompleteTorsionFree.p_mem_pdIdeal, witt_reduction_spec k]⟩) (algebraMap _ k))
    ⟨fun B ↦ CommAlg.homOfRingHom (frobPow B.p_eq_zero_mod_pdIdeal a) fun z ↦
    .symm (congr(pdQuotientMap _ $((hg' (teichmuller p ⟦z⟧)).trans ((congrArg _ (hf _).symm).trans
    (map_pow ..)))).trans (map_pow ..)), by intros; ext; exact (map_pow ..).symm⟩
  choose J Jn Js JY using (exists_period_map hσ Bcris (.refl _) · hj hP.2)
  have A := (hasPartitions_periodAlg (S :=
    Amax) Bcris (.refl _)).hasZariskiDescent (𝟙 _) (by simp) (·.isTest.2)
  have U := A (hV.1.whisker (algFunctor ⋙ restrictAlg R _))
  let E n := LinearEquiv.ofBijective (H.mapₗ .. ∘ₗ J n Y) ((U.isCohomEquiv n).comp (JY ..))
  let P a hf := crysComparison.pull (freeAbMap (v a hf)) n
  choose C hC using fun z ↦ (E n).surjective (P 0 pow_one z)
  have key {a} γ hf z : E n (tensorAction _ ((a, toGp γ) : FrobGal) (ρ γ) (C z)) = P a hf z :=
    let F := toRingHom FrobGal Amax (a, toGp γ)
    let τ := Functor.whiskerRight ((baseChangeTranspose (PadicTest.twist (toGp γ) ⋙ tilt ⋙
      wittFunctor) (tilt ⋙ wittFunctor ⋙ algBaseChange _ ⋙ @restrictAlg _ _ _ _ F.toAlgebra)).2
      ⟨fun c ↦ CommAlg.homOfRingHom (includeRight.1.comp
      (map (iterateFrobenius c.TiltRing p a))) fun _ ↦ .trans (congrArg (tmul _ 1) (ext fun _ ↦ by
      exact congr($(tiltMap_comp ..)^_).trans (map_pow ..).symm)) ((includeRight.2 _).trans
      congr($(hA ..) ⊗ₜ _).symm), by intros; ext; exact congrArg (tmul _ 1) (ext fun _ ↦ (map_pow
      (tiltMap ..) ..).symm)⟩) (restrictAlg ℤ _ ⋙ algCompletion ℤ p ⋙ forget₂ _ CommRingCat)
    have hτ {c a w b v} (h : F a = b) (k : _ = v) : τ c (.of _ _ (a ⊗ₜ w)) = .of _ _ (b ⊗ₜ v) :=
      (adicMap_algebraMap ..).trans (congrArg _ congr($((mul_one _).trans h) ⊗ₜ $k))
    let β := (baseChangeTranspose (_ ⋙ _ ⋙ periodAlg ..) ((_ ⋙ periodAlg ..) ⋙ algBaseChange Bcris ⋙
      @restrictAlg _ _ _ _ (toRingHom FrobGal _ (a, _)).toAlgebra)).2 ⟨fun c ↦ CommAlg.homOfRingHom
      (includeRight.1.comp (τ c).hom) fun _ ↦ .trans congr(1 ⊗ₜ $(hτ rfl (map_one _)))
      ((includeRight.2 _).trans congr($(smul_algebraMap_eq_algebraMap_smul ..) ⊗ₜ _).symm),
      by intros; ext; exact congr(1 ⊗ₜ $(τ.naturality_apply ..))⟩
    have fix w := congr($(G' (F.comp g) fun w ↦ congr(pdQuotientMap F $(hg'
      w)).trans ((w.1 0).inductionOn fun z ↦ (untilt_surjective_of_isAIC (σ z)).elim fun t h ↦
      (congrArg _ (h ▸ ocToAmaxModPd_untilt t)).trans (hf ⟦z⟧ ▸ show _ = ocToAmaxModPd (σ
      _) by erw [map_pow, ← (Subtype.ext (by simp [← hσ, hj]) : toGp γ • σ z = σ z), ← h,
      ← untilt_frobGal_smul (a, _), ocToAmaxModPd_untilt, ← smul_teichmuller, ← hA]; rfl))) w)
    let σ : _ ⋙ crysComparison.φ ⟶ crysComparison.φ := ⟨fun c ↦ ⟨ofHom ⟨(τ c).hom, fun _ ↦
      hτ (fix ..) (map_one _)⟩⟩, by intros; ext; apply τ.naturality_apply⟩
    let N := freeAb V.toFunctor
    .trans (congrArg (H.map _ _ n) (Js n Y _ _ (Functor.whiskerRight β (restrictAlg ℤ _ ⋙
      moduleCoeff (asModules (𝟭 _))) :) (fun _ _ _ h ↦ congrArg up (congrArg₂ (tmul _) (mul_one _)
      (hτ (map_one _) (ext fun i ↦ congr($(pow_iterate ..) _).symm.trans (iterate_fixed (h i) _)))))
      _)) (.trans (map_pull_eq_pull_map
      (b := (Functor.whiskerRight (toTwistAlg hσ hj γ) N :)) ..) (.trans (congrArg _ (hC z)) (.trans
      (pull_trans ..) ((congrArg (pull ⟨_, ·⟩ _ n z) (by ext; exact congr(⟨$(by simp) ⊗ₜ _⟩))).trans
      (congr($(pull_whiskerRight σ crysComparison.coeffHom _) z).trans (congrArg (pull _ · n z) (by
    ext c : 2
    exact ((N.map_comp ..).trans congr($(N.map_comp ..) ≫ _)).symm.trans (congrArg _ (ext_apply
      (untilt_surjective_of_isAIC (R := c.ProdRing).forall.2 fun x ↦
      (congrArg _ (fontaineTheta_teichmuller x)).symm.trans (congr(pdQuotientMap (τ
      c).hom $((pow_one _).trans (testToThickening_theta ..))).trans ((congrArg _ (hτ (map_one _)
      (map_teichmuller ..))).trans ((testToThickening_theta ..).symm.trans (.trans
      (congrArg _ ((fontaineTheta_teichmuller _).trans (map_pow ..))) (map_pow ..)))))))))))))))
  have S : Submodule.span Bcris (.range C) = ⊤ := by
    simp [← Submodule.map_eq_top_iff (e := E n), Submodule.map_span, ← range_comp', hC]
    exact span_range_crysComparison_pull_eq_top V _ (isoOfAppBijective _ fun _ ↦
      (funext pow_one).symm.subst bijective_id).isIso_hom (witt_reduction_spec k k).2.1 hV
      (irreducible p) (.equiv <| equivOfCompatibleSMul _ ℚ_[p] .. ≪≫ₗ E ·) n
  have D {F} z : C z ∈ fixedPeriods ρ _ F := .of_forall fun g ↦
    (E n).injective (hC z ▸ key g pow_one z)
  refine (iff_self_and.2 fun c ↦ LinearMap.ext_on_range S fun z ↦ ?_).1
    (eq_top_mono (Submodule.span_mono (range_subset_iff.2 D)) S)
  let T := ⨅ i, (V.whisker _).preimage (testPoints.map (u i))
  refine (JY ..).1 (((InfClosed.iInf_mem (s := IsCohomDense _) (fun _ a _ ↦
    a.inf) .of_top_le fun _ ↦ U.preimage _ : T ∈ _).isCohomEquiv n).1 ?_)
  simp [linearFrob_apply c.isPotCrys (hW _), D, Jn, H.map_map]
  exact .trans congr(∑ i, m i • $(congr(H.map _ $freeAb.hom_ext n _).trans
    ((H.map_comp ..).trans ((congrArg _ (key _ (hf (hW i)) z)).trans (H.map_map (T.homOfLe (iInf_le
    _ i) ≫ Subfunctor.fromPreimage ..) ..))))) (H.sum_map_eq_zero_of_relationLocus _ _ (A fun c w ↦
    (hM _ _ hN hy c (T.ι.1 c w) · · |>.imp fun _ ↦ .imp_right fun e B f b ↦ ((congrArg _
    (by funext; exact ((_ ≫= Category.assoc ..).trans (Spec.map_comp_assoc ..).symm))).mpr (e _
    (CrysTest.p_eq_zero_mod_pdIdeal _) _ (by exact b.map (testToThickening B).hom)
    ((((testToThickening B).hom.comp f).2 _).trans (congr(pdQuotientMap _ $h0).trans (map_zero
    _))))).mono fun _ _ e ↦ Subtype.ext (down_injective (Over.OverMorphism.ext e)))).isCohomEquiv _)
end
section FoldSeg7
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor
open AlgebraicGeometry CategoryTheory PairRestrictBijective H freeAb ModuleCat.Algebra
lemma exists_hasHodgeTateWeight {p h : ℕ} {R :
  CommRingCat} {E k : Type} [Field k] [Field E] [EmbeddedInQpBar p k] [Algebra R Ω] [Algebra R E]
  [Algebra E k] [Algebra E Ω] [IsScalarTower R E Ω] {Y} [IsCharted Y Ω] [IsProper Y.hom] {A} [I :
  PadicPlaceEmbedding E A p] (hR : ∀ r, algebraMap R Ω r ∈ A) (he : ∀ x, algebraMap k
  _ (algebraMap E k x) = I.e (algebraMap E Ω x)) d [SmoothOfRelativeDimension d Y.hom] ε (hk :
  ∀ z, algebraMap k (PadicAlgCl p) (ε z) = z) {W} [IsProper W.hom] {q} (x : HodgeH _ q) : ∃ v, ∃ Θ :
  _ →ₛₗ[ε] _, HasHodgeTateWeight (ellAdicCohom.galoisAction R Ω (decompGroup Gal(Ω/E) A) Y (q + h))
  h v ∧ ∀ u : W ⟶ Y, hodgeTateMap h (x.map (freeAb.map ((algPoints E R).map u))).baseChange =
  Θ ((((ellAdicCohom ..).map u.op).hom.restrictScalars _).baseChange _ v) := by
  obtain ⟨⟨e, ⟨⟨⟩, hj⟩, _⟩, θ, hθ⟩ := I, exists_periodAlg_iso_genericAlg
  algebraize [theta.comp (algebraMap ℤ_[p] _), (algebraMap E k).comp (algebraMap R E),
    (.codRestrict (.comp (algebraMap ..) (e.comp _)) _ (by simpa) : R →+* OC)]
  have := IsScalarTower.of_algebraMap_eq (S := OC) ((OC.toPadicIntAlgHom _).2 · |>.symm)
  choose J h₁ h₂ h₃ using exists_period_map (R := R) (by tauto) _ θ _ hj isPeriodRingPair_OC
  let B {n} W [IsProper W.hom] : H (genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R W))
    genericCoeff n ≃ₗ[k] _ := .ofBijective (mapₗ ..) (IsCohomEquiv.of_bijective (p :=
    toGenericPoints k (congrArg (algebraMap ..) <|
    IsScalarTower.algebraMap_apply R E Ω · ▸ he _) W) (·.bijective_generic_points) n)
  have S W z y : J W (z • y) = ε z • J W y := by
    erw [← (J W).map_smul, RingHom.comp_apply, hk, IsScalarTower.algebraMap_smul]
  refine (exists_hodgeTateMap_eq ?D h x.baseChange).elim fun ξ hξ ↦ ((h₃ Y).2 (B Y ξ)).elim fun v
    hv ↦ ⟨v, restrictToPairs ∘ₛₗ (B W).symm.comp ⟨_, S W⟩, fun g ↦ (h₃ Y).1 ((h₂ Y g _ _ (by
    intros; erw [hθ, hθ, PadicTest.structMap_twist]; rfl) _).trans (hv ▸
    (Comparison.map_pull_eq_pull_map (by exact hom_ext fun A _ ↦ congr(.of ⟨$(Over.OverMorphism.ext
    ((Spec.map_comp_assoc (CommRingCat.ofHom (algebraMap A.ProdRing A.GenericRing)) (𝟙 _)
    _).symm.trans (Spec.map_comp_assoc (𝟙 _) (CommRingCat.ofHom
    (algebraMap A.ProdRing A.GenericRing)) _)))⟩)) ..).symm.trans ((congrArg (B Y)
    (injective_restrictToPairs ?D (hodgeTateMap_galois_twist (by simp [*]) hξ (hk _)))).trans (by
    simp [algebra_compatible_smul (PadicAlgCl p), *])))), fun u ↦ by
    simp [hodgeTateMap_map, *, ← restrictToPairs_map]; rw [(B W).symm_apply_eq.2]
    erw [← map_comp, ← map_comp]; congr 2; exact hom_ext⟩
  apply (hasAtlas_algPoints d).isChartCovered.pairRestrictBijective
end FoldSeg7
