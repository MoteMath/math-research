import Lib.PadicHodge.PeriodRings.BdR
import Lib.Cohomology.ProperBaseChange.ValuativeDensity
noncomputable section
section
open CoeffAction CategoryTheory Function Ideal TensorProduct Functor ModuleCat ULift H Finset Fact
variable {C C'} [Category C] [Category C'] {S} [CommRing S] {N G : AbFunctor C} {N' G' : AbFunctor C'} {φ} {α : N' ⟶ φ ⋙ N} {Φ : C ⥤ ModuleCat S} {Φ'} {β : φ ⋙ Φ ⟶ Φ'} {a : S} {q : moduleCoeff Φ ⟶ G} {p} [ThePrime p] {B} [CommRing B] [Algebra S B] {W} [CommRing W] {π : W} {X E Y F : Type*} [Algebra W S] [AddCommGroup X] [Module W X] [AddCommGroup E] [Module W E] [AddCommGroup Y]
variable (π X) in
abbrev IsDerivedComplete := Bijective (shiftDiff X π)
lemma IsDerivedComplete.of_isAdicComplete (_ : IsAdicComplete (span {π}) X) : IsDerivedComplete π X := ⟨out, out⟩
lemma IsDerivedComplete.exists_eq_of_approx (hD : IsDerivedComplete π X) (hF : IsDerivedComplete π E) (f : E →ₗ[W] X) (g : F → X) (h : ∀ x, ∃ n y, g x = f n + π • g y) x : ∃ n, f n = g x := mem_range_of_approx (s := ⟨hF.2⟩) (i := ⟨hD.1⟩) f (by simp) g h x
lemma IsDerivedComplete.pi {ι} (h : IsDerivedComplete π X) : IsDerivedComplete π (ι → X) := (swap_bijective.comp h.comp_left).comp swap_bijective
attribute [local simp] shiftDiff smul_eq_push smul_sub funext_iff
lemma IsDerivedComplete.of_retract (hF : IsDerivedComplete π E) m (a : E →ₗ[W] X) (b : X →ₗ[W] E) (h : ∀ x, a (b x) = π ^ m • x) : IsDerivedComplete π X := let g (y u : ℕ → _) j := ∑ i ∈ range m, π ^ i • y (j + i) + a (u (j + m))
  have t x : g (shiftDiff _ π x) (b ∘ x) = x := by
    simp_all [g, smul_smul, ← pow_succ, add_assoc, sum_range_sub' _]
  by use fun x y e ↦ t x ▸ t y ▸ congrArg₂ g e (hF.1 (by simpa using congr(b ∘ $e))), fun y ↦
    (hF.2 (b ∘ y)).imp' (g y) fun u e ↦ .trans (by simp [g, ← e, smul_sum]; grind [smul_comm]) (t y)
lemma IsDerivedComplete.congr (e : E ≃ₗ[W] X) (h : IsDerivedComplete π E) : IsDerivedComplete π X := h.of_retract 0 e e.symm (by simp)
lemma IsDerivedComplete.baseChange [IsDomain W] [IsDiscreteValuationRing W] (h : Irreducible π) (hD : IsDerivedComplete π X) (hW : IsDerivedComplete π W) (hS : IsDerivedComplete (algebraMap W S π) S) (hf : Module.rank W X < .aleph0) : IsDerivedComplete (algebraMap W S π) (S ⊗[W] X) := have ⟨s, hs, hs'⟩ := exists_maximal_linearIndepOn W id
  have ⟨_⟩ := Cardinal.lt_aleph0_iff_fintype.1 (hs.cardinal_le_rank.trans_lt hf)
  let τ := Fintype.linearCombination W _
  have ⟨m, r, H⟩ : ∃ j r, ∀ y, ∃ z, π ^ j • (r + π ^ j • (y + π • z)) ∈ τ.range := by
    by_contra! y; choose y hy using y
    let t := (Nat.fold · (fun j _ s ↦ s + π ^ j • y j s) 0)
    have ⟨u, hu⟩ := hD.2 fun j ↦ y j (t j)
    have ⟨a, o, ha⟩ := dite _ (fun _ ↦ ⟨1, by aesop⟩) (hs' (u 0))
    obtain ⟨n, c, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible o h
    use hy n (t n) (u n.succ) (by simpa [τ, ← congrFun hu, mul_smul, ← (by induction · <;> simp [t, ← congrFun hu, *]; module : ∀ j, u 0 = t j + π ^ j • u j)] using ha)
  .of_retract (hS.pi.congr (piScalarRight ..).symm) (m + m) (τ.baseChange S) (.baseChange _ (.codRestrictOfInjective (π ^ (m + m) • 1) τ hs.fintypeLinearCombination_injective (id (hD.exists_eq_of_approx hW.pi τ _ fun y ↦ by choose z u e using H; use u y - u 0, z 0 - z y; simp [e]; module
    )))) (by induction · <;> simp_all [← map_pow])
lemma IsDerivedComplete.cohomology (h : ∀ A, IsDerivedComplete a (Φ A)) N n : IsDerivedComplete a (_root_.H N (moduleCoeff Φ) n) := (Comparison.bijective_iff_of_comm_sq (by
  simp [← push_comp]; use (fun _ ↦ congr($((pushHom ..).map_sub ..) ·).symm)) (pi_bijective ..) (pi_bijective ..)).1 (push_bijective_of_isIso (isoOfAppBijective (piAbFunctor.lift (_ - _)) (h · |>.congr moduleEquiv.symm)).isIso_hom _)
abbrev ModShortExact (a : S) (q : moduleCoeff Φ ⟶ G) := ∃ w, (ShortComplex.mk (End.asHom (act a)) q w).ShortExact
lemma modShortExact_of_isReductionMod {F} {q : Φ ⋙ forget₂ _ _ ⟶ F} {m : ℕ} (h : ∀ A, IsSMulRegular (Φ A) m ∧ IsReductionMod m (q A)) : ModShortExact ↑m (whiskerRight q _) := by
  simp [IsSMulRegular, IsReductionMod, forall_and, ← Nat.cast_smul_eq_nsmul S] at h
  exact ⟨_, (shortExact_of_app (α := whiskerRight ((m : S) • 𝟙 Φ) _) (g := q) h.1 h.2.2 h.2.1).2.map_of_exact ((whiskeringRight ..).1 AddCommGrpCat.uliftFunctor)⟩
lemma ModShortExact.exists_smul_eq_of_push_eq_zero (h : ModShortExact a q) {n} x : push N q n x = 0 → ∃ y, a • y = x := x.covariant_sequence_exact₂ N h.2
lemma Comparison.IsBijective.of_mod {q'} {γ : _ ⟶ G'} (h : ModShortExact a q) (h' : ModShortExact a q') (w : coeffMap β ≫ q' = φ.whiskerLeft q ≫ γ) (d : ∀ n, Surjective (a • · : (pullₗ β α n).ker → _) → IsDerivedComplete a (H N (moduleCoeff Φ) n)) (d' : ∀ n, IsDerivedComplete a (H N' (moduleCoeff Φ') n)) (k : (of φ γ).IsBijective α) : (ofModuleHom φ β).IsBijective α := have c := (pull_hom_covariant h.2 h'.2 ⟨_, _, _, .symm (by ext; apply_rules [up_inj.2, LinearMap.map_smul]), w⟩ α)
  have i n := (fun v ↦ And.intro (d n v) (.of_ker _ ((d n v).exists_eq_of_approx (d' n) 0 (↑) (⟨0, v · |>.imp (by aesop)⟩) ⟨·, ·⟩ |>.choose_spec.symm))) (by simpa [Surjective] using! ((c.rotate.exists_preimage · (k n).1) (n.casesOn (by tauto) (k · |>.2)) 0))
  (⟨i · |>.2, (d' _).exists_eq_of_approx (i _).1 (pullₗ ..) _ (c.exists_preimage_mod_f (i _).2 · _ ((k _).2 _).choose_spec |>.imp (by tauto))⟩)
lemma IsCompleteTorsionFree.isDerivedComplete (h : IsCompleteTorsionFree B) : IsDerivedComplete (p : S) B := .of_isAdicComplete (isAdicComplete_over_base h.2)
lemma IsCompleteTorsionFree.isSMulRegular_natCast (h : IsCompleteTorsionFree B) : IsSMulRegular B (p : S) := fun _ _ e ↦ h.1 (mod_cast e)
open AdicCompletion Submodule.Quotient LinearMap IsScalarTower Comparison LinearEquiv
abbrev IsBijOnCompletion (p : ℕ) (j : X →ₗ[W] E) := Bijective (map (span {↑p}) j)
section
omit [ThePrime p]
lemma IsBijOnCompletion.of_dvd_sub_of_pow_dvd {C} [CommRing C] [Algebra S C] (κ : B →ₐ[S] C) (h : ∀ y, ∃ x, ↑p ∣ y - κ x) (k : ∀ n x, (p : C) ^ n ∣ κ x → (p : B) ^ n ∣ x) : IsBijOnCompletion p κ.toLinearMap := by
  use fun _ _ e ↦ AdicCompletion.ext fun n ↦ Injective.of_ker
    (κ.toLinearMap.reduceModIdeal (span {(p : S)} ^ n)) ?_ (congrArg (·.1 n) e),
    map_surjective_of_mkQ_comp_surjective ?_ <;> rintro ⟨⟩ <;> simp_all [quot_mk_eq_mk, Submodule.Quotient.eq, span_singleton_pow, mem_span_singleton, dvd_sub_comm]
lemma isBijOnCompletion_completion : IsBijOnCompletion p (toAlgHom S B (PadicCompletion B p)).toLinearMap := .of_dvd_sub_of_pow_dvd _ (by simpa using! exists_approx · 1) fun _ _ ↦ pow_dvd_iff.1
lemma IsBijOnCompletion.linearMap_comp_bijective {j : X →ₗ[W] E} (h : IsBijOnCompletion p j) [Module W Y] [IsAdicComplete (span {(p : W)}) Y] : Bijective (· ∘ₗ j : (E →ₗ[W] Y) → _) := bijective_iff_has_inverse.2 ⟨fun g ↦ (ofLinearEquiv ..).symm.1 ∘ₗ (AdicCompletion.map _ g ∘ₗ (ofBijective _ h).symm.1).restrictScalars _ ∘ₗ of .., by
  constructor <;> intro <;> ext <;> simp [← map_of, ← AdicCompletion.map_comp_apply, symm_apply_eq]⟩
lemma IsReductionMod.comp_algebraMap {q : PadicCompletion B p →+ X} (h : IsReductionMod p q) : IsReductionMod p (q.comp (algebraMap B _).toAddMonoidHom) := ⟨h.1.forall.2 (exists_approx · 1 |>.imp (by simp_all [dvd_def, sub_eq_iff_eq_add, IsReductionMod, Exact])), (by simpa [h.2 _, dvd_def, eq_comm] using @pow_dvd_iff _ _ ↑p 1 ·)⟩
end
lemma FP.isBijective_of_isReductionMod {Θ : C ⥤ CommAlg W} (hN : FP N) (hW : IsCompleteTorsionFree W) (hS : IsCompleteTorsionFree S) (hΘ : ∀ A, IsCompleteTorsionFree (Θ.obj A)) [IsDomain W] [IsDiscreteValuationRing W] [Module.Flat W S] (h : Irreducible (p : W)) {X} (j : 𝟭 _ ⋙ asModules Θ ⋙ tensorWith S S ⟶ asModules X) (hf : ∀ n, Surjective ((p : S) • · : (pullₗ j (𝟙 N) n).ker → _) → Module.rank W (H N (moduleCoeff (asModules Θ)) n) < .aleph0) (hX : ∀ A, IsCompleteTorsionFree (X.obj A)) (hj : ∀ A {Y : Type} [AddCommGroup Y] (q : _ →+ Y), IsReductionMod p q → IsReductionMod p (q ∘ j.app A)) : (ofModuleHom _ j).IsBijective (𝟙 N) := by
  let q := (asModules X).whiskerLeft ({app _ := ↟(Submodule.mkQ _)} : 𝟭 _ ⟶ .mk _ (ofHom <| QuotSMulTop.map ↑p ·.1))
  have E {A} : IsReductionMod p (q A).1.toAddMonoidHom := ⟨Quot.exists_rep, by
    simpa [← Nat.cast_smul_eq_nsmul S] using! exact_lsmul_mkQ_smul_top _ _⟩
  use .of_mod (q := coeffMap (j ≫ q)) (q' := coeffMap q) (modShortExact_of_isReductionMod fun A ↦ ⟨fun _ _ e ↦ (hΘ A).isSMulRegular_natCast.lTensor S (mod_cast e), hj A _ E⟩)
    (modShortExact_of_isReductionMod (⟨hX · |>.1, E⟩)) rfl (.congr (.ofBijective _ (hN ..)) <| by
    simpa using IsDerivedComplete.baseChange h (.cohomology (hΘ · |>.isDerivedComplete) ..)
      hW.isDerivedComplete (mod_cast hS.isDerivedComplete) <| hf · ·)
    (.cohomology (hX · |>.isDerivedComplete) _) (IsCohomEquiv.of_isIso _).bij
variable (S p)
def algCompletion.of : 𝟭 _ ⟶ algCompletion S p := ⟨fun _ ↦ CommAlgCat.ofHom (toAlgHom ..), by delta algCompletion; aesop⟩
def moduleCompletion : ModuleCat S ⥤ ModuleCat S := .mk _ (ofHom <| .restrictScalars _ <| map (span {↑p}) ·.1)
instance : (moduleCompletion S p).Additive := ⟨hom_ext (map_ext'' _ rfl)⟩
def moduleCompletionIso : asModules (𝟭 _) ⋙ moduleCompletion S p ≅ asModules (algCompletion S p) := isoOfAppBijective (whiskerRight (whiskerRight (algCompletion.of ..) _) _) (isBijOnCompletion_completion (B := ·)) ≪≫ .symm (NatIso.ofComponents fun _ ↦ (@ofLinearEquiv _ _ _ _ _ _ (isAdicComplete_over_base _root_.isAdicComplete)).toModuleIso)
end
open CategoryTheory Limits PadicTest Perfection Equiv Function Algebra TensorProduct TimesBNat PreTilt SingleObj
lemma Function.Bijective.map_prod {S} [Ring S] {X Y Z : ModuleCat S} {f : X ⟶ Y} {g : X ⟶ Z} (b : Bijective fun x ↦ (f x, g x)) (U : _ ⥤ Type*) [PreservesFiniteProducts U] : Bijective fun x ↦ (U.map f x, U.map g x) := ((mapIsLimitOfPreservesOfIsLimit U _ _ ((Y.binaryProductLimitCone Z).2.ofPointIso (i := by rwa [ConcreteCategory.isIso_iff_bijective]
  ))).conePointUniqueUpToIso (Types.binaryProductLimit ..)).toEquiv.bijective
lemma bijective_prod_tilt {p} [ThePrime p] {c d d' : PadicTest} (f : c ⟶ d) (g : c ⟶ d') (b : Bijective fun x ↦ (f.1 x, g.1 x)) : Bijective fun x ↦ ((asModules tilt).map f x, (asModules _).map g x) := ((quotientMulEquiv ..).bijective_comp _).1 ((((ofBijective _ b.comp_left).trans (arrowProdEquivProdArrow ..)).subtypeEquiv (by simp [← b.1.eq_iff, forall_and])).trans (subtypeProdEquivProd.trans ((quotientMulEquiv ..).1.prodCongr (quotientMulEquiv ..).1))).bijective
section
variable (p S) [CommRing S] (K) [CommRing K] [Algebra S K] [ThePrime p] [Algebra Ainf S] {Ψ}
structure IsPeriodRingPair extends isCompleteTorsionFree : IsCompleteTorsionFree S where
  dvd_xi : ↑p ∣ algebraMap _ S xi
  isUnit_tau : IsUnit (algebraMap S K (algebraMap _ S tau))
variable {p S}
lemma isPeriodRingPair_OC : IsPeriodRingPair p OC ℂ_[p] := ⟨⟨.of_ne_zero NeZero.out, {}⟩, theta_xi ▸ by simp, by simp [RingHom.algebraMap_toAlgebra]⟩
lemma hasPartitions_periodAlg (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) : HasPartitions ringFunctor (moduleCoeff Ψ) := let e {R} := mk WittVector.coeff .mk'
  let θ := Functor.isoWhiskerRight
    ((_ ⋙ _ ⋙ algBaseChange S).isoWhiskerLeft (moduleCompletionIso ..)) _ ≪≫ θ
  have i {A} := (θ.symm.app A).toLinearEquiv.bijective
  ⟨exists_isIdemQuotient, fun f g b ↦ .map_prod ((Comparison.bijective_iff_of_comm_sq (by simp; tauto) i (i.prodMap i)).2 (((@id (Function.prod ((asModules (_ ⋙ wittFunctor)).2 f) ((asModules _).2 g)).Bijective (((arrowProdEquivProdArrow ..).trans (e.prodCongr e).symm).bijective.comp ((bijective_prod_tilt f g b).comp_left.comp e.bijective))).map_prod (tensorWith .. ⋙ forget _)).map_prod (moduleCompletion .. ⋙ tensorWith .. ⋙ forget _))) (forget _ ⋙ uliftFunctor)⟩
variable {K}
lemma IsPeriodRingPair.pFlat_smul_eq_zero (h : IsPeriodRingPair p S K) (x : OFlat ⊗[Ainf] S) : pFlat • x = 0 := (smul_def xi x).trans (by simpa [p_eq_zero_of_algebra_oFlat] using! (map_dvd includeRight h.2).mul_right x)
end
variable {p} [ThePrime p] {C} [Category C] (F : AbFunctor C) (ψ : C ⥤ CommAlg OC)
abbrev epsNonneg := epsPow.comp NNRat.coeHom.toAddMonoidHom.toMultiplicative
abbrev underlyingSet := forget (CommAlg OC) ⋙ uliftFunctor
def rootSystems : TimesBNat (CommAlg OC) ⥤ Type 1 := by refine ⟨(ULift <| _ →* ·.1), fun f ↦ ↾(⟨((algebraMap ..).1.comp (untilt.comp epsNonneg) * ·)^[f.2.toAdd] <| .comp f.1.hom ·.1⟩), ?_, ?_⟩ <;> intros <;> ext <;> simp [id_as_one, comp_as_mul, @toAdd_mul ℕ, pow_add]; ring
def rootSystems.atOne : rootSystems ⟶ fst _ ⋙ underlyingSet := ⟨fun _ ↦ ↾(⟨·.1 (.ofAdd 1)⟩), by
  intros; ext; simp [rootSystems]; erw [ULift.up_inj, MonoidHom.mul_apply]; aesop⟩
abbrev rootSystemsAt {A} y := fibreProd ((ψ.prod (𝟭 _)).whiskerLeft rootSystems.atOne) ((fst C).whiskerLeft (@pointMap _ _ (ψ ⋙ _) A y))
abbrev RootSystemsAreLines := ∀ A (y : (ψ ⋙ underlyingSet) A), IsUnit y.1 → IsLine F (Y := rootSystemsAt ψ y) (fibreProd.snd ..)
end
noncomputable section
open CategoryTheory CommAlgCat Ideal Quotient Nat Function Algebra TensorProduct Perfection WittVector IsScalarTower nonZeroDivisors AlgHom DFunLike
variable {p} [hp : ThePrime p] {S T} [CommRing S] [CommRing T] [Algebra S T] {x M} [CommMonoid M] [PerfectRing M p] (h : IsCompleteTorsionFree S) (E : CrysTest S)
def frobModPd [Fact ¬IsUnit (p : S)] : S ⧸ pdIdeal S →+* ModP S p := lift _ (.comp (frobenius ..) (mk _)) fun _ h ↦ (eq_zero_iff_dvd ..).2 ((dvd_factorial Fin.pos' .refl).natCast.trans (h p))
include h
lemma IsCompleteTorsionFree.p_mem_pdIdeal : ↑p ∈ pdIdeal S := fun n ↦ (coprime_ordCompl hp.out n.factorial_ne_zero).cast.elim fun a ⟨b, _⟩ ↦ ((mem_jacobson_bot.1 (h.2.le_jacobson_bot _ (subset_span rfl)) (-a)).dvd_mul_right.1 ⟨b, by grind [congr(($(ordProj_mul_ordCompl_eq_self n ! p) : S)), factorization_def, hp.out]⟩).trans (pow_dvd_pow _ (padicValNat_factorial_le p n))
lemma IsCompleteTorsionFree.isLocalHom_pdQuotientMk : IsLocalHom (pdQuotientMk S) := isLocalHom_of_le_jacobson_bot _ fun _ y ↦ isRadical_jacobson _ ⟨p, h.2.le_jacobson_bot _ (mem_span_singleton.2 ((dvd_factorial Fin.pos' .refl).natCast.trans (y p)))⟩
lemma IsCompleteTorsionFree.monoidHom_lift_bijective : Bijective ((pdQuotientMk S).1.comp : (M →* S) → _) := by
  have := h.2
  nontriviality S using bijective_iff_existsUnique, ExistsUnique, ext_iff
  refine ((liftMonoidHom ..).1.symm.bijective_comp _).1 (((quotientMulEquiv p _).monoidHomCongrRightEquiv.trans (liftMonoidHom ..).1.symm).trans ⟨(factor (by simp [h.p_mem_pdIdeal])).1.comp, (frobModPd.1.comp <| ·.comp (powMulEquiv M p).symm), ?_, ?_⟩).bijective <;> intro x <;> ext m <;> rw [← powMulEquiv_symm_pow_p _ p m, x.map_pow] <;> simp <;> rcases x _ <;> rfl
lemma IsCompleteTorsionFree.existsUnique_witt_lift {b} [CommRing b] [PerfectRing b p] (e : (p : b) = 0) (f : b →+* _) : ∃! g : WittVector p b →+* S, ∀ x, pdQuotientMk S (g x) = f (x.coeff 0) := have := h.2; by
    by_cases! Subsingleton S
    · use .mk' 1 ?_ <;> aesop_cat
    have := @CharP.of_eq_zero _ _ (frobModPd.comp f).domain_nontrivial _ hp.out e
    exact .imp (fun _ a ↦ ⟨a, fun _ e ↦ witt_hom_ext (congr($(@h.monoidHom_lift_bijective.1 (.comp ..) (.comp ..) (by aesop)) ·))⟩)
      ⟨(fontaineTheta ..).comp (map ((pthRoot ..).comp (lift _ _ _ (frobModPd.comp f)))), fun x ↦ congr(factor (by simp [h.p_mem_pdIdeal]) $(mk_fontaineTheta _)).trans ((by rcases f _; rfl : factor _ (frobModPd _) = f _ ^ p).trans (by simp [← f.map_pow]))⟩
omit h
omit [ThePrime p] in
lemma IsBijOnCompletion.comp_bijective {C W X : CommAlg S} (κ : C ⟶ W) (c : IsBijOnCompletion p κ.hom.toLinearMap) (d : IsAdicComplete (span {(p : X)}) X) : Bijective (κ ≫ · : (W ⟶ X) → _) := have := isAdicComplete_over_base (S := S) d
  ⟨fun _ _ e ↦ hom_ext (toLinearMap_injective (c.linearMap_comp_bijective.1 congr($e.1))), (c.linearMap_comp_bijective.2 ·.1.toLinearMap |>.elim fun G e ↦ have m x := @c.linearMap_comp_bijective.1 (G ∘ₗ .mulLeft _ x) (G x • G); by simp [ext_iff] at *; use ofHom (.ofLinearMap G (by grind [e 1]) (m · fun t ↦ by rw [mul_comm, m, mul_comm]; simp_all [← map_mul])), by bound)⟩
instance : CoeSort (CrysTest S) Type := ⟨(·.1)⟩
instance : HasUniqueDiv E := ⟨fun n a _ _ _ ↦ E.2.1.pow n ((E.2.p_mem_pdIdeal n).elim (by grind [congr(($(mul_factorial_pred a) : E))]))⟩
lemma CrysTest.p_eq_zero_mod_pdIdeal : (p : _ ⧸ pdIdeal E) = 0 := eq_zero_iff_mem.2 E.2.p_mem_pdIdeal
variable (S) (J : Set T)
def preEnvelope := adjoin T {(x ^ n) ⊗ₜ[ℤ] (n ! : ℚ)⁻¹ | (x ∈ J) (n)}
abbrev Envelope : CrysTest S := ⟨.of S (PadicCompletion (preEnvelope J) p), isCompleteTorsionFree_completion fun _ _ h ↦ Subtype.ext (((isUnit_of_invertible ↑p).map includeRight).mul_left_cancel (by simpa using congr($h.1)))⟩
lemma Envelope.existsUnique_lift {B} h (hJ : ∀ x ∈ J, h x ∈ pdIdeal _) : ∃! g : Envelope S J ⟶ B, g.1.hom.comp (toAlgHom ..) = h := let := h.1.toAlgebra
  let F := (AlgEquiv.ofInjective _ (includeLeft_injective Int.cast_injective)).symm.toAlgHom.comp
    ((Subalgebra.inclusion (by exact Subalgebra.map_le.2 (adjoin_le fun y ⟨x, hx, n, e⟩ ↦ (hJ x hx n).imp fun c hc ↦ by simpa [← e, ← hc] using! (smul_tmul n ! c (n ! : ℚ)⁻¹).symm))).comp (subalgebraMap (preEnvelope J) (rTensor ℚ (ofId ..))))
  ((isBijOnCompletion_completion.comp_bijective (ofHom _) B.2.2).existsUnique (ofHom (F.restrictScalars S))).elim fun G e H ↦
    ⟨⟨G⟩, ext (F.2 · ▸ congr($e _)), fun ⟨G⟩ e ↦ H G (hom_ext (ext fun x ↦ (IsLocalizedModule.surj ℤ⁰ (toAlgHom ℤ T _).toLinearMap x.1).elim fun ⟨t, n⟩ c ↦ zsmul_right_injective (coe_ne_zero n) (by simpa [↓← map_zsmul, (Subtype.ext c : n.1 • x = ofId T _ t)] using! congr($e t)))) ▸ rfl⟩
lemma Envelope.algebraMap_mem_pdIdeal (hx : x ∈ J) : algebraMap T (Envelope S J) x ∈ pdIdeal _ := pdIdeal_le_comap (algebraMap (preEnvelope J) _) (⟨⟨_, subset_adjoin ⟨x, hx, ·, rfl⟩⟩, by ext; simp [natCast_def']⟩)
lemma powers_le_comap_powers (p : ℕ) {A B} [CommRing A] [CommRing B] (f : A →+* B) : .powers p ≤ (Submonoid.powers ↑p).comap f := by simp [Submonoid.powers_le]
abbrev PadicTest.GenericRing {p} [ThePrime p] (c : PadicTest) := Localization.Away (p : c.ProdRing)
lemma PadicTest.eq_zero_of_algebraMap_genericRing {p} [ThePrime p] (c : PadicTest) x (e : algebraMap c.ProdRing c.GenericRing x = 0) : x = 0 := (IsLocalization.Away.exists_of_eq _ (by simpa)).elim (c.isLeftRegular_p.pow · ·)
end
section
open Module Submodule Nat Polynomial Function Set Algebra LinearMap TensorProduct algebraMap
variable {p} [ThePrime p] {A} [CommRing A] (B : CrysTest A) {T I} [CommRing T] [Algebra B T]
lemma exists_preEnvelope_basis z (b : Basis _ B T) (u : I → T) {v} {t : B} (hb : ∀ a n, b (a, n) = u a * v ^ n) (q : t - v = z) : ∃ (y : ℕ → preEnvelope {z}) (b : Basis _ B _), (∀ a n, b (a, n) = u a * y n) ∧ ∀ n, z ^ n = n ! * y n := let F := b.constr B fun j ↦ u j.1 * z ^ j.2
  let c := b.map (.ofInvolutive F (congr($((b.ext fun (a, n) ↦ by
    have h w := by simpa using congr(mulLeft B (u a) $(((C t - X) ^ n :).aeval_eq_sum_range w))
    simp [F, h, ← hb, ← h, ← q] : F * F = 1)) ·)))
  let y n : preEnvelope {z} := ⟨_, subset_adjoin ⟨z, rfl, n, rfl⟩⟩
  have e j : c j = _ := b.constr_basis B ..
  have H n := by ext; simp [y, natCast_def']
  ⟨y, _, Prod.forall'.1 (Basis.mk_apply (linearIndependent_iff'.2 fun s g h i hi ↦ includeLeft_injective (S := ℤ) Int.cast_injective (by
    simpa [y, ← e, Finsupp.single_apply, hi, ite_tmul, smul_tmul', natCast_def', -map_smul] using
      congr(AlgebraTensorModule.rTensor ℤ ℚ (c.coord i) ($h) * i.2 !))) (by
  erw [← restrictScalars_top _ T, ← top_toSubmodule, ← adjoin_adjoin_coe_preimage, adjoin_eq_span, ← span_smul_of_span_eq_top c.span_eq, span_le, smul_subset_iff, forall_mem_range]
  intro j x hx; simpa [*, smul_def'] using Submonoid.closure_induction_left (by
    simp [← nsmul_eq_mul, nsmul_mem, mem_span_of_mem]) (fun x ⟨_, rfl, m, h⟩ w _ i n c ↦ by
    convert i (n + m) (c * (n + m).choose n) using 1; ext
    simp [← h, y, ← mul_assoc, pow_add, cast_add_choose, natCast_def']; field_simp) hx j.2 j.2 !)), H⟩
lemma koszulExact_pd_line {K} [CommRing K] [Algebra A K] (E : CrysTest A) [Algebra B E] [IsScalarTower A B E] [Zero I] {b : Basis _ B T} {j : T →ₗ[B] E} (J : IsBijOnCompletion p j) {u : I → E} {y : ℕ → E} {v t q} (hb : ∀ a n, j (b (a, n)) = u a * y n) (hy : ∀ n, (algebraMap B E t - v) ^ n = n ! * y n) (hr : IsUnit v) (ha : u 0 = 1) (hδ : p.cast ^ 3 ∣ q) (hq : IsUnit (algebraMap A K q)) (γ : E →ₐ[B] E) (hv : γ v = (q + 1) • v) (hu : ∀ a ≠ 0, ∃ η : A, γ (u a) = (η + 1) • u a ∧ p * η ∣ q) : KoszulExact (ULift.map.{0, _, 1, 1} (((Algebra.linearMap B E).restrictScalars A).baseChange K)) (.map ((γ.toLinearMap.restrictScalars A).baseChange K)) := by
  choose! η hu c hη using hu
  obtain ⟨⟨d, a⟩, _, _, e⟩ := hδ, isAdicComplete_over_base (S := B) E.2.2,
    B.2.2, by simpa using (hy 0).symm
  let s := -p ^ 2 * d • v
  choose w hw using fun n ↦ show ∃ w, γ (y n.succ) = y n.succ - q • v * (y n + p • w) from
    ((pdIdeal _).add_mem (pdIdeal_le_comap C (⟨_, hy ·⟩)) (smul_mem _ X (pdIdeal_le_comap C E.2.p_mem_pdIdeal)) n.succ).elim fun P h ↦
    (P.binomExpansion 0 s).rec fun k e ↦ ⟨-d • v * k, nsmul_right_injective n.succ.factorial_ne_zero (by linear_combination (norm := (simp [*, s, ↓map_pow, derivative_pow, factorial]; algebra)) n.succ ! * e + congr(eval s $h - eval 0 $h - s * (derivative $h).eval 0 - γ $(hy n.succ)))⟩
  choose F f using (J.linearMap_comp_bijective (Y := E).2 <| b.constr ℕ ·); choose κ k using
    J.linearMap_comp_bijective.2 (b.coord (0, 0))
  simp [DFunLike.ext_iff] at f k; let m := Algebra.linearMap B E
  let S := F fun i@(a, n) ↦ ite (a = 0) (-y n.succ) (p * c a • v * j (b i))
  let L W : End B E := v • (1 - (p : B) • W)
  let W := -F fun (a, n) ↦ ite (a = 0) (w n) (c a • γ (u a) * (y n - γ v * n.casesOn 0 (y + p • w)))
  have ⟨⟨h₃, h₄⟩, h₁, h₂⟩ : (γ.toLinearMap ∘ₗ m = m ∧ κ ∘ₗ m = .id) ∧ γ.toLinearMap ∘ₗ S + -S = q •
    L W ∧ q • (m ∘ₗ (t • κ) + -L 0) = S ∘ₗ F fun i@(a, n) ↦ ite (a = 0) (-q • j ((n + 1 : B) • b i - n.casesOn 0 (t • b ⟨a, ·⟩))) (-η a • j (b i)) := ⟨by simpa [*, m, LinearMap.ext_ring_iff]
    using (k (b (0, 0))), by constructor <;> exact J.linearMap_comp_bijective.1 (b.ext fun (a, n) ↦ nsmul_right_injective n.factorial_ne_zero (by
    have := (by simpa [factorial] using hy n.succ); cases n <;> simp +zetaDelta [f, k, apply_ite (F _)] <;> split <;> simp [*, hη a, smul_def'] <;> grind))⟩
  have H W := hq.smul_bijective.comp (f := ((L W).restrictScalars A).baseChange K)
    (TensorProduct.map_bijective (f := 1) bijective_id (hr.smul_bijective.comp ⟨fun x z e ↦ congrFun (@E.2.isDerivedComplete.1 (W^[·] x) (W^[·] z) (funext (by simpa [shiftDiff, ← End.pow_apply, pow_add] using (congr(W^[·] $e))))) 0, E.2.isDerivedComplete.exists_eq_of_approx E.2.isDerivedComplete _ _ fun x ↦ ⟨x, W x, by simp⟩⟩))
  apply_fun (·.restrictScalars A |>.baseChange K) at h₁ h₂ h₃ h₄
  simp [KoszulExact, subset_def, IsFixedPt, Surjective, baseChange_comp, LinearMap.ext_iff, ← ULift.down_inj] at *
  use LeftInverse.injective h₄, (H 0).2.forall.2 fun x e ↦ ⟨q • _, by
    simpa [add_neg_eq_zero] using (h₂ x).trans (congrArg _ (@(H W).1 _ 0 (by
    simp [← h₁, ← h₂, h₃, by simpa using e])))⟩, (H W).2.forall.2 (⟨_, h₁ ·⟩)
end
open CategoryTheory TensorProduct Function Functor Module LinearMap AlgebraTensorModule Lift WittVector AdicCompletion Submodule ModuleCat Comparison AddCommGrpCat
lemma CoeffCompBij.periodAlg_of_almostCoeff {C C'} [Category C] [Category C'] {p} [ThePrime p] {N : AbFunctor C} {N' : AbFunctor C'} {φ} {α : N' ⟶ φ ⋙ N} (hN : FP N) {S K} [CommRing S] [Algebra Ainf S] [CommRing K] [Algebra S K] [Flat S K] (hK : IsPeriodRingPair p S K) {ψ ψ'} {β : φ ⋙ ψ ⟶ ψ'} (hN' : ∀ G : _ ⥤ ModuleCat S, AllBijective (baseChangeMap K K N' (ψ' ⋙ G) ·)) (h : ∀ A, IsPerfectTorsionFree (ψ A)) (h' : ∀ A, IsPerfectTorsionFree (ψ' A)) (H : CoeffCompBij β α (almostCoeff (OFlat ⊗[Ainf] S))) : CoeffCompBij β α (asModules (periodAlg S) ⋙ tensorWith K K) := by
  have ⟨w, z, _⟩ := witt_reduction_spec OFlat OFlat
  let c : wittMaxIdeal →ₗ[Ainf] MaxIdealFlat := (Algebra.linearMap ..).restrict (q := (IsLocalRing.maximalIdeal _).restrictScalars _) fun _ ↦ (mem_wittMaxIdeal.1 · 0)
  have hc : IsReductionMod p c := ⟨(⟨⟨_, teichmuller_mem_wittMaxIdeal ·.2⟩, rfl⟩), fun _ ↦ by
    erw [Subtype.ext_iff, w.2]; simp [Subtype.ext_iff]; aesop (add simp [wittMaxIdeal, p_nonzero])⟩
  let P := asModules (wittFunctor (k := OFlat)) ⋙ tensorWith S (S ⊗[Ainf] wittMaxIdeal); let Q :=
    moduleCompletion S p
  have := CompatibleSMul.of_algebraMap_surjective (OFlat ⊗[Ainf] S) MaxIdealFlat w.1
  let E (b : CommAlg OFlat) :=
    .ofBijective _ ((hc.lTensor _).bijective_rTensor _ (by simp [p_eq_zero_of_algebra_oFlat])) ≪≫ₗ
    TensorProduct.comm .. ≪≫ₗ ((cancelBaseChange _ _ OFlat ..).symm ≪≫ₗ .lTensor b ((assoc _ _ _ _ S _).symm ≪≫ₗ equivOfCompatibleSMul OFlat ..)).restrictScalars _
  let e b : P b →+ _ := ((E b).1 ∘ₗ (wittConstCoeff b).lTensor _).toAddMonoidHom
  let q : P ⋙ Q ⋙ forget₂ .. ⟶ almostCoeff _ ⋙ forget₂ .. := ⟨fun b ↦ ofHom (.comp (QuotientAddGroup.lift _ (e b) (by simp [p_eq_zero_of_algebra_oFlat, ↓IsConcreteLE.le_iff, ↓mem_toAddSubgroup, ↓nsmulRange.mem_span_pow_smul_top_iff, ← Nat.cast_smul_eq_nsmul OFlat])) (AdicCompletion.eval _ _ 1).toAddMonoidHom), fun _ _ f ↦ ConcreteCategory.coe_ext (map_ext _ (DFunLike.congr_fun (tmul_ext : (e _).comp (P.2 f).1.toAddMonoidHom = .comp _ (e _)) <| · 1))⟩
  have m {D} [Category D] {ψ : D ⥤ _} (h : ∀ A, IsPerfectTorsionFree (ψ A)) :=
    modShortExact_of_isReductionMod (Φ := ψ ⋙ P ⋙ Q) (q := ψ.whiskerLeft q) fun A ↦ have := (h A).1; ((witt_reduction_spec OFlat _).1.lTensor _).elim
    fun k l ↦ ⟨isSMulRegular_completion (isSMulRegular_tensor_witt (isSMulRegular_tensor_of_flat_mod c w hc (z.1.submodule (wittMaxIdeal.restrictScalars _) _) hK.regular) (h A)), .of_comp (g := of _ _) ((E _).surjective.comp k), fun y : AdicCompletion .. ↦ (mkQ_surjective _ (y.1 1)).elim fun x a ↦ congr(Quot.lift _ _ $a.symm = 0).to_iff.trans ((E _).map_eq_zero_iff.trans ((l x).trans (by simpa [↓nsmulRange.mem_span_pow_smul_top_iff, ← a] using! (congr(y ∈ $(pow_smul_top_eq_ker_eval (n := 1) (fg_span_singleton _)))).symm)))⟩
  let v b : _ ⟶ P b := ↟(rTensor _ _ (toSpanSingleton _ _ (1 ⊗ₜ ⟨_, toWittResidue_tau⟩)))
  have t {X Y} f (g : Y ⟶ X) (h : g ≫ f = algebraMap _ S tau • 𝟙 Y) :
      Bijective ((Q ⋙ tensorWith K K).2 g ≫ (Q ⋙ _).2 f) := by
    rw [← Functor.map_comp, h, Q.comp_map, (rfl : Q.2 _ = (_ : S) • 𝟙 _)]
    simpa [tensorWith] using! hK.isUnit_tau.smul_bijective (β := K ⊗[S] Q Y)
  let γ := isoWhiskerRight (isoOfAppBijective (whiskerRight (⟨fun _ ↦ ↟(rTensor _ _ (liftBaseChange S (wittMaxIdeal.subtype.smulRight 1))), fun _ _ _ ↦ hom_ext tmul_ext⟩ : P ⟶ asModules (wittFunctor ⋙ algBaseChange S)) (Q ⋙ tensorWith ..)) (fun b ↦ ⟨.of_comp (t (v b) _ (by
    dsimp [P, tensorWith]; ext ⟨⟩; exact congr($(by simp [← tmul_smul, mul_comm]; rfl) ⊗ₜ _))).1, .of_comp (t _ (v b) (by ext; exact congr($(by simp [Algebra.smul_def]) ⊗ₜ _))).2⟩) ≪≫ (_ ⋙ algBaseChange S).isoWhiskerLeft (isoWhiskerRight (moduleCompletionIso ..) _)) (moduleCoeff (𝟭 _))
  refine (isBijective_iff_of_coeff_iso (c := ⟨φ, _⟩) (ψ.whiskerLeft γ.1) _ (whiskerLeft_comp_whiskerRight β γ.1)).1 (((.of_mod (m h) (m h') (by ext; exact congr(⟨$(q.2 _) _⟩)) (fun _ _ ↦ ?_) ?_ H : CoeffCompBij β α (P ⋙ Q)).baseChangeMap_bijective_iff hN).1 (hN' _)) <;> apply IsDerivedComplete.cohomology
    fun _ ↦ .of_isAdicComplete (AdicCompletion.isAdicComplete (fg_span_singleton _))
