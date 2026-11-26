import Lib.PadicHodge.WachGamma.KisinModuleDefs
noncomputable section
section
open Finset Algebra Module Set Submodule WittVector Lift.FrobGroup
variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : Lift.KummerChart Γ} {O} {L L' : Lift.KummerChart.JumpLattice O} {l a b : ℕ} {i i' : Lift.KummerChart.Letter} {n : ℤ} {x : L.Ambient} (g : k.galMonoid) (F : L.Hom L') (m : Lift.FrobGroup Γ) {μ : L.Functional}
namespace Lift.KummerChart.JumpLattice
attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule
attribute [-simp] Algebra.toRingHom_ofId map_one pow_eq_one_iff smul_right_inj
attribute [local simp] frobGroup_smul_smul Nat.cast_smul_eq_nsmul invOf_smul_eq_iff smul_pow
@[simp] lemma Hom.b3 : ∀ x, F.wittMap (m • x) = m • F.wittMap x := diagTensor_induction (by simp [F.isIntertwining])
lemma wittMap_mem_ainfLattice F : x ∈ L.ainfLattice → L.wittMap L' F x ∈ L'.ainfLattice := (mapsTo_span (f := (wittMap ..).restrictScalars _) (by simp) ·)
lemma Hom.comp_wittMap_mem_forms {μ} : μ ∈ L'.forms → μ ∘ₗ F.wittMap ∈ L.forms := by simp_all [forms, F.isIntertwining]
lemma Hom.map_mem_kisinAinf : x ∈ L.kisinAinf → F.wittMap x ∈ L'.kisinAinf := .imp (.imp fun _ ↦ .imp_right (by simpa using wittMap_mem_ainfLattice _ ·)) fun H n _ ↦ F.b3 .. ▸ H n _ ∘ F.comp_wittMap_mem_forms
lemma Hom.wittMap_mem_frobKisinAinf : x ∈ L.frobKisinAinf l → F.wittMap x ∈ L'.frobKisinAinf l := (F.b3 .. ▸ F.map_mem_kisinAinf · :)
@[simp] lemma d3 n a t : (L.letterOp i ^ n) (no_index (.mk a t)) = k.letterTeich i⁻¹ ^ n • .mk a
  (O.ζ.1 ^ n • t) := by induction n <;> simp_all [letterOp, pow_succ', mulZeta, smul_smul, mul_comm]
lemma mem_letterPart_iff_mulZeta : x ∈ letterPart i ↔ L.mulZeta.wittMap x = k.letterTeich i • x := sub_eq_zero.trans (inv_smul_eq_iff (g := k.letterTeich.toHomUnits i))
lemma S_smul (s : k.S) : s • x = s.1 • x := rfl
@[simp] lemma Hom.wittMap_letterProj : ∀ x, F.wittMap (L.letterProj i x) = L'.letterProj i (F.wittMap x) := diagTensor_induction (by simp [letterProj])
lemma smul_letterProj {m : FrobGroup Γ} (h : m • (k.letterTeich i⁻¹).1 = k.letterTeich i'⁻¹) : ∀ x, m • L.letterProj i x = L.letterProj i' (m • x) := diagTensor_induction (by simp_all [letterProj, smul_comm m, smul_sum, S_smul])
lemma gal_smul_letterProj : ∀ x, g.1 • L.letterProj i x = L.letterProj i (g.1 • x) := smul_letterProj (g.2.choose_spec ▸ (fixes _).1 _)
lemma phi_pow_smul_letterTeich : φ ^ l • (letterTeich i⁻¹).1 = letterTeich ((letterFrob ^ l) i)⁻¹ := by erw [phi_pow_smul, k.letterFrob.coe_pow, pow_iterate, map_pow, k.S.coe_pow, Subtype.coe_mk, map_teichmuller]; simp
lemma letterProj_mem_letterPart : L.letterProj i x ∈ letterPart i := (diagTensor_induction (by simp [letterProj, mul_geom_sum, ← map_pow, by
  simpa using O.ζ.2, map_one]) : ∀ x, ((_ - 1) * L.letterProj i) x = 0) x
lemma mem_letterPart_iff_letterProj : x ∈ letterPart i ↔ L.letterProj i x = x := ⟨by simp_all
  [letterProj, End.pow_apply, letterPart, Function.iterate_fixed], (· ▸ letterProj_mem_letterPart)⟩
lemma gal_smul_mem_letterPart : g • x ∈ letterPart i ↔ x ∈ letterPart i := by simp [mem_letterPart_iff_letterProj, k.galMonoid.smul_def, ← gal_smul_letterProj, smul_left_cancel_iff]
lemma phi_pow_smul_mem_letterPart_iff : φ ^ a • x ∈ letterPart i ↔ x ∈ letterPart (i.stepBack a) := by simp [mem_letterPart_iff_letterProj, ← Equiv.apply_symm_apply .. ▸ smul_letterProj phi_pow_smul_letterTeich, smul_left_cancel_iff]
lemma frobKisinAinf_zero : L.frobKisinAinf 0 = kisinAinf := Submodule.ext (by simp [frobKisinAinf])
lemma frobEUnit_pow_smul n : k.frobEUnit a ^ n • x = (k.frobE a).1 ^ n • x := by simp [Units.smul_def, frobEUnit, ← map_pow]
lemma finrank_wittFq [ThePrime b] {f} : finrank ℤ_[b] (WittFq f) = f := by simpa [Nat.pow_right_inj Fact.out] using (congrArg (·.index) (AddSubgroup.ext (H := pPowMultiples (WittFq f) 1) (by simp [mem_span_singleton, mul_comm]))).trans (Nat.card_congr quotientPEquiv.1)
lemma zTauUnit_smul : k.zTauUnit • x = k.zTau • x := rfl
@[simp] lemma frobEUnit_smul : k.frobEUnit a • x = (k.frobE a).1 • x := rfl
def basisValues : L.Functional →ₗ[BdR] Fin (finrank ℤ_[p] L.Carrier) → BdR := .pi fun l ↦ .applyₗ' _ (.mk 1 (finBasis _ _ l))
lemma ainfLattice_eq_span_basis : L.ainfLattice = span _ (.range (DiagTensor.mk 1 ∘ finBasis ℤ_[p]
  _)) := .trans (by simp [range_comp]; rfl) (span_span_of_tower ℤ_[p] ..)
lemma apply_eq_of_mem_fracSpan (f f' : L.Functional) (h : basisValues f = basisValues f') : x ∈ fracSpan → f x = f' x := fun ⟨_, a, e⟩ ↦ by
  simpa [smul_right_inj, by simpa using a] using f.eqOn_span (by simpa) (ainfLattice_eq_span_basis.le e)
@[simp] lemma d9 {r : Ainf} (g : Γ) : inr g • r = toGp g • r := rfl
@[simps] def conjForm (μ : L.Functional) (g : Γ) : L.Functional := ⟨⟨fun x ↦ (toGp g)⁻¹ • μ (inr g • x), by simp⟩, by simp [smul_distrib_smul]⟩
lemma form_gal_smul (hμ : μ ∈ L.forms) (hx : x ∈ fracSpan) : μ (g • x) = g • μ x := have ⟨_, _, rfl⟩ := g
  inv_smul_eq_iff.1
    (apply_eq_of_mem_fracSpan (conjForm ..) _ (funext (by simp [basisValues, hμ _])) hx)
lemma smul_mem_ainfLattice : x ∈ ainfLattice → m • x ∈ ainfLattice := (mapsTo_span (f := semilinearAct m) (by simp) ·)
lemma smul_mem_fracSpan : x ∈ fracSpan → m • x ∈ fracSpan := .imp' (m • ·) (by simp_all [smul_eq_zero_iff_eq, ← frobGroup_smul_smul, smul_mem_ainfLattice])
lemma valueAt_frobEUnit_zpow_smul : ∀ x, valueAt a μ (k.frobEUnit b ^ n • x) = phiInvToBdR a (k.frobE b) ^ n * valueAt a μ x := (MulAction.surjective
  (k.frobEUnit b ^ (-n).toNat)).forall.2 (by cases n <;> simp [↓smul_smul, frobEUnit_pow_smul])
lemma mk_one_mem_ainfLattice t : no_index (.mk 1 t) ∈ L.ainfLattice := subset_span ⟨t, rfl⟩
lemma letterProj_mk_mem_ainfLattice t : L.letterProj i (.mk 1 t) ∈ ainfLattice := by simp (maxDischargeDepth := 4) [letterProj, sum_mem, smul_of_tower_mem, mk_one_mem_ainfLattice]
lemma comp_letterProj_mem_forms (h : μ ∈ L.forms) : μ ∘ₗ L.letterProj i ∈ L.forms := fun t g ↦ by
  erw [← form_gal_smul ⟨_, g, rfl⟩ h (le_saturateBy (letterProj_mk_mem_ainfLattice t)), gal_smul_letterProj]; simp
lemma valueAt_comp_wittMap {μ} : valueAt a (μ ∘ₗ F.wittMap) x = valueAt a μ (F.wittMap x) := by simp [valueAt]
lemma sum_letterProj x : ∑ i, L.letterProj i x = x := by
  simp [letterProj, letterOp, ← smul_sum]
  rw [sum_comm, sum_eq_single 0 fun n a b ↦ by erw [← sum_smul, sum_hom_units_eq_zero (k.letterTeich.comp invMonoidHom ^ n) fun e ↦ (exists_pow_ne_one_of_isCyclic b (by aesop)).rec
    fun x : Letter ↦ (· (Units.ext (by simpa [letterTeich, RingHom.algebraMap_toAlgebra, ← map_pow] using! congr(($e x⁻¹).1.1 0)))), zero_smul]] <;> simp
lemma exists_span_formsOfType_mod_pred i u : ∃ r ≤ L.jumpMultiplicity i u, ∃ ν : Fin r → L.formsOfType i u, ∀ μ ∈ L.formsOfType i u, ∃ c : _ → PadicAlgCl p, μ - ∑ m, c m • (ν m).1 ∈ formsOfType i (u - 1) := by
  choose a ha using fun μ : L.formsOfType i u ↦ (mem_span_singleton.1 <| μ.2.2 ·); have A {μ t z y} h (e : thetaBdR y = z := by simp +zetaDelta [smul_def']) := (congrArg _ ((smul_left_inj NeZero.out).1 ((ha μ t).trans h))).trans e; let f μ : L.Carrier →ₛₗ[(ofId ℤ_[p] ℂ_[p] : ℤ_[p] →+* ℂ_[p])] _ := ⟨⟨thetaBdR ∘ a μ, fun _ _ ↦ A (by simp [add_smul, ← ha]) (map_add ..)⟩, fun c t ↦ A (y := c • a μ t) (by simp [← ha])⟩; have G μ t (g : k.Γ') : f μ (L.ρ g t) = (χ g ^ (-u)).1 • toGp g • f μ t := A (by erw [comp_letterProj_mem_forms μ.2.1, ← ha, smul_distrib_smul, y6, smul_comm, ← smul_assoc]); choose _ ν hs' li using exists_fun_fin_finrank_span_eq ℂ_[p] (.range f); choose ν eν using ν; refine ⟨_, L.inClass.isPotCrys.sum_jump_eq_jump_overZp.2 _ _ _ _ (forall_mem_range.2 fun μ ↦ ⟨(nearOne_le <| G μ ·), fun t ↦ A (by erw [← mulZeta.wittMap_letterProj (.mk 1 t), mem_letterPart_iff_mulZeta.1 letterProj_mem_letterPart, μ.1.map_smul, ← ha, ← smul_assoc])⟩), ν, SetCoe.forall'.2 fun μ ↦ ?_⟩; obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun _).1 (hs'.ge (subset_span ⟨μ, rfl⟩))
  choose c' K e' using fun m ↦ (z7 k.Γ').1 fun g ↦ (li.eq_coords_of_eq (g := toGp g • c) (LinearMap.ext ((L.ρ.apply_bijective g).2.forall.2 (by
    simpa [← hc, ← eν, G, smul_sum] using G μ · g))) m).symm
  use c', fun t g ↦ by simp_all [μ.2.1 t, (ν _).2.1 t, smul_sub, smul_sum, smul_def'], fun t ↦ by
    simpa [← ha, ↓← smul_def', sub_smul, sum_smul] using! mul_mem_hodgeFil (n := -u)
      (algebraMap_mem_hodgeFil_one_iff (y := a μ t - ∑ m, c' m • a _ t).2 (by simpa [← eν, e', smul_def'] using! congr($hc.symm t))) (subset_span rfl)
lemma formsOfType_subset_pred_of_notMem (h : n ∉ L.U i) : L.formsOfType i n ⊆ L.formsOfType i (n - 1) := (L.exists_span_formsOfType_mod_pred i n).elim
  (by rw [jumpMultiplicity, sum_eq_zero (by grind [InClass, JumpLattice])]; aesop)
end Lift.KummerChart.JumpLattice
end
section
open Algebra Algebra.TensorProduct Module _root_.TensorProduct FaithfulSMul Finset LinearMap Matrix MulSemiringAction Pointwise Submodule algebraMap Lift.Chart
namespace Lift.KummerChart.JumpLattice
attribute [-instance] Bialgebra.toAlgebra NormedAlgebra.toAlgebra NormedSpace.toModule
variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {L : JumpLattice O}
lemma exists_functional_extend (f : _ →ₗ[ℤ_[p]] BdR) : ∃ μ : L.Functional, ∀ t, μ (.mk 1 t) = f t := (exists_extend_of_notMem (p := ⊥) 0 (@NeZero.one _ _ (by
  apply_rules [nontrivial_of_algebraMap_injective_of_isDomain, algebraMap_injective])).1 f).rec
  fun Ψ h ↦ ⟨AlgebraTensorModule.lift ((liftBaseChangeEquiv BdR).2 Ψ), by bound⟩
attribute [-simp] LinearMap.map_smul_of_tower map_one map_smul
attribute [local simp ←] IsScalarTower.algebraMap_apply
attribute [local simp] Fintype.linearCombination_apply Function.comp_def S_smul basisValues frobGroup_smul_smul phiInvToBdR mulVec vecMul MonoidHom.map_one Prod.mk_one_one RingHom.map_one mul_smul dotProduct
lemma equivariant_iff_basisValues {μ g A μ'} (hA : IsUnit A) (H : (repMatrix L.ρ (finBasis ..) g).map (↑) * A.map (toGp g • ·) = A) : (∀ t, μ' (.mk 1 (L.ρ g t)) = toGp g • μ (.mk 1 t)) ↔ basisValues μ' ᵥ* A = toGp g • basisValues μ ᵥ* A := by
  erw [(funext ((toRingHom ..).map_vecMul A _) : toGp g • _ ᵥ* A = _), ← congr(_ ᵥ* $H), ← vecMul_vecMul, (vecMul_injective_of_isUnit (hA.map (toRingHom ..).mapMatrix)).eq_iff]
  simpa [funext_iff, repMatrix, toMatrixAlgEquiv_apply, ← smul_def', ← commutes, ← map_smul_of_tower, ← map_sum, -LinearMap.map_smulₛₗ] using ⟨by tauto, fun h t ↦ by
    simpa [inv_smul_eq_iff] using apply_eq_of_mem_fracSpan (conjForm μ' g) μ (funext (by simp [h]))
      (le_saturateBy (mk_one_mem_ainfLattice t))⟩
lemma kisinAinf_le_fracSpan : L.kisinAinf ≤ L.fracSpan := fun _ ⟨⟨_, ⟨_, rfl⟩, h⟩, _⟩ ↦ ⟨_, by simp, h⟩
instance : IsTorsionFree Ainf L.Ambient := .trans_faithfulSMul _ WittCFlat (_ ⊗ _)
lemma frame_theorem : ((∀ (f : _ →ₗ[k.S] k.S) {ι : Type} [Fintype ι] (v : ι → _) (c : ι → Ainf), (∀ i, v i ∈ L.valueFieldPoints fracSpan) → ∑ i, c i • v i = 0 → ∑ i, f (c i) • v i = 0) ∧ (∀ l A δ, 3 * k.e ≤ p ^ l → k.e * A ≤ p ^ l * δ → ∀ x ∈ L.valueFieldPoints (frobKisinAinf l), p ^ (4 * δ) • x ∈ span k.S {y ∈ L.valueFieldPoints (frobKisinAinf l) | ∀ μ ∈ forms, ∀ g : Γ', toGp g.1 • μ y - μ y ∈ hodgeFil A}) ∧ L.kisinAinf = span _ L.kisinModule ∧ (∀ μ ∈ crysForms, ∀ y ∈ L.kisinModule, ∃ s ∈ k.bicommutant, k.E.1 ^ L.jumpBound • μ y = algebraMap _ _ s) ∧ ∀ d, (∀ {m r}, ainfToBPlus d ∣ ainfToBPlus (k.E.1 ^ m * r) → d ∣ r) → ∀ x ∈ kisinAinf, (∀ μ ∈ L.crysForms, k.E.1 ^ (2 * L.jumpBound) • μ x ∈ BPlus ∙ algebraMap _ _ d) → x ∈ d • kisinAinf) ∧ (∀ x ∈ kisinAinf, tau ^ L.jumpBound • x ∈ L.ainfLattice) ∧ (∀ x ∈ ainfLattice, tau ^ L.jumpBound • x ∈ L.kisinAinf) ∧ ∀ x ∈ L.kisinModule, k.frobEUnit 0 ^ L.jumpBound • FrobGroup.φ • x ∈ kisinModule := by
  set a := L.jumpBound; let e := finBasis ℤ_[p] L.Carrier
  obtain ⟨M, U, v, hM, hv, hU, eU⟩ := isChartOf.exists_isPeriodMatrix a a (ρ := .comp (overZp _) _)
    (L.inClass.1.mono le_sup_right :) e (Nat.sInf_mem exists_jump_bound)
  obtain ⟨Q, Q', Z, Y, B, hQ, hZ, eZ, X, hB, hG⟩ := hU.exists_frame; let s := Fintype.linearCombination Ainf (M := L.Ambient) (DiagTensor.mk 1 ∘ e)
  have hs : ainfLattice = s.range := by simp [ainfLattice_eq_span_basis, s, e]
  choose n hn using by simpa [← map_pow] using (((isUnit_WittCFlat_of_not_p_dvd not_p_dvd_tau).pow a).smul_bijective.2 <| s <| Qᵀ ·)
  let ν m := Fintype.linearCombination Ainf ((FrobGroup.φ • ·)^[m] ∘ n)
  have hν m t : (FrobGroup.φ ^ m • tau ^ a) • ν m t = s (Q.map (FrobGroup.φ ^ m • ·) *ᵥ t) := by
    simp [ν, smul_sum, smul_comm _ (t _), ← frobGroup_smul_smul, hn, ↓mulVec_eq_sum, -smul_pow']; simp [s, smul_sum]
  have hν₀ := by simpa [ν] using hν 0
  let ψ m := (algebraMap _ BdR).comp (toRingHom FrobGal Bcris (.ofAdd m, 1)); have I m {μ} : μ ∈ L.forms ↔ _ := forall_comm.trans (forall_congr' fun g ↦ (equivariant_iff_basisValues (M.isUnit.map (ψ m).mapMatrix) (by simpa [ψ, smul_smul, ↓map_mul, @MulAction.compHom_smul_def _ _ Bcris] using! congr((ψ m).mapMatrix $(hM g)))).trans funext_iff)
  have G' μ m t : (k.frobE m).1 ^ a • μ (ν m t) = basisValues μ ᵥ* (ψ m).mapMatrix M ⬝ᵥ (↑) ∘ (Z.map frobEnd^[m] *ᵥ ainfToBPlus ∘ t) := by
    have F := congr((k.frobE m).1 ^ (a + a) • μ $(hν m t) - basisValues μ ⬝ᵥ (ψ m).mapMatrix ($(eZ).map (↑)) *ᵥ t • 1); rw [Matrix.map_mul, eU, map_mul, ← mulVec_mulVec, dotProduct_mulVec] at F; apply (((isUnit_smul_of_dvd_mu 1 ⟨_, hv.symm⟩).pow a).map (ψ m)).mul_left_cancel; linear_combination (norm := (simp [s, ψ, smul_def', ↓map_apply, e, frobE_eq, FrobGroup.phi_pow_smul, mul_sum, ↓RingHom.mapMatrix_apply, FrobGal.smul_def, sum_mul, mul_comm (μ _)]; ring_nf)) F
  have G := by simpa [ν, smul_def'] using (G' · · <| Pi.single · 1)
  have K m {μ ν} hμ := mem_valueField_of_fixed ((@I m μ).1 hμ · ν)
  have hN i : n i ∈ L.kisinAinf := ⟨⟨_, ⟨a, rfl⟩, by simp [*]⟩, fun m μ hμ ↦ (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_frobE_of_ne m.succ_pos.ne) a).1 (by
    simpa [G] using! sum_mem fun ν _ ↦ mul_mem_hodgeFil (K _ hμ).1 algebraMap_mem_hodgeFil_zero)⟩
  have hP l i : FrobGroup.φ ^ l • n i ∈ valueFieldPoints (frobKisinAinf l) := ⟨by
    simp [frobKisinAinf, *], fun μ hμ ↦ by simpa using (div_mem (G μ l i ▸ sum_mem fun ν _ ↦ mul_mem (K l hμ).2 (Subfield.subset_closure (.inr ⟨(⟨_, Set.MapsTo.iterate @k.frobEnd_mem_bicommutant l (hZ ν i)⟩, 1), by simp⟩)) :) (phiInvToBdR_mem_valueField (k.frobE l ^ a)))⟩
  have H m (W : Submodule BPlus _) t (H : ∀ μ ∈ L.crysForms, μ (ν m t) ∈ W) i :
    phiInvToBdR 0 (k.frobE m ^ (a + a) * t i) ∈ W := by
    choose μ hμ using (exists_functional_extend <| .comp (algHom ..).toLinearMap <| e.constr ℕ <| frobEnd^[m] ∘ M.2 ·)
    have R ν : basisValues (μ ν) ᵥ* (ψ m).mapMatrix M = (1 : Matrix ..) ν := funext fun l ↦ by
      simpa [ψ, FrobGal.smul_def, *, e, Matrix.mul_apply] using! congr(ψ m ($(M.4) ν l))
    convert sum_smul_mem W (Y.map frobEnd^[m] i) fun ν _ ↦ W.smul_of_tower_mem ((k.frobE m).1 ^ a)
      (H _ ⟨by simp [I m, ↓R], _, hμ ν⟩)
    simpa [-mulVec, ↓G', ↓R, ↓map_mul, ← mulVec_mulVec, frobE_eq, algebraMap_eq_diagonal, FrobGroup.phi_pow_smul, ↓mulVec.eq_1 (Y.map _), smul_def'] using
      congr(((((frobEnd ^ m).mapMatrix $X.symm *ᵥ ainfToBPlus ∘ t) i :) : BdR))
  have h₂ x : x ∈ L.ainfLattice → ∃ t, ν 0 t = tau ^ a • x := hs ▸ fun ⟨α, h⟩ ↦ ⟨_, by
    simpa [h, hQ, pow_add] using! hν₀ (Q' *ᵥ α)⟩
  refine and_assoc.2 ⟨?X, ?_⟩
  exact fun f _ _ v c hv e ↦ (fracSpan.sum_smul_mem (f <| c ·) (t := univ) fun i _ ↦ (hv i).1).elim
    fun r ⟨hr, E⟩ ↦ (h₂ _ E).rec fun t E ↦ by simpa [ν, by simpa using hr, by simpa using (H 0 ⊥ t fun μ J ↦ by simp [E, smul_def', by simpa using (sum_map_mem_of_valueField f _ _ (hv · |>.2 _ J.1) (W := ⊥) (by simpa [smul_def'] using congr(μ $e)))])] using E.symm
  have S := @mem_span_range_iff_exists_fun.{0}; have K' w t h := (pi_dvd_iff.2 h : (fun _ ↦ w) ∣ t).imp fun s e ↦ (congr(ν 0 $e).trans (map_smul ..)).symm
  have e₀ := L.kisinAinf.span_eq_of_le (Set.range_subset_iff.2 hN) fun x f@⟨⟨_, ⟨N, rfl⟩, h⟩, _⟩ ↦ (by
    rw [smul_smul, ← pow_add, S]; induction' a + N with N ih <;> simp [pow_succ', ν]
    exact fun t h ↦ ih (by simpa [h, ν] using (K' _ t fun i ↦ tau_dvd_of_theta_frobEnd fun m ↦ by
      simpa [frobE_dvd_iff, FrobGroup.phi_pow_smul, mt frobE_dvd_iff.2 (not_frobE_dvd_frobE_of_ne m.succ_pos.ne)] using! phiInvToBdR_mem_hodgeFil_one_iff.1 (H (m + 1) ((hodgeFil 1).restrictScalars _) (FrobGroup.φ ^ (m + 1) • t ·) (by
      simp [h, ν, ← frobGroup_smul_smul, ← smul_sum]
      simpa [smul_def'] using (mul_mem_hodgeFil (phiInvToBdR_mem_hodgeFil_one_iff.2 (frobE_dvd_phi_pow_tau m.succ_pos)) <| (smul_mem _ (tau ^ N) f).2 m · ·.1)) i))) : _ → _) (h₂ _ h)
  have D l := (valueFieldPoints _).span_eq_of_le (Set.range_subset_iff.2 (hP l)) fun x hx ↦
    have ⟨t, e⟩ := (S _).1 (e₀.ge hx.1); (S _).2 ⟨_, by simpa [add_eq_zero_iff_eq_neg'] using (?X k.coord₀ (Option.rec _ _) (FrobGroup.φ ^ l • ·.elim (-1) t) (.imp_left ((show frobKisinAinf l ≤ fracSpan from fun _ h ↦ by simpa using smul_mem_fracSpan (FrobGroup.φ ^ l) (kisinAinf_le_fracSpan h)) ·) <| ·.rec hx (hP l)) (by simp [← frobGroup_smul_smul, ← smul_sum, e]))⟩
  simp only [↓← D, ↓← by simpa [frobKisinAinf_zero] using D 0, span_span_of_tower, ← e₀, forall_exists_index, mem_smul_pointwise_iff_exists, S, forall_apply_eq_imp_iff, exists_exists_eq_and]
  refine ⟨⟨fun l A δ b d c ↦ ?_, ⟨⟩, fun μ ⟨hμ, l, E⟩ c ↦ ?_, fun d D t h ↦ K' _ t fun i ↦ D (map_dvd _ (D ((mem_span_singleton.1 (H 0 _ ((_ : Ainf) • t) (by simpa [-map_sum] using! h)
    i)).imp fun y h ↦ algebraMap_injective _ BdR (by simpa [frobE, commutes y, smul_def'] using h.symm))))⟩, by simp [*], h₂, fun c ↦ ⟨B *ᵥ k.φ ∘ c, by
    simpa [mul_comm _ v.1, mul_comm _ tau, j4, hB, ← hv, ← hν₀, ← mulVec_mulVec, mul_pow, ↓frobEUnit_pow_smul, Units.smul_def, smul_sum (r := FrobGroup.φ), «φ», frobE, ν] using (hν 1 (FrobGroup.φ • c ·)).symm⟩⟩
  obtain ⟨V, D, hD, eV, R⟩ := radius_lemma (fixes _) (by simpa using (exists_smul_z 1).choose_spec) hZ X (hG _ (fixes _)).choose_spec b a; refine (map_nsmul (Fintype.linearCombination ..) ..).subst (mapsTo_span (fun y ↦ Exists.rec fun r h ↦ ⟨⟨y, rfl⟩, fun μ hμ g ↦ ?_⟩) (R A δ d c)); choose w f using h; simpa [by simpa [-mulVec, -mulVec_add, ν, eV, ← mulVec_mulVec, eq_add_of_sub_eq' (funext f : _ = (_ : BPlus) • w), algebraMap.smul, ← smul_sum] using G' μ l (y ·), ↓mulVec_add, mul_add, frobE, smul_sum, ← by simpa using (I l).1 hμ g, by simpa [← ext_iff] using hD _ (fixes g).1] using (fun F ↦ sub_mem (k7 (toGp g) F) F) (sum_mem fun ν _ ↦ mul_mem_hodgeFil (K l hμ).1 (mul_mem_hodgeFil (frobE_zpow_mem_hodgeFil 0 A) (@algebraMap_mem_hodgeFil_zero _ _ ↑(D ν ⬝ᵥ w)))); choose s f S using (isChartOf.v1 (b := ∑ i, l (e i) * M i ·) fun g ↦ by simpa [E, ψ, ← map_mul, ← map_sum] using ((I 0).1 hμ g _).symm)
  exact ⟨s ⬝ᵥ Z *ᵥ ainfToBPlus ∘ (c ·), by simp (maxDischargeDepth := 4) [sum_mem, mul_mem, *], by
    simpa [E, e, ψ, ← map_mul, ← map_sum, ← S] using! G' μ 0 (c ·)⟩
end Lift.KummerChart.JumpLattice
end
variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : Lift.KummerChart Γ} {O} {L : Lift.KummerChart.JumpLattice O} {x μ g} (hg : ∀ h ∈ k.Γ', g * h * g⁻¹ ∈ k.Γ')
namespace Lift.KummerChart.JumpLattice
lemma pow_smul_gal_sub_mem_span_of_dvd {g : Gp p} {d m x} (o : ∀ {y}, y ∈ k.bicommutant → d ∣ g • y - y) : (∃ s ∈ k.bicommutant, k.E.1 ^ m • x = algebraMap _ BdR s) → k.E.1 ^ (2 * m) • (g • x - x) ∈ BPlus ∙ algebraMap _ _ d := fun ⟨s, f, e⟩ ↦ Submodule.mem_span_singleton.2 (by
  obtain ⟨_, ⟨v, _⟩, ⟨r, _⟩, t, _⟩ := congr(g • $e), pow_dvd_pow_of_dvd (k.associated_smul_E g).dvd'
    m, o (k.q1 (k.E ^ m)), o f
  apply_fun algebraMap _ BdR at *
  use v • (k.E.1 ^ m • t - r * s)
  simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, pow_mul'] at *
  grind)
include hg
lemma conjForm_mem_forms (h : μ ∈ L.forms) : conjForm μ g ∈ L.forms := fun t s ↦ by
  simpa [mul_smul, inv_smul_eq_iff] using h (L.ρ g t) ⟨_, hg _ s.2⟩
lemma smul_mem_kisinAinf : x ∈ kisinAinf → FrobGroup.inr g • x ∈ L.kisinAinf := .imp (fun ⟨_, ⟨n, rfl⟩, s⟩ ↦ mem_saturateBy_of_smul (by simp [y1.pow_pow.dvd])
  ⟨n, rfl⟩ (le_saturateBy (frobGroup_smul_smul .. ▸ smul_mem_ainfLattice _ s))) fun h n _ e ↦ by
  simpa [smul_smul, ((FrobGroup.phi_mul_comm _).pow_left _).eq] using k7 (toGp g) (h n _ (conjForm_mem_forms hg e))
