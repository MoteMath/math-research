import Lib.ClassField.Places.CyclotomicRamification
import Lib.PadicHodge.Crystalline.Defs
noncomputable section
section
section
open Algebra Finset Polynomial IntermediateField Submodule Units NeZero Set IsUltrametricDist InfiniteGalois AdjoinSimple NonarchimedeanGroup PadicComplex Subgroup
lemma tate_eq_zero_of_chi_twist {p} [ThePrime p] {x : ℂ_[p]} {u v : ℤ} (hu : u ≠ v) (h : ∀ᶠ g in nhds 1, (cyclotomicGp g ^ u).1 • g • x = (cyclotomicGp g ^ v).1 • x) : x = 0 := (is_nonarchimedean _ h).rec fun U _ ↦ mem_span.1 (mem_span_fixed (.id _) (smulMonoidHom.comp ((cyclotomicGp ^ (-u + v))⁻¹.prod (actionRep ℤ_[p] _ (.id _)))) (by simp [smul_def', ← coe_eq, mul_smul_comm]) (by simpa
  [inv_smul_eq_iff, zpow_add, mul_smul]) (fixingSubgroup_fixedFieldOf _).le) ⊥ fun y h ↦ by
  simp_all [inv_smul_eq_iff]
  have ⟨C, H⟩ : ∃ C, ∀ z ∈ fixedField cyclotomicGp.ker, ‖normalizedTrace ℚ_[p] _ z‖ ≤ C * ‖z‖ := let T := normalizedTrace ℚ_[p] (PadicAlgCl p)
    ((nthRoots p 1).map T).finite_toSet.isBounded.exists_pos_norm_le.imp' (· * p) fun C ⟨c, d⟩ z _ ↦ by
    choose n ζ h k using by simpa using (exists_cyclotomicGp_eq_of_isClosed 1 (isClosed_setOf_smul z (· ≠ z))).mt (by aesop)
    have H η (h : η ^ p ^ n.succ = 1) : ‖T η‖ ≤ C := by if e : η ^ p = 1 then simp_all [pos] else simp [c.le, by
      simpa [← pow_mul, mul_sum, fun a ha ↦ ((exists_inertia_cyclotomicGp_eq a ha).rec fun g k ↦
      by erw [← cycCharMod_eq_iff (g := g).1 (by simp [cycCharMod_prime_pow_eq, k]) η h, normalizedTrace_map _ _ g.toAlgHom]
      : T (η ^ a) = T η), ← pow_succ', ne, h] using congr(T (η * $(geom_sum_eq e (p ^ n))))]
    obtain ⟨e, l, a, rfl⟩ := norm_zeta_sub_one_pow h ▸ norm_p_eq_inv, lt_imp_lt_of_le_imp_le (one_le_pow₀ ·) (norm_zeta_sub_one_pow h ▸ norm_p_lt_one), by simpa [natDegree_cyclotomic, -coe_range, mem_span_image_finset_iff_exists_fun', ↓← taylor_apply] using ((span_range_natDegree_eq_adjoin ((cyclotomic.monic ..).comp_X_add_C 1) (by simpa [↓aeval_comp, ← eval_map_algebraMap] using (isRoot_cyclotomic_iff.2 h))).ge ((adjoin_toSubalgebra {ζ - 1}).le ((fixedField_fixingSubgroup _).le ((k _).mtr <| by simpa using ·.2 (gen ..)))))
    grw [← sum_filter_ne_zero, map_sum, norm_sum_le_of_forall_le_of_nonneg]; bound
    intros; grw [norm_sum_eq_sup'_of_pairwise_ne ⟨_, ‹_›⟩, ← le_sup' _ ‹_›]
    simp [norm_smul]; grw [← pow_le_pow_of_le_one, e, sub_eq_add_neg, Commute.add_pow', map_sum, norm_sum_le_of_forall_le_of_nonneg c.le] <;> simp_all [T, field, le_of_lt, neg_one_pow_eq_ite, -nsmul_eq_mul, ← pow_mul, h.pow_eq_one_iff_dvd, apply_ite, (norm_nsmul_le _ _).trans]
    simp_all [Set.Pairwise, norm_smul, ← inv_eq_iff_eq_inv.2 e, ← zpow_natCast, ← zpow_mul, Padic.norm_eq_zpow_neg_valuation, ← zpow_add₀, l.ne, Int.emod_eq_of_lt, h.sub_one_ne_zero (by simp [Fact.out]), ne_of_apply_ne (· % ((p ^ n.succ).totient : ℤ))]
  have A x hx (f : C(_, ℂ_[p])) h : 1 ≤ C * ‖f x‖ := (mapsTo_image_iff.2 h).closure_left
    (f.2.norm.const_mul _) isClosed_Ici (ax_exists_near_fixed cyclotomicGp.ker hx)
  apply Function.mtr (by aesop) (A y⁻¹ (by aesop) (1 - y • .id _) fun w hw ↦ ?_)
  let ⟨γ, k, c⟩ : ∃ γ, γ w = w ∧ (cyclotomicGp γ ^ (-u + v)).1.1 ≠ 1 := (exists_inertia_cyclotomicGp_eq p.succ (by
   simp)).rec fun γ c ↦ (exists_pow_mem_of_index_ne_zero (quotient_finite_of_isOpen _
    (isLocalGalois_padic.1.6 w)).card_pos.ne' γ).rec fun N k ↦ ⟨_, k.2.2, (val_eq_one.2
    ∘ pow_natAbs_eq_one.2 ∘ ext ∘ PadicInt.ext).mt (by simp [c]; norm_cast; simp [ne]; lia)⟩
  convert A ((mk0 _ (sub_ne_zero.2 c))⁻¹ • y * w) ?_ (1 - (γ • .id _ - .id _)) fun z hz ↦ ?_ <;>
    simp +contextual [*, by simpa using hw, smul_comm _ _⁻¹, Units.smul_def]
  congr! 3; match_scalars <;> simp [field]
  norm_cast; simpa [map_sub, normalizedTrace_minpoly, ← C_1, -map_one] using H _ (sub_mem (one_mem _) (sub_mem (smul_mem_fixedPoints_of_normal γ hz) hz))
end
open UniformSpace.Completion Submodule Units Module Filter Topology nonZeroDivisors AlgHom
lemma b2 {A V ι} [CommRing A] [AddCommGroup V] [Module A V] (b : V ≃ₗ[A] ι →₀ A) {W W' : Submodule A _} (hP : ∀ v ∈ W, v ≠ 0 → (∀ y ∈ W, (∀ i, b v i = 0 → b y i = 0) → ∀ k, b v k • y = b y k • v) → ∃ u ∈ W ⊓ W', (∃ k, b u k = 1) ∧ ∀ i, b v i = 0 → b u i = 0) : W ≤ W' := ((InvImage.wf (b · |>.1) wellFounded_lt).fix (C := (· ∈ _ → _ ∧ _))
  (fun w ih hw ↦ by refine have h := (by_cases id fun _ ↦ hP w hw · fun y _ _ k ↦ ?_); ⟨by_cases
  (by bound) (h · |>.rec fun y ⟨_, ⟨k, _⟩, _⟩ ↦ ?_), h⟩ <;> (
  have := by simpa [mul_comm, LT.lt, LE.le, InvImage] using ih (b y k • w - b w k • y)
  grind [sub_mem_iff_left, smul_mem, one_smul, mem_inf, smul_eq_zero_of_left])) · · |>.1)
lemma le_of_hodgeTate_stable {p} [ThePrime p] {ι} [_root_.Finite ι] {F} (hF : nhds 1 ≤ F) (u : ι → ℤ) (W W' : Submodule ℂ_[p] (ι → ℂ_[p])) (hW : ∀ a ∈ W, ∀ᶠ g in F, (fun i ↦ (cyclotomicGp g ^ u i).1 • g • a i) ∈ W)
  (H : ∀ a k, (↑) ∘ a ∈ W → (∀ i, ‖a i‖ ≤ 1) → (∀ i, u i = u k ∨ a i = 0) → a k = 1 → (∀ i, ∀ᶠ g in F, g (a i) = a i) → (↑) ∘ a ∈ W') : W ≤ W' := b2 (Pi.basisFun ..).1 fun v hv n h ↦ by
  obtain ⟨k, z, _⟩ := by simpa [n] using v.support.toFinite.exists_maximalFor (‖v ·‖)
  have M := W.smul_mem (v k)⁻¹ hv
  have e i := by simpa [*, -smul_mul'] using (hW _ M).mono fun _ ↦ (congr((v k)⁻¹ * $(h _ · (by simp +contextual) k) i))
  have h₂ i := (tate_eq_zero_of_chi_twist · (hF (e i)))
  have f i := (e i).mono fun g h ↦ by_cases (isSMulRegular _ _ <| · ▸ h) (h₂ i · ▸ smul_zero g)
  choose a ha using (exists_algebraic_of_fixed_near_one <| hF <| f ·)
  simp [*, Pi.smul_def] at M h₂ f
  refine ⟨_, ⟨M, H a k M ?_ ?_ (coe_inj.1 ?_) f⟩, ?_⟩ <;>
    simp [← norm_coe (a _), ← ha, field, coe_one] <;> grind [norm_zero]
variable {p} [ThePrime p] {Γ} [Group Γ] [𝒥 : OverGp Γ p]
instance flat_padicInt_of_algebra_padic {B} [CommRing B] [Algebra ℤ_[p] B] [Algebra ℚ_[p] B] [IsScalarTower ℤ_[p] ℚ_[p] B] : Flat ℤ_[p] B := .trans _ ℚ_[p] _
lemma nearOne_eq_nhds_one [TopologicalSpace Γ] (hj : IsOpenEmbedding 𝒥.toGp) : nearOne Γ = 𝓝 1 := by simp [nearOne, hj.nhds_eq_comap]
variable (Γ) in abbrev localFieldOf := fixedFieldOf 𝒥.toGp.range
lemma mem_localFieldOf {x} : x ∈ localFieldOf Γ ↔ ∀ g, 𝒥.toGp g x = x := by simp
lemma exists_gp_eq_algHom (γ : _ →ₐ[ℤ_[p]] ℂ_[p]) : ∃ s : Gp p, ∀ x, γ x = s x := ⟨restrictNormal' (γ.extendScalarsOfIsLocalization _ _⁰) _, by simp [restrictNormal', PadicComplex.coe_eq]⟩
variable (Γ) in lemma nhds_one_le_map_nearOne : 𝓝 1 ≤ Filter.map toGp (nearOne Γ) := (map_comap_of_mem (𝒥.2.1.mem_nhds (one_mem _))).ge
end
section
variable {p} [ThePrime p] (Γ) [Group Γ] [𝒥 : OverGp Γ p] {m n x} {y : BdRPlus}
lemma z7 {x : ℂ_[p]} : (∀ g, 𝒥.toGp g • x = x) ↔ ∃ a ∈ localFieldOf Γ, x = a := by have := @exists_algebraic_of_fixed_near_one _ _ x ∘ (nhds_one_le_map_nearOne Γ ·); aesop
open BdRPlus Algebra IsDiscreteValuationRing IsFractionRing Submodule algebraMap
private lemma m1 : Prime x4 := j6.prime prime_xi
def tUnit : BdRˣ := .mk0 x4 (mod_cast m1.1)
def hodgeFil (n : ℤ) := BdRPlus ∙ (tUnit ^ n).1
attribute [local simp] smul_def' Units.smul_def tUnit hodgeFil mem_span_singleton
lemma mem_hodgeFil : x ∈ hodgeFil n ↔ ∃ y : BdRPlus, y * (tUnit ^ n).1 = x := by simp
@[simp] lemma algebraMap_mem_hodgeFil_zero : algebraMap _ _ y ∈ hodgeFil 0 := by simp
lemma hodgeFil_anti : Antitone hodgeFil := antitone_int_of_succ_le (by simp [← mul_self_zpow])
lemma mul_mem_hodgeFil {y} : x ∈ hodgeFil m → y ∈ hodgeFil n → x * y ∈ hodgeFil (m + n) := (by simpa [span_mul_span, zpow_add] using mul_mem_mul · ·)
lemma algebraMap_mem_hodgeFil_iff_xi_pow_dvd {M : ℕ} : ↑y ∈ hodgeFil M ↔ (xi : BdRPlus) ^ M ∣ y := by simp [j6.pow_pow.dvd_iff_dvd_left, dvd_def, eq_comm, mul_comm]; norm_cast
lemma algebraMap_mem_hodgeFil_one_iff : ↑y ∈ hodgeFil 1 ↔ thetaBdR y = 0 := by erw [algebraMap_mem_hodgeFil_iff_xi_pow_dvd, pow_one, j8]
lemma qpBar_mem_hodgeFil_iff : ↑(x : PadicAlgCl p) ∈ hodgeFil n ↔ 0 < n → x = 0 := ⟨flip (by
  simpa using algebraMap_mem_hodgeFil_one_iff.1 <| hodgeFil_anti · ·), (le_or_gt ..).elim (hodgeFil_anti · algebraMap_mem_hodgeFil_zero) ∘ by aesop⟩
lemma y6 g (k : ℤ) : g • ↑(tUnit ^ k) = (cyclotomicGp g ^ k).1 • (tUnit ^ k).1 := by cases k <;> cases exists_tPeriod.choose_spec <;> simp_all [x4] <;> ring!
lemma BdR.exists_sub_mem_of_smul_sub_mem (S : Submodule BdRPlus _) {x : BdR}
    (h : ∀ g, 𝒥.toGp g • x - x ∈ S) : ∃ a : localFieldOf Γ, x - a.1 ∈ S := by
  simp; by_contra! c
  have H a ha := (exists_units_eq_smul_zpow_of_irreducible m1.irreducible (S.zero_mem.ne_of_notMem (c a ha)).symm).elim fun n ↦ (·.imp fun u E ↦ by
   have e g i := c a ha (E ▸ S.smul_mem u ((S.smul_mem_iff_of_isUnit i).1 (by
    simpa [by simpa [-smul_def'] using y6, *, ← sub_smul, smul_distrib_smul, -smul_def', smul_algebra_smul_comm, eq_add_of_sub_eq E, ← smul_assoc] using h g)))
   simpa [(by_contra (isUnit_iff.1 u.isUnit <| tate_eq_zero_of_chi_twist · (nhds_one_le_map_nearOne Γ (by simp_all))) : n = 0), z7] using And.intro E e)
  obtain ⟨u, rfl, a, k, E⟩ := by simpa using H 0
  simpa [E] using isUnit_iff.1 ⟨_, coe_inj.1 ((map_sub ..).trans (H a k).choose_spec.1).symm⟩
end
section
section
open Filter Module Submodule LinearMap Fintype Finset Set RingHomClass FaithfulSMul Fint
variable {p} [ThePrime p] {Γ R T ι} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R] [OverGp Γ p] {ρ : Representation R Γ T} {γ : R →ₐ[ℤ_[p]] ℂ_[p]} [A : Algebra.IsAlgebraic ℤ_[p] R]
def evalOnBasis (b : Basis ι R T) : (T →ₛₗ[toRingHom γ] ℂ_[p]) ≃ₗ[ℂ_[p]] ι → ℂ_[p] := .ofBijective (pi (id.flip <| b ·)) ⟨fun _ _ ↦ b.ext ∘ congrFun, let := γ.toAlgebra; fun c ↦ ⟨⟨_, (b.constr ℕ c).2⟩, funext (b.constr_basis ℕ c)⟩⟩
instance : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) := IsFractionRing.comap_isAlgebraic_iff.2 (PadicAlgCl.isAlgebraic _)
variable (γ) in lemma exists_algHom_lift : ∃ δ : R →ₐ[ℤ_[p]] PadicAlgCl p, ∀ r, γ r = δ r := ((AlgEquiv.arrowCongr .refl (.ofInjectiveField (Algebra.algHom _ (PadicAlgCl p) _))).surjective (γ.codRestrict _ fun r ↦ IsAIC.mem_range_of_isIntegralElem (((A.1 r).algHom γ).extendScalars (algebraMap_injective ..)).isIntegral)).imp fun _ h _ ↦ congr(($h _).1).symm
lemma mem_hodgeTateMaps_of_span {s : ι → T} (hs : span R (range s) = ⊤) {f u} (h : ∀ i, ∀ᶠ g in nearOne Γ, f (ρ g (s i)) = (χ g ^ (-u)).1 • toGp g • f (s i)) : f ∈ hodgeTateMaps ρ γ u := (exists_algHom_lift γ).rec fun δ _ x ↦ by refine span_induction ?_ ?_ (fun _ _ _ _ ↦ (·.mp <| ·.mp ?_)) (fun r _ _ ↦ (·.mp ((eventually_nearOne_apply_eq Γ (δ r)).mp ?_))) (hs.ge ⟨⟩ : x ∈ _) <;> simp_all
omit A
variable [F : Module.Finite R T]
instance : Module.Finite ℂ_[p] (T →ₛₗ[toRingHom γ] ℂ_[p]) := let ⟨_, x, h⟩ := F.exists_fin
  .of_injective (pi (id.flip <| x ·)) fun _ _ ↦ ext_on_range h ∘ congrFun
lemma hodgeTateMaps.mem_span_same_weight {k : ι → ℤ} {f} (hf : ∀ i, f i ∈ hodgeTateMaps ρ γ (k i)) {u φ} (hφ : φ ∈ hodgeTateMaps ρ γ u) (h : φ ∈ span ℂ_[p] (range f)) : φ ∈ span (PadicAlgCl p) (f '' {i | k i = u}) := by
  obtain ⟨⟨_, x, hx⟩, _, a, _, e, hi⟩ := F.exists_fin, exists_linearIndependent' ℂ_[p] f; have := hi.finite; obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun _).1 (e.ge h)
  have H : ∀ i, ∀ᶠ g in _, (cyclotomicGp g ^ (-u + k (a i))).1 • g • c i = _ := eventually_all.1
   (nhds_one_le_map_nearOne Γ ((Eventually.all fun l ↦ (hφ (x l)).and (.all (a · |> hf <| x l))).mono fun g H ↦ linearIndependent_iffₛ.1 hi _ _ ((cancel_right (ρ.apply_bijective g).2).1 (ext_on_range hx (by simpa [H, smul_sum, smul_smul, zpow_add] using (H · |>.1.symm))))))
  exact sum_mem fun i _ ↦ if e : u = k (a i) then (exists_algebraic_of_fixed_near_one (by simpa [e] using H i)).rec (by aesop (add simp PadicComplex.coe_eq))
   else by simp [tate_eq_zero_of_chi_twist (neg_add_eq_zero.1.mt e) (by simpa using H i)]
instance finite_hodgeTateMaps u : Module.Finite (PadicAlgCl p) (hodgeTateMaps ρ γ u) := (exists_fun_fin_finrank_span_eq ..).elim fun _ ⟨h, e, _⟩ ↦ .of_fg ((fg_span (toFinite _)).of_le fun _ m ↦ hodgeTateMaps.mem_span_same_weight h m (e.ge (subset_span m)))
lemma hasJumps_of_basis [Fintype ι] {u} {b : Basis ι ℂ_[p] _} (h : ∀ i, b i ∈ hodgeTateMaps ρ γ (u i)) : HasJumps ρ γ (univ.1.map u) := fun v ↦ by erw [jump, ← span_eq_of_le _ (by grind [SetLike.mem_coe]) fun _ ↦ (hodgeTateMaps.mem_span_same_weight h · (by simp)), image_eq_range, univ.1.count_map, finrank_span_eq_card ((b.linearIndependent.restrict_scalars' _).comp _ (by simp))]; simp [eq_comm, card_def]
end
attribute [-simp] IsUnit.dvd Algebra.mul_smul_comm Algebra.smul_mul_assoc
namespace Lift
open Ainf Set Ideal Fact NeZero IsLocalRing PowerSeries Witt WittVector WithIdeal
variable {p} [ThePrime p] (f : ℕ+)
attribute [local simp] image_pair Ideal.map_pow mem_span_singleton mul_sub PadicInt.maximalIdeal_eq_span_p IsUnit.map Ainf.isUnit_iff_isUnit_constantCoeff ne
def flatFq := (iterateFrobenius OFlat p f).eqLocus (.id _)
@[simp] lemma card_flatFq : .card (flatFq f) = p ^ f.val := open Polynomial in
  have h := (isMonicOfDegree_X_pow ..).sub (by simp [elim])
  (Nat.subtype_card ⟨_, nodup_roots (galois_poly_separable p _ (by simp))⟩
    (by aesop (add simp h.ne_zero))).trans (((IsAlgClosed.splits _).of_splits_map_of_injective
    (IsFractionRing.injective _ CFlat) fun _ _ ↦ OFlat.isAIC.mem_range_of_isIntegralElem ⟨_, h.2, by aesop⟩).natDegree_eq_card_roots.symm.trans h.1)
instance : Finite (flatFq f) := Nat.finite_of_card_ne_zero (by simp)
instance : Field (flatFq f) := (Finite.isField_of_domain _).toField
@[reducible] def WittFq := WittVector p (flatFq f) deriving CommRing
instance : Algebra (WittFq f) Ainf := inferInstance
deriving instance Algebra (WittFq f) for @WittCFlat p _
structure Chart where
  (f) (seriesMap : (WittFq f)⟦X⟧ →ₐ[WittFq f] Ainf) (unitSeries) not_isUnit_z :
    ¬IsUnit (seriesMap X)
  (varpiFlat e) associated_xi : Associated (seriesMap (X ^ e * Units.val unitSeries + p.cast)) xi
  seriesMap_X : seriesMap X = teichmuller p varpiFlat
variable {f} (c : Chart) {Γ : Type} [Group Γ] {g : Gp p}
lemma exists_algHom_X_eq Λ {R} [CommRing Λ] [CommRing R] [Algebra Λ R] {I} [h : IsAdicComplete I R]
    {z} (hz : z ∈ I) : ∃ e : Λ⟦X⟧ →ₐ[Λ] R, e X = z := let := mk I
  let : UniformSpace Λ := ⊥
  by obtain ⟨⟨⟩⟩ := (IsAdic.isAdicComplete_iff (by rfl)).1 h, DiscreteTopology.instContinuousSMul
     use aeval (isTopologicallyNilpotent_of_mem hz), by simp [coe_aeval]
lemma exists_chart_of_pow_mul_eq_neg f {x : OC} {e} (v : OCˣ) (h : x ^ e * v = -p) : ∃ ev : (WittFq f)⟦X⟧ →ₐ[WittFq f] _, theta (ev X) = x ∧ ∀ A : _ˣ, theta (ev A.1) = v → ∃ c : Chart, c.f = f ∧ c.seriesMap ≍ ev ∧ c.varpiFlat.untilt = x ∧ c.e = e ∧ c.unitSeries ≍ A := (untilt_surjective_of_isAIC x).rec fun (u : OFlat) _ ↦ by
  refine (exists_algHom_X_eq _ (h := q4 ?_) (by bound)).imp fun _ hu ↦ ⟨?_, fun A _ ↦ ⟨⟨_, _, A, ?_, u, e, associated_of_dvd_dvd ((z6
    ?h ?_).1 ?_) (theta_eq_zero_iff_xi_dvd.1 ?h), hu⟩, ?_⟩⟩ <;>
    simp (maxDischargeDepth := 4) [*, -constantCoeff_apply, p_dvd_iff.1, @out ¬IsUnit _, mt ((IsUnit.mul · v.isUnit) ∘ .pow e ∘ .map theta)]; use -v, by aesop
instance : Module.Finite ℤ_[p] (WittFq f) := .of_surjective (Finsupp.lift _ _ _ (teichmuller p)) (@surjective_of_mkQ_comp_surjective _ _ (maximalIdeal _) _ _ _ _ _ _ _ (by simp [(isAdicComplete_over_base _).1]) _ (Quot.ind (⟨fun₀ | ·.1 0 => 1, SModEq.sub_mem.2 (by simp [p_dvd_iff, map_sub])⟩)))
lemma WittFq.j7 (m : FrobGal) c : ∃ b, m • algebraMap (WittFq f) Ainf c = algebraMap (WittFq f) _ b := ⟨⟨(⟨_, (smul_pow' m ..).symm.trans <| congrArg _ <| c.1 · |>.2⟩)⟩, rfl⟩
lemma v7 : (map ((residue _).comp (flatFq f).subtype) : WittFq f → _).Injective := map_injective _ (RingHom.injective _)
abbrev FixesLambda f (g : Gp p) := ∀ a, g • algebraMap (WittFq f) Ainf a = algebraMap _ _ a
namespace Chart
def S := c.seriesMap.range
def z : c.S := ⟨c.seriesMap X, _, rfl⟩
abbrev maxIdeal := span {↑p, c.z}
abbrev FixesThetaZ g := FixesLambda c.f g ∧ g • theta c.z = theta c.z
def IsChartOf (j : Γ →* Gp p) := ∀ g, c.FixesThetaZ g → g ∈ j.range
lemma z_eq_teichmuller : c.z = teichmuller p c.varpiFlat := c.8
instance : NeZero c.e := ⟨(prime_xi.2.1 <| c.7.isUnit <| by
  simp [·, p_dvd_iff.1, -constantCoeff_apply])⟩
lemma r3 : ∃ b, ↑c.z ∣ xi - p * b := c.7.rec (⟨·, by simp [← ·, add_mul, z]⟩)
lemma not_p_dvd_z : ¬↑p ∣ c.z.1 := (·.trans c.r3.choose_spec).mt (by simp [dvd_sub_left])
def x5 : (WittFq c.f)⟦X⟧ ≃ₐ[WittFq c.f] c.S := .ofInjective _ (.of_ker _ fun f h ↦ constantCoeff_divXPowOrder_eq_zero_iff.1 (v7 (by
  obtain _ := c.4, c.not_p_dvd_z, f.X_pow_order_mul_divXPowOrder ▸ h,
    congr(toWittResidue (c.seriesMap $f.divXPowOrder.eq_X_mul_shift_add_const))
  aesop (add simp [seriesMap_X, toWittResidue, z, C_eq_algebraMap, ((residue_eq_zero_iff _).2)]))))
@[irreducible, local simp] def E := c.z ^ c.e * c.x5 c.unitSeries + p
lemma associated_E_xi : Associated ↑c.E xi := by simpa using! c.7
lemma theta_E : theta c.E = 0 := theta_eq_zero_iff_xi_dvd.2 c.associated_E_xi.dvd'
lemma z_dvd_E_sub_p : c.z ∣ c.E - p := by simp
@[simp] lemma b9 : c.x5.symm c.z = X := c.x5.left_inv X
lemma z_pow_mem_span : c.z ^ c.e ∈ span {c.E, ↑p} := by simp [span_insert (_ * _), mem_sup_left]
lemma exists_z_dvd_sub_const s : ∃ a t, s = algebraMap (WittFq c.f) _ a + c.z * t := by simp [← sub_eq_iff_eq_add', ← dvd_def, ← map_dvd_iff c.x5.symm, X_dvd_iff]
instance : c.maxIdeal.IsMaximal := by
  simpa [eq_span_insert_X_of_X_mem_of_span_eq X_prime.2.1 ((map_maximalIdeal_of_surjective _ (@constantCoeff_surj (WittFq c.f) _)).trans (irreducible p).maximalIdeal_eq).symm, pair_comm X]
    using! (maximalIdeal _).map_isMaximal_of_equiv c.x5
instance : IsAdicComplete c.maxIdeal c.S := by
  simpa [isAdicComplete_iff, @IsHausdorff.of_isDomain _ _ c.maxIdeal (isNoetherianRing_range _), IsPrime.ne_top] using! (IsPrecomplete.congr_ringEquiv (span {↑p, X}) c.x5.toRingEquiv).2 (isPrecomplete_of_shiftDiff_surjective (fun b ↦ ((@out (shiftDiff _ (p : WittFq c.f)).Surjective).comp_left (coeff · <| b ·)).imp' (.mk ∘ flip ·) (by
    simp_all [funext_iff, PowerSeries.ext_iff, shiftDiff, flip, ← nsmul_eq_mul])) out)
lemma m5 n : ∃ N, c.maxIdeal ^ N • ⊤ ≤ (span {↑p, xi} ^ n).restrictScalars
  c.S := ⟨_, by simpa [← pow_mul] using! pow_right_mono (exists_pow_le_of_le_radical_of_fg (span_le.2 (pair_subset ⟨1, by aesop⟩
  (mem_radical_of_not_isUnit c.4 (by simp)))) ⟨{_, _}, by aesop⟩).choose_spec n⟩
instance : IsHausdorff c.maxIdeal Ainf := ⟨by simpa using! (j9 prime_p.2.1 c.4).1.1⟩
lemma z1 : ∃ d : AdicBasis c.maxIdeal Ainf, ∃ i, ∀ s : c.S, d.coord i s = s := (r1 rfl (prime_p.2.2 _ · ⟨·, ·⟩ |>.resolve_left c.not_p_dvd_z) _ (let := Quotient.field c.maxIdeal
  by simpa [mem_span_pair_iff, ← isUnit_iff_dvd_one] using! c.4)).imp fun d h ↦ (h (mem_singleton 1)).imp fun i e s ↦ by simpa [e, c.S.smul_def] using d.5 i (.single i s)
def adicBasis := c.z1.choose
def oneIndex := c.z1.choose_spec.choose
abbrev coord₀ := c.adicBasis.coord c.oneIndex
lemma coord₀_coe : ∀ s, c.coord₀ s.1 = s := c.z1.choose_spec.choose_spec
lemma dvd_iff_coe_dvd {a b : c.S} : a ∣ b ↔ a.1 ∣ b := ⟨map_dvd c.S.val, (c.coord₀_coe b ▸ ·.choose_spec ▸ ⟨_, map_smul _ a _⟩)⟩
def φ : c.S →+* c.S := (frobEnd.comp c.S.val.1).codRestrict _ (let F := c.seriesMap.comp (expand p out)
  have := q4 (a := F X) (by simp [F, c.4])
  (⟨_, mem_range_of_approx F.toAddMonoidHom (F.toSemilinearMap.2 X) _ (c.exists_z_dvd_sub_const ·
  |>.rec fun a ⟨t, e⟩ ↦ (a.j7 _).imp' C fun _ _ ↦ ⟨t, by
  simpa [F, e, C_eq_algebraMap, z, seriesMap_X]⟩) · |>.choose_spec⟩))
def frobE n := (c.φ ^ n) c.E
lemma coe_φ_pow n : ∀ r, ((c.φ ^ n) r).1 = frobEnd^[n] ↑r := by induction n <;> aesop
lemma dvd_smul_sub_of_fixesLambda {d} (h : d ∣ g • c.z.1 - c.z) (k : FixesLambda c.f g) (s : c.S) : d ∣ g • s - s := have := q4 c.4
  (mem_range_of_approx (.mulLeft d) (mul_smul_comm (c.seriesMap X) _) (g • (↑) - (↑)) (c.exists_z_dvd_sub_const · |>.rec fun a ⟨t, e⟩ ↦ (h.mul_right (g • t)).imp fun _ ↦ (⟨t, by
  simp [*, ← ·, sub_mul, z]⟩)) s).rec Dvd.intro
lemma smul_theta_of_fixesThetaZ (h : c.FixesThetaZ g) (s : c.S) : g • theta s = theta s := by simpa [← theta_eq_zero_iff_xi_dvd, h] using (c.dvd_smul_sub_of_fixesLambda (d := xi) · h.1 s)
open Polynomial hiding C X
lemma w4 n {N} (e : p ^ n * c.e = N) s : ∃! r : (WittFq c.f)[X]_N, c.frobE n ∣ s - r.1.aeval c.z := by
  obtain ⟨h, rfl⟩ : let g := (c.x5.symm (c.frobE n)).map (residue _)
    g ≠ 0 ∧ g.order.toNat = N := by simp [frobE, order_mul, ← pow_mul, -RingHom.coe_pow, e, by
    simpa using congrArg C ((residue_eq_zero_iff (p : WittFq c.f)).2 (irreducible p).1), IsUnit.ne_zero, ((c.φ ^ n) c.z).ext (a2 := c.z ^ p ^ n) (by simp [↓coe_φ_pow, z_eq_teichmuller]), order_zero_of_isUnit]
  simpa [← map_dvd_iff c.x5.symm, ← aeval_algHom_apply, dvd_def, sub_eq_iff_eq_add, aeval_def X, eval₂_C_X_eq_coe, ExistsUnique, mem_degreeLT] using (@exists_isWeierstrassDivision _ _ _ _ _ ((irreducible p).maximalIdeal_eq.substr inferInstance) h).rec fun _ ⟨_, H⟩ ↦ ⟨_, ⟨_, H.2⟩, H.1, fun _ a _ b ↦ (H.elim h ⟨a, b⟩).2.symm⟩
lemma exists_dvd_sub_sum_z_pow n {N} (e : p ^ n * c.e = N) s : ∃ w : Fin N → WittFq c.f, c.frobE n ∣ s - ∑ i, w i • c.z ^ i.1 := by simpa [(degreeLT.basis ..).equivFun.exists_congr_left] using (c.w4 n e s).exists
end Chart
end Lift
open Matrix nonZeroDivisors BdRPlus IsDiscreteValuationRing IsScalarTower Finset RingHom Function Units Filter algebraMap
variable {p} [ThePrime p] {ι} [Fintype ι] {A} [CommRing A] [Algebra A (PadicAlgCl p)] [Algebra A BdR] [IsScalarTower A (PadicAlgCl p) BdR]
def hodgeMatrix (W : Matrix ι ι BdRPlus) (k : ι → ℤ) := W.map (↑) * diagonal (tUnit ^ k · |>.1)
abbrev IsHodgeTateFrame (N P : Matrix ι ι ℂ_[p]) (k : ι → ℤ) g := ∀ w, P *ᵥ (fun i ↦ (cyclotomicGp g ^ (-k i)).1 • g • w i) = N *ᵥ g • P *ᵥ w
attribute [local simp] hodgeMatrix smul_sum comp_def Matrix.mul_apply diagonal dotProduct mul_sum mulVec sum_mul mul_assoc Algebra.smul_def
lemma isHodgeTateFrame_of_hodgeMatrix {W k} {N : Matrix ι ι A} {g} (h : N.map (↑) * g • hodgeMatrix W k = hodgeMatrix W k) : IsHodgeTateFrame (N.map ((↑) : A → PadicAlgCl p)) (W.map thetaBdR) k g := fun _ ↦ by ext i; simpa [← (by simpa [algebraMap_apply A (PadicAlgCl p) BdR, y6, ← mul_assoc, ← sum_mul, ← map_mul, ← map_sum, algebraMap_apply _ BdRPlus BdR, -val_zpow_eq_zpow_val] using congrFun₂ h i)] using! sum_comm
lemma exists_hodge_frame Γ [Group Γ] [OverGp Γ p] {F} (hF : nearOne Γ ≤ F) {U} {N : Γ → Matrix ι ι
  A} (hU : IsUnit U) (h : ∀ᶠ g in F, (N g).map ((↑) : A → BdR) * U.map (toGp g • ·) = U) : ∃ Y :
  SpecialLinearGroup ι _, ∃ W k, IsUnit W ∧ (∀ᶠ g in F, Y.1.map (toGp g) = Y) ∧ U * Y.1.map (↑) = hodgeMatrix W k ∧ (∀ᶠ g in F, (N g).map (↑) * toGp g • hodgeMatrix W k = hodgeMatrix W k) ∧ ∀ i l, ‖Y i l‖ ≤ 1 := by
  choose b W hW using IsLocalization.exist_integer_multiples_of_finite BdRPlus⁰ U.uncurry
  have t := m1
  let ⟨d, u, hu⟩ := eq_unit_mul_pow_irreducible (ne_zero b.2) t.irreducible
  refine ((InvImage.wf det wellFounded_dvdNotUnit).has_min {W | ∃ Y k, Y.1 ∈ (intQpBar p).matrix ∧ _ ∧ _} ⟨of (u.2 • W.curry), 1, -↑d, by
    have := t.1; simp [← ext_iff, *, tUnit, uncurry, field]⟩).elim
    fun W ⟨⟨Y, k, hY, hg, e⟩, hm⟩ ↦ ⟨Y, W, k, (fun H ↦ ⟨?_, hg, e, H, hY⟩) (h.mp (hg.mono fun g y h ↦ e ▸ .trans (by simp [← ext_iff]) congr($h * $(y).map _)))⟩
  simp [isUnit_iff_isUnit_det, thetaBdR.map_det, ← exists_mulVec_eq_zero_iff]
  refine fun _ ↦ mt (le_of_hodgeTate_stable ((nhds_one_le_map_nearOne Γ).trans (map_mono hF)) _ (toLin' _).ker ⊥ (fun v y ↦ H.mono fun _ h ↦ (isHodgeTateFrame_of_hodgeMatrix h v).trans (by aesop)) (fun a i z n _ _ f ↦ ?_) ·)
  choose V w using fun m ↦ j6.dvd'.trans ((j8 (x := (↑) ∘ a ⬝ᵥ W m)).1 (by simpa [mul_comm] using congr($z m)))
  have hd := (funext w ▸ det_updateCol_sum W i _).symm.trans (det_updateCol_smul ..)
  simp [*, mul_comm] at hd
  cases hm _ ⟨⟨Y * updateCol 1 i a, by simpa [← cramer_apply]⟩, k + Pi.single i 1, mul_mem hY (by simpa [updateCol_apply, ite_mem, one_apply] using! n ·), (hg.and (.all f)).mono (by simp_all [map_updateCol]), by
    simp [← mul_assoc]; ext _ l; by_cases l = i <;> simp [one_apply, zpow_add₀, *]
    erw [mul_rotate', ← map_mul, ← w]; simp [← IsScalarTower.algebraMap_apply]; grind⟩ ⟨((hU.map detMonoidHom).ne_zero <| by simpa [← map_det, ← mapMatrix_apply, ·, *] using congr(det $e)), _, t.2.1, mul_comm x4 _ ▸ hd⟩
