import Lib.General.Algebra.SuccessiveApprox
import Lib.PadicHodge.PeriodRings.Ainf
noncomputable section
attribute [local instance high] RingHomClass.toMonoidHomClass SubringClass.toSubsemiringClass
attribute [-simp] pow_eq_one_iff IsUnit.dvd map_eq_zero map_smul
open WittVector IsLocalRing MulSemiringAction ZMod Set
variable {p} [ThePrime p]
def toWittResidue : Ainf →ₐ[ℤ_[p]] WittVector p (ResidueField OFlat) := ⟨map (residue _), q9 _⟩
variable {k} [CommRing k] [CharP k p] [PerfectRing k p] {a c : WittVector p k}
lemma Witt.p_dvd_iff : ↑p ∣ a ↔ constantCoeff a = 0 := by simp [← Ideal.mem_span_singleton, ← ker_constantCoeff]
omit [PerfectRing k p] in
lemma Ainf.isUnit_iff_isUnit_constantCoeff : IsUnit a ↔ IsUnit (constantCoeff a) := ⟨.map _, (⟨mkUnit ·.unit_spec.symm, rfl⟩)⟩
lemma Witt.w8 (F G : k →+* k) s (h : (F - constantCoeff s • ⇑G).Surjective) : ∃ b, map F b - s * map G b = a := mem_range_of_approx ((map F).toAddMonoidHom - .comp (.mulLeft s) (map G).toAddMonoidHom) (map_natCast_smul _ (type_of% s) (type_of% s) p) id (·.1 0 |> h |>.imp' (teichmuller p) (by simp_all [← sub_eq_iff_eq_add', ← dvd_def, p_dvd_iff, map_sub, map_mul])) a
open Ideal Witt Function RingHom PadicComplex Pi OFlat NeZero Fact SModEq IsUltrametricDist
lemma Witt.y0 [Nontrivial k] [h : IsAIC k] s a : ∃ y : WittVector p k, frobenius y - s * y = a := frobenius_eq_map_frobenius p (R := k) ▸ w8 _ 1 s (h.exists_pow_sub_mul_eq p _)
lemma Witt.y3 {m} : p.cast ^ m ∣ a - c ↔ ∀ i < m, a.1 i = c.1 i := by rw [← mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero, le_coeff_eq_iff_le_sub_coeff_eq_zero]
lemma Witt.mem_span_pair_iff : a ∈ span {↑p, c} ↔ constantCoeff c ∣ constantCoeff a := by simp [span_insert, ← ker_constantCoeff, sup_comm, mem_span_singleton, ← comap_map_of_surjective', constantCoeff_surjective]
lemma Witt.dvd_of_mem_of_constantCoeff_dvd {I : Ideal _} (hc : c ∈ I) (hp : ∀ x, p.cast * x ∈ I → x ∈ I) (h : ∀ a ∈ I, constantCoeff c ∣ constantCoeff a) : ∀ a ∈ I, c ∣ a := by simpa [eq_comm]
  using! (mem_range_of_approx (.mulLeft c) (mul_smul_comm (p : type_of% c) c) I.subtype fun ⟨x, k⟩ ↦
  have ⟨a, b, _⟩ := mem_span_pair.1 (mem_span_pair_iff.2 (h x k))
  ⟨b, ⟨a, by grind [mul_mem_left, add_mem_cancel_right]⟩, by simp; grind⟩)
variable (g : Gp p) (m : FrobGal) (t : OFlat) (a : Ainf)
lemma frobEnd_eq_frobenius : frobEnd a = frobenius a := by ext; simpa using! v9 _
lemma smul_teichmuller : m • teichmuller p t = teichmuller p (m • t) := map_teichmuller ..
@[simp] lemma b0 : frobEnd (teichmuller p t) = teichmuller p t ^ p := by erw [map_teichmuller, v9, map_pow]
lemma untilt_frobGal_smul : (m • t).untilt = (m.2 • t.untilt) ^ p ^ m.1.toAdd := by erw [map_pow]; simp
@[simp] lemma theta_smul : theta (g • a) = g • theta a := (fontaineTheta_map_tiltMap (toRingHom ..) a).subst (by congr with; apply pow_one)
lemma r0 : constantCoeff (frobEnd a) = constantCoeff a ^ p := v9 _
variable {c a δ y : Ainf}
open Ainf Multiplicative
lemma associated_smul_of_dvd (h : ∀ g : Gp p, a ∣ g • a) : Associated (g • a) a := associated_of_dvd_dvd (by simpa using map_dvd (toRingHom _ _ g) (h g⁻¹)) (h g)
attribute [local simp] p_dvd_iff epsTilt tau r0 algebraMap_toAlgebra Ainf.isUnit_iff_isUnit_constantCoeff mem_span_pair_iff toWittResidue map_sub associated_smul_of_dvd mu epsRoot faithfulSMul_iff_algebraMap_injective
instance : FaithfulSMul ℤ_[p] (WittVector p k) :=
  by simpa using map_injective _ (castHom_injective k)
lemma z6 (h : theta c = 0) (h' : (constantCoeff c).untilt ∣ p) : theta a = 0 ↔ c ∣ a := ⟨dvd_of_mem_of_constantCoeff_dvd (mem_ker.2 h) (by simp [ne]) (fun _ _ ↦ untilt_dvd_iff.1 (h'.trans (by simp_all [← Quotient.eq_zero_iff_dvd, ← mk_fontaineTheta]))) a, by simp_all [dvd_def]⟩
instance : FaithfulSMul Ainf WittCFlat := by simpa using map_injective _ (by aesop_cat)
lemma isUnit_WittCFlat_of_not_p_dvd (h : ¬↑p ∣ a) : IsUnit (algebraMap _ WittCFlat a) := by simp_all [WittCFlat]
lemma exists_algebraMap_eq_of_frobenius_eq {k} [CommRing k] [IsDomain k] [CharP k p] (a : WittVector p k) (h : frobenius a = a) : ∃ c, algebraMap ℤ_[p] _ c = a := .imp' (equiv p ⟨·⟩) (by aesop)
  (Classical.skolem.1 ((GaloisField.splits_zmod_X_pow_sub_X p).mem_range_of_isRoot (i := castHom _ k) (FiniteField.X_pow_card_sub_X_ne_zero _ out) <| by simpa using congr(coeff $h ·)))
lemma z4 : Bijective (frobEnd : Ainf → _) := funext frobEnd_eq_frobenius ▸ frobenius_bijective ..
lemma theta_surjective : Surjective theta := fontaineTheta_surjective_of_isAIC
@[simp] lemma y9 : frobEnd tau = mu := by simp
@[simp] lemma r8 : theta tau ≠ 0 := by simp [(isPrimitiveRoot_untilt_epsPow _).ne_one, ne, elim]
@[simp] private lemma y4 j : theta (frobEnd^[j] mu) = 0 := by induction j <;> simp_all [-epsTilt]
lemma theta_iterate_frobEnd_xi j : theta (frobEnd^[j + 1] xi) = p := by have := y4 j; simp_all [← coe_pow, xi]
@[simp] lemma theta_xi : theta xi = 0 := by simpa [-tau, ↓← xi_mul_tau] using y4 0
lemma toWittResidue_tau : toWittResidue tau = 0 := (by simp_all [← isUnit_map_iff (residue _)] : ¬IsUnit tau → _) (by simpa [-tau, -epsTilt] using ·.map (theta.comp frobEnd))
lemma v0 : Associated ↑p (xi - teichmuller p (constantCoeff xi)) := Dvd.elim (by simp) fun u e ↦ ⟨IsUnit.unit (by have := toWittResidue_tau; apply_fun toWittResidue at e; simp_all [← map_coeff, p_nonzero, xi, CharP.cast_eq_zero, ← isUnit_map_iff (residue _)]), e.symm⟩
attribute [local simp] mul_assoc mul_pow isUnit_iff_dvd_one
lemma untilt_constantCoeff_xi_dvd_p : xi.constantCoeff.untilt ∣ p := by simpa using (v0.map theta).dvd'
variable {t g}
lemma toWittResidue_smul_of_isFrob {m} (h : IsFrob (intQpBar p) (p ^ m) g⁻¹) a : toWittResidue ((ofAdd m, g) • a) = toWittResidue a := .symm (ext fun n ↦ sub_mem.2 fun u ↦ absurd (@(g • (a.1 n).untilt).1.induction_on _ _ _ (isClosed_imp (isOpen_closedBall 0 (ne 1)) ((isClosed_ball 0 1).preimage (.fun_sub (continuous_const_smul g⁻¹) (continuous_pow _)))) (by simpa [↓smul_coe_Cp, coe_eq, ← map_pow, ← map_sub] using! h.2) (by simp [← b8]))
  (by simpa [untilt_frobGal_smul, OC.dvd_iff_norm_le] using (isUnit_iff_isUnit_constantCoeff.2 ((map_sub _ (teichmuller p _) (teichmuller p _)).symm.subst u)).map theta))
lemma not_p_dvd_tau : ¬↑p ∣ tau := r8 ∘ by aesop
attribute [-simp] constantCoeff_apply tau mu
lemma q2 : constantCoeff mu ≠ 0 := by simpa [← y9, ne] using not_p_dvd_tau
lemma theta_eq_zero_iff_xi_dvd : theta a = 0 ↔ xi ∣ a := z6 theta_xi untilt_constantCoeff_xi_dvd_p
attribute [local simp ←] theta_eq_zero_iff_xi_dvd xi_mul_tau mk_fontaineTheta
@[simp] lemma not_p_dvd_xi : ¬↑p ∣ xi := q2 ∘ by aesop
lemma OFlat.exists_dvd_pow {u} (h : ¬IsUnit u) (k : t ≠ 0) : ∃ n, t ∣ u ^ n := by simp_all [OFlat, ← zero_dvd_iff, ← untilt_dvd_iff, OC.exists_dvd_pow, ← theta_teichmuller]
lemma OFlat.q3 (h : ¬IsUnit t) : IsHausdorff (span {t}) OFlat ∧ Surjective (shiftDiff OFlat t) := by
  choose N H using fun k ↦ (exists_dvd_pow h (pow_ne_zero (p ^ k) q2)).imp
    fun _ ↦ (by simpa [OFlat, ← iterate_frobenius, PreTilt.coeff_iterate_frobenius', constantCoeff_apply, id theta_xi] using map_dvd (PreTilt.coeff k) ·)
  use ⟨fun x e ↦ Perfection.ext fun k ↦ by
    simpa [H] using! map_dvd (PreTilt.coeff k) (smodEq_span_pow_iff_dvd.1 (e (N k)))⟩, fun b ↦ ?_
  choose u hu U using fun k ↦ ((Module.End.isUnit_iff (1 - t.coeff k • LinearMap.funLeft (ModP OC p) _ .succ)).1 (IsNilpotent.isUnit_one_sub ⟨N k, by simp [smul_pow, H]⟩)).existsUnique
    (b · |>.coeff k)
  exact ⟨(⟨_, fun k ↦ congrFun (U k _ (by simpa [funext_iff, sub_pow_char] using congr($(hu k.succ) ^ p))) ·⟩), funext fun n ↦ Perfection.ext (congr($(hu ·) n))⟩
lemma v2 (h : ∀ j, theta (frobEnd^[j] a) = 0) : mu ∣ a := by
  apply dvd_of_mem_of_constantCoeff_dvd (I := ⨅ j, ker (theta.comp (frobEnd ^ j))) <;>
    simp [ne p, h, iterate_fixed, -xi_mul_tau]
  by_contra! ⟨a, h, this⟩; choose c e using (ValuationRing.dvd_total ..).resolve_left this
  refine q2 ((c.q3 (by aesop)).1.1 _
    fun n ↦ ?_)
  grw [smodEq_span_pow_iff_dvd, @n.lt_pow_self p out]; clear this; induction' n with _ ih generalizing a c; aesop; obtain ⟨b, rfl⟩ := theta_eq_zero_iff_xi_dvd.1 (h 0)
  exact pow_mul' c .. ▸ ih (frobEnd b)
    (by simpa [-iterate_succ, theta_iterate_frobEnd_xi, ne] using! h ·.succ) _ (y9 ▸ by simp_all [← p_dvd_iff, -y9])
lemma tau_dvd_of_theta_frobEnd (h : ∀ j, theta (frobEnd^[j + 1] a) = 0) : tau ∣ a := (map_dvd_iff (MulEquiv.ofBijective _ z4)).1 (y9 ▸ v2 h)
lemma Ainf.prime_p : Prime (p : Ainf) := by simp [Prime, p_nonzero]
lemma Ainf.mem_radical_of_not_isUnit (h : ¬IsUnit a) (hδ : ¬↑p ∣ δ) : a ∈ radical (span {↑p, δ}) := by simp_all [radical, exists_dvd_pow, ↓isUnit_iff_isUnit_constantCoeff]
lemma Ainf.exists_frobEnd_sub_xi_pow_mul_eq n x : ∃ c, frobEnd c - xi ^ n * c = x := by simp [frobEnd_eq_frobenius, y0, isAIC]
lemma m0 (ha : ¬IsUnit a) (hc : ¬IsUnit c) (hδ : ¬↑p ∣ δ) (h : ∀ m, ∃ x, y - δ * x ∈ span {a, c} ^ m) : δ ∣ y := dvd_of_mem_of_constantCoeff_dvd (I := ⨅ m, span {↑(p ^ m), δ}) (by aesop)
  (by simpa [mem_span_insert', mem_span_singleton] using fun _ h m ↦ (h m.succ).imp fun _ _ ↦ (prime_p.left_dvd_or_dvd_right_of_dvd_mul (by grind)).resolve_left hδ) (fun _ ↦ (by
  simpa using mem_iInf.1 · 1)) y (mem_iInf.2 fun m ↦ (Submodule.sub_mem_iff_left _ (mul_mem_right _ _ (by bound))).1 ((exists_pow_le_of_le_radical_of_fg (span_le.2 fun _ _ ↦ radical_le_radical_iff.2
  (span_le.2 (pair_subset ⟨m, by bound⟩ ⟨1, by bound⟩)) (mem_radical_of_not_isUnit (by
  grind) hδ)) ⟨{a, c}, by simp⟩).choose_spec (h _).choose_spec))
lemma Ainf.r2 (h : ¬IsUnit a) : Surjective (shiftDiff Ainf a) := fun b ↦ (@w8 p _ _ _ _ ⟨(bijective_frobenius ..).comp_left⟩ ⟨swap (b · |>.1)⟩ 1 (.pi (evalRingHom _ ·.succ)) (algebraMap _ _ a) (q3 (h ∘ isUnit_iff_isUnit_constantCoeff.2)).2).imp' _
  fun _ e ↦ funext (by simpa using! congr(($e).map <| evalRingHom _ ·))
lemma Ainf.prime_xi : Prime xi := ⟨q2 ∘ by aesop, by simp⟩
lemma y1 : Associated (g • tau) tau := by simp [tau_dvd_of_theta_frobEnd, ← Commute.iterate_right (smul_frobEnd _) .., -xi_mul_tau]
lemma smul_xi_mem_span : m • xi ∈ span {↑p, xi} := mem_span_pair_iff.2
  ((map_dvd _ (by simp : xi ∣ m.2 • xi)).trans (pow_dvd_pow _ one_le))
lemma Ainf.j9 (h : ¬IsUnit a) (k : ¬IsUnit c) : IsAdicComplete (span {a, c}) Ainf := { isPrecomplete_of_shiftDiff_surjective
  (r2 h) (r2 k) with haus' x e := by_contra (by
  choose n y _ _ using exists_eq_pow_p_mul x ·
  have := m0 h k (prime_p.not_dvd_mul not_p_dvd_xi (by simpa))
    (⟨0, by simpa [zero] using e ·⟩)
  simp_all [mul_dvd_mul_iff_right]) }
lemma Ainf.q4 (h : ¬IsUnit a) : IsAdicComplete (span {a}) Ainf := by simpa using j9 h h
instance : IsAdicComplete (span {↑p, xi}) Ainf := by simp [j9]
