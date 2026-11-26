import Lib.ClassField.Places.CyclotomicCharacter
import Lib.PadicHodge.PeriodRings.ThetaKernel
noncomputable section
section
attribute [-simp] sup_of_le_right sup_of_le_left
open Quot Ideal Submodule Finsupp AdicCompletion SModEq Function Module
variable {S F M} [CommRing S] [AddCommGroup F] [Module S F] [AddCommGroup M] [Module S M] {C} [AddCommGroup C] [Module S C] (I : Ideal S) [IsAdicComplete I C] (β : F →ₗ[S] M)
instance [IsPrecomplete I S] [Module.Finite S M] : IsPrecomplete I M := of_surjective_iff.1 (by simpa using (ofTensorProduct_surjective_of_finite I M).comp (TensorProduct.mk_surjective _ M _ (of_surjective I S)) ·)
lemma isHausdorff_of_injective_pi [IsHausdorff I F] {ι} (f : M →ₗ[S] ι → F) (h : Injective f := by simp) : IsHausdorff
  I M := of_injective_iff.1 fun _ _ e ↦ h <| funext fun i ↦ of_inj.1 <| (map_of ..).symm.trans <| (congrArg (AdicCompletion.map I (.proj i ∘ₗ f)) e).trans (map_of ..)
lemma isAdicComplete_of_free [IsAdicComplete I S] [Free S M] [Module.Finite S M] : IsAdicComplete I M := {isHausdorff_of_injective_pi I _ (Free.chooseBasis ..).equivFun.injective with}
lemma k9 (g : F →ₗ[S] C) (h₁ : Surjective (mkQ (I • ⊤) ∘ₗ β)) (h₂ : ∀ n, comap β (I ^ (n + n) • ⊤) ≤ comap g (I ^ n • ⊤)) : ∃ G : M →ₗ[S] C, ∀ f, G (β f) = g f := ⟨(ofLinearEquiv I _).symm.1 ∘ₗ (LinearMap.quotKerEquivOfSurjective _ (map_surjective_of_mkQ_comp_surjective h₁)).congrLeft _ ℕ (liftQ _ (map I g) ((mk_surjective I F).forall.2 fun a h ↦ ext (((a.map I g).2 (by simp)).trans <| zero.2 <| h₂ · (zero.1
  congr($h.1 _) :)))) ∘ₗ of I _, by simp [← map_of, LinearEquiv.symm_apply_eq]⟩
attribute [local simp] Ideal.span_insert pow_succ' mul_smul sup_smul mem_sup span_smul_eq
private lemma k3 {a} (t : S) (k : comap β (span {a, t} • ⊤) ≤ span {a, t} • ⊤) (h : ∀ y w : M, a • w = t • y → t = 0 ∨ ∃ c, a • c = y) n : comap β (span {t ^ n, a} • ⊤) ≤ span {t ^ n, a}
  • ⊤ := by induction' n with n i <;> simp_all [top_sup_eq, LE.le, mem_singleton_set_smul, add_comm]
            exact fun x v u e ↦ (k _ _ e).elim fun u' ⟨c, _⟩ ↦ (h (β c - t ^ n • v) (u - β u') (by grind [smul_sub, map_smul])).rec (by bound) fun ⟨w, _⟩ ↦ (@i c v w (by grind)).imp
              fun _ ↦ .imp' (u' + t • ·) (by grind [smul_add, smul_comm])
structure Lift.AdicBasis.{u} (M : Type u) [AddCommGroup M] [Module S M] where
  (Index : Type u) (b : Index → M) (coord : Index → M →ₗ[S] S)
  dense : Surjective (mkQ (I • ⊤) ∘ₗ linearCombination S b)
  dual i f : coord i (linearCombination S b f) = f i
lemma Lift.r1 {I p z} (hI : I = span {p, z}) [I.IsMaximal] [IsAdicComplete I S] (hz : ∀ a b : M, z • a = p • b → ∃ c, a = p • c) (t : Set M := ∅) (ht : LinearIndepOn (S ⧸ I) (I • ⊤ : Submodule S M).mkQ t := by simp) (hp : ∀ a : M, p • a = 0 → p = 0 ∨ a = 0 := by aesop) : ∃ c : AdicBasis I M, t ⊆ .range c.b := let := Quotient.field I
  by choose s _ _ hs li using exists_linearIndepOn_extension ht le_top
     use ⟨s, (↑), _, ?a, fun i ↦ (k9 I _ (lapply i) ?a fun n x h ↦ smul_top_le_comap_smul_top _ _ (smul_mono_left ?_ (k3 _ p (k3 _ z (hI ▸ fun x ↦ by simpa [← submodule_top, ← submodule_smul, Quotient.eq_zero_iff_mem] using! linearIndependent_iff''.1 li _ (x ·) (by aesop) ∘ (map_sum (mkQ _) ..).symm.trans ∘ zero.2)
    (by grind) n) (n.rec (by simp) (by simp_intro n i y w e; cases hz _ _ e; grind [hp (y - z • ‹M›), smul_sub, smul_comm])) n (smul_mono_left ?_ h)))).choose_spec⟩, by simpa
     exact ind (by simpa [mem_span_iff_linearCombination] using! (restrictScalars_span S _ mk_surjective _).le <| hs ⟨·, ⟨⟩, rfl⟩)
     all_goals simp [*, ← span_singleton_pow, pow_right_mono, sup_pow_add_le_pow_sup_pow]
abbrev nsmulRange n X [AddCommGroup X] := (@nsmulAddMonoidHom X _ n).range
variable {X Y} {S : _} [AddCommGroup X] [AddCommGroup Y] [CommRing S] [Module S X] [Module S Y]
lemma nsmulRange.map_mem (f : X →ₗ[S] Y) {n x} : x ∈ nsmulRange n X → f x ∈ nsmulRange n Y := by aesop
lemma nsmulRange.mem_span_pow_smul_top_iff {p : ℕ} {k x} : x ∈ Ideal.span {(p : S)} ^ k • (⊤ : Submodule S X) ↔ x ∈ nsmulRange (p ^ k) X := by simp [Ideal.span_singleton_pow, Submodule.span_smul_eq, Submodule.mem_singleton_set_smul, ← Nat.cast_smul_eq_nsmul S, eq_comm]
end
lemma free_finite_of_rank_le {S M : Type} [CommRing S] [Nontrivial S] [AddCommGroup M] [Module S M]
    {I : Ideal S} {p z} (hI : I = .span {p, z}) [I.IsMaximal] [IsAdicComplete I S] (H : IsHausdorff I M) (hz : ∀ x y : M, z • x = p • y → ∃ w, x = p • w) (d : ℕ) (hd : Module.rank S M ≤ d)
    (hp : ∀ x : M, p • x = 0 → p = 0 ∨ x = 0 := by simp) : Module.Free S M ∧ Module.Finite S M :=
  let ⟨c, _⟩ := Lift.r1 hI hz
  have li := linearIndependent_iff.2 (by simp_all [Finsupp.ext_iff, ← c.5])
  have := Cardinal.mk_lt_aleph0_iff.1 (by grw [li.cardinal_le_rank, hd]; simp)
  (fun e ↦ ⟨.of_equiv e, .equiv e⟩) (.ofBijective _ ⟨li, surjective_of_mkQ_comp_surjective c.4⟩)
namespace Lift.AdicBasis
open Finsupp Submodule AdicCompletion
variable {S A} [CommRing S] [AddCommGroup A] [Module S A] {I : Ideal S} (c : AdicBasis I A)
lemma coord_sub_mem_pow {n y f} (h : y - linearCombination S c.b f ∈ I ^ n • (⊤ : Submodule S A))
  i : c.coord i y - f i ∈ I ^ n := by simpa [dual] using smul_top_le_comap_smul_top _ (c.coord i) h
lemma eventually_sub_sum_mem y n : ∀ᶠ F in .atTop, y - ∑ i ∈ F, c.coord i y • c.b i ∈ I ^ n • (⊤ : Submodule S A) := Filter.mem_atTop_sets.2 (((map_surjective_of_mkQ_comp_surjective c.dense).comp (mk_surjective I _) (of I A y)).imp' (· n |>.1) fun f e F hF ↦ have hf := SModEq.sub_mem.1 congr($e.1 n).symm; (sub_mem_iff_right _ hf).1 (by simp [linearCombination_apply_of_mem_supported _ hF, sum_mem, ← F.sum_sub_distrib, ← sub_smul, smul_mem_smul, c.coord_sub_mem_pow hf]))
lemma m3 {P : Submodule S A} {n y} (hP : I ^ n • ⊤ ≤ P) (h : ∀ i, c.coord i y • c.b i ∈ P) : y ∈ P := by grind [sum_mem, sub_mem_iff_left, hP (c.eventually_sub_sum_mem y n).exists.choose_spec]
lemma eq_zero_of_coord [H : IsHausdorff I A] {y} (h : ∀ i, c.coord i y = 0) : y = 0 := H.1 _ (by simp_all [SModEq, c.m3 le_rfl])
end Lift.AdicBasis
attribute [-simp] map_smul isUnit_map_iff map_eq_zero Nat.cast_eq_zero IsUnit.dvd mul_eq_zero
open Ideal Polynomial AdjoinRoot nonZeroDivisors Localization IsScalarTower algebraMap
variable {p} [ThePrime p] (m : FrobGal) (a : Ainf) {R S} [CommRing R] [CommRing S] [Algebra R S]
def Amax := let A := AdjoinRoot (C p.cast * X - C xi); AdicCompletion (span {(p : A)}) A
deriving CommRing, Algebra Ainf, Algebra ℤ_[p], IsScalarTower ℤ_[p] Ainf
def BPlus := Away (p : Amax) deriving CommRing, Algebra Ainf, Algebra ℤ_[p], Algebra Amax, IsScalarTower ℤ_[p] Ainf, IsScalarTower Ainf Amax, IsScalarTower ℤ_[p] Amax
def Bcris := Away (algebraMap _ BPlus mu)
def BdRPlus := AdicCompletion (span {algebraMap _ BPlus xi}) BPlus
variable [Algebra R BPlus] [Algebra S BPlus] [IsScalarTower R S BPlus] in
deriving instance CommRing, Algebra R, IsScalarTower R S for @Bcris p _, @BdRPlus p _
attribute [instance 50] instAlgebraBcrisOfBPlus instAlgebraBdRPlusOfBPlus
instance [Algebra R Amax] : IsAdicComplete (span {(p : R)}) Amax := isAdicComplete_over_base isAdicComplete
def x1 := (toAlgHom Ainf Amax BPlus).range
def Amax.X : Amax := .of _ _ (root _)
open Amax IsLocalization Away Function MulSemiringAction Quotient Set
instance isLocalizationAway_p_bPlus : Away (p : Amax) BPlus := isLocalization
instance : Away (mu : BPlus) Bcris := isLocalization
@[simp] lemma BPlus.isUnit_p : IsUnit (p : BPlus) := mod_cast algebraMap_isUnit (p : Amax)
abbrev OC.toPadicIntAlgHom [Algebra ℤ_[p] R] (f : R →+* OC) : R →ₐ[ℤ_[p]] ℂ_[p] := ⟨𝓞_ℂ_[p].subtype.comp f, (congr($((ringHom_ext_of_approx (⟨_, by simp, mem_span_singleton.1 <| ·.appr_spec ·⟩) : f.comp _ = .codRestrict _ _ (by simpa using! (norm_algebraMap' ..).trans_le ·.2))) · |>.1))⟩
@[simp ←] lemma p_mul_X : p * X = xi := congr(.of _ _ $(sub_eq_zero.1 mk_self))
lemma Amax.j5 : ↑p ∈ Amax⁰ := mem_nonZeroDivisors_iff_left.2 fun _ ↦ IsSMulRegular.right_eq_zero_of_smul
  (isSMulRegular_completion (.of_right_eq_zero_of_smul (Quot.ind fun _ h ↦ ((prime_C_iff.2 Ainf.prime_p).left_dvd_or_dvd_right_of_dvd_mul (by simpa using mk_eq_zero.1 h)
  ).rec (by simpa using map_dvd constantCoeff ·) mk_eq_zero.2))) ∘ by simp
lemma Amax.exists_lift [IsAdicComplete (span {(p : R)}) R] (f : _ →+* R) x (h : f xi = p * x)
    : ∃ F : _ →+* R, (∀ a, F ↑a = f a) ∧ F X = x := ⟨(AdicCompletion.ofAlgEquiv (span {↑p})).symm.toRingHom.comp (adicMap (AdjoinRoot.lift f x (by aesop)) (by simp)), by
  and_intros <;> intros <;> erw [RingHom.comp_apply, adicMap_algebraMap] <;> simp⟩
lemma Amax.p_pow_dvd_of_mem_pow {n a} (h : a ∈ span {↑p, xi} ^ n) : (p : Amax) ^ n ∣ a
    := mem_span_singleton.1 ((span_singleton_pow ..).le (le_comap_pow _ _ (pow_right_mono (by simp [span_insert, mul_mem_right]) n h)))
lemma Amax.j2 a n : ∃ P : Ainf[X], p.cast ^ n ∣ a - aeval X P := by simpa [← aeval_eq, AdjoinRoot.mk_surjective.exists, ← aeval_algebraMap_apply] using! exists_approx a n
lemma Amax.q6 y n : ∃ d a w, (a : Ainf) = p ^ d * (y - p ^ n * w : Amax) := (y.j2 n).rec fun f ⟨c, h⟩ ↦ ⟨_, _, c, by simpa [p_mul_X, ← h] using! f.scaleRoots_eval₂_mul (algebraMap ..) X p⟩
attribute [local simp] IsUnit.pow smul_xi_mem_span NeZero.ne IsUnit.map
instance actAmax : MulSemiringAction FrobGal Amax := extendAction _ _ _ (fun _ ↦ (exists_lift ((algebraMap ..).comp (toRingHom ..)) _ (@pow_one .. ▸ p_pow_dvd_of_mem_pow (by simp)).choose_spec).choose_spec.1) fun h ↦ ringHom_ext_of_approx
  (q6 · · |>.rec fun _ ⟨a, _, e⟩ ↦ ⟨_, by simpa [e, pow_mem, mul_cancel_left_mem_nonZeroDivisors, j5] using (h a), _, sub_sub_self ..⟩)
instance : SMulDistribClass FrobGal Ainf Amax := smulDistribClass_of_tower (by delta actAmax; generalize_proofs; tauto)
instance actBPlus : MulSemiringAction FrobGal BPlus := locAction _ (p : Amax) (by simp)
instance : SMulDistribClass FrobGal Amax BPlus := smulDistribClass_of_tower (lift_eq _)
instance : SMulDistribClass FrobGal Ainf BPlus := smulDistribClass_of_tower (lift_eq _)
instance : Algebra ℚ_[p] BPlus := (IsLocalization.lift (g := algebraMap ℤ_[p] _) fun y : _⁰ ↦ PadicInt.unitCoeff_spec (coe_ne_zero y) ▸ by simp).toAlgebra
instance : IsScalarTower ℤ_[p] ℚ_[p] BPlus := of_algHom ⟨_, lift_eq _⟩
lemma z2 : Associated (p : Amax) ↑(frobEnd xi) := by
  rw [← add_eq_of_eq_sub' v0.choose_spec, map_add, algebraMap.coe_add, b0, (p_pow_dvd_of_mem_pow
    (pow_le_pow_right (Fact.out : 1 < p) (Ideal.pow_mem_pow ..))).choose_spec] <;>
    simp [sq, mul_assoc, ← mul_add, Witt.mem_span_pair_iff]
  exact ⟨(isUnit_of_dvd_sub (by simp) ⟨_, sub_eq_of_eq_add rfl⟩).unit, rfl⟩
lemma isUnit_smul_of_dvd_mu {a} (h : a ∣ mu) : IsUnit (↑(m • a) : Bcris) := @FrobGal.smul_def .. ▸ isUnit_of_dvd (mu : BPlus) (Iterate.rec _ (map_dvd _ (by grw [← toRingHom_apply, h, toRingHom_apply, ← y9, smul_frobEnd, y1.dvd])) (fun _ ↦ (isUnit_of_dvd _
  z2.dvd').dvd_mul_left.1 ∘ (by simpa [← xi_mul_tau] using! map_dvd frobEnd ·))
  _)
instance actBcris : MulSemiringAction FrobGal Bcris := locAction _ (mu : BPlus)
  (by simp [← algebraMap_apply, isUnit_smul_of_dvd_mu])
instance [SMul FrobGal R] [Algebra R BPlus] [SMulDistribClass FrobGal R BPlus] : SMulDistribClass FrobGal R Bcris := smulDistribClass_of_tower (lift_eq _)
def x2 := (exists_lift theta 0 (by simp)).choose
def thetaBPlus : BPlus →ₐ[ℚ_[p]] ℂ_[p] := (liftAlgHom ↑p (f := OC.toPadicIntAlgHom x2) (by simp)).extendScalarsOfIsLocalization _ _⁰
@[simp] private lemma b7 : x2 a = theta a := by grind [x2]
@[simp] lemma w1 (a : Amax) : thetaBPlus a = (x2 a).1 := lift_eq _ a
@[simp] lemma m6 : thetaBPlus a = (theta a).1 := (w1 _).trans (by simp)
private lemma x0 : Surjective thetaBPlus := (IsLocalization.lift_surjective_iff _).2
  (surj ↑p · |>.elim fun n ⟨a, _⟩ ↦ (theta_surjective a).rec fun b _ ↦ ⟨⟨b, _, n, rfl⟩, by simp_all⟩)
namespace Amax
variable {p : _} [ThePrime p] {f : Ainf[X]}
lemma k4 : ∃ F : _ →+* _, (∀ P, F (aeval X P) = P.map (Ideal.Quotient.mk (span {↑p, xi}))) ∧ ∀ y, ↑p ∣ y ↔ F y = 0 := have := by simpa [image_pair] using congr($(map_quotient_self (span {↑p, xi})).map C)
  (@exists_lift _ _ _ _ (by simpa [*] using {}) (algebraMap ..) .X (by aesop)).imp fun F H ↦ (⟨·, (j2 · 1 |>.rec fun P hP ↦ ⟨by simp_all [dvd_def], fun _ ↦ by
    obtain ⟨a, b, rfl⟩ := mem_span_pair.1 (by simpa [*, ext_iff, eq_zero_iff_mem, ← mem_map_C_iff, image_pair] using map_dvd F hP)
    simp_all [mul_left_comm, dvd_sub_left, dvd_add]⟩)⟩)
    (by simp [*, aeval_def, eval₂, sum, Polynomial.map])
lemma v5 (h : f.Monic) y m : p.cast ^ m ∣ aeval X f * y → p.cast ^ m ∣ y := pow_dvd_of_map
  (by grind) j5 (k4.rec (by simp_all [(h.map _).isRegular]))
lemma z3 {ν} (h : ∃ b, ν ∣ xi - p * b) n (y : Amax) : ∃ a z, p ^ n * y = (a : Ainf) + ν ^ n * z := h.rec fun b ⟨g, e⟩ ↦ n.rec ⟨0, by simp⟩ fun n ⟨a, z, k⟩ ↦ (mem_range_of_approx (s := ⟨fun y ↦ ((@Fact.out (shiftDiff _ _).Surjective).prodMap (g := shiftDiff _ _) Fact.out (_, _)).imp' ↿Function.prod fun _ ↦ congrArg ↿Function.prod⟩) ((algebraMap ..).toAddMonoidHom.coprod (.mulLeft _)) (map_natCast_smul _ Ainf ℤ p) id (by simpa using (j2 · 1 |>.rec fun P ⟨c, k⟩ ↦ ⟨_, _, c, by
  simpa using congr(aeval X $((P.modByMonic_add_div (.X - C b)).symm) + $k)⟩)) z).elim fun c l ↦ ⟨p
  * (a + ν ^ n * c.1), g * c.2, by replace e := congr(($e : Amax)); simp_all; grind⟩
lemma z0 {a : Ainf} {m} (h : (p : Amax) ^ m ∣ a) : a ∈ span {↑p, xi} ^ m := by induction m generalizing a; simp; choose c k using theta_surjective.exists.1 (map_dvd x2 h); cases (@theta_eq_zero_iff_xi_dvd p _ (a - p ^ ‹ℕ›.succ * c)).1 (by aesop); simp_all [pow_succ', mul_assoc, dvd_add_left, sub_eq_iff_eq_add, dvd_cancel_left_mem_nonZeroDivisors j5]; aesop (add 1% Ideal.mul_mem_mul, simp (v5 monic_X))
end Amax
end
noncomputable section
attribute [-simp] map_eq_zero isUnit_map_iff algebraMap.coe_inj IsUnit.dvd
open algebraMap Ideal Polynomial IsLocalization.Away IsScalarTower Algebra Amax Function BPlus
variable {p R} [ThePrime p] {y : BPlus} [CommRing R] [Algebra R BPlus] {x : BdRPlus} {a : Ainf}
attribute [local simp] IsUnit.pow smul_def theta_eq_zero_iff_xi_dvd sub_eq_iff_eq_add IsUnit.mul_right_inj IsUnit.mul_right_eq_zero mul_assoc mem_span_singleton mul_pow SModEq.sub_mem
attribute [local simp ←] IsScalarTower.algebraMap_apply mul_sub mul_sub_one
lemma injective_Amax_BPlus : Injective ((↑) : Amax → BPlus) := IsLocalization.injective _ (Submonoid.powers_le.2 j5)
lemma BPlus.exists_p_pow_mul_eq_amax : ∃ m b, p ^ m * y = (b : Amax) := by grind [surj (p : Amax) y, map_natCast]
lemma tau_dvd_xi_sub_p : tau ∣ xi - p := tau_dvd_of_theta_frobEnd (by simpa [iterate_fixed] using theta_iterate_frobEnd_xi)
lemma x1.y8 {e n} : e ∣ mu → e ^ n • y ∈ x1 → p ^ (2 * n) * y ∈ x1 := by
  grw [← xi_mul_tau, tau_dvd_xi_sub_p]
  exact fun ⟨t, k⟩ ⟨c, _⟩ ↦ let ⟨m, b, _⟩ := (p ^ (2 * n) * y).exists_p_pow_mul_eq_amax
    (b.v5 ((monic_X.mul (monic_X_sub_C 1)).pow n) m ⟨t ^ n • c, injective_Amax_BPlus (by
    replace k := congr(($k : Amax) ^ n • y)
    simp_all [pow_mul']; grind)⟩).imp (by aesop)
lemma BPlus.q0 y k n : ∃ m a, ∃ w ∈ x1, p ^ m * y = ↑(a : Ainf) + p ^ (m + k) * mu ^ n * w := y.exists_p_pow_mul_eq_amax.rec fun m ⟨b, _⟩ ↦ let ⟨d, c, w, _⟩ := b.q6 (m + k + n + n)
  let ⟨a, z, _⟩ := w.z3 ⟨1, tau_dvd_xi_sub_p.trans (by simp)⟩ n
  let ⟨e, x, _⟩ := z.z3 ⟨0, dvd_rfl⟩ n
  ⟨d + m, c + p ^ (d + m + k) * (p ^ n * a + tau ^ n * e), _, ⟨x, rfl⟩, by
  simp_all [← injective_Amax_BPlus.eq_iff, ← xi_mul_tau, pow_add, -p_mul_X]; grind⟩
@[simp] lemma BPlus.iterate_frobEnd_algebraMap j : frobEnd^[j] (a : BPlus) = frobEnd^[j] a := j.rec (by simp) (by aesop) a
lemma BPlus.dvd_of_thetaBPlus_frobEnd_eq_zero y {ν} {s : ℕ → ℕ} (H : ∀ {a}, (∀ j, theta (frobEnd^[s j] a) = 0) → ν ∣ a) (h : ∀ j, thetaBPlus (frobEnd^[s j] y) = 0) : ↑ν ∣ y := let ⟨n, a, z, _, e⟩ := y.q0 0 1
  by grw [← IsUnit.dvd_mul_left, e, dvd_add_right (map_dvd _ (H (by
            simpa [h] using congr(thetaBPlus <| frobEnd^[s ·] $e.symm)))), @H mu] <;> simp
@[local simp ←] private lemma k5 : thetaBPlus y = 0 ↔ ↑xi ∣ y := ⟨by simpa using @y.dvd_of_thetaBPlus_frobEnd_eq_zero p _ xi 0, by simp_all [dvd_def]⟩
lemma BPlus.eq_zero_of_forall_pow_dvd a (h : ∀ n, algebraMap _ _ (xi - p * a) ^ n ∣ y) : y = 0 := by
  by_contra; obtain ⟨⟨n, b, hb⟩, F, H⟩ := y.exists_p_pow_mul_eq_amax, Amax.k4
  obtain ⟨k, c, rfl, hc⟩ := exists_eq_pow_mul_of_not_forall_dvd ↑p b
    (mt _root_.eq_zero_of_forall_pow_dvd (by aesop : b ≠ 0))
  grw [algebraMap_apply _ Amax, Dvd.intro_left _ hb] at h; simp_all
  have t {n} : aeval _ ((.X - C a) ^ n) ∣ c := let ⟨w, _⟩ := h n
    w.exists_p_pow_mul_eq_amax.rec fun m ⟨d, _⟩ ↦ (d.v5 ((monic_X_sub_C a).pow
      n) m ⟨c, injective_Amax_BPlus (by simp; grind)⟩).imp fun _ _ ↦ injective_Amax_BPlus (by aesop)
  apply pow_rootMultiplicity_not_dvd hc; simpa [↓H] using map_dvd F t
instance : FaithfulSMul Ainf BPlus := .of_injective (ofId Ainf _) (injective_Amax_BPlus.comp (by simp_all [Injective, @IsHausdorff.eq_iff_smodEq _ _ (span {↑p, xi}) Ainf, z0]))
lemma BPlus.m4 : (mu : BPlus) ≠ 0 := mod_cast ne_zero_of_map q2
private def x3 := (quotientEquivAlgOfEq _ (by aesop : span {↑xi} = _)).trans
  (quotientKerAlgEquivOfSurjective x0)
def thetaBdR : BdRPlus →ₐ[ℚ_[p]] ℂ_[p] := .comp x3 ⟨(AdicCompletion.evalOneₐ _).1, by tauto⟩
@[simp] lemma w7 : thetaBdR y = thetaBPlus y := rfl
@[simp] private lemma d5 : thetaBdR a = (theta a).1 := m6 a
lemma BdRPlus.w2 {n} : (xi : BdRPlus) ^ n ∣ y ↔ (xi : BPlus) ^ n ∣ y := pow_dvd_iff (y := y)
open BdRPlus
lemma BdRPlus.w0 x n : ∃ y : BPlus, (xi : BdRPlus) ^ n ∣ x - y := exists_approx ..
lemma BdRPlus.q0 x n : ∃ m, ∃ r : Ainf, (xi : BdRPlus) ^ n ∣ p ^ m * x - r
  := (x.w0 n).rec fun z ⟨c, h⟩ ↦ (z.q0 0 n).imp fun m ⟨a, v, _, e⟩ ↦ ⟨a, by
  replace e := congr(($e : BdRPlus))
  simp_all [← xi_mul_tau, mul_add, ← add_sub, dvd_add, Dvd.dvd.mul_left]⟩
@[local simp ←] lemma j8 : thetaBdR x = 0 ↔ ↑xi ∣ x := by obtain ⟨_, _, _, _⟩ := @w2 (n := 1), x.w0 1; simp_all [dvd_add_right]
@[simp] lemma BdRPlus.isUnit_iff : IsUnit x ↔ thetaBdR x ≠ 0 := ⟨(·.map _ |>.ne_zero), isUnit_of_dvd_unit ⟨↑(surjInv x0 (thetaBdR x)⁻¹), rfl⟩ ∘ @isUnit_of_dvd_sub _ _ _ _ _ isAdicComplete isUnit_one ∘ j8.1 ∘ by simp_all [surjInv_eq]⟩
lemma BdRPlus.q5 (h : x ≠ 0) : ∃ n, Associated (xi ^ n : BdRPlus) x := (exists_eq_pow_mul_of_not_forall_dvd ↑xi x (h <| _root_.eq_zero_of_forall_pow_dvd ·)).imp (by simp_all [associated_mul_unit_right])
instance [FaithfulSMul R BPlus] : FaithfulSMul R BdRPlus := .of_injective (toAlgHom _ BPlus _)
  (.of_ker _ fun _ ↦ BPlus.eq_zero_of_forall_pow_dvd 0 ∘ by simp_all [← w2])
lemma BdRPlus.prime_xi : Prime (xi : BdRPlus) := by simp [Prime, Ainf.prime_xi.1]
instance : IsDomain BdRPlus := @NoZeroDivisors.to_isDomain _ _ ⟨_, _, prime_xi.1⟩ ⟨by
  by_contra! ⟨_, _, e, h, k⟩; simpa [e, ← map_pow, ← map_mul, Ainf.prime_xi.1] using (q5 h).choose_spec.mul_mul (q5 k).choose_spec⟩
instance : IsDiscreteValuationRing BdRPlus := .ofHasUnitMulPowIrreducibleFactorization ⟨_, prime_xi.irreducible, q5⟩
instance : IsDomain BPlus := .of_faithfulSMul _ BdRPlus
instance : IsDomain Amax := injective_Amax_BPlus.isDomain
instance : CharZero Amax := x2.charZero
instance : IsDomain Bcris := isDomain _ m4
lemma injective_BPlus_Bcris : Injective ((↑) : BPlus → Bcris) := IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors m4)
lemma Amax.nonempty_adicBasis (Λ : Type) [CommRing Λ] [Algebra Λ Amax] {I} (h : I = span {(p : Λ)})
    [I.IsMaximal] [IsAdicComplete I Λ] : Nonempty (Lift.AdicBasis I Amax) := (Lift.r1 (h ▸ span_insert_zero.symm) (by simp [NeZero.ne])).nonempty
end
seal Finset.univ Finset.sum Finset.prod
noncomputable section
namespace Lift
open WittVector Ideal RingHom Algebra algebraMap Valued IsLocalRing IsLocalization MonoidWithZeroHom.ValueGroup₀ Witt NeZero Metric Perfection OC nonZeroDivisors
variable {p} [ThePrime p]
def wittMaxIdeal := ker toWittResidue
lemma mem_wittMaxIdeal {a} : a ∈ wittMaxIdeal ↔ ∀ n, ¬IsUnit (a.coeff n) := by simp [wittMaxIdeal, toWittResidue, WittVector.ext_iff]
lemma teichmuller_mem_wittMaxIdeal {x} (h : ¬IsUnit x) : teichmuller p x ∈ wittMaxIdeal := mem_wittMaxIdeal.2 (·.rec h (by simp))
lemma WittCFlat.m2 (a d : WittCFlat) m : ∀ᶠ g : Gp p in nhds 1, ∃ b ∈ wittMaxIdeal, p.cast ^ m ∣ (g • a - a) * d - b := by
  delta WittCFlat at *; let := mk' (ValuationRing.valuation OFlat CFlat)
  have A (x : OFlat) : Continuous (· • x : Gp p → CFlat) := .of_at fun g s t ↦ (mem_nhds.1 t).rec
    fun γ h ↦ ((restrict₀_surjective _).comp (mk'_surjective OFlat⁰) γ.1).elim fun (c, e) k ↦ (not_forall.1 ((γ.ne_zero <| k ▸ by simp [·] : c ≠ 0) ∘ ext)).elim fun n H ↦ (tendsto_nhds.1 (continuousAt_id.smul_const (x.x6 n).1) ‖(p : OC)‖ (by simp [ne])).mono
    fun a b ↦ h (k ▸ v.restrict_lt_iff.2 (not_le.1 fun ⟨s, i⟩ ↦ H (by
    simp [eq_div_iff, smul_def, ← map_mul, ← map_sub, dist_eq_norm] at *
    erw [← i, map_mul, map_mul, map_sub, map_pow, map_pow, map_zero]
    simp [← coeff_tiltMap _ (x.r9 n), ← map_sub, (Quotient.eq_zero_iff_dvd ..).2, dvd_iff_norm_le, b.le, -map_smul])))
  let Z := (mk p (fun i ↦ (⟨(· • a.1 i), (mk'_surjective OFlat⁰ (a.1 i)).rec fun (c, e) ↦ (· ▸ by simpa
    [smul_div₀'] using! ((A c).div (A e) (by simp [smul_eq_zero_iff_eq])))⟩ : C(Gp p, _))) - a) * d
  have E g : Z.map (ContinuousMap.evalAlgHom ℤ _ g).1 = (g • a - a) * d := by aesop
  filter_upwards [(Finset.range m).eventually_all.2 fun i _ ↦ (Z.1 i).2.tendsto 1 (mem_nhds.2 ⟨1, fun y h ↦ ((v.restrict_lt_one_iff.1 h).rec fun ⟨c, e⟩ h ↦ ⟨⟨c, (h ⟨·.unit.inv, e ▸ by simp [smul_smul]⟩)⟩, e⟩ : ∃ c : maximalIdeal OFlat, c.1 • 1 = y - _)⟩)] with g h; choose! c _ using h; use ⟨(c ·)⟩, mem_wittMaxIdeal.2 (c · |>.2); simp_all [y3, algebraMap_toAlgebra, WittVector.ext_iff, Algebra.cast, smul_def]
end Lift
variable {p} [ThePrime p]
@[simp] lemma Lift.iterate_frobEnd_teichmuller (x : OFlat) n : frobEnd^[n] (WittVector.teichmuller p
  x) = .teichmuller p x ^ p ^ n := by induction n <;> simp_all; ring
lemma Lift.pow_p_pow_sub_mem_of_xi_dvd {x y} (h : xi ∣ x - y) m : x ^ p ^ m - y ^ p ^ m ∈ Ideal.span {↑p, xi} ^ m := Ideal.mul_le_left (SModEq.sub_mem.1 ((SModEq.sub_mem.2 (Ideal.mem_of_dvd _ h (by bound))).pow_pow_add_one (by bound) _))
lemma Lift.mu_sq_dvd_smul_mu_sub g : mu ^ 2 ∣ g • mu - (cyclotomicGp g).1 • mu := m0 Ainf.prime_p.2.1 Ainf.prime_xi.2.1 (q2 ∘ by simp [map_pow, Witt.p_dvd_iff]) fun m ↦ let u := WittVector.teichmuller p ((frobeniusEquiv _ p).symm^[m] epsTilt)
  (sq_dvd_add_pow_sub_sub mu 1 _).imp fun _ e ↦ Eq.subst (by
    simp [← smul_pow', ↓← e, cycChar_eq_of_equivariant p (g := g) (j := algebraMap ..) (smul_coe_Cp g · |>.symm), pow_right_comm, u, mu, ← map_pow, smul_sub]
    algebra) (sub_mem (@pow_p_pow_sub_mem_of_xi_dvd _ _ (g • u) (u ^ (cycCharMod ℂ_[p] (p ^ m) g).1.val) (by simpa [← theta_eq_zero_iff_xi_dvd, u, Subtype.ext_iff] using! (cycCharMod_spec g (mod_cast by simp [OFlat]))) m) (Ideal.mem_of_dvd _
    ((map_dvd (algebraMap ..) ((pow_dvd_cycChar_sub_iff m).2 zmod_eq_natCast_val)).mul_right mu) (by aesop (add 1% Ideal.pow_mem_pow))))
open Algebra NeZero algebraMap Ideal Amax IsScalarTower MulSemiringAction nonZeroDivisors AdicCompletion IsLocalization Away BdRPlus FormallySmooth BPlus IsFractionRing
lemma Amax.w6 {p} [ThePrime p] {u : Amax} (h : ↑p ∣ u) w : ∃ c, c - u * frobEnd c = w := mem_range_of_approx (.id _ - u • frobEnd.toAddMonoidHom) (map_zsmul _ p)
  id (⟨·, by simpa [← sub_eq_iff_eq_add'] using! h.mul_right _⟩) w
lemma exists_tPeriod {p} [ThePrime p] : ∃ t, Associated (mu * p : Amax) t ∧ frobEnd t = p * t ∧ ∀ g, g • t = (cyclotomicGp g).1 • t := z2.rec fun u a ↦ tau_dvd_xi_sub_p.rec fun w k ↦ let ⟨c, _⟩ := Amax.w6 ⟨u.1 ^ 2, rfl⟩ (frobEnd w); let t := mu * (p + mu * c)
    let ⟨e, h⟩ : mu * p * (u.1 + mu * u ^ 2 * frobEnd c) = t ∧ frobEnd t = p * t := by
      grind [map_natCast, j1, y9, xi_mul_tau, congr(frobEnd ($k : Amax))]
    ⟨t, ⟨(isUnit_of_dvd_sub u.isUnit (π := ↑p) (by simp [← xi_mul_tau, mul_assoc])).unit, e⟩, h, fun g ↦ (Lift.mu_sq_dvd_smul_mu_sub g).rec fun d k ↦ eq_of_forall_pow_dvd_sub p (.trans ⟨mu ^ 2,
      rfl⟩ <| ·.rec ⟨p * d + ((cyclotomicGp g).1 + mu * d) ^ 2 * g • c - (cyclotomicGp g).1 • c, by simp [t, eq_add_of_sub_eq k, smul_def]; ring!⟩ fun n ⟨z, H⟩ ↦ ⟨u ^ 2 * frobEnd z, mul_left_cancel₀ (ne ↑p) (by convert congr(frobEnd $H) <;> simp [← smul_frobEnd, h, ← congr(frobEnd $xi_mul_tau), ← a, smul_def] <;> simp [frobEnd] <;> ring)⟩)⟩
def x4 {p} [ThePrime p] : BdRPlus := exists_tPeriod.choose
lemma v4 {p} [ThePrime p] (V : Set _) n (u : Ainf) (hV : ∀ v ∈ V, v ∈ x1) (h : ∀ v ∈ V, ∃ w ∈ V, xi ^ n • v = u • frobEnd w) v (hv : v ∈ V) : ∃ a : Ainf, a = p ^ n.succ * v := by
  choose! y hy using hV; have := algebraMap_apply Ainf Amax BPlus
  choose a z H using fun k ↦ show ∃ a : Ainf, ∃ z, a = p ^ n.succ * y v - tau ^ n.succ * z * p ^ k by
    induction' k with k ih generalizing v; simpa [eq_sub_iff_add_eq, eq_comm] using (y v).z3 ⟨1, by simp [tau_dvd_xi_sub_p]⟩ _; obtain ⟨N, w, W, e⟩ := Ainf.prime_xi.1, h v hv; let ⟨c, z, C⟩ := ih w W
    refine (pow_dvd_of_map (x := u * frobEnd c) (n := n) (map_mul (algebraMap _ BPlus) _) (by simpa) (by simp [↓← k5, theta_eq_zero_iff_xi_dvd]) ⟨_, ?E⟩).imp fun d
      e ↦ ⟨u * X * frobEnd z, injective_Amax_BPlus (by simpa [e, N] using! ?E)⟩
    simp_all [smul_def, mul_pow, ← j1, j1 tau, ← xi_mul_tau]; grind
  peel by simpa [SModEq.sub_mem] using IsPrecomplete.prec' a fun h ↦ .sub_mem.2 ((mul_top _).ge (z0 (by simp [H, dvd_sub, (pow_dvd_pow _ h).trans])))
  simp_all [← eq_of_forall_pow_dvd_sub _ (by
    simpa [H, sub_right_comm, dvd_sub_left] using p_pow_dvd_of_mem_pow <| this ·)]
variable {p : _} [ThePrime p] (g : Gp p) {R} [CommRing R] [SMul (Gp p) R] [Algebra R BPlus] [SMulDistribClass (Gp p) R BPlus] (x : PadicAlgCl p) {S} [CommRing S] [SMul R S]
attribute [local simp ←] xi_mul_tau IsScalarTower.algebraMap_apply
attribute [-simp] map_smul smul_algebraMap p_mul_X
instance : SMulCommClass FrobGal ℚ_[p] Bcris := ⟨(map_smul <| toAlgHom _ _ · |>.extendScalarsOfIsLocalization _ ℤ_[p]⁰)⟩
instance actBdRPlus : MulSemiringAction (Gp p) BdRPlus := by
  apply actionOfHoms _ fun g ↦ adicMap (toRingHom _ _ g) (by simp [mem_span_singleton, ↓← k5])
    <;> intros <;> exact DFunLike.ext' (map_ext _ fun _ ↦ ext_evalₐ (by simp [mul_smul]))
instance : SMulDistribClass (Gp p) R BdRPlus := smulDistribClass_of_tower fun _ : BPlus ↦ by apply adicMap_algebraMap
@[instance_reducible] def BdR := FractionRing BdRPlus deriving Field
variable [Algebra R BdRPlus] [Algebra S BdRPlus] [IsScalarTower R S BdRPlus] [FaithfulSMul R BdRPlus] in
deriving instance Algebra R, IsScalarTower R S, IsFractionRing BdRPlus, FaithfulSMul R for @BdR p _
instance : CharZero BdR := charZero_of_charZero ℚ_[p] _
instance actBdR : MulSemiringAction (Gp p) BdR := mulSemiringAction _ BdRPlus _
instance : SMulDistribClass (Gp p) R BdR := smulDistribClass_of_tower fun _ : BdRPlus ↦ by simp
instance : Algebra Bcris BdR := (Away.lift _ ((coe_eq_zero_iff ..).ne.2 m4).isUnit).toAlgebra
instance : IsScalarTower R Bcris BdR := of_algebraMap_eq fun _ ↦ .symm (lift_eq _ _)
instance : FaithfulSMul Bcris BdR := .of_injective (ofId Bcris _)
  ((lift_injective_iff _).2 (by simp [injective_BPlus_Bcris.eq_iff]))
attribute [local instance] FormallyEtale.of_isSeparable
instance : Algebra (PadicAlgCl p) BdRPlus := (Exists.choose (exists_adicCompletionEvalOneₐ_comp_eq (x3.symm.toAlgHom.comp (algHom ..))) : _ →ₐ[ℚ_[p]] BdRPlus).toAlgebra
instance : IsScalarTower ℤ_[p] (PadicAlgCl p) BdRPlus := to₁₃₄ _ ℚ_[p] ..
lemma BdRPlus.j6 : Associated ↑xi x4 := .trans (by simp [associated_mul_isUnit_right_iff, ne]) (.map _ exists_tPeriod.choose_spec.1)
@[simp] private lemma b4 : thetaBdR x = .coe' x := x3.eq_symm_apply.1 (AlgHom.congr_fun (exists_adicCompletionEvalOneₐ_comp_eq _).choose_spec x)
@[simp] private lemma d4 x : thetaBdR (g • x) = g • thetaBdR x := (x.q0 1).elim
  fun _ ⟨_, _, e⟩ ↦ by simpa [smul_sub, ne] using congr(thetaBdR (g • $e) = g • thetaBdR $e)
instance : SMulDistribClass (Gp p) Bcris BdR := smulDistribClass_of_tower (B := Bcris) (congrFun (by
  apply IsLocalization.ext (.powers (mu : BPlus)) <;> simp))
@[simp] lemma BdR.smul_algebraMap_qpBar : g • (x : BdR) = g x := by simp [← by
  simpa using congrArg thetaBdR (coe_inj.1 (.trans (((toAlgHom _ _ g).extendScalarsOfIsLocalization ℚ_[p] ℤ_[p]⁰).restrictNormal_commutes _ x) (smul_algebraMap_eq_algebraMap_smul (R := BdR) ..)))]
lemma Bcris.fundamental_sequence_surjective a β : ∃ y : Bcris, ∃ x : BdRPlus, frobEnd y - y = a ∧ (x : BdR) = y - β := by
  obtain ⟨⟨U, V⟩, x, z, Z, E⟩ := (by simpa [-isUnit_map_iff] using isUnit_smul_of_dvd_mu 1 dvd_rfl), div_surjective BdRPlus β; obtain ⟨k, u, rfl⟩ := q5 (ne_zero Z); obtain ⟨⟨r, R⟩, y, x₀, X⟩ := U.pow k, (x * u.2).w0 k; let ⟨m, b, hb⟩ := surj (mu : BPlus) (a - frobEnd (y • ↑r⁻¹) + y • ↑r⁻¹); let ⟨n, e, _, ⟨w, rfl⟩, h⟩ := b.q0 0 m.succ; obtain ⟨⟨c, rfl⟩, ⟨s, S⟩, ⟨d, rfl⟩, t, T⟩ := e.exists_frobEnd_sub_xi_pow_mul_eq m, (V.pow m).smul (isUnit_p.pow n).unit, w6 z2.dvd w, (by simp [ne] : IsUnit (tau ^ m * p ^ n : BdRPlus)); use y • r⁻¹ + c • s⁻¹ - mu * d, c • t⁻¹ - mu * d - x₀, (s * U.unit ^ m).mul_right_inj.1 ?_; linear_combination (norm := (simp [smul_def, Ainf.prime_xi.1, *]; ring)) -congr($E - r.2 * $X)
  linear_combination (norm := (simp [smul_def, S]; ring))
    congr(frobEnd (c • $(s.3)) - xi ^ m • c • $(s.3) - p ^ n * $hb - $h)
