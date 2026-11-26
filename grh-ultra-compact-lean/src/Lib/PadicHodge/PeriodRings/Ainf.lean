import Lib.PadicHodge.PeriodRings.CpIntegers
noncomputable section
attribute [-simp] IsUnit.dvd pow_left_inj₀ map_smul
open MulSemiringAction Polynomial PreTilt IsOfFinOrder nonZeroDivisors WittVector Perfection NeZero Ideal.Quotient Fact ZMod ValuationRing Cardinal Complex IsPrimitiveRoot
lemma mk_complex_eq_mk_padicAlgCl {p} [Fact p.Prime] : #ℂ = #(PadicAlgCl p) := mk_complex ▸ (continuum_le_cardinal_of_module ℚ_[p] _).antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] _).trans (by simpa using! mk_quotient_le.trans (@mk_set_le (ℕ → ℚ) _)))
variable {p} [ThePrime p]
abbrev FrobGal := Multiplicative ℕ × Gp p
@[instance_reducible] def OFlat := PreTilt OC p
deriving CommRing, CharP _ p, PerfectRing _ p, IsDomain, ValuationRing
abbrev Ainf := WittVector p OFlat
@[instance_reducible] def CFlat := FractionRing OFlat
deriving Field, Algebra OFlat, IsFractionRing OFlat, FaithfulSMul OFlat, CharP _ p
@[instance_reducible] def WittCFlat := WittVector p CFlat deriving CommRing, IsDomain
abbrev theta : Ainf →+* OC := fontaineTheta ..
@[simp] lemma theta_teichmuller x : theta (teichmuller p x) = x.untilt := fontaineTheta_teichmuller x
instance {G} [AddCommMonoid G] [Module ℚ≥0 G] : PerfectRing (Multiplicative G) p := ⟨mod_cast @MulAction.bijective₀ ℚ≥0 G _ _ p out⟩
lemma exists_tilt_lift_of_character (a : Multiplicative ℚ →* ℂ_[p]) (k : a (.ofAdd 1) = 1) : ∃ χ : _
  →* OFlat, ∀ s, (χ s).untilt = a s := ⟨.comp (mapMonoidHom ..) (liftMonoidHom _ _ _ (a.codRestrict _ fun s ↦ b8.2 (of_pow (by simp [← map_pow, show s ^ s.toAdd.den = .ofAdd 1 ^ s.1 by aesop, k]) s.toAdd.3).norm_eq_one.le)), fun _ ↦ by erw [teichmuller₀_mapMonoidHom_idealQuotientMk]; simp⟩
def epsPow := (exists_tilt_lift_of_character ⟨⟨(algebraMap _ _ <| (IsAlgClosed.ringEquiv_of_equiv_of_charZero (mk_complex ▸ cantor _) (Quotient.exact (@mk_complex_eq_mk_padicAlgCl p _))).some <| exp <| 2 * Real.pi * I * ·.toAdd), by simp⟩, by simp [mul_add, exp_add]⟩ (by simp)).choose
lemma isPrimitiveRoot_untilt_epsPow s : IsPrimitiveRoot (epsPow s).untilt s.toAdd.den := by
  erw [← coe_submonoidClass_iff, (exists_tilt_lift_of_character ..).choose_spec] <;>
    simp [map_of_injective, RingHom.injective, EquivLike.injective, isPrimitiveRoot_exp_rat]
def epsRoot := epsPow (.ofAdd p⁻¹)
def epsTilt := epsRoot ^ p
@[simp] lemma epsPow_one : epsPow (.ofAdd 1) = epsTilt := by simp [epsTilt, epsRoot, ← map_pow, ← ofAdd_nsmul]
@[simp] lemma untilt_epsTilt : epsTilt.untilt = 1 := by simpa using isPrimitiveRoot_untilt_epsPow (.ofAdd 1)
def tau : Ainf := teichmuller p epsRoot - 1
def mu : Ainf := teichmuller p epsTilt - 1
def xi : Ainf := ∑ i ∈ .range p, teichmuller p epsRoot ^ i
lemma xi_mul_tau : xi * tau = mu := by erw [geom_sum_mul, mu, map_pow]
lemma OFlat.isAIC : IsAIC OFlat := ⟨fun f hf h ↦ by
  have K n w {d} : ∀ b {g}, IsMonicOfDegree g d → ∃ a : OFlat, ((d, a) = (0, b) ∨ g.IsRoot (a.coeff n)) ∧ g.eval (w.coeff n) ∣ (w - a).coeff n ^ d := d.rec (by simp) fun _ ih _ g ⟨k, m⟩ ↦ by
    obtain ⟨b : OFlat, q, rfl⟩ := by
      simpa [(coeff_surjective ((IsAIC.of_surjective mk_surjective).exists_pow_eq p) n).exists, ↓← dvd_iff_isRoot, k] using (IsAIC.of_surjective mk_surjective).1 g m
    let ⟨a, _, e⟩ := ih b ((isMonicOfDegree_X_sub_one _).of_mul_left ⟨by omega, m⟩)
    obtain t|t := dvd_total (w - a) _ <;> [use b; use a] <;> simp [← map_sub, ← coeff_def] <;>
      grw [e, t, pow_succ']; aesop
  choose a ha e using (K · · 0 ⟨rfl, hf.map (coeff ‹_›)⟩)
  simp_all [h.ne']
  use ⟨fun n ↦ ((n + f.natDegree).succ.rec 0 a : OFlat).coeff n, ?_⟩, ext ?_ <;> intro
  erw [coeff_pow_p', add_right_comm, eq_comm, ← sub_eq_zero, ← map_sub, ← coeffMonoidHom_pow_p_pow']
  grw [← zero_dvd_iff, ← ha, ← PreTilt.coeff_pow_p, e, pow_succ, pow_mul, ← Nat.lt_pow_self out];
    rfl
  erw [← eval₂_hom, eval₂_hom _ (a ..), ← coeffMonoidHom_pow_p_pow', ha, zero_pow out]; rfl⟩
variable {A R N S} [CommRing A] [MulSemiringAction FrobGal A] [SMul N A] [CommRing R] [CharP R p] [CommRing S] {M} [Monoid M] (n : ℕ) (g : Gp p) (x : OFlat)
def frobEnd := toRingHom FrobGal A (.ofAdd 1, 1)
instance : Algebra ℤ_[p] (WittVector p R) := ((WittVector.map (castHom dvd_rfl R)).comp (equiv p).symm).toAlgebra
instance (priority := low) [Algebra A S] : Algebra (WittVector p A) (WittVector p S) := (WittVector.map (algebraMap ..)).toAlgebra
instance actOFlat : MulSemiringAction FrobGal OFlat := by apply (actionOfHoms _ fun m ↦ (iterateFrobenius _ p
  m.1.toAdd).comp (tiltMap (toRingHom _ _ m.2))) <;> simp [iterateFrobenius_def, ← tiltMap_comp, pow_add, pow_mul', RingHom.ext_iff] <;> [convert tiltMap_id; congr!] <;> aesop (add simp mul_smul)
instance (priority := 100) FrobGal.galAct : MulSemiringAction (Gp p) A := compHom (M := FrobGal) _ (.inr ..)
@[instance 100] lemma FrobGal.d0 [SMulCommClass FrobGal N A] : SMulCommClass (Gp p) N A := SMul.comp.smulCommClass _
@[local simp] lemma FrobGal.smul_def (x : A) : (Multiplicative.ofAdd n, g) • x = frobEnd^[n] (g • x) := by erw [smul_iterate_apply, smul_smul]; congr <;> simp
@[simp] lemma smul_frobEnd (x : A) : g • frobEnd x = frobEnd (g • x) := by erw [smul_smul]; simp
def OFlat.x6 := untilt ((frobeniusEquiv _ p).symm^[n] x)
lemma OFlat.r9 : ↑(x6 n x) = x.coeff n := by simp [x6]
open algebraMap
lemma q9 [CharP S p] (f : R →+* S) (a : ℤ_[p]) : map (p := p) f a = algebraMap _ _ a := congr(map $((f.comp _).ext_zmod _) _)
instance [MulSemiringAction M R] : SMulCommClass M ℤ_[p] (WittVector p R) := ⟨fun _ ↦ map_smul (AlgHom.mk _ (q9 _))⟩
instance [MulSemiringAction M Ainf] [MulSemiringAction M S] [Algebra ℤ_[p] S] [Algebra Ainf S]
    [IsScalarTower ℤ_[p] Ainf S] [SMulCommClass M ℤ_[p] Ainf] [SMulDistribClass M Ainf S] :
    SMulCommClass M ℤ_[p] S := ⟨by simp [← algebraMap_smul Ainf, smul_distrib_smul]⟩
instance [CharP S p] [Algebra R S] : IsScalarTower ℤ_[p] (WittVector p R) (WittVector p S) := .of_algHom ⟨_, q9 _⟩
lemma OFlat.v9 : frobEnd x = x ^ p := (pow_mul ..).trans congr($(one_smul FrobGal x) ^ p)
variable {G} [Group G] [MulSemiringAction G OFlat] [MulSemiringAction FrobGal S]
instance [SMul S A] [SMulDistribClass FrobGal S A] : SMulDistribClass (Gp p) S A := ⟨(smul_distrib_smul <| (1, ·) ·)⟩
@[simp] lemma j1 [Algebra S A] [SMulDistribClass FrobGal S A] (x : S) : frobEnd (x : A) = frobEnd x := smul_algebraMap_eq_algebraMap_smul ..
instance : MulSemiringAction G CFlat := IsFractionRing.mulSemiringAction _ OFlat _
deriving instance Algebra ℤ_[p], Algebra Ainf, IsScalarTower ℤ_[p] Ainf, MulSemiringAction G, SMulCommClass G ℤ_[p] for @WittCFlat p _
instance : SMulDistribClass G Ainf WittCFlat := smulDistribClass_of_tower fun _ : Ainf ↦ ext fun _ ↦ smul_algebraMap_eq_algebraMap_smul ..
instance : CharP (IsLocalRing.ResidueField OFlat) p := .of_ringHom_of_ne_zero (mk _) _ out
instance : IsAlgClosed CFlat := (OFlat.isAIC.of_isLocalization _⁰).isAlgClosed
