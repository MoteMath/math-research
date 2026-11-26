import Lib.PadicHodge.WachKisin.HodgeFrame
import Lib.GaloisRep.Main.LocalEmbedding
import Lib.General.NumberTheory.Valuation
import Lib.General.Groups.ResidualIrreducibility
import Lib.PadicHodge.Crystalline.Jumps
noncomputable section
section
open Algebra _root_.RingHom Amax BPlus Ideal NeZero OC RingEquiv Set Witt WittVector nonZeroDivisors
attribute [-simp] map_smul
variable {p : ℕ} [ThePrime p] (c : Lift.Chart) {m : FrobGal} {y : BPlus} (n : ℕ)
def Lift.thetaPhiInv := theta.comp ((ofBijective _ z4)⁻¹ ^ n).toRingHom
@[simp] lemma Lift.d1 a : thetaPhiInv (n + 1) (frobEnd a) = thetaPhiInv n a := congr(thetaPhiInv n $(symm_apply_apply ..))
lemma Lift.q7 : ∀ a, thetaPhiInv n a = PreTilt.coeff n a.constantCoeff := n.rec
    mk_fontaineTheta fun _ ↦ z4.2.forall.2 ∘ by simp [↓r0]
@[simp] lemma Lift.thetaPhiInv_smul (g : Gp p) : ∀ a, thetaPhiInv n (g • a) = g • thetaPhiInv n a := n.rec (theta_smul g) fun _ ↦ z4.2.forall.2 ∘ by simp
lemma Lift.frobE_dvd_iff {c : Lift.Chart} {n a} : (c.frobE n).1 ∣ a ↔ thetaPhiInv n a = 0 := by erw [c.coe_φ_pow, theta_eq_zero_iff_xi_dvd, ← c.associated_E_xi.dvd_iff_dvd_left, inv_pow, ← map_dvd_iff_dvd_symm (_ : RingAut _)]; simp
namespace Lift.Chart
lemma z5 (f : _ →ₗ[c.S] _) α r (h : thetaPhiInv n α.1 ∣ thetaPhiInv n r) : ∃ x, c.frobE n ∣ f r - α * x := ((theta_surjective.comp (Equiv.surjective _)).exists.1 h).imp' f fun a _ ↦ .imp' f (fun b (k : r - α • a = c.frobE n • b) ↦ by simpa using congr(f $k)) (frobE_dvd_iff.2 (by simpa [smul_def]))
abbrev x7 : c.S →ₐ[ℤ_[p]] ℂ_[p] := toPadicIntAlgHom ((thetaPhiInv n).comp c.S.val)
lemma w9 {K : Subalgebra ℚ_[p] _} {y} (h : ∀ g : Gp p, (∀ n, ∀ x ∈ (c.x7 n).range, x ∈ K → g • x = x) → g y = y) : ↑y ∈ K := (InfiniteGalois.fixedField_fixingSubgroup (subalgebraEquivIntermediateField (K.comap (algHom ..)))).le (x := y) fun g ↦ h _ fun n _ s ↦ (IsAIC.mem_range_of_isIntegralElem ((IsIntegral.of_mem_of_fg _ · _ s) ((Submodule.fg_range ((c.x7 n).toLinearMap ∘ₗ ((Pi.basisFun ..).constr ℕ (c.z ^ ·.1)).restrictScalars _)).of_le (range_subset_iff.2 (c.exists_dvd_sub_sum_z_pow n rfl · |>.imp (by simp_all [dvd_iff_coe_dvd, frobE_dvd_iff]
  ))))).tower_top).rec fun x ↦ (· ▸ (.trans (smul_coe_Cp ..) congr($(g.2 ⟨x, ·⟩))))
lemma y5 {y : OFlat} (h : ∀ g : Gp p, (∀ s : c.S, g • s.1 = s) → g • y = y) N : ∀ᶠ n in .atTop, ∃ s : c.S, y.coeff N = PreTilt.coeff n s.1.constantCoeff := let t := teichmuller p y
  have ⟨_, ⟨x, hx, rfl⟩, e⟩ := SeminormedAddCommGroup.mem_closure_iff.1 (@ax_exists_near_fixed p _ (fixingSubgroup _ c.S) (thetaPhiInv N t) (by erw [← coe_smul, ← thetaPhiInv_smul, smul_teichmuller, h · ·])) ‖(p : ℂ_[p])‖ (by simp [ne])
  have m := @monotone_nat_of_le_succ _ _ (c.x7 · |>.range) fun _ _ ↦ .imp' c.φ (by simp [«φ»])
  (multiple_mem_adjoin_of_mem_localization_adjoin _⁰ _ _ _ (c.w9 fun g G ↦ hx ⟨g, fun s ↦ sub_eq_zero.1 (zero_dvd_iff.1 (dvd_of_mem_of_constantCoeff_dvd (⨅ n, ker (thetaPhiInv n)).zero_mem (by simp [ne]) (fun a h ↦ ⟨0, Perfection.ext (q7 · a ▸ by aesop)⟩) _ (by simpa [Subtype.ext_iff] using (G · _ ⟨_, rfl⟩ (subset_adjoin (Algebra.mem_iSup_of_mem _ ⟨_, rfl⟩))))))⟩)).elim fun ⟨a, _⟩ h ↦ Filter.mem_atTop_sets.2 ((mem_iUnion.1 ((Subalgebra.coe_iSup_of_directed m.directed_le).le
  (adjoin_le le_rfl h))).imp fun _ w n l ↦ (m l w).elim fun s u ↦ ((c.x7 n).range.smul_mem
    (one_mem _) a).elim fun α v ↦ (c.z5 n c.coord₀ α s ⟨thetaPhiInv N t - ⟨_, b8.2 (e.trans norm_p_lt_one).le⟩, by aesop⟩).imp fun s d ↦ q7 N
    t ▸ by simp_all [↓← q7, coord₀_coe, dvd_iff_coe_dvd, frobE_dvd_iff, mk_span_eq_iff_dvd_sub, e.le, ne_zero, OC.dvd_iff_norm_le, ← algebraMap_smul ℚ_[p] a])
attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule Subalgebra.isScalarTower_left
attribute [-simp] IsEmpty.forall_iff LinearMap.map_smul_of_tower isUnit_map_iff
lemma _root_.Lift.w3 (h : ∀ n, ∃ w ∈ x1, y = p ^ n * w) : y = 0 := let ⟨_, ⟨b, _⟩, _⟩ := h 0
  by grind [@eq_of_forall_pow_dvd_sub _ _ b 0 p _ (by simp_all [← injective_Amax_BPlus.eq_iff, x1, dvd_def])]
lemma _root_.Lift.map_p_pow_mul {F} [FunLike F BPlus BPlus] [AddMonoidHomClass F _ _] (G : F) n y : G (p ^ n * y) = p ^ n * G y := by grind [map_nsmul G (p ^ n)]
lemma _root_.Lift.y7 : ∀ y ∈ x1, m • y ∈ x1 := by simp [x1]
abbrev ainfToBPlus := algebraMap Ainf BPlus
lemma theta_z_dvd_p : theta c.z ∣ p := by grw [c.dvd_iff_coe_dvd.1 c.z_dvd_E_sub_p]; simp [theta_E]
lemma theta_z_ne_zero : theta c.z ≠ 0 := ne_zero_of_dvd_ne_zero out c.theta_z_dvd_p
def bicommutant := Subalgebra.comap (lmul c.S _) (.centralizer _ {G | ∀ y ∈ x1, G y ∈ x1})
@[simp] lemma q1 {c : Chart} (s : c.S) : ainfToBPlus s ∈ c.bicommutant := c.bicommutant.2 s
attribute [local simp] mem_span_singleton IsUnit.ne_zero IsUnit.pow map_p_pow_mul ne pow_mem
lemma m8 (f : _ →ₗ[c.S] _) : ∃ G : _ →ₗ[c.S] _, (∀ a, G (ainfToBPlus a) = ainfToBPlus (f a)) ∧ ∀ y ∈ x1, G y ∈ x1 := by
  let i := (IsScalarTower.toAlgHom c.S Ainf Amax).toLinearMap; have K {n a} := p_pow_dvd_of_mem_pow ∘ (by simpa [span_singleton_eq_span_singleton.2 c.associated_E_xi, span_insert, Ideal.map_pow, Ideal.map_sup] using ((span {↑p, c.E} ^ n).smul_top_le_comap_smul_top f ·)) ∘ @Amax.z0 _ _ a n; let F := ((primaryComponent _ (span {↑p})).comap (i.prod (i ∘ₗ f)).range.mkQ).subtype
  choose G₀ h₀ using (by simpa [span_singleton_pow, F, i, LE.le, primaryComponent_mem, ← Submodule.Quotient.mk_smul, @smul_def _ Amax, Function.Surjective, Submodule.Quotient.forall] using (k9 (span {↑p}) (.fst .. ∘ₗ F) (.snd .. ∘ₗ F)) :) (let ⟨d, a, w, e⟩ := ·.q6 1
    ⟨_, ⟨_, d, a, e, (K ⟨_, e⟩).choose_spec⟩, by simp⟩) fun n x z m a _ _ ↦ by
    grw [← le_self_add]; simpa [*, pow_add, mul_dvd_mul_iff_left] using @K (m + n) a
  have := (map_natCast (algebraMap c.S Amax) p ▸ isLocalizationAway_p_bPlus :); let j := (IsScalarTower.toAlgHom c.S Amax BPlus).toLinearMap; have H := IsLocalizedModule.map_apply (.powers ↑p) j j G₀; exact ⟨_, (by erw [H, h₀ _ _ 0 ·] <;> bound), by simp_all [x1, j]⟩
def extendToBPlus f := (c.m8 f).choose
lemma extendToBPlus_ainfToBPlus f a : c.extendToBPlus f (ainfToBPlus a) = ainfToBPlus (f a) := by grind [extendToBPlus]
lemma q8 f : ∀ y ∈ x1, c.extendToBPlus f y ∈ x1 := by grind [extendToBPlus]
lemma extendToBPlus_mul f (h : y ∈ c.bicommutant) x : c.extendToBPlus f (y * x) = y * c.extendToBPlus f x := congr($(h _ (c.q8 f)) x)
abbrev extendedCoord i := c.extendToBPlus (Algebra.linearMap .. ∘ₗ c.adicBasis.coord i)
attribute [local simp] smul_def q8 extendToBPlus_ainfToBPlus extendToBPlus_mul y7 mul_assoc pow_add
lemma k6 (G : _ →+ _) (hA : ∀ y ∈ x1, G y ∈ x1) (h : ∀ a, G (ainfToBPlus a) = 0) : G y = 0 := w3
  (let ⟨_, _, w, _, e⟩ := y.q0 · 0; ⟨G w, by simpa [*, -e] using congr(G $e)⟩)
lemma j3 {f} (h : ∀ a, m • f a ∈ c.S) : m • c.extendToBPlus f y ∈
  c.bicommutant := fun G _ ↦ by ext; simpa [mul_left_comm (m • _)] using (fun w : x1 ↦ k6 (.comp (G * .mulRight _ w - .mulRight _ (G w)).toAddMonoidHom (m • c.extendToBPlus f)) (by aesop)
  (by simpa using G.2 ⟨_, h ·⟩ _)) ⟨_, _, exists_p_pow_mul_eq_amax.choose_spec.choose_spec.symm⟩
lemma extendedCoord_mem_bicommutant i y : c.extendedCoord i y ∈ c.bicommutant := (one_smul ..).subst (c.j3 (by simp))
lemma v6 {u v} : v ∈ c.bicommutant → v ≠ 0 → v * u ∈ c.bicommutant → u ∈ c.bicommutant := by simp_all [bicommutant, Subalgebra.mem_centralizer_iff, DFunLike.ext_iff]
lemma exists_bicommutant_mul_p_eq_one : ∃ u ∈ c.bicommutant, u * p = 1 := ⟨↑isUnit_p.unit⁻¹, by simp [c.v6 (v := p)]⟩
lemma extendedCoord_oneIndex_eq_self (hy : y ∈ c.bicommutant) : c.extendedCoord c.oneIndex y = y := by obtain _ := c.coord₀_coe 1, (c.extendToBPlus_ainfToBPlus · 1), (c.extendToBPlus_mul · hy 1); aesop
lemma z8 y m : ∀ᶠ F in Filter.atTop, ∃ w ∈ x1, y - ∑ i ∈ F, c.adicBasis.b i • c.extendedCoord i y = p ^ m * w := (y.q0 m 0).rec fun k ⟨a, w, hw, e⟩ ↦ (c.adicBasis.eventually_sub_sum_mem a _).mono fun F h ↦ ⟨_, .symm ⟨by
  simpa [← mul_add, map_add, ← IsScalarTower.algebraMap_apply, ↓@commutes c.S, sub_eq_iff_eq_add] using congr((1 - ∑ i ∈ F, c.adicBasis.b i • c.extendedCoord i) $e - algebraMap _ _ $((p_pow_dvd_of_mem_pow ((c.m5 (k + m)).choose_spec h)).choose_spec.symm)), add_mem (sub_mem hw (sum_mem (by aesop))) ⟨_, rfl⟩⟩⟩
lemma frobEnd_mem_bicommutant : y ∈ c.bicommutant → frobEnd y ∈ c.bicommutant := (extendedCoord_oneIndex_eq_self _ · ▸ j3 _ fun _ ↦ («φ» _ _).2)
lemma z9 : ∃ u ∈ c.bicommutant, u * ainfToBPlus
  (c.φ c.E) = 1 := have h : IsUnit (ainfToBPlus (c.φ _)) := ((z2.trans ((c.associated_E_xi.map _).map _).symm).map (algebraMap ..)).isUnit (by simp)
  ⟨↑h.unit⁻¹, by simp [c.v6 _ h.ne_zero]⟩
lemma exists_pow_mul_extendedCoord_eq_add (ν : c.S) (h : ∃ b, ν.1 ∣ xi - p * b) (b : Amax) M : ∃ s : c.S, ∃ w ∈ c.bicommutant, p ^ M * c.extendedCoord c.oneIndex (algebraMap _ _ b) = ainfToBPlus s + ainfToBPlus ν ^ M * w := let ⟨_, _, f⟩ := b.z3 h M
  ⟨_, _, c.extendedCoord_mem_bicommutant _ _, by
    simpa [← IsScalarTower.algebraMap_apply] using! congr(c.extendToBPlus _ (algebraMap _ _ $f))⟩
lemma eventually_exists_pow_mul_eq_add_z_mul (hy : y ∈ c.bicommutant) : ∀ᶠ m in .atTop, ∃ w, ∃ x ∈ c.bicommutant, p ^ m * y = ainfToBPlus (algebraMap (WittFq c.f) _ w) + ainfToBPlus c.z * x := y.exists_p_pow_mul_eq_amax.rec fun k ⟨b, hb⟩ ↦ .mono (Filter.Ioi_mem_atTop k) fun _ h ↦ h.dest.rec fun n q ↦ q ▸ let ⟨s, _, hx, e⟩ := c.exists_pow_mul_extendedCoord_eq_add _ c.r3 (p ^ n * b) 1
  (c.exists_z_dvd_sub_const s).imp fun _ ⟨r, h⟩ ↦ ⟨_, add_mem (q1 r) hx, by
    simpa [extendedCoord_oneIndex_eq_self, hy, h, mul_add, add_assoc, ← hb, mul_left_comm] using e⟩
lemma z_dvd_sub {g} (h : FixesLambda c.f g) (hy : y ∈ c.bicommutant) : ainfToBPlus c.z ∣ g • y - y := by
  obtain ⟨⟨_, _, _, _, f⟩, _, e⟩ := (c.eventually_exists_pow_mul_eq_add_z_mul
    hy).exists, show c.z.1 ∣ g • c.z by erw [z_eq_teichmuller, smul_teichmuller]; simp [map_dvd, untilt_dvd_iff.1, OC.dvd_iff_norm_le, untilt_frobGal_smul]
  simpa [← mul_sub, h, e] using congr(ainfToBPlus c.z ∣ g • $f - $f)
lemma eq_zero_of_z_pow_dvd (h : ∀ n, ainfToBPlus c.z ^ n ∣ y) : y = 0 := c.7.rec fun a e ↦ BPlus.eq_zero_of_forall_pow_dvd a (by
  simp_all (maxDischargeDepth := 4) [← e, add_mul, ← pow_mul, mul_pow, IsUnit.map, z])
lemma z_dvd_of_dvd_E_pow_mul {k a} (h : ainfToBPlus c.z ∣ ainfToBPlus (c.E ^ k * a)) : ↑c.z ∣ a := dvd_of_mem_of_constantCoeff_dvd
  (I := (span {ainfToBPlus c.z}).comap ainfToBPlus) (by simp) (by simp) (fun _ h ↦ mem_span_pair_iff.1 (by simpa [image_pair, -smul_def] using c.adicBasis.m3 le_rfl fun i ↦ Submodule.smul_mem_smul (((pow_one _).trans (c.x5.isLocalRing.eq_maximalIdeal inferInstance)).ge fun u ↦ one_ne_zero (c.eq_zero_of_z_pow_dvd (by simp [isUnit_of_dvd_unit ((mem_span_singleton.1 h).imp' _ fun _ e ↦ by simpa using! congr(c.extendedCoord i $e)) (u.map (algebraMap ..))]))) ⟨⟩)) a (by induction k <;>
                             simp_all [pow_succ', E, add_mul, dvd_add_right, Dvd.dvd.mul_right])
end Lift.Chart
end
section
attribute [-instance] Subalgebra.moduleLeft
namespace Lift
open Ainf BPlus Fintype RingHom Function Algebra Matrix Amax Fact Ideal
variable {p} [ThePrime p] {d : Type} (c : Chart) [Fintype d] (U : Matrix d d BPlus) (h : ℕ) (v : Ainfˣ)
@[simp] lemma d7 : tau ≠ 0 := ne_zero_of_map r8
lemma lifting_the_exponent {R} [CommRing R] {f : Ainf →+* R} (hf : Surjective f) x v {n}
    (hv : ¬IsUnit v) (h : v ∣ x - 1) (H : p * f (x - 1) * f v ∣ f (x - 1) ^ p) (hn : n ≠ 0) :
    f (x ^ n - 1) ∣ p ^ padicValNat p n * f (x - 1) := by
  set s := ∑ i ∈ .range (n.divMaxPow p), x ^ i
  have ⟨y, H⟩ := hf.exists.1 (ZMod.exists_one_add_mul_pow_prime_pow_eq out (by gcongr) H (f s) (padicValNat p n))
  have := (@isUnit_of_dvd_sub _ _ _ (s + v * y) (n.divMaxPow p) (q4 hv) (by simp [Ainf.isUnit_iff_isUnit_constantCoeff, CharP.isUnit_natCast_iff out, p.not_dvd_divMaxPow out hn]) (by simp_all [s, ← Quotient.eq_zero_iff_dvd])).map f
  simp_all [s, mul_geom_sum, ← pow_mul]
namespace Chart
lemma associated_E_mul_tau_mu : Associated (c.E * tau) mu := xi_mul_tau ▸ c.associated_E_xi.mul_right _
lemma associated_smul_E g : Associated c.E.1 ((g : Gp p) • c.E) := (associated_smul_of_dvd g (by simp [c.associated_E_xi.dvd_iff_dvd_left, ← theta_eq_zero_iff_xi_dvd, theta_E])).symm
lemma exists_tau_mul_E_eq_mul_epsTilt_pow_sub {n} (hn : n ≠ 0) : ∃ α β, tau * c.E * (p ^ padicValNat p n + β * c.z) = α * (.teichmuller p epsTilt ^ n - 1) := match c.associated_E_mul_tau_mu.dvd', c.r3 with | ⟨v, _⟩, ⟨u, s, _⟩ => (lifting_the_exponent (Quotient.mkₐ_surjective ℤ (span {-c.z * mu})) _ _ (·.map _ |>.ne_zero toWittResidue_tau) (Dvd.intro_left _ xi_mul_tau) (.trans ⟨u, mk_span_eq_iff_dvd_sub.2 ⟨-tau * s, by grind [mu, xi_mul_tau]⟩⟩ (pow_dvd_pow _ (out : 1 < p))) hn).rec (Quot.ind fun α ↦ (⟨α * v, ·.imp (by grind [mu])⟩) ∘ mk_span_eq_iff_dvd_sub.1)
structure IsPeriodMatrix where
  exists_inv : ∃ W, U * W = (c.E * tau) ^ h • 1
  exists_frob : ∃ F F', (∀ i j, F i j ∈ c.bicommutant) ∧ F' * F = 1 ∧ U.map frobEnd = v • (U * F)
  exists_gal g : c.FixesThetaZ g → ∃ ρ, .map ρ ainfToBPlus * g • U = U
  hat_stable f y : (∃ w, U *ᵥ y = c.E.1 ^ h • w) → ∃ w, U *ᵥ c.extendToBPlus f ∘ y = c.E.1 ^ h • w
lemma E_ne_zero : c.E.1 ≠ 0 := (c.associated_E_xi.symm.prime prime_xi).1
attribute [local simp] mul_assoc mul_pow funext_iff pow_add mulVec_sum smul_sub
attribute [local simp↓] mulVec_smul E_ne_zero dotProduct_smul extendToBPlus_ainfToBPlus extendToBPlus_mul mulVec_sub Units.smul_def
lemma v3 {e} (he : e ∣ mu) : ∃ k, ∀ {y w}, U *ᵥ y = e ^ h • w → (∀ i, y i ∈ x1) → ∀ i, p ^ k * w i ∈ x1 := (IsLocalization.exist_integer_multiples_of_finite (.powers (p : Amax)) U.uncurry).rec fun ⟨_, k,
  rfl⟩ hk ↦ ⟨_ + k, fun e hy i ↦ by simpa using x1.y8 he (by
    erw [← mul_smul_comm, ← Pi.smul_apply, ← e, Finset.mul_sum]
    simpa [smul_def] using! sum_mem fun j _ ↦ mul_mem (hk (i, j)) (hy j))⟩
variable {c U h v} (hU : c.IsPeriodMatrix U h v)
include hU
namespace IsPeriodMatrix
lemma mulVec_injective : Injective U.mulVec := mulVec_injective_of_det_ne_zero (by
  simpa [·, @smul_def _ BPlus] using congr($(hU.1.choose_spec).det).symm)
lemma k1 : ∃ Q Z, Q.det ≠ 0 ∧ (∀ i j, Z i j ∈ c.bicommutant) ∧ U * Z = c.E.1 ^ h • Q.map ainfToBPlus ∧ (∀ x y, (∀ i, y i ∈ c.bicommutant) → U *ᵥ y = c.E.1 ^ h • ainfToBPlus ∘ x → ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x) ∧ ∀ x y, U *ᵥ y = c.E.1 ^ h • ainfToBPlus ∘ x → ∀ δ l g, ¬↑p ∣ δ → l ᵥ* Q = δ • g → δ ∣ l ⬝ᵥ x := by
  obtain ⟨⟨⟨W, e'⟩, ⟨F, F', _, o, eF⟩, -, R⟩, K, μ, u, hu, eu⟩ := hU, hU.mulVec_injective, c.associated_E_mul_tau_mu.dvd, c.exists_bicommutant_mul_p_eq_one
  obtain ⟨⟨n, hn⟩, ⟨k, hk⟩, ⟨ε, hε⟩, J, ψ, Ψ⟩ := v3 W h μ, v3 U h
    (dvd_of_mul_right_dvd μ), c.associated_E_xi.dvd, z4.imp_right Classical.skolem.1
  simp [ext_iff_mulVec, ← mulVec_mulVec, -funext_iff, -mul_pow] at e'; let g := c.E.1 ^ h • (Algebra.linearMap Ainf BPlus).compLeft d; have V := @v4 p _ {a | ∃ x y w f i, U *ᵥ y = g x ∧ U *ᵥ c.extendToBPlus f ∘ y = c.E.1 ^ h • w ∧ p ^ k * (p ^ n • w) i = a} h (ε ^ h * v⁻¹) ?_ ?_; any_goals rintro _ ⟨x, y, w, f, i, hy, hw, rfl⟩
  let P := (mulVecBilin ℕ _ U ∘ₗ c.bicommutant.val.toLinearMap.compLeft d).range.comap
    (g.restrictScalars _)
  choose y (ey : ∀ j, U *ᵥ (↑) ∘ y j = _) using P.coe_mem
  have ⟨⟨_, b⟩, _⟩ := free_finite_of_rank_le rfl (isHausdorff_of_injective_pi c.maxIdeal P.subtype)
    (fun ⟨x, y, k⟩ _ e ↦ (pi_dvd_iff.2 (prime_p.2.2 _ _ ⟨_, congr($e.1 ·)⟩ |>.resolve_left
    c.not_p_dvd_z)).rec (by rintro w rfl; exists ⟨w, (⟨_, hu⟩ * y ·), by
      simpa [g, ← mul_assoc, eu, ← mulVec_smul] using! congr(u • $k)⟩)) (card d) ?L
  choose q hq using (Cardinal.mk_fintype d ▸ b.mk_eq_rank''.trans_le ?L).some.2.surjective_comp_right b; let N := h.succ + k + n
  refine ⟨_ᵀ, _, mt exists_vecMul_eq_zero_iff.2 fun ⟨l, o, _⟩ ↦ o (dotProduct_eq_zero _ fun x ↦ by
    simpa using c.eq_zero_of_z_pow_dvd (map_pow ainfToBPlus _ · ▸ map_dvd ainfToBPlus (?Y (tau ^ h • x) (W *ᵥ ainfToBPlus ∘ x) (by simp [e', smul_def]) _ l 0 (c.not_p_dvd_z ∘ prime_p.dvd_of_dvd_pow) (by simp [*])) :)), by simp, ext_col (ey <| q ·), ?X, ?Y⟩
  exact fun x y o k ↦ ((Submodule.mem_span_range_iff_exists_fun _).1 (Submodule.span_mono (Set.range_comp_subset_range ..) (hq ▸ b.mem_span ⟨x, (⟨_, o ·⟩), k⟩))).imp
    (by simp [mulVec_eq_sum, Subtype.ext_iff]; tauto)
  refine fun x y e δ l g o a ↦ N.rec (by simp) (fun _ ↦ (Or.rec o.elim · ∘ prime_p.left_dvd_or_dvd_right_of_dvd_mul ∘ by simp [pow_succ'])) (m0
    (y := l ⬝ᵥ p ^ N • x) prime_p.2.1 prime_xi.2.1 o fun m ↦ ?_)
  choose _ r using (R · _ ⟨_, e⟩); choose z _ using (V _ ⟨_, _, _, ·, ·, e, r _, rfl⟩); choose s hs using fun f ↦ (?X (z f) (p ^ N • c.extendToBPlus f ∘ y) · (by simp [*, N])); choose G w hw ew using (Filter.eventually_all.2 (y · |> c.z8 <| m + k)).exists; use g ⬝ᵥ ∑ l ∈ G, c.adicBasis.b l • (↑) ∘ s _ fun _ ↦ nsmul_mem (c.extendedCoord_mem_bicommutant l _) _; rw [← smul_eq_mul, ← smul_dotProduct, ← a, ← dotProduct_mulVec, ← dotProduct_sub]; refine Submodule.sum_smul_mem _ _ fun i _ ↦ z0 ((@hk (p ^ N • u ^ (m + k) • (y - ∑ l ∈ G, c.adicBasis.b l • c.extendedCoord l ∘ y)) (u ^ (m + k) • ainfToBPlus ∘ _) ?_ (fun j ↦ nsmul_mem (by simp [*, ← mul_assoc, ← mul_pow, -pow_add]) _) i).imp fun z e ↦ injective_Amax_BPlus (by simpa [← pow_add, -Pi.sub_apply, ← mul_assoc, ← mul_pow, eu, (mul_comm _ u)] using! congr(p ^ m * $e).symm)); simp [*, N, G.mul_sum, G.smul_sum, smul_comm (_ ^ h), ← smul_def]
  exact rank_le fun b li ↦ have I {a : b → Ainf} : ∑ j, a j • (·.1) ∘ y j = 0 ↔ ∑ j, a j • j.1.1
    = 0 := (K.eq_iff.iff (g.map_eq_zero_iff fun _ _ ↦ by simp [g, smul_def])).1 (by simp [*])
    by simpa using (linearIndependent_iff.2 fun a ↦ (fun e j ↦ c.adicBasis.eq_zero_of_coord fun i ↦ linearIndependent_iff.1 li _ (Subtype.ext (by simpa using! I.1 (by
      simpa [smul_def, mul_comm] using congr(c.extendedCoord i ∘ $e)))) j) ∘ I.2).cardinal_le_rank
  apply hk (by rw [smul_comm, ← hw, ← mulVec_smul]) (by simpa [map_p_pow_mul] using (c.q8 f _ <| hn (K (by rw [e', mulVec_smul])) (by aesop) ·))
  have H {r w} (e : U *ᵥ w = r • ainfToBPlus ∘ ψ ∘ (v • c.E.1 ^ h • x)) : F *ᵥ _ = frobEnd (ainfToBPlus r) • y := K (by
    simpa [@smul_def _ BPlus, *, g, -e, map_mulVec, mul_left_comm] using congr(frobEnd ∘ $e))
  choose y' ha using (pow_dvd_of_map (map_mul frobEnd _) (by simp [↓m4]) (fun _ ⟨_, _⟩ ↦ dvd_of_thetaBPlus_frobEnd_eq_zero _ tau_dvd_of_theta_frobEnd (by simp [*]))
    ⟨_, by simpa [o, mul_left_comm] using congr((F' *ᵥ $(H (e' _))) ·)⟩)
  refine match R ⟨⟨ψ ∘ f ∘ frobEnd, by simp [← J.eq_iff, *]⟩, fun s _ ↦ J (by
    simpa [smul_def, Ψ] using! f.2 (c.φ s) _)⟩ y' ⟨_, ?Z⟩, H ?Z with | ⟨w', hw'⟩, Y => ⟨_, ⟨_, _, _, _, i, ?Z, hw', rfl⟩, (?_ : _ → _) congr(frobEnd ($hw' i))⟩
  simpa [e', smul_def, mul_left_comm] using congr(U *ᵥ $((funext ha : _ = (_ : BPlus) • y'))).symm
  erw [map_mulVec, comp_def, funext fun _ ↦ show frobEnd _ = c.extendToBPlus f (frobEnd _) from sub_eq_zero.1 (k6 (.mk' (_ ∘ _ - _ ∘ _) (by simp [sub_add_sub_comm])) (fun _
    _ ↦ by apply_rules [sub_mem, q8, y7]) (by simp [*])), eF, smul_mulVec, ← mulVec_mulVec, show F *ᵥ _ = (_ : BPlus) • c.extendToBPlus f ∘ y by
    simpa [mulVec, dotProduct, *, -Y, pow_mem (c.frobEnd_mem_bicommutant _), -j1]
      using congr(c.extendToBPlus f ∘ $Y)]
  exact (by simp [← by simpa [smul_def _ (w' _), map_eq_zero_iff _ J, hw, ← Algebra.mul_smul_comm] using ·, smul_smul, hε, mul_comm _ ε])
end IsPeriodMatrix
end Chart
end Lift
end
section
section
variable {p} [ι : ThePrime p] {m m' Γ s t} [Group Γ] {j : Γ →* _} (h : IsWeilPair (j s) m)
include h
lemma IsWeilPair.mul : IsWeilPair (j t) m' → IsWeilPair (j (s * t)) (m + m') := (by simpa [IsWeilPair, p.pow_add', ·.mul_iff])
lemma IsWeilPair.pow n : IsWeilPair (j (s ^ n)) (n * m) := by simpa [← pow_mul'] using! IsFrob.pow h n
lemma IsWeilPair.eq_pow_of_isFrob {q} (b : IsFrob (intQpBar p) q (j s)⁻¹) : q = p ^ m := by let ⟨l, _, P⟩ := p.succ.exists_infinite_primes; have := Fact.mk P; refine mod_cast (b.cycChar_eq l ?v).symm.trans (h.cycChar_eq l ?v); grind [Nat.prime_def, ι.out, valuation_natCast_eq_one]
omit h
namespace Lift
open WittVector
variable {p : _} [ThePrime p] {𝔣} {g : Gp p} {c : WittFq 𝔣}
def wittToQpBar := (exists_algHom_lift (OC.toPadicIntAlgHom (theta.comp (algebraMap (WittFq 𝔣) _)))).choose
lemma v8 : wittToQpBar c = (theta (algebraMap _ _ c)).1 := ((exists_algHom_lift _).choose_spec c).symm
lemma wittToQpBar_injective : Function.Injective (@wittToQpBar p _ 𝔣) := .of_ker _ (Ideal.eq_bot_of_liesOver_bot ℤ_[p] (.comap _ ⊥)).le
lemma w5 : g • algebraMap _ Ainf c = algebraMap _ _ c ↔ g (wittToQpBar c) = wittToQpBar c := (c.j7 _).rec fun _ e ↦ by erw [e, (map_injective _ Subtype.val_injective).eq_iff, ← wittToQpBar_injective.eq_iff, ← UniformSpace.Completion.coe_inj, v8, ← e, theta_smul]; simp [← v8]
end Lift
end
namespace Lift
open WittVector MulSemiringAction HasEnoughRootsOfUnity OFlat
variable {p} [ThePrime p] [Γ : GroupOverGp p] {f : ℕ+}
def FrobGroup (Γ : GroupOverGp p) := Multiplicative ℤ × Γ deriving Group
def FrobGroup.snd : FrobGroup Γ →* Γ := .snd ..
def FrobGroup.φ : FrobGroup Γ := (.ofAdd 1, 1)
def FrobGroup.inr : Γ →* FrobGroup Γ := .inr ..
instance : MulSemiringAction (FrobGroup Γ) OFlat := .compHom _ ((zpowersHom _ (frobeniusEquiv OFlat p)
  ).noncommCoprod ((toRingAut ..).comp toGp) fun _ _ ↦ .zpow_left (by ext1; simp [frobenius_def]) _)
lemma m9 (x : OFlat) : FrobGroup.φ • x = frobEnd x := x.v9 ▸ congr($(one_smul (FrobGroup Γ) x) ^ p)
lemma j4 (x : Ainf) : FrobGroup.φ • x = frobEnd x := ext fun _ ↦ m9 _
lemma r6 (x : WittCFlat) : FrobGroup.φ • x = frobenius x := frobenius_eq_map_frobenius p (R := CFlat) ▸ congr(x.map $(IsFractionRing.ringHom_ext (A := OFlat) (by simp [frobenius_def, m9, v9])))
lemma FrobGroup.phi_pow_smul n (x : Ainf) : φ ^ n • x = frobEnd^[n] x := by simp [← funext j4]
omit Γ
lemma isUnit_teichmuller_sub {a b : flatFq f} (h : a ≠ b) : IsUnit
  (teichmuller p a - teichmuller p b) := by simpa [Ainf.isUnit_iff_isUnit_constantCoeff, map_sub]
instance : HasEnoughRootsOfUnity (flatFq f) (p ^ f.val - 1) := of_card_le (by simp [← card_flatFq, ← Nat.card_units])
lemma exists_flatFq_root {K} [Field K] (s : WittFq f →+* K) x (H : x ≠ 0 → x ^ (p ^ f.val - 1) = 1) : ∃ a, s (teichmuller p a) = x := prim.rec fun g h ↦ by_cases (⟨0, by simp [·]⟩) (H · |> (h.map_of_injective (f := s.1.comp _) fun _ _ ↦ (by simpa using isUnit_teichmuller_sub · |>.map s).mtr
  ).eq_pow_of_pow_eq_one |>.imp' (g ^ ·) (by simp))
lemma fixes_roots_iff_fixesLambda g : (∀ ζ, ζ ^ (p ^ f.val - 1) = 1 → g ζ = ζ) ↔ FixesLambda f g := ⟨fun h c ↦ ext (c.1 · |> fun a ↦ congr($(w5 (c := teichmuller p a).2 (by grind [(a ^ p ^ _).ext a.2, NeZero.one_le, pow_sub₀])).1 0)), fun h _ e ↦ (exists_flatFq_root _ _ fun _ ↦ e).choose_spec ▸ w5.1 (h _)⟩
end Lift
open Fint Ideal IsLocalRing NeZero OFlat PadicComplex PowerSeries PreTilt WittVector
attribute [-simp] pow_left_inj₀
variable {p : outParam ℕ} [ThePrime p] (C : Subgroup (Gp p)) (Γ : outParam (GroupOverGp p))
lemma Lift.exists_smul_teichmuller_eq [hC : @IsClosed (Gp p) _ C] {π : PadicAlgCl p} (H : ∀ {x y n}, 0 < n → x ^ n = π → y ^ n = x ^ n → ∃ g ∈ C, g • x = y) (u v : OFlat) e [NeZero e] (hu : (u.untilt ^ e).1 = π)
  (hv : v.untilt ^ e = u.untilt ^ e) : ∃ g ∈ C, g • teichmuller p u = teichmuller p v := by
  choose! b A B using fun y (_ : untilt y ^ e = u.untilt ^ e) n ↦ by simpa [← coe_eq] using (IsAIC.exists_root_map_eq (f := algebraMap ..) (Polynomial.monic_X_pow_sub_C π (ne (p ^ n * e))) (x := (x6 n y).1) (by simp [pow_mul, ← SubmonoidClass.coe_pow, x6, coe_eq, *]))
  have cl n := hC.inter (isClosed_setOf_smul (b u n) (· = (v.x6 n).1))
  refine ((cl 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ (fun n _ ↦ .imp_right fun h ↦ by simpa [← smul_coe_Cp, B, x6, ↓Function.iterate_succ', ← untilt_iterate_frobeniusEquiv_symm_pow (_^[n] _) 1] using congr($h ^ p))
    (fun n ↦ by simpa [← B v hv] using! H (pos _) (A u rfl n) (by simp [*])) cl).imp
   fun g h ↦ ⟨(h _ ⟨0, rfl⟩).1, (map_teichmuller ..).trans (congrArg _ (Perfection.ext fun n ↦ ?_))⟩
  erw [map_pow, pow_one, ← coeff_tiltMap _ (r9 ..), ← r9]
  congr 1 with; simpa [← B] using (h _ ⟨n, rfl⟩).2
class Lift.KummerChart extends chart : Chart where
  (Γ' : Subgroup Γ) (index_coprime : Γ'.index.Coprime p) fixes (g : Γ') :
    chart.FixesThetaZ (toGp g.1)
  isChartOf : chart.IsChartOf (toGp.comp Γ'.subtype)
  nearOne_le : nearOne Γ ≤ .map Γ'.subtype ⊤
  exists_smul_z l : ∃ g : Γ', toGp g.1 • chart.z.1 = teichmuller p epsTilt ^ l * chart.z
@[simp] lemma Lift.KummerChart.thetaPhiInv_phi_pow [GroupOverGp p] a r : thetaPhiInv a (FrobGroup.φ ^ a • r) = theta r := a.rec (by aesop) (by simp [pow_succ', mul_smul, j4])
variable {Γ} [k : Lift.KummerChart Γ]
def Lift.KummerChart.differentExp := if k.e = 1 then 0 else padicValNat p k.e + 1
def Lift.KummerChart.IsUnramified := k.E = k.z + p ∧ k.e = 1 ∧ differentExp = 0
lemma Lift.KummerChart.chart_isChartOf : k.chart.IsChartOf Γ.overGp.toGp := (k.isChartOf · · |>.elim (⟨·, ·⟩))
lemma Lift.exists_kummer_chart Γ [Group Γ] [𝒥 : OverGp Γ p] : ∃ k : KummerChart ⟨Γ⟩, (∀ g, k.FixesThetaZ (𝒥.toGp g)) ∧ k.e * k.f = 𝒥.toGp.range.index ∧ (inertiaGroup _ (intQpBar p) ≤ 𝒥.toGp.range → k.IsUnramified) ∧ ∃ φ ∈ 𝒥.toGp.range, IsFrob (intQpBar p) (p ^ k.f.val) φ := by
  obtain ⟨L, ⟨⟨e, f, ⟨⟨_, ⟨h2⟩⟩⟩⟩⟩⟩ := @residueCard_padic p _ ▸ IsLocalGalois.of_finite ⟨_, 𝒥.2.1⟩; lift f to ℕ+ using Ne.pos (by simpa [·, *] using L.6.one_lt_card); obtain ⟨⟨⟨φ, hφ⟩, ⟨D⟩⟩, ⟨⟩, π, hπ⟩ := h2 ▸ L.frobenius_spec, id L, L.5.exists_irreducible
  let ⟨v, hv⟩ : Associated (π ^ e) (-p) := by simpa [← dvd_dvd_iff_associated, ← ge_antisymm_iff, dvd_iff_valuationVia_le, valuationVia] using! ((isUniformiser_ell.val_pow_eq_iff_mul_ordRat isLocalGalois_padic _ 1).2 (by simpa [*] using (isUniformiser_iff_irreducible.2 ⟨_, hπ⟩).ordRat_eq_one L (π := .mk0 π (mod_cast hπ.ne_zero))))
  wlog v₁ : e = 1 → v = 1 generalizing π v; apply this _ ((irreducible_mul_units v).2 hπ) 1 <;> simp [of_not_imp v₁, ← hv]
  have hf (g : 𝒥.toGp.range) := (@fixes_roots_iff_fixesLambda p _ f g).1 fun ζ e ↦ (D hφ).induction_on g
    (isClosed_setOf_smul _ (· = _)) fun n ↦ (apply_eq_pow_of_isFrob ((hφ.pow _).mul_iff.2 n.2.2) not_dvd_pow_sub_one e).trans (by simp [pow_eq_pow_of_modEq ((Nat.modEq_sub one_le).pow _) e])
  let κ := ((algebraMap ..).comp (localFieldOf Γ).val.1).restrict
    (valRingBelow _ (intQpBar p)) 𝓞_ℂ_[p] (by simp [← coe_nnnorm])
  obtain ⟨ev, _, H⟩ := exists_chart_of_pow_mul_eq_neg f (v.map κ) (by simpa using congr(κ $hv)); have : IsHausdorff (span {κ π}) OC := ⟨fun x h ↦ eq_of_forall_pow_dvd_sub p fun _ ↦ by grw [← map_natCast κ, neg_dvd.1 (Associated.dvd' ⟨v, hv⟩), map_pow, ← pow_mul, smodEq_span_pow_iff_dvd.1 (h _)]⟩
  choose V hV using dsimp% mem_range_of_approx (π := @X (WittFq f) _) (π' := κ π) (theta.comp ev.1).toAddMonoidHom (by simp [*]) κ fun x ↦ let ⟨a, h⟩ := (exists_flatFq_root ((residue _).comp ((wittToQpBar.1.codRestrict (localFieldOf _) fun _ _ ↦ w5.1 (hf ..)).codRestrict _ fun _ ↦ by simpa using! v8 ▸ (_ : OC).2)) (residue _ x) (by simp [·, ← h2, FiniteField.pow_card_sub_one_eq_one]))
    ⟨C (teichmuller p a), ((hπ.maximalIdeal_eq ▸ mk_span_eq_iff_dvd_sub.1 :) h.symm).imp fun y e ↦ by simpa [eq_add_of_sub_eq' e, C_eq_algebraMap] using Subtype.ext v8⟩
  obtain ⟨c, rfl, rfl, _, _, a⟩ := H (IsUnit.mul_iff.1 (isUnit_of_mem_nonunits_one_sub_self ((V v - V 1 + 1) * V v.2) (by simpa [*, ← map_mul κ] using ·.map ev |>.map theta))).1.unit (by simp [*])
  refine ⟨⟨c, ⊤, ?_, ?_, fun σ H ↦ cast ?_ ((fixingSubgroup_fixedFieldOf _).le fun x ↦ by
    obtain h | h := (valRingBelow (localFieldOf Γ) (intQpBar p)).2 x <;> simpa [*, κ, ← coe_eq, Subtype.ext_iff] using c.smul_theta_of_fixesThetaZ H ⟨_, V ⟨_, h⟩, rfl⟩), ?_, fun l ↦ cast ?_ (exists_smul_teichmuller_eq 𝒥.toGp.range (L.exists_inertia_smul_eq_of_pow_eq (π := .mk0 π.1 (mod_cast hπ.ne_zero)) (isUniformiser_iff_irreducible.2 ⟨_, hπ⟩) · · · |>.imp' (↑) ?_)
    c.varpiFlat (epsTilt ^ l * c.varpiFlat) 1 ?_ ?_)⟩, ?_, ?_, ?_, φ, φ.2, hφ⟩ <;> simp +contextual
    [*, a.eq, c.z_eq_teichmuller, κ, Chart.E, ← coe_eq, mem_localFieldOf.1, Subtype.ext_iff, KummerChart.IsUnramified, KummerChart.differentExp, Chart.FixesThetaZ, FixesLambda, hf ⟨_, _⟩]
end
section
attribute [-simp] isUnit_map_iff map_smul
section
open BPlus BdRPlus Lift Polynomial IsLocalization IsScalarTower Algebra IsSeparable algebraMap
variable {p} [ThePrime p] {Γ} [Group Γ] [𝒥 : OverGp Γ p] {c : Chart}
lemma Lift.Chart.IsChartOf.k8 (hc : c.IsChartOf 𝒥.toGp) {ι} [Fintype ι] (a : ι → _) (ha : ∀ l, a l ∈ localFieldOf Γ) f (y : ι → _) : ∑ l, a l * algebraMap _ BdRPlus (y l) ∣ ∑ l, (a l : BdRPlus) * c.extendToBPlus f (y l) := by
  let T : Subalgebra ℚ_[p] _ := ⟨c.bicommutant.1, fun r G _ ↦ LinearMap.ext ((linearMap_compatibleSMul (nonZeroDivisors ℤ_[p]) ..).1 (G.restrictScalars _) r)⟩
  choose t ht using fun m l ↦ show ∃ t : T, (xi : BdRPlus) ^ m ∣ t - a l by
    obtain ⟨⟨t, k, _⟩, _, g, E⟩ := c.w9 (K := T.map thetaBPlus) fun g h ↦ (h 0 _ ⟨·, rfl⟩ ⟨_, q1 _, m6 _⟩) |> fun H ↦ ha l ⟨g, hc g ⟨by simpa [FixesLambda, w5, thetaPhiInv, ← v8]
      using (H ⟨_, c.S.2 ·⟩), Subtype.ext (H c.z)⟩⟩, isSeparable ℚ_[p] (a l)
    let F := X - g * minpoly _ (a l); apply_fun aeval (a l : BdRPlus) at E; grw [m.lt_two_pow_self]; refine m.rec ⟨⟨t, k⟩, by simpa [← j8]⟩ fun m ⟨t, h⟩ ↦ ⟨F.aeval t, ?_⟩; cases (F.map (ofId _ BdRPlus).1).binomExpansion (a l) (t - a l); grw [pow_succ, pow_mul, h]; simp_all [aeval_algebraMap_apply, F]
  have I m y : (c.E : BPlus) ^ m ∣ ∑ l, (t ..).1 * _ ↔ _ ∣ (↑) ∘ a ⬝ᵥ ofId _ BdRPlus ∘ y := (c.associated_E_xi.map _).pow_pow.dvd_iff_dvd_left.trans (w2.symm.trans (dvd_iff_dvd_of_dvd_sub (by simpa [sub_mul] using! Finset.dvd_sum fun _ _ ↦ (ht ..).mul_right _)))
  simpa [← IsDiscreteValuationRing.addVal_le_iff_dvd, prime_xi.irreducible, ENat.forall_natCast_le_iff_le] using! ((I ..).1 <| I · y |>.2 · |>.imp' _ fun u h ↦ by
    simpa [c.extendToBPlus_mul, pow_mem] using congr(c.extendToBPlus f $h) :)
lemma exists_witt_coeff_of_isChartOf (hc : c.IsChartOf 𝒥.toGp) {b b' : Bcris} (h₀ : b' ≠ 0) (h : ∀ g, b' * 𝒥.toGp g • b = toGp g • b' * b) : ∃ m, ∃ w : WittFq c.f, p ^ m * b = (w : Ainf) * b' := by
  obtain ⟨⟨⟨a, A⟩, e⟩, B, C, _⟩ := @BdR.exists_sub_mem_of_smul_sub_mem p _ Γ _ _ ⊥ (b / b') (by simp_all [smul_div₀', ← map_mul, div_eq_div_iff, smul_eq_zero_iff_eq, mul_comm]), surj₂
    (.powers (mu : BPlus)) _ b b'
  have ⟨i, q⟩ : ∃ i, c.extendedCoord i C ≠ 0 := by by_contra!; simp_all [map_units, IsUnit.ne_zero, w3 (by simpa [*] using (c.z8 C · |>.exists))]
  obtain ⟨⟨n, γ, E, N⟩, J, _, H⟩ := exists_eq_pow_mul_of_not_forall_dvd (fun _ ↦ _) (c.extendedCoord i ∘ ![B, C]) fun H ↦ q (c.eq_zero_of_z_pow_dvd (H · |> pi_dvd_iff.1 <| 1)), (isIntegral ℚ_[p] a).algebraMap (B := BdR), hc.k8 ![1, -a] (by simpa using A) (Algebra.linearMap .. ∘ₗ c.adicBasis.coord i) ![B, C]; simp [funext_iff, -Fin.forall_fin_two] at E
  choose m w u _ _ using (Filter.Eventually.all (c.eventually_exists_pow_mul_eq_add_z_mul <| c.v6 (by bound)
    (left_ne_zero_of_mul (E 1 ▸ q)) <| E · ▸ c.extendedCoord_mem_bicommutant i _)).exists
  have I l := (IsIntegral.of_finite ℤ_[p] (w l)).algebraMap (B := Ainf)
  have := by_contra fun h ↦ N (pi_dvd_iff.2 fun _ ↦ ((IsIntegral.isLocalHom _ (integralClosure _ BdR)).1 _ (.of_mul_eq_one_right ⟨_, mul_mem ((J.mul (I 1).algebraMap.tower_top).sub (I 0).algebraMap.tower_top).inv.tower_top (sub_mem (algebraMap_mem _ (u 0)) (J.tower_top.smul (u 1)))⟩ (Subtype.ext ((mul_assoc ..).trans ((inv_mul_eq_one₀ h).2 (by
    simp [← coe_inj _ BdR, smul_def, ← algebraMap_apply] at *
    norm_cast at *; grind)))))).dvd)
  have ⟨r, t, h⟩ := (w 1).exists_eq_pow_p_mul' fun k ↦ N (((isUnit_p.pow m).map (ofId ..)).dvd_mul_left.1 ⟨u, funext (by simp_all)⟩); use r, ↑t⁻¹ * w 0, (coe_inj _ BdR).1 ?_; have := congr(ofId Ainf BdR $(t.mul_inv_eq_iff_eq_mul.2 h)); simp [h₀, field, ← algebraMap_apply] at *; grind
lemma Bcris.exists_witt_ratio {a b : Bcris} (h₀ : b ≠ 0) (h : ∀ᶠ g : Gp p in nhds 1, b * g • a = g • b * a) : ∃ f n, ∃ w : WittFq f, p ^ n * a = (w : Ainf) * b :=
  have ⟨U, h⟩ := NonarchimedeanGroup.is_nonarchimedean _ h
  ⟨_, exists_witt_coeff_of_isChartOf (exists_kummer_chart _ (𝒥 := ⟨_, ⟨U.1.range_subtype ▸ U.2⟩⟩)).choose.chart_isChartOf h₀ (h ·.2)⟩
end
namespace Lift.KummerChart
open Polynomial FrobGroup ValuationRing NeZero
variable {p} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ] (a : ℕ)
def galMonoid := MonoidHom.mrange (inr.comp k.Γ'.subtype)
def zTau := tau * k.z
lemma frobE_eq : (k.frobE a).1 = φ ^ a • k.E := by erw [phi_pow_smul, k.coe_φ_pow]
lemma m7 : ¬↑p ∣ (k.frobE a).1 := fun ⟨_, h⟩ ↦ not_p_dvd_xi (.trans ⟨_, by simpa [frobE_eq, ← eq_inv_smul_iff] using h⟩ k.associated_E_xi.dvd)
def frobEUnit := (isUnit_WittCFlat_of_not_p_dvd (m7 a)).unit
def zTauUnit := (isUnit_WittCFlat_of_not_p_dvd (Ainf.prime_p.not_dvd_mul not_p_dvd_tau k.not_p_dvd_z)).unit
variable {a} {b : ℕ} (g : k.galMonoid)
attribute [local simp] Chart.theta_z_ne_zero ne frobE_dvd_iff zTau coeff_derivative
@[simp high] lemma d6 : (k.frobE a).1 ≠ 0 := m7 a ∘ by aesop
lemma exists_derivative_dvd_p_pow : ∃ P : (WittFq k.f)[X], k.E ∣ aeval k.z P ∧ theta (aeval k.z P.derivative).1 ∣ p ^ differentExp := by
  choose r h u using k.w4 0 (one_mul _); obtain ⟨⟨R, D⟩, _, -⟩ := k.w4 0 rfl (k.z ^ k.e); simp [degreeLT, differentExp] at D ⊢
  use X ^ k.e - R, by simpa
  split; simp [*, (by aesop : R.derivative = 0)]; refine (dvd_total ..).resolve_right fun e ↦ ?_; choose x H using k.coord₀_coe _ ▸ k.z5 0 _ (p ^ _) _ (by simpa)
  have t := u _ (p ^ _ • _) (by simpa [mul_sub] using (h x).mul_left _) ▸ u _ ⟨_, by
    simp [degreeLT]; grind⟩ (dvd_sub_comm.1 H)
  simpa [by simpa [Padic.norm_eq_zpow_neg_valuation] using PadicComplex.norm_extends' p k.e, D, OC.dvd_iff_norm_le, norm_p_eq_inv, NeZero.one_le, inv_le_inv₀, pos, pow_le_pow_iff_right₀, Fact.out] using (theta.comp (algebraMap ..)).map_dvd ⟨_, congr($(t).1.coeff k.e.pred).trans (nsmul_eq_mul ..)⟩
@[simps] instance : OverGp Γ' p := ⟨toGp.comp _, ⟨Subgroup.isOpen_of_mem_nhds _ (nhds_one_le_map_nearOne Γ (nearOne_le (⟨·, rfl⟩)))⟩⟩
lemma not_frobE_dvd_p a : ¬(k.frobE a).1 ∣ p := by simp
lemma frobE_dvd_phi_pow_tau (h : a < b) : (k.frobE a).1 ∣ φ ^ b • tau := have ⟨b, e⟩ := a.exists_eq_add_of_lt h
  by simp [e, pow_add, mul_smul, j4, phi_pow_smul b]
lemma not_frobE_dvd_frobE_of_ne (h : a ≠ b) : ¬(k.frobE a).1 ∣ k.frobE b := fun d ↦ by
  refine h.lt_or_gt.elim (?_ ∘ (Prime.associated_of_dvd ?_ ?_ d).dvd'.trans ∘ frobE_dvd_phi_pow_tau)
    (?_ ∘ d.trans ∘ frobE_dvd_phi_pow_tau) <;> simp [Prime, isUnit_iff_dvd_one]
lemma smul_phi_pow_comm {X} [MulAction (FrobGroup Γ) X] (x : X) : g • φ ^ a • x = φ ^ a • g • x :=
  by erw [smul_smul, smul_smul, Commute.pow_right (.prod (.all ..) (.one_right _))]
lemma phi_pow_smul_z : φ ^ a • k.z.1 = k.z ^ p ^ a := by simp [phi_pow_smul, k.z_eq_teichmuller]
lemma zTau_dvd_phi_pow_smul a : k.zTau ∣ φ ^ a • k.zTau := by simp [k.z_eq_teichmuller, phi_pow_smul, mul_dvd_mul, tau, sub_one_dvd_pow_sub_one]
lemma not_frobE_dvd_zTau a : ¬↑(k.frobE a) ∣ k.zTau := (·.trans (zTau_dvd_phi_pow_smul a)).mt (by simp)
lemma zTau_mul_E_dvd_smul_sub (s : k.S) : zTau * k.E ∣ g • s - s := let ⟨_, g, rfl⟩ := g
  by obtain ⟨⟨h, hg⟩, _⟩ := fixes g, k.theta_z_ne_zero
     grw [zTau, mul_rotate, mul_assoc, k.associated_E_mul_tau_mu.dvd]; apply k.dvd_smul_sub_of_fixesLambda _ h
     erw [← theta_smul, k.z_eq_teichmuller, smul_teichmuller] at *
     cases untilt_dvd_iff.1 (by simpa using hg.symm.dvd)
     simp_all [v2, mul_dvd_mul, ← mul_sub_one]
end Lift.KummerChart
end
open TensorProduct Filter Classical Submodule Finsupp Module LinearMap Function Polynomial Lift Free Bcris Multiplicative IsPrincipal Fint Multiset
attribute [-simp] Set.forall_neg_mem _root_.map_eq_zero map_smul_of_tower smul_assoc
attribute [local simp] isWeilPair_zero_iff tensorAction_smul
variable {p} [ThePrime p] {Γ R'} [Group Γ] [CommRing R'] [Algebra ℤ_[p] R'] [𝒥 : OverGp Γ p] {F} (hF : nearOne Γ ≤ F) {s t m k R T T' T''} [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup T'] [Module R' T'] [Module ℤ_[p] T'] [IsScalarTower ℤ_[p] R' T'] {ρ σ : Representation R Γ T} {ρ' : Representation R' Γ _} {ι κ : Type*} (h : IsPotCrys ρ) (hs : IsWeilPair (𝒥.toGp s) m) {b : Bcris} [Finite κ] {S : κ → _} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, Module ℤ_[p] (S i)] [∀ i, IsScalarTower ℤ_[p] R (S i)] {τ : ∀ _, Representation R Γ _} {P} (hA : ∀ i, IsAdmissible (τ i) F) (f : ∀ i, T' →ₗ[ℤ_[p]] S i) (hf : ∀ i, ∀ᶠ g in F, ∀ x, f i (ρ' g x) = τ i g (f i x)) (hi : ∀ x, (∀ i, f i x = 0) → x = 0)
lemma eventually_tensorAction_eq {x : ι → _} (hx : ∀ i, x i ∈ fixedPeriods ρ Bcris F) a : ∀ᶠ g in F, tensorAction _ (toGp g) (ρ g) (linearCombination Bcris x a) = linearCombination _ x (toGp g • a) := a.induction_linear
  (by simp) (fun _ _ ↦ (·.mp <| ·.mp (by aesop))) fun i _ ↦ (hx i).mp (by aesop)
@[simp] lemma b6 a b x : coefEnd R T a (b ⊗ₜ x) = b ⊗ₜ (a • x) := rfl
lemma map_eq_zero_of_roots {K A} [Field K] [IsAlgClosed K] [CharZero K] [Ring A] (φ : K[X] →+* A) {P
  Q} : (∃ n > 0, φ X ^ n = 1) → φ Q = 0 → (∀ x, Q.IsRoot x → P.IsRoot x) → φ P = 0 := fun ⟨n, k⟩ ↦
  by grind [(X_pow_sub_one_separable_iff.2 (mod_cast k.1.ne')).of_dvd ((mem_iff_generator_dvd (RingHom.ker φ)).1 (by aesop)), mem_iff_generator_dvd, =_ RingHom.mem_ker, mem_roots', IsRoot.dvd, Separable.ne_zero, nodup_roots, le_iff_subset, subset_iff, = IsAlgClosed.dvd_iff_roots_le_roots]
lemma IsWeilPair.inv : IsWeilPair (toGp s) 0 → IsWeilPair (toGp s⁻¹) 0 := by simp
include hi in
open AlgebraTensorModule in
private lemma k0 : ∃ Ψ : _ →ₗ[Bcris] _, LeftInverse Ψ fun x i ↦ (f i).baseChange Bcris x := ⟨liftBaseChange _ (curry (lTensor ℚ_[p] Bcris (pi f)).leftInverse 1) ∘ₗ piRightInv .., fun x ↦ by
  induction x <;> simp_all [← Pi.add_def]
  erw [leftInverse_apply_of_inj (ker_eq_bot.2 (Flat.lTensor_preserves_injective_linearMap _ (.of_ker _ (hi · ∘ congrFun)))) (1 ⊗ₜ _), ← tmul_eq_smul_one_tmul]⟩
section
include hF
private lemma r5 (w : ι →₀ Bcris) (n : b ≠ 0) (h : ∀ᶠ g in F, b • toGp g • w = (toGp g • b) • w) : ∃ a, w = b • a ∧ ∀ᶠ g in F, toGp g • a = a := ((range_mapRange _ (mul_zero b)).ge fun i ↦ .imp (by tauto) (let ⟨_, m, _, e⟩ := exists_witt_ratio n (nhds_one_le_map_nearOne Γ (hF (h.mono fun _ k ↦ congr($k i))))
  ((BPlus.isUnit_p.pow m).map (algebraMap ..)).dvd_mul_left.1 (by simp [e]))).imp
  (by rintro a rfl; simp_all [Finsupp.ext_iff, mul_left_comm b, smul_eq_zero_iff_eq])
lemma le_of_fixed_mem_of_saturated {W W' : Submodule Bcris (ι →₀ Bcris)} (hs : ∀ b ≠ (0 : Bcris), ∀ w, b • w ∈ W → w ∈ W) (hW : ∀ v ∈ W, ∀ᶠ g in F, toGp g • v ∈ W) (H : ∀ w ∈ W, (∀ᶠ g in F, toGp g • w = w) → w ∈ W') : W ≤ W' := b2 1 fun v hv n h ↦ (ne_iff.1 n).rec fun k n ↦ (r5 hF v n ((hW v hv).mono fun _ ↦ (h _ · (by aesop) k))).imp
  (by simp; grind [Finsupp.smul_apply, smul_eq_mul, left_eq_mul₀, mul_eq_zero])
lemma IsAdmissible.k1 (h : IsAdmissible ρ F) : ∃ s : Set (fixedPeriods ρ Bcris F), ∃ v : Basis s Bcris _, ∀ i, v i ∈ fixedPeriods ρ Bcris F := (exists_maximal_linearIndepOn _ (·.1)).imp fun s ⟨hs, hm⟩ ↦ ⟨.mk (id hs) (h ▸ span_le.2 fun y hy ↦ byCases (subset_span ⟨⟨⟨_, hy⟩, ·⟩, rfl⟩) (by
  rw [Set.image_eq_range, ← range_linearCombination] at *
  exact (hm _ · |>.rec fun b ⟨hb, w, o⟩ ↦ (r5 hF w hb ((eventually_tensorAction_eq (·.1.2) w).mp (hy.mono fun g k l ↦ hs (by simp [*, smul_comm b, ← l])))).imp (by aesop)))), by simp⟩
include hA
lemma IsAdmissible.b1 (Φ : ∀ i, _ →ₗ[Bcris] Bcris ⊗ S i) (H : ∀ i, ∀ᶠ g in F, ∀ x, Φ i (tensorAction Bcris (toGp g) (ρ' g) x) = tensorAction _ (toGp g) (τ i g) (Φ i x)) (Ψ : _ →ₗ[Bcris] _) (e : LeftInverse Ψ (pi Φ)) : IsAdmissible ρ' F := by
  choose s v hv using (hA · |>.k1 hF)
  let Θ := (Pi.basis v).1.1 ∘ₗ pi Φ; have I : Injective Θ := by simp [Θ, e.injective]
  have E x : ∀ᶠ g in F, Θ (tensorAction _ (toGp g) (ρ' g) x) = toGp g • Θ x := .mono (.all fun i ↦ (H i).and (eventually_tensorAction_eq (hv i) ((v i).1 (Φ i x)))) (by aesop)
  exact top_unique ((gciMapComap I).l_le_l_iff.1 (le_of_fixed_mem_of_saturated hF
    (by simp_all [Θ, range_comp, range_eq_ker_of_leftInverse e]) (by simp; peel E; bound)
    fun _ ⟨y, h⟩ k ↦ ⟨y, subset_span ((E y).mp (k.mono (by lia))), h.2⟩))
include hf hi
lemma IsAdmissible.of_jointly_injective : IsAdmissible ρ' F := (k0 f hi).rec
  (.b1 hF hA _ (hf · |>.mono fun _ ↦ (tensorAction_periodTensorMap · _ · |>.symm)))
end
section
include hs
lemma IsWeilPair.smul_eq_of_fixed_nearOne (h : ∀ᶠ g in nearOne Γ, toGp g • b = b) : (ofAdd m, toGp s) • b = b := by obtain ⟨f, n, w, e⟩ := exists_witt_ratio one_ne_zero (nhds_one_le_map_nearOne Γ (by simpa)); simpa [← smul_algebraMap_eq_algebraMap_smul, ← by simpa using e, (NeZero.of_faithfulSMul ℚ_[p] ..).1] using congrArg (algebraMap _ Bcris) ((w.j7 _).rec fun _ k ↦ (v7 (k ▸ toWittResidue_smul_of_isFrob hs _ :) ▸ k :))
include h
@[local simp] lemma linearFrob_apply {d} : d ∈ Dpcris ρ → linearFrob ρ s m d = tensorAction _ (ofAdd m, toGp s) (ρ s) d := let ⟨_, v, hv⟩ := h.k1 le_rfl
  @epsilon_spec (End ..) (∀ d ∈ _, · d = _) ⟨v.constr ℕ _, (reindex_equiv v.1.symm).1.2 fun c a ↦ by
     simp [(hs.smul_eq_of_fixed_nearOne (b := c ·) (.mp a ((eventually_tensorAction_eq hv c).mp (by simp_all [v.ext_elem_iff])))), Finsupp.sum, linearCombination]
     rfl⟩ d
lemma linearFrob_mul (ht : IsWeilPair (toGp t) k) : linearFrob ρ (s * t) (m + k) = linearFrob ρ s m * linearFrob ρ t k := ext_on h fun d hd ↦ .trans (by simp_all [↓hs.mul, tensorAction_tensorAction]) (linearFrob_apply h hs (linearFrob_apply h
  ht hd ▸ ((tendsto_comap_iff.2 (by convert (tendsto_comap.const_mul _).mul_const (toGp t) <;>
  aesop) : Tendsto (t⁻¹ * · * t) (nearOne Γ) _).eventually hd).mono fun g e ↦ .trans (by
    repeat erw [tensorAction_tensorAction (M := FrobGal)]; simp [← map_mul, mul_assoc])
  (congrArg _ e))).symm
lemma linearFrob_pow n : linearFrob ρ (s ^ n) (n * m) = linearFrob ρ s m ^ n := n.rec (ext_on h fun _ hd ↦ by simpa [*] using! mem_of_mem_nhds (mem_comap'.1 hd) toGp.map_one)
  (by simp_all [pow_add, add_mul, linearFrob_mul, ↓hs.pow])
lemma baseChange_linearFrob (h' : IsPotCrys ρ') (f : T →ₗ[_] _) (hf : ∀ᶠ g in nearOne Γ ⊔ pure s, ∀ x, f (ρ g x) = ρ' g (f x)) x : f.baseChange _ (linearFrob ρ s m x) = linearFrob ρ' s m
  (f.baseChange _ x) := by induction eq_top_iff'.1 h x using span_induction <;> simp_all
  [fixedPeriods.map hf.1, tensorAction_periodTensorMap hf.2, baseChange_eq_periodTensorMap]
lemma commute_coefEnd_linearFrob a : Commute (coefEnd R T a) (linearFrob ρ s m) :=
  ext (baseChange_linearFrob h hs h _ (by simp))
lemma linearFrob_twist_cyclotomicGp (d : ℕ) (e : ∀ g x, σ g x = (χ g ^ (-d : ℤ)).1 • ρ g x) : linearFrob σ s m = (p : Bcris) ^ (m * d) • linearFrob ρ s m := ext_on h fun y a ↦ let ⟨_, _, l, k⟩ := exists_tate_twist_unit _ e
  by simpa [*, mul_smul, zpow_mul, pow_mul] using (linearFrob_apply (h.tate_twist _ e) hs (a.out.mono fun g a ↦ k 0 g y ▸ by simpa)).trans (k ..)
end
include hs hf hi in
lemma IsKilledBy.of_jointly_injective (k : nearOne Γ ⊔ pure s ≤ F) (h : ∀ i, IsKilledBy (τ i) s m P)
    {φ Q} (e : .map φ Q = P) (hφ : ∀ i a x, f i (a • x) = φ a • f i x) : IsKilledBy ρ' s m
  Q := have a := IsAdmissible.of_jointly_injective le_rfl (h · |>.1) f (hf · |> k |>.1) hi
  ⟨a, ext fun x ↦ (k0 f hi).choose_spec.injective (funext fun i ↦ .trans (by
      clear e; induction Q using recOnHorner generalizing x <;>
        simp [*, baseChange_linearFrob a hs (h i).1 _ (k (hf i))]
      induction x <;> simp [*]) (congr($((e ▸ h i :).2) (baseChange _ (f i) x)).trans (by simp)))⟩
lemma IsCrystalline.linearFrob_eq_one (h : IsCrystalline ρ) (hs : IsWeilPair (toGp s) 0) : linearFrob ρ s 0 = 1 := ext_on h fun _ hd ↦ linearFrob_apply h.isPotCrys hs ((nearOne Γ).univ_mem' hd) ▸ hd s
variable [AddCommGroup T''] [Module R T''] [Module ℤ_[p] T''] [IsScalarTower ℤ_[p] R T''] (c : ℤ) {σ : Representation R Γ T''} (v : IsPotCrys σ) (B : (_ →ₗ[ℤ_[p]] T →ₗ[ℤ_[p]] T' : Type)) (e : ∀ g x y, B (σ g x) (ρ g y) = ρ' g (B x y))
lemma IsPotCrys.eventually_linearFrob_eq_one [Module.Finite R T] [Free.{0} R T]
    (h : IsPotCrys ρ) : ∀ᶠ g in nearOne Γ, IsWeilPair (toGp g) 0 → linearFrob ρ g 0 = 1 := by
  choose n a d hd using (mem_span_set'.1 <| h.ge (x := 1 ⊗ₜ chooseBasis R T ·) ⟨⟩)
  filter_upwards [Eventually.all fun l ↦ .all (d l · |>.2)] with g k s
  ext t; rw [← (chooseBasis R T).sum_repr t]
  simp [↓map_sum, ← b6, ← End.mul_apply, ← (commute_coefEnd_linearFrob h s _).eq]
  simp [← hd, linearFrob_apply h s _ ▸ k _ _]
include e
private lemma j0 {x y} : x ∈ fixedPeriods σ _ F → y ∈ fixedPeriods ρ _ F → baseChangePairing B x y ∈ fixedPeriods ρ' Bcris F := (·.mp <| ·.mono fun g k h ↦ (baseChangePairing_map _ (e g) ..).symm.trans congr(baseChangePairing B $h $k))
lemma IsAdmissible.of_bilinear (h : IsAdmissible σ F) (k : IsAdmissible ρ F) (H : Surjective (lift B)) : IsAdmissible ρ' F := isAdmissible_of_one_tmul_mem_span (H.forall.2 fun z ↦ by
  induction z <;> simp_all [tmul_add, add_mem]
  simpa [baseChangePairing] using BilinMap.apply_apply_mem_of_mem_span _ _ _ _ (fun _ a _ b ↦ subset_span (j0 B e a b)) (1 ⊗ₜ _) (1 ⊗ₜ _) (h.ge ⟨⟩) (k.ge ⟨⟩))
include h hs v in
lemma linearFrob_baseChangePairing (w : IsPotCrys ρ') : (baseChangePairing B).compl₁₂ (linearFrob σ s m) (linearFrob ρ s m) = (baseChangePairing B).compr₂ (linearFrob ρ' s m) := ext_on v fun _ _ ↦ ext_on h fun _ _ ↦ by simp_all [linearFrob_apply, j0 B e]; exact baseChangePairing_map _ (e s) ..
omit e
include hF
lemma IsAdmissible.of_pairing [Module.Finite R T] [Free.{0} R T]
    (w : IsAdmissible ρ F) (b : T'' ≃ₗ[R] T →ₗ[R] R) (H : ∀ g x y, b (σ g x) (ρ g y) = (χ g ^ c).1 • b x y) : IsAdmissible σ F ∧ ∀ s Q, IsWeilPair (toGp s) 0 → IsKilledBy ρ s 0 Q → IsKilledBy σ s⁻¹ 0 Q := by
  let B := b.restrictScalars₁₂ ℤ_[p] ℤ_[p]
  have A {F : Filter Γ} : IsAdmissible (charRep R (χ ^ c)) F := isAdmissible_of_cyclotomicGp_zpow c (by tauto)
  let ⟨Ψ, r⟩ := k0 (B.flip ∘ chooseBasis R T) fun _ ↦ (b.map_eq_zero_iff.1 <| Basis.ext _ ·)
  have q a y x : (B.flip y).baseChange _ (coefEnd R _ a x) = baseChangePairing B x (1 ⊗ₜ (a • y)) := by induction x <;> simp_all [B, baseChangePairing, smul_tmul']
  choose n a d hd using (mem_span_set'.1 <| w.ge (x := 1 ⊗ₜ chooseBasis R T ·) ⟨⟩)
  have v := b1 hF (fun _ ↦ A) ((baseChangePairing B).flip <| d _ <| Sigma.snd ·) (d _ ·.2
    |>.2.mono fun g h x ↦ (congrArg _ h).symm.trans (baseChangePairing_map _ (H g) ..)) (Ψ ∘ₗ pi
    fun l ↦ ∑ k, a l k • proj ⟨l, k⟩) (by simpa [← hd, LinearMap.pi, by simpa using q 1] using! r)
  use v, fun s Q hs ⟨P, K⟩ ↦ (fun v ↦ ⟨v, ext fun x ↦ r.injective (funext ?_)⟩) (v.mono hF)
  obtain _ := linearFrob_pow v hs 0, fun s (h : IsWeilPair (toGp s) 0) ↦
    congr($(linearFrob_baseChangePairing P h v B ‹_› A) ∘ₗ linearFrob σ s⁻¹ 0)
  simp_all [DFunLike.ext_iff, ← End.mul_apply, ← linearFrob_mul, IsCrystalline.linearFrob_eq_one A]
  simpa [eval₂_eq_sum_range, ← linearFrob_pow, pow_mem, *, (commute_coefEnd_linearFrob P ..).eq] using fun _ ↦ congr(baseChangePairing B x $(K (1 ⊗ₜ _)))
