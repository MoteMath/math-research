import Lib.PadicHodge.Crystalline.RegularityFrobenius
import Lib.PadicHodge.BlochKato.CocycleContinuity
section
open Algebra IsScalarTower IsLocalization.Away algebraMap Function
variable {p} [ThePrime p]
lemma y2 (y : Bcris) (a : ℕ) {ν} (hν : mu ∣ ν) (h : ∀ n, ↑((⟨.ofAdd n, 1⟩ : FrobGal) • y) ∈ hodgeFil (-a)) : ∃ c : BPlus, c = ν ^ a • y := hν.elim fun s E ↦ (surj (mu : BPlus) (ν ^ a • y)).rec (·.rec (by grind) fun N ih ⟨c, H⟩ ↦ ih
  ((c.dvd_of_thetaBPlus_frobEnd_eq_zero v2 fun n ↦ w7 ▸ algebraMap_mem_hodgeFil_one_iff.1 (hodgeFil_anti (by lia) (Set.mem_of_eq_of_mem (by
  linear_combination (norm := (simp [E, smul_def, ← algebraMap_apply, FrobGal.smul_def]; ring))
    -congr((↑((⟨.ofAdd n, 1⟩ : FrobGal) • $H) : BdR)))
  (mul_mem_hodgeFil (h n) (algebraMap_mem_hodgeFil_iff_xi_pow_dvd.2 (.mul_left (pow_dvd_pow_of_dvd (map_dvd _ (theta_eq_zero_iff_xi_dvd.1 (by simp))) (a + N.succ)) ↑(frobEnd^[n]
  s ^ a))))))).imp fun _ _ ↦ (algebraMap_isUnit (mu : BPlus)).mul_left_cancel (by grind)))
lemma Bcris.exists_padic_eq_of_frobEnd_fixed {y : Bcris} (h : frobEnd y = y) {x : BdRPlus} (hx : (y : BdR) = x) : ∃ a : ℚ_[p], a = y := by
  obtain ⟨c,
    rfl⟩ := by simpa [FrobGal.smul_def, iterate_fixed, *] using y2 y 0 dvd_rfl
  simp [injective_BPlus_Bcris.eq_iff] at h; let ⟨m, _, H⟩ := c.exists_p_pow_mul_eq_amax; let ⟨a, e⟩ := v4 {_} 0 1 (by simp [x1]) (by simp_all [← H]) _ H; obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_frobenius_eq a ((coe_inj _ BPlus).1 (by simp [← frobEnd_eq_frobenius, ← j1, e, h])); use b / p / p ^ m, (coe_inj _ BdR).1 (by simpa [field, algebraMap_apply _ ℚ_[p] BdR b, NeZero.ne, ← algebraMap_apply] using congr(($e : BdR)))
end
section
namespace Lift.Chart
open BPlus Algebra Matrix MulSemiringAction Function Witt RingHom Ideal Quotient PreTilt
open WittVector renaming constantCoeff → π
variable {p} [ThePrime p] {d} {c : Chart} [Fintype d]
private lemma exists_det_ne_zero {S D} [CommRing S] [Semiring D] [Nontrivial D] (R : S →+* D) (X : Set (d → S)) (h : ∀ t, (∀ x ∈ X, R (t ⬝ᵥ x) = 0) → ∀ i, R (t i) = 0) : ∃ N, R (det N) ≠ 0 ∧ ∀ k, N k ∈ X := (exists_maximalFor_of_wellFoundedGT _ (· · ∈ X) ⟨1, by simp⟩).imp fun N m ↦ ⟨m.1, fun k ↦ by_contra fun hk ↦ m.1 (by simp [N.det_eq_sum_mul_adjugate_row k, h (N.adjugate · k) fun x h ↦ by_contra fun n ↦ hk (@m.2 (N.updateRow k x) (by simpa [← cramer_transpose_apply, ← adjugate_transpose, cramer_eq_adjugate_mulVec]) (fun l ↦ by by_cases l = k <;> simp [*]) k (by simpa))])⟩
attribute [-simp] map_smul smul_right_inj Matrix.mul_smul
attribute [local simp] map_smul' smul_smul mulVec_sub Set.image_pair pow_succ mul_sub Units.smul_def comp_def map_mulVec
attribute [local simp ←] mul_assoc mul_pow Subalgebra.smul_def OFlat.v9 iterate_frobenius
lemma IsPeriodMatrix.exists_frame {U h v} (hU : c.IsPeriodMatrix U h v) : ∃ (Q L Z Z' : Matrix d d _) (B : Matrix d d c.S), Q * L = tau ^ h • 1 ∧ (∀ i j, Z i j ∈ c.bicommutant) ∧ U * Z = c.E.1 ^ h • Q.map ainfToBPlus ∧ Z' * Z = c.E.1 ^ h • 1 ∧ Q.map frobEnd = v • (Q * B.map (↑)) ∧ ∀ g, c.FixesThetaZ g → ∃ G, g • Z = Z * .map G ainfToBPlus := by
  obtain ⟨⟨Q, Z, h₀, hZ, e, hN, hA⟩, ⟨⟨U', _⟩, ⟨F, -, _, -, eF⟩⟩, ⟨u, hu, eu⟩, ⟨t, ht⟩, q, _, eq⟩ := hU.k1, id hU, c.z9, c.associated_E_mul_tau_mu.dvd, c.exists_bicommutant_mul_p_eq_one
  have act (m : FrobGal) (ρ : Matrix d d _) F w r (h₁ : .map ρ ainfToBPlus * m • U = U * F) (h₂ : w * ainfToBPlus (m • c.E.1) = ainfToBPlus (c.E.1 * r)) : U * w ^ h • (F * m • Z) = c.E.1 ^ h • (r ^ h • ρ * m • Q).map ainfToBPlus := by
    erw [mul_smul_comm, ← mul_assoc, ← h₁, mul_assoc, ← map_mul (toRingHom _ _ m).mapMatrix]; ext; simp [@smul_def _ BPlus, mul_apply, Finset.mul_sum, mul_left_comm (ainfToBPlus _), *]
  choose b o using (hN _ _ (fun i ↦ mul_mem (pow_mem (mul_mem (q1 _) hu) h) (sum_mem fun _ _ ↦ by apply_rules [mul_mem, frobEnd_mem_bicommutant])) congr(col $(act _
    (v⁻¹ • 1) F _ 1 (congr(_ * $eF).trans (by simp)) (by simpa using! congr(_ * $eu))) ·))
  have o : Q * bᵀ.map (↑) = _ := ext_col o; let R := π.domRestrict c.S
  have A g H := act (1, g) _ 1 1 _ ((hU.3 g H).choose_spec.trans (by simp)) (by
    erw [one_mul, ← (c.associated_smul_E g).choose_spec])
  by_cases h₁ : ↑p ∣ Q.det
  · have H i j t : t ⬝ᵥ c.adicBasis.coord i ∘ Q j = c.adicBasis.coord i ((Q *ᵥ (t ·)) j) := by
      simp [mulVec_eq_sum, dotProduct]
    have ⟨N, D, hX⟩ := exists_det_ne_zero R {c.adicBasis.coord i ∘ Q j | (i) (j)} fun t h i ↦ (pi_dvd_iff.2 fun j ↦ p_dvd_iff.2 ((OFlat.q3 (mt Ainf.isUnit_iff_isUnit_constantCoeff.2 c.4)).1.1 _ fun n ↦ .zero.2 (mem_comap.1 ((Submodule.restrictScalars_mem ..).1 (c.adicBasis.m3 (by
        simp [Ideal.map_pow, ← map_le_iff_le_comap]; rfl) (mul_mem_right _ _ <| ker_le_comap π <| H ..
        ▸ h _ ⟨·, _, rfl⟩)))))).rec fun w hw ↦ (hN w (Z *ᵥ q • ainfToBPlus ∘ (t ·)) (fun _ ↦ sum_mem (by simp [mul_mem, *])) (by ext; simpa [e, eq] using congr(_ • (q * ainfToBPlus ($hw _))))).rec fun | _, rfl => p_dvd_iff.1 ⟨_, congr($(mulVec_injective_of_det_ne_zero h₀ (hw.trans (Q.mulVecLin.2 ..).symm)) i)⟩
    choose σ τ S using hX
    have ker {m ρ C a} (h : C = ρ * m • Q) : Q.map π *ᵥ a = 0 → C.map π *ᵥ toRingHom FrobGal _ m ∘ a
      = 0 := (by simpa [h, ← Pi.zero_def] using! congr(_ *ᵥ toRingHom _ _ m ∘ $(·)))
    have ⟨a, ν, e₁, hw, hm⟩ : ∃ a ν, a ν = 1 ∧ Q.map π *ᵥ a = 0 ∧ ∀ g : OFlat →+* OFlat, Q.map π *ᵥ g ∘ a = 0 → g ∘ a = a := by
      have ⟨w, h, hm⟩ := exists_minimalFor_of_wellFoundedLT _ support (exists_mulVec_eq_zero_iff.2 (π.map_det Q ▸ p_dvd_iff.1 h₁))
      choose ν a ha using by
        simpa [mem_span_singleton] using @Finite.exists_max _ _ _ (ne_iff.1 h.1).nonempty _ (span {w ·})
      generalize e : w ν = t at *; cases (funext ha : w = t • a); use a, ν, ?_, ?_, fun g h ↦ by_contra (@hm _ ⟨sub_ne_zero.2 ·, ?_⟩ ?_ ν ?_ ?_) <;> aesop
    refine let K := R bᵀ.det * R N.det; (mul_ne_zero (fun H ↦ h₀ (eq_of_forall_pow_dvd_sub p (·.rec (by simp) fun n h ↦ (map_dvd_iff (MulEquiv.ofBijective _ z4)).1 (by
      simpa [map_det, IsUnit.pow, ← det_mul, o] using! mul_dvd_mul h (p_dvd_iff.2 H)))))
      D (Perfection.ext (f := K) fun M ↦ ?_)).rec
    choose n s e using ((add_right_injective M).nat_tendsto_atTop.eventually (.all fun i ↦ c.y5 (fun g hg ↦ congr($(hm _ (ker (by simpa [↓← ext_iff, smul_def, e, ↓E_ne_zero, -Matrix.map_mul]
      using ((by ext; simpa using congr($(hZ _ _ ⟨(toRingHom _ _ g).toAddHom, by
      simp [c.S.smul_def, smul_def, hg]⟩ y7) 1) : g • Z = Z) ▸ A g
      (by simp [← theta_smul, FixesThetaZ, FixesLambda, hg ⟨_, _⟩]) :)) hw)) i)) M)).exists
    have ⟨C, hC, ha⟩ : ∃ C, K * R (det C) ∣ K ^ p ^ n ∧ Q.map π *ᵥ C.map R *ᵥ a ^ p ^ n = 0 := n.rec
      ⟨1, by simpa⟩ fun n ⟨C, h, e⟩ ↦ ⟨bᵀ * C.map c.φ, by
      grw [det_mul, map_mul, pow_succ, pow_mul, ← h, mul_pow, ← pow_dvd_pow K (Fact.out : 1 < p), Dvd.intro _ (refl K)]; simp [map_det]; rfl, by simpa [pow_mul, Pi.pow_def] using! ker o e⟩
    simpa [OFlat, K, mul_assoc, by simpa using (map_det ..).trans (det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (funext fun k ↦ (((coeff _).comp R).map_mulVec (N * C) ..).symm.trans (by
         erw [← mulVec_mulVec, mulVec, dotProduct_comm, ← S, H, ← q7, eq_add_of_sub_eq (c.z5 _ _ p _ (by simpa [OFlat, ← eq_zero_iff_dvd, q7, mulVec_eq_sum, e] using! congr(coeff (M + n) ($ha _)))).choose_spec.choose_spec]
         simp [CharP.cast_eq_zero, frobE_dvd_iff.1 dvd_rfl])) ((e ν).subst (by simp [*])))]
      using! map_dvd (coeff (M + n)) hC
  have hQ {X Y} (eY : U * Y = c.E.1 ^ h • .map X ainfToBPlus) : ∃ L, Q * L = X := by
    choose a e using fun i ↦ (hA _ _ congr(col $eY ·) _ _ _ h₁ congr($Q.adjugate_mul i)); use of a; simp [← smul_right_inj h₀, ← mul_smul_comm, mul_adjugate, ← (ext e : _ * X = Q.det • of a)]
  choose k a w ea using (q0 · 0 h); obtain ⟨⟨n, hn⟩, L, hL⟩ := Finite.exists_le (k ∘ U.uncurry), @hQ (tau ^ h • 1) U' (by simp [-map_pow, *])
  have hX : (U.map fun y ↦ p ^ (n - k y) * a y).map ainfToBPlus = U * ainfToBPlus p ^ n • (1 - t ^ h • U' * U.map
    w) := by ext i j; simp [*, ← pow_sub_mul_pow _ (hn (i, j))]; clear * - ea ht; grind [smul_def]
  obtain ⟨Y, rfl⟩ : Q.map ainfToBPlus ∣ U := (hQ (by rw [hX, ← mul_smul_comm])).imp' (q ^ n • ·.map
    ainfToBPlus + (t * c.E) ^ h • L.map ainfToBPlus * U.map w) (by simp +contextual [mul_add, ← Matrix.map_mul, *, -map_pow])
  use Q, L, Z, Y, bᵀ, hL, hZ, e, (isRegular_of_isLeftRegular_det (mul_right_injective₀
    (mt (ainfToBPlus.map_det Q).trans (by simpa)))).1 (by simpa), by simp [o]; rfl, fun g H ↦ (hQ (A g H)).imp fun L hL ↦ isLeftRegular_iff_mulVec_injective.2 hU.mulVec_injective (by simpa [← hL, e] using! A g H)
end Lift.Chart
end
open RingHom Algebra BdRPlus Function Matrix algebraMap Module.Basis
seal Module.Basis.baseChange
attribute [local simp ←] IsScalarTower.algebraMap_apply
attribute [local simp] AlgHom.map_smul_of_tower comp_def dotProduct hodgeMatrix mul_assoc smul_smul
variable {p} [ThePrime p] {T Γ ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Group Γ] [Fintype ι] [𝒥 : OverGp Γ p] {ρ : Representation ℤ_[p] Γ T} (a b : ℕ) {c} (hc : Lift.Chart.IsChartOf c 𝒥.toGp)
include hc
lemma Lift.Chart.IsChartOf.v1 {b : Bcris} (hb : ∀ g, 𝒥.toGp g • b = b) : ∃ s ∈ c.bicommutant, s = b := by obtain ⟨⟨u, h, f⟩, m, w, e⟩ := c.exists_bicommutant_mul_p_eq_one, exists_witt_coeff_of_isChartOf hc one_ne_zero (by simpa); exact ⟨_, mul_mem (pow_mem h m) (q1 w), by simpa [smul_def, mul_pow, e] using congr($f ^ m • b)⟩
lemma Lift.Chart.IsChartOf.exists_isPeriodMatrix (h : IsCrystalline ρ) e (hab : ∀ k, jump ρ (ofId ..) k ≠ 0 → -a ≤ k ∧ k ≤ b) : ∃ M : GL ι Bcris, ∃ U v, (∀ g, (repMatrix ρ e g).map (algebraMap _ _) * M.1.map (toGp g • ·) = M.1) ∧ c.E * tau * v.1 = mu ∧ c.IsPeriodMatrix U (a + b) (v ^ a) ∧ U.map (algebraMap ..) = (c.E * tau) ^
  a • M.1 := let A m := mapMatrix (MulSemiringAction.toRingHom FrobGal Bcris m)
  let P := {N : _ˣ // ∀ g, (repMatrix ρ e g).map (↑) * A (1, toGp g) N = N.1}
  let F := (ofId ..).mapMatrix
  have I : Injective F := map_injective injective_BPlus_Bcris
  have X {B m} (h : ∀ n i l, _) : ∃ C, F C = (_ * tau) ^ m • B := ⟨_, ext fun i l ↦ invFun_eq (y2 _ m c.associated_E_mul_tau_mu.dvd' (h · i l))⟩
  (h.k1 le_top).rec fun _ ⟨u, hu⟩ ↦ by
  let M : P := ⟨@unitOfInvertible _ _ _ (invertibleToMatrix ..), fun g ↦ ext_col ((equivFun_tensorAction ..).symm.trans <| congrArg _ <| u.reindex_apply (u.indexEquiv (e.baseChange _)) · ▸ hu ..)⟩
  let N n : P := ⟨M.1.map (A (.ofAdd n, 1)).1, (.trans (by simp [A]) congr(A _ $(M.2 ·)))⟩
  choose Y hY W k h₄ h₅ _ using fun N :
    P ↦ by simpa [IsUnit, -hodgeMatrix] using (exists_hodge_frame Γ le_top
    (N.1.isUnit.map (mapMatrix _)) (.trans (by simp; rfl) congr($(N.2 ·).map (ofId ..))))
  have J n i := hab (k n i)
    (by rw [(hasJumps_of_rows e (.map _ (W n))⁻¹ _ (by exact .of_forall (inv_mul_apply_of_isHodgeTateFrame <| isHodgeTateFrame_of_hodgeMatrix <| h₅ n ·))).1]; simp)
  have T {B : Matrix ..} {k c P} (Q : GL ι BdRPlus) (h : ∀ i, _) (e : B * _ = hodgeMatrix P k) i l :
    B i l ∈ hodgeFil c := (Q.map (ofId ..).1).eq_mul_inv_iff_mul_eq.2 e ▸ sum_mem fun m _ ↦ hodgeFil_anti (h m) (by simp [mem_hodgeFil, ← map_inv, field, ← map_mul])
  choose R hX eX using fun M N : P ↦ (hc.v1 fun g ↦ congrFun₂ (by
    simpa [← map_mul, N.2] using! congr(M.1⁻¹ * $(M.2 g) * A (1, toGp g) (M.1⁻¹ * N.1)).symm) · ·)
  obtain ⟨eX, ⟨v, o⟩, ⟨w, _⟩, ⟨V, H⟩, Z, _⟩ := ((F (of _)).ext <| eX · ·), c.associated_E_mul_tau_mu, c.z9, X (T (.map _ (Y _).toGL) (J _
    · |>.1) <| h₄ <| N ·), X fun n ↦ T (W (N n)) (neg_le_neg <| J (N n) · |>.2) (((N n).1.map (ofId
    ..).mapMatrix.1.1).inv_mul_eq_iff_eq_mul.2 (by erw [← mul_assoc, h₄]; simp [zpow_ne_zero]))
  have G m : F (m • V) = (_ * m • tau) ^ a • A m _ := ext (by
    simpa [F, smul_def] using! congr(m • $H · ·))
  refine ⟨_, V, v, M.2, o, ⟨⟨Z, I (by simp [*]; module)⟩, ⟨Chart.ainfToBPlus (c.φ c.E) ^ a • of (R M (N 1)), w ^ a • of (R (N 1) M), by simp [*, mul_mem, pow_mem], I (by simp [↓smul_mul_smul, *, ← mul_pow]), I ((G _).trans
    (by simp [Units.smul_def, H, eX, N, ← o, «φ», -smul_of, FrobGal.smul_def]; module))⟩, fun g h ↦ (hc g h).choose_spec ▸ ((c.associated_smul_E _).symm.mul_mul y1).rec fun r h ↦ ⟨r.1 ^ a • (repMatrix ρ e _).map (↑), I (by erw [map_mul, G, H, map_smul (ofId Ainf _).mapMatrix, smul_mul_smul, ← mul_pow, mul_comm, h, M.2])⟩, fun f y ↦ ?_⟩, H⟩
  choose t ht using fun l ↦ hc.k8 _ (fun k ⟨_, g, rfl⟩ ↦
    congr($(((toGp g).toAlgHom.map_adjugate _).trans (congrArg _ (hY M g))) l k)) f y
  simp [smul_def, ← dvd_def, pi_dvd_iff, ← w2, (c.associated_E_xi.map _).pow_pow.dvd_iff_dvd_left]
  exact fun h i ↦ (Finset.dvd_sum fun _ _ ↦ (h _).mul_left _).trans (by
    obtain _ := congr((ofId _ BdR).mapMatrix $H), ((Y M).toGL.map _).eq_mul_inv_iff_mul_eq.2 (h₄ M)
    simp [F, ofId, map_mulVec, ↓← map_inv, ← coe_inj _ BdR] at *
    simp [*, ← mul_assoc]
    simp [↓← mulVec_mulVec, mulVec, diagonal]
    congr 2; ext j; grind [(algebraMap.coe_inj ..).1 (ht j)] :
    ((↑(W M) * diagonal t * (W M).2) *ᵥ (↑) ∘ (V *ᵥ y)) i = _).dvd
