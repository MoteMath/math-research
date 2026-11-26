import New.Selmer.DeterminantBound
import Lib.ClassField.LocalDuality.CrystallineDuality
import New.Lift.ExponentTheorems
import Lib.General.NumberTheory.Valuation
import Lib.GaloisRep.WeightCongruence.WeightCongruence
import New.Selmer.RibetFirstOrder
import New.Selmer.LabelledColumns
import Lib.Cyclotomic.OddSha.OddShaBound
import New.Patching.OnePrimeTie
import New.Selmer.BaseLevelOfLabel
import New.Filling.RowDimension
import New.Rows.RowVolume
section
open Fact Int ZMod IsCyclotomicExtension Parameters IsAlgClosed
variable {P} {D : Data P} {ℓ} [hp : Fact ℓ.Prime] {e : D.E →+* PadicAlgCl ℓ} {g g' g₁ : Gp ℓ}
private lemma w4 (H : ∀ ζ, ζ ^ D.cycloConductor = 1 → g ζ = ζ) x : g (e x) = e x := have := (@toCycloField P D.s).toAlgebra
  (surjective_domRestrict_of_isAlgebraic e.toRatAlgHom).elim fun ψ E ↦ congr($E x) ▸ congr($(((zeta_spec D.cycloConductor ℚ (cycloField D.cycloConductor)).powerBasis _).algHom_ext (f := .comp (g.restrictScalars ℚ) ψ) (by simp [H, ← map_pow, zeta_pow])) _)
lemma s23_n6 (σ : D.E →+* _) : σ (P.sqrtNegDInE D.s) = cmSign σ * QuadField.sqrtNegD P.d ∧ Φ (.mk σ) (P.ζ _) = σ (P.ζ _) ^ (cmSign σ).1 := by cases Φ_eq_or σ with exact ‹_› ▸ (by
       simp [cmSign, ← RCLike.star_def, ← map_star_complex])
variable [PadicIso ℓ] {a i n} (t : .mk (s23_z1 e g) ∈ D.thick) (t' : .mk (s23_z1 e g') ∈ D.thick) (h : (g' * g⁻¹) (e (P.ζ _) ^ ℓ ^ a) = (e (P.ζ D.s) ^ ℓ ^ a) ^ ℓ ^ n)
include h
variable (e g g' a n) in
private lemma ft_j2 {y} m d (c : (ℓ ^ a).Coprime m) (hy : .mk (s23_z1 e g') * y = .mk (s23_z1 e g) := by apply mul_div_cancel) : (@placeClass P _ m d y).1 =
  (cmSign (s23_z1 e g) * cmSign (s23_z1 e g') : ℤ) * ℓ ^ n := by
  have E := congr((g' (ιℓ $(hy ▸ phi_mul _ _ (ζ ..))) ^ (cmSign (s23_z1 e g')).1) ^ ℓ ^ a)
  simp [galOfPlace_zeta, s23_n6, s23_z1, ← zpow_natCast, ← zpow_mul] at *; rw [zpow_mul', h, ← zpow_mul, mul_rotate, ← div_eq_one_iff_eq, ← zpow_sub₀, ← sub_mul, (isPrimitiveRoot_zeta.map_of_injective e.injective).zpow_eq_one_iff_dvd] at E
  simpa [placeClass, unitsMap, mul_comm, ↓← mul_assoc, ← intCast_eq_intCast_iff_dvd_sub] using c.symm.cast.dvd_of_dvd_mul_right (d.natCast.trans E)
  repeat simp [isPrimitiveRoot_zeta.ne_zero, NeZero.ne, zpow_ne_zero]
include t t'
lemma s23_j7 (h₁ : (g' * g₁⁻¹) (e (P.ζ _) ^ ℓ ^ a) = (e (P.ζ _) ^ ℓ ^ a) ^ ℓ ^ i) (hk : ℓ ≤ D.k * D.t) (hi : 0 < i) (hn : i < n) (hL : n ≤ 27 * D.s) : .mk (s23_z1 e g₁) ∉ D.thick := fun u ↦ by
  have A {g n m} h d c := congr($(ft_j2 e g g' a n h m d c) ^ 2); simp [mul_pow, ← Int.cast_pow, isUnit_sq, -map_pow] at A; obtain rfl | o := hp.1.eq_two_or_odd'
  · grind [@orderOf_one_add_prime 3 out nofun _ ▸ orderOf_le_of_pow_eq_one hi (.trans (by norm_num
      [← mul_pow, sq]) ((A h₁ ⟨_, mul_left_comm ..⟩ (.pow _ _ rfl)).symm.trans (by simp [D.thick_eq_neg_one_mod, *]))), @Nat.lt_pow_succ_log_self 3 out D.s]
  exact (@two_pow_le_of_pow_eq_one ℓ hp.1.one_lt (i * 2) _ (by lia) (by rw [Int.cast_natCast, pow_mul, ← A h₁ two_pow_dvd_N₁, ← map_div, D.three_term (2 * i) (2 * n) _ _ _ _ t' _ u _ t] <;> first | lia | (simp [Units.ext_iff, pow_mul, A h, A h₁, o.pow]; try ring))).not_gt
    (by grw [natAbs_natCast, hk, hn, hL]; use D.nat_le_of_hasLogBound)
omit h
private lemma ft_r4 (c : ℓ ∣ D.cycloConductor) : cmSign (s23_z1 e g) = cmSign (s23_z1 e g') := units_ne_iff_eq_neg.not_right.2 fun _ ↦ if b : ℓ ∣ D.N₁ then by
    let x := e (P.c₀InE D.s); rcases congr(g (ιℓ ($((s23_n6 (s23_z1 e g)).1) + $((s23_n6 (s23_z1 e g')).1)))), P.dvd_norm_c₀ out b, congr(‖e $(P.c₀InE_mul_one_sub D.s)‖), IsUltrametricDist.norm_add_le_max x (1 - x), dist_smul (g * g'⁻¹) x 0; simp_all [sqrtNegDInE, map_ofNat, s23_z1, ← Padic.norm_natCast_lt_one_iff, ← PadicAlgCl.norm_extends]; grind [sq_nonneg (‖x‖ - 1), sq] else (exists_apply_eq_pow b (by simp [← map_pow, isPrimitiveRoot_zeta.1]) _).elim fun n ↦ mt (ft_j2 e g g' 0 n · _ ⟨_, rfl⟩ (by simp))
  (by simp_all [D.placeClass_of_thick, hp.1.dvd_mul, Nat.prime_dvd_prime_iff_eq, out]; grind
  [pow_d_ne_neg_one])
end
section
export Lift (InClass)
open Lift crysCocycles Module Set Multiset Finset DFunLike Submodule Finite TensorProduct
variable {ℓ} [ThePrime ℓ] {O : CoeffRing ℓ} {Γ n} [Group Γ] [Fintype n] [𝒥 : OverGp Γ ℓ] {R} [CommRing R] [Algebra ℤ_[ℓ] R] {L : GalLattice O Γ}
noncomputable abbrev s23_d1 (ρ : Γ →* Matrix n n R) : GalLattice R Γ := ⟨n → R, actionRep R _ ρ⟩
private lemma m7 [TopologicalSpace Γ] {E} [Field E] [UnramCMField E] {e : E →+* _} [PadicIso ℓ] (hj : IsCompletionGroup e 𝒥.toGp) (h : IsPotCrys L.ρ) {J : _ → _} (hJ : ∀ g, HasJumps L.ρ (t0 O g) (J (s23_z1 e g))) : finrank O (crysCocycles L.ρ) = finrank O L + ∑ σ with ∃ g, s23_z1 e g = σ, (J σ).countP (· < 0) := have := fg h
  Nat.mul_left_cancel (card_pos_iff.2 ⟨t0 O 1⟩) (by
    choose s _ using @s23_w8 _ _ O
    choose K _ hK using h.exists_hasJumps
    simpa [(finrank_eq h (J := univ.sum K) (by simp [h.sum_jump_eq_jump_overZp, count_sum', ← hK _ ·])).2, hj.p5, mul_add, finrank_mul_finrank, ← coe_countPAddMonoidHom, sum_set_coe, ← filter_mem_univ_eq_toFinset, (Multiset.ext' fun u ↦ hK .. ▸ hJ · u), fun g ↦ (by simp [Function.Injective, Subtype.ext_iff, ← apply_rangeSplitting, hj.w7] : ((⟨_, ·, rfl⟩) <| rangeSplitting (s23_z1 e) · * g).Injective).bijective_of_finite.sum_comp (J ·)] using congrArg (countP _)
      (congr(∑ y, $((by intro; simp_all [t0, ext_iff]; grind : (t0 O <| rangeSplitting (s23_z1 e) y * s ·).Injective).bijective_of_finite.sum_comp K)).symm.trans sum_comm))
private lemma d4 {k : ℕ} (hT : IsPotCrys L.ρ) {S} {y : NNReal} (hk : finrank O L * (2 * k) ≤ y) (h : ∀ c ∈ crysCocycles L.ρ, (ℓ : ↑O) ^ k • c ∈ S) : O.normLength (relLength (crysCocycles L.ρ) S) ≤ 𝒥.toGp.range.index * y := by obtain ⟨_, K, r, H⟩ := fg hT, hT.exists_hasJumps (ρ := overZp _) _; grw [relLength, length_le_of_surjective _ (factor_surjective ((span_smul_eq {(ℓ : ↑O) ^ k} ⊤).trans_le ?_)), ← (quotTensorEquivQuotSMul ..).length_eq, (equivFinsuppOfBasisRight (Module.finBasis (↑O) (crysCocycles L.ρ))).length_eq, ← hk] <;> simp_all [set_smul_le_iff, submoduleOf]; exact_mod_cast le_of_mul_le_mul_left (by grw [← mul_assoc, finrank_mul_finrank, (finrank_eq hT H).2, countP_le_card, r, ← one_add_mul, Nat.one_le_of_lt (toGp.range.quotient_finite_of_isOpen 𝒥.2.1).card_pos, ← finrank_mul_finrank _ O]; linarith!) (finrank_pos : _ < finrank ℤ_[ℓ] O)
end
section
open Lift Nat Module Finset Real
private lemma ft_n4 {ℓ} [hp : ThePrime ℓ] [Γ : GroupOverGp ℓ] [TopologicalSpace Γ] {O : CoeffRing ℓ} {L : GalLattice O Γ} (Q m h μ : ℕ) {G b δ η W} {th ε : _ → _} {U U'} (Q₀ : 0 < Q) (hQ : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h) (hG : 99 * h ^ 3 ≤ G) (hb : 99 * (G * h ^ 3 + G) ≤ b) (hm : 2 * (4 * b : ℝ).log < m) (hδ : δ < η) (hη : 99 * ((η + W) * Q + η + h) ≤ h ^ 3) (hU : ∀ g, IsInJumpWindow η (-ε g) (ite (th g) b G + δ) W (U g)) (hU' : ∀ g, IsInJumpWindow η (ε g) (ite (th g) b G + δ) W (U' g)) (hL : InClass ⊤ ⊥ U' L) (c : (∀ g, (∀ u < 0, u ∈ U g ∨ u ∈ U' g → 2 * u ≤ -h) ∧ ∑ u ∈ Icc (-↑η) ↑η, jump L.ρ g u ≤ μ) ∨ ∀ g, U' g ⊆ Icc (-η) 0) {y : NNReal} (hy : (10 ^ 5 * (finrank O L * (2 * lambdaLoss h b ℓ / Q * m) + μ * lambdaLoss h b ℓ) : ℕ) ≤ y) (k : KummerChart Γ) (ζ : k.LetterRoot O) (T s : _ → _) (hj : Topology.IsOpenEmbedding Γ.overGp.toGp) (hf : k.e * k.f = Γ.overGp.toGp.range.index) (he : k.e ≤ h) (hs : ∀ g, th g ∨ Q < ℓ → th g = T (g ζ) ∧ ε g = s (g ζ)) (hu : k.IsUnramified ∧ 7 ≤ ℓ ∨ ℓ ≤ Q ∧ ∀ z z', s z = s z') (hT : ℓ ≤ Q → ∀ᵉ (z) (a ∈ Icc 1 (ℓ.log (h ^ 3))) (b ∈ Icc 1 (ℓ.log (h ^ 3))), T z → T (z ^ ℓ ^ a) → ¬T (z ^ ℓ ^ (a + b))) : O.normLength (relLength (crysCocycles L.ρ) (cupOrthogonal (InClass ⊤ ⊥ U) L)) ≤ Γ.overGp.toGp.range.index * y := by
  have M {H} (h : H ≤ 4 * b := by omega) : ℓ.log H < m := by grw [← @cast_lt ℝ, ← hm, h, natLog_le_logb, logb, ← hp.out.two_le, ← one_sub_inv_le_log_of_pos] <;> norm_num; linarith
  have N {n} := (lambdaLoss.eq_1 h b ℓ ▸ padicValNat_dvd_iff_le (n := n) (by simp [prod_eq_zero_iff])).1; have A := (2 * lambdaLoss h b ℓ).lt_div_mul_add Q₀; generalize lambdaLoss .. = v, _ / Q = K at *; have Λ : 2 * b < ℓ * (v + 1) := (lt_mul_div_succ _ hp.out.pos).trans_le (by grw [← N (.mul_right pow_padicValNat_dvd _), ← padicValNat_mul_div_factorial, padicValNat_factorial_mul]; lia)
  have hv i : let z := ↑(theta (k.letterTeich i)); let w := (IsInJumpWindow (ite (ℓ ≤ Q) (2 * G) η) · (ite (T z) (b + δ) (G + δ)) W); w (-s z) (k.letterJumps ζ U i) ∧ w (s z) (k.letterJumps ζ U' i) := by clear * - hs hU hU' hδ hη hG hQ; simp [← ite_add, KummerChart.letterJumps, IsInJumpWindow, -cast_ite] at *; generalize theta _ = z; grind
  have ex {x} (e : x ≤ m) := d4 hL.isPotCrys (k := 10 ^ 4 * (K * x))
    (hy.trans' (mod_cast by grw [e]; ring; omega)) ∘ forall₂_imp
    (k.mem_cupOrthogonal_of_scaledCupBounds ζ hj le_top le_rfl hL (U := U) _ ⟨·, ·⟩)
  split_ifs at hv with hl <;> simp [hl] at hu
  · have D : 2 * (b + δ) < h ^ 2 * K := by
      nlinarith only [A, Λ, hl, hQ, h.le_mul_self, (by omega : h + δ ≤ b)]
    have := (lt_pow_succ_log_self hp.out.one_lt (h ^ 3)).le
    refine ex M fun _ _ _ _ P _ ↦ P.scaledCupBounds_sparse_thick (by omega : _ ≤ 9 * G) hv (by
      grw [← this, D, he]; linarith) (this.trans' (by omega)) (by omega) rfl
      (by clear * - hu; tauto) (by omega) (by grw [pow_log_le_self]; linarith; omega) (by
      simpa [(k.letterFrob.coe_pow · |>.trans (pow_iterate ..))] using hT hl <| theta <| k.letterTeich ·) ?_ ..
    grw [KummerChart.differentExp, ite_le_sup, padicValNat_le_nat_log, M, M, M, (by omega : _ + m ≤ h)]; nlinarith only [D, hb]
  by_cases Z : h ^ 3 ≤ v
  · refine ex M fun _ _ _ _ P _ ↦ P.scaledCupBounds_two_sizes le_rfl hv ?_ rfl hu.1 hu.2 ?_ ?_ (by
      and_intros <;> nlinarith only [Λ, hl, hb, hη, hδ, Z, A, (by omega : Q ≤ h ^ 3)]) .. <;> omega
  obtain ⟨F, B⟩ := k.few_low_jumps ζ hj hu.1 (by omega) (a := 2 * (v + 1)) (by
    intro; grw [ite_le_sup, mul_left_comm, tsub_mul]; omega) (by omega) (by
    intro; split <;> omega) (fun _ y A d ↦ by_contra fun o ↦ Z (N (by
    obtain _ := Int.natAbs_le_of_dvd_ne_zero d o, (by nlinarith only [Λ, Z, hb] : 9 * G ≤ ℓ); grw [← dvd_prod_of_mem (a := y.natAbs), ← Int.natCast_dvd.1 d] <;> simp at A ⊢; omega))) hL hv
  exact if n : h / 5 ≤ v ∧ _ then by
    grw [B μ n.2, O.normLength_natCast_mul, ← hy, ← hf, (by omega : _ + 1 ≤ 6 * v), ← (M bot_le).succ_le, @Nat.le_of_mul_le_mul_right (W + 1) K _ (by omega) Q₀]; simp [hu.1.2]; norm_cast; ring; omega
  else by simp [relLength_eq_zero.2 (F (by clear * - n c; grind))]
end
section
open Lift CoeffRing Module Nat Classical NeZero NumberField Finset
open Data hiding loss
private lemma ft_j1 {P ℓ Γ} {D : Data P} [hp : ThePrime ℓ] [PadicIso ℓ] [Group Γ] [𝒥 : OverGp Γ ℓ] [TopologicalSpace Γ] {e r t J} (hJ : IsRowType D r t J) (hj : IsCompletionGroup e 𝒥.toGp) : ∀ᶠ O : CoeffRing ℓ in .atTop, ∀ {L : _ → GalLattice O Γ} {F K U}, (∃ n, ℓ = D.g n ∧ ∀ s, IsWeilPair (toGp s) 0 → Lift.IsTameType ℓ D.r ((D.r + D.t) * D.r) (K s)) ∨ F = ⊤ ∧ K = ⊥ → (∀ g, ∀ a ∈ U g, ∃ i, jump (L i).ρ g a ≠ 0) → (∀ i g, HasJumps (L i).ρ (t0 O g) (i.elim (J (s23_z1 e g)) fun c : Fin t ↦ {↑c})) → finrank O (L none) = r → ∀ c, let x := ite (c = none) 1 D.t; InClass F K U (L c) → O.normLength (relLength (crysCocycles (L c).tateDual.ρ) (cupOrthogonal (InClass F K U) _)) ≤ 𝒥.toGp.range.index * ↑(finrank O (L c) * (loss D ℓ / x)) := by
  obtain ⟨⟨k, -, he, un, y, A, hy⟩, N, ⟨i, a, m⟩⟩ := exists_kummer_chart Γ, D.nat_le_of_hasLogBound (B := D.k * D.t).trans' ∘ le_of_dvd one_le ∘ hp.out.dvd_of_dvd_pow ∘ (dvd_trans · P.N₁_mul_d_dvd_M_omega), hJ.low_or_high, D.t_odd.pos, D.k_pos, hJ.t_le, (D.nat_le_of_hasLogBound : 3 * D.t ≤ D.h₂), D.h₂.le_mul_self
  filter_upwards [eventually_primitiveRoot (ℓ ^ k.f.val - 1)] with O ⟨ζ, z⟩ L F K U Y B T rfl c x H
  choose r R using @s23_w8 _ _ O; replace T i g a := R g ▸ T i _ a; simp [T, Option.exists, Fin.exists_iff] at B
  have W g : let σ := s23_z1 e (r g)
    let v := (IsInJumpWindow (D.h₂ ^ 2 + 1) · (ite (id (.mk σ ∈ D.thick)) D.b₁ D.b₂ + (i * D.h + D.h₂ - 2 * D.t)) (4 * D.t)); v (-cmSign σ) (U g) ∧ v (cmSign σ) ((U g).image (-· - 1)) := by
    intro σ; simpa [IsInJumpWindow, ← forall_and] using fun u h ↦ by obtain ⟨h, ⟨⟩⟩ := (B g u h).imp_left (m σ u), Int.units_eq_one_or (cmSign σ) <;> simp [*, w, abs_le] at h ⊢ <;> lia
  obtain ⟨hD, ⟨X⟩, ⟨n, ⟨⟩, Y⟩ | ⟨⟨⟩, ⟨⟩⟩⟩ := H.dual, (by lia : x ≤ D.t ∧ 0 < x), Y
  · have G g := (hj.2 g).2 (w4 fun z hz ↦ (exists_apply_eq_pow (P.not_dvd_N₁_mul_d_of_modEq_one (D.g_modEq_one _)) hz g).elim (by simp [pow_eq_pow_of_modEq ((D.g_modEq_one _).pow _) hz]))
    refine d4 hD.isPotCrys ?_ (tame_types_exponent (Γ := ⟨Γ⟩) hj.1 G hD Y (hj.w7.2 (G (_ / 1)) ▸ W ·) (by grw [sub_le, a]; split <;> use D.nat_lt_of_hasLogBound)); grw [finrank_linearMap_self, loss, ← one_le_padicValNat_of_dvd out, ← le_self_add, X]; gcongr; rify; use D.le_of_hasLogBound; clear * -; revert n; simp [gProd]
  let F := (t0 O · ζ); have C {g g' k} (this : F g' = F g ^ k) := cycCharMod_eq_iff.1 (cycCharMod_eq_of_isPrimitiveRoot (g := g' * g⁻¹) (.map_of_injective (.coe_submonoidClass_iff.2 z) g.injective) (by simpa [t0, F, ← map_pow])); let w z g := ite (ℓ ∣ D.cycloConductor) (.mk (s23_z1 e g) ∈ D.thick) (F g = z); have u h := un fun _ ↦ (hj.2 _).2 ∘ w4 ∘ apply_eq_self_of_mem_inertiaGroup h; have σ h g g' (H : F g = F g' ^ 1) := hj.w7.2 (k.chart_isChartOf _ ⟨(fixes_roots_iff_fixesLambda (g * g'⁻¹)).1 (by simpa using C H), sub_eq_iff_eq_add.2 (u h).1 ▸ by simp [k.theta_E]⟩)
  refine ft_n4 (Γ := ⟨Γ⟩) _ D.m D.h₂ (finrank O (L c) * D.m / (D.k * x))
    D.nat_le_of_hasLogBound D.nat_le_of_hasLogBound D.nat_le_of_hasLogBound
    D.nat_le_of_hasLogBound D.lt_of_hasLogBound (by grw [sub_le, a]; use D.nat_lt_of_hasLogBound)
    D.nat_le_of_hasLogBound (W · |>.1) (fun g _ h ↦ (W g).2 _ (filter_subset (jump (L c).tateDual.ρ g · ≠ 0) _ h)) (hD.imp_right (by simp +contextual)) ?_ (by
    simp [loss, finrank_linearMap]; grw [cast_div_le, cast_div_le, ← X]; field; norm_cast; clear * -; lia) k ⟨ζ, by erw [card_units, card_flatFq, z.1]⟩ (∃ g, .mk (s23_z1 e g) ∈ D.thick ∧ F g = ·) (cmSign ∘ s23_z1 e ∘ epsilon ∘ w) hj.1 he (by
    grw [Nat.le_mul_of_pos_right k.e k.f.pos, he, hj.p5, Finite.card_subtype_le]; simpa [Embeddings.card, finrank_eq_two_mul_card_infinitePlace] using D.nat_le_of_hasLogBound)
    (fun g H ↦ by clear * - R σ H N C; grind [ft_r4, @epsilon_spec _ (w (g ζ)) (by
    grind)]) (if h : _ then .inr ⟨N h, by simp [w, h]⟩ else .inl ⟨u h, le_of_not_ge (h ∘ (dvd_trans
    · (.trans (by cbv) ((P.3.mul_right _).mul_right _))) ∘ hp.out.dvd_primorial_iff.2)⟩) (by
    rintro h _ a p b q ⟨_, c, ⟨⟩⟩ ⟨_, _, E⟩ ⟨_, v, B⟩; rcases (pow_sub_one_mul out _).trans (apply_eq_pow_of_isFrob hy (not_dvd_ordCompl hp.out out) ((P.isPrimitiveRoot_zeta.pow_of_dvd out (ordProj_dvd ..)).map_of_injective e.injective).1).symm, log_mono .refl hp.out.one_lt (D.nat_le_of_hasLogBound : D.h₂ ^ 3 ≤ (2 ^ D.s) ^ 12) with X
    simp [(hj.2 _).1 A, P.isPrimitiveRoot_zeta.ne_zero out, ← pow_mul 2] at *; apply s23_j7 c v (C B _ X) (C (by rwa [E, ← pow_mul, ← pow_add]) _ X)
      h <;> omega)
  cases c <;> [left; right] <;> simp [jump_tateDual H.isPotCrys, x, Nat.le_div_iff_mul_le, *] <;> clear W T H hD C
  exact fun g ↦ ⟨by grind [Int.units_natAbs], (hJ.card_low_le _).trans' (by
    gcongr; induction J _ using Multiset.induction <;> simp [Multiset.count_cons, Multiset.countP_cons, sub_eq_iff_eq_add, neg_eq_iff_eq_neg]; lia)⟩
  grind
end
section
open Submodule commutatorElement AddMonoidHom Matrix.Module QuotientAddGroup
lemma f2 {O G n} [CommRing O] [Group G] [Fintype n] {I : Ideal O} [Finite (O ⧸ I)] {ρ : G →* Matrix n n O} (hρ : span O (.range ρ) = ⊤) (χ : G →* O) {c : G →* G} (H U : Subgroup G) [hN : H.Normal] γ {g₀ z} {s : O} {y : G → n → O ⧸ I} {W} (x : W → G → _ →+ QZ) (hi : ∀ w v, (∀ g ∈ U, x w g = x v g) → w = v) (hU : ∀ g ∈ U, ∀ m : n → O ⧸ I, ρ g • m = m) (hH : ∀ g ∈ H, c g ∈ H ∧ g ∈ U) (κ : ∀ g : G, ⁅g, γ⁆ ∈ H) (p : IsUnit (s - 1)) (s₂ : IsUnit (s + 1)) (hγ : ρ (c γ)⁻¹ = s • 1 ∧ ρ γ = s • 1 ∧ χ (c γ) = 1 ∧ χ γ = 1 ∧ y γ = 0) (hz : z ∈ U ∧ c z ∈ U) (hy : ∀ g h, y (g * h) = y g + ρ g • y h) {i} (hu : IsUnit (y g₀ i)) (hW : ∀ᵉ (w) (g) (a ∈ U) (b ∈ U) (m), x w (a * (g * b * g⁻¹)) m = x w a m + x w b (χ g • ρ g⁻¹ • m)) (hq : ∀ᵉ (w) (h ∈ H) (t : O), x w (z * h) (t • y (z * h)) = x w (c (z * h)) (t • y (c (z * h)))) {g α α'} (hδ : ρ g = α • 1 ∧ ρ (c g)⁻¹ = α' • 1) : Nat.card W ≤ .card (torsionBy O (n → O ⧸ I) (α - χ (c g) * α')) := have cj g a := eq_sub_of_add_eq (hy (a * g⁻¹) g).symm
  have J k (h : ρ k⁻¹ = s • 1) := by simpa [*, ↓map_mul] using hU (k⁻¹ * k)
  have ⟨τ, hτ, u⟩ : ∃ τ ∈ H, IsUnit (y τ i) := ⟨_, κ g₀, by simpa [map_mul_eq_one, cj, *, commutatorElement_def, sub_smul] using (hu.smul (-p.unit))⟩
  have C w {b} v : ∀ t k, x w b (t • ρ k • y τ) = x w (c τ) (χ (c k) • t • ρ (c k)⁻¹ • y (c b))
    := (p.mul s₂).unit.mulRight.forall_congr_right.1 fun r k ↦ by
    have F {b} v t := congr($(hq w b v (r * s * t)) - $(hq w _ (mul_mem v (hN.1 _ hτ k)) (r * s * t)))
    linear_combination (norm := simp (maxDischargeDepth := 6) [cj, hW, ↓hU, hy, hz, v, hH, hγ, J, hτ, mul_mem, hN.1, by simpa using hW w 1, mul_smul, sub_eq_add_neg, add_smul, ↓smul_comm (ρ _), ↓smul_add])
      F (mul_mem v (hN.1 b v γ)) 1 - F v (s + 1) + F H.one_mem s
    abel
  have V {f} h := functions_ext _ f 0 fun j m ↦ by
    simpa [Algebra.smul_def, mul_assoc] using closure_induction (p := fun A _ ↦ f (A • y τ) = 0)
      (by simp) (by grind [add_smul]) h (eq_top_iff'.1 hρ (.single j i (m * u.unit⁻¹).out))
  (Nat.card_le_card_of_injective (fun w ↦ lift _ (x w (c τ)) ((range_le_ker_iff (DistribSMul.toAddMonoidHom _ _) _).2 (V (by simpa [smul_smul, ↓sub_smul, *, mul_comm α, mul_comm α', mul_assoc] using (C w (hH _ hτ).1 · <| · * g))))) fun w v e ↦ hi w v fun g o ↦ ext (p.smul_bijective.2.forall.2 fun m ↦ have Z w := sub_eq_of_eq_add (hW w γ ⁅g, γ⁆ (by simp [*]) g o (ρ γ • m)); by simpa [commutatorElement_def, *, mul_assoc, sub_smul, sub_mul, mul_sub, sub_eq_zero, ↓smul_smul] using ((Z w).congr (Z v)).2 congr($(sub_eq_zero.1 (V (by simp [*, by simpa [DFunLike.ext_iff, forall_mk] using e]))) _))).trans_eq ((card_hom_QZ _).trans AddSubgroup.index_range)
open IsDiscreteValuationRing Matrix Module Ideal MvPolynomial NeZero Finsupp
attribute [local simp] MulAction.compHom_smul_def mapRel linearCombination_apply twistAtPoint Module.smul_def sum_mapRange_index mem_obeying _root_.funext_iff mem_selmerModule_iff Algebra.smul_def algebraMap_eq_diagonal
private lemma m9 {ℓ M q E n σ O₀ O} [NeZero ℓ] [Field E] [EmbeddedNumberField E] [Fintype n] [Fintype σ] [CommRing O₀] [CommRing O] [DVR O] [CharZero O] {ρ : Gal(Ω/E) →* Matrix n n O₀} e₀ (S : Finset (FinPlace E)) {h} (hh : ∀ j : σ, IsLocallyConstant (h j)) (hρ : IsLocallyConstant (s23_z5 ℓ M ρ)) L y₀ : ∃ F, addVal O (MvPolynomial.eval y₀ F) ≤ length O (selmerModule (twistAtPoint (q := q) h y₀ e₀ ρ) S (mapRel e₀ '' L) (QuotSpan (ℓ ^ M : O))) ∧ ∀ O' [CommRing O'] [DVR O'] e y, length O' (selmerModule (twistAtPoint h y (e.comp e₀) ρ) S (mapRel (e.comp e₀) '' L) (QuotSpan (ℓ ^ M : O'))) ≤ addVal O' (eval₂Hom e y F) := by
  choose ι _ γ R r H using s23_k3 (ℓ ^ M) (twistAtPoint h X (C.comp e₀) ρ) ((hρ.eventually_eq 1).and (.all (hh · |>.eventually_eq 1))) S.finite_toSet (mapRel (C.comp e₀) '' L); choose A W hu hW k using exists_matrix_addVal_det_le_length (.map ((aeval y₀).toLinearMap.compLeft _) (R.restrictScalars O)) (ne (ℓ.cast ^ M)) (⟨_, r <| C ∘ ·, by simp⟩); choose u hu hu' using hu
  have K {O'} [CommRing O'] (e : O →+* O') y := @H (O' ⧸ _) _ (.compHom _ (eval₂Hom e y)) nsmul_quot_eq_zero
   fun g ⟨a, b⟩ ↦ by simpa [b] using! congr((($a).map (quotientMap _ (e.comp e₀) (by simp))).mulVec)
  use det u, ?_, fun O _ _ e y ↦ ?_ <;> erw [RingHom.map_det]
  exact (funext hu' ▸ k).trans (length_le_of_le_map ⟨⟨(↿· ∘ γ), by tauto⟩, by tauto⟩ _ fun w h ↦ by
    simpa using (K ..).2.2 ((hW _).1 ⟨·, ·, rfl⟩ w h))
  grw [← length_ker_le_addVal_det, ← relLength_bot, relLength_le_of_inj ⟨⟨(↿· ∘ γ), by tauto⟩, by tauto⟩, relLength_bot]; simpa using! (@(K e y).1 · · _ <| hu ·); simpa using! (@(K e y).2.1 · · 0)
private lemma ft_m0 {ℓ O k N} [p : ThePrime ℓ] [CommRing O] t {u : O} (h : u ^ ℓ ^ k = 1) M (a : k + M ≤ N) : ↑ℓ ∣ (1 + t * (u - 1) - 1) ^ ℓ ^ k ∧ (ℓ : O) ^ M ∣ (1 + t * (u - 1)) ^ ℓ ^ N - 1 := by have H a := congr((ℓ : O) ∣ $(add_pow_prime_pow_eq' p.out 1 a k) - 1); simp [add_assoc, dvd_add_left] at H; refine ⟨?t, by simpa [← pow_mul, ← pow_add, a.trans'] using (pow_dvd_pow _ (by lia)).trans (dvd_sub_pow_of_dvd_sub ((H _).2 ?t) (N - k))⟩; simp [mul_pow, Dvd.dvd.mul_left, ← H, h]
end
section
section
open Matrix.Module Module Nat Ideal Matrix MonoidHom Set Subgroup commutatorElement
variable {E n O B} [Field E] [UnramCMField E] [Fintype n] [CommRing O] [CommRing B] [Algebra O B] [TopologicalSpace B] [DiscreteTopology B] {ρ : Gal(Ω/E) →* Matrix n n O} {S L}
private noncomputable def ft_v2 (g : Gal(Ω/E)) := (LinearEquiv.curry O B _ n).symm.1 ∘ₗ .funLeft O _ (idOrConjInv · g)
private lemma ft_q5 {x A P Q K c} (h : x ∈ selmerModule ρ S L B) (l : K ⊆ L) (k : S ⊆ P ∪ Q := by simp [unionWithConj])
  : x ∈ selmerZ1 ⟨actionRep O _ ρ, c⟩ P A (fun _ ↦ localCocycles ρ K _ B) Q := ⟨(mem_selmerModule_iff.1 (selmerModule_mono h .rfl (by grind))).imp (⟨h.2.continuous, ·⟩) (·.1), fun _ _ ↦ ⟨x, selmerModule_mono h l, rfl⟩, (nomatch ·, ·.false_of_isTotallyComplex)⟩
variable {ℓ} {E : _} {ι} {O : _} [ThePrime ℓ] [Field E] [UnramCMField E] [CommRing O] {V W S₀ M N P₀ J} {x : _ → AuxPrimeData E _ × (ι → O)} (hp : IsPencil ℓ S₀ V W N P₀ J x) {n : Type} [Fintype n] {ρ : Gal(Ω/E) →* Matrix n n O}
include hp
omit [ThePrime ℓ] in
lemma IsPencil.r2 {v} (hv : v ∈ J) w (hw : w ∈ J) : (x w).1.h (x v).1.γ = ite (w = v) (.ofAdd 1) 1 := by grind [IsPencil, IsAnticyclotomicAt, (hp.3 w hw).eq_one_of_mem_inertiaAbove, inertiaAbove]
lemma IsPencil.v8 {R} [CommRing R] {y : J → R} hy (v : J) b : let χ := pointChar (x ·.1 |>.1.h) y hy
  χ (idOrConjInv b (x v).1.γ) = y v ∧ (v ≠ P₀ → χ (idOrConjInv b (x v).1.φ) = y ⟨_, hp.2⟩) := by
  simp_all [(hp.3 ..).apply_idOrConjInv, hp.r2, hp.4, Subtype.coe_eq_iff, hp.2, apply_ite, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod]
attribute [local simp] Finsupp.mapRange_sub' Units.smul_def funext_iff mapRel sub_smul twistRep in
lemma IsPencil.j8 i (hu : ∀ g ∈ inertiaAbove S₀ᶜ, s23_z5 ℓ M ρ g = 1) k (hk : k + M + M ≤ N) (hU : ∀ g, V i g → s23_z5 ℓ M ρ g = 1) O' [CommRing O'] [DVR O'] (e : O →+* O') {u} (h : u ^ ℓ ^ k = 1) I (w : _ → _) (hI : I ⊆ J) (h₀ : P₀ ∈ I → u = 1) (hF : ∀ p : I × _, s23_z5 ℓ M ρ (idOrConjInv p.2 (x p.1).1.φ) = s23_z5 ℓ M ρ (w p)) {S L} : let y (j : J) := 1 + ite (j = P₀) 1 (e ((x j).2 i)) * (u - 1)
  let r := twistAtPoint (x ·.1 |>.1.h) y e ρ
  let B := QuotSpan (ℓ ^ M : O')
  length O' (selmerModule r S (mapRel e '' L) B) ≤ length O' (selmerModule r S (mapRel e '' (L ∪ s23_v1 I x i)) B) + ∑ p, IsDiscreteValuationRing.addVal _ (u • (ρ (w p)).map e - 1).det := by
  intro y r B
  rw [image_union, selmerModule.eq_1 _ _ (_ ∪ _), ← union_assoc, obeying, iInf_union, inf_right_comm, add_comm, iInf_image, s23_v1, iInf_range, ← relLength_add_length_inf]
  apply add_le_add_left ((relLength_iInf_le ..).trans _)
  gcongr with ⟨⟨v, o⟩, b⟩
  grw [relLength_ker, ← length_ker_le_addVal_det, length_mono]
  intro d ⟨c, H, l⟩
  have hy {N} a j : (y j : B) ^ ℓ ^ N = 1 := mk_span_eq_iff_dvd_sub.2 (ft_m0 _ h M a).2
  let R := twistRep (quotientMap _ e (by simp)) (pointChar (x ·.1 |>.1.h) _ (hy (by lia)))
    (s23_z5 ℓ M ρ)
  lift v to J using hI o
  obtain ⟨⟨_, q, p⟩⟩ := hp.3 _ v.2, hp.1 _ v.2, @Algebra.smul_def O' B
  have hc g h : c (g * h) =
    c g + R g • c h := by simp +zetaDelta [mem_selmerModule_iff.1 H, twistAtPoint, s23_z5, *]
  have C {w A} hA hw (l : w ∉ placesDividing E ℓ) := let := (hu · ⟨w, hw, A, hA, ·⟩)
    (tame_affineAction nsmul_quot_eq_zero hA hc (by simp_all [← Finset.prod_pow, smul_pow, map_pow, R, pow_right_comm]) ((J.eventually_all.2 (hp.3 · · |>.isLocallyConstant.eventually_eq 1)).mp (by simp_all [R])) ⟨·, ·⟩ (by simp [hA.valuation_natCast_eq_one_iff.2 l]) H.2 |>.2 (q.of_dvd (pow_add ℓ .. ▸ pow_dvd_pow ℓ hk)))
  have C := congr($(show Commute (affineAction hc (idOrConjInv b (x v).1.φ)) (affineAction hc (idOrConjInv b (x v).1.γ)) by
    cases b <;> simp [idOrConjInv, C p.conjPlace_star, IsFrob.conjPlace_conjGal, C p, *]) 0)
  obtain rfl | _ := eq_or_ne ↑v P₀ <;> simpa [R, y, hp.v8, hF ⟨⟨v, o⟩, b⟩, *] using! show R (idOrConjInv b (x v).1.φ) • d =
    d by by_cases (x v).2 i = 0 <;> simp [R, y, ← l, map_smul', hp.6, affineAction, hp.v8, s23_z6 p, *] at C ⊢ <;> exact (by linear_combination C ·)
lemma IsPencil.g8 [PadicIntegerRing O ℓ] {i S L γ β} (r : IsBalanced ℓ S ρ L γ β M) (hV : V i = (s23_z5 ℓ M ρ · = 1)) (hS : S ⊆ S₀) {a : O} [NeZero a] (ha : a ∣ ℓ ^ M) : let X T := (selmerModule ρ (unionWithConj S T) (L ∪ s23_v1 J x i ∪ {.single γ 1}) (QuotSpan a)); (∃ y ∈ X J, ∃ g e, IsUnit (y g e)) → (∀ P ∉ J, ∀ l, (∀ t, IsPencil ℓ S₀ V W N P₀ (insert P J) (Function.update x P (l, Pi.single i t))) → X J ≤ ((X (insert P J)).map (ft_v2 l.γ)).comap (ft_v2 l.φ)) → length O (X J) ≤ β := fun ⟨y, hy, g, k, hu⟩ Z ↦ by
  obtain ⟨⟨r₁, r₂, r₄, ⟨⟨v, ⟨hv, hw⟩, B, hB, e⟩, s, hs, hs', s₁⟩, _, r₇, _, α, _, hα, h⟩, Y, m, _, p₁, p₂, p₃, _, _, p₆⟩ := r, (mem_selmerModule_iff.1 hy).1, (mt <| @hS ·), (hV.le _ <| hp.6 · · i · ·), id hp; obtain ⟨hm, ⟨⟩, c, _, -, -, p, -, b₀, q, _⟩ := fun b : n → _ ↦ funext (nsmul_quot_eq_zero (ha.trans (pow_dvd_pow _ M.le_succ)) <| b ·), PSigma.mk _ (discreteTopology_bot (QuotSpan a)), cycChar_eq_one_of_mem_inertiaAbove ⟨v, by tauto⟩, p₁ _ p₂, p₃ _ p₂; let := IsTorsionBy.module (smul_quot_eq_zero_of_dvd ha); have G (b : n → QuotSpan a) : IsLocallyConstant (ρ · • b) := r₁.comp (· • b); let X := DiscreteModule.of (actionRep O _ ρ) (continuous_prod_of_discrete_right.2 (G · |>.continuous)); let U := (s23_z5 ℓ M ρ).ker ⊓ (cycCharMod Ω (ℓ ^ M.succ)).ker; let H := ⁅normalClosure (range (idOrConjInv · γ)), ⊤⁆ ⊓ U; have k b g : ⁅idOrConjInv .., g⁆ ∈ H := ⟨commutator_mem_commutator (subset_normalClosure ⟨b, rfl⟩) ⟨⟩, U.inv_mem_iff.1 (by cases b <;> constructor <;> erw [commutatorElement_inv, div_mem_ker_iff] <;> simp [idOrConjInv, mul_inv_cancel_comm, s23_z5, *, map_mul_eq_one])⟩; have u : (x P₀).1.γ ∈ U ⊓ U.comap conjGal := by simp [U, s23_z5, cycCharMod_prime_pow_eq, cycChar_eq_one_of_mem_inertiaAbove ⟨_, b₀, _, p, q⟩, (r₂ _ ⟨_, ·, _, p, q⟩), (r₂ _ ⟨_, ·, _, p.conjPlace_star, q.conjPlace_conjGal⟩), *]
  have v' g (h : s23_z5 ℓ M ρ g = 1) (m : X) : ρ g • m = m := congr($h • m).trans (by simp); have D (b : X) : (ρ · • b - b) ∈ selmerModule ρ S (L ∪ s23_v1 J x i) _ := mem_selmerModule_iff.2 ⟨by simp [mul_smul, smul_sub], by simp_all, (iInf_union.ge : _ ≤ obeying ..) ⟨r₇ a b, mem_obeying.2 fun | _, ⟨⟨⟨w, v⟩, s⟩, rfl⟩ => by by_cases (x w).2 i = 0 <;> simp [*, r₂ _ (s23_z6 (p₃ _ v).3 (p₃ _ v).6.1 (by simp [*, p₁ _]) s)]⟩, (G b).sub (.const b)⟩; choose A hA using fun v : FinPlace E ↦ @ENat.exists_eq_iInf {A // IsPlaceOver A v} ⟨_, v.isPlaceOver_placeOver⟩ (length O <| localCocycles ρ (L ∪ s23_v1 J x i) · (QuotSpan a)); let := ZMod.algebra' X _ (ringChar.dvd ((nsmul_one _).symm.trans (hm 1))); have o : U.IsOpen := .inter (r₁ {1}) isOpen_ker_cycCharMod.1; choose _ _ _ _ _ σ _ π T' _ _ lc h₁ d R using selmerZ1.exists_split_primes_relations (M := X) (S := unionWithConj S J) (fun g h ↦ by ext; simp [X, r₂ g (h.imp (by grind))]) (A · |>.2) (fun _ ↦ localCocycles ..) (fun v k _ ⟨b, e⟩ ↦ ⟨_, selmerModule_mono (D b) .rfl, e⟩) (·.false_of_isTotallyComplex.elim) QZ (.mk ⟨U, o⟩) (v' · ·.1) (fun _ ↦ (·.2)) (·.false_of_isTotallyComplex.elim); specialize h₁ (σ.hasFewCocycles_of_central nofun ⟨Pi.finite, hm, (v' · ·.1), fun _ _ ↦ s₁.smul_left_cancel.1 ∘ by simp [X, *, sub_smul]⟩ c (k true · |>.2) d)
  grw [f2 r₄ (.comp (Units.coeHom _) (cycCharIn O Ω ℓ)) (c := conjGal) (H ⊓ H.comap conjGal) U γ (·.1 <| π ·) (fun w v h ↦ by ext i : 2; simpa [R _ w.2, R _ v.2] using h _ (σ.isFrob i).2) (v' · ·.1) (by simp +contextual [H]) (fun g ↦ by simpa [idOrConjInv, mul_assoc, commutatorElement_def] using (And.intro (inv_mem (k true g)) (k false (conjGal (γ * g))))) s₁ hs' (by simpa [*] using mem_obeying.1 hy.1 _ (.inr (.inr rfl))) u Y hu (fun w g ↦ by
    simpa [by simpa using map_cycChar_smul (σ := g) (Ω := Ω) (.id _) _ hm]
      using! (R _ w.2).2.1 g) (fun w h ⟨⟨z, h₂⟩, _, h₃⟩ t ↦ ?_) hα, ← card_fin (_ + _), ← card_fun, ← Finset.prod_coe_sort, ← card_pi] at h₁
  simp [← card_prod] at h₁; have := length_le_of_card_dvd_or_le ℓ (R := O) (.inr ⟨h₁, ((selmerZ1.finite_unramified_cocycles X).sep _).instProd⟩)
  grw [length_prod, ← relLength_add_length_inf _ (LinearMap.proj γ).ker, relLength_ker, (Submodule.map ..).eq_top_iff'.2 (s₁.smul_bijective.2.forall.2 fun c ↦ ⟨_, ft_q5 (D c) .rfl, by simp
    [hs, sub_smul]⟩), length_top, add_right_comm, ← length_prod] at this
  refine ((ENat.add_le_add_iff_left length_ne_top).1 (this.trans ?_)).trans' (length_mono fun x h ↦ ⟨ft_q5 h le_sup_left, by simpa using mem_obeying.1 h.1 _ (.inr (.inr rfl))⟩); simp_rw [length_prod, length_pi_of_fintype, Fin.sum_const, add_assoc]; grw [length_mono inf_le_left, (Finset.sum_coe_sort ..).trans (congrArg _ (funext hA)), unionWithConj, ← S.card_sdiff_add_card_eq_card S.subset_union_left, add_rotate', (length_ker_le_addVal_det _ a).trans' (length_mono (smul_one_smul (Matrix n n O) _ · |>.trans)), ← S.sum_sdiff S.subset_union_left, Finset.sum_le_card_nsmul _ _ _ fun v hv ↦ ?_, add_assoc, add_assoc, add_nsmul, add_assoc, ← h a ha]
  · gcongr; exacts [length_mono (Submodule.map_mono fun _ ↦ (selmerModule_mono · le_sup_left)), by simp]
  · let ⟨w, hw, e⟩ : ∃ w ∈ J, v = w ∨ v = star w := by clear * - hv; grind
    choose b A o H using exists_conj_side_detects (nsmul_quot_eq_zero ha) _ (p₃ w hw).6.2.2 (p₃ w hw).5 (r₂ · ∘ .imp (by clear * - hv; grind)) e; grw [iInf_le _ ⟨A, o⟩, localCocycles, ← relLength_ker, ← length_top, ← relLength_bot]
    exact relLength_le_of_inj (.proj _) (by simp) fun c d (h : c _ = 0) ↦ funext ((H c d (by
      simpa [h] using mem_obeying.1 d.1 _ (.inr (.inr ⟨(⟨w, hw⟩, b), rfl⟩)))).2 _ (p₃ w hw).4 h)
  have D := lc.comp₂ hy.2 (w.1 · <| t • ·); obtain ⟨P, hP, n, c, ⟨f, h₁, hj⟩, _, hl⟩ := p3 N (J.erase P₀) (J ∪ (S₀ ∪ (T' ∪ S₀.image star))).finite_toSet (mul_mem (subset_normalClosure ⟨_, by simp [*], _, p, q⟩) (normalClosure_mono (forall_mem_range.2 (s23_z6 hB e (by simp [hS hv, hw, (p₁ _).mt]))) (commutator_le_left _ _ z))) (((D.comp₂ (D.comp_continuous continuous_conjGal) Eq).eventually_eq _).and (.and ((o.inter o.preimage_of_continuous).eventually_mem (mul_mem u ⟨h₂, h₃⟩)) (J.eventually_all.2 (p₃ · · |>.isLocallyConstant.eventually_eq _)))); simp [U, idOrConjInv, (x · |>.1.h.mem_ker.1 (Abelianization.commutator_subset_ker _ (commutator_mono le_top le_rfl z)))] at hP hj h₁ p₆; obtain ⟨⟨⟨n₂, _⟩, _⟩, I, _, _, a, F, m, j, _⟩ := hP, mem_ker.1 (U.inv_mem h₁.2).1, hl _ .rfl; choose δ l using exists_isTameGeneratorFor Gal(Ω/E) (ℓ ^ M.succ) a; refine (Z P n₂ c (fun t ↦ by constructor <;> simp +contextual [*, IsAuxiliary, p₁ _, idOrConjInv, @eq_comm _ P, (ne_of_mem_of_not_mem · n₂), isSplit_of_q_prime, hp.r2, star_eq_iff_star_eq, fun v h ↦ ((hl _ le_sup_left).eq_one_of_mem_decompGroup · (p₃ v h).3 (p₃ v h).4.1)]) hy).elim fun x' ⟨hx, e'⟩ ↦ f.mp ?_
  choose k e using l.exists_apply_eq_nsmul a (by simpa [P.2.pow_mem_iff_mem] using! m ∘ .inr) j (fun g ↦ (x' (conjGal g)⁻¹, _)) ((hx.2.comp_continuous (by fun_prop)).prodMk hx.2)
    (by simp +contextual [mem_selmerModule_iff.1 hx, add_comm, by simpa [idOrConjInv] using (r₂ _ <| s23_z6 (τ := ·) a · (by simp [*]) ·)])
  have : IsTameGeneratorFor _ (conjPlace c.place) (conjGal δ)⁻¹ := l.imp (by simp) fun ⟨π, y, u, e, h⟩ ↦ ⟨star π, unitsRep cmConj (unitsRep δ y), by simpa [a.conjPlace_star.isUniformiser_iff, a.isUniformiser_iff, DiscreteUnits.ext_iff, conjGal, ↓← map_inv, ← map_cycCharMod_mul, isComplexConj_cmConj.cycCharMod_eq_neg_one] using (⟨u, congr(unitsRep cmConj (unitsRep δ $e)), congr(-unitsRep cmConj $h)⟩ : _ ∧ _ ∧ _)⟩; simp [*, idOrConjInv, cocycle_apply_inv Y, ft_v2, -LinearEquiv.coe_curry_symm, @funext_iff Bool] at e e'
  simpa [← e, e', add_neg_eq_zero] using (R _ w.2).2.2 ![P, star P] ![c.place, conjPlace c.place] ![c.φ, _] ![δ, (conjGal δ)⁻¹] (by simp [(isSplit_of_q_prime n).symm])
    (by simpa [*, -h₁, a.conjPlace_star, F.conjPlace_conjGal]) _
    (ft_q5 (Submodule.smul_mem _ t (nsmul_mem hx k)) le_sup_left)
end
open Module Fintype IsLocalRing Polynomial LinearMap Submodule
private lemma x0 {O m B} [CommRing O] [DVR O] [Fintype m] [AddCommGroup B] [Module O B] {I : Ideal O} [IsArtinian O (O ⧸ I)] (Φ₀ Φ₁ : B →ₗ[O] m → O ⧸ I) Y : ∃ T, List.length T ≤ card m ∧ ∀ s, residue O s ∉ T → length O ↥(Y ⊓ (s • Φ₀ - Φ₁).ker) ≤ length O ↥(Y ⊓ Φ₀.ker ⊓ (Y.map Φ₀).comap Φ₁) := let Z := ⨆ s : O, Y ⊓ (s • Φ₀ - Φ₁).ker
  have z : Z ≤ (Z.map Φ₀).comap Φ₁ := iSup_le fun s y h ↦ ⟨_, Z.smul_mem s (mem_iSup_of_mem s h), by aesop⟩
  have ⟨σ, e⟩ := projective_lifting_property _ ((I.mkQ.compLeft m).submoduleComap _)
    (Φ₀.submoduleMap_surjective Z)
  have q := e ▸ submoduleComap_surjective_of_surjective _ _ I.mkQ_surjective.comp_left
  (projective_lifting_property _ (Φ₁.restrict z ∘ₗ σ) q).elim fun ψ e ↦ ⟨(ψ.charpoly.aroots _).toList, by simp [(card_roots_map_le_natDegree _).trans, (finrank_le _).trans, charpoly_natDegree], fun s hs ↦ by
  simp [map_monic_ne_zero, charpoly_monic, eval_charpoly, ← isUnit_iff_isUnit_det, End.isUnit_iff] at hs
  grw [length_mono (le_inf (le_iSup _ s : _ ≤ Z) inf_le_right), ← ENat.add_le_add_iff_left, relLength_add_length_inf, ← relLength_add_length_inf _ Φ₀.ker] <;> simp [relLength_ker, length_ne_top]
  exact add_le_add (length_mono (Subtype.forall'.2 ((q.comp hs.2).forall.2 (⟨σ ·, by simp_all [DFunLike.ext_iff, -Subtype.forall]⟩)))) (length_mono (by grw [← (by simp [Z] : Z ≤ Y)]; order))⟩
end
section
seal Finset.univ Finset.sum Finset.prod
open Polynomial Filter Finset Real IsUltrametricDist NeZero Function Fint CoeffRing
variable {ℓ} [p : ThePrime ℓ] {κ : Type}
private lemma ft_c3 [Fintype κ] (y : κ → ℝ) {r} (hy : ∀ k, 0 < y k) (h0 : 0 < r) (h1 : r < 1) (e : ‖(ℓ : PadicAlgCl ℓ)‖ < r ^ (ℓ - 1)) : ∀ᶠ N in atTop, ∀ᶠ O : CoeffRing ℓ in atTop, ∀ F : κ → O.1[X], (∀ k, ∃ i, y k ≤ ‖((F k).coeff i).1‖ * r ^ i) → ∃ ζ : ↑O, ζ ^ ℓ ^ N = 1 ∧ ∀ k, r * y k ≤ ‖((F k).eval (ζ - 1)).1‖ := (exists_pow_lt_of_lt_one (by simp [ne] : 0 < ‖(ℓ : PadicAlgCl ℓ)‖) h1).rec fun a ha ↦ ((tendsto_sum_range_one_div_nat_succ_atTop.atTop_mul_const_of_neg (log_neg h0 h1)).eventually_lt_atBot _).mono fun N J ↦ .mono (.all fun j : range N ↦ eventually_primitiveRoot (ℓ ^ j.1.succ)) fun O η F h ↦ by
  contrapose! J; let ρ j := r ^ (↑(ℓ ^ j) : ℝ)⁻¹
  let ⟨m, ρ1⟩ : Monotone ρ ∧ ∀ j, ρ j ≤ 1 := by simp [ρ, Monotone, rpow_le_one_iff_of_pos, *]; bound [pos ℓ]
  let g j := (@gaussNorm_isAbsoluteValue (ρ j) O _ (.comp (NormedField.toAbsoluteValue _) O.1.subtype_injective) isNonarchimedean_norm (by bound)).toAbsoluteValue; have U {j F x} : g j F ≤ x ↔ ∀ i, ‖(F.coeff i).1‖ * _ ≤ x := ⟨swap (F.le_gaussNorm _ (by bound) · |>.trans), (exists_eq_gaussNorm ..).choose_spec.trans_le ∘ (· _)⟩; have G k t : y k ≤ g t (F k) := (h k).rec (by grw [← U.1 le_rfl ·, ← m bot_le]; simp [ρ]); choose Q hQ using (dvd_prod_of_mem F <| mem_univ ·); have Z t : 0 < ∏ k, g t (F k) := prod_pos (by grind); grw [sum_mul, ← sum_le_sum fun j _ ↦ ?_, sum_range_sub' fun j ↦ a * (∏ k, g j (F k)).log, ← G, U.2 (by bound)] <;> simp [prod_pos, le_of_lt, *]; choose η hη using η ⟨j, ‹_›⟩; choose k u using fun i ↦ J (η ^ i) (by grind [hη.pow_eq_one_iff_dvd, pow_dvd_pow, =_ pow_mul]); have W := congr(($(X_pow_sub_C_eq_prod hη one_le (one_pow _)).comp (X - C (-1))).derivative).symm; choose S s using (range (ℓ ^ j.succ)).dvd_sum fun i hi ↦ prod_erase_mul _ (fun i ↦ X - C (η ^ i - 1)) hi ▸ mul_dvd_mul_left _ ((sub_mul _ (F (k i)) _ ▸ (dvd_modByMonic_sub ..).mul_right (Q (k i))).trans (sub_dvd_pow_sub_pow _ _ (a * j.succ))); simp [-map_neg, -map_sub, -map_pow, Polynomial.prod_comp, sub_sub, ← map_add, ← hQ, mul_sub, derivative_prod_finset, derivative_pow, neg_add_eq_sub, ← sum_mul] at W s
  have K t (ht : j ≤ t) := (by
    have n : IsNonarchimedean (g t) := isNonarchimedean_gaussNorm _ isNonarchimedean_norm (by bound)
    have l b : g t (X - C b) = ‖b.1‖ ⊔ ρ t ∧ g t (C b) = ‖b.1‖ := ⟨eq_of_forall_ge_iff (by
      simp [U, ← Nat.and_forall_add_one, coeff_X]; bound [norm_nonneg b.1]), gaussNorm_C ..⟩
    have z i := (norm_pow_sub_one_le_norm_sub_one (norm_le_one η) i).trans
      ((lt_of_pow_lt_pow_left₀ _ (by bound) (by rwa [norm_zeta_sub_one_pow (by simpa), Nat.totient_prime_pow_succ p.out, pow_mul, rpow_inv_natCast_pow h0.le out])).le.trans (m ht))
    have V a b := congr(g t $s) ▸ n.add_eq_right_of_lt (map_neg_eq_map _)
      ((n.apply_sum_le_sup a).trans_lt b)
    simp [map_neg_eq_map, -map_neg, -map_sub, -map_natCast, ne, *] at V
    use (eq_inv_mul_iff_mul_eq₀ (by positivity)).2 (V fun _ _ ↦ by
      grw [ρ1, (u _).le, G, mul_assoc, ← map_mul, ← hQ, mul_pow, pow_mul, ha] <;> simp [*]))
  have V := log_le_log (by simp [ne, field, *]) ((@U j S _).2 (by grw [m j.le_succ, ← U])); simp [log_mul, rpow_def_of_pos, ρ, pow_add, field, ne_of_gt, ne, *] at V ⊢; grind [nsmul_le_nsmul_left_of_nonpos (log_neg h0 h1).le p.out.two_le]
private lemma w5 [Finite κ] {δ : NNReal} (hδ : 0 < δ) (m L a q : ℕ) (B : κ → NNReal) : ∀ᶠ N in atTop, ∀ᶠ O : CoeffRing ℓ in atTop, ∀ (σ T : Type) [Fintype σ] [Fintype T], Fintype.card σ ≤ q → ∀ (D : T → O.1[X]) (F : κ × Set.Icc 1 m → MvPolynomial σ _) (u : _ → _ → ↑O), (∀ n, (D n).Monic) → ∑ n, (D n).natDegree ≤ L → (∀ k j, ↑ℓ ∣ (u k j - 1) ^ a) → (∀ k, ellVal ((F k).eval (u k)).1 ≤ B k.1) → ∃ ζ : σ → ↑O, (∀ k, ellVal ((F k).eval (ζ · ^ k.2.1)).1 ≤ ↑(δ + B k.1)) ∧ ∀ j, ζ j ^ ℓ ^ N = 1 ∧ ∀ n, ellVal ((D n).eval (ζ j)).1 ≤ δ := by
  choose r r0 e r1 using exists_pow_btwn (x := ‖(ℓ : PadicAlgCl ℓ)‖ ⊔ ℓ ^ (-δ.toReal)) (q + L + ℓ + m * a).succ_ne_zero (by simp [norm_p_lt_one, rpow_lt_one_iff, Fact.out, *]) one_pos; simp [pow_lt_one_iff_of_nonneg r0.le] at r1; have R n (h : n ≤ _ := by grind) := max_lt_iff.1 (e.trans_le (pow_le_pow_of_le_one r0.le r1.le h))
  refine .mono (.all fun n : Set.Iic q ↦ ft_c3 (Option.rec (r ^ L) fun k : κ × Set.Icc 1 m ↦ ℓ ^ (-B k.1 : ℝ) * r ^ n.1) (by rintro ⟨⟩ <;> bound [pos ℓ]) r0 r1 (R _).1)
    fun N Y ↦ .mono (.all Y) fun O Y σ T _ _ hq D F u hD hL hu hB ↦ (univ.induction_on (motive := (fun T s ↦ ∃ ζ, (∀ k, ℓ ^ (-B k.1 : ℝ) * r ^ #s ≤ ‖((F k).eval (s.piecewise (ζ · ^ k.2.1) (u k))).1‖) ∧ ∀ j ∈ s, T ζ j) (_ : _ → Set σ)) ⟨1, by simp [← ellVal_le_iff, *]⟩ fun j s _ ⟨ζ, H, h⟩ ↦ ?_).imp fun ζ ↦ .imp (by grw [← (R _).2.le]; simp [rpow_add, pos, ↓ellVal_le_iff]) (· · (by simp))
  have p d x y (h : x ^ d = (y j).1) G : (MvPolynomial.eval y G : ↑O).1 = aeval (x - 1)
    (G.aeval fun i ↦ ite (i = j) ((1 + X) ^ d) (C (y i)))
  apply G.induction_on <;> simp +contextual [*, apply_ite]
  choose z Z W using Y ⟨_, s.card_le_univ.trans hq⟩ (Option.rec (taylor 1 (univ.prod D)) _) (·.rec ⟨(univ.prod D).natDegree, by simp [leadingCoeff_prod, natDegree_prod_le, hL.trans', pow_le_pow_iff_right_of_lt_one₀, *]⟩ fun k ↦ (not_forall₂.1 (mt (pow_le_norm_aeval ((X ^ k.2.1 - C (u k j).1) ^ a) (O.1.val 1) r0.le) (by simpa [leadingCoeff_X_pow_sub_C k.2.2.1, norm_sub_rev] using ((dvd_iff_norm_le ..).1 (hu ..)).trans_lt (R _ (by grw [k.2.2.2]; lia)).1))).rec fun w ⟨hw, W⟩ ↦ (exists_norm_finsetSum_le ..).imp fun i h ↦ by
      simp [norm_sub_rev] at hw W ⊢; grw [H, p k.2 w, aeval_eq_sum_range, h.2, O.1.smul_def] <;> simp [*]; gcongr)
  have V n := ellVal_le_iff.2 <| ((dvd_iff_norm_le ..).1 (eval_dvd (dvd_prod_of_mem D (mem_univ n)))).trans' (by grw [(R L.succ).2, pow_succ', W none, taylor_eval_sub]); refine ⟨update ζ j z, fun k ↦ ?_, by grind⟩; simpa +contextual [pow_succ, mul_rotate' r, p k.2 z, piecewise, *] using (W k).trans congr(‖$(aeval_algebraMap_apply _ (z - 1) _)‖).ge
end
section
open Module Fintype NeZero Finset Fint
variable {ℓ} [ThePrime ℓ] {E ι : Type} [Field E] [UnramCMField E] [Finite ι] {n : ι → Type} [∀ i, Fintype (n i)] {S₀ S : Finset (FinPlace E)} {z M} {γ β : ι → _} (hS : S ⊆ S₀) (hz : z ∈ inertiaAbove (S₀ \ placesDividing E ℓ))
include hS hz
attribute [-simp] Set.insert_eq_of_mem
open IsLocalRing Ideal LinearMap Order Matrix.Module Function Ideal.Quotient in
lemma s1 {O W} [CommRing O] [PadicIntegerRing O ℓ] {ρ : ∀ i, _ →* Matrix _ (n i) O} {L : ∀ _, Set _} (h : ∀ i, IsBalanced ℓ S (ρ i) (L i) (γ i) (β i) M) (hW : W ∈ nhds z) {a : O} : a ∣ ℓ ^ M → ∃ J₀, ∀ N, let X T J x i a := selmerModule (ρ i) (unionWithConj S T) (L i ∪ s23_v1 J x i ∪ {.single (γ i) 1}) (QuotSpan a)
  let Q := IsPencil ℓ S₀ (fun i g ↦ s23_z5 ℓ M (ρ i) g = 1) W N
  ∃ P₀ J x, Q P₀ J x ∧ #J ≤ J₀ ∧ ∀ i, length O (X J J x i a) ≤ β i := by
  refine WfDvdMonoid.induction_on_irreducible a (by simp [ne] at ·) (fun a u _ ↦ ⟨1, (p3 · ∅ S₀.finite_toSet (Subgroup.subset_normalClosure (by simpa)) hW |>.imp fun P₀ ⟨_, _, A, _⟩ ↦ ⟨{P₀}, fun _ ↦ (A, 0), by constructor <;> simp_all [IsAuxiliary, isSplit_of_q_prime], by simp [(length_mono le_top).trans, u]⟩)⟩) fun a ϖ z hϖ ih ha ↦ ?_
  obtain _ := NeZero.mk z, NeZero.mk hϖ.ne_zero, dvd_of_mul_left_dvd ha
  have F i J R : Finite (selmerModule ..) := let := IsTorsionBy.module (smul_quot_eq_zero_of_dvd ha)
    have ⟨_, _, _, _, _, H⟩ := s23_k3 _ (ρ i) ((h i).1.eventually_eq 1) (finite_toSet J) R
    .of_injective _ (H _ (nsmul_quot_eq_zero ha) fun g e b ↦ congr($e • b).trans (by simp)).2.1.injective
  let f : {f // ker f = ⊥} := ⟨_, (span {a}).ker_liftQ_eq_bot' ((span {ϖ * a}).mkQ ∘ₗ (ϖ • 1)) (ext (by simp [ker_comp, mem_span_singleton, mul_dvd_mul_iff_left, ne]))⟩
  apply (ih ‹_›).imp'
  intro J₁ ih N X Q
  choose P₀ J x q d b using ih N
  have I {J x} (hp : Q P₀ J x) T ⦃k : O⦄ (hk : k ∣ ℓ ^ M) {i R K} l : selmerModule (ρ i)
    (unionWithConj S J) R (QuotSpan k) ⊓ ker (pi fun v : ↥(J \ T) ↦ ft_v2 (x v).1.γ) ≤ selmerModule _ (unionWithConj S T) K _ := fun c ⟨a, z'⟩ ↦ selmerModule_mono
    a l fun v o ↦ have ⟨w, j, e⟩ : ∃ w ∈ J \ T, v = w ∨ v = star w := by clear * - o; grind
    (hp.3 w (sdiff_subset j) |> fun p ↦ exists_conj_side_detects (nsmul_quot_eq_zero hk) _ p.6.2.2 p.5 (by clear * - o h; grind [inertiaAbove, IsBalanced]) e).elim fun b ⟨_, _, H⟩ ↦ (H c a congr(($z' ⟨w, j⟩ ⟨b, ·⟩))).1
  let g (s : _ × _) k i := length O (X s.1 s.1 s.2 i k)
  obtain ⟨⟨J, x⟩, ⟨h₀, B, d⟩, W⟩ := (InvImage.wf (univ.sum <| g · (ϖ * a)) wellFounded_lt).has_min
    {t | Q P₀ t.1 t.2 ∧ g t a ≤ β ∧ #t.1 + univ.sum (g t (ϖ * a)) ≤ ?f J₁} ⟨(J, x), q, b, by
    grw [ENat.natCast_toNat, d, sum_le_sum fun i _ ↦ by grw [← relLength_add_length_inf, length_mono (I q ∅ ha bot_le), relLength_ker, length_mono le_top, length_top, length_pi, (by simpa : ENat.card _ ≤ .card (Fin J₁)), ← length_finsupp]]
    simp [length_ne_top, -length_finsupp]⟩
  refine ⟨_, _, _, h₀, Nat.cast_le.1 (le_of_add_le_left d), fun i ↦ by_cases (h₀.g8 (h i) rfl hS ha · fun P q Z r ↦ relLength_eq_zero.1 (not_bot_lt_iff.1 fun y ↦ ?_)) fun u ↦ (B i).trans' (length_le_of_le_map ((f.1.compLeft _).compLeft _) _ (mk_surjective.comp_left.comp_left.forall.2 fun s v ↦ by
    choose a e using (mem_span_singleton.1 <| hϖ.maximalIdeal_eq.le fun h ↦ u ⟨_, v, ·, ·, h.map _⟩)
    cases funext₂ e
    exact ⟨(a · ·), v.imp (fun h ↦ (comp_mem_obeying_iff .id).2 (f.2.le <| (comp_mem_obeying_iff _).1 h · · ·)) (.desc _ _ · (ker_eq_bot.1 f.2).comp_left), rfl⟩))⟩
  have K := by simpa [q, ker_pi, iInf_subtype] using I (r 0) J
  choose b c H using fun k [NeZero k] ↦ x0 (ft_v2 Z.γ) (ft_v2 Z.φ) (X (insert P J) J x i k)
  obtain ⟨t, v, ht, hu⟩ := by simpa [residue_surjective.exists] using Cardinal.exists_notMem_of_length_lt (0 :: b (ϖ * a) ++ b a) (.trans_le (mod_cast (h i).5.trans_le' (by clear * - c; grind [card_prod, card_bool])) (Cardinal.natCast_toNat_le _))
  let u := (insert P J, update x P (Z, Pi.single i v.unit.inv))
  have A j k : X u.1 u.1 u.2 j k ≤ X u.1 J x .. ⊓ ker (ft_v2 Z.γ - (u.2 P).2 j • ft_v2 Z.φ) := fun c ↦ by simp +contextual [-Pi.single_apply, X, u, selmerModule, mem_obeying, funext_iff, s23_v1, ft_v2, or_imp, forall_and, (ne_of_mem_of_not_mem · q)]
  have U {k} [NeZero k] hk h := (forall_update_iff ⊥ fun j r ↦ r + g u k j ≤ g (J, x) ..).2 ⟨by
    unfold g
    grw [length_mono, H k t h, length_mono, relLength_add_length_inf]
    grw [K hk .rfl]
    grw [A]
    simp +contextual [u, smul_smul, IsConcreteLE.le_iff], fun j e ↦ by simpa [bot_eq_zero'] using length_mono ((A ..).trans (by simp [u, X, *]))⟩
  have L := lt_of_le_of_lt' (by simpa [bot_eq_zero', sum_update_of_mem, X] using sum_mono (U ha ht)) (ENat.lt_add_left (by simp [g, length_ne_top]) y)
  exact W u ⟨r _, B.trans' (le_of_add_le_right (U ‹_› hu)), by
    grw [card_insert_le, Nat.cast_succ, add_right_comm, add_assoc, add_one_le_of_lt L, d]⟩ L
open Matrix Filter MvPolynomial ENNReal NNReal CoeffRing IsDiscreteValuationRing Subalgebra
lemma g0 {κ T : Type} [Finite κ] [Finite T] {O : CoeffRing ℓ} {ρ : ∀ i, _ →* Matrix _ (n i) O} {μ : κ → T → _} {L : ∀ _, _} {B : ι → _} (hρ : ∀ i, IsBalanced ℓ S (ρ i) (L i) (γ i) (β i) M) {val : κ → _} (hf : ∀ k, IsFamily S₀ (μ k) (val k)) (hB : ∀ i, B i ≠ ⊤) (hβ : ∀ i, O.normLength (β i + ∑ b, addVal _ (ρ i (idOrConjInv b z) - 1).det) ≤ B i) {c η : ℝ≥0} (hc : ∀ k t, ellVal ((μ k t z).1 - 1) ≤ c) (hη : 0 < η) m : ∃ I ψ, ∀ d ∈ Set.Icc 1 m, (∀ k, ellVal (val k I (ψ ^ d)) ≤ ellVal (val k ∅ 1) + 8 * c + η) ∧ s23_g7 S₀ I (ψ ^ d) η ∧ ∀ i, ∀ᶠ O' in atTop, ∃ hO : O ≤ O', ∃ ψ', (∀ g, (ψ' g).1 = (ψ ^ d) g) ∧ O'.normLength (length O' (selmerModule (twistRep (inclusion hO).1 ψ' (ρ i)) (unionWithConj S I) (mapRel (inclusion hO).1 '' (L i ∪ {.single (γ i) 1})) (QuotSpan (ℓ ^ M : ↑O')))) ≤ B i + η := by
  choose J₀ hJ using s1 hS hz hρ ((Eventually.all fun k ↦ .all fun t ↦ ((IsUltrametricDist.isClosed_ball ..).preimage (Units.continuous_val.comp ((hf _).1 _))).compl_mem_nhds (ellVal_le_iff.1 (hc k t)).not_gt).and (.all fun i ↦ (((hρ i).1.comp_continuous continuous_conjGal.inv).prodMk (hρ i).1).eventually_eq z)) dvd_rfl; choose δ hδ _ using exists_pos_mul_lt hη (J₀ * 8 + 2)
  lift B ⊕ᵥ fun k ↦ ellVal (val k ∅ 1) + 8 * c to ι ⊕ κ → ℝ≥0 using by
    simp [ellVal, mul_eq_top, (hf _).4, *] with b W
  choose k hk using (w5 hδ 1 _ 1 _ b).exists; choose N hN l using ((w5 hδ m _ _ J₀ (δ + b · + J₀ * 8 * δ)).and (Ici_mem_atTop _)).exists; choose P₀ J x hp hJ hl using hJ N; let θ (j : J) := (x j).1.h; obtain ⟨A, o, q, a⟩ := hp.1, hp.2, J.erase_subset P₀, fun j : J ↦ hp.3 _ j.2
  have Q {y hy I} (_ : ∀ j, ↑j ∉ I → y j = (1 : PadicAlgCl ℓ) := by simp +contextual [t]) :
      IsFromU1 (placesDividing E ℓ) I (pointChar θ y hy) := by
    choose φ e b d using (a · |>.exists_ideleChar)
    use (LocallyConstant.unflip (⟨θ ·, (a _).isLocallyConstant⟩)).2.comp
      (pointChar (Pi.evalMonoidHom _) y hy), pointChar φ y hy, by simp [e], fun u h k ↦ prod_eq_one _ fun j ↦ by by_cases j.1 ∈ I <;> simp +contextual [*], (by simp [θ, d _ · · ·])
  have U {I} : I ⊆ J → IsAuxiliary S₀ I := by clear * - A; grind
  have K {k} I (v : J) s := ((hf k).3 I v · (U s) · · _ _ (a v).3 (a v).4); choose O' hN hk hO hm V hV using (hN.and (hk.and (.and (Ici_mem_atTop O) (.and (.all fun p : (κ × T) × J × ℤˣ ↦ eventually_mem (norm_eq_one_of_continuous ((hf p.1.1).1 p.1.2) ((x p.2.1).1.φ ^ p.2.2.1)).le) (.all fun p : κ × Set.Iic J ↦ (let ⟨_, _, g, c, a, b⟩ := (hf p.1).2 _ (U p.2.2); .mono (.all (eventually_mem <| a ·)) fun O H ↦ ⟨∑ i, C ⟨_, H i⟩ * ∏ j, X j ^ (θ j (g i)).toAdd.val, by simp [b]⟩ : ∀ᶠ O : CoeffRing ℓ in _, ∃ F, ∀ {y} hy, (eval y F : O.1).1 = val p.1 p.2 (pointChar θ (y ·) hy))))))).exists; let e := (inclusion hO).1; have r i := hp.j8 i (by simp [s23_z5, (hρ i).2 · <| ·.imp fun _ ↦ by gcongr]) k l fun _ ↦ id; let t (s : ι ⊕ κ) (j : J) := ite (↑j = P₀) 1 (s.elim (e ∘ (x j).2) 0)
  choose G g g' using fun i ↦ m9 (.id _) _ (a · |>.isLocallyConstant)
    (hρ i).1 (L i ∪ {.single (γ i) 1} ∪ s23_v1 (J.erase P₀) x i) _
  choose u f₃ p s using hk (Fin 1) (J × ι × Bool ⊕ _) le_rfl ((fun (v, i, b) ↦ ((ρ i (idOrConjInv b (x v).1.φ)⁻¹).map e).charpoly) ⊕ᵥ (.X - .C ⟨_, hm ·⟩)) (fun s ↦ eval₂ C (fun j ↦ 1 + C (t s.1 j) * (X 0 - 1)) (s.1.elim (.map e ∘ G) (V ⟨·, {P₀}, by simpa⟩))) 1 (by simp [↓charpoly_monic, Polynomial.Monic]) (by simp [↓sum_prod_type]; grw [hJ]) (by simp) (by
    rintro ⟨i | k', _⟩ <;> simp [← eval_assoc, congrFun W, hV]
    · grw [← hβ, ← hl]
      convert normLength_mono ((g i).trans (r i _ _ (one_pow _) {P₀} (idOrConjInv ·.2 z) (by simpa) (by simp) (by simpa using! hp.5.2 i))) <;> simp [e, eval₂_eq', eval_eq' _ (G i), sum_prod_type, mapRel.eq_def, twistAtPoint, funext_iff] <;> clear * - o <;> refine ?u; ext; simp [s23_v1]; grind
    convert! K ∅ ⟨_, o⟩ (by simpa) nofun 1 ⟨.const _, 1, by simp⟩ c (by
      simpa [ellVal_le_iff, dist_eq_norm'] using hp.5.1 k')
    ext; simp)
  choose F f ϕ using fun i ↦ m9 e _ (a · |>.isLocallyConstant) (hρ i).1 ..; simp [← eval_assoc, Function.comp_def] at f₃ p
  choose ζ f hζ w using hN J (Set.Icc 1 m) (by simpa) _ (·.1.elim F (V ⟨·, J, by simp⟩)) _
    (Polynomial.monic_X_pow_sub_C 1 <| ne_of_gt ·.2.1) (by simp [-map_one]; rfl) (fun s j ↦ (ft_m0 (t s.1 j) p 0 .refl).1) (by
    rintro ⟨i | k', _⟩ <;> simp
    · grw (transparency := default) [← normLength_addVal, (f i).trans (r i _ e p _ _ q (by simp) fun _ ↦ rfl), g' i _ e, map_add, normLength_addVal, f₃.1, map_sum, sum_le_sum fun z _ ↦ normLength_addVal _ ▸ (ellVal_le_ellVal ((dvd_iff_norm_le ..).1 ⟨det _, by
          erw [eval_charpoly, ← det_mul, sub_one_mul]; congr; simp [← Matrix.map_mul, ← map_mul, smul_one_eq_diagonal]⟩)).trans (s 0 (.inl (⟨_, q z.1.2⟩, i, z.2))), ← hJ]
      simp; gcongr; norm_num
    have y j : (1 + t (.inr k') j * (u 0 - 1)).1 ^ ℓ ^ N = 1 := mod_cast l.dest.choose_spec ▸ by
      simp [pow_add, pow_mul, t, add_ite, *]
    grw [← f₃.2, hV _ y, hV _ y, ← hJ, ← q, ← @Finset.induction_on' _ (fun I ↦ ellVal (val k' (insert P₀ I) (pointChar θ _ y)) ≤ _ + #I * 8 * _) _ _ (by simp) fun v I a b w i ↦ ?_, insert_erase o]; lift v to J using q a; simp at a; grw [I.insert_comm, K _ v (by grw [b]; simp [*]) (by simp [*]) _ Q δ fun z t ↦ (ellVal_le_ellVal ((hp.v8 y v true).2 a ▸ by fin_cases t <;> simp [t, (isUnit_iff_norm_eq_one _).1 (.of_pow_eq_one p out), norm_eq_one_of_continuous, (hf _).1, sub_div', inv_eq_one_div, norm_pos_iff.1, norm_sub_rev, mul_comm (u 0).1, mul_one_div, -one_div])).trans (s 0 (.inr ((k', z), v, -t))), i]; simp [w, add_mul, add_assoc])
  replace f s := (f s).trans (.trans_eq (coe_le_coe.2 (by linarith)) congr($W _ + η)); have hd d j : (ζ j ^ d).1 ^ ℓ ^ N = 1 := mod_cast by simp [pow_right_comm _ d, hζ]
  use J, pointChar θ _ (hd 1), fun d e ↦ ?_; rw [show _ ^ d = pointChar θ _ (hd d) by ext; simp [← prod_pow, pow_right_comm]]; exact ⟨(hV .. ▸ f ⟨.inr ·, d, e⟩ :), ⟨A, Q, _, fun v ↦ ⟨(a v).5, map_one _, _, _, (a v).6.2.2⟩, (sum_le_card_nsmul _ _ ↑δ fun v _ ↦ (hp.v8 (hd d) v true).1 ▸ by simpa using w v ⟨d, e⟩).trans (by simp; grw [hJ]; norm_cast; bound)⟩, fun i ↦ mem_atTop_sets.2 ⟨O', fun R h ↦ ⟨hO.trans h, pointChar θ (inclusion h ∘ ζ ^ d) (Subtype.ext <| hd d ·), by simp, (normLength_mono (ϕ i _ (inclusion h).1 _)).trans (by simpa [eval₂_eq', eval_eq'] using f ⟨.inl i, d, e⟩)⟩⟩⟩
end
section
open Lift Polynomial Multiset minpoly Pi Filter Function
variable {P} {D : Data P} {ℓ} [ThePrime ℓ] {O : CoeffRing ℓ} {n} [Fintype n]
private lemma n7 {N r K M} (b : card M ≤ N) (k : ∀ y ∈ M, ∃ a ∈ Set.Icc 1 r, y ^ (ℓ ^ a - 1) = 1) (h : ∀ Q : O[X], (∀ y ∈ M, Q.aeval (y : PadicAlgCl ℓ) = 0) → K Q) : Lift.IsTameType ℓ r (N * r) K :=
  have H y c : (minpoly _ y).Monic ∧ (minpoly ℤ_[ℓ] y).natDegree ≤ r := by
    choose f hf hx using k y c; obtain ⟨a, rfl : wittToQpBar _ = _⟩ := exists_flatFq_root (f := f.toPNat hf.1) _ _ fun _ ↦ hx; grw [algHom_eq _ wittToQpBar_injective, natDegree_le, KummerChart.JumpLattice.finrank_wittFq]; use monic (.of_finite ..), hf.2
  ⟨h _ (k · · |>.elim fun a h ↦ by rw [(Finset.dvd_lcm (mem_Icc.2 h.1)).choose_spec]; simp [pow_mul, h]), _, monic_multiset_prod_of_monic _ _ (H · · |>.1), by grw [natDegree_multiset_prod_le, sum_le_card_nsmul, ← b] <;> aesop, h _ (by aesop (add simp map_multiset_prod))⟩
variable [PadicIso ℓ] {τ} {u : AbsGal D →* Matrix n n O}
lemma IsColumn.eq_one_of_mem_inertiaAbove {t S R} (h : IsColumn (n := n) D t τ S R) : ∀ g ∈ inertiaAbove (placesDividing _ ℓ ∪ placesAboveG D ∪ S)ᶜ, R g = 1 := by grind [IsColumn, IsGoodAt, IsPlaceOver.valuation_natCast_eq_one_iff, placesDividing, inertiaAbove]
private lemma k1 {R t S} w {𝓡 : _ → Prop} (h : IsColumn D t τ S R) (m : 𝓡 R) : let v := s23_d1 (u.comp (decompGroup _ (placeOver w.1)).subtype)
  let J g := τ (s23_z1 ((localChart ℓ _ w).e.comp (algebraMap ..)) g)
  IsLatticeIn R u → (∀ g, HasJumps v.ρ (t0 O g) (J g)) ∧ InClass (⨅ _ : ↑w ∈ placesAboveG D, ⊥) (fun s Q ↦ w.1 ∈ placesAboveG D ∧ ∀ R, 𝓡 R → ∃ P, PolyKillsAt R (placeOver w.1) s.1 P ∧ ∀ y, P.IsRoot y → Q.aeval y = 0) (toFinset ∘ J ∘ surjInv s23_w8) v := by
  let ⟨⟨_, c⟩, d, z⟩ := h.local_conditions _ (by simp) w.1.isPlaceOver_placeOver
  intro v J ⟨P, hP⟩
  let L := P.toLin.toLinearEquiv
  let F := L.1.restrictScalars _ ∘ₗ O.1.val.toLinearMap.compLeft n
  have hf g x : F (v.ρ g x) = decompRep R _ g (F x) := congr(L $(funext (O.1.val.1.map_mulVec _ x))).trans (hP g ▸ by simp [L, F, mul_assoc]; rfl)
  suffices _ from ⟨this, .of_jointly_injective le_sup_left (by by_cases ↑w ∈ placesAboveG D <;> simp [*, (z _).2]) _ (fun _ ↦ .of_forall hf) ?I, by simp [← count_ne_zero, ← this .., surjInv_eq], fun s Q k hs ↦ (k.2 R m).rec fun _ ⟨a, _⟩ ↦ .of_jointly_injective hs _ (by tauto) ?I le_top (fun _ ↦ ⟨c, map_eq_zero_of_roots (eval₂RingHom' _ _ (commute_coefEnd_linearFrob c hs)) ((((mapClusterPt_one_atTop_pow _).frequently (mem_comap'.1 c.eventually_linearFrob_eq_one)).mono (by simpa [← linearFrob_pow c hs ·] using · (map_pow ..) (hs.pow _))).forall_exists_of_atTop 1) (a.2 hs).2 (by simpa [eval_map])⟩) rfl fun () _ _ ↦ L.map_smul ..⟩
  any_goals intro g _; rw [t0, ← jump_baseChange ⟨F.1, fun _ _ ↦ L.map_smul ..⟩ (basisFun ..) ((basisFun ..).map L) (fun _ ↦ congr(L $(by ext; simp [apply_ite]))) (.of_forall hf), ← @d _ _ g]
  all_goals simp [F, v, J, funext_iff]; tauto
open DistribSMul LinearMap NeZero Submodule crysCocycles Ideal.Quotient Matrix.Module
lemma s23_d8 {ℓ} [ThePrime ℓ] {X n R Γ G d : Type} [Fintype X] [Fintype n] [CommRing R] [PadicIntegerRing R ℓ] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group G] [Fintype d] [𝒥 : OverGp Γ ℓ] (hj : Topology.IsOpenEmbedding 𝒥.toGp) {η : Γ →* _} {u : X → G →* Matrix n n R} {ρ : G →* Matrix d d R} {F K U} (hZ : ∀ x, InClass F K U (s23_d1 ((u x).comp η))) m : let L := s23_d1 (ρ.comp η); InClass F K U L → relLength (obeyingCocycles u ρ (ℓ ^ m)) ((obeying (relationsOn (crysCocycles L.ρ)) _).comap (.funLeft R _ η)) ≤ relLength (crysCocycles L.tateDual.ρ) (cupOrthogonal (InClass F K U) _) := by
  intro L H; let τ := (mkQ (R ∙ (ℓ : R) ^ m)).compLeft d; obtain ⟨⟨f, b⟩, o : Function.Surjective τ, ⟨⟩⟩ := exists_perfect_pairing (L := L), mk_surjective.comp_left, PSigma.mk _ (discreteTopology_bot (QuotSpan (ℓ ^ m : R))); have hτ : τ.toAddMonoidHom.ker = pPowMultiples L m := by ext; simp [τ, L, Algebra.smul_def, funext_iff, eq_zero_iff_mem, mem_span_singleton, Classical.skolem, mul_comm]
  have e g x : τ (L.ρ g x) = ρ (η g) • τ x := by ext; apply map_sum (mkQ _)
  have C y := _root_.funext (nsmul_quot_eq_zero dvd_rfl <| τ y ·); grw [relLength_comap, relLength_mono le_rfl (Submodule.map_le_iff_le_comap (f := τ.compLeft Γ).2 (comp_mem_obeying ·))]; refine (length_le_of_card_dvd_or_le ℓ ∘ .inl : (toAddSubgroup _).relIndex (toAddSubgroup _) ∣ (toAddSubgroup _).relIndex (toAddSubgroup _) → relLength .. ≤ relLength ..) (H.isPotCrys.relIndex_dvd_of_orthogonal hj H.dual.isPotCrys (.ofBijective _ b) (by simp) ⟨by simp, by simp⟩ e o hτ (V := .of (actionRep _ _ (ρ.comp η)) (by simpa [o.forall, e, continuous_prod_of_discrete_right] using fun x ↦ (continuous_comp hj H.isPotCrys τ C (coboundary_mem x)).add_const (τ x))) |> (forall₂_and.1 fun s hs ↦ ?_).elim)
  choose y hY t q a ha E using show ∃ y, InClass F K U y ∧ ∃ t : y →ₗ[R] _, (∀ g x, t (y.ρ g x) = ρ (η g) • t x) ∧ s ∈ (crysCocycles y.ρ).map (t.compLeft Γ) from hs.elim (by tauto) fun ⟨w, hw, s⟩ ↦ by
    choose k Y i hx using obeyingCocycles.exists_graph_subrepresentation _ _ hw; have := i.moduleIsTorsionFree (R := R) _ (by simp)
    use ⟨_, Y.toRepresentation.comp η⟩, .of_jointly_injective (hZ <| Prod.fst ·) (fun a ↦ ⟨⟨(·.1.1 a.1 · a.2), by tauto⟩, by tauto⟩) (by tauto) fun _ h ↦ i (by ext; apply congrFun (h (_, _))), domRestrict (snd ..) _, by tauto, (⟨_, hx · 0⟩) ∘ η, of_smul (a := (ℓ ^ m) ^ k) out
      ((_root_.funext fun _ ↦ i (by ext; simp [mul_sub, Subrepresentation.toRepresentation, ← algebraMap_smul R])).subst (coboundary_mem ⟨_, hx 1 1⟩)), s
  choose p P using Module.projective_lifting_property τ t o; subst P E; simp at q; let ψ p : (y.tensor L.tateDual).tateDual := TensorProduct.lift (dualMap p).flip
  have E g : (?_ : ℤ_[ℓ]) • ψ ?_ = GalLattice.ρ _ g (ψ p) - ψ p := by ext x l; simpa [ψ] using congr(l $((y.ρ.linHom L.ρ g p - p).codRestrictOfInjective_comp_apply (toLinearMap ..) (smul_right_injective _ out) (fun _ ↦ hτ.le (by simp [e, ← q])) x))
  exact ⟨⟨continuous_comp hj hY.isPotCrys (τ ∘ₗ p).toAddMonoidHom (C <| p ·) ha, by simp [*, apply_mul ha]⟩, _, rfl, fun _ ↦ (· y ⟨m, ψ p, f, ⟨_, of_smul out (_root_.funext E ▸ coboundary_mem _)⟩, mod_cast E⟩ hY a ha)⟩
open Finset Fintype IsLocalRing Matrix
variable {P : _} {D : Data P} {ℓ : _} [ThePrime ℓ] [PadicIso ℓ] {n : Type} [Fintype n]
lemma IsRow.n3 {t J R w} (r : IsRow D t J R) (hG : D.IsChosen w) (hℓ : w ∈ placesAboveG D \ placesDividing _ ℓ) M (h := (Finset.finite_toSet _).subset (placesDividing_union_subset_badPlaces D ℓ)) : ∀ᶠ O : CoeffRing ℓ in .atTop, ∃ u : _ →* Matrix n n O, ∃ γ β, IsLatticeIn R u ∧ O.normLength (β + ∑ b, IsDiscreteValuationRing.addVal _ (u (idOrConjInv b w.isPlaceOver_placeOver.tameGenerator) - 1).det)
  ≤ 10 * D.f * Fintype.card n * crudeUnit ℓ D ∧ IsBalanced ℓ h.toFinset u (crysRels u) γ β M := by
  filter_upwards [r.span_and_scalar, eventually_exists_isLatticeIn r.continuous] with O hs ⟨u, hu⟩
  obtain ⟨⟨hs, g, l, α, c, hg⟩, ⟨Φ, I, f, d⟩, ⟨i⟩, S, ⟨⟨a, b⟩⟩, h2, g₀, o, y, q, hy⟩ := hs u hu, hu.exists_algHom, card_pos_iff.1 r.2.1.1, Set.union_sdiff_left ▸ h.sdiff, r.2, sum_mono r.card_neg_le, r.5
  cases by simpa [q] using congr($(hu.choose_spec g₀) i i)
  replace q : u _ = u _ .. • 1 := I (by simpa [f])
  have Y j h := (O.isUnit_iff_norm_eq_one (_ ^ j - 1)).2 (by simpa using hy 0 j h)
  choose! γ m Z F G H using (r.inertia_above_g · · (FinPlace.isPlaceOver_placeOver _))
  simp_rw [← f, ← map_one Φ, ← map_sub, d, ← S.mem_toFinset] at *; choose L K using (k1 · r.1 r hu)
  have C {g y} (e : u g = y • 1) : IsUnit y ∧ u (conjGal g)⁻¹ = (cycInv ℓ _ O g⁻¹ ^ (t - 1) * y) • 1 := ⟨by simpa [e, Nat.ne_of_gt a] using isUnits_det_units (u.toHomUnits g), (by exact fun _ _ ↦ ext_iff_trace_mul_left.2 ∘ DFunLike.ext_iff.1 : (traceLinearMap .. ∘ₗ mulRight O ·).Injective)
    (ext_on_range hs fun k ↦ by ext; simp [cycInv, e, by simpa [↓← hu.trace_eq] using And.intro (r.trace_conj (conjGal k * g⁻¹)) (r.trace_conj (conjGal k))]; ring)⟩
  refine ⟨u, _, _, hu, ?_, (isOpen_discrete · |>.preimage ((hu.continuous r.continuous).matrix_map continuous_quot_mk)), fun _ ↦ hu.eq_one ∘ r.eq_one_of_mem_inertiaAbove _ ∘ by simp, hs, ⟨by simpa, _, ⟨by simp [C q, cycInv, cycChar_eq_one_of_mem_inertiaAbove (o.imp fun _ ↦ .imp_left (·.2))], q⟩, by simpa [sq, mul_self_sub_one] using Y 2⟩, orderOf_le_card.trans_lt' (by
    simpa using (Y _ ⟨((C q).1.map (residue O)).isOfFinOrder.orderOf_pos, ·⟩ |>.map (residue O))), fun x b ↦ Quotient.induction_on_pi b fun b ↦ by simpa [s23_c6, entrywise] using! (fun v _ ↦ comp_mem_obeying (Z := ZfAt _ u) _ (crysCocycles.coboundary_mem b)), _, _, _, ⟨hg, (C hg).2⟩, fun x hx ↦ by
    grw [iInf_le _ ⟨_, FinPlace.isPlaceOver_placeOver _⟩, (by simp [← Finset.coe_inj] : h.toFinset = (placesDividing _ ℓ).toFinset ∪ S.toFinset), sum_union (by simp [Finset.disjoint_right]), ← sum_set_coe]
    refine .trans (add_le_add_three (sum_le_sum fun v _ ↦ .trans (length_mono (by
     rintro _ ⟨_, h, ⟨⟩⟩; simp [mem_selmerModule_iff, s23_c6] at h; tauto)) (length_obeying_relationsOn_le (crysCocycles.fg (K _).isPotCrys) i)) (sum_le_sum fun v c ↦ have p := v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 (S.mem_toFinset.1 c).2; length_localCocycles_le (nsmul_quot_eq_zero hx) v.isPlaceOver_placeOver (hu.eq_one ∘ G v c ·) (((r.local_conditions v (·.1) v.isPlaceOver_placeOver).1.1 p).mono fun _ ↦ (hu.eq_one ∘ ·)) (γ v) (by simp [*])) le_rfl) ?_
    simp_rw [← sum_mul, m7 (localChart ..).inducesPlace.2 (K _).isPotCrys (L _), ← Nat.cast_sum, sum_add_distrib]
    simp [NumberField.Embeddings.card, finrank_eq_two_mul_card_infinitePlace, ← two_mul, mul_assoc, star_involutive.bijective.sum_comp (J · |>.countP (· < 0))] at h2
    grw [s23_f4, h2, length_ker_le_addVal_det, ← add_assoc, add_assoc]
    gcongr; simp [Finset.disjoint_right]; ring; rfl⟩
  simp [-univ_bool, ← Z w hℓ hG]
  grw [H w hℓ, sum_le_sum (by exact (H · · true)), sum_const, card_le_of_subset_placesAboveG, ellVal_le_ellVal, ellVal_le_crudeUnit D ℓ l ⟨mul_pos a (t - 1).succ_pos, mul_le_mul' b (D.t_odd.rec (by omega))⟩] <;> simp [← add_mul, cycInv, c, ← mul_assoc, pow_succ', ← one_sub_mul, pow_mul, norm_sub_rev, (O.isUnit_iff_norm_eq_one _).1 (C hg).1]
  gcongr; norm_cast; nlinarith [D.f.pos_of_neZero]
end
section
open LinearMap Module Finset
variable {ℓ} [ThePrime ℓ] {E J : Type} [Field E] [UnramCMField E] {O : CoeffRing ℓ}
attribute [local simp] tateTwist cycInv sub_smul funext_iff idOrConjInv eq_neg_iff_add_eq_zero
lemma s23_m2 {e S ν c} (he : e ≠ 0) (h : c ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ ∪ .conjClosure S) ∅ _ ⊓ .pi (shaLocalSet ℓ E e) ⊥) : c + c ∘ conjGal ∈ s23_m5 O S ν e := by
  simp_all [s23_m5, mem_selmerModule_iff, add_add_add_comm _ (_ • _), shaLocalSet, obeying]
  exact h.elim fun ⟨_, u, l⟩ h ↦ ⟨⟨fun _ ⟨_, _, _, b, c⟩ ↦ u _ ⟨_, by aesop, _, b.conjPlace_star, c.conjPlace_conjGal⟩, l.add (l.comp_continuous (by fun_prop))⟩, by simp [add_comm], by
    intros; simp [*, h _ ‹_›, h _ _ _ (decompGroup.map cmConj_conjGal_smul ‹_›), ↓val_comap_lt_one]⟩
lemma g9 [Fintype J] [LinearOrder J] {ν w τ φ t γ h c} {e : Fin t} {ty : J →o _} (tri : IsPrimeTriangle ν w τ φ γ t ty h c) {Z : Submodule O _} (N : Z ≤ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ ∪ .conjClosure (.range w)) ∅ (QuotSpan (ℓ ^ ν : ↑O))) (H : ∀ c ∈ Z, ∀ m, (∀ g, c g = (cycInv ℓ E O g ^ e.1 - 1) • m) → ∀ g, (cycInv ℓ E O γ ^ e.1 - 1) • c g = 0) {b} (hb : relLength Z (obeying (crysRels (tateTwist ℓ E O e)) _) + length O (shaOdd ℓ E O e ν) ≤ b) : s23_f3 Z (s23_q1 τ) (s23_q1 φ) {j | (ty j).1 = e} (ℓ ^ h) b := have C {z} k := (mem_selmerModule_iff.1 (@N z k)).1
  have F j := by simpa using (tri.isNewPlaces.v7 O (j, false)).imp_right (smul_quot_eq_zero_of_dvd <| · e)
  ⟨shaLocalSet ℓ E e, fun j hj z k ↦ by
    cases (mem_filter.1 hj).2
    simpa [F, cocycle_apply_inv (C k.1), ← Nat.cast_smul_eq_nsmul O] using tri.step O j _ (s23_m2 (ty j).2.ne' ⟨N k.1, k.2⟩), fun S hS a ↦ have K {z} k := tri.isNewPlaces.z4 (N (hS k).1) (a z k).1 .rfl
  hb.trans' (add_le_add (relLength_le_of_inj 1 (by simp) fun _ k l g ⟨_, h, a⟩ ↦ by
    let ⟨v, p⟩ := exists_isPlaceOver_of_val_ne_one E NeZero.out h.ne
    let ⟨x, n⟩ := p.exists_smul Gal(Ω/E) v.isPlaceOver_placeOver
    split_ifs at a with i <;> have d := n ▸ conj_mem_decompGroup_smul a.1 <;> simpa [← mul_assoc, C k g, a, i, by simpa using mem_obeying.1 l _ ⟨_, ⟨⟨v, p.valuation_natCast_lt_one_iff.1 h⟩, rfl⟩, .single ⟨_, d⟩ 1, fun z y ↦ by simp [crysCocycles.apply_eq_zero_of_cyclotomicGp (𝒥 := _) (s23_n5 e) y (s := ⟨_, d⟩) (ext (by simp [*])) fun c ↦ (localChart ..).isWeilPair_zero_iff.2 (n ▸ IsFrob.conj (by tauto) x :)], rfl⟩] using C k x⁻¹ (x * g * x⁻¹)) ((relLength_bot _).le.trans' (if n : e.1 = 0 then relLength_mono (fun z k ↦ ⟨⟨(hS k).2, by simp [n]⟩, K k⟩) bot_le else have A {z} k := s23_m2 (S := ∅) n ⟨selmerModule_mono (@K z k) .rfl, (hS k).2⟩; (tri.coboundary O ⟨e, by omega⟩).elim fun D L ↦ D.elim fun q t ↦ relLength_le_of_inj (funLeft _ _ conjGal - 1) (fun z k ↦ ⟨⟨sub_mem ((add_mem_cancel_left (hS k).2).1 (by simpa [shaLocalSet, n] using (A k).2.2)) (hS k).2, by simp⟩, sub_mem ((add_mem_cancel_left (K k)).1 (selmerModule_mono (A k).1 .rfl)) (K k)⟩) fun z k v ↦ funext fun g ↦ by linear_combination (norm := (simp [-funext_iff]; module)) q • H _ (hS (S.smul_mem _ (by simp [add_mem, k]))).1 _ ((sub_eq_zero.1 v : _ ∘ _ = z) ▸ L _ (A k) (by simpa [cocycle_apply_inv (C (hS k).1), F, Subtype.ext_iff] using (a z k).2)) g + t • z g)))⟩
end
section
open Module CoeffRing ENNReal Filter Finset Fintype Function Lift Matrix NeZero NumberField Polynomial Matrix.Module
attribute [-instance] NormedAlgebra.toAlgebra Subalgebra.isScalarTower_left
attribute [-simp] IsUnit.dvd length_eq_zero
noncomputable def t2 {P} (D : Data P) ℓ := D.h₂ ^ 27 * (crudeUnit ℓ D + padicValNat ℓ (exists_length_shaOdd_le _ D.t _ D.z9).choose) + 4 * D.f * loss D ℓ
variable {ℓ} [ThePrime ℓ] {P} {D : Data P} {K Y n r : Type} [Fintype n] [Fintype r] {t ν : ℕ} {w} {τ φ : K → AbsGal D} {u : Y → GalRep ℓ D.E n} {O : CoeffRing ℓ}
lemma obeyingCocycles.mem_selmerModule [Fintype Y] {u : Y → AbsGal D →* Matrix n n O} (hc : ∀ x, Continuous (u x)) {S} (hS : ∀ g ∈ inertiaAbove Sᶜ, ∀ x, u x g = 1) {ρ : _ →* Matrix r r O} {b c L} (h : c ∈ obeyingCocycles u ρ b) [NeZero b] (l : c ∈ obeying L _) : c ∈ selmerModule ρ S L _ := by choose k _ p H using exists_graph_subrepresentation u _ h; refine mem_selmerModule_iff.2 ⟨mem_obeying_cocycleRels.1 h.1, fun g k ↦ congr($(@p ⟨_, H g 0⟩ 0 (by ext; simp [*])).1.2), l, (IsLocallyConstant.iff_exists_open _).2 fun g ↦ ⟨_, (continuous_pi (hc · |>.matrix_map (Ideal.span {b ^ k}).continuous_mkQ)).1 {_} (by simp), rfl, fun h K ↦ ?_⟩⟩; choose w hw using (Ideal.mk_span_eq_iff_dvd_sub.1 congr($K · · ·)); exact congr($(@p ⟨_, H h 0⟩ ⟨_, H g (of ∘ w)⟩ (by ext; simp [← hw])).1.2)
lemma s23_h9 (hw : s23_q3 ν w τ φ) {S 𝒥 e} (hu : ∀ x, IsConjSelfDual t (u x)) (h : IsTraceIdeal (S := S) (L := PadicAlgCl ℓ) 𝒥 (u · · |>.1) (ℓ ^ ν : ↑O) τ φ id e) : IsTraceIdeal 𝒥 (u · · |>.1) (ℓ ^ ν) (s23_q1 τ) (s23_q1 φ) (·.1) e := h.imp_right (.imp_right fun k g ↦ (k g).imp_right fun a (j, b) ↦ b.rec (by
  have H h i x : (u x (s23_q1 h (j, false) ^ i * g)).1.trace = cycInv ℓ _ O (s23_q1 h (j, false) ^ i * g) ^ (t - 1) • (u x (h j ^ i * (conjGal g)⁻¹)).1.trace := by simpa [idOrConjInv, cycInv, trace_mul_comm _⁻¹, O.1.smul_def] using (hu x).trace_conj ((h j)⁻¹ ^ i * conjGal g)
  choose d hd using (hw.v7 O (j, false)).2
  convert 𝒥.smul_of_tower_mem (cycInv ℓ _ O g ^ (t - 1))
    (sub_mem ((k (conjGal g)⁻¹).2 j) (𝒥.smul_mem ⟨_, h.1 j⟩ (sum_mem fun i _ ↦ 𝒥.smul_of_tower_mem (d ((t - 1) * i) * ((X - 1) * e j).coeff i) (k (φ j ^ i * (conjGal g)⁻¹)).1)))
  simp [*, Subalgebra.smul_def, ↓aeval_eq_sum_range, sum_mul, sub_mul, mul_sum, mul_sub, eq_add_of_sub_eq' (hd _), sub_sub, add_mul, mul_add, MvPolynomial.smul_eq_C_mul, by simpa [hw.v7, mul_pow, ← pow_mul'] using And.intro H (H τ <| Bool.toNat ·)]; ac_rfl) (a j))
variable [Fintype Y] [PadicIso ℓ] {V : AuxPair D.E r n} {c ϑ} (hc : IsApt V c ϑ)
private lemma ft_r8 (hc : IsApt V c ϑ) {τ τ' S R} {R' : Y → _} (hT : IsRow D t τ R) (hC : ∀ x, IsLabelledColumn V t τ' (twistedLabel V c · * (X - 1) ^ t) S (R' x)) (ϵ : Sigma (@RowBlockIndex r t) ≃ n) π : ∀ᶠ O : CoeffRing ℓ in atTop, ∀ T {T₀} (u : Y → _ →* Matrix n n O) (M : Option (Fin t) → ℕ), (∀ g, u π g = reindex ϵ ϵ (blockDiagonal' (blockRep T · g))) → (∀ x, IsLatticeIn (R' x) (u x)) → IsLatticeIn R T₀ → (∀ v : placesDividing D.E ℓ, T.comp (decompGroup _ (placeOver v.1)).subtype = T₀.comp (Subgroup.subtype _)) → ∑ i, O.normLength (s7 (blockRep T i) u (M i)) ≤ 4 * card r * D.f * loss D ℓ := by
  have he v := (localChart ℓ D.E v).inducesPlace.2
  filter_upwards [Eventually.all (ft_j1 hT.2 <| he ·)] with O h T _ u M hπ Z Y H
  simp_rw [s7, s23_c6]; let L H i := s23_d1 ((blockRep (t := t) T i).comp (Subgroup.subtype H)); let f := .funCongrLeft O O ϵ ≪≫ₗ .piCurry _ fun _ _ ↦ _; have hf H i g x : f (u π g.1 *ᵥ x) i = (L H i).ρ g (f x i) := by simp +zetaDelta [funext_iff, hπ, mulVec_apply_eq_sum, reindex_equiv ϵ, Fintype.sum_sigma, blockDiagonal'_apply', Sigma.curry]
  have hu v x := k1 v (hC x).1 (hC x) (Z x)
  have S v i := InClass.of_jointly_injective (fun _ ↦ (hu v π).2) (fun () ↦ f.symm ∘ₗ .single _ (L _ ·) i)
    (by simp [f.symm_apply_eq, funext_iff, hf, (Pi.apply_single fun i ↦ (L _ i).ρ ·)]) (by simp)
  grw (transparency := default) [relLength_iInf_le, (map_sum ..).le, s23_d8 (he _).1 (hu _ · |>.2) _ (S ..), fun v i ↦ h v ((em (v.1 ∈ placesAboveG D)).imp (·.imp fun k b ↦ by
    cases (v.1.charP_quotient b).eq _ (v.1.charP_quotient v.2); use rfl, fun s w ↦ ((s23_v6 n hc b v.1.isPlaceOver_placeOver _).choose_spec.2 _ ((localChart ..).isWeilPair_zero_iff.1 w)).elim fun μ H ↦ n7 (by grw [H.1, hc.rank_le.1, hT.t_le]) (H.2.1 · · |>.2.2) fun _ _ ↦ ⟨⟨k, b⟩, fun _ N ↦ ⟨_, (H.2.2 N).1, by simpa [eval_multiset_prod]⟩⟩) (by simp [·, funext_iff])) (fun g a this ↦ exists_jump_of_jointly_injective (S v · |>.isPotCrys) (.proj · ∘ₗ f.1) (hf _) (by simp [← funext_iff, ← Pi.zero_def]) (surjInv_eq s23_w8 g ▸ ((hu v π).1 ..).trans_ne (by simpa))) (Option.rec (H v ▸ k1 v hT.1 hT Y).1 fun c _ _ ↦ by rw [hasJumps_of_cyclotomicGp_zpow _ (s23_n5 _), finrank_pi]; simp!) (finrank_pi _) i (S ..)]
  simp! [L, (he _).p5, ← sum_mul]; simp_rw [Finset.card_eq_sum_ones]; norm_cast; grw [s23_f4, hT.t_le.trans (le_mul_of_one_le_left' hT.rank_mem.1)]; have := D.t_odd.pos.ne'; simp [Embeddings.card, finrank_eq_two_mul_card_infinitePlace, field]; linarith
lemma s6 (hc : IsApt V c ϑ) {J' ψ Q} (hq : s23_g7 (badPlaces D ℓ) Q ψ (crudeUnit ℓ D)) [Fintype K] [LinearOrder K] {ty a h} (hh : h ≤ padicValNat ℓ D.chosenGroupOrder) (tri : IsPrimeTriangle ν w τ φ a V.rankDiff ty (D.h₂ * h) (D.h₂ ^ 22 * h)) (S : Subalgebra (intQpBar ℓ) (Y → MvPolynomial K (PadicAlgCl ℓ))) (hu : ∀ x, IsLabelledColumn V V.rankDiff J' (twistedLabel V c · * (X - 1) ^ V.rankDiff) (.conjClosure Q ∪ (Set.range w).conjClosure) (u x) ∧ ∀ g ∈ inertiaAbove (.conjClosure Q), ((u x g).1 - ψ g • 1) * ((u x g).1 - 1) = 0) {𝓧 : Set Y} {J R γ y : 𝓧 → _} {m₀} (hm : ⌊D.r * t2 D ℓ⌋₊ < m₀) (hR : ∀ x, IsRow (n := r) D V.rankDiff (J x) (R x) ∧ SelmerLengthLe ψ (R x) Q m₀ (γ x) (y x)) (hl' : ∀ (x : 𝓧) g, (u x g).1.trace = ψ g * (R x g).1.trace + ∑ e ∈ range V.rankDiff, cycInv ℓ _ _ g ^ e) {𝒥 e} (h𝒥 : IsTraceIdeal (S := S) 𝒥 (u · · |>.1) (ℓ ^ ν) τ φ id e) (he' : ∀ j, (e j).eval 1 = 1) π θ : ∃ d, IsRibetElement 𝒥 (fun x ↦ ((s23_q7 (γ π) a (y π) (ℓ ^ (m₀ + D.h₂ * h)) θ).linearCombination (intQpBar ℓ) fun g ↦ (u x g).1 - 1).det) π d ∧ @ellVal ℓ _ (D.chosenGroupOrder ^ 3 * d) ≤ card r * t2 D ℓ := by
  obtain ⟨⟨-, hψ, σ, hq⟩, ⟨hJ⟩, ⟨s, hs, hr⟩, ⟨od, -, odd⟩, o, hG, ϵ⟩ := hq, hR π, tri.detect, (exists_length_shaOdd_le _ D.t _ D.z9).choose_spec, of_pos hc.odd.2.pos, ((finite_toSet _).subset (placesDividing_union_subset_badPlaces D ℓ)).sdiff (t := placesDividing _ ℓ), (equivOfCardEq (by simp! [V.rank_lt.le]) : Sigma (@RowBlockIndex r V.rankDiff) ≃ n); let z := σ ⊕ᵥ fun v : hG.toFinset ↦ v.1.isPlaceOver_placeOver.tameGenerator; have N : s23_q3 0 (_ ⊕ᵥ _) z 1 := Sum.rec hq.1 (⟨hG.mem_toFinset.1 ·.2 |>.2, map_one _, _, _, rfl⟩); have M k {S} h : s23_q1 z k ∈ inertiaAbove S := (N k.1).2.2.elim fun _ ⟨a, e⟩ ↦ s23_z6 a (e ▸ a.tameGenerator.2) h _; choose O' l hL ζ η hR' R₀ ψ' y' ey hl hψ' e₀ hy c₀ hS using ((ft_r8 hc hJ (hu · |>.1) ϵ π).and (.and (.all (eventually_exists_isLatticeIn <| hu · |>.1.continuous)) ((eventually_primitiveRoot (Monoid.exponent (ZMod D.cycloConductor)ˣ)).and (.and (.all (e · |>.finite_range_coeff.eventually_all.2 fun a _ ↦ eventually_mem a.2)) (.all (hR · |>.elim (·.span_and_scalar.and ·))))))).exists; choose η hε using fun j ↦ (mem_lifts ((e j).map (intQpBar ℓ).subtype)).1 ((mem_map_rangeS (algebraMap O' _)).2 (⟨⟨_, η j _ ⟨·, rfl⟩⟩, by simp⟩)); let T x := twistRep (.id _) (ψ' x) (R₀ x); have p1 {g} (h : ψ g = 1) : T π g = R₀ π g := by ext; simp [*, T, twistRep]
  have sp x := Basis.units_smul_span_eq_top (w := (ψ' x).toHomUnits) (hR' x _ (hl x)).1; let Φ R [CommRing R] := (reindexAlgEquiv R R ϵ).toAlgHom.comp blockDiagonalAlgHom; have B x (e : Fin V.rankDiff) g : Eq (blockRep (T x) (some e) g) fun _ _ ↦ cycInv ℓ _ O' g ^ e.1 := funext₂ fun _ _ ↦ ite_eq_left rfl
  choose u' hL hB using fun x ↦ show ∃ v, IsLatticeIn (u x) v ∧ ∀ h g, v g = Φ _
    (blockRep (T ⟨x, h⟩) · g) from if h : x ∈ 𝓧 then ⟨(Φ _).1.1.comp (.pi _), .imp (fun Z c g ↦ by
    simp [c, mul_assoc, Φ, ← submatrix_map, blockDiagonal'_map]; rfl) ((hu x).1.nondeg.exists_conj_of_trace_eq (.pi (O'.1.val.mapMatrix.1.1.comp <| blockRep (T ⟨x, h⟩) ·)) (Φ _) (fun y _ H ↦ by
    ext (_ | e) a b; simpa [mul_apply, single_apply, ite_and] using congrFun₂ (LinearMap.congr_fun (LinearMap.ext_on_range (g := 0) (f := .mulLeftRight _ (y _, y _) ∘ₗ (Algebra.linearMap O' _).mapMatrix) (sp _) (congr($(H ·) _))) (.single b a 1)) a b
    with_unfolding_all simpa using! (sum_singleton _ a).symm.trans congr($(H 1) _ a a)) fun g ↦ by
    simp [↓hl' ⟨x, h⟩, ↓← (hl _).trace_eq, ← hψ' ⟨x, h⟩, Φ, trace, sum_range, mul_sum, reindex_equiv ϵ, Fintype.sum_sigma, B, cycInv]; simp!; rfl), fun _ _ ↦ rfl⟩ else (hL x).imp (by tauto)
  choose F I f d tr using (hL · |>.exists_algHom); have hC x := (hL x).continuous (hu x).1.continuous; have U g h x := (hL x).eq_one ((hu x).1.eq_one_of_mem_inertiaAbove g h)
  refine (r5 (S := ⟨_, (S.2 ⟨·, norm_le_one _⟩)⟩) u' 𝒥 (.trans ⟨(⟨none, ·⟩) ⊕ᵥ (⟨some
    ·, ()⟩), (·.rec (·.rec .inl fun e _ ↦ .inr e)), by rintro ⟨⟩ <;> rfl, by rintro ⟨⟨⟩⟩ <;> rfl⟩ ϵ) π T (by simp) (fun x g ↦ (reindex ..).symm_apply_eq.1 (by ext1 ⟨⟩ ⟨⟩ <;> simp [hB, Φ, blockDiagonal', B] <;> rfl)) (sp π) e₀ hy (by simp [cycInv, c₀]) out (by
    simpa [IsTraceIdeal, ↓(hL _).charpoly_eq_map, ← f, aeval_algHom_apply (F _), ← map_mul, sub_mul, tr, O'.1.smul_def] using s23_h9 tri.isNewPlaces (e := η) (hu · |>.1.1.1) (by
      simpa [IsTraceIdeal, hε, ← aeval_map_algebraMap (PadicAlgCl ℓ)] using! h𝒥)) (fun e k ↦ by
    simpa [by simpa [eval_map, he'] using (congr(Polynomial.eval 1 $(hε ·)))]
      using ((tri.isNewPlaces.v7 ..).2 e).trans (sub_dvd_eval_sub _ 1 (η _))) _ (by simpa [cycInv] using (map_dvd (algebraMap _ O') <| tri.prod_dvd ·)) ⟨(ty ·), ty.2⟩ out (.trans (by
    simp [s23_q7, Finsupp.linearCombination_apply ℕ, Finsupp.sum, f, pow_add, ey, O'.1.smul_def]; rfl) <| d · _) (le_self_add.trans_lt (O'.normLength_mono.reflect_lt ((le_add_self.trans ?H).trans_lt (by grw [hJ.rank_mem.2]; simpa using mod_cast Nat.lt_of_floor_lt hm)))) ((relLength_add_length_inf _ (obeying (crysRels (T π)) _)).ge.trans (add_le_add (relLength_mono (fun _ ↦ (·.1.1)) le_rfl) (length_mono (T := _ ⊓ _) fun c k ↦ ⟨tri.isNewPlaces.z4 (obeyingCocycles.mem_selmerModule hC U k.1.1.1 k.2) (k.1.1.2 _ ⟨·, rfl⟩) (Set.union_assoc ..).ge fun g ⟨v, hv, H⟩ _ ↦ (p1 (hψ.eq_one_of_mem_inertiaAbove g ⟨v, mt .inr hv, H⟩)).trans ((hl π).eq_one (hJ.eq_one_of_mem_inertiaAbove g ⟨v, mt (.imp_right nofun) hv, H⟩)), k.1.2⟩))) (o := fun k ↦ ite k.1.isLeft (C (ψ' π (s23_q1 z k)) - X) (∑ i ∈ range D.chosenGroupOrder, X ^ i)) (by simp [N.v7]) (by
    rintro ⟨j | j, b⟩ x <;> apply I x; simpa [f, ← hψ' π, Algebra.smul_def, ← neg_mul] using! congr(-$((hu x).2 _ (M _ (by simp)))); have ⟨v, ⟨⟨i, b⟩, l⟩, A, a, s⟩ := @M (.inr j, b) (placesAboveG D \ placesDividing _ ℓ) (by simpa using j.2); have ⟨μ, _, Z, P⟩ := (s23_v6 n hc b a V.rankDiff).choose_spec.2 _ s
    convert ((hu x).1.local_conditions v (·.2 (.inr ⟨i, b⟩)) a).1.aeval_eq_zero_of_roots
      (a.valuation_natCast_eq_one_iff.2 l) s (P (hu x).1).1
      (X ^ D.chosenGroupOrder - 1) _ <;> simp [f, geom_sum_mul, eval_multiset_prod]
    exact (Z · · |>.2.2.elim fun d ⟨a, h⟩ ↦ (g_pow_sub_one_dvd_chosenGroupOrder D (a.imp_right D.nat_le_of_hasLogBound.trans')).choose_spec ▸ by rw [pow_mul, h, one_pow])) (s := s ∪ image (s23_q1 τ) univ) fun e Z H ↦ (fun N ↦ ⟨g9 tri N (H · · |>.2.2) (add_le_add (relLength_mono (H · · |>.1) le_rfl) (odd ℓ _ ⟨ζ, inferInstance⟩ e (e.2.trans_le hJ.t_le) ν)), fun c k b ↦ hr _ e c (tri.isNewPlaces.z4 (N c k) (by simp [b])) (by simp +contextual
    [b])⟩) fun c k ↦ N.z4 (obeyingCocycles.mem_selmerModule hC U (H c k).1 (by simp [obeying])) (H c k).2.1).elim fun d k ↦ ⟨d, k.1, .trans (by
    grw [ellVal_mul_le, (normLength_addVal d).ge, k.2, card_union_le, card_image_le]) ?H⟩
  rw [← @Nat.cast_le ℝ≥0∞] at hs; simp [t2, mul_add (_ ^ 27), ellVal_natCast, ne, od, two_mul, mul_two, add_mul, hψ', sum_prod_type, hψ.apply_idOrConjInv, z, -AddValuation.map_pow, -ENat.natCast_sub, -natCast_sub] at hs hq ⊢; grw [hS, hJ.rank_mem.2, mul_add (card r : ℝ≥0∞), ← le_mul_of_one_le_left' (mod_cast hJ.rank_mem.1), hq.2, card_le_of_subset_placesAboveG D (by simp), le_self_add.trans hs, le_add_self.trans hs, hh, hJ.t_le, (by simp [crudeUnit] : (padicValNat ℓ _ : ℝ≥0∞) ≤ crudeUnit ℓ D)]; exact (add_le_add (by gcongr <;> exact_mod_cast D.nat_le_of_hasLogBound) ((l _ u' (·.elim m₀ fun _ ↦ ν) (hB _ _) hL (hl π) fun v ↦ MonoidHom.ext (p1 <| hψ.eq_one_of_mem_decompGroup v.2 v.1.isPlaceOver_placeOver ·.2)).trans_eq (by ring)) : ((4 + D.t * (2 + 10 * D.f + 6 * D.h₂ ^ 22) + D.h₂ ^ 22 + D.h₂) * _ + D.t * _ + _ : ℝ≥0∞) ≤ _).trans_eq' (by simp only [sum_option, Data.t]; push_cast; ring1!)
end
section
private lemma ft_m6 {ℓ} [ThePrime ℓ] {E} [Field E] [UnramCMField E] {O S r e b c} (k : c ∈ s23_m5 (E := E) O S r e) (h : ∀ u : _ →+ ZMod (ℓ ^ r), (u <| c ·) ∈ Z1 (charRep _ (cycCharMod Ω (ℓ ^ r) ^ e)⁻¹) → u b = 0) : b = 0 := QZ.eq_zero_of_forall_hom_eq_zero ((QZ.bijective_ofZMod_comp (funext <| nsmul_quot_eq_zero ∘' ·)).2.forall.2 fun u ↦ by simp [h u ⟨(k.1.2.comp _).continuous, by simp [tateTwist, cycInv, charRep, CharP.cast_eq_zero, ↓← map_pow, ← map_inv, mem_selmerModule_iff.1 k.1, map_cycChar_smul u r]⟩])
open Classical Finset Function NumberField selmerZ1 Subgroup IsCMField
variable {ℓ} [ThePrime ℓ] {E : Type} [Field E] [UnramCMField E] (r : ℕ) (w : FinPlace E)
def s23_n0 (x : FrobeniusDatum E) := ↑ℓ ∉ x.w.1 ∧ cycCharMod Ω (ℓ ^ r) x.frob = 1
private noncomputable abbrev z3 := w.below (maximalRealSubfield E)
structure IsLaw e (Φ : Set _) (T : Finset _) (z : Gal(Ω/E) → ZMod (ℓ ^ r)) where
  isLocallyConstant : IsLocallyConstant z
  map_conj_mul g a b : cycCharMod Ω (ℓ ^ r) a = 1 → cycCharMod Ω (ℓ ^ r) b = 1 →
    z (g * a * g⁻¹ * b) = cycCharMod Ω (ℓ ^ r) g ^ (e + 1) * z a + z b
  odd b : cycCharMod Ω (ℓ ^ r) b = 1 → z (conjGal b) = -z b
  reciprocity {J : Type} [Fintype J] (x : J → _) : Injective (z3 <| x · |>.w) → (∀ j,
    s23_n0 r (x j) ∧ z3 (x j).w ∉ T) → ∀ j, (∀ i ≠ j, z (x i).frob = 0) → ∀ O,
    ∀ c ∈ s23_m5 O (.range (x · |>.w)) r e,
    (∀ g ∈ Φ, c g = 0) → ∀ n : ℕ, 2 * z (x j).frob ∣ n → n • c (x j).isPlaceOver.tameGenerator = 0
lemma s23_f5 : z3 (star w) = z3 w := by ext x; exact congr($(Subtype.ext (mem_maximalRealSubfield_iff_star_eq.1 x.1.2)) ∈ w.1)
lemma s8 {r} e (hr : 0 < r) (hf : 4 ≤ Fintype.card (InfinitePlace E)) {I k} [Fintype I] (hI : k ≤ Fintype.card I) {x : I → FrobeniusDatum E} (hx : ∀ i, s23_n0 r (x i)) (i : Injective (z3 <| x · |>.w)) (y : Fin k → _) : ∃ z T, IsLaw r e (.range (x · |>.frob)) T z ∧ (∀ i, z (y i) = 0) ∧ ∃ g, IsUnit (z g) ∧ cycCharMod Ω (ℓ ^ r) g = 1 := by
  let K := maximalRealSubfield E; let res : Gal(Ω/E) →* _ := AlgEquiv.restrictScalarsHom (maximalRealSubfield E); let c₀ : Gal(Ω/maximalRealSubfield E) := {cmConj with commutes' x := (mem_maximalRealSubfield_iff_star_eq.1 x.2 ▸ cmConj_algebraMap x.1 :)}; obtain ⟨⟨⟨⟨ce, ij⟩, _⟩, -, ix⟩, cs : IsComplexConj c₀, -, op⟩ := (@is_quadratic E _ _ _).2 ▸ isClosedEmbedding_galois_restrict res, isComplexConj_cmConj, isOpenEmbedding_galois_restrict res (by tauto)
  have N c (h : IsComplexConj c) :
    c ∉ res.range | ⟨s, e⟩ => (e ▸ h).false_of_isTotallyComplex (c := s)
  choose p o using fun σ ↦ show ite (σ ∈ res.range) σ (σ * c₀) ∈ res.range by
    split <;> simp [mul_mem_iff_of_index_two, *]
  obtain ⟨cp, _, p1⟩ := ce.continuous_iff.2 ((continuous_congr o).2 (continuous_id.if (op.frontier_eq ▸ by simp) (by fun_prop))), normal_of_index_eq_two ix, (ij <| (o _).trans <| ite_eq_left ⟨·, rfl⟩)
  have μ g h : p (g * h) = p g * p h ∨ p (g * h) = p g * conjGal (p h) := by simp only [← ij.eq_iff, map_mul, mul_mem_iff_of_index_two, *, show res (conjGal (p h)) = c₀ * res _ * c₀ from rfl]; grind [cs.mul_self]
  have u W g : g ∈ inertiaAbove W → p g ∈ inertiaAbove (z3 ⁻¹' W) := fun ⟨v, a, A, hA, h⟩ ↦ by
    obtain ⟨⟨w, hw, rfl⟩, e⟩ := hA.exists_above (L := E), o g; split at e; exact ⟨w, a, A, hw, (e ▸ h :)⟩
    cases StablyUnram.exists_isUnit_sub_star.elim fun y u ↦ w.1.notMem_of_isUnit u ((hw _).1 (by
      simpa [← (by simpa [res, c₀] using congr($e (algebraMap E Ω y)) :)] using h.2 _ (A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A (star y)⟩)))
  let κ := MonoidHom.mk' (cycChar Ω ℓ ∘ p) (by cases μ · · <;> simp [*]); have hu g h : κ g = 1 := cycChar_eq_one_of_mem_inertiaAbove (by simpa using! u (placesDividing _ ℓ)ᶜ g h); let ρ := (Units.map (PadicInt.toZModPow r).1).comp κ; let V := OpenNormalSubgroup.mk ⟨res.range ⊓ (cycCharMod Ω (ℓ ^ r)).ker, op.inter isOpen_ker_cycCharMod.1⟩; have U s (h : cycCharMod Ω (ℓ ^ r) s = 1) : res s⁻¹ ∈ V := ⟨⟨_, rfl⟩, by simpa⟩; have v : V ≤ ρ.ker | _, ⟨⟨s, rfl⟩, h⟩ => by simpa [ρ, κ, *, cycCharMod_prime_pow_eq] using! h
  have D (x : FrobeniusDatum E) : IsFrob x.valRing (z3 x.w).q (res x.frob⁻¹) := ((x.prime_q.pow_eq_iff.1 ((z3 x.w).1.absNorm_pow_inertiaDeg _)).1 ▸ x.isFrob :)
  obtain ⟨⟨S, hS⟩, hm, l, w⟩ := (placesDividing _ ℓ ∪ .range (z3 <| x
    · |>.w)).toFinite.exists_finset, dvd_pow_self ℓ hr.ne', @NeZero.one_le ℓ _, isOpen_mono v V.1.2
  choose P hP η Φ using fun u : FinPlace _ ↦ show ∃ A, IsPlaceOver A u ∧ (u ∈ S → u ∉ placesDividing _ ℓ → ∃ i, IsFrob A u.q (res (x i).frob⁻¹)) from if h : ∃ i, z3 (x i).w =
    u then h.rec fun i e ↦ e ▸ ⟨_, (x i).isPlaceOver.isPlaceOver_below, by tauto⟩ else ⟨_, u.isPlaceOver_placeOver, by simp +contextual [*]⟩
  let M := DiscreteModule.of (charRep (ZMod (ℓ ^ r)) (ρ ^ e)⁻¹)
    (((Continuous.of_isOpen_ker _ w).pow e).inv.fst'.smul continuous_snd)
  generalize m : M = A; have t {g} (h : ρ g = 1) : A.ρ g = 1 := m ▸ by ext; simp [M, charRep, h]
  have t' {g} (h : κ g = 1) := @t g (by simp [ρ, h]); have L (B := A) (r : ∀ {g}, A.ρ g = 1 → B.ρ g = 1) u (h : u ∈ S) : (d0 (B.restrictTo (decompGroup _ (P u))).ρ).range ≤ .pi {g | ↑ℓ ∈ u.1 → κ g = 1} ⊥ := fun _ ⟨m, J⟩ ↦ J ▸ fun g a ↦ sub_eq_zero.2 congr($(r (if b : _ then t' (a b) else t ((hP _).decompGroup_le (Φ u h b) w (by simp [ρ, hu · ⟨u, b, _, hP u, ·⟩]) (v (U _ (hx _).2)) g.2))) m); have hu' g (h : g ∈ inertiaAbove Sᶜ) := t' (hu g (h.imp (by simp +contextual [hS])))
  have C c (h : IsComplexConj c) := t' (by simp [IsComplexConj.cycChar_eq_neg_one, *] :
    cycChar Ω ℓ (res (p c)) = 1)
  have c := exists_split_primes_relations hu' hP _ (L A id) @C A V (congr($(t <| @v · ·) ·)) (fun _ ↦ (·.2)) (N _ · ·.1)
  extract_lets Y at c
  choose q ι _ Q _ s γ π T hT hST hπ _ d H using c; let Z := (smulAddHom _ (Y (.range s.v)) ℓ).ker
  have B : .card Z * ℓ ^ (k + 1) ≤ ℓ ^ Fintype.card ι := by
    let W := A.submodule (ℓ • LinearMap.id).ker fun g a h ↦ by simpa using congr(A.ρ g $h)
    obtain ⟨_, hM⟩ : Finite W ∧ .card W = ℓ := by subst m; use inferInstance, (IsAddCyclic.card_nsmulAddMonoidHom_ker ..).trans (by simp [M, Nat.gcd_eq_right hm])
    have r {g} (h : A.ρ g = 1) : W.ρ g = 1 := by ext; simp [W, h]
    let ψ := ((DistribMulAction.toAddAut _ W).comp W.ρ.asGroupHom).prod (cycCharMod Ω ℓ)
    have u : V ≤ ψ.ker
      | _, h => Prod.ext (by ext; exact congr($(r (t (v h))) _)) (cycCharMod_eq_one_of_dvd hm h.2)
    let O := OpenNormalSubgroup.mk ⟨_, isOpen_mono u V.1.2⟩
    have G {D : Subgroup _} [IsClosed (SetLike.coe D)] := exists_procyclic_generator (κ.domRestrict D) ((continuous_cycChar ℓ).comp cp |>.comp continuous_subtype_val)
      (s23_p7 <| p ·)
    obtain ⟨γ, hγ⟩ := @G _ O.isClosed; choose v n _ B R φ Q X _ using fun g : O × _ ↦ chebotarev (V.1.2.preimage (continuous_const_mul g.1.1)) ⟨g.1⁻¹, by simp⟩ (((finite_natCast_mem q).union (Set.finite_range s.v)).insert g.2); let t := (cond · (γ, ofNonempty) (dite _ (⟨c₀, ·⟩) fun _ ↦ 1, v (γ, ofNonempty))); simp [-Prod.forall] at n
    let s' : SplitPlaces ℓ q _ O _ := ⟨fun _ h ↦ congr($h.2), hm.trans s.dvd_level, _, s.4.sumElim (Bool.injective_iff.2 (n (t _)).1) (by simp [n]), by simp [s.level_notMem, n], Sum.rec s.valRing (B ∘ t), Sum.rec s.isPlaceOver (R ∘' t), Sum.rec s.φ (φ ∘ t), Sum.rec (s.isFrob · |>.imp id (u ·))
      fun _ ↦ ⟨X _, (mul_mem_cancel_left (by simp)).1 (u (Q _))⟩, by congr!, (s.inertiaGroup_le
      · · |>.trans u), fun F _ h ↦ s.principal_sup_idelesUnitOff F (@h · · <| inclusion u ·)⟩
    have c : W.FiniteKilledFixedInj ℓ O 1 0 := ⟨‹_›, by simp [← hM], fun _ h ↦ (congr($h.1 ·)), fun _ _ ↦ by simp⟩
    have B := (card_mul_pow_le (r <| hu' · ·) hP _ (L W r) (r <| C _ ·) s' (s'.card_trivialised_of_isHigmanProjective c (c.isHigmanProjective_of_coprime (.of_dvd_right (index_ker ψ ▸ card_subgroup_dvd_card _) (by simp [← sq, l, ← Nat.card_congr (MulAutMultiplicative W).1, Nat.totient_prime Fact.out, (hM ▸ (isCyclic_of_prime_card (α := Multiplicative W) hM).card_mulAut :)]))) fun y m f ↦ by
      let F := MulAction.stabilizer Gal(Ω/K) y.toMul; have H : V ≤ F := d y (hm.choose_spec ▸ mul_nsmul y .. ▸ nsmul_mem (m.imp id (· <| inclusion u ·)) _) (f <| .inl ·); have e j := (mul_mem_cancel_right (f (.inr j))).1 (H (Q _))
      simpa using! hγ (F.subgroupOf _) (fun g (a : cycChar Ω ℓ (p g) = 1) ↦ by
        have b := o g ▸ U (p g)⁻¹ (by simp [a, cycCharMod_prime_pow_eq])
        split at b; exacts [H b, (F.mul_mem_cancel_right (by
          simpa [t, (mul_mem_cancel_left g.2).1 (u b)] using e false)).1 (H b)]) (isOpen_mono H V.1.2).preimage_val (e true)).1 hT).trans' (mul_le_mul_left (@Nat.card_le_card_of_injective Z _ ((finite_unramified_cocycles W).subset fun _ ↦ (·.1)) (fun x ↦ ⟨fun g ↦ ⟨_, congr($(x.2).1 g)⟩, x.1.2.imp (.imp (.imp (·.subtype_mk _) (Subtype.ext <| · · ·)) fun b ↦ (Subtype.ext <| b · <| ·.imp (by simp +contextual [s']))) (.imp (Subtype.ext <| · · · · ·) (Subtype.ext <| · · ·))⟩) (by simp [Injective, funext_iff])) _)
    grw [S.prod_le_prod' (g := fun v ↦ ite (↑ℓ ∉ v.1) 1 (.card W)) fun v _ ↦ ?_, hM, card_infinitePlace_eq_card_infinitePlace, ← hf, ← S.card_filter_add_card_filter_not (↑ℓ ∉
      ·.1), ← hI.trans (card_le_card_of_injOn _ ?_ i.injOn)] at B
    simpa [prod_ite, pow_add, pow_succ, ← mul_assoc, add_right_comm _ _ 4, NeZero.pos] using B; simp [hS, (hx _).1]; split; simp [Pi.bot_def, *, inf_eq_left.2]; exact G.elim fun γ hγ ↦ Nat.card_le_card_of_injective _ (.of_ker ((LinearMap.proj γ).domRestrict _) fun ⟨_, x⟩ ↦ Subtype.ext ∘ funext ∘ hγ (cocycleKer (W.restrictTo _).ρ x.2.2) (x.1 · ∘ const _) (x.2.1.1 {0} (by simp)))
  subst m
  choose n a n2 j β using exists_primitive_relation (.mk' (·.1 ∘ γ) (by bound)) (π ∘ res ∘ y⁻¹) hr B
    ((finite_unramified_cocycles M).subset inf_le_left)
  obtain ⟨α, ad, law⟩ := H (.mulRight <| n ·) (a ⟨·, ·⟩)
  exact ⟨(n <| π <| res ·⁻¹), T, ⟨(hπ.comp n).comp_continuous (by fun_prop), fun g a b h h' ↦ by
    simpa [M, charRep, ρ, ↓map_inv, κ, *, cycCharMod_prime_pow_eq, pow_succ', add_comm] using! ad (res g) _ (U b h') _ (U a h) 1, fun b h ↦ by
    simpa [by simpa using (ad 1 1 · 1 · 1), *, cs.cycCharMod_eq_neg_one, ← map_inv
      conjGal, -map_inv, inv_eq_iff_mul_eq_one.2 cs.mul_self] using! (ad c₀ 1 V.one_mem _ (U b h) 1), fun w i h j z O c Z φ _ ⟨y, b⟩ ↦ ft_m6 Z fun f ⟨l, fs⟩ ↦ by
    obtain ⟨⟨⟨h1, h2, -⟩, h3, h4⟩, F⟩ := Z.imp mem_selmerModule_iff.1 id, (w · |>.isPlaceOver.isPlaceOver_below (K := K)); choose δ hδ using exists_isTameGeneratorFor Gal(Ω/K) (ℓ ^ r) ∘' F; let X : Z1 M.ρ := ⟨_, l.comp cp, (by cases μ · · <;> simp [M, charRep, ρ, κ, *, -h1, cycCharMod_prime_pow_eq])⟩
    have x4 g a : (X + X).1 g = 0 := h2 _ ((u (placesDividing _ ℓ ∪ .range (z3 <| w · |>.w))ᶜ g a).imp fun _ ↦ .imp (mt (by
      clear * -; simp [placesDividing]; grind only [s23_f5])) id) |> (by simp [X, ·])
    choose m hm using (hδ j).exists_apply_eq_nsmul (F j) (by simp [(w j).w.2.pow_mem_iff_mem, *, (h j).1.1]) (τ := res _) (w j).isPlaceOver.tameGenerator.2 X.1 (X.2.1.1 · ⟨⟩)
      (by simp [X.2.2, t' <| hu · ⟨_, by simp [placesDividing, (h j).1.1], _, F j, ·⟩])
    have := (law _ _ _ δ i (⟨(h _).2, F _, hδ ·, D _, U _ (h _).1.2⟩) _ ⟨⟨(X + X).2, (x4 · <|
      ·.imp (by simp +contextual [hS]))⟩, fun u a ⟨g, d⟩ b ↦ if c : _ then by
      simpa [X, t' (b c), h4 (p (g * g)) ⟨_, (hP u).valuation_natCast_lt_one_iff.2 c, ((o _).trans (ite_eq_left (mul_self_mem_of_index_two ix g)) ▸ mul_mem d d :), κ.ker.mul_mem (b c) (b c)⟩] using (X.2.2 g g).symm else DiscreteModule.Z1.eq_zero_on_decompGroup _ (hP u) (Φ u a c) (x4 · ⟨u, (·.elim c fun ⟨j, e⟩ ↦ (h j).2 (e ▸ hST a :)), _, hP u, ·⟩) (by simp [X, *, cocycle_apply_inv h1, -map_inv]) g d, fun g h ↦ by
      simpa [C g h, h.mul_self ▸ X.2.2 g g] using X.2.2 1 1⟩).symm.trans
      (Fintype.sum_eq_single j (by simp [z · ·, -map_inv]))
    simp [X, p1] at this hm; simp [↓map_nsmul, b, hm]
    linear_combination -m * y * this⟩, n2, (s.isFrob j).2.elim fun ⟨g, e⟩ a ↦ ⟨g⁻¹, by simpa [e, β] using congr(IsUnit ($(α j) 1)), by simpa [← e] using! a⟩⟩
end
section
open Function Finset Fintype Filter PadicInt WellFoundedLT Classical
private lemma ft_j9 {ℓ E} [ThePrime ℓ] [Field E] [UnramCMField E] t {N y h γ} [NeZero N] (hE : ∀ x, algebraMap E Ω x ∈ cycloField N) (hN : N + t < y) (hh : ∀ a ∈ Set.Ioo 0 t, (cycChar Ω ℓ γ ^ a).1 - 1 ∣ ℓ ^ h) (hy : ℓ ≤ y ^ 2 ∨ h = 0) (hf : 4 ≤ numInfPlaces E) {W} (hW : ∀ ν g, ∃ δ, cycChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g)) : ∃ J, ∃ (_ : Fintype J) (_ : LinearOrder J), ∃ ty, ∀ ν > 0, ∃ Q : TaylorWilesPlaces E J (ℓ ^ ν), IsPrimeTriangle ν Q.w (Q.frobData · |>.isPlaceOver.tameGenerator) (Q.frobData · |>.frob) γ⁻¹ t ty (y * h) (y ^ 22 * h) ∧ ∀ j, Q.frobData j ∈ W := by
  choose p hq R using exists_detecting_points_cocycles hE ℓ; let g i := (γ⁻¹ * i)⁻¹ * (i * γ⁻¹)
  have hD (a : Fin t) : (ℓ ^ h) ^ 3 * ∏ k ∈ {a}ᶜ, ((cycChar Ω ℓ γ ^ a.1).1 - (cycChar Ω ℓ γ ^ k.1).1) ∣ ℓ ^ (y * h) := by
    grw [prod_dvd_prod_of_dvd _ (fun _ ↦ ℓ.cast ^ h) fun k n ↦ ?_, pow_mul']; simp [card_compl, ← pow_add]; grind [pow_dvd_pow, NeZero, Fin]
    wlog H : k < a generalizing a k; grind [mem_compl, neg_dvd, _=_ neg_sub]
    erw [← pow_sub_mul_pow _ H.le, ← sub_one_mul, Units.mul_right_dvd]; grind
  have h2 a k := dvd_trans (by nth_grw 1 [← hh _ ⟨k, a.2⟩, pow_succ', ← map_pow, ← s23_p7]) (hD a); obtain ⟨⟨⟩⟩ := exists_wellFoundedLT p, (mostFrobeniiAt E 1).nonempty_of_neBot; let J := {e : Fin t // 0 < e.1} ×ₗ p; use J, inferInstance, inferInstance, ⟨_, Prod.Lex.monotone_fst⟩, fun ν hν ↦ ?_; let κ := cycCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν); let m := (κ γ).1.valMinAbs
  let H := (AddSubgroup.ofSub {v : _ → ℤ | ∃ y, κ y = 1 ∧ ∀ {d Φ T z}, IsLaw ν d Φ T z → z y = v (d, z)} ⟨(·.2 1 |>.cast), 1, by simp⟩ fun _ ⟨a, _, p⟩ _ ⟨b, _, q⟩ ↦ ⟨a / b, by simp [*], fun h ↦ by
    simp [← p h, ← q h, by simpa [κ, *] using h.map_conj_mul 1 (a / b) b]⟩).toIntSubmodule
  let I (j : J) := {i : Set.Iio j | i.1.1.1 = j.1.1}; have F j := (fix_eq (fun (j : J) f ↦ epsilon fun (x, T, z) ↦ s23_n0 ν x ∧ IsLaw ν j.1 (.range fun i : I j ↦ (f _ i.1.2).1.frob) T z ∧ 2 * z x.frob ∣ ↑(ℓ ^ (y * h)) ∧ (∀ O, ∀ c ∈ s23_m5 O ∅ ν j.1, (c + c) (g j.2) = c x.frob) ∧ (∀ i h, z3 (f i h).1.w ≠ z3 x.w ∧ z3 x.w ∉ (f i h).2.1 ∧ (f i h).2.2 x.frob = 0) ∧ z3 x.w ∉ T ∧ x ∈ W) j).symm; generalize fix (α := J) _ = f at F
  replace F := fix fun j p ↦ F j ▸ epsilon_spec (by
    choose h₁ hz _ _ h₃ _ using (SetCoe.forall' (s := .Iio j)).1 p; let B := Module.finBasis ℤ (H.map (.funLeft _ _ fun i : I j ↦ (↑j.1, (f i).2.2))); choose v hv hb using (B · |>.2); choose y hy k using id hv; choose _ T₀ r hk w U hw using s8 j.1 hν hf (I := I j) (.trans (Submodule.finrank_le _) (by simp)) (h₁ ·) (.of_lt_imp_ne (by simp +contextual [h₃])) y; have n : (·.2 w |>.cast) ∈ H := ⟨w, by simpa⟩; choose c A using B.mem_submodule_iff'.1 ⟨_, n, rfl⟩
    have ⟨u, hu, L⟩ := prod_induction (s := {j.1.1}ᶜ) (fun a (d, _) ↦ (m ^ d - m ^ a.1) * m) (∀ v ∈ H, · * v ∈ H) (by simp +contextual [mul_assoc]) (by simp) (fun a _ _ k@⟨b, B, q⟩ ↦ (zsmul_mem k (-m ^ (a.1 + 1))).rec fun a ⟨A, p⟩ ↦ ⟨_, by simp [*], fun k ↦ (k.map_conj_mul γ b a B A).trans
      (by simp [p k, q k, m]; ring)⟩) _ (sub_mem (H.sum_smul_mem (t := univ) c fun j _ ↦ hv j) n)
    have h₄ (i : Set.Iio j) : (f i).2.2 u = 0 := by by_cases i.1.1.1 = j.1.1 <;> simp [L (hz i), prod_eq_zero (i := i.1.1.1), I, (by simpa [← hb] using congrFun A ⟨i, ·⟩), *]
    choose δ hδ V using hW _ _
    have Y (f : _ → ZMod (ℓ ^ ν)) n (hf : ∀ a b, κ a = 1 → κ b = 1 → f (a * b) = f a + f b) :
        f (δ ^ n * (g j.2 * conjGal (g j.2) * (u / conjGal u))) =
        n • f δ + (f (g j.2) + f (conjGal (g j.2)) + (f u - f (conjGal u))) := by
      clear * - hf hδ hu; have := hf (u / conjGal u) (conjGal u); induction n <;> simp_all [pow_succ, add_smul, κ, cycCharMod_prime_pow_eq, g, mul_comm]
    have R {e Φ T z} (h : IsLaw ν e Φ T z) := (Y z (ℓ ^ ν) (by simpa using h.map_conj_mul 1)).trans (by simp [CharP.cast_eq_zero, *, κ, ↓h.odd, g, mul_comm, mul_two] : _ = 2 * z u) ▸ h.isLocallyConstant.eventually_eq _; refine (nonempty_of_mem (inter_mem V (inter_mem_inf (eventually_mostFrobenii ((eventually_notMem_star_notMem ℓ ∅).and (tendsto_place_comap_cofinite (algebraMap _ E) (Set.toFinite (T₀ ∪ ⋃ i, insert (z3 (f i).1.w) (f i).2.1)).compl_mem_cofinite :)) fun _ ↦ id) ⟨_, (R r).and ((eventually_all.2 (R <| hz ·)).and (((selmerZ1.finite_unramified_cocycles (.of (charRep ..) (((Continuous.of_isOpen_ker κ Fact.out).pow _).inv.fst'.smul continuous_snd)) (placesDividing E ℓ).toFinite).eventually_all.2 fun x h ↦ (continuous_discrete_rng.1 h.1.1 _).mem_nhds rfl).and (isOpen_ker_cycCharMod.1.mem_nhds (by simp [cycCharMod_prime_pow_eq, g, mul_comm, *])))), .rfl⟩))).elim fun x ⟨a, ⟨z, n⟩, b, c, d, o⟩ ↦ ⟨(x, _, _), ⟨z.2.2, o⟩, r, by simpa [L r, ← k _ r, cycCharMod_prime_pow_eq, ← mul_assoc, map_ofNat, sq, m, *, κ, ((Units.isUnit _).map _).pow] using map_dvd (toZModPow ν) ((mul_dvd_mul_right ⟨_, rfl⟩ _).trans (h2 _ j.1.2)), fun O k hk ↦ sub_eq_zero.1 (ft_m6 hk fun u m ↦ (fun d ↦ ?_) (d _ ⟨m, ?_⟩)), by simp [h₄] at n c; simpa [Ne.symm, *]⟩; erw [map_sub, d, Y (u <| k ·)]
    all_goals simp +contextual [hk.2.1, mem_selmerModule_iff.1 hk.1, ↓m.2, κ, charRep, CharP.cast_eq_zero])
  choose a d k l c e s using F; have inj : Injective (z3 ∘ _) := .of_lt_imp_ne (swap (c · · · |>.1)); have hw : s23_q3 ν _ (f · |>.1.isPlaceOver.tameGenerator) _ := (and_assoc.1 ⟨a ·, _, _, rfl⟩)
  refine ⟨⟨(f · |>.1), ⟨inj.of_comp, by grind [isSplit_of_q_prime, s23_f5, FrobeniusDatum.prime_q]⟩, (f · |>.1.isFrob.mem_ker_cycCharMod_iff (by simp [(FrobeniusDatum.isPlaceOver _).valuation_natCast_eq_one_iff, (a _).1]) |>.1 (inv_mem (a _).2) |>.symm.dvd')⟩, ⟨hw, ⟨p, hy.elim (by
    simp [J]; grw [card_subtype_le, hq y (by omega) ·, Fintype.card_fin]; nlinarith [(y ^ 21 * h).zero_le]) (by simp [·]), by tauto⟩, dvd_of_mul_left_dvd ∘' hD, fun O j z hz H ↦ (d j).reciprocity (J := Set.Ici j) _ inj.injOn.injective (⟨a ·, by clear * - c e; grind⟩) ⊥ (c · _ ·.bot_lt |>.2.2) O z ⟨s23_q3.z4 (J := Set.Iio j) (hw ·) hz.1 (by simp +contextual [idOrConjInv, cocycle_apply_inv (mem_selmerModule_iff.1 hz.1).1, hz.2.1, *, -smul_eq_zero]), hz.2⟩ (fun _ ⟨i, e⟩ ↦ e ▸ (H _ i.1.2).2 i.2) _ (k j), fun O e ↦ ⟨by simpa [cycInv, map_ofNat] using map_dvd (algebraMap _ O) (.trans ⟨_, rfl⟩ (h2 _ e.2)), fun z k K ↦ ?_⟩⟩, s⟩
  choose m u _ c
    using by simpa [mem_selmerModule_iff, tateTwist, -Pi.add_apply] using add_mem k.1 k.1
  refine congrFun (sub_eq_zero.1 (R (e := e) _ (mem_selmerModule_iff.2 ⟨?_, ?_, ?_, (funext ?_).subst ((c.comp_continuous (continuous_const_mul γ⁻¹)).sub (c.comp_continuous (continuous_mul_const γ⁻¹)))⟩) fun _ h ↦ sub_eq_zero.2 (sah m _ _ (l (e, ⟨_, h⟩) O z k ▸ K _ rfl)))) <;> simp +contextual [m, tateTwist, cycInv, u, cycChar_eq_one_of_mem_inertiaAbove, obeying, -Pi.add_apply] <;> intros <;> module
end
section
open Matrix Polynomial Fintype ComplexOrder IsUltrametricDist NormedField
variable {ℓ} [ThePrime ℓ] {P} {D : Data P} {r n} [Fintype n]
private lemma ft_t7 {A A' B C : (PadicAlgCl ℓ)[X]} (m : B.Monic) (z : ∀ i, ‖C.coeff i‖ ≤ 1) (a : ∀ i, ‖(A * B - C).coeff i‖ < 1) (h : ∀ i, ‖C.coeff i - (A' * B).coeff i‖ < 1) (u : 1 ≤ ‖eval 1 A'‖) : ∃ e, A ∣ .map (intQpBar ℓ).subtype e ∧ e.eval 1 = 1 :=
  have v : 1 ≤ ‖A.eval 1‖ := by
    grw [← sub_add_cancel A' A, eval_add, norm_add_le_max, eval_eq_sum_range, (exists_norm_finsetSum_le ..).choose_spec.2, norm_mul, norm_coeff_le_of_mul_monic m (le_supNorm _), (exists_eq_supNorm _).choose_spec, sub_mul, ← sub_add_sub_cancel _ C, coeff_add, norm_add_le_max] at u; simp_all [norm_sub_rev (C.coeff _), not_le_of_gt]
  ((A * .C (A.eval 1)⁻¹).lifts_iff_coeff_lifts.2 (by simp [← NNReal.coe_le_coe, field, norm_coeff_le_of_mul_monic m (by grw [← sub_add_cancel (A * B), coeff_add _ _ ·, norm_add_le_max, a, z, max_self, v])])).imp fun e he ↦ ⟨⟨_, he⟩, by simpa [norm_pos_iff.1 (by bound)] using congr(eval 1 $he)⟩
private lemma ft_p9 {T : AbsGal D → Matrix n n (PadicAlgCl ℓ)} (c : Continuous T) (δ : ℕ → _) {y : PadicAlgCl ℓ} {A} (h : ∀ i, T (δ i) = y ^ i • A) (hy : ∀ j ∈ Set.Icc 1 (4 * card n + 2), ‖y ^ j - 1‖ = 1) : ∃ i, ∀ᶠ φ in nhds (δ i), 1 ≤ ‖(T φ).charpoly.eval 1‖ := by
  by_contra! a; simp_rw [eval_charpoly, ← mem_ball_zero_iff] at a; have (i : Fin (card n + 1)) H := a i ((isClosed_ball ..).preimage_of_continuous.compl_mem_nhds (by simpa [h] using! ((congrArg valuation (det_aeval_neg_eq_prod_roots (-A) (1 - y ^ i.1 • .X))).trans (map_multiset_prod ..)).trans_ge (Multiset.one_le_prod H))); choose z μ m H using by simpa using this
  refine z 0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (.of_lt_imp_ne fun i j a e ↦ (valuation.map_sub_lt (H j) (H i)).ne ?_) m (by simp)); simpa [e, mul_assoc, ← sub_one_mul, NNReal.eq_iff, hy (j - i) (by grind), ← pow_sub_mul_pow y a.le] using valuation.map_one_sub_of_lt (H i)
variable [PadicIso ℓ] [Fintype r] [Nonempty n] {O : AuxPair D.E r n} {x : Isotypic (stdSpace _ n) (O.κ, O.detExp)} {f} (hf : f ∈ x.1) (h₀ : f ≠ 0) (h : ∀ g, (normalisedRep O x.galRep g).1.charpoly.IsRoot 1)
include hf h₀ h
lemma f6 {w hw S i} (hℓ : ↑ℓ ∉ w.1) (hS : HasHeckePolyAt f.1 w hw S) : i < O.rankDiff → S.IsRoot (O.a.frobValue r w * w.q ^ i) := by
  obtain ⟨⟨s, b⟩, y, _, e, a⟩ := w.isPlaceOver_placeOver.exists_isFrob (AbsGal D), hasHeckePolyAt_iff_localFormRep.1 hS
  exact isRoot_string_of_norm isUnitary_localFormRep y h₀ e a (.of_map (by
    simpa [↓chiOneInv_spec w.isPlaceOver_placeOver hℓ 1, b] using isRoot_of_isRoot_charpoly (P := comp _ ((chiOneInv O s⁻¹).1⁻¹ • .X)) (by
    simpa [aeval_comp, Units.smul_def] using (((sphericalCompat_std w f.2 (x.isEigenform hf h₀)).2 (x.attached_galRep hf h₀) hS.1 _ w.isPlaceOver_placeOver).2.2 _ _ hS s⁻¹ b).1
      (w.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 hℓ)) (h s⁻¹)) ιℓ.toRingHom.injective) (by simp [AutChar.frobValue, sq, ← mul_pow, ← pow_add, O.rank_lt.le])
lemma t1 (z : ∀ g i, ‖(normalisedRep O x.galRep g).1.charpoly.coeff i‖ ≤ 1) : ∀ᶠ y in mostFrobenii _, ∀ S, 1 ≤ ‖eval 1 S‖ → (∀ i, ‖(normalisedRep O x.galRep y.frob).1.charpoly.coeff i - coeff (S * ∏ i ∈ .range O.rankDiff, (X - C (cycInv ℓ _ _ y.frob ^ i))) i‖ < 1) → ∃ e, HasRootString (x.heckePolyAt y.w) (.map (algebraMap EllAdicIntegers _) e) y.w.q (ιℓ.symm (chiOneInv O y.frob).1)⁻¹ O.rankDiff ∧ e.eval 1 = 1 := by
  filter_upwards [(x.attached_galRep hf h₀).2.2.2 _ one_half_pos, eventually_mostFrobenii ((x.isEigenform hf h₀).2.and (eventually_notMem_star_notMem ℓ ∅))] with w a ⟨k, _, _, l⟩ _ b e
  refine (Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C (pow_right_strictMono₀ (by
    simp)).injective).set_pairwise _) (by simpa [chiOneInv_spec w.isPlaceOver l 1, w.isFrob, ↓dvd_iff_isRoot] using (fun _ ↦ f6 hf h₀ h l (k w.prime_q).2))).elim fun T y ↦ (ft_t7 (A := chiOneInv O w.frob ^ card n • 1 * T.map ιℓ) (monic_prod_X_sub_C ..) (z _) (fun i ↦ ?_) e b).imp fun _ : (intQpBar ℓ)[X] ↦ .imp_left (⟨T, y, by simpa [Polynomial.map_map] using! map_dvd (mapEquiv ιℓ.symm) <| dvd_of_mul_left_dvd ·⟩)
  generalize x.heckePolyAt _ = H at *; by_cases! i ≤ card n <;> simpa [‹_›, s23_w6 w l, pow_sub₀, Units.smul_def, ← mul_sub, ← by simpa [Polynomial.map_prod, mul_comm _ T] using congr(mapEquiv ιℓ $y), norm_sub_rev, charpoly_smul_coeff, coeff_eq_zero_of_natDegree_lt, mul_assoc, mul_comm (ιℓ _), norm_eq_one_of_continuous, AlgHeckeChar.continuous_avatar] using (a _ rfl i).trans_lt one_half_lt_one
end
section
open Polynomial Fintype Module Filter Isotypic Real LinearMap LevelPlaces.LevelForm Submodule IsApt NeZero PadicInt Units
attribute [-simp] map_eq_zero nsmul_eq_mul Pi.smul_apply
theorem t5 {P} {D : Data P} {ℓ} [ThePrime ℓ] (ι : PadicIso ℓ) (ϑ : D.Twist) (hq : s23_g7 (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (crudeUnit ℓ D)) {r n} [Fintype r] [Fintype n] {O : AuxPair _ r n} {E Z} (hw : Z ≤ span ℂ {y ∈ Z | (∃ c, y ∈ (tupleProj O c).range ∧ IsApt O c ϑ ∧ (tupleProj O c).range ≤ range (O.groupAlgAction E)) ∧ ∃ z, O.Lifts y z ∧ ∃ R, ∃ V : AuxPair _ r n, HasRow V z R ∧ O.μ = V.μ * ϑ.toAutChar ∧ ∃ γ s, SelmerLengthLe ϑ.invAvatar R ϑ.Q (⌊D.r * t2 D ℓ⌋₊ + 1) γ s}) : DenominatorLe ιℓ O E Z (t2 D ℓ * log ℓ) := by
  refine let A := _; have hZ : span ℂ A = Z := span_eq_of_le _ inf_le_left hw; fun _ e ↦ e ▸ fun Ξ Ξ' hl hΞ ↦ s23_d3 hZ toSmoothForm (innerₛₗ ℂ ∘ Ξ) (by simp)
        (D.chosenGroupOrder ^ 3) fun _ m₀ o ↦ ?_
  have T {S} (k : S ⊆ A) w h s X : span ℂ S ∈ (O.heckePolyOnForms h s X).invtSubmodule := span_le.2 fun y m ↦ (O.heckePolyOnForms_eq_smul h s ((k m).2.2.choose_spec.1 w h s) X).symm.subst (smul_mem _ _ (subset_span m)); have hT := hZ ▸ T le_rfl; let N (x : Isotypic (stdSpace _ n) (O.κ, O.detExp)) := normalisedRep O x.galRep; let 𝓧 (x : Isotypic ..) := ∃ v ∈ A, v.toSmoothForm ∈ x.1 ∧ v.toSmoothForm ≠ 0; choose c m₁ hc le using m₀.2.1; have z {v} (m : v ∈ A) : tupleProj O c v = 0 ∨ v ∈ (tupleProj O c).range ∧ ∃ x : Isotypic .., v.toSmoothForm ∈ x.1 ∧ _ := or_iff_not_imp_left.2 fun h ↦ ⟨m.2.1.elim fun b k ↦ (by_contra (h <| tupleProj_eq_self_of_mem_range k.1 ▸ by simp [← End.mul_apply, ← map_mul, tupleIdem_orthogonal.ortho ·]) : c = b) ▸ k.1, by_contra fun H ↦ h <| mem_ker.1 <| s23_g4 (T (by simpa)) (by simpa [mem_span_singleton] using fun x _ m a b ↦ (H ⟨x, (smul_mem_iff _ a).1 m, b⟩).elim) (mem_span_singleton_self v)⟩; choose x₀ m₂ using ((z m₀).resolve_left ((tupleProj_eq_self_of_mem_range m₁).trans_ne o)).2; have h𝓧 : 𝓧 x₀ := ⟨_, m₀, m₂⟩; have := card_pos_iff.1 O.rank_lt.pos; choose! _ R hR hL γ₀ y₀ hS₀ using fun {x} (m : 𝓧 x) ↦ (m.elim fun _ k ↦ k.1.2.2.elim fun _ L ↦ L.2.elim fun R V ↦ V.elim fun _ e ↦ e.1.1.imp fun _ r ↦ ⟨R, r, e.1.2 e.2.1 L.1 (k.2.elim isEigenform) (k.2.elim attached_galRep), e.2.2⟩ : ∃ τ R, IsRow D O.rankDiff τ R ∧ _ ∧ _); choose γ hγ y h₀ hy using (hR h𝓧).exists_scalar_inertia; choose _ B sp j co using exists_baseLevel hc hq.1
  have cp (x : B.Eigensystem ![]) g i : ‖(N x g).1.charpoly.coeff
    i‖ ≤ 1 := by simp [(eventually_exists_isLatticeIn (r := N x) (co _ _ (by simp) _ x.2).1.continuous).exists.choose_spec.choose_spec.charpoly_eq_map]
  choose h hh hℓ g₁ hC using (if l : D.h₂ ^ 2 < ℓ then IsCyclic.exists_ofOrder_eq_natCard.elim fun b hb ↦ (exists_inertia_cycChar_eq (valuation_comap_intQpBar_lt_one (IsAlgClosed.lift (R := ℚ)).1) (ZMod.val_coe_unit_coprime b).symm).elim fun γ i ↦ ⟨0, bot_le, .inr rfl, {γ with commutes' x := D.z9 x ⟨γ, cycCharMod_of_mem_inertiaGroup i.1 ((Nat.coprime_of_lt_prime out (D.nat_le_of_hasLogBound.trans_lt l) Fact.out).valuation_eq_one (valuation_comap_intQpBar_lt_one _))⟩}, fun a h ↦ (IsUnit.of_map toZMod _ (by
      erw [val_pow_eq_pow_val, i.2]; simpa using pow_ne_one_of_lt_orderOf h.1.ne' (by grind [orderOf_units, Nat.card_units, Nat.card_zmod, Nat.le_self_pow]))).dvd⟩ else (exists_chosen_notMem_placesDividing D ℓ).elim fun v ⟨i, _, hw, hi⟩ ↦ ⟨_, le_rfl, by lia, (v.isPlaceOver_placeOver.exists_isFrob _).imp
    fun φ hφ a ha ↦ by simpa [hφ.cycChar_eq ℓ (v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 hw.2), hi, pos, valuation] using (g_pow_sub_one_dvd_chosenGroupOrder D ⟨ha.1, ha.2.le.trans D.nat_le_of_hasLogBound⟩).natCast.trans (unitCoeff_spec (p := ℓ) out).dvd⟩ : ∃ h ≤ padicValNat ℓ D.chosenGroupOrder, (ℓ ≤ D.h₂ ^ 2 ∨ h = 0) ∧ ∃ γ : AbsGal D, ∀ a ∈ Set.Ioo 0 D.t, (cycChar Ω ℓ γ ^ a).1 - 1 ∣ ℓ ^ h)
  let s := {x : B.Eigensystem ![] | ∀ g, (N x g).1.charpoly.IsRoot 1}
  have W (j : ℕ) (t : Set ↥sᶜ) : ∃ θ, ∀ x ∈ t, ((s23_q7 (@γ₀ x₀) g₁⁻¹ (@y₀ x₀) (ℓ ^ j) θ).linearCombination (intQpBar ℓ) fun g ↦ (N x g).1 - 1).det ≠ 0 := t.toFinite.induction_on _
    (by simp) @fun a _ _ f ⟨θ, h⟩ ↦ (not_forall.1 a.2).elim fun g k ↦ ((f.insert _).eventually_all.2 fun z m ↦ ((mul_right_injective₀ (neg_ne_zero.2 (ne (ℓ ^ j : PadicAlgCl ℓ)))).comp Nat.cast_injective).tendsto_cofinite.eventually (eventually_cofinite_not_isRoot (mt ext_iff.1 fun e ↦ m.elim (k <| ((Matrix.eval_charpoly ..).trans (coeff_det_X_add_C_card ..).symm).trans <|
    · ▸ e _) (h z · (coeff_det_X_add_C_zero (_ - (N z g).1) _ ▸ e 0))))).exists.imp' (θ + .single g
    ·) (by simp_rw [IsRoot.def, eval_det]; intro; convert id
           simp [s23_q7, X_mul, ← Matrix.smul_eq_mul_diagonal, -Finsupp.smul_single]; module)
  choose θ z' hθ hz' using (W _ .univ).imp fun θ h ↦ ((IsFractionRing.isAlgebraic_iff (intQpBar ℓ) (PadicAlgCl ℓ) _).2 (.of_finite ..)).exists_nonzero_coeff_and_aeval_eq_zero
    (Pi.isUnit_iff.2 (h · ⟨⟩ |>.isUnit)).mem_nonZeroDivisors
  rw [aeval_pi_apply, funext_iff] at hz'
  choose J _ _ ty hP using ft_j9 O.rankDiff D.z9
    (by grw [hc.rank_le.2]; exact D.nat_lt_of_hasLogBound) (by grw [hc.rank_le.2]; exact hC) hℓ
    D.nat_le_of_hasLogBound fun ν g ↦ (ft_p9 (hq.2.1.isLocallyConstant.continuous.smul (continuous_val.comp (hR h𝓧).continuous)) _ (by
    intro; simp [hq.2.1.eq_one_of_mem_inertiaAbove γ (hγ.imp (by clear * - hq; grind [s23_g7])), h₀, _root_.smul_pow, smul_comm (ϑ.invAvatar g), pow_right_comm y]; rfl) (hy ν)).elim fun i
    hσ ↦ ⟨γ ^ i, by simp [cycChar_eq_one_of_mem_inertiaAbove (hγ.imp fun _ ↦ .imp_left (·.2))], inter_mem_inf ((eventually_mostFrobenii ((eventually_notMem_star_notMem ℓ (badPlaces D ℓ)).and (B.eventually_isOffLevel (L := ![])))).and <| .all fun x : {x : B.Eigensystem _ // (∀ g k, ‖((N x g).1.charpoly.coeff - (N x₀ g).1.charpoly.coeff) k‖ < 1) ∧ x ∈ s} ↦ x.1.2.elim fun f m ↦ t1 (x := x.1.1) m.1.1 m.2 x.2.2 (cp _)) (preimage_mem_comap hσ)⟩
  choose! ν hν using @ENNReal.exists_nat_gt _; have w (a : EllAdicIntegers) : a.1 = algebraMap _ _ a := rfl; choose Q tri q s₅ using hP _ ν.succ_pos
  let a := ((coeHom _).comp (chiOneInv O)).codRestrict (intQpBar ℓ) (norm_eq_one_of_continuous (by
    fun_prop) · |>.le)
  choose e s he using fun k x ↦ (q k).2 x _ (s₅ k) (congr(‖_ - coeff $(charpoly_eq_mul_of_trace_pow_add _ _ _ (by
    simpa [N, _root_.smul_pow, pow_right_comm] using hL h𝓧 <| _ ^ ·)) _‖).ge.trans_lt <| x.2.1 _ ·)
  let ξ {J L x v} m (a : _ ∧ _) : B.Eigensystem (J := J) L := ⟨x, _, ⟨a.1, B.formsOfLevel_base_le _ (sp v m)⟩, a.2⟩; refine (B.exists_diagOp_mem_ellIntegralForms Q (q · |>.1.2) (a := a) (N := N) (fun _ _ ↦ rfl) (fun k ↦ Subtype.ext ((chiOneInv_spec (Q.frobData k).isPlaceOver (tri.isNewPlaces k).1 0 (inv_mem (Q.frobData k).isPlaceOver.tameGenerator.2)).trans (pow_zero _))) _ z' (𝓧 ·) ⟨ξ m₁ m₂, h𝓧⟩ _ hc.odd.2.pos.ne' (fun k x m h₀ h₁ ↦ (s k ⟨⟨x, m⟩, fun g k ↦ h₁ ⟨_, sub_mem (algebraMap_mem _ (⟨_, cp ..⟩ : EllAdicIntegers)) (B.charpoly_mem_heckeAlgebra (a := a) (fun _ _ ↦ rfl) g k)⟩ (sub_self _), by_contra (h₀ <| hz' ⟨_, ·⟩)⟩).imp fun _ ↦ .imp_right (·.trans (Polynomial.map_dvd _ (Finset.univ.dvd_prod_of_mem _ (Finset.mem_univ _))))) (dvd_iff_ellVal_le.2 <| (hν (by simp [ellVal, ne, w, map_ofNat]; exact (hθ <| Subtype.ext ·))).le.trans <| by simp [w]) fun S _ hS ↦ s6 hc hq hh tri S (co _ _ (q · |>.1.1.1) _ ·.2) .refl (fun x ↦ ⟨hR x.2, hS₀ x.2⟩) (hL ·.2) hS (fun j ↦ (eval_prod ..).trans (Finset.prod_eq_one fun i _ ↦ he j i) : ∀ j, eval (1 : EllAdicIntegers) _ = 1) _ θ).elim fun s h ↦ ?_; let' E s := B.diagOp (L := Q.w) s ∘ₗ toSmoothForm; have key s {y v} m a : (E s ∘ₗ tupleProj O c) v = _ := congr(E s $(IsApt.tupleProj_eq_self_of_mem_range m)).trans (B.diagOp_apply s (@ξ _ _ y v m a) a.1); refine ⟨_, fun v m ↦ (z m).elim (⟨0, by simp [·]⟩) fun k ↦ ⟨_, key _ k.1 k.2.choose_spec⟩, fun l e ↦ smul_left_injective ℂ m₂.2 (key s m₁ m₂ ▸ e) ▸ ?_, fun a b w m e ↦ ?_⟩; convert ellVal_le_iff.1 h.1 using 1 <;> simp [rpow_def_of_pos, pos] <;> ring
  have : _ • _ • w.toSmoothForm ∈ BaseLevel.ellIntegralForms := e ▸ h.2 _ (sp _ ⟨_, rfl⟩) _ (j _ fun _ h ↦ by simpa using! (weylGauge_le_one_iff (ι := _) _ h).1 ((hΞ b).1 _)) _ (sp _ ⟨_, rfl⟩)
    (fun s k ↦ (hw.trans (sInf_le fun v m ↦ (z m).elim (by simp [·]) fun r ↦ r.2.elim fun _ a ↦ by
    simpa [k (ξ r.1 a) ⟨v, m, a⟩] using key s r.1 a) : _ ≤ (E s ∘ₗ _).ker) (by simp))
    fun s k ↦ (E s ∘ₗ _).sub_mem_ker_iff.1 (show tupleProj O c (Ξ' b - _) ∈ (E s).ker by
    choose w ok hv hS using ((B.eventually_isOffLevel (L := ![])).and_frequently (frequently_isSplit_notMem_places O)).exists
    refine s23_g4 (Z := (tupleProj O c).range ⊓ Zᗮ ⊓ (_ ⊓ (O.heckePolyOnForms hv hS (O.testValue w)).ker)ᗮ) (by
      have orth_mem {Z} (hT : ∀ w hw hS X, Z ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule) w hw hS X : Zᗮ ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule := fun y m _ a ↦ inner_eq_zero_symm.1 ((LevelPlaces.LevelForm.p6 ..).trans (inner_eq_zero_symm.1 (m _ (hT _ _ (by aesop) _ a)))); iterate 2 intros; apply_rules only [Sublattice.inf_mem, orth_mem, IsApt.range_tupleProj_mem_invtSubmodule, hT]; intro; simp +contextual [O.k6 hv]) (fun x v r a ↦ by_contra fun H ↦ inner_self_ne_zero.2 (ne_zero_of_map a.2) (r.2 v ⟨r.1, ?_⟩)) ⟨⟨⟨_, rfl⟩, isSymmetric_tupleProj.orthogonalComplement_mem_invtSubmodule (hw.trans (sInf_le fun v m ↦ (z m).elim (by simp [·]) (by simp [tupleProj_eq_self_of_mem_range ·.1, m.1]))) (by simp)⟩, fun _ a ↦ by rw [← isSymmetric_tupleProj, tupleProj_eq_self_of_mem_range a.1.1, sub_mem ((hΞ b).2 _ _ _) (orthogonal_le inf_le_right (by simp)) _ ⟨⟨le a.1.1, a.2⟩, a.1.2⟩]⟩
    let y {J L} := @ξ J L x v r.1.1 a; choose z t e u using hasHeckePolyAt_of_mem_eigenformsAt (ok.2.2.2 _ y.2 ⟨a.1, sp _ r.1.1⟩) hv; simpa [O.heckePolyOnForms_eq_smul _ _ (isSphericalWith_of_heckeSplit z u), ne_zero_of_map a.2, e, eval_heckePoly, AuxPair.testValue, AutChar.frobValue, HeckeChar.atUnif] using f6 a.1 a.2 (by_contra fun h ↦ H <| by simp [E, B.diagOp_apply s y a.1, k y (hz' ⟨y, h⟩)]) ok.2.2.1 ⟨z, t, e, u⟩ (by simp [O.rank_lt]))
  simpa [nsmul_eq_mul, ← PadicComplex.norm_extends ℓ D.chosenGroupOrder, inner_smul_right_eq_smul, field] using (Ξ a).norm_inner_le_one (D.chosenGroupOrder • D.chosenGroupOrder • w) ⟨(algebraMap ..).comp ιℓ.toRingHom⟩ (D.card_classAut_dvd_chosenGroupOrder hc.card_le levelOf_le_Kf) (hl a _)
    (weylGauge_le_one_of_integralAbove (ι := _) _ (by simpa using! this · ·))
end
section
open Matrix Filter Real Module Finsupp Finset CoeffRing Subalgebra RingHom
attribute [-simp] map_smul AlgHom.toRingHom_eq_coe
lemma c0 {P} (D : Data P) ℓ [ThePrime ℓ] (ι : PadicIso ℓ) {I : Type} [Finite I] {r : I → Type} [∀ i, Fintype (r i)] {R : ∀ i, _ →* GL (r i) _} (h : ∀ i, ∃ t J, IsRow D t J (R i)) M : ∃ τ : D.MFoldTwist, ∀ n, let ϑ := τ.powTwist n
  s23_g7 (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (crudeUnit ℓ D) ∧ (∀ i, ∃ γ y, SelmerLengthLe ϑ.invAvatar (R i) ϑ.Q M γ y) ∧ ∀ (p : D.Pair) s, p.IsRamified → ‖ιℓ (p.ratio ϑ s)⁻¹‖ ≤ exp (9 * crudeUnit ℓ D * log ℓ) := by
  choose w _ hw hℓ hi using exists_chosen_notMem_placesDividing D ℓ
  choose μ V f₁ f₃ f using fun k : Subtype _ × _ ↦ s2 hw hℓ.2 _ k.2 k.1.2
  choose O u γ β hu hβ hρ using (eventually_all.2 (h · |>.choose_spec.choose_spec.n3 hw hℓ M)).exists
  choose Q ψ a j c using g0 (by simp; grind) ⟨w, by grind, _, w.isPlaceOver_placeOver, w.isPlaceOver_placeOver.tameGenerator.2⟩
    hρ f₁ (by finiteness) hβ (fun _ _ ↦ by grw [f₃, hi, ← ellVal_le_crudeUnit D ℓ _ ⟨.refl, D.nat_le_of_hasLogBound⟩, pow_one]) (η := crudeUnit ℓ D) (by simp [crudeUnit]) D.m
  obtain ⟨τ, rfl, rfl⟩ := (j 1 ⟨.refl, D.nat_le_of_hasLogBound⟩).elim (s23_k2 · <| pow_one ψ ▸ ·.1)
  simp_rw [show ∀ n, τ.invAvatar ^ n = (τ.pow n).invAvatar by simp [MonoidHom.ext_iff, Data.TameChar.pow, q4 (artinMap_surjective ..).choose_spec]] at *; have N n hn w c (e : τ.ψ w ^ n = 1) : False := have ⟨σ, hw, H⟩ := (j n hn).2.2
    (hw ⟨w, c⟩).2.2.elim fun B ⟨b, k⟩ ↦ have ⟨x, hx, j⟩ := b.exists_localArtin_eq (inv_mem b.tameGenerator.2) 0
      by simpa [ellVal, ← k, q4 (b.artinAt_eq_of_localArtin_eq j ▸ artinMap_locIdele ..), (τ.pow n).4.charUnramifiedAt e ((τ.pow n).5 _ (τ.6 w c)) x hx] using (single_le_sum (by simp) (mem_univ ⟨w, c⟩)).trans H
  use ⟨⟨τ, by simpa using N 1 ⟨.refl, D.nat_le_of_hasLogBound⟩⟩, N⟩, fun ⟨n, hn⟩ ↦ have s@⟨s₁, s₂, _⟩ := j n hn
    ⟨s, fun i ↦ have ⟨⟨v, o, z⟩, y, e', _, hs⟩ := (hρ i).4; ⟨γ i, ⟨_, norm_le_one y⟩, (c n hn i).mono ?_⟩, fun p s hp ↦ le_exp_of_log_le (by
      simpa using! neg_le_neg (le_log_of_rpow_le (by simp [NeZero.pos]) (ellVal_le_iff.1 (f (⟨p, hp⟩, s) ⟨τ.pow n, N n hn⟩ s₁ (9 * _) ((a n hn _).trans_eq (by simp; ring))))))⟩
  rintro O' ⟨hO, ψ', k, s₇⟩; let e := (inclusion hO).1
  refine ⟨e.mapMatrix.1.comp (u i), _, e y, rfl, hu i, k, by simp [twistRep, map_smul', e', by
      simpa [← k] using s₂.eq_one_of_mem_inertiaAbove _ ⟨v, by clear * - s₁ o; simp at *; grind, z⟩], by simpa using hs.map e, cycChar_eq_one_of_mem_inertiaAbove ⟨v, o.2, z⟩, s₇.trans' (normLength_mono (length_mono ?_))⟩
  rintro x ⟨⟨h⟩⟩; use mem_obeying.2 ?_
  let := e.toAlgebra; have := (inclusion.faithfulSMul hO).to_isTorsionFree
  have := Finite.right ℤ_[ℓ] O.1 O'.1
  rintro _ (H | ⟨_, ⟨_, ⟨v, rfl⟩, f, hf, rfl⟩ | rfl, rfl⟩)
  exacts [mem_obeying.1 h _ (.inl (by simpa [unionWithConj] using! H)), mem_obeying.1 h _ (.inr ⟨_, ⟨v, rfl⟩, mapRel _ f, fun z a ↦ funext fun i ↦ (forall_dual_apply_eq_zero_iff O _).1 fun l ↦ by
    simpa [← smul_toAlgebra, mapRel, linearCombination, ↓sum_mapRange_index, sum] using congrFun
      (hf _ (crysCocycles.map a ((l.restrictScalars _).compLeft _) fun g ↦ by simp [funext_iff, twistRep, mulVec, dotProduct, ← smul_toAlgebra, by simpa [← k] using (s₂.eq_one_of_mem_decompGroup v.2 v.1.isPlaceOver_placeOver g.2)])) i, mapDomain_mapRange _ _ _ _ (map_add _)⟩), by simpa [mapRel]]
end
section
open Matrix Polynomial Fintype Filter Data AutChar Classical LinearMap Space Subtype Finset
variable {P} {D : Data P} {r n} [Fintype r] [Fintype n] {O : AuxPair D.E r n} {ℓ} [ThePrime ℓ] (ι : PadicIso ℓ)
private lemma p2 {c} (hO : IsApt O c 1) b J R (h : IsLabelledColumn (m := r) O (card r) J c ∅ R) (s : ∀ g, (mostFrobeniiAt _ g).Tendsto (ιℓ <| b ·.w 1) (nhds (R g).1.trace)) (hJ : IsRowType D (card r) O.rankDiff fun σ ↦ (J σ).map (· - ((card r - O.rankDiff) / 2 - cmSign σ * O.weight (.mk σ)))) : ∃ T, HasRow O b T := have ⟨N', a, ha⟩ : 2 ∣ card n ∧ 2 ∣ (card r - O.rankDiff : ℤ) := by grind [IsApt]
  ⟨_, ⟨_, (h.twist_avatar O.hasWeight.inv 0 a (by grind [IsApt]) hO (hO.tame_part_eq.rec (by aesop))).isRow hO (by simpa [HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, cmSign, apply_ite, ha, sub_eq_add_neg] using hJ)⟩, @fun ϑ V _ _ S h₃ hy f U σ ↦ by
  simp [trace_eq_neg_charpoly_nextCoeff (S _).1, nextCoeff, O.rank_lt.ne_zero, TameChar.invAvatar]
  apply tendsto_nhds_unique (.congr' (mem_inf_of_left _) (.neg (.mul _ (U.tendsto_charpoly_coeff ..)))) (.add (.mul _ (.mul _ (s σ))) _)
  any_goals apply tendsto_mostFrobeniiAt (g := σ) _
  filter_upwards [eventually_mostFrobenii (f.2.and (eventually_notMem_star_notMem ℓ (.image V.placeAt ⊤))), (ϑ.hasWeight.inv.toAlgebraic 0 0).eventually_avatar_frob, (O.hasWeight.inv.toAlgebraic 0 a).eventually_avatar_frob] with x ⟨u, o, _, hl⟩ d d'
  choose _ z s E v using u x.prime_q
  have k T := (smul_left_inj f.1).1 ((isSphericalWith_of_heckeSplit z v).2 T ▸ (hy _ ‹_› (by aesop)).2 T)
  obtain ⟨m, i, l⟩ := (u x.prime_q).2.isMonicOfDegree f.1, k 0, congr(-deriv ($(k ·)) 0)
  simp (disch := fun_prop) only [heckePolyEval, trivialHecke, smul_eq_mul, deriv_fun_mul, deriv_fun_finsetProd, deriv_fun_sum, deriv_fun_pow] at i l; simp [E, ← sum_mul, zero_pow_eq, O.rank_lt.pos, isMonicOfDegree_iff, sum_range_succ', hO.odd.1.pos] at i l m
  simp [↓d, ↓d', E, chiOneInv_spec x.isPlaceOver hl 1, x.isFrob, HasWeight.toAlgebraic, s23_w6 x hl, field, HeckeChar.atUnif, heckeCoeff, h₃, ← ha, ← i, m, AutChar.frobValue, Nat.sub_sub_self O.rank_lt.pos, l, zpow_sub₀, _root_.spaceChar_rankTwist N', ← map_natCast ιℓ, FinPlace.q_eq_sqrt_sq, pow_sub₀, O.rank_lt.le]
  ring⟩
private lemma ft_n1 {p} (H : D.goodForms (D.spaceW D.m) ⊓ D.eigenPart _ p ≠ ⊥) (j : D.LiftIndex) : ∃ T, HasRow (D.auxPair .one j) (p ⟨·, ·⟩) T := by
  obtain ⟨⟨z, ⟨hz, hp⟩, z0⟩, d, κ, hκ⟩ := (Submodule.ne_bot_iff _).1 H, exists_isHCParam_of_hasGap D.hasGap_signsY_paramW; let L := (AlgForm ..).subtype ∘ₗ ((D.spaceW D.m).toAlgForm hκ).1; have ρ g y : L _ = rightRegular ℂ _ _ g (L y) := congr($(toAlgForm_formRep hκ ..).1)
  obtain ⟨K : L z ∈ levelSpace (rightRegular ℂ ..) D.chosenLevel, hf : _ ∈ forms _ (d, κ), c : ∀ x, (ResField ((auxPair ..).chosenPlace x))[X], hc, hl⟩ := by simp [← ρ, mem_levelSpace.1 z.2], (toAlgForm _ hκ z.1).2, D.goodTupleFamilies.exists_ne_zero_of_sum_ne_zero
    (by simpa [e₀] using ((D.isCentralProj_e₀.1.map _).mem_range_iff.1 hz).trans_ne z0)
  have E := D.isEigenform_of_hasHeckePolyAt (by simpa [L]) fun w a ↦ ⟨levelSpace_anti (maxCompactAt_le_levelOf a.2) K, (p ⟨w, ·⟩), rfl, fun i ↦ map_heckeSplit _ i L ▸ by
    simp [by simpa [w2, a, Subtype.ext_iff] using (Submodule.mem_iInf _).1 hp (w, i)]⟩
  obtain ⟨a, R, h⟩ := s23_n9 D 1 j hc, (sphericalCompat_std ofNonempty hf E).1; apply p2 ι a
  convert isLabelledColumn_of_hasProductLabel a hf E h (fun _ _ b ↦ levelSpace_anti (maxCompactAt_le_levelOf b) K) fun i ↦ HasParahoricType.hasProductLabel (e := .refl _) (b := 0) (s := 0) (ψ := 1) (L.domRestrict _) (fun _ ↦ by simp [L])
    (hl <| piTensorElem_apply_eq_zero i ·) ⟨by simp, fun k _ _ e ↦ by
    simpa [-GeneralLinearGroup.val_det_apply] using ρ .. ▸ congr(L $(apply_liftResidue_eq _ _ ((reduceFamily_atSplit ..).trans (congrArg _ (Units.ext e))))).symm⟩ nofun nofun
  simp; simpa [Nat.sub_sub_self D.r_odd.pos, trace_eq_neg_charpoly_coeff, ↓card_rowIndex] using (h.tendsto_charpoly_coeff · D.r.pred |>.neg); simp [↓card_rowIndex, auxPair, AuxPair.rankDiff, jumps]; convert isRowType_auxPair j.2 using 3 with σ q i; have := hκ.eq_hcParameter (.mk σ) (D.basisVec q)
  simp [cmSign, apply_ite, hcParameter, diagramWeight_apply, ↓card_rowIndex] at *; clear * - this
    i; grind [Data.basisVec, paramW, decrPosition_paramW]
end
open Submodule Data Polynomial Multiset Finset Real
lemma exists_isFitFamily {P} (D : Data P) : ∃ θ, D.IsFitFamily θ := by
  choose R' F' using fun {ℓ} {_ : ThePrime ℓ} {ι : PadicIso ℓ} (p : {p : D.Pair × D.LiftIndex // p.1.IsRankOne p.2}) ↦ p2 ι (isApt_rank_one 1 p.2) 1 (fun _ ↦ {0}) 1 (by
    have := (@isFiniteTypeAt_char ℓ _ _ D.E _ _ · 1 Unit _ _ continuous_one (by simp)); simp_rw [← C_1]; use! continuous_one <;> simp_all [IsTraceNondeg, Matrix.trace, ← Matrix.ext_iff, IsLabelledAt, ↓aroots_X_sub_C, isGoodAt_iff]) (by simp) (by use ?_, ?_, ⟨p.1.2, ?_⟩ <;> simp [← cons_zero, countP_cons] <;> grind [Pair.IsRankOne, Int.units_natAbs, !(D.nat_lt_of_hasLogBound : 2 * D.h₂ ^ 2 + D.t < D.w _ _)])
  choose R F using fun {ℓ} {_ : ThePrime ℓ} {ι} (a : _ × (D.m8 _ (D.goodForms _)).toFinset) ↦ ft_n1 ι ((Set.Finite.mem_toFinset _).1 a.2.2) a.1
  choose τ H using fun κ : PrimePadicIso ↦ @c0 _ D κ.1 ⟨⟩ ⟨κ.2⟩ _ _
    (·.getRight?.map 0 |> @RowBlockIndex _ 1) _
    (Sum.rec _ _) (Sum.rec (⟨_, F · |>.1⟩) (⟨_, F' · |>.1⟩)) ⌊D.r * t2 D κ.1⌋₊.succ
  choose s s' using fun T (hT : ∀ l ∈ T, Nat.Prime l) ↦ show ∑ l ∈ T, t2 D l * log l ≤ D.B₀ ∧ ∑ l ∈ T, 9 * crudeUnit l D * log l ≤ D.x ^ 999 by
    clear * - hT; have L {a} : ∑ l ∈ T, padicValNat l a * log l ≤ log⁺ a := by grw [log_of_nat_eq_posLog, log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset _ subset_union_right, ← T.subset_union_left] <;> simp_all [Nat.factorization_def]
    push_cast [t2, _root_.loss, lambdaLoss, crudeUnit, add_mul, @mul_assoc ℝ, sum_add_distrib, ← mul_sum]
    grw [L, sum_le_sum fun _ _ ↦ by grw [mul_comm, log_le_self (by simp)], sum_le_hasSum _ (by simp)
      (hasSum_coe_mul_geometric_of_norm_lt_one (by bound)), L, (exists_length_shaOdd_le ..).choose_spec.2.1, classNumber_le, L, L, prod_le_prod (by simp; tauto), prod_const, Nat.card_Ioc, tsub_tsub_le_tsub_add, add_tsub_cancel_left]
    push_cast [↓log_of_nat_eq_posLog, sub_half, Nat.cast_natAbs, abs_discr_eq_rootDiscr_pow, finrank_eq_two_mul_card_infinitePlace]
    any_goals exact neg_one_lt_zero.le.trans (Nat.cast_nonneg _)
    exacts [⟨add_halves D.B₀ ▸ add_le_add D.le_of_hasLogBound D.le_of_hasLogBound, D.le_of_hasLogBound⟩, D.nat_le_of_hasLogBound, D.z9]
  use τ, fun κ ↦ (@s23_q9 _ _ _ ⟨⟩ _ (H κ ⟨1, .refl, D.nat_le_of_hasLogBound⟩).1.1).1, fun j ↦ ⟨_, s, fun κ ↦ have := ThePrime.mk; ⟨t5 _ _ (H ..).1 (D.range_goodLift_le fun q y a c k m ↦ dite (y = 0) (by simp [·]) (subset_span ⟨⟨⟨y, a.1⟩, rfl⟩, ⟨c, m, s23_n9 D _ j k, D.range_tupleIdem_le k⟩, _, D.lifts_auxLift _ a.2, _, _, F ⟨j, q, by simpa using mt (D.s23_c7 (D.hasRigidLabels_spaceW j) (D.hasRigidLabels_spaceW ⟨_, D.nat_le_of_hasLogBound, .refl⟩) · |>.le a) ·⟩, by simp [auxPair, liftChar, twist_one_spec], (H ..).2.1 (.inl _)⟩)), fun p h ↦ t5 _ _ (H ..).1 (span_mono (forall_eq.2 ⟨by simp, ⟨_, s23_k5 _ h, isApt_rank_one _ h, le_rfl⟩, _, LValueData.auxPair_lifts_trivialLift _, _, _, F' ⟨(p, j), h⟩, by simp [twist_one_spec], (H ..).2.1 (.inr _)⟩))⟩⟩, (.of_le s' fun _ ↦ H _ · |>.2.2 · · ·)
