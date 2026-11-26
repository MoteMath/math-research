import Lib.LocalGL.Green.CuspidalAtScalars
section
open IntermediateField Complex ComplexConjugate Finset Hall IsGalois LinearEquiv Module MulChar Polynomial Units LinearMap.GeneralLinearGroup
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] (T : MulChar K ℂ) {Q m} {x y z : K} (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (η : K → ℂ)
include hQ hx
private lemma v6 : ∃ e, thetaChar T Q x = T ^ e ∧ T x = exp (2 * Real.pi * I / (Q - 1 :)) ^ e :=
  have : NeZero (Q - 1) := ⟨by lia⟩; ⟨_, rfl, @Classical.epsilon_spec _ (_ = _ ^ ·) (by
   grind [(isPrimitiveRoot_exp _ this.1).eq_pow_of_pow_eq_one, congr(T $hx)])⟩
lemma thetaChar_apply_pow {m a N} (hN : N ≠ 0) (hm : N = (Q - 1) * m) (h : T z = exp (2 * Real.pi * I / N) ^ a) : thetaChar T Q x (z ^ m) = (T ^ a) x := by
  obtain ⟨⟨x, rfl⟩, ⟨z, rfl⟩, _, _⟩ := IsUnit.of_pow_eq_one hx (by lia),
   T.apply_ne_zero_iff.1 (h.trans_ne (by simp)), v6 T hQ hx
  simp_all [← exp_nsmul, pow_apply_coe]; grind [Nat.cast_eq_zero]
lemma r4 : y ^ (Q - 1) = 1 → z ^ (Q - 1) = 1 → thetaChar T Q (x * y) z = thetaChar T Q x z * thetaChar T Q y z := by grind [v6 T, @thetaChar_apply_pow (m := 1), mul_pow, map_mul (thetaChar T Q z) x y]
lemma s11_j8 {m r a} (h : 2 ≤ m) (e : m = Q ^ r) (o : x ^ a = y) : z ^ (m - 1) = 1 → thetaChar T m y z = thetaChar T Q x (z ^ ∑ i ∈ .range r, Q ^ i) ^ a := by grind [v6 T, thetaChar_apply_pow T, @thetaChar_apply_pow (m := 1), map_pow (thetaChar T m z) x a, pow_mul, one_pow, pow_right_comm, geom_sum_mul_of_one_le]
variable [IsFaithfulMulChar K T]
noncomputable def charName : MulChar k ℂ ≃* kˣ := .symm (.ofBijective (F := _ →* _) (.mk' (fun a ↦ ⟨(thetaChar T (.card k) (algebraMap k K a)).comp (algebraMap k K), by simp⟩) (by
   simp [MulChar.ext_iff, r4 T Finite.one_lt_card])) (((injective_iff_map_eq_one
  _).2 fun a h ↦ (v6 T Finite.one_lt_card (algebraMap_pow_card_pred_eq_one a)).elim
  fun e ⟨p, q⟩ ↦ by rw [← Nat.card_units, ← IsCyclic.exponent_eq_card, ((isPrimitiveRoot_exp _
  NeZero.out).pow_eq_one_iff_dvd e).2 (Monoid.exponent_dvd_of_forall_pow_eq_one _)] at q <;> cases e
  <;> simp_all [pow_apply', ← map_pow, IsFaithfulMulChar.injective, map_eq_one_iff, MulChar.ext_iff, ← val_eq_one]).bijective_of_nat_card_le (card_eq_card_units_of_hasEnoughRootsOfUnity ..).le))
omit hQ hx
lemma thetaChar_charName χ y : thetaChar T (.card k) (algebraMap k K (charName T χ)) (algebraMap k K y) = χ y := congr($((charName T).1.3 χ) y)
lemma charName_pow_eq_one {T} [IsFaithfulMulChar K T] {χ M} (h : χ ^ M = 1) : (charName T χ).1 ^ M = (1 : k) := mod_cast by simp [← map_pow, h]
open Fint
lemma y0 {L} [Field L] [Finite L] [Algebra k L] (φ : L →ₐ[k] K) (B : Hall k) : q0 (finrank k L) (greenCuspidal k η) B.mulMu = finMean fun z : Lˣ ↦ conj (η (φ z)) * B (simClassOf (LinearMap.mulLeft k z.1)) :=
  let ρ (e : L ≃ₗ[k] L) := (e.conjAlgEquiv k).toAlgHom.comp (Algebra.lmul ..); let := φ.toAlgebra
   have H e z : simClassOf (ρ e z) = simClassOf (LinearMap.mulLeft k z) :=
    s11_q1 e⁻¹
   have E g : (greenCuspidal k η).mulMu (simClassOf g) =
     (∑ z, η (φ z) * Nat.card {e // ρ (generalLinearEquiv k L e) z = g}) / Nat.card Lˣ := by
    obtain h | ⟨a, y, rfl⟩ := em' (∃ a y, ρ a y = g); simp_all; by_contra! ⟨h0, h1⟩
    have ⟨P, j, p, e⟩ := (s11_j9 η).exists_charpoly_eq_pow h0; let V :=
     AEval' g; let A := AdjoinRoot P
    let : Module A V := IsTorsionBy.module (congr($(minpoly.dvd_iff.1 ((s11_k9
     h1).minpoly_squarefree.isRadical _ _ (e ▸ g.minpoly_dvd_charpoly))) ·))
    rcases Fact.mk p, ‹Finite V›, show IsScalarTower k A V from IsTorsionBySet.isScalarTower _; have r := finrank_mul_finrank k A; let := (FiniteField.nonempty_algHom_of_finrank_dvd (L := L) ⟨_, (r V).symm⟩).some.toAlgebra; let t := ofFinrankEq _ _ (mul_left_cancel₀ (by grind [r L, finrank_pos]) (r L ▸ r V))
    exact h (t.symm.restrictScalars k) _ (.trans
     (.symm (LinearMap.ext (t.eq_symm_apply.2 <| t.map_smul (.root P) ·))) (aeval_X _))
    erw [eq_div_iff (by simp), H, Nat.card_units, m1 (adjoin.powerBasis
     (integral k y)), minpoly_gen, ← (splits _ y).map_aroots_algebraMap, Multiset.map_map, ← sum_mk _ (nodup_roots (.map (separable ..))), sum_mul]
    apply sum_subset_zero_on_sdiff le_top <;> intro z h; simp [(show ρ · z ≠ ρ a y from
     ne_of_apply_ne (aeval · (minpoly k y)) (by simp_all [aeval_algHom_apply, minpoly.ne_zero_of_finite]))]
    obtain ⟨c, rfl⟩ := minpoly.exists_algEquiv_of_root (.of_finite ..) (mem_aroots.1 h).2
    exact congr(_ * $(Nat.card_congr (((Equiv.mulLeft a * .mulRight c).trans (generalLinearEquiv
     ..).1.symm).subtypeEquiv fun e ↦ ((a * e).forall_congr
     (by simp [ρ, Algebra.smul_def, mul_eq_trans])).trans LinearMap.ext_iff.symm)))
   star_injective (by simp [*, z6, classInner, finMean, Fintype.sum_eq_add_sum_subtype_ne _ (0 : L), mul_left_comm, fun e (z : Lˣ) g ↦ (.symm Units.ext_iff : ρ e z = g.1 ↔ z.map (ρ e) = g), Ne.symm, mul_div, reindex_equiv unitsEquivNeZero, Fintype.card_subtype, ← sum_boole, ← sum_comm_cycle, ← sum_div, mul_sum, field, mul_comm _ (η _)])
instance : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
end
open Polynomial Hall IsAlgClosed Classical FiniteField LinearMap Finset minpoly Multiset Module UniqueFactorizationMonoid ComplexConjugate AdjoinRoot
variable {k K : Type _} [Field k] [Finite k] [Field K] [Algebra k K] {T : MulChar K ℂ} {P : k[X]} (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0) {x : K} (hx : P.aeval x = 0)
@[simp] lemma gt_v2 (T : MulChar K ℂ) (hP : Irreducible P) (hm : P.Monic) : labelChar T P = greenTau T P := by simp [labelChar, normalizedFactors_irreducible hP, hm.normalize_eq_self, hP.ne_zero]
attribute [local simp] greenTau q0 Hall.ext_iff charpoly_natDegree thetaChar_charName q6 Finite.one_lt_card aeval_algHom_apply coe_frobeniusAlgHom
lemma isCuspidal_greenTau : (greenTau T P).IsCuspidal := fun _ ↦ by simp_intro ..; split <;> simp; apply_rules [s11_j9]
lemma s11_j1 c : c.dim ≠ P.natDegree → greenTau T P c = 0 := by aesop
variable [IsFaithfulMulChar K T]
lemma s11_m3 [IsAlgClosed K] {L} [Field L] [Algebra L K] {i} (σ : L →+* L) (h : ∀ y, σ y = y ^ .card k ^ i) (P : L[X]) : (P.map σ).aroots K = (P.aroots K).map (· ^ .card k ^ i) := by open Fint in convert (splits _).roots_map (frobeniusAlgHom k K ^ i).1 <;> aesop
include hP h0 hx
lemma root_pow_card_pow_pred_eq_one : x ^ (.card k ^ P.natDegree - 1) = 1 ∧ 2 ≤ .card k ^ P.natDegree := by aesop (add simp [(root_pow_card_pow_eq_self_iff hP), Nat.succ_le_iff, hP.natDegree_pos.ne', aeval_def])
omit [IsFaithfulMulChar K T] in
lemma s11_m0 {a} [NeZero a] : let d := P.natDegree; (greenCuspidal k
   (thetaChar T (.card k ^ d) (x ^ a))).rankPart d = (greenCuspidal k (thetaChar T (.card k ^ d)
   x <| · ^ a)).rankPart d := by
  simp [Hall.ext_iff]; intros; split_ifs <;> [subst_vars; rfl]
  rw [s11_m8, one_mul]; intro z; by_cases z =
  0 <;> simp_all [s11_j8 T _ _ _ (pow_one _).symm rfl, root_pow_card_pow_pred_eq_one hP h0 hx, MulChar.map_zero, NeZero.ne]
lemma s11_w4 : let d := P.natDegree
  greenTau T P = (-1 : ℂ) ^ d • (greenCuspidal k (thetaChar T (.card k ^ d) x)).rankPart d := by
  rw [greenTau, ← (exists_pow_card_pow_eq_of_root hP hx (@epsilon_spec _ (P.aeval · = 0) ⟨x,
   hx⟩)).choose_spec.2, s11_m0 hP h0 hx]
  delta greenCuspidal brauerLift; congr! 6
  open Fint in erw [← Multiset.map_map, ← s11_m3 (.id k)] <;> simp [pow_card_pow]
omit hx
seal q0 finrank
lemma s11_p9 (hm : P.Monic) : (∀ S, Irreducible S → S.Monic → S.coeff 0 ≠ 0 → q0 P.natDegree (greenTau T P) (greenTau T S) = ite (P = S) 1 0) ∧ (P.eval 1 ≠ 0 → q4 P.natDegree (greenTau T P) constOne = 0) := by
  have := NeZero.of_pos hP.natDegree_pos; let L := Extension k _ P.natDegree; let := (lift : L →ₐ[k] K).toAlgebra; have r : _ = finrank k L := (finrank_extension ..).symm; let j χ := algebraMap L K (charName T χ).1
  have R {S : k[X]} (i : Fact (Irreducible S)) (z : S.coeff 0 ≠ 0) h : ∃ χ, S.aeval (j χ) = 0 :=
   ⟨(charName T).symm (.map (algEquivExtension k _ _ _ (finrank_quotient_span_eq_natDegree.trans
   h)).toMonoidHom (.mk0 (root S) (z <| by simpa [·] using eval₂_root S))), by simp [j]⟩
  have ⟨χ, a⟩ := R ⟨hP⟩ h0 rfl
  have o ξ : @finMean Lˣ (fun z ↦ conj (χ z) * ξ z) = ite (j χ = j ξ) 1 0 := by
   open Fint in simpa [finMean, field, ← χ.star_apply', ← @inv_mul_eq_one _ _ χ, j, Units.val_inj, MulChar.ext_iff, MonoidHom.ext_iff] using sum_hom_units ((χ⁻¹ * ξ).comp (Units.coeHom L))
  have p B := y0 (thetaChar T (.card L) (j χ)) (IsScalarTower.toAlgHom k
   L _) B ▸ k5
   (H := constOne) (s11_j9 _) finrank_pos.ne'
  rw [s11_w4 hP h0 a, r, ← natCard_eq_pow_finrank]
  use fun S i m z ↦ byCases (R ⟨i⟩ z · |>.rec fun ξ b ↦ by
   rw [show ite .. = ↑(count (j χ) (S.aroots K)) by simp [eq_comm, i.ne_zero, ↓mem_aroots, *, ↓count_eq_of_nodup (nodup_roots (PerfectField.ofFinite.1 i).map), eq_iff_aeval_eq_zero, eq_of_irreducible_of_monic hP a hm], s11_w4 i z b]
   simpa [fun (u : L) i ↦ v9 (g := mulLeft k u) (irreducible (x :=
    u) i) (monic i) (aeval_algHom k (Algebra.lmul k L) u ▸ .zero) ▸ aroots_pow_eq_frobenius_orbit (irreducible i) (x := algebraMap L K u) (by simp), IsIntegral.of_finite, aroots_eq_frobenius_orbit i b, *, mulMu, j, mul_sum, eq_one_of_monic_natDegree_zero, ← range_val, finMean_sum, ← mul_pow, ← ξ.pow_apply_coe, count_map, mul_mul_mul_comm _ (conj _), ← natCard_eq_pow_finrank, charpoly_monic] using! p (brauerLift k
    (thetaChar T (.card L) (j ξ)))) (by aesop), fun h ↦ by simpa [by simpa using (o 1).trans (by
     aesop (add simp aeval_def)), mulMu.eq_unfold, s11_j3, q4, j,
   finrank_pos.ne'] using (p constOne).symm
