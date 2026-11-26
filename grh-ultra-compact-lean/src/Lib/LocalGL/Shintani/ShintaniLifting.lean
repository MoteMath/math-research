import Lib.LocalGL.Green.LabelIdempotents
open Algebra Algebra.TensorProduct IntermediateField _root_.Subalgebra _root_.TensorProduct ComplexConjugate Fin FiniteField Finset Fint Function Hall IsGalois Module Polynomial Units minpoly
variable {k n V ι} [Field k] [Finite k] [Fintype n] [AddCommGroup V] [Module ℂ V]
lemma sum_evalGL_prod_eq_zero_iff [LinearOrder ι] (b : n → ι) [Fintype ι] {F : ι → _} (hF : ∀ a, Lift ℕ (F a) (F a)) (A : GL n k → End ℂ V) {v} (h : ∀ g x, A g (A x v) = A (g * x) v) : ∑ᶠ g, star ((∏ a, (F a).rankPart (Fintype.card {i // b i = a})).evalGL g) • A g v = 0 ↔ ∀ y, ∑ᶠ p, star (∏ a, (F a).evalGL (blockHom b a p)) • A (p * y) v = 0 := by
  let L := Finsupp.lift _ ℂ _ (A · v) ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).1
  let ρ := (Representation.leftRegular ..).quotient L.ker
   (A · |> L.ker_le_ker_comp |>.trans_eq (congrArg _ (by aesop) : _ = (L ∘ₗ _).ker))
  have := (isChar_of_mem_virtualChars (prod_mem fun a _ ↦ comp_mem_virtualChars (hF
   a).evalGL_mem_virtualChars (blockHom ..))).groupAlgElem_eq_zero_iff (ρ := ρ.domRestrict _).trans
   (m4 b F (mem_univ <| b ·) _ ρ.char_conj ▸ (isChar_of_mem_virtualChars
   (Lift.evalGL_mem_virtualChars (prod_hom_rel .one fun _ _ _ ↦
   .mul (.rankPart_of_descendsTo (hF ..))))).groupAlgElem_eq_zero_iff.symm)
  simp_all +zetaDelta [Submodule.linearMap_qext_iff, MonoidAlgebra.lhom_ext'_iff, Subtype.ext_iff, LinearMap.ext_ring_iff, ← L.quotKerEquivRange.map_eq_zero_iff, asAlgebraHom_eq_sum]
  use fun e y ↦ ((MulAut.conj y).sum_comp _).rec (by simpa [h, w3] using congr(A y $e)),
   (by simpa using · 1)
variable {k : Type*} {k'} {n : Type*} {K r} [Field k] [Field k'] [Algebra k k'] [Finite k] [Finite k'] [Fintype n] [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K] (T) [IsFaithfulMulChar K T] (σ : Gal(k'/k)) {L} [Field L] [Algebra k L] {P : k[X]} {x : K}
omit [Finite k] in
@[simp] lemma evalGL_detChar χ (g : GL n k) : (detChar χ).evalGL g = χ g.1.det := by simp [Hall.evalGL, detChar, Matrix.det_eq_sign_charpoly_coeff]
attribute [local simp ←] prod_pow_eq_pow_sum card_eq_pow_finrank finMean_const_mul trace_eq_sum_automorphisms in
attribute [local simp] AlgEquiv.eq_symm_apply exists_fin_succ forall_fin_succ coe_frobeniusAlgEquivOfAlgebraic coe_frobeniusAlgHom pow_card_pow q0 mulMu q4 funext_iff pow_add pow_mul in
variable (k') in
private lemma r6 [Finite L] (hP : Irreducible P) (hL : IsLabel r P) (hx : aeval x P = 0) (hn : finrank k L = r) : ∃ Φ : GalSemidirect k k' (Fin r) → ℂ, IsChar Φ ∧ DescendsTo Φ (greenCuspidal k (thetaChar T (.card k ^ r) x)).mulMu ∧ DescendsTo Φ ((-1 : ℂ) ^ r • (labelChar T (P.map (algebraMap k k'))).mulMu) := by
  obtain ⟨rfl, i : IsIntegral k' x, Q, _, X, q⟩ := hL.2.2.1, .tower_top ⟨P, hL.1, hx⟩,
   @natCard_eq_pow_finrank k k', @finite_of_finite k' (k' ⊗[k] L),
   root_pow_card_pow_pred_eq_one hP hL.2.2.2 hx
  have D {S} {z : K} i s h a := (root_pow_card_pow_eq_self_iff (P := S) i s).symm.trans (Q ▸
   Nat.pow_mul _ _ a ▸ root_pow_card_pow_eq_self_iff hP (x := z) h)
  have G := adjoin.finrank i ▸ D (irreducible i) (by simp) hx; obtain ⟨_, r, hr⟩ := finite_iff_finite.1 (adjoin.finiteDimensional i), (G _).1 dvd_rfl; set N := k'⟮x⟯
  have ⟨g, a, ⟨c, d⟩, H⟩ := (hL.map k').q9 K (p := fun n c ↦ c ∣ P.map _ →
   ∃ b, ∃ a : Fin b → ℕ,
   ((∀ z, aeval z c = 0 → ∃ j, ∃ v < finrank k' N, a j < P.natDegree ∧ z ^ .card k' ^ v = x ^ .card
   k ^ a j) ∧ b * finrank k' N = n) ∧ ∀ B, (-1) ^ n * q0 n (labelChar T c) (mulMu B) =
   finMean fun u : _ → Nˣ ↦ (∏ j, conj (thetaChar T (.card N) (x ^ .card k ^ a j) (u j))) * B
   (simClassOf (LinearMap.mulLeft k' (u · |>.1)))) (by simp [j2, finMean, univ_eq_empty]) (fun S _ _ z m i o s ih h ↦ ?_) dvd_rfl
  obtain ⟨ψ⟩ := nonempty_algHom_of_finrank_dvd ⟨r, hn ▸ finrank_mul_finrank k k' N ▸ hr⟩; let F := frobeniusAlgEquivOfAlgebraic k k'; let n (i : _ × Fin r) := a i.1 + P.natDegree * i.2; let Φ := frobeniusAlgEquivOfAlgebraic k N; let χ a := AlgHom.liftEquiv k k' L N (.comp ↑(Φ ^ a)⁻¹ ψ)
  have I i t : χ 0 (Algebra.TensorProduct.map (F ^ n i).toAlgHom (.id ..) t) = (Φ ^ n i) (χ (a i.1)
   t) := by induction t <;> simp [*]; simp +zetaDelta [smul_def', mul_pow, ← map_pow, ← hn]
  have b := Surjective.bijective_of_nat_card_le (f := (F ^ n ·))
   ((bijective_frobeniusAlgEquivOfAlgebraic_pow ..).2.forall.2 fun u ↦ (c (x ^ .card k ^ u.1) (by
   simpa [hx] using P.aeval_algHom_apply (frobeniusAlgHom .. ^ u.1) x)).elim fun j ⟨v, l, p, t⟩ ↦
   ⟨(j, ⟨_, Nat.div_lt_of_lt_mul (by nlinarith [u.2])⟩), .trans congr(F ^ $(Nat.mod_eq_of_modEq (by
   simpa only [s11_k3 hP hx, Q, ← pow_mul, ← pow_add] using
    t) p ▸ Nat.mod_add_div ..))
   (by ext; simp [F])⟩) (by simp [↓card_aut_eq_finrank]; nlinarith [hP.natDegree_pos])
  let e := equivFinsuppOfBasisLeft (N := L) (finBasis k k').traceDual; let π := AlgHom.pi (χ <| a ·)
  let E := π.toLinearMap.linearEquivOfInjective (fun t u h ↦ e.injective (by
   ext; exact ψ.injective (by simp_all [π, fun t i ↦ (by induction t <;> simp [*, e, add_mul, χ, ← sum_smul, -map_mul] : ψ (e t i) = ∑ τ : Gal(k'/k), χ 0 (map τ.toAlgHom
    (.id k L) (t * finBasis k k' i ⊗ₜ 1))), ← b.sum_comp]))) (by simp [*])
  peel 3 s11_k1 _ _ _ hn (N.val.comp (χ 0))
  refine this _ fun B ↦ .trans (by simp; ac_rfl) ((H B).trans (finMean_equiv ((mapEquiv ⟨E.toEquiv,
   map_mul π⟩).trans .piUnits) fun t ↦
   .symm congr($(?_) * B $(s11_q1 E (map_mul π _)))))
  simp_rw [← b.prod_comp, map_prod, AlgHom.comp_apply, I, Fintype.prod_prod_type]; congr!; erw [s11_j8 T q X Finite.one_lt_card (by rw [← pow_mul, ← hr]; simp) rfl (algebraMap_pow_card_pred_eq_one _)]; simp [n, Φ, prod_range, prod_pow]; rfl
  have R := by simpa [s] using map_dvd (aeval z) h
  obtain ⟨d, ⟨e, w, rfl⟩, b, y, ⟨f, rfl⟩, H⟩ := by simpa [← G, Nat.dvd_right_iff_eq] using D i s R,
   exists_pow_card_pow_eq_of_root hP hx R, ih (.trans (by simp) h)
  use b + 1, cons e y, by simp [-Nat.card_eq_fintype_card]; grind [exists_pow_card_pow_eq_of_root],
   fun B ↦ ?_
  rw [pow_add, map_mul, gt_v2 T i m, z7 s11_j1, d, (funext fun a ↦ .trans ?_ congr((-1) ^
   finrank k' N * $(y0 _ N.val (B <| simClassOf <| ·.out.2.prodMap
   a.out.2)) * _) : q4 _ _ _ = _), mul_assoc, H, finMean_equiv (consEquiv _) (by tauto)]
  simp [↓finMean_prod, finMean, prod_univ_succ, mul_sum, ↓sum_div, sum_comm (α := _ˣ)]; congr! 2
  simpa [field, ← pow_mul] using .inl (congrArg B ((s11_w5 _).rec fun f _ ↦
   (s11_w5 _).rec
   fun e _ ↦ s11_q1 (f.prodCongr e ≪≫ₗ consLinearEquiv _ fun _ ↦ _)))
  simp [mul_comm (finMean _), s11_w4 i o s, d]; ac_rfl
omit [IsScalarTower k k' K] in
lemma b1 {c : k'[X]} (hc : IsLabel r c) (g : GL n k') : (labelChar T c).evalGL (g.map σ) = (labelChar T (c.map σ)).evalGL g := let τ := σ.toRingEquiv; let := τ.toRingHom.toAlgebra
  have A := s11_m3 (K :=
   K) (algebraMap ..) (exists_forall_apply_eq_pow _ _ _ σ).choose_spec
  have ⟨_, _, a, b⟩ := ((hc.q9 K (by simp) fun R _ _ x m p z e h ↦ by
  have i := R.mapEquiv_apply τ ▸ p.map _
  simpa only [map_mul, mapEquiv_apply, gt_v2, m.map, s11_w4 p z e, *, natDegree_map, s11_w4 i (by simpa) (mem_aroots.1 (A _ ▸ Multiset.mem_map.2 ⟨x, by aesop,
   rfl⟩)).2, s11_m0 p z e] using .mul (.y2 fun _ ↦
   s11_x7 (AlgEquiv.ext <| (reindex_equiv σ).1.2 ·.4)
   ((irreducible_criteria_of_isClassFunction _ w3).2.1 (by simp)) (by simp [Hall.evalGL, Matrix.charpoly_map, A])) h :
  Lift ℂ (labelChar T (c.mapEquiv τ)) (labelChar T c)).exists_descendsTo n)
  DescendsTo.iff_comp_inl_eq_evalGL.1 b ▸ a 1 (σ.range_eq_univ.trans (by bound)) _ g rfl
   (by aesop)
lemma lift_detChar {χ χ'} (h : (charName T χ').1 = algebraMap k k' (charName T χ).1) : Lift ℕ (detChar χ) (detChar χ') := fun _ ↦ have ⟨_, a, e, f⟩ := s11_k8 _ ((thetaChar
   T (.card k) (algebraMap k K (charName T χ))).comp (.comp (algebraMap k' K) Matrix.detMonoidHom))
  ⟨_, a.mem_virtualChars, fun σ s ↦ by simp +contextual [DescendsOnCoset, f σ s _, RingHom.map_det, ← thetaChar_charName T, IsScalarTower.algebraMap_apply k k' K], .iff_comp_inl_eq_evalGL.2 (by
   ext g; simpa [← thetaChar_charName T, ↓← map_pow, AlgEquiv.map_det, norm_eq_prod_automorphisms, ← IsScalarTower.algebraMap_apply, ↓← algebraMap_norm_eq_pow_sum, *] using!
    (s11_j8 T Finite.one_lt_card
    (algebraMap_pow_card_pred_eq_one (charName T χ)) Finite.one_lt_card
    natCard_eq_pow_finrank (pow_one _) (algebraMap_pow_card_pred_eq_one g.det)).symm)⟩
omit [Finite k] in
lemma fixed_eq_range_iff_ne_one (hp : (finrank k L).Prime) {σ : Gal(L/k)} : HasFixedField k σ ↔ σ ≠ 1 := by simpa [iff_comm, SetLike.ext_iff, DFunLike.ext_iff, Set.ext_iff, lt_top_iff_ne_top] using! (Subalgebra.isSimpleOrder_of_finrank_prime k _ hp).lt_top_iff_eq_bot (a := σ.toAlgHom.equalizer 1)
lemma DescendsTo.r0 (hp : (finrank k k').Prime) {F G : Hall k} {Φ Ψ : GalSemidirect k k' n → ℂ} (v : IsClassFunction Φ) (w : IsClassFunction Ψ) (l : DescendsTo Φ F) (m : DescendsTo Ψ G) : let N : ℂ := Nat.card Gal(k'/k); N * _root_.classInner Φ Ψ = _root_.classInner
   (Φ ∘ SemidirectProduct.inl) (Ψ ∘ SemidirectProduct.inl) + (N - 1) * q0 (.card n)
   F G := have := (univ.erase 1).sum_congr rfl fun σ e ↦
   (fun s ↦ (v1 s).choose_spec.1.y4.2 (l _ s) (m σ s)
   (by tauto)) (by grind [fixed_eq_range_iff_ne_one])
  by simp_all [↓w0, _root_.classInner, Subgroup.index_ker, ↓SemidirectProduct.rightHom_surjective, Fintype.card_pos, ← mul_sum, ← finMean_sum, sub_eq_iff_eq_add', SemidirectProduct.rightHom_eq_right.trans rfl, field]
lemma shintani_lift_labelChar (hp : (finrank k k').Prime) T [IsFaithfulMulChar K T] {c} (hc : IsLabel r c) : Lift ℕ (labelChar T c) (labelChar T (c.map (algebraMap k k'))) :=
  hc.q9 K (by simp) fun P _ _ x hm hP h0 hx ↦ by
  simp; apply Lift.mul
  obtain ⟨h1 | h1, _, hL : IsLabel ..⟩ := em' (P.IsRoot 1), NeZero.of_pos hP.natDegree_pos,
   ⟨hm, hP.squarefree, rfl, h0⟩
  obtain ⟨hθ, u, M, ⟨B, b⟩, J, v, j, i⟩ := gt_v2 T hP hm ▸ s11_w4 hP h0 hx,
   s11_y9 T hL _ hL, hL.map k', s11_m5 k k' (thetaChar T ..),
   r6 k' T hP hL hx (finrank_extension ..)
  obtain ⟨⟨β, b, d, _⟩, Φ, l, o, _⟩ := b _, hθ ▸ b.y2 _
  obtain ⟨⟨N, t⟩, _⟩ := v.exists_classInner_eq b, j.r0 hp v.isClassFunction
   (isClassFunction_of_mem_virtualChars b) d, x8 T M (by
   simpa [aeval_def]), x8 T hL h1
  refine rankPart_labelChar T M ▸ rankPart_labelChar T hL ▸ .rankPart_of_descendsTo ⟨_,
   ((IsLabel.z3 T (by simpa)).b0 (fun σ g
   ↦ by erw [b1 T σ M]; congr with; simp) l
   (by grind [isClassFunction_of_mem_virtualChars l, Nat.card_fin, o.r0 hp]) (N - 1) ?_).1.mem_virtualChars, by simpa +contextual [DescendsTo, DescendsOnCoset, fixed_eq_range_iff_ne_one, *] using o, by simp⟩
  simp_all [-brauerLift, w0, greenCuspidal, comp_def, q0.eq_1, mul_assoc, mul_left_comm]; grind [neg_one_pow_eq_or]
  simpa [← labelChar_X_sub_C T, eq_of_irreducible_of_monic hP h1 hm] using
   Lift.rankPart_of_descendsTo (@lift_detChar k k' K _ _ _ _ _ _ _ _ _ T _ 1 1 (by simp) 1)
