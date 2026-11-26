import Lib.General.LinearAlgebra.FramedCoefficient
import Lib.DiscreteSeries.FlenstedJensen.TailBounds
import Lib.Weil.DualPair.ModularDataDecay
section
open Ring Matrix Norms.Frobenius Complex intervalIntegral
variable {n} [Fintype n] {P Q X Y : Matrix n n ℂ} {ε h} {l : @HCParam n ε} {δ c : ℝ}
attribute [local simp] mul_add add_mul mul_assoc lie_def IsIdempotentElem.eq
  IsIdempotentElem.mul_self_mul IsStarProjection.isIdempotentElem principalMinor_eq_det coordProj
lemma exists_det_compress_eq_exp_logOneAdd (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hδ :
  δ ≤ 2⁻¹) (hX : ‖X‖ ≤ δ) (h0 : (⁅P, Q⁆ * Y).trace = 0) (h1 : ‖⁅P, X⁆ - Y‖ ≤ δ * c) (hY : ‖Y‖ ≤
  c) (hD : ‖Q - P‖ ≤ c) : ∃ r, (1 + P * X).det = cexp
  ((Q * logOneAdd X).trace - 4⁻¹ * (Y * Y).trace + r) ∧ ‖r‖ ≤ 100 * δ * c ^ 2 := by
  obtain ⟨p, ⟨δ0, _⟩ : 0 ≤ δ ∧ 0 ≤ c⟩ := norm_proj_mul_le hP hX, by grind [norm_nonneg]
  obtain ⟨a, ⟨i, d⟩, j, k⟩ := (norm_le_insert' _ Y).trans (by grw [hY, h1, hδ]),
    trace_mul_logOneAdd (p.trans hδ) 1, trace_mul_logOneAdd (hX.trans hδ) Q
  refine ⟨_, ?_, congr(‖$(integral_add (i.sub j) (.mul_const (continuous_ofReal.intervalIntegrable
    ..) (2⁻¹ * (Y * Y).trace)))‖).ge.trans
    ((norm_integral_le_of_norm_le_const fun s h ↦ ?_).trans (by aesop))⟩
  simp_all [det_one_add_eq_exp_trace_logOneAdd (p.trans hδ), integral_ofReal]; ring
  obtain ⟨⟨⟨_, f, F⟩, w⟩, ⟨_, e, E⟩, v⟩ := inv_one_add_bounds (norm_smul_le_of_le_one s hX),
    inv_one_add_bounds (norm_smul_le_of_le_one s p)
  set W := (1 + s • X)⁻¹; set V := (1 + s • (P * X))⁻¹; set A := ⁅P, X⁆; set D := Q - P
  let Z := W - 1; let N := Z * (A * Z + A) + A * Z
  rw [show _ + _ = trace ((P * D + Q * D - D) * (A - Y + Z * A - s • (N + A) * X)) - trace (s • (P *
    A) * ((N + A) * (V - 1) + N)) - trace ((D - P * D - P * D) * D * (X + Z * X)) - trace ((s / 2) •
    (A - Y) * (A + Y)) by
      linear_combination (norm := (
      simp +zetaDelta [hP, hQ, trace_mul_comm P, trace_mul_comm V, trace_mul_comm Y (_ * _),
        trace_mul_comm X (P * X), mul_sub, sub_mul]; ring))
        h0 + congr(($E * P * W * X * P + V * P * (A * ($F * P * (1 - W) + W * P *
      $f) - $f * X * P) + (1 - P) * $e * P * X - ⁅P, D⁆ * ($F * P * W - W * P * $f) * X).trace)]
  apply le_trans; apply_rules (transparency :=
    .reducible) (maxDepth := 99) [@norm_smul_le_of_le_one, norm_proj_mul_le hP, norm_proj_mul_le hQ,
    @norm_trace_mul_le, norm_sub_le_of_le, norm_add_le_of_le, norm_mul_le_of_le] <;> grind
  nlinarith [mul_nonneg δ0 (sq_nonneg c), sq_nonneg (δ * c)]
lemma exists_principalMinor_eq_exp (hg : l.HasGap h) (g : USign ε) : let X :=
    g.1.1 - 1; ‖X‖ < 1000⁻¹ → ∃ y, l.dsCoeff g = l.flenstedJensen 1 y ∧ ∀ p [DecidablePred p],
    (∀ i j, p i → ¬p j → l i < l j) → ∀ k : maxCompactU ε, let k := k.1.1.1; ∃ r, principalMinor
      (kᴴ * y * k) p = cexp ((coordProj p * logOneAdd X).trace + ‖⁅coordProj p, X⁆‖ ^ 2 / 4 + r)
    ∧ ‖r‖ ≤ 200000 * ‖X‖ * (‖⁅coordProj p, X⁆‖ ^ 2 + ‖⁅coordProj p, k⁆‖ ^ 2) := by
  intro X _; let r l := lowerMask ε l X; let u := r (-l)
  obtain ⟨⟨i, j⟩ : ‖X‖ ≤ 2⁻¹ ∧ 4 * ‖X‖ ≤ 2⁻¹, δ0, hX⟩ := by grind, norm_nonneg X, le_refl ‖X‖
  let y c := (1 - u) * g * (1 - r c); let m := X - u - u * X; have T c : ‖y c - 1‖ ≤ 4 * ‖X‖
  rw [(by grind : _ - 1 = m - r c - m * r c)]; swap
  use y l, ?_, ?_
  · have A c := isAccretive_of_norm_sub_one_lt ((T c).trans_lt (by bound))
    obtain ⟨a, b⟩ :=
      isAccretive_of_norm_sub_one_lt (by bound), by simpa [y, show r 0 = 0 from rfl] using A 0
    have := (flenstedJensen_shift_eq_conj hg (u := (r l)ᴴ) (by simp [r]; grind) (by
      simpa [IsAccretive, add_comm] using b) (by simpa [y, IsAccretive, add_comm] using A l)).trans
      (congrArg _ (flenstedJensen_shift_eq_conj hg (by simp_all [u, r]) a b))
    simp_all [dsCoeff_eq_flenstedJensen hg (one_mem _), y]
  have I p [DecidablePred p] (hp : ∀ i j, p i → ¬p j → l j < l i) : principalMinor (y l) p =
    principalMinor g p := by
    clear * - hp hg; rw [principalMinor_mul, principalMinor_mul, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hg.1, mul_comm, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hg.neg.1] <;> simp [u, r, BlockTriangular] <;> grind
  intro p _ hp κ k; let s := signMatrix ε
  obtain ⟨w : kᴴ * k = 1, o : k ∈ _, hP, d : Commute s (coordProj p)⟩ := (U_one_mem_unitaryGroup ⟨_,
    κ.2⟩).1, mem_maxCompactU.1 κ.2, isStarProjection_coordProj p, commute_diagonal ..
  set P := coordProj p; set A := ⁅P, X⁆; set B := ⁅P, u⁆; set C := ⁅P, r l⁆; set G := B * X + u * A
  let Q := k * P * kᴴ; let V := (1 + X)⁻¹ - 1; let H := G + m * C - (G + B - A) * r l
  have ⟨N, E⟩ : (∀ c, ⁅P, r c⁆ = lowerMask ε c A) ∧ B = blockDiagPart ε A - C := by
    simp +zetaDelta [← ext_iff, blockDiagPart]; grind
  have M x : (1 + (1 - P) * (x - 1)).det =
    principalMinor x (¬p ·) := by simp [P, det_apply, sub_mul]; grind
  obtain ⟨R, a, b, W, _ : Pᴴ = P, _, _, _ : gᴴ = s * g.1.1⁻¹ * s⟩ := hP.one_sub, norm_nonneg A,
    norm_nonneg ⁅P, k⁆, mul_eq_one_symm w, hP.2, (inv_one_add_bounds hX i).2,
    (N · ▸ norm_entryMask_le), by grind [U.inv_mat, signMatrix_mul_self]
  have := ((by simp [Q, mul_sub, ← mul_assoc, *] : k * ⁅P, k⁆ᴴ =
    P - Q) ▸ frobenius_norm_mul_of_unitary w _).trans_le (norm_star _).le
  have ⟨x, e, _⟩ := exists_det_compress_eq_exp_logOneAdd R R i hX ?_ (by simp [A, mul_sub, sub_mul,
    mul_nonneg]) (norm_neg A).le (by simp)
  have ⟨z, f, _⟩ := exists_det_compress_eq_exp_logOneAdd (Y :=
    B + C - A) (c := 4 * ‖A‖) R R j (T l) ?_ ?_ ?_ (by simp)
  have ⟨t, q, _⟩ := exists_det_compress_eq_exp_logOneAdd (P := Q) (Y := A - B - C) (c := 4 * (‖A‖ +
    ‖⁅P, k⁆‖)) (hP.map (Unitary.conjStarAlgAut ℂ _ ⟨k, w, W⟩)) hP j (T l) ?_ ?_ ?_ (by linarith)
  rw [M, I _ (by tauto), ← M, e] at f
  use t + z - x + ((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace, .trans (by
    simp [det_one_add_mul_comm k, Q, P]; noncomm_ring [w]) (q.trans (mul_right_cancel₀ (by simp)
    (congr(_ * ($f * $((det_one_add_eq_exp_trace_logOneAdd ((T l).trans j)).symm.trans
    (.trans (by simpa [principalMinor_of_forall, X] using I ⊤)
    (det_one_add_eq_exp_trace_logOneAdd i))))).trans ?_))), ?_
  on_goal 7 => rw [(by simp +zetaDelta; noncomm_ring : _ - _ = H)]
  on_goal 4 => rw [(by simp +zetaDelta; noncomm_ring :
    _ - _ = (y l - 1) * (P - Q) - (P - Q) * (y l - 1) - H)]
  any_goals (apply le_trans; apply_rules (transparency := .reducible) [norm_entryMask_le.trans,
    @norm_smul_le_of_le_one,
    @norm_trace_mul_le, norm_sub_le_of_le, norm_add_le_of_le, norm_mul_le_of_le, le_rfl]; on_goal
    -1 => first | nlinarith only [δ0, j, b, mul_nonneg δ0 a, mul_nonneg δ0 (sq_nonneg ‖A‖),
                mul_nonneg δ0 (sq_nonneg (‖A‖ - ‖⁅P, k⁆‖))] | nlinarith)
  all_goals simp [Q, V, s, *, blockDiagPart_eq, d.eq, trace_mul_comm P,
    (mem_blockDiagAlg_iff_commute.1 o).left_comm, ← ofReal_pow,
    A, X, inv_eq_left_inv w ▸ blockDiagAlg.inv_mem o _ rfl, trace_mul_comm k, trace_mul_comm kᴴ,
    trace_mul_comm s, signMatrix_mul_self, ← mul_assoc s s, ← exp_add, mul_sub, sub_mul,
    ← trace_star_mul_self_eq_norm_sq, inv_le_one₀] <;> ring_nf
end
section
open Matrix MeasureTheory Finset Fintype Ring Complex ComplexOrder Norms.L2Operator Norms.Frobenius
variable {n} [Fintype n] {ε} {l : @HCParam n ε} {δ T : ℝ} {L A : ℕ} (w : n → ℤ)
  (X : Matrix n n ℂ)
noncomputable abbrev gapWeightedNormSq := ∑ i, ∑ j, |w i - w j| * ‖X i j‖ ^ 2
lemma sum_norm_lie_coordProj_sq : letI a := ∑ j, |w j|; ∑ t ∈ Ioc (-a) a, ‖⁅coordProj (t ≤ w ·),
    X⁆‖ ^ 2 = gapWeightedNormSq w X ∧
    ∑ t ∈ Ioc (-a) a, (coordProj (t ≤ w ·) * X).trace = ∑ i, (w i + a) * X i i := by
  have := neg_sum_abs_le_and_le_sum_abs w; simp [frobenius_norm_sq_eq_sum, coordProj, lie_def,
    trace, (Ioc ..).sum_comm, ite_sub, sub_ite,
    apply_ite norm, ← Order.lt_add_one_iff]; simp [sum_ite, ← add_mul,
    ← Ico_add_one_add_one_eq_Ioc, -Order.lt_add_one_iff, -Order.add_one_le_iff]
  constructor <;> congr! <;> norm_cast <;> grind
lemma norm_weightMinors_sq_le_exp (k : maxCompactU ε) : ‖weightMinors w k‖ ^ 2 ≤
  (-(gapWeightedNormSq w k / 2)).exp := by
  simp [weightMinors_eq_det_zpow_mul_prod _ _ _ (neg_sum_abs_le_and_le_sum_abs w),
    ← sum_norm_lie_coordProj_sq, sum_div, ← sum_neg_distrib, Real.exp_sum,
    ← prod_pow]; gcongr with t; have ⟨a, b⟩ := isStarProjection_coordProj (t ≤ w ·)
  nth_rw 1 [principalMinor_eq_det, ← coordProj, ← a, mul_assoc, det_one_sub_mul_comm, sq,
    ← norm_star, ← norm_mul,
    ← det_conjTranspose, ← det_mul, (isHermitian_conjTranspose_mul_self _).det_eq_prod_eigenvalues]
  grw [norm_prod, (Real.add_one_le_exp _).trans_eq' (sub_add_cancel ‖_‖ 1)]
  simp [← Real.exp_sum, abs_of_nonneg (eigenvalues_conjTranspose_mul_self_nonneg ..),
    ← real_le_real, ↓← trace_star_mul_self_eq_norm_sq, -conjTranspose_sub]
  erw [← (isHermitian_conjTranspose_mul_self _).trace_eq_sum_eigenvalues]
  simp [lie_def, b.isHermitian.eq, mul_sub, sub_mul, mul_assoc, ← maxCompactU.coe_inv, a.eq,
    (coordProj _).trace_mul_comm, trace_mul_comm _⁻¹ (_ * _)]
  grind
lemma dsCoeff_gaussian_shape [Nonempty n]
    (hg : l.HasLargeGap A) (hL : ∀ a, |l a| ≤ L) {g : USign ε} (hZ : ‖g.1.1
  - 1‖ ≤ δ) (hT : 1 ≤ T) (a : card n ^ 2 ≤ T := by nlinarith) (b : card n ^ 2 * Real.log (card n +
  L + 1) ≤ T := by bound) (hδ : δ * T ≤ 1e-12 := by bound) : ∃ κ ∈ Set.Icc (0 : ℝ) 1, ‖l.dsCoeff g /
  (intDiagonal l.lowestKType * logOneAdd (g.1.1 - 1)).trace.exp - κ‖ ≤ κ / 10 + (-100 * T).exp := by
  obtain ⟨this, ⟨y, y1, y2⟩, H0, t, h⟩ := (norm_nonneg _).trans hZ,
    exists_principalMinor_eq_exp hg g (by nlinarith), kTypeNormSq_pos l.lowestKType,
    (norm_exp_sub_sum_le_exp_norm_sub_sum · 1), measure_ball_le_integral_dsCoeff hL
    (haarK ε) (maxCompactU ε).subtype integrable_of_compactSpace 1 le_rfl
  simp [↓← ENNReal.ofReal_mul', le_of_lt, dsCoeff_of_mem_maxCompactU, unitary, star,
    @CStarRing.norm_of_mem_unitary _ instL2OpNormedRing, ← maxCompactU.coe_inv] at h t
  simp (disch := positivity) [← Real.log_nonneg_iff, Real.log_mul] at h
  repeat grw [Real.log_le_self Nat.ofNat_pos.le] at h
  let q := gapWeightedNormSq (-paramAddRho l) (g - 1) / 4
  use q.exp⁻¹, ⟨by bound, by simp [field]; positivity⟩
  set E := @trace ..
  have d k := by simpa [principalMinor_of_forall, coordProj, lie_def, -det_mul] using (y2 ⊤ · k)
  choose r e hr using fun k : maxCompactU ε ↦ show ∃ r, weightMinors _ _ =
    (q - E - r).exp ∧ ‖r‖ ≤ 1e6 * δ * (q + gapWeightedNormSq l.lowestKType k / 2 + card n ^ 2) by
    choose x f i using fun t ↦
      y2 (t ≤ (-paramAddRho l) ·) (by simp [← hg.paramAddRho_lt_iff]; lia) k
    refine ⟨_, by rw [weightMinors_eq_det_zpow_mul_prod (d k ▸ exp_ne_zero _) _ _
      (neg_sum_abs_le_and_le_sum_abs _), d, funext f,
      ← exp_int_mul, ← exp_sum, ← exp_add, sub_sub_self], ?_⟩
    simp_rw [sum_add_distrib, ← sub_sub, sum_norm_lie_coordProj_sq, ← sum_div, add_mul]
    conv_lhs => enter [1, 1]; simp [lowestKType, E, q, trace, sub_mul, mul_sum,
      ← sum_norm_lie_coordProj_sq]; ring
    grw [norm_sub_le, norm_sum_le, norm_sum_le, i, ← mul_sum, norm_mul_le_of_le (r₁ := card n)
      (mod_cast abs_twoRho_le ..)
      ((norm_logOneAdd_le (hZ.trans (by nlinarith))).trans' (by grw [← sq_le_sq₀,
      frobenius_norm_sq_eq_sum, ← single_le_sum, ← single_le_sum] <;> simp [sum_nonneg'])), hZ,
      sum_add_distrib, (sum_norm_lie_coordProj_sq ..).1, (sum_norm_lie_coordProj_sq ..).1.trans_le
      (c := gapWeightedNormSq l.lowestKType k + 2 * card n * re (k.1.1.1ᴴ *
      k).trace) (by simp [gapWeightedNormSq, trace_star_mul_self_eq_norm_sq,
                      frobenius_norm_sq_eq_sum, mul_sum, ← sum_add_distrib, ← add_mul, -ofReal_pow]
                    gcongr; norm_cast; grind [lowestKType, twoRho])]
    simp [q, ← sub_nonneg, ← maxCompactU.coe_inv]; ring; positivity
  grw [y1, flenstedJensen, div_right_comm, div_sub' (by positivity), norm_div,
    Complex.norm_of_nonneg H0.le,
    div_le_iff₀ H0, ← integral_div, ← integral_complex_ofReal, ← integral_mul_const, ← integral_sub
    (integrable_of_compactSpace (by fun_prop (disch := simp [*]))) integrable_of_compactSpace,
    add_mul, ← integral_const_mul, ← average_const (haarK ε) (_ * _), average_eq_integral,
    ← integral_add integrable_of_compactSpace integrable_of_compactSpace]
  refine norm_integral_le_of_norm_le integrable_of_compactSpace (.of_forall fun k ↦ ?_)
  simp [e, mul_conj', exp_sub]; field_simp
  simp
  by_cases ‖r k‖ < 20⁻¹
  · grw [norm_exp_sub_one_le, ← H0] <;> nlinarith
  grw [← sq_nonneg, zero_add, t, sub_one_lt, norm_weightMinors_sq_le_exp, ← Real.exp_log H0]
  field
  simp [← Real.exp_add]
  nlinarith [hr k, le_mul_of_one_le_right this hT]
end
section
noncomputable section
open Finset Matrix Norms.Frobenius Complex ComplexConjugate Set ComplexOrder Int HCParam Sgn
variable {n m X S : Type} [Fintype n] [Fintype m] [Fintype X] [Group S] {ε} (l : @HCParam n ε) {η}
  (k : @HCParam m η) (j : S →* USign ε × USign η) (τ : X → m) (B : ℝ) {M} (e : X ⊕ Fin M ≃ n) (φ :
  S → ℂ) {u : Matrix X X ℂ}
def HCParam.phase (x : Matrix n n ℂ × Matrix m m ℂ) :=
  (intDiagonal l.lowestKType * x.1).trace - (intDiagonal k.lowestKType * x.2).trace
structure IsSteep where
  sign_inl x : ε (e (.inl x)) = 1
  sign_inr i : ε (e (.inr i)) = (-1) ^ i.1
  weight_eq_zero x : l.lowestKType (e (.inl x)) = 0
  weight_strictAnti : StrictAnti fun i ↦ l.lowestKType (e (.inr i))
  weight_mem i : (l.lowestKType (e (.inr i)) : ℝ) ∈ Icc (-3 * B) (-B)
abbrev subOnePair s := ((j s).1.1.1 - 1, (j s).2.1.1 - 1)
def HCParam.laplaceIntegrand s := l.dsCoeff (j s).1 * conj (k.dsCoeff (j s).2) * cexp (-φ s)
structure IsTwoFactor extends IsSteep l B e where
  phase_eq s : l.phase k (subOnePair j s) = φ s
  trace_eq s : (subOnePair j s).1.trace = (subOnePair j s).2.trace
  phase_mul s t : φ (s * t) = φ s + φ t
  re_phase s : (φ s).re = 0
  sign_weight_right x : η (τ x) = 1 ∧ k.lowestKType (τ x) = 0
  weight_bounds_right i i' : 0 ≤ k.lowestKType i ∧ (η i ≠ η i' → k.lowestKType i ≤ 3 * B)
  exists_diagonal : ∀ u ∈ unitaryGroup X ℂ, ∃ s, subOnePair j s = (inclMatrix ℂ (e ∘ .inl) *
    (u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ, inclMatrix ℂ τ * (u - 1) * (inclMatrix ℂ τ)ᴴ)
attribute [local simp] diagonal_apply phase Matrix.mul_apply
lemma exists_unitary_sub_one_eq_inclMatrix {Y} [Fintype Y] (e : X ⊕ Y ≃ n) (h : ∀ x,
  ε (e (.inl x)) = 1) (k : uᴴ * u = 1) : ∃ s : USign ε, s.1.1 - 1 =
  inclMatrix ℂ (e ∘ .inl) * (u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ := ⟨U.of IsHermInvolution.isUnit _
  (by simp_all [← ext_iff, inclMatrix, signMatrix, reindex_equiv e]), add_sub_cancel_left ..⟩
lemma norm_sq_add_re_trace_le (g : USign ε) (a C : ℝ) (v w : n → ℤ) (h : ∀ i j, a * v i ^ 2 ≤ w i ∧
    (ε i ≠ ε j → w i ≤ C)) : a * ‖intDiagonal v * (g.1.1 - 1)‖ ^ 2 + 2 *
  (intDiagonal w * (g.1.1 - 1)).trace.re ≤ 2 * C * ‖g.1.1 - blockDiagPart ε g‖ ^ 2 := by
  rw [(?_ : 2 * _ = (intDiagonal w * ((g - 1) * (1 - g.1⁻¹))).trace.re)]
  simp [frobenius_norm_sq_eq_sum, trace, mul_sum, ← sum_add_distrib, blockDiagPart, eq_comm]
  gcongr with i _ j; cases h i j
  split_ifs <;> simp_all [mul_right_comm, ← cast_mul, mul_pow,
    Complex.sq_norm, normSq, signMatrix, U.inv_mat] <;> nlinarith
  simp [↓mul_sub, ↓sub_mul, ↓Units.mul_inv, trace, signMatrix, U.inv_mat, mul_right_comm,
    ← cast_mul]; ring
variable {l k j τ B e φ}
lemma IsTwoFactor.phase_logOneAdd (H :
  IsTwoFactor l k j τ B e φ) s (a : ‖(subOnePair j s).1‖ ≤ 2⁻¹) (b : ‖(subOnePair j s).2‖ ≤ 2⁻¹) :
  l.phase k ((subOnePair j s).map logOneAdd logOneAdd) = φ s := by
  have p i t : l.phase k (subOnePair j s ^ i * subOnePair j s * (1 + subOnePair j t)) = 0 ^ i * φ
    s := by induction' i with i h generalizing t <;> [have := H.phase_mul s t; have := h (s *
    t)] <;> simp_all [← H.phase_eq, pow_succ, sub_mul, mul_sub] <;> grind
  have := intervalIntegral.integral_congr_Ioo_of_le (μ := by volume_tac) zero_le_one fun r o ↦
    have G {n} [Fintype n] {X D : Matrix n n ℂ} (h : ‖X‖ ≤ 2⁻¹) :=
      ((hasSum_geom_series_inverse (-r • X) (by simp; grind [norm_smul_le_of_le_one r h])).mul_right
      X).mapL (traceLinearMap .. ∘ₗ .mulLeft ℂ D).toContinuousLinearMap
    ((G a).sub (G b)).unique (hasSum_single 0 fun i _ ↦ by
      simpa [↓smul_pow, *] using Or.inl (p i 1))
  simp_all [← H.phase_eq, trace_mul_logOneAdd, ← nonsing_inv_eq_ringInverse]
open MatMul
lemma dsCoeff_mul_eq_of_zero_weight_block {σ} (z : ∀ x : X, ε (σ x) = 1 ∧ l.lowestKType (σ x) = 0)
  {k g t : USign ε} (hk : k.1.1 - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) (e : t = k * g) :
  intDiagonal l.lowestKType * (k.1.1 - 1) = 0 ∧ l.dsCoeff t =
  l.dsCoeff g ∧ ‖t.1.1 - 1‖ ^ 2 + 2 * (t.1.1 - 1).trace.re ≤ 2 * ‖g.1.1 - blockDiagPart ε g‖ ^ 2 :=
  have F i j : i ∉ range σ ∨ j ∉ range σ → k.1 i j = ite (i = j) 1 0 := by
    simp_all [or_imp, sub_eq_iff_eq_add, inclMatrix, eq_comm]
  have M x : weightMinors l.lowestKType (k * x) = weightMinors l.lowestKType x :=
    finprod_congr fun t ↦ by rw [principalMinor_mul (by grind), principalMinor_eq_det,
    (?_ : 1 - _ = ite (t ≤ 0) k.1.1 1)] <;> split <;> simp [field, ← ext_iff] <;> grind
  have c : ↑k ∈ blockDiagAlg ε := by grind [mem_blockDiagAlg]
  ⟨ext (by simp; grind), by
    simpa [*, ← frobenius_norm_mul_of_unitary (U_one_mem_unitaryGroup ⟨_, mem_maxCompactU.2 c⟩).1
      (g - _), dsCoeff, flenstedJensen] using norm_sq_add_re_trace_le t 1 1 1 1⟩
lemma norm_dsCoeff_pow_four_le {h} [hg : l.HasLargeGap h] (g : USign ε) : ‖l.dsCoeff g‖ ^ 4 ≤
  (1 + ‖g.1.1 - blockDiagPart ε g‖ ^ 2)⁻¹ ^ h := by
  have b (X : Matrix n n ℂ) (H := X.posSemidef_conjTranspose_mul_self) (e := H.eigenvalues_nonneg) :
      1 + ‖X‖ ^ 2 ≤ ‖(Xᴴ * X).charpoly.eval (-1)‖ := by
    rw [← ofReal_re (_ ^ 2), ← trace_star_mul_self_eq_norm_sq]; simpa [H.1.charpoly_eq,
      Polynomial.eval_prod, ← neg_add',
      -neg_add_rev, *, H.1.trace_eq_sum_eigenvalues, add_nonneg, ← re_eq_norm.2] using
      univ.induction_on (by simp) (by simp_intro a s ..; nlinarith [e a, s.sum_nonneg' e])
  grw [b, eval_charpoly, (?_ : _ - _ = -((blockDiagPart ε g)ᴴ * blockDiagPart ε g)), pow_mul _ 2 2,
    det_neg, (le_div_iff₀ _).2 (norm_dsCoeff_sq_mul_det_pow_le_one hg (by bound) g)] <;> simp [sq,
    mul_pow, ↓map_neg]
  linear_combination (norm := (simp [blockDiagPart_eq, IsHermInvolution.mul_self,
    IsHermInvolution.isHermitian.eq]; module)) congr(blockDiagPart ε ($(g.2) * signMatrix ε))
lemma IsTwoFactor.exists_near_one (H : IsTwoFactor l k j τ B e φ) r (hB : 1 ≤ B) (e0 : 0 < r) (he :
  r ≤ 100⁻¹) s (h : ‖(j s).1.1.1 - blockDiagPart ε (j s).1‖ ^ 2 + ‖(j s).2.1.1 - blockDiagPart η
  (j s).2‖ ^ 2 ≤ r ^ 2) : ∃ t, l.laplaceIntegrand k j φ s =
  l.laplaceIntegrand k j φ t ∧ ‖(subOnePair j t).1‖ ≤ 10 * r ∧ ‖(subOnePair j t).2‖ ≤ 10 * r := by
  let χ i : ℤ := (e.symm i).elim 0 1
  obtain ⟨K, R⟩ := H.exists_diagonal, norm_sq_add_re_trace_le (j s).1 B (3 * B) χ (-l.lowestKType),
    H.phase_eq s ▸ H.re_phase s, norm_sq_add_re_trace_le (j s).1 (-1) 0 χ (-χ),
    norm_sq_add_re_trace_le (j s).2 0 _ 0 _ (mod_cast H.weight_bounds_right)
  set Q := inclMatrix ℂ _
  have : Qᴴ * Q = 1 ∧ intDiagonal χ = 1 - Q * Qᴴ ∧ signMatrix ε * Q = Q := by
    simp [← ext_iff, reindex_equiv e, Q, inclMatrix, signMatrix, χ, H.sign_inl]
  simp [reindex_equiv e, χ, H.weight_eq_zero, ← diagonal_neg, -Matrix.mul_sub, -Matrix.sub_mul] at *
  set c := _ * (subOnePair j s).1
  have : ‖c‖ ^ 2 ≤ 6 * r ^ 2 := by nlinarith [R (by bound) (by grind [IsTwoFactor, IsSteep])]
  have ⟨⟨_, f, _⟩, v⟩ := inv_one_add_bounds (norm_smul_of_nonneg one_half_pos.le c).le
  set W : Matrix n n ℂ := _⁻¹
  let N := (subOnePair j s).1 * W * Q
  have a := mem_unitaryGroup_iff (A := 1 + Nᴴ * Q).2 (by
    linear_combination (norm := (simp [star, N, c, *, IsHermInvolution.isHermitian.eq,
      ← (signMatrix ε).mul_assoc Q]; module)) congr(Qᴴ * Wᴴ *
      $((j s).1.2) * W * Q - (signMatrix ε * $f * Q)ᴴ * N - Nᴴ * signMatrix ε * $f * Q))
  let ⟨s₀, h₁, h₂⟩ := K _ a
  let T := (subOnePair j (s₀ * s)).1
  obtain ⟨k₁, k₂⟩ := dsCoeff_mul_eq_of_zero_weight_block (⟨H.sign_inl ·, H.weight_eq_zero _⟩)
    h₁ congr($(j.map_mul _ s).1), H.trace_eq _ ▸ dsCoeff_mul_eq_of_zero_weight_block
    H.sign_weight_right h₂ congr($(j.map_mul _ s).2), ((re_le_norm _).trans (norm_trace_mul_le
    (norm_sub_le T c) v)).trans_eq' (by linear_combination (norm := (simp +zetaDelta
    [eq_add_of_sub_eq h₁, Q.trace_mul_comm, star, ← Qᴴ.mul_assoc Q, *]; ring)) congr(($(a.2) +
    Nᴴ * Q * Qᴴ * $f * Q).trace.re) : _ = c.trace.re - T.trace.re), sq_nonneg (‖T‖ - 2 * ‖c‖)
  use s₀ * s, by simp [laplaceIntegrand, H.phase_mul, ← H.phase_eq, ↓k₁, ↓k₂], ?_, ?_ <;> nlinarith
end
end
open MeasureTheory Matrix Space G EuclideanSpace Fintype Set Measure Subtype U Norms.L2Operator
  ComplexConjugate
lemma norm_poincare_period_sub_le {E n s} [Field E] [CMType E] [Fintype n] {V : Space E n s}
  [StablyUnram E] {F S a R A d} (hF : V.IsAutomorphic F) (hS : ∀ g, ‖F g‖ ≤ S) (ha : a ≠ 0) {l : _ →
    @HCParam (n ⊕ Unit) (s ⊕ᵥ 1)} (hl : HasLevel F (principalLevel n a)) (hR : ∀ w,
  R ≤ ‖Φ w a.val‖) (hA : 2 * numInfPlaces E * (card n + 1) + 2 ≤
  A) (hB : 8 * (card n + 1) ^ 2 < A) (hg : ∀ w, (l w).HasLargeGap (2 * A)) (R0 : 0 ≤ R) x (hx :
  d ^ 2 ≤ R * (V.move x).firstMinimum) (hd : numInfPlaces E ≤ d) (hD : 10 ≤ d)
  (ω α : GInf ..) : let φ (g : GInf ..) := ∏ w, conj ((l w).dsCoeff ((α w)⁻¹ * g w * ω w :))
  let ψ g (r : GInf E s) := φ (g * inl s _ ∘ r)
  let L := ∏ w, (2 * (‖(α w).1.1‖ * ‖(ω w).1.1‖) ^ 2) ^ A *
    (16 ^ A * volume.real {r : USign s | ‖r.1.1 - 1‖ ≤ 1})
  let Z := V.sum (signedSpace (n := Unit) E 1); let i := sum.comp (.inl ..)
    let v :=
      volume.real (SetLike.coe (principalLevel n a)); let X (γ : Z.Γ) h := (i x)⁻¹ * γ.1 * i h
      let K γ h := φ (X γ h).1 * indicator (principalLevel (n ⊕ Unit) a) 1 (X γ h).2
      Integrable (ψ 1) ∧ ‖∫ h, ∑' γ, K γ h * F h ∂V.quotMeasure - v • realConv (ψ 1) F x‖ ≤
        v * L * S * (10 / d) := by
  intro φ ψ L Z j v X K
  have hL g t (h : 0 < t) (e : ∀ r : _ → _, t ≤ ∏ w, ‖(g w * inl s _ (r w)).1.1‖) :
    Integrable (ψ g) ∧ ∫ r, ‖ψ g r‖ ≤ L * t⁻¹ ^ A := open Finset in by
    have k w := integral_decay_le volume isProperMap_inl (by simpa) (g w)⁻¹
    refine have i := (Integrable.fintype_prod (k · |>.1.comp_inv.const_mul _)).mul_const _
      have N := ae_of_all _ fun r ↦ ?_; ⟨i.mono' (Continuous.aestronglyMeasurable (by fun_prop)) N,
      (integral_mono_of_nonneg (.of_forall (by simp)) i N).trans <| by
      simp_rw [integral_mul_const, L, prod_mul_distrib, integral_const_mul]; gcongr
      simpa [← fromBlocks_one', sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, mul_pow] using
        (integral_fintype_prod_eq_prod _).trans_le (prod_le_prod₀ (by positivity [·, ·]) fun w _ ↦
        (integral_inv_eq_self ..).trans_le (k w).2)⟩
    grw [e r, ← prod_inv_distrib, ← Finset.prod_pow, ← prod_mul_distrib, norm_prod]; gcongr
    nth_grw 1 [Complex.norm_conj, norm_dsCoeff_le_pow (hg _) (by bound), pow_mul, ← mul_pow,
      ← mul_pow, map_inv, ← _root_.mul_inv_rev, U.norm_inv, ← U.norm_inv (ω _)]
    gcongr; have (x : type_of% (α ‹_›).1) := x.norm_pos; simp only [field, *]
    grw [← mul_pow, ← mul_pow, mul_comm ‖_‖, ← norm_mul₃_le]; simp [mul_assoc]
  have H g := (hL g 1 one_pos (by simp [↓le_prod_opNorm])).1; use H 1
  choose y hy using
    (fun ⟨_, g, rfl⟩ ↦ ⟨g.1.1 *ᵥ (0 ⊕ᵥ 1), by simp [↓move_vecAtPoint, ↓← ratEmbed_mulVec_vecAtPoint,
    funext_iff, Z, j, ↓sum_vecAtPoint, Space.vecAtPoint, signedSpace, entrywise]⟩ :
    ∀ γ : Z.Γ, ∃ y, ∀ k u, (Z.move u).vecAtPoint y = (u⁻¹ * γ * j k).mat *ᵥ Pi.single (.inr ()) 1)
  have ⟨C, hC, h1⟩ := (j.range.subgroupOf Z.Γ).exists_isComplement_left 1
  let W := {γ : C | ∃ k, (X γ k).2 ∈ principalLevel _ a}
  have key {u k} (hu : (X u k).2 ∈ principalLevel _ a) h :
      K u (k * h) = ψ (X u k).1 h.1 * indicator (principalLevel n a) 1 h.2 := by
    simp [K, X, ← mul_assoc, indicator]; congr!
    erw [mul_mem_cancel_left hu]; simp [principalLevel, mem_Kf, ← mat_snd, j,
      (show ∃ y ∈ Ô E, 0 = · * y by use 0; simp)]
  have M {W} [RCLike W] {f : _ → W} hf := ((measurePreserving_orbitMeasure.comp
    (measurePreserving_swap (ν := V.quotMeasure))).fubini (f := f) hf).elim fun i e ↦
    And.intro i.prod_right_ae (e ▸ hasSum_integral_measure i.integral_prod_left)
  let f (γ : W) := (Z.move (j x)).archCoords (y γ); let o : W := ⟨⟨_, h1⟩, x, by simp [X]⟩
  choose k h using @mem _ W
  have sep : Pairwise (d ^ 2 ≤ ‖f · - f ·‖) := fun γ γ' ne ↦ by
    obtain ⟨w, hw⟩ := MulAction.surjective₀ (a.ext.mt ha) (y γ - y γ')
    grw [← map_sub, ← hw, hx, ((le_inf le_rfl (by grw [← one_le_firstMinimum]; simp)).trans
      inf_le_firstMinimum_sum).trans ((Z.move (j x)).firstMinimum_le (fun i ↦ ?_) fun e ↦
      ne (val_injective (hC.leftQuotientEquiv.symm.injective (QuotientGroup.eq.2 ((((mem_range_sum
      stdForm_sum).1 (by simp)).2 ?_).imp' toUnitary.symm fun _ ↦ (toUnitary.injective <| .trans (by
      ext : 2; exact (mat_sum _).trans (by simp; rfl)) ·)))))), ← norm_smul_of_nonneg R0]
    simp [norm_eq, archCoords, -algebraMap_smul, mul_pow]; grw [← hR]
    choose t ht e using (h · |>.2 i (.inr ())); convert sub_mem (ht γ) (ht γ')
    use (isUnit_algebraMap_finAdele ha).mul_left_cancel (by
      simpa [mul_sub, ← e, fun γ ↦ hy γ.1 (k γ), X,
                        -mat_mul, ↓map_smulₛₗ] using! congr(((Z.move _).vecAtPoint $hw i).2))
    simpa [mat, ← ext_iff, hy _ 1, e, eq_sub_iff_add_eq, Unique.forall_iff] using
      (congr((Z.move γ).vecAtPoint $hw ·))
  obtain ⟨m, _, _, O : ‖f o‖ ≤ d⟩ := (isOpen_principalLevel (n := n) ha).measurableSet,
    C.to_countable.to_subtype, (norm_nonneg _).trans (hS x), by simp [hd.trans', hy _ x, o, f,
    archCoords, -mat_mul, sum_prod_type, norm_eq, NeZero.one_le]
  have N (γ : Elem {o}ᶜ) : d ^ 2 / 2 ≤ ‖f γ‖ := by nlinarith [(sep γ.2).trans (norm_sub_le ..)]
  have T := tsum_inv_pow_le_of_separated (by bound) (by nlinarith [@sep · · <| coe_ne_coe.2 ·]) N
    (by simpa [← mul_assoc])
  have J γ := ((integrable_congr (ae_of_all volume (key (h γ)))).2 ((H _).mul_prod (((
    integrableOn_const (by simp)).mono_set principalLevel_le_Kf).integrable_indicator
    m))).comp_mul_left (k γ)⁻¹
  simp [Subgroup.smul_def, -Subtype.forall] at M J
  have I γ := (J γ).mul_bdd hF.1.aestronglyMeasurable (.of_forall hS)
  have b (γ : Elem {o}ᶜ) : _ ≤ v * L * S * d ^ A * ‖f γ‖⁻¹ ^ A := (integral_mono (I γ).norm
    ((J γ).norm.mul_const S) (by grw [norm_mul, hS ·])).trans <| by
    rw [integral_mul_const, ← integral_mul_left_eq_self _ (k γ)]
    simp [key, h, volume_eq_prod, norm_indicator_eq_indicator_norm]
    grw [integral_prod_mul (‖ψ _ ·‖), (hL _ (‖f γ‖ / d) (by grw [← N]; bound) fun r ↦ by
      grw [(mem_and_norm_le_of_vecAtPoint _ _ _ (X γ (k γ * (r, 1))).mat 1
        (le_prod_opNorm (X γ _).1).2 _).2,
        O] <;> simp [hy 1 x, hy γ (k γ * (r, 1)), X, o, -mulVec_single, mul_assoc, field]
      rfl).2] <;> simp [m]; linear_combination
  convert! (((hasSum_singleton ..).hasSum_iff_compl.1 ((hasSum_integral_of_summable_integral_norm
    (fun p : _ × _ ↦ (M (I p.1)).1 p.2) ((summable_prod_of_nonneg (by positivity [·])).2 ⟨(I ·
    |>.norm |> M |>.2.summable), .compl_add (.of_nonneg_of_le (by simp; positivity [·])
    ((M (I _).norm).2.tsum_eq.trans_le <| b ·) (T.1.mul_left _)) .of_finite⟩)).prod_fiberwise
    (I · |> M |>.2))).norm_le_of_bounded (T.1.hasSum.mul_left _) (b · |>.trans'
    (norm_integral_le_integral_norm _))).trans _ with h
  rw [← (hC.1.comp (val_injective.prodMap (g := fun δ : V.Γ ↦
    ⟨⟨_, by simp [Z, sum_mem_Γ]⟩, δ, rfl⟩) _)).tsum_eq (hC.2.forall.2 _)]
  simp [hF.2, K, X, mul_assoc]; rfl
  simp_intro _ [isClosedEmbedding_sum.1.2.eq_iff]
  rintro ⟨σ, ⟨_, e⟩, δ, ⟨⟩⟩ m; exists ⟨⟨σ, δ * h, by
    simp [K, X, mul_assoc] at m ⊢; tauto⟩, δ, ((sum_mem_Γ ..).1 e).1⟩
  erw [← integral_mul_left_eq_self _ x, ← mul_smul_one, ← integral_indicator_const _ m,
    ← integral_prod_mul]
  simp [key, indicator, X, o]; congr! 3
  simp [← hl _ ‹_› (x * (_, 1)), mul_assoc]
  grw [mul_assoc, T.2, ← mul_pow, pow_le_of_le_one _ _ (by omega)] <;> field_simp <;> linarith
open Complex Real HCParam
lemma IsTwoFactor.laplace_method {n m X S} [Fintype n] [Fintype m] [Fintype X] [Group S]
  [TopologicalSpace S] [MeasurableSpace S] [MeasurableMul S] [BorelSpace S] (ν : Measure S)
  [ν.IsMulRightInvariant] [IsFiniteMeasureOnCompacts ν] {ε l η k τ} {B β : ℝ} {L M h : ℕ} [Nonempty
  n] [Nonempty m] {e : X ⊕ Fin M ≃ n} {j : S →* USign ε × _} {φ} (H : IsTwoFactor l k j τ B e φ)
  (hg : l.HasLargeGap h) (hg' : @HasLargeGap m _ η k h) (hB : 1 ≤ B) (hL : ∀ a, |l a| ≤ L) (hK :
  ∀ a, |k a| ≤ L) (hβ : 10 ^ 12 ≤ β) (hn : card n + card m + L ≤ β) (hh : 10 ^ 30 * ((card n + card
  m) ^ 2 * β.log) ^ 3 ≤ h) (hj : IsProperMap (j · |>.1)) (hj' : Continuous (j · |>.2)) (lip :
  ∀ s, ‖(subOnePair j s).1‖ ≤ 1 → ‖(j s).2.1.1‖ ≤ β + 1) : ν.real {s | ‖(subOnePair j s).1‖ ≤ 1} ≤
  β ^ (20 * (card n + card m) ^ 2) * ‖∫ s, l.laplaceIntegrand k j φ s ∂ν‖ := by
  obtain ⟨b : 16 ≤ β, a : 1 ≤ β.log⟩ := by bound,
    by grind [le_log_iff_exp_le, exp_one_lt_d9], hj.1, one_le_cast_card n, one_le_cast_card m
  have hb := measure_ball_le_covering ν ((U.sum (signMatrix_sum ..)).comp j) 1 (by bound :
    _ ≤ 200 * β ^ 5) (by bound : _ ≤ β + 1) (by field; nlinarith : _ ≤ β ^ 8)
  simp [U.sum, ← fromBlocks_one', sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
    -_root_.mul_inv_rev] at hb
  set N : ℕ := _ ^ 2; let g s := 2 / ‖(j s * 1).1.1.1‖
  have p c (_ : c ≤ 18 * N) s : ‖l.laplaceIntegrand k j φ s‖ ≤ g s ^ c := by
    simp [g, HCParam.laplaceIntegrand, H.re_phase]; grw [norm_dsCoeff_le_one hg', mul_one,
      norm_dsCoeff_le_pow hg]
    grw [gapThreshold, ← hh, ← a]; norm_cast; grind [Nat.le_self_pow]
  have A s : 4 * ‖l.laplaceIntegrand k j φ s‖ ≤ 8 *
    ((l.laplaceIntegrand k j φ s).re + 16 * β⁻¹ ^ (50 * N) * g s ^ (8 * N)) := by
    obtain e | e := le_total _ (β⁻¹ ^ _) <;> grw [mul_assoc, ← e, ← pow_add]
    grind [abs_re_le_norm]
    set T := _ * β.log with hT
    rw [← (_ ^ _ : ℝ).exp_log (by bound), (by simp [N]; ring : Real.log _ = -100 * T)]
    obtain ⟨t : 1 ≤ T, e, e1⟩ := by bound, mul_left_surjective₀ (by positivity : T ≠ 0) 1e-13
    have f : e ≤ 100⁻¹ := by nlinarith
    obtain ⟨r, z, w, v⟩ | o := (le_total ..).imp_left (H.exists_near_one e hB (by nlinarith) f s)
    · obtain ⟨⟨a, ⟨u, i⟩, b⟩, c, o, d⟩ := dsCoeff_gaussian_shape hg hL w t,
        dsCoeff_gaussian_shape hg'.neg (by simpa) v t
      set x : ℂ := _ - a; set y : ℂ := _ - c; set E := rexp _
      grw [z.trans (by simp [y, HCParam.laplaceIntegrand, ↓← H.phase_logOneAdd r (by bound)
        (by bound), phase, ← diagonal_neg,
        Complex.exp_sub, Complex.exp_neg]; field : _ = a * c - (-x * c + -x * y + -a * y)), sub_re,
        re_le_norm, norm_sub_le, norm_add₃_le]; clear * - u i o b d t; simp_all [abs_of_nonneg]
      grw [d]; nlinarith [(by bound : 0 < E), (by simp [E]; grind : E ≤ 1)]
    grw [← (?_ : ‖l.laplaceIntegrand k j φ s‖ ≤ rexp _)]; clear * -; grind [abs_re_le_norm]
    simp [HCParam.laplaceIntegrand, H.re_phase]
    grw [← pow_le_pow_iff_left₀, mul_pow, norm_dsCoeff_pow_four_le, norm_dsCoeff_pow_four_le,
      ← mul_pow, ← mul_inv, ← (?_ : 1 + e ^ 2 ≤ _ * _), ← log_le_log_iff] <;> try positivity
    simp; grw [← le_log_one_add_of_nonneg, ← hh]
    field; repeat nlinarith only [e1, f, t, o]
  have ⟨I, hw⟩ := integral_decay_le ν (j := .comp (.fst ..) j) hj (by rify [N]; bound : _ < 8 * N) 1
  have T := I.mono' (by cases funext H.phase_eq; fun_prop [HCParam.laplaceIntegrand, phase] :
    Continuous _).aestronglyMeasurable (.of_forall (p _ (by omega)))
  grw [((T.re.add (I.const_mul _)).const_mul 8).measure_le_integral (.of_forall (A · |>.trans' ?_))
    fun s o ↦ (A s).trans' (by simp [HCParam.laplaceIntegrand, H.re_phase]; grw
    [← half_le_norm_dsCoeff hL _ o.1, ← half_le_norm_dsCoeff hK _ o.2] <;> linarith),
    integral_const_mul, integral_add' T.re (by fun_prop),
    integral_const_mul, integral_re T, hw, ← ENNReal.ofReal_mul, RCLike.re_le_norm, (?_ : _ ^ _ ≤
    β ^ (20 * N) / 16), ← mul_assoc (16 * _), (?_ : _ * 16 ^ _ ≤ (β ^ (20 * N))⁻¹)] at hb
  have := ENNReal.toReal_le_of_le_ofReal (by bound)
    (hb.trans' (ν.mono (⟨by grw [norm_le_insert' _ 1]; simp; bound, lip · ·⟩)))
  field_simp at this; linarith!
  all_goals (repeat grw [b]); simp [field, ← pow_add, ← pow_mul, ← pow_succ, ← pow_succ']
    <;> bound [N.pos_of_neZero]
open Finset Lagrange
lemma IsSteep.exists_isTwoFactor_restriction {n X} [Fintype n] [Fintype X] {ε B h l l' M} {e :
  X ⊕ Fin M ≃ n} {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M) (H : IsSteep l B e) (H' :
  IsSteep l' B e') (hg : l'.HasGap h) (hB : 1 ≤ B) : ∃ ω : USign (ε ⊕ᵥ 1),
  let j := (MonoidHom.id _).prod ((MulAut.conj ω).symm.toMonoidHom.comp (U.inl ..))
  ‖ω.1.1‖ ≤ card (n ⊕ Unit) ^ 2 * (6 * B) ^ (M + (M + 1)) ∧ IsTwoFactor l (-l') j (e' ∘ .inl) B
    e 0 ∧ ∀ s, (subOnePair j s).2 = ω⁻¹.1.1 * (subOnePair j s).1.fromBlocks 0 0 0 * ω.1.1 :=
  let x := Fin.append (-l'.lowestKType <| e' <| .inr ·.rev) (l.lowestKType ∘ e ∘ .inr)
  have o : ∀ i j, _ ∧ |(x i - x j : ℝ)| ≤ 6 * B := by simp [x, @Fin.forall_fin_add (_ + 1),
    H.weight_strictAnti.lt_iff_gt, H'.weight_strictAnti.lt_iff_gt]; rify; grind [IsSteep]
  have ⟨c, c1, hc⟩ := @exists_lagrange_weights _ x (o · · |>.1)
  let r {n} (g : Fin n → _) s y := (∏ j ∈ s, (x y - x (g j) : ℝ)) / c y
  let d a := r (.natAdd _) Finset.univ (.castAdd _ a) * (-1) ^ a.1
  let R y a := d a * r (.castAdd _) (Finset.univ.erase a) y
  have E a b : R (.castAdd _ b) a = ite (a = b) 1 0 := (c1 (a.castAdd _)).elim (by
    simp_rw [R, r, ← filter_ne', prod_filter]
    grind (splits := 20) [prod_eq_zero_iff, Fin.prod_univ_add])
  let f := e.sumCongr 1
  let ω := U.of IsHermInvolution.isUnit (Matrix.reindex f e' (fromRows (fromBlocks 1 0 0 (Matrix.of
    fun k a ↦ R (.natAdd _ k) a.rev)) (Matrix.of fun () ↦ 0 ⊕ᵥ (d ·.rev)))) (Matrix.ext (by
    have k a b := congr(ofReal $((Fin.sum_univ_add fun y ↦ R y a * (-1) ^ y.1 * R y b).symm.trans
      (.trans (by simp [mul_sum, eval_nodal]; grind) congr(d a * d b * $((hc (nodal (disjSum
      (Finset.univ.erase a) (Finset.univ.erase b)) (x <| .castAdd _ <| ·.elim id id))
      (by simp [-Nat.cast_add])).symm.trans (.trans (congrArg _ (by simp)) nodal_monic))))))
    simp [↓(reindex_equiv e').1, mul_apply, reindex_equiv e, signMatrix, H'.sign_inl, H'.sign_inr,
      Matrix.diagonal, f,
      H.sign_inl, H.sign_inr, pow_add, apply_ite, *] at k ⊢; grind [neg_one_pow_eq_ite]))
  ⟨ω, by
  refine ⟨sq (_ : ℝ) ▸ l2_opNorm_le_of_apply ((reindex_equiv f).1.2 ?_), have A s := ?_; ⟨⟨H,
      fun s ↦ ?_, by simp [trace_conj']; simp [trace], by simp, by simp, by simp [H'.sign_inl,
      H'.weight_eq_zero], by
              simp [↓reindex_equiv e', H'.weight_eq_zero]; rify; grind [IsSteep], fun u hu ↦
      (exists_unitary_sub_one_eq_inclMatrix e H.sign_inl hu.1).imp fun s hs ↦ Prod.ext hs ?_⟩, A⟩⟩
  · simp [↓reindex_equiv e', ω, R, d, apply_ite, pow_add]; split_ands <;>
      (repeat grw [fun n g s y ↦ (by grw [abs_div, div_le_self, abs_prod, (o ..).2,
      prod_const, card_finset_fin_le] <;> grind : |@r n g s y| ≤ _)]) <;> bound
  · erw [mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    simp [mul_sub, ← sub_one_mul, mul_assoc, ← ext_iff]
  · rw [HCParam.phase, A, trace_mul_cycle', ← mul_assoc, ← fromRows_toRows (ω.1.1 * _),
      ((Matrix.reindex e e').symm.injective (Matrix.ext ?_) : toRows₁ _ = fromCols (intDiagonal
      l.lowestKType) (replicateCol Unit (ofReal ∘ (0 ⊕ᵥ -r (.castAdd _) Finset.univ ∘ .natAdd _) ∘
      e.symm)) * ω.1.1)] <;> simp [Matrix.mul_assoc, trace, mul_apply, Matrix.diagonal]
    simp +zetaDelta [H.weight_eq_zero, H'.weight_eq_zero]; grind [mul_prod_erase]
  erw [A, hs, mul_assoc, Units.inv_mul_eq_iff_eq_mul, ← (Matrix.reindex f e').symm.apply_eq_iff_eq]
  simp [← Matrix.mul_assoc, entrywise, ω, f, inclMatrix, reindex_equiv e]⟩
