import New.Data.Weights
import Lib.Analytic.QuadraticTwist.ZeroFreeTwist
import New.Seesaw.IndexTypes
section
open Complex Filter Nat Real Set MeasureTheory Topology
lemma entireL_ne_zero_of_primeError_le {M} [NeZero M] {a : ZMod M} {β} (hβ : 1 / 2 < β)
  (ha : IsUnit a) (h : ∀ d : Primes, d = a → (d.1 % 8 = 7 ∧ M.Coprime d) ∧ ∀ᶠ x in atTop, primeError
  d M x ≤ x ^ (β - 1)) ρ (hρ : β < ρ.re) (χ : DirichletCharacter ℂ M) : entireL χ ρ ≠ 0 := by
  let ⟨d, e, hZ⟩ := exists_entireL_quadTwist_ne_zero |ρ.im| hβ ha (by grind)
  use by_cases (entireL_ne_zero χ) (flip ?_ (((h d e).1.elim isPolar_primeError).landau (by bound)
    (le_total · 1 |>.rec ?_ ?_) (.mono (tendsto_exp_atTop (h d e).2) (by simp [exp_mul, mul_comm]))
    hρ)) <;> simp +contextual (maxDischargeDepth := 3) [le_of_lt, div_re,
    (tendsto_sub_mul_logDeriv_entireL _).1.2, *, normSq, entireL_ne_zero, (hβ.trans hρ).trans',
    ← cast_sum, tendsto_sub_mul_logDeriv_entireL, ne_of_apply_ne re, ne_of_gt]; bound
lemma IsPolar.eventually_moment_le {E r} (h : IsPolar E r) : ∀ᶠ R in 𝓝[>] 3, ∀ᶠ t in atTop,
    (∀ v ≥ 0, |E v| ≤ t * v.exp) ∧ ∀ k, let F v := v ^ k * (-3 * v).exp * E v
  IntegrableOn F (Ioi 0) ∧ |∫ v in Ioi 0, F v| ≤ k ! * t / R ^ k := h.elim fun m ⟨C, Φ, _, hC, e,
      A, _⟩ ↦ ((isCompact_closedBall (1 + 3) 3).exists_thickening_subset_open (isOpen_analyticAt ..)
      (A · <| by simpa using (re_le_norm _).trans ·)).elim fun ε ⟨o, D⟩ ↦ by
  filter_upwards [Ioo_mem_nhdsGT (by bound : 3 < ε + 3)] with R ⟨a, b⟩
  simp [o] at D
  have J k : ∀ s, 2 < re s → let F v := (-v) ^ k * E v * ((1 - s) * v).exp
    IntegrableOn F (Ioi 0) ∧ iteratedDeriv k Φ s = ∫ v in Ioi 0, F v := by
    induction' k with k ih <;> intro s hs; simp [integrableOn_laplace_of_abs_le m hC, *]
    obtain ⟨⟨ε, o, q⟩, n⟩ := exists_pos_mul_lt (sub_pos.2 hs) 2, (isOpen_re_gt _).mem_nhds hs
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le ((isOpen_re_gt _).mem_nhds
      (lt_tsub_iff_right.1 q)) (.mono n (ih · · |>.1.1)) (ih s hs).1 (by fun_prop) (.mono
      (self_mem_ae_restrict (by simp)) fun v u z j ↦ ?_) ((ih (ε + 2) (by simpa)).1.norm.div_const
      ε) (.of_forall fun v z _ ↦ ((hasDerivAt_mul_const _).cexp.const_mul _).comp_const_sub ..)
    · simpa [iteratedDeriv_succ, pow_succ, ← mul_assoc, mul_right_comm] using! this.imp id
        (·.congr_of_eventuallyEq (.mono n (ih · · |>.2)) |>.deriv)
    simp [abs_of_pos, le_div_iff₀, mul_assoc, *]
    grw [← j.out, lt_add_one (v * ε), add_one_le_exp, ← Real.exp_add]; bound
  filter_upwards [mem_atTop C, mem_atTop (tsum _)] with t c d
  use (by grw [hC · ·, c]), fun k ↦ (J k 4 (by norm_num)).rec fun i j ↦ (?_ : _ ∧ _)
  grw [← d,
    ← (summable_taylor_of_removable (1 + 3 + R) D (by simp; grind)).norm.le_tsum k (by bound)]
  norm_num [j, neg_pow (ofReal _), mul_assoc, integrable_const_mul_iff, IntegrableOn,
    mul_comm (ofReal _)] at i ⊢
  use mod_cast i.re, mod_cast by simp [field]; bound
lemma IsPolar.exists_window_sub_mul_le {E r E' r'} (h : IsPolar E r) (h' :
  IsPolar E' r') : ∀ᶠ t in atTop, ∀ X ∈ Icc 0
  t.exp, ∃ u ∈ Icc t (t ^ 2), E u - X * E' u ≤ (-t).exp := (h.eventually_moment_le.and
  (h'.eventually_moment_le.and (Ioo_mem_nhdsGT (lt_add_one _)))).exists.elim fun R ⟨c, d, p, q⟩ ↦ by
  simp_rw [IntegrableOn, abs_le, forall_and] at *
  filter_upwards [c, d, mem_atTop (99 / (R.log - .log 3)), mem_atTop 9]
    with t ⟨c, _, a⟩ ⟨d, _, b⟩ u _ X ⟨_, _⟩
  let k := ⌈t ^ 2 / 9⌉₊
  obtain ⟨w, I, K : t + t * X + 1 ≤ t.exp * t.exp⟩ := three_pos.trans p,
    mod_cast fun R : ℝ ↦ (@laplace_pow R · k), by nlinarith [t.add_one_le_exp]
  have J R o := Integrable.of_integral_ne_zero ((I R o).trans_ne (by simp; grind))
  by_contra! N
  have : 0 ≤ ∫ v in Ioi 0, v ^ k * ((-R * v).exp * (7 * t).exp + (-1 * v).exp *
    (2 * t - t ^ 2).exp + (-3 * v).exp * (E v - _ * X - (-t).exp)) := setIntegral_nonneg
    (by simp) fun v (l : 0 < v) ↦ mul_nonneg (by bound) (by_cases (by bound [N v ·]) fun x ↦ ?_)
  · simp (disch := first | fun_prop (disch := simp [w]) | simp [*]) [mul_add, mul_sub, ← mul_assoc,
      integral_add, integral_sub, I, -neg_mul] at this
    grw [a.2, ← b.1, (by ring : _ - _ * X = k ! * (t + t * X) / R ^ k), lt_add_one (t + _), K,
      add_sub, sub_pos] at this
    apply this.not_ge ((add_le_add_three ..).trans_eq (add_thirds _)) <;>
    simp (disch := positivity) [← log_le_log_iff] <;> nlinarith [log_three_lt_d9,
      abs_le.1 (abs_sub_ceil_le (by bound : 0 ≤ t ^ 2 / 9)), (div_le_iff₀ (by bound)).1 u]
  grw [← neg_le_iff_add_nonneg, ← c.1, d.2, (by grind : -t ≤ v), (by ring : -_ = (-3 * v).exp *
    v.exp * (t + t * X + 1)), K, ← max_le_add_of_nonneg] <;> simp [← Real.exp_add, exp_nonneg, l.le]
  contrapose! x; use ?_ <;> nlinarith
end
open Finset Behrend Real Filter NumberField ClassGroup NeZero QuadField
lemma exists_three_term_free {G H} [CommGroup G] [CommGroup H] (φ : G →* H) c g (n M L : ℕ)
    (hL : 0 < L) (h : (L * M) ^ n ≤ orderOf (φ g)) : ∃ T, (∀ σ ∈ T, ∃ e, σ = c * g ^ e) ∧
    (M ^ n / (n * M ^ 2) : ℝ) ≤ #T ∧ ∀ i j, 0 < i → i < j → j ≤ L → ∀ σ ∈ T, ∀ τ ∈ T, ∀ ρ ∈ T, φ
    (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1 := (exists_large_sphere n M).elim fun k _ ↦ by
  have := pow_injOn_Iio_orderOf.comp map_injOn fun _ k ↦ h.trans' (finFunctionFinEquiv (⟨_, k ·⟩)).2
  use image (c * g ^ map (L * M) ·) (sphere n M k)
  rw [card_image_iff.2 fun _ a _ b _ ↦ this.mono (fun v k ↦ show ∀ i, _ from fun i ↦ ?_)
    a b ?_] <;> simp_all
    [← map_pow, sphere, Behrend.box, -map_apply, ↓forall_mem_image] <;> try nlinarith [k.1 i]
  intro i j _ o _ u hu _ v hv _ w hw _ H
  obtain ⟨a, ha, rfl⟩ := lt_iff_exists_add.1 o
  have e := @this ((i + a) • v) (by simp; nlinarith [hv ·]) (i • w + a • u)
    (by simp; nlinarith [hu ·, hw ‹_›]) (by simpa [pow_add, pow_mul', ↓div_pow,
    div_eq_iff_eq_mul, ← mul_assoc, -map_apply, -nsmul_eq_mul] using H)
  simp [by simpa [← mul_sum, *, ← add_mul, ha.ne', mul_left_comm i] using show
    ∑ l, (i + a) * (a * Int.natAbs (u l - v l) ^ 2 + i * v l ^ 2) =
    ∑ l, i * (i * w l ^ 2 + a * u l ^ 2) by simp [funext_iff] at e; zify at *; grind]
lemma exists_mul_principal {K} [Field K] [NumberField K] {I J : Fin (classNumber K + 1) → FinPlace
  K} (H : ∀ i, ((I i).1 * (J i).1).IsPrincipal) : ∃ i j, i ≠ j ∧ ((I i).1 * (J j).1).IsPrincipal :=
  let c (v : FinPlace K) := mk0 ⟨_, mem_nonZeroDivisors_of_ne_zero v.3⟩
  have e v w : _ ↔ c v * c w = 1 := by rw [← map_mul, mk0_eq_one_iff]
  by simp_all; grind [Fintype.exists_ne_map_eq_of_card_lt (c ∘ I) (card_fin _).ge]
lemma exists_data P {ε : ℝ} (e0 : 0 < ε / 6) (e1 : ε < 1 / 100) : ∀ᶠ x in atTop, ∃ D : Data P,
    D.x = x ∧ log D.x₁ = x ^ (ε / 6) ∧ (1e6 * log x) ^ 2 ≤ log D.x₁ ∧
    log (log D.b) = ε * log x ∧ towerDeg D.s / log D.b ≤ #D.thick := by
  have ⟨n, h⟩ := exists_nat_gt (99 * P.N₀ * P.d / (ε / 6) ⊔ 6)
  have E (k : ℕ) := tendsto_exp_mul_div_rpow_atTop k _ e0
  have ev k c := E k (mem_atTop c)
  rw [← map_exp_atTop, eventually_map]
  filter_upwards [E 0 (exists_prime_modEq_one_log_mem (P.N₀ * P.d) n (by grind [Parameters])),
    ev 2 1e12, ev (n + 1)
    ((P.N₀ * 8019 + 2) * 10368 ^ n), mem_atTop 1, ev 0 (2 * classNumber P.K + 1e6), Ioi_mem_atTop 0,
    mem_atTop 2, ev 0 (1e12 * P.c).exp, ev 1 (8019 * 2 ^ n * n)] with x hg h3 hL lx h5 x0 _ hf hC
  simp_all [↓rpow_natCast, le_div_iff₀, div_lt_iff₀, ← exp_mul, mul_comm x]
  have N (x y : ℝ) (e : 1 ≤ x := by simp; bound) (h : 1 < y := by simp) := exists_nat_pow_near e h
  obtain ⟨⟨h, n0⟩, ⟨o, m1, m2⟩, e, r1, r2⟩ := h, N (x / 2).exp 2, N (5 * x).exp 3
  let s := (o + 1) * 22
  have s8 : s ≤ 32 * x := by simp [s, pow_le_iff_le_log, exp_pos] at *; nlinarith [log_two_gt_d9]
  have W0 := exp_pos (ε / 6 * x)
  have ⟨k, k1, k2⟩ := N (2 ^ s / _) (2 ^ n) ((one_le_div W0).2 (by
    grw [pow_mul, ← le_self_pow₀, ← m2, e1] <;> bound)) (mod_cast by grind)
  set W := exp (_ * x)
  have Y i j (h : i ≤ j := by lia) : W ^ i ≤ W ^ j := by bound
  have s6 := @pow_le_of_le_log ((P.N₀ * P.d) ^ ((s + 6) * 2)) W n W0 (by
    grw [log_pow, log_exp, ← mul_assoc, ← h, log_le_self] <;> simp [field]; grind)
  have s5 : 2 ^ s ≤ W ^ n := s6.trans' (mod_cast by gcongr <;> nlinarith only [P.lt_d, pos P.N₀])
  obtain ⟨hg, w2⟩ := hg _ (by lia) s6, Y 2 6
  simp [pow_mul, field] at hg k2
  choose i1 p hp hm l u using fun i : Fin (classNumber P.K + 1) ↦ have : 0 ≤ i * W ∧ (i + 1) * W * 2
    ≤ W ^ 2 := ⟨by bound, by grw [i.is_le]; nlinarith only [h5]⟩; And.intro this (hg (10 * W ^ 6
    + 2 * i * W) (by bound) (by nlinarith only [this, Y 7 n, w2, h5]))
  have hN i := (hm i).of_dvd (P.N₁_mul_d_dvd_M_omega.pow out)
  choose I J nI nJ eJ using fun i ↦ have := Fact.mk (hp i); (FinPlace.exists_natCast_mem P.K
      (p i)).imp fun w h ↦ (prime_inert_or_eq_mul w h).imp fun _ ↦
      (·.2.resolve_left (by simp [(q_eq_iff_legendreSym_ne_neg_one w h).2, sq,
      P.chiK_eq_one_of_modEq_one (hN i), (hp i).ne_one]))
  have ⟨i, j, ne, α, hα⟩ := exists_mul_principal (⟨_, eJ · |>.symm⟩)
  let M := P.N₀ * 3 ^ (Nat.log 3 s + 5)
  have := @Parameters.placeClass_placeOfInt P s (M + 1) (mod_cast by simp [M])
  have ⟨T, t1, t2, t⟩ := exists_three_term_free (P.placeClass P.two_pow_dvd_N₁) (P.placeOfInt s
    (-1)) (P.placeOfInt s (M + 1)) n (2 ^ k) (324 * s) (by lia) (le_of_mul_le_mul_left (.trans (by
    unfold M; norm_cast; grw [pow_add, Nat.pow_log_le_add_one]; rify
    grw [← (le_div_iff₀ W0).1 k1, lx, ← hL, s8, s8]; ring; rfl)
    (@two_pow_le_of_pow_eq_one (M + 1) (mod_cast by
    simp) _ s (orderOf_pos _) (this ▸ Units.ext_iff.1 (pow_orderOf_eq_one _)))) (pos _))
  refine ⟨⟨_, W ^ 6, W, s, _, _, s8, T, p ∘ ![i, j], α, ?_, ?_, ?_, ⟨o, rfl, rfl⟩, ⟨e, rfl⟩,
    fun _ k ↦ (by cases t1 · ·; simp [*, P.placeClass_placeOfInt isCoprime_one_left.neg_left,
    Units.ext_iff, (ZMod.natCast_eq_zero_iff M _).2 k]), t, ?_, ?_, fun _ ↦ (hm _).symm.dvd',
    (Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    rify; grw [← log_lt_log_iff, u, ← l] <;> simp [(hp _).pos]; bound).injective.comp
    (by simpa), by
    simp [pow_le_iff_le_log, le_pow_iff_log_le, (hp _).pos, exp_pos]; grind, ?_, ?_⟩, ?_⟩ <;>
    simp [m2.le, r2.le, ← absNorm_span_eq_mul_star, ← hα, nI, nJ, hp, hN]
  simp [W]; and_intros <;> nlinarith only [e0, e1, w2, lx, h3, hf, h5]
  iterate 2 simpa [pow_succ']
  grw [← le_sqrt_of_sq_le w2]; intros
  apply hg <;> grind
  use by bound, by simp [W, field]
  grw [← t2, towerDeg, pow_add, Nat.pow_log_le_add_one]; simp; grw [k2, s8, pow_succ,
    pow_right_comm]
  field; grw [(lt_of_pow_lt_pow_left₀ n W0.le (by grw [← s5, pow_right_comm, k1]; bound) :), lx]
  nlinarith only [hC, Y 3 5]
