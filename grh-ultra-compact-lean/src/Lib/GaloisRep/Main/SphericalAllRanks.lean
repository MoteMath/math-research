import Lib.GaloisRep.Main.AvatarCompatibility
import Lib.GaloisRep.EvenRank.ThetaLift
section
open NumberField Matrix Polynomial Filter Fintype Finset AlgHeckeChar AutChar Metric Classical Units
lemma sphericalCompat_std {ℓ E n} [ThePrime ℓ] [PadicIso ℓ] [Field E] [EmbeddedNumberField E] [CMType E] [Fintype n] [Nonempty n] [WeilData E] w : SphericalCompat E n (card n) w := fun P κ f hf h ↦ by
 let t := card n + 1
 let c (i : Fin 2) u : ℤ := -torsionOrder E * ((-κ.2 u).toNat + ite (u = ofNonempty) i.1 0)
 choose μ hμ using (exists_hasWeight_of_prod_eq_one (S := ∅) (e := c ·) (by tauto)
  (by simp_all [c, _root_.zpow_mul, ← map_pow, _root_.pow_torsionOrder_eq_one]))
 have e {i} u : c i u ≤ κ.2 u := by simp [c]; grw [← (torsionOrder_pos E).nat_succ_le]; lia
 let θ i (l : Fin t) := (hμ i).toAlgebraic (card n + t) (t - l)
 have X₀ {l l' w} (_ : w.IsSplit) : heckeCoeff (θ 0 l).1.1 ∅ w ≠ heckeCoeff (θ 1 l').1.1 ∅ w := fun e ↦ by
  choose n _ γ a k using ((hμ 0).mul (hμ 1).inv).exists_pow_eq_prod (divStar (locFullIdele w _))
   (Unitary.coe_mul_star_self 1)
  rcases a w, congrArg (w.valuation E) ((Φ _).injective (by simpa [c, mul_add] using (k.symm.trans
   congr($(div_eq_one.2
   (Circle.ext (by simpa [θ, heckeCoeff, HasWeight.toAlgebraic, HeckeChar.finPart, abs_of_nonneg, Real.sqrt_eq_zero'] using! congr($e / ‖$e‖)))).1 ^ n))) : γ.1 ^ _ = 1)
  simp_all [coe_divStar, locFullIdele, ← map_inv, NeZero.ne]
 have N := (eventually_mostFrobenii h.2 fun y ↦ (· y.prime_q)).and (.all fun i ↦ ((hμ i).toAlgebraic t t).eventually_avatar_frob.and (.all (eventually_avatar_frob <| θ i ·)))
 let R i w := ∏ l, (X - C (heckeCoeff (θ i l).1.1 ∅ w))
 choose! F hF o h' Q q e' using fun {i} ↦ j2 (hμ i) e rfl ⟨f, hf⟩ h.1 t.le_refl
 choose H σ s using (r7 (by grind) w hF ⟨@o ·, by peel h.2 using q this.1 this⟩ |>.symm)
 let ρ i := twistByChar ((hμ i).toAlgebraic t t).avatar (σ i)
 have c i : Attached (P * R i) (ρ i) := (s i).imp (fun _ ↦ .of_coeHom_comp (.smul (by fun_prop) (by
  fun_prop))) (.imp (·.twist _) (.imp_right (· · · |>.mp <| N.mono fun y ⟨⟨_, p⟩, a⟩ ↦ by simp [R, θ, ← e' p.1 p, ρ, Units.smul_def, charpoly_smul_coeff, ← (a i).1, ← mul_sub, ((q p.1 p).isMonicOfDegree o).1, mul_comm (ιℓ _), norm_eq_one_of_continuous, continuous_avatar])))
 have K {g} i := (ρ i g).1.trace_eq_neg_charpoly_coeff ▸ (((c i).tendsto_charpoly_coeff ..).neg.sub
  (tendsto_mostFrobeniiAt fun g ↦ ∑ l, ((θ i l).avatar g).1)).congr' (mem_inf_of_left (N.mono
  fun y a ↦ ((a.1.2.isMonicOfDegree h.1).rec fun d m ↦ by simp [R, a, by
  simpa [↓prod_X_sub_C_nextCoeff, nextCoeff, m.natDegree_mul, d, monic_prod_X_sub_C] using m.nextCoeff_mul (q := R i y.w) (monic_prod_X_sub_C ..)] :
  _ = -ιℓ ((P y.w).coeff (card n - 1)))))
 refine ⟨(IsTraceNondeg.t5 (by simp) (c · |>.2.1) (fun _ _ ↦ DFunLike.ne_iff.2 (dense_of_mostFrobenii (N.mono fun y a e ↦ X₀ a.1.1 (by simpa [a] using congr($e.1)))).nonempty)
  fun _ _ ↦ eq_add_of_sub_eq (tendsto_nhds_unique (K _) (K 0))).imp fun r ⟨nr, hr⟩ ↦ ⟨nr.k5 (.congr (by cases c 0; fun_prop) hr), nr, .id, ((c 0).2.2.2 · · |>.mp <| N.mono fun y a b ↦ forall_eq.2 (norm_coeff_le_of_mul_monic (monic_prod_X_sub_C ..) (by
  simpa [sub_mul, charpoly_eq_mul_of_trace_pow_add _ _ _ (by simpa [sub_eq_iff_eq_add] using hr <| y.frob ^ ·), a, R, Polynomial.map_prod] using b)))⟩, fun r b x A hA ↦ ?_⟩
 have U i g := (r g).1.trace_eq_neg_charpoly_coeff ▸ tendsto_nhds_unique
  (b.tendsto_charpoly_coeff ..).neg (K i)
 choose T J H using (H · (s _) (h' x) A hA)
 choose x y G using fun {i a l} ↦ (avatarCompatAt_of_stablyUnram _).sphericalClause_of_unramified
  ((hμ i).charUnramifiedAt_toAlgebraic rfl rfl a l) hA
 choose _ u v z using (local_clauses_twist A (r' := ρ ·) fun _ ↦ rfl)
 choose Y Z K using fun i ↦ local_clauses_of_trace_limit (J := jumps κ (card n)) b.1 b.2.1 Eq (pure
  ()) (fun _ ↦ Option.elim' 1 (-1)) (fun _ ↦ (fun j ↦ Option.elim' (jumps κ (card n) + ∑ l, j l)
  j) _) (fun _ ↦ Option.elim' ⟨ρ i⟩ (⟨(GeneralLinearGroup.scalar _).comp <| θ i · |>.avatar⟩))
  (fun _ ↦ (·.rec (c i).1 fun _ ↦ .of_coeHom_comp <| .matrix_diagonal (by
  simp +instances; fun_prop))) (fun _ ↦ (·.rec (u i (T i) x) fun _ ↦ x)) (fun _ ↦ Option.rec (by
  convert! v _ (J i) y
  simp [jumps, HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, sum_ite, e, ← range_val, ← sum_multiset_singleton, ← Multiset.coe_mapAddMonoidHom, sum_range, Fin.sum_univ_add]
  apply congrArg₂ _ (by clear * -; grind); split
  exacts [by ring, sum_equiv Fin.revPerm _ _ (by simp +arith)]) fun _ ↦ y) (.inl inferInstance)
  (by simp +instances [tendstoUniformly_iff, U i])
  (by simp +contextual [eq_comm, Multiset.count_sum'])
 use Y 0, Z 0, fun hw P p s hs ↦ ?_
 have K i c := (K i .refl (fun _ o ↦ ⟨.refl, o.rec (z i ((H i _ _ (q p.1 p) s hs).of_dvd (by
  erw [← e' p.1 p, Polynomial.comp, eval₂_map, scaleRoots_eval₂_mul]; simp [Polynomial.map]))
  (G s hs)) fun l ↦ (G s hs).of_dvd (by simp [dvd_iff_isRoot, R, θ, eval_map, eval₂_finsetProd, prod_eq_zero (mem_univ l)])⟩) (by simp +instances [tendstoUniformly_iff, U i, mul_sub, mul_sum])).of_dvd (Polynomial.map_dvd ιℓ.toRingHom (dvd_mul_right (P * R i w) c))
 have ⟨a, b, e⟩ : IsCoprime (R ..) (R ..) := .prod_left fun _ _ ↦ .prod_right fun _ _ ↦ pairwise_coprime_X_sub_C (fun _ _ ↦ id) (X₀ hw)
 rw [← mul_one P, ← e, mul_add]
 clear * - K
 grind [PolyKillsAt, IsKilledBy, eval₂_add, Polynomial.map_add, K 0 a, K 1 b]
end
section
open Algebra QZChar ComplexOrder Fintype Ideal MonoidHom Polynomial QuotientGroup Set Subgroup Valued WithZero
attribute [local simp] Pi.mulSingle_apply Subring.mem_centralizer_iff Units.ext_iff funext_iff heckeGL norm_locField_eq_q_zpow coe_normAbsChar_locField
variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n} [Field E] [CMType E] {w} [Fintype n] {κ P ξ} {hw : _ ≠ w} {f : (stdSpace E n).forms κ} (H : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
include H
lemma IsIwahoriEigen.v5 {y} (h : v (y.1 - 1) < 1) : normAbsChar.prod (.pi ξ) y = 1 := by
 simpa [-Units.ext_iff, normAbsChar, dominantTorus, Monotone, apply_ite, H.2, (smul_left_injective
  ℂ H.1).eq_iff' (one_smul ..), by simpa using v.map_one_add_of_lt h] using fun i a ↦ (H.2.2 (Pi.mulSingle i y) a).symm.trans (compactMean_apply (diagGL_mem_proIwahori.2 (by aesop)) _)
lemma IsIwahoriEigen.v6 y (h : v y.1 = 1) : normAbsChar.prod (.pi ξ) (y ^ (w.q - 1)) = 1 := H.v5 (card_ResField w ▸ residue_eq_iff_valuation_sub_lt_one.1 (algebraMap_pow_card_pred_eq_one (K := ResField w) (k := ResField w) (.mk0 ⟦⟨_, h.le⟩⟧ (residue_eq_iff_valuation_sub_lt_one.1.mt (by simp [h])))))
lemma Attached.v7 [Nonempty n] [WeilData E] [EmbeddedNumberField E] {r : GalRep ℓ E n} {A : ClosurePlace} (he : IsEigenform f.1 P) (hr : Attached P r) (hs : Antitone (‖ξ · (uniformizer w) |>.1‖)) (hA : IsPlaceOver A w) (s : decompGroup _ A) x (k : ℕ) (hQ : IsFrob A (w.q ^ k) s.1⁻¹) (hx : localArtin Gal(Ω/E) A w x = s) (hv : v x.1 = .exp (-k)) : IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (card n)) ∧ PolyKillsAt r A s.1 (∏ i, (X - C (ιℓ (ξ i x)))) := by
  wlog k₀ : 0 < k generalizing s x k
  · obtain ⟨⟨⟩, φ, hφ, e⟩ := not_lt.1 k₀, hA.exists_frob_inv_eq_localArtin (Γ := Gal(Ω/E)) (v_uniformizer w)
    have ⟨a, b, z⟩ := this _ _ 1 (by simpa) e (by simp) one_pos
    have G n h := (this (s * φ⁻¹ ^ n) (x * uniformizer w ^ n) n
      (by simpa using (hφ.pow n).mul_iff.2 hQ) (by simp_all) (by simp [*]) h).2.2
    use a, b, fun l ↦ eval₂_eq_zero_of_pos_pow ⟨_, by simp [commutes]⟩ ⟨_, by simp
                  [commutes]⟩ (z.1 l) (by simp) (by simpa using! G · · |>.1 l), @fun j d _ c ↦ ?_
    obtain ⟨⟨f, hf, -⟩, p⟩ := w.exists_q_eq_pow (hA.valuation_natCast_lt_one_iff.1
      (j.inducesPlace.1.1 ▸ valuation_comap_intQpBar_lt_one _)), a.2
    have W : IsWeilPair (j.toGp φ⁻¹) f := by simpa [IsWeilPair, j.isFrob_iff, ← hf]
    use p, eval₂_eq_zero_of_pos_pow ⟨_, forall_mem_range.2 (commute_coefEnd_linearFrob p c)⟩ ⟨_, forall_mem_range.2
      (commute_coefEnd_linearFrob p W)⟩ (z.2 W).2 (by simp) fun n h ↦ linearFrob_pow p W _ ▸ linearFrob_mul p c (W.pow _) ▸ by simpa using! ((G n h).2 (c.mul (W.pow _))).2
  replace hs : Antitone (‖ξ · x |>.1‖) := fun i j c ↦ le_of_pow_le_pow_left₀ w.q_bounds.1.ne'
    (by simp) (by simpa [← norm_pow, by simpa [div_pow, div_eq_iff, ← pow_mul]
    using (H.v6 (x / uniformizer w ^ k) (by simp [*]))] using pow_le_pow_left₀ (by simp) (hs c) _)
  let D := (zpowers (normAbsChar.prod (.pi ξ) x)).comap (normAbsChar.prod (.pi ξ))
  induction' m : D.index using Nat.strongRec with _ ih generalizing E k
  have := @finiteIndex_of_le _ _ _ D ⟨(@index_pow_local_le _ _ _ _ ⟨(mul_pos k₀
    w.q_bounds.1).ne'⟩ w).1⟩ fun _ ⟨y, t⟩ ↦ t ▸ ⟨-(v y.1).log * (w.q - 1), by simpa
    [mul_zpow, zpow_mul, ← zpow_natCast, inv_eq_iff_mul_eq_one] using (H.v6
        (x ^ (v y.1).log * y ^ k) (by rw [← exp_log (x := v _)] <;> simp [*, mul_comm]))⟩
  obtain G | ⟨p, hp, h⟩ := not_or_of_imp D.index.exists_prime_and_dvd
  · simp [D, hv, -zpow_neg, (zpow_right_strictMono₀ (by simp : (1 : ℂ) < w.q)).injective.eq_iff, eq_top_iff', mem_zpowers_iff, ← zpow_mul] at G
    cases Int.eq_one_of_dvd_one k.cast_nonneg ((G (uniformizer w)).imp (by simp +contextual))
    exact isUnitary_localFormRep |> fun b ↦ (H.exists_isExponent b self_mem_cyclicSpan).elim fun u
      ⟨h, o, l⟩ ↦ hasHeckePolyAt_iff_localFormRep.2 ⟨compactMean_mem_levelSpace u, fun j ↦ Multiset.esymm (List.ofFn (ξ · x |>.1)) j / w.q ^ j.choose 2, (Multiset.prod_X_sub_X_eq_sum_esymm (List.ofFn (ξ · x |>.1))).trans (by simp [heckePoly, mul_div_cancel₀, mul_assoc]), fun j ↦ sub_eq_zero.1 (Not.imp_symm (b.1 _) (by
      simp +contextual (maxDischargeDepth := 4) [-mem_levelSpace, (isBiInvariant_basicDoubleCoset
        j).heckeFun_adjoint _ _ b.2, IsBiInvariant, ↓(isBiInvariant_basicDoubleCoset
      j).heckeFun_adjoint _ (compactMean_mem_levelSpace u) b.2 (compactMean_mem_levelSpace u), IsBiInvariant.heckeFun_mem, compactMean_mem_levelSpace, b.compactMean_adjoint, ← (isBiInvariant_basicDoubleCoset j).heckeFun_comm, by
        simpa [partialHecke_zero_eq_heckeGL, -mem_levelSpace] using (l.apply_partialHecke (x := ·)
          hv · bot_le j)]))⟩ |> fun k ↦ ((sphericalCompat_std w (by simp) (he.v9 (by
      simpa using compactMean_mem_cyclicSpan 1 h) fun c ↦ o (l.eq_zero_of_eq_zero_on_spherical hv
      (fun y ↦ (by simpa [·, eq_comm] using G y)) hs (by simp [c, ← compactMean_eq_self (H := Kw ..)
      · · ▸ b.compactMean_adjoint u _])))).2 hr k.1 A hA).imp (isGoodAt_iff.1 · |>.1) (.imp_right
      (by simpa [Polynomial.map_prod, Fin.prod_ofFn] using · _ _ k s (by simpa using hQ)))
  obtain ⟨χ, o, ⟨x₀⟩, h⟩ := by simpa [addOrderOf_eq_prime_iff (hp := ⟨hp⟩), DFunLike.ext_iff] using @exists_prime_addOrderOf_dvd_card' (Additive (_ ⧸ D) →+ QZ) _ _ p ⟨hp⟩ (by rwa [card_hom_QZ])
  choose μ u _ _ _ hu hb B hD hk using s08_w9 hw hA hp (χ.toMultiplicativeRight.comp (mk' D)) h (o ·) fun y a ↦ χ.map_zero ▸ congrArg χ ((eq_one_iff _).2 ⟨0, (H.v6 y a).symm⟩)
  cases (hb u).2 rfl
  obtain ⟨Y, X, f', _, he', hS, hξ'⟩ := hD x, (hk x).trans (χ.map_zero ▸ congrArg χ
    ((eq_one_iff x).2 (mem_zpowers _))), exists_baseChange_isIwahoriEigen hu hb (by simp [*]) H
  obtain ⟨⟨_, hr'⟩, n, rfl⟩ := (sphericalCompat_std u f'.2 he').1, Int.ofNat_dvd.1 (dvd_neg.1 ⟨_, by
    simpa [v_localNorm (absNorm_pow_inertiaDeg ..), *] using congr(log (v $((exists_localNorm_of_abelianLift_artinAt X).choose_spec).1)).symm⟩)
  rw [pow_mul, absNorm_pow_inertiaDeg, hA.artinAt_eq_of_localArtin_eq hx] at *; obtain ⟨⟨y, o, d⟩, a, b, c⟩ := B.exists_localArtin_eq (g := (w1 μ).fixingSubgroupEquiv
    ⟨s, (·.2 ⟨s, X⟩)⟩) hQ n, (hS.r4 hr' he' he).2.1 hr A
  have e := (div_mem_ker_iff _).1 (H.v5 (by simpa using (hA.localArtin_tame_symbol (x := 1) (hA.isUniformiser_iff.2 (hA.exists_uniformiser Gal(Ω/E)).choose_spec.1) (by simp [v_localNorm (absNorm_pow_inertiaDeg ..), *])
    ((div_mem_ker_iff _).2 (hx ▸ (B.localArtin_adeleNorm (AlgEquiv.restrictScalarsHom E)).1 d))
    congr($(((DiscreteUnits.ofBase Gal(Ω/E) Ω _).1.exists_nsmul
    (FinPlace.q_bounds _).1.ne').choose_spec).1))))
  simp_rw [← by simpa using congr($e.2)] at hs ⊢
  exact (ih _ (m ▸ Finite.card_subtype_lt fun ⟨y, e⟩ ↦ h (congr(χ $e) ▸ hk _ ▸ abelianLift_artinAt_of_mem_closure (L := w1 μ))) hξ' he' hr' B _ _ _ ‹_› d o
    (by nlinarith) hs (.trans (by rcongr; simp; simp [D, ↓← e, mem_zpowers_iff, ↓norm_localNorm])
    (index_ker ((mk' D).comp (localNorm E u))))).imp a (.imp (b _) ((c ⟨s, X, Y⟩).2 _))
end
