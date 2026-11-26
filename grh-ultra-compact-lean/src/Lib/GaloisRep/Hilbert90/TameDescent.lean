import Lib.General.LinearAlgebra.ValuedMatrix
import Lib.Adelic.Adeles.AdeleIdempotent
open Algebra Nat Quotient Filter Finset Function Ideal Matrix MulEquiv Subgroup Ideal.Quotient
attribute [local simp] map_smul' RingHom.ext_iff add_assoc mul_assoc
variable {R n B V} [CommRing R] [CommRing B] [Fintype n] {σ p} {m x : R} (o : IsProfiniteRing R) {θ : B →+* B} (t : IsTameAtLevel σ p m) (h : IsArtinianRing R ∨ IsProfiniteRing R) [AddCommGroup V] [Module R V] (τ : V →ₛₗ[σ] V)
@[to_additive fixed_sum] lemma s08_j3 {M} [CommMonoid M] (τ : M →* M) (a : ℕ → M) (hp : a p = a 0) (ha : ∀ i, a (i + 1) = τ (a i) := by simp [↓iterate_succ']) : τ ((range p).prod a) = (range p).prod a := by cases p with simp_all [↓map_prod, prod_range_add, prod_range_succ' a]
lemma iterate_mul_apply : ∀ x, (m * σ ·)^[p] x = (range p).prod (σ ^ · <| m) * (σ ^ p) x := by
 induction p <;> simp [*, prod_range_add]
lemma isTameAtLevel_gal {K L} [Field K] [Field L] [Algebra K L] (σ : Gal(L/K)) [Finite Gal(L/K)] : @IsTameAtLevel L _ σ (orderOf σ) 1 := by
 simp_all [IsTameAtLevel, ← AlgEquiv.coe_pow, ↓orderOf_pos, eq_bot_of_prime]
 grind +extAll [pow_ne_one_of_lt_orderOf, AlgEquiv.one_apply]
lemma isTameAtLevel_one : IsTameAtLevel 1 1 m := ⟨rfl, ⟨1, by simp⟩, by aesop⟩
lemma IsTameAtLevel.of_skew (h : σ ^ 2 = 1) (u : IsUnit (x - σ x)) : σ m = m → IsTameAtLevel σ 2 m := (⟨·, u.exists_right_inv.imp' (x * ·) fun z e ↦ ⟨0, by simp_all [range]; grind [map_one σ]⟩, h, by simp, fun 1 _ _ _ H ↦ mem_of_dvd _ (neg_sub x _ ▸ u.neg.dvd) (H x)⟩)
lemma s08_j4 (e : σ ^ p = 1) : IsFixedPt σ (∏ i ∈ range p, (σ ^ i) x) := s08_j3 _ _ congr($e x)
lemma isProfiniteRing_intAdeles {E} [Field E] [NumberField E] : IsProfiniteRing (Ô E) := fun x ↦ by
 convert @existsUnique_eq' _ ((hyperfilter _).map x).lim
 erw [@Ultrafilter.lim_eq_iff_le_nhds _ _ _ isCompact_Ô.compactSpace, ← Tendsto, tendsto_subtype_rng, ← tendsto_sub_nhds_zero_iff, (⟨by simp [mem_nhds_zero_finAdele_iff]; tauto⟩ :
  HasBasis _ (· ≠ 0) fun N ↦ (N • ·) '' Ô E).tendsto_right_iff]
 simp [dvd_def, Subtype.ext_iff, eq_comm]
lemma IsProfiniteRing.of_retract (o : IsProfiniteRing R) (i : B →+ R) (r : _ →+ B) (e : ∀ x, r (i x) = x) : IsProfiniteRing B := fun x ↦ (o (i ∘ x)).imp' r fun L ⟨a, u⟩ ↦ ⟨(a · · |>.mono fun N ↦ .imp' r (by simp +contextual [← nsmul_eq_mul, ← map_nsmul, eq_comm, e])), fun y k ↦ u (i y)
 (k · · |>.mono (by simp +contextual [dvd_def, ← map_sub, ← nsmul_eq_mul])) ▸ (e y).symm⟩
lemma IsProfiniteRing.j5 (o : IsProfiniteRing R) (b : B ≃+ (n → R)) : IsProfiniteRing B := of_retract (R := n → R) (fun x ↦ by
 choose L _ using forall_existsUnique_iff.1 (o <| swap x ·)
 simp_all [pi_dvd_iff, @forall_comm _ n, ← funext_iff]) b b.symm b.1.3
lemma IsProfiniteRing.eqLocus (o : IsProfiniteRing R) : IsTameAtLevel σ p 0 → IsProfiniteRing (σ.eqLocus 1) := fun ⟨_, ⟨e, _⟩, h, _⟩ ↦ o.of_retract (.mk' (↑) (by simp)) (.mk' (fun x ↦ ⟨_, fixed_sum σ (σ^[·] (e * x)) congr($h _)⟩) (by simp [mul_add])) (by simp_all [iterate_fixed ·.2, ← sum_mul])
namespace IsTameAtLevel
include t
lemma of_map (f : R →+* B) (hf : Semiconj f σ θ) : θ ^ p = 1 → IsTameAtLevel θ p (f m) := (⟨by rw [← hf, t.1], t.2.1.imp' f fun _ ↦ (by simpa [hf.iterate_right ..] using map_dvd f ·), ·, t.2.2.2.imp_right (fun P _ _ ↦ · · · (P.comap f) (by simp_all [hf.iterate_right ..]))⟩)
lemma j6 (o : IsProfiniteRing R) : let I N := span {↑N}
 let q N := quotientMap (I N) σ (by aesop)
 ∃ Λ : _ →ₐ[R] R, Semiconj Λ (Pi.map (q · !)) σ ∧ ∀ N, Finite (R ⧸ I N !) ∧ IsTameAtLevel (q N !) p m := by
  intro I q; simp [IsProfiniteRing, ← eq_zero_iff_dvd] at o
  choose Λ a u using fun x : ∀ N, R ⧸ I N ! ↦ o (out ∘' x)
  have H {F} (G : ∀ M, _) (e : ∀ {M}, Semiconj₂ (mk _) F (G M))
   x y : Λ (fun N ↦ G _ (x N) (y N)) = F (Λ x) (Λ y) := .symm (u _ _ fun M h ↦ by
   filter_upwards [a x M h, a y M h, hyperfilter_le_atTop (mem_atTop M)] with N d d' l
   grw [e.eq, ← d, ← d', ← e.eq, mk_span_eq_iff_dvd_sub, dvd_factorial (by lia)
    l]; simp [e.eq, I, ← eq_zero_iff_dvd])
  have c a := H (fun _ _ _ ↦ mk _ a) (by tauto) 0 0
  use ⟨.mk' ⟨⟨Λ, c 1⟩, H _ (map_mul _)⟩ (H _ (map_add _)), c⟩, (H (const _ <| q ·) (by tauto) 0 :), fun N ↦ ⟨.of_not_infinite fun i ↦ ((Set.toFinite {_}).preimage_embedding _).notMem_hyperfilter (by simpa using! (o (out ∘ i.natEmbedding _)).choose_spec.1 N ! (by simp)), t.of_map _
   (by tauto) (by ext x; apply IsPeriodicPt.map congr($(t.2.2.1) x); tauto)⟩
lemma exists_smul_mem_span_fixedPoints (hτ : ∀ v, τ^[p] v = v) P [i : IsPrime P] (hm : m ∉ P) : ∃ r ∉ P, ∀ v, r • v ∈ Submodule.span R (fixedPoints τ) := by
 choose! u w using (not_forall.1 <| hm ∘ t.2.2.2.2 · · P)
 refine ⟨_, ?_, fun v ↦ ((∑ z ∈ range p, (LinearMap.proj z).smulRight (τ^[z] v)).map_span_le ..).2
  ?_ ⟨_, (adjoin_eq_span ..).le (prod_mem (by aesop) : ∏ x ∈ Ioo 0 p, ((σ ^ x) (u x) • 1 - (σ ^ · <| u x)) ∈ adjoin R (RingHom.pi (σ ^ ·)).range), (LinearMap.sum_apply ..).trans (sum_eq_single 0 (by simp_all [prod_eq_zero (i := ·), zero_lt_iff]) ?_)⟩⟩ <;> simp_all [IsTameAtLevel, i.prod_mem_iff]
 exact fun _ ↦ Submodule.subset_span (fixed_sum (τ : V →+ V) _ (by aesop))
lemma j7 (h : IsArtinianRing R ∨ IsProfiniteRing R) (c : GL n R) {Y} (hY : c.1 = 1 + m • Y) (hc : twistedNorm (.map σ) p c = 1) : ∃ k : GL n R, ∃ W, c * k.1.map σ = k ∧ k.1 = 1 + m • W := by
  wlog f : IsArtinianRing R
  · choose Λ H _ T using t.j6 (by lia); choose k W a b using fun N ↦ this (T N) (by tauto) (.map _ c) (by ext; simp [hY]; rfl) (by rw [← map_twistedNorm, hc] <;> bound) inferInstance
    let L := Λ.mapMatrix.comp (piAlgEquiv (n := n) R).symm.toAlgHom
    exact ⟨(piUnits.symm k).map L, _, by convert ← map_mul L .. ▸ congrArg L (funext a) <;> bound [Λ.2], by simpa using! congrArg L (funext b : _ = 1 + m • W)⟩
  let τ := .mulLeft R c.1 ∘ₛₗ σ.toSemilinearMap.mapMatrix
  have ⟨_, ⟨e, _, _⟩, hσ, _, _⟩ := t
  choose hτ _ using fun i v ↦ (by induction i with simp_all [τ, ↓twistedNorm_succ', twistedNorm, ↓iterate_succ', map_add] :
    τ^[i] v = twistedNorm (.map σ) i c * v.map (σ ^ i) ∧ τ^[i] 1 = 1 + m • (Y + τ ·)^[i] 0)
  have ⟨g, ⟨hg, W, hW⟩, hmax⟩ := exists_maximalFor_of_wellFoundedGT {g | τ g = g ∧ ∃ W, g = 1 + m • W} (det · ∉ MaximalSpectrum.asIdeal ·) ⟨_, fixed_sum (p := p) τ (τ^[·] (e • 1))
    (by aesop), _, by simp_all [← sum_smul, sub_eq_iff_eq_add', ← smul_sum, smul_comm _ m, add_smul, mul_smul]; rw [smul_add]⟩
  use .mk'' g (by_contra (exists_max_ideal_of_mem_nonunits · |>.elim fun M ⟨i, H⟩ ↦ ?_)), W, hg, hW
  choose _ y e using f.exists_pow_succ_smul_dvd g.det 1
  let N := (range p).prod (σ ^ · <| (1 - g.det) * (1 - g.det * y))
  have D : _ ∣ N := dvd_prod_of_mem _ (by simpa)
  have : mk M N = 1 := (MonoidHom.mker _).prod_mem fun i _ ↦ by erw [← iterate_fixed hg i, hτ, det_mul, unit_mul_mem_iff_mem _ (by simp), ← RingHom.map_det, ← eq_zero_iff_mem] at H; simp_all
  choose _ k using (by simp [hW, ← eq_zero_iff_dvd, det_one_add_smul m] : m ∣ _).trans D
  choose _ _ E using t.exists_smul_mem_span_fixedPoints τ (by aesop) M (by simp_all [eq_zero_iff_mem.2 ·])
  choose _ _ G E using Submodule.mem_span_set'.1 (E 1)
  apply mt congr($Eᵀ.det ∈ M).mp (by simp_all [← eq_zero_iff_mem])
  erw [transpose_sum, det, sum_fn, MultilinearMap.map_sum]
  refine sum_mem fun _ _ ↦ (det_mul_column ..).symm.subst (M.2 _ (by_contra ((fun v (o : τ
    v = v) (j : vᵀ.det ∉ M) ↦ @hmax (g - N • (g - v)) ⟨by simp [hg, o]; erw [s08_j4 hσ], _, by rw [hW, k, mul_smul, smul_sub m, add_sub]⟩ (fun ⟨m, _⟩ j ↦ have := (by
    simpa [by simpa [pow_succ, mt eq_zero_iff_mem.1 j] using congr(mk m $e)] using map_dvd (mk m)
      D); ?_) ⟨M, i⟩ ?_ H) _ (ext (congrFun₂ (G _).2 · ·))))) <;> simpa [← eq_zero_iff_mem, RingHom.map_det, g.map_sub, this] using j
include h in
lemma j8 (u : IsUnit x) (h₁ : m ∣ x - 1) (hc : ∏ i ∈ range p, (σ ^ i) x = 1) : ∃ g : Rˣ, m ∣ g - 1 ∧ x * σ g = g := .imp' (·.det) (by simp_all [← ext_iff]) (t.j7 h (diagGL fun () ↦ u.unit) (by ext; simpa using eq_add_of_sub_eq' h₁.choose_spec) (by aesop))
lemma exists_norm (h : Finite R ∨ IsProfiniteRing R) (hu : IsUnit x) (hf : σ x = x) (h₁ : m ∣ x - 1) : ∃ z : Rˣ, m ∣ z - 1 ∧ m ∣ z⁻¹ - 1 ∧ ∏ i ∈ range p, (σ ^ i) z = x := by
  wlog f : Finite R
  · choose Λ H F T using t.j6 (by lia); choose z d d' e using fun N ↦ this (T N) (by grind) (hu.map _) (hf ▸ quotientMap_mk) (map_dvd _ h₁) (F N)
    have D {y} := Λ.commutes m ▸ map_dvd Λ ∘ pi_dvd_iff (y := y - 1).2; simp at D
    use (piUnits.symm z).map Λ, D d, D d'
    simpa [← H.iterate_right .., ← prod_fn] using! congr(Λ $(funext e)).trans (Λ.2 x)
  let H := ofDiv {x : Rˣ | m ∣ x - 1} ⟨1, by simp⟩ fun x h y k ↦ by
    simpa [sub_mul] using! (h.sub k).mul_right ↑y⁻¹
  let s i : H →* H := (Units.map ↑(σ ^ i)).restrict fun _ ↦ (by simpa [iterate_fixed t.1] using! map_dvd (σ ^ i) ·)
  choose z hz using (eq_of_le_of_card_ge (fun | _, ⟨z, rfl⟩ => div_eq_one.2 (by
    ext; simpa using! (s08_j4 t.2.2.1).symm)) (index_ker ((range p).prod s) ▸ index_range (f := s 0 / s 1).ge.trans (index_antitone fun c hc ↦ (t.j8 (by tauto)
    (by simp) c.2 (by simpa using! congr($hc.1.1))).elim fun a e ↦ ⟨⟨a, e.1⟩, div_eq_of_eq_mul'' (by ext; tauto)⟩))).ge (x := ⟨hu.unit, h₁⟩) (div_eq_one.2 (by ext; tauto))
  use z, z.2, z⁻¹.2, by simpa using! congr($hz.1.1)
