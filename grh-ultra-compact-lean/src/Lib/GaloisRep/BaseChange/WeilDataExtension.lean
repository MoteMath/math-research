import Lib.GaloisRep.BaseChange.BaseChangePlaces
import Lib.Adelic.Landherr.Landherr
import Lib.ClassField.Global.Avatars
section
open Subgroup NumberField Algebra IntermediateField IsGalois ComplexEmbedding Finset
variable {E E' : Type} {L} [Field L] [NumberField L] [IsCMField L] [Field E] [Field E'] [Algebra E L]
private lemma y9 (x : L) {w : 𝔸f L} (h : w = x * star w) : ∃ y, IsSelfAdjoint ((principalIdele y).1 * w) := ⟨(by grind [@exists_isUnit_sub_star L, star_one L, Ne.isUnit] : ∃ z, IsUnit (z + x * star z)).choose_spec.star.unit, by simp [IsSelfAdjoint]; grind [by simpa using congr(star $h)]⟩
lemma IsStep.q3 [NumberField E] [IsCMField E] [Algebra E E'] [Algebra E' L] [IsScalarTower E E' L] {μ} (hμ : IsStep (E := E) E' μ) {g : Gal(L/E)} {x} (hx : g x = x) (hL :
 E'[x] = ⊤) u (hu : u ∈ normKer L μ) (hN : let N := (u.1 * adeleMap g ·)^[orderOf g] 1; N = x • star N) :
 ∃ z c, IsUnit c ∧ IsSelfAdjoint (star c * ((principalIdele z * u).1 * adeleMap g c)) := by
 let K := fixedField (zpowers g)
 algebraize [Ω.fieldEmb L, (Ω.fieldEmb L).comp (algebraMap E L), (Ω.fieldEmb L).comp (algebraMap E' L)]
 lift x to K using (smul_eq_self_of_mem_zpowers ·.2 hx)
 rcases IsScalarTower.to₁₂₄ E E' L Ω, @id (IsGalois K L) (of_fixed_field ..), (subgroupEquivAlgEquiv _).isCyclic.1 (isCyclic_zpowers g), s08_z7 E
  fun y : K ↦ ⟨⟨_, fun a ↦ (map_star_CM a.1.toRingHom y).trans (congrArg _ (y.2 a))⟩, (by simp [← lift_algebraMap_apply L ·])⟩
 have nm w := (finAdeleIncl_adeleNorm K L w).trans (((finEquivZPowers
  (isOfFinOrder_of_finite g)).trans (subgroupEquivAlgEquiv _).1).prod_comp _).symm
 obtain ⟨⟨y, a, w, -, e⟩, ⟨χ, i⟩, ψ, j⟩ := (y9 x (adeleMap_injective
  _ ((nm u).trans (by simpa [adeleMap_star, nm, iterate_mul_apply, adeleMap_gal_pow, prod_range] using! hN)))).imp ((@exists_eq_principalIdele_mul_norm K _ {}).1 (t := principalIdele · * u.map _) · 1 (by simp)), exists_char_of_isCyclic (isCyclic_of_prime_card (card_aut_eq_finrank E E')), exists_char_of_isCyclic ‹_›
 obtain ⟨c, s, -, ⟨⟩⟩ := (char_artinMap_eq_one_iff ψ w).1 ((artinMap _ w).exists_rep.elim
  fun f r ↦ r ▸ eq_fixingSubgroup_of_isProGalois (J := j).1.ge fun ⟨_, _, rfl⟩ ↦ hL.ge.trans
  (AlgHom.adjoin_le_equalizer ⟨f.toRingHom.comp _, (eq_fixingSubgroup_of_isProGalois (J := i).1.le
  (artinMap_adeleNorm (g := f.restrictScalars E) r.symm 1 (by tauto) ▸ (char_artinMap_eq_one_iff ..).2 (by simpa [← (((adeleNorm E K).comp (adeleNorm K L)).ext adeleNorm_adeleNorm), isTotallyPositive_of_isTotallyComplex, ← hμ.apply_norm_eq_one_iff, hμ.apply_principal, map_adeleNorm_principalIdele, units_map_adeleNorm_star, eq_inv_mul_of_mul_eq e] using hu)) ⟨_, ·, rfl⟩)⟩ (algHom ..) (forall_eq.2 (f.4 x))) ⟨⟩)
 have ⟨k, H⟩ : (s * star s / u).map (adeleNorm ..) ∈ principalIdele.range := ⟨y / (a * c * star c), by simp [div_eq_div_iff_mul_eq_mul, e, Units.ext_iff]; ring⟩
 obtain ⟨z, rfl⟩ := hasse_norm k (congr($H.1 ·) ▸ adeleNorm_mem_closure) (isTotallyPositive_of_isTotallyComplex _)
 exact ⟨z, (hilbert90_finite_idele (u := ↑(principalIdele z / _)) (by
  erw [prod_range, ← nm, ← Units.coe_map, map_div, ← H, map_adeleNorm_principalIdele]; simp)).imp
  fun _ ↦ .imp_right (by nth_rw 1 [← ·]; simp [IsSelfAdjoint, division_def]; ring)⟩
open Matrix Polynomial UniqueFactorizationMonoid Classical ComplexOrder Module Function U
variable {E E' n : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] [IsGalois E E'] [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) [Fact (finrank E E').Prime]
@[simp] private lemma q4 [IsCMField E] {M : Matrix n n E} [IsStarNormal M] : aeval M (radical M.charpoly) = 0 := have := Matrix.isNilpotent_trace_of_isNilpotent ((commute_conjTranspose_aeval M
  (w := radical M.charpoly).isNilpotent_mul_left
  ⟨_, by simpa [aeval_self_charpoly] using aeval_dvd M (Classical.choose_spec (exists_dvd_radical_self_pow M.charpoly_monic.ne_zero))⟩).map (Φ ofNonempty).mapMatrix)
 by simpa [conjTranspose_map _ (map_star_complex _), ← ext_iff, trace_conjTranspose_mul_self_eq_zero_iff]
include hσ
lemma galois_descent_prime ⦃x⦄ (h : σ x = x) : x ∈ (algebraMap E _).range := (mem_bot_iff_fixed x).2 (by simp [(bijective_pow_gal hσ).2.forall, iterate_fixed h])
lemma adeleMap_galois_descent ⦃x⦄ (h : adeleMap σ x = x) : x ∈ (finAdeleIncl E E').range := by
 simp [↓mem_range_finAdeleIncl_iff, (bijective_pow_gal hσ).2.forall, ← adeleMap_gal_pow, iterate_fixed h]
omit hσ in
lemma U.hasse_principle_coboundary [IsCMField E'] {E : Type} [Field E] [CMType E] [Algebra E E'] [IsGalois E E'] {σ : Gal(E'/E)} (hσ : σ ≠ 1) [Fact (finrank E E').Prime] [StablyUnram E] {s} (u : Gf _ n) (hs : (map (algebraMap E' _)) s = u * (galoisGf σ u)⁻¹) (hN : twistedNorm (mapEnd (map_star_CM σ)) (finrank E E') s = 1) : ∃ g, mapEnd (map_star_CM σ) g = s⁻¹ * g := by
 let a := algebraMap E' (𝔸f E')
 choose g _ hg _ using (isTameAtLevel_gal σ).j7 (by tauto) s.1 (Y := s - 1) (by simp) (by erw [← map_twistedNorm (U 1).subtype, orderOf_eq_prime (card_aut_eq_finrank E E' ▸ pow_card_eq_one')] <;> aesop)
 obtain ⟨⟨y, hy⟩, J, hJ⟩ := exists_gl_map_eq_of_fixed (adeleMap_injective _)
  (adeleMap_galois_descent hσ) (g := u.1⁻¹ * g.map a) (by ext1; simpa [a, (congr($hs.1.1) : s.1.1.map _ = _), comp_def, mul_assoc] using! congr(u⁻¹ * ($hg).map a)), exists_gl_map_eq_of_fixed (RingHom.injective _) (galois_descent_prime hσ) (g := star g * 1 * g) (by ext1; simpa [star, conjTranspose_map _ (map_star_CM _), ← inv_val_eq_conjTranspose, mul_assoc, -RingHom.coe_coe] using congr($hgᴴ * $hg))
 choose l hl using Space.landherr ⟨J, _, gram_mkAdelicGL (fun w ↦ gram_inv_of_gram_eq (x := g.map _) (by simpa [entrywise] using congr($hJ.symm.1.map (ComplexEmbedding.lift _ (Φ w)))))
  (gram_inv_of_gram_eq (Matrix.map_injective (adeleMap_injective (algebraMap _ E'))
  (by simpa [← hy, ↓map_conjTranspose_mul_mul, adeleMap_star] using (gram_mul_of_gram_eq u⁻¹.2 (y := g.map a) (by simpa [entrywise, a] using congr($hJ.symm.1.map a))))))⟩ (stdSpace E n)
 use ⟨g * l.map (algebraMap ..), gram_mul_of_gram_eq congr($hJ.symm) (by simp [← map_conjTranspose_mul_mul, map_star_CM, hl])⟩, eq_inv_mul_of_mul_eq (by ext; simp_all [map, ← mul_assoc, comp_def])
omit hσ
variable {R S n : Type _} [CommRing R] [StarRing R] [Fintype n] {γ γ' a c : U (1 : Matrix n n R)} {σ : R →+* R} {z : Polynomial R} {w : Polynomial R} {p : ℕ} {u : R} {v : R} {D : Subgroup Rˣ} {x : Matrix n n R} {y : Matrix n n R} [CommRing S] [StarRing S] {hσ : ∀ x, σ _ = _}
instance : IsStarNormal γ.1.1 := ⟨by simp [commute_iff_eq, star, ← inv_val_eq_conjTranspose]⟩
attribute [local simp] mul_assoc mul_add conjTranspose_nonsing_inv map_aeval_matrix IsRootQuotient
lemma U.isRootQuotient_conj (h : γ * c = c * γ') : IsRootQuotient γ' z a → IsRootQuotient γ z ↑(c * a * c⁻¹) := by simp [← c.1.mul_inv_eq_iff_eq_mul.2 (aeval_semiconj congr($h.1.1).symm _), ← inv_val_eq_conjTranspose]; grind
lemma U.isRootQuotient_map {f : R →+* S} hf (h : IsRootQuotient γ z a) : IsRootQuotient ((map f hf) γ) (z.map f) ((map f hf) a : U 1) := by simpa [conjTranspose_map _ hf] using! congr(($h).map f)
lemma U.existsUnique_isRootQuotient (h : IsUnit (aeval γ.1.1 z)) : ∃! a : U 1, IsRootQuotient γ z a.1.1 := have := h.invertible; ⟨of isUnit_one _ (by simp [commute_conjTranspose_aeval, Commute.left_comm]), invOf_mul_cancel_right .., by aesop (add simp mul_right_eq_iff_eq_mul_invOf)⟩
lemma IsRootQuotient.mul : IsRootQuotient γ z x → IsRootQuotient γ w y → IsRootQuotient γ (z * w) (x * y) := by grind [(commute_conjTranspose_aeval γ.1.1).eq, conjTranspose_mul]
lemma IsMatchingPair.mul {A j K L f f' φ φ'} (h : IsMatchingPair (A := A) (n := n) hσ p u D j K f φ)
 (h' : IsMatchingPair hσ p v D j L f' φ') : u * v = 0 → u * u = u → v * v = v → star u = u → star v = v → IsMatchingPair hσ p (u + v) D j (K ⊓ L) (f * f') (φ * φ') := by intros; refine ⟨by simp +contextual [h.1, h'.1, -mul_assoc], fun P H e ↦ match h.2 P ?_
 e, h'.2 P ?_ e with | ⟨z, ⟨a, A⟩, a'⟩, ⟨w, ⟨b, B⟩, b'⟩ => ⟨z * w, ⟨by grind [congr($a * $b), smul_mul_smul], fun γ c ↦ ⟨by grind [mul_mem, det_mul], by
 convert (A γ c).2.mul (B γ c).2 <;> simp [twistedNorm_map_eq_prod, add_mul]
 match_scalars <;> grind⟩⟩, fun γ r
 _ hr ↦ by simp +contextual [a' γ r, b' γ r, *, by simpa [↓smul_smul, mul_sub, mul_comm, *] using congr((u • $hr, v • $hr, z * u • $b.symm, v • $a.symm * w))]⟩⟩ <;> revert H <;> gcongr <;> simp
lemma IsRootQuotient.twistedNorm_eq_mul (h : IsRootQuotient γ (twistedNorm (.map σ) p z) γ) (hc : γ * c = c * mapEnd hσ γ) (ha : IsRootQuotient γ z a) (hu : IsUnit (aeval γ.1.1 z)) : twistedNorm (mapEnd hσ) p c = γ * twistedNorm (mapEnd hσ) p (a⁻¹ * c) := eq_mul_of_mul_inv_eq (And.elim
 (existsUnique_isRootQuotient · |>.unique · h) (p.rec (by simp [twistedNorm]) fun _ ih ↦ by
 erw [twistedNorm_succ' (mapRingHom σ).1, mul_comm]
 simpa [*, aeval_semiconj (x := γ.1.1.map σ) congr($hc.1.1).symm, twistedNorm_succ']
 using! ih.imp (c.1.isUnit.mul ∘ .map σ.mapMatrix)
  (isRootQuotient_map hσ · |> isRootQuotient_conj hc |>.mul ha)))
end
section
seal Finset.univ Finset.sum Finset.prod
attribute [-simp] Subtype.forall
open NumberField Matrix Polynomial UniqueFactorizationMonoid AdjoinRoot MulAction Function Norms.L2Operator Algebra AlgEquiv MulDistribMulAction Ideal ComplexConjugate Ring
lemma exists_global_root {E E' n} [Field E] [CMType E] [Field E'] [Algebra E E'] [Fintype n] {p μ} {σ : Gal(E'/E)} [Fact p.Prime] (ho : σ ^ p = 1) (hσ : σ ≠ 1) [hμ : IsStep (E := E) E' μ]
  {z} {γ' : U (n := n) 1} : let k := algebraMap E' _; let P := γ'.1.1.charpoly; σ • P = P → IsNormRoot n (adeleMap σ) p 1 (normKer _ μ) (P.map k) z → ∀ {γ : Gf _ n}, γ.1.1.charpoly = P.map k → let T c := z * mapRingHom (adeleMap σ.toRingHom) c; ∃ w c, ∀ x, .map k w * T c = x → ∀ γ : Gf _ n, aeval γ.1.1 ((radical P).map k) = 0 → IsUnit (aeval γ.1.1 x) ∧ IsRootQuotient γ x ≤ IsRootQuotient γ c := by
 intro k P hγ hz γ e T
 obtain ⟨⟨_, v, hv⟩, hI⟩ := @id (IsCoprime P X) (isUnit_aeval_iff_isCoprime.1 (by simp)), fun {q} ↦ mem_primeFactors.trans (P.mem_normalizedFactors_iff (p := q) (charpoly_monic _).ne_zero)
 have cj {γ : Gf E' n} (h : aeval γ.1.1 (P.map k) = 0) := by
  simpa [← aeval_comp, star, by simpa using left_inv_eq_left_inv γ.2 (by
   simpa [h] using congr(aeval γ.1.1 (map k $hv)))] using star_aeval (R := 𝔸f E') γ.1.1
 let τ := (toPerm σ).subtypePermOfFintype fun q h ↦ hI.2 ((hI.1 h).imp
  (.map (toMulEquiv _ σ)) (.imp (by simp [smul_eq_map]) (hγ ▸ map_dvd (toMulEquiv _ σ) ·)))
 have C S [CommRing S] f := pairwise_primeFactors_isRelPrime (a := P).imp fun _ _ ↦ (·.isCoprime.map (mapRingHom (S := S) f))
 have crt {S} [CommRing S] f := exists_forall_sub_mem_ideal
  (((C S f).subtype _).mono fun _ _ ↦ (isCoprime_span_singleton_iff ..).2)
 have := e.symm.dvd.trans (charpoly_dvd_charpoly_aeval_comp (T^[p] 1 - X * ((T^[p] 1).map conj).comp (v.map k)))
 choose hq hm hP using fun q ↦ (hI.1 (Subtype.prop q)).imp_left Fact.mk
 let θ (q : primeFactors P) := aeval (R := 𝔸f E') (root q.1 : 𝔸f (AdjoinRoot q.1))
 choose _ h₁ sur ker F hβ using fun q ↦ adjoinRoot_cm_presentation (hm q) 1 (fun φ x h ↦ mod_cast
  (spectrum_subset_unitary_of_mem_unitary (U_one_mem_unitaryGroup ((U.map φ) γ'))
   (mem_spectrum_of_isRoot_charpoly ((isRoot_of_mem_roots h).dvd
    ((charpoly_map ..).substr (map_dvd φ (hP q)))))).2) (refl (θ q)) (.refl k)
 choose d hd e₀ using fun q ↦ (hz.2 _ e).1 _ (leftMulMatrix (Module.finBasis ..) (θ q X))
  (by simp [aeval_algHom_apply, *, mk_eq_zero.2])
 simp [← cj (e ▸ aeval_self_charpoly _), aeval_algHom_apply, ← norm_eq_matrix_det, by simpa [← (by rw [iterate_mul_apply, map_one, mul_one]; with_unfolding_all rfl : T^[p] 1 = twistedNorm (.map (adeleMap σ)) p z)] using (hz.2 γ e).2, mem_span_singleton] at this crt e₀ h₁
 have hu q := lmul_isUnit_iff.1 ((LinearMap.isUnit_iff_isUnit_det _).2 ⟨_, e₀ q⟩)
 have hw q := left_inv_eq_right_inv (by simpa [hP, mk_eq_zero.2] using congr(mk q $hv)) (h₁ q)
 let g {q q'} (h : τ q = q') := mapAlgEquiv σ q q' (.of_eq (smul_eq_map E' σ ▸ congr($h)))
 have hT {q q'} h f : θ q' (T f) = θ q' z * adeleMap (@g q q' h) (θ q f) := by
  simp [θ, g, T, aeval_def, hom_eval₂, eval₂_map, algebraMap_eq_finAdeleIncl, RingHom.comp]
 choose y c₁ h₂ h₄ using fun q ↦ show ∃ y c, IsUnit (θ q c) ∧ IsSelfAdjoint
   (star (θ q c) * ((principalIdele y).1 * θ q (T^[period τ q] c))) by
  have i := isReduced_of_injective (RingHom.pi (evalAt (E := AdjoinRoot q.1))) DFunLike.coe_injective
  cases' by simpa [← ker, *, map_X k ▸ F q X] using (map_dvd k (hP q)).trans this with N
  obtain f | rfl := (eq_or_ne (τ q) q).imp_right
   (minimalPeriod_eq_prime (by simp [τ, ← toPermHom_apply, ← map_pow, *] : (τ ^ p) q = _))
  have ⟨hg, hx⟩ : Semiconj (of q.1) σ (g f) ∧ g f (root _) = root _ := by simp [g, Semiconj]
  have := orderOf_eq_prime (coe_toAlgHom_injective (by ext <;> simp [iterate_fixed, ← coe_pow σ, ← hg.iterate_right p _, *]) : g f ^ p = 1) fun h ↦ hσ (ext (coe_injective' <| h ▸ hg ·))
  simpa [hT f, period_eq_one_iff.2, *, (sur _).exists, mul_assoc] using hμ.q3 hx
   adjoinRoot_eq_top (hu q).unit (.trans congr(μ $(by ext; simp [*])) (hd q))
   (by simpa [*, Semiconj.iterate_right (gb := (_ * adeleMap _ ·)) (hT f) p _] using! N)
  peel y9 _ N using ⟨1, by simpa⟩
 let r q := @invFun _ _ ⟨q⟩ (periodicOrbit τ) (periodicOrbit τ q)
 choose e j J hr using by simpa [periodicOrbit] using (by simp [r, τ.injective.mem_periodicPts, invFun_eq, periodicOrbit_apply_eq] : ∀ q, r (τ q) = r q ∧ q ∈ periodicOrbit τ (r q))
 obtain ⟨⟨c, Y⟩, w, W⟩ := crt k fun q ↦ T^[j q] (c₁ (r q)), crt (.id _) fun q ↦ surjInv mk_surjective (y q ^ 0 ^ j q).1
 use w, c, fun x X γ h ↦ (crt k fun q ↦ surjInv (sur q) (θ q x)⁻¹ʳ).elim fun d hd ↦ ?_
 simp [← ker, ← mk_eq_mk, surjInv_eq] at W Y hd
 choose H G using @id (∀ q, IsUnit (θ q x) ∧ IsSelfAdjoint (star (θ q c) * θ q x))
   ((reindex_equiv τ).1.2 fun q ↦ by
  simp_rw [← X, map_mul, hT rfl, Y, ← hT, ← iterate_succ_apply', F, W]
  rw [iterate_injOn_Iio_minimalPeriod (J _) ((j q).succ.mod_lt (J _).pos)
   (by simp [↓iterate_succ', ↓← hr, e]), e, congrArg τ (hr q), ← iterate_succ_apply' τ]
  use .mul (.map _ ⟨_ ^ _, rfl⟩) ((j q).succ.rec (h₂ _) fun _ _ ↦ by simp [*, -hr, iterate_succ', -iterate_succ, IsUnit.map]), (Nat.eq_or_lt_of_le (J q)).elim (by
   rw [·, iterate_minimalPeriod]; simpa using! (h₄ _))
   (by simp [Nat.mod_eq_of_lt ·, -iterate_succ]))
 have K (f g : (𝔸f E')[X]) := by
  simpa [Subtype.forall', ← ker] using (aeval_eq_zero_of_dvd_aeval_eq_zero · h) ∘ (map_prod
   (mapRingHom k) ..).dvd.trans ∘ Finset.prod_dvd_of_coprime (C _ k) (z := f - g)
 use .of_mul_eq_one _ (by simpa [*, inverse] using K (x * d) 1), fun a b ↦ by rw [IsRootQuotient, cj, K _ (_ * (c * d)), map_mul, ← mul_assoc, ← cj, b, ← map_mul, mul_left_comm, K] <;> simp [*, -hr, -Y, K _ 0, ← mul_assoc, mul_inverse_cancel_right, (star_star_mul ..).symm.trans (G _)]
open WithZero Valued IsDedekindDomain HeightOneSpectrum FiniteMultiplicity Finset WeilData RingHom
attribute [local simp] prime of_prime_left differentIdeal_ne_bot im_pos
lemma q5 {E L : Type} [Field E] [CMType E] [Field L] [Algebra E L] [h : CMOver E L] [WeilData E] [StablyUnram L] (hu : ∀ v : FinPlace L, star v = v → ¬v.1 ∣ differentIdeal (𝓞 E) _) : Nonempty (WeilData L) := by
 obtain ⟨⟨_, -, -, g, -, _, H⟩, ⟨⟩, _⟩ := @exists_reduction_and_idele_generator L _ _ (differentIdeal ℤ _) (by simp), exists_wellFoundedLT (FinPlace L), (by simpa [RingHom.ext_iff] using h.2 <| Φ ·)
 let i := algebraMap E L
 let s := principalIdele (.map i.1 (.mk0 j j_ne_zero)) * g
 have ⟨β, _⟩ := exists_idele_eq_uniformizer_zpow (fun u ↦ (ite (u < star u) 1 0 - (v (s.1 u)).log) / 2) ((finite_idele_val_ne_one s).subset (by aesop))
 refine have : SplittingChar L := ⟨⟨υ.1.comp ⟨_, .units_map (.prodMap (.pi (∏ u with u.comap i = ·, Pi.evalMonoidHom _ u)) (adeleNorm ..)) (by simp [MonoidHom.pi]; and_intros <;> fun_prop)⟩, fun _ ⟨x, e⟩ ↦ υ.2 _ ⟨norm E x, ?_⟩⟩, fun _ _ ↦ by
  erw [υ_unit] <;> simp_all [prod_fiberwise, adeleNorm_mem_Ohat, Submonoid.mem_units_iff], fun _ ↦ congr(υ.1 $(by bound)).trans (υ_star _)⟩; ⟨⟨i j, by simp [← map_star_CM], by aesop, β, fun u ↦ ?_, by simpa [map_ofNat] using map_isIntegral_int i isIntegral_traceOne, exists_eq_principalIdele_mul_norm.2.2⟩⟩
 ext w <;> simp [← e]
 algebraize [Φ w]
 erw [norm_eq_prod_embeddings]
 refine' prod_bij' (fun σ _ ↦ .mk σ) (fun u _ ↦ ⟨Φ u, _⟩) .. <;> simp [algebraMap_toAlgebra, i, ← (h.2 _).2] <;> aesop
 let w := FinPlace.below E u
 rcases valuation_star u (i j), self_dual w ▸ log_exp _, (H (star ↑g⁻¹)).1 (forall_ψf_mul_eq_one.1
  (by simp_all [↓ψf_star (_ * _), mem_Ô, forall_ψf_mul_eq_one.2 ∘ (H _).2])), self_dual w ▸ exp_ne_zero, differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L) ▸ emultiplicity_mul u.prime
 rw [← exp_log (x := v _), exp_inj] <;> simp_all [s, i, ← w.valuation_liesOver L, mem_Ô, ← map_star_CM, v_inv, ← log_le_log, emultiplicity_eq_multiplicity, irreducible, emultiplicity_map_eq_ramificationIdx'_mul (v := w.1), ← eq_sub_iff_add_eq, ne_bot, w.1.ramificationIdx'_eq_ramificationIdx _ w.ne_bot]
 norm_cast at *; grind [multiplicity_eq_zero_of_not_dvd, star_star, below_star, @congrArg _ _ (star w) w (v <| α.1 ·)]
end
