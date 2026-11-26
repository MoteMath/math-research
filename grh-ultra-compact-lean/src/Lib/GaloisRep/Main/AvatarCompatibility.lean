import Lib.GaloisRep.Main.HeckeOperatorOfFunction
import Lib.PadicHodge.Characters.LocalCharacters
import Lib.PadicHodge.Crystalline.HodgeTateFrame
import Lib.Shimura.Transfer.PELDataExistence
import Lib.Cohomology.PointClass.GaloisRep
import Lib.Shimura.IntegralModel.ModelExistence
import Lib.ClassField.Local.ArtinMapAtPlace
import Lib.LocalGL.Green.GreenTau
import Lib.ClassField.Grunwald.Grunwald
import Lib.GaloisRep.BaseChange.BaseChangeEigenchar
import Lib.Weil.DualPair.PairSumNegation
private lemma nodup_jumps {E : Type} [Field E] [CMType E] (κ : Weight E) N σ : (jumps κ N σ).Nodup := .map (.of_lt_imp_ne fun i j h ↦ by grind [Finset.sum_mono_set (κ.1 (.mk σ)) (Finset.Ioo_subset_Ioo h.le N.le_refl)]) List.nodup_range
section
section
attribute [-simp] Matrix.map_mul LaurentPolynomial.single_eq_C_mul_T LaurentPolynomial.T_pow det_classical
open Matrix MvPolynomial Polynomial Finset Algebra Fintype Submodule Function ConjAct LaurentPolynomial Fin Filter
variable {k K N R S A : Type} [NormedField k] [Fintype N] [CommRing R] [CommRing S] {m n} {e : Fin n → ℤ} (y : Matrix N N R) [NormedField K] [NormedAlgebra K k] [CommRing A] [Algebra A R] [Algebra A S]
attribute [local simp high] mvPolynomialX_mapMatrix_aeval Matrix.sum_apply coeff_X_mul' comp_def sq units_smul_def mul_assoc LaurentPolynomial.algebraMap_apply map_mul ofId Finsupp.weight_single isHomogeneous_C_mul_X IsHomogeneous.sum IsHomogeneous.mul
noncomputable abbrev q6 m a := (of (flip (uncurry <| y ^ @Fin.val m ·) ∘ a)).det
@[simp] private lemma ac_q7 a (φ : R →ₐ[A] S) : φ (q6 y m a) = q6 (φ.mapMatrix y) m a := by simp [q6, ↓← map_pow, φ.map_det]; rfl
lemma FreeInts.q8 {c} (he : FreeInts e) (hc : Surjective c) {x : GL N k} (hm : m ≤ n + 1) (h : ∀ a, q6 (diagonal (T ∘ e ∘ c) * x.1.map .C) m a = 0) : n < m ∧ ∀ {a b}, c a = c b → a ≠ b → x⁻¹ a b = 0 ∧ x⁻¹ a a = x⁻¹ b b := by
 let y := diagonal (X ∘ c) * x.1.map .C
 have hy j : ∀ a b, ((y ^ j) a b).IsHomogeneous j := by induction j <;> simp_all [← totalDegree_zero_iff_isHomogeneous, y, pow_add, mul_apply, diagonal, mul_comm (X _), apply_ite]
 let z := (ofId _ (FractionRing (MvPolynomial (Fin n) k))).mapMatrix y
 have (o : m ≤ _) := minors_eq_zero_iff.1 (fun a ↦ (ac_q7 ..).symm.trans (by
  simpa [-ac_q7] using congr($((ac_q7 y a (AddMonoidAlgebra.mapDomainAlgHom k k
   _)).trans (.trans (by simp [y, MvPolynomial.X, ← single_eq_monomial, T, ↓algHom_C]) (h a))).coeff.support).symm.trans (Finsupp.mapDomain_support_of_injOn _ (.mono ((homogeneousSubmodule_eq_finsupp_supported ..).le (by simpa [det_apply'] using (.sum _ _ _ fun _ _ ↦ .C_mul (.prod _ _ _ (by tauto)) _))) (he _ (by grw [isLt, ← hm]; simp))))))
  (((linearIndependent_pow z).comp _ (castLEEmb o).2).of_comp (LinearEquiv.curry ..).1)
 obtain ⟨M, D⟩ := minpoly.monic z.isIntegral, z.minpoly_dvd_charpoly.trans (charpoly_map ..).dvd
 choose s hq _ U using lifts_and_natDegree_eq_and_monic (by
  simpa [M] using! IsIntegrallyClosed.eq_map_mul_C_of_dvd _ y.charpoly_monic D) M
 have ⟨w, hw⟩ := (map_dvd_map _ (IsFractionRing.injective ..) U).1 (hq ▸ D)
 obtain ⟨⟨α, v⟩⟩ := by simpa [det_eq_sign_charpoly_coeff, hw, ne_zero_iff] using (by simpa [y, prod_eq_zero_iff] using (x.map _).det_ne_zero : y.det ≠ 0)
 have : ((optionEquivLeft ..).symm y.charpoly).totalDegree ≤ card N := by
  simp [charpoly, det_apply, y, charmatrix, diagonal_apply, apply_ite]
  grw (transparency := .default) [totalDegree_finsetSum, totalDegree_smul_le, totalDegree_finsetProd, totalDegree_sub, totalDegree_mul]; simp [ite_apply, apply_ite]
 grw [← y.charpoly_natDegree_eq_dim, hw, map_mul, totalDegree_mul_of_isDomain (by aesop)
  (by aesop), natDegree_mul_le, ← totalDegree_coeff_optionEquivLeft_le, ← le_totalDegree
  (by simpa), ← degreeOf_le_totalDegree, ← natDegree_optionEquivLeft] at this
 have hr := s.X_mul_divX_add ▸ (ext (by
  simpa [z, ↓aeval_algHom_apply, ↓Polynomial.aeval_map_algebraMap] using congrFun₂ congr(aeval z $hq)) : s.aeval y = 0)
 have h2 a b := congr((($((s.divX.divX_mul_X_add ▸ hr :)) * x.1⁻¹.map .C :) a b).coeff α)
 simp [y, add_mul, mul_add, algebraMap, α.sum_fintype, ↓map_add] at *; simp [← mul_assoc, coeff_mul_X', mul_comm (s.coeff _), ← @eq_of_le_of_not_lt _ _ 1 ⇑α (hc.forall.2
  fun a ↦ Nat.pos_of_ne_zero fun z ↦ by simpa [*] using congr(($hr a a).coeff α))
  (by bound [by simpa using sum_strictMono ·])] at *; grind [diagonal_apply, MvPolynomial.coeff_zero]
private lemma ac_q9 [NeZero n] {E} [Field E] [NumberField E] [Algebra E Ω] (r : Gal(Ω/E) →* GL N K) (c : Continuous r) (d : ∀ v, diagonal v ∈ span K (.range (r · |>.1))) {P : _ → K[X]} (h₁ : ∀ᶠ y in mostFrobenii E, (P y).aeval (r y.frob).1 = 0 ∧ (P y).IsMonicOfDegree n) (Q : GL N k) κ (he : FreeInts e) (l : ∀ i, e i ∈ Set.range κ) (t : ∀ h : MvPolynomial _ k, (∀ᶠ g in nhds 1, h.aeval (Q.1 * (r g).1.map (algebraMap ..)).uncurry = 0) → h.aeval (diagonal (T ∘ κ) * Q.1.map LaurentPolynomial.C).uncurry = 0) : card N = n ∧ ∀ᶠ y in mostFrobenii E, (r y.frob).1.charpoly = P y := by
 delta uncurry at t
 let φ := (MulSemiringAction.toAlgHom K (Matrix N ..) (toConjAct Q)).comp (ofId K k).mapMatrix
 have W {m g} {p : K[X]} (o : p ≠ 0) (e : p.aeval (r g).1 = 0) (h : p.natDegree < m) :
  q6 (φ _) m = 0 := funext (minors_eq_zero_iff.2 ((·.restrict_scalars' K).mt (by
  exact not_linearIndependent_iff.2 ⟨_, funext (by simpa [aeval_eq_sum_range' h, sum_range]
   using! (congr(φ $e · ·))), ⟨_, h⟩, by simpa⟩)))
 have : e.Injective := fun i j h ↦ Finsupp.basisSingleOne.injective (by apply he 1 <;> simp [*])
 have Z {m} x h a := t (q6 (mvPolynomialX N N k * (Q⁻¹ * Units.map φ (r x)).1.map C) m a)
  (.mono ((map_mul_right_nhds_one x).le ((isClosed_eq (f := fun g ↦ q6 (φ (r g)) m) (by
  simp [φ]; fun_prop [flip]) continuous_zero).closure_eq.subst h))
  (by simp_all [φ, Matrix.map_mul]))
 simp [-diagonal_mul, -Units.coe_map, ← Matrix.map_mul] at Z
 have H x := Z x (univ_mem' (dense_of_mostFrobenii (h₁.mono fun g h ↦ W h.2.ne_zero h.1 congr($(h.2.1) + 1).le)))
 choose l L using l
 choose c hc using fun j ↦ ((det_vandermonde_eq_zero_iff.1 (by simpa [det_classical, diagonal_pow, flip_def, uncurry] using! (H 1 (Function.diag ∘ cons j l)))).elim (by
  simp [T, forall_fin_succ, AddMonoidAlgebra.single_inj]; grind) : ∃ i, e i = κ j)
 obtain ⟨rfl, hs⟩ := funext hc, (⟨l ·, by grind⟩ : Surjective c)
 have hN := card_of_bijective ⟨fun a b h ↦ by_contra fun o ↦ by simpa using ((congrFun₂ Q.3 a a).symm.trans (sum_eq_zero fun t _ ↦ by apply ((span_induction (p := fun x _ ↦ φ x a b = 0 ∧ φ x a a = φ x b b) (by simpa using (H ·⁻¹ |> he.q8 hs .refl |>.2 h o)) _ _ _ (d (Pi.single t 1))).elim (by simp [φ, mul_apply, diagonal, apply_ite]; grind)) <;> simp +contextual)), hs⟩
 use by simp [*], h₁.mp fun V a ⟨x, b⟩ ↦ ⟨_, sdiff_le, a.sdiff (by simp), Set.not_subset.1
  (mem_nhds_iff.2 ⟨V, ·, a, b⟩ |> Z x |> he.q8 hs (by simp) |>.1.false), .of_forall fun _ _ _
  _ _ _ g h ↦ (sub_eq_zero.1 (by_contra (g.2 <| subset_closure <| W · (by simp [*, aeval_self_charpoly]) (h.2.natDegree_sub_lt NeZero.out ⟨by simp [*], charpoly_monic _⟩)))).symm⟩
end
variable {E K₀ ℓ} [Field E] [EmbeddedNumberField E] [Field K₀] [NumberField K₀] [ThePrime ℓ]
open Polynomial Units Fintype Matrix Metric Filter Submodule
noncomputable def AlgHeckeChar.baseChange [Algebra K₀ E] (ω : AlgHeckeChar K₀) : AlgHeckeChar E := ⟨(ω.1.1.comp (Units.map (adeleNorm ..)), .ofAdd (ω.1.2.toAdd <| ·.comp (algebraMap ..))), ω.2.1.preimage_of_continuous, fun x ↦ by
 simp [map_adeleNorm_principalIdele, ω.2.2]
 convert ← prod_fiberwise (RingHom.comp · (algebraMap ..)) _ with s
 let := s.toAlgebra
 erw [Algebra.norm_eq_prod_embeddings, ← Finset.prod_zpow]
 apply prod_equiv (.mk (⟨_, RingHom.congr_fun ·.2⟩) (⟨_, ·.comp_algebraMap⟩)); aesop⟩
@[fun_prop] lemma continuous_cycCharIn : Continuous (cycCharIn (Γ := Gal(Ω/E)) (PadicAlgCl ℓ) Ω
 ℓ) := (continuous_algebraMap ..).units_map.comp (continuous_cycChar ℓ)
private lemma ac_j0 [PadicIso ℓ] [CMType E] (ω : AlgHeckeChar E) (d : ℕ) {ρ : PadicRep _ ℓ} (hρ : Continuous ρ.rep) : ∃ ρ' : PadicRep _ ℓ, Continuous ρ'.rep ∧ ∀ w, (∀ σ, inducedPrime σ = w → ω.1.2.toAdd σ = d) → CharUnramifiedAt ω.1.1 w → let c := (ω.1.1 (locIdele w (uniformizer w))).1; ∀ {R J q a t}, SphericalClause ρ.rep R J w
  (heckePoly q a fun j ↦ ιℓ (t j * c⁻¹ ^ j)) → SphericalClause ρ'.rep R (fun τ ↦ (J τ).map (· + -ω.1.2.toAdd τ)) w ((heckePoly q a t).map ιℓ) := by
 let θ := ω / show IsHeckeOfType 1 _ by simp [IsHeckeOfType, isOpen_iff_nhds].toAlgebraic (m := d) (by tauto)
 let ν := cycCharIn _ Ω ℓ ^ d * θ.avatar
 use ⟨twistByChar ν ρ.rep⟩, .of_coeHom_comp (.smul (by fun_prop) (by fun_prop))
 intro w hd hω c R J q a t h A hA
 have ⟨x, b, p⟩ := show heckeCoeff θ.1.1 ∅ w = w.q ^ d * c by simp [heckeCoeff, θ, ← two_mul, _root_.zpow_mul, ← Complex.ofReal_pow, field] ▸ (avatarCompatAt_of_type_eq_zero θ (by aesop)).sphericalClause_of_unramified (fun _ ↦ by aesop) hA
 refine (local_clauses_twist A (μ := ν) (by tauto)).2.elim fun T ⟨U, V⟩ ↦ (h hA).imp (T · ⟨by
  simpa +contextual [ν, cycChar_of_mem_inertiaGroup (A := A)] using x.1, x.2.tate_twist d ?_⟩)
  (.imp (U · fun l γ τ t u ↦ (jump_twist_cyclotomicGp (-d) ?_).subst
  (.trans (by simp [Multiset.count_singleton, θ, IsHeckeOfType.toAlgebraic, ← eq_sub_iff_add_eq])
  (b t _))) fun h s hs ↦ V (c := ιℓ c) ((h s hs).of_dvd ⟨C _, by simp +contextual [Polynomial.ext_iff, c, apply_ite, pow_sub₀, field]⟩) (.of_dvd ⟨fun l ↦ by
  obtain := congr(algebraMap _ (PadicAlgCl ℓ) $(hs.cycChar_eq ℓ l)).symm, (p s hs).1
  simp_all [Matrix.algebraMap_eq_diagonal, ν, Matrix.diagonal_pow, funext_iff], @fun l h k hk ↦ ((p s hs).2 hk).elim fun o q ↦ (And.intro · ?_) (o.tate_twist d ?_)⟩
  ((C_mul_dvd (a := ↑w.q ^ d) (by simp)).2 dvd_rfl)))
 rotate_right 2
 rw [C_mul', eval₂_smul, ← q, eq_comm, linearFrob_twist_cyclotomicGp ‹_› hk d]
 simp [hk.eq_pow_of_isFrob (by rwa [← map_inv, l.isFrob_iff]), ↓eval₂_sub, ↓eval₂_C, pow_mul, Algebra.smul_def, mul_sub]
 all_goals simp [ν, PadicPlaceEmbedding.cyclotomicGp_eq_cycChar, mul_smul, ← map_pow, ← Units.smul_def]
attribute [local simp] tendstoUniformly_iff trace_blockDiagonal' Finset.mul_sum
private lemma ac_j1 {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E] (F : Filter (FinPlace E)) J (P : FinPlace E → (PadicAlgCl ℓ)[X]) (h : ∀ τ, ∃ ρ : PadicRep Gal(Ω/E) ℓ, Continuous ρ.rep ∧ ∀ᶠ w in F, SphericalClause ρ.rep OccursIn (Set.indicator {τ} J) w (P w)) : ∃ b, ∃ r : GalRep ℓ E (Fin b), Continuous r ∧ (∀ v, diagonal v ∈ span (PadicAlgCl ℓ) (.range fun g ↦ (r g).1)) ∧ ∀ᶠ w in F, SphericalClause r OccursIn J w (P w) := by
 choose ρ hρ H using h
 choose σ n t using s08_m7 fun _ ↦ (· (.toHomUnits (.comp blockDiagonalAlgHom.1.1 (.pi ((Units.coeHom _).comp <| ρ · |>.rep)))))
 choose b d _ s f j u a using s08_k4 _ (.id _) n.hasSemiprimeSpan
 let f' := (reindexAlgEquiv _ (PadicAlgCl ℓ) (@finSigmaFinEquiv _ d)).toAlgHom.comp blockDiagonalAlgHom
 have ht i : (f' (n1 i)).trace = 1 := by
  simp_all [f', -coe_reindexAlgEquiv, Fintype.sum_eq_single i]
 choose B C e hB using k3 f f'
  (by simp_all [n4, n5]; grind)
 simp [trace] at ht a
 have := n.k5 (by simp [t]; fun_prop)
 refine ⟨∑ i, d i, .toHomUnits (.comp f' s), .of_coeHom_comp (.congr (by fun_prop) (congr(C * $(a · ▸ hB _)).trans (by simp [← C.mul_assoc, e]))), fun v ↦ (f'.toLinearMap.map_span_le ..).2 (by
  aesop) ⟨fun i ↦ diagonal (v <| finSigmaFinEquiv ⟨i, ·⟩), u.ge ⟨⟩, by aesop⟩, .mono (.all H) fun _ H A hA ↦ ?_⟩
 choose U K z using local_clauses_of_trace_limit this n OccursIn (pure ()) 1 _ _ (by simpa)
  (by grind [SphericalClause]) (fun _ ↦ (H · hA |>.2.1)) (.inl inferInstance) (by simp [t])
  fun τ _ _ _ h _ a _ ↦ h () τ (by aesop) (by simp_all [Tendsto, ← Nat.cast_sum])
 refine (local_clauses_of_retract (φ := .id _) 1 1 (by simp) (by simp) .id univ_mem (by simp [← hB, a]) e).elim fun _ y ↦ ⟨by aesop (add simp isGoodAt_iff), fun l _ _ t ↦ (mt ?_ ∘ K t ·), fun s i ↦ y.2 s ⟨⟩ (z .refl (fun _ τ ↦ ⟨.refl, (H τ hA).2.2 s i⟩) (by simp [t]))⟩
 simpa [jump_eq_zero_iff] using fun h g hg ↦ g.ext fun w ↦ by
  simpa [-mulVec_single, n8, mul_vecMulVec, vecMulVec_mul, vecMulVec_mulVec, ← map_mul, ht, ← Finset.sum_mul, ← Pi.single_mul, ← sum_mulVec, ← map_sum, n3, hodgeTateMaps.pull] using congr(∑ i, ∑ c, ∑ x, $(h _ (hodgeTateMaps.pull
   (intertwiner f f' fun _ ↦ vecMulVec (f (n1 i 0 c) *ᵥ w) (Pi.single x 1)).toLin'
   (by simp [← a, n9]) ⟨g, hg⟩).2) (f' (n1 i c) *ᵥ Pi.single x 1))
end
section
attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
open Finset Matrix LaurentPolynomial
seal Finset.univ Finset.sum Finset.prod in
private lemma ac_v3 {p} [ThePrime p] {n} [Fintype n] (κ : n → ℤ) (x : n → ℂ_[p]) (F : MvPolynomial n ℂ_[p]) (h : ∀ᶠ g in nhds 1, F.aeval (fun i ↦ (cyclotomicGp g ^ (-κ i)).1 • g • x i) = 0) : F.aeval (fun i ↦ T (κ i) * C (x i)) = 0 := by
 simp_rw [F.aeval_def, F.eval₂_eq', ← F.support.sum_coe_sort, ← Algebra.smul_def] at *; let ⟨V, h⟩ := NonarchimedeanGroup.is_nonarchimedean _ h
 refine le_of_hodgeTate_stable le_rfl (∑ i, ·.1 i * κ i) (of _).vecMulLinear.ker
  (Fintype.linearCombination ..).ker (fun a u ↦ .mono V.mem_nhds_one fun k o ↦ funext fun g ↦ ?_)
  (fun v i a _ e _ _ ↦ .trans (sum_congr rfl fun l _ ↦ by cases e l <;> simp [*, T, C]; rfl)
  (sum_smul.symm.trans (congr($a 1 • T _).trans (by simp)))) (funext fun g : V ↦ h g.2)
 simpa [mul_pow, smul_smul, smul_prod', dotProduct, _root_.zpow_mul', vecMul, smul_sum, by simpa [-map_prod] using fun f ↦ map_prod (zpowersHom _ (cyclotomicGp k)) (.ofAdd ∘ f : n → _), mul_zpow, smul_pow, prod_smul, smul_comm k] using congr(k • $u (⟨k, o⟩⁻¹ * g))
end
section
open IsLocalization Subgroup
attribute [local grind =] mem_star_place star_natCast star_star below_star
attribute [local simp] Function.uncurry mul_assoc starRingEnd_apply
private lemma ac_t4 {ℓ E a d} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E] [StablyUnram E] (ha : Odd a) {κ f} (hf : f ∈ (stdSpace E (Fin a)).forms κ) {S P} (hP : IsSphericalOff S f P) {w₀ v} (hS : w₀ ∈ S) (hu : IsSplitPrimeToDisc (w₀.below _)) {χ} (hty : IsCuspidalType (localCongruence _ _ 0) χ) (hχ : ∀ j, rightRegular ℂ _ _ (atSplit hu.star_ne j.1) f = χ j • f) (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below _) {ε : Ω →+* PadicAlgCl ℓ} (hσ : placeOfEmb (ε.comp (algebraMap ..)) = v) {e : Fin a → ℤ} (he : FreeInts e) (he' : ∀ i, e i ∈ jumps κ a (.comp ιℓ.symm (ε.comp (algebraMap ..)))) w' (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧ (↑ℓ ∈ w'.1 → w'.below (QuadField d) = w₀.below _)) : ∃ r : GalRep ℓ E (Fin a), Continuous r ∧ (∀ᶠ y in mostFrobenii E, (r y.frob).1.charpoly = (P y.w).map ιℓ) ∧ (w' ∉ S ∧ star w' ∉ S → SphericalClause r Eq (jumps κ a) w' ((P w').map ιℓ)) := by
 have _ := NeZero.of_pos ha.pos
 have {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
 let F := pure v ⊔ Filter.principal {w | w' = w ∧ w' ∉ S ∧ star w' ∉ S}
 refine
  (ac_j1 ((mostFrobenii E).map (·.w) ⊔ F) (jumps κ a) (P · |>.map ιℓ) fun τ₀ ↦ let s₀ := (ιℓ.symm.toRingHom.comp (ε.comp (algebraMap ..))).comp (algebraMap (QuadField d) E)
  ?_).elim fun b ⟨r, hr, hd, h₁, gv, gc⟩ ↦ ?_
 obtain ⟨⟨ξ, μ, n, A₀, hμ, hξ, hz, hl⟩, Ψ, ⟨hv₀, hΨ⟩, N, h, model⟩ := exists_occursInWeight ha (algebraMap ..) s₀ κ, exists_pel a _ {w₀, w'}
 have ev w := (eventually_notMem_star_notMem d S).and ((tendsto_place_comap_cofinite (algebraMap
  ..)).eventually (eventually_notMem_star_notMem N ((insert w S).image (.below (QuadField d)))))
 obtain ⟨w₁, g₁, ⟨⟨k₁, k₂, -⟩, hw⟩, nt⟩ := ((frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime).and_eventually ((ev w').and (eventually_isNeat (n := Fin a)))).exists
 let B := insert w₁ {w ∈ S ∪ S.image star | star (w.below (QuadField d)) ∉ [w₀.below _, w'.below _]}
 have cv : ∀ w ∈ insert w₁ S, w ∈ B ∨ star w ∈ B := by clear * - hu hw' this hv hσ; grind
  [IsSplitPrimeToDisc.star_ne_and_prime_norm, natCast_mem_placeOfEmb]
 choose 𝔑 h𝔑 hB hlev using exists_levelGU_conj_le (⟨rightStab f, hf.1⟩ ⊓ (.comap _ (Gf.continuous_atPlace w₀) ⟨localCongruence _ _ 0, isOpen_localCongruence⟩ ⊓ .comap _ (Gf.continuous_atPlace w₁) ⟨_, isOpen_proIwahori⟩) : OpenSubgroup _).2 (fun k h ↦ ⟨congrFun (hP.2.1 k (h.imp_right (by simp))), by simp [Gf.mem_trivialOn.1 h.2, *]⟩) cv N
 obtain ⟨gv, k₃⟩ : F.Eventually (IsSafe 𝔑) ∧ 𝔑 ∉ (star w₀).1 ∧ 𝔑 ∈ w₁.1 ∧ 𝔑 ∉ (star w₁).1 := by
  simp [F, IsSafe, hB, B]; clear * - hu hv hw' hS h hw g₁ this
  grind -ring -linarith
 have gS w : IsSafe 𝔑 w → 𝔑 ∈ w₀.1 ∧ w ∉ S ∧ star w ∉ S := by clear * - cv hB hS k₃; grind [IsSafe]
 choose t ht ht' using fun w : SafePlace 𝔑 ↦ ((gS _ w.2).2.elim (hP.2.2 _ w.1.2)).2
 have η := nt 𝔑 (by simp [·] at k₃) k₃.2.1
 obtain ⟨⟨D, rfl, rfl, T, V⟩, _, -⟩ := model 𝔑 η.1 h𝔑, trace_definiteForms ξ η 1 1
 have O (u : Gf E D.Index) : IsSignedFrameFor (invTransposeGL u.1) .. := isSignedFrameFor_one (entryConj u)
 let Q (p : _ × Gf ..) : _ ⧸ levelGU D.Index D.𝔑 := ⟦toFinGL p.1 * invTransposeGL p.2.1⟧
 let φ := Q.extend (fun (y, u) ↦ ξ y (f u)) 0
 have hφ o : φ (Q o) = _ := Function.FactorsThrough.extend_apply (fun ⟨z, t⟩ ⟨y, u⟩ e ↦ by
  obtain ⟨⟨y, rfl⟩, e⟩ := mul_left_surjective z y, QuotientGroup.eq.1 e
  have := hf.2 (entryConj ⟨y, ((O u).conj_eq_smul (O t)
   (by simpa [-IsScalarFrame] using levelGU.isScalarFrame_inv_one e)).trans (by simp)⟩) u
  rw [← mul_inv_cancel_left t (_ * u), (hlev _ ?_).1] at this; simp [*]
  simp; erw [stdSpace_embFin]; simpa using! e) ..
 choose L H using fun w hw x ↦ @by_cases (∃ z k p, Q p = ⟦toFinGL z * (x * conjAtSplit w k)⟧)
  (∃ L : _ →ₗ[ℂ] _, ∀ y g, φ ⟦toFinGL y * (x * conjAtSplit w g)⟧ = ξ y (L (rightRegular ℂ _ _ (atSplit w.2 g) f))) (fun ⟨z, k, p, e⟩ ↦ by
  rw [QuotientGroup.eq] at e; have := conjAtSplit_dualComponent (w := w) hw e
  generalize dualComponent (n := D.Index) w _ = c at this
  exact ⟨ξ _ ∘ₗ .proj _, fun y g ↦ (congrArg φ (QuotientGroup.eq.2 (by simpa using! (inv_mul_eq_of_eq_mul (this.2 (k⁻¹ * g)) ▸ mul_mem (inv_mem this.1) e :)))).symm.trans ((hφ (y * (z⁻¹ * _), _ * atSplit w.2 (c * k⁻¹) * _)).trans congr($(map_mul ξ ..) _))⟩)
  (⟨0, by simp [φ, by simpa using ·]⟩)
 let s := @centralScalar E _ _ _ D.Index
 have hc x g : g * s x = s x * g := commute_scalar_GL ..
 have mem : cyclicSpan ((rightRegular ..).comp s) (φ ⟦·⟧) ≤ definiteForms D.𝔑 ξ := Submodule.span_le.2 fun _ ⟨x, e⟩ ↦ e ▸ ⟨⟨fun y z ↦ H ⟨_, hu.star_ne⟩ k₃.1 |> fun G ↦ by simpa [← (by simpa using G · 1 1)] using G _ y 1, fun z ↦ (dite_eq_right fun ⟨p, e⟩ ↦ · (by
  simpa [s, ratConj] using IsSignedFrame.mul ⟨_, O p.2⟩ p.1 (mul_mem (QuotientGroup.eq.1 e).1
   (inv_mem (centralScalar_mem_GU x).1))))⟩, by simp [funext_iff, hc, ← mul_assoc]⟩
 choose ω ψ hψ' hψ cen using @exists_eigencharacter ℂ _ _ _ _ _ _ (.of_fg (.of_le .of_finite mem))
  _ _ _ apply_mem_cyclicSpan
  (hP.1 <| by ext1; simpa using (hφ (1, _)).symm.trans congr($(· self_mem_cyclicSpan) _))
 obtain ⟨hF, c, h₃⟩ := mem hψ', Finsupp.mem_span_range_iff_exists_finsupp.1 hψ'
 have hω' x h : x ∈ ω.toHomUnits.ker := Units.ext ((smul_left_inj hψ).1 (cen x ▸ hF.2 ⟨_, h⟩ :))
 let L w h := c.sum fun x r ↦ r • LinearMap.pi (L w h <| s x * ·)
 have hL w h g : rightRegular ℂ _ _ (conjAtSplit w g) ψ = L w h ((rightRegular ℂ ..).comp (atSplit w.2) g f) := by
  simp [funext_iff, ← h₃, L, Finsupp.sum, ← mul_assoc, hc, (by simpa using H _ h · 1 ·)]
 replace h₃ := (by simpa using hL · · 1 |>.symm)
 obtain ⟨hs, hω⟩ : IsTestVector _ (rightRegular ..) ψ ⟨_, hu.star_ne⟩ ⟨_, g₁⟩ χ ∧ (ω.toHomUnits, .ofAdd A₀) ∈ algHeckeChars _ := by refine ⟨⟨⟨hS.ne_of_notMem k₁, k₃⟩, ⟨fun g h ↦ by simpa using (hlev _ h).2.1, fun _ ↦ (·.1)⟩, hty, fun _ h ↦ by simpa using (hlev _ h).2.2, hψ, ?_, ?_⟩, isOpen_mono (hω' · ⟨(centralScalar_mem_GU _).1, mem_comap.1 ·⟩) ((isOpen_congruenceGL_span η.1).preimage (.of_coeHom_comp <| .matrix_diagonal <| by simp; fun_prop)), fun x ↦ (smul_left_inj hψ).1 (cen _ ▸ funext fun y ↦ congr(ψ $((hc ..).trans ?_)).trans ((hF.1.1 _ y).trans (congr($(hz x) _).trans ?_)))⟩ <;> simp +contextual [s, h₃, k₃, ↓hL, Units.ext_iff, ↓hχ, ↓by simpa [mem_sphericalAt_iff g₁] using (hP.2.2 _ g₁ k₁ k₂).1]
 let M := ⨅ w, ⨅ _ : IsSafe D.𝔑 w, w.1.primeCompl
 have hM w : Disjoint M.carrier w.1 ↔ IsSafe D.𝔑 w := by
  have ⟨y, _, e, _⟩ := exists_levelGU_conj_le (n := Unit) isOpen_univ le_top (S := {w}) (fun _ ↦ .inl) 1
  clear * - e; simp_all [M, Set.disjoint_left, Ideal.one_notMem]; grind
 have z : M ≤ _ := iInf₂_le_of_le v gv.1 v.1.primeCompl_le_nonZeroDivisors
 choose ρ hρ H₁ using (exists_model (nonempty_universalFamily z fun m k ↦ V _ ((hM ⟨_, .comap _, (bot_lt_under_prime M (Localization.subalgebra E M z) z m (m.bot_lt_of_maximal
  (Ring.not_isField_of_ne_of_ne (Ideal.map_ne_bot_of_ne_bot v.3)
  ((map_algebraMap_ne_top_iff_disjoint ..).2 ((hM v).2 gv.1)))).ne').ne'⟩).1 ((disjoint_under_iff
  ..).2 k.1.1))).some η T V _).some.exists_galois_rep η M iInf₂_le (fun w ↦ t w * ((ω (unifNorm w.1))⁻¹ ^ ·))
  (.filter (fun _ ↦ τ₀.comp (algebraMap ..) = s₀) ((jumps κ _ τ₀).map (· + ↑μ))) fun u hu ↦ by
  obtain ⟨⟨u, o, rfl⟩, e⟩ := by simpa using hu
  refine (hl _ e u o).imp_right (· hv₀ hΨ η hs hF fun w j ↦ ?_)
  erw [asAlgebraHom_tau (w, j) hF.2, ← h₃ _ (w.2.2.2 _ (below_star ..)), ← map_heckeFun _ (isBiInvariant_basicDoubleCoset
   j).1 fun g ↦ by erw [h₃, hL], ht', map_smul, h₃, map_smul, cen]; simp [smul_smul]
 refine (ac_j0 (.baseChange ⟨_, hω⟩) μ hρ).imp fun _ ⟨c, H₂⟩ ↦ ⟨c, .mono ⟨eventually_mostFrobenii (ev w₁) fun y ⟨a, k⟩ ↦ ?_, gv⟩ fun w g A hA ↦ ?_⟩
 have g : IsSplitPrimeToDisc (y.w.below (QuadField d)) := (mem_zmultiples_of_prime_card (hp := ⟨y.prime_q⟩) rfl (Ideal.Quotient.eq_zero_iff_mem.1.mt a.2.2)).elim fun a e ↦ ⟨a * d, by
  simpa using Ideal.Quotient.eq.1 e.symm, 1 - 2 * a * QuadField.sqrtNegDInt d, 2 * a * QuadField.sqrtNegDInt d + 1, by clear * -; simp; grind [QuadField.sqrtNegDInt_sq d]⟩
 simp [IsSafe, hB]; clear * - g k this; grind -ring -linarith
 have K s (e : inducedPrime s = w) : s.comp (algebraMap ..) = s₀ := (NumberField.InfinitePlace.mk_eq_iff.1 (by subsingleton)).resolve_right fun h ↦ g.2.2 _ (by ext; simpa [← hv.2.2, ← e, ← hσ, s₀, map_star_CM, -starRingEnd_apply] using (congr(‖ιℓ ($h _)‖ < 1)).symm) (gS w g).1
 refine ht ⟨⟨w, g.1.star_ne⟩, g⟩ ▸ Fintype.card_fin _ ▸ (H₂ w ?_ (fun x r ↦ hω' _ (mem_levelGU_of_local (centralScalar_mem_GU _).1
  (by simpa [s, mem_intGL, ← map_inv, ite_mem, Matrix.diagonal, star_eq_adeleMap] using! (coe_idelesUnitOff_empty.le (locIdele_mem_idelesUnitOff r)).imp adeleNorm_mem_Ohat adeleNorm_mem_Ohat) fun v h ↦ ⟨1, by simpa using! evalAt_centralScalar_of_ne (g.2.2 v · h) x⟩)) (H₁ ⟨⟨w, _⟩, g⟩) hA).imp_right (.imp_left (·.congr hA ?_)) <;> simp +contextual [*, AlgHeckeChar.baseChange, apply_ite, RingHom.algebraMap_toAlgebra]
 clear * -; grind
 obtain ⟨⟨j, hj⟩, z, q, -⟩ := exists_inducesPlace E Gal(Ω/E) (ι := ε) rfl, gv (hσ ▸ isPlaceOver_placeOfEmb ε)
 let := PadicPlaceEmbedding.mk (toOverGp := ⟨_, ⟨hj.2.1.2⟩⟩) _ hj
 choose T k hT hk _ using z.2.isPotCrys.exists_isHodgeTateFrame (Pi.basisFun ..) (IsScalarTower.toAlgHom ..)
 obtain ⟨rfl, u⟩ := by simpa using (ac_q9 r hr hd (.mp h₁ <| eventually_mostFrobenii (eventually_notMem_star_notMem ℓ S) fun y ⟨o, p, l⟩ g ↦ ⟨((g y.isPlaceOver).2.2 _ y.isFrob).1 (y.isPlaceOver.valuation_natCast_eq_one_iff.2 l), ((hP.2.2 _ (isSplit_of_q_prime y.prime_q) o p).isMonicOfDegree hP.1).rec (⟨by simp [·], ·.map _⟩)⟩) T⁻¹ k he (fun n ↦ by simpa
  [List.count_eq_zero] using (hk _ ▸ q (g := 1) (by tauto) _ (by simpa using! he' n) :)) fun F h ↦
    by convert ac_v3 (k ·.1) T⁻¹.1.uncurry F (nhds_one_le_map_nearOne _ (hT.mp (nearOne_eq_nhds_one hj.2.1 ▸ .mono (continuousAt_subtype_val h) fun g h f ↦ .trans (by congr!; erw [← inv_mul_apply_of_isHodgeTateFrame f]; simp [Matrix.mul_apply]) h)))
       simp)
 use r, hr, u, fun p A h ↦ (gc ⟨rfl, p⟩ h).rec fun u ↦ (⟨u, ·.imp_left fun k o γ τ t x ↦ ?_⟩)
 choose K c d using u.2.isPotCrys.exists_hasJumps γ
 rw [d, Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (nodup_jumps ..)).2
  (by simpa [d _, OccursIn] using! k t ·)) (by simp [c, jumps])]
end
section
open NumberField Polynomial Ideal Quotient IsAlgClosed Fint IsLocalRing RingHom algebraMap
variable {E : Type} [Field E] [EmbeddedNumberField E] (w : FinPlace E) (A : ClosurePlace) {K : Type} [Field K] [Algebra (ResField w) K] (T : MulChar K ℂ) (f) (s : Gal(Ω/E)) (a)
lemma w0 {R} [Field R] (g : _ →+* R) (h : w.1 ≤ ker g) : ∃ j : ResField w →+* R, ∀ x, j (algebraMap _ _ x) = g x := ⟨_, liftOfSurjective_comp_apply _ (algebraMap_ResField_surjective w) ⟨g, by simpa [LE.le]⟩⟩
def IsTameExponent := IsPlaceOver A w ∧ f ≠ 0 ∧ s ∈ inertiaGroup _ A ∧ ∃ (φ : 𝓞 Ω →+* K) (π : E)
 (z : Ω) (t : 𝓞 Ω), centrePrime Ω A ≤ ker φ ∧ (∀ x : 𝓞 E, φ x = (x : ResField w)) ∧ IsUniformiser A
 π ∧ z ^ (w.q ^ f - 1) = π ∧ t = s z / z ∧ T (φ t) = .exp (2 * Real.pi * .I / (w.q ^ f - 1 :)) ^ a
variable {w A f s a}
open Nat
def IsLabelledAt {ℓ} [ThePrime ℓ] [PadicIso ℓ] A T f (P : _ → _ → Prop) (c : (ResField w)[X]) := ∀ ⦃s a⦄, IsTameExponent w A T f s a → P s ((c.aroots K).map fun x ↦ X - C (ιℓ ((T ^ a) x))).prod
variable [IsFaithfulMulChar K T]
lemma IsTameExponent.pow_apply_charName {d} (h : IsTameExponent w A T f s a) {u} (hu : Valued.v u.1 = 1) (b : localArtin _ A w u = ⟦⟨s, d⟩⟧) χ : (T ^ a) ((charName T χ).1 : ResField w) = χ (residue _ ⟨u, hu.le⟩) := by
 obtain ⟨⟨c, q, _, ρ, π, z, t, o, _, p, r, _, e⟩, ⟨k, l⟩, x, g⟩ := h, w.q.sub_one_dvd_pow_sub_one f, algebraMap_ResField_surjective w (residue _ ⟨u, hu.le⟩)
 rw [l, pow_mul'] at r
 grind [thetaChar_charName, card_ResField, =_ (thetaChar_apply_pow T w.one_lt_q · (by simp [q, ne_of_gt]) l e), algebraMap_pow_card_pred_eq_one, mem_ker, @o (t ^ k - x) (by
  simpa [*, div_pow, mem_centrePrime] using! (c.localArtin_tame_symbol p hu b r).1 (residue_eq_iff_valuation_sub_lt_one.1 g.symm))]
lemma IsLabel.root_pow_eq_one {c : (ResField w)[X]} {r} (h : IsLabel r c) {x : K} (hx : aeval x c = 0) : x ^ (w.q ^ (r)! - 1) = 1 ∧ ∃ d ∈ Set.Icc 1 r, x ^ (w.q ^ d - 1) = 1 := have i := minpoly.irreducible ⟨c, h.1, hx⟩
 by grind [card_ResField, aroots_pow_eq_frobenius_orbit i (j := 1) (K := K), aeval_def, eval₂_at_zero, map_eq_zero, IsLabel, pow_pred_eq_one_iff, root_pow_card_pow_eq_self_iff, minpoly.aeval, dvd_factorial, i.natDegree_pos, natDegree_le_natDegree, minpoly.min, one_lt_pow₀ w.one_lt_q]
lemma exists_isTameExponent (hA : IsPlaceOver A w) f : (∃ s : inertiaGroup _ A, IsTameExponent w A T (f)! s.1 1) ∧ ∀ s ∈ inertiaGroup _ A, ∃ a, IsTameExponent w A T (f)! s a ∧ (s = hA.tameGenerator → a.Coprime (w.q ^ (f)! - 1)) := by
 obtain ⟨_, H : NeZero ((w.q ^ (f)! - 1 :) : ResField w)⟩ := hA.centrePrime_liesOver, ⟨by simp [← card_ResField, Fin.pos']⟩
 let := Quotient.field w.1
 let := Algebra.compHom K (lift w.1 (algebraMap _ (ResField w)) (by simp))
 let ρ := (lift : _ →ₐ[_ ⧸ w.1] K).1.comp (mk (centrePrime Ω A))
 obtain ⟨_, n, hv⟩ := H.of_faithfulSMul _ K, H.of_neZero_natCast, hA.valuation_natCast_eq_one_iff.2 (mt algebraMap_ResField_eq_zero.2 (mod_cast H.1))
 choose π z u hz g using hA.exists_tameGenerator.choose_spec _ hv
 choose j _ G k using ((isRoot_cyclotomic_iff.1 (map_cyclotomic _ ρ ▸ (isRoot_cyclotomic_iff.2
  g.toInteger_isPrimitiveRoot).map)).map_of_injective
  IsFaithfulMulChar.injective).isPrimitiveRoot_iff.1 (Complex.isPrimitiveRoot_exp _ n.1)
 apply g.pow_of_coprime at G
 have r s h {a} e : IsTameExponent w A T _ s a := ⟨hA, by simp, h, ρ, π, z, (g.toInteger ^ j) ^
   a, by grw [← comap_ker, ← ker_le_comap, mk_ker], (lift.2 <| mk _ ·), u, hz, e, by aesop⟩
 use ⟨_, r _ (hA.tameGenerator ^ j).2 (inertia_pow_smul_div hA.tameGenerator.2 hv hz _ ▸ pow_one
  _)⟩, ((G.eq_pow_of_pow_eq_one (by simp_all [div_pow, ← map_pow])).imp fun a ⟨_, e⟩ ↦ ⟨r · · e, (by rwa [← G.pow_iff_coprime n.pos, e, ·])⟩)
end
section
section
open NumberField Ideal Algebra ComplexEmbedding Subgroup QZChar QZ FractionalIdeal RingOfIntegers
section
variable {E} [Field E] [EmbeddedNumberField E] [IsCMField E] (χ : QZChar Gal(Ω/E))
noncomputable abbrev QZChar.w1 := fixedFieldOf (ker (symmetrise χ))
instance : IsCMField (w1 χ) := s08_z7 E fun y ↦ ⟨⟨_, (cmConj_cmConj
 _ ▸ congr(cmConj $(y.2 ⟨_, add_eq_zero_symm <| congr(χ.1 $(conjGal_conjGal _) + _).trans ·.2⟩)))⟩, (lift_comp_algebraMap Ω · ▸ let J := lift Ω _; (exists_smul_emb_eq _ (J.comp cmConj) (star J) (by
  ext; simpa using map_star_complex (J.comp _) _)).rec fun g h ↦ (y.2 ⟨g, map_mul_eq_one (toHom χ)
  (mul_eq_one_symm (by ext; simp_all [← J.injective.eq_iff, conjGal]))⟩ ▸ h y :))⟩
end
open InfinitePlace in noncomputable instance {E} [Field E] [EmbeddedNumberField E] [CMType E] (χ : QZChar Gal(Ω/E)) : CMOver E (w1 χ) where
  Φ u := let e := u.embedding; ite (e.comp (algebraMap ..) = Φ (u.comap (algebraMap E _))) e (star e)
  mk_Φ := by aesop
  mem_type_iff := by grind [embedding_mk_eq, Φ_eq_or, comap_mk, conjugate_comp, star_star]
variable {E} [Field E] [EmbeddedNumberField E] [IsCMField E] (χ : QZChar Gal(Ω/E))
instance [h : StablyUnram E] : StablyUnram (w1 χ) := ⟨_, h.1.choose_spec.map_of_injective (algebraMap ..).injective⟩
lemma QZChar.w7 {u : FinPlace (w1 χ)} (h : ∀ {A : ClosurePlace}, IsPlaceOver A (u.below E) → inertiaGroup _ A ≤ ker (symmetrise χ)) : ¬u.1 ∣ differentIdeal (𝓞 E) _ := not_dvd_differentIdeal_iff.2 <| ramificationIdx_eq_one_iff.1 ((u.isPlaceOver_placeOver.isPlaceOver_below.ramification_in_tower _
 u.isPlaceOver_placeOver).2.1 (h u.isPlaceOver_placeOver.isPlaceOver_below))
private lemma ac_w8 [StablyUnram E] {p} (hp : Nat.Prime p) (h : p • χ = 0) {g₀} (h₀ : (symmetrise χ).1 g₀ ≠ 0) (ht : ∀ {A : ClosurePlace} {u : FinPlace E}, IsPlaceOver A u → ↑p ∈ u.1 → inertiaGroup _ A ≤ ker (symmetrise χ)) : IsStep (w1 χ) (ideleChar χ) ∧ Module.finrank E (w1 χ) = p := have := Fact.mk hp
  (iff_and_self.2 fun | rfl => ⟨isOpen_mono (expUnit.ker.ker_le_comap _)
    (continuous_iff_isOpen_ker.1 continuous_artinMap χ), by simp [artinMap_principalIdele, isTotallyPositive_of_isTotallyComplex], by simp [isTotallyPositive_of_isTotallyComplex, ← abelianLift_symmetrise, char_artinMap_eq_one_iff (symmetrise χ), expUnit_eq_one_iff], ((eq_top_iff_one _).1 ((IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists (not_isField E) (intTrace ..).range).not_right.2 fun ⟨u, hI⟩ ↦ by
    obtain ⟨n, P, ⟨⟩⟩ := coeIdeal_ne_zero (K := E).2 u.3, FinPlace.comap_surjective (algebraMap E (w1 χ)) u
    refine w7 χ (ht · (hI ⟨1, ext ?_⟩)) <| dvd_iff_le.2 <| (differentialIdeal_le_iff (L := w1 χ)
      ?_).2 fun _ ⟨x, hx⟩ ↦ coe_one.le <| (div_self n).le <| (mem_div_iff_of_ne_zero n).2 fun
      | _, ⟨a, ha, rfl⟩ => ((mem_inv_iff ?_).1 hx.1 _ ⟨_, ha, rfl⟩).rec fun z _ ↦ ⟨_, hI ⟨z, rfl⟩, ?_⟩ <;> simp_all [algebraMap_intTrace (L := w1 χ), algebraMap_eq_smul_one, trace_apply, map_one, P.3])).imp (by simp [← algebraMap_intTrace (A := 𝓞 E)])⟩).1 (by
    rw [finrank_fixedFieldOf, eq_comm, ← hp.dvd_iff_eq (h₀ <| index_eq_one.1 · |>.ge ⟨⟩), index_ker]
    exact .trans (card_dvd_of_le fun | _, ⟨_, rfl⟩ => χ.2.2 .. ▸ exists_ofZMod congr($h.1 _))
      (p.card_zmod ▸ card_range_dvd (ofZMod p).toMultiplicative))
lemma s08_w9 {E} [Field E] [EmbeddedNumberField E] [CMType E] {w : FinPlace E} {A : ClosurePlace} [WeilData E] {p} (hw : w.IsSplit) (hA : IsPlaceOver A w) (hp : p.Prime) (χ : _ →* _) {x₀} (h₁ : χ x₀ ≠ 1) (hχ : ∀ x, χ x ^ p = 1) (ht : ∀ x, Valued.v x.1 = 1 → χ (x ^ (w.q - 1)) = 1) : ∃ ν : QZChar Gal(Ω/E), let E' := QZChar.w1 ν; ∃ (u : FinPlace E')
  (_ : WeilData E'), IsStep E' (QZChar.ideleChar ν) ∧ Module.finrank E E' = p ∧ u.IsSplit ∧ (∀ u', u'.below E = w ↔ u' = u) ∧ IsPlaceOver A u ∧ (∀ x, QZChar.abelianLift ν (artinAt _ w x) = 1) ∧ ∀ x, QZChar.abelianLift (QZChar.symmetrise ν) (artinAt _ w x) = χ x := by
 obtain ⟨_, ν, hν, h⟩ := Fact.mk hp, grunwald hp (((@finite_natCast_mem _ _ _ _ ⟨hp.ne_zero⟩).insert w).insert (star w)) (.mk' (χ ∘ ideleAt w ∘ star) (by simp)) (isOpen_of_forall_pow_mem hp.ne_zero (T := χ.ker) (by simpa)).preimage_of_continuous (by tauto)
 replace ht h x e := (pow_eq_one_iff_of_coprime (.of_dvd_left
  ((w.natCast_mem_iff_dvd h).1 w.1.absNorm_mem) (by simp))).1 ⟨hχ _, map_pow χ .. ▸ ht x e⟩
 have h₆ := by simpa [star_locIdele, hw.symm] using h w
 have h₅ x := by simpa [*, star_locIdele (v := w) x ▸ h ..] using QZChar.abelianLift_symmetrise ν (locIdele w x)
 replace h {A u} (hA : IsPlaceOver A u) (a : star u = u ∨ ↑p ∈ u.1) := (hA.artinAt_units_trivial_iff_unramified (QZChar.symmetrise ν)).1 fun x b ↦ by_cases (by aesop)
  fun _ : w ≠ u ↦ by by_cases w = star u <;> subst_eqs <;> cases a <;> simp_all [star_locIdele, mt isSplit_of_q_prime, ← artinMap_locIdele, QZChar.abelianLift_symmetrise]
 obtain ⟨⟨_, hg₀, e₀⟩, u, _, ⟨⟩⟩ := (hA.range_abelianLift_artinAt _).le ⟨_, h₅ x₀⟩, hA.exists_above (L := QZChar.w1 ν)
 obtain ⟨_, ⟨⟩⟩ := ac_w8 ν hp hν (e₀ ▸ h₁) (h · ∘ .inr)
 simp [← hA.ncard_above_mul_relIndex (QZChar.ker (QZChar.symmetrise ν)), Nat.prime_mul_iff, Set.ext_iff, LE.le] at hp hg₀
 use ν, u, (q5 fun v e ↦ QZChar.w7 _ (h · ?_)).some <;> grind [below_star]
open IsDedekindDomain HeightOneSpectrum Nat ZMod decompGroup QuadField algebraMap
attribute [local simp] QZChar.comap mul_mem_right mul_mem_left two_smul neg_eq_self NeZero.ne
private lemma ac_r3 E [Field E] [EmbeddedNumberField E] [IsCMField E] [StablyUnram E] (n : ℕ) (hn : n ≠ 0) : ∃ χ : QZChar Gal(Ω/E), let E' := w1 χ; let U := ker (symmetrise χ)
    let N := U ⊓ ker χ; ∃ᵉ (D) (_ : HasQuadSubfield D E'), IsStep E' (ideleChar χ) ∧ (∃ m, ∀ H :
      Subgroup Gal(Ω/E), inertiaAbove {x : FinPlace E | ↑n ∉ x.1 ∧ x.q ≤ m} ⊆ H → ∀ g, ∃ h ∈ H, g * h ∈ N) ∧ (∀ u : FinPlace E', ↑n ∈ u.1 → IsSplitPrimeToDisc (u.below (QuadField D))) ∧ ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w → ↑n ∈ w.1 → decompGroup _ A ≤ U ∧ inertiaGroup _ A ≤ N ∧ (w.IsSplit → decompGroup _ A ≤ N) := by
  let k := Ideal.absNorm (span {(4 : 𝓞 E)})
  let R := 4 * n * (2 * n) ^ k
  have ⟨j, b, O⟩ := @exists_eq_two_pow_mul_odd R (by aesop)
  let C := 1 + b * (2 + 8 * b)
  have ⟨q, g, p, f⟩ := @forall_exists_prime_gt_and_eq_mod R ⟨by aesop⟩ _ (-unitOfCoprime C (by
    cases j <;> simp [*, C, coprime_mul_iff_right, parity_simps]))⁻¹.isUnit
    (C * n * Ideal.absNorm (differentIdeal ℤ (𝓞 E)))
  let D := C * q
  obtain ⟨⟨M, hD⟩, Z, _⟩ := (natCast_eq_zero_iff (D + 1) R).1 (by simp [D, f, neg_add_eq_zero]), (eq_zero_of_dvd_of_lt · g), Fact.mk p
  obtain ⟨d, ⟨P, r⟩, ⟨i, ω, _⟩, ⟨⟩, s, t, l⟩ := Fact.mk (by lia : D % 4 = 3), FinPlace.exists_natCast_mem E q, ‹StablyUnram E›.exists_i_c₀, exists_wellFoundedLT (FinPlace E), @Prime.sq_add_sq q _ (by grind [C.mul_mod q 4])
  simp [p.dvd_mul, ← P.natCast_mem_iff_dvd r, *] at Z
  have ⟨α, _⟩ : ∃ α : 𝓞 E, α * star α = D := ⟨(1 + 2 * b * ω) * (s + t * i), by simp [D, ← l]; grind⟩
  obtain ⟨B, s, hs⟩ := P.isPlaceOver_placeOver, @exists_forall_sub_mem_ideal _ _ _ (@finite_natCast_mem _ _ _ _ ⟨hn⟩)
    (·.1.1 ^ k) (fun _ _ ↦ by grind [isCoprime_pow_of_ne]) fun w ↦ ite (star w.1 < w) α 1
  have N {w : FinPlace E} (h : 2 * n.cast ∈ w.1) :
    ↑(D + 1) ∈ w.1 ^ k := by simp [hD, R, pow_mem_pow h]
  let t := ite (s = 0) 1 (s * star s)
  have T {w} (h : ↑n ∈ asIdeal w) : 1 - α * t * ite (w < star w) i (star α) ^ 2 ∈ w.1 ^ k ∨ star w = w ∧ α * t ∉ w.1 ∧ 2 ∉ w.1 := by grind [hs ⟨w, h⟩, =_ Quotient.eq_zero_iff_mem, star_star, one_notMem w.1, IsConcreteLE.le_iff, Ideal.mem_comap, le_comap_pow _ k (hs ⟨star w, by simpa⟩), pow_le_self, show k ≠ 0 by simp [k], starRingEnd_apply, mem_star_place, → w.2.2]
  obtain ⟨⟨b, hb⟩, ⟨G, -, U⟩, _⟩ := IsAIC.exists_pow_eq 2 (↑(↑(α * t) : E) : Ω), B.decompGroup_spec
    Gal(Ω/E), by simpa [addOrderOf_eq_prime_iff] using QZ.addOrderOf_mk_inv two_pos
  have S (g : Gal(Ω/E)) {c : Ω} {x : E} (h : c ^ 2 = x) := eq_or_eq_neg_of_sq_eq_sq (g c) c (by simp [← map_pow, h])
  have L {A w g c} (a : IsPlaceOver A w) hg {x u : 𝓞 E} h (H : 1 - x * u ^ 2 ∈ w.1 ^ k) := (@S g c x h).resolve_right fun e ↦ have o (z : Ω) := A.valuation.map_add_le le_rfl (val_smul
      (σ := g) hg (1 + z * (u : E))).le; mt (Int.natAbs_le_of_dvd_ne_zero ∘ absNorm_dvd_norm_of_mem) (by simp [k, Nat.lt_pow_self]) (show 4 ∈ w.1 ^ k by
    rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := E)] at *; grw [← H, ← a.isEquiv.le_iff_le]
    convert mul_le_mul' (o c) (o (-c)) <;> simp [← map_mul, map_ofNat] <;> grind)
  let y := (i / t : E) * b * cmConj b
  have hy : y ^ 2 = ((-D : 𝓞 E) : E) := by
    simp [y, mul_pow, ↓← map_pow, hb, -map_neg, t]; field_simp [ite_eq_iff]
    exact_mod_cast by grind [star_mul, star_star]
  have := by simpa [y] using congr($hy = 0)
  let χ : QZChar _ := ⟨_, ((isLocallyConstant_smul b).comp (if · = b then 0 else .mk
    2⁻¹)).continuous, fun g h ↦ by cases S g hb <;> cases S h hb <;> simp [*]⟩
  have H {g} : (symmetrise χ).1 g = 0 ↔ g y = y := by cases S g hb <;> cases S g (by
           rw [← map_pow cmConj, hb, cmConj_algebraMap]) <;> simp [*, y, χ, conjGal]
  have Y {A w} a h g m := H.2 (@L A w g _ a m _ 1 hy (by simpa [add_comm] using N h))
  have ⟨σ, I, J⟩ := G.exists_inertia_smul_eq_of_pow_eq (@U (.mk0 _ (by simp)) (B.isUniformiser_iff.2 (by erw [valuation_of_algebraMap]; simp [D, *, p.ne_zero, -NeZero.ne, intValuation_eq_exp_neg_multiplicity, mt dvd_differentIdeal_of_mem_sq (Z.2 <| le_of_dvd
    · (absNorm_mem _)), multiplicity_eq_of_dvd_of_not_dvd (k := 1)]))) two_pos hy (neg_sq y)
  have J := mt H.1 (J.trans_ne (by simpa [y]))
  let := (@embOfSqrt D (w1 χ) _ _ ⟨y, (H.1 ·.2)⟩ _ (by ext; simp [*])).toAlgebra
  use χ, D, {}, (ac_w8 χ prime_two (by ext; simp [χ, ite_add_ite, *]) J fun a h ↦ (Y a (by simp_all) · ·.1)).1, ⟨P.q, fun U e g ↦ .imp' _ (fun i : Fin 2 × Fin 2 ↦ (⟨mul_mem (pow_mem (e ⟨P, ?_, _, B, I⟩) i.1) (pow_mem (e ⟨_, ?_, _, B.conjPlace_star, I.conjPlace_conjGal⟩) i.2),
    ·⟩)) (Not.imp_symm (by simp [↓map_mul, toHom, χ, ← ofAdd_add]; split_ifs <;> simp [*]) J)⟩, fun u h ↦ ((u.below _).2.2 ((c₀_mul_one_sub D).substr ?_)).elim
    (fun _ ↦ ⟨0, ?_, 1, 1, by simp⟩)
    (⟨1, by simpa using neg_mem ·, -1, -1, ?_⟩), fun a l ↦ (fun y ↦ ⟨y, fun g i ↦ ⟨y _ i.1, ite_eq_left ((T l).elim (L a i.1 hb) fun _ ↦ inertia_fixes_root_of_unit i (a.valuation_natCast_eq_one_iff.2 ?_) hb (a.valuationVia_eq_one_iff.2 ?_) ?_)⟩, fun e _ g ↦ ⟨y _ g, ite_eq_left (L a g hb ((T l).resolve_right ?_))⟩⟩) (Y a ?_) <;> simp [↓valuation_eq_one_iff_notMem, *, -O, R, mul_assoc]
end
lemma IsWeakBaseChange.r4 {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n M M'} [Field E] [CMType E] [EmbeddedNumberField E] [Fintype n] {χ : QZChar Gal(Ω/E)} {f : _ → M → ℂ} {f' : Gf (QZChar.w1 χ) n → M' → ℂ} {S P P'} {r' : GalRep ℓ _ n} (hs : IsWeakBaseChange (QZChar.ideleChar χ) S f f') (hr' : Attached P' r') (he' : IsEigenform f' P') (he : IsEigenform f P) : let L := QZChar.w1 χ; let N := QZChar.ker (QZChar.symmetrise χ) ⊓ QZChar.ker χ
  let i : N →* _ := L.fixingSubgroupEquiv.toMonoidHom.comp (Subgroup.inclusion (id fun s h ↦ (·.2 ⟨s, h.1⟩))); N.IsOpen ∧ (∀ {r : GalRep ℓ E n}, Attached P r → ∀ A, (IsFiniteTypeAt r' A → IsFiniteTypeAt r A) ∧ (∀ {κ} m, HasJumpsAt r' A (jumps κ.baseChange m) → HasJumpsAt r A
   (jumps κ m)) ∧ ∀ s, (r s.1).1.det = (r' (i s)).1.det ∧ ∀ Q, PolyKillsAt r' A (i s) Q → PolyKillsAt r A s Q) ∧ ∃ ρ : N →* _, Attached P ρ (·.1) ∧ ∀ s, ρ s = r' (i s) := by
 intro L N i
 obtain ⟨hφ, o⟩ := isOpenEmbedding_galois_restrict (Γ' := Gal(Ω/L))
  (AlgEquiv.restrictScalarsHom E) (by simp), (QZChar.isOpen_ker _).inter (QZChar.isOpen_ker χ)
 refine (fun c ↦ ⟨o, fun h A ↦ ?_, r'.comp i, c, by simp⟩) ⟨hr'.1.comp (hφ.continuous_iff.2 continuous_subtype_val), (hr'.2.1.comp L.fixingSubgroupEquiv.toMonoidHom).comp _, o.isOpenMap_subtype_val, (hr'.2.2.2 · · |>.and (eventually_mostFrobenii he'.2 fun y ↦ (· y.prime_q)) |> mostFrobenii_push hφ _ |>.mp (eventually_mostFrobenii (he.2.and ((finite_ramified o).and hs.1.cj.compl_mem_cofinite)) fun x ⟨y, I, z⟩ B s e ↦ x.isPlaceOver.exists_above.rec fun u ⟨a, i⟩ ↦ have D : _ ≤ N := x.isPlaceOver.decompGroup_le x.isFrob o (I _ x.isPlaceOver) (by bound)
  have G := x.isPlaceOver.split_completely fun _ h ↦ (D h).1
  (B ⟨_, _, _, (G u i).1 ▸ x.prime_q, a, (G u i).1 ▸ (e ▸ x.isFrob :)⟩ i (by tauto)).rec fun b d ↦ (show _ → _ → P' u = P x.w by simp_all [HasHeckePolyAt, heckePoly, he'.1, smul_left_inj]) d.2
   ((hs.2 _ z u i).2 ⟨by simp [(x.isPlaceOver.artinAt_trivial_iff_decompGroup_le _).2 fun _ h ↦ (D h).2], G⟩ _ _ (y x.prime_q).2).2 ▸ b _ rfl))⟩
 choose Z h using c.2.1.exists_conj_of_trace_eq _ (.id ..) (h.2.1.comp N.subtype).hasSemiprimeSpan
  (c.trace_eq h · rfl)
 refine (local_clauses_of_retract 1 (algebraMap ..) (by simp) (by simp) hφ ((hφ.continuous.1 _ o).mem_nhds N.one_mem) (fun _ ↦ (h ⟨_, ·⟩)) Z.4).imp_right (.imp (fun b _ _ ↦ b Z.3 ∘ cast ?_) fun c s ↦ ⟨by simpa [field] using! congr($(h s).det).symm, @c _ s.2⟩)
 simp [jumps.eq_unfold]; congr!; apply CMOver.mem_type_iff
open Finset Matrix Fintype Filter Representation
attribute [local simp] smul_smul map_smul' _root_.zpow_mul scalarFin coe_divStar
lemma Attached.r5 {E n} [Field E] [Fintype n] [CMType E] {κ ℓ} [ThePrime ℓ] [PadicIso ℓ] [Algebra E Ω] {f P} {r : GalRep ℓ E n} (hr : Attached P r) (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P) : ∃ θ : AlgHeckeChar E, (∀ σ, θ.1.2.toAdd σ = (if σ = Φ (.mk σ) then 1 else -1) * (card n * κ.2 (.mk σ) + ∑ i ∈ .range (card n), i * κ.1 (.mk σ) i) - (card n).choose 2) ∧ (∀ w (hw : star w ≠ w) x, (Valued.v x.1 = 1 → ∀ {c : ℂ}, rightRegular ℂ _ _ (atSplit hw (.scalar n x)) f = c • f → θ.1.1 (locIdele w x) = c) ∧ (Valued.v x.1 = .exp (-1) → ∀ {Q}, HasHeckePolyAt f w hw Q → θ.1.1 (locIdele w x) = (-1) ^ card n * Q.coeff 0)) ∧ ∀ g, (r g).1.det = AlgHeckeChar.avatar θ g := by
  let z := (scalarFin (E := E) n).comp divStar.1
  choose χ _ e using exists_monoidHom_extend (.domRestrict (.fst _ ℂˣ) (Subgroup.mk ⟨⟨{p | rightRegular ℂ _ _ (z p.1)
    f = p.2 • f}, by simp_all [mul_comm]⟩, by simp⟩ (by simp_all))) (.domRestrict (.snd ..) _) ⊥ fun a e ↦ Units.ext ((smul_left_inj he.1).1 (a.2.symm.trans (by simp_all)))
  have h x c (h : rightRegular ℂ _ _ (z x) f = c • f) : (χ x).1 = c := congr($(e ⟨(x, .mk0 c fun _ ↦ by
      simp_all [IsEigenform, ← inv_apply_eq_iff, eq_comm]), h⟩).1)
  refine ⟨IsHeckeOfType.toAlgebraic (k := -2 * (card n).choose 2) (by simp; lia)
    ⟨((rightStab f).comap z).isOpen_mono (e ⟨⟨·, 1⟩, by simpa using! funext ·⟩) (hf.1.preimage ((U.isClosedEmbedding_mat (by simp)).continuous_iff.2 (.matrix_diagonal (by simp; fun_prop)))), fun x ↦ ?_⟩, congrFun (toAdd_ofAdd _), (and_iff_left_of_imp fun H g ↦ ?_).2 fun w hw x ↦ ?_⟩
  · simp [← prod_mul_distrib, -neg_add_rev, ← two_mul, ← mul_zpow, div_pow, sq (Φ _ _), ← Complex.conj_mul', mul_div_mul_right, h (principalIdele x) _ (by simp [funext_iff, fun g ↦ (Subtype.ext (by ext; simp [z, mul_comm, division_def]) : g * z (principalIdele x) = stdEmbFin (U.of (by simp) ((x.1 / star x.1) • 1) (by simp)) * g), stdSpace_weightRep_apply, hf.2 _, weylRep, Units.smul_def, schur_smul, @starRingEnd_apply E, ← prod_mul_distrib, ← zpow_add₀, ← zpow_natCast, ← _root_.zpow_mul]; tauto)]
  · exact (det_eq_sign_charpoly_coeff _).trans (tendsto_nhds_unique
      ((hr.tendsto_charpoly_coeff ..).const_mul _)
     ((tendsto_mostFrobeniiAt (AlgHeckeChar.avatar _ · |>.1)).congr' (mem_inf_of_left
      ((AlgHeckeChar.eventually_avatar_frob _).mp (eventually_mostFrobenii he.2 fun y a e ↦ e.trans
      (by simpa [heckeCoeff] using congr(ιℓ $((H ..).2 (v_uniformizer _) (a y.prime_q).2))))))))
  have h := (Subtype.ext (Units.ext (by simp [z]; simp [atSplit, ← map_inv, locGL, locIdele, ← diagonal_one, star_eq_conjTranspose])) : z (locIdele w x) = atSplit hw (.scalar n x)) ▸ h _
  exact ⟨(by simp [·, h · ·]), fun hx _ ⟨m, _, _, ht⟩ ↦ by simp [*, h _ (by erw [← ht, ← heckeSplit_dual hw 0 _ m hx (zero_add _).symm, heckeGL_zero (by rwa [← mem_sphericalAt_iff, sphericalAt, maxCompactAt, Gf.supportedOn_star])]), ← Complex.ofReal_pow, field, ← pow_mul']⟩
end
section
open Matrix Polynomial Filter Finset Metric Nat Gf NumberField Ideal Subgroup Module.End
attribute [local simp] s08_v8
private lemma ac_r6 {ℓ E a D} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [StablyUnram E] (ha : Odd a) [HasQuadSubfield D E] {u} (sp : ∀ v, ↑ℓ ∈ v.1 ∨ v = u → IsSplitPrimeToDisc (v.below (QuadField D))) : SphericalCompat E (Fin a) a u := fun P κ f hf he ↦ by
  have ⟨z, l, _⟩ : ∃ z, ↑ℓ ∈ z.1 ∧ (↑ℓ ∈ u.1 → u = z) := by grind [FinPlace.exists_natCast_mem E ℓ]
  have A a := ((sp z (.inl l)).exists_place_above_ne a u).imp fun x h ↦ (exists_comap_intQpBar_eq
    (p := ℓ) (x.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.2
    (by simpa [l] using congr(↑ℓ ∈ $(h.1).1)))).imp fun e H ↦ (H ▸ isPlaceOver_placeOfEmb e).unique
    x.isPlaceOver_placeOver |> fun k ↦ (fun {θ} (o : p5 x θ) ↦ (⟨h, k, o, by
    grind [star_star, p5]⟩ : ∃ _ _ _, IsSplitPrimeToDisc (x.below (QuadField D)) ∧ ¬p5 u θ)) (p6 _ (.comp ιℓ.symm
    (e.comp (algebraMap ..))) (by aesop))
  obtain ⟨_, v, _, B, -, o', l, n'⟩ := NeZero.of_pos ha.pos, A u
  obtain ⟨⟨x, θ, C, hθ, o, n₂, n⟩, ⟨ϑ, ty, c⟩, g, i, F⟩ := A v, exists_isCuspidalType v a, by simpa [funext_iff] using he.1
  let V := s08_v8 n₂.star_ne ⟨_, hf.1⟩
  have ⟨S, h, h₂⟩ := exists_inf_trivialOn_le V.2
  let K := .comap _ (continuous_atPlace v) ⟨localCongruence _ v 0, isOpen_localCongruence⟩ ⊓ s08_v8 l.star_ne V ⊓ ⟨_, isOpen_Kf⟩
  let χ : K.1 →* _ := ϑ.comp (.mk' (⟨_, ·.2.1.1⟩) (by simp [Subtype.ext_iff]))
  obtain ⟨⟨s, t, N, H, y, m⟩, O, L, _, _⟩ := s08_m3 (S := {F | ∃ r Q μ M g w q k J, _}) (fun h ↦ F (by simpa [s08_k9, ← map_mul, ← Pi.zero_def] using congr((weylRep _ κ.2 (k8 g) *ᵥ ($h ⟨g, ·⟩)) i))) (g3 _ ⟨by aesop, K.2⟩ (.mono (isOpen_localCongruence.preimage_of_continuous.mem_nhds (by simp))
    fun _ ↦ c _) {v | ¬_} ⟨_, hf⟩ (fun d h ↦ by simpa [V, χ, o.p8, o'.p8, *] using d.2.1.2) fun μ _ g j q M N ↦ Submodule.mapsTo_span (f := (s08_k9 ..).domRestrict _)
    (fun g i ↦ forall_eq'.1 fun F w ↦ i.2.rec fun P e ↦ (ac_t4 ha g.2
    e (S.mem_insert_self v) l ty (fun j ↦ congr($(i.1 ⟨_, by simpa [K] using! j.2.1⟩).1).trans (by
    simp [χ])) ((h x (inf_le_of_right_le (by simp [V, LE.le, ← range_atSplit n₂.star_ne]))).rec (by
    clear * - B C; grind)) hθ (fun d h _ a _ b e ↦ q _ n d h a b (by simp [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, mul_sub, mul_add, ← sum_mul, ← cast_sum] at *; grind only))
    (List.mem_map_of_mem <| mem_range.2 ·.2) u (by simp +contextual [*])).rec (⟨·, P, μ, M, g, w, e, N, j, ·⟩)) (have := (stdSpace ..).finite_formTranslation_levelSpace μ K.2 χ; (fun _ o ⟨k, a, b⟩ ↦ by simp at b; simp [χ, *, o ⟨k, by simpa [b] using h₂ ⟨a, mem_trivialOn.2 b.2⟩, a⟩]) |> fun J ↦ le_span_isSphericalOff (levelSpace _ _ χ) J (fun _ _ a b _ _ h ↦ heckeSplit_mem_levelSpace _ _ (levelSpace_le_sphericalAt a b (J h)) inf_le_right h) g)), eventually_mostFrobenii (.and (eventually_notMem_star_notMem ℓ (insert v S)) he.2) fun y ↦ And.imp_right (· y.prime_q), p4 hf
  choose r Q μ M g w q k J hr hU hw using (y · |>.2)
  choose b hb c T using p9 κ
  choose! d m using fun x h X j o o' (l : _ → x = u) e ↦ CanLift.prf (β := N) _ (m (_, _)
    ((T x h j).imp fun _ ↦ .imp_right fun T ↦ ⟨T 1 X e (by simp [← map_mul]), fun i ↦ w i ▸ T _ _
    ((q i).2.2 _ _ o o') fun _ ↦ k i _ fun _ h ↦ p7 _ _ _ (l · ▸ h)⟩))
  exact (s08_m8 H (mostFrobeniiAt E · |>.map fun y ↦ d y.w (P y.w) (a - 1))
    L.toSubmodule.complete_of_finiteDimensional (fun _ ↦ mem_inf_of_left (O.mono fun _ ⟨_, _, e⟩ ↦ by simp [*]; have ⟨c, _, _, t⟩ := e; simp (maxDischargeDepth := 3) [*, eq_div_of_mul_eq F congr($(t _) _ _).symm, mul_mem, heckeSplit, heckeGL_eq_sum ((mem_sphericalAt_iff _).1 c), div_mem, _root_.sum_mem, -Int.cast_mul])) hr fun g i ↦ tendsto_map' ((tendsto_mostFrobeniiAt (r
    i · |>.1.trace)).congr' (mem_inf_of_left ((hU i).mp (O.mono (by simp +contextual [*, trace_eq_neg_charpoly_coeff])))))).rec fun R ⟨hR, hN, hT⟩ ↦ ⟨hR, hN, .id, fun η k ↦ ((Iic a).eventually_all.2 fun i _ ↦ tendstoUniformly_iff.1 ((H.m4 (.C ((-1) ^ (a - i) / (a - i)!) * s08_m5 (a - i) 1) (⟨_, hT <| FrobeniusDatum.frob · ^ ·⟩)).add (H.2.comp fun z ↦ d z.w (P z.w) i)) η k).exists.rec fun ε h ↦ .mono (.and (.all (hU ⟨ε,
    ·⟩)) O) fun z ⟨p, o, n, e⟩ ↦ forall_eq.2 fun i ↦ (le_or_gt i a).rec (fun l ↦ by
    simpa [l, o, c, m, n, e, ← by simpa using (ext_iff.1 <| p ·), sub_eq_add_neg, fs_m6, t6, charpoly_monic, coeff_eq_esymm_roots_of_splits, IsAlgClosed.splits, ← mul_assoc] using (h i (by simpa) z).le) (fun _ ↦ by
    simp [*, k.le, coeff_eq_zero_of_natDegree_lt, (e.isMonicOfDegree he.1).1])⟩ |> fun e ↦ ⟨⟨R, e⟩, fun _ c k A hA ↦ And.elim (fun e M ↦ by
    choose g j p using (hw ⟨·, ·⟩ M hA)
    replace j η i := (j η i).congr (J' := jumps κ a) hA fun _ _ ↦ by simp [*, jumps, p6]
    exact (local_clauses_of_trace_limit c.1 c.2.1 _ _ _ _ (⟨r ⟨·, ·⟩⟩) (hr ⟨·, ·⟩) g j (.inr j) (by
    simpa [e] using! H.2.comp (⟨_, hT ·⟩)) fun _ _ _ _ h ↦ cast_inj.1 ∘ tendsto_nhds_unique
    (by simpa [← h, sum_mul] using (H.2.tendsto_at 1).mul_const _)).imp_right (.imp_right fun Y k Q hQ s hs ↦ Y .refl (⟨by simp [(hQ.isMonicOfDegree he.1).1, (((q _).2.2 _ k M.1 M.2).isMonicOfDegree (q _).1).1], p · · s hs⟩) fun j ↦ by simpa [mul_assoc, *] using (H.m4 ((b u k j)⁻¹ • .X 0 * .X 1) (![d u Q j, ⟨_, hT ·⟩])))) ⟨c.trace_eq e, (h u fun g b ↦ by simpa [V, mem_supportedOn.1 b.2 x, C, funext_iff] using k ⟨g, b⟩).elim (by clear * - B; aesop)⟩⟩
lemma r7 {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E] [CMType E] [StablyUnram E] {a} (ha : Odd a) w : SphericalCompat E (Fin a) a w := fun P κ f hf he ↦ by
 choose S _ hS using exists_inf_trivialOn_le hf.1
 let n T := ℓ * (T + w.q + S.sup FinPlace.q).factorial
 choose χ _ _ hμ G H L using fun {T} ↦ ac_r3 E (n T) NeZero.out
 have hp {T} {v : FinPlace E} (h := by omega) : ↑(n T) ∈ v.1 := mem_of_dvd _ ((Nat.dvd_factorial v.one_lt_q.le h).mul_left ℓ).natCast (absNorm_mem _)
 choose F _ Z hs _ using fun {T} ↦ exists_isWeakBaseChange_of_matching (hμ := @hμ T) ⟨_, hf⟩ isLocalMatching_empty ![] 0 _ rfl (by
  simp) nofun fun _ a _ ↦ trace_restrict_ne_zero one_ne_zero (he.1 congr($(·.le ⟨by simp, a⟩)))
  fun _ _ ↦ eigenspace_le_maxGenEigenspace (by simp [heckeFun, @Fintype.card_unique _ (.mk' _)])
 choose _ e hu _ hr using fun {T x A} a m ↦ (IsPlaceOver.exists_above a).imp fun u e ↦ And.intro e.2 ((ac_r6 ha
  (H · <| ·.elim (mem_of_dvd _ (by simp [n])) (by simpa [·, ← e.2] using m)) (@F T).2 Z).symm.imp_left fun H {r} c ↦ (@H r c · A e.1) ∘ (hs.2 x nofun u e.2).1 fun v e ↦ ⟨hμ.exists_gal_ne_one.imp (notMem_inertia_of_comap_ne ∘ (a.split_completely (L a m).1 v e).2 ·), fun y c ↦ by simp [localNorm, ideleAt, ((e ▸ a).artinAt_units_trivial_iff_unramified _).2 fun _ h ↦ ((L a m).2.1 h).2, v_adeleNorm_eq_one, locIdele_mem_idelesUnitOff c]⟩)
 choose ho hR ρ hρ hs' using (@hs · |>.r4 (hr w.isPlaceOver_placeOver hp) Z he)
 obtain ⟨⟨m, G⟩, ⟨C, d, o, -⟩, z⟩ := @G 0, hρ 0, (mt <| @hp 0 · ∘ _root_.le_add_left ∘ S.le_sup)
 let K := (⨅ T, (ρ (T + m)).ker.map (Subgroup.subtype _)).normalCore
 choose Q c using fun T ↦ (d.comp (inclusion inf_le_left)).exists_conj_of_trace_eq _ (.id ..)
  ((hρ (T + m)).2.1.comp (inclusion inf_le_right)).hasSemiprimeSpan fun _ ↦ (hρ 0).trace_eq (hρ _) _ rfl
 have k {T} g h (a : h ∈ K) p : ρ 0 ⟨g.1 * h, p⟩ = Q T * ρ (T + m) g * (Q T)⁻¹ := by
  obtain ⟨y, e, rfl⟩ := Subgroup.mem_iInf.1 (normalCore_le _ a) T
  rw [← mul_one (ρ _ g), ← e, ← map_mul]
  exact eq_mul_inv_of_mul_eq (Units.ext (c _ ⟨_, p, (_ * y).2⟩))
 choose y Y s using G K fun s ⟨x, ⟨p, _⟩, A, a, i⟩ c ↦ Subgroup.mem_iInf.2 fun T ↦ ⟨⟨_, (L (a.smul c) hp).2.1 (i.conj c)⟩, hs' .. ▸ (hu (a.smul c) hp (hr ..) (levelSpace_le_sphericalAt
  (z _ p) (z _ (by simpa)) (by simpa [LE.le, funext_iff] using hS))).1.1
  ((a.smul c).valuation_natCast_eq_one_iff.2 (p ∘ mem_of_dvd _ (by simp [n]))) _ (i.conj c), rfl⟩
 have u {x z} (p : (z.1 : _ ⧸ K) = x.1 := by simp [Y]) : ρ 0 x = ρ 0 z := (ρ 0).eq_iff.2 ((@k 0 1 _ (QuotientGroup.eq.1 p) _).trans (by simp))
 exact ⟨⟨.mk' (ρ 0 ⟨_, s ·⟩) fun _ _ ↦ .trans u (map_mul ..), continuous_of_continuousAt_one _
  fun _ h ↦ o.nhds_le 1 ((C.congr fun _ ↦ u).tendsto 1 h), fun x m t ↦ d x (Submodule.span_mono
  (by simp) m) (t · ▸ congr((x * $u).trace)), .id, fun η e V O n ↦ (chebotarev O n he.2).elim fun y ⟨_, p, _, a, _, v, f, _⟩ ↦ ((hρ (y.q + m)).2.2.2 η e _ (O.inter (ho (y.q + m))) ⟨_, v, (L a hp).2.2 (isSplit_of_q_prime p) f.1⟩).imp fun O ⟨a, b⟩ ↦ ⟨fun _ h ↦ (a h).1, by peel b; simpa [k ⟨_, (a ‹_›).2⟩, Y] using this _ rfl⟩⟩, fun _ R f A a ↦ match hR 0 R A, L a hp with | ⟨i, j, y⟩, ⟨U, g, D⟩ => (hu a hp (hr ..) f).imp (isGoodAt_iff.2 <| isGoodAt_iff.1 · |>.imp i fun x s h ↦ (y ⟨s, g h⟩).2 _ (x _ h)) (.imp (j _) fun x hw P d s h ↦ (y ⟨s, inv_mem (D hw h.1)⟩).2 _ (x _ P ((hs.2 w nofun _ (e ..)).2 ⟨by simp [(a.artinAt_trivial_iff_decompGroup_le _).2 fun _ h ↦ (D hw h).2], a.split_completely U⟩ _ _ d).2 _ ((a.split_completely U _ (e ..)).1 ▸ h)))⟩
lemma avatarCompatAt_of_stablyUnram {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E] {w : FinPlace E} [NumberField.IsCMField E] [StablyUnram E] θ : AvatarCompatAt w θ := fun A hA ↦ by
  wlog hw : w.IsSplit generalizing E
  · choose χ _ _ _ _ S H using ac_r3 E _ w.one_lt_q.ne_bot
    let j : Gal(Ω/QZChar.w1 χ) →* _ := AlgEquiv.restrictScalarsHom E
    obtain ⟨a, c, u, hu, rfl⟩ := (H hA w.1.absNorm_mem).1, isOpenEmbedding_galois_restrict j (by tauto), hA.exists_above (L := QZChar.w1 χ)
    have k := (hA.split_completely a u rfl).1
    refine have T := local_clauses_of_retract 1 _ (by simp) (by tauto) c Filter.univ_mem ?_ (one_mul 1)
      (this θ.baseChange hu (S u (k ▸ u.1.absNorm_mem)).star_ne).imp T.1 (.imp (T.2.1 (by simp))
        fun c s m l t ↦ (c (.ofRingEquiv (·.2 ⟨_, a (inv_mem t.1)⟩)) m l (by rwa [k])).elim fun y
        ⟨o, e, p⟩ ↦ ⟨_, by simp [v_localNorm (f := 1), *], (hu.localArtin_adeleNorm j).1 e, by simpa [← adeleNorm_locIdele] using! T.2.2 _ ⟨⟩ p⟩)
    simp; refine (dense_of_mostFrobenii (eventually_mostFrobenii
      (eventually_notMem_star_notMem ℓ {u}) fun y l ↦ (y.isPlaceOver.exists_localArtin_eq
      y.isFrob 1).elim fun z e ↦ ?_)).induction (fun _ ↦ id) (by apply isClosed_eq <;> fun_prop)
    erw [AlgHeckeChar.avatar_localArtin _ y.isPlaceOver (.inl l.2.2) e.2, θ.1.1.comp_apply, adeleNorm_locIdele, θ.avatar_localArtin y.isPlaceOver.isPlaceOver_below _
      ((y.isPlaceOver.localArtin_adeleNorm j).1 e.2)]; simp [l]
  have : CMType E := {}
  let ⟨v, o⟩ := (((Northcott.finite_le (h := FinPlace.q) (2 ^ Module.finrank ℚ E)).insert w).insert
    (star w)).exists_notMem
  let k s := ite (inducedPrime s = w) (θ.1.2.toAdd s) (-θ.1.2.toAdd (star s))
  have e : levelSpace ((stdSpace E (Fin 1)).formTranslation (0, k ∘ Φ)) _ ≃ₗ[ℂ] _ := freeLevelEquiv _ _ _ (classAut_eq_bot (w := ![v]) (by simp [·.ext_iff]) (by aesop) le_rfl)
  obtain ⟨f, ⟨-, P, hP⟩, -⟩ := have := e.symm.finiteDimensional; not_forall₂.1
    (Submodule.nontrivial_iff_ne_bot.1 e.nontrivial <| eq_bot_mono (levelSpace_anti
      (.trans (by simp) inf_trivialOn_le_levelOf) |> (le_span_isSphericalOff (S := {v}) _ · (by
    intros; apply_rules [heckeSplit_mem_levelSpace, levelSpace_le_sphericalAt, levelOf_le_Kf]))) <| Submodule.span_eq_bot.2 ·)
  have he : IsEigenform _ P := ⟨hP.1, (eventually_notMem_star_notMem 1 {v}).mono (by grind [IsSphericalOff, isSplit_of_q_prime])⟩
  obtain ⟨hP, ⟨r, hr⟩, hS⟩ := hP.2.2 w hw (by aesop) (by aesop), r7 odd_one w f.2 he
  obtain ⟨⟨t, e⟩, ⟨a₁, b₁, c₁⟩, θ₁, h₁, H, D⟩ := by simpa [Polynomial.isMonicOfDegree_one_iff] using (hP.isMonicOfDegree he.1), (hS hr hP.1 A hA).imp_left isGoodAt_iff.1, hr.r5 f.2 he
  refine (local_clauses_twist A (by simp [← Matrix.ext_iff, by simpa using D])).elim fun T U ↦ (avatarCompatAt_of_type_eq_zero (θ / θ₁) (fun σ h ↦ ?_) hA).imp (T a₁.1) (.imp (by
    convert U.2.1 b₁ ·; simp [jumps, Multiset.range, *]; lia) fun c ↦ ?_)
  simp [h₁]; grind [Φ_eq_or σ, congr(inducedPrime $(NumberField.IsCMField.isConj_complexConj E
    _)).trans (placeOfEmb_comp_star (ιℓ.toRingHom.comp _))]
  peel c with s m hm hs x v _ k
  refine U.2.2 (.of_dvd ?_ (Polynomial.dvd_iff_isRoot (a := ιℓ (θ₁.1.1 (locIdele w x))).2 (by simp))) k
  interval_cases m
  simpa [(H w hw x).1 v (hP.1 ⟨_, by simp [mem_intGL, mem_LocInt, v]⟩)] using a₁.2 _ (inv_mem hs)
  simpa [(H ..).2 v hP, e] using c₁ _ _ hP _ (pow_one w.q ▸ hs)
end
