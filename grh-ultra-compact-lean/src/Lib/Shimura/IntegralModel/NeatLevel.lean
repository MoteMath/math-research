import Lib.Shimura.Uniformisation.Frames
import Lib.Weil.Unramified.SphericalHecke
import Lib.General.NumberTheory.QuadFieldSplitting
import Lib.Adelic.Adeles.OneSidedPoisson
import Lib.Adelic.Adeles.NormAbsValue
import Lib.Adelic.Reduction.MahlerForms
noncomputable section
open MonoidAlgebra Submodule QuotientGroup Representation
variable {G} (k) [Group G] [CommRing k] (K : Subgroup G)
def spanOn D := span k (of k G '' D)
variable {k} {a b W} [AddCommGroup W] [Module k W]
lemma asAlgebraHom_eq_sum_support (π : Representation k G W) : π.asAlgebraHom a = ∑ g ∈ a.coeff.support, a.coeff g • π g := rfl
@[local simp] def cosetFn a := ((ofMulAction k G (G ⧸ K)).asAlgebraHom a (.single ⟦1⟧ 1)).coeff
def fixedToEigen {H} [Group H] (ι : H →* G) (J := K.comap ι) (χ : J →* k := 1) : Submodule k
  k[G] := by use! {a | ∀ ⦃W⦄ [AddCommGroup.{0} W] [Module k W] ⦃π⦄ ⦃v : W⦄, v ∈ levelSpace π K →
  π.asAlgebraHom a v ∈ levelSpace (π.comp ι) J χ} <;> simp_all [smul_smul, mul_comm]
variable {K} {D D' D'' : Set G} (h : a ∈ spanOn k D)
def Model.cosetSum (ψ : _ → W) a := (cosetFn K a).linearCombination k ψ
lemma single_one_mem_levelSpace : .single (mk 1) 1 ∈ levelSpace (ofMulAction k G (G ⧸ K)) K := (by simp [← mk_mul_of_mem 1 ·.2])
include h
lemma spanOn.exists_mem_of_cosetFn_ne_zero {q} : _root_.cosetFn K a q ≠ 0 → ∃ d ∈ D, d = q := Function.mtr (by induction h using span_induction <;> aesop)
lemma spanOn.mul (h' : b ∈ spanOn k D') (H : ∀ g ∈ D, ∀ g' ∈ D', g * g' ∈ D'') : a * b ∈ spanOn k
  D'' := span_mono (by rintro _ ⟨⟩; grind) ((span_mul_span ..).le (mul_mem_mul h h'))
end
section
open Function LinearMap Finset
attribute [local simp] cosetFn asAlgebraHom_eq_sum_support sum_mul Finsupp.single_apply
lemma trace_eq_weighted_sum {A G Γ W M I} [Group G] [Group Γ] {e : Γ →* G} {K} [Field A]
  [AddCommGroup W] [Module A W] [Module.Finite A W] [AddCommGroup M] [Module A M] [Fintype I] {ρ : Representation A Γ W} {s T D a} (r : I → G) (w : I → A) (ι : M →ₗ[A] G → W) (hM : ι.range = ρ.coindV e ⊓ .pi D ⊥ ⊓ levelSpace (rightRegular ..) K) (σ : G ≃* G) (S : I → G → _) (hS : ∀ i g γ, γ ∈ S i g ↔ g⁻¹ * (e γ * r i) ∈ K) (hw : ∀ g, if g ∉ D then ∑ i, w i * #(S i g) = 1 else ∀ i, S i g = ∅) (hT : ∀ ψ, ι (T ψ) = (rightRegular ..).asAlgebraHom a (s <| ι ψ <| σ.symm ·)) (hσ : K.comap ↑σ = K) (hι : Injective ι := by simp) : Module.Finite A M ∧ trace A M T = ∑ i, w i * ∑ᶠ γ,
  cosetFn K a ((r i)⁻¹ * σ (e γ) * σ (r i)) * (s * ρ γ).trace A W := by
  let J i := codRestrictOfInjective (pi (S i · |>.sum ρ)) ι hι fun v ↦ by
    simp [hM, funext_iff]; use ⟨fun γ g ↦ sum_equiv (.mulLeft γ⁻¹) ?_ ?_, by grind⟩, fun _ _ _ ↦ sum_equiv 1 ?_ ?_ <;> simp_all [mul_assoc, mul_mem_cancel_left]
  have hJ : ∑ i, w i • J i ∘ₗ proj (r i) ∘ₗ ι = 1 := ext fun ψ ↦ hι (by
    ext g; have ⟨c, d⟩ := hM.le ⟨ψ, rfl⟩; simp at c
    simp +contextual [J, smul_comm (w _), ← smul_assoc, ← sum_smul, ← c.1, ← hS, fun x h ↦ by simpa using congrFun (d ⟨g⁻¹ * x, h⟩) g]
    grind [one_smul, smul_zero])
  have := Module.Finite.of_surjective (lsum A _ A J) (⟨(w · • _), by simpa using congr($hJ ·)⟩)
  rw [← mul_one T, ← hJ]; simp [mul_sum, this]; congr!
  erw [← trace_comp_cycle, show _ ∘ₗ _ = ∑ g ∈ _, a.coeff g • s * (S ..).sum ρ by aesop]
  simp [mul_sum, sum_sigma']; rw [← finsum_sum_filter (·.2)]
  simp [sum_filter, sum_sigma, mul_assoc, ← QuotientGroup.eq, ↓K.mem_comap, hσ ▸ hS]
end
noncomputable section
open NumberField Cardinal Polynomial Classical Module Matrix.GeneralLinearGroup Prod MulAction
section
variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n] {d : ℕ} {d₀ : ℕ} [Fact (d % 4 = 3)]
def IsSplitPrimeToDisc (u : FinPlace (QuadField d)) := ∃ b : ℤ, let x := QuadField.c₀ d - b; x ∈ u.1 ∧ IsCoprime x (star x)
lemma IsSplitPrimeToDisc.star_ne_and_prime_norm {w : FinPlace (QuadField d)} : IsSplitPrimeToDisc w → w.IsSplit ∧ w.q.Prime ∧ ∀ u, u = w ∨ u = star w ↔ ↑w.q ∈ u.1 := by grind [IsSplitPrimeToDisc, =_ mem_star_place, star_natCast, (@QuadField.prime_inert_or_eq_mul _ · _ ⟨·⟩ w), → w.2.notMem_of_isCoprime_of_mem, w.1.exists_prime_and_absNorm_eq_pow]
class HasQuadSubfield (d : outParam ℕ) (E : semiOutParam Type) [semiOutParam (Field E)] extends Fact (d % 4 = 3), Algebra (QuadField d) E
abbrev SplitFinPlace (E : Type) [Field.{0} E] [NumberField E] [IsCMField E] := {w : FinPlace E // w.IsSplit}
variable (K : Subgroup (GL n (𝔸f E))) (y : GL n E) (k : Type _) [CommRing k] (v : SplitFinPlace E) (𝔑 : 𝓞 E)
def MarkedTriple (Z := ℂ) := (_ ⧸ K) × GL n E × Z
instance {Z} : MulAction (GL n E) (MarkedTriple K Z) := @mulAction _ _ _ _ (.compHom _ toFinGL) (@mulAction _ _ _ _ (.compHom _ MulAut.conj) (ofEndHom 1))
abbrev γ x := x⁻¹ * toFinGL y⁻¹ * x
def conjAtSplit := (@invTransposeGL n _).toMonoidHom.comp (.comp (N := Gf ..) (U 1).subtype (atSplit v.2))
def dualComponent := (@invTransposeGL n _).symm.toMonoidHom.comp (map (evalAt v.1))
def IsCuspidalType {F} [Field F] (J : Subgroup (GL n F)) (χ : J →* ℂ) := ∀ ε, IsIdempotentElem ε → ε ≠ 0 → ε ≠ 1 → ∃ j Y, 1 + ε * Y * (1 - ε) = j.1.1 ∧ χ j ≠ 1
variable [HasQuadSubfield d₀ E]
abbrev unifNorm := (locIdele _ (uniformizer v)).map (adeleNorm (QuadField d₀) E)
abbrev centralScalar := (scalar n).comp (Units.map ((starRingEnd _).comp (finAdeleIncl (QuadField d₀) E)).1)
def IsSafe (w : FinPlace E) := IsSplitPrimeToDisc (w.below (QuadField d₀)) ∧ 𝔑 ∉ w.1 ∧ ∀ v, .below _ v = star (w.below (QuadField d₀)) → 𝔑 ∉ v.1
abbrev SafePlace := {w : SplitFinPlace E // IsSafe 𝔑 w}
def heckeIsogeny U := centralScalar (n := n) (unifNorm v ^ finrank (ResField v.1) (SubmoduleElem U))⁻¹ * conjAtSplit v (transposeGL (basicCosetRep U))
variable (n)
def levelGU := GU E n ⊓ congruenceGL (Ô E ∙ algebraMap _ _ 𝔑) id
def heckeSum j := ∑ U with finrank (ResField v.1) (SubmoduleElem U) = j, MonoidAlgebra.of k (GL n _) (heckeIsogeny v U)
def heckeAlgebra := (spanOn k (GUPlus E n) ⊓ fixedToEigen (levelGU n 𝔑) (.id _) (levelGU n 𝔑)).toSubalgebra ⟨Submodule.subset_span ⟨1, by simp, rfl⟩, by simp [fixedToEigen]⟩ (by simp_all [fixedToEigen, -mem_levelSpace, spanOn.mul _ _ fun _ h _ ↦ mul_mem h])
variable {n 𝔑} (f : heckeAlgebra n ℂ 𝔑)
abbrev heckeCosetFn := cosetFn (levelGU n 𝔑) f.1
def IsRegularHecke := ∀ ⦃y : GL n E⦄ ⦃x⦄, heckeCosetFn f (γ y x) ≠ 0 → y.1.charpoly.Separable
end
variable {E : Type} [Field.{0} E] [CMBase E] {n : Type} [Fintype.{0} n] (t : E →+* ℂ) (ε : Prop) (y : GL n E) {ν : ℕ} (α : Fin ν → 𝓞 E) (P : E[X]) (μ : ℂ) {𝔑 : 𝓞 E} (f : heckeAlgebra n ℂ 𝔑) (ω : _ → n → ℂ)
def numberedRoots : n ↪ ℂ := @epsilon _ (mk_le_aleph0.trans (aleph0_le_mk ℂ)) fun r ↦ (P.map t).roots = Finset.univ.1.map r
def eigenReflection (i : n) := aeval (y.1.map (Φ v₀)) (ite ε (Lagrange.interpolate .univ (numberedRoots (Φ v₀) y.1.charpoly) (if · = i then 1 else -1)) 1)
def countTerm (c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n)) := let (q, y, μ) := c.out
  ite (IsSignedFrame q.out (eigenReflection ε y μ)) (heckeCosetFn f (γ y q.out) * ω y.1.charpoly μ) 0
def IsLieRoot (r : ℂ) := if .mk t = v₀ then if t = Φ v₀ then r = μ else r ≠ star μ else t = Φ (.mk t)
def lieRoots σ := (P.map σ).roots.map fun r ↦ (if IsLieRoot σ μ r then X else 1) * C r
def localTerm (j : n) := let r := numberedRoots (Φ v₀) P; (Lagrange.basis .univ r j).comp (X * C (r j)) * ∏ i, ∏ σ, ((lieRoots P (r j) σ).map (1 - C (σ (α i)) * ·)).prod
open Fintype Matrix Multiset Ideal ComplexOrder AddMonoidHom Rat RingHom Algebra
attribute [local simp] map_smul' IsIntegrallyClosed.isIntegral_iff mul_smul trace_mul_cycle
section
variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n] {x : GL n (𝔸f E)} {ℓ : Matrix n n ℂ} {y : GL n E} {β : Matrix n n E} {x' : GL n (𝔸f E)} {ℓ' : Matrix n n ℂ} {β' : Matrix n n E} {𝔑 : 𝓞 E}
instance [h : StablyUnram E] : Nontrivial (InfinitePlace E) := h.1.rec fun _ h ↦ by grind [finrank_eq_two_mul_card_infinitePlace, one_lt_card_iff_nontrivial, (totient_mul_totient_le_finrank _ 1 rfl .one h).trans' (by decide +kernel : 3 ≤ _)]
lemma mem_GU (a : (𝔸f ℚ)ˣ) (h : xᴴ * x.1 = finAdeleIncl ℚ E a • 1) : x ∈ GU E n ∧ ∀ c : ℚ, c = finIdeleAbs a → IsScalarFrame x c := by
  obtain ⟨s, u, hu, rfl⟩ := by simpa [Subgroup.mem_sup, classNumber_eq] using
    pow_classNumber_mem_principal_sup a
  let ν : (Ô ℚ)ˣ := (Ô ℚ).unitsEquivUnitsType ⟨u, coe_idelesUnitOff_empty.le (by simpa)⟩
  simp [↓map_mul, ↓finIdeleAbs_principalIdele, finIdeleAbs, ideleAbs_eq_prod_of_v_eq_one, hu, -cast_inv]
  erw [and_iff_right_of_imp (⟨_, by simp, ·⟩)]
  cases abs_choice s.1 <;> [use ν; use -ν] <;> simp [*, ν, ↓map_smul']
lemma mem_GUPlus_of_mem_levelGU : x ∈ levelGU n 𝔑 → x ∈ GUPlus E n := .imp_right (·.1.isIntMatrix_inv)
lemma IsFrameFor.isHermitian_map {f : E →+* ℂ} : IsFrameFor β x → (β.map f).IsHermitian
  | ⟨_, h⟩ => .map ((isHermitian_map_iff (star_algebraMap_finAdele · |>.symm) (RingHom.injective _)).1 (by simp [IsHermitian, ← gram_inv_of_gram_eq h, star_eq_adeleMap]; congr; aesop)) _
    (map_star_complex f)
end
variable {E : Type} [Field.{0} E] [Ψ : CMBase E] {n : Type} [Fintype.{0} n] {x : GL n (𝔸f E)} {ℓ : Matrix n n ℂ} {y : GL n E} {β : Matrix n n E} {x' : GL n (𝔸f E)} {ℓ' : Matrix n n ℂ} {β' : Matrix n n E} {𝔑 : 𝓞 E} [Nonempty n] {c : ℚ} {ι : Type _} [Fintype ι] {w : ι → FinPlace E}
omit [Nonempty n] in
lemma isSignedFrameFor_one (g : Gf E n) : IsSignedFrameFor g.1 1 1 := ⟨⟨1, by simpa [U] using g.2⟩, by simpa using .one⟩
lemma IsFrameFor.exists_intCast_eq (h : x ∈ GUPlus E n) : IsFrameFor ((c : E) • 1) x → ∃ z : ℤ, z = c | ⟨_, e⟩ => by simpa [isIntegral_ratCast_iff] using fun i ↦ congr($(gram_inv_of_gram_eq e) i i ∈ Ô E).mp (sum_mem (by simp [mul_mem, h.2, -coe_units_inv, star_eq_adeleMap]))
lemma IsScalarFrame.eq_one_of_mem_levelGU (h : x ∈ levelGU n 𝔑) (e : IsScalarFrame x⁻¹ c) : c = 1 := by
  obtain ⟨w, rfl⟩ := e.2.exists_intCast_eq (mem_GUPlus_of_mem_levelGU (inv_mem h))
  simp_all [IsScalarFrame]; obtain ⟨left, right⟩ := e; grind
  [inv_intCast_den, Rat.den_intCast, (right.mul_iff.1 ⟨1, by simp [left.ne']⟩).exists_intCast_eq (c := w⁻¹) (mem_GUPlus_of_mem_levelGU h)]
lemma levelGU.isScalarFrame_inv_one (h : x ∈ levelGU n 𝔑) : IsScalarFrame x⁻¹ 1 := (inv_mem h).1.rec fun _ e ↦ e.eq_one_of_mem_levelGU h ▸ e
lemma IsFrameFor.unique w : IsFrameFor β x → IsFrameFor β' x → (β.map (Φ w)).PosDef → (β'.map (Φ w)).PosDef → β' = β
  | ⟨ε, h⟩, ⟨δ, h'⟩, P, P' => by
    obtain ⟨⟨u, rfl⟩, b⟩ := mul_right_surjective ε δ, integralBasis E
    obtain ⟨⟨k, a⟩, e⟩ := by simpa [← map_trace, b.ext_elem_iff] using P.trace_pos.ne', by
      simpa [by simpa using gram_inv_of_gram_eq h] using gram_inv_of_gram_eq h'
    have ⟨s, q⟩ : ∃ s : ℚ, u.1.1 = s := ⟨_ * _, by
      simpa [← adeleCombination_repr b, adeleBasis, algebraMap_eq_smul_one, ← map_trace, ← smul_toAlgebra, ← eq_inv_smul_iff₀ a] using congr((adeleBasis b).repr (trace $e) k)⟩
    cases (Matrix.map_injective (RingHom.injective _) (.trans (by aesop) e) : (s : E) • β = β')
    simp [IsScalarFrame.eq_one_of_mem_levelGU (levelGU n (0 : 𝓞 E)).one_mem ⟨by simpa [← Complex.ofReal_ratCast, P.trace_pos] using P'.trace_pos, u, by aesop⟩]
lemma IsSignedFrameFor.conj_eq_smul (h : IsSignedFrameFor x ℓ β) (h' : IsSignedFrameFor x' ℓ' β') (H : IsScalarFrame (x'⁻¹ * toFinGL y * x)⁻¹ c) : yᴴ * β' * y.1 = (c : E) • β := (exists_ne Ψ.v₀).rec fun w _ ↦ by
  apply (h.1.mul_iff.2 H.2).unique w (by simp [IsFrameFor.conj_iff, *]) <;>
    simp [↓map_conjTranspose_mul_mul, ↓map_smul', cast_smul_eq_qsmul]
  exacts [.smul (by grind) H.1, (y.map _).isUnit.posDef_star_left_conjugate_iff.2 (by grind)]
lemma IsSignedFrameFor.similitude_and_root_norm (h : IsSignedFrameFor x ℓ β) (H : IsScalarFrame (x⁻¹ * toFinGL y * x)⁻¹ c) (l : ratConj y ℓ = ℓ) : yᴴ * β * y.1 = (c : E) • β ∧ ∀ᵉ
  (w) (r ∈ (y.1.charpoly.map (Φ w)).roots), r * star r = c := ⟨h.conj_eq_smul h H, fun w r q ↦ by
  have P := h.2 w; set J := ite (w = v₀) ..
  obtain ⟨l, -, u, a, hu⟩ := by simpa using
    (Units.mul_inv_eq_iff_eq_mul _).1 (by aesop : ConjAct.toConjAct (y.map (Φ w)) • J = J), by
    simpa [← charpoly_map, eval_charpoly, ← exists_mulVec_eq_zero_iff] using q
  simpa [↓map_conjTranspose_mul_mul, ← vecMul_vecMul, ← star_mulVec, ← dotProduct_mulVec, ← J.mulVec_mulVec, ← hu, l, field, (P.dotProduct_mulVec_pos a).ne'] using
    congr(star u ᵥ* $(h.conj_eq_smul h H).map (Φ w) ⬝ᵥ J *ᵥ u)⟩
lemma IsSignedFrameFor.eq_one_of_congr_large_norm (h : IsSignedFrameFor x ℓ β) {I} J (f : IsScalarFrame (x⁻¹ * toFinGL y * x)⁻¹ 1) (k : x⁻¹ * toFinGL y * x ∈ congruenceGL (.map (Algebra.linearMap (Ô E) _) J) id) (hℓ : ratConj y ℓ = ℓ)
  (b : (2 * card n) ^ finrank ℚ E < absNorm I) (c : under (𝓞 E) J ≤ I) : y = 1 := by
  obtain ⟨⟨q, H⟩, ⟨w, P⟩, ⟨_, A⟩, a, ⟨⟩⟩ := h.similitude_and_root_norm f hℓ, (exists_ne v₀).imp fun w ↦ (by simpa [·] using h.2 w), (by simp [map_trace] : Matrix.trace _ = ↑(y.1 - 1).trace).subst (sum_mem fun i _ ↦ k.2 i i)
  have := by simpa using congr($(norm_eq_zero_iff.1 (Int.eq_zero_of_abs_lt_dvd
    (absNorm_dvd_norm_of_mem (@c ⟨_, algebraMap_mem_Ô.1 A⟩ a)) (by
    rify at *; grw [← b]; erw [← cast_intCast, coe_norm_int, abs_norm_eq_prod_norm_sq, finrank_eq_two_mul_card_infinitePlace, pow_mul, ← Finset.prod_const]; gcongr; simp [map_trace]
    grw [trace_eq_sum_roots_charpoly, charpoly_map, norm_sub_le, norm_multiset_sum_le, two_mul, sum_map_le_sum_map _ 1 (by simpa using congr(√‖$(H _ · ·)‖).le)]
    simp [IsAlgClosed.card_roots_eq_natDegree]))).val)
  use Units.ext (map_injective (Φ w).injective (by simpa [kronecker_mulVec_vec, star_vec_dotProduct_vec, sub_mul, ← mul_assoc, ← map_conjTranspose_mul_mul, -vec_sub, P.det_pos.ne', ← map_trace, *] using (P.inv.transpose.kronecker P).dotProduct_mulVec_pos (x := vec (y.map (Φ w) - 1))))
variable (n 𝔑) in
def IsNeat := 𝔑 ≠ 0 ∧ ∀ {x ℓ y}, IsSignedFrame x ℓ → x⁻¹ * toFinGL y * x ∈ levelGU n 𝔑 → ratConj y ℓ = ℓ → y = 1
lemma eventually_isNeat : ∀ᶠ w : FinPlace E in .cofinite, ∀ 𝔑 ≠ 0, 𝔑 ∈ w.1 → IsNeat n 𝔑 := .mono
  (Northcott.finite_le (h := FinPlace.q) _).compl_mem_cofinite fun w b _ h₀ a ↦
  ⟨h₀, fun ⟨_, h⟩ k l ↦ h.eq_one_of_congr_large_norm (span _) (levelGU.isScalarFrame_inv_one k) (by simpa [Submodule.map_span] using! k.2) l (by aesop) fun _ c ↦ mem_of_dvd _ ((dvd_iff_Ô h₀).1 (mem_span_singleton.1 c)) a⟩
omit [Nonempty n] Ψ
lemma classAut_eq_bot {E : Type} [Field.{0} E] [CMType E] {w : ι → FinPlace E}
    [Nontrivial (InfinitePlace E)] (hw : w.Injective) (b : (2 * card n) ^ finrank ℚ E < ∏ i, (w i).q) {K} (hK : K ≤ levelOf w ⊥) g :
  classAut (stdSpace E n).Γf K g = ⊥ := bot_unique (by
  rintro _ ⟨⟨γ, rfl⟩, k⟩; obtain ⟨⟨hk, h⟩, _ : CMBase E⟩ := mem_levelOf.1 (hK k), ⟨Classical.ofNonempty⟩
  simp [((isEmpty_or_nonempty n).rec (by subsingleton) fun _ ↦ Subtype.ext ((isSignedFrameFor_one g).eq_one_of_congr_large_norm (⨅ i, ker (reduceAt (w i))) (by simpa [← stdSpace_embFin]
    using mod_cast (isSignedFrameFor_one _).1) (stdSpace_embFin γ ▸ ⟨hk, (⟨_, mem_iInf.2 fun a ↦ intGL.map_eq_one.1 congr($h a) · ·, rfl⟩)⟩) _ (by rwa [map_prod]) _) :
    γ = 1), ratConj, IsConcreteLE.le_iff, mem_prod_finPlace_iff hw])
end
