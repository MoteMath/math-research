import Lib.General.LinearAlgebra.CommonEigenvectors
import Lib.Weil.Unramified.HeckeGL
noncomputable section
section
open Matrix NumberField Gf Set RingHom Polynomial
variable {n A W W' E : Type*} [Fintype n] [Field E] [NumberField E] [IsCMField E] [CommRing A] [AddCommGroup W] [Module A W] [AddCommGroup W'] [Module A W'] {w u : FinPlace E} (π : Representation A (Gf E n) W) {π' : Representation A (Gf E n) W'} {v : W} (hw : w.IsSplit) (hu : _ ≠ u) (i : ℕ) (j : ℕ)
variable (n w) in
abbrev maxCompactAt := Kf .. ⊓ supportedOn n {w}
def heckeSplit := heckeGL (π.comp (atSplit hw)) j
abbrev sphericalAt w := levelSpace π (maxCompactAt n w)
variable {π} {σ : A →+* A} {Z : Type _} [AddCommMonoid Z] [Module A Z] (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v' : W'} (hv : v ∈ sphericalAt π w)
lemma FinPlace.IsSplit.star : w.IsSplit → (Star.star w).IsSplit := star_injective.ne
lemma Gf.supportedOn_star : supportedOn n {star w} = supportedOn n {w} := by aesop
lemma levelSpace_le_sphericalAt {S : Finset _} : w ∉ S → star w ∉ S → levelSpace π (Kf .. ⊓ trivialOn n S) ≤ sphericalAt π w := by aesop_cat
lemma mem_sphericalAt_iff : v ∈ sphericalAt π w ↔ v ∈ levelSpace (π.comp (atSplit hw)) (Kw ..) := by simp [inf_comm (Kf ..), ← range_atSplit hw]
lemma map_heckeSplit (L : W →ₛₗ[σ] W') (hL : ∀ g ∈ supportedOn n {w}, L (π g v) = π' g (L v) := by tauto) : L (heckeSplit π hw j v) = heckeSplit (A := A) π' hw j (L v) := by simp [heckeSplit, heckeGL, heckeFun_sum, map_indicator, *]
@[local simp] lemma heckeSplit_comm_of_trivialOn {g} (hg : g ∈ trivialOn n {w}) : π g (heckeSplit π hw j v) = heckeSplit π hw j (π g v) := map_heckeSplit _ _ _ fun _ h ↦ congr($((commute_supportedOn_trivialOn h hg).map π) v).symm
include hv
lemma heckeSplit_star : heckeSplit π hw.star j v = heckeFun (π.comp (atSplit hw)) (Kw ..) ((basicDoubleCoset n w j).indicator 1 ·⁻¹) v := have R := (range_atSplit hw.star).trans (supportedOn_star.trans (range_atSplit hw).symm); heckeFun_comp ((atPlace w).comp (atSplit hw.star)) (by simp) ((mem_sphericalAt_iff _).1 hv) (by simp) (R.ge ⟨·, rfl⟩ |>.imp (by aesop)) (by simp [← atPlace_star_mem_iff]) (R.le ⟨·, rfl⟩ |>.rec fun _ ↦ (by simp [← ·])) (by simp [basicDoubleCoset, ← map_inv, indicator, atPlace_star (star_star _), -coe_units_inv, ← mapMatrix_apply, ← map_det]; aesop)
lemma heckeSplit_dual {ϖ} : Valued.v ϖ.1 = .exp (-1) → Fintype.card n = i + j → π (atSplit hw (.scalar n ϖ)) (heckeSplit π hw.star i v) = heckeSplit π hw j v := heckeSplit_star hw _ hv ▸ heckeGL_dual ((mem_sphericalAt_iff _).1 hv)
lemma heckeSplit_comm_of_atPlace_mem {g} (hg : g.atPlace w ∈ Kw ..) : heckeSplit π hw j (π g v) = π g (heckeSplit π hw j v) := by rw [← div_mul_cancel g (atSplit hw (g.atPlace w)), map_mul, mem_sphericalAt_iff hw] at *; have : heckeSplit π hw j v ∈ _ := (isBiInvariant_basicDoubleCoset j).heckeFun_mem hv; simp_all
lemma heckeSplit_adjoint (hv' : v' ∈ sphericalAt π' w) (hB : ∀ g x y, B (π g x) (π' g y) = B x y) : B (heckeSplit π hw j v) v' = B v (heckeSplit (A := A) π' hw.star j v') := by apply ((isBiInvariant_basicDoubleCoset j).heckeFun_adjoint B _ _ ((mem_sphericalAt_iff _).1 hv')).2.trans <;> simp [heckeSplit_star, *, indicator, ↓← mem_sphericalAt_iff]
lemma heckeSplit_mem_levelSpace {K χ} (hK : K ≤ Kf ..) (h : v ∈ levelSpace π K χ) : heckeSplit π hw j v ∈ levelSpace π K χ := by simp_all [← heckeSplit_comm_of_atPlace_mem, LE.le, mem_Kf_iff, -mem_supportedOn]
lemma heckeSplit_comm (hv' : v ∈ sphericalAt π u) : heckeSplit π hw i (heckeSplit π hu j v) = heckeSplit π hu j (heckeSplit π hw i v) := by obtain ⟨h, _ | rfl | rfl⟩ := (mem_sphericalAt_iff hw).1 hv, em' (w = u ∨ star w = u); exacts [map_heckeSplit _ _ _ (by simp_all), (isBiInvariant_basicDoubleCoset i).heckeFun_comm (isBiInvariant_basicDoubleCoset j) h, by simpa [↓heckeSplit_mem_levelSpace, heckeSplit_star, *] using! ((isBiInvariant_basicDoubleCoset i).heckeFun_comm ((isBiInvariant_basicDoubleCoset j).heckeFun_adjoint (0 : _ →ₗ[A] _ →ₗ[A] A) h (by simp) h).1 h)]
omit hv
lemma IsUnitary.le_span_hecke_eigenvectors [Module ℂ W] {π B} (hB : IsUnitary π B) {p} (hp : ∀ w, p w → w.IsSplit ∧ p (star w)) {U : Submodule ℂ W} [Module.Finite ℂ U] (hU : ∀ w : FinPlace E, p w → U ≤ levelSpace π (maxCompactAt n w)) (h : ∀ w h j, ∀ x ∈ U, heckeSplit π (hp w h).1 j x ∈ U) : U ≤ .span ℂ {x ∈ U | ∃ c : Subtype p × ℕ → ℂ, ∀ i, heckeSplit π (hp _ i.1.2).1 i.2 x = c i • x} := U.comap_subtype_eq_top.1 (Not.imp_symm (exists_eigenvector_of_commute _ (fun i ↦ h _ (hp _ i.1.2).2 i.2) (by grind [heckeSplit_comm, IsConcreteLE.le_iff])) fun ⟨c, H, _⟩ ↦ H fun x a ↦ Submodule.subset_span ⟨x.2, star c, fun ⟨⟨w, o⟩, i⟩ ↦ ((by simpa using a :) _ o i).elim (·.rec (by simp) (fun _ r x s ↦ sub_eq_zero.1 ((hB.1 _ ·
 |>.1.ne).mtr (by simp [heckeSplit_adjoint _ i B _ (hU w o _) hB.2, heckeSplit_comm, ↓hU _ _ _, hp w o, *, by simpa [sub_eq_iff_eq_add] using r _ s]; ring))) x)⟩)
abbrev Weight (E : Type) [Field E] := (InfinitePlace E → ℕ → ℕ) × (InfinitePlace E → ℤ)
def heckePoly {R : Type} [CommRing R] (q N : ℕ) (t : ℕ → R) := ∑ j ∈ .range (N + 1), C ((-1) ^ j * q ^ j.choose 2 * t j) * X ^ (N - j)
variable {E n M : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] (f : Gf E n → M → ℂ)
def HasHeckePolyAt w (hw : _ ≠ w) (P : ℂ[X]) := f ∈ levelSpace (rightRegular ℂ ..) (maxCompactAt n w) ∧ ∃ t, P = heckePoly w.q (Fintype.card n) t ∧ ∀ j, heckeSplit (rightRegular ℂ ..) hw j f = t j • f
def IsEigenform (P : _ → _) := f ≠ 0 ∧ ∀ᶠ w in .cofinite, w.q.Prime → ∃ hw, HasHeckePolyAt f w hw (P w)
def IsSphericalOff (S : Finset _) f (P : FinPlace E → _) := f ≠ 0 ∧ (∀ k ∈ Kf .. ⊓ Gf.trivialOn n S, rightRegular ℂ _ (M → ℂ) k f = f) ∧ ∀ w hw, w ∉ S → star w ∉ S → HasHeckePolyAt f w hw (P w)
def HasLabel {w} (hw : _ ≠ w) (Ξ : _ → ℂ) := (∀ k, reduceGL k = 1 → rightRegular ℂ _ _ (atSplit hw k.1) f = f) ∧ ∑ᶠ x, star (Ξ x) • rightRegular ℂ _ _ (atSplit hw (Function.surjInv reduceGL_surjective x).1) f ≠ 0
def jumps {E : Type} [Field E] [CMType E] (κ : Weight E) N σ := (Multiset.range N).map fun j ↦ let u := κ.2 (.mk σ) + ∑ h ∈ .Ioo j N, κ.1 (.mk σ) h + (N - 1 - j); ite (σ = Φ (.mk σ)) (N - 1 - u) u
variable (n : Type _) {W E : Type _} [Fintype n] [AddCommGroup W] [Module ℂ W] [Field E] [NumberField E] (w : FinPlace E) (t : ℕ → W) (X : ℂ)
def heckePolyEval := ∑ i ∈ .range (Fintype.card n + 1), ((-X) ^ i * w.q ^ i.choose 2) • t i
variable {n} [NumberField.IsCMField E] (π : Representation ℂ (Gf E n) W) {w : FinPlace E} (hw : _ ≠ w)
def heckePolyOp := heckePolyEval n w (heckeSplit π hw)
def IsSphericalWith (p : _ → ℂ) y := y ∈ sphericalAt π w ∧ ∀ T, heckePolyOp π hw T y = p T • y
end
variable {n ι A W E : Type*} [Fintype n] [Field E] [NumberField E] [NumberField.IsCMField E] {w : ι → FinPlace E} [CommRing A] [AddCommGroup W] [Module A W] {π : Representation A (Gf E n) W} {H : Subgroup (∀ i, GL n (ResField (w i)))} {χ : H →* A}
lemma levelSpace_levelOf_apply {v} (hv : v ∈ levelSpace π _ (χ.comp (levelOf.reduction ..))) k (x : H) (e : Kf.reduceFamily w k = x.1) : π k v = χ x • v := by cases x; aesop (add simp mem_levelOf)
variable [Finite ι] [IsConjApart w] (s : ∀ i, GL n (ResField (w i)))
@[local grind] def liftResidue := (exists_reduceFamily_eq s).choose
lemma liftResidue_mem_supportedOn : (liftResidue s).1 ∈ Gf.supportedOn n (.range w) := by grind
@[local simp] lemma reduceFamily_liftResidue : Kf.reduceFamily w (liftResidue s) = s := by grind
lemma apply_liftResidue_eq (v : levelSpace π _ (χ.comp (levelOf.reduction ..))) k {s} (e : Kf.reduceFamily w k = s) : π (liftResidue s).1 v = π k v := by simpa using congr(π k $(levelSpace_levelOf_apply v.2 (k⁻¹ * _) 1 (by aesop)))
variable (π χ) in
def levelRep {S} [Group S] (φ : S →* _) (h : ∀ s (x : H), ∃ hx, χ ⟨(φ s)⁻¹ * x * φ s, hx⟩ = χ x) : Representation A S (levelSpace π _ (χ.comp (levelOf.reduction ..))) := ⟨⟨fun s ↦ (π (liftResidue (φ s))).restrict fun v hv g ↦ by erw [← map_smul, ← (h ..).2, ← levelSpace_levelOf_apply hv ((liftResidue (φ s))⁻¹ * ⟨_, levelOf_le_Kf g.2⟩ * _)] <;> aesop, by ext; simp [apply_liftResidue_eq _ 1]⟩,
 by intros; ext; simpa using! apply_liftResidue_eq _ (_ * _) (by simp)⟩
open Finset PowerSeries Polynomial Classical NumberField
variable {E n W W' : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {π : Representation ℂ (Gf E n) W} {w : FinPlace E} {p : ℂ → ℂ} {y : W} {π' : Representation ℂ (Gf E n) W'} {hw : _ ≠ w} {σ : ℂ →+* ℂ} (L : W →ₛₗ[σ] W')
attribute [local simp] heckeGL heckePolyOp heckePolyEval IsSphericalWith mul_smul
lemma isSphericalWith_of_heckeSplit (hy : y ∈ sphericalAt π w) {t} (h : ∀ i, heckeSplit π hw i y = t i • y) : IsSphericalWith π hw (heckePolyEval n w t) y := by simp_all [sum_smul]
lemma IsSphericalWith.smul {a : ℂ} (h : IsSphericalWith π hw p y) : IsSphericalWith π hw p (a • y) := by simp_all [smul_comm a]
lemma map_heckePolyOp T (hL : ∀ g ∈ Gf.supportedOn n {w}, L (π g y) = π' g (L y) := by tauto) : L (heckePolyOp π hw T y) = heckePolyOp π' hw (σ T) (L y) := by simp [map_heckeSplit _ _ L hL]
lemma heckePolyOp_adjoint (hw : w.IsSplit) {Z} [AddCommGroup Z] [Module ℂ Z] {z} (B : W →ₛₗ[σ] W' →ₗ[ℂ] Z) (hy : y ∈ sphericalAt π w) (hz : z ∈ sphericalAt π' w) (hB : ∀ g x y, B (π g x) (π' g y) = B x y) X : B (heckePolyOp π hw X y) z = B y (heckePolyOp π' hw.star (σ X) z) := by simp [← heckeSplit_adjoint (π := π), *]
lemma sum_coeff_invOfUnit_smul_eq {R V} [CommRing R] [Algebra R ℂ] [AddCommGroup V] [Module ℂ V] {a b : ℕ → V} {s t r} {Q : R[X]} (hQ : Q.coeff 0 = 1) (h : r ∈ s) (H : ∀ U : ℂ, ∑ i ∈ t, U ^ i • b i = Q.aeval U • ∑ i ∈ s, U ^ i • a i) : ∑ i ∈ t, algebraMap R ℂ (coeff r (invOfUnit Q 1 * .X ^ i)) • b i = a r := Module.eval_apply_injective ℂ (by ext f; simpa [← mul_assoc, mul_sum, mul_comm (f _), *, ← PowerSeries.coeff_map, ← RingHom.map_mul] using congr(((invOfUnit Q 1).map (algebraMap R ℂ) * coeToPowerSeries.ringHom $((funext (by simpa [eval_finsetSum, mul_comm] using congr(f $(H ·))) : ∑ i ∈ t, f _ • .X ^ i = Q.map (algebraMap R ℂ) * ∑ i ∈ s, f _ • .X ^ i))).coeff r))
lemma heckeSplit_mem_of_heckePolyOp (N : Submodule ℂ _) (h : ∀ T, heckePolyOp π hw T ∈ N) i : heckeSplit π hw i ∈ N := byCases (by simpa using (@sum_coeff_invOfUnit_smul_eq ℂ _ _ _ _ _ _ 0 _ ∅ i 1 (by simp) · (fun U ↦ by simpa using (N.ker_mkQ.ge (h (-U))).symm) |>.symm :)) (by simp_all [heckeSplit, heckeFun, le_card_of_mem_basicDoubleCoset.mt])
lemma exists_heckeSplit_eq_smul p : ∃ t : ℕ → ℂ, ∀ y, IsSphericalWith π hw p y → ∀ i, heckeSplit π hw i y = t i • y := (skolem.1 (heckeSplit_mem_of_heckePolyOp ((LinearMap.id.smulRight (@Subtype.val _ (IsSphericalWith π hw p))).range.comap (.pi (.applyₗ ·.1))) fun T ↦ ⟨_, funext (·.2.2 T |>.symm)⟩)).imp (by simp_all [funext_iff, -IsSphericalWith])
