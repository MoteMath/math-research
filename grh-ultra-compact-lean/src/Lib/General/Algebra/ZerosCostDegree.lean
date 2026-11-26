import Lib.General.LinearAlgebra.ColumnLattices
noncomputable section
open Classical MvPolynomial Module Finset Matrix Nat Sigma Finsupp Fintype Function Submodule Ideal
variable {σ Φ m R : Type} [CommRing R] [Fintype Φ] (n n' : Φ → Type) [∀ τ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] (c : m → Φ) (N e : Φ → ℕ) (κ : Φ → ℕ → ℕ) (τ) (z : ∀ _, Matrix _ _ R)
def borelMul (b y : _ → R) (x : m × ℕ) := ∑ i ∈ range (x.2 + 1), y (x.1, i) * b (c x.1, i, x.2)
def diagramWeight := ∑ τ, ∑ h ∈ range (N τ), κ τ h • ∑ i ∈ range h, single (τ, i) 1
variable (m R)
abbrev MatrixPoly := MvPolynomial (m × ℕ) R
abbrev Tableau N (k : ℕ → ℕ) := ∀ h : Fin N, Fin (k h) → Fin h → m
variable {m} {h N : ℕ} {k}
def jet : MvPolynomial σ R →ₗ[R] MvPowerSeries σ R →ₗ[R] R := (basisMonomials ..).constr ℕ fun d ↦ (d.prod fun _ ↦ (·!)) • MvPowerSeries.coeff d
@[local simp] def fockPairing : LinearMap.BilinForm R (MvPolynomial σ R) := (jet R).compl₂ (coeToMvPowerSeries.algHom R).toLinearMap
def minor (I : Fin h → m) : MatrixPoly m R := det (of (X ⟨I ·, ·⟩))
def nabla (l : Φ × ℕ →₀ ℕ) : Submodule R (MatrixPoly m R) := (aeval (borelMul c (C ∘ @X R _ _) X)).toLinearMap.eqLocus ((l.prod fun p ↦ (@X R _ _ (p.1, p.2, p.2) ^ ·)) • (aeval X).toLinearMap)
def tableauPoly e (T : Tableau σ N k) := ∏ h, ∏ j, @minor m R _ _ (e ∘ T h j)
def PolyRep.alternant (x : Fin N → ℂ) (l : ℕ → ℕ) := ite (l N = 0) (det (of fun i j ↦ x i ^ (l j.rev + j))) 0
def IsStdTableauSet (s : Finset (Tableau m N k)) := (∀ R [CommRing R], let v (T : Tableau m N k) := tableauPoly R id T; LinearIndepOn R v s ∧ ∀ T, v T ∈ Submodule.span R (v '' s)) ∧ ∀ M (e : Fin M ≃ m) x, (∑ T ∈ s, ∏ h, ∏ j, ∏ a, x (T h j a)) * PolyRep.alternant (x ∘ e) 0 = PolyRep.alternant (x ∘ e) (∑ h ∈ Ioo · N, k h)
def StdTableau m N k := {T // T ∈ epsilon (@IsStdTableauSet m N k)} deriving Fintype
instance : Coe Type (Φ → Type) := ⟨fun n _ ↦ n⟩
abbrev rankAt := card (n τ)
abbrev PolyRep.rowPos := equivFin (n τ)
abbrev WeylIndexFam := ∀ τ, StdTableau (n τ) (rankAt n τ) (κ τ)
abbrev WeylIndex n [Fintype n] κ := @WeylIndexFam Φ n _ κ
abbrev nablaFam := nabla R (@Sigma.fst _ n) (diagramWeight (rankAt n) κ)
def nablaBasis (i : WeylIndexFam n κ) := ∏ τ, tableauPoly (m := Σ τ, n τ) R (Sigma.mk τ) (i τ).1
def highestPoly (N : Φ → ℕ) := ∏ τ, tableauPoly R (Sigma.mk τ) (fun h _ ↦ Fin.castLE h.is_le' : Tableau _ (N τ) (κ τ))
def detPow := ∏ τ, minor (m := Σ τ, n τ) R (⟨τ, (equivFin (n τ)).symm ·⟩) ^ e τ
def PolyRep.genericMatrixAt := of (@X R (Σ τ, n τ × n τ) _ ⟨τ, ·, ·⟩)
def hookNumber N := fockPairing ℤ (highestPoly ℤ κ N) (highestPoly ℤ κ N)
def schurDetExp := ite (rankAt n τ < rankAt n' τ) (κ τ (rankAt n τ)) 0
@[grind] def FitsRanks := ∀ τ, rankAt n τ ≤ rankAt n' τ ∧ ∀ h ∈ Ioo (rankAt n τ) (rankAt n' τ), κ τ h = 0
variable {R n n'} (y : (Σ τ, n τ) × ℕ → R) (α a) (f g : MvPolynomial σ R) (i F)
def rowSubst : MatrixPoly (Σ τ, n' τ) R →ₐ[R] MatrixPoly (Σ τ, n τ) R := aeval fun x ↦ ∑ a, z _ x.1.2 a • X (⟨_, a⟩, x.2)
def permArray (e : ∀ τ, n τ → ℕ) (x : (Σ τ, n τ) × ℕ) := @ite R (e _ x.1.2 = x.2) _ 1 0
instance : CoeOut (∀ τ, n τ ≃ Fin (rankAt n τ)) (∀ τ, n τ → ℕ) := ⟨(· · ·)⟩
abbrev PolyRep.nablaCombination := Fintype.linearCombination R (nablaBasis R n κ)
abbrev PolyRep.evalMat := eval (R := R) fun x : Σ τ, n τ × n τ ↦ z _ x.2.1 x.2.2
omit [Fintype Φ] [∀ τ, Fintype (n τ)] in @[simp] lemma PolyRep.genericMatrixAt_map_evalMat τ : (genericMatrixAt R n τ).map (evalMat z) = z τ := by ext; simp [genericMatrixAt]
@[local simp↓ low] lemma jet_eq_sum : jet R f F = ∑ m ∈ f.support, f.coeff m * (m.prod fun _ ↦ (↑·!)) * F.coeff m := by simp [jet, Basis.constr_apply]; ac_rfl
lemma jet_monomial : jet R (monomial α a) F = a * (α.prod fun _ : σ ↦ (↑·!)) * F.coeff α := by aesop
@[local simp↓] lemma jet_mul_X : jet R (f * X i) F = jet R f (F.pderiv i) := by simp +singlePass [← mul_prod_erase' _ i, F.coeff_pderiv]; simp!; grind
lemma fockPairing_monomial : fockPairing R (monomial α a) g = α.prod (fun _ ↦ (·!)) * (a * g.coeff α) := by simp; grind
lemma fockPairing_C : fockPairing R (C a) g = a * constantCoeff g := by aesop
lemma fockPairing_mul_X : fockPairing R (f * X i) g = fockPairing R f (pderiv i g) := by simp [MvPowerSeries.pderiv_coe]
def schur := of (invFun (Fintype.linearCombination R (nablaBasis R n κ · * detPow R n (schurDetExp n n' κ))) ∘ rowSubst z ∘ nablaBasis R n' κ)
def tableauWeight {κ} (i : WeylIndexFam n κ) τ a := ∑ h, ∑ j, #{s | (i τ).1 h j s = a}
variable (n) [Fintype m] (z : Matrix m σ R) {R'} [CommRing R'] [Fintype σ]
def weylKernel := rowSubst (fun τ ↦ of fun i ↦ (y ⟨⟨τ, ·⟩, i.1⟩)) (highestPoly R κ (rankAt n))
def weylGram := of (invFun (PolyRep.nablaCombination (R := ℤ) κ) ∘ invFun (PolyRep.nablaCombination κ) (weylKernel n κ X))
def toPoly := PolyRep.nablaCombination κ ∘ₗ ((weylGram n κ).map (@Int.cast R _)).mulVecLin
def weylEval := (nablaBasis R n κ i).eval y
def linSubst : MvPolynomial σ R →ₐ[R] MvPolynomial m R := aeval (∑ t, z t · • X t)
lemma fockPairing_linSubst f : ∀ g, fockPairing R f (linSubst z g) = fockPairing R (linSubst zᵀ f) g := by have ⦃f i⦄ : (linSubst z f).pderiv i = ∑ a, z i a • linSubst z (f.pderiv a) <;> apply f.induction_on <;> simp_all [linSubst, fockPairing_C, fockPairing_mul_X, @Finset.mul_sum σ, -fockPairing, hom_bind₁, apply_ite]
variable {n} (a : ℕ) (ψ : R →+* R') (A B : Matrix σ σ R)
abbrev weylGramOver {κ} := (weylGram n κ).map (@Int.cast R _)
variable (σ) in abbrev Monomials := ↥((@univ σ _).finsuppAntidiag a)
lemma linSubst_eq_bind₁ : linSubst A = bind₁ Aᵀ.toMvPolynomial := by simp [linSubst, X, smul_monomial]; rfl
attribute [local simp ←] ext_iff toMvPolynomial_mul C_mul' degree_eq_sum
@[simp] lemma linSubst_one : linSubst 1 f = f := by simp [linSubst_eq_bind₁]
lemma linSubst_mul : linSubst (A * B) f = linSubst A (linSubst B f) := by simp [linSubst_eq_bind₁, bind₁_bind₁]
lemma map_linSubst : MvPolynomial.map ψ (linSubst A f) = linSubst (A.map ψ) (MvPolynomial.map ψ f) := by simp [linSubst, map_bind₁]
variable {a f} {S} [Fintype S] (α : Monomials σ a)
lemma Monomials.degree_eq : α.1.degree = a := by aesop
lemma Monomials.isHomogeneous_linSubst : (linSubst A (monomial α 1)).IsHomogeneous a := by simpa [linSubst_eq_bind₁] using! (isHomogeneous_monomial 1 α.degree_eq).aeval _ Aᵀ.toMvPolynomial_isHomogeneous
lemma sum_monomials_eq_of_isHomogeneous (hf : f.IsHomogeneous a) : ∑ β : Monomials σ a, f.coeff β • monomial β 1 = f := by ext; simpa [coeff_sum, eq_comm, sum_attach _ fun β ↦ ite _ (f.coeff β) 0] using hf.coeff_eq_zero
def symPowMatrix a := MonoidHom.mk ⟨fun A ↦ @of _ _ R fun β α : Monomials σ a ↦ (linSubst A (monomial α.1 1)).coeff β.1, by simp [eq_comm, one_apply]⟩ fun A B ↦ by ext; simpa [linSubst_mul, @mul_comm R, coeff_sum, Matrix.mul_apply] using congr((linSubst A $(sum_monomials_eq_of_isHomogeneous (Monomials.isHomogeneous_linSubst ..))).coeff _).symm
def exponentOf : (S → Monomials σ a) ↪ σ × S →₀ ℕ := ⟨fun β ↦ equivFunOnFinite.symm fun x ↦ (β x.2).1 x.1, id fun _ _ h ↦ by ext; congrm $h (_, _)⟩
def polyOfCoeffs := ∑ β : S → Monomials σ a, monomial (R := R) (exponentOf β) ∘ₗ .proj β
lemma symPowMatrix_map : symPowMatrix a (A.map ψ) = (symPowMatrix a A).map ψ := by simp [symPowMatrix, ← coeff_map, map_linSubst]
lemma exists_le_cost_of_vanishing {K ι S : Type} [Field K] [Fintype ι] [Fintype S] (κ : ι → ℕ) (κ0 : ∀ u, 0 < κ u) (z : S → _) (inj : z.Injective) (card : ∏ u, κ u ≤ Fintype.card S) (hz : ∀ u, ∃ g : MvPolynomial ι K, (∀ α ∈ g.support, weight (κ · : ι → ℝ)⁻¹ α < 1) ∧ ∀ t, MvPolynomial.eval (z t) g = z t u ^ κ u) (d : ℕ) f (f0 : f ≠ 0) (hf : ∀ t, f ∈ vanishingIdeal K {z t} ^ d) : ∃ α ∈ f.support, d ≤ weight (κ · : ι → ℝ)⁻¹ α := by
 choose g hg h0 using hz
 have ⟨Γ, hΓ⟩ := (@finite_of_degree_lt ι _ d).exists_finset_coe
 let T (w : ι → K) := bind₁ (X + C ∘ w)
 let J := LinearMap.pi fun y : S × Γ ↦ lcoeff K y.2 ∘ₗ (T (z y.1)).toLinearMap
 have hJ {p} y h : J p y = 0 := (mem_pow_idealOfVars_iff' ..).1 (le_comap_pow (T _) d (pow_right_mono (fun p ↦ by simpa [T, degree_eq_zero_iff, hom_bind₁, ← constantCoeff_eq] using (mem_pow_idealOfVars_iff' 1 (T _ p)).2) (I := vanishingIdeal K {z y.1}) d h)) _ (hΓ.le y.2.2)
 let b α γ := monomial α 1 * bind₁ (fun u ↦ X u ^ κ u - g u) (monomial γ 1)
 let v (x : univ.finsupp (range ∘ κ) × Γ) := b x.1 x.2
 have lin {N p} h : p ∈ N := span_le.2 (Set.forall_mem_image.2 h) ((basisMonomials ι K).mem_span_image.2 (le_refl ↑p.support))
 have div M : ∀ α γ, (d ≤ γ.degree + weight (κ · : ι → ℝ)⁻¹ α → J.ker ≤ M) → b α γ ∈ span K (.range v) ⊔ M := (wellQuasiOrdered_le.of_surjective (s := weight (κ · : ι → ℝ)⁻¹ ⁻¹'o LE.le) ⟨id, fun e ↦ by simp [weight_eq_sum]; grw [e _]⟩ (⟨·, rfl⟩)).wellFounded.fix fun α ih γ hγ ↦ by
  by_cases! e : ∀ u, α u < κ u
  exact (lt_or_ge _ d).elim (mem_sup_left <| subset_span ⟨⟨⟨_, by simpa [mem_finsupp_iff]⟩, γ, hΓ.ge ·⟩, rfl⟩) fun o ↦ mem_sup_right (hγ (by grw [o, weight_eq_sum]; simp; positivity) (funext (hJ · (mul_mem_left _ _ (le_comap_pow _ d (pow_right_mono (by simp [Ideal.span_le, h0]) d ((mem_pow_idealOfVars_iff ..).2 (by simpa))))))))
  obtain ⟨u, β, rfl⟩ := e.imp fun _ ↦ exists_add_of_le ∘ single_le_iff.2
  simp [weight, κ0, ne_of_gt] at *
  convert add_mem (ih β ?_ ?_ (Finsupp.single u 1 + γ) ?_) (@lin (.comap (.mulRight K (b β γ)) (_ ⊔ M)) (g u) fun δ e ↦ by simp [b]; apply ih <;> grind) <;> simp [b, monomial_single_add] <;> grind
 refine f0.imp_symm fun H ↦ (range_ker_disjoint (v := v) (linearIndependent_of_top_le_span_of_card_le_finrank (fun y _ ↦ ?_) (by simp; bound))).le_bot ⟨lin fun α e ↦ by simpa [b, mt (⟨α, e, ·⟩) H] using div ⊥ α 0, funext (hJ · (hf _))⟩
 have ⟨p, h⟩ := exists_forall_sub_mem_ideal (I := (vanishingIdeal K {z ·} ^ d)) (fun t t' ↦ .pow ∘ isCoprime_of_isMaximal ∘ mt fun h ↦ inj (by ext u; simpa using h.ge (by simp : X u - C (z t' u) ∈ _))) fun t ↦ T (-z t) (∑ γ, monomial γ.1 (y (t, γ)))
 rw [Set.range_comp, span_image, ← show J p = y by
  ext x; simpa [J, T, bind₁_bind₁, coeff_sum] using hJ x (h _)]
 exact (comap_map_eq ..).ge (lin fun α _ ↦ by simpa [b] using div J.ker α 0)
