import Lib.General.Algebra.ZerosCostDegree
open Finset MvPolynomial Matrix Sigma SetLike
variable {σ Φ m R S : Type} {l : Φ × ℕ →₀ ℕ} [CommRing R] [CommRing S] {c : m → Φ} (φ : R →+* S) (p q : MvPolynomial σ R) {n n' n'' : Φ → _} [∀ τ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] (z : ∀ τ, Matrix (n' τ) (n τ) R) {f}
attribute [local simp] rowSubst det_apply map_finsuppProd coeff_map aeval_bind₁ diagramWeight tableauPoly pow_add ite_and minor borelMul highestPoly smul_sum Matrix.mul_apply jet_monomial nablaBasis detPow
lemma mem_nabla : f ∈ nabla R c l ↔ ∀ S [CommRing S] [Algebra R S] b y, aeval (borelMul c b y) f = (l.prod fun p k ↦ (b (p.1, p.2, p.2) : S) ^ k) * aeval y f := by simpa [nabla, ← C_mul'] using ⟨fun h _ _ _ b _ ↦ by simpa [comp_aeval_apply] using! congr(aevalTower (aeval b) _ $h), by tauto⟩
instance : GradedMonoid (nabla R c) := by refine' {..} <;> simp_all [mem_nabla, Finsupp.prod_add_index', mul_mul_mul_comm]
lemma minor_mem_nabla {h τ} {I : Fin h → m} (hI : ∀ s, c (I s) = τ) : minor R I ∈ nabla R c (∑ i ∈ range h, .single (τ, i) 1) := mem_nabla.2 fun _ _ _ _ y ↦ by simpa +contextual [← Finsupp.prod_finsetSum_index, prod_range, hI, sum_ite, filter_ge_eq_Iic, Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, ↓det_of_isUpperTriangular, BlockTriangular, mul_comm, ↓isEmpty_Prop] using det_mul (of (y ⟨I ·, ·⟩)) (of (if · ≤ · then _ else 0))
omit [∀ τ, Fintype (n' τ)] in
lemma rowSubst_mem_nabla {f} (h : f ∈ nabla R fst l) : rowSubst z f ∈ nabla R fst l := by simp [mem_nabla, ← mem_nabla.1 h, borelMul.eq_unfold, sum_mul, univ.sum_comm]
lemma rowSubst_rowSubst z' f : rowSubst z (rowSubst (n' := n'') z' f) = rowSubst (fun τ ↦ z' τ * z τ) f := by simp [bind₁_bind₁, mul_smul, sum_smul, @sum_comm (n' _)]
@[simp] lemma rowSubst_one (f : MatrixPoly (Sigma n) R) : rowSubst (fun _ ↦ 1) f = f := by simp
lemma fPC : fockPairing R p q = fockPairing R q p := by simp [fockPairing, jet_eq_sum]; grind [sum_congr_of_eq_on_inter]
lemma map_jet F : φ (jet R p F) = jet S (map φ p) (.map φ F) := p.induction_on' (by simp) (by aesop)
lemma map_fockPairing : φ (fockPairing R p q) = fockPairing S (map φ p) (map φ q) := map_jet ..
lemma fockPairing_rowSubst p : ∀ q, fockPairing R (rowSubst z p) q = fockPairing R p (rowSubst (fun τ ↦ (z τ)ᵀ) q) := by
 set w := rowSubst fun τ ↦ (z τ)ᵀ; have ⦃p i⦄ : (w p).pderiv i = ∑ a, z _ i.1.2 a • w (p.pderiv (⟨_, a⟩, i.2)) <;> apply
  p.induction_on <;> simp_all [w, fockPairing_C, fockPairing_mul_X, @mul_sum (n _), hom_bind₁, apply_ite]; aesop
variable [Fintype Φ] {N : Φ → ℕ} {κ : Φ → ℕ → ℕ} {κ' : Φ → ℕ → ℕ} {p}
lemma fockPairing_star_self_pos [PartialOrder R] [StarRing R] [StarOrderedRing R] [IsDomain R] (hp : p ≠ 0) : 0 < fockPairing R (map (starRingEnd R) p) p := by erw [fPC, jet_eq_sum]; apply sum_pos <;> simp_all [star_right_conjugate_pos, isRegular_iff_ne_zero, Finsupp.prod, prod_pos, Nat.factorial_pos, starRingEnd_apply]
lemma diagramWeight_apply τ i : diagramWeight N κ (τ, i) = (Ioo i (N τ)).sum (κ τ) := by simp [Finsupp.single_apply]; grind [sum_congr_of_eq_on_inter]
lemma diagramWeight_add : diagramWeight N (κ + κ') = diagramWeight N κ + diagramWeight N κ' := by simp
@[simp] lemma map_nablaBasis i : map φ (nablaBasis R n κ i) = nablaBasis S n κ i := by simp
@[simp] lemma map_highestPoly : map φ (highestPoly R κ N) = highestPoly S κ N := by simp
@[simp] lemma map_detPow e : map φ (detPow R n e) = detPow S n e := by simp
@[simp] lemma detPow_zero : detPow R n 0 = 1 := by simp
