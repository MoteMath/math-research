import Lib.GLn.SchurModule.Nabla
open MvPolynomial Finset
section
noncomputable section
open MonomialOrder Finsupp Matrix Fin
namespace PolyRep
variable {Φ J m R ι : Type} [CommRing R] {F δ G : ι → _} {t : Finset ι} {γ} {a : R}
def columnOrder : MonomialOrder ℕ := @lex ℕᵒᵈ _ _
lemma cOLt i δ : (∀ j > i, γ j = δ j) → γ i < δ i → γ ≺[columnOrder] δ := (⟨_, ·, ·⟩)
abbrev HasLeadingTerm F γ (G : R) := columnOrder.degree F ≼[columnOrder] γ ∧ F.coeff γ = G
lemma HasLeadingTerm.mul {F F' γ' a'} : HasLeadingTerm F γ a → HasLeadingTerm F' γ' a' → HasLeadingTerm (F * F') (γ + γ') (a * a') := by grind [degree_mul_le, coeff_mul_of_add_of_degree_le]
lemma HasLeadingTerm.of_monomial : HasLeadingTerm (monomial γ a) γ a := ⟨degree_monomial_le _, by simp⟩
lemma HasLeadingTerm.prod (h : ∀ i, HasLeadingTerm (F i) (δ i) (G i : R)) : HasLeadingTerm (t.prod F) (t.sum δ) (t.prod G) := t.induction (by bound) (by grind [mul])
lemma HasLeadingTerm.sum (h : ∀ i, HasLeadingTerm (F i) (δ i) (G i : R)) j (H : ∀ i ∈ t, i ≠ j → δ i ≺[columnOrder] δ j) (hj : j ∉ t → G j = 0 := by simp) : HasLeadingTerm (t.sum F) (δ j) (G j) := by grw [HasLeadingTerm, degree_sum_le, coeff_sum, sum_eq_ite j, t.sup_le_iff] <;> grind [coeff_eq_zero_of_lt]
variable [Fintype J] (c : m → Φ) (τ h : J → _) (x : m) (l : ℕ →₀ ℕ)
def rExp : MatrixPoly m R ≃ₐ[R] MvPolynomial ℕ (MatrixPoly {a // a ≠ x} R) := (renameEquiv R (((Equiv.optionSubtypeNe x).symm.prodCongr 1).trans optionProdEquiv)).trans (sumAlgEquiv ..)
def iLac := Icc 0 (l - l.comapDomain .succ (by simp))
def cWt := ∑ j, ∑ i ∈ range (h j), single ((τ j : Φ), i) 1
abbrev CTab := ∀ j, Fin (h j) → {a // c a = τ j}
variable {c τ h x} (S) [CommRing S] (I : CTab c τ h)
def mPrd := ∏ j, minor S (I j · |>.1)
attribute [local simp] cWt minor Finsupp.le_def sum_range_succ det_apply' prod_pow_eq_pow_sum
lemma dWcW [Fintype Φ] N κ : diagramWeight N κ = @cWt Φ (Σ τ, Σ h : Fin (N τ), Fin (κ τ h)) _ (·.1) (·.2.1) := by simp [↓Fintype.sum_sigma, diagramWeight, sum_range]
lemma mPN : mPrd R I ∈ nabla R c (cWt τ h) := SetLike.prod_mem_graded _ _ _ fun _ _ ↦ minor_mem_nabla (by grind)
lemma exBd h (H : γ ∈ iLac ((cWt τ h).curry (c x))) : ∃ k, cWt τ h = γ.mapDomain (c x, ·) + cWt τ k ∧ ∀ I : CTab (c ∘ (↑)) τ k, ∃ K : CTab c τ h, (∀ R [CommRing R], HasLeadingTerm (rExp x (mPrd R K)) γ (mPrd R I)) ∧ ∀ y : m → ℂ, ∏ j, ∏ s, y (K j s) = y x ^ degree γ * ∏ j, ∏ s, y (I j s) := by
  simp [iLac, Finsupp.single_apply, sum_ite, ite_and] at H; choose S _ a using (exists_subset_card_eq <| H · |>.trans (le_card_sdiff ..))
  let e j := ite (∀ i, j ∉ S i) 0 1; choose k K using fun j ↦ le_iff_exists_add'.1 (by grind : e j ≤ h j); cases funext K; cases show γ = ∑ j, single (k j) (e j) by
    ext; simp [← a, card_eq_sum_ones, ← sum_ite_mem_eq]; grind
  use k, by simp [mapDomain_finsetSum, ← sum_add_distrib, e]; congr!; split <;> simp; grind, fun I ↦ ⟨(⟨if h : _ then I · ⟨·, h⟩ else x, by grind⟩), fun R _ ↦ ?_, by simp [prod_univ_add]; grind⟩
  erw [map_prod]; refine .prod fun j ↦ ?_; dsimp +instances; rcases h : e j with _ | ⟨⟨⟩⟩ <;> [convert HasLeadingTerm.of_monomial; convert HasLeadingTerm.sum (t := univ) (fun s ↦ @.of_monomial (MatrixPoly _ R) _ (single s.1 1) ((-1) ^ (k j + s.1) * det (of (X ⟨I j · |>.1, s.succAbove ·⟩)))) (last _) (by grind [cOLt (k
    j)]); lia] <;> simp [rExp, (I ..).1.2, ↓det_succ_row' _ (last _), monomial_eq]; ac_rfl
lemma altS {N} (A : Antitone l) i x : @alternant (N + 1) x l = (-1) ^ i.1 * (∏ a, (x (i.succAbove a) - x i)) * ∑ γ ∈ iLac l, x i ^ degree γ * alternant (x ∘ i.succAbove) (l - γ) := by
  have := @A (N + 1); erw [alternant, iLac, ← det_classical, det_eq_of_forall_col_eq_smul_add_pred (B := fun _ ↦ vecCons _ _) _ (by tauto) fun _ _ ↦ by erw
    [← sub_eq_iff_eq_add, mul_comm, ← mul_geom_sum₂_Ico _ (x i) (by gcongr <;> first | exact A (by grind) | grind), cons_val_succ], det_classical, det_succ_row' _ i, sum_univ_succ, det_mul_column, det_apply']
  simp [alternant, prod_univ_sum, Finset.mul_sum, -val_rev]; rw [univ.sum_comm, ite_sum_zero, ← sum_filter, ← sum_filter]; refine' sum_bij' (fun g _ ↦ onFinset (range (N + 1)) (fun n ↦ l n - (List.ofFn ((g - (↑)) ∘ rev))[n]!) _) (fun γ _ j ↦ (l - γ) j.rev + j) .. <;> simp [degree_eq_weight_one, -val_rev, sum_range, weight_apply, le_tsub_iff_left (A _), ← rev_bijective.sum_comp (l · - _)] <;> grind
end PolyRep
end
end
section
seal Finset.univ Finset.sum Finset.prod
attribute [-instance] IsAddTorsionFree.of_isDomain_charZero
open Finsupp Algebra MonomialOrder
namespace PolyRep
variable {Φ m R} [CommRing R] {c : m → Φ} {x l f}
attribute [local simp] borelMul coeff_map mul_assoc algHom prod single_apply mul_pow ite_apply
attribute [local simp ←] map_pow map_prod C_pow Finsupp.sum.eq_1 pow_mul
lemma dREI (hf : f ∈ nabla R c l) : columnOrder.degree (rExp x f) ∈ iLac (l.curry (c x)) := by
 set γ := columnOrder.degree (rExp x f); simp [iLac, le_def]; by_contra! ⟨i, _⟩; let θ := aeval (R := R) fun y ↦ Polynomial.CC (X y : MatrixPoly {a // a ≠ x} R) + .X * .CC (single (c x, i) (X (y.1, i + 1)) (c y.1, y.2)); have {p} : (θ p).coeff 0 = .C p := by apply p.induction_on <;> aesop
 let Ψ := (aevalTower ((mapAlgHom θ).comp (algHom ..)) fun j ↦ (C .X * X (i + 1)) ^ single i 1 j * X i ^ single (i + 1) 1 j * X j).comp (rExp x).toAlgHom; let b : Φ × _ → type_of% (Ψ f) | (τ, j, k) => single j (C (.C .X ^ single (c x, i) 1 (τ, j) * .X ^ single (c x, i + 1) 1 (τ, j))) k - single (c x, i) (single (j + 1) 1 k) (τ, j)
 apply absurd congr((($(mem_nabla.1 hf _ b (Ψ ∘ X)).coeff (single (i + 1) (γ i) + single i (γ (i + 1)) + γ)).coeff (l (c x, i + 1) + γ i)).coeff (l (c x, i)))
 rw [← aeval_unique, (algHom_ext fun ⟨y, _⟩ ↦ by
  simp +zetaDelta [rExp, ite_and, mul_sub]
  split_ifs <;> subst_vars <;> simp_all <;> ring : aeval _ = (mapAlgHom (.restrictScalars _
  (Polynomial.aeval (.C .X * .X)))).comp (aeval (mapAlgHom (Polynomial.aeval 0) ∘ (borelMul c b
  (Ψ ∘ X) - Ψ ∘ X) + Ψ ∘ X)))]
 simp [Ψ, aevalTower, eval₂_eq, b, -pow_ite, -Prod.mk.injEq, prod_pow_eq_pow_sum, -map_aeval, ↓if_mem_support, Polynomial.coeff_X_pow_mul', ← Polynomial.comp_eq_aeval]; rw [sum_eq_ite γ] <;> simp_all [X_pow_eq_monomial, Polynomial.coeff_mul_X_pow', Finsupp.ext_iff, apply_ite Polynomial.coeff, DFunLike.ite_apply] <;> grind [coeff_eq_zero_of_lt, degree_zero, coeff_degree_eq_zero_iff, cOLt]
lemma HasLeadingTerm.lCN (hf : f ∈ nabla R c ((columnOrder.degree (rExp x f)).mapDomain (c x, ·) + l)) : columnOrder.leadingCoeff (rExp x f) ∈ nabla R (c ∘ (↑)) l := by
  have H := _root_.mem_nabla.1 hf _ (C ∘ C ∘ @X R _ _) ((mapAlgHom (aeval X)).comp (rExp x).toAlgHom ∘ @X R _ _); rw [← aeval_unique, (algHom_ext (by simp [rExp]; aesop) : aeval _ = (aevalTower ((algHom ..).comp (aeval (borelMul (c ∘ (↑)) (C ∘ @X R _ _) X)))
    (borelMul c (C ∘ C ∘ @X R _ _) (X ·.2) ⟨x, ·⟩)).comp (rExp x).toAlgHom)] at H
  refine (IsRegular.right · ((sum (fun n ↦ mul of_monomial (prod fun j ↦ by
    simpa only [pow_eq_prod_const] using! prod fun _ ↦ sum (fun _ ↦ mul of_monomial of_monomial) j
      (by grind [cOLt j]))) _ ?_ ?_).2.symm.trans
      ((congrArg (AddMonoidAlgebra.coeff · _) H).trans ?_)))
    (by simpa using .monomial (.prod (by simp))) <;> simp_all [leadingCoeff, ↓prod_add_index', pow_add, ↓prod_mapDomain_index, ← C_mul', lt_iff_le_and_ne] <;> grind [columnOrder.le_degree]
end PolyRep
end
section
open MonomialOrder Submodule Finsupp Nat
attribute [local simp] zero_lt_iff single_apply sub_mem sum_smul_mem
lemma PolyRep.exMB {Φ J m} [Fintype m] [Fintype J] c τ h : ∃ (ι : Type) (_ : Fintype ι) (I : ι → @CTab Φ J m c τ h), (∀ R [CommRing R], LinearIndependent R (fun i ↦ mPrd R (I i)) ∧ nabla R c (cWt τ h) ≤ span R (.range fun i ↦ mPrd R (I i))) ∧ ∀ [Subsingleton Φ] t N (e : Fin N ≃ m) (x : m → ℂ), (∑ i, ∏ j, ∏ s, x (I i j s)) * alternant (x ∘ e) 0 = alternant (x ∘ e) (cWt τ h ⟨t, ·⟩) := by
  obtain ⟨_, _ | ⟨⟨y⟩⟩⟩ := columnOrder.toSyn.injective, isEmpty_or_nonempty m
  obtain ⟨⟨⟩⟩ := eq_or_ne h 0 <;> [use Unit; use Empty] <;> use .ofFinite _, nofun, fun R ↦ ⟨?_, (·.eq_C_of_isEmpty ▸ ?_ ∘ (mem_nabla.1 · R 0 0))⟩, fun _ ↦ rec ?_ fun _ _ ↦ (·.isEmpty.elim 0) <;> simp_all [univ_eq_empty, Fintype.linearIndependent_iff, mPrd, minor, alternant, ← C_mul', cWt, ← one_eq_span, pow_add, ← prod_finsetSum_index, funext_iff, prod_pow_eq_pow_sum, nontriviality]
  choose k K B L V using (exBd h <| Subtype.prop ·)
  choose ι _ I hI W using (exMB (m := {a // a ≠ y}) _ τ <| k ·)
  use Sigma ι, inferInstance, (B _ <| I _ ·.2), fun R ↦
    have L γ a : HasLeadingTerm (rExp y (sum a fun i (r : R) ↦ r • mPrd R (B γ (I γ i)))) γ (a.sum fun i ↦ (· • mPrd R (I γ i))) := by simp_all [HasLeadingTerm, sum, degree_le_iff, not_imp_comm]
    ⟨.of_ker _ fun a _ ↦ by_contra fun H ↦ ?_, wellFounded_lt.onFun (f := columnOrder.toSyn ∘ columnOrder.degree ∘ rExp y).fix fun f ih hf ↦ ?_⟩, @fun S t ↦ rec (nomatch ·.2 y) fun N _ f x ↦ ?_
  have ⟨x, hx⟩ := a.splitSupport.exists_max_image (columnOrder.toSyn ·) (by simpa [splitSupport]); simp_all [← (HasLeadingTerm.sum (L · _) _ (by grind) (absurd hx.1)).2, ← map_sum, sigma_sum, linearIndependent_iff, mem_splitSupport_iff_nonzero, linearCombination_apply]; exact (mem_span_range_iff_exists_finsupp.1 ((hI ..).2 (HasLeadingTerm.lCN (K ⟨_, dREI hf⟩ ▸ hf)))).elim fun a ha ↦ (sub_mem_iff_left _ (sum_smul_mem _ a fun i (_ : i ∈ a.support) ↦ subset_span (by use ⟨_, i⟩))).1 (by_cases (ih _ · (by simp [*, mPN])) (by
    have H := L ⟨_, dREI hf⟩ a
    rw [ha, sum] at H; revert H
    generalize ∑ i ∈ a.support, a i • mPrd R (B _ _) = g; intro H
    have : (rExp y (f - g)).coeff (columnOrder.degree (rExp y f)) = 0 := by
      simp [H.2, leadingCoeff]
    grind [degree_sub_le, coeff_degree_eq_zero_iff, zero_mem, EmbeddingLike.map_eq_zero_iff]))
  erw [S.1 t, altS (.curry _ _) _ (f.2 y), ← (iLac _).sum_coe_sort, altS 0, mul_left_comm, Fintype.sum_sigma, univ.sum_mul]; congr with γ; simpa [K γ, Pi.sub_def, V, iLac, ← univ.mul_sum, mul_assoc, Prod.mk_right_injective] using .inl (W γ _ _ (.optionSubtype _ ⟨(finSuccEquiv' _).symm.trans f, f.4 _⟩) (x ·)); repeat simp [Antitone, cWt, ite_and] <;> bound
termination_by Nat.card m
end
section
seal Finset.univ Finset.sum Finset.prod
open Matrix PolyRep Submodule Equiv Classical Fintype Function Sigma
variable {Φ R S : Type} {F : Type _} [CommRing R] [CommRing S] [Fintype Φ] {n : Φ → Type} {n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] {κ : Φ → ℕ → ℕ} (h : FitsRanks n n' κ) (A : AddSubgroup R) (t : Φ → R) {ι : Type} {M} [Fintype ι] (z : ∀ τ, Matrix (n' τ) (n τ) R) (e : Φ → ℕ) (i : WeylIndexFam n' κ) {f} [FunLike F R S] [RingHomClass F R S] (φ : F) (g : ∀ τ, Matrix (n τ) (n τ) R) (x : ∀ τ, n τ → R)
attribute [local simp] AlgHom.map_det Matrix.map Matrix.mul_apply minor tableauPoly prod_smul prod_univ_sum RingHom.map_det detPow sum_smul sum_mul Fintype.prod_sigma mPrd diagramWeight_apply smul_sum permArray bind₁_bind₁
attribute [local simp ←] rowSubst_rowSubst det_mul det_mul_column pow_mul dWcW zsmul_eq_mul' C_mul' QuotientAddGroup.eq_zero_iff diagonal.eq_1 prod_pow_eq_pow_sum Fin.ext_iff mul_smul
omit [∀ τ, Fintype (n' τ)] in
lemma prod_tableauPoly_mem_nabla {M : Φ → ℕ} {T : ∀ τ, Tableau (n' τ) (M τ) (κ τ)} : ∏ τ, tableauPoly R (.mk τ) (T τ) ∈ nabla R fst (diagramWeight M κ) := dWcW M
 κ ▸ Eq.subst (by simp) (mPN (⟨⟨_, T _ _ ·.2.2 ·⟩, rfl⟩))
lemma iSTE {k} : IsStdTableauSet (epsilon (@IsStdTableauSet ι M k)) := epsilon_spec (by
  choose _ _ I h W using @exMB Unit (Σ _, Σ h : Fin M, Fin (k h)) ι _ _ 0 fst (·.2.1)
  use univ.map ⟨_, .of_comp (f := tableauPoly ℤ id) (by simpa using! (h ℤ).1.injective)⟩, fun R ↦ ⟨coe_map .. ▸ .image_of_comp _ _ (by simpa using! (h _).1), fun T ↦ by
    simpa [← Set.range_comp] using! (h R).2 (mPN (⟨T _ ·.2.2 ·, rfl⟩))⟩, by simpa using W ())
lemma linearIndependent_nablaBasis : LinearIndependent R (nablaBasis R n κ) := by
  induction' hk : card Φ with _ ih generalizing Φ R
  exacts [have := card_eq_zero_iff.1 hk; .of_subsingleton' default (by simp [nablaBasis, univ_eq_empty]), (card_eq_succ.1 hk).elim fun τ _ ↦ .of_comp (aeval fun (⟨σ, a⟩, j) ↦ dite (σ = τ) (C <| X ⟨· ▸ a, j⟩) (X ⟨⟨⟨_, ·⟩, a⟩, j⟩)).toLinearMap ((linearIndependent_equiv'
    (piSplitAt ..) (by simp [funext_iff, nablaBasis, prod_eq_mul_prod_subtype_ne _ τ, @Subtype.prop
    _ (· ≠ τ)])).2 (linearIndependent_smul (iSTE.1 R).1 (ih (by simp [*]))))]
lemma iRDP {e} : IsRegular (detPow R n e) := isRegular_iff_mem_nonZeroDivisors.2
 (mem_nonZeroDivisors_of_injective (f := (coeToMvPowerSeries.algHom _).comp (bind₁ (permArray (rowPos n) - X))) ((coe_injective _ R).comp (Involutive.injective (by aesop_cat)))
 (MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff (by simp [map_pow, map_sub])))
omit [Fintype Φ] [∀ τ, Fintype (n' τ)] in
lemma PolyRep.rsMn τ I : rowSubst z (minor R (⟨τ, I ·⟩)) = det ((z τ).submatrix I (rowPos n τ).symm) • minor R (⟨τ, (rowPos n τ).symm ·⟩) := by simp [rowSubst, reindex_equiv (rowPos n τ).symm]; rfl
@[simp] lemma rowSubst_detPow : rowSubst g (detPow R n e) = (∏ τ, (g τ).det ^ e τ) • detPow R n e := by simp [-minor, rsMn, mul_pow]
lemma nabla_le_span_nablaBasis_mul_detPow : nabla R fst (diagramWeight (rankAt n) κ + ∑ τ, e τ • (range (rankAt n τ)).sum (.single ⟨τ, ·⟩ 1)) ≤ (Fintype.linearCombination R (nablaBasis R n κ · * detPow R n e)).range := by
  simp_rw [← Fin.sum_const, ← Fintype.sum_sigma', dWcW]; refine (exMB _ (_ ⊕ᵥ _) (_ ⊕ᵥ _)).elim fun _ ⟨_, I, H, _⟩ ↦ (congrArg _ (sum_sum_type _)).ge.trans ((H R).2.trans (span_le.2 fun _ ⟨i, h⟩ ↦ h ▸ ?_)); choose T h using ((sigmaSubtype _).symm.surjective <| I i · ·)
  exact ⟨_, by simpa [← funext₂ h, -C_mul', -univ_eq_attach] using! congr((∏ τ, rename (·.map (mk τ)
    id) $(((mem_span_image_finset_iff_exists_fun _).1 ((iSTE.1 R).2 (T <|
    .inl ⟨τ, ·, ·⟩))).choose_spec)) * ∏ τ, ∏ j, $((rsMn (R := R) (fun _ ↦ 1) τ (T (.inr ⟨τ, j⟩))).symm))⟩
lemma PolyRep.nCI : Injective (nablaCombination (R := R) (n := n) κ) := linearIndependent_nablaBasis.fintypeLinearCombination_injective
lemma sNB : (nablaCombination κ).range = nablaFam R n κ := le_antisymm
 (by simp [span_le, nablaBasis, prod_tableauPoly_mem_nabla, -tableauPoly])
 (by simpa using nabla_le_span_nablaBasis_mul_detPow 0)
lemma scNB (h : f ∈ nablaFam R n κ) : ∑ i, invFun (nablaCombination κ) f i • nablaBasis R n κ i = f := invFun_eq (sNB.ge h)
lemma PolyRep.liNB : LinearIndependent R (nablaBasis R n κ · * detPow R n e) := linearIndependent_nablaBasis.map_injOn (.mulRight ..) iRDP.2.injOn
lemma PolyRep.coord_mem_of_coeff_mem {x : _ → R} (H : ∑ j, x j • (nablaBasis R n κ j * detPow R n e) = f) (h : ∀ d, f.coeff d ∈ A) i : x i ∈ A := by
 have E (S : Type) [CommRing S] j := (nablaBasis ℤ n κ j * detPow ℤ n e).coeff_map (algebraMap ℤ S); subst H; simp at E h; let φ := TrivSqZeroExt.inrHom ℤᵐᵒᵖ _ ∘ TensorProduct.mk ℤ ℤᵐᵒᵖ (R ⧸ A) 1; simpa [φ] using congr($(linearIndependent_iff.1 (liNB e) (φ <|
  x ·) (by ext1; simpa [φ, coeff_sum, E R, E (TrivSqZeroExt ..)] using congr(φ $(h _))) i).snd)
omit [Fintype Φ] in
@[simp] lemma FitsRanks.refl : FitsRanks n n κ := by grind
omit [Fintype Φ] in
@[simp] lemma schurDetExp_self : schurDetExp n n κ = 0 := funext (by simp [schurDetExp])
lemma PolyRep.sEqE {z} (h : ∀ i, ∑ j, M i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) = rowSubst z (nablaBasis R n' κ i)) : schur κ z = M := funext fun i ↦ (liNB _).fintypeLinearCombination_injective
 (.trans (invFun_eq ⟨_, h i⟩) (h i).symm)
@[local simp] lemma schur_diagonal_eq_prod : schur κ (diagonal <| x ·) = diagonal fun i ↦ ∏ τ, ∏ h, ∏ j, ∏ s, x τ ((i τ).1 h j s) := sEqE (by simp [diagonal, nablaBasis, rowSubst, ← prod_mul_distrib])
lemma weyl_character {a : Φ → ℕ} (e : ∀ τ, Fin (a τ) ≃ n τ) (x : ∀ _, _ → ℂ) : (schur κ (diagonal <| x ·)).trace * ∏ τ, (vandermonde (x τ ∘ e τ)).det = ∏ τ, det (of fun i j ↦ x τ (e τ i) ^ (diagramWeight (rankAt n) κ (τ, j.rev) + j)) := by simpa [← card_congr (e _), ← sum_coe_sort (epsilon _), alternant, -univ_eq_attach] using! congr(∏ τ, $(iSTE (M := rankAt n τ).2 _ (e τ) _))
@[simp] lemma schur_one (h : ∀ τ, g τ = 1) : schur κ g = 1 := sEqE (by simp [h, rowSubst])
lemma schur_diagonal : schur κ (diagonal <| x ·) = diagonal (∏ τ, ∏ a, x τ a ^ tableauWeight · τ a) := by simp [tableauWeight, @prod_comm _ _ (n _), card_filter, -sum_boole]
include h
lemma PolyRep.diagramWeight_eq_of_fitsRanks : diagramWeight (rankAt n') κ = diagramWeight (rankAt n) κ + ∑ τ, schurDetExp n n' κ τ • (range (rankAt n τ)).sum (.single ⟨τ, ·⟩ 1) := .trans (sum_congr _ _ fun τ ↦ by grind [zero_smul, schurDetExp, sum_eq_ite (rankAt n τ), sum_range_add_sum_Ico _ (h τ).1]) sum_add_distrib
@[simp ← low] lemma sum_schur_smul_nablaBasis : ∑ j, schur κ z i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) = rowSubst z (nablaBasis R _ κ i) := invFun_eq (nabla_le_span_nablaBasis_mul_detPow _ (diagramWeight_eq_of_fitsRanks h ▸ rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla))
@[simp ←] lemma schur_map : schur κ (z · |>.map φ) = (schur κ z).map φ := sEqE (by simpa [rowSubst, map_bind₁] using congr(map (φ : R →+* S) $(sum_schur_smul_nablaBasis h z ·)))
lemma map_schur i j : φ (schur κ z i j) = schur κ (fun τ ↦ of (φ <| z τ · ·)) i j := schur_map h z φ ▸ rfl
@[simp ←] lemma schur_mul_left (g : ∀ τ, Matrix (n' τ) (n' τ) R) : (schur κ fun τ ↦ g τ * z τ) = schur κ g * schur κ z := sEqE fun _ ↦ by simpa [h, -C_mul'] using sum_comm
lemma schur_mul_right : schur κ (fun τ ↦ z τ * g τ) = (∏ τ, (g τ).det ^ schurDetExp n n' κ τ) • (schur κ z * schur κ g) := sEqE
 fun _ ↦ by simpa [h, -detPow, -C_mul', mul_sum, mul_left_comm] using sum_comm
lemma schur_apply_eq_prod j : schur κ z i j = ∏ τ, schur (fun () ↦ κ τ) (fun _ ↦ z τ) (fun _ ↦ i τ) fun _ ↦ j τ := congrFun₂ (sEqE fun i ↦ by simpa [nablaBasis, rowSubst, -C_mul']
  using! (congr(∏ τ, rename (·.map (mk τ ·.2) id) $(((piUnique _).symm.sum_comp _).trans (sum_schur_smul_nablaBasis (const Unit (h τ)) (fun _ ↦ z τ) fun _ ↦ i τ))))) ..
lemma schur_smul : (schur κ fun τ ↦ t τ • z τ) = (∏ τ, t τ ^ ∑ i ∈ range (rankAt n' τ), i * κ τ i) • schur κ z := by simp [smul_eq_diagonal_mul, schur_mul_left h, sum_range]
end
noncomputable def weylRep {Φ R} [CommRing R] [Fintype Φ] {n : Φ → _} [∀ τ, Fintype (n τ)] κ (e : Φ → ℤ) := MonoidHom.mk ⟨fun g : ∀ τ, GL (n τ) R ↦ (∏ τ, (g τ).det ^ e τ) • schur κ (g · |>.1), by simp⟩ (by simp [mul_zpow, smul_mul_smul])
