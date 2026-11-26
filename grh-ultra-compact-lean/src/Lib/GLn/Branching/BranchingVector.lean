import Lib.GLn.SchurModule.RationalRep
import Lib.General.LinearAlgebra.SubmersionZero
import Lib.Adelic.Witt.FrameAction
import Lib.General.LinearAlgebra.ExpSurjective
open MvPolynomial Finset Matrix
section
variable {Φ R} [CommRing R] [Fintype Φ] {n n' : Φ → _} {κ} [∀ τ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] (e : ∀ τ, n τ ≃ Fin (rankAt n τ)) (i : WeylIndexFam n κ)
open PolyRep Equiv Fintype
attribute [local simp] tableauWeight rowSubst permArray weylEval minor tableauPoly Finsupp.single_apply ite_and RingHom.map_det highestPoly AlgHom.map_det Matrix.map diagramWeight sum_card_fiberwise_eq_card_filter Fin.val_inj weylKernel
lemma tableau_col_injective τ h j : ((i τ).1 h j).Injective := fun _ _ _ ↦
 by_contra ((@linearIndependent_nablaBasis _ ℤ).ne_zero i <| by simpa [nablaBasis, prod_eq_zero_iff] using ⟨τ, h, j, det_zero_of_row_eq · (by aesop)⟩)
omit [Fintype Φ] in
lemma sum_tableauWeight τ : ∑ a, tableauWeight i τ a = ∑ h ∈ range (rankAt n τ), h * κ τ h := by simp [sum_comm, sum_range, mul_comm]
lemma sum_tableauWeight_le τ A : A.sum (tableauWeight i τ ·) ≤ (range #A).sum (diagramWeight (rankAt n) κ ⟨τ, ·⟩) ∧ (∑ x ∈ range #A, (diagramWeight (rankAt n) κ) (τ, x) ≤ A.sum (tableauWeight i τ ·) → ∀ h j s, h.1 ≤ #A → (i τ).1 h j s ∈ A) := by
 have c (p : Σ h, Fin (κ ..)) := le_min (card_le_card_of_injOn (t := A) _ (mem_filter_univ · |>.1) (tableau_col_injective i τ _ p.2).injOn) (card_le_univ _)
 simpa [-mem_range, mul_comm, Fintype.sum_sigma, sum_range (n := rankAt ..), sum_comm] using And.intro (sum_mono c) fun e h j s _ ↦ card_filter_eq_iff.1
  (congr($((Pi.le_def.2 c).eq_of_not_lt ((sum_strictMono ·).mt e)) ⟨h, j⟩).trans (by simpa)) s
omit [Fintype Φ] [∀ τ, Fintype (n' τ)] in
lemma PolyRep.eRS z y f : eval y (@rowSubst Φ R _ n n' _ z f) = eval (fun x ↦ ∑ a, z _ x.1.2 a * y (⟨_, a⟩, x.2)) f := (aeval_bind₁ ..).trans (by simp)
lemma schur_mulVec_weylEval (h : FitsRanks n n' κ) z y : (detPow R n (schurDetExp n n' κ)).eval y • schur κ z *ᵥ weylEval n κ y = weylEval n' κ fun x ↦ ∑ a, z _ x.1.2 a * y (⟨_, a⟩, x.2) := funext (by simpa [↓PolyRep.eRS, mulVec_apply_eq_sum, mul_sum, mul_rotate'] using congr(eval y $(sum_schur_smul_nablaBasis h _ ·)))
lemma schur_mulVec_weylEval_of_detExp_zero (h : FitsRanks n n' κ) (d : schurDetExp n n' κ = 0) z (y : _ → R) : schur κ z *ᵥ weylEval n κ y = weylEval n' κ fun x ↦ ∑ a, z _ x.1.2 a * y (⟨_, a⟩, x.2) := by simp [← schur_mulVec_weylEval, *]
lemma wkNF y : weylKernel n κ y ∈ nablaFam R n κ := rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla
lemma PolyRep.eWKP : (weylKernel n κ (permArray e)).eval (permArray e) = (1 : R) := by simp [reindex_equiv (e _).symm, ← diagonal.eq_1]
lemma mNBW (φ : _ →ₗ[R] R) (h : φ (nablaBasis R n κ i) ≠ 0 → ∀ τ a, diagramWeight (rankAt n) κ (τ, e τ a) ≤ tableauWeight i τ a) : φ (nablaBasis R n κ i) = φ (weylKernel n κ (permArray e)) * weylEval n κ (permArray e) i := by
 by_cases! p : ∀ τ h j s, e τ ((i τ).1 h j s) < h; rw [mul_comm, ← smul_eq_mul, ← map_smul]
 simp [nablaBasis, ← C_mul', ← prod_mul_distrib, ← det_mul, -prod_const]; congr!; ext; rw [mul_apply, sum_eq_ite ⟨_, p ..⟩] <;> aesop
 choose τ k j s p using p; convert (mul_zero _).symm; by_contra; simpa [p.not_gt] using (sum_tableauWeight_le i τ ((Iio k).map (e τ).symm)).2 (by
  grw [← h ‹_›]; simp [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio]) _ j s
 simp [nablaBasis]; repeat apply prod_eq_zero (mem_univ ‹_›)
 grind only [det_eq_zero_of_row_eq_zero s, of_apply]
lemma schur_one_row_eq_symPowMatrix {a m σ} [Fintype m] [Fintype σ] {k} (q : σ ≃ m) (h : 1 < card m) (hκ : ∀ i > 0, i < card m → k i = ite (i = 1) a 0) : ∃ φ : _ ≃ _, ∀ (c : ℂ) z i j, c ^ a * schur (fun () ↦ k) (fun _ ↦ z) i j = symPowMatrix a (c • zᵀ.submatrix q q) (φ j) (φ i) := by
  have s : ∑ h ∈ range (card m), h * k h = a := by grind [sum_eq_ite 1]
  choose φ B using fun i ↦ (⟨⟨∑ h, ∑ j, ∑ s, .single (q.symm ((i ()).1 h j s)) 1, by
    simp [@sum_comm _ _ σ, ← s, sum_range, mul_comm]⟩, by
    simp [nablaBasis, monomial_sum_one, ← X.eq_1]; congr! with ⟨_ | _ | _⟩ <;> simp [univ_eq_empty]
    grind [Fin]⟩ : ∃ d : Monomials σ a, nablaBasis ℂ m (fun () ↦ k) i = bind₁ (X ⟨⟨(), q ·⟩, 0⟩) (monomial d 1))
  have e : φ.Bijective := ⟨fun i j c ↦ (@linearIndependent_nablaBasis _ ℂ).injective (by grind), fun ⟨d, _⟩ ↦ Function.mtr (by simp_all [Subtype.ext_iff, rename_bind₁])
      congr((rename (q.symm ·.1.2) $(scNB (show bind₁ (X ⟨⟨(), q ·⟩, 0⟩) (monomial d 1) ∈ nablaFam ℂ m fun () ↦ k by
      simp_all [mem_nabla, monomial_eq, borelMul, mul_pow, prod_pow_eq_pow_sum]
      rw [sum_eq_ite 1] <;> simp_all <;> grind))).coeff d)⟩
  use .ofBijective φ e, fun c z ↦ congrFun₂ (.trans (funext₂ (by simp [schur_smul, s])) (sEqE (z := fun () ↦ c • z) (by simpa [*, monomial_eq, reindex_equiv q, ↓← e.sum_comp, symPowMatrix, linSubst] using congr(bind₁ _ $(sum_monomials_eq_of_isHomogeneous <| φ · |>.isHomogeneous_linSubst _)))))
open Finsupp Nat RingHom
variable {Φ : _} [Fintype Φ] {κ : Φ → ℕ → ℕ} {N L}
@[simp] lemma hookNumber_pos : 0 < hookNumber κ N := (fockPairing_star_self_pos (ne_of_apply_ne (eval (permArray fun _ ↦ (↑))) (by simp [highestPoly, tableauPoly, minor, map_det, Matrix.map, permArray, Fin.val_inj, ← diagonal.eq_1]))).trans_eq (congr (by simp) rfl)
@[simp] lemma hookNumber_ne_zero : hookNumber κ N ≠ 0 := hookNumber_pos.ne'
lemma hookNumber_le (h : ∑ τ, ∑ h ∈ range (N τ), h * κ τ h ≤ L) : hookNumber κ N ≤ (L ^ L) ^ 3 := by
 have k := (le_of_dvd (by grind) <| @prod_factorial_dvd_factorial_sum · · ·)
 simp_rw [hookNumber, highestPoly, tableauPoly, minor, det_apply, prod_univ_sum, prod_smul, of_apply, X, ← monomial_sum_one, LinearMap.map_sum₂, map_sum, smul_monomial, fockPairing_monomial, coeff_monomial, prod, mul_ite_zero]; grw [ite_le_sup, le_abs_self (_ • _ * _), k]; simp [↓← degree_apply, -prod_const, -cast_prod, Fintype.card_perm, Units.smul_def, abs_prod]; repeat grw [k]
 grw [← cast_pow, ← factorial_le_pow, ← h]; simp [sum_range, pow_succ, mul_comm]
end
section
seal Finset.univ Finset.sum Finset.prod
open Module PolyRep ComplexOrder Sigma Function Fintype Equiv
variable {Φ R S} [CommRing R] [CommRing S] [Fintype Φ] {n n'} [∀ τ : Φ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] {κ} (e : ∀ τ, n τ ≃ Fin (rankAt n τ)) (φ : R →+* S) (N) (ι : ∀ τ, n τ ⊕ Unit ≃ n' τ) (g : ∀ τ, Matrix (n τ) (n τ) R) (ξ η s : _ → R) (y : (Σ τ, n τ) × ℕ → R) (h : FitsRanks n n' κ) (z : ∀ τ, Matrix (n' τ) (n τ) R)
attribute [local simp] comp_def weylEval Fin.val_inj ite_and permArray Matrix.mul_apply mul_sum minor linearCombination_apply dotProduct Matrix.map mulVec RingHom.map_det detPow tableauPoly AlgHom.map_det
namespace PolyRep
def squarePart τ := of (y ⟨⟨τ, ·⟩, e τ ·⟩)
lemma schur_squarePart_mulVec : schur κ (squarePart e y) *ᵥ weylEval n κ (permArray e) = weylEval n κ y := by simp [funext_iff, ↓schur_mulVec_weylEval_of_detExp_zero, nablaBasis, squarePart, -Fin.val_castLE, ← Fin.val_castLE Fin.is_le', ← eq_symm_apply]
lemma ext_weylEval [IsDomain R] {M} [AddCommGroup M] [Module R M] [Free R M] {L L' : _ →ₗ[R] M} {s} e (h : ∀ y ∈ Set.univ.pi fun _ ↦ s, eval y (detPow R n e) ≠ 0 → L (weylEval n κ y) = L' (weylEval n κ y)) (hs : s.Infinite := by exact Set.infinite_univ) : L = L' := by ext i; exact eval_apply_injective R (LinearMap.ext fun φ ↦ (liNB e).eq_coords_of_eq (funext_set _ (by tauto) fun y k ↦ by simpa [← mul_assoc, ← sum_mul, mul_comm _ (φ _), imp_iff_or_not] using (congrArg φ <| pi_eq_sum_univ' (weylEval n κ y) ▸ h y k · :)) i)
lemma mWK : map φ (weylKernel n κ y) = weylKernel n κ (φ ∘ y) := by simp [weylKernel, rowSubst, map_bind₁, ← C_mul']
lemma rsHP : rowSubst (fun τ ↦ of fun i a ↦ y (⟨τ, a⟩, i.1)) (highestPoly R κ N) = ∏ τ, ∏ h ∈ range (N τ), (of fun s t : Fin h ↦ ∑ a, y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det ^ κ τ h := by simp [highestPoly, prod_range, rowSubst]
lemma wkBM b : weylKernel n κ (borelMul fst b y) = ((diagramWeight (rankAt n) κ).prod fun p ↦ (b (p.1, p.2, p.2) ^ ·)) • weylKernel n κ y := have h {y : _ → R} : weylKernel n κ y = eval (C ∘ y) (weylKernel n κ X) := by simp [weylKernel, rsHP, ← C_mul', mul_comm]; congr! 3; apply det_transpose
 by simpa [← C_mul', map_finsuppProd, borelMul, h] using! (mem_nabla.1 (wkNF X) _ (C ∘ b) (C ∘ y))
@[simp ←] lemma eval_toPoly : eval y (toPoly n κ ξ) = weylEval n κ y ⬝ᵥ weylGramOver *ᵥ ξ := by simp [toPoly, mul_comm]
lemma nablaCombination_weylGramOver_mulVec : nablaCombination κ (weylGramOver *ᵥ ξ) = toPoly n κ ξ := rfl
noncomputable def blockScalar τ := ((g τ).fromBlocks 0 0 (diagonal fun _ ↦ s τ)).reindex (ι τ) (ι τ)
@[grind] lemma diagramWeight_eq_succ_add τ i : diagramWeight N κ (τ, i) = diagramWeight N κ (τ, i + 1) + ite (i + 1 < N τ) (κ τ (i + 1)) 0 := by grind [diagramWeight_apply, sum_Ioo_add_eq_sum_Ico, =_ Ico_add_one_left_eq_Ioo, Ico_eq_empty]
lemma rsWK (hg : ∀ τ, (g τ)ᵀ.BlockTriangular (e τ)) : rowSubst g (weylKernel n κ (permArray e)) = (∏ τ, ∏ a, g τ a a ^ diagramWeight (rankAt n) κ (τ, e τ a)) • weylKernel n κ (permArray e) := by
 convert wkBM _ (∏ τ, ∏ a, ∏ b, if · = ⟨τ, e τ a, e τ b⟩ then g τ b a else 1)
 erw [rowSubst_rowSubst]; congr; simp +instances [funext_iff, ← ext_iff, reindex_equiv (e _), borelMul]; tauto; simp [← prod_pow, Finsupp.prod_finsetProd_comm, ← and_assoc, ← Prod.ext_iff (y := (_, _))]; congr!; aesop
include ι
omit [Fintype Φ] in
lemma rAS τ : rankAt n' τ = rankAt n τ + 1 := by simp [← card_congr (ι _)]
end PolyRep
@[simp] lemma tPWE : toPoly n κ (weylEval n κ y) = weylKernel n κ y := by simpa [mWK, toPoly, weylGram, ← eval_map, aeval_def, ← C_mul'] using (congr(mapAlgHom (aeval y) $(congr(∑ i, $(scNB (coord_mem_of_coeff_mem
  (nablaFam ℤ ..).toAddSubgroup 0 rfl (by simp [mem_nabla, aeval_eq_eval₂Hom, ← coeff_map, scNB (wkNF X), mWK, wkBM]) i)) • _).trans (scNB (wkNF X)))))
lemma PolyRep.weylGram_eq_submatrix {Ψ} [Fintype Ψ] κ (p : Φ ≃ Ψ) : weylGram n κ = (weylGram _ _).submatrix (p.piCongrLeft' _) (p.piCongrLeft' _) := let e := Prod.map p.symm.sigmaCongrLeft id
 toLin'.injective (ext_weylEval 0 fun y _ _ ↦ nCI (.trans (tPWE _) (by simpa [toPoly, rowSubst, nablaBasis, e, weylKernel, highestPoly, reindex_equiv p.symm, reindex_equiv (p.piCongrLeft' _).symm] using congr(rename e $(tPWE (y ∘ e))).symm)))
@[simp] lemma map_toPoly : map φ (toPoly n κ ξ) = toPoly n κ (φ ∘ ξ) := by simp [toPoly, ← C_mul']
include h
lemma PolyRep.vecMul_schur_eq_iff {c x} : c ᵥ* schur κ z = x ↔ rowSubst z (nablaCombination κ c) = nablaCombination κ x * detPow R n (schurDetExp n n' κ) := (iRDP.2.comp nCI).eq_iff.symm.trans (by simp [h, vecMul_eq_sum, sum_mul]; rfl)
variable [IsDomain R] [CharZero R]
@[simp] lemma toPoly_schur z ξ : toPoly n' κ (schur κ z *ᵥ ξ) = rowSubst (fun τ ↦ (z τ)ᵀ) (toPoly n κ ξ * detPow R n (schurDetExp n n' κ)) := congr($((ext_weylEval (schurDetExp n n' κ) fun y _ k ↦ (smul_right_inj k).1 (by
 simp [← map_smul, -map_mul, -detPow, schur_mulVec_weylEval h, weylKernel, mul_comm (z ..)]
 erw [← rowSubst_rowSubst, rsHP]; congr
 simp [rsHP, ← C_mul', ← prod_mul_distrib]; congr with τ
 rw [← prod_range_mul_prod_Ico _ (h _).1, schurDetExp, mul_left_comm, ← mul_pow, ← det_transpose, ← det_mul, (Ico ..).prod_eq_ite (rankAt n τ) (by simp_all [FitsRanks, lt_of_le_of_ne'])]
 simp [-det_mul, reindex_equiv (rowPos n τ).symm]; rfl) : toPoly .. ∘ₗ toLin' _ = (rowSubst fun τ ↦ (z τ)ᵀ).toLinearMap ∘ₗ .mulRight .. ∘ₗ _)) ξ)
omit h
@[simp] lemma fockPairing_toPoly_nablaBasis k : fockPairing R (toPoly n κ ξ) (nablaBasis R n κ k) = hookNumber κ (rankAt n) * ξ k := by
 have H j := mNBW (rowPos n) j (fockPairing R (weylKernel n κ (permArray (rowPos n)))) fun k τ a ↦ by
  have := fockPairing_rowSubst (fun _ ↦ diagonal (if mk _ · = ⟨τ, a⟩ then 2 else 1))
   (weylKernel n κ (permArray (rowPos n))) (nablaBasis R n κ j)
  simp_all [rsWK, schur_diagonal, diagonal_apply]; norm_cast at *; simp_all
 erw [fockPairing_rowSubst, rowSubst_rowSubst] at H; simp [rowSubst, ← eq_symm_apply] at H; exact congr($((ext_weylEval 0 fun y _ ↦ schur_squarePart_mulVec (rowPos n) y ▸ by simp [fockPairing_rowSubst, H, hookNumber, map_fockPairing, -eq_intCast, mul_left_comm] : (fockPairing _).flip _ ∘ₗ toPoly .. = algebraMap ℤ R _ • .proj k)) ξ)
@[simp] lemma fockPairing_toPoly_toPoly : fockPairing R (toPoly n κ ξ) (toPoly n κ η) = hookNumber κ (rankAt n) * ξ ⬝ᵥ weylGramOver *ᵥ η := by simp [← nablaCombination_weylGramOver_mulVec η, mul_rotate']
lemma weylGram_isSymm : (weylGram n κ).IsSymm := .ext fun i j ↦ by simpa using (fPC ..).trans (fockPairing_toPoly_toPoly (Pi.single i 1) (Pi.single j (1 : ℤ)))
lemma weylGram_mul_fockPairing : weylGram n κ * (of fun i j ↦ fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)) = hookNumber κ (rankAt n) • 1 := ext (by simpa [-zsmul_eq_mul, toPoly, weylGram_isSymm.apply, eq_comm] using fockPairing_toPoly_nablaBasis <| Pi.single · (1 : ℤ))
lemma weylGram_mul_schur : weylGramOver * schur κ g = (schur κ fun τ ↦ (g τ)ᵀ)ᵀ * weylGramOver := .symm <| ext_iff_mulVec.2 (by simp [← mulVec_mulVec, mulVec_transpose, vecMul_schur_eq_iff, ↓nablaCombination_weylGramOver_mulVec, -Matrix.map])
lemma tPI : Injective (toPoly (R := R) n κ) := .of_comp (f := (fockPairing R · ∘ nablaBasis R n κ)) fun _ ↦ by simp [funext_iff]
lemma weylGram_posDef : (weylGramOver : Matrix (WeylIndexFam n κ) _ ℂ).PosDef := .of_dotProduct_mulVec_pos (.ext (by simp [weylGram_isSymm.apply])) fun ξ h ↦ by simpa [-mul_sum] using fockPairing_star_self_pos ((map_ne_zero_iff _ tPI).2 h)
lemma range_toPoly : (toPoly n κ).range = nablaFam ℂ n κ := ((toLinearEquiv' _ weylGram_posDef.isUnit.invertible).range_comp _).trans sNB
end
section
open Complex ComplexOrder Norms.L2Operator NormedSpace ComplexStarModule
section
variable {Φ R} [CommRing R] [Fintype Φ] {n} [∀ τ : Φ, Fintype (n τ)] {κ} (ξ : WeylIndexFam n κ → ℂ)
noncomputable def weylNormSq := (star ξ ⬝ᵥ (weylGram n κ).map (↑) *ᵥ ξ).re
@[simp] lemma weylNormSq_nonneg : 0 ≤ weylNormSq ξ := weylGram_posDef.posSemidef.re_dotProduct_nonneg ξ
lemma weylNormSq_smul (t : ℂ) : weylNormSq (t • ξ) = ‖t‖ ^ 2 * weylNormSq ξ := by simp [weylNormSq, ← mul_assoc, mul_conj', sq]
@[simp] lemma weylNormSq_comp_smul {F} [FunLike F ℂ ℂ] [MulHomClass F ℂ ℂ] (σ : F) t : weylNormSq (σ ∘ (t • ξ)) = ‖σ t‖ ^ 2 * weylNormSq (σ ∘ ξ) := by convert weylNormSq_smul ..; aesop
namespace PolyRep
lemma aEM {P} : AnalyticOnNhd ℂ (@evalMat Φ ℂ _ n · P) ⊤ := .eval_linearMap ⟨⟨_, by tauto⟩, by tauto⟩ P
lemma zariski_dense_unitary x P (h : ∀ g, (∀ τ, (g τ)ᴴ * g τ = 1) → @evalMat Φ ℂ _ n g P = 0) : evalMat x P = 0 := eq_zero_of_submersion aEM hasStrictFDerivAt_exp_zero
 (by bound) (.of_forall fun x ↦ by simpa [smul_smul, realPart_add_I_smul_imaginaryPart] using congrFun ((aEM.comp (fun _ _ ↦ .comp
 (exp_analytic _) (f := I • (· • (-ℜ x).1 + ℑ x)) (by fun_prop)) (by simp)).eq_of_frequently_eq
 analyticOnNhd_const (((hasDerivAt_id 0).ofReal_comp.tendsto_nhdsNE one_ne_zero).frequently (.of_forall fun t ↦ h _ (congrFun (selfAdjoint.expUnitary (t • -ℜ x + ℑ x)).2.1)))) I) x
lemma posDef_cauchy_schwarz {ι} [Fintype ι] {M} (h : PosDef M) (x : ι → ℂ) y : ‖star x ⬝ᵥ M *ᵥ y‖ ^ 2 ≤ (star y ⬝ᵥ M *ᵥ y).re * (star x ⬝ᵥ M *ᵥ x).re := by simpa only [dotProduct_comm, norm_inner_symm, sq] using! (@inner_mul_inner_self_le _ _ _ (_) (M.toInnerProductSpace h.posSemidef) y x)
lemma coe_weylNormSq : weylNormSq ξ = star ξ ⬝ᵥ weylGramOver *ᵥ ξ := Complex.ext rfl (weylGram_posDef.posSemidef.dotProduct_mulVec_nonneg ξ).2
lemma star_weylEval y : star (weylEval n κ y) = weylEval n κ (star y : _ → ℂ) := by ext; simp [weylEval, map_eval]; rfl
lemma weylNormSq_weylEval_permArray (e : ∀ τ, n τ ≃ Fin (rankAt n τ)) : weylNormSq (weylEval n κ (permArray e)) = 1 := by simpa [weylNormSq, ↓star_weylEval, Pi.star_def, permArray] using! congr(re $(eWKP e))
open Kronecker SetLike
variable {Φ R : Type} [CommRing R] [Fintype Φ] {n : Φ → _} [∀ τ, Fintype (n τ)] {κ : _} {κ'}
attribute [scoped simp] vecMulVec_apply kronecker_mulVec_vec mul_vecMulVec vecMulVec_mul vecMul_transpose vec_dotProduct_vec star_vec vecMulVec_mulVec
attribute [local simp] weylKernel highestPoly tableauPoly mulVec_transpose
variable (R n κ κ') in noncomputable def comulMatrix := of fun (p, q) k ↦ (↑(Function.invFun (nablaCombination (κ + κ')) (nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q) k) : R)
lemma cmWE y : comulMatrix R n κ κ' *ᵥ weylEval n _ y = (vecMulVec (weylEval n _ y) (weylEval n _ y)).vec := _root_.funext fun _ ↦ .trans (by
 simpa using! congr(($(scNB (f := nablaBasis .. * nablaBasis ..) (congr(nabla _
  _ $diagramWeight_add).ge (mul_mem_graded prod_tableauPoly_mem_nabla
  prod_tableauPoly_mem_nabla))).map (algebraMap ℤ R)).eval y)) (mul_comm ..)
variable [IsDomain R] [Infinite R]
lemma vmCM {a b x} : (vecMulVec b a).vec ᵥ* comulMatrix R n κ _ = x ↔ nablaCombination κ a * nablaCombination κ' b = nablaCombination _ x := by simp [← nCI.eq_iff, MvPolynomial.funext_iff, cmWE, ← weylEval.eq_1, Fintype.linearCombination, ← dotProduct.eq_1, ← dotProduct_mulVec]; grind
lemma cmIE (g : ∀ τ, Matrix (n τ) (n τ) R) : let C := comulMatrix R n κ κ'
 Cᵀ * ((weylGram n κ).map (↑) ⊗ₖ (weylGram n κ').map (@Int.cast R _) * C) = weylGramOver ∧ schur κ g ⊗ₖ schur κ' g * C = C * schur (κ + κ') g := by constructor <;> exact toLin'.injective (ext_weylEval 0
 (by simp [cmWE, vmCM, nablaCombination_weylGramOver_mulVec, pow_add, schur_mulVec_weylEval_of_detExp_zero]))
lemma hLCM : HasLeftInv (comulMatrix ℤ n κ κ') := ⟨_, ext_row fun _ ↦ vmCM.2 (by simp [← single_one_vecMul, nablaBasis, Fin.prod_univ_add]; congr <;> exact scNB prod_tableauPoly_mem_nabla)⟩
lemma _root_.weylNormSq_le_mul_of_toPoly_eq {ξ η ζ} (h : toPoly n (κ + κ') ζ = toPoly n κ ξ * toPoly n κ' η) : weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η := let C := comulMatrix ℂ n κ κ'; by
    nlinarith [mul_nonneg (weylNormSq_nonneg ξ) (weylNormSq_nonneg η), by
      simpa [star_mulVec, ← dotProduct_mulVec, by simpa [toPoly, ← vmCM] using h.symm, cmIE 1, ← coe_weylNormSq, (Matrix.ext (by simp [comulMatrix]) : Cᴴ = Cᵀ), C, ↓map_vecMulVec_star, -vecMul_transpose, vecMul_transpose _ ξ] using posDef_cauchy_schwarz
        (weylGram_posDef.kronecker weylGram_posDef) (C *ᵥ ζ) (vecMulVec η ξ).vec]
end PolyRep
end
namespace PolyRep
attribute [-simp] zsmul_eq_mul
variable {Φ : Type} (R : Type) [CommRing R] [Fintype Φ] {n N : Φ → _} [∀ τ, Fintype (n τ)] [∀ τ, Fintype (N τ)] (ι : ∀ τ, n τ ⊕ Unit ≃ N τ) {γ κ' : Φ → ℕ → ℕ}
noncomputable def nRO (i : ∀ _, _) τ := (((((finCongr (rAS ι τ)).trans (finSuccEquiv' (i τ))).trans (rowPos ..).symm.optionCongr).trans (.optionEquivSumPUnit _)).trans (ι τ)).symm
noncomputable def brV γ κ := weylKernel N γ (permArray (nRO ι 0)) * weylKernel
 (R := R) N κ (permArray (nRO ι ⊤))
lemma rowSubst_branchVector s : rowSubst (blockScalar ι 1 s) (brV R ι γ κ') = (∏ τ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) • brV R ι γ κ' := by rw [brV, map_mul, rsWK, rsWK] <;> simp [nRO, blockScalar, rAS ι, reindex_equiv (ι _), diagramWeight_apply, Nat.Ioo_eq_range', BlockTriangular] <;> grind
lemma exSW {κ₀ q} (f : ∀ τ, _ ≃ Fin (rankAt n τ)) (p : ∀ τ a, (rowPos n τ a).1 ≤ f τ a + 1) (hq : ∀ τ, ∀ i < q, κ' τ i = 0) (h₀ : ∀ τ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) : ∃ c : ℤ, 0 < c ∧ (∀ L, ∑ τ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧ ∃ η, c • (weylKernel n γ (permArray f) * weylKernel n κ' (permArray (rowPos n)) : MatrixPoly _ ℤ) = toPoly n κ₀ η := by
  let β τ i := ite (i ∈ Ioo 0 (q ⊓ rankAt n τ)) (γ τ i) 0; obtain ⟨α, rfl⟩ := exists_add_of_le (by aesop_cat : β ≤ κ₀); use hookNumber α (rankAt n), hookNumber_pos, fun _ ↦ hookNumber_le ∘ (sum_le_sum (by simp_all; grind [sum_congr_of_eq_on_inter])).trans; obtain ⟨⟨F, hF⟩, ζ, T⟩ := (by simp [weylKernel, rsHP, prod_sigma']; grind [prod_dvd_prod_of_dvd, pow_dvd_pow] : weylKernel (R := ℤ) n β (permArray f) ∣ weylKernel n γ (permArray f)), ((sNB.ge (congr(nabla ℤ _ $((by grind [=_ diagramWeight_add, diagramWeight_apply, sum_congr, add_comm] : diagramWeight (rankAt n) (β + α) = diagramWeight _ γ + diagramWeight _ κ'))).ge (SetLike.mul_mem_graded (wkNF (R := ℤ) (permArray f)) (wkNF (R := ℤ) (permArray (rowPos n)))))).imp' _ fun c _ ↦ by rw [← nablaCombination_weylGramOver_mulVec, mulVec_mulVec c, ← map_mul_intCast, weylGram_mul_fockPairing]; simp [*, Matrix.map_intCast, ← C_mul'] : ∃ ζ, toPoly n (β + α) ζ = hookNumber (β + α) (rankAt n) • (weylKernel n γ (permArray f) * weylKernel n κ' (permArray (rowPos n)) : MatrixPoly _ ℤ)); obtain ⟨a, Q⟩ : ∃ a, comulMatrix ℤ n β α *ᵥ ζ = (vecMulVec a _).vec := ⟨_, _root_.funext fun ⟨i, i'⟩ ↦ by simpa [← tPWE, mul_assoc] using mNBW f i (fockPairing ℤ (toPoly n β ((comulMatrix ℤ n β α *ᵥ ζ) ⟨·, _⟩))) fun h τ a ↦ by by_contra! o; obtain ⟨E, B⟩ := congr(($((cmIE fun _ ↦ diagonal (2 ^ Finsupp.single (Sigma.mk τ a) 1 ⟨_, ·⟩)).2) *ᵥ ζ) ⟨i, i'⟩), add_lt_add_of_lt_of_le o (sum_tableauWeight_le i' τ {a}).1; rw [← mulVec_mulVec, ← mulVec_mulVec, (tPI (by simp [T, rsWK, smul_smul]; rw [mul_comm]) : _ *ᵥ ζ = (_ : ℤ) • ζ)] at E; simp_all [schur_diagonal, ← pow_add, diagramWeight, ite_and, diagonal_kronecker_diagonal, Finsupp.single_apply, ← sum_add_distrib]; grind [exists_lt_of_sum_lt B, sum_eq_zero.mt o.ne_bot]⟩; have D := by simpa [vmCM, nablaCombination_weylGramOver_mulVec, *, mul_assoc, mulVec_transpose, ← mulVec_mulVec, ← Algebra.mul_smul_comm, ne_zero_of_map (ne_zero_of_eq_one
    (eWKP f))] using congr($((cmIE 1).1) *ᵥ ζ)
  exact hLCM.elim fun L l ↦ ⟨_, by simpa [← Q, smul_comm (hookNumber α _), ← Int.zsmul_eq_mul, T, l, -smul_eq_mul, ← Pi.smul_def] using congr(toPoly _ _ (L *ᵥ (vecMulVec (fockPairing ℤ $D <|
    nablaBasis ℤ n α ·) (weylEval n β (permArray f))).vec))⟩
end PolyRep
end
section
open ComplexOrder Equiv PolyRep RingHom SetLike
variable {Φ} {K : Type} [Field K] [CharZero K] [Fintype Φ] {n} [∀ τ : Φ, Fintype (n τ)] {κ} (e : ∀ τ, n τ ≃ Fin (rankAt n τ))
lemma PolyRep.ext_schur_weylEval {M} [AddCommGroup M] [Module K M] {L L' : _ →ₗ[K] M} (h : ∀ (g : ∀ _, GL _ K) v, v = schur κ (g · |>.1) *ᵥ weylEval n κ (permArray e) → L v = L' v) : L = L' := ext_weylEval 1 fun y _ _ ↦ h
 (fun τ ↦ ((isUnit_submatrix_equiv (rowPos n τ).symm (e τ).symm).1 (by simp_all [detPow, minor, det_apply, isUnit_iff_isUnit_det, prod_eq_zero_iff])).unit) _ (schur_squarePart_mulVec ..).symm
lemma scalar_of_commute_schur {T} (h : ∀ g : ∀ τ, Matrix (n τ) _ ℂ, (∀ τ, (g τ)ᴴ * g τ = 1) → Commute T (schur κ g)) : T ∈ Set.range (scalar _) := by
 let v : _ → ℂ := weylEval n κ (permArray (rowPos n)); have H g i := by
  simpa +contextual [Ring.lie_def, ↓map_mulVec, Matrix.map_sub, (h ..).eq, Function.comp_def, ← mulVec_mulVec] using zariski_dense_unitary (n := n) g ((⁅schur κ (genericMatrixAt ℂ n), T.map C⁆ *ᵥ C ∘ v) i)
 have p i := mNBW (rowPos n) i (fockPairing ℂ (toPoly n κ (T *ᵥ v))) fun k τ a ↦ by
  have := (tPI (by simp [v, rsWK]; rfl) : schur κ (fun σ ↦ diagonal (if σ = τ ∧ · ≍ a then 2 else 1)) *ᵥ v = (_ : ℂ) • v) ▸ congr(‖$(H _ i)‖); simp_all [schur_diagonal, ite_and]
 use ?_, toLin'.injective (ext_schur_weylEval (rowPos n) (by
  simp_all [← funext (H _), -mulVec_mulVec, ← mulVec_smul, v, ← tPWE, mul_assoc]
  rw [funext p]; tauto))
section
attribute [local simp] Fin.val_inj filter_eq' prod_eq_zero_iff squarePart schur_squarePart_mulVec transpose_map transpose_nonsing_inv eq_inv_smul_iff ite_and minor mul_pow weylRep smul_smul
variable {Φ : Type} {n : Φ → Type} [Fintype Φ] [∀ τ : Φ, Fintype (n τ)] {κ κ' : Φ → ℕ → ℕ} (e e' : ∀ τ, n τ ≃ Fin (rankAt n τ)) (he : e' = (e · |>.trans Fin.revPerm)) (hκ : ∀ τ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h))
include he hκ
lemma PolyRep.exDM : ∃ J, ∀ R [CommRing R] g, (∀ τ, @IsUnit R _ (g τ).det) → map J Int.cast *ᵥ schur κ g *ᵥ weylEval n _ (permArray e') = (∏ τ, (g τ).det ^ diagramWeight (rankAt n) κ' (τ, 0)) • (schur κ' fun τ ↦ (g⁻¹ τ)ᵀ) *ᵥ weylEval n _ (permArray e) := by
  let ρ {τ} {h : Fin _} := (Perm.sumCongr 1 Fin.revPerm).trans (finSumFinEquiv.trans ((finCongr (Nat.add_sub_of_le h.is_le')).trans (e τ).symm)); choose π q using fun {τ h} ↦ Perm.exists_smul_eq_embedding (.trans .inl (@ρ τ h).toEmbedding); let D {τ h} I := (π I).sign • minor ℤ (Sigma.mk τ ∘ @π τ h I ∘ @ρ τ h ∘ .inr); constructor; intro R _ g _; ext i; have p p : (@squarePart _ R n _ p).Surjective := (⟨fun (a, k) ↦ ∑ b with p _ b = k, · _ a.2 b, by bound⟩); obtain ⟨⟨y, w⟩, ⟨z, hz⟩, M⟩ := p e' g, p e fun τ ↦ (g⁻¹ τ)ᵀ, (flip cast (by repeat apply_rules [prod_mem_graded, pow_mem_graded, zsmul_mem, minor_mem_nabla] <;> intros) congr(_ ∈ nabla _ _ (∑ _, $((sum_equiv (.neg _) (by simp) (by rintro ⟨⟨⟩⟩ <;> simp [*, Fin.neg_def])).trans (sum_range _).symm))) : ∏ τ, ∏ h, ∏ j, D ⟨_, tableau_col_injective i τ h j⟩ ^ min 1 ↑h ∈ nablaFam ℤ n κ)
  have H τ h I : aeval y (@D τ h I) = (g τ).det * aeval z (minor R (⟨τ, I ·⟩)) := by
    convert congr((π I).sign * $((((squarePart e z τ).submatrix I ρ).fromRows (fromCols 0 1)).det_mul_comm (((g τ)ᵀ.submatrix _root_.id (π I)).submatrix ρ ρ))) using 1
    rw [(?_ : _ * _ = fromBlocks 1 0 _ _ᵀ)]
    any_goals rw [det_mul, det_submatrix_equiv_self, ← (submatrix _ I _).fromCols_toCols]
    any_goals simp [D, -squarePart, det_permute', ← zsmul_eq_mul, AlgHom.map_det, -fromCols_toCols]
    any_goals ext ⟨⟩ ⟨⟩ <;> simp [*, -squarePart, -q, ← DFunLike.congr_fun (q I)] <;> rfl
    all_goals congr 2 with; simp [ρ, mul_apply, ← w, *] <;> grind
  convert congr(aeval y $(scNB M)); simp [← w, aeval_def, ← eval_map]; rfl
  simp [↓← hz, nablaBasis, tableauPoly, H, weylEval, ↓prod_pow_eq_pow_sum, diagramWeight, Finsupp.single_apply, sum_range]; congr with <;> congr with ⟨⟨⟩⟩ <;> simp
lemma exists_dual_isometry : ∃ (J : Matrix ..) (J' : Matrix (WeylIndexFam n κ') (WeylIndexFam n κ) ℤ), J * J' = 1 ∧ J' * J = 1 ∧ Jᵀ * weylGram n κ * J = weylGram n κ' ∧ ∀ R [Field R] [CharZero R], let j := J.map (@Int.cast R _)
  j *ᵥ weylEval n _ (permArray e) = weylEval n κ (permArray e') ∧ ∀ g : ∀ τ, GL (n τ) R, schur κ
    (fun τ ↦ (g τ)⁻¹.1ᵀ) * j = j * weylRep κ' (fun τ ↦ -(Ico 1 (rankAt n τ)).sum (κ τ ·)) g := by
  simp [← (map_injective (algebraMap _ ℂ).injective_int).eq_iff, -algebraMap_int_eq, -Nat.cast_sum]; refine (exDM _ _ he hκ).elim fun K _ ↦ (exDM e' e (by bound) (by grind)).imp fun J H ↦ ⟨K, toLin'.injective (ext_schur_weylEval e' ?_), toLin'.injective (ext_schur_weylEval e ?_), (fun A ↦ ⟨?_, A⟩) fun R ↦ ⟨by simpa using H R 1, fun _ ↦ toLin'.injective (ext_schur_weylEval e ?_)⟩⟩ <;> simp +contextual [*, -he, sum_Ico_reflect, diagramWeight_apply, ← Ico_add_one_left_eq_Ioo, Units.smul_def]
  refine weylGram_posDef.isUnit.dvd.elim fun T q ↦ q.trans ?_
  obtain ⟨_, rfl⟩ := scalar_of_commute_schur (T := T) fun g h ↦ weylGram_posDef.isUnit.mul_left_cancel (by simp [← q, weylGram_mul_schur, det_ne_zero_of_left_inverse (h _), ← transpose_mul, ← fun (g h : ∀ _, _) ↦ by
                     simpa using (A ℂ).2 fun τ ↦ .mk'' (g τ) (h τ), Units.smul_def, Matrix.mul_assoc _ _ (schur _ _), ← Matrix.mul_assoc, mul_assoc])
  simp [← by simpa [← mulVec_mulVec, ← toBilin'_comp, toBilin'_apply', A, eWKP]
    using congr((toBilin' $q).toQuadraticMap (weylEval _ _ (permArray e)))]
end
attribute [local simp ←] Equiv.eq_symm_apply mul_sum coe_weylNormSq rowSubst_branchVector diagonal.eq_1 mulVec_mulVec submatrix_map vecMul_vecMul coe_eval₂Hom coeff_map eval₂_comp monomial_sum_one weylEval.eq_1
attribute [local simp] Fin.top_eq_last prod_eq_zero_iff Function.comp_def blockScalar.eq_unfold squarePart eval_toPoly nablaCombination_weylGramOver_mulVec weylNormSq_weylEval_permArray BlockTriangular fromBlocks_transpose mulVec_transpose Matrix.mul_assoc smul_vecMul vecMul_smul vecMul_sub aeval_def map_det map_dotProduct map_matrix_mul map_mulVec Units.smul_def permArray weylGram_mul_schur diagramWeight_add minor mul_assoc weylRep _root_.zpow_add
variable {n N : Φ → _} [∀ τ, Fintype (n τ)] [∀ τ, Fintype (N τ)] (ι : ∀ τ, n τ ⊕ Unit ≃ N τ) {κ κ₀ : Φ → ℕ → ℕ} (e₀ e : Φ → ℤ) (A : Matrix (WeylIndexFam n κ₀) (WeylIndexFam N κ) ℂ) {γ κ' : Φ → ℕ → ℕ}
def SpansBranchingMaps := ∀ T, (∀ g : ∀ _, GL _ ℂ, (∀ τ, (g τ).1ᴴ * (g τ).1 = 1) → ∃ x, (∀ τ, (x τ).1 = blockScalar ι (g · |>.1) 1 τ) ∧ T * weylRep κ e x = weylRep κ₀ e₀ g * T) → ∃ a : ℂ, T = a • A
open Norms.L2Operator
lemma exists_branching_matrix κ₀ q (e e₀ : Φ → ℤ) (k : γ + κ' = κ) (h₀ : ∀ τ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = κ' τ h + γ τ (h + 1)) (hq : ∀ τ, ∀ i < q, κ' τ i = 0) (h₁ : ∀ τ, e₀ τ = e τ + κ' τ (rankAt n τ)) : ∃ br : Matrix (WeylIndexFam n κ₀) (WeylIndexFam N κ) ℤ, (∀ R [Field R] [CharZero R] g (s : Φ → Rˣ) x, (∀ τ, (x τ).1 = blockScalar ι (g · |>.1) (s · |>.1) τ) → br.map (@Int.cast R _) * weylRep κ e x = (∏ τ, s τ ^ (diagramWeight (rankAt N) γ (τ, 0) + e τ)) • (weylRep κ₀ e₀ g * br.map (@Int.cast R _))) ∧ (∀ L, ∑ τ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → ∀ ξ, weylNormSq (br.map (↑) *ᵥ ξ) ≤ ((L ^ L) ^ 3) ^ 2 * weylNormSq ξ) ∧ SpansBranchingMaps ι e₀ e (br.map (↑)) := by
  obtain ⟨I, rfl, c, hc, hA, η, hη⟩ := (@weylGram_posDef _ _ N _ κ).isUnit.invertible, k, exSW (rowPos n · |>.trans (finRotate _).symm)
    (by simp; grind [Fin.val_sub_one_of_ne_zero]) hq h₀
  let E₀ := nRO ι ⊤; let u₀ τ := of fun a c ↦ ite (a = ι τ (.inr ()) ∨ a = c) (1 : ℂ) 0; let U₀ := ((by constructor <;> simp [funext_iff] <;> grind : IsLinearMap ℂ fun (M : type_of% u₀) τ ↦ of fun a c ↦ ite (E₀ τ a < E₀ τ c) (M τ a c) 0 + ite (a = c) (M τ (ι τ (.inr ())) c - ∑ d with E₀ τ d < E₀ τ c, M τ d c) 0).mk' _).toContinuousLinearMap
  let v₀ := weylEval (R := ℂ) N (γ + κ') (permArray E₀); let v := schur (γ + κ') u₀ *ᵥ v₀; have hv r (h : ∀ g, (∀ τ, (g τ)ᵀ.BlockTriangular (rowPos n τ)) → r ⬝ᵥ schur (γ + κ') (blockScalar ι g 1) *ᵥ v = (0 : ℂ)) : r = 0 := (dotProductEquiv ..).injective (ext_schur_weylEval E₀ fun g ↦ by
    simpa [v] using eq_zero_of_submersion (aEM (P := C ∘ r ⬝ᵥ schur (γ + κ') (genericMatrixAt ℂ _) *ᵥ C ∘ v₀)) (((1 - u₀ • U₀).hasStrictFDerivAt.const_add u₀).fun_mul' (U₀.hasStrictFDerivAt.const_add 1)) (a := 0)
      (by bound) (.of_forall fun M ↦ let g τ := ((1 + M - U₀ M) τ).submatrix (ι τ ∘ .inl) (ι τ ∘ .inl)
      have ⟨l, k⟩ : _ ∧ u₀ + (1 - u₀ • U₀) M = blockScalar ι g 1 * u₀ := .imp_left (h g) (by
        simp [funext_iff, entrywise, reindex_equiv (ι _), u₀, U₀, E₀, nRO, sum_filter, g]; grind-order)
      by simp [↓k, -Pi.smul_apply, l, v, -blockScalar.eq_unfold, schur_mul_left, (tPI (by simpa [v₀] using (rsWK _ _ (by simp [U₀]; grind))) : schur (γ + κ') (1 + U₀ M ·) *ᵥ v₀ = (_ : ℂ) • v₀)]) _)
  let K {S} [CommRing S] x y := eval y (rowSubst (blockScalar ι (fun τ ↦ (squarePart (rowPos n) x τ)ᵀ) 1) (brV S ι γ κ')); let L S [CommRing S] := .mulRight S (detPow S n fun τ ↦ κ' τ (rankAt n τ)) ∘ₗ toPoly n κ₀; have A S T [CommRing S] [CommRing T] (φ : S →+* T) x y : φ (K x y) = K (φ <| x ·) (φ <| y ·) := by simp [K, brV, weylKernel, eRS, reindex_equiv (ι _), map_eval, apply_ite]
  have Z S [CommRing S] b x y : K x _ = _ * K x y := mem_nabla.1 (rowSubst_mem_nabla _ (by apply_rules [mul_mem_graded, wkNF])) S b y; have G {S} [CommRing S] [IsDomain S] [CharZero S] g θ : L S ((∏ τ, (g τ).det ^ κ' τ (rankAt n τ)) • schur _ g *ᵥ θ) = rowSubst (fun τ ↦ (g τ)ᵀ) (L _ θ) := by simp [L]
  have R y (Y : ∀ τ j, y (⟨τ, ι τ (.inr ())⟩, j + 1) = 0) : ∃ θ, ∀ x, eval x (L (MatrixPoly (Sigma N) ℤ) θ) = c * K x y := ⟨(∏ τ, ∏ h ∈ range (rankAt n τ), y (⟨τ, ι τ (.inr ())⟩, 0) ^ γ τ (h + 1)) • _, fun x ↦ by
    rw [map_smul, G (fun τ ↦ of (y ⟨⟨τ, ι τ <| .inl ·⟩, rowPos n τ ·⟩)) (C ∘ η), LinearMap.comp_apply]
    simp [↓← map_toPoly, ← hη, K, brV, weylKernel, rsHP, rAS ι, detPow, eRS, mul_comm _ (x _), prod_range_succ' (_ ^ γ _ ·), prod_range_succ, Matrix.map, -permArray, -finRotate_symm_apply]
    simp [det_succ_row_zero', Fin.sum_univ_succ, reindex_equiv (ι _), nRO, mul_pow, submatrix, Y, -finRotate_symm_apply]
    rw [mul_left_comm]; clear * -; conv_rhs => simp +singlePass [← det_transpose]
    congr! <;> simp +instances (disch := grind) [ite_eq_right, ← Fin.eq_mk_iff_val_eq, Nat.mod_eq_of_lt, Fin.add_def, -finRotate_symm_apply] <;> rfl⟩
  obtain ⟨⟨θ, H⟩, _, s⟩ := R (borelMul (·.1) (fun (τ, i, j) ↦ ite (i = j) 1 (ite (i = 0) (-1) 0) * X (⟨τ, ι τ (.inr ())⟩, j - i)) X) (by simp [borelMul, sum_range_succ', mul_comm]), nabla_le_span_nablaBasis_mul_detPow
    (κ := γ + κ') 0 (x := c • K (C ∘ @X ℤ _ _) X) (by simp [mem_nabla, *, mul_left_comm])
  simp [Z, Int.cast_comm, X_pow_eq_monomial, Finsupp.prod] at H; choose B₀ l using coord_mem_of_coeff_mem (L ℤ).range.toAddSubgroup _ s fun δ ↦ ⟨_, funext fun x ↦ by
    simpa [← map_nablaBasis C, ← map_detPow C, L, weylEval, entrywise, -map_nablaBasis, -map_detPow, A, coeff_sum, mul_comm (eval x _), ← Int.cast_comm, ← zsmul_eq_mul, -Function.comp_def] using! (congrArg (AddMonoidAlgebra.coeff · (_ + δ)) (H (C ∘ x))).trans (coeff_monomial_mul ..)⟩
  let B := (of B₀)ᵀ; have k {T} [CommRing T] y x : eval x (L T (B.map (↑) *ᵥ weylEval N _ y)) = c * K x y := by
    simpa [B, ← eval_map, dotProduct, L, ← l, A, weylEval, mulVec_eq_sum, smul_eq_C_mul, mul_comm (eval y _), Fintype.linearCombination_apply] using congr(eval₂ (aeval x).1 y $s)
  have ha : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀ (permArray (rowPos n))) ᵥ* B.map (↑)) = (c : ℂ) • brV ℂ ι γ κ' := funext fun y ↦ by
    simpa [B, Fintype.linearCombination_apply, K, L, detPow, ← dotProduct.eq_1, dotProduct_mulVec, Fin.val_inj, Matrix.map.eq_1 (of _), vecMul_mulVec, ← transpose_map, weylGram_isSymm.eq] using k y (permArray (rowPos n))
  have he {S} [Field S] [CharZero S] g (s : _ → S) : let b := B.map (@Int.cast S _)
    b * schur (γ + κ') (blockScalar ι g s) = (∏ τ, s τ ^ diagramWeight (rankAt N) γ (τ, 0) * (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * b) := toLin'.injective (ext_weylEval 0 fun y _ _ ↦ tPI (iRDP.2 (funext (by
    simp [schur_mulVec_weylEval_of_detExp_zero, *, mul_smul, eRS (n' := n), K, ← eRS, -blockScalar.eq_unfold, mul_left_comm]
    simp [← smul_eval, ← map_smul, rowSubst_rowSubst, mul_comm (g ..)]
    tauto) : L _ _ = L _ _)))
  set G₀ := weylGramOver (R := ℂ) (n := n); set x := G₀ *ᵥ _; have E := by simpa using (he (S := ℂ) · 1)
  use B, by simp_all [mul_zpow, smul_smul, mul_left_comm], fun A H ξ ↦ ?_, fun T l ↦ ?_
  set T := map B _; have hC := weylGramOver.mul_invOf_cancel_left (Tᵀ * G₀); set C := I.1 * (Tᵀ * G₀); let w := C *ᵥ weylEval n _ (permArray (rowPos n)); trans weylNormSq w * weylNormSq ξ; obtain ⟨⟨m, hm⟩, p, q⟩ := scalar_of_commute_schur (T := T * C) fun g u ↦ by
    simpa [commute_iff_eq, det_ne_zero_of_left_inverse (u _), (weylGramOver.mul_right_injective_of_invertible (by simpa [hC, G₀, ← weylGramOver.mul_assoc] using congr($(E _)ᵀ * G₀)) : schur (γ + κ')
      (blockScalar ι g 1) * C = (_ : ℂ) • C * schur κ₀ g), -blockScalar.eq_unfold]
      using congr($(he g 1) * C), mul_nonneg (weylNormSq_nonneg ξ) (weylNormSq_nonneg w), posDef_cauchy_schwarz weylGram_posDef (C *ᵥ T *ᵥ ξ) ξ
  simp [w, weylNormSq.eq_1 (C *ᵥ _), star_mulVec_dotProduct C, T, mulVec_mulVec _ T, ← hm, by
    simpa [weylGram_posDef.1.eq, transpose_conjTranspose, G₀] using (congr($hCᴴ *ᵥ ·))] at *; nlinarith
  grw [weylNormSq_le_mul_of_toPoly_eq (by
    rw [map_smul, tPWE, tPWE, ← nablaCombination_weylGramOver_mulVec, mulVec_mulVec, hC]
    simpa), weylNormSq_smul, Complex.norm_intCast, hA _ H] <;> simp
  let D {R} [CommRing R] g := mulRightLinearMap _ R (schur (γ + κ') (blockScalar (R := R) ι g 1)) - (∏ τ, (g τ).det ^ κ' τ (rankAt n τ)) • mulLeftLinearMap _ R (schur κ₀ g); have top T (hT : ∀ g, D g T = 0) (h : x ᵥ* T ⬝ᵥ v = 0) : T = 0 :=
    have hT := by simpa [D] using (congr(x ᵥ* $(hT ·)))
    transpose_injective (mul_left_injective_of_inv _ _ weylGram_posDef.isUnit.mul_val_inv (toLin'.injective (ext_schur_weylEval _ fun g ↦ by simpa [mulVec_mulVec _ weylGramOver, (hv (x ᵥ* T) fun g l ↦ by simp [hT, h, dotProduct_mulVec, (by simpa [vecMul_schur_eq_iff, x, G₀] using rsWK _ _ l : x ᵥ* schur _ g = (_ : ℂ) • x)])] using (hT (g · |>.1.transpose)).symm)))
  exact ⟨_, sub_eq_zero.1 (top _ (fun g ↦ by ext; simpa [map_sub, D, E] using (zariski_dense_unitary g (D (genericMatrixAt ℂ _) (T.map C) _ _) fun g u ↦ (l (⟨_, _, mul_eq_one_symm <| u ·, u _⟩) u).elim fun x ⟨y, h⟩ ↦ by simpa [D, h₁, y, det_ne_zero_of_left_inverse (u _)] using congr($h _ _))) (by
    simp [← div_eq_iff (mt (top _ (sub_eq_zero.2 <| E ·)) (by simpa [·, brV, hc.ne', (ne_zero_of_map (ne_zero_of_eq_one (eWKP _)))] using ha.symm))]; rfl))⟩
end
