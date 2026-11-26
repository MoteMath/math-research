import Lib.GLn.SchurModule.SchurOrthogonality
import Lib.Adelic.CuspForms.Petersson
open MeasureTheory Complex ComplexConjugate Finset Fintype
variable {Φ n} [Fintype Φ] [Fintype n] {κ e N} {l : Φ → @HCParam n 1} (h : IsHCParam κ e l) (w)
attribute [local grind] hcParameter IsHCParam decrPosition
lemma hcParameter_strictAnti {w} : StrictAnti (hcParameter κ e N w) := strictAnti_nat_of_succ_lt (by grind)
lemma isHCParam_hcParameter n [Fintype n] κ e : IsHCParam κ e fun (w : Φ) i ↦ hcParameter κ e (card n) w (equivFin n i) := by simp [IsHCParam, Function.Injective, hcParameter_strictAnti.injective.eq_iff, Fin.val_inj]
lemma hcParameter_eq_of_steps (L : ℕ → ℤ) (hs : ∀ p, p + 1 < N → L p = L (p + 1) + 2 * κ w (p + 1) + 2) {q} (h₀ : q < N) (h : L q = hcParameter κ e N w q) : ∀ p < N, hcParameter κ e N w p = L p := by
 grind [(Nat.rec (by tauto) (by grind) : ∀ p < N, _ = L p - hcParameter κ e N w p)]
lemma highestVector_cyclic (h : ∀ w, (l w).Injective) e (f : _ →ₗ[ℂ] ℂ) u : (∀ x, gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x u) = 0) ∨ (∀ x, f (conjWeylRep κ e (s := 1) x (highestVector κ l)) = 0) → f u = 0 := by
 rintro ⟨⟩ <;> simpa [*, gramForm_highestVector_self, -Fintype.card_pi] using
   schur_orthogonality e f (highestVector κ l) u (highestVector κ l)
include h
lemma IsHCParam.eq_hcParameter i : l w i = hcParameter κ e (card n) w (decrPosition (l w) i) := by
 choose u b H using
   (h w).2; rw [decrPosition, card_bijective (Fin.mk _ <| b ·) (t := Iio ⟨_, b i⟩)] <;> simp [H, hcParameter_strictAnti.lt_iff_gt, ↓bijective_iff_injective_and_card]; intro; grind
lemma IsHCParam.exists_decrPosition_eq {q} (hq : q < card n) : ∃ i, decrPosition (l w) i = q ∧ l w i = hcParameter κ e (card n) w q ∧ ∀ x < l w i, q < #{k | x < l w k} := ((exists_equiv_decrPosition (h w).1).choose.surjective ⟨q, hq⟩).imp (by grind [eq_hcParameter, card_lt_card, ssubset_iff.2 ⟨·, _⟩])
lemma IsHCParam.hasGap c : (l w).HasGap c := ⟨(h w).1, by grind [h.eq_hcParameter], nofun⟩
lemma IsHCParam.lowestKType_eq i : (l w).lowestKType i = e w + diagramWeight (rankAt n) κ (w, decrPosition (l w) i) := by simp [HCParam.lowestKType, paramAddRho, twoRho]; grind [card_lt_add_card_gt_add_one _ i, h.eq_hcParameter]
lemma IsHCParam.gramForm_conjWeylRep_eq_dsCoeff x : gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x (highestVector κ l)) = ∏ w, conj ((l w).dsCoeff (x w)) := by
 choose _ _ using (exists_equiv_decrPosition <| h · |>.1)
 simpa [↓gramForm_apply, ↓star_highestVector, highestVector, *, conjWeylRep, conj_weightMinors.trans weightMinors_transpose.symm, mem_maxCompactU, dsCoeff_of_mem_maxCompactU (h.hasGap _ 0), funext (h.lowestKType_eq _)] using! weylRep_coeff_eq_prod_weightMinors ..
lemma IsHCParam.prod_formalDegree : ∏ w, (l w).formalDegree = card (WeylIndex n κ) := inv_injective (ofReal_injective (by simpa [h.gramForm_conjWeylRep_eq_dsCoeff, h _, ↓dsCoeff_inv (h.hasGap _ 0), formalDegree, Pi.inv_def, ← prod_mul_distrib, conj_mul', ← integral_fintype_prod_eq_prod, ← integral_complex_ofReal, gramForm_highestVector_self] using! (fun v ↦ schur_orthogonality e (gramForm v) v v v) (highestVector κ l)))
