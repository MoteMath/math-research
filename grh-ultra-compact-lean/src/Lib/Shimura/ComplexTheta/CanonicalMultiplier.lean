import Lib.Shimura.Uniformisation.LieExponential
noncomputable section
open Complex Finset
variable {V V' ι : Type} [FinComplexSpace V] [FinComplexSpace V'] (B : RealComplexForm V) (b : V →L[ℂ] V) {L}
def canonicalMultiplier x := (Real.pi * I * B.riemannForm (b x) x).exp
def normalizedShift x := (canonicalMultiplier B b x)⁻¹ • B.thetaShift x
attribute [local simp] sum_div exp_sum funext_iff thetaShift_apply exp_neg fieldEq canonicalMultiplier normalizedShift exp_add
lemma thetaShift_prod [Fintype ι] {B : ι → _} {A : ι → V' →L[ℂ] V} {f : ι → _} u : thetaShift (∑ i, pullForm (A i) (B i)) u (∏ i, f i ∘ A i) = ∏ i, thetaShift (B i) (A i u) (f i) ∘ A i := by simp
variable {B : LatticeForm L} {b x y f} (adj : ∀ u w, B.riemannForm (b u) w = B.riemannForm u w - B.riemannForm u (b w))
lemma mem_thetaSpace_iff_normalizedShift : f ∈ B.thetaSpace (canonicalMultiplier B b) ↔ Differentiable ℂ f ∧ ∀ l ∈ L, normalizedShift B b l f = f := .and .rfl (by simp [mul_right_comm])
include adj
lemma isAppellHumbert_canonicalMultiplier (re : ∀ u w, (B u w).re = (B w u).re) (h : ∀ᵉ (l ∈ L) (m ∈ L), ∃ n : ℤ, B.riemannForm (b l) m = n) : IsAppellHumbert B (canonicalMultiplier B b) := by simp [isAppellHumbert_iff, ← exp_add, exp_eq_exp_iff_exists_int]; norm_cast; grind [riemannForm_swap]
lemma IsAppellHumbert.normalizedShift_normalizedShift {χ} (h : IsAppellHumbert B χ) : normalizedShift B b x (normalizedShift B b y f) = B.riemannPhase (b x) y • normalizedShift B b (x + y) f := by simp [riemannForm_swap y, adj y x, h.thetaShift_thetaShift, mul_add, sub_eq_add_neg, two_mul, add_mul]
