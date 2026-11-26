import Lib.DiscreteSeries.FlenstedJensen.RepresentationDefs
import Lib.General.LinearAlgebra.CommonEigenvectors
open Finset
noncomputable section
section
variable {n} [Fintype n] {M H} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : GlModule n M) {ε} (l ν : @HCParam n ε) (x)
def IsUnitaryCasimirGe (ρ : GlModule n H) := (∀ a b v w, inner ℂ (ρ.E a b v) w = ↑(ε a * ε b) * inner ℂ v (ρ.E b a w)) ∧ ∀ y, l.casimirValue * ‖y‖ ^ 2 ≤ (inner ℂ y (ρ.casimirK 1 y)).re
def HCParam.casimirKValue := ∑ a, ν a * (ν a + twoRho l (ε · = ε ·) a)
namespace GlModule
attribute [scoped simp, scoped grind =] Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
def adTwist (g : GL n ℂ) := mk (ρ.ρ ∘ₗ .mulLeftRight ℂ (g, ↑g⁻¹)) (by simp [← map_bracket, mul_assoc, map_sub])
def word w := (List.map ρ.E.uncurry w).prod
variable (ε)
def filtration
 | 0 => sInf {W | x ∈ W ∧ ∀ a b, ε a = ε b → W ∈ (ρ.E a b).invtSubmodule}
 | s + 1 => filtration s ⊔ ⨆ (a) (b), (filtration s).map (ρ.E a b)
open Matrix Submodule SetLike Module
variable {n : _} [Fintype n] {M : _} [AddCommGroup M] [Module ℂ M] {ε : _} {ρ : GlModule n M} {x : _} {y s} (hy : y ∈ ρ.filtration ε x s) {a b} {c : ℂ}
lemma mSMS c d : ρ (single a b 1 * single c d 1) = ite (b = c) (ρ.E a d) 0 := by aesop
lemma apply_eq_sum X : ρ X = ∑ a, ∑ b, X a b • ρ.E a b := by simp [← map_smul, ← map_sum, ← matrix_eq_sum_single]
lemma aaB X Y : ρ X (ρ Y x) = ρ Y (ρ X x) + ρ (X * Y - Y * X) x := by simp [map_bracket]
lemma cES (f : _ → _ → ℂ) {D} : ε a = ε b → Commute (ρ.E a b) D → Commute (ρ.E a b) (∑ c, ∑ d, f (ε c) (ε d) • (ρ.E c d * D * ρ.E d c)) := by simp_all [ρ.aaB (single a b _), commute_iff_eq, DFunLike.ext_iff, mSMS, add_assoc, DFunLike.ite_apply, apply_ite (_ : End ..), smul_sub]
lemma cECK : ε a = ε b → Commute (ρ.E a b) (ρ.casimirK ε) := by simpa [casimir, sum_filter] using (ρ.cES (diagonal 1) · (.one_right _))
lemma casimirK_one_adTwist g : (ρ.adTwist g).casimirK 1 = ρ.casimirK 1 := by
 simp [casimir, adTwist, E, ρ.apply_eq_sum (_ * _), mul_apply, single, ite_and, smul_smul, sum_mul_sum, mul_right_comm _ _ (_ * _)]; conv_lhs => repeat rw [sum_comm_cycle]; enter [2, _]
 simp [mul_left_comm, ← sum_smul, ← mul_sum, ← sum_mul, ← mul_apply]
lemma filtration_mono : Monotone (ρ.filtration ε x) := monotone_nat_of_le_succ (by simp!)
lemma self_mem_filtration : x ∈ ρ.filtration ε x s := filtration_mono bot_le (by simp_all!)
include hy
@[local simp] lemma eMFS : ρ.E a b y ∈ ρ.filtration ε x (s + 1) := mem_sup_right (by grw [← le_iSup₂]; tauto)
lemma E_mem_filtration (h : ε a = ε b) : ρ.E a b y ∈ ρ.filtration ε x s := by induction s generalizing y; grind [filtration, mem_sInf]; apply mem_comap.1 (IsConcreteLE.le_iff.1 (sup_le _ (iSup₂_le _)) hy) <;> simp [IsConcreteLE.le_iff, ρ.aaB (single a b _), mSMS] <;> aesop
omit hy
lemma cKMF (hy : y ∈ ρ.filtration ε x 0) : ρ.casimirK ε x = c • x → ρ.casimirK ε y = c • y := (mem_sInf.1 hy (LinearMap.eqLocus _ (c • 1)) ⟨·, by simp_all [← End.mul_apply _, ← (cECK ..).eq]⟩)
def generatedBy x := ρ.restrictTo (ρ.filtration 1 x 0) (by simp_all [ρ.apply_eq_sum ·, ← sum_product', sum_smul_mem, E_mem_filtration])
lemma casimirK_generatedBy (h : ρ.casimirK 1 x = c • x) y : (ρ.generatedBy x).casimirK 1 y = c • y := by ext1; simpa [casimir] using! cKMF y.2 h
end GlModule
open Fintype
variable {n : _} [Fintype n] {ε l : _} {h h'} (hg : @HasGap n _ ε l h) (r) [@DecidableRel n n r] (i)
attribute [grind norm] Pi.top_apply Prop.top_eq_true
attribute [local grind] twoRho HasGap Pi.neg_def
lemma abs_twoRho_le l : |twoRho l r i| ≤ card n := by grind
lemma twoRho_neg l : twoRho (-l) r i = -twoRho l r i := by simp [twoRho]
lemma card_lt_add_card_gt_add_one {l : n → ℤ} (h : l.Injective) i : #{j | l j < l i} + #{j | l i < l j} + 1 = card n := by rw [← card_union_of_disjoint, ← @card_insert_of_notMem _ _ i, card_eq_iff_eq_univ] <;> grind [disjoint_left]
include hg
lemma two_mul_paramAddRho : 2 * paramAddRho l i = l i + twoRho l ⊤ i := by grind [paramAddRho, card_lt_add_card_gt_add_one _ i]
@[local grind .] lemma two_mul_lowestKType : 2 * l.lowestKType i = l i + twoRho l (ε · ≠ ε ·) i - twoRho l (ε · = ε ·) i := by simp [lowestKType, twoRho, filter_and, filter_not, sdiff_inter_right_comm]; grind [two_mul_paramAddRho]
lemma abs_lowestKType_le {L : ℕ} (hL : ∀ a, |l a| ≤ L) a : |l.lowestKType a| ≤ ↑(L + card n) := by grind
lemma HCParam.HasGap.mono : h' ≤ h → l.HasGap h' := by grind
lemma HCParam.HasGap.signs_one : l.compactForm.HasGap h := ⟨hg.1, hg.2, by simp⟩
lemma HCParam.HasGap.neg : (-l).HasGap h := by grind [Function.Injective]
@[simp] lemma lowestKType_neg : (-l).lowestKType = -l.lowestKType := by grind [hg.neg, twoRho_neg]
end
open Complex InnerProductSpace GlModule
variable {n H M} [Fintype n] [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε ν x g} {l : HCParam ε} {ρ : GlModule n H} (h : IsUnitaryCasimirGe l ρ) [AddCommGroup M] [Module ℂ M] {σ : GlModule n M} (r) [DecidableRel r]
lemma HCParam.IsKHighest.of_E_eq_smul : (∀ a b, ε a = ε b → l b ≤ l a → σ.E a b x = ite (a = b) (ν a : ℂ) 0 • x) → l.IsKHighest σ ν x := by grind [IsKHighest, zero_smul]
lemma GlModule.cD2R (hl : l.Injective) (s : Std.Symm r := by tauto) : σ.casimir r = 2 * σ.casimir (r ⊓ (l · < l ·)) + σ.casimir (Eq ⊓ r) + ∑ a, (twoRho l r a : ℂ) • σ.E a a := sub_eq_zero.1 (by
  simp [casimir, twoRho, sum_filter, ← sum_boole, ← sum_sub_distrib, sub_smul, sum_smul, two_mul, ← sum_add_distrib, ← sum_product']
  apply sum_ninvolution .swap <;> grind [mSMS, (σ.map_bracket · · |>.symm), s.1])
attribute [local simp] HCParam.casimirKValue HCParam.IsKHighest filter_and filter_eq smul_smul sum_smul
lemma HCParam.IsKHighest.casimirK_eq_smul [hg : l.HasGap g] (hx : l.IsKHighest σ ν x) : σ.casimirK ε x = (l.casimirKValue ν : ℂ) • x := by simp_all [↓cD2R (ε · = ε ·) hg.1, casimir, sum_eq_zero, mul_add, add_smul, mul_comm]
include h
lemma IsUnitaryCasimirGe.inC : ⟪x, ρ.casimir r x⟫_ℂ = ∑ a, ∑ b with r a b, (ε a * ε b).1 * ‖ρ.E b a x‖ ^ 2 := by simp [casimir, ← inner_conj_symm x, sum_inner, h.1]
lemma HCParam.IsKHighest.cBnd [hg : l.HasGap g] (hw : l.IsKHighest ρ (l.lowestKType + ν) x) (o : x ≠ 0) : 0 ≤ ∑ a, (Fintype.card n ^ 2 + ν a * (ν a + l a)) := by obtain ⟨k⟩ := h.2 x, congr(re ⟪x, $(ρ.cD2R (ε · ≠ ε ·) hg.neg.1) x + $(hw.casimirK_eq_smul)⟫_ℂ); simp_all [h.inC, ← sum_add_distrib, sum_filter_not_add_sum_filter, casimirValue, add_assoc, ← ofReal_pow, ← add_mul, two_mul, ← sum_smul]; grw [sum_nonpos (by simp_all [sum_nonpos, Int.units_ne_iff_eq_neg])] at k; simp_all [-sum_add_distrib]; rify; grw [sub_nonneg.2 k, ← sum_sub_distrib]; gcongr with a; field; norm_cast; grw [(sq_abs _).ge, abs_twoRho_le, twoRho_neg, ← sub_eq_iff_comm.1 (two_mul_lowestKType hg _).symm]; grind [sq_nonneg (l a - 2 * l.lowestKType a)]
end
section
open Pi Submodule Module GlModule LinearMap End
variable {n} [Fintype n] {H} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε} {l : HCParam ε} {ρ : GlModule n H} {ν x s g} (hx : l.IsKHighest ρ ν x) [hg : l.HasGap g]
noncomputable def wWt (ν : n → ℤ) := List.foldr (fun (a, b) ↦ (· + (single a 1 - single b 1))) ν
attribute [local simp] word wWt mSMS add_smul HCParam.IsKHighest hasEigenvalue_iff Submodule.eq_bot_iff
local add_aesop_rules 1% (by rw [aaB])
lemma HCParam.exHV (W : Submodule ℂ H) [Module.Finite ℂ W] (h0 : W ≠ ⊥) (hW : ∀ a b, ε a = ε b → W ∈ (ρ.E a b).invtSubmodule) : ∃ μ : n → ℂ, ∃ v ∈ W, v ≠ 0 ∧ (∀ a, ρ.E a a v = μ a • v) ∧ ρ.IsCompactPrimitive l v := ({μ | _}.exists_max_image ((↑) ∘ l ⬝ᵥ · |>.re) (.subset (.pi' (finite_hasEigenvalue <| restrict _ <| hW · _ rfl)) (by simp; bound))
  (.right (exists_eigenvector_of_commute _ (hW · _ rfl) (by aesop) (U := ⊥) (.symm (by aesop))))).imp fun μ ⟨⟨v, h⟩, H⟩ ↦ ⟨v, by simpa [h] using fun a b e f ↦ not_imp_comm.1 (H (μ + (single a 1 - single b 1)) ⟨_, by tauto, ·, by aesop⟩) (by simpa)⟩
include hx
lemma HCParam.IsKHighest.eWW w a : ρ.E a a (ρ.word w x) = (wWt ν w a : ℂ) • ρ.word w x ∧
 |wWt ν w a - ν a| ≤ w.length := by
 induction w <;> constructor <;> [aesop; aesop; aesop; (simp_all; grind)]
include hg
lemma HCParam.IsKHighest.fLWM : let Q T := ∀ a b, ε a = ε b → l a < l b → T ∈ (ρ.E a b).invtSubmodule
 ∀ T, Q T → (∀ w, w.length ≤ s → ρ.word w x ∈ T) → ρ.filtration ε x s ≤ T := by
 intro Q T o g; have k r {T} : Q T → Q ((pi (Prod.map ε ε ⁻¹' r) fun _ ↦ T).comap (.pi ρ.E.uncurry)) := by aesop
 induction' s with s i generalizing T
 apply sInf_le_of_le _ (sInf_le (s := {T | Q T ∧ x ∈ T}) (by simp_all))
 simpa using fun a b e y u T o t ↦ u _ (k (.diagonal _) o)
  (by simp_all; grind [smul_mem, zero_mem, HasGap]) (a, b) e
 simp! [map_le_iff_le_comap]; use by grind, fun a b _ ↦ (i _ (k ⊤ o) (fun w e p _ ↦ g (w.cons p) (by simpa)) · (a, b) ⟨⟩)
lemma HCParam.IsKHighest.finite_filtration (h : IsUnitaryCasimirGe l ρ) s : Module.Finite ℂ (ρ.filtration ε x s) := s.rec (.of_fg ((fg_span ((((List.finite_length_le _ (l ⬝ᵥ (ν + ν + l) + l.casimirKValue ν).toNat).image (ρ.word · x)).insert 0).subset (by
  rintro _ ⟨m, w, _, rfl⟩; by_contra
  obtain ⟨_, t⟩ := dotProduct_self_star_nonneg (l + wWt ν w), (sum_le_sum fun a _ ↦ single_le_sum (a := a) (by aesop) (by simp)).trans congr($(cKMF m
    hx.casimirK_eq_smul ▸ h.inC _).re).ge
  simp_all [star_trivial, hx.eWW, norm_smul, mul_pow, ← sum_mul, ← Complex.ofReal_pow, -word]
  simp_all [dotProduct]; norm_cast at t; grind : ↑(ρ.filtration ε x 0) ∩ (ρ.word · x) ''
  {w | w.length ≤ l ⬝ᵥ (ν - wWt ν w)} ⊆ _))).of_le (hx.fLWM _ (fun a b e
  c ↦ mapsTo_span fun _ ⟨t, w, _⟩ ↦ ⟨E_mem_filtration t e, w.cons (a, b), by simp_all; lia⟩)
  fun | [], _ => subset_span ⟨self_mem_filtration, [], by simp⟩))) fun _ _ ↦ finite_sup ..
end
