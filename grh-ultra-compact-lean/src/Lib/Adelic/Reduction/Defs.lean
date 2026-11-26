import Lib.DiscreteSeries.FlenstedJensen.RepresentationDefs
import Lib.Adelic.Reduction.MahlerForms
noncomputable section
open Finset ENNReal Fintype MatMul Matrix MeasureTheory Set Submodule
deriving instance MeasurableMul₂, MeasurableInv for G
attribute [-instance] instSecondCountableTopologySubtypeMem_new
variable {E : Type} {n : Type} [Field.{0} E] [NumberField E] [NumberField.IsCMField E] [Fintype n] {s : n → _}
instance : (@volume (G E s) _).IsHaarMeasure := Measure.prod.instIsHaarMeasure ..
instance : @SFinite (G E s) _ volume := inferInstance
variable {E n : Type} [Field.{0} E] [CMType E] [Fintype n] {s : n → _} in abbrev Space.quotMeasure (V : Space E n s) := V.Γ.qms
variable {E' n' : Type*} {E n : Type} [Field.{0} E] [CMType E] [Fintype n] {s : n → ℤˣ} (V : Space E n s)
lemma encard_hermitian_le [Field E'] [CMType E'] [Fintype n'] {B} (hB : IsCompact B) : ∃ C ≠ ∞, ∀ x : n' → ℤ, {T | Tᴴ = T ∧ (of fun i j ↦ ↑(twoAtInfinity E' ^ (-(x i + x j))) * toAdele (T i j : E')) ∈ B}.encard ≤ C * .ofReal ((2 ^ numInfPlaces E') ^ ∑ i, ∑ j, (x i + x j).toNat) := exists_isUnit_sub_star.elim fun θ h ↦ ((rpow_left_surjective two_ne_zero).exists.1 (encard_le_of_dyadic_box ((hB.add (hB.smul (toAdele (θ : E')))).image_auto vec (by fun_prop [vec])))).imp fun C ↦ .imp (by simp) fun k x ↦ by
 grw [← ENNReal.pow_le_pow_left_iff two_ne_zero, sq, ← ENat.toENNReal_mul, ← encard_prod, k
   (x · + x ·).uncurry (fun (S, T) ↦ (S + θ • T).vec) (fun (T, U) a (S, R) c e ↦ by
   have := congr(star $e)
   simp [← ext_iff, ↓funext_iff] at *
   grind) fun T a ↦ ⟨_, add_mem_add a.1.2 (smul_mem_smul_set a.2.2), by ext1 ⟨⟩; simp; ring⟩]
 simp [mul_pow, sum_prod_type, ← pow_mul]
namespace Space
lemma ideleAbs_det_x [Field n'] [CMType n'] [Fintype E'] {s} (V : Space n' E' s) : ideleAbs V.x.det = 1 := by simpa [field, pow_eq_one_iff_of_nonneg] using congr(ideleAbs $(show (star V.x * .map toAdele V.isUnit_J.unit * V.x) ^ 2 = 1 by ext1; simp [sq, star, V.3]).det)
lemma lintegral_encard_ne_top {t} [Fintype t] {Ω} (hΩ : IsCompact Ω) (z : Nonempty n → 2 * card t < card n) : ∫⁻ g, {ξ : Matrix n t E | (V.toRatCoords g).1⁻¹.1 * ξ.map toAdele ∈ Ω}.encard ∂V.quotMeasure ≠ ⊤ := ne_of_lt ((exists_isCompact_profileBases E n).rec fun M ⟨c, hM, h₀⟩ ↦ by
 have hN := (hM.mul (isCompact_setOf_le_ideleAbs_det isCompact_closedBall_prod_integral.matrix one_pos)).union hM
 choose S hS s using exists_compact_gram_entry hN isCompact_singleton
 obtain ⟨⟨d, hd⟩, ⟨C, _, k⟩, ⟨C₁, _, h₁⟩, b⟩ := exists_eq_zero_of_zpow_mul_mem hS,
   encard_hermitian_le (n' := n) hS.matrix,
   encard_le_of_dyadic_box ((hM.prod hΩ).image_auto fun (a, b) (j, i) ↦ (a.2 * V.x.2 * b) i j),
   G.isClosedEmbedding_mat.isCompact_preimage ((hN.mul hN.inv).image_auto (·.1))
 let K := 9 * (2 * c - card n * d + |d|).toNat
 choose! A r a hr using (@id <| ∃ g, ∃ Z ∈ profileBases _ · (V.move g).x, star Z.1 * V.J * Z = ·)
 have m {β ω : _ → _} (p : Σ x, Elem (β x)) := (@measurable_const ℝ≥0∞ _ (borel _) _ (ω p.1)).indicator (measurable_const_mul (A p.1 p.2.1)⁻¹ b.measurableSet)
 grw [lintegral_mono fun g ↦ ?_, lintegral_orbitMeasure_lintegral (.tsum (L := .unconditional _) m), lintegral_tsum (m · |>.aemeasurable), lintegral_indicator_const_le]
 simp [ENNReal.tsum_sigma'] at b ⊢
 grw [k, (mul_assoc ..).le, mul_div_le, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, @tsum_prod_le_prod_tsum _ _ ℤ ((2 ^ numInfPlaces E)⁻¹ ^ ·.natAbs.div2),
   le_of_add_le_left (tsum_nat_add_neg (by simp)).ge]; swap
 choose x Y v hx using h₀ _
 have ⟨σ, _, hσ⟩ := exists_ne_zero_of_sum_ne_zero ((star Y * V.isUnit_J.unit * Y).det_ne_zero ∘ (det_apply _).trans)
 have h i m := sub_nonneg.2 (not_lt.1 (prod_ne_zero_iff.1 (right_ne_zero_of_smul hσ) i m
   <| hd _ · (s (V.move g).3 (.inr v) ..))); have hy i := single_le_sum h (mem_univ i)
 grw [h₁ (-x ·.2) _ (vec_bijective.1.comp Y⁻¹.1.mul_right_injective_of_invertible).injOn fun ξ _ ↦
   ⟨(_, _), ⟨v, ‹_›⟩, by ext1; simp [dyadicDiag, move, toRatCoords, ← Matrix.map_mul, ← map_inv]⟩,
   lintegral_count, ENNReal.tsum_comm, ← ENNReal.tsum_prod, ← tsum_comp_le_tsum_of_injective (f := fun Z : profileBases _ x _ ↦ ⟨⟨x, _, IsSelfAdjoint.conjugate' V.conjTranspose_J _, s (V.move g).3 Z.2⟩, _, ⟨_, gram_mul_of_gram_eq (hr x _ ⟨_, _, Z.2, rfl⟩) (gram_inv_of_gram_eq rfl)⟩,
   rfl⟩) (by simp +contextual [Function.Injective, V.ratEmbed_injective.eq_iff]), funext fun Z ↦
   indicator_of_mem (by exact ⟨_, Set.mul_mem_mul (a x _ ⟨_, _, Z.2, rfl⟩)
   (inv_mem_inv.2 Z.2), by simp [move, ratEmbed, toRatCoords, G.mat, U.map]⟩) _]
 let W a j := (a - x j).toNat
 simp [σ.sum_comp, ideleAbs_det_x] at hy hx ⊢
 grw [mul_div, ← mul_assoc, mul_rotate' _ (C₁ * 2 ^ (numInfPlaces E * (card n).succ ^ 2 * K)), ← encard_image_le (Y.2 * ·.1 - 1 |>.vec), ← encard_mono fun u k ↦ ?_, ← minkowski_first (dyadicDiag fun (i, j) ↦ W (x i) j), ideleAbs_det_dyadicDiag_natCast, prod_pow_eq_pow_sum, ← ENNReal.inv_pow, ← division_def]
 have : ∑ i, (2 * (x i).natAbs.div2 + ∑ j, 2 * (W 0 (σ i) + (x i + x j).toNat)) ≤ ∑ i, (K + W 0 i +
   W 0 (σ i) + ∑ j, (W (x i) j + 3 * W (x i) (σ j) + K)) := by clear * - h hy hx; gcongr <;> grind
 have := sum_mono fun i ↦ mul_le_mul_left (z ⟨i⟩) (W 0 i)
 simp [← mul_sum, σ.sum_comp, ← pow_mul, ← pow_add, ← mul_add, ENNReal.le_div_iff_mul_le, mul_assoc, sum_prod_type] at *; gcongr 3; simp; lia
 have e p (h : x p.1 ≤ x p.2) : u p = 0 := by grind [eq_zero_of_norm_Φ, by
   simpa [dyadicDiag, ← map_inv, pi_norm_lt_iff, h, W] using k p]
 use Y * .mk'' (1 + (of u.curry)ᵀ)
   (by rw [det_eq_one_of_unitriangular (lev := x)] <;> simp +contextual [e]), .inl
   ⟨_, v, _, ⟨fun i j ↦ ?_, by simp [field]⟩, mul_inv_cancel_left ..⟩, by simp [funext_iff]
 have := (k (j, i)).imp_left (·.out.le); revert this
 by_cases i = j <;> cases le_total (x j) (x i) <;> simp [*, dyadicDiag, W, ← map_inv diagGL, -map_inv, mul_comm, _root_.zpow_sub, mul_assoc]
 simp [← tsum_even_add_odd (f := (_ ^ ·.div2)), one_lt_pow₀, ENNReal.tsum_add, b.measure_lt_top, mul_lt_top_iff, Ne.lt_top, *])
instance isFiniteMeasure_quotMeasure : IsFiniteMeasure V.quotMeasure := ⟨by simpa [ENat.card, Cardinal.mk_eq_one]
 using (V.lintegral_encard_ne_top (t := Empty) isCompact_univ (by simp [card_pos_iff])).lt_top⟩
abbrev _root_.typeKernel (l : _ → n → ℤ) (s : n → _) (x : GInf E s) := ∏ w, dsKernel (l w) (x w)
def _root_.realConv (k F : _ → ℂ) (g : G E s) := ∫ x, k x * F (g * (x, 1))
variable (E s) in abbrev _root_.finRightRep : Representation ℂ (Gf E n) (G E s → ℂ) := (rightRegular ..).comp (.inr ..)
structure _root_.ThetaKernel {n'} [Fintype.{0} n'] {t} (X) [NormedAddCommGroup X] [NormedSpace ℂ X]
   (S : Space E n s) (T : Space E n' t) where
 ω : G E s × G E t →* X →L[ℂ] X
 θ : X →L[ℂ] ℂ
 continuous : Continuous ↿(ω · ·)
 rat_mul {γ γ'} : γ ∈ S.Γ → γ' ∈ T.Γ → ∀ g k φ, θ (ω (γ * g, γ' * k) φ) = θ (ω (g, k) φ)
attribute [fun_prop] ThetaKernel.continuous
structure IsAutomorphic (F : G E s → ℂ) where
 continuous : Continuous F
 rat_mul : V.Γ.FixesLeft F
 exists_level : ∃ K : OpenSubgroup _, HasLevel F K
lemma isAutomorphic_const c : V.IsAutomorphic fun _ ↦ c := by use ?_ <;> continuity
def petersson (F F' : G E s → ℂ) := ∫ g, starRingEnd ℂ (F g) * F' g ∂V.quotMeasure
attribute [local simp] petersson realConv funext_iff mul_assoc
structure IsForm (e : GInf E s → ℂ) (F : G E s → ℂ) extends V.IsAutomorphic F where
 bounded : ∃ C, ∀ g, ‖F g‖ ≤ C
 realConv_eq : Integrable e → realConv e F = F
variable {V} {F F' : G E s → ℂ} (V' : Space E n s) (e : GInf E s → ℂ)
lemma IsAutomorphic.map₂ (h : V.IsAutomorphic F) (h' : V.IsAutomorphic F') (f : _ → _ → ℂ) (c : Continuous ↿f := by fun_prop) : V.IsAutomorphic fun g ↦ f (F g) (F' g) := by
 obtain ⟨⟨_, _, ⟨K⟩⟩, _, _, ⟨L⟩⟩ := h, h'
 use by fun_prop, ?_, K ⊓ L <;> aesop
lemma IsAutomorphic.conj (h : V.IsAutomorphic F) : V.IsAutomorphic (star F) := h.map₂ h fun _ ↦ star
lemma IsAutomorphic.comp_mul_right (h : V.IsAutomorphic F) a : V.IsAutomorphic (F <| · * a) := have ⟨_, _, K, k⟩ := h; ⟨by fun_prop, by aesop, K.comap (MulAut.conj a.2⁻¹) (.mul_const (by fun_prop) _),
 fun _ r _ ↦ .trans (by aesop) (k _ r _)⟩
lemma IsAutomorphic.eq_zero_of_petersson_self (h : V.IsAutomorphic F) (b : MemLp F 2 V.quotMeasure) (e : V.petersson F F = 0) : F = 0 := by
 apply h.1.ext_on
   (dense_of_ae_orbitMeasure _ ((integral_eq_zero_iff_of_nonneg _ b.integrable_norm_pow').1
   _)) (by fun_prop) <;> simp_all [h.2, RCLike.conj_mul, EqOn, Pi.le_def, -Prod.forall]
 assumption_mod_cast
lemma IsForm.isBoundedMeasurable {e} {F : G E s → ℂ} (k : V.IsForm e F) : IsBoundedMeasurable F := .of k.2 k.1.1
lemma IsForm.memLp {e} (k : V.IsForm e F) : MemLp F 2 V.quotMeasure := k.isBoundedMeasurable.memLp_top.mono_exponent le_top
lemma IsForm.comp_mul_right {e} (k : V.IsForm e F) a : V.IsForm e (F <| · * (1, a)) := by use k.1.comp_mul_right _ <;> cases k <;> aesop
def Form := ↥(ofLinearComb {F | V'.IsForm e F} ⟨0, isAutomorphic_const .., by aesop, by simp⟩ fun _
 h _ k x y ↦ ⟨h.map₂ k.1 (x * · + y * ·), ⟨_, (by simp; grw [norm_add_le, norm_mul, norm_mul,
 h.2.choose_spec ·, k.2.choose_spec])⟩, have j F (h : V'.IsForm e F) i :=
   (And.intro (h.3 i) fun g ↦ (h.isBoundedMeasurable.integrable_mul_comp i (g * ⟨·, 1⟩)).const_mul)
 by simp_all [mul_add, integral_add, mul_left_comm]⟩) deriving AddCommGroup, Module ℂ
instance : CoeFun (V'.Form e) fun _ ↦ G E s → ℂ := ⟨(·.1)⟩
instance peterssonCore : InnerProductSpace.Core ℂ (V'.Form e) := have k (F F' : V'.Form e) := (integral_congr_ae (F.2.memLp.coeFn_toLp.comp₂ (inner ℂ) F'.2.memLp.coeFn_toLp)).symm; ⟨by use! (V'.petersson · ·) <;> simp_all [↓← L2.inner_def, mul_comm, sq, ← inner_add_left,
 ← inner_smul_left] <;> bound, fun ⟨_, h⟩ ↦ Subtype.ext ∘ h.eq_zero_of_petersson_self h.memLp⟩
instance : NormedAddCommGroup (V'.Form e) := (peterssonCore ..).toNormedAddCommGroup
instance : InnerProductSpace ℂ (V'.Form e) := .ofCore _
def formRep (V : Space E n s) (e : GInf E s → ℂ) : Representation ℂ (Gf E n) (V.Form e) := (finRightRep ..).subrepresentation _ fun _ _ ↦ (·.comp_mul_right _)
