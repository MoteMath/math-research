import Lib.Weil.GaussSum.LocalHomUnit
import New.SiegelWeil.DescentsVanishPlanes
import New.Exchange.TriangleLevelExponent
import Lib.SiegelWeil.RallisInner.SharpData
import New.Exchange.ExchangeTheorem
section FoldSeg0
open ComplexInnerProductSpace Finset Module ComplexConjugate
variable {I V : Type} {F : ℕ → ℕ → Type} [∀ i n, NormedAddCommGroup (F i n)] [∀ i n,
  InnerProductSpace ℂ (F i n)] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (m) (w : I → ℕ → ℕ)
  (M : ℕ → (I → ℂ) → Prop) (a : I → ∀ i n, F i n →ₗ[ℂ] F i (n + 1))
  (d : I → ∀ i n, F i (n + 1) →ₗ[ℂ] F (i + 1) n) (j : ∀ i, V →ₗᵢ[ℂ] F i 0) (G : Prop)
attribute [local simp] compUpTo inner_smul_right NeZero.ne
structure IsTriangle where
  cost_one : M 0 1
  cost_mul {n n' N c c'} : M n c → M n' c' → n + n' ≤ N → M N (c * c')
  square_law i n (h : i + (n + 1) < m) : ∃ β, (∀ t y z, w t n * ⟪z, a t _ n (d t i n y)⟫ =
    conj (β t)⁻¹ * w t (n + 2) * ⟪z, d t i _ (a t i _ y)⟫) ∧ (G → M 1 β ∧ ∃ κ, M 0 κ ∧ ∀ t z, ∃ x,
    (∀ y, ⟪a t i _ y, z⟫ = ⟪y, x⟫) ∧ ∀ y, ⟪d t i n x, y⟫ = κ t * ⟪d t i _ z, a t _ n y⟫)
  length_one i (h : i < m) t y : (∀ z, ⟪z, a t i 0 (j i y)⟫ = ⟪d t i 0 z, j _ y⟫) ∧
    ∃ v, j _ v = d t i 0 (a t i 0 (j i y)) ∧ (v = 0 → y = 0)
noncomputable abbrev weightedChain t i := compUpTo fun n ↦ (w t n : ℂ) • a t i n
variable {m w M a d j G} (h : IsTriangle m w M a d j G) [∀ t n, NeZero (w t n)]
include h
lemma IsTriangle.weightedChain_descent i n (hi : i + n < m) : ∃ β κ, (∀ t y,
  weightedChain w a t _ n (d t i 0 (a t i 0 y)) = (w t n.succ / w t 1 / w t 0 / conj (β t) : ℂ) • d
  t i n (weightedChain w a t i _ y)) ∧ (G → M n (κ * β) ∧ ∀ t y z, ⟪z, a t i n
  (weightedChain w a t i n (j i y))⟫ = κ t * ⟪d t i n z, weightedChain w a t _ n (j _ y)⟫) := by
  induction' n with n H; use 1, 1; simp [h.1, h.4 i hi]
  choose _ _ e r u using H hi.le; choose! _ f s _ c _ p q using h.3 i n hi
  refine ⟨_, _, fun t y ↦ ext_inner_left ℂ ?_, fun g ↦ ⟨(mul_mul_mul_comm ..).subst (h.2 (r g)
    (h.2 (c g) (s g) .refl) .refl), ?_⟩⟩ <;> simp [← inner_conj_symm _ (a _ i n.succ _), *, field]
lemma IsTriangle.eq_zero_of_weightedChain {t} : ∀ n i, i + n ≤ m → ∀ y,
  weightedChain w a t i n (j i y) = 0 → y = 0 := Nat.rec (by simp [norm_map, ← norm_eq_zero]) fun _
  _ i hi y ↦ by grind [h.weightedChain_descent _ _ hi, h.4 i (by lia) t y, smul_zero]
lemma IsTriangle.inner_weightedChain_eq (hG : G) {U} [AddCommGroup U] [Module ℂ U] {s : U → V} (S :
  I → ℕ → End ℂ U) (hS :
  ∀ i < m, ∀ t x y, w t 0 * ⟪a t i 0 (j i x), a t i 0 (j i (s y))⟫ = ⟪x, s (S t i y)⟫) : ∀ n i,
  i + n = m → ∃ κ, M (n * n) κ ∧ ∀ t, ∃ T : End ℂ U, T.det = ∏ k ∈ Ico i m, (S t k).det ∧ ∀ x y,
  ⟪weightedChain w a t i n (j i x), weightedChain w a t i n (j i (s y))⟫ = κ t * (w t 0 * w t 1 ^
  n / w t n) * ⟪x, s (T y)⟫ := Nat.rec (fun _ _ ↦ ⟨_, h.1, fun _ ↦ ⟨1, by aesop⟩⟩) fun n H i hi ↦ by
  choose _ k T _ E using H i.succ (by lia); choose β _ e l _ using h.weightedChain_descent i n hi.le
  choose g z q p using h.4 i (by omega)
  refine ⟨_, h.2 (l hG) k (by lia), fun t ↦ ⟨S t i * T t,
    by grind [prod_eq_prod_Ico_succ_bot], fun x y ↦ ?_⟩⟩
  specialize E t (z t x) y; simp [*, field] at E ⊢
  grind [(j _).inner_map_map, h.eq_zero_of_weightedChain (t := t) n i.succ, zero_smul,
    inner_zero_left]
end FoldSeg0
namespace Data
open Finset Fintype Modulus MulChar
variable {P} {D : Data P} {n n' N : ℕ} {c c' : D.MFoldTwist → ℂ}
variable (D n c) in
def CostsSquares := ∀ θ, D.IsFitFamily θ → HeightLe (n * (2 * D.t * D.x ^ 999)) fun ι ↦
  (‖c (θ ι) / c 1‖ ^ 2 :)⁻¹
lemma CostsSquares.mul (h : D.CostsSquares n c) (h' : D.CostsSquares n' c') (e : n + n' ≤ N) :
  D.CostsSquares N (c * c')
  | θ, o => ((h θ o).mul (h' θ o)).mono (by grw [← e]; grind) (by simp [field])
lemma card_𝔪 e ϑ : card (D.𝔪 ϑ e).ResRing = (∏ i, (D.chosen i).q) ^ e * ϑ.levelNorm := by
  erw [LevelPlaces.card_levelModulus_resRing, prod_coe_sort, levelPlaces]
lemma CostsSquares.of_norm_sq_eq_mul_card_zpow e C (k : ℤ) (h : ∀ ϑ, ‖c ϑ‖ ^ 2 =
  C * card (D.𝔪 ϑ e).ResRing ^ k) : D.CostsSquares 0 c
  | _, o => o.heightLe_of_eq_zpow_mul (@.prod _ ∅ id 1 nofun) (by simp) fun _ _ ↦
    ⟨-k, by simp_all [div_pow, card_𝔪, mul_zpow, field, twist_one_spec]⟩
lemma CostsSquares.one : D.CostsSquares 0 1 := .of_norm_sq_eq_mul_card_zpow 0 1 0 (by simp)
lemma isPrimitiveMulChar_of_isTameFor {ϑ ν γ χ} : IsTameFor (D.𝔪 ϑ 1) ν γ χ → IsPrimitiveMulChar χ
  | ⟨_, ψ, _, hψ, H⟩, a,
    n => have := matrix_ext_modulusResidue (x := !![a]) (y := 0) (D.levelPlaces ϑ).apart.1
    have ⟨w, m, _⟩ : ∃ w m, modulusResidue _ m a ≠ 0 := by by_contra!; simp_all [← Matrix.ext_iff]
    (ne_one_iff.1 ((hψ w).2 m)).elim fun x _ ↦
      (algebraMap_ResField_surjective w ((x - 1) / modulusResidue _ m a)).elim fun b (_ :
      modulusResidue _ m b = _) ↦ ⟨Modulus.reduction _ ⟨_, idem_mem_Ô {w}⟩ * ↑b, by
      simp_all [finprod_eq_single _ (Subtype.mk w m), apply_eq_zero_iff, charOfTamePart_apply]⟩
lemma exists_isTameFor_costsSquares_one (p : D.Pair) (r : p.IsRamified) e [NeZero e] (n :
  D.LiftIndex) : (∀ ϑ : D.MFoldTwist, IsTameFor (D.𝔪 ϑ e)
  (p.ν * ϑ.toAutChar ^ n.1)⁻¹ (p.c ·) (charOfTamePart _ (p.ψ * ϑ.ψ ^ n.1))⁻¹) ∧ ∀ {c C}, (∀ ϑ :
  D.MFoldTwist, ‖c ϑ‖ ^ 2 = C * lValueProd (D.𝔪 ϑ e).places (p.ν * ϑ.toAutChar ^ n.1)⁻¹ p.z) →
  D.CostsSquares 1 c := ⟨fun ϑ ↦ by simpa [Pi.neg_def] using! (isTameFor_of_hasWeight
  _ (p.hasWeight.mul (ϑ.powTwist n).hasWeight) r).inv, fun h θ o ↦ o.heightLe_of_eq_zpow_mul
  (.prod (s := Icc 1 p.z) fun _ _ ↦ (o.height_le n (p.lowerPoint _) 1 r).pow 2) (by simp [field,
  p.7.2]) fun ι _ ↦ ⟨-p.z ^ 2, have := p.lValueProd_eq 1 ((θ ι).powTwist n)
  by simp_all [div_pow, twist_one_spec, MFoldTwist.powTwist, TameChar.pow, places_modulus_eq_union]
     simp_all [field, sq, zpow_mul, pow_mul]⟩⟩
end Data
section FoldSeg2
attribute [-simp] Space.θ_apply
open MeasureTheory Matrix Fintype Space WeilData
variable {E n n' n₁ n₂} [Field E] [CMType E] [Fintype n] [Fintype n'] [Fintype n₁]
  [Fintype n₂] {s s' s₁ s₂} (A' : Space E n s) {A : Space E n' s'} {U₁ : Space E n₁ s₁}
  {U₂ : Space E n₂ s₂}
lemma integral_integral_sum_eq {c G : n → ℂ} {F : n →
  _} : let μ := U₁.quotMeasure.prod U₂.quotMeasure
  (∀ i, c i ≠ 0 → Integrable (F i) (μ.prod A.quotMeasure) ∧ integral (μ.prod A.quotMeasure) (F i) =
    G i) → ∫ x, ∫ y, ∑ i, c i • F i (x, y) ∂A.quotMeasure ∂μ = ∑ i, c i • G i := fun _ ↦ by
  rw [integral_integral, integral_finsetSum] <;> (try apply integrable_finsetSum) <;>
    congr! <;> by_cases c ‹_› = 0 <;> simp [Integrable.const_mul, *]
lemma apply_eq_mul_of_formRep_one {e e₁ e₂ f w} {y : A.Form e} {c c' C : ℂ} {u d l : _ →ₗ[ℂ] _} (h :
  y = c • u (U₁.formRep e₁ 1 f)) (h' : U₂.formRep e₂ 1 w = c' • d y) (H : c' * c = C) :
  l w = C * l (d (u f)) := by simp_all [smul_smul]
lemma exists_integrable_kernel_bound {y y'} (r : y ∈ U₁.rapidFunctions) (r' :
  y' ∈ U₂.rapidFunctions) {b₁ b₂ : AutChar E} {K : fockSpace s → _ → _ → ℂ} (h : ∃ B N C, ∀ v g z,
  weightedNorm N v ≠ ⊤ → ‖K v g z‖ * A.height z ^ 0 ≤ C * (weightedNorm N v).toReal * (U₁.sum
  U₂).height g ^ B) (hK : ∀ v, Continuous ↿(K v) := by fun_prop) : ∃ N C, ∀ v, weightedNorm N
  v ≠ ⊤ → let F q := y q.1.1 * y' q.1.2 * (b₁.1 q.1.1.det * b₂.1 q.1.2.det)⁻¹.1 * K v (.sum q.1) q.2
  Integrable F ((U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure) ∧ ∀ q, ‖F q‖ ≤
    C * (weightedNorm N v).toReal := by
  obtain ⟨⟨⟨⟩, r⟩, ⟨⟨⟩, r'⟩, B, N, C, h⟩ := r, r', by simpa using h
  obtain ⟨⟨a, r⟩, b, r'⟩ := r B, r' B
  use N, |C| * |a| * b, fun v hv ↦ (⟨.of_bound (by fun_prop) _ (.of_forall ‹_›), ·⟩) fun _ ↦ ?_
  grw [norm_mul, h, le_abs_self C, height_sum_le, ← r', ← le_abs_self a, ← r] <;>
    simp [le_of_lt, mul_pow, field, *]
variable [WeilData E] (A U₁ U₂)
attribute [local simp] modKernel pairTheta pairWeil_apply
lemma one_square {k₁ k₂ d k Φ₁ Φ₂ k' Φ₁' Φ₂' I} {a b ν 𝔪 χ : ∀ _ : I, _} (h₂ : IsEdgeFamily b k₂ k d
  Φ₂) (h₁ : IsEdgeFamily a k₁ k (!d) Φ₁) (h₃ : IsEdgeFamily a k' k₂ (!d) Φ₂') (h₄ : IsEdgeFamily b
  k' k₁ d Φ₁') σ (hs : negCount (s₁ ⊕ᵥ s₂) = negCount s' + negCount s) e (he : card n' =
  card n + 2 * e) (hn : 2 * negCount (s₁ ⊕ᵥ s₂) + 2 ≤ card (n₁ ⊕ n₂)) {μ : _ → ℤ} (hμ : ∀ v, card
  (n₁ ⊕ n₂) ≤ 2 * μ v + 2 * negCount (s₁ ⊕ᵥ s₂)) (ht : ∀ i, IsTameFor (𝔪 i) (ν i) μ (χ i)) (hE :
  ∀ i {p q} [Fintype p] [Fintype q], card p + card q = card n₁ + card n₂ → a i p * b i q = rankTwist
  (ν i)⁻¹ (n₁ ⊕ n₂)) : let u i x := modDescent _ A (b i) Φ₂ (Pi.single x.toCols₂ 1) _ _ ∘ₗ modLift
                         U₁ A (a i) Φ₁ (Pi.single x.toCols₁ 1) _ (k !d)
  let v i y := modLift A' U₂ (a i) Φ₂' (Pi.single y.toRows₂ 1) _ (k₂ !d) ∘ₗ
    modDescent _ _ (b i) Φ₁' (Pi.single y.toRows₁ 1) (k₁ !d) (k' !d)
  ∃ C κ, ∀ i, ∃ c ≠ 0, ‖c‖ ^ 2 = C * lValueProd (𝔪 i).places (ν i) e ∧
    ∀ f (l : _ →ₗ[ℂ] ℂ), SquareLaw (χ i) σ (κ / c) (l <| u i · f) (l <| v i · f) := by
  intro u v; obtain ⟨C, _, h₀, H⟩ :=
    exchange_theorem (U₁.sum U₂) A A' σ hs he hn hμ (weightedNorm_polyVector_ne_top · _)
  choose N D hi hF using fun j : (_ × U₂.Form (k₂ d)) × Σ i, {x // HasLeftInv (R :=
    (𝔪 i).ResRing) xᵀ} ↦ exists_integrable_kernel_bound (h₁.1.form_mem_rapidFunctions j.1.1)
    (h₂.1.form_mem_rapidFunctions j.1.2) (pairTheta_decay_of_onto _ A (rankTwist _ (n₁ ⊕ n₂)) 1
    (evalAt _) (𝔪 _).disjoint_places_star ((𝔪 _).isSchwartzBruhat_liftFn
    (Pi.single j.2.2.1 1 ∘ vecToMat)) (fun _ c ↦ (isPrimitiveMatrix_of_liftFn_ne_zero _ (by
    simpa using fun _ ↦ (· ▸ j.2.2.2)) (ht _).1.some.2 c).2.imp (by tauto)) 0)
  obtain ⟨⟨P, hP⟩, hp, S⟩ := exists_tendsto_weightedNorm h₀, (hi · _ <|
    weightedNorm_polyVector_ne_top _ ·), mem_rename_range_mul _ _
  refine ⟨C, ((LinearMap.toSpanSingleton ℂ _ fun j ↦ ∫ g, j.1.2 g * u _ j.2.2.1 j.1.1 g
    ∂U₂.quotMeasure).range.closed_of_finiteDimensional.isSeqClosed (fun n ↦ ?_) (tendsto_pi_nhds.2
    fun j ↦ tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' (((hP _).eventually_ne bot_ne_top).mono
    fun n h ↦ integral_sub (hp j (P n)) (by tauto) ▸ norm_integral_le_of_norm_le_const <| .of_forall
    (hF j _ h · |>.trans_eq' <| by rw [norm_sub_rev]; simp [mul_sub])) ((((ENNReal.tendsto_toReal
    bot_ne_top).comp (hP _)).const_smul_zero (D j)).zero_smul_const _)))).imp fun κ hκ i ↦ ?_⟩
  refine Submodule.mul_induction_on (S ?x (P n)) ?_ fun P Q ↦ (Set.mem_of_eq_of_mem
    (by ext; simpa [mul_add] using integral_add (hp ..) (hp ..)) <| add_mem · ·)
  swap; rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  obtain ⟨⟨α, e₁⟩, β, e₂⟩ := h₁.exists_lift_eq_realConv P, h₂.exists_lift_eq_realConv Q
  have e F (F' : A.Form _) := by
    simpa [petersson, realConv, ← integral_conj] using (conjForm (eq_star_of_eq_star (h₂.2.1 d).2)
      F).2.petersson_realConv_realConv (h₁.2.1 _).1 F'.2 (star α).integrable β.integrable
  refine ⟨_, funext fun _ ↦ ((integral_prod_symm _ (hp ..)).trans (.trans ?_ ((e ..).trans (congrArg
    _ (h₂.isArrow_modDatum.elim (·.integral_mul_formLift_swap · ..)))))).symm⟩
  simp_rw [← realConv.eq_1, ← e₁, ← e₂, lift, ← integral_prod_mul]
  congr! 4; erw [← modKernel, (?_ : Pi.single _ _ = _), ← hE _ rfl,
    modKernel_sum_left]; simp [field]
  grind [fromCols_toCols]
  simp
  obtain ⟨⟨c, c₀, c₁, H⟩, e, o, t⟩ := H _ _ _ (ht i), (mul_comm ..).trans (hE i (add_comm ..)), by
    simpa using card_congr σ,
    (((ht i).inv.mul (hasWeight_upsilonU1_pow _)).inv (ν := rankTwist _ (n₁ ⊕ n₂)))
  use c, c₀, c₁, fun f l ↦ ⟨fun u x ↦ apply_eq_mul_of_formRep_one
    (h₁.isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_single 1 _) _)
    (h₂.isArrow_modDatum.2.formRep_formLift_of_eq_smul (pairWeil_modDatum_single 1 (liftMod u)⁻¹) _)
    (by simpa [← hE i rfl, ← map_inv] using t.apply_det (liftMod u)), fun u x ↦
    apply_eq_mul_of_formRep_one
    (h₄.isArrow_modDatum.2.formRep_formLift_of_eq_smul (pairWeil_modDatum_single (liftMod u) 1) _)
    (h₃.isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_single _ 1) _)
    (by simpa [← e] using t.apply_det (liftMod u)), fun Φ Ψ hP ↦ ?_⟩
  simp only [← smul_eq_mul, ← map_smul, ← map_sum]
  refine congrArg l (ext_inner_left ℂ fun z ↦ ?_); let f' := conjForm (d.not_not ▸ (h₂.1 _).2) z
  obtain ⟨L, R, K⟩ := fun x ↦ integral_integral_sum_eq fun y hy ↦ (⟨·, integral_prod_symm _ ‹_›⟩)
    ((exists_integrable_kernel_bound (h₁.1.form_mem_rapidFunctions f) (h₂.1.form_mem_rapidFunctions
    f') (pairTheta_modDatum_decay A' _ x x (Ψ := Pi.single y 1) (ht i).1 (by simpa using ⟨_,
    (hP.2 y hy).choose_spec.2 ▸ invFirstRows_mul_firstCols ..⟩) 0)).choose_spec.choose_spec _
    (weightedNorm_polyVector_ne_top _ _)).1, integral_integral_sum_eq fun x hx ↦ by
    simpa +instances only using (fun j ↦ (⟨hi j _ (h₀ _), congr($hκ j).symm⟩ : _ ∧ _ = κ * _)) ⟨(f,
      f'), i, x, (hP.1 x hx).choose_spec.2 ▸ hasLeftInv_invLastRows_transpose ..⟩, by
    simpa only [thetaIntegral, pairTheta, modDatum_eq_sum _ _ Φ, modDatum_eq_sum _ _ Ψ, map_sum,
      map_smul] using H Φ Ψ hP
  simp only [← mul_smul_comm, ← Finset.mul_sum, pairTheta, mul_left_comm _ c, ← modDatum.eq_1, K,
    integral_const_mul] at *
  simp [inner_smul_right, inner_sum, field]
  erw [← R, L, mul_comm]; congr!
  erw [(?_ : Pi.single _ _ = _), ← e, inner_eq_petersson, petersson,
    h₃.isArrow_modDatum.1.coe_formLift, ThetaKernel.integral_lift_eq_integral_descent _
    (h₃.1.form_mem_rapidFunctions _) (h₂.1.form_mem_rapidFunctions f')]; simp_rw
    [h₄.isArrow_modDatum.2.coe_formLift, lift, ← integral_prod_mul]
  congr! 4; nth_rw 1 [← pairTheta, ← modKernel, modKernel_sum_right, e,
    ← hE i (o ▸ add_comm ..).symm]
  simp [e, ← hE i o, field]
  clear * -; grind [fromRows_toRows]
end FoldSeg2
section
attribute [local simp] Space.θ_apply
noncomputable section
open MeasureTheory Matrix Complex ComplexConjugate Fintype LinearMap
open WeilData Space Modulus ComplexInnerProductSpace
variable {E N N'} [Field E] [CMType E] [WeilData E] [Fintype N] [Fintype N'] {s s'}
  (S : Space E N s) (T : Space E N' s') {I} {a : I → _} {P} (D : Data P) (z ϑ i n)
def formNegEquiv l : S.Form (typeKernel l s) ≃ₗᵢ[ℂ] S.neg.Form (typeKernel l _) := .symm
  (LinearEquiv.isometryOfInner
  (.ofEq _ _ (.symm (SetLike.ext ((isForm_neg_iff_and_integral_neg S _).1 _))) ≪≫ₗ .ofSubmodule'
  (.funCongrLeft ℂ ℂ G.neg.1) _) fun _ _ ↦ .symm ((isForm_neg_iff_and_integral_neg S _).2 _))
lemma IsEdgeFamily.exists_adjoint_first_arrow {l k' Φ Φ'} (h : IsEdgeFamily a (kernelPair l s) k'
  false Φ) i {𝔪} Ψ : let b i n [Fintype n] := (a i n)⁻¹ * upsilonU1 ^ card n
  IsEdgeFamily b (kernelPair l (-s)) k' true Φ' → ∃ Ψ', ∀ y x, ⟪x, modLift S T (a i) (𝔪 := 𝔪) Φ Ψ _
    _ y⟫ = ⟪modDescent _ T (b i) (𝔪 := 𝔪) Φ' Ψ' (k' false) _ x, formNegEquiv S l y⟫ := fun h' ↦ by
  obtain ⟨⟨c, _⟩, κ, K⟩ := exists_modKernel_neg_left S T, h'.petersson_descent_eq _
  exact ⟨c • conj κ • _, (reindex_equiv (formNegEquiv ..).symm).1.2 fun y x ↦ by
  simp [modDescent, modDatum, Pi.smul_comp]
  erw [← star_inj, mul_comm, mul_comm _ κ, ← K, inner_eq_petersson,
    h.isArrow_modDatum.1.coe_formLift]; simp_all [modKernel, pairTheta, Space.lift, Space.petersson,
    ← integral_conj, mul_assoc, isForm_neg_iff_and_integral_neg S S.neg, mul_left_comm _ c]; tauto⟩
namespace Data
seal U w Int.add instInv
abbrev TriForm := (D.gridSpace i ..).Form (typeKernel (D.gridParam z i 0 n) _)
def triLift : D.TriForm z i n →ₗ[ℂ] D.TriForm z i (n + 1) := modLift _ _ (gridChar ϑ (!z) (n + i))
  (D.gridHarmonic i false (!z) (n + i) z 0 n 0 (n + 1))
  (inclusionDatum (triangleModulus z ϑ).ResRing) ..
def triNegEquiv : ∀ i, D.TriForm z 0 0 ≃ₗᵢ[ℂ] D.TriForm z i 0 := Nat.rec (.refl ..) fun _ ↦
  (·.trans (formNegEquiv ..))
def triBase : Submodule ℂ (D.TriForm z 0 0) :=
  levelSpace (formRep ..) (z.rec D.chosenLevel (principalLevel _ D.gridLevelGen))
lemma triNegEquiv_formRep k y : ∀ i, D.triNegEquiv z i (formRep _ _ k y) =
  formRep _ _ k (D.triNegEquiv z i y) := Nat.rec rfl fun _ ↦ congrArg (formNegEquiv ..)
lemma hasSum_inner_triLift (h : i < D.m) : ∃ C,
  ∀ ϑ (y : D.triBase z), let a y := D.triLift z ϑ i 0 (D.triNegEquiv z i y)
  (∀ v, (∀ x, ⟪v, x⟫ = ⟪a y, a x⟫) → v ∈ D.triBase z ∧ (v = 0 → y = 0)) ∧ ∀ x, HasSum (fun γ ↦ C *
    (cosetTerm (card (D.GridIndex z 0 1)) (gridChar ϑ (!z) i (D.GridIndex z 0 1))
    (triangleModulus z ϑ).places.conjClosureᶜ x y γ / card (D.GridIndex z 0 1 × D.GridIndex z 0 0 →
    (triangleModulus z ϑ).ResRing))) (triangleOrder z ϑ 0 * ⟪a x, a y⟫) := by
  have e := D.paramsCorrespond_grid false z i 0 0 rfl
  obtain ⟨C, -, H⟩ := rallis_inner_product_euler (T :=
    gridSpace ..) e.isEdge_jointHarmonic (by simp [card_gridIndex]; grind [Bool])
  use C, fun ϑ y ↦ ?_
  have r u := by simpa [triNegEquiv_formRep] using congr(D.triNegEquiv z i $(y.2 u))
  specialize H (gridChar ϑ ..) (gridChar ϑ ..) (isSharp_modDatum (F := Pi.single
    (inclMatrix (triangleModulus z ϑ).ResRing .inl) 1) _ _ (.inr nonempty_modulus_places) _ (by
    simp; exact inclMatrix_transpose_mul_self .inl) (by cases z <;> exact ((auxPair ..).tame_eq_one
    · <| places_levelModulus.ge.mt ·)) (by simp)) _ fun k ⟨u, a, e⟩ g ↦ congr($(r ⟨k, e ▸ by
    cases z; exacts [D.levelY_le_chosenLevel ϑ 0 ⟨u, (LevelPlaces.ker_reductionK₀_eq _).le a, rfl⟩,
      (mem_principalLevel_iff gridModulus_one_ideal _).2 a]⟩).1 g)
  refine ⟨fun v p ↦ ⟨fun u ↦ ext_inner_right ℂ (((formRep ..).apply_bijective u).2.forall.2
    fun x ↦ ?_), fun o ↦ by simpa using H.1 (inner_self_eq_zero.1 (by erw [← p]; simp [o]))⟩,
    fun x ↦ ((H.2 _).mul_left _).congr_fun (by simp [cosetTerm, ← triNegEquiv_formRep, field,
      Bool.cond_false, -Bool.cond_eq_ite])⟩
  let o : Kf .. := ⟨u.1, by cases z; exacts [levelOf_le_Kf u.2, u.2.1]⟩
  choose k f using reductionK₀_surjective (blockGL ((triangleModulus z ϑ).reductionK₀ o,
    (1 : GL (Fin (D.t - z.toNat)) _)))
  erw [inner_formRep, one_smul, p, p, ← (gridSpace ..).inner_formRep k.1]
  repeat erw [(isEdgeFamily_of_paramsCorrespond (D.gridChar · _ _) _
    e).isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_single (y :=
    inclMatrix _ .inl) o k (by erw [f, ← map_inv]; simp [inclMatrix_inl]; rfl))]
  erw [inner_smul_left, inner_smul_right, ← mul_assoc, conj_mul', r, ← triNegEquiv_formRep,
    Circle.norm_coe, one_pow, one_mul]; rfl
attribute [local implicit_reducible] Data.GridIndex BlockIndex kernelPair
theorem exists_isTriangle : ∃ d, IsTriangle D.m (D.triangleOrder z) D.CostsSquares (D.triLift z) d
    (fun i ↦ (D.triNegEquiv z i).toLinearIsometry.comp (D.triBase z).subtypeₗᵢ) (z = false) := by
  let b i ϑ n [Fintype n] := (D.gridChar ϑ (!z) (0 + i) n)⁻¹ * upsilonU1 ^ card n
  have L {i n} (h : i + n < D.m) := isEdgeFamily_of_paramsCorrespond (D.gridChar · _ _) false
    (D.paramsCorrespond_grid _ z i 0 n rfl)
  choose! Φ F using fun i n h ↦ Exists.intro _
    (isEdgeFamily_of_paramsCorrespond (b i) true (@paramsCorrespond_first_arrow n _ D i z h).1)
  have R {n i} h := Exists.intro _
    (isEdgeFamily_of_paramsCorrespond (b i) true (@paramsCorrespond_first_arrow n _ D i z h).2)
  choose! p H using fun i h ϑ ↦ (L h).exists_adjoint_first_arrow (gridSpace ..) (gridSpace ..) ϑ
    (inclusionDatum (triangleModulus z ϑ).ResRing) (F i 0 h)
  let e ϑ i : ∀ n, Matrix (D.GridIndex z 0 (n + 1)) _ _ → ℂ := Nat.rec (p i ϑ) fun _ ↦ nextDatum
  use fun ϑ i n ↦ modDescent _ _ (b i ϑ) (Φ i n) (e ϑ i n) .., .one, .mul, fun i n h ↦ ?_,
    fun i h ϑ y ↦ ⟨H i h ϑ _, (((D.hasSum_inner_triLift z i h).choose_spec ϑ y).1 _ fun _ ↦
    ((D.triNegEquiv z i.succ).symm.inner_map_eq_flip ..).trans (H i h ..).symm).elim (⟨⟨_, ·⟩,
    (D.triNegEquiv z i.succ).right_inv _, · ∘ Subtype.ext_iff.1⟩)⟩
  obtain ⟨⟨H, g⟩, h₀, h₁, h₀', h₁', ⟨P, h₂⟩, _, h₂'⟩ := exists_isTameFor_costsSquares_one ⟨_,
    fun _ ↦ (n + 1) * D.h, _, _, by simpa using!
    (hasWeight_upsilonU1_pow (n.succ * D.h)).inv.mul (D.chi_hasWeight.zpow n.succ), by simp_all,
    ⟨D.nat_le_of_hasLogBound, le_rfl⟩, by clear * -; grind, fun _ ↦ by
    grw [le_of_add_le_right h.le]; use D.le_of_hasLogBound⟩ (D.omega_zpow_ne_one _) (cond z D.b₁ 1)
    ⟨_, n.succ_pos, by omega⟩, @L (i + 1) n (by lia), L h, F _ _ h.le, F _ _ h, R h, R h.le
  simp only [triLift, n.succ_add] at h₁ ⊢
  obtain ⟨Q, rfl⟩ := (fun s t ↦ (⟨flipPoly t s (P.map conj), by
    apply P.induction_on <;> simp +contextual [flipPoly, Int.cast_smul_eq_zsmul, pairSign,
    -zsmul_eq_mul, smul_smul, ← Units.val_mul, mul_comm (t _)]⟩ : ∃ Q, flipPoly s t (Q.map conj) =
    P)) (D.gridSigns z (i + 1) 0 _) (D.gridSigns z i 0 _)
  have ht ϑ := H (cond z 1 ϑ)
  have S := one_square (gridSpace ..) (gridSpace ..) (gridSpace ..) (gridSpace ..) h₁' h₁ h₀ h₀'
    swapFirstTwo ?s (D.t - z.toNat) ?e ?t ?u ht ?v
  have T := one_square (gridSpace ..) (gridSpace ..) (gridSpace ..) (gridSpace ..) h₂ h₀ h₁ h₂'
    swapFirstTwo ?s' 0 rfl ?t' ?u' ht ?v'
  case s | s' =>
    clear * -; simp_rw [negCount_sumElim, card_neg_gridSigns_eq_sum, ← Finset.sum_add_distrib,
      entrySign_eq]
    grind
  case t | t' | e => clear * -; simp [card_neg_gridSigns_eq_sum, card_gridIndex]; grind [Bool]
  case u | u' => cases z <;> simp [card_gridIndex, Data.h, D.t_odd.pos] <;>
    nlinarith [D.k_add_t_add_one_le_h₂, D.r_add_six_le_t]
  case v | v' =>
    clear * -; intros; apply_fun Additive.ofMul
    cases z <;> simp [b, rankTwist, gridChar, liftChar, μ₀, TameChar.pow, twist_one_spec,
      card_gridIndex] at * <;> match_scalars <;> grind
  choose C κ c _ _ S using S; choose _ _ _ _ _ T using T
  use (conj <| c · / κ), fun ϑ y z ↦ by simpa [modDescent, modDatum_eq_sum _ _ (e _ _ _)] using!
    (S _ _ (innerₛₗ ℂ z)).sum_eq_nextDatum _
  rintro rfl
  choose c₁ n₁ e₁ using @exists_conj_modKernel_eq_swap
  choose _ _ hG using (SquareLaw.sum_fourier_eq_nextDatum (D.Y n) (Fin D.t)
    (isPrimitive_primAddChar _) <| isPrimitiveMulChar_of_isTameFor <| ht ·)
  obtain ⟨⟨_, M⟩, _, M₀⟩ := h₁'.petersson_descent_eq Q, h₂'.petersson_descent_eq _
  refine ⟨g (C := C / ‖κ‖ ^ 2) (by simp [*, field]), _, ?_, fun ϑ z ↦
    have A :=
      h₁.isArrow_modDatum.1.inner_formLift_adjoint h₁.isArrow_modDatum.2 (h₂.1 _).2 (h₁.1 true).2 z
    ⟨_, A, fun y ↦ by
    let u j := (triangleModulus false ϑ).flipScalar (D.GridIndex false 0 j)
    have K := by simpa using hG ϑ (e ϑ i n) (T ϑ (formRep _ _ (u n)⁻¹ y) (innerₛₗ ℂ z))
    simp_rw [← inner_smul_right, ← inner_sum, ← (modLift ..).map_smul, ← map_sum, ← map_smul₂] at K
    repeat erw [← map_sum₂, ← modDatum_eq_sum] at K
    have K := congr(conj $(M₀ ..)).trans (by erw [map_mul, ← A, inner_conj_symm, K, ((formRep
      ..).inv_self_apply (u _) _).symm.trans
      (congrArg _ (h₀.isArrow_modDatum.1.formRep_formLift_of_eq_smul (k := u _) (by
      erw [pairWeil_apply, G.onHom_scalarFin]) _)), (formRep ..).self_inv_apply, inner_eq_petersson,
      h₂.isArrow_modDatum.2.coe_formLift, funext (formRep_apply _ _),
      ← ThetaKernel.lift_omega_left _ (h₁'.1.form_mem_rapidFunctions _).1 (1, u _)])
    erw [← inner_formRep (u n)⁻¹, inner_eq_petersson, funext (formRep_apply _ _),
      h₀'.isArrow_modDatum.2.coe_formLift]
    simp [petersson, ↓conj_petersson] at K
    simp [Space.lift, ← integral_conj, u, rep_apply_apply, e₁, petersson, -θ_apply,
      ← pairTheta.eq_1, ← modKernel.eq_1, mul_assoc, mul_left_comm _ (c₁ ..)] at K M ⊢
    erw [K, (eq_inv_mul_iff_mul_eq₀ (by simpa using left_ne_zero_of_mul_eq_one (n₁ ..))).2 (M ..)]
    simp [← mul_assoc]; rfl⟩⟩
  apply_rules (transparency := .instances) [CostsSquares.mul _ _ (zero_add 0).le] <;> first
    | exact .of_norm_sq_eq_mul_card_zpow 1 _ 0 (by simp [*, lValueProd, div_pow]; rfl)
    | exact .of_norm_sq_eq_mul_card_zpow 1 1 (-.ofNat _) (by simp [field]; tauto)
    | exact .of_norm_sq_eq_mul_card_zpow 1 1 (.ofNat _) (by simp [inv_eq_iff_eq_inv, field]; tauto)
unseal w Int.add instInv
end Data
end
end
namespace Data
open Finset Fintype Subgroup LevelPlaces
variable {P} (D : Data P) (ϑ : D.MFoldTwist)
seal dsKernel U
attribute [-simp] Bool.cond_eq_ite
attribute [local simp] Bool.cond_true Bool.cond_false
lemma stdLevelIndex_lastResLevel_eq : ∃ C, ∃ k : ℤ, ∀ ϑ :
  D.MFoldTwist, let w := triangleOrder false ϑ; stdLevelIndex (levelOf _ (D.lastResLevel ϑ)) = C *
    card (D.𝔪 ϑ 0).ResRing ^ k * (D.auxPair ϑ 1).gramFactor ^ D.m * w D.m / (w 0 * w 1 ^ D.m) := by
  choose k K using card_parabolic_blockNumber D.RowIndex (Fin _)
  use D.triangleOrder false 1 0 * (D.triangleOrder false 1 1 / (D.auxPair .one 1).gramFactor) ^ D.m,
    (k 1 - D.t * card D.RowIndex) * D.m - k D.m, fun ϑ ↦ ?_
  let := Prop.linearOrder
  have f n w : _ = Nat.card (GL (D.GridIndex false 0 n) _) :=
    K n (ResField ((D.levelPlaces ϑ).twistPlace w)) ▸ index_mul_card _
  simp +instances [inf_top_eq, inf_bot_eq, ↓fun R [CommRing R] ↦ (ext fun _ ↦ forall₂_congr
    (by simp! [lt_iff_le_and_ne]) : parabolic (R := R) (· ∉ Set.range (.inl : D.RowIndex ↪ D.Y 1)) =
    parabolic (blockNumber 1)), AuxPair.gramFactor, auxPair, AuxPair.rankDiff, triangleOrder,
    triangleModulus, lastResLevel, ← f 1, ← f D.m, auxLevel, index_rangeParabolic,
    card_levelModulus_resRing, LevelPlaces.card_GL_levelModulus, field, card_ResField,
    relIndex_levelOf, Nat.card_pi, index_pi_univ, div_pow,
    prod_eq_zero_iff, zpow_sub₀, zpow_add₀, zpow_mul, prod_pow,
    -Nat.card_eq_fintype_card, Bool.cond_false, -Bool.cond_eq_ite,
    @univ_eq_empty (D.levelPlaces .one).TwistIndex _ ⟨nofun⟩]
  field_simp [prod_eq_zero_iff, NeZero.ne]; ring!
lemma inner_iotaAtLevel x y : let u := weightedChain (D.triangleOrder false) (D.triLift _) ϑ 0 D.m;
    inner ℂ (D.iotaAtLevel ϑ x) (D.iotaAtLevel ϑ y) = stdLevelIndex (levelOf _ (D.lastResLevel ϑ)) *
    card (WeylIndex (D.Y D.m) D.columnsY) * inner ℂ (u x.1) (u y.1) := by
  rw [LevelForm.inner_eq_petersson (D.spaceY _) D.isHCParam_Y]
  congr <;> simpa [weightedChain, triangleOrder, triangleModulus,
    LevelPlaces.card_GL_levelModulus] using! (D.spaceY _).ofAlgForm_toAlgForm D.isHCParam_Y _
@[simp] lemma iotaAtLevel_injective : Function.Injective (D.iotaAtLevel ϑ) := .of_ker _ fun y e ↦
  (D.exists_isTriangle _).choose_spec.eq_zero_of_weightedChain D.m 0 (by simp) _
  (by simpa [e, -Fintype.card_pi] using! D.inner_iotaAtLevel ϑ y y)
end Data
