import Lib.GLn.Dual.ClassSum
import Lib.Adelic.CuspForms.ClassReps
import Lib.Adelic.CuspForms.SmoothFormPairing
import Lib.Weil.Unramified.UniformiserScalar
import Lib.DiscreteSeries.Holomorphic.HolomorphicChamber
noncomputable section
open Matrix NumberField MvPolynomial ComplexConjugate ComplexOrder Subgroup Real PolyRep Finset
section
variable {E r n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [Fintype n]
variable (E) in
structure LevelPlaces where
 (ChosenIndex TwistIndex) [fintypeChosen : Fintype ChosenIndex] [fintypeTwist : Fintype TwistIndex]
 chosenPlace : ChosenIndex → _
 twistPlace : TwistIndex → FinPlace E
 apart : IsConjApart (chosenPlace ⊕ᵥ twistPlace)
lemma maxCompactAt_le_levelOf {ι} {u : ι → FinPlace E} {w H} (h : w ∉ (Set.range u).conjClosure) : maxCompactAt n w ≤ levelOf u H := .trans (by simp_all [LE.le]; grind [star_star]) inf_trivialOn_le_levelOf
def fockLetters {Φ} (s : r → ℤˣ) (ord : r → ℕ) (c : ℤˣ) : MatrixPoly (Σ _ : Φ, n) ℂ →ₐ[ℂ] MvPolynomial (Φ × n × r) ℂ := aeval fun x ↦ ∑ a with s a = c ∧ ord a = x.2, X (x.1.1, x.1.2, a)
def letterPoly {Φ} [Fintype Φ] s ord c κ := (@fockLetters r n _ Φ s ord c).toLinearMap ∘ₗ toPoly _ κ
end
variable {E n : Type} [Field E] [CMType E] [Fintype n] (P : LevelPlaces E)
abbrev stdClassSum {X} [AddCommMonoid X] [Module ℚ X] := classSum (W := X) (stdSpace E n).Γf
namespace LevelPlaces
attribute [instance] fintypeChosen fintypeTwist apart
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (P : LevelPlaces E)
instance isConjApart_chosenPlace : IsConjApart P.chosenPlace := ⟨P.apart.1.comp Sum.inl_injective, fun _ _ ↦ P.apart.2 (.inl _) (.inl _)⟩
abbrev placeAt := P.chosenPlace ⊕ᵥ P.twistPlace
abbrev places := Set.range P.placeAt
end
variable (S : LevelPlaces E) (H : Subgroup (∀ i, GL n (ResField (S.placeAt i)))) (χ : H →* ℂ) (κ : NumberField.InfinitePlace E → ℕ → ℕ) (e : NumberField.InfinitePlace E → ℤ)
def LevelForm : Type := levelSpace (algFormRep κ e) _ (χ.comp (levelOf.reduction ..)) deriving AddCommGroup, Module ℂ, Module ℚ
instance : CoeFun (S.LevelForm H χ κ e) fun _ ↦ Gf E n → WeylIndex n κ → ℂ := ⟨(·.1.1)⟩
attribute [local simp] map_classSum mul_classSum mul_sum Rat.smul_def mul_nonneg gramForm_apply toLinearMapₛₗ₂'_apply dotProduct mulVec
variable {S H χ κ e} (σ : ℂ ≃+* ℂ) (φ φ' : S.LevelForm H χ κ e)
namespace LevelForm
lemma algFormRep_eq_self_of_mem {k} (hk : k ∈ levelOf S.placeAt ⊥) : algFormRep κ e k φ.1 = φ.1 := by simp [levelSpace_levelOf_apply φ.2 _ 1 (mem_levelOf.1 hk).2]
lemma mem_sphericalAt {w} (hS : w ∉ S.places.conjClosure) : φ.1 ∈ sphericalAt (algFormRep ..) w := by simp [↓algFormRep_eq_self_of_mem, maxCompactAt_le_levelOf hS _]
def _root_.evalForm g := (⟨⟨(· g), by tauto⟩, by tauto⟩ : S.LevelForm H χ κ e →ₗ[ℂ] _)
lemma _root_.apply_eq_evalForm g : φ g = evalForm g φ := rfl
def toSmoothForm : S.LevelForm H χ κ e →ₗ[ℂ] (stdSpace E n).forms (κ, e) := Submodule.subtype _
@[irreducible] def innerAt := ((stdLevelIndex (levelOf _ H) : ℂ) • smoothPairing (toLinearMapₛₗ₂' ℂ (.comp ↑σ⁻¹ ((starRingEnd ℂ).comp σ)) _ (weylGramOver (κ := κ))) (σ.injective <| by simpa [Int.cast_comm] using gramForm_map_weightRep σ · · ·)).compl₂ (toSmoothForm (χ := χ)) ∘ₛₗ toSmoothForm (χ := χ) (e := e)
lemma innerAt_eq_stdClassSum : innerAt σ φ φ' = σ⁻¹ (stdClassSum (levelOf _ H) fun g ↦ gramForm (σ ∘ φ g) (σ ∘ φ' g)) := by unfold innerAt; generalize_proofs; dsimp [smoothPairing]; rw [classIntegral_eq_of_le (pairing_mem_smoothInvariants ‹_› ..).1 (fun k hk g ↦ σ.injective (by simp [← mul_assoc, RCLike.mul_conj, ← map_pow, @Complex.norm_eq_one_of_pow_eq_one _ (.card H), ne_of_gt, fun φ : LevelForm .. ↦ (congr($(φ.2 ⟨_, hk⟩).1 g) : φ.toSmoothForm.1 _ = χ _ • φ.toSmoothForm.1 g)])) (levelOf_le_Kf (H := H))]; simp [mul_comm]; rfl
lemma conj_innerAt : σ⁻¹ (conj (σ (φ'.innerAt σ φ))) = φ.innerAt σ φ' := by simp [innerAt_eq_stdClassSum, starRingEnd_apply, star_form weylGram_posDef.1, -dotProduct]
lemma eq_zero_of_innerAt_self (h : φ.innerAt σ φ = 0) : φ = 0 := eq_of_eq_on_class_reps Quot.out_eq (funext fun _ ↦ by_contra fun H ↦ (classSum_pos (fun _ ↦ weylGram_posDef.posSemidef.dotProduct_mulVec_nonneg _) (weylGram_posDef.dotProduct_mulVec_pos (by simpa [funext_iff] using! H))).ne' ((map_eq_zero _).1 (innerAt_eq_stdClassSum σ φ φ ▸ h :)))
end LevelForm
instance : NormedAddCommGroup (S.LevelForm H χ κ e) := InnerProductSpace.Core.toNormedAddCommGroup (cd := ⟨⟨⟨(·.innerAt 1)⟩, LevelForm.conj_innerAt 1, by simp [LevelForm.innerAt_eq_stdClassSum, classSum, sum_nonneg, ← weylNormSq.eq_1, -dotProduct], by simp, by simp⟩, LevelForm.eq_zero_of_innerAt_self 1⟩)
instance : InnerProductSpace ℂ (S.LevelForm H χ κ e) := .ofCore _
instance : FiniteDimensional ℂ (S.LevelForm H χ κ e) := finite_levelSpace_smoothFormRep
attribute [local simp] LevelForm.innerAt_eq_stdClassSum
lemma isOfFinOrder_level_char k : IsOfFinOrder (χ.comp (levelOf.reduction ..) k) := χ.isOfFinOrder (isMulTorsion_of_finite _)
variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {S : LevelPlaces E} {H : Subgroup (∀ i, GL n (ResField (S.placeAt i)))} {χ : H →* ℂ} in
instance : Fact (χ.comp (levelOf.reduction _ H) =ᶠ[nhds 1] 1) := ⟨.mono ((isOpen_levelOf (w := S.placeAt) (H := ⊥)).preimage continuous_subtype_val |>.mem_nhds (by simp)) fun k h ↦ by simp [show levelOf.reduction _ _ k = 1 from Subtype.ext (mem_levelOf.1 h).2]⟩
lemma map_inner_self_eq {χ' l p c c'} {B : S.LevelForm H χ' _ l} {a a' : _ → ℂ} (h : ∀ g i, σ (φ g i) = c * a g * B g (Equiv.piCongrLeft' _ p i)) (h' : ∀ g i, star (σ (star (φ g i))) = c' * a' g * B g (p.piCongrLeft' _ i)) (hc : ∀ g, a g * star (a' g) = 1) : σ (inner ℂ φ φ) = star c' * c * inner ℂ B B := by set f := p.piCongrLeft' _; simp_all [inner, ↓star_involutive.eq_iff, reindex_equiv f, weylGram_eq_submatrix κ p]; grind
namespace LevelForm
variable (σ : ℂ ≃+* ℂ) {l : ℕ} [Fact l.Prime] (j : PadicPlace l)
def normSqAt := classSum stdRatPoints (levelOf _ H) fun g ↦ weylNormSq (σ ∘ φ g)
lemma norm_map_inner_le : ‖σ (inner ℂ φ' φ)‖ ≤ √(φ.normSqAt σ) * √(φ'.normSqAt ((starRingAut.trans σ).trans starRingAut)) := by simp_rw [inner, innerAt_eq_stdClassSum, normSqAt, classSum, finsum_eq_sum_of_fintype, map_sum]; grw [norm_sum_le, ← sum_sqrt_mul_sqrt_le]; gcongr; grw [← sqrt_mul, smul_mul_smul, weylNormSq, weylNormSq, ← posDef_cauchy_schwarz weylGram_posDef]; repeat simp [-mul_sum]
lemma _root_.gramForm_mem_embValRing {g u v} (hu : weylGauge (ι := ⟨j.ιₚ.comp conj⟩) κ e g u ≤ 1) (hv : weylGauge (ι := j) κ e g v ≤ 1) : gramForm (n := n) u v ∈ embValRing (ι := j) := let ⟨γ, h, _⟩ := exists_mul_mem_integralAbove l g 1; by erw [← @weylGauge_embFin (γ := γ), @weylGauge_le_one_iff (hk := h), ← gramForm_map_weightRep 1] at *; exact sum_mem fun _ _ ↦ mul_mem (hu _) (sum_mem fun _ _ ↦ mul_mem (by simp) (hv _))
def integralForms : Submodule embValRing (S.LevelForm H χ κ e) := .copy ((integralFormsAt ⊤ 1).comap (toSmoothForm.restrictScalars _)) {φ | ∀ g, weylGauge κ e g (φ g) ≤ 1} (by unfold integralFormsAt GaugeLe; aesop (add simp top_inf_eq))
lemma norm_inner_le_one {A} (hA : ∀ g, Nat.card (classAut stdRatPoints (levelOf _ H) g) ∣ A) (a : φ ∈ integralForms ⟨j.ιₚ.comp conj⟩) (b : φ' ∈ integralForms j) : ‖j.ιₚ (A • inner ℂ φ φ')‖ ≤ 1 := by simpa only [inner, innerAt_eq_stdClassSum] using! smul_classSum_mem _ hA (gramForm_mem_embValRing j (a _) <| b ·)
variable {J : Type} [Fintype J] (y : J → S.LevelForm H χ κ e) {V β : ℝ}
def pm (σ : J → ℂ ≃+* ℂ) := of fun i l ↦ stdClassSum (levelOf _ H) fun g ↦ gramForm (σ i ∘ y i g) (σ l ∘ y l g)
def covolumeSq σ := ‖(pm y fun _ ↦ σ).det‖
variable {y} {σ} {k : ℕ} {z : Fin k → S.LevelForm H χ κ e} (hz : ∀ a, (z a).normSqAt σ ≤ exp β)
open MatrixOrder in
private lemma pm_psd {σ} : (pm y σ).PosSemidef := Eq.subst (a := stdClassSum (levelOf _ H) fun g ↦ let T := of fun a i ↦ σ i (y i g a); Tᴴ * weylGramOver * T) (by simp [pm, classSum, Matrix.mul_assoc, Matrix.sum_apply, entrywise]) (finsum_nonneg fun _ ↦ ((weylGram_posDef.posSemidef.conjTranspose_mul_mul_same _).smul (by simp)).nonneg).posSemidef
lemma norm_map_det_gram_le (h : ∀ σ, covolumeSq y σ ≤ exp V) : ‖σ (Matrix.gram ℂ y).det‖ ≤ exp V := by simpa [σ.map_det, pm, inner, toBlocks₁₂, Matrix.map] using le_of_sq_le_sq ((norm_det_sq_le_of_posSemidef ((fromBlocks_toBlocks (pm (y ⊕ᵥ y) (cond ·.isLeft ((starRingAut.trans σ).trans starRingAut) σ))).substr pm_psd)).trans (by rw [sq]; gcongr <;> apply h)) V.exp_nonneg
include hz
lemma covolumeSq_le : covolumeSq z σ ≤ exp (k * β) := by grw [covolumeSq, hadamard_det_inequality pm_psd, exp_nat_mul, ← Fin.prod_const]; gcongr; simpa [↓← Complex.re_eq_norm.2 pm_psd.diag_nonneg, pm, normSqAt, weylNormSq, ← Complex.reLm_coe] using hz _
lemma covolumeSq_elim_le (h : covolumeSq y σ ≤ exp V) : covolumeSq (y ⊕ᵥ z) σ ≤ exp (V + k * β) := by grw [exp_add, ← h, ← covolumeSq_le hz]; exacts [fischer_det_inequality pm_psd, norm_nonneg _]
