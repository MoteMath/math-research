import Lib.Weil.Construction.SubmoduleNormedSpace
import Lib.DiscreteSeries.CuspKernel.CircleMean
variable {B A} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] (B₀ : AddSubgroup B) [CompactSpace (B ⧸ B₀)] (F : B → ℂ) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (A₀ : AddSubgroup A) [CompactSpace (A ⧸ A₀)] (φ : A →+ B)
def IsContPeriodic := Continuous F ∧ ∀ᵉ (γ ∈ B₀) (x), F (γ + x) = F x
scoped instance IsDualFamily.quotMeasurableSpace : MeasurableSpace (B ⧸ B₀) := borel _
open IsDualFamily MeasureTheory QuotientAddGroup Function
instance : BorelSpace (B ⧸ B₀) := ⟨rfl⟩
instance : @IsProbabilityMeasure (B ⧸ B₀) _ (.addHaarMeasure ⊤) := ⟨Measure.addHaarMeasure_self⟩
noncomputable def quotMean := ∫ q : B ⧸ B₀, F q.out ∂.addHaarMeasure ⊤
lemma norm_quotMean_le {F C} (h : ∀ x, ‖F x‖ ≤ C) : ‖quotMean B₀ F‖ ≤ C := by
 grw [quotMean, norm_integral_le_of_norm_le_const] <;> aesop
variable {B₀ F} (h : IsContPeriodic B₀ F)
@[simp] lemma quotMean_const_mul c F : quotMean B₀ (c * F ·) = c * quotMean B₀ F := integral_const_mul ..
@[simp] lemma quotMean_const c : quotMean B₀ (fun _ ↦ c) = c := by simp [quotMean]
include h
omit [IsTopologicalAddGroup B] [CompactSpace (B ⧸ B₀)] in lemma IsContPeriodic.apply_out_mk x : F (mk x : B ⧸ B₀).out = F x := by grind [mk_out_eq_add B₀ x, add_comm, IsContPeriodic]
omit [IsTopologicalAddGroup B] [CompactSpace (B ⧸ B₀)] in lemma IsContPeriodic.continuous_out : Continuous (F ·.out : B ⧸ B₀ → ℂ) := ⟨(funext h.apply_out_mk ▸ h.1).1⟩
lemma IsContPeriodic.integrable_out : Integrable (F ·.out : B ⧸ B₀ → ℂ) (.addHaarMeasure ⊤) := h.continuous_out.integrable_of_hasCompactSupport (.of_compactSpace _)
lemma quotMean_translate a : quotMean B₀ (F <| · + a) = quotMean B₀ F := .trans (by simp [quotMean, ← h.apply_out_mk]) (integral_add_right_eq_self _ ↑a)
lemma quotMean_quotMean [SecondCountableTopology A] {A'} [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] A₁ [CompactSpace (_ ⧸ A₁)] (φ : A × A' →+ B) (hφ : Continuous φ) (h₀ : ∀ a ∈ A₀, ∀ b ∈ A₁, φ (a, b) ∈ B₀) (hs : Surjective φ) : quotMean A₀ (fun a ↦ quotMean A₁ (F <| φ ⟨a, ·⟩)) = quotMean B₀ F := by
 let T := (map (.prod ..) _ φ fun _ k ↦ h₀ _ k.1 _ k.2).comp (prodAddEquiv ..).symm.toAddMonoidHom
 simpa [quotMean, ← h.apply_out_mk, show ∀ x, φ x = T (x.1, x.2) by tauto] using!
   ((T.measurePreserving ((isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff.1 (continuous_mk.comp
 hφ)) ((mk_surjective.comp hs).of_comp (g := .map mk mk)) (by simp)).fubini h.integrable_out).2
lemma quotMean_comp (h₀ : ∀ a ∈ A₀, φ a ∈ B₀) (hs : Surjective φ) (hφ : Continuous φ := by
   simp; fun_prop) : quotMean A₀ (F <| φ ·) = quotMean B₀ F := by simp [← quotMean_quotMean (A :=
 Unit) ⊤ h _ (φ.comp (.snd ..)) hφ.snd' (fun _ _ ↦ h₀) (by aesop_cat)]
