import Lib.General.LinearAlgebra.PartialDerivComm
open AddSubgroup MeasureTheory Set
attribute [simp] lintegral_count withDensity_smul_measure ENNReal.tsum_prod' ENNReal.tsum_mul_left ENNReal.tsum_mul_right
variable {H X G} [MeasurableSpace H] [MeasurableSpace X] [SMul H X] (ν : Measure H) (μ : Measure X) [Group G] (N : Subgroup G) [TopologicalSpace G]
@[to_additive] abbrev Subgroup.Cocpt := ∃ C, IsCompact C ∧ ∀ g, ∃ γ ∈ N, γ * g ∈ C
@[simp] abbrev Subgroup.FixesLeft {W} (F : G → W) := ∀ γ ∈ N, ∀ g, F (γ * g) = F g
@[to_additive IsAddCutoff] def IsCutoff β := Measurable β ∧ ∀ x : X, ∫⁻ h, β (h • x) ∂ν = 1
@[to_additive addOrbitMeasure] noncomputable abbrev orbitMeasure := μ.withDensity (Classical.epsilon (IsCutoff ν))
@[to_additive HasAddCutoff] abbrev HasCutoff X [MeasurableSpace X] [SMul H X] := Fact (∃ β, IsCutoff (X := X) ν β)
@[to_additive] instance (priority := high) mulActionSubgroupSelf : MulAction N G := inferInstance
@[to_additive] instance (priority := high) smulSubgroupSelf : SMul N G := inferInstance
@[to_additive] noncomputable abbrev Subgroup.qms [MeasurableSpace G] (μ : Measure G := by volume_tac) := orbitMeasure (@Measure.count N _) μ
variable {V} {X : Type*} [AddCommGroup V] [MeasurableSpace V] {ν : Measure V} [ν.IsAddLeftInvariant] {M L : AddSubgroup V} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace V] [IsTopologicalAddGroup V] [BorelSpace V]
lemma setIntegral_add_mem (F : V → X) {m} : m ∈ M → ∫ x in M, F (m + x) ∂ν = ∫ x in M, F x ∂ν := by simp_all [← (measurePreserving_add_left ..).setIntegral_image_emb (measurableEmbedding_addLeft m), preimage, add_mem_cancel_left]
lemma setIntegral_char (ho : @IsOpen V _ M) {χ : V → ℂ} (h : ∀ x y, χ (x + y) = χ x * χ y) : ∫ x in M, χ x ∂ν = ite (∀ x ∈ M, χ x = 1) ↑(ν.real M) 0 := by
  split; simp [setIntegral_congr_fun ho.measurableSet ‹_›]; by_contra
  simp_all [← mul_eq_right₀ this, ← integral_const_mul, ← h, setIntegral_add_mem]
lemma setIntegral_eq_finsum [IsFiniteMeasureOnCompacts ν] [CompleteSpace X] [T2Space V] (hc : @IsCompact V _ M) (hL : @IsOpen V _ L) {F : V → X} (hF : ∀ x y : M, -x.1 + y ∈ L → F y = F x) : ∫ x in M, F x ∂ν = ν.real (L ∩ M) • ∑ᶠ q : M ⧸ L.addSubgroupOf M, F q.out := by
  have := fintypeOfIndexNeZero (hc.relIndex_ne_zero_add hL); rw [setIntegral_congr_fun hc.measurableSet, integral_finsetSum]
  simpa [Finset.smul_sum, hL.measurableSet] using this.sum_congr _ _
   fun q ↦ setIntegral_add_mem (indicator L fun _ ↦ F q.out) (-q.out).2
  all_goals intro x h
  exact (integrableOn_const hc.measure_ne_top).indicator (measurable_const_add _ hL.measurableSet); have := (@QuotientAddGroup.eq _ _ (L.addSubgroupOf M) · ⟨x, h⟩ |>.symm); simp_all [indicator, mem_addSubgroupOf, ← hF _ ⟨x, h⟩]
