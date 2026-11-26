import Lib.Weil.GaussSum.LocalHomUnit
import Lib.Adelic.Witt.FrameAction
variable {X} [TopologicalSpace X] {s : Set X} {φ Γ Y Z} {F : Type} [TopologicalSpace Γ] [TopologicalSpace Y]
def schwartzBruhat s := Submodule.ofLinearComb {f : X → ℂ | IsLocallyConstant f ∧ HasCompactSupport f ∧ f.support ⊆ s} ⟨0, .zero, .zero, nofun⟩ fun _ ⟨f, p, _⟩ _ ⟨g, q, _⟩ a b ↦
  ⟨f.comp₂ g (a * · + b * ·), p.mul_left.add q.mul_left, by simp_all; grind⟩
lemma schwartzBruhat.comp [T2Space X] {t : Set Y} (h : φ ∈ schwartzBruhat s) {f} g (hs : s.MapsTo g t) (hf : Continuous f := by fun_prop) (hg : Continuous g := by fun_prop)
  (hi : g.LeftInverse f := by intro; aesop) : φ ∘ f ∈ schwartzBruhat t := ⟨h.1.comp_continuous hf,
  h.2.1.comp_isClosedEmbedding (hi.isClosedEmbedding hg hf), (hi · ▸ h.2.2.trans hs ·)⟩
lemma schwartzBruhat.isLocallyConstant_curry (h : φ ∈ schwartzBruhat s) (f : Γ → Y → X) (g : Γ → X → Y) (hi : ∀ γ y, g γ (f γ y) = y := by
  simp) (hf : Continuous ↿f := by fun_prop) (hg : Continuous ↿g := by fun_prop) : IsLocallyConstant
  fun γ y ↦ φ (f γ y) := (IsLocallyConstant.iff_exists_open _).2 fun k ↦ let : UniformSpace ℂ := ⊥
  (exists_nhds_square (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
  ((ContinuousMap.comp ⟨_, h.1.continuous⟩ (.mk fun ((a, b), x) ↦ f a (g b x))).curry.2.tendsto (k,
  k)) _ h.2.1 _ .rfl)).imp (by simp [Set.subset_def]; grind [subset_tsupport φ, Function.support])
open MeasureTheory
lemma integral_mem_of_isLocallyConstant [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (μ : Measure Y) [IsFiniteMeasure μ] {f : Y → Z → ℂ} (l : IsLocallyConstant f) {P : Submodule ℂ _} (h : ∀ g, f g ∈ P) : (∫ g, f g · ∂μ) ∈ P := by
  convert P.sum_smul_mem (μ.real <| f ⁻¹' {·}) (t := l.range_finite.toFinset) (f := id) (by simpa); simp [← integral_indicator_const, (l _).measurableSet]
  rw [← integral_finsetSum] <;> simp [Set.indicator, Integrable.indicator, (l _).measurableSet]
class SemilocalField F extends CommRing F, TopologicalSpace F, MeasureSpace F, IsTopologicalRing F,
   PolishSpace F, LocallyCompactSpace F, BorelSpace F, volume.IsAddHaarMeasure where
  O : Subring F
  ϖ : Fˣ
  ϖ_mem : ↑ϖ ∈ O
  isCompact_O : @IsCompact F _ O
  volume_O : volume O = 1
  isOpen_O : _root_.IsOpen O.carrier
  unif_nilpotent : IsTopologicallyNilpotent ϖ.1
  valPair : IsValuationPair O
variable [V : SemilocalField F] (χ : MulChar F ℂ)
@[simp] abbrev IsIntegralUnit (x : F) := x ∈ SemilocalField.O ∧ ∃ s ∈ SemilocalField.O, s * x = 1
noncomputable def invOnUnits x := ite (IsIntegralUnit x) (χ x)⁻¹ 0
class TameLocalChar where
  (ResidueRing) [commRing : CommRing ResidueRing] [finite : Finite ResidueRing] (reduction :
   V.O →+* ResidueRing) (resChar) reduction_spec : (⇑reduction).Surjective ∧ ∀ x, reduction x = 0 ↔
   SemilocalField.ϖ⁻¹.1 * x.1 ∈ SemilocalField.O
  resChar_spec : IsPrimitiveMulChar resChar ∧ ∀ x, invOnUnits χ x.1 = resChar (reduction x)
attribute [instance_reducible, instance] TameLocalChar.commRing
attribute [instance] TameLocalChar.finite
lemma isIntegralUnit_iff_isUnit {u : V.O} : IsIntegralUnit u.1 ↔ IsUnit u := by simp [isUnit_iff_exists_inv', Subtype.ext_iff]
def HasIntegralConductor (ψ : AddChar F ℂ) := Continuous ψ ∧ ∀ t, (∀ s ∈ SemilocalField.O, ψ (t * s) = 1) ↔ t ∈ SemilocalField.O
