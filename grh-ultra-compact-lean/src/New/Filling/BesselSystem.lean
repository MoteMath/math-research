import New.Filling.EichlerFlag
import Lib.DiscreteSeries.CuspKernel.BesselSchurBound
noncomputable section
open MeasureTheory Matrix ComplexConjugate Real Fintype Set Norms.L2Operator
variable (𝔰 : Shape)
def Shape.openCellConst := volU 𝔰.k / volU 𝔰.r * sphereDensity 𝔰.k 1
lemma Shape.openCellConst_pos : 0 < 𝔰.openCellConst := by simp [openCellConst]; positivity
def Shape.bandConst := volU 𝔰.k / volU 𝔰.r * π ^ ((2 * 𝔰.ϱ + 1) * 𝔰.k)
variable {𝔰} (y : 𝔰.G₁) {I : Type} [Fintype I] (b) (W : 𝔰.G₁ → EuclideanSpace ℂ I) (deg f)
def besselSize := ⨅ s : besselS, ‖(s.1 * y).1.1‖ + 1
abbrev InCut := besselSize y ≤ b ^ (6 * 𝔰.n + 2)
def frameBox ρ := {y : 𝔰.G₁ | ∀ a, ‖frameVector y a‖ ≤ ρ}
def gramDiscReal (Z : 𝔰.FrameMat) := (frameDisc 1 Z).re
def cellMass ρ d := (ρ ^ (9 * 𝔰.n) / gramDiscReal (realFrameGram y)) ^ (10 ^ 5 * 𝔰.n ^ 4) * (d ^ 2 / (deg * 𝔰.openCellConst * (gramDiscReal (realFrameGram y) / 2) ^ (𝔰.k - 1)))
def besselCorrelation {G I} [Group G] [MeasurableSpace G] (μ : Measure G) (W : G → EuclideanSpace ℂ I) (γ : G) : EuclideanSpace ℂ (I × I) := .toLp 2 fun x ↦ ∫ y, W y x.1 * conj (W (γ⁻¹ * y) x.2) ∂μ
def SchurLe D := ∀ φ : _ → ℂ, Integrable φ → ∫⁻ γ, ‖∫ y, φ y • W (γ * y)‖ₑ ^ 2 ∂besselQuotMeasure ≤ D * ∫⁻ y, ‖φ y‖ₑ ^ 2
def HasSchurBound rep B D := ∃ V : _ → C(_, _), W = V [] ∧ ∀ w, IsBesselFunction rep (V w) ∧ (∀ (γ : ℝ → 𝔰.G₁) X t, HasDerivAt (γ · |>.1.1) (γ t * X) t → HasDerivAt (V w ∘ γ) (∑ a, ∑ b, X a b • V ((a, b) :: w) (γ t)) t) ∧ (w.length ≤ 2 * 𝔰.n ^ 2 → SchurLe (V w) (.ofReal (B ^ (2 * w.length)) * D))
def normCorrelation p := (√𝔰.openCellConst * √(‖(p 𝔰.ϱ).1‖ ^ 2 - 1) ^ (𝔰.k - 1) / card I * ∏ a ∈ .range 𝔰.ϱ, ‖(p a).1‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))) • besselCorrelation volume W
  (weylElem 𝔰.ϱ p * y)
def HasBandLimits J := SieveSystem unitOrOne (·⁻¹.1) 𝔰.ϱ J wave ((1 + b⁻¹ ^ 10) / deg) (headWeight (𝔰.n ^ 6)) (fun ξ ↦ 𝔰.bandConst * b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) ‖ξ‖⁻¹) ∧ ∀ σ ∈ GT 𝔰.ϱ, ∀ p q, realFrameGram σ 𝔰.top 𝔰.top = p 𝔰.ϱ → q 𝔰.ϱ = p 𝔰.ϱ → J 𝔰.n p q = inner ℂ (normCorrelation σ W p) (normCorrelation σ W q)
class inductive Side | full | cut
structure IsCutPair rep (W : Side → C(𝔰.G₁, EuclideanSpace ℂ I)) where
  isBesselFunction t : IsBesselFunction rep (W t)
  integrable : Integrable (W .full) besselQuotMeasure
  lintegral_sq_full_eq : ∫⁻ y, ‖W .full y‖ₑ ^ 2 ∂besselQuotMeasure = card I
  lintegral_sq_cut_le : ∫⁻ y, ‖W .cut y‖ₑ ^ 2 ∂besselQuotMeasure ≤ card I
  inCut_of_ne_zero y : W .cut y ≠ 0 → InCut y b
  lintegral_sq_sub_le : ∫⁻ y, ‖W .cut y - W .full y‖ₑ ^ 2 ∂besselQuotMeasure ≤ .ofReal (b⁻¹ ^ (5 * 𝔰.r ^ 2)) ^ 2 * card I
  exists_majorant : ∃ A, ∃ m : Measure _, Measurable A ∧ besselU.FixesLeft A ∧ (∀ t y, ite (W .full y = W .cut y) 1 (.ofReal (b ^ (3 * 𝔰.r ^ 3 * f))) * ‖W t y‖ₑ ≤ A y) ∧ (∀ y, A y ≤ m {g | InCut (y * g) b}) ∧ IsFiniteMeasure m ∧ m univ * ∫⁻ y, A y ∂besselQuotMeasure ≤ .ofReal (b ^ (2 * 𝔰.r ^ 3)) * card I
variable (𝔰)
structure BesselSystem where
  (I) [fintype : Fintype I] [nonempty : Nonempty I]
  W : _ → C(𝔰.G₁, EuclideanSpace ℂ I)
  (deg : ℝ) (deg_pos : 0 < deg) (rep) tail : IsCutPair b f rep W
  irreducible M : (∀ h, Commute M (rep h).1) → M ∈ range (scalar I)
  hasSchurBound : ∀ P ≥ b ^ 5, HasSchurBound (W .full) rep P (.ofReal deg⁻¹ * card I)
  eight_mul_rank_le : 8 * 𝔰.r ≤ b
  (bandLimit) band_limits : HasBandLimits b (W .cut) deg bandLimit
attribute [instance] Side.full BesselSystem.fintype BesselSystem.nonempty
