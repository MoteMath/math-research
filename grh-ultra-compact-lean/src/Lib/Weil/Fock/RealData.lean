import Lib.Weil.Construction.Projections
variable {E n s} [Field E] [CMType E] [WeilData E] [Fintype n] (V : Space E n s) (v w f f')
namespace Space
lemma dataInner_integrated : V.dataInner (V.integrated v f) (V.integrated w f') = realInner v w * V.dataInner (V.projReal f) (V.projReal f') := by
 simpa [mul_comm] using Heisenberg.IsVacuum.integral_form_eq_mul_modelInner (ν := .dirac ()) (fun _ ↦ .bilinearComp _
 (.flip _ f) (.flip _ f')) (by simp) (by simp [integrated_realHeisOp]) ..
lemma theta_integrated : V.θ (V.integrated v f) = ∫ y, v y * f (realVec y) ∂realMeasure _ := by simp [integrated, Heisenberg.Rep.map_integrated_eq_integral]
