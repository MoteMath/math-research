import Lib.Shimura.TraceFormula.DefiniteTrace
import Lib.Adelic.CuspForms.WeightParameter
variable {a} {ι : Type} [Fintype ι]
lemma det_zpow_add {r : Fin a → ℂ} {g : GL (Fin a) ℂ} (h : ∀ i, g.1.charpoly.IsRoot (r i)) d (k : _ → ℤ) : (Matrix.of fun i j ↦ r i ^ (d + k j)).det = Finset.univ.prod r ^ d * (Matrix.of (r · ^ k ·)).det := by simpa [← Finset.prod_zpow, zpow_add₀ (spectrum.ne_zero_of_mem_of_unit (Matrix.mem_spectrum_of_isRoot_charpoly (h _)))] using! Matrix.det_mul_column ..
lemma trace_weylRep κ e {g : ι → GL (Fin a) ℂ} {x : ι → Fin a ↪ ℂ} (hg : ∀ v i, (g v).1.charpoly.IsRoot (x v i)) : (weylRep κ e g).trace * ∏ v, (Matrix.vandermonde (x v)).det = ∏ v, Matrix.det (.of fun i j : Fin a ↦ x v i ^ (e v + ↑(diagramWeight (rankAt (Fin a)) κ (v, j.rev) + j))) := by
 choose h hh using (isConj_diagonal_of_isRoot_charpoly <| hg ·); rw [← mul_inv_cancel_right g h, map_mul, Matrix.trace_mul_comm, ← map_mul]; simpa [weylRep, ← (hh _).eq, mul_assoc, Units.smul_def, det_zpow_add (hg _)] using .inl
  (weyl_character 1 _)
