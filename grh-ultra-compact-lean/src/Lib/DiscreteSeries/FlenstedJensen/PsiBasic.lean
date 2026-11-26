import Lib.DiscreteSeries.FlenstedJensen.FlenstedJensenInvariance
import Lib.DiscreteSeries.Holomorphic.HolomorphicExtension
open Matrix MeasureTheory ComplexConjugate ComplexOrder U
variable {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) (g : USign ε)
attribute [local simp] flenstedJensen dsCoeff ne_of_gt
attribute [local simp↓ ←] maxCompactU.coe_inv principalMinor_coe_inv integral_conj
lemma wUI w : weightMinors w g.1.1⁻¹ = conj (weightMinors w g) := by simp [↓conj_weightMinors, weightMinors, ← principalMinor_of_forall (p := ⊤)]
instance {J : Matrix n n ℂ} : SigmaCompactSpace (U J) := inferInstance
@[simp] lemma dsCoeff_one : l.dsCoeff 1 = 1 := by simp [RCLike.mul_conj, field]; norm_cast
include hg
lemma dsCoeff_polar (p q : maxCompactU ε) {z : USign ε} (hz : z.1.1.PosDef) : l.dsCoeff (p * z * q⁻¹ :) = (∫ u, weightMinors l.lowestKType (p * u.1) * conj (weightMinors l.lowestKType (q * u)) / weightMinors (-paramAddRho l) (u.1.1.1ᴴ * z * u) ∂haarK ε) / l.lowestKType.kTypeNormSq := by rw [dsCoeff_eq_flenstedJensen hg (mem_maxCompactU.1 (p * q⁻¹).2), flenstedJensen, ← integral_mul_left_eq_self _ q]; simp [mul_assoc]; simpa [mul_assoc] using hz.isAccretive.conjTranspose_mul_mul (k := ↑q⁻¹)
lemma dsCoeff_inv : l.dsCoeff ↑g⁻¹ = conj (l.dsCoeff g) := by obtain ⟨k, z, ⟨hz⟩⟩ := exists_polar g; obtain ⟨⟩ := dsCoeff_polar hg 1 k (z := z⁻¹) (by simpa), dsCoeff_polar hg k 1 hz, (wUI <| ·⁻¹ * z * ·); simp_all [mul_assoc, mul_comm]
@[simp] lemma dsCoeff_neg : (-l).dsCoeff g = conj (l.dsCoeff g) := by obtain ⟨k, z, ⟨b⟩⟩ := exists_polar g; obtain ⟨⟩ := dsCoeff_polar hg k 1 b, dsCoeff_polar hg.neg k 1 b; simp_all [kTypeNormSq, (by grind [two_mul_paramAddRho, hg.neg, twoRho_neg, Pi.neg_def] : paramAddRho (-l) = -paramAddRho l)]; norm_cast; simp [↓weightMinors_neg, ↓wUI]
lemma dsCoeff_of_mem_maxCompactU {k} (hk : k ∈ maxCompactU ε) : l.dsCoeff k = weightMinors l.lowestKType k := by simp_all [mem_maxCompactU,
  by simpa using (isHolOfWeight_weightMinors hg.neg.1 k fun () ↦ hg.isKDominant_lowestKType).integral_mul_conj_weightMinors hg.neg.1 hg.isKDominant_lowestKType]
