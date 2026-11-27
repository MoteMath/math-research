import MinkowskiRaneySingularityEngine

namespace MinkowskiRaneySingularityEngineChallenge

open RaneyMinkowski RaneyMinkowski.RaneyCert
open RatQ Mat2

theorem minkowskiQ_sbMat_mediant (w : List Bool) :
    mediantQ (sbMat w) ≈q dyadMid w :=
  _root_.RaneyMinkowski.minkowskiQ_sbMat_mediant w

theorem hellinger_tv_singularity {n : Nat} {C : RaneyCert n} (H : HellingerCert C)
    (k : Nat) (s : Fin n) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (C.mat s * sbMat w)))
      ≤q mkPos (H.v s) H.vMin H.vMin_pos * (mkPos H.rNum H.rDen H.rDen_pos).pow k :=
  _root_.RaneyMinkowski.RaneyCert.hellinger_tv_singularity H k s

theorem singularity_D2 (k : Nat) :
    sumWordsQ k (fun w => minQ (dyad 1 k) (colMeasure (⟨1, 0, 0, 2⟩ * sbMat w)))
      ≤q mkPos 65 57 (by decide) * (mkPos 63 64 (by decide)).pow k :=
  _root_.RaneyMinkowski.singularity_D2 k

theorem bit_expansion_D2 (k : Nat) :
    2 * RaneyCert.sumFinList 4 (fun s => stationaryD2.pi s * sumWordsNat k (fun w => (certD2.runEmit s w).length)) =
    k * 2 ^ k * 14 :=
  _root_.RaneyMinkowski.bit_expansion_D2 k

theorem integral_convergence_D2 (k : Nat) :
    abs (RaneyCert.avgMediantQ ⟨1, 0, 0, 2⟩ k - mkPos 9 13 (by decide))
      ≤q mkPos 65 48 (by decide) * (mkPos 9 16 (by decide)).pow k :=
  _root_.RaneyMinkowski.integral_convergence_D2 k

theorem exact_closed_form_D2 (k : Nat) :
    RaneyCert.avgMediantQ ⟨1, 0, 0, 2⟩ k ≈q
      mkPos 9 13 (by decide) + mkPos (d2Seq k).1 (52 * 8 ^ k) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) :=
  _root_.RaneyMinkowski.exact_closed_form_D2 k

theorem row_col_duality_D5 :
    (∀ s : Fin 15, rowMeasure (certD5.mat s) ≈q mkPos (stationaryD5.pi s) 16 (by decide)) ∧
    sumFinQ 15 (fun s => rowMeasure (certD5.mat s)) ≈q ofNat 6 ∧
    sumFinQ 15 (fun s => rowMeasure (certD5.mat s) * dyad ((certD5.emit s false).length + (certD5.emit s true).length) 1)
      ≈q sumFinQ 15 (fun s => colMeasure (certD5.mat s)) :=
  _root_.RaneyMinkowski.row_col_duality_D5

theorem sharpness_hellinger_const_counterexample :
    2 * 181 * 181 < 256 * 256 ∧
    ¬ (RaneyCert.hWeight 181 256 (by decide) (1 + 1) ≤q
       RaneyCert.hWeight 181 256 (by decide) 1 * RaneyCert.hWeight 181 256 (by decide) 1) :=
  _root_.RaneyMinkowski.sharpness_hellinger_const_counterexample

end MinkowskiRaneySingularityEngineChallenge
