import CarryAutomatonKrylovL4Energy

namespace CarryAutomatonKrylovL4EnergyChallenge

open PureSiliconAuto

theorem apCorr_even {d : Nat} (A : BinAuto d) (p q : Fin d) (k t : Nat) :
    apCorr A p q (k + 1) (2 * t) =
      A.sig0 p * A.sig0 q * apCorr A (A.del0 p) (A.del0 q) k t +
      A.sig1 p * A.sig1 q * apCorr A (A.del1 p) (A.del1 q) k t :=
  _root_.PureSiliconAuto.apCorr_even A p q k t

theorem bijTail_infinite_flat_spectrum (m : Nat) (ψ : Fin (2 ^ m) → Bool) :
    (∀ k s, s ≥ 1 → sumFin (2 ^ (m + 1)) (fun q => apCorr (bijTailAuto m ψ) q q k s) = 0) ∧
    (∀ k (X : Int),
      sumFin (2 ^ (m + 1)) (fun q => polyEval (bijTailAuto m ψ) q k X * polyRevEval (bijTailAuto m ψ) q k X) =
      (2 : Int) ^ (k + m + 1) * X ^ (2 ^ k - 1)) ∧
    (∀ k,
      sumFin (2 ^ (m + 1)) (fun q =>
        sumRange (2 ^ k) (fun n => (bijTailAuto m ψ).eval q n) *
        sumRange (2 ^ k) (fun n => (bijTailAuto m ψ).eval q n)) =
      (2 : Int) ^ (k + m + 1)) :=
  _root_.PureSiliconAuto.bijTail_infinite_flat_spectrum m ψ

theorem innerQRZ_dualStep {d : Nat} (A : BinAuto d) (W : DualQRZ) (S : QRZFn (d * d)) :
    innerQRZ (d * d) (dualStep A W) S = innerQRZ (d * d) W (primalStep A S) :=
  _root_.PureSiliconAuto.innerQRZ_dualStep A W S

theorem paperfolding_direct_rec (n : Nat) :
    paperfoldingAuto.eval 0 (2 * n) = (if n % 2 = 0 then 1 else -1) ∧
    paperfoldingAuto.eval 0 (2 * n + 1) = paperfoldingAuto.eval 0 n :=
  _root_.PureSiliconAuto.paperfolding_direct_rec n

theorem baumSweet_classical_rec (n : Nat) :
    baumSweetAuto.eval 0 0 = 1 ∧
    baumSweetAuto.eval 0 (2 * n + 1) = baumSweetAuto.eval 0 n ∧
    baumSweetAuto.eval 0 (4 * n) = baumSweetAuto.eval 0 n ∧
    baumSweetAuto.eval 0 (4 * n + 2) = 0 :=
  _root_.PureSiliconAuto.baumSweet_classical_rec n

theorem mask6Cert_valid : checkWitnessedDualCert mask6Auto (dualTotE4 4) mask6Cert = true :=
  _root_.PureSiliconAuto.mask6Cert_valid

theorem mask6_totE4_rec (k : Nat) :
    totE4 mask6Auto (k + 5) =
      2 * totE4 mask6Auto (k + 4) + 16 * totE4 mask6Auto (k + 2) + 256 * totE4 mask6Auto k :=
  _root_.PureSiliconAuto.mask6_totE4_rec k

theorem rudinShapiro_E4_closed_form (k : Nat) (hk : k ≥ 1) :
    3 * E4State rudinShapiroAuto 0 k = (4 : Int) ^ (k + 1) - (-2 : Int) ^ k :=
  _root_.PureSiliconAuto.rudinShapiro_E4_closed_form k hk

end CarryAutomatonKrylovL4EnergyChallenge
