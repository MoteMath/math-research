/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HilbertMooreCornerGlueLocality

/-!
# Verified Solutions (`hilbert-moore-corner-glue-locality`)
-/

namespace HilbertMooreCornerGlueLocalityChallenge

open SiliconHilbert

theorem hilbert2D_bijective_bv (w : Nat) (x : BitVec (2 * w)) :
    hilbert2D.invEvalBV hilbert2D_bijCert w ⟨0, by decide⟩ (hilbert2D.evalBV w ⟨0, by decide⟩ x) = x ∧
    hilbert2D.evalBV w ⟨0, by decide⟩ (hilbert2D.invEvalBV hilbert2D_bijCert w ⟨0, by decide⟩ x) = x :=
  SiliconHilbert.hilbert2D_bijective_bv w x

theorem hilbert2D_unit_step_and_hamming (w t : Nat) (ht : t + 1 < 2 ^ (2 * w)) :
    hilbert2D.l1Dist w ⟨0, by decide⟩ t (t + 1) = 1 ∧
    hilbert2D.hammingDist w ⟨0, by decide⟩ t (t + 1) = 1 + valBase 4 (t + 1) :=
  SiliconHilbert.hilbert2D_unit_step_and_hamming w t ht

theorem hilbert2D_total_switching_energy (w : Nat) :
    3 * sumFin (2 ^ (2 * w) - 1) (fun t => hilbert2D.hammingDist w ⟨0, by decide⟩ t (t + 1)) + 3 * w =
      4 * (2 ^ (2 * w) - 1) :=
  SiliconHilbert.hilbert2D_total_switching_energy w

theorem hilbert2D_holder_l1_locality (w u v : Nat) (huv : u ≤ v) (hv : v < 2 ^ (2 * w)) :
    (hilbert2D.l1Dist w ⟨0, by decide⟩ u v) ^ 2 ≤ 16 * (v - u) :=
  SiliconHilbert.hilbert2D_holder_l1_locality w u v huv hv

theorem hilbert2D_twoCycle_binomial (w : Nat) (hw : w ≥ 1) :
    hilbert2D.fixCount w ⟨0, by decide⟩ = fib (w + 1) ∧
    hilbert2D.fixCount2 w ⟨0, by decide⟩ ⟨0, by decide⟩ = fib (w + 1) * fib (w + 1) ∧
    hilbert2D.twoCyclePts w ⟨0, by decide⟩ = fib (w + 1) * (fib (w + 1) - 1) :=
  SiliconHilbert.hilbert2D_twoCycle_binomial w hw

theorem hilbert2D_orbit_3smooth (w : Nat) (s : Fin 4) (x : BitVec (2 * w)) :
    BitBlockTransducer.iter (hilbert2D.evalBV w s) (12 ^ w) x = x :=
  SiliconHilbert.hilbert2D_orbit_3smooth w s x

theorem moore2D_hamiltonian_cycle (w : Nat) :
    (∀ t < 2 ^ (2 * (w + 1)),
      d4Hilbert.invRootInterleaved d4Hilbert_bijCert d4Hilbert_glueCert moore2D_rootCert w
        (d4Hilbert.evalRootInterleaved d4Hilbert_glueCert moore2D_rootCert w t) = t) ∧
    (∀ y < 2 ^ (2 * (w + 1)),
      d4Hilbert.evalRootInterleaved d4Hilbert_glueCert moore2D_rootCert w
        (d4Hilbert.invRootInterleaved d4Hilbert_bijCert d4Hilbert_glueCert moore2D_rootCert w y) = y) ∧
    (∀ t < 2 ^ (2 * (w + 1)),
      d4Hilbert.l1RootDist d4Hilbert_glueCert moore2D_rootCert w t ((t + 1) % 2 ^ (2 * (w + 1))) = 1) :=
  SiliconHilbert.moore2D_hamiltonian_cycle w

theorem hilbert3D_fixCount_fibonacci (w : Nat) :
    hilbert3D.fixCount w ⟨0, by decide⟩ = fib (w + 2) :=
  SiliconHilbert.hilbert3D_fixCount_fibonacci w

end HilbertMooreCornerGlueLocalityChallenge
