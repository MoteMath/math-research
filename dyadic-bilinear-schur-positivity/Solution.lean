import DyadicBilinearSchurPositivity

namespace DyadicBilinearSchurPositivityChallenge

open DyadicPDEngine
open ZHalf

theorem soundness_strict_pd {m : Nat} (sys : BQS m) (Wtarget : Fin m → Fin m → ZHalf)
    (cert : PDCert m) (hcheck : checkStrictPD sys Wtarget cert = true) :
    ∀ (k : Nat) (x : Fin (2 ^ k) → ZHalf), (∃ i, x i ≠ 0) →
      0 < sys.Q k x + quadForm Wtarget (sys.L k x) :=
  _root_.DyadicPDEngine.soundness_strict_pd sys Wtarget cert hcheck

theorem v2Nat_xor_eq_absDiff (i j : Nat) : v2Nat (i ^^^ j) = v2Nat (absDiff i j) :=
  _root_.DyadicPDEngine.v2Nat_xor_eq_absDiff i j

theorem thm_monnaArch_strict_pd (k : Nat) (x : Fin (2 ^ k) → ZHalf) (hx : ∃ i, x i ≠ 0) :
    0 < dyad 1 1 * (muForm k x * muForm k x) - monnaArchForm k x :=
  _root_.DyadicPDEngine.thm_monnaArch_strict_pd k x hx

theorem monnaArch_direct_induction_fails :
    deltaMat sysArch WArchTarget ⟨0, by decide⟩ ⟨0, by decide⟩ *
    deltaMat sysArch WArchTarget ⟨3, by decide⟩ ⟨3, by decide⟩ -
    deltaMat sysArch WArchTarget ⟨0, by decide⟩ ⟨3, by decide⟩ *
    deltaMat sysArch WArchTarget ⟨3, by decide⟩ ⟨0, by decide⟩ < 0 :=
  _root_.DyadicPDEngine.monnaArch_direct_induction_fails

theorem adelic_kernels_noncommuting :
    sumFin (fun t : Fin 4 => riesz2AdicKernel 1 0 t.val * monnaArchKernel 2 t.val 2) ≠
    sumFin (fun t : Fin 4 => monnaArchKernel 2 0 t.val * riesz2AdicKernel 1 t.val 2) :=
  _root_.DyadicPDEngine.adelic_kernels_noncommuting

theorem thm_adelic_sharp_dipole_k1 :
    3 * (muForm 1 (vec2 1 0) * muForm 1 (vec2 1 0)) -
    4 * ((muForm 1 (vec2 1 0) - 2 * nuForm 1 (vec2 1 0)) *
         (muForm 1 (vec2 1 0) - 2 * nuForm 1 (vec2 1 0))) -
    3 * riesz2AdicForm 1 1 (vec2 1 0) - 2 * monnaArchForm 1 (vec2 1 0) < 0 :=
  _root_.DyadicPDEngine.thm_adelic_sharp_dipole_k1

theorem asym_nondiag_asymmetric_diag :
    sysAsym.F WAsymIndef 2 (basisFin4 ⟨0, by decide⟩) ≠
    sysAsym.F WAsymIndef 2 (basisFin4 ⟨3, by decide⟩) :=
  _root_.DyadicPDEngine.asym_nondiag_asymmetric_diag

theorem thm_asym_nondiag_sharp_W00 :
    sysAsym.F (mat2 0 2 2 (-2)) 1 (vec2 4 1) < 0 :=
  _root_.DyadicPDEngine.thm_asym_nondiag_sharp_W00

end DyadicBilinearSchurPositivityChallenge
