import CayleyHamiltonPerronAnnihilator

namespace CayleyHamiltonPerronAnnihilatorChallenge

open CHKAE

theorem matAnn_sound (cert : MatAnnCert) (u v : Vec cert.d) (h : checkMatAnn cert = true) :
    ∀ n : Nat,
      obs (toMat cert.d cert.d cert.M) u v (n + cert.c.length) =
      finSum cert.c.length (fun j => toVec cert.c.length cert.c j * obs (toMat cert.d cert.d cert.M) u v (n + j.val)) :=
  _root_.CHKAE.matAnn_sound cert u v h

theorem scaledVal_exact_valuation (cert : ScaledValCert)
    (h : checkScaledVal cert = true)
    (hq_dvd : cert.q ∣ cert.m0)
    (hnonzero : cert.periodTable.all (fun a => a % cert.q != 0) = true) :
    ∀ n : Nat,
      cert.q ^ (n + cert.preShift) ∣
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) ∧
      ¬ (cert.q ^ (n + cert.preShift + 1) ∣
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0)) :=
  _root_.CHKAE.scaledVal_exact_valuation cert h hq_dvd hnonzero

theorem carrySumK_eq_obs (k : Nat) (hk : 1 ≤ k) (n : Nat) :
    carrySumK k n =
      obs (carryMat k) (fun c : Fin k => pm1 (popcount c.val))
          (fun c : Fin k => if c = ⟨0, hk⟩ then 1 else 0) n :=
  _root_.CHKAE.carrySumK_eq_obs k hk n

theorem thm_Z5_and_K7_pos : ∀ n : Nat, Z_corr 5 n > 0 ∧ K_corr 7 n > 0 :=
  _root_.CHKAE.thm_Z5_and_K7_pos

theorem thm_C3_odd_part_mod4 : ∀ n : Nat, n ≥ 3 →
    ∃ t : Int, carrySumK 3 n = (2 : Int) ^ (n + 1) * t ∧
      t % 4 = (if n % 2 = 0 then 1 else 3) :=
  _root_.CHKAE.thm_C3_odd_part_mod4

theorem thm_C5_pos_for_all_ge_8 : ∀ n : Nat, n ≥ 8 → carrySumK 5 n > 0 :=
  _root_.CHKAE.thm_C5_pos_for_all_ge_8

theorem sharpness_K23_fails : K_corr 23 3 = 0 ∧ K_corr 23 4 = -4 :=
  _root_.CHKAE.sharpness_K23_fails

theorem sharpness_K7_Z5_shift : K_corr 7 2 ≠ 2 * Z_corr 5 2 :=
  _root_.CHKAE.sharpness_K7_Z5_shift

end CayleyHamiltonPerronAnnihilatorChallenge
