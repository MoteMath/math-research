import CayleyHamiltonPerronAnnihilator.Defs

namespace CayleyHamiltonPerronAnnihilatorChallenge

open CHKAE

theorem matAnn_sound (cert : MatAnnCert) (u v : Vec cert.d) (h : checkMatAnn cert = true) :
    ∀ n : Nat,
      obs (toMat cert.d cert.d cert.M) u v (n + cert.c.length) =
      finSum cert.c.length (fun j => toVec cert.c.length cert.c j * obs (toMat cert.d cert.d cert.M) u v (n + j.val)) := by
  sorry

theorem scaledVal_exact_valuation (cert : ScaledValCert)
    (h : checkScaledVal cert = true)
    (hq_dvd : cert.q ∣ cert.m0)
    (hnonzero : cert.periodTable.all (fun a => a % cert.q != 0) = true) :
    ∀ n : Nat,
      cert.q ^ (n + cert.preShift) ∣
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0) ∧
      ¬ (cert.q ^ (n + cert.preShift + 1) ∣
        obs (toMat cert.d cert.d cert.M) (toVec cert.d cert.u) (toVec cert.d cert.v) (n + cert.n0)) := by
  sorry

/-- Exact semantic bridge for ALL `k ≥ 1` and ALL `n : Nat`. -/
theorem carrySumK_eq_obs (k : Nat) (hk : 1 ≤ k) (n : Nat) :
    carrySumK k n =
      obs (carryMat k) (fun c : Fin k => pm1 (popcount c.val))
          (fun c : Fin k => if c = ⟨0, hk⟩ then 1 else 0) n := by
  sorry

/-- **THEOREM 2a (Strict Positivity of `Z_5` and `K_7`):** For ALL `n : Nat`, both `Z_corr 5 n > 0` and `K_corr 7 n > 0`. -/
theorem thm_Z5_and_K7_pos : ∀ n : Nat, Z_corr 5 n > 0 ∧ K_corr 7 n > 0 := by
  sorry

theorem thm_C3_odd_part_mod4 : ∀ n : Nat, n ≥ 3 →
    ∃ t : Int, carrySumK 3 n = (2 : Int) ^ (n + 1) * t ∧
      t % 4 = (if n % 2 = 0 then 1 else 3) := by
  sorry

/-- **THEOREM 5b (Eventual Strict Positivity of `C_5` Beyond Descartes' Rule of Signs):** -/
theorem thm_C5_pos_for_all_ge_8 : ∀ n : Nat, n ≥ 8 → carrySumK 5 n > 0 := by
  sorry

/-- **Sharpness Witness 1 (Carried-vs-Carryless Positivity Fails at `c = 23`!):** -/
theorem sharpness_K23_fails : K_corr 23 3 = 0 ∧ K_corr 23 4 = -4 := by
  sorry

/-- **Sharpness Witness 5 (`+3` shift in `K_7(n+3) = 2*Z_5(n)` is sharp):** -/
theorem sharpness_K7_Z5_shift : K_corr 7 2 ≠ 2 * Z_corr 5 2 := by
  sorry

end CayleyHamiltonPerronAnnihilatorChallenge
