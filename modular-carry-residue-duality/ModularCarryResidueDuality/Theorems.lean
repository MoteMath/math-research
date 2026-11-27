/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ModularCarryResidueDuality.Defs

/-!
# Theorems (`ModularCarryResidueDuality`)

All proofs of the dual carry-residue engine, the Mersenne / negacyclic / Fermat families and sharpness witnesses.
-/

namespace ModularCarryResidueDuality

theorem halveStep_lt {m x : Nat} (hodd : m % 2 = 1) (hx : x < m) : halveStep m x < m := by
  unfold halveStep
  split <;> omega

theorem halveIter_lt {m x : Nat} (hodd : m % 2 = 1) (hx : x < m) (i : Nat) :
    halveIter m i x < m := by
  induction i with
  | zero => exact hx
  | succ i ih => exact halveStep_lt hodd ih

theorem two_mul_halveStep_mod {m x : Nat} (hodd : m % 2 = 1) :
    (2 * halveStep m x) % m = x % m := by
  unfold halveStep
  split
  · next he =>
    have : 2 * (x / 2) = x := by omega
    rw [this]
  · next ho =>
    have : 2 * ((x + m) / 2) = x + m := by omega
    rw [this, Nat.add_mod_right]

theorem pow2_mul_halveIter_mod {m x : Nat} (hodd : m % 2 = 1) (i : Nat) :
    (2 ^ i * halveIter m i x) % m = x % m := by
  induction i with
  | zero => simp [halveIter]
  | succ i ih =>
    simp only [halveIter]
    have hpow : 2 ^ (i + 1) * halveStep m (halveIter m i x) =
        2 ^ i * (2 * halveStep m (halveIter m i x)) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hpow, Nat.mul_mod, two_mul_halveStep_mod hodd, ← Nat.mul_mod, ih]

theorem halveStep_zero (m : Nat) : halveStep m 0 = 0 := by
  simp [halveStep]

theorem halveIter_zero (m i : Nat) : halveIter m i 0 = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [halveIter, ih, halveStep_zero]

theorem halvingOrbitSum_zero (m L : Nat) : halvingOrbitSum m 0 L = 0 := by
  unfold halvingOrbitSum
  rw [Nat.zero_mod, sumNat_eq_zero_iff]
  intro i _
  exact halveIter_zero m i

/-- Exact arithmetic specification of the MSB Euclidean division automaton. -/
theorem msb_spec {m : Nat} (hm : 0 < m) (L n : Nat) (hn : n < 2 ^ L) :
    remAt m hm L n 0 = n % m ∧ eucQuot m hm L n = n / m := by
  induction L generalizing n with
  | zero =>
    have h0 : n = 0 := by simp at hn; omega
    subst h0
    simp [remAt, eucQuot, stateMSB, stateMSBAux, zeroFin, outValMSB, sumNat]
  | succ L ih =>
    have hdiv : n / 2 < 2 ^ L := by rw [Nat.pow_succ] at hn; omega
    obtain ⟨hrem, hquot⟩ := ih (n / 2) hdiv
    have hstep :
        stateMSB (msbDivFin m hm) (zeroFin hm) (L + 1) n 0 =
          ((msbDivFin m hm).step
            (stateMSB (msbDivFin m hm) (zeroFin hm) L (n / 2) 0)
            (bitAt n 0)).1 := by
      rw [stateMSB_step _ _ _ _ 0 (by omega), stateMSB_succ_shift]
    have hbit0 : boolNat (bitAt n 0) = n % 2 := by rw [boolNat_bitAt]; simp
    have hprev_eq := msbDiv_step_eq hm
      (stateMSB (msbDivFin m hm) (zeroFin hm) L (n / 2) 0).isLt (bitAt n 0)
    have hrval : (stateMSB (msbDivFin m hm) (zeroFin hm) L (n / 2) 0).val = (n / 2) % m := hrem
    have h2n : 2 * ((n / 2) % m) + n % 2 =
        m * boolNat (outBitMSB (msbDivFin m hm) (zeroFin hm) (L + 1) n 0) +
          remAt m hm (L + 1) n 0 := by
      have h1 := hprev_eq.1
      have hst : remAt m hm (L + 1) n 0 =
          ((msbDivTransducer m).step
            (stateMSB (msbDivFin m hm) (zeroFin hm) L (n / 2) 0).val (bitAt n 0)).1 := by
        unfold remAt; rw [hstep]; rfl
      have hob : outBitMSB (msbDivFin m hm) (zeroFin hm) (L + 1) n 0 =
          ((msbDivTransducer m).step
            (stateMSB (msbDivFin m hm) (zeroFin hm) L (n / 2) 0).val (bitAt n 0)).2 := by
        unfold outBitMSB; rw [stateMSB_succ_shift]; rfl
      rw [hst, hob, ← hrval, ← hbit0]
      exact h1
    have hrem_lt : remAt m hm (L + 1) n 0 < m :=
      (stateMSB (msbDivFin m hm) (zeroFin hm) (L + 1) n 0).isLt
    have hmod_eq :
        (2 * ((n / 2) % m) + n % 2) % m = n % m := by
      have hn_eq : n = 2 * (n / 2) + n % 2 := by omega
      conv => rhs; rw [hn_eq]
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    have hrem_new : remAt m hm (L + 1) n 0 = n % m := by
      have h1 : (2 * ((n / 2) % m) + n % 2) % m = remAt m hm (L + 1) n 0 := by
        rw [h2n, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
      omega
    have hquot_new : eucQuot m hm (L + 1) n = n / m := by
      unfold eucQuot
      rw [outValMSB_succ]
      change boolNat (outBitMSB (msbDivFin m hm) (zeroFin hm) (L + 1) n 0) +
        2 * eucQuot m hm L (n / 2) = n / m
      rw [hquot]
      have hdiv2 : n / 2 = m * (n / 2 / m) + (n / 2) % m := by
        have := Nat.div_add_mod (n / 2) m; omega
      have hdivn : n = m * (n / m) + n % m := by
        have := Nat.div_add_mod n m; omega
      have hmul2 : m * (2 * (n / 2 / m)) = 2 * (m * (n / 2 / m)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
      have hcomb : m * (boolNat (outBitMSB (msbDivFin m hm) (zeroFin hm) (L + 1) n 0) +
            2 * (n / 2 / m)) + n % m = m * (n / m) + n % m := by
        rw [Nat.mul_add, hmul2, ← hrem_new]
        omega
      have : m * (boolNat (outBitMSB (msbDivFin m hm) (zeroFin hm) (L + 1) n 0) +
            2 * (n / 2 / m)) = m * (n / m) := by omega
      exact Nat.eq_of_mul_eq_mul_left hm this
    exact ⟨hrem_new, hquot_new⟩

theorem remAt_eq_div_mod {m : Nat} (hm : 0 < m) (L n i : Nat) (hi : i ≤ L) (hn : n < 2 ^ L) :
    remAt m hm L n i = (n / 2 ^ i) % m := by
  induction i generalizing L n with
  | zero =>
    simpa using (msb_spec hm L n hn).1
  | succ i ih =>
    cases L with
    | zero => omega
    | succ L =>
      have hdiv : n / 2 < 2 ^ L := by rw [Nat.pow_succ] at hn; omega
      have hshift : remAt m hm (L + 1) n (i + 1) = remAt m hm L (n / 2) i := by
        unfold remAt
        rw [stateMSB_succ_shift]
      rw [hshift, ih L (n / 2) (by omega) hdiv, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

/-- Exact arithmetic specification of the LSB 2-adic division carry transducer. -/
theorem lsb_spec {m : Nat} (hodd : m % 2 = 1) (n i : Nat) :
    m * twoAdicQuot m hodd i n = n % 2 ^ i + carryAt m hodd n i * 2 ^ i ∧
    twoAdicQuot m hodd i n < 2 ^ i := by
  induction i with
  | zero =>
    simp [twoAdicQuot, outValLSB, sumNat, carryAt, stateLSB, zeroFin, Nat.mod_one]
  | succ i ih =>
    obtain ⟨heq, hlt⟩ := ih
    have hstep := (lsbCarry_step_eq hodd
      (stateLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i).isLt (bitAt n i)).1
    have hq_def : twoAdicQuot m hodd (i + 1) n =
        twoAdicQuot m hodd i n +
          boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i) * 2 ^ i := by
      simp [twoAdicQuot, outValLSB, sumNat]
    have hmod_step : n % 2 ^ (i + 1) = n % 2 ^ i + boolNat (bitAt n i) * 2 ^ i := by
      rw [boolNat_bitAt, mod_pow2_succ]
    have hc_step : carryAt m hodd n i +
        m * boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i) =
        boolNat (bitAt n i) + 2 * carryAt m hodd n (i + 1) := hstep
    constructor
    · rw [hq_def, Nat.mul_add, heq, hmod_step]
      have h1 : m * (boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i) * 2 ^ i) =
          (m * boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i)) * 2 ^ i := by
        rw [Nat.mul_assoc]
      have h2 : carryAt m hodd n i * 2 ^ i +
          (m * boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i)) * 2 ^ i =
          (carryAt m hodd n i +
            m * boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i)) * 2 ^ i := by
        rw [Nat.add_mul]
      have h3 : (boolNat (bitAt n i) + 2 * carryAt m hodd n (i + 1)) * 2 ^ i =
          boolNat (bitAt n i) * 2 ^ i + carryAt m hodd n (i + 1) * 2 ^ (i + 1) := by
        rw [Nat.add_mul, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.mul_assoc,
            Nat.mul_comm 2 (carryAt m hodd n (i + 1)), Nat.mul_assoc]
      rw [h1]
      calc n % 2 ^ i + carryAt m hodd n i * 2 ^ i +
              (m * boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i)) * 2 ^ i
          = n % 2 ^ i + (carryAt m hodd n i * 2 ^ i +
              (m * boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i)) * 2 ^ i) := by omega
        _ = n % 2 ^ i + (carryAt m hodd n i +
              m * boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin (by omega)) n i)) * 2 ^ i := by rw [h2]
        _ = n % 2 ^ i + (boolNat (bitAt n i) + 2 * carryAt m hodd n (i + 1)) * 2 ^ i := by rw [hc_step]
        _ = n % 2 ^ i + (boolNat (bitAt n i) * 2 ^ i + carryAt m hodd n (i + 1) * 2 ^ (i + 1)) := by rw [h3]
        _ = n % 2 ^ i + boolNat (bitAt n i) * 2 ^ i + carryAt m hodd n (i + 1) * 2 ^ (i + 1) := by omega
    · exact sum_bool_val_lt (i + 1) _

theorem lsb_spec_full {m : Nat} (hodd : m % 2 = 1) (L n : Nat) (hn : n < 2 ^ L) :
    m * twoAdicQuot m hodd L n = n + carryAt m hodd n L * 2 ^ L := by
  have h := (lsb_spec hodd n L).1
  rw [Nat.mod_eq_of_lt hn] at h
  exact h

/-- Coprime cancellation for `2^i` mod odd `m`: if `2^i * a ≡ 2^i * b (mod m)` then `a ≡ b (mod m)`. -/
theorem mod_eq_of_pow2_mul_mod_eq {m a b : Nat} (hodd : m % 2 = 1) (i : Nat)
    (h : (2 ^ i * a) % m = (2 ^ i * b) % m) : a % m = b % m := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    apply ih
    have h2 : (2 * (2 ^ i * a)) % m = (2 * (2 ^ i * b)) % m := by
      have ha : 2 * (2 ^ i * a) = 2 ^ (i + 1) * a := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
      have hb : 2 * (2 ^ i * b) = 2 ^ (i + 1) * b := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
      rw [ha, hb]; exact h
    have hinv : (2 * ((m + 1) / 2)) % m = 1 % m := by
      have : 2 * ((m + 1) / 2) = m + 1 := by omega
      rw [this, Nat.add_mod_left]
    have hstep : ∀ x, ((m + 1) / 2 * (2 * x)) % m = x % m := by
      intro x
      have hassoc : (m + 1) / 2 * (2 * x) = (2 * ((m + 1) / 2)) * x := by
        rw [← Nat.mul_assoc, Nat.mul_comm ((m + 1) / 2) 2]
      rw [hassoc, Nat.mul_mod, hinv, ← Nat.mul_mod, Nat.one_mul]
    have hl := hstep (2 ^ i * a)
    have hr := hstep (2 ^ i * b)
    have hmul : ((m + 1) / 2 * (2 * (2 ^ i * a))) % m = ((m + 1) / 2 * (2 * (2 ^ i * b))) % m := by
      rw [Nat.mul_mod, h2, ← Nat.mul_mod]
    omega

/-- Pointwise Modular Coupling Lemma:
    At EVERY bit cut `i ≤ L`, `remAt_i - carryAt_i = halveIter_i (n % m) - m * 1[remAt_i < carryAt_i]`. -/
theorem pointwise_modular_coupling {m : Nat} (hodd : m % 2 = 1) (L n i : Nat)
    (hi : i ≤ L) (hn : n < 2 ^ L) :
    (remAt m (by omega) L n i : Int) - (carryAt m hodd n i : Int) =
      (halveIter m i (n % m) : Int) -
        (m : Int) * (if remAt m (by omega) L n i < carryAt m hodd n i then 1 else 0) := by
  have hm : 0 < m := by omega
  have hr_lt : remAt m hm L n i < m := (stateMSB (msbDivFin m hm) (zeroFin hm) L n i).isLt
  have hc_lt : carryAt m hodd n i < m := (stateLSB (lsbCarryFin m hodd) (zeroFin hm) n i).isLt
  have hrho_lt : halveIter m i (n % m) < m := halveIter_lt hodd (Nat.mod_lt n hm) i
  have hr_eq : remAt m hm L n i = (n / 2 ^ i) % m := remAt_eq_div_mod hm L n i hi hn
  have hc_eq := (lsb_spec hodd n i).1
  have hcong : (2 ^ i * (remAt m hm L n i + m - carryAt m hodd n i)) % m =
      (2 ^ i * halveIter m i (n % m)) % m := by
    rw [pow2_mul_halveIter_mod hodd i, Nat.mod_mod]
    have hsplit : n = 2 ^ i * (n / 2 ^ i) + n % 2 ^ i := by
      have := Nat.div_add_mod n (2 ^ i); omega
    have h1 : (n + carryAt m hodd n i * 2 ^ i) % m = (2 ^ i * (n / 2 ^ i) + m * twoAdicQuot m hodd i n) % m := by
      congr 1; omega
    have h2 : (n + carryAt m hodd n i * 2 ^ i) % m = (2 ^ i * remAt m hm L n i) % m := by
      rw [h1, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod,
          Nat.mul_mod, ← hr_eq, ← Nat.mod_eq_of_lt hr_lt]
      conv => rhs; rw [Nat.mul_mod, Nat.mod_eq_of_lt hr_lt]
    have h3 : (2 ^ i * (remAt m hm L n i + m - carryAt m hodd n i) +
               carryAt m hodd n i * 2 ^ i) % m = (2 ^ i * remAt m hm L n i) % m := by
      have heq : 2 ^ i * (remAt m hm L n i + m - carryAt m hodd n i) +
                 carryAt m hodd n i * 2 ^ i =
                 2 ^ i * remAt m hm L n i + m * 2 ^ i := by
        have hsum : remAt m hm L n i + m - carryAt m hodd n i + carryAt m hodd n i =
               remAt m hm L n i + m := by omega
        calc 2 ^ i * (remAt m hm L n i + m - carryAt m hodd n i) + carryAt m hodd n i * 2 ^ i
            = 2 ^ i * (remAt m hm L n i + m - carryAt m hodd n i) + 2 ^ i * carryAt m hodd n i := by
              rw [Nat.mul_comm (carryAt m hodd n i)]
          _ = 2 ^ i * (remAt m hm L n i + m - carryAt m hodd n i + carryAt m hodd n i) := by
              rw [← Nat.mul_add]
          _ = 2 ^ i * (remAt m hm L n i + m) := by rw [hsum]
          _ = 2 ^ i * remAt m hm L n i + m * 2 ^ i := by rw [Nat.mul_add, Nat.mul_comm (2 ^ i) m]
      rw [heq, Nat.add_mul_mod_self_left]
    have hcancel : ∀ x y z, (x + z) % m = (y + z) % m → x % m = y % m := by
      intro x y z hxyz
      have hz_eq : z + (m - z % m) = (z / m + 1) * m := by
        have hdm : m * (z / m) + z % m = z := Nat.div_add_mod z m
        have hzlt : z % m < m := Nat.mod_lt z hm
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (z / m) m]
        omega
      have hx : x % m = (x + z + (m - z % m)) % m := by
        rw [Nat.add_assoc, hz_eq, Nat.add_mul_mod_self_right]
      have hy : y % m = (y + z + (m - z % m)) % m := by
        rw [Nat.add_assoc, hz_eq, Nat.add_mul_mod_self_right]
      rw [hx, hy, Nat.add_mod, hxyz, ← Nat.add_mod]
    exact hcancel _ _ (carryAt m hodd n i * 2 ^ i) (by rw [h3, ← h2])
  have hmod := mod_eq_of_pow2_mul_mod_eq hodd i hcong
  rw [Nat.mod_eq_of_lt hrho_lt] at hmod
  by_cases hlt : remAt m hm L n i < carryAt m hodd n i
  · simp only [hlt, ↓reduceIte, Int.mul_one]
    have hval : remAt m hm L n i + m - carryAt m hodd n i < m := by omega
    rw [Nat.mod_eq_of_lt hval] at hmod
    omega
  · simp only [hlt, ↓reduceIte, Int.mul_zero, Int.sub_zero]
    have hval : (remAt m hm L n i + m - carryAt m hodd n i) % m =
        remAt m hm L n i - carryAt m hodd n i := by
      have : remAt m hm L n i + m - carryAt m hodd n i =
          (remAt m hm L n i - carryAt m hodd n i) + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hval] at hmod
    omega

/-- THEOREM A (Master Dual Carry-Residue Conservation Law):
    Instantiating our general `dual_coupling_lift` engine with the 1-bit certificates
    `msbDivCert` and `lsbCarryCert` yields, for ALL odd m, ALL L, and ALL n < 2^L:
      m * (s2(Q_L(n)) - s2(n / m) - W_m(n, L)) = 2 * ((n % m) + c_L) - O_m(n % m, L). -/
theorem master_dual_carry_residue_law {m : Nat} (hodd : m % 2 = 1) (L n : Nat) (hn : n < 2 ^ L) :
    (m : Int) * dualInvariant m hodd L n =
      2 * (((n % m : Nat) : Int) + (carryAt m hodd n L : Int)) - (halvingOrbitSum m (n % m) L : Int) := by
  have hm : 0 < m := by omega
  have hlift := dual_coupling_lift
    (msbDivCert m hm) (lsbCarryCert m hodd) rfl rfl
    (zeroFin hm) (zeroFin hm) L n hn
    (fun i => (halveIter m i (n % m) : Int))
    (fun i => if remAt m hm L n i < carryAt m hodd n i then 1 else 0)
    (fun i hi => pointwise_modular_coupling hodd L n i (by omega) hn)
  have hsumW : sumInt L (fun i => if remAt m hm L n i < carryAt m hodd n i then (1 : Int) else 0) =
      (carryDomCount m hodd L n : Int) := by
    unfold carryDomCount
    rw [← sumInt_ofNat]
    apply sumInt_congr
    intro i _
    split <;> rfl
  have hsumO : sumInt L (fun i => (halveIter m i (n % m) : Int)) =
      (halvingOrbitSum m (n % m) L : Int) := by
    unfold halvingOrbitSum
    rw [Nat.mod_mod, sumInt_ofNat]
  have hrem0 : remAt m hm L n 0 = n % m := (msb_spec hm L n hn).1
  simp only [msbDivCert, lsbCarryCert, zeroFin] at hlift
  rw [hsumW, hsumO] at hlift
  change (m : Int) * dualInvariant m hodd L n =
    (2 * (carryAt m hodd n L : Int) - 2 * 0) -
    (-2 * (remAt m hm L n 0 : Int) - -2 * 0) -
    (halvingOrbitSum m (n % m) L : Int) at hlift
  rw [hrem0] at hlift
  omega

/-- Corollary: `dualInvariant` uses `n / m` explicitly via `msb_spec`. -/
theorem dualInvariant_eq {m : Nat} (hodd : m % 2 = 1) (L n : Nat) (hn : n < 2 ^ L) :
    dualInvariant m hodd L n =
      (popcount (twoAdicQuot m hodd L n) : Int) -
      (popcount (n / m) : Int) -
      (carryDomCount m hodd L n : Int) := by
  unfold dualInvariant
  rw [(msb_spec (by omega) L n hn).2]

/-- THEOREM B (Exact Synchronized-Trace Divisibility Equivalence):
    For ALL odd m, ALL L, and ALL n < 2^L, the four conditions are equivalent:
    (1) m ∣ n
    (2) carryAt m L = 0
    (3) ∀ i ≤ L, remAt_i = carryAt_i  (pointwise identical MSB remainder & LSB carry traces!)
    (4) twoAdicQuot L n = n / m. -/
theorem synchronized_trace_divisibility_iff {m : Nat} (hodd : m % 2 = 1) (L n : Nat)
    (hn : n < 2 ^ L) :
    (m ∣ n ↔ carryAt m hodd n L = 0) ∧
    (m ∣ n ↔ ∀ i, i ≤ L → remAt m (by omega) L n i = carryAt m hodd n i) ∧
    (m ∣ n ↔ twoAdicQuot m hodd L n = n / m) := by
  have hm : 0 < m := by omega
  have hfull := lsb_spec_full hodd L n hn
  have hcL_lt : carryAt m hodd n L < m := (stateLSB (lsbCarryFin m hodd) (zeroFin hm) n L).isLt
  have h1 : m ∣ n ↔ carryAt m hodd n L = 0 := by
    constructor
    · rintro ⟨k, hk⟩
      have hmod : (2 ^ L * carryAt m hodd n L) % m = (2 ^ L * 0) % m := by
        have hsum : m * twoAdicQuot m hodd L n = m * k + 2 ^ L * carryAt m hodd n L := by
          rw [hfull, hk, Nat.mul_comm (carryAt m hodd (m * k) L) (2 ^ L)]
        have h0 : (m * k + 2 ^ L * carryAt m hodd n L) % m = 0 := by
          rw [← hsum, Nat.mul_mod_right]
        rw [Nat.mul_add_mod] at h0
        simpa using h0
      have h0 := mod_eq_of_pow2_mul_mod_eq hodd L hmod
      rw [Nat.mod_eq_of_lt hcL_lt, Nat.zero_mod] at h0
      exact h0
    · intro hc0
      rw [hc0, Nat.zero_mul, Nat.add_zero] at hfull
      exact ⟨twoAdicQuot m hodd L n, hfull.symm⟩
  have h2 : m ∣ n ↔ ∀ i, i ≤ L → remAt m hm L n i = carryAt m hodd n i := by
    constructor
    · intro hdvd i hi
      have hmod0 : n % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have hcoup := pointwise_modular_coupling hodd L n i hi hn
      rw [hmod0, halveIter_zero] at hcoup
      have hr_lt : remAt m hm L n i < m := (stateMSB (msbDivFin m hm) (zeroFin hm) L n i).isLt
      have hc_lt : carryAt m hodd n i < m := (stateLSB (lsbCarryFin m hodd) (zeroFin hm) n i).isLt
      by_cases hlt : remAt m hm L n i < carryAt m hodd n i
      · simp [hlt] at hcoup; omega
      · simp [hlt] at hcoup; omega
    · intro hall
      have hL := hall L (Nat.le_refl L)
      have hrL : remAt m hm L n L = 0 := by
        unfold remAt; rw [stateMSB_top]; rfl
      rw [h1]
      omega
  have h3 : m ∣ n ↔ twoAdicQuot m hodd L n = n / m := by
    constructor
    · intro hdvd
      have hc0 := h1.mp hdvd
      rw [hc0, Nat.zero_mul, Nat.add_zero] at hfull
      have hdiv : n = m * (n / m) := by
        have := Nat.div_add_mod n m
        have hmod0 := Nat.mod_eq_zero_of_dvd hdvd
        omega
      exact Nat.eq_of_mul_eq_mul_left hm (by omega)
    · intro hq
      have hdiv : n = m * (n / m) + n % m := by
        have := Nat.div_add_mod n m; omega
      rw [hq] at hfull
      have : n % m = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
  exact ⟨h1, h2, h3⟩

/-- Carry-state formula: `carryAt m L = (m - halveIter m L (n % m)) % m`. -/
theorem carryAt_top_formula {m : Nat} (hodd : m % 2 = 1) (L n : Nat) (hn : n < 2 ^ L) :
    carryAt m hodd n L =
      if n % m = 0 then 0 else m - halveIter m L (n % m) := by
  have hm : 0 < m := by omega
  have hcoup := pointwise_modular_coupling hodd L n L (Nat.le_refl L) hn
  have hrL : remAt m hm L n L = 0 := by unfold remAt; rw [stateMSB_top]; rfl
  rw [hrL] at hcoup
  have hcL_lt : carryAt m hodd n L < m := (stateLSB (lsbCarryFin m hodd) (zeroFin hm) n L).isLt
  by_cases hr0 : n % m = 0
  · simp only [hr0, ↓reduceIte]
    exact (synchronized_trace_divisibility_iff hodd L n hn).1.mp (Nat.dvd_of_mod_eq_zero hr0)
  · simp only [hr0, ↓reduceIte]
    have hcne : carryAt m hodd n L ≠ 0 := by
      intro h0
      have hdvd := (synchronized_trace_divisibility_iff hodd L n hn).1.mpr h0
      exact hr0 (Nat.mod_eq_zero_of_dvd hdvd)
    have hpos : 0 < carryAt m hodd n L := by omega
    simp only [hpos, ↓reduceIte] at hcoup
    omega

/-- Decomposition of the 2-adic quotient: `Q_L(n) = (n / m) + Q_L(n % m)` whenever `n < 2^L`. -/
theorem twoAdicQuot_eq_euc_add_rem {m : Nat} (hodd : m % 2 = 1) (L n : Nat) (hn : n < 2 ^ L) :
    twoAdicQuot m hodd L n = n / m + twoAdicQuot m hodd L (n % m) := by
  have hm : 0 < m := by omega
  have hrlt : n % m < 2 ^ L := Nat.lt_of_le_of_lt (Nat.mod_le n m) hn
  have h1 := lsb_spec_full hodd L n hn
  have h2 := lsb_spec_full hodd L (n % m) hrlt
  have hc1 := carryAt_top_formula hodd L n hn
  have hc2 := carryAt_top_formula hodd L (n % m) hrlt
  rw [Nat.mod_mod] at hc2
  have hceq : carryAt m hodd n L = carryAt m hodd (n % m) L := by rw [hc1, hc2]
  have hdiv : n = m * (n / m) + n % m := by
    have := Nat.div_add_mod n m; omega
  have hmul : m * twoAdicQuot m hodd L n = m * (n / m + twoAdicQuot m hodd L (n % m)) := by
    rw [Nat.mul_add, h1, h2, hceq]
    omega
  exact Nat.eq_of_mul_eq_mul_left hm hmul

/-- THEOREM C (Exact Carry-Complementarity Law):
    For ALL odd m, ALL L ≥ 1, and ALL n < 2^L with `¬ (m ∣ n)`:
      carriesAdd (n / m) (Q_L (n % m)) + W_m(n, L) = L - 1 - v2(n % m). -/
theorem carry_complementarity_law {m : Nat} (hodd : m % 2 = 1) (L n : Nat)
    (hn : n < 2 ^ L) (hndvd : ¬ (m ∣ n)) :
    carriesAdd (n / m) (twoAdicQuot m hodd L (n % m)) + carryDomCount m hodd L n =
      L - 1 - v2 (n % m) := by
  have hm : 0 < m := by omega
  let E := n / m
  let r := n % m
  let Qr := twoAdicQuot m hodd L r
  let Q := twoAdicQuot m hodd L n
  have hr_pos : 0 < r := by
    have : r ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
    omega
  have hr_lt_m : r < m := Nat.mod_lt n hm
  have hr_lt_pow : r < 2 ^ L := Nat.lt_of_le_of_lt (Nat.mod_le n m) hn
  have hv2_lt : v2 r < L := v2_lt_of_lt_pow2 hr_pos hr_lt_pow
  have hQ_eq : Q = E + Qr := twoAdicQuot_eq_euc_add_rem hodd L n hn
  have hQ_lt : Q < 2 ^ L := (lsb_spec hodd n L).2
  have hcarries : carriesAdd E Qr = sumNat L (fun i => carryIn E Qr i) :=
    carriesAdd_eq_sum_carryIn L E Qr (by omega)
  change carriesAdd E Qr + carryDomCount m hodd L n = L - 1 - v2 r
  rw [hcarries]
  unfold carryDomCount
  rw [← sumNat_add]
  have hterm : ∀ i, i < L →
      carryIn E Qr i + (if remAt m hm L n i < carryAt m hodd n i then 1 else 0) =
        if v2 r < i then 1 else 0 := by
    intro i hi
    have hQr_full : m * Qr = r + carryAt m hodd r L * 2 ^ L := lsb_spec_full hodd L r hr_lt_pow
    have hQr_mod0_iff : Qr % 2 ^ i = 0 ↔ i ≤ v2 r := by
      rw [← Nat.dvd_iff_mod_eq_zero, ← pow2_dvd_iff_le_v2 hr_pos]
      have hdvdL : 2 ^ i ∣ 2 ^ L := Nat.pow_dvd_pow 2 (by omega)
      constructor
      · intro h
        have h1 : 2 ^ i ∣ m * Qr := Nat.dvd_trans h (Nat.dvd_mul_left Qr m)
        have h2 : 2 ^ i ∣ carryAt m hodd r L * 2 ^ L := Nat.dvd_trans hdvdL (Nat.dvd_mul_left _ _)
        rw [hQr_full] at h1
        exact (Nat.dvd_add_left h2).mp h1
      · intro h
        have h2 : 2 ^ i ∣ carryAt m hodd r L * 2 ^ L := Nat.dvd_trans hdvdL (Nat.dvd_mul_left _ _)
        have h1 : 2 ^ i ∣ m * Qr := by rw [hQr_full]; exact Nat.dvd_add h h2
        have hcop : Nat.Coprime (2 ^ i) m := by
          apply Nat.Coprime.pow_left
          show Nat.gcd 2 m = 1
          rw [Nat.gcd_rec, hodd]
          decide
        exact hcop.dvd_of_dvd_mul_left h1
    have hnat :
        m * (E % 2 ^ i) + r + carryAt m hodd n i * 2 ^ i =
          m * (Q % 2 ^ i) + remAt m hm L n i * 2 ^ i := by
      have hdivn : n = m * E + r := (Nat.div_add_mod n m).symm
      have hsplit_n : n = (n / 2 ^ i) * 2 ^ i + n % 2 ^ i := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod n (2 ^ i)).symm
      have hdiv_hi : n / 2 ^ i = m * (n / 2 ^ i / m) + remAt m hm L n i := by
        rw [remAt_eq_div_mod hm L n i (by omega) hn]
        exact (Nat.div_add_mod (n / 2 ^ i) m).symm
      have hE_hi : n / 2 ^ i / m = E / 2 ^ i := by
        show n / 2 ^ i / m = n / m / 2 ^ i
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      have hlsb_i : m * (Q % 2 ^ i) = n % 2 ^ i + carryAt m hodd n i * 2 ^ i := by
        have h1 := (lsb_spec hodd n i).1
        have hQmod : Q % 2 ^ i = twoAdicQuot m hodd i n := by
          have hsplitQ : Q = twoAdicQuot m hodd i n +
              2 ^ i * sumNat (L - i) (fun j => boolNat (outBitLSB (lsbCarryFin m hodd) (zeroFin hm) n (i + j)) * 2 ^ j) := by
            show outValLSB (lsbCarryFin m hodd) (zeroFin hm) L n = _
            unfold twoAdicQuot outValLSB
            have hL : L = i + (L - i) := by omega
            conv => lhs; rw [hL]
            rw [sumNat_split]
            congr 1
            rw [← sumNat_mul_left]
            apply sumNat_congr
            intro j _
            rw [Nat.pow_add, Nat.mul_comm (2 ^ i) (2 ^ j), ← Nat.mul_assoc,
                Nat.mul_comm _ (2 ^ i)]
          rw [hsplitQ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lsb_spec hodd n i).2]
        rw [hQmod]; exact h1
      have hE_split : E = (E / 2 ^ i) * 2 ^ i + E % 2 ^ i := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod E (2 ^ i)).symm
      have htop : m * ((E / 2 ^ i) * 2 ^ i) = m * (n / 2 ^ i / m) * 2 ^ i := by
        rw [hE_hi, Nat.mul_assoc]
      have hcomb1 : n = m * (n / 2 ^ i / m) * 2 ^ i + remAt m hm L n i * 2 ^ i + n % 2 ^ i := by
        calc n = (n / 2 ^ i) * 2 ^ i + n % 2 ^ i := hsplit_n
          _ = (m * (n / 2 ^ i / m) + remAt m hm L n i) * 2 ^ i + n % 2 ^ i := by
              congr 2
          _ = m * (n / 2 ^ i / m) * 2 ^ i + remAt m hm L n i * 2 ^ i + n % 2 ^ i := by rw [Nat.add_mul]
      have hcomb2 : n = m * (n / 2 ^ i / m) * 2 ^ i + m * (E % 2 ^ i) + r := by
        calc n = m * E + r := hdivn
          _ = m * ((E / 2 ^ i) * 2 ^ i + E % 2 ^ i) + r := by
              congr 2
          _ = m * ((E / 2 ^ i) * 2 ^ i) + m * (E % 2 ^ i) + r := by rw [Nat.mul_add]
          _ = m * (n / 2 ^ i / m) * 2 ^ i + m * (E % 2 ^ i) + r := by rw [htop]
      omega
    have hcarry_eq : E % 2 ^ i + Qr % 2 ^ i = Q % 2 ^ i + carryIn E Qr i * 2 ^ i := by
      have hQmod : Q % 2 ^ i = (E % 2 ^ i + Qr % 2 ^ i) % 2 ^ i := by
        rw [hQ_eq, Nat.add_mod]
      rw [hQmod]
      unfold carryIn
      have hdm := (Nat.div_add_mod (E % 2 ^ i + Qr % 2 ^ i) (2 ^ i)).symm
      rw [Nat.mul_comm (2 ^ i)] at hdm
      omega
    have hpow_pos : 0 < 2 ^ i := Nat.two_pow_pos i
    by_cases hgt : v2 r < i
    · simp only [hgt, ↓reduceIte]
      have hQr_pos : 0 < Qr % 2 ^ i := by
        have : Qr % 2 ^ i ≠ 0 := fun h => by
          have := hQr_mod0_iff.mp h; omega
        omega
      have hc01 : carryIn E Qr i = 0 ∨ carryIn E Qr i = 1 := by
        have := carryIn_le_one E Qr i; omega
      rcases hc01 with hc0 | hc1
      · rw [hc0, Nat.zero_mul, Nat.add_zero] at hcarry_eq
        have hQge : E % 2 ^ i + 1 ≤ Q % 2 ^ i := by omega
        have hmQ : m * (E % 2 ^ i) + m ≤ m * (Q % 2 ^ i) := by
          calc m * (E % 2 ^ i) + m = m * (E % 2 ^ i + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ m * (Q % 2 ^ i) := Nat.mul_le_mul_left m hQge
        have hlt_mul : remAt m hm L n i * 2 ^ i < carryAt m hodd n i * 2 ^ i := by omega
        have hlt_rc : remAt m hm L n i < carryAt m hodd n i :=
          Nat.lt_of_mul_lt_mul_right hlt_mul
        simp [hc0, hlt_rc]
      · rw [hc1, Nat.one_mul] at hcarry_eq
        have hQr_lt : Qr % 2 ^ i < 2 ^ i := Nat.mod_lt Qr hpow_pos
        have hEge : Q % 2 ^ i + 1 ≤ E % 2 ^ i := by omega
        have hmE : m * (Q % 2 ^ i) + m ≤ m * (E % 2 ^ i) := by
          calc m * (Q % 2 ^ i) + m = m * (Q % 2 ^ i + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ m * (E % 2 ^ i) := Nat.mul_le_mul_left m hEge
        have hlt_mul : carryAt m hodd n i * 2 ^ i < remAt m hm L n i * 2 ^ i := by omega
        have hlt_cr : carryAt m hodd n i < remAt m hm L n i :=
          Nat.lt_of_mul_lt_mul_right hlt_mul
        have hnot : ¬ (remAt m hm L n i < carryAt m hodd n i) := by omega
        simp [hc1, hnot]
    · simp only [hgt, ↓reduceIte]
      have hQr0 : Qr % 2 ^ i = 0 := hQr_mod0_iff.mpr (by omega)
      have hc0 : carryIn E Qr i = 0 := by
        unfold carryIn
        rw [hQr0, Nat.add_zero]
        exact Nat.div_eq_of_lt (Nat.mod_lt E hpow_pos)
      rw [hc0, Nat.zero_mul, Nat.add_zero, hQr0, Nat.add_zero] at hcarry_eq
      rw [hcarry_eq] at hnat
      have hlt_mul : carryAt m hodd n i * 2 ^ i < remAt m hm L n i * 2 ^ i := by omega
      have hlt_cr : carryAt m hodd n i < remAt m hm L n i :=
        Nat.lt_of_mul_lt_mul_right hlt_mul
      have hnot : ¬ (remAt m hm L n i < carryAt m hodd n i) := by omega
      simp [hc0, hnot]
  rw [sumNat_congr hterm]
  have hcount : ∀ M a, a < M → sumNat M (fun i => if a < i then 1 else 0) = M - 1 - a := by
    intro M a ha
    induction M with
    | zero => omega
    | succ M ih =>
      simp only [sumNat]
      by_cases h : a = M
      · subst h
        have hzero : sumNat a (fun i => if a < i then 1 else 0) = 0 := by
          rw [sumNat_eq_zero_iff]
          intro i hi; simp [show ¬ (a < i) by omega]
        simp [hzero]
      · have hlt : a < M := by omega
        rw [ih hlt]
        simp [hlt]
        omega
  exact hcount L (v2 r) hv2_lt

/-- THEOREM D (Universal 2-adic Reciprocal Popcount Law):
    For ALL odd m, ALL L ≥ 1, and ALL `0 < r < m` with `r < 2^L`:
      m * (popcount(Q_L(r)) - (L - 1 - v2(r))) = 2 * (r + c_L(r)) - O_m(r, L). -/
theorem two_adic_reciprocal_popcount_master {m : Nat} (hodd : m % 2 = 1) (L r : Nat)
    (hr_pos : 0 < r) (hr_lt_m : r < m) (hr_lt_pow : r < 2 ^ L) :
    (m : Int) * ((popcount (twoAdicQuot m hodd L r) : Int) - ((L - 1 - v2 r : Nat) : Int)) =
      2 * ((r : Int) + (carryAt m hodd r L : Int)) - (halvingOrbitSum m r L : Int) := by
  have hmod : r % m = r := Nat.mod_eq_of_lt hr_lt_m
  have hdiv : r / m = 0 := Nat.div_eq_of_lt hr_lt_m
  have hndvd : ¬ (m ∣ r) := by
    intro hdvd
    have := Nat.le_of_dvd hr_pos hdvd
    omega
  have hmaster := master_dual_carry_residue_law hodd L r hr_lt_pow
  have hcomp := carry_complementarity_law hodd L r hr_lt_pow hndvd
  have hinv := dualInvariant_eq hodd L r hr_lt_pow
  rw [hmod] at hmaster hcomp
  rw [hdiv] at hcomp hinv
  have hc0 : carriesAdd 0 (twoAdicQuot m hodd L r) = 0 := by
    have h := kummer_carriesAdd 0 (twoAdicQuot m hodd L r)
    simp only [Nat.zero_add, popcount_zero] at h
    omega
  rw [hc0, Nat.zero_add] at hcomp
  rw [hinv, popcount_zero, hcomp] at hmaster
  simpa using hmaster

/-! ## Shared Periodicity & Summation Helpers for Infinite Families -/

theorem sumNat_swap (A B : Nat) (f : Nat → Nat → Nat) :
    sumNat A (fun i => sumNat B (fun j => f i j)) =
      sumNat B (fun j => sumNat A (fun i => f i j)) := by
  induction A with
  | zero =>
    simp only [sumNat]
    symm
    rw [sumNat_eq_zero_iff]
    intro _ _; rfl
  | succ A ih =>
    simp only [sumNat, ih]
    rw [← sumNat_add]

theorem sumNat_cyclic_shift (k j : Nat) (hj : j < k) (f : Nat → Nat) :
    sumNat k (fun i => f ((j + i) % k)) = sumNat k f := by
  have hk1 : k = (k - j) + j := by omega
  have hk2 : k = j + (k - j) := by omega
  have hsplit1 : sumNat k (fun i => f ((j + i) % k)) =
      sumNat (k - j) (fun i => f ((j + i) % k)) +
      sumNat j (fun i => f ((j + (k - j + i)) % k)) := by
    have h := sumNat_split (k - j) j (fun i => f ((j + i) % k))
    rw [← hk1] at h
    exact h
  have hpart1 : sumNat (k - j) (fun i => f ((j + i) % k)) =
      sumNat (k - j) (fun i => f (j + i)) := by
    apply sumNat_congr
    intro i hi
    rw [Nat.mod_eq_of_lt (by omega)]
  have hpart2 : sumNat j (fun i => f ((j + (k - j + i)) % k)) = sumNat j f := by
    apply sumNat_congr
    intro i hi
    have heq : j + (k - j + i) = k + i := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hsplit1, hpart1, hpart2, Nat.add_comm]
  have hsplit2 := sumNat_split j (k - j) f
  rw [← hk2] at hsplit2
  exact hsplit2.symm

theorem sumNat_pow2 (k : Nat) : sumNat k (fun j => 2 ^ j) = 2 ^ k - 1 := by
  induction k with
  | zero => simp [sumNat]
  | succ k ih =>
    simp only [sumNat, ih, Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    omega

theorem halveIter_add (m a b x : Nat) :
    halveIter m (a + b) x = halveIter m b (halveIter m a x) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← Nat.add_assoc]
    simp only [halveIter, ih]

theorem halveIter_periodic_mul {m P r : Nat} (hper : halveIter m P r = r) (t : Nat) :
    halveIter m (t * P) r = r := by
  induction t with
  | zero => simp [halveIter]
  | succ t ih =>
    rw [Nat.succ_mul, halveIter_add, ih, hper]

theorem halvingOrbitSum_periodic_mul {m P r : Nat} (hr : r < m) (hper : halveIter m P r = r) (t : Nat) :
    halvingOrbitSum m r (t * P) = t * halvingOrbitSum m r P := by
  unfold halvingOrbitSum
  rw [Nat.mod_eq_of_lt hr]
  induction t with
  | zero => simp [sumNat]
  | succ t ih =>
    rw [Nat.succ_mul, sumNat_split, ih, Nat.succ_mul]
    congr 1
    apply sumNat_congr
    intro i _
    rw [halveIter_add, halveIter_periodic_mul hper t]

theorem dualInvariant_of_dvd {m : Nat} (hodd : m % 2 = 1) (L n : Nat)
    (hn : n < 2 ^ L) (hdvd : m ∣ n) :
    dualInvariant m hodd L n = 0 := by
  have hm : (0 : Int) < (m : Int) := by omega
  have hmaster := master_dual_carry_residue_law hodd L n hn
  have hmod0 : n % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hc0 : carryAt m hodd n L = 0 := (synchronized_trace_divisibility_iff hodd L n hn).1.mp hdvd
  rw [hmod0, hc0, halvingOrbitSum_zero] at hmaster
  have hzero : (m : Int) * dualInvariant m hodd L n = 0 := by omega
  exact (Int.mul_eq_zero.mp hzero).resolve_left (by omega)

/-! ## Layer 4: Infinite Mersenne Family `m = 2^k - 1` (`∀ k ≥ 2, ∀ t ≥ 1, ∀ n < 2^(t*k)`) -/


def rotR (k x : Nat) : Nat := x / 2 + (x % 2) * 2 ^ (k - 1)

theorem halveStep_mersenne {k x : Nat} (hk : 1 ≤ k) :
    halveStep (2 ^ k - 1) x = rotR k x := by
  unfold halveStep rotR
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk1, Nat.pow_succ, Nat.mul_comm]
  have hpos : 1 ≤ 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
  split
  · next he =>
    rw [he, Nat.zero_mul, Nat.add_zero]
  · next ho =>
    have h1 : x % 2 = 1 := by omega
    rw [h1, Nat.one_mul]
    omega

theorem bitAt_rotR {k x j : Nat} (hk : 1 ≤ k) (hx : x < 2 ^ k) (hj : j < k) :
    boolNat (bitAt (rotR k x) j) = boolNat (bitAt x ((j + 1) % k)) := by
  rw [boolNat_bitAt, boolNat_bitAt]
  unfold rotR
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk1, Nat.pow_succ, Nat.mul_comm]
  by_cases hlast : j + 1 = k
  · have hj_eq : j = k - 1 := by omega
    rw [hlast, Nat.mod_self, Nat.pow_zero, Nat.div_one, hj_eq]
    have hdiv_lt : x / 2 < 2 ^ (k - 1) := by omega
    have hp : 0 < 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
    rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hdiv_lt, Nat.zero_add, Nat.mod_mod]
  · have hlt : j + 1 < k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsplit : k - 1 = j + (k - 1 - j) := by omega
    have hpow2 : 2 ^ (k - 1) = 2 ^ (k - 1 - j) * 2 ^ j := by
      conv => lhs; rw [hsplit, Nat.pow_add, Nat.mul_comm]
    have hp : 0 < 2 ^ j := Nat.two_pow_pos j
    rw [hpow2, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ hp]
    have heven : 2 ∣ 2 ^ (k - 1 - j) := by
      have hpos : 1 ≤ k - 1 - j := by omega
      have hsub : k - 1 - j = (k - 1 - j - 1) + 1 := by omega
      rw [hsub, Nat.pow_succ]
      exact Nat.dvd_mul_left 2 _
    rcases heven with ⟨q, hq⟩
    rw [hq, ← Nat.mul_assoc, Nat.mul_comm (x % 2) 2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2 ^ j), ← Nat.pow_succ]

theorem bitAt_halveIter_mersenne {k r i j : Nat} (hk : 1 ≤ k) (hr : r < 2 ^ k - 1) (hj : j < k) :
    boolNat (bitAt (halveIter (2 ^ k - 1) i r) j) = boolNat (bitAt r ((j + i) % k)) := by
  induction i generalizing j with
  | zero =>
    simp [halveIter, Nat.mod_eq_of_lt hj]
  | succ i ih =>
    simp only [halveIter]
    rw [halveStep_mersenne hk]
    have hlt_m : halveIter (2 ^ k - 1) i r < 2 ^ k - 1 :=
      halveIter_lt (mersenne_odd hk) hr i
    have hlt_pow : halveIter (2 ^ k - 1) i r < 2 ^ k := by omega
    rw [bitAt_rotR hk hlt_pow hj]
    have hj' : (j + 1) % k < k := Nat.mod_lt _ (by omega)
    rw [ih hj']
    have hmod : ((j + 1) % k + i) % k = (j + (i + 1)) % k := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega
    rw [hmod]

theorem halveIter_mersenne_period {k r : Nat} (hk : 1 ≤ k) (hr : r < 2 ^ k - 1) :
    halveIter (2 ^ k - 1) k r = r := by
  have hodd := mersenne_odd hk
  have hm_pos : 0 < 2 ^ k - 1 := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  have hpow_mod : 2 ^ k % (2 ^ k - 1) = 1 % (2 ^ k - 1) := by
    have heq : 2 ^ k = (2 ^ k - 1) + 1 := by omega
    conv => lhs; arg 1; rw [heq]
    rw [Nat.add_mod_left]
  have h1 := pow2_mul_halveIter_mod hodd k (x := r)
  rw [Nat.mul_mod, hpow_mod, ← Nat.mul_mod, Nat.one_mul] at h1
  have hlt := halveIter_lt hodd hr k
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hr] at h1
  exact h1

/-- Exact Mersenne cyclic-rotation orbit sum: `O_{2^k - 1}(r, k) = (2^k - 1) * popcount r`. -/
theorem halvingOrbitSum_mersenne_period {k r : Nat} (hk : 1 ≤ k) (hr : r < 2 ^ k - 1) :
    halvingOrbitSum (2 ^ k - 1) r k = (2 ^ k - 1) * popcount r := by
  have hodd := mersenne_odd hk
  unfold halvingOrbitSum
  rw [Nat.mod_eq_of_lt hr]
  have hexpand : sumNat k (fun i => halveIter (2 ^ k - 1) i r) =
      sumNat k (fun i => sumNat k (fun j => boolNat (bitAt r ((j + i) % k)) * 2 ^ j)) := by
    apply sumNat_congr
    intro i _
    have hlt_m : halveIter (2 ^ k - 1) i r < 2 ^ k - 1 := halveIter_lt hodd hr i
    have hlt_pow : halveIter (2 ^ k - 1) i r < 2 ^ k := by omega
    rw [← sum_bits_val k (halveIter (2 ^ k - 1) i r) hlt_pow]
    apply sumNat_congr
    intro j hj
    rw [bitAt_halveIter_mersenne hk hr hj]
  rw [hexpand, sumNat_swap]
  have hinner : ∀ j, j < k →
      sumNat k (fun i => boolNat (bitAt r ((j + i) % k)) * 2 ^ j) = popcount r * 2 ^ j := by
    intro j hj
    have hpull : sumNat k (fun i => boolNat (bitAt r ((j + i) % k)) * 2 ^ j) =
        2 ^ j * sumNat k (fun i => boolNat (bitAt r ((j + i) % k))) := by
      rw [← sumNat_mul_left]
      apply sumNat_congr
      intro i _; rw [Nat.mul_comm]
    rw [hpull, sumNat_cyclic_shift k j hj (fun u => boolNat (bitAt r u)),
        ← popcount_eq_sum_bits k r (by omega), Nat.mul_comm]
  rw [sumNat_congr hinner]
  have hpull2 : sumNat k (fun j => popcount r * 2 ^ j) =
      popcount r * sumNat k (fun j => 2 ^ j) := sumNat_mul_left k (popcount r) (fun j => 2 ^ j)
  rw [hpull2, sumNat_pow2, Nat.mul_comm]

/-- THEOREM E1 (Infinite Mersenne Family Dual Invariant Law):
    For ALL k ≥ 2, ALL t ≥ 1, and ALL n < 2^(t*k):
      dualInvariant (2^k - 1) (t*k) n =
        if (2^k - 1) ∣ n then 0 else 2 - t * popcount (n % (2^k - 1)). -/
theorem mersenne_dual_invariant_law {k t n : Nat} (hk : 2 ≤ k) (_ht : 1 ≤ t)
    (hn : n < 2 ^ (t * k)) :
    dualInvariant (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) n =
      if (2 ^ k - 1) ∣ n then 0
      else 2 - (t : Int) * (popcount (n % (2 ^ k - 1)) : Int) := by
  have hodd := mersenne_odd (by omega : 1 ≤ k)
  have hm_pos : 0 < 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  by_cases hdvd : (2 ^ k - 1) ∣ n
  · simp only [hdvd, ↓reduceIte]
    exact dualInvariant_of_dvd hodd (t * k) n hn hdvd
  · simp only [hdvd, ↓reduceIte]
    have hmaster := master_dual_carry_residue_law hodd (t * k) n hn
    have hr_lt : n % (2 ^ k - 1) < 2 ^ k - 1 := Nat.mod_lt n hm_pos
    have hr_ne : n % (2 ^ k - 1) ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have hper : halveIter (2 ^ k - 1) k (n % (2 ^ k - 1)) = n % (2 ^ k - 1) :=
      halveIter_mersenne_period (by omega) hr_lt
    have hcL : carryAt (2 ^ k - 1) hodd n (t * k) = (2 ^ k - 1) - n % (2 ^ k - 1) := by
      rw [carryAt_top_formula hodd (t * k) n hn]
      simp only [hr_ne, ↓reduceIte, halveIter_periodic_mul hper t]
    have horb : halvingOrbitSum (2 ^ k - 1) (n % (2 ^ k - 1)) (t * k) =
        t * ((2 ^ k - 1) * popcount (n % (2 ^ k - 1))) := by
      rw [halvingOrbitSum_periodic_mul hr_lt hper t,
          halvingOrbitSum_mersenne_period (by omega) hr_lt]
    rw [hcL, horb] at hmaster
    have hsum_rc : (((n % (2 ^ k - 1) : Nat) : Int) + (((2 ^ k - 1) - n % (2 ^ k - 1) : Nat) : Int)) =
        ((2 ^ k - 1 : Nat) : Int) := by omega
    rw [hsum_rc] at hmaster
    have hrhs :
        2 * ((2 ^ k - 1 : Nat) : Int) -
          ((t * ((2 ^ k - 1) * popcount (n % (2 ^ k - 1))) : Nat) : Int) =
        ((2 ^ k - 1 : Nat) : Int) * (2 - (t : Int) * (popcount (n % (2 ^ k - 1)) : Int)) := by
      have hcast : ((t * ((2 ^ k - 1) * popcount (n % (2 ^ k - 1))) : Nat) : Int) =
          ((2 ^ k - 1 : Nat) : Int) * ((t : Int) * (popcount (n % (2 ^ k - 1)) : Int)) := by
        push_cast
        rw [Int.mul_left_comm]
      rw [hcast, Int.mul_sub, Int.mul_comm ((2 ^ k - 1 : Nat) : Int) 2]
    rw [hrhs] at hmaster
    have hsub : ((2 ^ k - 1 : Nat) : Int) *
        (dualInvariant (2 ^ k - 1) hodd (t * k) n -
          (2 - (t : Int) * (popcount (n % (2 ^ k - 1)) : Int))) = 0 := by
      rw [Int.mul_sub, hmaster, Int.sub_self]
    have hzero := (Int.mul_eq_zero.mp hsub).resolve_left (by omega)
    omega

/-- Helper: positive natural number has positive popcount. -/
theorem popcount_pos_of_pos {n : Nat} (hn : 0 < n) : 0 < popcount n := by
  have hstrong : ∀ s n, n ≤ s → 0 < n → 0 < popcount n := by
    intro s
    induction s with
    | zero => intro n h1 h2; omega
    | succ s ih =>
      intro n h1 h2
      rw [popcount_step]
      by_cases hmod : n % 2 = 1
      · omega
      · have hdiv : 0 < n / 2 := by omega
        have := ih (n / 2) (by omega) hdiv
        omega
  exact hstrong n n (Nat.le_refl n) hn

/-- THEOREM E2 (Sharp Mersenne Divisibility Threshold — exact iff for ALL t ≥ 3):
    For ALL k ≥ 2, ALL t ≥ 3, and ALL n < 2^(t*k):
      (2^k - 1) ∣ n ↔ popcount(Q_{t*k}(n)) - popcount(n / (2^k - 1)) = W_{2^k - 1}(n, t*k). -/
theorem mersenne_divisibility_threshold_iff {k t n : Nat} (hk : 2 ≤ k) (ht : 3 ≤ t)
    (hn : n < 2 ^ (t * k)) :
    (2 ^ k - 1) ∣ n ↔
      (popcount (twoAdicQuot (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) n) : Int) -
      (popcount (n / (2 ^ k - 1)) : Int) =
      (carryDomCount (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) n : Int) := by
  have hodd := mersenne_odd (by omega : 1 ≤ k)
  have hlaw := mersenne_dual_invariant_law hk (by omega : 1 ≤ t) hn
  have hinv := dualInvariant_eq hodd (t * k) n hn
  constructor
  · intro hdvd
    simp only [hdvd, ↓reduceIte] at hlaw
    rw [hinv] at hlaw
    omega
  · intro heq
    by_cases hdvd : (2 ^ k - 1) ∣ n
    · exact hdvd
    · exfalso
      simp only [hdvd, ↓reduceIte] at hlaw
      rw [hinv] at hlaw
      have hr_pos : 0 < n % (2 ^ k - 1) := by
        have : n % (2 ^ k - 1) ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
        omega
      have hpc : 1 ≤ popcount (n % (2 ^ k - 1)) := popcount_pos_of_pos hr_pos
      have hmul : 3 ≤ t * popcount (n % (2 ^ k - 1)) := by
        calc 3 = 3 * 1 := by decide
        _ ≤ t * popcount (n % (2 ^ k - 1)) := Nat.mul_le_mul ht hpc
      have hmulI : (3 : Int) ≤ (t : Int) * (popcount (n % (2 ^ k - 1)) : Int) := by
        exact_mod_cast hmul
      omega

/-- THEOREM E3 (Mersenne 2-adic Reciprocal Popcount Law):
    For ALL k ≥ 2, ALL t ≥ 1, and ALL `0 < r < 2^k - 1`:
      popcount(Q_{t*k}(r)) = t * (k - popcount r) + 1 - v2 r. -/
theorem mersenne_reciprocal_popcount_law {k t r : Nat} (hk : 2 ≤ k) (ht : 1 ≤ t)
    (hr_pos : 0 < r) (hr_lt : r < 2 ^ k - 1) :
    popcount (twoAdicQuot (2 ^ k - 1) (mersenne_odd (by omega)) (t * k) r) =
      t * (k - popcount r) + 1 - v2 r := by
  have hodd := mersenne_odd (by omega : 1 ≤ k)
  have hle_tk : k ≤ t * k := by
    calc k = 1 * k := (Nat.one_mul k).symm
    _ ≤ t * k := Nat.mul_le_mul_right k ht
  have hr_pow : r < 2 ^ (t * k) := by
    have h1 : r < 2 ^ k := by omega
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hle_tk)
  have hndvd : ¬ ((2 ^ k - 1) ∣ r) := by
    intro hdvd; have := Nat.le_of_dvd hr_pos hdvd; omega
  have hlaw := mersenne_dual_invariant_law hk ht hr_pow
  simp only [hndvd, ↓reduceIte] at hlaw
  rw [Nat.mod_eq_of_lt hr_lt] at hlaw
  have hinv := dualInvariant_eq hodd (t * k) r hr_pow
  rw [Nat.div_eq_of_lt hr_lt, popcount_zero] at hinv
  have hcomp := carry_complementarity_law hodd (t * k) r hr_pow hndvd
  rw [Nat.div_eq_of_lt hr_lt, Nat.mod_eq_of_lt hr_lt] at hcomp
  have hc0 : carriesAdd 0 (twoAdicQuot (2 ^ k - 1) hodd (t * k) r) = 0 := by
    have h := kummer_carriesAdd 0 (twoAdicQuot (2 ^ k - 1) hodd (t * k) r)
    simp only [Nat.zero_add, popcount_zero] at h; omega
  rw [hc0, Nat.zero_add] at hcomp
  have hv2_lt : v2 r < t * k := v2_lt_of_lt_pow2 hr_pos hr_pow
  have hpc_le_k : popcount r ≤ k := by
    rw [popcount_eq_sum_bits k r (by omega)]
    have hle : sumNat k (fun i => boolNat (bitAt r i)) ≤ sumNat k (fun _ => 1) := by
      have hgen : ∀ M (f g : Nat → Nat), (∀ i, i < M → f i ≤ g i) → sumNat M f ≤ sumNat M g := by
        intro M f g hfg
        induction M with
        | zero => simp [sumNat]
        | succ M ih =>
          simp only [sumNat]
          have := ih (fun i hi => hfg i (by omega))
          have := hfg M (by omega)
          omega
      exact hgen k _ _ (fun i _ => by cases bitAt r i <;> decide)
    rw [sumNat_const, Nat.mul_one] at hle
    exact hle
  have hdist : t * (k - popcount r) + t * popcount r = t * k := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hpc_le_k]
  have hv2_le_tk : v2 r ≤ t * (k - popcount r) := by
    -- Stronger fact: v2 r ≤ k - popcount r since r < 2^k has v2 r trailing zeros and popcount r ones!
    have hsum_le : popcount r + v2 r ≤ k := by
      have hsplit_r : popcount r = sumNat k (fun i => boolNat (bitAt r i)) :=
        popcount_eq_sum_bits k r (by omega)
      have hv2_k : v2 r < k := v2_lt_of_lt_pow2 hr_pos (by omega)
      rw [hsplit_r]
      have hk_split : k = v2 r + (k - v2 r) := by omega
      conv => lhs; rw [hk_split]
      rw [sumNat_split]
      have hzeros : sumNat (v2 r) (fun i => boolNat (bitAt r i)) = 0 := by
        rw [sumNat_eq_zero_iff]
        intro i hi
        rw [boolNat_bitAt]
        have hdvd : 2 ^ (i + 1) ∣ r := (pow2_dvd_iff_le_v2 hr_pos).mpr (by omega)
        rcases hdvd with ⟨q, hq⟩
        rw [hq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos i)]
        omega
      rw [hzeros, Nat.zero_add]
      have hle_rest : sumNat (k - v2 r) (fun i => boolNat (bitAt r (v2 r + i))) ≤ k - v2 r := by
        have hgen : ∀ M (f : Nat → Nat), (∀ i, i < M → f i ≤ 1) → sumNat M f ≤ M := by
          intro M f hf
          induction M with
          | zero => simp [sumNat]
          | succ M ih =>
            simp only [sumNat]
            have := ih (fun i hi => hf i (by omega))
            have := hf M (by omega)
            omega
        exact hgen (k - v2 r) _ (fun i _ => by cases bitAt r (v2 r + i) <;> decide)
      omega
    calc v2 r ≤ k - popcount r := by omega
      _ = 1 * (k - popcount r) := (Nat.one_mul _).symm
      _ ≤ t * (k - popcount r) := Nat.mul_le_mul_right _ ht
  omega

/-! ## Layer 5: Infinite Negacyclic Family `m ∣ (2^d + 1)` & Fermat Family `m = 2^k + 1` -/

theorem halveIter_ne_zero {m r : Nat} (hodd : m % 2 = 1) (hr0 : 0 < r) (hrm : r < m) (i : Nat) :
    0 < halveIter m i r := by
  have h1 := pow2_mul_halveIter_mod hodd i (x := r)
  rw [Nat.mod_eq_of_lt hrm] at h1
  apply Nat.pos_of_ne_zero
  intro h0
  rw [h0, Nat.mul_zero, Nat.zero_mod] at h1
  omega

/-- Half-period antipodal flip for ANY negacyclic odd modulus `m ∣ (2^d + 1)`:
    `halveIter m d r = m - r` for ALL `0 < r < m`. -/
theorem halveIter_negacyclic_half {m d r : Nat} (hodd : m % 2 = 1) (hdvd : m ∣ 2 ^ d + 1)
    (hr0 : 0 < r) (hrm : r < m) :
    halveIter m d r = m - r := by
  have hm_pos : 0 < m := by omega
  have hlt : halveIter m d r < m := halveIter_lt hodd hrm d
  have h1 := pow2_mul_halveIter_mod hodd d (x := r)
  rw [Nat.mod_eq_of_lt hrm] at h1
  have hsum_mod : (r + halveIter m d r) % m = 0 := by
    have h2 : ((2 ^ d + 1) * halveIter m d r) % m = 0 := by
      rcases hdvd with ⟨q, hq⟩
      rw [hq, Nat.mul_assoc, Nat.mul_mod_right]
    have h3 : ((2 ^ d + 1) * halveIter m d r) % m = (r + halveIter m d r) % m := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_mod, h1]
      conv => rhs; rw [Nat.add_mod, Nat.mod_eq_of_lt hrm]
    omega
  have hpos_sum : 0 < r + halveIter m d r := by omega
  have hlt_2m : r + halveIter m d r < 2 * m := by omega
  have hdvd_sum : m ∣ r + halveIter m d r := Nat.dvd_of_mod_eq_zero hsum_mod
  rcases hdvd_sum with ⟨q, hq⟩
  have hq1 : q = 1 := by
    match q with
    | 0 => simp at hq; omega
    | 1 => rfl
    | k + 2 =>
      have : m * (k + 2) = 2 * m + m * k := by rw [Nat.mul_add, Nat.mul_comm m 2]; omega
      omega
  rw [hq1, Nat.mul_one] at hq
  omega

theorem halveIter_negacyclic_full {m d r : Nat} (hodd : m % 2 = 1) (hdvd : m ∣ 2 ^ d + 1)
    (hr0 : 0 < r) (hrm : r < m) :
    halveIter m (2 * d) r = r := by
  have h2d : 2 * d = d + d := by omega
  rw [h2d, halveIter_add, halveIter_negacyclic_half hodd hdvd hr0 hrm]
  rw [halveIter_negacyclic_half hodd hdvd (by omega) (by omega)]
  omega

/-- Exact Negacyclic Full-Period Orbit Sum (completely residue-blind!):
    For ALL odd `m ∣ (2^d + 1)` and ALL `0 < r < m`: `O_m(r, 2*d) = d * m`. -/
theorem halvingOrbitSum_negacyclic_period {m d r : Nat} (hodd : m % 2 = 1) (hdvd : m ∣ 2 ^ d + 1)
    (hr0 : 0 < r) (hrm : r < m) :
    halvingOrbitSum m r (2 * d) = d * m := by
  unfold halvingOrbitSum
  rw [Nat.mod_eq_of_lt hrm]
  have h2d : 2 * d = d + d := by omega
  rw [h2d, sumNat_split, ← sumNat_add]
  have hpair : ∀ i, i < d → halveIter m i r + halveIter m (d + i) r = m := by
    intro i _
    rw [Nat.add_comm d i, halveIter_add]
    have hlt := halveIter_lt hodd hrm i
    have hpos := halveIter_ne_zero hodd hr0 hrm i
    rw [halveIter_negacyclic_half hodd hdvd hpos hlt]
    omega
  rw [sumNat_congr hpair, sumNat_const]

/-- THEOREM F1 (Infinite Negacyclic Residue-Blind Constant Collapse Law):
    For ALL odd `m ≥ 3`, ALL `d ≥ 1` with `m ∣ (2^d + 1)`, ALL `t ≥ 1`, and ALL `n < 2^(2*t*d)`:
      dualInvariant m (2*t*d) n = if m ∣ n then 0 else 2 - t * d.
    Completely independent of BOTH `n` AND the nonzero residue `n % m`! -/
theorem negacyclic_dual_invariant_law {m d t n : Nat} (hodd : m % 2 = 1) (hm3 : 3 ≤ m)
    (_hd : 1 ≤ d) (hdvd_m : m ∣ 2 ^ d + 1) (_ht : 1 ≤ t) (hn : n < 2 ^ (2 * t * d)) :
    dualInvariant m hodd (2 * t * d) n =
      if m ∣ n then 0 else 2 - (t : Int) * (d : Int) := by
  have hm_pos : 0 < m := by omega
  by_cases hdvd : m ∣ n
  · simp only [hdvd, ↓reduceIte]
    exact dualInvariant_of_dvd hodd (2 * t * d) n hn hdvd
  · simp only [hdvd, ↓reduceIte]
    have hmaster := master_dual_carry_residue_law hodd (2 * t * d) n hn
    have hr_lt : n % m < m := Nat.mod_lt n hm_pos
    have hr_ne : n % m ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have hr_pos : 0 < n % m := by omega
    have hper : halveIter m (2 * d) (n % m) = n % m :=
      halveIter_negacyclic_full hodd hdvd_m hr_pos hr_lt
    have h2td : 2 * t * d = t * (2 * d) := by
      rw [Nat.mul_assoc, Nat.mul_comm t d, ← Nat.mul_assoc, Nat.mul_comm 2 d, Nat.mul_comm]
    have hcL : carryAt m hodd n (2 * t * d) = m - n % m := by
      rw [carryAt_top_formula hodd (2 * t * d) n hn]
      simp only [hr_ne, ↓reduceIte]
      rw [h2td, halveIter_periodic_mul hper t]
    have horb : halvingOrbitSum m (n % m) (2 * t * d) = t * (d * m) := by
      rw [h2td, halvingOrbitSum_periodic_mul hr_lt hper t,
          halvingOrbitSum_negacyclic_period hodd hdvd_m hr_pos hr_lt]
    rw [hcL, horb] at hmaster
    have hsum_rc : (((n % m : Nat) : Int) + ((m - n % m : Nat) : Int)) = (m : Int) := by omega
    rw [hsum_rc] at hmaster
    have hrhs :
        2 * (m : Int) - ((t * (d * m) : Nat) : Int) =
        (m : Int) * (2 - (t : Int) * (d : Int)) := by
      have hcast : ((t * (d * m) : Nat) : Int) = (m : Int) * ((t : Int) * (d : Int)) := by
        push_cast
        rw [← Int.mul_assoc, Int.mul_comm ((t : Int) * (d : Int)) (m : Int)]
      rw [hcast, Int.mul_sub, Int.mul_comm (m : Int) 2]
    rw [hrhs] at hmaster
    have hsub : (m : Int) * (dualInvariant m hodd (2 * t * d) n - (2 - (t : Int) * (d : Int))) = 0 := by
      rw [Int.mul_sub, hmaster, Int.sub_self]
    have hzero := (Int.mul_eq_zero.mp hsub).resolve_left (by omega)
    omega


/-- THEOREM F2 (Infinite Fermat/Proth Family `m = 2^k + 1` Specialization):
    For ALL k ≥ 1, ALL t ≥ 1, and ALL n < 2^(2*t*k):
      dualInvariant (2^k + 1) (2*t*k) n = if (2^k + 1) ∣ n then 0 else 2 - t * k. -/
theorem fermat_dual_invariant_law {k t n : Nat} (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hn : n < 2 ^ (2 * t * k)) :
    dualInvariant (2 ^ k + 1) (fermat_odd hk) (2 * t * k) n =
      if (2 ^ k + 1) ∣ n then 0 else 2 - (t : Int) * (k : Int) := by
  have hm3 : 3 ≤ 2 ^ k + 1 := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  exact negacyclic_dual_invariant_law (fermat_odd hk) hm3 hk (Nat.dvd_refl _) ht hn

/-- THEOREM F3 (Sharp Negacyclic Divisibility Equivalence whenever `t * d ≠ 2`):
    For ALL odd `m ≥ 3`, `d ≥ 1` with `m ∣ (2^d + 1)`, ALL `t ≥ 1` with `t * d ≠ 2`, and ALL `n < 2^(2*t*d)`:
      m ∣ n ↔ popcount(Q_{2*t*d}(n)) - popcount(n / m) = W_m(n, 2*t*d). -/
theorem negacyclic_divisibility_iff_ne_two {m d t n : Nat} (hodd : m % 2 = 1) (hm3 : 3 ≤ m)
    (hd : 1 ≤ d) (hdvd_m : m ∣ 2 ^ d + 1) (ht : 1 ≤ t) (hne2 : t * d ≠ 2)
    (hn : n < 2 ^ (2 * t * d)) :
    m ∣ n ↔
      (popcount (twoAdicQuot m hodd (2 * t * d) n) : Int) -
      (popcount (n / m) : Int) =
      (carryDomCount m hodd (2 * t * d) n : Int) := by
  have hlaw := negacyclic_dual_invariant_law hodd hm3 hd hdvd_m ht hn
  have hinv := dualInvariant_eq hodd (2 * t * d) n hn
  constructor
  · intro hdvd
    simp only [hdvd, ↓reduceIte] at hlaw
    rw [hinv] at hlaw
    omega
  · intro heq
    by_cases hdvd : m ∣ n
    · exact hdvd
    · exfalso
      simp only [hdvd, ↓reduceIte] at hlaw
      rw [hinv] at hlaw
      have htd : (t : Int) * (d : Int) = 2 := by omega
      have htd_nat : t * d = 2 := by exact_mod_cast htd
      exact hne2 htd_nat

/-- THEOREM F4 (Exact Exceptional Collapse when `t * d = 2`):
    When `t * d = 2` (so `L = 4`, covering `(m,d,t) = (3,1,2)` and `(5,2,1)`),
    `dualInvariant m 4 n = 0` IDENTICALLY for EVERY `n < 16` (divisible OR NOT!). -/
theorem negacyclic_exceptional_collapse_eq_two {m d t n : Nat} (hodd : m % 2 = 1) (hm3 : 3 ≤ m)
    (hd : 1 ≤ d) (hdvd_m : m ∣ 2 ^ d + 1) (ht : 1 ≤ t) (heq2 : t * d = 2)
    (hn : n < 2 ^ (2 * t * d)) :
    dualInvariant m hodd (2 * t * d) n = 0 := by
  have hlaw := negacyclic_dual_invariant_law hodd hm3 hd hdvd_m ht hn
  by_cases hdvd : m ∣ n
  · simp only [hdvd, ↓reduceIte] at hlaw; exact hlaw
  · simp only [hdvd, ↓reduceIte] at hlaw
    have htdI : (t : Int) * (d : Int) = 2 := by exact_mod_cast heq2
    omega

/-- THEOREM F5 (Residue-Blind Negacyclic 2-adic Reciprocal Popcount Law):
    For ALL odd `m ≥ 3`, `d ≥ 1` with `m ∣ (2^d + 1)`, ALL `t ≥ 1`, and ALL `0 < r < m`:
      popcount(Q_{2*t*d}(r)) = t * d + 1 - v2 r
    COMPLETELY INDEPENDENT OF `popcount r`! -/
theorem negacyclic_reciprocal_popcount_law {m d t r : Nat} (hodd : m % 2 = 1) (hm3 : 3 ≤ m)
    (hd : 1 ≤ d) (hdvd_m : m ∣ 2 ^ d + 1) (ht : 1 ≤ t) (hr_pos : 0 < r) (hr_lt : r < m) :
    popcount (twoAdicQuot m hodd (2 * t * d) r) = t * d + 1 - v2 r := by
  have hm_le : m ≤ 2 ^ d + 1 := Nat.le_of_dvd (Nat.succ_pos _) hdvd_m
  have h2d_le : 2 * d ≤ 2 * t * d := by
    have : 2 * d = 2 * 1 * d := by omega
    rw [this]
    exact Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 ht)
  have hpow_ge : 2 ^ d + 1 ≤ 2 ^ (2 * d) := by
    have h2 : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
    have hmul : 2 ^ (2 * d) = 2 ^ d * 2 ^ d := by
      have : 2 * d = d + d := by omega
      rw [this, Nat.pow_add]
    have hsq : 2 * 2 ^ d ≤ 2 ^ d * 2 ^ d := Nat.mul_le_mul_right (2 ^ d) h2
    omega
  have hr_pow : r < 2 ^ (2 * t * d) := by
    have h1 : r < 2 ^ (2 * d) := by omega
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) h2d_le)
  have hndvd : ¬ (m ∣ r) := by
    intro hdvd; have := Nat.le_of_dvd hr_pos hdvd; omega
  have hlaw := negacyclic_dual_invariant_law hodd hm3 hd hdvd_m ht hr_pow
  simp only [hndvd, ↓reduceIte] at hlaw
  have hinv := dualInvariant_eq hodd (2 * t * d) r hr_pow
  rw [Nat.div_eq_of_lt hr_lt, popcount_zero] at hinv
  have hcomp := carry_complementarity_law hodd (2 * t * d) r hr_pow hndvd
  rw [Nat.div_eq_of_lt hr_lt, Nat.mod_eq_of_lt hr_lt] at hcomp
  have hc0 : carriesAdd 0 (twoAdicQuot m hodd (2 * t * d) r) = 0 := by
    have h := kummer_carriesAdd 0 (twoAdicQuot m hodd (2 * t * d) r)
    simp only [Nat.zero_add, popcount_zero] at h; omega
  rw [hc0, Nat.zero_add] at hcomp
  have hv2_lt : v2 r < 2 * t * d := v2_lt_of_lt_pow2 hr_pos hr_pow
  have hv2_le_d : v2 r ≤ d := by
    apply Nat.le_of_not_lt
    intro hgt
    have hdvd_r : 2 ^ (d + 1) ∣ r := (pow2_dvd_iff_le_v2 hr_pos).mpr (by omega)
    have hle_r : 2 ^ (d + 1) ≤ r := Nat.le_of_dvd hr_pos hdvd_r
    rw [Nat.pow_succ] at hle_r
    omega
  have hd_le_td : d ≤ t * d := by
    calc d = 1 * d := (Nat.one_mul d).symm
    _ ≤ t * d := Nat.mul_le_mul_right d ht
  have h2td : 2 * t * d = 2 * (t * d) := Nat.mul_assoc 2 t d
  have hcomp' : carryDomCount m hodd (2 * t * d) r = 2 * (t * d) - 1 - v2 r := by
    rw [hcomp, h2td]
  have htd_cast : ((t * d : Nat) : Int) = (t : Int) * (d : Int) := by push_cast; rfl
  rw [hinv, hcomp', ← htd_cast] at hlaw
  rw [h2td] at hv2_lt
  omega

/-- Fermat specialization `m = 2^k + 1` of the residue-blind 2-adic reciprocal popcount law. -/
theorem fermat_reciprocal_popcount_law {k t r : Nat} (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hr_pos : 0 < r) (hr_lt : r < 2 ^ k + 1) :
    popcount (twoAdicQuot (2 ^ k + 1) (fermat_odd hk) (2 * t * k) r) = t * k + 1 - v2 r := by
  have hm3 : 3 ≤ 2 ^ k + 1 := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  exact negacyclic_reciprocal_popcount_law (fermat_odd hk) hm3 hk (Nat.dvd_refl _) ht hr_pos hr_lt

/-! ## Layer 6: Kernel-Checked Non-Vacuity Witnesses, Sharpness Counterexamples, & Axiom Audit -/

/-- Non-vacuity witness 1 (Mersenne non-multiple): k=3 (m=7), t=3 (L=9), n=100 (100 % 7 = 2, popcount 2 = 1),
    giving dualInvariant = 2 - 3*1 = -1. -/
theorem witness_mersenne_non_multiple :
    dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 9 100 = -1 := by
  have h := mersenne_dual_invariant_law (k := 3) (t := 3) (n := 100) (by omega) (by omega) (by decide)
  have hndvd : ¬ (7 ∣ 100) := by decide
  simpa [hndvd, popcount] using h

/-- Non-vacuity witness 2 (Mersenne multiple): k=3 (m=7), t=3 (L=9), n=98 = 7 * 14,
    giving dualInvariant = 0 and synchronized traces everywhere. -/
theorem witness_mersenne_multiple :
    dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 9 98 = 0 ∧
    (∀ i, i ≤ 9 → remAt 7 (by omega) 9 98 i = carryAt 7 (mersenne_odd (k := 3) (by omega)) 98 i) := by
  have h1 := mersenne_dual_invariant_law (k := 3) (t := 3) (n := 98) (by omega) (by omega) (by decide)
  have hdvd : 7 ∣ 98 := ⟨14, by decide⟩
  have h2 := (synchronized_trace_divisibility_iff (mersenne_odd (k := 3) (by omega)) 9 98 (by decide)).2.1.mp hdvd
  exact ⟨by simpa [hdvd] using h1, h2⟩

/-- Non-vacuity witness 3 (Fermat non-multiple): k=3 (m=9), t=1 (L=6), n=23 (9 ∤ 23),
    giving residue-blind dualInvariant = 2 - 1*3 = -1 and popcount(Q_6(5)) = 4. -/
theorem witness_fermat_m9 :
    dualInvariant 9 (fermat_odd (k := 3) (by omega)) 6 23 = -1 ∧
    popcount (twoAdicQuot 9 (fermat_odd (k := 3) (by omega)) 6 5) = 4 := by
  have h1 := fermat_dual_invariant_law (k := 3) (t := 1) (n := 23) (by omega) (by omega) (by decide)
  have hndvd : ¬ (9 ∣ 23) := by decide
  have h2 := fermat_reciprocal_popcount_law (k := 3) (t := 1) (r := 5) (by omega) (by omega) (by omega) (by omega)
  have hv2 : v2 5 = 0 := v2_odd (by decide)
  rw [hv2] at h2
  exact ⟨by simpa [hndvd] using h1, by simpa using h2⟩

/-- Non-vacuity witness 4 (Proper negacyclic divisor `m = 11 ∣ 2^5 + 1 = 33`, NOT of form `2^k + 1`!):
    At d=5, t=1, L=10, n=100 (11 ∤ 100), dualInvariant = 2 - 5 = -3 and popcount(Q_10(3)) = 6! -/
theorem witness_proper_negacyclic_m11 :
    dualInvariant 11 (by decide) 10 100 = -3 ∧
    popcount (twoAdicQuot 11 (by decide) 10 3) = 6 := by
  have hdvd11 : 11 ∣ 2 ^ 5 + 1 := ⟨3, by decide⟩
  have h1 := negacyclic_dual_invariant_law (m := 11) (d := 5) (t := 1) (n := 100)
    (by decide) (by omega) (by omega) hdvd11 (by omega) (by decide)
  have hndvd : ¬ (11 ∣ 100) := by decide
  have h2 := negacyclic_reciprocal_popcount_law (m := 11) (d := 5) (t := 1) (r := 3)
    (by decide) (by omega) (by omega) hdvd11 (by omega) (by omega) (by omega)
  have hv2 : v2 3 = 0 := v2_odd (by decide)
  rw [hv2] at h2
  exact ⟨by simpa [hndvd] using h1, by simpa using h2⟩

/-- SHARPNESS 1 (Infinite family of counterexamples to Mersenne divisibility iff at `t = 2`):
    For EVERY `k ≥ 2`, at `t = 2` (`L = 2*k`), `n = 1` is NOT divisible by `2^k - 1`,
    YET `dualInvariant (2^k - 1) (2*k) 1 = 0`! Thus `t ≥ 3` in Theorem E2 is sharp! -/
theorem sharpness_mersenne_t_eq_2_infinite (k : Nat) (hk : 2 ≤ k) :
    ¬ ((2 ^ k - 1) ∣ 1) ∧
    dualInvariant (2 ^ k - 1) (mersenne_odd (by omega)) (2 * k) 1 = 0 := by
  have hm3 : 3 ≤ 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  have hndvd : ¬ ((2 ^ k - 1) ∣ 1) := by
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
  have hlt : 1 < 2 ^ (2 * k) := by
    have : 2 ≤ 2 ^ (2 * k) := by
      calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hlaw := mersenne_dual_invariant_law (k := k) (t := 2) (n := 1) hk (by omega) hlt
  simp only [hndvd, ↓reduceIte] at hlaw
  rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ k - 1)] at hlaw
  have hpc1 : popcount 1 = 1 := by rw [popcount_step]; simp [popcount_zero]
  rw [hpc1] at hlaw
  exact ⟨hndvd, by omega⟩

/-- SHARPNESS 2 (Infinite family of counterexamples to Mersenne divisibility iff at `t = 1`):
    For EVERY `k ≥ 3`, at `t = 1` (`L = k`), `n = 3` is NOT divisible by `2^k - 1`,
    YET `dualInvariant (2^k - 1) k 3 = 0`! -/
theorem sharpness_mersenne_t_eq_1_infinite (k : Nat) (hk : 3 ≤ k) :
    ¬ ((2 ^ k - 1) ∣ 3) ∧
    dualInvariant (2 ^ k - 1) (mersenne_odd (by omega)) (1 * k) 3 = 0 := by
  have hm7 : 7 ≤ 2 ^ k - 1 := by
    have : 8 ≤ 2 ^ k := by
      calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  have hndvd : ¬ ((2 ^ k - 1) ∣ 3) := by
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
  have hlt : 3 < 2 ^ (1 * k) := by
    rw [Nat.one_mul]; omega
  have hlaw := mersenne_dual_invariant_law (k := k) (t := 1) (n := 3) (by omega) (by omega) hlt
  simp only [hndvd, ↓reduceIte] at hlaw
  rw [Nat.mod_eq_of_lt (by omega : 3 < 2 ^ k - 1)] at hlaw
  have hpc3 : popcount 3 = 2 := by
    rw [popcount_step, popcount_step]; simp [popcount_zero]
  rw [hpc3] at hlaw
  exact ⟨hndvd, by omega⟩

/-- SHARPNESS 3 (Exact exception set `t * d = 2` for Negacyclic divisibility iff):
    At `(m, d, t) = (5, 2, 1)` and `(3, 1, 2)` (`L = 4`), `n = 1` is NOT divisible by `m`,
    YET `dualInvariant m 4 1 = 0`! Thus `t * d ≠ 2` in Theorem F3 is sharp! -/
theorem sharpness_negacyclic_td_eq_2 :
    (¬ (5 ∣ 1) ∧ dualInvariant 5 (fermat_odd (k := 2) (by omega)) 4 1 = 0) ∧
    (¬ (3 ∣ 1) ∧ dualInvariant 3 (fermat_odd (k := 1) (by omega)) 4 1 = 0) := by
  have h5 := negacyclic_exceptional_collapse_eq_two (m := 5) (d := 2) (t := 1) (n := 1)
    (fermat_odd (k := 2) (by omega)) (by omega) (by omega) (Nat.dvd_refl _) (by omega) (by decide) (by decide)
  have h3 := negacyclic_exceptional_collapse_eq_two (m := 3) (d := 1) (t := 2) (n := 1)
    (fermat_odd (k := 1) (by omega)) (by omega) (by omega) (Nat.dvd_refl _) (by omega) (by decide) (by decide)
  exact ⟨⟨by decide, h5⟩, ⟨by decide, h3⟩⟩

/-- SHARPNESS 4 (Non-negacyclic odd modulus `m = 7` breaks residue-blindness):
    At `m = 7, L = 3`, `1` and `3` are both non-multiples of 7, yet
    `dualInvariant 7 3 1 = 1 ≠ 0 = dualInvariant 7 3 3`! -/
theorem sharpness_non_negacyclic_breaks_residue_blindness :
    dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 3 1 = 1 ∧
    dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 3 3 = 0 ∧
    dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 3 1 ≠
      dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 3 3 := by
  have h1 := mersenne_dual_invariant_law (k := 3) (t := 1) (n := 1) (by omega) (by omega) (by decide)
  have h3 := mersenne_dual_invariant_law (k := 3) (t := 1) (n := 3) (by omega) (by omega) (by decide)
  have hpc1 : popcount 1 = 1 := by rw [popcount_step]; simp [popcount_zero]
  have hpc3 : popcount 3 = 2 := by rw [popcount_step, popcount_step]; simp [popcount_zero]
  have hv1 : dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 3 1 = 1 := by
    have hnd : ¬ ((2 ^ 3 - 1) ∣ 1) := by decide
    have hm1 : 1 % (2 ^ 3 - 1) = 1 := by decide
    simp only [hnd, ↓reduceIte, hm1, hpc1] at h1
    change dualInvariant (2 ^ 3 - 1) (mersenne_odd (by omega)) (1 * 3) 1 = 1
    omega
  have hv3 : dualInvariant 7 (mersenne_odd (k := 3) (by omega)) 3 3 = 0 := by
    have hnd : ¬ ((2 ^ 3 - 1) ∣ 3) := by decide
    have hm3 : 3 % (2 ^ 3 - 1) = 3 := by decide
    simp only [hnd, ↓reduceIte, hm3, hpc3] at h3
    change dualInvariant (2 ^ 3 - 1) (mersenne_odd (by omega)) (1 * 3) 3 = 0
    omega
  exact ⟨hv1, hv3, by omega⟩

/-- SHARPNESS 5 (Non-period width `L = 3` breaks residue-blindness even for Fermat `m = 5`):
    At `m = 5, L = 3` (since `4 ∤ 3`), `dualInvariant 5 3 1 = 0 ≠ 1 = dualInvariant 5 3 3`! -/
theorem sharpness_non_period_width_breaks_collapse :
    dualInvariant 5 (by decide) 3 1 = 0 ∧
    dualInvariant 5 (by decide) 3 3 = 1 ∧
    dualInvariant 5 (by decide) 3 1 ≠ dualInvariant 5 (by decide) 3 3 := by
  have h1 := master_dual_carry_residue_law (m := 5) (by decide) 3 1 (by decide)
  have h3 := master_dual_carry_residue_law (m := 5) (by decide) 3 3 (by decide)
  have hc1 : carryAt 5 (by decide) 1 3 = 3 := by decide
  have ho1 : halvingOrbitSum 5 (1 % 5) 3 = 8 := by decide
  have hc3 : carryAt 5 (by decide) 3 3 = 4 := by decide
  have ho3 : halvingOrbitSum 5 (3 % 5) 3 = 9 := by decide
  rw [hc1, ho1] at h1
  rw [hc3, ho3] at h3
  exact ⟨by omega, by omega, by omega⟩

/-- SHARPNESS 6 (Oddness of `m` is necessary for the 2-adic division carry transducer):
    For even `m = 2`, there is NO `q` with `(2 * q) % 2 = 1`. -/
theorem sharpness_even_modulus_no_2adic_quotient : ¬ ∃ q : Nat, (2 * q) % 2 = 1 := by
  rintro ⟨q, hq⟩; omega

end ModularCarryResidueDuality
