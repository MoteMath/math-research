/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FenwickTriggerChainMonoid.Defs

/-!
# Theorems (`fenwick-trigger-chain-monoid`)

Full proofs of the headline infinite theorems of Fenwick Low-Bit Trigger-Chain Transducer and Monoid Dichotomy.
-/

namespace FenwickTransducer

theorem lowbit_le (x : Nat) : lowbit x ≤ x := by
  induction x using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [lowbit_zero]
    | succ m =>
      by_cases hodd : (m + 1) % 2 = 1
      · have : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
        rw [this, lowbit_odd]; omega
      · have : m + 1 = 2 * ((m + 1) / 2) := by omega
        have hlt : (m + 1) / 2 < m + 1 := by omega
        rw [this, lowbit_even]
        have := ih ((m + 1) / 2) hlt
        omega

theorem lowbit_eq_pow_ctz {x : Nat} (hx : 0 < x) : lowbit x = 2 ^ ctz x := by
  induction x using Nat.strongRecOn with
  | ind n ih =>
    by_cases hodd : n % 2 = 1
    · have h1 : n ≠ 0 := by omega
      unfold lowbit ctz
      simp [h1, hodd]
    · have h1 : n ≠ 0 := by omega
      have hdiv : 0 < n / 2 := by omega
      have hlt : n / 2 < n := by omega
      unfold lowbit ctz
      simp only [h1, ↓reduceDIte, hodd, ↓reduceIte]
      rw [ih (n / 2) hlt hdiv, Nat.add_comm 1, Nat.pow_succ, Nat.mul_comm]

theorem lowbit_dvd (x : Nat) : lowbit x ∣ x := by
  induction x using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [lowbit_zero]
    | succ m =>
      by_cases hodd : (m + 1) % 2 = 1
      · have : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
        rw [this, lowbit_odd]; exact Nat.one_dvd _
      · have : m + 1 = 2 * ((m + 1) / 2) := by omega
        have hlt : (m + 1) / 2 < m + 1 := by omega
        rw [this, lowbit_even]
        exact Nat.mul_dvd_mul_left 2 (ih ((m + 1) / 2) hlt)

theorem fenwickD_zero : fenwickD 0 = 0 := by
  simp [fenwickD, lowbit_zero]

theorem fenwickD_odd (k : Nat) : fenwickD (2 * k + 1) = 2 * k := by
  simp [fenwickD, lowbit_odd]

theorem fenwickD_even (k : Nat) : fenwickD (2 * k) = 2 * fenwickD k := by
  simp only [fenwickD, lowbit_even]
  have := lowbit_le k
  omega

theorem fenwickU_zero : fenwickU 0 = 0 := by
  simp [fenwickU, lowbit_zero]

theorem fenwickU_odd (k : Nat) : fenwickU (2 * k + 1) = 2 * (k + 1) := by
  simp only [fenwickU, lowbit_odd]; omega

theorem fenwickU_even (k : Nat) : fenwickU (2 * k) = 2 * fenwickU k := by
  simp only [fenwickU, lowbit_even]; omega

theorem fenwickD_le (x : Nat) : fenwickD x ≤ x := Nat.sub_le _ _

theorem fenwickU_le_double (x : Nat) : fenwickU x ≤ 2 * x := by
  simp only [fenwickU]
  have := lowbit_le x
  omega

/-- Helper: bitwise AND commutes with doubling. -/
theorem and_double (a b : Nat) : (2 * a) &&& (2 * b) = 2 * (a &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_and]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ]
    have hda : ∀ z : Nat, 2 * z / (2 ^ j * 2) = z / 2 ^ j := by
      intro z; rw [Nat.mul_comm (2 ^ j) 2, Nat.mul_div_mul_left _ _ (by omega)]
    rw [hda a, hda b, hda (a &&& b)]
    have htb := Nat.testBit_and a b j
    simpa only [Nat.testBit, Nat.shiftRight_eq_div_pow] using htb.symm

/-- Helper: for odd `v < 2^n`, `v &&& (2^n - v) = 1`. -/
theorem odd_and_twos_comp (n v : Nat) (hv : v < 2 ^ n) (hodd : v % 2 = 1) :
    v &&& (2 ^ n - v) = 1 := by
  induction n generalizing v with
  | zero => omega
  | succ n ih =>
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    have hv_eq : v = 2 * (v / 2) + 1 := by omega
    have hsub : 2 ^ (n + 1) - v = 2 * (2 ^ n - 1 - v / 2) + 1 := by omega
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      rw [Nat.testBit_and]
      simp [Nat.testBit_zero, hodd, hsub]
    | succ j =>
      rw [Nat.testBit_and]
      have h1b : Nat.testBit 1 (j + 1) = false := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have : 2 ^ (j + 1) ≥ 2 := by
          have := Nat.one_le_pow j 2 (by omega)
          rw [Nat.pow_succ]; omega
        rw [Nat.div_eq_of_lt (by omega)]
        rfl
      rw [h1b]
      -- Bit (j+1) of v is bit j of (v/2), and bit (j+1) of (2^(n+1)-v) is bit j of (2^n - 1 - v/2)
      have hdiv1 : v / 2 ^ (j + 1) = (v / 2) / 2 ^ j := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
      have hdiv2 : (2 ^ (n + 1) - v) / 2 ^ (j + 1) = (2 ^ n - 1 - v / 2) / 2 ^ j := by
        rw [hsub, Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
        congr 1; omega
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv1, hdiv2]
      -- Now (v/2) + (2^n - 1 - v/2) = 2^n - 1, so their bit j cannot both be 1!
      by_cases hjn : j < n
      · have ha : v / 2 < 2 ^ n := by omega
        have hsum : (v / 2) / 2 ^ j + (2 ^ n - 1 - v / 2) / 2 ^ j = 2 ^ (n - j) - 1 := by
          have hpowj : 2 ^ n = 2 ^ (n - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
          have hq : (v / 2) / 2 ^ j < 2 ^ (n - j) := by
            rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), ← hpowj]; exact ha
          have hr : (v / 2) % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
          have h1p : 1 ≤ 2 ^ (n - j) := Nat.one_le_pow _ _ (by omega)
          have hdecomp : 2 ^ n - 1 - v / 2 =
              2 ^ j * (2 ^ (n - j) - 1 - (v / 2) / 2 ^ j) + (2 ^ j - 1 - (v / 2) % 2 ^ j) := by
            have hd := Nat.div_add_mod (v / 2) (2 ^ j)
            have hmul : 2 ^ j * (2 ^ (n - j) - 1 - (v / 2) / 2 ^ j) + 2 ^ j * ((v / 2) / 2 ^ j)
                = 2 ^ j * (2 ^ (n - j) - 1) := by
              rw [← Nat.mul_add]; congr 1; omega
            have hmul2 : 2 ^ j * (2 ^ (n - j) - 1) + 2 ^ j = 2 ^ n := by
              have hfact : 2 ^ j * (2 ^ (n - j) - 1) + 2 ^ j * 1 =
                  2 ^ j * ((2 ^ (n - j) - 1) + 1) := (Nat.mul_add _ _ _).symm
              rw [Nat.mul_one, Nat.sub_add_cancel h1p] at hfact
              rw [hfact, Nat.mul_comm, ← hpowj]
            have h2j : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by omega)
            omega
          rw [hdecomp, Nat.mul_add_div (Nat.two_pow_pos j)]
          have hrem : 2 ^ j - 1 - (v / 2) % 2 ^ j < 2 ^ j := by
            have := Nat.two_pow_pos j; omega
          rw [Nat.div_eq_of_lt hrem]
          omega
        have h1p : 1 ≤ 2 ^ (n - j) := Nat.one_le_pow _ _ (by omega)
        have heven : 2 ^ (n - j) % 2 = 0 := by
          have : n - j = (n - j - 1) + 1 := by omega
          rw [this, Nat.pow_succ]; omega
        have hodd_sum : ((v / 2) / 2 ^ j + (2 ^ n - 1 - v / 2) / 2 ^ j) % 2 = 1 := by
          rw [hsum]; omega
        have hA : (1 &&& (v / 2) / 2 ^ j) = ((v / 2) / 2 ^ j) % 2 := by
          rw [Nat.and_comm, Nat.and_one_is_mod]
        have hB : (1 &&& (2 ^ n - 1 - v / 2) / 2 ^ j) = ((2 ^ n - 1 - v / 2) / 2 ^ j) % 2 := by
          rw [Nat.and_comm, Nat.and_one_is_mod]
        rw [hA, hB]
        by_cases hm1 : ((v / 2) / 2 ^ j) % 2 = 1
        · have hm2 : ((2 ^ n - 1 - v / 2) / 2 ^ j) % 2 = 0 := by omega
          simp [hm1, hm2]
        · have hm1' : ((v / 2) / 2 ^ j) % 2 = 0 := by omega
          simp [hm1']
      · have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
        have hz : (v / 2) / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
        rw [hz]; rfl

/-- Hardware identity connecting `lowbit` to two's-complement `x &&& (-x)` on `BitVec w`. -/
theorem lowbit_bitvec_eq (w : Nat) (x : BitVec w) :
    (x &&& (-x)).toNat = lowbit x.toNat := by
  cases x with
  | ofFin xf =>
    revert xf
    induction w with
    | zero =>
      intro ⟨v, hv⟩
      have hv0 : v = 0 := by omega
      subst hv0
      simp [lowbit_zero]
    | succ w ih =>
      intro ⟨v, hv⟩
      by_cases hv0 : v = 0
      · subst hv0
        simp [lowbit_zero]
      · by_cases hodd : v % 2 = 1
        · have h1 : lowbit v = 1 := by
            have : v = 2 * (v / 2) + 1 := by omega
            rw [this, lowbit_odd]
          have htoNat : (BitVec.ofFin ⟨v, hv⟩).toNat = v := rfl
          have hneg : (-(BitVec.ofFin ⟨v, hv⟩)).toNat = 2 ^ (w + 1) - v := by
            simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ (w + 1) - v < 2 ^ (w + 1) by omega)]
          rw [BitVec.toNat_and, hneg, htoNat, h1]
          exact odd_and_twos_comp (w + 1) v hv hodd
        · have hv2 : v = 2 * (v / 2) := by omega
          have hdiv_lt : v / 2 < 2 ^ w := by rw [Nat.pow_succ] at hv; omega
          have hih := ih ⟨v / 2, hdiv_lt⟩
          have hneg_w : (-(BitVec.ofFin ⟨v / 2, hdiv_lt⟩)).toNat = 2 ^ w - v / 2 := by
            have hne0 : v / 2 ≠ 0 := by omega
            simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ w - v / 2 < 2 ^ w by omega)]
          have hneg_succ : (-(BitVec.ofFin ⟨v, hv⟩)).toNat = 2 * (2 ^ w - v / 2) := by
            simp [BitVec.toNat_neg, Nat.mod_eq_of_lt (show 2 ^ (w + 1) - v < 2 ^ (w + 1) by omega)]
            rw [Nat.pow_succ]; omega
          have hto1 : (BitVec.ofFin ⟨v, hv⟩).toNat = v := rfl
          have hto2 : (BitVec.ofFin ⟨v / 2, hdiv_lt⟩).toNat = v / 2 := rfl
          rw [BitVec.toNat_and, hneg_succ, hto1]
          rw [BitVec.toNat_and, hneg_w, hto2] at hih
          calc v &&& 2 * (2 ^ w - v / 2)
              = (2 * (v / 2)) &&& (2 * (2 ^ w - v / 2)) := by rw [← hv2]
            _ = 2 * ((v / 2) &&& (2 ^ w - v / 2)) := and_double _ _
            _ = 2 * lowbit (v / 2) := by rw [hih]
            _ = lowbit (2 * (v / 2)) := (lowbit_even _).symm
            _ = lowbit v := by rw [← hv2]

-- ============================================================================
-- SECTION 2: Reusable General LSB-First Finite-State Transducer Engine
-- ============================================================================

namespace LsbTransducer

/-- Output of `run` for `n` bits is strictly less than 2^n. -/
theorem run_lt_pow {Q : Type} (T : LsbTransducer Q) (q : Q) (n x : Nat) :
    (T.run q n x).2 < 2 ^ n := by
  induction n generalizing q x with
  | zero => simp [run]
  | succ n ih =>
    rw [run]
    cases hstep : T.step q (x % 2 == 1) with
    | mk q' bOut =>
      dsimp only
      have hrest := ih q' (x / 2)
      rw [Nat.pow_succ]
      cases bOut <;> simp <;> omega

/-- Exact composition theorem (∀ n, x : Nat): product transducer computes T1 ∘ T2. -/
theorem run_compose {Q1 Q2 : Type} (T1 : LsbTransducer Q1) (T2 : LsbTransducer Q2)
    (q1 : Q1) (q2 : Q2) (n x : Nat) :
    ((T1.compose T2).run (q1, q2) n x).2 = (T1.run q1 n (T2.run q2 n x).2).2 := by
  cases T1 with | mk init1 step1 =>
  cases T2 with | mk init2 step2 =>
  induction n generalizing q1 q2 x with
  | zero => simp [run]
  | succ n ih =>
    rw [run, run, run]
    dsimp only [compose]
    cases h2 : step2 q2 (x % 2 == 1) with
    | mk q2' bMid =>
      dsimp only
      have hmod : (((if bMid then 1 else 0) + 2 * (LsbTransducer.run ⟨init2, step2⟩ q2' n (x / 2)).2) % 2 == 1) = bMid := by
        cases bMid <;> simp
      have hdiv : ((if bMid then 1 else 0) + 2 * (LsbTransducer.run ⟨init2, step2⟩ q2' n (x / 2)).2) / 2 =
          (LsbTransducer.run ⟨init2, step2⟩ q2' n (x / 2)).2 := by
        cases bMid <;> simp <;> omega
      rw [hmod, hdiv]
      cases h1 : step1 q1 bMid with
      | mk q1' bOut =>
        dsimp only
        exact congrArg (fun r => (if bOut then 1 else 0) + 2 * r) (ih q1' q2' (x / 2))

/-- Corollary: `evalMod` commutes with transducer composition for all n, x. -/
theorem evalMod_compose {Q1 Q2 : Type} (T1 : LsbTransducer Q1) (T2 : LsbTransducer Q2)
    (n x : Nat) :
    (T1.compose T2).evalMod n x = T1.evalMod n (T2.evalMod n x) :=
  run_compose T1 T2 T1.init T2.init n x

/-- REUSABLE FINITE-TO-INFINITE LIFTING ENGINE:
    Any simulation relation `R` preserved by single-bit steps lifts to universal equality
    across all bit-widths `n : Nat` and all inputs `x : Nat`. -/
theorem run_eq_of_sim {Q1 Q2 : Type} {T1 : LsbTransducer Q1} {T2 : LsbTransducer Q2}
    {R : Q1 → Q2 → Prop} (hSim : IsSim T1 T2 R)
    {q1 : Q1} {q2 : Q2} (hR : R q1 q2) (n x : Nat) :
    (T1.run q1 n x).2 = (T2.run q2 n x).2 := by
  induction n generalizing q1 q2 x with
  | zero => simp [run]
  | succ n ih =>
    rw [run, run]
    dsimp only
    have ⟨hout, hnext⟩ := hSim q1 q2 (x % 2 == 1) hR
    rw [hout, ih hnext (x / 2)]

theorem evalMod_eq_of_sim {Q1 Q2 : Type} {T1 : LsbTransducer Q1} {T2 : LsbTransducer Q2}
    {R : Q1 → Q2 → Prop} (hSim : IsSim T1 T2 R) (hInit : R T1.init T2.init) :
    ∀ n x : Nat, T1.evalMod n x = T2.evalMod n x :=
  fun n x => run_eq_of_sim hSim hInit n x

/-- `run` depends only on the lowest `n` bits of `x` (2-adic causality / 1-Lipschitz). -/
theorem run_mod_eq {Q : Type} (T : LsbTransducer Q) (q : Q) (n x : Nat) :
    T.run q n (x % 2 ^ n) = T.run q n x := by
  induction n generalizing q x with
  | zero => simp [run]
  | succ n ih =>
    rw [run, run]
    dsimp only
    have hm : (x % 2 ^ (n + 1)) % 2 = x % 2 := by
      rw [Nat.pow_succ]
      exact Nat.mod_mod_of_dvd x (Nat.dvd_mul_left 2 _)
    have hd : (x % 2 ^ (n + 1)) / 2 = (x / 2) % 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
      have h1 : x = 2 * (x / 2) + x % 2 := by omega
      have h2 : x % (2 * 2 ^ n) = 2 * ((x / 2) % 2 ^ n) + x % 2 := by
        conv => lhs; rw [h1]
        have hlt : 2 * ((x / 2) % 2 ^ n) + x % 2 < 2 * 2 ^ n := by
          have := Nat.mod_lt (x / 2) (Nat.two_pow_pos n)
          omega
        have hq : 2 * (x / 2) + x % 2 =
            2 * 2 ^ n * ((x / 2) / 2 ^ n) + (2 * ((x / 2) % 2 ^ n) + x % 2) := by
          have := Nat.div_add_mod (x / 2) (2 ^ n)
          rw [Nat.mul_assoc]
          omega
        rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [h2]; omega
    rw [hm, hd, ih]

/-- Run on a concatenated bit-stream `x + 2^a * y` splits cleanly at bit `a`. -/
theorem run_add_pow {Q : Type} (T : LsbTransducer Q) (q : Q) (a b x y : Nat)
    (hx : x < 2 ^ a) :
    T.run q (a + b) (x + 2 ^ a * y) =
      let (qa, outA) := T.run q a x
      let (qab, outB) := T.run qa b y
      (qab, outA + 2 ^ a * outB) := by
  induction a generalizing q x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    simp [run]
  | succ a ih =>
    have hsum : a + 1 + b = (a + b) + 1 := by omega
    rw [hsum, run]
    have hpow : 2 ^ (a + 1) * y = 2 * (2 ^ a * y) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    have hmod : (x + 2 ^ (a + 1) * y) % 2 = x % 2 := by
      rw [hpow]; omega
    have hdiv : (x + 2 ^ (a + 1) * y) / 2 = x / 2 + 2 ^ a * y := by
      rw [hpow]; omega
    have hxdiv : x / 2 < 2 ^ a := by rw [Nat.pow_succ] at hx; omega
    rw [hmod, hdiv]
    cases hstep : T.step q (x % 2 == 1) with
    | mk q' bOut =>
      dsimp only
      rw [ih q' (x / 2) hxdiv]
      rw [run, hstep]
      dsimp only
      congr 1
      have hpow2 : 2 ^ (a + 1) * (T.run (T.run q' a (x / 2)).1 b y).2 =
          2 * (2 ^ a * (T.run (T.run q' a (x / 2)).1 b y).2) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
      omega

end LsbTransducer

theorem T_id_run (n x : Nat) : (T_id.run () n x).2 = x % 2 ^ n := by
  induction n generalizing x with
  | zero => simp [LsbTransducer.run, Nat.mod_one]
  | succ n ih =>
    rw [LsbTransducer.run]
    have hstep : T_id.step () (x % 2 == 1) = ((), x % 2 == 1) := rfl
    rw [hstep]
    dsimp only
    rw [ih (x / 2)]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
    have hlt : 2 * ((x / 2) % 2 ^ n) + x % 2 < 2 * 2 ^ n := by
      have := Nat.mod_lt (x / 2) (Nat.two_pow_pos n); omega
    have hq : x = 2 * 2 ^ n * ((x / 2) / 2 ^ n) + (2 * ((x / 2) % 2 ^ n) + x % 2) := by
      have := Nat.div_add_mod (x / 2) (2 ^ n)
      rw [Nat.mul_assoc]; omega
    have hmod : x % (2 * 2 ^ n) = 2 * ((x / 2) % 2 ^ n) + x % 2 := by
      conv => lhs; rw [hq]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    rw [hmod]
    by_cases hodd : x % 2 = 1
    · have hb : (x % 2 == 1) = true := by simp [hodd]
      rw [hb]; simp; omega
    · have hb : (x % 2 == 1) = false := by simp [hodd]
      rw [hb]; simp; omega

theorem T_D_run_copy (n x : Nat) : (T_D.run true n x).2 = x % 2 ^ n := by
  have hsim : LsbTransducer.IsSim T_D T_id (fun q _ => q = true) := by
    intro q1 q2 b hR; subst hR; simp [T_D, T_id]
  rw [LsbTransducer.run_eq_of_sim hsim rfl n x, T_id_run]

theorem T_U_run_copy (n x : Nat) : (T_U.run .copy n x).2 = x % 2 ^ n := by
  have hsim : LsbTransducer.IsSim T_U T_id (fun q _ => q = .copy) := by
    intro q1 q2 b hR; subst hR; simp [T_U, T_id]
  rw [LsbTransducer.run_eq_of_sim hsim rfl n x, T_id_run]

theorem T_U_run_carry (n x : Nat) : (T_U.run .carry n x).2 = (x + 1) % 2 ^ n := by
  induction n generalizing x with
  | zero => simp [LsbTransducer.run, Nat.mod_one]
  | succ n ih =>
    rw [LsbTransducer.run]
    by_cases hodd : x % 2 = 1
    · have hb : (x % 2 == 1) = true := by simp [hodd]
      have hstep : T_U.step .carry (x % 2 == 1) = (.carry, false) := by rw [hb]; rfl
      rw [hstep]
      dsimp only
      rw [ih (x / 2)]
      have hx : x + 1 = 2 * (x / 2 + 1) := by omega
      rw [hx, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_mod_mul_left]
      simp
    · have hb : (x % 2 == 1) = false := by simp [hodd]
      have hstep : T_U.step .carry (x % 2 == 1) = (.copy, true) := by rw [hb]; rfl
      rw [hstep]
      dsimp only
      rw [T_U_run_copy]
      have hx : x + 1 = 2 * (x / 2) + 1 := by omega
      rw [hx, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
      have hlt : 2 * ((x / 2) % 2 ^ n) + 1 < 2 * 2 ^ n := by
        have := Nat.mod_lt (x / 2) (Nat.two_pow_pos n); omega
      have hq : 2 * (x / 2) + 1 =
          2 * 2 ^ n * ((x / 2) / 2 ^ n) + (2 * ((x / 2) % 2 ^ n) + 1) := by
        have := Nat.div_add_mod (x / 2) (2 ^ n)
        rw [Nat.mul_assoc]; omega
      conv => rhs; rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      simp [Nat.add_comm]

theorem T_D_evalMod (n x : Nat) : T_D.evalMod n x = fenwickD x % 2 ^ n := by
  unfold LsbTransducer.evalMod
  change (T_D.run false n x).2 = fenwickD x % 2 ^ n
  induction n generalizing x with
  | zero => simp [LsbTransducer.run, Nat.mod_one]
  | succ n ih =>
    rw [LsbTransducer.run]
    by_cases hodd : x % 2 = 1
    · have hb : (x % 2 == 1) = true := by simp [hodd]
      have hstep : T_D.step false (x % 2 == 1) = (true, false) := by rw [hb]; rfl
      rw [hstep]
      dsimp only
      rw [T_D_run_copy]
      have hx : x = 2 * (x / 2) + 1 := by omega
      conv => rhs; rw [hx, fenwickD_odd]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_mod_mul_left]
      simp
    · have hb : (x % 2 == 1) = false := by simp [hodd]
      have hstep : T_D.step false (x % 2 == 1) = (false, false) := by rw [hb]; rfl
      rw [hstep]
      dsimp only
      rw [ih (x / 2)]
      have hx : x = 2 * (x / 2) := by omega
      conv => rhs; rw [hx, fenwickD_even]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_mod_mul_left]
      simp

theorem T_U_evalMod (n x : Nat) : T_U.evalMod n x = fenwickU x % 2 ^ n := by
  unfold LsbTransducer.evalMod
  change (T_U.run .seek n x).2 = fenwickU x % 2 ^ n
  induction n generalizing x with
  | zero => simp [LsbTransducer.run, Nat.mod_one]
  | succ n ih =>
    rw [LsbTransducer.run]
    by_cases hodd : x % 2 = 1
    · have hb : (x % 2 == 1) = true := by simp [hodd]
      have hstep : T_U.step .seek (x % 2 == 1) = (.carry, false) := by rw [hb]; rfl
      rw [hstep]
      dsimp only
      rw [T_U_run_carry]
      have hx : x = 2 * (x / 2) + 1 := by omega
      conv => rhs; rw [hx, fenwickU_odd]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_mod_mul_left]
      simp
    · have hb : (x % 2 == 1) = false := by simp [hodd]
      have hstep : T_U.step .seek (x % 2 == 1) = (.seek, false) := by rw [hb]; rfl
      rw [hstep]
      dsimp only
      rw [ih (x / 2)]
      have hx : x = 2 * (x / 2) := by omega
      conv => rhs; rw [hx, fenwickU_even]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_mod_mul_left]
      simp

/-- 2-adic causality of `fenwickD` and `fenwickU` follows immediately from `run_mod_eq`. -/
theorem fenwickD_mod_pow (n x : Nat) :
    fenwickD (x % 2 ^ n) % 2 ^ n = fenwickD x % 2 ^ n := by
  rw [← T_D_evalMod, ← T_D_evalMod, LsbTransducer.evalMod, LsbTransducer.evalMod,
      LsbTransducer.run_mod_eq]

theorem fenwickU_mod_pow (n x : Nat) :
    fenwickU (x % 2 ^ n) % 2 ^ n = fenwickU x % 2 ^ n := by
  rw [← T_U_evalMod, ← T_U_evalMod, LsbTransducer.evalMod, LsbTransducer.evalMod,
      LsbTransducer.run_mod_eq]

-- ============================================================================
-- Parameterized Trigger-Chain Transducer Class & 4-Rule Compiler
-- ============================================================================

theorem getElem_append_left' (t s : List Bool) (i : Nat) (hi : i < t.length) :
    (t ++ s)[i]'(by simp; omega) = t[i] := by
  simp [List.getElem_append_left hi]

theorem getElem_append_right' (t s : List Bool) (i : Nat) (hge : t.length ≤ i)
    (hlt : i < (t ++ s).length) :
    (t ++ s)[i]'hlt = s[i - t.length]'(by simp at hlt; omega) := by
  simp [List.getElem_append_right hge]

theorem triggerChain_step_match (t : List Bool) (e : Bool)
    (q : Fin (t.length + 1)) (h : q.val < t.length) (b : Bool) (hb : b = t[q.val]) :
    (triggerChain t e).step q b = (⟨q.val + 1, Nat.succ_lt_succ h⟩, e && (q.val + 1 == t.length)) := by
  simp [triggerChain, h, hb]

theorem triggerChain_step_miss (t : List Bool) (e : Bool)
    (q : Fin (t.length + 1)) (h : q.val < t.length) (b : Bool) (hb : b ≠ t[q.val]) :
    (triggerChain t e).step q b = (q, false) := by
  simp [triggerChain, h, hb]

theorem triggerChain_step_copy (t : List Bool) (e : Bool)
    (q : Fin (t.length + 1)) (h : q.val = t.length) (b : Bool) :
    (triggerChain t e).step q b = (q, b) := by
  have hnot : ¬ (q.val < t.length) := by omega
  simp [triggerChain, hnot]

-- THE FOUR FUNDAMENTAL COMPOSITION-COLLAPSE LAWS (discharged via `evalMod_eq_of_sim`!)

/-- Rule 1: D ∘ C(t, false) = C(t ++ [true], false). -/
theorem collapse_D_false (t : List Bool) (n x : Nat) :
    (T_D.compose (triggerChain t false)).evalMod n x =
    (triggerChain (t ++ [true]) false).evalMod n x := by
  let R : (Bool × Fin (t.length + 1)) → Fin ((t ++ [true]).length + 1) → Prop :=
    fun (qd, qt) q2 =>
      (qd = false ∧ qt.val = q2.val) ∨
      (qd = true ∧ qt.val = t.length ∧ q2.val = t.length + 1)
  have hSim : LsbTransducer.IsSim (T_D.compose (triggerChain t false))
      (triggerChain (t ++ [true]) false) R := by
    intro ⟨qd, qt⟩ q2 b hR
    have hlen : (t ++ [true]).length = t.length + 1 := by simp
    rcases hR with ⟨hqd, hqeq⟩ | ⟨hqd, hqt, hq2⟩
    · subst hqd
      by_cases hlt : qt.val < t.length
      · have hlt2 : q2.val < (t ++ [true]).length := by omega
        have hget : (t ++ [true])[q2.val]'hlt2 = t[qt.val]'hlt := by
          have := getElem_append_left' t [true] q2.val (by omega)
          simpa [hqeq] using this
        by_cases hb : b = t[qt.val]
        · have hs1 := triggerChain_step_match t false qt hlt b hb
          have hs2 := triggerChain_step_match (t ++ [true]) false q2 hlt2 b (by rw [hget]; exact hb)
          simp only [LsbTransducer.compose, hs1, hs2, Bool.false_and, T_D]
          exact ⟨rfl, Or.inl ⟨rfl, by simp [hqeq]⟩⟩
        · have hs1 := triggerChain_step_miss t false qt hlt b hb
          have hs2 := triggerChain_step_miss (t ++ [true]) false q2 hlt2 b (by rw [hget]; exact hb)
          simp only [LsbTransducer.compose, hs1, hs2, T_D]
          exact ⟨rfl, Or.inl ⟨rfl, hqeq⟩⟩
      · have hqt_eq : qt.val = t.length := by omega
        have hlt2 : q2.val < (t ++ [true]).length := by omega
        have hget : (t ++ [true])[q2.val]'hlt2 = true := by
          have := getElem_append_right' t [true] q2.val (by omega) hlt2
          have hsub : q2.val - t.length = 0 := by omega
          simpa [hsub] using this
        have hs1 := triggerChain_step_copy t false qt hqt_eq b
        cases b
        · have hs2 := triggerChain_step_miss (t ++ [true]) false q2 hlt2 false (by rw [hget]; decide)
          simp only [LsbTransducer.compose, hs1, hs2, T_D]
          exact ⟨rfl, Or.inl ⟨rfl, hqeq⟩⟩
        · have hs2 := triggerChain_step_match (t ++ [true]) false q2 hlt2 true (by rw [hget])
          simp only [LsbTransducer.compose, hs1, hs2, Bool.false_and, T_D]
          exact ⟨rfl, Or.inr ⟨rfl, hqt_eq, by simp [← hqeq, hqt_eq]⟩⟩
    · subst hqd
      have hs1 := triggerChain_step_copy t false qt hqt b
      have hs2 := triggerChain_step_copy (t ++ [true]) false q2 (by omega) b
      simp only [LsbTransducer.compose, hs1, hs2, T_D]
      exact ⟨trivial, Or.inr ⟨rfl, hqt, hq2⟩⟩
  exact LsbTransducer.evalMod_eq_of_sim hSim (Or.inl ⟨rfl, rfl⟩) n x

/-- Rule 2: D ∘ C(t, true) = C(t, false) whenever t is non-empty. -/
theorem collapse_D_true (t : List Bool) (ht : 0 < t.length) (n x : Nat) :
    (T_D.compose (triggerChain t true)).evalMod n x =
    (triggerChain t false).evalMod n x := by
  let R : (Bool × Fin (t.length + 1)) → Fin (t.length + 1) → Prop :=
    fun (qd, qt) q2 =>
      (qd = false ∧ qt.val < t.length ∧ qt.val = q2.val) ∨
      (qd = true ∧ qt.val = t.length ∧ q2.val = t.length)
  have hSim : LsbTransducer.IsSim (T_D.compose (triggerChain t true))
      (triggerChain t false) R := by
    intro ⟨qd, qt⟩ q2 b hR
    rcases hR with ⟨hqd, hlt, hqeq⟩ | ⟨hqd, hqt, hq2⟩
    · subst hqd
      have hlt2 : q2.val < t.length := by omega
      have hget : t[q2.val]'hlt2 = t[qt.val]'hlt := by congr 1; omega
      by_cases hb : b = t[qt.val]
      · have hs1 := triggerChain_step_match t true qt hlt b hb
        have hs2 := triggerChain_step_match t false q2 hlt2 b (by rw [hget]; exact hb)
        by_cases hlast : qt.val + 1 = t.length
        · have heq : (qt.val + 1 == t.length) = true := by simp [hlast]
          simp only [LsbTransducer.compose, hs1, hs2, heq, Bool.true_and, Bool.false_and, T_D]
          exact ⟨rfl, Or.inr ⟨rfl, hlast, by dsimp only; omega⟩⟩
        · have hne : (qt.val + 1 == t.length) = false := by simp [hlast]
          simp only [LsbTransducer.compose, hs1, hs2, hne, Bool.true_and, Bool.false_and, T_D]
          exact ⟨rfl, Or.inl ⟨rfl, by dsimp only; omega, by simp [hqeq]⟩⟩
      · have hs1 := triggerChain_step_miss t true qt hlt b hb
        have hs2 := triggerChain_step_miss t false q2 hlt2 b (by rw [hget]; exact hb)
        simp only [LsbTransducer.compose, hs1, hs2, T_D]
        exact ⟨rfl, Or.inl ⟨rfl, hlt, hqeq⟩⟩
    · subst hqd
      have hs1 := triggerChain_step_copy t true qt hqt b
      have hs2 := triggerChain_step_copy t false q2 hq2 b
      simp only [LsbTransducer.compose, hs1, hs2, T_D]
      exact ⟨trivial, Or.inr ⟨rfl, hqt, hq2⟩⟩
  exact LsbTransducer.evalMod_eq_of_sim hSim (Or.inl ⟨rfl, ht, rfl⟩) n x

/-- Rule 3: U ∘ C(t, false) = C(t ++ [true, false], true). -/
theorem collapse_U_false (t : List Bool) (n x : Nat) :
    (T_U.compose (triggerChain t false)).evalMod n x =
    (triggerChain (t ++ [true, false]) true).evalMod n x := by
  let R : (UState × Fin (t.length + 1)) → Fin ((t ++ [true, false]).length + 1) → Prop :=
    fun (qu, qt) q2 =>
      (qu = .seek ∧ qt.val = q2.val) ∨
      (qu = .carry ∧ qt.val = t.length ∧ q2.val = t.length + 1) ∨
      (qu = .copy ∧ qt.val = t.length ∧ q2.val = t.length + 2)
  have hSim : LsbTransducer.IsSim (T_U.compose (triggerChain t false))
      (triggerChain (t ++ [true, false]) true) R := by
    intro ⟨qu, qt⟩ q2 b hR
    have hlen : (t ++ [true, false]).length = t.length + 2 := by simp
    rcases hR with ⟨hqu, hqeq⟩ | ⟨hqu, hqt, hq2⟩ | ⟨hqu, hqt, hq2⟩
    · subst hqu
      by_cases hlt : qt.val < t.length
      · have hlt2 : q2.val < (t ++ [true, false]).length := by omega
        have hget : (t ++ [true, false])[q2.val]'hlt2 = t[qt.val]'hlt := by
          have := getElem_append_left' t [true, false] q2.val (by omega)
          simpa [hqeq] using this
        have hnotlast : (q2.val + 1 == (t ++ [true, false]).length) = false := by
          simp; omega
        by_cases hb : b = t[qt.val]
        · have hs1 := triggerChain_step_match t false qt hlt b hb
          have hs2 := triggerChain_step_match (t ++ [true, false]) true q2 hlt2 b (by rw [hget]; exact hb)
          simp only [LsbTransducer.compose, hs1, hs2, hnotlast, Bool.false_and, Bool.true_and, T_U]
          exact ⟨rfl, Or.inl ⟨rfl, by simp [hqeq]⟩⟩
        · have hs1 := triggerChain_step_miss t false qt hlt b hb
          have hs2 := triggerChain_step_miss (t ++ [true, false]) true q2 hlt2 b (by rw [hget]; exact hb)
          simp only [LsbTransducer.compose, hs1, hs2, T_U]
          exact ⟨rfl, Or.inl ⟨rfl, hqeq⟩⟩
      · have hqt_eq : qt.val = t.length := by omega
        have hlt2 : q2.val < (t ++ [true, false]).length := by omega
        have hget : (t ++ [true, false])[q2.val]'hlt2 = true := by
          have := getElem_append_right' t [true, false] q2.val (by omega) hlt2
          have hsub : q2.val - t.length = 0 := by omega
          simpa [hsub] using this
        have hnotlast : (q2.val + 1 == (t ++ [true, false]).length) = false := by
          simp; omega
        have hs1 := triggerChain_step_copy t false qt hqt_eq b
        cases b
        · have hs2 := triggerChain_step_miss (t ++ [true, false]) true q2 hlt2 false (by rw [hget]; decide)
          simp only [LsbTransducer.compose, hs1, hs2, T_U]
          exact ⟨rfl, Or.inl ⟨rfl, hqeq⟩⟩
        · have hs2 := triggerChain_step_match (t ++ [true, false]) true q2 hlt2 true (by rw [hget])
          simp only [LsbTransducer.compose, hs1, hs2, hnotlast, Bool.true_and, T_U]
          exact ⟨rfl, Or.inr (Or.inl ⟨rfl, hqt_eq, by simp [← hqeq, hqt_eq]⟩)⟩
    · subst hqu
      have hlt2 : q2.val < (t ++ [true, false]).length := by omega
      have hget : (t ++ [true, false])[q2.val]'hlt2 = false := by
        have := getElem_append_right' t [true, false] q2.val (by omega) hlt2
        have hsub : q2.val - t.length = 1 := by omega
        simpa [hsub] using this
      have hislast : (q2.val + 1 == (t ++ [true, false]).length) = true := by
        simp; omega
      have hs1 := triggerChain_step_copy t false qt hqt b
      cases b
      · have hs2 := triggerChain_step_match (t ++ [true, false]) true q2 hlt2 false (by rw [hget])
        simp only [LsbTransducer.compose, hs1, hs2, hislast, Bool.true_and, T_U]
        exact ⟨rfl, Or.inr (Or.inr ⟨rfl, hqt, by simp [hq2]⟩)⟩
      · have hs2 := triggerChain_step_miss (t ++ [true, false]) true q2 hlt2 true (by rw [hget]; decide)
        simp only [LsbTransducer.compose, hs1, hs2, T_U]
        exact ⟨rfl, Or.inr (Or.inl ⟨rfl, hqt, hq2⟩)⟩
    · subst hqu
      have hs1 := triggerChain_step_copy t false qt hqt b
      have hs2 := triggerChain_step_copy (t ++ [true, false]) true q2 (by omega) b
      simp only [LsbTransducer.compose, hs1, hs2, T_U]
      exact ⟨trivial, Or.inr (Or.inr ⟨rfl, hqt, hq2⟩)⟩
  exact LsbTransducer.evalMod_eq_of_sim hSim (Or.inl ⟨rfl, rfl⟩) n x

/-- Rule 4: U ∘ C(t, true) = C(t ++ [false], true) whenever t is non-empty. -/
theorem collapse_U_true (t : List Bool) (ht : 0 < t.length) (n x : Nat) :
    (T_U.compose (triggerChain t true)).evalMod n x =
    (triggerChain (t ++ [false]) true).evalMod n x := by
  let R : (UState × Fin (t.length + 1)) → Fin ((t ++ [false]).length + 1) → Prop :=
    fun (qu, qt) q2 =>
      (qu = .seek ∧ qt.val < t.length ∧ qt.val = q2.val) ∨
      (qu = .carry ∧ qt.val = t.length ∧ q2.val = t.length) ∨
      (qu = .copy ∧ qt.val = t.length ∧ q2.val = t.length + 1)
  have hSim : LsbTransducer.IsSim (T_U.compose (triggerChain t true))
      (triggerChain (t ++ [false]) true) R := by
    intro ⟨qu, qt⟩ q2 b hR
    have hlen : (t ++ [false]).length = t.length + 1 := by simp
    rcases hR with ⟨hqu, hlt, hqeq⟩ | ⟨hqu, hqt, hq2⟩ | ⟨hqu, hqt, hq2⟩
    · subst hqu
      have hlt2 : q2.val < (t ++ [false]).length := by omega
      have hget : (t ++ [false])[q2.val]'hlt2 = t[qt.val]'hlt := by
        have := getElem_append_left' t [false] q2.val (by omega)
        simpa [hqeq] using this
      have hnotlast : (q2.val + 1 == (t ++ [false]).length) = false := by
        simp; omega
      by_cases hb : b = t[qt.val]
      · have hs1 := triggerChain_step_match t true qt hlt b hb
        have hs2 := triggerChain_step_match (t ++ [false]) true q2 hlt2 b (by rw [hget]; exact hb)
        by_cases hlast : qt.val + 1 = t.length
        · have heq : (qt.val + 1 == t.length) = true := by simp [hlast]
          simp only [LsbTransducer.compose, hs1, hs2, heq, hnotlast, Bool.true_and, T_U]
          exact ⟨rfl, Or.inr (Or.inl ⟨rfl, hlast, by simp [← hqeq, hlast]⟩)⟩
        · have hne : (qt.val + 1 == t.length) = false := by simp [hlast]
          simp only [LsbTransducer.compose, hs1, hs2, hne, hnotlast, Bool.true_and, T_U]
          exact ⟨rfl, Or.inl ⟨rfl, by dsimp only; omega, by simp [hqeq]⟩⟩
      · have hs1 := triggerChain_step_miss t true qt hlt b hb
        have hs2 := triggerChain_step_miss (t ++ [false]) true q2 hlt2 b (by rw [hget]; exact hb)
        simp only [LsbTransducer.compose, hs1, hs2, T_U]
        exact ⟨rfl, Or.inl ⟨rfl, hlt, hqeq⟩⟩
    · subst hqu
      have hlt2 : q2.val < (t ++ [false]).length := by omega
      have hget : (t ++ [false])[q2.val]'hlt2 = false := by
        have := getElem_append_right' t [false] q2.val (by omega) hlt2
        have hsub : q2.val - t.length = 0 := by omega
        simpa [hsub] using this
      have hislast : (q2.val + 1 == (t ++ [false]).length) = true := by
        simp; omega
      have hs1 := triggerChain_step_copy t true qt hqt b
      cases b
      · have hs2 := triggerChain_step_match (t ++ [false]) true q2 hlt2 false (by rw [hget])
        simp only [LsbTransducer.compose, hs1, hs2, hislast, Bool.true_and, T_U]
        exact ⟨rfl, Or.inr (Or.inr ⟨rfl, hqt, by simp [hq2]⟩)⟩
      · have hs2 := triggerChain_step_miss (t ++ [false]) true q2 hlt2 true (by rw [hget]; decide)
        simp only [LsbTransducer.compose, hs1, hs2, T_U]
        exact ⟨rfl, Or.inr (Or.inl ⟨rfl, hqt, hq2⟩)⟩
    · subst hqu
      have hs1 := triggerChain_step_copy t true qt hqt b
      have hs2 := triggerChain_step_copy (t ++ [false]) true q2 (by omega) b
      simp only [LsbTransducer.compose, hs1, hs2, T_U]
      exact ⟨trivial, Or.inr (Or.inr ⟨rfl, hqt, hq2⟩)⟩
  exact LsbTransducer.evalMod_eq_of_sim hSim (Or.inl ⟨rfl, ht, rfl⟩) n x

-- Structural invariants of `compileSpec`

theorem compileSpec_emit (w : List FenwickOp) :
    (compileSpec w).2 = match w with | .U :: _ => true | _ => false := by
  cases w with
  | nil => rfl
  | cons g v => cases g <;> simp [compileSpec] <;> split <;> rfl

theorem compileSpec_len (w : List FenwickOp) :
    (compileSpec w).1.length = match w with
      | [] => 0
      | .D :: _ => w.length
      | .U :: _ => w.length + 1 := by
  induction w with
  | nil => rfl
  | cons g v ih =>
    cases g with
    | D =>
      simp only [compileSpec, List.length_cons]
      have he := compileSpec_emit v
      cases v with
      | nil => simp [compileSpec]
      | cons g2 v2 =>
        cases g2 <;> simp_all
    | U =>
      simp only [compileSpec, List.length_cons]
      have he := compileSpec_emit v
      cases v with
      | nil => simp [compileSpec]
      | cons g2 v2 =>
        cases g2 <;> simp_all <;> omega

theorem compileSpec_valid_last (w : List FenwickOp) :
    (compileSpec w).2 = true → (compileSpec w).1.getLast? = some false := by
  cases w with
  | nil => simp [compileSpec]
  | cons g v =>
    cases g with
    | D =>
      simp only [compileSpec]
      split <;> simp
    | U =>
      simp only [compileSpec]
      split <;> simp

theorem compileSpec_head (w : List FenwickOp) (hw : w ≠ []) :
    (compileSpec w).1.head? = some true := by
  induction w with
  | nil => contradiction
  | cons g v ih =>
    cases v with
    | nil =>
      cases g <;> rfl
    | cons g2 v2 =>
      have hv : g2 :: v2 ≠ [] := List.cons_ne_nil _ _
      have hih := ih hv
      cases hspec : compileSpec (g2 :: v2) with
      | mk t e =>
        rw [hspec] at hih
        cases t with
        | nil => simp at hih
        | cons b bs =>
          simp only [List.head?_cons, Option.some.injEq] at hih
          subst hih
          cases g <;> cases e <;> simp [compileSpec, hspec]

theorem compileSpec_pos_of_emit (w : List FenwickOp) (he : (compileSpec w).2 = true) :
    0 < (compileSpec w).1.length := by
  have hlen := compileSpec_len w
  cases w with
  | nil => simp [compileSpec] at he
  | cons g v =>
    cases g with
    | D => simp [compileSpec_emit] at he
    | U =>
      simp only at hlen
      omega

-- ============================================================================
-- THEOREM 1: Trigger-Chain Compilation & Exact Linear State-Complexity Collapse
-- ============================================================================

/-- Theorem 1a: For EVERY word w ∈ {U, D}*, EVERY bit-width n, and EVERY x : Nat,
    evalWord w x mod 2^n equals the compiled linear TriggerChain transducer. -/
theorem evalWord_mod_eq_compile (w : List FenwickOp) (n x : Nat) :
    evalWord w x % 2 ^ n = (compileTC w).evalMod n x := by
  induction w with
  | nil =>
    simp only [evalWord, compileTC, compileSpec]
    have hsim : LsbTransducer.IsSim (triggerChain [] false) T_id (fun _ _ => True) := by
      intro q1 q2 b _; simp [triggerChain, T_id]
    rw [LsbTransducer.evalMod_eq_of_sim hsim trivial n x]
    exact (T_id_run n x).symm
  | cons g v ih =>
    cases g with
    | D =>
      simp only [evalWord]
      rw [← fenwickD_mod_pow, ih, ← T_D_evalMod, ← LsbTransducer.evalMod_compose]
      unfold compileTC
      simp only [compileSpec]
      cases he : (compileSpec v).2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact collapse_D_false (compileSpec v).1 n x
      · simp only [↓reduceIte]
        have hpos := compileSpec_pos_of_emit v he
        exact collapse_D_true (compileSpec v).1 hpos n x
    | U =>
      simp only [evalWord]
      rw [← fenwickU_mod_pow, ih, ← T_U_evalMod, ← LsbTransducer.evalMod_compose]
      unfold compileTC
      simp only [compileSpec]
      cases he : (compileSpec v).2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact collapse_U_false (compileSpec v).1 n x
      · simp only [↓reduceIte]
        have hpos := compileSpec_pos_of_emit v he
        exact collapse_U_true (compileSpec v).1 hpos n x

/-- Upper bound: each Fenwick step at most doubles x. -/
theorem evalWord_lt_pow (w : List FenwickOp) (k x : Nat) (hx : x < 2 ^ k) :
    evalWord w x < 2 ^ (k + w.length) := by
  induction w with
  | nil => simpa [evalWord] using hx
  | cons g v ih =>
    simp only [List.length_cons, ← Nat.add_assoc, Nat.pow_succ]
    cases g with
    | D =>
      change fenwickD (evalWord v x) < 2 ^ (k + v.length) * 2
      have := fenwickD_le (evalWord v x)
      omega
    | U =>
      change fenwickU (evalWord v x) < 2 ^ (k + v.length) * 2
      have := fenwickU_le_double (evalWord v x)
      omega

/-- Theorem 1b (Unbounded Nat exact compilation): For every w, x and any bit-width n
    with evalWord w x < 2^n, evalWord w x is computed exactly by `compileTC w`. -/
theorem evalWord_eq_compile (w : List FenwickOp) (x n : Nat) (h : evalWord w x < 2 ^ n) :
    evalWord w x = (compileTC w).evalMod n x := by
  rw [← Nat.mod_eq_of_lt h, evalWord_mod_eq_compile]

/-- Theorem 1c: Exact linear state count of `compileTC w` (collapsing 3^|w| to |w|+1 or |w|+2). -/
theorem compileTC_numStates (w : List FenwickOp) :
    ((compileSpec w).1.length + 1) = match w with
      | [] => 1
      | .D :: _ => w.length + 1
      | .U :: _ => w.length + 2 := by
  rw [compileSpec_len]
  cases w with
  | nil => rfl
  | cons g v => cases g <;> rfl

theorem fromBits_lt_pow (bs : List Bool) : fromBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [fromBits]
  | cons b bs ih =>
    simp only [fromBits, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem fromBits_append (a b : List Bool) :
    fromBits (a ++ b) = fromBits a + 2 ^ a.length * fromBits b := by
  induction a with
  | nil => simp [fromBits]
  | cons x xs ih =>
    simp only [List.cons_append, fromBits, List.length_cons, ih, Nat.pow_succ]
    have hmul : 2 ^ xs.length * 2 * fromBits b = 2 * (2 ^ xs.length * fromBits b) := by
      rw [Nat.mul_comm (2 ^ xs.length) 2, Nat.mul_assoc]
    omega

theorem compileSpec_valid (w : List FenwickOp) :
    ValidSpec (compileSpec w).1 (compileSpec w).2 :=
  compileSpec_valid_last w

/-- Monotonicity bound: `triggerChain` advances state by at most 1 per bit. -/
theorem triggerChain_step_val_le (t : List Bool) (e : Bool) (q : Fin (t.length + 1)) (b : Bool) :
    ((triggerChain t e).step q b).1.val ≤ q.val + 1 := by
  by_cases hlt : q.val < t.length
  · by_cases hb : b = t[q.val]
    · rw [triggerChain_step_match t e q hlt b hb]; simp
    · rw [triggerChain_step_miss t e q hlt b hb]; dsimp only; omega
  · have hEq : q.val = t.length := by omega
    rw [triggerChain_step_copy t e q hEq b]; dsimp only; omega

theorem triggerChain_run_val_le (t : List Bool) (e : Bool) (q : Fin (t.length + 1)) (k x : Nat) :
    ((triggerChain t e).run q k x).1.val ≤ q.val + k := by
  induction k generalizing q x with
  | zero => simp [LsbTransducer.run]
  | succ k ih =>
    rw [LsbTransducer.run]
    cases hstep : (triggerChain t e).step q (x % 2 == 1) with
    | mk q' bOut =>
      dsimp only
      have h1 : q'.val ≤ q.val + 1 := by
        have := triggerChain_step_val_le t e q (x % 2 == 1)
        rw [hstep] at this; exact this
      have h2 := ih q' (x / 2)
      omega

/-- Exact lockstep matching: feeding `t.drop i` from state `i` advances to state `t.length`. -/
theorem triggerChain_run_drop (t : List Bool) (e : Bool) (i : Nat) (hi : i ≤ t.length) :
    ((triggerChain t e).run ⟨i, Nat.lt_succ_of_le hi⟩ (t.length - i) (fromBits (t.drop i))).1.val
      = t.length := by
  generalize hk : t.length - i = k
  induction k generalizing i with
  | zero =>
    have heq : i = t.length := by omega
    simp [LsbTransducer.run, heq]
  | succ k ih =>
    have hlt : i < t.length := by omega
    have hdrop : t.drop i = t[i] :: t.drop (i + 1) := List.drop_eq_getElem_cons hlt
    rw [hdrop, fromBits, LsbTransducer.run]
    have hmod : (((if t[i] then 1 else 0) + 2 * fromBits (t.drop (i + 1))) % 2 == 1) = t[i] := by
      cases t[i] <;> simp
    have hdiv : ((if t[i] then 1 else 0) + 2 * fromBits (t.drop (i + 1))) / 2 =
        fromBits (t.drop (i + 1)) := by
      cases t[i] <;> simp <;> omega
    rw [hmod, hdiv]
    have hstep := triggerChain_step_match t e ⟨i, Nat.lt_succ_of_le hi⟩ hlt t[i] rfl
    rw [hstep]
    dsimp only
    exact ih (i + 1) (by omega) (by omega)

/-- Exact lockstep prefix reachability: feeding `t.take i` from state `0` reaches state `i`. -/
theorem triggerChain_run_take (t : List Bool) (e : Bool) (i : Nat) (hi : i ≤ t.length) :
    ((triggerChain t e).run ⟨0, Nat.zero_lt_succ _⟩ i (fromBits (t.take i))).1.val = i := by
  -- More general lemma: starting at state `a` with `a + k ≤ t.length`, feeding `t.drop a |>.take k` reaches `a + k`
  suffices ∀ a k (hak : a + k ≤ t.length),
      ((triggerChain t e).run ⟨a, by omega⟩ k (fromBits ((t.drop a).take k))).1.val = a + k by
    simpa using this 0 i (by omega)
  intro a k
  induction k generalizing a with
  | zero => intro _; simp [LsbTransducer.run]
  | succ k ih =>
    intro hak
    have hlt : a < t.length := by omega
    have hdrop : (t.drop a).take (k + 1) = t[a] :: (t.drop (a + 1)).take k := by
      rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
    rw [hdrop, fromBits, LsbTransducer.run]
    have hmod : (((if t[a] then 1 else 0) + 2 * fromBits ((t.drop (a + 1)).take k)) % 2 == 1) = t[a] := by
      cases t[a] <;> simp
    have hdiv : ((if t[a] then 1 else 0) + 2 * fromBits ((t.drop (a + 1)).take k)) / 2 =
        fromBits ((t.drop (a + 1)).take k) := by
      cases t[a] <;> simp <;> omega
    rw [hmod, hdiv]
    have hstep := triggerChain_step_match t e ⟨a, by omega⟩ hlt t[a] rfl
    rw [hstep]
    dsimp only
    have := ih (a + 1) (by omega)
    omega

/-- Exact lockstep output on `fromBits t` for `t.length` steps. -/
theorem triggerChain_run_exact_out (t : List Bool) (e : Bool) (i : Nat) (hi : i ≤ t.length) :
    ((triggerChain t e).run ⟨i, Nat.lt_succ_of_le hi⟩ (t.length - i) (fromBits (t.drop i))).2 =
      if e = true ∧ i < t.length then 2 ^ (t.length - i - 1) else 0 := by
  generalize hk : t.length - i = k
  induction k generalizing i with
  | zero =>
    have : ¬ (i < t.length) := by omega
    simp [LsbTransducer.run, this]
  | succ k ih =>
    have hlt : i < t.length := by omega
    have hdrop : t.drop i = t[i] :: t.drop (i + 1) := List.drop_eq_getElem_cons hlt
    rw [hdrop, fromBits, LsbTransducer.run]
    have hmod : (((if t[i] then 1 else 0) + 2 * fromBits (t.drop (i + 1))) % 2 == 1) = t[i] := by
      cases t[i] <;> simp
    have hdiv : ((if t[i] then 1 else 0) + 2 * fromBits (t.drop (i + 1))) / 2 =
        fromBits (t.drop (i + 1)) := by
      cases t[i] <;> simp <;> omega
    rw [hmod, hdiv]
    have hstep := triggerChain_step_match t e ⟨i, Nat.lt_succ_of_le hi⟩ hlt t[i] rfl
    rw [hstep]
    dsimp only
    rw [ih (i + 1) (by omega) (by omega)]
    by_cases hk0 : k = 0
    · subst hk0
      have hlast : i + 1 = t.length := by omega
      have hbeq : (i + 1 == t.length) = true := by simp [hlast]
      have hnotlt : ¬ (i + 1 < t.length) := by omega
      cases e <;> simp [hbeq, hlt, hnotlt]
    · have hnotlast : i + 1 < t.length := by omega
      have hbeq : (i + 1 == t.length) = false := by simp; omega
      cases e
      · simp [hbeq]
      · simp only [hbeq, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hnotlast, hlt, and_self]
        have hsub : k = (k - 1) + 1 := by omega
        have hsub2 : k + 1 - 1 = (k - 1) + 1 := by omega
        rw [hsub2, Nat.pow_succ, Nat.mul_comm]
        omega

/-- A valid triggerChain never emits `true` on input `true` from any non-COPY state! -/
theorem triggerChain_valid_step_true_out {t : List Bool} {e : Bool} (hval : ValidSpec t e)
    (q : Fin (t.length + 1)) (hlt : q.val < t.length) :
    ((triggerChain t e).step q true).2 = false := by
  by_cases hb : true = t[q.val]
  · rw [triggerChain_step_match t e q hlt true hb]
    dsimp only
    cases he : e
    · rfl
    · simp only [Bool.true_and]
      have hlast := hval he
      by_cases hq : q.val + 1 = t.length
      · have hget : t.getLast? = some t[q.val] := by
          rw [List.getLast?_eq_getElem?]
          have hidx : t.length - 1 = q.val := by omega
          rw [hidx, List.getElem?_eq_getElem hlt]
        rw [hget] at hlast
        have : t[q.val] = false := Option.some.inj hlast
        rw [this] at hb
        cases hb
      · simp [hq]
  · rw [triggerChain_step_miss t e q hlt true hb]

/-- Output is strictly zero while `q.val + k < t.length` (or `q.val + k ≤ t.length` when `e = false`). -/
theorem triggerChain_run_zero_of_lt (t : List Bool) (e : Bool) (q : Fin (t.length + 1))
    (k x : Nat) (h : q.val + k < t.length ∨ (e = false ∧ q.val + k ≤ t.length)) :
    ((triggerChain t e).run q k x).2 = 0 := by
  induction k generalizing q x with
  | zero => simp [LsbTransducer.run]
  | succ k ih =>
    rw [LsbTransducer.run]
    have hqlt : q.val < t.length := by omega
    by_cases hb : (x % 2 == 1) = t[q.val]
    · rw [triggerChain_step_match t e q hqlt (x % 2 == 1) hb]
      dsimp only
      have hout : (e && (q.val + 1 == t.length)) = false := by
        rcases h with h1 | ⟨he, _⟩
        · have : (q.val + 1 == t.length) = false := by simp; omega
          simp [this]
        · subst he; rfl
      rw [hout]
      have harg : (⟨q.val + 1, Nat.succ_lt_succ hqlt⟩ : Fin (t.length + 1)).val + k < t.length ∨
          (e = false ∧ (⟨q.val + 1, Nat.succ_lt_succ hqlt⟩ : Fin (t.length + 1)).val + k ≤ t.length) := by
        dsimp only
        rcases h with h1 | ⟨he, h2⟩
        · left; omega
        · right; exact ⟨he, by omega⟩
      have hih := ih ⟨q.val + 1, Nat.succ_lt_succ hqlt⟩ (x / 2) harg
      rw [hih]; rfl
    · rw [triggerChain_step_miss t e q hqlt (x % 2 == 1) hb]
      dsimp only
      have harg : q.val + k < t.length ∨ (e = false ∧ q.val + k ≤ t.length) := by
        rcases h with h1 | ⟨he, h2⟩
        · left; omega
        · right; exact ⟨he, by omega⟩
      have hih := ih q (x / 2) harg
      rw [hih]; rfl

/-- On valid `(t, e)`, running from state `i < j` on `t.drop j ++ [true]` gives output `< 2^(t.length - j)`,
    while running from state `j` gives output `≥ 2^(t.length - j)`. -/
theorem triggerChain_distinguish_states {t : List Bool} {e : Bool} (hval : ValidSpec t e)
    (i j : Fin (t.length + 1)) (hij : i.val < j.val) :
    ((triggerChain t e).run i (t.length - j.val + 1) (fromBits (t.drop j.val ++ [true]))).2 ≠
    ((triggerChain t e).run j (t.length - j.val + 1) (fromBits (t.drop j.val ++ [true]))).2 := by
  let k := t.length - j.val
  change ((triggerChain t e).run i (k + 1) (fromBits (t.drop j.val ++ [true]))).2 ≠
         ((triggerChain t e).run j (k + 1) (fromBits (t.drop j.val ++ [true]))).2
  have hlen : (t.drop j.val).length = k := by simp [k]
  have hlt_drop : fromBits (t.drop j.val) < 2 ^ k := by
    have := fromBits_lt_pow (t.drop j.val); rwa [hlen] at this
  have hpack : fromBits (t.drop j.val ++ [true]) = fromBits (t.drop j.val) + 2 ^ k * 1 := by
    rw [fromBits_append, hlen]; rfl
  rw [hpack]
  have hsplit_i := LsbTransducer.run_add_pow (triggerChain t e) i k 1 (fromBits (t.drop j.val)) 1 hlt_drop
  have hsplit_j := LsbTransducer.run_add_pow (triggerChain t e) j k 1 (fromBits (t.drop j.val)) 1 hlt_drop
  have hqj : ((triggerChain t e).run j k (fromBits (t.drop j.val))).1.val = t.length :=
    triggerChain_run_drop t e j.val (Nat.le_of_lt_succ j.isLt)
  have hstep_j : ((triggerChain t e).run ((triggerChain t e).run j k (fromBits (t.drop j.val))).1 1 1).2 = 1 := by
    rw [LsbTransducer.run]
    have h1 : (1 % 2 == 1) = true := rfl
    rw [h1, triggerChain_step_copy t e _ hqj true]
    simp [LsbTransducer.run]
  have hout_j_ge : 2 ^ k ≤ ((triggerChain t e).run j (k + 1) (fromBits (t.drop j.val) + 2 ^ k * 1)).2 := by
    rw [hsplit_j]; dsimp only; rw [hstep_j]; omega
  have hqi_lt : ((triggerChain t e).run i k (fromBits (t.drop j.val))).1.val < t.length := by
    have := triggerChain_run_val_le t e i k (fromBits (t.drop j.val))
    omega
  have hstep_i : ((triggerChain t e).run ((triggerChain t e).run i k (fromBits (t.drop j.val))).1 1 1).2 = 0 := by
    rw [LsbTransducer.run]
    have h1 : (1 % 2 == 1) = true := rfl
    rw [h1]
    have h0 := triggerChain_valid_step_true_out hval _ hqi_lt
    cases hst : (triggerChain t e).step ((triggerChain t e).run i k (fromBits (t.drop j.val))).1 true with
    | mk qf bo =>
      rw [hst] at h0; dsimp only at h0; subst h0
      simp [LsbTransducer.run]
  have hout_i_lt : ((triggerChain t e).run i (k + 1) (fromBits (t.drop j.val) + 2 ^ k * 1)).2 < 2 ^ k := by
    rw [hsplit_i]; dsimp only; rw [hstep_i]
    have := LsbTransducer.run_lt_pow (triggerChain t e) i k (fromBits (t.drop j.val))
    omega
  omega

/-- Elementary pigeonhole lemma on `Fin` (no Mathlib needed!). -/
theorem fin_le_of_inj {a b : Nat} (f : Fin a → Fin b) (hf : ∀ x y, f x = f y → x = y) :
    a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le b
  | succ a ih =>
    cases b with
    | zero => exact Fin.elim0 (f ⟨0, Nat.zero_lt_succ a⟩)
    | succ b =>
      let lastA : Fin (a + 1) := ⟨a, Nat.lt_succ_self a⟩
      let y0 : Fin (b + 1) := f lastA
      let g : Fin a → Fin b := fun i =>
        let fi := f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        if hlt : fi.val < y0.val then
          ⟨fi.val, by omega⟩
        else
          ⟨fi.val - 1, by
            have hne : fi ≠ y0 := fun heq => by
              have := hf ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ lastA heq
              have hv : i.val = a := congrArg Fin.val this
              omega
            have hvalne : fi.val ≠ y0.val := fun h => hne (Fin.ext h)
            omega⟩
      have hg : ∀ x y : Fin a, g x = g y → x = y := by
        intro x y hxy
        have hv : (g x).val = (g y).val := congrArg Fin.val hxy
        dsimp only [g] at hv
        have hnx : (f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩).val ≠ y0.val := fun h => by
          have := hf ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ lastA (Fin.ext h)
          have : x.val = a := congrArg Fin.val this; omega
        have hny : (f ⟨y.val, Nat.lt_succ_of_lt y.isLt⟩).val ≠ y0.val := fun h => by
          have := hf ⟨y.val, Nat.lt_succ_of_lt y.isLt⟩ lastA (Fin.ext h)
          have : y.val = a := congrArg Fin.val this; omega
        split at hv <;> split at hv
        · have heq : f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ = f ⟨y.val, Nat.lt_succ_of_lt y.isLt⟩ :=
            Fin.ext hv
          have hfin := hf _ _ heq
          have hval : x.val = y.val := by
            have := congrArg Fin.val hfin
            exact this
          exact Fin.ext hval
        · dsimp only at hv; omega
        · dsimp only at hv; omega
        · dsimp only at hv
          have heq : f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ = f ⟨y.val, Nat.lt_succ_of_lt y.isLt⟩ :=
            Fin.ext (by omega)
          have hfin := hf _ _ heq
          have hval : x.val = y.val := by
            have := congrArg Fin.val hfin
            exact this
          exact Fin.ext hval
      exact Nat.succ_le_succ (ih g hg)

/-- THEOREM 1d (Myhill-Nerode Exact Minimality Lower Bound):
    NO deterministic LSB transducer with fewer than `|compileSpec w|.1 + 1` states
    can compute `evalWord w` modulo 2^n for all n, x! -/
theorem compileTC_minimal (w : List FenwickOp) {m : Nat} (T' : LsbTransducer (Fin m))
    (hEq : ∀ n x : Nat, T'.evalMod n x = evalWord w x % 2 ^ n) :
    (compileSpec w).1.length + 1 ≤ m := by
  let t := (compileSpec w).1
  let e := (compileSpec w).2
  change t.length + 1 ≤ m
  have hT_eq : ∀ n x : Nat, T'.evalMod n x = (triggerChain t e).evalMod n x := by
    intro n x; rw [hEq n x, evalWord_mod_eq_compile]; rfl
  let f : Fin (t.length + 1) → Fin m := fun i =>
    (T'.run T'.init i.val (fromBits (t.take i.val))).1
  apply fin_le_of_inj f
  intro i j hij
  suffices ∀ a b : Fin (t.length + 1), a.val < b.val → f a ≠ f b by
    by_cases hlt : i.val < j.val
    · exact absurd hij (this i j hlt)
    · by_cases hgt : j.val < i.val
      · exact absurd hij.symm (this j i hgt)
      · exact Fin.ext (by omega)
  intro a b hab hfab
  let suf := fromBits (t.drop b.val ++ [true])
  let k := t.length - b.val + 1
  have ha_lt : fromBits (t.take a.val) < 2 ^ a.val := by
    have := fromBits_lt_pow (t.take a.val)
    have hl : (t.take a.val).length = a.val := by simp; omega
    rwa [hl] at this
  have hb_lt : fromBits (t.take b.val) < 2 ^ b.val := by
    have := fromBits_lt_pow (t.take b.val)
    have hl : (t.take b.val).length = b.val := by simp; omega
    rwa [hl] at this
  have h1 := hT_eq (a.val + k) (fromBits (t.take a.val) + 2 ^ a.val * suf)
  have h2 := hT_eq (b.val + k) (fromBits (t.take b.val) + 2 ^ b.val * suf)
  unfold LsbTransducer.evalMod at h1 h2
  rw [LsbTransducer.run_add_pow T' T'.init a.val k _ suf ha_lt,
      LsbTransducer.run_add_pow (triggerChain t e) (triggerChain t e).init a.val k _ suf ha_lt] at h1
  rw [LsbTransducer.run_add_pow T' T'.init b.val k _ suf hb_lt,
      LsbTransducer.run_add_pow (triggerChain t e) (triggerChain t e).init b.val k _ suf hb_lt] at h2
  dsimp only at h1 h2
  have hdiv_eq : ∀ p1 p2 s1 s2 r : Nat, p1 < 2 ^ r → p2 < 2 ^ r →
      p1 + 2 ^ r * s1 = p2 + 2 ^ r * s2 → s1 = s2 := by
    intro p1 p2 s1 s2 r hp1 hp2 heq
    have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
    have h1d : (p1 + 2 ^ r * s1) / 2 ^ r = s1 := by
      rw [Nat.add_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hp1, Nat.add_zero]
    have h2d : (p2 + 2 ^ r * s2) / 2 ^ r = s2 := by
      rw [Nat.add_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hp2, Nat.add_zero]
    rw [← h1d, heq, h2d]
  have hsuf_a := hdiv_eq _ _ _ _ a.val
    (LsbTransducer.run_lt_pow T' _ _ _) (LsbTransducer.run_lt_pow (triggerChain t e) _ _ _) h1
  have hsuf_b := hdiv_eq _ _ _ _ b.val
    (LsbTransducer.run_lt_pow T' _ _ _) (LsbTransducer.run_lt_pow (triggerChain t e) _ _ _) h2
  have hqa : ((triggerChain t e).run (triggerChain t e).init a.val (fromBits (t.take a.val))).1 = a :=
    Fin.ext (triggerChain_run_take t e a.val (Nat.le_of_lt_succ a.isLt))
  have hqb : ((triggerChain t e).run (triggerChain t e).init b.val (fromBits (t.take b.val))).1 = b :=
    Fin.ext (triggerChain_run_take t e b.val (Nat.le_of_lt_succ b.isLt))
  rw [hqa] at hsuf_a
  rw [hqb] at hsuf_b
  have hsame : (T'.run (f a) k suf).2 = (T'.run (f b) k suf).2 := by rw [hfab]
  have hcontra : ((triggerChain t e).run a k suf).2 = ((triggerChain t e).run b k suf).2 := by
    rw [← hsuf_a, ← hsuf_b]; exact hsame
  exact triggerChain_distinguish_states (compileSpec_valid w) a b hab hcontra

-- ============================================================================
-- THEOREM 2: The Fenwick Free Monoid Theorem (<U, D> ≅ {U, D}* on Nat)
-- ============================================================================

/-- Helper: list append injectivity on suffixes. -/
theorem list_append_cancel_right {α : Type} {l1 l2 s : List α}
    (h : l1 ++ s = l2 ++ s) : l1 = l2 := List.append_cancel_right h

/-- Helper: two non-empty lists differing at the last element are unequal. -/
theorem last_ne_append_singleton (a b : List Bool) (x y : Bool) (hxy : x ≠ y) :
    a ++ [x] ≠ b ++ [y] := by
  intro heq
  have h1 := congrArg List.getLast? heq
  simp at h1
  exact hxy h1

/-- Structural injectivity of the 4-rule compiler `compileSpec`. -/
theorem compileSpec_injective {w1 w2 : List FenwickOp}
    (h : compileSpec w1 = compileSpec w2) : w1 = w2 := by
  induction w1 generalizing w2 with
  | nil =>
    cases w2 with
    | nil => rfl
    | cons g v =>
      have hlen := congrArg (fun p => p.1.length) h
      rw [compileSpec_len [], compileSpec_len (g :: v)] at hlen
      cases g <;> simp at hlen
  | cons g1 v1 ih =>
    cases w2 with
    | nil =>
      have hlen := congrArg (fun p => p.1.length) h
      rw [compileSpec_len (g1 :: v1), compileSpec_len []] at hlen
      cases g1 <;> simp at hlen
    | cons g2 v2 =>
      -- Outermost op is uniquely determined by the `emit` bit!
      have hemit := congrArg Prod.snd h
      rw [compileSpec_emit (g1 :: v1), compileSpec_emit (g2 :: v2)] at hemit
      cases g1 <;> cases g2
      · -- Both D :: _
        have h1 : compileSpec (.D :: v1) =
            (if (compileSpec v1).2 then (compileSpec v1).1 else (compileSpec v1).1 ++ [true], false) := by
          simp only [compileSpec]; split <;> rfl
        have h2 : compileSpec (.D :: v2) =
            (if (compileSpec v2).2 then (compileSpec v2).1 else (compileSpec v2).1 ++ [true], false) := by
          simp only [compileSpec]; split <;> rfl
        have ht := congrArg Prod.fst (h1.symm.trans (h.trans h2))
        cases hv1 : (compileSpec v1).2 <;> cases hv2 : (compileSpec v2).2
        · simp only [hv1, hv2, Bool.false_eq_true, ↓reduceIte] at ht
          have ht' := list_append_cancel_right ht
          have hspec : compileSpec v1 = compileSpec v2 := Prod.ext ht' (by rw [hv1, hv2])
          rw [ih hspec]
        · simp only [hv1, hv2, Bool.false_eq_true, ↓reduceIte] at ht
          have hlast := compileSpec_valid_last v2 hv2
          rw [← ht] at hlast; simp at hlast
        · simp only [hv1, hv2, Bool.false_eq_true, ↓reduceIte] at ht
          have hlast := compileSpec_valid_last v1 hv1
          rw [ht] at hlast; simp at hlast
        · simp only [hv1, hv2, ↓reduceIte] at ht
          have hspec : compileSpec v1 = compileSpec v2 := Prod.ext ht (by rw [hv1, hv2])
          rw [ih hspec]
      · simp at hemit
      · simp at hemit
      · -- Both U :: _
        have h1 : compileSpec (.U :: v1) =
            (if (compileSpec v1).2 then (compileSpec v1).1 ++ [false] else (compileSpec v1).1 ++ [true, false], true) := by
          simp only [compileSpec]; split <;> rfl
        have h2 : compileSpec (.U :: v2) =
            (if (compileSpec v2).2 then (compileSpec v2).1 ++ [false] else (compileSpec v2).1 ++ [true, false], true) := by
          simp only [compileSpec]; split <;> rfl
        have ht := congrArg Prod.fst (h1.symm.trans (h.trans h2))
        cases hv1 : (compileSpec v1).2 <;> cases hv2 : (compileSpec v2).2
        · simp only [hv1, hv2, Bool.false_eq_true, ↓reduceIte] at ht
          have ht' := list_append_cancel_right ht
          have hspec : compileSpec v1 = compileSpec v2 := Prod.ext ht' (by rw [hv1, hv2])
          rw [ih hspec]
        · simp only [hv1, hv2, Bool.false_eq_true, ↓reduceIte] at ht
          have hcat : (compileSpec v1).1 ++ [true, false] = ((compileSpec v1).1 ++ [true]) ++ [false] := by simp
          rw [hcat] at ht
          have ht' := list_append_cancel_right ht
          have hlast := compileSpec_valid_last v2 hv2
          rw [← ht'] at hlast; simp at hlast
        · simp only [hv1, hv2, Bool.false_eq_true, ↓reduceIte] at ht
          have hcat : (compileSpec v2).1 ++ [true, false] = ((compileSpec v2).1 ++ [true]) ++ [false] := by simp
          rw [hcat] at ht
          have ht' := list_append_cancel_right ht
          have hlast := compileSpec_valid_last v1 hv1
          rw [ht'] at hlast; simp at hlast
        · simp only [hv1, hv2, ↓reduceIte] at ht
          have ht' := list_append_cancel_right ht
          have hspec : compileSpec v1 = compileSpec v2 := Prod.ext ht' (by rw [hv1, hv2])
          rw [ih hspec]

/-- Key stalling lemma: if `t1 ≠ t2` and `t1.length ≤ t2.length`, then running `triggerChain t2 e2`
    on `fromBits t1` for `t1.length` steps ends strictly before COPY (`qFinal < t2.length`). -/
theorem triggerChain_stall_of_ne {t1 t2 : List Bool} (e2 : Bool)
    (hlen : t1.length ≤ t2.length) (hne : t1 ≠ t2) :
    ((triggerChain t2 e2).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).1.val < t2.length := by
  by_cases hlt : t1.length < t2.length
  · have hbd := triggerChain_run_val_le t2 e2 ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)
    dsimp only at hbd
    omega
  · have heqLen : t1.length = t2.length := by omega
    -- Find an index i < t1.length where t1[i] ≠ t2[i]; in fact take the FIRST such index!
    have hex : ∃ i : Nat, ∃ hi : i < t1.length,
        (∀ j : Nat, (hj : j < i) → t1[j]'(by omega) = t2[j]'(by omega)) ∧
        t1[i]'hi ≠ t2[i]'(by omega) := by
      have findDiff : ∀ (a b : List Bool) (hab : a.length = b.length), a ≠ b →
          ∃ i : Nat, ∃ hi : i < a.length,
            (∀ j, (hj : j < i) → a[j]'(by omega) = b[j]'(by omega)) ∧
            a[i]'hi ≠ b[i]'(by omega) := by
        intro a
        induction a with
        | nil =>
          intro b hab hne'
          cases b with
          | nil => exact absurd rfl hne'
          | cons _ _ => simp at hab
        | cons x xs ih =>
          intro b hab hne'
          cases b with
          | nil => simp at hab
          | cons y ys =>
            by_cases hxy : x = y
            · have hne_tl : xs ≠ ys := fun h => hne' (by rw [hxy, h])
              rcases ih ys (by simp at hab; exact hab) hne_tl with ⟨i, hi, hp, hd⟩
              refine ⟨i + 1, by simp; omega, ?_, by simpa using hd⟩
              intro j hj
              cases j with
              | zero => exact hxy
              | succ j' => simpa using hp j' (by omega)
            · refine ⟨0, by simp, ?_, by simpa using hxy⟩
              intro j hj; omega
      exact findDiff t1 t2 heqLen hne
    rcases hex with ⟨idx, hidx, hpref, hdiff⟩
    have hsplit1 : t1 = t1.take idx ++ (t1[idx]'hidx :: t1.drop (idx + 1)) := by
      have h1 := (List.take_append_drop idx t1).symm
      rw [List.drop_eq_getElem_cons hidx] at h1
      exact h1
    have htake_eq : t1.take idx = t2.take idx := by
      apply List.ext_getElem
      · simp; omega
      · intro j hj1 hj2
        simp only [List.getElem_take]
        have hjlt : j < idx := by simp at hj1; omega
        exact hpref j hjlt
    have htake_len : (t1.take idx).length = idx := by simp; omega
    have hlen_sum : t1.length = idx + (t1.length - idx) := by omega
    have hfb : fromBits t1 = fromBits (t1.take idx) + 2 ^ idx * fromBits (t1[idx]'hidx :: t1.drop (idx + 1)) := by
      conv => lhs; rw [hsplit1, fromBits_append, htake_len]
    have hlt_take : fromBits (t1.take idx) < 2 ^ idx := by
      have := fromBits_lt_pow (t1.take idx); rwa [htake_len] at this
    rw [hlen_sum, hfb, LsbTransducer.run_add_pow _ _ idx (t1.length - idx) _ _ hlt_take]
    dsimp only
    have hq_idx : ((triggerChain t2 e2).run ⟨0, Nat.zero_lt_succ _⟩ idx (fromBits (t1.take idx))).1 =
        ⟨idx, by omega⟩ := by
      apply Fin.ext
      rw [htake_eq]
      exact triggerChain_run_take t2 e2 idx (by omega)
    rw [hq_idx]
    have hrem_pos : t1.length - idx = (t1.length - idx - 1) + 1 := by omega
    rw [hrem_pos, LsbTransducer.run]
    simp only [fromBits]
    have hmod : (((if t1[idx] then 1 else 0) + 2 * fromBits (t1.drop (idx + 1))) % 2 == 1) = t1[idx] := by
      cases t1[idx] <;> simp
    have hmiss : (triggerChain t2 e2).step ⟨idx, by omega⟩ (t1[idx]'hidx) = (⟨idx, by omega⟩, false) :=
      triggerChain_step_miss t2 e2 ⟨idx, by omega⟩ (by dsimp only; omega) (t1[idx]'hidx) hdiff
    rw [hmod]
    change ((triggerChain t2 e2).run ((triggerChain t2 e2).step ⟨idx, by omega⟩ (t1[idx]'hidx)).1
        (t1.length - idx - 1) _).1.val < t2.length
    rw [hmiss]
    dsimp only
    have hbd := triggerChain_run_val_le t2 e2 ⟨idx, by omega⟩ (t1.length - idx - 1)
      (((if t1[idx] then 1 else 0) + 2 * fromBits (t1.drop (idx + 1))) / 2)
    dsimp only at hbd
    omega

/-- Constructive separating witness for ANY two distinct valid TriggerChains `(t1, e1) ≠ (t2, e2)`
    with `t1.length ≤ t2.length`: `x = fromBits t1 + 2 ^ t1.length` separates them mod `2^(t1.length + 1)`! -/
theorem triggerChain_separate_witness {t1 t2 : List Bool} {e1 e2 : Bool}
    (hv1 : ValidSpec t1 e1) (hv2 : ValidSpec t2 e2)
    (hlen : t1.length ≤ t2.length) (hne : (t1, e1) ≠ (t2, e2)) :
    (triggerChain t1 e1).evalMod (t1.length + 1) (fromBits t1 + 2 ^ t1.length) ≠
    (triggerChain t2 e2).evalMod (t1.length + 1) (fromBits t1 + 2 ^ t1.length) := by
  unfold LsbTransducer.evalMod
  change ((triggerChain t1 e1).run ⟨0, Nat.zero_lt_succ _⟩ (t1.length + 1) (fromBits t1 + 2 ^ t1.length)).2 ≠
         ((triggerChain t2 e2).run ⟨0, Nat.zero_lt_succ _⟩ (t1.length + 1) (fromBits t1 + 2 ^ t1.length)).2
  have hlt1 : fromBits t1 < 2 ^ t1.length := fromBits_lt_pow t1
  have hx : fromBits t1 + 2 ^ t1.length = fromBits t1 + 2 ^ t1.length * 1 := by omega
  rw [hx, LsbTransducer.run_add_pow (triggerChain t1 e1) _ t1.length 1 (fromBits t1) 1 hlt1,
      LsbTransducer.run_add_pow (triggerChain t2 e2) _ t1.length 1 (fromBits t1) 1 hlt1]
  dsimp only
  -- Compute output of T1: reaches COPY after t1.length steps, then emits 1 on bit t1.length!
  have hq1 : ((triggerChain t1 e1).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).1.val = t1.length := by
    simpa using triggerChain_run_drop t1 e1 0 (Nat.zero_le _)
  have hstep1 : ((triggerChain t1 e1).run
      ((triggerChain t1 e1).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).1 1 1).2 = 1 := by
    rw [LsbTransducer.run]
    have h1 : (1 % 2 == 1) = true := rfl
    rw [h1, triggerChain_step_copy t1 e1 _ hq1 true]
    simp [LsbTransducer.run]
  rw [hstep1]
  by_cases ht : t1 = t2
  · subst ht
    have hene : e1 ≠ e2 := fun h => hne (by rw [h])
    -- Both reach COPY after t1.length steps, so upper bit is 1 for both; compare lower bits!
    have hq2 : ((triggerChain t1 e2).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).1.val = t1.length := by
      simpa using triggerChain_run_drop t1 e2 0 (Nat.zero_le _)
    have hstep2 : ((triggerChain t1 e2).run
        ((triggerChain t1 e2).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).1 1 1).2 = 1 := by
      rw [LsbTransducer.run]
      have h1 : (1 % 2 == 1) = true := rfl
      rw [h1, triggerChain_step_copy t1 e2 _ hq2 true]
      simp [LsbTransducer.run]
    rw [hstep2]
    have ho1 : ((triggerChain t1 e1).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).2 =
        if e1 = true ∧ 0 < t1.length then 2 ^ (t1.length - 1) else 0 := by
      simpa using triggerChain_run_exact_out t1 e1 0 (Nat.zero_le _)
    have ho2 : ((triggerChain t1 e2).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).2 =
        if e2 = true ∧ 0 < t1.length then 2 ^ (t1.length - 1) else 0 := by
      simpa using triggerChain_run_exact_out t1 e2 0 (Nat.zero_le _)
    rw [ho1, ho2]
    cases e1 <;> cases e2
    · exact absurd rfl hene
    · have hpos : 0 < t1.length := by
        have hl := hv2 rfl
        cases t1 with
        | nil => simp at hl
        | cons _ _ => simp
      simp [hpos]
    · have hpos : 0 < t1.length := by
        have hl := hv1 rfl
        cases t1 with
        | nil => simp at hl
        | cons _ _ => simp
      simp [hpos]
    · exact absurd rfl hene
  · -- t1 ≠ t2: T2 stalls strictly before COPY, so emits 0 on bit t1.length!
    have hq2_lt := triggerChain_stall_of_ne e2 hlen ht
    have hstep2 : ((triggerChain t2 e2).run
        ((triggerChain t2 e2).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).1 1 1).2 = 0 := by
      rw [LsbTransducer.run]
      have h1 : (1 % 2 == 1) = true := rfl
      rw [h1]
      have h0 := triggerChain_valid_step_true_out hv2 _ hq2_lt
      cases hst : (triggerChain t2 e2).step
          ((triggerChain t2 e2).run ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)).1 true with
      | mk qf bo =>
        rw [hst] at h0; dsimp only at h0; subst h0
        simp [LsbTransducer.run]
    rw [hstep2]
    have hlt2 := LsbTransducer.run_lt_pow (triggerChain t2 e2) ⟨0, Nat.zero_lt_succ _⟩ t1.length (fromBits t1)
    omega

/-- THEOREM 2 (Fenwick Free Monoid Theorem):
    The low-bit jump operators U and D generate a FREE monoid on Nat:
    no two distinct words in {U, D}* induce the same function Nat → Nat. -/
theorem fenwick_free_monoid (w1 w2 : List FenwickOp)
    (h : ∀ x : Nat, evalWord w1 x = evalWord w2 x) : w1 = w2 := by
  apply compileSpec_injective
  by_cases hEqSpec : compileSpec w1 = compileSpec w2
  · exact hEqSpec
  · exfalso
    by_cases hlen : (compileSpec w1).1.length ≤ (compileSpec w2).1.length
    · have hsep := triggerChain_separate_witness (compileSpec_valid w1) (compileSpec_valid w2) hlen hEqSpec
      let n := (compileSpec w1).1.length + 1
      let x := fromBits (compileSpec w1).1 + 2 ^ (compileSpec w1).1.length
      have heq : (compileTC w1).evalMod n x = (compileTC w2).evalMod n x := by
        rw [← evalWord_mod_eq_compile w1 n x, ← evalWord_mod_eq_compile w2 n x, h x]
      exact hsep heq
    · have hlen2 : (compileSpec w2).1.length ≤ (compileSpec w1).1.length := by omega
      have hsep := triggerChain_separate_witness (compileSpec_valid w2) (compileSpec_valid w1) hlen2 (Ne.symm hEqSpec)
      let n := (compileSpec w2).1.length + 1
      let x := fromBits (compileSpec w2).1 + 2 ^ (compileSpec w2).1.length
      have heq : (compileTC w2).evalMod n x = (compileTC w1).evalMod n x := by
        rw [← evalWord_mod_eq_compile w2 n x, ← evalWord_mod_eq_compile w1 n x, h x]
      exact hsep heq

-- ============================================================================
-- THEOREM 3: Sharp Finite-Width Collapse & Exact Cardinality |<U_w, D_w>| = 2^w
-- ============================================================================

/-- THEOREM 3a (Exact Nilpotency at Index w):
    For EVERY bit-width w ≥ 1 and EVERY word v of length ≥ w, evalWord v x ≡ 0 (mod 2^w) ∀ x. -/
theorem evalWord_mod_zero_of_len_ge (w : Nat) (v : List FenwickOp) (hv : w ≤ v.length) (x : Nat) :
    evalWord v x % 2 ^ w = 0 := by
  rw [evalWord_mod_eq_compile]
  unfold compileTC LsbTransducer.evalMod
  apply triggerChain_run_zero_of_lt
  have hlen := compileSpec_len v
  have he := compileSpec_emit v
  have hinit : ((triggerChain (compileSpec v).1 (compileSpec v).2).init).val = 0 := rfl
  rw [hinit]
  cases v with
  | nil =>
    have hw0 : w = 0 := by simp at hv; omega
    subst hw0
    right; exact ⟨rfl, Nat.zero_le _⟩
  | cons g v' =>
    cases g with
    | D =>
      right
      exact ⟨he, by simp only [List.length_cons] at hlen hv; omega⟩
    | U =>
      left
      simp only [List.length_cons] at hlen hv
      omega

/-- Helper: when `t` ends in `false` and has length `w ≥ 1`, `fromBits t < 2^(w - 1) < 2^w`. -/
theorem fromBits_lt_half_of_last_false {t : List Bool} (hlast : t.getLast? = some false) :
    fromBits t < 2 ^ (t.length - 1) := by
  cases ht : t.reverse with
  | nil =>
    have : t = [] := List.reverse_eq_nil_iff.mp ht
    subst this; simp at hlast
  | cons b revRest =>
    have hteq : t = revRest.reverse ++ [b] := by
      have := congrArg List.reverse ht
      simpa using this
    rw [hteq] at hlast
    have hb : b = false := by
      rw [List.getLast?_append] at hlast
      simp at hlast
      exact hlast
    subst hb
    rw [hteq, fromBits_append]
    simp only [fromBits, List.length_append, List.length_singleton, Nat.add_sub_cancel]
    simpa using fromBits_lt_pow revRest.reverse

/-- THEOREM 3b (Strict Non-Vanishing Below Width w):
    For EVERY w ≥ 1 and EVERY word v of length < w, there exists x < 2^w with evalWord v x % 2^w ≠ 0. -/
theorem evalWord_mod_nonzero_of_len_lt (w : Nat) (v : List FenwickOp) (hv : v.length < w) :
    ∃ x : Nat, x < 2 ^ w ∧ evalWord v x % 2 ^ w ≠ 0 := by
  cases v with
  | nil =>
    have hw1 : 1 ≤ w := by simp at hv; omega
    have h2 : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw1
    refine ⟨1, by omega, ?_⟩
    simp only [evalWord]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  | cons g v' =>
    let v := g :: v'
    have hv' : v.length < w := hv
    let t := (compileSpec v).1
    let e := (compileSpec v).2
    have hlen := compileSpec_len v
    have he := compileSpec_emit v
    cases g with
    | D =>
      have htlen : t.length = v.length := hlen
      have hlt_pow : fromBits t + 2 ^ t.length < 2 ^ w := by
        have h1 := fromBits_lt_pow t
        have h2 : 2 ^ (t.length + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.pow_succ] at h2
        omega
      refine ⟨fromBits t + 2 ^ t.length, hlt_pow, ?_⟩
      intro hzero
      have hdiv_pow : 2 ^ (t.length + 1) ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
      have hmod0 : evalWord v (fromBits t + 2 ^ t.length) % 2 ^ (t.length + 1) = 0 := by
        rw [← Nat.mod_mod_of_dvd _ hdiv_pow, hzero, Nat.zero_mod]
      rw [evalWord_mod_eq_compile] at hmod0
      unfold compileTC LsbTransducer.evalMod at hmod0
      change ((triggerChain t e).run ⟨0, Nat.zero_lt_succ _⟩ (t.length + 1) (fromBits t + 2 ^ t.length)).2 = 0 at hmod0
      have hx : fromBits t + 2 ^ t.length = fromBits t + 2 ^ t.length * 1 := by omega
      rw [hx, LsbTransducer.run_add_pow _ _ t.length 1 (fromBits t) 1 (fromBits_lt_pow t)] at hmod0
      dsimp only at hmod0
      have hq : ((triggerChain t e).run ⟨0, Nat.zero_lt_succ _⟩ t.length (fromBits t)).1.val = t.length := by
        simpa using triggerChain_run_drop t e 0 (Nat.zero_le _)
      have hstep : ((triggerChain t e).run
          ((triggerChain t e).run ⟨0, Nat.zero_lt_succ _⟩ t.length (fromBits t)).1 1 1).2 = 1 := by
        rw [LsbTransducer.run]
        have h1 : (1 % 2 == 1) = true := rfl
        rw [h1, triggerChain_step_copy t e _ hq true]
        simp [LsbTransducer.run]
      rw [hstep] at hmod0
      have hpos : 0 < 2 ^ t.length := Nat.two_pow_pos _
      omega
    | U =>
      have htlen : t.length = v.length + 1 := hlen
      have heT : e = true := he
      have hlast : t.getLast? = some false := compileSpec_valid_last v heT
      have hlt_x : fromBits t < 2 ^ w := by
        have h1 := fromBits_lt_half_of_last_false hlast
        have h2 : 2 ^ (t.length - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      refine ⟨fromBits t, hlt_x, ?_⟩
      intro hzero
      have hdiv_pow : 2 ^ t.length ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
      have hmod0 : evalWord v (fromBits t) % 2 ^ t.length = 0 := by
        rw [← Nat.mod_mod_of_dvd _ hdiv_pow, hzero, Nat.zero_mod]
      rw [evalWord_mod_eq_compile] at hmod0
      unfold compileTC LsbTransducer.evalMod at hmod0
      change ((triggerChain t e).run ⟨0, Nat.zero_lt_succ _⟩ t.length (fromBits t)).2 = 0 at hmod0
      have ho : ((triggerChain t e).run ⟨0, Nat.zero_lt_succ _⟩ t.length (fromBits t)).2 =
          if e = true ∧ 0 < t.length then 2 ^ (t.length - 1) else 0 := by
        simpa using triggerChain_run_exact_out t e 0 (Nat.zero_le _)
      have hpos : 0 < t.length := by omega
      rw [ho] at hmod0
      simp only [heT, hpos, and_self, ↓reduceIte] at hmod0
      have hpow_pos : 0 < 2 ^ (t.length - 1) := Nat.two_pow_pos _
      omega

/-- THEOREM 3c (Faithfulness Below Width w):
    Any two distinct words v1, v2 of length < w induce DISTINCT functions on [0, 2^w) mod 2^w! -/
theorem evalWord_mod_injective_of_len_lt (w : Nat) (v1 v2 : List FenwickOp)
    (hv1 : v1.length < w) (hv2 : v2.length < w)
    (h : ∀ x < 2 ^ w, evalWord v1 x % 2 ^ w = evalWord v2 x % 2 ^ w) :
    v1 = v2 := by
  apply compileSpec_injective
  by_cases hEqSpec : compileSpec v1 = compileSpec v2
  · exact hEqSpec
  · exfalso
    suffices ∀ a b : List FenwickOp, a.length < w → b.length < w →
        (compileSpec a).1.length ≤ (compileSpec b).1.length →
        compileSpec a ≠ compileSpec b →
        (∀ x < 2 ^ w, evalWord a x % 2 ^ w = evalWord b x % 2 ^ w) → False by
      by_cases hle : (compileSpec v1).1.length ≤ (compileSpec v2).1.length
      · exact this v1 v2 hv1 hv2 hle hEqSpec h
      · exact this v2 v1 hv2 hv1 (by omega) (Ne.symm hEqSpec) (fun x hx => (h x hx).symm)
    intro a b ha hb hle hne_ab hab
    let t1 := (compileSpec a).1
    let e1 := (compileSpec a).2
    let t2 := (compileSpec b).1
    let e2 := (compileSpec b).2
    have hlen1 := compileSpec_len a
    have hlen2 := compileSpec_len b
    by_cases hltw : t1.length < w
    · have hx_lt : fromBits t1 + 2 ^ t1.length < 2 ^ w := by
        have h1 := fromBits_lt_pow t1
        have h2 : 2 ^ (t1.length + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.pow_succ] at h2; omega
      have hsep := triggerChain_separate_witness (compileSpec_valid a) (compileSpec_valid b) hle hne_ab
      have hdiv : 2 ^ (t1.length + 1) ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
      have heq_mod : evalWord a (fromBits t1 + 2 ^ t1.length) % 2 ^ (t1.length + 1) =
          evalWord b (fromBits t1 + 2 ^ t1.length) % 2 ^ (t1.length + 1) := by
        rw [← Nat.mod_mod_of_dvd _ hdiv, hab _ hx_lt, Nat.mod_mod_of_dvd _ hdiv]
      rw [evalWord_mod_eq_compile, evalWord_mod_eq_compile] at heq_mod
      exact hsep heq_mod
    · have ht1_le : (compileSpec a).1.length ≤ w := by
        cases a with
        | nil => simp [compileSpec]
        | cons g v' => cases g <;> simp only at hlen1 <;> omega
      have ht2_le : (compileSpec b).1.length ≤ w := by
        cases b with
        | nil => simp [compileSpec]
        | cons g v' => cases g <;> simp only at hlen2 <;> omega
      have ht1_eq : (compileSpec a).1.length = w := by dsimp only [t1] at hltw; omega
      have ht2_eq : (compileSpec b).1.length = w := by omega
      have he1 : (compileSpec a).2 = true := by
        have hem := compileSpec_emit a
        cases a with
        | nil => simp [compileSpec] at ht1_eq; omega
        | cons g v' => cases g <;> simp only at hlen1 hem <;> omega
      have he2 : (compileSpec b).2 = true := by
        have hem := compileSpec_emit b
        cases b with
        | nil => simp [compileSpec] at ht2_eq; omega
        | cons g v' => cases g <;> simp only at hlen2 hem <;> omega
      have htne : t1 ≠ t2 := by
        intro ht; apply hne_ab; exact Prod.ext ht (by rw [he1, he2])
      have hlast1 : t1.getLast? = some false := compileSpec_valid_last a he1
      have ht1_eq' : t1.length = w := ht1_eq
      have hx_lt : fromBits t1 < 2 ^ w := by
        have h1 := fromBits_lt_half_of_last_false hlast1
        have h2 : 2 ^ (t1.length - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have heq := hab (fromBits t1) hx_lt
      rw [evalWord_mod_eq_compile, evalWord_mod_eq_compile] at heq
      unfold compileTC LsbTransducer.evalMod at heq
      change ((triggerChain t1 e1).run ⟨0, Nat.zero_lt_succ _⟩ w (fromBits t1)).2 =
             ((triggerChain t2 e2).run ⟨0, Nat.zero_lt_succ _⟩ w (fromBits t1)).2 at heq
      have ho1 : ((triggerChain t1 e1).run ⟨0, Nat.zero_lt_succ _⟩ w (fromBits t1)).2 = 2 ^ (w - 1) := by
        have h0 := triggerChain_run_exact_out t1 e1 0 (Nat.zero_le _)
        simp only [Nat.sub_zero, List.drop_zero] at h0
        have hwpos : 0 < t1.length := by omega
        have he1' : e1 = true := he1
        rw [he1'] at h0 ⊢
        simp only [hwpos, and_self, ↓reduceIte] at h0
        rw [← ht1_eq']
        exact h0
      have hq2_lt : ((triggerChain t2 e2).run ⟨0, Nat.zero_lt_succ _⟩ w (fromBits t1)).1.val < t2.length := by
        rw [← ht1_eq]
        exact triggerChain_stall_of_ne e2 (by omega) htne
      have ho2_zero : ∀ q k x,
          ((triggerChain t2 e2).run q k x).1.val < t2.length →
          ((triggerChain t2 e2).run q k x).2 = 0 := by
        intro q k x
        induction k generalizing q x with
        | zero => intro _; simp [LsbTransducer.run]
        | succ k ih =>
          rw [LsbTransducer.run]
          intro hfin
          have hqlt : q.val < t2.length := by
            by_cases hltq : q.val < t2.length
            · exact hltq
            · exfalso
              have hqeq : q.val = t2.length := by omega
              have hstay : ∀ m z, ((triggerChain t2 e2).run q m z).1.val = t2.length := by
                intro m
                induction m with
                | zero => intro _; exact hqeq
                | succ m ihm =>
                  intro z; rw [LsbTransducer.run, triggerChain_step_copy t2 e2 q hqeq]
                  exact ihm (z / 2)
              have := hstay (k + 1) x
              rw [LsbTransducer.run] at this
              omega
          by_cases hb : (x % 2 == 1) = t2[q.val]
          · rw [triggerChain_step_match t2 e2 q hqlt (x % 2 == 1) hb] at hfin ⊢
            dsimp only at hfin ⊢
            have hnotlast : q.val + 1 < t2.length := by
              by_cases hlt1 : q.val + 1 < t2.length
              · exact hlt1
              · exfalso
                have hqeq : q.val + 1 = t2.length := by omega
                have hstay : ∀ m z, ((triggerChain t2 e2).run ⟨q.val + 1, Nat.succ_lt_succ hqlt⟩ m z).1.val = t2.length := by
                  intro m
                  induction m with
                  | zero => intro _; exact hqeq
                  | succ m ihm =>
                    intro z; rw [LsbTransducer.run, triggerChain_step_copy t2 e2 _ hqeq]
                    exact ihm (z / 2)
                have := hstay k (x / 2)
                omega
            have hbeq : (q.val + 1 == t2.length) = false := by simp; omega
            rw [hbeq, Bool.and_false, ih _ _ hfin]; rfl
          · rw [triggerChain_step_miss t2 e2 q hqlt (x % 2 == 1) hb] at hfin ⊢
            dsimp only at hfin ⊢
            rw [ih _ _ hfin]; rfl
      have ho2 := ho2_zero ⟨0, Nat.zero_lt_succ _⟩ w (fromBits t1) hq2_lt
      rw [ho1, ho2] at heq
      have hpow_pos : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
      omega

theorem wordsOfLen_length (k : Nat) : (wordsOfLen k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [wordsOfLen, ih, Nat.pow_succ]; omega

theorem wordsLt_length (w : Nat) : (wordsLt w).length = 2 ^ w - 1 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp [wordsLt, ih, wordsOfLen_length, Nat.pow_succ]
    have := Nat.one_le_pow w 2 (by omega)
    omega

theorem wordsOfLen_mem_iff (k : Nat) (v : List FenwickOp) :
    v ∈ wordsOfLen k ↔ v.length = k := by
  induction k generalizing v with
  | zero =>
    simp [wordsOfLen]
  | succ k ih =>
    simp only [wordsOfLen, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> simp [(ih u).mp hu]
    · intro hlen
      cases v with
      | nil => simp at hlen
      | cons g u =>
        have hu : u.length = k := by simp at hlen; omega
        cases g
        · left; exact ⟨u, (ih u).mpr hu, rfl⟩
        · right; exact ⟨u, (ih u).mpr hu, rfl⟩

theorem wordsLt_mem_iff (w : Nat) (v : List FenwickOp) :
    v ∈ wordsLt w ↔ v.length < w := by
  induction w with
  | zero => simp [wordsLt]
  | succ w ih =>
    simp only [wordsLt, List.mem_append, ih, wordsOfLen_mem_iff]
    omega

/-- THEOREM 3d (Exact Cardinality `|<U_w, D_w>| = 2^w` on `BitVec w`, ∀ w : Nat):
    `finiteMonoidReps w` has exact length `2^w`, covers EVERY word `v ∈ {U, D}*` modulo `2^w`,
    and all `2^w` representatives induce pairwise distinct functions on `[0, 2^w) → [0, 2^w)`. -/
theorem fenwick_finite_monoid_card (w : Nat) :
    (finiteMonoidReps w).length = 2 ^ w ∧
    (∀ v : List FenwickOp, ∃ r ∈ finiteMonoidReps w,
        ∀ x < 2 ^ w, evalWord v x % 2 ^ w = evalWord r x % 2 ^ w) ∧
    (∀ i j : Fin (finiteMonoidReps w).length,
        (∀ x < 2 ^ w, evalWord ((finiteMonoidReps w)[i]) x % 2 ^ w =
                      evalWord ((finiteMonoidReps w)[j]) x % 2 ^ w) → i = j) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Exact count: (2^w - 1) + 1 = 2^w
    simp only [finiteMonoidReps, List.length_append, wordsLt_length, List.length_singleton]
    have := Nat.one_le_pow w 2 (by omega)
    omega
  · -- Completeness: every word v matches some r ∈ finiteMonoidReps w mod 2^w
    intro v
    by_cases hlt : v.length < w
    · refine ⟨v, ?_, fun _ _ => rfl⟩
      simp [finiteMonoidReps, wordsLt_mem_iff, hlt]
    · refine ⟨List.replicate w FenwickOp.D, ?_, ?_⟩
      · simp [finiteMonoidReps]
      · intro x _
        rw [evalWord_mod_zero_of_len_ge w v (by omega) x,
            evalWord_mod_zero_of_len_ge w (List.replicate w FenwickOp.D) (by simp) x]
  · -- Pairwise distinctness of all 2^w representatives as functions mod 2^w
    have nodup_map_inj : ∀ {α β : Type} (f : α → β) (l : List α),
        (∀ x y, f x = f y → x = y) → l.Nodup → (l.map f).Nodup := by
      intro α β f l hf hnd
      induction l with
      | nil => simp
      | cons a as ih =>
        simp only [List.nodup_cons] at hnd
        simp only [List.map_cons, List.nodup_cons, List.mem_map]
        refine ⟨?_, ih hnd.2⟩
        rintro ⟨b, hb, hfb⟩
        have hab := hf b a hfb
        subst hab
        exact hnd.1 hb
    have nodup_getElem_inj : ∀ {α : Type} (l : List α), l.Nodup →
        ∀ (a b : Nat) (ha : a < l.length) (hb : b < l.length), l[a]'ha = l[b]'hb → a = b := by
      intro α l hnd
      induction l with
      | nil => intro a _ ha; simp at ha
      | cons x xs ih =>
        simp only [List.nodup_cons] at hnd
        intro a b ha hb heq
        cases a with
        | zero =>
          cases b with
          | zero => rfl
          | succ b' =>
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
            exact absurd (heq ▸ List.getElem_mem _) hnd.1
        | succ a' =>
          cases b with
          | zero =>
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
            exact absurd (heq.symm ▸ List.getElem_mem _) hnd.1
          | succ b' =>
            simp only [List.getElem_cons_succ] at heq
            exact congrArg Nat.succ (ih hnd.2 a' b' (by simp at ha; omega) (by simp at hb; omega) heq)
    have hnodup_len : ∀ k, (wordsOfLen k).Nodup := by
      intro k
      induction k with
      | zero => simp [wordsOfLen]
      | succ k ih =>
        simp only [wordsOfLen, List.nodup_append]
        refine ⟨nodup_map_inj (.D :: ·) _ (fun _ _ h => (List.cons.inj h).2) ih,
                nodup_map_inj (.U :: ·) _ (fun _ _ h => (List.cons.inj h).2) ih, ?_⟩
        intro a ha b hb heq
        simp only [List.mem_map] at ha hb
        rcases ha with ⟨_, _, rfl⟩
        rcases hb with ⟨_, _, rfl⟩
        cases heq
    have hnodup_lt : ∀ m, (wordsLt m).Nodup := by
      intro m
      induction m with
      | zero => simp [wordsLt]
      | succ m' ih =>
        simp only [wordsLt, List.nodup_append]
        refine ⟨ih, hnodup_len m', ?_⟩
        intro a ha b hb heq
        subst heq
        have h1 := (wordsLt_mem_iff m' a).mp ha
        have h2 := (wordsOfLen_mem_iff m' a).mp hb
        omega
    intro i j hij
    by_cases hi : i.val < (wordsLt w).length
    · by_cases hj : j.val < (wordsLt w).length
      · have hgi : (finiteMonoidReps w)[i] = (wordsLt w)[i.val] := by
          change (wordsLt w ++ [List.replicate w FenwickOp.D])[i.val]'i.isLt = (wordsLt w)[i.val]
          exact List.getElem_append_left hi
        have hgj : (finiteMonoidReps w)[j] = (wordsLt w)[j.val] := by
          change (wordsLt w ++ [List.replicate w FenwickOp.D])[j.val]'j.isLt = (wordsLt w)[j.val]
          exact List.getElem_append_left hj
        rw [hgi, hgj] at hij
        have hli : (wordsLt w)[i.val].length < w := (wordsLt_mem_iff w _).mp (List.getElem_mem _)
        have hlj : (wordsLt w)[j.val].length < w := (wordsLt_mem_iff w _).mp (List.getElem_mem _)
        have heq_w := evalWord_mod_injective_of_len_lt w _ _ hli hlj hij
        exact Fin.ext (nodup_getElem_inj (wordsLt w) (hnodup_lt w) i.val j.val hi hj heq_w)
      · have hgi : (finiteMonoidReps w)[i] = (wordsLt w)[i.val] := by
          change (wordsLt w ++ [List.replicate w FenwickOp.D])[i.val]'i.isLt = (wordsLt w)[i.val]
          exact List.getElem_append_left hi
        have hgj : (finiteMonoidReps w)[j] = List.replicate w FenwickOp.D := by
          have hj_lt : j.val < (wordsLt w ++ [List.replicate w FenwickOp.D]).length := j.isLt
          have hsub : j.val - (wordsLt w).length = 0 := by
            simp only [List.length_append, List.length_singleton] at hj_lt; omega
          change (wordsLt w ++ [List.replicate w FenwickOp.D])[j.val]'hj_lt = List.replicate w FenwickOp.D
          rw [List.getElem_append_right (Nat.le_of_not_lt hj)]
          simp [hsub]
        rw [hgi, hgj] at hij
        have hli : (wordsLt w)[i.val].length < w := (wordsLt_mem_iff w _).mp (List.getElem_mem _)
        rcases evalWord_mod_nonzero_of_len_lt w _ hli with ⟨x, hx, hnz⟩
        have h0 := evalWord_mod_zero_of_len_ge w (List.replicate w FenwickOp.D) (by simp) x
        rw [hij x hx] at hnz
        exact absurd h0 hnz
    · by_cases hj : j.val < (wordsLt w).length
      · have hgi : (finiteMonoidReps w)[i] = List.replicate w FenwickOp.D := by
          have hi_lt : i.val < (wordsLt w ++ [List.replicate w FenwickOp.D]).length := i.isLt
          have hsub : i.val - (wordsLt w).length = 0 := by
            simp only [List.length_append, List.length_singleton] at hi_lt; omega
          change (wordsLt w ++ [List.replicate w FenwickOp.D])[i.val]'hi_lt = List.replicate w FenwickOp.D
          rw [List.getElem_append_right (Nat.le_of_not_lt hi)]
          simp [hsub]
        have hgj : (finiteMonoidReps w)[j] = (wordsLt w)[j.val] := by
          change (wordsLt w ++ [List.replicate w FenwickOp.D])[j.val]'j.isLt = (wordsLt w)[j.val]
          exact List.getElem_append_left hj
        rw [hgi, hgj] at hij
        have hlj : (wordsLt w)[j.val].length < w := (wordsLt_mem_iff w _).mp (List.getElem_mem _)
        rcases evalWord_mod_nonzero_of_len_lt w _ hlj with ⟨x, hx, hnz⟩
        have h0 := evalWord_mod_zero_of_len_ge w (List.replicate w FenwickOp.D) (by simp) x
        rw [← hij x hx] at hnz
        exact absurd h0 hnz
      · apply Fin.ext
        have hi_lt := i.isLt
        have hj_lt := j.isLt
        simp only [finiteMonoidReps, List.length_append, List.length_singleton] at hi_lt hj_lt
        omega

-- ============================================================================
-- SECTION 5: THEOREM 4 — Universal Fenwick Ancestor-Spine Collapse & Bitwise Laws
-- ============================================================================

/-- Clearing the lowest `k` bits of `x` is always an iterated `fenwickD` ancestor of `x`. -/
theorem hi_eq_iter_D (k x : Nat) :
    ∃ m : Nat, (x / 2 ^ k) * 2 ^ k = iterN fenwickD m x := by
  induction k with
  | zero => exact ⟨0, by simp [iterN]⟩
  | succ k ih =>
    rcases ih with ⟨m, hm⟩
    by_cases hbit : (x / 2 ^ k) % 2 = 0
    · refine ⟨m, ?_⟩
      have hdiv : x / 2 ^ (k + 1) = (x / 2 ^ k) / 2 := by
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      rw [hdiv, Nat.pow_succ, ← Nat.mul_assoc]
      have : (x / 2 ^ k) / 2 * 2 = x / 2 ^ k := by omega
      rw [← hm, Nat.mul_right_comm, this]
    · -- Bit k is 1, so lowbit((x / 2^k) * 2^k) = 2^k!
      refine ⟨m + 1, ?_⟩
      simp only [iterN, ← hm]
      have hodd : (x / 2 ^ k) % 2 = 1 := by omega
      have hlb_pow : ∀ r a, a % 2 = 1 → lowbit (a * 2 ^ r) = 2 ^ r := by
        intro r
        induction r with
        | zero =>
          intro a ha
          have ha1 : a = 2 * (a / 2) + 1 := by omega
          rw [Nat.pow_zero, Nat.mul_one]
          conv => lhs; rw [ha1]
          exact lowbit_odd (a / 2)
        | succ r ihr =>
          intro a ha
          rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ r) 2, lowbit_even, ihr a ha, Nat.mul_comm]
      have hlb : lowbit ((x / 2 ^ k) * 2 ^ k) = 2 ^ k := hlb_pow k _ hodd
      simp only [fenwickD, hlb]
      have hdiv : x / 2 ^ (k + 1) = (x / 2 ^ k) / 2 := by
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      have hq : x / 2 ^ k = 2 * ((x / 2 ^ k) / 2) + 1 := by omega
      rw [hdiv, Nat.pow_succ]
      conv => rhs; rw [hq, Nat.add_mul, Nat.one_mul]
      have hcomm : 2 * ((x / 2 ^ k) / 2) * 2 ^ k = (x / 2 ^ k) / 2 * (2 ^ k * 2) := by
        rw [Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k)]
      rw [hcomm]; omega

/-- Bitwise projection of clearing the lowest `k` bits: `((x / 2^k) * 2^k) &&& x = (x / 2^k) * 2^k`. -/
theorem hi_and_self (k x : Nat) :
    ((x / 2 ^ k) * 2 ^ k) &&& x = (x / 2 ^ k) * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hik : i < k
  · have hzero : Nat.testBit ((x / 2 ^ k) * 2 ^ k) i = false := by
      have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by rw [← Nat.pow_add]; congr 1; omega
      have hdiv_eq : (x / 2 ^ k) * 2 ^ k / 2 ^ i = (x / 2 ^ k) * 2 ^ (k - i) := by
        have hstep : (x / 2 ^ k) * 2 ^ k = ((x / 2 ^ k) * 2 ^ (k - i)) * 2 ^ i := by
          rw [Nat.mul_assoc, ← hpow]
        rw [hstep]
        exact Nat.mul_div_cancel _ (Nat.two_pow_pos i)
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv_eq]
      rw [Nat.and_comm 1, Nat.and_one_is_mod]
      have heven : 2 ^ (k - i) % 2 = 0 := by
        have : k - i = (k - i - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; omega
      have hmod0 : ((x / 2 ^ k) * 2 ^ (k - i)) % 2 = 0 := by
        rw [Nat.mul_mod, heven]; simp
      rw [hmod0]; rfl
    rw [hzero]; rfl
  · have hsame : Nat.testBit ((x / 2 ^ k) * 2 ^ k) i = Nat.testBit x i := by
      have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by rw [← Nat.pow_add]; congr 1; omega
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have h1 : (x / 2 ^ k) * 2 ^ k / 2 ^ i = (x / 2 ^ k) / 2 ^ (i - k) := by
        rw [hpow, Nat.mul_comm (x / 2 ^ k) (2 ^ k), Nat.mul_div_mul_left _ _ (Nat.two_pow_pos k)]
      have h2 : x / 2 ^ i = (x / 2 ^ k) / 2 ^ (i - k) := by
        rw [hpow, Nat.div_div_eq_div_mul]
      rw [h1, h2]
    rw [hsame]; cases Nat.testBit x i <;> rfl

/-- Helper: `lowbit` of `(q * 2^r + d)` for `0 < d < 2^r` equals `lowbit d`. -/
theorem lowbit_add_mul_pow (q r d : Nat) (hd0 : 0 < d) (hd : d < 2 ^ r) :
    lowbit (q * 2 ^ r + d) = lowbit d := by
  induction r generalizing q d with
  | zero => omega
  | succ r ih =>
    have hpow : q * 2 ^ (r + 1) = 2 * (q * 2 ^ r) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, ← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc]
    by_cases hodd : d % 2 = 1
    · have h1 : q * 2 ^ (r + 1) + d = 2 * (q * 2 ^ r + d / 2) + 1 := by omega
      have h2 : d = 2 * (d / 2) + 1 := by omega
      rw [h1, lowbit_odd, h2, lowbit_odd]
    · have h1 : q * 2 ^ (r + 1) + d = 2 * (q * 2 ^ r + d / 2) := by omega
      have h2 : d = 2 * (d / 2) := by omega
      rw [h1, lowbit_even]
      conv => rhs; rw [h2, lowbit_even]
      congr 1
      exact ih q (d / 2) (by omega) (by rw [Nat.pow_succ] at hd; omega)

/-- General Fenwick Interval-Ancestor Theorem:
    If `fenwickD y < x ≤ y`, then `y` is a `fenwickU`-ancestor of `x` (and `m ≥ 1` if `x < y`). -/
theorem exists_iter_U_of_interval (x y : Nat) (hlo : fenwickD y < x) (hhi : x ≤ y) :
    ∃ m : Nat, iterN fenwickU m x = y ∧ (x < y → 1 ≤ m) := by
  generalize hd : y - x = dist
  induction dist using Nat.strongRecOn generalizing x with
  | ind d ih =>
    by_cases heq : x = y
    · subst heq; exact ⟨0, rfl, fun h => absurd h (Nat.lt_irrefl _)⟩
    · have hxlt : x < y := by omega
      have hypos : 0 < y := by omega
      have hxpos : 0 < x := by omega
      -- Show fenwickU x ≤ y!
      have hUx_le : fenwickU x ≤ y := by
        let r := ctz y
        have hlb_y : lowbit y = 2 ^ r := lowbit_eq_pow_ctz hypos
        have hdvd_y : 2 ^ r ∣ y := by rw [← hlb_y]; exact lowbit_dvd y
        rcases hdvd_y with ⟨ky, hky⟩
        have hky_pos : 1 ≤ ky := by
          by_cases h0 : ky = 0
          · rw [h0] at hky; simp at hky; omega
          · omega
        have hDy : fenwickD y = (ky - 1) * 2 ^ r := by
          have hadd : (ky - 1) * 2 ^ r + 2 ^ r = y := by
            have h1 : (ky - 1) * 2 ^ r + 1 * 2 ^ r = ((ky - 1) + 1) * 2 ^ r := (Nat.add_mul _ _ _).symm
            rw [Nat.one_mul, Nat.sub_add_cancel hky_pos] at h1
            rw [h1, Nat.mul_comm, ← hky]
          simp only [fenwickD, hlb_y]
          omega
        let rem := x - fenwickD y
        have hrem_pos : 0 < rem := by omega
        have hrem_lt : rem < 2 ^ r := by simp only [rem, fenwickD, hlb_y] at hlo ⊢; omega
        have hx_decomp : x = (ky - 1) * 2 ^ r + rem := by omega
        have hlb_x : lowbit x = lowbit rem := by
          rw [hx_decomp]
          exact lowbit_add_mul_pow (ky - 1) r rem hrem_pos hrem_lt
        have hlb_rem_pow : lowbit rem = 2 ^ ctz rem := lowbit_eq_pow_ctz hrem_pos
        have hctz_lt : ctz rem < r := by
          by_cases hlt_r : ctz rem < r
          · exact hlt_r
          · exfalso
            have h1 : 2 ^ r ≤ 2 ^ ctz rem := Nat.pow_le_pow_right (by omega) (by omega)
            have h2 : lowbit rem ≤ rem := lowbit_le rem
            omega
        have hdvd_rem : lowbit rem ∣ rem := lowbit_dvd rem
        have hdvd_pow : lowbit rem ∣ 2 ^ r := by
          rw [hlb_rem_pow]; exact Nat.pow_dvd_pow 2 (Nat.le_of_lt hctz_lt)
        rcases hdvd_rem with ⟨a, ha⟩
        rcases hdvd_pow with ⟨b, hb⟩
        have hab : a < b := by
          by_cases hlt_ab : a < b
          · exact hlt_ab
          · exfalso
            have : lowbit rem * b ≤ lowbit rem * a := Nat.mul_le_mul_left _ (by omega)
            omega
        have hstep_le : rem + lowbit rem ≤ 2 ^ r := by
          have : lowbit rem * (a + 1) ≤ lowbit rem * b := Nat.mul_le_mul_left _ (by omega)
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
        have hy_eq : fenwickD y + 2 ^ r = y := by
          simp only [fenwickD, hlb_y]
          have := lowbit_le y
          omega
        simp only [fenwickU, hlb_x]
        have hx_eq : x = fenwickD y + rem := by simp only [rem]; omega
        omega
      have hlb_pos : 0 < lowbit x := lowbit_pos hxpos
      have hUx_gt : x < fenwickU x := by simp only [fenwickU]; omega
      have hdist_lt : y - fenwickU x < d := by omega
      rcases ih (y - fenwickU x) hdist_lt (fenwickU x) (by omega) hUx_le rfl with ⟨m, hm, _⟩
      refine ⟨m + 1, ?_, fun _ => by omega⟩
      have hshift : ∀ k z, iterN fenwickU (k + 1) z = iterN fenwickU k (fenwickU z) := by
        intro k
        induction k with
        | zero => intro z; rfl
        | succ k ihk => intro z; change fenwickU (iterN fenwickU (k + 1) z) = fenwickU (iterN fenwickU k (fenwickU z)); rw [ihk z]
      rw [hshift, hm]

/-- Cut-structure of `triggerChain t false`: every run on `x < 2^n` outputs `(x / 2^k) * 2^k` for some `k`. -/
theorem triggerChain_cut_false (t : List Bool) (q : Fin (t.length + 1)) (n x : Nat) (hx : x < 2 ^ n) :
    ∃ k : Nat, ((triggerChain t false).run q n x).2 = (x / 2 ^ k) * 2 ^ k := by
  induction n generalizing q x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    exact ⟨0, by simp [LsbTransducer.run]⟩
  | succ n ih =>
    have hxdiv : x / 2 < 2 ^ n := by rw [Nat.pow_succ] at hx; omega
    rw [LsbTransducer.run]
    by_cases hlt : q.val < t.length
    · by_cases hb : (x % 2 == 1) = t[q.val]
      · rw [triggerChain_step_match t false q hlt (x % 2 == 1) hb]
        dsimp only
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        rcases ih ⟨q.val + 1, Nat.succ_lt_succ hlt⟩ (x / 2) hxdiv with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        rw [hk, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul, Nat.mul_left_comm]
      · rw [triggerChain_step_miss t false q hlt (x % 2 == 1) hb]
        dsimp only
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        rcases ih q (x / 2) hxdiv with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        rw [hk, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul, Nat.mul_left_comm]
    · -- Already in COPY: copies x completely (k = 0)!
      have hqeq : q.val = t.length := by omega
      rw [triggerChain_step_copy t false q hqeq]
      dsimp only
      -- Remaining n steps from COPY just return (x / 2) % 2^n = x / 2!
      have hcopy : ∀ m z, z < 2 ^ m → ((triggerChain t false).run q m z).2 = z := by
        intro m
        induction m with
        | zero => intro z hz; simp [LsbTransducer.run]; omega
        | succ m ihm =>
          intro z hz
          rw [LsbTransducer.run, triggerChain_step_copy t false q hqeq]
          dsimp only
          have hzdiv : z / 2 < 2 ^ m := by rw [Nat.pow_succ] at hz; omega
          rw [ihm (z / 2) hzdiv]
          by_cases ho : z % 2 = 1
          · have : (z % 2 == 1) = true := by simp [ho]
            rw [this]; simp; omega
          · have : (z % 2 == 1) = false := by simp [ho]
            rw [this]; simp; omega
      rw [hcopy n (x / 2) hxdiv]
      refine ⟨0, ?_⟩
      simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one]
      by_cases ho : x % 2 = 1
      · have : (x % 2 == 1) = true := by simp [ho]
        rw [this]; simp; omega
      · have : (x % 2 == 1) = false := by simp [ho]
        rw [this]; simp; omega

/-- Cut-structure of `triggerChain t true` (when `t` starts with `true` and ends with `false`):
    output on `x < 2^n` is either `0` OR `(x / 2^p) * 2^p + 2^p` with `x % 2^p > 0` and `(x / 2^p) % 2 = 0`! -/
theorem triggerChain_cut_true (t : List Bool) (hhead : t.head? = some true)
    (hlast : t.getLast? = some false) (n x : Nat) (hx : x < 2 ^ n) :
    ((triggerChain t true).run ⟨0, Nat.zero_lt_succ _⟩ n x).2 = 0 ∨
    ∃ p : Nat, (x / 2 ^ p) % 2 = 0 ∧ 0 < x % 2 ^ p ∧
      ((triggerChain t true).run ⟨0, Nat.zero_lt_succ _⟩ n x).2 = (x / 2 ^ p) * 2 ^ p + 2 ^ p := by
  -- Helper for states q with 1 ≤ q.val < t.length (where a 1-bit has ALREADY been seen below!)
  have hgen : ∀ (q : Fin (t.length + 1)) (m y : Nat),
      q.val < t.length → y < 2 ^ m →
      ((triggerChain t true).run q m y).2 = 0 ∨
      ∃ p : Nat, (y / 2 ^ p) % 2 = 0 ∧
        ((triggerChain t true).run q m y).2 = (y / 2 ^ p) * 2 ^ p + 2 ^ p := by
    intro q m
    induction m generalizing q with
    | zero => intro y _ _; left; simp [LsbTransducer.run]
    | succ m ih =>
      intro y hqlt hy
      have hydiv : y / 2 < 2 ^ m := by rw [Nat.pow_succ] at hy; omega
      rw [LsbTransducer.run]
      by_cases hb : (y % 2 == 1) = t[q.val]
      · rw [triggerChain_step_match t true q hqlt (y % 2 == 1) hb]
        dsimp only
        by_cases hfin : q.val + 1 = t.length
        · -- Final trigger matched! Since t ends in false, bit 0 of y MUST be 0, and next state is COPY!
          have hbit0 : t[q.val] = false := by
            have hg : t.getLast? = some t[q.val] := by
              rw [List.getLast?_eq_getElem?]
              have : t.length - 1 = q.val := by omega
              rw [this, List.getElem?_eq_getElem hqlt]
            rw [hg] at hlast
            exact Option.some.inj hlast
          have hy_even : y % 2 = 0 := by rw [hbit0] at hb; simp at hb; omega
          have hbeq : (q.val + 1 == t.length) = true := by simp [hfin]
          rw [hbeq, Bool.true_and]
          have hcopy : ∀ k z, z < 2 ^ k →
              ((triggerChain t true).run ⟨q.val + 1, Nat.succ_lt_succ hqlt⟩ k z).2 = z := by
            intro k
            induction k with
            | zero => intro z hz; simp [LsbTransducer.run]; omega
            | succ k ihk =>
              intro z hz
              rw [LsbTransducer.run, triggerChain_step_copy t true _ hfin]
              dsimp only
              have hzdiv : z / 2 < 2 ^ k := by rw [Nat.pow_succ] at hz; omega
              rw [ihk (z / 2) hzdiv]
              by_cases ho : z % 2 = 1
              · have : (z % 2 == 1) = true := by simp [ho]
                rw [this]; simp; omega
              · have : (z % 2 == 1) = false := by simp [ho]
                rw [this]; simp; omega
          rw [hcopy m (y / 2) hydiv]
          right
          refine ⟨0, by simpa using hy_even, ?_⟩
          simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one, ↓reduceIte]
          omega
        · have hbeq : (q.val + 1 == t.length) = false := by simp [hfin]
          rw [hbeq, Bool.and_false]
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          rcases ih ⟨q.val + 1, Nat.succ_lt_succ hqlt⟩ (y / 2) (by dsimp only; omega) hydiv with h0 | ⟨p, hp0, hpeq⟩
          · left; rw [h0]
          · right
            refine ⟨p + 1, ?_, ?_⟩
            · rw [Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]; exact hp0
            · rw [hpeq, Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]
              rw [Nat.mul_add, Nat.mul_left_comm]
      · rw [triggerChain_step_miss t true q hqlt (y % 2 == 1) hb]
        dsimp only
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        rcases ih q (y / 2) hqlt hydiv with h0 | ⟨p, hp0, hpeq⟩
        · left; rw [h0]
        · right
          refine ⟨p + 1, ?_, ?_⟩
          · rw [Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]; exact hp0
          · rw [hpeq, Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]
            rw [Nat.mul_add, Nat.mul_left_comm]
  have htlen_ge2 : 2 ≤ t.length := by
    cases t with
    | nil => simp at hhead
    | cons a rest =>
      cases rest with
      | nil => simp at hhead hlast; rw [hhead] at hlast; cases hlast
      | cons _ _ => simp
  have ht0 : t[0]'(by omega) = true := by
    cases t with
    | nil => simp at hhead
    | cons a _ => simp at hhead; exact hhead
  induction n generalizing x with
  | zero => left; simp [LsbTransducer.run]
  | succ n ih =>
    have hxdiv : x / 2 < 2 ^ n := by rw [Nat.pow_succ] at hx; omega
    rw [LsbTransducer.run]
    have h0lt : (⟨0, Nat.zero_lt_succ t.length⟩ : Fin (t.length + 1)).val < t.length := by
      dsimp only; omega
    by_cases hodd : x % 2 = 1
    · have hb : (x % 2 == 1) = t[0]'(by omega) := by rw [ht0]; simp [hodd]
      rw [triggerChain_step_match t true ⟨0, Nat.zero_lt_succ _⟩ h0lt (x % 2 == 1) hb]
      dsimp only
      have hbeq : (0 + 1 == t.length) = false := by simp; omega
      rw [hbeq, Bool.and_false]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      rcases hgen ⟨1, by omega⟩ n (x / 2) (by dsimp only; omega) hxdiv with h0 | ⟨p, hp0, hpeq⟩
      · left; rw [h0]
      · right
        refine ⟨p + 1, ?_, ?_, ?_⟩
        · rw [Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]; exact hp0
        · have hdvd : 2 ∣ 2 ^ (p + 1) := by rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
          have hm : (x % 2 ^ (p + 1)) % 2 = 1 := by rw [Nat.mod_mod_of_dvd _ hdvd]; exact hodd
          omega
        · rw [hpeq, Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]
          rw [Nat.mul_add, Nat.mul_left_comm]
    · have hb : (x % 2 == 1) ≠ t[0]'(by omega) := by rw [ht0]; simp; omega
      rw [triggerChain_step_miss t true ⟨0, Nat.zero_lt_succ _⟩ h0lt (x % 2 == 1) hb]
      dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      rcases ih (x / 2) hxdiv ht0 with h0 | ⟨p, hp0, hrem_pos, hpeq⟩
      · left; rw [h0]
      · right
        refine ⟨p + 1, ?_, ?_, ?_⟩
        · rw [Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]; exact hp0
        · have hx2 : x = 2 * (x / 2) := by omega
          rw [hx2, Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, Nat.mul_mod_mul_left]
          omega
        · rw [hpeq, Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, ← Nat.div_div_eq_div_mul]
          rw [Nat.mul_add, Nat.mul_left_comm]

/-- Helper: for `(x / 2^p) % 2 = 0`, `((x / 2^p) * 2^p + 2^p) &&& x = (x / 2^p) * 2^p`. -/
theorem u_cut_and_self (x p : Nat) (hbit : (x / 2 ^ p) % 2 = 0) :
    ((x / 2 ^ p) * 2 ^ p + 2 ^ p) &&& x = (x / 2 ^ p) * 2 ^ p := by
  have hsum : (x / 2 ^ p) * 2 ^ p + 2 ^ p = (x / 2 ^ p + 1) * 2 ^ p := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hsum]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hip : i < p
  · have hz1 : Nat.testBit ((x / 2 ^ p + 1) * 2 ^ p) i = false := by
      have hpow : 2 ^ p = 2 ^ (p - i) * 2 ^ i := by rw [← Nat.pow_add]; congr 1; omega
      have hdiv_eq : (x / 2 ^ p + 1) * 2 ^ p / 2 ^ i = (x / 2 ^ p + 1) * 2 ^ (p - i) := by
        have hstep : (x / 2 ^ p + 1) * 2 ^ p = ((x / 2 ^ p + 1) * 2 ^ (p - i)) * 2 ^ i := by
          rw [Nat.mul_assoc, ← hpow]
        rw [hstep]
        exact Nat.mul_div_cancel _ (Nat.two_pow_pos i)
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv_eq]
      rw [Nat.and_comm 1, Nat.and_one_is_mod]
      have hev : 2 ^ (p - i) % 2 = 0 := by
        have : p - i = (p - i - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; omega
      have : ((x / 2 ^ p + 1) * 2 ^ (p - i)) % 2 = 0 := by rw [Nat.mul_mod, hev]; simp
      rw [this]; rfl
    have hz2 : Nat.testBit ((x / 2 ^ p) * 2 ^ p) i = false := by
      have hpow : 2 ^ p = 2 ^ (p - i) * 2 ^ i := by rw [← Nat.pow_add]; congr 1; omega
      have hdiv_eq : (x / 2 ^ p) * 2 ^ p / 2 ^ i = (x / 2 ^ p) * 2 ^ (p - i) := by
        have hstep : (x / 2 ^ p) * 2 ^ p = ((x / 2 ^ p) * 2 ^ (p - i)) * 2 ^ i := by
          rw [Nat.mul_assoc, ← hpow]
        rw [hstep]
        exact Nat.mul_div_cancel _ (Nat.two_pow_pos i)
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv_eq]
      rw [Nat.and_comm 1, Nat.and_one_is_mod]
      have hev : 2 ^ (p - i) % 2 = 0 := by
        have : p - i = (p - i - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; omega
      have : ((x / 2 ^ p) * 2 ^ (p - i)) % 2 = 0 := by rw [Nat.mul_mod, hev]; simp
      rw [this]; rfl
    rw [hz1, hz2]; rfl
  · by_cases heq : i = p
    · subst heq
      have htx : Nat.testBit x i = false := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rw [Nat.and_comm 1, Nat.and_one_is_mod, hbit]; rfl
      have htl : Nat.testBit ((x / 2 ^ i) * 2 ^ i) i = false := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow,
                   Nat.mul_div_cancel _ (Nat.two_pow_pos i)]
        rw [Nat.and_comm 1, Nat.and_one_is_mod, hbit]; rfl
      rw [htx, htl, Bool.and_false]
    · have hgt : p < i := by omega
      have hpow : 2 ^ i = 2 ^ p * 2 ^ (i - p) := by rw [← Nat.pow_add]; congr 1; omega
      have h2ge : 2 ∣ 2 ^ (i - p) := by
        have : i - p = (i - p - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
      have hqsame : (x / 2 ^ p + 1) / 2 ^ (i - p) = (x / 2 ^ p) / 2 ^ (i - p) := by
        -- Since x / 2^p is even and 2^(i-p) is even, adding 1 does not change quotient by 2^(i-p)!
        rcases h2ge with ⟨c, hc⟩
        have h1 : (x / 2 ^ p) = 2 * ((x / 2 ^ p) / 2) := by omega
        have h2 : (x / 2 ^ p + 1) = 2 * ((x / 2 ^ p) / 2) + 1 := by omega
        rw [hc, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        congr 1; omega
      have ht1 : Nat.testBit ((x / 2 ^ p + 1) * 2 ^ p) i = Nat.testBit x i := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have h1 : (x / 2 ^ p + 1) * 2 ^ p / 2 ^ i = (x / 2 ^ p + 1) / 2 ^ (i - p) := by
          rw [hpow, Nat.mul_comm _ (2 ^ p), Nat.mul_div_mul_left _ _ (Nat.two_pow_pos p)]
        have h2 : x / 2 ^ i = (x / 2 ^ p) / 2 ^ (i - p) := by
          rw [hpow, Nat.div_div_eq_div_mul]
        rw [h1, h2, hqsame]
      have ht2 : Nat.testBit ((x / 2 ^ p) * 2 ^ p) i = Nat.testBit x i := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have h1 : (x / 2 ^ p) * 2 ^ p / 2 ^ i = (x / 2 ^ p) / 2 ^ (i - p) := by
          rw [hpow, Nat.mul_comm _ (2 ^ p), Nat.mul_div_mul_left _ _ (Nat.two_pow_pos p)]
        have h2 : x / 2 ^ i = (x / 2 ^ p) / 2 ^ (i - p) := by
          rw [hpow, Nat.div_div_eq_div_mul]
        rw [h1, h2]
      rw [ht1, ht2]; cases Nat.testBit x i <;> rfl

/-- THEOREM 4a (Universal D-Spine Collapse & Bitwise Projection):
    For EVERY mixed Fenwick word `D :: v` and EVERY `x : Nat`, `evalWord (D :: v) x`
    lies on the pure monotone `fenwickD` spine of `x` and satisfies `y &&& x = y`. -/
theorem evalWord_D_spine (v : List FenwickOp) (x : Nat) :
    (∃ m : Nat, evalWord (.D :: v) x = iterN fenwickD m x) ∧
    (evalWord (.D :: v) x &&& x = evalWord (.D :: v) x) := by
  have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
  let n := x + (FenwickOp.D :: v).length
  have hlt_eval : evalWord (.D :: v) x < 2 ^ n := evalWord_lt_pow (.D :: v) x x hx_lt
  have hlt_x_n : x < 2 ^ n := Nat.lt_of_lt_of_le hx_lt (Nat.pow_le_pow_right (by omega) (by omega))
  have heq : evalWord (.D :: v) x = (compileTC (.D :: v)).evalMod n x :=
    evalWord_eq_compile (.D :: v) x n hlt_eval
  have heF : (compileSpec (.D :: v)).2 = false := compileSpec_emit (.D :: v)
  unfold compileTC LsbTransducer.evalMod at heq
  rw [heF] at heq
  change evalWord (.D :: v) x =
      ((triggerChain (compileSpec (.D :: v)).1 false).run ⟨0, Nat.zero_lt_succ _⟩ n x).2 at heq
  rcases triggerChain_cut_false (compileSpec (.D :: v)).1 ⟨0, Nat.zero_lt_succ _⟩ n x hlt_x_n with ⟨k, hk⟩
  rw [heq, hk]
  exact ⟨hi_eq_iter_D k x, hi_and_self k x⟩

/-- THEOREM 4b (Universal U-Spine Collapse & Bitwise Projection):
    For EVERY mixed Fenwick word `U :: v` and EVERY `x : Nat`, `evalWord (U :: v) x` is either `0`
    OR lies strictly on the pure monotone `fenwickU` spine of `x` (`y = U^[m] x`, `m ≥ 1`),
    satisfying `D(y) < x ≤ y` and `y &&& x = D(y)`. -/
theorem evalWord_U_spine (v : List FenwickOp) (x : Nat) :
    evalWord (.U :: v) x = 0 ∨
    ((∃ m : Nat, 1 ≤ m ∧ evalWord (.U :: v) x = iterN fenwickU m x) ∧
     fenwickD (evalWord (.U :: v) x) < x ∧
     x ≤ evalWord (.U :: v) x ∧
     (evalWord (.U :: v) x &&& x = fenwickD (evalWord (.U :: v) x))) := by
  have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
  let n := x + (FenwickOp.U :: v).length + 1
  have hlt_eval : evalWord (.U :: v) x < 2 ^ n := by
    have h1 := evalWord_lt_pow (.U :: v) x x hx_lt
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
  have hlt_x_n : x < 2 ^ n := Nat.lt_of_lt_of_le hx_lt (Nat.pow_le_pow_right (by omega) (by omega))
  have heq : evalWord (.U :: v) x = (compileTC (.U :: v)).evalMod n x :=
    evalWord_eq_compile (.U :: v) x n hlt_eval
  have heT : (compileSpec (.U :: v)).2 = true := compileSpec_emit (.U :: v)
  have hhead : (compileSpec (.U :: v)).1.head? = some true :=
    compileSpec_head (.U :: v) (List.cons_ne_nil _ _)
  have hlast : (compileSpec (.U :: v)).1.getLast? = some false :=
    compileSpec_valid_last (.U :: v) heT
  unfold compileTC LsbTransducer.evalMod at heq
  rw [heT] at heq
  change evalWord (.U :: v) x =
      ((triggerChain (compileSpec (.U :: v)).1 true).run ⟨0, Nat.zero_lt_succ _⟩ n x).2 at heq
  rcases triggerChain_cut_true (compileSpec (.U :: v)).1 hhead hlast n x hlt_x_n with h0 | ⟨p, hp0, hrem_pos, hpeq⟩
  · left; rw [heq, h0]
  · right
    rw [heq, hpeq]
    let y := (x / 2 ^ p) * 2 ^ p + 2 ^ p
    change (∃ m : Nat, 1 ≤ m ∧ y = iterN fenwickU m x) ∧
           fenwickD y < x ∧ x ≤ y ∧ (y &&& x = fenwickD y)
    have hlb_y : lowbit y = 2 ^ p := by
      have hodd : (x / 2 ^ p + 1) % 2 = 1 := by omega
      have hsum : y = (x / 2 ^ p + 1) * 2 ^ p := by simp only [y, Nat.add_mul, Nat.one_mul]
      rw [hsum]
      have hlb_pow : ∀ r a, a % 2 = 1 → lowbit (a * 2 ^ r) = 2 ^ r := by
        intro r
        induction r with
        | zero =>
          intro a ha
          have ha1 : a = 2 * (a / 2) + 1 := by omega
          rw [Nat.pow_zero, Nat.mul_one]
          conv => lhs; rw [ha1]
          exact lowbit_odd (a / 2)
        | succ r ihr =>
          intro a ha
          rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ r) 2, lowbit_even, ihr a ha, Nat.mul_comm]
      exact hlb_pow p _ hodd
    have hDy : fenwickD y = (x / 2 ^ p) * 2 ^ p := by
      simp only [fenwickD, hlb_y, y]; omega
    have hdivmod : x = (x / 2 ^ p) * 2 ^ p + x % 2 ^ p := by
      have := Nat.div_add_mod x (2 ^ p); rw [Nat.mul_comm]; omega
    have hmod_lt : x % 2 ^ p < 2 ^ p := Nat.mod_lt x (Nat.two_pow_pos p)
    have hlo : fenwickD y < x := by rw [hDy]; omega
    have hlt : x < y := by simp only [y]; omega
    rcases exists_iter_U_of_interval x y hlo (Nat.le_of_lt hlt) with ⟨m, hm, hm1⟩
    refine ⟨⟨m, hm1 hlt, hm.symm⟩, hlo, Nat.le_of_lt hlt, ?_⟩
    rw [hDy]
    exact u_cut_and_self x p hp0

-- ============================================================================
-- SECTION 6: THEOREM 5 — Two's-Complement Word-Conjugation & Fenwick Depth Duality
-- ============================================================================

/-- Helper: `lowbit (2^n - x) = lowbit x` for all `0 < x < 2^n`. -/
theorem lowbit_twos_comp (n x : Nat) (hx0 : 0 < x) (hx : x < 2 ^ n) :
    lowbit (2 ^ n - x) = lowbit x := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hodd : x % 2 = 1
    · have h1 : x = 2 * (x / 2) + 1 := by omega
      have h2 : 2 ^ (n + 1) - x = 2 * (2 ^ n - 1 - x / 2) + 1 := by omega
      rw [h2, lowbit_odd]
      conv => rhs; rw [h1]
      exact (lowbit_odd (x / 2)).symm
    · have h1 : x = 2 * (x / 2) := by omega
      have h2 : 2 ^ (n + 1) - x = 2 * (2 ^ n - x / 2) := by omega
      rw [h2, lowbit_even]
      conv => rhs; rw [h1, lowbit_even]
      congr 1
      exact ih (x / 2) (by omega) (by omega)

/-- Single-step two's-complement conjugation: `-(D x) = U (-x)` and `-(U x) = D (-x)` mod `2^n`. -/
theorem fenwickD_twos_comp (n x : Nat) :
    (2 ^ n - fenwickD x % 2 ^ n) % 2 ^ n = fenwickU ((2 ^ n - x % 2 ^ n) % 2 ^ n) % 2 ^ n := by
  rw [← fenwickD_mod_pow n x]
  generalize hr_def : x % 2 ^ n = r
  have hr_lt : r < 2 ^ n := by rw [← hr_def]; exact Nat.mod_lt x (Nat.two_pow_pos n)
  by_cases hr0 : r = 0
  · subst hr0
    simp [fenwickD_zero, fenwickU_zero]
  · have hrpos : 0 < r := by omega
    have hneg_lt : 2 ^ n - r < 2 ^ n := by omega
    have hlb := lowbit_twos_comp n r hrpos hr_lt
    have hle := lowbit_le r
    have hD_lt : fenwickD r < 2 ^ n := by simp only [fenwickD]; omega
    rw [Nat.mod_eq_of_lt hneg_lt, Nat.mod_eq_of_lt hD_lt]
    simp only [fenwickD, fenwickU, hlb]
    have heq : 2 ^ n - (r - lowbit r) = (2 ^ n - r) + lowbit r := by omega
    rw [heq]

theorem fenwickU_twos_comp (n x : Nat) :
    (2 ^ n - fenwickU x % 2 ^ n) % 2 ^ n = fenwickD ((2 ^ n - x % 2 ^ n) % 2 ^ n) % 2 ^ n := by
  rw [← fenwickU_mod_pow n x]
  generalize hr_def : x % 2 ^ n = r
  have hr_lt : r < 2 ^ n := by rw [← hr_def]; exact Nat.mod_lt x (Nat.two_pow_pos n)
  by_cases hr0 : r = 0
  · subst hr0
    simp [fenwickD_zero, fenwickU_zero]
  · have hrpos : 0 < r := by omega
    have hneg_lt : 2 ^ n - r < 2 ^ n := by omega
    have hlb := lowbit_twos_comp n r hrpos hr_lt
    have hlb_le_neg : lowbit r ≤ 2 ^ n - r := by
      rw [← hlb]; exact lowbit_le (2 ^ n - r)
    rw [Nat.mod_eq_of_lt hneg_lt]
    simp only [fenwickD, fenwickU, hlb]
    by_cases htop : r + lowbit r = 2 ^ n
    · rw [htop, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
      have hzero : 2 ^ n - r - lowbit r = 0 := by omega
      rw [hzero, Nat.zero_mod]
    · have hU_lt : r + lowbit r < 2 ^ n := by omega
      rw [Nat.mod_eq_of_lt hU_lt]
      have heq : 2 ^ n - (r + lowbit r) = 2 ^ n - r - lowbit r := by omega
      rw [heq]

/-- THEOREM 5a (Exact Two's-Complement Word-Conjugation Duality, ∀ w ∈ {U, D}*, ∀ n, x : Nat):
    Negation mod 2^n conjugates every Fenwick word `w` into its dual word `dualWord w`. -/
theorem evalWord_twos_complement_duality (w : List FenwickOp) (n x : Nat) :
    (2 ^ n - evalWord w x % 2 ^ n) % 2 ^ n =
    evalWord (dualWord w) ((2 ^ n - x % 2 ^ n) % 2 ^ n) % 2 ^ n := by
  induction w with
  | nil =>
    simp only [evalWord, dualWord]
    rw [Nat.mod_mod]
  | cons g v ih =>
    cases g with
    | D =>
      simp only [evalWord, dualWord]
      rw [fenwickD_twos_comp, ih, fenwickU_mod_pow]
    | U =>
      simp only [evalWord, dualWord]
      rw [fenwickU_twos_comp, ih, fenwickD_mod_pow]

theorem popcount_zero : popcount 0 = 0 := by unfold popcount; simp

theorem popcount_odd (k : Nat) : popcount (2 * k + 1) = 1 + popcount k := by
  conv => lhs; unfold popcount
  have h2 : (2 * k + 1) % 2 = 1 := by omega
  have h3 : (2 * k + 1) / 2 = k := by omega
  simp [h2, h3]

theorem popcount_even (k : Nat) : popcount (2 * k) = popcount k := by
  cases k with
  | zero => simp [popcount_zero]
  | succ m =>
    conv => lhs; unfold popcount
    have h1 : 2 * (m + 1) ≠ 0 := by omega
    have h2 : 2 * (m + 1) % 2 = 0 := by omega
    have h3 : 2 * (m + 1) / 2 = m + 1 := by omega
    simp [h1, h2, h3]

theorem ctz_zero : ctz 0 = 0 := by unfold ctz; simp

theorem ctz_odd (k : Nat) : ctz (2 * k + 1) = 0 := by
  conv => lhs; unfold ctz
  have h2 : (2 * k + 1) % 2 = 1 := by omega
  simp [h2]

theorem ctz_even (k : Nat) (hk : 0 < k) : ctz (2 * k) = 1 + ctz k := by
  conv => lhs; unfold ctz
  have h1 : 2 * k ≠ 0 := by omega
  have h3 : 2 * k / 2 = k := by omega
  simp [h1, h3]

theorem popcount_fenwickD {x : Nat} (hx : 0 < x) : popcount (fenwickD x) + 1 = popcount x := by
  induction x using Nat.strongRecOn with
  | ind n ih =>
    by_cases hodd : n % 2 = 1
    · have hn : n = 2 * (n / 2) + 1 := by omega
      conv => lhs; rw [hn, fenwickD_odd, popcount_even]
      conv => rhs; rw [hn, popcount_odd]
      omega
    · have hn : n = 2 * (n / 2) := by omega
      have hdiv : 0 < n / 2 := by omega
      conv => lhs; rw [hn, fenwickD_even, popcount_even]
      conv => rhs; rw [hn, popcount_even]
      exact ih (n / 2) (by omega) hdiv

theorem popcount_twos_comp (n x : Nat) (hx0 : 0 < x) (hx : x < 2 ^ n) :
    popcount (2 ^ n - x) + popcount x = n + 1 - ctz x := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hodd : x % 2 = 1
    · have h1 : x = 2 * (x / 2) + 1 := by omega
      have h2 : 2 ^ (n + 1) - x = 2 * (2 ^ n - 1 - x / 2) + 1 := by omega
      have hctz : ctz x = 0 := by unfold ctz; simp [show x ≠ 0 by omega, hodd]
      rw [hctz, Nat.sub_zero]
      have hcomp : ∀ m a, a < 2 ^ m → popcount (2 ^ m - 1 - a) + popcount a = m := by
        intro m
        induction m with
        | zero =>
          intro a ha
          have ha0 : a = 0 := by omega
          subst ha0
          simp [popcount_zero]
        | succ m ihm =>
          intro a ha
          have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
          by_cases hao : a % 2 = 1
          · have ha1 : a = 2 * (a / 2) + 1 := by omega
            have hc1 : 2 ^ (m + 1) - 1 - a = 2 * (2 ^ m - 1 - a / 2) := by omega
            rw [hc1, popcount_even]
            conv => lhs; rhs; rw [ha1, popcount_odd]
            have := ihm (a / 2) (by omega); omega
          · have ha1 : a = 2 * (a / 2) := by omega
            have hc1 : 2 ^ (m + 1) - 1 - a = 2 * (2 ^ m - 1 - a / 2) + 1 := by omega
            rw [hc1, popcount_odd]
            conv => lhs; rhs; rw [ha1, popcount_even]
            have := ihm (a / 2) (by omega); omega
      rw [h2, popcount_odd]
      conv => lhs; rhs; rw [h1, popcount_odd]
      have := hcomp n (x / 2) (by omega)
      omega
    · have h1 : x = 2 * (x / 2) := by omega
      have h2 : 2 ^ (n + 1) - x = 2 * (2 ^ n - x / 2) := by omega
      have hctz : ctz x = 1 + ctz (x / 2) := by
        conv => lhs; unfold ctz
        simp [show x ≠ 0 by omega, hodd]
      have hctz_le : ctz (x / 2) < n := by
        have hlb_eq := lowbit_eq_pow_ctz (show 0 < x / 2 by omega)
        have hlb_le := lowbit_le (x / 2)
        by_cases hlt_n : ctz (x / 2) < n
        · exact hlt_n
        · exfalso
          have : 2 ^ n ≤ 2 ^ ctz (x / 2) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
      rw [h2, popcount_even]
      conv => lhs; rhs; rw [h1, popcount_even]
      rw [hctz]
      have hih := ih (x / 2) (by omega) (by omega)
      omega

/-- THEOREM 5b (Exact Fenwick Depth Duality on `[1, 2^n)`):
    For EVERY `n ≥ 1` and EVERY `0 < x < 2^n`:
    `depthU x (2^n) = popcount (2^n - x)` AND `depthU x (2^n) + popcount x = n + 1 - ctz x`. -/
theorem fenwick_depth_duality (n x : Nat) (hx0 : 0 < x) (hx : x < 2 ^ n) :
    depthU x (2 ^ n) = popcount (2 ^ n - x) ∧
    depthU x (2 ^ n) + popcount x = n + 1 - ctz x := by
  have hdep : depthU x (2 ^ n) = popcount (2 ^ n - x) := by
    generalize hd : 2 ^ n - x = dist
    induction dist using Nat.strongRecOn generalizing x with
    | ind d ih =>
      unfold depthU
      simp only [hx0, hx, and_self, ↓reduceDIte]
      have hlb := lowbit_twos_comp n x hx0 hx
      have hlb_pos := lowbit_pos hx0
      have hlb_le : lowbit x ≤ 2 ^ n - x := by rw [← hlb]; exact lowbit_le _
      have hUx_le : fenwickU x ≤ 2 ^ n := by simp only [fenwickU]; omega
      by_cases htop : fenwickU x = 2 ^ n
      · rw [htop]
        have hbase : depthU (2 ^ n) (2 ^ n) = 0 := by unfold depthU; simp
        rw [hbase, ← hd]
        have hrem : 2 ^ n - x = lowbit x := by simp only [fenwickU] at htop; omega
        rw [hrem, lowbit_eq_pow_ctz hx0]
        have hpc_pow : ∀ k, popcount (2 ^ k) = 1 := by
          intro k
          induction k with
          | zero => unfold popcount; simp [popcount_zero]
          | succ k ihk => rw [Nat.pow_succ, Nat.mul_comm, popcount_even, ihk]
        rw [hpc_pow]
      · have hUx_lt : fenwickU x < 2 ^ n := by omega
        have hUx_pos : 0 < fenwickU x := by simp only [fenwickU]; omega
        have hdist_lt : 2 ^ n - fenwickU x < d := by simp only [fenwickU]; omega
        rw [ih (2 ^ n - fenwickU x) hdist_lt (fenwickU x) hUx_pos hUx_lt rfl, ← hd]
        have hsub : 2 ^ n - fenwickU x = fenwickD (2 ^ n - x) := by
          simp only [fenwickU, fenwickD, hlb]; omega
        rw [hsub]
        have hpc := popcount_fenwickD (show 0 < 2 ^ n - x by omega)
        omega
  exact ⟨hdep, by rw [hdep]; exact popcount_twos_comp n x hx0 hx⟩

-- ============================================================================
-- SECTION 7: THEOREM 6 — Sharpness Counterexamples, Non-Vacuity & Axiom Receipts
-- ============================================================================

theorem lowbit_3 : lowbit 3 = 1 := lowbit_odd 1

theorem lowbit_4 : lowbit 4 = 4 := by
  have h1 : lowbit 1 = 1 := lowbit_odd 0
  have h2 : lowbit 2 = 2 := by change lowbit (2 * 1) = 2; rw [lowbit_even, h1]
  change lowbit (2 * 2) = 4; rw [lowbit_even, h2]

theorem lowbit_6 : lowbit 6 = 2 := by
  change lowbit (2 * 3) = 2; rw [lowbit_even, lowbit_3]

theorem fenwickU_3 : fenwickU 3 = 4 := by simp [fenwickU, lowbit_3]

theorem fenwickU_4 : fenwickU 4 = 8 := by simp [fenwickU, lowbit_4]

theorem fenwickD_6 : fenwickD 6 = 4 := by simp [fenwickD, lowbit_6]

/-- THEOREM 6a (Sharpness of Multiplier c = ±1):
    For `T_3(x) = x + 3 * lowbit(x)`, the Universal Fenwick Ancestor-Spine Collapse
    AND Bitwise Projection Laws BREAK already at `x = 3` (`T_3(3) = 6`). -/
theorem sharpness_T3_breaks_spines :
    jumpT3 3 = 6 ∧
    (∀ m : Nat, iterN fenwickD m 3 ≠ 6) ∧
    (∀ m : Nat, iterN fenwickU m 3 ≠ 6) ∧
    (jumpT3 3 &&& 3 ≠ fenwickD (jumpT3 3)) := by
  have hT3 : jumpT3 3 = 6 := by simp [jumpT3, lowbit_3]
  refine ⟨hT3, ?_, ?_, ?_⟩
  · intro m
    have hle : ∀ k, iterN fenwickD k 3 ≤ 3 := by
      intro k
      induction k with
      | zero => exact Nat.le_refl 3
      | succ k ih => exact Nat.le_trans (fenwickD_le _) ih
    have := hle m; omega
  · intro m
    cases m with
    | zero => simp [iterN]
    | succ m1 =>
      cases m1 with
      | zero => simp [iterN, fenwickU_3]
      | succ m2 =>
        have hge : ∀ k, 8 ≤ iterN fenwickU (k + 2) 3 := by
          intro k
          induction k with
          | zero => simp [iterN, fenwickU_3, fenwickU_4]
          | succ k ih =>
            have hstep : iterN fenwickU (k + 1 + 2) 3 = fenwickU (iterN fenwickU (k + 2) 3) := rfl
            rw [hstep]
            simp only [fenwickU]
            omega
        have h8 := hge m2
        intro h6
        have h6' : iterN fenwickU (m2 + 2) 3 = 6 := h6
        omega
  · rw [hT3, fenwickD_6]; decide

/-- THEOREM 6b (Sharpness of Unbounded Nat for Free Monoid):
    On EVERY finite bit-width `w ≥ 2`, the Fenwick monoid `<U_w, D_w>` is NOT free:
    the distinct length-`w` words `U^(w-1) D` and `U^w` collapse identically to `0` mod `2^w`. -/
theorem sharpness_finite_width_not_free (w : Nat) (hw : 2 ≤ w) :
    ∃ w1 w2 : List FenwickOp,
      w1 ≠ w2 ∧ w1.length = w ∧ w2.length = w ∧
      ∀ x : Nat, evalWord w1 x % 2 ^ w = evalWord w2 x % 2 ^ w := by
  let w1 : List FenwickOp := List.replicate (w - 1) .U ++ [.D]
  let w2 : List FenwickOp := List.replicate w .U
  have hlen1 : w1.length = w := by simp [w1]; omega
  have hlen2 : w2.length = w := by simp [w2]
  have hne : w1 ≠ w2 := by
    intro heq
    have hlast := congrArg List.getLast? heq
    have hl1 : w1.getLast? = some .D := by
      simp only [w1, List.getLast?_append, List.getLast?_singleton]; rfl
    have hl2 : w2.getLast? = some .U := by
      have hwpos : w = (w - 1) + 1 := by omega
      have hrep : w2 = List.replicate (w - 1) .U ++ [.U] := by
        simp only [w2]; conv => lhs; rw [hwpos, List.replicate_succ']
      rw [hrep]
      simp only [List.getLast?_append, List.getLast?_singleton]; rfl
    rw [hl1, hl2] at hlast
    cases hlast
  refine ⟨w1, w2, hne, hlen1, hlen2, ?_⟩
  intro x
  rw [evalWord_mod_zero_of_len_ge w w1 (by omega) x,
      evalWord_mod_zero_of_len_ge w w2 (by omega) x]

-- ============================================================================
-- KERNEL-CHECKED NON-VACUITY WITNESSES
-- ============================================================================

-- Small concrete evaluation helper for `lowbit` on explicit literals

theorem lowbit_eval_even {n k : Nat} (h : n = 2 * k) : lowbit n = 2 * lowbit k := by
  rw [h, lowbit_even]

theorem lowbit_eval_odd {n k : Nat} (h : n = 2 * k + 1) : lowbit n = 1 := by
  rw [h, lowbit_odd]

/-- Non-vacuity witness 1: Concrete compilation, state count, and evaluation of `UDUD` on `x = 173`. -/
example :
    compileSpec [.U, .D, .U, .D] = ([true, true, false, true, false], true) ∧
    (compileSpec [.U, .D, .U, .D]).1.length + 1 = 6 ∧
    evalWord [.U, .D, .U, .D] 173 = 192 ∧
    iterN fenwickU 3 173 = 192 ∧
    (192 &&& 173) = fenwickD 192 := by
  have lb173 : lowbit 173 = 1 := lowbit_eval_odd (k := 86) rfl
  have lb172 : lowbit 172 = 4 := by
    rw [lowbit_eval_even (k := 86) rfl, lowbit_eval_even (k := 43) rfl, lowbit_eval_odd (k := 21) rfl]
  have lb174 : lowbit 174 = 2 := by
    rw [lowbit_eval_even (k := 87) rfl, lowbit_eval_odd (k := 43) rfl]
  have lb176 : lowbit 176 = 16 := by
    rw [lowbit_eval_even (k := 88) rfl, lowbit_eval_even (k := 44) rfl,
        lowbit_eval_even (k := 22) rfl, lowbit_eval_even (k := 11) rfl, lowbit_eval_odd (k := 5) rfl]
  have lb160 : lowbit 160 = 32 := by
    rw [lowbit_eval_even (k := 80) rfl, lowbit_eval_even (k := 40) rfl,
        lowbit_eval_even (k := 20) rfl, lowbit_eval_even (k := 10) rfl,
        lowbit_eval_even (k := 5) rfl, lowbit_eval_odd (k := 2) rfl]
  have lb192 : lowbit 192 = 64 := by
    rw [lowbit_eval_even (k := 96) rfl, lowbit_eval_even (k := 48) rfl,
        lowbit_eval_even (k := 24) rfl, lowbit_eval_even (k := 12) rfl,
        lowbit_eval_even (k := 6) rfl, lowbit_eval_even (k := 3) rfl, lowbit_eval_odd (k := 1) rfl]
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · simp [evalWord, fenwickD, fenwickU, lb173, lb172, lb176, lb160]
  · simp [iterN, fenwickU, lb173, lb174, lb176]
  · simp [fenwickD, lb192]

/-- Non-vacuity witness 2: Concrete separating witness for `UD ≠ DU` (`x = fromBits [true, false] + 4 = 5`). -/
example :
    evalWord [.U, .D] 5 ≠ evalWord [.D, .U] 5 := by
  have lb5 : lowbit 5 = 1 := lowbit_eval_odd (k := 2) rfl
  have lb4 : lowbit 4 = 4 := lowbit_4
  have lb6 : lowbit 6 = 2 := lowbit_6
  simp [evalWord, fenwickU, fenwickD, lb5, lb4, lb6]

/-- Non-vacuity witness 3: Concrete exact cardinality `2^4 = 16` for `BitVec 4`. -/
example : (finiteMonoidReps 4).length = 16 := by
  decide

/-- Non-vacuity witness 4: Concrete depth duality at `n = 8, x = 172` (`ctz 172 = 2`, `popcount 172 = 4`, `depthU = 3`). -/
example :
    depthU 172 (2 ^ 8) = 3 ∧
    popcount (2 ^ 8 - 172) = 3 ∧
    depthU 172 (2 ^ 8) + popcount 172 = 8 + 1 - ctz 172 := by
  have hdual := fenwick_depth_duality 8 172 (by omega) (by decide)
  have hpc84 : popcount (2 ^ 8 - 172) = 3 := by
    change popcount 84 = 3
    rw [show (84 : Nat) = 2 * 42 from rfl, popcount_even,
        show (42 : Nat) = 2 * 21 from rfl, popcount_even,
        show (21 : Nat) = 2 * 10 + 1 from rfl, popcount_odd,
        show (10 : Nat) = 2 * 5 from rfl, popcount_even,
        show (5 : Nat) = 2 * 2 + 1 from rfl, popcount_odd,
        show (2 : Nat) = 2 * 1 from rfl, popcount_even,
        show (1 : Nat) = 2 * 0 + 1 from rfl, popcount_odd, popcount_zero]
  exact ⟨hdual.1.trans hpc84, hpc84, hdual.2⟩

/-- Non-vacuity witness 5: Concrete `BitVec 8` hardware `lowbit` identity at `x = 172#8`. -/
example : ((172#8) &&& (-(172#8))).toNat = lowbit (172#8).toNat :=
  lowbit_bitvec_eq 8 (172#8)

end FenwickTransducer
