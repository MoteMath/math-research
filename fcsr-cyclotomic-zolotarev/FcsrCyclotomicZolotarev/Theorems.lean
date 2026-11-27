/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FcsrCyclotomicZolotarev.Defs

/-
  Pure-Silicon 2-Adic FCSR Engine — Standalone Lean 4.34.1 Formalization
  Author: dynsil-7 (Thread 2: Bitwise Dynamics, T-Functions & Reversible Silicon Orbit Mechanisms)

  Zero external dependencies (pure Lean 4 core only). Zero `sorry`, zero custom axioms.
-/


-- ============================================================================
-- Section 0: Core Exact-Binary Helpers (Bit Extraction & Finite Sums)
-- ============================================================================

namespace SiliconFCSR

theorem bit_lt_two (n i : Nat) : bit n i < 2 := Nat.mod_lt _ (by omega)

theorem bit_le_one (n i : Nat) : bit n i ≤ 1 := by
  have := bit_lt_two n i; omega

theorem bit_zero (i : Nat) : bit 0 i = 0 := by
  simp [bit]

theorem bit_zero_idx (n : Nat) : bit n 0 = n % 2 := by
  simp [bit]

theorem bit_div_two (n i : Nat) : bit (n / 2) i = bit n (i + 1) := by
  simp [bit, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem mod_mul_eq (n a b : Nat) : n % (a * b) = n % a + a * ((n / a) % b) := by
  by_cases ha : a = 0
  · subst ha; simp
  · by_cases hb : b = 0
    · subst hb; simp; have := Nat.div_add_mod n a; omega
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
      have h1 := Nat.div_add_mod n a
      have h2 := Nat.div_add_mod (n / a) b
      have h3 : n = a * b * (n / a / b) + (n % a + a * ((n / a) % b)) := by
        calc n = a * (n / a) + n % a := h1.symm
          _ = a * (b * (n / a / b) + (n / a) % b) + n % a := by rw [h2]
          _ = a * b * (n / a / b) + (n % a + a * ((n / a) % b)) := by
              rw [Nat.mul_add, Nat.mul_assoc]; omega
      have hlt : n % a + a * ((n / a) % b) < a * b := by
        have r1 : n % a < a := Nat.mod_lt n ha_pos
        have r2 : (n / a) % b < b := Nat.mod_lt (n / a) hb_pos
        have hle : (n / a) % b + 1 ≤ b := r2
        have hmul : a * ((n / a) % b + 1) ≤ a * b := Nat.mul_le_mul_left a hle
        rw [Nat.mul_add, Nat.mul_one] at hmul
        omega
      conv => lhs; rw [h3]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem bit_mod_pow_of_lt (n k i : Nat) (h : i < k) :
    bit (n % 2 ^ k) i = bit n i := by
  unfold bit
  have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt h)]
  have h2dvd : 2 ∣ 2 ^ (k - i) := ⟨2 ^ (k - i - 1), pow2_pred_mul (k - i) (by omega)⟩
  have h1 : n % (2 ^ i * 2 ^ (k - i)) / 2 ^ i = (n / 2 ^ i) % 2 ^ (k - i) := by
    rw [Nat.mod_mul_right_div_self]
  rw [hpow, h1]
  exact Nat.mod_mod_of_dvd _ h2dvd

theorem mod_pow_succ (n k : Nat) :
    n % 2 ^ (k + 1) = n % 2 ^ k + bit n k * 2 ^ k := by
  unfold bit
  rw [Nat.pow_succ, mod_mul_eq, Nat.mul_comm (2 ^ k)]

theorem div_two_mod_pow (n k : Nat) :
    2 * ((n / 2) % 2 ^ k) + n % 2 = n % 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, mod_mul_eq]
  omega

theorem sumNat_congr {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumInt_congr {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumNat_add (n : Nat) (f g : Nat → Nat) :
    sumNat n (fun i => f i + g i) = sumNat n f + sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, ih]; omega

theorem sumInt_add (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_sub (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i - g i) = sumInt n f - sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumInt n (fun i => c * f i) = c * sumInt n f := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih => simp only [sumInt, ih, Int.mul_add]

theorem sumInt_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumInt n (fun i => f i * c) = sumInt n f * c := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih => simp only [sumInt, ih, Int.add_mul]

theorem sumNat_mul_left (n : Nat) (c : Nat) (f : Nat → Nat) :
    sumNat n (fun i => c * f i) = c * sumNat n f := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih => simp only [sumNat, ih, Nat.mul_add]

theorem sumNat_mul_right (n : Nat) (f : Nat → Nat) (c : Nat) :
    sumNat n (fun i => f i * c) = sumNat n f * c := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih => simp only [sumNat, ih, Nat.add_mul]

theorem sumInt_ofNat (n : Nat) (f : Nat → Nat) :
    sumInt n (fun i => (f i : Int)) = (sumNat n f : Int) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, sumNat, ih, Int.natCast_add]

theorem sumInt_const (n : Nat) (c : Int) :
    sumInt n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt, ih]
    have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [this, Int.add_mul, Int.one_mul]

theorem sumNat_const (n : Nat) (c : Nat) :
    sumNat n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih => simp only [sumNat, ih, Nat.succ_mul]

theorem sumInt_nonneg (n : Nat) (f : Nat → Int) (h : ∀ i, i < n → 0 ≤ f i) :
    0 ≤ sumInt n f := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h k (by omega)
    omega

theorem sumInt_lt (n : Nat) (f g : Nat → Int) (hn : 0 < n)
    (h : ∀ i, i < n → f i < g i) : sumInt n f < sumInt n g := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [sumInt]
    cases k with
    | zero =>
      simp only [sumInt, Int.zero_add]
      exact h 0 (by omega)
    | succ m =>
      have h1 := ih (by omega) (fun i hi => h i (by omega))
      have h2 := h (m + 1) (by omega)
      omega

theorem sumInt_shift_one (n : Nat) (f : Nat → Int) (hper : f n = f 0) :
    sumInt n (fun i => f (i + 1)) = sumInt n f := by
  have aux : ∀ m, sumInt m (fun i => f (i + 1)) + f 0 = sumInt m f + f m := by
    intro m
    induction m with
    | zero => simp [sumInt]
    | succ k ih => simp only [sumInt]; omega
  have h := aux n
  omega

theorem sumInt_shift (n d : Nat) (f : Nat → Int) (hper : ∀ t, f (t + n) = f t) :
    sumInt n (fun i => f (i + d)) = sumInt n f := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : sumInt n (fun i => f (i + (d + 1))) = sumInt n (fun i => f ((i + 1) + d)) := by
      apply sumInt_congr; intro i _; congr 1; omega
    rw [h1]
    have h2 : sumInt n (fun i => f ((i + 1) + d)) = sumInt n (fun i => f (i + d)) := by
      apply sumInt_shift_one n (fun i => f (i + d))
      have := hper d
      simpa [Nat.add_comm] using this
    rw [h2, ih]

theorem sumInt_swap (a b : Nat) (f : Nat → Nat → Int) :
    sumInt a (fun i => sumInt b (fun j => f i j)) =
    sumInt b (fun j => sumInt a (fun i => f i j)) := by
  induction a with
  | zero =>
    simp only [sumInt]
    induction b with
    | zero => rfl
    | succ m ih => simp only [sumInt, ← ih]; omega
  | succ k ih =>
    simp only [sumInt, ih, ← sumInt_add]

theorem sumInt_split (a b : Nat) (f : Nat → Int) :
    sumInt (a + b) f = sumInt a f + sumInt b (fun i => f (a + i)) := by
  induction b with
  | zero => simp [sumInt]
  | succ k ih =>
    rw [← Nat.add_assoc]
    simp only [sumInt, ih]
    omega

theorem sumInt_mul_split (d k : Nat) (f : Nat → Int) :
    sumInt (d * k) f = sumInt d (fun j => sumInt k (fun t => f (j * k + t))) := by
  induction d with
  | zero => simp [sumInt]
  | succ m ih =>
    rw [Nat.succ_mul, sumInt_split, ih]
    rfl

theorem sum_bits_mod (n k : Nat) :
    sumNat k (fun j => bit n j * 2 ^ j) = n % 2 ^ k := by
  induction k with
  | zero => simp [sumNat, Nat.mod_one]
  | succ m ih =>
    simp only [sumNat, ih, mod_pow_succ]

theorem sum_bits_eq (n k : Nat) (h : n < 2 ^ k) :
    sumNat k (fun j => bit n j * 2 ^ j) = n := by
  rw [sum_bits_mod, Nat.mod_eq_of_lt h]

namespace FCSRSpec

theorem q_ge_three (spec : FCSRSpec) : 3 ≤ spec.q := by
  have := spec.hc_ge2; unfold q; omega

theorem q_odd (spec : FCSRSpec) : spec.q % 2 = 1 := by
  have := spec.hc_ge2; unfold q; omega

theorem q_add_one (spec : FCSRSpec) : spec.q + 1 = 2 * spec.c := by
  have := spec.hc_ge2; unfold q; omega

theorem qInt_pos (spec : FCSRSpec) : 0 < spec.qInt := by
  have := spec.q_ge_three; unfold qInt; omega

theorem tap_msb (spec : FCSRSpec) : bit spec.c (spec.r - 1) = 1 := by
  unfold bit
  have h1 : spec.c / 2 ^ (spec.r - 1) = 1 := by
    have hlo := spec.hc_lo
    have hhi : spec.c < 2 * 2 ^ (spec.r - 1) := by
      rw [← spec.pow_r_eq]; exact spec.hc_hi
    have hpos : 0 < 2 ^ (spec.r - 1) := Nat.pow_pos (by omega)
    have hge : 1 ≤ spec.c / 2 ^ (spec.r - 1) := (Nat.le_div_iff_mul_le hpos).2 (by omega)
    have hlt : spec.c / 2 ^ (spec.r - 1) < 2 := (Nat.div_lt_iff_lt_mul hpos).2 (by omega)
    omega
  rw [h1]

theorem tapWeight_pos (spec : FCSRSpec) : 1 ≤ spec.tapWeight := by
  unfold tapWeight
  have hsplit : spec.r = (spec.r - 1) + 1 := by have := spec.hr; omega
  have h : sumNat spec.r (fun j => bit spec.c j) =
      sumNat (spec.r - 1) (fun j => bit spec.c j) + bit spec.c (spec.r - 1) := by
    conv => lhs; rw [hsplit]
    rfl
  rw [h, spec.tap_msb]
  omega

theorem tapWeightedSum_eq (spec : FCSRSpec) :
    sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1)) = 2 * spec.c := by
  have h1 : sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1)) =
      sumNat spec.r (fun j => (bit spec.c j * 2 ^ j) * 2) := by
    apply sumNat_congr; intro j _; rw [Nat.pow_succ, Nat.mul_assoc]
  rw [h1, sumNat_mul_right, sum_bits_eq spec.c spec.r spec.hc_hi, Nat.mul_comm]

theorem tapWeightedSum_eq_q_add_one (spec : FCSRSpec) :
    sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1)) = spec.q + 1 := by
  rw [spec.tapWeightedSum_eq, spec.q_add_one]

/-- Compute binary bit-length of a positive natural number. -/
def bitLen : Nat → Nat
  | 0 => 0
  | n + 1 => bitLen ((n + 1) / 2) + 1

theorem bitLen_pos (n : Nat) (h : 1 ≤ n) : 1 ≤ bitLen n := by
  cases n with
  | zero => omega
  | succ m => unfold bitLen; omega

theorem bitLen_bounds (n : Nat) (h : 1 ≤ n) :
    2 ^ (bitLen n - 1) ≤ n ∧ n < 2 ^ bitLen n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      unfold bitLen
      by_cases h1 : (m + 1) / 2 = 0
      · have hm : m = 0 := by omega
        subst hm
        simp [bitLen]
      · have hge : 1 ≤ (m + 1) / 2 := by omega
        have hlt : (m + 1) / 2 < m + 1 := by omega
        have ⟨hlo, hhi⟩ := ih ((m + 1) / 2) hlt hge
        have hbl : 1 ≤ bitLen ((m + 1) / 2) := bitLen_pos _ hge
        have hp1 : 2 ^ bitLen ((m + 1) / 2) = 2 * 2 ^ (bitLen ((m + 1) / 2) - 1) :=
          pow2_pred_mul _ hbl
        have hp2 : 2 ^ (bitLen ((m + 1) / 2) + 1) = 2 * 2 ^ bitLen ((m + 1) / 2) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        constructor
        · simp only [Nat.add_sub_cancel]; omega
        · omega

/-- Construct an `FCSRSpec` directly from ANY odd integer `q ≥ 3`. -/
def ofOdd (q : Nat) (hq_ge : 3 ≤ q) (hq_odd : q % 2 = 1) : FCSRSpec :=
  let c := (q + 1) / 2
  have hc_ge2 : 2 ≤ c := by omega
  have hc_ge1 : 1 ≤ c := by omega
  have hb := bitLen_bounds c hc_ge1
  { c := c
    r := bitLen c
    hr := bitLen_pos c hc_ge1
    hc_lo := hb.1
    hc_hi := hb.2
    hc_ge2 := hc_ge2 }

theorem ofOdd_q (q : Nat) (hq_ge : 3 ≤ q) (hq_odd : q % 2 = 1) :
    (ofOdd q hq_ge hq_odd).q = q := by
  unfold ofOdd FCSRSpec.q
  dsimp only
  omega


-- ============================================================================
-- Hardware FCSR State, Transition, and Exact 2-Adic Potential
-- ============================================================================

end FCSRSpec

theorem FCSRState.ext {spec : FCSRSpec} {s1 s2 : FCSRState spec}
    (h1 : s1.reg = s2.reg) (h2 : s1.carry = s2.carry) : s1 = s2 := by
  cases s1; cases s2; cases h1; cases h2; rfl

namespace FCSRSpec

theorem outBit_lt_two {spec : FCSRSpec} (s : FCSRState spec) : outBit s < 2 :=
  Nat.mod_lt _ (by omega)

theorem stepN_zero (spec : FCSRSpec) (s : FCSRState spec) :
    spec.stepN 0 s = s := rfl

theorem stepN_succ (spec : FCSRSpec) (n : Nat) (s : FCSRState spec) :
    spec.stepN (n + 1) s = spec.stepN n (spec.step s) := rfl

theorem stepN_add (spec : FCSRSpec) (a b : Nat) (s : FCSRState spec) :
    spec.stepN (a + b) s = spec.stepN b (spec.stepN a s) := by
  induction a generalizing s with
  | zero => simp [stepN]
  | succ k ih =>
    rw [Nat.succ_add, stepN_succ, stepN_succ, ih]

theorem stepN_succ_right (spec : FCSRSpec) (n : Nat) (s : FCSRState spec) :
    spec.stepN (n + 1) s = spec.step (spec.stepN n s) := by
  rw [stepN_add]; rfl

theorem divStep_eq (q : Nat) (hq_odd : q % 2 = 1) (p : Int) :
    p = (q : Int) * (p % 2) + 2 * divStep q p := by
  unfold divStep
  have hp : p % 2 = 0 ∨ p % 2 = 1 := by omega
  rcases hp with h0 | h1
  · rw [h0]; omega
  · rw [h1]; omega

/-- Key per-tap modular identity for one hardware clock tick. -/
private theorem step_reg_mod_pow (spec : FCSRSpec) (s : FCSRState spec)
    (k : Nat) (hk : k ≤ spec.r - 1) :
    2 * ((spec.step s).reg % 2 ^ k) + s.reg % 2 =
    s.reg % 2 ^ k + bit s.reg k * 2 ^ k := by
  have hnew : (spec.step s).reg = s.reg / 2 + ((spec.sigma s) % 2).toNat * 2 ^ (spec.r - 1) := rfl
  have hdvd : 2 ^ k ∣ 2 ^ (spec.r - 1) := by
    have : 2 ^ (spec.r - 1) = 2 ^ k * 2 ^ (spec.r - 1 - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hk]
    exact ⟨2 ^ (spec.r - 1 - k), this⟩
  have hmod : (spec.step s).reg % 2 ^ k = (s.reg / 2) % 2 ^ k := by
    rw [hnew]
    rcases hdvd with ⟨m, hm⟩
    rw [hm, ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ k), Nat.mul_assoc]
    rw [Nat.add_mul_mod_self_left]
  rw [hmod, div_two_mod_pow, mod_pow_succ]

/-- ENGINE THEOREM 1A: Exact one-step 2-adic potential invariant (holds for ALL states). -/
theorem potential_step (spec : FCSRSpec) (s : FCSRState spec) :
    spec.potential s = spec.qInt * (outBit s : Int) + 2 * spec.potential (spec.step s) := by
  have hsum :
      2 * sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * ((spec.step s).reg % 2 ^ (spec.r - 1 - j)))
      + sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1)) * (s.reg % 2)
      = sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (s.reg % 2 ^ (spec.r - 1 - j)))
      + spec.tapDot s.reg * 2 ^ spec.r := by
    rw [← sumNat_mul_left, ← sumNat_mul_right, ← sumNat_add]
    unfold tapDot
    rw [← sumNat_mul_right, ← sumNat_add]
    apply sumNat_congr
    intro j hj
    have hk : spec.r - 1 - j ≤ spec.r - 1 := by omega
    have hpow : 2 ^ (j + 1) * 2 ^ (spec.r - 1 - j) = 2 ^ spec.r := by
      rw [← Nat.pow_add]; congr 1; omega
    have hstep := step_reg_mod_pow spec s (spec.r - 1 - j) hk
    have hm := congrArg (fun x => bit spec.c j * 2 ^ (j + 1) * x) hstep
    simp only [Nat.mul_add] at hm
    calc 2 * (bit spec.c j * 2 ^ (j + 1) * ((spec.step s).reg % 2 ^ (spec.r - 1 - j)))
          + bit spec.c j * 2 ^ (j + 1) * (s.reg % 2)
        = bit spec.c j * 2 ^ (j + 1) * (2 * ((spec.step s).reg % 2 ^ (spec.r - 1 - j)))
          + bit spec.c j * 2 ^ (j + 1) * (s.reg % 2) := by
            congr 1; rw [Nat.mul_left_comm]
      _ = bit spec.c j * 2 ^ (j + 1) * (s.reg % 2 ^ (spec.r - 1 - j))
          + bit spec.c j * 2 ^ (j + 1) * (bit s.reg (spec.r - 1 - j) * 2 ^ (spec.r - 1 - j)) := hm
      _ = bit spec.c j * 2 ^ (j + 1) * (s.reg % 2 ^ (spec.r - 1 - j))
          + bit spec.c j * bit s.reg (spec.r - 1 - j) * 2 ^ spec.r := by
            congr 1
            calc bit spec.c j * 2 ^ (j + 1) * (bit s.reg (spec.r - 1 - j) * 2 ^ (spec.r - 1 - j))
                = bit spec.c j * bit s.reg (spec.r - 1 - j) * (2 ^ (j + 1) * 2 ^ (spec.r - 1 - j)) := by
                  simp only [Nat.mul_assoc]; congr 1; rw [Nat.mul_left_comm]
              _ = bit spec.c j * bit s.reg (spec.r - 1 - j) * 2 ^ spec.r := by rw [hpow]
  rw [spec.tapWeightedSum_eq_q_add_one] at hsum
  have hsg : s.carry + (spec.tapDot s.reg : Int) =
      2 * (spec.step s).carry + (((spec.sigma s) % 2).toNat : Int) := by
    have hc : (spec.step s).carry = (spec.sigma s) / 2 := rfl
    have hdef : spec.sigma s = s.carry + (spec.tapDot s.reg : Int) := rfl
    omega
  have hreg_eq : 2 * (spec.step s).reg + s.reg % 2 =
      s.reg + ((spec.sigma s) % 2).toNat * 2 ^ spec.r := by
    have hnew : (spec.step s).reg = s.reg / 2 + ((spec.sigma s) % 2).toNat * 2 ^ (spec.r - 1) := rfl
    have hpr := spec.pow_r_eq
    have hdm := Nat.div_add_mod s.reg 2
    rw [hnew, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (((spec.sigma s) % 2).toNat),
        Nat.mul_assoc, ← hpr]
    omega
  unfold potential potentialZero outBit qInt
  rw [sumInt_ofNat, sumInt_ofNat]
  have hsumI : 2 * (sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * ((spec.step s).reg % 2 ^ (spec.r - 1 - j))) : Int)
      + ((spec.q : Int) + 1) * ((s.reg % 2 : Nat) : Int)
      = (sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (s.reg % 2 ^ (spec.r - 1 - j))) : Int)
      + (spec.tapDot s.reg : Int) * ((2 ^ spec.r : Nat) : Int) := by
    have := congrArg (fun x : Nat => (x : Int)) hsum
    simpa [Int.natCast_add, Int.natCast_mul] using this
  have hqmul : ((spec.q : Int) + 1) * ((s.reg % 2 : Nat) : Int) =
      (spec.q : Int) * ((s.reg % 2 : Nat) : Int) + ((s.reg % 2 : Nat) : Int) := by
    rw [Int.add_mul, Int.one_mul]
  rw [hqmul] at hsumI
  have hregI : 2 * ((spec.step s).reg : Int) + ((s.reg % 2 : Nat) : Int) =
      (s.reg : Int) + (((spec.sigma s) % 2).toNat : Int) * ((2 ^ spec.r : Nat) : Int) := by
    have := congrArg (fun x : Nat => (x : Int)) hreg_eq
    simpa [Int.natCast_add, Int.natCast_mul] using this
  have hcarryI : s.carry * ((2 ^ spec.r : Nat) : Int) + (spec.tapDot s.reg : Int) * ((2 ^ spec.r : Nat) : Int) =
      2 * ((spec.step s).carry * ((2 ^ spec.r : Nat) : Int)) + (((spec.sigma s) % 2).toNat : Int) * ((2 ^ spec.r : Nat) : Int) := by
    have hm := congrArg (fun x => x * ((2 ^ spec.r : Nat) : Int)) hsg
    simpa [Int.add_mul, Int.mul_assoc] using hm
  omega

theorem outBit_eq_potential_emod (spec : FCSRSpec) (s : FCSRState spec) :
    (outBit s : Int) = spec.potential s % 2 := by
  have h := spec.potential_step s
  have hodd := spec.q_odd
  have hob := outBit_lt_two s
  unfold qInt at h
  have hbit : outBit s = 0 ∨ outBit s = 1 := by omega
  rcases hbit with h0 | h1
  · rw [h0] at h ⊢; omega
  · rw [h1] at h ⊢; omega

theorem potential_step_eq_divStep (spec : FCSRSpec) (s : FCSRState spec) :
    spec.potential (spec.step s) = divStep spec.q (spec.potential s) := by
  have h1 := spec.potential_step s
  have h2 := divStep_eq spec.q spec.q_odd (spec.potential s)
  have h3 := spec.outBit_eq_potential_emod s
  unfold qInt at h1
  rw [h3] at h1
  omega

theorem potential_stepN_eq_divStepN (spec : FCSRSpec) (n : Nat) (s : FCSRState spec) :
    spec.potential (spec.stepN n s) = divStepN spec.q n (spec.potential s) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [stepN_succ, ih, spec.potential_step_eq_divStep]
    rfl

theorem wordRun_lt (spec : FCSRSpec) (s : FCSRState spec) (n : Nat) :
    spec.wordRun s n < 2 ^ n := by
  unfold wordRun
  have hle : sumNat n (fun t => outBit (spec.stepN t s) * 2 ^ t) ≤
      sumNat n (fun t => 2 ^ t) := by
    apply sumNat_le_sumNat; intro t _
    have := outBit_lt_two (spec.stepN t s)
    calc outBit (spec.stepN t s) * 2 ^ t ≤ 1 * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ t := Nat.one_mul _
  have := sum_pow2_eq n
  omega

/-- ENGINE THEOREM 1B: Exact 2-adic rational representation for ALL `n ∈ ℕ` (no limits). -/
theorem word_representation_exact (spec : FCSRSpec) (s : FCSRState spec) (n : Nat) :
    spec.qInt * (spec.wordRun s n : Int) + ((2 ^ n : Nat) : Int) * spec.potential (spec.stepN n s)
    = spec.potential s := by
  induction n with
  | zero =>
    simp [wordRun, sumNat, stepN]
  | succ k ih =>
    have hstep := spec.potential_step (spec.stepN k s)
    rw [← stepN_succ_right] at hstep
    unfold wordRun at ih ⊢
    simp only [sumNat, Int.natCast_add, Int.natCast_mul]
    rw [Int.mul_add]
    have hpow : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) * 2 := by
      rw [Nat.pow_succ]; exact_mod_cast rfl
    rw [hpow, Int.mul_assoc]
    have hmul := congrArg (fun x => ((2 ^ k : Nat) : Int) * x) hstep
    rw [Int.mul_add] at hmul
    have hcomm : spec.qInt * ((outBit (spec.stepN k s) : Int) * ((2 ^ k : Nat) : Int)) =
        ((2 ^ k : Nat) : Int) * (spec.qInt * (outBit (spec.stepN k s) : Int)) := by
      rw [Int.mul_comm ((outBit (spec.stepN k s) : Int)), ← Int.mul_assoc, Int.mul_comm spec.qInt, Int.mul_assoc]
    rw [hcomm]
    omega

/-- Corollary: `q * W_n(s) ≡ P_q(s) (mod 2^n)` for every `n ∈ ℕ`. -/
theorem word_representation_mod_pow2 (spec : FCSRSpec) (s : FCSRState spec) (n : Nat) :
    (spec.qInt * (spec.wordRun s n : Int)) % ((2 ^ n : Nat) : Int) =
    spec.potential s % ((2 ^ n : Nat) : Int) := by
  have h := spec.word_representation_exact s n
  rw [← h, Int.add_mul_emod_self_left]

-- ============================================================================
-- Section 1C: Global Bijection `FCSRState spec ≃ ℤ` & Periodic Core Reversibility
-- ============================================================================

/-- Register bit `j` equals the output bit `j` clock ticks later (`j < r`). -/
theorem bit_reg_eq_outBit_stepN (spec : FCSRSpec) (s : FCSRState spec) (j : Nat) (hj : j < spec.r) :
    bit s.reg j = outBit (spec.stepN j s) := by
  induction j generalizing s with
  | zero => simp [bit, outBit, stepN]
  | succ k ih =>
    rw [stepN_succ, ← ih (spec.step s) (by omega)]
    have hnew : (spec.step s).reg = s.reg / 2 + ((spec.sigma s) % 2).toNat * 2 ^ (spec.r - 1) := rfl
    have hmod : bit (spec.step s).reg k = bit (s.reg / 2) k := by
      have hk : k < spec.r - 1 := by omega
      have h1 := bit_mod_pow_of_lt (spec.step s).reg (spec.r - 1) k hk
      have h2 := bit_mod_pow_of_lt (s.reg / 2) (spec.r - 1) k hk
      rw [← h1, ← h2, hnew, Nat.add_mul_mod_self_right]
    rw [hmod, bit_div_two]

theorem reg_eq_wordRun_r (spec : FCSRSpec) (s : FCSRState spec) :
    s.reg = spec.wordRun s spec.r := by
  rw [← sum_bits_eq s.reg spec.r s.hreg]
  unfold wordRun
  apply sumNat_congr
  intro j hj
  rw [bit_reg_eq_outBit_stepN spec s j hj]

/-- ENGINE THEOREM 1C: `potential` is globally INJECTIVE on the ENTIRE hardware state space. -/
theorem potential_injective (spec : FCSRSpec) {s1 s2 : FCSRState spec}
    (h : spec.potential s1 = spec.potential s2) : s1 = s2 := by
  have hreg : s1.reg = s2.reg := by
    rw [reg_eq_wordRun_r spec s1, reg_eq_wordRun_r spec s2]
    unfold wordRun
    apply sumNat_congr
    intro t _
    have ho1 := spec.outBit_eq_potential_emod (spec.stepN t s1)
    have ho2 := spec.outBit_eq_potential_emod (spec.stepN t s2)
    rw [spec.potential_stepN_eq_divStepN, h] at ho1
    rw [spec.potential_stepN_eq_divStepN] at ho2
    congr 1; omega
  have hcarry : s1.carry = s2.carry := by
    unfold potential at h
    rw [hreg] at h
    have hpos : ((2 ^ spec.r : Nat) : Int) > 0 := by exact_mod_cast spec.pow_r_pos
    have hmul : (s1.carry - s2.carry) * ((2 ^ spec.r : Nat) : Int) = 0 := by
      rw [Int.sub_mul]; omega
    have hzero : s1.carry - s2.carry = 0 := by
      rcases Int.mul_eq_zero.mp hmul with h0 | h0
      · exact h0
      · omega
    omega
  exact FCSRState.ext hreg hcarry

theorem divWord_exact (q : Nat) (hq_odd : q % 2 = 1) (p : Int) (n : Nat) :
    (q : Int) * (divWord q p n : Int) + ((2 ^ n : Nat) : Int) * divStepN q n p = p := by
  induction n with
  | zero => simp [divWord, sumNat, divStepN]
  | succ k ih =>
    have hstep := divStep_eq q hq_odd (divStepN q k p)
    have hsucc : divStepN q (k + 1) p = divStep q (divStepN q k p) := by
      clear ih hstep
      induction k generalizing p with
      | zero => rfl
      | succ m ihm => exact ihm (divStep q p)
    rw [← hsucc] at hstep
    have hto : (((divStepN q k p) % 2).toNat : Int) = (divStepN q k p) % 2 := by omega
    unfold divWord at ih ⊢
    simp only [sumNat, Int.natCast_add, Int.natCast_mul]
    rw [hto, Int.mul_add]
    have hpow : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) * 2 := by
      rw [Nat.pow_succ]; exact_mod_cast rfl
    rw [hpow, Int.mul_assoc]
    have hmul := congrArg (fun x => ((2 ^ k : Nat) : Int) * x) hstep
    rw [Int.mul_add] at hmul
    have hcomm : (q : Int) * ((divStepN q k p) % 2 * ((2 ^ k : Nat) : Int)) =
        ((2 ^ k : Nat) : Int) * ((q : Int) * ((divStepN q k p) % 2)) := by
      rw [Int.mul_comm ((divStepN q k p) % 2), ← Int.mul_assoc, Int.mul_comm (q : Int), Int.mul_assoc]
    rw [hcomm]
    omega

theorem potentialZero_mod_pow_r (spec : FCSRSpec) (reg : Nat) :
    (spec.potentialZero reg - spec.qInt * (reg : Int)) % ((2 ^ spec.r : Nat) : Int) = 0 := by
  unfold potentialZero qInt
  rw [sumInt_ofNat]
  have hdvd : ((2 ^ spec.r : Nat) : Int) ∣
      ((sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg % 2 ^ (spec.r - 1 - j))) : Int)
       - (reg : Int) - (spec.q : Int) * (reg : Int)) := by
    have hq1 : (spec.q : Int) * (reg : Int) + (reg : Int) =
        ((sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1)) * reg : Nat) : Int) := by
      rw [spec.tapWeightedSum_eq_q_add_one]
      have : ((spec.q + 1) * reg : Nat) = spec.q * reg + reg := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [this]; exact_mod_cast rfl
    have hnat : sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1)) * reg =
        sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg % 2 ^ (spec.r - 1 - j))) +
        sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j)) := by
      rw [← sumNat_mul_right, ← sumNat_add]
      apply sumNat_congr; intro j _
      have hdm := Nat.div_add_mod reg (2 ^ (spec.r - 1 - j))
      have hdm' : reg = reg % 2 ^ (spec.r - 1 - j) + (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j) := by
        rw [Nat.mul_comm] at hdm; omega
      calc bit spec.c j * 2 ^ (j + 1) * reg
          = bit spec.c j * 2 ^ (j + 1) * (reg % 2 ^ (spec.r - 1 - j) + (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j)) := by
            rw [← hdm']
        _ = bit spec.c j * 2 ^ (j + 1) * (reg % 2 ^ (spec.r - 1 - j)) +
            bit spec.c j * 2 ^ (j + 1) * (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j) := by
            rw [Nat.mul_add, ← Nat.mul_assoc]
    have hnatI : ((sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1)) * reg : Nat) : Int) =
        (sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg % 2 ^ (spec.r - 1 - j))) : Int) +
        (sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j)) : Int) := by
      exact_mod_cast hnat
    have heq : (sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg % 2 ^ (spec.r - 1 - j))) : Int)
        - (reg : Int) - (spec.q : Int) * (reg : Int) =
        -((sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j)) : Nat) : Int) := by
      omega
    rw [heq]
    apply Int.dvd_neg.mpr
    have hnat_dvd : 2 ^ spec.r ∣
        sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j)) := by
      refine ⟨sumNat spec.r (fun j => bit spec.c j * (reg / 2 ^ (spec.r - 1 - j))), ?_⟩
      rw [← sumNat_mul_left]
      apply sumNat_congr; intro j hj
      have hpow : 2 ^ (j + 1) * 2 ^ (spec.r - 1 - j) = 2 ^ spec.r := by
        rw [← Nat.pow_add]; congr 1; omega
      calc bit spec.c j * 2 ^ (j + 1) * (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ (spec.r - 1 - j)
          = bit spec.c j * (reg / 2 ^ (spec.r - 1 - j)) * (2 ^ (j + 1) * 2 ^ (spec.r - 1 - j)) := by
            simp only [Nat.mul_assoc]; congr 1; rw [Nat.mul_left_comm]
        _ = bit spec.c j * (reg / 2 ^ (spec.r - 1 - j)) * 2 ^ spec.r := by rw [hpow]
        _ = 2 ^ spec.r * (bit spec.c j * (reg / 2 ^ (spec.r - 1 - j))) := Nat.mul_comm _ _
    exact_mod_cast hnat_dvd
  exact Int.emod_eq_zero_of_dvd hdvd

theorem potential_encode (spec : FCSRSpec) (p : Int) :
    spec.potential (spec.encode p) = p := by
  unfold potential encode
  dsimp only
  have h1 := spec.potentialZero_mod_pow_r (divWord spec.q p spec.r)
  have h2 := divWord_exact spec.q spec.q_odd p spec.r
  have hdvd : ((2 ^ spec.r : Nat) : Int) ∣ (spec.potentialZero (divWord spec.q p spec.r) - p) := by
    have hd1 : ((2 ^ spec.r : Nat) : Int) ∣ (spec.potentialZero (divWord spec.q p spec.r) - spec.qInt * (divWord spec.q p spec.r : Int)) :=
      Int.dvd_of_emod_eq_zero h1
    have hd2 : ((2 ^ spec.r : Nat) : Int) ∣ (spec.qInt * (divWord spec.q p spec.r : Int) - p) := by
      refine ⟨-(divStepN spec.q spec.r p), ?_⟩
      unfold qInt
      rw [Int.mul_neg]
      omega
    have hadd := Int.dvd_add hd1 hd2
    have hcancel : (spec.potentialZero (divWord spec.q p spec.r) - spec.qInt * (divWord spec.q p spec.r : Int)) +
        (spec.qInt * (divWord spec.q p spec.r : Int) - p) =
        spec.potentialZero (divWord spec.q p spec.r) - p := by omega
    rw [hcancel] at hadd
    exact hadd
  rcases hdvd with ⟨k, hk⟩
  have hpos : ((2 ^ spec.r : Nat) : Int) > 0 := by exact_mod_cast spec.pow_r_pos
  have hdiv : (spec.potentialZero (divWord spec.q p spec.r) - p) / ((2 ^ spec.r : Nat) : Int) = k := by
    rw [hk, Int.mul_ediv_cancel_left k (by omega)]
  rw [hdiv, Int.mul_comm]
  omega

theorem encode_potential (spec : FCSRSpec) (s : FCSRState spec) :
    spec.encode (spec.potential s) = s :=
  spec.potential_injective (spec.potential_encode (spec.potential s))

theorem divStep_mem_core (q : Nat) (hq_odd : q % 2 = 1) (hq : 3 ≤ q) {p : Int}
    (hlo : -(q : Int) < p) (hhi : p < 0) :
    -(q : Int) < divStep q p ∧ divStep q p < 0 := by
  have h := divStep_eq q hq_odd p
  have hp : p % 2 = 0 ∨ p % 2 = 1 := by omega
  rcases hp with h0 | h1
  · rw [h0] at h; omega
  · rw [h1] at h; omega

theorem invDivStep_mem_core (q : Nat) (hq_odd : q % 2 = 1) {p : Int}
    (hlo : -(q : Int) < p) (hhi : p < 0) :
    -(q : Int) < invDivStep q p ∧ invDivStep q p < 0 := by
  unfold invDivStep
  split <;> omega

theorem invDivStep_divStep (q : Nat) (hq_odd : q % 2 = 1) {p : Int}
    (hlo : -(q : Int) < p) (hhi : p < 0) :
    invDivStep q (divStep q p) = p := by
  have h := divStep_eq q hq_odd p
  have hp : p % 2 = 0 ∨ p % 2 = 1 := by omega
  unfold invDivStep
  rcases hp with h0 | h1
  · rw [h0] at h; split <;> omega
  · rw [h1] at h; split <;> omega

theorem divStep_invDivStep (q : Nat) (hq_odd : q % 2 = 1) (p : Int) :
    divStep q (invDivStep q p) = p := by
  unfold invDivStep
  split
  · have h := divStep_eq q hq_odd (2 * p)
    have hm : (2 * p) % 2 = 0 := by omega
    rw [hm] at h; omega
  · have h := divStep_eq q hq_odd (2 * p + (q : Int))
    have hm : (2 * p + (q : Int)) % 2 = 1 := by omega
    rw [hm] at h; omega

theorem step_inCore (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) :
    spec.InCore (spec.step s) := by
  unfold InCore at hs ⊢
  rw [spec.potential_step_eq_divStep]
  exact divStep_mem_core spec.q spec.q_odd spec.q_ge_three hs.1 hs.2

theorem stepN_inCore (spec : FCSRSpec) (n : Nat) {s : FCSRState spec} (hs : spec.InCore s) :
    spec.InCore (spec.stepN n s) := by
  induction n generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (spec.step_inCore hs)

theorem invStep_inCore (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) :
    spec.InCore (spec.invStep s) := by
  unfold InCore at hs ⊢
  unfold invStep
  rw [spec.potential_encode]
  exact invDivStep_mem_core spec.q spec.q_odd hs.1 hs.2

/-- ENGINE THEOREM 1D: Exact Hardware Reversibility Bijection on the Periodic Core `P_q`. -/
theorem step_bijection_on_core (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) :
    spec.invStep (spec.step s) = s ∧ spec.step (spec.invStep s) = s := by
  constructor
  · apply spec.potential_injective
    unfold invStep
    rw [spec.potential_encode, spec.potential_step_eq_divStep]
    exact invDivStep_divStep spec.q spec.q_odd hs.1 hs.2
  · apply spec.potential_injective
    unfold invStep
    rw [spec.potential_step_eq_divStep, spec.potential_encode]
    exact divStep_invDivStep spec.q spec.q_odd (spec.potential s)

/-- SHARPNESS THEOREM 1E: Reversibility FAILS outside the periodic core for EVERY odd `q ≥ 3`! -/
theorem step_not_injective_outside_core (spec : FCSRSpec) :
    ∃ s1 s2 : FCSRState spec,
      s1 ≠ s2 ∧ ¬ spec.InCore s1 ∧ ¬ spec.InCore s2 ∧ spec.step s1 = spec.step s2 := by
  have hpow_ge2 : 2 ≤ 2 ^ spec.r := by
    have := spec.pow_r_eq
    have : 1 ≤ 2 ^ (spec.r - 1) := Nat.pow_pos (by omega)
    omega
  let s1 : FCSRState spec := ⟨0, by omega, -1⟩
  let s2 : FCSRState spec := ⟨1, by omega, -2⟩
  have htd0 : spec.tapDot 0 = 0 := by
    unfold tapDot
    rw [sumNat_congr (g := fun _ => 0) (fun i _ => by simp [bit_zero])]
    rw [sumNat_const]; omega
  have htd1 : spec.tapDot 1 = 1 := by
    unfold tapDot
    have hsplit : spec.r = (spec.r - 1) + 1 := by have := spec.hr; omega
    have hprev : sumNat (spec.r - 1) (fun j => bit spec.c j * bit 1 (spec.r - 1 - j)) = 0 := by
      rw [sumNat_congr (g := fun _ => 0)]
      · rw [sumNat_const]; omega
      · intro j hj
        have h2 : 2 ≤ 2 ^ (spec.r - 1 - j) := by
          have := pow2_pred_mul (spec.r - 1 - j) (by omega)
          have : 1 ≤ 2 ^ (spec.r - 1 - j - 1) := Nat.pow_pos (by omega)
          omega
        have hb : bit 1 (spec.r - 1 - j) = 0 := by
          unfold bit; rw [Nat.div_eq_of_lt (by omega)]
        rw [hb, Nat.mul_zero]
    have hlast : sumNat spec.r (fun j => bit spec.c j * bit 1 (spec.r - 1 - j)) =
        sumNat (spec.r - 1) (fun j => bit spec.c j * bit 1 (spec.r - 1 - j)) +
        bit spec.c (spec.r - 1) * bit 1 (spec.r - 1 - (spec.r - 1)) := by
      conv => lhs; rw [hsplit]
      rfl
    rw [hlast, hprev, Nat.sub_self, bit_zero_idx, spec.tap_msb]
  have hsg1 : spec.sigma s1 = -1 := by unfold sigma s1; dsimp only; rw [htd0]; omega
  have hsg2 : spec.sigma s2 = -1 := by unfold sigma s2; dsimp only; rw [htd1]; omega
  have hstep_eq : spec.step s1 = spec.step s2 := by
    apply FCSRState.ext
    · change 0 / 2 + ((spec.sigma s1) % 2).toNat * 2 ^ (spec.r - 1) =
             1 / 2 + ((spec.sigma s2) % 2).toNat * 2 ^ (spec.r - 1)
      rw [hsg1, hsg2]
    · change (spec.sigma s1) / 2 = (spec.sigma s2) / 2
      rw [hsg1, hsg2]
  have hp1 : spec.potential s1 = ((2 ^ spec.r : Nat) : Int) := by
    unfold potential potentialZero s1
    dsimp only
    have h0 : sumInt spec.r (fun j => ((bit spec.c j * 2 ^ (j + 1) * (0 % 2 ^ (spec.r - 1 - j)) : Nat) : Int)) = 0 := by
      rw [sumInt_congr (g := fun _ => 0) (fun i _ => by simp)]
      rw [sumInt_const]; omega
    rw [h0]; omega
  refine ⟨s1, s2, ?_, ?_, ?_, hstep_eq⟩
  · intro h
    have := congrArg FCSRState.reg h
    simp [s1, s2] at this
  · intro hc
    have hlt := hc.2
    omega
  · intro hc
    have hlt := hc.2
    have hps1 := spec.potential_step s1
    have hps2 := spec.potential_step s2
    rw [hstep_eq] at hps1
    have ho1 : outBit s1 = 0 := rfl
    have ho2 : outBit s2 = 1 := rfl
    rw [ho1] at hps1
    rw [ho2] at hps2
    have hqp := spec.qInt_pos
    simp at hps1 hps2
    omega

-- ============================================================================
-- Section 2: Exact Complementation Involution, Carry Bounds & Conservation
-- ============================================================================

theorem complement_involutive (spec : FCSRSpec) (s : FCSRState spec) :
    spec.complement (spec.complement s) = s := by
  apply FCSRState.ext
  · change 2 ^ spec.r - 1 - (2 ^ spec.r - 1 - s.reg) = s.reg
    have := s.hreg; omega
  · change (spec.tapWeight : Int) - 1 - ((spec.tapWeight : Int) - 1 - s.carry) = s.carry
    omega

theorem complement_outBit (spec : FCSRSpec) (s : FCSRState spec) :
    outBit (spec.complement s) = 1 - outBit s := by
  unfold outBit complement
  dsimp only
  have h2dvd : 2 ∣ 2 ^ spec.r := by
    rw [spec.pow_r_eq]; exact ⟨2 ^ (spec.r - 1), rfl⟩
  rcases h2dvd with ⟨k, hk⟩
  have hreg := s.hreg
  omega

/-- ENGINE THEOREM 2A: Exact potential negation under `C_q` (holds on ALL states, periodic or transient). -/
theorem complement_potential (spec : FCSRSpec) (s : FCSRState spec) :
    spec.potential (spec.complement s) = -spec.qInt - spec.potential s := by
  have hmod_comp : ∀ j, j < spec.r →
      (2 ^ spec.r - 1 - s.reg) % 2 ^ (spec.r - 1 - j) + s.reg % 2 ^ (spec.r - 1 - j) =
      2 ^ (spec.r - 1 - j) - 1 := by
    intro j hj
    have hdvd : 2 ^ (spec.r - 1 - j) ∣ 2 ^ spec.r := by
      refine ⟨2 ^ (j + 1), ?_⟩
      rw [← Nat.pow_add]; congr 1; omega
    rcases hdvd with ⟨m, hm⟩
    have hpos : 0 < 2 ^ (spec.r - 1 - j) := Nat.pow_pos (by omega)
    have hm_pos : 1 ≤ m := by
      cases m with
      | zero =>
        rw [Nat.mul_zero] at hm
        have := spec.pow_r_pos; omega
      | succ _ => omega
    have hreg := s.hreg
    have hdiv_le : s.reg / 2 ^ (spec.r - 1 - j) ≤ m - 1 := by
      have : s.reg < 2 ^ (spec.r - 1 - j) * m := by rw [← hm]; exact hreg
      have : s.reg / 2 ^ (spec.r - 1 - j) < m := (Nat.div_lt_iff_lt_mul hpos).2 (by rw [Nat.mul_comm]; exact this)
      omega
    have hdm := Nat.div_add_mod s.reg (2 ^ (spec.r - 1 - j))
    have hrem : s.reg % 2 ^ (spec.r - 1 - j) < 2 ^ (spec.r - 1 - j) := Nat.mod_lt _ hpos
    have hrew : 2 ^ spec.r - 1 - s.reg =
        (2 ^ (spec.r - 1 - j) - 1 - s.reg % 2 ^ (spec.r - 1 - j)) +
        2 ^ (spec.r - 1 - j) * (m - 1 - s.reg / 2 ^ (spec.r - 1 - j)) := by
      have hm1 : 2 ^ (spec.r - 1 - j) * m =
          2 ^ (spec.r - 1 - j) * (m - 1 - s.reg / 2 ^ (spec.r - 1 - j)) +
          2 ^ (spec.r - 1 - j) * (s.reg / 2 ^ (spec.r - 1 - j)) + 2 ^ (spec.r - 1 - j) := by
        rw [← Nat.mul_add, ← Nat.mul_succ]
        congr 1; omega
      omega
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsum_add :
      sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * ((2 ^ spec.r - 1 - s.reg) % 2 ^ (spec.r - 1 - j))) +
      sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (s.reg % 2 ^ (spec.r - 1 - j))) +
      (spec.q + 1) =
      spec.tapWeight * 2 ^ spec.r := by
    rw [← sumNat_add, ← spec.tapWeightedSum_eq_q_add_one, ← sumNat_add]
    unfold tapWeight
    rw [← sumNat_mul_right]
    apply sumNat_congr
    intro j hj
    have hmc := hmod_comp j hj
    have hpow : 2 ^ (j + 1) * 2 ^ (spec.r - 1 - j) = 2 ^ spec.r := by
      rw [← Nat.pow_add]; congr 1; omega
    have hpos : 1 ≤ 2 ^ (spec.r - 1 - j) := Nat.pow_pos (by omega)
    have hm1 : (2 ^ spec.r - 1 - s.reg) % 2 ^ (spec.r - 1 - j) + s.reg % 2 ^ (spec.r - 1 - j) + 1 =
        2 ^ (spec.r - 1 - j) := by omega
    calc bit spec.c j * 2 ^ (j + 1) * ((2 ^ spec.r - 1 - s.reg) % 2 ^ (spec.r - 1 - j)) +
          bit spec.c j * 2 ^ (j + 1) * (s.reg % 2 ^ (spec.r - 1 - j)) +
          bit spec.c j * 2 ^ (j + 1)
        = bit spec.c j * 2 ^ (j + 1) *
            ((2 ^ spec.r - 1 - s.reg) % 2 ^ (spec.r - 1 - j) + s.reg % 2 ^ (spec.r - 1 - j) + 1) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      _ = bit spec.c j * 2 ^ (j + 1) * 2 ^ (spec.r - 1 - j) := by rw [hm1]
      _ = bit spec.c j * 2 ^ spec.r := by rw [Nat.mul_assoc, hpow]
  unfold potential potentialZero complement qInt
  dsimp only
  rw [sumInt_ofNat, sumInt_ofNat]
  have hsumI :
      (sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * ((2 ^ spec.r - 1 - s.reg) % 2 ^ (spec.r - 1 - j))) : Int) +
      (sumNat spec.r (fun j => bit spec.c j * 2 ^ (j + 1) * (s.reg % 2 ^ (spec.r - 1 - j))) : Int) +
      ((spec.q : Int) + 1) =
      (spec.tapWeight : Int) * ((2 ^ spec.r : Nat) : Int) := by
    exact_mod_cast hsum_add
  have hregI : ((2 ^ spec.r - 1 - s.reg : Nat) : Int) + (s.reg : Int) = ((2 ^ spec.r : Nat) : Int) - 1 := by
    have := s.hreg; have := spec.pow_r_pos; omega
  have hcarryI : ((spec.tapWeight : Int) - 1 - s.carry) * ((2 ^ spec.r : Nat) : Int) +
      s.carry * ((2 ^ spec.r : Nat) : Int) =
      (spec.tapWeight : Int) * ((2 ^ spec.r : Nat) : Int) - ((2 ^ spec.r : Nat) : Int) := by
    rw [← Int.add_mul]
    have h1 : (spec.tapWeight : Int) - 1 - s.carry + s.carry = (spec.tapWeight : Int) - 1 := by omega
    rw [h1, Int.sub_mul, Int.one_mul]
  omega

/-- ENGINE THEOREM 2B: Exact hardware commutation `step (C_q s) = C_q (step s)`. -/
theorem complement_step (spec : FCSRSpec) (s : FCSRState spec) :
    spec.step (spec.complement s) = spec.complement (spec.step s) := by
  apply spec.potential_injective
  rw [spec.complement_potential]
  have h1 := spec.potential_step (spec.complement s)
  have h2 := spec.potential_step s
  rw [spec.complement_potential, spec.complement_outBit] at h1
  have hob := outBit_lt_two s
  have h1bit : ((1 - outBit s : Nat) : Int) = 1 - (outBit s : Int) := by omega
  rw [h1bit, Int.mul_sub, Int.mul_one] at h1
  omega

theorem complement_stepN (spec : FCSRSpec) (n : Nat) (s : FCSRState spec) :
    spec.stepN n (spec.complement s) = spec.complement (spec.stepN n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [stepN_succ, stepN_succ, spec.complement_step, ih]

theorem complement_inCore (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) :
    spec.InCore (spec.complement s) := by
  unfold InCore at hs ⊢
  rw [spec.complement_potential]
  omega

/-- ENGINE THEOREM 2C: Exact Goresky-Klapper Carry Bounds `0 ≤ m ≤ w(q+1) - 1` on `P_q`
    (proved constructively via `potentialZero ≥ -(2^r - 1)` + complementation involution!). -/
theorem carry_bounds_on_core (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) :
    0 ≤ s.carry ∧ s.carry ≤ (spec.tapWeight : Int) - 1 := by
  have lower : ∀ t : FCSRState spec, spec.InCore t → 0 ≤ t.carry := by
    intro t ht
    have hlt := ht.2
    unfold potential potentialZero at hlt
    have hsum_nn : 0 ≤ sumInt spec.r (fun j =>
        ((bit spec.c j * 2 ^ (j + 1) * (t.reg % 2 ^ (spec.r - 1 - j)) : Nat) : Int)) := by
      apply sumInt_nonneg; intro i _; exact Int.natCast_nonneg _
    have hreg_lt : (t.reg : Int) < ((2 ^ spec.r : Nat) : Int) := by exact_mod_cast t.hreg
    have hmul : -((2 ^ spec.r : Nat) : Int) < t.carry * ((2 ^ spec.r : Nat) : Int) := by omega
    if h0 : 0 ≤ t.carry then
      exact h0
    else
      have hle : t.carry ≤ -1 := by omega
      have hpos : (0 : Int) ≤ ((2 ^ spec.r : Nat) : Int) := Int.natCast_nonneg _
      have hle2 : t.carry * ((2 ^ spec.r : Nat) : Int) ≤ (-1) * ((2 ^ spec.r : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_right hle hpos
      omega
  constructor
  · exact lower s hs
  · have hc := lower (spec.complement s) (spec.complement_inCore hs)
    change 0 ≤ (spec.tapWeight : Int) - 1 - s.carry at hc
    omega

/-- ENGINE THEOREM 2D: Universal Carry-Bit Conservation Law over ANY periodic orbit of ANY odd `q ≥ 3`:
    `∑_{t=0}^{T-1} m_t = (w(q+1) - 1) * ∑_{t=0}^{T-1} a_t`. -/
theorem universal_carry_bit_conservation (spec : FCSRSpec) (s : FCSRState spec) (T : Nat)
    (hper : spec.stepN T s = s) :
    sumInt T (fun t => (spec.stepN t s).carry) =
    ((spec.tapWeight : Int) - 1) * sumInt T (fun t => (outBit (spec.stepN t s) : Int)) := by
  have hper_shift : ∀ t, spec.stepN (t + T) s = spec.stepN t s := by
    intro t; rw [Nat.add_comm, stepN_add, hper]
  have hone : ∀ t,
      (outBit (spec.stepN (t + spec.r) s) : Int) + 2 * (spec.stepN (t + 1) s).carry =
      (spec.stepN t s).carry +
      sumInt spec.r (fun j => (bit spec.c j : Int) * (outBit (spec.stepN (t + (spec.r - 1 - j)) s) : Int)) := by
    intro t
    let st := spec.stepN t s
    have htop : (outBit (spec.stepN (t + spec.r) s) : Int) = (((spec.sigma st) % 2).toNat : Int) := by
      have h1 : spec.stepN (t + spec.r) s = spec.stepN (spec.r - 1) (spec.step st) := by
        have htr : t + spec.r = t + 1 + (spec.r - 1) := by have := spec.hr; omega
        rw [htr, stepN_add, stepN_add]; rfl
      rw [h1, ← bit_reg_eq_outBit_stepN spec (spec.step st) (spec.r - 1) (by have := spec.hr; omega)]
      have hnew : (spec.step st).reg = st.reg / 2 + ((spec.sigma st) % 2).toNat * 2 ^ (spec.r - 1) := rfl
      have hdiv_lt : st.reg / 2 < 2 ^ (spec.r - 1) := by
        have hpr := spec.pow_r_eq; have hsr := st.hreg; omega
      have htop_lt : ((spec.sigma st) % 2).toNat < 2 := by omega
      have hbit : bit (spec.step st).reg (spec.r - 1) = ((spec.sigma st) % 2).toNat := by
        unfold bit
        rw [hnew, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)),
            Nat.div_eq_of_lt hdiv_lt, Nat.zero_add, Nat.mod_eq_of_lt htop_lt]
      rw [hbit]
    have hsg : st.carry + (spec.tapDot st.reg : Int) =
        2 * (spec.step st).carry + (((spec.sigma st) % 2).toNat : Int) := by
      have hc : (spec.step st).carry = (spec.sigma st) / 2 := rfl
      have hdef : spec.sigma st = st.carry + (spec.tapDot st.reg : Int) := rfl
      omega
    have htd : (spec.tapDot st.reg : Int) =
        sumInt spec.r (fun j => (bit spec.c j : Int) * (outBit (spec.stepN (t + (spec.r - 1 - j)) s) : Int)) := by
      unfold tapDot
      rw [← sumInt_ofNat]
      apply sumInt_congr; intro j hj
      rw [Int.natCast_mul, bit_reg_eq_outBit_stepN spec st (spec.r - 1 - j) (by omega)]
      have : spec.stepN (spec.r - 1 - j) st = spec.stepN (t + (spec.r - 1 - j)) s := by
        rw [stepN_add]
      rw [this]
    have hnext : spec.stepN (t + 1) s = spec.step st := stepN_succ_right spec t s
    rw [htop, hnext, ← htd]
    exact hsg.symm.trans (by omega) |> fun h => by
      have : st.carry = (spec.stepN t s).carry := rfl
      omega
  have hsum_eq :
      sumInt T (fun t => (outBit (spec.stepN (t + spec.r) s) : Int) + 2 * (spec.stepN (t + 1) s).carry) =
      sumInt T (fun t => (spec.stepN t s).carry +
        sumInt spec.r (fun j => (bit spec.c j : Int) * (outBit (spec.stepN (t + (spec.r - 1 - j)) s) : Int))) :=
    sumInt_congr (fun t _ => hone t)
  rw [sumInt_add, sumInt_add, sumInt_mul_left, sumInt_swap] at hsum_eq
  have hbits_r : sumInt T (fun t => (outBit (spec.stepN (t + spec.r) s) : Int)) =
      sumInt T (fun t => (outBit (spec.stepN t s) : Int)) :=
    sumInt_shift T spec.r (fun t => (outBit (spec.stepN t s) : Int)) (fun t => by rw [hper_shift])
  have hcarry_1 : sumInt T (fun t => (spec.stepN (t + 1) s).carry) =
      sumInt T (fun t => (spec.stepN t s).carry) :=
    sumInt_shift T 1 (fun t => (spec.stepN t s).carry) (fun t => by rw [hper_shift])
  have htap_sum :
      sumInt spec.r (fun j => sumInt T (fun t => (bit spec.c j : Int) * (outBit (spec.stepN (t + (spec.r - 1 - j)) s) : Int))) =
      (spec.tapWeight : Int) * sumInt T (fun t => (outBit (spec.stepN t s) : Int)) := by
    have hinner : ∀ j, j < spec.r →
        sumInt T (fun t => (bit spec.c j : Int) * (outBit (spec.stepN (t + (spec.r - 1 - j)) s) : Int)) =
        (bit spec.c j : Int) * sumInt T (fun t => (outBit (spec.stepN t s) : Int)) := by
      intro j _
      rw [sumInt_mul_left]
      congr 1
      exact sumInt_shift T (spec.r - 1 - j) (fun t => (outBit (spec.stepN t s) : Int))
        (fun t => by rw [hper_shift])
    rw [sumInt_congr hinner, sumInt_mul_right, sumInt_ofNat]
    rfl
  rw [hbits_r, hcarry_1, htap_sum] at hsum_eq
  rw [Int.sub_mul, Int.one_mul]
  omega

-- ============================================================================
-- Section 3: Finite-Certificate Exact Period & Half-Period Engine
-- ============================================================================

/-- `2^n * P_q(step^n s) ≡ P_q(s) (mod q)` for all `n ∈ ℕ`. -/
theorem stepN_potential_mod (spec : FCSRSpec) (s : FCSRState spec) (n : Nat) :
    spec.qInt ∣ (((2 ^ n : Nat) : Int) * spec.potential (spec.stepN n s) - spec.potential s) := by
  refine ⟨-(spec.wordRun s n : Int), ?_⟩
  have h := spec.word_representation_exact s n
  rw [Int.mul_neg]
  omega

/-- Coprimality helper: since `q` is odd, `q ∣ 2^n * x → q ∣ x`. -/
theorem odd_dvd_of_dvd_pow2_mul (q : Nat) (hq_odd : q % 2 = 1) (n : Nat) (x : Int)
    (h : (q : Int) ∣ ((2 ^ n : Nat) : Int) * x) : (q : Int) ∣ x := by
  induction n with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have hpow : ((2 ^ (k + 1) : Nat) : Int) * x = 2 * (((2 ^ k : Nat) : Int) * x) := by
      rw [Nat.pow_succ, Nat.mul_comm _ 2, Int.natCast_mul, Int.mul_assoc]; rfl
    rw [hpow] at h
    rcases h with ⟨m, hm⟩
    have hq_def : (q : Int) = 2 * ((q / 2 : Nat) : Int) + 1 := by omega
    have hqm : (q : Int) * m = 2 * (((q / 2 : Nat) : Int) * m) + m := by
      conv => lhs; rw [hq_def]
      rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
    have hm_even : m % 2 = 0 := by omega
    have hm_eq : m = 2 * (m / 2) := by omega
    refine ⟨m / 2, ?_⟩
    have hqm2 : (q : Int) * m = 2 * ((q : Int) * (m / 2)) := by
      conv => lhs; rw [hm_eq]
      rw [Int.mul_left_comm]
    omega

/-- Periodicity iff modular divisibility on the periodic core `P_q`. -/
theorem stepN_eq_iff_dvd (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s) (T : Nat) :
    spec.stepN T s = s ↔ spec.qInt ∣ (((2 ^ T : Nat) : Int) - 1) * spec.potential s := by
  constructor
  · intro heq
    have h := spec.stepN_potential_mod s T
    rw [heq] at h
    simpa [Int.sub_mul, Int.one_mul] using h
  · intro hdvd
    have hmod := spec.stepN_potential_mod s T
    have hdiff : spec.qInt ∣ ((2 ^ T : Nat) : Int) * (spec.potential (spec.stepN T s) - spec.potential s) := by
      have hsub := Int.dvd_sub hmod hdvd
      have halg : (((2 ^ T : Nat) : Int) * spec.potential (spec.stepN T s) - spec.potential s) -
          (((2 ^ T : Nat) : Int) - 1) * spec.potential s =
          ((2 ^ T : Nat) : Int) * (spec.potential (spec.stepN T s) - spec.potential s) := by
        rw [Int.sub_mul, Int.one_mul, Int.mul_sub]; omega
      rw [halg] at hsub
      exact hsub
    have hq_dvd : spec.qInt ∣ (spec.potential (spec.stepN T s) - spec.potential s) :=
      odd_dvd_of_dvd_pow2_mul spec.q spec.q_odd T _ hdiff
    have hsT := spec.stepN_inCore T hs
    rcases hq_dvd with ⟨k, hk⟩
    have hlo1 := hs.1; have hhi1 := hs.2
    have hlo2 := hsT.1; have hhi2 := hsT.2
    have hqp := spec.qInt_pos
    have hk0 : k = 0 := by
      if hpos : k ≥ 1 then
        have : spec.qInt * k ≥ spec.qInt * 1 := Int.mul_le_mul_of_nonneg_left hpos (by omega)
        omega
      else if hneg : k ≤ -1 then
        have : spec.qInt * k ≤ spec.qInt * (-1) := Int.mul_le_mul_of_nonneg_left hneg (by omega)
        omega
      else omega
    subst hk0
    have hpeq : spec.potential (spec.stepN T s) = spec.potential s := by omega
    exact spec.potential_injective hpeq

/-- If `step^a s = s` and `step^b s = s`, then `step^(gcd a b) s = s` (pure Euclidean descent). -/
theorem stepN_mul_eq (spec : FCSRSpec) (s : FCSRState spec) (a k : Nat)
    (ha : spec.stepN a s = s) : spec.stepN (a * k) s = s := by
  induction k with
  | zero => simp [stepN]
  | succ m ih =>
    rw [Nat.mul_succ, stepN_add, ih, ha]

theorem stepN_mod_eq (spec : FCSRSpec) (s : FCSRState spec) (a b : Nat)
    (ha : spec.stepN a s = s) (hb : spec.stepN b s = s) :
    spec.stepN (b % a) s = s := by
  have hdm := Nat.div_add_mod b a
  have h1 : spec.stepN b s = spec.stepN (b % a) (spec.stepN (a * (b / a)) s) := by
    conv => lhs; rw [← hdm]
    rw [stepN_add]
  rw [stepN_mul_eq spec s a (b / a) ha] at h1
  rw [← h1, hb]

theorem stepN_gcd_eq (spec : FCSRSpec) (s : FCSRState spec) (a b : Nat)
    (ha : spec.stepN a s = s) (hb : spec.stepN b s = s) :
    spec.stepN (Nat.gcd a b) s = s := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    cases a with
    | zero => simpa using hb
    | succ a' =>
      rw [Nat.gcd_rec]
      exact ih (b % (a' + 1)) (Nat.mod_lt b (by omega)) (a' + 1)
        (stepN_mod_eq spec s (a' + 1) b ha hb) ha

/-- Minimal period predicate for a hardware FCSR state `s`. -/
def IsExactPeriod (spec : FCSRSpec) (s : FCSRState spec) (T : Nat) : Prop :=
  0 < T ∧ spec.stepN T s = s ∧ ∀ t, 0 < t → t < T → spec.stepN t s ≠ s

/-- ENGINE THEOREM 3A: Half-Period Complementation Certificate Soundness.
    If `s ∈ P_q` and `q ∣ (2^h + 1) * P_q(s)`, then:
    (1) `step^h s = complement s` (full hardware register + carry complementation),
    (2) `step^(2h) s = s`,
    (3) `∀ t, a_{t+h} = 1 - a_t`,
    (4) `∀ t, m_{t+h} = (w(q+1) - 1) - m_t`,
    (5) exact 50/50 bit balance `∑_{t=0}^{2h-1} a_t = h`,
    (6) exact carry sum `∑_{t=0}^{2h-1} m_t = h * (w(q+1) - 1)`. -/
theorem halfPeriod_certificate (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s)
    (h : Nat) (hdvd : spec.qInt ∣ (((2 ^ h : Nat) : Int) + 1) * spec.potential s) :
    spec.stepN h s = spec.complement s ∧
    spec.stepN (2 * h) s = s ∧
    (∀ t, outBit (spec.stepN (t + h) s) = 1 - outBit (spec.stepN t s)) ∧
    (∀ t, (spec.stepN (t + h) s).carry = (spec.tapWeight : Int) - 1 - (spec.stepN t s).carry) ∧
    sumInt (2 * h) (fun t => (outBit (spec.stepN t s) : Int)) = (h : Int) ∧
    sumInt (2 * h) (fun t => (spec.stepN t s).carry) = (h : Int) * ((spec.tapWeight : Int) - 1) := by
  have hcomp_eq : spec.stepN h s = spec.complement s := by
    have hmod := spec.stepN_potential_mod s h
    -- 2^h * P(step^h s) - P(s) ≡ 0 (mod q) and (2^h + 1) * P(s) ≡ 0 (mod q)
    -- => 2^h * (P(step^h s) + P(s)) ≡ 0 (mod q)
    -- => 2^h * (P(step^h s) - (-q - P(s))) ≡ 0 (mod q)
    have hsum_dvd : spec.qInt ∣ ((2 ^ h : Nat) : Int) * (spec.potential (spec.stepN h s) - spec.potential (spec.complement s)) := by
      have h1 := Int.dvd_add hmod hdvd
      have h2 : spec.qInt ∣ ((2 ^ h : Nat) : Int) * spec.qInt := ⟨((2 ^ h : Nat) : Int), Int.mul_comm _ _⟩
      have h3 := Int.dvd_add h1 h2
      rw [spec.complement_potential]
      have halg : (((2 ^ h : Nat) : Int) * spec.potential (spec.stepN h s) - spec.potential s) +
          (((2 ^ h : Nat) : Int) + 1) * spec.potential s + ((2 ^ h : Nat) : Int) * spec.qInt =
          ((2 ^ h : Nat) : Int) * (spec.potential (spec.stepN h s) - (-spec.qInt - spec.potential s)) := by
        rw [Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_sub, Int.mul_neg]; omega
      rw [halg] at h3
      exact h3
    have hq_dvd := odd_dvd_of_dvd_pow2_mul spec.q spec.q_odd h _ hsum_dvd
    have hsH := spec.stepN_inCore h hs
    have hsC := spec.complement_inCore hs
    rcases hq_dvd with ⟨k, hk⟩
    have hlo1 := hsH.1; have hhi1 := hsH.2
    have hlo2 := hsC.1; have hhi2 := hsC.2
    have hqp := spec.qInt_pos
    unfold FCSRSpec.qInt at hlo1 hhi1 hlo2 hhi2 hqp
    have hk0 : k = 0 := by
      if hpos : k ≥ 1 then
        have : (spec.q : Int) * k ≥ (spec.q : Int) * 1 := Int.mul_le_mul_of_nonneg_left hpos (by omega)
        omega
      else if hneg : k ≤ -1 then
        have : (spec.q : Int) * k ≤ (spec.q : Int) * (-1) := Int.mul_le_mul_of_nonneg_left hneg (by omega)
        omega
      else omega
    subst hk0
    exact spec.potential_injective (by omega)
  have hper2h : spec.stepN (2 * h) s = s := by
    have h2 : 2 * h = h + h := by omega
    rw [h2, stepN_add, hcomp_eq, spec.complement_stepN, hcomp_eq, spec.complement_involutive]
  have hbit_anti : ∀ t, outBit (spec.stepN (t + h) s) = 1 - outBit (spec.stepN t s) := by
    intro t
    rw [Nat.add_comm, stepN_add, hcomp_eq, spec.complement_stepN, spec.complement_outBit]
  have hcarry_anti : ∀ t, (spec.stepN (t + h) s).carry = (spec.tapWeight : Int) - 1 - (spec.stepN t s).carry := by
    intro t
    rw [Nat.add_comm, stepN_add, hcomp_eq, spec.complement_stepN]
    rfl
  have hbal : sumInt (2 * h) (fun t => (outBit (spec.stepN t s) : Int)) = (h : Int) := by
    have h2 : 2 * h = h + h := by omega
    rw [h2, sumInt_split, ← sumInt_add]
    have h1 : sumInt h (fun t => (outBit (spec.stepN t s) : Int) + (outBit (spec.stepN (h + t) s) : Int)) =
        sumInt h (fun _ => (1 : Int)) := by
      apply sumInt_congr; intro t _
      have ha := hbit_anti t
      rw [Nat.add_comm] at ha
      have hlt := outBit_lt_two (spec.stepN t s)
      omega
    rw [h1, sumInt_const, Int.mul_one]
  have hcsum : sumInt (2 * h) (fun t => (spec.stepN t s).carry) = (h : Int) * ((spec.tapWeight : Int) - 1) := by
    rw [spec.universal_carry_bit_conservation s (2 * h) hper2h, hbal, Int.mul_comm]
  exact ⟨hcomp_eq, hper2h, hbit_anti, hcarry_anti, hbal, hcsum⟩

-- ----------------------------------------------------------------------------
-- Decidable Finite-Certificate Engine for Arbitrary Concrete `(q, p, T)`
-- ----------------------------------------------------------------------------

/-- Fast modular exponentiation `base ^ exp % mod` (pure exact Nat). -/
def powMod (base exp m : Nat) : Nat :=
  match exp with
  | 0 => 1 % m
  | k + 1 => (base * powMod base k m) % m

theorem powMod_eq (base exp m : Nat) : powMod base exp m = (base ^ exp) % m := by
  induction exp with
  | zero => simp [powMod]
  | succ k ih =>
    simp only [powMod, ih, Nat.pow_succ]
    rw [Nat.mul_comm (base ^ k) base, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- Strip all factors of `d` from `n` (fuel-bounded for structural recursion). -/
def stripFactorFuel : Nat → Nat → Nat → Nat
  | 0, n, _ => n
  | fuel + 1, n, d =>
    if d ≥ 2 ∧ n % d = 0 then stripFactorFuel fuel (n / d) d else n

def stripList (n : Nat) (factors : List Nat) : Nat :=
  factors.foldl (fun acc d => stripFactorFuel acc acc d) n

/-- Every prime divisor `p` of `n` divides some element of `factors` if `stripList n factors = 1`. -/
theorem stripFactorFuel_dvd_prop (fuel n d p : Nat)
    (hp_prime : ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b)
    (hdiv : p ∣ n) (hnot : ¬ p ∣ stripFactorFuel fuel n d) : p ∣ d := by
  induction fuel generalizing n with
  | zero => simp [stripFactorFuel] at hnot; exact False.elim (hnot hdiv)
  | succ f ih =>
    unfold stripFactorFuel at hnot
    split at hnot
    · rename_i hcond
      have hdm : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hcond.2)
      rw [← hdm] at hdiv
      rcases hp_prime d (n / d) hdiv with hpd | hpq
      · exact hpd
      · exact ih (n / d) hpq hnot
    · exact False.elim (hnot hdiv)

theorem stripList_prime_mem (n : Nat) (factors : List Nat) (p : Nat) (hp : 2 ≤ p)
    (hp_prime : ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b)
    (hdiv : p ∣ n) (hstrip : stripList n factors = 1) :
    ∃ d ∈ factors, p ∣ d := by
  unfold stripList at hstrip
  induction factors generalizing n with
  | nil =>
    simp at hstrip
    rw [hstrip] at hdiv
    have := Nat.le_of_dvd (by omega) hdiv
    omega
  | cons d ds ih =>
    simp only [List.foldl_cons] at hstrip
    by_cases hpd : p ∣ stripFactorFuel n n d
    · rcases ih (stripFactorFuel n n d) hpd hstrip with ⟨x, hx, hpx⟩
      exact ⟨x, List.mem_cons_of_mem d hx, hpx⟩
    · exact ⟨d, List.mem_cons_self .., stripFactorFuel_dvd_prop n n d p hp_prime hdiv hpd⟩

/-- Elementary primality check by trial division up to `n - 1` (exact, decidable). -/
def isPrimeCheck (p : Nat) : Bool :=
  p ≥ 2 && (List.range p).all (fun d => d < 2 || p % d != 0)

theorem isPrimeCheck_sound (p : Nat) (h : isPrimeCheck p = true) :
    2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → ¬ (d ∣ p) := by
  unfold isPrimeCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
             Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨h.1, ?_⟩
  intro d hd1 hd2 hdvd
  have hspec := h.2 d hd2
  rcases hspec with hlt | hne
  · omega
  · exact hne (Nat.mod_eq_zero_of_dvd hdvd)

/-- Euclid's lemma for `isPrimeCheck`: if `p` passes `isPrimeCheck` and `p ∣ a * b`, then `p ∣ a ∨ p ∣ b`. -/
theorem isPrimeCheck_dvd_mul (p : Nat) (hp : isPrimeCheck p = true) :
    ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b := by
  have ⟨hp2, hnodiv⟩ := isPrimeCheck_sound p hp
  intro a b hab
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    have hcop : Nat.gcd p a = 1 := by
      have hg_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
      have hg_le : Nat.gcd p a ≤ p := Nat.le_of_dvd (by omega) hg_dvd_p
      have hg_pos : 1 ≤ Nat.gcd p a := Nat.pos_of_ne_zero (by
        intro h0
        have := Nat.gcd_eq_zero_iff.mp h0
        omega)
      by_cases h1 : Nat.gcd p a = 1
      · exact h1
      · by_cases hEq : Nat.gcd p a = p
        · have : p ∣ a := hEq ▸ Nat.gcd_dvd_right p a
          exact False.elim (hpa this)
        · exact False.elim (hnodiv (Nat.gcd p a) (by omega) (by omega) hg_dvd_p)
    -- Use Nat.Coprime.dvd_of_dvd_mul_left
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop) hab

/-- Every integer `m ≥ 2` has a prime divisor passing `isPrimeCheck`. -/
theorem exists_prime_dvd (m : Nat) (hm : 2 ≤ m) :
    ∃ p, isPrimeCheck p = true ∧ p ∣ m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hp : isPrimeCheck m = true
    · exact ⟨m, hp, Nat.dvd_refl m⟩
    · -- m is composite, so there exists 2 ≤ d < m with d ∣ m
      unfold isPrimeCheck at hp
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
                 Bool.or_eq_true, bne_iff_ne, ne_eq] at hp
      have hex : ∃ d, 2 ≤ d ∧ d < m ∧ d ∣ m := by
        -- Constructively find smallest divisor >= 2
        let rec findDiv (d : Nat) (hd : 2 ≤ d) :
            (∀ k, 2 ≤ k → k < d → ¬ k ∣ m) → d ≤ m → ∃ x, 2 ≤ x ∧ x < m ∧ x ∣ m := by
          intro hprev hle
          by_cases hdm : d = m
          · subst hdm
            exfalso
            apply hp
            refine ⟨hm, fun k hk => ?_⟩
            by_cases hk2 : k < 2
            · exact Or.inl hk2
            · right
              intro hmod
              exact hprev k (by omega) hk (Nat.dvd_of_mod_eq_zero hmod)
          · by_cases hdiv : m % d = 0
            · exact ⟨d, hd, by omega, Nat.dvd_of_mod_eq_zero hdiv⟩
            · exact findDiv (d + 1) (by omega) (fun k hk1 hk2 hkd => by
                by_cases hkd' : k = d
                · subst hkd'; exact hdiv (Nat.mod_eq_zero_of_dvd hkd)
                · exact hprev k hk1 (by omega) hkd) (by omega)
        exact findDiv 2 (by omega) (fun _ h1 h2 => by omega) hm
      rcases hex with ⟨d, hd2, hdm, hddvd⟩
      rcases ih d hdm hd2 with ⟨p, hpp, hpd⟩
      exact ⟨p, hpp, Nat.dvd_trans hpd hddvd⟩

/-- Reusable Finite Certificate for Exact Minimal Period of an FCSR Orbit. -/
structure ExactPeriodCert where
  q : Nat
  pNeg : Nat
  T : Nat
  primeFactors : List Nat

def ExactPeriodCert.check (cert : ExactPeriodCert) : Bool :=
  (cert.q ≥ 3) &&
  (cert.q % 2 == 1) &&
  (1 ≤ cert.pNeg) &&
  (cert.pNeg < cert.q) &&
  (cert.T ≥ 1) &&
  (stripList cert.T cert.primeFactors == 1) &&
  (cert.primeFactors.all (fun l =>
    isPrimeCheck l && (cert.T % l == 0) &&
    (((powMod 2 (cert.T / l) cert.q + cert.q - 1) * cert.pNeg) % cert.q != 0))) &&
  (((powMod 2 cert.T cert.q + cert.q - 1) * cert.pNeg) % cert.q == 0)

theorem nat_pow_sub_one_dvd_iff (q pNeg E : Nat) (hq : 1 ≤ q) :
    ((q : Int) ∣ (((2 ^ E : Nat) : Int) - 1) * (-(pNeg : Int))) ↔
    (((powMod 2 E q + q - 1) * pNeg) % q = 0) := by
  rw [powMod_eq]
  have hge1 : 1 ≤ 2 ^ E := Nat.pow_pos (by omega)
  have hnat_int : ((q : Int) ∣ (((2 ^ E : Nat) : Int) - 1) * (-(pNeg : Int))) ↔
      q ∣ (2 ^ E - 1) * pNeg := by
    have heq : (((2 ^ E : Nat) : Int) - 1) * (-(pNeg : Int)) = -(((2 ^ E - 1) * pNeg : Nat) : Int) := by
      rw [Int.mul_neg, Int.natCast_mul]
      have : ((2 ^ E - 1 : Nat) : Int) = ((2 ^ E : Nat) : Int) - 1 := by omega
      rw [this]
    rw [heq, Int.dvd_neg]
    exact Int.ofNat_dvd
  rw [hnat_int, Nat.dvd_iff_mod_eq_zero]
  -- Show (2^E - 1) * pNeg ≡ (2^E % q + q - 1) * pNeg (mod q)
  have hmod_eq : ((2 ^ E - 1) * pNeg) % q = (((2 ^ E % q + q - 1) * pNeg) % q) := by
    have hdm := Nat.div_add_mod (2 ^ E) q
    have h2 : 2 ^ E - 1 + q = q * (2 ^ E / q) + (2 ^ E % q + q - 1) := by omega
    have h3 : (2 ^ E - 1) * pNeg + q * pNeg = q * ((2 ^ E / q) * pNeg) + (2 ^ E % q + q - 1) * pNeg := by
      calc (2 ^ E - 1) * pNeg + q * pNeg = (2 ^ E - 1 + q) * pNeg := (Nat.add_mul _ _ _).symm
        _ = (q * (2 ^ E / q) + (2 ^ E % q + q - 1)) * pNeg := by rw [h2]
        _ = q * ((2 ^ E / q) * pNeg) + (2 ^ E % q + q - 1) * pNeg := by rw [Nat.add_mul, Nat.mul_assoc]
    have hl : ((2 ^ E - 1) * pNeg + q * pNeg) % q = ((2 ^ E - 1) * pNeg) % q := Nat.add_mul_mod_self_left _ _ _
    have hr : (q * ((2 ^ E / q) * pNeg) + (2 ^ E % q + q - 1) * pNeg) % q = ((2 ^ E % q + q - 1) * pNeg) % q :=
      Nat.mul_add_mod _ _ _
    rw [← hl, h3, hr]
  rw [hmod_eq]

/-- ENGINE THEOREM 3B: Soundness of the Computable Finite Exact-Period Certificate Checker. -/
theorem ExactPeriodCert.sound (cert : ExactPeriodCert) (h : cert.check = true) :
    ∃ (hq_ge : 3 ≤ cert.q) (hq_odd : cert.q % 2 = 1),
      let spec := FCSRSpec.ofOdd cert.q hq_ge hq_odd
      let s := spec.encode (-(cert.pNeg : Int))
      spec.InCore s ∧ spec.IsExactPeriod s cert.T := by
  unfold ExactPeriodCert.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hq3, hqodd⟩, hp1⟩, hpq⟩, hT1⟩, hstrip⟩, hfacs⟩, hTmod⟩
  refine ⟨hq3, hqodd, ?_⟩
  intro spec s
  have hspec_q : spec.q = cert.q := FCSRSpec.ofOdd_q cert.q hq3 hqodd
  have hs_pot : spec.potential s = -(cert.pNeg : Int) := spec.potential_encode _
  have hs_core : spec.InCore s := by
    unfold FCSRSpec.InCore FCSRSpec.qInt
    rw [hs_pot, hspec_q]; omega
  refine ⟨hs_core, hT1, ?_, ?_⟩
  · -- Period divides T
    rw [spec.stepN_eq_iff_dvd hs_core cert.T, hs_pot]
    unfold FCSRSpec.qInt
    rw [hspec_q]
    exact (nat_pow_sub_one_dvd_iff cert.q cert.pNeg cert.T (by omega)).2 hTmod
  · -- Minimality: no 0 < t < T satisfies stepN t s = s
    intro t ht0 htlt hteq
    have hTeq : spec.stepN cert.T s = s := by
      rw [spec.stepN_eq_iff_dvd hs_core cert.T, hs_pot]
      unfold FCSRSpec.qInt
      rw [hspec_q]
      exact (nat_pow_sub_one_dvd_iff cert.q cert.pNeg cert.T (by omega)).2 hTmod
    let g := Nat.gcd t cert.T
    have hgeq : spec.stepN g s = s := spec.stepN_gcd_eq s t cert.T hteq hTeq
    have hg_dvd_T : g ∣ cert.T := Nat.gcd_dvd_right t cert.T
    have hg_le_t : g ≤ t := Nat.le_of_dvd ht0 (Nat.gcd_dvd_left t cert.T)
    have hg_pos : 1 ≤ g := Nat.pos_of_ne_zero (by
      intro h0
      have := Nat.gcd_eq_zero_iff.mp h0
      omega)
    have hquot_ge2 : 2 ≤ cert.T / g := by
      have hdm : g * (cert.T / g) = cert.T := Nat.mul_div_cancel' hg_dvd_T
      have : g < cert.T := by omega
      by_cases h1 : cert.T / g ≤ 1
      · have : g * (cert.T / g) ≤ g * 1 := Nat.mul_le_mul_left g h1
        omega
      · omega
    rcases exists_prime_dvd (cert.T / g) hquot_ge2 with ⟨p, hpp, hp_dvd_quot⟩
    have hp_dvd_T : p ∣ cert.T := by
      have hdm : g * (cert.T / g) = cert.T := Nat.mul_div_cancel' hg_dvd_T
      rw [← hdm]
      exact Nat.dvd_trans hp_dvd_quot (Nat.dvd_mul_left _ _)
    have ⟨hp2, _⟩ := isPrimeCheck_sound p hpp
    rcases stripList_prime_mem cert.T cert.primeFactors p hp2 (isPrimeCheck_dvd_mul p hpp) hp_dvd_T hstrip with
      ⟨l, hl_mem, hp_dvd_l⟩
    have hl_spec := hfacs l hl_mem
    have ⟨hl2, hlnodiv⟩ := isPrimeCheck_sound l hl_spec.1.1
    have hpl : p = l := by
      have hple : p ≤ l := Nat.le_of_dvd (by omega) hp_dvd_l
      by_cases heq : p = l
      · exact heq
      · exact False.elim (hlnodiv p hp2 (by omega) hp_dvd_l)
    subst hpl
    -- Now g * p ∣ T, so g ∣ T / p
    have hg_dvd_Tp : g ∣ cert.T / p := by
      rcases hp_dvd_quot with ⟨m, hm⟩
      have hdm : g * (cert.T / g) = cert.T := Nat.mul_div_cancel' hg_dvd_T
      rw [hm] at hdm
      -- g * (p * m) = T => p * (g * m) = T => T / p = g * m
      have hTpm : p * (g * m) = cert.T := by
        calc p * (g * m) = g * (p * m) := by rw [Nat.mul_left_comm]
          _ = cert.T := hdm
      refine ⟨m, ?_⟩
      have : cert.T / p = g * m := by
        rw [← hTpm, Nat.mul_div_right _ (by omega)]
      exact this
    rcases hg_dvd_Tp with ⟨k, hk⟩
    have hTpeq : spec.stepN (cert.T / p) s = s := by
      rw [hk]; exact spec.stepN_mul_eq s g k hgeq
    have hdvd_Tp := (spec.stepN_eq_iff_dvd hs_core (cert.T / p)).1 hTpeq
    rw [hs_pot] at hdvd_Tp
    unfold FCSRSpec.qInt at hdvd_Tp
    rw [hspec_q] at hdvd_Tp
    have hmod_zero := (nat_pow_sub_one_dvd_iff cert.q cert.pNeg (cert.T / p) (by omega)).1 hdvd_Tp
    exact hl_spec.2 hmod_zero

-- ============================================================================
-- Section 4: The d-Section Cyclotomic Potential & Bit-Weight Engine
-- ============================================================================

theorem repunit_mul_pred (d k : Nat) :
    repunit d k * (2 ^ k - 1) = 2 ^ (d * k) - 1 := by
  induction d with
  | zero => simp [repunit, sumNat]
  | succ m ih =>
    unfold repunit at ih ⊢
    simp only [sumNat]
    rw [Nat.add_mul, ih]
    have hpow_ge1 : 1 ≤ 2 ^ k := Nat.pow_pos (by omega)
    have hpow_m_ge1 : 1 ≤ 2 ^ (m * k) := Nat.pow_pos (by omega)
    have hmul : 2 ^ (m * k) * (2 ^ k - 1) + 2 ^ (m * k) = 2 ^ ((m + 1) * k) := by
      calc 2 ^ (m * k) * (2 ^ k - 1) + 2 ^ (m * k)
          = 2 ^ (m * k) * (2 ^ k - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = 2 ^ (m * k) * 2 ^ k := by rw [Nat.sub_add_cancel hpow_ge1]
        _ = 2 ^ (m * k + k) := (Nat.pow_add 2 (m * k) k).symm
        _ = 2 ^ ((m + 1) * k) := by rw [Nat.succ_mul]
    omega

/-- ENGINE THEOREM 4: The `d`-Section Cyclotomic Potential, Bit-Recurrence & Carry-Conservation Engine.
    For ANY odd `q ≥ 3`, ANY `d ≥ 2`, `k ≥ 1` with `q ∣ ∑_{j=0}^{d-1} 2^(j*k)`, and ANY `s ∈ P_q`:
    (1) `step^(d*k) s = s`,
    (2) `∀ t, 1 ≤ c(t) ≤ d - 1` and `S(t) = -q * c(t)`,
    (3) `∀ t, c(t + k) = c(t)`,
    (4) `∀ t, ∑_{j=0}^{d-1} a_{t + j*k} = 2 * c(t + 1) - c(t)`,
    (5) `∑_{t=0}^{d*k-1} a_t = ∑_{t=0}^{k-1} c(t)`,
    (6) `∑_{t=0}^{d*k-1} m_t = (w(q+1) - 1) * ∑_{t=0}^{k-1} c(t)`. -/
theorem dSection_cyclotomic_engine (spec : FCSRSpec) {s : FCSRState spec} (hs : spec.InCore s)
    (d k : Nat) (hd : 2 ≤ d) (hq_dvd : spec.q ∣ repunit d k) :
    spec.stepN (d * k) s = s ∧
    (∀ t, 1 ≤ spec.sectionQuantum s d k t ∧ spec.sectionQuantum s d k t ≤ (d : Int) - 1) ∧
    (∀ t, spec.sectionSum s d k t = -spec.qInt * spec.sectionQuantum s d k t) ∧
    (∀ t, spec.sectionQuantum s d k (t + k) = spec.sectionQuantum s d k t) ∧
    (∀ t, sumInt d (fun j => (outBit (spec.stepN (t + j * k) s) : Int)) =
          2 * spec.sectionQuantum s d k (t + 1) - spec.sectionQuantum s d k t) ∧
    sumInt (d * k) (fun t => (outBit (spec.stepN t s) : Int)) =
      sumInt k (fun t => spec.sectionQuantum s d k t) ∧
    sumInt (d * k) (fun t => (spec.stepN t s).carry) =
      ((spec.tapWeight : Int) - 1) * sumInt k (fun t => spec.sectionQuantum s d k t) := by
  -- Step 1: q ∣ 2^(d*k) - 1, hence stepN (d * k) s = s
  have hper : spec.stepN (d * k) s = s := by
    rw [spec.stepN_eq_iff_dvd hs (d * k)]
    have hd1 : spec.q ∣ 2 ^ (d * k) - 1 := by
      rw [← repunit_mul_pred d k]
      exact Nat.dvd_trans hq_dvd (Nat.dvd_mul_right _ _)
    have hd2 : spec.qInt ∣ (((2 ^ (d * k) : Nat) : Int) - 1) := by
      have hge1 : 1 ≤ 2 ^ (d * k) := Nat.pow_pos (by omega)
      have : (((2 ^ (d * k) - 1 : Nat) : Int)) = ((2 ^ (d * k) : Nat) : Int) - 1 := by omega
      rw [← this]
      exact Int.ofNat_dvd.mpr hd1
    exact Int.dvd_mul_of_dvd_left hd2
  -- Step 2: q ∣ sectionSum t for every t
  have hS_dvd : ∀ t, spec.qInt ∣ spec.sectionSum s d k t := by
    intro t
    have hmul_dvd : spec.qInt ∣ ((2 ^ ((d - 1) * k) : Nat) : Int) * spec.sectionSum s d k t := by
      unfold sectionSum
      rw [← sumInt_mul_left]
      have hterm : ∀ j, j < d →
          spec.qInt ∣ (((2 ^ ((d - 1) * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s) -
                       ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * spec.potential (spec.stepN t s)) := by
        intro j hj
        have hmod := spec.stepN_potential_mod (spec.stepN t s) (j * k)
        rw [← stepN_add] at hmod
        have hmul : spec.qInt ∣ ((2 ^ ((d - 1 - j) * k) : Nat) : Int) *
            (((2 ^ (j * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s) - spec.potential (spec.stepN t s)) :=
          Int.dvd_mul_of_dvd_right hmod
        have hpow : (2 ^ ((d - 1 - j) * k) : Nat) * (2 ^ (j * k) : Nat) = 2 ^ ((d - 1) * k) := by
          rw [← Nat.pow_add, ← Nat.add_mul]
          congr 2; omega
        have hpowI : ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * ((2 ^ (j * k) : Nat) : Int) =
            ((2 ^ ((d - 1) * k) : Nat) : Int) := by exact_mod_cast hpow
        have halg : ((2 ^ ((d - 1 - j) * k) : Nat) : Int) *
            (((2 ^ (j * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s) - spec.potential (spec.stepN t s)) =
            ((2 ^ ((d - 1) * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s) -
            ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * spec.potential (spec.stepN t s) := by
          rw [Int.mul_sub, ← Int.mul_assoc, hpowI]
        rw [halg] at hmul
        exact hmul
      have hsum_diff : spec.qInt ∣
          (sumInt d (fun j => ((2 ^ ((d - 1) * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s)) -
           sumInt d (fun j => ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * spec.potential (spec.stepN t s))) := by
        rw [← sumInt_sub]
        have aux : ∀ m, m ≤ d →
            spec.qInt ∣ sumInt m (fun j =>
              ((2 ^ ((d - 1) * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s) -
              ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * spec.potential (spec.stepN t s)) := by
          intro m hm
          induction m with
          | zero => simp [sumInt]
          | succ r ihr =>
            simp only [sumInt]
            exact Int.dvd_add (ihr (by omega)) (hterm r (by omega))
        exact aux d (Nat.le_refl d)
      have hrev : sumNat d (fun j => 2 ^ ((d - 1 - j) * k)) = repunit d k := by
        unfold repunit
        have aux_rev : ∀ m (f : Nat → Nat),
            sumNat m (fun j => f (m - 1 - j)) = sumNat m f := by
          intro m f
          induction m generalizing f with
          | zero => rfl
          | succ r ihr =>
            simp only [sumNat, Nat.add_sub_cancel, Nat.sub_self]
            have hshift : sumNat r (fun j => f (r - j)) = sumNat r (fun j => f (r - 1 - j + 1)) := by
              apply sumNat_congr; intro j hj; congr 1; omega
            rw [hshift, ihr (fun j => f (j + 1))]
            clear ihr hshift
            have hadd : ∀ n, sumNat n (fun j => f (j + 1)) + f 0 = f n + sumNat n f := by
              intro n
              induction n with
              | zero => simp [sumNat]
              | succ u ihu => simp only [sumNat]; omega
            have := hadd r
            omega
        exact aux_rev d (fun j => 2 ^ (j * k))
      have h2_dvd : spec.qInt ∣ sumInt d (fun j => ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * spec.potential (spec.stepN t s)) := by
        rw [sumInt_mul_right, sumInt_ofNat, hrev]
        exact Int.dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hq_dvd)
      have hadd := Int.dvd_add hsum_diff h2_dvd
      have hcancel : (sumInt d (fun j => ((2 ^ ((d - 1) * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s)) -
          sumInt d (fun j => ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * spec.potential (spec.stepN t s))) +
          sumInt d (fun j => ((2 ^ ((d - 1 - j) * k) : Nat) : Int) * spec.potential (spec.stepN t s)) =
          sumInt d (fun j => ((2 ^ ((d - 1) * k) : Nat) : Int) * spec.potential (spec.stepN (t + j * k) s)) := by omega
      rw [hcancel] at hadd
      exact hadd
    exact odd_dvd_of_dvd_pow2_mul spec.q spec.q_odd ((d - 1) * k) _ hmul_dvd
  -- Step 3: Exact quantization S(t) = -q * c(t) and bounds 1 ≤ c(t) ≤ d - 1
  have hSeq : ∀ t, spec.sectionSum s d k t = -spec.qInt * spec.sectionQuantum s d k t := by
    intro t
    rcases hS_dvd t with ⟨m, hm⟩
    unfold sectionQuantum
    have hqp := spec.qInt_pos
    have hneg : -spec.sectionSum s d k t = spec.qInt * (-m) := by rw [hm, Int.mul_neg]
    rw [hneg, Int.mul_ediv_cancel_left (-m) (by omega), Int.neg_mul, Int.mul_neg, Int.neg_neg]
    exact hm
  have hbounds : ∀ t, 1 ≤ spec.sectionQuantum s d k t ∧ spec.sectionQuantum s d k t ≤ (d : Int) - 1 := by
    intro t
    have hlo : -((d : Int) * spec.qInt) < spec.sectionSum s d k t := by
      unfold sectionSum
      have h1 : sumInt d (fun _ => -spec.qInt) < sumInt d (fun j => spec.potential (spec.stepN (t + j * k) s)) :=
        sumInt_lt d _ _ (by omega) (fun j _ => (spec.stepN_inCore (t + j * k) hs).1)
      rw [sumInt_const, Int.mul_neg] at h1
      exact h1
    have hhi : spec.sectionSum s d k t < 0 := by
      unfold sectionSum
      have h1 : sumInt d (fun j => spec.potential (spec.stepN (t + j * k) s)) < sumInt d (fun _ => (0 : Int)) :=
        sumInt_lt d _ _ (by omega) (fun j _ => (spec.stepN_inCore (t + j * k) hs).2)
      rw [sumInt_const, Int.mul_zero] at h1
      exact h1
    rw [hSeq t] at hlo hhi
    have hqp := spec.qInt_pos
    constructor
    · if h1 : 1 ≤ spec.sectionQuantum s d k t then exact h1
      else
        have hle0 : spec.sectionQuantum s d k t ≤ 0 := by omega
        have : spec.qInt * spec.sectionQuantum s d k t ≤ spec.qInt * 0 :=
          Int.mul_le_mul_of_nonneg_left hle0 (by omega)
        rw [Int.neg_mul] at hhi; omega
    · if h2 : spec.sectionQuantum s d k t ≤ (d : Int) - 1 then exact h2
      else
        have hge : (d : Int) ≤ spec.sectionQuantum s d k t := by omega
        have : spec.qInt * (d : Int) ≤ spec.qInt * spec.sectionQuantum s d k t :=
          Int.mul_le_mul_of_nonneg_left hge (by omega)
        rw [Int.neg_mul] at hlo
        rw [Int.mul_comm] at this
        omega
  -- Step 4: Periodicity c(t + k) = c(t)
  have hc_per : ∀ t, spec.sectionQuantum s d k (t + k) = spec.sectionQuantum s d k t := by
    intro t
    unfold sectionQuantum
    congr 1; congr 1
    unfold sectionSum
    have hshift : sumInt d (fun j => spec.potential (spec.stepN (t + k + j * k) s)) =
        sumInt d (fun j => spec.potential (spec.stepN (t + (j + 1) * k) s)) := by
      apply sumInt_congr; intro j _; congr 2; rw [Nat.succ_mul]; omega
    rw [hshift]
    apply sumInt_shift_one d (fun j => spec.potential (spec.stepN (t + j * k) s))
    rw [Nat.add_comm t (d * k), stepN_add, hper]
    simp
  -- Step 5: Master bit-section recurrence: ∑_{j=0}^{d-1} a_{t + j*k} = 2 * c(t+1) - c(t)
  have hbit_rec : ∀ t, sumInt d (fun j => (outBit (spec.stepN (t + j * k) s) : Int)) =
      2 * spec.sectionQuantum s d k (t + 1) - spec.sectionQuantum s d k t := by
    intro t
    have hstep_sum : spec.sectionSum s d k t =
        spec.qInt * sumInt d (fun j => (outBit (spec.stepN (t + j * k) s) : Int)) +
        2 * spec.sectionSum s d k (t + 1) := by
      unfold sectionSum
      rw [← sumInt_mul_left, ← sumInt_mul_left, ← sumInt_add]
      apply sumInt_congr; intro j _
      have h1 := spec.potential_step (spec.stepN (t + j * k) s)
      have h2 : spec.step (spec.stepN (t + j * k) s) = spec.stepN (t + 1 + j * k) s := by
        rw [← stepN_succ_right]; congr 1; omega
      rw [h2] at h1
      exact h1
    rw [hSeq t, hSeq (t + 1)] at hstep_sum
    have hqp := spec.qInt_pos
    have hmul_eq : spec.qInt * sumInt d (fun j => (outBit (spec.stepN (t + j * k) s) : Int)) =
        spec.qInt * (2 * spec.sectionQuantum s d k (t + 1) - spec.sectionQuantum s d k t) := by
      rw [Int.neg_mul, Int.neg_mul] at hstep_sum
      rw [Int.mul_sub]
      have h2 : 2 * -(spec.qInt * spec.sectionQuantum s d k (t + 1)) =
          -(spec.qInt * (2 * spec.sectionQuantum s d k (t + 1))) := by
        rw [Int.mul_neg, Int.mul_left_comm]
      rw [h2] at hstep_sum
      omega
    have hdiff : spec.qInt * (sumInt d (fun j => (outBit (spec.stepN (t + j * k) s) : Int)) -
        (2 * spec.sectionQuantum s d k (t + 1) - spec.sectionQuantum s d k t)) = 0 := by
      rw [Int.mul_sub]; omega
    rcases Int.mul_eq_zero.mp hdiff with hq0 | h0
    · omega
    · omega
  -- Step 6: Exact total bit weight and total carry sum over d * k steps
  have htot_bits : sumInt (d * k) (fun t => (outBit (spec.stepN t s) : Int)) =
      sumInt k (fun t => spec.sectionQuantum s d k t) := by
    rw [sumInt_mul_split, sumInt_swap]
    have h1 : sumInt k (fun t => sumInt d (fun j => (outBit (spec.stepN (j * k + t) s) : Int))) =
        sumInt k (fun t => 2 * spec.sectionQuantum s d k (t + 1) - spec.sectionQuantum s d k t) := by
      apply sumInt_congr; intro t _
      have hcomm : sumInt d (fun j => (outBit (spec.stepN (j * k + t) s) : Int)) =
          sumInt d (fun j => (outBit (spec.stepN (t + j * k) s) : Int)) := by
        apply sumInt_congr; intro j _; rw [Nat.add_comm]
      rw [hcomm, hbit_rec t]
    rw [h1, sumInt_sub, sumInt_mul_left]
    have hsh : sumInt k (fun t => spec.sectionQuantum s d k (t + 1)) =
        sumInt k (fun t => spec.sectionQuantum s d k t) :=
      sumInt_shift_one k (fun t => spec.sectionQuantum s d k t) (by simpa using hc_per 0)
    rw [hsh]
    change 2 * sumInt k (fun t => spec.sectionQuantum s d k t) -
        sumInt k (fun t => spec.sectionQuantum s d k t) =
        sumInt k (fun t => spec.sectionQuantum s d k t)
    omega
  have htot_carries : sumInt (d * k) (fun t => (spec.stepN t s).carry) =
      ((spec.tapWeight : Int) - 1) * sumInt k (fun t => spec.sectionQuantum s d k t) := by
    rw [spec.universal_carry_bit_conservation s (d * k) hper, htot_bits]
  exact ⟨hper, hbounds, hSeq, hc_per, hbit_rec, htot_bits, htot_carries⟩


-- ============================================================================
-- Section 5: Zolotarev Silicon Permutation-Parity Engine (100% Self-Contained)
-- ============================================================================

end FCSRSpec

def xorNat (n : Nat) (f : Nat → Bool) : Bool :=
  match n with
  | 0 => false
  | k + 1 => xor (xorNat k f) (f k)

theorem xorNat_congr {n : Nat} {f g : Nat → Bool}
    (h : ∀ i, i < n → f i = g i) : xorNat n f = xorNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [xorNat]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem xorNat_false (n : Nat) : xorNat n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ k ih => simp [xorNat, ih]

theorem xorNat_xor (n : Nat) (f g : Nat → Bool) :
    xorNat n (fun i => xor (f i) (g i)) = xor (xorNat n f) (xorNat n g) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [xorNat, ih]
    cases xorNat k f <;> cases xorNat k g <;> cases f k <;> cases g k <;> rfl

theorem xorNat_swap (a b : Nat) (f : Nat → Nat → Bool) :
    xorNat a (fun i => xorNat b (fun j => f i j)) =
    xorNat b (fun j => xorNat a (fun i => f i j)) := by
  induction a with
  | zero =>
    simp only [xorNat]
    exact (xorNat_false b).symm
  | succ k ih =>
    simp only [xorNat, ih, ← xorNat_xor]

theorem xorNat_split (a b : Nat) (f : Nat → Bool) :
    xorNat (a + b) f = xor (xorNat a f) (xorNat b (fun i => f (a + i))) := by
  induction b with
  | zero => simp [xorNat]
  | succ k ih =>
    rw [← Nat.add_assoc]
    simp only [xorNat, ih]
    cases xorNat a f <;> cases xorNat k (fun i => f (a + i)) <;> cases f (a + k) <;> rfl

theorem xorNat_replace_one (n p : Nat) (hp : p < n) (f : Nat → Bool) (v : Bool) :
    xorNat n (fun i => if i = p then v else f i) =
    xor (xorNat n f) (xor (f p) v) := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [xorNat]
    by_cases hpk : p = k
    · subst hpk
      have hleft : xorNat p (fun i => if i = p then v else f i) = xorNat p f := by
        apply xorNat_congr; intro i hi
        have hne : i ≠ p := by omega
        simp [hne]
      rw [hleft]
      simp only [ite_true]
      cases xorNat p f <;> cases f p <;> cases v <;> rfl
    · have hlt : p < k := by omega
      have hne : k ≠ p := by omega
      simp only [hne, ite_false]
      rw [ih hlt]
      cases xorNat k f <;> cases f k <;> cases f p <;> cases v <;> rfl

/-- Bijection structure on `{0, ..., n - 1}`. -/
structure FinBij (n : Nat) where
  toFun : Nat → Nat
  invFun : Nat → Nat
  map_lt : ∀ i, i < n → toFun i < n
  inv_lt : ∀ i, i < n → invFun i < n
  left_inv : ∀ i, i < n → invFun (toFun i) = i
  right_inv : ∀ i, i < n → toFun (invFun i) = i

theorem FinBij.inj {n : Nat} (π : FinBij n) {i j : Nat} (hi : i < n) (hj : j < n)
    (h : π.toFun i = π.toFun j) : i = j := by
  have h1 := π.left_inv i hi
  have h2 := π.left_inv j hj
  rw [h] at h1
  omega

/-- Bijection invariance of Boolean XOR reduction over `{0, ..., n - 1}`. -/
theorem xorNat_bijection (n : Nat) (π : FinBij n) (f : Nat → Bool) :
    xorNat n (fun i => f (π.toFun i)) = xorNat n f := by
  induction n with
  | zero => rfl
  | succ k ih =>
    let p := π.invFun k
    have hp_lt : p < k + 1 := π.inv_lt k (by omega)
    have hpi_p : π.toFun p = k := π.right_inv k (by omega)
    by_cases hpk : p = k
    · -- π fixes k, so π restricts to a bijection on {0, ..., k - 1}
      have hpi_k : π.toFun k = k := by rw [hpk] at hpi_p; exact hpi_p
      let π' : FinBij k := {
        toFun := π.toFun
        invFun := π.invFun
        map_lt := fun i hi => by
          have hlt := π.map_lt i (by omega)
          have hne : π.toFun i ≠ k := by
            intro heq
            have : i = k := π.inj (by omega) (by omega) (heq.trans hpi_k.symm)
            omega
          omega
        inv_lt := fun i hi => by
          have hlt := π.inv_lt i (by omega)
          have hne : π.invFun i ≠ k := by
            intro heq
            have : i = k := by
              have := π.right_inv i (by omega)
              rw [heq, hpi_k] at this; omega
            omega
          omega
        left_inv := fun i hi => π.left_inv i (by omega)
        right_inv := fun i hi => π.right_inv i (by omega)
      }
      simp only [xorNat, hpi_k]
      rw [ih π']
    · -- p < k: swap outputs at p and k to restrict to {0, ..., k - 1}
      have hp_lt_k : p < k := by omega
      have hpi_k_lt : π.toFun k < k := by
        have hlt := π.map_lt k (by omega)
        have hne : π.toFun k ≠ k := by
          intro heq
          have : k = p := π.inj (by omega) hp_lt (heq.trans hpi_p.symm)
          omega
        omega
      let π' : FinBij k := {
        toFun := fun i => if i = p then π.toFun k else π.toFun i
        invFun := fun j => if j = π.toFun k then p else π.invFun j
        map_lt := fun i hi => by
          split
          · exact hpi_k_lt
          · rename_i hne
            have hlt := π.map_lt i (by omega)
            have hnek : π.toFun i ≠ k := by
              intro heq
              have : i = p := π.inj (by omega) hp_lt (heq.trans hpi_p.symm)
              exact hne this
            omega
        inv_lt := fun j hj => by
          split
          · exact hp_lt_k
          · rename_i hne
            have hlt := π.inv_lt j (by omega)
            have hnek : π.invFun j ≠ k := by
              intro heq
              have : j = π.toFun k := by
                have := π.right_inv j (by omega)
                rw [heq] at this; exact this.symm
              exact hne this
            omega
        left_inv := fun i hi => by
          by_cases hip : i = p
          · subst hip; simp
          · simp only [hip, ite_false]
            have hne : π.toFun i ≠ π.toFun k := by
              intro heq
              have : i = k := π.inj (by omega) (by omega) heq
              omega
            simp only [hne, ite_false]
            exact π.left_inv i (by omega)
        right_inv := fun j hj => by
          by_cases hjk : j = π.toFun k
          · subst hjk; simp
          · simp only [hjk, ite_false]
            have hne : π.invFun j ≠ p := by
              intro heq
              have : j = k := by
                have := π.right_inv j (by omega)
                rw [heq, hpi_p] at this; exact this.symm
              omega
            simp only [hne, ite_false]
            exact π.right_inv j (by omega)
      }
      have hih := ih π'
      have hrep : xorNat k (fun i => f (π'.toFun i)) =
          xor (xorNat k (fun i => f (π.toFun i))) (xor (f (π.toFun p)) (f (π.toFun k))) := by
        have heq : xorNat k (fun i => f (π'.toFun i)) =
            xorNat k (fun i => if i = p then f (π.toFun k) else f (π.toFun i)) := by
          apply xorNat_congr; intro i _; dsimp only [π']; split <;> rfl
        rw [heq]
        exact xorNat_replace_one k p hp_lt_k (fun i => f (π.toFun i)) (f (π.toFun k))
      rw [hpi_p] at hrep
      simp only [xorNat]
      rw [← hih, hrep]
      cases xorNat k (fun i => f (π.toFun i)) <;> cases f k <;> cases f (π.toFun k) <;> rfl

/-- Inversion parity of a permutation on `{0, ..., n - 1}`:
    XOR over all pairs `(i, j)` of `[i < j ∧ f j < f i]`. -/
def invParity (n : Nat) (f : Nat → Nat) : Bool :=
  xorNat n (fun i => xorNat n (fun j => decide (i < j ∧ f j < f i)))

theorem invParity_id (n : Nat) : invParity n id = false := by
  unfold invParity
  dsimp only [id]
  have h1 : ∀ i, i < n → xorNat n (fun j => decide (i < j ∧ j < i)) = false := by
    intro i _
    rw [xorNat_congr (g := fun _ => false) (fun j _ => by simp; omega)]
    exact xorNat_false n
  rw [xorNat_congr h1]
  exact xorNat_false n

def FinBij.comp {n : Nat} (f g : FinBij n) : FinBij n where
  toFun := fun i => f.toFun (g.toFun i)
  invFun := fun i => g.invFun (f.invFun i)
  map_lt := fun i hi => f.map_lt _ (g.map_lt i hi)
  inv_lt := fun i hi => g.inv_lt _ (f.inv_lt i hi)
  left_inv := fun i hi => by rw [f.left_inv _ (g.map_lt i hi), g.left_inv i hi]
  right_inv := fun i hi => by rw [g.right_inv _ (f.inv_lt i hi), f.right_inv i hi]

def FinBij.idBij (n : Nat) : FinBij n where
  toFun := id
  invFun := id
  map_lt := fun _ hi => hi
  inv_lt := fun _ hi => hi
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

def FinBij.iter {n : Nat} (π : FinBij n) : Nat → FinBij n
  | 0 => FinBij.idBij n
  | k + 1 => FinBij.comp π (π.iter k)

/-- ENGINE THEOREM 5A: Pure-Silicon Permutation Parity Homomorphism (`invParity (f ∘ g) = invParity f ⊕ invParity g`). -/
theorem invParity_comp {n : Nat} (f g : FinBij n) :
    invParity n (fun i => f.toFun (g.toFun i)) = xor (invParity n f.toFun) (invParity n g.toFun) := by
  -- Pointwise decomposition for every i < n, j < n:
  -- [i < j ∧ f(g j) < f(g i)] = [i < j ∧ g j < g i] ⊕ [i < j ∧ g i < g j ∧ f(g j) < f(g i)] ⊕ [i < j ∧ g j < g i ∧ f(g i) < f(g j)]
  have hpt : ∀ i, i < n → ∀ j, j < n →
      decide (i < j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)) =
      xor (decide (i < j ∧ g.toFun j < g.toFun i))
          (xor (decide (i < j ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)))
               (decide (i < j ∧ g.toFun j < g.toFun i ∧ f.toFun (g.toFun i) < f.toFun (g.toFun j)))) := by
    intro i hi j hj
    by_cases hij : i < j
    · have hgne : g.toFun i ≠ g.toFun j := fun heq => by
        have := g.inj hi hj heq; omega
      have hfne : f.toFun (g.toFun i) ≠ f.toFun (g.toFun j) := fun heq => by
        have := f.inj (g.map_lt i hi) (g.map_lt j hj) heq
        exact hgne this
      by_cases hglt : g.toFun i < g.toFun j <;> by_cases hflt : f.toFun (g.toFun i) < f.toFun (g.toFun j)
      · have h1 : ¬ g.toFun j < g.toFun i := by omega
        have h2 : ¬ f.toFun (g.toFun j) < f.toFun (g.toFun i) := by omega
        simp [hij, hglt, hflt, h1, h2]
      · have h1 : ¬ g.toFun j < g.toFun i := by omega
        have h2 : f.toFun (g.toFun j) < f.toFun (g.toFun i) := by omega
        simp [hij, hglt, hflt, h1, h2]
      · have h1 : g.toFun j < g.toFun i := by omega
        have h2 : ¬ f.toFun (g.toFun j) < f.toFun (g.toFun i) := by omega
        simp [hij, hglt, hflt, h1, h2]
      · have h1 : g.toFun j < g.toFun i := by omega
        have h2 : f.toFun (g.toFun j) < f.toFun (g.toFun i) := by omega
        simp [hij, hglt, hflt, h1, h2]
    · simp [hij]
  unfold invParity
  have h1 : xorNat n (fun i => xorNat n (fun j => decide (i < j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)))) =
      xorNat n (fun i => xorNat n (fun j =>
        xor (decide (i < j ∧ g.toFun j < g.toFun i))
            (xor (decide (i < j ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)))
                 (decide (i < j ∧ g.toFun j < g.toFun i ∧ f.toFun (g.toFun i) < f.toFun (g.toFun j)))))) := by
    apply xorNat_congr; intro i hi; apply xorNat_congr; intro j hj; exact hpt i hi j hj
  rw [h1]
  have hsplit1 : ∀ i,
      xorNat n (fun j => xor (decide (i < j ∧ g.toFun j < g.toFun i))
          (xor (decide (i < j ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)))
               (decide (i < j ∧ g.toFun j < g.toFun i ∧ f.toFun (g.toFun i) < f.toFun (g.toFun j))))) =
      xor (xorNat n (fun j => decide (i < j ∧ g.toFun j < g.toFun i)))
          (xor (xorNat n (fun j => decide (i < j ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i))))
               (xorNat n (fun j => decide (i < j ∧ g.toFun j < g.toFun i ∧ f.toFun (g.toFun i) < f.toFun (g.toFun j))))) := by
    intro i; rw [xorNat_xor, xorNat_xor]
  simp only [hsplit1, xorNat_xor]
  -- Swap i and j in the third term!
  rw [xorNat_swap n n (fun i j => decide (i < j ∧ g.toFun j < g.toFun i ∧ f.toFun (g.toFun i) < f.toFun (g.toFun j)))]
  -- Combine the second and third terms!
  rw [← xorNat_xor]
  have hcombine :
      xorNat n (fun i => xor
        (xorNat n (fun j => decide (i < j ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i))))
        (xorNat n (fun j => decide (j < i ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i))))) =
      xorNat n (fun i => xorNat n (fun j => decide (g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)))) := by
    apply xorNat_congr; intro i _
    rw [← xorNat_xor]
    apply xorNat_congr; intro j _
    by_cases hcond : g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)
    · have hne : i ≠ j := by intro heq; subst heq; omega
      by_cases hij : i < j
      · have hji : ¬ j < i := by omega
        simp [hcond, hij, hji]
      · have hji : j < i := by omega
        simp [hcond, hij, hji]
    · have h1 : ¬ (i < j ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)) := fun hc => hcond hc.2
      have h2 : ¬ (j < i ∧ g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i)) := fun hc => hcond hc.2
      simp [hcond]
  rw [hcombine]
  -- Now apply xorNat_bijection on j, then on i!
  have hbij_j : ∀ i,
      xorNat n (fun j => decide (g.toFun i < g.toFun j ∧ f.toFun (g.toFun j) < f.toFun (g.toFun i))) =
      xorNat n (fun v => decide (g.toFun i < v ∧ f.toFun v < f.toFun (g.toFun i))) := by
    intro i
    exact xorNat_bijection n g (fun v => decide (g.toFun i < v ∧ f.toFun v < f.toFun (g.toFun i)))
  simp only [hbij_j]
  rw [xorNat_bijection n g (fun u => xorNat n (fun v => decide (u < v ∧ f.toFun v < f.toFun u)))]
  exact Bool.xor_comm _ _

theorem invParity_iter {n : Nat} (π : FinBij n) (k : Nat) :
    invParity n (π.iter k).toFun = (decide (k % 2 = 1) && invParity n π.toFun) := by
  induction k with
  | zero => simp [FinBij.iter, FinBij.idBij, invParity_id]
  | succ m ih =>
    have hcomp : (π.iter (m + 1)).toFun = fun i => π.toFun ((π.iter m).toFun i) := rfl
    rw [hcomp, invParity_comp, ih]
    have hmod : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · have hs : (m + 1) % 2 = 1 := by omega
      rw [h0, hs]; cases invParity n π.toFun <;> rfl
    · have hs : (m + 1) % 2 = 0 := by omega
      rw [h1, hs]; cases invParity n π.toFun <;> rfl

/-- The FCSR periodic-core permutation `π_q(x) = 2x mod q` indexed on `{0, ..., q - 2}` (representing `x = i + 1`). -/
def mul2Bij (q : Nat) (hq_odd : q % 2 = 1) (hq : 3 ≤ q) : FinBij (q - 1) where
  toFun := fun i => (2 * (i + 1)) % q - 1
  invFun := fun j =>
    let y := j + 1
    (if y % 2 = 0 then y / 2 else (y + q) / 2) - 1
  map_lt := fun i hi => by
    have hmod_pos : 1 ≤ (2 * (i + 1)) % q := by
      by_cases hlt : 2 * (i + 1) < q
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · have h2lt : 2 * (i + 1) - q < q := by omega
        have heq : 2 * (i + 1) = (2 * (i + 1) - q) + q := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt h2lt]
        -- 2 * (i + 1) is even, q is odd => 2 * (i + 1) ≠ q
        omega
    have hmod_lt : (2 * (i + 1)) % q < q := Nat.mod_lt _ (by omega)
    omega
  inv_lt := fun j hj => by
    dsimp only; split <;> omega
  left_inv := fun i hi => by
    dsimp only
    by_cases hlt : 2 * (i + 1) < q
    · rw [Nat.mod_eq_of_lt hlt]
      have h1 : 2 * (i + 1) - 1 + 1 = 2 * (i + 1) := by omega
      rw [h1]; simp
    · have h2lt : 2 * (i + 1) - q < q := by omega
      have heq : 2 * (i + 1) = (2 * (i + 1) - q) + q := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt h2lt]
      have hodd : (2 * (i + 1) - q - 1 + 1) % 2 = 1 := by omega
      have hne : ¬ (2 * (i + 1) - q - 1 + 1) % 2 = 0 := by omega
      simp [hne]; omega
  right_inv := fun j hj => by
    dsimp only
    split <;> rename_i heven
    · have h1 : (j + 1) / 2 - 1 + 1 = (j + 1) / 2 := by omega
      rw [h1]
      have h2 : 2 * ((j + 1) / 2) = j + 1 := by omega
      rw [h2, Nat.mod_eq_of_lt (by omega)]; omega
    · have h1 : (j + 1 + q) / 2 - 1 + 1 = (j + 1 + q) / 2 := by omega
      rw [h1]
      have h2 : 2 * ((j + 1 + q) / 2) = (j + 1) + q := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

theorem mul2Bij_iter_eq (q : Nat) (hq_odd : q % 2 = 1) (hq : 3 ≤ q) (k i : Nat) (hi : i < q - 1) :
    ((mul2Bij q hq_odd hq).iter k).toFun i + 1 = (2 ^ k * (i + 1)) % q := by
  induction k with
  | zero =>
    simp [FinBij.iter, FinBij.idBij]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  | succ m ih =>
    have hlt_m : ((mul2Bij q hq_odd hq).iter m).toFun i < q - 1 :=
      ((mul2Bij q hq_odd hq).iter m).map_lt i hi
    have hstep : ((mul2Bij q hq_odd hq).iter (m + 1)).toFun i =
        (2 * (((mul2Bij q hq_odd hq).iter m).toFun i + 1)) % q - 1 := rfl
    rw [hstep, ih]
    have hmod_pos : 1 ≤ (2 * ((2 ^ m * (i + 1)) % q)) % q := by
      have h1 : (2 * ((2 ^ m * (i + 1)) % q)) % q = (2 * (2 ^ m * (i + 1))) % q := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [h1]
      -- Since i + 1 < q and q is odd, q cannot divide 2^(m+1) * (i + 1)
      have hndvd : ¬ q ∣ 2 ^ (m + 1) * (i + 1) := by
        intro hd
        have hdI : (q : Int) ∣ ((2 ^ (m + 1) : Nat) : Int) * ((i + 1 : Nat) : Int) := by
          exact_mod_cast hd
        have hqi := FCSRSpec.odd_dvd_of_dvd_pow2_mul q hq_odd (m + 1) ((i + 1 : Nat) : Int) hdI
        have hqnat : q ∣ i + 1 := Int.ofNat_dvd.mp hqi
        have hle := Nat.le_of_dvd (by omega) hqnat
        omega
      have hpow : 2 * (2 ^ m * (i + 1)) = 2 ^ (m + 1) * (i + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc]
      rw [hpow]
      have hne0 : (2 ^ (m + 1) * (i + 1)) % q ≠ 0 := by
        intro h0; exact hndvd (Nat.dvd_of_mod_eq_zero h0)
      omega
    have hpow : (2 * ((2 ^ m * (i + 1)) % q)) % q = (2 ^ (m + 1) * (i + 1)) % q := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ m), ← Nat.pow_succ]
    omega

/-- Helper: XOR of `true` repeated `n` times equals `decide (n % 2 = 1)`. -/
private theorem xorNat_true (n : Nat) : xorNat n (fun _ => true) = decide (n % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ u ihu =>
    simp only [xorNat, ihu]
    have : u % 2 = 0 ∨ u % 2 = 1 := by omega
    rcases this with h0 | h1
    · have hs : (u + 1) % 2 = 1 := by omega
      rw [h0, hs]; rfl
    · have hs : (u + 1) % 2 = 0 := by omega
      rw [h1, hs]; rfl

/-- Helper: XOR of `decide (k ≤ i)` over `k = 0 .. m - 1` equals `decide ((i + 1) % 2 = 1)` for `i < m`. -/
private theorem xorNat_le_count (m i : Nat) (hi : i < m) :
    xorNat m (fun k => decide (k ≤ i)) = decide ((i + 1) % 2 = 1) := by
  induction m with
  | zero => omega
  | succ r ih =>
    simp only [xorNat]
    by_cases hir : i = r
    · subst hir
      have hconst : xorNat i (fun k => decide (k ≤ i)) = xorNat i (fun _ => true) :=
        xorNat_congr (fun k hk => by simp; omega)
      rw [hconst, xorNat_true i]
      simp only [Nat.le_refl, decide_true]
      have : i % 2 = 0 ∨ i % 2 = 1 := by omega
      rcases this with h0 | h1
      · have hs : (i + 1) % 2 = 1 := by omega
        rw [h0, hs]; rfl
      · have hs : (i + 1) % 2 = 0 := by omega
        rw [h1, hs]; rfl
    · have hlt : i < r := by omega
      have hgt : ¬ r ≤ i := by omega
      simp only [hgt, decide_false, Bool.xor_false]
      exact ih hlt

/-- Helper: XOR of `decide ((i + 1) % 2 = 1)` over `i = 0 .. m - 1` equals `decide (m % 4 = 1 ∨ m % 4 = 2)`. -/
private theorem xorNat_tri_parity (m : Nat) :
    xorNat m (fun i => decide ((i + 1) % 2 = 1)) = decide (m % 4 = 1 ∨ m % 4 = 2) := by
  induction m with
  | zero => rfl
  | succ r ih =>
    simp only [xorNat, ih]
    have hmod : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
    rcases hmod with h0 | h1 | h2 | h3
    · have h1' : (r + 1) % 2 = 1 := by omega
      have h2' : (r + 1) % 4 = 1 := by omega
      simp [h0, h1', h2']
    · have h1' : (r + 1) % 2 = 0 := by omega
      have h2' : (r + 1) % 4 = 2 := by omega
      simp [h1, h1', h2']
    · have h1' : (r + 1) % 2 = 1 := by omega
      have h2' : (r + 1) % 4 = 3 := by omega
      simp [h2, h1', h2']
    · have h1' : (r + 1) % 2 = 0 := by omega
      have h2' : (r + 1) % 4 = 0 := by omega
      simp [h3, h1', h2']

/-- ENGINE THEOREM 5B: Pure-Silicon Zolotarev Inversion Parity of the FCSR Core Permutation `π_q`. -/
theorem invParity_mul2Bij (q : Nat) (hq_odd : q % 2 = 1) (hq : 3 ≤ q) :
    invParity (q - 1) (mul2Bij q hq_odd hq).toFun = decide (q % 8 = 3 ∨ q % 8 = 5) := by
  let m := (q - 1) / 2
  let f : Nat → Nat := (mul2Bij q hq_odd hq).toFun
  have hqm : q - 1 = m + m := by omega
  have hq2m : q = 2 * m + 1 := by omega
  have hlow : ∀ i, i < m → f i = 2 * i + 1 := by
    intro i hi
    change (2 * (i + 1)) % q - 1 = 2 * i + 1
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hhigh : ∀ k, k < m → f (m + k) = 2 * k := by
    intro k hk
    change (2 * (m + k + 1)) % q - 1 = 2 * k
    have heq : 2 * (m + k + 1) = (2 * k + 1) + q := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  change invParity (q - 1) f = decide (q % 8 = 3 ∨ q % 8 = 5)
  unfold invParity
  rw [hqm, xorNat_split m m]
  have hsecond : xorNat m (fun u =>
      xorNat (m + m) (fun j => decide (m + u < j ∧ f j < f (m + u)))) = false := by
    rw [xorNat_congr (g := fun _ => false)]
    · exact xorNat_false m
    · intro u hu
      rw [xorNat_split m m]
      have hA : xorNat m (fun j => decide (m + u < j ∧ f j < f (m + u))) = false := by
        rw [xorNat_congr (g := fun _ => false) (fun j hj => by simp; omega)]
        exact xorNat_false m
      have hB : xorNat m (fun v => decide (m + u < m + v ∧ f (m + v) < f (m + u))) = false := by
        rw [xorNat_congr (g := fun _ => false)]
        · exact xorNat_false m
        · intro v hv
          rw [hhigh v hv, hhigh u hu]
          simp; omega
      rw [hA, hB]; rfl
  have hfirst : xorNat m (fun i =>
      xorNat (m + m) (fun j => decide (i < j ∧ f j < f i))) =
      xorNat m (fun i => decide ((i + 1) % 2 = 1)) := by
    apply xorNat_congr; intro i hi
    rw [xorNat_split m m]
    have hA : xorNat m (fun j => decide (i < j ∧ f j < f i)) = false := by
      rw [xorNat_congr (g := fun _ => false)]
      · exact xorNat_false m
      · intro j hj
        rw [hlow j hj, hlow i hi]
        simp; omega
    have hB : xorNat m (fun k => decide (i < m + k ∧ f (m + k) < f i)) =
        decide ((i + 1) % 2 = 1) := by
      rw [xorNat_congr (g := fun k => decide (k ≤ i))]
      · exact xorNat_le_count m i hi
      · intro k hk
        rw [hhigh k hk, hlow i hi]
        by_cases hki : k ≤ i
        · have h1 : i < m + k ∧ 2 * k < 2 * i + 1 := by omega
          simp [hki, h1]
        · have h1 : ¬ (i < m + k ∧ 2 * k < 2 * i + 1) := by omega
          simp [hki, h1]
    rw [hA, hB, Bool.false_xor]
  rw [hfirst, hsecond, Bool.xor_false, xorNat_tri_parity m]
  by_cases hq8 : q % 8 = 3 ∨ q % 8 = 5
  · have hm4 : m % 4 = 1 ∨ m % 4 = 2 := by omega
    simp [hq8, hm4]
  · have hm4 : ¬ (m % 4 = 1 ∨ m % 4 = 2) := by omega
    simp [hq8, hm4]

/-- ENGINE THEOREM 5C: Universal Even-Period Law for ALL `q ≡ 3, 5 (mod 8)` (prime OR composite!). -/
theorem even_period_of_mod8_3_or_5 (q : Nat) (hq_odd : q % 2 = 1) (hq : 3 ≤ q)
    (hmod8 : q % 8 = 3 ∨ q % 8 = 5) (T : Nat) (hpow : 2 ^ T % q = 1) :
    T % 2 = 0 := by
  let π := mul2Bij q hq_odd hq
  have hid : invParity (q - 1) (π.iter T).toFun = false := by
    have hagree : ∀ i, i < q - 1 → (π.iter T).toFun i = i := by
      intro i hi
      have h1 : (π.iter T).toFun i + 1 = (2 ^ T * (i + 1)) % q := mul2Bij_iter_eq q hq_odd hq T i hi
      have h2 : (2 ^ T * (i + 1)) % q = i + 1 := by
        rw [Nat.mul_mod, hpow, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
      rw [h2] at h1
      omega
    unfold invParity
    have hcongr : xorNat (q - 1) (fun i => xorNat (q - 1) (fun j => decide (i < j ∧ (π.iter T).toFun j < (π.iter T).toFun i))) =
        xorNat (q - 1) (fun i => xorNat (q - 1) (fun j => decide (i < j ∧ j < i))) := by
      apply xorNat_congr; intro i hi; apply xorNat_congr; intro j hj
      rw [hagree i hi, hagree j hj]
    rw [hcongr]
    exact invParity_id (q - 1)
  rw [invParity_iter, invParity_mul2Bij q hq_odd hq] at hid
  have htrue : decide (q % 8 = 3 ∨ q % 8 = 5) = true := decide_eq_true hmod8
  rw [htrue, Bool.and_true] at hid
  have hne : ¬ T % 2 = 1 := by
    intro h1; rw [h1] at hid; simp at hid
  omega

-- ============================================================================
-- Section 6: Six Infinite-Family Theorems, Concrete Certificates,
--            Non-Vacuity Witnesses, and Sharpness Counterexamples
-- ============================================================================

namespace Families

/-- Helper: `stepN T (encode (-1)) = encode (-1) ↔ 2 ^ T % q = 1` for ANY odd `q ≥ 3`. -/
theorem stepN_neg1_iff_pow2_mod (spec : FCSRSpec) (T : Nat) :
    spec.stepN T (spec.encode (-1)) = spec.encode (-1) ↔ 2 ^ T % spec.q = 1 := by
  have hcore : spec.InCore (spec.encode (-1)) := by
    unfold FCSRSpec.InCore FCSRSpec.qInt
    rw [spec.potential_encode]
    have := spec.q_ge_three; omega
  rw [spec.stepN_eq_iff_dvd hcore T, spec.potential_encode]
  have hge1 : 1 ≤ 2 ^ T := Nat.pow_pos (by omega)
  have hq3 := spec.q_ge_three
  have hiff : (spec.qInt ∣ (((2 ^ T : Nat) : Int) - 1) * (-1)) ↔ spec.q ∣ 2 ^ T - 1 := by
    have heq : (((2 ^ T : Nat) : Int) - 1) * (-1) = -(((2 ^ T - 1 : Nat) : Int)) := by omega
    rw [heq, Int.dvd_neg]
    exact Int.ofNat_dvd
  rw [hiff, Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h0
    have hdm := Nat.div_add_mod (2 ^ T - 1) spec.q
    have : 2 ^ T = spec.q * ((2 ^ T - 1) / spec.q) + 1 := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · intro h1
    have hdm := Nat.div_add_mod (2 ^ T) spec.q
    have : 2 ^ T - 1 = spec.q * (2 ^ T / spec.q) := by omega
    rw [this, Nat.mul_mod_right]

/-- Helper: `Nat.gcd (2^a - 1) (2^b - 1)` divisibility via `stepN_gcd_eq`!
    If `2^a % q = 1` and `2^b % q = 1`, then `2^(Nat.gcd a b) % q = 1`! -/
theorem pow2_mod_gcd (spec : FCSRSpec) (a b : Nat)
    (ha : 2 ^ a % spec.q = 1) (hb : 2 ^ b % spec.q = 1) :
    2 ^ Nat.gcd a b % spec.q = 1 := by
  rw [← stepN_neg1_iff_pow2_mod] at ha hb ⊢
  exact spec.stepN_gcd_eq (spec.encode (-1)) a b ha hb

-- ----------------------------------------------------------------------------
-- INFINITE FAMILY 1: Mersenne-Form FCSR `q = 2^k - 1` (∀ k ≥ 2)
-- ----------------------------------------------------------------------------

def specPow2Sub1 (k : Nat) (hk : 2 ≤ k) : FCSRSpec where
  c := 2 ^ (k - 1)
  r := k
  hr := by omega
  hc_lo := Nat.le_refl _
  hc_hi := by
    rw [pow2_pred_mul k (by omega)]
    have : 1 ≤ 2 ^ (k - 1) := Nat.pow_pos (by omega)
    omega
  hc_ge2 := by
    have h1 : 1 ≤ k - 1 := by omega
    have := pow2_pred_mul (k - 1) h1
    have : 1 ≤ 2 ^ (k - 1 - 1) := Nat.pow_pos (by omega)
    omega

theorem specPow2Sub1_q (k : Nat) (hk : 2 ≤ k) :
    (specPow2Sub1 k hk).q = 2 ^ k - 1 := by
  unfold specPow2Sub1 FCSRSpec.q
  dsimp only
  rw [← pow2_pred_mul k (by omega)]

theorem sumNat_term_le (n t : Nat) (f : Nat → Nat) (ht : t < n) :
    f t ≤ sumNat n f := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [sumNat]
    by_cases htm : t = m
    · subst htm; omega
    · have := ih (by omega); omega

theorem specPow2Sub1_tapWeight (k : Nat) (hk : 2 ≤ k) :
    (specPow2Sub1 k hk).tapWeight = 1 := by
  unfold FCSRSpec.tapWeight specPow2Sub1
  dsimp only
  have hprev : sumNat (k - 1) (fun j => bit (2 ^ (k - 1)) j) = 0 := by
    rw [sumNat_congr (g := fun _ => 0)]
    · rw [sumNat_const]; omega
    · intro j hj
      unfold bit
      have hpow : 2 ^ (k - 1) = 2 ^ j * 2 ^ (k - 1 - j) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      have h2 := pow2_pred_mul (k - 1 - j) (by omega)
      rw [hpow, Nat.mul_div_right _ (Nat.pow_pos (by omega)), h2]
      omega
  have hsplit : k = (k - 1) + 1 := by omega
  have hlast : sumNat k (fun j => bit (2 ^ (k - 1)) j) =
      sumNat (k - 1) (fun j => bit (2 ^ (k - 1)) j) + bit (2 ^ (k - 1)) (k - 1) := by
    conv => lhs; arg 1; rw [hsplit]
    rfl
  rw [hlast, hprev]
  unfold bit
  rw [Nat.div_self (Nat.pow_pos (by omega))]

/-- INFINITE THEOREM 1 (`q = 2^k - 1`, ∀ k ≥ 2):
    Zero carry identically on `P_q`, exact universal period `k`, `W_k(s) = -P_q(s)`,
    and exact minimal period `k` on `encode (-1)` — PLUS universal sharpness:
    half-period complementation FAILS on `encode (-1)` for ALL `k ≥ 3`! -/
theorem family_pow2_sub_1 (k : Nat) (hk : 2 ≤ k) :
    let spec := specPow2Sub1 k hk
    spec.q = 2 ^ k - 1 ∧
    spec.tapWeight = 1 ∧
    (∀ s, spec.InCore s → s.carry = 0 ∧ spec.stepN k s = s ∧ (spec.wordRun s k : Int) = -spec.potential s) ∧
    spec.IsExactPeriod (spec.encode (-1)) k ∧
    (3 ≤ k → ∀ h, spec.stepN h (spec.encode (-1)) ≠ spec.complement (spec.encode (-1))) := by
  intro spec
  have hq : spec.q = 2 ^ k - 1 := specPow2Sub1_q k hk
  have hw : spec.tapWeight = 1 := specPow2Sub1_tapWeight k hk
  have hpowk : 2 ^ k % spec.q = 1 := by
    rw [hq]
    have hge2 : 2 ≤ 2 ^ k - 1 := by
      have := spec.q_ge_three; omega
    have heq : 2 ^ k = 1 + (2 ^ k - 1) := by omega
    conv => lhs; arg 1; rw [heq]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hcore_all : ∀ s, spec.InCore s → s.carry = 0 ∧ spec.stepN k s = s ∧ (spec.wordRun s k : Int) = -spec.potential s := by
    intro s hs
    have ⟨hc0, hc1⟩ := spec.carry_bounds_on_core hs
    rw [hw] at hc1
    have hcz : s.carry = 0 := by omega
    have hper : spec.stepN k s = s := by
      rw [spec.stepN_eq_iff_dvd hs k]
      have hd : spec.qInt ∣ (((2 ^ k : Nat) : Int) - 1) := by
        refine ⟨1, ?_⟩
        unfold FCSRSpec.qInt; rw [hq]
        have : 1 ≤ 2 ^ k := Nat.pow_pos (by omega)
        omega
      exact Int.dvd_mul_of_dvd_left hd
    have hword : (spec.wordRun s k : Int) = -spec.potential s := by
      have hw_ex := spec.word_representation_exact s k
      rw [hper] at hw_ex
      have hqeq : spec.qInt = ((2 ^ k : Nat) : Int) - 1 := by
        unfold FCSRSpec.qInt; rw [hq]
        have : 1 ≤ 2 ^ k := Nat.pow_pos (by omega); omega
      have hmul : spec.qInt * ((spec.wordRun s k : Int) + spec.potential s) = 0 := by
        rw [Int.mul_add]
        have : ((2 ^ k : Nat) : Int) * spec.potential s - spec.potential s = spec.qInt * spec.potential s := by
          rw [hqeq, Int.sub_mul, Int.one_mul]
        omega
      have hqp := spec.qInt_pos
      rcases Int.mul_eq_zero.mp hmul with h0 | h0
      · omega
      · omega
    exact ⟨hcz, hper, hword⟩
  have hmin : spec.IsExactPeriod (spec.encode (-1)) k := by
    refine ⟨by omega, (stepN_neg1_iff_pow2_mod spec k).2 hpowk, ?_⟩
    intro t ht0 htlt hteq
    rw [stepN_neg1_iff_pow2_mod] at hteq
    have hlt : 2 ^ t < 2 ^ k - 1 := by
      have hle : 2 ^ t ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 := pow2_pred_mul k (by omega)
      have hge2 : 2 ≤ 2 ^ (k - 1) := by
        have := pow2_pred_mul (k - 1) (by omega)
        have : 1 ≤ 2 ^ (k - 1 - 1) := Nat.pow_pos (by omega)
        omega
      omega
    rw [hq, Nat.mod_eq_of_lt hlt] at hteq
    have h2le : 2 ≤ 2 ^ t := by
      have := pow2_pred_mul t (by omega)
      have : 1 ≤ 2 ^ (t - 1) := Nat.pow_pos (by omega)
      omega
    omega
  have hsharp : 3 ≤ k → ∀ h, spec.stepN h (spec.encode (-1)) ≠ spec.complement (spec.encode (-1)) := by
    intro hk3 h hcomp
    let s := spec.encode (-1)
    have hs : spec.InCore s := by
      unfold FCSRSpec.InCore FCSRSpec.qInt; rw [spec.potential_encode]; have := spec.q_ge_three; omega
    have hper : spec.stepN k s = s := (hcore_all s hs).2.1
    -- Sum of bits over k steps starting at (stepN h s) equals sum starting at s!
    have hsum_h : sumInt k (fun t => (FCSRSpec.outBit (spec.stepN t (spec.stepN h s)) : Int)) =
        sumInt k (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) := by
      have hrew : sumInt k (fun t => (FCSRSpec.outBit (spec.stepN t (spec.stepN h s)) : Int)) =
          sumInt k (fun t => (FCSRSpec.outBit (spec.stepN (t + h) s) : Int)) := by
        apply sumInt_congr; intro t _; rw [← FCSRSpec.stepN_add, Nat.add_comm]
      rw [hrew]
      exact sumInt_shift k h (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int))
        (fun t => by rw [Nat.add_comm t k, FCSRSpec.stepN_add, hper])
    -- Meanwhile sum of bits starting at complement s is k - sum starting at s!
    have hsum_c : sumInt k (fun t => (FCSRSpec.outBit (spec.stepN t (spec.complement s)) : Int)) =
        (k : Int) - sumInt k (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) := by
      have h1 : sumInt k (fun t => (FCSRSpec.outBit (spec.stepN t (spec.complement s)) : Int)) =
          sumInt k (fun t => 1 - (FCSRSpec.outBit (spec.stepN t s) : Int)) := by
        apply sumInt_congr; intro t _
        rw [spec.complement_stepN, spec.complement_outBit]
        have := FCSRSpec.outBit_lt_two (spec.stepN t s); omega
      rw [h1, sumInt_sub, sumInt_const, Int.mul_one]
    -- Compute sum of bits of s = encode (-1) directly: wordRun s k = 1 => outBit 0 = 1 and outBit t = 0 for 1 ≤ t < k!
    have hwk : spec.wordRun s k = 1 := by
      have h1 := (hcore_all s hs).2.2
      rw [spec.potential_encode] at h1
      omega
    have hbits_s : sumInt k (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = 1 := by
      -- Since wordRun s k = sumNat k (fun t => outBit (stepN t s) * 2^t) = 1:
      -- outBit 0 = 1 and for 1 ≤ t < k, outBit t = 0 (otherwise wordRun ≥ 2^t ≥ 2)!
      have hbit_eq : ∀ t, t < k → FCSRSpec.outBit (spec.stepN t s) = if t = 0 then 1 else 0 := by
        intro t ht
        have h1 : FCSRSpec.outBit (spec.stepN t s) * 2 ^ t ≤ spec.wordRun s k :=
          sumNat_term_le k t (fun t => FCSRSpec.outBit (spec.stepN t s) * 2 ^ t) ht
        by_cases ht0 : t = 0
        · subst ht0
          simp only [ite_true]
          have h0 : (FCSRSpec.outBit (spec.stepN 0 s) : Int) = spec.potential s % 2 :=
            spec.outBit_eq_potential_emod s
          rw [spec.potential_encode] at h0
          omega
        · simp only [ht0, ite_false]
          have h2 : 2 ≤ 2 ^ t := by
            have := pow2_pred_mul t (by omega)
            have : 1 ≤ 2 ^ (t - 1) := Nat.pow_pos (by omega)
            omega
          by_cases hob : FCSRSpec.outBit (spec.stepN t s) = 0
          · exact hob
          · have hge : 1 ≤ FCSRSpec.outBit (spec.stepN t s) := by omega
            have hmul : 1 * 2 ^ t ≤ FCSRSpec.outBit (spec.stepN t s) * 2 ^ t :=
              Nat.mul_le_mul_right _ hge
            omega
      rw [sumInt_congr (fun t ht => by rw [hbit_eq t ht])]
      have haux : ∀ m, sumInt (m + 1) (fun t => ((if t = 0 then 1 else 0 : Nat) : Int)) = 1 := by
        intro m
        induction m with
        | zero => simp [sumInt]
        | succ r ihr =>
          change sumInt (r + 1) (fun t => ((if t = 0 then 1 else 0 : Nat) : Int)) +
            ((if r + 1 = 0 then 1 else 0 : Nat) : Int) = 1
          rw [ihr]; simp
      have hk_eq : k = (k - 1) + 1 := by omega
      conv => lhs; arg 1; rw [hk_eq]
      exact haux (k - 1)
    rw [hcomp, hsum_c, hbits_s] at hsum_h
    omega
  exact ⟨hq, hw, hcore_all, hmin, hsharp⟩

-- ----------------------------------------------------------------------------
-- INFINITE FAMILY 2: Fermat-Form FCSR `q = 2^k + 1` (∀ k ≥ 1)
-- ----------------------------------------------------------------------------

/-- INFINITE THEOREM 2 (`q = 2^k + 1`, ∀ k ≥ 1):
    Universal half-period complementation at `h = k` (bits + carries + 50/50 balance),
    exact minimal period `2 * k` on `encode (-1)`, and for `k ≥ 2`, `tapWeight = 2` (single-bit carry). -/
theorem family_pow2_add_1 (k : Nat) (hk : 1 ≤ k) :
    ∃ (hq3 : 3 ≤ 2 ^ k + 1) (hqo : (2 ^ k + 1) % 2 = 1),
      let spec := FCSRSpec.ofOdd (2 ^ k + 1) hq3 hqo
      spec.q = 2 ^ k + 1 ∧
      (∀ s, spec.InCore s →
        spec.stepN k s = spec.complement s ∧
        spec.stepN (2 * k) s = s ∧
        (∀ t, FCSRSpec.outBit (spec.stepN (t + k) s) = 1 - FCSRSpec.outBit (spec.stepN t s)) ∧
        (∀ t, (spec.stepN (t + k) s).carry = (spec.tapWeight : Int) - 1 - (spec.stepN t s).carry) ∧
        sumInt (2 * k) (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = (k : Int) ∧
        sumInt (2 * k) (fun t => (spec.stepN t s).carry) = (k : Int) * ((spec.tapWeight : Int) - 1)) ∧
      spec.IsExactPeriod (spec.encode (-1)) (2 * k) := by
  have hpow2 : 2 ≤ 2 ^ k := by
    have := pow2_pred_mul k hk
    have : 1 ≤ 2 ^ (k - 1) := Nat.pow_pos (by omega)
    omega
  have hq3 : 3 ≤ 2 ^ k + 1 := by omega
  have hqo : (2 ^ k + 1) % 2 = 1 := by
    have := pow2_pred_mul k hk; omega
  refine ⟨hq3, hqo, ?_⟩
  intro spec
  have hq : spec.q = 2 ^ k + 1 := FCSRSpec.ofOdd_q _ hq3 hqo
  have hhalf : ∀ s, spec.InCore s →
      spec.stepN k s = spec.complement s ∧
      spec.stepN (2 * k) s = s ∧
      (∀ t, FCSRSpec.outBit (spec.stepN (t + k) s) = 1 - FCSRSpec.outBit (spec.stepN t s)) ∧
      (∀ t, (spec.stepN (t + k) s).carry = (spec.tapWeight : Int) - 1 - (spec.stepN t s).carry) ∧
      sumInt (2 * k) (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = (k : Int) ∧
      sumInt (2 * k) (fun t => (spec.stepN t s).carry) = (k : Int) * ((spec.tapWeight : Int) - 1) := by
    intro s hs
    apply spec.halfPeriod_certificate hs k
    have hd : spec.qInt ∣ (((2 ^ k : Nat) : Int) + 1) := by
      refine ⟨1, ?_⟩; unfold FCSRSpec.qInt; rw [hq]; omega
    exact Int.dvd_mul_of_dvd_left hd
  have hcore1 : spec.InCore (spec.encode (-1)) := by
    unfold FCSRSpec.InCore FCSRSpec.qInt; rw [spec.potential_encode]; rw [hq]; omega
  have hmin : spec.IsExactPeriod (spec.encode (-1)) (2 * k) := by
    refine ⟨by omega, (hhalf _ hcore1).2.1, ?_⟩
    intro t ht0 htlt hteq
    rw [stepN_neg1_iff_pow2_mod] at hteq
    by_cases htk : t < k
    · have hlt : 2 ^ t < 2 ^ k + 1 := by
        have := Nat.pow_lt_pow_right (a := 2) (by omega) htk; omega
      rw [hq, Nat.mod_eq_of_lt hlt] at hteq
      have h2t : 2 ≤ 2 ^ t := by
        have := pow2_pred_mul t (by omega)
        have : 1 ≤ 2 ^ (t - 1) := Nat.pow_pos (by omega); omega
      omega
    · by_cases heqk : t = k
      · subst heqk
        rw [hq, Nat.mod_eq_of_lt (by omega)] at hteq
        omega
      · -- k < t < 2*k: write t = k + u with 1 ≤ u < k
        -- 2^(k + u) = 2^k * 2^u ≡ -2^u (mod 2^k + 1)
        -- If 2^(k+u) ≡ 1 (mod 2^k + 1), then (2^k + 1) ∣ (2^u + 1), impossible since 2 ≤ 2^u + 1 < 2^k + 1!
        let u := t - k
        have hu1 : 1 ≤ u := by omega
        have huk : u < k := by omega
        have htu : t = k + u := by omega
        have hdvd1 : spec.q ∣ 2 ^ t - 1 := by
          rw [Nat.dvd_iff_mod_eq_zero]
          have hge1 : 1 ≤ 2 ^ t := Nat.pow_pos (by omega)
          have hdm := Nat.div_add_mod (2 ^ t) spec.q
          have : 2 ^ t - 1 = spec.q * (2 ^ t / spec.q) := by omega
          rw [this, Nat.mul_mod_right]
        have hdvd2 : spec.q ∣ 2 ^ u * (2 ^ k + 1) := by
          rw [hq]; exact Nat.dvd_mul_left _ _
        have hsum : 2 ^ u * (2 ^ k + 1) = (2 ^ t - 1) + (2 ^ u + 1) := by
          have hmul : 2 ^ u * (2 ^ k + 1) = 2 ^ t + 2 ^ u := by
            rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add, Nat.add_comm u k, ← htu]
          have hpos : 1 ≤ 2 ^ t := Nat.pow_pos (by omega)
          omega
        have hdvd_u : spec.q ∣ 2 ^ u + 1 := by
          rw [hsum] at hdvd2
          exact (Nat.dvd_add_right hdvd1).mp hdvd2
        have hle := Nat.le_of_dvd (Nat.succ_pos _) hdvd_u
        have hlt : 2 ^ u < 2 ^ k := Nat.pow_lt_pow_right (by omega) huk
        omega
  exact ⟨hq, hhalf, hmin⟩

-- ----------------------------------------------------------------------------
-- INFINITE FAMILY 3: Sparse 2-Tap Family `q = 2^k + 3` (∀ k ≥ 3)
-- ----------------------------------------------------------------------------

theorem specPow2Add3_q (k : Nat) (hk : 3 ≤ k) :
    (specPow2Add3 k hk).q = 2 ^ k + 3 := by
  unfold specPow2Add3 FCSRSpec.q
  dsimp only
  have := pow2_pred_mul k (by omega)
  omega

theorem specPow2Add3_tapWeight (k : Nat) (hk : 3 ≤ k) :
    (specPow2Add3 k hk).tapWeight = 2 := by
  unfold FCSRSpec.tapWeight specPow2Add3
  dsimp only
  have hbit : ∀ j, j < k → bit (2 ^ (k - 1) + 2) j = if j = 1 ∨ j = k - 1 then 1 else 0 := by
    intro j hj
    unfold bit
    by_cases hj1 : j = 1
    · subst hj1
      have hpow : 2 ^ (k - 1) = 4 * 2 ^ (k - 3) := by
        have h4 : (4 : Nat) = 2 ^ 2 := rfl
        rw [h4, ← Nat.pow_add]; congr 1; omega
      rw [hpow]; simp; omega
    · by_cases hjk : j = k - 1
      · subst hjk
        simp only [or_true, ite_true]
        have hge4 : 2 ^ 2 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hlt : 2 < 2 ^ (k - 1) := by omega
        have hdiv : (2 ^ (k - 1) + 2) / 2 ^ (k - 1) = 1 := by
          rw [Nat.add_comm, Nat.add_div_right _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hlt]
        rw [hdiv]
      · simp only [hj1, hjk, or_self, ite_false]
        by_cases hj0 : j = 0
        · subst hj0
          have h1 := pow2_pred_mul (k - 1) (by omega)
          simp; omega
        · have h2le : 2 ≤ j := by omega
          have hpow : 2 ^ (k - 1) = 2 ^ j * (2 * 2 ^ (k - 2 - j)) := by
            have h1 : 2 * 2 ^ (k - 2 - j) = 2 ^ (1 + (k - 2 - j)) := by
              rw [Nat.pow_add, Nat.pow_one]
            rw [h1, ← Nat.pow_add]; congr 1; omega
          have hge4 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h2le
          have h2lt : 2 < 2 ^ j := by omega
          rw [hpow, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega)),
              Nat.div_eq_of_lt h2lt, Nat.zero_add]
          omega
  rw [sumNat_congr hbit]
  have hcount : ∀ m, m + 2 ≤ k - 1 →
      sumNat (m + 2) (fun j => if j = 1 ∨ j = k - 1 then 1 else 0) = 1 := by
    intro m
    induction m with
    | zero =>
      intro hle
      simp only [Nat.zero_add, sumNat]
      simp; omega
    | succ v ihv =>
      intro hle
      change sumNat (v + 2) (fun j => if j = 1 ∨ j = k - 1 then 1 else 0) +
        (if v + 2 = 1 ∨ v + 2 = k - 1 then 1 else 0) = 1
      rw [ihv (by omega)]
      simp; omega
  have hsplit : k = (k - 1) + 1 := by omega
  have hlast : sumNat k (fun j => if j = 1 ∨ j = k - 1 then 1 else 0) =
      sumNat (k - 1) (fun j => if j = 1 ∨ j = k - 1 then 1 else 0) +
      (if k - 1 = 1 ∨ k - 1 = k - 1 then 1 else 0) := by
    conv => lhs; arg 1; rw [hsplit]
    rfl
  rw [hlast]
  have hk2 : k - 1 = (k - 3) + 2 := by omega
  have hc := hcount (k - 3) (by omega)
  rw [← hk2] at hc
  rw [hc]
  simp

/-- INFINITE THEOREM 3 (`q = 2^k + 3`, ∀ k ≥ 3):
    (1) `tapWeight = 2`, hence single-bit carry `0 ≤ m_t ≤ 1` on `P_q` and `∑ m_t = ∑ a_t` on every periodic orbit,
    (2) exact `k`-block coupling: `P(s) + 3 * P(stepN k s) = q * (W_k(s) + P(stepN k s))` with `W_k(s) + P(stepN k s) ∈ {-3, -2, -1}`,
    (3) **Zolotarev Even-Period Law**: EVERY period `T` of `encode (-1)` (and every universal period) is EVEN! -/
theorem family_pow2_add_3 (k : Nat) (hk : 3 ≤ k) :
    let spec := specPow2Add3 k hk
    spec.q = 2 ^ k + 3 ∧
    spec.tapWeight = 2 ∧
    (∀ s, spec.InCore s → 0 ≤ s.carry ∧ s.carry ≤ 1) ∧
    (∀ s, spec.InCore s →
      spec.potential s + 3 * spec.potential (spec.stepN k s) =
        spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) ∧
      -3 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ∧
      (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ -1) ∧
    (∀ T, spec.stepN T (spec.encode (-1)) = spec.encode (-1) → T % 2 = 0) := by
  intro spec
  have hq : spec.q = 2 ^ k + 3 := specPow2Add3_q k hk
  have hw : spec.tapWeight = 2 := specPow2Add3_tapWeight k hk
  have hcarry : ∀ s, spec.InCore s → 0 ≤ s.carry ∧ s.carry ≤ 1 := by
    intro s hs; have := spec.carry_bounds_on_core hs; rw [hw] at this; omega
  have hcouple : ∀ s, spec.InCore s →
      spec.potential s + 3 * spec.potential (spec.stepN k s) =
        spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) ∧
      -3 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ∧
      (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ -1 := by
    intro s hs
    have hrep := spec.word_representation_exact s k
    have hpow : ((2 ^ k : Nat) : Int) = spec.qInt - 3 := by
      unfold FCSRSpec.qInt; rw [hq]; omega
    rw [hpow, Int.sub_mul] at hrep
    have heq : spec.potential s + 3 * spec.potential (spec.stepN k s) =
        spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) := by
      rw [Int.mul_add]; omega
    have hsk := spec.stepN_inCore k hs
    have hqp := spec.qInt_pos
    have hlo : -4 * spec.qInt < spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) := by
      rw [← heq]; have := hs.1; have := hsk.1; omega
    have hhi : spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) < 0 := by
      rw [← heq]; have := hs.2; have := hsk.2; omega
    refine ⟨heq, ?_, ?_⟩
    · if h1 : -3 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) then exact h1
      else
        have hle : (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ -4 := by omega
        have : spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) ≤ spec.qInt * (-4) :=
          Int.mul_le_mul_of_nonneg_left hle (by omega)
        omega
    · if h2 : (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ -1 then exact h2
      else
        have hge : 0 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) := by omega
        have : spec.qInt * 0 ≤ spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) :=
          Int.mul_le_mul_of_nonneg_left hge (by omega)
        omega
  have heven : ∀ T, spec.stepN T (spec.encode (-1)) = spec.encode (-1) → T % 2 = 0 := by
    intro T hT
    rw [stepN_neg1_iff_pow2_mod] at hT
    have hmod8 : spec.q % 8 = 3 ∨ spec.q % 8 = 5 := by
      left
      rw [hq]
      have h8 : 8 ∣ 2 ^ k := by
        refine ⟨2 ^ (k - 3), ?_⟩
        have : 2 ^ k = 2 ^ 3 * 2 ^ (k - 3) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hk]
        simpa using this
      rcases h8 with ⟨m, hm⟩
      rw [hm]; omega
    exact even_period_of_mod8_3_or_5 spec.q spec.q_odd spec.q_ge_three hmod8 T hT
  exact ⟨hq, hw, hcarry, hcouple, heven⟩

-- ----------------------------------------------------------------------------
-- INFINITE FAMILY 4: Maximally-Dense Tap Family `q = 2^k - 3` (∀ k ≥ 3)
-- ----------------------------------------------------------------------------

def specPow2Sub3 (k : Nat) (hk : 3 ≤ k) : FCSRSpec where
  c := 2 ^ (k - 1) - 1
  r := k - 1
  hr := by omega
  hc_lo := by
    have h1 := pow2_pred_mul (k - 1) (by omega)
    have hge2 : 2 ^ 1 ≤ 2 ^ (k - 1 - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  hc_hi := by
    have : 1 ≤ 2 ^ (k - 1) := Nat.pow_pos (by omega); omega
  hc_ge2 := by
    have hge4 : 2 ^ 2 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem specPow2Sub3_q (k : Nat) (hk : 3 ≤ k) :
    (specPow2Sub3 k hk).q = 2 ^ k - 3 := by
  unfold specPow2Sub3 FCSRSpec.q
  dsimp only
  have h1 := pow2_pred_mul k (by omega)
  have hge4 : 2 ^ 2 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem specPow2Sub3_tapWeight (k : Nat) (hk : 3 ≤ k) :
    (specPow2Sub3 k hk).tapWeight = k - 1 := by
  unfold FCSRSpec.tapWeight specPow2Sub3
  dsimp only
  have hall1 : ∀ j, j < k - 1 → bit (2 ^ (k - 1) - 1) j = 1 := by
    intro j hj
    unfold bit
    have hpow : 2 ^ (k - 1) = 2 ^ j * 2 ^ (k - 1 - j) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have h2 : 2 ^ 1 ≤ 2 ^ (k - 1 - j) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 1 ≤ 2 ^ j := Nat.pow_pos (by omega)
    have hle_pow : 2 ^ j ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hrew : 2 ^ (k - 1) - 1 = (2 ^ j - 1) + 2 ^ j * (2 ^ (k - 1 - j) - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← hpow]; omega
    rw [hrew, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have heven : 2 ∣ 2 ^ (k - 1 - j) := ⟨2 ^ (k - 1 - j - 1), pow2_pred_mul (k - 1 - j) (by omega)⟩
    rcases heven with ⟨u, hu⟩
    omega
  rw [sumNat_congr hall1, sumNat_const, Nat.mul_one]

/-- INFINITE THEOREM 4 (`q = 2^k - 3`, ∀ k ≥ 3):
    (1) `tapWeight = k - 1` (maximally dense all-1 taps), carry `0 ≤ m_t ≤ k - 2`,
    (2) exact `k`-block coupling: `P(s) - 3 * P(stepN k s) = q * (W_k(s) + P(stepN k s))` with `W_k(s) + P(stepN k s) ∈ {0, 1, 2}`,
    (3) **Zolotarev Even-Period Law**: EVERY period `T` of `encode (-1)` is EVEN! -/
theorem family_pow2_sub_3 (k : Nat) (hk : 3 ≤ k) :
    let spec := specPow2Sub3 k hk
    spec.q = 2 ^ k - 3 ∧
    spec.tapWeight = k - 1 ∧
    (∀ s, spec.InCore s → 0 ≤ s.carry ∧ s.carry ≤ (k : Int) - 2) ∧
    (∀ s, spec.InCore s →
      spec.potential s - 3 * spec.potential (spec.stepN k s) =
        spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) ∧
      0 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ∧
      (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ 2) ∧
    (∀ T, spec.stepN T (spec.encode (-1)) = spec.encode (-1) → T % 2 = 0) := by
  intro spec
  have hq : spec.q = 2 ^ k - 3 := specPow2Sub3_q k hk
  have hw : spec.tapWeight = k - 1 := specPow2Sub3_tapWeight k hk
  have hcarry : ∀ s, spec.InCore s → 0 ≤ s.carry ∧ s.carry ≤ (k : Int) - 2 := by
    intro s hs; have := spec.carry_bounds_on_core hs; rw [hw] at this; omega
  have hcouple : ∀ s, spec.InCore s →
      spec.potential s - 3 * spec.potential (spec.stepN k s) =
        spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) ∧
      0 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ∧
      (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ 2 := by
    intro s hs
    have hrep := spec.word_representation_exact s k
    have h8le : 8 ≤ 2 ^ k := by
      have : 2 ^ k = 2 ^ 3 * 2 ^ (k - 3) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hk]
      have : 1 ≤ 2 ^ (k - 3) := Nat.pow_pos (by omega); omega
    have hpow : ((2 ^ k : Nat) : Int) = spec.qInt + 3 := by
      unfold FCSRSpec.qInt; rw [hq]; omega
    rw [hpow, Int.add_mul] at hrep
    have heq : spec.potential s - 3 * spec.potential (spec.stepN k s) =
        spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) := by
      rw [Int.mul_add]; omega
    have hsk := spec.stepN_inCore k hs
    have hqp := spec.qInt_pos
    have hlo : -spec.qInt < spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) := by
      rw [← heq]; have := hs.1; have := hsk.2; omega
    have hhi : spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) < 3 * spec.qInt := by
      rw [← heq]; have := hs.2; have := hsk.1; omega
    refine ⟨heq, ?_, ?_⟩
    · if h1 : 0 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) then exact h1
      else
        have hle : (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ -1 := by omega
        have : spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) ≤ spec.qInt * (-1) :=
          Int.mul_le_mul_of_nonneg_left hle (by omega)
        omega
    · if h2 : (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) ≤ 2 then exact h2
      else
        have hge : 3 ≤ (spec.wordRun s k : Int) + spec.potential (spec.stepN k s) := by omega
        have : spec.qInt * 3 ≤ spec.qInt * ((spec.wordRun s k : Int) + spec.potential (spec.stepN k s)) :=
          Int.mul_le_mul_of_nonneg_left hge (by omega)
        omega
  have heven : ∀ T, spec.stepN T (spec.encode (-1)) = spec.encode (-1) → T % 2 = 0 := by
    intro T hT
    rw [stepN_neg1_iff_pow2_mod] at hT
    have hmod8 : spec.q % 8 = 3 ∨ spec.q % 8 = 5 := by
      right
      rw [hq]
      have h8 : 8 ∣ 2 ^ k := by
        refine ⟨2 ^ (k - 3), ?_⟩
        have : 2 ^ k = 2 ^ 3 * 2 ^ (k - 3) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hk]
        simpa using this
      rcases h8 with ⟨m, hm⟩
      have hm1 : 1 ≤ m := by
        cases m with
        | zero => rw [Nat.mul_zero] at hm; have := Nat.pow_pos (a := 2) (n := k) (by omega); omega
        | succ _ => omega
      rw [hm]; omega
    exact even_period_of_mod8_3_or_5 spec.q spec.q_odd spec.q_ge_three hmod8 T hT
  exact ⟨hq, hw, hcarry, hcouple, heven⟩

-- ----------------------------------------------------------------------------
-- INFINITE FAMILY 5: `d`-Section Repunit Family `q = ∑_{j=0}^{d-1} 2^(j*k)` (∀ d ≥ 2, k ≥ 1)
-- ----------------------------------------------------------------------------

theorem repunit_ge_three (d k : Nat) (hd : 2 ≤ d) (hk : 1 ≤ k) :
    3 ≤ FCSRSpec.repunit d k := by
  have aux : ∀ m, 1 + 2 ^ k ≤ FCSRSpec.repunit (m + 2) k := by
    intro m
    induction m with
    | zero => simp [FCSRSpec.repunit, sumNat]
    | succ r ih =>
      exact Nat.le_trans ih (Nat.le_add_right _ _)
  have hd2 : d = (d - 2) + 2 := by omega
  have h1 := aux (d - 2)
  rw [← hd2] at h1
  have h2k : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

theorem repunit_odd (d k : Nat) (hd : 2 ≤ d) (hk : 1 ≤ k) :
    FCSRSpec.repunit d k % 2 = 1 := by
  have aux : ∀ m, FCSRSpec.repunit (m + 1) k % 2 = 1 := by
    intro m
    induction m with
    | zero => simp [FCSRSpec.repunit, sumNat]
    | succ r ih =>
      have hstep : FCSRSpec.repunit (r + 1 + 1) k = FCSRSpec.repunit (r + 1) k + 2 ^ ((r + 1) * k) := rfl
      have hpos : 1 ≤ (r + 1) * k := Nat.mul_pos (by omega) hk
      have heven := pow2_pred_mul ((r + 1) * k) hpos
      rw [hstep, heven]; omega
  have hd1 : d = (d - 1) + 1 := by omega
  rw [hd1]
  exact aux (d - 1)

theorem repunit_gt_pow (d k : Nat) (hd : 2 ≤ d) :
    2 ^ ((d - 1) * k) < FCSRSpec.repunit d k := by
  have hsplit : d = (d - 1) + 1 := by omega
  unfold FCSRSpec.repunit
  have hlast : sumNat d (fun j => 2 ^ (j * k)) =
      sumNat (d - 1) (fun j => 2 ^ (j * k)) + 2 ^ ((d - 1) * k) := by
    conv => lhs; arg 1; rw [hsplit]
    rfl
  rw [hlast]
  have h0 : 1 ≤ sumNat (d - 1) (fun j => 2 ^ (j * k)) := by
    have hterm := sumNat_term_le (d - 1) 0 (fun j => 2 ^ (j * k)) (by omega)
    simp at hterm; exact hterm
  omega

/-- INFINITE THEOREM 5 (Repunit `d`-Section Family `q = (2^(dk) - 1) / (2^k - 1)`, ∀ d ≥ 2, k ≥ 1):
    Full `d`-section cyclotomic conservation law for EVERY periodic state `s ∈ P_q`,
    AND exact minimal period `= d * k` on `encode (-1)`! -/
theorem family_repunit_dSection (d k : Nat) (hd : 2 ≤ d) (hk : 1 ≤ k) :
    ∃ (hq3 : 3 ≤ FCSRSpec.repunit d k) (hqo : FCSRSpec.repunit d k % 2 = 1),
      let spec := FCSRSpec.ofOdd (FCSRSpec.repunit d k) hq3 hqo
      spec.q = FCSRSpec.repunit d k ∧
      spec.IsExactPeriod (spec.encode (-1)) (d * k) ∧
      (∀ s, spec.InCore s →
        (∀ t, 1 ≤ spec.sectionQuantum s d k t ∧ spec.sectionQuantum s d k t ≤ (d : Int) - 1) ∧
        (∀ t, sumInt d (fun j => (FCSRSpec.outBit (spec.stepN (t + j * k) s) : Int)) =
              2 * spec.sectionQuantum s d k (t + 1) - spec.sectionQuantum s d k t) ∧
        sumInt (d * k) (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) =
          sumInt k (fun t => spec.sectionQuantum s d k t) ∧
        sumInt (d * k) (fun t => (spec.stepN t s).carry) =
          ((spec.tapWeight : Int) - 1) * sumInt k (fun t => spec.sectionQuantum s d k t)) := by
  have hq3 := repunit_ge_three d k hd hk
  have hqo := repunit_odd d k hd hk
  refine ⟨hq3, hqo, ?_⟩
  intro spec
  have hq : spec.q = FCSRSpec.repunit d k := FCSRSpec.ofOdd_q _ hq3 hqo
  have hdvd : spec.q ∣ FCSRSpec.repunit d k := by rw [hq]; exact Nat.dvd_refl _
  have hcore1 : spec.InCore (spec.encode (-1)) := by
    unfold FCSRSpec.InCore FCSRSpec.qInt; rw [spec.potential_encode, hq]; omega
  have hdk_pos : 0 < d * k := Nat.mul_pos (by omega) (by omega)
  have heng1 := spec.dSection_cyclotomic_engine hcore1 d k hd hdvd
  have hmin : spec.IsExactPeriod (spec.encode (-1)) (d * k) := by
    refine ⟨hdk_pos, heng1.1, ?_⟩
    intro t ht0 htlt hteq
    have hdk_eq := (stepN_neg1_iff_pow2_mod spec (d * k)).1 heng1.1
    have ht_eq := (stepN_neg1_iff_pow2_mod spec t).1 hteq
    have hg_eq := pow2_mod_gcd spec t (d * k) ht_eq hdk_eq
    let g := Nat.gcd t (d * k)
    have hg_pos : 1 ≤ g := Nat.pos_of_ne_zero (by
      intro h0; have := Nat.gcd_eq_zero_iff.mp h0; omega)
    have hg_dvd : g ∣ d * k := Nat.gcd_dvd_right t (d * k)
    have hg_lt : g < d * k := by
      have := Nat.le_of_dvd ht0 (Nat.gcd_dvd_left t (d * k)); omega
    -- Since g is a proper divisor of d * k, 2 * g ≤ d * k, so g ≤ (d - 1) * k (since d ≥ 2)!
    have hg_le : g ≤ (d - 1) * k := by
      rcases hg_dvd with ⟨m, hm⟩
      have hm2 : 2 ≤ m := by
        cases m with
        | zero => rw [Nat.mul_zero] at hm; omega
        | succ u =>
          cases u with
          | zero => rw [Nat.mul_one] at hm; omega
          | succ _ => omega
      have h2g : 2 * g ≤ d * k := by
        calc 2 * g ≤ m * g := Nat.mul_le_mul_right g hm2
          _ = g * m := Nat.mul_comm m g
          _ = d * k := hm.symm
      have hd2 : d * k ≤ 2 * ((d - 1) * k) := by
        have h1 : d ≤ 2 * (d - 1) := by omega
        calc d * k ≤ (2 * (d - 1)) * k := Nat.mul_le_mul_right k h1
          _ = 2 * ((d - 1) * k) := Nat.mul_assoc 2 (d - 1) k
      omega
    have hpow_le : 2 ^ g ≤ 2 ^ ((d - 1) * k) := Nat.pow_le_pow_right (by omega) hg_le
    have hq_gt := repunit_gt_pow d k hd
    have hlt : 2 ^ g < spec.q := by rw [hq]; omega
    rw [Nat.mod_eq_of_lt hlt] at hg_eq
    have h2g : 2 ≤ 2 ^ g := by
      have := pow2_pred_mul g hg_pos
      have : 1 ≤ 2 ^ (g - 1) := Nat.pow_pos (by omega); omega
    omega
  refine ⟨hq, hmin, ?_⟩
  intro s hs
  have heng := spec.dSection_cyclotomic_engine hs d k hd hdvd
  exact ⟨heng.2.1, heng.2.2.2.2.1, heng.2.2.2.2.2.1, heng.2.2.2.2.2.2⟩

-- ----------------------------------------------------------------------------
-- INFINITE FAMILY 6: Cyclotomic `Phi_6(2^k) = 2^(2k) - 2^k + 1` (∀ k ≥ 2; sharp at k = 1!)
-- ----------------------------------------------------------------------------

/-- INFINITE THEOREM 6 (`q = 2^(2k) - 2^k + 1`, ∀ k ≥ 2):
    Universal half-period complementation at `h = 3 * k` (exact 50/50 bit balance over `6k` ticks)
    AND exact minimal period `= 6 * k` on `encode (-1)`! (Sharp at `k = 1`, where `q = 3, T = 2 ≠ 6`.) -/
theorem family_phi6 (k : Nat) (hk : 2 ≤ k) :
    ∃ (hq3 : 3 ≤ 2 ^ (2 * k) - 2 ^ k + 1) (hqo : (2 ^ (2 * k) - 2 ^ k + 1) % 2 = 1),
      let spec := FCSRSpec.ofOdd (2 ^ (2 * k) - 2 ^ k + 1) hq3 hqo
      spec.q = 2 ^ (2 * k) - 2 ^ k + 1 ∧
      (∀ s, spec.InCore s →
        spec.stepN (3 * k) s = spec.complement s ∧
        spec.stepN (6 * k) s = s ∧
        sumInt (6 * k) (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = (3 * k : Int)) ∧
      spec.IsExactPeriod (spec.encode (-1)) (6 * k) := by
  have h2k_ge4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk; omega
  have h22k_eq : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  have h2k_le : 2 ^ k < 2 ^ (2 * k) := by
    rw [h22k_eq]
    calc 2 ^ k = 2 ^ k * 1 := (Nat.mul_one _).symm
      _ < 2 ^ k * 2 ^ k := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hq3 : 3 ≤ 2 ^ (2 * k) - 2 ^ k + 1 := by
    have hmul : 4 * 2 ^ k ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ h2k_ge4
    omega
  have hqo : (2 ^ (2 * k) - 2 ^ k + 1) % 2 = 1 := by
    have h1 := pow2_pred_mul (2 * k) (by omega)
    have h2 := pow2_pred_mul k (by omega)
    omega
  refine ⟨hq3, hqo, ?_⟩
  intro spec
  have hq : spec.q = 2 ^ (2 * k) - 2 ^ k + 1 := FCSRSpec.ofOdd_q _ hq3 hqo
  -- Key algebraic identity: (2^k + 1) * (2^(2k) - 2^k + 1) = 2^(3k) + 1
  have h3k_fac : (2 ^ k + 1) * spec.q = 2 ^ (3 * k) + 1 := by
    rw [hq]
    have h3 : 2 ^ (3 * k) = 2 ^ k * 2 ^ (2 * k) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h1 : (2 ^ k + 1) * (2 ^ (2 * k) - 2 ^ k + 1) + (2 ^ k + 1) * 2 ^ k =
        (2 ^ k + 1) * (2 ^ (2 * k) + 1) := by
      rw [← Nat.mul_add]
      congr 1; omega
    have h2 : (2 ^ k + 1) * (2 ^ (2 * k) + 1) = 2 ^ (3 * k) + 1 + (2 ^ k + 1) * 2 ^ k := by
      have hL : (2 ^ k + 1) * (2 ^ (2 * k) + 1) = 2 ^ (3 * k) + 2 ^ (2 * k) + 2 ^ k + 1 := by
        rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← h3]; omega
      have hR : (2 ^ k + 1) * 2 ^ k = 2 ^ (2 * k) + 2 ^ k := by
        rw [Nat.add_mul, Nat.one_mul, ← h22k_eq]
      omega
    omega
  have hhalf : ∀ s, spec.InCore s →
      spec.stepN (3 * k) s = spec.complement s ∧
      spec.stepN (6 * k) s = s ∧
      sumInt (6 * k) (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = (3 * k : Int) := by
    intro s hs
    have hcert := spec.halfPeriod_certificate hs (3 * k) (by
      have hd : spec.qInt ∣ (((2 ^ (3 * k) : Nat) : Int) + 1) := by
        refine ⟨((2 ^ k + 1 : Nat) : Int), ?_⟩
        have hI : ((2 ^ k + 1 : Nat) : Int) * (spec.q : Int) = ((2 ^ (3 * k) : Nat) : Int) + 1 := by
          exact_mod_cast h3k_fac
        unfold FCSRSpec.qInt; rw [Int.mul_comm]; exact hI.symm
      exact Int.dvd_mul_of_dvd_left hd)
    have h6 : 2 * (3 * k) = 6 * k := by omega
    rw [h6] at hcert
    exact ⟨hcert.1, hcert.2.1, by simpa using hcert.2.2.2.2.1⟩
  have hcore1 : spec.InCore (spec.encode (-1)) := by
    unfold FCSRSpec.InCore FCSRSpec.qInt; rw [spec.potential_encode, hq]; omega
  have hmin : spec.IsExactPeriod (spec.encode (-1)) (6 * k) := by
    refine ⟨by omega, (hhalf _ hcore1).2.1, ?_⟩
    intro t ht0 htlt hteq
    have h6_eq := (stepN_neg1_iff_pow2_mod spec (6 * k)).1 (hhalf _ hcore1).2.1
    have ht_eq := (stepN_neg1_iff_pow2_mod spec t).1 hteq
    have hg_eq := pow2_mod_gcd spec t (6 * k) ht_eq h6_eq
    let g := Nat.gcd t (6 * k)
    have hg_pos : 1 ≤ g := Nat.pos_of_ne_zero (by
      intro h0; have := Nat.gcd_eq_zero_iff.mp h0; omega)
    have hg_dvd : g ∣ 6 * k := Nat.gcd_dvd_right t (6 * k)
    have hg_lt : g < 6 * k := by
      have := Nat.le_of_dvd ht0 (Nat.gcd_dvd_left t (6 * k)); omega
    rcases hg_dvd with ⟨m, hm⟩
    have hm2 : 2 ≤ m := by
      cases m with
      | zero => rw [Nat.mul_zero] at hm; omega
      | succ u =>
        cases u with
        | zero => rw [Nat.mul_one] at hm; omega
        | succ _ => omega
    have hg_dvd_pow : spec.q ∣ 2 ^ g - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have hge1 : 1 ≤ 2 ^ g := Nat.pow_pos (by omega)
      have hdm := Nat.div_add_mod (2 ^ g) spec.q
      have hge_mod : 2 ^ g % spec.q = 1 := hg_eq
      have : 2 ^ g - 1 = spec.q * (2 ^ g / spec.q) := by omega
      rw [this, Nat.mul_mod_right]
    by_cases hm_eq2 : m = 2
    · rw [hm_eq2] at hm
      have hg3k : g = 3 * k := by omega
      rw [hg3k] at hg_dvd_pow
      have hd3p : spec.q ∣ 2 ^ (3 * k) + 1 := ⟨2 ^ k + 1, by rw [Nat.mul_comm spec.q]; exact h3k_fac.symm⟩
      have hsum : 2 ^ (3 * k) + 1 = (2 ^ (3 * k) - 1) + 2 := by
        have : 1 ≤ 2 ^ (3 * k) := Nat.pow_pos (by omega); omega
      rw [hsum] at hd3p
      have hd2 : spec.q ∣ 2 := (Nat.dvd_add_right hg_dvd_pow).mp hd3p
      have hle := Nat.le_of_dvd (by omega) hd2
      have := spec.q_ge_three; omega
    · by_cases hm_eq3 : m = 3
      · rw [hm_eq3] at hm
        have hg2k : g = 2 * k := by omega
        rw [hg2k] at hg_dvd_pow
        have hadd : 2 ^ (2 * k) - 1 = spec.q + (2 ^ k - 2) := by rw [hq]; omega
        rw [hadd] at hg_dvd_pow
        have hd_sub : spec.q ∣ 2 ^ k - 2 := (Nat.dvd_add_right (Nat.dvd_refl spec.q)).mp hg_dvd_pow
        have hle := Nat.le_of_dvd (by omega) hd_sub
        have hq_big : 2 ^ k < spec.q := by
          rw [hq]
          have hmul : 4 * 2 ^ k ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ h2k_ge4
          omega
        omega
      · -- m ≥ 4 => 4 * g ≤ 6 * k => g ≤ 2 * k - 1 (since k ≥ 2) => 2^g - 1 < q!
        have hm4 : 4 ≤ m := by omega
        have h4g : 4 * g ≤ 6 * k := by
          calc 4 * g ≤ m * g := Nat.mul_le_mul_right g hm4
            _ = g * m := Nat.mul_comm m g
            _ = 6 * k := hm.symm
        have hgle : g ≤ 2 * k - 1 := by omega
        have hpow_le : 2 ^ g ≤ 2 ^ (2 * k - 1) := Nat.pow_le_pow_right (by omega) hgle
        have hhalf2k : 2 ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := pow2_pred_mul (2 * k) (by omega)
        have hpowk_lt : 2 ^ k < 2 ^ (2 * k - 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        have hlt_q : 2 ^ g - 1 < spec.q := by rw [hq]; omega
        have hle := Nat.le_of_dvd (by
          have := pow2_pred_mul g hg_pos
          have : 1 ≤ 2 ^ (g - 1) := Nat.pow_pos (by omega); omega) hg_dvd_pow
        omega
  exact ⟨hq, hhalf, hmin⟩

-- ----------------------------------------------------------------------------
-- Concrete Machine-Checked Certificates, Sharpness Counterexamples & Non-Vacuity
-- ----------------------------------------------------------------------------

/-- Concrete certificate for `q = 11 = 2^3 + 3` (prime): exact minimal period `10` (via `decide`!). -/
def cert_q11 : FCSRSpec.ExactPeriodCert := ⟨11, 1, 10, [2, 5]⟩

theorem cert_q11_valid : cert_q11.check = true := by decide

/-- Concrete certificate for `q = 13 = 2^4 - 3` (prime): exact minimal period `12` (via `decide`!). -/
def cert_q13 : FCSRSpec.ExactPeriodCert := ⟨13, 1, 12, [2, 3]⟩

theorem cert_q13_valid : cert_q13.check = true := by decide

/-- SHARPNESS WITNESS A (`q = 35 = 2^5 + 3`, composite `5 * 7`):
    Exact minimal period `12` (even, as forced by Zolotarev!), YET half-period complementation FAILS! -/
def cert_q35 : FCSRSpec.ExactPeriodCert := ⟨35, 1, 12, [2, 3]⟩

theorem cert_q35_valid : cert_q35.check = true := by decide

theorem sharpness_q35_no_half_period :
    let spec := specPow2Add3 5 (by omega)
    let s := spec.encode (-1)
    spec.q = 35 ∧ spec.IsExactPeriod s 12 ∧ spec.stepN 6 s ≠ spec.complement s := by
  have hsound := FCSRSpec.ExactPeriodCert.sound cert_q35 cert_q35_valid
  rcases hsound with ⟨hq3, hqo, _, hper_c⟩
  let specC := FCSRSpec.ofOdd cert_q35.q hq3 hqo
  have hqC : specC.q = 35 := FCSRSpec.ofOdd_q cert_q35.q hq3 hqo
  intro spec s
  have hq : spec.q = 35 := by rw [specPow2Add3_q 5 (by omega)]
  have hno : spec.stepN 6 s ≠ spec.complement s := by
    intro hcomp
    have hmod := spec.stepN_potential_mod s 6
    rw [hcomp, spec.complement_potential, spec.potential_encode] at hmod
    have h1 : spec.qInt ∣ (((2 ^ 6 : Nat) : Int) + 1) := by
      have hd1 : spec.qInt ∣ ((2 ^ 6 : Nat) : Int) * spec.qInt := ⟨((2 ^ 6 : Nat) : Int), Int.mul_comm _ _⟩
      have hadd := Int.dvd_add hmod hd1
      have halg : (((2 ^ 6 : Nat) : Int) * (-spec.qInt - -1) - -1) + ((2 ^ 6 : Nat) : Int) * spec.qInt =
          ((2 ^ 6 : Nat) : Int) + 1 := by
        rw [Int.mul_sub, Int.mul_neg]; omega
      rw [halg] at hadd
      exact hadd
    unfold FCSRSpec.qInt at h1
    rw [hq] at h1
    have hnat : 35 ∣ 65 := Int.ofNat_dvd.mp h1
    have hmod0 := Nat.mod_eq_zero_of_dvd hnat
    omega
  have hper : spec.IsExactPeriod s 12 := by
    refine ⟨by omega, ?_, ?_⟩
    · rw [stepN_neg1_iff_pow2_mod, hq]
    · intro t ht0 htlt hteq
      rw [stepN_neg1_iff_pow2_mod, hq] at hteq
      have hteq' : specC.stepN t (specC.encode (-1)) = specC.encode (-1) := by
        rw [stepN_neg1_iff_pow2_mod, hqC]; exact hteq
      exact hper_c.2.2 t ht0 htlt hteq'
  exact ⟨hq, hper, hno⟩

/-- SHARPNESS WITNESS B (`q = 253 = 2^8 - 3`, composite `11 * 23`):
    Exact minimal period `110` (even, as forced by Zolotarev!), YET half-period complementation FAILS! -/
def cert_q253 : FCSRSpec.ExactPeriodCert := ⟨253, 1, 110, [2, 5, 11]⟩

theorem cert_q253_valid : cert_q253.check = true := by decide

theorem sharpness_q253_no_half_period :
    let spec := specPow2Sub3 8 (by omega)
    let s := spec.encode (-1)
    spec.q = 253 ∧ spec.IsExactPeriod s 110 ∧ spec.stepN 55 s ≠ spec.complement s := by
  have hsound := FCSRSpec.ExactPeriodCert.sound cert_q253 cert_q253_valid
  rcases hsound with ⟨hq3, hqo, _, hper_c⟩
  let specC := FCSRSpec.ofOdd cert_q253.q hq3 hqo
  have hqC : specC.q = 253 := FCSRSpec.ofOdd_q cert_q253.q hq3 hqo
  intro spec s
  have hq : spec.q = 253 := by rw [specPow2Sub3_q 8 (by omega)]
  have hno : spec.stepN 55 s ≠ spec.complement s := by
    intro hcomp
    have hmod := spec.stepN_potential_mod s 55
    rw [hcomp, spec.complement_potential, spec.potential_encode] at hmod
    have h1 : spec.qInt ∣ (((2 ^ 55 : Nat) : Int) + 1) := by
      have hd1 : spec.qInt ∣ ((2 ^ 55 : Nat) : Int) * spec.qInt := ⟨((2 ^ 55 : Nat) : Int), Int.mul_comm _ _⟩
      have hadd := Int.dvd_add hmod hd1
      have halg : (((2 ^ 55 : Nat) : Int) * (-spec.qInt - -1) - -1) + ((2 ^ 55 : Nat) : Int) * spec.qInt =
          ((2 ^ 55 : Nat) : Int) + 1 := by
        rw [Int.mul_sub, Int.mul_neg]; omega
      rw [halg] at hadd
      exact hadd
    unfold FCSRSpec.qInt at h1
    rw [hq] at h1
    have hnat : 253 ∣ 2 ^ 55 + 1 := Int.ofNat_dvd.mp (by exact_mod_cast h1)
    have hmod0 := Nat.mod_eq_zero_of_dvd hnat
    have hpow : (2 ^ 55 + 1) % 253 = (FCSRSpec.powMod 2 55 253 + 1) % 253 := by
      rw [FCSRSpec.powMod_eq, Nat.add_mod, Nat.add_mod (2 ^ 55 % 253), Nat.mod_mod]
    rw [hpow] at hmod0
    have hne : (FCSRSpec.powMod 2 55 253 + 1) % 253 ≠ 0 := by decide
    exact hne hmod0
  have hper : spec.IsExactPeriod s 110 := by
    refine ⟨by omega, ?_, ?_⟩
    · rw [stepN_neg1_iff_pow2_mod, hq]
    · intro t ht0 htlt hteq
      rw [stepN_neg1_iff_pow2_mod, hq] at hteq
      have hteq' : specC.stepN t (specC.encode (-1)) = specC.encode (-1) := by
        rw [stepN_neg1_iff_pow2_mod, hqC]; exact hteq
      exact hper_c.2.2 t ht0 htlt hteq'
  exact ⟨hq, hper, hno⟩

/-- SHARPNESS WITNESS C: `q = 2^3 + 1 = 9` with non-coprime `p = -3` has exact period `2 < 6 = 2*3`. -/
def cert_q9_p3 : FCSRSpec.ExactPeriodCert := ⟨9, 3, 2, [2]⟩

theorem cert_q9_p3_valid : cert_q9_p3.check = true := by decide

/-- SHARPNESS WITNESS D: `Phi_6(2^k)` boundary `k = 1` gives `q = 3`, exact period `2 ≠ 6*1`. -/
def cert_q3_phi6_k1 : FCSRSpec.ExactPeriodCert := ⟨3, 1, 2, [2]⟩

theorem cert_q3_phi6_k1_valid : cert_q3_phi6_k1.check = true := by decide

/-- SHARPNESS WITNESS E: `q = 7 = 2^3 - 1 ≡ 7 (mod 8)` has ODD exact period `3`,
    showing the Zolotarev `q ≡ 3, 5 (mod 8)` condition is sharp. -/
def cert_q7_odd_period : FCSRSpec.ExactPeriodCert := ⟨7, 1, 3, [3]⟩

theorem cert_q7_odd_period_valid : cert_q7_odd_period.check = true := by decide

-- ----------------------------------------------------------------------------
-- Kernel-Checked Non-Vacuity Witnesses (Inhabiting All Engine Hypotheses)
-- ----------------------------------------------------------------------------

/-- Non-vacuity witness for `dSection_cyclotomic_engine` at `d = 3, k = 2` (`q = 21`, `p = -1`). -/
theorem nonvacuity_dSection_q21 :
    ∃ (spec : FCSRSpec) (s : FCSRState spec),
      spec.q = 21 ∧ spec.InCore s ∧ spec.q ∣ FCSRSpec.repunit 3 2 ∧
      spec.IsExactPeriod s 6 ∧
      sumInt 6 (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = 2 := by
  have h := family_repunit_dSection 3 2 (by omega) (by omega)
  rcases h with ⟨hq3, hqo, hq, hmin, hsec⟩
  let spec := FCSRSpec.ofOdd (FCSRSpec.repunit 3 2) hq3 hqo
  let s := spec.encode (-1)
  have hs : spec.InCore s := by
    unfold FCSRSpec.InCore FCSRSpec.qInt; rw [spec.potential_encode, hq]; omega
  have hrep21 : FCSRSpec.repunit 3 2 = 21 := by decide
  have hsum2 : sumInt 6 (fun t => (FCSRSpec.outBit (spec.stepN t s) : Int)) = 2 := by
    have h1 := (hsec s hs).2.2.1
    have hq21 : spec.q = 21 := by rw [hq, hrep21]
    have hspec_def : spec = FCSRSpec.ofOdd 21 (by omega) (by decide) := by
      unfold spec; congr 1
    -- Direct decidable evaluation of sectionQuantum sum for q = 21, p = -1
    have hcheck : sumInt 2 (fun t => spec.sectionQuantum s 3 2 t) = 2 := by
      have hspec_r : spec.qInt = 21 := by unfold FCSRSpec.qInt; rw [hq21]; rfl
      have hpt : ∀ n, spec.potential (spec.stepN n s) = FCSRSpec.divStepN 21 n (-1) := by
        intro n
        rw [spec.potential_stepN_eq_divStepN, spec.potential_encode, hq21]
      unfold FCSRSpec.sectionQuantum FCSRSpec.sectionSum
      simp only [sumInt, hpt, hspec_r]
      decide
    rw [h1, hcheck]
  refine ⟨spec, s, by rw [hq, hrep21], hs, by rw [hq]; exact Nat.dvd_refl _, hmin, hsum2⟩

/-- Non-vacuity witness for `step_bijection_on_core` + `carry_bounds_on_core` + `halfPeriod_certificate` at `q = 17 = 2^4 + 1`. -/
theorem nonvacuity_core_and_halfPeriod_q17 :
    ∃ (spec : FCSRSpec) (s : FCSRState spec),
      spec.q = 17 ∧ spec.InCore s ∧
      spec.invStep (spec.step s) = s ∧
      spec.stepN 4 s = spec.complement s ∧
      spec.IsExactPeriod s 8 := by
  have h := family_pow2_add_1 4 (by omega)
  rcases h with ⟨hq3, hqo, hq, hhalf, hmin⟩
  let spec := FCSRSpec.ofOdd (2 ^ 4 + 1) hq3 hqo
  let s := spec.encode (-1)
  have hs : spec.InCore s := by
    unfold FCSRSpec.InCore FCSRSpec.qInt; rw [spec.potential_encode, hq]; omega
  exact ⟨spec, s, by rw [hq], hs, (spec.step_bijection_on_core hs).1, (hhalf s hs).1, hmin⟩


-- ============================================================================
-- Axiom Audit (`#print axioms` on EVERY main engine & family theorem)
-- ============================================================================

end Families

end SiliconFCSR
