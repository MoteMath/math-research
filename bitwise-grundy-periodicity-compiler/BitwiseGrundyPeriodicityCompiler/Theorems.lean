/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitwiseGrundyPeriodicityCompiler.Defs

namespace BitwiseGrundyCompiler

/-! ## Section 1: Pure-Silicon Bitwise & Carry/Borrow Primitives -/


theorem allLt_iff {p : Nat → Bool} {n : Nat} :
    allLt p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [allLt]
  | succ k ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hik : i < k
      · exact h1 i hik
      · have : i = k := by omega
        subst this; exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

/-! ### Fuel-independence and recurrence laws for `popcount`, `bitLen`, `ctz` -/

theorem popcountAux_eq (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    popcountAux f1 n = popcountAux f2 n := by
  induction f1 generalizing f2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases f2 <;> simp [popcountAux]
  | succ f1 ih =>
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [popcountAux]
    | succ f2 =>
      simp only [popcountAux]
      by_cases hn : n = 0
      · subst hn; simp
      · have hbeq : (n == 0) = false := beq_false_of_ne hn
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [ih f2 (n / 2) (by omega) (by omega)]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_eq_mod_add_div (n : Nat) :
    popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => rfl
  | succ m =>
    unfold popcount
    simp only [popcountAux]
    have hbeq : (m + 1 == 0) = false := beq_false_of_ne (by omega)
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [popcountAux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) (by omega)]

theorem bitLenAux_eq (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    bitLenAux f1 n = bitLenAux f2 n := by
  induction f1 generalizing f2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases f2 <;> simp [bitLenAux]
  | succ f1 ih =>
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [bitLenAux]
    | succ f2 =>
      simp only [bitLenAux]
      by_cases hn : n = 0
      · subst hn; simp
      · have hbeq : (n == 0) = false := beq_false_of_ne hn
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [ih f2 (n / 2) (by omega) (by omega)]

theorem bitLen_zero : bitLen 0 = 0 := rfl

theorem bitLen_succ_eq (n : Nat) (hn : n ≠ 0) :
    bitLen n = 1 + bitLen (n / 2) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m =>
    unfold bitLen
    simp only [bitLenAux]
    have hbeq : (m + 1 == 0) = false := beq_false_of_ne (by omega)
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [bitLenAux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) (by omega)]

theorem ctzAux_eq (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    ctzAux f1 n = ctzAux f2 n := by
  induction f1 generalizing f2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases f2 <;> simp [ctzAux]
  | succ f1 ih =>
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [ctzAux]
    | succ f2 =>
      simp only [ctzAux]
      by_cases hn : n = 0
      · subst hn; simp
      · have hbeq : (n == 0) = false := beq_false_of_ne hn
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        by_cases hodd : n % 2 = 1
        · have h1 : (n % 2 == 1) = true := beq_iff_eq.mpr hodd
          simp [h1]
        · have h1 : (n % 2 == 1) = false := beq_false_of_ne hodd
          simp only [h1, Bool.false_eq_true, ↓reduceIte]
          rw [ih f2 (n / 2) (by omega) (by omega)]

theorem ctz_zero : ctz 0 = 0 := rfl

theorem ctz_odd {n : Nat} (h : n % 2 = 1) : ctz n = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    unfold ctz
    simp only [ctzAux]
    have hbeq : (m + 1 == 0) = false := beq_false_of_ne (by omega)
    have h1 : ((m + 1) % 2 == 1) = true := beq_iff_eq.mpr h
    simp [hbeq, h1]

theorem ctz_even {n : Nat} (hne : n ≠ 0) (he : n % 2 = 0) :
    ctz n = 1 + ctz (n / 2) := by
  cases n with
  | zero => exact absurd rfl hne
  | succ m =>
    unfold ctz
    simp only [ctzAux]
    have hbeq : (m + 1 == 0) = false := beq_false_of_ne (by omega)
    have h1 : ((m + 1) % 2 == 1) = false := beq_false_of_ne (by omega)
    simp only [hbeq, h1, Bool.false_eq_true, ↓reduceIte]
    rw [ctzAux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) (by omega)]

/-! ### Bitwise & 2-adic structural lemmas -/

theorem popcount_mul2_add (q r : Nat) (hr : r < 2) :
    popcount (2 * q + r) = r + popcount q := by
  rw [popcount_eq_mod_add_div]
  have h1 : (2 * q + r) % 2 = r := by omega
  have h2 : (2 * q + r) / 2 = q := by omega
  rw [h1, h2]

theorem popcount_shift_add (a b k : Nat) (hb : b < 2 ^ k) :
    popcount (a * 2 ^ k + b) = popcount a + popcount b := by
  induction k generalizing a b with
  | zero =>
    have hb0 : b = 0 := by simp at hb; omega
    subst hb0; simp [popcount_zero]
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have hdiv : b / 2 < 2 ^ k := by rw [hpow] at hb; omega
    have hmul : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ k) 2]
    have hsplit : a * 2 ^ (k + 1) + b = 2 * (a * 2 ^ k + b / 2) + b % 2 := by
      rw [hmul]; omega
    rw [hsplit, popcount_mul2_add _ _ (by omega), ih a (b / 2) hdiv]
    have hpb : popcount b = b % 2 + popcount (b / 2) := popcount_eq_mod_add_div b
    omega

theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · subst h; simp [bitLen_zero]
    · rw [bitLen_succ_eq n h, Nat.pow_add, Nat.pow_one]
      have hlt := ih (n / 2) (by omega)
      omega

theorem ctz_mul_two_pow (q k : Nat) (hq : q > 0) :
    ctz (q * 2 ^ k) = k + ctz q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have hpos : q * 2 ^ (k + 1) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (by have := Nat.two_pow_pos (k + 1); omega)
    have heven : (q * 2 ^ (k + 1)) % 2 = 0 := by
      rw [hpow, ← Nat.mul_assoc]; omega
    have hdiv : (q * 2 ^ (k + 1)) / 2 = q * 2 ^ k := by
      rw [hpow, ← Nat.mul_assoc]; omega
    rw [ctz_even hpos heven, hdiv, ih]
    omega

theorem ctz_two_pow (k : Nat) : ctz (2 ^ k) = k := by
  have h := ctz_mul_two_pow 1 k (by omega)
  simp only [Nat.one_mul] at h
  have h1 : ctz 1 = 0 := ctz_odd (by omega)
  omega

theorem ctz_le_iff_mod_ne_zero (q t : Nat) (hq : q > 0) :
    ctz q ≤ t ↔ q % 2 ^ (t + 1) ≠ 0 := by
  induction t generalizing q with
  | zero =>
    simp only [Nat.zero_add, Nat.pow_one]
    by_cases hodd : q % 2 = 1
    · rw [ctz_odd hodd]; omega
    · have hev : q % 2 = 0 := by omega
      rw [ctz_even (by omega) hev]; omega
  | succ t ih =>
    by_cases hodd : q % 2 = 1
    · rw [ctz_odd hodd]
      constructor
      · intro _ hdiv
        have h2 : 2 ∣ 2 ^ (t + 2) := by
          rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
        have hq2 : 2 ∣ q := Nat.dvd_trans h2 (Nat.dvd_of_mod_eq_zero hdiv)
        omega
      · intro _; omega
    · have hev : q % 2 = 0 := by omega
      have hq2 : q / 2 > 0 := by omega
      rw [ctz_even (by omega) hev]
      have hpow : 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hqeq : q = 2 * (q / 2) := by omega
      have hmod_eq : q % (2 * 2 ^ (t + 1)) = 2 * ((q / 2) % 2 ^ (t + 1)) := by
        have h := Nat.mul_mod_mul_left 2 (q / 2) (2 ^ (t + 1))
        rw [← hqeq] at h
        exact h
      rw [hpow, hmod_eq]
      have ih' := ih (q / 2) hq2
      omega

theorem ctz_eq_iff_mod (q t : Nat) (hq : q > 0) :
    ctz q = t ↔ q % 2 ^ (t + 1) = 2 ^ t := by
  induction t generalizing q with
  | zero =>
    simp only [Nat.zero_add, Nat.pow_one, Nat.pow_zero]
    by_cases hodd : q % 2 = 1
    · rw [ctz_odd hodd]; omega
    · have hev : q % 2 = 0 := by omega
      rw [ctz_even (by omega) hev]; omega
  | succ t ih =>
    by_cases hodd : q % 2 = 1
    · rw [ctz_odd hodd]
      constructor
      · intro h; omega
      · intro h
        have hpow : 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        have hpow2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
        have hmod2 : (q % 2 ^ (t + 2)) % 2 = q % 2 := by
          rw [hpow, Nat.mod_mul_right_mod]
        rw [h, hpow2] at hmod2
        omega
    · have hev : q % 2 = 0 := by omega
      have hq2 : q / 2 > 0 := by omega
      rw [ctz_even (by omega) hev]
      have hpow : 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpow2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
      have hqeq : q = 2 * (q / 2) := by omega
      have hmod_eq : q % (2 * 2 ^ (t + 1)) = 2 * ((q / 2) % 2 ^ (t + 1)) := by
        have h := Nat.mul_mod_mul_left 2 (q / 2) (2 ^ (t + 1))
        rw [← hqeq] at h
        exact h
      rw [hpow, hmod_eq]
      have ih' := ih (q / 2) hq2
      rw [hpow2]
      have hiff : 2 * (q / 2 % (2 * 2 ^ t)) = 2 * 2 ^ t ↔ q / 2 % 2 ^ (t + 1) = 2 ^ t := by
        rw [← hpow2]; omega
      omega

theorem testBit_add_mul_two_pow_lt (n m k i : Nat) (hi : i < k) :
    (n + m * 2 ^ k).testBit i = n.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
    rw [← Nat.pow_add]; congr 1; omega
  have hdiv : (n + m * 2 ^ k) / 2 ^ i = n / 2 ^ i + m * 2 ^ (k - i) := by
    rw [hpow, ← Nat.mul_assoc]
    exact Nat.add_mul_div_right n (m * 2 ^ (k - i)) (Nat.two_pow_pos i)
  rw [hdiv]
  have hev : (m * 2 ^ (k - i)) % 2 = 0 := by
    obtain ⟨d, hd⟩ : ∃ d, k - i = d + 1 := ⟨k - i - 1, by omega⟩
    rw [hd, Nat.pow_succ, ← Nat.mul_assoc]
    omega
  have : (n / 2 ^ i + m * 2 ^ (k - i)) % 2 = (n / 2 ^ i) % 2 := by omega
  rw [this]

theorem land_add_mul_two_pow (n m mask k : Nat) (hmask : mask < 2 ^ k) :
    ((n + m * 2 ^ k) &&& mask) = (n &&& mask) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  by_cases hi : i < k
  · rw [testBit_add_mul_two_pow_lt n m k i hi]
  · have hmask0 : mask.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      have hle : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    simp [hmask0]

theorem xor_shift_add (a1 a2 b1 b2 k : Nat) (hb1 : b1 < 2 ^ k) (hb2 : b2 < 2 ^ k) :
    (a1 * 2 ^ k + b1) ^^^ (a2 * 2 ^ k + b2) = (a1 ^^^ a2) * 2 ^ k + (b1 ^^^ b2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  have hshift : ∀ a b, b < 2 ^ k →
      (a * 2 ^ k + b).testBit i = if i < k then b.testBit i else a.testBit (i - k) := by
    intro a b hb
    by_cases hi : i < k
    · simp only [hi, ↓reduceIte]
      rw [Nat.add_comm]
      exact testBit_add_mul_two_pow_lt b a k i hi
    · simp only [hi, ↓reduceIte]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hpow, ← Nat.div_div_eq_div_mul]
      have hdivk : (a * 2 ^ k + b) / 2 ^ k = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hb, Nat.zero_add]
      rw [hdivk]
  have hbx : b1 ^^^ b2 < 2 ^ k := Nat.xor_lt_two_pow hb1 hb2
  rw [hshift a1 b1 hb1, hshift a2 b2 hb2, hshift (a1 ^^^ a2) (b1 ^^^ b2) hbx]
  split <;> simp [Nat.testBit_xor]

theorem popcount_xor_pred (q : Nat) (hq : q > 0) :
    popcount (q ^^^ (q - 1)) = ctz q + 1 := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    by_cases hodd : q % 2 = 1
    · rw [ctz_odd hodd]
      have hq1 : q = (q / 2) * 2 + 1 := by omega
      have hqm1 : q - 1 = (q / 2) * 2 + 0 := by omega
      have hxor : q ^^^ (q - 1) = 1 := by
        have h := xor_shift_add (q / 2) (q / 2) 1 0 1 (by omega) (by omega)
        simp only [Nat.pow_one] at h
        rw [← hq1, ← hqm1] at h
        rw [h, Nat.xor_self]
        decide
      rw [hxor]
      decide
    · have hev : q % 2 = 0 := by omega
      have hq2 : q / 2 > 0 := by omega
      rw [ctz_even (by omega) hev]
      have hq1 : q = (q / 2) * 2 + 0 := by omega
      have hqm1 : q - 1 = (q / 2 - 1) * 2 + 1 := by omega
      have hxor : q ^^^ (q - 1) = ((q / 2) ^^^ (q / 2 - 1)) * 2 + 1 := by
        have h := xor_shift_add (q / 2) (q / 2 - 1) 0 1 1 (by omega) (by omega)
        simp only [Nat.pow_one] at h
        rw [← hq1, ← hqm1] at h
        rw [h]
        have : (0 : Nat) ^^^ 1 = 1 := by decide
        rw [this]
      rw [hxor]
      have hstep := popcount_shift_add ((q / 2) ^^^ (q / 2 - 1)) 1 1 (by omega)
      simp only [Nat.pow_one] at hstep
      rw [hstep, ih (q / 2) (by omega) hq2]
      have hp1 : popcount 1 = 1 := by decide
      omega

theorem xor_mod_two (x y : Nat) : (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
  have h := Nat.testBit_xor x y 0
  simp only [Nat.testBit_zero] at h
  by_cases hx : x % 2 = 1 <;> by_cases hy : y % 2 = 1
  · have htrue : decide ((x ^^^ y) % 2 = 1) = false := by rw [h]; simp [hx, hy]
    have : ¬((x ^^^ y) % 2 = 1) := of_decide_eq_false htrue
    omega
  · have htrue : decide ((x ^^^ y) % 2 = 1) = true := by rw [h]; simp [hx, hy]
    have : (x ^^^ y) % 2 = 1 := of_decide_eq_true htrue
    omega
  · have htrue : decide ((x ^^^ y) % 2 = 1) = true := by rw [h]; simp [hx, hy]
    have : (x ^^^ y) % 2 = 1 := of_decide_eq_true htrue
    omega
  · have htrue : decide ((x ^^^ y) % 2 = 1) = false := by rw [h]; simp [hx, hy]
    have : ¬((x ^^^ y) % 2 = 1) := of_decide_eq_false htrue
    omega

/-- Core carry-in popcount identity (proved by bit-slice induction on `a + b`). -/
theorem popcount_add_carry_aux (a b : Nat) (c : Bool) :
    popcount a + popcount b + c.toNat =
      popcount (a + b + c.toNat) + popcount (((a + b + c.toNat) ^^^ a ^^^ b) / 2) := by
  induction hsum : a + b using Nat.strongRecOn generalizing a b c with
  | ind s ih =>
    subst hsum
    by_cases h0 : a = 0 ∧ b = 0
    · rcases h0 with ⟨rfl, rfl⟩
      cases c <;> decide
    · have hlt : a / 2 + b / 2 < a + b := by omega
      let c' : Bool := decide (a % 2 + b % 2 + c.toNat ≥ 2)
      have hc' : c'.toNat = (a % 2 + b % 2 + c.toNat) / 2 := by
        cases c <;> simp only [c', Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
        · by_cases hge : a % 2 + b % 2 ≥ 2
          · rw [decide_eq_true hge]; simp; omega
          · rw [decide_eq_false hge]; simp; omega
        · by_cases hge : a % 2 + b % 2 + 1 ≥ 2
          · rw [decide_eq_true hge]; simp; omega
          · rw [decide_eq_false hge]; simp; omega
      have hsum_div : (a + b + c.toNat) / 2 = a / 2 + b / 2 + c'.toNat := by
        rw [hc']; omega
      have hxor_div : ((a + b + c.toNat) ^^^ a ^^^ b) / 2 =
          ((a / 2 + b / 2 + c'.toNat) ^^^ (a / 2) ^^^ (b / 2)) := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_div_two, Nat.testBit_xor]
        rw [← hsum_div]
        simp [Nat.testBit_div_two]
      have hpop_a : popcount a = a % 2 + popcount (a / 2) := popcount_eq_mod_add_div a
      have hpop_b : popcount b = b % 2 + popcount (b / 2) := popcount_eq_mod_add_div b
      have hpop_s : popcount (a + b + c.toNat) =
          (a + b + c.toNat) % 2 + popcount (a / 2 + b / 2 + c'.toNat) := by
        rw [popcount_eq_mod_add_div, hsum_div]
      have hpop_x : popcount (((a + b + c.toNat) ^^^ a ^^^ b) / 2) =
          c'.toNat + popcount (((a / 2 + b / 2 + c'.toNat) ^^^ (a / 2) ^^^ (b / 2)) / 2) := by
        rw [hxor_div, popcount_eq_mod_add_div]
        have hbit0 : ((a / 2 + b / 2 + c'.toNat) ^^^ (a / 2) ^^^ (b / 2)) % 2 = c'.toNat := by
          rw [xor_mod_two, xor_mod_two]
          cases c' <;> simp <;> omega
        rw [hbit0]
      have hrec := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) c' rfl
      have hbit_arith : a % 2 + b % 2 + c.toNat = (a + b + c.toNat) % 2 + 2 * c'.toNat := by
        rw [hc']; omega
      omega

/-- **Kummer Carry-Popcount Identity**:
`popcount a + popcount b = popcount (a + b) + popcount ((a + b) ^^^ a ^^^ b)`. -/
theorem popcount_add_carry (a b : Nat) :
    popcount a + popcount b = popcount (a + b) + popcount ((a + b) ^^^ a ^^^ b) := by
  have h := popcount_add_carry_aux a b false
  simp only [Bool.toNat_false, Nat.add_zero] at h
  have hmod0 : ((a + b) ^^^ a ^^^ b) % 2 = 0 := by
    rw [xor_mod_two, xor_mod_two]; omega
  have hpx := popcount_eq_mod_add_div ((a + b) ^^^ a ^^^ b)
  omega

/-- **Kummer Borrow-Popcount Identity**:
For all `s ≤ n`, `popcount (n - s) + popcount s = popcount n + borrowCount n s`. -/
theorem kummer_borrow_popcount (n s : Nat) (hsn : s ≤ n) :
    popcount (n - s) + popcount s = popcount n + borrowCount n s := by
  have h := popcount_add_carry (n - s) s
  have hns : n - s + s = n := Nat.sub_add_cancel hsn
  rw [hns] at h
  exact h

/-- Decomposition of `borrowCount (q * 2^k + r) s` when `s ≤ r < 2^k` (no borrow out of bit `k-1`). -/
theorem borrowCount_decomp_ge (q r s k : Nat) (hrk : r < 2 ^ k) (hsr : s ≤ r) :
    borrowCount (q * 2 ^ k + r) s = borrowCount r s := by
  unfold borrowCount borrowMask
  have hsub : q * 2 ^ k + r - s = q * 2 ^ k + (r - s) := by omega
  rw [hsub]
  have hrs : r - s < 2 ^ k := by omega
  have h1 := xor_shift_add q q r (r - s) k hrk hrs
  rw [h1, Nat.xor_self, Nat.zero_mul, Nat.zero_add]

/-- Decomposition of `borrowCount (q * 2^k + r) s` when `r < s < 2^k` and `q > 0`
(exact ripple-borrow split: `(ctz q + 1) + low_borrows`). -/
theorem borrowCount_decomp_lt (q r s k : Nat) (hrk : r < 2 ^ k) (hsk : s < 2 ^ k)
    (hrs : r < s) (hq : q > 0) :
    borrowCount (q * 2 ^ k + r) s =
      (ctz q + 1) + popcount (r ^^^ (2 ^ k + r - s) ^^^ s) := by
  unfold borrowCount borrowMask
  have hqsplit : q * 2 ^ k = (q - 1) * 2 ^ k + 2 ^ k := by
    have h1 : q = (q - 1) + 1 := by omega
    calc q * 2 ^ k = ((q - 1) + 1) * 2 ^ k := by rw [← h1]
      _ = (q - 1) * 2 ^ k + 1 * 2 ^ k := Nat.add_mul (q - 1) 1 (2 ^ k)
      _ = (q - 1) * 2 ^ k + 2 ^ k := by rw [Nat.one_mul]
  have hsub : q * 2 ^ k + r - s = (q - 1) * 2 ^ k + (2 ^ k + r - s) := by omega
  rw [hsub]
  have hlow : 2 ^ k + r - s < 2 ^ k := by omega
  have h1 := xor_shift_add q (q - 1) r (2 ^ k + r - s) k hrk hlow
  rw [h1]
  have hrx : r ^^^ (2 ^ k + r - s) < 2 ^ k := Nat.xor_lt_two_pow hrk hlow
  have h2 := xor_shift_add (q ^^^ (q - 1)) 0 (r ^^^ (2 ^ k + r - s)) s k hrx hsk
  simp only [Nat.zero_mul, Nat.zero_add, Nat.xor_zero] at h2
  rw [h2, popcount_shift_add _ _ k (Nat.xor_lt_two_pow hrx hsk), popcount_xor_pred q hq]

/-- Helper splitting `n` and `n + m * 2^(k + B)` at bit boundary `k`. -/
private theorem split_shift_eq (n m k B : Nat) :
    n = (n / 2 ^ k) * 2 ^ k + n % 2 ^ k ∧
    n + m * 2 ^ (k + B) = (n / 2 ^ k + m * 2 ^ B) * 2 ^ k + n % 2 ^ k := by
  have h1 : n = (n / 2 ^ k) * 2 ^ k + n % 2 ^ k := by
    have h := Nat.div_add_mod n (2 ^ k)
    rw [Nat.mul_comm] at h; omega
  have hmul : m * 2 ^ (k + B) = (m * 2 ^ B) * 2 ^ k := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ k) (2 ^ B), ← Nat.mul_assoc]
  have h2 : n + m * 2 ^ (k + B) = (n / 2 ^ k + m * 2 ^ B) * 2 ^ k + n % 2 ^ k := by
    rw [Nat.add_mul, ← hmul]
    omega
  exact ⟨h1, h2⟩

/-- **Borrow-Count Dyadic Localization Theorem (`≤ B`)**:
For all `s < 2^k` and `s ≤ n`, adding any multiple of `2^(k + B)` preserves `borrowCount n s ≤ B`. -/
theorem borrowCount_le_shift_inv (s k B n m : Nat) (hsk : s < 2 ^ k) (hsn : s ≤ n) :
    borrowCount (n + m * 2 ^ (k + B)) s ≤ B ↔ borrowCount n s ≤ B := by
  obtain ⟨hneq, hnpeq⟩ := split_shift_eq n m k B
  let q := n / 2 ^ k
  let r := n % 2 ^ k
  have hrk : r < 2 ^ k := Nat.mod_lt n (Nat.two_pow_pos k)
  rw [hnpeq]
  by_cases hsr : s ≤ r
  · rw [borrowCount_decomp_ge (q + m * 2 ^ B) r s k hrk hsr]
    have hrhs : borrowCount n s = borrowCount r s := by
      calc borrowCount n s = borrowCount (q * 2 ^ k + r) s := by rw [← hneq]
        _ = borrowCount r s := borrowCount_decomp_ge q r s k hrk hsr
    rw [hrhs]
  · have hrs : r < s := by omega
    have hq : q > 0 := Nat.pos_of_ne_zero fun h0 => by
      have h0' : n / 2 ^ k = 0 := h0
      rw [h0', Nat.zero_mul, Nat.zero_add] at hneq
      omega
    have hqp : q + m * 2 ^ B > 0 := by omega
    rw [borrowCount_decomp_lt (q + m * 2 ^ B) r s k hrk hsk hrs hqp]
    have hrhs : borrowCount n s = (ctz q + 1) + popcount (r ^^^ (2 ^ k + r - s) ^^^ s) := by
      calc borrowCount n s = borrowCount (q * 2 ^ k + r) s := by rw [← hneq]
        _ = (ctz q + 1) + popcount (r ^^^ (2 ^ k + r - s) ^^^ s) :=
            borrowCount_decomp_lt q r s k hrk hsk hrs hq
    rw [hrhs]
    let Llow := popcount (r ^^^ (2 ^ k + r - s) ^^^ s)
    by_cases hB : B < 1 + Llow
    · constructor <;> intro h <;> omega
    · let t := B - 1 - Llow
      have hle_iff : ∀ x, x + 1 + Llow ≤ B ↔ x ≤ t := by intro x; omega
      rw [hle_iff, hle_iff, ctz_le_iff_mod_ne_zero _ t hqp, ctz_le_iff_mod_ne_zero _ t hq]
      have hdvd : 2 ^ (t + 1) ∣ m * 2 ^ B := by
        have hpow : 2 ^ B = 2 ^ (t + 1) * 2 ^ (B - (t + 1)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hpow]
        exact ⟨m * 2 ^ (B - (t + 1)), by rw [Nat.mul_comm (2 ^ (t + 1)), ← Nat.mul_assoc, Nat.mul_comm m, Nat.mul_comm _ (2 ^ (t + 1))]⟩
      obtain ⟨u, hu⟩ := hdvd
      rw [hu, Nat.add_mul_mod_self_left]

/-- **Borrow-Count Dyadic Localization Theorem (`= B`)**:
For all `s < 2^k` and `s ≤ n`, adding any multiple of `2^(k + B)` preserves `borrowCount n s = B`. -/
theorem borrowCount_eq_shift_inv (s k B n m : Nat) (hsk : s < 2 ^ k) (hsn : s ≤ n) :
    borrowCount (n + m * 2 ^ (k + B)) s = B ↔ borrowCount n s = B := by
  obtain ⟨hneq, hnpeq⟩ := split_shift_eq n m k B
  let q := n / 2 ^ k
  let r := n % 2 ^ k
  have hrk : r < 2 ^ k := Nat.mod_lt n (Nat.two_pow_pos k)
  rw [hnpeq]
  by_cases hsr : s ≤ r
  · rw [borrowCount_decomp_ge (q + m * 2 ^ B) r s k hrk hsr]
    have hrhs : borrowCount n s = borrowCount r s := by
      calc borrowCount n s = borrowCount (q * 2 ^ k + r) s := by rw [← hneq]
        _ = borrowCount r s := borrowCount_decomp_ge q r s k hrk hsr
    rw [hrhs]
  · have hrs : r < s := by omega
    have hq : q > 0 := Nat.pos_of_ne_zero fun h0 => by
      have h0' : n / 2 ^ k = 0 := h0
      rw [h0', Nat.zero_mul, Nat.zero_add] at hneq
      omega
    have hqp : q + m * 2 ^ B > 0 := by omega
    rw [borrowCount_decomp_lt (q + m * 2 ^ B) r s k hrk hsk hrs hqp]
    have hrhs : borrowCount n s = (ctz q + 1) + popcount (r ^^^ (2 ^ k + r - s) ^^^ s) := by
      calc borrowCount n s = borrowCount (q * 2 ^ k + r) s := by rw [← hneq]
        _ = (ctz q + 1) + popcount (r ^^^ (2 ^ k + r - s) ^^^ s) :=
            borrowCount_decomp_lt q r s k hrk hsk hrs hq
    rw [hrhs]
    let Llow := popcount (r ^^^ (2 ^ k + r - s) ^^^ s)
    by_cases hB : B < 1 + Llow
    · constructor <;> intro h <;> omega
    · let t := B - 1 - Llow
      have heq_iff : ∀ x, x + 1 + Llow = B ↔ x = t := by intro x; omega
      rw [heq_iff, heq_iff, ctz_eq_iff_mod _ t hqp, ctz_eq_iff_mod _ t hq]
      have hdvd : 2 ^ (t + 1) ∣ m * 2 ^ B := by
        have hpow : 2 ^ B = 2 ^ (t + 1) * 2 ^ (B - (t + 1)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hpow]
        exact ⟨m * 2 ^ (B - (t + 1)), by rw [Nat.mul_comm (2 ^ (t + 1)), ← Nat.mul_assoc, Nat.mul_comm m, Nat.mul_comm _ (2 ^ (t + 1))]⟩
      obtain ⟨u, hu⟩ := hdvd
      rw [hu, Nat.add_mul_mod_self_left]

/-- **Dyadic Borrow-Wall Crossing Impossibility Lemma**:
Any move `s < 2^k` crossing a `2^L`-boundary (with `k + B ≤ L`) forces strictly more than `B` borrows. -/
theorem borrowCount_cross_wall_gt (s k B L q r : Nat)
    (hsk : s < 2 ^ k) (hL : k + B ≤ L) (hq : q > 0) (hrs : r < s) :
    borrowCount (q * 2 ^ L + r) s > B := by
  have hrk : r < 2 ^ k := by omega
  have hpow : 2 ^ L = 2 ^ (L - k) * 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  have hrew : q * 2 ^ L + r = (q * 2 ^ (L - k)) * 2 ^ k + r := by
    rw [hpow, Nat.mul_assoc]
  rw [hrew]
  have hq' : q * 2 ^ (L - k) > 0 := Nat.mul_pos hq (Nat.two_pow_pos _)
  rw [borrowCount_decomp_lt (q * 2 ^ (L - k)) r s k hrk hsk hrs hq',
      ctz_mul_two_pow q (L - k) hq]
  omega

/-! ## Section 2: Bitwise/Carry Subtraction Game DSL & True Sprague-Grundy Semantics -/


theorem mem_legalMoves_iff (G : BitGame) (n s : Nat) :
    s ∈ legalMoves G n ↔ legalMove G n s = true := by
  induction G with
  | nil => simp [legalMoves, legalMove]
  | cons r rs ih =>
    simp only [legalMoves, legalMove, List.filterMap_cons, List.any_cons, Bool.or_eq_true]
    by_cases h : (0 < r.step && r.step ≤ n && evalGuard r.step r.guard n) = true
    · simp only [h, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (rfl | hmem)
        · left
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
          exact ⟨⟨⟨trivial, h.1.1⟩, h.1.2⟩, h.2⟩
        · exact Or.inr (ih.mp hmem)
      · rintro (hr | hmem)
        · left
          simp only [Bool.and_eq_true, beq_iff_eq] at hr
          exact hr.1.1.1.symm
        · exact Or.inr (ih.mpr hmem)
    · have hf : (0 < r.step && r.step ≤ n && evalGuard r.step r.guard n) = false := by
        cases hc : (0 < r.step && r.step ≤ n && evalGuard r.step r.guard n)
        · rfl
        · exact absurd hc h
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hmem; exact Or.inr (ih.mp hmem)
      · rintro (hr | hmem)
        · exfalso
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
          have : (0 < r.step && r.step ≤ n && evalGuard r.step r.guard n) = true := by
            simp [hr.1.1.2, hr.1.2, hr.2]
          exact h this
        · exact ih.mpr hmem


/-! ### Computable `mex` with completeness & exclusion proofs -/


private def countGe (xs : List Nat) (k : Nat) : Nat :=
  (xs.filter (fun x => decide (k ≤ x))).length

private theorem countGe_le_pred (l : List Nat) (k : Nat) :
    (l.filter (fun y => decide (k + 1 ≤ y))).length ≤
    (l.filter (fun y => decide (k ≤ y))).length := by
  induction l with
  | nil => simp
  | cons a al ih =>
    simp only [List.filter_cons]
    by_cases ha1 : k + 1 ≤ a
    · have ha2 : k ≤ a := by omega
      simp [ha1, ha2]; omega
    · by_cases ha2 : k ≤ a
      · simp [ha1, ha2]; omega
      · simp [ha1, ha2]; omega

private theorem countGe_succ_lt (xs : List Nat) (k : Nat) (hk : k ∈ xs) :
    countGe xs (k + 1) < countGe xs k := by
  induction xs with
  | nil => cases hk
  | cons a tl ih =>
    simp only [countGe, List.filter_cons]
    cases hk with
    | head =>
      have h1 : decide (k + 1 ≤ k) = false := decide_eq_false (by omega)
      simp [h1]
      have := countGe_le_pred tl k
      omega
    | tail _ hmem =>
      have hlt := ih hmem
      simp only [countGe] at hlt
      by_cases ha1 : k + 1 ≤ a
      · have ha2 : k ≤ a := by omega
        simp [ha1, ha2]; omega
      · by_cases ha2 : k ≤ a
        · simp [ha1, ha2]; omega
        · simp [ha1, ha2]; omega

private theorem mexAux_not_mem (xs : List Nat) (fuel k : Nat)
    (hf : countGe xs k < fuel) : mexAux xs fuel k ∉ xs := by
  induction fuel generalizing k with
  | zero => omega
  | succ f ih =>
    simp only [mexAux]
    by_cases hc : xs.contains k = true
    · simp only [hc, ↓reduceIte]
      have hmem : k ∈ xs := List.elem_iff.mp hc
      have hlt : countGe xs (k + 1) < countGe xs k := countGe_succ_lt xs k hmem
      exact ih (k + 1) (by omega)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      intro hmem
      exact hc (List.elem_iff.mpr hmem)

private theorem lt_mexAux_mem (xs : List Nat) (fuel k v : Nat)
    (hkv : k ≤ v) (hv : v < mexAux xs fuel k) : v ∈ xs := by
  induction fuel generalizing k with
  | zero => simp [mexAux] at hv; omega
  | succ f ih =>
    simp only [mexAux] at hv
    by_cases hc : xs.contains k = true
    · simp only [hc, ↓reduceIte] at hv
      by_cases hvk : v = k
      · subst hvk; exact List.elem_iff.mp hc
      · exact ih (k + 1) (by omega) hv
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hv
      omega

theorem mex_not_mem (xs : List Nat) : mex xs ∉ xs := by
  unfold mex
  apply mexAux_not_mem
  have hle : countGe xs 0 ≤ xs.length := List.length_filter_le _ _
  omega

theorem lt_mex_mem {xs : List Nat} {v : Nat} (hv : v < mex xs) : v ∈ xs :=
  lt_mexAux_mem xs (xs.length + 1) 0 v (Nat.zero_le v) hv

/-! ### Direct recursive Sprague-Grundy function & Impartial-Game Winning Predicates -/


theorem mapMoves_eq_map_legalMoves (G : BitGame) (n : Nat) (f : Nat → Nat) :
    mapMoves G n (fun m _ => f m) = (legalMoves G n).map (fun s => f (n - s)) := by
  induction G with
  | nil => rfl
  | cons r rs ih =>
    unfold mapMoves legalMoves at ih ⊢
    simp only [List.filterMap_cons]
    by_cases h : 0 < r.step ∧ r.step ≤ n ∧ evalGuard r.step r.guard n = true
    · have hb : (decide (0 < r.step) && decide (r.step ≤ n) && evalGuard r.step r.guard n) = true := by
        simp [h.1, h.2.1, h.2.2]
      have hd : (if h' : 0 < r.step ∧ r.step ≤ n ∧ evalGuard r.step r.guard n = true then
          some (f (n - r.step)) else none) = some (f (n - r.step)) := by simp [h]
      have hi : (if (decide (0 < r.step) && decide (r.step ≤ n) && evalGuard r.step r.guard n) = true then
          some r.step else none) = some r.step := by simp [hb]
      rw [hd, hi]
      simp only [List.map_cons, ih]
    · have hb : (decide (0 < r.step) && decide (r.step ≤ n) && evalGuard r.step r.guard n) = false := by
        cases hc : (decide (0 < r.step) && decide (r.step ≤ n) && evalGuard r.step r.guard n)
        · rfl
        · exfalso
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          exact h ⟨hc.1.1, hc.1.2, hc.2⟩
      have hd : (if h' : 0 < r.step ∧ r.step ≤ n ∧ evalGuard r.step r.guard n = true then
          some (f (n - r.step)) else none) = none := by simp [h]
      have hi : (if (decide (0 < r.step) && decide (r.step ≤ n) && evalGuard r.step r.guard n) = true then
          some r.step else none) = none := by simp [hb]
      rw [hd, hi]
      exact ih

theorem grundy_eq (G : BitGame) (n : Nat) :
    grundy G n = mex ((legalMoves G n).map (fun s => grundy G (n - s))) := by
  rw [grundy, mapMoves_eq_map_legalMoves]


theorem isWinning_iff (G : BitGame) (n : Nat) :
    IsWinning G n ↔ ∃ s, legalMove G n s = true ∧ ¬ IsWinning G (n - s) := by
  rw [IsWinning]
  constructor
  · rintro ⟨s, hleg, hnext⟩; exact ⟨s, hleg, hnext⟩
  · rintro ⟨s, hleg, hnext⟩; exact ⟨s, hleg, hnext⟩

/-- **Fundamental Sprague-Grundy 1-Heap Bridge**: `IsWinning G n ↔ grundy G n ≠ 0`. -/
theorem isWinning_iff_grundy_ne_zero (G : BitGame) (n : Nat) :
    IsWinning G n ↔ grundy G n ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [isWinning_iff]
    constructor
    · rintro ⟨s, hleg, hnext⟩ h0
      have hlt : n - s < n := by have hb := legalMove_bounds hleg; omega
      have hmem : grundy G (n - s) ∈ (legalMoves G n).map (fun t => grundy G (n - t)) :=
        List.mem_map.mpr ⟨s, (mem_legalMoves_iff G n s).mpr hleg, rfl⟩
      have hneq0 : grundy G (n - s) = 0 := by
        by_cases hz : grundy G (n - s) = 0
        · exact hz
        · exact absurd ((ih (n - s) hlt).mpr hz) hnext
      rw [hneq0] at hmem
      have hnot := mex_not_mem ((legalMoves G n).map (fun t => grundy G (n - t)))
      rw [← grundy_eq G n, h0] at hnot
      exact hnot hmem
    · intro hne
      have hpos : 0 < mex ((legalMoves G n).map (fun t => grundy G (n - t))) := by
        rw [← grundy_eq G n]; omega
      obtain ⟨s, hs_mem, hs_zero⟩ := List.mem_map.mp (lt_mex_mem hpos)
      have hleg : legalMove G n s = true := (mem_legalMoves_iff G n s).mp hs_mem
      have hlt : n - s < n := by have hb := legalMove_bounds hleg; omega
      have hnext : ¬ IsWinning G (n - s) := fun hw => (ih (n - s) hlt).mp hw hs_zero
      exact ⟨s, hleg, hnext⟩

/-! ### Full Multi-Heap Disjunctive-Sum Sprague-Grundy XOR Theorem -/


theorem isWinningMulti_iff (G : BitGame) (hs : List Nat) :
    IsWinningMulti G hs ↔ ∃ hs', MultiMove G hs hs' ∧ ¬ IsWinningMulti G hs' := by
  rw [IsWinningMulti]
  constructor
  · rintro ⟨hs', hm, hn⟩; exact ⟨hs', hm, hn⟩
  · rintro ⟨hs', hm, hn⟩; exact ⟨hs', hm, hn⟩

private theorem xor_lt_of_msb (x d k : Nat) (hdk : d < 2 ^ (k + 1))
    (hdk_bit : d.testBit k = true) (hxk : x.testBit k = true) :
    (x ^^^ d) < x := by
  have hx_split : x = (x / 2 ^ (k + 1)) * 2 ^ (k + 1) + x % 2 ^ (k + 1) := by
    have := Nat.div_add_mod x (2 ^ (k + 1)); rw [Nat.mul_comm] at this; omega
  have hxd_split : x ^^^ d = (x / 2 ^ (k + 1)) * 2 ^ (k + 1) + ((x % 2 ^ (k + 1)) ^^^ d) := by
    have h1 := xor_shift_add (x / 2 ^ (k + 1)) 0 (x % 2 ^ (k + 1)) d (k + 1)
      (Nat.mod_lt _ (Nat.two_pow_pos _)) hdk
    simp only [Nat.zero_mul, Nat.zero_add, Nat.xor_zero] at h1
    rw [← hx_split] at h1
    exact h1
  have hxk_mod : (x % 2 ^ (k + 1)).testBit k = true := by
    rw [Nat.testBit_mod_two_pow]; simp [hxk]
  have hx_low_ge : 2 ^ k ≤ x % 2 ^ (k + 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hxk_mod
    have hmod1 : (x % 2 ^ (k + 1)) / 2 ^ k % 2 = 1 := of_decide_eq_true hxk_mod
    have hdiv_ge : 1 ≤ (x % 2 ^ (k + 1)) / 2 ^ k :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at hmod1; omega
    have hda := Nat.div_add_mod (x % 2 ^ (k + 1)) (2 ^ k)
    have hmul : 2 ^ k * 1 ≤ 2 ^ k * ((x % 2 ^ (k + 1)) / 2 ^ k) :=
      Nat.mul_le_mul_left (2 ^ k) hdiv_ge
    rw [Nat.mul_one] at hmul
    omega
  have hxd_low_lt : (x % 2 ^ (k + 1)) ^^^ d < 2 ^ k := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Nat.testBit_xor]
    by_cases hik : i = k
    · subst hik; simp [hxk_mod, hdk_bit]
    · have hgt : k + 1 ≤ i := by omega
      have h1 : (x % 2 ^ (k + 1)).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
        have := Nat.mod_lt x (Nat.two_pow_pos (k + 1))
        omega
      have h2 : d.testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
        omega
      simp [h1, h2]
  omega

private theorem testBit_bitLen_pred {d : Nat} (hd : d ≠ 0) :
    d.testBit (bitLen d - 1) = true := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases h1 : d = 1
    · subst h1; decide
    · have hdiv : d / 2 ≠ 0 := by omega
      have hbl : bitLen d = 1 + bitLen (d / 2) := bitLen_succ_eq d hd
      have hbl_pos : bitLen (d / 2) ≥ 1 := by
        have hlt := lt_two_pow_bitLen (d / 2)
        by_cases hz : bitLen (d / 2) = 0
        · rw [hz] at hlt; omega
        · omega
      have hsub : bitLen d - 1 = (bitLen (d / 2) - 1) + 1 := by omega
      rw [hsub, Nat.testBit_succ]
      exact ih (d / 2) (by omega) hdiv

private theorem multiMove_nimSum_ne {G : BitGame} {hs hs' : List Nat}
    (hm : MultiMove G hs hs') :
    nimSum (hs'.map (grundy G)) ≠ nimSum (hs.map (grundy G)) := by
  induction hm with
  | head hleg =>
    rename_i n s tl
    simp only [List.map_cons, nimSum]
    intro heq
    have hg : grundy G (n - s) = grundy G n := by
      have h1 : (grundy G (n - s) ^^^ nimSum (tl.map (grundy G))) ^^^ nimSum (tl.map (grundy G)) =
          (grundy G n ^^^ nimSum (tl.map (grundy G))) ^^^ nimSum (tl.map (grundy G)) :=
        congrArg (· ^^^ nimSum (tl.map (grundy G))) heq
      simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h1
      exact h1
    have hmem : grundy G n ∈ (legalMoves G n).map (fun s => grundy G (n - s)) :=
      List.mem_map.mpr ⟨s, (mem_legalMoves_iff G n s).mpr hleg, hg⟩
    have hnot := mex_not_mem ((legalMoves G n).map (fun s => grundy G (n - s)))
    rw [← grundy_eq G n] at hnot
    exact hnot hmem
  | tail hm ih =>
    rename_i n tl tl'
    simp only [List.map_cons, nimSum]
    intro heq
    apply ih
    have h1 : grundy G n ^^^ (grundy G n ^^^ nimSum (tl'.map (grundy G))) =
        grundy G n ^^^ (grundy G n ^^^ nimSum (tl.map (grundy G))) :=
      congrArg (grundy G n ^^^ ·) heq
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
    exact h1

private theorem multiMove_append_left {G : BitGame} (pre : List Nat) {a b : List Nat}
    (hm : MultiMove G a b) : MultiMove G (pre ++ a) (pre ++ b) := by
  induction pre with
  | nil => exact hm
  | cons x tl ih => exact MultiMove.tail ih

private theorem nimSum_append (a b : List Nat) :
    nimSum (a ++ b) = nimSum a ^^^ nimSum b := by
  induction a with
  | nil => simp [nimSum]
  | cons x tl ih => simp [nimSum, ih, Nat.xor_assoc]

/-- **Full Multi-Heap Disjunctive-Sum Sprague-Grundy XOR Theorem**:
For ANY bitwise/carry subtraction game `G` and ANY finite list of heaps `hs`,
`IsWinningMulti G hs ↔ nimSum (hs.map (grundy G)) ≠ 0`. -/
theorem isWinningMulti_iff_nimSum_ne_zero (G : BitGame) (hs : List Nat) :
    IsWinningMulti G hs ↔ nimSum (hs.map (grundy G)) ≠ 0 := by
  induction hsum : heapSum hs using Nat.strongRecOn generalizing hs with
  | ind s ih =>
    subst hsum
    rw [isWinningMulti_iff]
    constructor
    · rintro ⟨hs', hm, hnext⟩ h0
      have hlt := multiMove_heapSum_lt hm
      have hne : nimSum (hs'.map (grundy G)) ≠ 0 := by
        rw [← h0]; exact multiMove_nimSum_ne hm
      exact hnext ((ih _ hlt hs' rfl).mpr hne)
    · intro hne
      let d := nimSum (hs.map (grundy G))
      have hd_pos : bitLen d ≥ 1 := by
        have hlt := lt_two_pow_bitLen d
        by_cases hz : bitLen d = 0
        · rw [hz] at hlt; omega
        · omega
      let k := bitLen d - 1
      have hdk_lt : d < 2 ^ (k + 1) := by
        have hlt := lt_two_pow_bitLen d
        have hk1 : k + 1 = bitLen d := by omega
        rw [hk1]; exact hlt
      have hdk_bit : d.testBit k = true := testBit_bitLen_pred hne
      have hex : ∃ (pre suf : List Nat) (h : Nat),
          hs = pre ++ h :: suf ∧ (grundy G h).testBit k = true := by
        have hgen : ∀ (l : List Nat), (nimSum (l.map (grundy G))).testBit k = true →
            ∃ (pre suf : List Nat) (h : Nat), l = pre ++ h :: suf ∧ (grundy G h).testBit k = true := by
          intro l hl
          induction l with
          | nil => simp [nimSum] at hl
          | cons a tl ihl =>
            simp only [List.map_cons, nimSum, Nat.testBit_xor] at hl
            cases ha : (grundy G a).testBit k
            · rw [ha, Bool.false_xor] at hl
              obtain ⟨pre, suf, h, heq, hh⟩ := ihl hl
              exact ⟨a :: pre, suf, h, by simp [heq], hh⟩
            · exact ⟨[], tl, a, rfl, ha⟩
        exact hgen hs hdk_bit
      obtain ⟨pre, suf, h, hseq, hhk⟩ := hex
      have hlt_g : grundy G h ^^^ d < grundy G h := xor_lt_of_msb (grundy G h) d k hdk_lt hdk_bit hhk
      rw [grundy_eq G h] at hlt_g
      obtain ⟨step, hs_mem, hs_eq⟩ := List.mem_map.mp (lt_mex_mem hlt_g)
      rw [← grundy_eq G h] at hs_eq
      have hleg : legalMove G h step = true := (mem_legalMoves_iff G h step).mp hs_mem
      have hm : MultiMove G hs (pre ++ (h - step) :: suf) := by
        rw [hseq]; exact multiMove_append_left pre (MultiMove.head hleg)
      have hsum_lt := multiMove_heapSum_lt hm
      have hns_zero : nimSum ((pre ++ (h - step) :: suf).map (grundy G)) = 0 := by
        simp only [List.map_append, List.map_cons, nimSum_append, nimSum, hs_eq]
        have hd_eq : d = nimSum (pre.map (grundy G)) ^^^ (grundy G h ^^^ nimSum (suf.map (grundy G))) := by
          change nimSum (hs.map (grundy G)) = _
          rw [hseq]; simp [List.map_append, List.map_cons, nimSum_append, nimSum]
        have hcalc : nimSum (pre.map (grundy G)) ^^^ ((grundy G h ^^^ d) ^^^ nimSum (suf.map (grundy G))) =
            (nimSum (pre.map (grundy G)) ^^^ (grundy G h ^^^ nimSum (suf.map (grundy G)))) ^^^ d := by
          apply Nat.eq_of_testBit_eq
          intro i
          simp only [Nat.testBit_xor]
          cases (nimSum (pre.map (grundy G))).testBit i <;>
          cases (grundy G h).testBit i <;>
          cases d.testBit i <;>
          cases (nimSum (suf.map (grundy G))).testBit i <;> rfl
        rw [hcalc, ← hd_eq, Nat.xor_self]
      have hnext : ¬ IsWinningMulti G (pre ++ (h - step) :: suf) := fun hw =>
        (ih _ hsum_lt _ rfl).mp hw hns_zero
      exact ⟨pre ++ (h - step) :: suf, hm, hnext⟩

/-! ## Section 3: Universal Shift-Invariance Meta-Theorem & Regime I (Dyadic Borrow-Wall Theorem) -/


theorem guardShiftBits_le_gameShiftBits {G : BitGame} {r : BitRule} (hr : r ∈ G) :
    guardShiftBits r.step r.guard ≤ gameShiftBits G := by
  induction G with
  | nil => cases hr
  | cons hd tl ih =>
    simp only [gameShiftBits]
    cases hr with
    | head => exact Nat.le_max_left _ _
    | tail _ h => exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- **Universal Guard Shift-Invariance Meta-Theorem**:
For ANY `BitGuard` AST `g`, step `s`, `n ≥ s`, and any shift `p` divisible by `2^(guardShiftBits s g)`,
`evalGuard s g (n + p) = evalGuard s g n`. -/
theorem evalGuard_shift_inv (s : Nat) (g : BitGuard) (n p : Nat)
    (hsn : s ≤ n) (hdvd : 2 ^ guardShiftBits s g ∣ p) :
    evalGuard s g (n + p) = evalGuard s g n := by
  induction g with
  | always => rfl
  | maskEq mask pat =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_comm (2 ^ bitLen mask) m, land_add_mul_two_pow n m mask (bitLen mask) (lt_two_pow_bitLen mask)]
  | borrowFree =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_comm (2 ^ bitLen s) m, land_add_mul_two_pow n m s (bitLen s) (lt_two_pow_bitLen s)]
  | borrowDepthLe d =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.add_mul_mod_self_left]
  | borrowCountLe B =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_comm (2 ^ (bitLen s + B)) m]
    exact decide_eq_decide.mpr (borrowCount_le_shift_inv s (bitLen s) B n m (lt_two_pow_bitLen s) hsn)
  | borrowCountEq B =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_comm (2 ^ (bitLen s + B)) m]
    exact decide_eq_decide.mpr (borrowCount_eq_shift_inv s (bitLen s) B n m (lt_two_pow_bitLen s) hsn)
  | popcountDeltaLe delta =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    obtain ⟨m, rfl⟩ := hdvd
    have h1 : popcount (n + 2 ^ (bitLen s + popcount s + delta) * m - s) ≤
        popcount (n + 2 ^ (bitLen s + popcount s + delta) * m) + delta ↔
        borrowCount (n + 2 ^ (bitLen s + popcount s + delta) * m) s ≤ popcount s + delta := by
      have hk := kummer_borrow_popcount (n + 2 ^ (bitLen s + popcount s + delta) * m) s (by omega)
      omega
    have h2 : popcount (n - s) ≤ popcount n + delta ↔ borrowCount n s ≤ popcount s + delta := by
      have hk := kummer_borrow_popcount n s hsn
      omega
    apply decide_eq_decide.mpr
    rw [h1, h2, Nat.mul_comm (2 ^ (bitLen s + popcount s + delta)) m, Nat.add_assoc (bitLen s)]
    exact borrowCount_le_shift_inv s (bitLen s) (popcount s + delta) n m (lt_two_pow_bitLen s) hsn
  | and g1 g2 ih1 ih2 =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    have h1 : 2 ^ guardShiftBits s g1 ∣ p :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_left _ _)) hdvd
    have h2 : 2 ^ guardShiftBits s g2 ∣ p :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_right _ _)) hdvd
    rw [ih1 h1, ih2 h2]
  | or g1 g2 ih1 ih2 =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    have h1 : 2 ^ guardShiftBits s g1 ∣ p :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_left _ _)) hdvd
    have h2 : 2 ^ guardShiftBits s g2 ∣ p :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_right _ _)) hdvd
    rw [ih1 h1, ih2 h2]
  | not g ih =>
    simp only [evalGuard, guardShiftBits] at hdvd ⊢
    rw [ih hdvd]

/-- **Universal Game Move-Set Shift-Invariance**:
For any `n ≥ maxStep G` and any `p` divisible by `2 ^ gameShiftBits G`,
`legalMoves G (n + p) = legalMoves G n`. -/
theorem legalMoves_shift_inv (G : BitGame) (n p : Nat)
    (hn : maxStep G ≤ n) (hdvd : 2 ^ gameShiftBits G ∣ p) :
    legalMoves G (n + p) = legalMoves G n := by
  induction G with
  | nil => rfl
  | cons r rs ih =>
    simp only [maxStep, gameShiftBits] at hn hdvd
    have hr_le : r.step ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hrs_le : maxStep rs ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hr_dvd : 2 ^ guardShiftBits r.step r.guard ∣ p :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_left _ _)) hdvd
    have hrs_dvd : 2 ^ gameShiftBits rs ∣ p :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_right _ _)) hdvd
    have hge : evalGuard r.step r.guard (n + p) = evalGuard r.step r.guard n :=
      evalGuard_shift_inv r.step r.guard n p hr_le hr_dvd
    have hle1 : decide (r.step ≤ n + p) = true := decide_eq_true (by omega)
    have hle2 : decide (r.step ≤ n) = true := decide_eq_true hr_le
    have iht := ih hrs_le hrs_dvd
    unfold legalMoves at iht ⊢
    simp only [List.filterMap_cons, hle1, hle2, hge, iht]

/-- Single-move shift-invariance: if `s` is legal at `n` and `2 ^ gameShiftBits G ∣ p`,
then `s` is legal at `n + p`. -/
theorem legalMove_shift_inv (G : BitGame) (n p s : Nat)
    (hleg : legalMove G n s = true) (hdvd : 2 ^ gameShiftBits G ∣ p) :
    legalMove G (n + p) s = true := by
  induction G with
  | nil => simp [legalMove] at hleg
  | cons r rs ih =>
    simp only [legalMove, List.any_cons, Bool.or_eq_true] at hleg ⊢
    simp only [gameShiftBits] at hdvd
    rcases hleg with hr | hrs
    · left
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr ⊢
      rcases hr with ⟨⟨⟨hstep, hpos⟩, hle⟩, hguard⟩
      have hr_dvd : 2 ^ guardShiftBits r.step r.guard ∣ p :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_left _ _)) hdvd
      have hge := evalGuard_shift_inv r.step r.guard n p hle hr_dvd
      exact ⟨⟨⟨hstep, hpos⟩, by omega⟩, by rw [hge, hguard]⟩
    · right
      have hrs_dvd : 2 ^ gameShiftBits rs ∣ p :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_max_right _ _)) hdvd
      exact ih hrs hrs_dvd

/-! ### Regime I: Universal Infinite-Family Theorem — The Dyadic Borrow-Wall Theorem -/


theorem evalGuard_wall_false (s : Nat) (g : BitGuard) (L q r : Nat)
    (hwall : isWallGuard g = true) (hL : guardShiftBits s g ≤ L)
    (hq : q > 0) (hrs : r < s) :
    evalGuard s g (q * 2 ^ L + r) = false := by
  induction g with
  | always => simp [isWallGuard] at hwall
  | maskEq _ _ => simp [isWallGuard] at hwall
  | or _ _ => simp [isWallGuard] at hwall
  | not _ => simp [isWallGuard] at hwall
  | borrowFree =>
    simp only [evalGuard, guardShiftBits] at hL ⊢
    have hsk : s < 2 ^ bitLen s := lt_two_pow_bitLen s
    have hpow : 2 ^ L = 2 ^ (L - bitLen s) * 2 ^ bitLen s := by
      rw [← Nat.pow_add]; congr 1; omega
    have hrew : q * 2 ^ L + r = r + (q * 2 ^ (L - bitLen s)) * 2 ^ bitLen s := by
      rw [hpow, ← Nat.mul_assoc]; omega
    rw [hrew, land_add_mul_two_pow r _ s (bitLen s) hsk]
    have hle : (r &&& s) ≤ r := Nat.and_le_left
    exact beq_false_of_ne (by omega)
  | borrowDepthLe d =>
    simp only [evalGuard, guardShiftBits] at hL ⊢
    have hpow : 2 ^ L = 2 ^ (L - d) * 2 ^ d := by
      rw [← Nat.pow_add]; congr 1; omega
    have hmod : (q * 2 ^ L + r) % 2 ^ d = r % 2 ^ d := by
      rw [hpow, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [hmod]
    have : r % 2 ^ d ≤ r := Nat.mod_le r (2 ^ d)
    exact decide_eq_false (by omega)
  | borrowCountLe B =>
    simp only [evalGuard, guardShiftBits] at hL ⊢
    have hgt := borrowCount_cross_wall_gt s (bitLen s) B L q r (lt_two_pow_bitLen s) hL hq hrs
    exact decide_eq_false (by omega)
  | borrowCountEq B =>
    simp only [evalGuard, guardShiftBits] at hL ⊢
    have hgt := borrowCount_cross_wall_gt s (bitLen s) B L q r (lt_two_pow_bitLen s) hL hq hrs
    exact decide_eq_false (by omega)
  | popcountDeltaLe delta =>
    simp only [evalGuard, guardShiftBits] at hL ⊢
    have hL' : bitLen s + (popcount s + delta) ≤ L := by omega
    have hgt := borrowCount_cross_wall_gt s (bitLen s) (popcount s + delta) L q r
      (lt_two_pow_bitLen s) hL' hq hrs
    have hle_n : s ≤ q * 2 ^ L + r := by
      have hsk : s < 2 ^ bitLen s := lt_two_pow_bitLen s
      have hpow : 2 ^ bitLen s ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
      have hq1 : 1 * 2 ^ L ≤ q * 2 ^ L := Nat.mul_le_mul_right (2 ^ L) hq
      omega
    have hk := kummer_borrow_popcount (q * 2 ^ L + r) s hle_n
    exact decide_eq_false (by omega)
  | and g1 g2 ih1 ih2 =>
    simp only [isWallGuard, Bool.or_eq_true] at hwall
    simp only [evalGuard, guardShiftBits] at hL ⊢
    rcases hwall with hw1 | hw2
    · rw [ih1 hw1 (Nat.le_trans (Nat.le_max_left _ _) hL)]; simp
    · rw [ih2 hw2 (Nat.le_trans (Nat.le_max_right _ _) hL)]; simp

/-- **Regime I — Dyadic Borrow-Wall Crossing Impossibility (Game Level)**:
In any wall-guarded game `G` with `L = gameShiftBits G`, no legal move can ever cross a `2^L`-boundary. -/
theorem dyadic_wall_no_crossing (G : BitGame)
    (hwall : ∀ r ∈ G, isWallGuard r.guard = true)
    (q r s : Nat) (hq : q > 0) (hrs : r < s) :
    legalMove G (q * 2 ^ gameShiftBits G + r) s = false := by
  cases hm : legalMove G (q * 2 ^ gameShiftBits G + r) s with
  | false => rfl
  | true =>
    exfalso
    unfold legalMove at hm
    obtain ⟨rule, hrmem, hcond⟩ := List.any_eq_true.mp hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨⟨⟨hstep, _⟩, _⟩, hge⟩
    subst hstep
    have hf := evalGuard_wall_false rule.step rule.guard (gameShiftBits G) q r
      (hwall rule hrmem) (guardShiftBits_le_gameShiftBits hrmem) hq hrs
    rw [hf] at hge
    cases hge

private theorem legalMoves_wall_shift_eq (G : BitGame) (L : Nat)
    (hwall : ∀ r ∈ G, isWallGuard r.guard = true)
    (hL : ∀ r ∈ G, guardShiftBits r.step r.guard ≤ L)
    (n : Nat) :
    legalMoves G (n + 2 ^ L) = legalMoves G n := by
  induction G with
  | nil => rfl
  | cons rule rs ih =>
    have hw_rule := hwall rule (List.Mem.head _)
    have hL_rule := hL rule (List.Mem.head _)
    have iht := ih (fun x hx => hwall x (List.Mem.tail _ hx)) (fun x hx => hL x (List.Mem.tail _ hx))
    unfold legalMoves at iht ⊢
    simp only [List.filterMap_cons, iht]
    let q := n / 2 ^ L
    let r := n % 2 ^ L
    have hneq : n = q * 2 ^ L + r := by
      have h := Nat.div_add_mod n (2 ^ L)
      rw [Nat.mul_comm] at h
      exact h.symm
    have hnp : n + 2 ^ L = (q + 1) * 2 ^ L + r := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    by_cases hsr : rule.step ≤ r
    · have hle_n : rule.step ≤ n := by omega
      have hle_np : rule.step ≤ n + 2 ^ L := by omega
      have hdvd : 2 ^ guardShiftBits rule.step rule.guard ∣ 2 ^ L := Nat.pow_dvd_pow 2 hL_rule
      have hge := evalGuard_shift_inv rule.step rule.guard n (2 ^ L) hle_n hdvd
      simp [hle_n, hle_np, hge]
    · have hrs : r < rule.step := by omega
      have hf_np : evalGuard rule.step rule.guard (n + 2 ^ L) = false := by
        rw [hnp]
        exact evalGuard_wall_false rule.step rule.guard L (q + 1) r hw_rule hL_rule (Nat.succ_pos q) hrs
      have hcond_n : (decide (0 < rule.step) && decide (rule.step ≤ n) && evalGuard rule.step rule.guard n) = false := by
        by_cases hq0 : q = 0
        · have hnr : n = r := by rw [hq0, Nat.zero_mul, Nat.zero_add] at hneq; exact hneq
          have hf_le : decide (rule.step ≤ n) = false := decide_eq_false (by omega)
          simp [hf_le]
        · have hf_n : evalGuard rule.step rule.guard n = false := by
            rw [hneq]
            exact evalGuard_wall_false rule.step rule.guard L q r hw_rule hL_rule (Nat.pos_of_ne_zero hq0) hrs
          simp [hf_n]
      simp [hf_np, hcond_n]

/-- **Regime I — Universal Dyadic Borrow-Wall Periodicity Theorem**:
For ANY finite bitwise/carry subtraction game `G` whose rules are all wall-guarded
(`borrowFree`, `borrowDepthLe`, `borrowCountLe`, `borrowCountEq`, `popcountDeltaLe`, or `and` thereof),
letting `L = gameShiftBits G`:
1. `grundy G` is **purely periodic from `n = 0`** with period `2^L`: `∀ n, grundy G (n + 2^L) = grundy G n`.
2. Exact modular reduction: `∀ n, grundy G n = grundy G (n % 2^L)`. -/
theorem dyadic_borrow_wall_periodicity (G : BitGame)
    (hwall : ∀ r ∈ G, isWallGuard r.guard = true) :
    ∀ n, grundy G (n + 2 ^ gameShiftBits G) = grundy G n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [grundy_eq G (n + 2 ^ gameShiftBits G), grundy_eq G n]
    have hmoves : legalMoves G (n + 2 ^ gameShiftBits G) = legalMoves G n :=
      legalMoves_wall_shift_eq G (gameShiftBits G) hwall
        (fun r hr => guardShiftBits_le_gameShiftBits hr) n
    rw [hmoves]
    congr 1
    apply List.map_congr_left
    intro s hs
    have hleg : legalMove G n s = true := (mem_legalMoves_iff G n s).mp hs
    have hb := legalMove_bounds hleg
    have hsub : n + 2 ^ gameShiftBits G - s = (n - s) + 2 ^ gameShiftBits G :=
      Nat.sub_add_comm hb.2.1
    rw [hsub]
    exact ih (n - s) (by have hpos := hb.1; have hle := hb.2.1; omega)

theorem dyadic_borrow_wall_mod (G : BitGame)
    (hwall : ∀ r ∈ G, isWallGuard r.guard = true) (n : Nat) :
    grundy G n = grundy G (n % 2 ^ gameShiftBits G) := by
  let M := 2 ^ gameShiftBits G
  have hstep : ∀ q r, grundy G (q * M + r) = grundy G r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih =>
      have hrew : (q + 1) * M + r = (q * M + r) + M := by rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hrew, dyadic_borrow_wall_periodicity G hwall, ih]
  have hdiv : n = (n / M) * M + n % M := by
    have h := Nat.div_add_mod n M
    rw [Nat.mul_comm] at h
    exact h.symm
  calc grundy G n = grundy G ((n / M) * M + n % M) := congrArg (grundy G) hdiv
    _ = grundy G (n % M) := hstep (n / M) (n % M)

theorem dyadic_borrow_wall_winning_mod (G : BitGame)
    (hwall : ∀ r ∈ G, isWallGuard r.guard = true) (n : Nat) :
    IsWinning G n ↔ IsWinning G (n % 2 ^ gameShiftBits G) := by
  rw [isWinning_iff_grundy_ne_zero, isWinning_iff_grundy_ne_zero, dyadic_borrow_wall_mod G hwall n]

/-! ## Section 4: Reusable Verified Sprague-Grundy Periodicity & Winning-Bitmask Compiler (Regime II) -/

/-! ### Unpacked certificate invariants & Soundness Meta-Theorems -/

private structure CertChecks (G : BitGame) (c : PeriodWinCert) : Prop where
  pos_period : 0 < c.period
  pos_minPeriod : 0 < c.minPeriod
  minPeriod_dvd : c.minPeriod ∣ c.period
  shift_dvd : 2 ^ gameShiftBits G ∣ c.period
  rec_ok : ∀ n, n < c.preperiod + c.period + maxStep G →
    evalPeriodic c n = mex ((legalMoves G n).map (fun s => evalPeriodic c (n - s)))
  comp_ok : ∀ r, r < c.period →
    c.table.getD (c.preperiod + r) 0 = c.table.getD (c.preperiod + r % c.minPeriod) 0
  preMask_ok : ∀ i, i < c.preperiod →
    c.preWinMask.testBit i = decide (c.table.getD i 0 ≠ 0)
  perMask_ok : ∀ r, r < c.minPeriod →
    c.perWinMask.testBit r = decide (c.table.getD (c.preperiod + r) 0 ≠ 0)
  preMove_ok : ∀ n, n < c.preperiod + maxStep G → evalPeriodic c n ≠ 0 →
    legalMove G n (c.preMoves.getD n 0) = true ∧ evalPeriodic c (n - c.preMoves.getD n 0) = 0
  perMove_ok : ∀ r, r < c.period → evalPeriodic c (c.preperiod + maxStep G + r) ≠ 0 →
    legalMove G (c.preperiod + maxStep G + r) (c.perMoves.getD r 0) = true ∧
    evalPeriodic c (c.preperiod + maxStep G + r - c.perMoves.getD r 0) = 0

private theorem checkCert_unpack {G : BitGame} {c : PeriodWinCert} (h : checkCert G c = true) :
    CertChecks G c := by
  unfold checkCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allLt_iff] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hposP⟩, hposM⟩, hmodM⟩, _⟩, hmodS⟩, hrec⟩, hcomp⟩, hpreM⟩, hperM⟩, _⟩, _⟩, hpreMv⟩, hperMv⟩
  refine ⟨hposP, hposM, Nat.dvd_of_mod_eq_zero hmodM, Nat.dvd_of_mod_eq_zero hmodS, hrec, hcomp, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hpreM i hi]
    cases c.table.getD i 0 <;> rfl
  · intro r hr
    rw [hperM r hr]
    cases c.table.getD (c.preperiod + r) 0 <;> rfl
  · intro n hn hne
    have h1 := hpreMv n hn
    split at h1
    · rename_i hz; exact absurd hz hne
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1; exact h1
  · intro r hr hne
    have h1 := hperMv r hr
    split at h1
    · rename_i hz; exact absurd hz hne
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1; exact h1

theorem evalPeriodic_shift (c : PeriodWinCert) (n : Nat) (hn : c.preperiod ≤ n) :
    evalPeriodic c (n + c.period) = evalPeriodic c n := by
  unfold evalPeriodic
  have h1 : ¬(n + c.period < c.preperiod) := by omega
  have h2 : ¬(n < c.preperiod) := by omega
  simp only [h1, h2, ↓reduceIte]
  have hsub : n + c.period - c.preperiod = (n - c.preperiod) + c.period := by omega
  rw [hsub, Nat.add_mod_right]

theorem evalPeriodic_shift_mul (c : PeriodWinCert) (n k : Nat) (hn : c.preperiod ≤ n) :
    evalPeriodic c (n + k * c.period) = evalPeriodic c n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrew : n + (k + 1) * c.period = (n + k * c.period) + c.period := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hrew, evalPeriodic_shift c (n + k * c.period) (by omega), ih]

/-- **Soundness Meta-Theorem 1 (Exact Infinite Grundy Equivalence `∀ n : Nat`)**:
If `checkCert G c = true`, then `grundy G n = evalPeriodic c n` for ALL `n : Nat`. -/
theorem checkCert_sound_grundy (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, grundy G n = evalPeriodic c n := by
  have hc := checkCert_unpack h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < c.preperiod + c.period + maxStep G
    · rw [grundy_eq G n, hc.rec_ok n hlt]
      congr 1
      apply List.map_congr_left
      intro s hs
      have hleg : legalMove G n s = true := (mem_legalMoves_iff G n s).mp hs
      have hb := legalMove_bounds hleg
      exact ih (n - s) (by omega)
    · -- Inductive shift-invariance lift for all n ≥ preperiod + period + maxStep G
      let m := n - c.period
      have hmn : m + c.period = n := by omega
      have hm_ge_ms : maxStep G ≤ m := by omega
      have hm_ge_pre : c.preperiod ≤ m := by omega
      have hmoves : legalMoves G n = legalMoves G m := by
        rw [← hmn]
        exact legalMoves_shift_inv G m c.period hm_ge_ms hc.shift_dvd
      have hg_eq : grundy G n = grundy G m := by
        rw [grundy_eq G n, grundy_eq G m, hmoves]
        congr 1
        apply List.map_congr_left
        intro s hs
        have hleg : legalMove G m s = true := (mem_legalMoves_iff G m s).mp hs
        have hb := legalMove_bounds hleg
        have hns_eq : n - s = (m - s) + c.period := by omega
        have hms_pre : c.preperiod ≤ m - s := by omega
        rw [ih (n - s) (by omega), hns_eq, evalPeriodic_shift c (m - s) hms_pre,
            ← ih (m - s) (by have := hc.pos_period; omega)]
      rw [hg_eq, ih m (by have := hc.pos_period; omega), ← hmn, evalPeriodic_shift c m hm_ge_pre]

/-- **Soundness Meta-Theorem 2 (Exact Ultimate Periodicity at Certificate Period)**. -/
theorem checkCert_sound_period (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, c.preperiod ≤ n → grundy G (n + c.period) = grundy G n := by
  intro n hn
  rw [checkCert_sound_grundy G c h (n + c.period), checkCert_sound_grundy G c h n]
  exact evalPeriodic_shift c n hn

/-- **Soundness Meta-Theorem 3 (Exact Compressed Minimal-Period Ultimate Periodicity `∀ n ≥ n0`)**:
Certifies minimal period `c.minPeriod` even when `c.minPeriod` is NOT divisible by `2^L` (e.g. odd period `5`). -/
theorem checkCert_sound_minPeriod (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, c.preperiod ≤ n → grundy G (n + c.minPeriod) = grundy G n := by
  have hc := checkCert_unpack h
  have hcomp_eval : ∀ x, c.preperiod ≤ x →
      evalPeriodic c x = c.table.getD (c.preperiod + (x - c.preperiod) % c.minPeriod) 0 := by
    intro x hx
    unfold evalPeriodic
    have hnot : ¬(x < c.preperiod) := by omega
    simp only [hnot, ↓reduceIte]
    rw [hc.comp_ok ((x - c.preperiod) % c.period) (Nat.mod_lt _ hc.pos_period)]
    obtain ⟨q, hq⟩ := hc.minPeriod_dvd
    have hmod : (x - c.preperiod) % c.period % c.minPeriod = (x - c.preperiod) % c.minPeriod := by
      rw [hq, Nat.mod_mul_right_mod]
    rw [hmod]
  intro n hn
  rw [checkCert_sound_grundy G c h (n + c.minPeriod), checkCert_sound_grundy G c h n,
      hcomp_eval (n + c.minPeriod) (by omega), hcomp_eval n hn]
  have hsub : n + c.minPeriod - c.preperiod = (n - c.preperiod) + c.minPeriod := by omega
  rw [hsub, Nat.add_mod_right]

/-- **Soundness Meta-Theorem 4 (Exact Preperiod Winning-Strategy Bitmask Law)**. -/
theorem checkCert_sound_winMask_pre (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, n < c.preperiod → (IsWinning G n ↔ c.preWinMask.testBit n = true) := by
  have hc := checkCert_unpack h
  intro n hn
  rw [isWinning_iff_grundy_ne_zero, checkCert_sound_grundy G c h n]
  unfold evalPeriodic
  simp only [hn, ↓reduceIte, hc.preMask_ok n hn, decide_eq_true_eq]

/-- **Soundness Meta-Theorem 5 (Exact Periodic Winning-Strategy Bitmask Law `∀ n ≥ n0`)**:
A single packed binary integer `c.perWinMask` decides win/loss for ALL `n ≥ c.preperiod`. -/
theorem checkCert_sound_winMask_per (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, c.preperiod ≤ n →
      (IsWinning G n ↔ c.perWinMask.testBit ((n - c.preperiod) % c.minPeriod) = true) := by
  have hc := checkCert_unpack h
  intro n hn
  rw [isWinning_iff_grundy_ne_zero, checkCert_sound_grundy G c h n]
  unfold evalPeriodic
  have hnot : ¬(n < c.preperiod) := by omega
  simp only [hnot, ↓reduceIte]
  rw [hc.comp_ok ((n - c.preperiod) % c.period) (Nat.mod_lt _ hc.pos_period)]
  obtain ⟨q, hq⟩ := hc.minPeriod_dvd
  have hmod : (n - c.preperiod) % c.period % c.minPeriod = (n - c.preperiod) % c.minPeriod := by
    rw [hq, Nat.mod_mul_right_mod]
  rw [hmod, hc.perMask_ok _ (Nat.mod_lt _ hc.pos_minPeriod), decide_eq_true_eq]

/-- **Soundness Meta-Theorem 6 (Constructive Winning-Move Oracle `∀ n : Nat`)**:
For EVERY winning heap `n : Nat`, `evalWinMove G c n` returns a legal move landing in a losing position! -/
theorem checkCert_sound_winMove (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ n, IsWinning G n →
      legalMove G n (evalWinMove G c n) = true ∧ ¬ IsWinning G (n - evalWinMove G c n) := by
  have hc := checkCert_unpack h
  intro n hwin
  have hne : evalPeriodic c n ≠ 0 := by
    rw [← checkCert_sound_grundy G c h n]
    exact (isWinning_iff_grundy_ne_zero G n).mp hwin
  unfold evalWinMove
  dsimp only
  split
  · rename_i hlt
    obtain ⟨hleg, hzero⟩ := hc.preMove_ok n hlt hne
    refine ⟨hleg, ?_⟩
    rw [isWinning_iff_grundy_ne_zero, checkCert_sound_grundy G c h]
    exact fun h0 => h0 hzero
  · rename_i hlt
    let r := (n - (c.preperiod + maxStep G)) % c.period
    let k := (n - (c.preperiod + maxStep G)) / c.period
    let m := c.preperiod + maxStep G + r
    have hdiv : n - (c.preperiod + maxStep G) = k * c.period + r := by
      have hdm := Nat.div_add_mod (n - (c.preperiod + maxStep G)) c.period
      rw [Nat.mul_comm] at hdm; exact hdm.symm
    have hnm : n = m + k * c.period := by omega
    have hr_lt : r < c.period := Nat.mod_lt _ hc.pos_period
    have hm_ne : evalPeriodic c m ≠ 0 := by
      have heq := evalPeriodic_shift_mul c m k (by omega)
      rw [← hnm] at heq
      rw [← heq]; exact hne
    obtain ⟨hleg_m, hzero_m⟩ := hc.perMove_ok r hr_lt hm_ne
    have hkp_dvd : 2 ^ gameShiftBits G ∣ k * c.period := Nat.dvd_mul_left_of_dvd hc.shift_dvd k
    have hleg_n : legalMove G n (c.perMoves.getD r 0) = true := by
      rw [hnm]
      exact legalMove_shift_inv G m (k * c.period) (c.perMoves.getD r 0) hleg_m hkp_dvd
    refine ⟨hleg_n, ?_⟩
    rw [isWinning_iff_grundy_ne_zero, checkCert_sound_grundy G c h]
    have hb := legalMove_bounds hleg_m
    have hsub : n - c.perMoves.getD r 0 = (m - c.perMoves.getD r 0) + k * c.period := by omega
    have hge_pre : c.preperiod ≤ m - c.perMoves.getD r 0 := by omega
    rw [hsub, evalPeriodic_shift_mul c (m - c.perMoves.getD r 0) k hge_pre, hzero_m]
    exact fun h0 => h0 rfl

/-- **Soundness Meta-Theorem 7 (Losing Position Closure `∀ n : Nat`)**:
Every legal move from a losing position lands in a winning position. -/
theorem checkCert_sound_losing_closure (G : BitGame) (n : Nat) (hlose : ¬ IsWinning G n) :
    ∀ s, legalMove G n s = true → IsWinning G (n - s) := by
  intro s hleg
  by_cases hw : IsWinning G (n - s)
  · exact hw
  · exfalso
    exact hlose ((isWinning_iff G n).mpr ⟨s, hleg, hw⟩)

/-- **Soundness Meta-Theorem 8 (Certified Multi-Heap Disjunctive-Sum Law `∀ hs : List Nat`)**:
Any finite disjunctive sum of heaps `hs` is winning iff the XOR of the certified periodic Grundy
values is nonzero! -/
theorem checkCert_sound_multiHeap (G : BitGame) (c : PeriodWinCert) (h : checkCert G c = true) :
    ∀ hs : List Nat, IsWinningMulti G hs ↔ nimSum (hs.map (evalPeriodic c)) ≠ 0 := by
  intro hs
  rw [isWinningMulti_iff_nimSum_ne_zero]
  have hmap : hs.map (grundy G) = hs.map (evalPeriodic c) :=
    List.map_congr_left fun x _ => checkCert_sound_grundy G c h x
  rw [hmap]

/-! ## Section 5: Discharged Novel Infinite Theorems via the Compiler (6 Showcase Games) -/

/-- **Game 1 (`G_pop136`)**: Popcount-Nonincreasing Subtraction `{1, 3, 6}`
(`popcount (n - s) ≤ popcount n`). Exemplifies BOTH Regime I (Dyadic Borrow-Wall)
and Regime II (exact minimal period `16`, winning bitmask `0xd5ea = 54762`, density `10/16`). -/
def G_pop136 : BitGame :=
  [⟨1, .popcountDeltaLe 0⟩, ⟨3, .popcountDeltaLe 0⟩, ⟨6, .popcountDeltaLe 0⟩]

def cert_G_pop136 : PeriodWinCert := {
  preperiod  := 0
  period     := 32
  minPeriod  := 16
  table      := #[0, 1, 0, 1, 0, 1, 2, 3, 1, 0, 1, 0, 1, 0, 2, 3, 0, 1, 0, 1, 0, 1, 2, 3, 1, 0, 1, 0, 1, 0, 2, 3]
  preWinMask := 0
  perWinMask := 54762
  preMoves   := #[0, 1, 0, 1, 0, 1]
  perMoves   := #[6, 3, 6, 0, 1, 0, 3, 0, 1, 6, 0, 1, 0, 1, 0, 1, 6, 3, 6, 0, 1, 0, 3, 0, 1, 6, 0, 1, 0, 1, 0, 1]
}

theorem cert_G_pop136_ok : checkCert G_pop136 cert_G_pop136 = true := by decide

theorem G_pop136_borrow_wall_pure_32 : ∀ n, grundy G_pop136 (n + 32) = grundy G_pop136 n := by
  have hwall : ∀ r ∈ G_pop136, isWallGuard r.guard = true := by decide
  have hshift : 2 ^ gameShiftBits G_pop136 = 32 := by decide
  rw [← hshift]
  exact dyadic_borrow_wall_periodicity G_pop136 hwall

theorem G_pop136_period_16 : ∀ n, grundy G_pop136 (n + 16) = grundy G_pop136 n :=
  fun n => checkCert_sound_minPeriod G_pop136 cert_G_pop136 cert_G_pop136_ok n (Nat.zero_le n)

theorem G_pop136_winMask : ∀ n, IsWinning G_pop136 n ↔ (54762 : Nat).testBit (n % 16) = true :=
  fun n => checkCert_sound_winMask_per G_pop136 cert_G_pop136 cert_G_pop136_ok n (Nat.zero_le n)

theorem G_pop136_winMove :
    ∀ n, IsWinning G_pop136 n →
      legalMove G_pop136 n (evalWinMove G_pop136 cert_G_pop136 n) = true ∧
      ¬ IsWinning G_pop136 (n - evalWinMove G_pop136 cert_G_pop136 n) :=
  checkCert_sound_winMove G_pop136 cert_G_pop136 cert_G_pop136_ok

/-- **Game 2 (`G_wallbreach_24`)**: Borrow-Free Phase `B = 0` of `{1(B=0), 3(always), 4(B=0)}`.
Wall-breaching via `3(always)` induces nontrivial preperiod `n0 = 5` and non-power-of-2 period `24`. -/
def G_wallbreach_24 : BitGame :=
  [⟨1, .borrowCountLe 0⟩, ⟨3, .always⟩, ⟨4, .borrowCountLe 0⟩]

def cert_G_wallbreach_24 : PeriodWinCert := {
  preperiod  := 5
  period     := 24
  minPeriod  := 24
  table      := #[0, 1, 0, 1, 2, 3, 2, 0, 0, 1, 1, 2, 2, 0, 0, 1, 1, 2, 0, 2, 0, 1, 1, 3, 0, 2, 0, 1, 1]
  preWinMask := 26
  perWinMask := 14114035
  preMoves   := #[0, 1, 0, 1, 4, 3, 4, 0, 0]
  perMoves   := #[1, 3, 3, 4, 0, 0, 1, 3, 3, 0, 1, 0, 1, 4, 3, 0, 1, 0, 1, 4, 3, 4, 0, 0]
}

theorem cert_G_wallbreach_24_ok : checkCert G_wallbreach_24 cert_G_wallbreach_24 = true := by decide

theorem G_wallbreach_24_period : ∀ n, 5 ≤ n → grundy G_wallbreach_24 (n + 24) = grundy G_wallbreach_24 n :=
  checkCert_sound_minPeriod G_wallbreach_24 cert_G_wallbreach_24 cert_G_wallbreach_24_ok

theorem G_wallbreach_24_winMask :
    ∀ n, 5 ≤ n → (IsWinning G_wallbreach_24 n ↔ (14114035 : Nat).testBit ((n - 5) % 24) = true) :=
  checkCert_sound_winMask_per G_wallbreach_24 cert_G_wallbreach_24 cert_G_wallbreach_24_ok

/-- **Game 3 (`G_wallbreach_48`)**: Single-Borrow Phase `B = 1` of `{1(B≤1), 3(always), 4(B≤1)}`.
Increasing borrow budget `0 → 1` causes a sharp phase transition: `(n0=5, p=24) → (n0=0, p=48)`! -/
def G_wallbreach_48 : BitGame :=
  [⟨1, .borrowCountLe 1⟩, ⟨3, .always⟩, ⟨4, .borrowCountLe 1⟩]

def cert_G_wallbreach_48 : PeriodWinCert := {
  preperiod  := 0
  period     := 48
  minPeriod  := 48
  table      := #[0, 1, 0, 1, 2, 3, 2, 0, 0, 1, 3, 1, 2, 0, 2, 0, 1, 0, 1, 0, 2, 3, 2, 1, 0, 1, 0, 2, 2, 3, 1, 0, 0, 2, 1, 2, 1, 0, 3, 0, 2, 1, 2, 1, 0, 3, 0, 2]
  preWinMask := 0
  perWinMask := 192820324687482
  preMoves   := #[0, 1, 0, 1]
  perMoves   := #[4, 3, 4, 0, 0, 1, 3, 3, 4, 0, 1, 0, 3, 0, 1, 0, 3, 4, 3, 4, 0, 1, 0, 1, 4, 3, 4, 0, 0, 1, 3, 3, 4, 0, 1, 0, 3, 4, 3, 4, 0, 1, 0, 1, 0, 1, 0, 1]
}

theorem cert_G_wallbreach_48_ok : checkCert G_wallbreach_48 cert_G_wallbreach_48 = true := by decide

theorem G_wallbreach_48_period : ∀ n, grundy G_wallbreach_48 (n + 48) = grundy G_wallbreach_48 n :=
  fun n => checkCert_sound_minPeriod G_wallbreach_48 cert_G_wallbreach_48 cert_G_wallbreach_48_ok n (Nat.zero_le n)

theorem G_wallbreach_48_winMask :
    ∀ n, IsWinning G_wallbreach_48 n ↔ (192820324687482 : Nat).testBit (n % 48) = true :=
  fun n => checkCert_sound_winMask_per G_wallbreach_48 cert_G_wallbreach_48 cert_G_wallbreach_48_ok n (Nat.zero_le n)


def cert_G_coprime_p5 : PeriodWinCert := {
  preperiod  := 15
  period     := 20
  minPeriod  := 5
  table      := #[0, 0, 1, 1, 1, 0, 0, 2, 1, 2, 0, 0, 1, 1, 3, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2]
  preWinMask := 29596
  perWinMask := 28
  preMoves   := #[0, 0, 2, 2, 3, 0, 0, 2, 3, 3, 0, 0, 7, 3, 3, 0, 0, 7, 2, 3, 0, 0]
  perMoves   := #[2, 2, 3, 0, 0, 2, 3, 3, 0, 0, 7, 3, 3, 0, 0, 7, 2, 3, 0, 0]
}

theorem cert_G_coprime_p5_ok : checkCert G_coprime_p5 cert_G_coprime_p5 = true := by decide

theorem G_coprime_p5_period_5 : ∀ n, 15 ≤ n → grundy G_coprime_p5 (n + 5) = grundy G_coprime_p5 n :=
  checkCert_sound_minPeriod G_coprime_p5 cert_G_coprime_p5 cert_G_coprime_p5_ok

theorem G_coprime_p5_winMask :
    ∀ n, 15 ≤ n → (IsWinning G_coprime_p5 n ↔ (28 : Nat).testBit ((n - 15) % 5) = true) :=
  checkCert_sound_winMask_per G_coprime_p5 cert_G_coprime_p5 cert_G_coprime_p5_ok

theorem G_coprime_p5_multiHeap :
    ∀ hs : List Nat, IsWinningMulti G_coprime_p5 hs ↔ nimSum (hs.map (evalPeriodic cert_G_coprime_p5)) ≠ 0 :=
  checkCert_sound_multiHeap G_coprime_p5 cert_G_coprime_p5 cert_G_coprime_p5_ok

/-- **Game 5 (`G_hybrid_40`)**: Five-Fold Carry-Resonance `{1(borrowFree), 2(B≤1), 5(always)}`.
Exact period `40 = 5 × 8` from `n = 0`, 40-bit winning-strategy bitmask `0xd9b66e9b66`. -/
def G_hybrid_40 : BitGame :=
  [⟨1, .borrowFree⟩, ⟨2, .borrowCountLe 1⟩, ⟨5, .always⟩]

def cert_G_hybrid_40 : PeriodWinCert := {
  preperiod  := 0
  period     := 40
  minPeriod  := 40
  table      := #[0, 1, 1, 0, 0, 1, 2, 0, 1, 2, 0, 1, 1, 0, 0, 1, 0, 2, 1, 3, 0, 1, 1, 0, 0, 1, 2, 0, 1, 2, 0, 1, 1, 0, 0, 1, 2, 0, 1, 2]
  preWinMask := 0
  perWinMask := 935068605286
  preMoves   := #[0, 1, 2, 0, 0]
  perMoves   := #[1, 2, 0, 5, 5, 0, 1, 2, 0, 0, 1, 0, 1, 2, 5, 0, 1, 2, 0, 0, 1, 2, 0, 5, 2, 0, 1, 5, 0, 0, 1, 2, 0, 5, 2, 0, 1, 2, 0, 0]
}

theorem cert_G_hybrid_40_ok : checkCert G_hybrid_40 cert_G_hybrid_40 = true := by decide

theorem G_hybrid_40_period : ∀ n, grundy G_hybrid_40 (n + 40) = grundy G_hybrid_40 n :=
  fun n => checkCert_sound_minPeriod G_hybrid_40 cert_G_hybrid_40 cert_G_hybrid_40_ok n (Nat.zero_le n)

theorem G_hybrid_40_winMask :
    ∀ n, IsWinning G_hybrid_40 n ↔ (935068605286 : Nat).testBit (n % 40) = true :=
  fun n => checkCert_sound_winMask_per G_hybrid_40 cert_G_hybrid_40 cert_G_hybrid_40_ok n (Nat.zero_le n)

/-- **Game 6 (`G_compound`)**: Full-DSL Compound Guard exercising `borrowCountEq`, `borrowDepthLe`,
`maskEq`, `and`, `or`, `not`. Exact preperiod `3`, period `16`, winning bitmask `0x8ccd = 36045`. -/
def G_compound : BitGame :=
  [⟨1, .borrowCountEq 1⟩,
   ⟨2, .and (.not (.maskEq 3 0)) (.borrowCountLe 2)⟩,
   ⟨5, .or (.borrowDepthLe 3) (.maskEq 7 2)⟩]

def cert_G_compound : PeriodWinCert := {
  preperiod  := 3
  period     := 16
  minPeriod  := 16
  table      := #[0, 0, 1, 1, 0, 2, 1, 0, 0, 1, 3, 0, 0, 1, 2, 0, 0, 0, 2]
  preWinMask := 4
  perWinMask := 36045
  preMoves   := #[0, 0, 1, 2, 0, 5, 2, 0]
  perMoves   := #[0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 1, 2, 0, 5, 2, 0]
}

theorem cert_G_compound_ok : checkCert G_compound cert_G_compound = true := by decide

theorem G_compound_period : ∀ n, 3 ≤ n → grundy G_compound (n + 16) = grundy G_compound n :=
  checkCert_sound_minPeriod G_compound cert_G_compound cert_G_compound_ok

theorem G_compound_winMask :
    ∀ n, 3 ≤ n → (IsWinning G_compound n ↔ (36045 : Nat).testBit ((n - 3) % 16) = true) :=
  checkCert_sound_winMask_per G_compound cert_G_compound cert_G_compound_ok

/-- Kernel-checked Non-Vacuity Witness: all 6 showcase certificates are inhabited and
yield concrete winning & losing heaps (including multi-heap disjunctive sums). -/
theorem non_vacuity_showcase :
    (IsWinning G_pop136 1007 ∧ ¬ IsWinning G_pop136 1008) ∧
    (IsWinning G_coprime_p5 1002 ∧ ¬ IsWinning G_coprime_p5 1000) ∧
    (¬ IsWinningMulti G_coprime_p5 [1002, 1007] ∧ IsWinningMulti G_coprime_p5 [14, 19]) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (G_pop136_winMask 1007).mpr (by decide)
  · intro hw; exact absurd ((G_pop136_winMask 1008).mp hw) (by decide)
  · exact (G_coprime_p5_winMask 1002 (by omega)).mpr (by decide)
  · intro hw; exact absurd ((G_coprime_p5_winMask 1000 (by omega)).mp hw) (by decide)
  · intro hw; exact ((G_coprime_p5_multiHeap [1002, 1007]).mp hw) (by decide)
  · exact (G_coprime_p5_multiHeap [14, 19]).mpr (by decide)

/-! ## Section 6: Regime III — Proved Aperiodic Sharpness Boundary & Tightness Witnesses -/

/-- Exact preperiod sharpness for `G_coprime_p5`: `g(14) = 3 ≠ 2 = g(19)` (`n0 = 15` is minimal). -/
theorem preperiod_sharp_coprime_p5 :
    grundy G_coprime_p5 14 = 3 ∧ grundy G_coprime_p5 19 = 2 := by
  rw [checkCert_sound_grundy G_coprime_p5 cert_G_coprime_p5 cert_G_coprime_p5_ok 14,
      checkCert_sound_grundy G_coprime_p5 cert_G_coprime_p5 cert_G_coprime_p5_ok 19]
  decide

/-- Exact preperiod sharpness for `G_wallbreach_24`: `g(4) = 2 ≠ 1 = g(28)` (`n0 = 5` is minimal). -/
theorem preperiod_sharp_wallbreach_24 :
    grundy G_wallbreach_24 4 = 2 ∧ grundy G_wallbreach_24 28 = 1 := by
  rw [checkCert_sound_grundy G_wallbreach_24 cert_G_wallbreach_24 cert_G_wallbreach_24_ok 4,
      checkCert_sound_grundy G_wallbreach_24 cert_G_wallbreach_24 cert_G_wallbreach_24_ok 28]
  decide

/-- Exact dyadic modulus sharpness for `borrowCount_le_shift_inv`:
For `s = 1` (`k = 1`) and `B = 1`, shift `2^(k+B) = 4` is minimal because shift `2^(k+B-1) = 2` fails at `n = 2`. -/
theorem borrowCount_localization_modulus_sharp :
    borrowCount 2 1 ≤ 1 ∧ ¬ (borrowCount (2 + 2) 1 ≤ 1) := by
  decide


theorem borrowCount_one_eq_ctz (n : Nat) (hn : n > 0) :
    borrowCount n 1 = ctz n := by
  unfold borrowCount borrowMask
  by_cases hodd : n % 2 = 1
  · rw [ctz_odd hodd]
    have h1 : n = (n / 2) * 2 + 1 := by omega
    have h2 : n - 1 = (n / 2) * 2 + 0 := by omega
    have hx := xor_shift_add (n / 2) (n / 2) 1 0 1 (by omega) (by omega)
    simp only [Nat.pow_one] at hx
    rw [← h1, ← h2] at hx
    rw [hx, Nat.xor_self, Nat.zero_mul, Nat.zero_add]
    decide
  · have hev : n % 2 = 0 := by omega
    have hq : n / 2 > 0 := by omega
    have h1 : n = (n / 2) * 2 + 0 := by omega
    have h2 : n - 1 = (n / 2 - 1) * 2 + 1 := by omega
    have hx := xor_shift_add (n / 2) (n / 2 - 1) 0 1 1 (by omega) (by omega)
    simp only [Nat.pow_one] at hx
    rw [← h1, ← h2] at hx
    have h01 : (0 : Nat) ^^^ 1 = 1 := by decide
    rw [h01] at hx
    have hx2 := xor_shift_add ((n / 2) ^^^ (n / 2 - 1)) 0 1 1 1 (by omega) (by omega)
    simp only [Nat.pow_one, Nat.zero_mul, Nat.zero_add, Nat.xor_zero, Nat.xor_self] at hx2
    rw [hx, hx2, popcount_shift_add _ 0 1 (by omega), popcount_zero, Nat.add_zero,
        popcount_xor_pred (n / 2) hq, ctz_even (by omega) hev]
    omega

theorem grundyParity_eq (n : Nat) :
    grundyParity n = mex (
      (if 1 ≤ n ∧ ctz n % 2 = 0 then [grundyParity (n - 1)] else []) ++
      (if 2 ≤ n then [grundyParity (n - 2)] else [])
    ) := by
  rw [grundyParity]
  by_cases h1 : 1 ≤ n
  · have hbc : borrowCount n 1 = ctz n := borrowCount_one_eq_ctz n (by omega)
    simp [h1, hbc]
  · simp [h1]

private theorem grundyParity_10_11 : grundyParity 10 = 0 ∧ grundyParity 11 = 1 := by
  have g0 : grundyParity 0 = 0 := by rw [grundyParity_eq]; decide
  have g1 : grundyParity 1 = 1 := by rw [grundyParity_eq, g0]; decide
  have g2 : grundyParity 2 = 1 := by rw [grundyParity_eq, g0]; decide
  have g3 : grundyParity 3 = 0 := by rw [grundyParity_eq, g2, g1]; decide
  have g4 : grundyParity 4 = 2 := by rw [grundyParity_eq, g3, g2]; decide
  have g5 : grundyParity 5 = 1 := by rw [grundyParity_eq, g4, g3]; decide
  have g6 : grundyParity 6 = 0 := by rw [grundyParity_eq, g4]; decide
  have g7 : grundyParity 7 = 2 := by rw [grundyParity_eq, g6, g5]; decide
  have g8 : grundyParity 8 = 1 := by rw [grundyParity_eq, g6]; decide
  have g9 : grundyParity 9 = 0 := by rw [grundyParity_eq, g8, g7]; decide
  have g10 : grundyParity 10 = 0 := by rw [grundyParity_eq, g8]; decide
  have g11 : grundyParity 11 = 1 := by rw [grundyParity_eq, g10, g9]; decide
  exact ⟨g10, g11⟩

/-- **Regime III Closed-Form Ruler-Parity Theorem (`∀ k ≥ 3`)**:
In the Borrow-Parity Game, for ALL `k ≥ 3`:
- `grundyParity (4 * k)     = if ctz k % 2 = 0 then 2 else 1`
- `grundyParity (4 * k + 1) = 0`
- `grundyParity (4 * k + 2) = 0`
- `grundyParity (4 * k + 3) = 1` -/
theorem grundyParity_closed_form (k : Nat) (hk : 3 ≤ k) :
    grundyParity (4 * k) = (if ctz k % 2 = 0 then 2 else 1) ∧
    grundyParity (4 * k + 1) = 0 ∧
    grundyParity (4 * k + 2) = 0 ∧
    grundyParity (4 * k + 3) = 1 := by
  -- Induction on m = k - 3 maintaining invariant (g(4k-2) = 0, g(4k-1) = 1)
  have hinv : ∀ m, grundyParity (4 * (m + 3) - 2) = 0 ∧ grundyParity (4 * (m + 3) - 1) = 1 := by
    intro m
    induction m with
    | zero => exact grundyParity_10_11
    | succ m ih =>
      rcases ih with ⟨hm2, hm1⟩
      let j := m + 3
      have hctz4 : ctz (4 * j) = 2 + ctz j := by
        have h := ctz_mul_two_pow j 2 (by omega)
        rw [Nat.mul_comm] at h; exact h
      have hg4 : grundyParity (4 * j) = if ctz j % 2 = 0 then 2 else 1 := by
        rw [grundyParity_eq (4 * j)]
        have h1 : 1 ≤ 4 * j := by omega
        have h2 : 2 ≤ 4 * j := by omega
        have hsub1 : 4 * j - 1 = 4 * (m + 3) - 1 := rfl
        have hsub2 : 4 * j - 2 = 4 * (m + 3) - 2 := rfl
        rw [hsub1, hsub2, hm1, hm2, hctz4]
        by_cases hp : ctz j % 2 = 0
        · simp [h1, h2, hp]; decide
        · simp [h1, h2, hp]; decide
      have hg41 : grundyParity (4 * j + 1) = 0 := by
        rw [grundyParity_eq (4 * j + 1)]
        have h1 : 1 ≤ 4 * j + 1 := by omega
        have h2 : 2 ≤ 4 * j + 1 := by omega
        have hctz1 : ctz (4 * j + 1) = 0 := ctz_odd (by omega)
        have hsub1 : 4 * j + 1 - 1 = 4 * j := by omega
        have hsub2 : 4 * j + 1 - 2 = 4 * (m + 3) - 1 := by omega
        rw [hsub1, hsub2, hg4, hm1, hctz1]
        by_cases hp : ctz j % 2 = 0 <;> simp [h1, h2, hp] <;> decide
      have hg42 : grundyParity (4 * j + 2) = 0 := by
        rw [grundyParity_eq (4 * j + 2)]
        have h1 : 1 ≤ 4 * j + 2 := by omega
        have h2 : 2 ≤ 4 * j + 2 := by omega
        have hctz2 : ctz (4 * j + 2) = 1 := by
          rw [ctz_even (by omega) (by omega)]
          have hdiv : (4 * j + 2) / 2 = 2 * j + 1 := by omega
          rw [hdiv, ctz_odd (by omega)]
        have hsub2 : 4 * j + 2 - 2 = 4 * j := by omega
        rw [hsub2, hg4, hctz2]
        by_cases hp : ctz j % 2 = 0 <;> simp [h1, h2, hp] <;> decide
      have hg43 : grundyParity (4 * j + 3) = 1 := by
        rw [grundyParity_eq (4 * j + 3)]
        have h1 : 1 ≤ 4 * j + 3 := by omega
        have h2 : 2 ≤ 4 * j + 3 := by omega
        have hctz3 : ctz (4 * j + 3) = 0 := ctz_odd (by omega)
        have hsub1 : 4 * j + 3 - 1 = 4 * j + 2 := by omega
        have hsub2 : 4 * j + 3 - 2 = 4 * j + 1 := by omega
        rw [hsub1, hsub2, hg42, hg41, hctz3]
        simp [h1, h2]; decide
      have heq1 : 4 * (m + 1 + 3) - 2 = 4 * j + 2 := by omega
      have heq2 : 4 * (m + 1 + 3) - 1 = 4 * j + 3 := by omega
      rw [heq1, heq2]
      exact ⟨hg42, hg43⟩
  obtain ⟨hm2, hm1⟩ := hinv (k - 3)
  have hk_eq : k - 3 + 3 = k := by omega
  rw [hk_eq] at hm2 hm1
  have hctz4 : ctz (4 * k) = 2 + ctz k := by
    have h := ctz_mul_two_pow k 2 (by omega)
    rw [Nat.mul_comm] at h; exact h
  have hg4 : grundyParity (4 * k) = if ctz k % 2 = 0 then 2 else 1 := by
    rw [grundyParity_eq (4 * k), hm1, hm2, hctz4]
    have h1 : 1 ≤ 4 * k := by omega
    have h2 : 2 ≤ 4 * k := by omega
    by_cases hp : ctz k % 2 = 0
    · simp [h1, h2, hp]; decide
    · simp [h1, h2, hp]; decide
  have hg41 : grundyParity (4 * k + 1) = 0 := by
    rw [grundyParity_eq (4 * k + 1)]
    have h1 : 1 ≤ 4 * k + 1 := by omega
    have h2 : 2 ≤ 4 * k + 1 := by omega
    have hctz1 : ctz (4 * k + 1) = 0 := ctz_odd (by omega)
    have hsub1 : 4 * k + 1 - 1 = 4 * k := by omega
    have hsub2 : 4 * k + 1 - 2 = 4 * k - 1 := by omega
    rw [hsub1, hsub2, hg4, hm1, hctz1]
    by_cases hp : ctz k % 2 = 0 <;> simp [h1, h2, hp] <;> decide
  have hg42 : grundyParity (4 * k + 2) = 0 := by
    rw [grundyParity_eq (4 * k + 2)]
    have h1 : 1 ≤ 4 * k + 2 := by omega
    have h2 : 2 ≤ 4 * k + 2 := by omega
    have hctz2 : ctz (4 * k + 2) = 1 := by
      rw [ctz_even (by omega) (by omega)]
      have hdiv : (4 * k + 2) / 2 = 2 * k + 1 := by omega
      rw [hdiv, ctz_odd (by omega)]
    have hsub2 : 4 * k + 2 - 2 = 4 * k := by omega
    rw [hsub2, hg4, hctz2]
    by_cases hp : ctz k % 2 = 0 <;> simp [h1, h2, hp] <;> decide
  have hg43 : grundyParity (4 * k + 3) = 1 := by
    rw [grundyParity_eq (4 * k + 3)]
    have h1 : 1 ≤ 4 * k + 3 := by omega
    have h2 : 2 ≤ 4 * k + 3 := by omega
    have hctz3 : ctz (4 * k + 3) = 0 := ctz_odd (by omega)
    have hsub1 : 4 * k + 3 - 1 = 4 * k + 2 := by omega
    have hsub2 : 4 * k + 3 - 2 = 4 * k + 1 := by omega
    rw [hsub1, hsub2, hg42, hg41, hctz3]
    simp [h1, h2]; decide
  exact ⟨hg4, hg41, hg42, hg43⟩

private theorem ctz_add_higher_pow (q b : Nat) (hq : q > 0) (hb : ctz q < b) :
    ctz (2 ^ b + q) = ctz q := by
  have h1 := (ctz_eq_iff_mod q (ctz q) hq).mp rfl
  apply (ctz_eq_iff_mod (2 ^ b + q) (ctz q) (Nat.add_pos_right _ hq)).mpr
  have hpow : 2 ^ b = 2 ^ (b - (ctz q + 1)) * 2 ^ (ctz q + 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow, Nat.add_comm, Nat.add_mul_mod_self_right, h1]

private theorem lt_two_pow_self (m : Nat) : m < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.pow_succ]; omega

/-- **Regime III — Provable Aperiodicity Sharpness Theorem**:
Replacing bounded borrow count `borrowCount n s ≤ B` by borrow-count parity
`borrowCount n 1 % 2 = 0` completely destroys ultimate periodicity:
for EVERY preperiod `n0` and EVERY candidate period `p > 0`,
there exists `n ≥ n0` such that `grundyParity (n + p) ≠ grundyParity n`! -/
theorem grundyParity_not_eventually_periodic :
    ∀ n0 p, p > 0 → ∃ n, n0 ≤ n ∧ grundyParity (n + p) ≠ grundyParity n := by
  intro n0 p hp
  by_cases h4 : p % 4 = 0
  · let q := p / 4
    have hq : q > 0 := by omega
    have hpq : p = 4 * q := by omega
    let a := ctz q
    -- Choose exponent b = a + 1 + 2 * (n0 + 2) so b > a, b ≡ a + 1 (mod 2), and 4 * 2^b ≥ n0
    let b := a + 1 + 2 * (n0 + 2)
    let k := 2 ^ b
    have hk3 : 3 ≤ k := by
      have hge : 2 ≤ b := by omega
      have hpow : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hge
      have : 2 ^ 2 = 4 := by decide
      omega
    have hn_ge : n0 ≤ 4 * k := by
      have hlt : b < 2 ^ b := lt_two_pow_self b
      omega
    refine ⟨4 * k, hn_ge, ?_⟩
    have hnp : 4 * k + p = 4 * (k + q) := by omega
    rw [hnp]
    have h1 := (grundyParity_closed_form k hk3).1
    have h2 := (grundyParity_closed_form (k + q) (by omega)).1
    rw [h1, h2, ctz_two_pow b, ctz_add_higher_pow q b hq (by omega)]
    by_cases ha : ctz q % 2 = 0
    · have hb : b % 2 ≠ 0 := by omega
      simp [ha, hb]
    · have hb : b % 2 = 0 := by omega
      simp [ha, hb]
  · -- When 4 ∤ p, pick n = 4 * 2^(2 * (n0 + 2)): g(n) = 2 while g(n + p) ∈ {0, 1}!
    let b := 2 * (n0 + 2)
    let k := 2 ^ b
    have hk3 : 3 ≤ k := by
      have hpow : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 ^ 2 = 4 := by decide
      omega
    have hn_ge : n0 ≤ 4 * k := by
      have hlt : b < 2 ^ b := lt_two_pow_self b
      omega
    refine ⟨4 * k, hn_ge, ?_⟩
    have hg_n : grundyParity (4 * k) = 2 := by
      have h1 := (grundyParity_closed_form k hk3).1
      rw [h1, ctz_two_pow b]
      have hev : b % 2 = 0 := by omega
      simp [hev]
    rw [hg_n]
    let k' := (4 * k + p) / 4
    have hk'3 : 3 ≤ k' := by omega
    have hcf := grundyParity_closed_form k' hk'3
    have hr : (4 * k + p) % 4 = p % 4 := by omega
    have hdiv : 4 * k + p = 4 * k' + p % 4 := by omega
    have hmod_cases : p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
    rcases hmod_cases with hm1 | hm2 | hm3
    · rw [hdiv, hm1, hcf.2.1]; decide
    · rw [hdiv, hm2, hcf.2.2.1]; decide
    · rw [hdiv, hm3, hcf.2.2.2]; decide

/-- **P/N-Position vs. Grundy Splitting Phenomenon in `G_parity`**:
Even though `grundyParity` is provably aperiodic, its 1-heap winning set (`g ≠ 0`) IS periodic
with period 4 for `n ≥ 12`, whereas the 2-heap Nim-sum `g(4k) ^^^ g(4) = 0 ↔ ctz k % 2 = 0` is aperiodic! -/
theorem grundyParity_oneHeap_periodic_vs_twoHeap_aperiodic :
    (∀ n, 12 ≤ n → (grundyParity n ≠ 0 ↔ n % 4 = 0 ∨ n % 4 = 3)) ∧
    (∀ k, 3 ≤ k → (grundyParity (4 * k) ^^^ grundyParity 4 = 0 ↔ ctz k % 2 = 0)) := by
  constructor
  · intro n hn
    let k := n / 4
    have hk : 3 ≤ k := by omega
    have hcf := grundyParity_closed_form k hk
    have hdiv : n = 4 * k + n % 4 := by omega
    have hm : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hm with h0 | h1 | h2 | h3
    · rw [hdiv, h0, Nat.add_zero, hcf.1]
      by_cases hp : ctz k % 2 = 0 <;> simp [hp]
    · rw [hdiv, h1, hcf.2.1]; simp
    · rw [hdiv, h2, hcf.2.2.1]; simp
    · rw [hdiv, h3, hcf.2.2.2]; simp
  · intro k hk
    have hg4 : grundyParity 4 = 2 := by
      have g0 : grundyParity 0 = 0 := by rw [grundyParity_eq]; decide
      have g1 : grundyParity 1 = 1 := by rw [grundyParity_eq, g0]; decide
      have g2 : grundyParity 2 = 1 := by rw [grundyParity_eq, g0]; decide
      have g3 : grundyParity 3 = 0 := by rw [grundyParity_eq, g2, g1]; decide
      rw [grundyParity_eq, g3, g2]; decide
    rw [(grundyParity_closed_form k hk).1, hg4]
    by_cases hp : ctz k % 2 = 0 <;> simp [hp] <;> decide

/-! ## Section 7: Kernel-Checked Negative / Mutation Tests (`checkCert bad = false`) -/

/-- Mutant 1: Corrupted entry inside the certified Grundy table. -/
def mut1_corrupt_table : PeriodWinCert :=
  { cert_G_coprime_p5 with table := cert_G_coprime_p5.table.set! 15 1 }

/-- Mutant 2: Unaligned period (`period = 5` fails `4 ∣ period` shift-invariance requirement). -/
def mut2_unaligned_period : PeriodWinCert :=
  { cert_G_coprime_p5 with
    period   := 5
    table    := cert_G_coprime_p5.table.extract 0 20
    perMoves := cert_G_coprime_p5.perMoves.extract 0 5 }

/-- Mutant 3: Fake minimal-period compression (`minPeriod = 16` on period-48 game). -/
def mut3_fake_minPeriod : PeriodWinCert :=
  { cert_G_wallbreach_48 with
    minPeriod  := 16
    perWinMask := cert_G_wallbreach_48.perWinMask &&& 65535 }

/-- Mutant 4: Single bit flip in packed periodic winning bitmask `perWinMask`. -/
def mut4_corrupt_perWinMask : PeriodWinCert :=
  { cert_G_coprime_p5 with perWinMask := cert_G_coprime_p5.perWinMask ^^^ 1 }

/-- Mutant 5: Single bit flip in packed preperiod winning bitmask `preWinMask`. -/
def mut5_corrupt_preWinMask : PeriodWinCert :=
  { cert_G_coprime_p5 with preWinMask := cert_G_coprime_p5.preWinMask ^^^ 4 }

/-- Mutant 6: Corrupted winning move in `perMoves` (lands on a non-zero Grundy heap). -/
def mut6_bad_winMove : PeriodWinCert :=
  { cert_G_coprime_p5 with perMoves := cert_G_coprime_p5.perMoves.set! 0 3 }

/-- Mutant 7: Truncated preperiod `n0 = 14` on `G_coprime_p5` (fails across peak `g(14) = 3`). -/
def mut7_truncated_preperiod : PeriodWinCert :=
  { cert_G_coprime_p5 with
    preperiod  := 14
    table      := cert_G_coprime_p5.table.extract 0 34
    preWinMask := cert_G_coprime_p5.preWinMask &&& 16383
    preMoves   := cert_G_coprime_p5.preMoves.extract 0 21 }

/-- Mutant 8: Zero-step rule smuggling (`step = 0` breaks well-foundedness/termination). -/
def mut8_zero_step_game : BitGame := ⟨0, .always⟩ :: G_coprime_p5

theorem mut1_rejected : checkCert G_coprime_p5 mut1_corrupt_table = false := by decide
theorem mut2_rejected : checkCert G_coprime_p5 mut2_unaligned_period = false := by decide
theorem mut3_rejected : checkCert G_wallbreach_48 mut3_fake_minPeriod = false := by decide
theorem mut4_rejected : checkCert G_coprime_p5 mut4_corrupt_perWinMask = false := by decide
theorem mut5_rejected : checkCert G_coprime_p5 mut5_corrupt_preWinMask = false := by decide
theorem mut6_rejected : checkCert G_coprime_p5 mut6_bad_winMove = false := by decide
theorem mut7_rejected : checkCert G_coprime_p5 mut7_truncated_preperiod = false := by decide
theorem mut8_rejected : checkCert mut8_zero_step_game cert_G_coprime_p5 = false := by decide


end BitwiseGrundyCompiler
