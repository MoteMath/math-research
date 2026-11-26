/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ClmulLiftDeterminants.Defs
import Mathlib.Data.BitVec
import Mathlib.Tactic

/-!
# Binary Carry-Less Multiplication & `{0, 1}`-Lift Polynomial Identities

Establishes the core arithmetic properties of `clmul`, `bitPolyEval`, `bitrevNat`, and `ctz`
(trailing-zero count) used in the exact Schur reduction of `oddClmulMatrix`.
-/

namespace ClmulLiftDeterminants

open scoped BigOperators
open Finset

/-! ## Section 1: Bitwise Helpers, `bitrevNat`, and `ctz` -/

theorem testBit_eq_false_of_lt_two_pow {n r : ℕ} (h : n < 2 ^ r) : n.testBit r = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt h]
  simp

theorem testBit_two_mul_succ (x r : ℕ) : (2 * x).testBit (r + 1) = x.testBit r := by
  rw [Nat.testBit_succ]
  have : (2 * x) / 2 = x := by omega
  rw [this]

theorem mod_two_xor (a b : ℕ) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one (a ^^^ b) with hab | hab <;>
  rw [ha, hb, hab] at h ⊢ <;>
  simp_all

theorem mod_two_and (a b : ℕ) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  have h := Nat.testBit_and a b 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one (a &&& b) with hab | hab <;>
  rw [ha, hb, hab] at h ⊢ <;>
  simp_all

/-- `k`-bit reversal of a natural number `x`. -/
def bitrevNat : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => (x % 2) * 2 ^ k + bitrevNat k (x / 2)

theorem bitrevNat_lt : ∀ k x, bitrevNat k x < 2 ^ k
  | 0, _ => by simp [bitrevNat]
  | k + 1, x => by
    simp only [bitrevNat]
    have hlt := bitrevNat_lt k (x / 2)
    have hmod : x % 2 < 2 := Nat.mod_lt x (by omega)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega

theorem bitrevNat_zero : ∀ k, bitrevNat k 0 = 0
  | 0 => rfl
  | k + 1 => by simp [bitrevNat, bitrevNat_zero k]

theorem bitrevNat_one (k : ℕ) (hk : 1 ≤ k) : bitrevNat k 1 = 2 ^ (k - 1) := by
  cases k with
  | zero => omega
  | succ k' => simp [bitrevNat, bitrevNat_zero]

theorem bitrevNat_allOnes : ∀ k, bitrevNat k (2 ^ k - 1) = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
    have hpos : 0 < 2 ^ k := by positivity
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    have hmod : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hdiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
    simp only [bitrevNat, hmod, hdiv, bitrevNat_allOnes k]
    omega

theorem testBit_bitrevNat : ∀ k x u, u < k →
    (bitrevNat k x).testBit u = x.testBit (k - 1 - u)
  | 0, _, _, hu => absurd hu (Nat.not_lt_zero _)
  | k + 1, x, u, hu => by
    simp only [bitrevNat]
    have hlt := bitrevNat_lt k (x / 2)
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu) with hlt_u | rfl
    · -- u < k: (x%2)*2^k has bit u = 0
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ k = 2 ^ u * (2 * 2 ^ (k - 1 - u)) := by
        have : k = u + 1 + (k - 1 - u) := by omega
        conv_lhs => rw [this, pow_add, pow_add, pow_one]
        ring
      have hpos : 0 < 2 ^ u := by positivity
      have hdiv : ((x % 2) * 2 ^ k + bitrevNat k (x / 2)) / 2 ^ u =
          2 * ((x % 2) * 2 ^ (k - 1 - u)) + bitrevNat k (x / 2) / 2 ^ u := by
        have h1 : (x % 2) * 2 ^ k + bitrevNat k (x / 2) =
            2 ^ u * (2 * ((x % 2) * 2 ^ (k - 1 - u))) + bitrevNat k (x / 2) := by
          rw [hpow]; ring
        rw [h1, Nat.mul_add_div hpos]
      rw [hdiv, Nat.mul_add_mod, ← Nat.testBit_eq_decide_div_mod_eq,
          testBit_bitrevNat k (x / 2) u hlt_u]
      have hsub : k + 1 - 1 - u = (k - 1 - u) + 1 := by omega
      rw [hsub, Nat.testBit_succ]
    · -- u = k: top bit is x % 2 = x.testBit 0
      have hsub : u + 1 - 1 - u = 0 := by omega
      rw [hsub, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpos : 0 < 2 ^ u := by positivity
      have hdiv : ((x % 2) * 2 ^ u + bitrevNat u (x / 2)) / 2 ^ u = x % 2 := by
        rw [mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, add_zero]
      rw [hdiv, pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (dvd_refl 2)]

theorem bitrevNat_bitrevNat (k x : ℕ) (hx : x < 2 ^ k) : bitrevNat k (bitrevNat k x) = x := by
  apply Nat.eq_of_testBit_eq
  intro u
  by_cases hu : u < k
  · rw [testBit_bitrevNat k _ u hu, testBit_bitrevNat k x (k - 1 - u) (by omega)]
    congr 1; omega
  · have hge : k ≤ u := Nat.not_lt.mp hu
    rw [testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le (bitrevNat_lt k _) (Nat.pow_le_pow_right (by omega) hge)),
        testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge))]

/-- Trailing-zero count (2-adic valuation) of a positive natural number, `0` at `0`. -/
def ctz (n : ℕ) : ℕ :=
  if n = 0 then 0 else if n % 2 = 1 then 0 else 1 + ctz (n / 2)

theorem ctz_spec : ∀ n, n ≠ 0 →
    (n / 2 ^ ctz n) % 2 = 1 ∧ 2 ^ ctz n * (n / 2 ^ ctz n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hodd : n % 2 = 1
    · have hctz : ctz n = 0 := by unfold ctz; simp [hn, hodd]
      simp [hctz, hodd]
    · have heven : n % 2 = 0 := by omega
      have hctz : ctz n = 1 + ctz (n / 2) := by conv_lhs => unfold ctz; simp [hn, hodd]
      have hdiv_ne : n / 2 ≠ 0 := by omega
      have ⟨h1, h2⟩ := ih (n / 2) (by omega) hdiv_ne
      rw [hctz, add_comm 1, pow_succ', ← Nat.div_div_eq_div_mul]
      refine ⟨h1, ?_⟩
      rw [mul_assoc, h2]
      omega

theorem ctz_lt_of_lt_two_pow {n k : ℕ} (hn : n ≠ 0) (hlt : n < 2 ^ k) : ctz n < k := by
  by_contra hge
  have hk : k ≤ ctz n := Nat.not_lt.mp hge
  have ⟨hodd, hmul⟩ := ctz_spec n hn
  have hq : 0 < n / 2 ^ ctz n :=
    Nat.pos_of_ne_zero fun h => by rw [h] at hodd; norm_num at hodd
  have h1 : 2 ^ k ≤ 2 ^ ctz n := Nat.pow_le_pow_right (by omega) hk
  have h2 : 2 ^ ctz n ≤ 2 ^ ctz n * (n / 2 ^ ctz n) := Nat.le_mul_of_pos_right _ hq
  rw [hmul] at h2
  omega

/-! ## Section 2: `clmul` Algebra & Bit Formula -/

theorem clmul_zero_right (a : ℕ) : clmul a 0 = 0 := by
  unfold clmul; simp

theorem clmul_eq_of_ne_zero (a : ℕ) {b : ℕ} (hb : b ≠ 0) :
    clmul a b = (if b % 2 = 1 then a else 0) ^^^ (2 * clmul a (b / 2)) := by
  conv_lhs => unfold clmul
  simp [hb]

theorem clmul_one_right (a : ℕ) : clmul a 1 = a := by
  rw [clmul_eq_of_ne_zero a (by omega)]
  simp [clmul_zero_right]

theorem clmul_two_mul_right (a b : ℕ) : clmul a (2 * b) = 2 * clmul a b := by
  by_cases hb : b = 0
  · subst hb; simp [clmul_zero_right]
  · rw [clmul_eq_of_ne_zero a (by omega)]
    have hmod : (2 * b) % 2 = 0 := by omega
    have hdiv : (2 * b) / 2 = b := by omega
    simp [hmod, hdiv]

theorem clmul_pow_two_mul_right (r a b : ℕ) : clmul a (2 ^ r * b) = 2 ^ r * clmul a b := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc, clmul_two_mul_right, ih, mul_assoc]

theorem two_mul_xor (x y : ℕ) : 2 * (x ^^^ y) = (2 * x) ^^^ (2 * y) := by
  apply Nat.eq_of_testBit_eq
  intro r
  cases r with
  | zero => simp [Nat.testBit_zero]
  | succ r =>
    rw [Nat.testBit_xor, testBit_two_mul_succ, testBit_two_mul_succ, testBit_two_mul_succ,
        Nat.testBit_xor]

theorem clmul_xor_right (a : ℕ) : ∀ b c, clmul a (b ^^^ c) = clmul a b ^^^ clmul a c := by
  intro b c
  induction hsum : b + c using Nat.strong_induction_on generalizing b c with
  | h s ih =>
    by_cases hb : b = 0
    · subst hb; simp [clmul_zero_right]
    · by_cases hc : c = 0
      · subst hc; simp [clmul_zero_right]
      · have hdiv_xor : (b ^^^ c) / 2 = (b / 2) ^^^ (c / 2) := by
          apply Nat.eq_of_testBit_eq; intro r
          rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor,
              Nat.testBit_div_two, Nat.testBit_div_two]
        have hlt : b / 2 + c / 2 < s := by omega
        have hih := ih (b / 2 + c / 2) hlt (b / 2) (c / 2) rfl
        rw [clmul_eq_of_ne_zero a hb, clmul_eq_of_ne_zero a hc]
        have hbc_mod : (b ^^^ c) % 2 = (b % 2) ^^^ (c % 2) := mod_two_xor b c
        by_cases hbc : b ^^^ c = 0
        · have heq : b = c := Nat.eq_of_testBit_eq fun r => by
            have h := congrArg (fun n => n.testBit r) hbc
            rw [Nat.testBit_xor, Nat.zero_testBit] at h
            cases hb' : b.testBit r <;> cases hc' : c.testBit r <;> simp [hb', hc'] at h ⊢
          subst heq
          simp [clmul_zero_right]
        · rw [clmul_eq_of_ne_zero a hbc, hdiv_xor, hih, two_mul_xor]
          rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1 <;>
          rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
          · have : (b ^^^ c) % 2 = 0 := by rw [hbc_mod, hb0, hc0]; decide
            simp [hb0, hc0, this]
          · have : (b ^^^ c) % 2 = 1 := by rw [hbc_mod, hb0, hc1]; decide
            simp only [hb0, hc1, this, ↓reduceIte, zero_ne_one, Nat.zero_xor]
            apply Nat.eq_of_testBit_eq; intro r
            simp only [Nat.testBit_xor]; cases a.testBit r <;> cases (2 * clmul a (b / 2)).testBit r <;> cases (2 * clmul a (c / 2)).testBit r <;> rfl
          · have : (b ^^^ c) % 2 = 1 := by rw [hbc_mod, hb1, hc0]; decide
            simp only [hb1, hc0, this, ↓reduceIte, zero_ne_one, Nat.zero_xor]
            apply Nat.eq_of_testBit_eq; intro r
            simp only [Nat.testBit_xor]; cases a.testBit r <;> cases (2 * clmul a (b / 2)).testBit r <;> cases (2 * clmul a (c / 2)).testBit r <;> rfl
          · have : (b ^^^ c) % 2 = 0 := by rw [hbc_mod, hb1, hc1]; decide
            simp only [hb1, hc1, this, ↓reduceIte, zero_ne_one, Nat.zero_xor]
            apply Nat.eq_of_testBit_eq; intro r
            simp only [Nat.testBit_xor]; cases a.testBit r <;> cases (2 * clmul a (b / 2)).testBit r <;> cases (2 * clmul a (c / 2)).testBit r <;> rfl

theorem clmul_xor_left (a b : ℕ) : ∀ c, clmul (a ^^^ b) c = clmul a c ^^^ clmul b c := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hc : c = 0
    · subst hc; simp [clmul_zero_right]
    · rw [clmul_eq_of_ne_zero _ hc, clmul_eq_of_ne_zero a hc, clmul_eq_of_ne_zero b hc,
          ih (c / 2) (by omega), two_mul_xor]
      by_cases hodd : c % 2 = 1
      · simp only [hodd, ↓reduceIte]
        apply Nat.eq_of_testBit_eq; intro r
        simp only [Nat.testBit_xor]
        cases a.testBit r <;> cases b.testBit r <;>
        cases (2 * clmul a (c / 2)).testBit r <;> cases (2 * clmul b (c / 2)).testBit r <;> rfl
      · simp [hodd]

theorem clmul_two_mul_left (a : ℕ) : ∀ b, clmul (2 * a) b = 2 * clmul a b := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b = 0
    · subst hb; simp [clmul_zero_right]
    · rw [clmul_eq_of_ne_zero _ hb, clmul_eq_of_ne_zero a hb, ih (b / 2) (by omega), two_mul_xor]
      by_cases hodd : b % 2 = 1 <;> simp [hodd]

theorem clmul_zero_left : ∀ b, clmul 0 b = 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b = 0
    · subst hb; exact clmul_zero_right 0
    · rw [clmul_eq_of_ne_zero 0 hb, ih (b / 2) (by omega)]; simp

theorem clmul_one_left : ∀ b, clmul 1 b = b := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b = 0
    · subst hb; exact clmul_zero_right 1
    · rw [clmul_eq_of_ne_zero 1 hb, ih (b / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one b with h0 | h1
      · simp only [h0, zero_ne_one, ↓reduceIte, Nat.zero_xor]; omega
      · simp only [h1, ↓reduceIte]
        apply Nat.eq_of_testBit_eq; intro r
        cases r with
        | zero => simp [Nat.testBit_zero, h1]
        | succ r =>
          rw [Nat.testBit_xor, testBit_two_mul_succ]
          have h1lt : 1 < 2 ^ (r + 1) := by
            have : 0 < 2 ^ r := by positivity
            rw [pow_succ]; omega
          have h1r : (1 : ℕ).testBit (r + 1) = false := testBit_eq_false_of_lt_two_pow h1lt
          rw [h1r, Bool.false_xor, Nat.testBit_succ]

theorem clmul_comm : ∀ a b, clmul a b = clmul b a := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hb : b = 0
    · subst hb; rw [clmul_zero_right, clmul_zero_left]
    · rw [clmul_eq_of_ne_zero a hb, ih (b / 2) (by omega) a]
      have hb_eq : b = (if b % 2 = 1 then 1 else 0) ^^^ (2 * (b / 2)) := by
        apply Nat.eq_of_testBit_eq; intro r
        cases r with
        | zero =>
          rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [Nat.testBit_zero, h]
        | succ r =>
          rw [Nat.testBit_xor, testBit_two_mul_succ, Nat.testBit_succ]
          have h1r : (if b % 2 = 1 then (1 : ℕ) else 0).testBit (r + 1) = false := by
            split_ifs
            · apply testBit_eq_false_of_lt_two_pow
              have : 0 < 2 ^ r := by positivity
              rw [pow_succ]; omega
            · simp
          simp [h1r]
      conv_rhs => rw [hb_eq, clmul_xor_left, clmul_two_mul_left]
      by_cases hodd : b % 2 = 1 <;> simp [hodd, clmul_one_left, clmul_zero_left]

theorem clmul_pow_two_mul_left (r a b : ℕ) : clmul (2 ^ r * a) b = 2 ^ r * clmul a b := by
  rw [clmul_comm, clmul_pow_two_mul_right, clmul_comm]

theorem clmul_pow_two_right (r a : ℕ) : clmul a (2 ^ r) = 2 ^ r * a := by
  have := clmul_pow_two_mul_right r a 1
  simpa [clmul_one_right] using this

/-- Exact convolution bit formula for `clmul`: bit `m` of `clmul a b` is the parity of the number
of `d ≤ m` with `a.testBit d = true ∧ b.testBit (m - d) = true`. -/
theorem testBit_clmul : ∀ m a b,
    (clmul a b).testBit m =
      decide (((Finset.range (m + 1)).filter (fun d => a.testBit d && b.testBit (m - d))).card % 2 = 1)
  | 0, a, b => by
    by_cases hb : b = 0
    · subst hb; simp [clmul_zero_right]
    · rw [clmul_eq_of_ne_zero a hb, Nat.testBit_xor, Nat.testBit_zero]
      have h20 : (2 * clmul a (b / 2)) % 2 = 0 := by omega
      simp only [Nat.testBit_zero, h20, zero_ne_one, decide_false, Bool.xor_false]
      rw [Finset.range_one]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb' | hb' <;>
      simp [Finset.filter_singleton, ha, hb', Nat.testBit_zero]
  | m + 1, a, b => by
    by_cases hb : b = 0
    · subst hb; simp [clmul_zero_right]
    · rw [clmul_eq_of_ne_zero a hb, Nat.testBit_xor, testBit_two_mul_succ,
          testBit_clmul m a (b / 2)]
      -- Split range (m + 2) into {m + 1} (d = m + 1, b.testBit 0) and range (m + 1) (d ≤ m, (b/2).testBit (m - d))
      have hfilt :
          ((Finset.range (m + 2)).filter (fun d => a.testBit d && b.testBit (m + 1 - d))).card =
          (if a.testBit (m + 1) && b.testBit 0 then 1 else 0) +
          ((Finset.range (m + 1)).filter (fun d => a.testBit d && (b / 2).testBit (m - d))).card := by
        rw [Finset.range_add_one, Finset.filter_insert]
        have hnotmem : m + 1 ∉ (Finset.range (m + 1)).filter (fun d => a.testBit d && b.testBit (m + 1 - d)) := by
          simp
        have hrest :
            (Finset.range (m + 1)).filter (fun d => a.testBit d && b.testBit (m + 1 - d)) =
            (Finset.range (m + 1)).filter (fun d => a.testBit d && (b / 2).testBit (m - d)) := by
          refine Finset.filter_congr fun d hd => ?_
          have hdm : d ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
          have hsub : m + 1 - d = (m - d) + 1 := by omega
          rw [hsub, Nat.testBit_succ]
        rw [Nat.sub_self]
        split_ifs with htop
        · rw [Finset.card_insert_of_notMem hnotmem, hrest]; omega
        · rw [hrest]; omega
      rw [hfilt]
      have hb0 : b.testBit 0 = decide (b % 2 = 1) := by simp [Nat.testBit_zero]
      rw [hb0]
      rcases Nat.mod_two_eq_zero_or_one b with h0 | h1
      · simp [h0]
      · simp only [h1, ↓reduceIte, decide_true, Bool.and_true]
        set cnt := ((Finset.range (m + 1)).filter (fun d => a.testBit d && (b / 2).testBit (m - d))).card
        cases ha : a.testBit (m + 1) <;>
        rcases Nat.mod_two_eq_zero_or_one cnt with hc | hc <;>
        simp [hc, Nat.add_mod]

/-! ## Section 3: `bitPolyEval` Algebra over Arbitrary Commutative Rings -/

theorem bitPolyEval_zero {R : Type*} [CommRing R] (t : R) : bitPolyEval t 0 = 0 := by
  unfold bitPolyEval; simp

theorem bitPolyEval_eq_of_ne_zero {R : Type*} [CommRing R] (t : R) {n : ℕ} (hn : n ≠ 0) :
    bitPolyEval t n = (if n % 2 = 1 then 1 else 0) + t * bitPolyEval t (n / 2) := by
  conv_lhs => unfold bitPolyEval
  simp [hn]

theorem bitPolyEval_one {R : Type*} [CommRing R] (t : R) : bitPolyEval t 1 = 1 := by
  rw [bitPolyEval_eq_of_ne_zero t (by omega)]
  simp [bitPolyEval_zero]

theorem bitPolyEval_two_mul {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    bitPolyEval t (2 * n) = t * bitPolyEval t n := by
  by_cases hn : n = 0
  · subst hn; simp [bitPolyEval_zero]
  · rw [bitPolyEval_eq_of_ne_zero t (by omega)]
    have hmod : (2 * n) % 2 = 0 := by omega
    have hdiv : (2 * n) / 2 = n := by omega
    simp [hmod, hdiv]

theorem bitPolyEval_pow_two_mul {R : Type*} [CommRing R] (t : R) (r n : ℕ) :
    bitPolyEval t (2 ^ r * n) = t ^ r * bitPolyEval t n := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc, bitPolyEval_two_mul, ih, pow_succ', mul_assoc]

theorem bitPolyEval_pow_two {R : Type*} [CommRing R] (t : R) (r : ℕ) :
    bitPolyEval t (2 ^ r) = t ^ r := by
  have := bitPolyEval_pow_two_mul t r 1
  simpa [bitPolyEval_one] using this

/-- Fundamental binary carry-free lift law over ANY commutative ring `R`:
`bitPolyEval t (a ^^^ b) = bitPolyEval t a + bitPolyEval t b - 2 * bitPolyEval t (a &&& b)`. -/
theorem bitPolyEval_xor {R : Type*} [CommRing R] (t : R) :
    ∀ a b : ℕ, bitPolyEval t (a ^^^ b) =
      bitPolyEval t a + bitPolyEval t b - 2 * bitPolyEval t (a &&& b) := by
  intro a b
  induction hsum : a + b using Nat.strong_induction_on generalizing a b with
  | h s ih =>
    by_cases ha : a = 0
    · subst ha; simp [bitPolyEval_zero]
    · by_cases hb : b = 0
      · subst hb; simp [bitPolyEval_zero]
      · have hdiv_xor : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
          apply Nat.eq_of_testBit_eq; intro r
          rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor,
              Nat.testBit_div_two, Nat.testBit_div_two]
        have hdiv_and : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
          apply Nat.eq_of_testBit_eq; intro r
          rw [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_and,
              Nat.testBit_div_two, Nat.testBit_div_two]
        have hih := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
        have heval_step : ∀ x : ℕ,
            bitPolyEval t x = (if x % 2 = 1 then 1 else 0) + t * bitPolyEval t (x / 2) := by
          intro x
          by_cases hx : x = 0
          · subst hx; simp [bitPolyEval_zero]
          · exact bitPolyEval_eq_of_ne_zero t hx
        rw [heval_step (a ^^^ b), heval_step a, heval_step b, heval_step (a &&& b),
            hdiv_xor, hdiv_and, hih]
        have hmod_xor : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := mod_two_xor a b
        have hmod_and : (a &&& b) % 2 = (a % 2) &&& (b % 2) := mod_two_and a b
        rcases Nat.mod_two_eq_zero_or_one a with h0 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one b with g0 | g1
        · have hx : (a ^^^ b) % 2 = 0 := by rw [hmod_xor, h0, g0]; decide
          have hn : (a &&& b) % 2 = 0 := by rw [hmod_and, h0, g0]; decide
          simp only [h0, g0, hx, hn, zero_ne_one, ↓reduceIte]; ring
        · have hx : (a ^^^ b) % 2 = 1 := by rw [hmod_xor, h0, g1]; decide
          have hn : (a &&& b) % 2 = 0 := by rw [hmod_and, h0, g1]; decide
          simp only [h0, g1, hx, hn, zero_ne_one, ↓reduceIte]; ring
        · have hx : (a ^^^ b) % 2 = 1 := by rw [hmod_xor, h1, g0]; decide
          have hn : (a &&& b) % 2 = 0 := by rw [hmod_and, h1, g0]; decide
          simp only [h1, g0, hx, hn, zero_ne_one, ↓reduceIte]; ring
        · have hx : (a ^^^ b) % 2 = 0 := by rw [hmod_xor, h1, g1]; decide
          have hn : (a &&& b) % 2 = 1 := by rw [hmod_and, h1, g1]; decide
          simp only [h1, g1, hx, hn, zero_ne_one, ↓reduceIte]; ring

theorem and_eq_zero_of_lt_two_pow_mul {a b k : ℕ} (ha : a < 2 ^ k) :
    a &&& (2 ^ k * b) = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hr : r < k
  · have h2 : (2 ^ k * b).testBit r = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ k = 2 ^ r * (2 * 2 ^ (k - 1 - r)) := by
        have : k = r + 1 + (k - 1 - r) := by omega
        conv_lhs => rw [this, pow_add, pow_add, pow_one]
        ac_rfl
      have hpos : 0 < 2 ^ r := by positivity
      have hdiv : (2 ^ k * b) / 2 ^ r = 2 * (2 ^ (k - 1 - r) * b) := by
        have : 2 ^ k * b = 2 ^ r * (2 * (2 ^ (k - 1 - r) * b)) := by rw [hpow]; ring
        rw [this, Nat.mul_div_right _ hpos]
      rw [hdiv]; simp
    simp [h2]
  · have hge : k ≤ r := Nat.not_lt.mp hr
    have h1 : a.testBit r = false :=
      testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hge))
    simp [h1]

theorem testBit_pow_two_mul (k b r : ℕ) :
    (2 ^ k * b).testBit r = if r < k then false else b.testBit (r - k) := by
  by_cases hr : r < k
  · simp only [hr, ↓reduceIte]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ k = 2 ^ r * (2 * 2 ^ (k - 1 - r)) := by
      have : k = r + 1 + (k - 1 - r) := by omega
      conv_lhs => rw [this, pow_add, pow_add, pow_one]
      ac_rfl
    have hpos : 0 < 2 ^ r := by positivity
    have hdiv : (2 ^ k * b) / 2 ^ r = 2 * (2 ^ (k - 1 - r) * b) := by
      have : 2 ^ k * b = 2 ^ r * (2 * (2 ^ (k - 1 - r) * b)) := by rw [hpow]; ring
      rw [this, Nat.mul_div_right _ hpos]
    rw [hdiv]; simp
  · simp only [hr, ↓reduceIte]
    have hge : k ≤ r := Nat.not_lt.mp hr
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ r = 2 ^ k * 2 ^ (r - k) := by
      have : r = k + (r - k) := by omega
      conv_lhs => rw [this, pow_add]
    have hpos : 0 < 2 ^ k := by positivity
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_div_right _ hpos]

theorem xor_eq_add_of_and_eq_zero {a b : ℕ} (hand : a &&& b = 0) : a ^^^ b = a + b := by
  suffices h : ∀ s a b : ℕ, a + b = s → a &&& b = 0 → a ^^^ b = a + b from h (a + b) a b rfl hand
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro a b hsum hand
    by_cases ha : a = 0
    · subst ha; simp
    · by_cases hb : b = 0
      · subst hb; simp
      · have hdiv_xor : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
          apply Nat.eq_of_testBit_eq; intro r
          rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor,
              Nat.testBit_div_two, Nat.testBit_div_two]
        have hdiv_and : (a / 2) &&& (b / 2) = 0 := by
          have h0 := congrArg (· / 2) hand
          have h1 : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
            apply Nat.eq_of_testBit_eq; intro r
            rw [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_and,
                Nat.testBit_div_two, Nat.testBit_div_two]
          rw [h1] at h0; simpa using h0
        have hih := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl hdiv_and
        have hmod_and : (a % 2) &&& (b % 2) = 0 := by
          rw [← mod_two_and, hand]
        have hmod_xor : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := mod_two_xor a b
        rcases Nat.mod_two_eq_zero_or_one a with ha' | ha' <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb' | hb'
        · have hx : (a ^^^ b) % 2 = 0 := by rw [hmod_xor, ha', hb']; decide
          omega
        · have hx : (a ^^^ b) % 2 = 1 := by rw [hmod_xor, ha', hb']; decide
          omega
        · have hx : (a ^^^ b) % 2 = 1 := by rw [hmod_xor, ha', hb']; decide
          omega
        · rw [ha', hb'] at hmod_and; norm_num at hmod_and

end ClmulLiftDeterminants
