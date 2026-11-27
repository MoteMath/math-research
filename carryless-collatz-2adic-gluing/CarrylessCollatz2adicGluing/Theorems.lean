/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarrylessCollatz2adicGluing.Defs

/-!
# Theorems (`CarrylessCollatz2adicGluing`)

dynsil-9: 2-Adic Piecewise-Affine & Carryless-Collatz Conjugacy Engine
  Standalone Lean 4.34.1 (zero Mathlib, zero sorry, zero custom axioms).

  Contents:
    Section 1. Pure-Silicon Bitwise & Carryless (`clmul`) Arithmetic Primitives
               (pure structural recursion for instant kernel reduction & `decide`)
    Section 2. Reusable Infinite Proof Engine: `ShiftFaithful`, Parity-Vector Conjugacy `Q`,
               Constructive O(k) Hensel Inverse `R`, 2-Adic Isometry, Exact m-Step Haar
               Measure Preservation, Bijective 2-Adic Lift, Universal Transfer Conjugacy `Phi`,
               Exact Syracuse `v_2` Preservation & Conjugacy, and Universal 2-Adic Periodic-Orbit
               Classification (exact bijection with `{0, ..., 2^p - 1}` for all `p >= 1`).
    Section 3. Finite-Table Ultrametric Gluing Certifier (IFF) for Arbitrary 2^r-Branch
               Carried and Carryless Piecewise-Affine Maps, plus Parametric Families &
               Decidable Concrete Certifications (`r = 2`, `r = 3`).
    Section 4. Novel Infinite Theorem I: Universal Carry-vs-Carryless Self-Coding Phase
               Transition & Finite-Certificate Fixed-Point Collapse Mechanism.
    Section 5. Novel Infinite Theorem II: Carryless-Collatz Trajectory Degree Identity,
               Cycle Degree-Balance Obstruction (`L = bitDeg p * popcount(Q L x)`), and
               2-Adic Uniqueness Proof of Carryless 3x+1's Unique Non-Zero Cycle `{1}`.
    Section 6. Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples.
    Section 7. Axiom Audits (`#print axioms` on all main theorems).
-/


namespace Dynsil9

-- ============================================================================
-- SECTION 1: Pure-Silicon Bitwise & Carryless (`clmul`) Arithmetic Primitives
-- ============================================================================

/-- Structurally recursive fuel helper for `bitDeg`. -/
def bitDegAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≤ 1 then 0 else bitDegAux fuel (n / 2) + 1

theorem bitDegAux_eq : ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → bitDegAux f1 n = bitDegAux f2 n := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 n h1 _
    have hn : n = 0 := by omega
    subst hn; cases f2 <;> simp [bitDegAux]
  | succ f1 ih =>
    intro f2 n h1 h2
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [bitDegAux]
    | succ f2 =>
      simp only [bitDegAux]
      by_cases hle : n ≤ 1
      · simp [hle]
      · simp only [hle, ↓reduceIte]
        congr 1
        exact ih f2 (n / 2) (by omega) (by omega)

/-- Exact bit-degree `floor(log2 n)` for `n >= 1`, and `0` for `n = 0`. -/
def bitDeg (n : Nat) : Nat := bitDegAux n n

theorem bitDeg_eq (n : Nat) : bitDeg n = if n ≤ 1 then 0 else bitDeg (n / 2) + 1 := by
  cases n with
  | zero => rfl
  | succ m =>
    simp only [bitDeg, bitDegAux]
    by_cases hle : m + 1 ≤ 1
    · simp [hle]
    · simp only [hle, ↓reduceIte]
      congr 1
      exact bitDegAux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)

/-- Structurally recursive fuel helper for `popcount`. -/
def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n % 2 + popcountAux fuel (n / 2)

theorem popcountAux_eq : ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → popcountAux f1 n = popcountAux f2 n := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 n h1 _
    have hn : n = 0 := by omega
    subst hn; cases f2 <;> simp [popcountAux]
  | succ f1 ih =>
    intro f2 n h1 h2
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [popcountAux]
    | succ f2 =>
      simp only [popcountAux]
      by_cases h0 : n = 0
      · simp [h0]
      · simp only [h0, ↓reduceIte]
        congr 1
        exact ih f2 (n / 2) (by omega) (by omega)

/-- Exact Hamming weight (number of 1-bits) of `n`. -/
def popcount (n : Nat) : Nat := popcountAux n n

theorem popcount_eq (n : Nat) : popcount n = if n = 0 then 0 else n % 2 + popcount (n / 2) := by
  cases n with
  | zero => rfl
  | succ m =>
    simp only [popcount, popcountAux, Nat.succ_ne_zero, ↓reduceIte]
    congr 1
    exact popcountAux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)

theorem v2Aux_eq : ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → v2Aux f1 n = v2Aux f2 n := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 n h1 _
    have hn : n = 0 := by omega
    subst hn; cases f2 <;> simp [v2Aux]
  | succ f1 ih =>
    intro f2 n h1 h2
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [v2Aux]
    | succ f2 =>
      simp only [v2Aux]
      by_cases h0 : n = 0
      · simp [h0]
      · by_cases h1m : n % 2 = 1
        · simp [h0, h1m]
        · simp only [h0, h1m, ↓reduceIte]
          congr 1
          exact ih f2 (n / 2) (by omega) (by omega)

theorem v2_eq (n : Nat) :
    v2 n = if n = 0 then 0 else if n % 2 = 1 then 0 else v2 (n / 2) + 1 := by
  cases n with
  | zero => rfl
  | succ m =>
    simp only [v2, v2Aux, Nat.succ_ne_zero, ↓reduceIte]
    by_cases h1m : (m + 1) % 2 = 1
    · simp [h1m]
    · simp only [h1m, ↓reduceIte]
      congr 1
      exact v2Aux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)

theorem clmulAux_eq : ∀ f1 f2 a b, a ≤ f1 → a ≤ f2 → clmulAux f1 a b = clmulAux f2 a b := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 a b h1 _
    have ha : a = 0 := by omega
    subst ha; cases f2 <;> simp [clmulAux]
  | succ f1 ih =>
    intro f2 a b h1 h2
    cases f2 with
    | zero =>
      have ha : a = 0 := by omega
      subst ha; simp [clmulAux]
    | succ f2 =>
      simp only [clmulAux]
      by_cases ha : a = 0
      · simp [ha]
      · simp only [ha, ↓reduceIte]
        congr 2
        exact ih f2 (a / 2) b (by omega) (by omega)

theorem clmul_eq (a b : Nat) :
    clmul a b = if a = 0 then 0 else (if a % 2 = 1 then b else 0) ^^^ (clmul (a / 2) b <<< 1) := by
  cases a with
  | zero => rfl
  | succ m =>
    simp only [clmul, clmulAux, Nat.succ_ne_zero, ↓reduceIte]
    congr 2
    exact clmulAux_eq m ((m + 1) / 2) ((m + 1) / 2) b (by omega) (Nat.le_refl _)

theorem iter_succ_right (T : Nat → Nat) (j x : Nat) :
    iter T (j + 1) x = T (iter T j x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => exact ih (T x)

theorem iter_add (T : Nat → Nat) (a b x : Nat) :
    iter T (a + b) x = iter T b (iter T a x) := by
  induction a generalizing x with
  | zero => simp [iter]
  | succ a ih =>
    rw [Nat.succ_add]
    exact ih (T x)

-- Basic bitwise / mod-2^k bridge lemmas

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k

theorem pow2_split (k : Nat) (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  cases k with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel, Nat.pow_succ]
    omega

theorem testBit_div_two (u j : Nat) : (u / 2).testBit j = u.testBit (j + 1) := by
  have := Nat.testBit_div_two_pow (x := u) (i := j) (n := 1)
  simpa [Nat.add_comm] using this

theorem mod_two_pow_eq_iff (a b k : Nat) :
    a % 2 ^ k = b % 2 ^ k ↔ ∀ i, i < k → a.testBit i = b.testBit i := by
  constructor
  · intro h i hi
    have h1 := Nat.testBit_mod_two_pow a k i
    have h2 := Nat.testBit_mod_two_pow b k i
    simp only [hi, decide_true, Bool.true_and] at h1 h2
    rw [← h1, ← h2, h]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < k
    · simp [hi, h i hi]
    · simp [hi]

theorem mod_pow2_of_le {a b k j : Nat} (hjk : j ≤ k) (h : a % 2 ^ k = b % 2 ^ k) :
    a % 2 ^ j = b % 2 ^ j := by
  rw [mod_two_pow_eq_iff] at h ⊢
  intro i hi
  exact h i (Nat.lt_of_lt_of_le hi hjk)

theorem testBit_add_pow2_lt (x k i : Nat) (hi : i < k) :
    (x + 2 ^ k).testBit i = x.testBit i := by
  have h : (x + 2 ^ k) % 2 ^ k = x % 2 ^ k := Nat.add_mod_right x (2 ^ k)
  exact (mod_two_pow_eq_iff _ _ _).mp h i hi

theorem testBit_add_pow2_eq (x k : Nat) :
    (x + 2 ^ k).testBit k = !x.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hdiv : (x + 2 ^ k) / 2 ^ k = x / 2 ^ k + 1 := Nat.add_div_right x (pow2_pos k)
  rw [hdiv]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h0 | h1
  · have : (x / 2 ^ k + 1) % 2 = 1 := by omega
    simp [h0, this]
  · have : (x / 2 ^ k + 1) % 2 = 0 := by omega
    simp [h1, this]

theorem add_pow2_mod_pow2_succ_eq_xor (x k : Nat) :
    (x + 2 ^ k) % 2 ^ (k + 1) = (x ^^^ (1 <<< k)) % 2 ^ (k + 1) := by
  rw [mod_two_pow_eq_iff]
  intro i hi
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hlt : i < k
  · have hge : ¬(k ≤ i) := Nat.not_le.mpr hlt
    simp [hge, testBit_add_pow2_lt x k i hlt]
  · have heq : i = k := by omega
    subst heq
    simp [testBit_add_pow2_eq]

theorem xor_pow2_mod_pow2_eq_add (x k : Nat) (hk : 1 ≤ k) :
    (x ^^^ (1 <<< (k - 1))) % 2 ^ k = (x + 2 ^ (k - 1)) % 2 ^ k := by
  have h := add_pow2_mod_pow2_succ_eq_xor x (k - 1)
  have h1 : k - 1 + 1 = k := by omega
  rw [h1] at h
  exact h.symm

theorem xor_mod_pow2 (a b k : Nat) :
    (a ^^^ b) % 2 ^ k = ((a % 2 ^ k) ^^^ (b % 2 ^ k)) % 2 ^ k := by
  rw [mod_two_pow_eq_iff]
  intro i hi
  simp [Nat.testBit_xor, Nat.testBit_mod_two_pow, hi]

theorem shiftLeft_eq_mul_pow2 (a k : Nat) : a <<< k = a * 2 ^ k :=
  Nat.shiftLeft_eq a k

theorem div2_mod_pow2 (a k : Nat) : (a / 2) % 2 ^ k = (a % 2 ^ (k + 1)) / 2 := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mod_mul_right_div_self]

theorem mod_pow2_succ_eq (a k : Nat) :
    a % 2 ^ (k + 1) = a % 2 + 2 * ((a / 2) % 2 ^ k) := by
  rw [div2_mod_pow2]
  have hdiv := Nat.div_add_mod (a % 2 ^ (k + 1)) 2
  have hmod2 : (a % 2 ^ (k + 1)) % 2 = a % 2 := by
    have := mod_pow2_of_le (a := a) (b := a % 2 ^ (k + 1)) (k := k + 1) (j := 1) (by omega)
      (by simp)
    simpa using this.symm
  omega

-- `clmul` algebraic laws

theorem clmul_zero_left (b : Nat) : clmul 0 b = 0 := rfl

theorem clmul_zero_right (a : Nat) : clmul a 0 = 0 := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [clmul_eq]
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha, ih (a / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega))]

theorem clmul_one_left (b : Nat) : clmul 1 b = b := by
  rw [clmul_eq]; simp [clmul_zero_left]

theorem clmul_xor_right (p a b : Nat) :
    clmul p (a ^^^ b) = clmul p a ^^^ clmul p b := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    rw [clmul_eq p (a ^^^ b), clmul_eq p a, clmul_eq p b]
    by_cases hp : p = 0
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      rw [ih (p / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hp) (by omega))]
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hodd : p % 2 = 1
      · simp only [hodd, ↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft]
        cases a.testBit i <;> cases b.testBit i <;>
        cases decide (1 ≤ i) <;>
        cases (clmul (p / 2) a).testBit (i - 1) <;>
        cases (clmul (p / 2) b).testBit (i - 1) <;> rfl
      · simp only [hodd, ↓reduceIte, Nat.zero_xor, Nat.testBit_xor, Nat.testBit_shiftLeft]
        cases decide (1 ≤ i) <;>
        cases (clmul (p / 2) a).testBit (i - 1) <;>
        cases (clmul (p / 2) b).testBit (i - 1) <;> rfl

theorem clmul_shiftLeft_right (p a k : Nat) :
    clmul p (a <<< k) = (clmul p a) <<< k := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    rw [clmul_eq p (a <<< k), clmul_eq p a]
    by_cases hp : p = 0
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      rw [ih (p / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hp) (by omega))]
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hodd : p % 2 = 1
      · simp only [hodd, ↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft]
        by_cases hik : k ≤ i
        · by_cases hi1 : 1 ≤ i
          · have h1 : 1 ≤ i - k ↔ k + 1 ≤ i := by omega
            have h2 : k ≤ i - 1 ↔ k + 1 ≤ i := by omega
            have h3 : i - 1 - k = i - k - 1 := by omega
            by_cases hk1 : k + 1 ≤ i
            · simp [hik, hi1, h1.mpr hk1, h2.mpr hk1, h3]
            · simp [hik, hi1, h1, h2, hk1]
          · have hk0 : k = 0 := by omega
            have hi0 : i = 0 := by omega
            subst hk0; subst hi0; simp
        · have hnot : ¬(k ≤ i - 1) := by omega
          simp [hik, hnot]
      · simp only [hodd, ↓reduceIte, Nat.zero_xor, Nat.testBit_shiftLeft]
        by_cases hik : k ≤ i
        · by_cases hi1 : 1 ≤ i
          · have h1 : 1 ≤ i - k ↔ k + 1 ≤ i := by omega
            have h2 : k ≤ i - 1 ↔ k + 1 ≤ i := by omega
            have h3 : i - 1 - k = i - k - 1 := by omega
            by_cases hk1 : k + 1 ≤ i
            · simp [hik, hi1, h1.mpr hk1, h2.mpr hk1, h3]
            · simp [hik, hi1, h1, h2, hk1]
          · have hk0 : k = 0 := by omega
            have hi0 : i = 0 := by omega
            subst hk0; subst hi0; simp
        · have hnot : ¬(k ≤ i - 1) := by omega
          simp [hik, hnot]

theorem clmul_two_mul_left (u x : Nat) :
    clmul (2 * u) x = (clmul u x) <<< 1 := by
  by_cases hu : u = 0
  · subst hu; simp [clmul_zero_left]
  · rw [clmul_eq (2 * u) x]
    have h2u : 2 * u ≠ 0 := by omega
    have hmod : (2 * u) % 2 = 0 := by omega
    have hdiv : (2 * u) / 2 = u := by omega
    simp [h2u, hmod, hdiv]

theorem clmul_pow2_mul_left (v u x : Nat) :
    clmul (2 ^ v * u) x = (clmul u x) <<< v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have h : 2 ^ (v + 1) * u = 2 * (2 ^ v * u) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc]
    rw [h, clmul_two_mul_left, ih]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_shiftLeft]
    by_cases h1 : 1 ≤ i
    · by_cases hv : v ≤ i - 1
      · have hv1 : v + 1 ≤ i := by omega
        have heq : i - 1 - v = i - (v + 1) := by omega
        simp [h1, hv, hv1, heq]
      · have hv1 : ¬(v + 1 ≤ i) := by omega
        simp [h1, hv, hv1]
    · have hv1 : ¬(v + 1 ≤ i) := by omega
      simp [h1, hv1]

theorem clmul_one_add_pow2_mul_left (v u x : Nat) (hv : 1 ≤ v) :
    clmul (1 + 2 ^ v * u) x = x ^^^ ((clmul u x) <<< v) := by
  rw [clmul_eq (1 + 2 ^ v * u) x]
  have hne : 1 + 2 ^ v * u ≠ 0 := by omega
  have h2 : 2 ^ v = 2 * 2 ^ (v - 1) := pow2_split v hv
  have hmul2 : 2 ^ v * u = 2 * (2 ^ (v - 1) * u) := by rw [h2, Nat.mul_assoc]
  have hmod : (1 + 2 ^ v * u) % 2 = 1 := by rw [hmul2]; omega
  have hdiv : (1 + 2 ^ v * u) / 2 = 2 ^ (v - 1) * u := by rw [hmul2]; omega
  simp only [hne, ↓reduceIte, hmod, hdiv]
  rw [clmul_pow2_mul_left]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftLeft]
  by_cases h1 : 1 ≤ i
  · by_cases hvi : v ≤ i
    · have hv1 : v - 1 ≤ i - 1 := by omega
      have heq : i - 1 - (v - 1) = i - v := by omega
      simp [h1, hv1, hvi, heq]
    · have hv1 : ¬(v - 1 ≤ i - 1) := by omega
      simp [h1, hv1, hvi]
  · have hvi : ¬(v ≤ i) := by omega
    simp [h1, hvi]

theorem clmul_mod_pow2 (p a k : Nat) :
    clmul p (a % 2 ^ k) % 2 ^ k = clmul p a % 2 ^ k := by
  induction p using Nat.strongRecOn generalizing k with
  | ind p ih =>
    rw [clmul_eq p (a % 2 ^ k), clmul_eq p a]
    by_cases hp : p = 0
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      rw [mod_two_pow_eq_iff]
      intro i hi
      simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
      have hfirst : (if p % 2 = 1 then a % 2 ^ k else 0).testBit i =
                    (if p % 2 = 1 then a else 0).testBit i := by
        split <;> simp [Nat.testBit_mod_two_pow, hi]
      rw [hfirst]
      congr 1
      by_cases hi1 : 1 ≤ i
      · simp only [hi1, decide_true, Bool.true_and]
        have hlt : i - 1 < k := by omega
        have hrec := ih (p / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hp) (by omega)) k
        exact (mod_two_pow_eq_iff _ _ _).mp hrec (i - 1) hlt
      · simp [hi1]

theorem clmul_mod_two (p a : Nat) :
    clmul p a % 2 = (p % 2) * (a % 2) := by
  rw [clmul_eq]
  by_cases hp : p = 0
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    have h0 : ((clmul (p / 2) a <<< 1) % 2) = 0 := by
      rw [shiftLeft_eq_mul_pow2]; omega
    have hxor : ∀ u v : Nat, v % 2 = 0 → (u ^^^ v) % 2 = u % 2 := by
      intro u v hv
      have h1 : (u ^^^ v).testBit 0 = u.testBit 0 := by
        rw [Nat.testBit_xor]
        have hv0 : v.testBit 0 = false := by
          rw [Nat.testBit_zero]; simp [hv]
        simp [hv0]
      rw [Nat.testBit_zero, Nat.testBit_zero] at h1
      rcases Nat.mod_two_eq_zero_or_one (u ^^^ v) with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one u with hb | hb <;> simp_all
    rw [hxor _ _ h0]
    rcases Nat.mod_two_eq_zero_or_one p with hp0 | hp1
    · simp [hp0]
    · simp [hp1]

theorem clmul_one_right (p : Nat) : clmul p 1 = p := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    rw [clmul_eq]
    by_cases hp : p = 0
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      rw [ih (p / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hp) (by omega))]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
      cases i with
      | zero =>
        simp only [Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one p with hp0 | hp1
        · simp [hp0]
        · simp [hp1]
      | succ i =>
        have hlo : (if p % 2 = 1 then 1 else 0).testBit (i + 1) = false := by
          split
          · exact Nat.testBit_lt_two_pow (by
              have hge : 2 ^ 1 ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
              have h1 : 1 < 2 ^ (i + 1) := Nat.lt_of_lt_of_le (by omega) hge
              exact h1)
          · simp
        rw [hlo, Bool.false_xor]
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.le_add_left, decide_true,
                   Bool.true_and, testBit_div_two]

-- `bitDeg` and `clmul_bitDeg` lemmas

theorem bitDeg_bounds {n : Nat} (hn : 0 < n) :
    2 ^ bitDeg n ≤ n ∧ n < 2 ^ (bitDeg n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [bitDeg_eq n]
    by_cases hle : n ≤ 1
    · have hn1 : n = 1 := by omega
      subst hn1; simp
    · simp only [hle, ↓reduceIte]
      have hpos : 0 < n / 2 := by omega
      have hlt : n / 2 < n := Nat.div_lt_self hn (by omega)
      have ⟨h1, h2⟩ := ih (n / 2) hlt hpos
      rw [Nat.pow_succ, Nat.pow_succ]
      omega

theorem bitDeg_eq_of_bounds {n d : Nat} (h1 : 2 ^ d ≤ n) (h2 : n < 2 ^ (d + 1)) :
    bitDeg n = d := by
  have hn : 0 < n := Nat.lt_of_lt_of_le (pow2_pos d) h1
  have ⟨b1, b2⟩ := bitDeg_bounds hn
  rcases Nat.lt_trichotomy (bitDeg n) d with hlt | heq | hgt
  · have hle : bitDeg n + 1 ≤ d := by omega
    have hp : 2 ^ (bitDeg n + 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hle
    omega
  · exact heq
  · have hle : d + 1 ≤ bitDeg n := by omega
    have hp : 2 ^ (d + 1) ≤ 2 ^ bitDeg n := Nat.pow_le_pow_right (by omega) hle
    omega

theorem xor_preserves_band {a b N : Nat} (ha1 : 2 ^ N ≤ a) (ha2 : a < 2 ^ (N + 1))
    (hb : b < 2 ^ N) :
    2 ^ N ≤ a ^^^ b ∧ a ^^^ b < 2 ^ (N + 1) := by
  have hlt : a ^^^ b < 2 ^ (N + 1) :=
    Nat.xor_lt_two_pow ha2 (Nat.lt_trans hb (by rw [Nat.pow_succ]; omega))
  have haN : a.testBit N = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : a / 2 ^ N = 1 := by
      have hp := pow2_pos N
      have h2 : a < 2 * 2 ^ N := by rw [Nat.pow_succ] at ha2; omega
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hdiv]
  have hbN : b.testBit N = false := Nat.testBit_lt_two_pow hb
  have hxorN : (a ^^^ b).testBit N = true := by
    rw [Nat.testBit_xor, haN, hbN]; rfl
  have hge : 2 ^ N ≤ a ^^^ b := by
    cases Nat.lt_or_ge (a ^^^ b) (2 ^ N) with
    | inl hltN =>
      have hf := Nat.testBit_lt_two_pow hltN
      rw [hxorN] at hf
      exact Bool.noConfusion hf
    | inr hgeN => exact hgeN
  exact ⟨hge, hlt⟩

theorem clmul_bitDeg {p x : Nat} (hp : 0 < p) (hx : 0 < x) :
    2 ^ (bitDeg p + bitDeg x) ≤ clmul p x ∧
    clmul p x < 2 ^ (bitDeg p + bitDeg x + 1) := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    by_cases hp1 : p ≤ 1
    · have hpEq : p = 1 := by omega
      subst hpEq
      have hd0 : bitDeg 1 = 0 := rfl
      rw [clmul_one_left, hd0, Nat.zero_add]
      exact bitDeg_bounds hx
    · have hp_pos2 : 0 < p / 2 := by omega
      have hp_lt : p / 2 < p := Nat.div_lt_self hp (by omega)
      have ⟨ih1, ih2⟩ := ih (p / 2) hp_lt hp_pos2
      have hdeg_p : bitDeg p = bitDeg (p / 2) + 1 := by
        rw [bitDeg_eq p]; simp [hp1]
      have hN : bitDeg p + bitDeg x = (bitDeg (p / 2) + bitDeg x) + 1 := by omega
      have hsh1 : 2 ^ (bitDeg p + bitDeg x) ≤ (clmul (p / 2) x) <<< 1 := by
        rw [shiftLeft_eq_mul_pow2, hN, Nat.pow_succ]; omega
      have hsh2 : (clmul (p / 2) x) <<< 1 < 2 ^ (bitDeg p + bitDeg x + 1) := by
        rw [shiftLeft_eq_mul_pow2, hN, Nat.pow_succ, Nat.pow_succ]; omega
      have hlo : (if p % 2 = 1 then x else 0) < 2 ^ (bitDeg p + bitDeg x) := by
        have ⟨_, hx2⟩ := bitDeg_bounds hx
        have hle : bitDeg x + 1 ≤ bitDeg p + bitDeg x := by omega
        have hp2 := Nat.pow_le_pow_right (n := 2) (by omega) hle
        split
        · exact Nat.lt_of_lt_of_le hx2 hp2
        · exact pow2_pos _
      rw [clmul_eq p x]
      have hpne : p ≠ 0 := by omega
      simp only [hpne, ↓reduceIte]
      rw [Nat.xor_comm]
      exact xor_preserves_band hsh1 hsh2 hlo

-- `v2` decomposition lemma

theorem v2_decomp {n : Nat} (hn : 0 < n) :
    ∃ u : Nat, u % 2 = 1 ∧ n = 2 ^ v2 n * u := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hne : n ≠ 0 := by omega
    by_cases hodd : n % 2 = 1
    · have hv0 : v2 n = 0 := by rw [v2_eq n]; simp [hne, hodd]
      exact ⟨n, hodd, by simp [hv0]⟩
    · have hv_step : v2 n = v2 (n / 2) + 1 := by
        rw [v2_eq n]; simp [hne, hodd]
      have hpos : 0 < n / 2 := by omega
      have hlt : n / 2 < n := Nat.div_lt_self hn (by omega)
      have ⟨u, hu, heq⟩ := ih (n / 2) hlt hpos
      refine ⟨u, hu, ?_⟩
      rw [hv_step, Nat.pow_succ]
      have heven : n = 2 * (n / 2) := by omega
      calc n = 2 * (n / 2) := heven
        _ = 2 * (2 ^ v2 (n / 2) * u) := congrArg (2 * ·) heq
        _ = 2 ^ v2 (n / 2) * 2 * u := by rw [Nat.mul_left_comm, Nat.mul_assoc]

-- `popcount` helper lemmas

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_bit_add (b y : Nat) (hb : b < 2) :
    popcount (b + 2 * y) = b + popcount y := by
  by_cases hby : b + 2 * y = 0
  · have hb0 : b = 0 := by omega
    have hy0 : y = 0 := by omega
    subst hb0; subst hy0; rfl
  · rw [popcount_eq (b + 2 * y)]
    simp only [hby, ↓reduceIte]
    have hmod : (b + 2 * y) % 2 = b := by omega
    have hdiv : (b + 2 * y) / 2 = y := by omega
    rw [hmod, hdiv]

theorem popcount_le_width (k x : Nat) (hx : x < 2 ^ k) : popcount x ≤ k := by
  induction k generalizing x with
  | zero =>
    have hx0 : x = 0 := by simp at hx; omega
    subst hx0; simp [popcount_zero]
  | succ k ih =>
    have hx_split : x = x % 2 + 2 * (x / 2) := by omega
    have hpop_x : popcount x = x % 2 + popcount (x / 2) := by
      rw [← popcount_bit_add (x % 2) (x / 2) (Nat.mod_lt x (by omega)), ← hx_split]
    have hdiv : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have hih := ih (x / 2) hdiv
    have hmod : x % 2 ≤ 1 := by omega
    omega

theorem popcount_eq_width_iff (k x : Nat) (hx : x < 2 ^ k) :
    popcount x = k ↔ x = 2 ^ k - 1 := by
  induction k generalizing x with
  | zero =>
    simp at hx
    constructor
    · intro _; omega
    · intro _; subst hx; rfl
  | succ k ih =>
    have hx_split : x = x % 2 + 2 * (x / 2) := by omega
    have hdiv_lt : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
    have hpop_div : popcount (x / 2) ≤ k := popcount_le_width k (x / 2) hdiv_lt
    have hpop_x : popcount x = x % 2 + popcount (x / 2) := by
      rw [← popcount_bit_add (x % 2) (x / 2) (Nat.mod_lt x (by omega)), ← hx_split]
    constructor
    · intro h
      have hmod1 : x % 2 = 1 := by omega
      have hpopk : popcount (x / 2) = k := by omega
      have hdiv_eq := (ih (x / 2) hdiv_lt).mp hpopk
      have hp := pow2_pos k
      rw [Nat.pow_succ]
      omega
    · intro h
      have hp := pow2_pos k
      have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      have hmod1 : x % 2 = 1 := by omega
      have hdiv_eq : x / 2 = 2 ^ k - 1 := by omega
      have hpopk := (ih (x / 2) hdiv_lt).mpr hdiv_eq
      omega

/-- Canonical bijective 2-adic piecewise-affine lift `G_T(x) = (x % 2) + 2 * T(x)`. -/
def bijectiveLift (T : Nat → Nat) (x : Nat) : Nat :=
  x % 2 + 2 * T x

-- Basic properties of `Q`

theorem Q_lt (T : Nat → Nat) (k x : Nat) : Q T k x < 2 ^ k := by
  induction k generalizing x with
  | zero => simp [Q]
  | succ k ih =>
    simp only [Q]
    have h := ih (T x)
    have hmod : x % 2 < 2 := Nat.mod_lt x (by omega)
    rw [Nat.pow_succ]
    omega

theorem Q_conj_shift (T : Nat → Nat) (k x : Nat) :
    Q T k (T x) = Q T (k + 1) x / 2 := by
  simp only [Q]
  have hmod : x % 2 < 2 := Nat.mod_lt x (by omega)
  omega

theorem Q_mod_compat (T : Nat → Nat) (k x : Nat) :
    Q T (k + 1) x % 2 ^ k = Q T k x := by
  induction k generalizing x with
  | zero => simp [Q, Nat.mod_one]
  | succ k ih =>
    have hmod : x % 2 < 2 := Nat.mod_lt x (by omega)
    have hih := ih (T x)
    have h1 : (x % 2 + 2 * Q T (k + 1) (T x)) % (2 * 2 ^ k) =
              x % 2 + 2 * (Q T (k + 1) (T x) % 2 ^ k) := by
      have hlt : x % 2 + 2 * (Q T (k + 1) (T x) % 2 ^ k) < 2 * 2 ^ k := by
        have := Nat.mod_lt (Q T (k + 1) (T x)) (pow2_pos k)
        omega
      have heq : x % 2 + 2 * Q T (k + 1) (T x) =
                 (x % 2 + 2 * (Q T (k + 1) (T x) % 2 ^ k)) + (2 * 2 ^ k) * (Q T (k + 1) (T x) / 2 ^ k) := by
        have hdm := Nat.div_add_mod (Q T (k + 1) (T x)) (2 ^ k)
        calc x % 2 + 2 * Q T (k + 1) (T x)
            = x % 2 + 2 * (2 ^ k * (Q T (k + 1) (T x) / 2 ^ k) + Q T (k + 1) (T x) % 2 ^ k) := by
              rw [hdm]
          _ = (x % 2 + 2 * (Q T (k + 1) (T x) % 2 ^ k)) + (2 * 2 ^ k) * (Q T (k + 1) (T x) / 2 ^ k) := by
              rw [Nat.mul_add, ← Nat.mul_assoc]; omega
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    change (x % 2 + 2 * Q T (k + 1) (T x)) % 2 ^ (k + 1) = x % 2 + 2 * Q T k (T x)
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, h1, hih]

theorem Q_mod_compat_le (T : Nat → Nat) {j k : Nat} (hjk : j ≤ k) (x : Nat) :
    Q T k x % 2 ^ j = Q T j x := by
  induction k with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0; simp [Q]
  | succ m ih =>
    by_cases hjm : j ≤ m
    · have h1 := mod_pow2_of_le (a := Q T (m + 1) x) (b := Q T m x) (k := m) (j := j) hjm
        (by rw [Q_mod_compat, Nat.mod_eq_of_lt (Q_lt T m x)])
      rw [h1, ih hjm]
    · have hjeq : j = m + 1 := by omega
      subst hjeq
      exact Nat.mod_eq_of_lt (Q_lt T (m + 1) x)

theorem Q_bit (T : Nat → Nat) (j k x : Nat) (hjk : j < k) :
    (Q T k x / 2 ^ j) % 2 = (iter T j x) % 2 := by
  induction j generalizing k x with
  | zero =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [Nat.pow_zero, Nat.div_one, Q, iter]
      omega
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [Q, iter]
      have hdiv : (x % 2 + 2 * Q T k (T x)) / 2 ^ (j + 1) = Q T k (T x) / 2 ^ j := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
        have hstep : (x % 2 + 2 * Q T k (T x)) / 2 = Q T k (T x) := by
          have : x % 2 < 2 := Nat.mod_lt x (by omega); omega
        rw [hstep]
      rw [hdiv]
      exact ih k (T x) (by omega)

theorem Q_succ_high (T : Nat → Nat) (k x : Nat) :
    Q T (k + 1) x = Q T k x + ((iter T k x) % 2) * 2 ^ k := by
  have hcompat := Q_mod_compat T k x
  have hlt := Q_lt T (k + 1) x
  have hdiv : Q T (k + 1) x / 2 ^ k = (iter T k x) % 2 := by
    have hbit := Q_bit T k (k + 1) x (Nat.lt_succ_self k)
    have hq_lt2 : Q T (k + 1) x / 2 ^ k < 2 := by
      rw [Nat.pow_succ] at hlt
      exact Nat.div_lt_of_lt_mul (by omega)
    rw [Nat.mod_eq_of_lt hq_lt2] at hbit
    exact hbit
  have hdm := Nat.div_add_mod (Q T (k + 1) x) (2 ^ k)
  rw [hcompat, hdiv, Nat.mul_comm (2 ^ k)] at hdm
  omega

-- ShiftFaithful iteration laws

theorem ShiftFaithful.iter_causal {T : Nat → Nat} (hT : ShiftFaithful T) :
    ∀ j k x y, x % 2 ^ (k + j) = y % 2 ^ (k + j) →
      iter T j x % 2 ^ k = iter T j y % 2 ^ k := by
  intro j
  induction j with
  | zero => intro k x y h; simpa [iter] using h
  | succ j ih =>
    intro k x y h
    simp only [iter]
    apply ih k (T x) (T y)
    have h' : x % 2 ^ (k + j + 1) = y % 2 ^ (k + j + 1) := by
      have : k + (j + 1) = k + j + 1 := by omega
      rwa [← this]
    exact hT.causal (k + j) x y h'

theorem ShiftFaithful.Q_congr {T : Nat → Nat} (hT : ShiftFaithful T) (k x y : Nat)
    (hxy : x % 2 ^ k = y % 2 ^ k) : Q T k x = Q T k y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [Q]
    have h0 : x % 2 = y % 2 := by
      simpa using mod_pow2_of_le (j := 1) (k := k + 1) (by omega) hxy
    have h1 : T x % 2 ^ k = T y % 2 ^ k := hT.causal k x y hxy
    rw [h0, ih (T x) (T y) h1]

theorem ShiftFaithful.iter_flip {T : Nat → Nat} (hT : ShiftFaithful T) :
    ∀ j k x, j ≤ k →
      iter T j (x + 2 ^ k) % 2 ^ (k - j + 1) = (iter T j x + 2 ^ (k - j)) % 2 ^ (k - j + 1) := by
  intro j
  induction j with
  | zero =>
    intro k x _
    simp [iter]
  | succ j ih =>
    intro k x hjk
    have hk1 : 1 ≤ k := by omega
    have hstep := hT.flip k x hk1
    have heq1 : k - (j + 1) + 1 + j = k := by omega
    have hc := hT.iter_causal j (k - (j + 1) + 1) (T (x + 2 ^ k)) (T x + 2 ^ (k - 1))
      (by rwa [heq1])
    simp only [iter]
    rw [hc]
    have hih := ih (k - 1) (T x) (by omega)
    have heq2 : k - 1 - j = k - (j + 1) := by omega
    rwa [heq2] at hih

theorem ShiftFaithful.Q_flip {T : Nat → Nat} (hT : ShiftFaithful T) (k x : Nat) :
    Q T (k + 1) (x + 2 ^ k) =
      Q T k x + ((iter T k x + 1) % 2) * 2 ^ k := by
  rw [Q_succ_high]
  have hlo : Q T k (x + 2 ^ k) = Q T k x :=
    hT.Q_congr k (x + 2 ^ k) x (Nat.add_mod_right x (2 ^ k))
  have hhi := hT.iter_flip k k x (Nat.le_refl k)
  simp only [Nat.sub_self, Nat.pow_zero, Nat.zero_add, Nat.pow_one] at hhi
  rw [hlo, hhi]

-- Constructive O(k) Hensel Decoder `R` theorems

theorem R_lt (T : Nat → Nat) (k y : Nat) : R T k y < 2 ^ k := by
  induction k with
  | zero => simp [R]
  | succ k ih =>
    simp only [R]
    split
    · exact Nat.lt_trans ih (by rw [Nat.pow_succ]; omega)
    · rw [Nat.pow_succ]; omega

theorem R_mod_compat (T : Nat → Nat) (k y : Nat) :
    R T (k + 1) y % 2 ^ k = R T k y := by
  simp only [R]
  have hlt := R_lt T k y
  split
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

theorem R_congr (T : Nat → Nat) (k y1 y2 : Nat) (hy : y1 % 2 ^ k = y2 % 2 ^ k) :
    R T k y1 = R T k y2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [R]
    have hlo := mod_pow2_of_le (j := k) (k := k + 1) (by omega) hy
    rw [ih hlo]
    have hbit : (y1 / 2 ^ k) % 2 = (y2 / 2 ^ k) % 2 := by
      have hb := (mod_two_pow_eq_iff y1 y2 (k + 1)).mp hy k (Nat.lt_succ_self k)
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at hb
      rcases Nat.mod_two_eq_zero_or_one (y1 / 2 ^ k) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (y2 / 2 ^ k) with h2 | h2 <;> simp_all
    rw [hbit]

theorem mod_pow2_succ_high (y k : Nat) :
    y % 2 ^ (k + 1) = y % 2 ^ k + ((y / 2 ^ k) % 2) * 2 ^ k := by
  have h1 : (y % 2 ^ (k + 1)) / 2 ^ k = (y / 2 ^ k) % 2 := by
    rw [Nat.pow_succ, Nat.mod_mul_right_div_self]
  have h2 : (y % 2 ^ (k + 1)) % 2 ^ k = y % 2 ^ k := by
    rw [Nat.pow_succ, Nat.mod_mul_right_mod]
  have hdm := Nat.div_add_mod (y % 2 ^ (k + 1)) (2 ^ k)
  rw [h1, h2, Nat.mul_comm (2 ^ k)] at hdm
  omega

/-- **Theorem 1 (Right-Inverse of Silicon Hensel Decoder):**
    `Q T k (R T k y) = y % 2^k` for ALL widths `k` and ALL `y`. -/
theorem ShiftFaithful.Q_R_cancel {T : Nat → Nat} (hT : ShiftFaithful T) (k y : Nat) :
    Q T k (R T k y) = y % 2 ^ k := by
  induction k with
  | zero => simp [Q, Nat.mod_one]
  | succ k ih =>
    have hmod_decomp := mod_pow2_succ_high y k
    simp only [R]
    split
    · rename_i heq
      rw [Q_succ_high, ih, heq, hmod_decomp]
    · rename_i hne
      rw [hT.Q_flip, ih, hmod_decomp]
      congr 1
      have hbit : (iter T k (R T k y) + 1) % 2 = (y / 2 ^ k) % 2 := by
        rcases Nat.mod_two_eq_zero_or_one (iter T k (R T k y)) with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ k) with h2 | h2 <;> omega
      rw [hbit]

/-- **Theorem 2 (2-Adic Isometry / Injectivity of `Q`):**
    `Q T k x = Q T k y -> x % 2^k = y % 2^k` for ALL `k, x, y`. -/
theorem ShiftFaithful.Q_inj_mod {T : Nat → Nat} (hT : ShiftFaithful T) (k x y : Nat)
    (h : Q T k x = Q T k y) : x % 2 ^ k = y % 2 ^ k := by
  induction k generalizing x y with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hlo : Q T k x = Q T k y := by
      have h1 := congrArg (· % 2 ^ k) h
      rwa [Q_mod_compat, Q_mod_compat] at h1
    have hxymod : x % 2 ^ k = y % 2 ^ k := ih x y hlo
    have hbitx : (x / 2 ^ k) % 2 = (y / 2 ^ k) % 2 := by
      have hx_dec := mod_pow2_succ_high x k
      have hy_dec := mod_pow2_succ_high y k
      have h2k_lt : 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; have := pow2_pos k; omega
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with hx0 | hx1 <;>
      rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ k) with hy0 | hy1
      · omega
      · exfalso
        have hmod : y % 2 ^ (k + 1) = (x + 2 ^ k) % 2 ^ (k + 1) := by
          have hadd : (x + 2 ^ k) % 2 ^ (k + 1) = (x % 2 ^ (k + 1) + 2 ^ k) % 2 ^ (k + 1) := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt h2k_lt]
          rw [hadd, hx_dec, hy_dec, hx0, hy1, hxymod]
          simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul]
          exact (Nat.mod_eq_of_lt (by
            have := Nat.mod_lt y (pow2_pos k)
            rw [Nat.pow_succ]; omega)).symm
        have hqy := hT.Q_congr (k + 1) y (x + 2 ^ k) hmod
        rw [hT.Q_flip] at hqy
        have hqx := Q_succ_high T k x
        rw [hqx, hqy] at h
        have hbit_eq : (iter T k x) % 2 = (iter T k x + 1) % 2 := by
          have hp := pow2_pos k
          have : ((iter T k x) % 2) * 2 ^ k = ((iter T k x + 1) % 2) * 2 ^ k := by omega
          exact Nat.eq_of_mul_eq_mul_right hp this
        omega
      · exfalso
        have hmod : x % 2 ^ (k + 1) = (y + 2 ^ k) % 2 ^ (k + 1) := by
          have hadd : (y + 2 ^ k) % 2 ^ (k + 1) = (y % 2 ^ (k + 1) + 2 ^ k) % 2 ^ (k + 1) := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt h2k_lt]
          rw [hadd, hx_dec, hy_dec, hx1, hy0, hxymod]
          simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul]
          exact (Nat.mod_eq_of_lt (by
            have := Nat.mod_lt y (pow2_pos k)
            rw [Nat.pow_succ]; omega)).symm
        have hqx := hT.Q_congr (k + 1) x (y + 2 ^ k) hmod
        rw [hT.Q_flip] at hqx
        have hqy := Q_succ_high T k y
        rw [hqx, hqy] at h
        have hbit_eq : (iter T k y + 1) % 2 = (iter T k y) % 2 := by
          have hp := pow2_pos k
          have : ((iter T k y + 1) % 2) * 2 ^ k = ((iter T k y) % 2) * 2 ^ k := by omega
          exact Nat.eq_of_mul_eq_mul_right hp this
        omega
      · omega
    rw [mod_pow2_succ_high, mod_pow2_succ_high, hxymod, hbitx]

/-- **Theorem 3 (Left-Inverse of Silicon Hensel Decoder):**
    `R T k (Q T k x) = x % 2^k` for ALL widths `k` and ALL `x`. -/
theorem ShiftFaithful.R_Q_cancel {T : Nat → Nat} (hT : ShiftFaithful T) (k x : Nat) :
    R T k (Q T k x) = x % 2 ^ k := by
  have h1 : Q T k (R T k (Q T k x)) = Q T k x := by
    rw [hT.Q_R_cancel, Nat.mod_eq_of_lt (Q_lt T k x)]
  have h2 := hT.Q_inj_mod k (R T k (Q T k x)) x h1
  rwa [Nat.mod_eq_of_lt (R_lt T k (Q T k x))] at h2

/-- **Theorem 4 (Exact 2-Adic Isometry):**
    `Q T k x % 2^j = Q T k y % 2^j ↔ x % 2^j = y % 2^j` for ALL `j ≤ k`. -/
theorem ShiftFaithful.Q_isometry {T : Nat → Nat} (hT : ShiftFaithful T) {j k : Nat} (hjk : j ≤ k)
    (x y : Nat) : Q T k x % 2 ^ j = Q T k y % 2 ^ j ↔ x % 2 ^ j = y % 2 ^ j := by
  rw [Q_mod_compat_le T hjk x, Q_mod_compat_le T hjk y]
  exact ⟨hT.Q_inj_mod j x y, hT.Q_congr j x y⟩

/-- Iterated shift conjugacy: `Q T k (iter T m x) = Q T (k + m) x / 2^m`. -/
theorem Q_iter_conj_shift (T : Nat → Nat) (m k x : Nat) :
    Q T k (iter T m x) = Q T (k + m) x / 2 ^ m := by
  induction m generalizing k x with
  | zero => simp [iter]
  | succ m ih =>
    simp only [iter]
    have h1 : k + (m + 1) = (k + m) + 1 := by omega
    rw [ih k (T x), Q_conj_shift, h1, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

/--
  **Theorem 5 (Exact m-Step 2-Adic Haar Measure Preservation):**
  For EVERY `ShiftFaithful` map `T`, EVERY `k, m : Nat`, and EVERY target cylinder `y < 2^k`,
  the `m`-step preimage fiber `{ x < 2^(k + m) | T^[m] x % 2^k = y }` is in EXPLICIT
  CONSTRUCTIVE BIJECTION with `Fin (2^m)` via `r ↦ R T (k + m) (r + 2^m * Q T k y)`.
-/
theorem ShiftFaithful.measure_preserving_m_steps {T : Nat → Nat} (hT : ShiftFaithful T)
    (k m y : Nat) (hy : y < 2 ^ k) :
    let enc : Nat → Nat := fun r => R T (k + m) (r + 2 ^ m * Q T k y)
    let dec : Nat → Nat := fun x => Q T m x
    (∀ r, r < 2 ^ m →
      enc r < 2 ^ (k + m) ∧ iter T m (enc r) % 2 ^ k = y ∧ dec (enc r) = r) ∧
    (∀ x, x < 2 ^ (k + m) → iter T m x % 2 ^ k = y →
      dec x < 2 ^ m ∧ enc (dec x) = x) := by
  dsimp only
  constructor
  · intro r hr
    refine ⟨R_lt T (k + m) _, ?_, ?_⟩
    · have hqlt : Q T k y < 2 ^ k := Q_lt T k y
      have hsum_lt : r + 2 ^ m * Q T k y < 2 ^ (k + m) := by
        rw [Nat.pow_add, Nat.mul_comm (2 ^ k) (2 ^ m)]
        have : 2 ^ m * (Q T k y + 1) ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      have hq := hT.Q_R_cancel (k + m) (r + 2 ^ m * Q T k y)
      rw [Nat.mod_eq_of_lt hsum_lt] at hq
      have hiter : Q T k (iter T m (R T (k + m) (r + 2 ^ m * Q T k y))) = Q T k y := by
        rw [Q_iter_conj_shift, hq, Nat.add_mul_div_left _ _ (pow2_pos m),
            Nat.div_eq_of_lt hr, Nat.zero_add]
      have hinj := hT.Q_inj_mod k _ y hiter
      rwa [Nat.mod_eq_of_lt hy] at hinj
    · have hqlt : Q T k y < 2 ^ k := Q_lt T k y
      have hsum_lt : r + 2 ^ m * Q T k y < 2 ^ (k + m) := by
        rw [Nat.pow_add, Nat.mul_comm (2 ^ k) (2 ^ m)]
        have : 2 ^ m * (Q T k y + 1) ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      have h1 : Q T m (R T (k + m) (r + 2 ^ m * Q T k y)) =
                Q T (k + m) (R T (k + m) (r + 2 ^ m * Q T k y)) % 2 ^ m :=
        (Q_mod_compat_le T (Nat.le_add_left m k) _).symm
      rw [h1, hT.Q_R_cancel, Nat.mod_eq_of_lt hsum_lt, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hr]
  · intro x hx hiter
    refine ⟨Q_lt T m x, ?_⟩
    have hQeq : Q T (k + m) x = Q T m x + 2 ^ m * Q T k y := by
      have h1 := Q_mod_compat_le T (Nat.le_add_left m k) x
      have h2 : Q T (k + m) x / 2 ^ m = Q T k y := by
        rw [← Q_iter_conj_shift, hT.Q_congr k (iter T m x) y (by rw [hiter, Nat.mod_eq_of_lt hy])]
      have hdm := Nat.div_add_mod (Q T (k + m) x) (2 ^ m)
      rw [h1, h2] at hdm
      omega
    rw [← hQeq, hT.R_Q_cancel, Nat.mod_eq_of_lt hx]

/--
  **Theorem 6 (Bijective 2-Adic Piecewise-Affine Lift):**
  Every `ShiftFaithful` map `T` lifts to a 1-Lipschitz 2-adic isometry
  `bijectiveLift T x = (x % 2) + 2 * T x` which is an exact bijection on `Z / 2^k Z`
  for ALL `k >= 1`, with explicit inverse via `R T`.
-/
theorem ShiftFaithful.bijectiveLift_isometry {T : Nat → Nat} (hT : ShiftFaithful T) :
    (∀ k x y, x % 2 ^ k = y % 2 ^ k → bijectiveLift T x % 2 ^ k = bijectiveLift T y % 2 ^ k) ∧
    (∀ k x y, bijectiveLift T x % 2 ^ k = bijectiveLift T y % 2 ^ k → x % 2 ^ k = y % 2 ^ k) ∧
    (∀ k y, y < 2 ^ k → ∃ x, x < 2 ^ k ∧ bijectiveLift T x % 2 ^ k = y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k x y hxy
    cases k with
    | zero => simp [Nat.mod_one]
    | succ k =>
      simp only [bijectiveLift]
      have h0 : x % 2 = y % 2 := by
        simpa using mod_pow2_of_le (j := 1) (k := k + 1) (by omega) hxy
      have h1 : T x % 2 ^ k = T y % 2 ^ k := hT.causal k x y hxy
      rw [mod_pow2_succ_eq, mod_pow2_succ_eq]
      have hxm : (x % 2 + 2 * T x) % 2 = x % 2 := by omega
      have hym : (y % 2 + 2 * T y) % 2 = y % 2 := by omega
      have hxd : (x % 2 + 2 * T x) / 2 = T x := by
        have : x % 2 < 2 := Nat.mod_lt x (by omega); omega
      have hyd : (y % 2 + 2 * T y) / 2 = T y := by
        have : y % 2 < 2 := Nat.mod_lt y (by omega); omega
      rw [hxm, hym, hxd, hyd, h0, h1]
  · intro k x y hxy
    cases k with
    | zero => simp [Nat.mod_one]
    | succ k =>
      simp only [bijectiveLift] at hxy
      have h0 : x % 2 = y % 2 := by
        have hm := mod_pow2_of_le (j := 1) (k := k + 1) (by omega) hxy
        simp only [Nat.pow_one] at hm; omega
      have h1 : T x % 2 ^ k = T y % 2 ^ k := by
        have hd := congrArg (· / 2) hxy
        rw [← div2_mod_pow2, ← div2_mod_pow2] at hd
        have hxd : (x % 2 + 2 * T x) / 2 = T x := by
          have : x % 2 < 2 := Nat.mod_lt x (by omega); omega
        have hyd : (y % 2 + 2 * T y) / 2 = T y := by
          have : y % 2 < 2 := Nat.mod_lt y (by omega); omega
        rwa [hxd, hyd] at hd
      have hQ : Q T (k + 1) x = Q T (k + 1) y := by
        simp only [Q, h0, hT.Q_congr k (T x) (T y) h1]
      exact hT.Q_inj_mod (k + 1) x y hQ
  · intro k y hy
    cases k with
    | zero => exact ⟨0, by omega, by omega⟩
    | succ k =>
      let y0 := y % 2
      let yhi := y / 2
      have hyhi : yhi < 2 ^ k := by
        rw [Nat.pow_succ] at hy; omega
      let x := R T (k + 1) (y0 + 2 * Q T k yhi)
      refine ⟨x, R_lt T (k + 1) _, ?_⟩
      have hsum_lt : y0 + 2 * Q T k yhi < 2 ^ (k + 1) := by
        have := Q_lt T k yhi
        have : y0 < 2 := Nat.mod_lt y (by omega)
        rw [Nat.pow_succ]; omega
      have hqx : Q T (k + 1) x = y0 + 2 * Q T k yhi := by
        rw [hT.Q_R_cancel, Nat.mod_eq_of_lt hsum_lt]
      have hx0 : x % 2 = y0 := by
        have := congrArg (· % 2) hqx
        simp only [Q] at this; omega
      have hTx : T x % 2 ^ k = yhi := by
        have hqt : Q T k (T x) = Q T k yhi := by
          rw [Q_conj_shift, hqx]
          have : y0 < 2 := Nat.mod_lt y (by omega); omega
        have hinj := hT.Q_inj_mod k (T x) yhi hqt
        rwa [Nat.mod_eq_of_lt hyhi] at hinj
      simp only [bijectiveLift]
      rw [mod_pow2_succ_eq]
      have hxm : (x % 2 + 2 * T x) % 2 = x % 2 := by omega
      have hxd : (x % 2 + 2 * T x) / 2 = T x := by
        have : x % 2 < 2 := Nat.mod_lt x (by omega); omega
      rw [hxm, hxd, hx0, hTx]
      omega

/-- **Theorem 7 (Universal Mutual Conjugacy `Phi` Between ANY Two `ShiftFaithful` Maps):** -/
theorem Phi_inv {T1 T2 : Nat → Nat} (h1 : ShiftFaithful T1) (h2 : ShiftFaithful T2)
    (k x : Nat) : Phi T2 T1 k (Phi T1 T2 k x) = x % 2 ^ k := by
  simp only [Phi]
  rw [h2.Q_R_cancel, Nat.mod_eq_of_lt (Q_lt T1 k x), h1.R_Q_cancel]

theorem Phi_compat {T1 T2 : Nat → Nat} (k x : Nat) :
    Phi T1 T2 (k + 1) x % 2 ^ k = Phi T1 T2 k x := by
  simp only [Phi]
  rw [R_mod_compat, R_congr T2 k (Q T1 (k + 1) x) (Q T1 k x)
    (by rw [Q_mod_compat, Nat.mod_eq_of_lt (Q_lt T1 k x)])]

theorem Phi_conj {T1 T2 : Nat → Nat} (h2 : ShiftFaithful T2)
    (k x : Nat) : Phi T1 T2 k (T1 x) = T2 (Phi T1 T2 (k + 1) x) % 2 ^ k := by
  simp only [Phi]
  have hQ : Q T2 k (T2 (R T2 (k + 1) (Q T1 (k + 1) x))) = Q T1 k (T1 x) := by
    rw [Q_conj_shift, h2.Q_R_cancel, Nat.mod_eq_of_lt (Q_lt T1 (k + 1) x), Q_conj_shift]
  rw [← hQ, h2.R_Q_cancel]

theorem Phi_iter_conj {T1 T2 : Nat → Nat} (h2 : ShiftFaithful T2)
    (m k x : Nat) : Phi T1 T2 k (iter T1 m x) = iter T2 m (Phi T1 T2 (k + m) x) % 2 ^ k := by
  simp only [Phi]
  have hQ : Q T2 k (iter T2 m (R T2 (k + m) (Q T1 (k + m) x))) = Q T1 k (iter T1 m x) := by
    rw [Q_iter_conj_shift, h2.Q_R_cancel, Nat.mod_eq_of_lt (Q_lt T1 (k + m) x), Q_iter_conj_shift]
  rw [← hQ, h2.R_Q_cancel]

-- Exact Syracuse valuation preservation & conjugacy

theorem iter_even_halve {T : Nat → Nat} (hEven : ∀ n, T (2 * n) = n) :
    ∀ s y, 2 ^ s ∣ y → iter T s y = y / 2 ^ s := by
  intro s
  induction s with
  | zero => intro y _; simp [iter]
  | succ s ih =>
    intro y hdvd
    rcases hdvd with ⟨q, rfl⟩
    have h2 : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ s) 2, Nat.mul_assoc]
    simp only [iter]
    rw [h2, hEven, ih (2 ^ s * q) (Nat.dvd_mul_right _ _)]
    have hdiv : (2 * (2 ^ s * q)) / 2 ^ (s + 1) = (2 ^ s * q) / 2 ^ s := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ s) 2, Nat.mul_div_mul_left _ _ (by omega)]
    rw [hdiv]

theorem Q_zero_iff_dvd {T : Nat → Nat} (hEven : ∀ n, T (2 * n) = n) :
    ∀ s y, Q T s y = 0 ↔ 2 ^ s ∣ y := by
  intro s
  induction s with
  | zero => intro y; simp [Q]
  | succ s ih =>
    intro y
    simp only [Q]
    constructor
    · intro h
      have h0 : y % 2 = 0 := by omega
      have hq : Q T s (T y) = 0 := by omega
      have hy2 : y = 2 * (y / 2) := by omega
      rw [hy2, hEven] at hq
      rcases (ih (y / 2)).mp hq with ⟨q, hqeq⟩
      refine ⟨q, ?_⟩
      rw [hy2, hqeq, Nat.pow_succ, Nat.mul_comm (2 ^ s) 2, Nat.mul_assoc]
    · rintro ⟨q, rfl⟩
      have h2 : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ s) 2, Nat.mul_assoc]
      rw [h2, hEven]
      have h0 : (2 * (2 ^ s * q)) % 2 = 0 := by omega
      rw [h0, (ih (2 ^ s * q)).mpr (Nat.dvd_mul_right _ _)]

/-- **Theorem 8 (Exact Syracuse 2-Adic Valuation Preservation & Conjugacy):** -/
theorem Syracuse_conjugacy {T1 T2 : Nat → Nat}
    (h2 : ShiftFaithful T2)
    (hE1 : ∀ n, T1 (2 * n) = n) (hE2 : ∀ n, T2 (2 * n) = n)
    (x v k : Nat) (hk : v + 2 ≤ k)
    (hdvd : 2 ^ v ∣ T1 x) (hndvd : ¬ 2 ^ (v + 1) ∣ T1 x) :
    let y := Phi T1 T2 k x
    (2 ^ v ∣ T2 y) ∧ (¬ 2 ^ (v + 1) ∣ T2 y) ∧
    Phi T1 T2 (k - 1 - v) (T1 x / 2 ^ v) = (T2 y / 2 ^ v) % 2 ^ (k - 1 - v) := by
  intro y
  have hk1 : k - 1 + 1 = k := by omega
  have hq_eq : Q T2 (k - 1) (T2 y) = Q T1 (k - 1) (T1 x) := by
    calc Q T2 (k - 1) (T2 y)
        = Q T2 (k - 1 + 1) y / 2 := Q_conj_shift T2 (k - 1) y
      _ = Q T2 k y / 2 := by rw [hk1]
      _ = Q T1 k x / 2 := by
          simp only [y, Phi]
          rw [h2.Q_R_cancel, Nat.mod_eq_of_lt (Q_lt T1 k x)]
      _ = Q T1 (k - 1 + 1) x / 2 := by rw [hk1]
      _ = Q T1 (k - 1) (T1 x) := (Q_conj_shift T1 (k - 1) x).symm
  have hqv : Q T2 v (T2 y) = Q T1 v (T1 x) := by
    have hle : v ≤ k - 1 := by omega
    rw [← Q_mod_compat_le T2 hle, ← Q_mod_compat_le T1 hle, hq_eq]
  have hqv1 : Q T2 (v + 1) (T2 y) = Q T1 (v + 1) (T1 x) := by
    have hle : v + 1 ≤ k - 1 := by omega
    rw [← Q_mod_compat_le T2 hle, ← Q_mod_compat_le T1 hle, hq_eq]
  have hdvd2 : 2 ^ v ∣ T2 y := by
    rw [← Q_zero_iff_dvd hE2, hqv, (Q_zero_iff_dvd hE1 v (T1 x)).mpr hdvd]
  have hndvd2 : ¬ 2 ^ (v + 1) ∣ T2 y := by
    intro h
    apply hndvd
    rw [← Q_zero_iff_dvd hE1, ← hqv1, (Q_zero_iff_dvd hE2 (v + 1) (T2 y)).mpr h]
  refine ⟨hdvd2, hndvd2, ?_⟩
  have hstep1 : iter T1 (v + 1) x = T1 x / 2 ^ v := by
    have : iter T1 (v + 1) x = iter T1 v (T1 x) := by
      rw [Nat.add_comm]; exact iter_add T1 1 v x
    rw [this, iter_even_halve hE1 v (T1 x) hdvd]
  have hstep2 : iter T2 (v + 1) y = T2 y / 2 ^ v := by
    have : iter T2 (v + 1) y = iter T2 v (T2 y) := by
      rw [Nat.add_comm]; exact iter_add T2 1 v y
    rw [this, iter_even_halve hE2 v (T2 y) hdvd2]
  have hkm : (k - 1 - v) + (v + 1) = k := by omega
  have hconj := Phi_iter_conj (T1 := T1) h2 (v + 1) (k - 1 - v) x
  rw [hkm, hstep1] at hconj
  simpa [y, hstep2] using hconj

-- Universal 2-adic Periodic-Orbit Classification

theorem repWord_lt (p w k : Nat) : repWord p w k < 2 ^ k := by
  induction k with
  | zero => simp [repWord]
  | succ k ih =>
    simp only [repWord]
    have hb : (w / 2 ^ (k % p)) % 2 ≤ 1 := by omega
    rw [Nat.pow_succ]
    have : ((w / 2 ^ (k % p)) % 2) * 2 ^ k ≤ 2 ^ k := by
      calc ((w / 2 ^ (k % p)) % 2) * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ hb
        _ = 2 ^ k := Nat.one_mul _
    omega

theorem repWord_bit (p w k j : Nat) (hjk : j < k) :
    (repWord p w k).testBit j = decide ((w / 2 ^ (j % p)) % 2 = 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [repWord]
    have hlt := repWord_lt p w k
    by_cases hj : j < k
    · have hmod : (repWord p w k + ((w / 2 ^ (k % p)) % 2) * 2 ^ k) % 2 ^ k =
                  repWord p w k % 2 ^ k := by
        rw [Nat.add_mul_mod_self_right]
      rw [(mod_two_pow_eq_iff _ _ _).mp hmod j hj]
      exact ih hj
    · have hjeq : j = k := by omega
      subst hjeq
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (repWord p w j + ((w / 2 ^ (j % p)) % 2) * 2 ^ j) / 2 ^ j =
                  (w / 2 ^ (j % p)) % 2 := by
        rw [Nat.add_mul_div_right _ _ (pow2_pos j), Nat.div_eq_of_lt hlt, Nat.zero_add]
      rw [hdiv, Nat.mod_mod]

theorem repWord_shift (p w k : Nat) :
    repWord p w (k + p) / 2 ^ p = repWord p w k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_div_two_pow]
  by_cases hj : j < k
  · rw [repWord_bit p w (k + p) (j + p) (by omega), repWord_bit p w k j hj, Nat.add_mod_right]
  · have h1 : (repWord p w (k + p)).testBit (j + p) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (repWord_lt p w (k + p))
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : (repWord p w k).testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (repWord_lt p w k)
        (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, h2]

theorem repWord_mod_compat (p w k : Nat) :
    repWord p w (k + 1) % 2 ^ k = repWord p w k := by
  simp only [repWord]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (repWord_lt p w k)]

theorem repWord_self (p w : Nat) (hw : w < 2 ^ p) :
    repWord p w p = w := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < p
  · rw [repWord_bit p w p j hj, Nat.mod_eq_of_lt hj, Nat.testBit_eq_decide_div_mod_eq]
  · have h1 : (repWord p w p).testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (repWord_lt p w p)
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : w.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, h2]

/-- **Theorem 9 (Universal 2-Adic Periodic-Orbit Classification):** -/
theorem ShiftFaithful.periodic_orbit_classification {T : Nat → Nat} (hT : ShiftFaithful T)
    (p : Nat) (hp : 1 ≤ p) :
    (∀ w, w < 2 ^ p →
      (∀ k, perOrbit T p w k < 2 ^ k) ∧
      (∀ k, perOrbit T p w (k + 1) % 2 ^ k = perOrbit T p w k) ∧
      (∀ k, iter T p (perOrbit T p w (k + p)) % 2 ^ k = perOrbit T p w k) ∧
      Q T p (perOrbit T p w p) = w) ∧
    (∀ z : Nat → Nat,
      (∀ k, z k < 2 ^ k) →
      (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, iter T p (z (k + p)) % 2 ^ k = z k) →
      ∀ k, z k = perOrbit T p (Q T p (z p)) k) := by
  constructor
  · intro w hw
    refine ⟨fun k => R_lt T k _, ?_, ?_, ?_⟩
    · intro k
      simp only [perOrbit]
      rw [R_mod_compat]
      exact R_congr T k (repWord p w (k + 1)) (repWord p w k)
        (by rw [repWord_mod_compat, Nat.mod_eq_of_lt (repWord_lt p w k)])
    · intro k
      simp only [perOrbit]
      have hQ : Q T k (iter T p (R T (k + p) (repWord p w (k + p)))) = repWord p w k := by
        rw [Q_iter_conj_shift, hT.Q_R_cancel, Nat.mod_eq_of_lt (repWord_lt p w (k + p)),
            repWord_shift p w k]
      have hR := congrArg (R T k) hQ
      rwa [hT.R_Q_cancel] at hR
    · simp only [perOrbit]
      rw [hT.Q_R_cancel, repWord_self p w hw, Nat.mod_eq_of_lt hw]
  · intro z hzlt hzcompat hzper
    let w := Q T p (z p)
    have hcompat_le : ∀ a b, a ≤ b → z b % 2 ^ a = z a := by
      intro a b hab
      induction b with
      | zero =>
        have ha0 : a = 0 := by omega
        subst ha0; exact Nat.mod_eq_of_lt (hzlt 0)
      | succ m ih =>
        by_cases ham : a ≤ m
        · have hm : z (m + 1) % 2 ^ m = z m % 2 ^ m := by
            rw [hzcompat m, Nat.mod_eq_of_lt (hzlt m)]
          have h1 := mod_pow2_of_le ham hm
          rw [h1, ih ham]
        · have haeq : a = m + 1 := by omega
          subst haeq; exact Nat.mod_eq_of_lt (hzlt (m + 1))
    have hQrep : ∀ k, Q T k (z k) = repWord p w k := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        by_cases hkp : k ≤ p
        · have h1 : Q T k (z k) = Q T p (z p) % 2 ^ k := by
            rw [Q_mod_compat_le T hkp (z p),
                hT.Q_congr k (z k) (z p) (by rw [Nat.mod_eq_of_lt (hzlt k), hcompat_le k p hkp])]
          have h2 : repWord p w k = w % 2 ^ k := by
            apply Nat.eq_of_testBit_eq
            intro j
            by_cases hj : j < k
            · rw [repWord_bit p w k j hj, Nat.testBit_mod_two_pow]
              simp only [hj, decide_true, Bool.true_and, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj hkp),
                         Nat.testBit_eq_decide_div_mod_eq]
            · rw [Nat.testBit_mod_two_pow]
              simp only [hj, decide_false, Bool.false_and]
              exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (repWord_lt p w k)
                (Nat.pow_le_pow_right (by omega) (by omega)))
          rw [h1, h2]
        · let m := k - p
          have hlt : m < k := by omega
          have hsub : m + p = k := by omega
          have hih := ih m hlt
          have hlo : Q T k (z k) % 2 ^ p = w := by
            rw [Q_mod_compat_le T (by omega) (z k)]
            exact hT.Q_congr p (z k) (z p)
              (by rw [hcompat_le p k (by omega), Nat.mod_eq_of_lt (hzlt p)])
          have hhi : Q T k (z k) / 2 ^ p = repWord p w m := by
            calc Q T k (z k) / 2 ^ p
                = Q T (m + p) (z (m + p)) / 2 ^ p := by rw [hsub]
              _ = Q T m (iter T p (z (m + p))) := (Q_iter_conj_shift T p m (z (m + p))).symm
              _ = Q T m (z m) := hT.Q_congr m _ _ (by rw [hzper m, Nat.mod_eq_of_lt (hzlt m)])
              _ = repWord p w m := hih
          have hrepl : repWord p w k % 2 ^ p = w := by
            have h1 : repWord p w k % 2 ^ p = repWord p w p := by
              apply Nat.eq_of_testBit_eq
              intro j
              rw [Nat.testBit_mod_two_pow]
              by_cases hj : j < p
              · simp only [hj, decide_true, Bool.true_and]
                rw [repWord_bit p w k j (by omega), repWord_bit p w p j hj]
              · simp only [hj, decide_false, Bool.false_and]
                exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (repWord_lt p w p)
                  (Nat.pow_le_pow_right (by omega) (by omega)))).symm
            rw [h1, repWord_self p w (Q_lt T p (z p))]
          have hreph : repWord p w k / 2 ^ p = repWord p w m := by
            calc repWord p w k / 2 ^ p
                = repWord p w (m + p) / 2 ^ p := by rw [hsub]
              _ = repWord p w m := repWord_shift p w m
          have hdm1 := Nat.div_add_mod (Q T k (z k)) (2 ^ p)
          have hdm2 := Nat.div_add_mod (repWord p w k) (2 ^ p)
          rw [hlo, hhi] at hdm1
          rw [hrepl, hreph] at hdm2
          omega
    intro k
    change z k = R T k (repWord p w k)
    rw [← hQrep k, hT.R_Q_cancel, Nat.mod_eq_of_lt (hzlt k)]

/-- Evaluate a `2^r`-branch carryless piecewise-affine map `T(x) = (clmul p_i x ^^^ q_i) / 2`. -/
def evalClTable (r : Nat) (tab : Nat → Nat × Nat) (x : Nat) : Nat :=
  let (p, q) := tab (x % 2 ^ r)
  (clmul p x ^^^ q) / 2

theorem allLt_eq_true_iff (n : Nat) (f : Nat → Bool) :
    allLt n f = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => simp [allLt]
  | succ m ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases him : i < m
      · exact h1 i him
      · have : i = m := by omega
        subst this; exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h m (Nat.lt_succ_self m)⟩

/-- Finite Boolean Ultrametric Gluing Certifier for ANY `2^r`-branch carryless table (`r >= 1`). -/
def checkClTable (r : Nat) (tab : Nat → Nat × Nat) : Bool :=
  let N := 2 ^ r
  let T := evalClTable r tab
  allLt N (fun i => decide ((tab i).1 % 2 = 1)) &&
  allLt r (fun k =>
    if k = 0 then true
    else allLt N (fun i =>
      decide (T i % 2 ^ k = T (i % 2 ^ (k + 1)) % 2 ^ k) &&
      decide (T (i ^^^ (1 <<< k)) % 2 ^ k = (T i + 2 ^ (k - 1)) % 2 ^ k)))

theorem evalAffTable_decomp (r : Nat) (hr : 1 ≤ r) (tab : Nat → Nat × Nat) (x : Nat) :
    evalAffTable r tab x =
      evalAffTable r tab (x % 2 ^ r) + (tab (x % 2 ^ r)).1 * 2 ^ (r - 1) * (x / 2 ^ r) := by
  simp only [evalAffTable]
  rw [Nat.mod_mod]
  have h2r : 2 ^ r = 2 * 2 ^ (r - 1) := pow2_split r hr
  have hx : x = x % 2 ^ r + 2 ^ r * (x / 2 ^ r) := by
    have := Nat.div_add_mod x (2 ^ r); omega
  generalize tab (x % 2 ^ r) = ab
  rcases ab with ⟨a, b⟩
  dsimp only
  have heq : a * x + b = (a * (x % 2 ^ r) + b) + 2 * (a * 2 ^ (r - 1) * (x / 2 ^ r)) := by
    calc a * x + b
        = a * (x % 2 ^ r + 2 ^ r * (x / 2 ^ r)) + b := by rw [← hx]
      _ = a * (x % 2 ^ r) + a * (2 * 2 ^ (r - 1) * (x / 2 ^ r)) + b := by rw [Nat.mul_add, h2r]
      _ = (a * (x % 2 ^ r) + b) + a * (2 * 2 ^ (r - 1) * (x / 2 ^ r)) := by omega
      _ = (a * (x % 2 ^ r) + b) + 2 * (a * 2 ^ (r - 1) * (x / 2 ^ r)) := by
          congr 1
          calc a * (2 * 2 ^ (r - 1) * (x / 2 ^ r))
              = a * (2 * (2 ^ (r - 1) * (x / 2 ^ r))) := by rw [Nat.mul_assoc]
            _ = 2 * (a * (2 ^ (r - 1) * (x / 2 ^ r))) := by rw [Nat.mul_left_comm]
            _ = 2 * (a * 2 ^ (r - 1) * (x / 2 ^ r)) := by rw [Nat.mul_assoc]
  rw [heq, Nat.add_mul_div_left _ _ (by omega)]

/--
  **Theorem 10 (Exact Finite-to-Infinite Ultrametric Gluing Characterization — Carried Tables):**
  For EVERY `r >= 1` and EVERY `2^r`-branch carried table `tab`:
    `checkAffTable r tab = true ↔ ShiftFaithful (evalAffTable r tab)`.
-/
theorem checkAffTable_iff_shiftFaithful (r : Nat) (hr : 1 ≤ r) (tab : Nat → Nat × Nat) :
    checkAffTable r tab = true ↔ ShiftFaithful (evalAffTable r tab) := by
  have hmod_low : ∀ k x, k < r → evalAffTable r tab x % 2 ^ k = evalAffTable r tab (x % 2 ^ r) % 2 ^ k := by
    intro k x hkr
    have hd := evalAffTable_decomp r hr tab x
    have hdiv : 2 ^ k ∣ 2 ^ (r - 1) := Nat.pow_dvd_pow 2 (by omega)
    rcases hdiv with ⟨c, hc⟩
    have heq : evalAffTable r tab x =
               evalAffTable r tab (x % 2 ^ r) + 2 ^ k * ((tab (x % 2 ^ r)).1 * c * (x / 2 ^ r)) := by
      rw [hd, hc]
      congr 1
      calc (tab (x % 2 ^ r)).1 * (2 ^ k * c) * (x / 2 ^ r)
          = 2 ^ k * ((tab (x % 2 ^ r)).1 * c) * (x / 2 ^ r) := by rw [Nat.mul_left_comm]
        _ = 2 ^ k * ((tab (x % 2 ^ r)).1 * c * (x / 2 ^ r)) := by rw [Nat.mul_assoc]
    rw [heq, Nat.add_mul_mod_self_left]
  constructor
  · intro hchk
    simp only [checkAffTable, Bool.and_eq_true, allLt_eq_true_iff] at hchk
    rcases hchk with ⟨hodd, hglue⟩
    have hcausal : ∀ k x y, x % 2 ^ (k + 1) = y % 2 ^ (k + 1) →
        evalAffTable r tab x % 2 ^ k = evalAffTable r tab y % 2 ^ k := by
      intro k x y hxy
      by_cases hk0 : k = 0
      · subst hk0; simp [Nat.mod_one]
      · by_cases hkr : k < r
        · have hgx := hglue k hkr
          simp only [hk0, ↓reduceIte, allLt_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq] at hgx
          have hx1 := (hgx (x % 2 ^ r) (Nat.mod_lt x (pow2_pos r))).1
          have hy1 := (hgx (y % 2 ^ r) (Nat.mod_lt y (pow2_pos r))).1
          have hrx : (x % 2 ^ r) % 2 ^ (k + 1) = x % 2 ^ (k + 1) :=
            Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (by omega))
          have hry : (y % 2 ^ r) % 2 ^ (k + 1) = y % 2 ^ (k + 1) :=
            Nat.mod_mod_of_dvd y (Nat.pow_dvd_pow 2 (by omega))
          rw [hmod_low k x hkr, hmod_low k y hkr, hx1, hy1, hrx, hry, hxy]
        · have hxr : x % 2 ^ r = y % 2 ^ r := mod_pow2_of_le (by omega) hxy
          simp only [evalAffTable]
          rw [hxr]
          generalize tab (y % 2 ^ r) = ab
          rcases ab with ⟨a, b⟩
          dsimp only
          rw [div2_mod_pow2, div2_mod_pow2]
          congr 1
          rw [Nat.add_mod, Nat.mul_mod, hxy, ← Nat.mul_mod, ← Nat.add_mod]
    refine ⟨hcausal, ?_⟩
    intro k x hk1
    by_cases hkr : k < r
    · have hk0 : k ≠ 0 := by omega
      have hgx := hglue k hkr
      simp only [hk0, ↓reduceIte, allLt_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq] at hgx
      let i := x % 2 ^ r
      have hi : i < 2 ^ r := Nat.mod_lt x (pow2_pos r)
      have hflip_i := (hgx i hi).2
      have hmod_eq : (x + 2 ^ k) % 2 ^ (k + 1) = (i ^^^ (1 <<< k)) % 2 ^ (k + 1) := by
        rw [add_pow2_mod_pow2_succ_eq_xor, mod_two_pow_eq_iff]
        intro j hj
        simp only [Nat.testBit_xor]
        congr 1
        have hxi : i % 2 ^ (k + 1) = x % 2 ^ (k + 1) :=
          Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (by omega))
        exact ((mod_two_pow_eq_iff i x (k + 1)).mp hxi j hj).symm
      rw [hcausal k (x + 2 ^ k) (i ^^^ (1 <<< k)) hmod_eq, hflip_i]
      have hlow := hmod_low k x hkr
      rw [Nat.add_mod, ← hlow, ← Nat.add_mod]
    · have hge : r ≤ k := by omega
      have hxr : (x + 2 ^ k) % 2 ^ r = x % 2 ^ r := by
        rcases Nat.pow_dvd_pow 2 hge with ⟨c, hc⟩
        rw [hc, Nat.add_mul_mod_self_left]
      have ha_odd : (tab (x % 2 ^ r)).1 % 2 = 1 :=
        decide_eq_true_eq.mp (hodd (x % 2 ^ r) (Nat.mod_lt x (pow2_pos r)))
      simp only [evalAffTable]
      rw [hxr]
      generalize hpair : tab (x % 2 ^ r) = ab
      rw [hpair] at ha_odd
      rcases ab with ⟨a, b⟩
      dsimp only at ha_odd ⊢
      have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := pow2_split k hk1
      have heq : (a * (x + 2 ^ k) + b) / 2 = (a * x + b) / 2 + a * 2 ^ (k - 1) := by
        have hnum : a * (x + 2 ^ k) + b = (a * x + b) + 2 * (a * 2 ^ (k - 1)) := by
          rw [Nat.mul_add, h2k]
          calc a * x + a * (2 * 2 ^ (k - 1)) + b
              = (a * x + b) + a * (2 * 2 ^ (k - 1)) := by omega
            _ = (a * x + b) + 2 * (a * 2 ^ (k - 1)) := by rw [Nat.mul_left_comm]
        rw [hnum, Nat.add_mul_div_left _ _ (by omega)]
      rw [heq]
      have ha_split : a = 2 * (a / 2) + 1 := by omega
      have hmul : a * 2 ^ (k - 1) = 2 ^ k * (a / 2) + 2 ^ (k - 1) := by
        calc a * 2 ^ (k - 1)
            = (2 * (a / 2) + 1) * 2 ^ (k - 1) := by rw [← ha_split]
          _ = 2 * (a / 2) * 2 ^ (k - 1) + 2 ^ (k - 1) := by rw [Nat.add_mul, Nat.one_mul]
          _ = 2 ^ k * (a / 2) + 2 ^ (k - 1) := by
              congr 1
              rw [h2k, Nat.mul_assoc, Nat.mul_comm (a / 2) (2 ^ (k - 1)), ← Nat.mul_assoc]
      rw [hmul, ← Nat.add_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
  · intro hSF
    simp only [checkAffTable, Bool.and_eq_true, allLt_eq_true_iff]
    constructor
    · intro i hi
      simp only [decide_eq_true_eq]
      have hfl := hSF.flip r i hr
      have hxr : (i + 2 ^ r) % 2 ^ r = i := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      have hd := evalAffTable_decomp r hr tab (i + 2 ^ r)
      have hdiv : (i + 2 ^ r) / 2 ^ r = 1 := by
        rw [Nat.add_div_right _ (pow2_pos r), Nat.div_eq_of_lt hi]
      rw [hxr, hdiv, Nat.mul_one] at hd
      rw [hd] at hfl
      have h2r : 2 ^ r = 2 * 2 ^ (r - 1) := pow2_split r hr
      rcases Nat.mod_two_eq_zero_or_one (tab i).1 with hev | hodd
      · exfalso
        have hmul : (tab i).1 * 2 ^ (r - 1) = 2 ^ r * ((tab i).1 / 2) := by
          have ha_sp : (tab i).1 = 2 * ((tab i).1 / 2) := by omega
          calc (tab i).1 * 2 ^ (r - 1)
              = 2 * ((tab i).1 / 2) * 2 ^ (r - 1) := by rw [← ha_sp]
            _ = 2 ^ r * ((tab i).1 / 2) := by
                rw [h2r, Nat.mul_assoc, Nat.mul_comm ((tab i).1 / 2) (2 ^ (r - 1)), ← Nat.mul_assoc]
        rw [hmul, Nat.add_mul_mod_self_left] at hfl
        -- Compare bit (r - 1) of both sides: contradiction!
        have hb := (mod_two_pow_eq_iff _ _ r).mp hfl (r - 1) (by omega)
        rw [testBit_add_pow2_eq] at hb
        cases h0 : (evalAffTable r tab i).testBit (r - 1) <;> simp [h0] at hb
      · exact hodd
    · intro k hkr
      by_cases hk0 : k = 0
      · simp [hk0]
      · simp only [hk0, ↓reduceIte, allLt_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq]
        intro i _
        constructor
        · exact hSF.causal k i (i % 2 ^ (k + 1)) (by rw [Nat.mod_mod])
        · have h1 := hSF.causal k (i ^^^ (1 <<< k)) (i + 2 ^ k)
            (add_pow2_mod_pow2_succ_eq_xor i k).symm
          rw [h1]
          exact hSF.flip k i (by omega)

-- Carryless `2^r`-branch table exact decomposition & IFF certifier

theorem evalClTable_decomp (r : Nat) (hr : 1 ≤ r) (tab : Nat → Nat × Nat) (x : Nat) :
    evalClTable r tab x =
      evalClTable r tab (x % 2 ^ r) ^^^ (clmul (tab (x % 2 ^ r)).1 (x / 2 ^ r) <<< (r - 1)) := by
  simp only [evalClTable]
  rw [Nat.mod_mod]
  have hx : x = (x % 2 ^ r) ^^^ ((x / 2 ^ r) <<< r) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases hj : j < r
    · have hnot : ¬(r ≤ j) := by omega
      simp [hj, hnot]
    · have hle : r ≤ j := by omega
      simp only [hj, decide_false, Bool.false_and, Bool.false_xor, hle, decide_true, Bool.true_and]
      rw [Nat.testBit_div_two_pow]
      have : j - r + r = j := by omega
      rw [this]
  generalize tab (x % 2 ^ r) = pq
  rcases pq with ⟨p, q⟩
  dsimp only
  have hcl : clmul p x = clmul p (x % 2 ^ r) ^^^ (clmul p (x / 2 ^ r) <<< r) := by
    calc clmul p x
        = clmul p ((x % 2 ^ r) ^^^ ((x / 2 ^ r) <<< r)) := by rw [← hx]
      _ = clmul p (x % 2 ^ r) ^^^ clmul p ((x / 2 ^ r) <<< r) := clmul_xor_right p _ _
      _ = clmul p (x % 2 ^ r) ^^^ (clmul p (x / 2 ^ r) <<< r) := by rw [clmul_shiftLeft_right]
  rw [hcl]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_div_two, testBit_div_two,
      Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  have h1 : (r ≤ j + 1) ↔ (r - 1 ≤ j) := by omega
  have h2 : j + 1 - r = j - (r - 1) := by omega
  have hsh : (decide (r ≤ j + 1) && (clmul p (x / 2 ^ r)).testBit (j + 1 - r)) =
             (decide (r - 1 ≤ j) && (clmul p (x / 2 ^ r)).testBit (j - (r - 1))) := by
    by_cases h : r - 1 ≤ j
    · simp [h, h1.mpr h, h2]
    · have h' : ¬(r ≤ j + 1) := fun hc => h (h1.mp hc)
      simp [h, h']
  rw [hsh]
  cases (clmul p (x % 2 ^ r)).testBit (j + 1) <;> cases q.testBit (j + 1) <;>
  cases (decide (r - 1 ≤ j) && (clmul p (x / 2 ^ r)).testBit (j - (r - 1))) <;> rfl

/--
  **Theorem 11 (Exact Finite-to-Infinite Ultrametric Gluing Characterization — Carryless Tables):**
  For EVERY `r >= 1` and EVERY `2^r`-branch carryless table `tab`:
    `checkClTable r tab = true ↔ ShiftFaithful (evalClTable r tab)`.
-/
theorem checkClTable_iff_shiftFaithful (r : Nat) (hr : 1 ≤ r) (tab : Nat → Nat × Nat) :
    checkClTable r tab = true ↔ ShiftFaithful (evalClTable r tab) := by
  have hmod_low : ∀ k x, k < r → evalClTable r tab x % 2 ^ k = evalClTable r tab (x % 2 ^ r) % 2 ^ k := by
    intro k x hkr
    rw [mod_two_pow_eq_iff]
    intro j hj
    rw [evalClTable_decomp r hr tab x, Nat.testBit_xor, Nat.testBit_shiftLeft]
    have hnot : ¬(r - 1 ≤ j) := by omega
    simp [hnot]
  constructor
  · intro hchk
    simp only [checkClTable, Bool.and_eq_true, allLt_eq_true_iff] at hchk
    rcases hchk with ⟨hodd, hglue⟩
    have hcausal : ∀ k x y, x % 2 ^ (k + 1) = y % 2 ^ (k + 1) →
        evalClTable r tab x % 2 ^ k = evalClTable r tab y % 2 ^ k := by
      intro k x y hxy
      by_cases hk0 : k = 0
      · subst hk0; simp [Nat.mod_one]
      · by_cases hkr : k < r
        · have hgx := hglue k hkr
          simp only [hk0, ↓reduceIte, allLt_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq] at hgx
          have hx1 := (hgx (x % 2 ^ r) (Nat.mod_lt x (pow2_pos r))).1
          have hy1 := (hgx (y % 2 ^ r) (Nat.mod_lt y (pow2_pos r))).1
          have hrx : (x % 2 ^ r) % 2 ^ (k + 1) = x % 2 ^ (k + 1) :=
            Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (by omega))
          have hry : (y % 2 ^ r) % 2 ^ (k + 1) = y % 2 ^ (k + 1) :=
            Nat.mod_mod_of_dvd y (Nat.pow_dvd_pow 2 (by omega))
          rw [hmod_low k x hkr, hmod_low k y hkr, hx1, hy1, hrx, hry, hxy]
        · have hxr : x % 2 ^ r = y % 2 ^ r := mod_pow2_of_le (by omega) hxy
          simp only [evalClTable]
          rw [hxr]
          generalize tab (y % 2 ^ r) = pq
          rcases pq with ⟨p, q⟩
          dsimp only
          rw [div2_mod_pow2, div2_mod_pow2]
          congr 1
          rw [xor_mod_pow2, xor_mod_pow2 (clmul p y),
              ← clmul_mod_pow2 p x (k + 1), hxy, clmul_mod_pow2 p y (k + 1)]
    refine ⟨hcausal, ?_⟩
    intro k x hk1
    by_cases hkr : k < r
    · have hk0 : k ≠ 0 := by omega
      have hgx := hglue k hkr
      simp only [hk0, ↓reduceIte, allLt_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq] at hgx
      let i := x % 2 ^ r
      have hi : i < 2 ^ r := Nat.mod_lt x (pow2_pos r)
      have hflip_i := (hgx i hi).2
      have hmod_eq : (x + 2 ^ k) % 2 ^ (k + 1) = (i ^^^ (1 <<< k)) % 2 ^ (k + 1) := by
        rw [add_pow2_mod_pow2_succ_eq_xor, mod_two_pow_eq_iff]
        intro j hj
        simp only [Nat.testBit_xor]
        congr 1
        have hxi : i % 2 ^ (k + 1) = x % 2 ^ (k + 1) :=
          Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (by omega))
        exact ((mod_two_pow_eq_iff i x (k + 1)).mp hxi j hj).symm
      rw [hcausal k (x + 2 ^ k) (i ^^^ (1 <<< k)) hmod_eq, hflip_i]
      have hlow := hmod_low k x hkr
      rw [Nat.add_mod, ← hlow, ← Nat.add_mod]
    · have hge : r ≤ k := by omega
      rw [hcausal k (x + 2 ^ k) (x ^^^ (1 <<< k)) (add_pow2_mod_pow2_succ_eq_xor x k)]
      have hxr : (x ^^^ (1 <<< k)) % 2 ^ r = x % 2 ^ r := by
        rw [mod_two_pow_eq_iff]
        intro j hj
        rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
        have hnot : ¬(k ≤ j) := by omega
        simp [hnot]
      have hp_odd : (tab (x % 2 ^ r)).1 % 2 = 1 :=
        decide_eq_true_eq.mp (hodd (x % 2 ^ r) (Nat.mod_lt x (pow2_pos r)))
      simp only [evalClTable]
      rw [hxr]
      generalize hpair : tab (x % 2 ^ r) = pq
      rw [hpair] at hp_odd
      rcases pq with ⟨p, q⟩
      dsimp only at hp_odd ⊢
      rw [clmul_xor_right, clmul_shiftLeft_right, clmul_one_right]
      rw [← xor_pow2_mod_pow2_eq_add _ k hk1]
      rw [mod_two_pow_eq_iff]
      intro j hj
      rw [testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
          testBit_div_two, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
      have hbit : (decide (k ≤ j + 1) && p.testBit (j + 1 - k)) =
                  (decide (k - 1 ≤ j) && (1 : Nat).testBit (j - (k - 1))) := by
        by_cases hjk : j = k - 1
        · subst hjk
          have h1 : k ≤ k - 1 + 1 := by omega
          have h2 : k - 1 + 1 - k = 0 := by omega
          have hp0 : p.testBit 0 = true := by rw [Nat.testBit_zero]; simp [hp_odd]
          simp [h1, h2, hp0]
        · have hnot1 : ¬(k ≤ j + 1) := by omega
          have hnot2 : ¬(k - 1 ≤ j) := by omega
          simp [hnot1, hnot2]
      rw [hbit]
      cases (clmul p x).testBit (j + 1) <;> cases q.testBit (j + 1) <;>
      cases (decide (k - 1 ≤ j) && (1 : Nat).testBit (j - (k - 1))) <;> rfl
  · intro hSF
    simp only [checkClTable, Bool.and_eq_true, allLt_eq_true_iff]
    constructor
    · intro i hi
      simp only [decide_eq_true_eq]
      have hfl := hSF.flip r i hr
      have hxr : (i + 2 ^ r) % 2 ^ r = i := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      have hd := evalClTable_decomp r hr tab (i + 2 ^ r)
      have hdiv : (i + 2 ^ r) / 2 ^ r = 1 := by
        rw [Nat.add_div_right _ (pow2_pos r), Nat.div_eq_of_lt hi]
      rw [hxr, hdiv, clmul_one_right] at hd
      rw [hd] at hfl
      have hbit := (mod_two_pow_eq_iff _ _ r).mp hfl (r - 1) (by omega)
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_add_pow2_eq] at hbit
      simp only [Nat.le_refl, decide_true, Bool.true_and, Nat.sub_self] at hbit
      have hp0 : (tab i).1.testBit 0 = true := by
        cases h0 : (evalClTable r tab i).testBit (r - 1) <;>
        cases hp : (tab i).1.testBit 0 <;> simp_all
      rw [Nat.testBit_zero] at hp0
      exact decide_eq_true_eq.mp hp0
    · intro k hkr
      by_cases hk0 : k = 0
      · simp [hk0]
      · simp only [hk0, ↓reduceIte, allLt_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq]
        intro i _
        constructor
        · exact hSF.causal k i (i % 2 ^ (k + 1)) (by rw [Nat.mod_mod])
        · have h1 := hSF.causal k (i ^^^ (1 <<< k)) (i + 2 ^ k)
            (add_pow2_mod_pow2_succ_eq_xor i k).symm
          rw [h1]
          exact hSF.flip k i (by omega)

theorem TCarried_eq_evalAffTable (a b x : Nat) :
    TCarried a b x = evalAffTable 1 (fun i => if i = 0 then (1, 0) else (a, b)) x := by
  simp only [TCarried, evalAffTable, Nat.pow_one]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem TCarryless_eq_evalClTable (p q x : Nat) :
    TCarryless p q x = evalClTable 1 (fun i => if i = 0 then (1, 0) else (p, q)) x := by
  simp only [TCarryless, evalClTable, Nat.pow_one]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, clmul_one_left]

/-- Every carried generalized Collatz map `TCarried a b` with odd `a` is `ShiftFaithful`. -/
theorem carriedCollatz_shiftFaithful (a b : Nat) (ha : a % 2 = 1) :
    ShiftFaithful (TCarried a b) := by
  have heq : TCarried a b = evalAffTable 1 (fun i => if i = 0 then (1, 0) else (a, b)) :=
    funext (TCarried_eq_evalAffTable a b)
  rw [heq, ← checkAffTable_iff_shiftFaithful 1 (by omega)]
  simp [checkAffTable, allLt, ha]

/-- Every carryless generalized Collatz map `TCarryless p q` with odd `p` is `ShiftFaithful`. -/
theorem carrylessCollatz_shiftFaithful (p q : Nat) (hp : p % 2 = 1) :
    ShiftFaithful (TCarryless p q) := by
  have heq : TCarryless p q = evalClTable 1 (fun i => if i = 0 then (1, 0) else (p, q)) :=
    funext (TCarryless_eq_evalClTable p q)
  rw [heq, ← checkClTable_iff_shiftFaithful 1 (by omega)]
  simp [checkClTable, allLt, hp]

theorem TCarried_even (a b n : Nat) : TCarried a b (2 * n) = n := by
  have h0 : 2 * n % 2 = 0 := by omega
  simp [TCarried, h0]

theorem TCarryless_even (p q n : Nat) : TCarryless p q (2 * n) = n := by
  have h0 : 2 * n % 2 = 0 := by omega
  simp [TCarryless, h0]

/--
  **Corollary (Carried Collatz `3x+1` and Carryless Collatz `3x ^ 1` are Constructively
  2-Adically Conjugate, Including Exact Syracuse `v_2` Preservation!):**
-/
theorem carried_carryless_3x1_syracuse_conjugate
    (x v k : Nat) (hk : v + 2 ≤ k)
    (hdvd : 2 ^ v ∣ TCarried 3 1 x) (hndvd : ¬ 2 ^ (v + 1) ∣ TCarried 3 1 x) :
    let y := Phi (TCarried 3 1) (TCarryless 3 1) k x
    (2 ^ v ∣ TCarryless 3 1 y) ∧ (¬ 2 ^ (v + 1) ∣ TCarryless 3 1 y) ∧
    Phi (TCarried 3 1) (TCarryless 3 1) (k - 1 - v) (TCarried 3 1 x / 2 ^ v) =
      (TCarryless 3 1 y / 2 ^ v) % 2 ^ (k - 1 - v) :=
  Syracuse_conjugacy
    (carrylessCollatz_shiftFaithful 3 1 rfl)
    (TCarried_even 3 1) (TCarryless_even 3 1) x v k hk hdvd hndvd

theorem countLt_eq_zero_iff (n : Nat) (P : Nat → Bool) :
    countLt n P = 0 ↔ ∀ x, x < n → P x = false := by
  induction n with
  | zero => simp [countLt]
  | succ m ih =>
    simp only [countLt]
    constructor
    · intro h x hx
      have h1 : countLt m P = 0 := by split at h <;> omega
      have h2 : P m = false := by
        cases hm : P m
        · rfl
        · simp [hm] at h
      by_cases hxm : x < m
      · exact ih.mp h1 x hxm
      · have : x = m := by omega
        subst this; exact h2
    · intro h
      have h1 := ih.mpr (fun x hx => h x (Nat.lt_succ_of_lt hx))
      have h2 := h m (Nat.lt_succ_self m)
      simp [h1, h2]

theorem countLt_all_true (n : Nat) (P : Nat → Bool) (h : ∀ x, x < n → P x = true) :
    countLt n P = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [countLt, h m (Nat.lt_succ_self m), ↓reduceIte]
    rw [ih (fun x hx => h x (Nat.lt_succ_of_lt hx))]

theorem countLt_congr (n : Nat) (P1 P2 : Nat → Bool) (h : ∀ x, x < n → P1 x = P2 x) :
    countLt n P1 = countLt n P2 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [countLt, h m (Nat.lt_succ_self m), ih (fun x hx => h x (Nat.lt_succ_of_lt hx))]

theorem countLt_even_odd_split (m : Nat) (P : Nat → Bool) :
    countLt (2 * m) P =
      countLt m (fun y => P (2 * y)) + countLt m (fun y => P (2 * y + 1)) := by
  induction m with
  | zero => simp [countLt]
  | succ m ih =>
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h2]
    simp only [countLt]
    rw [ih]
    omega

/-- Number of ODD `k`-bit self-coding residues `x < 2^k` with `x % 2 = 1` and `Q T k x = x`. -/
def oddFixedCount (T : Nat → Nat) (k : Nat) : Nat :=
  countLt (2 ^ k) (fun x => decide (x % 2 = 1) && decide (Q T k x = x))

theorem oddFixedCount_eq_half (T : Nat → Nat) (k : Nat) :
    oddFixedCount T (k + 1) =
      countLt (2 ^ k) (fun y => decide (Q T (k + 1) (2 * y + 1) = 2 * y + 1)) := by
  simp only [oddFixedCount]
  rw [Nat.pow_succ, Nat.mul_comm, countLt_even_odd_split]
  have hev : countLt (2 ^ k)
      (fun y => decide (2 * y % 2 = 1) && decide (Q T (k + 1) (2 * y) = 2 * y)) = 0 := by
    rw [countLt_eq_zero_iff]
    intro y _
    have : 2 * y % 2 = 0 := by omega
    simp [this]
  rw [hev, Nat.zero_add]
  apply countLt_congr
  intro y _
  have : (2 * y + 1) % 2 = 1 := by omega
  simp [this]

/-- Exact recurrence for even-halving maps: `fixedCount T (k + 1) = fixedCount T k + oddFixedCount T (k + 1)`. -/
theorem fixedCount_succ {T : Nat → Nat} (hEven : ∀ n, T (2 * n) = n) (k : Nat) :
    fixedCount T (k + 1) = fixedCount T k + oddFixedCount T (k + 1) := by
  simp only [fixedCount]
  rw [Nat.pow_succ, Nat.mul_comm, countLt_even_odd_split, oddFixedCount_eq_half]
  congr 1
  apply countLt_congr
  intro y _
  simp only [Q, hEven]
  have h0 : (2 * y) % 2 = 0 := by omega
  rw [h0, Nat.zero_add]
  by_cases h : Q T k y = y
  · simp [h]
  · have : 2 * Q T k y ≠ 2 * y := by omega
    simp [h, this]

/--
  **Theorem 12 (Reusable Finite-Certificate Self-Coding Collapse Mechanism):**
  For ANY even-halving `ShiftFaithful` map `T`, if `oddFixedCount T k0 = 0` at a SINGLE
  finite width `k0 >= 1`:
    1. `∀ k >= k0, oddFixedCount T k = 0`;
    2. `∀ k >= k0 - 1, fixedCount T k = fixedCount T (k0 - 1)` (exact infinite plateau!);
    3. `∀ k >= k0 - 1, ∀ x < 2^k, Q T k x = x → 2 ^ (k - (k0 - 1)) ∣ x`;
    4. `x = 0` is the UNIQUE 2-adic fixed point of `Q T` in `Z_2`!
-/
theorem selfCoding_collapse_of_no_odd {T : Nat → Nat}
    (hT : ShiftFaithful T) (hEven : ∀ n, T (2 * n) = n) (k0 : Nat) (hk0 : 1 ≤ k0)
    (hno : oddFixedCount T k0 = 0) :
    (∀ k, k0 ≤ k → oddFixedCount T k = 0) ∧
    (∀ k, k0 - 1 ≤ k → fixedCount T k = fixedCount T (k0 - 1)) ∧
    (∀ k x, k0 - 1 ≤ k → x < 2 ^ k → Q T k x = x → 2 ^ (k - (k0 - 1)) ∣ x) ∧
    (∀ z : Nat → Nat, (∀ k, z k < 2 ^ k) → (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, Q T k (z k) = z k) → ∀ k, z k = 0) := by
  have hno_k0 : ∀ x, x < 2 ^ k0 → x % 2 = 1 → Q T k0 x ≠ x := by
    intro x hx hodd hfix
    have hf := (countLt_eq_zero_iff _ _).mp hno x hx
    simp [hodd, hfix] at hf
  have hno_odd_all : ∀ k, k0 ≤ k → ∀ x, x < 2 ^ k → x % 2 = 1 → Q T k x ≠ x := by
    intro k hk x _ hodd hfix
    have hlo : Q T k0 (x % 2 ^ k0) = x % 2 ^ k0 := by
      have h1 : Q T k x % 2 ^ k0 = Q T k0 x := Q_mod_compat_le T hk x
      rw [hfix] at h1
      rw [hT.Q_congr k0 (x % 2 ^ k0) x (by rw [Nat.mod_mod]), ← h1]
    have hodd_lo : (x % 2 ^ k0) % 2 = 1 := by
      have h2 := mod_pow2_of_le (a := x % 2 ^ k0) (b := x) (k := k0) (j := 1) hk0 (by simp)
      simpa [Nat.pow_one, hodd] using h2
    exact hno_k0 (x % 2 ^ k0) (Nat.mod_lt x (pow2_pos k0)) hodd_lo hlo
  have hodd_zero : ∀ k, k0 ≤ k → oddFixedCount T k = 0 := by
    intro k hk
    rw [oddFixedCount, countLt_eq_zero_iff]
    intro x hx
    by_cases hodd : x % 2 = 1
    · have hne := hno_odd_all k hk x hx hodd
      simp [hodd, hne]
    · simp [hodd]
  have hplateau : ∀ k, k0 - 1 ≤ k → fixedCount T k = fixedCount T (k0 - 1) := by
    intro k hk
    induction k with
    | zero =>
      have : k0 - 1 = 0 := by omega
      rw [this]
    | succ m ih =>
      by_cases hm : k0 - 1 ≤ m
      · rw [fixedCount_succ hEven m, hodd_zero (m + 1) (by omega), Nat.add_zero, ih hm]
      · have : m + 1 = k0 - 1 := by omega
        rw [this]
  have hdvd : ∀ k x, k0 - 1 ≤ k → x < 2 ^ k → Q T k x = x → 2 ^ (k - (k0 - 1)) ∣ x := by
    intro k
    induction k with
    | zero =>
      intro x hk _ _
      have : 0 - (k0 - 1) = 0 := by omega
      rw [this]; simp
    | succ m ih =>
      intro x hk hx hfix
      by_cases hm : k0 - 1 ≤ m
      · have heven : x % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
          · exact h0
          · exact False.elim (hno_odd_all (m + 1) (by omega) x hx h1 hfix)
        have hx2 : x = 2 * (x / 2) := by omega
        have hdiv_lt : x / 2 < 2 ^ m := by rw [Nat.pow_succ] at hx; omega
        have hfix_half : Q T m (x / 2) = x / 2 := by
          have h1 : Q T (m + 1) (2 * (x / 2)) = 2 * (x / 2) := by rwa [← hx2]
          simp only [Q, hEven] at h1
          omega
        rcases ih (x / 2) hm hdiv_lt hfix_half with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have hsub : m + 1 - (k0 - 1) = (m - (k0 - 1)) + 1 := by omega
        rw [hsub, Nat.pow_succ, hx2, hq, Nat.mul_comm (2 ^ (m - (k0 - 1))) 2, Nat.mul_assoc]
      · have hsub : m + 1 - (k0 - 1) = 0 := by omega
        rw [hsub]; simp
  refine ⟨hodd_zero, hplateau, hdvd, ?_⟩
  intro z hzlt hzcompat hzfix k
  have hcompat_le : ∀ a b, a ≤ b → z b % 2 ^ a = z a := by
    intro a b hab
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this; exact Nat.mod_eq_of_lt (hzlt 0)
    | succ m ih =>
      by_cases ham : a ≤ m
      · have hm : z (m + 1) % 2 ^ m = z m % 2 ^ m := by
          rw [hzcompat m, Nat.mod_eq_of_lt (hzlt m)]
        have h1 := mod_pow2_of_le ham hm
        rw [h1, ih ham]
      · have : a = m + 1 := by omega
        subst this; exact Nat.mod_eq_of_lt (hzlt (m + 1))
  let M := k + (k0 - 1)
  have hdivM : 2 ^ k ∣ z M := by
    have h := hdvd M (z M) (by omega) (hzlt M) (hzfix M)
    have hsub : M - (k0 - 1) = k := by omega
    rwa [hsub] at h
  have hmod0 : z M % 2 ^ k = 0 := Nat.mod_eq_zero_of_dvd hdivM
  rw [hcompat_le k M (by omega)] at hmod0
  exact hmod0

/--
  **Theorem 13 (Universal Carryless Self-Coding Exact Formula — ALL odd `p > 1`, ALL `k >= 1`):**
  For EVERY odd `p > 1` (let `v = v2 (p - 1) >= 1`) and EVERY width `k`:
    1. For `k <= v`: `Q (TCarryless p 1) k` is the IDENTITY on `Z / 2^k Z`.
    2. Exact closed-form count for ALL `k`:
         `fixedCount (TCarryless p 1) k = 2 ^ (min k (v2 (p - 1)))`.
    3. `0` is the UNIQUE 2-adic fixed point of `Q (TCarryless p 1)` in `Z_2`!
-/
theorem carryless_selfCoding_exact (p : Nat) (hp_odd : p % 2 = 1) (hp_gt : 1 < p) :
    let v := v2 (p - 1)
    (1 ≤ v) ∧
    (∀ k, k ≤ v → ∀ x, Q (TCarryless p 1) k x = x % 2 ^ k) ∧
    (∀ k, fixedCount (TCarryless p 1) k = 2 ^ (min k v)) ∧
    (∀ z : Nat → Nat, (∀ k, z k < 2 ^ k) → (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, Q (TCarryless p 1) k (z k) = z k) → ∀ k, z k = 0) := by
  intro v
  have hp1_pos : 0 < p - 1 := by omega
  have hp1_even : (p - 1) % 2 = 0 := by omega
  have hv_pos : 1 ≤ v := by
    change 1 ≤ v2 (p - 1)
    rw [v2_eq (p - 1)]
    have hne : p - 1 ≠ 0 := by omega
    have hnot1 : (p - 1) % 2 ≠ 1 := by omega
    simp [hne, hnot1]
  rcases v2_decomp hp1_pos with ⟨u, hu_odd, hp1_eq⟩
  have hp_eq : p = 1 + 2 ^ v * u := by
    change p - 1 = 2 ^ v * u at hp1_eq
    omega
  have hT_odd : ∀ y, y % 2 = 1 →
      TCarryless p 1 y = (y / 2) ^^^ (clmul u y <<< (v - 1)) := by
    intro y hy
    simp only [TCarryless]
    have hne0 : y % 2 ≠ 0 := by omega
    simp only [hne0, ↓reduceIte]
    rw [hp_eq, clmul_one_add_pow2_mul_left v u y hv_pos]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, testBit_div_two,
        Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
    have h1bit : (1 : Nat).testBit (j + 1) = false := by
      exact Nat.testBit_lt_two_pow (by
        have hge : 2 ^ 1 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        exact Nat.lt_of_lt_of_le (by omega) hge)
    rw [h1bit, Bool.xor_false]
    congr 1
    have h1 : (v ≤ j + 1) ↔ (v - 1 ≤ j) := by omega
    have h2 : j + 1 - v = j - (v - 1) := by omega
    by_cases h : v - 1 ≤ j
    · simp [h, h1.mpr h, h2]
    · have h' : ¬(v ≤ j + 1) := fun hc => h (h1.mp hc)
      simp [h, h']
  have hT_mod_vm1 : ∀ y, TCarryless p 1 y % 2 ^ (v - 1) = (y / 2) % 2 ^ (v - 1) := by
    intro y
    rcases Nat.mod_two_eq_zero_or_one y with hy0 | hy1
    · simp [TCarryless, hy0]
    · rw [hT_odd y hy1, mod_two_pow_eq_iff]
      intro j hj
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
      have hnot : ¬(v - 1 ≤ j) := by omega
      simp [hnot]
  have hQ_id : ∀ k, k ≤ v → ∀ x, Q (TCarryless p 1) k x = x % 2 ^ k := by
    intro k
    induction k with
    | zero => intro _ x; simp [Q, Nat.mod_one]
    | succ k ih =>
      intro hkv x
      simp only [Q]
      have hmodk : TCarryless p 1 x % 2 ^ k = (x / 2) % 2 ^ k :=
        mod_pow2_of_le (j := k) (k := v - 1) (by omega) (hT_mod_vm1 x)
      rw [ih (by omega) (TCarryless p 1 x), hmodk, ← mod_pow2_succ_eq]
  have hno_odd_vp1 : oddFixedCount (TCarryless p 1) (v + 1) = 0 := by
    rw [oddFixedCount, countLt_eq_zero_iff]
    intro x hx
    by_cases hodd : x % 2 = 1
    · have hne : Q (TCarryless p 1) (v + 1) x ≠ x := by
        intro hfix
        have hqt : Q (TCarryless p 1) v (TCarryless p 1 x) = x / 2 := by
          rw [Q_conj_shift, hfix]
        rw [hQ_id v (Nat.le_refl v), hT_odd x hodd] at hqt
        have hb := congrArg (fun n => n.testBit (v - 1)) hqt
        rw [Nat.testBit_mod_two_pow] at hb
        have hlt : v - 1 < v := by omega
        simp only [hlt, decide_true, Bool.true_and, Nat.testBit_xor, Nat.testBit_shiftLeft,
                   Nat.le_refl, Nat.sub_self] at hb
        have hcl_odd : clmul u x % 2 = 1 := by
          rw [clmul_mod_two, hu_odd, hodd]
        have hcl0 : (clmul u x).testBit 0 = true := by
          rw [Nat.testBit_zero]; simp [hcl_odd]
        rw [hcl0] at hb
        cases hbit : (x / 2).testBit (v - 1) <;> simp [hbit] at hb
      simp [hodd, hne]
    · simp [hodd]
  have hcol := selfCoding_collapse_of_no_odd
    (carrylessCollatz_shiftFaithful p 1 hp_odd) (TCarryless_even p 1) (v + 1) (by omega) hno_odd_vp1
  refine ⟨hv_pos, hQ_id, ?_, hcol.2.2.2⟩
  intro k
  by_cases hkv : k ≤ v
  · have hmin : min k v = k := Nat.min_eq_left hkv
    rw [hmin, fixedCount]
    apply countLt_all_true
    intro x hx
    rw [hQ_id k hkv x, Nat.mod_eq_of_lt hx]
    simp
  · have hvk : v ≤ k := by omega
    have hmin : min k v = v := Nat.min_eq_right hvk
    rw [hmin]
    have hplat := hcol.2.1 k (by omega)
    simp only [Nat.add_sub_cancel] at hplat
    rw [hplat, fixedCount]
    apply countLt_all_true
    intro x hx
    rw [hQ_id v (Nat.le_refl v) x, Nat.mod_eq_of_lt hx]
    simp

/--
  **Theorem 14A (Single-Carry Collapse for Carried Collatz `a ≡ 1 (mod 4)`):**
  For EVERY `a` with `a % 4 = 1` and EVERY `k >= 1`:
    `fixedCount (TCarried a 1) k = 2`,
  and `0` is the UNIQUE 2-adic fixed point of `Q (TCarried a 1)` in `Z_2`!
-/
theorem carried_mod4_eq1_collapse (a : Nat) (ha : a % 4 = 1) :
    (∀ k, 1 ≤ k → fixedCount (TCarried a 1) k = 2) ∧
    (∀ z : Nat → Nat, (∀ k, z k < 2 ^ k) → (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, Q (TCarried a 1) k (z k) = z k) → ∀ k, z k = 0) := by
  have ha_odd : a % 2 = 1 := by omega
  have hno2 : oddFixedCount (TCarried a 1) 2 = 0 := by
    rw [oddFixedCount, countLt_eq_zero_iff]
    intro x hx
    by_cases hodd : x % 2 = 1
    · have hne : Q (TCarried a 1) 2 x ≠ x := by
        simp only [Q, TCarried]
        have hne0 : x % 2 ≠ 0 := by omega
        simp only [hne0, ↓reduceIte]
        have ha4 : a = 4 * (a / 4) + 1 := by omega
        have hx4 : x = 1 ∨ x = 3 := by omega
        rcases hx4 with rfl | rfl <;> omega
      simp [hodd, hne]
    · simp [hodd]
  have hcol := selfCoding_collapse_of_no_odd
    (carriedCollatz_shiftFaithful a 1 ha_odd) (TCarried_even a 1) 2 (by omega) hno2
  refine ⟨?_, hcol.2.2.2⟩
  intro k hk
  have hplat := hcol.2.1 k (by omega)
  have hf1 : fixedCount (TCarried a 1) 1 = 2 := by
    simp [fixedCount, countLt, Q]
  simpa [hf1] using hplat

/-- Parameter-congruence lifting: `Q (TCarried a b) k` depends ONLY on `a % 2^k`. -/
theorem carried_iter_param_congr (a1 a2 b : Nat) :
    ∀ k x y, a1 % 2 ^ (k + 1) = a2 % 2 ^ (k + 1) → x % 2 ^ (k + 1) = y % 2 ^ (k + 1) →
      TCarried a1 b x % 2 ^ k = TCarried a2 b y % 2 ^ k := by
  intro k x y ha hxy
  have h0 : x % 2 = y % 2 := by
    simpa using mod_pow2_of_le (j := 1) (k := k + 1) (by omega) hxy
  simp only [TCarried]
  by_cases hx0 : x % 2 = 0
  · have hy0 : y % 2 = 0 := by omega
    simp only [hx0, hy0, ↓reduceIte]
    rw [div2_mod_pow2, div2_mod_pow2, hxy]
  · have hy0 : y % 2 ≠ 0 := by omega
    simp only [hx0, hy0, ↓reduceIte]
    rw [div2_mod_pow2, div2_mod_pow2]
    congr 1
    rw [Nat.add_mod, Nat.mul_mod, ha, hxy, ← Nat.mul_mod, ← Nat.add_mod]

theorem carried_Q_param_congr (a1 a2 b : Nat) :
    ∀ k x y, a1 % 2 ^ k = a2 % 2 ^ k → x % 2 ^ k = y % 2 ^ k →
      Q (TCarried a1 b) k x = Q (TCarried a2 b) k y := by
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro x y ha hxy
    simp only [Q]
    have h0 : x % 2 = y % 2 := by
      simpa using mod_pow2_of_le (j := 1) (k := k + 1) (by omega) hxy
    have hak : a1 % 2 ^ k = a2 % 2 ^ k := mod_pow2_of_le (by omega) ha
    have hT := carried_iter_param_congr a1 a2 b k x y ha hxy
    rw [h0, ih (TCarried a1 b x) (TCarried a2 b y) hak hT]

/--
  **Theorem 14B (Finite-Certificate Arithmetic-Progression Collapse for `a ≡ 11 (mod 16)`):**
  For EVERY `a` with `a % 16 = 11` and EVERY `k >= 3`:
    `fixedCount (TCarried a 1) k = 6`,
  and `0` is the UNIQUE 2-adic fixed point of `Q (TCarried a 1)` in `Z_2`!
-/
theorem carried_mod16_eq11_collapse (a : Nat) (ha : a % 16 = 11) :
    (∀ k, 3 ≤ k → fixedCount (TCarried a 1) k = 6) ∧
    (∀ z : Nat → Nat, (∀ k, z k < 2 ^ k) → (∀ k, z (k + 1) % 2 ^ k = z k) →
      (∀ k, Q (TCarried a 1) k (z k) = z k) → ∀ k, z k = 0) := by
  have ha_odd : a % 2 = 1 := by omega
  have ha16 : a % 2 ^ 4 = 11 % 2 ^ 4 := by simpa using ha
  have hq4 : ∀ x, Q (TCarried a 1) 4 x = Q (TCarried 11 1) 4 x :=
    fun x => carried_Q_param_congr a 11 1 4 x x ha16 rfl
  have hq3 : ∀ x, Q (TCarried a 1) 3 x = Q (TCarried 11 1) 3 x :=
    fun x => carried_Q_param_congr a 11 1 3 x x (mod_pow2_of_le (by omega) ha16) rfl
  have hno4_11 : oddFixedCount (TCarried 11 1) 4 = 0 := by decide
  have hf3_11 : fixedCount (TCarried 11 1) 3 = 6 := by decide
  have hno4 : oddFixedCount (TCarried a 1) 4 = 0 := by
    have heq : oddFixedCount (TCarried a 1) 4 = oddFixedCount (TCarried 11 1) 4 := by
      simp only [oddFixedCount]
      exact countLt_congr _ _ _ (fun x _ => by rw [hq4 x])
    rw [heq, hno4_11]
  have hf3 : fixedCount (TCarried a 1) 3 = 6 := by
    have heq : fixedCount (TCarried a 1) 3 = fixedCount (TCarried 11 1) 3 := by
      simp only [fixedCount]
      exact countLt_congr _ _ _ (fun x _ => by rw [hq3 x])
    rw [heq, hf3_11]
  have hcol := selfCoding_collapse_of_no_odd
    (carriedCollatz_shiftFaithful a 1 ha_odd) (TCarried_even a 1) 4 (by omega) hno4
  refine ⟨?_, hcol.2.2.2⟩
  intro k hk
  have hplat := hcol.2.1 k (by omega)
  simpa [hf3] using hplat

/--
  **Theorem 14C (Unbounded Self-Coding Growth for Classical Carried Collatz `3x+1`):**
  For classical Carried Collatz `TCarried 3 1`, EVERY `(2^k - 2^r) % 2^k` (`0 <= r <= k`) is
  a self-coding fixed point, giving `fixedCount (TCarried 3 1) k >= k + 1` for ALL `k`!
-/
theorem carried_collatz_all_ones_fixed (k : Nat) :
    Q (TCarried 3 1) k (2 ^ k - 1) = 2 ^ k - 1 := by
  induction k with
  | zero => simp [Q]
  | succ k ih =>
    have hp := pow2_pos k
    have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hodd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hT : TCarried 3 1 (2 ^ (k + 1) - 1) = 3 * 2 ^ k - 1 := by
      simp only [TCarried]
      have hne0 : (2 ^ (k + 1) - 1) % 2 ≠ 0 := by omega
      simp only [hne0, ↓reduceIte]
      omega
    have hmod : (3 * 2 ^ k - 1) % 2 ^ k = (2 ^ k - 1) % 2 ^ k := by
      have heq : 3 * 2 ^ k - 1 = (2 ^ k - 1) + 2 ^ k * 2 := by omega
      rw [heq, Nat.add_mul_mod_self_left]
    simp only [Q, hodd, hT]
    rw [(carriedCollatz_shiftFaithful 3 1 rfl).Q_congr k (3 * 2 ^ k - 1) (2 ^ k - 1) hmod, ih]
    omega

theorem carried_collatz_neg_pow2_fixed (k r : Nat) (hr : r ≤ k) :
    Q (TCarried 3 1) k ((2 ^ k - 2 ^ r) % 2 ^ k) = (2 ^ k - 2 ^ r) % 2 ^ k := by
  induction r generalizing k with
  | zero =>
    have hp := pow2_pos k
    have hlt : 2 ^ k - 1 < 2 ^ k := by omega
    simp only [Nat.pow_zero, Nat.mod_eq_of_lt hlt]
    exact carried_collatz_all_ones_fixed k
  | succ r ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hrk : r ≤ k := by omega
      by_cases heq : r = k
      · subst heq
        have hzero : ∀ m, Q (TCarried 3 1) m 0 = 0 := by
          intro m; induction m with
          | zero => rfl
          | succ m ihm => simp [Q, TCarried, ihm]
        simp [hzero]
      · have hlt_r : r < k := by omega
        have hpr : 2 ^ r < 2 ^ k := Nat.pow_lt_pow_right (by omega) hlt_r
        have hpr_pos := pow2_pos r
        have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
        have h2r : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ]; omega
        have hlt1 : 2 ^ (k + 1) - 2 ^ (r + 1) < 2 ^ (k + 1) := by omega
        have hlt2 : 2 ^ k - 2 ^ r < 2 ^ k := by omega
        rw [Nat.mod_eq_of_lt hlt1]
        have htwice : 2 ^ (k + 1) - 2 ^ (r + 1) = 2 * (2 ^ k - 2 ^ r) := by omega
        rw [htwice]
        simp only [Q, TCarried_even]
        have h0 : 2 * (2 ^ k - 2 ^ r) % 2 = 0 := by omega
        rw [h0, Nat.zero_add]
        have hih := ih k hrk
        rw [Nat.mod_eq_of_lt hlt2] at hih
        rw [hih]

/-- Explicit lower bound `fixedCount (TCarried 3 1) k >= k + 1` for ALL `k`. -/
theorem carried_collatz_fixedCount_ge (k : Nat) :
    k + 1 ≤ fixedCount (TCarried 3 1) k := by
  induction k with
  | zero => simp [fixedCount, countLt, Q]
  | succ k ih =>
    rw [fixedCount_succ (TCarried_even 3 1)]
    have hodd_ge1 : 1 ≤ oddFixedCount (TCarried 3 1) (k + 1) := by
      have hp := pow2_pos k
      have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      have hfix := carried_collatz_all_ones_fixed (k + 1)
      have hodd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
      simp only [oddFixedCount]
      have hsplit : 2 ^ (k + 1) = (2 ^ (k + 1) - 1) + 1 := by omega
      rw [hsplit]
      simp only [countLt, hodd, hfix, decide_true, Bool.and_self, ↓reduceIte]
      omega
    omega

-- ============================================================================
-- SECTION 5: Novel Infinite Theorem II — Carryless-Collatz Trajectory Degree
--            Identity, Cycle Obstruction & Unique Non-Zero Cycle of 3x ^ 1
-- ============================================================================

/-- For `p >= 3` and `q < 2^(bitDeg p)`, every `x > 0` maps to `TCarryless p q x > 0`
    and obeys the exact bit-degree law `bitDeg (T x) + 1 = bitDeg x + bitDeg p * (x % 2)`. -/
theorem carryless_step_bitDeg {p q x : Nat}
    (hp3 : 3 ≤ p) (hq : q < 2 ^ bitDeg p) (hx : 0 < x) :
    0 < TCarryless p q x ∧
    bitDeg (TCarryless p q x) + 1 = bitDeg x + bitDeg p * (x % 2) := by
  have hdp : 1 ≤ bitDeg p := by
    rw [bitDeg_eq p]
    have hnot : ¬(p ≤ 1) := by omega
    simp [hnot]
  rcases Nat.mod_two_eq_zero_or_one x with hev | hodd
  · simp only [TCarryless, hev, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    have hx2 : 2 ≤ x := by omega
    have hdiv_pos : 0 < x / 2 := by omega
    refine ⟨hdiv_pos, ?_⟩
    rw [bitDeg_eq x]
    have hnot1 : ¬(x ≤ 1) := by omega
    simp [hnot1]
  · simp only [TCarryless, hodd, Nat.mul_one]
    have h10 : ¬((1 : Nat) = 0) := by omega
    simp only [h10, ↓reduceIte]
    have ⟨hcl1, hcl2⟩ := clmul_bitDeg (p := p) (x := x) (by omega) hx
    have hq_lt : q < 2 ^ (bitDeg p + bitDeg x) :=
      Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _))
    have ⟨hb1, hb2⟩ := xor_preserves_band hcl1 hcl2 hq_lt
    have hN_pos : 1 ≤ bitDeg p + bitDeg x := by omega
    have h2N : 2 ^ (bitDeg p + bitDeg x) = 2 * 2 ^ (bitDeg p + bitDeg x - 1) :=
      pow2_split (bitDeg p + bitDeg x) hN_pos
    have h2N1 : 2 ^ (bitDeg p + bitDeg x + 1) = 2 * 2 ^ (bitDeg p + bitDeg x) := by
      rw [Nat.pow_succ]; omega
    have hdiv_ge : 2 ^ (bitDeg p + bitDeg x - 1) ≤ (clmul p x ^^^ q) / 2 := by omega
    have hdiv_lt : (clmul p x ^^^ q) / 2 < 2 ^ (bitDeg p + bitDeg x - 1 + 1) := by
      have heq : bitDeg p + bitDeg x - 1 + 1 = bitDeg p + bitDeg x := by omega
      rw [heq]; omega
    have hpos : 0 < (clmul p x ^^^ q) / 2 :=
      Nat.lt_of_lt_of_le (pow2_pos _) hdiv_ge
    have hdeg := bitDeg_eq_of_bounds hdiv_ge hdiv_lt
    exact ⟨hpos, by omega⟩

/-- **Theorem 15 (Universal Carryless-Collatz Exact Trajectory Bit-Degree Identity):** -/
theorem carryless_trajectory_bitDeg {p q : Nat}
    (hp3 : 3 ≤ p) (hq : q < 2 ^ bitDeg p) :
    ∀ L x, 0 < x →
      0 < iter (TCarryless p q) L x ∧
      bitDeg (iter (TCarryless p q) L x) + L =
        bitDeg x + bitDeg p * popcount (Q (TCarryless p q) L x) := by
  intro L
  induction L with
  | zero =>
    intro x hx
    simp [iter, Q, popcount_zero, hx]
  | succ L ih =>
    intro x hx
    have ⟨hTx_pos, hstep⟩ := carryless_step_bitDeg hp3 hq hx
    have ⟨hiter_pos, hih⟩ := ih (TCarryless p q x) hTx_pos
    refine ⟨hiter_pos, ?_⟩
    simp only [iter, Q]
    rw [popcount_bit_add _ _ (Nat.mod_lt x (by omega)), Nat.mul_add]
    omega

/-- **Theorem 16 (Carryless-Collatz Finite-Cycle Degree-Balance Obstruction):** -/
theorem carryless_cycle_degree_balance {p q L x : Nat}
    (hp3 : 3 ≤ p) (hq : q < 2 ^ bitDeg p) (hx : 0 < x)
    (hcyc : iter (TCarryless p q) L x = x) :
    L = bitDeg p * popcount (Q (TCarryless p q) L x) := by
  have ⟨_, htraj⟩ := carryless_trajectory_bitDeg hp3 hq L x hx
  rw [hcyc] at htraj
  omega

theorem carryless_no_cycle_not_dvd {p q L x : Nat}
    (hp3 : 3 ≤ p) (hq : q < 2 ^ bitDeg p) (hx : 0 < x)
    (hndvd : ¬ bitDeg p ∣ L) :
    iter (TCarryless p q) L x ≠ x := by
  intro hcyc
  have hbal := carryless_cycle_degree_balance hp3 hq hx hcyc
  exact hndvd ⟨popcount (Q (TCarryless p q) L x), hbal⟩

/-- **Theorem 17 (Unique Non-Zero Finite Cycle of Carryless `3x+1`, via 2-Adic Uniqueness):** -/
theorem carryless_3x1_fixed_one : TCarryless 3 1 1 = 1 := by decide

theorem carryless_3x1_iter_one (L : Nat) : iter (TCarryless 3 1) L 1 = 1 := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [iter, carryless_3x1_fixed_one, ih]

theorem carryless_3x1_Q_one (L : Nat) : Q (TCarryless 3 1) L 1 = 2 ^ L - 1 := by
  induction L with
  | zero => simp [Q]
  | succ L ih =>
    simp only [Q, carryless_3x1_fixed_one, ih]
    have hp := pow2_pos L
    rw [Nat.pow_succ]; omega

theorem carryless_3x1_unique_nonzero_cycle {L x : Nat} (hL : 1 ≤ L) (hx : 0 < x)
    (hcyc : iter (TCarryless 3 1) L x = x) : x = 1 := by
  have hd3 : bitDeg 3 = 1 := by decide
  have hq3 : 1 < 2 ^ bitDeg 3 := by decide
  have hbal := carryless_cycle_degree_balance (p := 3) (q := 1) (by omega) hq3 hx hcyc
  rw [hd3, Nat.one_mul] at hbal
  have hQ_all1 : Q (TCarryless 3 1) L x = 2 ^ L - 1 :=
    (popcount_eq_width_iff L (Q (TCarryless 3 1) L x) (Q_lt _ L x)).mp hbal.symm
  have hSF := carrylessCollatz_shiftFaithful 3 1 rfl
  have huniq := (hSF.periodic_orbit_classification L hL).2
  have hz_eq_x : ∀ k, x % 2 ^ k = perOrbit (TCarryless 3 1) L (2 ^ L - 1) k := by
    have hx_proj := huniq (fun k => x % 2 ^ k)
      (fun k => Nat.mod_lt x (pow2_pos k))
      (fun k => Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (Nat.le_succ k)))
      (fun k => by
        rw [hSF.iter_causal L k (x % 2 ^ (k + L)) x (by rw [Nat.mod_mod]), hcyc])
    have hQx : Q (TCarryless 3 1) L (x % 2 ^ L) = 2 ^ L - 1 := by
      rw [hSF.Q_congr L (x % 2 ^ L) x (by rw [Nat.mod_mod]), hQ_all1]
    intro k
    simpa [hQx] using hx_proj k
  have hz_eq_1 : ∀ k, 1 % 2 ^ k = perOrbit (TCarryless 3 1) L (2 ^ L - 1) k := by
    have h1_proj := huniq (fun k => 1 % 2 ^ k)
      (fun k => Nat.mod_lt 1 (pow2_pos k))
      (fun k => Nat.mod_mod_of_dvd 1 (Nat.pow_dvd_pow 2 (Nat.le_succ k)))
      (fun k => by
        rw [hSF.iter_causal L k (1 % 2 ^ (k + L)) 1 (by rw [Nat.mod_mod]),
            carryless_3x1_iter_one L])
    have hQ1 : Q (TCarryless 3 1) L (1 % 2 ^ L) = 2 ^ L - 1 := by
      rw [hSF.Q_congr L (1 % 2 ^ L) 1 (by rw [Nat.mod_mod]), carryless_3x1_Q_one L]
    intro k
    simpa [hQ1] using h1_proj k
  have hlt_x : x < 2 ^ (x + 1) := by
    have hpow : ∀ n, n < 2 ^ n := by
      intro n; induction n with
      | zero => simp
      | succ n ihn => rw [Nat.pow_succ]; omega
    exact Nat.lt_trans (Nat.lt_succ_self x) (hpow (x + 1))
  have hlt_1 : 1 < 2 ^ (x + 1) := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (by omega : 1 ≤ x + 1)
    exact Nat.lt_of_lt_of_le (by omega) this
  have hmod := (hz_eq_x (x + 1)).trans (hz_eq_1 (x + 1)).symm
  rwa [Nat.mod_eq_of_lt hlt_x, Nat.mod_eq_of_lt hlt_1] at hmod

-- ============================================================================
-- SECTION 6: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples
-- ============================================================================

-- 6A. Non-vacuity witnesses for `checkAffTable` / `checkClTable` (r = 2 and r = 3)

/-- Non-trivial 4-branch carried table with 4 distinct odd slopes (1, 3, 5, 7). -/
def tab4Aff (i : Nat) : Nat × Nat :=
  match i with
  | 0 => (1, 0)
  | 1 => (3, 1)
  | 2 => (5, 0)
  | _ => (7, 1)

/-- Non-trivial 8-branch carried table with 8 distinct odd slopes (1, 3, 5, 7, 9, 11, 13, 15). -/
def tab8Aff (i : Nat) : Nat × Nat :=
  (2 * i + 1, i % 2)

/-- Non-trivial 4-branch carryless table with 4 distinct odd polynomials (1, 3, 5, 7). -/
def tab4Cl (i : Nat) : Nat × Nat :=
  match i with
  | 0 => (1, 0)
  | 1 => (3, 1)
  | 2 => (5, 0)
  | _ => (7, 1)

/-- Certified by `decide` -> lifts to ALL infinite-width theorems via Theorems 10 & 11! -/
theorem tab4Aff_shiftFaithful : ShiftFaithful (evalAffTable 2 tab4Aff) :=
  (checkAffTable_iff_shiftFaithful 2 (by omega) tab4Aff).mp (by decide)

theorem tab8Aff_shiftFaithful : ShiftFaithful (evalAffTable 3 tab8Aff) :=
  (checkAffTable_iff_shiftFaithful 3 (by omega) tab8Aff).mp (by decide)

theorem tab4Cl_shiftFaithful : ShiftFaithful (evalClTable 2 tab4Cl) :=
  (checkClTable_iff_shiftFaithful 2 (by omega) tab4Cl).mp (by decide)

/-- Non-vacuity witness: Carryless 5x+1 genuinely has non-trivial cycles satisfying `L = 2 * m`! -/
example : iter (TCarryless 5 1) 2 1 = 1 ∧ 2 = bitDeg 5 * popcount (Q (TCarryless 5 1) 2 1) := by
  decide

example : iter (TCarryless 5 1) 4 7 = 7 ∧ 4 = bitDeg 5 * popcount (Q (TCarryless 5 1) 4 7) := by
  decide

/-- Non-vacuity witness: Concrete Syracuse conjugacy at `x = 5` (`T_+(5) = 8 = 2^3`, `k = 6`). -/
example :
    let T1 := TCarried 3 1
    let T2 := TCarryless 3 1
    let y := Phi T1 T2 6 5
    T1 5 = 8 ∧ 2 ^ 3 ∣ T2 y ∧ ¬ 2 ^ 4 ∣ T2 y ∧
    Phi T1 T2 2 (T1 5 / 8) = (T2 y / 8) % 2 ^ 2 := by
  decide

-- 6B. Kernel-checked sharpness / falsification counterexamples!

/-- Sharpness 1: Even slope `a_1 = 2` fails `checkAffTable` and breaks `Q_2` injectivity (`Q_2(1) = Q_2(3)`). -/
def tabEvenBad (i : Nat) : Nat × Nat :=
  if i = 0 then (1, 0) else (2, 2)

theorem sharpness_even_slope_fails :
    checkAffTable 1 tabEvenBad = false ∧
    ¬ ShiftFaithful (evalAffTable 1 tabEvenBad) ∧
    Q (evalAffTable 1 tabEvenBad) 2 1 = Q (evalAffTable 1 tabEvenBad) 2 3 := by
  have hchk : checkAffTable 1 tabEvenBad = false := by decide
  have hcol : Q (evalAffTable 1 tabEvenBad) 2 1 = Q (evalAffTable 1 tabEvenBad) 2 3 := by decide
  refine ⟨hchk, ?_, hcol⟩
  intro hSF
  have htrue := (checkAffTable_iff_shiftFaithful 1 (by omega) tabEvenBad).mpr hSF
  rw [hchk] at htrue
  exact Bool.noConfusion htrue

/-- Sharpness 2: ALL slopes odd AND ALL divisions exact, yet ONE broken cross-branch gluing bit
    in a 4-branch table fails `checkAffTable` and breaks `Q_2` injectivity (`Q_2(0) = Q_2(2)`). -/
def tab4GlueBad (i : Nat) : Nat × Nat :=
  match i with
  | 0 => (1, 0)
  | 1 => (3, 1)
  | 2 => (5, 2)
  | _ => (7, 1)

theorem sharpness_broken_gluing_fails :
    (∀ i, i < 4 → (tab4GlueBad i).1 % 2 = 1) ∧
    checkAffTable 2 tab4GlueBad = false ∧
    ¬ ShiftFaithful (evalAffTable 2 tab4GlueBad) ∧
    Q (evalAffTable 2 tab4GlueBad) 2 0 = Q (evalAffTable 2 tab4GlueBad) 2 2 := by
  have hodd : ∀ i, i < 4 → (tab4GlueBad i).1 % 2 = 1 := by
    intro i hi
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | _ + 4 => omega
  have hchk : checkAffTable 2 tab4GlueBad = false := by decide
  have hcol : Q (evalAffTable 2 tab4GlueBad) 2 0 = Q (evalAffTable 2 tab4GlueBad) 2 2 := by decide
  refine ⟨hodd, hchk, ?_, hcol⟩
  intro hSF
  have htrue := (checkAffTable_iff_shiftFaithful 2 (by omega) tab4GlueBad).mpr hSF
  rw [hchk] at htrue
  exact Bool.noConfusion htrue

/-- Sharpness 3: Violating `q < 2^(bitDeg p)` (`p = 3`, `bitDeg 3 = 1`, `q = 7 >= 2^1`)
    breaks Cycle Degree-Balance: `{1, 2}` is a non-zero 2-cycle with `L = 2 != 1 * 1 = d * m`. -/
theorem sharpness_degree_balance_requires_q_bound :
    iter (TCarryless 3 7) 2 1 = 1 ∧
    2 ≠ bitDeg 3 * popcount (Q (TCarryless 3 7) 2 1) := by
  decide

/-- Sharpness 4: Single-carry phase contrast at multiplier `5`:
    Carryless `TCarryless 5 1` has `fixedCount = 4`, Carried `TCarried 5 1` collapses to `2`,
    Carried `TCarried 11 1` collapses to `6`, while Carried `TCarried 3 1` has `16` at `k = 5`. -/
theorem sharpness_carry_phase_contrast :
    fixedCount (TCarryless 5 1) 5 = 4 ∧
    fixedCount (TCarried 5 1) 5 = 2 ∧
    fixedCount (TCarried 11 1) 5 = 6 ∧
    fixedCount (TCarried 3 1) 5 = 16 := by
  decide

end Dynsil9

-- ============================================================================
-- SECTION 7: Axiom Audits (`#print axioms` on every main theorem)
-- ============================================================================


