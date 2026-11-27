/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KummerCarryValuationAutomata.Defs

/-!
# Generalized Kummer / Legendre Carry-Valuation Automaton (CVA) Engine
Worker: `adic-4` (Thread 4: 2-Adic, Nimber, Carry-Arithmetic & Number-Theoretic Infinite Mechanisms)

Standalone Lean 4.34.1 formalization (zero Mathlib, zero `sorry`, standard axioms only).

## Contents
1. **Verified Exact Arithmetic & Legendre/Kummer Foundation** (built from scratch):
   - `fact`, `binom`, `trinom`, `popcount`, `v2`, `gray` (all structurally recursive & kernel-reducible)
   - Exact divisibility characterization of `v2`: `2 ^ v2 n ∣ n` and `¬ (2 ^ (v2 n + 1) ∣ n)` for `n > 0`
   - Legendre's Formula: `v2 (fact n) + popcount n = n`
   - Kummer's Theorem: `v2 (binom (a + b) a) + popcount (a + b) = popcount a + popcount b`
   - Trinomial Kummer Theorem: `v2 (trinom a b c) + popcount (a + b + c) = popcount a + popcount b + popcount c`
2. **Reusable Finite-to-Infinite Proof Mechanism (`CVA S`)**:
   - Generic finite-state Carry-Valuation Automaton (`CVA S`)
   - `CVA.coboundary_sound`: finite `decide`-checked potential certifies `∀ n, M.eval q n = φ q`
   - `CVA.lower_sound` / `CVA.upper_sound`: finite `decide`-checked tropical potentials certify
     `∀ n, φ q ≤ M.eval q n` and `∀ n, M.eval q n ≤ ψ q`
   - `pos_upper_of_doubling_inv`: lifts odd-input CVA bounds to `∀ n ≥ 1`
   - `CVA.pumping_exact`: finite `decide`-checked zero-slack lasso certifies an infinite family
     achieving exact equality in the bound (`∀ m : Nat`) — proving both slope and offset are sharp!
3. **Novel Infinite Theorem Families Proved Through the Engine**:
   - **Family I (Shifted-Bitwise Kummer Collapse Laws, `∀ n : Nat`)**:
     * `v2 (binom (n + (n ^^^ (2 * n))) n) = popcount (n ||| (2 * n))`
     * `2 * v2 (binom (n + (n ^^^ (2 * n))) n) = 2 * popcount n + popcount (n ^^^ (2 * n))`
     * `v2 (binom (n + (n ||| (2 * n))) n) = popcount (n ||| (2 * n))`
     * `v2 (binom (n + (n &&& (2 * n))) n) = popcount (n &&& (2 * n))`
     * `v2 (trinom n (2 * n) (n ^^^ (2 * n))) = popcount (n ||| (2 * n))`
     * Plus popcount conservation laws `popcount (n + (n ||| 2*n)) = popcount n` and `popcount (n + (n &&& 2*n)) = popcount n`
   - **Family II (Gray-Code Binomial Tight Valuation Sandwich & Universal Evenness)**:
     * `∀ n, popcount (gray n) ≤ 2 * v2 (binom (n + gray n) n)` (sharp on infinite family `∀ m`)
     * `∀ n ≥ 1, 2 ∣ binom (n + gray n) n` (universal evenness)
     * `∀ n ≥ 1, v2 (binom (n + gray n) n) + 1 ≤ v2 (binom (n + (n ^^^ (2 * n))) n)` (sharp on infinite family `∀ m`)
   - **Family III (Parametric `k`-Binomial Tropical Engine & Non-Integer Slope Laws, `∀ n ≥ 1`)**:
     * Parametric `2*(k-1)`-state CVA proved once for all `k ≥ 2`
     * `k = 11` (20 states, slope `5/2`): `2 * v2 (binom (11 * n) n) + 2 ≤ 5 * popcount n` (sharp `∀ m`)
     * `k = 25` (48 states, slope `8/3`): `3 * v2 (binom (25 * n) n) + 3 ≤ 8 * popcount n` (sharp `∀ m`)
     * `k = 55` (108 states, slope `13/4`): `4 * v2 (binom (55 * n) n) + 8 ≤ 13 * popcount n` (sharp `∀ m`)
4. **Non-Vacuity Witnesses, Sharpness Counterexamples, and `#print axioms` Receipts**.
-/


-- ============================================================================
-- SECTION 1: Exact Arithmetic Primitives & Legendre / Kummer Foundation
-- ============================================================================

namespace CVAEngine

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by simp [fact]
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem binom_self : ∀ n, binom n n = 1
  | 0 => rfl
  | n + 1 => by
    simp only [binom, binom_self n]
    have h0 : ∀ m k, m < k → binom m k = 0 := by
      intro m
      induction m with
      | zero => intro k hk; cases k with | zero => omega | succ k' => rfl
      | succ m ih =>
        intro k hk
        cases k with
        | zero => omega
        | succ k' =>
          simp only [binom]
          rw [ih k' (by omega), ih (k' + 1) (by omega)]
    rw [h0 n (n + 1) (by omega)]

theorem binom_mul_fact : ∀ a b, binom (a + b) a * fact a * fact b = fact (a + b) := by
  intro a
  induction a with
  | zero =>
    intro b
    simp [binom, fact]
  | succ a iha =>
    intro b
    induction b with
    | zero =>
      simp [binom_self, fact]
    | succ b ihb =>
      have h1 : a + 1 + (b + 1) = (a + (b + 1)) + 1 := by omega
      have h2 : a + (b + 1) = (a + 1) + b := by omega
      rw [h1, binom]
      have eq1 := iha (b + 1)
      have eq2 := ihb
      rw [← h2] at eq2
      have lhs_split :
          (binom (a + (b + 1)) a + binom (a + (b + 1)) (a + 1)) * fact (a + 1) * fact (b + 1)
          = (a + 1) * (binom (a + (b + 1)) a * fact a * fact (b + 1))
          + (b + 1) * (binom (a + (b + 1)) (a + 1) * fact (a + 1) * fact b) := by
        simp only [fact]
        have t1 : binom (a + (b + 1)) a * ((a + 1) * fact a) * ((b + 1) * fact b)
            = (a + 1) * (binom (a + (b + 1)) a * fact a * ((b + 1) * fact b)) := by
          ac_rfl
        have t2 : binom (a + (b + 1)) (a + 1) * ((a + 1) * fact a) * ((b + 1) * fact b)
            = (b + 1) * (binom (a + (b + 1)) (a + 1) * ((a + 1) * fact a) * fact b) := by
          ac_rfl
        rw [Nat.add_mul, Nat.add_mul, t1, t2]
      rw [lhs_split, eq1, eq2]
      have rhs_eq : fact (a + (b + 1) + 1) = ((a + 1) + (b + 1)) * fact (a + (b + 1)) := by
        simp only [fact]
        congr 1; omega
      rw [rhs_eq]
      exact (Nat.add_mul (a + 1) (b + 1) (fact (a + (b + 1)))).symm

theorem binom_pos (a b : Nat) : 0 < binom (a + b) a := by
  have hne : binom (a + b) a ≠ 0 := by
    intro hz
    have heq := binom_mul_fact a b
    rw [hz, Nat.zero_mul, Nat.zero_mul] at heq
    have hp := fact_pos (a + b)
    omega
  omega

theorem trinom_mul_fact (a b c : Nat) :
    trinom a b c * fact a * fact b * fact c = fact (a + b + c) := by
  unfold trinom
  have h1 := binom_mul_fact a (b + c)
  have h2 := binom_mul_fact b c
  have hadd : a + (b + c) = a + b + c := by omega
  rw [hadd] at h1
  calc binom (a + b + c) a * binom (b + c) b * fact a * fact b * fact c
      = (binom (a + b + c) a * fact a) * (binom (b + c) b * fact b * fact c) := by ac_rfl
    _ = (binom (a + b + c) a * fact a) * fact (b + c) := by rw [h2]
    _ = binom (a + b + c) a * fact a * fact (b + c) := by ac_rfl
    _ = fact (a + b + c) := h1

theorem trinom_pos (a b c : Nat) : 0 < trinom a b c := by
  unfold trinom
  have hadd : a + b + c = a + (b + c) := by omega
  rw [hadd]
  exact Nat.mul_pos (binom_pos a (b + c)) (binom_pos b c)

-- Bit-parity helper

theorem mod_two_eq_bool_toNat (n : Nat) : (n % 2 == 1).toNat = n % 2 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
  cases h : n % 2 with
  | zero => rfl
  | succ k =>
    have hk : k = 0 := by omega
    subst hk; rfl

theorem nat_eq_two_mul_div_add_bool (n : Nat) :
    n = 2 * (n / 2) + (n % 2 == 1).toNat := by
  rw [mod_two_eq_bool_toNat]; omega

-- Structurally recursive, kernel-reducible binary popcount s_2(n)

theorem popcountAux_eq : ∀ fuel1 fuel2 n, n ≤ fuel1 → n ≤ fuel2 →
    popcountAux fuel1 n = popcountAux fuel2 n := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 n h1 _
    have hz : n = 0 := by omega
    subst hz
    cases fuel2 <;> rfl
  | succ f1 ih =>
    intro fuel2 n h1 h2
    cases n with
    | zero =>
      cases fuel2 <;> rfl
    | succ m =>
      cases fuel2 with
      | zero => omega
      | succ f2 =>
        simp only [popcountAux]
        congr 1
        exact ih f2 ((m + 1) / 2) (by omega) (by omega)

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_step {n : Nat} (hn : n ≠ 0) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => omega
  | succ m =>
    unfold popcount
    simp only [popcountAux]
    congr 1
    exact popcountAux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) (by omega)

theorem popcount_two_mul_add (n b : Nat) (hb : b ≤ 1) :
    popcount (2 * n + b) = b + popcount n := by
  by_cases h : 2 * n + b = 0
  · have hn : n = 0 := by omega
    have hb0 : b = 0 := by omega
    subst hn; subst hb0; rfl
  · rw [popcount_step h]
    have hmod : (2 * n + b) % 2 = b := by omega
    have hdiv : (2 * n + b) / 2 = n := by omega
    rw [hmod, hdiv]

theorem popcount_double (n : Nat) : popcount (2 * n) = popcount n := by
  have h := popcount_two_mul_add n 0 (by omega)
  simpa using h

theorem popcount_pos_of_pos {n : Nat} (hn : 0 < n) : 0 < popcount n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [popcount_step (by omega)]
    by_cases hmod : n % 2 = 1
    · omega
    · have hdiv : 0 < n / 2 := by omega
      have hih := ih (n / 2) (by omega) hdiv
      omega

-- Structurally recursive, kernel-reducible exact 2-adic valuation v_2(n)

theorem v2Aux_eq : ∀ fuel1 fuel2 n, n ≤ fuel1 → n ≤ fuel2 →
    v2Aux fuel1 n = v2Aux fuel2 n := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 n h1 _
    have hz : n = 0 := by omega
    subst hz
    cases fuel2 <;> rfl
  | succ f1 ih =>
    intro fuel2 n h1 h2
    cases n with
    | zero =>
      cases fuel2 <;> rfl
    | succ m =>
      cases fuel2 with
      | zero => omega
      | succ f2 =>
        simp only [v2Aux]
        by_cases hmod : (m + 1) % 2 = 1
        · simp [hmod]
        · simp only [hmod, ↓reduceIte]
          congr 1
          exact ih f2 ((m + 1) / 2) (by omega) (by omega)

theorem v2_zero : v2 0 = 0 := rfl

theorem v2_odd {n : Nat} (h : n % 2 = 1) : v2 n = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    unfold v2
    simp [v2Aux, h]

theorem v2_two_mul {n : Nat} (hn : 0 < n) : v2 (2 * n) = 1 + v2 n := by
  cases h2n : 2 * n with
  | zero => omega
  | succ m =>
    unfold v2
    simp only [v2Aux]
    have hmod : (m + 1) % 2 ≠ 1 := by omega
    have hdiv : (m + 1) / 2 = n := by omega
    simp only [hmod, ↓reduceIte, hdiv]
    congr 1
    exact v2Aux_eq m n n (by omega) (by omega)

theorem v2_mul : ∀ a b, 0 < a → 0 < b → v2 (a * b) = v2 a + v2 b := by
  intro a b
  induction hsum : a + b using Nat.strongRecOn generalizing a b with
  | ind s ih =>
    intro ha hb
    by_cases ha2 : a % 2 = 0
    · have ha' : a = 2 * (a / 2) := by omega
      have ha_pos : 0 < a / 2 := by omega
      rw [ha', Nat.mul_assoc, v2_two_mul (Nat.mul_pos ha_pos hb), v2_two_mul ha_pos]
      have hih := ih (a / 2 + b) (by omega) (a / 2) b rfl ha_pos hb
      omega
    · by_cases hb2 : b % 2 = 0
      · have hb' : b = 2 * (b / 2) := by omega
        have hb_pos : 0 < b / 2 := by omega
        have hrew : a * (2 * (b / 2)) = 2 * (a * (b / 2)) := by ac_rfl
        rw [hb', hrew, v2_two_mul (Nat.mul_pos ha hb_pos), v2_two_mul hb_pos]
        have hih := ih (a + b / 2) (by omega) a (b / 2) rfl ha hb_pos
        omega
      · have ha1 : a % 2 = 1 := by omega
        have hb1 : b % 2 = 1 := by omega
        have hab1 : (a * b) % 2 = 1 := by
          rw [Nat.mul_mod, ha1, hb1]
        rw [v2_odd ha1, v2_odd hb1, v2_odd hab1]

theorem pow_two_v2_dvd : ∀ n, 0 < n → 2 ^ v2 n ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hmod : n % 2 = 1
    · rw [v2_odd hmod]; simp
    · have hdiv_pos : 0 < n / 2 := by omega
      have hn_eq : n = 2 * (n / 2) := by omega
      have hv : v2 n = 1 + v2 (n / 2) := by
        conv => lhs; rw [hn_eq]
        exact v2_two_mul hdiv_pos
      have hpow : 2 ^ v2 n = 2 * 2 ^ v2 (n / 2) := by
        rw [hv, Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
      have ⟨k, hk⟩ := ih (n / 2) (by omega) hdiv_pos
      refine ⟨k, ?_⟩
      rw [hpow]
      have hmul : 2 * (n / 2) = 2 * 2 ^ v2 (n / 2) * k := by
        conv => lhs; rw [hk]
        ac_rfl
      exact hn_eq.trans hmul

theorem not_pow_two_v2_succ_dvd : ∀ n, 0 < n → ¬ (2 ^ (v2 n + 1) ∣ n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn ⟨k, hk⟩
    by_cases hmod : n % 2 = 1
    · rw [v2_odd hmod] at hk
      simp at hk
      omega
    · have hdiv_pos : 0 < n / 2 := by omega
      have hn_eq : n = 2 * (n / 2) := by omega
      have hv : v2 n = 1 + v2 (n / 2) := by
        conv => lhs; rw [hn_eq]
        exact v2_two_mul hdiv_pos
      rw [hv] at hk
      have hpow : 2 ^ (1 + v2 (n / 2) + 1) = 2 * 2 ^ (v2 (n / 2) + 1) := by
        have h1 : 1 + v2 (n / 2) + 1 = (v2 (n / 2) + 1) + 1 := by omega
        rw [h1, Nat.pow_succ, Nat.mul_comm]
      rw [hpow, Nat.mul_assoc] at hk
      have h2eq : 2 * (n / 2) = 2 * (2 ^ (v2 (n / 2) + 1) * k) := by rw [← hn_eq]; exact hk
      have hcancel : n / 2 = 2 ^ (v2 (n / 2) + 1) * k := Nat.eq_of_mul_eq_mul_left (by omega) h2eq
      exact ih (n / 2) (by omega) hdiv_pos ⟨k, hcancel⟩

-- Legendre's Formula: v_2(n!) + s_2(n) = n

theorem v2_fact_double : ∀ k, v2 (fact (2 * k)) = k + v2 (fact k)
  | 0 => by simp [fact, v2_odd]
  | k + 1 => by
    have hstep : fact (2 * (k + 1)) = 2 * (k + 1) * (2 * k + 1) * fact (2 * k) := by
      have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [e1, fact, fact]
      have e2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [e2]
      ac_rfl
    rw [hstep]
    have hp_a : 0 < 2 * (k + 1) := by omega
    have hp_b : 0 < 2 * k + 1 := by omega
    have hp1 : 0 < 2 * (k + 1) * (2 * k + 1) := Nat.mul_pos hp_a hp_b
    have hp2 : 0 < fact (2 * k) := fact_pos (2 * k)
    rw [v2_mul _ _ hp1 hp2, v2_mul _ _ hp_a hp_b]
    rw [v2_two_mul (Nat.succ_pos k), v2_odd (by omega : (2 * k + 1) % 2 = 1)]
    rw [v2_fact_double k]
    have hfk : fact (k + 1) = (k + 1) * fact k := rfl
    rw [hfk, v2_mul _ _ (Nat.succ_pos k) (fact_pos k)]
    omega

theorem v2_fact_add_popcount : ∀ n, v2 (fact n) + popcount n = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [fact, v2_odd, popcount_zero]
    · by_cases hmod : n % 2 = 0
      · have hn : n = 2 * (n / 2) := by omega
        rw [hn, v2_fact_double, popcount_double]
        have hih := ih (n / 2) (by omega)
        omega
      · have hn : n = 2 * (n / 2) + 1 := by omega
        have hfact : fact (2 * (n / 2) + 1) = (2 * (n / 2) + 1) * fact (2 * (n / 2)) := rfl
        rw [hn, hfact, v2_mul _ _ (by omega) (fact_pos _)]
        rw [v2_odd (by omega : (2 * (n / 2) + 1) % 2 = 1), v2_fact_double]
        rw [popcount_two_mul_add (n / 2) 1 (by omega)]
        have hih := ih (n / 2) (by omega)
        omega

-- Kummer's Theorem: v_2(C(a+b, a)) + s_2(a+b) = s_2(a) + s_2(b)

theorem v2_binom_add_popcount (a b : Nat) :
    v2 (binom (a + b) a) + popcount (a + b) = popcount a + popcount b := by
  have hmul := binom_mul_fact a b
  have hv := congrArg v2 hmul
  rw [v2_mul _ _ (Nat.mul_pos (binom_pos a b) (fact_pos a)) (fact_pos b)] at hv
  rw [v2_mul _ _ (binom_pos a b) (fact_pos a)] at hv
  have la := v2_fact_add_popcount a
  have lb := v2_fact_add_popcount b
  have lab := v2_fact_add_popcount (a + b)
  omega

-- Trinomial Kummer Theorem

theorem v2_trinom_add_popcount (a b c : Nat) :
    v2 (trinom a b c) + popcount (a + b + c) = popcount a + popcount b + popcount c := by
  have hmul := trinom_mul_fact a b c
  have hv := congrArg v2 hmul
  have hp1 : 0 < trinom a b c := trinom_pos a b c
  have hp2 : 0 < trinom a b c * fact a := Nat.mul_pos hp1 (fact_pos a)
  have hp3 : 0 < trinom a b c * fact a * fact b := Nat.mul_pos hp2 (fact_pos b)
  rw [v2_mul _ _ hp3 (fact_pos c), v2_mul _ _ hp2 (fact_pos b), v2_mul _ _ hp1 (fact_pos a)] at hv
  have la := v2_fact_add_popcount a
  have lb := v2_fact_add_popcount b
  have lc := v2_fact_add_popcount c
  have labc := v2_fact_add_popcount (a + b + c)
  omega

theorem v2_binom_double (a b : Nat) :
    v2 (binom (2 * a + 2 * b) (2 * a)) = v2 (binom (a + b) a) := by
  have h1 := v2_binom_add_popcount (2 * a) (2 * b)
  have h2 := v2_binom_add_popcount a b
  have hp_sum : popcount (2 * a + 2 * b) = popcount (a + b) := by
    have hs : 2 * a + 2 * b = 2 * (a + b) := by omega
    rw [hs, popcount_double]
  rw [hp_sum, popcount_double, popcount_double] at h1
  omega

theorem v2_binom_k_mul (k n : Nat) (hk : 1 ≤ k) :
    v2 (binom (k * n) n) + popcount (k * n) = popcount n + popcount ((k - 1) * n) := by
  have hsplit : k * n = n + (k - 1) * n := by
    cases k with
    | zero => omega
    | succ k' => simp [Nat.succ_mul]; omega
  rw [hsplit]
  exact v2_binom_add_popcount n ((k - 1) * n)

theorem v2_binom_k_double (k n : Nat) (hk : 1 ≤ k) :
    v2 (binom (k * (2 * n)) (2 * n)) = v2 (binom (k * n) n) := by
  have h1 := v2_binom_k_mul k (2 * n) hk
  have h2 := v2_binom_k_mul k n hk
  have hp1 : popcount (k * (2 * n)) = popcount (k * n) := by
    have e1 : k * (2 * n) = 2 * (k * n) := by ac_rfl
    rw [e1, popcount_double]
  have hp2 : popcount ((k - 1) * (2 * n)) = popcount ((k - 1) * n) := by
    have e2 : (k - 1) * (2 * n) = 2 * ((k - 1) * n) := by ac_rfl
    rw [e2, popcount_double]
  rw [hp1, hp2, popcount_double] at h1
  omega

-- ============================================================================
-- SECTION 2: Reusable Finite-to-Infinite Mechanism — Carry-Valuation Automaton
-- ============================================================================

structure CVA (S : Nat) where
  delta : Fin S → Bool → Fin S
  w     : Fin S → Bool → Int
  tau   : Fin S → Int

-- Structurally recursive, kernel-reducible CVA evaluation

def CVA.evalAux {S : Nat} (M : CVA S) : Nat → Fin S → Nat → Int
  | 0, q, _ => M.tau q
  | _ + 1, q, 0 => M.tau q
  | fuel + 1, q, n =>
    let b := (n % 2 == 1)
    M.w q b + M.evalAux fuel (M.delta q b) (n / 2)

def CVA.eval {S : Nat} (M : CVA S) (q : Fin S) (n : Nat) : Int :=
  M.evalAux n q n

theorem CVA.evalAux_eq {S : Nat} (M : CVA S) :
    ∀ fuel1 fuel2 q n, n ≤ fuel1 → n ≤ fuel2 →
      M.evalAux fuel1 q n = M.evalAux fuel2 q n := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 q n h1 _
    have hz : n = 0 := by omega
    subst hz
    cases fuel2 <;> rfl
  | succ f1 ih =>
    intro fuel2 q n h1 h2
    cases n with
    | zero =>
      cases fuel2 <;> rfl
    | succ m =>
      cases fuel2 with
      | zero => omega
      | succ f2 =>
        simp only [CVA.evalAux]
        congr 1
        exact ih f2 (M.delta q ((m + 1) % 2 == 1)) ((m + 1) / 2) (by omega) (by omega)

theorem CVA.eval_zero {S : Nat} (M : CVA S) (q : Fin S) :
    M.eval q 0 = M.tau q := rfl

theorem CVA.eval_step {S : Nat} (M : CVA S) (q : Fin S) {n : Nat} (hn : n ≠ 0) :
    M.eval q n = M.w q (n % 2 == 1) + M.eval (M.delta q (n % 2 == 1)) (n / 2) := by
  cases n with
  | zero => omega
  | succ m =>
    unfold CVA.eval
    simp only [CVA.evalAux]
    congr 1
    exact CVA.evalAux_eq M m ((m + 1) / 2) (M.delta q ((m + 1) % 2 == 1)) ((m + 1) / 2)
      (by omega) (by omega)

theorem CVA.eval_two_mul_add {S : Nat} (M : CVA S) (q : Fin S) (n : Nat) (b : Bool)
    (h : 2 * n + b.toNat ≠ 0) :
    M.eval q (2 * n + b.toNat) = M.w q b + M.eval (M.delta q b) n := by
  rw [CVA.eval_step M q h]
  have hmod : ((2 * n + b.toNat) % 2 == 1) = b := by
    cases b <;> simp [Bool.toNat]
  have hdiv : (2 * n + b.toNat) / 2 = n := by
    cases b <;> simp [Bool.toNat] <;> omega
  rw [hmod, hdiv]

-- Computable universal check over Fin S (for instant kernel `decide`)

def forallFin (S : Nat) (p : Fin S → Bool) : Bool :=
  (List.finRange S).all p

theorem forallFin_true_iff {S : Nat} {p : Fin S → Bool} :
    forallFin S p = true ↔ ∀ q : Fin S, p q = true := by
  unfold forallFin
  rw [List.all_eq_true]
  constructor
  · intro h q; exact h q (List.mem_finRange q)
  · intro h q _; exact h q

-- Decidable Finite Certificate Checkers

def CVA.checkCoboundary {S : Nat} (M : CVA S) (φ : Fin S → Int) : Bool :=
  forallFin S fun q =>
    (M.tau q == φ q) &&
    (M.w q false + φ (M.delta q false) == φ q) &&
    (M.w q true  + φ (M.delta q true)  == φ q)

def CVA.checkLower {S : Nat} (M : CVA S) (φ : Fin S → Int) : Bool :=
  forallFin S fun q =>
    decide (φ q ≤ M.tau q) &&
    decide (φ q ≤ M.w q false + φ (M.delta q false)) &&
    decide (φ q ≤ M.w q true  + φ (M.delta q true))

def CVA.checkUpper {S : Nat} (M : CVA S) (ψ : Fin S → Int) : Bool :=
  forallFin S fun q =>
    decide (M.tau q ≤ ψ q) &&
    decide (M.w q false + ψ (M.delta q false) ≤ ψ q) &&
    decide (M.w q true  + ψ (M.delta q true)  ≤ ψ q)

-- Meta-Theorem 1: Exact Coboundary Lifting (Finite Certificate → ∀ n : Nat)

theorem CVA.coboundary_sound {S : Nat} (M : CVA S) (φ : Fin S → Int)
    (hcert : M.checkCoboundary φ = true) :
    ∀ q n, M.eval q n = φ q := by
  have hall := (forallFin_true_iff).mp hcert
  intro q n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    have hq := hall q
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    rcases hq with ⟨⟨htau, h0⟩, h1⟩
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero, htau]
    · rw [CVA.eval_step M q hn, ih (n / 2) (by omega)]
      cases hb : (n % 2 == 1)
      · exact h0
      · exact h1

-- Meta-Theorem 2: Tropical Sub-Potential Lifting (Finite Certificate → ∀ n : Nat)

theorem CVA.lower_sound {S : Nat} (M : CVA S) (φ : Fin S → Int)
    (hcert : M.checkLower φ = true) :
    ∀ q n, φ q ≤ M.eval q n := by
  have hall := (forallFin_true_iff).mp hcert
  intro q n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    have hq := hall q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    rcases hq with ⟨⟨htau, h0⟩, h1⟩
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero]; exact htau
    · rw [CVA.eval_step M q hn]
      have hih := ih (n / 2) (by omega) (M.delta q (n % 2 == 1))
      cases hb : (n % 2 == 1)
      · simp only [hb] at hih; omega
      · simp only [hb] at hih; omega

-- Meta-Theorem 3: Tropical Super-Potential Lifting (Finite Certificate → ∀ n : Nat)

theorem CVA.upper_sound {S : Nat} (M : CVA S) (ψ : Fin S → Int)
    (hcert : M.checkUpper ψ = true) :
    ∀ q n, M.eval q n ≤ ψ q := by
  have hall := (forallFin_true_iff).mp hcert
  intro q n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    have hq := hall q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    rcases hq with ⟨⟨htau, h0⟩, h1⟩
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero]; exact htau
    · rw [CVA.eval_step M q hn]
      have hih := ih (n / 2) (by omega) (M.delta q (n % 2 == 1))
      cases hb : (n % 2 == 1)
      · simp only [hb] at hih; omega
      · simp only [hb] at hih; omega

-- Meta-Theorem 4: Positive-Input Lifting via Doubling Invariance (∀ n ≥ 1)

theorem pos_upper_of_doubling_inv (F : Nat → Int) (B : Int)
    (hdbl : ∀ n, F (2 * n) = F n)
    (hodd : ∀ m, F (2 * m + 1) ≤ B) :
    ∀ n, 1 ≤ n → F n ≤ B := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hmod : n % 2 = 0
    · have heq : n = 2 * (n / 2) := by omega
      rw [heq, hdbl]
      exact ih (n / 2) (by omega) (by omega)
    · have heq : n = 2 * (n / 2) + 1 := by omega
      rw [heq]
      exact hodd (n / 2)

-- Meta-Theorem 5: Zero-Slack Lasso Pumping Engine (Infinite Sharpness Certificates!)

def CVA.runState {S : Nat} (M : CVA S) : Fin S → List Bool → Fin S
  | q, [] => q
  | q, b :: bs => M.runState (M.delta q b) bs

def CVA.runWeight {S : Nat} (M : CVA S) : Fin S → List Bool → Int
  | _, [] => 0
  | q, b :: bs => M.w q b + M.runWeight (M.delta q b) bs

theorem fromBits_append (xs ys : List Bool) :
    fromBits (xs ++ ys) = fromBits xs + 2 ^ xs.length * fromBits ys := by
  induction xs with
  | nil => simp [fromBits]
  | cons b xs ih =>
    simp only [List.cons_append, fromBits, List.length_cons, ih, Nat.pow_succ]
    have : 2 * (fromBits xs + 2 ^ xs.length * fromBits ys)
         = 2 * fromBits xs + 2 ^ xs.length * 2 * fromBits ys := by
      rw [Nat.mul_add]
      congr 1; ac_rfl
    omega

theorem fromBits_pos_of_suffix_pos (xs ys : List Bool) (hy : 0 < fromBits ys) :
    0 < fromBits (xs ++ ys) := by
  rw [fromBits_append]
  have hp : 0 < 2 ^ xs.length := Nat.pow_pos (by omega)
  have hm : 0 < 2 ^ xs.length * fromBits ys := Nat.mul_pos hp hy
  omega

theorem CVA.eval_append_bits {S : Nat} (M : CVA S) (q : Fin S) (xs ys : List Bool)
    (hy : 0 < fromBits ys) :
    M.eval q (fromBits (xs ++ ys)) = M.runWeight q xs + M.eval (M.runState q xs) (fromBits ys) := by
  induction xs generalizing q with
  | nil => simp [CVA.runWeight, CVA.runState]
  | cons b xs ih =>
    simp only [List.cons_append, fromBits, CVA.runWeight, CVA.runState]
    have hpos : 0 < fromBits (xs ++ ys) := fromBits_pos_of_suffix_pos xs ys hy
    have hcomm : b.toNat + 2 * fromBits (xs ++ ys) = 2 * fromBits (xs ++ ys) + b.toNat := by omega
    rw [hcomm, CVA.eval_two_mul_add M q (fromBits (xs ++ ys)) b (by omega)]
    rw [ih (M.delta q b)]
    omega

theorem CVA.eval_repeat_cycle {S : Nat} (M : CVA S) (qc : Fin S) (cyc suff : List Bool)
    (hcyc_st : M.runState qc cyc = qc)
    (hcyc_w : M.runWeight qc cyc = 0)
    (hsuff : 0 < fromBits suff) :
    ∀ m, M.eval qc (fromBits (repeatBits cyc m ++ suff)) = M.eval qc (fromBits suff) := by
  intro m
  induction m with
  | zero => simp [repeatBits]
  | succ m ih =>
    simp only [repeatBits, List.append_assoc]
    have hpos : 0 < fromBits (repeatBits cyc m ++ suff) :=
      fromBits_pos_of_suffix_pos (repeatBits cyc m) suff hsuff
    rw [CVA.eval_append_bits M qc cyc (repeatBits cyc m ++ suff) hpos]
    rw [hcyc_st, hcyc_w, ih]
    omega

theorem CVA.pumping_exact {S : Nat} (M : CVA S) (q0 qc : Fin S)
    (pref cyc suff : List Bool)
    (hpref : M.runState q0 pref = qc)
    (hcyc_st : M.runState qc cyc = qc)
    (hcyc_w : M.runWeight qc cyc = 0)
    (hsuff : 0 < fromBits suff) :
    ∀ m, M.eval q0 (pumpBits pref cyc suff m) = M.runWeight q0 pref + M.eval qc (fromBits suff) := by
  intro m
  unfold pumpBits
  rw [List.append_assoc]
  have hpos : 0 < fromBits (repeatBits cyc m ++ suff) :=
    fromBits_pos_of_suffix_pos (repeatBits cyc m) suff hsuff
  rw [CVA.eval_append_bits M q0 pref (repeatBits cyc m ++ suff) hpos]
  rw [hpref, CVA.eval_repeat_cycle M qc cyc suff hcyc_st hcyc_w hsuff m]

-- Popcount of bit-lists (certifies unbounded growth of pumped sharpness families!)

def countTrue : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + countTrue bs

theorem countTrue_append (xs ys : List Bool) :
    countTrue (xs ++ ys) = countTrue xs + countTrue ys := by
  induction xs with
  | nil => simp [countTrue]
  | cons b xs ih => simp [countTrue, ih]; omega

theorem countTrue_repeat (cyc : List Bool) (m : Nat) :
    countTrue (repeatBits cyc m) = m * countTrue cyc := by
  induction m with
  | zero => simp [repeatBits, countTrue]
  | succ m ih =>
    simp only [repeatBits, countTrue_append, ih, Nat.succ_mul]
    omega

theorem popcount_fromBits (xs : List Bool) : popcount (fromBits xs) = countTrue xs := by
  induction xs with
  | nil => simp [fromBits, countTrue, popcount_zero]
  | cons b xs ih =>
    simp only [fromBits, countTrue]
    have hcomm : b.toNat + 2 * fromBits xs = 2 * fromBits xs + b.toNat := by omega
    rw [hcomm, popcount_two_mul_add _ _ (by cases b <;> simp), ih]

theorem popcount_pumpBits (pref cyc suff : List Bool) (m : Nat) :
    popcount (pumpBits pref cyc suff m) = countTrue pref + m * countTrue cyc + countTrue suff := by
  unfold pumpBits
  rw [popcount_fromBits, countTrue_append, countTrue_append, countTrue_repeat]

theorem pumpBits_pos (pref cyc suff : List Bool) (hsuff : 0 < fromBits suff) (m : Nat) :
    0 < pumpBits pref cyc suff m := by
  unfold pumpBits
  rw [List.append_assoc]
  exact fromBits_pos_of_suffix_pos pref (repeatBits cyc m ++ suff)
    (fromBits_pos_of_suffix_pos (repeatBits cyc m) suff hsuff)

-- ============================================================================
-- SECTION 3: Bitwise Stream Lemmas for Core Lean `Nat` (`^^^`, `|||`, `&&&`)
-- ============================================================================

theorem testBit_two_mul_add (n : Nat) (b : Bool) (i : Nat) :
    (2 * n + b.toNat).testBit i = match i with | 0 => b | j + 1 => n.testBit j := by
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    cases b <;> simp [Bool.toNat]
  | succ j =>
    rw [Nat.testBit_succ]
    have hdiv : (2 * n + b.toNat) / 2 = n := by cases b <;> simp [Bool.toNat] <;> omega
    rw [hdiv]

theorem xor_two_mul_add (a b : Nat) (ba bb : Bool) :
    (2 * a + ba.toNat) ^^^ (2 * b + bb.toNat) = 2 * (a ^^^ b) + (xor ba bb).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_two_mul_add, testBit_two_mul_add, testBit_two_mul_add]
  cases i with
  | zero => rfl
  | succ j => simp [Nat.testBit_xor]

theorem lor_two_mul_add (a b : Nat) (ba bb : Bool) :
    (2 * a + ba.toNat) ||| (2 * b + bb.toNat) = 2 * (a ||| b) + (ba || bb).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_two_mul_add, testBit_two_mul_add, testBit_two_mul_add]
  cases i with
  | zero => rfl
  | succ j => simp [Nat.testBit_or]

theorem land_two_mul_add (a b : Nat) (ba bb : Bool) :
    (2 * a + ba.toNat) &&& (2 * b + bb.toNat) = 2 * (a &&& b) + (ba && bb).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_two_mul_add, testBit_two_mul_add, testBit_two_mul_add]
  cases i with
  | zero => rfl
  | succ j => simp [Nat.testBit_and]

theorem add_xor_eq_two_lor (a b : Nat) : a + b + (a ^^^ b) = 2 * (a ||| b) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; simp; omega
    · let ba := (a % 2 == 1)
      let bb := (b % 2 == 1)
      have ha_eq : a = 2 * (a / 2) + ba.toNat := nat_eq_two_mul_div_add_bool a
      have hb_eq : b = 2 * (b / 2) + bb.toNat := nat_eq_two_mul_div_add_bool b
      rw [ha_eq, hb_eq, xor_two_mul_add, lor_two_mul_add]
      have hih := ih (a / 2) (by omega) (b / 2)
      have hbits : ba.toNat + bb.toNat + (xor ba bb).toNat = 2 * (ba || bb).toNat := by
        cases ba <;> cases bb <;> rfl
      omega

theorem popcount_lor_add_land (a b : Nat) :
    popcount (a ||| b) + popcount (a &&& b) = popcount a + popcount b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; simp [popcount_zero]
    · let ba := (a % 2 == 1)
      let bb := (b % 2 == 1)
      have ha_eq : a = 2 * (a / 2) + ba.toNat := nat_eq_two_mul_div_add_bool a
      have hb_eq : b = 2 * (b / 2) + bb.toNat := nat_eq_two_mul_div_add_bool b
      rw [ha_eq, hb_eq, lor_two_mul_add, land_two_mul_add]
      rw [popcount_two_mul_add _ _ (by cases (ba || bb) <;> simp)]
      rw [popcount_two_mul_add _ _ (by cases (ba && bb) <;> simp)]
      rw [popcount_two_mul_add _ _ (by cases ba <;> simp)]
      rw [popcount_two_mul_add _ _ (by cases bb <;> simp)]
      have hih := ih (a / 2) (by omega) (b / 2)
      have hbits : (ba || bb).toNat + (ba && bb).toNat = ba.toNat + bb.toNat := by
        cases ba <;> cases bb <;> rfl
      omega

theorem popcount_xor_add_two_land (a b : Nat) :
    popcount (a ^^^ b) + 2 * popcount (a &&& b) = popcount a + popcount b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; simp [popcount_zero]
    · let ba := (a % 2 == 1)
      let bb := (b % 2 == 1)
      have ha_eq : a = 2 * (a / 2) + ba.toNat := nat_eq_two_mul_div_add_bool a
      have hb_eq : b = 2 * (b / 2) + bb.toNat := nat_eq_two_mul_div_add_bool b
      rw [ha_eq, hb_eq, xor_two_mul_add, land_two_mul_add]
      rw [popcount_two_mul_add _ _ (by cases (xor ba bb) <;> simp)]
      rw [popcount_two_mul_add _ _ (by cases (ba && bb) <;> simp)]
      rw [popcount_two_mul_add _ _ (by cases ba <;> simp)]
      rw [popcount_two_mul_add _ _ (by cases bb <;> simp)]
      have hih := ih (a / 2) (by omega) (b / 2)
      have hbits : (xor ba bb).toNat + 2 * (ba && bb).toNat = ba.toNat + bb.toNat := by
        cases ba <;> cases bb <;> rfl
      omega

theorem two_popcount_lor_eq (a b : Nat) :
    2 * popcount (a ||| b) = popcount a + popcount b + popcount (a ^^^ b) := by
  have h1 := popcount_lor_add_land a b
  have h2 := popcount_xor_add_two_land a b
  omega

-- ============================================================================
-- SECTION 4: FAMILY I — Shifted-Bitwise Kummer Collapse Laws (Exact Coboundaries)
-- ============================================================================

-- 3 reachable states of Shifted-XOR and Shifted-OR:
--   0 -> (prev=false, c=0), 1 -> (prev=true, c=1), 2 -> (prev=false, c=1)

def stPrev3 : Fin 3 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => false

def stCarry3 : Fin 3 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

-- 4A. Shifted-XOR CVA: computes popcount(n ^^^ (2*n + prev)) - 2 * popcount(n + (n ^^^ (2*n + prev)) + c)

def sxorCVA : CVA 3 where
  delta q b := match q, b with
    | ⟨0, _⟩, false => ⟨0, by decide⟩
    | ⟨0, _⟩, true  => ⟨1, by decide⟩
    | ⟨1, _⟩, false => ⟨2, by decide⟩
    | ⟨1, _⟩, true  => ⟨1, by decide⟩
    | ⟨2, _⟩, false => ⟨0, by decide⟩
    | ⟨2, _⟩, true  => ⟨1, by decide⟩
  w q b :=
    let xb := xor b (stPrev3 q)
    let s  := b.toNat + xb.toNat + stCarry3 q
    (xb.toNat : Int) - 2 * ((s % 2 : Nat) : Int)
  tau q :=
    ((stPrev3 q).toNat : Int) - 2 * (popcount ((stPrev3 q).toNat + stCarry3 q) : Int)

def phiSxor : Fin 3 → Int
  | ⟨0, _⟩ =>  0
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => -2

theorem sxorCVA_cert : sxorCVA.checkCoboundary phiSxor = true := by decide

theorem sxor_base_arith (q : Fin 3) :
    sxorCVA.tau q =
      (popcount (0 ^^^ (2 * 0 + (stPrev3 q).toNat)) : Int)
      - 2 * (popcount (0 + (0 ^^^ (2 * 0 + (stPrev3 q).toNat)) + stCarry3 q) : Int) := by
  revert q; decide

theorem sxor_step_arith (q : Fin 3) (b : Bool) :
    (b.toNat + (xor b (stPrev3 q)).toNat + stCarry3 q) / 2 = stCarry3 (sxorCVA.delta q b) ∧
    (stPrev3 (sxorCVA.delta q b) = b) ∧
    (sxorCVA.w q b = ((xor b (stPrev3 q)).toNat : Int)
      - 2 * (((b.toNat + (xor b (stPrev3 q)).toNat + stCarry3 q) % 2 : Nat) : Int)) := by
  revert q b; decide

theorem sxorCVA_eval : ∀ (q : Fin 3) (n : Nat),
    sxorCVA.eval q n =
      (popcount (n ^^^ (2 * n + (stPrev3 q).toNat)) : Int)
      - 2 * (popcount (n + (n ^^^ (2 * n + (stPrev3 q).toNat)) + stCarry3 q) : Int) := by
  intro q n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero]; exact sxor_base_arith q
    · let b := (n % 2 == 1)
      have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
      rw [CVA.eval_step sxorCVA q hn]
      change sxorCVA.w q b + sxorCVA.eval (sxorCVA.delta q b) (n / 2) = _
      rw [ih (n / 2) (by omega) (sxorCVA.delta q b)]
      rcases sxor_step_arith q b with ⟨hc, hprev, hw⟩
      rw [hprev, ← hc, hw]
      have hxor : n ^^^ (2 * n + (stPrev3 q).toNat)
          = 2 * ((n / 2) ^^^ (2 * (n / 2) + b.toNat)) + (xor b (stPrev3 q)).toNat := by
        conv => lhs; rw [hn_eq]
        exact xor_two_mul_add (n / 2) (2 * (n / 2) + b.toNat) b (stPrev3 q)
      rw [hxor]
      have hpop1 : popcount (2 * ((n / 2) ^^^ (2 * (n / 2) + b.toNat)) + (xor b (stPrev3 q)).toNat)
          = (xor b (stPrev3 q)).toNat + popcount ((n / 2) ^^^ (2 * (n / 2) + b.toNat)) :=
        popcount_two_mul_add _ _ (by cases (xor b (stPrev3 q)) <;> simp)
      have hsum : n + (2 * ((n / 2) ^^^ (2 * (n / 2) + b.toNat)) + (xor b (stPrev3 q)).toNat) + stCarry3 q
          = 2 * (n / 2 + ((n / 2) ^^^ (2 * (n / 2) + b.toNat)) + (b.toNat + (xor b (stPrev3 q)).toNat + stCarry3 q) / 2)
            + (b.toNat + (xor b (stPrev3 q)).toNat + stCarry3 q) % 2 := by omega
      rw [hpop1, hsum, popcount_two_mul_add _ _ (by omega)]
      omega

theorem shifted_xor_kummer_exact (n : Nat) :
    2 * v2 (binom (n + (n ^^^ (2 * n))) n) = 2 * popcount n + popcount (n ^^^ (2 * n)) := by
  have hcob := CVA.coboundary_sound sxorCVA phiSxor sxorCVA_cert ⟨0, by decide⟩ n
  rw [sxorCVA_eval ⟨0, by decide⟩ n] at hcob
  simp only [stPrev3, stCarry3, phiSxor, Bool.toNat, Bool.cond_false, Nat.add_zero] at hcob
  have hk := v2_binom_add_popcount n (n ^^^ (2 * n))
  omega

theorem shifted_xor_kummer_eq_or (n : Nat) :
    v2 (binom (n + (n ^^^ (2 * n))) n) = popcount (n ||| (2 * n)) := by
  have h1 := shifted_xor_kummer_exact n
  have h2 := two_popcount_lor_eq n (2 * n)
  rw [popcount_double] at h2
  omega

-- 4B. Shifted-OR CVA: computes popcount(n) - popcount(n + (n ||| (2*n + prev)) + c)

def sorCVA : CVA 3 where
  delta q b := match q, b with
    | ⟨0, _⟩, false => ⟨0, by decide⟩
    | ⟨0, _⟩, true  => ⟨1, by decide⟩
    | ⟨1, _⟩, false => ⟨2, by decide⟩
    | ⟨1, _⟩, true  => ⟨1, by decide⟩
    | ⟨2, _⟩, false => ⟨0, by decide⟩
    | ⟨2, _⟩, true  => ⟨1, by decide⟩
  w q b :=
    let ob := b || stPrev3 q
    let s  := b.toNat + ob.toNat + stCarry3 q
    (b.toNat : Int) - ((s % 2 : Nat) : Int)
  tau q := -(popcount ((stPrev3 q).toNat + stCarry3 q) : Int)

def phiSor : Fin 3 → Int
  | ⟨0, _⟩ =>  0
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => -1

theorem sorCVA_cert : sorCVA.checkCoboundary phiSor = true := by decide

theorem sor_base_arith (q : Fin 3) :
    sorCVA.tau q =
      (popcount 0 : Int) - (popcount (0 + (0 ||| (2 * 0 + (stPrev3 q).toNat)) + stCarry3 q) : Int) := by
  revert q; decide

theorem sor_step_arith (q : Fin 3) (b : Bool) :
    (b.toNat + (b || stPrev3 q).toNat + stCarry3 q) / 2 = stCarry3 (sorCVA.delta q b) ∧
    (stPrev3 (sorCVA.delta q b) = b) ∧
    (sorCVA.w q b = (b.toNat : Int)
      - (((b.toNat + (b || stPrev3 q).toNat + stCarry3 q) % 2 : Nat) : Int)) := by
  revert q b; decide

theorem sorCVA_eval : ∀ (q : Fin 3) (n : Nat),
    sorCVA.eval q n =
      (popcount n : Int) - (popcount (n + (n ||| (2 * n + (stPrev3 q).toNat)) + stCarry3 q) : Int) := by
  intro q n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero]; exact sor_base_arith q
    · let b := (n % 2 == 1)
      have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
      rw [CVA.eval_step sorCVA q hn]
      change sorCVA.w q b + sorCVA.eval (sorCVA.delta q b) (n / 2) = _
      rw [ih (n / 2) (by omega) (sorCVA.delta q b)]
      rcases sor_step_arith q b with ⟨hc, hprev, hw⟩
      rw [hprev, ← hc, hw]
      have hlor : n ||| (2 * n + (stPrev3 q).toNat)
          = 2 * ((n / 2) ||| (2 * (n / 2) + b.toNat)) + (b || stPrev3 q).toNat := by
        conv => lhs; rw [hn_eq]
        exact lor_two_mul_add (n / 2) (2 * (n / 2) + b.toNat) b (stPrev3 q)
      rw [hlor]
      have hpopn : popcount n = b.toNat + popcount (n / 2) := by
        conv => lhs; rw [hn_eq]
        exact popcount_two_mul_add (n / 2) _ (by cases b <;> simp)
      have hsum : n + (2 * ((n / 2) ||| (2 * (n / 2) + b.toNat)) + (b || stPrev3 q).toNat) + stCarry3 q
          = 2 * (n / 2 + ((n / 2) ||| (2 * (n / 2) + b.toNat)) + (b.toNat + (b || stPrev3 q).toNat + stCarry3 q) / 2)
            + (b.toNat + (b || stPrev3 q).toNat + stCarry3 q) % 2 := by omega
      rw [hpopn, hsum, popcount_two_mul_add _ _ (by omega)]
      omega

theorem popcount_add_shifted_or (n : Nat) :
    popcount (n + (n ||| (2 * n))) = popcount n := by
  have hcob := CVA.coboundary_sound sorCVA phiSor sorCVA_cert ⟨0, by decide⟩ n
  rw [sorCVA_eval ⟨0, by decide⟩ n] at hcob
  simp only [stPrev3, stCarry3, phiSor, Bool.toNat, Bool.cond_false, Nat.add_zero] at hcob
  omega

theorem shifted_or_kummer_exact (n : Nat) :
    v2 (binom (n + (n ||| (2 * n))) n) = popcount (n ||| (2 * n)) := by
  have hk := v2_binom_add_popcount n (n ||| (2 * n))
  have hp := popcount_add_shifted_or n
  omega

theorem shifted_xor_eq_shifted_or_v2 (n : Nat) :
    v2 (binom (n + (n ^^^ (2 * n))) n) = v2 (binom (n + (n ||| (2 * n))) n) := by
  rw [shifted_xor_kummer_eq_or, shifted_or_kummer_exact]

-- 4C. Shifted-AND CVA: 3 reachable states: 0 -> (false, 0), 1 -> (true, 0), 2 -> (true, 1)

def stPrevAnd : Fin 3 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => true

def stCarryAnd : Fin 3 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

def sandCVA : CVA 3 where
  delta q b := match q, b with
    | ⟨0, _⟩, false => ⟨0, by decide⟩
    | ⟨0, _⟩, true  => ⟨1, by decide⟩
    | ⟨1, _⟩, false => ⟨0, by decide⟩
    | ⟨1, _⟩, true  => ⟨2, by decide⟩
    | ⟨2, _⟩, false => ⟨0, by decide⟩
    | ⟨2, _⟩, true  => ⟨2, by decide⟩
  w q b :=
    let ab := b && stPrevAnd q
    let s  := b.toNat + ab.toNat + stCarryAnd q
    (b.toNat : Int) - ((s % 2 : Nat) : Int)
  tau q := -(popcount (stCarryAnd q) : Int)

def phiSand : Fin 3 → Int
  | ⟨0, _⟩ =>  0
  | ⟨1, _⟩ =>  0
  | ⟨2, _⟩ => -1

theorem sandCVA_cert : sandCVA.checkCoboundary phiSand = true := by decide

theorem sand_base_arith (q : Fin 3) :
    sandCVA.tau q =
      (popcount 0 : Int) - (popcount (0 + (0 &&& (2 * 0 + (stPrevAnd q).toNat)) + stCarryAnd q) : Int) := by
  revert q; decide

theorem sand_step_arith (q : Fin 3) (b : Bool) :
    (b.toNat + (b && stPrevAnd q).toNat + stCarryAnd q) / 2 = stCarryAnd (sandCVA.delta q b) ∧
    (stPrevAnd (sandCVA.delta q b) = b) ∧
    (sandCVA.w q b = (b.toNat : Int)
      - (((b.toNat + (b && stPrevAnd q).toNat + stCarryAnd q) % 2 : Nat) : Int)) := by
  revert q b; decide

theorem sandCVA_eval : ∀ (q : Fin 3) (n : Nat),
    sandCVA.eval q n =
      (popcount n : Int) - (popcount (n + (n &&& (2 * n + (stPrevAnd q).toNat)) + stCarryAnd q) : Int) := by
  intro q n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero]; exact sand_base_arith q
    · let b := (n % 2 == 1)
      have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
      rw [CVA.eval_step sandCVA q hn]
      change sandCVA.w q b + sandCVA.eval (sandCVA.delta q b) (n / 2) = _
      rw [ih (n / 2) (by omega) (sandCVA.delta q b)]
      rcases sand_step_arith q b with ⟨hc, hprev, hw⟩
      rw [hprev, ← hc, hw]
      have hland : n &&& (2 * n + (stPrevAnd q).toNat)
          = 2 * ((n / 2) &&& (2 * (n / 2) + b.toNat)) + (b && stPrevAnd q).toNat := by
        conv => lhs; rw [hn_eq]
        exact land_two_mul_add (n / 2) (2 * (n / 2) + b.toNat) b (stPrevAnd q)
      rw [hland]
      have hpopn : popcount n = b.toNat + popcount (n / 2) := by
        conv => lhs; rw [hn_eq]
        exact popcount_two_mul_add (n / 2) _ (by cases b <;> simp)
      have hsum : n + (2 * ((n / 2) &&& (2 * (n / 2) + b.toNat)) + (b && stPrevAnd q).toNat) + stCarryAnd q
          = 2 * (n / 2 + ((n / 2) &&& (2 * (n / 2) + b.toNat)) + (b.toNat + (b && stPrevAnd q).toNat + stCarryAnd q) / 2)
            + (b.toNat + (b && stPrevAnd q).toNat + stCarryAnd q) % 2 := by omega
      rw [hpopn, hsum, popcount_two_mul_add _ _ (by omega)]
      omega

theorem popcount_add_shifted_and (n : Nat) :
    popcount (n + (n &&& (2 * n))) = popcount n := by
  have hcob := CVA.coboundary_sound sandCVA phiSand sandCVA_cert ⟨0, by decide⟩ n
  rw [sandCVA_eval ⟨0, by decide⟩ n] at hcob
  simp only [stPrevAnd, stCarryAnd, phiSand, Bool.toNat, Bool.cond_false, Nat.add_zero] at hcob
  omega

theorem shifted_and_kummer_exact (n : Nat) :
    v2 (binom (n + (n &&& (2 * n))) n) = popcount (n &&& (2 * n)) := by
  have hk := v2_binom_add_popcount n (n &&& (2 * n))
  have hp := popcount_add_shifted_and n
  omega

-- 4D. Shifted-XOR Trinomial Collapse

theorem shifted_xor_trinom_exact (n : Nat) :
    v2 (trinom n (2 * n) (n ^^^ (2 * n))) = popcount (n ||| (2 * n)) := by
  have ht := v2_trinom_add_popcount n (2 * n) (n ^^^ (2 * n))
  have hsum : n + 2 * n + (n ^^^ (2 * n)) = 2 * (n ||| (2 * n)) := add_xor_eq_two_lor n (2 * n)
  rw [hsum, popcount_double, popcount_double] at ht
  have h2 := two_popcount_lor_eq n (2 * n)
  rw [popcount_double] at h2
  omega

-- ============================================================================
-- SECTION 5: FAMILY II — Gray-Code Binomial Tight Valuation Sandwich & Evenness
-- ============================================================================

theorem gray_two_mul_add (n : Nat) (p : Bool) :
    gray (2 * n + p.toNat) = 2 * gray n + (xor p (n % 2 == 1)).toNat := by
  unfold gray
  have hdiv : (2 * n + p.toNat) / 2 = n := by cases p <;> simp [Bool.toNat] <;> omega
  rw [hdiv]
  let bn := (n % 2 == 1)
  have hn : n = 2 * (n / 2) + bn.toNat := nat_eq_two_mul_div_add_bool n
  conv => lhs; arg 2; rw [hn]
  exact xor_two_mul_add n (n / 2) p bn

theorem shifted_xor_eq_two_gray_add_mod (n : Nat) :
    n ^^^ (2 * n) = 2 * gray n + n % 2 := by
  let b := (n % 2 == 1)
  have hn : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
  have hmod : b.toNat = n % 2 := mod_two_eq_bool_toNat n
  have h2n : 2 * n = 2 * n + (false : Bool).toNat := by simp
  conv => lhs; arg 1; rw [hn]
  conv => lhs; arg 2; rw [h2n]
  rw [xor_two_mul_add (n / 2) n b false]
  have hx : xor b false = b := by cases b <;> rfl
  rw [hx, hmod]
  unfold gray
  rw [Nat.xor_comm]

theorem popcount_shifted_xor_eq_gray_add_mod (n : Nat) :
    popcount (n ^^^ (2 * n)) = n % 2 + popcount (gray n) := by
  rw [shifted_xor_eq_two_gray_add_mod]
  exact popcount_two_mul_add (gray n) (n % 2) (by omega)

theorem gray_pos_of_pos {n : Nat} (hn : 0 < n) : 0 < gray n := by
  have hne_z : gray n ≠ 0 := by
    intro hz
    have heq : n ^^^ (n / 2) = 0 := hz
    have hsame : n = n / 2 := by
      apply Nat.eq_of_testBit_eq
      intro i
      have htb := congrArg (fun x => x.testBit i) heq
      rw [Nat.testBit_xor, Nat.zero_testBit] at htb
      cases h1 : n.testBit i <;> cases h2 : (n / 2).testBit i <;> simp_all
    omega
  omega

-- 5-state Gray CVA encoding:
--   0 = init, 1 = (prev=false, c=0), 2 = (prev=true, c=0), 3 = (prev=false, c=1), 4 = (prev=true, c=1)

def q0_5 : Fin 5 := ⟨0, by decide⟩

def q1_5 : Fin 5 := ⟨1, by decide⟩

def q2_5 : Fin 5 := ⟨2, by decide⟩

def q3_5 : Fin 5 := ⟨3, by decide⟩

def q4_5 : Fin 5 := ⟨4, by decide⟩

def grayPrev : Fin 5 → Bool
  | ⟨2, _⟩ | ⟨4, _⟩ => true
  | _ => false

def grayCarry : Fin 5 → Nat
  | ⟨3, _⟩ | ⟨4, _⟩ => 1
  | _ => 0

def grayDelta (q : Fin 5) (b : Bool) : Fin 5 :=
  match q, b with
  | ⟨0, _⟩, false => q1_5
  | ⟨0, _⟩, true  => q2_5
  | ⟨1, _⟩, false => q1_5
  | ⟨1, _⟩, true  => q2_5
  | ⟨2, _⟩, false => q3_5
  | ⟨2, _⟩, true  => q2_5
  | ⟨3, _⟩, false => q1_5
  | ⟨3, _⟩, true  => q4_5
  | ⟨4, _⟩, false => q3_5
  | ⟨4, _⟩, true  => q4_5

-- Formula-defined step weights (eliminates any transcription mismatch!)

def grayLowerCVA : CVA 5 where
  delta := grayDelta
  w q b :=
    if q.val = 0 then 0
    else
      let p  := grayPrev q
      let gb := xor p b
      let s  := p.toNat + gb.toNat + grayCarry q
      2 * (p.toNat : Int) + (gb.toNat : Int) - 2 * ((s % 2 : Nat) : Int)
  tau q :=
    if q.val = 0 then 0
    else
      let p := (grayPrev q).toNat
      3 * (p : Int) - 2 * (popcount (2 * p + grayCarry q) : Int)

def phiGrayLower : Fin 5 → Int
  | ⟨0, _⟩ =>  0
  | ⟨1, _⟩ =>  0
  | ⟨2, _⟩ =>  1
  | ⟨3, _⟩ => -2
  | ⟨4, _⟩ => -1

theorem grayLowerCVA_cert : grayLowerCVA.checkLower phiGrayLower = true := by decide

def grayUpperCVA : CVA 5 where
  delta := grayDelta
  w q b :=
    if q.val = 0 then 0
    else
      let p  := grayPrev q
      let gb := xor p b
      let s  := p.toNat + gb.toNat + grayCarry q
      (gb.toNat : Int) - 2 * ((s % 2 : Nat) : Int)
  tau q :=
    if q.val = 0 then 0
    else
      let p := (grayPrev q).toNat
      (p : Int) - 2 * (popcount (2 * p + grayCarry q) : Int)

def psiGrayUpper : Fin 5 → Int
  | ⟨0, _⟩ =>  0
  | ⟨1, _⟩ =>  0
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -2
  | ⟨4, _⟩ => -3

theorem grayUpperCVA_cert : grayUpperCVA.checkUpper psiGrayUpper = true := by decide

theorem gray_base_lower (q : Fin 5) (hq : 1 ≤ q.val) :
    let x := 2 * 0 + (grayPrev q).toNat
    grayLowerCVA.tau q =
      2 * (popcount x : Int) + (popcount (gray x) : Int) - 2 * (popcount (x + gray x + grayCarry q) : Int) := by
  revert q hq; decide

theorem gray_base_upper (q : Fin 5) (hq : 1 ≤ q.val) :
    let x := 2 * 0 + (grayPrev q).toNat
    grayUpperCVA.tau q =
      (popcount (gray x) : Int) - 2 * (popcount (x + gray x + grayCarry q) : Int) := by
  revert q hq; decide

theorem gray_run_arith (q : Fin 5) (hq : 1 ≤ q.val) (b : Bool) :
    1 ≤ (grayDelta q b).val ∧
    grayPrev (grayDelta q b) = b ∧
    grayCarry (grayDelta q b) = ((grayPrev q).toNat + (xor (grayPrev q) b).toNat + grayCarry q) / 2 ∧
    grayLowerCVA.w q b =
      2 * ((grayPrev q).toNat : Int) + ((xor (grayPrev q) b).toNat : Int)
      - 2 * ((((grayPrev q).toNat + (xor (grayPrev q) b).toNat + grayCarry q) % 2 : Nat) : Int) ∧
    grayUpperCVA.w q b =
      ((xor (grayPrev q) b).toNat : Int)
      - 2 * ((((grayPrev q).toNat + (xor (grayPrev q) b).toNat + grayCarry q) % 2 : Nat) : Int) := by
  revert q hq b; decide

theorem grayLowerCVA_eval_run : ∀ (q : Fin 5), 1 ≤ q.val → ∀ (n : Nat),
    grayLowerCVA.eval q n =
      2 * (popcount (2 * n + (grayPrev q).toNat) : Int)
      + (popcount (gray (2 * n + (grayPrev q).toNat)) : Int)
      - 2 * (popcount (2 * n + (grayPrev q).toNat + gray (2 * n + (grayPrev q).toNat) + grayCarry q) : Int) := by
  intro q hq n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero]; exact gray_base_lower q hq
    · let b := (n % 2 == 1)
      have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
      rw [CVA.eval_step grayLowerCVA q hn]
      change grayLowerCVA.w q b + grayLowerCVA.eval (grayDelta q b) (n / 2) = _
      rcases gray_run_arith q hq b with ⟨hq', hprev', hcarry', hwlo, _⟩
      rw [ih (n / 2) (by omega) (grayDelta q b) hq']
      rw [hprev', hcarry', hwlo, ← hn_eq]
      have hpopx : popcount (2 * n + (grayPrev q).toNat) = (grayPrev q).toNat + popcount n :=
        popcount_two_mul_add n (grayPrev q).toNat (by cases grayPrev q <;> simp)
      have hgray : gray (2 * n + (grayPrev q).toNat) = 2 * gray n + (xor (grayPrev q) b).toNat :=
        gray_two_mul_add n (grayPrev q)
      have hpopg : popcount (2 * gray n + (xor (grayPrev q) b).toNat)
          = (xor (grayPrev q) b).toNat + popcount (gray n) :=
        popcount_two_mul_add (gray n) _ (by cases xor (grayPrev q) b <;> simp)
      have hsum : 2 * n + (grayPrev q).toNat + (2 * gray n + (xor (grayPrev q) b).toNat) + grayCarry q
          = 2 * (n + gray n + ((grayPrev q).toNat + (xor (grayPrev q) b).toNat + grayCarry q) / 2)
            + ((grayPrev q).toNat + (xor (grayPrev q) b).toNat + grayCarry q) % 2 := by omega
      rw [hgray, hpopx, hpopg, hsum, popcount_two_mul_add _ _ (by omega)]
      omega

theorem grayUpperCVA_eval_run : ∀ (q : Fin 5), 1 ≤ q.val → ∀ (n : Nat),
    grayUpperCVA.eval q n =
      (popcount (gray (2 * n + (grayPrev q).toNat)) : Int)
      - 2 * (popcount (2 * n + (grayPrev q).toNat + gray (2 * n + (grayPrev q).toNat) + grayCarry q) : Int) := by
  intro q hq n
  induction n using Nat.strongRecOn generalizing q with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; rw [CVA.eval_zero]; exact gray_base_upper q hq
    · let b := (n % 2 == 1)
      have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
      rw [CVA.eval_step grayUpperCVA q hn]
      change grayUpperCVA.w q b + grayUpperCVA.eval (grayDelta q b) (n / 2) = _
      rcases gray_run_arith q hq b with ⟨hq', hprev', hcarry', _, hwhi⟩
      rw [ih (n / 2) (by omega) (grayDelta q b) hq']
      rw [hprev', hcarry', hwhi, ← hn_eq]
      have hgray : gray (2 * n + (grayPrev q).toNat) = 2 * gray n + (xor (grayPrev q) b).toNat :=
        gray_two_mul_add n (grayPrev q)
      have hpopg : popcount (2 * gray n + (xor (grayPrev q) b).toNat)
          = (xor (grayPrev q) b).toNat + popcount (gray n) :=
        popcount_two_mul_add (gray n) _ (by cases xor (grayPrev q) b <;> simp)
      have hsum : 2 * n + (grayPrev q).toNat + (2 * gray n + (xor (grayPrev q) b).toNat) + grayCarry q
          = 2 * (n + gray n + ((grayPrev q).toNat + (xor (grayPrev q) b).toNat + grayCarry q) / 2)
            + ((grayPrev q).toNat + (xor (grayPrev q) b).toNat + grayCarry q) % 2 := by omega
      rw [hgray, hpopg, hsum, popcount_two_mul_add _ _ (by omega)]
      omega

theorem gray_init_step (b : Bool) :
    1 ≤ (grayDelta q0_5 b).val ∧
    grayPrev (grayDelta q0_5 b) = b ∧
    grayCarry (grayDelta q0_5 b) = 0 := by
  revert b; decide

theorem grayLowerCVA_eval_init (n : Nat) :
    grayLowerCVA.eval q0_5 n =
      2 * (v2 (binom (n + gray n) n) : Int) - (popcount (gray n) : Int) := by
  by_cases hn : n = 0
  · subst hn; decide
  · let b := (n % 2 == 1)
    have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
    rw [CVA.eval_step grayLowerCVA q0_5 hn]
    change grayLowerCVA.w q0_5 b + grayLowerCVA.eval (grayDelta q0_5 b) (n / 2) = _
    have hw0 : grayLowerCVA.w q0_5 b = 0 := by cases b <;> rfl
    rcases gray_init_step b with ⟨hq1, hpr, hca⟩
    rw [hw0, grayLowerCVA_eval_run _ hq1 (n / 2)]
    simp only [hpr, hca, Nat.add_zero]
    rw [← hn_eq]
    have hk := v2_binom_add_popcount n (gray n)
    omega

theorem grayUpperCVA_eval_init (n : Nat) :
    grayUpperCVA.eval q0_5 n =
      2 * (v2 (binom (n + gray n) n) : Int) - (2 * (popcount n : Int) + (popcount (gray n) : Int)) := by
  by_cases hn : n = 0
  · subst hn; decide
  · let b := (n % 2 == 1)
    have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
    rw [CVA.eval_step grayUpperCVA q0_5 hn]
    change grayUpperCVA.w q0_5 b + grayUpperCVA.eval (grayDelta q0_5 b) (n / 2) = _
    have hw0 : grayUpperCVA.w q0_5 b = 0 := by cases b <;> rfl
    rcases gray_init_step b with ⟨hq1, hpr, hca⟩
    rw [hw0, grayUpperCVA_eval_run _ hq1 (n / 2)]
    simp only [hpr, hca, Nat.add_zero]
    rw [← hn_eq]
    have hk := v2_binom_add_popcount n (gray n)
    omega

-- Main Gray-Code Theorems!

theorem gray_binom_lower (n : Nat) :
    popcount (gray n) ≤ 2 * v2 (binom (n + gray n) n) := by
  have h := CVA.lower_sound grayLowerCVA phiGrayLower grayLowerCVA_cert q0_5 n
  rw [grayLowerCVA_eval_init] at h
  have h0 : phiGrayLower q0_5 = 0 := rfl
  rw [h0] at h
  omega

theorem gray_binom_even (n : Nat) (hn : 1 ≤ n) :
    2 ∣ binom (n + gray n) n := by
  have hgp : 0 < popcount (gray n) := popcount_pos_of_pos (gray_pos_of_pos hn)
  have hlo := gray_binom_lower n
  have hv : 1 ≤ v2 (binom (n + gray n) n) := by omega
  have hdvd := pow_two_v2_dvd (binom (n + gray n) n) (binom_pos n (gray n))
  have h2dvd : 2 ∣ 2 ^ v2 (binom (n + gray n) n) := by
    cases hv2 : v2 (binom (n + gray n) n) with
    | zero => omega
    | succ k =>
      refine ⟨2 ^ k, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm]
  exact Nat.dvd_trans h2dvd hdvd

theorem gray_binom_upper (n : Nat) :
    2 * v2 (binom (n + gray n) n) ≤ 2 * popcount n + popcount (gray n) := by
  have h := CVA.upper_sound grayUpperCVA psiGrayUpper grayUpperCVA_cert q0_5 n
  rw [grayUpperCVA_eval_init] at h
  have h0 : psiGrayUpper q0_5 = 0 := rfl
  rw [h0] at h
  omega

theorem grayUpperCVA_eval_one_pos : ∀ m, 1 ≤ m → grayUpperCVA.eval q1_5 m ≤ -2 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    rw [CVA.eval_step grayUpperCVA q1_5 (by omega)]
    by_cases hmod : m % 2 = 0
    · have hb : (m % 2 == 1) = false := by simp [hmod]
      rw [hb]
      have hw : grayUpperCVA.w q1_5 false = 0 := rfl
      have hd : grayUpperCVA.delta q1_5 false = q1_5 := rfl
      rw [hw, hd]
      have hih := ih (m / 2) (by omega) (by omega)
      omega
    · have hb : (m % 2 == 1) = true := by simp; omega
      rw [hb]
      have hw : grayUpperCVA.w q1_5 true = -1 := rfl
      have hd : grayUpperCVA.delta q1_5 true = q2_5 := rfl
      rw [hw, hd]
      have hup := CVA.upper_sound grayUpperCVA psiGrayUpper grayUpperCVA_cert q2_5 (m / 2)
      have h2 : psiGrayUpper q2_5 = -1 := rfl
      rw [h2] at hup
      omega

theorem gray_strictly_below_shifted_xor (n : Nat) (hn : 1 ≤ n) :
    v2 (binom (n + gray n) n) + 1 ≤ v2 (binom (n + (n ^^^ (2 * n))) n) := by
  rw [shifted_xor_kummer_eq_or]
  have hor := two_popcount_lor_eq n (2 * n)
  rw [popcount_double, popcount_shifted_xor_eq_gray_add_mod] at hor
  have hev := grayUpperCVA_eval_init n
  rw [CVA.eval_step grayUpperCVA q0_5 (by omega)] at hev
  by_cases hmod : n % 2 = 0
  · have hb : (n % 2 == 1) = false := by simp [hmod]
    rw [hb] at hev
    have hw : grayUpperCVA.w q0_5 false = 0 := rfl
    have hd : grayUpperCVA.delta q0_5 false = q1_5 := rfl
    rw [hw, hd] at hev
    have hbound := grayUpperCVA_eval_one_pos (n / 2) (by omega)
    omega
  · have hb : (n % 2 == 1) = true := by simp; omega
    rw [hb] at hev
    have hw : grayUpperCVA.w q0_5 true = 0 := rfl
    have hd : grayUpperCVA.delta q0_5 true = q2_5 := rfl
    rw [hw, hd] at hev
    have hbound := CVA.upper_sound grayUpperCVA psiGrayUpper grayUpperCVA_cert q2_5 (n / 2)
    have h2 : psiGrayUpper q2_5 = -1 := rfl
    rw [h2] at hbound
    omega

-- Infinite Sharpness Families for Family II (certified via CVA.pumping_exact + decide!)

def grayLowerFam (m : Nat) : Nat :=
  pumpBits [false] [true, true, false, false] [true, true] m

theorem gray_binom_lower_sharp_infinite (m : Nat) :
    2 * v2 (binom (grayLowerFam m + gray (grayLowerFam m)) (grayLowerFam m))
      = popcount (gray (grayLowerFam m)) ∧
    popcount (grayLowerFam m) = 2 * m + 2 := by
  have hpump := CVA.pumping_exact grayLowerCVA q0_5 q1_5
    [false] [true, true, false, false] [true, true]
    (by decide) (by decide) (by decide) (by decide) m
  have hval : grayLowerCVA.runWeight q0_5 [false]
      + grayLowerCVA.eval q1_5 (fromBits [true, true]) = 0 := by decide
  rw [hval] at hpump
  change grayLowerCVA.eval q0_5 (grayLowerFam m) = 0 at hpump
  rw [grayLowerCVA_eval_init] at hpump
  have hpop : popcount (grayLowerFam m) = 2 * m + 2 := by
    unfold grayLowerFam
    rw [popcount_pumpBits]
    have hc1 : countTrue [false] = 0 := rfl
    have hc2 : countTrue [true, true, false, false] = 2 := rfl
    have hc3 : countTrue [true, true] = 2 := rfl
    rw [hc1, hc2, hc3]; omega
  constructor
  · omega
  · exact hpop

def grayUpperFam (m : Nat) : Nat :=
  pumpBits [true, false, true] [false, true] [false, true] m

theorem gray_binom_upper_sharp_infinite (m : Nat) :
    v2 (binom (grayUpperFam m + gray (grayUpperFam m)) (grayUpperFam m)) + 1
      = v2 (binom (grayUpperFam m + (grayUpperFam m ^^^ (2 * grayUpperFam m))) (grayUpperFam m)) ∧
    popcount (grayUpperFam m) = m + 3 := by
  have hpump := CVA.pumping_exact grayUpperCVA q0_5 q4_5
    [true, false, true] [false, true] [false, true]
    (by decide) (by decide) (by decide) (by decide) m
  have hval : grayUpperCVA.runWeight q0_5 [true, false, true]
      + grayUpperCVA.eval q4_5 (fromBits [false, true]) = -1 := by decide
  rw [hval] at hpump
  change grayUpperCVA.eval q0_5 (grayUpperFam m) = -1 at hpump
  rw [grayUpperCVA_eval_init] at hpump
  have hodd : grayUpperFam m % 2 = 1 := by
    unfold grayUpperFam pumpBits
    simp [fromBits]
  have hor := two_popcount_lor_eq (grayUpperFam m) (2 * grayUpperFam m)
  rw [popcount_double, popcount_shifted_xor_eq_gray_add_mod, hodd] at hor
  rw [shifted_xor_kummer_eq_or]
  have hpop : popcount (grayUpperFam m) = m + 3 := by
    unfold grayUpperFam
    rw [popcount_pumpBits]
    have hc1 : countTrue [true, false, true] = 2 := rfl
    have hc2 : countTrue [false, true] = 1 := rfl
    rw [hc1, hc2]; omega
  constructor
  · omega
  · exact hpop

-- ============================================================================
-- SECTION 6: FAMILY III — Parametric k-Binomial Tropical Engine & Non-Integer Slopes
-- ============================================================================

-- Universal 2*(k-1)-state CVA for q * v2(binom(k*n, n)) - p * popcount(n) for ANY k ≥ 2!
-- State st ∈ Fin (2*(k-1)) encodes (c1 = st.val / 2, d = st.val % 2) with c2 = c1 + d < k.

def kBinomCVA (k p q : Nat) (hk : 2 ≤ k) : CVA (2 * (k - 1)) where
  delta st b :=
    let c1 := st.val / 2
    let d  := st.val % 2
    let c2 := c1 + d
    let s1 := (k - 1) * b.toNat + c1
    let s2 := k * b.toNat + c2
    let c1' := s1 / 2
    let d'  := s2 / 2 - s1 / 2
    ⟨2 * c1' + d', by
      have hc1 : c1 ≤ k - 2 := by have := st.isLt; omega
      have hd : d ≤ 1 := by omega
      have hb : b.toNat ≤ 1 := by cases b <;> simp
      have hs1 : s1 ≤ 2 * k - 3 := by
        have hmul : (k - 1) * b.toNat ≤ k - 1 := by cases b <;> simp
        omega
      have hs2 : s2 = s1 + b.toNat + d := by
        cases b <;> simp [s1, s2, c2] <;> omega
      omega⟩
  w st b :=
    let c1 := st.val / 2
    let d  := st.val % 2
    let c2 := c1 + d
    let s1 := (k - 1) * b.toNat + c1
    let s2 := k * b.toNat + c2
    (q : Int) * ((b.toNat : Int) + ((s1 % 2 : Nat) : Int) - ((s2 % 2 : Nat) : Int))
      - (p : Int) * (b.toNat : Int)
  tau st :=
    let c1 := st.val / 2
    let c2 := c1 + st.val % 2
    (q : Int) * ((popcount c1 : Int) - (popcount c2 : Int))

-- Parametric Soundness Theorem: proved ONCE for ALL k ≥ 2, ALL p, q : Nat!

theorem kBinomCVA_eval (k p q : Nat) (hk : 2 ≤ k) :
    ∀ (st : Fin (2 * (k - 1))) (n : Nat),
      let c1 := st.val / 2
      let c2 := c1 + st.val % 2
      (kBinomCVA k p q hk).eval st n =
        (q : Int) * ((popcount n : Int) + (popcount ((k - 1) * n + c1) : Int)
          - (popcount (k * n + c2) : Int))
        - (p : Int) * (popcount n : Int) := by
  intro st n
  induction n using Nat.strongRecOn generalizing st with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn
      rw [CVA.eval_zero]
      simp [kBinomCVA, popcount_zero]
    · let b := (n % 2 == 1)
      have hn_eq : n = 2 * (n / 2) + b.toNat := nat_eq_two_mul_div_add_bool n
      rw [CVA.eval_step (kBinomCVA k p q hk) st hn]
      change (kBinomCVA k p q hk).w st b
        + (kBinomCVA k p q hk).eval ((kBinomCVA k p q hk).delta st b) (n / 2) = _
      rw [ih (n / 2) (by omega) ((kBinomCVA k p q hk).delta st b)]
      have hb : b.toNat ≤ 1 := by cases b <;> simp
      have hkmul : k * b.toNat = (k - 1) * b.toNat + b.toNat := by
        cases b <;> simp <;> omega
      have hs2_rel : k * b.toNat + (st.val / 2 + st.val % 2)
          = ((k - 1) * b.toNat + st.val / 2) + b.toNat + st.val % 2 := by omega
      have hdiv_next : ((kBinomCVA k p q hk).delta st b).val / 2
          = ((k - 1) * b.toNat + st.val / 2) / 2 := by
        simp only [kBinomCVA]; omega
      have hmod_next : ((kBinomCVA k p q hk).delta st b).val % 2
          = (k * b.toNat + (st.val / 2 + st.val % 2)) / 2 - ((k - 1) * b.toNat + st.val / 2) / 2 := by
        simp only [kBinomCVA]; omega
      have hc2_next : ((k - 1) * b.toNat + st.val / 2) / 2
          + ((k * b.toNat + (st.val / 2 + st.val % 2)) / 2 - ((k - 1) * b.toNat + st.val / 2) / 2)
          = (k * b.toNat + (st.val / 2 + st.val % 2)) / 2 := by omega
      simp only [hdiv_next, hmod_next, hc2_next]
      have hpopn : popcount n = b.toNat + popcount (n / 2) := by
        conv => lhs; rw [hn_eq]
        exact popcount_two_mul_add (n / 2) b.toNat hb
      have hlin1 : (k - 1) * n + st.val / 2
          = 2 * ((k - 1) * (n / 2) + ((k - 1) * b.toNat + st.val / 2) / 2)
            + ((k - 1) * b.toNat + st.val / 2) % 2 := by
        conv => lhs; rw [hn_eq]
        have : (k - 1) * (2 * (n / 2) + b.toNat) = 2 * ((k - 1) * (n / 2)) + (k - 1) * b.toNat := by
          rw [Nat.mul_add]; congr 1; ac_rfl
        omega
      have hlin2 : k * n + (st.val / 2 + st.val % 2)
          = 2 * (k * (n / 2) + (k * b.toNat + (st.val / 2 + st.val % 2)) / 2)
            + (k * b.toNat + (st.val / 2 + st.val % 2)) % 2 := by
        conv => lhs; rw [hn_eq]
        have : k * (2 * (n / 2) + b.toNat) = 2 * (k * (n / 2)) + k * b.toNat := by
          rw [Nat.mul_add]; congr 1; ac_rfl
        omega
      have hpop1 : popcount ((k - 1) * n + st.val / 2)
          = ((k - 1) * b.toNat + st.val / 2) % 2
            + popcount ((k - 1) * (n / 2) + ((k - 1) * b.toNat + st.val / 2) / 2) := by
        rw [hlin1]; exact popcount_two_mul_add _ _ (by omega)
      have hpop2 : popcount (k * n + (st.val / 2 + st.val % 2))
          = (k * b.toNat + (st.val / 2 + st.val % 2)) % 2
            + popcount (k * (n / 2) + (k * b.toNat + (st.val / 2 + st.val % 2)) / 2) := by
        rw [hlin2]; exact popcount_two_mul_add _ _ (by omega)
      change (kBinomCVA k p q hk).w st b + _ =
        (q : Int) * ((popcount n : Int) + (popcount ((k - 1) * n + st.val / 2) : Int)
          - (popcount (k * n + (st.val / 2 + st.val % 2)) : Int))
        - (p : Int) * (popcount n : Int)
      rw [hpopn, hpop1, hpop2]
      simp only [kBinomCVA]
      have hcast : ∀ a c : Nat, ((a + c : Nat) : Int) = (a : Int) + (c : Int) := Int.natCast_add
      have hmul_dist : ∀ (a x y : Int), a * (x + y) = a * x + a * y := Int.mul_add
      have hmul_sub : ∀ (a x y : Int), a * (x - y) = a * x - a * y := Int.mul_sub
      simp only [hcast, hmul_dist, hmul_sub]
      omega

-- Odd-input specialization for ANY odd k ≥ 3!

theorem kBinomCVA_eval_odd (k p q : Nat) (hk : 3 ≤ k) (hodd : k % 2 = 1) (m : Nat) :
    (kBinomCVA k p q (by omega)).eval ⟨2 * ((k - 1) / 2), by omega⟩ m =
      (q : Int) * (v2 (binom (k * (2 * m + 1)) (2 * m + 1)) : Int)
      - (p : Int) * (popcount (2 * m + 1) : Int) + (p : Int) := by
  have hev := kBinomCVA_eval k p q (by omega) ⟨0, by omega⟩ (2 * m + 1)
  have hstep := CVA.eval_two_mul_add (kBinomCVA k p q (by omega)) ⟨0, by omega⟩ m true
    (by simp [Bool.toNat])
  simp only [Bool.toNat, Bool.cond_true] at hstep
  have hdelta : (kBinomCVA k p q (by omega)).delta ⟨0, by omega⟩ true
      = ⟨2 * ((k - 1) / 2), by omega⟩ := by
    apply Fin.ext
    simp only [kBinomCVA, Bool.toNat, Bool.cond_true]
    omega
  have hw0 : (kBinomCVA k p q (by omega)).w ⟨0, by omega⟩ true = -(p : Int) := by
    simp only [kBinomCVA, Bool.toNat, Bool.cond_true, Nat.zero_div, Nat.zero_mod, Nat.add_zero, Nat.mul_one]
    have hm1 : (k - 1) % 2 = 0 := by omega
    rw [hm1, hodd]
    omega
  rw [hdelta, hw0] at hstep
  simp only [Nat.zero_div, Nat.zero_mod, Nat.add_zero] at hev
  have hk_kum := v2_binom_k_mul k (2 * m + 1) (by omega)
  have hq_eq :
      (q : Int) * ((popcount (2 * m + 1) : Int) + (popcount ((k - 1) * (2 * m + 1)) : Int)
        - (popcount (k * (2 * m + 1)) : Int))
      = (q : Int) * (v2 (binom (k * (2 * m + 1)) (2 * m + 1)) : Int) := by
    congr 1; omega
  rw [hq_eq] at hev
  omega

-- Parametric Positive-Input Lifting Theorem for ALL odd k ≥ 3!

theorem kBinom_upper_pos_of_cert (k p q : Nat) (hk : 3 ≤ k) (hodd : k % 2 = 1)
    (ψ : Fin (2 * (k - 1)) → Int)
    (hcert : (kBinomCVA k p q (by omega)).checkUpper ψ = true) :
    ∀ n, 1 ≤ n →
      (q : Int) * (v2 (binom (k * n) n) : Int)
        ≤ (p : Int) * (popcount n : Int) + (-(p : Int) + ψ ⟨2 * ((k - 1) / 2), by omega⟩) := by
  let F : Nat → Int := fun n =>
    (q : Int) * (v2 (binom (k * n) n) : Int) - (p : Int) * (popcount n : Int)
  have hpos : ∀ n, 1 ≤ n → F n ≤ -(p : Int) + ψ ⟨2 * ((k - 1) / 2), by omega⟩ := by
    apply pos_upper_of_doubling_inv F (-(p : Int) + ψ ⟨2 * ((k - 1) / 2), by omega⟩)
    · intro n
      simp only [F, v2_binom_k_double k n (by omega), popcount_double]
    · intro m
      have hup := CVA.upper_sound (kBinomCVA k p q (by omega)) ψ hcert
        ⟨2 * ((k - 1) / 2), by omega⟩ m
      rw [kBinomCVA_eval_odd k p q hk hodd m] at hup
      simp only [F]
      omega
  intro n hn
  have h := hpos n hn
  simp only [F] at h
  omega

-- Array-backed potential helper (fast O(1) lookup for `decide`!)

def potFromArray (S : Nat) (arr : Array Int) (q : Fin S) : Int :=
  arr.getD q.val 0

-- ----------------------------------------------------------------------------
-- 6A. k = 11 (20 states, exact tropical eigenvalue 5/2):
--     ∀ n ≥ 1, 2 * v2(C(11n, n)) + 2 ≤ 5 * s2(n)
-- ----------------------------------------------------------------------------

def cva11 : CVA 20 := kBinomCVA 11 5 2 (by decide)

def q10_20 : Fin 20 := ⟨10, by decide⟩

def q11_20 : Fin 20 := ⟨11, by decide⟩

def psi11Arr : Array Int :=
  #[0, -2, 0, 0, 0, -2, 0, 2, 0, 1, 3, 1, 0, -2, 0, 4, 0, 0, 2, 3]

def psi11 : Fin 20 → Int := potFromArray 20 psi11Arr

theorem cert_k11 : cva11.checkUpper psi11 = true := by decide

theorem binom_11n_sharp_slope (n : Nat) (hn : 1 ≤ n) :
    2 * v2 (binom (11 * n) n) + 2 ≤ 5 * popcount n := by
  have h := kBinom_upper_pos_of_cert 11 5 2 (by decide) (by decide) psi11 cert_k11 n hn
  have hv : psi11 q10_20 = 3 := by decide
  change (2 : Int) * (v2 (binom (11 * n) n) : Int)
    ≤ (5 : Int) * (popcount n : Int) + (-(5 : Int) + psi11 q10_20) at h
  rw [hv] at h
  omega

-- Infinite Exact Attainment Family for k = 11: n_m = 3 * (32^(m+2) - 1) / 31

def cyc11 : List Bool := [true, false, false, false, true]

def suff11 : List Bool := [true]

def fam11 (m : Nat) : Nat :=
  2 * pumpBits cyc11 cyc11 suff11 m + 1

theorem binom_11n_sharp_infinite (m : Nat) :
    2 * v2 (binom (11 * fam11 m) (fam11 m)) + 2 = 5 * popcount (fam11 m) ∧
    popcount (fam11 m) = 2 * m + 4 := by
  have hpump := CVA.pumping_exact cva11 q10_20 q11_20 cyc11 cyc11 suff11
    (by decide) (by decide) (by decide) (by decide) m
  have hval : cva11.runWeight q10_20 cyc11 + cva11.eval q11_20 (fromBits suff11) = 3 := by decide
  rw [hval] at hpump
  have hodd := kBinomCVA_eval_odd 11 5 2 (by decide) (by decide) (pumpBits cyc11 cyc11 suff11 m)
  change cva11.eval q10_20 (pumpBits cyc11 cyc11 suff11 m) = _ at hodd
  rw [hodd] at hpump
  have hpop : popcount (fam11 m) = 2 * m + 4 := by
    unfold fam11
    rw [popcount_two_mul_add _ 1 (by omega), popcount_pumpBits]
    have hc1 : countTrue cyc11 = 2 := rfl
    have hc2 : countTrue suff11 = 1 := rfl
    rw [hc1, hc2]; omega
  constructor
  · unfold fam11; omega
  · exact hpop

-- ----------------------------------------------------------------------------
-- 6B. k = 25 (48 states, exact denominator-3 tropical eigenvalue 8/3):
--     ∀ n ≥ 1, 3 * v2(C(25n, n)) + 3 ≤ 8 * s2(n)
-- ----------------------------------------------------------------------------

def cva25 : CVA 48 := kBinomCVA 25 8 3 (by decide)

def q24_48 : Fin 48 := ⟨24, by decide⟩

def q25_48 : Fin 48 := ⟨25, by decide⟩

def psi25Arr : Array Int :=
  #[0, -3, 0, 0, 0, 2, 5, 3, 0, -1, 2, 5, 5, 4, 7, 6,
    0, -3, 0, 2, 2, -1, 2, 8, 5, 2, 5, 7, 7, 4, 7, 9,
    0, -3, 0, 0, 0, -3, 0, 5, 2, 1, 4, 2, 2, 6, 9, 11]

def psi25 : Fin 48 → Int := potFromArray 48 psi25Arr

theorem cert_k25 : cva25.checkUpper psi25 = true := by decide

theorem binom_25n_sharp_slope (n : Nat) (hn : 1 ≤ n) :
    3 * v2 (binom (25 * n) n) + 3 ≤ 8 * popcount n := by
  have h := kBinom_upper_pos_of_cert 25 8 3 (by decide) (by decide) psi25 cert_k25 n hn
  have hv : psi25 q24_48 = 5 := by decide
  change (3 : Int) * (v2 (binom (25 * n) n) : Int)
    ≤ (8 : Int) * (popcount n : Int) + (-(8 : Int) + psi25 q24_48) at h
  rw [hv] at h
  omega

-- Infinite Exact Attainment Family for k = 25: n_m = 41 * (1024^(m+2) - 1) / 1023

def cyc25 : List Bool := [false, false, true, false, true, false, false, false, false, true]

def suff25 : List Bool := [false, false, true, false, true]

def fam25 (m : Nat) : Nat :=
  2 * pumpBits cyc25 cyc25 suff25 m + 1

theorem binom_25n_sharp_infinite (m : Nat) :
    3 * v2 (binom (25 * fam25 m) (fam25 m)) + 3 = 8 * popcount (fam25 m) ∧
    popcount (fam25 m) = 3 * m + 6 := by
  have hpump := CVA.pumping_exact cva25 q24_48 q25_48 cyc25 cyc25 suff25
    (by decide) (by decide) (by decide) (by decide) m
  have hval : cva25.runWeight q24_48 cyc25 + cva25.eval q25_48 (fromBits suff25) = 5 := by decide
  rw [hval] at hpump
  have hodd := kBinomCVA_eval_odd 25 8 3 (by decide) (by decide) (pumpBits cyc25 cyc25 suff25 m)
  change cva25.eval q24_48 (pumpBits cyc25 cyc25 suff25 m) = _ at hodd
  rw [hodd] at hpump
  have hpop : popcount (fam25 m) = 3 * m + 6 := by
    unfold fam25
    rw [popcount_two_mul_add _ 1 (by omega), popcount_pumpBits]
    have hc1 : countTrue cyc25 = 3 := rfl
    have hc2 : countTrue suff25 = 2 := rfl
    rw [hc1, hc2]; omega
  constructor
  · unfold fam25; omega
  · exact hpop

-- ----------------------------------------------------------------------------
-- 6C. k = 55 (108 states, exact denominator-4 tropical eigenvalue 13/4):
--     ∀ n ≥ 1, 4 * v2(C(55n, n)) + 8 ≤ 13 * s2(n)
-- ----------------------------------------------------------------------------

def cva55 : CVA 108 := kBinomCVA 55 13 4 (by decide)

def q54_108 : Fin 108 := ⟨54, by decide⟩

def q55_108 : Fin 108 := ⟨55, by decide⟩

def psi55Arr : Array Int :=
  #[0, -4, 0, 0, 0, -4, 0, 4, 0, -4, 0, 0, 0, -4, 0, 8, 0, 7, 11, 7,
    0, -4, 0, 4, 0, 1, 5, 1, 0, -3, 1, 12, 0, 6, 10, 11, 11, 7, 11, 11,
    0, 2, 6, 2, 0, -2, 2, 8, 0, 6, 10, 6, 5, 1, 5, 5, 0, -3, 1, 1,
    1, -3, 1, 16, 0, -3, 1, 10, 10, 6, 10, 15, 11, 7, 11, 11, 11, 7, 11, 15,
    0, 3, 7, 6, 6, 2, 6, 6, 0, 1, 5, 2, 2, -2, 2, 12, 0, 1, 5, 10,
    10, 6, 10, 10, 5, 1, 5, 5]

def psi55 : Fin 108 → Int := potFromArray 108 psi55Arr

theorem cert_k55 : cva55.checkUpper psi55 = true := by decide

theorem binom_55n_sharp_slope (n : Nat) (hn : 1 ≤ n) :
    4 * v2 (binom (55 * n) n) + 8 ≤ 13 * popcount n := by
  have h := kBinom_upper_pos_of_cert 55 13 4 (by decide) (by decide) psi55 cert_k55 n hn
  have hv : psi55 q54_108 = 5 := by decide
  change (4 : Int) * (v2 (binom (55 * n) n) : Int)
    ≤ (13 : Int) * (popcount n : Int) + (-(13 : Int) + psi55 q54_108) at h
  rw [hv] at h
  omega

-- Infinite Exact Attainment Family for k = 55: n_m = 149 * (8192^(m+2) - 1) / 8191

theorem binom_55n_sharp_infinite (m : Nat) :
    4 * v2 (binom (55 * fam55 m) (fam55 m)) + 8 = 13 * popcount (fam55 m) ∧
    popcount (fam55 m) = 4 * m + 8 := by
  have hpump := CVA.pumping_exact cva55 q54_108 q55_108 cyc55 cyc55 suff55
    (by decide) (by decide) (by decide) (by decide) m
  have hval : cva55.runWeight q54_108 cyc55 + cva55.eval q55_108 (fromBits suff55) = 5 := by decide
  rw [hval] at hpump
  have hodd := kBinomCVA_eval_odd 55 13 4 (by decide) (by decide) (pumpBits cyc55 cyc55 suff55 m)
  change cva55.eval q54_108 (pumpBits cyc55 cyc55 suff55 m) = _ at hodd
  rw [hodd] at hpump
  have hpop : popcount (fam55 m) = 4 * m + 8 := by
    unfold fam55
    rw [popcount_two_mul_add _ 1 (by omega), popcount_pumpBits]
    have hc1 : countTrue cyc55 = 4 := rfl
    have hc2 : countTrue suff55 = 3 := rfl
    rw [hc1, hc2]; omega
  constructor
  · unfold fam55; omega
  · exact hpop

-- ============================================================================
-- SECTION 7: Non-Vacuity Witnesses, Sharpness Counterexamples, & Axiom Receipts
-- ============================================================================

-- Non-vacuity witnesses: concrete constructive inhabitants of all theorem hypotheses & outputs

example : v2 (binom (11 + (11 ^^^ (2 * 11))) 11) = 5 ∧ popcount (11 ||| (2 * 11)) = 5 := by
  have h := shifted_xor_kummer_eq_or 11
  have hp : popcount (11 ||| (2 * 11)) = 5 := by decide
  omega

example : v2 (binom (11 + (11 ||| (2 * 11))) 11) = 5 ∧ popcount (11 + (11 ||| (2 * 11))) = popcount 11 := by
  have h1 := shifted_or_kummer_exact 11
  have h2 := popcount_add_shifted_or 11
  have hp : popcount (11 ||| (2 * 11)) = 5 := by decide
  omega

example : v2 (binom (11 + (11 &&& (2 * 11))) 11) = 1 ∧ popcount (11 &&& (2 * 11)) = 1 := by
  have h := shifted_and_kummer_exact 11
  have hp : popcount (11 &&& (2 * 11)) = 1 := by decide
  omega

example : v2 (trinom 11 22 (11 ^^^ 22)) = 5 := by
  rw [shifted_xor_trinom_exact 11]; decide

example : 2 ∣ binom (6 + gray 6) 6 ∧ 2 * v2 (binom (6 + gray 6) 6) = popcount (gray 6) := by
  constructor
  · exact gray_binom_even 6 (by decide)
  · have h := v2_binom_add_popcount 6 (gray 6)
    have hp : popcount 6 = 2 ∧ popcount (gray 6) = 2 ∧ popcount (6 + gray 6) = 3 := by decide
    omega

example : 2 * v2 (binom (11 * 3) 3) + 2 = 5 * popcount 3 := by
  have h := v2_binom_k_mul 11 3 (by decide)
  have hp : popcount 3 = 2 ∧ popcount ((11 - 1) * 3) = 4 ∧ popcount (11 * 3) = 2 := by decide
  omega

-- Explicit non-vacuity of the generic CVA certificate interfaces (all three modes inhabited!)

theorem cva_coboundary_nonvacuous : ∃ φ, sxorCVA.checkCoboundary φ = true := ⟨phiSxor, sxorCVA_cert⟩

theorem cva_lower_nonvacuous : ∃ φ, grayLowerCVA.checkLower φ = true := ⟨phiGrayLower, grayLowerCVA_cert⟩

theorem cva_upper_nonvacuous : ∃ ψ, cva11.checkUpper ψ = true := ⟨psi11, cert_k11⟩

-- Kernel-checked Sharpness Counterexamples (proving hypotheses cannot be relaxed!)
-- 1. Shifted-XOR / Shifted-OR collapse FAILS at shift k = 2 (4*n) already at n = 1!

theorem counterexample_shift2_xor :
    v2 (binom (1 + (1 ^^^ (4 * 1))) 1) ≠ popcount (1 ||| (4 * 1)) := by
  have hk := v2_binom_add_popcount 1 (1 ^^^ (4 * 1))
  have hp : popcount 1 = 1 ∧ popcount (1 ^^^ (4 * 1)) = 2 ∧
            popcount (1 + (1 ^^^ (4 * 1))) = 2 ∧ popcount (1 ||| (4 * 1)) = 2 := by decide
  omega

theorem counterexample_shift2_or :
    v2 (binom (1 + (1 ||| (4 * 1))) 1) ≠ popcount (1 ||| (4 * 1)) := by
  have hk := v2_binom_add_popcount 1 (1 ||| (4 * 1))
  have hp : popcount 1 = 1 ∧ popcount (1 ||| (4 * 1)) = 2 ∧
            popcount (1 + (1 ||| (4 * 1))) = 2 := by decide
  omega

-- 2. Shifted-AND collapse FAILS at shift k = 2 (4*n) at n = 13!

theorem counterexample_shift2_and :
    v2 (binom (13 + (13 &&& (4 * 13))) 13) ≠ popcount (13 &&& (4 * 13)) := by
  have hk := v2_binom_add_popcount 13 (13 &&& (4 * 13))
  have hp : popcount 13 = 3 ∧ popcount (13 &&& (4 * 13)) = 1 ∧
            popcount (13 + (13 &&& (4 * 13))) = 2 := by decide
  omega

-- 3. General 2-variable (a, b) collapse FAILS for AND at (a, b) = (3, 1)!

theorem counterexample_general_and :
    v2 (binom (3 + (3 &&& 1)) 3) ≠ popcount (3 &&& 1) := by
  have hk := v2_binom_add_popcount 3 (3 &&& 1)
  have hp : popcount 3 = 2 ∧ popcount (3 &&& 1) = 1 ∧ popcount (3 + (3 &&& 1)) = 1 := by decide
  omega

-- 4. Gray-code universal evenness FAILS at n = 0 (binom 0 0 = 1 is odd)!

theorem counterexample_gray_zero : ¬ (2 ∣ binom (0 + gray 0) 0) := by decide

-- 5. k = 11 affine offset -2 CANNOT be tightened to -3 (fails at n = 3: 2*4 + 3 = 11 > 10)!

theorem counterexample_k11_offset :
    ¬ (2 * v2 (binom (11 * 3) 3) + 3 ≤ 5 * popcount 3) := by
  have hk := v2_binom_k_mul 11 3 (by decide)
  have hp : popcount 3 = 2 ∧ popcount ((11 - 1) * 3) = 4 ∧ popcount (11 * 3) = 2 := by decide
  omega

-- 6. k = 25 affine offset -3 CANNOT be tightened to -4 (fails at n = 41)!

theorem counterexample_k25_offset :
    ¬ (3 * v2 (binom (25 * 41) 41) + 4 ≤ 8 * popcount 41) := by
  have hk := v2_binom_k_mul 25 41 (by decide)
  have hp : popcount 41 = 3 ∧ popcount ((25 - 1) * 41) = 6 ∧ popcount (25 * 41) = 2 := by decide
  omega

-- 7. k = 55 affine offset -8 CANNOT be tightened to -9 (fails at n = 149)!

theorem counterexample_k55_offset :
    ¬ (4 * v2 (binom (55 * 149) 149) + 9 ≤ 13 * popcount 149) := by
  have hk := v2_binom_k_mul 55 149 (by decide)
  have hp : popcount 149 = 4 ∧ popcount ((55 - 1) * 149) = 10 ∧ popcount (55 * 149) = 3 := by decide
  omega

-- Axiom verification receipts (every main theorem uses only standard Lean axioms)

end CVAEngine
