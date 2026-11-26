/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitrevIncrementCycles.Defs

/-!
# Bit-Reversal Increment Parity-Dichotomy Cycle Theorem (`bitrev-increment-cycles`)

Pure-`Init` (zero Mathlib) proof of all four theorems in `Challenge.lean`:
1. `bitrevInc_return_map`: exact 3/4/5-step `k → k + 2` return-map law on the embedded slice `2 * m`.
2. `bitrevInc_odd_single_cycle`: for every odd bit-width `k = 2t + 1`, `bitrevInc k` is a single
   full-period Hamiltonian cycle of length `2^(2t + 1)`.
3. `bitrevInc_even_zero_period`: for every even bit-width `k = 2(m + 1)`, the orbit of `0` under
   `bitrevInc (2(m + 1))` has exact minimal period `2^(m + 2) - 1`.
4. `bitrevInc_single_cycle_iff_odd`: for every `k ≥ 1`, `IsSingleCycle k ↔ k % 2 = 1`.
-/

namespace BitrevIncrementCycles

/-! ## Section 1: Basic `bitrev`, `bitrevInc`, `iter`, and `pack` Identities -/

private theorem two_pow_pos (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

private theorem two_pow_succ_eq (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem bitrev_lt : ∀ k x, bitrev k x < 2 ^ k
  | 0, _ => by simp [bitrev]
  | k + 1, x => by
    simp only [bitrev]
    have hlt := bitrev_lt k (x / 2)
    have hmod : x % 2 < 2 := Nat.mod_lt x (by decide)
    rw [two_pow_succ_eq]
    have hmul : (x % 2) * 2 ^ k ≤ 2 ^ k := by
      cases h : x % 2 with
      | zero => simp
      | succ n =>
        have hn : n = 0 := by omega
        subst hn; simp
    omega

theorem bitrev_zero : ∀ k, bitrev k 0 = 0
  | 0 => rfl
  | k + 1 => by
    simp [bitrev, bitrev_zero k]

theorem bitrev_allOnes : ∀ k, bitrev k (2 ^ k - 1) = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
    have hpos := two_pow_pos k
    have hpow := two_pow_succ_eq k
    have hmod : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hdiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
    simp only [bitrev, hmod, hdiv, bitrev_allOnes k]
    omega

theorem bitrev_double_add (k m b : Nat) (hb : b < 2) :
    bitrev (k + 1) (2 * m + b) = b * 2 ^ k + bitrev k m := by
  have hmod : (2 * m + b) % 2 = b := by omega
  have hdiv : (2 * m + b) / 2 = m := by omega
  simp [bitrev, hmod, hdiv]

theorem bitrev_add_pow : ∀ k m a, m < 2 ^ k → a < 2 →
    bitrev (k + 1) (a * 2 ^ k + m) = 2 * bitrev k m + a
  | 0, m, a, hm, ha => by
    have hm0 : m = 0 := by simp at hm; omega
    subst hm0
    have hmod : a % 2 = a := by omega
    simp [bitrev, hmod]
  | k + 1, m, a, hm, ha => by
    have hpow := two_pow_succ_eq k
    have hmod : (a * 2 ^ (k + 1) + m) % 2 = m % 2 := by
      rw [hpow]
      have : a * (2 * 2 ^ k) + m = 2 * (a * 2 ^ k) + m := by
        rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]
      rw [this, Nat.mul_add_mod]
    have hdiv : (a * 2 ^ (k + 1) + m) / 2 = a * 2 ^ k + m / 2 := by
      rw [hpow]
      have : a * (2 * 2 ^ k) + m = 2 * (a * 2 ^ k) + m := by
        rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]
      rw [this, Nat.mul_add_div (by decide)]
    have hmdiv : m / 2 < 2 ^ k := by omega
    conv => lhs; rw [bitrev]
    rw [hmod, hdiv, bitrev_add_pow k (m / 2) a hmdiv ha]
    conv => rhs; arg 1; arg 2; rw [bitrev]
    rw [hpow]
    have h1 : m % 2 * (2 * 2 ^ k) = 2 * (m % 2 * 2 ^ k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (m % 2) 2, Nat.mul_assoc]
    rw [h1]
    omega

theorem bitrev_bitrev : ∀ k x, x < 2 ^ k → bitrev k (bitrev k x) = x
  | 0, x, hx => by simp at hx; simp [bitrev, hx]
  | k + 1, x, hx => by
    have hpow := two_pow_succ_eq k
    have hdiv : x / 2 < 2 ^ k := by omega
    have hmod : x % 2 < 2 := Nat.mod_lt x (by decide)
    conv => lhs; arg 2; rw [bitrev]
    rw [bitrev_add_pow k (bitrev k (x / 2)) (x % 2) (bitrev_lt k (x / 2)) hmod]
    rw [bitrev_bitrev k (x / 2) hdiv]
    omega

theorem bitrev_eq_allOnes_iff (k x : Nat) (hx : x < 2 ^ k) :
    bitrev k x = 2 ^ k - 1 ↔ x = 2 ^ k - 1 := by
  constructor
  · intro h
    have := congrArg (bitrev k) h
    rw [bitrev_bitrev k x hx, bitrev_allOnes k] at this
    exact this
  · intro h
    subst h
    exact bitrev_allOnes k

theorem bitrevInc_lt (k x : Nat) : bitrevInc k x < 2 ^ k :=
  Nat.mod_lt _ (two_pow_pos k)

theorem bitrevInc_zero (k : Nat) (hk : 1 ≤ k) : bitrevInc k 0 = 1 := by
  unfold bitrevInc
  rw [bitrev_zero]
  have h2 : 2 ≤ 2 ^ k := by
    cases k with
    | zero => omega
    | succ k' =>
      have := two_pow_pos k'
      rw [two_pow_succ_eq]; omega
  exact Nat.mod_eq_of_lt (by omega)

theorem bitrevInc_allOnes (k : Nat) : bitrevInc k (2 ^ k - 1) = 0 := by
  unfold bitrevInc
  rw [bitrev_allOnes]
  have hpos := two_pow_pos k
  have : 2 ^ k - 1 + 1 = 2 ^ k := by omega
  rw [this, Nat.mod_self]

theorem bitrevInc_eq_add_one (k x : Nat) (hx : x < 2 ^ k) (hne : x ≠ 2 ^ k - 1) :
    bitrevInc k x = bitrev k x + 1 := by
  unfold bitrevInc
  have hlt := bitrev_lt k x
  have hne' : bitrev k x ≠ 2 ^ k - 1 := fun h => hne ((bitrev_eq_allOnes_iff k x hx).mp h)
  exact Nat.mod_eq_of_lt (by omega)

theorem bitrevInc_injective (k : Nat) {x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : bitrevInc k x = bitrevInc k y) : x = y := by
  have hrx := bitrev_lt k x
  have hry := bitrev_lt k y
  have hrev : bitrev k x = bitrev k y := by
    unfold bitrevInc at h
    have hpos := two_pow_pos k
    by_cases h1 : bitrev k x + 1 < 2 ^ k
    · by_cases h2 : bitrev k y + 1 < 2 ^ k
      · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
      · have hy1 : bitrev k y + 1 = 2 ^ k := by omega
        rw [Nat.mod_eq_of_lt h1, hy1, Nat.mod_self] at h; omega
    · have hx1 : bitrev k x + 1 = 2 ^ k := by omega
      by_cases h2 : bitrev k y + 1 < 2 ^ k
      · rw [hx1, Nat.mod_self, Nat.mod_eq_of_lt h2] at h; omega
      · omega
  have := congrArg (bitrev k) hrev
  rw [bitrev_bitrev k x hx, bitrev_bitrev k y hy] at this
  exact this

theorem iter_add (f : Nat → Nat) : ∀ a b x, iter f (a + b) x = iter f b (iter f a x)
  | 0, b, x => by simp [iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    simp only [iter]
    exact iter_add f a b (f x)

theorem iter_succ_right (f : Nat → Nat) (n x : Nat) :
    iter f (n + 1) x = f (iter f n x) := by
  rw [iter_add]
  rfl

theorem iter_bitrevInc_lt (k : Nat) : ∀ s x, x < 2 ^ k → iter (bitrevInc k) s x < 2 ^ k
  | 0, _, hx => hx
  | s + 1, x, _ => iter_bitrevInc_lt k s (bitrevInc k x) (bitrevInc_lt k x)

/-! ## Section 2: `(a, m, b)` Packing & Exact `k → k + 2` Return-Map Law -/

/-- Decomposes/packs a `(k + 2)`-bit integer into `(top bit a, middle k bits m, bottom bit b)`. -/
def pack (k a m b : Nat) : Nat :=
  a * 2 ^ (k + 1) + 2 * m + b

theorem pack_lt (k a m b : Nat) (ha : a < 2) (hm : m < 2 ^ k) (hb : b < 2) :
    pack k a m b < 2 ^ (k + 2) := by
  unfold pack
  have h1 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := two_pow_succ_eq (k + 1)
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ_eq k
  cases a with
  | zero => omega
  | succ a' =>
    have ha0 : a' = 0 := by omega
    subst ha0
    rw [Nat.zero_add, Nat.one_mul]
    omega

theorem pack_decompose (k x : Nat) (hx : x < 2 ^ (k + 2)) :
    ∃ a m b, a < 2 ∧ m < 2 ^ k ∧ b < 2 ∧ x = pack k a m b := by
  have h1 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := two_pow_succ_eq (k + 1)
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ_eq k
  have hpos := two_pow_pos (k + 1)
  refine ⟨x / 2 ^ (k + 1), (x % 2 ^ (k + 1)) / 2, x % 2, ?_, ?_, ?_, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  · have hmod := Nat.mod_lt x hpos; omega
  · exact Nat.mod_lt x (by decide)
  · unfold pack
    have hdm := Nat.div_add_mod x (2 ^ (k + 1))
    have hrem_mod : (x % 2 ^ (k + 1)) % 2 = x % 2 := by
      have : 2 ∣ 2 ^ (k + 1) := ⟨2 ^ k, by rw [h2]⟩
      exact Nat.mod_mod_of_dvd x this
    have hmul : x / 2 ^ (k + 1) * 2 ^ (k + 1) = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) :=
      Nat.mul_comm _ _
    omega

theorem pack_ne_zero_of_a_eq_one (k m b : Nat) : pack k 1 m b ≠ 0 := by
  unfold pack
  have := two_pow_pos (k + 1)
  omega

theorem pack_ne_zero_of_b_eq_one (k a m : Nat) : pack k a m 1 ≠ 0 := by
  unfold pack; omega

theorem pack_ne_zero_of_m_ne_zero (k a m b : Nat) (hm : m ≠ 0) : pack k a m b ≠ 0 := by
  unfold pack; omega

theorem bitrev_pack (k a m b : Nat) (ha : a < 2) (hm : m < 2 ^ k) (hb : b < 2) :
    bitrev (k + 2) (pack k a m b) = pack k b (bitrev k m) a := by
  have hpow := two_pow_succ_eq k
  have harg : pack k a m b = 2 * (a * 2 ^ k + m) + b := by
    unfold pack
    rw [hpow]
    have : a * (2 * 2 ^ k) = 2 * (a * 2 ^ k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]
    omega
  rw [harg, bitrev_double_add (k + 1) (a * 2 ^ k + m) b hb, bitrev_add_pow k m a hm ha]
  unfold pack
  omega

theorem bitrevInc_pack_zero (k m b : Nat) (hm : m < 2 ^ k) (hb : b < 2) :
    bitrevInc (k + 2) (pack k 0 m b) = pack k b (bitrev k m) 1 := by
  unfold bitrevInc
  rw [bitrev_pack k 0 m b (by decide) hm hb]
  have hlt := pack_lt k b (bitrev k m) 1 hb (bitrev_lt k m) (by decide)
  have hadd : pack k b (bitrev k m) 0 + 1 = pack k b (bitrev k m) 1 := by unfold pack; omega
  rw [hadd, Nat.mod_eq_of_lt hlt]

theorem bitrevInc_pack_one_ne (k m b : Nat) (hm : m < 2 ^ k) (hne : m ≠ 2 ^ k - 1) (hb : b < 2) :
    bitrevInc (k + 2) (pack k 1 m b) = pack k b (bitrevInc k m) 0 := by
  conv => lhs; unfold bitrevInc
  rw [bitrev_pack k 1 m b (by decide) hm hb]
  have hinc := bitrevInc_eq_add_one k m hm hne
  have hlt_inc : bitrev k m + 1 < 2 ^ k := by
    have := bitrev_lt k m
    have hne' : bitrev k m ≠ 2 ^ k - 1 := fun h => hne ((bitrev_eq_allOnes_iff k m hm).mp h)
    omega
  have hlt := pack_lt k b (bitrev k m + 1) 0 hb hlt_inc (by decide)
  have hadd : pack k b (bitrev k m) 1 + 1 = pack k b (bitrev k m + 1) 0 := by unfold pack; omega
  rw [hadd, Nat.mod_eq_of_lt hlt, ← hinc]

theorem bitrevInc_pack_one_allOnes (k b : Nat) (hb : b < 2) :
    bitrevInc (k + 2) (pack k 1 (2 ^ k - 1) b) = pack k (1 - b) 0 0 := by
  unfold bitrevInc
  have hpos := two_pow_pos k
  rw [bitrev_pack k 1 (2 ^ k - 1) b (by decide) (by omega) hb, bitrev_allOnes]
  have h1 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := two_pow_succ_eq (k + 1)
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ_eq k
  unfold pack
  cases b with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.one_mul, Nat.mul_zero, Nat.add_zero]
    have hsum : 2 * (2 ^ k - 1) + 1 + 1 = 2 ^ (k + 1) := by omega
    rw [hsum]
    exact Nat.mod_eq_of_lt (by omega)
  | succ b' =>
    have hb0 : b' = 0 := by omega
    subst hb0
    rw [Nat.zero_add]
    simp only [Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    have hsum : 2 ^ (k + 1) + 2 * (2 ^ k - 1) + 1 + 1 = 2 ^ (k + 2) := by omega
    rw [hsum, Nat.mod_self]

/-- Exact 3-step return segment from `pack k 0 (2^k - 1) 0` back to `0`. -/
theorem seg3_steps (k : Nat) :
    iter (bitrevInc (k + 2)) 0 (pack k 0 (2 ^ k - 1) 0) = pack k 0 (2 ^ k - 1) 0 ∧
    iter (bitrevInc (k + 2)) 1 (pack k 0 (2 ^ k - 1) 0) = pack k 0 (2 ^ k - 1) 1 ∧
    iter (bitrevInc (k + 2)) 2 (pack k 0 (2 ^ k - 1) 0) = pack k 1 (2 ^ k - 1) 1 ∧
    iter (bitrevInc (k + 2)) 3 (pack k 0 (2 ^ k - 1) 0) = 0 := by
  have hpos := two_pow_pos k
  have hm : 2 ^ k - 1 < 2 ^ k := by omega
  have hs1 : bitrevInc (k + 2) (pack k 0 (2 ^ k - 1) 0) = pack k 0 (2 ^ k - 1) 1 := by
    rw [bitrevInc_pack_zero k (2 ^ k - 1) 0 hm (by decide), bitrev_allOnes]
  have hs2 : bitrevInc (k + 2) (pack k 0 (2 ^ k - 1) 1) = pack k 1 (2 ^ k - 1) 1 := by
    rw [bitrevInc_pack_zero k (2 ^ k - 1) 1 hm (by decide), bitrev_allOnes]
  have hs3 : bitrevInc (k + 2) (pack k 1 (2 ^ k - 1) 1) = 0 := by
    rw [bitrevInc_pack_one_allOnes k 1 (by decide)]
    simp [pack]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa [iter] using hs1
  · simp only [iter, hs1, hs2]
  · simp only [iter, hs1, hs2, hs3]

/-- Exact 4-step return segment from `pack k 0 m 0` to `pack k 0 (f_k^2(m)) 0` when
`m ≠ 2^k - 1` and `f_k(m) ≠ 2^k - 1`. -/
theorem seg4_steps (k m : Nat) (hm : m < 2 ^ k) (hne : m ≠ 2 ^ k - 1)
    (hnext : bitrevInc k m ≠ 2 ^ k - 1) :
    iter (bitrevInc (k + 2)) 0 (pack k 0 m 0) = pack k 0 m 0 ∧
    iter (bitrevInc (k + 2)) 1 (pack k 0 m 0) = pack k 0 (bitrev k m) 1 ∧
    iter (bitrevInc (k + 2)) 2 (pack k 0 m 0) = pack k 1 m 1 ∧
    iter (bitrevInc (k + 2)) 3 (pack k 0 m 0) = pack k 1 (bitrevInc k m) 0 ∧
    iter (bitrevInc (k + 2)) 4 (pack k 0 m 0) = pack k 0 (bitrevInc k (bitrevInc k m)) 0 := by
  have hs1 : bitrevInc (k + 2) (pack k 0 m 0) = pack k 0 (bitrev k m) 1 :=
    bitrevInc_pack_zero k m 0 hm (by decide)
  have hs2 : bitrevInc (k + 2) (pack k 0 (bitrev k m) 1) = pack k 1 m 1 := by
    rw [bitrevInc_pack_zero k (bitrev k m) 1 (bitrev_lt k m) (by decide), bitrev_bitrev k m hm]
  have hs3 : bitrevInc (k + 2) (pack k 1 m 1) = pack k 1 (bitrevInc k m) 0 :=
    bitrevInc_pack_one_ne k m 1 hm hne (by decide)
  have hs4 : bitrevInc (k + 2) (pack k 1 (bitrevInc k m) 0) = pack k 0 (bitrevInc k (bitrevInc k m)) 0 :=
    bitrevInc_pack_one_ne k (bitrevInc k m) 0 (bitrevInc_lt k m) hnext (by decide)
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simpa [iter] using hs1
  · simp only [iter, hs1, hs2]
  · simp only [iter, hs1, hs2, hs3]
  · simp only [iter, hs1, hs2, hs3, hs4]

/-- Exact 5-step return segment from `pack k 0 m 0` to `pack k 0 1 0 = 2` when
`m ≠ 2^k - 1` and `f_k(m) = 2^k - 1`. Absorbs `(1, 0, 0)` at step 4! -/
theorem seg5_steps (k m : Nat) (hk : 1 ≤ k) (hm : m < 2 ^ k) (hne : m ≠ 2 ^ k - 1)
    (hnext : bitrevInc k m = 2 ^ k - 1) :
    iter (bitrevInc (k + 2)) 0 (pack k 0 m 0) = pack k 0 m 0 ∧
    iter (bitrevInc (k + 2)) 1 (pack k 0 m 0) = pack k 0 (bitrev k m) 1 ∧
    iter (bitrevInc (k + 2)) 2 (pack k 0 m 0) = pack k 1 m 1 ∧
    iter (bitrevInc (k + 2)) 3 (pack k 0 m 0) = pack k 1 (2 ^ k - 1) 0 ∧
    iter (bitrevInc (k + 2)) 4 (pack k 0 m 0) = pack k 1 0 0 ∧
    iter (bitrevInc (k + 2)) 5 (pack k 0 m 0) = pack k 0 1 0 := by
  have h2k : 2 ≤ 2 ^ k := by
    cases k with
    | zero => omega
    | succ k' => have := two_pow_pos k'; rw [two_pow_succ_eq]; omega
  have hs1 : bitrevInc (k + 2) (pack k 0 m 0) = pack k 0 (bitrev k m) 1 :=
    bitrevInc_pack_zero k m 0 hm (by decide)
  have hs2 : bitrevInc (k + 2) (pack k 0 (bitrev k m) 1) = pack k 1 m 1 := by
    rw [bitrevInc_pack_zero k (bitrev k m) 1 (bitrev_lt k m) (by decide), bitrev_bitrev k m hm]
  have hs3 : bitrevInc (k + 2) (pack k 1 m 1) = pack k 1 (2 ^ k - 1) 0 := by
    rw [bitrevInc_pack_one_ne k m 1 hm hne (by decide), hnext]
  have hs4 : bitrevInc (k + 2) (pack k 1 (2 ^ k - 1) 0) = pack k 1 0 0 :=
    bitrevInc_pack_one_allOnes k 0 (by decide)
  have hs5 : bitrevInc (k + 2) (pack k 1 0 0) = pack k 0 1 0 := by
    rw [bitrevInc_pack_one_ne k 0 0 (by omega) (by omega) (by decide), bitrevInc_zero k hk]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [iter] using hs1
  · simp only [iter, hs1, hs2]
  · simp only [iter, hs1, hs2, hs3]
  · simp only [iter, hs1, hs2, hs3, hs4]
  · simp only [iter, hs1, hs2, hs3, hs4, hs5]

/-- Theorem 4 (Exact `k → k + 2` return-map law). -/
theorem bitrevInc_return_map (k m : Nat) (hk : 1 ≤ k) (hm : m < 2 ^ k) :
    (m = 2 ^ k - 1 → iter (bitrevInc (k + 2)) 3 (2 * m) = 0) ∧
    (m ≠ 2 ^ k - 1 → bitrevInc k m = 2 ^ k - 1 → iter (bitrevInc (k + 2)) 5 (2 * m) = 2) ∧
    (m ≠ 2 ^ k - 1 → bitrevInc k m ≠ 2 ^ k - 1 →
      iter (bitrevInc (k + 2)) 4 (2 * m) = 2 * bitrevInc k (bitrevInc k m)) := by
  have hpack : 2 * m = pack k 0 m 0 := by simp [pack]
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    subst heq
    rw [hpack]
    exact (seg3_steps k).2.2.2
  · intro hne hnext
    rw [hpack]
    simpa [pack] using (seg5_steps k m hk hm hne hnext).2.2.2.2.2
  · intro hne hnext
    rw [hpack]
    simpa [pack] using (seg4_steps k m hm hne hnext).2.2.2.2

/-! ## Section 3: Theorem 1 (Odd Bit-Width Full-Period Hamiltonian Cycle) -/

/-- Helper: if `iter (bitrevInc k) L 0 = 0` and `iter (bitrevInc k) s 0 ≠ 0` for all `0 < s < L`,
then `iter (bitrevInc k) (L - 1) 0 = 2^k - 1` and `iter (bitrevInc k) s 0 ≠ 2^k - 1` for `s < L - 1`. -/
private theorem iter_pre_allOnes (k L : Nat) (hL : 1 ≤ L)
    (hret : iter (bitrevInc k) L 0 = 0)
    (hmin : ∀ s, 0 < s → s < L → iter (bitrevInc k) s 0 ≠ 0) :
    iter (bitrevInc k) (L - 1) 0 = 2 ^ k - 1 ∧
    ∀ s, s < L - 1 → iter (bitrevInc k) s 0 ≠ 2 ^ k - 1 := by
  have hpos := two_pow_pos k
  constructor
  · have hsucc : bitrevInc k (iter (bitrevInc k) (L - 1) 0) = bitrevInc k (2 ^ k - 1) := by
      have : L - 1 + 1 = L := by omega
      rw [← iter_succ_right (bitrevInc k), this, hret, bitrevInc_allOnes]
    exact bitrevInc_injective k (iter_bitrevInc_lt k (L - 1) 0 hpos) (by omega) hsucc
  · intro s hs hEq
    have hzero : iter (bitrevInc k) (s + 1) 0 = 0 := by
      rw [iter_succ_right, hEq, bitrevInc_allOnes]
    exact hmin (s + 1) (by omega) (by omega) hzero

/-- Strong induction predicate for odd `k`: full cycle + minimal period `2^k`. -/
private def IsSingleCycleStrong (k : Nat) : Prop :=
  iter (bitrevInc k) (2 ^ k) 0 = 0 ∧
  (∀ s, 0 < s → s < 2 ^ k → iter (bitrevInc k) s 0 ≠ 0) ∧
  (∀ x, x < 2 ^ k → ∃ s, s < 2 ^ k ∧ iter (bitrevInc k) s 0 = x)

private theorem bitrevInc_odd_single_cycle_strong : ∀ t, IsSingleCycleStrong (2 * t + 1)
  | 0 => by
    refine ⟨by decide, ?_, ?_⟩
    · intro s hs1 hs2
      have : s = 1 := by omega
      subst this; decide
    · intro x hx
      cases x with
      | zero => exact ⟨0, by decide, by decide⟩
      | succ x' =>
        have : x' = 0 := by omega
        subst this
        exact ⟨1, by decide, by decide⟩
  | t + 1 => by
    have ih := bitrevInc_odd_single_cycle_strong t
    let k := 2 * t + 1
    have hk_eq : 2 * (t + 1) + 1 = k + 2 := by omega
    rw [hk_eq]
    rcases ih with ⟨hret, hmin, hsurj⟩
    have hk : 1 ≤ k := by omega
    have hpos_k := two_pow_pos k
    have h2k : 2 ≤ 2 ^ k := by
      have hpos' := two_pow_pos (2 * t)
      have hpow' : 2 ^ k = 2 * 2 ^ (2 * t) := two_pow_succ_eq (2 * t)
      omega
    -- Write 2^k = 2 * H with H = 2^(2 * t) ≥ 1
    let H := 2 ^ (2 * t)
    have hH_pos : 1 ≤ H := two_pow_pos (2 * t)
    have h2H : 2 ^ k = 2 * H := two_pow_succ_eq (2 * t)
    have h4H : 2 ^ (k + 2) = 8 * H := by
      have h1 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := two_pow_succ_eq (k + 1)
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ_eq k
      omega
    have ⟨hlast, hne_last⟩ := iter_pre_allOnes k (2 ^ k) (by omega) hret hmin
    -- Phase A: for all j ≤ H - 1, iter f_{k+2} (4 * j) 0 = pack k 0 (iter f_k (2 * j) 0) 0
    have hPhaseA : ∀ j, j ≤ H - 1 →
        iter (bitrevInc (k + 2)) (4 * j) 0 = pack k 0 (iter (bitrevInc k) (2 * j) 0) 0 := by
      intro j
      induction j with
      | zero => intro _; simp [iter, pack]
      | succ j ihj =>
        intro hj
        have hj' : j ≤ H - 1 := by omega
        have hstep := ihj hj'
        have hm_lt : iter (bitrevInc k) (2 * j) 0 < 2 ^ k := iter_bitrevInc_lt k (2 * j) 0 hpos_k
        have hm_ne : iter (bitrevInc k) (2 * j) 0 ≠ 2 ^ k - 1 := hne_last (2 * j) (by omega)
        have hnext_ne : bitrevInc k (iter (bitrevInc k) (2 * j) 0) ≠ 2 ^ k - 1 := by
          rw [← iter_succ_right (bitrevInc k)]; exact hne_last (2 * j + 1) (by omega)
        have h4 : 4 * (j + 1) = 4 * j + 4 := by omega
        rw [h4, iter_add, hstep]
        have hseg := (seg4_steps k _ hm_lt hm_ne hnext_ne).2.2.2.2
        rw [hseg, ← iter_succ_right (bitrevInc k), ← iter_succ_right (bitrevInc k)]
        exact congrArg (fun n => pack k 0 (iter (bitrevInc k) n 0) 0) (by omega)
    -- Transition A → B at j = H - 1 (where 2 * j = 2^k - 2):
    have hEndA_val : iter (bitrevInc (k + 2)) (4 * (H - 1)) 0 =
        pack k 0 (iter (bitrevInc k) (2 * (H - 1)) 0) 0 := hPhaseA (H - 1) (Nat.le_refl _)
    have hmA_lt : iter (bitrevInc k) (2 * (H - 1)) 0 < 2 ^ k :=
      iter_bitrevInc_lt k (2 * (H - 1)) 0 hpos_k
    have hmA_ne : iter (bitrevInc k) (2 * (H - 1)) 0 ≠ 2 ^ k - 1 :=
      hne_last (2 * (H - 1)) (by omega)
    have hmA_next : bitrevInc k (iter (bitrevInc k) (2 * (H - 1)) 0) = 2 ^ k - 1 := by
      rw [← iter_succ_right (bitrevInc k)]
      have : 2 * (H - 1) + 1 = 2 ^ k - 1 := by omega
      rw [this, hlast]
    have hTransAB := seg5_steps k _ hk hmA_lt hmA_ne hmA_next
    have hStartB : iter (bitrevInc (k + 2)) (4 * (H - 1) + 5) 0 =
        pack k 0 (iter (bitrevInc k) 1 0) 0 := by
      rw [iter_add, hEndA_val, hTransAB.2.2.2.2.2]
      have : iter (bitrevInc k) 1 0 = 1 := by simp [iter, bitrevInc_zero k hk]
      rw [this]
    -- Phase B: for all j ≤ H - 1, iter f_{k+2} (4*(H-1) + 5 + 4*j) 0 = pack k 0 (iter f_k (2*j + 1) 0) 0
    have hPhaseB : ∀ j, j ≤ H - 1 →
        iter (bitrevInc (k + 2)) (4 * (H - 1) + 5 + 4 * j) 0 =
        pack k 0 (iter (bitrevInc k) (2 * j + 1) 0) 0 := by
      intro j
      induction j with
      | zero => intro _; simpa using hStartB
      | succ j ihj =>
        intro hj
        have hj' : j ≤ H - 1 := by omega
        have hstep := ihj hj'
        have hm_lt : iter (bitrevInc k) (2 * j + 1) 0 < 2 ^ k :=
          iter_bitrevInc_lt k (2 * j + 1) 0 hpos_k
        have hm_ne : iter (bitrevInc k) (2 * j + 1) 0 ≠ 2 ^ k - 1 :=
          hne_last (2 * j + 1) (by omega)
        have hnext_ne : bitrevInc k (iter (bitrevInc k) (2 * j + 1) 0) ≠ 2 ^ k - 1 := by
          rw [← iter_succ_right (bitrevInc k)]; exact hne_last (2 * j + 2) (by omega)
        have h4 : 4 * (H - 1) + 5 + 4 * (j + 1) = (4 * (H - 1) + 5 + 4 * j) + 4 := by omega
        rw [h4, iter_add, hstep]
        have hseg := (seg4_steps k _ hm_lt hm_ne hnext_ne).2.2.2.2
        rw [hseg, ← iter_succ_right (bitrevInc k), ← iter_succ_right (bitrevInc k)]
        exact congrArg (fun n => pack k 0 (iter (bitrevInc k) n 0) 0) (by omega)
    -- Transition B → 0 at j = H - 1 (where 2 * j + 1 = 2^k - 1):
    have hEndB_val : iter (bitrevInc (k + 2)) (4 * (H - 1) + 5 + 4 * (H - 1)) 0 =
        pack k 0 (2 ^ k - 1) 0 := by
      rw [hPhaseB (H - 1) (Nat.le_refl _)]
      have : 2 * (H - 1) + 1 = 2 ^ k - 1 := by omega
      rw [this, hlast]
    have hTransB0 := seg3_steps k
    -- 1) Return to 0 at step 2^(k+2)
    have hret_new : iter (bitrevInc (k + 2)) (2 ^ (k + 2)) 0 = 0 := by
      have htot : 2 ^ (k + 2) = (4 * (H - 1) + 5 + 4 * (H - 1)) + 3 := by omega
      rw [htot, iter_add, hEndB_val, hTransB0.2.2.2]
    -- 2) Minimality: no 0 < s < 2^(k+2) lands on 0
    have hmin_new : ∀ s, 0 < s → s < 2 ^ (k + 2) → iter (bitrevInc (k + 2)) s 0 ≠ 0 := by
      intro s hs_pos hs_lt
      by_cases h1 : s < 4 * (H - 1)
      · let j := s / 4
        let r := s % 4
        have hj : j < H - 1 := by omega
        have hs_eq : s = 4 * j + r := by omega
        rw [hs_eq, iter_add, hPhaseA j (by omega)]
        have hm_lt := iter_bitrevInc_lt k (2 * j) 0 hpos_k
        have hm_ne := hne_last (2 * j) (by omega)
        have hnext_ne : bitrevInc k (iter (bitrevInc k) (2 * j) 0) ≠ 2 ^ k - 1 := by
          rw [← iter_succ_right (bitrevInc k)]; exact hne_last (2 * j + 1) (by omega)
        have hseg := seg4_steps k _ hm_lt hm_ne hnext_ne
        have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        rcases hr with hr | hr | hr | hr <;> rw [hr]
        · rw [hseg.1]
          have hj_pos : 0 < 2 * j := by omega
          exact pack_ne_zero_of_m_ne_zero k 0 _ 0 (hmin (2 * j) hj_pos (by omega))
        · rw [hseg.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
        · rw [hseg.2.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
        · rw [hseg.2.2.2.1]; exact pack_ne_zero_of_a_eq_one _ _ _
      · by_cases h2 : s < 4 * (H - 1) + 5
        · let r := s - 4 * (H - 1)
          have hs_eq : s = 4 * (H - 1) + r := by omega
          rw [hs_eq, iter_add, hEndA_val]
          have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
          rcases hr with hr | hr | hr | hr | hr <;> rw [hr]
          · rw [hTransAB.1]
            have hpos_idx : 0 < 2 * (H - 1) := by omega
            exact pack_ne_zero_of_m_ne_zero k 0 _ 0 (hmin (2 * (H - 1)) hpos_idx (by omega))
          · rw [hTransAB.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
          · rw [hTransAB.2.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
          · rw [hTransAB.2.2.2.1]; exact pack_ne_zero_of_a_eq_one _ _ _
          · rw [hTransAB.2.2.2.2.1]; exact pack_ne_zero_of_a_eq_one _ _ _
        · by_cases h3 : s < 4 * (H - 1) + 5 + 4 * (H - 1)
          · let d := s - (4 * (H - 1) + 5)
            let j := d / 4
            let r := d % 4
            have hj : j < H - 1 := by omega
            have hs_eq : s = (4 * (H - 1) + 5 + 4 * j) + r := by omega
            rw [hs_eq, iter_add, hPhaseB j (by omega)]
            have hm_lt := iter_bitrevInc_lt k (2 * j + 1) 0 hpos_k
            have hm_ne := hne_last (2 * j + 1) (by omega)
            have hnext_ne : bitrevInc k (iter (bitrevInc k) (2 * j + 1) 0) ≠ 2 ^ k - 1 := by
              rw [← iter_succ_right (bitrevInc k)]; exact hne_last (2 * j + 2) (by omega)
            have hseg := seg4_steps k _ hm_lt hm_ne hnext_ne
            have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
            rcases hr with hr | hr | hr | hr <;> rw [hr]
            · rw [hseg.1]
              exact pack_ne_zero_of_m_ne_zero k 0 _ 0 (hmin (2 * j + 1) (by omega) (by omega))
            · rw [hseg.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
            · rw [hseg.2.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
            · rw [hseg.2.2.2.1]; exact pack_ne_zero_of_a_eq_one _ _ _
          · let r := s - (4 * (H - 1) + 5 + 4 * (H - 1))
            have hs_eq : s = (4 * (H - 1) + 5 + 4 * (H - 1)) + r := by omega
            rw [hs_eq, iter_add, hEndB_val]
            have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
            rcases hr with hr | hr | hr <;> rw [hr]
            · rw [hTransB0.1]
              exact pack_ne_zero_of_m_ne_zero k 0 _ 0 (by omega)
            · rw [hTransB0.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
            · rw [hTransB0.2.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
    -- 3) Surjectivity: every x < 2^(k+2) is visited at some step < 2^(k+2)
    have hsurj_new : ∀ x, x < 2 ^ (k + 2) → ∃ s, s < 2 ^ (k + 2) ∧ iter (bitrevInc (k + 2)) s 0 = x := by
      intro x hx
      rcases pack_decompose k x hx with ⟨a, m, b, ha, hm, hb, rfl⟩
      have h_ab_00_01_11 : ∀ s0, s0 < 2 ^ k →
          ∃ base, base + 2 < 2 ^ (k + 2) ∧
            iter (bitrevInc (k + 2)) base 0 = pack k 0 (iter (bitrevInc k) s0 0) 0 ∧
            iter (bitrevInc (k + 2)) (base + 1) 0 = pack k 0 (bitrev k (iter (bitrevInc k) s0 0)) 1 ∧
            iter (bitrevInc (k + 2)) (base + 2) 0 = pack k 1 (iter (bitrevInc k) s0 0) 1 := by
        intro s0 hs0
        by_cases heven : s0 % 2 = 0
        · let j := s0 / 2
          have hs0_eq : s0 = 2 * j := by omega
          have hj_le : j ≤ H - 1 := by omega
          refine ⟨4 * j, by omega, ?_, ?_, ?_⟩
          · rw [hPhaseA j hj_le, ← hs0_eq]
          · rw [iter_add, hPhaseA j hj_le, ← hs0_eq]
            simp only [iter]
            exact bitrevInc_pack_zero k _ 0 (iter_bitrevInc_lt k s0 0 hpos_k) (by decide)
          · rw [iter_add, hPhaseA j hj_le, ← hs0_eq]
            simp only [iter]
            rw [bitrevInc_pack_zero k _ 0 (iter_bitrevInc_lt k s0 0 hpos_k) (by decide),
                bitrevInc_pack_zero k _ 1 (bitrev_lt k _) (by decide),
                bitrev_bitrev k _ (iter_bitrevInc_lt k s0 0 hpos_k)]
        · let j := s0 / 2
          have hs0_eq : s0 = 2 * j + 1 := by omega
          have hj_le : j ≤ H - 1 := by omega
          refine ⟨4 * (H - 1) + 5 + 4 * j, by omega, ?_, ?_, ?_⟩
          · rw [hPhaseB j hj_le, ← hs0_eq]
          · rw [iter_add, hPhaseB j hj_le, ← hs0_eq]
            simp only [iter]
            exact bitrevInc_pack_zero k _ 0 (iter_bitrevInc_lt k s0 0 hpos_k) (by decide)
          · rw [iter_add, hPhaseB j hj_le, ← hs0_eq]
            simp only [iter]
            rw [bitrevInc_pack_zero k _ 0 (iter_bitrevInc_lt k s0 0 hpos_k) (by decide),
                bitrevInc_pack_zero k _ 1 (bitrev_lt k _) (by decide),
                bitrev_bitrev k _ (iter_bitrevInc_lt k s0 0 hpos_k)]
      have ha_cases : a = 0 ∨ a = 1 := by omega
      have hb_cases : b = 0 ∨ b = 1 := by omega
      rcases ha_cases with rfl | rfl <;> rcases hb_cases with rfl | rfl
      · -- (0, m, 0)
        rcases hsurj m hm with ⟨s0, hs0, hm_eq⟩
        rcases h_ab_00_01_11 s0 hs0 with ⟨base, hbase_lt, h0, _, _⟩
        exact ⟨base, by omega, by rw [h0, hm_eq]⟩
      · -- (0, m, 1): choose s0 with g s0 = bitrev k m
        rcases hsurj (bitrev k m) (bitrev_lt k m) with ⟨s0, hs0, hrev_eq⟩
        rcases h_ab_00_01_11 s0 hs0 with ⟨base, hbase_lt, _, h1, _⟩
        exact ⟨base + 1, by omega, by rw [h1, hrev_eq, bitrev_bitrev k m hm]⟩
      · -- (1, m, 0)
        rcases hsurj m hm with ⟨s0, hs0, hm_eq⟩
        by_cases hs0_zero : s0 = 0
        · subst hs0_zero
          have hm0 : m = 0 := by simpa [iter] using hm_eq.symm
          subst hm0
          refine ⟨4 * (H - 1) + 4, by omega, ?_⟩
          rw [iter_add, hEndA_val, hTransAB.2.2.2.2.1]
        · let sp := s0 - 1
          have hsp_lt : sp < 2 ^ k - 1 := by omega
          have hsp_next : bitrevInc k (iter (bitrevInc k) sp 0) = m := by
            rw [← iter_succ_right (bitrevInc k)]
            have : sp + 1 = s0 := by omega
            rw [this, hm_eq]
          by_cases hsp_even : sp % 2 = 0
          · let j := sp / 2
            have hsp_eq : sp = 2 * j := by omega
            refine ⟨4 * j + 3, by omega, ?_⟩
            have hstep : 4 * j + 3 = (4 * j + 2) + 1 := by omega
            rw [hstep, iter_succ_right, iter_add, hPhaseA j (by omega), ← hsp_eq]
            simp only [iter]
            rw [bitrevInc_pack_zero k _ 0 (iter_bitrevInc_lt k sp 0 hpos_k) (by decide),
                bitrevInc_pack_zero k _ 1 (bitrev_lt k _) (by decide),
                bitrev_bitrev k _ (iter_bitrevInc_lt k sp 0 hpos_k),
                bitrevInc_pack_one_ne k _ 1 (iter_bitrevInc_lt k sp 0 hpos_k) (hne_last sp hsp_lt) (by decide),
                hsp_next]
          · let j := sp / 2
            have hsp_eq : sp = 2 * j + 1 := by omega
            have hj_lt : j < H - 1 := by omega
            refine ⟨4 * (H - 1) + 5 + 4 * j + 3, by omega, ?_⟩
            have hstep : 4 * (H - 1) + 5 + 4 * j + 3 = (4 * (H - 1) + 5 + 4 * j + 2) + 1 := by omega
            rw [hstep, iter_succ_right, iter_add, hPhaseB j (by omega), ← hsp_eq]
            simp only [iter]
            rw [bitrevInc_pack_zero k _ 0 (iter_bitrevInc_lt k sp 0 hpos_k) (by decide),
                bitrevInc_pack_zero k _ 1 (bitrev_lt k _) (by decide),
                bitrev_bitrev k _ (iter_bitrevInc_lt k sp 0 hpos_k),
                bitrevInc_pack_one_ne k _ 1 (iter_bitrevInc_lt k sp 0 hpos_k) (hne_last sp hsp_lt) (by decide),
                hsp_next]
      · -- (1, m, 1)
        rcases hsurj m hm with ⟨s0, hs0, hm_eq⟩
        rcases h_ab_00_01_11 s0 hs0 with ⟨base, hbase_lt, _, _, h2⟩
        exact ⟨base + 2, by omega, by rw [h2, hm_eq]⟩
    exact ⟨hret_new, hmin_new, hsurj_new⟩

/-- Theorem 1 (Odd bit-width Hamiltonian cycle). -/
theorem bitrevInc_odd_single_cycle (t : Nat) :
    IsSingleCycle (2 * t + 1) := by
  have h := bitrevInc_odd_single_cycle_strong t
  exact ⟨h.1, h.2.2⟩

/-! ## Section 4: Theorem 2 (Exact Even-Width Orbit Period of `0`) -/

/-- Theorem 2 (Exact even-width orbit period of `0`): for `k = 2(m + 1)`, the orbit of `0`
under `bitrevInc (2(m + 1))` has exact minimal period `2^(m + 2) - 1`. -/
theorem bitrevInc_even_zero_period : ∀ m,
    iter (bitrevInc (2 * (m + 1))) (2 ^ (m + 2) - 1) 0 = 0 ∧
    ∀ s : Nat, 0 < s → s < 2 ^ (m + 2) - 1 → iter (bitrevInc (2 * (m + 1))) s 0 ≠ 0
  | 0 => by
    refine ⟨by decide, ?_⟩
    intro s hs1 hs2
    have hcases : s = 1 ∨ s = 2 := by omega
    rcases hcases with rfl | rfl <;> decide
  | m + 1 => by
    have ih := bitrevInc_even_zero_period m
    let k := 2 * (m + 1)
    have hk_eq : 2 * (m + 1 + 1) = k + 2 := by omega
    rw [hk_eq]
    rcases ih with ⟨hret, hmin⟩
    have hpos_k := two_pow_pos k
    have h2k : 2 ≤ 2 ^ k := by
      have hk1 : k = (k - 1) + 1 := by omega
      have hpos' := two_pow_pos (k - 1)
      have hpow' : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv => lhs; rw [hk1]
        exact two_pow_succ_eq (k - 1)
      omega
    let L := 2 ^ (m + 2) - 1
    let H := 2 ^ (m + 1) - 1
    have hpow_m2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := two_pow_succ_eq (m + 1)
    have hpow_m3 : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := two_pow_succ_eq (m + 2)
    have hpos_m1 : 1 ≤ 2 ^ (m + 1) := two_pow_pos (m + 1)
    have hL_eq : L = 2 * H + 1 := by omega
    have hLnext_eq : 2 ^ (m + 1 + 2) - 1 = 4 * H + 3 := by omega
    have ⟨hlast, hne_last⟩ := iter_pre_allOnes k L (by omega) hret hmin
    -- Walk all H normal 4-step segments: for all j ≤ H, iter f_{k+2} (4 * j) 0 = pack k 0 (g (2*j)) 0
    have hWalk : ∀ j, j ≤ H →
        iter (bitrevInc (k + 2)) (4 * j) 0 = pack k 0 (iter (bitrevInc k) (2 * j) 0) 0 := by
      intro j
      induction j with
      | zero => intro _; simp [iter, pack]
      | succ j ihj =>
        intro hj
        have hstep := ihj (by omega)
        have hm_lt := iter_bitrevInc_lt k (2 * j) 0 hpos_k
        have hm_ne := hne_last (2 * j) (by omega)
        have hnext_ne : bitrevInc k (iter (bitrevInc k) (2 * j) 0) ≠ 2 ^ k - 1 := by
          rw [← iter_succ_right (bitrevInc k)]; exact hne_last (2 * j + 1) (by omega)
        have h4 : 4 * (j + 1) = 4 * j + 4 := by omega
        rw [h4, iter_add, hstep]
        have hseg := (seg4_steps k _ hm_lt hm_ne hnext_ne).2.2.2.2
        rw [hseg, ← iter_succ_right (bitrevInc k), ← iter_succ_right (bitrevInc k)]
        exact congrArg (fun n => pack k 0 (iter (bitrevInc k) n 0) 0) (by omega)
    have hAtH : iter (bitrevInc (k + 2)) (4 * H) 0 = pack k 0 (2 ^ k - 1) 0 := by
      rw [hWalk H (Nat.le_refl _)]
      have : 2 * H = L - 1 := by omega
      rw [this, hlast]
    have hSeg3 := seg3_steps k
    constructor
    · rw [hLnext_eq, iter_add, hAtH, hSeg3.2.2.2]
    · intro s hs_pos hs_lt
      rw [hLnext_eq] at hs_lt
      by_cases h1 : s < 4 * H
      · let j := s / 4
        let r := s % 4
        have hj : j < H := by omega
        have hs_eq : s = 4 * j + r := by omega
        rw [hs_eq, iter_add, hWalk j (by omega)]
        have hm_lt := iter_bitrevInc_lt k (2 * j) 0 hpos_k
        have hm_ne := hne_last (2 * j) (by omega)
        have hnext_ne : bitrevInc k (iter (bitrevInc k) (2 * j) 0) ≠ 2 ^ k - 1 := by
          rw [← iter_succ_right (bitrevInc k)]; exact hne_last (2 * j + 1) (by omega)
        have hseg := seg4_steps k _ hm_lt hm_ne hnext_ne
        have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        rcases hr with hr | hr | hr | hr <;> rw [hr]
        · rw [hseg.1]
          exact pack_ne_zero_of_m_ne_zero k 0 _ 0 (hmin (2 * j) (by omega) (by omega))
        · rw [hseg.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
        · rw [hseg.2.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
        · rw [hseg.2.2.2.1]; exact pack_ne_zero_of_a_eq_one _ _ _
      · let r := s - 4 * H
        have hs_eq : s = 4 * H + r := by omega
        rw [hs_eq, iter_add, hAtH]
        have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
        rcases hr with hr | hr | hr <;> rw [hr]
        · rw [hSeg3.1]; exact pack_ne_zero_of_m_ne_zero k 0 _ 0 (by omega)
        · rw [hSeg3.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _
        · rw [hSeg3.2.2.1]; exact pack_ne_zero_of_b_eq_one _ _ _

/-! ## Section 5: Theorem 3 (Parity Dichotomy `IsSingleCycle k ↔ k % 2 = 1`) -/

/-- Pure-`Init` surjection pigeonhole: no function `h : Nat → Nat` can map `{0, ..., m - 1}`
surjectively onto `{0, ..., n - 1}` when `m < n`. -/
private theorem no_surj_of_lt : ∀ m n (h : Nat → Nat), m < n →
    (∀ x, x < n → ∃ r, r < m ∧ h r = x) → False
  | 0, n, _, hlt, hsurj => by
    rcases hsurj 0 (by omega) with ⟨r, hr, _⟩
    omega
  | m + 1, n, h, hlt, hsurj => by
    let v := h m
    let h' : Nat → Nat := fun r => if h r < v then h r else h r - 1
    apply no_surj_of_lt m (n - 1) h' (by omega)
    intro y hy
    by_cases hyv : y < v
    · rcases hsurj y (by omega) with ⟨r, hr, hreq⟩
      have hrm : r ≠ m := by intro heq; subst heq; omega
      refine ⟨r, by omega, ?_⟩
      dsimp only [h']
      simp only [hreq, hyv, ↓reduceIte]
    · rcases hsurj (y + 1) (by omega) with ⟨r, hr, hreq⟩
      have hrm : r ≠ m := by intro heq; subst heq; omega
      refine ⟨r, by omega, ?_⟩
      dsimp only [h']
      have hnot : ¬ (y + 1 < v) := by omega
      simp only [hreq, hnot, ↓reduceIte]
      omega

/-- Periodic orbit reduction modulo `L`: if `iter f L x = x` and `0 < L`, then
`iter f s x = iter f (s % L) x` for all `s`. -/
private theorem iter_mod_period (f : Nat → Nat) (L x : Nat) (_hL : 0 < L)
    (hper : iter f L x = x) : ∀ s, iter f s x = iter f (s % L) x := by
  intro s
  have hmul : ∀ q, iter f (L * q) x = x := by
    intro q
    induction q with
    | zero => simp [iter]
    | succ q ih =>
      have : L * (q + 1) = L * q + L := by rw [Nat.mul_add, Nat.mul_one]
      rw [this, iter_add, ih, hper]
  have hdm : s = L * (s / L) + s % L := (Nat.div_add_mod s L).symm
  conv => lhs; rw [hdm]
  rw [iter_add, hmul (s / L)]

private theorem two_pow_add_two_sub_one_lt : ∀ m, 2 ^ (m + 2) - 1 < 2 ^ (2 * (m + 1))
  | 0 => by decide
  | m + 1 => by
    have ih := two_pow_add_two_sub_one_lt m
    have h1 : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := two_pow_succ_eq (m + 2)
    have h2 : 2 ^ (2 * (m + 1 + 1)) = 4 * 2 ^ (2 * (m + 1)) := by
      have hidx : 2 * (m + 1 + 1) = (2 * (m + 1) + 1) + 1 := by omega
      rw [hidx, two_pow_succ_eq, two_pow_succ_eq]; omega
    have hpos := two_pow_pos (m + 2)
    omega

/-- Theorem 3 (Parity dichotomy): for every `k ≥ 1`, `bitrevInc k` is a single full-period cycle
on `{0, ..., 2^k - 1}` if and only if `k` is odd. -/
theorem bitrevInc_single_cycle_iff_odd (k : Nat) (hk : 1 ≤ k) :
    IsSingleCycle k ↔ k % 2 = 1 := by
  constructor
  · intro hcyc
    by_cases hodd : k % 2 = 1
    · exact hodd
    · exfalso
      have heven : k % 2 = 0 := by omega
      let m := k / 2 - 1
      have hk_eq : k = 2 * (m + 1) := by omega
      rw [hk_eq] at hcyc
      have hper := (bitrevInc_even_zero_period m).1
      let L := 2 ^ (m + 2) - 1
      have hL_pos : 0 < L := by
        have hpos := two_pow_pos (m + 1)
        have : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := two_pow_succ_eq (m + 1)
        omega
      have hL_lt : L < 2 ^ (2 * (m + 1)) := two_pow_add_two_sub_one_lt m
      apply no_surj_of_lt L (2 ^ (2 * (m + 1))) (fun r => iter (bitrevInc (2 * (m + 1))) r 0) hL_lt
      intro x hx
      rcases hcyc.2 x hx with ⟨s, _, hs_eq⟩
      refine ⟨s % L, Nat.mod_lt s hL_pos, ?_⟩
      rw [← iter_mod_period (bitrevInc (2 * (m + 1))) L 0 hL_pos hper s, hs_eq]
  · intro hodd
    have hk_eq : k = 2 * (k / 2) + 1 := by omega
    rw [hk_eq]
    exact bitrevInc_odd_single_cycle (k / 2)

end BitrevIncrementCycles
