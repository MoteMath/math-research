/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ClmulLiftDeterminants.Defs
import ClmulLiftDeterminants.BitAlgebra
import ClmulLiftDeterminants.RevHadamard
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Exact Monomial Determinant Formulas & Gap Vanishing for Carry-Less `F_2[x]`-Lift Matrices

Proves all five headline theorems for `(oddClmulMatrix t n)_{i,j} = bitPolyEval t (clmul (2i+1) (2j+1))`
via an explicit polynomial Schur-complement reduction over arbitrary commutative rings `R` (requiring
no division): for every `k ≥ 0` and `1 ≤ m ≤ 2^k`,

  `det(M_{2^k + m}(t)) = det(M_{2^k}(t)) * (-2 * t^(k + 1))^m * det(revHadamard R k m)`.

Combined with the exact bit-reversed Hadamard determinants in `RevHadamard.lean`, this yields
monomial determinants at `n ∈ {2^k - 1, 2^k, 2^k + 1}`, identical vanishing on every gap
`2^k + 2 ≤ n ≤ 2^(k + 1) - 2`, and the exact non-vanishing locus over integral domains with `2 ≠ 0, t ≠ 0`.
-/

namespace ClmulLiftDeterminants

open scoped BigOperators
open Finset

/-! ## Section 1: Explicit Polynomial Elimination Matrix `schurX` -/

/-- Explicit `2^k × m` elimination matrix `X_{k, m}(t)` over any commutative ring `R`:
- Column `j = 0`: `(1 + t^(k + 1)) * e_0`.
- Column `j = 2^v * (2q + 1)` (`v = ctz j`, `q = j / 2^(v + 1)`):
  `e_j + t^(v + 1) * (e_{2^(k - 1 - v) + q} - e_q)`. -/
def schurX {R : Type*} [CommRing R] (t : R) (k m : ℕ) : Matrix (Fin (2 ^ k)) (Fin m) R :=
  Matrix.of fun i j =>
    if j.1 = 0 then
      if i.1 = 0 then 1 + t ^ (k + 1) else 0
    else
      let v := ctz j.1
      let q := j.1 / 2 ^ (v + 1)
      (if i.1 = j.1 then (1 : R) else 0) +
      (if i.1 = 2 ^ (k - 1 - v) + q then t ^ (v + 1) else 0) -
      (if i.1 = q then t ^ (v + 1) else 0)

/-- Contraction of any vector `f : Fin (2^k) → R` with column `j` of `schurX t k m`. -/
theorem sum_mul_schurX {R : Type*} [CommRing R] (t : R) {k m : ℕ} (hm : m ≤ 2 ^ k)
    (f : ℕ → R) (j : Fin m) :
    (∑ i : Fin (2 ^ k), f i.1 * schurX t k m i j) =
      if j.1 = 0 then (1 + t ^ (k + 1)) * f 0
      else
        let v := ctz j.1
        let q := j.1 / 2 ^ (v + 1)
        f j.1 + t ^ (v + 1) * f (2 ^ (k - 1 - v) + q) - t ^ (v + 1) * f q := by
  have hj_lt : j.1 < 2 ^ k := lt_of_lt_of_le j.2 hm
  by_cases hj0 : j.1 = 0
  · simp only [hj0, ↓reduceIte, schurX, Matrix.of_apply]
    have h0_lt : 0 < 2 ^ k := by positivity
    rw [Finset.sum_eq_single (⟨0, h0_lt⟩ : Fin (2 ^ k))]
    · simp [mul_comm]
    · intro i _ hi
      have hi0 : i.1 ≠ 0 := fun h => hi (Fin.ext h)
      simp [hi0]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [hj0, ↓reduceIte, schurX, Matrix.of_apply]
    set v := ctz j.1
    set q := j.1 / 2 ^ (v + 1)
    have hv_lt : v < k := ctz_lt_of_lt_two_pow hj0 hj_lt
    have ⟨hodd, hmul⟩ := ctz_spec j.1 hj0
    have hq_eq : j.1 = 2 ^ v * (2 * q + 1) := by
      have hdiv : j.1 / 2 ^ (v + 1) = (j.1 / 2 ^ v) / 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
      have hodd' : (j.1 / 2 ^ v) % 2 = 1 := hodd
      have h2q : 2 * q + 1 = j.1 / 2 ^ v := by
        dsimp [q]; rw [hdiv]; omega
      rw [h2q, hmul]
    have hq_lt_half : q < 2 ^ (k - 1 - v) := by
      have hpow : 2 ^ k = 2 ^ v * (2 * 2 ^ (k - 1 - v)) := by
        have : k = v + 1 + (k - 1 - v) := by omega
        conv_lhs => rw [this, pow_add, pow_add, pow_one]
        ac_rfl
      have hpos : 0 < 2 ^ v := by positivity
      have h1 : 2 ^ v * (2 * q + 1) < 2 ^ v * (2 * 2 ^ (k - 1 - v)) := by
        rw [← hq_eq, ← hpow]; exact hj_lt
      have h2 : 2 * q + 1 < 2 * 2 ^ (k - 1 - v) := Nat.lt_of_mul_lt_mul_left h1
      omega
    have h2_lt : 2 ^ (k - 1 - v) + q < 2 ^ k := by
      have hpow : 2 * 2 ^ (k - 1 - v) ≤ 2 ^ k := by
        have : k - 1 - v + 1 ≤ k := by omega
        calc 2 * 2 ^ (k - 1 - v) = 2 ^ (k - 1 - v + 1) := by rw [pow_succ, mul_comm]
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) this
      omega
    have hq_lt : q < 2 ^ k := by omega
    have hsum_ite : ∀ (a : ℕ) (ha : a < 2 ^ k) (c : R),
        (∑ i : Fin (2 ^ k), f i.1 * (if i.1 = a then c else 0)) = c * f a := by
      intro a ha c
      rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin (2 ^ k))]
      · simp [mul_comm]
      · intro i _ hi
        have hne : i.1 ≠ a := fun h => hi (Fin.ext h)
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsplit :
        (∑ i : Fin (2 ^ k),
          f i.1 * ((if i.1 = j.1 then (1 : R) else 0) +
            (if i.1 = 2 ^ (k - 1 - v) + q then t ^ (v + 1) else 0) -
            (if i.1 = q then t ^ (v + 1) else 0))) =
        (∑ i : Fin (2 ^ k), f i.1 * (if i.1 = j.1 then (1 : R) else 0)) +
        (∑ i : Fin (2 ^ k), f i.1 * (if i.1 = 2 ^ (k - 1 - v) + q then t ^ (v + 1) else 0)) -
        (∑ i : Fin (2 ^ k), f i.1 * (if i.1 = q then t ^ (v + 1) else 0)) := by
      simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hsplit, hsum_ite j.1 hj_lt 1, hsum_ite (2 ^ (k - 1 - v) + q) h2_lt (t ^ (v + 1)),
        hsum_ite q hq_lt (t ^ (v + 1)), one_mul]

/-! ## Section 2: Bitwise Overlap Identities for Top (`AX = B`) and Bottom (`C - Bᵀ X`) -/

/-- For `r < 2^k`, letting `a = 2 * (2^k + r) + 1`, we have `a &&& (2^(k + 1) * a) = 2^(k + 1)`. -/
theorem odd_upper_and_shift {k r : ℕ} (hr : r < 2 ^ k) :
    (2 * (2 ^ k + r) + 1) &&& (2 ^ (k + 1) * (2 * (2 ^ k + r) + 1)) = 2 ^ (k + 1) := by
  set a := 2 * (2 ^ k + r) + 1
  have ha_eq : a = 2 ^ (k + 1) + (2 * r + 1) := by
    dsimp [a]; rw [pow_succ]; ring
  have ha_lt : a < 2 ^ (k + 2) := by
    have hpow1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    have hpow2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
    omega
  apply Nat.eq_of_testBit_eq
  intro u
  rw [Nat.testBit_and, testBit_pow_two_mul, Nat.testBit_two_pow]
  by_cases hu : u < k + 1
  · have hne : k + 1 ≠ u := by omega
    simp [hu, hne]
  · by_cases hu_eq : u = k + 1
    · subst hu_eq
      simp only [lt_self_iff_false, ↓reduceIte, Nat.sub_self]
      have ha0 : a.testBit 0 = true := by
        have hmod : a % 2 = 1 := by dsimp [a]; omega
        simp [Nat.testBit_zero, hmod]
      have ha_top : a.testBit (k + 1) = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, ha_eq]
        have hpos : 0 < 2 ^ (k + 1) := by positivity
        have hlt_rem : 2 * r + 1 < 2 ^ (k + 1) := by rw [pow_succ]; omega
        have hdiv : (2 ^ (k + 1) + (2 * r + 1)) / 2 ^ (k + 1) = 1 := by
          have : 2 ^ (k + 1) + (2 * r + 1) = (2 * r + 1) + 2 ^ (k + 1) * 1 := by ring
          rw [this, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt_rem, zero_add]
        rw [hdiv]; decide
      simp [ha0, ha_top]
    · have hu_ge : k + 2 ≤ u := by omega
      have ha_u : a.testBit u = false :=
        testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le ha_lt (Nat.pow_le_pow_right (by omega) hu_ge))
      have hne : k + 1 ≠ u := by omega
      simp [hu, ha_u, hne]

/-- Bit `(k + 1)` of `U = 2^(v + 1) * clmul (2*(2^k + r) + 1) (2*q + 1)` equals the parity of
`popcntK k (bitrevNat k r &&& j)` when `r, j < 2^k`, `j ≠ 0`, `v = ctz j`, `q = j / 2^(v + 1)`. -/
theorem testBit_U_eq_popcnt_rev {k r j : ℕ} (hr : r < 2 ^ k) (hj0 : j ≠ 0) (hj : j < 2 ^ k) :
    let v := ctz j
    let q := j / 2 ^ (v + 1)
    (2 ^ (v + 1) * clmul (2 * (2 ^ k + r) + 1) (2 * q + 1)).testBit (k + 1) =
      decide (popcntK k (bitrevNat k r &&& j) % 2 = 1) := by
  intro v q
  have hv_lt : v < k := ctz_lt_of_lt_two_pow hj0 hj
  have ⟨hodd, hmul⟩ := ctz_spec j hj0
  have hj_eq : j = 2 ^ v * (2 * q + 1) := by
    have hdiv : j / 2 ^ (v + 1) = (j / 2 ^ v) / 2 := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
    have hodd' : (j / 2 ^ v) % 2 = 1 := hodd
    have h2q : 2 * q + 1 = j / 2 ^ v := by
      dsimp [q]; rw [hdiv]; omega
    rw [h2q, hmul]
  rw [testBit_pow_two_mul]
  have hnotlt : ¬(k + 1 < v + 1) := by omega
  simp only [hnotlt, ↓reduceIte]
  have hsub : k + 1 - (v + 1) = k - v := by omega
  rw [hsub, testBit_clmul]
  apply congrArg (fun x => decide (x % 2 = 1))
  unfold popcntK
  -- Biject S1 = {d ∈ range (k - v + 1) | a.testBit d && (2q+1).testBit (k - v - d)}
  -- onto S2 = {u ∈ range k | (bitrevNat k r &&& j).testBit u = true} via d ↦ k - d!
  set a := 2 * (2 ^ k + r) + 1
  have ha_bit : ∀ d, 1 ≤ d → d ≤ k → a.testBit d = r.testBit (d - 1) := by
    intro d hd1 hdk
    have ha_eq : a = 2 ^ (k + 1) + (2 * r + 1) := by dsimp [a]; rw [pow_succ]; ring
    have hd_sub : d = (d - 1) + 1 := by omega
    conv_lhs => rw [hd_sub, Nat.testBit_succ]
    have hdiv : a / 2 = 2 ^ k + r := by dsimp [a]; omega
    rw [hdiv]
    have hxor : 2 ^ k + r = r ^^^ 2 ^ k := by
      rw [xor_eq_add_of_and_eq_zero, add_comm]
      simpa using and_eq_zero_of_lt_two_pow_mul (b := 1) hr
    rw [hxor, Nat.testBit_xor, Nat.testBit_two_pow]
    have hne : k ≠ d - 1 := by omega
    simp [hne]
  have hj_bit : ∀ s, (2 * q + 1).testBit s = j.testBit (v + s) := by
    intro s
    rw [hj_eq, testBit_pow_two_mul]
    have hnot : ¬(v + s < v) := by omega
    simp [hnot]
  refine Finset.card_bij (fun d _ => k - d) ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true] at hd ⊢
    rcases hd with ⟨hd_lt, ha_d, hq_d⟩
    have hd_pos : 1 ≤ d := by
      by_contra h0
      have hd0 : d = 0 := by omega
      subst hd0
      rw [Nat.sub_zero, hj_bit] at hq_d
      have hvk : v + (k - v) = k := by omega
      rw [hvk, testBit_eq_false_of_lt_two_pow hj] at hq_d
      simp at hq_d
    have hu_lt : k - d < k := by omega
    refine ⟨hu_lt, ?_⟩
    rw [Nat.testBit_and, testBit_bitrevNat k r (k - d) hu_lt]
    have hidx : k - 1 - (k - d) = d - 1 := by omega
    rw [hidx, ← ha_bit d hd_pos (by omega), ha_d, Bool.true_and]
    rw [hj_bit] at hq_d
    have hidx2 : v + (k - v - d) = k - d := by omega
    rw [hidx2] at hq_d
    exact hq_d
  · intro d1 hd1 d2 hd2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hd1 hd2
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_and, Bool.and_eq_true] at hu
    rcases hu with ⟨hu_lt, hrev_u, hj_u⟩
    have hu_ge_v : v ≤ u := by
      by_contra hlt_v
      rw [hj_eq, testBit_pow_two_mul] at hj_u
      have : u < v := by omega
      simp [this] at hj_u
    refine ⟨k - u, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
    refine ⟨by omega, ?_, ?_⟩
    · rw [ha_bit (k - u) (by omega) (by omega)]
      rw [testBit_bitrevNat k r u hu_lt] at hrev_u
      have hidx : k - u - 1 = k - 1 - u := by omega
      rw [hidx]; exact hrev_u
    · rw [hj_bit]
      have hidx : v + (k - v - (k - u)) = u := by omega
      rw [hidx]; exact hj_u

/-- Master row-level identity for any odd integer `a`:
computes `eval(clmul a (2(2^k+j)+1)) - (row_a · col_j(schurX))` for both top (`i < 2^k`) and
bottom (`i = 2^k + r`) rows! -/
theorem row_elim_identity {R : Type*} [CommRing R] (t : R) {k m : ℕ} (hm : m ≤ 2 ^ k)
    (a : ℕ) (j : Fin m) :
    bitPolyEval t (clmul a (2 * (2 ^ k + j.1) + 1)) -
      (∑ i : Fin (2 ^ k), bitPolyEval t (clmul a (2 * i.1 + 1)) * schurX t k m i j) =
    if j.1 = 0 then
      -2 * bitPolyEval t (a &&& (2 ^ (k + 1) * a))
    else
      let v := ctz j.1
      let q := j.1 / 2 ^ (v + 1)
      let U := 2 ^ (v + 1) * clmul a (2 * q + 1)
      2 * (bitPolyEval t (a &&& U) - bitPolyEval t (a &&& (U ^^^ (2 ^ (k + 1) * a)))) := by
  rw [sum_mul_schurX t hm (fun i => bitPolyEval t (clmul a (2 * i + 1))) j]
  have hj_lt : j.1 < 2 ^ k := lt_of_lt_of_le j.2 hm
  by_cases hj0 : j.1 = 0
  · simp only [hj0, ↓reduceIte, add_zero, mul_zero, zero_add, clmul_one_right]
    have harg : 2 * 2 ^ k + 1 = 1 ^^^ 2 ^ (k + 1) := by
      rw [xor_eq_add_of_and_eq_zero]
      · rw [pow_succ]; ring
      · have h1 : 1 < 2 ^ (k + 1) := by
          have : 0 < 2 ^ k := by positivity
          rw [pow_succ]; omega
        have h := and_eq_zero_of_lt_two_pow_mul (b := 1) h1
        rw [mul_one] at h; exact h
    rw [harg, clmul_xor_right, clmul_one_right, clmul_pow_two_right,
        bitPolyEval_xor, bitPolyEval_pow_two_mul]
    ring
  · simp only [hj0, ↓reduceIte]
    set v := ctz j.1
    set q := j.1 / 2 ^ (v + 1)
    have hv_lt : v < k := ctz_lt_of_lt_two_pow hj0 hj_lt
    have ⟨hodd, hmul⟩ := ctz_spec j.1 hj0
    have hj_eq : j.1 = 2 ^ v * (2 * q + 1) := by
      have hdiv : j.1 / 2 ^ (v + 1) = (j.1 / 2 ^ v) / 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
      have hodd' : (j.1 / 2 ^ v) % 2 = 1 := hodd
      have h2q : 2 * q + 1 = j.1 / 2 ^ v := by
        dsimp [q]; rw [hdiv]; omega
      rw [h2q, hmul]
    have hq_lt_half : q < 2 ^ (k - 1 - v) := by
      have hpow : 2 ^ k = 2 ^ v * (2 * 2 ^ (k - 1 - v)) := by
        have : k = v + 1 + (k - 1 - v) := by omega
        conv_lhs => rw [this, pow_add, pow_add, pow_one]
        ac_rfl
      have h1 : 2 ^ v * (2 * q + 1) < 2 ^ v * (2 * 2 ^ (k - 1 - v)) := by
        rw [← hj_eq, ← hpow]; exact hj_lt
      have h2 : 2 * q + 1 < 2 * 2 ^ (k - 1 - v) := Nat.lt_of_mul_lt_mul_left h1
      omega
    set b1 := 2 * q + 1
    set b2 := 2 * (2 ^ (k - 1 - v) + q) + 1
    set U := 2 ^ (v + 1) * clmul a b1
    set U' := 2 ^ (v + 1) * clmul a b2
    -- Express 2*j + 1 = 1 ^^^ (2^(v+1) * b1) and 2*(2^k + j) + 1 = 1 ^^^ (2^(v+1) * b2)
    have h2j1 : 2 * j.1 + 1 = 1 ^^^ (2 ^ (v + 1) * b1) := by
      rw [xor_eq_add_of_and_eq_zero]
      · rw [hj_eq, pow_succ]; dsimp [b1]; ring
      · have h1 : 1 < 2 ^ (v + 1) := by
          have : 0 < 2 ^ v := by positivity
          rw [pow_succ]; omega
        exact and_eq_zero_of_lt_two_pow_mul h1
    have h2Nj1 : 2 * (2 ^ k + j.1) + 1 = 1 ^^^ (2 ^ (v + 1) * b2) := by
      rw [xor_eq_add_of_and_eq_zero]
      · have hpow : 2 ^ (v + 1) * (2 * 2 ^ (k - 1 - v)) = 2 * 2 ^ k := by
          have : k + 1 = (v + 1) + 1 + (k - 1 - v) := by omega
          calc 2 ^ (v + 1) * (2 * 2 ^ (k - 1 - v))
              = 2 ^ (v + 1) * 2 ^ 1 * 2 ^ (k - 1 - v) := by rw [pow_one]; ring
            _ = 2 ^ ((v + 1) + 1 + (k - 1 - v)) := by rw [← pow_add, ← pow_add]
            _ = 2 ^ (k + 1) := by rw [← this]
            _ = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
        calc 2 * (2 ^ k + j.1) + 1
            = 1 + (2 * 2 ^ k + 2 * (2 ^ v * b1)) := by rw [hj_eq]; dsimp [b1]; ring
          _ = 1 + (2 ^ (v + 1) * (2 * 2 ^ (k - 1 - v)) + 2 ^ (v + 1) * b1) := by
              rw [hpow, pow_succ]; ring
          _ = 1 + 2 ^ (v + 1) * b2 := by dsimp [b1, b2]; ring
      · have h1 : 1 < 2 ^ (v + 1) := by
          have : 0 < 2 ^ v := by positivity
          rw [pow_succ]; omega
        exact and_eq_zero_of_lt_two_pow_mul h1
    -- Show U' = U ^^^ (2^(k + 1) * a)
    have hb2_xor : b2 = b1 ^^^ 2 ^ (k - v) := by
      rw [xor_eq_add_of_and_eq_zero]
      · have hpow : 2 ^ (k - v) = 2 * 2 ^ (k - 1 - v) := by
          have : k - v = (k - 1 - v) + 1 := by omega
          conv_lhs => rw [this, pow_succ, mul_comm]
        rw [hpow]; dsimp [b1, b2]; ring
      · have hb1_lt : b1 < 2 ^ (k - v) := by
          have hpow : 2 ^ (k - v) = 2 * 2 ^ (k - 1 - v) := by
            have : k - v = (k - 1 - v) + 1 := by omega
            conv_lhs => rw [this, pow_succ, mul_comm]
          dsimp [b1]; omega
        simpa using and_eq_zero_of_lt_two_pow_mul (b := 1) hb1_lt
    have hU'_eq : U' = U ^^^ (2 ^ (k + 1) * a) := by
      have hpow_mul_xor : ∀ r x y : ℕ, 2 ^ r * (x ^^^ y) = (2 ^ r * x) ^^^ (2 ^ r * y) := by
        intro r x y
        induction r with
        | zero => simp
        | succ r ihr => rw [pow_succ', mul_assoc, mul_assoc, mul_assoc, ihr, two_mul_xor]
      have hpow_sum : 2 ^ (v + 1) * 2 ^ (k - v) = 2 ^ (k + 1) := by
        rw [← pow_add]; congr 1; omega
      dsimp [U', U]
      rw [hb2_xor, clmul_xor_right, clmul_pow_two_right, hpow_mul_xor, ← mul_assoc, hpow_sum]
    -- Apply bitPolyEval_xor to a ^^^ U' and a ^^^ U
    have hcl1 : clmul a (2 * j.1 + 1) = a ^^^ U := by
      rw [h2j1, clmul_xor_right, clmul_one_right, clmul_pow_two_mul_right]
    have hcl2 : clmul a (2 * (2 ^ k + j.1) + 1) = a ^^^ U' := by
      rw [h2Nj1, clmul_xor_right, clmul_one_right, clmul_pow_two_mul_right]
    have heval_U : t ^ (v + 1) * bitPolyEval t (clmul a b1) = bitPolyEval t U := by
      dsimp [U]; rw [bitPolyEval_pow_two_mul]
    have heval_U' : t ^ (v + 1) * bitPolyEval t (clmul a b2) = bitPolyEval t U' := by
      dsimp [U']; rw [bitPolyEval_pow_two_mul]
    rw [hcl2, hcl1, heval_U', heval_U, bitPolyEval_xor, bitPolyEval_xor, ← hU'_eq]
    ring

/-! ## Section 3: Master Schur Reduction Theorem over Arbitrary Commutative Rings -/

/-- Master exact polynomial block Schur reduction over ANY commutative ring `R`:
for every `k : ℕ`, `m ≤ 2^k`, and `t : R`,
`det(M_{2^k + m}(t)) = det(M_{2^k}(t)) * (-2 * t^(k + 1))^m * det(revHadamard R k m)`. -/
theorem det_oddClmulMatrix_add {R : Type*} [CommRing R] (t : R) (k m : ℕ) (hm : m ≤ 2 ^ k) :
    (oddClmulMatrix t (2 ^ k + m)).det =
      (oddClmulMatrix t (2 ^ k)).det * (-2 * t ^ (k + 1)) ^ m * (revHadamard R k m).det := by
  set N := 2 ^ k
  let e : Fin N ⊕ Fin m ≃ Fin (N + m) := finSumFinEquiv
  let Mblk : Matrix (Fin N ⊕ Fin m) (Fin N ⊕ Fin m) R :=
    (oddClmulMatrix t (N + m)).submatrix e e
  let X := schurX t k m
  let L : Matrix (Fin N ⊕ Fin m) (Fin N ⊕ Fin m) R :=
    Matrix.fromBlocks 1 0 (-X.transpose) 1
  let U : Matrix (Fin N ⊕ Fin m) (Fin N ⊕ Fin m) R :=
    Matrix.fromBlocks 1 (-X) 0 1
  let A : Matrix (Fin N) (Fin N) R := oddClmulMatrix t N
  let B : Matrix (Fin N) (Fin m) R :=
    Matrix.of fun i j => bitPolyEval t (clmul (2 * i.1 + 1) (2 * (N + j.1) + 1))
  let C : Matrix (Fin m) (Fin m) R :=
    Matrix.of fun r j => bitPolyEval t (clmul (2 * (N + r.1) + 1) (2 * (N + j.1) + 1))
  have hMblk : Mblk = Matrix.fromBlocks A B B.transpose C := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Mblk, e, A, oddClmulMatrix]
      | inr j => simp [Mblk, e, B, oddClmulMatrix]
    | inr i =>
      cases j with
      | inl j =>
        simp only [Mblk, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply,
          B, oddClmulMatrix, Matrix.of_apply, e, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
          Fin.val_natAdd, Fin.val_castAdd, clmul_comm]
      | inr j => simp [Mblk, e, C, oddClmulMatrix]
  -- Top block identity: A * X = B
  have hAX : A * X = B := by
    ext i j
    have ha_lt : 2 * i.1 + 1 < 2 ^ (k + 1) := by
      have hi := i.2; rw [pow_succ]; omega
    have hdisj : (2 * i.1 + 1) &&& (2 ^ (k + 1) * (2 * i.1 + 1)) = 0 :=
      and_eq_zero_of_lt_two_pow_mul ha_lt
    have hrow := row_elim_identity t hm (2 * i.1 + 1) j
    have hrhs0 :
        bitPolyEval t (clmul (2 * i.1 + 1) (2 * (2 ^ k + j.1) + 1)) -
          (∑ x : Fin (2 ^ k), bitPolyEval t (clmul (2 * i.1 + 1) (2 * x.1 + 1)) * schurX t k m x j) = 0 := by
      rw [hrow]
      by_cases hj0 : j.1 = 0
      · simp [hj0, hdisj, bitPolyEval_zero]
      · simp only [hj0, ↓reduceIte]
        set v := ctz j.1
        set q := j.1 / 2 ^ (v + 1)
        set Uv := 2 ^ (v + 1) * clmul (2 * i.1 + 1) (2 * q + 1)
        have hand_eq : (2 * i.1 + 1) &&& (Uv ^^^ (2 ^ (k + 1) * (2 * i.1 + 1))) =
            (2 * i.1 + 1) &&& Uv := by
          apply Nat.eq_of_testBit_eq; intro u
          rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor]
          have h0 := congrArg (fun n => n.testBit u) hdisj
          rw [Nat.testBit_and, Nat.zero_testBit] at h0
          cases hb1 : (2 * i.1 + 1).testBit u <;> cases hb2 : Uv.testBit u <;>
            cases hb3 : (2 ^ (k + 1) * (2 * i.1 + 1)).testBit u <;> simp_all
        rw [hand_eq, sub_self, mul_zero]
    have hmul_eq : (A * X) i j =
        ∑ x : Fin (2 ^ k), bitPolyEval t (clmul (2 * i.1 + 1) (2 * x.1 + 1)) * schurX t k m x j := by
      simp only [A, X, oddClmulMatrix, Matrix.mul_apply, Matrix.of_apply, N]
    have hB_eq : B i j = bitPolyEval t (clmul (2 * i.1 + 1) (2 * (2 ^ k + j.1) + 1)) := by
      simp [B, N]
    rw [hmul_eq, hB_eq]
    exact (sub_eq_zero.mp hrhs0).symm
  -- Bottom block identity: C - Bᵀ * X = (-2 * t^(k + 1)) • revHadamard R k m
  have hSchur : C - B.transpose * X = (-2 * t ^ (k + 1)) • revHadamard R k m := by
    ext r j
    have hr_lt : r.1 < 2 ^ k := lt_of_lt_of_le r.2 hm
    have hj_lt : j.1 < 2 ^ k := lt_of_lt_of_le j.2 hm
    set a := 2 * (2 ^ k + r.1) + 1
    have hbtX : (C - B.transpose * X) r j =
        bitPolyEval t (clmul a (2 * (2 ^ k + j.1) + 1)) -
          (∑ x : Fin (2 ^ k), bitPolyEval t (clmul a (2 * x.1 + 1)) * schurX t k m x j) := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, C, B, X,
        Matrix.of_apply, N, a]
      congr 1
      refine Finset.sum_congr rfl fun x _ => by rw [clmul_comm]
    rw [hbtX, row_elim_identity t hm a j]
    have hand_a : a &&& (2 ^ (k + 1) * a) = 2 ^ (k + 1) := odd_upper_and_shift hr_lt
    by_cases hj0 : j.1 = 0
    · simp only [hj0, ↓reduceIte, hand_a, bitPolyEval_pow_two, Matrix.smul_apply, smul_eq_mul,
        revHadamard, Matrix.of_apply, Nat.and_zero, popcntK, Nat.zero_testBit,
        Bool.false_eq_true, Finset.filter_false, Finset.card_empty, pow_zero, mul_one]
    · simp only [hj0, ↓reduceIte, Matrix.smul_apply, smul_eq_mul, revHadamard, Matrix.of_apply]
      set v := ctz j.1
      set q := j.1 / 2 ^ (v + 1)
      set Uv := 2 ^ (v + 1) * clmul a (2 * q + 1)
      -- Show a &&& (Uv ^^^ (2^(k+1) * a)) = (a &&& Uv) ^^^ 2^(k+1)
      have hand_xor : a &&& (Uv ^^^ (2 ^ (k + 1) * a)) = (a &&& Uv) ^^^ 2 ^ (k + 1) := by
        apply Nat.eq_of_testBit_eq; intro u
        have h1 := congrArg (fun n => n.testBit u) hand_a
        rw [Nat.testBit_and] at h1
        rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, ← h1]
        cases a.testBit u <;> cases Uv.testBit u <;> cases (2 ^ (k + 1) * a).testBit u <;> rfl
      rw [hand_xor, bitPolyEval_xor, bitPolyEval_pow_two]
      -- Compute (a &&& Uv) &&& 2^(k+1) = if Uv.testBit (k+1) then 2^(k+1) else 0
      have ha_top : a.testBit (k + 1) = true := by
        have h1 := congrArg (fun n => n.testBit (k + 1)) hand_a
        rw [Nat.testBit_and, Nat.testBit_two_pow_self] at h1
        cases ha : a.testBit (k + 1)
        · simp [ha] at h1
        · rfl
      have hand_bit : (a &&& Uv) &&& 2 ^ (k + 1) =
          if Uv.testBit (k + 1) then 2 ^ (k + 1) else 0 := by
        apply Nat.eq_of_testBit_eq; intro u
        rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_two_pow]
        by_cases hu : k + 1 = u
        · subst hu
          cases hUv : Uv.testBit (k + 1) <;> simp [ha_top]
        · cases hUv : Uv.testBit (k + 1) <;> simp [hu]
      rw [hand_bit]
      have hU_bit : Uv.testBit (k + 1) = decide (popcntK k (bitrevNat k r.1 &&& j.1) % 2 = 1) :=
        testBit_U_eq_popcnt_rev hr_lt hj0 hj_lt
      rw [hU_bit]
      rcases Nat.mod_two_eq_zero_or_one (popcntK k (bitrevNat k r.1 &&& j.1)) with hp | hp
      · have hpow_even : (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1) = 1 := by
          have : Even (popcntK k (bitrevNat k r.1 &&& j.1)) := Nat.even_iff.mpr hp
          exact Even.neg_one_pow this
        simp only [hp, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, bitPolyEval_zero,
          hpow_even]
        ring
      · have hpow_odd : (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1) = -1 := by
          have : Odd (popcntK k (bitrevNat k r.1 &&& j.1)) := Nat.odd_iff.mpr hp
          exact Odd.neg_one_pow this
        simp only [hp, decide_true, ↓reduceIte, bitPolyEval_pow_two, hpow_odd]
        ring
  -- Block congruence: L * Mblk * U = diag(A, (-2 * t^(k+1)) • revHadamard R k m)
  have hdiag : L * Mblk * U =
      Matrix.fromBlocks A 0 0 ((-2 * t ^ (k + 1)) • revHadamard R k m) := by
    rw [hMblk]
    simp only [L, U, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.neg_mul, Matrix.mul_neg]
    have hA_symm : A.transpose = A := by
      ext i j; simp [A, oddClmulMatrix, clmul_comm]
    have h21 : -(X.transpose * A) + B.transpose = 0 := by
      have h1 := congrArg Matrix.transpose hAX
      rw [Matrix.transpose_mul, hA_symm] at h1
      rw [h1, neg_add_cancel]
    have h12 : -(A * X) + B = 0 := by rw [hAX, neg_add_cancel]
    rw [h21, h12]
    congr 1
    rw [Matrix.zero_mul, neg_zero, zero_add]
    have hsym : X.transpose * B = B.transpose * X := by
      have h1 := congrArg Matrix.transpose hAX
      rw [Matrix.transpose_mul, hA_symm] at h1
      calc X.transpose * B = X.transpose * (A * X) := by rw [hAX]
        _ = (X.transpose * A) * X := by rw [Matrix.mul_assoc]
        _ = B.transpose * X := by rw [h1]
    rw [hsym, ← hSchur, neg_add_eq_sub]
  have hL_det : L.det = 1 := by simp [L]
  have hU_det : U.det = 1 := by simp [U]
  have hdet := congrArg Matrix.det hdiag
  rw [Matrix.det_mul, Matrix.det_mul, hL_det, hU_det, one_mul, mul_one,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Fintype.card_fin] at hdet
  have hMblk_det : Mblk.det = (oddClmulMatrix t (N + m)).det :=
    Matrix.det_submatrix_equiv_self e (oddClmulMatrix t (N + m))
  rw [hMblk_det] at hdet
  rw [hdet, mul_assoc]

/-! ## Section 4: Headline Theorems -/

theorem det_oddClmulMatrix_zero {R : Type*} [CommRing R] (t : R) :
    (oddClmulMatrix t 0).det = 1 := by
  simp

theorem det_oddClmulMatrix_one {R : Type*} [CommRing R] (t : R) :
    (oddClmulMatrix t 1).det = 1 := by
  rw [Matrix.det_fin_one]
  simp [oddClmulMatrix, clmul_one_right, bitPolyEval_one]

/-- Theorem 2 (Exact `2^k → 2^k + 1` recurrence):
for every `k : ℕ`, every commutative ring `R`, and every `t : R`,
`det(M_{2^k + 1}(t)) = (-2 * t^(k + 1)) * det(M_{2^k}(t))`. -/
theorem det_oddClmulMatrix_pow_two_add_one {R : Type*} [CommRing R] (t : R) (k : ℕ) :
    (oddClmulMatrix t (2 ^ k + 1)).det =
      (-2 * t ^ (k + 1)) * (oddClmulMatrix t (2 ^ k)).det := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [det_oddClmulMatrix_add t k 1 h1]
  have hrev1 : (revHadamard R k 1).det = 1 := by
    rw [Matrix.det_fin_one]
    simp [revHadamard, bitrevNat_zero, popcntK]
  rw [hrev1, pow_one, mul_one, mul_comm]

/-- Theorem 1 (Exact monomial determinant at `n = 2^k`):
for every `k ≥ 1`, every commutative ring `R`, and every `t : R`,
`det(M_{2^k}(t)) = ± 2^(k · 2^(k - 1)) · t^((k - 1) · 2^k + 1)`. -/
theorem det_oddClmulMatrix_pow_two {R : Type*} [CommRing R] (t : R) (k : ℕ) (hk : 1 ≤ k) :
    (oddClmulMatrix t (2 ^ k)).det =
      (if k = 2 then (1 : R) else -1) * (2 : R) ^ (k * 2 ^ (k - 1)) * t ^ ((k - 1) * 2 ^ k + 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      have h2 := det_oddClmulMatrix_pow_two_add_one t 0
      rw [pow_zero, det_oddClmulMatrix_one] at h2
      simpa using h2
    · have hk1 : 1 ≤ k := by omega
      have hih := ih hk1
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      rw [hpow, det_oddClmulMatrix_add t k (2 ^ k) (le_refl _), hih, det_revHadamard_full R k]
      -- (-2 * t^(k+1))^(2^k) = 2^(2^k) * t^((k+1) * 2^k) since 2^k is even
      have heven : Even (2 ^ k) := by
        have : 2 ^ k = 2 * 2 ^ (k - 1) := by
          have hk' : k = (k - 1) + 1 := by omega
          conv_lhs => rw [hk', pow_succ, mul_comm]
        exact ⟨2 ^ (k - 1), by omega⟩
      have hneg_pow : (-2 * t ^ (k + 1)) ^ (2 ^ k) =
          (2 : R) ^ (2 ^ k) * t ^ ((k + 1) * 2 ^ k) := by
        rw [show (-2 * t ^ (k + 1)) = (-1 : R) * (2 * t ^ (k + 1)) by ring,
            mul_pow, Even.neg_one_pow heven, one_mul, mul_pow, ← pow_mul]
      rw [hneg_pow]
      -- Combine powers of 2 and t
      have hexp2 : k * 2 ^ (k - 1) + 2 ^ k + k * 2 ^ (k - 1) = (k + 1) * 2 ^ k := by
        have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
          have hk' : k = (k - 1) + 1 := by omega
          conv_lhs => rw [hk', pow_succ, mul_comm]
        rw [h2k]; ring
      have hexpt : ((k - 1) * 2 ^ k + 1) + (k + 1) * 2 ^ k = k * (2 ^ k + 2 ^ k) + 1 := by
        have : (k - 1) + (k + 1) = 2 * k := by omega
        calc (k - 1) * 2 ^ k + 1 + (k + 1) * 2 ^ k
            = ((k - 1) + (k + 1)) * 2 ^ k + 1 := by ring
          _ = (2 * k) * 2 ^ k + 1 := by rw [this]
          _ = k * (2 ^ k + 2 ^ k) + 1 := by ring
      have h2_comb : (2 : R) ^ (k * 2 ^ (k - 1)) * (2 : R) ^ (2 ^ k) * (2 : R) ^ (k * 2 ^ (k - 1)) =
          (2 : R) ^ ((k + 1) * 2 ^ k) := by
        rw [← pow_add, ← pow_add, hexp2]
      have ht_comb : t ^ ((k - 1) * 2 ^ k + 1) * t ^ ((k + 1) * 2 ^ k) =
          t ^ (k * (2 ^ k + 2 ^ k) + 1) := by
        rw [← pow_add, hexpt]
      have hsign : (if k = 2 then (1 : R) else -1) * (if k = 1 ∨ k = 2 then (-1 : R) else 1) =
          if k + 1 = 2 then (1 : R) else -1 := by
        by_cases h1 : k = 1
        · subst h1; simp
        · by_cases h2 : k = 2
          · subst h2; simp
          · have hne : k + 1 ≠ 2 := by omega
            simp [h1, h2, hne]
      calc (if k = 2 then (1 : R) else -1) * (2 : R) ^ (k * 2 ^ (k - 1)) *
              t ^ ((k - 1) * 2 ^ k + 1) * ((2 : R) ^ (2 ^ k) * t ^ ((k + 1) * 2 ^ k)) *
              ((if k = 1 ∨ k = 2 then (-1 : R) else 1) * (2 : R) ^ (k * 2 ^ (k - 1)))
          = ((if k = 2 then (1 : R) else -1) * (if k = 1 ∨ k = 2 then (-1 : R) else 1)) *
            ((2 : R) ^ (k * 2 ^ (k - 1)) * (2 : R) ^ (2 ^ k) * (2 : R) ^ (k * 2 ^ (k - 1))) *
            (t ^ ((k - 1) * 2 ^ k + 1) * t ^ ((k + 1) * 2 ^ k)) := by ring
        _ = (if k + 1 = 2 then (1 : R) else -1) * (2 : R) ^ ((k + 1) * 2 ^ k) *
              t ^ (k * (2 ^ k + 2 ^ k) + 1) := by rw [hsign, h2_comb, ht_comb]
        _ = (if k + 1 = 2 then (1 : R) else -1) * (2 : R) ^ ((k + 1) * 2 ^ (k + 1 - 1)) *
              t ^ ((k + 1 - 1) * (2 ^ k + 2 ^ k) + 1) := by simp

/-- Theorem 3 (Exact monomial determinant at `n = 2^k - 1`):
for every `k ≥ 1`, every commutative ring `R`, and every `t : R`,
`det(M_{2^k - 1}(t)) = ± 2^(k · 2^(k - 1) - k) · t^((k - 1) · 2^k + 1 - k)`. -/
theorem det_oddClmulMatrix_pow_two_sub_one {R : Type*} [CommRing R] (t : R) (k : ℕ) (hk : 1 ≤ k) :
    (oddClmulMatrix t (2 ^ k - 1)).det =
      (if k ≤ 3 then (1 : R) else (-1 : R) ^ (k - 1)) *
        (2 : R) ^ (k * 2 ^ (k - 1) - k) * t ^ ((k - 1) * 2 ^ k + 1 - k) := by
  cases k with
  | zero => omega
  | succ k' =>
    by_cases hk0 : k' = 0
    · subst hk0
      rw [show 2 ^ (0 + 1) - 1 = 1 by norm_num, det_oddClmulMatrix_one]
      simp
    · have hk1 : 1 ≤ k' := by omega
      have hpos : 0 < 2 ^ k' := by positivity
      have hsplit : 2 ^ (k' + 1) - 1 = 2 ^ k' + (2 ^ k' - 1) := by
        rw [pow_succ]; omega
      rw [hsplit, det_oddClmulMatrix_add t k' (2 ^ k' - 1) (by omega),
          det_oddClmulMatrix_pow_two t k' hk1, det_revHadamard_sub_one R k' hk1]
      -- (-2 * t^(k'+1))^(2^k' - 1) = -1 * 2^(2^k' - 1) * t^((k'+1) * (2^k' - 1))
      have hodd : Odd (2 ^ k' - 1) := by
        have h2k : 2 ^ k' = 2 * 2 ^ (k' - 1) := by
          have : k' = (k' - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ, mul_comm]
        have hpos' : 0 < 2 ^ (k' - 1) := by positivity
        exact ⟨2 ^ (k' - 1) - 1, by omega⟩
      have hneg_pow : (-2 * t ^ (k' + 1)) ^ (2 ^ k' - 1) =
          (-1 : R) * (2 : R) ^ (2 ^ k' - 1) * t ^ ((k' + 1) * (2 ^ k' - 1)) := by
        rw [show (-2 * t ^ (k' + 1)) = (-1 : R) * (2 * t ^ (k' + 1)) by ring,
            mul_pow, Odd.neg_one_pow hodd, mul_pow, ← pow_mul, mul_assoc]
      rw [hneg_pow]
      have h2k_eq : 2 ^ k' = 2 * 2 ^ (k' - 1) := by
        have : k' = (k' - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ, mul_comm]
      have hle_k : k' ≤ k' * 2 ^ (k' - 1) :=
        Nat.le_mul_of_pos_right k' (by positivity)
      have hsub1 : (k' + 1) * 2 ^ k' = 2 * (k' * 2 ^ (k' - 1)) + 2 ^ k' := by
        rw [h2k_eq]; ring
      have hexp2 : k' * 2 ^ (k' - 1) + (2 ^ k' - 1) + (k' * 2 ^ (k' - 1) - k') =
          (k' + 1) * 2 ^ k' - (k' + 1) := by omega
      have hexpt : ((k' - 1) * 2 ^ k' + 1) + (k' + 1) * (2 ^ k' - 1) =
          k' * 2 ^ (k' + 1) + 1 - (k' + 1) := by
        have h1 : (k' + 1) * (2 ^ k' - 1) + (k' + 1) = (k' + 1) * 2 ^ k' := by
          calc (k' + 1) * (2 ^ k' - 1) + (k' + 1)
              = (k' + 1) * ((2 ^ k' - 1) + 1) := by ring
            _ = (k' + 1) * 2 ^ k' := by rw [Nat.sub_add_cancel (by omega)]
        have h2 : (k' - 1) * 2 ^ k' + (k' + 1) * 2 ^ k' = k' * 2 ^ (k' + 1) := by
          have : (k' - 1) + (k' + 1) = 2 * k' := by omega
          calc (k' - 1) * 2 ^ k' + (k' + 1) * 2 ^ k'
              = ((k' - 1) + (k' + 1)) * 2 ^ k' := by ring
            _ = (2 * k') * 2 ^ k' := by rw [this]
            _ = k' * 2 ^ (k' + 1) := by rw [pow_succ]; ring
        omega
      have h2_comb : (2 : R) ^ (k' * 2 ^ (k' - 1)) * (2 : R) ^ (2 ^ k' - 1) *
          (2 : R) ^ (k' * 2 ^ (k' - 1) - k') = (2 : R) ^ ((k' + 1) * 2 ^ k' - (k' + 1)) := by
        rw [← pow_add, ← pow_add, hexp2]
      have ht_comb : t ^ ((k' - 1) * 2 ^ k' + 1) * t ^ ((k' + 1) * (2 ^ k' - 1)) =
          t ^ (k' * 2 ^ (k' + 1) + 1 - (k' + 1)) := by
        rw [← pow_add, hexpt]
      have hsign : (if k' = 2 then (1 : R) else -1) * (-1 : R) *
          (if k' = 1 then (1 : R) else if k' = 2 then -1 else (-1 : R) ^ k') =
          if k' + 1 ≤ 3 then (1 : R) else (-1 : R) ^ k' := by
        by_cases h1 : k' = 1
        · subst h1; simp
        · by_cases h2 : k' = 2
          · subst h2; simp
          · have hnotle : ¬(k' + 1 ≤ 3) := by omega
            simp [h1, h2, hnotle]
      calc (if k' = 2 then (1 : R) else -1) * (2 : R) ^ (k' * 2 ^ (k' - 1)) *
              t ^ ((k' - 1) * 2 ^ k' + 1) *
              ((-1 : R) * (2 : R) ^ (2 ^ k' - 1) * t ^ ((k' + 1) * (2 ^ k' - 1))) *
              ((if k' = 1 then (1 : R) else if k' = 2 then -1 else (-1 : R) ^ k') *
                (2 : R) ^ (k' * 2 ^ (k' - 1) - k'))
          = ((if k' = 2 then (1 : R) else -1) * (-1 : R) *
              (if k' = 1 then (1 : R) else if k' = 2 then -1 else (-1 : R) ^ k')) *
            ((2 : R) ^ (k' * 2 ^ (k' - 1)) * (2 : R) ^ (2 ^ k' - 1) *
              (2 : R) ^ (k' * 2 ^ (k' - 1) - k')) *
            (t ^ ((k' - 1) * 2 ^ k' + 1) * t ^ ((k' + 1) * (2 ^ k' - 1))) := by ring
        _ = (if k' + 1 ≤ 3 then (1 : R) else (-1 : R) ^ k') *
            (2 : R) ^ ((k' + 1) * 2 ^ k' - (k' + 1)) *
            t ^ (k' * 2 ^ (k' + 1) + 1 - (k' + 1)) := by rw [hsign, h2_comb, ht_comb]
        _ = (if k' + 1 ≤ 3 then (1 : R) else (-1 : R) ^ (k' + 1 - 1)) *
            (2 : R) ^ ((k' + 1) * 2 ^ (k' + 1 - 1) - (k' + 1)) *
            t ^ ((k' + 1 - 1) * 2 ^ (k' + 1) + 1 - (k' + 1)) := by simp

/-- Theorem 4 (Identical vanishing on every gap `2^k + 2 ≤ n ≤ 2^(k + 1) - 2`):
for every commutative ring `R` and every `t : R`, `det(M_n(t)) = 0`. -/
theorem det_oddClmulMatrix_eq_zero_of_gap {R : Type*} [CommRing R] (t : R) (k n : ℕ)
    (hlo : 2 ^ k + 2 ≤ n) (hhi : n ≤ 2 ^ (k + 1) - 2) :
    (oddClmulMatrix t n).det = 0 := by
  set m := n - 2 ^ k
  have hn_eq : n = 2 ^ k + m := by omega
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  have hm_lo : 2 ≤ m := by omega
  have hm_hi : m ≤ 2 ^ k - 2 := by omega
  have hm_le : m ≤ 2 ^ k := by omega
  rw [hn_eq, det_oddClmulMatrix_add t k m hm_le, det_revHadamard_gap R k m hm_lo hm_hi, mul_zero]

/-- Theorem 5 (Complete non-vanishing locus):
over any integral domain `R` with `(2 : R) ≠ 0` and `t ≠ 0`, `det(M_n(t)) ≠ 0` if and only if
`n ∈ {2^k - 1, 2^k, 2^k + 1}` for some `k : ℕ`. -/
theorem det_oddClmulMatrix_ne_zero_iff {R : Type*} [CommRing R] [IsDomain R] (t : R)
    (h2 : (2 : R) ≠ 0) (ht : t ≠ 0) (n : ℕ) :
    (oddClmulMatrix t n).det ≠ 0 ↔
      ∃ k : ℕ, n = 2 ^ k - 1 ∨ n = 2 ^ k ∨ n = 2 ^ k + 1 := by
  have hneg1 : (-1 : R) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  constructor
  · intro hne
    by_contra hnot
    push Not at hnot
    have hn6 : 6 ≤ n := by
      by_contra hlt
      interval_cases n
      · exact (hnot 0).1 (by norm_num)
      · exact (hnot 0).2.1 (by norm_num)
      · exact (hnot 0).2.2 (by norm_num)
      · exact (hnot 2).1 (by norm_num)
      · exact (hnot 2).2.1 (by norm_num)
      · exact (hnot 2).2.2 (by norm_num)
    set k := Nat.log 2 n
    have hlo0 : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hhi0 : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by omega) n
    have hne0 := (hnot k).2.1
    have hne1 := (hnot k).2.2
    have hne_top := (hnot (k + 1)).1
    have hlo : 2 ^ k + 2 ≤ n := by omega
    have hhi : n ≤ 2 ^ (k + 1) - 2 := by omega
    exact hne (det_oddClmulMatrix_eq_zero_of_gap t k n hlo hhi)
  · rintro ⟨k, rfl | rfl | rfl⟩
    · -- n = 2^k - 1
      by_cases hk : k = 0
      · subst hk; simp
      · rw [det_oddClmulMatrix_pow_two_sub_one t k (by omega)]
        refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ h2)) (pow_ne_zero _ ht)
        split_ifs
        · exact one_ne_zero
        · exact pow_ne_zero _ hneg1
    · -- n = 2^k
      by_cases hk : k = 0
      · subst hk
        rw [pow_zero, det_oddClmulMatrix_one]
        exact one_ne_zero
      · rw [det_oddClmulMatrix_pow_two t k (by omega)]
        refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ h2)) (pow_ne_zero _ ht)
        split_ifs <;> [exact one_ne_zero; exact hneg1]
    · -- n = 2^k + 1
      rw [det_oddClmulMatrix_pow_two_add_one t k]
      have hfac : -2 * t ^ (k + 1) ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr h2) (pow_ne_zero _ ht)
      refine mul_ne_zero hfac ?_
      by_cases hk : k = 0
      · subst hk
        rw [pow_zero, det_oddClmulMatrix_one]
        exact one_ne_zero
      · rw [det_oddClmulMatrix_pow_two t k (by omega)]
        refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ h2)) (pow_ne_zero _ ht)
        split_ifs <;> [exact one_ne_zero; exact hneg1]

end ClmulLiftDeterminants
