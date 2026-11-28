/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NegabinaryCarryDet.Defs

/-!
# Core Proofs for Negabinary (Base `-2`) Carry-Borrow Determinants

Proves unconditionally over any commutative ring `R` and all `n : ℕ`:
1. Exact Base-`(-2)` Digit-Sum Conservation (`negAdd_popcount_conservation`).
2. Bitwise characterization of `runPrefix` (`runPrefix_iff_bits`).
3. Exact lower-unitriangular `LDLᵀ` factorization of the zero-positive-carry matrix
   `negZeroPosCarryMat R n = runPrefixMat R n * thueMorseDiag R n * (runPrefixMat R n)ᵀ`,
   yielding `det = ∏ k < n, (-1) ^ popcount k` for every `n : ℕ`.
4. Exact zero-borrow matrix determinant `det (negZeroBorrowMat R n) = ∏ k < n, (-1) ^ popcount k`
   together with concrete witnesses that `negZeroPosCarryMat ≠ disjointBitMat`.
5. Exact even/odd block-decoupling of `negParityMat R 0 n` and `negKMat R m`, and the
   machine-checked `n = 34` spontaneous prime-factor-`3` anomaly (`negParityMat_n34_anomaly`).
-/

namespace NegabinaryCarryDet

open Matrix BigOperators

/-! ## Section 1: Basic `popcount` and `negAddFullAux` Fuel-Independence Lemmas -/

lemma popcount_zero : popcount 0 = 0 := by simp [popcount]

lemma popcount_eq (n : ℕ) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => simp [popcount]
  | succ k => simp [popcount]

lemma popcount_two_mul (n : ℕ) : popcount (2 * n) = popcount n := by
  cases n with
  | zero => simp [popcount]
  | succ k =>
    rw [popcount_eq (2 * (k + 1))]
    simp

lemma popcount_two_mul_add_one (n : ℕ) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_eq (2 * n + 1)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

lemma popcount_bit_add (d s : ℕ) (hd : d ≤ 1) :
    popcount (d + 2 * s) = d + popcount s := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · simp [popcount_two_mul]
  · rw [show 1 + 2 * s = 2 * s + 1 by omega, popcount_two_mul_add_one]

private lemma negStep_carry_mem (cin : ℤ) (a b : ℕ) :
    (negStep cin a b).2.1 = -1 ∨ (negStep cin a b).2.1 = 0 ∨ (negStep cin a b).2.1 = 1 := by
  unfold negStep
  dsimp only
  split_ifs <;> simp

lemma negAddFullAux_zero_zero_zero (f : ℕ) :
    negAddFullAux f 0 0 0 = (0, 0, 0) := by
  induction f with
  | zero => rfl
  | succ f ih =>
    simp [negAddFullAux, negStep, ih]

lemma negAddFullAux_zero_zero_one (f : ℕ) (hf : 1 ≤ f) :
    negAddFullAux f 1 0 0 = (1, 0, 0) := by
  cases f with
  | zero => omega
  | succ f =>
    simp [negAddFullAux, negStep, negAddFullAux_zero_zero_zero]

lemma negAddFullAux_zero_zero_negOne (f : ℕ) (hf : 2 ≤ f) :
    negAddFullAux f (-1) 0 0 = (3, 1, 0) := by
  match f with
  | 0 | 1 => omega
  | f + 2 =>
    simp [negAddFullAux, negStep, negAddFullAux_zero_zero_zero]

lemma negAddFullAux_fuel_irrel :
    ∀ f1 f2 : ℕ, ∀ cin : ℤ, ∀ i j : ℕ,
      (cin = -1 ∨ cin = 0 ∨ cin = 1) →
      max i j + 2 ≤ f1 → max i j + 2 ≤ f2 →
      negAddFullAux f1 cin i j = negAddFullAux f2 cin i j := by
  intro f1
  induction f1 with
  | zero => intro f2 cin i j _ h1 _; omega
  | succ f1 ih =>
    intro f2 cin i j hcin h1 h2
    cases f2 with
    | zero => omega
    | succ f2 =>
      by_cases h0 : i = 0 ∧ j = 0
      · rcases h0 with ⟨rfl, rfl⟩
        rcases hcin with rfl | rfl | rfl
        · rw [negAddFullAux_zero_zero_negOne _ (by omega),
              negAddFullAux_zero_zero_negOne _ (by omega)]
        · rw [negAddFullAux_zero_zero_zero, negAddFullAux_zero_zero_zero]
        · rw [negAddFullAux_zero_zero_one _ (by omega),
              negAddFullAux_zero_zero_one _ (by omega)]
      · have hmax : max (i / 2) (j / 2) < max i j := by omega
        simp only [negAddFullAux]
        have hc' := negStep_carry_mem cin (i % 2) (j % 2)
        have heq := ih f2 (negStep cin (i % 2) (j % 2)).2.1 (i / 2) (j / 2) hc' (by omega) (by omega)
        rw [heq]

lemma negAddFull_unfold (cin : ℤ) (i j : ℕ) :
    negAddFullAux (negFuel i j) cin i j =
      let (d, c', pc, nb) := negStep cin (i % 2) (j % 2)
      let (sRest, pcRest, nbRest) := negAddFullAux (negFuel (i / 2) (j / 2)) c' (i / 2) (j / 2)
      (d + 2 * sRest, pc + pcRest, nb + nbRest) := by
  unfold negFuel
  change (let (d, c', pc, nb) := negStep cin (i % 2) (j % 2)
      let (sRest, pcRest, nbRest) := negAddFullAux (max i j + 3) c' (i / 2) (j / 2)
      (d + 2 * sRest, pc + pcRest, nb + nbRest)) = _
  have hc' := negStep_carry_mem cin (i % 2) (j % 2)
  have hirr := negAddFullAux_fuel_irrel (max i j + 3) (max (i / 2) (j / 2) + 4)
    (negStep cin (i % 2) (j % 2)).2.1 (i / 2) (j / 2) hc' (by omega) (by omega)
  dsimp only
  rw [hirr]

/-! ## Section 2: Theorem 1 — Exact Base-`(-2)` Digit-Sum Conservation Law -/

private lemma negAddFullAux_conservation :
    ∀ f : ℕ, ∀ cin : ℤ, ∀ i j : ℕ,
      (cin = -1 ∨ cin = 0 ∨ cin = 1) → max i j + 2 ≤ f →
      (popcount i : ℤ) + popcount j + cin - popcount (negAddFullAux f cin i j).1 =
        3 * ((negAddFullAux f cin i j).2.2 - (negAddFullAux f cin i j).2.1) := by
  intro f
  induction f with
  | zero => intro cin i j _ h; omega
  | succ f ih =>
    intro cin i j hcin hf
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩
      rcases hcin with rfl | rfl | rfl
      · rw [negAddFullAux_zero_zero_negOne _ (by omega)]
        norm_num [popcount]
      · rw [negAddFullAux_zero_zero_zero]
        norm_num [popcount]
      · rw [negAddFullAux_zero_zero_one _ (by omega)]
        norm_num [popcount]
    · have hmax : max (i / 2) (j / 2) + 2 ≤ f := by omega
      have ha : i % 2 = 0 ∨ i % 2 = 1 := Nat.mod_two_eq_zero_or_one i
      have hb : j % 2 = 0 ∨ j % 2 = 1 := Nat.mod_two_eq_zero_or_one j
      have hd_le : (negStep cin (i % 2) (j % 2)).1 ≤ 1 := by
        unfold negStep
        rcases hcin with rfl | rfl | rfl <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
          simp [ha, hb]
      have hc' := negStep_carry_mem cin (i % 2) (j % 2)
      have hloc : ((i % 2 : ℕ) : ℤ) + (j % 2 : ℕ) + cin -
          ((negStep cin (i % 2) (j % 2)).1 : ℤ) - (negStep cin (i % 2) (j % 2)).2.1 =
          3 * (((negStep cin (i % 2) (j % 2)).2.2.2 : ℤ) - (negStep cin (i % 2) (j % 2)).2.2.1) := by
        unfold negStep
        rcases hcin with rfl | rfl | rfl <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
          simp [ha, hb]
      have hih := ih (negStep cin (i % 2) (j % 2)).2.1 (i / 2) (j / 2) hc' hmax
      have h1 : (negAddFullAux (f + 1) cin i j).1 =
          (negStep cin (i % 2) (j % 2)).1 +
            2 * (negAddFullAux f (negStep cin (i % 2) (j % 2)).2.1 (i / 2) (j / 2)).1 := rfl
      have h2 : (negAddFullAux (f + 1) cin i j).2.1 =
          (negStep cin (i % 2) (j % 2)).2.2.1 +
            (negAddFullAux f (negStep cin (i % 2) (j % 2)).2.1 (i / 2) (j / 2)).2.1 := rfl
      have h3 : (negAddFullAux (f + 1) cin i j).2.2 =
          (negStep cin (i % 2) (j % 2)).2.2.2 +
            (negAddFullAux f (negStep cin (i % 2) (j % 2)).2.1 (i / 2) (j / 2)).2.2 := rfl
      rw [h1, h2, h3, popcount_bit_add _ _ hd_le, popcount_eq i, popcount_eq j]
      push_cast at hloc ⊢
      linarith

/-- **Theorem 1 (Exact Base-`(-2)` Digit-Sum Conservation Law):**
For all `i, j : ℕ`,
`s_2(i) + s_2(j) - s_2(i +_{-2} j) = 3 * (negNegBorrows 0 i j - negPosCarries 0 i j)`. -/
theorem negAdd_popcount_conservation (i j : ℕ) :
    (popcount i : ℤ) + popcount j - popcount (negAdd 0 i j) =
      3 * ((negNegBorrows 0 i j : ℤ) - negPosCarries 0 i j) := by
  have h := negAddFullAux_conservation (negFuel i j) 0 i j (Or.inr (Or.inl rfl))
    (by unfold negFuel; omega)
  simpa [negAdd, negNegBorrows, negPosCarries] using h

/-! ## Section 3: Theorem 2 — Bitwise Characterization of `runPrefix` -/

lemma runPrefix_zero (i : ℕ) : runPrefix i 0 = true := by simp [runPrefix]

lemma runPrefix_even (i k : ℕ) : runPrefix i (2 * k) = runPrefix (i / 2) k := by
  cases k with
  | zero => simp [runPrefix]
  | succ k =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    conv_lhs => unfold runPrefix
    have hmod : (2 * k + 1 + 1) % 2 = 0 := by omega
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    simp only [hmod, ↓reduceIte, hdiv]

lemma runPrefix_odd (i k : ℕ) :
    runPrefix i (2 * k + 1) =
      (decide (i % 2 = 1 ∧ (i / 2) % 2 = k % 2) && runPrefix (i / 2) k) := by
  conv_lhs => unfold runPrefix
  have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp only [hmod, ↓reduceIte, hdiv]

lemma runPrefix_self (i : ℕ) : runPrefix i i = true := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => exact runPrefix_zero 0
    | succ m =>
      set n := m + 1
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hk2 : n = 2 * k := by omega
        rw [hk2, runPrefix_even]
        have hdiv : (2 * k) / 2 = k := by omega
        rw [hdiv]
        exact ih k (by omega)
      · rw [hk, runPrefix_odd]
        have h1 : (2 * k + 1) % 2 = 1 := by omega
        have h2 : (2 * k + 1) / 2 = k := by omega
        rw [h1, h2]
        simp [ih k (by omega)]

lemma runPrefix_le {i k : ℕ} (h : runPrefix i k = true) : k ≤ i := by
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
    cases k with
    | zero => omega
    | succ m =>
      set n := m + 1
      rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
      · have hq2 : n = 2 * q := by omega
        rw [hq2, runPrefix_even] at h
        have := ih q (by omega) h
        omega
      · rw [hq, runPrefix_odd] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have := ih q (by omega) h.2
        omega

/-- **Theorem 2 (Bitwise Characterization of `runPrefix`):**
`runPrefix i k = true` iff `k` is a submask of `i` and whenever bit `r` of `k` is `1` and
bit `r + 1` of `k` is `0`, bit `r + 1` of `i` is also `0` (downward prefixes of `1`-runs). -/
theorem runPrefix_iff_bits (i k : ℕ) :
    runPrefix i k = true ↔
      (∀ r, k.testBit r = true → i.testBit r = true) ∧
      (∀ r, k.testBit r = true → k.testBit (r + 1) = false → i.testBit (r + 1) = false) := by
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
    cases k with
    | zero =>
      simp [runPrefix]
    | succ m =>
      set n := m + 1
      rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
      · have hq2 : n = 2 * q := by omega
        rw [hq2, runPrefix_even, ih q (by omega) (i / 2)]
        constructor
        · rintro ⟨hsub, hrun⟩
          refine ⟨fun r hr => ?_, fun r hr hnext => ?_⟩
          · cases r with
            | zero => simp [Nat.testBit_zero] at hr
            | succ r =>
              rw [Nat.testBit_succ] at hr ⊢
              exact hsub r (by simpa using hr)
          · cases r with
            | zero => simp [Nat.testBit_zero] at hr
            | succ r =>
              rw [Nat.testBit_succ] at hr hnext ⊢
              exact hrun r (by simpa using hr) (by simpa using hnext)
        · rintro ⟨hsub, hrun⟩
          refine ⟨fun r hr => ?_, fun r hr hnext => ?_⟩
          · have := hsub (r + 1) (by rw [Nat.testBit_succ]; simpa using hr)
            rw [Nat.testBit_succ] at this; exact this
          · have := hrun (r + 1) (by rw [Nat.testBit_succ]; simpa using hr)
              (by rw [Nat.testBit_succ]; simpa using hnext)
            rw [Nat.testBit_succ] at this; exact this
      · rw [hq, runPrefix_odd]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [ih q (by omega) (i / 2)]
        have hq_div : (2 * q + 1) / 2 = q := by omega
        have hq_mod : (2 * q + 1) % 2 = 1 := by omega
        constructor
        · rintro ⟨⟨hi0, hbit1⟩, hsub, hrun⟩
          refine ⟨fun r hr => ?_, fun r hr hnext => ?_⟩
          · cases r with
            | zero => simp [Nat.testBit_zero, hi0]
            | succ r =>
              rw [Nat.testBit_succ, hq_div] at hr
              rw [Nat.testBit_succ]
              exact hsub r hr
          · cases r with
            | zero =>
              rw [Nat.testBit_succ, hq_div, Nat.testBit_zero] at hnext
              rw [Nat.testBit_succ, Nat.testBit_zero]
              simpa [hbit1] using hnext
            | succ r =>
              rw [Nat.testBit_succ, hq_div] at hr hnext
              rw [Nat.testBit_succ]
              exact hrun r hr hnext
        · rintro ⟨hsub, hrun⟩
          have hi0 : i % 2 = 1 := by
            have := hsub 0 (by simp [Nat.testBit_zero, hq_mod])
            simpa [Nat.testBit_zero] using this
          have hbit1 : (i / 2) % 2 = q % 2 := by
            rcases Nat.mod_two_eq_zero_or_one q with hqm | hqm
            · have hq0 : (2 * q + 1).testBit 1 = false := by
                rw [Nat.testBit_succ, hq_div, Nat.testBit_zero]; simp [hqm]
              have hi1 := hrun 0 (by simp [Nat.testBit_zero, hq_mod]) hq0
              rw [Nat.testBit_succ, Nat.testBit_zero] at hi1
              have : (i / 2) % 2 ≠ 1 := by simpa using hi1
              omega
            · have hq1 : (2 * q + 1).testBit 1 = true := by
                rw [Nat.testBit_succ, hq_div, Nat.testBit_zero]; simp [hqm]
              have hi1 := hsub 1 hq1
              rw [Nat.testBit_succ, Nat.testBit_zero] at hi1
              have : (i / 2) % 2 = 1 := by simpa using hi1
              omega
          refine ⟨⟨hi0, hbit1⟩, fun r hr => ?_, fun r hr hnext => ?_⟩
          · have := hsub (r + 1) (by rw [Nat.testBit_succ, hq_div]; exact hr)
            rw [Nat.testBit_succ] at this; exact this
          · have := hrun (r + 1) (by rw [Nat.testBit_succ, hq_div]; exact hr)
              (by rw [Nat.testBit_succ, hq_div]; exact hnext)
            rw [Nat.testBit_succ] at this; exact this

/-! ## Section 4: Theorems 3 & 4 — Exact `LDLᵀ` Factorization & Determinant of `negZeroPosCarryMat` -/

private lemma negPosCarries_zero_unfold (i j : ℕ) :
    negPosCarries 0 i j =
      if i % 2 = 1 ∧ j % 2 = 1 then negPosCarries (-1) (i / 2) (j / 2)
      else negPosCarries 0 (i / 2) (j / 2) := by
  unfold negPosCarries
  rw [negAddFull_unfold 0 i j]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    simp [negStep, hi, hj]

private lemma negPosCarries_negOne_unfold (i j : ℕ) :
    negPosCarries (-1) i j =
      if i % 2 = 0 ∧ j % 2 = 0 then 1 + negPosCarries 1 (i / 2) (j / 2)
      else negPosCarries 0 (i / 2) (j / 2) := by
  unfold negPosCarries
  rw [negAddFull_unfold (-1) i j]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    simp [negStep, hi, hj]

private lemma sum_range_split_even_odd {R : Type*} [CommRing R] (f : ℕ → R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k =
      (∑ k ∈ Finset.range m, f (2 * k)) + ∑ k ∈ Finset.range m, f (2 * k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

private lemma runPrefix_sum_trim {R : Type*} [CommRing R] (i j M : ℕ) (hM : max i j < M) :
    ∑ k ∈ Finset.range M,
        ((-1 : R) ^ popcount k * (if runPrefix i k then 1 else 0) * (if runPrefix j k then 1 else 0)) =
      ∑ k ∈ Finset.range (max i j + 1),
        ((-1 : R) ^ popcount k * (if runPrefix i k then 1 else 0) * (if runPrefix j k then 1 else 0)) := by
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
  intro k _ hk
  simp only [Finset.mem_range, not_lt] at hk
  have hfalse : runPrefix i k = false := by
    by_contra h
    have ht : runPrefix i k = true := Bool.eq_true_of_not_eq_false h
    have := runPrefix_le ht
    omega
  simp [hfalse]

private lemma negZeroPosCarry_pointwise_sum {R : Type*} [CommRing R] :
    ∀ M i j : ℕ, max i j < M →
      (if negPosCarries 0 i j = 0 then (1 : R) else 0) =
        ∑ k ∈ Finset.range M,
          ((-1 : R) ^ popcount k * (if runPrefix i k then 1 else 0) * (if runPrefix j k then 1 else 0)) := by
  intro M i j hM
  rw [runPrefix_sum_trim i j M hM]
  suffices hmain : ∀ s i j : ℕ, i + j ≤ s →
      (if negPosCarries 0 i j = 0 then (1 : R) else 0) =
        ∑ k ∈ Finset.range (max i j + 1),
          ((-1 : R) ^ popcount k * (if runPrefix i k then 1 else 0) * (if runPrefix j k then 1 else 0)) by
    exact hmain (i + j) i j le_rfl
  intro s
  induction s with
  | zero =>
    intro i j hij
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi hj
    simp [negPosCarries, negFuel, negAddFullAux_zero_zero_zero, popcount, runPrefix]
  | succ s ih =>
    intro i j hij
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩
      simp [negPosCarries, negFuel, negAddFullAux_zero_zero_zero, popcount, runPrefix]
    · set m := max (i / 2) (j / 2) + 1
      have h2m : max i j < 2 * m := by omega
      rw [← runPrefix_sum_trim i j (2 * m) h2m, sum_range_split_even_odd]
      have heven :
          ∑ k ∈ Finset.range m,
            ((-1 : R) ^ popcount (2 * k) * (if runPrefix i (2 * k) then 1 else 0) *
              (if runPrefix j (2 * k) then 1 else 0)) =
          ∑ k ∈ Finset.range m,
            ((-1 : R) ^ popcount k * (if runPrefix (i / 2) k then 1 else 0) *
              (if runPrefix (j / 2) k then 1 else 0)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [popcount_two_mul, runPrefix_even, runPrefix_even]
      have heven_val :
          ∑ k ∈ Finset.range m,
            ((-1 : R) ^ popcount k * (if runPrefix (i / 2) k then 1 else 0) *
              (if runPrefix (j / 2) k then 1 else 0)) =
          (if negPosCarries 0 (i / 2) (j / 2) = 0 then (1 : R) else 0) :=
        (ih (i / 2) (j / 2) (by omega)).symm
      rw [negPosCarries_zero_unfold]
      by_cases h11 : i % 2 = 1 ∧ j % 2 = 1
      · simp only [h11, and_self, ↓reduceIte]
        rw [negPosCarries_negOne_unfold]
        have hodd_rw :
            ∑ k ∈ Finset.range m,
              ((-1 : R) ^ popcount (2 * k + 1) * (if runPrefix i (2 * k + 1) then 1 else 0) *
                (if runPrefix j (2 * k + 1) then 1 else 0)) =
            - ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k *
                  (if (i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [popcount_two_mul_add_one, pow_add, pow_one, runPrefix_odd, runPrefix_odd]
          simp only [h11.1, h11.2, true_and]
          by_cases h1 : (i / 2) % 2 = k % 2 <;> by_cases h2 : (j / 2) % 2 = k % 2 <;>
            by_cases hri : runPrefix (i / 2) k = true <;>
            by_cases hrj : runPrefix (j / 2) k = true <;>
            simp [h1, h2, hri, hrj]
        rw [heven, hodd_rw]
        rcases Nat.mod_two_eq_zero_or_one (i / 2) with hi1 | hi1 <;>
          rcases Nat.mod_two_eq_zero_or_one (j / 2) with hj1 | hj1
        · -- Subcase (0, 0): odd sum cancels even sum completely => 0!
          have hnz : 1 + negPosCarries 1 (i / 2 / 2) (j / 2 / 2) ≠ 0 := by omega
          have hsub_eq :
              ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k *
                  (if (i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) =
              ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k *
                  (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rcases Nat.mod_two_eq_zero_or_one k with hk | hk
            · simp [hi1, hj1, hk]
            · have hr : runPrefix (i / 2) k = false := by
                rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
                · omega
                · rw [hq, runPrefix_odd]; simp [hi1]
              simp [hi1, hj1, hk, hr]
          rw [hsub_eq]
          simp [hi1, hj1]
        · -- Subcase (0, 1): odd sum is 0!
          have hzero :
              ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k *
                  (if (i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            have : ¬((i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2) := by omega
            simp [this]
          have hstep0 : negPosCarries 0 (i / 2) (j / 2) = negPosCarries 0 (i / 2 / 2) (j / 2 / 2) := by
            rw [negPosCarries_zero_unfold]; simp [hi1, hj1]
          rw [hzero, neg_zero, add_zero, heven_val, hstep0]
          simp [hi1, hj1]
        · -- Subcase (1, 0): symmetric to (0, 1)!
          have hzero :
              ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k *
                  (if (i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            have : ¬((i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2) := by omega
            simp [this]
          have hstep0 : negPosCarries 0 (i / 2) (j / 2) = negPosCarries 0 (i / 2 / 2) (j / 2 / 2) := by
            rw [negPosCarries_zero_unfold]; simp [hi1, hj1]
          rw [hzero, neg_zero, add_zero, heven_val, hstep0]
          simp [hi1, hj1]
        · -- Subcase (1, 1): even sum minus odd-k' part of even sum leaves even-k' part = ih (i/4, j/4)!
          set m2 := max (i / 2 / 2) (j / 2 / 2) + 1
          have hm2 : max (i / 2) (j / 2) < 2 * m2 := by omega
          have htrim1 :
              ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k * (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) =
              ∑ k ∈ Finset.range (2 * m2),
                ((-1 : R) ^ popcount k * (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) := by
            rw [runPrefix_sum_trim (i / 2) (j / 2) (2 * m2) hm2]
          have htrim2 :
              ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k *
                  (if (i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) =
              ∑ k ∈ Finset.range (2 * m2),
                ((-1 : R) ^ popcount k *
                  (if (i / 2) % 2 = k % 2 ∧ (j / 2) % 2 = k % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) k then 1 else 0) *
                  (if runPrefix (j / 2) k then 1 else 0)) := by
            have hle : m ≤ 2 * m2 := by omega
            refine Finset.sum_subset (Finset.range_mono hle) ?_
            intro k _ hk
            simp only [Finset.mem_range, not_lt] at hk
            have hf : runPrefix (i / 2) k = false := by
              by_contra h
              have := runPrefix_le (Bool.eq_true_of_not_eq_false h); omega
            simp [hf]
          rw [htrim1, htrim2, sum_range_split_even_odd, sum_range_split_even_odd]
          have hkill_even :
              ∑ k ∈ Finset.range m2,
                ((-1 : R) ^ popcount (2 * k) *
                  (if (i / 2) % 2 = (2 * k) % 2 ∧ (j / 2) % 2 = (2 * k) % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) (2 * k) then 1 else 0) *
                  (if runPrefix (j / 2) (2 * k) then 1 else 0)) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            simp [hi1, hj1]
          have hkeep_odd :
              ∑ k ∈ Finset.range m2,
                ((-1 : R) ^ popcount (2 * k + 1) *
                  (if (i / 2) % 2 = (2 * k + 1) % 2 ∧ (j / 2) % 2 = (2 * k + 1) % 2 then (1 : R) else 0) *
                  (if runPrefix (i / 2) (2 * k + 1) then 1 else 0) *
                  (if runPrefix (j / 2) (2 * k + 1) then 1 else 0)) =
              ∑ k ∈ Finset.range m2,
                ((-1 : R) ^ popcount (2 * k + 1) *
                  (if runPrefix (i / 2) (2 * k + 1) then 1 else 0) *
                  (if runPrefix (j / 2) (2 * k + 1) then 1 else 0)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmod1 : (2 * k + 1) % 2 = 1 := by omega
            simp [hi1, hj1, hmod1]
          rw [hkill_even, zero_add, hkeep_odd]
          have hsimp_even :
              ∑ k ∈ Finset.range m2,
                ((-1 : R) ^ popcount (2 * k) * (if runPrefix (i / 2) (2 * k) then 1 else 0) *
                  (if runPrefix (j / 2) (2 * k) then 1 else 0)) =
              ∑ k ∈ Finset.range m2,
                ((-1 : R) ^ popcount k * (if runPrefix (i / 2 / 2) k then 1 else 0) *
                  (if runPrefix (j / 2 / 2) k then 1 else 0)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [popcount_two_mul, runPrefix_even, runPrefix_even]
          rw [show ∀ a b : R, a + b + -b = a from fun a b => by ring, hsimp_even]
          have hnot00 : ¬((i / 2) % 2 = 0 ∧ (j / 2) % 2 = 0) := by omega
          simp only [hnot00, ↓reduceIte]
          exact ih (i / 2 / 2) (j / 2 / 2) (by omega)
      · -- Case `(i_0, j_0) ≠ (1, 1)`: odd sum is 0!
        simp only [h11, ↓reduceIte]
        have hodd_zero :
            ∑ k ∈ Finset.range m,
              ((-1 : R) ^ popcount (2 * k + 1) * (if runPrefix i (2 * k + 1) then 1 else 0) *
                (if runPrefix j (2 * k + 1) then 1 else 0)) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [runPrefix_odd, runPrefix_odd]
          by_cases hi1 : i % 2 = 1
          · have hj0 : j % 2 ≠ 1 := fun hj1 => h11 ⟨hi1, hj1⟩
            simp [hj0]
          · simp [hi1]
        rw [heven, hodd_zero, add_zero, heven_val]

/-- **Theorem 3 (Exact Negabinary Zero-Positive-Carry `LDLᵀ` Factorization):**
For every commutative ring `R` and every `n : ℕ`,
`negZeroPosCarryMat R n = runPrefixMat R n * thueMorseDiag R n * (runPrefixMat R n)ᵀ`. -/
theorem negZeroPosCarryMat_eq_LDL {R : Type*} [CommRing R] (n : ℕ) :
    negZeroPosCarryMat R n = runPrefixMat R n * thueMorseDiag R n * (runPrefixMat R n)ᵀ := by
  ext i j
  simp only [negZeroPosCarryMat, Matrix.of_apply, Matrix.mul_apply, thueMorseDiag,
    Matrix.diagonal_apply, Matrix.transpose_apply, runPrefixMat]
  have hsum :
      ∑ x : Fin n, (∑ k : Fin n, (if runPrefix i.1 k.1 then (1 : R) else 0) *
        (if k = x then (-1 : R) ^ popcount k.1 else 0)) * (if runPrefix j.1 x.1 then 1 else 0) =
      ∑ k ∈ Finset.range n,
        ((-1 : R) ^ popcount k * (if runPrefix i.1 k then 1 else 0) * (if runPrefix j.1 k then 1 else 0)) := by
    have h1 : ∀ x : Fin n,
        (∑ k : Fin n, (if runPrefix i.1 k.1 then (1 : R) else 0) *
          (if k = x then (-1 : R) ^ popcount k.1 else 0)) =
        (if runPrefix i.1 x.1 then (1 : R) else 0) * (-1 : R) ^ popcount x.1 := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp
      · intro k _ hkx; simp [hkx]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    simp_rw [h1]
    rw [← Fin.sum_univ_eq_sum_range (fun k =>
      (-1 : R) ^ popcount k * (if runPrefix i.1 k then 1 else 0) * (if runPrefix j.1 k then 1 else 0)) n]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  exact negZeroPosCarry_pointwise_sum n i.1 j.1 (by omega)

lemma det_runPrefixMat {R : Type*} [CommRing R] (n : ℕ) :
    (runPrefixMat R n).det = 1 := by
  have htri : (runPrefixMat R n).IsLowerTriangular := by
    intro i j hij
    have hlt : i.1 < j.1 := hij
    simp only [runPrefixMat, Matrix.of_apply]
    have hf : runPrefix i.1 j.1 = false := by
      by_contra h
      have := runPrefix_le (Bool.eq_true_of_not_eq_false h)
      omega
    simp [hf]
  rw [Matrix.det_of_isLowerTriangular (runPrefixMat R n) htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [runPrefixMat, runPrefix_self]

/-- **Theorem 4 (Exact Negabinary Zero-Positive-Carry Thue-Morse Determinant):**
For every commutative ring `R` and every `n : ℕ`,
`(negZeroPosCarryMat R n).det = ∏ k : Fin n, (-1 : R) ^ popcount k.1`. -/
theorem det_negZeroPosCarryMat {R : Type*} [CommRing R] (n : ℕ) :
    (negZeroPosCarryMat R n).det = ∏ k : Fin n, (-1 : R) ^ popcount k.1 := by
  rw [negZeroPosCarryMat_eq_LDL, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      det_runPrefixMat, thueMorseDiag, Matrix.det_diagonal]
  ring

/-! ## Section 5: Theorems 5 & 6 — Zero-Borrow Matrix Equivalence & Non-Equality Witness -/

private lemma negNegBorrows_zero_unfold (i j : ℕ) :
    negNegBorrows 0 i j =
      if i % 2 = 1 ∧ j % 2 = 1 then 1 + negNegBorrows (-1) (i / 2) (j / 2)
      else negNegBorrows 0 (i / 2) (j / 2) := by
  unfold negNegBorrows
  rw [negAddFull_unfold 0 i j]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    simp [negStep, hi, hj]

lemma negNegBorrows_eq_zero_iff_and_eq_zero (i j : ℕ) :
    negNegBorrows 0 i j = 0 ↔ (i &&& j) = 0 := by
  induction i using Nat.strong_induction_on generalizing j with
  | h i ih =>
    by_cases h0 : i = 0
    · subst h0
      simp only [Nat.zero_and, iff_true]
      induction j using Nat.strong_induction_on with
      | h j ihj =>
        cases j with
        | zero => simp [negNegBorrows, negFuel, negAddFullAux_zero_zero_zero]
        | succ m =>
          rw [negNegBorrows_zero_unfold]
          simp [ihj ((m + 1) / 2) (by omega)]
    · rw [negNegBorrows_zero_unfold]
      have hand : (i &&& j) = 0 ↔ ¬(i % 2 = 1 ∧ j % 2 = 1) ∧ ((i / 2) &&& (j / 2)) = 0 := by
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · rintro ⟨hi1, hj1⟩
            have hb := congrArg (fun x => x.testBit 0) h
            rw [Nat.testBit_and] at hb
            simp [Nat.testBit_zero, hi1, hj1] at hb
          · apply Nat.eq_of_testBit_eq; intro r
            have hb := congrArg (fun x => x.testBit (r + 1)) h
            rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.zero_testBit] at hb
            rw [Nat.testBit_and, Nat.zero_testBit]
            exact hb
        · rintro ⟨hnot, hdiv⟩
          apply Nat.eq_of_testBit_eq; intro r
          cases r with
          | zero =>
            rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero, Nat.zero_testBit]
            rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
              rcases Nat.mod_two_eq_zero_or_one j with hj | hj
            · simp [hi, hj]
            · simp [hi, hj]
            · simp [hi, hj]
            · exact absurd ⟨hi, hj⟩ hnot
          | succ r =>
            have hb := congrArg (fun x => x.testBit r) hdiv
            rw [Nat.testBit_and, Nat.zero_testBit] at hb
            rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.zero_testBit]
            exact hb
      rw [hand, ← ih (i / 2) (by omega) (j / 2)]
      split_ifs with h11
      · simp [h11]
      · simp [h11]

private def submask (i k : ℕ) : Bool :=
  decide ((k &&& i) = k)

private lemma submask_le {i k : ℕ} (h : submask i k = true) : k ≤ i := by
  simp only [submask, decide_eq_true_eq] at h
  have hbits : ∀ r, k.testBit r = true → i.testBit r = true := by
    intro r hr
    have hb := congrArg (fun x => x.testBit r) h
    rw [Nat.testBit_and, hr, Bool.true_and] at hb
    exact hb
  clear h
  suffices ∀ n m : ℕ, (∀ r, n.testBit r = true → m.testBit r = true) → n ≤ m from
    this k i hbits
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m hm
    cases n with
    | zero => omega
    | succ p =>
      have hdiv : (p + 1) / 2 ≤ m / 2 := ih ((p + 1) / 2) (by omega) (m / 2) (fun r hr => by
        have := hm (r + 1) (by rw [Nat.testBit_succ]; exact hr)
        rw [Nat.testBit_succ] at this; exact this)
      rcases Nat.mod_two_eq_zero_or_one (p + 1) with hp | hp
      · omega
      · have hm1 : m % 2 = 1 := by
          have := hm 0 (by simp [Nat.testBit_zero, hp])
          simpa [Nat.testBit_zero] using this
        omega

private lemma submask_self (i : ℕ) : submask i i = true := by
  simp [submask]

private lemma submask_even (i k : ℕ) : submask i (2 * k) = submask (i / 2) k := by
  simp only [submask, decide_eq_decide]
  have hdiv : (2 * k) / 2 = k := by omega
  constructor
  · intro h; apply Nat.eq_of_testBit_eq; intro r
    have hb := congrArg (fun x => x.testBit (r + 1)) h
    rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, hdiv] at hb
    rw [Nat.testBit_and]
    exact hb
  · intro h; apply Nat.eq_of_testBit_eq; intro r
    cases r with
    | zero => rw [Nat.testBit_and, Nat.testBit_zero]; simp
    | succ r =>
      have hb := congrArg (fun x => x.testBit r) h
      rw [Nat.testBit_and] at hb
      rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, hdiv]
      exact hb

private lemma submask_odd (i k : ℕ) :
    submask i (2 * k + 1) = (decide (i % 2 = 1) && submask (i / 2) k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [submask, Bool.and_eq_true, decide_eq_true_eq]
  have hdiv : (2 * k + 1) / 2 = k := by omega
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hb := congrArg (fun x => x.testBit 0) h
      rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero] at hb
      simp [hmod] at hb; exact hb
    · apply Nat.eq_of_testBit_eq; intro r
      have hb := congrArg (fun x => x.testBit (r + 1)) h
      rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, hdiv] at hb
      rw [Nat.testBit_and]; exact hb
  · rintro ⟨hi1, hsub⟩
    apply Nat.eq_of_testBit_eq; intro r
    cases r with
    | zero => rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero]; simp [hmod, hi1]
    | succ r =>
      have hb := congrArg (fun x => x.testBit r) hsub
      rw [Nat.testBit_and] at hb
      rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, hdiv]
      exact hb

private lemma disjointBit_pointwise_sum {R : Type*} [CommRing R] :
    ∀ M i j : ℕ, max i j < M →
      (if (i &&& j) = 0 then (1 : R) else 0) =
        ∑ k ∈ Finset.range M,
          ((-1 : R) ^ popcount k * (if submask i k then 1 else 0) * (if submask j k then 1 else 0)) := by
  intro M i j hM
  have htrim : ∀ M' : ℕ, max i j < M' →
      ∑ k ∈ Finset.range M',
        ((-1 : R) ^ popcount k * (if submask i k then 1 else 0) * (if submask j k then 1 else 0)) =
      ∑ k ∈ Finset.range (max i j + 1),
        ((-1 : R) ^ popcount k * (if submask i k then 1 else 0) * (if submask j k then 1 else 0)) := by
    intro M' hM'
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    have hf : submask i k = false := by
      by_contra h; have := submask_le (Bool.eq_true_of_not_eq_false h); omega
    simp [hf]
  rw [htrim M hM]
  suffices hmain : ∀ s i j : ℕ, i + j ≤ s →
      (if (i &&& j) = 0 then (1 : R) else 0) =
        ∑ k ∈ Finset.range (max i j + 1),
          ((-1 : R) ^ popcount k * (if submask i k then 1 else 0) * (if submask j k then 1 else 0)) by
    exact hmain (i + j) i j le_rfl
  intro s
  induction s with
  | zero =>
    intro i j hij
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi hj; simp [popcount, submask]
  | succ s ih =>
    intro i j hij
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩; simp [popcount, submask]
    · set m := max (i / 2) (j / 2) + 1
      have h2m : max i j < 2 * m := by omega
      have htrim' :
          ∑ k ∈ Finset.range (max i j + 1),
            ((-1 : R) ^ popcount k * (if submask i k then 1 else 0) * (if submask j k then 1 else 0)) =
          ∑ k ∈ Finset.range (2 * m),
            ((-1 : R) ^ popcount k * (if submask i k then 1 else 0) * (if submask j k then 1 else 0)) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
        simp only [Finset.mem_range, not_lt] at hk
        have hf : submask i k = false := by
          by_contra h; have := submask_le (Bool.eq_true_of_not_eq_false h); omega
        simp [hf]
      rw [htrim', sum_range_split_even_odd]
      have heven :
          ∑ k ∈ Finset.range m,
            ((-1 : R) ^ popcount (2 * k) * (if submask i (2 * k) then 1 else 0) *
              (if submask j (2 * k) then 1 else 0)) =
          ∑ k ∈ Finset.range m,
            ((-1 : R) ^ popcount k * (if submask (i / 2) k then 1 else 0) *
              (if submask (j / 2) k then 1 else 0)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [popcount_two_mul, submask_even, submask_even]
      by_cases h11 : i % 2 = 1 ∧ j % 2 = 1
      · have hne : (i &&& j) ≠ 0 := by
          intro h
          have hb := congrArg (fun x => x.testBit 0) h
          rw [Nat.testBit_and] at hb
          simp [Nat.testBit_zero, h11.1, h11.2] at hb
        have hodd :
            ∑ k ∈ Finset.range m,
              ((-1 : R) ^ popcount (2 * k + 1) * (if submask i (2 * k + 1) then 1 else 0) *
                (if submask j (2 * k + 1) then 1 else 0)) =
            - ∑ k ∈ Finset.range m,
                ((-1 : R) ^ popcount k * (if submask (i / 2) k then 1 else 0) *
                  (if submask (j / 2) k then 1 else 0)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [popcount_two_mul_add_one, pow_add, pow_one, submask_odd, submask_odd]
          by_cases hsi : submask (i / 2) k = true <;> by_cases hsj : submask (j / 2) k = true <;>
            simp [h11.1, h11.2, hsi, hsj]
        rw [heven, hodd, add_neg_cancel]
        simp [hne]
      · have hodd :
            ∑ k ∈ Finset.range m,
              ((-1 : R) ^ popcount (2 * k + 1) * (if submask i (2 * k + 1) then 1 else 0) *
                (if submask j (2 * k + 1) then 1 else 0)) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [submask_odd, submask_odd]
          by_cases hi1 : i % 2 = 1
          · have hj0 : j % 2 ≠ 1 := fun hj1 => h11 ⟨hi1, hj1⟩
            simp [hj0]
          · simp [hi1]
        have hiff : (i &&& j) = 0 ↔ ((i / 2) &&& (j / 2)) = 0 := by
          rw [← negNegBorrows_eq_zero_iff_and_eq_zero, ← negNegBorrows_eq_zero_iff_and_eq_zero,
              negNegBorrows_zero_unfold]
          simp [h11]
        rw [heven, hodd, add_zero, ← ih (i / 2) (j / 2) (by omega)]
        simp [hiff]

/-- **Theorem 5 (Exact Negabinary Zero-Borrow Matrix Determinant):**
`negZeroBorrowMat R n = disjointBitMat R n` and both share the exact same Thue-Morse determinant
`∏ k < n, (-1) ^ popcount k` as `negZeroPosCarryMat R n` for every `n : ℕ`. -/
theorem det_negZeroBorrowMat {R : Type*} [CommRing R] (n : ℕ) :
    (negZeroBorrowMat R n).det = ∏ k : Fin n, (-1 : R) ^ popcount k.1 := by
  have heq : negZeroBorrowMat R n = disjointBitMat R n := by
    ext i j
    simp [negZeroBorrowMat, disjointBitMat, negNegBorrows_eq_zero_iff_and_eq_zero]
  rw [heq]
  let LS : Matrix (Fin n) (Fin n) R := Matrix.of fun i k => if submask i.1 k.1 then 1 else 0
  have hfac : disjointBitMat R n = LS * thueMorseDiag R n * LSᵀ := by
    ext i j
    simp only [disjointBitMat, Matrix.of_apply, Matrix.mul_apply, thueMorseDiag,
      Matrix.diagonal_apply, Matrix.transpose_apply, LS]
    have h1 : ∀ x : Fin n,
        (∑ k : Fin n, (if submask i.1 k.1 then (1 : R) else 0) *
          (if k = x then (-1 : R) ^ popcount k.1 else 0)) =
        (if submask i.1 x.1 then (1 : R) else 0) * (-1 : R) ^ popcount x.1 := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp
      · intro k _ hkx; simp [hkx]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    simp_rw [h1]
    have hsum :
        ∑ x : Fin n, (if submask i.1 x.1 then (1 : R) else 0) * (-1 : R) ^ popcount x.1 *
          (if submask j.1 x.1 then 1 else 0) =
        ∑ k ∈ Finset.range n,
          ((-1 : R) ^ popcount k * (if submask i.1 k then 1 else 0) * (if submask j.1 k then 1 else 0)) := by
      rw [← Fin.sum_univ_eq_sum_range _ n]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    exact disjointBit_pointwise_sum n i.1 j.1 (by omega)
  have hLS : LS.det = 1 := by
    have htri : LS.IsLowerTriangular := by
      intro i j hij
      have hlt : i.1 < j.1 := hij
      simp only [LS, Matrix.of_apply]
      have hf : submask i.1 j.1 = false := by
        by_contra h; have := submask_le (Bool.eq_true_of_not_eq_false h); omega
      simp [hf]
    rw [Matrix.det_of_isLowerTriangular LS htri]
    exact Finset.prod_eq_one fun i _ => by simp [LS, submask_self]
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hLS, thueMorseDiag, Matrix.det_diagonal]
  ring

/-- **Theorem 6 (Non-Equality Witness):**
`negZeroPosCarryMat` and `disjointBitMat` are genuinely distinct matrices (already differing at
`(1, 3)` and `(3, 3)`), despite sharing the exact same Thue-Morse `LDLᵀ` diagonal and determinant
for every `n : ℕ`. -/
theorem negZeroPosCarry_ne_disjointBit :
    (negPosCarries 0 1 3 = 0 ∧ (1 &&& 3) ≠ 0) ∧
    (negPosCarries 0 3 3 = 0 ∧ (3 &&& 3) ≠ 0) := by
  decide

/-! ## Section 6: Theorems 7 & 8 — Exact Even/Odd Block-Decoupling of `H_n` and `K_m` -/

private def evenOddEquiv (n : ℕ) : Fin n ≃ Fin ((n + 1) / 2) ⊕ Fin (n / 2) where
  toFun i :=
    if h : i.1 % 2 = 0 then Sum.inl ⟨i.1 / 2, by omega⟩
    else Sum.inr ⟨i.1 / 2, by omega⟩
  invFun
    | Sum.inl u => ⟨2 * u.1, by omega⟩
    | Sum.inr v => ⟨2 * v.1 + 1, by omega⟩
  left_inv i := by
    by_cases h : i.1 % 2 = 0
    · simp only [h, ↓reduceDIte]; ext; dsimp only; omega
    · simp only [h, ↓reduceDIte]; ext; dsimp only; omega
  right_inv x := by
    cases x with
    | inl u =>
      have h : (2 * u.1) % 2 = 0 := by omega
      simp only [h, ↓reduceDIte]
      congr 1; ext; dsimp only; omega
    | inr v =>
      have h : (2 * v.1 + 1) % 2 ≠ 0 := by omega
      simp only [h, ↓reduceDIte]
      congr 1; ext; dsimp only; omega

private lemma negParity_entry_2u_2v {R : Type*} [CommRing R] (u v : ℕ) :
    (-1 : R) ^ negPosCarries 0 (2 * u) (2 * v) = (-1 : R) ^ negPosCarries 0 u v := by
  rw [negPosCarries_zero_unfold]; simp

private lemma negParity_entry_2u1_2v {R : Type*} [CommRing R] (u v : ℕ) :
    (-1 : R) ^ negPosCarries 0 (2 * u + 1) (2 * v) = (-1 : R) ^ negPosCarries 0 u v := by
  rw [negPosCarries_zero_unfold]
  have h1 : (2 * u + 1) / 2 = u := by omega
  simp [h1]

private lemma negParity_entry_2u_2v1 {R : Type*} [CommRing R] (u v : ℕ) :
    (-1 : R) ^ negPosCarries 0 (2 * u) (2 * v + 1) = (-1 : R) ^ negPosCarries 0 u v := by
  rw [negPosCarries_zero_unfold]
  have h1 : (2 * v + 1) / 2 = v := by omega
  simp [h1]

private lemma negParity_entry_2u1_2v1 {R : Type*} [CommRing R] (u v : ℕ) :
    (-1 : R) ^ negPosCarries 0 (2 * u + 1) (2 * v + 1) = (-1 : R) ^ negPosCarries (-1) u v := by
  rw [negPosCarries_zero_unfold]
  have h1 : (2 * u + 1) % 2 = 1 := by omega
  have h2 : (2 * v + 1) % 2 = 1 := by omega
  have h3 : (2 * u + 1) / 2 = u := by omega
  have h4 : (2 * v + 1) / 2 = v := by omega
  simp [h1, h2, h3, h4]

/-- **Theorem 7 (Exact Even/Odd Block-Decoupling of `negParityMat`):**
For every commutative ring `R` and every `n : ℕ`,
`det (negParityMat R 0 n) = det (negParityMat R 0 ((n + 1) / 2)) * det (negKMat R (n / 2))`. -/
theorem det_negParityMat_decouple {R : Type*} [CommRing R] (n : ℕ) :
    (negParityMat R 0 n).det =
      (negParityMat R 0 ((n + 1) / 2)).det * (negKMat R (n / 2)).det := by
  let L : Matrix (Fin n) (Fin n) R := Matrix.of fun i j =>
    if i = j then 1
    else if i.1 % 2 = 1 ∧ j.1 + 1 = i.1 then -1
    else 0
  have hL_det : L.det = 1 := by
    have htri : L.IsLowerTriangular := by
      intro i j hij
      have hlt : i.1 < j.1 := hij
      have hne : i ≠ j := fun h => by subst h; omega
      simp only [L, Matrix.of_apply, hne, ↓reduceIte]
      split_ifs with h
      · omega
      · rfl
    rw [Matrix.det_of_isLowerTriangular L htri]
    exact Finset.prod_eq_one fun i _ => by simp [L]
  have hL_mul : ∀ (A : Matrix (Fin n) (Fin n) R) (i j : Fin n),
      (L * A) i j =
        if h : i.1 % 2 = 0 then A i j
        else A i j - A ⟨i.1 - 1, by omega⟩ j := by
    intro A i j
    simp only [Matrix.mul_apply, L, Matrix.of_apply]
    by_cases h : i.1 % 2 = 0
    · simp only [h, ↓reduceDIte]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        have : ¬(i.1 % 2 = 1 ∧ k.1 + 1 = i.1) := by omega
        simp [hki.symm, h]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · simp only [h, ↓reduceDIte]
      let i' : Fin n := ⟨i.1 - 1, by omega⟩
      have hne : i' ≠ i := by intro heq; have := congrArg Fin.val heq; dsimp [i'] at this; omega
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i'⟩)]
      have hrest : ∑ k ∈ (Finset.univ.erase i).erase i',
          (if i = k then (1 : R) else if i.1 % 2 = 1 ∧ k.1 + 1 = i.1 then -1 else 0) * A k j = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        simp only [Finset.mem_erase] at hk
        have h1 : i ≠ k := hk.2.1.symm
        have h2 : k.1 + 1 ≠ i.1 := by
          intro heq
          apply hk.1; ext; dsimp [i']; omega
        simp [h1, h2]
      have hi'_cond : i.1 % 2 = 1 ∧ i'.1 + 1 = i.1 := by dsimp [i']; omega
      rw [hrest, add_zero]
      simp [hne.symm, hi'_cond]
      ring
  have hR_mul : ∀ (B : Matrix (Fin n) (Fin n) R) (i j : Fin n),
      (B * Lᵀ) i j =
        if h : j.1 % 2 = 0 then B i j
        else B i j - B i ⟨j.1 - 1, by omega⟩ := by
    intro B i j
    have hT := hL_mul Bᵀ j i
    have heq : (B * Lᵀ) i j = (L * Bᵀ) j i := by
      rw [← Matrix.transpose_apply (L * Bᵀ), Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [heq, hT]
    split_ifs <;> rfl
  let M := L * negParityMat R 0 n * Lᵀ
  have hdetM : (negParityMat R 0 n).det = M.det := by
    dsimp [M]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hL_det]
    ring
  rw [hdetM, ← Matrix.det_reindex_self (evenOddEquiv n) M]
  have hblocks :
      Matrix.reindex (evenOddEquiv n) (evenOddEquiv n) M =
        Matrix.fromBlocks (negParityMat R 0 ((n + 1) / 2)) 0 0 (negKMat R (n / 2)) := by
    ext s t
    cases s with
    | inl u =>
      cases t with
      | inl v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          M, hR_mul, hL_mul, Matrix.fromBlocks_apply₁₁, negParityMat, Matrix.of_apply]
        have hu : (2 * u.1) % 2 = 0 := by omega
        have hv : (2 * v.1) % 2 = 0 := by omega
        simp only [hu, hv, ↓reduceDIte]
        exact negParity_entry_2u_2v u.1 v.1
      | inr v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          M, hR_mul, hL_mul, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, negParityMat, Matrix.of_apply]
        have hu : (2 * u.1) % 2 = 0 := by omega
        have hv : (2 * v.1 + 1) % 2 ≠ 0 := by omega
        simp only [hu, hv, ↓reduceDIte, show 2 * v.1 + 1 - 1 = 2 * v.1 by omega]
        rw [negParity_entry_2u_2v1, negParity_entry_2u_2v, sub_self]
    | inr u =>
      cases t with
      | inl v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          M, hR_mul, hL_mul, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, negParityMat, Matrix.of_apply]
        have hu : (2 * u.1 + 1) % 2 ≠ 0 := by omega
        have hv : (2 * v.1) % 2 = 0 := by omega
        simp only [hu, hv, ↓reduceDIte, show 2 * u.1 + 1 - 1 = 2 * u.1 by omega]
        rw [negParity_entry_2u1_2v, negParity_entry_2u_2v, sub_self]
      | inr v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          M, hR_mul, hL_mul, Matrix.fromBlocks_apply₂₂, negKMat, Matrix.sub_apply, negParityMat, Matrix.of_apply]
        have hu : (2 * u.1 + 1) % 2 ≠ 0 := by omega
        have hv : (2 * v.1 + 1) % 2 ≠ 0 := by omega
        simp only [hu, hv, ↓reduceDIte, show 2 * u.1 + 1 - 1 = 2 * u.1 by omega,
          show 2 * v.1 + 1 - 1 = 2 * v.1 by omega]
        rw [negParity_entry_2u1_2v1, negParity_entry_2u1_2v, negParity_entry_2u_2v1, negParity_entry_2u_2v]
        ring
  rw [hblocks, Matrix.det_fromBlocks_zero₂₁]

/-- **Theorem 8 (Exact Second-Stage Block-Decoupling of `negKMat`):**
For every commutative ring `R` and every `m : ℕ`,
`det (negKMat R m) = (-1) ^ m * det (negJMat R ((m + 1) / 2)) * det (negKMat R (m / 2))`. -/
theorem det_negKMat_decouple {R : Type*} [CommRing R] (m : ℕ) :
    (negKMat R m).det =
      (-1 : R) ^ m * (negJMat R ((m + 1) / 2)).det * (negKMat R (m / 2)).det := by
  rw [← Matrix.det_reindex_self (evenOddEquiv m) (negKMat R m)]
  have hblocks :
      Matrix.reindex (evenOddEquiv m) (evenOddEquiv m) (negKMat R m) =
        Matrix.fromBlocks (-negJMat R ((m + 1) / 2)) 0 0 (-negKMat R (m / 2)) := by
    ext s t
    cases s with
    | inl u =>
      cases t with
      | inl v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          Matrix.fromBlocks_apply₁₁, Matrix.neg_apply, negKMat, negJMat, Matrix.sub_apply,
          Matrix.add_apply, negParityMat, Matrix.of_apply]
        rw [negParity_entry_2u_2v, negPosCarries_negOne_unfold]
        have hu0 : (2 * u.1) % 2 = 0 := by omega
        have hv0 : (2 * v.1) % 2 = 0 := by omega
        have hud : (2 * u.1) / 2 = u.1 := by omega
        have hvd : (2 * v.1) / 2 = v.1 := by omega
        simp only [hu0, hv0, hud, hvd, and_self, ↓reduceIte, pow_add, pow_one]
        ring
      | inr v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, negKMat, Matrix.sub_apply, negParityMat, Matrix.of_apply]
        rw [negParity_entry_2u_2v1, negPosCarries_negOne_unfold]
        have hu0 : (2 * u.1) % 2 = 0 := by omega
        have hv1 : (2 * v.1 + 1) % 2 = 1 := by omega
        have hud : (2 * u.1) / 2 = u.1 := by omega
        have hvd : (2 * v.1 + 1) / 2 = v.1 := by omega
        have hnot : ¬((2 * u.1) % 2 = 0 ∧ (2 * v.1 + 1) % 2 = 0) := by omega
        simp only [hnot, ↓reduceIte, hud, hvd, sub_self]
    | inr u =>
      cases t with
      | inl v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, negKMat, Matrix.sub_apply, negParityMat, Matrix.of_apply]
        rw [negParity_entry_2u1_2v, negPosCarries_negOne_unfold]
        have hud : (2 * u.1 + 1) / 2 = u.1 := by omega
        have hvd : (2 * v.1) / 2 = v.1 := by omega
        have hnot : ¬((2 * u.1 + 1) % 2 = 0 ∧ (2 * v.1) % 2 = 0) := by omega
        simp only [hnot, ↓reduceIte, hud, hvd, sub_self]
      | inr v =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, evenOddEquiv, Equiv.coe_fn_symm_mk,
          Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, negKMat, Matrix.sub_apply, negParityMat, Matrix.of_apply]
        rw [negParity_entry_2u1_2v1, negPosCarries_negOne_unfold]
        have hud : (2 * u.1 + 1) / 2 = u.1 := by omega
        have hvd : (2 * v.1 + 1) / 2 = v.1 := by omega
        have hnot : ¬((2 * u.1 + 1) % 2 = 0 ∧ (2 * v.1 + 1) % 2 = 0) := by omega
        simp only [hnot, ↓reduceIte, hud, hvd]
        ring
  rw [hblocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, Matrix.det_neg,
      Fintype.card_fin, Fintype.card_fin]
  have hsum : (m + 1) / 2 + m / 2 = m := by omega
  calc (-1 : R) ^ ((m + 1) / 2) * (negJMat R ((m + 1) / 2)).det *
        ((-1 : R) ^ (m / 2) * (negKMat R (m / 2)).det)
      = ((-1 : R) ^ ((m + 1) / 2) * (-1 : R) ^ (m / 2)) *
          (negJMat R ((m + 1) / 2)).det * (negKMat R (m / 2)).det := by ring
    _ = (-1 : R) ^ ((m + 1) / 2 + m / 2) *
          (negJMat R ((m + 1) / 2)).det * (negKMat R (m / 2)).det := by rw [← pow_add]
    _ = (-1 : R) ^ m * (negJMat R ((m + 1) / 2)).det * (negKMat R (m / 2)).det := by rw [hsum]

/-! ## Section 7: Theorem 9 — Exact `n = 33` Power-of-2 & `n = 34` Spontaneous Factor-of-3 Anomaly -/

private lemma det_negJMat_1 : (negJMat ℤ 1).det = 2 := by
  rw [Matrix.det_fin_one]; decide

private lemma det_negJMat_2 : (negJMat ℤ 2).det = -4 := by
  rw [Matrix.det_fin_two]; decide

private def E4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; -1, 1, 1, 0; -1, 1, 0, 1]

private def U4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 0, 2, 2; 0, -2, 2, 2; 0, 0, -2, 0; 0, 0, 0, 2]

private lemma det_negJMat_4 : (negJMat ℤ 4).det = 16 := by
  have hmul : E4 * negJMat ℤ 4 = U4 := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hE : E4.det = 1 := by
    have htri : E4.IsLowerTriangular := by
      intro i j hij; have hlt : i.1 < j.1 := hij; clear hij
      fin_cases i <;> fin_cases j <;> simp_all [E4]
    rw [Matrix.det_of_isLowerTriangular E4 htri]; decide
  have hU : U4.det = 16 := by
    have htri : U4.IsUpperTriangular := by
      intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [U4]
    rw [Matrix.det_of_isUpperTriangular htri]; decide
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, hE, one_mul, hU] at h
  exact h

private def E8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 1, 0, 0,  0,  0, 0, 0, 0;
      0, 1, 0,  0,  0, 0, 0, 0;
     -1, 1, 1,  0,  0, 0, 0, 0;
     -1, 1, 0,  1,  0, 0, 0, 0;
     -1, 1, 1, -1,  1, 0, 0, 0;
     -1, 1, 1, -1,  0, 1, 0, 0;
     -1, 1, 1, -1, -1, 1, 1, 0;
     -1, 1, 1, -1, -1, 1, 0, 1]

private def U8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2,  0,  2, 2,  2, 2,  2,  2;
     0, -2,  2, 2,  2, 2,  2,  2;
     0,  0, -2, 0,  2, 2,  2,  2;
     0,  0,  0, 2,  2, 2,  2,  2;
     0,  0,  0, 0, -2, 0, -2, -2;
     0,  0,  0, 0,  0, 2, -2, -2;
     0,  0,  0, 0,  0, 0,  2,  0;
     0,  0,  0, 0,  0, 0,  0, -2]

private lemma det_negJMat_8 : (negJMat ℤ 8).det = 256 := by
  have hmul : E8 * negJMat ℤ 8 = U8 := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hE : E8.det = 1 := by
    have htri : E8.IsLowerTriangular := by
      intro i j hij; have hlt : i.1 < j.1 := hij; clear hij
      fin_cases i <;> fin_cases j <;> simp_all [E8]
    rw [Matrix.det_of_isLowerTriangular E8 htri]; decide
  have hU : U8.det = 256 := by
    have htri : U8.IsUpperTriangular := by
      intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [U8]
    rw [Matrix.det_of_isUpperTriangular htri]; decide
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, hE, one_mul, hU] at h
  exact h

private def E9 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![ 1, 0, 0,  0,  0, 0, 0,  0, 0;
      0, 1, 0,  0,  0, 0, 0,  0, 0;
     -1, 1, 1,  0,  0, 0, 0,  0, 0;
     -1, 1, 0,  1,  0, 0, 0,  0, 0;
     -1, 1, 1, -1,  1, 0, 0,  0, 0;
     -1, 1, 1, -1,  0, 1, 0,  0, 0;
     -1, 1, 1, -1, -1, 1, 1,  0, 0;
     -1, 1, 1, -1, -1, 1, 0,  1, 0;
     -2, 1, 1, -1,  0, 1, 1, -1, 1]

private def U9 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![2,  0,  2, 2,  2, 2,  2,  2,  2;
     0, -2,  2, 2,  2, 2,  2,  2,  0;
     0,  0, -2, 0,  2, 2,  2,  2,  0;
     0,  0,  0, 2,  2, 2,  2,  2,  0;
     0,  0,  0, 0, -2, 0, -2, -2,  0;
     0,  0,  0, 0,  0, 2, -2, -2, -2;
     0,  0,  0, 0,  0, 0,  2,  0, -2;
     0,  0,  0, 0,  0, 0,  0, -2, -2;
     0,  0,  0, 0,  0, 0,  0,  0, -6]

private lemma det_negJMat_9 : (negJMat ℤ 9).det = -1536 := by
  have hmul : E9 * negJMat ℤ 9 = U9 := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hE : E9.det = 1 := by
    have htri : E9.IsLowerTriangular := by
      intro i j hij; have hlt : i.1 < j.1 := hij; clear hij
      fin_cases i <;> fin_cases j <;> simp_all [E9]
    rw [Matrix.det_of_isLowerTriangular E9 htri]; decide
  have hU : U9.det = -1536 := by
    have htri : U9.IsUpperTriangular := by
      intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [U9]
    rw [Matrix.det_of_isUpperTriangular htri]; decide
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, hE, one_mul, hU] at h
  exact h

private lemma det_negKMat_0 : (negKMat ℤ 0).det = 1 := by simp
private lemma det_negKMat_1 : (negKMat ℤ 1).det = -2 := by
  have h := det_negKMat_decouple (R := ℤ) 1
  change (negKMat ℤ 1).det = (-1 : ℤ) ^ 1 * (negJMat ℤ 1).det * (negKMat ℤ 0).det at h
  rw [h, det_negJMat_1, det_negKMat_0]; norm_num
private lemma det_negKMat_2 : (negKMat ℤ 2).det = -4 := by
  have h := det_negKMat_decouple (R := ℤ) 2
  change (negKMat ℤ 2).det = (-1 : ℤ) ^ 2 * (negJMat ℤ 1).det * (negKMat ℤ 1).det at h
  rw [h, det_negJMat_1, det_negKMat_1]; norm_num
private lemma det_negKMat_4 : (negKMat ℤ 4).det = 16 := by
  have h := det_negKMat_decouple (R := ℤ) 4
  change (negKMat ℤ 4).det = (-1 : ℤ) ^ 4 * (negJMat ℤ 2).det * (negKMat ℤ 2).det at h
  rw [h, det_negJMat_2, det_negKMat_2]; norm_num
private lemma det_negKMat_8 : (negKMat ℤ 8).det = 256 := by
  have h := det_negKMat_decouple (R := ℤ) 8
  change (negKMat ℤ 8).det = (-1 : ℤ) ^ 8 * (negJMat ℤ 4).det * (negKMat ℤ 4).det at h
  rw [h, det_negJMat_4, det_negKMat_4]; norm_num
private lemma det_negKMat_16 : (negKMat ℤ 16).det = 65536 := by
  have h := det_negKMat_decouple (R := ℤ) 16
  change (negKMat ℤ 16).det = (-1 : ℤ) ^ 16 * (negJMat ℤ 8).det * (negKMat ℤ 8).det at h
  rw [h, det_negJMat_8, det_negKMat_8]; norm_num
private lemma det_negKMat_17 : (negKMat ℤ 17).det = 393216 := by
  have h := det_negKMat_decouple (R := ℤ) 17
  change (negKMat ℤ 17).det = (-1 : ℤ) ^ 17 * (negJMat ℤ 9).det * (negKMat ℤ 8).det at h
  rw [h, det_negJMat_9, det_negKMat_8]; norm_num

private lemma det_negParityMat_1 : (negParityMat ℤ 0 1).det = 1 := by
  rw [Matrix.det_fin_one]; decide
private lemma det_negParityMat_2 : (negParityMat ℤ 0 2).det = -2 := by
  have h := det_negParityMat_decouple (R := ℤ) 2
  change (negParityMat ℤ 0 2).det = (negParityMat ℤ 0 1).det * (negKMat ℤ 1).det at h
  rw [h, det_negParityMat_1, det_negKMat_1]; norm_num
private lemma det_negParityMat_3 : (negParityMat ℤ 0 3).det = 4 := by
  have h := det_negParityMat_decouple (R := ℤ) 3
  change (negParityMat ℤ 0 3).det = (negParityMat ℤ 0 2).det * (negKMat ℤ 1).det at h
  rw [h, det_negParityMat_2, det_negKMat_1]; norm_num
private lemma det_negParityMat_5 : (negParityMat ℤ 0 5).det = -16 := by
  have h := det_negParityMat_decouple (R := ℤ) 5
  change (negParityMat ℤ 0 5).det = (negParityMat ℤ 0 3).det * (negKMat ℤ 2).det at h
  rw [h, det_negParityMat_3, det_negKMat_2]; norm_num
private lemma det_negParityMat_9 : (negParityMat ℤ 0 9).det = -256 := by
  have h := det_negParityMat_decouple (R := ℤ) 9
  change (negParityMat ℤ 0 9).det = (negParityMat ℤ 0 5).det * (negKMat ℤ 4).det at h
  rw [h, det_negParityMat_5, det_negKMat_4]; norm_num
private lemma det_negParityMat_17 : (negParityMat ℤ 0 17).det = -65536 := by
  have h := det_negParityMat_decouple (R := ℤ) 17
  change (negParityMat ℤ 0 17).det = (negParityMat ℤ 0 9).det * (negKMat ℤ 8).det at h
  rw [h, det_negParityMat_9, det_negKMat_8]; norm_num

private def tmProd : ℕ → ℤ
  | 0 => 1
  | n + 1 => tmProd n * (-1 : ℤ) ^ popcount n

private lemma tmProd_eq (n : ℕ) :
    tmProd n = ∏ k : Fin n, (-1 : ℤ) ^ popcount k.1 := by
  induction n with
  | zero => simp [tmProd]
  | succ n ih =>
    rw [tmProd, ih, Fin.prod_univ_castSucc]
    rfl

/-- **Theorem 9 (The `n = 34` Spontaneous Prime-Factor-`3` Anomaly):**
While `det (negParityMat ℤ 0 n) = 2 ^ (n - 1) * ∏ k < n, (-1) ^ popcount k` holds at `n = 33`
(and in fact for all `1 ≤ n ≤ 33`), at `n = 34` an exact prime factor of `3` spontaneously
appears via `det (negJMat ℤ 9) = -1536 = -3 * 2 ^ 9`. -/
theorem negParityMat_n34_anomaly :
    (negParityMat ℤ 0 33).det = (2 : ℤ) ^ 32 * ∏ k : Fin 33, (-1 : ℤ) ^ popcount k.1 ∧
    (negParityMat ℤ 0 34).det = 3 * (2 : ℤ) ^ 33 * ∏ k : Fin 34, (-1 : ℤ) ^ popcount k.1 := by
  have h33 : (negParityMat ℤ 0 33).det = -4294967296 := by
    have h := det_negParityMat_decouple (R := ℤ) 33
    change (negParityMat ℤ 0 33).det = (negParityMat ℤ 0 17).det * (negKMat ℤ 16).det at h
    rw [h, det_negParityMat_17, det_negKMat_16]; norm_num
  have h34 : (negParityMat ℤ 0 34).det = -25769803776 := by
    have h := det_negParityMat_decouple (R := ℤ) 34
    change (negParityMat ℤ 0 34).det = (negParityMat ℤ 0 17).det * (negKMat ℤ 17).det at h
    rw [h, det_negParityMat_17, det_negKMat_17]; norm_num
  have hp33 : (∏ k : Fin 33, (-1 : ℤ) ^ popcount k.1) = -1 := by
    rw [← tmProd_eq]; simp [tmProd, popcount]
  have hp34 : (∏ k : Fin 34, (-1 : ℤ) ^ popcount k.1) = -1 := by
    rw [← tmProd_eq]; simp [tmProd, popcount]
  rw [h33, h34, hp33, hp34]
  norm_num

end NegabinaryCarryDet
