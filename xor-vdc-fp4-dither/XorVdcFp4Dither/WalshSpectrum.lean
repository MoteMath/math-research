/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XorVdcFp4Dither.XorVdcCore

/-!
# Exact Walsh–Hadamard Spectral Diagonalization, Trace Conservation, and E2M1 Ratios (Theorem 2)

Proves for all `b ≥ 1` (`B = 2^b`):
1. Exact Walsh–Hadamard diagonalization of `xorCovMatrix b` and `xorVdcCovMatrix b`:
   `(M h_k)_i = λ_k h_k(i)` for every `k, i < 2^b`.
2. Every `popcount ≥ 2` Walsh mode has exact eigenvalue `1/12 < 1/6` (50% lower MSE than ind SR).
3. Exact mode counts strictly beating independent SR: `14/16` at `B = 16`, `29/32` at `B = 32`.
4. Exact universal Trace Conservation: `∑_{k < 2^b} λ_k = B * (1/6)` (zero penalty on isotropic blocks).
5. Exact OCP E2M1 uncorrelated positive block MSE ratios: `61/96` (`B = 16`) and `359/576` (`B = 32`).
-/

namespace XorVdcFp4Dither

/-! ### 1. Walsh Character Orthogonality and Bit-Reversal Symmetry -/

theorem popcountBits_zero (b : Nat) : popcountBits b 0 = 0 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [popcountBits, ih]

theorem popcountBits_and_zero_left (b i : Nat) : popcountBits b (0 &&& i) = 0 := by
  simp [popcountBits_zero]

theorem walshSign_zero_left (b i : Nat) : walshSign b 0 i = 1 := by
  unfold walshSign
  rw [popcountBits_and_zero_left]
  decide

theorem walshSign_succ (b k i : Nat) :
    walshSign (b + 1) k i =
      (if (k % 2) * (i % 2) = 0 then (1 : Rat) else -1) * walshSign b (k / 2) (i / 2) := by
  unfold walshSign
  simp only [popcountBits]
  have hmod : (k &&& i) % 2 = (k % 2) * (i % 2) := by
    have htb : (k &&& i).testBit 0 = (k.testBit 0 && i.testBit 0) := Nat.testBit_and k i 0
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
        Nat.testBit_eq_decide_div_mod_eq] at htb
    simp only [Nat.pow_zero, Nat.div_one] at htb
    have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hki : (k &&& i) % 2 = 0 ∨ (k &&& i) % 2 = 1 := by omega
    rcases hk with hk0 | hk1 <;> rcases hi with hi0 | hi1 <;> rcases hki with hki0 | hki1 <;>
      simp_all
  have hdiv : (k &&& i) / 2 = (k / 2) &&& (i / 2) := by
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_and, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_div_two,
        Nat.testBit_and]
  simp only [hmod, hdiv]
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hp : popcountBits b (k / 2 &&& i / 2) % 2 = 0 ∨
      popcountBits b (k / 2 &&& i / 2) % 2 = 1 := by omega
  rcases hk with hk0 | hk1 <;> rcases hi with hi0 | hi1 <;> rcases hp with hp0 | hp1 <;>
    simp_all <;> grind

theorem sumRange_two_mul (n : Nat) (f : Nat → Rat) :
    sumRange (2 * n) f = sumRange n (fun j => f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    have h1 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h1]
    simp only [sumRange]
    rw [ih]
    grind

/-- Exact orthogonality of Walsh characters: `∑_{j < 2^b} h_k(j) = 2^b` if `k = 0`, else `0`. -/
theorem sumRange_walshSign (b k : Nat) (hk : k < 2 ^ b) :
    sumRange (2 ^ b) (fun j => walshSign b k j) =
      if k = 0 then ((2 ^ b : Nat) : Rat) else 0 := by
  induction b generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simp [sumRange, walshSign, popcountBits]; grind
  | succ b ih =>
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, sumRange_two_mul]
    have hkdiv : k / 2 < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hpair :
        sumRange (2 ^ b) (fun j => walshSign (b + 1) k (2 * j) + walshSign (b + 1) k (2 * j + 1)) =
        (if k % 2 = 0 then (2 : Rat) else 0) * sumRange (2 ^ b) (fun j => walshSign b (k / 2) j) := by
      rw [← sumRange_mul_left]
      apply sumRange_congr
      intro j _
      rw [walshSign_succ, walshSign_succ]
      have h2j_mod : (2 * j) % 2 = 0 := by omega
      have h2j_div : (2 * j) / 2 = j := by omega
      have h2j1_mod : (2 * j + 1) % 2 = 1 := by omega
      have h2j1_div : (2 * j + 1) / 2 = j := by omega
      rw [h2j_mod, h2j_div, h2j1_mod, h2j1_div]
      have hkmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hkmod with h0 | h1
      · simp [h0]; grind
      · simp [h1]; grind
    rw [hpair, ih (k / 2) hkdiv]
    have hkmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.zero_mod, Nat.zero_div, ↓reduceIte]
      rw [rat_natCast_mul]
      have h2 : ((2 : Nat) : Rat) = 2 := rfl
      rw [h2]
    · simp only [hk0, ↓reduceIte]
      rcases hkmod with h0 | h1
      · have hdivne : k / 2 ≠ 0 := by omega
        simp [h0, hdivne]
      · simp [h1]

theorem bitSign_eq_walshSign_pow2 {b s j : Nat} (hs : s < b) :
    bitSign s j = walshSign b (2 ^ s) j := by
  induction b generalizing s j with
  | zero => omega
  | succ b ih =>
    rw [walshSign_succ]
    cases s with
    | zero =>
      unfold bitSign bitAt
      simp only [Nat.pow_zero, Nat.div_one, Nat.one_mod, Nat.one_mul]
      have hdiv0 : 1 / 2 = 0 := rfl
      rw [hdiv0, walshSign_zero_left]
      have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases hj with h0 | h1 <;> simp_all <;> grind
    | succ s =>
      have hs' : s < b := by omega
      have hpow_mod : 2 ^ (s + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      have hpow_div : 2 ^ (s + 1) / 2 = 2 ^ s := by rw [Nat.pow_succ]; omega
      rw [hpow_mod, hpow_div]
      simp only [Nat.zero_mul, ↓reduceIte]
      have hbit : bitSign (s + 1) j = bitSign s (j / 2) := by
        unfold bitSign bitAt
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ s) 2, ← Nat.div_div_eq_div_mul]
      rw [hbit, ih hs', Rat.one_mul]

theorem walshSign_mul_walshSign (b k1 k2 j : Nat) :
    walshSign b k1 j * walshSign b k2 j = walshSign b (k1 ^^^ k2) j := by
  induction b generalizing k1 k2 j with
  | zero => simp [walshSign, popcountBits]
  | succ b ih =>
    rw [walshSign_succ, walshSign_succ, walshSign_succ]
    have hdiv : (k1 ^^^ k2) / 2 = (k1 / 2) ^^^ (k2 / 2) := by
      apply Nat.eq_of_testBit_eq
      intro s
      rw [Nat.testBit_xor, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_div_two,
          Nat.testBit_xor]
    have hmod : (k1 ^^^ k2) % 2 = (k1 % 2 + k2 % 2) % 2 := by
      have h := bitAt_xor 0 k1 k2
      unfold bitAt at h
      simpa using h
    rw [hdiv, hmod, ← ih (k1 / 2) (k2 / 2) (j / 2)]
    have hk1 : k1 % 2 = 0 ∨ k1 % 2 = 1 := by omega
    have hk2 : k2 % 2 = 0 ∨ k2 % 2 = 1 := by omega
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hk1 with a | a <;> rcases hk2 with c | c <;> rcases hj with d | d <;>
      simp [a, c, d] <;> grind

theorem sumRange_bitSign_walshSign (b s k : Nat) (hs : s < b) (hk : k < 2 ^ b) :
    sumRange (2 ^ b) (fun j => bitSign s j * walshSign b k j) =
      if k = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0 := by
  have hcongr :
      sumRange (2 ^ b) (fun j => bitSign s j * walshSign b k j) =
      sumRange (2 ^ b) (fun j => walshSign b (2 ^ s ^^^ k) j) := by
    apply sumRange_congr
    intro j _
    rw [bitSign_eq_walshSign_pow2 hs, walshSign_mul_walshSign]
  rw [hcongr]
  have h2s_lt : 2 ^ s < 2 ^ b := Nat.pow_lt_pow_right (by omega) hs
  rw [sumRange_walshSign b (2 ^ s ^^^ k) (Nat.xor_lt_two_pow h2s_lt hk)]
  have hiff : (2 ^ s ^^^ k = 0) ↔ (k = 2 ^ s) := by
    constructor
    · intro h0
      have h1 := congrArg (fun x => 2 ^ s ^^^ x) h0
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at h1
      exact h1
    · intro heq
      rw [heq, Nat.xor_self]
  by_cases h : k = 2 ^ s
  · have h0 : 2 ^ s ^^^ k = 0 := hiff.mpr h
    simp [h]
  · have hne : 2 ^ s ^^^ k ≠ 0 := fun h0 => h (hiff.mp h0)
    simp [h, hne]

/-! ### 2. Popcount-1 Characterization (`popcountBits b k = 1 ↔ ∃ s < b, k = 2^s`) -/

theorem popcountBits_pow2 {b s : Nat} (hs : s < b) :
    popcountBits b (2 ^ s) = 1 := by
  induction b generalizing s with
  | zero => omega
  | succ b ih =>
    simp only [popcountBits]
    cases s with
    | zero =>
      simp only [Nat.pow_zero]
      have h0 : 1 / 2 = 0 := rfl
      rw [h0, popcountBits_zero]
    | succ s =>
      have hs' : s < b := by omega
      have hmod : 2 ^ (s + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      have hdiv : 2 ^ (s + 1) / 2 = 2 ^ s := by rw [Nat.pow_succ]; omega
      rw [hmod, hdiv, ih hs']

theorem popcountBits_eq_zero_iff {b k : Nat} (hk : k < 2 ^ b) :
    popcountBits b k = 0 ↔ k = 0 := by
  induction b generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simp [popcountBits]
  | succ b ih =>
    simp only [popcountBits]
    have hkdiv : k / 2 < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
      omega
    constructor
    · intro h
      have hm : k % 2 = 0 := by omega
      have hd : popcountBits b (k / 2) = 0 := by omega
      have hk2 : k / 2 = 0 := (ih hkdiv).mp hd
      omega
    · intro h
      subst h
      simp [popcountBits_zero]

theorem popcountBits_eq_one_iff {b k : Nat} (hk : k < 2 ^ b) :
    popcountBits b k = 1 ↔ ∃ s, s < b ∧ k = 2 ^ s := by
  induction b generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simp [popcountBits]
  | succ b ih =>
    simp only [popcountBits]
    have hkdiv : k / 2 < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
      omega
    constructor
    · intro h
      have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hmod with h0 | h1
      · have hp1 : popcountBits b (k / 2) = 1 := by omega
        obtain ⟨s, hs, hks⟩ := (ih hkdiv).mp hp1
        refine ⟨s + 1, by omega, ?_⟩
        rw [Nat.pow_succ]
        omega
      · have hp0 : popcountBits b (k / 2) = 0 := by omega
        have hk2 : k / 2 = 0 := (popcountBits_eq_zero_iff hkdiv).mp hp0
        refine ⟨0, by omega, ?_⟩
        simp only [Nat.pow_zero]
        omega
    · intro ⟨s, hs, hks⟩
      subst hks
      exact popcountBits_pow2 hs

/-! ### 3. Exact Walsh–Hadamard Diagonalization of `xorCovMatrix` -/

theorem sumRange_delta_mul (B i : Nat) (hi : i < B) (f : Nat → Rat) :
    sumRange B (fun j => (if i = j then (1 : Rat) / 12 else 0) * f j) = ((1 : Rat) / 12) * f i := by
  induction B with
  | zero => omega
  | succ B ih =>
    simp only [sumRange]
    by_cases heq : i = B
    · subst heq
      have h0 : sumRange i (fun j => (if i = j then (1 : Rat) / 12 else 0) * f j) = 0 := by
        have hcongr : sumRange i (fun j => (if i = j then (1 : Rat) / 12 else 0) * f j) =
            sumRange i (fun _ => (0 : Rat)) := by
          apply sumRange_congr
          intro j hj
          have hne : i ≠ j := by omega
          simp [hne]
        rw [hcongr, sumRange_const]; grind
      rw [h0]
      simp; grind
    · have hlt : i < B := by omega
      rw [ih hlt]
      simp [heq]; grind

private theorem walsh_eig_alg_0 (B : Rat) (hB : B ≠ 0) :
    (1 : Rat) / 12 + (1 : Rat) / (12 * B * B) * B = (1 : Rat) / 12 + (1 : Rat) / (12 * B) := by
  grind

private theorem walsh_eig_alg_pow2 (B x : Rat) (hB : B ≠ 0) :
    (1 : Rat) / 12 + (x * x * B) / (4 * B * B) = (1 : Rat) / 12 + (x * x) / (4 * B) := by
  grind

theorem xorCovMatrix_walsh_eig (b k i : Nat) (hk : k < 2 ^ b) (hi : i < 2 ^ b) :
    matVec (2 ^ b) (xorCovMatrix b) (walshSign b k) i =
    xorWalshEig b k * walshSign b k i := by
  unfold matVec xorCovMatrix xorRankCov
  have hBne : ((2 ^ b : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero b
  -- Split the matrix-vector product into the 3 terms of `xorCovMatrix`
  have hsplit :
      sumRange (2 ^ b) (fun j =>
        ((if i = j then (1 : Rat) / 12 else 0) +
          (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat)) +
          sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (i ^^^ j)) /
            (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat))) *
        walshSign b k j) =
      sumRange (2 ^ b) (fun j => (if i = j then (1 : Rat) / 12 else 0) * walshSign b k j) +
      sumRange (2 ^ b) (fun j =>
        ((1 : Rat) / (12 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat))) * walshSign b k j) +
      sumRange (2 ^ b) (fun j =>
        (sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (i ^^^ j)) /
          (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat))) * walshSign b k j) := by
    rw [← sumRange_add, ← sumRange_add]
    apply sumRange_congr
    intro j _
    grind
  rw [hsplit]
  -- Term 1: diagonal `(1/12) * h_k(i)`
  rw [sumRange_delta_mul (2 ^ b) i hi (walshSign b k)]
  -- Term 2: constant `(1 / (12 B^2)) * ∑_j h_k(j)`
  rw [sumRange_mul_left, sumRange_walshSign b k hk]
  -- Term 3: dyadic rank sum
  have hterm3 :
      sumRange (2 ^ b) (fun j =>
        (sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (i ^^^ j)) /
          (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat))) * walshSign b k j) =
      sumRange b (fun s =>
        ((4 ^ s : Nat) : Rat) * bitSign s i *
          (if k = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) /
        (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat)) := by
    have hpull :
        sumRange (2 ^ b) (fun j =>
          (sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (i ^^^ j)) /
            (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat))) * walshSign b k j) =
        sumRange (2 ^ b) (fun j =>
          sumRange b (fun s =>
            ((4 ^ s : Nat) : Rat) * bitSign s i * (bitSign s j * walshSign b k j))) /
          (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat)) := by
      rw [← sumRange_div_const]
      apply sumRange_congr
      intro j _
      have h1 :
          sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (i ^^^ j)) * walshSign b k j =
          sumRange b (fun s =>
            ((4 ^ s : Nat) : Rat) * bitSign s i * (bitSign s j * walshSign b k j)) := by
        rw [← sumRange_mul_right]
        apply sumRange_congr
        intro s _
        rw [bitSign_xor]
        grind
      rw [← h1]
      grind
    rw [hpull, sumRange_swap]
    congr 1
    apply sumRange_congr
    intro s hs
    rw [sumRange_mul_left, sumRange_bitSign_walshSign b s k hs hk]
  rw [hterm3]
  -- Evaluate Term 3 by cases on `k`
  unfold xorWalshEig
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte]
    have hzero3 :
        sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
          (if 0 = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) = 0 := by
      have hcongr :
          sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
            (if 0 = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) =
          sumRange b (fun _ => (0 : Rat)) := by
        apply sumRange_congr
        intro s _
        have hne : (0 : Nat) ≠ 2 ^ s := Nat.ne_of_lt (Nat.two_pow_pos s)
        simp [hne]
      rw [hcongr, sumRange_const]; grind
    rw [hzero3, walshSign_zero_left]
    have h0div : (0 : Rat) / (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat)) = 0 := by grind
    rw [h0div]
    have halg := walsh_eig_alg_0 ((2 ^ b : Nat) : Rat) hBne
    grind
  · simp only [hk0, ↓reduceIte]
    by_cases hp1 : popcountBits b k = 1
    · simp only [hp1, ↓reduceIte]
      obtain ⟨s0, hs0, hks0⟩ := (popcountBits_eq_one_iff hk).mp hp1
      have hsum3 :
          sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
            (if k = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) =
          ((4 ^ s0 : Nat) : Rat) * bitSign s0 i * ((2 ^ b : Nat) : Rat) := by
        have hgen : ∀ n, s0 < n →
            sumRange n (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
              (if 2 ^ s0 = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) =
            ((4 ^ s0 : Nat) : Rat) * bitSign s0 i * ((2 ^ b : Nat) : Rat) := by
          intro n
          induction n with
          | zero => omega
          | succ n ih =>
            intro hlt
            simp only [sumRange]
            by_cases heq : s0 = n
            · subst heq
              have h0 :
                  sumRange s0 (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
                    (if 2 ^ s0 = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) = 0 := by
                have hcongr :
                    sumRange s0 (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
                      (if 2 ^ s0 = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) =
                    sumRange s0 (fun _ => (0 : Rat)) := by
                  apply sumRange_congr
                  intro s hs
                  have hne : 2 ^ s0 ≠ 2 ^ s :=
                    Nat.ne_of_gt (Nat.pow_lt_pow_right (by omega) hs)
                  simp [hne]
                rw [hcongr, sumRange_const]; grind
              rw [h0]; simp; grind
            · have hlt' : s0 < n := by omega
              rw [ih hlt']
              have hne : 2 ^ s0 ≠ 2 ^ n :=
                Nat.ne_of_lt (Nat.pow_lt_pow_right (by omega) hlt')
              simp [hne]; grind
        rw [hks0]
        exact hgen b hs0
      rw [hsum3, hks0, bitSign_eq_walshSign_pow2 hs0]
      have h4s0 : ((4 ^ s0 : Nat) : Rat) = ((2 ^ s0 : Nat) : Rat) * ((2 ^ s0 : Nat) : Rat) := by
        have hnat : 4 ^ s0 = 2 ^ s0 * 2 ^ s0 := by rw [← Nat.mul_pow]
        rw [hnat, rat_natCast_mul]
      rw [h4s0]
      have halg := walsh_eig_alg_pow2 ((2 ^ b : Nat) : Rat) ((2 ^ s0 : Nat) : Rat) hBne
      grind
    · simp only [hp1, ↓reduceIte]
      have hzero3 :
          sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
            (if k = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) = 0 := by
        have hcongr :
            sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s i *
              (if k = 2 ^ s then ((2 ^ b : Nat) : Rat) else 0)) =
            sumRange b (fun _ => (0 : Rat)) := by
          apply sumRange_congr
          intro s hs
          have hne : k ≠ 2 ^ s := by
            intro heq
            exact hp1 ((popcountBits_eq_one_iff hk).mpr ⟨s, hs, heq⟩)
          simp [hne]
        rw [hcongr, sumRange_const]; grind
      rw [hzero3]
      grind

/-! ### 4. Bit-Reversal Symmetry for `xorVdcCovMatrix` -/

theorem bitrev_succ_half {b x : Nat} (hx : x < 2 ^ b) :
    bitrev (b + 1) x = 2 * bitrev b x := by
  induction b generalizing x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0; rfl
  | succ b ih =>
    have hdiv : x / 2 < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
      omega
    have hstep1 : bitrev (b + 1 + 1) x = (x % 2) * 2 ^ (b + 1) + bitrev (b + 1) (x / 2) := rfl
    have hstep2 : bitrev (b + 1) x = (x % 2) * 2 ^ b + bitrev b (x / 2) := rfl
    rw [hstep1, hstep2, ih hdiv, Nat.pow_succ]
    have hm : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hm with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega

theorem bitrev_succ_add_pow {b x : Nat} (hx : x < 2 ^ b) :
    bitrev (b + 1) (2 ^ b + x) = 2 * bitrev b x + 1 := by
  induction b generalizing x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0; rfl
  | succ b ih =>
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmod : (2 ^ (b + 1) + x) % 2 = x % 2 := by rw [hpow]; omega
    have hdiv : (2 ^ (b + 1) + x) / 2 = 2 ^ b + x / 2 := by rw [hpow]; omega
    have hxdiv : x / 2 < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hstep1 : bitrev (b + 1 + 1) (2 ^ (b + 1) + x) =
        ((2 ^ (b + 1) + x) % 2) * 2 ^ (b + 1) + bitrev (b + 1) ((2 ^ (b + 1) + x) / 2) := rfl
    have hstep2 : bitrev (b + 1) x = (x % 2) * 2 ^ b + bitrev b (x / 2) := rfl
    rw [hstep1, hstep2, hmod, hdiv, ih hxdiv, Nat.pow_succ]
    have hm : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hm with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega

theorem sumRange_bitrev (b : Nat) (f : Nat → Rat) :
    sumRange (2 ^ b) (fun j => f (bitrev b j)) = sumRange (2 ^ b) f := by
  induction b generalizing f with
  | zero => simp [sumRange, bitrev]
  | succ b ih =>
    have hpow1 : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
    have hpow2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow1, sumRange_append]
    have hleft : sumRange (2 ^ b) (fun j => f (bitrev (b + 1) j)) =
        sumRange (2 ^ b) (fun j => f (2 * j)) := by
      have hcongr : sumRange (2 ^ b) (fun j => f (bitrev (b + 1) j)) =
          sumRange (2 ^ b) (fun j => f (2 * bitrev b j)) := by
        apply sumRange_congr
        intro j hj
        rw [bitrev_succ_half hj]
      rw [hcongr]
      exact ih (fun x => f (2 * x))
    have hright : sumRange (2 ^ b) (fun j => f (bitrev (b + 1) (2 ^ b + j))) =
        sumRange (2 ^ b) (fun j => f (2 * j + 1)) := by
      have hcongr : sumRange (2 ^ b) (fun j => f (bitrev (b + 1) (2 ^ b + j))) =
          sumRange (2 ^ b) (fun j => f (2 * bitrev b j + 1)) := by
        apply sumRange_congr
        intro j hj
        rw [bitrev_succ_add_pow hj]
      rw [hcongr]
      exact ih (fun x => f (2 * x + 1))
    rw [hleft, hright, ← sumRange_add, ← sumRange_two_mul, ← hpow2, hpow1]

theorem popcountBits_bitrev (b x : Nat) :
    popcountBits b (bitrev b x) = popcountBits b x := by
  induction b generalizing x with
  | zero => rfl
  | succ b ih =>
    -- Split `x` into `x % 2^b` and top bit, or directly induct using `bitrev (b+1)`
    have hmod_lt : x % 2 ^ (b + 1) < 2 ^ (b + 1) := Nat.mod_lt x (Nat.two_pow_pos (b + 1))
    -- Prove first that `bitrev` and `popcountBits` depend only on `x % 2^b`.
    have hbr_mod : ∀ n y, bitrev n (y % 2 ^ n) = bitrev n y := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ihn =>
        intro y
        simp only [bitrev]
        have h1 : (y % 2 ^ (n + 1)) % 2 = y % 2 := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          rw [hpow, Nat.mod_mul_right_mod]
        have h2 : (y % 2 ^ (n + 1)) / 2 = (y / 2) % 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          rw [hpow, Nat.mod_mul_right_div_self]
        rw [h1, h2, ihn (y / 2)]
    have hpc_mod : ∀ n y, popcountBits n (y % 2 ^ n) = popcountBits n y := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ihn =>
        intro y
        simp only [popcountBits]
        have h1 : (y % 2 ^ (n + 1)) % 2 = y % 2 := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          rw [hpow, Nat.mod_mul_right_mod]
        have h2 : (y % 2 ^ (n + 1)) / 2 = (y / 2) % 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          rw [hpow, Nat.mod_mul_right_div_self]
        rw [h1, h2, ihn (y / 2)]
    rw [← hbr_mod (b + 1) x, ← hpc_mod (b + 1) x]
    let y := x % 2 ^ (b + 1)
    have hy : y < 2 ^ (b + 1) := hmod_lt
    show popcountBits (b + 1) (bitrev (b + 1) y) = popcountBits (b + 1) y
    by_cases hlt : y < 2 ^ b
    · have htop0 : ∀ n z, z < 2 ^ n → popcountBits (n + 1) z = popcountBits n z := by
        intro n
        induction n with
        | zero =>
          intro z hz
          have hz0 : z = 0 := by omega
          subst hz0; rfl
        | succ n ihn =>
          intro z hz
          have hstep1 : popcountBits (n + 1 + 1) z = z % 2 + popcountBits (n + 1) (z / 2) := rfl
          have hstep2 : popcountBits (n + 1) z = z % 2 + popcountBits n (z / 2) := rfl
          have hzdiv : z / 2 < 2 ^ n := by
            rw [Nat.div_lt_iff_lt_mul (by omega)]
            have : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
            omega
          rw [hstep1, hstep2, ihn (z / 2) hzdiv]
      rw [bitrev_succ_half hlt, htop0 b y hlt]
      have hstep : popcountBits (b + 1) (2 * bitrev b y) =
          (2 * bitrev b y) % 2 + popcountBits b ((2 * bitrev b y) / 2) := rfl
      have h1 : (2 * bitrev b y) % 2 = 0 := by omega
      have h2 : (2 * bitrev b y) / 2 = bitrev b y := by omega
      rw [hstep, h1, h2, ih y]; omega
    · let z := y - 2 ^ b
      have hz : z < 2 ^ b := by
        have : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
        omega
      have hyEq : y = 2 ^ b + z := by omega
      have htop1 : ∀ n w, w < 2 ^ n → popcountBits (n + 1) (2 ^ n + w) = 1 + popcountBits n w := by
        intro n
        induction n with
        | zero =>
          intro w hw
          have hw0 : w = 0 := by omega
          subst hw0; rfl
        | succ n ihn =>
          intro w hw
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          have hm : (2 ^ (n + 1) + w) % 2 = w % 2 := by rw [hpow]; omega
          have hd : (2 ^ (n + 1) + w) / 2 = 2 ^ n + w / 2 := by rw [hpow]; omega
          have hwdiv : w / 2 < 2 ^ n := by
            rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
          have hstep1 : popcountBits (n + 1 + 1) (2 ^ (n + 1) + w) =
              (2 ^ (n + 1) + w) % 2 + popcountBits (n + 1) ((2 ^ (n + 1) + w) / 2) := rfl
          have hstep2 : popcountBits (n + 1) w = w % 2 + popcountBits n (w / 2) := rfl
          rw [hstep1, hstep2, hm, hd, ihn (w / 2) hwdiv]; omega
      rw [hyEq, bitrev_succ_add_pow hz, htop1 b z hz]
      have hstep : popcountBits (b + 1) (2 * bitrev b z + 1) =
          (2 * bitrev b z + 1) % 2 + popcountBits b ((2 * bitrev b z + 1) / 2) := rfl
      have h1 : (2 * bitrev b z + 1) % 2 = 1 := by omega
      have h2 : (2 * bitrev b z + 1) / 2 = bitrev b z := by omega
      rw [hstep, h1, h2, ih z]

theorem bitrev_and (b k i : Nat) :
    bitrev b (k &&& i) = bitrev b k &&& bitrev b i := by
  induction b generalizing k i with
  | zero => simp [bitrev]
  | succ b ih =>
    simp only [bitrev]
    have hmod : (k &&& i) % 2 = (k % 2) * (i % 2) := by
      have htb : (k &&& i).testBit 0 = (k.testBit 0 && i.testBit 0) := Nat.testBit_and k i 0
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
          Nat.testBit_eq_decide_div_mod_eq] at htb
      simp only [Nat.pow_zero, Nat.div_one] at htb
      have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
      have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
      have hki : (k &&& i) % 2 = 0 ∨ (k &&& i) % 2 = 1 := by omega
      rcases hk with hk0 | hk1 <;> rcases hi with hi0 | hi1 <;> rcases hki with hki0 | hki1 <;>
        simp_all
    have hdiv : (k &&& i) / 2 = (k / 2) &&& (i / 2) := by
      apply Nat.eq_of_testBit_eq
      intro s
      rw [Nat.testBit_and, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_div_two,
          Nat.testBit_and]
    rw [hmod, hdiv, ih (k / 2) (i / 2)]
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_and]
    have hbr1 : bitrev b (k / 2) < 2 ^ b := bitrev_lt b (k / 2)
    have hbr2 : bitrev b (i / 2) < 2 ^ b := bitrev_lt b (i / 2)
    have hbr12 : bitrev b (k / 2) &&& bitrev b (i / 2) < 2 ^ b :=
      Nat.and_lt_two_pow _ hbr2
    have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hk with hk0 | hk1 <;> rcases hi with hi0 | hi1
    · simp [hk0, hi0, Nat.testBit_and]
    · simp only [hk0, hi1, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
      rw [testBit_add_two_pow hbr2, Nat.testBit_and]
      by_cases hs : s = b
      · have hfalse : (bitrev b (k / 2)).testBit s = false :=
          testBit_eq_false_of_lt_pow hbr1 (by omega)
        rw [hfalse]; simp [hs]
      · simp [hs]
    · simp only [hk1, hi0, Nat.mul_zero, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
      rw [testBit_add_two_pow hbr1, Nat.testBit_and]
      by_cases hs : s = b
      · have hfalse : (bitrev b (i / 2)).testBit s = false :=
          testBit_eq_false_of_lt_pow hbr2 (by omega)
        rw [hfalse]; simp [hs]
      · simp [hs]
    · simp only [hk1, hi1, Nat.one_mul]
      rw [testBit_add_two_pow hbr12, testBit_add_two_pow hbr1, testBit_add_two_pow hbr2,
          Nat.testBit_and]
      by_cases hs : s = b <;> simp [hs]

theorem walshSign_bitrev (b k i : Nat) :
    walshSign b (bitrev b k) (bitrev b i) = walshSign b k i := by
  unfold walshSign
  rw [← bitrev_and, popcountBits_bitrev]

theorem xorVdcCovMatrix_walsh_eig (b k i : Nat) (_hk : k < 2 ^ b) (_hi : i < 2 ^ b) :
    matVec (2 ^ b) (xorVdcCovMatrix b) (walshSign b k) i =
    xorVdcWalshEig b k * walshSign b k i := by
  unfold matVec xorVdcCovMatrix xorVdcWalshEig
  have hcongr :
      sumRange (2 ^ b) (fun j => xorCovMatrix b (bitrev b i) (bitrev b j) * walshSign b k j) =
      sumRange (2 ^ b) (fun j =>
        xorCovMatrix b (bitrev b i) (bitrev b j) * walshSign b (bitrev b k) (bitrev b j)) := by
    apply sumRange_congr
    intro j _
    rw [walshSign_bitrev]
  rw [hcongr, sumRange_bitrev b (fun x => xorCovMatrix b (bitrev b i) x * walshSign b (bitrev b k) x)]
  have heig := xorCovMatrix_walsh_eig b (bitrev b k) (bitrev b i) (bitrev_lt b k) (bitrev_lt b i)
  unfold matVec at heig
  rw [heig, walshSign_bitrev]

/-! ### 5. Exact Trace Conservation (`∑_k λ_k = B / 6`) -/

private theorem trace_alg_identity (B : Rat) (hB : B ≠ 0) :
    B * ((1 : Rat) / 12) + (1 : Rat) / (12 * B) + ((B * B - 1) / 3) / (4 * B) =
    B * ((1 : Rat) / 6) := by
  grind

theorem xorWalshEig_trace (b : Nat) :
    sumRange (2 ^ b) (fun k => xorWalshEig b k) = ((2 ^ b : Nat) : Rat) * ((1 : Rat) / 6) := by
  have hBne : ((2 ^ b : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero b
  -- Split `xorWalshEig b k = 1/12 + excess(k)`
  have hsplit :
      sumRange (2 ^ b) (fun k => xorWalshEig b k) =
      sumRange (2 ^ b) (fun _ => (1 : Rat) / 12) +
      sumRange (2 ^ b) (fun k =>
        if k = 0 then (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) else 0) +
      sumRange (2 ^ b) (fun k =>
        if popcountBits b k = 1 then ((k : Rat) * (k : Rat)) / (4 * ((2 ^ b : Nat) : Rat)) else 0) := by
    rw [← sumRange_add, ← sumRange_add]
    apply sumRange_congr
    intro k _
    unfold xorWalshEig
    by_cases hk0 : k = 0
    · subst hk0
      have hp0 : popcountBits b 0 = 0 := popcountBits_zero b
      simp [hp0]; grind
    · by_cases hp1 : popcountBits b k = 1
      · simp [hk0, hp1]; grind
      · simp [hk0, hp1]; grind
  rw [hsplit, sumRange_const]
  -- Evaluate the `k = 0` term
  have hk0_sum :
      sumRange (2 ^ b) (fun k =>
        if k = 0 then (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) else 0) =
      (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) := by
    have hgen : ∀ n, 0 < n →
        sumRange n (fun k => if k = 0 then (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) else 0) =
        (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        simp only [sumRange]
        cases n with
        | zero => simp [sumRange]; grind
        | succ n =>
          rw [ih (by omega)]
          simp; grind
    exact hgen (2 ^ b) (Nat.two_pow_pos b)
  rw [hk0_sum]
  -- Evaluate the `popcount = 1` sum = `(∑_{s < b} 4^s) / (4 B)`
  have hpow1_sum :
      sumRange (2 ^ b) (fun k =>
        if popcountBits b k = 1 then ((k : Rat) * (k : Rat)) / (4 * ((2 ^ b : Nat) : Rat)) else 0) =
      sumRange b (fun s => ((4 ^ s : Nat) : Rat)) / (4 * ((2 ^ b : Nat) : Rat)) := by
    rw [← sumRange_div_const]
    have hnum :
        sumRange (2 ^ b) (fun k =>
          if popcountBits b k = 1 then ((k : Rat) * (k : Rat)) else 0) =
        sumRange b (fun s => ((4 ^ s : Nat) : Rat)) := by
      have hgen : ∀ n,
          sumRange (2 ^ n) (fun k =>
            if popcountBits n k = 1 then ((k : Rat) * (k : Rat)) else 0) =
          sumRange n (fun s => ((4 ^ s : Nat) : Rat)) := by
        intro n
        induction n with
        | zero => simp [sumRange, popcountBits]; grind
        | succ n ih =>
          have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
          rw [hpow, sumRange_append]
          -- Left half: `k < 2^n`, `popcountBits (n+1) k = popcountBits n k`
          have hleft :
              sumRange (2 ^ n) (fun k =>
                if popcountBits (n + 1) k = 1 then ((k : Rat) * (k : Rat)) else 0) =
              sumRange (2 ^ n) (fun k =>
                if popcountBits n k = 1 then ((k : Rat) * (k : Rat)) else 0) := by
            apply sumRange_congr
            intro k hk
            have hpc : popcountBits (n + 1) k = popcountBits n k := by
              have htop0 : ∀ m z, z < 2 ^ m → popcountBits (m + 1) z = popcountBits m z := by
                intro m
                induction m with
                | zero => intro z hz; have hz0 : z = 0 := (by omega); rw [hz0]; rfl
                | succ m ihm =>
                  intro z hz
                  have hstep1 : popcountBits (m + 1 + 1) z = z % 2 + popcountBits (m + 1) (z / 2) := rfl
                  have hstep2 : popcountBits (m + 1) z = z % 2 + popcountBits m (z / 2) := rfl
                  have hzdiv : z / 2 < 2 ^ m := by
                    rw [Nat.div_lt_iff_lt_mul (by omega)]
                    have : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
                    omega
                  rw [hstep1, hstep2, ihm (z / 2) hzdiv]
              exact htop0 n k hk
            rw [hpc]
          -- Right half: `2^n + k`, `popcountBits (n+1) (2^n + k) = 1 + popcountBits n k`
          -- So `= 1` iff `k = 0`!
          have hright :
              sumRange (2 ^ n) (fun k =>
                if popcountBits (n + 1) (2 ^ n + k) = 1 then
                  (((2 ^ n + k : Nat) : Rat) * ((2 ^ n + k : Nat) : Rat))
                else 0) =
              ((4 ^ n : Nat) : Rat) := by
            have hcongr :
                sumRange (2 ^ n) (fun k =>
                  if popcountBits (n + 1) (2 ^ n + k) = 1 then
                    (((2 ^ n + k : Nat) : Rat) * ((2 ^ n + k : Nat) : Rat))
                  else 0) =
                sumRange (2 ^ n) (fun k =>
                  if k = 0 then ((4 ^ n : Nat) : Rat) else 0) := by
              apply sumRange_congr
              intro k hk
              have htop1 : ∀ m w, w < 2 ^ m →
                  popcountBits (m + 1) (2 ^ m + w) = 1 + popcountBits m w := by
                intro m
                induction m with
                | zero => intro w hw; have hw0 : w = 0 := (by omega); rw [hw0]; rfl
                | succ m ihm =>
                  intro w hw
                  have hpowm : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
                  have hm : (2 ^ (m + 1) + w) % 2 = w % 2 := by rw [hpowm]; omega
                  have hd : (2 ^ (m + 1) + w) / 2 = 2 ^ m + w / 2 := by rw [hpowm]; omega
                  have hwdiv : w / 2 < 2 ^ m := by
                    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
                  have hstep1 : popcountBits (m + 1 + 1) (2 ^ (m + 1) + w) =
                      (2 ^ (m + 1) + w) % 2 + popcountBits (m + 1) ((2 ^ (m + 1) + w) / 2) := rfl
                  have hstep2 : popcountBits (m + 1) w = w % 2 + popcountBits m (w / 2) := rfl
                  rw [hstep1, hstep2, hm, hd, ihm (w / 2) hwdiv]; omega
              rw [htop1 n k hk]
              by_cases hk0 : k = 0
              · subst hk0
                rw [popcountBits_zero]
                have h4n : 4 ^ n = 2 ^ n * 2 ^ n := by rw [← Nat.mul_pow]
                simp [h4n]
              · have hpne : popcountBits n k ≠ 0 := fun h0 => hk0 ((popcountBits_eq_zero_iff hk).mp h0)
                simp [hk0, hpne]
            rw [hcongr]
            have hgen0 : ∀ m, 0 < m →
                sumRange m (fun k => if k = 0 then ((4 ^ n : Nat) : Rat) else 0) =
                ((4 ^ n : Nat) : Rat) := by
              intro m hm
              induction m with
              | zero => omega
              | succ m ihm =>
                simp only [sumRange]
                cases m with
                | zero => simp [sumRange]; grind
                | succ m => rw [ihm (by omega)]; simp; grind
            exact hgen0 (2 ^ n) (Nat.two_pow_pos n)
          rw [hleft, ih, hright]
          simp [sumRange]
      exact hgen b
    have hdiv_eq :
        sumRange (2 ^ b) (fun k =>
          if popcountBits b k = 1 then ((k : Rat) * (k : Rat)) / (4 * ((2 ^ b : Nat) : Rat)) else 0) =
        sumRange (2 ^ b) (fun k =>
          (if popcountBits b k = 1 then ((k : Rat) * (k : Rat)) else 0) /
            (4 * ((2 ^ b : Nat) : Rat))) := by
      apply sumRange_congr
      intro k _
      by_cases h : popcountBits b k = 1 <;> simp [h]; grind
    rw [hdiv_eq, sumRange_div_const, hnum, ← sumRange_div_const]
  rw [hpow1_sum, sumRange_geom4]
  have h4b : ((4 ^ b : Nat) : Rat) = ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat) := by
    have hnat : 4 ^ b = 2 ^ b * 2 ^ b := by rw [← Nat.mul_pow]
    rw [hnat, rat_natCast_mul]
  rw [h4b]
  exact trace_alg_identity ((2 ^ b : Nat) : Rat) hBne

theorem xorVdcWalshEig_trace (b : Nat) :
    sumRange (2 ^ b) (fun k => xorVdcWalshEig b k) = ((2 ^ b : Nat) : Rat) * ((1 : Rat) / 6) := by
  unfold xorVdcWalshEig
  rw [sumRange_bitrev b (fun k => xorWalshEig b k)]
  exact xorWalshEig_trace b

/-! ### 6. Popcount ≥ 2 Modes, Exact Mode Counts (`14/16`, `29/32`), and E2M1 Ratios -/

theorem xorWalshEig_popcount_ge_two (b k : Nat) (hk : 2 ≤ popcountBits b k) :
    xorWalshEig b k = 1 / 12 ∧ xorVdcWalshEig b k = 1 / 12 := by
  have hne0 : k ≠ 0 := by
    intro h0; subst h0; rw [popcountBits_zero] at hk; omega
  have hne1 : popcountBits b k ≠ 1 := by omega
  have h1 : xorWalshEig b k = 1 / 12 := by
    unfold xorWalshEig
    simp [hne0, hne1]
  have hpc_br : popcountBits b (bitrev b k) = popcountBits b k := popcountBits_bitrev b k
  have hbr_ne0 : bitrev b k ≠ 0 := by
    intro h0; rw [h0, popcountBits_zero] at hpc_br; omega
  have hbr_ne1 : popcountBits b (bitrev b k) ≠ 1 := by omega
  have h2 : xorVdcWalshEig b k = 1 / 12 := by
    unfold xorVdcWalshEig xorWalshEig
    simp [hbr_ne0, hbr_ne1]
  exact ⟨h1, h2⟩

theorem e2m1_ratios_exact :
    e2m1MeanH = 7 / 6 ∧
    e2m1MeanH2 = 7 / 4 ∧
    e2m1XorMseRatio 16 = 61 / 96 ∧
    e2m1XorMseRatio 32 = 359 / 576 := by
  have h1 : e2m1MeanH = 7 / 6 := by simp only [e2m1MeanH, e2m1Widths, sumListRat]; grind
  have h2 : e2m1MeanH2 = 7 / 4 := by simp only [e2m1MeanH2, e2m1Widths, sumListRat]; grind
  have h3 : e2m1XorMseRatio 16 = 61 / 96 := by unfold e2m1XorMseRatio; rw [h1, h2]; grind
  have h4 : e2m1XorMseRatio 32 = 359 / 576 := by unfold e2m1XorMseRatio; rw [h1, h2]; grind
  exact ⟨h1, h2, h3, h4⟩

theorem xorWalshEig_lt_one_sixth_iff {b k : Nat} (hb : 1 ≤ b) :
    xorWalshEig b k < 1 / 6 ↔ (k = 0 ∨ popcountBits b k ≠ 1 ∨ 3 * k * k < 2 ^ b) := by
  unfold xorWalshEig
  have hBpos : (0 : Rat) < ((2 ^ b : Nat) : Rat) := rat_pow2_pos b
  have hBgt1 : (1 : Rat) < ((2 ^ b : Nat) : Rat) := by
    have hnat : 1 < 2 ^ b := by
      have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb
      omega
    have hint : (1 : Int) < ((2 ^ b : Nat) : Int) := by omega
    exact Rat.intCast_lt_intCast.mpr hint
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte, true_or, iff_true]
    have h1 : (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) < (1 : Rat) / 12 := by
      have hpos : (0 : Rat) < 12 * ((2 ^ b : Nat) : Rat) := rat_mul_pos (by grind) hBpos
      have hsub : (1 : Rat) / 12 - (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) =
          (((2 ^ b : Nat) : Rat) - 1) / (12 * ((2 ^ b : Nat) : Rat)) := by
        have hne : ((2 ^ b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hBpos
        grind
      apply rat_lt_of_sub_pos
      rw [hsub, Rat.div_def]
      exact rat_mul_pos (rat_sub_pos hBgt1) (rat_inv_pos hpos)
    have h2 : (1 : Rat) / 12 + (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat)) < (1 : Rat) / 12 + (1 : Rat) / 12 := by
      rw [Rat.add_comm ((1 : Rat) / 12), Rat.add_comm ((1 : Rat) / 12)]
      exact (Rat.add_lt_add_right (c := (1 : Rat) / 12)).mpr h1
    have h3 : (1 : Rat) / 12 + (1 : Rat) / 12 = (1 : Rat) / 6 := by grind
    rw [h3] at h2
    exact h2
  · by_cases hp1 : popcountBits b k = 1
    · simp only [hk0, hp1, ↓reduceIte, false_or, ne_eq, not_true_eq_false]
      have h4Bpos : (0 : Rat) < 4 * ((2 ^ b : Nat) : Rat) := rat_mul_pos (by grind) hBpos
      have h4Bne : 4 * ((2 ^ b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt h4Bpos
      have hiff_rat :
          ((1 : Rat) / 12 + ((k : Rat) * (k : Rat)) / (4 * ((2 ^ b : Nat) : Rat)) < 1 / 6) ↔
          (3 * (k : Rat) * (k : Rat) < ((2 ^ b : Nat) : Rat)) := by
        have hdiff :
            (1 : Rat) / 6 - ((1 : Rat) / 12 + ((k : Rat) * (k : Rat)) / (4 * ((2 ^ b : Nat) : Rat))) =
            (((2 ^ b : Nat) : Rat) - 3 * (k : Rat) * (k : Rat)) / (12 * ((2 ^ b : Nat) : Rat)) := by
          have hne : ((2 ^ b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hBpos
          grind
        have h12Bpos : (0 : Rat) < 12 * ((2 ^ b : Nat) : Rat) := rat_mul_pos (by grind) hBpos
        constructor
        · intro hlt
          have hpos := rat_sub_pos hlt
          rw [hdiff, Rat.div_def] at hpos
          have hnum_pos : (0 : Rat) < ((2 ^ b : Nat) : Rat) - 3 * (k : Rat) * (k : Rat) := by
            by_cases hn : (0 : Rat) < ((2 ^ b : Nat) : Rat) - 3 * (k : Rat) * (k : Rat)
            · exact hn
            · have hle : ((2 ^ b : Nat) : Rat) - 3 * (k : Rat) * (k : Rat) ≤ 0 := Rat.not_lt.mp hn
              have hprod : (((2 ^ b : Nat) : Rat) - 3 * (k : Rat) * (k : Rat)) *
                  (12 * ((2 ^ b : Nat) : Rat))⁻¹ ≤ 0 * (12 * ((2 ^ b : Nat) : Rat))⁻¹ :=
                rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt (rat_inv_pos h12Bpos))
              have h0 : (0 : Rat) * (12 * ((2 ^ b : Nat) : Rat))⁻¹ = 0 := by grind
              rw [h0] at hprod
              exact absurd hpos (Rat.not_lt.mpr hprod)
          exact rat_lt_of_sub_pos hnum_pos
        · intro hlt
          apply rat_lt_of_sub_pos
          rw [hdiff, Rat.div_def]
          exact rat_mul_pos (rat_sub_pos hlt) (rat_inv_pos h12Bpos)
      rw [hiff_rat]
      have hcast : ((3 * k * k : Nat) : Rat) = 3 * (k : Rat) * (k : Rat) := by
        rw [rat_natCast_mul, rat_natCast_mul]; rfl
      rw [← hcast]
      constructor
      · intro h
        have hint : ((3 * k * k : Nat) : Int) < ((2 ^ b : Nat) : Int) :=
          Rat.intCast_lt_intCast.mp h
        omega
      · intro h
        have hint : ((3 * k * k : Nat) : Int) < ((2 ^ b : Nat) : Int) := by omega
        exact Rat.intCast_lt_intCast.mpr hint
    · simp only [hk0, hp1, ↓reduceIte, false_or, ne_eq, not_false_eq_true, true_or, iff_true]
      grind

theorem countRange_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i, i < n → p i = q i) :
    countRange n p = countRange n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem walsh_better_mode_counts :
    countRange 16 (fun k => decide (xorVdcWalshEig 4 k < 1 / 6)) = 14 ∧
    countRange 32 (fun k => decide (xorVdcWalshEig 5 k < 1 / 6)) = 29 := by
  have h16 :
      countRange 16 (fun k => decide (xorVdcWalshEig 4 k < 1 / 6)) =
      countRange 16 (fun k =>
        let br := bitrev 4 k
        decide (br = 0 ∨ popcountBits 4 br ≠ 1 ∨ 3 * br * br < 2 ^ 4)) := by
    apply countRange_congr
    intro k _
    unfold xorVdcWalshEig
    simp only [decide_eq_decide]
    exact xorWalshEig_lt_one_sixth_iff (by omega)
  have h32 :
      countRange 32 (fun k => decide (xorVdcWalshEig 5 k < 1 / 6)) =
      countRange 32 (fun k =>
        let br := bitrev 5 k
        decide (br = 0 ∨ popcountBits 5 br ≠ 1 ∨ 3 * br * br < 2 ^ 5)) := by
    apply countRange_congr
    intro k _
    unfold xorVdcWalshEig
    simp only [decide_eq_decide]
    exact xorWalshEig_lt_one_sixth_iff (by omega)
  rw [h16, h32]
  decide

/-! ### 7. Headline Theorem 2 -/

theorem xor_vdc_walsh_spectrum_and_trace_conservation :
    (∀ (b k i : Nat), k < 2 ^ b → i < 2 ^ b →
      matVec (2 ^ b) (xorCovMatrix b) (walshSign b k) i = xorWalshEig b k * walshSign b k i ∧
      matVec (2 ^ b) (xorVdcCovMatrix b) (walshSign b k) i = xorVdcWalshEig b k * walshSign b k i) ∧
    (∀ (b k : Nat), 2 ≤ popcountBits b k →
      xorWalshEig b k = 1 / 12 ∧ xorVdcWalshEig b k = 1 / 12 ∧ (1 / 12 : Rat) < 1 / 6) ∧
    (∀ (b : Nat),
      sumRange (2 ^ b) (fun k => xorWalshEig b k) = ((2 ^ b : Nat) : Rat) * (1 / 6) ∧
      sumRange (2 ^ b) (fun k => xorVdcWalshEig b k) = ((2 ^ b : Nat) : Rat) * (1 / 6)) ∧
    (countRange 16 (fun k => decide (xorVdcWalshEig 4 k < 1 / 6)) = 14 ∧
     countRange 32 (fun k => decide (xorVdcWalshEig 5 k < 1 / 6)) = 29) ∧
    (e2m1XorMseRatio 16 = 61 / 96 ∧ e2m1XorMseRatio 32 = 359 / 576) := by
  refine ⟨?_, ?_, ?_, walsh_better_mode_counts, ?_⟩
  · intro b k i hk hi
    exact ⟨xorCovMatrix_walsh_eig b k i hk hi, xorVdcCovMatrix_walsh_eig b k i hk hi⟩
  · intro b k hk
    have ⟨h1, h2⟩ := xorWalshEig_popcount_ge_two b k hk
    exact ⟨h1, h2, by grind⟩
  · intro b
    exact ⟨xorWalshEig_trace b, xorVdcWalshEig_trace b⟩
  · exact ⟨e2m1_ratios_exact.2.2.1, e2m1_ratios_exact.2.2.2⟩

end XorVdcFp4Dither
