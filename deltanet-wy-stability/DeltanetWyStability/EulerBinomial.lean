/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltanetWyStability.RatAlg

/-!
# Theorem 4: Exact Binomial Power Law & Catastrophic Euler-Product Intermediate Peaks
-/

namespace DeltanetWyStability

/-- Left/right commutativity of matrix powers `A * A^k = A^k * A`. -/
theorem matPow_comm {n : Nat} (A : RatMat n n) (k : Nat) :
    matMul A (matPow A k) = matMul (matPow A k) A := by
  induction k with
  | zero =>
    simp only [matPow, matMul_id_left, matMul_id_right]
  | succ m ih =>
    simp only [matPow]
    rw [← matMul_assoc, ih, matMul_assoc]

theorem matPow_succ_left {n : Nat} (A : RatMat n n) (k : Nat) :
    matPow A (k + 1) = matMul A (matPow A k) := by
  rw [matPow, matPow_comm]

theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k' => rfl
  | succ n' ih =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [choose]
      rw [ih (by omega), ih (by omega)]

/-- Hockey-stick identity over `Fin C`:
    `∑_{lo ≤ m < hi} C(m - lo, k) = C(hi - lo, k + 1)`. -/
theorem sumFin_hockey_stick (C lo hi k : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ C) :
    sumFin (fun m : Fin C =>
      if lo ≤ m.val ∧ m.val < hi then ((choose (m.val - lo) k : Nat) : Rat) else 0) =
      ((choose (hi - lo) (k + 1) : Nat) : Rat) := by
  induction hi with
  | zero =>
    have hlo0 : lo = 0 := Nat.eq_zero_of_le_zero hlo
    subst hlo0
    rw [sumFin_congr (g := fun _ => 0)]
    · rw [sumFin_zero]; simp [choose]
    · intro m; simp
  | succ s ih =>
    by_cases hls : lo = s + 1
    · subst hls
      rw [sumFin_congr (g := fun _ => 0)]
      · rw [sumFin_zero, Nat.sub_self]; simp [choose]
      · intro m
        have hfalse : ¬ (s + 1 ≤ m.val ∧ m.val < s + 1) := by omega
        simp [hfalse]
    · have hlo_le : lo ≤ s := by omega
      have hs_lt : s < C := by omega
      let ms : Fin C := ⟨s, hs_lt⟩
      have hsplit : sumFin (fun m : Fin C =>
            if lo ≤ m.val ∧ m.val < s + 1 then ((choose (m.val - lo) k : Nat) : Rat) else 0) =
          sumFin (fun m : Fin C =>
            (if lo ≤ m.val ∧ m.val < s then ((choose (m.val - lo) k : Nat) : Rat) else 0) +
            (if m = ms then ((choose (s - lo) k : Nat) : Rat) else 0)) := by
        apply sumFin_congr
        intro m
        by_cases hms : m = ms
        · subst hms
          have h1 : lo ≤ s ∧ s < s + 1 := ⟨hlo_le, Nat.lt_succ_self s⟩
          simp only [ms, h1, ↓reduceIte]; grind
        · have hne : m.val ≠ s := fun hv => hms (Fin.ext hv)
          have heqv : (lo ≤ m.val ∧ m.val < s + 1) ↔ (lo ≤ m.val ∧ m.val < s) := by omega
          by_cases hc : lo ≤ m.val ∧ m.val < s
          · have hc' : lo ≤ m.val ∧ m.val < s + 1 := heqv.mpr hc
            simp only [hc, hc', hms, ↓reduceIte]; grind
          · have hc' : ¬ (lo ≤ m.val ∧ m.val < s + 1) := fun h => hc (heqv.mp h)
            simp only [hc, hc', hms, ↓reduceIte]; grind
      rw [hsplit, sumFin_add_fn, ih hlo_le (Nat.le_of_lt hs_lt)]
      have hsingle : sumFin (fun m : Fin C => if m = ms then ((choose (s - lo) k : Nat) : Rat) else 0) =
          ((choose (s - lo) k : Nat) : Rat) := by
        rw [sumFin_single ms]
        · simp
        · intro m hm; simp [hm]
      rw [hsingle]
      have hsub : s + 1 - lo = (s - lo) + 1 := by omega
      rw [hsub, choose, Rat.natCast_add]
      grind

/-- Exact entry formula for powers of the aligned strictly lower-triangular matrix `L_C`:
    for all `k ≥ 1`, `(L_C^k)_{i, j} = β^k * C(i - j - 1, k - 1)` when `j + k ≤ i`, else `0`. -/
theorem alignedL_pow_entry (C : Nat) (β : Rat) (k : Nat) (hk : 1 ≤ k) (i j : Fin C) :
    matPow (alignedL C β) k i j =
      if j.val + k ≤ i.val then
        ratPow β k * ((choose (i.val - j.val - 1) (k - 1) : Nat) : Rat)
      else
        0 := by
  cases k with
  | zero => omega
  | succ m =>
    clear hk
    induction m generalizing i j with
    | zero =>
      rw [matPow_succ_left, matPow, matMul_id_right]
      unfold alignedL
      simp only [Nat.add_sub_cancel, choose]
      by_cases hlt : j.val < i.val
      · have hle : j.val + 1 ≤ i.val := by omega
        simp only [hlt, hle, ↓reduceIte]
        rw [ratPow_one]
        grind
      · have hnot : ¬ j.val + 1 ≤ i.val := by omega
        simp only [hlt, hnot, ↓reduceIte]
    | succ m ih =>
      rw [matPow_succ_left]
      unfold matMul
      have hterm : sumFin (fun r : Fin C => alignedL C β i r * matPow (alignedL C β) (m + 1) r j) =
          sumFin (fun r : Fin C =>
            ratPow β (m + 2) *
              (if j.val + 1 ≤ r.val ∧ r.val < i.val then ((choose (r.val - (j.val + 1)) m : Nat) : Rat) else 0)) := by
        apply sumFin_congr
        intro r
        rw [ih r j]
        unfold alignedL
        by_cases hri : r.val < i.val
        · by_cases hjm : j.val + (m + 1) ≤ r.val
          · have hjr : j.val + 1 ≤ r.val ∧ r.val < i.val := ⟨by omega, hri⟩
            have hsub1 : r.val - j.val - 1 = r.val - (j.val + 1) := by omega
            have hsub2 : m + 1 - 1 = m := by omega
            simp only [hri, hjm, hjr, hsub1, hsub2, ↓reduceIte]
            have hp : ratPow β (m + 2) = ratPow β (m + 1) * β := rfl
            rw [hp]
            grind
          · by_cases hjr : j.val + 1 ≤ r.val
            · have hlt_m : r.val - (j.val + 1) < m := by omega
              have hch0 : choose (r.val - (j.val + 1)) m = 0 := choose_eq_zero_of_lt hlt_m
              simp only [hri, hjm, hjr, hch0, ↓reduceIte]; grind
            · simp only [hri, hjm, hjr, ↓reduceIte]; grind
        · simp only [hri, ↓reduceIte]; grind
      rw [hterm, sumFin_mul_left]
      by_cases hle : j.val + (m + 2) ≤ i.val
      · have hji : j.val + 1 ≤ i.val := by omega
        rw [sumFin_hockey_stick C (j.val + 1) i.val m hji (Nat.le_of_lt i.isLt)]
        have hsub1 : i.val - (j.val + 1) = i.val - j.val - 1 := by omega
        have hsub2 : m + 2 - 1 = m + 1 := by omega
        simp only [hle, hsub1, hsub2, ↓reduceIte]
      · simp only [hle, ↓reduceIte]
        by_cases hji : j.val + 1 ≤ i.val
        · rw [sumFin_hockey_stick C (j.val + 1) i.val m hji (Nat.le_of_lt i.isLt)]
          have hlt : i.val - (j.val + 1) < m + 1 := by omega
          rw [choose_eq_zero_of_lt hlt]
          grind
        · rw [sumFin_congr (g := fun _ => 0)]
          · rw [sumFin_zero]; grind
          · intro r
            have hnot : ¬ (j.val + 1 ≤ r.val ∧ r.val < i.val) := by omega
            simp [hnot]

/-! ### Fast factorial characterization of `choose` (zero exponential recursion) -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [choose, ih, choose_eq_zero_of_lt (Nat.lt_succ_self k)]

theorem choose_mul_fact (n k : Nat) (h : k ≤ n) :
    choose n k * (fact k * fact (n - k)) = fact n := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero h
    subst hk; rfl
  | succ n ih =>
    cases k with
    | zero =>
      simp only [choose, Nat.sub_zero, fact, Nat.one_mul]
    | succ j =>
      by_cases hjn : j = n
      · subst hjn
        rw [choose_self, Nat.sub_self]
        simp only [fact, Nat.one_mul, Nat.mul_one]
      · have hjlt : j < n := by omega
        have hjle : j ≤ n := Nat.le_of_lt hjlt
        have hj1le : j + 1 ≤ n := hjlt
        have hsub1 : n + 1 - (j + 1) = n - j := by omega
        have hsub2 : n - j = (n - (j + 1)) + 1 := by omega
        rw [choose, hsub1, Nat.add_mul]
        have h1 : choose n j * (fact (j + 1) * fact (n - j)) = (j + 1) * fact n := by
          have hrec := ih j hjle
          have hf : fact (j + 1) = (j + 1) * fact j := rfl
          rw [hf]
          have hassoc : choose n j * ((j + 1) * fact j * fact (n - j)) =
              (j + 1) * (choose n j * (fact j * fact (n - j))) := by
            rw [Nat.mul_assoc (j + 1), Nat.mul_left_comm (choose n j) (j + 1)]
          rw [hassoc, hrec]
        have h2 : choose n (j + 1) * (fact (j + 1) * fact (n - j)) = (n - j) * fact n := by
          have hrec := ih (j + 1) hj1le
          have hf : fact (n - j) = (n - j) * fact (n - (j + 1)) := by
            conv => lhs; rw [hsub2]
            simp only [fact]
            rw [← hsub2]
          rw [hf]
          have hassoc : choose n (j + 1) * (fact (j + 1) * ((n - j) * fact (n - (j + 1)))) =
              (n - j) * (choose n (j + 1) * (fact (j + 1) * fact (n - (j + 1)))) := by
            rw [Nat.mul_left_comm (fact (j + 1)) (n - j), Nat.mul_left_comm (choose n (j + 1)) (n - j)]
          rw [hassoc, hrec]
        rw [h1, h2, ← Nat.add_mul]
        have hsum : (j + 1) + (n - j) = n + 1 := by omega
        rw [hsum]
        rfl

theorem choose_14_7 : choose 14 7 = 3432 := by
  have h := choose_mul_fact 14 7 (by decide)
  have hpos : 0 < fact 7 * fact (14 - 7) := Nat.mul_pos (fact_pos 7) (fact_pos (14 - 7))
  have hval : 3432 * (fact 7 * fact (14 - 7)) = fact 14 := by decide
  exact Nat.eq_of_mul_eq_mul_right hpos (h.trans hval.symm)

theorem choose_62_31 : choose 62 31 = 465428353255261088 := by
  have h := choose_mul_fact 62 31 (by decide)
  have hpos : 0 < fact 31 * fact (62 - 31) := Nat.mul_pos (fact_pos 31) (fact_pos (62 - 31))
  have hval : 465428353255261088 * (fact 31 * fact (62 - 31)) = fact 62 := by decide
  exact Nat.eq_of_mul_eq_mul_right hpos (h.trans hval.symm)

theorem ratPow_two_32 : ratPow 2 32 = (4294967296 : Rat) := by
  have h4 : ratPow 2 4 = (16 : Rat) := by simp only [ratPow]; grind
  have h8 : ratPow 2 8 = (256 : Rat) := by rw [show (8 : Nat) = 4 + 4 from rfl, ratPow_add, h4]; grind
  have h16 : ratPow 2 16 = (65536 : Rat) := by rw [show (16 : Nat) = 8 + 8 from rfl, ratPow_add, h8]; grind
  rw [show (32 : Nat) = 16 + 16 from rfl, ratPow_add, h16]
  grind

/-- Headline Theorem 4: Exact binomial power law for aligned strictly-lower-triangular `L_C`
    and explicit catastrophic Euler-product intermediate peaks at `C = 16` and `C = 64`. -/
theorem euler_product_binomial_peak_explosion :
    (∀ (C : Nat) (β : Rat) (k : Nat), 1 ≤ k → ∀ (i j : Fin C), j.val + k ≤ i.val →
      matPow (alignedL C β) k i j =
        ratPow β k * ((choose (i.val - j.val - 1) (k - 1) : Nat) : Rat)) ∧
    matPow (alignedL 16 1) 8 ⟨15, by decide⟩ ⟨0, by decide⟩ = 3432 ∧
    matPow (alignedL 64 1) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ = 465428353255261088 ∧
    matPow (alignedL 64 2) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ =
      ratPow 2 32 * 465428353255261088 ∧
    (1000000000000000000000000000 : Rat) <
      matPow (alignedL 64 2) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ := by
  have h16 : matPow (alignedL 16 1) 8 ⟨15, by decide⟩ ⟨0, by decide⟩ = 3432 := by
    rw [alignedL_pow_entry 16 1 8 (by decide)]
    have hle : (⟨0, by decide⟩ : Fin 16).val + 8 ≤ (⟨15, by decide⟩ : Fin 16).val := by decide
    simp only [hle, ↓reduceIte, ratPow_one_base]
    have h1 : (⟨15, by decide⟩ : Fin 16).val - (⟨0, by decide⟩ : Fin 16).val - 1 = 14 := rfl
    have h2 : (8 : Nat) - 1 = 7 := rfl
    rw [h1, h2, choose_14_7]
    grind
  have h64_1 : matPow (alignedL 64 1) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ = 465428353255261088 := by
    rw [alignedL_pow_entry 64 1 32 (by decide)]
    have hle : (⟨0, by decide⟩ : Fin 64).val + 32 ≤ (⟨63, by decide⟩ : Fin 64).val := by decide
    simp only [hle, ↓reduceIte, ratPow_one_base]
    have h1 : (⟨63, by decide⟩ : Fin 64).val - (⟨0, by decide⟩ : Fin 64).val - 1 = 62 := rfl
    have h2 : (32 : Nat) - 1 = 31 := rfl
    rw [h1, h2, choose_62_31]
    grind
  have h64_2 : matPow (alignedL 64 2) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ =
      ratPow 2 32 * 465428353255261088 := by
    rw [alignedL_pow_entry 64 2 32 (by decide)]
    have hle : (⟨0, by decide⟩ : Fin 64).val + 32 ≤ (⟨63, by decide⟩ : Fin 64).val := by decide
    simp only [hle, ↓reduceIte]
    have h1 : (⟨63, by decide⟩ : Fin 64).val - (⟨0, by decide⟩ : Fin 64).val - 1 = 62 := rfl
    have h2 : (32 : Nat) - 1 = 31 := rfl
    rw [h1, h2, choose_62_31]
    rfl
  refine ⟨fun C β k hk i j hle => by rw [alignedL_pow_entry C β k hk i j]; simp [hle],
    h16, h64_1, h64_2, ?_⟩
  rw [h64_2, ratPow_two_32]
  grind

end DeltanetWyStability
