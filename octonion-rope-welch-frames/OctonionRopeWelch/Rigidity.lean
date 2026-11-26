/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OctonionRopeWelch.Defs

/-!
# Theorem 1: 4D Power-of-2 Quaternion Rigidity Obstruction

Proves:
1. Mod-8 4-square parity descent: for ALL `r ≥ 3` and ALL `a b c d : Int`,
   `a^2 + b^2 + c^2 + d^2 = 2^r → 2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d` (zero primitive solutions!).
2. Universal structural rigidity (`r_4(2^r) = 24`): for ALL `r ≥ 1`, every integer solution to
   `a^2 + b^2 + c^2 + d^2 = 2^r` is `2^((r - 1) / 2)` times an element of `baseHurwitz2` (for
   odd `r`) or `baseHurwitz4` (for even `r`), both of which have exact cardinality 24 with no
   duplicates.
-/

namespace OctonionRopeWelch

private theorem sq_mod8_cases (x : Int) :
    (x * x) % 8 = 0 ∨ (x * x) % 8 = 1 ∨ (x * x) % 8 = 4 := by
  have h : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
           x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  have hmul : (x * x) % 8 = ((x % 8) * (x % 8)) % 8 := by rw [Int.mul_emod]
  rw [hmul]
  rcases h with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

private theorem even_of_sq_mod8_ne_one (x : Int) (h : (x * x) % 8 ≠ 1) : 2 ∣ x := by
  have h8 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
            x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  have hmul : (x * x) % 8 = ((x % 8) * (x % 8)) % 8 := by rw [Int.mul_emod]
  rw [hmul] at h
  rcases h8 with h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8
  · exact ⟨x / 2, by omega⟩
  · rw [h8] at h; contradiction
  · exact ⟨x / 2, by omega⟩
  · rw [h8] at h; contradiction
  · exact ⟨x / 2, by omega⟩
  · rw [h8] at h; contradiction
  · exact ⟨x / 2, by omega⟩
  · rw [h8] at h; contradiction

private theorem pow2_mod8_eq_zero {r : Nat} (hr : 3 ≤ r) : ((2 : Int) ^ r) % 8 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  rw [Int.pow_add]
  have h23 : (2 : Int) ^ 3 = 8 := by decide
  rw [h23]
  omega

/-- Mod-8 4-square parity descent: if `a^2 + b^2 + c^2 + d^2 = 2^r` with `r ≥ 3`,
    then all four integers are even (zero primitive solutions). -/
theorem four_sq_pow2_all_even (r : Nat) (hr : 3 ≤ r) (a b c d : Int)
    (heq : a * a + b * b + c * c + d * d = (2 : Int) ^ r) :
    2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d := by
  have hsum : (a * a + b * b + c * c + d * d) % 8 = 0 := by
    rw [heq]; exact pow2_mod8_eq_zero hr
  have ha := sq_mod8_cases a
  have hb := sq_mod8_cases b
  have hc := sq_mod8_cases c
  have hd := sq_mod8_cases d
  have hne : (a * a) % 8 ≠ 1 ∧ (b * b) % 8 ≠ 1 ∧ (c * c) % 8 ≠ 1 ∧ (d * d) % 8 ≠ 1 := by
    omega
  exact ⟨even_of_sq_mod8_ne_one a hne.1,
         even_of_sq_mod8_ne_one b hne.2.1,
         even_of_sq_mod8_ne_one c hne.2.2.1,
         even_of_sq_mod8_ne_one d hne.2.2.2⟩

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h => exact Int.mul_nonneg_of_nonpos_of_nonpos h h

private theorem int_bounds_of_sq_le_two (x : Int) (h : x * x ≤ 2) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  have hlt : ¬ (2 ≤ x) := by
    intro h2
    have h4 : 4 ≤ x * x := by
      have : 2 * 2 ≤ x * x := Int.mul_le_mul h2 h2 (by decide) (by omega)
      omega
    omega
  have hgt : ¬ (x ≤ -2) := by
    intro h2
    have h4 : 4 ≤ (-x) * (-x) := by
      have h2' : 2 ≤ -x := by omega
      have : 2 * 2 ≤ (-x) * (-x) := Int.mul_le_mul h2' h2' (by decide) (by omega)
      omega
    have heq : (-x) * (-x) = x * x := Int.neg_mul_neg x x
    omega
  omega

private theorem int_bounds_of_sq_le_four (x : Int) (h : x * x ≤ 4) :
    x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by
  have hlt : ¬ (3 ≤ x) := by
    intro h3
    have h9 : 9 ≤ x * x := by
      have : 3 * 3 ≤ x * x := Int.mul_le_mul h3 h3 (by decide) (by omega)
      omega
    omega
  have hgt : ¬ (x ≤ -3) := by
    intro h3
    have h9 : 9 ≤ (-x) * (-x) := by
      have h3' : 3 ≤ -x := by omega
      have : 3 * 3 ≤ (-x) * (-x) := Int.mul_le_mul h3' h3' (by decide) (by omega)
      omega
    have heq : (-x) * (-x) = x * x := Int.neg_mul_neg x x
    omega
  omega

private theorem mem_baseHurwitz2_of_sq_sum_eq_two (a b c d : Int)
    (h : a * a + b * b + c * c + d * d = 2) :
    (a, b, c, d) ∈ baseHurwitz2 := by
  have ha0 := int_sq_nonneg a; have hb0 := int_sq_nonneg b
  have hc0 := int_sq_nonneg c; have hd0 := int_sq_nonneg d
  have ha := int_bounds_of_sq_le_two a (by omega)
  have hb := int_bounds_of_sq_le_two b (by omega)
  have hc := int_bounds_of_sq_le_two c (by omega)
  have hd := int_bounds_of_sq_le_two d (by omega)
  rcases ha with rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl <;>
  rcases hd with rfl | rfl | rfl <;>
  first | contradiction | (simp only [baseHurwitz2]; decide)

private theorem mem_baseHurwitz4_of_sq_sum_eq_four (a b c d : Int)
    (h : a * a + b * b + c * c + d * d = 4) :
    (a, b, c, d) ∈ baseHurwitz4 := by
  have ha0 := int_sq_nonneg a; have hb0 := int_sq_nonneg b
  have hc0 := int_sq_nonneg c; have hd0 := int_sq_nonneg d
  have ha := int_bounds_of_sq_le_four a (by omega)
  have hb := int_bounds_of_sq_le_four b (by omega)
  have hc := int_bounds_of_sq_le_four c (by omega)
  have hd := int_bounds_of_sq_le_four d (by omega)
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  rcases hd with rfl | rfl | rfl | rfl | rfl <;>
  first | contradiction | (simp only [baseHurwitz4]; decide)

/-- Universal 2-adic descent classification: for EVERY `r ≥ 1`, every integer solution to
    `a^2 + b^2 + c^2 + d^2 = 2^r` is `2^((r - 1) / 2)` times an element of `baseHurwitz2`
    (if `r` is odd) or `baseHurwitz4` (if `r` is even). -/
theorem four_sq_pow2_classification (r : Nat) (hr : 1 ≤ r) :
    ∀ a b c d : Int, a * a + b * b + c * c + d * d = (2 : Int) ^ r →
      ∃ a0 b0 c0 d0 : Int,
        a = (2 : Int) ^ ((r - 1) / 2) * a0 ∧
        b = (2 : Int) ^ ((r - 1) / 2) * b0 ∧
        c = (2 : Int) ^ ((r - 1) / 2) * c0 ∧
        d = (2 : Int) ^ ((r - 1) / 2) * d0 ∧
        (if r % 2 = 1 then (a0, b0, c0, d0) ∈ baseHurwitz2
         else (a0, b0, c0, d0) ∈ baseHurwitz4) := by
  match r with
  | 0 => omega
  | 1 =>
    intro a b c d heq
    refine ⟨a, b, c, d, by omega, by omega, by omega, by omega, ?_⟩
    simp only [Nat.mod_eq_of_lt (by decide : 1 < 2), ite_true]
    exact mem_baseHurwitz2_of_sq_sum_eq_two a b c d heq
  | 2 =>
    intro a b c d heq
    refine ⟨a, b, c, d, by omega, by omega, by omega, by omega, ?_⟩
    simp only [show (2 : Nat) % 2 = 0 from rfl, show ¬ ((0 : Nat) = 1) from by decide, ite_false]
    exact mem_baseHurwitz4_of_sq_sum_eq_four a b c d heq
  | r' + 3 =>
    intro a b c d heq
    have heven := four_sq_pow2_all_even (r' + 3) (by omega) a b c d heq
    rcases heven with ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, ⟨c1, hc1⟩, ⟨d1, hd1⟩⟩
    have hpow : (2 : Int) ^ (r' + 3) = 4 * (2 : Int) ^ (r' + 1) := by
      have h1 : r' + 3 = (r' + 1) + 2 := by omega
      rw [h1, Int.pow_add]
      have h22 : (2 : Int) ^ 2 = 4 := by decide
      rw [h22, Int.mul_comm]
    have hsum1 : a1 * a1 + b1 * b1 + c1 * c1 + d1 * d1 = (2 : Int) ^ (r' + 1) := by
      rw [ha1, hb1, hc1, hd1, hpow] at heq
      have hmul :
          (2 * a1) * (2 * a1) + (2 * b1) * (2 * b1) + (2 * c1) * (2 * c1) + (2 * d1) * (2 * d1) =
          4 * (a1 * a1 + b1 * b1 + c1 * c1 + d1 * d1) := by
        have e1 : (2 * a1) * (2 * a1) = 4 * (a1 * a1) := by
          rw [Int.mul_assoc, Int.mul_left_comm a1 2 a1, ← Int.mul_assoc]; rfl
        have e2 : (2 * b1) * (2 * b1) = 4 * (b1 * b1) := by
          rw [Int.mul_assoc, Int.mul_left_comm b1 2 b1, ← Int.mul_assoc]; rfl
        have e3 : (2 * c1) * (2 * c1) = 4 * (c1 * c1) := by
          rw [Int.mul_assoc, Int.mul_left_comm c1 2 c1, ← Int.mul_assoc]; rfl
        have e4 : (2 * d1) * (2 * d1) = 4 * (d1 * d1) := by
          rw [Int.mul_assoc, Int.mul_left_comm d1 2 d1, ← Int.mul_assoc]; rfl
        rw [e1, e2, e3, e4]
        simp only [Int.mul_add]
      rw [hmul] at heq
      omega
    have ih := four_sq_pow2_classification (r' + 1) (by omega) a1 b1 c1 d1 hsum1
    rcases ih with ⟨a0, b0, c0, d0, ha0, hb0, hc0, hd0, hmem⟩
    have hdiv : ((r' + 3 - 1) / 2) = ((r' + 1 - 1) / 2) + 1 := by omega
    have hmod : (r' + 3) % 2 = (r' + 1) % 2 := by omega
    have hpow2 : (2 : Int) ^ ((r' + 3 - 1) / 2) = 2 * (2 : Int) ^ ((r' + 1 - 1) / 2) := by
      rw [hdiv, Int.pow_succ, Int.mul_comm]
    refine ⟨a0, b0, c0, d0, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha1, ha0, hpow2, Int.mul_assoc]
    · rw [hb1, hb0, hpow2, Int.mul_assoc]
    · rw [hc1, hc0, hpow2, Int.mul_assoc]
    · rw [hd1, hd0, hpow2, Int.mul_assoc]
    · rw [hmod]; exact hmem
termination_by r

/-- Headline Theorem 1: 4D Power-of-2 Quaternion Rigidity Obstruction.
    1. Zero primitive solutions for ALL `r ≥ 3` (`2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d`).
    2. Universal `r_4(2^r) = 24` structural classification for ALL `r ≥ 1`, with exact
       cardinality `24`, duplicate-free base lists, and every base element satisfying the
       norm equation. -/
theorem quaternion_pow2_rigidity_obstruction :
    (∀ (r : Nat), 3 ≤ r → ∀ (a b c d : Int),
      a * a + b * b + c * c + d * d = (2 : Int) ^ r →
      2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d) ∧
    (∀ (r : Nat), 1 ≤ r → ∀ (a b c d : Int),
      a * a + b * b + c * c + d * d = (2 : Int) ^ r →
      ∃ a0 b0 c0 d0 : Int,
        a = (2 : Int) ^ ((r - 1) / 2) * a0 ∧
        b = (2 : Int) ^ ((r - 1) / 2) * b0 ∧
        c = (2 : Int) ^ ((r - 1) / 2) * c0 ∧
        d = (2 : Int) ^ ((r - 1) / 2) * d0 ∧
        (if r % 2 = 1 then (a0, b0, c0, d0) ∈ baseHurwitz2
         else (a0, b0, c0, d0) ∈ baseHurwitz4)) ∧
    baseHurwitz2.length = 24 ∧
    baseHurwitz2.Nodup ∧
    (∀ q ∈ baseHurwitz2, q.1 * q.1 + q.2.1 * q.2.1 + q.2.2.1 * q.2.2.1 + q.2.2.2 * q.2.2.2 = 2) ∧
    baseHurwitz4.length = 24 ∧
    baseHurwitz4.Nodup ∧
    (∀ q ∈ baseHurwitz4, q.1 * q.1 + q.2.1 * q.2.1 + q.2.2.1 * q.2.2.1 + q.2.2.2 * q.2.2.2 = 4) := by
  refine ⟨four_sq_pow2_all_even, four_sq_pow2_classification, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

end OctonionRopeWelch
