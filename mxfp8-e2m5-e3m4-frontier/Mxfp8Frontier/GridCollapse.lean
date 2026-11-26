/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp8Frontier.RatOrder

/-!
# Theorem 1: Exact `E1M6_FN ≡ INT8` (`E0M7`) Grid Collapse & 5-Format Microscaling Family

Proves:
1. Universal bit-width collapse: for any mantissa width `m_bits : Nat` and any code
   `c < 2 ^ (m_bits + 1)`, IEEE-subnormal `E1 M_{m_bits}` decodes identically to integer
   `E0 M_{m_bits + 1}` (`fp8MagInt 1 m_bits c = fp8MagInt 0 (m_bits + 1) c = c`).
2. Exact 8-bit specialization (`m_bits = 6`): for all 7-bit unsigned codes `c < 128`,
   `E1M6_FN` and `E0M7` (`INT8`) have bit-for-bit identical integer magnitudes `0..127`
   and identical normalized rational grid points `c / 127`.
3. Exact maximum dynamic range `M_int` for all six 8-bit formats, collapsing `E1M6_FN`
   onto `INT8` and establishing the strictly increasing 5-format chain
   `INT8 (127) < E2M5_FN (252) < E3M4_FN (1,984) < E4M3_OCP (229,376) < E5M2_IEEE (3,758,096,384)`.
-/

namespace Mxfp8Frontier

/-- Universal 1-exponent-bit IEEE-subnormal collapse: for ANY mantissa width `m_bits`
    and ANY `(m_bits + 1)`-bit unsigned code `c < 2 ^ (m_bits + 1)`, `E1 M_{m_bits}`
    decodes identically to the linear integer grid `c`. -/
theorem fp8MagInt_one_exp_eq_id (m_bits c : Nat) (hc : c < 2 ^ (m_bits + 1)) :
    fp8MagInt 1 m_bits c = c := by
  unfold fp8MagInt
  simp only [Nat.one_ne_zero, ↓reduceIte]
  have hpow : 2 ^ (m_bits + 1) = 2 ^ m_bits * 2 := Nat.pow_succ 2 m_bits
  have hpos : 0 < 2 ^ m_bits := Nat.pow_pos (by decide)
  by_cases hlt : c < 2 ^ m_bits
  · have hdiv : c / 2 ^ m_bits = 0 := Nat.div_eq_of_lt hlt
    have hmod : c % 2 ^ m_bits = c := Nat.mod_eq_of_lt hlt
    simp [hdiv, hmod]
  · have hge : 2 ^ m_bits ≤ c := Nat.le_of_not_lt hlt
    have hdiv_ge : 1 ≤ c / 2 ^ m_bits := by
      have := Nat.div_le_div_right (c := 2 ^ m_bits) hge
      rw [Nat.div_self hpos] at this
      exact this
    have hdiv_lt : c / 2 ^ m_bits < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      rw [Nat.mul_comm]
      omega
    have hdiv : c / 2 ^ m_bits = 1 := by omega
    have hdm : 2 ^ m_bits * (c / 2 ^ m_bits) + c % 2 ^ m_bits = c := Nat.div_add_mod c (2 ^ m_bits)
    rw [hdiv, Nat.mul_one] at hdm
    simp [hdiv, hdm]

/-- Headline Theorem 1 (`fp8_e1m6_collapse_to_int8_exact`). -/
theorem fp8_e1m6_collapse_to_int8_exact :
    (∀ m_bits c : Nat, c < 2 ^ (m_bits + 1) →
      fp8MagInt 1 m_bits c = fp8MagInt 0 (m_bits + 1) c ∧
      fp8MagInt 1 m_bits c = c) ∧
    (∀ c : Nat, c < 128 →
      fp8MagInt 1 6 c = fp8MagInt 0 7 c ∧
      fp8NormRat 1 6 127 c = fp8NormRat 0 7 127 c) ∧
    (fp8MagInt 0 7 127 = 127 ∧
     fp8MagInt 1 6 127 = 127 ∧
     fp8MagInt 2 5 127 = 252 ∧
     fp8MagInt 3 4 127 = 1984 ∧
     fp8MagInt 4 3 126 = 229376 ∧
     fp8MagInt 5 2 123 = 3758096384) ∧
    (127 < 252 ∧ 252 < 1984 ∧ 1984 < 229376 ∧ 229376 < 3758096384) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m_bits c hc
    have h1 := fp8MagInt_one_exp_eq_id m_bits c hc
    refine ⟨?_, h1⟩
    rw [h1]
    rfl
  · intro c hc
    have h1 := fp8MagInt_one_exp_eq_id 6 c (by omega)
    refine ⟨?_, ?_⟩
    · rw [h1]; rfl
    · unfold fp8NormRat
      rw [h1]
      rfl
  · refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · decide

end Mxfp8Frontier
