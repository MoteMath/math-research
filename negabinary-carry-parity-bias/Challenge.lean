import Defs

namespace NegabinaryCarryParityBias

/-- **Theorem 1 — Exact 3-State Negabinary Transfer Recurrence:**
For all bit-widths `w` and addends `q`, stepping the bit-width from `w` to `w + 1`
acts on `(S_w(m, 0), S_w(m, +1), S_w(m, -1))` by exact integer transfer matrices
`T_0` (for `m = 2q`) and `T_1` (for `m = 2q + 1`). -/
theorem negabinParitySum_step (w q : Nat) :
    (negabinParitySum (w + 1) (2 * q) .zero = 2 * negabinParitySum w q .zero ∧
     negabinParitySum (w + 1) (2 * q) .pos =
       negabinParitySum w q .zero - negabinParitySum w q .neg ∧
     negabinParitySum (w + 1) (2 * q) .neg =
       negabinParitySum w q .zero - negabinParitySum w q .pos) ∧
    (negabinParitySum (w + 1) (2 * q + 1) .zero =
       negabinParitySum w q .zero - negabinParitySum w q .neg ∧
     negabinParitySum (w + 1) (2 * q + 1) .pos = -2 * negabinParitySum w q .neg ∧
     negabinParitySum (w + 1) (2 * q + 1) .neg = 2 * negabinParitySum w q .zero) := by
  sorry

/-- **Theorem 2 — Exact Zero-Addend Jacobsthal Law & Constant Carry Gap:**
For all `w : Nat`, the zero-addend negabinary carry-parity sums satisfy
`S_w(0, 0) = 2^w`, `S_w(0, +1) = J_w + 1`, `S_w(0, -1) = J_w - 1`,
`3 * J_w = 2^w - (-1)^w`, and the topological gap `S_w(0, +1) - S_w(0, -1) = 2`. -/
theorem negabinParitySum_zero (w : Nat) :
    negabinParitySum w 0 .zero = (2 ^ w : Int) ∧
    negabinParitySum w 0 .pos = jacobsthal w + 1 ∧
    negabinParitySum w 0 .neg = jacobsthal w - 1 ∧
    3 * jacobsthal w = (2 ^ w : Int) - (-1 : Int) ^ w ∧
    negabinParitySum w 0 .pos - negabinParitySum w 0 .neg = 2 := by
  sorry

/-- **Theorem 3 — Universal Exact Spectral Decomposition (all `m, k : Nat`):**
For EVERY integer `m` and EVERY excess width `k ≥ 0`, `3 * S_{bitLen m + k}(m, c)`
decomposes identically into an exponential bias mode `b * 2^k`, a period-2
oscillation `o * (-1)^k`, and a constant offset `3 * d`, given by `negabinSpec m`. -/
theorem negabinParitySum_spectral (m k : Nat) :
    3 * negabinParitySum (bitLen m + k) m .zero =
      (negabinSpec m).1.1 * (2 ^ k : Int) + (negabinSpec m).2.1.1 * (-1 : Int) ^ k +
        3 * (negabinSpec m).2.2.1 ∧
    3 * negabinParitySum (bitLen m + k) m .pos =
      (negabinSpec m).1.2.1 * (2 ^ k : Int) + (negabinSpec m).2.1.2.1 * (-1 : Int) ^ k +
        3 * (negabinSpec m).2.2.2.1 ∧
    3 * negabinParitySum (bitLen m + k) m .neg =
      (negabinSpec m).1.2.2 * (2 ^ k : Int) + (negabinSpec m).2.1.2.2 * (-1 : Int) ^ k +
        3 * (negabinSpec m).2.2.2.2 := by
  sorry

/-- **Theorem 4 — Universal `±1/3` Negabinary Extremal Barrier:**
For EVERY `m ≥ 1`, the scaled asymptotic bias `b_0(m)` satisfies
`-2^(bitLen m) ≤ b_0(m) ≤ 2^(bitLen m)`, i.e., `|β_{-2}(m)| ≤ 1/3`. -/
theorem negabinBias_abs_le_one_third (m : Nat) (hm : 1 ≤ m) :
    -(2 ^ bitLen m : Int) ≤ (negabinSpec m).1.1 ∧
    (negabinSpec m).1.1 ≤ (2 ^ bitLen m : Int) := by
  sorry

/-- **Theorem 5 — Complete Classification of All `+1/3` Maximizers:**
Among all positive integers `m ≥ 1`, the asymptotic negabinary carry-parity bias attains
`+1/3` (`b_0(m) = 2^(bitLen m)`) IF AND ONLY IF `m = 2^k` for some `k : Nat`. -/
theorem negabinBias_eq_pos_one_third_iff (m : Nat) (hm : 1 ≤ m) :
    (negabinSpec m).1.1 = (2 ^ bitLen m : Int) ↔ ∃ k : Nat, m = 2 ^ k := by
  sorry

/-- **Theorem 6 — Complete Classification of All `-1/3` Minimizers:**
Among all positive integers `m ≥ 1`, the asymptotic negabinary carry-parity bias attains
`-1/3` (`b_0(m) = -2^(bitLen m)`) IF AND ONLY IF `m ∈ {3 * 2^k, 7 * 2^k, 13 * 2^k}`. -/
theorem negabinBias_eq_neg_one_third_iff (m : Nat) (hm : 1 ≤ m) :
    (negabinSpec m).1.1 = -(2 ^ bitLen m : Int) ↔
      ∃ k : Nat, m = 3 * 2 ^ k ∨ m = 7 * 2 ^ k ∨ m = 13 * 2 ^ k := by
  sorry

/-- **Theorem 7 — Infinite Zero-Bias Kernel & Exact Period-2 Collapse:**
For all `r, k : Nat`, the constants `m ∈ {5 * 2^r, 9 * 2^r, 15 * 2^r}` lie in the
exact zero-bias kernel (`b_0(m) = 0`), collapsing the exponential sum `S_w(m, 0)` to
a bounded period-2 oscillation for ALL `k ≥ 0`. -/
theorem negabinZeroBias_bounded_family (r k : Nat) :
    (negabinSpec (5 * 2 ^ r)).1.1 = 0 ∧
    negabinParitySum (bitLen (5 * 2 ^ r) + k) (5 * 2 ^ r) .zero =
      (2 ^ r : Int) * (3 + (-1 : Int) ^ k) ∧
    (negabinSpec (9 * 2 ^ r)).1.1 = 0 ∧
    negabinParitySum (bitLen (9 * 2 ^ r) + k) (9 * 2 ^ r) .zero =
      (2 ^ r : Int) * (3 + (-1 : Int) ^ k) ∧
    (negabinSpec (15 * 2 ^ r)).1.1 = 0 ∧
    negabinParitySum (bitLen (15 * 2 ^ r) + k) (15 * 2 ^ r) .zero =
      -(2 ^ r : Int) * (3 + (-1 : Int) ^ k) := by
  sorry

/-- **Theorem 8 — Universal Exact Standard-Binary (Base `+2`) Spectral Decomposition:**
For EVERY `m, k : Nat` and carry `c ∈ {0, 1}`, `3 * S^{+2}_{bitLen m + k}(m, c)`
decomposes identically into `g * 2^k + u * (-1)^k` (with zero constant mode!). -/
theorem base2ParitySum_spectral (m k : Nat) :
    3 * base2ParitySum (bitLen m + k) m .zero =
      (base2Spec m).1.1 * (2 ^ k : Int) + (base2Spec m).2.1 * (-1 : Int) ^ k ∧
    3 * base2ParitySum (bitLen m + k) m .one =
      (base2Spec m).1.2 * (2 ^ k : Int) + (base2Spec m).2.2 * (-1 : Int) ^ k := by
  sorry

/-- **Theorem 9 — Base-`(+2)` Asymmetric `(-1/9, +1/3]` Barrier & Sharp Infimum Family:**
Unlike negabinary (`[-1/3, +1/3]`), standard base-`(+2)` carry-parity bias is STRICTLY
trapped inside `(-1/9, +1/3]` for ALL `m ≥ 1`:
`-2^(bitLen m) < 3 * g_0(m) ≤ 3 * 2^(bitLen m)`, NEVER attaining `-1/9`,
while the explicit family `m_r = 3 * 2^(2r + 1) - 1` approaches `-1/9` from above:
`3 * g_0(m_r) = -2^(bitLen m_r) + 8` (i.e., `β_{+2}(m_r) = -1/9 + 1 / (9 * 4^r)`). -/
theorem base2Bias_asymmetric_barrier :
    (∀ m : Nat, 1 ≤ m →
      -(2 ^ bitLen m : Int) < 3 * (base2Spec m).1.1 ∧
      (base2Spec m).1.1 ≤ (2 ^ bitLen m : Int)) ∧
    (∀ r : Nat,
      let mr := 3 * 2 ^ (2 * r + 1) - 1
      bitLen mr = 2 * r + 3 ∧
      3 * (base2Spec mr).1.1 = -(2 ^ bitLen mr : Int) + 8) := by
  sorry

/-- **Theorem 10 — Complete Classification of Base-`(+2)` `+1/3` Maximizers:**
Among all positive integers `m ≥ 1`, the standard binary carry-parity bias attains
`+1/3` (`g_0(m) = 2^(bitLen m)`) IF AND ONLY IF `m ∈ {2^k, 3 * 2^k}`. -/
theorem base2Bias_eq_pos_one_third_iff (m : Nat) (hm : 1 ≤ m) :
    (base2Spec m).1.1 = (2 ^ bitLen m : Int) ↔ ∃ k : Nat, m = 2 ^ k ∨ m = 3 * 2 ^ k := by
  sorry

end NegabinaryCarryParityBias
