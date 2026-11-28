import Defs

namespace ClmulCarryDynamics

/-- Carry-less multiplication distributes over bitwise XOR in its second argument. -/
theorem clmul_xor (a x y : Nat) :
    clmul a (x ^^^ y) = clmul a x ^^^ clmul a y := by
  sorry

/-- For any odd multiplier `a`, `x ↦ clmul a x mod 2^w` is injective on `{0, ..., 2^w - 1}`. -/
theorem clmul_mod_injective_of_odd (w a : Nat) (ha : a % 2 = 1) :
    ∀ x y, x < 2 ^ w → y < 2 ^ w →
      clmul a x % 2 ^ w = clmul a y % 2 ^ w → x = y := by
  sorry

/-- **Carryless–Carried Hybrid Hull–Dobell Theorem (all `w ≥ 2`):**
`x ↦ (clmul a x + b) mod 2^w` is a single cycle of length `2^w` if and only if
`a ≡ 1 (mod 4)` and `b ≡ 1 (mod 2)`. -/
theorem hybrid_hull_dobell_iff (w a b : Nat) (hw : 2 ≤ w) :
    IsFullCycle (hybridStep a b w) (2 ^ w) ↔ a % 4 = 1 ∧ b % 2 = 1 := by
  sorry

/-- **Exact Carry-Vector Rotation Reduction (all `w ≥ 1`):**
Adding `1` to `kaprekarStep x` turns the bitwise carry-vector + rotation formula
into left-shifting `x ||| (x + 1)` and injecting `x.msb` at bit `0`. -/
theorem kaprekarStep_add_one_eq {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    kaprekarStep x + 1#w =
      (((x ||| (x + 1#w)) <<< 1) ||| (if x.msb then 1#w else 0#w)) := by
  sorry

/-- **Exact Step-`t` Image Characterization (all `w ≥ 3`, `1 ≤ t ≤ w - 1`):**
A bitvector `y : BitVec w` lies in the `t`-fold image of `kaprekarStep` if and only if
bits `1, ..., t` of `y + 1#w` are all `1`. -/
theorem kaprekarStep_image_char {w : Nat} (hw : 3 ≤ w) (t : Nat)
    (ht1 : 1 ≤ t) (ht2 : t ≤ w - 1) (y : BitVec w) :
    (∃ x : BitVec w, iterate kaprekarStep t x = y) ↔
      (∀ i, 1 ≤ i → i ≤ t → (y + 1#w).getLsbD i = true) := by
  sorry

/-- **Exact `w`-Step Universal Kaprekar Sink & Sharp Diameter `w` (all `w ≥ 3`):**
Every `x : BitVec w` collapses to the unique fixed point `~~~1#w` (`2^w - 2`)
in at most `w` steps, and `0#w` has not yet reached `~~~1#w` at step `w - 1`. -/
theorem kaprekarStep_universal_sink {w : Nat} (hw : 3 ≤ w) :
    (∀ x : BitVec w, iterate kaprekarStep w x = ~~~1#w) ∧
    iterate kaprekarStep (w - 1) 0#w ≠ ~~~1#w ∧
    kaprekarStep (~~~1#w) = ~~~1#w := by
  sorry

/-- **Sharpness at `w = 2`:** At width `2`, `kaprekarStep` has two distinct fixed points
`1#2` and `2#2`, so the universal sink theorem fails below `w = 3`. -/
theorem kaprekarStep_w2_sharpness :
    kaprekarStep 1#2 = 1#2 ∧ kaprekarStep 2#2 = 2#2 ∧ (1#2 : BitVec 2) ≠ 2#2 := by
  sorry

/-- **Zero-Carry `m = 3` Fibbinary Characterization:**
Carried and carry-less multiplication by `3` coincide on `x` if and only if
`x` has no adjacent `1`-bits (`x &&& (2 * x) = 0`). -/
theorem carried_eq_clmul3_iff (x : Nat) :
    3 * x = clmul 3 x ↔ (x &&& (2 * x)) = 0 := by
  sorry

/-- **Exact Zero-Carry `m = 3` Fibonacci Law (all `w : Nat`):**
The number of `x < 2^w` satisfying `3 * x = clmul 3 x` is `fib (w + 2)`. -/
theorem zeroCarry3Count_eq_fib (w : Nat) :
    zeroCarry3Count w = fib (w + 2) := by
  sorry

/-- **Exact `3^⌊w/2⌋` Carried-vs-Carryless Parity Correlation Law (all `w ≥ 1`):**
The signed parity correlation `∑_{x < 2^w} (-1)^(popcount (3*x) + popcount (clmul 3 x))`
equals `4 * 3^(w/2 - 1)` for even `w ≥ 2` and `2 * 3^(w/2)` for odd `w ≥ 1`. -/
theorem carried_clmul3_parity_sum (w : Nat) (hw : 1 ≤ w) :
    clmul3ParitySum w =
      if w % 2 = 0 then 4 * (3 : Int) ^ (w / 2 - 1) else 2 * (3 : Int) ^ (w / 2) := by
  sorry

end ClmulCarryDynamics
