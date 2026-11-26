import ArxFibonacciIsospectrality.Defs

open ArxFibonacciIsospectrality

namespace ArxFibonacciChallenge

/-- Theorem 1 (Exact finite-level 2-adic perturbation law for `y ↦ y ^^^ c`):
adding `2^r` to `y` before XORing with `c` shifts `y ^^^ c` modulo `2^(r+2)` by
`σ * 2^r` where `σ = 3` if bit `r` of `c` is `1` and `σ = 1` otherwise. -/
theorem xor_add_pow_two_mod (r y c : Nat) :
    ((y + 2 ^ r) ^^^ c) % 2 ^ (r + 2) =
      ((y ^^^ c) + (if c.testBit r then 3 else 1) * 2 ^ r) % 2 ^ (r + 2) := by
  sorry

/-- Theorem 2 (Unique fixed point of `arxFibStep c m` on `{0, ..., 2^m - 1}^2`):
for `m ≥ 1`, `(c % 2^m, c % 2^m)` is the unique fixed point of `G_{c,m}`. -/
theorem arxFibStep_fixed_point_iff (c m x y : Nat) (hm : 1 ≤ m)
    (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    arxFibStep c m (x, y) = (x, y) ↔ x = c % 2 ^ m ∧ y = c % 2 ^ m := by
  sorry

/-- Theorem 3 (Exact closed-form minimal period of every non-fixed state):
if `(x, y)` agrees with `(c, c)` modulo `2^r0` and differs modulo `2^(r0+1)` with `r0 < m`,
then its exact minimal period under `G_{c,m}` is `3 * 2^(m - 1 - r0)`. -/
theorem arxFibStep_exact_minPeriod (c m x y r0 : Nat)
    (hm : 1 ≤ m) (hx : x < 2 ^ m) (hy : y < 2 ^ m) (hr0 : r0 < m)
    (hmatch : x % 2 ^ r0 = c % 2 ^ r0 ∧ y % 2 ^ r0 = c % 2 ^ r0)
    (hdiff : ¬(x % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1) ∧ y % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1))) :
    IsMinPeriod (arxFibStep c m) (x, y) (3 * 2 ^ (m - 1 - r0)) := by
  sorry

/-- Theorem 4 (Exact key-invariant cycle spectrum via period-preserving involution):
for every `m ≥ 1`, every key `c`, every period `L`, and every `(x, y) ∈ {0, ..., 2^m - 1}^2`,
the involution `(x, y) ↦ (x ^^^ (c % 2^m), y ^^^ (c % 2^m))` preserves exact minimal periods
between `G_{c,m}` and unkeyed linear Fibonacci `G_{0,m}`. -/
theorem arxFibStep_isospectral_bijection (c m x y L : Nat)
    (hm : 1 ≤ m) (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    IsMinPeriod (arxFibStep c m) (x, y) L ↔
      IsMinPeriod (arxFibStep 0 m) (x ^^^ (c % 2 ^ m), y ^^^ (c % 2 ^ m)) L := by
  sorry

/-- Theorem 5 (Sharpness contrast witness for `3 * x + (y ^^^ c)`):
changing `1 * x` to `3 * x` destroys key-invariance already at `m = 2`:
for `c = 1` every 2-bit state satisfies `H_{1,2}^3(x, y) = (x, y)` (zero period-6 states),
whereas for `c = 0` the state `(0, 1)` has exact minimal period `6`. -/
theorem arxFibStep3_breaks_isospectrality :
    (∀ x y : Nat, x < 4 → y < 4 → iter (arxFibStep3 1 2) 3 (x, y) = (x, y)) ∧
    IsMinPeriod (arxFibStep3 0 2) (0, 1) 6 := by
  sorry

end ArxFibonacciChallenge
