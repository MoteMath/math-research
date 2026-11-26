import ArxFibonacciIsospectrality

open ArxFibonacciIsospectrality

namespace ArxFibonacciChallenge

theorem xor_add_pow_two_mod (r y c : Nat) :
    ((y + 2 ^ r) ^^^ c) % 2 ^ (r + 2) =
      ((y ^^^ c) + (if c.testBit r then 3 else 1) * 2 ^ r) % 2 ^ (r + 2) :=
  ArxFibonacciIsospectrality.xor_add_pow_two_mod r y c

theorem arxFibStep_fixed_point_iff (c m x y : Nat) (hm : 1 ≤ m)
    (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    arxFibStep c m (x, y) = (x, y) ↔ x = c % 2 ^ m ∧ y = c % 2 ^ m :=
  ArxFibonacciIsospectrality.arxFibStep_fixed_point_iff c m x y hm hx hy

theorem arxFibStep_exact_minPeriod (c m x y r0 : Nat)
    (hm : 1 ≤ m) (hx : x < 2 ^ m) (hy : y < 2 ^ m) (hr0 : r0 < m)
    (hmatch : x % 2 ^ r0 = c % 2 ^ r0 ∧ y % 2 ^ r0 = c % 2 ^ r0)
    (hdiff : ¬(x % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1) ∧ y % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1))) :
    IsMinPeriod (arxFibStep c m) (x, y) (3 * 2 ^ (m - 1 - r0)) :=
  ArxFibonacciIsospectrality.arxFibStep_exact_minPeriod c m x y r0 hm hx hy hr0 hmatch hdiff

theorem arxFibStep_isospectral_bijection (c m x y L : Nat)
    (hm : 1 ≤ m) (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    IsMinPeriod (arxFibStep c m) (x, y) L ↔
      IsMinPeriod (arxFibStep 0 m) (x ^^^ (c % 2 ^ m), y ^^^ (c % 2 ^ m)) L :=
  ArxFibonacciIsospectrality.arxFibStep_isospectral_bijection c m x y L hm hx hy

theorem arxFibStep3_breaks_isospectrality :
    (∀ x y : Nat, x < 4 → y < 4 → iter (arxFibStep3 1 2) 3 (x, y) = (x, y)) ∧
    IsMinPeriod (arxFibStep3 0 2) (0, 1) 6 :=
  ArxFibonacciIsospectrality.arxFibStep3_breaks_isospectrality

end ArxFibonacciChallenge
