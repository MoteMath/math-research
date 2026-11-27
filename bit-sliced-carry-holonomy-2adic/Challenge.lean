import BitSlicedCarryHolonomy2adic.Defs

namespace BitSlicedCarryHolonomy2adicChallenge

open CarryHolonomyEngine

/-- **Core Engine Theorem A (`holonomy_lift_step`)**: For any `TPerm f`, any level `k`, and any `L`, the bit `k` of `iter f L x0` is exactly `x0.testBit k ^^ holonomy f k x0 L`! -/
theorem iter_testBit_eq_holonomy {f : Nat → Nat} (hf : TPerm f) (k x0 L : Nat) :
    (iter f L x0).testBit k = xor (x0.testBit k) (holonomy f k x0 L) := by
  sorry

/-- **Core Engine Theorem B1 (`majority_carry_holonomy`)**: For ANY `TPerm Φ`, ANY `c`, and ANY doubled cycle `2L` at level `k+1` (with `L` even): `holonomy (Φ · + c) (k+1) x0 (2*L)` equals the XOR of the twist derivative `β` and the carry-overflow parity over the half-cycle `y_i = iter T i x0 % 2^k`! -/
theorem majority_carry_holonomy {Φ : Nat → Nat} (hΦ : TPerm Φ) (c k x0 L : Nat)
    (hcyc : iter (fun x => Φ x + c) L x0 % 2 ^ k = x0 % 2 ^ k)
    (hhol : holonomy (fun x => Φ x + c) k x0 L = true)
    (heven : L % 2 = 0) :
    holonomy (fun x => Φ x + c) (k + 1) x0 (2 * L) =
      xor
        (xorRange L (fun i =>
          let y := iter (fun x => Φ x + c) i x0 % 2 ^ k
          xor ((Φ y).testBit (k + 1)) ((Φ (y + 2 ^ k)).testBit (k + 1))))
        (xorRange L (fun i =>
          let y := iter (fun x => Φ x + c) i x0 % 2 ^ k
          decide (Φ y % 2 ^ k + c % 2 ^ k ≥ 2 ^ k))) := by
  sorry

/-- **Core Engine Theorem C3 (Exact Minimal Periodicity Mod `2^(k0 + m)`)**: Under the certified doubling tower plus base minimality (`∀ 0 < r < L0, iter f r 0 % 2^k0 ≠ 0`), for EVERY `m : Nat`, `L0 * 2 ^ m` is the **EXACT minimal period** of `iter f · 0` modulo `2 ^ (k0 + m)`! -/
theorem tower_to_min_period {f : Nat → Nat} (hf : TPerm f) (k0 L0 : Nat)
    (hL0 : 0 < L0)
    (hcyc0 : iter f L0 0 % 2 ^ k0 = 0)
    (hmin0 : ∀ r, 0 < r → r < L0 → iter f r 0 % 2 ^ k0 ≠ 0)
    (hhol : ∀ m, holonomy f (k0 + m) 0 (L0 * 2 ^ m) = true)
    (m : Nat) :
    iter f (L0 * 2 ^ m) 0 % 2 ^ (k0 + m) = 0 ∧
    ∀ d, 0 < d → d < L0 * 2 ^ m → iter f d 0 % 2 ^ (k0 + m) ≠ 0 := by
  sorry

/-- **Theorem 1A (Gray-Carry Ergodicity for `s ≥ 2`, odd `c`)**: For ALL `s ≥ 2`, ALL odd `c`, and ALL `k : Nat`, the orbit of `0` modulo `2^k` has exact minimal period `2^k` (stated as: `iter (grayCarryStep s c) (2^k) 0 % 2^k = 0` and no smaller positive `d` returns to `0`). The valuation law `v2 (iter (grayCarryStep s c) n 0) = v2 n` is not part of this statement. -/
theorem grayCarry_ge2_odd_period (s c k : Nat) (hs : 2 ≤ s) (hc : c % 2 = 1) :
    iter (grayCarryStep s c) (2 ^ k) 0 % 2 ^ k = 0 ∧
    ∀ d, 0 < d → d < 2 ^ k → iter (grayCarryStep s c) d 0 % 2 ^ k ≠ 0 := by
  sorry

theorem quadAnd_v2 (s t c n : Nat) (hs : 1 ≤ s) (hst : s < t) (ht : 3 ≤ t) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (quadAndStep s t c) n 0) = v2 c + v2 n := by
  sorry

/-- **Theorem 3B (Affine-XOR Exact Valuation Law for ALL even `A ≥ 2`, ALL `c ≥ 1`, ALL `n ≥ 1`)**: `v2 (iter (affineXorStep A c) n 0) = if n % 2 = 1 then v2 c else v2 n + v2 c + v2 A - 1`! -/
theorem affineXor_even_v2 (A c n : Nat) (hApos : A ≠ 0) (hAev : A % 2 = 0) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (affineXorStep A c) n 0) =
      if n % 2 = 1 then v2 c else v2 n + v2 c + v2 A - 1 := by
  sorry

/-- **Sharpness 2 (`A = 0` in Affine-XOR, i.e. `a_{n+1} = a_n ^^^ c`)**: `A = 0` has zero holonomy at every level: exact period 2 forever (`d_{2m} = 0`, `d_{2m+1} = c`)! -/
theorem sharpness_affineXor_A0_period2 (c m : Nat) :
    iter (affineXorStep 0 c) (2 * m) 0 = 0 ∧
    iter (affineXorStep 0 c) (2 * m + 1) 0 = c := by
  sorry

theorem sharpness_carryless_gray_period_collapse :
    iter (carrylessGrayStep 1) 4 0 = 8 ∧
    iter (carrylessGrayStep 1) 4 0 % 8 = 0 ∧
    holonomy (carrylessGrayStep 1) 2 0 4 = false ∧
    v2 (iter (carrylessGrayStep 1) 4 0) = 3 ∧
    v2 (iter (carrylessGrayStep 1) 4 0) ≠ v2 1 + v2 4 := by
  sorry

end BitSlicedCarryHolonomy2adicChallenge
