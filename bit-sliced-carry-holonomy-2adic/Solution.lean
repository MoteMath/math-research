import BitSlicedCarryHolonomy2adic

namespace BitSlicedCarryHolonomy2adicChallenge

open CarryHolonomyEngine

theorem iter_testBit_eq_holonomy {f : Nat → Nat} (hf : TPerm f) (k x0 L : Nat) :
    (iter f L x0).testBit k = xor (x0.testBit k) (holonomy f k x0 L) :=
  _root_.CarryHolonomyEngine.iter_testBit_eq_holonomy hf k x0 L

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
          decide (Φ y % 2 ^ k + c % 2 ^ k ≥ 2 ^ k))) :=
  _root_.CarryHolonomyEngine.majority_carry_holonomy hΦ c k x0 L hcyc hhol heven

theorem tower_to_min_period {f : Nat → Nat} (hf : TPerm f) (k0 L0 : Nat)
    (hL0 : 0 < L0)
    (hcyc0 : iter f L0 0 % 2 ^ k0 = 0)
    (hmin0 : ∀ r, 0 < r → r < L0 → iter f r 0 % 2 ^ k0 ≠ 0)
    (hhol : ∀ m, holonomy f (k0 + m) 0 (L0 * 2 ^ m) = true)
    (m : Nat) :
    iter f (L0 * 2 ^ m) 0 % 2 ^ (k0 + m) = 0 ∧
    ∀ d, 0 < d → d < L0 * 2 ^ m → iter f d 0 % 2 ^ (k0 + m) ≠ 0 :=
  _root_.CarryHolonomyEngine.tower_to_min_period hf k0 L0 hL0 hcyc0 hmin0 hhol m

theorem grayCarry_ge2_odd_period (s c k : Nat) (hs : 2 ≤ s) (hc : c % 2 = 1) :
    iter (grayCarryStep s c) (2 ^ k) 0 % 2 ^ k = 0 ∧
    ∀ d, 0 < d → d < 2 ^ k → iter (grayCarryStep s c) d 0 % 2 ^ k ≠ 0 :=
  _root_.CarryHolonomyEngine.grayCarry_ge2_odd_period s c k hs hc

theorem quadAnd_v2 (s t c n : Nat) (hs : 1 ≤ s) (hst : s < t) (ht : 3 ≤ t) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (quadAndStep s t c) n 0) = v2 c + v2 n :=
  _root_.CarryHolonomyEngine.quadAnd_v2 s t c n hs hst ht hc hn

theorem affineXor_even_v2 (A c n : Nat) (hApos : A ≠ 0) (hAev : A % 2 = 0) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (affineXorStep A c) n 0) =
      if n % 2 = 1 then v2 c else v2 n + v2 c + v2 A - 1 :=
  _root_.CarryHolonomyEngine.affineXor_even_v2 A c n hApos hAev hc hn

theorem sharpness_affineXor_A0_period2 (c m : Nat) :
    iter (affineXorStep 0 c) (2 * m) 0 = 0 ∧
    iter (affineXorStep 0 c) (2 * m + 1) 0 = c :=
  _root_.CarryHolonomyEngine.sharpness_affineXor_A0_period2 c m

theorem sharpness_carryless_gray_period_collapse :
    iter (carrylessGrayStep 1) 4 0 = 8 ∧
    iter (carrylessGrayStep 1) 4 0 % 8 = 0 ∧
    holonomy (carrylessGrayStep 1) 2 0 4 = false ∧
    v2 (iter (carrylessGrayStep 1) 4 0) = 3 ∧
    v2 (iter (carrylessGrayStep 1) 4 0) ≠ v2 1 + v2 4 :=
  _root_.CarryHolonomyEngine.sharpness_carryless_gray_period_collapse

end BitSlicedCarryHolonomy2adicChallenge
