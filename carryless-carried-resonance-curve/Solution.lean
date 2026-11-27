/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarrylessCarriedResonanceCurve

/-!
# Verified Solutions (`carryless-carried-resonance-curve`)
-/

namespace CarrylessCarriedResonanceCurveChallenge

open SiliconPolyBridge

theorem henselLift_iff_dvd {F : Nat → Int} {L : Nat} (hF : ScaledIsometry F L)
    (n t : Nat) :
    ((2 ^ (L + t) : Nat) : Int) ∣ F n ↔ n % 2 ^ t = henselLift F L t :=
  SiliconPolyBridge.henselLift_iff_dvd hF n t

theorem regime_I_carried_dominated {a r e m : Nat} (hr : 2 ≤ r) (he : 1 ≤ e)
    (ha : exactPow2 r ((a : Int) - 1)) (hm : m % 2 = 1) :
    exactPow2 (r + e) (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) :=
  SiliconPolyBridge.regime_I_carried_dominated hr he ha hm

theorem regime_II_carryless_dominated {a s e m : Nat} (hs : 2 ≤ s) (he : 1 ≤ e)
    (ha : exactPow2 s ((a : Int) + 1)) (hm : m % 2 = 1) (hlt : 2 ^ e < s + e) :
    exactPow2 (2 ^ e) (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) :=
  SiliconPolyBridge.regime_II_carryless_dominated hs he ha hm hlt

theorem regime_III_carried_dominated {a s e m : Nat} (hs : 2 ≤ s) (he : 1 ≤ e)
    (ha : exactPow2 s ((a : Int) + 1)) (hm : m % 2 = 1) (hlt : s + e < 2 ^ e) :
    exactPow2 (s + e) (((a ^ (2 ^ e * m) : Nat) : Int) - (clpow a (2 ^ e * m) : Int)) :=
  SiliconPolyBridge.regime_III_carried_dominated hs he ha hm hlt

theorem resonant_bridge_master {a e B : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) :
    (∀ t : Nat, henselLift (F_bridge a e B) (2 ^ e + 1) t < 2 ^ t ∧
      ((2 ^ (2 ^ e + 1 + t) : Nat) : Int) ∣
        F_bridge a e B (henselLift (F_bridge a e B) (2 ^ e + 1) t)) ∧
    (∀ n t : Nat, ((2 ^ (2 ^ e + 1 + t) : Nat) : Int) ∣ F_bridge a e B n ↔
      n % 2 ^ t = henselLift (F_bridge a e B) (2 ^ e + 1) t) ∧
    (∀ N : Nat, ∃ t : Nat, N < henselLift (F_bridge a e B) (2 ^ e + 1) t) :=
  SiliconPolyBridge.resonant_bridge_master he ha hB

theorem resonant_root_invariance_below_threshold {a e B : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) (hBlt : B < 2 ^ (2 ^ e)) :
    ∀ t : Nat, henselLift (F_bridge a e B) (2 ^ e + 1) t =
               henselLift (F_bridge a e 1) (2 ^ e + 1) t :=
  SiliconPolyBridge.resonant_root_invariance_below_threshold he ha hB hBlt

theorem resonant_bit_root_shift_law {a e B : Nat} (he : 2 ≤ e)
    (ha : exactPow2 (2 ^ e - e) ((a : Int) + 1)) (hB : B % 2 = 1) :
    henselLift (F_bridge a e B) (2 ^ e + 1) 1 =
      (henselLift (F_bridge a e 1) (2 ^ e + 1) 1) ^^^ (if B.testBit (2 ^ e) then 1 else 0) :=
  SiliconPolyBridge.resonant_bit_root_shift_law he ha hB

theorem resonance_curve_infinitely_inhabited (e q : Nat) :
    exactPow2 (2 ^ e - e) ((((2 * q + 1) * 2 ^ (2 ^ e - e) - 1 : Nat) : Int) + 1) :=
  SiliconPolyBridge.resonance_curve_infinitely_inhabited e q

end CarrylessCarriedResonanceCurveChallenge
