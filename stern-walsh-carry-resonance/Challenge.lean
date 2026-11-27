/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SternWalshCarryResonance.Defs

/-!
# Trusted Challenge Statements (`stern-walsh-carry-resonance`)
-/

namespace SternWalshCarryResonanceChallenge

open SternCW

/-- Calkin-Wilf matrix products give the consecutive Stern values `s(2^k + x), s(2^k + x + 1)` at every level `k`. -/
theorem stern_cw_bridge (k : Nat) :
    ∀ x < 2 ^ k, cwVec 1 k x = ⟨Int.ofNat (stern (2 ^ k + x)), Int.ofNat (stern (2 ^ k + x + 1))⟩ := by
  sorry

/-- Exact Walsh-Hadamard coefficient of Stern level `k` in closed form via the inverse Gray code. -/
theorem stern_walsh_spectrum (k m : Nat) (hm : m < 2 ^ k) :
    sumInt (2 ^ k) (fun x => tmSign (x &&& m) * Int.ofNat (stern (2 ^ k + x))) =
      triSign (popcount m) * 3 ^ (k - popcount (m ||| igray m)) := by
  sorry

/-- Parametric `a`-Stern Walsh spectrum: exact closed form for every integer `a`, level `k` and mask `m`. -/
theorem aStern_walsh_spectrum (a : Int) (k m : Nat) (hm : m < 2 ^ k) :
    (walshSum (Lmat a) (Rmat a) ePlus k m).x =
      a ^ (popcount m) * (2 + a) ^ (expPlus k m) * (2 - a) ^ (expMinus m) * triSign (popcount m) := by
  sorry

/-- At `a = 2` the Walsh vector vanishes exactly when `expMinus m > 0`. -/
theorem twoStern_walsh_vanishing (k m : Nat) (hm : m < 2 ^ k) :
    walshSum (Lmat 2) (Rmat 2) ePlus k m = Vec2.zero ↔ expMinus m > 0 := by
  sorry

/-- Mod-3 resonance, `c = 3q`: exact period 4 in `k`, non-constant at period 2. -/
theorem carryStern_mod0_periodic (q k : Nat) (hk : 2 ^ k ≥ 3 * q) :
    carrySternF (3 * q) (k + 4) = carrySternF (3 * q) k ∧
    carrySternG (3 * q) (k + 4) = carrySternG (3 * q) k ∧
    carrySternF (3 * q) (k + 2) ≠ carrySternF (3 * q) k := by
  sorry

/-- Mod-3 resonance, `c = 3q + 1`: `F` is an exact affine progression, `G` has period 4. -/
theorem carryStern_mod1_affine (q k : Nat) (hk : 2 ^ k ≥ 3 * q + 1) :
    carrySternF (3 * q + 1) (k + 1) - carrySternF (3 * q + 1) k = -2 * tmSign q ∧
    carrySternG (3 * q + 1) (k + 4) = carrySternG (3 * q + 1) k := by
  sorry

/-- Mod-3 resonance, `c = 3q + 2`: dual of the `c = 3q + 1` law. -/
theorem carryStern_mod2_affine_dual (q k : Nat) (hk : 2 ^ k ≥ 3 * q + 2) :
    carrySternF (3 * q + 2) (k + 4) = carrySternF (3 * q + 2) k ∧
    carrySternG (3 * q + 2) (k + 1) - carrySternG (3 * q + 2) k = -2 * tmSign q := by
  sorry

/-- Quadratic Thue-Morse Stern vector closed form for every level `k >= 1`. -/
theorem quadStern_tm_closed_form (k : Nat) (hk : k ≥ 1) :
    (quadSternVec k).x = -3 * (-5 : Int) ^ ((k - 1) / 2) ∧
    (quadSternVec k).y = if k % 2 = 1 then 0 else -6 * (-5 : Int) ^ (k / 2 - 1) := by
  sorry

end SternWalshCarryResonanceChallenge
