/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SternWalshCarryResonance

/-!
# Verified Solutions (`stern-walsh-carry-resonance`)
-/

namespace SternWalshCarryResonanceChallenge

open SternCW

theorem stern_cw_bridge (k : Nat) :
    ∀ x < 2 ^ k, cwVec 1 k x = ⟨Int.ofNat (stern (2 ^ k + x)), Int.ofNat (stern (2 ^ k + x + 1))⟩ :=
  SternCW.stern_cw_bridge k

theorem stern_walsh_spectrum (k m : Nat) (hm : m < 2 ^ k) :
    sumInt (2 ^ k) (fun x => tmSign (x &&& m) * Int.ofNat (stern (2 ^ k + x))) =
      triSign (popcount m) * 3 ^ (k - popcount (m ||| igray m)) :=
  SternCW.stern_walsh_spectrum k m hm

theorem aStern_walsh_spectrum (a : Int) (k m : Nat) (hm : m < 2 ^ k) :
    (walshSum (Lmat a) (Rmat a) ePlus k m).x =
      a ^ (popcount m) * (2 + a) ^ (expPlus k m) * (2 - a) ^ (expMinus m) * triSign (popcount m) :=
  SternCW.aStern_walsh_spectrum a k m hm

theorem twoStern_walsh_vanishing (k m : Nat) (hm : m < 2 ^ k) :
    walshSum (Lmat 2) (Rmat 2) ePlus k m = Vec2.zero ↔ expMinus m > 0 :=
  SternCW.twoStern_walsh_vanishing k m hm

theorem carryStern_mod0_periodic (q k : Nat) (hk : 2 ^ k ≥ 3 * q) :
    carrySternF (3 * q) (k + 4) = carrySternF (3 * q) k ∧
    carrySternG (3 * q) (k + 4) = carrySternG (3 * q) k ∧
    carrySternF (3 * q) (k + 2) ≠ carrySternF (3 * q) k :=
  SternCW.carryStern_mod0_periodic q k hk

theorem carryStern_mod1_affine (q k : Nat) (hk : 2 ^ k ≥ 3 * q + 1) :
    carrySternF (3 * q + 1) (k + 1) - carrySternF (3 * q + 1) k = -2 * tmSign q ∧
    carrySternG (3 * q + 1) (k + 4) = carrySternG (3 * q + 1) k :=
  SternCW.carryStern_mod1_affine q k hk

theorem carryStern_mod2_affine_dual (q k : Nat) (hk : 2 ^ k ≥ 3 * q + 2) :
    carrySternF (3 * q + 2) (k + 4) = carrySternF (3 * q + 2) k ∧
    carrySternG (3 * q + 2) (k + 1) - carrySternG (3 * q + 2) k = -2 * tmSign q :=
  SternCW.carryStern_mod2_affine_dual q k hk

theorem quadStern_tm_closed_form (k : Nat) (hk : k ≥ 1) :
    (quadSternVec k).x = -3 * (-5 : Int) ^ ((k - 1) / 2) ∧
    (quadSternVec k).y = if k % 2 = 1 then 0 else -6 * (-5 : Int) ^ (k / 2 - 1) :=
  SternCW.quadStern_tm_closed_form k hk

end SternWalshCarryResonanceChallenge
