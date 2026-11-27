/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PopcountClockBorrowAccel

/-!
# Verified Solutions (`popcount-clock-borrow-accel`)
-/

namespace PopcountClockBorrowAccelChallenge

open Dynsil11

theorem T_xor_unit_clock (t x : Nat) : V_unit (iter T_xor t x) = V_unit x - (t : Int) :=
  Dynsil11.T_xor_unit_clock t x

theorem T_xor_hits_mersenne_exact : ∀ (N m x : Nat),
    x < 2 ^ m → V_unit x + (m : Int) = (N : Int) →
    iter T_xor N x = 2 ^ m - 1 :=
  Dynsil11.T_xor_hits_mersenne_exact 

theorem T_xor_sync_collision_iff (x y : Nat) :
    (∃ t : Nat, iter T_xor t x = iter T_xor t y) ↔ V_unit x = V_unit y :=
  Dynsil11.T_xor_sync_collision_iff x y

theorem T_sub_borrow_acceleration {x : Nat} (hphi : 0 < phi x) :
    2 ^ popcount x ≤ x ∧
    T_sub x = iter T_xor (ctzPos (x >>> popcount x) + 1) x ∧
    phi (T_sub x) = phi x - 1 :=
  Dynsil11.T_sub_borrow_acceleration hphi

theorem T_sub_hits_mersenne_exact : ∀ (N x : Nat),
    phi x = (N : Int) →
    iter T_sub N x = 2 ^ popcount (iter T_sub N x) - 1 :=
  Dynsil11.T_sub_hits_mersenne_exact 

theorem F_xor_wrap_unique_2w_cycle {w : Nat} (hw : 0 < w) :
    (∀ x < 2 ^ w, ∃ t, iter (F_xor_wrap w) t x = 2 ^ w - 1) ∧
    iter (F_xor_wrap w) (2 * w) (2 ^ w - 1) = 2 ^ w - 1 ∧
    (∀ t, 0 < t → t < 2 * w → iter (F_xor_wrap w) t (2 ^ w - 1) ≠ 2 ^ w - 1) :=
  Dynsil11.F_xor_wrap_unique_2w_cycle hw

theorem F_sub_wrap_unique_cycle {w : Nat} (hw : 0 < w) :
    (∀ x < 2 ^ w, ∃ t, iter (F_sub_wrap w) t x = 2 ^ w - 1) ∧
    iter (F_sub_wrap w) (w + 1) (2 ^ w - 1) = 2 ^ w - 1 ∧
    (∀ t, 0 < t → t < w + 1 → iter (F_sub_wrap w) t (2 ^ w - 1) ≠ 2 ^ w - 1) :=
  Dynsil11.F_sub_wrap_unique_cycle hw

theorem complement_carry_borrow_conjugacy {w x : Nat} (hw : 0 < w) (hx : x < 2 ^ w) :
    comp w (F_sub_wrap w (comp w x)) = F_add_dual_wrap w x :=
  Dynsil11.complement_carry_borrow_conjugacy hw hx

end PopcountClockBorrowAccelChallenge
