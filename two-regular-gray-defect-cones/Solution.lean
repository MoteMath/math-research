/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoRegularGrayDefectCones

/-!
# Verified Solutions (`two-regular-gray-defect-cones`)
-/

namespace TwoRegularGrayDefectConesChallenge

open LinRepEngine

theorem checkConePosCert_sound {d r : Nat} (R : LinRep d) (D : ConePosCertData d r)
    (h : checkConePosCert R D = true) : ∀ n : Nat, 1 ≤ n → 0 ≤ evalRep R n :=
  LinRepEngine.checkConePosCert_sound R D h

theorem gray_defect_nonneg_all_q (q : Int) (hq : 0 ≤ q) (n : Nat) : 0 ≤ S_q q n :=
  LinRepEngine.gray_defect_nonneg_all_q q hq n

theorem W_G_sharp_two_fifths_bound (n : Nat) (hn : 1 ≤ n) :
    5 * W_G n ≤ 2 * (n : Int) - 2 + ((n % 2 : Nat) : Int) :=
  LinRepEngine.W_G_sharp_two_fifths_bound n hn

theorem extremal_W_G_odd (k : Nat) :
    5 * W_G (extremalA k) = 2 * (extremalA k : Int) - 1 :=
  LinRepEngine.extremal_W_G_odd k

theorem W_G_thue_morse_parity (n : Nat) :
    (2 : Int) ∣ (W_G n - ((n % 2 : Nat) : Int) * (1 - ((popcount n % 2 : Nat) : Int))) :=
  LinRepEngine.W_G_thue_morse_parity n

theorem E_G_mod4_law (n : Nat) :
    (4 : Int) ∣ (E_G n - ((n % 2 : Nat) : Int) * (((n / 2) % 4 : Nat) : Int)) :=
  LinRepEngine.E_G_mod4_law n

theorem E_G_dyadic_parabolic_sandwich (n : Nat) :
    Q_dyadic n ≤ 2 * E_G n ∧ E_G n ≤ Q_dyadic n :=
  LinRepEngine.E_G_dyadic_parabolic_sandwich n

theorem S_q_second_diff_identity (q : Int) (n : Nat) :
    S_q q (2 * n) + S_q q (2 * n + 2) - 2 * S_q q (2 * n + 1) = -2 * ((n % 2 : Nat) : Int) :=
  LinRepEngine.S_q_second_diff_identity q n

end TwoRegularGrayDefectConesChallenge
