/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoAdicCarryFirewallCovers

/-!
# Verified Solutions (`two-adic-carry-firewall-covers`)
-/

namespace TwoAdicCarryFirewallCoversChallenge

open AdicCompactness

theorem coverTree_sound {L : Type} {P : Nat → Prop}
    (valid : Nat → Nat → L → Bool)
    (hleaf : ∀ r d cert, r < 2 ^ d → valid r d cert = true → ∀ q, P (r + q * 2 ^ d))
    (t : CoverTree L) (hchk : checkCover valid 0 0 t = true) :
    ∀ n : Nat, P n :=
  AdicCompactness.coverTree_sound valid hleaf t hchk

theorem T4_global_convergence :
    ∀ n : Nat, ∃ m : Nat, iterNat (TCollatz 4) m n ≤ 1 :=
  AdicCompactness.T4_global_convergence

theorem T5_global_convergence :
    ∀ n : Nat, ∃ m : Nat, iterNat (TCollatz 5) m n ≤ 1 :=
  AdicCompactness.T5_global_convergence

theorem X21_global_convergence_to_zero :
    ∀ n : Nat, ∃ m : Nat, iterNat (TXorCollatz 2 1) m n = 0 :=
  AdicCompactness.X21_global_convergence_to_zero

theorem X33_global_convergence_to_zero :
    ∀ n : Nat, ∃ m : Nat, iterNat (TXorCollatz 3 3) m n = 0 :=
  AdicCompactness.X33_global_convergence_to_zero

theorem grayQuad2_val_ceiling :
    ∀ n : Nat, ¬ (2 ^ 15 ∣ (n ^^^ (n >>> 1)) * (n ^^^ (n >>> 1)) + 3 * n + 60) :=
  AdicCompactness.grayQuad2_val_ceiling

theorem grayQuad2_neq_shift15 :
    ∀ n : Nat, (n ^^^ (n >>> 1)) * (n ^^^ (n >>> 1)) + 3 * n + 60 ≠ (n <<< 15) :=
  AdicCompactness.grayQuad2_neq_shift15

theorem T8_nontrivial_6cycle_never_drops :
    ∀ m : Nat, 975 ≤ iterNat (TCollatz 8) m 975 :=
  AdicCompactness.T8_nontrivial_6cycle_never_drops

end TwoAdicCarryFirewallCoversChallenge
