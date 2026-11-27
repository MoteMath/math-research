/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MortonCarryMonodromyRenorm

/-!
# Verified Solutions (`morton-carry-monodromy-renorm`)
-/

namespace MortonCarryMonodromyRenormChallenge

open Dynsil4.CMR

theorem cmr_full_period_compiler {B S : Nat} (hB : 2 ≤ B) (A : RenormAutomaton B S)
    (hfull : ∀ s, A.len s = B) (s : Fin S) (n : Nat) :
    HasExactPeriod (step B (A.perm s) n) 0 (B ^ n) :=
  Dynsil4.CMR.cmr_full_period_compiler hB A hfull s n

theorem mortonRot_exact_period_all_d_n (d : Nat) (hd : 1 ≤ d) (n : Nat) :
    HasExactPeriod (step (2 ^ d) (rotDigitPerm d hd) n) 0 ((d + 1) ^ n) :=
  Dynsil4.CMR.mortonRot_exact_period_all_d_n d hd n

theorem mortonRot_orbit_iff_flagHelix (d : Nat) (hd : 1 ≤ d) (n z : Nat) (hz : z < (2 ^ d) ^ n) :
    (∃ t, t < (d + 1) ^ n ∧ iter (step (2 ^ d) (rotDigitPerm d hd) n) t 0 = z) ↔
      isFlagHelix d hd n z = true :=
  Dynsil4.CMR.mortonRot_orbit_iff_flagHelix d hd n z hz

theorem morton2D_exact_period_all_z (n : Nat) :
    ∀ z, z < 4 ^ n → HasExactPeriod (step 4 swap2D n) z (period2D n z) :=
  Dynsil4.CMR.morton2D_exact_period_all_z n

theorem morton2D_period_dichotomy (n : Nat) :
    ∀ z, z < 4 ^ n →
      (∃ k, k ≤ n ∧ period2D n z = 3 ^ k) ∨
      (∃ k, k + 2 ≤ n ∧ period2D n z = 2 * 3 ^ k) :=
  Dynsil4.CMR.morton2D_period_dichotomy n

theorem delayed_fracture_exact_period (n : Nat) :
    HasExactPeriod (step 8 piDelay n) 0 (piDelayAutomaton.orbitProd ⟨0, by omega⟩ n) :=
  Dynsil4.CMR.delayed_fracture_exact_period n

theorem delayed_fracture_closed_form (n : Nat) :
    piDelayAutomaton.orbitProd ⟨0, by omega⟩ n * 2 ^ (n / 3) = 8 ^ n :=
  Dynsil4.CMR.delayed_fracture_closed_form n

end MortonCarryMonodromyRenormChallenge
