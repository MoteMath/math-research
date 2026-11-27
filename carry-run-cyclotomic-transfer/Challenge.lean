/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryRunCyclotomicTransfer.Defs

/-!
# Trusted Challenge Statements (`carry-run-cyclotomic-transfer`)

Headline infinite theorems; proofs are supplied in `Solution.lean`.
-/

namespace CarryRunCyclotomicTransferChallenge

open SiliconCarryTransfer

/-- **THEOREM 1A (Even-Radix Carry-Run Cyclotomic Period-`(L+2)` Collapse)**:
    For EVERY even radix `B = 2m` (`m ≥ 1`), EVERY carry-run bound `L ≥ 1`, and EVERY digit-width `w : Nat`:
    `∑_{x,y < (2m)^w, carryRun(x,y) ≤ L} (-1)^(σ_{2m}((x+y) mod (2m)^w))`
    equals `m^w` if `w ≡ 0`, `-m^w` if `w ≡ L+1`, and `0` otherwise `(mod L+2)`! -/
theorem evenRadix_carryRun_outputParity_collapse (m L : Nat) (hm : 1 ≤ m) (hL : 1 ≤ L) (w : Nat) :
    sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
      if maxCarryRunLe (2 * m) L w x y then paritySign (digitSum (2 * m) w ((x + y) % (2 * m) ^ w)) else 0)) =
    if w % (L + 2) = 0 then (m : Int) ^ w
    else if w % (L + 2) = L + 1 then -((m : Int) ^ w)
    else 0 := by
  sorry

/-- **THEOREM 1C (Binary Carry-Run Full-Sum Thue–Morse Collapse — Including MSB Carry-Out)**:
    For EVERY `L ≥ 1` and EVERY bit-width `w : Nat`,
    `∑_{x,y < 2^w, carryRun(x,y) ≤ L} (-1)^popcount(x + y)`
    has exact period `L + 2`, taking values `1` at `w ≡ 0` or `L+1`, `-2` at `w ≡ 1`, and `0` otherwise! -/
theorem binary_carryRun_fullPopcount_collapse (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
      if maxCarryRunLe 2 L w x y then paritySign (popcount (w + 1) (x + y)) else 0)) =
    if w % (L + 2) = 0 then 1
    else if w % (L + 2) = 1 then -2
    else if w % (L + 2) = L + 1 then 1
    else 0 := by
  sorry

/-- **THEOREM 2B (Even-Radix Ripple-Carry Input-Parity Period-`(L+1)` Monomial Collapse)**:
    For EVERY even radix `B = 2m` (`m ≥ 1`), EVERY ripple depth bound `L ≥ 1`, and EVERY width `w : Nat`:
    `∑_{x,y < (2m)^w, rippleDepth(x,y) ≤ L} (-1)^(σ_{2m}(x) + σ_{2m}(y))`
    vanishes identically whenever `(L + 1) ∤ w`, and equals
    `((-1)^(L+1) * 2^L * m^(L+1))^(w / (L + 1))` whenever `(L + 1) ∣ w`! -/
theorem evenRadix_rippleDepth_inputParity_collapse (m L : Nat) (hm : 1 ≤ m) (hL : 1 ≤ L) (w : Nat) :
    sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
      if maxRippleDepthLe (2 * m) L w x y then
        paritySign (digitSum (2 * m) w x + digitSum (2 * m) w y)
      else 0)) =
    if w % (L + 1) = 0 then
      (paritySign (L + 1) * (2 : Int) ^ L * (m : Int) ^ (L + 1)) ^ (w / (L + 1))
    else 0 := by
  sorry

/-- **THEOREM 2C (Exact Unweighted Binary Ripple-Carry Recurrence)**:
    For EVERY `L ≥ 1` and EVERY `w : Nat`, let `R_L(w) = #{(x, y) ∈ [0, 2^w)^2 | rippleDepth(x,y) ≤ L}`.
    Then `R_L(w + L + 1) = 4 * R_L(w + L) - 2^L * R_L(w)`! -/
theorem binary_rippleDepth_plain_recurrence (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    let R := fun n => sumNat (2 ^ n) (fun x => sumNat (2 ^ n) (fun y =>
      if maxRippleDepthLe 2 L n x y then (1 : Int) else 0))
    R (w + L + 1) = 4 * R (w + L) - (2 : Int) ^ L * R w := by
  sorry

/-- **THEOREM 3A (Exact Bivariate Absorption-Weighted Carry-Run 3-Term Recurrence)**:
    For EVERY integer absorption weight `t ∈ ℤ`, EVERY `L ≥ 1`, and EVERY bit-width `w : Nat`:
    `A_L(t, w + L + 2) = (1 - t) * A_L(t, w + L) + t * A_L(t, w)`! -/
theorem binary_carryRun_absorption_recurrence (t : Int) (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    carryRunAbsSum t L (w + L + 2) =
      (1 - t) * carryRunAbsSum t L (w + L) + t * carryRunAbsSum t L w := by
  sorry

/-- **THEOREM 3B (Zero-Absorption Odd/Even Dichotomy at `t = 0`)**:
    Over all `w`-bit pairs `(x, y)` with `carryRun(x, y) ≤ L` and ZERO carry absorptions:
    - For EVERY **odd** `L = 2k + 1` and EVERY `w ≥ L`: `A_{2k+1}(0, w) = 0` (exact finite support!).
    - For EVERY **even** `L = 2k` (`k ≥ 1`) and EVERY `w ≥ L`: `A_{2k}(0, w) = (-1)^w` (persistent oscillation!). -/
theorem binary_zeroAbsorption_dichotomy (L : Nat) (hL : 1 ≤ L) (w : Nat) (hw : L ≤ w) :
    carryRunAbsSum 0 L w = if L % 2 = 1 then 0 else paritySign w := by
  sorry

/-- **UNIVERSAL 3-PARAMETER RIPPLE-CARRY MATRIX ANNIHILATOR** (`∀ L ≥ 1, ∀ k, p, g ∈ ℤ`):
    `M_rip(L; k, p, g)^(L+1) v - (k + p + g) * M_rip(L; k, p, g)^L v + g * p^L * v = 0`
    on every coordinate `i ≤ L` and every vector `v`! -/
theorem rippleOp_annihilator (L : Nat) (hL : 1 ≤ L) (k p g : Int) (v : Nat → Int) :
    ∀ i, i < L + 1 →
      iterOp (rippleOp L k p g) (L + 1) v i -
        (k + p + g) * iterOp (rippleOp L k p g) L v i +
        g * p ^ L * v i = 0 := by
  sorry

/-- **UNIVERSAL 4-PARAMETER CARRY-RUN MATRIX ANNIHILATOR** (`∀ L ≥ 1, ∀ a, b, c, r ∈ ℤ`):
    `M_run^(L+2) v - (a+r) M_run^(L+1) v + (a*r - b*c) M_run^L v + b*c*r^L * v = 0`
    on every coordinate `i ≤ L` and every vector `v`! -/
theorem runOp_annihilator (L : Nat) (hL : 1 ≤ L) (a b c r : Int) (v : Nat → Int) :
    ∀ i, i < L + 1 →
      iterOp (runOp L a b c r) (L + 2) v i -
        (a + r) * iterOp (runOp L a b c r) (L + 1) v i +
        (a * r - b * c) * iterOp (runOp L a b c r) L v i +
        b * c * r ^ L * v i = 0 := by
  sorry

end CarryRunCyclotomicTransferChallenge
