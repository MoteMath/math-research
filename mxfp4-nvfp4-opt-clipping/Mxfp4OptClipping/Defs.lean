/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`mxfp4-nvfp4-opt-clipping`)

Pure-`Init` (zero Mathlib) exact rational definitions for OCP MXFP4 (`E2M1 + E8M0`),
NVFP4 (`E2M1 + E4M3`), optimal block-scale clipping, and E2M1 `-0` (`0b1000`) repurposing.
-/

namespace Mxfp4OptClipping

/-- Exact rational absolute value. -/
def absRat (u : Rat) : Rat :=
  if u < 0 then -u else u

/-- Exact rational square. -/
def sq (x : Rat) : Rat :=
  x * x

/-- Exact coordinate squared quantization error for OCP FP4 E2M1
    (`Q_E2M1^+ = {0, 1/2, 1, 3/2, 2, 3, 4, 6}`) at scale `s`. -/
def e2m1ErrSq (s u : Rat) : Rat :=
  let a := absRat u
  min (sq (a - 0))
    (min (sq (a - s * (1 / 2)))
      (min (sq (a - s * 1))
        (min (sq (a - s * (3 / 2)))
          (min (sq (a - s * 2))
            (min (sq (a - s * 3))
              (min (sq (a - s * 4))
                   (sq (a - s * 6))))))))

/-- Exact coordinate squared quantization error for E2M1 extended with an extra
    repurposed level `c` (`-0` code `0b1000` repurposed to `±c`). -/
def e2m1PlusErrSq (c s u : Rat) : Rat :=
  min (e2m1ErrSq s u) (sq (absRat u - s * c))

/-- Total squared L2 energy `‖x‖₂²` of a block `x : List Rat`. -/
def blockEnergy : List Rat → Rat
  | [] => 0
  | u :: xs => sq u + blockEnergy xs

/-- Total squared quantization error `‖x - Q_s(x)‖₂²` of a block `x` under E2M1 at scale `s`. -/
def blockErrSq (s : Rat) : List Rat → Rat
  | [] => 0
  | u :: xs => e2m1ErrSq s u + blockErrSq s xs

/-- Total squared quantization error of a block `x` under extended E2M1 (`±c`) at scale `s`. -/
def blockPlusErrSq (c s : Rat) : List Rat → Rat
  | [] => 0
  | u :: xs => e2m1PlusErrSq c s u + blockPlusErrSq c s xs

/-- Single-entry MXFP4 clipping-minus-rounding penalty `Φ(u) = (u - 3)² - e₁(u)`. -/
def clipPenalty (u : Rat) : Rat :=
  sq (u - 3) - e2m1ErrSq 1 u

/-- Total clipping penalty summed over entries with `|u| > 3` when halving `s = 1 → 1/2`. -/
def clipCost : List Rat → Rat
  | [] => 0
  | u :: xs =>
    (if (3 : Rat) < absRat u then clipPenalty (absRat u) else 0) + clipCost xs

/-- Total bulk MSE reduction summed over entries with `|u| ≤ 3` when halving `s = 1 → 1/2`. -/
def bulkGain : List Rat → Rat
  | [] => 0
  | u :: xs =>
    (if absRat u ≤ (3 : Rat) then e2m1ErrSq 1 u - e2m1ErrSq (1 / 2) u else 0) + bulkGain xs

/-- Exact 3-regime worst-case EF21 contraction for `opt-E8M0` MXFP4 at block size `B ≥ 1`. -/
def omegaOptE8M0 (B : Nat) : Rat :=
  let b : Rat := (B : Rat)
  if B ≤ 49 then
    (b + 15) / (b + 399)
  else if B ≤ 145 then
    ((b + 143) * (b + 143)) / (b * b + 1438 * b + 185185)
  else
    (b - 1) / (b + 575)

/-- Exact worst-case EF21 contraction for `ceil-E4M3` NVFP4 on core/deadzone bulk (`|u| ≤ 2`)
    and unconditionally for all blocks with `B ≥ 12`. -/
def omegaCeilE4M3 (B : Nat) : Rat :=
  let b : Rat := (B : Rat)
  (9 * b + 55) / (9 * b + 4087)

/-- Exact worst-case EF21 contraction for `nearest-E4M3` NVFP4 on core/deadzone bulk (`|u| ≤ 2`)
    and unconditionally for all blocks with `B ≥ 20`. -/
def omegaNearestE4M3 (B : Nat) : Rat :=
  let b : Rat := (B : Rat)
  (9 * b + 7) / (9 * b + 4615)

/-- Exact unrestricted all-block worst-case EF21 contraction for `ceil-E4M3` NVFP4
    (including the `[4, 6]`-midpoint `u = 5` regime for `2 ≤ B ≤ 11`). -/
def omegaCeilE4M3Full (B : Nat) : Rat :=
  let b : Rat := (B : Rat)
  if B ≤ 11 then
    (9 * b - 5) / (225 * b + 31)
  else
    omegaCeilE4M3 B

/-- Exact unrestricted all-block worst-case EF21 contraction for `nearest-E4M3` NVFP4
    (including the `[4, 6]`-midpoint `u = 5` regime for `2 ≤ B ≤ 19`). -/
def omegaNearestE4M3Full (B : Nat) : Rat :=
  let b : Rat := (B : Rat)
  if B ≤ 19 then
    (9 * b - 8) / (225 * b + 64)
  else
    omegaNearestE4M3 B

/-- Exact unrestricted all-block worst-case EF21 contraction for MXFP4 `ceil-E8M0`
    with E2M1 `-0` repurposed to `±8`. -/
def omegaE2M1Plus8 (B : Nat) : Rat :=
  let b : Rat := (B : Rat)
  if B ≤ 33 then
    (b + 15) / (b + 399)
  else
    (b - 1) / (b + 255)

/-- Exact 3-regime deadzone-bulk worst-case EF21 contraction for MXFP4 `ceil-E8M0`
    with E2M1 `-0` repurposed to `±1/4` (exact phase transitions at `B = 33` and `B = 49`). -/
def omegaE2M1PlusQtr (B : Nat) : Rat :=
  let b : Rat := (B : Rat)
  if B ≤ 33 then
    (b + 63) / (b + 1599)
  else if B ≤ 49 then
    (b + 15) / (b + 783)
  else
    (b - 1) / (b + 575)

/-- Construct the canonical single-outlier + uniform-bulk block `(M, u, ..., u)` of length `B` (`B ≥ 1`). -/
def mkSingleOutlierBlock (B : Nat) (M u : Rat) : List Rat :=
  M :: List.replicate (B - 1) u

end Mxfp4OptClipping
