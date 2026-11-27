/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`muon-ns-dyadic-cycles`)

Pure-`Init` (zero Mathlib, zero `native_decide`) exact rational and bit-exact
IEEE-754 / OCP FP8-E4M3FN / MXFP4-E2M1 Round-to-Nearest-Even (RNE) definitions
for quantized Newton-Schulz and Muon quintic orthogonalization.

All floating-point arithmetic (`fpAdd`, `fpMul`, `fpPackRne`) is implemented in
pure `Nat` with offset exponent `expOff = exp2 + 512` and O(1) non-recursive
`floorLog2` for fast, exact Lean 4 kernel reduction.
-/

namespace MuonNsDyadic

/-- Exact rational absolute value. -/
def ratAbs (q : Rat) : Rat :=
  if q < 0 then -q else q

/-- Exact odd quintic polynomial `p(x) = a*x + b*x^3 + c*x^5` over `Rat`. -/
def quinticEval (a b c x : Rat) : Rat :=
  a * x + b * (x * x * x) + c * (x * x * x * x * x)

/-- Exact first derivative `p'(x) = a + 3*b*x^2 + 5*c*x^4` over `Rat`. -/
def quinticDeriv (a b c x : Rat) : Rat :=
  a + 3 * b * (x * x) + 5 * c * (x * x * x * x)

/-- Exact second derivative `p''(x) = 6*b*x + 20*c*x^3` over `Rat`. -/
def quinticSecondDeriv (_a b c x : Rat) : Rat :=
  6 * b * x + 20 * c * (x * x * x)

/-- Specification of a binary floating-point format (IEEE-754, OCP FP8-E4M3FN, MXFP4-E2M1). -/
structure FpSpec where
  ebits : Nat
  mbits : Nat
  bias : Nat
  hasInf : Bool
  hasFnNan : Bool
  saturate : Bool
  deriving Repr, DecidableEq

/-- IEEE-754 / BFloat16 (`E8M7`, bias `127`, Inf/NaN). -/
def bf16Spec : FpSpec :=
  { ebits := 8, mbits := 7, bias := 127, hasInf := true, hasFnNan := false, saturate := false }

/-- OCP FP8-E4M3FN non-saturating (`E4M3`, bias `7`, no Inf, `0x7F`/`0xFF` = NaN, max finite `448`). -/
def fp8E4M3FNSpec : FpSpec :=
  { ebits := 4, mbits := 3, bias := 7, hasInf := false, hasFnNan := true, saturate := false }

/-- OCP MXFP4-E2M1 (`E2M1`, bias `1`, no Inf, no NaN, saturates to `±6`). -/
def mxfp4E2M1Spec : FpSpec :=
  { ebits := 2, mbits := 1, bias := 1, hasInf := false, hasFnNan := false, saturate := true }

/-- Exponent offset (`512`) so all intermediate dyadic exponents stay strictly positive `Nat`. -/
def fpExpOffset : Nat := 512

/-- Strict call-by-value `Nat` binder for fast Lean 4 kernel reduction (eliminates call-by-name `let` blowup). -/
def strictNat {α : Type} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

/-- Non-recursive O(1) `floor(log2 n)` for `1 ≤ n < 2^32` with strict evaluation and zero `let` duplication. -/
def floorLog2 (n : Nat) : Nat :=
  strictNat n fun n =>
  let f2 (x acc : Nat) : Nat := if Nat.ble 2 x then acc + 1 else acc
  let f4 (x acc : Nat) : Nat :=
    if Nat.ble 4 x then strictNat (x / 4) fun x' => f2 x' (acc + 2) else f2 x acc
  let f16 (x acc : Nat) : Nat :=
    if Nat.ble 16 x then strictNat (x / 16) fun x' => f4 x' (acc + 4) else f4 x acc
  let f256 (x acc : Nat) : Nat :=
    if Nat.ble 256 x then strictNat (x / 256) fun x' => f16 x' (acc + 8) else f16 x acc
  if Nat.ble 65536 n then strictNat (n / 65536) fun n' => f256 n' 16 else f256 n 0

/-- Unpacked floating-point value: NaN, signed Inf, or exact dyadic `(-1)^sign * sig * 2^(expOff - 512)`. -/
inductive FpVal where
  | nan
  | inf (sign : Bool)
  | fin (sign : Bool) (sig : Nat) (expOff : Nat)
  deriving Repr, DecidableEq

/-- Canonical quiet NaN bit-pattern for `spec`. -/
def fpCanonNaN (spec : FpSpec) : Nat :=
  strictNat (2 ^ spec.ebits) fun expBase =>
  strictNat (2 ^ spec.mbits) fun mantBase =>
  let expMask := expBase - 1
  let mantMask := mantBase - 1
  if spec.hasFnNan then
    expMask * mantBase + mantMask
  else
    expMask * mantBase + 2 ^ (spec.mbits - 1)

/-- Unpack raw `bits` under `spec` into exact `FpVal`. -/
def fpUnpack (spec : FpSpec) (bits : Nat) : FpVal :=
  strictNat bits fun bits =>
  strictNat (2 ^ spec.ebits) fun expBase =>
  strictNat (2 ^ spec.mbits) fun mantBase =>
  strictNat (expBase - 1) fun expMask =>
  strictNat (mantBase - 1) fun mantMask =>
  strictNat ((bits / (expBase * mantBase)) % 2) fun sBit =>
  strictNat ((bits / mantBase) % expBase) fun exp =>
  strictNat (bits % mantBase) fun mant =>
  let sign := Nat.beq sBit 1
  if spec.hasInf && Nat.beq exp expMask then
    if Nat.beq mant 0 then .inf sign else .nan
  else if spec.hasFnNan && Nat.beq exp expMask && Nat.beq mant mantMask then
    .nan
  else if Nat.beq exp 0 then
    if Nat.beq mant 0 then
      .fin sign 0 fpExpOffset
    else
      .fin sign mant (fpExpOffset + 1 - spec.bias - spec.mbits)
  else
    .fin sign (mantBase + mant) (fpExpOffset + exp - spec.bias - spec.mbits)

/-- Predicate: `bits` represents NaN under `spec`. -/
def fpIsNaN (spec : FpSpec) (bits : Nat) : Bool :=
  match fpUnpack spec bits with
  | .nan => true
  | _ => false

/-- Predicate: `bits` represents `±Inf` under `spec`. -/
def fpIsInf (spec : FpSpec) (bits : Nat) : Bool :=
  match fpUnpack spec bits with
  | .inf _ => true
  | _ => false

/-- Predicate: `bits` represents a finite number under `spec`. -/
def fpIsFinite (spec : FpSpec) (bits : Nat) : Bool :=
  match fpUnpack spec bits with
  | .fin _ _ _ => true
  | _ => false

/-- Exact rational value of a finite bit-pattern under `spec` (`0` for non-finite). -/
def fpToRat (spec : FpSpec) (bits : Nat) : Rat :=
  match fpUnpack spec bits with
  | .fin sign sig expOff =>
    if Nat.beq sig 0 then 0
    else
      let mag : Rat :=
        if Nat.ble fpExpOffset expOff then
          ((sig * 2 ^ (expOff - fpExpOffset) : Nat) : Rat)
        else
          (sig : Rat) / ((2 ^ (fpExpOffset - expOff) : Nat) : Rat)
      if sign then -mag else mag
  | _ => 0

/-- Exact Round-to-Nearest-Even (RNE) packer from dyadic `(-1)^sign * sig * 2^(expOff - 512)`. -/
def fpPackRne (spec : FpSpec) (sign : Bool) (sig : Nat) (expOff : Nat) : Nat :=
  strictNat sig fun sig =>
  strictNat expOff fun expOff =>
  strictNat (2 ^ spec.ebits) fun expBase =>
  strictNat (2 ^ spec.mbits) fun mantBase =>
  strictNat (if sign then expBase * mantBase else 0) fun sBit =>
  if Nat.beq sig 0 then
    sBit
  else
    strictNat (expBase - 1) fun expMask =>
    strictNat (mantBase - 1) fun mantMask =>
    strictNat (floorLog2 sig) fun bl =>
    strictNat (bl + expOff) fun eTrueOff =>
    strictNat (fpExpOffset + 1 - spec.bias) fun eMinOff =>
    if Nat.ble eMinOff eTrueOff then
      strictNat (
        if Nat.ble bl spec.mbits then
          sig * 2 ^ (spec.mbits - bl)
        else
          strictNat (2 ^ (bl - spec.mbits)) fun powSh =>
          strictNat (sig / powSh) fun q0 =>
          strictNat (sig % powSh) fun rem =>
          strictNat (powSh / 2) fun half =>
          if Nat.ble (half + 1) rem || (Nat.beq rem half && Nat.beq (q0 % 2) 1) then q0 + 1 else q0
      ) fun q =>
      let carry := Nat.beq q (2 * mantBase)
      strictNat (if carry then q / 2 else q) fun q' =>
      strictNat (if carry then eTrueOff + 1 else eTrueOff) fun eTrueOff' =>
      strictNat (eTrueOff' + spec.bias - fpExpOffset) fun expBiased =>
      strictNat (q' % mantBase) fun qMant =>
      if spec.hasInf then
        if Nat.ble expMask expBiased then
          sBit + expMask * mantBase
        else
          sBit + expBiased * mantBase + qMant
      else if spec.hasFnNan then
        if Nat.ble (expMask + 1) expBiased || (Nat.beq expBiased expMask && Nat.beq qMant mantMask) then
          if spec.saturate then
            sBit + expMask * mantBase + (mantMask - 1)
          else
            sBit + expMask * mantBase + mantMask
        else
          sBit + expBiased * mantBase + qMant
      else
        if Nat.ble (expMask + 1) expBiased then
          sBit + expMask * mantBase + mantMask
        else
          sBit + expBiased * mantBase + qMant
    else
      strictNat (eMinOff - spec.mbits) fun eLsbOff =>
      strictNat (
        if Nat.ble eLsbOff expOff then
          sig * 2 ^ (expOff - eLsbOff)
        else
          strictNat (eLsbOff - expOff) fun sh =>
          if Nat.ble (bl + 3) sh then
            0
          else
            strictNat (2 ^ sh) fun powSh =>
            strictNat (sig / powSh) fun q0 =>
            strictNat (sig % powSh) fun rem =>
            strictNat (powSh / 2) fun half =>
            if Nat.ble (half + 1) rem || (Nat.beq rem half && Nat.beq (q0 % 2) 1) then q0 + 1 else q0
      ) fun q =>
      if Nat.beq q mantBase then
        sBit + mantBase
      else
        sBit + q

/-- Bit-exact RNE floating-point addition under `spec` (using exact sticky-bit alignment). -/
def fpAdd (spec : FpSpec) (a b : Nat) : Nat :=
  strictNat (2 ^ spec.ebits) fun expBase =>
  strictNat (2 ^ spec.mbits) fun mantBase =>
  strictNat (expBase - 1) fun expMask =>
  strictNat (expBase * mantBase) fun signBase =>
  match fpUnpack spec a, fpUnpack spec b with
  | .nan, _ | _, .nan => fpCanonNaN spec
  | .inf sa, .inf sb =>
    if sa != sb then fpCanonNaN spec
    else (if sa then signBase else 0) + expMask * mantBase
  | .inf sa, _ => (if sa then signBase else 0) + expMask * mantBase
  | _, .inf sb => (if sb then signBase else 0) + expMask * mantBase
  | .fin sa ma ea, .fin sb mb eb =>
    if Nat.beq ma 0 && Nat.beq mb 0 then
      if sa && sb then signBase else 0
    else if Nat.beq ma 0 then
      fpPackRne spec sb mb eb
    else if Nat.beq mb 0 then
      fpPackRne spec sa ma ea
    else
      let addOrdered (s1 : Bool) (m1 e1 : Nat) (s2 : Bool) (m2 e2 : Nat) : Nat :=
        strictNat (e1 - e2) fun diff =>
        let finish (x1 x2 eRes : Nat) : Nat :=
          strictNat x1 fun x1 =>
          strictNat x2 fun x2 =>
          if s1 == s2 then
            fpPackRne spec s1 (x1 + x2) eRes
          else if Nat.beq x1 x2 then
            0
          else if Nat.ble (x2 + 1) x1 then
            fpPackRne spec s1 (x1 - x2) eRes
          else
            fpPackRne spec s2 (x2 - x1) eRes
        if Nat.ble diff (spec.mbits + 4) then
          finish (m1 * 2 ^ diff) m2 e2
        else
          finish (m1 * 16) 1 (e1 - 4)
      if Nat.ble eb ea then addOrdered sa ma ea sb mb eb
      else addOrdered sb mb eb sa ma ea

/-- Bit-exact RNE floating-point multiplication under `spec`. -/
def fpMul (spec : FpSpec) (a b : Nat) : Nat :=
  strictNat (2 ^ spec.ebits) fun expBase =>
  strictNat (2 ^ spec.mbits) fun mantBase =>
  strictNat (expBase - 1) fun expMask =>
  strictNat (expBase * mantBase) fun signBase =>
  match fpUnpack spec a, fpUnpack spec b with
  | .nan, _ | _, .nan => fpCanonNaN spec
  | .inf sa, .inf sb =>
    (if sa != sb then signBase else 0) + expMask * mantBase
  | .inf sa, .fin sb mb _ =>
    if Nat.beq mb 0 then fpCanonNaN spec
    else (if sa != sb then signBase else 0) + expMask * mantBase
  | .fin sa ma _, .inf sb =>
    if Nat.beq ma 0 then fpCanonNaN spec
    else (if sa != sb then signBase else 0) + expMask * mantBase
  | .fin sa ma ea, .fin sb mb eb =>
    let sres := sa != sb
    if Nat.beq ma 0 || Nat.beq mb 0 then
      if sres then signBase else 0
    else
      fpPackRne spec sres (ma * mb) (ea + eb - fpExpOffset)

/-- Quintic polynomial parenthesization mode. -/
inductive EvalMode where
  | monomial     -- ((a*x) + b*x^3) + c*x^5
  | horner       -- x * (a + x^2 * (b + c*x^2))
  | muonMatForm  -- a*x + x * (b*x^2 + c*x^4)
  deriving Repr, DecidableEq

/-- Single bit-exact quintic step under `spec` and `mode` (strictly evaluated). -/
def quinticStep (spec : FpSpec) (mode : EvalMode) (a b c x : Nat) : Nat :=
  strictNat x fun x =>
  strictNat (fpMul spec x x) fun x2 =>
  match mode with
  | .monomial =>
    strictNat (fpMul spec x2 x) fun x3 =>
    strictNat (fpMul spec x3 x2) fun x5 =>
    fpAdd spec (fpAdd spec (fpMul spec a x) (fpMul spec b x3)) (fpMul spec c x5)
  | .horner =>
    strictNat (fpAdd spec b (fpMul spec c x2)) fun inner =>
    strictNat (fpAdd spec a (fpMul spec x2 inner)) fun mid =>
    fpMul spec x mid
  | .muonMatForm =>
    strictNat (fpMul spec x2 x2) fun x4 =>
    strictNat (fpAdd spec (fpMul spec b x2) (fpMul spec c x4)) fun B =>
    fpAdd spec (fpMul spec a x) (fpMul spec x B)

/-- `n`-step stationary quintic iteration (strictly evaluated). -/
def quinticIter (spec : FpSpec) (mode : EvalMode) (a b c : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => strictNat (quinticStep spec mode a b c x) fun y => quinticIter spec mode a b c n y

/-- Non-stationary quintic schedule iteration (for Polar-Express, strictly evaluated). -/
def quinticScheduleIter (spec : FpSpec) (mode : EvalMode) : List (Nat × Nat × Nat) → Nat → Nat
  | [], x => x
  | (a, b, c) :: rest, x =>
    strictNat (quinticStep spec mode a b c x) fun y => quinticScheduleIter spec mode rest y

-- ============================================================================
-- Exact Format Bit-Pattern Constants (from a GPU + CPU fraction-oracle search)
-- ============================================================================

/-- BF16 `1.0` (`0x3F80`). -/
def bf16One : Nat := 0x3F80
/-- BF16 `+Inf` (`0x7F80`). -/
def bf16PosInf : Nat := 0x7F80

/-- Jordan's Muon quintic `(3.4445, -4.7750, 2.0315)` rounded to BF16: `(55/16, -153/32, 65/32)`. -/
def jordanBf16A : Nat := 0x405C
def jordanBf16B : Nat := 0xC099
def jordanBf16C : Nat := 0x4002

/-- GPU-discovered BF16 globally optimal dyadic quintic (Monomial): `(35/16, -31/16, 3/4)`. -/
def bf16OptA : Nat := 0x400C
def bf16OptB : Nat := 0xBFF8
def bf16OptC : Nat := 0x3F40

/-- OCP FP8-E4M3FN `1.0` (`0x38`) and canonical NaN (`0x7F`). -/
def fp8One : Nat := 0x38
def fp8NaN : Nat := 0x7F

/-- GPU-discovered FP8-E4M3FN globally optimal dyadic quintic: `(2, -9/8, 1/8)`. -/
def fp8OptA : Nat := 0x40
def fp8OptB : Nat := 0xB9
def fp8OptC : Nat := 0x20

/-- Jordan's Muon quintic rounded to FP8-E4M3FN: `(7/2, -5, 2)`. -/
def jordanFp8A : Nat := 0x46
def jordanFp8B : Nat := 0xCA
def jordanFp8C : Nat := 0x40

/-- Polar-Express 5-step schedule (Amsel et al. 2025) rounded to BF16. -/
def polarExpressBf16 : List (Nat × Nat × Nat) :=
  [ (0x4105, 0xC1BD, 0x418A),
    (0x4083, 0xC03D, 0x3F0B),
    (0x407D, 0xC03A, 0x3F0D),
    (0x4054, 0xC01F, 0x3F03),
    (0x4013, 0xBFD6, 0x3ED6) ]

/-- Polar-Express 5-step schedule rounded to OCP FP8-E4M3FN. -/
def polarExpressFp8 : List (Nat × Nat × Nat) :=
  [ (0x50, 0xDC, 0x59),
    (0x48, 0xC4, 0x31),
    (0x48, 0xC4, 0x31),
    (0x45, 0xC2, 0x30),
    (0x41, 0xBD, 0x2D) ]

/-- MXFP4-E2M1 `1.0` (`0x2`) and saturation ceiling `6.0` (`0x7`). -/
def mxfp4One : Nat := 0x2
def mxfp4Six : Nat := 0x7

/-- Jordan's Muon quintic rounded to MXFP4-E2M1: `(3, -4, 2)`. -/
def jordanMxfp4A : Nat := 0x5
def jordanMxfp4B : Nat := 0xE
def jordanMxfp4C : Nat := 0x4

/-- Classic cubic Newton-Schulz `(3/2, -1/2, 0)` in MXFP4-E2M1. -/
def classicNsMxfp4A : Nat := 0x3
def classicNsMxfp4B : Nat := 0x9
def classicNsMxfp4C : Nat := 0x0

-- ============================================================================
-- Pure-Kernel Range Checker (Zero `native_decide`)
-- ============================================================================

/-- Structurally recursive binary-splitting range checker (`O(log count)` depth). -/
def checkRangeFuel (p : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, _, count => count == 0
  | fuel + 1, start, count =>
    if count == 0 then true
    else if count == 1 then p start
    else
      let half := count / 2
      checkRangeFuel p fuel start half && checkRangeFuel p fuel (start + half) (count - half)

/-- Check `p` on `[start, start + count)` with depth bound `12` (covers up to `4096` points). -/
def checkRange (p : Nat → Bool) (start count : Nat) : Bool :=
  checkRangeFuel p 12 start count

theorem checkRangeFuel_spec (p : Nat → Bool) :
    ∀ (fuel start count : Nat), checkRangeFuel p fuel start count = true →
      ∀ x : Nat, start ≤ x → x < start + count → p x = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro start count h x hlo hhi
    simp only [checkRangeFuel, beq_iff_eq] at h
    omega
  | succ f ih =>
    intro start count h x hlo hhi
    unfold checkRangeFuel at h
    by_cases h0 : count = 0
    · omega
    · simp only [h0, beq_iff_eq, ↓reduceIte] at h
      by_cases h1 : count = 1
      · simp only [h1, ↓reduceIte] at h
        have hx : x = start := by omega
        rw [hx]; exact h
      · simp only [h1, ↓reduceIte, Bool.and_eq_true] at h
        by_cases hlt : x < start + count / 2
        · exact ih start (count / 2) h.1 x hlo hlt
        · exact ih (start + count / 2) (count - count / 2) h.2 x (by omega) (by omega)

theorem checkRange_spec (p : Nat → Bool) (start count : Nat)
    (h : checkRange p start count = true) :
    ∀ x : Nat, start ≤ x → x < start + count → p x = true :=
  checkRangeFuel_spec p 12 start count h

end MuonNsDyadic
