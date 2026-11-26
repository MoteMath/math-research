/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`fp8-e4m3-lop3-circuits`)

Pure-`Init` (zero Mathlib) definitions for:
- OCP `FP8-E4M3FN` and OCP `FP4-E2M1` exact dyadic/integer value semantics;
- Exact integer RNE Voronoi certification for `1 / sqrt(x)` on `FP8-E4M3FN`;
- 3-input `LOP3` gates (`lop3.b32`), general `LOP3` DAGs, gate counts, topological depth,
  and semantic essential-variable counts;
- Wave 3A (`w3-fp8-e4m3-sfu-free`) GPU-synthesized exact 0-ULP `LOP3` circuits:
  - `e4m3RsqrtPosDag` (15 `LOP3`, depth 8, 126 positive finite codes),
  - `e4m3RsqrtFullDag` (33 `LOP3`, depth 14, all 256 codes),
  - `e4m3ExpDag` (67 `LOP3`, depth 9, 254 finite codes),
  - `e4m3GeluDag` (82 `LOP3`, depth 15, 254 finite codes),
  - `e4m3SiluDag` (93 `LOP3`, depth 16, 254 finite codes),
  - `e4m3E2m1SigProdDag` (14 `LOP3`) + `e4m3E2m1ExpSumDag` (10 `LOP3`) + 4 control `LOP3`
    = 28-`LOP3` exact zero-FP `FP8-E4M3FN × FP4-E2M1` aligned product circuit.
-/

namespace Fp8E4m3Lop3

/-! ## 1. OCP FP8-E4M3FN & FP4-E2M1 Exact Dyadic Semantics -/

/-- True iff `x : BitVec 8` is an OCP `FP8-E4M3FN` NaN code (`0x7F` or `0xFF`). -/
def isNanE4M3 (x : BitVec 8) : Bool :=
  (x &&& 0x7F#8) == 0x7F#8

/-- True iff `x : BitVec 8` is a finite OCP `FP8-E4M3FN` code (254 codes: all except `0x7F`, `0xFF`). -/
def isFiniteE4M3 (x : BitVec 8) : Bool :=
  !isNanE4M3 x

/-- True iff `x : BitVec 8` is a strictly positive finite OCP `FP8-E4M3FN` code (`0x01..0x7E`, 126 codes). -/
def isPosFiniteE4M3 (x : BitVec 8) : Bool :=
  1 ≤ x.toNat && x.toNat ≤ 126

/-- True iff `x : BitVec 8` is a strictly negative finite OCP `FP8-E4M3FN` code (`0x81..0xFE`, 126 codes). -/
def isNegFiniteE4M3 (x : BitVec 8) : Bool :=
  129 ≤ x.toNat && x.toNat ≤ 254

/-- True iff `x : BitVec 8` is signed zero (`0x00` or `0x80`). -/
def isZeroE4M3 (x : BitVec 8) : Bool :=
  (x &&& 0x7F#8) == 0x00#8

/-- Exact scaled magnitude `512 * |val(x)|` for finite OCP `FP8-E4M3FN` (since min subnormal is `2^-9 = 1/512`). -/
def e4m3MagScaled (x : BitVec 8) : Nat :=
  let e := (x.toNat >>> 3) &&& 0xF
  let m := x.toNat &&& 0x7
  if e == 0 then m else (8 + m) <<< (e - 1)

/-- Exact signed scaled value `512 * val(x) ∈ [-229376, 229376]` for finite OCP `FP8-E4M3FN`. -/
def e4m3ScaledVal (x : BitVec 8) : Int :=
  let mag : Int := (e4m3MagScaled x : Int)
  if x.getLsbD 7 then -mag else mag

/-- Exact 4-bit significand `s_a = ((e_a != 0) << 3) | m_a ∈ [0, 15]` of `FP8-E4M3FN`. -/
def e4m3Sig (x : BitVec 8) : Nat :=
  let e := (x.toNat >>> 3) &&& 0xF
  let m := x.toNat &&& 0x7
  (if e == 0 then 0 else 8) + m

/-- Exact 4-bit exponent field `e_a ∈ [0, 15]` of `FP8-E4M3FN`. -/
def e4m3ExpField (x : BitVec 8) : Nat :=
  (x.toNat >>> 3) &&& 0xF

/-- Exact scaled magnitude `2 * |val(b)| ∈ {0, 1, 2, 3, 4, 6, 8, 12}` of OCP `FP4-E2M1`. -/
def e2m1MagVal (b : BitVec 3) : Nat :=
  let e := (b.toNat >>> 1) &&& 0x3
  let m := b.toNat &&& 0x1
  if e == 0 then m else (2 + m) <<< (e - 1)

/-- Exact signed scaled value `2 * val(b) ∈ {-12..12}` of OCP `FP4-E2M1`. -/
def e2m1TwiceVal (b : BitVec 4) : Int :=
  let mag : Int := (e2m1MagVal (b.truncate 3) : Int)
  if b.getLsbD 3 then -mag else mag

/-- Exact 2-bit significand `s_b = ((e_b != 0) << 1) | m_b ∈ [0, 3]` of `FP4-E2M1`. -/
def e2m1Sig (b : BitVec 4) : Nat :=
  let e := (b.toNat >>> 1) &&& 0x3
  let m := b.toNat &&& 0x1
  (if e == 0 then 0 else 2) + m

/-- Exact 2-bit exponent field `e_b ∈ [0, 3]` of `FP4-E2M1`. -/
def e2m1ExpField (b : BitVec 4) : Nat :=
  (b.toNat >>> 1) &&& 0x3

/-- Exact pure-integer RNE Voronoi optimality condition for `y = RNE_E4M3(1 / sqrt(val(x)))`
    on positive finite `x ∈ [0x01, 0x7E]`.
    Since `val(x) = vx / 512` and the midpoint between adjacent FP8 codes `a, b` is
    `(va + vb) / 1024`, the condition `mid_lo ≤ 1/sqrt(val(x)) ≤ mid_hi` (strict when `y` is odd)
    is algebraically equivalent to `lo_num^2 * vx ≤ 1024^2 * 512 ≤ hi_num^2 * vx`. -/
def isExactRneRsqrtE4M3 (x y : BitVec 8) : Bool :=
  if !isPosFiniteE4M3 x || !isPosFiniteE4M3 y then
    false
  else
    let vx := e4m3MagScaled x
    let vy := e4m3MagScaled y
    let vPrev := e4m3MagScaled (BitVec.ofNat 8 (y.toNat - 1))
    let loNum := vPrev + vy
    let rhs := 536870912
    let loOk :=
      if y.toNat % 2 == 0 then loNum * loNum * vx ≤ rhs
      else loNum * loNum * vx < rhs
    let hiOk :=
      if y.toNat < 126 then
        let vNext := e4m3MagScaled (BitVec.ofNat 8 (y.toNat + 1))
        let hiNum := vy + vNext
        if y.toNat % 2 == 0 then rhs ≤ hiNum * hiNum * vx
        else rhs < hiNum * hiNum * vx
      else
        true
    loOk && hiOk

/-! ## 2. 3-Input `LOP3` Gate & General `LOP3` DAG Formalism -/

/-- Exact 3-input Boolean lookup gate (`lop3.b32`):
    `idx = 4*a + 2*b + c`, returning bit `idx` of `imm8`. -/
def lop3 (imm8 : BitVec 8) (a b c : Bool) : Bool :=
  let idx := (if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)
  imm8.getLsbD idx

/-- A single `LOP3` gate referencing three earlier wire indices `(a, b, c)` with truth table `imm8`. -/
structure Lop3Gate where
  a : Nat
  b : Nat
  c : Nat
  imm8 : BitVec 8
  deriving Repr, DecidableEq

/-- An output wire specification: either a Boolean constant or a wire index (`0..n-1` inputs, `n..` gates). -/
inductive Lop3Out where
  | const (b : Bool)
  | node (idx : Nat)
  deriving Repr, DecidableEq

/-- A multi-output `LOP3` DAG with primary input wires `0..7` and gate outputs `8..8+gates.length-1`. -/
structure Lop3Dag where
  gates : List Lop3Gate
  outputs : List Lop3Out
  deriving Repr, DecidableEq

/-- Evaluate all gates of a `LOP3` DAG into a `Nat` bitmask starting from initial input bitmask `initMask`
    at first gate index `nextIdx`. -/
def evalGatesMask : List Lop3Gate → Nat → Nat → Nat
  | [], _, mask => mask
  | g :: gs, nextIdx, mask =>
      let va := mask.testBit g.a
      let vb := mask.testBit g.b
      let vc := mask.testBit g.c
      let v := lop3 g.imm8 va vb vc
      let mask' := if v then mask ||| (1 <<< nextIdx) else mask
      evalGatesMask gs (nextIdx + 1) mask'

/-- Read a `Lop3Out` wire from an evaluated `Nat` bitmask. -/
def evalOutMask (mask : Nat) : Lop3Out → Bool
  | .const b => b
  | .node idx => mask.testBit idx

/-- Pack a list of `Lop3Out` bits (LSB first) into a `Nat` bitmask. -/
def packOutsMask (mask : Nat) : List Lop3Out → Nat → Nat
  | [], _ => 0
  | o :: os, bit =>
      let rest := packOutsMask mask os (bit + 1)
      if evalOutMask mask o then rest ||| (1 <<< bit) else rest

/-- Evaluate an 8-input, 8-output `Lop3Dag` on `x : BitVec 8`. -/
def evalLop3Dag8 (dag : Lop3Dag) (x : BitVec 8) : BitVec 8 :=
  let mask := evalGatesMask dag.gates 8 x.toNat
  BitVec.ofNat 8 (packOutsMask mask dag.outputs 0)

/-- Evaluate a 6-input, 6-output `Lop3Dag` (embedded in 8-wire space `0..7`) on `x : BitVec 6`. -/
def evalLop3Dag6 (dag : Lop3Dag) (x : BitVec 6) : BitVec 6 :=
  let mask := evalGatesMask dag.gates 8 x.toNat
  BitVec.ofNat 6 (packOutsMask mask dag.outputs 0)

/-- Evaluate a 6-input, 5-output `Lop3Dag` (embedded in 8-wire space `0..7`) on `x : BitVec 6`. -/
def evalLop3Dag5 (dag : Lop3Dag) (x : BitVec 6) : BitVec 5 :=
  let mask := evalGatesMask dag.gates 8 x.toNat
  BitVec.ofNat 5 (packOutsMask mask dag.outputs 0)

/-- Compute the topological depth array for wires `0..7` (depth 0) followed by each gate in `gates`. -/
def gateDepths (gates : List Lop3Gate) : Array Nat :=
  gates.foldl (fun acc g =>
    let da := acc.getD g.a 0
    let db := acc.getD g.b 0
    let dc := acc.getD g.c 0
    acc.push (1 + max da (max db dc)))
    #[0, 0, 0, 0, 0, 0, 0, 0]

/-- Exact topological `LOP3` depth of a `Lop3Dag` (max depth over its outputs). -/
def dagDepth (dag : Lop3Dag) : Nat :=
  let ds := gateDepths dag.gates
  dag.outputs.foldl (fun acc o =>
    match o with
    | .const _ => acc
    | .node idx => max acc (ds.getD idx 0)) 0

/-! ## 3. General `LOP3` Circuit Fan-In & Essential-Variable Definitions -/

/-- A general `n`-input single-output `LOP3` DAG (arbitrary gate sharing and fan-out).
    Primary inputs are wires `0..n-1`; gate `k` (`0 ≤ k < gates.length`) produces wire `n + k`
    and may reference any wire `< n + k`. -/
structure SingleOutLop3Dag (n : Nat) where
  gates : List Lop3Gate
  out : Lop3Out
  deriving Repr, DecidableEq

/-- Well-formedness: every gate `k` only references wires `< n + k`, and `out` references `< n + gates.length`. -/
def SingleOutLop3Dag.WellFormed {n : Nat} (d : SingleOutLop3Dag n) : Prop :=
  (∀ k (hk : k < d.gates.length),
    let g := d.gates[k]
    g.a < n + k ∧ g.b < n + k ∧ g.c < n + k) ∧
  (match d.out with
   | .const _ => True
   | .node idx => idx < n + d.gates.length)

/-- Evaluate a general `n`-input single-output `LOP3` DAG on `x : BitVec n`. -/
def SingleOutLop3Dag.eval {n : Nat} (d : SingleOutLop3Dag n) (x : BitVec n) : Bool :=
  let mask := evalGatesMask d.gates n x.toNat
  evalOutMask mask d.out

/-- Topological depth of a general `n`-input single-output `LOP3` DAG. -/
def SingleOutLop3Dag.depth {n : Nat} (d : SingleOutLop3Dag n) : Nat :=
  let ds := d.gates.foldl (fun acc g =>
    let da := acc.getD g.a 0
    let db := acc.getD g.b 0
    let dc := acc.getD g.c 0
    acc.push (1 + max da (max db dc)))
    (Array.replicate n 0)
  match d.out with
  | .const _ => 0
  | .node idx => ds.getD idx 0

/-- Flip bit `i` of `x : BitVec n`. -/
def flipBit {n : Nat} (x : BitVec n) (i : Fin n) : BitVec n :=
  x ^^^ (1#n <<< i.val)

/-- Variable `i : Fin n` is semantically essential for `f : BitVec n → Bool` on the full domain
    iff there exists an input `x` where flipping bit `i` changes `f x`. -/
def isEssentialVar {n : Nat} (f : BitVec n → Bool) (i : Fin n) : Prop :=
  ∃ x : BitVec n, f x ≠ f (flipBit x i)

/-- Binary-splitting existential check over `[base, base + 2^d)` (recursion depth `d`). -/
def anyPow2 (p : Nat → Bool) : Nat → Nat → Bool
  | 0, base => p base
  | d + 1, base => anyPow2 p d base || anyPow2 p d (base + 2 ^ d)

/-- Binary-splitting count over `[base, base + 2^d)` (recursion depth `d`). -/
def countPow2 (p : Nat → Bool) : Nat → Nat → Nat
  | 0, base => if p base then 1 else 0
  | d + 1, base => countPow2 p d base + countPow2 p d (base + 2 ^ d)

/-- Count of codes `x : BitVec 8` satisfying `p x = true` (recursion depth 8). -/
def countBv8 (p : BitVec 8 → Bool) : Nat :=
  countPow2 (fun k => p (BitVec.ofNat 8 k)) 8 0

/-- Variable `i : Fin n` is semantically essential for `f` restricted to care domain `P : BitVec n → Bool`
    iff there exists `x` with both `x` and `flipBit x i` in `P` where `f x ≠ f (flipBit x i)`. -/
def isEssentialVarOn {n : Nat} (P : BitVec n → Bool) (f : BitVec n → Bool) (i : Fin n) : Bool :=
  anyPow2 (fun k =>
    let x := BitVec.ofNat n k
    let x' := flipBit x i
    P x && P x' && (f x != f x')) n 0

/-- Count of essential variables of `f : BitVec n → Bool` on care domain `P`. -/
def essentialVarCountOn {n : Nat} (P : BitVec n → Bool) (f : BitVec n → Bool) : Nat :=
  ((List.finRange n).filter (isEssentialVarOn P f)).length

/-- Count of essential variables of `f : BitVec n → Bool` on the full domain `BitVec n`. -/
def essentialVarCount {n : Nat} (f : BitVec n → Bool) : Nat :=
  essentialVarCountOn (fun _ => true) f

/-- Extract bit `k` of an 8-bit function `f : BitVec 8 → BitVec 8`. -/
def outBit8 (f : BitVec 8 → BitVec 8) (k : Fin 8) (x : BitVec 8) : Bool :=
  (f x).getLsbD k.val

/-! ## 4. Frontier 1: Wave 3A GPU-Synthesized OCP `FP8-E4M3FN` `LOP3` Circuits -/

/-- Exact 15-LOP3 (depth 8) positive FP8-E4M3FN rsqrt circuit (0x01..0x7E). -/
def e4m3RsqrtPosDag : Lop3Dag where
  gates := [
    ⟨2, 1, 0, 0xFE#8⟩,
    ⟨3, 4, 8, 0x13#8⟩,
    ⟨0, 5, 9, 0x66#8⟩,
    ⟨5, 6, 9, 0x23#8⟩,
    ⟨3, 10, 11, 0x08#8⟩,
    ⟨1, 2, 12, 0xA7#8⟩,
    ⟨1, 2, 3, 0x4D#8⟩,
    ⟨0, 13, 14, 0xCA#8⟩,
    ⟨2, 3, 8, 0x0B#8⟩,
    ⟨12, 1, 16, 0x3A#8⟩,
    ⟨0, 2, 17, 0x16#8⟩,
    ⟨18, 0, 3, 0xE8#8⟩,
    ⟨16, 10, 11, 0x80#8⟩,
    ⟨20, 4, 19, 0x56#8⟩,
    ⟨5, 6, 9, 0x9C#8⟩
  ]
  outputs := [
    .node 15,
    .node 17,
    .node 19,
    .node 21,
    .node 10,
    .node 22,
    .node 11,
    .const false
  ]

/-- Exact 33-LOP3 (depth 14) full-domain FP8-E4M3FN rsqrt circuit (all 256 codes). -/
def e4m3RsqrtFullDag : Lop3Dag where
  gates := [
    ⟨2, 1, 0, 0xB2#8⟩,
    ⟨1, 4, 8, 0x81#8⟩,
    ⟨0, 6, 9, 0xB9#8⟩,
    ⟨5, 6, 10, 0x3D#8⟩,
    ⟨11, 4, 5, 0xD2#8⟩,
    ⟨5, 10, 6, 0xCA#8⟩,
    ⟨6, 12, 13, 0x25#8⟩,
    ⟨1, 5, 14, 0x87#8⟩,
    ⟨15, 0, 2, 0xE0#8⟩,
    ⟨1, 2, 16, 0x92#8⟩,
    ⟨2, 1, 0, 0x09#8⟩,
    ⟨4, 17, 18, 0xF6#8⟩,
    ⟨1, 19, 14, 0x2D#8⟩,
    ⟨20, 0, 2, 0xF2#8⟩,
    ⟨3, 16, 21, 0xCA#8⟩,
    ⟨7, 0, 22, 0xFA#8⟩,
    ⟨4, 2, 1, 0x35#8⟩,
    ⟨2, 24, 14, 0x8D#8⟩,
    ⟨3, 17, 25, 0xCA#8⟩,
    ⟨7, 0, 26, 0xFA#8⟩,
    ⟨3, 13, 12, 0xCA#8⟩,
    ⟨7, 0, 28, 0xFA#8⟩,
    ⟨6, 28, 14, 0x8B#8⟩,
    ⟨7, 0, 30, 0xFA#8⟩,
    ⟨3, 29, 31, 0xF8#8⟩,
    ⟨32, 18, 27, 0xB4#8⟩,
    ⟨1, 4, 16, 0x96#8⟩,
    ⟨6, 4, 19, 0xCA#8⟩,
    ⟨5, 4, 35, 0xCA#8⟩,
    ⟨3, 34, 36, 0xCA#8⟩,
    ⟨7, 0, 37, 0xFA#8⟩,
    ⟨3, 4, 9, 0x23#8⟩,
    ⟨39, 5, 7, 0xBE#8⟩
  ]
  outputs := [
    .node 23,
    .node 27,
    .node 33,
    .node 38,
    .node 40,
    .node 29,
    .node 31,
    .const false
  ]

/-- Exact 67-LOP3 (depth 9) FP8-E4M3FN exp circuit (254 finite codes). -/
def e4m3ExpDag : Lop3Dag where
  gates := [
    ⟨2, 1, 0, 0x35#8⟩,
    ⟨2, 1, 0, 0x1E#8⟩,
    ⟨7, 8, 9, 0xCA#8⟩,
    ⟨2, 1, 0, 0x3E#8⟩,
    ⟨2, 1, 0, 0xF8#8⟩,
    ⟨2, 7, 12, 0x81#8⟩,
    ⟨0, 11, 13, 0x99#8⟩,
    ⟨0, 2, 14, 0x85#8⟩,
    ⟨1, 2, 15, 0xA7#8⟩,
    ⟨3, 10, 16, 0xCA#8⟩,
    ⟨4, 5, 17, 0x02#8⟩,
    ⟨2, 1, 0, 0x0E#8⟩,
    ⟨0, 1, 13, 0x9A#8⟩,
    ⟨0, 19, 20, 0xAE#8⟩,
    ⟨3, 15, 21, 0xCA#8⟩,
    ⟨0, 15, 21, 0x52#8⟩,
    ⟨0, 7, 12, 0x99#8⟩,
    ⟨3, 23, 24, 0xCA#8⟩,
    ⟨4, 22, 25, 0xCA#8⟩,
    ⟨0, 19, 13, 0x91#8⟩,
    ⟨0, 7, 27, 0x44#8⟩,
    ⟨3, 9, 28, 0xDA#8⟩,
    ⟨4, 29, 0, 0xC0#8⟩,
    ⟨5, 26, 30, 0xCA#8⟩,
    ⟨6, 18, 31, 0xCA#8⟩,
    ⟨7, 7, 7, 0x01#8⟩,
    ⟨2, 1, 0, 0xEB#8⟩,
    ⟨7, 19, 34, 0xCA#8⟩,
    ⟨3, 35, 15, 0xCA#8⟩,
    ⟨4, 33, 36, 0xCA#8⟩,
    ⟨5, 33, 37, 0xCA#8⟩,
    ⟨3, 20, 14, 0xCA#8⟩,
    ⟨0, 10, 24, 0xEA#8⟩,
    ⟨3, 7, 40, 0x5C#8⟩,
    ⟨3, 12, 41, 0x56#8⟩,
    ⟨4, 39, 42, 0xCA#8⟩,
    ⟨0, 20, 11, 0x11#8⟩,
    ⟨3, 33, 44, 0xCA#8⟩,
    ⟨4, 7, 45, 0x40#8⟩,
    ⟨5, 43, 46, 0xCA#8⟩,
    ⟨6, 38, 47, 0xCA#8⟩,
    ⟨7, 2, 1, 0x0E#8⟩,
    ⟨2, 20, 49, 0xA6#8⟩,
    ⟨3, 50, 20, 0xCA#8⟩,
    ⟨4, 33, 51, 0xCA#8⟩,
    ⟨5, 33, 52, 0xCA#8⟩,
    ⟨3, 14, 13, 0xCA#8⟩,
    ⟨4, 54, 41, 0xCA#8⟩,
    ⟨5, 55, 46, 0xCA#8⟩,
    ⟨6, 53, 56, 0xCA#8⟩,
    ⟨3, 27, 14, 0xC5#8⟩,
    ⟨4, 33, 58, 0xCA#8⟩,
    ⟨5, 33, 59, 0xCA#8⟩,
    ⟨0, 3, 13, 0x66#8⟩,
    ⟨4, 61, 33, 0xCA#8⟩,
    ⟨5, 46, 62, 0xA3#8⟩,
    ⟨6, 60, 63, 0xCA#8⟩,
    ⟨3, 49, 11, 0xCA#8⟩,
    ⟨4, 33, 65, 0xCA#8⟩,
    ⟨5, 33, 66, 0xCA#8⟩,
    ⟨2, 40, 42, 0x06#8⟩,
    ⟨4, 5, 68, 0xBF#8⟩,
    ⟨6, 67, 69, 0xCA#8⟩,
    ⟨4, 33, 45, 0xCA#8⟩,
    ⟨5, 33, 71, 0xCA#8⟩,
    ⟨6, 69, 72, 0xAD#8⟩,
    ⟨6, 7, 69, 0x31#8⟩
  ]
  outputs := [
    .node 32,
    .node 48,
    .node 57,
    .node 64,
    .node 70,
    .node 73,
    .node 74,
    .const false
  ]

/-- Exact 82-LOP3 (depth 15) FP8-E4M3FN gelu circuit (254 finite codes). -/
def e4m3GeluDag : Lop3Dag where
  gates := [
    ⟨2, 1, 0, 0x8B#8⟩,
    ⟨2, 1, 0, 0x65#8⟩,
    ⟨2, 1, 0, 0x2C#8⟩,
    ⟨3, 9, 10, 0xCA#8⟩,
    ⟨1, 0, 1, 0x24#8⟩,
    ⟨1, 3, 9, 0x7B#8⟩,
    ⟨11, 12, 13, 0x69#8⟩,
    ⟨0, 8, 14, 0x82#8⟩,
    ⟨4, 15, 12, 0xCA#8⟩,
    ⟨3, 9, 12, 0x1C#8⟩,
    ⟨0, 16, 17, 0x80#8⟩,
    ⟨5, 0, 18, 0x0A#8⟩,
    ⟨2, 1, 0, 0x36#8⟩,
    ⟨0, 3, 17, 0x88#8⟩,
    ⟨20, 15, 21, 0x96#8⟩,
    ⟨4, 22, 11, 0xCA#8⟩,
    ⟨4, 14, 1, 0xCA#8⟩,
    ⟨5, 23, 24, 0xCA#8⟩,
    ⟨6, 19, 25, 0xCA#8⟩,
    ⟨3, 2, 1, 0xC7#8⟩,
    ⟨2, 12, 17, 0x9D#8⟩,
    ⟨2, 27, 28, 0x26#8⟩,
    ⟨2, 1, 0, 0x86#8⟩,
    ⟨0, 29, 30, 0x2F#8⟩,
    ⟨3, 8, 20, 0xCA#8⟩,
    ⟨0, 1, 15, 0x9C#8⟩,
    ⟨32, 33, 29, 0xC6#8⟩,
    ⟨4, 31, 34, 0xCA#8⟩,
    ⟨5, 35, 16, 0xCA#8⟩,
    ⟨6, 0, 36, 0xCA#8⟩,
    ⟨7, 26, 37, 0xCA#8⟩,
    ⟨2, 12, 17, 0x6E#8⟩,
    ⟨4, 39, 27, 0xCA#8⟩,
    ⟨3, 35, 40, 0x02#8⟩,
    ⟨5, 0, 41, 0x0A#8⟩,
    ⟨1, 3, 30, 0x89#8⟩,
    ⟨4, 13, 43, 0xCA#8⟩,
    ⟨0, 1, 14, 0xC6#8⟩,
    ⟨4, 45, 2, 0xCA#8⟩,
    ⟨5, 44, 46, 0xCA#8⟩,
    ⟨6, 42, 47, 0xCA#8⟩,
    ⟨4, 17, 32, 0xCA#8⟩,
    ⟨2, 1, 0, 0x78#8⟩,
    ⟨4, 33, 50, 0xCA#8⟩,
    ⟨5, 49, 51, 0xCA#8⟩,
    ⟨6, 1, 52, 0xCA#8⟩,
    ⟨7, 48, 53, 0xCA#8⟩,
    ⟨1, 2, 45, 0xC6#8⟩,
    ⟨4, 55, 3, 0xCA#8⟩,
    ⟨46, 51, 56, 0x9A#8⟩,
    ⟨3, 4, 39, 0x4C#8⟩,
    ⟨56, 57, 58, 0x92#8⟩,
    ⟨8, 27, 59, 0x40#8⟩,
    ⟨5, 0, 60, 0x0A#8⟩,
    ⟨4, 21, 29, 0xCA#8⟩,
    ⟨5, 62, 56, 0xCA#8⟩,
    ⟨6, 61, 63, 0xCA#8⟩,
    ⟨3, 30, 55, 0xAC#8⟩,
    ⟨1, 55, 65, 0x14#8⟩,
    ⟨4, 65, 66, 0xCA#8⟩,
    ⟨5, 67, 57, 0xCA#8⟩,
    ⟨6, 2, 68, 0xCA#8⟩,
    ⟨7, 64, 69, 0xCA#8⟩,
    ⟨5, 40, 59, 0xCA#8⟩,
    ⟨50, 29, 71, 0x01#8⟩,
    ⟨4, 43, 28, 0x1A#8⟩,
    ⟨5, 73, 58, 0xCA#8⟩,
    ⟨6, 72, 74, 0xCA#8⟩,
    ⟨6, 3, 71, 0xCA#8⟩,
    ⟨7, 75, 76, 0xCA#8⟩,
    ⟨0, 1, 61, 0x02#8⟩,
    ⟨0, 62, 73, 0xEE#8⟩,
    ⟨3, 4, 39, 0x80#8⟩,
    ⟨5, 79, 80, 0xCA#8⟩,
    ⟨6, 78, 81, 0xCA#8⟩,
    ⟨3, 4, 76, 0xC6#8⟩,
    ⟨7, 82, 83, 0xCA#8⟩,
    ⟨5, 6, 80, 0x37#8⟩,
    ⟨7, 85, 0, 0xC0#8⟩,
    ⟨4, 84, 86, 0xD9#8⟩,
    ⟨87, 5, 7, 0x48#8⟩,
    ⟨7, 6, 7, 0x04#8⟩
  ]
  outputs := [
    .node 38,
    .node 54,
    .node 70,
    .node 77,
    .node 84,
    .node 88,
    .node 89,
    .node 86
  ]

/-- Exact 93-LOP3 (depth 16) FP8-E4M3FN silu circuit (254 finite codes). -/
def e4m3SiluDag : Lop3Dag where
  gates := [
    ⟨7, 0, 7, 0x04#8⟩,
    ⟨2, 1, 0, 0x1C#8⟩,
    ⟨2, 1, 0, 0xE1#8⟩,
    ⟨2, 7, 10, 0x83#8⟩,
    ⟨0, 9, 11, 0x11#8⟩,
    ⟨0, 7, 12, 0xB8#8⟩,
    ⟨3, 8, 13, 0xCA#8⟩,
    ⟨2, 1, 0, 0x26#8⟩,
    ⟨7, 11, 15, 0x1A#8⟩,
    ⟨2, 1, 0, 0x73#8⟩,
    ⟨7, 2, 7, 0x04#8⟩,
    ⟨9, 17, 18, 0x59#8⟩,
    ⟨1, 19, 11, 0x81#8⟩,
    ⟨7, 17, 10, 0xC4#8⟩,
    ⟨20, 15, 21, 0xB1#8⟩,
    ⟨13, 16, 22, 0xE9#8⟩,
    ⟨7, 1, 0, 0xC6#8⟩,
    ⟨23, 19, 24, 0xD4#8⟩,
    ⟨7, 2, 1, 0x09#8⟩,
    ⟨25, 16, 26, 0x65#8⟩,
    ⟨3, 23, 27, 0xCA#8⟩,
    ⟨4, 14, 28, 0xCA#8⟩,
    ⟨5, 8, 29, 0xCA#8⟩,
    ⟨0, 13, 16, 0xE2#8⟩,
    ⟨3, 25, 31, 0xCA#8⟩,
    ⟨27, 31, 22, 0x9A#8⟩,
    ⟨7, 15, 10, 0xA9#8⟩,
    ⟨33, 20, 34, 0x91#8⟩,
    ⟨1, 2, 35, 0x39#8⟩,
    ⟨0, 20, 36, 0x4E#8⟩,
    ⟨3, 33, 37, 0xCA#8⟩,
    ⟨4, 32, 38, 0xCA#8⟩,
    ⟨3, 2, 0, 0x6A#8⟩,
    ⟨4, 40, 24, 0xCA#8⟩,
    ⟨5, 39, 41, 0xCA#8⟩,
    ⟨6, 30, 42, 0xCA#8⟩,
    ⟨7, 1, 7, 0x04#8⟩,
    ⟨2, 11, 15, 0x3D#8⟩,
    ⟨0, 10, 45, 0x9D#8⟩,
    ⟨0, 46, 36, 0x88#8⟩,
    ⟨0, 1, 47, 0x44#8⟩,
    ⟨3, 48, 22, 0xCA#8⟩,
    ⟨4, 44, 49, 0xCA#8⟩,
    ⟨5, 44, 50, 0xCA#8⟩,
    ⟨0, 18, 26, 0x64#8⟩,
    ⟨3, 52, 35, 0xCA#8⟩,
    ⟨3, 21, 16, 0xCA#8⟩,
    ⟨4, 53, 54, 0xCA#8⟩,
    ⟨3, 19, 1, 0xCA#8⟩,
    ⟨0, 2, 34, 0xAC#8⟩,
    ⟨4, 56, 57, 0xCA#8⟩,
    ⟨5, 55, 58, 0xCA#8⟩,
    ⟨6, 51, 59, 0xCA#8⟩,
    ⟨0, 1, 12, 0x75#8⟩,
    ⟨1, 35, 61, 0x42#8⟩,
    ⟨3, 62, 46, 0xCA#8⟩,
    ⟨4, 18, 63, 0xCA#8⟩,
    ⟨5, 18, 64, 0xCA#8⟩,
    ⟨3, 26, 36, 0xCA#8⟩,
    ⟨3, 20, 34, 0xCA#8⟩,
    ⟨4, 66, 67, 0xCA#8⟩,
    ⟨35, 36, 56, 0x63#8⟩,
    ⟨0, 1, 19, 0xBF#8⟩,
    ⟨0, 3, 70, 0x98#8⟩,
    ⟨4, 69, 71, 0xCA#8⟩,
    ⟨5, 68, 72, 0xCA#8⟩,
    ⟨6, 65, 73, 0xCA#8⟩,
    ⟨3, 7, 3, 0x20#8⟩,
    ⟨1, 10, 26, 0x48#8⟩,
    ⟨3, 45, 76, 0xCA#8⟩,
    ⟨4, 75, 77, 0xCA#8⟩,
    ⟨5, 75, 78, 0xCA#8⟩,
    ⟨3, 26, 11, 0x7A#8⟩,
    ⟨3, 12, 61, 0xCA#8⟩,
    ⟨4, 80, 81, 0xCA#8⟩,
    ⟨3, 4, 70, 0x5C#8⟩,
    ⟨5, 82, 83, 0xCA#8⟩,
    ⟨6, 79, 84, 0xCA#8⟩,
    ⟨3, 47, 76, 0xCA#8⟩,
    ⟨4, 7, 86, 0x3A#8⟩,
    ⟨4, 5, 87, 0xA2#8⟩,
    ⟨3, 7, 2, 0x32#8⟩,
    ⟨2, 3, 81, 0x2B#8⟩,
    ⟨4, 89, 90, 0xCA#8⟩,
    ⟨4, 3, 4, 0x80#8⟩,
    ⟨5, 91, 92, 0xCA#8⟩,
    ⟨6, 88, 93, 0xCA#8⟩,
    ⟨7, 86, 91, 0x28#8⟩,
    ⟨5, 7, 95, 0x3A#8⟩,
    ⟨4, 5, 90, 0xC4#8⟩,
    ⟨6, 96, 97, 0xCA#8⟩,
    ⟨2, 7, 65, 0x31#8⟩,
    ⟨6, 99, 0, 0xC0#8⟩
  ]
  outputs := [
    .node 43,
    .node 60,
    .node 74,
    .node 85,
    .node 94,
    .node 98,
    .node 100,
    .node 7
  ]

/-! ## 5. Exact 60-Digit `mpmath` RNE Reference Tables (`exp`, `gelu`, `silu`) -/

/-- Exact 60-digit mpmath RNE saturated OCP FP8-E4M3FN exp table. -/
def e4m3ExpRefTable : Array (BitVec 8) := #[
  0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8,
  0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x39#8, 0x39#8, 0x39#8, 0x39#8, 0x39#8, 0x39#8, 0x39#8, 0x39#8,
  0x39#8, 0x39#8, 0x39#8, 0x3A#8, 0x3A#8, 0x3A#8, 0x3A#8, 0x3A#8, 0x3A#8, 0x3B#8, 0x3B#8, 0x3B#8, 0x3C#8, 0x3C#8, 0x3C#8, 0x3D#8,
  0x3D#8, 0x3E#8, 0x3F#8, 0x40#8, 0x40#8, 0x41#8, 0x42#8, 0x42#8, 0x43#8, 0x44#8, 0x46#8, 0x48#8, 0x49#8, 0x4A#8, 0x4C#8, 0x4D#8,
  0x4F#8, 0x51#8, 0x54#8, 0x58#8, 0x5A#8, 0x5D#8, 0x60#8, 0x63#8, 0x66#8, 0x6B#8, 0x71#8, 0x77#8, 0x7D#8, 0x7E#8, 0x7E#8, 0x7E#8,
  0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8,
  0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8,
  0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7E#8, 0x7F#8,
  0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8, 0x38#8,
  0x38#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x37#8, 0x36#8, 0x36#8, 0x36#8,
  0x36#8, 0x36#8, 0x36#8, 0x35#8, 0x35#8, 0x35#8, 0x35#8, 0x35#8, 0x34#8, 0x34#8, 0x34#8, 0x33#8, 0x33#8, 0x33#8, 0x32#8, 0x32#8,
  0x32#8, 0x31#8, 0x31#8, 0x30#8, 0x2F#8, 0x2E#8, 0x2D#8, 0x2D#8, 0x2C#8, 0x2A#8, 0x29#8, 0x28#8, 0x26#8, 0x25#8, 0x23#8, 0x22#8,
  0x21#8, 0x1D#8, 0x1B#8, 0x18#8, 0x15#8, 0x12#8, 0x0F#8, 0x0C#8, 0x09#8, 0x06#8, 0x03#8, 0x02#8, 0x01#8, 0x01#8, 0x00#8, 0x00#8,
  0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
  0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
  0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x7F#8
]

/-- Exact 60-digit mpmath RNE OCP FP8-E4M3FN gelu (exact erf) table. -/
def e4m3GeluRefTable : Array (BitVec 8) := #[
  0x00#8, 0x01#8, 0x01#8, 0x02#8, 0x02#8, 0x03#8, 0x03#8, 0x04#8, 0x04#8, 0x05#8, 0x05#8, 0x06#8, 0x06#8, 0x07#8, 0x07#8, 0x08#8,
  0x08#8, 0x09#8, 0x0A#8, 0x0B#8, 0x0C#8, 0x0E#8, 0x0F#8, 0x10#8, 0x10#8, 0x12#8, 0x13#8, 0x14#8, 0x15#8, 0x16#8, 0x17#8, 0x18#8,
  0x19#8, 0x1A#8, 0x1B#8, 0x1D#8, 0x1E#8, 0x1F#8, 0x20#8, 0x21#8, 0x22#8, 0x23#8, 0x24#8, 0x26#8, 0x28#8, 0x29#8, 0x29#8, 0x2A#8,
  0x2B#8, 0x2D#8, 0x2F#8, 0x30#8, 0x31#8, 0x32#8, 0x33#8, 0x34#8, 0x35#8, 0x38#8, 0x39#8, 0x3A#8, 0x3B#8, 0x3C#8, 0x3D#8, 0x3F#8,
  0x40#8, 0x41#8, 0x42#8, 0x43#8, 0x44#8, 0x45#8, 0x46#8, 0x47#8, 0x48#8, 0x49#8, 0x4A#8, 0x4B#8, 0x4C#8, 0x4D#8, 0x4E#8, 0x4F#8,
  0x50#8, 0x51#8, 0x52#8, 0x53#8, 0x54#8, 0x55#8, 0x56#8, 0x57#8, 0x58#8, 0x59#8, 0x5A#8, 0x5B#8, 0x5C#8, 0x5D#8, 0x5E#8, 0x5F#8,
  0x60#8, 0x61#8, 0x62#8, 0x63#8, 0x64#8, 0x65#8, 0x66#8, 0x67#8, 0x68#8, 0x69#8, 0x6A#8, 0x6B#8, 0x6C#8, 0x6D#8, 0x6E#8, 0x6F#8,
  0x70#8, 0x71#8, 0x72#8, 0x73#8, 0x74#8, 0x75#8, 0x76#8, 0x77#8, 0x78#8, 0x79#8, 0x7A#8, 0x7B#8, 0x7C#8, 0x7D#8, 0x7E#8, 0x7F#8,
  0x80#8, 0x80#8, 0x81#8, 0x81#8, 0x82#8, 0x82#8, 0x83#8, 0x83#8, 0x84#8, 0x84#8, 0x85#8, 0x85#8, 0x86#8, 0x86#8, 0x87#8, 0x87#8,
  0x88#8, 0x89#8, 0x8A#8, 0x8B#8, 0x8C#8, 0x8C#8, 0x8D#8, 0x8E#8, 0x8F#8, 0x90#8, 0x91#8, 0x92#8, 0x93#8, 0x94#8, 0x95#8, 0x96#8,
  0x96#8, 0x98#8, 0x99#8, 0x99#8, 0x9A#8, 0x9B#8, 0x9C#8, 0x9C#8, 0x9D#8, 0x9E#8, 0x9F#8, 0xA0#8, 0xA0#8, 0xA1#8, 0xA1#8, 0xA2#8,
  0xA2#8, 0xA2#8, 0xA3#8, 0xA3#8, 0xA3#8, 0xA3#8, 0xA3#8, 0xA2#8, 0xA2#8, 0xA1#8, 0xA0#8, 0x9F#8, 0x9D#8, 0x9B#8, 0x99#8, 0x97#8,
  0x94#8, 0x8E#8, 0x88#8, 0x84#8, 0x82#8, 0x81#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8,
  0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
  0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
  0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x7F#8
]

/-- Exact 60-digit mpmath RNE OCP FP8-E4M3FN silu table. -/
def e4m3SiluRefTable : Array (BitVec 8) := #[
  0x00#8, 0x01#8, 0x01#8, 0x02#8, 0x02#8, 0x03#8, 0x03#8, 0x04#8, 0x04#8, 0x05#8, 0x05#8, 0x06#8, 0x06#8, 0x07#8, 0x07#8, 0x08#8,
  0x08#8, 0x09#8, 0x0A#8, 0x0B#8, 0x0C#8, 0x0D#8, 0x0E#8, 0x0F#8, 0x10#8, 0x11#8, 0x12#8, 0x13#8, 0x15#8, 0x16#8, 0x17#8, 0x18#8,
  0x18#8, 0x1A#8, 0x1B#8, 0x1C#8, 0x1D#8, 0x1E#8, 0x20#8, 0x20#8, 0x21#8, 0x22#8, 0x24#8, 0x25#8, 0x26#8, 0x28#8, 0x29#8, 0x29#8,
  0x2A#8, 0x2B#8, 0x2D#8, 0x2F#8, 0x30#8, 0x31#8, 0x32#8, 0x33#8, 0x34#8, 0x36#8, 0x38#8, 0x39#8, 0x3A#8, 0x3B#8, 0x3C#8, 0x3D#8,
  0x3E#8, 0x40#8, 0x41#8, 0x42#8, 0x43#8, 0x45#8, 0x46#8, 0x47#8, 0x48#8, 0x49#8, 0x4A#8, 0x4B#8, 0x4C#8, 0x4D#8, 0x4E#8, 0x4F#8,
  0x50#8, 0x51#8, 0x52#8, 0x53#8, 0x54#8, 0x55#8, 0x56#8, 0x57#8, 0x58#8, 0x59#8, 0x5A#8, 0x5B#8, 0x5C#8, 0x5D#8, 0x5E#8, 0x5F#8,
  0x60#8, 0x61#8, 0x62#8, 0x63#8, 0x64#8, 0x65#8, 0x66#8, 0x67#8, 0x68#8, 0x69#8, 0x6A#8, 0x6B#8, 0x6C#8, 0x6D#8, 0x6E#8, 0x6F#8,
  0x70#8, 0x71#8, 0x72#8, 0x73#8, 0x74#8, 0x75#8, 0x76#8, 0x77#8, 0x78#8, 0x79#8, 0x7A#8, 0x7B#8, 0x7C#8, 0x7D#8, 0x7E#8, 0x7F#8,
  0x80#8, 0x80#8, 0x81#8, 0x81#8, 0x82#8, 0x82#8, 0x83#8, 0x83#8, 0x84#8, 0x84#8, 0x85#8, 0x85#8, 0x86#8, 0x86#8, 0x87#8, 0x87#8,
  0x88#8, 0x89#8, 0x8A#8, 0x8B#8, 0x8C#8, 0x8D#8, 0x8E#8, 0x8F#8, 0x90#8, 0x91#8, 0x92#8, 0x93#8, 0x93#8, 0x94#8, 0x95#8, 0x96#8,
  0x97#8, 0x98#8, 0x99#8, 0x9A#8, 0x9B#8, 0x9C#8, 0x9C#8, 0x9D#8, 0x9E#8, 0x9F#8, 0xA0#8, 0xA1#8, 0xA2#8, 0xA2#8, 0xA3#8, 0xA4#8,
  0xA4#8, 0xA5#8, 0xA6#8, 0xA7#8, 0xA7#8, 0xA8#8, 0xA8#8, 0xA8#8, 0xA9#8, 0xA9#8, 0xA9#8, 0xA9#8, 0xA9#8, 0xA9#8, 0xA8#8, 0xA8#8,
  0xA7#8, 0xA6#8, 0xA4#8, 0xA3#8, 0xA1#8, 0xA0#8, 0x9D#8, 0x9B#8, 0x99#8, 0x95#8, 0x91#8, 0x8B#8, 0x88#8, 0x85#8, 0x83#8, 0x82#8,
  0x81#8, 0x81#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8,
  0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8,
  0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x7F#8
]

/-! ## 6. Frontier 3: 28-`LOP3` Exact Zero-FP `FP8-E4M3FN × FP4-E2M1` Aligned Product -/

/-- Exact 14-LOP3 4-bit × 2-bit significand product P[5:0] = s_a * s_b ∈ [0, 45]. -/
def e4m3E2m1SigProdDag : Lop3Dag where
  gates := [
    ⟨4, 0, 4, 0x80#8⟩,
    ⟨4, 0, 1, 0x6C#8⟩,
    ⟨0, 5, 9, 0x9A#8⟩,
    ⟨1, 5, 8, 0x40#8⟩,
    ⟨11, 2, 4, 0x78#8⟩,
    ⟨0, 1, 2, 0x92#8⟩,
    ⟨13, 0, 3, 0x96#8⟩,
    ⟨4, 14, 2, 0xCA#8⟩,
    ⟨4, 3, 4, 0x80#8⟩,
    ⟨5, 15, 16, 0xCA#8⟩,
    ⟨2, 3, 14, 0x18#8⟩,
    ⟨4, 18, 3, 0xCA#8⟩,
    ⟨5, 19, 0, 0xC0#8⟩,
    ⟨3, 5, 19, 0x40#8⟩
  ]
  outputs := [
    .node 8,
    .node 10,
    .node 12,
    .node 17,
    .node 20,
    .node 21
  ]

/-- Exact 10-LOP3 5-bit aligned exponent sum E_sum[4:0] = max(e_a,1) + max(e_b,1) - 1 ∈ [1, 17]. -/
def e4m3E2m1ExpSumDag : Lop3Dag where
  gates := [
    ⟨0, 4, 5, 0xD2#8⟩,
    ⟨0, 3, 8, 0xA9#8⟩,
    ⟨2, 8, 9, 0xCA#8⟩,
    ⟨1, 8, 10, 0xCA#8⟩,
    ⟨0, 4, 5, 0x57#8⟩,
    ⟨4, 5, 10, 0xC4#8⟩,
    ⟨1, 12, 13, 0xCA#8⟩,
    ⟨1, 2, 12, 0x9C#8⟩,
    ⟨2, 3, 15, 0x9C#8⟩,
    ⟨0, 3, 16, 0x44#8⟩
  ]
  outputs := [
    .node 11,
    .node 14,
    .node 15,
    .node 16,
    .node 17
  ]

/-- 1-`LOP3` sign XOR (`a7 ^ b3`, `imm8 = 0x3C`). -/
def e4m3E2m1SignLop3 (a : BitVec 8) (b : BitVec 4) : Bool :=
  lop3 0x3C#8 (a.getLsbD 7) (b.getLsbD 3) false

/-- 2-`LOP3` implicit-bit flag `e_a_nz = e_a0 | e_a1 | e_a2 | e_a3` (`0xFE`, `0xFC`). -/
def e4m3EaNzLop3 (a : BitVec 8) : Bool :=
  let t := lop3 0xFE#8 (a.getLsbD 3) (a.getLsbD 4) (a.getLsbD 5)
  lop3 0xFC#8 t (a.getLsbD 6) false

/-- 1-`LOP3` implicit-bit flag `e_b_nz = e_b0 | e_b1` (`0xFC`). -/
def e2m1EbNzLop3 (b : BitVec 4) : Bool :=
  lop3 0xFC#8 (b.getLsbD 1) (b.getLsbD 2) false

/-- Total `LOP3` gate count of the exact unrounded aligned `E4M3 × E2M1` product circuit:
    `1 (sign) + 2 (e_a_nz) + 1 (e_b_nz) + 14 (P[5:0]) + 10 (E_sum[4:0]) = 28`. -/
def e4m3TimesE2m1GateCount : Nat :=
  1 + 2 + 1 + e4m3E2m1SigProdDag.gates.length + e4m3E2m1ExpSumDag.gates.length

/-- Complete 28-`LOP3` zero-FP `FP8-E4M3FN × FP4-E2M1` exact aligned product returning
    `(sign, P[5:0], E_sum[4:0])`. -/
def e4m3TimesE2m1Aligned28 (a : BitVec 8) (b : BitVec 4) : Bool × BitVec 6 × BitVec 5 :=
  let sgn := e4m3E2m1SignLop3 a b
  let eanz := e4m3EaNzLop3 a
  let ebnz := e2m1EbNzLop3 b
  let sigIn : BitVec 6 := BitVec.ofNat 6 (
    (a.toNat &&& 0x7) |||
    (if eanz then 8 else 0) |||
    ((b.toNat &&& 0x1) <<< 4) |||
    (if ebnz then 32 else 0))
  let expIn : BitVec 6 := BitVec.ofNat 6 (
    ((a.toNat >>> 3) &&& 0xF) |||
    (((b.toNat >>> 1) &&& 0x3) <<< 4))
  (sgn, evalLop3Dag6 e4m3E2m1SigProdDag sigIn, evalLop3Dag5 e4m3E2m1ExpSumDag expIn)

/-- Signed integer reconstruction `(-1)^sign * P * 2^(E_sum - 1)` of the 28-`LOP3` aligned product
    (representing `1024 * val(a) * val(b)`). -/
def alignedProdScaled1024 (res : Bool × BitVec 6 × BitVec 5) : Int :=
  let (sgn, p, esum) := res
  let mag : Int := ((p.toNat <<< (esum.toNat - 1)) : Int)
  if sgn then -mag else mag

end Fp8E4m3Lop3
