/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Sub-Byte E2M1 & Minimal-`LOP3` Circuits (`subbyte-e2m1-lop3`)

Pure-`Init` (zero Mathlib) definitions of:
- exact OCP MXFP4 (E2M1) nibble decoding `e2m1TwiceVal`,
- exact PTX 3-input Boolean lookup gate `lop3`,
- the 0-`LOP3` 2-trit / 4-bit → E2M1 unpacker (`unpack2t4b`) and encoder (`encode2t4b`),
- the optimal 4-`LOP3` 3-trit / 5-bit → E2M1 unpacker (`unpack3t5b`) and encoder (`encode3t5b`),
- Hamming weight (`weight`) and support predicates (`DependsOnAtMost2`, `DependsOnAtMost4`),
- 3-quinary / 7-bit slot projections (`slot3`, `countFin5`),
- bijective 2-bit asymmetric codebook (`asym2Val`), and
- 4:2 vs 3:2 compressor primitives (`sum4to2`, `sum3to2`, `carry3to2`).
-/

namespace SubbyteE2M1Lop3

/-- Exact OCP MXFP4 (E2M1) nibble decoding `2 * value(n) ∈ {0, ±1, ±2, ±3, ±4, ±6, ±8, ±12}`,
    where `n` has bits `S = b3, E1 = b2, E0 = b1, M0 = b0`.
    Both `+0.0` (`0000`) and `-0.0` (`1000`) decode to `0`, and `±1.0` (`0010`/`1010`)
    decode to `±2`. -/
def e2m1TwiceVal (n : BitVec 4) : Int :=
  let s  := n.getLsbD 3
  let e1 := n.getLsbD 2
  let e0 := n.getLsbD 1
  let m0 := n.getLsbD 0
  let mag : Int :=
    match e1, e0, m0 with
    | false, false, false => 0
    | false, false, true  => 1
    | false, true,  false => 2
    | false, true,  true  => 3
    | true,  false, false => 4
    | true,  false, true  => 6
    | true,  true,  false => 8
    | true,  true,  true  => 12
  if s then -mag else mag

/-- Exact PTX 3-input Boolean lookup gate `lop3.b32`:
    returns bit `(4 * a + 2 * b + c)` of `imm8`. -/
def lop3 (imm8 : UInt8) (a b c : Bool) : Bool :=
  ((imm8.toNat >>> ((if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0))) &&& 1) == 1

/-- Construct a ternary E2M1 nibble with sign `s`, exponent bit `e0`, and `E1 = M0 = 0`. -/
def mkE2M1Ternary (s e0 : Bool) : BitVec 4 :=
  BitVec.ofNat 4 ((if s then 8 else 0) + (if e0 then 2 else 0))

/-- Predicate for a ternary weight `w ∈ {-1, 0, +1}`. -/
def IsTrit (w : Int) : Prop :=
  w = -1 ∨ w = 0 ∨ w = 1

/-- Decode a triple of E2M1 nibbles to their `2 * value` integers. -/
def decode3E2M1 (t : BitVec 4 × BitVec 4 × BitVec 4) : Int × Int × Int :=
  (e2m1TwiceVal t.1, e2m1TwiceVal t.2.1, e2m1TwiceVal t.2.2)

/-- 0-`LOP3` (pure bit-wire routing, zero Boolean gates) 2-trit / 4-bit → E2M1 unpacker. -/
def unpack2t4b (x : BitVec 4) : BitVec 4 × BitVec 4 :=
  let s0 := x.getLsbD 0
  let e0 := x.getLsbD 1
  let s1 := x.getLsbD 2
  let e1 := x.getLsbD 3
  (mkE2M1Ternary s0 e0, mkE2M1Ternary s1 e1)

/-- Explicit encoder for 2 ternary weights into 4 bits for `unpack2t4b`. -/
def encode2t4b (w0 w1 : Int) : BitVec 4 :=
  let s0 := w0 == -1
  let e0 := w0 != 0
  let s1 := w1 == -1
  let e1 := w1 != 0
  BitVec.ofNat 4
    ((if s0 then 1 else 0) + (if e0 then 2 else 0) +
     (if s1 then 4 else 0) + (if e1 then 8 else 0))

/-- Exact 4-`LOP3` 3-trit / 5-bit → E2M1 unpacker (`I093`):
    - Direct wires (`0 LOP3`): `S0 = c0`, `S1 = c1`, `S2 = c2`, `E1 = M0 = 0`.
    - `G1`: `E0_0 = lop3 0x73 c4 c3 c2` (`~c3 | (c4 & ~c2)`)
    - `G2`: `E0_1 = lop3 0xC7 c4 c3 c0` (`(c4 == c3) | (~c4 & ~c0)`)
    - `G3`: `t    = lop3 0x3B c0 c1 c3`
    - `G4`: `E0_2 = lop3 0x71 t c3 c4` -/
def unpack3t5b (x : BitVec 5) : BitVec 4 × BitVec 4 × BitVec 4 :=
  let c0 := x.getLsbD 0
  let c1 := x.getLsbD 1
  let c2 := x.getLsbD 2
  let c3 := x.getLsbD 3
  let c4 := x.getLsbD 4
  let e0 := lop3 0x73 c4 c3 c2
  let e1 := lop3 0xC7 c4 c3 c0
  let t  := lop3 0x3B c0 c1 c3
  let e2 := lop3 0x71 t c3 c4
  (mkE2M1Ternary c0 e0, mkE2M1Ternary c1 e1, mkE2M1Ternary c2 e2)

/-- Explicit encoder for 3 ternary weights into 5 bits for `unpack3t5b`. -/
def encode3t5b (w0 w1 w2 : Int) : BitVec 5 :=
  let s0 := w0 == -1
  let s1 := w1 == -1
  let s2 := w2 == -1
  let nz0 := w0 != 0
  let nz1 := w1 != 0
  let nz2 := w2 != 0
  let (c4, c3, c2, c1, c0) : Bool × Bool × Bool × Bool × Bool :=
    match nz0, nz1, nz2 with
    | true,  true,  true  => (false, false, s2,    s1,    s0)
    | false, true,  true  => (false, true,  s2,    s1,    false)
    | false, false, true  => (false, true,  s2,    false, true)
    | false, false, false => (false, true,  false, true,  true)
    | true,  false, true  => (true,  false, s2,    false, s0)
    | true,  false, false => (true,  false, false, true,  s0)
    | true,  true,  false => (true,  true,  false, s1,    s0)
    | false, true,  false => (true,  true,  true,  s1,    false)
  BitVec.ofNat 5
    ((if c0 then 1 else 0) + (if c1 then 2 else 0) + (if c2 then 4 else 0) +
     (if c3 then 8 else 0) + (if c4 then 16 else 0))

/-- Hamming weight of a Boolean function `f : BitVec k → Bool`:
    number of `k`-bit inputs on which `f` evaluates to `true`. -/
def weight {k : Nat} (f : BitVec k → Bool) : Nat :=
  (List.finRange (2 ^ k)).countP (fun i => f (BitVec.ofNat k i.val))

/-- A Boolean function on `BitVec 5` depends on at most 2 of the 5 input bits. -/
def DependsOnAtMost2 (f : BitVec 5 → Bool) : Prop :=
  ∃ (i0 i1 : Fin 5) (g : Bool → Bool → Bool),
    ∀ x : BitVec 5, f x = g (x.getLsbD i0.val) (x.getLsbD i1.val)

/-- A Boolean function on `BitVec 7` depends on at most 4 of the 7 input bits. -/
def DependsOnAtMost4 (f : BitVec 7 → Bool) : Prop :=
  ∃ (i0 i1 i2 i3 : Fin 7) (g : Bool → Bool → Bool → Bool → Bool),
    ∀ x : BitVec 7,
      f x = g (x.getLsbD i0.val) (x.getLsbD i1.val) (x.getLsbD i2.val) (x.getLsbD i3.val)

/-- Slot selector for a triple of quinary values `Fin 5 × Fin 5 × Fin 5`. -/
def slot3 (s : Fin 3) (t : Fin 5 × Fin 5 × Fin 5) : Fin 5 :=
  match s with
  | ⟨0, _⟩ => t.1
  | ⟨1, _⟩ => t.2.1
  | ⟨2, _⟩ => t.2.2

/-- Number of elements in `Fin 5` satisfying predicate `P`. -/
def countFin5 (P : Fin 5 → Bool) : Nat :=
  (List.finRange 5).countP P

/-- Bijective 2-bit asymmetric codebook (`I098`/`I100`): `w = -2*b1 + b0 ∈ {-2, -1, 0, +1}`. -/
def asym2Val (b1 b0 : Bool) : Int :=
  -(if b1 then 2 else 0) + (if b0 then 1 else 0)

/-- 5-input parity bit of a 4:2 compressor (`x0 ⊕ x1 ⊕ x2 ⊕ x3 ⊕ cin`). -/
def sum4to2 (x0 x1 x2 x3 cin : Bool) : Bool :=
  xor (xor (xor (xor x0 x1) x2) x3) cin

/-- 3:2 carry-save adder sum bit (`XOR3` via `lop3 0x96`). -/
def sum3to2 (a b c : Bool) : Bool :=
  lop3 0x96 a b c

/-- 3:2 carry-save adder carry bit (`MAJ3` via `lop3 0xE8`). -/
def carry3to2 (a b c : Bool) : Bool :=
  lop3 0xE8 a b c

end SubbyteE2M1Lop3
