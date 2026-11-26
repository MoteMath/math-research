/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Sparse 2:4, 5t8b, E2M1 Multiplier & 2-Quinary `LOP3` Circuits

Pure-`Init` (zero Mathlib) definitions of all Wave 1C (`w1-lop3-subbyte-synth`) GPU-synthesized
`LOP3` circuits and lower-bound predicates:
1. 10-`LOP3` direct-sign 5-trit / 8-bit → 5 × OCP E2M1 unpacker (`unpack5t8b`, `encode5t8b`)
   and `DependsOnAtMost4` on `BitVec 8`.
2. Tight 1-`LOP3` 3-bit → 4-bit 2:4 sparse mask (`unpackMask24_3b`) and 1-`LOP3` 3-bit →
   unordered `{idx0, idx1}` (`unpackUnordered24_3b`).
3. Tight 3-`LOP3` 3-bit → ordered `(idx0 < idx1)` (`unpackOrdered24_3b`) and `WireOrConst3`.
4. 12-`LOP3` 8-bit → 3 × 4-bit 2:4 sparse masks (`unpackTripleMask24_8b`) and `maxFiber`.
5. 25-`LOP3` zero-FP `E2M1 × E2M1` magnitude multiplier (`e2m1MagMul25`, `e2m1MagVal`).
6. 4-`LOP3` depth-2 2-quinary / 5-bit → 2 × E2M1 unpacker (`unpack2q5b`, `encode2q5b`) and
   `WireOrConst5`.
-/

namespace Sparse24E2M1Lop3

/-! ## Basic Primitives -/

/-- Exact OCP MXFP4 (E2M1) nibble decoding `2 * value(n) ∈ {0, ±1, ±2, ±3, ±4, ±6, ±8, ±12}`,
    where `n` has bits `S = b3, E1 = b2, E0 = b1, M0 = b0`. -/
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

/-- Exact OCP MXFP4 (E2M1) 3-bit magnitude table `2 * |value| ∈ [0, 1, 2, 3, 4, 6, 8, 12]`. -/
def e2m1MagVal (a : BitVec 3) : Nat :=
  match a.getLsbD 2, a.getLsbD 1, a.getLsbD 0 with
  | false, false, false => 0
  | false, false, true  => 1
  | false, true,  false => 2
  | false, true,  true  => 3
  | true,  false, false => 4
  | true,  false, true  => 6
  | true,  true,  false => 8
  | true,  true,  true  => 12

/-- Exact PTX 3-input Boolean lookup gate `lop3.b32`:
    returns bit `(4 * a + 2 * b + c)` of `imm8`. -/
def lop3 (imm8 : UInt8) (a b c : Bool) : Bool :=
  ((imm8.toNat >>> ((if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0))) &&& 1) == 1

/-- Construct a 4-bit vector from `(b0, b1, b2, b3)` (LSB first). -/
def mkBits4 (b0 b1 b2 b3 : Bool) : BitVec 4 :=
  BitVec.ofNat 4
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) +
     (if b2 then 4 else 0) + (if b3 then 8 else 0))

/-- Construct an E2M1 nibble `(S, E1, E0, M0)`. -/
def mkE2M1 (s e1 e0 m0 : Bool) : BitVec 4 :=
  mkBits4 m0 e0 e1 s

/-- Construct a ternary E2M1 nibble with sign `s`, exponent bit `e0`, and `E1 = M0 = 0`. -/
def mkE2M1Ternary (s e0 : Bool) : BitVec 4 :=
  mkE2M1 s false e0 false

/-- Predicate for a ternary weight `w ∈ {-1, 0, +1}`. -/
def IsTrit (w : Int) : Prop :=
  w = -1 ∨ w = 0 ∨ w = 1

/-- Predicate for a quinary weight `w ∈ {-2, -1, 0, +1, +2}`. -/
def IsQuinary (w : Int) : Prop :=
  w = -2 ∨ w = -1 ∨ w = 0 ∨ w = 1 ∨ w = 2

/-- Hamming weight of a Boolean function `f : BitVec k → Bool`:
    number of `k`-bit inputs on which `f` evaluates to `true`. -/
def weight {k : Nat} (f : BitVec k → Bool) : Nat :=
  (List.finRange (2 ^ k)).countP (fun i => f (BitVec.ofNat k i.val))

/-- A Boolean function on `BitVec 8` depends on at most 4 of the 8 input bits. -/
def DependsOnAtMost4 (f : BitVec 8 → Bool) : Prop :=
  ∃ (i0 i1 i2 i3 : Fin 8) (g : Bool → Bool → Bool → Bool → Bool),
    ∀ x : BitVec 8,
      f x = g (x.getLsbD i0.val) (x.getLsbD i1.val) (x.getLsbD i2.val) (x.getLsbD i3.val)

/-- A Boolean function on `BitVec k` is a constant, a raw input wire, or an inverted input wire. -/
def WireOrConst {k : Nat} (f : BitVec k → Bool) : Prop :=
  (∃ c : Bool, ∀ x : BitVec k, f x = c) ∨
  (∃ i : Fin k, (∀ x : BitVec k, f x = x.getLsbD i.val) ∨
                (∀ x : BitVec k, f x = !x.getLsbD i.val))

/-! ## Frontier 1: 10-`LOP3` Direct-Sign `5t8b → 5 × E2M1` -/

/-- Slot selector for a 5-tuple of E2M1 nibbles. -/
def slot5 (i : Fin 5) (t : BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4) : BitVec 4 :=
  match i with
  | ⟨0, _⟩ => t.1
  | ⟨1, _⟩ => t.2.1
  | ⟨2, _⟩ => t.2.2.1
  | ⟨3, _⟩ => t.2.2.2.1
  | ⟨4, _⟩ => t.2.2.2.2

/-- Decode a 5-tuple of E2M1 nibbles to their `2 * value` integers. -/
def decode5E2M1 (t : BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4) :
    Int × Int × Int × Int × Int :=
  (e2m1TwiceVal t.1, e2m1TwiceVal t.2.1, e2m1TwiceVal t.2.2.1,
   e2m1TwiceVal t.2.2.2.1, e2m1TwiceVal t.2.2.2.2)

/-- Exact 10-`LOP3` direct-sign (`S0..S4 = c0..c4`) 5-trit / 8-bit → 5 × E2M1 unpacker
    synthesized on RX 7900 XTX (`results.json`: `frontier_1_5t8b_e2m1.best_verified_circuit`). -/
def unpack5t8b (x : BitVec 8) : BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 :=
  let c0  := x.getLsbD 0
  let c1  := x.getLsbD 1
  let c2  := x.getLsbD 2
  let c3  := x.getLsbD 3
  let c4  := x.getLsbD 4
  let c5  := x.getLsbD 5
  let c6  := x.getLsbD 6
  let c7  := x.getLsbD 7
  let w8  := lop3 0xA1 c7 c6 c5
  let w9  := lop3 0xEC c1 c5 w8
  let w10 := lop3 0x78 c6 w8 c0
  let w11 := lop3 0x69 c4 c3 c2
  let w12 := lop3 0x1E c7 c4 w9
  let w13 := lop3 0x2D w8 w12 c1
  let w14 := lop3 0xAE w13 c0 w12
  let w15 := lop3 0xDA w10 w9 w11
  let w16 := lop3 0xF4 w10 c2 w15
  let w17 := lop3 0x9A w16 w15 w9
  (mkE2M1Ternary c0 w13, mkE2M1Ternary c1 w14, mkE2M1Ternary c2 w15,
   mkE2M1Ternary c3 w16, mkE2M1Ternary c4 w17)

/-- Map a ternary weight `w ∈ {-1, 0, +1}` to its index `{0, 1, 2}`. -/
def tritIdx (w : Int) : Nat :=
  if w == -1 then 0 else if w == 0 then 1 else 2

/-- Compact 9 × 27 lookup table for `encode5t8b` (243 exact 8-bit codes). -/
def encode5t8bSlice (hi : Nat) : List Nat :=
  match hi with
  | 0 => [127, 31, 126, 191, 252, 254, 125, 189, 124,
          91, 159, 90, 157, 158, 156, 89, 25, 88,
          123, 27, 122, 187, 248, 250, 121, 185, 120]
  | 1 => [55, 22, 54, 247, 180, 182, 53, 245, 52,
          51, 18, 50, 243, 176, 178, 49, 241, 48,
          59, 26, 58, 251, 184, 186, 57, 249, 56]
  | 2 => [119, 23, 118, 183, 244, 246, 117, 181, 116,
          87, 215, 86, 213, 214, 212, 85, 21, 84,
          115, 19, 114, 179, 240, 242, 113, 177, 112]
  | 3 => [95, 223, 94, 221, 222, 220, 93, 29, 92,
          63, 30, 62, 255, 188, 190, 61, 253, 60,
          203, 75, 202, 73, 74, 72, 201, 9, 200]
  | 4 => [143, 151, 142, 149, 12, 148, 141, 20, 140,
          139, 147, 138, 145, 8, 144, 137, 16, 136,
          131, 155, 130, 153, 0, 152, 129, 24, 128]
  | 5 => [199, 71, 198, 69, 70, 68, 197, 5, 196,
          39, 6, 38, 231, 164, 166, 37, 229, 36,
          83, 211, 82, 209, 210, 208, 81, 17, 80]
  | 6 => [111, 15, 110, 175, 236, 238, 109, 173, 108,
          207, 79, 206, 77, 78, 76, 205, 13, 204,
          107, 11, 106, 171, 232, 234, 105, 169, 104]
  | 7 => [47, 14, 46, 239, 172, 174, 45, 237, 44,
          43, 10, 42, 235, 168, 170, 41, 233, 40,
          35, 2, 34, 227, 160, 162, 33, 225, 32]
  | _ => [103, 7, 102, 167, 228, 230, 101, 165, 100,
          135, 67, 134, 65, 4, 64, 133, 1, 132,
          99, 3, 98, 163, 224, 226, 97, 161, 96]

/-- Explicit encoder mapping any ternary 5-tuple `(w0, w1, w2, w3, w4) ∈ {-1, 0, +1}^5`
    to its exact 8-bit code for `unpack5t8b`. -/
def encode5t8b (w0 w1 w2 w3 w4 : Int) : BitVec 8 :=
  let hi := tritIdx w3 + 3 * tritIdx w4
  let lo := tritIdx w0 + 3 * tritIdx w1 + 9 * tritIdx w2
  BitVec.ofNat 8 ((encode5t8bSlice hi).getD lo 0)

/-! ## Frontier 2A: Single-Group `3-bit → 2:4 Sparse Mask` & `2×2-bit Indices` -/

/-- Population count of a 4-bit mask. -/
def popcount4 (m : BitVec 4) : Nat :=
  (if m.getLsbD 0 then 1 else 0) + (if m.getLsbD 1 then 1 else 0) +
  (if m.getLsbD 2 then 1 else 0) + (if m.getLsbD 3 then 1 else 0)

/-- Predicate for a valid 2-of-4 sparse mask (Hamming weight 2 in `BitVec 4`). -/
def isMask24 (m : BitVec 4) : Bool :=
  popcount4 m == 2

/-- Tight 1-`LOP3` 3-bit → 4-bit 2:4 sparse mask unpacker:
    `m0 = c0, m1 = c1, m2 = c2, m3 = lop3 0x17 c2 c1 c0` (`~MAJ3`). -/
def unpackMask24_3b (x : BitVec 3) : BitVec 4 :=
  let c0 := x.getLsbD 0
  let c1 := x.getLsbD 1
  let c2 := x.getLsbD 2
  mkBits4 c0 c1 c2 (lop3 0x17 c2 c1 c0)

/-- Construct a `Fin 4` index from its two bits `(lsb, msb)`. -/
def mkFin4 (b0 b1 : Bool) : Fin 4 :=
  ⟨(if b0 then 1 else 0) + (if b1 then 2 else 0), by cases b0 <;> cases b1 <;> decide⟩

/-- Tight 1-`LOP3` 3-bit → unordered 2:4 index pair `{idx0, idx1}` unpacker:
    `i0_0 = c0, i0_1 = c1, i1_0 = c2, i1_1 = lop3 0x63 c2 c1 c0`. -/
def unpackUnordered24_3b (x : BitVec 3) : Fin 4 × Fin 4 :=
  let c0 := x.getLsbD 0
  let c1 := x.getLsbD 1
  let c2 := x.getLsbD 2
  let i11 := lop3 0x63 c2 c1 c0
  (mkFin4 c0 c1, mkFin4 c2 i11)

/-- Explicit 3-bit encoder for unordered 2:4 pairs `{a, b}` (`a < b`). -/
def encodeUnordered24_3b (a b : Fin 4) : BitVec 3 :=
  match a.val, b.val with
  | 0, 1 => BitVec.ofNat 3 4
  | 0, 2 => BitVec.ofNat 3 0
  | 0, 3 => BitVec.ofNat 3 3
  | 1, 2 => BitVec.ofNat 3 1
  | 1, 3 => BitVec.ofNat 3 5
  | _, _ => BitVec.ofNat 3 6

/-- Tight 3-`LOP3` 3-bit → ordered 2:4 index pair `(idx0 < idx1)` unpacker:
    `i0_0 = c2`, `i0_1 = 0x08`, `i1_0 = 0x2D`, `i1_1 = 0x3E`. -/
def unpackOrdered24_3b (x : BitVec 3) : Fin 4 × Fin 4 :=
  let c0 := x.getLsbD 0
  let c1 := x.getLsbD 1
  let c2 := x.getLsbD 2
  let i00 := c2
  let i01 := lop3 0x08 c2 c1 c0
  let i10 := lop3 0x2D c2 c1 c0
  let i11 := lop3 0x3E c2 c1 c0
  (mkFin4 i00 i01, mkFin4 i10 i11)

/-- Explicit 3-bit encoder for ordered 2:4 pairs `(a < b)`. -/
def encodeOrdered24_3b (a b : Fin 4) : BitVec 3 :=
  match a.val, b.val with
  | 0, 1 => BitVec.ofNat 3 0
  | 0, 2 => BitVec.ofNat 3 1
  | 0, 3 => BitVec.ofNat 3 2
  | 1, 2 => BitVec.ofNat 3 4
  | 1, 3 => BitVec.ofNat 3 5
  | _, _ => BitVec.ofNat 3 3

/-- Extract one of the 4 index output bits `(i0_0, i0_1, i1_0, i1_1)` from a `Fin 4 × Fin 4` pair. -/
def idxPairBit (p : Fin 4 × Fin 4) (k : Fin 4) : Bool :=
  match k with
  | ⟨0, _⟩ => p.1.val % 2 == 1
  | ⟨1, _⟩ => p.1.val / 2 == 1
  | ⟨2, _⟩ => p.2.val % 2 == 1
  | ⟨3, _⟩ => p.2.val / 2 == 1

/-! ## Frontier 2B: 12-`LOP3` `8-bit → 3 × 4-bit 2:4 Sparse Masks` -/

/-- Exact 12-`LOP3` 8-bit → 3 × 4-bit 2:4 sparse mask unpacker (`H3_G12` in `results.json`):
    3 direct wires (`c5, c6, c7`), 3 shared helpers (`w8..w10`), 6 folded gates (`w11,w12,w14,w15,w17,w18`),
    and 3 `~MAJ3` (`0x17`) completion gates (`w13,w16,w19`). -/
def unpackTripleMask24_8b (x : BitVec 8) : BitVec 4 × BitVec 4 × BitVec 4 :=
  let c0  := x.getLsbD 0
  let c1  := x.getLsbD 1
  let c2  := x.getLsbD 2
  let c3  := x.getLsbD 3
  let c4  := x.getLsbD 4
  let c5  := x.getLsbD 5
  let c6  := x.getLsbD 6
  let c7  := x.getLsbD 7
  let w8  := lop3 0xAB c3 c2 c0
  let w9  := lop3 0x97 c2 c0 c4
  let w10 := lop3 0x4D c1 c2 w8
  let w11 := lop3 0x96 c5 c2 w8
  let w12 := lop3 0x96 c5 w10 c1
  let w13 := lop3 0x17 c5 w11 w12
  let w14 := lop3 0xA5 c6 c3 w10
  let w15 := lop3 0x1E c6 w10 c4
  let w16 := lop3 0x17 c6 w14 w15
  let w17 := lop3 0x96 c7 w8 c3
  let w18 := lop3 0x4B c7 w9 c0
  let w19 := lop3 0x17 c7 w17 w18
  (mkBits4 c5 w11 w12 w13, mkBits4 c6 w14 w15 w16, mkBits4 c7 w17 w18 w19)

/-- Fiber index `{0, 1, 2}` of a valid 2-of-4 mask modulo complementation of `m0` (`6 = 2 × 3`). -/
def mask24FiberIdx (m : BitVec 4) : Nat :=
  let mn := if m.getLsbD 0 then m ^^^ BitVec.ofNat 4 15 else m
  if mn == BitVec.ofNat 4 6 then 0
  else if mn == BitVec.ofNat 4 10 then 1
  else 2

/-- 27-entry `3t5b` core table for `encodeTripleMask24_8b`. -/
def tripleMaskCoreTable : List Nat :=
  [19, 17, 23, 3, 1, 7, 28, 30, 5,
   18, 16, 26, 2, 0, 10, 12, 14, 8,
   27, 25, 31, 11, 9, 15, 20, 22, 13]

/-- Explicit 8-bit encoder for any triple of valid 2-of-4 sparse masks (`6^3 = 216` triples). -/
def encodeTripleMask24_8b (m0 m1 m2 : BitVec 4) : BitVec 8 :=
  let idx := mask24FiberIdx m0 + 3 * mask24FiberIdx m1 + 9 * mask24FiberIdx m2
  let lo5 := tripleMaskCoreTable.getD idx 0
  let hi3 := (if m0.getLsbD 0 then 32 else 0) +
             (if m1.getLsbD 0 then 64 else 0) +
             (if m2.getLsbD 0 then 128 else 0)
  BitVec.ofNat 8 (lo5 + hi3)

/-- Maximum fiber size of a 2-of-4 mask given `d` direct input wires assigned to it. -/
def maxFiber (d : Nat) : Nat :=
  match d with
  | 0 => 6
  | 1 => 3
  | 2 => 2
  | _ => 1

/-! ## Frontier 3: 25-`LOP3` Zero-FP `E2M1 × E2M1` Magnitude Multiplier -/

/-- Exact 25-`LOP3` zero-FP `E2M1 × E2M1` magnitude multiplier (`results.json`:
    `frontier_3_e2m1_mul.best_circuit`, wires `0..5 = b0, b1, b2, a0, a1, a2`). -/
def e2m1MagMul25 (a b : BitVec 3) : BitVec 8 :=
  let w0  := b.getLsbD 0
  let w1  := b.getLsbD 1
  let w2  := b.getLsbD 2
  let w3  := a.getLsbD 0
  let w4  := a.getLsbD 1
  let w5  := a.getLsbD 2
  let w6  := lop3 0xBC w2  w1  w1
  let w7  := lop3 0xE2 w4  w4  w5
  let w8  := lop3 0xBC w0  w0  w3
  let w9  := lop3 0xE2 w7  w0  w0
  let w10 := lop3 0x78 w9  w6  w3
  let w11 := lop3 0x40 w7  w6  w8
  let w12 := lop3 0x6C w4  w7  w7
  let w13 := lop3 0x39 w5  w12 w2
  let w14 := lop3 0xA6 w1  w2  w12
  let w15 := lop3 0x8C w14 w2  w1
  let w16 := lop3 0xAE w12 w5  w15
  let w17 := lop3 0x5B w13 w8  w15
  let w18 := lop3 0xF7 w14 w17 w8
  let w19 := lop3 0x35 w14 w8  w10
  let w20 := lop3 0xCA w14 w10 w11
  let w21 := lop3 0xC2 w14 w11 w9
  let w22 := lop3 0x38 w16 w17 w21
  let p0  := lop3 0x10 w8  w18 w16
  let p1  := lop3 0x03 w19 w16 w11
  let p2  := lop3 0x18 w16 w18 w20
  let p3  := lop3 0x24 w19 w16 w22
  let p4  := lop3 0x91 w16 w17 w20
  let p5  := lop3 0x18 w22 w19 w21
  let p6  := lop3 0x81 w14 w8  w17
  let p7  := lop3 0x40 w5  w22 w11
  BitVec.ofNat 8
    ((if p0 then 1 else 0) + (if p1 then 2 else 0) + (if p2 then 4 else 0) +
     (if p3 then 8 else 0) + (if p4 then 16 else 0) + (if p5 then 32 else 0) +
     (if p6 then 64 else 0) + (if p7 then 128 else 0))

/-! ## Frontier 4: 4-`LOP3` Depth-2 `2-quinary / 5-bit → 2 × E2M1` -/

/-- Exact 4-`LOP3` depth-2 `2q5b → 2 × E2M1` unpacker (`4gate_mode1_direct2` in `results.json`):
    `S0 = c0`, `S1 = c1`, `E1_0 = g0`, `E0_0 = g1`, `E1_1 = g2`, `E0_1 = g3`, `M0 = 0`. -/
def unpack2q5b (x : BitVec 5) : BitVec 4 × BitVec 4 :=
  let c0 := x.getLsbD 0
  let c1 := x.getLsbD 1
  let c2 := x.getLsbD 2
  let c3 := x.getLsbD 3
  let c4 := x.getLsbD 4
  let g0 := lop3 0x38 c3 c4 c1
  let g1 := lop3 0x19 c2 c2 g0
  let g2 := lop3 0xC4 c4 c3 c2
  let g3 := lop3 0x0D g2 g2 c4
  (mkE2M1 c0 g0 g1 false, mkE2M1 c1 g2 g3 false)

/-- Explicit 5-bit encoder for all 25 quinary pairs `(w0, w1) ∈ {-2, -1, 0, +1, +2}^2`. -/
def encode2q5b (w0 w1 : Int) : BitVec 5 :=
  BitVec.ofNat 5 <|
    match w0, w1 with
    |  1,  1 => 0  | -1,  1 => 1  |  1, -1 => 2  | -1, -1 => 3
    |  0,  1 => 4  |  0, -1 => 6  |  2,  2 => 8  | -2,  2 => 9
    |  2, -2 => 10 | -2, -2 => 11 |  2,  1 => 12 | -2,  1 => 13
    |  2, -1 => 14 | -2, -1 => 15 |  1,  0 => 16 | -1,  0 => 17
    |  2,  0 => 18 | -2,  0 => 19 |  0,  0 => 20 |  1,  2 => 24
    | -1,  2 => 25 |  1, -2 => 26 | -1, -2 => 27 |  0,  2 => 28
    |  0, -2 => 30 |  _,  _ => 0

/-- Extract one of the 6 E2M1 output bits `(S0, E1_0, E0_0, S1, E1_1, E0_1)` from a pair of nibbles. -/
def quinaryOutBit (p : BitVec 4 × BitVec 4) (k : Fin 6) : Bool :=
  match k with
  | ⟨0, _⟩ => p.1.getLsbD 3  -- S0
  | ⟨1, _⟩ => p.1.getLsbD 2  -- E1_0
  | ⟨2, _⟩ => p.1.getLsbD 1  -- E0_0
  | ⟨3, _⟩ => p.2.getLsbD 3  -- S1
  | ⟨4, _⟩ => p.2.getLsbD 2  -- E1_1
  | ⟨5, _⟩ => p.2.getLsbD 1  -- E0_1

end Sparse24E2M1Lop3
