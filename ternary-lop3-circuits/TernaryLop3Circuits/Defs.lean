/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Minimal-`LOP3` Ternary Bit-Plane Circuits

Pure-`Init` (zero Mathlib) definitions of:
- the 3-input Boolean lookup gate `lop3` (matching PTX `lop3.b32`),
- bit-plane trit semantics (`tritVal`, `tritDisjoint`, `fin3ToTrit`),
- the optimal 6-`LOP3` depth-2 3-trit / 5-bit unpacking circuit (`unpack3t5b`) and its 4-codeword escape cube (`esc3t5b`),
- the 14-`LOP3` depth-4 escape-cube 5-trit / 8-bit unpacking circuit (`unpack5t8b`),
- the 9-`LOP3` ternary × signed INT4 `[-8, 7]` exact 5-bit product (`ternaryInt4Exact5`),
- the 4+10-`LOP3` ternary × FP4 (E2M1) exact 5-bit product (`fp4ToMag4`, `ternaryFp4Exact5`),
- population count (`popcnt`) for Carry-Save-Adder conservation, and
- cardinality / support predicates (`countTrue`, `DependsOnAtMost4`) for exact lower bounds.
-/

namespace TernaryLop3Circuits

/-- 3-input Boolean lookup table `LOP3(a, b, c, imm8)` matching PTX `lop3.b32`:
    returns bit `(4 * a + 2 * b + c)` of `imm8`. -/
def lop3 (a b c : Bool) (imm8 : Nat) : Bool :=
  let idx := (if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)
  (imm8 >>> idx) &&& 1 == 1

/-- Extract bit `i` of a natural number as a `Bool`. -/
def bitAt (x i : Nat) : Bool :=
  (x >>> i) &&& 1 == 1

/-- Convert a `Bool` to `Int` (`true ↦ 1`, `false ↦ 0`). -/
def boolToInt (b : Bool) : Int :=
  if b then 1 else 0

/-- Decode a bit-plane trit `(p, n)` to `Int`: `p - n ∈ {-1, 0, 1}`. -/
def tritVal (pn : Bool × Bool) : Int :=
  boolToInt pn.1 - boolToInt pn.2

/-- A bit-plane trit `(p, n)` is disjoint (valid) iff `p` and `n` are not both `true`. -/
def tritDisjoint (pn : Bool × Bool) : Bool :=
  !(pn.1 && pn.2)

/-- Canonical bijection `Fin 3 → {-1, 0, 1} ⊂ Int`: `0 ↦ -1`, `1 ↦ 0`, `2 ↦ 1`. -/
def fin3ToTrit (t : Fin 3) : Int :=
  (t.val : Int) - 1

/-- Number of inputs `x : Fin n` for which `f x = true`. -/
def countTrue {n : Nat} (f : Fin n → Bool) : Nat :=
  (List.finRange n).countP f

/-- 4-codeword escape cube `x0 && !x1 && x3` on 5-bit codewords `Fin 32`. -/
def esc3t5b (x : Fin 32) : Bool :=
  lop3 (bitAt x.val 0) (bitAt x.val 1) (bitAt x.val 3) 0x20

/-- Co-designed 6-`LOP3`, depth-2 3-trit / 5-bit unpacking circuit on `x : Fin 32`.
    Returns `((p0, n0), (p1, n1), (p2, n2))`. -/
def unpack3t5b (x : Fin 32) : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) :=
  let x0 := bitAt x.val 0
  let x1 := bitAt x.val 1
  let x2 := bitAt x.val 2
  let x3 := bitAt x.val 3
  let x4 := bitAt x.val 4
  let p0 := lop3 x0 x1 x2 0xE0
  let n0 := lop3 p0 x4 x4 0x0C
  let p1 := lop3 x0 x1 x2 0x52
  let n1 := lop3 p1 x3 x4 0x06
  let p2 := lop3 x1 x2 x3 0x16
  let n2 := lop3 p2 x2 x4 0x06
  ((p0, n0), (p1, n1), (p2, n2))

/-- Output lane selector for a 3-trit decoder: `0..5` select `p0, n0, p1, n1, p2, n2`. -/
def lane3t (out : (Bool × Bool) × (Bool × Bool) × (Bool × Bool)) : Fin 6 → Bool
  | ⟨0, _⟩ => out.1.1
  | ⟨1, _⟩ => out.1.2
  | ⟨2, _⟩ => out.2.1.1
  | ⟨3, _⟩ => out.2.1.2
  | ⟨4, _⟩ => out.2.2.1
  | ⟨5, _⟩ => out.2.2.2

/-- Co-designed 14-`LOP3`, depth-4 escape-cube 5-trit / 8-bit unpacking circuit on `x : Fin 256`.
    Returns `((p0, n0), (p1, n1), (p2, n2), (p3, n3), (p4, n4))`. -/
def unpack5t8b (x : Fin 256) :
    (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) :=
  let x0 := bitAt x.val 0
  let x1 := bitAt x.val 1
  let x2 := bitAt x.val 2
  let x3 := bitAt x.val 3
  let x4 := bitAt x.val 4
  let x5 := bitAt x.val 5
  let x6 := bitAt x.val 6
  let x7 := bitAt x.val 7
  let esc := lop3 x0 x1 x3 0x20
  let y0  := lop3 esc x5 x0 0xCA
  let y1  := lop3 esc x6 x1 0xCA
  let y3  := lop3 esc x7 x3 0xCA
  let p2  := lop3 y0 y1 x2 0xE0
  let n2  := lop3 p2 x4 x4 0x0C
  let p3  := lop3 y0 y1 x2 0x52
  let n3  := lop3 p3 y3 x4 0x06
  let p4  := lop3 y1 x2 y3 0x16
  let n4  := lop3 p4 x2 x4 0x06
  let p0  := lop3 esc x5 x6 0xF8
  let n0  := lop3 p0 x5 x7 0x06
  let p1  := lop3 esc x5 x6 0xF1
  let n1  := lop3 p1 esc x7 0x01
  ((p0, n0), (p1, n1), (p2, n2), (p3, n3), (p4, n4))

/-- Output lane selector for a 5-trit decoder: `0..9` select `p0, n0, p1, n1, p2, n2, p3, n3, p4, n4`. -/
def lane5t
    (out : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool)) :
    Fin 10 → Bool
  | ⟨0, _⟩ => out.1.1
  | ⟨1, _⟩ => out.1.2
  | ⟨2, _⟩ => out.2.1.1
  | ⟨3, _⟩ => out.2.1.2
  | ⟨4, _⟩ => out.2.2.1.1
  | ⟨5, _⟩ => out.2.2.1.2
  | ⟨6, _⟩ => out.2.2.2.1.1
  | ⟨7, _⟩ => out.2.2.2.1.2
  | ⟨8, _⟩ => out.2.2.2.2.1
  | ⟨9, _⟩ => out.2.2.2.2.2

/-- A Boolean function `f : Fin 256 → Bool` depends on at most 4 of the 8 input bits
    if it factors through 4 bit positions `(i0, i1, i2, i3 : Fin 8)`. -/
def DependsOnAtMost4 (f : Fin 256 → Bool) : Prop :=
  ∃ (i0 i1 i2 i3 : Fin 8) (g : Bool → Bool → Bool → Bool → Bool),
    ∀ x : Fin 256,
      f x = g (bitAt x.val i0.val) (bitAt x.val i1.val) (bitAt x.val i2.val) (bitAt x.val i3.val)

/-- Two's-complement 4-bit signed integer `[-8, 7]` from bits `(a0, a1, a2, a3)`. -/
def int4Signed (a0 a1 a2 a3 : Bool) : Int :=
  boolToInt a0 + 2 * boolToInt a1 + 4 * boolToInt a2 - 8 * boolToInt a3

/-- Exact 9-`LOP3` Ternary × Signed INT4 `[-8, 7]` 5-bit unsigned offset product circuit. -/
def ternaryInt4Exact5 (p n a0 a1 a2 a3 : Bool) : Bool × Bool × Bool × Bool × Bool :=
  let z  := lop3 p n n 0xFC
  let y0 := lop3 z a0 a0 0xC0
  let t1 := lop3 n a0 a0 0xC0
  let y1 := lop3 z a1 t1 0x60
  let t2 := lop3 t1 n a1 0xF8
  let y2 := lop3 z a2 t2 0x60
  let t3 := lop3 t2 n a2 0xF8
  let y3 := lop3 z a3 t3 0x9F
  let y4 := lop3 n a3 t3 0x40
  (y0, y1, y2, y3, y4)

/-- Exact 4-`LOP3` FP4 (E2M1) magnitude decoder `(e1, e0, m0) ↦ (b0, b1, b2, b3)`
    giving the 4-bit unsigned integer `2 * |x| ∈ {0, 1, 2, 3, 4, 6, 8, 12}`. -/
def fp4ToMag4 (e1 e0 m0 : Bool) : Bool × Bool × Bool × Bool :=
  let b0 := lop3 e1 m0 m0 0x0C
  let b1 := lop3 e1 e0 m0 0x2C
  let b2 := lop3 e1 e0 m0 0xB0
  let b3 := lop3 e1 e0 e0 0xC0
  (b0, b1, b2, b3)

/-- Exact 10-`LOP3` Ternary × FP4 (E2M1) sign-magnitude product circuit (4+10 `LOP3` total). -/
def ternaryFp4Exact5 (p n s e1 e0 m0 : Bool) : Bool × Bool × Bool × Bool × Bool :=
  let (b0, b1, b2, b3) := fp4ToMag4 e1 e0 m0
  let z  := lop3 p n n 0xFC
  let ne := lop3 s p n 0xCA
  let y0 := lop3 z b0 b0 0xC0
  let t1 := lop3 ne b0 b0 0xC0
  let y1 := lop3 z b1 t1 0x60
  let t2 := lop3 t1 ne b1 0xF8
  let y2 := lop3 z b2 t2 0x60
  let t3 := lop3 t2 ne b2 0xF8
  let y3 := lop3 z b3 t3 0x60
  let t4 := lop3 t3 ne b3 0xF8
  (y0, y1, y2, y3, t4)

/-- Exact scaled integer value `2 * x` of an FP4 (E2M1) code `(s, e1, e0, m0)`. -/
def fp4Scaled2 (s e1 e0 m0 : Bool) : Int :=
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

/-- Population count (Hamming weight): number of `1`-bits in the binary expansion of `n : Nat`. -/
def popcnt (n : Nat) : Nat :=
  if h : n = 0 then 0 else (n % 2) + popcnt (n / 2)
termination_by n
decreasing_by omega

end TernaryLop3Circuits
