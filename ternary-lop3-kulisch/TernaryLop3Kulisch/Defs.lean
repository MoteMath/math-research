/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`ternary-lop3-kulisch`)

Pure-`Init` (zero Mathlib) definitions for Wave 4A (`w4-int-ternary-matmul`):
1. Exact PTX `LOP3.B32` gate (`lop3`) and general acyclic `LOP3` DAG evaluator (`Lop3Dag`, `evalWire`).
2. Synthesized minimal-`LOP3` counters:
   - 4-`LOP3` depth-3 `K=2` balanced-ternary counter (`ternaryK2Lop3`, `ternaryK2Dag`).
   - 7-`LOP3` depth-3 `K=3` balanced-ternary counter (`ternaryK3Lop3`, `ternaryK3Dag`).
   - 8-`LOP3` depth-3 `N=7` Harley–Seal 7→3 bit-counter compressor (`harleySealN7Lop3`, `harleySealN7Dag`).
3. Exact OCP FP8-E4M3 and FP8-E5M2 Kulisch integer encodings (`e4m3Scaled`, `e5m2Scaled`).
4. Exact SWAR64 bit-packed multi-lane dot-product accumulator (`swarPack64`, `swarDotAcc64`, `swarExtractLane`).
-/

namespace TernaryLop3Kulisch

/-! ## 1. PTX `LOP3.B32` Primitive and General `LOP3` DAGs -/

/-- Exact PTX 3-input Boolean lookup gate `lop3.b32`:
    returns bit `(4 * a + 2 * b + c)` of `imm8` (`a = 0xF0, b = 0xCC, c = 0xAA`). -/
def lop3 (imm8 : UInt8) (a b c : Bool) : Bool :=
  ((imm8.toNat >>> ((if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0))) &&& 1) == 1

/-- A single `LOP3` gate referencing three earlier wire indices `(a, b, c)` and truth table `imm8`. -/
structure Lop3Gate where
  a : Nat
  b : Nat
  c : Nat
  imm8 : UInt8
deriving Repr, DecidableEq

/-- An acyclic `LOP3` circuit represented as a list of gates appended sequentially after the inputs. -/
abbrev Lop3Dag := List Lop3Gate

/-- Sequentially append evaluated `LOP3` gates onto the wire table `wires`.
    Out-of-range wire references default to constant `false`, so every `Lop3Dag` is automatically acyclic. -/
def evalDagGo (wires : List Bool) : Lop3Dag → List Bool
  | [] => wires
  | g :: rest =>
    let va := wires.getD g.a false
    let vb := wires.getD g.b false
    let vc := wires.getD g.c false
    evalDagGo (wires ++ [lop3 g.imm8 va vb vc]) rest

/-- Evaluate all wires (primary inputs `0 .. n - 1` followed by gate outputs `n .. n + dag.length - 1`). -/
def evalDag {n : Nat} (dag : Lop3Dag) (x : Fin n → Bool) : List Bool :=
  evalDagGo ((List.finRange n).map x) dag

/-- Value of wire `w` in `dag` on input `x : Fin n → Bool`. -/
def evalWire {n : Nat} (dag : Lop3Dag) (x : Fin n → Bool) (w : Nat) : Bool :=
  (evalDag dag x).getD w false

/-! ## 2. Balanced-Ternary & Parallel Bit-Counter Specifications and Circuits -/

/-- Value of a balanced trit encoded as `(p, n)` (`p = +1`, `n = -1`). -/
def tritVal (p n : Bool) : Int :=
  (if p then 1 else 0) - (if n then 1 else 0)

/-- Validity predicate for a balanced trit `(p, n)`: excludes the invalid state `(true, true)`. -/
def tritValid (p n : Bool) : Bool :=
  !(p && n)

/-- Signed 3-bit two's-complement integer value of `(s0, s1, s2)` in `{-4, ..., +3}`. -/
def twosComp3 (s0 s1 s2 : Bool) : Int :=
  (if s0 then 1 else 0) + 2 * (if s1 then 1 else 0) - 4 * (if s2 then 1 else 0)

/-- Unsigned 3-bit integer value of `(s0, s1, s2)` in `{0, ..., 7}`. -/
def u3Val (s0 s1 s2 : Bool) : Nat :=
  (if s0 then 1 else 0) + 2 * (if s1 then 1 else 0) + 4 * (if s2 then 1 else 0)

/-- Exact 4-`LOP3` depth-3 `K=2` balanced-ternary counter (`4 inputs → 3-bit two's complement`).
    Synthesized on RX 7900 XTX (`results.json`: `Ternary_K2_4LOP3_exhaustive`). -/
def ternaryK2Lop3 (p0 n0 p1 n1 : Bool) : Bool × Bool × Bool :=
  let g0 := lop3 0x16 p0 p1 n1
  let s0 := lop3 0x26 p0 n0 g0
  let s2 := lop3 0x98 n0 n1 g0
  let s1 := lop3 0x42 p0 p1 s2
  (s0, s1, s2)

/-- The 4-`LOP3` `K=2` balanced-ternary counter represented explicitly as a `Lop3Dag` of length 4. -/
def ternaryK2Dag : Lop3Dag :=
  [ ⟨0, 2, 3, 0x16⟩,
    ⟨0, 1, 4, 0x26⟩,
    ⟨1, 3, 4, 0x98⟩,
    ⟨0, 2, 6, 0x42⟩ ]

/-- Validity predicate on 4-bit input `x : Fin 4 → Bool` for `K=2` balanced ternary (`9/16` valid). -/
def validK2 (x : Fin 4 → Bool) : Prop :=
  tritValid (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) = true ∧
  tritValid (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) = true

/-- Exact 7-`LOP3` depth-3 `K=3` balanced-ternary counter (`6 inputs → 3-bit two's complement`).
    Synthesized on RX 7900 XTX (`results.json`: `Ternary_K3_7LOP3_twoscomp_mixed`). -/
def ternaryK3Lop3 (p0 n0 p1 n1 p2 n2 : Bool) : Bool × Bool × Bool :=
  let t0 := lop3 0x96 p0 n0 p1
  let t1 := lop3 0x96 n1 p2 n2
  let s0 := lop3 0x3C t0 t1 p0
  let g3 := lop3 0x0D p0 n0 p1
  let g4 := lop3 0x1B n1 t0 t1
  let s1 := lop3 0x96 n2 g3 g4
  let s2 := lop3 0xD4 n2 g3 g4
  (s0, s1, s2)

/-- The 7-`LOP3` `K=3` balanced-ternary counter represented explicitly as a `Lop3Dag` of length 7. -/
def ternaryK3Dag : Lop3Dag :=
  [ ⟨0, 1, 2, 0x96⟩,
    ⟨3, 4, 5, 0x96⟩,
    ⟨6, 7, 0, 0x3C⟩,
    ⟨0, 1, 2, 0x0D⟩,
    ⟨3, 6, 7, 0x1B⟩,
    ⟨5, 9, 10, 0x96⟩,
    ⟨5, 9, 10, 0xD4⟩ ]

/-- Validity predicate on 6-bit input `x : Fin 6 → Bool` for `K=3` balanced ternary (`27/64` valid). -/
def validK3 (x : Fin 6 → Bool) : Prop :=
  tritValid (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) = true ∧
  tritValid (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) = true ∧
  tritValid (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) = true

/-- Exact popcount of 7 Boolean inputs. -/
def popcount7 (x0 x1 x2 x3 x4 x5 x6 : Bool) : Nat :=
  (if x0 then 1 else 0) + (if x1 then 1 else 0) + (if x2 then 1 else 0) +
  (if x3 then 1 else 0) + (if x4 then 1 else 0) + (if x5 then 1 else 0) +
  (if x6 then 1 else 0)

/-- Exact popcount of a 7-bit input vector `x : Fin 7 → Bool`. -/
def popcount7Vec (x : Fin 7 → Bool) : Nat :=
  popcount7
    (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)
    (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩)

/-- Exact 8-`LOP3` depth-3 `N=7` Harley–Seal 7→3 bit-counter compressor (4 full adders: `0x96 = XOR3`, `0xE8 = MAJ3`). -/
def harleySealN7Lop3 (x0 x1 x2 x3 x4 x5 x6 : Bool) : Bool × Bool × Bool :=
  let a0 := lop3 0x96 x0 x1 x2
  let c0 := lop3 0xE8 x0 x1 x2
  let a1 := lop3 0x96 x3 x4 x5
  let c1 := lop3 0xE8 x3 x4 x5
  let s0 := lop3 0x96 a0 a1 x6
  let c2 := lop3 0xE8 a0 a1 x6
  let s1 := lop3 0x96 c0 c1 c2
  let s2 := lop3 0xE8 c0 c1 c2
  (s0, s1, s2)

/-- The 8-`LOP3` `N=7` Harley–Seal 7→3 compressor represented explicitly as a `Lop3Dag` of length 8. -/
def harleySealN7Dag : Lop3Dag :=
  [ ⟨0, 1, 2, 0x96⟩,
    ⟨0, 1, 2, 0xE8⟩,
    ⟨3, 4, 5, 0x96⟩,
    ⟨3, 4, 5, 0xE8⟩,
    ⟨7, 9, 6, 0x96⟩,
    ⟨7, 9, 6, 0xE8⟩,
    ⟨8, 10, 12, 0x96⟩,
    ⟨8, 10, 12, 0xE8⟩ ]

/-! ## 3. OCP FP8-E4M3 and FP8-E5M2 Exact Kulisch Encodings -/

/-- Predicate for finite OCP FP8-E4M3 bit patterns (no Inf; only `exp = 15, mant = 7` is NaN). -/
def e4m3Finite (x : BitVec 8) : Bool :=
  !(((x.toNat >>> 3) &&& 15 == 15) && ((x.toNat &&& 7) == 7))

/-- Exact scaled integer value `val(x) * 2^9` of an OCP FP8-E4M3 byte (`0` for NaN).
    Minimum positive subnormal `0x01` has scaled value `1` (`2^-9`);
    maximum finite `0x7E` has scaled value `14 * 2^14 = 229,376 = 448 * 2^9`. -/
def e4m3Scaled (x : BitVec 8) : Int :=
  let s := (x.toNat >>> 7) &&& 1
  let e := (x.toNat >>> 3) &&& 15
  let m := x.toNat &&& 7
  if e == 15 && m == 7 then 0
  else
    let mag : Nat := if e == 0 then m else (8 + m) * (2 ^ (e - 1))
    if s == 1 then -(Int.ofNat mag) else Int.ofNat mag

/-- Exact scaled integer product `(val(x) * val(y)) * 2^18` of two OCP FP8-E4M3 bytes. -/
def e4m3ProdScaled (x y : BitVec 8) : Int :=
  e4m3Scaled x * e4m3Scaled y

/-- Exact unrounded Kulisch dot-product sum scaled by `2^18` for a list of OCP FP8-E4M3 pairs. -/
def e4m3DotScaled (pairs : List (BitVec 8 × BitVec 8)) : Int :=
  (pairs.map (fun p => e4m3ProdScaled p.1 p.2)).sum

/-- Predicate for finite OCP FP8-E5M2 bit patterns (`exp < 31`; `exp = 31` is Inf/NaN). -/
def e5m2Finite (x : BitVec 8) : Bool :=
  ((x.toNat >>> 2) &&& 31) != 31

/-- Exact scaled integer value `val(x) * 2^16` of an OCP FP8-E5M2 byte (`0` for Inf/NaN).
    Minimum positive subnormal `0x01` has scaled value `1` (`2^-16`);
    maximum finite `0x7B` has scaled value `7 * 2^29 = 3,758,096,384 = 57,344 * 2^16`. -/
def e5m2Scaled (x : BitVec 8) : Int :=
  let s := (x.toNat >>> 7) &&& 1
  let e := (x.toNat >>> 2) &&& 31
  let m := x.toNat &&& 3
  if e == 31 then 0
  else
    let mag : Nat := if e == 0 then m else (4 + m) * (2 ^ (e - 1))
    if s == 1 then -(Int.ofNat mag) else Int.ofNat mag

/-- Exact scaled integer product `(val(x) * val(y)) * 2^32` of two OCP FP8-E5M2 bytes. -/
def e5m2ProdScaled (x y : BitVec 8) : Int :=
  e5m2Scaled x * e5m2Scaled y

/-! ## 4. SWAR64 Bit-Packed Multi-Lane Dot-Product Definitions -/

/-- Predicate for balanced ternary integers `x ∈ {-1, 0, +1}`. -/
def IsTernary (x : Int) : Prop :=
  x = -1 ∨ x = 0 ∨ x = 1

/-- Predicate for two's-complement INT2 integers `x ∈ {-2, -1, 0, +1}`. -/
def IsInt2 (x : Int) : Prop :=
  x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1

/-- Exact integer sum over `Fin L`. -/
def sumInt {L : Nat} (f : Fin L → Int) : Int :=
  ((List.finRange L).map f).sum

/-- Exact integer dot product of two length-`L` vectors. -/
def exactDotInt {L : Nat} (a b : Fin L → Int) : Int :=
  sumInt (fun k => a k * b k)

/-- Exact natural-number sum over `Fin L`. -/
def sumNat {L : Nat} (f : Fin L → Nat) : Nat :=
  ((List.finRange L).map f).sum

/-- Pack `P` nonnegative lane values `v 0, ..., v (P-1)` at bit-stride `S` into a natural number. -/
def swarPackNat (P S : Nat) (v : Fin P → Nat) : Nat :=
  sumNat (fun p => v p * 2 ^ (p.val * S))

/-- Pack `P` nonnegative lane values at bit-stride `S` into a `uint64` (`BitVec 64`). -/
def swarPack64 (P S : Nat) (v : Fin P → Nat) : BitVec 64 :=
  BitVec.ofNat 64 (swarPackNat P S v)

/-- Extract lane `p` of width `S` bits from a `uint64` accumulator `acc` via shift-and-mask:
    `(acc >>> (p * S)) &&& ((1 <<< S) - 1)`. -/
def swarExtractLane (S : Nat) (acc : BitVec 64) (p : Nat) : Nat :=
  (acc.toNat >>> (p * S)) &&& ((1 <<< S) - 1)

/-- Single-`IMAD` `uint64` SWAR accumulator across `L` steps:
    `acc = ∑_{k < L} swarPack64 P S (a k) * (b k)` modulo `2^64`. -/
def swarDotAcc64 (P S L : Nat) (a : Fin L → Fin P → Nat) (b : Fin L → Nat) : BitVec 64 :=
  ((List.finRange L).map (fun k => swarPack64 P S (a k) * BitVec.ofNat 64 (b k))).foldl (· + ·) 0

end TernaryLop3Kulisch
