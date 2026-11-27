/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`gray-carry-whitening-transducer`)

Gray-code carry whitening via balanced-fiber transducer lifts: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace GrayTransducerEngine

/-- A general finite-state LSB-first Mealy transducer consuming bit-pairs `(x, y)`
    and producing outputs of type `Out`. -/
structure BinTransducer (S : Type) (Out : Type) where
  step : S → Bool → Bool → S
  out  : S → Bool → Bool → Out

/-- State of transducer `M` after reading the lowest `i` bit-pairs of `(a, b)`. -/
def stateAt {S Out : Type} (M : BinTransducer S Out) (s0 : S) (a b : Nat) : Nat → S
  | 0     => s0
  | i + 1 => M.step (stateAt M s0 a b i) (a.testBit i) (b.testBit i)

/-- Output of transducer `M` at bit position `i` on `(a, b)`. -/
def outAt {S Out : Type} (M : BinTransducer S Out) (s0 : S) (a b : Nat) (i : Nat) : Out :=
  M.out (stateAt M s0 a b i) (a.testBit i) (b.testBit i)

/-- Run a bit-pair-output transducer for `w` steps, assembling a `w`-bit pair `(u, v) < 2^w`. -/
def runPair {S : Type} (M : BinTransducer S (Bool × Bool)) (s0 : S) :
    Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0, 0)
  | w + 1, a, b =>
    let a0 := a.testBit 0
    let b0 := b.testBit 0
    let out0 := M.out s0 a0 b0
    let rest := runPair M (M.step s0 a0 b0) w (a / 2) (b / 2)
    (2 * rest.1 + out0.1.toNat, 2 * rest.2 + out0.2.toNat)

def sumNat : Nat → (Nat → Nat) → Nat
  | 0, _     => 0
  | k + 1, f => sumNat k f + f k

/-- Exact count of pairs `(a, b) ∈ [0, 2^w)^2` satisfying decidable predicate `P`. -/
def countPairs (w : Nat) (P : Nat → Nat → Bool) : Nat :=
  sumNat (2 ^ w) fun a => sumNat (2 ^ w) fun b => if P a b then 1 else 0

/-- Run a transducer for `w` steps, collecting the `w` LSB-first outputs into a `List Out`. -/
def runList {S Out : Type} (M : BinTransducer S Out) (s0 : S) :
    Nat → Nat → Nat → List Out
  | 0, _, _     => []
  | w + 1, a, b =>
    M.out s0 (a.testBit 0) (b.testBit 0) ::
      runList M (M.step s0 (a.testBit 0) (b.testBit 0)) w (a / 2) (b / 2)

/-- Number of input bit-pairs `(x, y) ∈ Bool²` producing output `o` from state `s`. -/
def sliceCount {S Out : Type} [DecidableEq Out] (M : BinTransducer S Out) (s : S) (o : Out) : Nat :=
  (if M.out s false false = o then 1 else 0) +
  (if M.out s false true  = o then 1 else 0) +
  (if M.out s true  false = o then 1 else 0) +
  (if M.out s true  true  = o then 1 else 0)

/-- Binary reflected Gray code `G(n) = n ^^^ (n >>> 1)`. -/
def gray (n : Nat) : Nat := n ^^^ (n >>> 1)

/-- Fuel-bounded structural recursion for `grayInv` (reduces cleanly in kernel `decide`). -/
def grayInvAux : Nat → Nat → Nat
  | 0, _     => 0
  | _ + 1, 0 => 0
  | f + 1, x => x ^^^ grayInvAux f (x >>> 1)

/-- Exact inverse Gray code `G⁻¹(x) = XOR_{k >= 0} (x >>> k)`. -/
def grayInv (x : Nat) : Nat := grayInvAux x x

/-- Fuel-bounded structural recursion for `parity` (reduces cleanly in kernel `decide`). -/
def parityAux : Nat → Nat → Bool
  | 0, _     => false
  | _ + 1, 0 => false
  | f + 1, x => Bool.xor (x.testBit 0) (parityAux f (x >>> 1))

/-- Global bit-parity `P(x) = popcount(x) mod 2`. -/
def parity (x : Nat) : Bool := parityAux x x

/-- Fuel-bounded structural recursion for `popcount` (reduces cleanly in kernel `decide`). -/
def popcountAux : Nat → Nat → Nat
  | 0, _     => 0
  | _ + 1, 0 => 0
  | f + 1, x => (x % 2) + popcountAux f (x / 2)

/-- Exact Hamming weight (popcount) of a natural number. -/
def popcount (x : Nat) : Nat := popcountAux x x

/-- Gray-code addition with carry-in `c0`: `G(G⁻¹(x) + G⁻¹(y) + c0)`. -/
def grayAddWith (x y : Nat) (c0 : Bool) : Nat := gray (grayInv x + grayInv y + c0.toNat)

/-- Gray-code addition `x ⊞ y = G(G⁻¹(x) + G⁻¹(y))`. -/
def grayAdd (x y : Nat) : Nat := grayAddWith x y false

/-- Gray-code subtraction with borrow-in `b0`: `G(G⁻¹(x) - G⁻¹(y) - b0)`. -/
def graySubWith (x y : Nat) (b0 : Bool) : Nat := gray (grayInv x - grayInv y - b0.toNat)

/-- Gray-code subtraction `x ⊟ y = G(G⁻¹(x) - G⁻¹(y))`. -/
def graySub (x y : Nat) : Nat := graySubWith x y false

/-- Gray-code doubling `2_G(x) = G(2 * G⁻¹(x))`. -/
def grayDouble (x : Nat) : Nat := gray (2 * grayInv x)

/-- Carry word of binary addition with carry-in `c0`. -/
def carryWord (a b : Nat) (c0 : Bool) : Nat := (a + b + c0.toNat) ^^^ a ^^^ b

/-- Borrow word of binary subtraction with borrow-in `b0` (for `b + b0 ≤ a`). -/
def borrowWord (a b : Nat) (b0 : Bool) : Nat := (a - b - b0.toNat) ^^^ a ^^^ b

/-- Full `(w+1)`-bit borrow word on `[0, 2^w)^2` without requiring `a ≥ b`. -/
def borrowWordFull (w a b : Nat) (b0 : Bool) : Nat :=
  ((2 ^ w + a - b - b0.toNat) ^^^ 2 ^ w) ^^^ a ^^^ b

def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def carryAt (a b : Nat) (c0 : Bool) : Nat → Bool
  | 0     => c0
  | i + 1 => maj (a.testBit i) (b.testBit i) (carryAt a b c0 i)

def borrowAt (a b : Nat) (b0 : Bool) : Nat → Bool
  | 0     => b0
  | i + 1 => maj (!(a.testBit i)) (b.testBit i) (borrowAt a b b0 i)

/-- Naive 8-state LSB Gray-addition transducer with state `(a_i, b_i, c_i)`. -/
def grayAddTransducer8 : BinTransducer (Bool × Bool × Bool) Bool where
  step := fun (a, b, c) xi yi => (Bool.xor a xi, Bool.xor b yi, maj a b c)
  out  := fun (a, b, c) xi yi => Bool.xor (Bool.xor xi yi) (Bool.xor c (maj a b c))

/-- Minimal 4-state quotient LSB Gray-addition transducer with state `(d_i, e_i) = (a_i ^ b_i, a_i ^ c_i)`. -/
def grayAddTransducer4 : BinTransducer (Bool × Bool) Bool where
  step := fun (d, e) xi yi => (Bool.xor d (Bool.xor xi yi), Bool.xor (d && e) xi)
  out  := fun (d, e) xi yi => Bool.xor (Bool.xor xi yi) ((!d) && e)

/-- Quotient projection `π(a, b, c) = (a ^ b, a ^ c)`. -/
def grayAddQuotient (s : Bool × Bool × Bool) : Bool × Bool :=
  (Bool.xor s.1 s.2.1, Bool.xor s.1 s.2.2)

/-- Joint 4-state Carry-Borrow Gray-Difference Transducer:
    State `(c, bor) ∈ Bool²`, outputs `(δ⁺_i, δ⁻_i) = (c_i ^ c_{i+1}, bor_i ^ bor_{i+1})`. -/
def carryBorrowTransducer : BinTransducer (Bool × Bool) (Bool × Bool) where
  step := fun (c, bor) ai bi => (maj ai bi c, maj (!ai) bi bor)
  out  := fun (c, bor) ai bi =>
    (Bool.xor c (maj ai bi c), Bool.xor bor (maj (!ai) bi bor))

/-- Forward 4-state transducer for `Φ_{w,c0,b0}(a, b) = (a ^^^ b, (G(a+b+c0) ^^^ G((2^w+a-b-b0) ^^^ 2^w)) % 2^w)`. -/
def phiTransducer : BinTransducer (Bool × Bool) (Bool × Bool) where
  step := fun (c, bor) ai bi => (maj ai bi c, maj (!ai) bi bor)
  out  := fun (c, bor) ai bi =>
    (Bool.xor ai bi,
     Bool.xor (Bool.xor c (maj ai bi c)) (Bool.xor bor (maj (!ai) bi bor)))

/-- Explicit 4-state LSB inverse transducer `Φ⁻¹`. -/
def phiInvTransducer : BinTransducer (Bool × Bool) (Bool × Bool) where
  step := fun (c, bor) di ti =>
    if !di then (Bool.xor c ti, bor) else (c, Bool.xor bor ti)
  out  := fun (c, bor) di ti =>
    if !di then (Bool.xor c ti, Bool.xor c ti)
    else (!(Bool.xor bor ti), Bool.xor bor ti)

/-- Direct arithmetic definition of `Φ_{w,c0,b0}` on `[0, 2^w)^2`. -/
def phiMap (w : Nat) (c0 b0 : Bool) (a b : Nat) : Nat × Nat :=
  (a ^^^ b, (gray (a + b + c0.toNat) ^^^ gray ((2 ^ w + a - b - b0.toNat) ^^^ 2 ^ w)) % 2 ^ w)

/-- Explicit inverse `Φ⁻¹_{w,c0,b0}` executed by the 4-state inverse transducer. -/
def phiMapInv (w : Nat) (c0 b0 : Bool) (d t : Nat) : Nat × Nat :=
  runPair phiInvTransducer (c0, b0) w d t

/-- Extract the lowest `w` bits of a pair `(u, v)` as a `List (Bool × Bool)`. -/
def pairBits : Nat → Nat → Nat → List (Bool × Bool)
  | 0, _, _     => []
  | w + 1, u, v => (u.testBit 0, v.testBit 0) :: pairBits w (u / 2) (v / 2)

def jointMult : Bool × Bool → Nat
  | (false, false) => 2
  | (true,  false) => 1
  | (false, true)  => 1
  | (true,  true)  => 0

/-- 2-state Carry-Difference Transducer: state `c ∈ Bool`, output `c ^ maj(a, b, c)`. -/
def carryDiffTransducer : BinTransducer Bool Bool where
  step := fun c ai bi => maj ai bi c
  out  := fun c ai bi => Bool.xor c (maj ai bi c)

def carryDiffMult : Bool → Nat
  | false => 3
  | true  => 1

/-- Extract the lowest `w` bits of `z` as a `List Bool`. -/
def wordBits : Nat → Nat → List Bool
  | 0, _     => []
  | w + 1, z => z.testBit 0 :: wordBits w (z / 2)

/-- General finite-state LSB-first Mealy transducer over arbitrary radix `B` digit-pairs. -/
structure RadixTransducer (B : Nat) (S : Type) (Out : Type) where
  step : S → Nat → Nat → S
  out  : S → Nat → Nat → Out

/-- Run a base-`B` transducer for `w` LSB-first digit steps, collecting the `w` outputs. -/
def runListBase {B : Nat} {S Out : Type} (M : RadixTransducer B S Out) (s0 : S) :
    Nat → Nat → Nat → List Out
  | 0, _, _     => []
  | w + 1, a, b =>
    M.out s0 (a % B) (b % B) ::
      runListBase M (M.step s0 (a % B) (b % B)) w (a / B) (b / B)

/-- Exact count of pairs `(a, b) ∈ [0, B^w)^2` satisfying decidable predicate `P`. -/
def countPairsBase (B w : Nat) (P : Nat → Nat → Bool) : Nat :=
  sumNat (B ^ w) fun a => sumNat (B ^ w) fun b => if P a b then 1 else 0

/-- Single-step radix-`B` fiber multiplicity of output `o` from state `s`. -/
def sliceCountBase (B : Nat) {S Out : Type} [DecidableEq Out]
    (M : RadixTransducer B S Out) (s : S) (o : Out) : Nat :=
  sumNat B fun da => sumNat B fun db => if M.out s da db = o then 1 else 0

/-- Exact base-`B` carry-in bit into digit position `i` of `a + b + c0`:
    `carryAtBase B a b c0 i = decide (a % B^i + b % B^i + c0 ≥ B^i)`. -/
def carryAtBase (B a b : Nat) (c0 : Bool) (i : Nat) : Bool :=
  decide (B ^ i ≤ a % B ^ i + b % B ^ i + c0.toNat)

/-- Base-`B` carry-transition word (bit `i` is `c_i ^^ c_{i+1}` for `i < w`). -/
def carryDiffWordBase (B : Nat) (c0 : Bool) (a b : Nat) : Nat → Nat
  | 0     => 0
  | w + 1 =>
    carryDiffWordBase B c0 a b w +
      (Bool.xor (carryAtBase B a b c0 w) (carryAtBase B a b c0 (w + 1))).toNat * 2 ^ w

/-- 2-state Base-`B` Carry-Transition Transducer. -/
def radixCarryDiffTransducer (B : Nat) : RadixTransducer B Bool Bool where
  step := fun c da db => decide (B ≤ da + db + c.toNat)
  out  := fun c da db => Bool.xor c (decide (B ≤ da + db + c.toNat))

def radixCarryDiffMult (B : Nat) : Bool → Nat
  | false => B * (B + 1) / 2
  | true  => B * (B - 1) / 2

def sumInt : Nat → (Nat → Int) → Int
  | 0, _     => 0
  | k + 1, f => sumInt k f + f k

/-- Number of `k`-operand bit-slices `v ∈ [0, 2^k)` whose Gray carry-transition bit
    `(c + (c + popcount v) / 2) % 2` equals `1`, from incoming carry state `c`. -/
def multiCarrySlice1 (k c : Nat) : Nat :=
  sumNat (2 ^ k) fun v => if (c + (c + popcount v) / 2) % 2 = 1 then 1 else 0

/-- Exact signed bias `D(k, c) = 2^k - 2 * multiCarrySlice1 k c = ∑_{v < 2^k} (-1)^(c + ⌊(c + |v|)/2⌋)`. -/
def multiCarryBias (k c : Nat) : Int :=
  (2 ^ k : Int) - 2 * (multiCarrySlice1 k c : Int)

/-- Auxiliary signed sum `S(k, s0) = ∑_{v < 2^k} (-1)^⌊(s0 + |v|)/2⌋`. -/
def carrySumBias (k s0 : Nat) : Int :=
  sumInt (2 ^ k) fun v => if ((s0 + popcount v) / 2) % 2 = 0 then 1 else -1

end GrayTransducerEngine
