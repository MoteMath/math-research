/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`SiliconCircuitBisimCompiler`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace SiliconBisim

-- ============================================================================
-- SECTION 0: PURE-SILICON COMBINATIONAL GATE-DAG LANGUAGE (`GateNet`)
-- ============================================================================

/-- Primitive pure-silicon Boolean gates. Wire indices `0 .. inW-1` are primary inputs;
    wire index `inW + i` is the output of gate `i`. -/
inductive GateOp where
  | const0
  | const1
  | not  (a : Nat)
  | and  (a b : Nat)
  | or   (a b : Nat)
  | xor  (a b : Nat)
  | nand (a b : Nat)
  | nor  (a b : Nat)
  | xnor (a b : Nat)
  | mux  (s d0 d1 : Nat)
  deriving Repr, DecidableEq

/-- A concrete combinational Boolean gate DAG. -/
structure GateNet where
  inW   : Nat
  gates : List GateOp
  outs  : List Nat
  deriving Repr, DecidableEq

/-- Read wire `i` from a wire-value list (defaulting to `false` if out of bounds). -/
def wireAt (wires : List Bool) (i : Nat) : Bool :=
  wires.getD i false

/-- Evaluate a single gate against the current wire values. -/
def evalGateOp (wires : List Bool) : GateOp → Bool
  | .const0       => false
  | .const1       => true
  | .not a        => !(wireAt wires a)
  | .and a b      => wireAt wires a && wireAt wires b
  | .or a b       => wireAt wires a || wireAt wires b
  | .xor a b      => xor (wireAt wires a) (wireAt wires b)
  | .nand a b     => !(wireAt wires a && wireAt wires b)
  | .nor a b      => !(wireAt wires a || wireAt wires b)
  | .xnor a b     => !(xor (wireAt wires a) (wireAt wires b))
  | .mux s d0 d1  => if wireAt wires s then wireAt wires d1 else wireAt wires d0

/-- Sequentially append evaluated gate outputs to the wire list. -/
def evalGatesAux (wires : List Bool) : List GateOp → List Bool
  | []      => wires
  | g :: gs => evalGatesAux (wires ++ [evalGateOp wires g]) gs

/-- Evaluate a `GateNet` on a `List Bool` of primary inputs. -/
def evalGateNetList (net : GateNet) (inp : List Bool) : List Bool :=
  let allWires := evalGatesAux inp net.gates
  net.outs.map (wireAt allWires)

/-- Convert a `BitVec n` to its LSB-first `List Bool` of length `n`. -/
def bvToList {n : Nat} (v : BitVec n) : List Bool :=
  (List.range n).map (fun i => v.getLsbD i)

/-- Pack an LSB-first `List Bool` into a `Nat`. -/
def listToNat : List Bool → Nat
  | []      => 0
  | b :: bs => (if b then 1 else 0) + 2 * listToNat bs

/-- Pack an LSB-first `List Bool` into a `BitVec n`. -/
def listToBv (n : Nat) (bs : List Bool) : BitVec n :=
  BitVec.ofNat n (listToNat bs)

/-- Evaluate a `GateNet` on `BitVec net.inW`, returning `BitVec net.outs.length`. -/
def evalGateNet (net : GateNet) (inp : BitVec net.inW) : BitVec net.outs.length :=
  listToBv net.outs.length (evalGateNetList net (bvToList inp))

/-- Helper: concatenate two `BitVec` values (LSB part `a` at low bits, `b` at high bits). -/
def bvCat {m n : Nat} (a : BitVec m) (b : BitVec n) : BitVec (m + n) :=
  BitVec.ofNat (m + n) (a.toNat + b.toNat * 2 ^ m)

/-- Extract the low `m` bits of a `BitVec (m + n)`. -/
def bvLo {m n : Nat} (v : BitVec (m + n)) : BitVec m :=
  BitVec.ofNat m v.toNat

/-- Extract the high `n` bits of a `BitVec (m + n)`. -/
def bvHi {m n : Nat} (v : BitVec (m + n)) : BitVec n :=
  BitVec.ofNat n (v.toNat / 2 ^ m)

/-- Exhaustive decidable universal quantifier over `BitVec n` (`0 .. 2^n - 1`). -/
def forallBv (n : Nat) (P : BitVec n → Bool) : Bool :=
  (List.range (2 ^ n)).all (fun k => P (BitVec.ofNat n k))

-- ============================================================================
-- SECTION 1: ENGINE 1 — LINEAR & MULTI-STRIDE BIT-SLICE BISIMULATION COMPILER
-- ============================================================================

/-- A linear bit-slice circuit generator with state width `stW`, input slice width `inW`,
    output slice width `outW`, and final summary width `finW`.
    `stepNet` takes `bvCat state inSlice` (`stW + inW` bits) and outputs `bvCat nextState outSlice`
    (`stW + outW` bits). `finNet` maps final state (`stW` bits) to final output (`finW` bits). -/
structure SliceGen where
  stW     : Nat
  inW     : Nat
  outW    : Nat
  finW    : Nat
  initSt  : BitVec stW
  stepNet : GateNet
  finNet  : GateNet
  hStepIn : stepNet.inW = stW + inW
  hStepOut: stepNet.outs.length = stW + outW
  hFinIn  : finNet.inW = stW
  hFinOut : finNet.outs.length = finW

def SliceGen.step (G : SliceGen) (q : BitVec G.stW) (x : BitVec G.inW) :
    BitVec G.stW × BitVec G.outW :=
  let inp : BitVec G.stepNet.inW := G.hStepIn ▸ bvCat q x
  let out : BitVec (G.stW + G.outW) := G.hStepOut ▸ evalGateNet G.stepNet inp
  (bvLo out, bvHi out)

def SliceGen.final (G : SliceGen) (q : BitVec G.stW) : BitVec G.finW :=
  G.hFinOut ▸ evalGateNet G.finNet (G.hFinIn ▸ q)

/-- Evaluate a `SliceGen` from an arbitrary starting state `q` over a list of input slices. -/
def evalSliceFrom (G : SliceGen) (q : BitVec G.stW) :
    List (BitVec G.inW) → List (BitVec G.outW) × BitVec G.finW
  | []      => ([], G.final q)
  | x :: xs =>
    let (q', y) := G.step q x
    let (ys, f) := evalSliceFrom G q' xs
    (y :: ys, f)

/-- Evaluate a `SliceGen` from its initial state on an arbitrary-width input stream. -/
def evalSliceGen (G : SliceGen) (xs : List (BitVec G.inW)) :
    List (BitVec G.outW) × BitVec G.finW :=
  evalSliceFrom G G.initSt xs

/-- Finite binary bisimulation certificate between two `SliceGen`s of possibly DIFFERENT
    state widths `s1, s2`: an explicit bitmask of `2^(s1 + s2)` bits encoding `R(q1, q2)`. -/
structure SliceBisimCert (s1 s2 : Nat) where
  relMask : BitVec (2 ^ (s1 + s2))
  deriving Repr, DecidableEq

def SliceBisimCert.rel {s1 s2 : Nat} (cert : SliceBisimCert s1 s2)
    (q1 : BitVec s1) (q2 : BitVec s2) : Bool :=
  cert.relMask.getLsbD (bvCat q1 q2).toNat

/-- Decidable finite base + inductive-step + finalization bisimulation checker. -/
def checkSliceBisim (G1 G2 : SliceGen)
    (hIn : G1.inW = G2.inW) (hOut : G1.outW = G2.outW) (hFin : G1.finW = G2.finW)
    (cert : SliceBisimCert G1.stW G2.stW) : Bool :=
  let baseOk := cert.rel G1.initSt G2.initSt
  let stepOk := forallBv G1.stW fun q1 =>
    forallBv G2.stW fun q2 =>
      if cert.rel q1 q2 then
        forallBv G1.inW fun x =>
          let (q1', y1) := G1.step q1 x
          let (q2', y2) := G2.step q2 (hIn ▸ x)
          decide (y1 = (hOut ▸ y2)) && cert.rel q1' q2'
      else true
  let finOk := forallBv G1.stW fun q1 =>
    forallBv G2.stW fun q2 =>
      if cert.rel q1 q2 then
        decide (G1.final q1 = (hFin ▸ G2.final q2))
      else true
  baseOk && stepOk && finOk

/-- **Engine 1B (Multi-Stride / 2-Bit Block Speculative Synchronization)**:
    Compare a 1-bit-per-step `SliceGen` `G1` against a 2-bit-per-step block generator `B2`
    (e.g. a 2-bit speculative Carry-Select Adder) across ALL even widths `2 * n` (`∀ n : Nat`)! -/
structure Block2Gen where
  stW     : Nat
  inW     : Nat   -- single-slice input width; block takes `inW + inW`
  outW    : Nat   -- single-slice output width; block produces `stW + outW + outW`
  finW    : Nat
  initSt  : BitVec stW
  stepNet : GateNet
  finNet  : GateNet
  hStepIn : stepNet.inW = stW + (inW + inW)
  hStepOut: stepNet.outs.length = stW + (outW + outW)
  hFinIn  : finNet.inW = stW
  hFinOut : finNet.outs.length = finW

def Block2Gen.step (B : Block2Gen) (q : BitVec B.stW) (x0 x1 : BitVec B.inW) :
    BitVec B.stW × BitVec B.outW × BitVec B.outW :=
  let inp : BitVec B.stepNet.inW := B.hStepIn ▸ bvCat q (bvCat x0 x1)
  let out : BitVec (B.stW + (B.outW + B.outW)) := B.hStepOut ▸ evalGateNet B.stepNet inp
  let q' := bvLo out
  let ys := bvHi out
  (q', bvLo ys, bvHi ys)

def Block2Gen.final (B : Block2Gen) (q : BitVec B.stW) : BitVec B.finW :=
  B.hFinOut ▸ evalGateNet B.finNet (B.hFinIn ▸ q)

-- ============================================================================
-- SECTION 2: ENGINE 2 — DYADIC PARALLEL-PREFIX TREE BISIMULATION COMPILER
-- ============================================================================

/-- A concrete gate-level parallel-prefix circuit specification:
    - `preNet`  : `inW → tokW` (local generate/propagate or prefix-token extractor)
    - `opNet`   : `tokW + tokW → tokW` (binary prefix combine cell `op(left, right)`)
    - `postNet` : `inW + stW → outW` (output slice given input slice and incoming state)
    - `actNet`  : `tokW + stW → stW` (how a prefix token acts on incoming carry/state) -/
structure PrefixSpec where
  inW     : Nat
  tokW    : Nat
  stW     : Nat
  outW    : Nat
  preNet  : GateNet
  opNet   : GateNet
  actNet  : GateNet
  postNet : GateNet
  hPreIn  : preNet.inW = inW
  hPreOut : preNet.outs.length = tokW
  hOpIn   : opNet.inW = tokW + tokW
  hOpOut  : opNet.outs.length = tokW
  hActIn  : actNet.inW = tokW + stW
  hActOut : actNet.outs.length = stW
  hPostIn : postNet.inW = inW + stW
  hPostOut: postNet.outs.length = outW

def PrefixSpec.pre (P : PrefixSpec) (x : BitVec P.inW) : BitVec P.tokW :=
  P.hPreOut ▸ evalGateNet P.preNet (P.hPreIn ▸ x)

def PrefixSpec.op (P : PrefixSpec) (u v : BitVec P.tokW) : BitVec P.tokW :=
  P.hOpOut ▸ evalGateNet P.opNet (P.hOpIn ▸ bvCat u v)

def PrefixSpec.act (P : PrefixSpec) (t : BitVec P.tokW) (c : BitVec P.stW) : BitVec P.stW :=
  P.hActOut ▸ evalGateNet P.actNet (P.hActIn ▸ bvCat t c)

def PrefixSpec.post (P : PrefixSpec) (x : BitVec P.inW) (c : BitVec P.stW) : BitVec P.outW :=
  P.hPostOut ▸ evalGateNet P.postNet (P.hPostIn ▸ bvCat x c)

/-- Contiguous range fold `op(xs[lo], op(xs[lo+1], ...))` for `len` elements starting at `lo`
    (with `len ≥ 1`, left-associated). -/
def rangeFold {α : Type} (op : α → α → α) (xs : Nat → α) (lo : Nat) : (len : Nat) → α
  | 0     => xs lo
  | 1     => xs lo
  | n + 2 => op (rangeFold op xs lo (n + 1)) (xs (lo + n + 1))

-- FOUR DISTINCT CONCRETE PARALLEL-PREFIX HARDWARE TOPOLOGIES ON `Fin (2^k) → α`

/-- Helper: lift `Fin (2^k) → α` to `Nat → α` (using default element `d` out of bounds). -/
def liftFn {n : Nat} {α : Type} (d : α) (f : Fin n → α) (i : Nat) : α :=
  if h : i < n then f ⟨i, h⟩ else d

/-- Topology 1: **Serial (Ripple) Prefix Chain** (`depth 2^k - 1`). -/
def serialPrefix {α : Type} (op : α → α → α) : ∀ (k : Nat), (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α)
  | k, xs => fun i => rangeFold op (liftFn (xs ⟨0, Nat.two_pow_pos k⟩) xs) 0 (i.val + 1)

/-- Topology 2: **Sklansky Parallel-Prefix Tree** (divide-and-conquer MSB-fanout, `depth k`). -/
def sklanskyPrefix {α : Type} (op : α → α → α) : ∀ (k : Nat), (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α)
  | 0, xs => xs
  | k + 1, xs =>
    let half := 2 ^ k
    let L := sklanskyPrefix op k (fun i : Fin half => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let R := sklanskyPrefix op k (fun i : Fin half => xs ⟨half + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let lastL := L ⟨half - 1, by have := Nat.two_pow_pos k; omega⟩
    fun i =>
      if h : i.val < half then
        L ⟨i.val, h⟩
      else
        op lastL (R ⟨i.val - half, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩)

/-- Topology 3: **Brent–Kung Parallel-Prefix Tree** (odd-even contraction + recursion + expansion,
    fanout 2, `depth 2k - 1`). -/
def brentKungPrefix {α : Type} (op : α → α → α) : ∀ (k : Nat), (Fin (2 ^ k) → α) → (Fin (2 ^ k) → α)
  | 0, xs => xs
  | k + 1, xs =>
    let half := 2 ^ k
    let pairs : Fin half → α := fun j =>
      op (xs ⟨2 * j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩)
         (xs ⟨2 * j.val + 1, by have := j.isLt; simp [Nat.pow_succ]; omega⟩)
    let P := brentKungPrefix op k pairs
    fun i =>
      if h0 : i.val = 0 then
        xs ⟨0, Nat.two_pow_pos (k + 1)⟩
      else if hOdd : i.val % 2 = 1 then
        P ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
      else
        op (P ⟨i.val / 2 - 1, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩) (xs i)

/-- Single Kogge–Stone doubling stage at stride `2^s`. -/
def koggeStoneStage {α : Type} (op : α → α → α) {n : Nat} (s : Nat) (cur : Fin n → α) : Fin n → α :=
  fun i =>
    if i.val < 2 ^ s then
      cur i
    else
      op (cur ⟨i.val - 2 ^ s, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩) (cur i)

/-- Run `stages` stages `0, 1, ..., stages - 1` of Kogge–Stone. -/
def koggeStoneRun {α : Type} (op : α → α → α) {n : Nat} : Nat → (Fin n → α) → (Fin n → α)
  | 0, xs => xs
  | s + 1, xs => koggeStoneStage op s (koggeStoneRun op s xs)

/-- Topology 4: **Kogge–Stone Parallel-Prefix Network** (`k` doubling stages, `depth k`, fanout 2). -/
def koggeStonePrefix {α : Type} (op : α → α → α) (k : Nat) (xs : Fin (2 ^ k) → α) : Fin (2 ^ k) → α :=
  koggeStoneRun op k xs

/-- Evaluate a `PrefixSpec` using any `2^k`-wire prefix topology `topo` on `xs : Fin (2^k) → BitVec P.inW`
    and incoming carry/state `c0 : BitVec P.stW`, producing `2^k` output slices AND final carry/state! -/
def evalPrefixCircuit (P : PrefixSpec)
    (topo : (BitVec P.tokW → BitVec P.tokW → BitVec P.tokW) →
            (k : Nat) → (Fin (2 ^ k) → BitVec P.tokW) → (Fin (2 ^ k) → BitVec P.tokW))
    (k : Nat) (c0 : BitVec P.stW) (xs : Fin (2 ^ k) → BitVec P.inW) :
    (Fin (2 ^ k) → BitVec P.outW) × BitVec P.stW :=
  let toks := fun i => P.pre (xs i)
  let prefs := topo P.op k toks
  let outFn := fun i : Fin (2 ^ k) =>
    let cin :=
      if h : i.val = 0 then c0
      else P.act (prefs ⟨i.val - 1, by have := i.isLt; omega⟩) c0
    P.post (xs i) cin
  let cOut := P.act (prefs ⟨2 ^ k - 1, by have := Nat.two_pow_pos k; omega⟩) c0
  (outFn, cOut)

/-- Convert `Fin n → α` to a `List α` of length `n`. -/
def finToList {n : Nat} {α : Type} (f : Fin n → α) : List α :=
  (List.finRange n).map f

/-- Finite binary certificate connecting a gate-level `PrefixSpec` `P` to a reference bit-slice
    generator `G : SliceGen`, via a **reachable-token bitmask** `validMask : BitVec (2^tokW)`! -/
structure PrefixToSliceCert (tokW : Nat) where
  validMask : BitVec (2 ^ tokW)
  deriving Repr, DecidableEq

def PrefixToSliceCert.valid {tokW : Nat} (cert : PrefixToSliceCert tokW) (t : BitVec tokW) : Bool :=
  cert.validMask.getLsbD t.toNat

/-- Decidable finite certificate checker for `PrefixSpec P` against `SliceGen G`:
    1. `pre` lands in `valid`;
    2. `op` closes `valid`;
    3. `op` is associative ON `valid` (strictly weaker than global associativity!);
    4. `act` is a monoid-action homomorphism on `valid`: `act (op u v) c = act v (act u c)`;
    5. Base compatibility with `G`: `act (pre x) c = (G.step c x).1` and `post x c = (G.step c x).2`. -/
def checkPrefixToSliceCert (P : PrefixSpec) (G : SliceGen)
    (hIn : P.inW = G.inW) (hSt : P.stW = G.stW) (hOut : P.outW = G.outW)
    (cert : PrefixToSliceCert P.tokW) : Bool :=
  let preOk := forallBv P.inW fun x => cert.valid (P.pre x)
  let closedOk := forallBv P.tokW fun u =>
    forallBv P.tokW fun v =>
      if cert.valid u && cert.valid v then cert.valid (P.op u v) else true
  let assocOk := forallBv P.tokW fun u =>
    forallBv P.tokW fun v =>
      forallBv P.tokW fun w =>
        if cert.valid u && cert.valid v && cert.valid w then
          decide (P.op (P.op u v) w = P.op u (P.op v w))
        else true
  let homOk := forallBv P.tokW fun u =>
    forallBv P.tokW fun v =>
      if cert.valid u && cert.valid v then
        forallBv P.stW fun c =>
          decide (P.act (P.op u v) c = P.act v (P.act u c))
      else true
  let baseOk := forallBv P.stW fun c =>
    forallBv P.inW fun x =>
      let (q', y) := G.step (hSt ▸ c) (hIn ▸ x)
      decide (P.act (P.pre x) c = (hSt.symm ▸ q')) &&
      decide (P.post x c = (hOut.symm ▸ y))
  preOk && closedOk && assocOk && homOk && baseOk

def id1Net : GateNet := { inW := 1, gates := [], outs := [0] }

-- ============================================================================
-- CONCRETE PARALLEL-PREFIX ADDER SPECS & 4-WAY CROSS-ENCODING EQUIVALENCE
-- ============================================================================

-- Common post-processing net for all prefix adders: inputs [a, b, cin] → [a ^ b ^ cin]
def adderPostNet : GateNet :=
  { inW := 3, gates := [.xor 0 1, .xor 3 2], outs := [4] }

-- Common action net for positive-logic (g, p): inputs [g, p, c] → [g | (p & c)]
def adderActPosNet : GateNet :=
  { inW := 3, gates := [.and 1 2, .or 0 3], outs := [4] }

-- (A) XOR-propagate + DON'T-CARE-GLITCHED black cell!
--     pre(a, b) = (a & b, a ^ b)  [valid tokens: (0,0)=0, (1,0)=1, (0,1)=2; (1,1)=3 UNREACHABLE!]
--     op((gL,pL), (gR,pR)) = ((gR | (pR & gL)) ^ (gR & pR), pR & pL)
--     Inputs to op: 0=gL, 1=pL, 2=gR, 3=pR.
def preXorPropNet : GateNet :=
  { inW := 2, gates := [.and 0 1, .xor 0 1], outs := [2, 3] }

def opGlitchedNet : GateNet :=
  { inW := 4
    gates := [
      .and 3 0,     -- w4 = pR & gL
      .or  2 4,     -- w5 = gR | (pR & gL)
      .and 2 3,     -- w6 = gR & pR  (don't-care glitch term!)
      .xor 5 6,     -- w7 = g_out = (gR | (pR & gL)) ^ (gR & pR)
      .and 3 1      -- w8 = p_out = pR & pL
    ]
    outs := [7, 8] }

def prefixAdderGlitchedXorSpec : PrefixSpec :=
  { inW := 2, tokW := 2, stW := 1, outW := 1
    preNet := preXorPropNet, opNet := opGlitchedNet
    actNet := adderActPosNet, postNet := adderPostNet
    hPreIn := rfl, hPreOut := rfl, hOpIn := rfl, hOpOut := rfl
    hActIn := rfl, hActOut := rfl, hPostIn := rfl, hPostOut := rfl }

-- (B) OR-propagate + standard black cell!
--     pre(a, b) = (a & b, a | b)  [valid tokens: (0,0)=0, (0,1)=2, (1,1)=3; (1,0)=1 UNREACHABLE!]
def preOrPropNet : GateNet :=
  { inW := 2, gates := [.and 0 1, .or 0 1], outs := [2, 3] }

def opStdBlackNet : GateNet :=
  { inW := 4
    gates := [
      .and 3 0,     -- w4 = pR & gL
      .or  2 4,     -- w5 = gR | (pR & gL)
      .and 3 1      -- w6 = pR & pL
    ]
    outs := [5, 6] }

def prefixAdderOrPropSpec : PrefixSpec :=
  { inW := 2, tokW := 2, stW := 1, outW := 1
    preNet := preOrPropNet, opNet := opStdBlackNet
    actNet := adderActPosNet, postNet := adderPostNet
    hPreIn := rfl, hPreOut := rfl, hOpIn := rfl, hOpOut := rfl
    hActIn := rfl, hActOut := rfl, hPostIn := rfl, hPostOut := rfl }

-- (C) Active-Low Inverted Propagate (ng = ~(a&b), np = ~(a^b))!
--     op((ngL,npL), (ngR,npR)) = (ngR & (npR | ngL), npR | npL)
--     act((ng,np), c) = (~ng) | ((~np) & c)
def preActiveLowNet : GateNet :=
  { inW := 2, gates := [.nand 0 1, .xnor 0 1], outs := [2, 3] }

def opActiveLowNet : GateNet :=
  { inW := 4
    gates := [
      .or  3 0,     -- w4 = npR | ngL
      .and 2 4,     -- w5 = ngR & (npR | ngL)
      .or  3 1      -- w6 = npR | npL
    ]
    outs := [5, 6] }

def actActiveLowNet : GateNet :=
  { inW := 3
    gates := [
      .not 0,       -- w3 = ~ng
      .not 1,       -- w4 = ~np
      .and 4 2,     -- w5 = (~np) & c
      .or  3 5      -- w6 = (~ng) | ((~np) & c)
    ]
    outs := [6] }

def prefixAdderActiveLowSpec : PrefixSpec :=
  { inW := 2, tokW := 2, stW := 1, outW := 1
    preNet := preActiveLowNet, opNet := opActiveLowNet
    actNet := actActiveLowNet, postNet := adderPostNet
    hPreIn := rfl, hPreOut := rfl, hOpIn := rfl, hOpOut := rfl
    hActIn := rfl, hActOut := rfl, hPostIn := rfl, hPostOut := rfl }

-- (D) XOR-black-cell `(gR ^ (pR & gL), pR & pL)` — valid for XOR-prop, INVALID for OR-prop!
def opXorBlackNet : GateNet :=
  { inW := 4
    gates := [
      .and 3 0,     -- w4 = pR & gL
      .xor 2 4,     -- w5 = gR ^ (pR & gL)
      .and 3 1      -- w6 = pR & pL
    ]
    outs := [5, 6] }

def prefixAdderXorBlackSpec : PrefixSpec :=
  { prefixAdderGlitchedXorSpec with opNet := opXorBlackNet, hOpIn := rfl, hOpOut := rfl }

def xor2Net : GateNet := { inW := 2, gates := [.xor 0 1], outs := [2] }

def grayDecodePrefixSpec : PrefixSpec :=
  { inW := 1, tokW := 1, stW := 1, outW := 1
    preNet := id1Net, opNet := xor2Net, actNet := xor2Net, postNet := xor2Net
    hPreIn := rfl, hPreOut := rfl, hOpIn := rfl, hOpOut := rfl
    hActIn := rfl, hActOut := rfl, hPostIn := rfl, hPostOut := rfl }

-- ============================================================================
-- SECTION 3: ENGINE 3 — RECURSIVE SHIFTER & ROTATOR BISIMULATION COMPILER
-- ============================================================================

/-- A concrete gate-level 2:1 multiplexer cell (`inW = 3`: `[sel, d0, d1]`, `outs = [out]`). -/
structure MuxCell where
  net  : GateNet
  hIn  : net.inW = 3
  hOut : net.outs.length = 1

def MuxCell.eval (M : MuxCell) (sel d0 d1 : Bool) : Bool :=
  let inp : BitVec 3 := listToBv 3 [sel, d0, d1]
  let out : BitVec 1 := M.hOut ▸ evalGateNet M.net (M.hIn ▸ inp)
  out.getLsbD 0

/-- Cyclic rotation by `s` positions on arbitrary width `w : Nat`. -/
def rotBy {w : Nat} (s : Nat) (xs : Fin w → Bool) : Fin w → Bool :=
  fun i => xs ⟨(i.val + s) % w, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- Reference unary 1-bit cyclic rotator iterated `s` times on arbitrary width `w`. -/
def iterRot {w : Nat} : Nat → (Fin w → Bool) → (Fin w → Bool)
  | 0, xs     => xs
  | s + 1, xs => rotBy 1 (iterRot s xs)

/-- Staged logarithmic mux barrel rotator on arbitrary width `w : Nat`:
    stage `j` rotates by `2^j` iff control bit `j` is `true`, using concrete `MuxCell M`. -/
def barrelRotAux (M : MuxCell) {w : Nat} (step : Nat) : List Bool → (Fin w → Bool) → (Fin w → Bool)
  | [], xs      => xs
  | c :: cs, xs =>
    let ys : Fin w → Bool := fun i =>
      M.eval c (xs i) (xs ⟨(i.val + step) % w, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩)
    barrelRotAux M (2 * step) cs ys

def barrelRot (M : MuxCell) {w : Nat} (ctrls : List Bool) (xs : Fin w → Bool) : Fin w → Bool :=
  barrelRotAux M 1 ctrls xs

/-- Divide-and-conquer recursive `2^k`-wire unshuffle-rotate-interleave tree rotator:
    1. Conditional 1-bit local mux layer controlled by `ctrls[0]`,
    2. Deinterleave into `even` and `odd` halves (`2^(k-1)` wires each),
    3. Recursively rotate BOTH halves identically by `ctrls[1..]`,
    4. Interleave back! -/
def recTreeRot (M : MuxCell) : ∀ (k : Nat), (Fin k → Bool) → (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, _, xs => xs
  | k + 1, ctrls, xs =>
    let c0 := ctrls ⟨0, Nat.zero_lt_succ k⟩
    let ys : Fin (2 ^ (k + 1)) → Bool := fun i =>
      M.eval c0 (xs i) (xs ⟨(i.val + 1) % 2 ^ (k + 1), Nat.mod_lt _ (Nat.two_pow_pos (k + 1))⟩)
    let ev : Fin (2 ^ k) → Bool := fun j => ys ⟨2 * j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
    let od : Fin (2 ^ k) → Bool := fun j => ys ⟨2 * j.val + 1, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
    let ev' := recTreeRot M k (fun j => ctrls j.succ) ev
    let od' := recTreeRot M k (fun j => ctrls j.succ) od
    fun i =>
      if i.val % 2 = 0 then
        ev' ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
      else
        od' ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩

def nandOnlyMuxCell : MuxCell :=
  { net := { inW := 3, gates := [.nand 0 0, .nand 3 1, .nand 0 2, .nand 4 5], outs := [6] }
    hIn := rfl, hOut := rfl }

def xorAndMuxCell : MuxCell :=
  { net := { inW := 3, gates := [.xor 1 2, .and 0 3, .xor 1 4], outs := [5] }
    hIn := rfl, hOut := rfl }

-- ============================================================================
-- SECTION 4: ENGINE 4 — BUTTERFLY, PEASE/OMEGA & BITONIC / ODD-EVEN COMPILER
-- ============================================================================

/-- A concrete 2-wire controlled gate cell (`inW = 3`: `[c, a, b]`, `outs = [u, v]`). -/
structure Cell2 where
  net  : GateNet
  hIn  : net.inW = 3
  hOut : net.outs.length = 2

def Cell2.eval (C : Cell2) (c a b : Bool) : Bool × Bool :=
  let inp : BitVec 3 := listToBv 3 [c, a, b]
  let out : BitVec 2 := C.hOut ▸ evalGateNet C.net (C.hIn ▸ inp)
  (out.getLsbD 0, out.getLsbD 1)

/-- Stride-`2^k` butterfly layer on `2^(k+1)` wires (pairs `i` with `i + 2^k`). -/
def strideLayer (f : Bool → Bool → Bool × Bool) {k : Nat}
    (xs : Fin (2 ^ (k + 1)) → Bool) : Fin (2 ^ (k + 1)) → Bool :=
  fun i =>
    if h : i.val < 2 ^ k then
      (f (xs ⟨i.val, i.isLt⟩) (xs ⟨i.val + 2 ^ k, by simp [Nat.pow_succ]; omega⟩)).1
    else
      (f (xs ⟨i.val - 2 ^ k, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩)
         (xs ⟨i.val, i.isLt⟩)).2

/-- Adjacent-pair layer on `2^(k+1)` wires (pairs `2j` with `2j+1`). -/
def applyPairs (f : Bool → Bool → Bool × Bool) {k : Nat}
    (xs : Fin (2 ^ (k + 1)) → Bool) : Fin (2 ^ (k + 1)) → Bool :=
  fun i =>
    let base := (i.val / 2) * 2
    let a := xs ⟨base, by have := i.isLt; omega⟩
    let b := xs ⟨base + 1, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
    if i.val % 2 = 0 then (f a b).1 else (f a b).2

/-- Bit-address right-rotation by 1 on `k` bits: `(b_{k-1}..b_1 b_0) ↦ (b_0 b_{k-1}..b_1)`. -/
def rotRightIdx : ∀ (k : Nat), Fin (2 ^ k) → Fin (2 ^ k)
  | 0, i => i
  | k + 1, i =>
    ⟨i.val / 2 + (i.val % 2) * 2 ^ k, by
      have hlt := i.isLt; simp [Nat.pow_succ] at hlt ⊢
      have hm : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases hm with h | h <;> simp [h] <;> omega⟩

/-- Perfect riffle shuffle on `2^k` wires: `shuffle xs i = xs (rotRightIdx k i)`. -/
def shuffle {k : Nat} (xs : Fin (2 ^ k) → Bool) : Fin (2 ^ k) → Bool :=
  fun i => xs (rotRightIdx k i)

/-- **Topology 1**: Recursive **Forward Butterfly Network** (`stride 2^(k-1) → ... → 1`). -/
def fwdButterfly (C : Cell2) : ∀ (k : Nat), (Fin k → Bool) → (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, _, xs => xs
  | k + 1, ctrls, xs =>
    let ys := strideLayer (C.eval (ctrls ⟨0, Nat.zero_lt_succ k⟩)) xs
    let L := fwdButterfly C k (fun j => ctrls j.succ)
               (fun i : Fin (2 ^ k) => ys ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let R := fwdButterfly C k (fun j => ctrls j.succ)
               (fun i : Fin (2 ^ k) => ys ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    fun i =>
      if h : i.val < 2 ^ k then L ⟨i.val, h⟩
      else R ⟨i.val - 2 ^ k, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩

/-- **Topology 2**: Recursive **Backward Butterfly Network** (`stride 1 → ... → 2^(k-1)`). -/
def bwdButterfly (C : Cell2) : ∀ (k : Nat), (Fin k → Bool) → (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, _, xs => xs
  | k + 1, ctrls, xs =>
    let L := bwdButterfly C k (fun j => ctrls j.succ)
               (fun i : Fin (2 ^ k) => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let R := bwdButterfly C k (fun j => ctrls j.succ)
               (fun i : Fin (2 ^ k) => xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let merged : Fin (2 ^ (k + 1)) → Bool := fun i =>
      if h : i.val < 2 ^ k then L ⟨i.val, h⟩
      else R ⟨i.val - 2 ^ k, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
    strideLayer (C.eval (ctrls ⟨0, Nat.zero_lt_succ k⟩)) merged

/-- **Topology 3**: Constant-Geometry **Pease / Omega Shuffle-Exchange Network**!
    Repeats the exact same `applyPairs ∘ shuffle` stage `k` times with `ctrls[0..k-1]`. -/
def omegaStage (C : Cell2) {k : Nat} (c : Bool) (xs : Fin (2 ^ k) → Bool) : Fin (2 ^ k) → Bool :=
  match k with
  | 0 => xs
  | _ + 1 => applyPairs (C.eval c) (shuffle xs)

def omegaRun (C : Cell2) {k : Nat} : List Bool → (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | [], xs      => xs
  | c :: cs, xs => omegaRun C cs (omegaStage C c xs)

def omegaNet (C : Cell2) (k : Nat) (ctrls : Fin k → Bool) (xs : Fin (2 ^ k) → Bool) :
    Fin (2 ^ k) → Bool :=
  omegaRun C (finToList ctrls) xs

-- Core `strideLayer` helper lemmas (clean, direct induction on `k`!)

def parHalf {k : Nat} (f : (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool))
    (xs : Fin (2 ^ (k + 1)) → Bool) : Fin (2 ^ (k + 1)) → Bool :=
  let L := f (fun i : Fin (2 ^ k) => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
  let R := f (fun i : Fin (2 ^ k) => xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
  fun i =>
    if h : i.val < 2 ^ k then L ⟨i.val, h⟩
    else R ⟨i.val - 2 ^ k, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩

/-- Count of `false` (zeros) in a Boolean vector `Fin n → Bool`. -/
def countFalse {n : Nat} (xs : Fin n → Bool) : Nat :=
  ((List.finRange n).filter (fun i => !(xs i))).length

/-- Reference **Threshold / Popcount Sorter** on `Fin n → Bool`:
    outputs `countFalse xs` zeros followed by `n - countFalse xs` ones. -/
def thresholdSort {n : Nat} (xs : Fin n → Bool) : Fin n → Bool :=
  fun i => decide (countFalse xs ≤ i.val)

/-- **Bitonic Merge Network** (concrete gate-level comparator `C : Cell2`, width `2^k`). -/
def bitonicMerge (C : Cell2) : ∀ (k : Nat), (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, xs => xs
  | k + 1, xs =>
    let ys := strideLayer (C.eval false) xs
    parHalf (bitonicMerge C k) ys

/-- **Batcher Bitonic Sort Network** (concrete gate-level comparator `C : Cell2`, width `2^k`). -/
def bitonicSort (C : Cell2) : ∀ (k : Nat), (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, xs => xs
  | k + 1, xs =>
    let L := bitonicSort C k (fun i : Fin (2 ^ k) => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let R := bitonicSort C k (fun i : Fin (2 ^ k) => xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    -- Reverse `R` so `L ++ rev R` is bitonic (`0* 1* 0*`)!
    let merged : Fin (2 ^ (k + 1)) → Bool := fun i =>
      if h : i.val < 2 ^ k then L ⟨i.val, h⟩
      else R ⟨2 ^ k - 1 - (i.val - 2 ^ k), by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
    bitonicMerge C (k + 1) merged

/-- Adjacent odd-even compare-exchange layer `(1,2), (3,4), ..., (2^k - 3, 2^k - 2)` for Batcher's
    Odd-Even Merge Network! -/
def oddEvenSwapLayer (f : Bool → Bool → Bool × Bool) {n : Nat} (xs : Fin n → Bool) : Fin n → Bool :=
  fun i =>
    if h0 : i.val = 0 then xs i
    else if hLast : i.val + 1 = n ∧ i.val % 2 = 1 then xs i
    else if hOdd : i.val % 2 = 1 then
      (f (xs i) (xs ⟨i.val + 1, by have := i.isLt; omega⟩)).1
    else
      (f (xs ⟨i.val - 1, by have := i.isLt; omega⟩) (xs i)).2

/-- **Batcher's Odd-Even Merge Network** (concrete gate-level comparator `C : Cell2`, width `2^k`). -/
def oddEvenMerge (C : Cell2) : ∀ (k : Nat), (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, xs => xs
  | 1, xs =>
    let (a, b) := C.eval false (xs ⟨0, by decide⟩) (xs ⟨1, by decide⟩)
    fun i => if i.val = 0 then a else b
  | k + 2, xs =>
    let ev : Fin (2 ^ (k + 1)) → Bool := fun j => xs ⟨2 * j.val, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
    let od : Fin (2 ^ (k + 1)) → Bool := fun j => xs ⟨2 * j.val + 1, by have := j.isLt; simp [Nat.pow_succ]; omega⟩
    let ev' := oddEvenMerge C (k + 1) ev
    let od' := oddEvenMerge C (k + 1) od
    let inter : Fin (2 ^ (k + 2)) → Bool := fun i =>
      if i.val % 2 = 0 then
        ev' ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
      else
        od' ⟨i.val / 2, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
    oddEvenSwapLayer (C.eval false) inter

/-- **Batcher's Odd-Even Mergesort Network** (concrete gate-level comparator `C : Cell2`, width `2^k`). -/
def oddEvenSort (C : Cell2) : ∀ (k : Nat), (Fin (2 ^ k) → Bool) → (Fin (2 ^ k) → Bool)
  | 0, xs => xs
  | k + 1, xs =>
    let L := oddEvenSort C k (fun i : Fin (2 ^ k) => xs ⟨i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let R := oddEvenSort C k (fun i : Fin (2 ^ k) => xs ⟨2 ^ k + i.val, by have := i.isLt; simp [Nat.pow_succ]; omega⟩)
    let merged : Fin (2 ^ (k + 1)) → Bool := fun i =>
      if h : i.val < 2 ^ k then L ⟨i.val, h⟩
      else R ⟨i.val - 2 ^ k, by have := i.isLt; simp [Nat.pow_succ] at *; omega⟩
    oddEvenMerge C (k + 1) merged

-- ============================================================================
-- CONCRETE GATE-LEVEL CELLS & CERTIFIED INFINITE THEOREMS FOR ENGINE 4
-- ============================================================================

/-- Fast Reed–Muller / ANF / Zeta-Transform Butterfly cell: `(a, a ^ b)` (ignoring `c`). -/
def anfCell : Cell2 :=
  { net := { inW := 3, gates := [.xor 1 2], outs := [1, 3] }, hIn := rfl, hOut := rfl }

/-- Non-involutive Order-3 GF(4) Linear Butterfly cell `(b, a ^ b)` and its inverse `(a ^ b, a)`! -/
def gf4FwdCell : Cell2 :=
  { net := { inW := 3, gates := [.xor 1 2], outs := [2, 3] }, hIn := rfl, hOut := rfl }

def gf4InvCell : Cell2 :=
  { net := { inW := 3, gates := [.xor 1 2], outs := [3, 1] }, hIn := rfl, hOut := rfl }

/-- Concrete Comparator Cells: AND/OR comparator, NAND-only comparator, and MUX-based comparator! -/
def andOrCmpCell : Cell2 :=
  { net := { inW := 3, gates := [.and 1 2, .or 1 2], outs := [3, 4] }, hIn := rfl, hOut := rfl }

def nandOnlyCmpCell : Cell2 :=
  { net := { inW := 3
             gates := [.nand 1 2, .nand 3 3, .nand 1 1, .nand 2 2, .nand 5 6]
             outs := [4, 7] }
    hIn := rfl, hOut := rfl }

end SiliconBisim
