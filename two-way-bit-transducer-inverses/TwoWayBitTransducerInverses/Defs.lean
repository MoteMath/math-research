/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`two-way-bit-transducer-inverses`)

Two-Way Bit-Transducer Tile-Witness Inversion and Coxeter-6 Phase Transition: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace BidirectionalTransducer


/-! ## Section 1: Core Mealy Transducers & BitVec <-> List Bool Bridge -/

inductive Dir where
  | fwd
  | bwd
  deriving DecidableEq, Repr

structure Mealy (Q : Type) where
  delta : Q → Bool → Q
  out   : Q → Bool → Bool
  q0    : Q

structure Sweep (Q : Type) where
  dir : Dir
  m   : Mealy Q

/-- Forward (LSB -> MSB) Mealy execution on a bit-list (head = LSB). -/
def runFwd {Q : Type} (m : Mealy Q) : Q → List Bool → List Bool × Q
  | q, [] => ([], q)
  | q, b :: bs =>
      let o := m.out q b
      let q' := m.delta q b
      let (os, qEnd) := runFwd m q' bs
      (o :: os, qEnd)

/-- Backward (MSB -> LSB) Mealy execution on a bit-list (last = MSB, head = LSB). -/
def runBwd {Q : Type} (m : Mealy Q) : Q → List Bool → List Bool × Q
  | q, [] => ([], q)
  | q, b :: bs =>
      let (os, qMid) := runBwd m q bs
      let o := m.out qMid b
      let qL := m.delta qMid b
      (o :: os, qL)

theorem runFwd_length {Q : Type} (m : Mealy Q) (q : Q) (xs : List Bool) :
    (runFwd m q xs).1.length = xs.length := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
      simp only [runFwd, List.length_cons]
      exact congrArg Nat.succ (ih (m.delta q b))

theorem runBwd_length {Q : Type} (m : Mealy Q) (q : Q) (xs : List Bool) :
    (runBwd m q xs).1.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp only [runBwd, List.length_cons]
      exact congrArg Nat.succ ih

/-- Run a single sweep starting from its initial state. -/
def runSweep {Q : Type} (sw : Sweep Q) (xs : List Bool) : List Bool :=
  match sw.dir with
  | .fwd => (runFwd sw.m sw.m.q0 xs).1
  | .bwd => (runBwd sw.m sw.m.q0 xs).1

/-- Run a sequence of sweeps (first sweep in list runs first). -/
def runSweeps {Q : Type} : List (Sweep Q) → List Bool → List Bool
  | [], xs => xs
  | sw :: sws, xs => runSweeps sws (runSweep sw xs)

theorem runSweep_length {Q : Type} (sw : Sweep Q) (xs : List Bool) :
    (runSweep sw xs).length = xs.length := by
  cases sw with
  | mk dir m =>
    cases dir with
    | fwd => exact runFwd_length m m.q0 xs
    | bwd => exact runBwd_length m m.q0 xs

theorem runSweeps_length {Q : Type} (sws : List (Sweep Q)) (xs : List Bool) :
    (runSweeps sws xs).length = xs.length := by
  induction sws generalizing xs with
  | nil => rfl
  | cons sw sws ih =>
      simp only [runSweeps]
      rw [ih, runSweep_length]

/-- Coupled two-way transducer: forward pass `F` feeds its final state into `B` via `beta`. -/
def runCoupledTwoWay {QF QB : Type} (F : Mealy QF) (beta : QF → QB) (B : Mealy QB)
    (xs : List Bool) : List Bool :=
  let (ys, sEnd) := runFwd F F.q0 xs
  (runBwd B (beta sEnd) ys).1

/-- Exact LSB-first conversion from `BitVec w` to `List Bool` of length `w`. -/
def toBits {w : Nat} (x : BitVec w) : List Bool :=
  List.ofFn (fun (i : Fin w) => x.getLsbD i.val)

/-- Exact LSB-first reconstruction from `List Bool` to `BitVec xs.length`. -/
def ofBits : (xs : List Bool) → BitVec xs.length
  | [] => BitVec.ofNat 0 0
  | b :: bs => BitVec.ofNat (bs.length + 1) (2 * (ofBits bs).toNat + b.toNat)

theorem toBits_length {w : Nat} (x : BitVec w) : (toBits x).length = w := by
  simp [toBits]

/-- Lift any length-preserving `List Bool → List Bool` operator to `BitVec w → BitVec w`. -/
def liftBV (f : List Bool → List Bool) (hf : ∀ xs, (f xs).length = xs.length)
    {w : Nat} (x : BitVec w) : BitVec w :=
  (ofBits (f (toBits x))).cast (by rw [hf, toBits_length])

/-- Forward, backward, and two-way transducer actions directly on `BitVec w`. -/
def fwdBV {Q : Type} (m : Mealy Q) {w : Nat} (x : BitVec w) : BitVec w :=
  liftBV (fun xs => (runFwd m m.q0 xs).1) (runFwd_length m m.q0) x

def bwdBV {Q : Type} (m : Mealy Q) {w : Nat} (x : BitVec w) : BitVec w :=
  liftBV (fun xs => (runBwd m m.q0 xs).1) (runBwd_length m m.q0) x

def twoWayBV {QF QB : Type} (F : Mealy QF) (B : Mealy QB) {w : Nat} (x : BitVec w) : BitVec w :=
  bwdBV B (fwdBV F x)

def sweepsBV {Q : Type} (sws : List (Sweep Q)) {w : Nat} (x : BitVec w) : BitVec w :=
  liftBV (runSweeps sws) (runSweeps_length sws) x

/-! ## Section 2: The General Bidirectional Tile-Witness Engine -/

/-- Local single-bit column tile relation across an arbitrary sequence of alternating sweeps. -/
def TileStep {Q : Type} : List (Sweep Q) → List Q → List Q → Bool → Bool → Prop
  | [], [], [], bit, out => bit = out
  | ⟨.fwd, m⟩ :: sws, qL :: cL, qR :: cR, bit, out =>
      m.delta qL bit = qR ∧ TileStep sws cL cR (m.out qL bit) out
  | ⟨.bwd, m⟩ :: sws, qL :: cL, qR :: cR, bit, out =>
      m.delta qR bit = qL ∧ TileStep sws cL cR (m.out qR bit) out
  | _, _, _, _, _ => False

/-- LSB boundary condition: every forward sweep starts at its `q0`. -/
def LeftBoundary {Q : Type} : List (Sweep Q) → List Q → Prop
  | [], [] => True
  | ⟨.fwd, m⟩ :: sws, q :: qs => q = m.q0 ∧ LeftBoundary sws qs
  | ⟨.bwd, _⟩ :: sws, _ :: qs => LeftBoundary sws qs
  | _, _ => False

/-- MSB boundary condition: every backward sweep starts at its `q0`. -/
def RightBoundary {Q : Type} : List (Sweep Q) → List Q → Prop
  | [], [] => True
  | ⟨.fwd, _⟩ :: sws, _ :: qs => RightBoundary sws qs
  | ⟨.bwd, m⟩ :: sws, q :: qs => q = m.q0 ∧ RightBoundary sws qs
  | _, _ => False

/-- Multi-bit chain of valid bidirectional tiles from left crossing `cL` to right crossing `cR`. -/
inductive TileChain {Q : Type} (sws : List (Sweep Q)) :
    List Q → List Q → List Bool → List Bool → Prop where
  | nil (c : List Q) : c.length = sws.length → TileChain sws c c [] []
  | cons {cL cM cR : List Q} {b o : Bool} {xs ys : List Bool} :
      TileStep sws cL cM b o →
      TileChain sws cM cR xs ys →
      TileChain sws cL cR (b :: xs) (o :: ys)

/-- Standard DFA run over bit-lists (LSB-first). -/
def runDFA {M : Type} (next : M → Bool → M) : M → List Bool → M
  | m, [] => m
  | m, b :: bs => runDFA next (next m b) bs

/-- Bitwise pointwise relation between two equal-length bit-lists. -/
inductive BitRel (P : Bool → Bool → Prop) : List Bool → List Bool → Prop where
  | nil : BitRel P [] []
  | cons {a b : Bool} {xs ys : List Bool} : P a b → BitRel P xs ys → BitRel P (a :: xs) (b :: ys)

def tileStepBool {Q : Type} [DecidableEq Q] :
    List (Sweep Q) → List Q → List Q → Bool → Bool → Bool
  | [], [], [], bit, out => decide (bit = out)
  | ⟨.fwd, m⟩ :: sws, qL :: cL, qR :: cR, bit, out =>
      decide (m.delta qL bit = qR) && tileStepBool sws cL cR (m.out qL bit) out
  | ⟨.bwd, m⟩ :: sws, qL :: cL, qR :: cR, bit, out =>
      decide (m.delta qR bit = qL) && tileStepBool sws cL cR (m.out qR bit) out
  | _, _, _, _, _ => false

def leftBoundaryBool {Q : Type} [DecidableEq Q] : List (Sweep Q) → List Q → Bool
  | [], [] => true
  | ⟨.fwd, m⟩ :: sws, q :: qs => decide (q = m.q0) && leftBoundaryBool sws qs
  | ⟨.bwd, _⟩ :: sws, _ :: qs => leftBoundaryBool sws qs
  | _, _ => false

def rightBoundaryBool {Q : Type} [DecidableEq Q] : List (Sweep Q) → List Q → Bool
  | [], [] => true
  | ⟨.fwd, _⟩ :: sws, _ :: qs => rightBoundaryBool sws qs
  | ⟨.bwd, m⟩ :: sws, q :: qs => decide (q = m.q0) && rightBoundaryBool sws qs
  | _, _ => false

/-- A finite crossing-witness certificate for any multi-sweep transducer system over `Q`. -/
structure FiniteTileCert (Q : Type) where
  sws      : List (Sweep Q)
  nMacro   : Nat
  m0       : Fin nMacro
  next     : Fin nMacro → Bool → Fin nMacro
  witness  : Fin nMacro → List (List Q)

def checkCert {Q : Type} [DecidableEq Q] (cert : FiniteTileCert Q) : Bool :=
  let allMacros := List.finRange cert.nMacro
  let okLen := allMacros.all fun m =>
    (cert.witness m).all fun c => decide (c.length = cert.sws.length)
  let okInit := (cert.witness cert.m0).all fun c =>
    leftBoundaryBool cert.sws c
  let okStep := allMacros.all fun m =>
    [false, true].all fun b =>
      (cert.witness (cert.next m b)).all fun cR =>
        (cert.witness m).any fun cL => tileStepBool cert.sws cL cR b b
  let okFinal := allMacros.all fun m =>
    (cert.witness m).any fun cR => rightBoundaryBool cert.sws cR
  okLen && okInit && okStep && okFinal

/--
The 2-state nonlinear skip-flip Mealy transducer `M_2`:
- `q = false` (flip mode): outputs `!b`; enters skip mode `true` iff `b = true`.
- `q = true` (skip mode): passes `b` unchanged and resets to `false`.
-/
def skipFlip2 (q0 : Bool := false) : Mealy Bool :=
  { delta := fun q b => (!q) && b
    out   := fun q b => b != (!q)
    q0    := q0 }

/-- Forward (LSB -> MSB) action of `skipFlip2` on `List Bool`. -/
def skipFlip2Fwd (xs : List Bool) : List Bool :=
  (runFwd (skipFlip2 false) false xs).1

/-- Backward (MSB -> LSB) action of `skipFlip2` on `List Bool`. -/
def skipFlip2Bwd (q0 : Bool := false) (xs : List Bool) : List Bool :=
  (runBwd (skipFlip2 q0) q0 xs).1

/-- Two-way composition `T_2 = B_2 ∘ F_2` on `BitVec w`. -/
def skipFlip2TwoWay {w : Nat} (x : BitVec w) : BitVec w :=
  twoWayBV (skipFlip2 false) (skipFlip2 false) x

/-- Shifted two-way composition `T_2' = B_2^{(q0=true)} ∘ F_2` on `BitVec w`. -/
def skipFlip2Shifted {w : Nat} (x : BitVec w) : BitVec w :=
  twoWayBV (skipFlip2 false) (skipFlip2 true) x

/-- 6-sweep certificate for `(B_2 ∘ F_2)^3 = id` (3 macro-states, 6 crossing witnesses). -/
def certSkipFlip2Period3 : FiniteTileCert Bool :=
  let swF : Sweep Bool := ⟨.fwd, skipFlip2 false⟩
  let swB : Sweep Bool := ⟨.bwd, skipFlip2 false⟩
  { sws    := [swF, swB, swF, swB, swF, swB]
    nMacro := 3
    m0     := ⟨0, by decide⟩
    next   := fun m b =>
      match m.val, b with
      | 0, false => ⟨1, by decide⟩
      | 0, true  => ⟨2, by decide⟩
      | 1, false => ⟨1, by decide⟩
      | 1, true  => ⟨2, by decide⟩
      | _, _     => ⟨0, by decide⟩
    witness := fun m =>
      match m.val with
      | 0 => [ [false, false, false, false, false, false],
               [false, true,  false, true,  false, true] ]
      | 1 => [ [false, false, false, false, false, false],
               [false, true,  true,  false, true,  true] ]
      | _ => [ [true,  false, true,  false, true,  false],
               [true,  false, true,  true,  false, true],
               [true,  true,  false, true,  true,  false] ] }

/-- Pure-core `n`-fold function iteration. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- 12-sweep certificate for `(B_2^{(q0=true)} ∘ F_2)^6 = id` (3 macro-states, 8 witnesses out of 4,096). -/
def certSkipFlip2ShiftedPeriod6 : FiniteTileCert Bool :=
  let swF : Sweep Bool := ⟨.fwd, skipFlip2 false⟩
  let swB : Sweep Bool := ⟨.bwd, skipFlip2 true⟩
  { sws    := [swF, swB, swF, swB, swF, swB, swF, swB, swF, swB, swF, swB]
    nMacro := 3
    m0     := ⟨0, by decide⟩
    next   := fun m b =>
      match m.val, b with
      | 0, false => ⟨1, by decide⟩
      | 0, true  => ⟨2, by decide⟩
      | 1, false => ⟨1, by decide⟩
      | 1, true  => ⟨2, by decide⟩
      | _, _     => ⟨0, by decide⟩
    witness := fun m =>
      match m.val with
      | 0 => [ [false, false, false, false, false, false, false, false, false, false, false, false],
               [false, true,  false, true,  false, true,  false, true,  false, true,  false, true] ]
      | 1 => [ [false, false, false, false, false, false, false, false, false, false, false, false],
               [false, true,  true,  false, true,  true,  false, true,  true,  false, true,  true],
               [false, true,  true,  true,  false, true,  true,  true,  false, true,  true,  true] ]
      | _ => [ [true,  false, true,  false, true,  false, true,  false, true,  false, true,  false],
               [true,  false, true,  true,  false, true,  true,  false, true,  true,  false, true],
               [true,  true,  false, true,  true,  false, true,  true,  false, true,  true,  false],
               [true,  true,  false, true,  true,  true,  false, true,  true,  true,  false, true] ] }

/-- Helper: final state of `skipFlip2` running forward on `xs`. -/
def sf2End (xs : List Bool) : Bool := (runFwd (skipFlip2 false) false xs).2

/-- Cumulative MSB-flip parity over `n` iterations of `skipFlip2Fwd` starting from `xs`. -/
def sf2FlipParity : Nat → List Bool → Bool
  | 0, _ => false
  | n + 1, xs => xor (!(sf2End xs)) (sf2FlipParity n (skipFlip2Fwd xs))

/-- Forward (LSB -> MSB) run-triggered involution `S_m`: flips the bit immediately above
every disjoint run of `m` consecutive `true`s. -/
def runTriggerS (m : Nat) : Mealy Nat :=
  { delta := fun q b => if q < m then (if b then q + 1 else 0) else 0
    out   := fun q b => if q < m then b else !b
    q0    := 0 }

/-- Backward (MSB -> LSB) run-triggered involution `R_m`: flips the bit immediately below
every disjoint run of `m` consecutive `false`s. -/
def runTriggerR (m : Nat) : Mealy Nat :=
  { delta := fun q b => if q < m then (if b then 0 else q + 1) else 0
    out   := fun q b => if q < m then b else !b
    q0    := 0 }

/-- Original run-triggered skip-flip transducer `F_m` (complements all bits except right after `m` ones). -/
def runSkipFlip (m : Nat) : Mealy Nat :=
  { delta := fun q b => if q < m then (if b then q + 1 else 0) else 0
    out   := fun q b => if q < m then !b else b
    q0    := 0 }

/-- Two-way composition `T_m = R_m ∘ S_m` on `BitVec w`. -/
def runTriggerTwoWay (m : Nat) {w : Nat} (x : BitVec w) : BitVec w :=
  twoWayBV (runTriggerS m) (runTriggerR m) x

def runTriggerSweeps6 (m : Nat) : List (Sweep Nat) :=
  let swS : Sweep Nat := ⟨.fwd, runTriggerS m⟩
  let swR : Sweep Nat := ⟨.bwd, runTriggerR m⟩
  [swS, swR, swS, swR, swS, swR, swS, swR, swS, swR, swS, swR]

/-- Interleaved 12-state crossing tuple `[s0, t0, s1, t1, ..., s5, t5]`. -/
def mkCross (s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 t5 : Nat) : List Nat :=
  [s0, t0, s1, t1, s2, t2, s3, t3, s4, t4, s5, t5]

def cSync (a b : Nat) : List Nat := mkCross a a a a a a b b b b b b

def cAltL (a b t : Nat) : List Nat := mkCross a b a b a b t t t t t t

def cAltR (s a b : Nat) : List Nat := mkCross s s s s s s a b a b a b

def cCyc0 (m : Nat) : List Nat := mkCross 0 m m 0 m m m 0 m m 0 m

def cCyc1 (m : Nat) : List Nat := mkCross m 0 m m 0 m m m 0 m m 0

def cCyc2 (m : Nat) : List Nat := mkCross m m 0 m m 0 0 m m 0 m m

/-- Symbolic `(2m + 1)`-state macro-automaton for `T_m^6 = id` (`∀ m ≥ 2`). -/
inductive SymMacro (m : Nat) where
  | start
  | afterZero (r : Nat) (hr : r < m)
  | inOnes (r : Nat) (h1 : 1 ≤ r) (h2 : r ≤ m)

def symNext (m : Nat) (hm : 2 ≤ m) : SymMacro m → Bool → SymMacro m
  | .start, false => .afterZero 0 (by omega)
  | .start, true => .inOnes 1 (by omega) (by omega)
  | .afterZero _ _, false => .afterZero 0 (by omega)
  | .afterZero _ _, true => .inOnes 1 (by omega) (by omega)
  | .inOnes r _ _, b =>
      if hr : r < m then
        if b then .inOnes (r + 1) (by omega) (by omega)
        else .afterZero r hr
      else .start

/-- Symbolic crossing-witness subsets `W(mac)` of size `m^2 + 4m + 1` in total. -/
def SymW (m : Nat) : SymMacro m → List Nat → Prop
  | .start, c => ∃ b, b ≤ m ∧ c = cSync 0 b
  | .afterZero r _, c =>
      (∃ b, b < m ∧ c = cSync 0 b) ∨
      (if r + 1 < m then c = cAltL 0 (r + 1) m else c = cCyc0 m)
  | .inOnes r _ _, c =>
      if r < m then
        (∃ b, b < m ∧ c = cSync r b) ∨ c = cAltL r 0 m
      else
        c = cSync m 0 ∨ c = cCyc1 m ∨ c = cCyc2 m ∨
        (∃ a, 1 ≤ a ∧ a < m ∧ (c = cAltR m 0 a ∨ c = cAltR m a 0))

/-- Counting helper: number of `true`s and `false`s in a bit-list. -/
def countBit (target : Bool) : List Bool → Nat
  | [] => 0
  | b :: bs => (if b == target then 1 else 0) + countBit target bs

/-- No two consecutive `true`s in a bit-list (given whether the immediately preceding bit was `true`). -/
def noAdjTrue : Bool → List Bool → Prop
  | _, [] => True
  | prev, b :: bs => (prev = true → b = false) ∧ noAdjTrue b bs

/-- Explicit alternating padding of length `d` whose top (last) bit is `false` whenever `d ≥ 1`. -/
def altPadRev : Nat → List Bool
  | 0 => []
  | n + 1 => (n % 2 == 1) :: altPadRev n

/-- Forward 2-to-1 parity-delay transducer `F_pd`: outputs previous parity state,
losing the final bit into `sEnd` (NOT injective on `List Bool` alone!). -/
def parityDelayF : Mealy Bool :=
  { delta := fun q b => xor q b
    out   := fun q _ => q
    q0    := false }

/-- Backward Gray-difference transducer `B_gd`: recovers `x` when started at `t_w = sEnd`. -/
def grayDiffB : Mealy Bool :=
  { delta := fun _ b => b
    out   := fun q b => xor q b
    q0    := false }

/-- Mutation Test 1: False period-2 claim for `skipFlip2` with the same 3-state DFA is REJECTED. -/
def badCertPeriod2 : FiniteTileCert Bool :=
  let swF : Sweep Bool := ⟨.fwd, skipFlip2 false⟩
  let swB : Sweep Bool := ⟨.bwd, skipFlip2 false⟩
  { sws    := [swF, swB, swF, swB]
    nMacro := 3
    m0     := ⟨0, by decide⟩
    next   := certSkipFlip2Period3.next
    witness := fun m =>
      match m.val with
      | 0 => [[false, false, false, false]]
      | 1 => [[false, false, false, false]]
      | _ => [[true, false, true, false]] }

/-- Mutation Test 2: Dropping a single required witness state from `certSkipFlip2Period3` is REJECTED. -/
def badCertDroppedWitness : FiniteTileCert Bool :=
  { certSkipFlip2Period3 with
    witness := fun m =>
      match m.val with
      | 2 => [ [true, false, true, false, true, false],
               [true, false, true, true,  false, true] ]  -- dropped `[true, true, false, true, true, false]`
      | _ => certSkipFlip2Period3.witness m }

/-- Sharpness 2: Perturbing ONE transition bit of `skipFlip2` (`delta true true := true`) breaks period 3 AND period 6 at `w = 3`. -/
def skipFlip2Perturbed : Mealy Bool :=
  { delta := fun _ b => b
    out   := fun q b => b != (!q)
    q0    := false }

/-- Sharpness 4: Variant A 3-state skip-flip (`skip 2 bits after a 1`) breaks period 3 and 6 at `w = 3`. -/
def skipFlipVariantA3 : Mealy Nat :=
  { delta := fun q b =>
      match q with
      | 0 => if b then 1 else 0
      | 1 => 2
      | _ => 0
    out   := fun q b => if q == 0 then !b else b
    q0    := 0 }

end BidirectionalTransducer
