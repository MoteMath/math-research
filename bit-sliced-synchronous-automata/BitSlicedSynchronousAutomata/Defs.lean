/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Bit-Sliced Synchronous Automaton Reflection Engine (`bit-sliced-synchronous-automata`)

Pure-`Init` (zero Mathlib) definitions of `SyncAutomaton`, `AutomatonCert`, `checkCert`, `BVProp`, `compileToSync`, `signedQuarterSum`, `unsignedQuarterSum`, `signedAddOverflow`, `unsignedAvg`, `signedAvg`, `grayCode`, and `bvParity`.
-/

namespace BitSync

/-- Bounded universal check over `0, 1, ..., n - 1`, optimized for fast kernel reduction. -/
def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | m + 1 => allBelow m p && p m

/-- A deterministic synchronous finite-state automaton reading `k`-bit slices (encoded in `Fin (2^k)`). -/
structure SyncAutomaton (k : Nat) (S : Type) where
  init   : S
  step   : S → Fin (2 ^ k) → S
  accept : S → Bool

/-- Run a synchronous automaton LSB-first on a `w`-slice stream. -/
def SyncAutomaton.runN {k : Nat} {S : Type} (M : SyncAutomaton k S) :
    (w : Nat) → (Fin w → Fin (2 ^ k)) → S
  | 0, _ => M.init
  | w + 1, stream =>
    M.step (M.runN w (fun i => stream i.castSucc)) (stream (Fin.last w))

/--
An explicit finite reachable-state invariant certificate for a synchronous automaton:
- `states` lists the reachable states, with `states[0] = M.init`;
- `nextIdx[i][a]` witnesses the index `j < states.length` with `M.step states[i] a = states[j]`.
-/
structure AutomatonCert (S : Type) where
  states  : List S
  nextIdx : List (List Nat)

/-- Total, executable certificate checker verified inside Lean's kernel via `decide`. -/
def checkCert {k : Nat} {S : Type} [BEq S]
    (M : SyncAutomaton k S) (cert : AutomatonCert S) : Bool :=
  let n := cert.states.length
  let alpha := 2 ^ k
  decide (0 < n) &&
  (match cert.states[0]? with
   | some s0 => s0 == M.init
   | none => false) &&
  (cert.nextIdx.length == n) &&
  allBelow n (fun i =>
    match cert.states[i]?, cert.nextIdx[i]? with
    | some si, some row =>
      (row.length == alpha) &&
      M.accept si &&
      allBelow alpha (fun a =>
        if hlt : a < alpha then
          match row[a]? with
          | some j =>
            decide (j < n) &&
            match cert.states[j]? with
            | some sj => M.step si ⟨a, hlt⟩ == sj
            | none => false
          | none => false
        else false)
    | _, _ => false)

/-- A pipelined synchronous bit-stream transducer emitting `Option Bool` at each tick. -/
structure PipeTransducer (k : Nat) (S : Type) where
  init : S
  step : S → Option (Fin (2 ^ k)) → S × Option Bool

def pipeVar {k : Nat} (j : Fin k) : PipeTransducer k Unit where
  init := ()
  step _ inp := ((), inp.map (fun a => a.val.testBit j.val))

def pipeZero (k : Nat) : PipeTransducer k Unit where
  init := ()
  step _ inp := ((), inp.map (fun _ => false))

def pipeAllOnes (k : Nat) : PipeTransducer k Unit where
  init := ()
  step _ inp := ((), inp.map (fun _ => true))

def pipeOne (k : Nat) : PipeTransducer k Bool where
  init := true
  step isLsb inp :=
    match inp with
    | some _ => (false, some isLsb)
    | none => (false, none)

def pipeDelay1 {k : Nat} {S : Type} (T : PipeTransducer k S) :
    PipeTransducer k (S × Option Bool) where
  init := (T.init, none)
  step st inp :=
    let (s', o') := T.step st.1 inp
    ((s', o'), st.2)

def DelayState (S : Type) : Nat → Type
  | 0 => S
  | n + 1 => DelayState S n × Option Bool

def pipeDelayK {k : Nat} {S : Type} (T : PipeTransducer k S) :
    (n : Nat) → PipeTransducer k (DelayState S n)
  | 0 => T
  | n + 1 => pipeDelay1 (pipeDelayK T n)

def pipeNot {k : Nat} {S : Type} (T : PipeTransducer k S) : PipeTransducer k S where
  init := T.init
  step s inp :=
    let (s', o) := T.step s inp
    (s', o.map (!·))

def pipeShl1 {k : Nat} {S : Type} (T : PipeTransducer k S) :
    PipeTransducer k (S × Bool) where
  init := (T.init, false)
  step st inp :=
    let (s', o) := T.step st.1 inp
    match o with
    | some b => ((s', b), some st.2)
    | none => ((s', st.2), none)

def pipeUshr1 {k : Nat} {S : Type} (T : PipeTransducer k S) :
    PipeTransducer k (S × Bool) where
  init := (T.init, false)
  step st inp :=
    let (s', o) := T.step st.1 inp
    if !st.2 then
      ((s', o.isSome), none)
    else
      match o with
      | some b => ((s', true), some b)
      | none => ((s', false), some false)

def pipeAshr1 {k : Nat} {S : Type} (T : PipeTransducer k S) :
    PipeTransducer k (S × Option Bool) where
  init := (T.init, none)
  step st inp :=
    let (s', o) := T.step st.1 inp
    match st.2 with
    | none => ((s', o), none)
    | some p =>
      match o with
      | some b => ((s', some b), some b)
      | none => ((s', none), some p)

def pipeBinOp {k : Nat} {S₁ S₂ : Type} (op : Bool → Bool → Bool)
    (T₁ : PipeTransducer k S₁) (T₂ : PipeTransducer k S₂) :
    PipeTransducer k (S₁ × S₂) where
  init := (T₁.init, T₂.init)
  step st inp :=
    let (s1', o1) := T₁.step st.1 inp
    let (s2', o2) := T₂.step st.2 inp
    ((s1', s2'),
     match o1, o2 with
     | some b1, some b2 => some (op b1 b2)
     | _, _ => none)

def pipeAdd {k : Nat} {S₁ S₂ : Type}
    (T₁ : PipeTransducer k S₁) (T₂ : PipeTransducer k S₂) :
    PipeTransducer k ((S₁ × S₂) × Bool) where
  init := ((T₁.init, T₂.init), false)
  step st inp :=
    let (s1', o1) := T₁.step st.1.1 inp
    let (s2', o2) := T₂.step st.1.2 inp
    match o1, o2 with
    | some b1, some b2 =>
      (((s1', s2'), b1.atLeastTwo b2 st.2), some (b1 ^^ (b2 ^^ st.2)))
    | _, _ => (((s1', s2'), st.2), none)

def pipeSub {k : Nat} {S₁ S₂ : Type}
    (T₁ : PipeTransducer k S₁) (T₂ : PipeTransducer k S₂) :
    PipeTransducer k ((S₁ × S₂) × Bool) where
  init := ((T₁.init, T₂.init), true)
  step st inp :=
    let (s1', o1) := T₁.step st.1.1 inp
    let (s2', o2) := T₂.step st.1.2 inp
    match o1, o2 with
    | some b1, some b2 =>
      let nb2 := !b2
      (((s1', s2'), b1.atLeastTwo nb2 st.2), some (b1 ^^ (nb2 ^^ st.2)))
    | _, _ => (((s1', s2'), st.2), none)

def pipeNeg {k : Nat} {S : Type} (T : PipeTransducer k S) :
    PipeTransducer k (S × Bool) where
  init := (T.init, true)
  step st inp :=
    let (s', o) := T.step st.1 inp
    match o with
    | some b =>
      let nb := !b
      ((s', nb && st.2), some (nb ^^ st.2))
    | none => ((s', st.2), none)

/-- Exact Hamming-weight parity (`popcount(x) % 2`) defined recursively on `BitVec w`. -/
def bvParityAux {w : Nat} (x : BitVec w) : Nat → Bool
  | 0 => false
  | n + 1 => bvParityAux x n ^^ x.getLsbD n

def bvParity {w : Nat} (x : BitVec w) : Bool := bvParityAux x w

/-- Bit-vector expression AST over `k` arbitrary-width `BitVec w` variables. -/
inductive BVExpr (k : Nat) where
  | var     : Fin k → BVExpr k
  | zero    : BVExpr k
  | allOnes : BVExpr k
  | one     : BVExpr k
  | not     : BVExpr k → BVExpr k
  | neg     : BVExpr k → BVExpr k
  | shl1    : BVExpr k → BVExpr k
  | ushr1   : BVExpr k → BVExpr k
  | ashr1   : BVExpr k → BVExpr k
  | and     : BVExpr k → BVExpr k → BVExpr k
  | or      : BVExpr k → BVExpr k → BVExpr k
  | xor     : BVExpr k → BVExpr k → BVExpr k
  | add     : BVExpr k → BVExpr k → BVExpr k
  | sub     : BVExpr k → BVExpr k → BVExpr k

/-- Native Lean 4 `BitVec w` semantics of `BVExpr k`. -/
def BVExpr.eval {k : Nat} (w : Nat) (env : Fin k → BitVec w) : BVExpr k → BitVec w
  | .var j     => env j
  | .zero      => 0#w
  | .allOnes   => BitVec.allOnes w
  | .one       => 1#w
  | .not e     => ~~~(e.eval w env)
  | .neg e     => -(e.eval w env)
  | .shl1 e    => (e.eval w env) <<< 1
  | .ushr1 e   => (e.eval w env) >>> 1
  | .ashr1 e   => (e.eval w env).sshiftRight 1
  | .and a b   => a.eval w env &&& b.eval w env
  | .or a b    => a.eval w env ||| b.eval w env
  | .xor a b   => a.eval w env ^^^ b.eval w env
  | .add a b   => a.eval w env + b.eval w env
  | .sub a b   => a.eval w env - b.eval w env

/-- Exact pipeline lookahead latency of a `BVExpr k`. -/
def BVExpr.latency {k : Nat} : BVExpr k → Nat
  | .var _     => 0
  | .zero      => 0
  | .allOnes   => 0
  | .one       => 0
  | .not e     => e.latency
  | .neg e     => e.latency
  | .shl1 e    => e.latency
  | .ushr1 e   => e.latency + 1
  | .ashr1 e   => e.latency + 1
  | .and a b   => max a.latency b.latency
  | .or a b    => max a.latency b.latency
  | .xor a b   => max a.latency b.latency
  | .add a b   => max a.latency b.latency
  | .sub a b   => max a.latency b.latency

/-- Compiled finite state type for `BVExpr k`. -/
def BVExpr.State {k : Nat} : BVExpr k → Type
  | .var _     => Unit
  | .zero      => Unit
  | .allOnes   => Unit
  | .one       => Bool
  | .not e     => e.State
  | .neg e     => e.State × Bool
  | .shl1 e    => e.State × Bool
  | .ushr1 e   => e.State × Bool
  | .ashr1 e   => e.State × Option Bool
  | .and a b   =>
      DelayState a.State (max a.latency b.latency - a.latency) ×
      DelayState b.State (max a.latency b.latency - b.latency)
  | .or a b    =>
      DelayState a.State (max a.latency b.latency - a.latency) ×
      DelayState b.State (max a.latency b.latency - b.latency)
  | .xor a b   =>
      DelayState a.State (max a.latency b.latency - a.latency) ×
      DelayState b.State (max a.latency b.latency - b.latency)
  | .add a b   =>
      (DelayState a.State (max a.latency b.latency - a.latency) ×
       DelayState b.State (max a.latency b.latency - b.latency)) × Bool
  | .sub a b   =>
      (DelayState a.State (max a.latency b.latency - a.latency) ×
       DelayState b.State (max a.latency b.latency - b.latency)) × Bool

/-- Compile a `BVExpr k` into a latency-aligned `PipeTransducer`. -/
def compileExpr {k : Nat} : (e : BVExpr k) → PipeTransducer k e.State
  | .var j     => pipeVar j
  | .zero      => pipeZero k
  | .allOnes   => pipeAllOnes k
  | .one       => pipeOne k
  | .not e     => pipeNot (compileExpr e)
  | .neg e     => pipeNeg (compileExpr e)
  | .shl1 e    => pipeShl1 (compileExpr e)
  | .ushr1 e   => pipeUshr1 (compileExpr e)
  | .ashr1 e   => pipeAshr1 (compileExpr e)
  | .and a b   =>
      pipeBinOp (· && ·) (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
                         (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .or a b    =>
      pipeBinOp (· || ·) (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
                         (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .xor a b   =>
      pipeBinOp xor (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
                    (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .add a b   =>
      pipeAdd (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
              (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .sub a b   =>
      pipeSub (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
              (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))

/-- A pipelined predicate automaton with stabilization latency `latency`. -/
structure PipePred (k : Nat) (S : Type) where
  init    : S
  step    : S → Option (Fin (2 ^ k)) → S
  verdict : S → Bool
  latency : Nat

/-- Run `n` deterministic flush (`none`) steps. -/
def flushN {k : Nat} {S : Type} (step : S → Option (Fin (2 ^ k)) → S) : Nat → S → S
  | 0, s => s
  | n + 1, s => flushN step n (step s none)

/-- Convert a `PipePred` into a standard `SyncAutomaton` (flush happens inside `accept`). -/
def PipePred.toSync {k : Nat} {S : Type} (P : PipePred k S) : SyncAutomaton k S where
  init := P.init
  step s a := P.step s (some a)
  accept s := P.verdict (flushN P.step P.latency s)

inductive BVProp (k : Nat) where
  | eq      : BVExpr k → BVExpr k → BVProp k
  | ult     : BVExpr k → BVExpr k → BVProp k
  | ule     : BVExpr k → BVExpr k → BVProp k
  | slt     : BVExpr k → BVExpr k → BVProp k
  | sle     : BVExpr k → BVExpr k → BVProp k
  | msb     : BVExpr k → BVProp k
  | lsb     : BVExpr k → BVProp k
  | parity  : BVExpr k → BVProp k
  | widthGe : Nat → BVProp k
  | pNot    : BVProp k → BVProp k
  | pAnd    : BVProp k → BVProp k → BVProp k
  | pOr     : BVProp k → BVProp k → BVProp k
  | pImp    : BVProp k → BVProp k → BVProp k
  | pIff    : BVProp k → BVProp k → BVProp k

/-- Native Lean 4 `BitVec w` Boolean semantics of `BVProp k`. -/
def BVProp.eval {k : Nat} (w : Nat) (env : Fin k → BitVec w) : BVProp k → Bool
  | .eq a b     => a.eval w env == b.eval w env
  | .ult a b    => (a.eval w env).ult (b.eval w env)
  | .ule a b    => (a.eval w env).ule (b.eval w env)
  | .slt a b    => (a.eval w env).slt (b.eval w env)
  | .sle a b    => (a.eval w env).sle (b.eval w env)
  | .msb e      => (e.eval w env).msb
  | .lsb e      => (e.eval w env).getLsbD 0
  | .parity e   => bvParity (e.eval w env)
  | .widthGe n  => decide (n ≤ w)
  | .pNot p     => !(p.eval w env)
  | .pAnd a b   => a.eval w env && b.eval w env
  | .pOr a b    => a.eval w env || b.eval w env
  | .pImp a b   => !(a.eval w env) || b.eval w env
  | .pIff a b   => a.eval w env == b.eval w env

/-- Compiled finite state type for `BVProp k`. -/
def BVProp.State {k : Nat} : BVProp k → Type
  | .eq a b =>
      (DelayState a.State (max a.latency b.latency - a.latency) ×
       DelayState b.State (max a.latency b.latency - b.latency)) × Bool
  | .ult a b =>
      (DelayState a.State (max a.latency b.latency - a.latency) ×
       DelayState b.State (max a.latency b.latency - b.latency)) × Bool
  | .ule a b =>
      (DelayState a.State (max a.latency b.latency - a.latency) ×
       DelayState b.State (max a.latency b.latency - b.latency)) × Bool
  | .slt a b =>
      ((DelayState a.State (max a.latency b.latency - a.latency) ×
        DelayState b.State (max a.latency b.latency - b.latency)) × Bool) × Bool
  | .sle a b =>
      ((DelayState a.State (max a.latency b.latency - a.latency) ×
        DelayState b.State (max a.latency b.latency - b.latency)) × Bool) × Bool
  | .msb e     => e.State × Bool
  | .lsb e     => (e.State × Bool) × Bool
  | .parity e  => e.State × Bool
  | .widthGe _ => Nat
  | .pNot p    => p.State
  | .pAnd a b  => a.State × b.State
  | .pOr a b   => a.State × b.State
  | .pImp a b  => a.State × b.State
  | .pIff a b  => a.State × b.State

def predEq {k : Nat} {S₁ S₂ : Type} (d : Nat)
    (T₁ : PipeTransducer k S₁) (T₂ : PipeTransducer k S₂) :
    PipePred k ((S₁ × S₂) × Bool) where
  init := ((T₁.init, T₂.init), true)
  step st inp :=
    let (s1', o1) := T₁.step st.1.1 inp
    let (s2', o2) := T₂.step st.1.2 inp
    match o1, o2 with
    | some b1, some b2 => ((s1', s2'), st.2 && (b1 == b2))
    | _, _ => ((s1', s2'), st.2)
  verdict st := st.2
  latency := d

def predUcmp {k : Nat} {S₁ S₂ : Type} (d : Nat) (initB : Bool)
    (T₁ : PipeTransducer k S₁) (T₂ : PipeTransducer k S₂) :
    PipePred k ((S₁ × S₂) × Bool) where
  init := ((T₁.init, T₂.init), initB)
  step st inp :=
    let (s1', o1) := T₁.step st.1.1 inp
    let (s2', o2) := T₂.step st.1.2 inp
    match o1, o2 with
    | some b1, some b2 => ((s1', s2'), ((!b1 && b2) || ((b1 == b2) && st.2)))
    | _, _ => ((s1', s2'), st.2)
  verdict st := st.2
  latency := d

def predScmp {k : Nat} {S₁ S₂ : Type} (d : Nat) (initB : Bool)
    (T₁ : PipeTransducer k S₁) (T₂ : PipeTransducer k S₂) :
    PipePred k (((S₁ × S₂) × Bool) × Bool) where
  init := (((T₁.init, T₂.init), initB), initB)
  step st inp :=
    let (s1', o1) := T₁.step st.1.1.1 inp
    let (s2', o2) := T₂.step st.1.1.2 inp
    match o1, o2 with
    | some b1, some b2 =>
      let u := st.1.2
      let sg' := (b1 && !b2) || ((b1 == b2) && u)
      let u'  := (!b1 && b2) || ((b1 == b2) && u)
      (((s1', s2'), u'), sg')
    | _, _ => (((s1', s2'), st.1.2), st.2)
  verdict st := st.2
  latency := d

def predMsb {k : Nat} {S : Type} (d : Nat) (T : PipeTransducer k S) :
    PipePred k (S × Bool) where
  init := (T.init, false)
  step st inp :=
    let (s', o) := T.step st.1 inp
    (s', match o with | some b => b | none => st.2)
  verdict st := st.2
  latency := d

def predLsb {k : Nat} {S : Type} (d : Nat) (T : PipeTransducer k S) :
    PipePred k ((S × Bool) × Bool) where
  init := ((T.init, false), false)
  step st inp :=
    let (s', o) := T.step st.1.1 inp
    match o with
    | some b => if !st.1.2 then ((s', true), b) else ((s', true), st.2)
    | none => ((s', st.1.2), st.2)
  verdict st := st.2
  latency := d

def predParity {k : Nat} {S : Type} (d : Nat) (T : PipeTransducer k S) :
    PipePred k (S × Bool) where
  init := (T.init, false)
  step st inp :=
    let (s', o) := T.step st.1 inp
    (s', match o with | some b => st.2 ^^ b | none => st.2)
  verdict st := st.2
  latency := d

def predWidthGe (k n : Nat) : PipePred k Nat where
  init := 0
  step st inp := match inp with | some _ => min n (st + 1) | none => st
  verdict st := decide (n ≤ st)
  latency := 0

def predNot {k : Nat} {S : Type} (P : PipePred k S) : PipePred k S where
  init := P.init
  step := P.step
  verdict s := !(P.verdict s)
  latency := P.latency

def predBin {k : Nat} {S₁ S₂ : Type} (op : Bool → Bool → Bool)
    (P₁ : PipePred k S₁) (P₂ : PipePred k S₂) : PipePred k (S₁ × S₂) where
  init := (P₁.init, P₂.init)
  step st inp := (P₁.step st.1 inp, P₂.step st.2 inp)
  verdict st := op (P₁.verdict st.1) (P₂.verdict st.2)
  latency := max P₁.latency P₂.latency

/-- Compile `BVProp k` to a `PipePred k p.State`. -/
def compileProp {k : Nat} : (p : BVProp k) → PipePred k p.State
  | .eq a b =>
      predEq (max a.latency b.latency)
        (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
        (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .ult a b =>
      predUcmp (max a.latency b.latency) false
        (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
        (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .ule a b =>
      predUcmp (max a.latency b.latency) true
        (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
        (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .slt a b =>
      predScmp (max a.latency b.latency) false
        (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
        (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .sle a b =>
      predScmp (max a.latency b.latency) true
        (pipeDelayK (compileExpr a) (max a.latency b.latency - a.latency))
        (pipeDelayK (compileExpr b) (max a.latency b.latency - b.latency))
  | .msb e     => predMsb e.latency (compileExpr e)
  | .lsb e     => predLsb e.latency (compileExpr e)
  | .parity e  => predParity e.latency (compileExpr e)
  | .widthGe n => predWidthGe k n
  | .pNot p    => predNot (compileProp p)
  | .pAnd a b  => predBin (· && ·) (compileProp a) (compileProp b)
  | .pOr a b   => predBin (· || ·) (compileProp a) (compileProp b)
  | .pImp a b  => predBin (fun x y => !x || y) (compileProp a) (compileProp b)
  | .pIff a b  => predBin (· == ·) (compileProp a) (compileProp b)

/-- Final compiler target: a standard `SyncAutomaton` for `checkCert`. -/
def compileToSync {k : Nat} (p : BVProp k) : SyncAutomaton k p.State :=
  (compileProp p).toSync

/-! ### Predicate Decidability Soundness Lemmas -/

/-- Overflow-free unsigned floor average `⌊(x + y) / 2⌋` on `BitVec w`. -/
def unsignedAvg {w : Nat} (x y : BitVec w) : BitVec w :=
  (x &&& y) + ((x ^^^ y) >>> 1)

/-- Overflow-free signed two's-complement floor average `⌊(x_s + y_s) / 2⌋` on `BitVec w`. -/
def signedAvg {w : Nat} (x y : BitVec w) : BitVec w :=
  (x &&& y) + ((x ^^^ y).sshiftRight 1)

/-- Bitwise 3-operand carry-save majority `(x & y) | (y & z) | (z & x)`. -/
def bvMaj {w : Nat} (x y z : BitVec w) : BitVec w :=
  (x &&& y) ||| (y &&& z) ||| (z &&& x)

/-- Overflow-free 3-operand unsigned carry-save quarter-sum `⌊(x + y + z) / 4⌋` on `BitVec w`. -/
def unsignedQuarterSum {w : Nat} (x y z : BitVec w) : BitVec w :=
  unsignedAvg (bvMaj x y z) ((x ^^^ y ^^^ z) >>> 1)

/-- Overflow-free 3-operand signed carry-save quarter-sum `⌊(x_s + y_s + z_s) / 4⌋` on `BitVec w`. -/
def signedQuarterSum {w : Nat} (x y z : BitVec w) : BitVec w :=
  signedAvg (bvMaj x y z) ((x ^^^ y ^^^ z).sshiftRight 1)

/-- Two's-complement signed addition overflow indicator for `x + y`. -/
def signedAddOverflow {w : Nat} (x y : BitVec w) : Bool :=
  ((x ^^^ (x + y)) &&& (y ^^^ (x + y))).msb

/-- Binary-reflected Gray code `G(x) = x ^^^ (x >>> 1)` on `BitVec w`. -/
def grayCode {w : Nat} (x : BitVec w) : BitVec w :=
  x ^^^ (x >>> 1)

@[instance_reducible]
def beqProd {α β : Type} (ba : BEq α) (bb : BEq β) : BEq (α × β) :=
  ⟨fun (a1, b1) (a2, b2) => ba.beq a1 a2 && bb.beq b1 b2⟩

instance instBEqDelayState {S : Type} [BEq S] : ∀ n, BEq (DelayState S n)
  | 0 => inferInstanceAs (BEq S)
  | n + 1 => beqProd (instBEqDelayState n) inferInstance

instance instBEqBVExprState {k : Nat} : (e : BVExpr k) → BEq e.State
  | .var _   => inferInstanceAs (BEq Unit)
  | .zero    => inferInstanceAs (BEq Unit)
  | .allOnes => inferInstanceAs (BEq Unit)
  | .one     => inferInstanceAs (BEq Bool)
  | .not e   => instBEqBVExprState e
  | .neg e   => beqProd (instBEqBVExprState e) inferInstance
  | .shl1 e  => beqProd (instBEqBVExprState e) inferInstance
  | .ushr1 e => beqProd (instBEqBVExprState e) inferInstance
  | .ashr1 e => beqProd (instBEqBVExprState e) inferInstance
  | .and a b =>
      beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
              (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency))
  | .or a b  =>
      beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
              (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency))
  | .xor a b =>
      beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
              (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency))
  | .add a b =>
      beqProd
        (beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
                 (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency)))
        inferInstance
  | .sub a b =>
      beqProd
        (beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
                 (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency)))
        inferInstance

instance instBEqBVPropState {k : Nat} : (p : BVProp k) → BEq p.State
  | .eq a b =>
      beqProd
        (beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
                 (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency)))
        inferInstance
  | .ult a b =>
      beqProd
        (beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
                 (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency)))
        inferInstance
  | .ule a b =>
      beqProd
        (beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
                 (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency)))
        inferInstance
  | .slt a b =>
      beqProd
        (beqProd
          (beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
                   (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency)))
          inferInstance)
        inferInstance
  | .sle a b =>
      beqProd
        (beqProd
          (beqProd (@instBEqDelayState _ (instBEqBVExprState a) (max a.latency b.latency - a.latency))
                   (@instBEqDelayState _ (instBEqBVExprState b) (max a.latency b.latency - b.latency)))
          inferInstance)
        inferInstance
  | .msb e     => beqProd (instBEqBVExprState e) inferInstance
  | .lsb e     => beqProd (beqProd (instBEqBVExprState e) inferInstance) inferInstance
  | .parity e  => beqProd (instBEqBVExprState e) inferInstance
  | .widthGe _ => inferInstanceAs (BEq Nat)
  | .pNot p    => instBEqBVPropState p
  | .pAnd a b  => beqProd (instBEqBVPropState a) (instBEqBVPropState b)
  | .pOr a b   => beqProd (instBEqBVPropState a) (instBEqBVPropState b)
  | .pImp a b  => beqProd (instBEqBVPropState a) (instBEqBVPropState b)
  | .pIff a b  => beqProd (instBEqBVPropState a) (instBEqBVPropState b)

end BitSync
