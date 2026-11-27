/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`AutomaticWordAvoidanceCompiler`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace SiliconAvoidance

-- ============================================================================
-- Section 1: Pure-Silicon Bitwise Arithmetic & Exact Bit-Slice Lemmas
-- ============================================================================

def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n == 0 then 0 else n % 2 + popcountAux fuel (n / 2)

def popcount (n : Nat) : Nat := popcountAux n n

def carryXor (K n : Nat) : Nat := popcount ((K * n) ^^^ n) % 2
def carryAnd (K n : Nat) : Nat := popcount ((K * n) &&& n) % 2
def grayMod4 (n : Nat) : Nat := popcount (n ^^^ (n / 2)) % 4

-- ============================================================================
-- Section 2: Pure-Data LSB-Indexed Binary Tree (`BTree`) & `DFAO` Engine
-- ============================================================================

inductive BTree (α : Type) where
  | empty : BTree α
  | leaf  : α → BTree α
  | node  : BTree α → BTree α → BTree α
  deriving Repr, DecidableEq

def BTree.get? {α : Type} : BTree α → Nat → Option α
  | .empty, _ => none
  | .leaf x, 0 => some x
  | .leaf _, _ + 1 => none
  | .node l r, n => if n % 2 == 0 then l.get? (n / 2) else r.get? (n / 2)

def BTree.all {α : Type} (p : α → Bool) : BTree α → Bool
  | .empty => true
  | .leaf x => p x
  | .node l r => l.all p && r.all p

/-- Pure-data 2-automatic finite-state transducer (MSB-first DFAO). -/
structure DFAO where
  numStates : Nat
  numAlpha  : Nat
  q0        : Nat
  d0        : List Nat
  d1        : List Nat
  tau       : List Nat
  deriving Repr, DecidableEq

def DFAO.step0 (M : DFAO) (q : Nat) : Nat := M.d0.getD q 0
def DFAO.step1 (M : DFAO) (q : Nat) : Nat := M.d1.getD q 0
def DFAO.out   (M : DFAO) (q : Nat) : Nat := M.tau.getD q 0

def DFAO.wf (M : DFAO) : Bool :=
  (0 < M.numStates) &&
  (0 < M.numAlpha) &&
  (M.q0 < M.numStates) &&
  (M.d0.length == M.numStates) &&
  (M.d1.length == M.numStates) &&
  (M.tau.length == M.numStates) &&
  (M.d0.all (fun q => q < M.numStates)) &&
  (M.d1.all (fun q => q < M.numStates)) &&
  (M.tau.all (fun a => a < M.numAlpha)) &&
  (M.step0 M.q0 == M.q0)

def DFAO.evalStateAux (M : DFAO) : Nat → Nat → Nat
  | 0, _ => M.q0
  | fuel + 1, n =>
    if n == 0 then M.q0
    else
      let q := M.evalStateAux fuel (n / 2)
      if n % 2 == 0 then M.step0 q else M.step1 q

def DFAO.evalState (M : DFAO) (n : Nat) : Nat :=
  M.evalStateAux n n

def DFAO.evalWord (M : DFAO) (n : Nat) : Nat :=
  M.out (M.evalState n)

-- ============================================================================
-- Section 4: Layer 1 — Pure-Data Overlap-Graph Window Certificate Engine
-- ============================================================================

def stateWindow (M : DFAO) (W n : Nat) : List Nat :=
  (List.range W).map (fun i => M.evalState (n + i))

def outputWindow (M : DFAO) (W n : Nat) : List Nat :=
  (List.range W).map (fun i => M.evalWord (n + i))

def stepWindow (M : DFAO) (b : Bool) (win : List Nat) : List Nat :=
  (List.range win.length).map (fun i =>
    let idx := (if b then 1 else 0) + i
    let q := win.getD (idx / 2) 0
    if idx % 2 == 0 then M.step0 q else M.step1 q)

/-- Pure-data node in an overlap-graph window certificate. -/
structure WindowNode where
  win   : List Nat
  next0 : Nat
  next1 : Nat
  deriving Repr, DecidableEq

/-- Pure-data finite overlap-graph certificate (ZERO Prop fields). -/
structure WindowCert where
  graph : BTree WindowNode
  deriving Repr, DecidableEq

def checkWindowCert (M : DFAO) (W : Nat) (ok : List Nat → Bool) (cert : WindowCert) : Bool :=
  M.wf &&
  (match cert.graph.get? 0 with
   | some nd => nd.win == stateWindow M W 0
   | none => false) &&
  cert.graph.all (fun nd =>
    (nd.win.length == W) &&
    nd.win.all (fun q => q < M.numStates) &&
    ok (nd.win.map M.out) &&
    (match cert.graph.get? nd.next0 with
     | some nd0 => nd0.win == stepWindow M false nd.win
     | none => false) &&
    (match cert.graph.get? nd.next1 with
     | some nd1 => nd1.win == stepWindow M true nd.win
     | none => false))

-- ============================================================================
-- Section 5: Layer 2 — Parity-Sync & Unbounded k-Power Avoidance Compiler
-- ============================================================================

def encodeWord (base : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc * base + x) 0

/-- Pure-data parity-tagged overlap-graph node. -/
structure SyncNode where
  parity : Bool
  win    : List Nat
  next0  : Nat
  next1  : Nat
  deriving Repr, DecidableEq

/-- Pure-data Parity-Synchronization Certificate (bitmask decoder + overlap graph). -/
structure SyncCert where
  width      : Nat
  parityMask : Nat
  graph      : BTree SyncNode
  deriving Repr, DecidableEq

def checkSyncCert (M : DFAO) (cert : SyncCert) : Bool :=
  M.wf &&
  (0 < cert.width) &&
  (match cert.graph.get? 0 with
   | some nd => (nd.parity == false) && (nd.win == stateWindow M cert.width 0)
   | none => false) &&
  cert.graph.all (fun nd =>
    (nd.win.length == cert.width) &&
    nd.win.all (fun q => q < M.numStates) &&
    (cert.parityMask.testBit (encodeWord M.numAlpha (nd.win.map M.out)) == nd.parity) &&
    (match cert.graph.get? nd.next0 with
     | some nd0 => (nd0.parity == false) && (nd0.win == stepWindow M false nd.win)
     | none => false) &&
    (match cert.graph.get? nd.next1 with
     | some nd1 => (nd1.parity == true) && (nd1.win == stepWindow M true nd.win)
     | none => false))

/-- Pure-data predicate: window of length `k * p` is NOT a k-power of period `p`. -/
def noPowerAtPeriod (k p : Nat) (outWin : List Nat) : Bool :=
  (List.range ((k - 1) * p)).any (fun j => outWin.getD j 0 != outWin.getD (j + p) 0)

/-- Pure-data Unbounded k-Power Avoidance Certificate (ZERO Prop fields). -/
structure PowerAvoidCert where
  syncCert  : SyncCert
  invEven   : List Nat
  reachCert : WindowCert
  baseCerts : List WindowCert
  deriving Repr, DecidableEq

def checkBasePowerCerts (M : DFAO) (k : Nat) : Nat → List WindowCert → Bool
  | _, [] => true
  | p, c :: cs =>
    checkWindowCert M (k * p) (noPowerAtPeriod k p) c &&
    checkBasePowerCerts M k (p + 1) cs

def checkPowerAvoidCert (M : DFAO) (k : Nat) (cert : PowerAvoidCert) : Bool :=
  (2 ≤ k) &&
  checkSyncCert M cert.syncCert &&
  checkWindowCert M 1 (fun _ => true) cert.reachCert &&
  cert.reachCert.graph.all (fun nd =>
    let q := nd.win.getD 0 0
    cert.invEven.getD (M.out (M.step0 q)) M.numAlpha == M.out q) &&
  (let pSync := (cert.syncCert.width + k - 2) / (k - 1)
   (cert.baseCerts.length == pSync - 1) &&
   checkBasePowerCerts M k 1 cert.baseCerts)

-- ============================================================================
-- Section 6: Layer 3 — Parity-Conditioned Overlap-Avoidance Compiler
-- ============================================================================

def noOverlapAtPeriod (p : Nat) (outWin : List Nat) : Bool :=
  (List.range (p + 1)).any (fun j => outWin.getD j 0 != outWin.getD (j + p) 0)

def checkBaseOverlapCerts (M : DFAO) : Nat → List WindowCert → Bool
  | _, [] => true
  | p, c :: cs =>
    checkWindowCert M (2 * p + 1) (noOverlapAtPeriod p) c &&
    checkBaseOverlapCerts M (p + 1) cs

/-- Pure-data Unbounded Overlap-Avoidance Certificate (ZERO Prop fields). -/
structure OverlapAvoidCert where
  syncCert    : SyncCert
  reachPar    : BTree SyncNode
  invPair     : List Nat
  invEvenPar0 : List Nat
  invEvenPar1 : List Nat
  invOddPar0  : List Nat
  invOddPar1  : List Nat
  baseCerts   : List WindowCert
  deriving Repr, DecidableEq

def checkReachPar1 (M : DFAO) (rp : BTree SyncNode) : Bool :=
  M.wf &&
  (match rp.get? 0 with
   | some nd => (nd.parity == false) && (nd.win == stateWindow M 1 0)
   | none => false) &&
  rp.all (fun nd =>
    (nd.win.length == 1) &&
    nd.win.all (fun q => q < M.numStates) &&
    (match rp.get? nd.next0 with
     | some nd0 => (nd0.parity == false) && (nd0.win == stepWindow M false nd.win)
     | none => false) &&
    (match rp.get? nd.next1 with
     | some nd1 => (nd1.parity == true) && (nd1.win == stepWindow M true nd.win)
     | none => false))

def checkOverlapAvoidCert (M : DFAO) (cert : OverlapAvoidCert) : Bool :=
  checkSyncCert M cert.syncCert &&
  checkReachPar1 M cert.reachPar &&
  cert.reachPar.all (fun nd =>
    let q := nd.win.getD 0 0
    let oq := M.out q
    let o0 := M.out (M.step0 q)
    let o1 := M.out (M.step1 q)
    (cert.invPair.getD (o0 * M.numAlpha + o1) M.numAlpha == oq) &&
    (if nd.parity == false then
       (cert.invEvenPar0.getD o0 M.numAlpha == oq) &&
       (cert.invOddPar0.getD o1 M.numAlpha == oq)
     else
       (cert.invEvenPar1.getD o0 M.numAlpha == oq) &&
       (cert.invOddPar1.getD o1 M.numAlpha == oq))) &&
  (cert.baseCerts.length == 2 * cert.syncCert.width - 1) &&
  checkBaseOverlapCerts M 1 cert.baseCerts

end SiliconAvoidance
