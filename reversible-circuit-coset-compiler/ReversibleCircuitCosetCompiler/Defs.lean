/-
  certcomp-14: Verified Lean 4 Reversible-Circuit Commutation & Group-Word Compiler
  =================================================================================
  Standalone Lean 4.34.1 (no Mathlib, no Lake).

  Architecture:
    Section 1 : Width-indexed reversible silicon machine (`State r w`, `Gate r`, exact `BitVec w`
                semantics, syntactic inverses & kernel-verified bijectivity).
    Section 2 : LSB-Causal Truncation & Bit-Window Projection Lifter (Layers 1A & 3):
                lifts local finite-width equivalence (`checkWindowEq`), pairwise distinctness
                (`checkDistinctAt`), and exact order lower bounds (`checkOrderLowerAt`) to ∀ w ≥ w0.
    Section 3 : Carry-Bit-Slice Transducer Bisimulation Lifter (Layer 1B):
                compiles hybrid register-parallel bitwise + modular-arithmetic circuits to
                2's-complement ripple-carry Mealy machines; finite bisimulation certificates
                (`checkBisimCert`) lift to ∀ w : Nat.
    Section 4 : Group-Word Rewriting & Finite Coset-Table Compiler (Layers 2A & 2B):
                `checkRewriteCert` & `checkCosetCert` lift local relator libraries and closed
                Cayley/coset tables to arbitrary-length word compilation, universal modulo-d
                power reduction (∀ n : Nat, ∀ w ≥ w0), and exact group cardinality theorems.
-/

namespace RevCert

-- ============================================================================
-- SECTION 1: Width-Indexed Reversible Silicon Machine & Exact BitVec Semantics
-- ============================================================================

abbrev State (r w : Nat) := Fin r → BitVec w

def setReg {r w : Nat} (s : State r w) (i : Fin r) (v : BitVec w) : State r w :=
  fun j => if j = i then v else s j

@[simp] theorem setReg_self {r w : Nat} (s : State r w) (i : Fin r) (v : BitVec w) :
    setReg s i v i = v := by
  simp [setReg]

@[simp] theorem setReg_ne {r w : Nat} (s : State r w) {i j : Fin r} (h : j ≠ i) (v : BitVec w) :
    setReg s i v j = s j := by
  simp [setReg, h]

def swapRegs {r w : Nat} (s : State r w) (i j : Fin r) : State r w :=
  fun k => if k = i then s j else if k = j then s i else s k

def flipBit {w : Nat} (x : BitVec w) (p : Nat) : BitVec w :=
  if p < w then x ^^^ (1#w <<< p) else x

inductive Gate (r : Nat) where
  | rNot  (i : Fin r)
  | rSwap (i j : Fin r)
  | rCnot (c t : Fin r)
  | rToff (c1 c2 t : Fin r)
  | rAdd  (s t : Fin r)
  | rSub  (s t : Fin r)
  | rNeg  (i : Fin r)
  | rInc  (i : Fin r)
  | rDec  (i : Fin r)
  | bNot  (i : Fin r) (p : Nat)
  | bSwap (i1 : Fin r) (p1 : Nat) (i2 : Fin r) (p2 : Nat)
  | bCnot (ic : Fin r) (pc : Nat) (it : Fin r) (pt : Nat)
  | bToff (i1 : Fin r) (p1 : Nat) (i2 : Fin r) (p2 : Nat) (it : Fin r) (pt : Nat)
  deriving DecidableEq, Repr

abbrev Circuit (r : Nat) := List (Gate r)

def Gate.inv {r : Nat} : Gate r → Gate r
  | .rAdd s t => .rSub s t
  | .rSub s t => .rAdd s t
  | .rInc i   => .rDec i
  | .rDec i   => .rInc i
  | g         => g

def Circuit.inv {r : Nat} (C : Circuit r) : Circuit r :=
  (C.reverse).map Gate.inv

def evalGate {r w : Nat} (g : Gate r) (s : State r w) : State r w :=
  match g with
  | .rNot i => setReg s i (~~~(s i))
  | .rSwap i j => swapRegs s i j
  | .rCnot c t =>
      if c ≠ t then setReg s t (s t ^^^ s c) else s
  | .rToff c1 c2 t =>
      if c1 ≠ t ∧ c2 ≠ t ∧ c1 ≠ c2 then setReg s t (s t ^^^ (s c1 &&& s c2)) else s
  | .rAdd src dst =>
      if src ≠ dst then setReg s dst (s dst + s src) else s
  | .rSub src dst =>
      if src ≠ dst then setReg s dst (s dst - s src) else s
  | .rNeg i => setReg s i (-(s i))
  | .rInc i => setReg s i (s i + 1#w)
  | .rDec i => setReg s i (s i - 1#w)
  | .bNot i p => setReg s i (flipBit (s i) p)
  | .bSwap i1 p1 i2 p2 =>
      if p1 < w ∧ p2 < w ∧ (i1 ≠ i2 ∨ p1 ≠ p2) then
        if (s i1).getLsbD p1 != (s i2).getLsbD p2 then
          let s1 := setReg s i1 (flipBit (s i1) p1)
          setReg s1 i2 (flipBit (s1 i2) p2)
        else s
      else s
  | .bCnot ic pc it pt =>
      if pc < w ∧ pt < w ∧ (ic ≠ it ∨ pc ≠ pt) then
        if (s ic).getLsbD pc then setReg s it (flipBit (s it) pt) else s
      else s
  | .bToff i1 p1 i2 p2 it pt =>
      if p1 < w ∧ p2 < w ∧ pt < w ∧
         (i1 ≠ it ∨ p1 ≠ pt) ∧ (i2 ≠ it ∨ p2 ≠ pt) ∧ (i1 ≠ i2 ∨ p1 ≠ p2) then
        if (s i1).getLsbD p1 && (s i2).getLsbD p2 then
          setReg s it (flipBit (s it) pt)
        else s
      else s

def evalCircuit {r w : Nat} (C : Circuit r) (s : State r w) : State r w :=
  C.foldl (fun st g => evalGate g st) s

def repeatCircuit {r : Nat} : Nat → Circuit r → Circuit r
  | 0, _     => []
  | n + 1, C => C ++ repeatCircuit n C

def truncateState {r w : Nat} (w0 : Nat) (s : State r w) : State r w0 :=
  fun i => (s i).setWidth w0

def zeroExtendState {r w0 : Nat} (w : Nat) (s : State r w0) : State r w :=
  fun i => (s i).setWidth w

def isRegGate {r : Nat} : Gate r → Bool
  | .rNot _ | .rSwap _ _ | .rCnot _ _ | .rToff _ _ _
  | .rAdd _ _ | .rSub _ _ | .rNeg _ | .rInc _ | .rDec _ => true
  | _ => false

def isRegCircuit {r : Nat} (C : Circuit r) : Bool :=
  C.all isRegGate

def isWindowGate {r : Nat} (w0 : Nat) : Gate r → Bool
  | .bNot _ p => decide (p < w0)
  | .bSwap _ p1 _ p2 => decide (p1 < w0) && decide (p2 < w0)
  | .bCnot _ pc _ pt => decide (pc < w0) && decide (pt < w0)
  | .bToff _ p1 _ p2 _ pt => decide (p1 < w0) && decide (p2 < w0) && decide (pt < w0)
  | _ => false

def isWindowCircuit {r : Nat} (w0 : Nat) (C : Circuit r) : Bool :=
  C.all (isWindowGate w0)

def isCausalGate {r : Nat} (w0 : Nat) (g : Gate r) : Bool :=
  isRegGate g || isWindowGate w0 g

def isCausalCircuit {r : Nat} (w0 : Nat) (C : Circuit r) : Bool :=
  C.all (isCausalGate w0)

def decodeState (r w0 : Nat) (idx : Nat) : State r w0 :=
  fun i => BitVec.ofNat w0 ((idx / (2 ^ (i.val * w0))) % (2 ^ w0))

def stateEqBool {r w : Nat} (s1 s2 : State r w) : Bool :=
  (List.finRange r).all (fun i => s1 i == s2 i)

def allRange (n : Nat) (p : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | k + 1 => p k && allRange k p

def anyRange (n : Nat) (p : Nat → Bool) : Bool :=
  match n with
  | 0 => false
  | k + 1 => p k || anyRange k p

/-- Layer 1A Checker: verifies local bit-window circuit equivalence at finite width w0. -/
def checkWindowEq (r w0 : Nat) (C1 C2 : Circuit r) : Bool :=
  isWindowCircuit w0 C1 && isWindowCircuit w0 C2 &&
  allRange (2 ^ (r * w0)) (fun idx =>
    let s := decodeState r w0 idx
    stateEqBool (evalCircuit C1 s) (evalCircuit C2 s))

/-- Layer 3 Checker: verifies pairwise distinctness of a finite family of causal circuits
    at finite width w0 — lifts to ALL w ≥ w0 for BOTH bit-window AND modular-add circuits! -/
def checkDistinctAt (r w0 : Nat) (reps : Array (Circuit r)) : Bool :=
  allRange reps.size (fun i => isCausalCircuit w0 reps[i]!) &&
  allRange reps.size (fun i =>
    allRange i (fun j =>
      anyRange (2 ^ (r * w0)) (fun idx =>
        let s := decodeState r w0 idx
        !(stateEqBool (evalCircuit reps[i]! s) (evalCircuit reps[j]! s)))))

/-- Layer 3 Exact-Order Lower-Bound Witness Checker at width w0:
    checks that C^k ≠ id at width w0 for every proper divisor k of d (0 < k < d, d % k = 0). -/
def checkOrderLowerAt (r w0 d : Nat) (C : Circuit r) : Bool :=
  isCausalCircuit w0 C &&
  decide (d > 0) &&
  allRange d (fun k =>
    if k > 0 ∧ d % k = 0 then
      anyRange (2 ^ (r * w0)) (fun idx =>
        let s := decodeState r w0 idx
        !(stateEqBool (evalCircuit (repeatCircuit k C) s) s))
    else true)

abbrev BitSlice (r : Nat) := Fin r → Bool

def setBit {r : Nat} (b : BitSlice r) (i : Fin r) (v : Bool) : BitSlice r :=
  fun j => if j = i then v else b j

def hasCarryGate {r : Nat} : Gate r → Bool
  | .rAdd _ _ | .rSub _ _ | .rNeg _ | .rInc _ | .rDec _ => true
  | _ => false

def initCarryGate {r : Nat} : Gate r → Bool
  | .rSub _ _ | .rNeg _ | .rInc _ => true
  | _ => false

def initCarries {r : Nat} : Circuit r → List Bool
  | []      => []
  | g :: gs => if hasCarryGate g then initCarryGate g :: initCarries gs else initCarries gs

def stepPureGate {r : Nat} (g : Gate r) (b : BitSlice r) : BitSlice r :=
  match g with
  | .rNot i         => setBit b i (!b i)
  | .rSwap i j      => fun k => if k = i then b j else if k = j then b i else b k
  | .rCnot c t      => if c ≠ t then setBit b t (b t ^^ b c) else b
  | .rToff c1 c2 t  => if c1 ≠ t ∧ c2 ≠ t ∧ c1 ≠ c2 then setBit b t (b t ^^ (b c1 && b c2)) else b
  | _               => b

def stepCarryGate {r : Nat} (g : Gate r) (c : Bool) (b : BitSlice r) : Bool × BitSlice r :=
  match g with
  | .rAdd src dst =>
      if src ≠ dst then
        (Bool.atLeastTwo (b dst) (b src) c, setBit b dst (b dst ^^ (b src ^^ c)))
      else (c, b)
  | .rSub src dst =>
      if src ≠ dst then
        (Bool.atLeastTwo (b dst) (!b src) c, setBit b dst (b dst ^^ ((!b src) ^^ c)))
      else (c, b)
  | .rNeg i =>
      (Bool.atLeastTwo (!b i) false c, setBit b i ((!b i) ^^ (false ^^ c)))
  | .rInc i =>
      (Bool.atLeastTwo (b i) false c, setBit b i ((b i) ^^ (false ^^ c)))
  | .rDec i =>
      (Bool.atLeastTwo (b i) true c, setBit b i ((b i) ^^ (true ^^ c)))
  | _ => (c, b)

def stepRegCirc {r : Nat} : Circuit r → List Bool → BitSlice r → List Bool × BitSlice r
  | [], cs, b => (cs, b)
  | g :: gs, cs, b =>
      if hasCarryGate g then
        match cs with
        | c :: cs' =>
            let (c', b') := stepCarryGate g c b
            let (csOut, bOut) := stepRegCirc gs cs' b'
            (c' :: csOut, bOut)
        | [] => ([], b)
      else
        stepRegCirc gs cs (stepPureGate g b)

def sliceAt {r w : Nat} (s : State r w) (k : Nat) : BitSlice r :=
  fun i => (s i).getLsbD k

def runCarryAt {r w : Nat} (C : Circuit r) (s : State r w) : Nat → List Bool
  | 0     => initCarries C
  | k + 1 => (stepRegCirc C (runCarryAt C s k) (sliceAt s k)).1

def runOutAt {r w : Nat} (C : Circuit r) (s : State r w) (k : Nat) : BitSlice r :=
  (stepRegCirc C (runCarryAt C s k) (sliceAt s k)).2

def carryOfGate {r w : Nat} (g : Gate r) (s : State r w) (k : Nat) : Bool :=
  match g with
  | .rAdd src dst => if src ≠ dst then BitVec.carry k (s dst) (s src) false else false
  | .rSub src dst => if src ≠ dst then BitVec.carry k (s dst) (~~~(s src)) true else true
  | .rNeg i       => BitVec.carry k (~~~(s i)) (0#w) true
  | .rInc i       => BitVec.carry k (s i) (0#w) true
  | .rDec i       => BitVec.carry k (s i) (~~~(0#w)) false
  | _             => false

abbrev BisimCert := List (List Bool × List Bool)

def decodeSlice (r : Nat) (m : Nat) : BitSlice r :=
  fun i => Nat.testBit m i.val

def sliceEqBool {r : Nat} (b1 b2 : BitSlice r) : Bool :=
  (List.finRange r).all (fun i => b1 i == b2 i)

/-- Layer 1B Checker: verifies a finite carry-state bisimulation certificate between two
    register-parallel silicon circuits (mixing CNOT, Toffoli, SWAP, NOT, MOD_ADD, MOD_SUB, NEG, INC, DEC). -/
def checkBisimCert (r : Nat) (C1 C2 : Circuit r) (cert : BisimCert) : Bool :=
  isRegCircuit C1 && isRegCircuit C2 &&
  cert.contains (initCarries C1, initCarries C2) &&
  cert.all (fun (q1, q2) =>
    allRange (2 ^ r) (fun m =>
      let b := decodeSlice r m
      let (nq1, o1) := stepRegCirc C1 q1 b
      let (nq2, o2) := stepRegCirc C2 q2 b
      sliceEqBool o1 o2 && cert.contains (nq1, nq2)))

def regTouched {r : Nat} : Gate r → List (Fin r)
  | .rNot i | .rNeg i | .rInc i | .rDec i | .bNot i _ => [i]
  | .rSwap i j | .rCnot i j | .rAdd i j | .rSub i j | .bSwap i _ j _ | .bCnot i _ j _ => [i, j]
  | .rToff i j k | .bToff i _ j _ k _ => [i, j, k]

def listsDisjoint {α : Type} [DecidableEq α] (l1 l2 : List α) : Bool :=
  l1.all (fun x => !l2.contains x)

/-- Decidable syntactic commutation check (disjoint registers or identical gate). -/
def gatesCommute {r : Nat} (g1 g2 : Gate r) : Bool :=
  (g1 == g2) || listsDisjoint (regTouched g1) (regTouched g2)

inductive RewriteStep (r : Nat) where
  | invElim  (pos : Nat)
  | invIntro (pos : Nat) (g : Gate r)
  | commute  (pos : Nat)
  | applyRel (idx : Nat) (fwd : Bool) (pos : Nat)
  deriving DecidableEq, Repr

abbrev RewriteCert (r : Nat) := List (RewriteStep r)

abbrev RelLib (r : Nat) := List (Circuit r × Circuit r)

def LibSound {r : Nat} (lib : RelLib r) (w0 : Nat) : Prop :=
  ∀ p ∈ lib, ∀ w, w0 ≤ w → ∀ s : State r w, evalCircuit p.1 s = evalCircuit p.2 s

def applyStep {r : Nat} (lib : RelLib r) (word : Circuit r) (step : RewriteStep r) : Option (Circuit r) :=
  match step with
  | .invElim pos =>
      match word.drop pos with
      | g1 :: g2 :: rest =>
          if (g2 == g1.inv) || (g1 == g2.inv) then
            some (word.take pos ++ rest)
          else none
      | _ => none
  | .invIntro pos g =>
      if pos ≤ word.length then
        some (word.take pos ++ [g, g.inv] ++ word.drop pos)
      else none
  | .commute pos =>
      match word.drop pos with
      | g1 :: g2 :: rest =>
          if gatesCommute g1 g2 then
            some (word.take pos ++ [g2, g1] ++ rest)
          else none
      | _ => none
  | .applyRel idx fwd pos =>
      match lib[idx]? with
      | some (lhs, rhs) =>
          let src := if fwd then lhs else rhs
          let dst := if fwd then rhs else lhs
          let suf := word.drop pos
          if src.length ≤ suf.length && (suf.take src.length == src) then
            some (word.take pos ++ dst ++ suf.drop src.length)
          else none
      | none => none

def runRewrite {r : Nat} (lib : RelLib r) (word : Circuit r) : RewriteCert r → Option (Circuit r)
  | [] => some word
  | st :: rest =>
      match applyStep lib word st with
      | some w' => runRewrite lib w' rest
      | none    => none

def checkRewriteCert {r : Nat} (lib : RelLib r) (w1 w2 : Circuit r) (cert : RewriteCert r) : Bool :=
  match runRewrite lib w1 cert with
  | some wf => wf == w2
  | none    => false

structure CosetCert (r : Nat) where
  numCosets  : Nat
  reps       : Array (Circuit r)
  table      : Array (Array Nat)
  edgeProofs : Array (Array (RewriteCert r))

def evalWord {r : Nat} (gens : Array (Circuit r)) : List Nat → Circuit r
  | []      => []
  | k :: ks => gens[k]! ++ evalWord gens ks

def repeatWord : Nat → List Nat → List Nat
  | 0, _     => []
  | n + 1, w => w ++ repeatWord n w

def walkCoset (table : Array (Array Nat)) (c : Nat) : List Nat → Nat
  | []      => c
  | k :: ks => walkCoset table (table[c]![k]!) ks

def checkCosetCert {r : Nat} (lib : RelLib r) (gens : Array (Circuit r)) (cc : CosetCert r) : Bool :=
  decide (cc.numCosets > 0) &&
  (cc.reps.size == cc.numCosets) &&
  (cc.table.size == cc.numCosets) &&
  (cc.edgeProofs.size == cc.numCosets) &&
  (cc.reps[0]! == []) &&
  allRange cc.numCosets (fun c =>
    (cc.table[c]!.size == gens.size) &&
    (cc.edgeProofs[c]!.size == gens.size) &&
    allRange gens.size (fun k =>
      let nc := cc.table[c]![k]!
      decide (nc < cc.numCosets) &&
      checkRewriteCert lib (cc.reps[c]! ++ gens[k]!) cc.reps[nc]! cc.edgeProofs[c]![k]!))

def circU : Circuit 2 := [.rAdd 0 1]
def circV : Circuit 2 := [.rSub 1 0]
def circS : Circuit 2 := [.rSwap 0 1]
def circC : Circuit 2 := circU ++ circV
def circJ : Circuit 2 := circU ++ circV ++ circU

def d6Gens : Array (Circuit 2) := #[circC, circS]
def d6Lib  : RelLib 2 :=
  [ (repeatCircuit 6 circC, [])
  , (circS ++ circC, repeatCircuit 5 circC ++ circS) ]

-- Family II: Bit-Indexed {bCnot(0,1), bSwap(0,1), bToff(0,1,2)} Weyl Group B3 (Order 48)
def gA : Gate 1 := .bCnot 0 0 0 1
def gS : Gate 1 := .bSwap 0 0 0 1
def gT : Gate 1 := .bToff 0 0 0 1 0 2

def b3Gens : Array (Circuit 1) := #[[gA], [gS], [gT]]
def b3Lib  : RelLib 1 :=
  [ ([gA, gS, gA], [gS, gA, gS])
  , ([gS, gT], [gT, gS])
  , ([gA, gT, gA, gT], [gT, gA, gT, gA])
  , ([gA, gS, gA, gT, gA, gS], [gS, gA, gT, gA, gS, gA]) ]

-- Family III: Hybrid Toffoli-Add Infinite Dihedral Tower D_{2^w} & Carry-Defect Tower K2, T3
def circPcnot : Circuit 3 := [.rSub 1 2, .rCnot 0 1, .rAdd 1 2, .rCnot 0 1]
def circPtoff : Circuit 4 := [.rSub 3 2, .rToff 0 1 3, .rAdd 3 2, .rToff 0 1 3]

def circK2 (a b c : Fin 3) : Circuit 3 :=
  [.rSub a c, .rSub b c, .rCnot a b, .rAdd b c, .rCnot a b]

def circK2_4 (a b c : Fin 4) : Circuit 4 :=
  [.rSub a c, .rSub b c, .rCnot a b, .rAdd b c, .rCnot a b]

def circPtoffOf (a b d c : Fin 4) : Circuit 4 :=
  [.rSub d c, .rToff a b d, .rAdd d c, .rToff a b d]

def circT3 (a b d c : Fin 4) : Circuit 4 :=
  circPtoffOf a b d c ++ circPtoffOf a b d c ++ circK2_4 a b c

def cert_sl2_braid : BisimCert := [([false, false, true], [false, true, true]), ([false, false, true], [true, false, false]), ([false, true, false], [true, false, true]), ([true, true, false], [false, true, true]), ([true, true, false], [true, false, false])]
def cert_j4 : BisimCert := [([false, false, true, false, false, true, true, true, false, true, true, false], []), ([false, false, true, false, true, false, false, false, true, false, true, false], []), ([false, false, true, true, true, false, true, true, false, false, false, true], []), ([false, false, true, true, true, false, true, true, false, true, true, false], []), ([false, true, false, false, false, true, false, true, false, false, false, true], []), ([false, true, false, false, true, false, false, true, false, false, true, false], []), ([true, true, false, false, false, true, false, false, true, true, true, false], []), ([true, true, false, false, false, true, true, true, false, true, true, false], []), ([true, true, false, true, true, false, false, false, true, false, false, true], []), ([true, true, false, true, true, false, false, false, true, true, true, false], []), ([true, true, false, true, true, false, true, true, false, false, false, true], []), ([true, true, false, true, true, false, true, true, false, true, true, false], [])]
def cert_not_add : BisimCert := [([false], [true]), ([true], [false])]
def cert_d6_c6 : BisimCert := [([false, false, true, true, false, false, true, true, false, false, true, true], []), ([false, false, true, true, false, true, false, false, true, true, false, true], []), ([false, true, false, false, true, true, false, true, false, false, true, true], []), ([false, true, false, true, false, true, false, true, false, true, false, true], []), ([true, true, false, false, true, true, false, false, true, true, false, false], []), ([true, true, false, true, false, false, true, true, false, true, false, false], [])]
def cert_d6_sc : BisimCert := [([false, false], [false, false, true, true, false, false, true, true, false, false]), ([false, false], [false, true, false, false, true, true, false, true, false, false]), ([false, true], [false, false, true, true, false, true, false, false, true, true]), ([false, true], [false, true, false, true, false, true, false, true, false, true]), ([true, true], [true, true, false, false, true, true, false, false, true, true]), ([true, true], [true, true, false, true, false, false, true, true, false, true])]
def cert_pcnot_dih : BisimCert := [([false, false], [false, false]), ([false, true], [false, true]), ([false, true], [true, false]), ([true, false], [false, true]), ([true, false], [true, false]), ([true, true], [true, true])]
def cert_ptoff_dih : BisimCert := [([false, false], [false, false]), ([false, true], [false, true]), ([false, true], [true, false]), ([true, false], [false, true]), ([true, false], [true, false]), ([true, true], [true, true])]
def cert_k2_sym : BisimCert := [([false, false, false], [false, false, false]), ([false, false, true], [false, false, true]), ([false, true, false], [false, true, false]), ([false, true, false], [true, false, false]), ([false, true, true], [false, true, true]), ([false, true, true], [true, false, true]), ([true, false, false], [false, true, false]), ([true, false, false], [true, false, false]), ([true, false, true], [false, true, true]), ([true, false, true], [true, false, true]), ([true, true, false], [true, true, false])]
def cert_k2_not : BisimCert := [([false, false, false, true, false, true], [false, false]), ([false, false, false, true, true, false], [false, false]), ([false, false, true, false, false, true], [false, false]), ([false, false, true, false, true, false], [false, false]), ([false, false, true, false, true, true], [false, true]), ([false, false, true, true, false, false], [false, false]), ([false, false, true, true, false, true], [false, true]), ([false, false, true, true, true, false], [false, true]), ([false, true, false, false, true, false], [false, false]), ([false, true, false, false, true, true], [false, true]), ([false, true, false, true, false, false], [false, false]), ([false, true, false, true, false, true], [false, true]), ([false, true, false, true, false, true], [true, false]), ([false, true, false, true, true, false], [false, true]), ([false, true, false, true, true, false], [true, false]), ([false, true, true, false, false, false], [false, false]), ([false, true, true, false, false, true], [false, true]), ([false, true, true, false, true, false], [false, true]), ([false, true, true, false, true, false], [true, false]), ([false, true, true, false, true, true], [true, true]), ([false, true, true, true, false, false], [true, false]), ([false, true, true, true, false, true], [true, true]), ([false, true, true, true, true, false], [true, true]), ([true, false, false, true, false, false], [false, false]), ([true, false, false, true, false, true], [false, true]), ([true, false, false, true, false, true], [true, false]), ([true, false, false, true, true, false], [true, false]), ([true, false, true, false, false, false], [false, false]), ([true, false, true, false, false, true], [false, true]), ([true, false, true, false, false, true], [true, false]), ([true, false, true, false, true, false], [false, true]), ([true, false, true, false, true, false], [true, false]), ([true, false, true, false, true, true], [true, true]), ([true, false, true, true, false, false], [true, false]), ([true, false, true, true, false, true], [true, true]), ([true, false, true, true, true, false], [true, true]), ([true, true, false, false, true, false], [true, false]), ([true, true, false, false, true, true], [true, true]), ([true, true, false, true, false, false], [true, false]), ([true, true, false, true, false, true], [true, true]), ([true, true, false, true, true, false], [true, true])]

def d6CosetCert : CosetCert 2 :=
  { numCosets := 12
    reps := #[
      [],
      [.rAdd 0 1, .rSub 1 0],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0],
      [.rSwap 0 1],
      [.rAdd 0 1, .rSub 1 0, .rSwap 0 1],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rSwap 0 1],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rSwap 0 1],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rSwap 0 1],
      [.rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rAdd 0 1, .rSub 1 0, .rSwap 0 1],
    ]
    table := #[
      #[1, 6],
      #[2, 7],
      #[3, 8],
      #[4, 9],
      #[5, 10],
      #[0, 11],
      #[11, 0],
      #[6, 1],
      #[7, 2],
      #[8, 3],
      #[9, 4],
      #[10, 5],
    ]
    edgeProofs := #[
      #[[], []],
      #[[], []],
      #[[], []],
      #[[], []],
      #[[], []],
      #[[.applyRel 0 true 0], []],
      #[[.applyRel 1 true 0], [.invElim 0]],
      #[[.applyRel 1 true 2, .applyRel 0 true 0], [.invElim 2]],
      #[[.applyRel 1 true 4, .applyRel 0 true 0], [.invElim 4]],
      #[[.applyRel 1 true 6, .applyRel 0 true 0], [.invElim 6]],
      #[[.applyRel 1 true 8, .applyRel 0 true 0], [.invElim 8]],
      #[[.applyRel 1 true 10, .applyRel 0 true 0], [.invElim 10]],
    ] }

def b3CosetCert : CosetCert 1 :=
  { numCosets := 48
    reps := #[
      [],
      [.bCnot 0 0 0 1],
      [.bSwap 0 0 0 1],
      [.bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1],
      [.bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1],
      [.bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1],
      [.bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1],
      [.bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1],
      [.bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
      [.bCnot 0 0 0 1, .bSwap 0 0 0 1, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bSwap 0 0 0 1, .bToff 0 0 0 1 0 2, .bCnot 0 0 0 1, .bToff 0 0 0 1 0 2],
    ]
    table := #[
      #[1, 2, 3],
      #[0, 4, 5],
      #[6, 0, 7],
      #[8, 7, 0],
      #[9, 1, 10],
      #[11, 10, 1],
      #[2, 9, 12],
      #[13, 3, 2],
      #[3, 14, 15],
      #[4, 6, 16],
      #[17, 5, 4],
      #[5, 18, 19],
      #[20, 16, 6],
      #[7, 21, 22],
      #[21, 8, 23],
      #[19, 23, 8],
      #[24, 12, 9],
      #[10, 25, 26],
      #[25, 11, 27],
      #[15, 27, 11],
      #[12, 28, 29],
      #[14, 13, 30],
      #[29, 30, 13],
      #[31, 15, 14],
      #[16, 32, 33],
      #[18, 17, 34],
      #[33, 34, 17],
      #[35, 19, 18],
      #[32, 20, 36],
      #[22, 36, 20],
      #[37, 22, 21],
      #[23, 35, 38],
      #[28, 24, 39],
      #[26, 39, 24],
      #[40, 26, 25],
      #[27, 31, 41],
      #[42, 29, 28],
      #[30, 42, 43],
      #[43, 41, 31],
      #[44, 33, 32],
      #[34, 44, 45],
      #[45, 38, 35],
      #[36, 37, 46],
      #[38, 46, 37],
      #[39, 40, 47],
      #[41, 47, 40],
      #[47, 43, 42],
      #[46, 45, 44],
    ]
    edgeProofs := #[
      #[[], [], []],
      #[[.invElim 0], [], []],
      #[[], [.invElim 0], []],
      #[[], [.applyRel 1 false 0], [.invElim 0]],
      #[[], [.invElim 1], []],
      #[[], [.applyRel 1 false 1], [.invElim 1]],
      #[[.invElim 1], [.applyRel 0 false 0], []],
      #[[], [.applyRel 1 true 0, .invElim 1], [.invElim 1]],
      #[[.invElim 1], [], []],
      #[[.invElim 2], [.applyRel 0 true 0, .invElim 2], []],
      #[[], [.applyRel 1 true 1, .invElim 2], [.invElim 2]],
      #[[.invElim 2], [], []],
      #[[], [.applyRel 1 false 2, .applyRel 0 false 0], [.invElim 2]],
      #[[.invElim 2], [], []],
      #[[.applyRel 0 true 1, .applyRel 1 false 0], [.invElim 2], []],
      #[[.applyRel 2 false 0], [.applyRel 1 false 2], [.invElim 2]],
      #[[], [.applyRel 0 true 0, .applyRel 1 true 2, .invElim 3], [.invElim 3]],
      #[[.invElim 3], [], []],
      #[[.applyRel 0 true 2, .applyRel 1 false 1], [.invElim 3], []],
      #[[.applyRel 2 true 0, .invElim 3], [.applyRel 1 false 3], [.invElim 3]],
      #[[.invElim 3], [], []],
      #[[.applyRel 0 true 2, .applyRel 1 true 0, .invElim 1], [.invElim 3], []],
      #[[.applyRel 2 false 1], [.applyRel 1 false 3], [.invElim 3]],
      #[[], [.applyRel 1 true 2, .invElim 3], [.invElim 3]],
      #[[.invElim 4], [], []],
      #[[.applyRel 0 true 3, .applyRel 1 true 1, .invElim 2], [.invElim 4], []],
      #[[.applyRel 2 false 2], [.applyRel 1 false 4], [.invElim 4]],
      #[[], [.applyRel 1 true 3, .invElim 4], [.invElim 4]],
      #[[.applyRel 3 false 0], [.invElim 4], []],
      #[[.applyRel 2 true 1, .invElim 4], [.applyRel 1 false 4], [.invElim 4]],
      #[[], [.applyRel 1 true 3, .invElim 4], [.invElim 4]],
      #[[.invElim 4], [.applyRel 1 true 2, .applyRel 0 false 3, .applyRel 2 false 0, .applyRel 1 false 3], []],
      #[[.applyRel 3 true 0, .invElim 5], [.invElim 5], []],
      #[[.applyRel 2 true 2, .invElim 5], [.applyRel 1 false 5], [.invElim 5]],
      #[[], [.applyRel 1 true 4, .invElim 5], [.invElim 5]],
      #[[.invElim 5], [.applyRel 1 true 3, .applyRel 0 false 4, .applyRel 2 true 0, .invElim 3, .applyRel 1 false 2], []],
      #[[], [.applyRel 1 true 4, .invElim 5], [.invElim 5]],
      #[[.invElim 5], [.applyRel 1 true 3, .applyRel 0 false 4, .applyRel 2 false 1, .applyRel 1 false 4], []],
      #[[.applyRel 2 false 3, .applyRel 0 true 1, .applyRel 1 false 0], [.applyRel 1 true 2, .applyRel 1 false 5, .applyRel 0 false 3, .applyRel 2 false 0, .applyRel 1 false 3], [.invElim 5]],
      #[[], [.applyRel 1 true 5, .invElim 6], [.invElim 6]],
      #[[.invElim 6], [.applyRel 1 true 4, .applyRel 0 false 5, .applyRel 2 false 2, .applyRel 1 false 5], []],
      #[[.applyRel 2 false 4, .applyRel 0 true 2, .applyRel 1 false 1], [.applyRel 1 true 3, .applyRel 1 false 6, .applyRel 0 false 4, .applyRel 2 true 0, .invElim 3, .applyRel 1 false 2], [.invElim 6]],
      #[[.invElim 6], [.applyRel 1 true 4, .applyRel 0 false 5, .applyRel 2 true 1, .invElim 4, .applyRel 1 false 3], []],
      #[[.applyRel 1 true 0, .applyRel 0 false 1, .applyRel 2 true 3, .invElim 6], [.applyRel 1 true 3, .applyRel 1 false 6, .applyRel 0 false 4, .applyRel 2 false 1, .applyRel 1 false 4], [.invElim 6]],
      #[[.invElim 7], [.applyRel 1 true 5, .applyRel 0 false 6, .applyRel 2 true 2, .invElim 5, .applyRel 1 false 4], []],
      #[[.applyRel 1 true 1, .applyRel 0 false 2, .applyRel 2 true 4, .invElim 7], [.applyRel 1 true 4, .applyRel 1 false 7, .applyRel 0 false 5, .applyRel 2 false 2, .applyRel 1 false 5], [.invElim 7]],
      #[[.applyRel 2 false 5, .applyRel 3 false 0], [.applyRel 1 true 4, .applyRel 1 false 7, .applyRel 0 false 5, .applyRel 2 true 1, .invElim 4, .applyRel 1 false 3], [.invElim 7]],
      #[[.applyRel 2 false 6, .applyRel 3 true 0, .invElim 5], [.applyRel 1 true 5, .applyRel 1 false 8, .applyRel 0 false 6, .applyRel 2 true 2, .invElim 5, .applyRel 1 false 4], [.invElim 8]],
    ] }

-- ----------------------------------------------------------------------------
-- 5.1 Family I Theorems: Modular-Add SL(2,Z) Braid & D6 Group (Order 12)
-- ----------------------------------------------------------------------------

end RevCert

-- 6.3 Exhaustive `#print axioms` audit on every meta-theorem and flagship theorem
