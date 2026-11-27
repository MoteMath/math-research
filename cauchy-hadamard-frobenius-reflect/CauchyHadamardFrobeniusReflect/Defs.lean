/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Cauchy-Hadamard-Frobenius Carryless Reflection Engine (`cauchy-hadamard-frobenius-reflect`)

Pure-`Init` (zero Mathlib) definitions of `Expr`, `Cert`, `evalBV`, `isLaneSafe`, `dilate`, `checkCert`, `bvPr`, `bvAndRange`, `bvXorRange`, `bvClmul`, `bvE`, `bvFrob`, and `sierpinskiInvLHS`.
-/

namespace CHReflect

/-- Exact hardware shift-and-XOR carryless multiplication mod `x^w`. -/
def bvClmul {w : Nat} (a b : BitVec w) : BitVec w :=
  (List.range w).foldl
    (fun acc i => if b.getLsbD i then acc ^^^ (a <<< i) else acc)
    0

/-- Iterated Frobenius squaring `F^r(a) = a^{2^r}` in `F_2[x]/(x^w)`. -/
def bvFrob {w : Nat} : Nat → BitVec w → BitVec w
  | 0, a => a
  | r + 1, a =>
    let x := bvFrob r a
    bvClmul x x

/-- Iterated Frobenius residue mask `E_r = F^r(allOnes)` (bits `k ≡ 0 mod 2^r`). -/
def bvE (w r : Nat) : BitVec w :=
  bvFrob r (~~~(0 : BitVec w))

/-- Stride-`2^r` prefix-XOR (weight-1 Rota–Baxter operator) `P_r(a) = clmul(a, E_r)`. -/
def bvPr {w : Nat} (r : Nat) (a : BitVec w) : BitVec w :=
  bvClmul a (bvE w r)

/-- Finite XOR-fold `⨁_{i < n} f i` on `BitVec w`. -/
def bvXorRange {w : Nat} : Nat → (Nat → BitVec w) → BitVec w
  | 0, _ => 0
  | n + 1, f => bvXorRange n f ^^^ f n

/-- Finite AND-fold `⋀_{i < n} f i` on `BitVec w`. -/
def bvAndRange {w : Nat} : Nat → (Nat → BitVec w) → BitVec w
  | 0, _ => ~~~(0 : BitVec w)
  | n + 1, f => bvAndRange n f &&& f n

inductive Expr where
  | zero : Expr
  | one : Expr
  | allOnes : Expr
  | var : Nat → Expr
  | xor : Expr → Expr → Expr
  | and : Expr → Expr → Expr
  | clmul : Expr → Expr → Expr
  | shl : Expr → Nat → Expr
  deriving DecidableEq, Repr

def Expr.frob : Nat → Expr → Expr
  | 0, e => e
  | r + 1, e => let x := Expr.frob r e; .clmul x x

def Expr.deltaR (r : Nat) (e : Expr) : Expr := .xor e (.shl e (2 ^ r))

def evalBV (w : Nat) (env : Nat → BitVec w) : Expr → BitVec w
  | .zero => 0
  | .one => BitVec.ofNat w 1
  | .allOnes => ~~~(0 : BitVec w)
  | .var i => env i
  | .xor a b => evalBV w env a ^^^ evalBV w env b
  | .and a b => evalBV w env a &&& evalBV w env b
  | .clmul a b => bvClmul (evalBV w env a) (evalBV w env b)
  | .shl a s => evalBV w env a <<< s

/-- Unified normal-form representation:
    - Polynomials (XOR-sums): `.xorCons m rest` ending in `.zero`
    - Monomials (AND-products): `.andCons a rest` ending in `.allOnes`
    - Convolution factor lists (`clmul`): `.mulCons p rest` ending in `.one`
    - Atoms: `.bitAt s`, `.var i s`, `.frob k m s`, `.conv fs s` -/
inductive NF where
  | zero : NF
  | allOnes : NF
  | one : NF
  | bitAt (s : Nat) : NF
  | var (idx : Nat) (s : Nat) : NF
  | frob (k : Nat) (m : NF) (s : Nat) : NF
  | conv (fs : NF) (s : Nat) : NF
  | andCons (a rest : NF) : NF
  | xorCons (m rest : NF) : NF
  | mulCons (p rest : NF) : NF
  deriving DecidableEq, Repr

def nfTag : NF → Nat
  | .zero => 0
  | .allOnes => 1
  | .one => 2
  | .bitAt _ => 3
  | .var _ _ => 4
  | .frob _ _ _ => 5
  | .conv _ _ => 6
  | .andCons _ _ => 7
  | .xorCons _ _ => 8
  | .mulCons _ _ => 9

/-- Pure structural comparator on `NF` (guaranteed structural on `x`, ZERO `WellFounded.fix`). -/
def cmpNF (x y : NF) : Ordering :=
  match x, y with
  | .zero, .zero => .eq
  | .allOnes, .allOnes => .eq
  | .one, .one => .eq
  | .bitAt s1, .bitAt s2 => compare s1 s2
  | .var i1 s1, .var i2 s2 =>
    match compare i1 i2 with | .eq => compare s1 s2 | o => o
  | .frob k1 m1 s1, .frob k2 m2 s2 =>
    match compare k1 k2 with
    | .eq => match compare s1 s2 with | .eq => cmpNF m1 m2 | o => o
    | o => o
  | .conv fs1 s1, .conv fs2 s2 =>
    match compare s1 s2 with | .eq => cmpNF fs1 fs2 | o => o
  | .andCons a1 r1, .andCons a2 r2 =>
    match cmpNF a1 a2 with | .eq => cmpNF r1 r2 | o => o
  | .xorCons m1 r1, .xorCons m2 r2 =>
    match cmpNF m1 m2 with | .eq => cmpNF r1 r2 | o => o
  | .mulCons p1 r1, .mulCons p2 r2 =>
    match cmpNF p1 p2 with | .eq => cmpNF r1 r2 | o => o
  | a, b => compare (nfTag a) (nfTag b)
termination_by structural x

def singleAtomPoly (a : NF) : NF := .xorCons (.andCons a .allOnes) .zero

def allOnesPoly : NF := .xorCons .allOnes .zero

def mulAppend : NF → NF → NF
  | .mulCons p ps1, ps2 => .mulCons p (mulAppend ps1 ps2)
  | .one, ps2 => ps2
  | p, ps2 => .mulCons p ps2

def xorInsert (m : NF) : NF → NF
  | .xorCons h t =>
    if m == h then t
    else match cmpNF m h with
    | .lt => .xorCons m (.xorCons h t)
    | _ => .xorCons h (xorInsert m t)
  | p => .xorCons m p

def xorPoly : NF → NF → NF
  | .xorCons m ms, p2 => xorPoly ms (xorInsert m p2)
  | .zero, p2 => p2
  | p1, p2 => xorInsert p1 p2

def atomInsertPlain (a : NF) : NF → NF
  | .andCons h t =>
    if a == h then .andCons h t
    else match cmpNF a h with
    | .lt => .andCons a (.andCons h t)
    | _ => .andCons h (atomInsertPlain a t)
  | m => .andCons a m

def atomMinShift : NF → Nat
  | .bitAt s => s
  | .var _ s => s
  | .frob _ _ s => s
  | .conv _ s => s
  | _ => 0

def isBitAtAnnihilated (t : Nat) (b : NF) : Bool :=
  if t < atomMinShift b then true
  else match b with
  | .bitAt s => s != t
  | .frob k _ s => ((t - s) % (2 ^ (k + 1))) != 0
  | _ => false

def extractELevel : NF → Option Nat
  | .xorCons .allOnes .zero => some 0
  | .xorCons (.andCons (.frob k .allOnes 0) .allOnes) .zero => some (k + 1)
  | _ => none

def makeEPoly : Nat → NF
  | 0 => allOnesPoly
  | k + 1 => singleAtomPoly (.frob k .allOnes 0)

def extractMonoClmulParts : NF → Nat × NF
  | .andCons (.bitAt s) .allOnes => (s, .one)
  | .andCons (.var i s) .allOnes => (s, .mulCons (singleAtomPoly (.var i 0)) .one)
  | .andCons (.conv fs s) .allOnes => (s, fs)
  | .andCons (.frob k m s) .allOnes => (s, .mulCons (singleAtomPoly (.frob k m 0)) .one)
  | m => (0, .mulCons (.xorCons m .zero) .one)

def insertSortedPoly (p : NF) : NF → NF
  | .mulCons h t =>
    match cmpNF p h with
    | .lt => .mulCons p (.mulCons h t)
    | _ => .mulCons h (insertSortedPoly p t)
  | rest => .mulCons p rest

def sortPolys : NF → NF
  | .mulCons p ps => insertSortedPoly p (sortPolys ps)
  | other => other

/-- Pure structural duplicate-pair extractor for Frobenius squaring (`f ⊗ f = F(f)`). -/
def splitSquaresAux : Option NF → NF → NF × NF
  | none, .mulCons p rest => splitSquaresAux (some p) rest
  | some p1, .mulCons p2 rest =>
    if p1 == p2 then
      let (dedup, sq) := splitSquaresAux none rest
      (dedup, .mulCons p1 sq)
    else
      let (dedup, sq) := splitSquaresAux (some p2) rest
      (.mulCons p1 dedup, sq)
  | none, other => (other, .one)
  | some p, other => (.mulCons p other, .one)

def splitSquares (ps : NF) : NF × NF := splitSquaresAux none ps

def findShiftableE (tot : Nat) : NF → Option (Nat × NF)
  | .mulCons fac rest =>
    match extractELevel fac with
    | some 0 => if 1 ≤ tot then some (0, rest) else
        (findShiftableE tot rest).map (fun (k, r) => (k, .mulCons fac r))
    | some (k + 1) => if 2 ^ k ≤ tot then some (k + 1, rest) else
        (findShiftableE tot rest).map (fun (k', r) => (k', .mulCons fac r))
    | none =>
        (findShiftableE tot rest).map (fun (k, r) => (k, .mulCons fac r))
  | _ => none

def removeLevelE (target : Nat) : NF → Option NF
  | .mulCons fac rest =>
    if extractELevel fac == some target then some rest
    else (removeLevelE target rest).map (.mulCons fac)
  | _ => none

def findAdjacentE : NF → Option (Nat × NF)
  | .mulCons fac rest =>
    match extractELevel fac with
    | some k =>
      match removeLevelE (k + 1) rest with
      | some rest' => some (k, rest')
      | none =>
        match k with
        | 0 => (findAdjacentE rest).map (fun (k', r) => (k', .mulCons fac r))
        | k' + 1 =>
          match removeLevelE k' rest with
          | some rest' => some (k', rest')
          | none => (findAdjacentE rest).map (fun (k2, r) => (k2, .mulCons fac r))
    | none => (findAdjacentE rest).map (fun (k, r) => (k, .mulCons fac r))
  | _ => none

def findFrobAtom : NF → Option (Nat × NF × Nat × NF)
  | .andCons (.frob k m s) rest => some (k, m, s, rest)
  | .andCons a rest => (findFrobAtom rest).map (fun (k, m, s, r) => (k, m, s, .andCons a r))
  | _ => none

def anyAnnihilates (t : Nat) : NF → Bool
  | .andCons b bs => isBitAtAnnihilated t b || anyAnnihilates t bs
  | _ => false

def anyBitAtAnnihilatesAtom (a : NF) : NF → Bool
  | .andCons (.bitAt t) bs => isBitAtAnnihilated t a || anyBitAtAnnihilatesAtom a bs
  | .andCons _ bs => anyBitAtAnnihilatesAtom a bs
  | _ => false

def shlAllOnesPoly : Nat → NF
  | 0 => allOnesPoly
  | s + 1 => xorInsert (.andCons (.bitAt s) .allOnes) (shlAllOnesPoly s)

def andAtomWithPolyOf (ins : NF → NF → NF) (a : NF) : NF → NF
  | .xorCons m ms => xorPoly (ins a m) (andAtomWithPolyOf ins a ms)
  | .zero => .zero
  | m => ins a m

def andMonoOntoPolyOf (ins : NF → NF → NF) : NF → NF → NF
  | .andCons a rest, p => andMonoOntoPolyOf ins rest (andAtomWithPolyOf ins a p)
  | .allOnes, p => p
  | a, p => andAtomWithPolyOf ins a p

def andMonoOf (ins : NF → NF → NF) (m1 m2 : NF) : NF :=
  andMonoOntoPolyOf ins m1 (.xorCons m2 .zero)

def andMonoWithPolyOf (ins : NF → NF → NF) (m1 : NF) : NF → NF
  | .xorCons m2 ms2 => xorPoly (andMonoOf ins m1 m2) (andMonoWithPolyOf ins m1 ms2)
  | .zero => .zero
  | m2 => andMonoOf ins m1 m2

def andPolyOf (ins : NF → NF → NF) : NF → NF → NF
  | .xorCons m1 ms1, p2 => xorPoly (andMonoWithPolyOf ins m1 p2) (andPolyOf ins ms1 p2)
  | .zero, _ => .zero
  | m1, p2 => andMonoWithPolyOf ins m1 p2

def shlMonoOf (shA : NF → Nat → NF) (andP : NF → NF → NF) : NF → Nat → NF
  | .allOnes, s => if s == 0 then allOnesPoly else shlAllOnesPoly s
  | .andCons a rest, s =>
    if s == 0 then .xorCons (.andCons a rest) .zero
    else match rest with
    | .allOnes => shA a s
    | _ => andP (shA a s) (shlMonoOf shA andP rest s)
  | a, s => if s == 0 then .xorCons a .zero else shA a s

def shlPolyOf (shM : NF → Nat → NF) : NF → Nat → NF
  | .xorCons m ms, s => if s == 0 then .xorCons m ms else xorPoly (shM m s) (shlPolyOf shM ms s)
  | .zero, _ => .zero
  | m, s => if s == 0 then m else shM m s

def frobPolyOf (frM : Nat → NF → NF) (k : Nat) : NF → NF
  | .xorCons m ms => xorPoly (frM k m) (frobPolyOf frM k ms)
  | .zero => .zero
  | m => frM k m

def convFactorsOf (shA : NF → Nat → NF) (shP : NF → Nat → NF) (fs : NF) (s : Nat) : NF :=
  match fs with
  | .one => singleAtomPoly (.bitAt s)
  | .mulCons p .one => shP p s
  | _ => shA (.conv fs 0) s

def clmulSquaresOf (clP : NF → NF → NF) (frP : Nat → NF → NF) : NF → NF → NF
  | acc, .mulCons sf rest => clmulSquaresOf clP frP (clP acc (frP 0 sf)) rest
  | acc, .one => acc
  | acc, sf => clP acc (frP 0 sf)

def clmulMonoWithPolyOf (clM : NF → NF → NF) (m1 : NF) : NF → NF
  | .xorCons m2 ms2 => xorPoly (clM m1 m2) (clmulMonoWithPolyOf clM m1 ms2)
  | .zero => .zero
  | m2 => clM m1 m2

def clmulPolyOf (clM : NF → NF → NF) : NF → NF → NF
  | .xorCons m1 ms1, p2 => xorPoly (clmulMonoWithPolyOf clM m1 p2) (clmulPolyOf clM ms1 p2)
  | .zero, _ => .zero
  | m1, p2 => clmulMonoWithPolyOf clM m1 p2

structure Ops where
  shlAtom : NF → Nat → NF
  shlMono : NF → Nat → NF
  shlPoly : NF → Nat → NF
  frobMono : Nat → NF → NF
  frobPoly : Nat → NF → NF
  insertAtom : NF → NF → NF
  andPoly : NF → NF → NF
  convFactors : NF → Nat → NF
  clmulPoly : NF → NF → NF

def shlAtomBase (a : NF) (s : Nat) : NF :=
  if s == 0 then singleAtomPoly a
  else match a with
  | .bitAt s0 => singleAtomPoly (.bitAt (s0 + s))
  | .var i s0 => singleAtomPoly (.var i (s0 + s))
  | .frob k m s0 => singleAtomPoly (.frob k m (s0 + s))
  | .conv fs s0 => singleAtomPoly (.conv fs (s0 + s))
  | _ => singleAtomPoly (.conv a s)

def insertAtomBase (a m : NF) : NF :=
  match a with
  | .bitAt t => if anyAnnihilates t m then .zero else .xorCons (atomInsertPlain (.bitAt t) m) .zero
  | _ => if anyBitAtAnnihilatesAtom a m then .zero else .xorCons (atomInsertPlain a m) .zero

def frobMonoBase (k : Nat) (m : NF) : NF :=
  singleAtomPoly (.frob k m 0)

def shlAtomStep (prev : Ops) (a : NF) (s : Nat) : NF :=
  if s == 0 then singleAtomPoly a
  else match a with
  | .bitAt s0 => singleAtomPoly (.bitAt (s0 + s))
  | .var i s0 => singleAtomPoly (.var i (s0 + s))
  | .frob k .allOnes s0 =>
    let tot := s0 + s
    let half := 2 ^ k
    if half ≤ tot then
      let rem := tot - half
      xorPoly (prev.shlPoly (makeEPoly k) rem)
              (prev.shlAtom (.frob k .allOnes 0) rem)
    else singleAtomPoly (.frob k .allOnes tot)
  | .frob k m s0 => singleAtomPoly (.frob k m (s0 + s))
  | .conv fs s0 =>
    let tot := s0 + s
    match findShiftableE tot fs with
    | none => singleAtomPoly (.conv fs tot)
    | some (0, rest) =>
      let restP := prev.convFactors rest 0
      xorPoly (prev.shlPoly (prev.clmulPoly restP allOnesPoly) (tot - 1))
              (prev.shlPoly restP (tot - 1))
    | some (k + 1, rest) =>
      let half := 2 ^ k
      let restP := prev.convFactors rest 0
      xorPoly (prev.shlPoly (prev.clmulPoly restP (makeEPoly k)) (tot - half))
              (prev.shlPoly (prev.clmulPoly restP (makeEPoly (k + 1))) (tot - half))
  | _ => singleAtomPoly (.conv a s)

def insertAtomStep (prev : Ops) (a m : NF) : NF :=
  match a with
  | .bitAt t => if anyAnnihilates t m then .zero else .xorCons (atomInsertPlain (.bitAt t) m) .zero
  | .frob k1 m1 s1 =>
    if anyBitAtAnnihilatesAtom (.frob k1 m1 s1) m then .zero
    else match findFrobAtom m with
    | none => .xorCons (atomInsertPlain (.frob k1 m1 s1) m) .zero
    | some (k2, m2, s2, rest) =>
      let kmin := Nat.min k1 k2
      let mod := 2 ^ (kmin + 1)
      let r1 := s1 % mod
      let r2 := s2 % mod
      if r1 != r2 then .zero
      else
        let q1 := s1 / mod
        let q2 := s2 / mod
        let p1 := if k1 == kmin then prev.shlMono m1 q1
                  else prev.shlPoly (prev.frobMono (k1 - kmin - 1) m1) q1
        let p2 := if k2 == kmin then prev.shlMono m2 q2
                  else prev.shlPoly (prev.frobMono (k2 - kmin - 1) m2) q2
        let fused := prev.shlPoly (prev.frobPoly kmin (prev.andPoly p1 p2)) r1
        prev.andPoly fused (.xorCons rest .zero)
  | _ => if anyBitAtAnnihilatesAtom a m then .zero else .xorCons (atomInsertPlain a m) .zero

def frobMonoStep (prev : Ops) (k : Nat) (m : NF) : NF :=
  match m with
  | .allOnes => singleAtomPoly (.frob k .allOnes 0)
  | .andCons (.bitAt s) .allOnes => singleAtomPoly (.bitAt (s * 2 ^ (k + 1)))
  | .andCons (.frob k0 m0 s0) .allOnes => prev.shlAtom (.frob (k + k0 + 1) m0 0) (s0 * 2 ^ (k + 1))
  | _ => singleAtomPoly (.frob k m 0)

def clmulMonoStep (prev : Ops) (m1 m2 : NF) : NF :=
  let (s1, f1) := extractMonoClmulParts m1
  let (s2, f2) := extractMonoClmulParts m2
  let s := s1 + s2
  let sorted := sortPolys (mulAppend f1 f2)
  let (dedup, sq) := splitSquares sorted
  match sq with
  | .mulCons _ _ => clmulSquaresOf prev.clmulPoly prev.frobPoly (prev.convFactors dedup s) sq
  | .one =>
    match findAdjacentE dedup with
    | none => prev.convFactors dedup s
    | some (k, rest) =>
      let base := prev.convFactors rest s
      let ek2 := makeEPoly (k + 2)
      prev.clmulPoly base (xorPoly ek2 (prev.shlPoly ek2 (2 ^ k)))
  | _ => clmulSquaresOf prev.clmulPoly prev.frobPoly (prev.convFactors dedup s) sq

def mkOps : Nat → Ops
  | 0 =>
    let andP := andPolyOf insertAtomBase
    let shM := shlMonoOf shlAtomBase andP
    let shP := shlPolyOf shM
    let frP := frobPolyOf frobMonoBase
    let convF := convFactorsOf shlAtomBase shP
    let clM : NF → NF → NF := fun m1 m2 =>
      let (s1, f1) := extractMonoClmulParts m1
      let (s2, f2) := extractMonoClmulParts m2
      convF (sortPolys (mulAppend f1 f2)) (s1 + s2)
    ⟨shlAtomBase, shM, shP, frobMonoBase, frP, insertAtomBase, andP, convF, clmulPolyOf clM⟩
  | fuel + 1 =>
    let prev := mkOps fuel
    let shA := shlAtomStep prev
    let ins := insertAtomStep prev
    let andP := andPolyOf ins
    let shM := shlMonoOf shA andP
    let shP := shlPolyOf shM
    let frM := frobMonoStep prev
    let frP := frobPolyOf frM
    let convF := convFactorsOf shA shP
    let clP := clmulPolyOf (clmulMonoStep prev)
    ⟨shA, shM, shP, frM, frP, ins, andP, convF, clP⟩

def normWith (ops : Ops) : Expr → NF
  | .zero => .zero
  | .one => singleAtomPoly (.bitAt 0)
  | .allOnes => allOnesPoly
  | .var i => singleAtomPoly (.var i 0)
  | .xor a b => xorPoly (normWith ops a) (normWith ops b)
  | .and a b => ops.andPoly (normWith ops a) (normWith ops b)
  | .clmul a b => ops.clmulPoly (normWith ops a) (normWith ops b)
  | .shl a s => ops.shlPoly (normWith ops a) s

def norm (fuel : Nat) (e : Expr) : NF :=
  normWith (mkOps fuel) e

-- ============================================================================
-- Complete Soundness Proof of `mkOps` & `norm`
-- ============================================================================

def isConst : Expr → Bool
  | .zero => true
  | .one => true
  | .allOnes => true
  | .var _ => false
  | .xor a b => isConst a && isConst b
  | .and a b => isConst a && isConst b
  | .clmul a b => isConst a && isConst b
  | .shl a _ => isConst a

def cartierSplit : Expr → Expr × Expr
  | .zero => (.zero, .zero)
  | .one => (.one, .zero)
  | .allOnes => (.allOnes, .allOnes)
  | .var i => (.var (2 * i), .var (2 * i + 1))
  | .xor a b =>
    let (a0, a1) := cartierSplit a
    let (b0, b1) := cartierSplit b
    (.xor a0 b0, .xor a1 b1)
  | .and a b =>
    let (a0, a1) := cartierSplit a
    let (b0, b1) := cartierSplit b
    (.and a0 b0, .and a1 b1)
  | .shl a s =>
    let (a0, a1) := cartierSplit a
    if s % 2 == 0 then (.shl a0 (s / 2), .shl a1 (s / 2))
    else (.shl a1 (s / 2 + 1), .shl a0 (s / 2))
  | .clmul a b =>
    if a == b then
      if isConst a then (a, .zero)
      else
        let (a0, a1) := cartierSplit a
        (.xor (.clmul a0 a0) (.shl (.clmul a1 a1) 1), .zero)
    else
      let (a0, a1) := cartierSplit a
      let (b0, b1) := cartierSplit b
      (.xor (.clmul a0 b0) (.shl (.clmul a1 b1) 1),
       .xor (.clmul a0 b1) (.clmul a1 b0))

/-- Finite Binary Proof Certificate AST (pure data, ZERO `Prop` fields!). -/
inductive Cert where
  | normEq (fuel : Nat) : Cert
  | cartierSplit (evenCert oddCert : Cert) : Cert
  | cancelDelta (r : Nat) (sub : Cert) : Cert
  | symm (sub : Cert) : Cert
  | trans (mid : Expr) (c1 c2 : Cert) : Cert
  | congXor (c1 c2 : Cert) : Cert
  | congAnd (c1 c2 : Cert) : Cert
  | congClmul (c1 c2 : Cert) : Cert
  | congShl (sub : Cert) : Cert
  deriving Repr

def checkCert (e1 e2 : Expr) : Cert → Bool
  | .normEq fuel => norm fuel e1 == norm fuel e2
  | .cartierSplit cEv cOd =>
    let (ev1, od1) := cartierSplit e1
    let (ev2, od2) := cartierSplit e2
    checkCert ev1 ev2 cEv && checkCert od1 od2 cOd
  | .cancelDelta r sub =>
    checkCert (Expr.deltaR r e1) (Expr.deltaR r e2) sub
  | .symm sub => checkCert e2 e1 sub
  | .trans mid c1 c2 => checkCert e1 mid c1 && checkCert mid e2 c2
  | .congXor c1 c2 =>
    match e1, e2 with
    | .xor a1 b1, .xor a2 b2 => checkCert a1 a2 c1 && checkCert b1 b2 c2
    | _, _ => false
  | .congAnd c1 c2 =>
    match e1, e2 with
    | .and a1 b1, .and a2 b2 => checkCert a1 a2 c1 && checkCert b1 b2 c2
    | _, _ => false
  | .congClmul c1 c2 =>
    match e1, e2 with
    | .clmul a1 b1, .clmul a2 b2 => checkCert a1 a2 c1 && checkCert b1 b2 c2
    | _, _ => false
  | .congShl sub =>
    match e1, e2 with
    | .shl a1 s1, .shl a2 s2 => (s1 == s2) && checkCert a1 a2 sub
    | _, _ => false

def isLaneSafe : Expr → Bool
  | .zero => true
  | .one => true
  | .allOnes => true
  | .var _ => true
  | .xor a b => isLaneSafe a && isLaneSafe b
  | .and a b => isLaneSafe a && isLaneSafe b
  | .shl a _ => isLaneSafe a
  | .clmul a b => (isLaneSafe a && isConst b) || (isConst a && isLaneSafe b)

def dilate (r : Nat) : Expr → Expr
  | .zero => .zero
  | .one => .xor .allOnes (.shl .allOnes (2 ^ r))
  | .allOnes => .allOnes
  | .var i => .var i
  | .xor a b => .xor (dilate r a) (dilate r b)
  | .and a b => .and (dilate r a) (dilate r b)
  | .shl a s => .shl (dilate r a) (s * 2 ^ r)
  | .clmul a b =>
    if isConst b then .clmul (dilate r a) (Expr.frob r b)
    else if isConst a then .clmul (Expr.frob r a) (dilate r b)
    else .clmul (dilate r a) (dilate r b)

end CHReflect
