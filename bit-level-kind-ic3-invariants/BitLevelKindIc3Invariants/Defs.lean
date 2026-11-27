/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Bit-Level k-Induction & IC3 Invariant Certificate Engine (`bit-level-kind-ic3-invariants`)

Pure-`Init` (zero Mathlib) definitions of `BVSystem`, `BVPred`, `NatSet`, `KIndIC3Cert`, `checkOblig`, `checkKIndIC3`, `runTrace`, `Safe`, and the five hardware traces (`grayTrace`, `csaTrace`, `defectPipeTrace`, `hybridTrace`, `avgFilterTrace`).
-/

namespace KIndIC3

inductive NatSet where
  | empty : NatSet
  | node  : Nat → NatSet → NatSet → NatSet
deriving Repr, DecidableEq

def NatSet.mem : NatSet → Nat → Bool
  | .empty, _ => false
  | .node v l r, x =>
    if x == v then true
    else if x < v then l.mem x
    else r.mem x

def NatSet.all (p : Nat → Bool) : NatSet → Bool
  | .empty => true
  | .node v l r => p v && l.all p && r.all p

def allRange (n : Nat) (p : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | k + 1 => p k && allRange k p

inductive BVExpr (r m : Nat) where
  | zero    : BVExpr r m
  | one     : BVExpr r m
  | allOnes : BVExpr r m
  | reg     : Fin r → BVExpr r m
  | inp     : Fin m → BVExpr r m
  | not     : BVExpr r m → BVExpr r m
  | and     : BVExpr r m → BVExpr r m → BVExpr r m
  | or      : BVExpr r m → BVExpr r m → BVExpr r m
  | xor     : BVExpr r m → BVExpr r m → BVExpr r m
  | add     : BVExpr r m → BVExpr r m → BVExpr r m
  | sub     : BVExpr r m → BVExpr r m → BVExpr r m
  | shl1    : BVExpr r m → BVExpr r m
  | shr1    : BVExpr r m → BVExpr r m
deriving Repr, DecidableEq

inductive BVPred (r m : Nat) where
  | pTrue  : BVPred r m
  | pFalse : BVPred r m
  | eq     : BVExpr r m → BVExpr r m → BVPred r m
  | ule    : BVExpr r m → BVExpr r m → BVPred r m
  | ult    : BVExpr r m → BVExpr r m → BVPred r m
  | lsbEq  : BVExpr r m → Bool → BVPred r m
  | msbEq  : BVExpr r m → Bool → BVPred r m
  | pNot   : BVPred r m → BVPred r m
  | pAnd   : BVPred r m → BVPred r m → BVPred r m
  | pOr    : BVPred r m → BVPred r m → BVPred r m
  | pImp   : BVPred r m → BVPred r m → BVPred r m
deriving Repr, DecidableEq

def evalExpr {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) :
    BVExpr r m → BitVec w
  | .zero      => 0#w
  | .one       => 1#w
  | .allOnes   => BitVec.allOnes w
  | .reg i     => regs i
  | .inp j     => inps j
  | .not e     => ~~~(evalExpr regs inps e)
  | .and e1 e2 => evalExpr regs inps e1 &&& evalExpr regs inps e2
  | .or e1 e2  => evalExpr regs inps e1 ||| evalExpr regs inps e2
  | .xor e1 e2 => evalExpr regs inps e1 ^^^ evalExpr regs inps e2
  | .add e1 e2 => evalExpr regs inps e1 + evalExpr regs inps e2
  | .sub e1 e2 => evalExpr regs inps e1 - evalExpr regs inps e2
  | .shl1 e    => evalExpr regs inps e <<< 1
  | .shr1 e    => evalExpr regs inps e >>> 1

def evalPred {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) :
    BVPred r m → Bool
  | .pTrue      => true
  | .pFalse     => false
  | .eq e1 e2   => decide (evalExpr regs inps e1 = evalExpr regs inps e2)
  | .ule e1 e2  => decide (evalExpr regs inps e1 ≤ evalExpr regs inps e2)
  | .ult e1 e2  => decide (evalExpr regs inps e1 < evalExpr regs inps e2)
  | .lsbEq e b  => decide ((evalExpr regs inps e).getLsbD 0 = b)
  | .msbEq e b  => decide ((evalExpr regs inps e).msb = b)
  | .pNot p     => !(evalPred regs inps p)
  | .pAnd p1 p2 => evalPred regs inps p1 && evalPred regs inps p2
  | .pOr p1 p2  => evalPred regs inps p1 || evalPred regs inps p2
  | .pImp p1 p2 => !(evalPred regs inps p1) || evalPred regs inps p2

structure BVSystem (r m : Nat) where
  init : BVPred r 0
  next : Fin r → BVExpr r m

def runTrace {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (inputs : Nat → Fin m → BitVec w) :
    Nat → (Fin r → BitVec w)
  | 0     => s0
  | t + 1 => fun i => evalExpr (runTrace sys s0 inputs t) (inputs t) (sys.next i)

def Safe {r m : Nat} (sys : BVSystem r m) (prop : BVPred r 0) : Prop :=
  ∀ (w : Nat), w ≥ 1 →
  ∀ (s0 : Fin r → BitVec w) (inputs : Nat → Fin m → BitVec w),
    evalPred s0 Fin.elim0 sys.init = true →
    ∀ (t : Nat), evalPred (runTrace sys s0 inputs t) Fin.elim0 prop = true

-- ============================================================================
-- Section 4: Bit-Slice Automaton Compiler (Exact Bit-Packed Nat Codes)
-- ============================================================================

def exprBits {r m : Nat} : BVExpr r m → Nat
  | .zero      => 0
  | .one       => 1
  | .allOnes   => 0
  | .reg _     => 0
  | .inp _     => 0
  | .not e     => exprBits e
  | .and e1 e2 => exprBits e1 + exprBits e2
  | .or e1 e2  => exprBits e1 + exprBits e2
  | .xor e1 e2 => exprBits e1 + exprBits e2
  | .add e1 e2 => exprBits e1 + exprBits e2 + 1
  | .sub e1 e2 => exprBits e1 + exprBits e2 + 1
  | .shl1 e    => exprBits e + 1
  | .shr1 e    => exprBits e + 2

def exprGuesses {r m : Nat} : BVExpr r m → Nat
  | .zero      => 0
  | .one       => 0
  | .allOnes   => 0
  | .reg _     => 0
  | .inp _     => 0
  | .not e     => exprGuesses e
  | .and e1 e2 => exprGuesses e1 + exprGuesses e2
  | .or e1 e2  => exprGuesses e1 + exprGuesses e2
  | .xor e1 e2 => exprGuesses e1 + exprGuesses e2
  | .add e1 e2 => exprGuesses e1 + exprGuesses e2
  | .sub e1 e2 => exprGuesses e1 + exprGuesses e2
  | .shl1 e    => exprGuesses e
  | .shr1 e    => exprGuesses e + 1

def exprInitCode {r m : Nat} : BVExpr r m → Nat
  | .zero      => 0
  | .one       => 1
  | .allOnes   => 0
  | .reg _     => 0
  | .inp _     => 0
  | .not e     => exprInitCode e
  | .and e1 e2 => exprInitCode e1 + exprInitCode e2 * 2 ^ exprBits e1
  | .or e1 e2  => exprInitCode e1 + exprInitCode e2 * 2 ^ exprBits e1
  | .xor e1 e2 => exprInitCode e1 + exprInitCode e2 * 2 ^ exprBits e1
  | .add e1 e2 => exprInitCode e1 + exprInitCode e2 * 2 ^ exprBits e1
  | .sub e1 e2 => exprInitCode e1 + exprInitCode e2 * 2 ^ exprBits e1
  | .shl1 e    => exprInitCode e
  | .shr1 e    => exprInitCode e

def stepExprCode {r m : Nat} (rBits uBits : Nat) :
    BVExpr r m → Nat → Nat → (Nat × Bool × Bool)
  | .zero, _, _    => (0, true, false)
  | .one, code, _  => (0, true, code % 2 == 1)
  | .allOnes, _, _ => (0, true, true)
  | .reg i, _, _   => (0, true, (rBits / 2 ^ i.val) % 2 == 1)
  | .inp j, _, _   => (0, true, (uBits / 2 ^ j.val) % 2 == 1)
  | .not e, code, gm =>
    let (c1, v1, b1) := stepExprCode rBits uBits e code gm
    (c1, v1, !b1)
  | .and e1 e2, code, gm =>
    let k1 := exprBits e1; let g1 := exprGuesses e1
    let (c1, v1, b1) := stepExprCode rBits uBits e1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let (c2, v2, b2) := stepExprCode rBits uBits e2 (code / 2 ^ k1) (gm / 2 ^ g1)
    (c1 + c2 * 2 ^ k1, v1 && v2, b1 && b2)
  | .or e1 e2, code, gm =>
    let k1 := exprBits e1; let g1 := exprGuesses e1
    let (c1, v1, b1) := stepExprCode rBits uBits e1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let (c2, v2, b2) := stepExprCode rBits uBits e2 (code / 2 ^ k1) (gm / 2 ^ g1)
    (c1 + c2 * 2 ^ k1, v1 && v2, b1 || b2)
  | .xor e1 e2, code, gm =>
    let k1 := exprBits e1; let g1 := exprGuesses e1
    let (c1, v1, b1) := stepExprCode rBits uBits e1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let (c2, v2, b2) := stepExprCode rBits uBits e2 (code / 2 ^ k1) (gm / 2 ^ g1)
    (c1 + c2 * 2 ^ k1, v1 && v2, b1 != b2)
  | .add e1 e2, code, gm =>
    let k1 := exprBits e1; let k2 := exprBits e2; let g1 := exprGuesses e1
    let (c1, v1, b1) := stepExprCode rBits uBits e1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let rest := code / 2 ^ k1
    let (c2, v2, b2) := stepExprCode rBits uBits e2 (rest % 2 ^ k2) (gm / 2 ^ g1)
    let cin := (rest / 2 ^ k2) % 2 == 1
    let out := (b1 != b2) != cin
    let cout := (b1 && b2) || (cin && (b1 != b2))
    (c1 + (c2 + cout.toNat * 2 ^ k2) * 2 ^ k1, v1 && v2, out)
  | .sub e1 e2, code, gm =>
    let k1 := exprBits e1; let k2 := exprBits e2; let g1 := exprGuesses e1
    let (c1, v1, b1) := stepExprCode rBits uBits e1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let rest := code / 2 ^ k1
    let (c2, v2, b2) := stepExprCode rBits uBits e2 (rest % 2 ^ k2) (gm / 2 ^ g1)
    let brw := (rest / 2 ^ k2) % 2 == 1
    let out := (b1 != b2) != brw
    let brwNext := (!b1 && b2) || (!b1 && brw) || (b2 && brw)
    (c1 + (c2 + brwNext.toNat * 2 ^ k2) * 2 ^ k1, v1 && v2, out)
  | .shl1 e, code, gm =>
    let k1 := exprBits e
    let (c1, v1, b1) := stepExprCode rBits uBits e (code % 2 ^ k1) gm
    let prev := (code / 2 ^ k1) % 2 == 1
    (c1 + b1.toNat * 2 ^ k1, v1, prev)
  | .shr1 e, code, gm =>
    let k1 := exprBits e; let g1 := exprGuesses e
    let (c1, v1, b1) := stepExprCode rBits uBits e (code % 2 ^ k1) (gm % 2 ^ g1)
    let expCode := (code / 2 ^ k1) % 4
    let ok :=
      if expCode == 0 then true
      else if expCode == 1 then !b1
      else if expCode == 2 then b1
      else false
    let guessBit := (gm / 2 ^ g1) % 2 == 1
    let nextExp := if guessBit then 2 else 1
    (c1 + nextExp * 2 ^ k1, v1 && ok, guessBit)

def exprFinalValid {r m : Nat} : BVExpr r m → Nat → Bool
  | .zero, _    => true
  | .one, _     => true
  | .allOnes, _ => true
  | .reg _, _   => true
  | .inp _, _   => true
  | .not e, code => exprFinalValid e code
  | .and e1 e2, code | .or e1 e2, code | .xor e1 e2, code =>
    let k1 := exprBits e1
    exprFinalValid e1 (code % 2 ^ k1) && exprFinalValid e2 (code / 2 ^ k1)
  | .add e1 e2, code | .sub e1 e2, code =>
    let k1 := exprBits e1; let k2 := exprBits e2
    let rest := code / 2 ^ k1
    exprFinalValid e1 (code % 2 ^ k1) && exprFinalValid e2 (rest % 2 ^ k2)
  | .shl1 e, code =>
    exprFinalValid e (code % 2 ^ exprBits e)
  | .shr1 e, code =>
    let k1 := exprBits e
    exprFinalValid e (code % 2 ^ k1) && ((code / 2 ^ k1) % 4 == 1)

def predBits {r m : Nat} : BVPred r m → Nat
  | .pTrue      => 0
  | .pFalse     => 0
  | .eq e1 e2   => exprBits e1 + exprBits e2 + 1
  | .ule e1 e2  => exprBits e1 + exprBits e2 + 1
  | .ult e1 e2  => exprBits e1 + exprBits e2 + 1
  | .lsbEq e _  => exprBits e + 2
  | .msbEq e _  => exprBits e + 1
  | .pNot p     => predBits p
  | .pAnd p1 p2 => predBits p1 + predBits p2
  | .pOr p1 p2  => predBits p1 + predBits p2
  | .pImp p1 p2 => predBits p1 + predBits p2

def predGuesses {r m : Nat} : BVPred r m → Nat
  | .pTrue      => 0
  | .pFalse     => 0
  | .eq e1 e2   => exprGuesses e1 + exprGuesses e2
  | .ule e1 e2  => exprGuesses e1 + exprGuesses e2
  | .ult e1 e2  => exprGuesses e1 + exprGuesses e2
  | .lsbEq e _  => exprGuesses e
  | .msbEq e _  => exprGuesses e
  | .pNot p     => predGuesses p
  | .pAnd p1 p2 => predGuesses p1 + predGuesses p2
  | .pOr p1 p2  => predGuesses p1 + predGuesses p2
  | .pImp p1 p2 => predGuesses p1 + predGuesses p2

def predInitCode {r m : Nat} : BVPred r m → Nat
  | .pTrue      => 0
  | .pFalse     => 0
  | .eq e1 e2   =>
    let k1 := exprBits e1; let k2 := exprBits e2
    exprInitCode e1 + (exprInitCode e2 + 1 * 2 ^ k2) * 2 ^ k1
  | .ule e1 e2  =>
    let k1 := exprBits e1
    exprInitCode e1 + exprInitCode e2 * 2 ^ k1
  | .ult e1 e2  =>
    let k1 := exprBits e1; let k2 := exprBits e2
    exprInitCode e1 + (exprInitCode e2 + 1 * 2 ^ k2) * 2 ^ k1
  | .lsbEq e _  => exprInitCode e
  | .msbEq e _  => exprInitCode e
  | .pNot p     => predInitCode p
  | .pAnd p1 p2 => predInitCode p1 + predInitCode p2 * 2 ^ predBits p1
  | .pOr p1 p2  => predInitCode p1 + predInitCode p2 * 2 ^ predBits p1
  | .pImp p1 p2 => predInitCode p1 + predInitCode p2 * 2 ^ predBits p1

def stepPredCode {r m : Nat} (rBits uBits : Nat) :
    BVPred r m → Nat → Nat → (Nat × Bool)
  | .pTrue, _, _  => (0, true)
  | .pFalse, _, _ => (0, true)
  | .eq e1 e2, code, gm =>
    let k1 := exprBits e1; let k2 := exprBits e2; let g1 := exprGuesses e1
    let (c1, v1, b1) := stepExprCode rBits uBits e1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let rest := code / 2 ^ k1
    let (c2, v2, b2) := stepExprCode rBits uBits e2 (rest % 2 ^ k2) (gm / 2 ^ g1)
    let ok := (rest / 2 ^ k2) % 2 == 1
    let okNext := ok && (b1 == b2)
    (c1 + (c2 + okNext.toNat * 2 ^ k2) * 2 ^ k1, v1 && v2)
  | .ule e1 e2, code, gm | .ult e1 e2, code, gm =>
    let k1 := exprBits e1; let k2 := exprBits e2; let g1 := exprGuesses e1
    let (c1, v1, b1) := stepExprCode rBits uBits e1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let rest := code / 2 ^ k1
    let (c2, v2, b2) := stepExprCode rBits uBits e2 (rest % 2 ^ k2) (gm / 2 ^ g1)
    let brw := (rest / 2 ^ k2) % 2 == 1
    let brwNext := (!b2 && b1) || (!b2 && brw) || (b1 && brw)
    (c1 + (c2 + brwNext.toNat * 2 ^ k2) * 2 ^ k1, v1 && v2)
  | .lsbEq e target, code, gm =>
    let k1 := exprBits e
    let (c1, v1, b1) := stepExprCode rBits uBits e (code % 2 ^ k1) gm
    let st := (code / 2 ^ k1) % 4
    let stNext := if st == 0 then (if b1 == target then 2 else 1) else st
    (c1 + stNext * 2 ^ k1, v1)
  | .msbEq e _, code, gm =>
    let k1 := exprBits e
    let (c1, v1, b1) := stepExprCode rBits uBits e (code % 2 ^ k1) gm
    (c1 + b1.toNat * 2 ^ k1, v1)
  | .pNot p, code, gm => stepPredCode rBits uBits p code gm
  | .pAnd p1 p2, code, gm | .pOr p1 p2, code, gm | .pImp p1 p2, code, gm =>
    let k1 := predBits p1; let g1 := predGuesses p1
    let (c1, v1) := stepPredCode rBits uBits p1 (code % 2 ^ k1) (gm % 2 ^ g1)
    let (c2, v2) := stepPredCode rBits uBits p2 (code / 2 ^ k1) (gm / 2 ^ g1)
    (c1 + c2 * 2 ^ k1, v1 && v2)

def predFinalValid {r m : Nat} : BVPred r m → Nat → Bool
  | .pTrue, _  => true
  | .pFalse, _ => true
  | .eq e1 e2, code | .ule e1 e2, code | .ult e1 e2, code =>
    let k1 := exprBits e1; let k2 := exprBits e2
    let rest := code / 2 ^ k1
    exprFinalValid e1 (code % 2 ^ k1) && exprFinalValid e2 (rest % 2 ^ k2)
  | .lsbEq e _, code | .msbEq e _, code =>
    exprFinalValid e (code % 2 ^ exprBits e)
  | .pNot p, code => predFinalValid p code
  | .pAnd p1 p2, code | .pOr p1 p2, code | .pImp p1 p2, code =>
    let k1 := predBits p1
    predFinalValid p1 (code % 2 ^ k1) && predFinalValid p2 (code / 2 ^ k1)

def predAccept {r m : Nat} : BVPred r m → Nat → Bool
  | .pTrue, _  => true
  | .pFalse, _ => false
  | .eq e1 e2, code =>
    let k1 := exprBits e1; let k2 := exprBits e2
    ((code / 2 ^ k1) / 2 ^ k2) % 2 == 1
  | .ule e1 e2, code | .ult e1 e2, code =>
    let k1 := exprBits e1; let k2 := exprBits e2
    ((code / 2 ^ k1) / 2 ^ k2) % 2 == 0
  | .lsbEq e _, code =>
    (code / 2 ^ exprBits e) % 4 == 2
  | .msbEq e target, code =>
    ((code / 2 ^ exprBits e) % 2 == 1) == target
  | .pNot p, code => !predAccept p code
  | .pAnd p1 p2, code =>
    let k1 := predBits p1
    predAccept p1 (code % 2 ^ k1) && predAccept p2 (code / 2 ^ k1)
  | .pOr p1 p2, code =>
    let k1 := predBits p1
    predAccept p1 (code % 2 ^ k1) || predAccept p2 (code / 2 ^ k1)
  | .pImp p1 p2, code =>
    let k1 := predBits p1
    (!predAccept p1 (code % 2 ^ k1)) || predAccept p2 (code / 2 ^ k1)

def predAliveHyp {r m : Nat} : BVPred r m → Nat → Bool
  | .pFalse, _ => false
  | .eq e1 e2, code =>
    let k1 := exprBits e1; let k2 := exprBits e2
    ((code / 2 ^ k1) / 2 ^ k2) % 2 == 1
  | .lsbEq e _, code =>
    (code / 2 ^ exprBits e) % 4 != 1
  | .pAnd p1 p2, code =>
    let k1 := predBits p1
    predAliveHyp p1 (code % 2 ^ k1) && predAliveHyp p2 (code / 2 ^ k1)
  | _, _ => true

-- ============================================================================
-- Section 5: Canonical Bit-Slice Simulation Lemmas (Soundness Core)
-- ============================================================================

def nextBits {r m : Nat} (next : Fin r → BVExpr r m) : (n : Nat) → n ≤ r → Nat
  | 0, _ => 0
  | n + 1, hn => nextBits next n (Nat.le_of_succ_le hn) + exprBits (next ⟨n, hn⟩)

def nextGuesses {r m : Nat} (next : Fin r → BVExpr r m) : (n : Nat) → n ≤ r → Nat
  | 0, _ => 0
  | n + 1, hn => nextGuesses next n (Nat.le_of_succ_le hn) + exprGuesses (next ⟨n, hn⟩)

def nextInitCode {r m : Nat} (next : Fin r → BVExpr r m) : (n : Nat) → n ≤ r → Nat
  | 0, _ => 0
  | n + 1, hn =>
    let k := nextBits next n (Nat.le_of_succ_le hn)
    nextInitCode next n (Nat.le_of_succ_le hn) + exprInitCode (next ⟨n, hn⟩) * 2 ^ k

def stepNextCode {r m : Nat} (next : Fin r → BVExpr r m) (rBits uBits : Nat) :
    (n : Nat) → n ≤ r → Nat → Nat → (Nat × Bool × Nat)
  | 0, _, _, _ => (0, true, 0)
  | n + 1, hn, code, gm =>
    let hn' := Nat.le_of_succ_le hn
    let k := nextBits next n hn'
    let g := nextGuesses next n hn'
    let (c1, v1, out1) := stepNextCode next rBits uBits n hn' (code % 2 ^ k) (gm % 2 ^ g)
    let (c2, v2, b2)   := stepExprCode rBits uBits (next ⟨n, hn⟩) (code / 2 ^ k) (gm / 2 ^ g)
    (c1 + c2 * 2 ^ k, v1 && v2, out1 + b2.toNat * 2 ^ n)

def nextFinalValid {r m : Nat} (next : Fin r → BVExpr r m) : (n : Nat) → n ≤ r → Nat → Bool
  | 0, _, _ => true
  | n + 1, hn, code =>
    let hn' := Nat.le_of_succ_le hn
    let k := nextBits next n hn'
    nextFinalValid next n hn' (code % 2 ^ k) && exprFinalValid (next ⟨n, hn⟩) (code / 2 ^ k)

def obGuesses {r m : Nat} (sys : BVSystem r m) :
    (steps : Nat) → (Fin (steps + 1) → BVPred r 0) → BVPred r 0 → Nat
  | 0, hyps, conc => predGuesses (hyps ⟨0, Nat.zero_lt_succ 0⟩) + predGuesses conc
  | s + 1, hyps, conc =>
    nextGuesses sys.next r (Nat.le_refl r) +
    predGuesses (hyps ⟨0, Nat.zero_lt_succ _⟩) +
    obGuesses sys s (fun j => hyps j.succ) conc

def obInitCode {r m : Nat} (sys : BVSystem r m) :
    (steps : Nat) → (Fin (steps + 1) → BVPred r 0) → BVPred r 0 → Nat
  | 0, hyps, conc =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ 0⟩
    predInitCode h0 + predInitCode conc * 2 ^ predBits h0
  | s + 1, hyps, conc =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ _⟩
    let kn := nextBits sys.next r (Nat.le_refl r)
    let kh := predBits h0
    let cRest := obInitCode sys s (fun j => hyps j.succ) conc
    nextInitCode sys.next r (Nat.le_refl r) +
      (predInitCode h0 + cRest * 2 ^ kh) * 2 ^ kn

def obStepCode {r m : Nat} (sys : BVSystem r m) :
    (steps : Nat) → (Fin (steps + 1) → BVPred r 0) → BVPred r 0 →
    Nat → Nat → Nat → Nat → Option Nat
  | 0, hyps, conc, rBits, _, code, gm =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ 0⟩
    let kh := predBits h0; let gh := predGuesses h0
    let (hc, hv) := stepPredCode rBits 0 h0 (code % 2 ^ kh) (gm % 2 ^ gh)
    if !hv || !predAliveHyp h0 hc then none
    else
      let (cc, cv) := stepPredCode rBits 0 conc (code / 2 ^ kh) (gm / 2 ^ gh)
      if !cv then none
      else some (hc + cc * 2 ^ kh)
  | s + 1, hyps, conc, rBits, uMask, code, gm =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ _⟩
    let kn := nextBits sys.next r (Nat.le_refl r)
    let gn := nextGuesses sys.next r (Nat.le_refl r)
    let kh := predBits h0; let gh := predGuesses h0
    let u0 := uMask % 2 ^ m
    let (nc, nv, rNext) := stepNextCode sys.next rBits u0 r (Nat.le_refl r) (code % 2 ^ kn) (gm % 2 ^ gn)
    if !nv then none
    else
      let restC := code / 2 ^ kn; let restG := gm / 2 ^ gn
      let (hc, hv) := stepPredCode rBits 0 h0 (restC % 2 ^ kh) (restG % 2 ^ gh)
      if !hv || !predAliveHyp h0 hc then none
      else
        match obStepCode sys s (fun j => hyps j.succ) conc rNext (uMask / 2 ^ m)
                (restC / 2 ^ kh) (restG / 2 ^ gh) with
        | none => none
        | some rc => some (nc + (hc + rc * 2 ^ kh) * 2 ^ kn)

def obIsBadAccept {r m : Nat} (sys : BVSystem r m) :
    (steps : Nat) → (Fin (steps + 1) → BVPred r 0) → BVPred r 0 → Nat → Bool
  | 0, hyps, conc, code =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ 0⟩
    let kh := predBits h0
    let hc := code % 2 ^ kh
    let cc := code / 2 ^ kh
    predFinalValid h0 hc && predAccept h0 hc && predFinalValid conc cc && (!predAccept conc cc)
  | s + 1, hyps, conc, code =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ _⟩
    let kn := nextBits sys.next r (Nat.le_refl r)
    let kh := predBits h0
    let nc := code % 2 ^ kn
    let rest := code / 2 ^ kn
    let hc := rest % 2 ^ kh
    let rc := rest / 2 ^ kh
    nextFinalValid sys.next r (Nat.le_refl r) nc &&
      predFinalValid h0 hc && predAccept h0 hc &&
      obIsBadAccept sys s (fun j => hyps j.succ) conc rc

def checkStepFrom {r m : Nat} (sys : BVSystem r m) (steps : Nat)
    (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0)
    (cert : NatSet) (code : Nat) : Bool :=
  let nR := 2 ^ r
  let nU := 2 ^ (steps * m)
  let nG := 2 ^ obGuesses sys steps hyps conc
  allRange nR fun rBits =>
    allRange nU fun uMask =>
      allRange nG fun gm =>
        match obStepCode sys steps hyps conc rBits uMask code gm with
        | none => true
        | some nxt => cert.mem nxt

def checkOblig {r m : Nat} (sys : BVSystem r m) (steps : Nat)
    (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0)
    (cert : NatSet) : Bool :=
  let init := obInitCode sys steps hyps conc
  -- 1. Bit-0 initiation (every alive successor after 1 bit-slice is in cert)
  checkStepFrom sys steps hyps conc cert init &&
  -- 2. Bit-slice closure (every alive successor of every cert state is in cert)
  cert.all (checkStepFrom sys steps hyps conc cert) &&
  -- 3. Disjointness from bad-accepting states
  cert.all (fun c => !obIsBadAccept sys steps hyps conc c)

def foldAnd {r : Nat} : List (BVPred r 0) → BVPred r 0
  | [] => .pTrue
  | [p] => p
  | p :: ps => .pAnd p (foldAnd ps)

structure KIndIC3Cert (r : Nat) where
  k           : Nat               -- induction depth (k ≥ 1)
  invClauses  : List (BVPred r 0) -- IC3 strengthening invariant clauses (empty => pure k-induction on prop)
  baseCerts   : List NatSet       -- k certificates for Base_0 .. Base_{k-1}
  stepCert    : NatSet            -- certificate for k-step Consecution
  safetyCert  : NatSet            -- certificate for Safety Entailment (Inv → Prop)
deriving Repr

def baseHyps {r : Nat} (init : BVPred r 0) (j : Nat) : Fin (j + 1) → BVPred r 0 :=
  fun idx => if idx.val == 0 then init else .pTrue

def stepHyps {r : Nat} (inv : BVPred r 0) (k : Nat) : Fin (k + 1) → BVPred r 0 :=
  fun idx => if idx.val < k then inv else .pTrue

def safetyHyps {r : Nat} (inv : BVPred r 0) : Fin 1 → BVPred r 0 :=
  fun _ => inv

def checkBases {r m : Nat} (sys : BVSystem r m) (inv : BVPred r 0) :
    Nat → List NatSet → Bool
  | _, [] => true
  | j, c :: cs =>
    checkOblig sys j (baseHyps sys.init j) inv c && checkBases sys inv (j + 1) cs

def checkKIndIC3 {r m : Nat} (sys : BVSystem r m) (prop : BVPred r 0)
    (cert : KIndIC3Cert r) : Bool :=
  let inv := if cert.invClauses.isEmpty then prop else foldAnd cert.invClauses
  (cert.k ≥ 1) &&
  (cert.baseCerts.length == cert.k) &&
  checkBases sys inv 0 cert.baseCerts &&
  checkOblig sys cert.k (stepHyps inv cert.k) inv cert.stepCert &&
  checkOblig sys 0 (safetyHyps inv) prop cert.safetyCert

def grayTrace (w : Nat) : Nat → BitVec w × BitVec w
  | 0 => (0#w, 0#w)
  | t + 1 =>
    let (x, g) := grayTrace w t
    let d := x ^^^ (x + 1#w)
    (x + 1#w, g ^^^ (d ^^^ (d >>> 1)))

def csaTrace {w : Nat} (u : Nat → BitVec w) : Nat → BitVec w × BitVec w × BitVec w
  | 0 => (0#w, 0#w, 0#w)
  | t + 1 =>
    let (S, C, A) := csaTrace u t
    let ut := u t
    ((S ^^^ C) ^^^ ut,
     ((S &&& C) ||| ((S &&& ut) ||| (C &&& ut))) <<< 1,
     A + ut)

def defectPipeTrace (w : Nat) : Nat → BitVec w × BitVec w × BitVec w
  | 0 => (0#w, 0#w, 0#w)
  | t + 1 =>
    let (p, a, b) := defectPipeTrace w t
    let q := (p + (p <<< 1)) + (b ^^^ 1#w)
    (q &&& ~~~(q <<< 1),
     (p + (p <<< 1)) ^^^ (p ^^^ (p <<< 1)),
     b + a)

def hybridTrace {w : Nat} (u : Nat → BitVec w) : Nat → BitVec w × BitVec w × BitVec w
  | 0 => (0#w, 0#w, 0#w)
  | t + 1 =>
    let (p, x, y) := hybridTrace u t
    let xu := x ^^^ u t
    (xu &&& ~~~(xu <<< 1),
     x + (p ^^^ (p <<< 1)),
     y + (p + (p <<< 1)))

def avgFilterTrace {w : Nat} (u : Nat → BitVec w) : Nat → BitVec w × BitVec w
  | 0 => (0#w, 0#w)
  | t + 1 =>
    let (L, M) := avgFilterTrace u t
    let ut := u t
    ((L >>> 1) + (ut >>> 1),
     (M &&& ut) + ((M ^^^ ut) >>> 1))

end KIndIC3
