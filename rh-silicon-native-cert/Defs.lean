/-
Trusted Minimal Definitions for `rh-silicon-native-cert` Palomar Bundle.
Strictly Init-only, zero transcendentals, zero continuum types, zero custom axioms.
Every definition below is pinned in `comparator.json` `definition_names`.
-/

namespace SiliconNativeCert

-- 1. Sound Integer Congruence Positivity (Engine 4)
def sumFin {n : Nat} (f : Fin n → Int) : Int :=
  (List.finRange n).foldl (fun acc i => acc + f i) 0

def quadForm {n : Nat} (G : Fin n → Fin n → Int) (v : Fin n → Int) : Int :=
  sumFin fun i => sumFin fun j => v i * G i j * v j

def rowAbsResidual {n : Nat} (G : Fin n → Fin n → Int) (S : Int) (i : Fin n) : Int :=
  sumFin fun j => Int.ofNat (G i j - if i = j then S else 0).natAbs

def IsStrictlyScaledDiagDom {n : Nat} (G : Fin n → Fin n → Int) (S : Int) : Prop :=
  0 < S ∧ ∀ i : Fin n, rowAbsResidual G S i < S

-- 2. Universal 4-State Binary Carry Transducers (Engine 2)
structure Transducer4 where
  outMask : UInt32
  nextPack : UInt32
  deriving DecidableEq, Repr

def Transducer4.idx (s : Nat) (a b : Bool) : Nat :=
  (s % 4) * 4 + (if a then 2 else 0) + (if b then 1 else 0)

def Transducer4.stepOut (t : Transducer4) (s : Nat) (a b : Bool) : Bool :=
  let i := Transducer4.idx s a b
  ((t.outMask.toNat >>> i) &&& 1) == 1

def Transducer4.stepNext (t : Transducer4) (s : Nat) (a b : Bool) : Nat :=
  let i := Transducer4.idx s a b
  (t.nextPack.toNat >>> (2 * i)) &&& 3

def Transducer4.evalFrom (t : Transducer4) : Nat → List (Bool × Bool) → List Bool
  | _, [] => []
  | s, (a, b) :: rest =>
    t.stepOut s a b :: t.evalFrom (t.stepNext s a b) rest

def Transducer4.eval (t : Transducer4) (inp : List (Bool × Bool)) : List Bool :=
  t.evalFrom 0 inp

def prodIdx (s1 s2 : Nat) : Nat :=
  (s1 % 4) * 4 + (s2 % 4)

def maskHas (invMask : UInt32) (s1 s2 : Nat) : Bool :=
  ((invMask.toNat >>> prodIdx s1 s2) &&& 1) == 1

def checkPairState (t1 t2 : Transducer4) (invMask : UInt32) (s1 s2 : Nat) : Bool :=
  if !maskHas invMask s1 s2 then
    true
  else
    [false, true].all fun a =>
      [false, true].all fun b =>
        (t1.stepOut s1 a b == t2.stepOut s2 a b) &&
        maskHas invMask (t1.stepNext s1 a b) (t2.stepNext s2 a b)

def checkPsyncInv4 (t1 t2 : Transducer4) (invMask : UInt32) : Bool :=
  maskHas invMask 0 0 &&
  (List.range 4).all fun s1 =>
    (List.range 4).all fun s2 =>
      checkPairState t1 t2 invMask s1 s2

def packTransducer4 (outFn : Nat → Bool → Bool → Bool) (nextFn : Nat → Bool → Bool → Nat) : Transducer4 :=
  let outNat := (List.range 4).foldl (fun acc s =>
    [false, true].foldl (fun acc2 a =>
      [false, true].foldl (fun acc3 b =>
        let i := Transducer4.idx s a b
        if outFn s a b then acc3 ||| (1 <<< i) else acc3) acc2) acc) 0
  let nextNat := (List.range 4).foldl (fun acc s =>
    [false, true].foldl (fun acc2 a =>
      [false, true].foldl (fun acc3 b =>
        let i := Transducer4.idx s a b
        let ns := nextFn s a b % 4
        acc3 ||| (ns <<< (2 * i))) acc2) acc) 0
  ⟨UInt32.ofNat outNat, UInt32.ofNat nextNat⟩

def tAdd : Transducer4 :=
  packTransducer4
    (fun s a b => ((s % 2) + (if a then 1 else 0) + (if b then 1 else 0)) % 2 == 1)
    (fun s a b => ((s % 2) + (if a then 1 else 0) + (if b then 1 else 0)) / 2)

def tXorPlusTwiceAnd : Transducer4 :=
  packTransducer4
    (fun s a b =>
      let prevAnd := s % 2
      let outerC := (s / 2) % 2
      let xorBit := if a != b then 1 else 0
      (xorBit + prevAnd + outerC) % 2 == 1)
    (fun s a b =>
      let prevAnd := s % 2
      let outerC := (s / 2) % 2
      let xorBit := if a != b then 1 else 0
      let curAnd := if a && b then 1 else 0
      let nextOuter := (xorBit + prevAnd + outerC) / 2
      curAnd + 2 * nextOuter)

-- 3. Universal Step-to-Target & Obstruction Targets (Engines 1 & 5)
def sqrtBit (w : Nat) : Nat :=
  2 ^ ((w + 1) / 2)

def SqrtScaleTarget (f : Nat → Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → ∃ C : Nat, ∀ w : Nat, 1 ≤ w →
    (f w) ^ (2 * k) ≤ C * (2 ^ w) ^ (k + 1)

-- 4. BIN-4 Carry-Split Factorization Graph (Engine 3)
def listProd : List Nat → Nat
  | [] => 1
  | d :: ds => d * listProd ds

def validFactorList (N : Nat) (xs : List Nat) : Bool :=
  xs.all (fun d => decide (2 ≤ d)) && decide (listProd xs ≤ N)

def listParity (xs : List Nat) : Bool :=
  xs.length % 2 == 1

def isSplitPair (a b d : Nat) : Bool :=
  decide (2 ≤ a) && decide (2 ≤ b) &&
    (decide (a * b = d) || (decide (d % 2 = 1) && decide (7 ≤ d) && decide (a = (d - 1) / 2) && decide (b = 2)))

def isOneStepSplit (xs ys : List Nat) : Prop :=
  ∃ pre suf d a b, xs = pre ++ d :: suf ∧ ys = pre ++ a :: b :: suf ∧ isSplitPair a b d = true

def isCarryMove (xs ys : List Nat) : Prop :=
  isOneStepSplit xs ys ∨ isOneStepSplit ys xs

end SiliconNativeCert
