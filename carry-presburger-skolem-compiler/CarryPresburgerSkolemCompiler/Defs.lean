/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`CarryPresburgerSkolemCompiler`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace CPRTE
/-! ## Section 1: Pure-Silicon Bitwise, Popcount, and Exact Carry-Count Primitives -/

def popcountFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n == 0 then 0 else n % 2 + popcountFuel fuel (n / 2)

def popcount (n : Nat) : Nat := popcountFuel n n

def carryCountFuel : Nat → Nat → Nat → Bool → Nat
  | 0, _, _, _ => 0
  | fuel + 1, a, b, cin =>
    if a == 0 && b == 0 then 0
    else
      let s := a % 2 + b % 2 + cin.toNat
      let cout := decide (s ≥ 2)
      cout.toNat + carryCountFuel fuel (a / 2) (b / 2) cout

def carryCount (a b : Nat) (cin : Bool) : Nat := carryCountFuel (a + b) a b cin

/-! ## Section 2: 4-Way Pointwise Bitwise Relations (`bitRel4`) -/

def bitIdx4 (b1 b2 b3 b4 : Bool) : Nat :=
  8 * b1.toNat + 4 * b2.toNat + 2 * b3.toNat + b4.toNat

def bitRel4Fuel : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0, mask, _, _, _, _ => Nat.testBit mask 0
  | fuel + 1, mask, v1, v2, v3, v4 =>
    if v1 == 0 && v2 == 0 && v3 == 0 && v4 == 0 then
      Nat.testBit mask 0
    else
      let idx := bitIdx4 (decide (v1 % 2 = 1)) (decide (v2 % 2 = 1))
                         (decide (v3 % 2 = 1)) (decide (v4 % 2 = 1))
      Nat.testBit mask idx && bitRel4Fuel fuel mask (v1 / 2) (v2 / 2) (v3 / 2) (v4 / 2)

def bitRel4Dec (mask v1 v2 v3 v4 : Nat) : Bool :=
  bitRel4Fuel (v1 + v2 + v3 + v4) mask v1 v2 v3 v4

/-! ## Section 3: Affine Terms, Dot Products, and Bit-Peeling Algebra -/

def vecStep : List Nat → List Bool → List Nat
  | v :: vs, b :: bs => (2 * v + b.toNat) :: vecStep vs bs
  | _, _ => []

def vecSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + vecSum xs

def vecDiv2 : List Nat → List Nat
  | [] => []
  | x :: xs => (x / 2) :: vecDiv2 xs

def vecMod2Bits : List Nat → List Bool
  | [] => []
  | x :: xs => (decide (x % 2 = 1)) :: vecMod2Bits xs

def dotNat : List Nat → List Nat → Nat
  | c :: cs, v :: vs => c * v + dotNat cs vs
  | _, _ => 0

def dotNatBool : List Nat → List Bool → Nat
  | c :: cs, b :: bs => c * b.toNat + dotNatBool cs bs
  | _, _ => 0

def dotInt : List Int → List Nat → Int
  | c :: cs, v :: vs => c * (v : Int) + dotInt cs vs
  | _, _ => 0

def dotIntBool : List Int → List Bool → Int
  | c :: cs, b :: bs => c * (b.toNat : Int) + dotIntBool cs bs
  | _, _ => 0

/-! ## Section 4: Carry-Presburger Syntax, Semantics, Exact Derivative, and Entailment -/

structure NatAff where
  coeffs : List Nat
  carry  : Nat
  deriving BEq, DecidableEq, Repr

structure IntAff where
  coeffs : List Int
  rhs    : Int
  deriving BEq, DecidableEq, Repr

def eqNatAff (a b : NatAff) : Bool := a.carry == b.carry && a.coeffs == b.coeffs
def eqIntAff (a b : IntAff) : Bool := a.rhs == b.rhs && a.coeffs == b.coeffs

def NatAff.eval (t : NatAff) (v : List Nat) : Nat :=
  dotNat t.coeffs v + t.carry

def NatAff.step (t : NatAff) (bs : List Bool) : Bool × NatAff :=
  let s := dotNatBool t.coeffs bs + t.carry
  (decide (s % 2 = 1), { coeffs := t.coeffs, carry := s / 2 })

inductive Atom where
  | linLe   (t : IntAff)
  | linEq   (t : IntAff)
  | modEq   (coeffs : List Int) (m : Nat) (r : Nat)
  | bitRel4 (mask : Nat) (t1 t2 t3 t4 : NatAff)
  | carryLe (t1 t2 : NatAff) (cin : Bool) (k : Nat)
  | popMod  (terms : List (Int × NatAff)) (m : Nat) (r : Nat)
  deriving DecidableEq, Repr

def eqPopTerms : List (Int × NatAff) → List (Int × NatAff) → Bool
  | [], [] => true
  | (w1, t1) :: r1, (w2, t2) :: r2 => w1 == w2 && eqNatAff t1 t2 && eqPopTerms r1 r2
  | _, _ => false

def eqAtom : Atom → Atom → Bool
  | .linLe t1, .linLe t2 => eqIntAff t1 t2
  | .linEq t1, .linEq t2 => eqIntAff t1 t2
  | .modEq c1 m1 r1, .modEq c2 m2 r2 => r1 == r2 && m1 == m2 && c1 == c2
  | .bitRel4 m1 a1 b1 c1 d1, .bitRel4 m2 a2 b2 c2 d2 =>
      m1 == m2 && eqNatAff a1 a2 && eqNatAff b1 b2 && eqNatAff c1 c2 && eqNatAff d1 d2
  | .carryLe a1 b1 c1 k1, .carryLe a2 b2 c2 k2 =>
      k1 == k2 && c1 == c2 && eqNatAff a1 a2 && eqNatAff b1 b2
  | .popMod t1 m1 r1, .popMod t2 m2 r2 => r1 == r2 && m1 == m2 && eqPopTerms t1 t2
  | _, _ => false

inductive Formula where
  | tt
  | ff
  | atom (a : Atom)
  | not  (f : Formula)
  | and  (f1 f2 : Formula)
  | or   (f1 f2 : Formula)
  deriving DecidableEq, Repr

def eqFormula : Formula → Formula → Bool
  | .tt, .tt => true
  | .ff, .ff => true
  | .atom a1, .atom a2 => eqAtom a1 a2
  | .not f1, .not f2 => eqFormula f1 f2
  | .and a1 b1, .and a2 b2 => eqFormula a1 a2 && eqFormula b1 b2
  | .or a1 b1, .or a2 b2 => eqFormula a1 a2 && eqFormula b1 b2
  | _, _ => false

def evalPopSum : List (Int × NatAff) → List Nat → Int
  | [], _ => 0
  | (w, t) :: rest, v => w * (popcount (t.eval v) : Int) + evalPopSum rest v

def evalAtomBool (a : Atom) (v : List Nat) : Bool :=
  match a with
  | .linLe t => decide (dotInt t.coeffs v ≤ t.rhs)
  | .linEq t => decide (dotInt t.coeffs v = t.rhs)
  | .modEq cs m r =>
      if m == 0 then true
      else decide (dotInt cs v % (m : Int) = ((r % m : Nat) : Int))
  | .bitRel4 mask t1 t2 t3 t4 =>
      bitRel4Dec mask (t1.eval v) (t2.eval v) (t3.eval v) (t4.eval v)
  | .carryLe t1 t2 cin k =>
      decide (carryCount (t1.eval v) (t2.eval v) cin ≤ k)
  | .popMod terms m r =>
      if m == 0 then true
      else decide (evalPopSum terms v % (m : Int) = ((r % m : Nat) : Int))

def evalFormulaBool (f : Formula) (v : List Nat) : Bool :=
  match f with
  | .tt => true
  | .ff => false
  | .atom a => evalAtomBool a v
  | .not f1 => !(evalFormulaBool f1 v)
  | .and f1 f2 => evalFormulaBool f1 v && evalFormulaBool f2 v
  | .or f1 f2 => evalFormulaBool f1 v || evalFormulaBool f2 v

/-! ### Smart Formula Constructors -/

def mkNot : Formula → Formula
  | .tt => .ff
  | .ff => .tt
  | .not f => f
  | f => .not f

def mkAnd : Formula → Formula → Formula
  | .ff, _ => .ff
  | _, .ff => .ff
  | .tt, f => f
  | f, .tt => f
  | f1, f2 => if eqFormula f1 f2 then f1 else .and f1 f2

def mkOr : Formula → Formula → Formula
  | .tt, _ => .tt
  | _, .tt => .tt
  | .ff, f => f
  | f, .ff => f
  | f1, f2 => if eqFormula f1 f2 then f1 else .or f1 f2

def bigOr : List Formula → Formula
  | [] => .ff
  | [f] => f
  | f :: fs => mkOr f (bigOr fs)

/-! ### Atom Simplification and Exact LSB-First Carry-Residue Derivative -/

def simpAtom (a : Atom) : Formula :=
  match a with
  | .linLe t =>
      if t.coeffs.all (fun c => decide (c ≤ 0)) && decide (0 ≤ t.rhs) then .tt
      else if t.coeffs.all (fun c => decide (0 ≤ c)) && decide (t.rhs < 0) then .ff
      else .atom (.linLe t)
  | .linEq t =>
      if t.coeffs.all (fun c => c == 0) then
        if t.rhs == 0 then .tt else .ff
      else if t.coeffs.all (fun c => decide (0 ≤ c)) && decide (t.rhs < 0) then .ff
      else if t.coeffs.all (fun c => decide (c ≤ 0)) && decide (0 < t.rhs) then .ff
      else .atom (.linEq t)
  | .modEq cs m r =>
      if m ≤ 1 then .tt
      else .atom (.modEq cs m (r % m))
  | .bitRel4 mask t1 t2 t3 t4 =>
      if t1.coeffs.all (fun c => c == 0) && t2.coeffs.all (fun c => c == 0) &&
         t3.coeffs.all (fun c => c == 0) && t4.coeffs.all (fun c => c == 0) then
        if bitRel4Dec mask t1.carry t2.carry t3.carry t4.carry then .tt else .ff
      else .atom (.bitRel4 mask t1 t2 t3 t4)
  | .carryLe t1 t2 cin k =>
      if t1.coeffs.all (fun c => c == 0) && t2.coeffs.all (fun c => c == 0) then
        if carryCount t1.carry t2.carry cin ≤ k then .tt else .ff
      else .atom (.carryLe t1 t2 cin k)
  | .popMod terms m r =>
      if m ≤ 1 then .tt
      else .atom (.popMod terms m (r % m))

def stepPopTerms (terms : List (Int × NatAff)) (bs : List Bool) :
    Int × List (Int × NatAff) :=
  match terms with
  | [] => (0, [])
  | (w, t) :: rest =>
    let (bit, t') := t.step bs
    let (delta, rest') := stepPopTerms rest bs
    (w * (bit.toNat : Int) + delta, (w, t') :: rest')

def stepAtom (a : Atom) (bs : List Bool) : Formula :=
  match a with
  | .linLe t =>
      let s := dotIntBool t.coeffs bs
      simpAtom (.linLe { coeffs := t.coeffs, rhs := (t.rhs - s) / 2 })
  | .linEq t =>
      let s := dotIntBool t.coeffs bs
      let d := t.rhs - s
      if d % 2 == 0 then
        simpAtom (.linEq { coeffs := t.coeffs, rhs := d / 2 })
      else .ff
  | .modEq cs m r =>
      if m ≤ 1 then .tt
      else
        let s := dotIntBool cs bs
        let v := (r : Int) - s
        if m % 2 == 0 then
          if v % 2 == 0 then
            let m' := m / 2
            let r' := ((v / 2) % (m' : Int)).toNat
            simpAtom (.modEq cs m' r')
          else .ff
        else
          let inv2 : Int := (((m + 1) / 2 : Nat) : Int)
          let r' := ((inv2 * v) % (m : Int)).toNat
          simpAtom (.modEq cs m r')
  | .bitRel4 mask t1 t2 t3 t4 =>
      let (b1, t1') := t1.step bs
      let (b2, t2') := t2.step bs
      let (b3, t3') := t3.step bs
      let (b4, t4') := t4.step bs
      if Nat.testBit mask (bitIdx4 b1 b2 b3 b4) then
        simpAtom (.bitRel4 mask t1' t2' t3' t4')
      else .ff
  | .carryLe t1 t2 cin k =>
      let (b1, t1') := t1.step bs
      let (b2, t2') := t2.step bs
      let bitSum := b1.toNat + b2.toNat + cin.toNat
      let cout := decide (bitSum ≥ 2)
      if cout then
        if k == 0 then .ff
        else simpAtom (.carryLe t1' t2' true (k - 1))
      else
        simpAtom (.carryLe t1' t2' false k)
  | .popMod terms m r =>
      if m ≤ 1 then .tt
      else
        let (delta, terms') := stepPopTerms terms bs
        let r' := (((r : Int) - delta) % (m : Int)).toNat
        simpAtom (.popMod terms' m r')

def stepFormula (f : Formula) (bs : List Bool) : Formula :=
  match f with
  | .tt => .tt
  | .ff => .ff
  | .atom a => stepAtom a bs
  | .not f1 => mkNot (stepFormula f1 bs)
  | .and f1 f2 => mkAnd (stepFormula f1 bs) (stepFormula f2 bs)
  | .or f1 f2 => mkOr (stepFormula f1 bs) (stepFormula f2 bs)

/-! ### Sound Syntactic Entailment Checker (`entails`) -/

def entailsAtom : Atom → Atom → Bool
  | .linLe t1, .linLe t2 => t1.coeffs == t2.coeffs && decide (t1.rhs ≤ t2.rhs)
  | .linEq t1, .linLe t2 => t1.coeffs == t2.coeffs && decide (t1.rhs ≤ t2.rhs)
  | .linEq t1, .modEq c2 m2 r2 =>
      t1.coeffs == c2 &&
        (m2 == 0 || decide (t1.rhs % (m2 : Int) = ((r2 % m2 : Nat) : Int)))
  | .carryLe a1 b1 cin1 k1, .carryLe a2 b2 cin2 k2 =>
      cin1 == cin2 && decide (k1 ≤ k2) && eqNatAff a1 a2 && eqNatAff b1 b2
  | a1, a2 => eqAtom a1 a2

def formulaSize : Formula → Nat
  | .tt => 1
  | .ff => 1
  | .atom _ => 1
  | .not f => 1 + formulaSize f
  | .and f1 f2 => 1 + formulaSize f1 + formulaSize f2
  | .or f1 f2 => 1 + formulaSize f1 + formulaSize f2

def entailsFuel : Nat → Formula → Formula → Bool
  | 0, _, _ => false
  | fuel + 1, p, q =>
    if eqFormula p q then true
    else match p, q with
    | .ff, _ => true
    | _, .tt => true
    | .or p1 p2, q => entailsFuel fuel p1 q && entailsFuel fuel p2 q
    | p, .or q1 q2 => entailsFuel fuel p q1 || entailsFuel fuel p q2
    | p, .and q1 q2 => entailsFuel fuel p q1 && entailsFuel fuel p q2
    | .and p1 p2, q => entailsFuel fuel p1 q || entailsFuel fuel p2 q
    | .not p1, .not q1 => entailsFuel fuel q1 p1
    | .atom a1, .atom a2 => entailsAtom a1 a2
    | _, _ => false

def entails (p q : Formula) : Bool :=
  entailsFuel (formulaSize p + formulaSize q) p q

/-! ## Section 5: Finite Residue-Carry Witness Certificate, Checker,
       Constructive Skolem Transducer, and General Soundness Meta-Theorem -/

def indexOfBits : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * indexOfBits bs

def bitsOfIndex : Nat → Nat → List Bool
  | 0, _ => []
  | d + 1, idx => (decide (idx % 2 = 1)) :: bitsOfIndex d (idx / 2)

structure StateEntry where
  formula : Formula
  baseY   : List Nat
  trans   : List (List (List Bool) × Nat)
  deriving Repr

def defaultEntry : StateEntry := { formula := .ff, baseY := [], trans := [] }

structure Cert where
  d       : Nat
  e       : Nat
  entries : List StateEntry
  deriving Repr

def checkTransList (cert : Cert) (f : Formula) :
    Nat → List (List (List Bool) × Nat) → Bool
  | _, [] => true
  | idx, (uList, nextIdx) :: rest =>
    let b := bitsOfIndex cert.d idx
    let okU := !uList.isEmpty && uList.all (fun u => u.length == cert.e)
    let okNext := decide (nextIdx < cert.entries.length)
    let target := (cert.entries.getD nextIdx defaultEntry).formula
    let stepped := bigOr (uList.map (fun u => stepFormula f (b ++ u)))
    okU && okNext && entails target stepped && checkTransList cert f (idx + 1) rest

def checkEntry (cert : Cert) (entry : StateEntry) : Bool :=
  entry.baseY.length == cert.e &&
  evalFormulaBool entry.formula (List.replicate cert.d 0 ++ entry.baseY) &&
  entry.trans.length == 2 ^ cert.d &&
  checkTransList cert entry.formula 0 entry.trans

def checkCert (cert : Cert) : Bool :=
  decide (0 < cert.entries.length) &&
  cert.entries.all (checkEntry cert)

/-- Constructive witness-bit selector for the 2-pass Skolem transducer -/
def pickWitnessU (f : Formula) (b : List Bool) (x' y' : List Nat) :
    List (List Bool) → List Bool
  | [] => []
  | u :: us =>
    if evalFormulaBool (stepFormula f (b ++ u)) (x' ++ y') then u
    else pickWitnessU f b x' y' us

/-- Executable, kernel-reducible constructive Skolem transducer `synthesizeFuel` -/
def synthesizeFuel : Nat → Cert → Nat → List Nat → List Nat
  | 0, cert, stIdx, _ => (cert.entries.getD stIdx defaultEntry).baseY
  | fuel + 1, cert, stIdx, x =>
    if vecSum x == 0 then
      (cert.entries.getD stIdx defaultEntry).baseY
    else
      let entry := cert.entries.getD stIdx defaultEntry
      let b := vecMod2Bits x
      let x' := vecDiv2 x
      let idx := indexOfBits b
      let pair := entry.trans.getD idx ([], 0)
      let y' := synthesizeFuel fuel cert pair.2 x'
      let u := pickWitnessU entry.formula b x' y' pair.1
      vecStep y' u

def synthesizeFrom (cert : Cert) (stIdx : Nat) (x : List Nat) : List Nat :=
  synthesizeFuel (vecSum x) cert stIdx x

def synthesizeY (cert : Cert) (x : List Nat) : List Nat :=
  synthesizeFrom cert 0 x

end CPRTE
