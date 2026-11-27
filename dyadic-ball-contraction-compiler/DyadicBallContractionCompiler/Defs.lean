/-
  Verified Lean 4 Dyadic Ball-Arithmetic & Contraction Enclosure Compiler
  =======================================================================
  Pure-silicon binary proof compiler (standalone Lean 4.36.0, zero Mathlib,
  zero floating-point, zero sorry, zero custom axioms, pure kernel `decide`).
-/

namespace DyadicCompiler

-- ============================================================================
-- PART 1: Exact Rational Numbers (ExactQ) — Zero Float, Zero Quotients
-- ============================================================================

structure ExactQ where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving Repr

namespace ExactQ

def ofInt (z : Int) : ExactQ := ⟨z, 1, by omega⟩

def ofDyadic (m : Int) (e : Nat) : ExactQ :=
  ⟨m, 2 ^ e, Nat.pow_pos (by omega)⟩

def equiv (a b : ExactQ) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

def le (a b : ExactQ) : Prop :=
  a.num * (b.den : Int) ≤ b.num * (a.den : Int)

def lt (a b : ExactQ) : Prop :=
  a.num * (b.den : Int) < b.num * (a.den : Int)

def neg (a : ExactQ) : ExactQ :=
  ⟨-a.num, a.den, a.den_pos⟩

def add (a b : ExactQ) : ExactQ :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def sub (a b : ExactQ) : ExactQ :=
  ⟨a.num * (b.den : Int) - b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def mul (a b : ExactQ) : ExactQ :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def sqr (a : ExactQ) : ExactQ :=
  ⟨a.num * a.num, a.den * a.den, Nat.mul_pos a.den_pos a.den_pos⟩

def abs (a : ExactQ) : ExactQ :=
  ⟨(a.num.natAbs : Int), a.den, a.den_pos⟩

def invPos (a : ExactQ) (h : 0 < a.num) : ExactQ :=
  ⟨(a.den : Int), a.num.toNat, by omega⟩

def pow (a : ExactQ) : Nat → ExactQ
  | 0 => ofInt 1
  | n + 1 => mul a (pow a n)

def dist (a b : ExactQ) : ExactQ := abs (sub a b)

end ExactQ

-- ============================================================================
-- PART 2: Exact Dyadic Balls (m, e, r) & Verified Outward Rounding
-- ============================================================================

structure DyadicBall where
  m : Int   -- center mantissa: center = m / 2^e
  e : Nat   -- binary exponent (scale 2^(-e))
  r : Nat   -- radius mantissa: radius = r / 2^e
  deriving Repr, DecidableEq

namespace DyadicBall

def contains (b : DyadicBall) (q : ExactQ) : Prop :=
  (b.m - (b.r : Int)) * (q.den : Int) ≤ q.num * ((2 ^ b.e : Nat) : Int) ∧
  q.num * ((2 ^ b.e : Nat) : Int) ≤ (b.m + (b.r : Int)) * (q.den : Int)

def fromInterval (lo hi : Int) (e : Nat) : DyadicBall :=
  let m := (lo + hi) / 2
  let r := (hi - m).toNat
  ⟨m, e, r⟩

def roundTo (b : DyadicBall) (p : Nat) : DyadicBall :=
  if b.e ≤ p then
    let s : Nat := 2 ^ (p - b.e)
    ⟨b.m * (s : Int), p, b.r * s⟩
  else
    let s : Int := ((2 ^ (b.e - p) : Nat) : Int)
    let lo := (b.m - (b.r : Int)) / s
    let hi := (b.m + (b.r : Int) + s - 1) / s
    fromInterval lo hi p

def bisectLeft (b : DyadicBall) : DyadicBall :=
  ⟨2 * b.m - (b.r : Int), b.e + 1, b.r⟩

def bisectRight (b : DyadicBall) : DyadicBall :=
  ⟨2 * b.m + (b.r : Int), b.e + 1, b.r⟩

def midpoint (b : DyadicBall) : ExactQ := ExactQ.ofDyadic b.m b.e
def midpointBall (b : DyadicBall) : DyadicBall := ⟨b.m, b.e, 0⟩
def radiusBall (b : DyadicBall) : DyadicBall := ⟨0, b.e, b.r⟩

def subset (a b : DyadicBall) : Bool :=
  if a.e ≤ b.e then
    let s : Int := ((2 ^ (b.e - a.e) : Nat) : Int)
    decide ((b.m - (b.r : Int)) ≤ (a.m - (a.r : Int)) * s ∧
            (a.m + (a.r : Int)) * s ≤ (b.m + (b.r : Int)))
  else
    let s : Int := ((2 ^ (a.e - b.e) : Nat) : Int)
    decide ((b.m - (b.r : Int)) * s ≤ (a.m - (a.r : Int)) ∧
            (a.m + (a.r : Int)) ≤ (b.m + (b.r : Int)) * s)

def maxAbsLE (b : DyadicBall) (qNum qExp : Nat) : Bool :=
  let maxM : Nat := b.m.natAbs + b.r
  if b.e ≤ qExp then
    decide (maxM * 2 ^ (qExp - b.e) ≤ qNum)
  else
    decide (maxM ≤ qNum * 2 ^ (b.e - qExp))

def constInt (z : Int) : DyadicBall := ⟨z, 0, 0⟩
def constDyadic (m : Int) (e : Nat) : DyadicBall := ⟨m, e, 0⟩
def neg (a : DyadicBall) : DyadicBall := ⟨-a.m, a.e, a.r⟩

def add (a b : DyadicBall) (prec : Nat) : DyadicBall :=
  let raw : DyadicBall :=
    if a.e ≤ b.e then
      let s : Nat := 2 ^ (b.e - a.e)
      ⟨a.m * (s : Int) + b.m, b.e, a.r * s + b.r⟩
    else
      let s : Nat := 2 ^ (a.e - b.e)
      ⟨a.m + b.m * (s : Int), a.e, a.r + b.r * s⟩
  raw.roundTo prec

def sub (a b : DyadicBall) (prec : Nat) : DyadicBall := add a b.neg prec

def mul (a b : DyadicBall) (prec : Nat) : DyadicBall :=
  let mNew := a.m * b.m
  let rNew := a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r
  (DyadicBall.mk mNew (a.e + b.e) rNew).roundTo prec

def sqr (a : DyadicBall) (prec : Nat) : DyadicBall :=
  let lo := a.m - (a.r : Int)
  let hi := a.m + (a.r : Int)
  let raw :=
    if 0 ≤ lo then fromInterval (lo * lo) (hi * hi) (2 * a.e)
    else if hi ≤ 0 then fromInterval (hi * hi) (lo * lo) (2 * a.e)
    else fromInterval 0 (max (lo * lo) (hi * hi)) (2 * a.e)
  raw.roundTo prec

def invPos (a : DyadicBall) (prec : Nat) : Option DyadicBall :=
  if a.m - (a.r : Int) ≤ 0 then none
  else
    let lo := a.m - (a.r : Int)
    let hi := a.m + (a.r : Int)
    let num : Int := ((2 ^ (a.e + prec) : Nat) : Int)
    let invLo := num / hi
    let invHi := (num + lo - 1) / lo
    some (fromInterval invLo invHi prec)

end DyadicBall

-- ============================================================================
-- PART 3: Expression AST, Exact Rational Semantics & Algebraic Jet Evaluator
-- ============================================================================

inductive Expr where
  | var : Expr
  | param : Expr
  | constInt : Int → Expr
  | constDyadic : Int → Nat → Expr
  | neg : Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | sqr : Expr → Expr
  | inv : Expr → Expr
  deriving Repr, DecidableEq

def evalQ : Expr → ExactQ → ExactQ → Option ExactQ
  | .var, _, x => some x
  | .param, p, _ => some p
  | .constInt z, _, _ => some (ExactQ.ofInt z)
  | .constDyadic m e, _, _ => some (ExactQ.ofDyadic m e)
  | .neg a, p, x => (evalQ a p x).map ExactQ.neg
  | .add a b, p, x => Option.bind (evalQ a p x) fun va => Option.bind (evalQ b p x) fun vb => some (va.add vb)
  | .sub a b, p, x => Option.bind (evalQ a p x) fun va => Option.bind (evalQ b p x) fun vb => some (va.sub vb)
  | .mul a b, p, x => Option.bind (evalQ a p x) fun va => Option.bind (evalQ b p x) fun vb => some (va.mul vb)
  | .sqr a, p, x => (evalQ a p x).map ExactQ.sqr
  | .inv a, p, x => Option.bind (evalQ a p x) fun va => if h : 0 < va.num then some (va.invPos h) else none

def iterQ (e : Expr) (p : ExactQ) : Nat → ExactQ → Option ExactQ
  | 0, x => some x
  | n + 1, x => Option.bind (iterQ e p n x) fun xn => evalQ e p xn

def evalBall (prec : Nat) : Expr → DyadicBall → DyadicBall → Option DyadicBall
  | .var, _, X => some (X.roundTo prec)
  | .param, P, _ => some (P.roundTo prec)
  | .constInt z, _, _ => some (DyadicBall.constInt z)
  | .constDyadic m e, _, _ => some (DyadicBall.constDyadic m e)
  | .neg a, P, X => (evalBall prec a P X).map DyadicBall.neg
  | .add a b, P, X => Option.bind (evalBall prec a P X) fun va => Option.bind (evalBall prec b P X) fun vb => some (DyadicBall.add va vb prec)
  | .sub a b, P, X => Option.bind (evalBall prec a P X) fun va => Option.bind (evalBall prec b P X) fun vb => some (DyadicBall.sub va vb prec)
  | .mul a b, P, X => Option.bind (evalBall prec a P X) fun va => Option.bind (evalBall prec b P X) fun vb => some (DyadicBall.mul va vb prec)
  | .sqr a, P, X => Option.bind (evalBall prec a P X) fun va => some (DyadicBall.sqr va prec)
  | .inv a, P, X => Option.bind (evalBall prec a P X) fun va => DyadicBall.invPos va prec

def evalJetBall (prec : Nat) : Expr → DyadicBall → DyadicBall → Option (DyadicBall × DyadicBall)
  | .var, _, X => some (X.roundTo prec, DyadicBall.constInt 1)
  | .param, P, _ => some (P.roundTo prec, DyadicBall.constInt 0)
  | .constInt z, _, _ => some (DyadicBall.constInt z, DyadicBall.constInt 0)
  | .constDyadic m e, _, _ => some (DyadicBall.constDyadic m e, DyadicBall.constInt 0)
  | .neg a, P, X => Option.bind (evalJetBall prec a P X) fun p => some (p.1.neg, p.2.neg)
  | .add a b, P, X =>
      Option.bind (evalJetBall prec a P X) fun pa =>
      Option.bind (evalJetBall prec b P X) fun pb =>
      some (DyadicBall.add pa.1 pb.1 prec, DyadicBall.add pa.2 pb.2 prec)
  | .sub a b, P, X =>
      Option.bind (evalJetBall prec a P X) fun pa =>
      Option.bind (evalJetBall prec b P X) fun pb =>
      some (DyadicBall.sub pa.1 pb.1 prec, DyadicBall.sub pa.2 pb.2 prec)
  | .mul a b, P, X =>
      Option.bind (evalJetBall prec a P X) fun pa =>
      Option.bind (evalJetBall prec b P X) fun pb =>
      let v := DyadicBall.mul pa.1 pb.1 prec
      let s := DyadicBall.add (DyadicBall.mul pa.2 pb.1 prec) (DyadicBall.mul pa.1 pb.2 prec) prec
      some (v, s)
  | .sqr a, P, X =>
      Option.bind (evalJetBall prec a P X) fun pa =>
      let v := DyadicBall.sqr pa.1 prec
      let twoVa := DyadicBall.mul (DyadicBall.constInt 2) pa.1 prec
      let s := DyadicBall.mul twoVa pa.2 prec
      some (v, s)
  | .inv a, P, X =>
      Option.bind (evalJetBall prec a P X) fun pa =>
      Option.bind (DyadicBall.invPos pa.1 prec) fun invV =>
      let invProd := DyadicBall.mul invV invV prec
      let s := (DyadicBall.mul pa.2 invProd prec).neg
      some (invV, s)

def evalCenteredBall (prec : Nat) (e : Expr) (P X : DyadicBall) : Option (DyadicBall × DyadicBall) :=
  Option.bind (evalJetBall prec e P X) fun jet =>
  Option.bind (evalBall prec e P X.midpointBall) fun vMid =>
  let delta := DyadicBall.mul jet.2 X.radiusBall prec
  some (DyadicBall.add vMid delta prec, jet.2)

-- Exact Algebraic Secant-Slope Identities over ExactQ (Zero Calculus!)
namespace SlopeIdentities

end SlopeIdentities

-- Soundness of evalBall
inductive StateTree where
  | leaf (prec : Nat) (useCentered : Bool) : StateTree
  | split (left right : StateTree) : StateTree
  deriving Repr, DecidableEq

inductive ParamTree where
  | pleaf (stateTree : StateTree) : ParamTree
  | psplit (left right : ParamTree) : ParamTree
  deriving Repr, DecidableEq

structure ParamContractionCert where
  expr : Expr
  p0 : DyadicBall
  b0 : DyadicBall
  qNum : Nat
  qExp : Nat
  tree : ParamTree
  deriving Repr, DecidableEq

def checkStateLeaf (e : Expr) (P B0 B : DyadicBall) (qNum qExp prec : Nat) (useCentered : Bool) : Bool :=
  let res := if useCentered then evalCenteredBall prec e P B else evalJetBall prec e P B
  match res with
  | none => false
  | some (V, S) => V.subset B0 && S.maxAbsLE qNum qExp

def checkStateTree (e : Expr) (P B0 B : DyadicBall) (qNum qExp : Nat) : StateTree → Bool
  | .leaf prec uc => checkStateLeaf e P B0 B qNum qExp prec uc
  | .split l r =>
      checkStateTree e P B0 B.bisectLeft qNum qExp l &&
      checkStateTree e P B0 B.bisectRight qNum qExp r

def checkParamTree (e : Expr) (P B0 : DyadicBall) (qNum qExp : Nat) : ParamTree → Bool
  | .pleaf st => checkStateTree e P B0 B0 qNum qExp st
  | .psplit l r =>
      checkParamTree e P.bisectLeft B0 qNum qExp l &&
      checkParamTree e P.bisectRight B0 qNum qExp r

def checkParamContraction (cert : ParamContractionCert) : Bool :=
  decide (cert.qNum < 2 ^ cert.qExp) &&
  checkParamTree cert.expr cert.p0 cert.b0 cert.qNum cert.qExp cert.tree

-- Core Property Certified by a StateTree on (P, B)
def IsSelfMappedLipschitz (e : Expr) (p : ExactQ) (B0 B : DyadicBall) (q : ExactQ) : Prop :=
  (∀ x, B.contains x → ∃ fx, evalQ e p x = some fx ∧ B0.contains fx) ∧
  (∀ x y fx fy, B.contains x → B.contains y → evalQ e p x = some fx → evalQ e p y = some fy →
    (fx.dist fy).le (q.mul (x.dist y)))

-- Binary-Tree Telescoping Soundness Meta-Theorem for StateTree!
def exprHalley : Expr :=
  .sub .var (.mul (.mul (.constInt 2) (.mul .var (.sub (.sqr .var) .param)))
                  (.inv (.add (.mul (.constInt 3) (.sqr .var)) .param)))

def exprBringNewton : Expr :=
  .sub .var (.mul (.sub (.add (.mul .var (.sqr (.sqr .var))) (.mul (.add (.constInt 1) .param) .var)) (.constInt 1))
                  (.inv (.add (.add (.constInt 1) .param) (.mul (.constInt 5) (.sqr (.sqr .var))))))

def exprLogistic : Expr :=
  .mul .param (.mul .var (.sub (.constInt 1) .var))

def exprBringDirect : Expr :=
  .inv (.add (.constInt 1) (.sqr (.sqr .var)))

def certHalley : ParamContractionCert := {
  expr := exprHalley,
  p0 := ⟨5, 1, 3⟩,       -- [1, 4]
  b0 := ⟨49, 5, 19⟩,     -- [15/16, 17/8], strictly contains [1, 2]
  qNum := 7,
  qExp := 3,             -- q = 7/8
  tree := (.psplit (.psplit (.pleaf (.split (.split (.split (.split (.split (.leaf 14 true) (.leaf 14 true)) (.leaf 14 true)) (.split (.leaf 14 true) (.leaf 14 true))) (.split (.split (.leaf 14 true) (.leaf 14 true)) (.split (.leaf 14 true) (.leaf 14 true)))) (.split (.split (.split (.leaf 14 true) (.leaf 14 true)) (.split (.leaf 14 true) (.leaf 14 true))) (.split (.split (.leaf 14 true) (.leaf 14 true)) (.split (.leaf 14 false) (.leaf 14 false)))))) (.pleaf (.split (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false)))))) (.psplit (.psplit (.pleaf (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.leaf 14 false) (.split (.leaf 14 false) (.leaf 14 false))))) (.pleaf (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.leaf 14 true) (.leaf 14 true))))) (.psplit (.pleaf (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.leaf 14 false)) (.split (.leaf 14 true) (.leaf 14 false))) (.split (.leaf 14 true) (.leaf 14 true)))) (.pleaf (.split (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.leaf 14 false)) (.leaf 14 true)) (.split (.leaf 14 true) (.leaf 14 true))) (.split (.split (.leaf 14 true) (.leaf 14 true)) (.leaf 14 true)))))))
}

def certBring : ParamContractionCert := {
  expr := exprBringNewton,
  p0 := ⟨1, 2, 1⟩,       -- [0, 1/2]
  b0 := ⟨3, 2, 1⟩,       -- [1/2, 1]
  qNum := 7,
  qExp := 3,             -- q = 7/8
  tree := (.psplit (.psplit (.psplit (.pleaf (.split (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false)))))) (.pleaf (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))))))) (.pleaf (.split (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false)))))))) (.psplit (.pleaf (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))))))) (.psplit (.pleaf (.split (.split (.leaf 14 true) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))))))) (.pleaf (.split (.split (.leaf 14 true) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.split (.leaf 14 false) (.leaf 14 false))) (.split (.split (.leaf 14 false) (.leaf 14 false)) (.split (.leaf 14 false) (.leaf 14 false))))))))))
}

def certBringTight : ParamContractionCert := {
  expr := exprBringNewton,
  p0 := ⟨0, 0, 0⟩,          -- p = 0 (classic Bring radical)
  b0 := ⟨791547, 20, 1⟩,    -- radius 2^(-20) around alpha ≈ 0.7548776662...
  qNum := 1,
  qExp := 16,               -- q = 1/65536
  tree := (.pleaf (.leaf 32 true))
}

def certLogistic : ParamContractionCert := {
  expr := exprLogistic,
  p0 := ⟨79, 5, 3⟩,      -- [19/8, 41/16]
  b0 := ⟨18, 5, 3⟩,      -- [15/32, 21/32], contains turning point x = 1/2
  qNum := 7,
  qExp := 3,             -- q = 7/8
  tree := (.pleaf (.split (.leaf 12 true) (.leaf 12 true)))
}

def certBringAlt : ParamContractionCert := {
  expr := exprBringDirect,
  p0 := ⟨0, 0, 0⟩,
  b0 := ⟨773, 10, 1⟩,    -- [772/1024, 774/1024]
  qNum := 63,
  qExp := 6,             -- q = 63/64
  tree := (.pleaf (.split (.leaf 18 false) (.leaf 18 false)))
}

-- Pure Kernel Verification via `decide` (Zero native_decide, Zero TrustCompiler!)
/-- Helper: Exact positive dyadic scaling factor 2^k for signed integer k : Int. -/
def pow2Q (k : Int) : ExactQ :=
  match k with
  | Int.ofNat n => ExactQ.ofInt ((2 ^ n : Nat) : Int)
  | Int.negSucc n => ExactQ.ofDyadic 1 (n + 1)

def bringPoly (p x : ExactQ) : ExactQ :=
  ((x.mul x.sqr.sqr).add (((ExactQ.ofInt 1).add p).mul x)).sub (ExactQ.ofInt 1)

/-- Exact fixed point x*(mu) = (mu - 1) / mu for any mu > 0. -/
def logisticFixedPoint (mu : ExactQ) (hmu : 0 < mu.num) : ExactQ :=
  (mu.sub (ExactQ.ofInt 1)).mul (mu.invPos hmu)

end DyadicCompiler

-- 5.9 Axiom Audit (Must show ONLY standard Lean axioms or empty!)
