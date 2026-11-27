/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`binary-morphism-abelian-balance`)

Binary Word-Morphism Modular-Stratified Abelian Balance Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace MSQRPAIE


/-! =========================================================================
    SECTION 1: Pure-Silicon Quadratic-Ring Arithmetic & Exact Integer Order
    ========================================================================= -/

/-- Element `u + v * λ₂` of `ℤ[λ₂]` where `λ₂ = (tr - √d) / 2`. -/
abbrev QElem := Int × Int

def qAdd (x y : QElem) : QElem := (x.1 + y.1, x.2 + y.2)

def qSub (x y : QElem) : QElem := (x.1 - y.1, x.2 - y.2)

def qNeg (x : QElem) : QElem := (-x.1, -x.2)

def qScale (k : Int) (x : QElem) : QElem := (k * x.1, k * x.2)

def qMulLam2 (tr det : Int) (x : QElem) : QElem := (-det * x.2, x.1 + tr * x.2)

/-- Exact integer test for `X - Y * √d ≥ 0` (valid for `d > 0`). -/
def signSqrtGe (d : Nat) (X Y : Int) : Bool :=
  if Y == 0 then decide (0 ≤ X)
  else if 0 < Y then decide (0 ≤ X ∧ (d : Int) * (Y * Y) ≤ X * X)
  else decide (0 ≤ X ∨ X * X ≤ (d : Int) * (Y * Y))

/-- Exact integer test for `X - Y * √d > 0` (valid for `d > 0`). -/
def signSqrtGt (d : Nat) (X Y : Int) : Bool :=
  if Y == 0 then decide (0 < X)
  else if 0 < Y then decide (0 < X ∧ (d : Int) * (Y * Y) < X * X)
  else decide (0 ≤ X ∨ X * X < (d : Int) * (Y * Y))

/-- Map `(u, v)` to `(X, Y) = (2u + tr*v, v)` so `2*(u + v*λ₂) = X - Y*√d`. -/
def qToXY (tr : Int) (x : QElem) : Int × Int := (2 * x.1 + tr * x.2, x.2)

def qNonneg (tr : Int) (d : Nat) (x : QElem) : Bool :=
  let p := qToXY tr x
  signSqrtGe d p.1 p.2

def qPos (tr : Int) (d : Nat) (x : QElem) : Bool :=
  let p := qToXY tr x
  signSqrtGt d p.1 p.2

def qLe (tr : Int) (d : Nat) (x y : QElem) : Bool := qNonneg tr d (qSub y x)

def qLt (tr : Int) (d : Nat) (x y : QElem) : Bool := qPos tr d (qSub y x)

/-! ### Elementary constructive `Int` square/product helpers -/

/-- A binary word morphism `σ : {0, 1}* → {0, 1}*` (`false` = 0, `true` = 1). -/
structure Morphism where
  w0 : List Bool
  w1 : List Bool
  deriving Repr, DecidableEq

def countZeros : List Bool → Nat
  | [] => 0
  | false :: t => countZeros t + 1
  | true :: t => countZeros t

def countOnes : List Bool → Nat
  | [] => 0
  | false :: t => countOnes t
  | true :: t => countOnes t + 1

namespace Morphism


def applyChar (m : Morphism) (b : Bool) : List Bool :=
  if b then m.w1 else m.w0

def applyWord (m : Morphism) (u : List Bool) : List Bool :=
  u.flatMap m.applyChar

def mA (m : Morphism) : Int := countZeros m.w0

def mB (m : Morphism) : Int := countOnes m.w0

def mC (m : Morphism) : Int := countZeros m.w1

def mD (m : Morphism) : Int := countOnes m.w1

def mTr (m : Morphism) : Int := m.mA + m.mD

def mDet (m : Morphism) : Int := m.mA * m.mD - m.mB * m.mC

def mDiscInt (m : Morphism) : Int := m.mTr * m.mTr - 4 * m.mDet

def mDisc (m : Morphism) : Nat := m.mDiscInt.toNat

def mLambda (m : Morphism) : QElem := (m.mC + m.mD, -1)

/-- Exact `ℤ[λ₂]`-valued abelian discrepancy `D(w) = #₀(w)*(λ₂ - d) + #₁(w)*c`. -/
def discWord (m : Morphism) (w : List Bool) : QElem :=
  (m.mC * (countOnes w : Int) - m.mD * (countZeros w : Int), (countZeros w : Int))

def iter (m : Morphism) : Nat → List Bool
  | 0 => [false]
  | k + 1 => m.applyWord (m.iter k)

def wordPrefix (m : Morphism) (n : Nat) : List Bool := (m.iter n).take n

def wordChar (m : Morphism) (n : Nat) : Bool := (m.iter (n + 1)).getD n false

def wordFactor (m : Morphism) (i n : Nat) : List Bool := ((m.iter (i + n)).drop i).take n

def iterChar (m : Morphism) : Nat → Bool → List Bool
  | 0, b => [b]
  | d + 1, b => m.applyWord (m.iterChar d b)

def dtStats (m : Morphism) : Nat → (Nat × Nat × Nat × Nat)
  | 0 => (1, 1, 0, 1)
  | d + 1 =>
    let (l0, l1, o0, o1) := m.dtStats d
    let a := countZeros m.w0; let b := countOnes m.w0
    let c := countZeros m.w1; let dd := countOnes m.w1
    (a * l0 + b * l1, c * l0 + dd * l1, a * o0 + b * o1, c * o0 + dd * o1)

def dtTakeOnesScan (m : Morphism) (d : Nat) (l0 l1 o0 o1 : Nat)
    (recFn : Bool → Nat → Nat) : List Bool → Nat → Nat
  | [], _ => 0
  | ch :: rest, pos =>
    let l := if ch then l1 else l0
    let o := if ch then o1 else o0
    if pos < l then recFn ch pos
    else o + dtTakeOnesScan m d l0 l1 o0 o1 recFn rest (pos - l)

def dtTakeOnes (m : Morphism) : Nat → Bool → Nat → Nat
  | 0, b, pos => if pos == 0 then 0 else if b then 1 else 0
  | d + 1, b, pos =>
    let (l0, l1, o0, o1) := m.dtStats d
    dtTakeOnesScan m d l0 l1 o0 o1 (m.dtTakeOnes d) (m.applyChar b) pos

end Morphism


/-! =========================================================================
    SECTION 3: Pure-Data Certificate Checker (`StratCert`) & Master Soundness
    ========================================================================= -/

/-- Pure-data finite certificate for `MS-QR-PAIE` (zero `Prop` fields). -/
structure StratCert where
  D    : Nat
  M    : Nat
  C    : Nat
  L0   : QElem
  U0   : QElem
  L1   : QElem
  U1   : QElem
  Lres : List QElem
  Ures : List QElem
  deriving Repr, DecidableEq

def wordSplitsAux (pref : List Bool) : List Bool → List (List Bool × Bool × List Bool)
  | [] => []
  | c :: t => (pref, c, t) :: wordSplitsAux (pref ++ [c]) t

def wordSplits (w : List Bool) : List (List Bool × Bool × List Bool) :=
  wordSplitsAux [] w

def StratCert.loState (cert : StratCert) (b : Bool) : QElem :=
  if b then cert.L1 else cert.L0

def StratCert.hiState (cert : StratCert) (b : Bool) : QElem :=
  if b then cert.U1 else cert.U0

def checkTransition (m : Morphism) (cert : StratCert) (lamPos : Bool)
    (src : Bool) (sp : List Bool × Bool × List Bool) : Bool :=
  let (r, dst, _) := sp
  let dr := qScale (cert.D : Int) (m.discWord r)
  let imgLo := qAdd (qMulLam2 m.mTr m.mDet (if lamPos then cert.loState src else cert.hiState src)) dr
  let imgHi := qAdd (qMulLam2 m.mTr m.mDet (if lamPos then cert.hiState src else cert.loState src)) dr
  let res := r.length % cert.M
  let lRes := cert.Lres.getD res (0, 0)
  let uRes := cert.Ures.getD res (0, 0)
  qLe m.mTr m.mDisc (cert.loState dst) imgLo &&
  qLe m.mTr m.mDisc imgHi (cert.hiState dst) &&
  qLe m.mTr m.mDisc lRes imgLo &&
  qLe m.mTr m.mDisc imgHi uRes

def checkAllTransitions (m : Morphism) (cert : StratCert) (lamPos : Bool) : Bool :=
  (wordSplits m.w0).all (checkTransition m cert lamPos false) &&
  (wordSplits m.w1).all (checkTransition m cert lamPos true)

def checkStratDiameter (m : Morphism) (cert : StratCert) : Bool :=
  let rhs := qScale (((cert.C + 1 : Nat) * cert.D : Nat) : Int) m.mLambda
  (List.range cert.M).all fun rho =>
    let negRho := (cert.M - rho) % cert.M
    (List.range cert.M).all fun r =>
      let rp := (r + rho) % cert.M
      let diff1 := qSub (cert.Ures.getD rp (0, 0)) (cert.Lres.getD r (0, 0))
      (List.range cert.M).all fun s =>
        let sp := (s + negRho) % cert.M
        let diff2 := qSub (cert.Ures.getD sp (0, 0)) (cert.Lres.getD s (0, 0))
        qLe m.mTr m.mDisc (qAdd diff1 diff2) rhs

/-- Pure-silicon decidable certificate verifier (zero `Prop` fields, zero floats). -/
def verifyCert (m : Morphism) (cert : StratCert) : Bool :=
  let lamPos := qPos m.mTr m.mDisc (0, 1)
  let lamNeg := qPos m.mTr m.mDisc (0, -1)
  (m.w0.head? == some false) &&
  decide (2 ≤ m.w0.length) &&
  decide (1 ≤ m.w1.length) &&
  decide (0 < cert.D) &&
  decide (0 < cert.M) &&
  (cert.Lres.length == cert.M) &&
  (cert.Ures.length == cert.M) &&
  (m.w0.length % cert.M == 0) &&
  (m.w1.length % cert.M == 0) &&
  decide (0 < m.mDiscInt) &&
  qPos m.mTr m.mDisc m.mLambda &&
  (lamPos || lamNeg) &&
  qLt m.mTr m.mDisc cert.L0 (0, 0) &&
  qLt m.mTr m.mDisc (0, 0) cert.U0 &&
  checkAllTransitions m cert lamPos &&
  checkStratDiameter m cert

def sigmaK (k : Nat) : Morphism :=
  { w0 := List.replicate k false ++ [true, false]
    w1 := [false, true] }

def phaseBound (k : Nat) : Nat :=
  if k == 1 then 1
  else if k == 2 then 2
  else if k == 3 then 3
  else if k ≤ 7 then 2 * k - 3
  else 2 * k - 4

def sigmaKCert (k : Nat) : StratCert :=
  if k == 1 then
    { D := 1, M := 1, C := 1,
      L0 := (0, -1), U0 := (1, -1), L1 := (-1, 0), U1 := (0, -1),
      Lres := [(-1, 0)], Ures := [(1, -1)] }
  else
    { D := 1, M := 1, C := phaseBound k,
      L0 := (1 - (k : Int), 0), U0 := (1, -1),
      L1 := (-(k : Int), 1), U1 := (0, -1),
      Lres := [(-(k : Int), 1)], Ures := [(1, -1)] }

def lam2Pow (k : Nat) : Nat → QElem
  | 0 => (1, 0)
  | m + 1 => qMulLam2 ((k : Int) + 2) (k : Int) (lam2Pow k m)

def uMinBase (k : Nat) : Nat → List Bool
  | 0 => []
  | m + 1 => (sigmaK k).applyWord (uMinBase k m) ++ List.replicate (k - 1) false

def uMin (k m : Nat) : List Bool :=
  (sigmaK k).applyWord (uMinBase k m) ++ List.replicate k false

def vMax (k : Nat) : Nat → List Bool
  | 0 => []
  | m + 1 => (sigmaK k).applyWord (vMax k m) ++ List.replicate k false ++ [true]

def tauA : Morphism :=
  { w0 := [false, true, false, true], w1 := [false, false, true] }

def tauB : Morphism :=
  { w0 := [false, true, true, false], w1 := [false, false, true] }

def tauACert : StratCert :=
  { D := 4, M := 1, C := 2,
    L0 := (-6, -1), U0 := (6, -1), L1 := (-10, 3), U1 := (-2, -1),
    Lres := [(-10, 3)], Ures := [(6, -1)] }

def tauBCert : StratCert :=
  { D := 4, M := 1, C := 4,
    L0 := (-10, 1), U0 := (14, -3), L1 := (-14, 5), U1 := (6, -3),
    Lres := [(-14, 5)], Ures := [(14, -3)] }

/-- Oscillating `M = 3, D = 3, det = -3` morphism: `0 ↦ 010101, 1 ↦ 001`. -/
def mu1 : Morphism :=
  { w0 := [false, true, false, true, false, true], w1 := [false, false, true] }

def mu1CertM3 : StratCert :=
  { D := 3, M := 3, C := 2,
    L0 := (-6, -1), U0 := (6, -1), L1 := (-9, 2), U1 := (0, -1),
    Lres := [(-3, 8), (-6, 5), (-9, 2)],
    Ures := [(6, -1), (3, -4), (0, -7)] }

/-- Unstratified `M = 1` attempt claiming `C = 2` for `mu1` MUST FAIL! -/
def mu1CertM1_failC2 : StratCert :=
  { D := 3, M := 1, C := 2,
    L0 := (-6, -1), U0 := (6, -1), L1 := (-9, 2), U1 := (0, -1),
    Lres := [(-9, 2)], Ures := [(6, -1)] }

/-- Monotone `M = 3, D = 1, det = +3` morphism: `0 ↦ 000001, 1 ↦ 100`. -/
def mu2 : Morphism :=
  { w0 := [false, false, false, false, false, true], w1 := [true, false, false] }

def mu2CertM3 : StratCert :=
  { D := 1, M := 3, C := 4,
    L0 := (-4, 0), U0 := (2, 0), L1 := (-5, 1), U1 := (0, 0),
    Lres := [(-3, -1), (-4, 0), (-5, 1)],
    Ures := [(0, 2), (2, 0), (1, 1)] }

def mu2CertM1_failC4 : StratCert :=
  { D := 1, M := 1, C := 4,
    L0 := (-4, 0), U0 := (2, 0), L1 := (-5, 1), U1 := (0, 0),
    Lres := [(-5, 1)], Ures := [(2, 0)] }

end MSQRPAIE
