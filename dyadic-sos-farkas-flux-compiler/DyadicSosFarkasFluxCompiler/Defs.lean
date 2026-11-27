/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Exact Dyadic Sum-of-Squares & Telescoping Flux Compiler (`dyadic-sos-farkas-flux-compiler`)

Pure-`Init` (zero Mathlib) definitions of `Dyadic`, `Poly`, `DyadicPoly`, `DyadicGram`, `FarkasSOSCert`, `CyclicFluxCert`, `sumDyadic`, `sumInt`, `cyclicWin`, and the concrete stencil terms for Theorems 1–6.
-/

namespace DyadicSOS

/-- Exact dyadic rational representing `mant / 2^exp` in `Z[1/2]`. -/
structure Dyadic where
  mant : Int
  exp  : Nat
deriving DecidableEq, Repr

namespace Dyadic

def zero : Dyadic := ⟨0, 0⟩

def one  : Dyadic := ⟨1, 0⟩

def ofInt (z : Int) : Dyadic := ⟨z, 0⟩

def ofNat (n : Nat) : Dyadic := ⟨(n : Int), 0⟩

def divPow2 (a : Dyadic) (k : Nat) : Dyadic := ⟨a.mant, a.exp + k⟩

def add (a b : Dyadic) : Dyadic :=
  ⟨a.mant * ((2 : Int) ^ b.exp) + b.mant * ((2 : Int) ^ a.exp), a.exp + b.exp⟩

def neg (a : Dyadic) : Dyadic := ⟨-a.mant, a.exp⟩

def sub (a b : Dyadic) : Dyadic := add a (neg b)

def mul (a b : Dyadic) : Dyadic := ⟨a.mant * b.mant, a.exp + b.exp⟩

def pow (a : Dyadic) : Nat → Dyadic
  | 0 => one
  | n + 1 => mul a (pow a n)

/-- Exact nonnegativity `0 ≤ a` in `Z[1/2]`. Since `2^exp > 0`, this is `0 ≤ mant`. -/
def Nonneg (a : Dyadic) : Prop := 0 ≤ a.mant

/-- Exact order `a ≤ b` in `Z[1/2]`. -/
def Le (a b : Dyadic) : Prop :=
  a.mant * ((2 : Int) ^ b.exp) ≤ b.mant * ((2 : Int) ^ a.exp)

/-- Exact zero predicate in `Z[1/2]`. -/
def IsZero (a : Dyadic) : Prop := a.mant = 0

/-- Kernel-fast exact power of 2 in `Int` via GMP `Nat.pow`. -/
def pow2Int (k : Nat) : Int := Int.ofNat (2 ^ k)

end Dyadic

/-- Sparse monomial: list of `(variable_index, exponent)` pairs. -/
abbrev Mono := List (Nat × Nat)

/-- Sparse integer polynomial: list of `(monomial, integer_coefficient)` pairs. -/
abbrev Poly := List (Mono × Int)

/-- Exact polynomial in `Z[1/2][x]`, representing `2^(-shift) * poly`. -/
structure DyadicPoly where
  shift : Nat
  poly  : Poly
deriving DecidableEq, Repr

namespace Mono

def cmp : Mono → Mono → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (v1, e1) :: t1, (v2, e2) :: t2 =>
    if v1 < v2 then .lt
    else if v2 < v1 then .gt
    else if e1 < e2 then .lt
    else if e2 < e1 then .gt
    else cmp t1 t2

def insertFactor (v e : Nat) : Mono → Mono
  | [] => [(v, e)]
  | (v', e') :: t =>
    if v < v' then (v, e) :: (v', e') :: t
    else if v' < v then (v', e') :: insertFactor v e t
    else (v, e + e') :: t

def mul : Mono → Mono → Mono
  | [], m2 => m2
  | (v, e) :: t, m2 => insertFactor v e (mul t m2)

def shiftFrom (k delta : Nat) (m : Mono) : Mono :=
  m.map (fun (v, e) => (if v < k then v else v + delta, e))

def eval (m : Mono) (env : Nat → Dyadic) : Dyadic :=
  match m with
  | [] => Dyadic.one
  | (v, e) :: t => Dyadic.mul (Dyadic.pow (env v) e) (eval t env)

def evalInt (m : Mono) (env : Nat → Int) : Int :=
  match m with
  | [] => 1
  | (v, e) :: t => ((env v) ^ e) * (evalInt t env)

end Mono

namespace Poly

def eval (p : Poly) (env : Nat → Dyadic) : Dyadic :=
  match p with
  | [] => Dyadic.zero
  | (m, c) :: t => Dyadic.add (Dyadic.mul (Dyadic.ofInt c) (Mono.eval m env)) (eval t env)

def evalInt (p : Poly) (env : Nat → Int) : Int :=
  match p with
  | [] => 0
  | (m, c) :: t => c * Mono.evalInt m env + evalInt t env

def insert (m : Mono) (c : Int) : Poly → Poly
  | [] => if c == 0 then [] else [(m, c)]
  | (m', c') :: t =>
    if c == 0 then (m', c') :: t
    else
      match Mono.cmp m m' with
      | .lt => (m, c) :: (m', c') :: t
      | .eq =>
        let s := c + c'
        if s == 0 then t else (m', s) :: t
      | .gt => (m', c') :: insert m c t

def normGo : Poly → Poly → Poly
  | [], acc => acc
  | (m, c) :: t, acc => normGo t (insert m c acc)

def norm (p : Poly) : Poly := normGo p []

def scale (k : Int) (p : Poly) : Poly :=
  if k == 0 then [] else p.map (fun (m, c) => (m, k * c))

def neg (p : Poly) : Poly := p.map (fun (m, c) => (m, -c))

def add (p q : Poly) : Poly := norm (p ++ q)

def mulTerm (m1 : Mono) (c1 : Int) (q : Poly) : Poly :=
  q.map (fun (m2, c2) => (Mono.mul m1 m2, c1 * c2))

def mulRaw : Poly → Poly → Poly
  | [], _ => []
  | (m1, c1) :: t1, q => mulTerm m1 c1 q ++ mulRaw t1 q

def mul (p q : Poly) : Poly := norm (mulRaw p q)

def shiftFrom (k delta : Nat) (p : Poly) : Poly :=
  norm (p.map (fun (m, c) => (Mono.shiftFrom k delta m, c)))

end Poly

namespace DyadicPoly

def zero : DyadicPoly := ⟨0, []⟩

def one  : DyadicPoly := ⟨0, [([], 1)]⟩

def eval (p : DyadicPoly) (env : Nat → Dyadic) : Dyadic :=
  Dyadic.divPow2 (Poly.eval p.poly env) p.shift

def natMax (a b : Nat) : Nat := if a ≤ b then b else a

def monoEq : Mono → Mono → Bool
  | [], [] => true
  | (v1, e1) :: t1, (v2, e2) :: t2 => (v1 == v2) && (e1 == e2) && monoEq t1 t2
  | _, _ => false

def polyEq : Poly → Poly → Bool
  | [], [] => true
  | (m1, c1) :: t1, (m2, c2) :: t2 => monoEq m1 m2 && (c1 == c2) && polyEq t1 t2
  | _, _ => false

def add (a b : DyadicPoly) : DyadicPoly :=
  let m := natMax a.shift b.shift
  let pa := Poly.scale (Dyadic.pow2Int (m - a.shift)) a.poly
  let pb := Poly.scale (Dyadic.pow2Int (m - b.shift)) b.poly
  ⟨m, Poly.add pa pb⟩

def neg (a : DyadicPoly) : DyadicPoly := ⟨a.shift, Poly.neg a.poly⟩

def sub (a b : DyadicPoly) : DyadicPoly := add a (neg b)

def mul (a b : DyadicPoly) : DyadicPoly := ⟨a.shift + b.shift, Poly.mul a.poly b.poly⟩

def shiftFrom (k delta : Nat) (a : DyadicPoly) : DyadicPoly :=
  ⟨a.shift, Poly.shiftFrom k delta a.poly⟩

def eq (a b : DyadicPoly) : Bool :=
  let pa := Poly.norm (Poly.scale (Dyadic.pow2Int b.shift) a.poly)
  let pb := Poly.norm (Poly.scale (Dyadic.pow2Int a.shift) b.poly)
  polyEq pa pb

end DyadicPoly

/--
Pure-data exact dyadic Gram matrix + binary LDL^T PSD certificate.
Represents `v(x)^T (2^(-shift) * G) v(x)` where `v(x)` is `basis` and
`2^scale * G = L^T * diag(diag) * L` with `diag[k] ≥ 0` and `G` symmetric.
-/
structure DyadicGram where
  basis : List Mono
  shift : Nat
  G     : List (List Int)
  scale : Nat
  diag  : List Int
  L     : List (List Int)
deriving DecidableEq, Repr

namespace Gram

def zeroRow (r : Nat) : List Int := List.replicate r (0 : Int)

def zeroMat (r : Nat) : List (List Int) := List.replicate r (zeroRow r)

def addScaledRow (k : Int) : List Int → List Int → List Int
  | a :: as, b :: bs => (a + k * b) :: addScaledRow k as bs
  | _, _ => []

def addOuterProd (d : Int) (row : List Int) : List (List Int) → List Int → List (List Int)
  | accRow :: accRows, c :: cs =>
      addScaledRow (d * c) accRow row :: addOuterProd d row accRows cs
  | _, _ => []

def reconFromFactors (r : Nat) : List Int → List (List Int) → List (List Int)
  | [], _ => zeroMat r
  | _, [] => zeroMat r
  | d :: ds, row :: rows =>
      addOuterProd d row (reconFromFactors r ds rows) row

def scaleMat (k : Int) (M : List (List Int)) : List (List Int) :=
  M.map (fun row => row.map (fun x => k * x))

def transpose : List (List Int) → List (List Int)
  | [] => []
  | r :: rs =>
    match rs with
    | [] => r.map (fun x => [x])
    | _ => List.zipWith List.cons r (transpose rs)

def isSymmetric (M : List (List Int)) : Bool :=
  M.isEmpty || (M == transpose M)

def checkPSD (g : DyadicGram) : Bool :=
  let r := g.basis.length
  (g.G.length == r) &&
  (g.G.all (fun row => row.length == r)) &&
  isSymmetric g.G &&
  (g.diag.length == g.L.length) &&
  (g.L.all (fun row => row.length == r)) &&
  (g.diag.all (fun d => decide (0 ≤ d))) &&
  (scaleMat (Dyadic.pow2Int g.scale) g.G == reconFromFactors r g.diag g.L)

-- Structural lemmas for `quadForm` and `addOuterProd`

def rowPoly : List Int → List Mono → Poly
  | c :: cs, m :: ms => (m, c) :: rowPoly cs ms
  | _, _ => []

def mulMonoPoly (m : Mono) (p : Poly) : Poly :=
  p.map (fun (m', c) => (Mono.mul m m', c))

def gramPolyRaw : List (List Int) → List Mono → List Mono → Poly
  | row :: rows, m :: ms, fullBasis =>
      mulMonoPoly m (rowPoly row fullBasis) ++ gramPolyRaw rows ms fullBasis
  | _, _, _ => []

def toDyadicPoly (g : DyadicGram) : DyadicPoly :=
  ⟨g.shift, Poly.norm (gramPolyRaw g.G g.basis g.basis)⟩

end Gram

/--
Pure-data exact dyadic Schmüdgen-Farkas Positivstellensatz certificate.
Proves `target ≥ 0` from `ineqs ≥ 0` and `eqs = 0` via the exact `Z[1/2][x]` identity:
  `target = mainGram + ∑_{(idxs, σ)} σ * ∏_{i ∈ idxs} ineqs[i] + ∑_j eqCofacts[j] * eqs[j]`.
-/
structure FarkasSOSCert where
  mainGram  : DyadicGram
  ineqProds : List (List Nat × DyadicGram)
  eqCofacts : List DyadicPoly
deriving DecidableEq, Repr

namespace FarkasSOS

def prodIneqs (ineqs : List DyadicPoly) : List Nat → Option DyadicPoly
  | [] => some DyadicPoly.one
  | idx :: rest =>
    match ineqs[idx]?, prodIneqs ineqs rest with
    | some g, some p => some (DyadicPoly.mul g p)
    | _, _ => none

def sumIneqProds (ineqs : List DyadicPoly) : List (List Nat × DyadicGram) → Option DyadicPoly
  | [] => some DyadicPoly.zero
  | (idxs, gr) :: rest =>
    if Gram.checkPSD gr then
      match prodIneqs ineqs idxs, sumIneqProds ineqs rest with
      | some p, some acc => some (DyadicPoly.add (DyadicPoly.mul (Gram.toDyadicPoly gr) p) acc)
      | _, _ => none
    else none

def sumEqCofacts : List DyadicPoly → List DyadicPoly → Option DyadicPoly
  | [], [] => some DyadicPoly.zero
  | q :: qs, h :: hs =>
    match sumEqCofacts qs hs with
    | some acc => some (DyadicPoly.add (DyadicPoly.mul q h) acc)
    | none => none
  | _, _ => none

def check (target : DyadicPoly) (ineqs eqs : List DyadicPoly) (cert : FarkasSOSCert) : Bool :=
  if !Gram.checkPSD cert.mainGram then false
  else
    match sumIneqProds ineqs cert.ineqProds, sumEqCofacts cert.eqCofacts eqs with
    | some sIneq, some sEq =>
        let rhs := DyadicPoly.add (Gram.toDyadicPoly cert.mainGram) (DyadicPoly.add sIneq sEq)
        DyadicPoly.eq target rhs
    | _, _ => false

end FarkasSOS

/-- Cyclic window embedding: variables `< paramCount` are global parameters,
and variables `paramCount + j` read `x ((i + j) % n)`. -/
def cyclicWin (paramCount n : Nat) (params x : Nat → Dyadic) (i : Nat) : Nat → Dyadic :=
  fun v => if v < paramCount then params v else x ((i + (v - paramCount)) % n)

def sumDyadic (f : Nat → Dyadic) : Nat → Dyadic
  | 0 => Dyadic.zero
  | k + 1 => Dyadic.add (sumDyadic f k) (f k)

def sumInt (f : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => sumInt f k + f k

/-- Pure-data infinite-dimensional cyclic telescoping flux-SOS-Farkas certificate. -/
structure CyclicFluxCert where
  flux    : DyadicPoly
  sosCert : FarkasSOSCert
deriving DecidableEq, Repr

def checkCyclicFlux (paramCount : Nat) (stencil : DyadicPoly)
    (localIneqs localEqs : List DyadicPoly) (cert : CyclicFluxCert) : Bool :=
  let shifted := DyadicPoly.sub (DyadicPoly.add stencil cert.flux)
                  (DyadicPoly.shiftFrom paramCount 1 cert.flux)
  FarkasSOS.check shifted localIneqs localEqs cert.sosCert

/-- Direct human-readable integer statement of Theorem 1 (Asymmetric-Skew Quartic Cyclic). -/
def asymSkewTerm (x : Nat → Int) (n i : Nat) : Int :=
  let a := x (i % n)
  let b := x ((i + 1) % n)
  let c := x ((i + 2) % n)
  8 * a ^ 4 + 8 * a ^ 2 * b ^ 2 - 13 * a ^ 3 * b + 13 * a * b ^ 2 * c

def thm3b_stencil : DyadicPoly :=
  { shift := 0, poly := [([], 2), ([(0, 1)], -3), ([(1, 1)], -3),
                         ([(0, 1), (1, 1)], 6), ([(0, 1), (2, 1)], 2),
                         ([(0, 1), (1, 1), (2, 1)], -2)] }

def boolToInt (b : Bool) : Int := if b then 1 else 0

-- (a+b-1)^2 + (a+c-1)^2 - 1/2 = (3 - 8a - 4b - 4c + 4a^2 + 2b^2 + 2c^2 + 4ab + 4ac) / 2

def frustratedTriTerm (b : Nat → Bool) (n i : Nat) : Int :=
  let x0 := boolToInt (b (i % n))
  let x1 := boolToInt (b ((i + 1) % n))
  let x2 := boolToInt (b ((i + 2) % n))
  2 * ((x0 + x1 - 1) ^ 2 + (x0 + x2 - 1) ^ 2) - 1

def biharmonicParamTerm (t : Int) (x : Nat → Int) (n i : Nat) : Int :=
  let a := x (i % n)
  let b := x ((i + 1) % n)
  let c := x ((i + 2) % n)
  (c - 2 * b + a) ^ 2 - 2 * t * (b - a) ^ 2 + t ^ 2 * a ^ 2

def openBiharmonicTerm (x : Nat → Int) (i : Nat) : Int :=
  (x (i + 2) - 2 * x (i + 1) + x i) ^ 2 - 4 * (x (i + 1) - x i) ^ 2 + 4 * x i ^ 2

def thm6_g0 : DyadicPoly := { shift := 0, poly := [([], 1), ([(0, 2)], -1), ([(1, 2)], -1)] }

def thm6_g1 : DyadicPoly := { shift := 4, poly := [([], -23), ([(0, 1)], 16), ([(1, 1)], 16)] }

end DyadicSOS
