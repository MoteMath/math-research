/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`BsdaMixedBitwisePermPolys`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace MixedPermEngine

-- ============================================================================
-- Section 1: Universal Coherent T-Function Framework & Bit-Slice Lifting
-- ============================================================================

/-- Standard bijectivity predicate (injective ∧ surjective), self-contained in core Lean 4. -/
def Bijective {α β : Type _} (f : α → β) : Prop :=
  (∀ a b, f a = f b → a = b) ∧ (∀ y, ∃ x, f x = y)

/-- A coherent family of `BitVec w` endomorphisms (a 2-adic T-function family):
    truncating the `(w+1)`-bit output to `w` bits depends only on the `w`-bit input. -/
def Coherent (f : ∀ w : Nat, BitVec w → BitVec w) : Prop :=
  ∀ (w : Nat) (x : BitVec (w + 1)),
    (f (w + 1) x).setWidth w = f w (x.setWidth w)

/-- The bit-`i` Boolean flip-derivative of a family `f` at lower prefix `x : BitVec i`:
    whether flipping bit `i` (the MSB of `BitVec (i+1)`) flips bit `i` of `f`. -/
def bitDeriv (f : ∀ w : Nat, BitVec w → BitVec w) (i : Nat) (x : BitVec i) : Bool :=
  (f (i + 1) (BitVec.cons true x)).msb != (f (i + 1) (BitVec.cons false x)).msb

/-- Bit 0 of `f` evaluated at `x_0 = b`. -/
def bit0Val (f : ∀ w : Nat, BitVec w → BitVec w) (b : Bool) : Bool :=
  (f 1 (BitVec.cons b (0#0))).msb

-- ============================================================================
-- Section 2: Exact 11-Rule Bit-Slice Differential Calculus on `BitVec w`
-- ============================================================================

/-- Two's-complement bit `i` of a signed integer `c`. -/
def intBit (c : Int) (i : Nat) : Bool :=
  match c with
  | Int.ofNat n   => n.testBit i
  | Int.negSucc n => !(n.testBit i)

/-- Auxiliary natural bit-length helper. -/
def natSigBits (m : Nat) : Nat :=
  if m = 0 then 0 else Nat.log2 m + 1

/-- Number of non-sign bits of `c : Int`; for all `i ≥ intSigBits c`, `intBit c i = (c < 0)`. -/
def intSigBits (c : Int) : Nat :=
  match c with
  | Int.ofNat n   => natSigBits n
  | Int.negSucc n => natSigBits n

-- ============================================================================
-- Section 3: Pure-Data Finite-Slice Automaton & Reachability Stabilization Engine
-- ============================================================================

/-- Concrete non-dependent state representation for all bit-slice transducers/automata. -/
inductive SState where
  | unit  : SState
  | bit   : Bool → SState
  | buf   : List Bool → SState
  | pair  : SState → SState → SState
  | carry : SState → SState → Bool → SState
  deriving DecidableEq, Repr

/-- Pure-data time-eventually-homogeneous bit-slice automaton (zero `Prop` fields). -/
structure SliceAuto where
  init1 : Bool → SState
  step  : Nat → SState → Bool → SState
  out   : Nat → SState → Bool
  L     : Nat

-- Deduplicated list union helpers (self-contained, fast kernel reduction)
def addUniq (q : SState) (l : List SState) : List SState :=
  if q ∈ l then l else q :: l

def unionUniq (xs acc : List SState) : List SState :=
  xs.foldl (fun a q => addUniq q a) acc

-- Reachable layers & cumulative BFS stabilization on `SliceAuto`
def stepList (stepFn : SState → Bool → SState) (l : List SState) : List SState :=
  unionUniq (l.flatMap (fun q => [stepFn q false, stepFn q true])) []

/-- Deduplicated list of all states reachable at bit-depth `i` (for `i ≥ 1`). -/
def layerList (A : SliceAuto) : Nat → List SState
  | 0     => []
  | 1     => unionUniq [A.init1 false, A.init1 true] []
  | i + 2 => stepList (A.step (i + 1)) (layerList A (i + 1))

/-- Cumulative homogeneous reachable states up to depth `A.L + d`. -/
def cumList (A : SliceAuto) : Nat → List SState
  | 0     => layerList A A.L
  | d + 1 => unionUniq (stepList (A.step A.L) (cumList A d)) (cumList A d)

/-- Boolean check whether `cumList A d` is closed under homogeneous transitions `A.step A.L`. -/
def isClosedAt (A : SliceAuto) (d : Nat) : Bool :=
  (stepList (A.step A.L) (cumList A d)).all (fun q => decide (q ∈ cumList A d))

/-- Computable BFS stabilization depth finder (guaranteed to terminate with `isClosedAt = true`). -/
def findStabDepthAux (A : SliceAuto) (d : Nat) : Nat → Nat
  | 0 => d
  | fuel + 1 => if isClosedAt A d then d else findStabDepthAux A (d + 1) fuel

def stabDepth (A : SliceAuto) (card : Nat) : Nat :=
  findStabDepthAux A 0 card

/-- Check `A.out i q == target` on all pre-stabilization layers `1 ≤ i < k`. -/
def checkPreLayers (A : SliceAuto) (target : Bool) : Nat → Bool
  | 0     => true
  | 1     => true
  | i + 2 =>
    checkPreLayers A target (i + 1) &&
    (layerList A (i + 1)).all (fun q => A.out (i + 1) q == target)

/-- Decidable finite-state checker certifying `∀ i ≥ 1, ∀ x : BitVec i, A.out i (A.run x) = target`. -/
def checkAutoConst (A : SliceAuto) (card : Nat) (target : Bool) : Bool :=
  let D := stabDepth A card
  checkPreLayers A target A.L &&
  (cumList A D).all (fun q => A.out A.L q == target)

-- ============================================================================
-- Section 4: `MixedExpr` AST, Pure-Data BSDA Compiler, and Lifting Engine
-- ============================================================================

/-- Mixed bitwise-arithmetic polynomial AST with `+`, `-`, `*`, `^`, `&`, `|`, `~`, `<<`,
    and signed two's-complement integer constants. -/
inductive MixedExpr where
  | var   : MixedExpr
  | const : Int → MixedExpr
  | not   : MixedExpr → MixedExpr
  | shl   : Nat → MixedExpr → MixedExpr
  | add   : MixedExpr → MixedExpr → MixedExpr
  | sub   : MixedExpr → MixedExpr → MixedExpr
  | xor   : MixedExpr → MixedExpr → MixedExpr
  | and   : MixedExpr → MixedExpr → MixedExpr
  | or    : MixedExpr → MixedExpr → MixedExpr
  | mul   : MixedExpr → MixedExpr → MixedExpr
  deriving DecidableEq, Repr

/-- Native `BitVec w` evaluation of `MixedExpr`. -/
def MixedExpr.eval (w : Nat) : MixedExpr → BitVec w → BitVec w
  | .var,     x => x
  | .const c, _ => BitVec.ofInt w c
  | .not e,   x => ~~~(e.eval w x)
  | .shl k e, x => (e.eval w x) <<< k
  | .add a b, x => a.eval w x + b.eval w x
  | .sub a b, x => a.eval w x - b.eval w x
  | .xor a b, x => a.eval w x ^^^ b.eval w x
  | .and a b, x => a.eval w x &&& b.eval w x
  | .or a b,  x => a.eval w x ||| b.eval w x
  | .mul a b, x => a.eval w x * b.eval w x

-- ----------------------------------------------------------------------------
-- 4A. Pure-Data `FullAuto` (Synchronous LSB→MSB Transducer for Mul-Free Exprs)
-- ----------------------------------------------------------------------------

/-- Pure-data synchronous bit transducer (zero `Prop` fields). -/
structure FullAuto where
  init    : SState
  step    : Nat → SState → Bool → SState
  out     : Nat → SState → Bool → Bool
  sigBits : Nat
  card    : Nat

def fullVar : FullAuto :=
  { init := .unit, step := fun _ _ _ => .unit, out := fun _ _ b => b, sigBits := 0, card := 1 }

def fullConst (c : Int) : FullAuto :=
  { init := .unit, step := fun _ _ _ => .unit, out := fun i _ _ => intBit c i,
    sigBits := intSigBits c, card := 1 }

def fullNot (M : FullAuto) : FullAuto :=
  { init := M.init, step := M.step, out := fun i q b => !(M.out i q b),
    sigBits := M.sigBits, card := M.card }

def fullShl (k : Nat) (M : FullAuto) : FullAuto :=
  if k = 0 then M
  else
    { init := .pair M.init (.buf (List.replicate k false))
      step := fun i q b =>
        match q with
        | .pair qm (.buf bs) => .pair (M.step i qm b) (.buf (bs.tail ++ [M.out i qm b]))
        | _ => .unit
      out := fun _ q _ =>
        match q with
        | .pair _ (.buf bs) => bs.headD false
        | _ => false
      sigBits := M.sigBits
      card := M.card * 2 ^ k }

def fullBitwise (op : Bool → Bool → Bool) (Ma Mb : FullAuto) : FullAuto :=
  { init := .pair Ma.init Mb.init
    step := fun i q b =>
      match q with
      | .pair qa qb => .pair (Ma.step i qa b) (Mb.step i qb b)
      | _ => .unit
    out := fun i q b =>
      match q with
      | .pair qa qb => op (Ma.out i qa b) (Mb.out i qb b)
      | _ => false
    sigBits := max Ma.sigBits Mb.sigBits
    card := Ma.card * Mb.card }

def fullAdd (Ma Mb : FullAuto) : FullAuto :=
  { init := .carry Ma.init Mb.init false
    step := fun i q b =>
      match q with
      | .carry qa qb c =>
        let va := Ma.out i qa b
        let vb := Mb.out i qb b
        .carry (Ma.step i qa b) (Mb.step i qb b) ((va && vb) || (va && c) || (vb && c))
      | _ => .unit
    out := fun i q b =>
      match q with
      | .carry qa qb c => (Ma.out i qa b) ^^ (Mb.out i qb b) ^^ c
      | _ => false
    sigBits := max Ma.sigBits Mb.sigBits
    card := 2 * (Ma.card * Mb.card) }

def fullSub (Ma Mb : FullAuto) : FullAuto :=
  { init := .carry Ma.init Mb.init false
    step := fun i q b =>
      match q with
      | .carry qa qb c =>
        let va := Ma.out i qa b
        let vb := Mb.out i qb b
        .carry (Ma.step i qa b) (Mb.step i qb b) ((!va && vb) || (!va && c) || (vb && c))
      | _ => .unit
    out := fun i q b =>
      match q with
      | .carry qa qb c => (Ma.out i qa b) ^^ (Mb.out i qb b) ^^ c
      | _ => false
    sigBits := max Ma.sigBits Mb.sigBits
    card := 2 * (Ma.card * Mb.card) }

/-- Compiler from mul-free `MixedExpr` to pure-data `FullAuto`. -/
def compileFull : MixedExpr → Option FullAuto
  | .var     => some fullVar
  | .const c => some (fullConst c)
  | .not e   => (compileFull e).map fullNot
  | .shl k e => (compileFull e).map (fullShl k)
  | .xor a b => do let ma ← compileFull a; let mb ← compileFull b; some (fullBitwise xor ma mb)
  | .and a b => do let ma ← compileFull a; let mb ← compileFull b; some (fullBitwise and ma mb)
  | .or a b  => do let ma ← compileFull a; let mb ← compileFull b; some (fullBitwise or ma mb)
  | .add a b => do let ma ← compileFull a; let mb ← compileFull b; some (fullAdd ma mb)
  | .sub a b => do let ma ← compileFull a; let mb ← compileFull b; some (fullSub ma mb)
  | .mul _ _ => none

-- ----------------------------------------------------------------------------
-- 4B. Pure-Data `DerivAuto` (BSDA Compiler for Full Nonlinear MixedExpr)
-- ----------------------------------------------------------------------------

/-- Pure-data Bit-Slice Derivative Automaton (zero `Prop` fields). -/
structure DerivAuto where
  bit0 : Bool → Bool
  auto : SliceAuto
  card : Nat

def DerivAuto.checkBijective (D : DerivAuto) : Bool :=
  (D.bit0 true != D.bit0 false) && checkAutoConst D.auto D.card true

def DerivAuto.checkZeroGe1 (D : DerivAuto) : Bool :=
  checkAutoConst D.auto D.card false

/-- Exact finite-slice lifting horizon `W*(e) = L + stabDepth + 1 ≥ 2`. -/
def DerivAuto.horizonW (D : DerivAuto) : Nat :=
  D.auto.L + stabDepth D.auto D.card + 1

def derivConstAuto (b0 : Bool → Bool) (dval : Bool) : DerivAuto :=
  { bit0 := b0
    auto := { init1 := fun _ => .unit, step := fun _ _ _ => .unit, out := fun _ _ => dval, L := 1 }
    card := 1 }

def fullToDeriv (M : FullAuto) : DerivAuto :=
  { bit0 := fun b => M.out 0 M.init b
    auto :=
      { init1 := fun b => M.step 0 M.init b
        step  := M.step
        out   := fun i q => M.out i q true != M.out i q false
        L     := max 1 M.sigBits }
    card := M.card }

def derivNot (D : DerivAuto) : DerivAuto :=
  { bit0 := fun b => !(D.bit0 b), auto := D.auto, card := D.card }

def derivXorPair (Da Db : DerivAuto) : DerivAuto :=
  { bit0 := fun b => Da.bit0 b ^^ Db.bit0 b
    auto :=
      { init1 := fun b => .pair (Da.auto.init1 b) (Db.auto.init1 b)
        step  := fun i q b =>
          match q with
          | .pair qa qb => .pair (Da.auto.step i qa b) (Db.auto.step i qb b)
          | _ => .unit
        out   := fun i q =>
          match q with
          | .pair qa qb => Da.auto.out i qa ^^ Db.auto.out i qb
          | _ => false
        L     := max Da.auto.L Db.auto.L }
    card := Da.card * Db.card }

def derivMul (Da Db : DerivAuto) : DerivAuto :=
  { bit0 := fun b => Da.bit0 b && Db.bit0 b
    auto :=
      { init1 := fun b => .carry (Da.auto.init1 b) (Db.auto.init1 b) b
        step  := fun i q b =>
          match q with
          | .carry qa qb x0 => .carry (Da.auto.step i qa b) (Db.auto.step i qb b) x0
          | _ => .unit
        out   := fun i q =>
          match q with
          | .carry qa qb x0 => (Da.bit0 x0 && Db.auto.out i qb) ^^ (Db.bit0 x0 && Da.auto.out i qa)
          | _ => false
        L     := max Da.auto.L Db.auto.L }
    card := 2 * (Da.card * Db.card) }

/-- Gated bitwise AND/OR: left operand is a zero-deriv `FullAuto` `Ma`, right is any `DerivAuto` `Db`. -/
def derivGateLeft (isOr : Bool) (Ma : FullAuto) (Db : DerivAuto) : DerivAuto :=
  { bit0 := fun b => if isOr then (Ma.out 0 Ma.init b || Db.bit0 b) else (Ma.out 0 Ma.init b && Db.bit0 b)
    auto :=
      { init1 := fun b => .pair (Ma.step 0 Ma.init b) (Db.auto.init1 b)
        step  := fun i q b =>
          match q with
          | .pair qa qb => .pair (Ma.step i qa b) (Db.auto.step i qb b)
          | _ => .unit
        out   := fun i q =>
          match q with
          | .pair qa qb =>
            let maskBit := if isOr then !(Ma.out i qa false) else Ma.out i qa false
            maskBit && Db.auto.out i qb
          | _ => false
        L     := max (max 1 Ma.sigBits) Db.auto.L }
    card := Ma.card * Db.card }

/-- Gated bitwise AND/OR: right operand is a zero-deriv `FullAuto` `Mb`, left is any `DerivAuto` `Da`. -/
def derivGateRight (isOr : Bool) (Da : DerivAuto) (Mb : FullAuto) : DerivAuto :=
  { bit0 := fun b => if isOr then (Da.bit0 b || Mb.out 0 Mb.init b) else (Da.bit0 b && Mb.out 0 Mb.init b)
    auto :=
      { init1 := fun b => .pair (Da.auto.init1 b) (Mb.step 0 Mb.init b)
        step  := fun i q b =>
          match q with
          | .pair qa qb => .pair (Da.auto.step i qa b) (Mb.step i qb b)
          | _ => .unit
        out   := fun i q =>
          match q with
          | .pair qa qb =>
            let maskBit := if isOr then !(Mb.out i qb false) else Mb.out i qb false
            maskBit && Da.auto.out i qa
          | _ => false
        L     := max Da.auto.L (max 1 Mb.sigBits) }
    card := Da.card * Mb.card }

/-- Master BSDA Compiler for `MixedExpr` (handles full Rivest polynomials, arbitrary mul-free
    transducers with unrestricted `&`/`|`/carries/shifts, inert nonlinear `&`/`|`, and
    zero-derivative transducer-gated nonlinear polynomials!). -/
def compileBSDA : MixedExpr → Option DerivAuto
  | .var     => some (derivConstAuto id true)
  | .const c => some (derivConstAuto (fun _ => intBit c 0) false)
  | .not e   => (compileBSDA e).map derivNot
  | .shl k e =>
    if k = 0 then compileBSDA e
    else some (derivConstAuto (fun _ => false) false)
  | .add a b => do let da ← compileBSDA a; let db ← compileBSDA b; some (derivXorPair da db)
  | .sub a b => do let da ← compileBSDA a; let db ← compileBSDA b; some (derivXorPair da db)
  | .xor a b => do let da ← compileBSDA a; let db ← compileBSDA b; some (derivXorPair da db)
  | .mul a b => do let da ← compileBSDA a; let db ← compileBSDA b; some (derivMul da db)
  | .and a b =>
    match compileFull a, compileFull b with
    | some fa, some fb => some (fullToDeriv (fullBitwise and fa fb))
    | mfa, mfb =>
      match compileBSDA a, compileBSDA b with
      | some da, some db =>
        if da.checkZeroGe1 && db.checkZeroGe1 then
          some (derivConstAuto (fun x0 => da.bit0 x0 && db.bit0 x0) false)
        else
          match mfa with
          | some fa => if da.checkZeroGe1 then some (derivGateLeft false fa db) else none
          | none =>
            match mfb with
            | some fb => if db.checkZeroGe1 then some (derivGateRight false da fb) else none
            | none => none
      | _, _ => none
  | .or a b =>
    match compileFull a, compileFull b with
    | some fa, some fb => some (fullToDeriv (fullBitwise or fa fb))
    | mfa, mfb =>
      match compileBSDA a, compileBSDA b with
      | some da, some db =>
        if da.checkZeroGe1 && db.checkZeroGe1 then
          some (derivConstAuto (fun x0 => da.bit0 x0 || db.bit0 x0) false)
        else
          match mfa with
          | some fa => if da.checkZeroGe1 then some (derivGateLeft true fa db) else none
          | none =>
            match mfb with
            | some fb => if db.checkZeroGe1 then some (derivGateRight true da fb) else none
            | none => none
      | _, _ => none

-- ============================================================================
-- Section 5: Infinite Family 1 — Generalized Bitwise-Masked Rivest Theorem
-- ============================================================================

/-- Connective between masked polynomial terms: `+`, `-`, or `^`. -/
inductive Connective where
  | add | sub | xor
  deriving DecidableEq, Repr

/-- A single term `(((coeff * x^deg) <<< shift) &&& mask)` combined via `op`. -/
structure MaskedTerm where
  coeff : Int
  deg   : Nat
  shift : Nat
  mask  : Int
  op    : Connective
  deriving DecidableEq, Repr

def bvPow {w : Nat} (x : BitVec w) : Nat → BitVec w
  | 0     => BitVec.ofInt w 1
  | d + 1 => x * bvPow x d

def evalMaskedTerm (w : Nat) (t : MaskedTerm) (x : BitVec w) : BitVec w :=
  ((BitVec.ofInt w t.coeff * bvPow x t.deg) <<< t.shift) &&& BitVec.ofInt w t.mask

def applyConn {w : Nat} : Connective → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .xor, a, b => a ^^^ b

def evalMaskedPoly (w : Nat) (a0 : Int) : List MaskedTerm → BitVec w → BitVec w
  | [],      _ => BitVec.ofInt w a0
  | t :: ts, x => applyConn t.op (evalMaskedPoly w a0 ts x) (evalMaskedTerm w t x)

def termBit0Deriv (t : MaskedTerm) : Bool :=
  decide (t.shift = 0) && decide (1 ≤ t.deg) && intBit t.coeff 0 && intBit t.mask 0

def termLinDeriv (t : MaskedTerm) (i : Nat) : Bool :=
  decide (t.shift = 0) && decide (t.deg = 1) && intBit t.coeff 0 && intBit t.mask i

def termOddDeriv (t : MaskedTerm) (i : Nat) : Bool :=
  decide (t.shift = 0) && decide (3 ≤ t.deg) && decide (t.deg % 2 = 1) && intBit t.coeff 0 && intBit t.mask i

def xorFold {α : Type _} (f : α → Bool) : List α → Bool
  | []      => false
  | a :: ts => xorFold f ts ^^ f a

/-- **Classical Rivest Theorem (2001) as an Immediate Corollary:**
    For an unmasked polynomial `a0 + a1*x + a2*x^2 + ...` (every mask = `-1`, shift = `0`),
    `maskedHorizon = 2`, so bijectivity ∀ `w ≥ 2` ↔ bijectivity mod 4! -/
def classicalTerms (cs : List Int) (startDeg : Nat := 1) : List MaskedTerm :=
  match cs with
  | [] => []
  | c :: rest => { coeff := c, deg := startDeg, shift := 0, mask := -1, op := .add } ::
                 classicalTerms rest (startDeg + 1)

-- ============================================================================
-- Section 6: Infinite Families 2 & 3 (Carry-Coupled Horizon, Complement-Bridge,
--            Add-XOR Cancellation, and Generalized Klimov-Shamir Criterion)
-- ============================================================================

/-- Carry-coupled pair expression: `F_{c,d}(x) = x + (x &&& (x + c)) + (x &&& (x + d))`. -/
def carryPairExpr (c d : Int) : MixedExpr :=
  .add (.add .var (.and .var (.add .var (.const c)))) (.and .var (.add .var (.const d)))

end MixedPermEngine
