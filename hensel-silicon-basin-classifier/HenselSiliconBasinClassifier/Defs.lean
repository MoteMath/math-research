/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`hensel-silicon-basin-classifier`)

2-Adic Hensel-Contraction Fixed-Point and Basin Classifier: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace HenselSilicon


/-! ## Helper Iteration, Bitwise & Arithmetic Lemmas -/

def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x     => x
  | n + 1, x => f (iter f n x)

def bvClmulAux {w : Nat} (a b : BitVec w) : Nat → BitVec w
  | 0     => 0#w
  | i + 1 =>
    let prev := bvClmulAux a b i
    if b.getLsbD i then prev ^^^ (a <<< i) else prev

def bvClmul {w : Nat} (a b : BitVec w) : BitVec w :=
  bvClmulAux a b w

inductive BPoly where
  | var   : BPoly
  | const : Nat → BPoly
  | add   : BPoly → BPoly → BPoly
  | sub   : BPoly → BPoly → BPoly
  | mul   : BPoly → BPoly → BPoly
  | xor   : BPoly → BPoly → BPoly
  | and   : BPoly → BPoly → BPoly
  | or    : BPoly → BPoly → BPoly
  | not   : BPoly → BPoly
  | shl   : BPoly → Nat → BPoly
  | clmul : BPoly → BPoly → BPoly
  deriving Repr, DecidableEq

def BPoly.eval : BPoly → {w : Nat} → BitVec w → BitVec w
  | .var, _, x        => x
  | .const c, w, _    => BitVec.ofNat w c
  | .add a b, _, x    => a.eval x + b.eval x
  | .sub a b, _, x    => a.eval x - b.eval x
  | .mul a b, _, x    => a.eval x * b.eval x
  | .xor a b, _, x    => a.eval x ^^^ b.eval x
  | .and a b, _, x    => a.eval x &&& b.eval x
  | .or  a b, _, x    => a.eval x ||| b.eval x
  | .not a, _, x      => ~~~(a.eval x)
  | .shl a s, _, x    => a.eval x <<< s
  | .clmul a b, _, x  => bvClmul (a.eval x) (b.eval x)

/-- Exact evaluation of bit 0 of a `BPoly` expression from bit 0 of `x`. -/
def BPoly.evalBit0 : BPoly → Bool → Bool
  | .var, x0        => x0
  | .const c, _     => c.testBit 0
  | .add a b, x0    => a.evalBit0 x0 ^^ b.evalBit0 x0
  | .sub a b, x0    => a.evalBit0 x0 ^^ b.evalBit0 x0
  | .mul a b, x0    => a.evalBit0 x0 && b.evalBit0 x0
  | .xor a b, x0    => a.evalBit0 x0 ^^ b.evalBit0 x0
  | .and a b, x0    => a.evalBit0 x0 && b.evalBit0 x0
  | .or  a b, x0    => a.evalBit0 x0 || b.evalBit0 x0
  | .not a, x0      => !(a.evalBit0 x0)
  | .shl a s, x0    => if s == 0 then a.evalBit0 x0 else false
  | .clmul a b, x0  => a.evalBit0 x0 && b.evalBit0 x0

mutual
  def BPoly.vanishesAbove (m : Nat) : BPoly → Bool
    | .const c   => decide (c < 2 ^ m)
    | .and a b   => a.vanishesAbove m || b.vanishesAbove m
    | .or  a b   => a.vanishesAbove m && b.vanishesAbove m
    | .xor a b   => a.vanishesAbove m && b.vanishesAbove m
    | .not a     => a.allOnesAbove m
    | _          => false

  def BPoly.allOnesAbove (m : Nat) : BPoly → Bool
    | .not a     => a.vanishesAbove m
    | .or  a b   => a.allOnesAbove m || b.allOnesAbove m
    | .and a b   => a.allOnesAbove m && b.allOnesAbove m
    | _          => false
end

/-- 3-valued abstract bit-derivative: provably 0 (contracting), provably 1 (isometric), or unknown. -/
inductive AbsBit where
  | zero : AbsBit
  | one  : AbsBit
  | top  : AbsBit
  deriving Repr, DecidableEq

def AbsBit.xor : AbsBit → AbsBit → AbsBit
  | .zero, b    => b
  | a, .zero    => a
  | .one, .one  => .zero
  | _, _        => .top

def AbsBit.scale (b : Bool) (d : AbsBit) : AbsBit :=
  if b then d else .zero

/--
  Computable 3-valued abstract 2-adic bit-derivative compiler for `BPoly` at threshold `m ≥ 1`.
  When `absDeriv m e x0 = .zero`, `e` is strictly 2-contracting at every bit `k ≥ m` on inputs
  with LSB `x0`. When `.one`, `e` is strictly isometric (bit-flips propagate 1-to-1) at bit `k ≥ m`.
-/
def BPoly.absDeriv (m : Nat) : BPoly → Bool → AbsBit
  | .var, _       => .one
  | .const _, _   => .zero
  | .add a b, x0  => AbsBit.xor (a.absDeriv m x0) (b.absDeriv m x0)
  | .sub a b, x0  => AbsBit.xor (a.absDeriv m x0) (b.absDeriv m x0)
  | .xor a b, x0  => AbsBit.xor (a.absDeriv m x0) (b.absDeriv m x0)
  | .not a, x0    => a.absDeriv m x0
  | .shl a s, x0  => if s == 0 then a.absDeriv m x0 else .zero
  | .mul a b, x0  =>
      AbsBit.xor (AbsBit.scale (a.evalBit0 x0) (b.absDeriv m x0))
                 (AbsBit.scale (b.evalBit0 x0) (a.absDeriv m x0))
  | .clmul a b, x0 =>
      AbsBit.xor (AbsBit.scale (a.evalBit0 x0) (b.absDeriv m x0))
                 (AbsBit.scale (b.evalBit0 x0) (a.absDeriv m x0))
  | .and a b, x0  =>
      if a.vanishesAbove m || b.vanishesAbove m then .zero
      else if a.allOnesAbove m then b.absDeriv m x0
      else if b.allOnesAbove m then a.absDeriv m x0
      else match a.absDeriv m x0, b.absDeriv m x0 with
           | .zero, .zero => .zero
           | _, _         => .top
  | .or a b, x0   =>
      if a.allOnesAbove m || b.allOnesAbove m then .zero
      else if a.vanishesAbove m then b.absDeriv m x0
      else if b.vanishesAbove m then a.absDeriv m x0
      else match a.absDeriv m x0, b.absDeriv m x0 with
           | .zero, .zero => .zero
           | _, _         => .top

def AbsBit.Satisfies (d : AbsBit) (dx dy : Bool) : Prop :=
  match d with
  | .zero => dy = false
  | .one  => dy = dx
  | .top  => True

/-- A width-polymorphic map `F` is a T-function (1-Lipschitz in the 2-adic metric)
    if it commutes with bit-width truncation `BitVec.setWidth`. -/
def IsTFunc (F : ∀ w, BitVec w → BitVec w) : Prop :=
  ∀ {w k : Nat}, k ≤ w → ∀ x : BitVec w,
    BitVec.setWidth k (F w x) = F k (BitVec.setWidth k x)

/-- Residue-class-localized 2-adic contraction above bit `m`: whenever `x` lies in
    the residue class `P` mod `2^m` and `x, y` agree on bits `0..k-1` (`m ≤ k < w`),
    `F w x` and `F w y` agree on bits `0..k`. -/
def IsContractingOn (F : ∀ w, BitVec w → BitVec w) (m : Nat) (P : BitVec m → Bool) : Prop :=
  ∀ {w k : Nat}, m ≤ k → k < w → ∀ x y : BitVec w,
    P (BitVec.setWidth m x) = true →
    BitVec.setWidth k x = BitVec.setWidth k y →
    BitVec.setWidth (k + 1) (F w x) = BitVec.setWidth (k + 1) (F w y)

/-- Decidable finite certificate checking `absDeriv m e (r.getLsbD 0) = .zero`
    for all `r : BitVec m` with `P r = true`. -/
def BPoly.checkContractingOn (e : BPoly) (m : Nat) (P : BitVec m → Bool) : Bool :=
  (List.range (2 ^ m)).all (fun n =>
    let r := BitVec.ofNat m n
    !P r || (e.absDeriv m (r.getLsbD 0) == .zero))

/-- Number of contracting steps along the mod-`2^m` orbit of `r` during `t` iterations. -/
def cycleContractionCount (F : ∀ w, BitVec w → BitVec w) (m : Nat)
    (P : BitVec m → Bool) (r : BitVec m) : Nat → Nat
  | 0     => 0
  | t + 1 =>
    cycleContractionCount F m P r t +
      if P (iter (F m) t r) then 1 else 0

/-- Exact ceiling quotient `⌈(w - m) / c⌉` of cycle rounds required for complete width-`w` contraction. -/
def henselRounds (w m c : Nat) : Nat :=
  (w - m + c - 1) / c

/-- Constructive Hensel lift of a mod-`2^m` periodic point `r` of period `L` with
    cycle-contraction count `c ≥ 1` to bit-width `w ≥ m`. -/
def henselLift (F : ∀ w, BitVec w → BitVec w) (m L c w : Nat) (r : BitVec m) : BitVec w :=
  iter (F w) (henselRounds w m c * L) (BitVec.setWidth w r)

/-- Exact cardinality of `{x : BitVec w | Q x = true}` over all `2^w` bit-vectors. -/
def bvCount (w : Nat) (Q : BitVec w → Bool) : Nat :=
  (List.range (2 ^ w)).countP (fun n => Q (BitVec.ofNat w n))

def isPeriodicB (F : ∀ w, BitVec w → BitVec w) (L w : Nat) (x : BitVec w) : Bool :=
  iter (F w) L x == x

def isFixedPointB (F : ∀ w, BitVec w → BitVec w) (w : Nat) (x : BitVec w) : Bool :=
  F w x == x

/-- Decidable finite check at width `m` that every `L`-periodic point of `F m`
    has at least one contracting step along its `L`-cycle. -/
def checkPeriodicContracting (F : ∀ w, BitVec w → BitVec w) (m L : Nat)
    (P : BitVec m → Bool) : Bool :=
  (List.range (2 ^ m)).all (fun n =>
    let r := BitVec.ofNat m n
    !(iter (F m) L r == r) || decide (1 ≤ cycleContractionCount F m P r L))

/-- Decidable finite check at width `m` that every `r : BitVec m` enters a fixed point
    in at most `dMax` steps. -/
def checkAllReachFixed (F : ∀ w, BitVec w → BitVec w) (m dMax : Nat) : Bool :=
  (List.range (2 ^ m)).all (fun n =>
    let r := BitVec.ofNat m n
    let y := iter (F m) dMax r
    F m y == y)

/-- Exact basin predicate at depth `D` for a fixed point `xStar`: `iter (F w) D x == xStar`. -/
def inFixedBasinAt (F : ∀ w, BitVec w → BitVec w) (w D : Nat) (xStar x : BitVec w) : Bool :=
  iter (F w) D x == xStar

def mapAsym : BPoly := .or (.and .var (.const 4)) (.mul .var .var)

def mapSeven : BPoly := .or (.and .var (.const 6)) (.mul .var .var)

def mapThree : BPoly := .add (.or (.and .var (.const 4)) (.mul .var .var)) (.const 2)

def mapXorAdd (c : Nat) : BPoly := .xor .var (.add .var (.const c))

def mapClmulHybrid : BPoly :=
  .xor (.xor (.clmul .var .var) (.add .var (.const 1))) .var

/-- `g(x) = x^3 + x^2 + 2`: `g'(1) = 5 ≡ 1 (mod 2)` (NOT globally contracting!),
    yet every orbit enters the contracting even class in 1 step! -/
def mapLocalEven : BPoly :=
  .add (.add (.mul (.mul .var .var) .var) (.mul .var .var)) (.const 2)

def isEven1 (r : BitVec 1) : Bool := r == 0#1

/-- `f(x) = x^3 + 2x + 1`: half-cycle contraction (`c = 1` out of `L = 2`),
    contracting on even inputs and isometric on odd inputs! -/
def mapHalfCycle : BPoly :=
  .add (.add (.mul (.mul .var .var) .var) (.mul (.const 2) .var)) (.const 1)

/-- Exact 2-adic distance `2^(-k)`: `x` and `y` agree on bits `< k` and differ on bit `k`. -/
def v2Exact {w : Nat} (k : Nat) (x y : BitVec w) : Prop :=
  BitVec.setWidth k x = BitVec.setWidth k y ∧ x.getLsbD k ≠ y.getLsbD k

/-- Counterexample 1: `x^3 + 2x` has `f'(1) ≡ 1 (mod 2)` (isometric on odd inputs),
    so its fixed-point count drops from 2 at `w = 1` to 1 at `w = 2`. -/
def mapMixedIso : BPoly :=
  .add (.mul (.mul .var .var) .var) (.mul (.const 2) .var)

/-- Counterexample 4: Even under global 2-adic contraction above `m = 3`, a 4-cycle can have
    convergence depth strictly exceeding `w` (`depth = 4 > 3 = w` at `x = 3#3`), contrasting
    sharply with `tfunc_fixedPoint_depth_le_width` (`≤ w` for all fixed points). -/
def mapCycle4 : BPoly := .add (.or (.and .var (.const 6)) (.mul .var .var)) (.const 1)

end HenselSilicon
