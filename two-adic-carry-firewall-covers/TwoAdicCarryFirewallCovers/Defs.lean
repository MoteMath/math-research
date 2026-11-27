/-!
# Definitions (`TwoAdicCarryFirewallCovers`)

Pure-silicon `Nat` definitions: single-wire clearing, the cover tree and its checker,
the reflected bitwise `Expr` language, firewalled Collatz-type steps, and Gray-quadratic expressions.
-/

namespace AdicCompactness

/-- Exact wire-clearing operator: zeroes bit `k` of `x` without touching any other bit. -/
def clearBitNat (x k : Nat) : Nat :=
  (x / 2 ^ (k + 1)) * 2 ^ (k + 1) + x % 2 ^ k

/-- A finite full binary prefix tree partitioning `Z_2` (and `Nat`) into disjoint
clopen balls `B(r, d) = {r + q * 2^d | q : Nat}` of non-uniform depths `d`. -/
inductive CoverTree (L : Type) where
  | leaf (cert : L)
  | branch (evenChild : CoverTree L) (oddChild : CoverTree L)
  deriving Repr, DecidableEq

/-- Generic decidable checker traversing a `CoverTree` with residue `r` and depth `d`. -/
def checkCover {L : Type} (valid : Nat → Nat → L → Bool) (r d : Nat) : CoverTree L → Bool
  | CoverTree.leaf cert => valid r d cert
  | CoverTree.branch t0 t1 =>
      checkCover valid r (d + 1) t0 && checkCover valid (r + 2 ^ d) (d + 1) t1

/-- Reflected pure-silicon bitwise-arithmetic expression language over `Nat`. -/
inductive Expr where
  | var
  | const (c : Nat)
  | add (e1 e2 : Expr)
  | mul (e1 e2 : Expr)
  | xor (e1 e2 : Expr)
  | and (e1 e2 : Expr)
  | or (e1 e2 : Expr)
  | shl (e : Expr) (s : Nat)
  | shr (e : Expr) (s : Nat)
  | clearBit (e : Expr) (k : Nat)
  | comp (e1 e2 : Expr)
  deriving Repr, DecidableEq

/-- Exact silicon evaluator for `Expr`. -/
def Expr.eval : Expr → Nat → Nat
  | .var, n => n
  | .const c, _ => c
  | .add e1 e2, n => e1.eval n + e2.eval n
  | .mul e1 e2, n => e1.eval n * e2.eval n
  | .xor e1 e2, n => e1.eval n ^^^ e2.eval n
  | .and e1 e2, n => e1.eval n &&& e2.eval n
  | .or e1 e2, n => e1.eval n ||| e2.eval n
  | .shl e s, n => e.eval n <<< s
  | .shr e s, n => e.eval n >>> s
  | .clearBit e k, n => clearBitNat (e.eval n) k
  | .comp e1 e2, n => e1.eval (e2.eval n)

/-- Generic single-wire Bit-`k`-Cleared Collatz-type dynamical step for ANY odd-step core. -/
def firewallStep (oddCore : Nat → Nat) (k n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else clearBitNat (oddCore n) k / 2

/-- Standard iteration `f^[t] n` (defined explicitly to stay zero-dependency). -/
def iterNat (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | t + 1, n => iterNat f t (f n)

/-- Bit-`k`-Cleared Collatz odd core `3n + 1` and step function `T_k`. -/
def collatzCore (n : Nat) : Nat := 3 * n + 1
def TCollatz (k n : Nat) : Nat := firewallStep collatzCore k n

/-- Nonlinear Bit-`k`-Cleared Carryless/XOR-Collatz odd core `(n ^^^ (n <<< 1)) + c`. -/
def xorCollatzCore (c n : Nat) : Nat := (n ^^^ (n <<< 1)) + c
def TXorCollatz (k c n : Nat) : Nat := firewallStep (xorCollatzCore c) k n

/-- Reflected Gray-Quadratic silicon expressions `G(n)^2 + a*n + b`. -/
def grayExpr : Expr := .xor .var (.shr .var 1)

def grayQuadExpr (a b : Nat) : Expr :=
  .add (.add (.mul grayExpr grayExpr) (.mul (.const a) .var)) (.const b)

def shift15Expr : Expr := .shl .var 15

end AdicCompactness
