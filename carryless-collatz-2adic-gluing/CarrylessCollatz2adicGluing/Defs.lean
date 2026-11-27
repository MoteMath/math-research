/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`CarrylessCollatz2adicGluing`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace Dynsil9
/-- Structurally recursive fuel helper for `v2`. -/
def v2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else if n % 2 = 1 then 0 else v2Aux fuel (n / 2) + 1

/-- Exact 2-adic valuation `v_2(n)` for `n >= 1`, and `0` for `n = 0`. -/
def v2 (n : Nat) : Nat := v2Aux n n

/-- Structurally recursive fuel helper for `clmul`. -/
def clmulAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    if a = 0 then 0
    else (if a % 2 = 1 then b else 0) ^^^ (clmulAux fuel (a / 2) b <<< 1)

/-- Exact carryless multiplication in `F_2[t]` encoded as binary `Nat`. -/
def clmul (a b : Nat) : Nat := clmulAux a a b

/-- Function iteration `T^[j] x`. -/
def iter (T : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | j + 1, x => iter T j (T x)

-- ============================================================================
-- SECTION 2: Reusable Infinite Proof Engine (`ShiftFaithful`)
-- ============================================================================

/--
  A map `T : Nat -> Nat` is `ShiftFaithful` (a 2-adic shift-isometry) if:
    1. `causal`: bit `j < k` of `T x` depends only on bits `0 .. k` of `x` (1-shift Lipschitz).
    2. `flip`: flipping bit `k` of `x` (`x + 2^k`) flips bit `k - 1` of `T x` mod `2^k`.
-/
structure ShiftFaithful (T : Nat → Nat) : Prop where
  causal : ∀ k x y, x % 2 ^ (k + 1) = y % 2 ^ (k + 1) → T x % 2 ^ k = T y % 2 ^ k
  flip   : ∀ k x, 1 ≤ k → T (x + 2 ^ k) % 2 ^ k = (T x + 2 ^ (k - 1)) % 2 ^ k

/-- The `k`-bit parity-vector encoder `Q T k x = sum_{j=0}^{k-1} (T^[j] x % 2) * 2^j`. -/
def Q (T : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => x % 2 + 2 * Q T k (T x)

/--
  Constructive O(k)-step Silicon Hensel Decoder `R T k y`:
  computes the exact unique `x < 2^k` satisfying `Q T k x = y % 2^k`, one bit at a time.
-/
def R (T : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, y =>
    let x := R T k y
    if (iter T k x) % 2 = (y / 2 ^ k) % 2 then x else x + 2 ^ k

/-- Constructive 2-adic transfer conjugacy `Phi T1 T2 k x = R T2 k (Q T1 k x)`. -/
def Phi (T1 T2 : Nat → Nat) (k x : Nat) : Nat :=
  R T2 k (Q T1 k x)

/-- `k`-bit truncation of the periodic bit-stream with period `p >= 1` and pattern `w`. -/
def repWord (p w : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => repWord p w k + ((w / 2 ^ (k % p)) % 2) * 2 ^ k

/-- The Hensel-constructed 2-adic `p`-periodic point associated to parity word `w < 2^p`. -/
def perOrbit (T : Nat → Nat) (p w k : Nat) : Nat :=
  R T k (repWord p w k)

-- ============================================================================
-- SECTION 3: Finite-Table Ultrametric Gluing Certifier (Exact Finite <-> Infinite)
-- ============================================================================

/-- Evaluate a `2^r`-branch carried piecewise-affine map `T(x) = (a_i * x + b_i) / 2`. -/
def evalAffTable (r : Nat) (tab : Nat → Nat × Nat) (x : Nat) : Nat :=
  let (a, b) := tab (x % 2 ^ r)
  (a * x + b) / 2

/-- Decidable bounded universal quantifier `∀ i < n, f i = true`. -/
def allLt (n : Nat) (f : Nat → Bool) : Bool :=
  match n with
  | 0 => true
  | m + 1 => allLt m f && f m

/-- Finite Boolean Ultrametric Gluing Certifier for ANY `2^r`-branch carried table (`r >= 1`). -/
def checkAffTable (r : Nat) (tab : Nat → Nat × Nat) : Bool :=
  let N := 2 ^ r
  let T := evalAffTable r tab
  allLt N (fun i => decide ((tab i).1 % 2 = 1)) &&
  allLt r (fun k =>
    if k = 0 then true
    else allLt N (fun i =>
      decide (T i % 2 ^ k = T (i % 2 ^ (k + 1)) % 2 ^ k) &&
      decide (T (i ^^^ (1 <<< k)) % 2 ^ k = (T i + 2 ^ (k - 1)) % 2 ^ k)))

-- Parametric 2-branch Carried & Carryless Collatz Families

/-- Carried generalized Collatz map: `x / 2` (even), `(a * x + b) / 2` (odd). -/
def TCarried (a b x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else (a * x + b) / 2

/-- Carryless generalized Collatz map: `x / 2` (even), `(clmul p x ^^^ q) / 2` (odd). -/
def TCarryless (p q x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else (clmul p x ^^^ q) / 2

-- ============================================================================
-- SECTION 4: Novel Infinite Theorem I — Universal Carry-vs-Carryless
--            Self-Coding Phase Transition & Finite-Certificate Collapse
-- ============================================================================

/-- Count of `x < n` satisfying predicate `P`. -/
def countLt (n : Nat) (P : Nat → Bool) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => countLt m P + if P m then 1 else 0

/-- Number of `k`-bit self-coding residues `x < 2^k` with `Q T k x = x`. -/
def fixedCount (T : Nat → Nat) (k : Nat) : Nat :=
  countLt (2 ^ k) (fun x => decide (Q T k x = x))

end Dynsil9
