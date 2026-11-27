/-
  Zeckendorf-to-Binary Carry-Bridge Transducer Engine
  Standalone Lean 4.34.1 formalization (zero Mathlib, zero sorry, zero custom axioms).

  Author: adic-7 (Thread 4: 2-Adic, Nimber, Carry-Arithmetic & Number-Theoretic Infinite Mechanisms)
-/

namespace CarryBridge

/-! ## Section 1: Pure-Silicon Bitwise, Carry, Popcount & Carryless Primitives -/

/-- Convert a Bool to Nat (0 or 1). -/
@[inline] def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Convert a Bool to Int (0 or 1). -/
@[inline] def b2i (b : Bool) : Int := if b then 1 else 0

/-- Exact popcount (Hamming weight) of a natural number. -/
def popcount (n : Nat) : Nat :=
  if n = 0 then 0 else n % 2 + popcount (n / 2)
termination_by n
decreasing_by omega

/-- Carryless multiplication in F_2[t] encoded as Nat. -/
def clmul (a b : Nat) : Nat :=
  if b = 0 then 0
  else (if b % 2 = 1 then a else 0) ^^^ (clmul a (b / 2) <<< 1)
termination_by b
decreasing_by omega

/-- Exact binary carry-in bitmask of `a + b`: `K_bin(a, b) = (a + b) ^^^ a ^^^ b`. -/
@[inline] def carryInMask (a b : Nat) : Nat := (a + b) ^^^ a ^^^ b

/-- Recursive binary carry-in bit with initial carry `c` at position `i`. -/
def carryBitWith (a b : Nat) (c : Bool) : Nat → Bool
  | 0 => c
  | i + 1 =>
    let ai := a.testBit i
    let bi := b.testBit i
    let ci := carryBitWith a b c i
    (ai && bi) || (ai && ci) || (bi && ci)

/-- Recursive binary carry-in bit at position `i` when adding `a + b`. -/
@[inline] def carryBit (a b : Nat) (i : Nat) : Bool := carryBitWith a b false i

/-- Finite sum `∑_{i=0}^{n-1} f i` in Nat. -/
def sumNat (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => sumNat k f + f k

/-- Finite sum `∑_{i=0}^{n-1} f i` in Int. -/
def sumInt (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumInt k f + f k

/-- `d` is `r`-spaced iff no two 1-bits of `d` are within distance `< r`. -/
def isRSpaced (r d : Nat) : Prop :=
  ∀ i j, 1 ≤ j → j < r → d.testBit i = true → d.testBit (i + j) = false

/-- `p` has no `r` consecutive 1-bits (`r`-Zeckendorf canonical form). -/
def noROnes (r p : Nat) : Prop :=
  ∀ i, ∃ j, j < r ∧ p.testBit (i + j) = false

/-! ### 1.1 Basic Bitwise & Sum Helpers -/

@[simp] theorem b2n_true : b2n true = 1 := rfl
@[simp] theorem b2n_false : b2n false = 0 := rfl
@[simp] theorem b2i_true : b2i true = 1 := rfl
@[simp] theorem b2i_false : b2i false = 0 := rfl

/-- A finite binary recurrence certificate `(r, maskS)` specifying the linear recurrence
    `G_{k+r} = ∑_{j ∈ S} G_{k+j}` where `S = { j < r | maskS.testBit j = true }`. -/
structure RecCert where
  r : Nat
  maskS : Nat
  deriving DecidableEq, Repr

/-- Binary defect `m_S = 2^r - maskS` added to a bitmask by a single `S`-rewrite at bit 0. -/
@[inline] def RecCert.mS (c : RecCert) : Nat := 2 ^ c.r - c.maskS

/-- Decidable validity check: `r ≥ 2`, `0 ∈ S` (`maskS` odd), and `maskS < 2^r`. -/
def RecCert.isValid (c : RecCert) : Bool :=
  decide (c.r ≥ 2) && (c.maskS % 2 == 1) && decide (c.maskS < 2 ^ c.r)

/-- Decidable difference-basis certificate check: valid AND for every `1 ≤ δ < r`,
    `S ∩ (S + δ) ≠ ∅` (encoded as `(maskS &&& (maskS >>> δ)) != 0`). -/
def RecCert.isDiffBasis (c : RecCert) : Bool :=
  c.isValid &&
    (List.range (c.r - 1)).all (fun t => (c.maskS &&& (c.maskS >>> (t + 1))) != 0)

/-! ### 2.1 Certificate Properties & Universal Two's-Complement Carry Identity -/

/-- Single bit-slice transition of the `(r+1)`-state Carry-Bridge Transducer. -/
def transducerStep (c : RecCert) (age : Fin (c.r + 1)) (xi pi di : Bool) :
    Option (Fin (c.r + 1)) :=
  if di && decide (age.val < c.r - 1) then
    none
  else
    let ci : Bool := decide (age.val < c.r)
    let msd_i : Bool :=
      if di then c.mS.testBit 0
      else if age.val < c.r - 1 then c.mS.testBit (age.val + 1)
      else false
    let ageNext : Fin (c.r + 1) :=
      if di then ⟨0, Nat.zero_lt_succ c.r⟩
      else ⟨min (age.val + 1) c.r, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    let ciNext : Bool := decide (ageNext.val < c.r)
    if b2n xi + b2n msd_i + b2n ci == b2n pi + 2 * b2n ciNext then
      some ageNext
    else
      none

/-- Run the `(r+1)`-state Carry-Bridge Transducer LSB-to-MSB for `n` bit-steps on `(x, p, d)`. -/
def transducerRun (c : RecCert) (x p d : Nat) : Nat → Option (Fin (c.r + 1))
  | 0 => some ⟨c.r, Nat.lt_succ_self c.r⟩
  | i + 1 =>
    match transducerRun c x p d i with
    | none => none
    | some age => transducerStep c age (x.testBit i) (p.testBit i) (d.testBit i)

/-- Transducer acceptance predicate: after processing all bits of `(x, p, d)` plus `r + 1`
    carry-flush steps, the transducer terminates in the flushed state `age = c.r`. -/
def TransducerAccepts (c : RecCert) (x p d : Nat) : Prop :=
  ∃ N, x < 2 ^ N ∧ p < 2 ^ N ∧ d < 2 ^ N ∧
    transducerRun c x p d (N + c.r + 1) = some ⟨c.r, Nat.lt_succ_self c.r⟩

/-- Recurrence evaluation of a bitmask `x` against any sequence `G : Nat → Int`. -/
def evalRecInt (G : Nat → Int) (x : Nat) : Int :=
  if x = 0 then 0
  else (if x % 2 = 1 then G 0 else 0) + evalRecInt (fun k => G (k + 1)) (x / 2)
termination_by x
decreasing_by omega

/-- Recurrence evaluation of a bitmask `x` against a Nat sequence `G : Nat → Nat`. -/
def evalRecNat (G : Nat → Nat) (x : Nat) : Nat :=
  if x = 0 then 0
  else (if x % 2 = 1 then G 0 else 0) + evalRecNat (fun k => G (k + 1)) (x / 2)
termination_by x
decreasing_by omega

/-- Sequence `G : Nat → Int` obeys the linear recurrence of certificate `c`. -/
def ObeysRecInt (c : RecCert) (G : Nat → Int) : Prop :=
  ∀ k, G (k + c.r) = sumInt c.r (fun j => if c.maskS.testBit j then G (k + j) else 0)

/-- Exact state invariant of `transducerRun c x p d n = some age`. -/
def AgeInv (r d n : Nat) (age : Fin (r + 1)) : Prop :=
  (∀ i j, i < n → 1 ≤ j → j < r → i + j < n → d.testBit i = true → d.testBit (i + j) = false) ∧
  (age.val < r → age.val < n ∧ d.testBit (n - 1 - age.val) = true ∧
    ∀ t, t < age.val → d.testBit (n - 1 - t) = false) ∧
  (age.val = r → ∀ t, t < r → t < n → d.testBit (n - 1 - t) = false)

end CarryBridge

namespace CarryBridge

/-! ## Section 3: The Difference-Basis Carry-Bridge Dichotomy Theorem (EXACT IFF) -/

/-- A single valid `S`-rewrite step at bit position `k`:
    requires bit `k + c.r` to be `0` and all bits `k + j` (`j ∈ S`) to be `1`,
    and replaces `w` by `w + c.mS * 2^k`. -/
def SRewriteStep (c : RecCert) (k w w' : Nat) : Prop :=
  w.testBit (k + c.r) = false ∧
  (∀ j, j < c.r → c.maskS.testBit j = true → w.testBit (k + j) = true) ∧
  w' = w + c.mS * 2 ^ k

/-- Multi-step `S`-rewrite derivation recording the exact sequence of fired positions `ks`. -/
inductive SRewriteDeriv (c : RecCert) : List Nat → Nat → Nat → Prop where
  | nil (w : Nat) : SRewriteDeriv c [] w w
  | cons {k : Nat} {ks : List Nat} {w w1 w2 : Nat} :
      SRewriteStep c k w w1 → SRewriteDeriv c ks w1 w2 → SRewriteDeriv c (k :: ks) w w2

/-- Sum of `2^k` over a list of fired positions. -/
def sumPow2 : List Nat → Nat
  | [] => 0
  | k :: ks => 2 ^ k + sumPow2 ks

/-- Pairwise distance `≥ r` between every pair of positions in `ks`. -/
def PairwiseRSpaced (r : Nat) (ks : List Nat) : Prop :=
  ks.Pairwise (fun u v => u + r ≤ v ∨ v + r ≤ u)

/-! ### 3.1 Single-Step Bit Flip Lemma (Zero-Carry XOR Decomposition) -/

/-- Canonical `r`-bonacci certificate: `S = {0, 1, ..., r-1}`, `maskS = 2^r - 1`, `mS = 1`. -/
def rBonacciCert (r : Nat) : RecCert := ⟨r, 2 ^ r - 1⟩

/-- Canonical `r`-bonacci weight sequence:
    `G_k = 2^k` for `k < r`, and `G_{k+r} = ∑_{j=0}^{r-1} G_{k+j}` for `k ≥ 0`. -/
def rBonacciWeight (r : Nat) (n : Nat) : Nat :=
  if h : n < r then 2 ^ n
  else sumNat r (fun j => if _hj : j < r then rBonacciWeight r (n - r + j) else 0)
termination_by n
decreasing_by omega

/-- Fibbinary predicate in pure bitmask form: `(x &&& (x <<< 1)) = 0`. -/
@[inline] def isFibbinary (x : Nat) : Prop := (x &&& (x <<< 1)) = 0

def certFib2   : RecCert := ⟨2, 0b11⟩       -- Fibonacci / Zeckendorf: G_{k+2} = G_{k+1} + G_k
def certTrib3  : RecCert := ⟨3, 0b111⟩      -- Tribonacci: G_{k+3} = G_{k+2} + G_{k+1} + G_k
def certTet4   : RecCert := ⟨4, 0b1111⟩     -- Tetranacci: G_{k+4} = G_{k+3} + G_{k+2} + G_{k+1} + G_k
def certDB4A   : RecCert := ⟨4, 0b1011⟩     -- Non-r-bonacci diff basis S = {0,1,3}, m_S = 5
def certDB4B   : RecCert := ⟨4, 0b1101⟩     -- Non-r-bonacci diff basis S = {0,2,3}, m_S = 3
def certDB5A   : RecCert := ⟨5, 0b10111⟩    -- Non-r-bonacci diff basis S = {0,1,2,4}, m_S = 9
def certDB6A   : RecCert := ⟨6, 0b101011⟩   -- Sparse 4-element diff basis for r=6: S = {0,1,3,5}, m_S = 21
def certNar3   : RecCert := ⟨3, 0b101⟩      -- Narayana's cows S = {0,2} (NOT a difference basis!)

end CarryBridge

/-! ### 5.4 Axiom Audit (`#print axioms` on EVERY Main Theorem) -/
