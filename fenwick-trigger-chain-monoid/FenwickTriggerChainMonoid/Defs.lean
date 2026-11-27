/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`fenwick-trigger-chain-monoid`)

Fenwick Low-Bit Trigger-Chain Transducer and Monoid Dichotomy: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace FenwickTransducer


-- ============================================================================
-- SECTION 1: Pure-Silicon Bitwise Primitives & Low-Bit Jump Operators
-- ============================================================================

/-- Trailing zero count v_2(x) for x > 0 (and 0 for x = 0). -/
def ctz (x : Nat) : Nat :=
  if h : x = 0 then 0
  else if x % 2 = 1 then 0
  else 1 + ctz (x / 2)
termination_by x

/-- Population count (Hamming weight) of x. -/
def popcount (x : Nat) : Nat :=
  if h : x = 0 then 0
  else (x % 2) + popcount (x / 2)
termination_by x

/-- Lowest set bit: lowbit(x) = 2^{v_2(x)} for x > 0, and 0 for x = 0. -/
def lowbit (x : Nat) : Nat :=
  if h : x = 0 then 0
  else if x % 2 = 1 then 1
  else 2 * lowbit (x / 2)
termination_by x

/-- Fenwick down-jump (interrogation parent): D(x) = x - lowbit(x). -/
def fenwickD (x : Nat) : Nat := x - lowbit x

/-- Fenwick up-jump (update parent): U(x) = x + lowbit(x). -/
def fenwickU (x : Nat) : Nat := x + lowbit x

/-- Generators of the Fenwick low-bit jump monoid. -/
inductive FenwickOp where
  | D : FenwickOp
  | U : FenwickOp
  deriving DecidableEq, Repr

/-- Apply a word w = [g_L, ..., g_1] right-to-left: (g_L ∘ ... ∘ g_1)(x). -/
def evalWord : List FenwickOp → Nat → Nat
  | [], x => x
  | .D :: v, x => fenwickD (evalWord v x)
  | .U :: v, x => fenwickU (evalWord v x)

/-- Dual word swapping U ↔ D. -/
def dualWord : List FenwickOp → List FenwickOp
  | [] => []
  | .D :: v => .U :: dualWord v
  | .U :: v => .D :: dualWord v

/-- n-fold iteration of an operator f : Nat → Nat. -/
def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => f (iterN f k x)

-- Basic bit-sliced recurrences for lowbit, ctz, popcount, fenwickD, fenwickU

theorem lowbit_zero : lowbit 0 = 0 := by
  unfold lowbit; simp

theorem lowbit_odd (k : Nat) : lowbit (2 * k + 1) = 1 := by
  unfold lowbit; simp

theorem lowbit_even (k : Nat) : lowbit (2 * k) = 2 * lowbit k := by
  cases k with
  | zero => simp [lowbit_zero]
  | succ m =>
    conv => lhs; unfold lowbit
    have h1 : 2 * (m + 1) ≠ 0 := by omega
    have h3 : 2 * (m + 1) / 2 = m + 1 := by omega
    simp [h1, h3]

theorem lowbit_pos {x : Nat} (hx : 0 < x) : 0 < lowbit x := by
  induction x using Nat.strongRecOn with
  | ind n ih =>
    by_cases hodd : n % 2 = 1
    · have : n = 2 * (n / 2) + 1 := by omega
      rw [this, lowbit_odd]; omega
    · have : n = 2 * (n / 2) := by omega
      have hdiv : 0 < n / 2 := by omega
      have hlt : n / 2 < n := by omega
      rw [this, lowbit_even]
      have := ih (n / 2) hlt hdiv
      omega

/-- A deterministic LSB-first Mealy transducer over state space `Q`. -/
structure LsbTransducer (Q : Type) where
  init : Q
  step : Q → Bool → Q × Bool

namespace LsbTransducer


/-- Run transducer `T` starting from state `q` for `n` LSB steps on `x : Nat`.
    Returns `(finalState, outputMod2PowN)`. -/
def run {Q : Type} (T : LsbTransducer Q) : Q → Nat → Nat → Q × Nat
  | q, 0, _ => (q, 0)
  | q, n + 1, x =>
    let (q', bOut) := T.step q (x % 2 == 1)
    let (qFin, rest) := T.run q' n (x / 2)
    (qFin, (if bOut then 1 else 0) + 2 * rest)

/-- Evaluate transducer `T` modulo 2^n on input `x : Nat`. -/
def evalMod {Q : Type} (T : LsbTransducer Q) (n x : Nat) : Nat :=
  (T.run T.init n x).2

/-- Product composition `(T1.compose T2)(x) = T1(T2(x))`. -/
def compose {Q1 Q2 : Type} (T1 : LsbTransducer Q1) (T2 : LsbTransducer Q2) :
    LsbTransducer (Q1 × Q2) where
  init := (T1.init, T2.init)
  step := fun (q1, q2) b =>
    let (q2', bMid) := T2.step q2 b
    let (q1', bOut) := T1.step q1 bMid
    ((q1', q2'), bOut)

/-- Simulation relation between two transducers (finite check on states × Bool). -/
def IsSim {Q1 Q2 : Type} (T1 : LsbTransducer Q1) (T2 : LsbTransducer Q2)
    (R : Q1 → Q2 → Prop) : Prop :=
  ∀ q1 q2 b, R q1 q2 →
    (T1.step q1 b).2 = (T2.step q2 b).2 ∧ R (T1.step q1 b).1 (T2.step q2 b).1

end LsbTransducer


-- ============================================================================
-- SECTION 3: Primitive Fenwick Transducers (T_D, T_U) & TriggerChain Compiler
-- ============================================================================

/-- Identity 1-state LSB transducer. -/
def T_id : LsbTransducer Unit where
  init := ()
  step := fun _ b => ((), b)

/-- 2-state LSB transducer for D(x) = x - lowbit(x). States: false = SEEK, true = COPY. -/
def T_D : LsbTransducer Bool where
  init := false
  step := fun q b =>
    match q with
    | false => if b then (true, false) else (false, false)
    | true => (true, b)

/-- States of the 3-state LSB transducer for U(x) = x + lowbit(x). -/
inductive UState where
  | seek : UState
  | carry : UState
  | copy : UState
  deriving DecidableEq, Repr

/-- 3-state LSB transducer for U(x) = x + lowbit(x). -/
def T_U : LsbTransducer UState where
  init := .seek
  step := fun q b =>
    match q with
    | .seek => if b then (.carry, false) else (.seek, false)
    | .carry => if b then (.carry, false) else (.copy, true)
    | .copy => (.copy, b)

/-- Trigger-chain transducer `C(t, e)` with exact state space `Fin (t.length + 1)`.
    States `0 .. t.length - 1` greedily match subsequence `t`; state `t.length` is COPY.
    When `e = true`, matching the final trigger `t[t.length - 1]` emits `true` (1). -/
def triggerChain (t : List Bool) (e : Bool) : LsbTransducer (Fin (t.length + 1)) where
  init := ⟨0, Nat.zero_lt_succ _⟩
  step := fun q b =>
    if h : q.val < t.length then
      if b == t[q.val] then
        let qNext : Fin (t.length + 1) := ⟨q.val + 1, Nat.succ_lt_succ h⟩
        (qNext, e && (q.val + 1 == t.length))
      else
        (q, false)
    else
      (q, b)

/-- The 4-rule algebraic compiler mapping any word `w ∈ {U, D}*` to `(triggers, emit)`. -/
def compileSpec : List FenwickOp → List Bool × Bool
  | [] => ([], false)
  | .D :: v =>
    let (t, e) := compileSpec v
    if e then (t, false) else (t ++ [true], false)
  | .U :: v =>
    let (t, e) := compileSpec v
    if e then (t ++ [false], true) else (t ++ [true, false], true)

/-- Compiled trigger-chain transducer for a word `w ∈ {U, D}*`. -/
def compileTC (w : List FenwickOp) : LsbTransducer (Fin ((compileSpec w).1.length + 1)) :=
  triggerChain (compileSpec w).1 (compileSpec w).2


/-- Convert an LSB-first bit list to a natural number. -/
def fromBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * fromBits bs

/-- Validity predicate for a TriggerChain: if `e = true`, `t` must end in `false`. -/
def ValidSpec (t : List Bool) (e : Bool) : Prop :=
  e = true → t.getLast? = some false

/-- Explicit enumeration of all words of exact length `k`. -/
def wordsOfLen : Nat → List (List FenwickOp)
  | 0 => [[]]
  | k + 1 => (wordsOfLen k).map (.D :: ·) ++ (wordsOfLen k).map (.U :: ·)

/-- Explicit enumeration of all words of length `< w` (count = 2^w - 1). -/
def wordsLt : Nat → List (List FenwickOp)
  | 0 => []
  | w + 1 => wordsLt w ++ wordsOfLen w

/-- Canonical representatives of all `2^w` distinct elements of `<U_w, D_w>` on `BitVec w`:
    all `2^w - 1` words of length `< w`, plus one representative `D^w` for the zero operator! -/
def finiteMonoidReps (w : Nat) : List (List FenwickOp) :=
  wordsLt w ++ [List.replicate w FenwickOp.D]

/-- Exact number of `fenwickU` steps from `x` to reach `≥ bound` (for `0 < x`). -/
def depthU (x bound : Nat) : Nat :=
  if h : 0 < x ∧ x < bound then
    1 + depthU (fenwickU x) bound
  else
    0
termination_by bound - x
decreasing_by
  have hlb := lowbit_pos h.1
  simp only [fenwickU]
  omega

/-- Perturbed odd-multiplier jump operator `T_3(x) = x + 3 * lowbit(x)`. -/
def jumpT3 (x : Nat) : Nat := x + 3 * lowbit x

-- Helper concrete evaluation lemmas (kernel-checked, zero native_decide)

end FenwickTransducer
