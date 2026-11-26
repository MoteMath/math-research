/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Definitions (`weak-bruhat-commutators`)

Pure-`Init` (zero Mathlib) definitions of single-pass and iterated bubble sort (`bubblePass`,
`iterBubble`), West's stack-sorting operator (`westSort`), pop-stack sorting (`popSort`),
the value-inversion set (`IsInv`) defining Left Weak Bruhat Order (`WeakBruhatLe`),
the descent-bottom set (`IsDesBot`, `DesBotSub`), the Bubble-Refined Order (`BubbleLe`),
and the numeric statistics `invCnt`, `desCnt`, `leftInv`.
-/

namespace WeakBruhatCommutators

/-- Bubble-sort carry helper: carries running maximum `m` rightward across `xs`. -/
def bubbleCarry (m : Nat) : List Nat → List Nat
  | [] => [m]
  | y :: rest =>
      if m > y then y :: bubbleCarry m rest
      else m :: bubbleCarry y rest

/-- Single left-to-right bubble-sort pass `B(xs)`. -/
def bubblePass : List Nat → List Nat
  | [] => []
  | x :: xs => bubbleCarry x xs

/-- `k`-fold iterated bubble-sort pass `B^k(xs)`. -/
def iterBubble : Nat → List Nat → List Nat
  | 0, xs => xs
  | k + 1, xs => bubblePass (iterBubble k xs)

/-- West's stack-sorting machine transition `westRun input stack`. -/
def westRun : List Nat → List Nat → List Nat
  | [], stack => stack
  | x :: xs, [] => westRun xs [x]
  | x :: xs, s :: ss =>
      if x > s then s :: westRun (x :: xs) ss
      else westRun xs (x :: s :: ss)
termination_by xs stack => 2 * xs.length + stack.length

/-- West's stack-sorting operator `S(xs)`. -/
def westSort (xs : List Nat) : List Nat :=
  westRun xs []

/-- Pop-stack helper reversing each maximal strictly decreasing run (accumulated in `run`). -/
def popAux : List Nat → List Nat → List Nat
  | [], run => run
  | x :: xs, [] => popAux xs [x]
  | x :: xs, r :: rs =>
      if r > x then popAux xs (x :: r :: rs)
      else (r :: rs) ++ popAux xs [x]

/-- Pop-stack sorting operator `P(xs)`: reverses every maximal descending run. -/
def popSort (xs : List Nat) : List Nat :=
  popAux xs []

/-- `a` appears strictly before `b` in `xs`. -/
def Before (xs : List Nat) (a b : Nat) : Prop :=
  ∃ l₁ l₂ l₃, xs = l₁ ++ a :: l₂ ++ b :: l₃

/-- `(a, b)` is a value-inversion of `xs`: `a > b` and `a` appears before `b` in `xs`. -/
def IsInv (xs : List Nat) (a b : Nat) : Prop :=
  b < a ∧ Before xs a b

/-- `a` appears immediately before `b` in `xs`. -/
def Adj (xs : List Nat) (a b : Nat) : Prop :=
  ∃ l₁ l₂, xs = l₁ ++ a :: b :: l₂

/-- `b` is a descent bottom of `xs`: some `a > b` appears immediately before `b`. -/
def IsDesBot (xs : List Nat) (b : Nat) : Prop :=
  ∃ a, b < a ∧ Adj xs a b

/-- There is an adjacent ascent `u < v` inside the contiguous segment of `xs` from `a` to `b`. -/
def HasAscentBetween (xs : List Nat) (a b : Nat) : Prop :=
  ∃ l₁ l₂ l₃ u v, xs = l₁ ++ a :: l₂ ++ b :: l₃ ∧ u < v ∧ Adj (a :: l₂ ++ [b]) u v

/-- Left Weak Bruhat Order on value-inversion sets: `InvSet(xs) ⊆ InvSet(ys)`. -/
def WeakBruhatLe (xs ys : List Nat) : Prop :=
  ∀ a b, IsInv xs a b → IsInv ys a b

/-- Descent-bottom set inclusion: `DesBot(xs) ⊆ DesBot(ys)`. -/
def DesBotSub (xs ys : List Nat) : Prop :=
  ∀ b, IsDesBot xs b → IsDesBot ys b

/-- Bubble-Refined Order `xs ⪯_B ys`: simultaneous Left Weak Bruhat and descent-bottom inclusion. -/
def BubbleLe (xs ys : List Nat) : Prop :=
  WeakBruhatLe xs ys ∧ DesBotSub xs ys

/-- Number of elements strictly less than `x` in `ys`. -/
def countLt (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if y < x then 1 else 0) + countLt x ys

/-- Number of elements strictly greater than `x` in `ys`. -/
def countGt (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if x < y then 1 else 0) + countGt x ys

/-- Number of inversions in `xs`. -/
def invCnt : List Nat → Nat
  | [] => 0
  | x :: xs => countLt x xs + invCnt xs

/-- Number of adjacent descents in `xs`. -/
def desCnt : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (if x > y then 1 else 0) + desCnt (y :: rest)

/-- Number of elements strictly greater than `b` appearing before the first occurrence of `b` in `xs`. -/
def leftInv (xs : List Nat) (b : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
      if x = b then 0
      else (if b < x then 1 else 0) + leftInv rest b

end WeakBruhatCommutators
