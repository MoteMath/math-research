/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Definitions (`sorting-operators`)

Pure `Init` (zero Mathlib) definitions of West's stack-sorting operator (`westSort`), single-pass
bubble sort (`bubblePass`), inversion count (`invCnt`), descent count (`desCnt`), and `321` / `231`
pattern counts (`pat321`, `pat231`) on lists of natural numbers.
-/

namespace SortingOperators

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

/-- Number of elements strictly less than `x` in `ys`. -/
def countLt (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if y < x then 1 else 0) + countLt x ys

/-- Number of inversions `(i < j, xs[i] > xs[j])` in `xs`. -/
def invCnt : List Nat → Nat
  | [] => 0
  | x :: xs => countLt x xs + invCnt xs

/-- Number of adjacent descents `(xs[i] > xs[i+1])` in `xs`. -/
def desCnt : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (if x > y then 1 else 0) + desCnt (y :: rest)

/-- Number of pairs `(b, c)` in `ys` (with `b` before `c`) forming a `321`-pattern `(x, b, c)`. -/
def countPairs321 (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if x > y then countLt y ys else 0) + countPairs321 x ys

/-- Total number of `321`-pattern occurrences in `xs`. -/
def pat321 : List Nat → Nat
  | [] => 0
  | x :: xs => countPairs321 x xs + pat321 xs

/-- Number of pairs `(b, c)` in `ys` (with `b` before `c`) forming a `231`-pattern `(x, b, c)`. -/
def countPairs231 (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if y > x then countLt x ys else 0) + countPairs231 x ys

/-- Total number of `231`-pattern occurrences in `xs`. -/
def pat231 : List Nat → Nat
  | [] => 0
  | x :: xs => countPairs231 x xs + pat231 xs

/-- Predicate stating that `xs` avoids the `321` pattern (`pat321 xs = 0`). -/
def Avoids321 (xs : List Nat) : Prop :=
  pat321 xs = 0

end SortingOperators
