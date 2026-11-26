/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Binary Lyness Periods (`binary-lyness-periods`)

Pure-`Init` (zero Mathlib) definitions of the 2-register XOR-Feistel step `feistelStep`,
the Binary Lyness recurrence `lynessStep c (x, y) = (y, x ^^^ (y + c))`, and its
bitwise-OR twin `orLynessStep c (x, y) = (y, x ^^^ (y ||| (y + c)))` on unbounded `Nat × Nat`.
-/

namespace BinaryLynessPeriods

/-- One step of the 2-register XOR-Feistel map `F_f(x, y) = (y, x ^^^ f y)` on `Nat × Nat`. -/
def feistelStep (f : Nat → Nat) (p : Nat × Nat) : Nat × Nat :=
  (p.2, p.1 ^^^ f p.2)

/-- `n`-fold iteration of a function `g`. -/
def iter {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter g n (g x)

/-- Binary Lyness step with additive constant `c`: `(x, y) ↦ (y, x ^^^ (y + c))`. -/
def lynessStep (c : Nat) (p : Nat × Nat) : Nat × Nat :=
  feistelStep (fun y => y + c) p

/-- Bitwise-OR Binary Lyness step with constant `c`: `(x, y) ↦ (y, x ^^^ (y ||| (y + c)))`. -/
def orLynessStep (c : Nat) (p : Nat × Nat) : Nat × Nat :=
  feistelStep (fun y => y ||| (y + c)) p

end BinaryLynessPeriods
