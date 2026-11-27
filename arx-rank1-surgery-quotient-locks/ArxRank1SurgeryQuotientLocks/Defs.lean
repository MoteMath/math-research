/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for ARX Rank-1 Surgery & Speck Quotient Locks (`arx-rank1-surgery-quotient-locks`)

Pure-`Init` (zero Mathlib) definitions of `iter`, `IsMinPeriod`, `swap`, `arxRound`, `arxFermatMap`, `arxAddRot`, `mersenneAddRotShadow`, `msb`, `speckRound`, `InSpeckSubspace`, `ValidSpeckKey`, `speckQuotient`, and `iterKeys`.
-/

namespace ARXInfiniteEngine

/-- Exact `n`-fold iteration of a map `f : α → α`. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

/-- Exact minimal period predicate for a dynamical orbit. -/
def IsMinPeriod {α : Type} (f : α → α) (x : α) (L : Nat) : Prop :=
  0 < L ∧ iter f L x = x ∧ ∀ k, 0 < k → k < L → iter f k x ≠ x

/-- Transposition swapping `a` and `b`, fixing all other elements. -/
def swap {α : Type} [DecidableEq α] (a b x : α) : α :=
  if x = a then b else if x = b then a else x

/-- Parameterized 1-word ARX round map on `BitVec w`: `x ↦ rotL_r(x + c) ⊕ d`. -/
def arxRound (w r : Nat) (c d : BitVec w) (x : BitVec w) : BitVec w :=
  (x + c).rotateLeft r ^^^ d

/-- Most-significant bit mask `2^(w - 1)` in `BitVec w`. -/
def msb (w : Nat) : BitVec w := BitVec.ofNat w (2 ^ (w - 1))

/-- Canonical complement-XOR ARX map: `x ↦ rotL_r(x + 1) ⊕ allOnes`. -/
def arxFermatMap (w r : Nat) (x : BitVec w) : BitVec w :=
  arxRound w r (1#w) (BitVec.allOnes w) x

/-- The pure Add-Rotate map `A w r x = (x + 1#w).rotateLeft r`. -/
def arxAddRot (w r : Nat) (x : BitVec w) : BitVec w :=
  arxRound w r (1#w) (0#w) x

/-- The zero-defect Mersenne shadow `ψ_{w,r}` of `arxAddRot w r`: fixes `allOnes w`,
    and maps `x < 2^w - 1` to `2^r * (x + 1) mod (2^w - 1)`. -/
def mersenneAddRotShadow (w r : Nat) (x : BitVec w) : BitVec w :=
  if x = BitVec.allOnes w then BitVec.allOnes w
  else BitVec.ofNat w ((2 ^ r * (x.toNat + 1)) % (2 ^ w - 1))

/-- Round-varying keyed iteration over a list of round keys `ks`. -/
def iterKeys {α κ : Type} (F : κ → α → α) : List κ → α → α
  | [], x => x
  | k :: ks, x => iterKeys F ks (F k x)

/-- Standard 2-word Speck ARX round function on `(BitVec w × BitVec w)`. -/
def speckRound (w a b : Nat) (k : BitVec w) (p : BitVec w × BitVec w) : BitVec w × BitVec w :=
  let x' := (p.1.rotateRight a + p.2) ^^^ k
  (x', p.2.rotateLeft b ^^^ x')

/-- The `(2*h + 2)`-dimensional `F_2`-linear carry-barrier subspace `V_h ⊂ (BitVec (2*h))²`:
    low `h - 1` bits of `y` vanish, and bits `h .. 2*h - 2` of `x ^^^ y` vanish. -/
def InSpeckSubspace (h : Nat) (p : BitVec (2 * h) × BitVec (2 * h)) : Prop :=
  (∀ i, i < h - 1 → p.2.getLsbD i = false) ∧
  (∀ i, i < h - 1 → (p.1 ^^^ p.2).getLsbD (h + i) = false)

/-- Valid round key for `V_h`: low `h - 1` bits of `k` vanish (`2^(h+1)` keys, arbitrary upper half!). -/
def ValidSpeckKey (h : Nat) (k : BitVec (2 * h)) : Prop :=
  ∀ i, i < h - 1 → k.getLsbD i = false

/-- 2-bit boundary quotient projection `π_h : (BitVec (2*h))² → Bool × Bool`. -/
def speckQuotient (h : Nat) (p : BitVec (2 * h) × BitVec (2 * h)) : Bool × Bool :=
  ((p.1 ^^^ p.2).getLsbD (2 * h - 1), p.2.getLsbD (h - 1))

end ARXInfiniteEngine
