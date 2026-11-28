/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions: Pure-Silicon Bit-Reversal LD-Systems and Non-Alexander XOR-Carry Knot Quandles

Zero-dependency pure-Init Lean 4 definitions pinned by `comparator.json`.
-/

namespace SiliconLDQuandles

/-- A partial involution `τ : α → Option α`: whenever `τ a = some b`, we have `τ b = some a`. -/
def IsPartialInvolution {α : Type u} (τ : α → Option α) : Prop :=
  ∀ a b, τ a = some b → τ b = some a

/-- The partial-involution LD operation `X ⋆_τ Y = X ∪ τ(Y \ X)` on Boolean predicates `α → Bool`. -/
def partialInvLD {α : Type u} (τ : α → Option α) (X Y : α → Bool) : α → Bool :=
  fun i =>
    X i || match τ i with
      | some j => Y j && !(X j)
      | none => false

/-- Bit-reversal on `w`-bit words (`BitVec w`). -/
def bitrev (w : Nat) (x : BitVec w) : BitVec w :=
  x.reverse

/-- Shifted bit-reversal LD operation on `BitVec w`:
`x ⋆_{w,s} y = x ||| ((bitrev w (y &&& ~~~x)) <<< s)`. -/
def bitrevShiftOp (w s : Nat) (x y : BitVec w) : BitVec w :=
  x ||| ((bitrev w (y &&& ~~~x)) <<< s)

/-- Coset-jump quandle operation `x ⋆_g y = y + g (y - x)` on `BitVec w`. -/
def cosetJump {w : Nat} (g : BitVec w → BitVec w) (x y : BitVec w) : BitVec w :=
  y + g (y - x)

/-- Explicit left-inverse of `cosetJump g`: `x ⋆_g⁻¹ z = z - g (z - x)`. -/
def cosetJumpInv {w : Nat} (g : BitVec w → BitVec w) (x z : BitVec w) : BitVec w :=
  z - g (z - x)

/-- Concrete GPU-discovered XOR-carry knot quandle operation on `BitVec w`:
`x ⋆_c y = (2 * x - y) - ((2 * (y - x)) ^^^ c) + c`. -/
def xorCarryOp (w : Nat) (c x y : BitVec w) : BitVec w :=
  (BitVec.ofNat w 2 * x - y) - ((BitVec.ofNat w 2 * (y - x)) ^^^ c) + c

end SiliconLDQuandles
