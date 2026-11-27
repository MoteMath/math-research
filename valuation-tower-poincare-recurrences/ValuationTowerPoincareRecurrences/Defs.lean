/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`ValuationTowerPoincareRecurrences`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace VTPR

/-! ## Section 1: Pure-Silicon `BitVec` 2-Adic & Lowest-Set-Bit Foundations -/

/-- Lowest set bit operator `u &&& (-u)` on `BitVec w`. -/
def lsb {w : Nat} (u : BitVec w) : BitVec w :=
  u &&& (-u)

/-- Bitwise OR fold over a `Fin n`-indexed tuple of bitvectors. -/
def orVec {w : Nat} : {n : Nat} → (Fin n → BitVec w) → BitVec w
  | 0, _ => 0#w
  | _ + 1, v => v 0 ||| orVec (fun i => v i.succ)

/-- Exact 1-bit left-doubling embedding `BitVec w → BitVec (w + 1)` (`x ↦ 2 * x`). -/
def shift2 {w : Nat} (x : BitVec w) : BitVec (w + 1) :=
  BitVec.ofNat (w + 1) (2 * x.toNat)

/-- Standard `n`-fold function iteration. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- State space `(BitVec w)^d` with `d = m + 2 ≥ 2`. -/
abbrev State (m w : Nat) : Type := Fin (m + 2) → BitVec w

/-- Tail view `(x_1, ..., x_{d-1})` of a state vector. -/
def tail {m w : Nat} (x : State m w) : Fin (m + 1) → BitVec w :=
  fun j => x j.succ

/-- General `d`-dimensional subtraction recurrence `F_Φ(x_0, x_1, ..., x_{d-1}) = (x_1, ..., x_{d-1}, Φ(x_1,...,x_{d-1}) - x_0)`. -/
def stepMap {m w : Nat} (Φ : (Fin (m + 1) → BitVec w) → BitVec w) (x : State m w) : State m w :=
  fun i =>
    if h : i.val + 1 < m + 2 then x ⟨i.val + 1, h⟩
    else Φ (tail x) - x 0

/-- Parity-bifurcated Poincaré factor: `lcm(2d, d+1)`. -/
def QFactor (d : Nat) : Nat :=
  if d % 2 = 0 then 2 * d * (d + 1) else d * (d + 1)

/-- Universal global period `Q(d) = lcm(2d, d+1) * (2d - 1)`. -/
def QPeriod (d : Nat) : Nat :=
  QFactor d * (2 * d - 1)

/-! ## Section 3: Reusable Valuation-Tower Poincaré Reduction (VTPR) Engine -/

/--
**Core Reusable Infinite Proof Mechanism (Layer 1 — Primitive VTPR Specification).**
Any nonlinear operator `Φ : (Fin (m + 1) → BitVec w) → BitVec w` satisfying just these
three 2-adic valuation-locking axioms with respect to an odd constant `c : BitVec w`
automatically obeys universal period `Q(m + 2)` on ALL primitive orbits, with ZERO
constraints on `Φ` at valuation `≥ 2` beyond 4-divisibility and sign-invariance!
-/
structure ValuationTowerSpec (m w : Nat)
    (Φ : (Fin (m + 1) → BitVec w) → BitVec w) (c : BitVec w) : Prop where
  /-- Constant `c` is odd (unit in `ℤ/2^wℤ`) whenever `w ≥ 1`. -/
  c_odd : 1 ≤ w → c.getLsbD 0 = true
  /-- Level-0 Odd-Pinning: if any tail coordinate is odd, `Φ v = c`. -/
  level0_odd : ∀ v : Fin (m + 1) → BitVec w,
    (∃ j : Fin (m + 1), (v j).getLsbD 0 = true) → Φ v = c
  /-- Level-1 Double-Pinning: if all tail coordinates are even and some has bit 1 set, `Φ v = 2 * c`. -/
  level1_val1 : ∀ v : Fin (m + 1) → BitVec w,
    (∀ j : Fin (m + 1), (v j).getLsbD 0 = false) →
    (∃ j : Fin (m + 1), (v j).getLsbD 1 = true) → Φ v = 2#w * c
  /-- Level-≥2 Evenness & Sign-Invariance: if all tail coordinates are 4-divisible,
      then `Φ v` is 4-divisible AND `Φ (-v) = Φ v`. -/
  level2_div4 : ∀ v : Fin (m + 1) → BitVec w,
    (∀ j : Fin (m + 1), (v j).getLsbD 0 = false ∧ (v j).getLsbD 1 = false) →
    (Φ v).getLsbD 0 = false ∧ (Φ v).getLsbD 1 = false
  level2_sign_inv : ∀ v : Fin (m + 1) → BitVec w,
    (∀ j : Fin (m + 1), (v j).getLsbD 0 = false ∧ (v j).getLsbD 1 = false) →
    Φ (fun j => -v j) = Φ v

/-- All coordinates are even (`2 ∣ x i`). -/
def allEven {m w : Nat} (e : State m w) : Prop :=
  ∀ i : Fin (m + 2), (e i).getLsbD 0 = false

/-- All coordinates are 4-divisible (`4 ∣ e i`). -/
def allDiv4 {m w : Nat} (e : State m w) : Prop :=
  ∀ i : Fin (m + 2), (e i).getLsbD 0 = false ∧ (e i).getLsbD 1 = false

/-- Involutive coordinate change between `inSection` and `allEven`: `e_0 = c - y_0`, `e_j = y_j`. -/
def toEven {m w : Nat} (c : BitVec w) (y : State m w) : State m w :=
  fun i => if i.val = 0 then c - y 0 else y i

/-- Poincaré return map `ℛ` in even coordinates. -/
def poincareR {m w : Nat} (Φ : (Fin (m + 1) → BitVec w) → BitVec w) (c : BitVec w)
    (e : State m w) : State m w :=
  fun i =>
    if i.val = 0 then e ⟨m + 1, by omega⟩
    else if i.val = 1 then (2#w * c - Φ (tail e)) - e 0
    else e ⟨i.val - 1, by omega⟩

/-- Linear signed-shift Poincaré monodromy `M = ℛ^{d+1}` on 4-divisible states. -/
def monodromyM {m w : Nat} (e : State m w) : State m w :=
  fun i =>
    if i.val = 0 then -e ⟨m + 1, by omega⟩
    else if i.val = 1 then e 0
    else -e ⟨i.val - 1, by omega⟩

/-! ### Step 3E: Layer 2 — 2-Adic Valuation-Homogeneity Tower Lifter (Full Space `∀ w, ∀ x`) -/

/--
**Reusable Infinite Proof Mechanism (Layer 2 — 2-Adic Valuation-Homogeneous Tower Lifter):**
If a family of operators `Φ : ∀ w, (Fin (m + 1) → BitVec w) → BitVec w` with multipliers
`c : ∀ w, BitVec w` satisfies `ValuationTowerSpec` at every width `w` AND commutes with
the 1-bit doubling embedding `shift2` (`Φ_{w+1}(2v) = 2 * Φ_w(v)`), then:
1. Joint lowest-set-bit `V(x) = lsb(x_0 ||| ... ||| x_{d-1})` is an EXACT CONSERVED INVARIANT
   at EVERY width `w : Nat` and EVERY state `x : State m w`!
2. `stepMap (Φ w)` has universal global period `QPeriod (m + 2)` on ALL states (primitive
   and non-primitive, across all valuation strata `k = 0, 1, ..., w`)!
-/
structure ValuationHomogeneousSpec (m : Nat)
    (Φ : ∀ w, (Fin (m + 1) → BitVec w) → BitVec w)
    (c : ∀ w, BitVec w) : Prop where
  tower : ∀ w, ValuationTowerSpec m w (Φ w) (c w)
  shift2_hom : ∀ (w : Nat) (v : Fin (m + 1) → BitVec w),
    Φ (w + 1) (fun j => shift2 (v j)) = shift2 (Φ w v)

/-- Twisted joint-LSB operator `Φ_c(x_1,...,x_{d-1}) = c * lsb(x_1 ||| ... ||| x_{d-1})`. -/
def twistedLSBPhi {m w : Nat} (c : BitVec w) (v : Fin (m + 1) → BitVec w) : BitVec w :=
  c * lsb (orVec v)

/-- Step map of the `d`-dimensional Twisted Joint-LSB Subtraction Recurrence. -/
def twistedLSBStep {m w : Nat} (c : BitVec w) : State m w → State m w :=
  stepMap (twistedLSBPhi c)

/-! ### 4B: Family 2 — Non-Homogeneous Wild Quadratic Family (Non-Transducer VTPR Generality) -/

/-- Sum of squares `∑ v_j^2` over a `Fin n`-indexed tuple of bitvectors. -/
def sumSq {w : Nat} : {n : Nat} → (Fin n → BitVec w) → BitVec w
  | 0, _ => 0#w
  | _ + 1, v => v 0 * v 0 + sumSq (fun i => v i.succ)

/-- Non-homogeneous, non-transducer operator with quadratic squaring at valuation `≥ 2`. -/
def wildQuadPhi {m w : Nat} (c : BitVec w) (v : Fin (m + 1) → BitVec w) : BitVec w :=
  let u := orVec v
  if u.getLsbD 0 then c
  else if u.getLsbD 1 then 2#w * c
  else 4#w * sumSq v

/-! ### 4C: Universal Exact Minimal Period Theorem (`∀ d ≥ 2, ∀ w ≥ 4, ∀ Φ ∈ VTPR`) -/

/-- Universal exact-period witness `v*_d = (1, 0, ..., 0, 4) ∈ (BitVec w)^d`. -/
def universalWitness (m w : Nat) : State m w :=
  fun i => if i.val = 0 then 1#w else if i.val = m + 1 then 4#w else 0#w

end VTPR
