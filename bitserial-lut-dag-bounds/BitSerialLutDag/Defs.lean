/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`BitSerialLutDag.Defs`)

Pure-`Init` (zero Mathlib) definitions for:
- Finite sums over `Fin n` (`Int`, `Nat`, `Rat`) and integer dot products.
- 2-input linear DAGs (`LinearGate`, `LinearDag g`) with exact coefficient-vector
  semantics, input-evaluation semantics, critical-path depth, and gate-set classes
  (`isPureAddSub`, `isRdna3AddLshl`).
- Sign-folded binary and balanced-ternary codebooks, exact lower bounds, and `ceilLog2`.
- Bit-serial `POPCNT` dot-product evaluators for binary and ternary weights against
  arbitrary `b`-bit signed (two's-complement) or unsigned activations.
- Exact rational LUT-vs-`POPCNT` amortization cost model and signed `int16` overflow
  / wrap-around definitions.
-/

namespace BitSerialLutDag

/-! ## Finite Sums & Dot Products -/

def finSumAuxInt {n : Nat} (f : Fin n → Int) : (k : Nat) → k ≤ n → Int
  | 0, _ => 0
  | k + 1, hk => finSumAuxInt f k (Nat.le_of_succ_le hk) + f ⟨k, hk⟩

def finSumInt {n : Nat} (f : Fin n → Int) : Int :=
  finSumAuxInt f n (Nat.le_refl n)

def finSumAuxNat {n : Nat} (f : Fin n → Nat) : (k : Nat) → k ≤ n → Nat
  | 0, _ => 0
  | k + 1, hk => finSumAuxNat f k (Nat.le_of_succ_le hk) + f ⟨k, hk⟩

def finSumNat {n : Nat} (f : Fin n → Nat) : Nat :=
  finSumAuxNat f n (Nat.le_refl n)

def dotInt {n : Nat} (w a : Fin n → Int) : Int :=
  finSumInt (fun i => w i * a i)

/-! ## Ceiling Log2 & Exact Codebook Sizes / Lower Bounds -/

def ceilLog2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then 0
    else 1 + ceilLog2Aux fuel ((n + 1) / 2)

/-- Exact ceiling base-2 logarithm: `ceilLog2 0 = 0`, `ceilLog2 1 = 0`,
    and for all `n ≥ 1`, `ceilLog2 n ≤ d ↔ n ≤ 2 ^ d`. -/
def ceilLog2 (n : Nat) : Nat :=
  ceilLog2Aux n n

/-- Universal 2-input linear DAG lower bound for sign-folded binary LUT (`g ≥ 2`). -/
def binaryLowerBound (g : Nat) : Nat :=
  2 ^ (g - 1) + g - 2

/-- Exact size of the sign-folded nonzero ternary codebook `{-1, 0, +1}^g / {±1}`. -/
def ternaryFoldedSize (g : Nat) : Nat :=
  (3 ^ g - 1) / 2

/-- Universal 2-input linear DAG lower bound for sign-folded ternary LUT (`g` inputs free). -/
def ternaryLowerBound (g : Nat) : Nat :=
  ternaryFoldedSize g - g

/-! ## 2-Input Linear DAG Model -/

/-- A single 2-input linear operation `c1 * w[u] + c2 * w[v]`. -/
structure LinearGate where
  u : Nat
  v : Nat
  c1 : Int
  c2 : Int
  deriving DecidableEq, Repr

/-- Pure `{+, -}` gate (`w[u] + w[v]` or `w[u] - w[v]`). -/
def LinearGate.isPureAddSub (gate : LinearGate) : Prop :=
  gate.c1 = 1 ∧ (gate.c2 = 1 ∨ gate.c2 = -1)

/-- RDNA 3 `V_ADD_LSHL_U32` / `V_SUB_LSHL` gate (`c1, c2 ∈ {-2, -1, +1, +2}`). -/
def LinearGate.isRdna3AddLshl (gate : LinearGate) : Prop :=
  (gate.c1 = 1 ∨ gate.c1 = -1 ∨ gate.c1 = 2 ∨ gate.c1 = -2) ∧
  (gate.c2 = 1 ∨ gate.c2 = -1 ∨ gate.c2 = 2 ∨ gate.c2 = -2)

/-- A 2-input linear DAG on `g` input wires `0 .. g-1` and `gates.length` gate wires `g .. g+L-1`. -/
structure LinearDag (g : Nat) where
  gates : List LinearGate
  deriving DecidableEq, Repr

/-- Acyclicity / well-formedness: gate `k` (at wire `g + k`) only reads wires `< g + k`. -/
def LinearDag.Valid {g : Nat} (dag : LinearDag g) : Prop :=
  ∀ (k : Nat) (gate : LinearGate), dag.gates[k]? = some gate →
    gate.u < g + k ∧ gate.v < g + k

def LinearDag.isPureAddSub {g : Nat} (dag : LinearDag g) : Prop :=
  ∀ gate ∈ dag.gates, gate.isPureAddSub

def LinearDag.isRdna3AddLshl {g : Nat} (dag : LinearDag g) : Prop :=
  ∀ gate ∈ dag.gates, gate.isRdna3AddLshl

/-- Unit basis vector `e_m` in `ℤ^g`. -/
def unitVec (g : Nat) (m : Nat) : Fin g → Int :=
  fun j => if j.val = m then 1 else 0

/-- Structural-fuel evaluator for wire coefficient vectors `w_m ∈ ℤ^g` (exact for `m ≤ fuel`). -/
def evalWireCoeffAux {g : Nat} (dag : LinearDag g) : Nat → Nat → Fin g → Int
  | 0, m => if m < g then unitVec g m else fun _ => 0
  | fuel + 1, m =>
    if m < g then
      unitVec g m
    else
      match dag.gates[m - g]? with
      | none => fun _ => 0
      | some gate =>
        if gate.u < m ∧ gate.v < m then
          fun j =>
            gate.c1 * evalWireCoeffAux dag fuel gate.u j +
            gate.c2 * evalWireCoeffAux dag fuel gate.v j
        else
          fun _ => 0

/-- Exact coefficient vector `w_m ∈ ℤ^g` computed by wire `m` of `dag`. -/
def evalWireCoeff {g : Nat} (dag : LinearDag g) (m : Nat) : Fin g → Int :=
  evalWireCoeffAux dag m m

/-- Structural-fuel evaluator for wire values on input `x : Fin g → Int` (exact for `m ≤ fuel`). -/
def evalWireValAux {g : Nat} (dag : LinearDag g) (x : Fin g → Int) : Nat → Nat → Int
  | 0, m => if h : m < g then x ⟨m, h⟩ else 0
  | fuel + 1, m =>
    if h : m < g then
      x ⟨m, h⟩
    else
      match dag.gates[m - g]? with
      | none => 0
      | some gate =>
        if gate.u < m ∧ gate.v < m then
          gate.c1 * evalWireValAux dag x fuel gate.u +
          gate.c2 * evalWireValAux dag x fuel gate.v
        else
          0

/-- Exact integer value computed by wire `m` of `dag` on arbitrary input vector `x : Fin g → Int`. -/
def evalWireVal {g : Nat} (dag : LinearDag g) (x : Fin g → Int) (m : Nat) : Int :=
  evalWireValAux dag x m m

/-- Structural-fuel evaluator for critical-path depth of wire `m` (exact for `m ≤ fuel`). -/
def wireDepthAux {g : Nat} (dag : LinearDag g) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, m =>
    if m < g then
      0
    else
      match dag.gates[m - g]? with
      | none => 0
      | some gate =>
        if gate.u < m ∧ gate.v < m then
          1 + max (wireDepthAux dag fuel gate.u) (wireDepthAux dag fuel gate.v)
        else
          0

/-- Critical-path depth of wire `m` in `dag` (inputs have depth `0`). -/
def wireDepth {g : Nat} (dag : LinearDag g) (m : Nat) : Nat :=
  wireDepthAux dag m m

def maxWireDepthUpTo {g : Nat} (dag : LinearDag g) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxWireDepthUpTo dag n) (wireDepth dag n)

/-- Critical-path depth of the entire DAG `dag`. -/
def dagDepth {g : Nat} (dag : LinearDag g) : Nat :=
  maxWireDepthUpTo dag (g + dag.gates.length)

/-- Number of nonzero coordinates of `w : Fin g → Int`. -/
def supportSize {g : Nat} (w : Fin g → Int) : Nat :=
  finSumNat (fun j => if w j ≠ 0 then 1 else 0)

/-- Full support: every coordinate of `w` is nonzero. -/
def isFullSupport {g : Nat} (w : Fin g → Int) : Prop :=
  ∀ j : Fin g, w j ≠ 0

/-! ## Binary & Balanced-Ternary Codebooks -/

/-- Sign-canonical binary target `idx ∈ Fin (2^(g-1))`: coordinate `0` is `+1`,
    and coordinate `j > 0` is `-1` if bit `j - 1` of `idx` is set, else `+1`. -/
def binaryTarget (g : Nat) (idx : Fin (2 ^ (g - 1))) : Fin g → Int :=
  fun j =>
    if j.val = 0 then 1
    else if idx.val.testBit (j.val - 1) then -1 else 1

/-- `dag` computes every sign-canonical binary target in `{-1, +1}^g / {±1}`. -/
def computesAllBinary {g : Nat} (dag : LinearDag g) : Prop :=
  ∀ idx : Fin (2 ^ (g - 1)), ∃ m < g + dag.gates.length,
    evalWireCoeff dag m = binaryTarget g idx

/-- Balanced-ternary digit extraction for nonnegative integer `n` at position `j`. -/
def balTernDigit : Nat → Nat → Int
  | 0, n =>
    match n % 3 with
    | 0 => 0
    | 1 => 1
    | _ => -1
  | j + 1, n =>
    let q := match n % 3 with
      | 2 => n / 3 + 1
      | _ => n / 3
    balTernDigit j q

/-- Sign-canonical ternary target `idx ∈ Fin (ternaryFoldedSize g)`, corresponding to
    the unique balanced-ternary representation of `idx.val + 1 ∈ [1, (3^g - 1)/2]`. -/
def ternaryTarget (g : Nat) (idx : Fin (ternaryFoldedSize g)) : Fin g → Int :=
  fun j => balTernDigit j.val (idx.val + 1)

/-- `dag` computes every sign-canonical nonzero ternary target in `{-1, 0, +1}^g / {±1}`. -/
def computesAllTernary {g : Nat} (dag : LinearDag g) : Prop :=
  ∀ idx : Fin (ternaryFoldedSize g), ∃ m < g + dag.gates.length,
    evalWireCoeff dag m = ternaryTarget g idx

/-- Bounded-support `(≤ k, g)` ternary target predicate. -/
def computesBoundedTernary {g : Nat} (dag : LinearDag g) (k : Nat) : Prop :=
  ∀ idx : Fin (ternaryFoldedSize g), supportSize (ternaryTarget g idx) ≤ k →
    ∃ m < g + dag.gates.length, evalWireCoeff dag m = ternaryTarget g idx

/-- Count of sign-folded `(≤ k, g)` ternary targets. -/
def countBoundedTernary (g k : Nat) : Nat :=
  ((List.finRange (ternaryFoldedSize g)).filter (fun idx =>
    decide (supportSize (ternaryTarget g idx) ≤ k))).length

/-! ## Explicit `g = 4` Binary DAG Witnesses -/

/-- Naive incremental T-MAC `g = 4` binary DAG: `14 ops, depth 3`, pure `{+, -}`.
    Wires: 0..3 = inputs `a0..a3`;
    4..5 = `a0 ± a1` (depth 1);
    6..9 = `(a0 ± a1) ± a2` (depth 2);
    10..17 = `((a0 ± a1) ± a2) ± a3` (depth 3, all 8 targets). -/
def naiveTmacG4Dag : LinearDag 4 :=
  ⟨[
    ⟨0, 1, 1, 1⟩,   -- 4:  (1, 1, 0, 0)
    ⟨0, 1, 1, -1⟩,  -- 5:  (1,-1, 0, 0)
    ⟨4, 2, 1, 1⟩,   -- 6:  (1, 1, 1, 0)
    ⟨4, 2, 1, -1⟩,  -- 7:  (1, 1,-1, 0)
    ⟨5, 2, 1, 1⟩,   -- 8:  (1,-1, 1, 0)
    ⟨5, 2, 1, -1⟩,  -- 9:  (1,-1,-1, 0)
    ⟨6, 3, 1, 1⟩,   -- 10: (1, 1, 1, 1)
    ⟨6, 3, 1, -1⟩,  -- 11: (1, 1, 1,-1)
    ⟨7, 3, 1, 1⟩,   -- 12: (1, 1,-1, 1)
    ⟨7, 3, 1, -1⟩,  -- 13: (1, 1,-1,-1)
    ⟨8, 3, 1, 1⟩,   -- 14: (1,-1, 1, 1)
    ⟨8, 3, 1, -1⟩,  -- 15: (1,-1, 1,-1)
    ⟨9, 3, 1, 1⟩,   -- 16: (1,-1,-1, 1)
    ⟨9, 3, 1, -1⟩   -- 17: (1,-1,-1,-1)
  ]⟩

/-- GPU-discovered optimal pure `{+, -}` `g = 4` binary DAG (Balanced 2+2 Tree):
    `12 ops, depth 2`, strictly beating naive T-MAC `(14, 3)` in BOTH ops and depth.
    Wires: 0..3 = inputs `a0..a3`;
    4..7 = `a0 ± a1`, `a2 ± a3` (depth 1);
    8..15 = `(a0 ± a1) ± (a2 ± a3)` (depth 2, all 8 targets). -/
def balancedTreeG4Dag : LinearDag 4 :=
  ⟨[
    ⟨0, 1, 1, 1⟩,   -- 4:  (1, 1, 0, 0)
    ⟨0, 1, 1, -1⟩,  -- 5:  (1,-1, 0, 0)
    ⟨2, 3, 1, 1⟩,   -- 6:  (0, 0, 1, 1)
    ⟨2, 3, 1, -1⟩,  -- 7:  (0, 0, 1,-1)
    ⟨4, 6, 1, 1⟩,   -- 8:  (1, 1, 1, 1)
    ⟨4, 6, 1, -1⟩,  -- 9:  (1, 1,-1,-1)
    ⟨4, 7, 1, 1⟩,   -- 10: (1, 1, 1,-1)
    ⟨4, 7, 1, -1⟩,  -- 11: (1, 1,-1, 1)
    ⟨5, 6, 1, 1⟩,   -- 12: (1,-1, 1, 1)
    ⟨5, 6, 1, -1⟩,  -- 13: (1,-1,-1,-1)
    ⟨5, 7, 1, 1⟩,   -- 14: (1,-1, 1,-1)
    ⟨5, 7, 1, -1⟩   -- 15: (1,-1,-1, 1)
  ]⟩

/-- GPU-discovered RDNA 3 `V_ADD_LSHL` Pareto point for `g = 4`: `11 ops, depth 3`. -/
def rdna3MidG4Dag : LinearDag 4 :=
  ⟨[
    ⟨0, 1, 1, 1⟩,   -- 4:  (1, 1, 0, 0) [d=1]
    ⟨0, 1, 1, -1⟩,  -- 5:  (1,-1, 0, 0) [d=1]
    ⟨2, 3, 1, 1⟩,   -- 6:  (0, 0, 1, 1) [d=1]
    ⟨4, 6, 1, 1⟩,   -- 7:  (1, 1, 1, 1) [d=2]
    ⟨4, 6, 1, -1⟩,  -- 8:  (1, 1,-1,-1) [d=2]
    ⟨5, 6, 1, 1⟩,   -- 9:  (1,-1, 1, 1) [d=2]
    ⟨5, 6, 1, -1⟩,  -- 10: (1,-1,-1,-1) [d=2]
    ⟨7, 3, 1, -2⟩,  -- 11: (1, 1, 1,-1) [d=3]
    ⟨7, 2, 1, -2⟩,  -- 12: (1, 1,-1, 1) [d=3]
    ⟨9, 3, 1, -2⟩,  -- 13: (1,-1, 1,-1) [d=3]
    ⟨9, 2, 1, -2⟩   -- 14: (1,-1,-1, 1) [d=3]
  ]⟩

/-- GPU-discovered lower-bound-tight RDNA 3 `V_ADD_LSHL` DAG for `g = 4`:
    `10 ops` (= `binaryLowerBound 4`), `depth 4` (`2.5×` lower latency than Gray code). -/
def rdna3MinOpsG4Dag : LinearDag 4 :=
  ⟨[
    ⟨0, 1, 1, 1⟩,   -- 4:  (1, 1, 0, 0) [d=1]
    ⟨2, 3, 1, 1⟩,   -- 5:  (0, 0, 1, 1) [d=1]
    ⟨4, 5, 1, 1⟩,   -- 6:  (1, 1, 1, 1) [d=2]
    ⟨4, 5, 1, -1⟩,  -- 7:  (1, 1,-1,-1) [d=2]
    ⟨6, 3, 1, -2⟩,  -- 8:  (1, 1, 1,-1) [d=3]
    ⟨6, 2, 1, -2⟩,  -- 9:  (1, 1,-1, 1) [d=3]
    ⟨6, 1, 1, -2⟩,  -- 10: (1,-1, 1, 1) [d=3]
    ⟨7, 1, 1, -2⟩,  -- 11: (1,-1,-1,-1) [d=3]
    ⟨8, 1, 1, -2⟩,  -- 12: (1,-1, 1,-1) [d=4]
    ⟨9, 1, 1, -2⟩   -- 13: (1,-1,-1, 1) [d=4]
  ]⟩

/-! ## Explicit Minimal Ternary DAG Witnesses (`g = 2, 3, 4` and `(≤2, 4)`) -/

/-- Exact minimal ternary DAG for `g = 2`: `2 ops, depth 1`, zero wasted intermediates. -/
def ternaryMinG2Dag : LinearDag 2 :=
  ⟨[
    ⟨0, 1, 1, 1⟩,   -- 2: (1, 1)
    ⟨1, 0, 1, -1⟩   -- 3: (-1, 1)
  ]⟩

/-- Exact minimal ternary DAG for `g = 3`: `10 ops, depth 2`, zero wasted intermediates.
    Inputs 0, 1, 2 = `e0, e1, e2`;
    3..4 = `e1 ± e0` (depth 1);
    5..12 = `e2 ± {e0, e1, e1+e0, e1-e0}` (depth ≤ 2). -/
def ternaryMinG3Dag : LinearDag 3 :=
  ⟨[
    ⟨1, 0, 1, 1⟩,   -- 3:  ( 1, 1, 0) [d=1]
    ⟨1, 0, 1, -1⟩,  -- 4:  (-1, 1, 0) [d=1]
    ⟨2, 0, 1, 1⟩,   -- 5:  ( 1, 0, 1) [d=1]
    ⟨2, 0, 1, -1⟩,  -- 6:  (-1, 0, 1) [d=1]
    ⟨2, 1, 1, 1⟩,   -- 7:  ( 0, 1, 1) [d=1]
    ⟨2, 1, 1, -1⟩,  -- 8:  ( 0,-1, 1) [d=1]
    ⟨2, 3, 1, 1⟩,   -- 9:  ( 1, 1, 1) [d=2]
    ⟨2, 3, 1, -1⟩,  -- 10: (-1,-1, 1) [d=2]
    ⟨2, 4, 1, 1⟩,   -- 11: (-1, 1, 1) [d=2]
    ⟨2, 4, 1, -1⟩   -- 12: ( 1,-1, 1) [d=2]
  ]⟩

/-- Exact minimal balanced ternary DAG for `g = 4`: `36 ops, depth 2`, zero wasted intermediates.
    Left canonical nonzero wires: `0, 1, 4, 5` (`e0, e1, e1+e0, e1-e0`, all depth ≤ 1).
    Right canonical nonzero wires: `2, 3, 6, 7` (`e2, e3, e3+e2, e3-e2`, all depth ≤ 1).
    Depth 2: all `4 × 4 × 2 = 32` combinations `R ± L` (first nonzero from the MSB side is `+1`). -/
def ternaryMinG4Dag : LinearDag 4 :=
  ⟨[
    -- Depth 1 (4 ops): left pair and right pair
    ⟨1, 0, 1, 1⟩,   -- 4:  ( 1, 1, 0, 0)
    ⟨1, 0, 1, -1⟩,  -- 5:  (-1, 1, 0, 0)
    ⟨3, 2, 1, 1⟩,   -- 6:  ( 0, 0, 1, 1)
    ⟨3, 2, 1, -1⟩,  -- 7:  ( 0, 0,-1, 1)
    -- Depth 2 (32 ops): R ± L for R ∈ {2, 3, 6, 7}, L ∈ {0, 1, 4, 5}
    ⟨2, 0, 1, 1⟩, ⟨2, 0, 1, -1⟩,
    ⟨2, 1, 1, 1⟩, ⟨2, 1, 1, -1⟩,
    ⟨2, 4, 1, 1⟩, ⟨2, 4, 1, -1⟩,
    ⟨2, 5, 1, 1⟩, ⟨2, 5, 1, -1⟩,
    ⟨3, 0, 1, 1⟩, ⟨3, 0, 1, -1⟩,
    ⟨3, 1, 1, 1⟩, ⟨3, 1, 1, -1⟩,
    ⟨3, 4, 1, 1⟩, ⟨3, 4, 1, -1⟩,
    ⟨3, 5, 1, 1⟩, ⟨3, 5, 1, -1⟩,
    ⟨6, 0, 1, 1⟩, ⟨6, 0, 1, -1⟩,
    ⟨6, 1, 1, 1⟩, ⟨6, 1, 1, -1⟩,
    ⟨6, 4, 1, 1⟩, ⟨6, 4, 1, -1⟩,
    ⟨6, 5, 1, 1⟩, ⟨6, 5, 1, -1⟩,
    ⟨7, 0, 1, 1⟩, ⟨7, 0, 1, -1⟩,
    ⟨7, 1, 1, 1⟩, ⟨7, 1, 1, -1⟩,
    ⟨7, 4, 1, 1⟩, ⟨7, 4, 1, -1⟩,
    ⟨7, 5, 1, 1⟩, ⟨7, 5, 1, -1⟩
  ]⟩

/-- Exact minimal bounded-support `(≤ 2, 4)` ternary DAG: `12 ops, depth 1`
    (all `C(4,2) * 2 = 12` pairwise sums/differences, covering all `16` sign-folded entries). -/
def ternarySparse2of4Dag : LinearDag 4 :=
  ⟨[
    ⟨1, 0, 1, 1⟩, ⟨1, 0, 1, -1⟩,
    ⟨2, 0, 1, 1⟩, ⟨2, 0, 1, -1⟩,
    ⟨2, 1, 1, 1⟩, ⟨2, 1, 1, -1⟩,
    ⟨3, 0, 1, 1⟩, ⟨3, 0, 1, -1⟩,
    ⟨3, 1, 1, 1⟩, ⟨3, 1, 1, -1⟩,
    ⟨3, 2, 1, 1⟩, ⟨3, 2, 1, -1⟩
  ]⟩

/-! ## Bit-Serial `POPCNT` Dot-Product Definitions -/

def boolToInt (b : Bool) : Int :=
  if b then 1 else 0

/-- Bit weight for bit `j` of a `b`-bit integer: `+2^j`, except `-2^(b-1)` for the
    MSB when `signed = true` (exact two's-complement arithmetic). -/
def bitWeight (b : Nat) (signed : Bool) (j : Fin b) : Int :=
  if signed && j.val + 1 == b then -((2 ^ j.val : Nat) : Int)
  else ((2 ^ j.val : Nat) : Int)

/-- Reconstruct an integer from its `b` bits (unsigned or two's-complement signed). -/
def bitsToInt (b : Nat) (signed : Bool) (bits : Fin b → Bool) : Int :=
  finSumInt (fun j => bitWeight b signed j * boolToInt (bits j))

/-- Extract the `b` two's-complement bits of an integer `x` (exact for `-2^(b-1) ≤ x < 2^(b-1)`). -/
def twosCompBits (b : Nat) (x : Int) : Fin b → Bool :=
  let u : Nat := (x % ((2 ^ b : Nat) : Int)).toNat
  fun j => u.testBit j.val

/-- Population count of a `K`-bit plane. -/
def popcnt {K : Nat} (plane : Fin K → Bool) : Nat :=
  finSumNat (fun i => if plane i then 1 else 0)

/-- Bitwise AND of two `K`-bit planes. -/
def andPlane {K : Nat} (p q : Fin K → Bool) : Fin K → Bool :=
  fun i => p i && q i

/-- Binary weight `{-1, +1}` decoded from a single bit (`false ↦ -1, true ↦ +1`). -/
def binWeight (p : Bool) : Int :=
  2 * boolToInt p - 1

/-- Ternary weight `{-1, 0, +1}` decoded from two bitplanes `(pPos, pNeg)`. -/
def ternWeight (pPos pNeg : Bool) : Int :=
  boolToInt pPos - boolToInt pNeg

/-- Zero-LUT bit-serial `POPCNT` dot product for binary `{-1, +1}` weights against
    `b`-bit activations stored in bit-sliced form `aPlanes : Fin b → Fin K → Bool`. -/
def popcntBinaryDot {K b : Nat} (signed : Bool) (wPlane : Fin K → Bool)
    (aPlanes : Fin b → Fin K → Bool) : Int :=
  finSumInt (fun j =>
    bitWeight b signed j *
      (2 * (popcnt (andPlane wPlane (aPlanes j)) : Int) - (popcnt (aPlanes j) : Int)))

/-- Zero-LUT bit-serial `POPCNT` dot product for ternary `{-1, 0, +1}` weights `(wPos, wNeg)`
    against `b`-bit activations stored in bit-sliced form `aPlanes : Fin b → Fin K → Bool`. -/
def popcntTernaryDot {K b : Nat} (signed : Bool) (wPos wNeg : Fin K → Bool)
    (aPlanes : Fin b → Fin K → Bool) : Int :=
  finSumInt (fun j =>
    bitWeight b signed j *
      ((popcnt (andPlane wPos (aPlanes j)) : Int) - (popcnt (andPlane wNeg (aPlanes j)) : Int)))

/-! ## LUT vs `POPCNT` Amortization Cost Model -/

/-- Exact per-`(M, N, K)` GEMM cost of a group-of-`g` LUT kernel:
    LUT precomputation (`M * (K / g) * cBuild`) plus lookups (`M * N * P * (K / g) * cLut`). -/
def lutGemmCost (M N K P g cBuild cLut : Rat) : Rat :=
  M * (K / g) * cBuild + M * N * P * (K / g) * cLut

/-- Exact per-`(M, N, K)` GEMM cost of a zero-LUT bit-serial `POPCNT` kernel:
    activation bit-slice transpose (`M * K * cTr`) plus `W`-wide `POPCNT` inner loop
    (`M * N * P * (K / W) * (b * cPop)`). -/
def popcntGemmCost (M N K P W b cTr cPop : Rat) : Rat :=
  M * K * cTr + M * N * P * (K / W) * (b * cPop)

/-- Per-MAC amortized cost as a function of reuse factor `R` (`M` or `N`):
    `setup / R + steady`. -/
def amortizedCost (setup steady R : Rat) : Rat :=
  setup / R + steady

/-! ## Signed `int16` Overflow & Two's-Complement Wrap-Around -/

def int16Min : Int := -32768
def int16Max : Int := 32767

def fitsInt16 (x : Int) : Prop :=
  int16Min ≤ x ∧ x ≤ int16Max

/-- Exact two's-complement 16-bit signed wrap-around (`int16` modular arithmetic). -/
def wrapInt16 (x : Int) : Int :=
  (x + 32768) % 65536 - 32768

end BitSerialLutDag
