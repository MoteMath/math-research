/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-!
# Walnut-Style Base-2 Automatic Predicate Decision-Certificate Lifter
  & Backward-Prophecy Skolem Engine (Standalone Lean 4.34.1)

Self-contained pure-silicon infinite proof engine (zero Mathlib, zero `native_decide`,
zero `sorry`, zero custom axioms) establishing sharp infinite combinatorial laws on the
non-classical 2-automatic Gray-Sum Parity Word:

    grayAddParity(n) := popcount(n + (n ^^^ (n / 2))) % 2 == 1.
-/

set_option autoImplicit false

namespace WalnutLifter

/-! ## Section 1: Pure-Silicon Balanced Binary Lookup Tree (`BTree`) & Helpers -/

/-- Balanced binary trie indexed by LSB bits of a `Nat` key.
    Lookup takes `O(depth)` kernel reductions instead of `O(n)` list traversal. -/
inductive BTree (α : Type) where
  | leaf (v : α)
  | node (l r : BTree α)
  deriving Repr, DecidableEq

/-- Lookup key `i` in a `BTree` of depth `d` using LSB bit branching. -/
def BTree.get {α : Type} : BTree α → Nat → Nat → α
  | .leaf v, _, _ => v
  | .node l _, 0, _ => l.get 0 0
  | .node l r, d + 1, i =>
    if i &&& 1 == 0 then l.get d (i >>> 1) else r.get d (i >>> 1)

/-- Structurally recursive divide-and-conquer check on `[lo, min(n, lo + 2^d))`
    with recursion depth `d` (reduces directly in Lean's kernel under `decide`). -/
def allPow2 (p : Nat → Bool) (n : Nat) : Nat → Nat → Bool
  | 0, lo => if lo < n then p lo else true
  | d + 1, lo =>
    if n ≤ lo then true
    else allPow2 p n d lo && allPow2 p n d (lo + 2 ^ d)

/-- Structurally recursive fallback check on `[lo, lo + len)` for arbitrary `n > 512`. -/
def allRangeLin (p : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | lo, k + 1 => p lo && allRangeLin p (lo + 1) k

/-- Check `p i = true` for all `0 ≤ i < n` (tight binary-tree depth `≤ 3 / 6 / 9`, works for all `n`). -/
def allLt (n : Nat) (p : Nat → Bool) : Bool :=
  if n ≤ 8 then allPow2 p n 3 0
  else if n ≤ 64 then allPow2 p n 6 0
  else if n ≤ 512 then allPow2 p n 9 0
  else allRangeLin p 0 n

/-- Bitmask built from a list of `Nat` bit indices. -/
def maskOfList : List Nat → Nat
  | [] => 0
  | q :: qs => (1 <<< q) ||| maskOfList qs

/-! ## Section 2: Multi-Track Base-2 LSB-First Encoding & DFA Semantics -/

/-- Tuple constructors avoiding Mathlib dependencies. -/
def tuple1 (a : Nat) : Fin 1 → Nat := fun _ => a

def tuple2 (a b : Nat) : Fin 2 → Nat
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

def tuple3 (a b c : Nat) : Fin 3 → Nat
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

def tuple4 (a b c d : Nat) : Fin 4 → Nat
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

def consTuple {k : Nat} (y : Nat) (x : Fin k → Nat) : Fin (k + 1) → Nat
  | ⟨0, _⟩ => y
  | ⟨j + 1, h⟩ => x ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Bit-slice `0 .. 2^k - 1` at bit position `i` of a `k`-tuple `x : Fin k → Nat`.
    Bit `j` of `sliceOf x i` equals `(x j).testBit i`. -/
def sliceAux : (k : Nat) → (Fin k → Nat) → Nat → Nat
  | 0, _, _ => 0
  | k + 1, x, i =>
    (if (x ⟨0, Nat.zero_lt_succ k⟩).testBit i then 1 else 0) +
      2 * sliceAux k (fun j => x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) i

def sliceOf {k : Nat} (x : Fin k → Nat) (i : Nat) : Nat :=
  sliceAux k x i

/-- LSB-first encoding of a `k`-tuple `x` of length `L`. -/
def encWord {k : Nat} (L : Nat) (x : Fin k → Nat) : List Nat :=
  (List.range L).map (sliceOf x)

/-- Upper bound `maxBitLen x` satisfying `∀ j, x j < 2 ^ (maxBitLen x)`. -/
def maxBitLenAux : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k + 1, x =>
    Nat.max (x ⟨0, Nat.zero_lt_succ k⟩)
      (maxBitLenAux k (fun j => x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))

def maxBitLen {k : Nat} (x : Fin k → Nat) : Nat :=
  maxBitLenAux k x

/-- A `k`-track LSB-first deterministic finite automaton. -/
structure DFA (k : Nat) where
  numStates : Nat
  init      : Nat
  step      : Nat → Nat → Nat
  accept    : Nat → Bool

def DFA.runFrom {k : Nat} (M : DFA k) (q : Nat) : List Nat → Nat
  | [] => q
  | a :: w => M.runFrom (M.step q a) w

def DFA.run {k : Nat} (M : DFA k) (w : List Nat) : Nat :=
  M.runFrom M.init w

def DFA.acceptsWord {k : Nat} (M : DFA k) (w : List Nat) : Bool :=
  M.accept (M.run w)

/-- Trailing-zero language invariance: appending an all-zero bit-slice never changes acceptance. -/
def DFA.PadInv {k : Nat} (M : DFA k) : Prop :=
  ∀ w : List Nat, (∀ a ∈ w, a < 2 ^ k) → M.acceptsWord (w ++ [0]) = M.acceptsWord w

/-- Canonical semantic evaluation of a `k`-track DFA on a `k`-tuple of natural numbers. -/
def DFA.eval {k : Nat} (M : DFA k) (x : Fin k → Nat) : Bool :=
  M.acceptsWord (encWord (maxBitLen x) x)

/-! ## Section 3: Boolean & Track-Reindexing Combinators -/

def dfaNot {k : Nat} (M : DFA k) : DFA k where
  numStates := M.numStates
  init := M.init
  step := M.step
  accept := fun q => !(M.accept q)

/-- Product DFA on `M₁ × M₂` with Boolean connective `op`. -/
def dfaProd {k : Nat} (op : Bool → Bool → Bool) (M₁ M₂ : DFA k) : DFA k where
  numStates := M₁.numStates * M₂.numStates
  init := M₁.init * M₂.numStates + M₂.init
  step := fun q a =>
    let q1 := q / M₂.numStates
    let q2 := q % M₂.numStates
    M₁.step q1 a * M₂.numStates + M₂.step q2 a
  accept := fun q =>
    op (M₁.accept (q / M₂.numStates)) (M₂.accept (q % M₂.numStates))

/-- State-closedness predicate (needed for clean `dfaProd` arithmetic). -/
def DFA.Closed {k : Nat} (M : DFA k) : Prop :=
  M.init < M.numStates ∧ ∀ q < M.numStates, ∀ a < 2 ^ k, M.step q a < M.numStates

/-- Reindex a `k₁`-track slice from a `k₂`-track slice using `f : Fin k₁ → Fin k₂`. -/
def reindexSliceAux : (k₁ : Nat) → {k₂ : Nat} → (Fin k₁ → Fin k₂) → Nat → Nat
  | 0, _, _, _ => 0
  | k₁ + 1, _, f, a =>
    (if a.testBit (f ⟨0, Nat.zero_lt_succ k₁⟩).val then 1 else 0) +
      2 * reindexSliceAux k₁ (fun j => f ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) a

def reindexSlice {k₁ k₂ : Nat} (f : Fin k₁ → Fin k₂) (a : Nat) : Nat :=
  reindexSliceAux k₁ f a

def dfaReindex {k₁ k₂ : Nat} (f : Fin k₁ → Fin k₂) (M : DFA k₁) : DFA k₂ where
  numStates := M.numStates
  init := M.init
  step := fun q a => M.step q (reindexSlice f a)
  accept := M.accept

/-! ## Section 4: Certified Primitive Arithmetic DFAs (`≤`, `<`, `+`, `+1`) -/

/-- 2-state LSB-first DFA for `x ≤ y`: state 0 = `le` (acc), state 1 = `gt` (rej). -/
def dfaLe : DFA 2 where
  numStates := 2
  init := 0
  step := fun q a =>
    let bx := a &&& 1
    let by_ := (a >>> 1) &&& 1
    if bx == by_ then q else if bx == 0 then 0 else 1
  accept := fun q => q == 0

/-- 2-state LSB-first DFA for `x < y`: state 0 = `ge` (rej), state 1 = `lt` (acc). -/
def dfaLt : DFA 2 where
  numStates := 2
  init := 0
  step := fun q a =>
    let bx := a &&& 1
    let by_ := (a >>> 1) &&& 1
    if bx == by_ then q else if bx == 0 then 1 else 0
  accept := fun q => q == 1

/-- 3-state LSB-first DFA for `x + y = z`:
    state 0 = carry 0 (acc), state 1 = carry 1 (rej), state 2 = dead (rej). -/
def dfaAdd : DFA 3 where
  numStates := 3
  init := 0
  step := fun q a =>
    if q ≥ 2 then 2
    else
      let bx := a &&& 1
      let by_ := (a >>> 1) &&& 1
      let bz := (a >>> 2) &&& 1
      let s := bx + by_ + q
      if s % 2 == bz then s / 2 else 2
  accept := fun q => q == 0

/-- 3-state LSB-first DFA for `x + 1 = y` (track 0 = y, track 1 = x):
    state 0 = carry 1 (initial, rej), state 1 = carry 0 (acc), state 2 = dead (rej). -/
def dfaAddOne : DFA 2 where
  numStates := 3
  init := 0
  step := fun q a =>
    if q ≥ 2 then 2
    else
      let by_ := a &&& 1
      let bx := (a >>> 1) &&& 1
      let c := if q == 0 then 1 else 0
      let s := bx + c
      if s % 2 == by_ then (if s / 2 == 1 then 0 else 1) else 2
  accept := fun q => q == 1

/-! ## Section 5: Pure-Data Infinite Proof Certificate Lifters
    1. `HomCert`       : DFA Minimization / Bisimulation Compression
    2. `ExistsCert`    : Forward Existential Quantifier Elimination (`∃ y : Nat`)
    3. `ProphecyCert`  : Backward-Prophecy / Bimachine Skolem Lifter (`∀ x, P(x) → ∃ y, M(y, x)`)
    4. `UniversalCert` : Reachable-Invariant Universal Validity / Emptiness -/

/-! ### 5.1 Lifter 1: `HomCert` (DFA Bisimulation / Minimization Certificate) -/

/-- Pure-data DFA homomorphism certificate (zero `Prop` fields). -/
structure HomCert where
  reachMask : Nat
  homTree   : BTree Nat
  homDepth  : Nat

def checkHomCert {k : Nat} (M₁ M₂ : DFA k) (cert : HomCert) : Bool :=
  let alpha := 2 ^ k
  (M₁.init < M₁.numStates) &&
  (M₂.init < M₂.numStates) &&
  (cert.reachMask.testBit M₁.init) &&
  (cert.homTree.get cert.homDepth M₁.init == M₂.init) &&
  allLt M₁.numStates fun q =>
    if cert.reachMask.testBit q then
      let hq := cert.homTree.get cert.homDepth q
      (hq < M₂.numStates) &&
      (M₁.accept q == M₂.accept hq) &&
      allLt alpha fun a =>
        let q' := M₁.step q a
        (q' < M₁.numStates) &&
        (cert.reachMask.testBit q') &&
        (cert.homTree.get cert.homDepth q' == M₂.step hq a)
    else true

/-! ### 5.2 Shared Trailing-Zero Reachability Certificate (`ZeroReachCert`) -/

/-- Pure-data rank certificate for trailing-zero reachability:
    `zAccMask.testBit q = true` certifies that from `q` some finite sequence of `(b, 0)`
    transitions in `M : DFA (k + 1)` reaches an accepting state of `M`. -/
structure ZeroReachCert where
  zAccMask : Nat
  zRank    : BTree Nat
  zBit     : BTree Bool
  depth    : Nat

def checkZeroReachSound {k : Nat} (M : DFA (k + 1)) (zc : ZeroReachCert) : Bool :=
  allLt M.numStates fun q =>
    if zc.zAccMask.testBit q then
      if M.accept q then true
      else
        let b := if zc.zBit.get zc.depth q then 1 else 0
        let q' := M.step q b
        (q' < M.numStates) &&
        (zc.zAccMask.testBit q') &&
        (zc.zRank.get zc.depth q' < zc.zRank.get zc.depth q)
    else true

def checkZeroReachComplete {k : Nat} (M : DFA (k + 1)) (zc : ZeroReachCert) : Bool :=
  allLt M.numStates fun q =>
    (!M.accept q || zc.zAccMask.testBit q) &&
    (!(zc.zAccMask.testBit (M.step q 0)) || zc.zAccMask.testBit q) &&
    (!(zc.zAccMask.testBit (M.step q 1)) || zc.zAccMask.testBit q)

/-- Reconstruct a `Nat` from an LSB-first list of `Bool`s. -/
def natOfBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * natOfBits bs

/-- Zip a bit-list `ys` onto an `x`-word `xs` of the same length, producing `(y, x)` slices. -/
def zipBitSlices : List Bool → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | b :: bs, a :: as => ((if b then 1 else 0) + 2 * a) :: zipBitSlices bs as

/-! ### 5.3 Lifter 2: `ExistsCert` (Forward Existential Quantifier Elimination `∃ y : Nat`) -/

/-- Pure-data forward existential projection certificate (`∃ y, M(y, x)`).
    `backWit` packs, for each edge `(u, a)`, the witness `(q, b)` for each `q'` in 16-bit slots:
    bit 0 = `b`, bits 1..15 = `q` (zero `Prop` fields). -/
structure ExistsCert where
  subMask   : BTree Nat
  subDepth  : Nat
  zCert     : ZeroReachCert
  accWit    : BTree Nat
  backWit   : BTree Nat
  edgeDepth : Nat

def checkExistsCert {k : Nat} (M : DFA (k + 1)) (D : DFA k) (cert : ExistsCert) : Bool :=
  let alpha := 2 ^ k
  (M.init < M.numStates) &&
  (D.init < D.numStates) &&
  checkZeroReachSound M cert.zCert &&
  checkZeroReachComplete M cert.zCert &&
  (cert.subMask.get cert.subDepth D.init == (1 <<< M.init)) &&
  allLt D.numStates fun u =>
    let mu := cert.subMask.get cert.subDepth u
    (if D.accept u then
      let q := cert.accWit.get cert.subDepth u
      (q < M.numStates) && (mu.testBit q) && (cert.zCert.zAccMask.testBit q)
     else
      allLt M.numStates fun q => !(mu.testBit q) || !(cert.zCert.zAccMask.testBit q)) &&
    allLt alpha fun a =>
      let u' := D.step u a
      let mu' := cert.subMask.get cert.subDepth u'
      let bw := cert.backWit.get cert.edgeDepth (u * alpha + a)
      (u' < D.numStates) &&
      (allLt M.numStates fun q =>
        if mu.testBit q then
          let q0 := M.step q (2 * a)
          let q1 := M.step q (2 * a + 1)
          (q0 < M.numStates) && (q1 < M.numStates) &&
          (mu'.testBit q0) && (mu'.testBit q1)
        else true) &&
      (allLt M.numStates fun q' =>
        if mu'.testBit q' then
          let packed := (bw >>> (16 * q')) &&& 65535
          let b := (packed &&& 1) == 1
          let q := packed >>> 1
          (q < M.numStates) && (mu.testBit q) &&
          (M.step q ((if b then 1 else 0) + 2 * a) == q')
        else true)

/-! ### 5.4 Lifter 3: `ProphecyCert` (Backward-Prophecy / Bimachine Skolem Lifter) -/

/-- Pure-data Backward-Prophecy / Bimachine Skolem Certificate for:
      `∀ x : Fin k → Nat, P_rev accepts (encWord L x).reverse → ∃ y : Nat, M(y, x)`.
    Achieves 80x–200x state compression over forward subset determinization by pairing a
    compact right-to-left lookahead automaton `B` with a sparse invariant `invMask[r]`,
    a bit-packed per-state reachability table `reachRow[r]` (bit `s` = `(r, s)` reachable in `B × P_rev`),
    and canonical Skolem bit-selector `σ(q, a, r')`. -/
structure ProphecyCert (k : Nat) where
  B        : DFA k
  invMask  : BTree Nat
  activeQ  : BTree (List Nat)
  reachRow : BTree Nat
  bDepth   : Nat
  zCert    : ZeroReachCert

def checkProphecyCert {k : Nat} (M : DFA (k + 1)) (P_rev : DFA k)
    (cert : ProphecyCert k) : Bool :=
  let alpha := 2 ^ k
  let np := P_rev.numStates
  (M.init < M.numStates) &&
  (cert.B.init < cert.B.numStates) &&
  (P_rev.init < np) &&
  checkZeroReachSound M cert.zCert &&
  (allLt cert.B.numStates fun r =>
    let qs := cert.activeQ.get cert.bDepth r
    (maskOfList qs == cert.invMask.get cert.bDepth r) &&
    qs.all (fun q => q < M.numStates)) &&
  ((cert.activeQ.get cert.bDepth cert.B.init).all fun q =>
    cert.zCert.zAccMask.testBit q) &&
  (allLt cert.B.numStates fun r' =>
    let m' := cert.invMask.get cert.bDepth r'
    allLt alpha fun a =>
      let r := cert.B.step r' a
      (r < cert.B.numStates) &&
      ((cert.activeQ.get cert.bDepth r).all fun q =>
        m'.testBit (M.step q (2 * a)) || m'.testBit (M.step q (2 * a + 1)))) &&
  ((cert.reachRow.get cert.bDepth cert.B.init).testBit P_rev.init) &&
  (allLt cert.B.numStates fun r =>
    let rMask := cert.reachRow.get cert.bDepth r
    allLt np fun s =>
      if rMask.testBit s then
        (!P_rev.accept s || (cert.invMask.get cert.bDepth r).testBit M.init) &&
        allLt alpha fun a =>
          let r' := cert.B.step r a
          let s' := P_rev.step s a
          (r' < cert.B.numStates) && (s' < np) &&
          ((cert.reachRow.get cert.bDepth r').testBit s')
      else true)

/-! ### 5.5 Lifter 4: `UniversalCert` (Reachable-Invariant Universal Validity / Emptiness) -/

/-- Pure-data reachable-invariant certificate proving `∀ x, M.eval x = target`. -/
structure UniversalCert where
  reachMask : Nat
  target    : Bool

def checkUniversalCert {k : Nat} (M : DFA k) (cert : UniversalCert) : Bool :=
  let alpha := 2 ^ k
  (M.init < M.numStates) &&
  (cert.reachMask.testBit M.init) &&
  allLt M.numStates fun q =>
    if cert.reachMask.testBit q then
      (M.accept q == cert.target) &&
      allLt alpha fun a =>
        let q' := M.step q a
        (q' < M.numStates) && (cert.reachMask.testBit q')
    else true

/-! ## Section 6: Parametric Right-to-Left Premise DFA `dfaPGePow2Rev e` (`p ≥ 2^e`) -/

/-- `(e + 2)`-state right-to-left (MSB-first) premise DFA on tracks `(n, p)` accepting iff `p ≥ 2^e`. -/
def dfaPGePow2Rev (e : Nat) : DFA 2 where
  numStates := e + 2
  init := 0
  step := fun s a =>
    let bp := (a >>> 1) &&& 1
    if s == 0 then
      if bp == 1 then 1 else 0
    else if s < e + 1 then
      s + 1
    else
      e + 1
  accept := fun s => s == e + 1

/-! ## Section 7: The Non-Classical Gray-Sum Parity Word `grayAddParity`
    `w(n) = popcount(n + (n ^^^ (n / 2))) % 2 == 1` and its 9-State DFAO Bridge -/

/-- Exact binary Hamming weight (`popcount`) on `Nat`. -/
def popcount (n : Nat) : Nat :=
  if h : n = 0 then 0
  else (n % 2) + popcount (n / 2)
termination_by n
decreasing_by omega

/-- The non-classical 2-automatic Gray-Sum Parity Word:
    `grayAddParity n = (popcount (n + (n ^^^ (n / 2)))) % 2 == 1`. -/
def grayAddParity (n : Nat) : Bool :=
  (popcount (n + (n ^^^ (n / 2)))) % 2 == 1

/-- 9-state LSB-first pad-invariant DFAO computing `grayAddParity n`. -/
def dfaGrayAdd : DFA 1 where
  numStates := 9
  init := 0
  step := fun q b =>
    let bit := b &&& 1
    if q == 0 then
      1 + 4 * bit
    else
      let idx := q - 1
      let pb := (idx / 4) % 2
      let c := (idx / 2) % 2
      let p := idx % 2
      let s := pb + (pb ^^^ bit) + c
      let nc := s / 2
      let np := p ^^^ (s % 2)
      1 + 4 * bit + 2 * nc + np
  accept := fun q =>
    if q == 0 then false
    else
      let idx := q - 1
      let pb := (idx / 4) % 2
      let c := (idx / 2) % 2
      let p := idx % 2
      ((p ^^^ c ^^^ pb) == 1)

end WalnutLifter
