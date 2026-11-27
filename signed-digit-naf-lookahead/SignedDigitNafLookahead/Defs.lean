/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`signed-digit-naf-lookahead`)

All definitions needed to state the headline theorems (zero `sorry`, pure `Init`).
-/

set_option linter.unusedVariables false

namespace SDTransducerEngine

-- ============================================================================
-- Section 0: Core Pure-Silicon Signed-Digit Primitives
-- ============================================================================

/-- Balanced binary signed digits `{-1, 0, 1}`. -/
inductive SD where
  | neg : SD
  | zero : SD
  | pos : SD
  deriving DecidableEq, Repr

def SD.toInt : SD → Int
  | .neg  => -1
  | .zero => 0
  | .pos  => 1

def SD.wt : SD → Nat
  | .neg  => 1
  | .zero => 0
  | .pos  => 1

def SD.ofInt (x : Int) : SD :=
  if x == -1 then .neg else if x == 1 then .pos else .zero

def SD.toFin3 : SD → Fin 3
  | .neg  => ⟨0, by decide⟩
  | .zero => ⟨1, by decide⟩
  | .pos  => ⟨2, by decide⟩

def SD.ofFin3 (a : Fin 3) : SD :=
  match a.val with
  | 0 => .neg
  | 1 => .zero
  | _ => .pos

/-- Sum digits `{-2, -1, 0, 1, 2}` arising from digit-wise addition of two `SD` digits. -/
def sumDigitVal (a : Fin 5) : Int := (a.val : Int) - 2

def intToFin5 (x : Int) : Fin 5 :=
  if x == -2 then ⟨0, by decide⟩
  else if x == -1 then ⟨1, by decide⟩
  else if x == 0 then ⟨2, by decide⟩
  else if x == 1 then ⟨3, by decide⟩
  else ⟨4, by decide⟩

/-- Integer value of an LSB-first digit list `∑ d_i * 2^i`. -/
def sdVal : List Int → Int
  | [] => 0
  | d :: ds => d + 2 * sdVal ds

/-- Hamming weight `∑ |d_i|` of a digit list. -/
def sdWt : List Int → Nat
  | [] => 0
  | d :: ds => d.natAbs + sdWt ds

/-- Non-Adjacent Form predicate: no two adjacent digits are both nonzero. -/
def isNAFB : List Int → Bool
  | [] => true
  | [_] => true
  | d₁ :: d₂ :: ds => (decide (d₁ = 0 ∨ d₂ = 0)) && isNAFB (d₂ :: ds)

def IsNAF (ds : List Int) : Prop := isNAFB ds = true

-- ============================================================================
-- Section 1: Reusable Infinite Proof Mechanism (`SDTransducer` Certificate Engine)
-- ============================================================================

/--
Pure-data finite-state signed-digit carry-absorption transducer with finite certificates:
- `m` states (`Fin m`), `k` input symbols (`Fin k`)
- `scale` = `1` for 0-delay transducers, `2` for 1-delay transducers
- `phi : Fin m → Int` is the finite carry-debt potential
- `psi : Fin m → Nat` is the finite weight potential
Zero `Prop` fields: every certificate property is checked by an executable `Bool` checker.
-/
structure SDTransducer (m k : Nat) where
  init  : Fin m
  scale : Int
  valIn : Fin k → Int
  wtIn  : Fin k → Nat
  step  : Fin m → Fin k → Int × Fin m
  flush : Fin m → List Int
  phi   : Fin m → Int
  psi   : Fin m → Nat

namespace SDTransducer

def runAux {m k : Nat} (T : SDTransducer m k) (q : Fin m) : List (Fin k) → List Int × Fin m
  | [] => ([], q)
  | a :: as =>
    let (o, q') := T.step q a
    let (os, qEnd) := runAux T q' as
    (o :: os, qEnd)

def runFrom {m k : Nat} (T : SDTransducer m k) (q : Fin m) (xs : List (Fin k)) : List Int :=
  let (os, qEnd) := runAux T q xs
  os ++ T.flush qEnd

def run {m k : Nat} (T : SDTransducer m k) (xs : List (Fin k)) : List Int :=
  runFrom T T.init xs

/-- Local non-negative edge defect `Δ(q, a) = wtIn(a) + ψ(q) - |out(q,a)| - ψ(δ(q,a))`. -/
def edgeDefect {m k : Nat} (T : SDTransducer m k) (q : Fin m) (a : Fin k) : Nat :=
  let (o, q') := T.step q a
  (T.wtIn a + T.psi q) - (o.natAbs + T.psi q')

def totalDefectFrom {m k : Nat} (T : SDTransducer m k) (q : Fin m) : List (Fin k) → Nat
  | [] => 0
  | a :: as => edgeDefect T q a + totalDefectFrom T (T.step q a).2 as

def totalDefect {m k : Nat} (T : SDTransducer m k) (xs : List (Fin k)) : Nat :=
  totalDefectFrom T T.init xs

variable {m k : Nat} (T : SDTransducer m k)

-- ---- Helper for 1-Delay Transducers (Dropping the Leading Dummy Zero) ----

def dropHeadZero : List Int → List Int
  | [] => []
  | _ :: ds => ds

end SDTransducer


-- ============================================================================
-- Section 2: Theorem 1 — 5-State Canonical SD -> NAF Carry-Absorption Transducer
-- ============================================================================

def nafStateVal (q : Fin 5) : Int := (q.val : Int) - 2

def nafStateOfInt (s : Int) : Fin 5 := intToFin5 s

def nafStepRaw (s d : Int) : Int × Int :=
  let v := s + 2 * d
  if v % 2 == 0 then (0, v / 2)
  else if v % 4 == 1 then (1, (v - 1) / 2)
  else (-1, (v + 1) / 2)

def nafFlushRaw (q : Fin 5) : List Int :=
  match q.val with
  | 0 => [0, -1]
  | 1 => [-1]
  | 2 => []
  | 3 => [1]
  | _ => [0, 1]

def nafPsi (q : Fin 5) : Nat :=
  if q.val == 2 then 0 else 1

/-- 5-state canonical SD -> NAF carry-absorption transducer instance of `SDTransducer`. -/
def nafTransducer : SDTransducer 5 3 where
  init  := ⟨2, by decide⟩
  scale := 2
  valIn := fun a => (SD.ofFin3 a).toInt
  wtIn  := fun a => (SD.ofFin3 a).wt
  step  := fun q a =>
    let (o, ns) := nafStepRaw (nafStateVal q) (SD.ofFin3 a).toInt
    (o, nafStateOfInt ns)
  flush := nafFlushRaw
  phi   := nafStateVal
  psi   := nafPsi

/-- Canonical NAF recoding of an arbitrary balanced signed-digit stream `D : List SD`. -/
def nafRecode (D : List SD) : List Int :=
  SDTransducer.dropHeadZero (nafTransducer.run (D.map SD.toFin3))

def nafTotalDefect (D : List SD) : Nat :=
  nafTransducer.totalDefect (D.map SD.toFin3)

-- ---- Unsigned Binary Specialization (`∀ n : Nat`) ----

/-- Structurally recursive binary expansion (kernel-reducible for `decide`!). -/
def natToSDAux : Nat → Nat → List SD
  | 0, _ => []
  | _, 0 => []
  | fuel + 1, n =>
    (if n % 2 == 1 then SD.pos else SD.zero) :: natToSDAux fuel (n / 2)

def natToSD (n : Nat) : List SD := natToSDAux n n

def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | fuel + 1, n => (n % 2) + popcountAux fuel (n / 2)

def popcount (n : Nat) : Nat := popcountAux n n

-- ============================================================================
-- Section 3: Theorem 2 — Exact Cubic Counting Recurrences (∀ w : Nat)
-- ============================================================================

def allBinWords : Nat → List (List SD)
  | 0 => [[]]
  | w + 1 =>
    let prev := allBinWords w
    prev.map (SD.zero :: ·) ++ prev.map (SD.pos :: ·)

def allSDWords : Nat → List (List SD)
  | 0 => [[]]
  | w + 1 =>
    let prev := allSDWords w
    prev.map (SD.neg :: ·) ++ prev.map (SD.zero :: ·) ++ prev.map (SD.pos :: ·)

def countZeroFrom (q : Fin 5) (L : List (List SD)) : Nat :=
  (L.filter (fun D => nafTransducer.totalDefectFrom q (D.map SD.toFin3) == 0)).length

/-- Exact count of `w`-bit unsigned binary strings where `popcount = wt_NAF`. -/
def countZeroDefectBin (w : Nat) : Nat :=
  countZeroFrom nafTransducer.init (allBinWords w)

/-- Exact count of length-`w` signed-digit strings achieving minimal NAF weight. -/
def countZeroDefectSD (w : Nat) : Nat :=
  countZeroFrom nafTransducer.init (allSDWords w)

/--
**Odd-Lookahead Carry-Free Parallel Adder (OL-CFPA)** carry function `c_i(s_{i-1}, s_i, s_{i+1})`:
  - `s_i = ±2  => c_i = ±1`
  - `s_i = 0   => c_i = 0`
  - `s_i = +1  => c_i = 1` iff `s_{i-1} ≥ 1` OR (`s_{i-1} = 0` AND `|s_{i+1}| = 1`)
  - `s_i = -1  => c_i = -1` iff `s_{i-1} ≤ -1` OR (`s_{i-1} = 0` AND `|s_{i+1}| = 1`)
-/
def olCarry (sp s sn : Int) : Int :=
  if s == 2 then 1
  else if s == -2 then -1
  else if s == 0 then 0
  else if s == 1 then
    if sp ≥ 1 ∨ (sp == 0 ∧ (sn == 1 ∨ sn == -1)) then 1 else 0
  else if s == -1 then
    if sp ≤ -1 ∨ (sp == 0 ∧ (sn == 1 ∨ sn == -1)) then -1 else 0
  else 0

/-- Strictly local `O(1)`-depth parallel evaluation on a sum-digit stream `xs : List (Fin 5)`. -/
def getSum (xs : List (Fin 5)) (i : Int) : Int :=
  if i < 0 then 0
  else match xs[i.toNat]? with
       | some a => sumDigitVal a
       | none   => 0

def olLocalCarryAt (xs : List (Fin 5)) (i : Int) : Int :=
  olCarry (getSum xs (i - 1)) (getSum xs i) (getSum xs (i + 1))

def olLocalDigitAt (xs : List (Fin 5)) (i : Int) : Int :=
  (getSum xs i - 2 * olLocalCarryAt xs i) + olLocalCarryAt xs (i - 1)

/-- Strictly local parallel output stream of length `xs.length + 1` (each digit computed in `O(1)` depth!). -/
def olParallelEval (xs : List (Fin 5)) : List Int :=
  (List.range (xs.length + 1)).map (fun i : Nat => olLocalDigitAt xs (i : Int))

/-- Structurally recursive digit-wise sum of two balanced signed-digit lists (kernel-reducible!). -/
def zipAddSD : List SD → List SD → List (Fin 5)
  | [], B => B.map (fun b => intToFin5 (0 + b.toInt))
  | a :: as, [] => intToFin5 (a.toInt + 0) :: as.map (fun x => intToFin5 (x.toInt + 0))
  | a :: as, b :: bs => intToFin5 (a.toInt + b.toInt) :: zipAddSD as bs

/-- Strictly local `O(1)`-depth carry-free parallel addition `A ⊞ B : List SD`. -/
def olAdd (A B : List SD) : List SD :=
  (olParallelEval (zipAddSD A B)).map SD.ofInt

-- ============================================================================
-- Section 5: Theorem 4 — Sharp Universal Zero-Lookahead Impossibility (∀ r : Nat)
--            & Periodic 3/2 Weight-Blowup for Classical Chow-Robertson (r = 1)
-- ============================================================================

def getS (s : List Int) (i : Int) : Int :=
  if i < 0 then 0 else (s[i.toNat]?).getD 0

def ValidSumStream (s : List Int) : Prop :=
  ∀ x ∈ s, -2 ≤ x ∧ x ≤ 2

/-- Causal carry function of finite lookback radius `r`: `c_i = C(s_i, s_{i-1}, ..., s_{i-r})`. -/
def causalCarryAt {r : Nat} (C : (Fin (r + 1) → Int) → Int) (s : List Int) (i : Int) : Int :=
  C (fun j => getS s (i - (j.val : Int)))

def causalDigitAt {r : Nat} (C : (Fin (r + 1) → Int) → Int) (s : List Int) (i : Int) : Int :=
  (getS s i - 2 * causalCarryAt C s i) + causalCarryAt C s (i - 1)

/-- Total output weight of a causal radius-`r` adder on finite input `s` (flushed over `s.length + r + 1` positions). -/
def causalOutWt {r : Nat} (C : (Fin (r + 1) → Int) → Int) (s : List Int) : Nat :=
  ((List.range (s.length + r + 1)).map (fun i : Nat => (causalDigitAt C s (i : Int)).natAbs)).foldr (· + ·) 0

/-- Axiomatization of ANY valid causal (zero-lookahead) carry-free parallel signed-digit adder of radius `r`. -/
structure CausalAdder (r : Nat) where
  C : (Fin (r + 1) → Int) → Int
  zero_stable : C (fun _ => 0) = 0
  carry_free : ∀ (s : List Int), ValidSumStream s → ∀ i : Nat,
    -1 ≤ causalDigitAt C s (i : Int) ∧ causalDigitAt C s (i : Int) ≤ 1

-- ---- Non-Vacuity Witness: Classical Chow-Robertson (r = 1) is a CausalAdder 1 ----

def crCarry (w : Fin 2 → Int) : Int :=
  let s := w ⟨0, by decide⟩
  let sp := w ⟨1, by decide⟩
  if s == 2 then 1
  else if s == -2 then -1
  else if s == 0 then 0
  else if s == 1 then (if sp ≥ 1 then 1 else 0)
  else if s == -1 then (if sp ≤ -1 then -1 else 0)
  else 0

-- ---- Theorem 4b: Explicit Periodic 3/2 Weight-Blowup Family for Chow-Robertson (∀ m : Nat) ----

def repeatBlock110 : Nat → List Int
  | 0 => []
  | m + 1 => 1 :: 1 :: 0 :: repeatBlock110 m

-- ---- 6.3 Exhaustive `#print axioms` Across All Public Theorems ----


end SDTransducerEngine
