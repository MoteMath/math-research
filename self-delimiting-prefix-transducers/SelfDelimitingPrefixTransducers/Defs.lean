/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`self-delimiting-prefix-transducers`)

Self-Delimiting Binary Prefix-Code Kirchhoff-Bellman Transducer Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace PrefixCodeEngine


/-! ==========================================================================
    SECTION 1: Basic Pure-Silicon Primitives (Bit-Strings, Lex Order, Jacobsthal)
    ========================================================================== -/

/-- Exact alternating sign `(-1)^n` in `Int`. -/
def negOnePow : Nat → Int
  | 0 => 1
  | n + 1 => -negOnePow n

/-- Exact integer Jacobsthal sequence: `J 0 = 0`, `J 1 = 1`, `J (n+2) = J (n+1) + 2 * J n`. -/
def jacobsthal : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n

/-- Hamming weight (popcount) of a bit-list. -/
def popcount : List Bool → Nat
  | [] => 0
  | false :: bs => popcount bs
  | true :: bs => 1 + popcount bs

/-- Strict lexicographic order on binary strings (`false < true`, strict prefix `<` extension). -/
inductive lexLt : List Bool → List Bool → Prop where
  | nil_cons (b : Bool) (bs : List Bool) : lexLt [] (b :: bs)
  | false_true (u v : List Bool) : lexLt (false :: u) (true :: v)
  | cons_same (b : Bool) {u v : List Bool} : lexLt u v → lexLt (b :: u) (b :: v)

/-- Divergent lexicographic order: `u` and `v` disagree at a first index with `false < true`. -/
inductive lexDiverge : List Bool → List Bool → Prop where
  | head (u v : List Bool) : lexDiverge (false :: u) (true :: v)
  | cons (b : Bool) {u v : List Bool} : lexDiverge u v → lexDiverge (b :: u) (b :: v)

/-- Exhaustive list of all `2^N` bitstrings of exact length `N`. -/
def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | N + 1 => (allBits N).map (false :: ·) ++ (allBits N).map (true :: ·)

/-- Integer sum of a function over a list. -/
def listSumInt {α : Type} (f : α → Int) : List α → Int
  | [] => 0
  | x :: xs => f x + listSumInt f xs

/-- Outcome of reading one bit in a finite-state prefix-code automaton. -/
inductive Step (S : Nat) where
  | cont (q : Fin S)
  | emit
  | dead
  deriving DecidableEq, Repr

/-- Finite-state self-delimiting binary prefix-code automaton with `S` states. -/
structure PrefixAut (S : Nat) where
  init : Fin S
  step : Fin S → Bool → Step S

/-- Inductive characterization of codewords accepted by `A` starting from state `q`. -/
inductive Accepts {S : Nat} (A : PrefixAut S) : Fin S → List Bool → Prop where
  | emit {q : Fin S} {b : Bool} (h : A.step q b = Step.emit) :
      Accepts A q [b]
  | cont {q q' : Fin S} {b : Bool} {w : List Bool}
      (h : A.step q b = Step.cont q') (hw : Accepts A q' w) :
      Accepts A q (b :: w)

/-- Deterministic single-codeword streaming decoder from state `q`. -/
def decodeOne {S : Nat} (A : PrefixAut S) : Fin S → List Bool → Option (List Bool × List Bool)
  | _, [] => none
  | q, b :: rest =>
    match A.step q b with
    | Step.emit => some ([b], rest)
    | Step.dead => none
    | Step.cont q' =>
      match decodeOne A q' rest with
      | none => none
      | some (w, rem) => some (b :: w, rem)

theorem decodeOne_length_lt {S : Nat} (A : PrefixAut S) {q : Fin S} {bits w rem : List Bool}
    (h : decodeOne A q bits = some (w, rem)) : rem.length < bits.length := by
  induction bits generalizing q w rem with
  | nil => simp [decodeOne] at h
  | cons b bs ih =>
    simp only [decodeOne] at h
    cases hs : A.step q b with
    | emit =>
      simp only [hs] at h
      injection h with hpair
      have hrem : bs = rem := congrArg Prod.snd hpair
      subst hrem
      simp
    | dead =>
      simp only [hs] at h
      cases h
    | cont q' =>
      simp only [hs] at h
      cases hd : decodeOne A q' bs with
      | none => simp only [hd] at h; cases h
      | some p =>
        simp only [hd] at h
        injection h with hpair
        have hrem : p.2 = rem := congrArg Prod.snd hpair
        have hlt := ih hd
        rw [← hrem]
        simp; omega

/-- Deterministic infinite-length stream decoder resetting to `A.init` after every `emit`. -/
def decodeStream {S : Nat} (A : PrefixAut S) (bits : List Bool) : Option (List (List Bool)) :=
  match bits with
  | [] => some []
  | b :: bs =>
    match h : decodeOne A A.init (b :: bs) with
    | none => none
    | some (w, rem) =>
      have _ : rem.length < (b :: bs).length := decodeOne_length_lt A h
      match decodeStream A rem with
      | none => none
      | some ws => some (w :: ws)
termination_by bits.length

def stepVal {S : Nat} (f : Fin S → Int) (emitVal : Int) : Step S → Int
  | Step.cont q' => f q'
  | Step.emit => emitVal
  | Step.dead => 0

def charSum {S : Nat} (A : PrefixAut S) (B : Int) (mu : Fin S → Bool → Int) : Nat → Fin S → Int
  | 0, _ => 0
  | N + 1, q =>
    let br (b : Bool) : Int :=
      match A.step q b with
      | Step.dead => 0
      | Step.emit => mu q b * B ^ N
      | Step.cont q' => mu q b * charSum A B mu N q'
    br false + br true

def activePot {S : Nat} (A : PrefixAut S) (mu : Fin S → Bool → Int) (kappa : Fin S → Int) :
    Nat → Fin S → Int
  | 0, q => kappa q
  | N + 1, q =>
    let br (b : Bool) : Int :=
      match A.step q b with
      | Step.dead => 0
      | Step.emit => 0
      | Step.cont q' => mu q b * activePot A mu kappa N q'
    br false + br true

def costSum {S : Nat} (A : PrefixAut S) (B : Int) (mu cost : Fin S → Bool → Int) :
    Nat → Fin S → Int
  | 0, _ => 0
  | N + 1, q =>
    let br (b : Bool) : Int :=
      match A.step q b with
      | Step.dead => 0
      | Step.emit => mu q b * (cost q b * B ^ N)
      | Step.cont q' => mu q b * (cost q b * charSum A B mu N q' + costSum A B mu cost N q')
    br false + br true

def activeCostPot {S : Nat} (A : PrefixAut S) (mu cost : Fin S → Bool → Int)
    (kappa phi : Fin S → Int) : Nat → Fin S → Int
  | 0, q => phi q
  | N + 1, q =>
    let br (b : Bool) : Int :=
      match A.step q b with
      | Step.dead => 0
      | Step.emit => 0
      | Step.cont q' =>
        mu q b * (cost q b * activePot A mu kappa N q' + activeCostPot A mu cost kappa phi N q')
    br false + br true

def activeMass {S : Nat} (A : PrefixAut S) : Nat → Fin S → Nat
  | 0, _ => 1
  | N + 1, q =>
    let br (b : Bool) : Nat :=
      match A.step q b with
      | Step.cont q' => activeMass A N q'
      | _ => 0
    br false + br true

/-! ### Semantic Equivalence Bridge: Exhaustive `2^N` Bit-String Evaluation (`B = 2`) -/

def evalRunChar {S : Nat} (A : PrefixAut S) (mu : Fin S → Bool → Int) (q : Fin S)
    (prodMu : Int) : List Bool → Int
  | [] => 0
  | b :: bs =>
    let pm := prodMu * mu q b
    match A.step q b with
    | Step.emit => pm
    | Step.dead => 0
    | Step.cont q' => evalRunChar A mu q' pm bs

def evalRunCost {S : Nat} (A : PrefixAut S) (mu cost : Fin S → Bool → Int) (q : Fin S)
    (prodMu sumCost : Int) : List Bool → Int
  | [] => 0
  | b :: bs =>
    let pm := prodMu * mu q b
    let sc := sumCost + cost q b
    match A.step q b with
    | Step.emit => pm * sc
    | Step.dead => 0
    | Step.cont q' => evalRunCost A mu cost q' pm sc bs

def IsKirchhoff0 {S : Nat} (A : PrefixAut S) (B : Int) (mu : Fin S → Bool → Int)
    (D : Int) (kappa : Fin S → Int) : Prop :=
  ∀ q : Fin S,
    B * kappa q =
      mu q false * stepVal kappa D (A.step q false) +
      mu q true  * stepVal kappa D (A.step q true)

def IsKirchhoff1 {S : Nat} (A : PrefixAut S) (B : Int) (mu cost : Fin S → Bool → Int)
    (D : Int) (kappa phi : Fin S → Int) : Prop :=
  ∀ q : Fin S,
    B * phi q =
      mu q false * (cost q false * stepVal kappa D (A.step q false) + stepVal phi 0 (A.step q false)) +
      mu q true  * (cost q true  * stepVal kappa D (A.step q true)  + stepVal phi 0 (A.step q true))

def runActive {S : Nat} (A : PrefixAut S) : Fin S → List Bool → Option (Fin S)
  | q, [] => some q
  | q, b :: bs =>
    match A.step q b with
    | Step.cont q' => runActive A q' bs
    | _ => none

def repeatList (c : List Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => c ++ repeatList c n

def fibAut (k : Nat) (hk : 0 < k) : PrefixAut k where
  init := ⟨0, hk⟩
  step := fun q b =>
    match b with
    | false => Step.cont ⟨0, hk⟩
    | true =>
      if h : q.val + 1 < k then Step.cont ⟨q.val + 1, h⟩
      else Step.emit

/-- Theorem T1c (`k`-bonacci Exact Expected-Length Conservation = `2^(k+1) - 2`, ∀ k ≥ 1, ∀ N). -/
def fibLenPhi (k : Nat) (q : Fin k) : Int := (2 : Int) ^ (k + 1) - (2 : Int) ^ (q.val + 1)

/-- Theorem T1d (`k`-bonacci Exact Wald Zero-Bias Conservation, ∀ k ≥ 1, ∀ N). -/
def biasCost {S : Nat} (_ : Fin S) (b : Bool) : Int := if b then 1 else -1

def popParityMu {S : Nat} (_ : Fin S) (b : Bool) : Int := if b then -1 else 1

def lenParityMu {S : Nat} (_ : Fin S) (_ : Bool) : Int := -1

def fibPopKappa (k : Nat) (q : Fin k) : Int :=
  negOnePow (k + q.val) * jacobsthal (q.val + 1)

def fibLenPKappa (k : Nat) (q : Fin k) : Int :=
  negOnePow (k + q.val) * jacobsthal (q.val + 2)

def runAut (a b : Nat) (ha : 0 < a) (hb : 0 < b) : PrefixAut (a + b - 1) where
  init := ⟨0, by omega⟩
  step := fun q bit =>
    match bit with
    | false =>
      if h0 : q.val = 0 ∨ a ≤ q.val then
        if ha1 : 1 < a then Step.cont ⟨1, by omega⟩ else Step.dead
      else
        if hnext : q.val + 1 < a then Step.cont ⟨q.val + 1, by omega⟩ else Step.dead
    | true =>
      if hlt : q.val < a then
        if hb1 : 1 < b then Step.cont ⟨a, by omega⟩ else Step.emit
      else
        if hnext : q.val + 1 < a + b - 1 then Step.cont ⟨q.val + 1, hnext⟩ else Step.emit

def runD (a b : Nat) : Int := (2 : Int) ^ (a - 1) + (2 : Int) ^ (b - 1) - 1

def runKraftKappa (a b : Nat) (q : Fin (a + b - 1)) : Int :=
  let A : Int := (2 : Int) ^ (a - 1)
  if q.val = 0 then 2 * A - 1
  else if q.val < a then 2 * (A - (2 : Int) ^ (q.val - 1))
  else 2 * (A + (2 : Int) ^ (q.val - a) - 1)

def runPopD (a b : Nat) : Int :=
  2 * (2 : Int) ^ (a - 1) * jacobsthal (b + 1) - 2 * jacobsthal (b - 1)

def runPopKappa (a b : Nat) (q : Fin (a + b - 1)) : Int :=
  let A : Int := (2 : Int) ^ (a - 1)
  if q.val = 0 then negOnePow b * (2 * A - 1)
  else if q.val < a then negOnePow b * (2 * (A - (2 : Int) ^ (q.val - 1)))
  else
    let j := q.val - a + 1
    negOnePow (b + j) * (2 * A * jacobsthal (j + 1) - 2 * jacobsthal (j - 1))

def runBiasNum (a b : Nat) : Int :=
  let A : Int := (2 : Int) ^ (a - 1)
  let B : Int := (2 : Int) ^ (b - 1)
  2 * A * B * ((a : Int) + (b : Int) - 2) - ((a : Int) - 2) * A - ((b : Int) - 2) * B - 1

def runBiasPhi (a b : Nat) (q : Fin (a + b - 1)) : Int :=
  let A : Int := (2 : Int) ^ (a - 1)
  let B : Int := (2 : Int) ^ (b - 1)
  let D : Int := A + B - 1
  if q.val = 0 then
    runBiasNum a b
  else if q.val < a then
    2 * (A - (2 : Int) ^ (q.val - 1)) * (B * ((b : Int) - 1) + (B - 1) * ((a : Int) - 1)) +
      2 * D * ((a : Int) - (q.val : Int)) * (2 : Int) ^ (q.val - 1)
  else
    let j := q.val - a + 1
    2 * (B - (2 : Int) ^ (j - 1)) * (A * ((a : Int) - 1) + (A - 1) * ((b : Int) - 1)) +
      2 * D * ((b : Int) - (j : Int)) * (2 : Int) ^ (j - 1)

def runKraftScaled (a b : Nat) (q : Fin (a + b - 1)) : Int :=
  runD a b * runKraftKappa a b q

def toBitsMSB : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, n => toBitsMSB w (n / 2) ++ [n % 2 == 1]

def fromBitsMSB_acc : Nat → List Bool → Nat
  | acc, [] => acc
  | acc, b :: bs => fromBitsMSB_acc (2 * acc + if b then 1 else 0) bs

def fromBitsMSB (bs : List Bool) : Nat := fromBitsMSB_acc 0 bs

theorem toBitsMSB_length (w n : Nat) : (toBitsMSB w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toBitsMSB, ih]

theorem fromBitsMSB_acc_append (acc : Nat) (u v : List Bool) :
    fromBitsMSB_acc acc (u ++ v) = fromBitsMSB_acc (fromBitsMSB_acc acc u) v := by
  induction u generalizing acc with
  | nil => rfl
  | cons b u ih => simp [fromBitsMSB_acc, ih]

theorem fromBitsMSB_toBitsMSB (w n : Nat) (hn : n < 2 ^ w) :
    fromBitsMSB (toBitsMSB w n) = n := by
  induction w generalizing n with
  | zero => simp [toBitsMSB, fromBitsMSB, fromBitsMSB_acc]; omega
  | succ w ih =>
    simp only [toBitsMSB, fromBitsMSB]
    rw [fromBitsMSB_acc_append]
    have hdiv : n / 2 < 2 ^ w := by rw [Nat.pow_succ] at hn; omega
    have ih' := ih (n / 2) hdiv
    simp only [fromBitsMSB] at ih'
    rw [ih']
    simp only [fromBitsMSB_acc]
    by_cases hmod : n % 2 = 1
    · simp [hmod]; omega
    · have h0 : n % 2 = 0 := by omega
      simp [h0]; omega

def floorLog2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, m => if m ≤ 1 then 0 else 1 + floorLog2Aux fuel (m / 2)

def floorLog2 (m : Nat) : Nat := floorLog2Aux m m

theorem floorLog2Aux_spec : ∀ (fuel m : Nat), 1 ≤ m → m ≤ fuel →
    2 ^ floorLog2Aux fuel m ≤ m ∧ m < 2 ^ (floorLog2Aux fuel m + 1) := by
  intro fuel
  induction fuel with
  | zero => intro m hm hle; omega
  | succ fuel ih =>
    intro m hm hle
    simp only [floorLog2Aux]
    by_cases hm1 : m ≤ 1
    · simp only [hm1, ↓reduceIte]
      have : m = 1 := by omega
      subst this; decide
    · simp only [hm1, ↓reduceIte]
      have ⟨h1, h2⟩ := ih (m / 2) (by omega) (by omega)
      have hp1 : 2 ^ (1 + floorLog2Aux fuel (m / 2)) = 2 ^ floorLog2Aux fuel (m / 2) * 2 := by
        rw [Nat.add_comm, Nat.pow_succ]
      have hp2 : 2 ^ (1 + floorLog2Aux fuel (m / 2) + 1) = 2 ^ (floorLog2Aux fuel (m / 2) + 1) * 2 := by
        have : 1 + floorLog2Aux fuel (m / 2) + 1 = (floorLog2Aux fuel (m / 2) + 1) + 1 := by omega
        rw [this, Nat.pow_succ]
      rw [hp1, hp2]
      omega

theorem floorLog2_spec (m : Nat) (hm : 1 ≤ m) :
    2 ^ floorLog2 m ≤ m ∧ m < 2 ^ (floorLog2 m + 1) :=
  floorLog2Aux_spec m m hm (Nat.le_refl m)

/-- Self-delimiting binary prefix code on `Nat`. -/
structure PrefixCode where
  enc : Nat → List Bool
  decOne : List Bool → Option (Nat × List Bool)
  roundtrip : ∀ n rest, decOne (enc n ++ rest) = some (n, rest)
  nonempty : ∀ n, enc n ≠ []

def PrefixCode.encStream (C : PrefixCode) (ns : List Nat) : List Bool :=
  (ns.map C.enc).flatten

def PrefixCode.decStream (C : PrefixCode) (bits : List Bool) : Option (List Nat) :=
  match bits with
  | [] => some []
  | b :: bs =>
    match C.decOne (b :: bs) with
    | none => none
    | some (n, rem) =>
      if _h : rem.length < (b :: bs).length then
        match C.decStream rem with
        | none => none
        | some ns => some (n :: ns)
      else none
termination_by bits.length

def PrefixCode.OrderPreserving (C : PrefixCode) : Prop :=
  ∀ m n : Nat, m < n → lexDiverge (C.enc m) (C.enc n)

def unary1DecAux (k : Nat) : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (k, rest)
  | true :: rest => unary1DecAux (k + 1) rest

theorem unary1DecAux_spec (k n : Nat) (rest : List Bool) :
    unary1DecAux k (List.replicate n true ++ (false :: rest)) = some (k + n, rest) := by
  induction n generalizing k with
  | zero => simp [unary1DecAux]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, unary1DecAux]
    rw [ih (k + 1)]
    congr 2; omega

def unary1Code : PrefixCode where
  enc n := List.replicate n true ++ [false]
  decOne := unary1DecAux 0
  roundtrip n rest := by
    have h := unary1DecAux_spec 0 n rest
    simpa [List.append_assoc] using h
  nonempty n := by cases n <;> simp

/-- The Compositional Elias-Lift Operator `eliasLift C`. -/
def eliasLift (C : PrefixCode) : PrefixCode where
  enc n :=
    let L := floorLog2 (n + 1)
    C.enc L ++ toBitsMSB L ((n + 1) - 2 ^ L)
  decOne bits :=
    match C.decOne bits with
    | none => none
    | some (L, rest) =>
      if rest.length < L then none
      else
        let rem := fromBitsMSB (rest.take L)
        some (2 ^ L + rem - 1, rest.drop L)
  roundtrip n rest := by
    dsimp only
    have ⟨hlo, hhi⟩ := floorLog2_spec (n + 1) (by omega)
    have hrem_lt : (n + 1) - 2 ^ floorLog2 (n + 1) < 2 ^ floorLog2 (n + 1) := by
      have hp : 2 ^ (floorLog2 (n + 1) + 1) = 2 ^ floorLog2 (n + 1) * 2 := Nat.pow_succ 2 _
      omega
    have hlen : (toBitsMSB (floorLog2 (n + 1)) ((n + 1) - 2 ^ floorLog2 (n + 1))).length =
        floorLog2 (n + 1) := toBitsMSB_length _ _
    rw [List.append_assoc, C.roundtrip (floorLog2 (n + 1)) _]
    have hnotlt : ¬ ((toBitsMSB (floorLog2 (n + 1)) ((n + 1) - 2 ^ floorLog2 (n + 1)) ++ rest).length <
        floorLog2 (n + 1)) := by
      simp [hlen]
    simp only [hnotlt, ↓reduceIte]
    have htake : (toBitsMSB (floorLog2 (n + 1)) ((n + 1) - 2 ^ floorLog2 (n + 1)) ++ rest).take
        (floorLog2 (n + 1)) = toBitsMSB (floorLog2 (n + 1)) ((n + 1) - 2 ^ floorLog2 (n + 1)) := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hdrop : (toBitsMSB (floorLog2 (n + 1)) ((n + 1) - 2 ^ floorLog2 (n + 1)) ++ rest).drop
        (floorLog2 (n + 1)) = rest := by
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
    rw [htake, hdrop, fromBitsMSB_toBitsMSB _ _ hrem_lt]
    have hrec : 2 ^ floorLog2 (n + 1) + (n + 1 - 2 ^ floorLog2 (n + 1)) - 1 = n := by omega
    rw [hrec]
  nonempty n := by
    intro h
    have h1 := List.append_eq_nil_iff.mp h
    exact C.nonempty _ h1.1

def sumRangeNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => sumRangeNat f N + f N

def sumRangeInt (f : Nat → Int) : Nat → Int
  | 0 => 0
  | N + 1 => sumRangeInt f N + f N

def kraftBlock (C : PrefixCode) (H N : Nat) : Nat :=
  sumRangeNat (fun n => 2 ^ (H - (C.enc n).length)) N

def popParityBlock (C : PrefixCode) (H N : Nat) : Int :=
  sumRangeInt (fun n => negOnePow (popcount (C.enc n)) * ((2 ^ (H - (C.enc n).length) : Nat) : Int)) N

def lenBlock (C : PrefixCode) (N : Nat) : Nat :=
  sumRangeNat (fun n => (C.enc n).length) N

def expLenBlock (C : PrefixCode) (H N : Nat) : Nat :=
  sumRangeNat (fun n => (C.enc n).length * 2 ^ (H - (C.enc n).length)) N

def eliasTower : Nat → PrefixCode
  | 0 => unary1Code
  | r + 1 => eliasLift (eliasTower r)

def towerBound : Nat → Nat → Nat
  | 0, M => M
  | r + 1, M => 2 ^ (towerBound r M) - 1

/-- Clean upper bound on codeword lengths in block `M` of `eliasTower r`. -/
def towerMaxLen : Nat → Nat → Nat
  | 0, M => M + 1
  | r + 1, M => towerMaxLen r M + towerBound r M

end PrefixCodeEngine
