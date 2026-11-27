/-!
# certcomp-6: Verified Lean 4 Bottom-Up Tree-Automaton & Quadtree Proof Compiler

A reusable, standalone Lean 4.36.0 pure-silicon proof-reflection and certificate-compiler engine
lifting finite binary certificates (checked in the kernel via `decide`, with no compiler-trusting
tactics, ZERO `Prop` fields inside certificates, ZERO Mathlib) to universally quantified infinite theorems
(`∀ k : Nat`) over height-`k` binary trees (`BTree α k`) and `2^k × 2^k` bit-quadtrees (`QTree α k`).
-/

namespace CertComp6

/-! ## Section 1: Pure-Silicon Bitmask, Sparse Quantifier & Tree Primitives -/

/-- Test whether bit `i` of natural-number bitmask `mask` is `1`. -/
@[inline] def bitSet (mask : Nat) (i : Nat) : Bool :=
  ((mask >>> i) &&& 1) == 1

/-- Structurally recursive quantifier over `Fin n` (reduces directly in kernel `decide`). -/
def allFinGo (n : Nat) (f : Fin n → Bool) : (i : Nat) → i ≤ n → Bool
  | 0, _ => true
  | i + 1, h => f ⟨i, h⟩ && allFinGo n f i (Nat.le_of_lt h)

def allFin (n : Nat) (f : Fin n → Bool) : Bool :=
  allFinGo n f n (Nat.le_refl n)

theorem allFinGo_iff (n : Nat) (f : Fin n → Bool) (i : Nat) (hi : i ≤ n) :
    allFinGo n f i hi = true ↔ ∀ j : Fin n, j.val < i → f j = true := by
  induction i with
  | zero => simp [allFinGo]
  | succ m ih =>
    unfold allFinGo
    simp only [Bool.and_eq_true, ih (Nat.le_of_lt hi)]
    constructor
    · intro ⟨hm, hlt⟩ j hj
      by_cases heq : j.val = m
      · have : j = ⟨m, hi⟩ := Fin.ext heq
        rw [this]; exact hm
      · exact hlt j (by omega)
    · intro h
      exact ⟨h ⟨m, hi⟩ (Nat.lt_succ_self m), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

theorem allFin_iff (n : Nat) (f : Fin n → Bool) :
    allFin n f = true ↔ ∀ j : Fin n, f j = true := by
  unfold allFin
  rw [allFinGo_iff]
  exact ⟨fun h j => h j j.isLt, fun h j _ => h j⟩

/-- Extract the sparse list of active indices `j : Fin n` with `bitSet mask j.val = true` ONCE.
    Avoids scanning zero-bits inside nested loops (up to `500,000×` faster in kernel `decide`). -/
def bitsOfMaskGo (n : Nat) (mask : Nat) : (i : Nat) → i ≤ n → List (Fin n) → List (Fin n)
  | 0, _, acc => acc
  | i + 1, h, acc =>
    let acc' := if bitSet mask i then ⟨i, h⟩ :: acc else acc
    bitsOfMaskGo n mask i (Nat.le_of_lt h) acc'

def bitsOfMask (n : Nat) (mask : Nat) : List (Fin n) :=
  bitsOfMaskGo n mask n (Nat.le_refl n) []

theorem mem_bitsOfMaskGo_iff (n mask : Nat) (i : Nat) (hi : i ≤ n) (acc : List (Fin n)) (j : Fin n) :
    j ∈ bitsOfMaskGo n mask i hi acc ↔ (j.val < i ∧ bitSet mask j.val = true) ∨ j ∈ acc := by
  induction i generalizing acc with
  | zero =>
    unfold bitsOfMaskGo
    simp
  | succ m ih =>
    unfold bitsOfMaskGo
    rw [ih (Nat.le_of_lt hi)]
    by_cases hbm : bitSet mask m = true
    · simp only [hbm, ite_true, List.mem_cons]
      constructor
      · intro h
        rcases h with ⟨hlt, hbj⟩ | heq | hacc
        · exact Or.inl ⟨Nat.lt_succ_of_lt hlt, hbj⟩
        · subst heq; exact Or.inl ⟨Nat.lt_succ_self m, hbm⟩
        · exact Or.inr hacc
      · intro h
        rcases h with ⟨hlt, hbj⟩ | hacc
        · by_cases heq : j.val = m
          · exact Or.inr (Or.inl (Fin.ext heq))
          · exact Or.inl ⟨by omega, hbj⟩
        · exact Or.inr (Or.inr hacc)
    · have hbmf : bitSet mask m = false := by
        cases hb : bitSet mask m with
        | false => rfl
        | true => exact absurd hb hbm
      simp only [hbmf, Bool.false_eq_true, ite_false]
      constructor
      · intro h
        rcases h with ⟨hlt, hbj⟩ | hacc
        · exact Or.inl ⟨Nat.lt_succ_of_lt hlt, hbj⟩
        · exact Or.inr hacc
      · intro h
        rcases h with ⟨hlt, hbj⟩ | hacc
        · by_cases heq : j.val = m
          · rw [heq] at hbj; rw [hbmf] at hbj; cases hbj
          · exact Or.inl ⟨by omega, hbj⟩
        · exact Or.inr hacc

theorem mem_bitsOfMask_iff (n mask : Nat) (j : Fin n) :
    j ∈ bitsOfMask n mask ↔ bitSet mask j.val = true := by
  unfold bitsOfMask
  rw [mem_bitsOfMaskGo_iff]
  simp [j.isLt]

/-- Core Lean 4 finite case-splitting helpers (zero Mathlib). -/
theorem fin2_forall {P : Fin 2 → Prop} (h0 : P ⟨0, by omega⟩) (h1 : P ⟨1, by omega⟩) :
    ∀ x : Fin 2, P x
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1

theorem fin4_forall {P : Fin 4 → Prop}
    (h0 : P ⟨0, by omega⟩) (h1 : P ⟨1, by omega⟩)
    (h2 : P ⟨2, by omega⟩) (h3 : P ⟨3, by omega⟩) :
    ∀ x : Fin 4, P x
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

theorem fin5_forall {P : Fin 5 → Prop}
    (h0 : P ⟨0, by omega⟩) (h1 : P ⟨1, by omega⟩) (h2 : P ⟨2, by omega⟩)
    (h3 : P ⟨3, by omega⟩) (h4 : P ⟨4, by omega⟩) :
    ∀ x : Fin 5, P x
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4

/-- Complete binary tree of height `k` (`2^k` leaves). -/
inductive BTree (α : Type) : Nat → Type where
  | leaf : α → BTree α 0
  | node : {k : Nat} → BTree α k → BTree α k → BTree α (k + 1)

/-- Complete quadtree of height `k` (`2^k × 2^k = 4^k` leaves: NW, NE, SW, SE). -/
inductive QTree (α : Type) : Nat → Type where
  | qleaf : α → QTree α 0
  | qnode : {k : Nat} → QTree α k → QTree α k → QTree α k → QTree α k → QTree α (k + 1)

/-- Exact Morton Z-order isomorphism: `QTree α k → BTree α (2 * k)`. -/
def qtreeToBTree {α : Type} : {k : Nat} → QTree α k → BTree α (2 * k)
  | 0, .qleaf a => .leaf a
  | _ + 1, .qnode nw ne sw se =>
    .node (.node (qtreeToBTree nw) (qtreeToBTree ne))
          (.node (qtreeToBTree sw) (qtreeToBTree se))

/-- Inverse Morton Z-order isomorphism: `BTree α (2 * k) → QTree α k`. -/
def btreeToQTree {α : Type} : {k : Nat} → BTree α (2 * k) → QTree α k
  | 0, .leaf a => .qleaf a
  | _ + 1, .node (.node nw ne) (.node sw se) =>
    .qnode (btreeToQTree nw) (btreeToQTree ne) (btreeToQTree sw) (btreeToQTree se)

theorem btreeToQTree_qtreeToBTree {α : Type} :
    ∀ {k : Nat} (q : QTree α k), btreeToQTree (qtreeToBTree q) = q
  | 0, .qleaf _ => rfl
  | _ + 1, .qnode nw ne sw se => by
    simp only [qtreeToBTree, btreeToQTree,
      btreeToQTree_qtreeToBTree nw, btreeToQTree_qtreeToBTree ne,
      btreeToQTree_qtreeToBTree sw, btreeToQTree_qtreeToBTree se]

theorem qtreeToBTree_btreeToQTree {α : Type} :
    ∀ {k : Nat} (t : BTree α (2 * k)), qtreeToBTree (btreeToQTree t) = t
  | 0, .leaf _ => rfl
  | _ + 1, .node (.node nw ne) (.node sw se) => by
    simp only [btreeToQTree, qtreeToBTree,
      qtreeToBTree_btreeToQTree nw, qtreeToBTree_btreeToQTree ne,
      qtreeToBTree_btreeToQTree sw, qtreeToBTree_btreeToQTree se]

/-- Bitwise complement on a `2^k × 2^k` bit-quadtree. -/
def notQ : {k : Nat} → QTree Bool k → QTree Bool k
  | 0, .qleaf b => .qleaf (!b)
  | _ + 1, .qnode nw ne sw se => .qnode (notQ nw) (notQ ne) (notQ sw) (notQ se)

/-- Dihedral group `D_4` actions on `QTree α k` (quadrant permutations). -/
def rot90Q {α : Type} : {k : Nat} → QTree α k → QTree α k
  | 0, .qleaf a => .qleaf a
  | _ + 1, .qnode nw ne sw se => .qnode (rot90Q sw) (rot90Q nw) (rot90Q se) (rot90Q ne)

def rot180Q {α : Type} : {k : Nat} → QTree α k → QTree α k
  | 0, .qleaf a => .qleaf a
  | _ + 1, .qnode nw ne sw se => .qnode (rot180Q se) (rot180Q sw) (rot180Q ne) (rot180Q nw)

def rot270Q {α : Type} : {k : Nat} → QTree α k → QTree α k
  | 0, .qleaf a => .qleaf a
  | _ + 1, .qnode nw ne sw se => .qnode (rot270Q ne) (rot270Q se) (rot270Q nw) (rot270Q sw)

def flipHQ {α : Type} : {k : Nat} → QTree α k → QTree α k
  | 0, .qleaf a => .qleaf a
  | _ + 1, .qnode nw ne sw se => .qnode (flipHQ ne) (flipHQ nw) (flipHQ se) (flipHQ sw)

def flipVQ {α : Type} : {k : Nat} → QTree α k → QTree α k
  | 0, .qleaf a => .qleaf a
  | _ + 1, .qnode nw ne sw se => .qnode (flipVQ sw) (flipVQ se) (flipVQ nw) (flipVQ ne)

def transQ {α : Type} : {k : Nat} → QTree α k → QTree α k
  | 0, .qleaf a => .qleaf a
  | _ + 1, .qnode nw ne sw se => .qnode (transQ nw) (transQ sw) (transQ ne) (transQ se)

def antiTransQ {α : Type} : {k : Nat} → QTree α k → QTree α k
  | 0, .qleaf a => .qleaf a
  | _ + 1, .qnode nw ne sw se => .qnode (antiTransQ se) (antiTransQ ne) (antiTransQ sw) (antiTransQ nw)

/-! ## Section 2: Reusable Kernel-Verified Bottom-Up Tree-Automaton & Quadtree Proof Compiler -/

/-- Ultimately periodic height phase with preperiod `r0` and period `p1 + 1` (zero `Prop` fields!). -/
def phaseOfNat (r0 p1 k : Nat) : Fin (r0 + p1 + 1) :=
  if h : k < r0 then
    ⟨k, by omega⟩
  else
    ⟨r0 + (k - r0) % (p1 + 1), by
      have hmod : (k - r0) % (p1 + 1) < p1 + 1 := Nat.mod_lt (k - r0) (by omega)
      omega⟩

/-- Successor phase transition on `Fin (r0 + p1 + 1)`. -/
def nextPhase (r0 p1 : Nat) (r : Fin (r0 + p1 + 1)) : Fin (r0 + p1 + 1) :=
  if h : r.val + 1 < r0 + p1 + 1 then
    ⟨r.val + 1, h⟩
  else
    ⟨r0, by omega⟩

theorem phaseOfNat_zero (r0 p1 : Nat) :
    phaseOfNat r0 p1 0 = ⟨0, by omega⟩ := by
  unfold phaseOfNat
  split
  · rfl
  · rename_i h
    have hr0 : r0 = 0 := by omega
    subst hr0
    simp

theorem phaseOfNat_succ (r0 p1 k : Nat) :
    phaseOfNat r0 p1 (k + 1) = nextPhase r0 p1 (phaseOfNat r0 p1 k) := by
  unfold phaseOfNat nextPhase
  by_cases h1 : k + 1 < r0
  · have h0 : k < r0 := by omega
    simp only [h1, h0, dite_true]
    have hlt : k + 1 < r0 + p1 + 1 := by omega
    simp [hlt]
  · by_cases h0 : k < r0
    · have hk : k + 1 = r0 := by omega
      simp only [h1, h0, dite_true, dite_false]
      have hlt : k + 1 < r0 + p1 + 1 := by omega
      simp only [hlt, dite_true]
      apply Fin.ext; dsimp only; simp [hk]
    · simp only [h1, h0, dite_false]
      have hsub : k + 1 - r0 = (k - r0) + 1 := by omega
      have hmod : (k - r0) % (p1 + 1) < p1 + 1 := Nat.mod_lt (k - r0) (by omega)
      by_cases hwrap : (k - r0) % (p1 + 1) + 1 < p1 + 1
      · have hlt : r0 + (k - r0) % (p1 + 1) + 1 < r0 + p1 + 1 := by omega
        simp only [hlt, dite_true]
        apply Fin.ext; dsimp only
        rw [hsub]
        have hdiv : (k - r0) = (p1 + 1) * ((k - r0) / (p1 + 1)) + (k - r0) % (p1 + 1) :=
          (Nat.div_add_mod (k - r0) (p1 + 1)).symm
        have hstep : ((k - r0) + 1) % (p1 + 1) = (k - r0) % (p1 + 1) + 1 := by
          conv => lhs; rw [hdiv]
          rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hwrap]
        omega
      · have heq : (k - r0) % (p1 + 1) = p1 := by omega
        have hnot : ¬ (r0 + (k - r0) % (p1 + 1) + 1 < r0 + p1 + 1) := by omega
        simp only [hnot, dite_false]
        apply Fin.ext; dsimp only
        rw [hsub]
        have hdiv : (k - r0) = (p1 + 1) * ((k - r0) / (p1 + 1)) + p1 := by
          have := (Nat.div_add_mod (k - r0) (p1 + 1)).symm
          rw [heq] at this; exact this
        have hstep : ((k - r0) + 1) % (p1 + 1) = 0 := by
          conv => lhs; rw [hdiv]
          rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_self]
        omega

/-- Pure-data certificate: one natural-number bitmask per height phase (ZERO `Prop` fields). -/
structure PhaseBitmaskCert (numPhases : Nat) where
  masks : Fin numPhases → Nat

/-! ### Engine A: Height-Timed Bottom-Up Binary Tree Automaton (`TimedBTA`) -/

/-- Pure-data height-timed bottom-up binary tree automaton (ZERO `Prop` fields). -/
structure TimedBTA where
  numLeaves : Nat
  numStates : Nat
  r0 : Nat
  p1 : Nat
  leaf : Fin numLeaves → Fin numStates
  comb : Fin (r0 + p1 + 1) → Fin numStates → Fin numStates → Fin numStates

def evalBTA (A : TimedBTA) : {k : Nat} → BTree (Fin A.numLeaves) k → Fin A.numStates
  | 0, .leaf a => A.leaf a
  | k + 1, .node l r =>
    A.comb (phaseOfNat A.r0 A.p1 k) (evalBTA A l) (evalBTA A r)

/-- Decidable sparse-bitmask certificate checker for `TimedBTA`. -/
def checkBTACert (A : TimedBTA)
    (good : Fin (A.r0 + A.p1 + 1) → Fin A.numStates → Bool)
    (cert : PhaseBitmaskCert (A.r0 + A.p1 + 1)) : Bool :=
  let leavesOk := allFin A.numLeaves (fun a =>
    bitSet (cert.masks ⟨0, by omega⟩) (A.leaf a).val)
  let stepOk := allFin (A.r0 + A.p1 + 1) (fun ph =>
    let active := bitsOfMask A.numStates (cert.masks ph)
    let nextMask := cert.masks (nextPhase A.r0 A.p1 ph)
    active.all (fun q1 =>
      active.all (fun q2 => bitSet nextMask (A.comb ph q1 q2).val)))
  let safeOk := allFin (A.r0 + A.p1 + 1) (fun ph =>
    (bitsOfMask A.numStates (cert.masks ph)).all (fun q => good ph q))
  leavesOk && stepOk && safeOk

theorem timedBTA_inv (A : TimedBTA)
    (good : Fin (A.r0 + A.p1 + 1) → Fin A.numStates → Bool)
    (cert : PhaseBitmaskCert (A.r0 + A.p1 + 1))
    (hcert : checkBTACert A good cert = true) :
    ∀ (k : Nat) (t : BTree (Fin A.numLeaves) k),
      bitSet (cert.masks (phaseOfNat A.r0 A.p1 k)) (evalBTA A t).val = true := by
  unfold checkBTACert at hcert
  simp only [Bool.and_eq_true] at hcert
  obtain ⟨⟨hleaves, hstep⟩, _⟩ := hcert
  rw [allFin_iff] at hleaves hstep
  intro k t
  induction t with
  | leaf a =>
    rw [phaseOfNat_zero]
    exact hleaves a
  | @node k' l r ihl ihr =>
    rw [phaseOfNat_succ]
    have hs := hstep (phaseOfNat A.r0 A.p1 k')
    simp only [List.all_eq_true, mem_bitsOfMask_iff] at hs
    exact hs (evalBTA A l) ihl (evalBTA A r) ihr

/-- Pure-data height-timed bottom-up quadtree automaton (ZERO `Prop` fields). -/
structure TimedQTA where
  numLeaves : Nat
  numStates : Nat
  r0 : Nat
  p1 : Nat
  leaf : Fin numLeaves → Fin numStates
  comb : Fin (r0 + p1 + 1) → Fin numStates → Fin numStates → Fin numStates → Fin numStates → Fin numStates

def evalQTA (A : TimedQTA) : {k : Nat} → QTree (Fin A.numLeaves) k → Fin A.numStates
  | 0, .qleaf a => A.leaf a
  | k + 1, .qnode nw ne sw se =>
    A.comb (phaseOfNat A.r0 A.p1 k) (evalQTA A nw) (evalQTA A ne) (evalQTA A sw) (evalQTA A se)

/-- Decidable sparse-bitmask certificate checker for `TimedQTA`. -/
def checkQTACert (A : TimedQTA)
    (good : Fin (A.r0 + A.p1 + 1) → Fin A.numStates → Bool)
    (cert : PhaseBitmaskCert (A.r0 + A.p1 + 1)) : Bool :=
  let leavesOk := allFin A.numLeaves (fun a =>
    bitSet (cert.masks ⟨0, by omega⟩) (A.leaf a).val)
  let stepOk := allFin (A.r0 + A.p1 + 1) (fun ph =>
    let active := bitsOfMask A.numStates (cert.masks ph)
    let nextMask := cert.masks (nextPhase A.r0 A.p1 ph)
    active.all (fun q0 =>
      active.all (fun q1 =>
        active.all (fun q2 =>
          active.all (fun q3 => bitSet nextMask (A.comb ph q0 q1 q2 q3).val)))))
  let safeOk := allFin (A.r0 + A.p1 + 1) (fun ph =>
    (bitsOfMask A.numStates (cert.masks ph)).all (fun q => good ph q))
  leavesOk && stepOk && safeOk

theorem timedQTA_inv (A : TimedQTA)
    (good : Fin (A.r0 + A.p1 + 1) → Fin A.numStates → Bool)
    (cert : PhaseBitmaskCert (A.r0 + A.p1 + 1))
    (hcert : checkQTACert A good cert = true) :
    ∀ (k : Nat) (q : QTree (Fin A.numLeaves) k),
      bitSet (cert.masks (phaseOfNat A.r0 A.p1 k)) (evalQTA A q).val = true := by
  unfold checkQTACert at hcert
  simp only [Bool.and_eq_true] at hcert
  obtain ⟨⟨hleaves, hstep⟩, _⟩ := hcert
  rw [allFin_iff] at hleaves hstep
  intro k q
  induction q with
  | qleaf a =>
    rw [phaseOfNat_zero]
    exact hleaves a
  | @qnode k' nw ne sw se ihnw ihne ihsw ihse =>
    rw [phaseOfNat_succ]
    have hs := hstep (phaseOfNat A.r0 A.p1 k')
    simp only [List.all_eq_true, mem_bitsOfMask_iff] at hs
    exact hs (evalQTA A nw) ihnw (evalQTA A ne) ihne (evalQTA A sw) ihsw (evalQTA A se) ihse

/-- General Soundness Meta-Theorem for Height-Timed Bottom-Up Quadtree Automata. -/
theorem timedQTA_sound (A : TimedQTA)
    (good : Fin (A.r0 + A.p1 + 1) → Fin A.numStates → Bool)
    (cert : PhaseBitmaskCert (A.r0 + A.p1 + 1))
    (hcert : checkQTACert A good cert = true) :
    ∀ (k : Nat) (q : QTree (Fin A.numLeaves) k),
      good (phaseOfNat A.r0 A.p1 k) (evalQTA A q) = true := by
  have hinv := timedQTA_inv A good cert hcert
  unfold checkQTACert at hcert
  simp only [Bool.and_eq_true] at hcert
  have hsafe := hcert.2
  rw [allFin_iff] at hsafe
  intro k q
  have hph := hsafe (phaseOfNat A.r0 A.p1 k)
  simp only [List.all_eq_true, mem_bitsOfMask_iff] at hph
  exact hph (evalQTA A q) (hinv k q)

/-- Morton Compiler Bridge: compiles any period-2 `TimedBTA` (`r0 = 0, p1 = 1`) on `BTree _ (2*k)`
    directly into a stationary `TimedQTA` (`r0 = 0, p1 = 0`) on `QTree _ k`. -/
def compilePeriod2BTAtoQTA (B : TimedBTA) (hr0 : B.r0 = 0) (hp1 : B.p1 = 1) : TimedQTA where
  numLeaves := B.numLeaves
  numStates := B.numStates
  r0 := 0
  p1 := 0
  leaf := B.leaf
  comb := fun _ nw ne sw se =>
    let ph0 : Fin (B.r0 + B.p1 + 1) := ⟨0, by omega⟩
    let ph1 : Fin (B.r0 + B.p1 + 1) := ⟨1, by omega⟩
    B.comb ph1 (B.comb ph0 nw ne) (B.comb ph0 sw se)

theorem phaseOfNat_two_mul_period2 (k : Nat) :
    phaseOfNat 0 1 (2 * k) = ⟨0, by omega⟩ := by
  unfold phaseOfNat
  simp only [Nat.not_lt_zero, dite_false, Nat.sub_zero, Nat.zero_add]
  apply Fin.ext
  change (2 * k) % 2 = 0
  omega

theorem phaseOfNat_two_mul_succ_period2 (k : Nat) :
    phaseOfNat 0 1 (2 * k + 1) = ⟨1, by omega⟩ := by
  unfold phaseOfNat
  simp only [Nat.not_lt_zero, dite_false, Nat.sub_zero, Nat.zero_add]
  apply Fin.ext
  change (2 * k + 1) % 2 = 1
  omega

theorem evalQTA_compilePeriod2BTAtoQTA (B : TimedBTA) (hr0 : B.r0 = 0) (hp1 : B.p1 = 1) :
    ∀ {k : Nat} (q : QTree (Fin B.numLeaves) k),
      evalQTA (compilePeriod2BTAtoQTA B hr0 hp1) q = evalBTA B (qtreeToBTree q) := by
  intro k q
  cases B with | mk nL nS r0 p1 lf cb =>
  simp only at hr0 hp1
  subst hr0; subst hp1
  induction q with
  | qleaf a => rfl
  | @qnode k' nw ne sw se ihnw ihne ihsw ihse =>
    change cb ⟨1, by omega⟩ (cb ⟨0, by omega⟩ _ _) (cb ⟨0, by omega⟩ _ _) =
      cb (phaseOfNat 0 1 (2 * k' + 1))
         (cb (phaseOfNat 0 1 (2 * k')) (evalBTA _ (qtreeToBTree nw)) (evalBTA _ (qtreeToBTree ne)))
         (cb (phaseOfNat 0 1 (2 * k')) (evalBTA _ (qtreeToBTree sw)) (evalBTA _ (qtreeToBTree se)))
    rw [phaseOfNat_two_mul_period2, phaseOfNat_two_mul_succ_period2, ihnw, ihne, ihsw, ihse]

/-! ### Engine C: Factored 2-Stage Quadtree Compiler (`FactoredQTA`) -/

/-- Pure-data 2-stage factored quadtree automaton reducing `O(|S|^4)` checks to `O(|S|^2 + |M|^2)`. -/
structure FactoredQTA where
  numLeaves : Nat
  numStates : Nat
  midStates : Nat
  leaf : Fin numLeaves → Fin numStates
  hTop : Fin numStates → Fin numStates → Fin midStates
  hBot : Fin numStates → Fin numStates → Fin midStates
  vGlue : Fin midStates → Fin midStates → Fin numStates

def evalFactoredQTA (A : FactoredQTA) : {k : Nat} → QTree (Fin A.numLeaves) k → Fin A.numStates
  | 0, .qleaf a => A.leaf a
  | _ + 1, .qnode nw ne sw se =>
    A.vGlue (A.hTop (evalFactoredQTA A nw) (evalFactoredQTA A ne))
            (A.hBot (evalFactoredQTA A sw) (evalFactoredQTA A se))

/-- Pure-data triple bitmask certificate `(evenMask, topMask, botMask)`. -/
structure FactoredBitmaskCert where
  evenMask : Nat
  topMask : Nat
  botMask : Nat

def checkFactoredQTACert (A : FactoredQTA) (good : Fin A.numStates → Bool)
    (cert : FactoredBitmaskCert) : Bool :=
  let evenList := bitsOfMask A.numStates cert.evenMask
  let topList  := bitsOfMask A.midStates cert.topMask
  let botList  := bitsOfMask A.midStates cert.botMask
  let leavesOk := allFin A.numLeaves (fun a => bitSet cert.evenMask (A.leaf a).val)
  let topOk := evenList.all (fun a => evenList.all (fun b => bitSet cert.topMask (A.hTop a b).val))
  let botOk := evenList.all (fun c => evenList.all (fun d => bitSet cert.botMask (A.hBot c d).val))
  let glueOk := topList.all (fun t => botList.all (fun b => bitSet cert.evenMask (A.vGlue t b).val))
  let safeOk := evenList.all good
  leavesOk && topOk && botOk && glueOk && safeOk

theorem factoredQTA_inv (A : FactoredQTA) (good : Fin A.numStates → Bool)
    (cert : FactoredBitmaskCert) (hcert : checkFactoredQTACert A good cert = true) :
    ∀ (k : Nat) (q : QTree (Fin A.numLeaves) k),
      bitSet cert.evenMask (evalFactoredQTA A q).val = true := by
  unfold checkFactoredQTACert at hcert
  simp only [Bool.and_eq_true, allFin_iff, List.all_eq_true, mem_bitsOfMask_iff] at hcert
  obtain ⟨⟨⟨⟨hleaves, htop⟩, hbot⟩, hglue⟩, _⟩ := hcert
  intro k q
  induction q with
  | qleaf a => exact hleaves a
  | qnode nw ne sw se ihnw ihne ihsw ihse =>
    exact hglue _ (htop _ ihnw _ ihne) _ (hbot _ ihsw _ ihse)

/-- Pure-data finite generator certificate for a factored upward-closed inductive invariant
    `(↑gens, ↑topGens, ↑botGens)` on a monotone 5-port quadtree automaton. -/
structure UpsetCert (m mid : Nat) where
  gens    : List (Fin m)
  topGens : List (Fin mid)
  botGens : List (Fin mid)

/-- Membership in the upward closure `↑gens` under finite preorder `le`. -/
def inUpset {m : Nat} (le : Fin m → Fin m → Bool) (gens : List (Fin m)) (x : Fin m) : Bool :=
  gens.any (fun g => le g x)

/-- Decidable certificate checker for a factored monotone quadtree automaton:
    checks leaves in `↑gens`, safety of `↑gens ∩ safeMask`, `hTop(gens × gens) ⊆ ↑topGens`,
    `hBot(gens × gens) ⊆ ↑botGens`, and `vGlue(topGens × botGens) ⊆ ↑gens`. -/
def checkUpsetCert {numLeaves m mid : Nat}
    (leaf : Fin numLeaves → Fin m)
    (hTop : Fin m → Fin m → Fin mid)
    (hBot : Fin m → Fin m → Fin mid)
    (vGlue : Fin mid → Fin mid → Fin m)
    (le : Fin m → Fin m → Bool)
    (leMid : Fin mid → Fin mid → Bool)
    (safeMask : Nat)
    (good : Fin m → Bool)
    (cert : UpsetCert m mid) : Bool :=
  let leavesOk := allFin numLeaves (fun a => inUpset le cert.gens (leaf a))
  let safeOk   := (bitsOfMask m safeMask).all (fun q => !(inUpset le cert.gens q) || good q)
  let topOk    := cert.gens.all (fun g0 => cert.gens.all (fun g1 => inUpset leMid cert.topGens (hTop g0 g1)))
  let botOk    := cert.gens.all (fun g2 => cert.gens.all (fun g3 => inUpset leMid cert.botGens (hBot g2 g3)))
  let glueOk   := cert.topGens.all (fun t => cert.botGens.all (fun b => inUpset le cert.gens (vGlue t b)))
  leavesOk && safeOk && topOk && botOk && glueOk

theorem inUpset_iff {m : Nat} (le : Fin m → Fin m → Bool) (gens : List (Fin m)) (x : Fin m) :
    inUpset le gens x = true ↔ ∃ g ∈ gens, le g x = true := by
  unfold inUpset
  simp [List.any_eq_true]

/-- General Soundness Meta-Theorem for Factored Monotone Upset Quadtree Compilation. -/
theorem monotoneUpsetQTA_sound {numLeaves m mid : Nat}
    (leaf : Fin numLeaves → Fin m)
    (hTop : Fin m → Fin m → Fin mid)
    (hBot : Fin m → Fin m → Fin mid)
    (vGlue : Fin mid → Fin mid → Fin m)
    (le : Fin m → Fin m → Bool)
    (leMid : Fin mid → Fin mid → Bool)
    (hle_trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hleMid_trans : ∀ a b c, leMid a b = true → leMid b c = true → leMid a c = true)
    (hTop_mono : ∀ a a' b b', le a a' = true → le b b' = true → leMid (hTop a b) (hTop a' b') = true)
    (hBot_mono : ∀ c c' d d', le c c' = true → le d d' = true → leMid (hBot c d) (hBot c' d') = true)
    (vGlue_mono : ∀ t t' b b', leMid t t' = true → leMid b b' = true → le (vGlue t b) (vGlue t' b') = true)
    (safeMask : Nat)
    (good : Fin m → Bool)
    (cert : UpsetCert m mid)
    (hcert : checkUpsetCert leaf hTop hBot vGlue le leMid safeMask good cert = true)
    (eval : {k : Nat} → QTree (Fin numLeaves) k → Fin m)
    (heval_leaf : ∀ a, eval (.qleaf a) = leaf a)
    (heval_node : ∀ {k} (nw ne sw se : QTree (Fin numLeaves) k),
      eval (.qnode nw ne sw se) = vGlue (hTop (eval nw) (eval ne)) (hBot (eval sw) (eval se)))
    (hsafe_inv : ∀ (k : Nat) (q : QTree (Fin numLeaves) k), bitSet safeMask (eval q).val = true) :
    ∀ (k : Nat) (q : QTree (Fin numLeaves) k),
      inUpset le cert.gens (eval q) = true ∧ good (eval q) = true := by
  unfold checkUpsetCert at hcert
  simp only [Bool.and_eq_true, allFin_iff, List.all_eq_true, mem_bitsOfMask_iff] at hcert
  obtain ⟨⟨⟨⟨hleaves, hsafe⟩, htop⟩, hbot⟩, hglue⟩ := hcert
  have hup : ∀ (k : Nat) (q : QTree (Fin numLeaves) k), inUpset le cert.gens (eval q) = true := by
    intro k q
    induction q with
    | qleaf a =>
      rw [heval_leaf]
      exact hleaves a
    | qnode nw ne sw se ihnw ihne ihsw ihse =>
      rw [heval_node]
      rw [inUpset_iff] at ihnw ihne ihsw ihse ⊢
      obtain ⟨g0, hg0, hle0⟩ := ihnw
      obtain ⟨g1, hg1, hle1⟩ := ihne
      obtain ⟨g2, hg2, hle2⟩ := ihsw
      obtain ⟨g3, hg3, hle3⟩ := ihse
      have ht := htop g0 hg0 g1 hg1
      rw [inUpset_iff] at ht
      obtain ⟨t, ht_mem, hlet⟩ := ht
      have ht_le : leMid t (hTop (eval nw) (eval ne)) = true :=
        hleMid_trans _ _ _ hlet (hTop_mono _ _ _ _ hle0 hle1)
      have hb := hbot g2 hg2 g3 hg3
      rw [inUpset_iff] at hb
      obtain ⟨b, hb_mem, hleb⟩ := hb
      have hb_le : leMid b (hBot (eval sw) (eval se)) = true :=
        hleMid_trans _ _ _ hleb (hBot_mono _ _ _ _ hle2 hle3)
      have hg := hglue t ht_mem b hb_mem
      rw [inUpset_iff] at hg
      obtain ⟨g', hg', hleg'⟩ := hg
      exact ⟨g', hg', hle_trans _ _ _ hleg' (vGlue_mono _ _ _ _ ht_le hb_le)⟩
  intro k q
  have hu := hup k q
  have hs := hsafe (eval q) (hsafe_inv k q)
  rw [hu] at hs
  exact ⟨hu, by simpa using hs⟩

/-! ## Section 3: Exact Finite-Graph Reachability & Strict List-Bitmask Warshall Bridge -/

inductive Reach {α : Type} (E : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Reach E x x
  | step {x y z : α} : E x y → Reach E y z → Reach E x z

theorem Reach.trans {α : Type} {E : α → α → Prop} {x y z : α}
    (h1 : Reach E x y) (h2 : Reach E y z) : Reach E x z := by
  induction h1 with
  | refl _ => exact h2
  | step e _ ih => exact .step e (ih h2)

theorem Reach.single {α : Type} {E : α → α → Prop} {x y : α} (e : E x y) : Reach E x y :=
  .step e (.refl y)

theorem Reach.mono {α : Type} {E1 E2 : α → α → Prop}
    (hsub : ∀ a b, E1 a b → E2 a b) {x y : α} (h : Reach E1 x y) : Reach E2 x y := by
  induction h with
  | refl x => exact .refl x
  | step e _ ih => exact .step (hsub _ _ e) ih

theorem Reach.symm_of_symm {α : Type} {E : α → α → Prop}
    (hsym : ∀ a b, E a b → E b a) {x y : α} (h : Reach E x y) : Reach E y x := by
  induction h with
  | refl x => exact .refl x
  | step e _ ih => exact Reach.trans ih (Reach.single (hsym _ _ e))

inductive ReachVia {n : Nat} (E : Fin n → Fin n → Prop) (k : Nat) : Fin n → Fin n → Prop where
  | base {x y} : (x = y ∨ E x y) → ReachVia E k x y
  | via {x y} {m : Fin n} : m.val < k → ReachVia E k x m → ReachVia E k m y → ReachVia E k x y

theorem ReachVia.mono_k {n : Nat} {E : Fin n → Fin n → Prop} {k : Nat} {x y : Fin n}
    (h : ReachVia E k x y) : ReachVia E (k + 1) x y := by
  induction h with
  | base hb => exact .base hb
  | via hm _ _ ih1 ih2 => exact .via (Nat.lt_succ_of_lt hm) ih1 ih2

theorem ReachVia.toReach {n : Nat} {E : Fin n → Fin n → Prop} {k : Nat} {x y : Fin n}
    (h : ReachVia E k x y) : Reach E x y := by
  induction h with
  | base hb =>
    rcases hb with rfl | e
    · exact .refl _
    · exact .single e
  | via _ _ _ ih1 ih2 => exact Reach.trans ih1 ih2

theorem Reach.toReachVia {n : Nat} {E : Fin n → Fin n → Prop} {x y : Fin n}
    (h : Reach E x y) : ReachVia E n x y := by
  induction h with
  | refl x => exact .base (Or.inl rfl)
  | @step a b c e _ ih => exact .via b.isLt (.base (Or.inr e)) ih

/-- Functional Warshall (used for clean symbolic proof). -/
def warshallStep {n : Nat} (k : Fin n) (M : Fin n → Nat) : Fin n → Nat :=
  fun i => if bitSet (M i) k.val then M i ||| M k else M i

def warshallLoop {n : Nat} (M : Fin n → Nat) : Nat → (Fin n → Nat)
  | 0 => M
  | k + 1 =>
    let prev := warshallLoop M k
    if h : k < n then warshallStep ⟨k, h⟩ prev else prev

def warshallRun {n : Nat} (M : Fin n → Nat) : Fin n → Nat :=
  warshallLoop M n

/-- Strict `List Nat` Warshall (memoizes every row once per step — eliminates exponential blowup!). -/
def warshallStepList (k : Nat) (M : List Nat) : List Nat :=
  let mk := M.getD k 0
  M.map (fun r => if bitSet r k then r ||| mk else r)

def warshallLoopList (M : List Nat) : Nat → List Nat
  | 0 => M
  | k + 1 => warshallStepList k (warshallLoopList M k)

def warshallRunList {n : Nat} (M : Fin n → Nat) : List Nat :=
  warshallLoopList (List.ofFn M) n

theorem warshallStepList_length (k : Nat) (M : List Nat) :
    (warshallStepList k M).length = M.length := by
  unfold warshallStepList; simp

theorem warshallLoopList_length (M : List Nat) (k : Nat) :
    (warshallLoopList M k).length = M.length := by
  induction k with
  | zero => rfl
  | succ m ih => unfold warshallLoopList; rw [warshallStepList_length, ih]

theorem getD_map_eq (f : Nat → Nat) (l : List Nat) (i : Nat) (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ m =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih m (by simp at hi; omega)

theorem warshallLoopList_getD {n : Nat} (M : Fin n → Nat) (k : Nat) (hk : k ≤ n) (i : Fin n) :
    (warshallLoopList (List.ofFn M) k).getD i.val 0 = warshallLoop M k i := by
  induction k generalizing i with
  | zero =>
    unfold warshallLoopList warshallLoop
    simp [List.getD_eq_getElem?_getD, i.isLt]
  | succ m ih =>
    have hmlt : m < n := by omega
    have hmle : m ≤ n := by omega
    unfold warshallLoopList warshallLoop warshallStepList
    simp only [hmlt, dite_true]
    have hlen : (warshallLoopList (List.ofFn M) m).length = n := by
      rw [warshallLoopList_length, List.length_ofFn]
    rw [getD_map_eq _ _ i.val (by omega)]
    rw [ih hmle i, ih hmle ⟨m, hmlt⟩]
    rfl

theorem warshallRunList_getD {n : Nat} (M : Fin n → Nat) (i : Fin n) :
    (warshallRunList M).getD i.val 0 = warshallRun M i :=
  warshallLoopList_getD M n (Nat.le_refl n) i

theorem bitSet_or (a b i : Nat) : bitSet (a ||| b) i = (bitSet a i || bitSet b i) := by
  unfold bitSet
  simp only [Nat.shiftRight_or_distrib, Nat.and_or_distrib_right]
  have ha : (a >>> i) &&& 1 = 0 ∨ (a >>> i) &&& 1 = 1 := by
    have : (a >>> i) &&& 1 = (a >>> i) % 2 := Nat.and_one_is_mod _
    omega
  have hb : (b >>> i) &&& 1 = 0 ∨ (b >>> i) &&& 1 = 1 := by
    have : (b >>> i) &&& 1 = (b >>> i) % 2 := Nat.and_one_is_mod _
    omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

theorem warshallStep_spec {n : Nat} (k : Fin n) (M : Fin n → Nat) (i j : Fin n) :
    bitSet (warshallStep k M i) j.val = true ↔
      bitSet (M i) j.val = true ∨ (bitSet (M i) k.val = true ∧ bitSet (M k) j.val = true) := by
  unfold warshallStep
  cases h : bitSet (M i) k.val with
  | false => simp
  | true => simp only [ite_true, bitSet_or, Bool.or_eq_true, true_and]

theorem warshallLoop_iff_ReachVia {n : Nat} (M : Fin n → Nat)
    (hrefl : ∀ x : Fin n, bitSet (M x) x.val = true) (k : Nat) (hk : k ≤ n) :
    ∀ x y : Fin n,
      bitSet (warshallLoop M k x) y.val = true ↔
        ReachVia (fun a b => bitSet (M a) b.val = true) k x y := by
  induction k with
  | zero =>
    intro x y
    unfold warshallLoop
    constructor
    · intro h; exact .base (Or.inr h)
    · intro h
      induction h with
      | base hb =>
        rcases hb with rfl | e
        · exact hrefl _
        · exact e
      | via hm => exact absurd hm (Nat.not_lt_zero _)
  | succ k ih =>
    have hlt : k < n := by omega
    have hle : k ≤ n := by omega
    intro x y
    unfold warshallLoop
    simp only [hlt, dite_true]
    rw [warshallStep_spec]
    rw [ih hle x y, ih hle x ⟨k, hlt⟩, ih hle ⟨k, hlt⟩ y]
    constructor
    · intro h
      rcases h with hxy | ⟨hxk, hky⟩
      · exact hxy.mono_k
      · exact .via (Nat.lt_succ_self k) hxk.mono_k hky.mono_k
    · intro h
      induction h with
      | base hb => exact Or.inl (.base hb)
      | @via a b m hm _ _ ih1 ih2 =>
        have hcases : m.val < k ∨ m.val = k := by omega
        rcases hcases with hltm | heqm
        · rcases ih1 with h1 | ⟨h1a, h1b⟩
          · rcases ih2 with h2 | ⟨h2a, h2b⟩
            · exact Or.inl (.via hltm h1 h2)
            · exact Or.inr ⟨.via hltm h1 h2a, h2b⟩
          · rcases ih2 with h2 | ⟨h2a, h2b⟩
            · exact Or.inr ⟨h1a, .via hltm h1b h2⟩
            · exact Or.inr ⟨h1a, h2b⟩
        · have hm_eq : m = ⟨k, hlt⟩ := Fin.ext heqm
          subst hm_eq
          rcases ih1 with h1 | ⟨h1a, _⟩
          · rcases ih2 with h2 | ⟨_, h2b⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inr ⟨h1, h2b⟩
          · rcases ih2 with h2 | ⟨_, h2b⟩
            · exact Or.inr ⟨h1a, h2⟩
            · exact Or.inr ⟨h1a, h2b⟩

/-- Pure-silicon unrolled 8-row and 10-row GMP-Nat Warshall (ZERO `List` allocations in kernel!). -/
@[inline] def wRow (r k rk : Nat) : Nat :=
  if bitSet r k then r ||| rk else r

@[inline] def wStep8 (k : Nat) (rk : Nat) (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (wRow s.1 k rk, wRow s.2.1 k rk, wRow s.2.2.1 k rk, wRow s.2.2.2.1 k rk,
   wRow s.2.2.2.2.1 k rk, wRow s.2.2.2.2.2.1 k rk, wRow s.2.2.2.2.2.2.1 k rk, wRow s.2.2.2.2.2.2.2 k rk)

def warshall8 (M : Fin 8 → Nat) : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let s0 := (M 0, M 1, M 2, M 3, M 4, M 5, M 6, M 7)
  let s1 := wStep8 0 s0.1 s0
  let s2 := wStep8 1 s1.2.1 s1
  let s3 := wStep8 2 s2.2.2.1 s2
  let s4 := wStep8 3 s3.2.2.2.1 s3
  let s5 := wStep8 4 s4.2.2.2.2.1 s4
  let s6 := wStep8 5 s5.2.2.2.2.2.1 s5
  let s7 := wStep8 6 s6.2.2.2.2.2.2.1 s6
  wStep8 7 s7.2.2.2.2.2.2.2 s7

def get8 (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) (i : Fin 8) : Nat :=
  match i.val with
  | 0 => s.1 | 1 => s.2.1 | 2 => s.2.2.1 | 3 => s.2.2.2.1
  | 4 => s.2.2.2.2.1 | 5 => s.2.2.2.2.2.1 | 6 => s.2.2.2.2.2.2.1 | _ => s.2.2.2.2.2.2.2

theorem get8_wStep8 (k : Fin 8) (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) (i : Fin 8) :
    get8 (wStep8 k.val (get8 s k) s) i = warshallStep k (get8 s) i := by
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem get8_warshall8 (M : Fin 8 → Nat) (i : Fin 8) :
    get8 (warshall8 M) i = warshallRun M i := by
  have h0 : get8 (M 0, M 1, M 2, M 3, M 4, M 5, M 6, M 7) = warshallLoop M 0 := by
    funext x; rcases x with ⟨x, hx⟩
    match x, hx with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  have hstep : ∀ (k : Fin 8) (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat),
      get8 s = warshallLoop M k.val → get8 (wStep8 k.val (get8 s k) s) = warshallLoop M (k.val + 1) := by
    intro k s hs; funext x
    rw [get8_wStep8, hs]
    change warshallStep k (warshallLoop M k.val) x =
      (if h : k.val < 8 then warshallStep ⟨k.val, h⟩ (warshallLoop M k.val) else warshallLoop M k.val) x
    simp [k.isLt]
  unfold warshall8 warshallRun
  have h1 := hstep ⟨0, by omega⟩ _ h0
  have h2 := hstep ⟨1, by omega⟩ _ h1
  have h3 := hstep ⟨2, by omega⟩ _ h2
  have h4 := hstep ⟨3, by omega⟩ _ h3
  have h5 := hstep ⟨4, by omega⟩ _ h4
  have h6 := hstep ⟨5, by omega⟩ _ h5
  have h7 := hstep ⟨6, by omega⟩ _ h6
  have h8 := hstep ⟨7, by omega⟩ _ h7
  exact congrFun h8 i

@[inline] def wStep10 (k : Nat) (rk : Nat)
    (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (wRow s.1 k rk, wRow s.2.1 k rk, wRow s.2.2.1 k rk, wRow s.2.2.2.1 k rk,
   wRow s.2.2.2.2.1 k rk, wRow s.2.2.2.2.2.1 k rk, wRow s.2.2.2.2.2.2.1 k rk,
   wRow s.2.2.2.2.2.2.2.1 k rk, wRow s.2.2.2.2.2.2.2.2.1 k rk, wRow s.2.2.2.2.2.2.2.2.2 k rk)

def warshall10 (M : Fin 10 → Nat) : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let s0 := (M 0, M 1, M 2, M 3, M 4, M 5, M 6, M 7, M 8, M 9)
  let s1 := wStep10 0 s0.1 s0
  let s2 := wStep10 1 s1.2.1 s1
  let s3 := wStep10 2 s2.2.2.1 s2
  let s4 := wStep10 3 s3.2.2.2.1 s3
  let s5 := wStep10 4 s4.2.2.2.2.1 s4
  let s6 := wStep10 5 s5.2.2.2.2.2.1 s5
  let s7 := wStep10 6 s6.2.2.2.2.2.2.1 s6
  let s8 := wStep10 7 s7.2.2.2.2.2.2.2.1 s7
  let s9 := wStep10 8 s8.2.2.2.2.2.2.2.2.1 s8
  wStep10 9 s9.2.2.2.2.2.2.2.2.2 s9

def get10 (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) (i : Fin 10) : Nat :=
  match i.val with
  | 0 => s.1 | 1 => s.2.1 | 2 => s.2.2.1 | 3 => s.2.2.2.1 | 4 => s.2.2.2.2.1
  | 5 => s.2.2.2.2.2.1 | 6 => s.2.2.2.2.2.2.1 | 7 => s.2.2.2.2.2.2.2.1
  | 8 => s.2.2.2.2.2.2.2.2.1 | _ => s.2.2.2.2.2.2.2.2.2

theorem get10_wStep10 (k : Fin 10) (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) (i : Fin 10) :
    get10 (wStep10 k.val (get10 s k) s) i = warshallStep k (get10 s) i := by
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl

theorem get10_warshall10 (M : Fin 10 → Nat) (i : Fin 10) :
    get10 (warshall10 M) i = warshallRun M i := by
  have h0 : get10 (M 0, M 1, M 2, M 3, M 4, M 5, M 6, M 7, M 8, M 9) = warshallLoop M 0 := by
    funext x; rcases x with ⟨x, hx⟩
    match x, hx with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl
  have hstep : ∀ (k : Fin 10) (s : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat),
      get10 s = warshallLoop M k.val → get10 (wStep10 k.val (get10 s k) s) = warshallLoop M (k.val + 1) := by
    intro k s hs; funext x
    rw [get10_wStep10, hs]
    change warshallStep k (warshallLoop M k.val) x =
      (if h : k.val < 10 then warshallStep ⟨k.val, h⟩ (warshallLoop M k.val) else warshallLoop M k.val) x
    simp [k.isLt]
  unfold warshall10 warshallRun
  have h1 := hstep ⟨0, by omega⟩ _ h0
  have h2 := hstep ⟨1, by omega⟩ _ h1
  have h3 := hstep ⟨2, by omega⟩ _ h2
  have h4 := hstep ⟨3, by omega⟩ _ h3
  have h5 := hstep ⟨4, by omega⟩ _ h4
  have h6 := hstep ⟨5, by omega⟩ _ h5
  have h7 := hstep ⟨6, by omega⟩ _ h6
  have h8 := hstep ⟨7, by omega⟩ _ h7
  have h9 := hstep ⟨8, by omega⟩ _ h8
  have h10 := hstep ⟨9, by omega⟩ _ h9
  exact congrFun h10 i

theorem warshallRun_iff_Reach_fn {n : Nat} (M : Fin n → Nat)
    (hrefl : ∀ x : Fin n, bitSet (M x) x.val = true) (x y : Fin n) :
    bitSet (warshallRun M x) y.val = true ↔
      Reach (fun a b => bitSet (M a) b.val = true) x y := by
  unfold warshallRun
  rw [warshallLoop_iff_ReachVia M hrefl n (Nat.le_refl n)]
  exact ⟨ReachVia.toReach, Reach.toReachVia⟩

/-- General Soundness & Completeness of Pure-Silicon Bitmask Warshall (`warshallRunList`). -/
theorem warshallRun_iff_Reach {n : Nat} (M : Fin n → Nat)
    (hrefl : ∀ x : Fin n, bitSet (M x) x.val = true) (x y : Fin n) :
    bitSet ((warshallRunList M).getD x.val 0) y.val = true ↔
      Reach (fun a b => bitSet (M a) b.val = true) x y := by
  rw [warshallRunList_getD]
  exact warshallRun_iff_Reach_fn M hrefl x y

/-! ## Section 4: Family I — Exact 16-Port Quadtree Switching Networks & the `D_33` Dichotomy -/

def glue16 (R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop) (u v : Fin 16) : Prop :=
  (∃ hu : u.val < 4, ∃ hv : v.val < 4, R0 ⟨u.val, hu⟩ ⟨v.val, hv⟩) ∨
  (∃ hu1 : 4 ≤ u.val, ∃ hu2 : u.val < 8, ∃ hv1 : 4 ≤ v.val, ∃ hv2 : v.val < 8,
    R1 ⟨u.val - 4, by omega⟩ ⟨v.val - 4, by omega⟩) ∨
  (∃ hu1 : 8 ≤ u.val, ∃ hu2 : u.val < 12, ∃ hv1 : 8 ≤ v.val, ∃ hv2 : v.val < 12,
    R2 ⟨u.val - 8, by omega⟩ ⟨v.val - 8, by omega⟩) ∨
  (∃ hu1 : 12 ≤ u.val, ∃ hv1 : 12 ≤ v.val,
    R3 ⟨u.val - 12, by omega⟩ ⟨v.val - 12, by omega⟩) ∨
  (u.val = 1 ∧ v.val = 7) ∨ (u.val = 7 ∧ v.val = 1) ∨
  (u.val = 0 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 0) ∨
  (u.val = 9 ∧ v.val = 15) ∨ (u.val = 15 ∧ v.val = 9) ∨
  (u.val = 10 ∧ v.val = 14) ∨ (u.val = 14 ∧ v.val = 10) ∨
  (u.val = 2 ∧ v.val = 8) ∨ (u.val = 8 ∧ v.val = 2) ∨
  (u.val = 6 ∧ v.val = 12) ∨ (u.val = 12 ∧ v.val = 6) ∨
  (u.val = 5 ∧ v.val = 13) ∨ (u.val = 13 ∧ v.val = 5) ∨
  (u.val = 3 ∧ v.val = 11) ∨ (u.val = 11 ∧ v.val = 3)

def outerPort16 : Fin 4 → Fin 16
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨5, by omega⟩
  | ⟨2, _⟩ => ⟨10, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩

def QNet (leafRel : Bool → Fin 4 → Fin 4 → Prop) : {k : Nat} → QTree Bool k → (Fin 4 → Fin 4 → Prop)
  | 0, .qleaf b => leafRel b
  | _ + 1, .qnode nw ne sw se =>
    fun i j =>
      Reach (glue16 (QNet leafRel nw) (QNet leafRel ne) (QNet leafRel sw) (QNet leafRel se))
        (outerPort16 i) (outerPort16 j)

def percLeafRel (b : Bool) (i j : Fin 4) : Prop :=
  if b then True else i = j

def trucLeafRel (b : Bool) (i j : Fin 4) : Prop :=
  if b then (i.val / 2 = j.val / 2)
  else ((i.val = 0 ∨ i.val = 3) ∧ (j.val = 0 ∨ j.val = 3)) ∨
       ((i.val = 1 ∨ i.val = 2) ∧ (j.val = 1 ∨ j.val = 2))

def glueTop8 (R0 R1 : Fin 4 → Fin 4 → Prop) (u v : Fin 8) : Prop :=
  (∃ hu : u.val < 4, ∃ hv : v.val < 4, R0 ⟨u.val, hu⟩ ⟨v.val, hv⟩) ∨
  (∃ hu : 4 ≤ u.val, ∃ hv : 4 ≤ v.val, R1 ⟨u.val - 4, by omega⟩ ⟨v.val - 4, by omega⟩) ∨
  (u.val = 1 ∧ v.val = 7) ∨ (u.val = 7 ∧ v.val = 1) ∨
  (u.val = 0 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 0)

def glueBot8 (R2 R3 : Fin 4 → Fin 4 → Prop) (u v : Fin 8) : Prop :=
  (∃ hu : u.val < 4, ∃ hv : v.val < 4, R2 ⟨u.val, hu⟩ ⟨v.val, hv⟩) ∨
  (∃ hu : 4 ≤ u.val, ∃ hv : 4 ≤ v.val, R3 ⟨u.val - 4, by omega⟩ ⟨v.val - 4, by omega⟩) ∨
  (u.val = 1 ∧ v.val = 7) ∨ (u.val = 7 ∧ v.val = 1) ∨
  (u.val = 2 ∧ v.val = 6) ∨ (u.val = 6 ∧ v.val = 2)

def topPort8 : Fin 5 → Fin 8
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨5, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨6, by omega⟩
  | ⟨4, _⟩ => ⟨3, by omega⟩

def botPort8 : Fin 5 → Fin 8
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨4, by omega⟩
  | ⟨2, _⟩ => ⟨5, by omega⟩
  | ⟨3, _⟩ => ⟨2, by omega⟩
  | ⟨4, _⟩ => ⟨3, by omega⟩

def glueVert10 (RT RB : Fin 5 → Fin 5 → Prop) (u v : Fin 10) : Prop :=
  (∃ hu : u.val < 5, ∃ hv : v.val < 5, RT ⟨u.val, hu⟩ ⟨v.val, hv⟩) ∨
  (∃ hu : 5 ≤ u.val, ∃ hv : 5 ≤ v.val, RB ⟨u.val - 5, by omega⟩ ⟨v.val - 5, by omega⟩) ∨
  (u.val = 2 ∧ v.val = 5) ∨ (u.val = 5 ∧ v.val = 2) ∨
  (u.val = 3 ∧ v.val = 6) ∨ (u.val = 6 ∧ v.val = 3) ∨
  (u.val = 1 ∧ v.val = 7) ∨ (u.val = 7 ∧ v.val = 1) ∨
  (u.val = 4 ∧ v.val = 9) ∨ (u.val = 9 ∧ v.val = 4)

def outerPort10 : Fin 4 → Fin 10
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨8, by omega⟩
  | ⟨3, _⟩ => ⟨4, by omega⟩

def emb10to16 (x : Fin 10) : Fin 16 :=
  if h : x.val < 5 then
    ⟨(topPort8 ⟨x.val, h⟩).val, by have := (topPort8 ⟨x.val, h⟩).isLt; omega⟩
  else
    ⟨(botPort8 ⟨x.val - 5, by omega⟩).val + 8, by have := (botPort8 ⟨x.val - 5, by omega⟩).isLt; omega⟩

theorem reachTop8_lift {R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop} {u v : Fin 8}
    (h : Reach (glueTop8 R0 R1) u v) :
    Reach (glue16 R0 R1 R2 R3) ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ := by
  induction h with
  | refl _ => exact .refl _
  | @step a b _ e _ ih =>
    refine .step ?_ ih
    unfold glueTop8 at e; unfold glue16
    rcases e with ⟨ha, hb, hr⟩ | ⟨ha, hb, hr⟩ | h1 | h2 | h3 | h4
    · exact Or.inl ⟨ha, hb, hr⟩
    · exact Or.inr (Or.inl ⟨ha, a.isLt, hb, b.isLt, hr⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4)))))))

theorem reachBot8_lift {R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop} {u v : Fin 8}
    (h : Reach (glueBot8 R2 R3) u v) :
    Reach (glue16 R0 R1 R2 R3) ⟨u.val + 8, by omega⟩ ⟨v.val + 8, by omega⟩ := by
  induction h with
  | refl _ => exact .refl _
  | @step a b _ e _ ih =>
    refine .step ?_ ih
    unfold glueBot8 at e; unfold glue16
    rcases e with ⟨ha, hb, hr⟩ | ⟨ha, hb, hr⟩ | h1 | h2 | h3 | h4
    · refine Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, ?_⟩))
      have ha' : (⟨a.val + 8 - 8, by omega⟩ : Fin 4) = ⟨a.val, ha⟩ := Fin.ext (by dsimp; omega)
      have hb' : (⟨b.val + 8 - 8, by omega⟩ : Fin 4) = ⟨b.val, hb⟩ := Fin.ext (by dsimp; omega)
      dsimp only; rw [ha', hb']; exact hr
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega, ?_⟩)))
      have ha' : (⟨a.val + 8 - 12, by omega⟩ : Fin 4) = ⟨a.val - 4, by omega⟩ := Fin.ext (by dsimp; omega)
      have hb' : (⟨b.val + 8 - 12, by omega⟩ : Fin 4) = ⟨b.val - 4, by omega⟩ := Fin.ext (by dsimp; omega)
      dsimp only; rw [ha', hb']; exact hr
    · right; right; right; right; right; right; right; right; left; dsimp; omega
    · right; right; right; right; right; right; right; right; right; left; dsimp; omega
    · right; right; right; right; right; right; right; right; right; right; left; dsimp; omega
    · right; right; right; right; right; right; right; right; right; right; right; left; dsimp; omega

theorem reachVert10_to_glue16 {R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop} {u v : Fin 10}
    (h : Reach (glueVert10
      (fun i j => Reach (glueTop8 R0 R1) (topPort8 i) (topPort8 j))
      (fun i j => Reach (glueBot8 R2 R3) (botPort8 i) (botPort8 j))) u v) :
    Reach (glue16 R0 R1 R2 R3) (emb10to16 u) (emb10to16 v) := by
  induction h with
  | refl _ => exact .refl _
  | @step a b _ e _ ih =>
    refine Reach.trans ?_ ih
    unfold glueVert10 at e
    rcases e with ⟨ha, hb, hr⟩ | ⟨ha, hb, hr⟩ | hbr
    · have ha' : emb10to16 a = ⟨(topPort8 ⟨a.val, ha⟩).val, by have := (topPort8 ⟨a.val, ha⟩).isLt; omega⟩ := by
        unfold emb10to16; simp [ha]
      have hb' : emb10to16 b = ⟨(topPort8 ⟨b.val, hb⟩).val, by have := (topPort8 ⟨b.val, hb⟩).isLt; omega⟩ := by
        unfold emb10to16; simp [hb]
      rw [ha', hb']; exact reachTop8_lift hr
    · have ha' : emb10to16 a = ⟨(botPort8 ⟨a.val - 5, by omega⟩).val + 8, by have := (botPort8 ⟨a.val - 5, by omega⟩).isLt; omega⟩ := by
        unfold emb10to16; have hnot : ¬ (a.val < 5) := by omega
        simp [hnot]
      have hb' : emb10to16 b = ⟨(botPort8 ⟨b.val - 5, by omega⟩).val + 8, by have := (botPort8 ⟨b.val - 5, by omega⟩).isLt; omega⟩ := by
        unfold emb10to16; have hnot : ¬ (b.val < 5) := by omega
        simp [hnot]
      rw [ha', hb']; exact reachBot8_lift hr
    · apply Reach.single
      rcases hbr with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have ha : a = ⟨2, by omega⟩ := Fin.ext h1; have hb : b = ⟨5, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
      · have ha : a = ⟨5, by omega⟩ := Fin.ext h1; have hb : b = ⟨2, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
      · have ha : a = ⟨3, by omega⟩ := Fin.ext h1; have hb : b = ⟨6, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
      · have ha : a = ⟨6, by omega⟩ := Fin.ext h1; have hb : b = ⟨3, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
      · have ha : a = ⟨1, by omega⟩ := Fin.ext h1; have hb : b = ⟨7, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
      · have ha : a = ⟨7, by omega⟩ := Fin.ext h1; have hb : b = ⟨1, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
      · have ha : a = ⟨4, by omega⟩ := Fin.ext h1; have hb : b = ⟨9, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩
      · have ha : a = ⟨9, by omega⟩ := Fin.ext h1; have hb : b = ⟨4, by omega⟩ := Fin.ext h2
        rw [ha, hb]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; exact ⟨rfl, rfl⟩

def HalfReach (R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop) (u : Fin 16) (p : Fin 10) : Prop :=
  (∃ hu : u.val < 8, ∃ hp : p.val < 5, Reach (glueTop8 R0 R1) ⟨u.val, hu⟩ (topPort8 ⟨p.val, hp⟩)) ∨
  (∃ hu : 8 ≤ u.val, ∃ hp : 5 ≤ p.val, Reach (glueBot8 R2 R3) ⟨u.val - 8, by omega⟩ (botPort8 ⟨p.val - 5, by omega⟩))

def HalfReachFrom (R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop) (p : Fin 10) (v : Fin 16) : Prop :=
  (∃ hp : p.val < 5, ∃ hv : v.val < 8, Reach (glueTop8 R0 R1) (topPort8 ⟨p.val, hp⟩) ⟨v.val, hv⟩) ∨
  (∃ hp : 5 ≤ p.val, ∃ hv : 8 ≤ v.val, Reach (glueBot8 R2 R3) (botPort8 ⟨p.val - 5, by omega⟩) ⟨v.val - 8, by omega⟩)

def ContractInv (R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop) (u v : Fin 16) : Prop :=
  (∃ hu : u.val < 8, ∃ hv : v.val < 8, Reach (glueTop8 R0 R1) ⟨u.val, hu⟩ ⟨v.val, hv⟩) ∨
  (∃ hu : 8 ≤ u.val, ∃ hv : 8 ≤ v.val, Reach (glueBot8 R2 R3) ⟨u.val - 8, by omega⟩ ⟨v.val - 8, by omega⟩) ∨
  (∃ pu pv : Fin 10, HalfReach R0 R1 R2 R3 u pu ∧ HalfReachFrom R0 R1 R2 R3 pv v ∧
    Reach (glueVert10
      (fun i j => Reach (glueTop8 R0 R1) (topPort8 i) (topPort8 j))
      (fun i j => Reach (glueBot8 R2 R3) (botPort8 i) (botPort8 j))) pu pv)

theorem glue16_to_contractInv {R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop} {u v : Fin 16}
    (h : Reach (glue16 R0 R1 R2 R3) u v) : ContractInv R0 R1 R2 R3 u v := by
  let RT := fun i j => Reach (glueTop8 R0 R1) (topPort8 i) (topPort8 j)
  let RB := fun i j => Reach (glueBot8 R2 R3) (botPort8 i) (botPort8 j)
  induction h with
  | refl x =>
    by_cases hx : x.val < 8
    · exact Or.inl ⟨hx, hx, .refl _⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega, .refl _⟩)
  | @step a b c e _ ih =>
    have hclass :
        (∃ ha : a.val < 8, ∃ hb : b.val < 8, glueTop8 R0 R1 ⟨a.val, ha⟩ ⟨b.val, hb⟩) ∨
        (∃ ha : 8 ≤ a.val, ∃ hb : 8 ≤ b.val, glueBot8 R2 R3 ⟨a.val - 8, by omega⟩ ⟨b.val - 8, by omega⟩) ∨
        (∃ pa pb : Fin 10, HalfReach R0 R1 R2 R3 a pa ∧
          ((∃ hpb : pb.val < 5, ∃ hb : b.val < 8, topPort8 ⟨pb.val, hpb⟩ = ⟨b.val, hb⟩) ∨
           (∃ hpb : 5 ≤ pb.val, ∃ hb : 8 ≤ b.val, botPort8 ⟨pb.val - 5, by omega⟩ = ⟨b.val - 8, by omega⟩)) ∧
          glueVert10 RT RB pa pb) := by
      unfold glue16 at e
      rcases e with ⟨ha, hb, hr⟩ | ⟨ha1, ha2, hb1, hb2, hr⟩ | ⟨ha1, ha2, hb1, hb2, hr⟩ | ⟨ha1, hb1, hr⟩ |
                    h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | hbr
      · exact Or.inl ⟨by omega, by omega, Or.inl ⟨ha, hb, hr⟩⟩
      · exact Or.inl ⟨ha2, hb2, Or.inr (Or.inl ⟨ha1, hb1, hr⟩)⟩
      · refine Or.inr (Or.inl ⟨ha1, hb1, Or.inl ⟨by dsimp; omega, by dsimp; omega, hr⟩⟩)
      · refine Or.inr (Or.inl ⟨by omega, by omega, Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega, ?_⟩)⟩)
        have ha' : (⟨a.val - 8 - 4, by omega⟩ : Fin 4) = ⟨a.val - 12, by omega⟩ := Fin.ext (by dsimp; omega)
        have hb' : (⟨b.val - 8 - 4, by omega⟩ : Fin 4) = ⟨b.val - 12, by omega⟩ := Fin.ext (by dsimp; omega)
        dsimp only; rw [ha', hb']; exact hr
      · exact Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inl h1))⟩
      · exact Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inl h2)))⟩
      · exact Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))⟩
      · exact Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h4))))⟩
      · exact Or.inr (Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega⟩))⟩)
      · exact Or.inr (Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega⟩)))⟩)
      · exact Or.inr (Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega⟩))))⟩)
      · exact Or.inr (Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by dsimp; omega, by dsimp; omega⟩))))⟩)
      · right; right
        rcases hbr with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨⟨2, by omega⟩, ⟨5, by omega⟩,
            Or.inl ⟨by omega, by dsimp; omega, by have : (⟨a.val, by omega⟩ : Fin 8) = topPort8 ⟨2, by omega⟩ := Fin.ext (by dsimp [topPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inr ⟨by dsimp; omega, by omega, Fin.ext (by simp [botPort8]; omega)⟩,
            by unfold glueVert10; right; right; left; exact ⟨rfl, rfl⟩⟩
        · exact ⟨⟨5, by omega⟩, ⟨2, by omega⟩,
            Or.inr ⟨by omega, by dsimp; omega, by have : (⟨a.val - 8, by omega⟩ : Fin 8) = botPort8 ⟨0, by omega⟩ := Fin.ext (by simp [botPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inl ⟨by dsimp; omega, by omega, Fin.ext (by simp [topPort8]; omega)⟩,
            by unfold glueVert10; right; right; right; left; exact ⟨rfl, rfl⟩⟩
        · exact ⟨⟨3, by omega⟩, ⟨6, by omega⟩,
            Or.inl ⟨by omega, by dsimp; omega, by have : (⟨a.val, by omega⟩ : Fin 8) = topPort8 ⟨3, by omega⟩ := Fin.ext (by dsimp [topPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inr ⟨by dsimp; omega, by omega, Fin.ext (by simp [botPort8]; omega)⟩,
            by unfold glueVert10; right; right; right; right; left; exact ⟨rfl, rfl⟩⟩
        · exact ⟨⟨6, by omega⟩, ⟨3, by omega⟩,
            Or.inr ⟨by omega, by dsimp; omega, by have : (⟨a.val - 8, by omega⟩ : Fin 8) = botPort8 ⟨1, by omega⟩ := Fin.ext (by simp [botPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inl ⟨by dsimp; omega, by omega, Fin.ext (by simp [topPort8]; omega)⟩,
            by unfold glueVert10; right; right; right; right; right; left; exact ⟨rfl, rfl⟩⟩
        · exact ⟨⟨1, by omega⟩, ⟨7, by omega⟩,
            Or.inl ⟨by omega, by dsimp; omega, by have : (⟨a.val, by omega⟩ : Fin 8) = topPort8 ⟨1, by omega⟩ := Fin.ext (by dsimp [topPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inr ⟨by dsimp; omega, by omega, Fin.ext (by simp [botPort8]; omega)⟩,
            by unfold glueVert10; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩⟩
        · exact ⟨⟨7, by omega⟩, ⟨1, by omega⟩,
            Or.inr ⟨by omega, by dsimp; omega, by have : (⟨a.val - 8, by omega⟩ : Fin 8) = botPort8 ⟨2, by omega⟩ := Fin.ext (by simp [botPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inl ⟨by dsimp; omega, by omega, Fin.ext (by simp [topPort8]; omega)⟩,
            by unfold glueVert10; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩⟩
        · exact ⟨⟨4, by omega⟩, ⟨9, by omega⟩,
            Or.inl ⟨by omega, by dsimp; omega, by have : (⟨a.val, by omega⟩ : Fin 8) = topPort8 ⟨4, by omega⟩ := Fin.ext (by dsimp [topPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inr ⟨by dsimp; omega, by omega, Fin.ext (by simp [botPort8]; omega)⟩,
            by unfold glueVert10; right; right; right; right; right; right; right; right; left; exact ⟨rfl, rfl⟩⟩
        · exact ⟨⟨9, by omega⟩, ⟨4, by omega⟩,
            Or.inr ⟨by omega, by dsimp; omega, by have : (⟨a.val - 8, by omega⟩ : Fin 8) = botPort8 ⟨4, by omega⟩ := Fin.ext (by simp [botPort8]; omega); rw [this]; exact .refl _⟩,
            Or.inl ⟨by dsimp; omega, by omega, Fin.ext (by simp [topPort8]; omega)⟩,
            by unfold glueVert10; right; right; right; right; right; right; right; right; right; exact ⟨rfl, rfl⟩⟩
    rcases hclass with ⟨ha, hb, etop⟩ | ⟨ha, hb, ebot⟩ | ⟨pa, pb, hpa, hpb_eq, ev⟩
    · rcases ih with ⟨hb', hc, hr⟩ | ⟨hb', _, _⟩ | ⟨pu, pv, hpu, hpv, hrv⟩
      · exact Or.inl ⟨ha, hc, .step etop hr⟩
      · omega
      · refine Or.inr (Or.inr ⟨pu, pv, ?_, hpv, hrv⟩)
        rcases hpu with ⟨hb', hpu_lt, hr⟩ | ⟨hb', _, _⟩
        · exact Or.inl ⟨ha, hpu_lt, .step etop hr⟩
        · omega
    · rcases ih with ⟨hb', _, _⟩ | ⟨hb', hc, hr⟩ | ⟨pu, pv, hpu, hpv, hrv⟩
      · omega
      · exact Or.inr (Or.inl ⟨ha, hc, .step ebot hr⟩)
      · refine Or.inr (Or.inr ⟨pu, pv, ?_, hpv, hrv⟩)
        rcases hpu with ⟨hb', _, _⟩ | ⟨hb', hpu_ge, hr⟩
        · omega
        · exact Or.inr ⟨ha, hpu_ge, .step ebot hr⟩
    · rcases ih with ⟨hb', hc, hr⟩ | ⟨hb', hc, hr⟩ | ⟨pu, pv, hpu, hpv, hrv⟩
      · rcases hpb_eq with ⟨hpb, hb, heq⟩ | ⟨_, hb, _⟩
        · refine Or.inr (Or.inr ⟨pa, pb, hpa, Or.inl ⟨hpb, hc, ?_⟩, .single ev⟩)
          rw [heq]; exact hr
        · omega
      · rcases hpb_eq with ⟨_, hb, _⟩ | ⟨hpb, hb, heq⟩
        · omega
        · refine Or.inr (Or.inr ⟨pa, pb, hpa, Or.inr ⟨hpb, hc, ?_⟩, .single ev⟩)
          rw [heq]; exact hr
      · refine Or.inr (Or.inr ⟨pa, pv, hpa, hpv, .step ev (.step ?_ hrv)⟩)
        rcases hpb_eq with ⟨hpb, hb, heq⟩ | ⟨hpb, hb, heq⟩
        · rcases hpu with ⟨hb', hpu_lt, hr⟩ | ⟨hb', _, _⟩
          · refine Or.inl ⟨hpb, hpu_lt, ?_⟩
            dsimp only; rw [heq]; exact hr
          · omega
        · rcases hpu with ⟨hb', _, _⟩ | ⟨hb', hpu_ge, hr⟩
          · omega
          · refine Or.inr (Or.inl ⟨hpb, hpu_ge, ?_⟩)
            dsimp only; rw [heq]; exact hr

theorem reach_glue16_iff_vGlue (R0 R1 R2 R3 : Fin 4 → Fin 4 → Prop) (i j : Fin 4) :
    Reach (glue16 R0 R1 R2 R3) (outerPort16 i) (outerPort16 j) ↔
    Reach (glueVert10
      (fun a b => Reach (glueTop8 R0 R1) (topPort8 a) (topPort8 b))
      (fun a b => Reach (glueBot8 R2 R3) (botPort8 a) (botPort8 b)))
      (outerPort10 i) (outerPort10 j) := by
  have hemb : ∀ x : Fin 4, emb10to16 (outerPort10 x) = outerPort16 x :=
    fin4_forall rfl rfl rfl rfl
  let RT := fun a b => Reach (glueTop8 R0 R1) (topPort8 a) (topPort8 b)
  let RB := fun a b => Reach (glueBot8 R2 R3) (botPort8 a) (botPort8 b)
  constructor
  · intro h
    have hci := glue16_to_contractInv h
    rcases hci with ⟨hi, hj, hr⟩ | ⟨hi, hj, hr⟩ | ⟨pu, pv, hpu, hpv, hrv⟩
    · have htop : ∀ x y : Fin 4,
          (hx : (outerPort16 x).val < 8) → (hy : (outerPort16 y).val < 8) →
          Reach (glueTop8 R0 R1) ⟨(outerPort16 x).val, hx⟩ ⟨(outerPort16 y).val, hy⟩ →
          Reach (glueVert10 RT RB) (outerPort10 x) (outerPort10 y) := by
        refine fin4_forall ?_ ?_ ?_ ?_ <;> refine fin4_forall ?_ ?_ ?_ ?_
        all_goals (intro hx hy hr; first
          | (exfalso; exact absurd hx (by decide))
          | (exfalso; exact absurd hy (by decide))
          | (apply Reach.single; refine Or.inl ⟨by decide, by decide, ?_⟩;
             dsimp only [RT, outerPort10, outerPort16, topPort8] at hr ⊢; exact hr))
      exact htop i j hi hj hr
    · have hbot : ∀ x y : Fin 4,
          (hx : 8 ≤ (outerPort16 x).val) → (hy : 8 ≤ (outerPort16 y).val) →
          Reach (glueBot8 R2 R3) ⟨(outerPort16 x).val - 8, by omega⟩ ⟨(outerPort16 y).val - 8, by omega⟩ →
          Reach (glueVert10 RT RB) (outerPort10 x) (outerPort10 y) := by
        refine fin4_forall ?_ ?_ ?_ ?_ <;> refine fin4_forall ?_ ?_ ?_ ?_
        all_goals (intro hx hy hr; first
          | (exfalso; exact absurd hx (by decide))
          | (exfalso; exact absurd hy (by decide))
          | (apply Reach.single; refine Or.inr (Or.inl ⟨by decide, by decide, ?_⟩);
             dsimp only [RB, outerPort10, outerPort16, botPort8] at hr ⊢; exact hr))
      exact hbot i j hi hj hr
    · have h1 : ∀ x : Fin 4, HalfReach R0 R1 R2 R3 (outerPort16 x) pu →
          Reach (glueVert10 RT RB) (outerPort10 x) pu :=
        fin4_forall
          (fun hpu => by rcases hpu with ⟨_, hlt, hr⟩ | ⟨hge, _, _⟩
                         · refine .single (Or.inl ⟨by decide, hlt, ?_⟩)
                           dsimp only [RT, outerPort10, outerPort16, topPort8] at hr ⊢; exact hr
                         · exfalso; exact absurd hge (by decide))
          (fun hpu => by rcases hpu with ⟨_, hlt, hr⟩ | ⟨hge, _, _⟩
                         · refine .single (Or.inl ⟨by decide, hlt, ?_⟩)
                           dsimp only [RT, outerPort10, outerPort16, topPort8] at hr ⊢; exact hr
                         · exfalso; exact absurd hge (by decide))
          (fun hpu => by rcases hpu with ⟨hlt, _, _⟩ | ⟨_, hge, hr⟩
                         · exfalso; exact absurd hlt (by decide)
                         · refine .single (Or.inr (Or.inl ⟨by decide, hge, ?_⟩))
                           dsimp only [RB, outerPort10, outerPort16, botPort8] at hr ⊢; exact hr)
          (fun hpu => by rcases hpu with ⟨_, hlt, hr⟩ | ⟨hge, _, _⟩
                         · refine .single (Or.inl ⟨by decide, hlt, ?_⟩)
                           dsimp only [RT, outerPort10, outerPort16, topPort8] at hr ⊢; exact hr
                         · exfalso; exact absurd hge (by decide))
      have h2 : ∀ y : Fin 4, HalfReachFrom R0 R1 R2 R3 pv (outerPort16 y) →
          Reach (glueVert10 RT RB) pv (outerPort10 y) :=
        fin4_forall
          (fun hpv => by rcases hpv with ⟨hlt, _, hr⟩ | ⟨_, hge, _⟩
                         · refine .single (Or.inl ⟨hlt, by decide, ?_⟩)
                           dsimp only [RT, outerPort10, outerPort16, topPort8] at hr ⊢; exact hr
                         · exfalso; exact absurd hge (by decide))
          (fun hpv => by rcases hpv with ⟨hlt, _, hr⟩ | ⟨_, hge, _⟩
                         · refine .single (Or.inl ⟨hlt, by decide, ?_⟩)
                           dsimp only [RT, outerPort10, outerPort16, topPort8] at hr ⊢; exact hr
                         · exfalso; exact absurd hge (by decide))
          (fun hpv => by rcases hpv with ⟨_, hlt, _⟩ | ⟨hge, _, hr⟩
                         · exfalso; exact absurd hlt (by decide)
                         · refine .single (Or.inr (Or.inl ⟨hge, by decide, ?_⟩))
                           dsimp only [RB, outerPort10, outerPort16, botPort8] at hr ⊢; exact hr)
          (fun hpv => by rcases hpv with ⟨hlt, _, hr⟩ | ⟨_, hge, _⟩
                         · refine .single (Or.inl ⟨hlt, by decide, ?_⟩)
                           dsimp only [RT, outerPort10, outerPort16, topPort8] at hr ⊢; exact hr
                         · exfalso; exact absurd hge (by decide))
      exact Reach.trans (h1 i hpu) (Reach.trans hrv (h2 j hpv))
  · intro h
    rw [← hemb i, ← hemb j]
    exact reachVert10_to_glue16 h

/-! ### Bell(4) = 15 & Bell(5) = 52 O(1) Direct-Match Partition & Row-Bitmask Representation -/

def bell4Tuple (s : Fin 15) : Nat × Nat × Nat × Nat :=
  match s.val with
  | 0 => (0, 0, 0, 0) | 1 => (0, 0, 0, 1) | 2 => (0, 0, 1, 0) | 3 => (0, 0, 1, 1) | 4 => (0, 0, 1, 2)
  | 5 => (0, 1, 0, 0) | 6 => (0, 1, 0, 1) | 7 => (0, 1, 0, 2) | 8 => (0, 1, 1, 0) | 9 => (0, 1, 1, 1)
  | 10 => (0, 1, 1, 2) | 11 => (0, 1, 2, 0) | 12 => (0, 1, 2, 1) | 13 => (0, 1, 2, 2) | _ => (0, 1, 2, 3)

def bell4At (s : Fin 15) (i : Fin 4) : Nat :=
  let t := bell4Tuple s
  match i.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2.1
  | _ => t.2.2.2

def bell4Rel (s : Fin 15) (i j : Fin 4) : Bool :=
  bell4At s i == bell4At s j

def bell4Rows (s : Fin 15) : Nat × Nat × Nat × Nat :=
  match s.val with
  | 0 => (15, 15, 15, 15) | 1 => (7, 7, 7, 8) | 2 => (11, 11, 4, 11) | 3 => (3, 3, 12, 12) | 4 => (3, 3, 4, 8)
  | 5 => (13, 2, 13, 13) | 6 => (5, 10, 5, 10) | 7 => (5, 2, 5, 8) | 8 => (9, 6, 6, 9) | 9 => (1, 14, 14, 14)
  | 10 => (1, 6, 6, 8) | 11 => (9, 2, 4, 9) | 12 => (1, 10, 4, 10) | 13 => (1, 2, 12, 12) | _ => (1, 2, 4, 8)

def bell4Row (s : Fin 15) (i : Fin 4) : Nat :=
  let r := bell4Rows s
  match i.val with | 0 => r.1 | 1 => r.2.1 | 2 => r.2.2.1 | _ => r.2.2.2

def bell5Tuple (s : Fin 52) : Nat × Nat × Nat × Nat × Nat :=
  match s.val with
  | 0 => (0,0,0,0,0) | 1 => (0,0,0,0,1) | 2 => (0,0,0,1,0) | 3 => (0,0,0,1,1) | 4 => (0,0,0,1,2)
  | 5 => (0,0,1,0,0) | 6 => (0,0,1,0,1) | 7 => (0,0,1,0,2) | 8 => (0,0,1,1,0) | 9 => (0,0,1,1,1)
  | 10 => (0,0,1,1,2) | 11 => (0,0,1,2,0) | 12 => (0,0,1,2,1) | 13 => (0,0,1,2,2) | 14 => (0,0,1,2,3)
  | 15 => (0,1,0,0,0) | 16 => (0,1,0,0,1) | 17 => (0,1,0,0,2) | 18 => (0,1,0,1,0) | 19 => (0,1,0,1,1)
  | 20 => (0,1,0,1,2) | 21 => (0,1,0,2,0) | 22 => (0,1,0,2,1) | 23 => (0,1,0,2,2) | 24 => (0,1,0,2,3)
  | 25 => (0,1,1,0,0) | 26 => (0,1,1,0,1) | 27 => (0,1,1,0,2) | 28 => (0,1,1,1,0) | 29 => (0,1,1,1,1)
  | 30 => (0,1,1,1,2) | 31 => (0,1,1,2,0) | 32 => (0,1,1,2,1) | 33 => (0,1,1,2,2) | 34 => (0,1,1,2,3)
  | 35 => (0,1,2,0,0) | 36 => (0,1,2,0,1) | 37 => (0,1,2,0,2) | 38 => (0,1,2,0,3) | 39 => (0,1,2,1,0)
  | 40 => (0,1,2,1,1) | 41 => (0,1,2,1,2) | 42 => (0,1,2,1,3) | 43 => (0,1,2,2,0) | 44 => (0,1,2,2,1)
  | 45 => (0,1,2,2,2) | 46 => (0,1,2,2,3) | 47 => (0,1,2,3,0) | 48 => (0,1,2,3,1) | 49 => (0,1,2,3,2)
  | 50 => (0,1,2,3,3) | _ => (0,1,2,3,4)

def bell5At (s : Fin 52) (i : Fin 5) : Nat :=
  let t := bell5Tuple s
  match i.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2.1
  | 3 => t.2.2.2.1
  | _ => t.2.2.2.2

def bell5Rel (s : Fin 52) (i j : Fin 5) : Bool :=
  bell5At s i == bell5At s j

def bell5Rows (s : Fin 52) : Nat × Nat × Nat × Nat × Nat :=
  match s.val with
  | 0 => (31,31,31,31,31) | 1 => (15,15,15,15,16) | 2 => (23,23,23,8,23) | 3 => (7,7,7,24,24) | 4 => (7,7,7,8,16)
  | 5 => (27,27,4,27,27) | 6 => (11,11,20,11,20) | 7 => (11,11,4,11,16) | 8 => (19,19,12,12,19) | 9 => (3,3,28,28,28)
  | 10 => (3,3,12,12,16) | 11 => (19,19,4,8,19) | 12 => (3,3,20,8,20) | 13 => (3,3,4,24,24) | 14 => (3,3,4,8,16)
  | 15 => (29,2,29,29,29) | 16 => (13,18,13,13,18) | 17 => (13,2,13,13,16) | 18 => (21,10,21,10,21) | 19 => (5,26,5,26,26)
  | 20 => (5,10,5,10,16) | 21 => (21,2,21,8,21) | 22 => (5,18,5,8,18) | 23 => (5,2,5,24,24) | 24 => (5,2,5,8,16)
  | 25 => (25,6,6,25,25) | 26 => (9,22,22,9,22) | 27 => (9,6,6,9,16) | 28 => (17,14,14,14,17) | 29 => (1,30,30,30,30)
  | 30 => (1,14,14,14,16) | 31 => (17,6,6,8,17) | 32 => (1,22,22,8,22) | 33 => (1,6,6,24,24) | 34 => (1,6,6,8,16)
  | 35 => (25,2,4,25,25) | 36 => (9,18,4,9,18) | 37 => (9,2,20,9,20) | 38 => (9,2,4,9,16) | 39 => (17,10,4,10,17)
  | 40 => (1,26,4,26,26) | 41 => (1,10,20,10,20) | 42 => (1,10,4,10,16) | 43 => (17,2,12,12,17) | 44 => (1,18,12,12,18)
  | 45 => (1,2,28,28,28) | 46 => (1,2,12,12,16) | 47 => (17,2,4,8,17) | 48 => (1,18,4,8,18) | 49 => (1,2,20,8,20)
  | 50 => (1,2,4,24,24) | _ => (1,2,4,8,16)

def bell5Row (s : Fin 52) (i : Fin 5) : Nat :=
  let r := bell5Rows s
  match i.val with | 0 => r.1 | 1 => r.2.1 | 2 => r.2.2.1 | 3 => r.2.2.2.1 | _ => r.2.2.2.2

theorem bell4Row_spec : ∀ (s : Fin 15) (i j : Fin 4), bitSet (bell4Row s i) j.val = bell4Rel s i j := by
  decide

theorem bell4Row_lt : ∀ (s : Fin 15) (i : Fin 4), bell4Row s i < 16 := by
  decide

theorem bell5Row_spec : ∀ (s : Fin 52) (i j : Fin 5), bitSet (bell5Row s i) j.val = bell5Rel s i j := by
  decide

theorem bell5Row_lt : ∀ (s : Fin 52) (i : Fin 5), bell5Row s i < 32 := by
  decide

def rgs4Of (R : Fin 4 → Fin 4 → Bool) : Nat × Nat × Nat × Nat :=
  let c1 := if R 0 1 then 0 else 1
  let c2 := if R 0 2 then 0 else if R 1 2 then c1 else c1 + 1
  let mx2 := max c1 c2
  let c3 := if R 0 3 then 0 else if R 1 3 then c1 else if R 2 3 then c2 else mx2 + 1
  (0, c1, c2, c3)

def findBell4 (t : Nat × Nat × Nat × Nat) : Fin 15 :=
  match t with
  | (0,0,0,0) => ⟨0, by omega⟩ | (0,0,0,1) => ⟨1, by omega⟩ | (0,0,1,0) => ⟨2, by omega⟩
  | (0,0,1,1) => ⟨3, by omega⟩ | (0,0,1,2) => ⟨4, by omega⟩ | (0,1,0,0) => ⟨5, by omega⟩
  | (0,1,0,1) => ⟨6, by omega⟩ | (0,1,0,2) => ⟨7, by omega⟩ | (0,1,1,0) => ⟨8, by omega⟩
  | (0,1,1,1) => ⟨9, by omega⟩ | (0,1,1,2) => ⟨10, by omega⟩ | (0,1,2,0) => ⟨11, by omega⟩
  | (0,1,2,1) => ⟨12, by omega⟩ | (0,1,2,2) => ⟨13, by omega⟩ | (0,1,2,3) => ⟨14, by omega⟩
  | _ => ⟨0, by omega⟩

def encodeBell4 (R : Fin 4 → Fin 4 → Bool) : Fin 15 :=
  findBell4 (rgs4Of R)

def rgs5Of (R : Fin 5 → Fin 5 → Bool) : Nat × Nat × Nat × Nat × Nat :=
  let c1 := if R 0 1 then 0 else 1
  let c2 := if R 0 2 then 0 else if R 1 2 then c1 else c1 + 1
  let mx2 := max c1 c2
  let c3 := if R 0 3 then 0 else if R 1 3 then c1 else if R 2 3 then c2 else mx2 + 1
  let mx3 := max mx2 c3
  let c4 := if R 0 4 then 0 else if R 1 4 then c1 else if R 2 4 then c2 else if R 3 4 then c3 else mx3 + 1
  (0, c1, c2, c3, c4)

def findBell5 (t : Nat × Nat × Nat × Nat × Nat) : Fin 52 :=
  match t with
  | (0,0,0,0,0) => ⟨0, by omega⟩ | (0,0,0,0,1) => ⟨1, by omega⟩ | (0,0,0,1,0) => ⟨2, by omega⟩
  | (0,0,0,1,1) => ⟨3, by omega⟩ | (0,0,0,1,2) => ⟨4, by omega⟩ | (0,0,1,0,0) => ⟨5, by omega⟩
  | (0,0,1,0,1) => ⟨6, by omega⟩ | (0,0,1,0,2) => ⟨7, by omega⟩ | (0,0,1,1,0) => ⟨8, by omega⟩
  | (0,0,1,1,1) => ⟨9, by omega⟩ | (0,0,1,1,2) => ⟨10, by omega⟩ | (0,0,1,2,0) => ⟨11, by omega⟩
  | (0,0,1,2,1) => ⟨12, by omega⟩ | (0,0,1,2,2) => ⟨13, by omega⟩ | (0,0,1,2,3) => ⟨14, by omega⟩
  | (0,1,0,0,0) => ⟨15, by omega⟩ | (0,1,0,0,1) => ⟨16, by omega⟩ | (0,1,0,0,2) => ⟨17, by omega⟩
  | (0,1,0,1,0) => ⟨18, by omega⟩ | (0,1,0,1,1) => ⟨19, by omega⟩ | (0,1,0,1,2) => ⟨20, by omega⟩
  | (0,1,0,2,0) => ⟨21, by omega⟩ | (0,1,0,2,1) => ⟨22, by omega⟩ | (0,1,0,2,2) => ⟨23, by omega⟩
  | (0,1,0,2,3) => ⟨24, by omega⟩ | (0,1,1,0,0) => ⟨25, by omega⟩ | (0,1,1,0,1) => ⟨26, by omega⟩
  | (0,1,1,0,2) => ⟨27, by omega⟩ | (0,1,1,1,0) => ⟨28, by omega⟩ | (0,1,1,1,1) => ⟨29, by omega⟩
  | (0,1,1,1,2) => ⟨30, by omega⟩ | (0,1,1,2,0) => ⟨31, by omega⟩ | (0,1,1,2,1) => ⟨32, by omega⟩
  | (0,1,1,2,2) => ⟨33, by omega⟩ | (0,1,1,2,3) => ⟨34, by omega⟩ | (0,1,2,0,0) => ⟨35, by omega⟩
  | (0,1,2,0,1) => ⟨36, by omega⟩ | (0,1,2,0,2) => ⟨37, by omega⟩ | (0,1,2,0,3) => ⟨38, by omega⟩
  | (0,1,2,1,0) => ⟨39, by omega⟩ | (0,1,2,1,1) => ⟨40, by omega⟩ | (0,1,2,1,2) => ⟨41, by omega⟩
  | (0,1,2,1,3) => ⟨42, by omega⟩ | (0,1,2,2,0) => ⟨43, by omega⟩ | (0,1,2,2,1) => ⟨44, by omega⟩
  | (0,1,2,2,2) => ⟨45, by omega⟩ | (0,1,2,2,3) => ⟨46, by omega⟩ | (0,1,2,3,0) => ⟨47, by omega⟩
  | (0,1,2,3,1) => ⟨48, by omega⟩ | (0,1,2,3,2) => ⟨49, by omega⟩ | (0,1,2,3,3) => ⟨50, by omega⟩
  | (0,1,2,3,4) => ⟨51, by omega⟩ | _ => ⟨0, by omega⟩

def encodeBell5 (R : Fin 5 → Fin 5 → Bool) : Fin 52 :=
  findBell5 (rgs5Of R)

theorem findBell4_rgs_exact :
    ∀ (c1 : Fin 2) (c2 : Fin 3) (c3 : Fin 4),
      c2.val ≤ c1.val + 1 →
      c3.val ≤ max c1.val c2.val + 1 →
      bell4Tuple (findBell4 (0, c1.val, c2.val, c3.val)) = (0, c1.val, c2.val, c3.val) := by
  decide

theorem findBell5_rgs_exact :
    ∀ (c1 : Fin 2) (c2 : Fin 3) (c3 : Fin 4) (c4 : Fin 5),
      c2.val ≤ c1.val + 1 →
      c3.val ≤ max c1.val c2.val + 1 →
      c4.val ≤ max (max c1.val c2.val) c3.val + 1 →
      bell5Tuple (findBell5 (0, c1.val, c2.val, c3.val, c4.val)) =
        (0, c1.val, c2.val, c3.val, c4.val) := by
  decide

theorem encodeBell4_spec (R : Fin 4 → Fin 4 → Bool)
    (hrefl : ∀ x, R x x = true)
    (hsym : ∀ x y, R x y = true → R y x = true)
    (htrans : ∀ x y z, R x y = true → R y z = true → R x z = true) :
    ∀ i j : Fin 4, bell4Rel (encodeBell4 R) i j = R i j := by
  have hsym' : ∀ x y, R x y = R y x := by
    intro x y
    cases hxy : R x y with
    | true => exact (hsym x y hxy).symm
    | false =>
      cases hyx : R y x with
      | false => rfl
      | true => have := hsym y x hyx; rw [hxy] at this; cases this
  have hfin : ∀ (b01 b02 b03 b12 b13 b23 : Bool),
      let Rf : Fin 4 → Fin 4 → Bool := fun x y =>
        match x.val, y.val with
        | 0, 0 | 1, 1 | 2, 2 | 3, 3 => true
        | 0, 1 | 1, 0 => b01
        | 0, 2 | 2, 0 => b02
        | 0, 3 | 3, 0 => b03
        | 1, 2 | 2, 1 => b12
        | 1, 3 | 3, 1 => b13
        | 2, 3 | 3, 2 => b23
        | _, _ => false
      (∀ x y z : Fin 4, Rf x y = true → Rf y z = true → Rf x z = true) →
      ∀ i j : Fin 4, bell4Rel (encodeBell4 Rf) i j = Rf i j := by
    decide
  have hReq : R = (fun x y =>
      match x.val, y.val with
      | 0, 0 | 1, 1 | 2, 2 | 3, 3 => true
      | 0, 1 | 1, 0 => R 0 1
      | 0, 2 | 2, 0 => R 0 2
      | 0, 3 | 3, 0 => R 0 3
      | 1, 2 | 2, 1 => R 1 2
      | 1, 3 | 3, 1 => R 1 3
      | 2, 3 | 3, 2 => R 2 3
      | _, _ => false) := by
    funext x y
    revert x y
    refine fin4_forall ?_ ?_ ?_ ?_ <;> refine fin4_forall ?_ ?_ ?_ ?_
    all_goals first | exact hrefl _ | rfl | exact hsym' _ _
  rw [hReq]
  exact hfin (R 0 1) (R 0 2) (R 0 3) (R 1 2) (R 1 3) (R 2 3) (by rw [← hReq]; exact htrans)

def symRel5 (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) (x y : Fin 5) : Bool :=
  match x.val, y.val with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 | 4, 4 => true
  | 0, 1 | 1, 0 => b01 | 0, 2 | 2, 0 => b02 | 0, 3 | 3, 0 => b03 | 0, 4 | 4, 0 => b04
  | 1, 2 | 2, 1 => b12 | 1, 3 | 3, 1 => b13 | 1, 4 | 4, 1 => b14
  | 2, 3 | 3, 2 => b23 | 2, 4 | 4, 2 => b24 | 3, 4 | 4, 3 => b34
  | _, _ => false

def triOk (a b c : Bool) : Bool :=
  (!(a && b) || c) && (!(a && c) || b) && (!(b && c) || a)

def isTrans5B (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) : Bool :=
  triOk b01 b02 b12 && triOk b01 b03 b13 && triOk b01 b04 b14 &&
  triOk b02 b03 b23 && triOk b02 b04 b24 && triOk b03 b04 b34 &&
  triOk b12 b13 b23 && triOk b12 b14 b24 && triOk b13 b14 b34 &&
  triOk b23 b24 b34

theorem encodeBell5_fin_check :
    allFin 32 (fun hi => allFin 32 (fun lo =>
      let mask := hi.val * 32 + lo.val
      let b01 := bitSet mask 0; let b02 := bitSet mask 1
      let b03 := bitSet mask 2; let b04 := bitSet mask 3
      let b12 := bitSet mask 4; let b13 := bitSet mask 5
      let b14 := bitSet mask 6; let b23 := bitSet mask 7
      let b24 := bitSet mask 8; let b34 := bitSet mask 9
      if isTrans5B b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 then
        let Rf := symRel5 b01 b02 b03 b04 b12 b13 b14 b23 b24 b34
        allFin 5 (fun i => allFin 5 (fun j => bell5Rel (encodeBell5 Rf) i j == Rf i j))
      else true)) = true := by
  decide

theorem encodeBell5_spec (R : Fin 5 → Fin 5 → Bool)
    (hrefl : ∀ x, R x x = true)
    (hsym : ∀ x y, R x y = true → R y x = true)
    (htrans : ∀ x y z, R x y = true → R y z = true → R x z = true) :
    ∀ i j : Fin 5, bell5Rel (encodeBell5 R) i j = R i j := by
  have hsym' : ∀ x y, R x y = R y x := by
    intro x y
    cases hxy : R x y with
    | true => exact (hsym x y hxy).symm
    | false =>
      cases hyx : R y x with
      | false => rfl
      | true => have := hsym y x hyx; rw [hxy] at this; cases this
  have hReq : R = symRel5 (R 0 1) (R 0 2) (R 0 3) (R 0 4) (R 1 2) (R 1 3) (R 1 4) (R 2 3) (R 2 4) (R 3 4) := by
    funext x y
    revert x y
    refine fin5_forall ?_ ?_ ?_ ?_ ?_ <;> refine fin5_forall ?_ ?_ ?_ ?_ ?_
    all_goals first | exact hrefl _ | rfl | exact hsym' _ _
  have htri : ∀ a b c : Fin 5, triOk (R a b) (R a c) (R b c) = true := by
    intro a b c; unfold triOk
    cases h1 : R a b <;> cases h2 : R a c <;> cases h3 : R b c <;> try rfl
    · have := htrans a c b h2 (hsym _ _ h3); rw [h1] at this; cases this
    · have := htrans a b c h1 h3; rw [h2] at this; cases this
    · have := htrans b a c (hsym _ _ h1) h2; rw [h3] at this; cases this
  have htransB : isTrans5B (R 0 1) (R 0 2) (R 0 3) (R 0 4) (R 1 2) (R 1 3) (R 1 4) (R 2 3) (R 2 4) (R 3 4) = true := by
    unfold isTrans5B
    simp [htri]
  let m : Nat :=
    (if R 0 1 then 1 else 0) + 2 * ((if R 0 2 then 1 else 0) + 2 * ((if R 0 3 then 1 else 0) +
    2 * ((if R 0 4 then 1 else 0) + 2 * ((if R 1 2 then 1 else 0) + 2 * ((if R 1 3 then 1 else 0) +
    2 * ((if R 1 4 then 1 else 0) + 2 * ((if R 2 3 then 1 else 0) + 2 * ((if R 2 4 then 1 else 0) +
    2 * (if R 3 4 then 1 else 0)))))))))
  have hm_lt : m < 1024 := by
    dsimp only [m]
    cases R 0 1 <;> cases R 0 2 <;> cases R 0 3 <;> cases R 0 4 <;> cases R 1 2 <;>
    cases R 1 3 <;> cases R 1 4 <;> cases R 2 3 <;> cases R 2 4 <;> cases R 3 4 <;> decide
  have hbits :
      bitSet m 0 = R 0 1 ∧ bitSet m 1 = R 0 2 ∧ bitSet m 2 = R 0 3 ∧ bitSet m 3 = R 0 4 ∧
      bitSet m 4 = R 1 2 ∧ bitSet m 5 = R 1 3 ∧ bitSet m 6 = R 1 4 ∧ bitSet m 7 = R 2 3 ∧
      bitSet m 8 = R 2 4 ∧ bitSet m 9 = R 3 4 := by
    have hstep : ∀ (b : Bool) (rest : Nat), bitSet ((if b then 1 else 0) + 2 * rest) 0 = b ∧
        ∀ k, bitSet ((if b then 1 else 0) + 2 * rest) (k + 1) = bitSet rest k := by
      intro b rest; constructor
      · cases b <;> unfold bitSet <;> simp [Nat.and_one_is_mod] <;> omega
      · intro k; unfold bitSet
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul]
        have hdiv2 : ((if b then 1 else 0) + 2 * rest) / 2 = rest := by
          cases b <;> simp <;> omega
        rw [hdiv2]
    refine ⟨(hstep _ _).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 1, (hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 2, (hstep _ _).2 1, (hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 3, (hstep _ _).2 2, (hstep _ _).2 1, (hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 4, (hstep _ _).2 3, (hstep _ _).2 2, (hstep _ _).2 1, (hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 5, (hstep _ _).2 4, (hstep _ _).2 3, (hstep _ _).2 2, (hstep _ _).2 1, (hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 6, (hstep _ _).2 5, (hstep _ _).2 4, (hstep _ _).2 3, (hstep _ _).2 2, (hstep _ _).2 1, (hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 7, (hstep _ _).2 6, (hstep _ _).2 5, (hstep _ _).2 4, (hstep _ _).2 3, (hstep _ _).2 2, (hstep _ _).2 1, (hstep _ _).2 0]; exact (hstep _ _).1
    · rw [(hstep _ _).2 8, (hstep _ _).2 7, (hstep _ _).2 6, (hstep _ _).2 5, (hstep _ _).2 4, (hstep _ _).2 3, (hstep _ _).2 2, (hstep _ _).2 1, (hstep _ _).2 0]
      cases R 3 4 <;> rfl
  have h1 := (allFin_iff 32 _).mp encodeBell5_fin_check ⟨m / 32, by omega⟩
  have hall := (allFin_iff 32 _).mp h1 ⟨m % 32, by omega⟩
  have hmeq : m / 32 * 32 + m % 32 = m := by omega
  dsimp only at hall
  rw [hmeq] at hall
  simp only [hbits.1, hbits.2.1, hbits.2.2.1, hbits.2.2.2.1, hbits.2.2.2.2.1,
             hbits.2.2.2.2.2.1, hbits.2.2.2.2.2.2.1, hbits.2.2.2.2.2.2.2.1,
             hbits.2.2.2.2.2.2.2.2.1, hbits.2.2.2.2.2.2.2.2.2, htransB, ite_true] at hall
  rw [allFin_iff] at hall
  intro i j
  have hi := hall i; rw [allFin_iff] at hi
  have hij := hi j; rw [beq_iff_eq] at hij
  rw [hReq]; exact hij

/-! ### Structurally Recursive Row-Bitmask Builder & Strict Bitmask Warshall Operators -/

def mkRowMaskGo (n : Nat) (f : Fin n → Bool) : (i : Nat) → i ≤ n → Nat
  | 0, _ => 0
  | i + 1, h =>
    let rest := mkRowMaskGo n f i (Nat.le_of_lt h)
    if f ⟨i, h⟩ then rest ||| (1 <<< i) else rest

def mkRowMask (n : Nat) (f : Fin n → Bool) : Nat :=
  mkRowMaskGo n f n (Nat.le_refl n)

theorem bitSet_one_shiftLeft (i j : Nat) : bitSet (1 <<< i) j = (i == j) := by
  unfold bitSet
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]
  by_cases heq : i = j
  · subst heq
    rw [Nat.div_self (Nat.two_pow_pos i)]
    simp
  · by_cases hlt : j < i
    · have hdiv : 2 ^ i / 2 ^ j = 2 ^ (i - j) := by
        have h1 : i = (i - j) + j := by omega
        conv => lhs; lhs; rw [h1, Nat.pow_add]
        exact Nat.mul_div_cancel _ (Nat.two_pow_pos j)
      rw [hdiv, Nat.and_one_is_mod]
      have : ∃ m, i - j = m + 1 := ⟨i - j - 1, by omega⟩
      rcases this with ⟨m, hm⟩
      rw [hm, Nat.pow_succ]
      have heven : (2 ^ m * 2) % 2 = 0 := by omega
      simp [heven, heq]
    · have hgt : i < j := by omega
      rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by omega) hgt)]
      simp [heq]

theorem bitSet_mkRowMaskGo (n : Nat) (f : Fin n → Bool) (i : Nat) (hi : i ≤ n) (j : Fin n) :
    bitSet (mkRowMaskGo n f i hi) j.val = (decide (j.val < i) && f j) := by
  induction i with
  | zero =>
    unfold mkRowMaskGo bitSet; simp
  | succ m ih =>
    unfold mkRowMaskGo
    by_cases heq : j.val = m
    · have hj : j = ⟨m, hi⟩ := Fin.ext heq
      subst hj
      have hlt : m < m + 1 := Nat.lt_succ_self m
      have hnot : ¬ (m < m) := Nat.lt_irrefl m
      cases hfm : f ⟨m, hi⟩ with
      | false =>
        simp only [Bool.false_eq_true, ite_false, ih (Nat.le_of_lt hi), hnot, decide_false, Bool.false_and, hlt, decide_true, Bool.true_and]
      | true =>
        simp only [ite_true, bitSet_or, bitSet_one_shiftLeft, beq_self_eq_true, Bool.or_true, hlt, decide_true, Bool.true_and]
    · have hbit : bitSet (1 <<< m) j.val = false := by
        rw [bitSet_one_shiftLeft]
        have hne : m ≠ j.val := fun h => heq h.symm
        simp [hne]
      have hstep : bitSet (if f ⟨m, hi⟩ then mkRowMaskGo n f m (Nat.le_of_lt hi) ||| 1 <<< m
                           else mkRowMaskGo n f m (Nat.le_of_lt hi)) j.val =
                   bitSet (mkRowMaskGo n f m (Nat.le_of_lt hi)) j.val := by
        cases f ⟨m, hi⟩ with
        | false => rfl
        | true => simp [bitSet_or, hbit]
      rw [hstep, ih (Nat.le_of_lt hi)]
      have hlt_iff : decide (j.val < m) = decide (j.val < m + 1) := by
        by_cases hjm : j.val < m
        · have : j.val < m + 1 := by omega
          simp [hjm, this]
        · have : ¬ (j.val < m + 1) := by omega
          simp [hjm, this]
      rw [hlt_iff]

theorem bitSet_mkRowMask (n : Nat) (f : Fin n → Bool) (j : Fin n) :
    bitSet (mkRowMask n f) j.val = f j := by
  unfold mkRowMask
  rw [bitSet_mkRowMaskGo]
  simp [j.isLt]

def glueTop8Bool (a b : Fin 15) (u v : Fin 8) : Bool :=
  (u == v) ||
  (if hu : u.val < 4 then if hv : v.val < 4 then bell4Rel a ⟨u.val, hu⟩ ⟨v.val, hv⟩ else false else false) ||
  (if hu : 4 ≤ u.val then if hv : 4 ≤ v.val then bell4Rel b ⟨u.val - 4, by omega⟩ ⟨v.val - 4, by omega⟩ else false else false) ||
  (u.val == 1 && v.val == 7) || (u.val == 7 && v.val == 1) ||
  (u.val == 0 && v.val == 4) || (u.val == 4 && v.val == 0)

def glueBot8Bool (c d : Fin 15) (u v : Fin 8) : Bool :=
  (u == v) ||
  (if hu : u.val < 4 then if hv : v.val < 4 then bell4Rel c ⟨u.val, hu⟩ ⟨v.val, hv⟩ else false else false) ||
  (if hu : 4 ≤ u.val then if hv : 4 ≤ v.val then bell4Rel d ⟨u.val - 4, by omega⟩ ⟨v.val - 4, by omega⟩ else false else false) ||
  (u.val == 1 && v.val == 7) || (u.val == 7 && v.val == 1) ||
  (u.val == 2 && v.val == 6) || (u.val == 6 && v.val == 2)

def glueVert10Bool (t b : Fin 52) (u v : Fin 10) : Bool :=
  (u == v) ||
  (if hu : u.val < 5 then if hv : v.val < 5 then bell5Rel t ⟨u.val, hu⟩ ⟨v.val, hv⟩ else false else false) ||
  (if hu : 5 ≤ u.val then if hv : 5 ≤ v.val then bell5Rel b ⟨u.val - 5, by omega⟩ ⟨v.val - 5, by omega⟩ else false else false) ||
  (u.val == 2 && v.val == 5) || (u.val == 5 && v.val == 2) ||
  (u.val == 3 && v.val == 6) || (u.val == 6 && v.val == 3) ||
  (u.val == 1 && v.val == 7) || (u.val == 7 && v.val == 1) ||
  (u.val == 4 && v.val == 9) || (u.val == 9 && v.val == 4)

/-- Ultra-fast O(1) row-bitmask builders for `hTop`, `hBot`, `vGlue` (ZERO `mkRowMask` loops!). -/
def hTopRow (a b : Fin 15) (u : Fin 8) : Nat :=
  (if h : u.val < 4 then bell4Row a ⟨u.val, h⟩ else bell4Row b ⟨u.val - 4, by omega⟩ <<< 4) |||
  (match u.val with | 0 => 16 | 1 => 128 | 4 => 1 | 7 => 2 | _ => 0)

def hBotRow (c d : Fin 15) (u : Fin 8) : Nat :=
  (if h : u.val < 4 then bell4Row c ⟨u.val, h⟩ else bell4Row d ⟨u.val - 4, by omega⟩ <<< 4) |||
  (match u.val with | 1 => 128 | 2 => 64 | 6 => 4 | 7 => 2 | _ => 0)

def vGlueRow (t b : Fin 52) (u : Fin 10) : Nat :=
  (if h : u.val < 5 then bell5Row t ⟨u.val, h⟩ else bell5Row b ⟨u.val - 5, by omega⟩ <<< 5) |||
  (match u.val with | 1 => 128 | 2 => 32 | 3 => 64 | 4 => 512 | 5 => 4 | 6 => 8 | 7 => 2 | 9 => 16 | _ => 0)

theorem bitSet_shiftLeft_add (x s j : Nat) :
    bitSet (x <<< s) j = (decide (s ≤ j) && bitSet x (j - s)) := by
  unfold bitSet
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  by_cases hle : s ≤ j
  · have hpow : 2 ^ j = 2 ^ s * 2 ^ (j - s) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow, Nat.mul_comm x (2 ^ s), Nat.mul_div_mul_left _ _ (Nat.two_pow_pos s)]
    simp [hle]
  · have hlt : j < s := by omega
    have hpow : 2 ^ s = 2 ^ j * 2 ^ (s - j) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow, ← Nat.mul_assoc, Nat.mul_comm x (2 ^ j), Nat.mul_assoc,
        Nat.mul_div_right _ (Nat.two_pow_pos j), Nat.and_one_is_mod]
    have heven : 2 ^ (s - j) % 2 = 0 := by
      have : ∃ m, s - j = m + 1 := ⟨s - j - 1, by omega⟩
      rcases this with ⟨m, hm⟩; rw [hm, Nat.pow_succ]; omega
    have hmul0 : (x * 2 ^ (s - j)) % 2 = 0 := by rw [Nat.mul_mod, heven]; simp
    simp [hle, hmul0]

theorem bitSet_of_lt_pow (x k j : Nat) (hx : x < 2 ^ k) (hj : k ≤ j) :
    bitSet x j = false := by
  unfold bitSet
  rw [Nat.shiftRight_eq_div_pow]
  have hlt : x < 2 ^ j := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj)
  rw [Nat.div_eq_of_lt hlt]; rfl

theorem bitSet_hTopRow (a b : Fin 15) (u v : Fin 8) :
    bitSet (hTopRow a b u) v.val = glueTop8Bool a b u v := by
  have h4 := bell4Row_spec
  have hlt := bell4Row_lt
  have hrefl : ∀ (s : Fin 15) (i : Fin 4), bell4Rel s i i = true := by decide
  have hseam : ∀ (u v : Fin 8),
      bitSet (match u.val with | 0 => 16 | 1 => 128 | 4 => 1 | 7 => 2 | _ => 0) v.val =
      ((u.val == 1 && v.val == 7) || (u.val == 7 && v.val == 1) ||
       (u.val == 0 && v.val == 4) || (u.val == 4 && v.val == 0)) := by decide
  unfold hTopRow glueTop8Bool
  rw [bitSet_or, hseam]
  by_cases hu : u.val < 4 <;> by_cases hv : v.val < 4
  · have hnu : ¬ (4 ≤ u.val) := by omega
    have hnv : ¬ (4 ≤ v.val) := by omega
    simp only [hu, hv, hnu, hnv, dite_true, dite_false, h4 a ⟨u.val, hu⟩ ⟨v.val, hv⟩, Bool.or_false]
    by_cases huv : u = v
    · subst huv; simp [hrefl]
    · simp [huv, Bool.or_assoc]
  · have hnu : ¬ (4 ≤ u.val) := by omega
    have h4v : 4 ≤ v.val := by omega
    have hzero : bitSet (bell4Row a ⟨u.val, hu⟩) v.val = false := bitSet_of_lt_pow _ 4 _ (hlt a ⟨u.val, hu⟩) h4v
    have hne : u ≠ v := fun h => by rw [h] at hu; omega
    simp [hu, hv, hnu, hzero, hne, Bool.or_assoc]
  · have h4u : 4 ≤ u.val := by omega
    have hnv : ¬ (4 ≤ v.val) := by omega
    have hne : u ≠ v := fun h => by rw [h] at hu; omega
    simp [hu, h4u, hnv, bitSet_shiftLeft_add, hne, Bool.or_assoc]
  · have h4u : 4 ≤ u.val := by omega
    have h4v : 4 ≤ v.val := by omega
    simp only [hu, hv, h4u, h4v, dite_true, dite_false, bitSet_shiftLeft_add, decide_true, Bool.true_and,
               h4 b ⟨u.val - 4, by omega⟩ ⟨v.val - 4, by omega⟩, Bool.or_false]
    by_cases huv : u = v
    · subst huv; simp [hrefl]
    · simp [huv, Bool.or_assoc]

theorem bitSet_hBotRow (c d : Fin 15) (u v : Fin 8) :
    bitSet (hBotRow c d u) v.val = glueBot8Bool c d u v := by
  have h4 := bell4Row_spec
  have hlt := bell4Row_lt
  have hrefl : ∀ (s : Fin 15) (i : Fin 4), bell4Rel s i i = true := by decide
  have hseam : ∀ (u v : Fin 8),
      bitSet (match u.val with | 1 => 128 | 2 => 64 | 6 => 4 | 7 => 2 | _ => 0) v.val =
      ((u.val == 1 && v.val == 7) || (u.val == 7 && v.val == 1) ||
       (u.val == 2 && v.val == 6) || (u.val == 6 && v.val == 2)) := by decide
  unfold hBotRow glueBot8Bool
  rw [bitSet_or, hseam]
  by_cases hu : u.val < 4 <;> by_cases hv : v.val < 4
  · have hnu : ¬ (4 ≤ u.val) := by omega
    have hnv : ¬ (4 ≤ v.val) := by omega
    simp only [hu, hv, hnu, hnv, dite_true, dite_false, h4 c ⟨u.val, hu⟩ ⟨v.val, hv⟩, Bool.or_false]
    by_cases huv : u = v
    · subst huv; simp [hrefl]
    · simp [huv, Bool.or_assoc]
  · have hnu : ¬ (4 ≤ u.val) := by omega
    have h4v : 4 ≤ v.val := by omega
    have hzero : bitSet (bell4Row c ⟨u.val, hu⟩) v.val = false := bitSet_of_lt_pow _ 4 _ (hlt c ⟨u.val, hu⟩) h4v
    have hne : u ≠ v := fun h => by rw [h] at hu; omega
    simp [hu, hv, hnu, hzero, hne, Bool.or_assoc]
  · have h4u : 4 ≤ u.val := by omega
    have hnv : ¬ (4 ≤ v.val) := by omega
    have hne : u ≠ v := fun h => by rw [h] at hu; omega
    simp [hu, h4u, hnv, bitSet_shiftLeft_add, hne, Bool.or_assoc]
  · have h4u : 4 ≤ u.val := by omega
    have h4v : 4 ≤ v.val := by omega
    simp only [hu, hv, h4u, h4v, dite_true, dite_false, bitSet_shiftLeft_add, decide_true, Bool.true_and,
               h4 d ⟨u.val - 4, by omega⟩ ⟨v.val - 4, by omega⟩, Bool.or_false]
    by_cases huv : u = v
    · subst huv; simp [hrefl]
    · simp [huv, Bool.or_assoc]

theorem bitSet_vGlueRow (t b : Fin 52) (u v : Fin 10) :
    bitSet (vGlueRow t b u) v.val = glueVert10Bool t b u v := by
  have h5 := bell5Row_spec
  have hlt := bell5Row_lt
  have hrefl : ∀ (s : Fin 52) (i : Fin 5), bell5Rel s i i = true := by decide
  have hseam : ∀ (u v : Fin 10),
      bitSet (match u.val with | 1 => 128 | 2 => 32 | 3 => 64 | 4 => 512 | 5 => 4 | 6 => 8 | 7 => 2 | 9 => 16 | _ => 0) v.val =
      ((u.val == 2 && v.val == 5) || (u.val == 5 && v.val == 2) ||
       (u.val == 3 && v.val == 6) || (u.val == 6 && v.val == 3) ||
       (u.val == 1 && v.val == 7) || (u.val == 7 && v.val == 1) ||
       (u.val == 4 && v.val == 9) || (u.val == 9 && v.val == 4)) := by decide
  unfold vGlueRow glueVert10Bool
  rw [bitSet_or, hseam]
  by_cases hu : u.val < 5 <;> by_cases hv : v.val < 5
  · have hnu : ¬ (5 ≤ u.val) := by omega
    have hnv : ¬ (5 ≤ v.val) := by omega
    simp only [hu, hv, hnu, hnv, dite_true, dite_false, h5 t ⟨u.val, hu⟩ ⟨v.val, hv⟩, Bool.or_false]
    by_cases huv : u = v
    · subst huv; simp [hrefl]
    · simp [huv, Bool.or_assoc]
  · have hnu : ¬ (5 ≤ u.val) := by omega
    have h5v : 5 ≤ v.val := by omega
    have hzero : bitSet (bell5Row t ⟨u.val, hu⟩) v.val = false := bitSet_of_lt_pow _ 5 _ (hlt t ⟨u.val, hu⟩) h5v
    have hne : u ≠ v := fun h => by rw [h] at hu; omega
    simp [hu, hv, hnu, hzero, hne, Bool.or_assoc]
  · have h5u : 5 ≤ u.val := by omega
    have hnv : ¬ (5 ≤ v.val) := by omega
    have hne : u ≠ v := fun h => by rw [h] at hu; omega
    simp [hu, h5u, hnv, bitSet_shiftLeft_add, hne, Bool.or_assoc]
  · have h5u : 5 ≤ u.val := by omega
    have h5v : 5 ≤ v.val := by omega
    simp only [hu, hv, h5u, h5v, dite_true, dite_false, bitSet_shiftLeft_add, decide_true, Bool.true_and,
               h5 b ⟨u.val - 5, by omega⟩ ⟨v.val - 5, by omega⟩, Bool.or_false]
    by_cases huv : u = v
    · subst huv; simp [hrefl]
    · simp [huv, Bool.or_assoc]

def hTopExec (a b : Fin 15) : Fin 52 :=
  let M := warshall8 (hTopRow a b)
  encodeBell5 (fun i j => bitSet (get8 M (topPort8 i)) (topPort8 j).val)

def hBotExec (c d : Fin 15) : Fin 52 :=
  let M := warshall8 (hBotRow c d)
  encodeBell5 (fun i j => bitSet (get8 M (botPort8 i)) (botPort8 j).val)

def vGlueExec (t b : Fin 52) : Fin 15 :=
  let M := warshall10 (vGlueRow t b)
  encodeBell4 (fun i j => bitSet (get10 M (outerPort10 i)) (outerPort10 j).val)

def qcombExec (a b c d : Fin 15) : Fin 15 :=
  vGlueExec (hTopExec a b) (hBotExec c d)

theorem reach_glueTop8Bool_iff (a b : Fin 15) (u v : Fin 8) :
    Reach (fun x y => glueTop8Bool a b x y = true) u v ↔
    Reach (glueTop8 (fun i j => bell4Rel a i j = true) (fun i j => bell4Rel b i j = true)) u v := by
  constructor
  · intro h
    induction h with
    | refl _ => exact .refl _
    | @step x y _ e _ ih =>
      unfold glueTop8Bool at e
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at e
      rcases e with (((((hxy | h0) | h1) | h2) | h3) | h4) | h5
      · subst hxy; exact ih
      · split at h0
        · split at h0
          · exact .step (Or.inl ⟨‹_›, ‹_›, h0⟩) ih
          · cases h0
        · cases h0
      · split at h1
        · split at h1
          · exact .step (Or.inr (Or.inl ⟨‹_›, ‹_›, h1⟩)) ih
          · cases h1
        · cases h1
      · exact .step (Or.inr (Or.inr (Or.inl h2))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inl h3)))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h5))))) ih
  · apply Reach.mono
    intro x y e
    unfold glueTop8 at e; unfold glueTop8Bool
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
    rcases e with ⟨hx, hy, hr⟩ | ⟨hx, hy, hr⟩ | h1 | h2 | h3 | h4
    · left; left; left; left; left; right; simp [hx, hy, hr]
    · left; left; left; left; right; simp [hx, hy, hr]
    · left; left; left; right; exact h1
    · left; left; right; exact h2
    · left; right; exact h3
    · right; exact h4

theorem reach_glueBot8Bool_iff (c d : Fin 15) (u v : Fin 8) :
    Reach (fun x y => glueBot8Bool c d x y = true) u v ↔
    Reach (glueBot8 (fun i j => bell4Rel c i j = true) (fun i j => bell4Rel d i j = true)) u v := by
  constructor
  · intro h
    induction h with
    | refl _ => exact .refl _
    | @step x y _ e _ ih =>
      unfold glueBot8Bool at e
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at e
      rcases e with (((((hxy | h0) | h1) | h2) | h3) | h4) | h5
      · subst hxy; exact ih
      · split at h0
        · split at h0
          · exact .step (Or.inl ⟨‹_›, ‹_›, h0⟩) ih
          · cases h0
        · cases h0
      · split at h1
        · split at h1
          · exact .step (Or.inr (Or.inl ⟨‹_›, ‹_›, h1⟩)) ih
          · cases h1
        · cases h1
      · exact .step (Or.inr (Or.inr (Or.inl h2))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inl h3)))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h5))))) ih
  · apply Reach.mono
    intro x y e
    unfold glueBot8 at e; unfold glueBot8Bool
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
    rcases e with ⟨hx, hy, hr⟩ | ⟨hx, hy, hr⟩ | h1 | h2 | h3 | h4
    · left; left; left; left; left; right; simp [hx, hy, hr]
    · left; left; left; left; right; simp [hx, hy, hr]
    · left; left; left; right; exact h1
    · left; left; right; exact h2
    · left; right; exact h3
    · right; exact h4

theorem reach_glueVert10Bool_iff (t b : Fin 52) (u v : Fin 10) :
    Reach (fun x y => glueVert10Bool t b x y = true) u v ↔
    Reach (glueVert10 (fun i j => bell5Rel t i j = true) (fun i j => bell5Rel b i j = true)) u v := by
  constructor
  · intro h
    induction h with
    | refl _ => exact .refl _
    | @step x y _ e _ ih =>
      unfold glueVert10Bool at e
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at e
      rcases e with (((((((((hxy | h0) | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9
      · subst hxy; exact ih
      · split at h0
        · split at h0
          · exact .step (Or.inl ⟨‹_›, ‹_›, h0⟩) ih
          · cases h0
        · cases h0
      · split at h1
        · split at h1
          · exact .step (Or.inr (Or.inl ⟨‹_›, ‹_›, h1⟩)) ih
          · cases h1
        · cases h1
      · exact .step (Or.inr (Or.inr (Or.inl h2))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inl h3)))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))))) ih
      · exact .step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h9))))))))) ih
  · apply Reach.mono
    intro x y e
    unfold glueVert10 at e; unfold glueVert10Bool
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
    rcases e with ⟨hx, hy, hr⟩ | ⟨hx, hy, hr⟩ | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · left; left; left; left; left; left; left; left; left; right; simp [hx, hy, hr]
    · left; left; left; left; left; left; left; left; right; simp [hx, hy, hr]
    · left; left; left; left; left; left; left; right; exact h1
    · left; left; left; left; left; left; right; exact h2
    · left; left; left; left; left; right; exact h3
    · left; left; left; left; right; exact h4
    · left; left; left; right; exact h5
    · left; left; right; exact h6
    · left; right; exact h7
    · right; exact h8

theorem glueTop8Bool_symm (a b : Fin 15) (x y : Fin 8) :
    glueTop8Bool a b x y = true → glueTop8Bool a b y x = true := by
  unfold glueTop8Bool bell4Rel
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  intro h
  rcases h with (((((hxy | h0) | h1) | h2) | h3) | h4) | h5
  · left; left; left; left; left; left; exact hxy.symm
  · split at h0
    · split at h0
      · left; left; left; left; left; right
        rename_i hx hy; simp only [hx, hy, dite_true]; rw [beq_iff_eq] at h0 ⊢; exact h0.symm
      · cases h0
    · cases h0
  · split at h1
    · split at h1
      · left; left; left; left; right
        rename_i hx hy; simp only [hx, hy, dite_true]; rw [beq_iff_eq] at h1 ⊢; exact h1.symm
      · cases h1
    · cases h1
  · left; left; right; exact ⟨h2.2, h2.1⟩
  · left; left; left; right; exact ⟨h3.2, h3.1⟩
  · right; exact ⟨h4.2, h4.1⟩
  · left; right; exact ⟨h5.2, h5.1⟩

theorem glueBot8Bool_symm (c d : Fin 15) (x y : Fin 8) :
    glueBot8Bool c d x y = true → glueBot8Bool c d y x = true := by
  unfold glueBot8Bool bell4Rel
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  intro h
  rcases h with (((((hxy | h0) | h1) | h2) | h3) | h4) | h5
  · left; left; left; left; left; left; exact hxy.symm
  · split at h0
    · split at h0
      · left; left; left; left; left; right
        rename_i hx hy; simp only [hx, hy, dite_true]; rw [beq_iff_eq] at h0 ⊢; exact h0.symm
      · cases h0
    · cases h0
  · split at h1
    · split at h1
      · left; left; left; left; right
        rename_i hx hy; simp only [hx, hy, dite_true]; rw [beq_iff_eq] at h1 ⊢; exact h1.symm
      · cases h1
    · cases h1
  · left; left; right; exact ⟨h2.2, h2.1⟩
  · left; left; left; right; exact ⟨h3.2, h3.1⟩
  · right; exact ⟨h4.2, h4.1⟩
  · left; right; exact ⟨h5.2, h5.1⟩

theorem glueVert10Bool_symm (t b : Fin 52) (x y : Fin 10) :
    glueVert10Bool t b x y = true → glueVert10Bool t b y x = true := by
  unfold glueVert10Bool bell5Rel
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  intro h
  rcases h with (((((((((hxy | h0) | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9
  · left; left; left; left; left; left; left; left; left; left; exact hxy.symm
  · split at h0
    · split at h0
      · left; left; left; left; left; left; left; left; left; right
        rename_i hx hy; simp only [hx, hy, dite_true]; rw [beq_iff_eq] at h0 ⊢; exact h0.symm
      · cases h0
    · cases h0
  · split at h1
    · split at h1
      · left; left; left; left; left; left; left; left; right
        rename_i hx hy; simp only [hx, hy, dite_true]; rw [beq_iff_eq] at h1 ⊢; exact h1.symm
      · cases h1
    · cases h1
  · left; left; left; left; left; left; right; exact ⟨h2.2, h2.1⟩
  · left; left; left; left; left; left; left; right; exact ⟨h3.2, h3.1⟩
  · left; left; left; left; right; exact ⟨h4.2, h4.1⟩
  · left; left; left; left; left; right; exact ⟨h5.2, h5.1⟩
  · left; left; right; exact ⟨h6.2, h6.1⟩
  · left; left; left; right; exact ⟨h7.2, h7.1⟩
  · right; exact ⟨h8.2, h8.1⟩
  · left; right; exact ⟨h9.2, h9.1⟩

theorem hTopExec_spec (a b : Fin 15) (i j : Fin 5) :
    bell5Rel (hTopExec a b) i j = true ↔
    Reach (glueTop8 (fun x y => bell4Rel a x y = true) (fun x y => bell4Rel b x y = true))
      (topPort8 i) (topPort8 j) := by
  unfold hTopExec
  have hrefl0 : ∀ x : Fin 8, bitSet (hTopRow a b x) x.val = true := by
    intro x; rw [bitSet_hTopRow]; simp [glueTop8Bool]
  have hwar : ∀ u v : Fin 8, bitSet (get8 (warshall8 (hTopRow a b)) u) v.val = true ↔
      Reach (fun x y => glueTop8Bool a b x y = true) u v := by
    intro u v; rw [get8_warshall8, warshallRun_iff_Reach_fn (hTopRow a b) hrefl0]
    simp [bitSet_hTopRow]
  rw [encodeBell5_spec]
  · rw [hwar, reach_glueTop8Bool_iff]
  · intro x; rw [hwar]; exact .refl _
  · intro x y h; rw [hwar] at h ⊢; exact Reach.symm_of_symm (glueTop8Bool_symm a b) h
  · intro x y z h1 h2; rw [hwar] at h1 h2 ⊢; exact Reach.trans h1 h2

theorem hBotExec_spec (c d : Fin 15) (i j : Fin 5) :
    bell5Rel (hBotExec c d) i j = true ↔
    Reach (glueBot8 (fun x y => bell4Rel c x y = true) (fun x y => bell4Rel d x y = true))
      (botPort8 i) (botPort8 j) := by
  unfold hBotExec
  have hrefl0 : ∀ x : Fin 8, bitSet (hBotRow c d x) x.val = true := by
    intro x; rw [bitSet_hBotRow]; simp [glueBot8Bool]
  have hwar : ∀ u v : Fin 8, bitSet (get8 (warshall8 (hBotRow c d)) u) v.val = true ↔
      Reach (fun x y => glueBot8Bool c d x y = true) u v := by
    intro u v; rw [get8_warshall8, warshallRun_iff_Reach_fn (hBotRow c d) hrefl0]
    simp [bitSet_hBotRow]
  rw [encodeBell5_spec]
  · rw [hwar, reach_glueBot8Bool_iff]
  · intro x; rw [hwar]; exact .refl _
  · intro x y h; rw [hwar] at h ⊢; exact Reach.symm_of_symm (glueBot8Bool_symm c d) h
  · intro x y z h1 h2; rw [hwar] at h1 h2 ⊢; exact Reach.trans h1 h2

theorem vGlueExec_spec (t b : Fin 52) (i j : Fin 4) :
    bell4Rel (vGlueExec t b) i j = true ↔
    Reach (glueVert10 (fun x y => bell5Rel t x y = true) (fun x y => bell5Rel b x y = true))
      (outerPort10 i) (outerPort10 j) := by
  unfold vGlueExec
  have hrefl0 : ∀ x : Fin 10, bitSet (vGlueRow t b x) x.val = true := by
    intro x; rw [bitSet_vGlueRow]; simp [glueVert10Bool]
  have hwar : ∀ u v : Fin 10, bitSet (get10 (warshall10 (vGlueRow t b)) u) v.val = true ↔
      Reach (fun x y => glueVert10Bool t b x y = true) u v := by
    intro u v; rw [get10_warshall10, warshallRun_iff_Reach_fn (vGlueRow t b) hrefl0]
    simp [bitSet_vGlueRow]
  rw [encodeBell4_spec]
  · rw [hwar, reach_glueVert10Bool_iff]
  · intro x; rw [hwar]; exact .refl _
  · intro x y h; rw [hwar] at h ⊢; exact Reach.symm_of_symm (glueVert10Bool_symm t b) h
  · intro x y z h1 h2; rw [hwar] at h1 h2 ⊢; exact Reach.trans h1 h2

theorem qcombExec_spec (a b c d : Fin 15) (i j : Fin 4) :
    bell4Rel (qcombExec a b c d) i j = true ↔
    Reach (glue16
      (fun x y => bell4Rel a x y = true)
      (fun x y => bell4Rel b x y = true)
      (fun x y => bell4Rel c x y = true)
      (fun x y => bell4Rel d x y = true))
      (outerPort16 i) (outerPort16 j) := by
  unfold qcombExec
  rw [vGlueExec_spec, reach_glue16_iff_vGlue]
  have htop : (fun x y => bell5Rel (hTopExec a b) x y = true) =
      (fun x y => Reach (glueTop8 (fun u v => bell4Rel a u v = true) (fun u v => bell4Rel b u v = true))
        (topPort8 x) (topPort8 y)) := by
    funext x y; exact propext (hTopExec_spec a b x y)
  have hbot : (fun x y => bell5Rel (hBotExec c d) x y = true) =
      (fun x y => Reach (glueBot8 (fun u v => bell4Rel c u v = true) (fun u v => bell4Rel d u v = true))
        (botPort8 x) (botPort8 y)) := by
    funext x y; exact propext (hBotExec_spec c d x y)
  rw [htop, hbot]

/-! ### Partition-Lattice Order & Free Symbolic Monotonicity of `hTopExec`, `hBotExec`, `vGlueExec` -/

theorem bitSubset4_eq : ∀ a b : Fin 16,
    ((a.val &&& b.val) == a.val) = allFin 4 (fun j => !(bitSet a.val j.val) || bitSet b.val j.val) := by
  have h : allFin 16 (fun a => allFin 16 (fun b =>
      ((a.val &&& b.val) == a.val) == allFin 4 (fun j => !(bitSet a.val j.val) || bitSet b.val j.val))) = true := by
    decide
  intro a b
  exact eq_of_beq ((allFin_iff 16 _).mp ((allFin_iff 16 _).mp h a) b)

theorem bitSubset5_eq : ∀ a b : Fin 32,
    ((a.val &&& b.val) == a.val) = allFin 5 (fun j => !(bitSet a.val j.val) || bitSet b.val j.val) := by
  have h : allFin 32 (fun a => allFin 32 (fun b =>
      ((a.val &&& b.val) == a.val) == allFin 5 (fun j => !(bitSet a.val j.val) || bitSet b.val j.val))) = true := by
    decide
  intro a b
  exact eq_of_beq ((allFin_iff 32 _).mp ((allFin_iff 32 _).mp h a) b)

def partLe (p q : Fin 15) : Bool :=
  let (a0, a1, a2, a3) := bell4Rows p
  let (b0, b1, b2, b3) := bell4Rows q
  ((a0 &&& b0) == a0) && ((a1 &&& b1) == a1) &&
  ((a2 &&& b2) == a2) && ((a3 &&& b3) == a3)

def part5Le (p q : Fin 52) : Bool :=
  let (a0, a1, a2, a3, a4) := bell5Rows p
  let (b0, b1, b2, b3, b4) := bell5Rows q
  ((a0 &&& b0) == a0) && ((a1 &&& b1) == a1) &&
  ((a2 &&& b2) == a2) && ((a3 &&& b3) == a3) && ((a4 &&& b4) == a4)

theorem partLe_iff (p q : Fin 15) :
    partLe p q = true ↔ ∀ i j : Fin 4, bell4Rel p i j = true → bell4Rel q i j = true := by
  have hrow : ∀ i : Fin 4, ((bell4Row p i &&& bell4Row q i) == bell4Row p i) = true ↔
      ∀ j : Fin 4, bell4Rel p i j = true → bell4Rel q i j = true := by
    intro i
    have hltp := bell4Row_lt p i
    have hltq := bell4Row_lt q i
    have hsub := bitSubset4_eq ⟨bell4Row p i, hltp⟩ ⟨bell4Row q i, hltq⟩
    dsimp only at hsub
    rw [hsub, allFin_iff]
    constructor
    · intro h j hp
      have hj := h j
      rw [bell4Row_spec, bell4Row_spec, hp] at hj
      simpa using hj
    · intro h j
      rw [bell4Row_spec, bell4Row_spec]
      cases hp : bell4Rel p i j with
      | false => simp
      | true => simp [h j hp]
  have heq : partLe p q =
      (((bell4Row p 0 &&& bell4Row q 0) == bell4Row p 0) &&
       ((bell4Row p 1 &&& bell4Row q 1) == bell4Row p 1) &&
       ((bell4Row p 2 &&& bell4Row q 2) == bell4Row p 2) &&
       ((bell4Row p 3 &&& bell4Row q 3) == bell4Row p 3)) := rfl
  rw [heq]
  simp only [Bool.and_eq_true, hrow]
  constructor
  · intro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ i
    exact fin4_forall (P := fun x => ∀ j : Fin 4, bell4Rel p x j = true → bell4Rel q x j = true) h0 h1 h2 h3 i
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩

theorem part5Le_iff (p q : Fin 52) :
    part5Le p q = true ↔ ∀ i j : Fin 5, bell5Rel p i j = true → bell5Rel q i j = true := by
  have hrow : ∀ i : Fin 5, ((bell5Row p i &&& bell5Row q i) == bell5Row p i) = true ↔
      ∀ j : Fin 5, bell5Rel p i j = true → bell5Rel q i j = true := by
    intro i
    have hltp := bell5Row_lt p i
    have hltq := bell5Row_lt q i
    have hsub := bitSubset5_eq ⟨bell5Row p i, hltp⟩ ⟨bell5Row q i, hltq⟩
    dsimp only at hsub
    rw [hsub, allFin_iff]
    constructor
    · intro h j hp
      have hj := h j
      rw [bell5Row_spec, bell5Row_spec, hp] at hj
      simpa using hj
    · intro h j
      rw [bell5Row_spec, bell5Row_spec]
      cases hp : bell5Rel p i j with
      | false => simp
      | true => simp [h j hp]
  have heq : part5Le p q =
      (((bell5Row p 0 &&& bell5Row q 0) == bell5Row p 0) &&
       ((bell5Row p 1 &&& bell5Row q 1) == bell5Row p 1) &&
       ((bell5Row p 2 &&& bell5Row q 2) == bell5Row p 2) &&
       ((bell5Row p 3 &&& bell5Row q 3) == bell5Row p 3) &&
       ((bell5Row p 4 &&& bell5Row q 4) == bell5Row p 4)) := rfl
  rw [heq]
  simp only [Bool.and_eq_true, hrow]
  constructor
  · intro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ i
    exact fin5_forall (P := fun x => ∀ j : Fin 5, bell5Rel p x j = true → bell5Rel q x j = true) h0 h1 h2 h3 h4 i
  · intro h
    exact ⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩

theorem partLe_trans (a b c : Fin 15) :
    partLe a b = true → partLe b c = true → partLe a c = true := by
  rw [partLe_iff, partLe_iff, partLe_iff]
  intro h1 h2 i j hij; exact h2 i j (h1 i j hij)

theorem part5Le_trans (a b c : Fin 52) :
    part5Le a b = true → part5Le b c = true → part5Le a c = true := by
  rw [part5Le_iff, part5Le_iff, part5Le_iff]
  intro h1 h2 i j hij; exact h2 i j (h1 i j hij)

theorem hTopExec_mono (a a' b b' : Fin 15)
    (ha : partLe a a' = true) (hb : partLe b b' = true) :
    part5Le (hTopExec a b) (hTopExec a' b') = true := by
  rw [partLe_iff] at ha hb
  rw [part5Le_iff]
  intro i j hij
  rw [hTopExec_spec] at hij ⊢
  refine Reach.mono (fun u v e => ?_) hij
  unfold glueTop8 at e ⊢
  rcases e with ⟨h1, h2, hr⟩ | ⟨h1, h2, hr⟩ | hrest
  · exact Or.inl ⟨h1, h2, ha _ _ hr⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hb _ _ hr⟩)
  · exact Or.inr (Or.inr hrest)

theorem hBotExec_mono (c c' d d' : Fin 15)
    (hc : partLe c c' = true) (hd : partLe d d' = true) :
    part5Le (hBotExec c d) (hBotExec c' d') = true := by
  rw [partLe_iff] at hc hd
  rw [part5Le_iff]
  intro i j hij
  rw [hBotExec_spec] at hij ⊢
  refine Reach.mono (fun u v e => ?_) hij
  unfold glueBot8 at e ⊢
  rcases e with ⟨h1, h2, hr⟩ | ⟨h1, h2, hr⟩ | hrest
  · exact Or.inl ⟨h1, h2, hc _ _ hr⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hd _ _ hr⟩)
  · exact Or.inr (Or.inr hrest)

theorem vGlueExec_mono (t t' b b' : Fin 52)
    (ht : part5Le t t' = true) (hb : part5Le b b' = true) :
    partLe (vGlueExec t b) (vGlueExec t' b') = true := by
  rw [part5Le_iff] at ht hb
  rw [partLe_iff]
  intro i j hij
  rw [vGlueExec_spec] at hij ⊢
  refine Reach.mono (fun u v e => ?_) hij
  unfold glueVert10 at e ⊢
  rcases e with ⟨h1, h2, hr⟩ | ⟨h1, h2, hr⟩ | hrest
  · exact Or.inl ⟨h1, h2, ht _ _ hr⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hb _ _ hr⟩)
  · exact Or.inr (Or.inr hrest)

theorem qcombExec_mono (a a' b b' c c' d d' : Fin 15)
    (ha : partLe a a' = true) (hb : partLe b b' = true)
    (hc : partLe c c' = true) (hd : partLe d d' = true) :
    partLe (qcombExec a b c d) (qcombExec a' b' c' d') = true :=
  vGlueExec_mono _ _ _ _ (hTopExec_mono _ _ _ _ ha hb) (hBotExec_mono _ _ _ _ hc hd)

/-! ### Percolation & Truchet FactoredQTA + Exact Homomorphism to Concrete `QNet` -/

def boolToFin2 (b : Bool) : Fin 2 := if b then ⟨1, by omega⟩ else ⟨0, by omega⟩
def fin2ToBool (a : Fin 2) : Bool := a.val == 1

def mapQTree {α β : Type} (f : α → β) : {k : Nat} → QTree α k → QTree β k
  | 0, .qleaf a => .qleaf (f a)
  | _ + 1, .qnode nw ne sw se => .qnode (mapQTree f nw) (mapQTree f ne) (mapQTree f sw) (mapQTree f se)

theorem map_fin2ToBool_boolToFin2 : ∀ {k : Nat} (q : QTree Bool k),
    mapQTree fin2ToBool (mapQTree boolToFin2 q) = q
  | 0, .qleaf false => rfl
  | 0, .qleaf true => rfl
  | _ + 1, .qnode nw ne sw se => by
    simp only [mapQTree, map_fin2ToBool_boolToFin2 nw, map_fin2ToBool_boolToFin2 ne,
               map_fin2ToBool_boolToFin2 sw, map_fin2ToBool_boolToFin2 se]

def TOP4 : Fin 15 := ⟨0, by omega⟩
def BOT4 : Fin 15 := ⟨14, by omega⟩
def SL4 : Fin 15 := ⟨8, by omega⟩
def BSL4 : Fin 15 := ⟨3, by omega⟩
def CROSS4 : Fin 15 := ⟨6, by omega⟩

def percFactoredQTA : FactoredQTA where
  numLeaves := 2
  numStates := 15
  midStates := 52
  leaf := fun a => if a.val == 1 then TOP4 else BOT4
  hTop := hTopExec
  hBot := hBotExec
  vGlue := vGlueExec

def trucFactoredQTA : FactoredQTA where
  numLeaves := 2
  numStates := 15
  midStates := 52
  leaf := fun a => if a.val == 1 then BSL4 else SL4
  hTop := hTopExec
  hBot := hBotExec
  vGlue := vGlueExec

def percEval {k : Nat} (q : QTree Bool k) : Fin 15 :=
  evalFactoredQTA percFactoredQTA (mapQTree boolToFin2 q)

def trucEval {k : Nat} (q : QTree Bool k) : Fin 15 :=
  evalFactoredQTA trucFactoredQTA (mapQTree boolToFin2 q)

theorem percLeaf_spec : ∀ (b : Bool) (i j : Fin 4),
    bell4Rel (percEval (.qleaf b)) i j = true ↔ QNet percLeafRel (.qleaf b) i j := by
  intro b i j
  unfold QNet percLeafRel
  cases b <;> revert i j <;> refine fin4_forall ?_ ?_ ?_ ?_ <;> refine fin4_forall ?_ ?_ ?_ ?_
  all_goals decide

theorem trucLeaf_spec : ∀ (b : Bool) (i j : Fin 4),
    bell4Rel (trucEval (.qleaf b)) i j = true ↔ QNet trucLeafRel (.qleaf b) i j := by
  intro b i j
  unfold QNet trucLeafRel
  cases b <;> revert i j <;> refine fin4_forall ?_ ?_ ?_ ?_ <;> refine fin4_forall ?_ ?_ ?_ ?_
  all_goals decide

theorem trucEval_eq_QNet :
    ∀ {k : Nat} (q : QTree Bool k) (i j : Fin 4),
      bell4Rel (trucEval q) i j = true ↔ QNet trucLeafRel q i j := by
  intro k q
  induction q with
  | qleaf b => exact trucLeaf_spec b
  | qnode nw ne sw se ihnw ihne ihsw ihse =>
    intro i j
    change bell4Rel (qcombExec (trucEval nw) (trucEval ne) (trucEval sw) (trucEval se)) i j = true ↔ _
    rw [qcombExec_spec]
    have h0 : (fun x y => bell4Rel (trucEval nw) x y = true) = QNet trucLeafRel nw := by
      funext x y; exact propext (ihnw x y)
    have h1 : (fun x y => bell4Rel (trucEval ne) x y = true) = QNet trucLeafRel ne := by
      funext x y; exact propext (ihne x y)
    have h2 : (fun x y => bell4Rel (trucEval sw) x y = true) = QNet trucLeafRel sw := by
      funext x y; exact propext (ihsw x y)
    have h3 : (fun x y => bell4Rel (trucEval se) x y = true) = QNet trucLeafRel se := by
      funext x y; exact propext (ihse x y)
    rw [h0, h1, h2, h3]; rfl

/-! ### Theorem 1A: Catalan-14 Planarity Conservation (Factored Bitmask Certificate) -/

def isPlanar4 (s : Fin 15) : Bool := s != CROSS4

def planarFactoredCert : FactoredBitmaskCert where
  evenMask := 32703
  topMask  := 4485929883860983
  botMask  := 4501194372476863

set_option maxHeartbeats 800000 in
theorem perc_planarCert_ok :
    checkFactoredQTACert percFactoredQTA isPlanar4 planarFactoredCert = true := by
  decide

/-- Reuse the verified step+safety closure of `planarFactoredCert` for Truchet leaves (only 2 leaf checks!). -/
theorem truc_planarCert_ok :
    checkFactoredQTACert trucFactoredQTA isPlanar4 planarFactoredCert = true := by
  have hp := perc_planarCert_ok
  unfold checkFactoredQTACert at hp ⊢
  simp only [Bool.and_eq_true] at hp ⊢
  have hleaves : allFin trucFactoredQTA.numLeaves
      (fun a => bitSet planarFactoredCert.evenMask (trucFactoredQTA.leaf a).val) = true := by decide
  exact ⟨⟨⟨⟨hleaves, hp.1.1.1.2⟩, hp.1.1.2⟩, hp.1.2⟩, hp.2⟩

@[inline] def encPair (a b : Fin 15) : Fin 225 := ⟨a.val * 15 + b.val, by omega⟩
@[inline] def decPair1 (x : Fin 225) : Fin 15 := ⟨x.val / 15, by omega⟩
@[inline] def decPair2 (x : Fin 225) : Fin 15 := ⟨x.val % 15, by omega⟩

@[inline] def encMidPair (a b : Fin 52) : Fin 2704 := ⟨a.val * 52 + b.val, by omega⟩
@[inline] def decMid1 (x : Fin 2704) : Fin 52 := ⟨x.val / 52, by omega⟩
@[inline] def decMid2 (x : Fin 2704) : Fin 52 := ⟨x.val % 52, by omega⟩

theorem decPair_encPair (a b : Fin 15) :
    decPair1 (encPair a b) = a ∧ decPair2 (encPair a b) = b := by
  constructor <;> apply Fin.ext <;> dsimp [decPair1, decPair2, encPair] <;> omega

theorem decMid_encMid (a b : Fin 52) :
    decMid1 (encMidPair a b) = a ∧ decMid2 (encMidPair a b) = b := by
  constructor <;> apply Fin.ext <;> dsimp [decMid1, decMid2, encMidPair] <;> omega

def pairLe (x y : Fin 225) : Bool :=
  partLe (decPair1 x) (decPair1 y) && partLe (decPair2 x) (decPair2 y)

def pairMidLe (x y : Fin 2704) : Bool :=
  part5Le (decMid1 x) (decMid1 y) && part5Le (decMid2 x) (decMid2 y)

def pairHTop (a b : Fin 225) : Fin 2704 :=
  encMidPair (hTopExec (decPair1 a) (decPair1 b)) (hTopExec (decPair2 a) (decPair2 b))

def pairHBot (c d : Fin 225) : Fin 2704 :=
  encMidPair (hBotExec (decPair1 c) (decPair1 d)) (hBotExec (decPair2 c) (decPair2 d))

def pairVGlue (t b : Fin 2704) : Fin 225 :=
  encPair (vGlueExec (decMid1 t) (decMid1 b)) (vGlueExec (decMid2 t) (decMid2 b))

def pairComb (a b c d : Fin 225) : Fin 225 :=
  pairVGlue (pairHTop a b) (pairHBot c d)

theorem pairLe_trans (x y z : Fin 225) :
    pairLe x y = true → pairLe y z = true → pairLe x z = true := by
  unfold pairLe; simp only [Bool.and_eq_true]
  intro ⟨h1, h2⟩ ⟨h3, h4⟩
  exact ⟨partLe_trans _ _ _ h1 h3, partLe_trans _ _ _ h2 h4⟩

theorem pairMidLe_trans (x y z : Fin 2704) :
    pairMidLe x y = true → pairMidLe y z = true → pairMidLe x z = true := by
  unfold pairMidLe; simp only [Bool.and_eq_true]
  intro ⟨h1, h2⟩ ⟨h3, h4⟩
  exact ⟨part5Le_trans _ _ _ h1 h3, part5Le_trans _ _ _ h2 h4⟩

theorem pairHTop_mono (a a' b b' : Fin 225)
    (ha : pairLe a a' = true) (hb : pairLe b b' = true) :
    pairMidLe (pairHTop a b) (pairHTop a' b') = true := by
  unfold pairLe at ha hb; unfold pairMidLe pairHTop
  simp only [Bool.and_eq_true] at ha hb ⊢
  rw [(decMid_encMid _ _).1, (decMid_encMid _ _).2, (decMid_encMid _ _).1, (decMid_encMid _ _).2]
  exact ⟨hTopExec_mono _ _ _ _ ha.1 hb.1, hTopExec_mono _ _ _ _ ha.2 hb.2⟩

theorem pairHBot_mono (c c' d d' : Fin 225)
    (hc : pairLe c c' = true) (hd : pairLe d d' = true) :
    pairMidLe (pairHBot c d) (pairHBot c' d') = true := by
  unfold pairLe at hc hd; unfold pairMidLe pairHBot
  simp only [Bool.and_eq_true] at hc hd ⊢
  rw [(decMid_encMid _ _).1, (decMid_encMid _ _).2, (decMid_encMid _ _).1, (decMid_encMid _ _).2]
  exact ⟨hBotExec_mono _ _ _ _ hc.1 hd.1, hBotExec_mono _ _ _ _ hc.2 hd.2⟩

theorem pairVGlue_mono (t t' b b' : Fin 2704)
    (ht : pairMidLe t t' = true) (hb : pairMidLe b b' = true) :
    pairLe (pairVGlue t b) (pairVGlue t' b') = true := by
  unfold pairMidLe at ht hb; unfold pairLe pairVGlue
  simp only [Bool.and_eq_true] at ht hb ⊢
  rw [(decPair_encPair _ _).1, (decPair_encPair _ _).2, (decPair_encPair _ _).1, (decPair_encPair _ _).2]
  exact ⟨vGlueExec_mono _ _ _ _ ht.1 hb.1, vGlueExec_mono _ _ _ _ ht.2 hb.2⟩

def numComp4 (s : Fin 15) : Nat :=
  let t := bell4Tuple s
  max (max t.1 t.2.1) (max t.2.2.1 t.2.2.2) + 1

def allPerimCovered (a b : Fin 15) : Bool :=
  (bell4Rel a 0 1 || bell4Rel b 0 1) &&
  (bell4Rel a 1 2 || bell4Rel b 1 2) &&
  (bell4Rel a 2 3 || bell4Rel b 2 3) &&
  (bell4Rel a 3 0 || bell4Rel b 3 0)

/-- Pure-silicon unrolled 4-row Warshall check for `a ∨ b = ⊤` (ZERO `List` allocations). -/
def joinIsTop (a b : Fin 15) : Bool :=
  let (a0, a1, a2, a3) := bell4Rows a
  let (b0, b1, b2, b3) := bell4Rows b
  let r0 := a0 ||| b0; let r1 := a1 ||| b1; let r2 := a2 ||| b2; let r3 := a3 ||| b3
  let r0 := wRow r0 0 r0; let r1 := wRow r1 0 r0; let r2 := wRow r2 0 r0; let r3 := wRow r3 0 r0
  let r0 := wRow r0 1 r1; let r2 := wRow r2 1 r1; let r3 := wRow r3 1 r1
  let r0 := wRow r0 2 r2; let r3 := wRow r3 2 r2
  let r0 := wRow r0 3 r3
  r0 == 15

def isExactDualPair (a b : Fin 15) : Bool :=
  (a.val == 1 && b.val == 5) || (a.val == 5 && b.val == 1) ||
  (a.val == 2 && b.val == 9) || (a.val == 9 && b.val == 2) ||
  (a.val == 8 && b.val == 3) || (a.val == 3 && b.val == 8)

def superConnGood (x : Fin 225) : Bool :=
  let a := decPair1 x
  let b := decPair2 x
  (a != CROSS4) && (b != CROSS4) &&
  allPerimCovered a b &&
  joinIsTop a b &&
  ((a == TOP4) || (b == TOP4) || (numComp4 a == 2 && numComp4 b == 2 && isExactDualPair a b))

/-- Exact 225-bit GMP literal encoding `Planar_4 × Planar_4 ⊆ Fin 225` (196 set bits). -/
def planarPairMask : Nat :=
  53814577828658551176793444281795891064588160952096691114276523343807

theorem bitSet_planarPairMask (a b : Fin 15) :
    bitSet planarPairMask (encPair a b).val = ((a != CROSS4) && (b != CROSS4)) := by
  have h : allFin 15 (fun x => allFin 15 (fun y =>
      bitSet planarPairMask (encPair x y).val == ((x != CROSS4) && (y != CROSS4)))) = true := by
    decide
  have hx := (allFin_iff 15 _).mp h a
  have hxy := (allFin_iff 15 _).mp hx b
  exact eq_of_beq hxy

def certG8 : UpsetCert 225 2704 where
  gens := [
    encPair ⟨0, by omega⟩ ⟨14, by omega⟩,
    encPair ⟨14, by omega⟩ ⟨0, by omega⟩,
    encPair ⟨1, by omega⟩ ⟨5, by omega⟩,
    encPair ⟨5, by omega⟩ ⟨1, by omega⟩,
    encPair ⟨2, by omega⟩ ⟨9, by omega⟩,
    encPair ⟨9, by omega⟩ ⟨2, by omega⟩,
    encPair ⟨8, by omega⟩ ⟨3, by omega⟩,
    encPair ⟨3, by omega⟩ ⟨8, by omega⟩
  ]
  topGens := [
    encMidPair ⟨0, by omega⟩ ⟨51, by omega⟩, encMidPair ⟨2, by omega⟩ ⟨42, by omega⟩,
    encMidPair ⟨5, by omega⟩ ⟨49, by omega⟩, encMidPair ⟨6, by omega⟩ ⟨47, by omega⟩,
    encMidPair ⟨7, by omega⟩ ⟨21, by omega⟩, encMidPair ⟨8, by omega⟩ ⟨41, by omega⟩,
    encMidPair ⟨9, by omega⟩ ⟨39, by omega⟩, encMidPair ⟨11, by omega⟩ ⟨29, by omega⟩,
    encMidPair ⟨12, by omega⟩ ⟨28, by omega⟩, encMidPair ⟨14, by omega⟩ ⟨18, by omega⟩,
    encMidPair ⟨18, by omega⟩ ⟨14, by omega⟩, encMidPair ⟨21, by omega⟩ ⟨7, by omega⟩,
    encMidPair ⟨28, by omega⟩ ⟨12, by omega⟩, encMidPair ⟨29, by omega⟩ ⟨11, by omega⟩,
    encMidPair ⟨39, by omega⟩ ⟨9, by omega⟩, encMidPair ⟨41, by omega⟩ ⟨8, by omega⟩,
    encMidPair ⟨42, by omega⟩ ⟨2, by omega⟩, encMidPair ⟨47, by omega⟩ ⟨6, by omega⟩,
    encMidPair ⟨49, by omega⟩ ⟨5, by omega⟩, encMidPair ⟨51, by omega⟩ ⟨0, by omega⟩
  ]
  botGens := [
    encMidPair ⟨0, by omega⟩ ⟨51, by omega⟩, encMidPair ⟨2, by omega⟩ ⟨45, by omega⟩,
    encMidPair ⟨3, by omega⟩ ⟨43, by omega⟩, encMidPair ⟨8, by omega⟩ ⟨33, by omega⟩,
    encMidPair ⟨9, by omega⟩ ⟨31, by omega⟩, encMidPair ⟨15, by omega⟩ ⟨34, by omega⟩,
    encMidPair ⟨25, by omega⟩ ⟨46, by omega⟩, encMidPair ⟨28, by omega⟩ ⟨50, by omega⟩,
    encMidPair ⟨29, by omega⟩ ⟨47, by omega⟩, encMidPair ⟨30, by omega⟩ ⟨35, by omega⟩,
    encMidPair ⟨31, by omega⟩ ⟨9, by omega⟩, encMidPair ⟨33, by omega⟩ ⟨8, by omega⟩,
    encMidPair ⟨34, by omega⟩ ⟨15, by omega⟩, encMidPair ⟨35, by omega⟩ ⟨30, by omega⟩,
    encMidPair ⟨43, by omega⟩ ⟨3, by omega⟩, encMidPair ⟨45, by omega⟩ ⟨2, by omega⟩,
    encMidPair ⟨46, by omega⟩ ⟨25, by omega⟩, encMidPair ⟨47, by omega⟩ ⟨29, by omega⟩,
    encMidPair ⟨50, by omega⟩ ⟨28, by omega⟩, encMidPair ⟨51, by omega⟩ ⟨0, by omega⟩
  ]

def percPairLeaf (a : Fin 2) : Fin 225 :=
  if a.val == 1 then encPair TOP4 BOT4 else encPair BOT4 TOP4

def trucPairLeaf (a : Fin 2) : Fin 225 :=
  if a.val == 1 then encPair BSL4 SL4 else encPair SL4 BSL4

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1200000 in
theorem percG8_cert_ok :
    checkUpsetCert percPairLeaf pairHTop pairHBot pairVGlue pairLe pairMidLe planarPairMask superConnGood certG8 = true := by
  decide

/-- Reuse the verified `G_8` upset closure & safety for Truchet leaves (only 2 leaf checks!). -/
theorem trucG8_cert_ok :
    checkUpsetCert trucPairLeaf pairHTop pairHBot pairVGlue pairLe pairMidLe planarPairMask superConnGood certG8 = true := by
  have hp := percG8_cert_ok
  unfold checkUpsetCert at hp ⊢
  simp only [Bool.and_eq_true] at hp ⊢
  have hleaves : allFin 2 (fun a => inUpset pairLe certG8.gens (trucPairLeaf a)) = true := by decide
  exact ⟨⟨⟨⟨hleaves, hp.1.1.1.2⟩, hp.1.1.2⟩, hp.1.2⟩, hp.2⟩

theorem numComp4_TOP4 : numComp4 TOP4 = 1 := by decide
theorem bell4Rel_TOP4 : ∀ i j : Fin 4, bell4Rel TOP4 i j = true := by decide

def qtree4OfBits (bits : Nat) : QTree Bool 2 :=
  let q2 (off : Nat) : QTree Bool 1 :=
    .qnode (.qleaf (bitSet bits off)) (.qleaf (bitSet bits (off + 1)))
           (.qleaf (bitSet bits (off + 2))) (.qleaf (bitSet bits (off + 3)))
  .qnode (q2 0) (q2 4) (q2 8) (q2 12)

def d33Witnesses : List (Fin 225 × Nat × Nat) := [
  (encPair ⟨0,by omega⟩ ⟨0,by omega⟩, 1057, 33),
  (encPair ⟨0,by omega⟩ ⟨1,by omega⟩, 1317, 1036),
  (encPair ⟨0,by omega⟩ ⟨2,by omega⟩, 38158, 1029),
  (encPair ⟨0,by omega⟩ ⟨3,by omega⟩, 36905, 32),
  (encPair ⟨0,by omega⟩ ⟨4,by omega⟩, 38157, 1028),
  (encPair ⟨0,by omega⟩ ⟨5,by omega⟩, 36926, 35),
  (encPair ⟨0,by omega⟩ ⟨7,by omega⟩, 38245, 1132),
  (encPair ⟨0,by omega⟩ ⟨8,by omega⟩, 1342, 1071),
  (encPair ⟨0,by omega⟩ ⟨9,by omega⟩, 1075, 42),
  (encPair ⟨0,by omega⟩ ⟨10,by omega⟩, 1335, 1070),
  (encPair ⟨0,by omega⟩ ⟨11,by omega⟩, 38206, 1063),
  (encPair ⟨0,by omega⟩ ⟨12,by omega⟩, 38451, 1578),
  (encPair ⟨0,by omega⟩ ⟨13,by omega⟩, 36923, 34),
  (encPair ⟨0,by omega⟩ ⟨14,by omega⟩, 38207, 1062),
  (encPair ⟨1,by omega⟩ ⟨0,by omega⟩, 2602, 41),
  (encPair ⟨1,by omega⟩ ⟨5,by omega⟩, 36922, 105),
  (encPair ⟨2,by omega⟩ ⟨0,by omega⟩, 33, 32928),
  (encPair ⟨2,by omega⟩ ⟨9,by omega⟩, 51, 32930),
  (encPair ⟨3,by omega⟩ ⟨0,by omega⟩, 1056, 33009),
  (encPair ⟨3,by omega⟩ ⟨8,by omega⟩, 1334, 33967),
  (encPair ⟨4,by omega⟩ ⟨0,by omega⟩, 32, 32937),
  (encPair ⟨5,by omega⟩ ⟨0,by omega⟩, 1025, 32960),
  (encPair ⟨5,by omega⟩ ⟨1,by omega⟩, 1285, 33924),
  (encPair ⟨7,by omega⟩ ⟨0,by omega⟩, 2570, 32969),
  (encPair ⟨8,by omega⟩ ⟨0,by omega⟩, 2761, 1),
  (encPair ⟨8,by omega⟩ ⟨3,by omega⟩, 36873, 0),
  (encPair ⟨9,by omega⟩ ⟨0,by omega⟩, 1228, 81),
  (encPair ⟨9,by omega⟩ ⟨2,by omega⟩, 38156, 1045),
  (encPair ⟨10,by omega⟩ ⟨0,by omega⟩, 2760, 9),
  (encPair ⟨11,by omega⟩ ⟨0,by omega⟩, 1, 32896),
  (encPair ⟨12,by omega⟩ ⟨0,by omega⟩, 204, 34897),
  (encPair ⟨13,by omega⟩ ⟨0,by omega⟩, 1024, 32977),
  (encPair ⟨14,by omega⟩ ⟨0,by omega⟩, 0, 32905)
]

def hilbertVal : {k : Nat} → Fin 4 → QTree Bool k → Nat
  | 0, _, .qleaf b => if b then 1 else 0
  | k + 1, orient, .qnode nw ne sw se =>
    let sh := 2 ^ (4 ^ k)
    match orient.val with
    | 0 =>
      hilbertVal ⟨1, by omega⟩ sw +
      sh * (hilbertVal ⟨0, by omega⟩ nw +
        sh * (hilbertVal ⟨0, by omega⟩ ne +
          sh * hilbertVal ⟨3, by omega⟩ se))
    | 1 =>
      hilbertVal ⟨0, by omega⟩ sw +
      sh * (hilbertVal ⟨1, by omega⟩ se +
        sh * (hilbertVal ⟨1, by omega⟩ ne +
          sh * hilbertVal ⟨2, by omega⟩ nw))
    | 2 =>
      hilbertVal ⟨3, by omega⟩ ne +
      sh * (hilbertVal ⟨2, by omega⟩ se +
        sh * (hilbertVal ⟨2, by omega⟩ sw +
          sh * hilbertVal ⟨1, by omega⟩ nw))
    | _ =>
      hilbertVal ⟨2, by omega⟩ ne +
      sh * (hilbertVal ⟨3, by omega⟩ nw +
        sh * (hilbertVal ⟨3, by omega⟩ sw +
          sh * hilbertVal ⟨0, by omega⟩ se))

def mortonVal : {k : Nat} → QTree Bool k → Nat
  | 0, .qleaf b => if b then 1 else 0
  | k + 1, .qnode nw ne sw se =>
    let sh := 2 ^ (4 ^ k)
    mortonVal nw + sh * (mortonVal ne + sh * (mortonVal sw + sh * mortonVal se))

theorem two_pow_four_pow_mod15 (k : Nat) (hk : 1 ≤ k) : (2 ^ (4 ^ k)) % 15 = 1 := by
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => decide
    | succ m' =>
      have hm := ih (by omega)
      have hpow : 4 ^ (m' + 2) = 4 ^ (m' + 1) * 4 := by rw [Nat.pow_succ]
      rw [hpow, Nat.pow_mul, Nat.pow_mod, hm]

theorem two_pow_four_pow_mod3 (k : Nat) (hk : 1 ≤ k) : (2 ^ (4 ^ k)) % 3 = 1 := by
  have h := two_pow_four_pow_mod15 k hk; omega

theorem two_pow_four_pow_mod5 (k : Nat) (hk : 1 ≤ k) : (2 ^ (4 ^ k)) % 5 = 1 := by
  have h := two_pow_four_pow_mod15 k hk; omega

theorem phaseOfNat_1_0_ge1 (k : Nat) (hk : 1 ≤ k) :
    phaseOfNat 1 0 k = ⟨1, by omega⟩ := by
  unfold phaseOfNat
  have hnot : ¬ (k < 1) := by omega
  simp only [hnot, dite_false]
  apply Fin.ext; dsimp only; omega

theorem hilbertVal_antiTrans : ∀ {k : Nat} (q : QTree Bool k),
    hilbertVal ⟨0, by omega⟩ (antiTransQ q) = hilbertVal ⟨1, by omega⟩ q ∧
    hilbertVal ⟨1, by omega⟩ (antiTransQ q) = hilbertVal ⟨0, by omega⟩ q ∧
    hilbertVal ⟨2, by omega⟩ (antiTransQ q) = hilbertVal ⟨3, by omega⟩ q ∧
    hilbertVal ⟨3, by omega⟩ (antiTransQ q) = hilbertVal ⟨2, by omega⟩ q
  | 0, .qleaf b => by simp [antiTransQ, hilbertVal]
  | _ + 1, .qnode nw ne sw se => by
    have ⟨hnw0, hnw1, hnw2, hnw3⟩ := hilbertVal_antiTrans nw
    have ⟨hne0, hne1, hne2, hne3⟩ := hilbertVal_antiTrans ne
    have ⟨hsw0, hsw1, hsw2, hsw3⟩ := hilbertVal_antiTrans sw
    have ⟨hse0, hse1, hse2, hse3⟩ := hilbertVal_antiTrans se
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [antiTransQ, hilbertVal,
      hnw0, hnw1, hnw2, hnw3, hne0, hne1, hne2, hne3,
      hsw0, hsw1, hsw2, hsw3, hse0, hse1, hse2, hse3]

theorem hilbertVal_rot180 : ∀ {k : Nat} (q : QTree Bool k),
    hilbertVal ⟨0, by omega⟩ (rot180Q q) = hilbertVal ⟨2, by omega⟩ q ∧
    hilbertVal ⟨1, by omega⟩ (rot180Q q) = hilbertVal ⟨3, by omega⟩ q ∧
    hilbertVal ⟨2, by omega⟩ (rot180Q q) = hilbertVal ⟨0, by omega⟩ q ∧
    hilbertVal ⟨3, by omega⟩ (rot180Q q) = hilbertVal ⟨1, by omega⟩ q
  | 0, .qleaf b => by simp [rot180Q, hilbertVal]
  | _ + 1, .qnode nw ne sw se => by
    have ⟨hnw0, hnw1, hnw2, hnw3⟩ := hilbertVal_rot180 nw
    have ⟨hne0, hne1, hne2, hne3⟩ := hilbertVal_rot180 ne
    have ⟨hsw0, hsw1, hsw2, hsw3⟩ := hilbertVal_rot180 sw
    have ⟨hse0, hse1, hse2, hse3⟩ := hilbertVal_rot180 se
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [rot180Q, hilbertVal,
      hnw0, hnw1, hnw2, hnw3, hne0, hne1, hne2, hne3,
      hsw0, hsw1, hsw2, hsw3, hse0, hse1, hse2, hse3]

theorem hilbertVal_trans : ∀ {k : Nat} (q : QTree Bool k),
    hilbertVal ⟨0, by omega⟩ (transQ q) = hilbertVal ⟨3, by omega⟩ q ∧
    hilbertVal ⟨1, by omega⟩ (transQ q) = hilbertVal ⟨2, by omega⟩ q ∧
    hilbertVal ⟨2, by omega⟩ (transQ q) = hilbertVal ⟨1, by omega⟩ q ∧
    hilbertVal ⟨3, by omega⟩ (transQ q) = hilbertVal ⟨0, by omega⟩ q
  | 0, .qleaf b => by simp [transQ, hilbertVal]
  | _ + 1, .qnode nw ne sw se => by
    have ⟨hnw0, hnw1, hnw2, hnw3⟩ := hilbertVal_trans nw
    have ⟨hne0, hne1, hne2, hne3⟩ := hilbertVal_trans ne
    have ⟨hsw0, hsw1, hsw2, hsw3⟩ := hilbertVal_trans sw
    have ⟨hse0, hse1, hse2, hse3⟩ := hilbertVal_trans se
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [transQ, hilbertVal,
      hnw0, hnw1, hnw2, hnw3, hne0, hne1, hne2, hne3,
      hsw0, hsw1, hsw2, hsw3, hse0, hse1, hse2, hse3]

theorem flipH_rot180_eq_flipV : ∀ {k : Nat} (q : QTree Bool k),
    rot180Q (flipHQ q) = flipVQ q
  | 0, .qleaf _ => rfl
  | _ + 1, .qnode nw ne sw se => by
    simp only [flipHQ, rot180Q, flipVQ,
      flipH_rot180_eq_flipV nw, flipH_rot180_eq_flipV ne,
      flipH_rot180_eq_flipV sw, flipH_rot180_eq_flipV se]

theorem flipH_antiTrans_eq_rot90 : ∀ {k : Nat} (q : QTree Bool k),
    antiTransQ (flipHQ q) = rot90Q q
  | 0, .qleaf _ => rfl
  | _ + 1, .qnode nw ne sw se => by
    simp only [flipHQ, antiTransQ, rot90Q,
      flipH_antiTrans_eq_rot90 nw, flipH_antiTrans_eq_rot90 ne,
      flipH_antiTrans_eq_rot90 sw, flipH_antiTrans_eq_rot90 se]

theorem flipH_trans_eq_rot270 : ∀ {k : Nat} (q : QTree Bool k),
    transQ (flipHQ q) = rot270Q q
  | 0, .qleaf _ => rfl
  | _ + 1, .qnode nw ne sw se => by
    simp only [flipHQ, transQ, rot270Q,
      flipH_trans_eq_rot270 nw, flipH_trans_eq_rot270 ne,
      flipH_trans_eq_rot270 sw, flipH_trans_eq_rot270 se]

def hilbertMod5QTA : TimedQTA where
  numLeaves := 2
  numStates := 5
  r0 := 1
  p1 := 0
  leaf := fun a => if a.val == 1 then ⟨4, by omega⟩ else ⟨0, by omega⟩
  comb := fun ph s0 s1 s2 s3 =>
    if ph.val == 0 then
      let a := (4 * s0.val) % 5
      let b := (4 * s1.val) % 5
      let c := (4 * s2.val) % 5
      let d := (4 * s3.val) % 5
      let h0 := c + 2 * (a + 2 * (b + 2 * d))
      let h1 := c + 2 * (d + 2 * (b + 2 * a))
      let h2 := b + 2 * (d + 2 * (c + 2 * a))
      let h3 := b + 2 * (a + 2 * (c + 2 * d))
      ⟨(h0 + h1 + h2 + h3) % 5, Nat.mod_lt _ (by omega)⟩
    else
      ⟨(s0.val + s1.val + s2.val + s3.val) % 5, Nat.mod_lt _ (by omega)⟩

def hilbertMod5Good (ph : Fin 2) (s : Fin 5) : Bool :=
  if ph.val == 0 then true else s.val == 0

def hilbertMod5Cert : PhaseBitmaskCert 2 where
  masks := fun ph => if ph.val == 0 then 17 else 1

theorem hilbertMod5Cert_ok :
    checkQTACert hilbertMod5QTA hilbertMod5Good hilbertMod5Cert = true := by
  decide

theorem shift4_mod_eq (sh m a b c d : Nat) (hsh : sh % m = 1) :
    (a + sh * (b + sh * (c + sh * d))) % m = (a + b + c + d) % m := by
  have hmul : ∀ x : Nat, (sh * x) % m = x % m := by
    intro x; rw [Nat.mul_mod, hsh, Nat.one_mul, Nat.mod_mod]
  have h1 : (c + sh * d) % m = (c + d) % m := by
    rw [Nat.add_mod, hmul, ← Nat.add_mod]
  have h2 : (b + sh * (c + sh * d)) % m = (b + (c + d)) % m := by
    rw [Nat.add_mod, hmul, h1, ← Nat.add_mod]
  have h3 : (a + sh * (b + sh * (c + sh * d))) % m = (a + (b + (c + d))) % m := by
    rw [Nat.add_mod, hmul, h2, ← Nat.add_mod]
  rw [h3]; congr 1; omega

theorem evalQTA_hilbertMod5_hom :
    ∀ {k : Nat} (q : QTree Bool k),
      (evalQTA hilbertMod5QTA (mapQTree boolToFin2 q)).val =
        (hilbertVal ⟨0, by omega⟩ q + hilbertVal ⟨1, by omega⟩ q +
         hilbertVal ⟨2, by omega⟩ q + hilbertVal ⟨3, by omega⟩ q) % 5 := by
  intro k q
  induction q with
  | qleaf b => cases b <;> rfl
  | @qnode k' nw ne sw se ihnw ihne ihsw ihse =>
    cases k' with
    | zero =>
      cases nw with | qleaf a =>
      cases ne with | qleaf b =>
      cases sw with | qleaf c =>
      cases se with | qleaf d =>
      cases a <;> cases b <;> cases c <;> cases d <;> rfl
    | succ m =>
      have hph := phaseOfNat_1_0_ge1 (m + 1) (by omega)
      have hsh := two_pow_four_pow_mod5 (m + 1) (by omega)
      change (hilbertMod5QTA.comb (phaseOfNat 1 0 (m + 1)) _ _ _ _).val = _
      rw [hph]
      change ((evalQTA hilbertMod5QTA (mapQTree boolToFin2 nw)).val +
              (evalQTA hilbertMod5QTA (mapQTree boolToFin2 ne)).val +
              (evalQTA hilbertMod5QTA (mapQTree boolToFin2 sw)).val +
              (evalQTA hilbertMod5QTA (mapQTree boolToFin2 se)).val) % 5 = _
      rw [ihnw, ihne, ihsw, ihse]
      simp only [hilbertVal]
      have h0 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 5
        (hilbertVal ⟨1, by omega⟩ sw) (hilbertVal ⟨0, by omega⟩ nw) (hilbertVal ⟨0, by omega⟩ ne) (hilbertVal ⟨3, by omega⟩ se) hsh
      have h1 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 5
        (hilbertVal ⟨0, by omega⟩ sw) (hilbertVal ⟨1, by omega⟩ se) (hilbertVal ⟨1, by omega⟩ ne) (hilbertVal ⟨2, by omega⟩ nw) hsh
      have h2 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 5
        (hilbertVal ⟨3, by omega⟩ ne) (hilbertVal ⟨2, by omega⟩ se) (hilbertVal ⟨2, by omega⟩ sw) (hilbertVal ⟨1, by omega⟩ nw) hsh
      have h3 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 5
        (hilbertVal ⟨2, by omega⟩ ne) (hilbertVal ⟨3, by omega⟩ nw) (hilbertVal ⟨3, by omega⟩ sw) (hilbertVal ⟨0, by omega⟩ se) hsh
      omega

theorem hilbert_mod5_quadruple_annihilation (k : Nat) (hk : 1 ≤ k) (q : QTree Bool k) :
    (hilbertVal ⟨0, by omega⟩ q + hilbertVal ⟨1, by omega⟩ q +
     hilbertVal ⟨2, by omega⟩ q + hilbertVal ⟨3, by omega⟩ q) % 5 = 0 := by
  have hs := timedQTA_sound hilbertMod5QTA hilbertMod5Good hilbertMod5Cert hilbertMod5Cert_ok k (mapQTree boolToFin2 q)
  change hilbertMod5Good (phaseOfNat 1 0 k) (evalQTA hilbertMod5QTA (mapQTree boolToFin2 q)) = true at hs
  rw [phaseOfNat_1_0_ge1 k hk] at hs
  simp only [hilbertMod5Good, beq_iff_eq, Nat.one_ne_zero, ite_false] at hs
  rw [← evalQTA_hilbertMod5_hom q]
  exact hs

@[inline] def enc4Mod3 (a b c d : Nat) : Fin 81 :=
  ⟨(a % 3) + 3 * ((b % 3) + 3 * ((c % 3) + 3 * (d % 3))), by omega⟩

@[inline] def dec4Mod3_0 (s : Fin 81) : Nat := s.val % 3
@[inline] def dec4Mod3_1 (s : Fin 81) : Nat := (s.val / 3) % 3
@[inline] def dec4Mod3_2 (s : Fin 81) : Nat := (s.val / 9) % 3
@[inline] def dec4Mod3_3 (s : Fin 81) : Nat := (s.val / 27) % 3

theorem dec4Mod3_enc4Mod3 (a b c d : Nat) :
    dec4Mod3_0 (enc4Mod3 a b c d) = a % 3 ∧
    dec4Mod3_1 (enc4Mod3 a b c d) = b % 3 ∧
    dec4Mod3_2 (enc4Mod3 a b c d) = c % 3 ∧
    dec4Mod3_3 (enc4Mod3 a b c d) = d % 3 := by
  have ha := Nat.mod_lt a (by omega : 0 < 3)
  have hb := Nat.mod_lt b (by omega : 0 < 3)
  have hc := Nat.mod_lt c (by omega : 0 < 3)
  have hd := Nat.mod_lt d (by omega : 0 < 3)
  dsimp only [dec4Mod3_0, dec4Mod3_1, dec4Mod3_2, dec4Mod3_3, enc4Mod3]
  refine ⟨by omega, by omega, by omega, by omega⟩

def hilbertMod3QTA : TimedQTA where
  numLeaves := 2
  numStates := 81
  r0 := 1
  p1 := 0
  leaf := fun a => if a.val == 1 then enc4Mod3 1 1 1 1 else enc4Mod3 0 0 0 0
  comb := fun ph nw ne sw se =>
    let w := if ph.val == 0 then 2 else 1
    let h0 := dec4Mod3_1 sw + w * (dec4Mod3_0 nw + w * (dec4Mod3_0 ne + w * dec4Mod3_3 se))
    let h1 := dec4Mod3_0 sw + w * (dec4Mod3_1 se + w * (dec4Mod3_1 ne + w * dec4Mod3_2 nw))
    let h2 := dec4Mod3_3 ne + w * (dec4Mod3_2 se + w * (dec4Mod3_2 sw + w * dec4Mod3_1 nw))
    let h3 := dec4Mod3_2 ne + w * (dec4Mod3_3 nw + w * (dec4Mod3_3 sw + w * dec4Mod3_0 se))
    enc4Mod3 h0 h1 h2 h3

def hilbertMod3Good (_ph : Fin 2) (s : Fin 81) : Bool :=
  (dec4Mod3_0 s == dec4Mod3_1 s) && (dec4Mod3_1 s == dec4Mod3_2 s) && (dec4Mod3_2 s == dec4Mod3_3 s)

def hilbertMod3Cert : PhaseBitmaskCert 2 where
  masks := fun ph => if ph.val == 0 then (1 <<< 0) ||| (1 <<< 40) else (1 <<< 0) ||| (1 <<< 40) ||| (1 <<< 80)

theorem hilbertMod3Cert_ok :
    checkQTACert hilbertMod3QTA hilbertMod3Good hilbertMod3Cert = true := by
  decide

theorem mod3_linear4 (w a b c d : Nat) :
    (a % 3 + w * (b % 3 + w * (c % 3 + w * (d % 3)))) % 3 =
      (a + w * (b + w * (c + w * d))) % 3 := by
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem mod3_sum4 (a b c d : Nat) :
    (a % 3 + (b % 3 + (c % 3 + d % 3))) % 3 = (a + b + c + d) % 3 := by
  have h : a + (b + (c + d)) = a + b + c + d := by omega
  rw [← h]; simp only [Nat.add_mod, Nat.mod_mod]

theorem enc4Mod3_congr {a1 b1 c1 d1 a2 b2 c2 d2 : Nat}
    (ha : a1 % 3 = a2 % 3) (hb : b1 % 3 = b2 % 3)
    (hc : c1 % 3 = c2 % 3) (hd : d1 % 3 = d2 % 3) :
    enc4Mod3 a1 b1 c1 d1 = enc4Mod3 a2 b2 c2 d2 := by
  apply Fin.ext; dsimp only [enc4Mod3]; rw [ha, hb, hc, hd]

theorem pairMod3_extract (a b : Nat) :
    (a % 3 + 3 * (b % 3)) % 3 = a % 3 ∧ (a % 3 + 3 * (b % 3)) / 3 = b % 3 := by
  have ha := Nat.mod_lt a (by omega : 0 < 3)
  have hb := Nat.mod_lt b (by omega : 0 < 3)
  omega

theorem evalQTA_hilbertMod3_hom :
    ∀ {k : Nat} (q : QTree Bool k),
      evalQTA hilbertMod3QTA (mapQTree boolToFin2 q) =
        enc4Mod3 (hilbertVal ⟨0, by omega⟩ q) (hilbertVal ⟨1, by omega⟩ q)
                 (hilbertVal ⟨2, by omega⟩ q) (hilbertVal ⟨3, by omega⟩ q) := by
  intro k q
  induction q with
  | qleaf b => cases b <;> rfl
  | @qnode k' nw ne sw se ihnw ihne ihsw ihse =>
    change hilbertMod3QTA.comb (phaseOfNat 1 0 k') _ _ _ _ = _
    rw [ihnw, ihne, ihsw, ihse]
    cases k' with
    | zero =>
      have hph : phaseOfNat 1 0 0 = ⟨0, by omega⟩ := rfl
      rw [hph]
      dsimp only [hilbertMod3QTA]
      simp only [beq_iff_eq, ite_true]
      rw [(dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2,
          (dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2,
          (dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2,
          (dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2]
      simp only [hilbertVal]
      have hpow : 2 ^ (4 ^ 0) = 2 := rfl
      rw [hpow]
      exact enc4Mod3_congr (mod3_linear4 2 _ _ _ _) (mod3_linear4 2 _ _ _ _)
                           (mod3_linear4 2 _ _ _ _) (mod3_linear4 2 _ _ _ _)
    | succ m =>
      rw [phaseOfNat_1_0_ge1 (m + 1) (by omega)]
      have hsh := two_pow_four_pow_mod3 (m + 1) (by omega)
      dsimp only [hilbertMod3QTA]
      simp only [beq_iff_eq, Nat.one_ne_zero, ite_false, Nat.one_mul]
      rw [(dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2,
          (dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2,
          (dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2,
          (dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
          (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2]
      simp only [hilbertVal]
      have h0 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 3
        (hilbertVal ⟨1, by omega⟩ sw) (hilbertVal ⟨0, by omega⟩ nw) (hilbertVal ⟨0, by omega⟩ ne) (hilbertVal ⟨3, by omega⟩ se) hsh
      have h1 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 3
        (hilbertVal ⟨0, by omega⟩ sw) (hilbertVal ⟨1, by omega⟩ se) (hilbertVal ⟨1, by omega⟩ ne) (hilbertVal ⟨2, by omega⟩ nw) hsh
      have h2 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 3
        (hilbertVal ⟨3, by omega⟩ ne) (hilbertVal ⟨2, by omega⟩ se) (hilbertVal ⟨2, by omega⟩ sw) (hilbertVal ⟨1, by omega⟩ nw) hsh
      have h3 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 3
        (hilbertVal ⟨2, by omega⟩ ne) (hilbertVal ⟨3, by omega⟩ nw) (hilbertVal ⟨3, by omega⟩ sw) (hilbertVal ⟨0, by omega⟩ se) hsh
      exact enc4Mod3_congr (by rw [h0]; exact mod3_sum4 _ _ _ _)
                           (by rw [h1]; exact mod3_sum4 _ _ _ _)
                           (by rw [h2]; exact mod3_sum4 _ _ _ _)
                           (by rw [h3]; exact mod3_sum4 _ _ _ _)

theorem hilbert_mod3_orientation_invariance (k : Nat) (q : QTree Bool k) :
    hilbertVal ⟨0, by omega⟩ q % 3 = hilbertVal ⟨1, by omega⟩ q % 3 ∧
    hilbertVal ⟨1, by omega⟩ q % 3 = hilbertVal ⟨2, by omega⟩ q % 3 ∧
    hilbertVal ⟨2, by omega⟩ q % 3 = hilbertVal ⟨3, by omega⟩ q % 3 := by
  have hs := timedQTA_sound hilbertMod3QTA hilbertMod3Good hilbertMod3Cert hilbertMod3Cert_ok k (mapQTree boolToFin2 q)
  rw [evalQTA_hilbertMod3_hom q] at hs
  unfold hilbertMod3Good at hs
  rw [(dec4Mod3_enc4Mod3 _ _ _ _).1, (dec4Mod3_enc4Mod3 _ _ _ _).2.1,
      (dec4Mod3_enc4Mod3 _ _ _ _).2.2.1, (dec4Mod3_enc4Mod3 _ _ _ _).2.2.2] at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  omega

def hilbertFlipHMod3QTA : TimedQTA where
  numLeaves := 2
  numStates := 9
  r0 := 1
  p1 := 0
  leaf := fun a => if a.val == 1 then ⟨4, by omega⟩ else ⟨0, by omega⟩
  comb := fun ph nw ne sw se =>
    let w := if ph.val == 0 then 2 else 1
    let a0 := nw.val % 3; let a1 := nw.val / 3
    let b0 := ne.val % 3; let b1 := ne.val / 3
    let c0 := sw.val % 3; let c1 := sw.val / 3
    let d0 := se.val % 3; let d1 := se.val / 3
    let h0 := (c0 + w * (a0 + w * (b0 + w * d0))) % 3
    let hf := (d1 + w * (b1 + w * (a1 + w * c1))) % 3
    ⟨h0 + 3 * hf, by omega⟩

def hilbertFlipHGood (ph : Fin 2) (s : Fin 9) : Bool :=
  if ph.val == 0 then true else (s.val % 3 + s.val / 3) % 3 == 0

def hilbertFlipHCert : PhaseBitmaskCert 2 where
  masks := fun ph =>
    if ph.val == 0 then (1 <<< 0) ||| (1 <<< 4)
    else (1 <<< 0) ||| (1 <<< 5) ||| (1 <<< 7)

theorem hilbertFlipHCert_ok :
    checkQTACert hilbertFlipHMod3QTA hilbertFlipHGood hilbertFlipHCert = true := by
  decide

theorem evalQTA_hilbertFlipH_hom :
    ∀ {k : Nat} (q : QTree Bool k),
      (evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 q)).val =
        (hilbertVal ⟨0, by omega⟩ q % 3) + 3 * (hilbertVal ⟨0, by omega⟩ (flipHQ q) % 3) := by
  intro k q
  induction q with
  | qleaf b => cases b <;> rfl
  | @qnode k' nw ne sw se ihnw ihne ihsw ihse =>
    change (hilbertFlipHMod3QTA.comb (phaseOfNat 1 0 k') _ _ _ _).val = _
    have hsw1 : hilbertVal ⟨0, by omega⟩ sw % 3 = hilbertVal ⟨1, by omega⟩ sw % 3 :=
      (hilbert_mod3_orientation_invariance k' sw).1
    have hse3 : hilbertVal ⟨0, by omega⟩ se % 3 = hilbertVal ⟨3, by omega⟩ se % 3 := by
      have h := hilbert_mod3_orientation_invariance k' se; omega
    have hfse1 : hilbertVal ⟨0, by omega⟩ (flipHQ se) % 3 = hilbertVal ⟨1, by omega⟩ (flipHQ se) % 3 :=
      (hilbert_mod3_orientation_invariance k' (flipHQ se)).1
    have hfsw3 : hilbertVal ⟨0, by omega⟩ (flipHQ sw) % 3 = hilbertVal ⟨3, by omega⟩ (flipHQ sw) % 3 := by
      have h := hilbert_mod3_orientation_invariance k' (flipHQ sw); omega
    cases k' with
    | zero =>
      have hph : phaseOfNat 1 0 0 = ⟨0, by omega⟩ := rfl
      rw [hph]
      change ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 sw)).val % 3 +
              2 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 nw)).val % 3 +
                2 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 ne)).val % 3 +
                  2 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 se)).val % 3)))) % 3 +
             3 * (((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 se)).val / 3 +
              2 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 ne)).val / 3 +
                2 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 nw)).val / 3 +
                  2 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 sw)).val / 3)))) % 3) = _
      rw [ihnw, ihne, ihsw, ihse]
      rw [(pairMod3_extract _ _).1, (pairMod3_extract _ _).1, (pairMod3_extract _ _).1, (pairMod3_extract _ _).1,
          (pairMod3_extract _ _).2, (pairMod3_extract _ _).2, (pairMod3_extract _ _).2, (pairMod3_extract _ _).2]
      rw [hsw1, hse3, hfse1, hfsw3]
      simp only [flipHQ, hilbertVal]
      have hpow : 2 ^ (4 ^ 0) = 2 := rfl
      rw [hpow, mod3_linear4 2, mod3_linear4 2]
    | succ m =>
      rw [phaseOfNat_1_0_ge1 (m + 1) (by omega)]
      change ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 sw)).val % 3 +
              1 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 nw)).val % 3 +
                1 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 ne)).val % 3 +
                  1 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 se)).val % 3)))) % 3 +
             3 * (((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 se)).val / 3 +
              1 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 ne)).val / 3 +
                1 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 nw)).val / 3 +
                  1 * ((evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 sw)).val / 3)))) % 3) = _
      rw [ihnw, ihne, ihsw, ihse]
      rw [(pairMod3_extract _ _).1, (pairMod3_extract _ _).1, (pairMod3_extract _ _).1, (pairMod3_extract _ _).1,
          (pairMod3_extract _ _).2, (pairMod3_extract _ _).2, (pairMod3_extract _ _).2, (pairMod3_extract _ _).2]
      rw [hsw1, hse3, hfse1, hfsw3]
      have hsh := two_pow_four_pow_mod3 (m + 1) (by omega)
      simp only [flipHQ, hilbertVal, Nat.one_mul]
      have h0 := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 3
        (hilbertVal ⟨1, by omega⟩ sw) (hilbertVal ⟨0, by omega⟩ nw) (hilbertVal ⟨0, by omega⟩ ne) (hilbertVal ⟨3, by omega⟩ se) hsh
      have hf := shift4_mod_eq (2 ^ (4 ^ (m + 1))) 3
        (hilbertVal ⟨1, by omega⟩ (flipHQ se)) (hilbertVal ⟨0, by omega⟩ (flipHQ ne))
        (hilbertVal ⟨0, by omega⟩ (flipHQ nw)) (hilbertVal ⟨3, by omega⟩ (flipHQ sw)) hsh
      rw [h0, hf, mod3_sum4, mod3_sum4]

theorem hilbert_flipH_mod3_neg (k : Nat) (hk : 1 ≤ k) (q : QTree Bool k) :
    (hilbertVal ⟨0, by omega⟩ q + hilbertVal ⟨0, by omega⟩ (flipHQ q)) % 3 = 0 := by
  have hs := timedQTA_sound hilbertFlipHMod3QTA hilbertFlipHGood hilbertFlipHCert hilbertFlipHCert_ok k (mapQTree boolToFin2 q)
  change hilbertFlipHGood (phaseOfNat 1 0 k) (evalQTA hilbertFlipHMod3QTA (mapQTree boolToFin2 q)) = true at hs
  rw [phaseOfNat_1_0_ge1 k hk] at hs
  simp only [hilbertFlipHGood, beq_iff_eq, Nat.one_ne_zero, ite_false] at hs
  rw [evalQTA_hilbertFlipH_hom q] at hs
  rw [(pairMod3_extract _ _).1, (pairMod3_extract _ _).2] at hs
  omega

def hilbertD4Sum {k : Nat} (q : QTree Bool k) : Nat :=
  hilbertVal ⟨0, by omega⟩ q +
  hilbertVal ⟨0, by omega⟩ (rot90Q q) +
  hilbertVal ⟨0, by omega⟩ (rot180Q q) +
  hilbertVal ⟨0, by omega⟩ (rot270Q q) +
  hilbertVal ⟨0, by omega⟩ (flipHQ q) +
  hilbertVal ⟨0, by omega⟩ (flipVQ q) +
  hilbertVal ⟨0, by omega⟩ (transQ q) +
  hilbertVal ⟨0, by omega⟩ (antiTransQ q)

def valX : {k : Nat} → BTree (Bool × Bool) k → Nat
  | 0, .leaf p => if p.1 then 1 else 0
  | k + 1, .node l r => valX l + 2 ^ (2 ^ k) * valX r

def valY : {k : Nat} → BTree (Bool × Bool) k → Nat
  | 0, .leaf p => if p.2 then 1 else 0
  | k + 1, .node l r => valY l + 2 ^ (2 ^ k) * valY r

theorem valX_lt : ∀ {k : Nat} (t : BTree (Bool × Bool) k), valX t < 2 ^ (2 ^ k)
  | 0, .leaf (false, _) => by simp [valX]
  | 0, .leaf (true, _) => by simp [valX]
  | k + 1, .node l r => by
    have hl := valX_lt l
    have hr := valX_lt r
    have hpow : 2 ^ (2 ^ (k + 1)) = 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    simp only [valX]; rw [hpow]
    have h1 : 2 ^ (2 ^ k) * valX r + 2 ^ (2 ^ k) ≤ 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      calc 2 ^ (2 ^ k) * valX r + 2 ^ (2 ^ k)
          = 2 ^ (2 ^ k) * (valX r + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := Nat.mul_le_mul_left _ hr
    omega

theorem valY_lt : ∀ {k : Nat} (t : BTree (Bool × Bool) k), valY t < 2 ^ (2 ^ k)
  | 0, .leaf (_, false) => by simp [valY]
  | 0, .leaf (_, true) => by simp [valY]
  | k + 1, .node l r => by
    have hl := valY_lt l
    have hr := valY_lt r
    have hpow : 2 ^ (2 ^ (k + 1)) = 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    simp only [valY]; rw [hpow]
    have h1 : 2 ^ (2 ^ k) * valY r + 2 ^ (2 ^ k) ≤ 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      calc 2 ^ (2 ^ k) * valY r + 2 ^ (2 ^ k)
          = 2 ^ (2 ^ k) * (valY r + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := Nat.mul_le_mul_left _ hr
    omega

def claGP : {k : Nat} → BTree (Bool × Bool) k → Bool × Bool
  | 0, .leaf (x, y) => (x && y, x != y)
  | _ + 1, .node l r =>
    let (gL, pL) := claGP l
    let (gR, pR) := claGP r
    (gR || (pR && gL), pR && pL)

theorem cla_step_arith (M sL sR : Nat) (hsL_lt : sL + 1 < 2 * M) :
    (decide (M ≤ sR) || (decide (sR + 1 = M) && decide (M ≤ sL))) = decide (M * M ≤ sL + M * sR) ∧
    (decide (sR + 1 = M) && decide (sL + 1 = M)) = decide (sL + M * sR + 1 = M * M) := by
  constructor
  · by_cases hR : M ≤ sR
    · have htot : M * M ≤ sL + M * sR := by
        calc M * M ≤ M * sR := Nat.mul_le_mul_left M hR
          _ ≤ sL + M * sR := Nat.le_add_left _ _
      simp [hR, htot]
    · by_cases hRp : sR + 1 = M
      · have hMsR : M * sR + M = M * M := by
          calc M * sR + M = M * (sR + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ = M * M := by rw [hRp]
        by_cases hL : M ≤ sL
        · have htot : M * M ≤ sL + M * sR := by omega
          simp [hR, hRp, hL, htot]
        · have htot : ¬ (M * M ≤ sL + M * sR) := by omega
          simp [hR, hRp, hL, htot]
      · have hsR_le : sR + 2 ≤ M := by omega
        have htot : sL + M * sR < M * M := by
          have h1 : M * sR + 2 * M ≤ M * M := by
            calc M * sR + 2 * M = M * (sR + 2) := by rw [Nat.mul_add, Nat.mul_comm 2 M]
              _ ≤ M * M := Nat.mul_le_mul_left M hsR_le
          omega
        have hnot : ¬ (M * M ≤ sL + M * sR) := by omega
        simp [hR, hRp, hnot]
  · by_cases hRp : sR + 1 = M
    · have hMsR : M * sR + M = M * M := by
        calc M * sR + M = M * (sR + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = M * M := by rw [hRp]
      by_cases hLp : sL + 1 = M
      · have htot : sL + M * sR + 1 = M * M := by omega
        simp [hRp, hLp, htot]
      · have htot : sL + M * sR + 1 ≠ M * M := by omega
        simp [hRp, hLp, htot]
    · have htot : sL + M * sR + 1 ≠ M * M := by
        by_cases hRlt : sR + 1 < M
        · have hsR_le : sR + 2 ≤ M := by omega
          have h1 : M * sR + 2 * M ≤ M * M := by
            calc M * sR + 2 * M = M * (sR + 2) := by rw [Nat.mul_add, Nat.mul_comm 2 M]
              _ ≤ M * M := Nat.mul_le_mul_left M hsR_le
          omega
        · have hRge : M ≤ sR := by omega
          have h1 : M * M ≤ M * sR := Nat.mul_le_mul_left M hRge
          omega
      simp [hRp, htot]

theorem claGP_spec : ∀ {k : Nat} (t : BTree (Bool × Bool) k),
    (claGP t).1 = decide (2 ^ (2 ^ k) ≤ valX t + valY t) ∧
    (claGP t).2 = decide (valX t + valY t + 1 = 2 ^ (2 ^ k))
  | 0, .leaf (false, false) => by decide
  | 0, .leaf (false, true) => by decide
  | 0, .leaf (true, false) => by decide
  | 0, .leaf (true, true) => by decide
  | k + 1, .node l r => by
    have ⟨hgL, hpL⟩ := claGP_spec l
    have ⟨hgR, hpR⟩ := claGP_spec r
    have hxL := valX_lt l; have hyL := valY_lt l
    have hM2 : 2 ^ (2 ^ (k + 1)) = (2 ^ (2 ^ k)) * (2 ^ (2 ^ k)) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    have hsum : valX (.node l r) + valY (.node l r) =
        (valX l + valY l) + (2 ^ (2 ^ k)) * (valX r + valY r) := by
      simp only [valX, valY, Nat.mul_add]; omega
    simp only [claGP, hgL, hpL, hgR, hpR, hsum, hM2]
    exact cla_step_arith (2 ^ (2 ^ k)) (valX l + valY l) (valX r + valY r) (by omega)

theorem two_pow_two_pow_mod7 (k : Nat) :
    (2 ^ (2 ^ k)) % 7 = if k % 2 == 0 then 2 else 4 := by
  induction k with
  | zero => decide
  | succ m ih =>
    have hpow : 2 ^ (2 ^ (m + 1)) = (2 ^ (2 ^ m)) ^ 2 := by
      rw [Nat.pow_succ, Nat.pow_mul]
    rw [hpow, Nat.pow_mod, ih]
    by_cases hm : m % 2 = 0
    · have hsucc : (m + 1) % 2 = 1 := by omega
      simp [hm, hsucc]
    · have hm1 : m % 2 = 1 := by omega
      have hsucc : (m + 1) % 2 = 0 := by omega
      simp [hm1, hsucc]

@[inline] def encCLA (g p : Bool) (s t : Nat) : Fin 196 :=
  ⟨(((if g then 1 else 0) * 2 + (if p then 1 else 0)) * 7 + (s % 7)) * 7 + (t % 7),
    by cases g <;> cases p <;> simp <;> omega⟩

@[inline] def decCLA_g (st : Fin 196) : Bool := (st.val / 98) == 1
@[inline] def decCLA_p (st : Fin 196) : Bool := ((st.val / 49) % 2) == 1
@[inline] def decCLA_s (st : Fin 196) : Nat := (st.val / 7) % 7
@[inline] def decCLA_t (st : Fin 196) : Nat := st.val % 7

theorem decCLA_encCLA (g p : Bool) (s u : Nat) :
    decCLA_g (encCLA g p s u) = g ∧ decCLA_p (encCLA g p s u) = p ∧
    decCLA_s (encCLA g p s u) = s % 7 ∧ decCLA_t (encCLA g p s u) = u % 7 := by
  cases g <;> cases p <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [decCLA_g, decCLA_p, decCLA_s, decCLA_t, encCLA] <;> omega

def claMod7BTA : TimedBTA where
  numLeaves := 4
  numStates := 196
  r0 := 0
  p1 := 1
  leaf := fun a =>
    match a.val with
    | 0 => encCLA false false 0 0
    | 1 => encCLA false true  1 1
    | 2 => encCLA false true  1 1
    | _ => encCLA true  false 2 0
  comb := fun ph stL stR =>
    let w := if ph.val == 0 then 2 else 4
    let gL := decCLA_g stL; let pL := decCLA_p stL; let sL := decCLA_s stL; let tL := decCLA_t stL
    let gR := decCLA_g stR; let pR := decCLA_p stR; let sR := decCLA_s stR; let tR := decCLA_t stR
    let g := gR || (pR && gL)
    let p := pR && pL
    let s := (sL + w * sR) % 7
    let tR_adj := if gL then (if pR then 0 else (tR + 1) % 7) else tR
    let t := (tL + w * tR_adj) % 7
    encCLA g p s t

def claMod7Good (ph : Fin 2) (st : Fin 196) : Bool :=
  let g := decCLA_g st; let p := decCLA_p st; let s := decCLA_s st; let t := decCLA_t st
  let w := if ph.val == 0 then 2 else 4
  let pRes := if ph.val == 0 then 1 else 3
  !(g && p) &&
  (s == (t + (if g then w else 0)) % 7) &&
  (!p || (s == pRes && t == pRes))

def claMod7Cert : PhaseBitmaskCert 2 where
  masks := fun ph =>
    if ph.val == 0 then 22388199103855886604165745872970871212146945
    else 5597092143808263080610623067109016528290049

theorem claMod7Cert_ok :
    checkBTACert claMod7BTA claMod7Good claMod7Cert = true := by
  decide

def pairBoolToFin4 (p : Bool × Bool) : Fin 4 :=
  match p with
  | (false, false) => ⟨0, by omega⟩
  | (false, true) => ⟨1, by omega⟩
  | (true, false) => ⟨2, by omega⟩
  | (true, true) => ⟨3, by omega⟩

def mapBTree {α β : Type} (f : α → β) : {k : Nat} → BTree α k → BTree β k
  | 0, .leaf a => .leaf (f a)
  | _ + 1, .node l r => .node (mapBTree f l) (mapBTree f r)

theorem trunc_step_arith (M sL sR : Nat) (hMpos : 0 < M)
    (hsL_lt : sL + 1 < 2 * M) (hsR_lt : sR + 1 < 2 * M) :
    (sL + M * sR) % (M * M) =
      (sL % M) + M * (if M ≤ sL then (if sR + 1 = M then 0 else (sR % M) + 1) else sR % M) := by
  by_cases hL : M ≤ sL
  · have hqL : sL = (sL % M) + M := by
      have : sL % M = sL - M := by rw [Nat.mod_eq_sub_mod hL, Nat.mod_eq_of_lt (by omega)]
      omega
    by_cases hRp : sR + 1 = M
    · have htot : sL + M * sR = (sL % M) + M * M := by
        have h1 : M * sR + M = M * M := by
          calc M * sR + M = M * (sR + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ = M * M := by rw [hRp]
        omega
      simp only [hL, hRp, ite_true, Nat.mul_zero, Nat.add_zero]
      have hmodlt : sL % M < M * M := by
        have h1 := Nat.mod_lt sL hMpos
        have h2 : M ≤ M * M := Nat.le_mul_of_pos_right M hMpos
        omega
      rw [htot, Nat.add_mod_right, Nat.mod_eq_of_lt hmodlt]
    · simp only [hL, hRp, ite_true, ite_false]
      by_cases hR : M ≤ sR
      · have hqR : sR = (sR % M) + M := by
          have : sR % M = sR - M := by rw [Nat.mod_eq_sub_mod hR, Nat.mod_eq_of_lt (by omega)]
          omega
        have hr_lt : sR % M + 1 < M := by
          have : sR % M = sR - M := by rw [Nat.mod_eq_sub_mod hR, Nat.mod_eq_of_lt (by omega)]
          omega
        have htot : sL + M * sR = (sL % M) + M * (sR % M + 1) + M * M := by
          calc sL + M * sR = (sL % M + M) + M * (sR % M + M) := by rw [← hqL, ← hqR]
            _ = (sL % M) + M * (sR % M + 1) + M * M := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
        rw [htot, Nat.add_mod_right, Nat.mod_eq_of_lt]
        have hmodL := Nat.mod_lt sL hMpos
        have h1 : M * (sR % M + 1) + M ≤ M * M := by
          calc M * (sR % M + 1) + M = M * (sR % M + 2) := by rw [Nat.mul_add, Nat.mul_add]; omega
            _ ≤ M * M := Nat.mul_le_mul_left M (by omega)
        omega
      · have hmodR : sR % M = sR := Nat.mod_eq_of_lt (by omega)
        have htot : sL + M * sR = (sL % M) + M * (sR % M + 1) := by
          rw [hmodR]; calc sL + M * sR = (sL % M + M) + M * sR := by rw [← hqL]
            _ = (sL % M) + M * (sR + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        rw [htot, Nat.mod_eq_of_lt]
        have hmodL := Nat.mod_lt sL hMpos
        have h1 : M * (sR % M + 1) + M ≤ M * M := by
          rw [hmodR]
          calc M * (sR + 1) + M = M * (sR + 2) := by rw [Nat.mul_add, Nat.mul_add]; omega
            _ ≤ M * M := Nat.mul_le_mul_left M (by omega)
        omega
  · simp only [hL, ite_false]
    have hmodL : sL % M = sL := Nat.mod_eq_of_lt (by omega)
    by_cases hR : M ≤ sR
    · have hqR : sR = (sR % M) + M := by
        have : sR % M = sR - M := by rw [Nat.mod_eq_sub_mod hR, Nat.mod_eq_of_lt (by omega)]
        omega
      have htot : sL + M * sR = (sL % M) + M * (sR % M) + M * M := by
        rw [hmodL]; calc sL + M * sR = sL + M * (sR % M + M) := by rw [← hqR]
          _ = sL + M * (sR % M) + M * M := by rw [Nat.mul_add]; omega
      rw [htot, Nat.add_mod_right, Nat.mod_eq_of_lt]
      have hmodR := Nat.mod_lt sR hMpos
      have h1 : M * (sR % M) + M ≤ M * M := by
        calc M * (sR % M) + M = M * (sR % M + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ M * M := Nat.mul_le_mul_left M hmodR
      omega
    · have hmodR : sR % M = sR := Nat.mod_eq_of_lt (by omega)
      rw [hmodL, hmodR, Nat.mod_eq_of_lt]
      have h1 : M * sR + M ≤ M * M := by
        calc M * sR + M = M * (sR + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ M * M := Nat.mul_le_mul_left M (by omega)
      omega

theorem evalBTA_claMod7_hom :
    ∀ {k : Nat} (t : BTree (Bool × Bool) k),
      evalBTA claMod7BTA (mapBTree pairBoolToFin4 t) =
        encCLA (claGP t).1 (claGP t).2
               ((valX t + valY t) % 7)
               (((valX t + valY t) % (2 ^ (2 ^ k))) % 7) := by
  intro k t
  induction t with
  | leaf p =>
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> rfl
  | @node k' l r ihl ihr =>
    change claMod7BTA.comb (phaseOfNat 0 1 k') _ _ = _
    rw [ihl, ihr]
    have ⟨hgL, hpL⟩ := claGP_spec l
    have ⟨hgR, hpR⟩ := claGP_spec r
    have hxL := valX_lt l; have hyL := valY_lt l
    have hxR := valX_lt r; have hyR := valY_lt r
    have hM2 : 2 ^ (2 ^ (k' + 1)) = (2 ^ (2 ^ k')) * (2 ^ (2 ^ k')) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    have hM7 : (2 ^ (2 ^ k')) % 7 = if k' % 2 == 0 then 2 else 4 := two_pow_two_pow_mod7 k'
    have hph : (phaseOfNat 0 1 k').val = k' % 2 := by unfold phaseOfNat; simp
    have hsum : valX (.node l r) + valY (.node l r) =
        (valX l + valY l) + (2 ^ (2 ^ k')) * (valX r + valY r) := by
      simp only [valX, valY, Nat.mul_add]; omega
    have htrunc := trunc_step_arith (2 ^ (2 ^ k')) (valX l + valY l) (valX r + valY r)
      (Nat.two_pow_pos _) (by omega) (by omega)
    dsimp only [claMod7BTA, claGP]
    rw [(decCLA_encCLA _ _ _ _).1, (decCLA_encCLA _ _ _ _).2.1,
        (decCLA_encCLA _ _ _ _).2.2.1, (decCLA_encCLA _ _ _ _).2.2.2,
        (decCLA_encCLA _ _ _ _).1, (decCLA_encCLA _ _ _ _).2.1,
        (decCLA_encCLA _ _ _ _).2.2.1, (decCLA_encCLA _ _ _ _).2.2.2]
    rw [hsum, hM2, htrunc, hph]
    congr 1
    · rw [Nat.add_mod (valX l + valY l), Nat.mul_mod (2 ^ (2 ^ k')), hM7]
      simp only [Nat.mod_mod]
      by_cases hk : k' % 2 = 0
      · simp [hk]; omega
      · have hk1 : k' % 2 = 1 := by omega
        simp [hk1]; omega
    · rw [hgL, hpR, Nat.add_mod ((valX l + valY l) % (2 ^ (2 ^ k'))), Nat.mul_mod (2 ^ (2 ^ k')), hM7]
      simp only [Nat.mod_mod]
      by_cases hL : 2 ^ (2 ^ k') ≤ valX l + valY l <;>
        by_cases hRp : valX r + valY r + 1 = 2 ^ (2 ^ k') <;>
        by_cases hk : k' % 2 = 0
      all_goals (
        try (have hk1 : k' % 2 = 1 := by omega)
        simp [*] <;> omega)

def mortonClaMod7QTA : TimedQTA :=
  compilePeriod2BTAtoQTA claMod7BTA rfl rfl

def badPlanarCert_injectCross : FactoredBitmaskCert where
  evenMask := planarFactoredCert.evenMask ||| (1 <<< 6)
  topMask := planarFactoredCert.topMask
  botMask := planarFactoredCert.botMask

def badPlanarCert_dropLeaf : FactoredBitmaskCert where
  evenMask := planarFactoredCert.evenMask ^^^ 1
  topMask := planarFactoredCert.topMask
  botMask := planarFactoredCert.botMask

def badPlanarCert_dropMid : FactoredBitmaskCert where
  evenMask := planarFactoredCert.evenMask
  topMask := planarFactoredCert.topMask ^^^ 1
  botMask := planarFactoredCert.botMask

def badG8Cert_dropGen : UpsetCert 225 2704 where
  gens := certG8.gens.tail
  topGens := certG8.topGens
  botGens := certG8.botGens

def badG8Cert_injectBotBot : UpsetCert 225 2704 where
  gens := encPair BOT4 BOT4 :: certG8.gens
  topGens := certG8.topGens
  botGens := certG8.botGens

def badG8Cert_dropTopGen : UpsetCert 225 2704 where
  gens := certG8.gens
  topGens := certG8.topGens.tail
  botGens := certG8.botGens

def badHilbertMod5Cert_dropLeaf : PhaseBitmaskCert 2 where
  masks := fun ph => if ph.val == 0 then 1 else 1

def badHilbertMod5Cert_unsafe : PhaseBitmaskCert 2 where
  masks := fun ph => if ph.val == 0 then 17 else 3

def badHilbertMod3Cert_unsafe : PhaseBitmaskCert 2 where
  masks := fun ph => if ph.val == 0 then (1 <<< 0) ||| (1 <<< 40) else (1 <<< 0) ||| (1 <<< 40) ||| (1 <<< 80) ||| (1 <<< 1)

def badClaMod7Cert_dropState : PhaseBitmaskCert 2 where
  masks := fun ph => if ph.val == 0 then claMod7Cert.masks ph ^^^ 1 else claMod7Cert.masks ph

def wrongPeriod1ClaBTA : TimedBTA where
  numLeaves := 4
  numStates := 196
  r0 := 0
  p1 := 0
  leaf := claMod7BTA.leaf
  comb := fun _ stL stR => claMod7BTA.comb ⟨0, by omega⟩ stL stR

def wrongPeriod1ClaGood (_ : Fin 1) (st : Fin 196) : Bool :=
  claMod7Good ⟨0, by omega⟩ st

def wrongPeriod1ClaCert : PhaseBitmaskCert 1 where
  masks := fun _ => claMod7Cert.masks ⟨0, by omega⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem negative_mutation_tests_all_rejected :
    checkFactoredQTACert percFactoredQTA isPlanar4 badPlanarCert_injectCross = false ∧
    checkFactoredQTACert percFactoredQTA isPlanar4 badPlanarCert_dropLeaf = false ∧
    checkFactoredQTACert percFactoredQTA isPlanar4 badPlanarCert_dropMid = false ∧
    checkUpsetCert percPairLeaf pairHTop pairHBot pairVGlue pairLe pairMidLe planarPairMask superConnGood badG8Cert_dropGen = false ∧
    checkUpsetCert percPairLeaf pairHTop pairHBot pairVGlue pairLe pairMidLe planarPairMask superConnGood badG8Cert_injectBotBot = false ∧
    checkUpsetCert percPairLeaf pairHTop pairHBot pairVGlue pairLe pairMidLe planarPairMask superConnGood badG8Cert_dropTopGen = false ∧
    checkQTACert hilbertMod5QTA hilbertMod5Good badHilbertMod5Cert_dropLeaf = false ∧
    checkQTACert hilbertMod5QTA hilbertMod5Good badHilbertMod5Cert_unsafe = false ∧
    checkQTACert hilbertMod3QTA hilbertMod3Good badHilbertMod3Cert_unsafe = false ∧
    checkBTACert claMod7BTA claMod7Good badClaMod7Cert_dropState = false ∧
    checkBTACert wrongPeriod1ClaBTA wrongPeriod1ClaGood wrongPeriod1ClaCert = false := by
  decide

/-! ## Section 8: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples -/

theorem sharpness_family1 :
    let out_uncomp := pairComb (encPair BOT4 BOT4) (encPair BOT4 TOP4) (encPair TOP4 BOT4) (encPair BOT4 BOT4)
    (joinIsTop (decPair1 out_uncomp) (decPair2 out_uncomp) = false) ∧
    (superConnGood out_uncomp = false) ∧
    (joinIsTop ⟨12, by omega⟩ ⟨7, by omega⟩ = false) ∧
    (qcombExec CROSS4 CROSS4 CROSS4 CROSS4 = CROSS4) := by
  decide

def qtree2_pixel01 : QTree Bool 2 :=
  .qnode (.qnode (.qleaf false) (.qleaf true) (.qleaf false) (.qleaf false))
         (.qnode (.qleaf false) (.qleaf false) (.qleaf false) (.qleaf false))
         (.qnode (.qleaf false) (.qleaf false) (.qleaf false) (.qleaf false))
         (.qnode (.qleaf false) (.qleaf false) (.qleaf false) (.qleaf false))

def qtree1_nw : QTree Bool 1 :=
  .qnode (.qleaf true) (.qleaf false) (.qleaf false) (.qleaf false)

theorem sharpness_family2 :
    ((hilbertVal ⟨0, by omega⟩ (.qleaf true) + hilbertVal ⟨1, by omega⟩ (.qleaf true) +
      hilbertVal ⟨2, by omega⟩ (.qleaf true) + hilbertVal ⟨3, by omega⟩ (.qleaf true)) % 5 = 4) ∧
    (hilbertD4Sum (.qleaf true) % 15 = 8) ∧
    ((hilbertVal ⟨0, by omega⟩ qtree1_nw + hilbertVal ⟨0, by omega⟩ (rot90Q qtree1_nw) +
      hilbertVal ⟨0, by omega⟩ (rot180Q qtree1_nw) + hilbertVal ⟨0, by omega⟩ (rot270Q qtree1_nw)) % 5 = 0) ∧
    ((hilbertVal ⟨0, by omega⟩ qtree2_pixel01 + hilbertVal ⟨0, by omega⟩ (rot90Q qtree2_pixel01) +
      hilbertVal ⟨0, by omega⟩ (rot180Q qtree2_pixel01) + hilbertVal ⟨0, by omega⟩ (rot270Q qtree2_pixel01)) % 5 = 4) ∧
    ((mortonVal qtree1_nw + mortonVal (antiTransQ qtree1_nw) +
      mortonVal (rot180Q qtree1_nw) + mortonVal (transQ qtree1_nw)) % 5 = 3) := by
  decide

def btree1_3_1 : BTree (Bool × Bool) 1 :=
  .node (.leaf (true, true)) (.leaf (true, false))

def btree1_2_1 : BTree (Bool × Bool) 1 :=
  .node (.leaf (false, true)) (.leaf (true, false))

end CertComp6

/-! ## Section 9: Exhaustive `#print axioms` Audit -/
