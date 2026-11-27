/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AutomaticWordAvoidanceCompiler.Defs

/-!
# Theorems (`AutomaticWordAvoidanceCompiler`)

# Pure-Silicon Automatic-Word Pattern-Avoidance Certificate Engine (Lean 4.34.1)

Standalone, zero-Mathlib, kernel-verified reflection compiler and proof engine.
Every certificate structure is 100% PURE DATA (`Nat`, `Bool`, `List`, `BTree`)
with ZERO `Prop` fields and ZERO `native_decide` / `Float` / `sorry`.

Architecture:
  Layer 0: Native Silicon Bitwise Arithmetic (`popcount`, `carryXor`, `carryAnd`, `grayMod4`)
           + Reusable Carry-Offset Vector Compiler (`checkCarryXorModel`, `checkCarryAndModel`)
  Layer 1: Pure-Data Overlap-Graph Invariant Engine (`WindowCert`, `windowCert_sound`)
  Layer 2: Parity-Synchronization & Even-Halving Unbounded k-Power Avoidance Compiler
           (`SyncCert`, `PowerAvoidCert`, `syncCert_sound`, `powerAvoidCert_sound`)
  Layer 3: Parity-Conditioned Both-Bit Halving Unbounded Overlap-Avoidance Compiler
           (`OverlapAvoidCert`, `overlapAvoidCert_sound`)
  Layer 4: Concrete Infinite Pure-Silicon Theorems (T1..T7), Sharpness Counterexamples,
           Non-Vacuity Witnesses, Hostile Mutation Tests, and `#print axioms`.
-/


namespace SiliconAvoidance
theorem popcountAux_zero (fuel : Nat) : popcountAux fuel 0 = 0 := by
  cases fuel <;> rfl

theorem popcountAux_fuel_irrel : ∀ (f1 f2 n : Nat), n ≤ f1 → n ≤ f2 →
    popcountAux f1 n = popcountAux f2 n
  | 0, f2, n, h1, _ => by
    have : n = 0 := by omega
    subst this; rw [popcountAux_zero, popcountAux_zero]
  | f1, 0, n, _, h2 => by
    have : n = 0 := by omega
    subst this; rw [popcountAux_zero, popcountAux_zero]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    cases n with
    | zero => rfl
    | succ m =>
      have hne : ((m + 1) == 0) = false := by simp
      simp only [popcountAux, hne, Bool.false_eq_true, ↓reduceIte]
      have ih := popcountAux_fuel_irrel f1 f2 ((m + 1) / 2) (by omega) (by omega)
      rw [ih]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_eq_mod_add_div (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => rfl
  | succ m =>
    unfold popcount
    have hne : ((m + 1) == 0) = false := by simp
    simp only [popcountAux, hne, Bool.false_eq_true, ↓reduceIte]
    rw [popcountAux_fuel_irrel m ((m + 1) / 2) ((m + 1) / 2) (by omega) (by omega)]

theorem popcount_two_mul (n : Nat) : popcount (2 * n) = popcount n := by
  rw [popcount_eq_mod_add_div]
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [h1, h2, Nat.zero_add]

theorem popcount_two_mul_add_one (n : Nat) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_eq_mod_add_div]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

theorem popcount_two_mul_add_bit (n b : Nat) (hb : b < 2) :
    popcount (2 * n + b) = popcount n + b := by
  have hcases : b = 0 ∨ b = 1 := by omega
  rcases hcases with rfl | rfl
  · simp [popcount_two_mul]
  · rw [popcount_two_mul_add_one]; omega

-- Bitwise mod 2 and div 2 identities via testBit extensionality
theorem mod_two_eq_testBit_zero (a : Nat) : a % 2 = if a.testBit 0 then 1 else 0 := by
  rw [Nat.testBit_zero]
  by_cases h : a % 2 = 1
  · simp [h]
  · have h0 : a % 2 = 0 := by omega
    simp [h0]

theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_div_two, Nat.testBit_div_two]

theorem and_div_two (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_and, Nat.testBit_div_two, Nat.testBit_div_two]

theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
  rw [mod_two_eq_testBit_zero, Nat.testBit_xor, mod_two_eq_testBit_zero a, mod_two_eq_testBit_zero b]
  cases a.testBit 0 <;> cases b.testBit 0 <;> rfl

theorem and_mod_two (a b : Nat) : (a &&& b) % 2 = (a % 2) * (b % 2) := by
  rw [mod_two_eq_testBit_zero, Nat.testBit_and, mod_two_eq_testBit_zero a, mod_two_eq_testBit_zero b]
  cases a.testBit 0 <;> cases b.testBit 0 <;> rfl

theorem popcount_xor_mod_two (a b : Nat) :
    popcount (a ^^^ b) % 2 = (popcount a + popcount b) % 2 := by
  induction hs : a + b using Nat.strongRecOn generalizing a b with
  | _ s ih =>
    by_cases h0 : a = 0 ∧ b = 0
    · rcases h0 with ⟨rfl, rfl⟩; rfl
    · have hlt : a / 2 + b / 2 < s := by omega
      rw [popcount_eq_mod_add_div (a ^^^ b), xor_mod_two, xor_div_two]
      rw [popcount_eq_mod_add_div a, popcount_eq_mod_add_div b]
      have hih := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) rfl
      omega

theorem popcount_and_step (a b : Nat) :
    popcount (a &&& b) = (a % 2) * (b % 2) + popcount ((a / 2) &&& (b / 2)) := by
  rw [popcount_eq_mod_add_div (a &&& b), and_mod_two, and_div_two]

theorem popcount_gray_step (n b : Nat) (hb : b < 2) :
    popcount ((2 * n + b) ^^^ n) = ((b + n % 2) % 2) + popcount (n ^^^ (n / 2)) := by
  rw [popcount_eq_mod_add_div ((2 * n + b) ^^^ n), xor_mod_two, xor_div_two]
  have h1 : (2 * n + b) % 2 = b := by omega
  have h2 : (2 * n + b) / 2 = n := by omega
  rw [h1, h2]

theorem popcount_gray_mod_two (n : Nat) : popcount (n ^^^ (n / 2)) % 2 = n % 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => rfl
    | succ m =>
      have hdiv : (m + 1) / 2 < m + 1 := by omega
      have hih := ih ((m + 1) / 2) hdiv
      have hdecomp : m + 1 = 2 * ((m + 1) / 2) + (m + 1) % 2 := by omega
      have hstep := popcount_gray_step ((m + 1) / 2) ((m + 1) % 2) (by omega)
      rw [← hdecomp] at hstep
      omega

theorem BTree.all_spec {α : Type} {p : α → Bool} {t : BTree α}
    (hall : t.all p = true) : ∀ i x, t.get? i = some x → p x = true := by
  induction t with
  | empty => intro i x h; cases h
  | leaf a =>
    intro i x h
    cases i with
    | zero =>
      simp only [BTree.get?, Option.some.injEq] at h
      subst h
      simpa [BTree.all] using hall
    | succ _ =>
      simp only [BTree.get?] at h
      cases h
  | node l r ihl ihr =>
    intro i x h
    simp only [BTree.all, Bool.and_eq_true] at hall
    simp only [BTree.get?] at h
    split at h
    · exact ihl hall.1 _ _ h
    · exact ihr hall.2 _ _ h

theorem DFAO.evalStateAux_zero (M : DFAO) (fuel : Nat) : M.evalStateAux fuel 0 = M.q0 := by
  cases fuel <;> rfl

theorem DFAO.evalStateAux_fuel_irrel (M : DFAO) :
    ∀ (f1 f2 n : Nat), n ≤ f1 → n ≤ f2 → M.evalStateAux f1 n = M.evalStateAux f2 n
  | 0, f2, n, h1, _ => by
    have : n = 0 := by omega
    subst this; rw [M.evalStateAux_zero, M.evalStateAux_zero]
  | f1, 0, n, _, h2 => by
    have : n = 0 := by omega
    subst this; rw [M.evalStateAux_zero, M.evalStateAux_zero]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    cases n with
    | zero => rfl
    | succ m =>
      have hne : ((m + 1) == 0) = false := by simp
      simp only [DFAO.evalStateAux, hne, Bool.false_eq_true, ↓reduceIte]
      rw [M.evalStateAux_fuel_irrel f1 f2 ((m + 1) / 2) (by omega) (by omega)]

theorem DFAO.evalState_zero (M : DFAO) : M.evalState 0 = M.q0 := rfl

theorem DFAO.evalState_succ (M : DFAO) (m : Nat) :
    M.evalState (m + 1) =
      let q := M.evalState ((m + 1) / 2)
      if (m + 1) % 2 == 0 then M.step0 q else M.step1 q := by
  unfold DFAO.evalState
  have hne : ((m + 1) == 0) = false := by simp
  simp only [DFAO.evalStateAux, hne, Bool.false_eq_true, ↓reduceIte]
  rw [M.evalStateAux_fuel_irrel m ((m + 1) / 2) ((m + 1) / 2) (by omega) (by omega)]

theorem list_getD_lt_of_all {xs : List Nat} {B i : Nat}
    (hall : xs.all (fun x => decide (x < B)) = true) (hi : i < xs.length) :
    xs.getD i 0 < B := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    cases i with
    | zero => simpa [List.getD] using hall.1
    | succ k =>
      simp only [List.length_cons] at hi
      simpa [List.getD] using ih hall.2 (by omega)

theorem DFAO.wf_q0_lt {M : DFAO} (hwf : M.wf = true) : M.q0 < M.numStates := by
  simp only [DFAO.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  exact hwf.1.1.1.1.1.1.1.2

theorem DFAO.wf_step0_q0 {M : DFAO} (hwf : M.wf = true) : M.step0 M.q0 = M.q0 := by
  simp only [DFAO.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  exact hwf.2

theorem DFAO.wf_step0_lt {M : DFAO} (hwf : M.wf = true) {q : Nat} (hq : q < M.numStates) :
    M.step0 q < M.numStates := by
  simp only [DFAO.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  exact list_getD_lt_of_all hwf.1.1.1.2 (by omega)

theorem DFAO.wf_step1_lt {M : DFAO} (hwf : M.wf = true) {q : Nat} (hq : q < M.numStates) :
    M.step1 q < M.numStates := by
  simp only [DFAO.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  exact list_getD_lt_of_all hwf.1.1.2 (by omega)

theorem DFAO.wf_out_lt {M : DFAO} (hwf : M.wf = true) {q : Nat} (hq : q < M.numStates) :
    M.out q < M.numAlpha := by
  simp only [DFAO.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  exact list_getD_lt_of_all hwf.1.2 (by omega)

theorem DFAO.evalState_lt {M : DFAO} (hwf : M.wf = true) (n : Nat) :
    M.evalState n < M.numStates := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => rw [M.evalState_zero]; exact M.wf_q0_lt hwf
    | succ m =>
      rw [M.evalState_succ]
      have hq := ih ((m + 1) / 2) (by omega)
      dsimp only
      split
      · exact M.wf_step0_lt hwf hq
      · exact M.wf_step1_lt hwf hq

theorem DFAO.evalState_two_mul {M : DFAO} (hwf : M.wf = true) (n : Nat) :
    M.evalState (2 * n) = M.step0 (M.evalState n) := by
  cases n with
  | zero =>
    simp only [Nat.mul_zero, M.evalState_zero]
    exact (M.wf_step0_q0 hwf).symm
  | succ m =>
    have hEq : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hEq, M.evalState_succ]
    have hmod : ((2 * m + 1) + 1) % 2 = 0 := by omega
    have hdiv : ((2 * m + 1) + 1) / 2 = m + 1 := by omega
    dsimp only
    rw [hmod, hdiv]
    rfl

theorem DFAO.evalState_two_mul_add_one {M : DFAO} (n : Nat) :
    M.evalState (2 * n + 1) = M.step1 (M.evalState n) := by
  rw [M.evalState_succ]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  dsimp only
  rw [hmod, hdiv]
  rfl

theorem DFAO.evalState_two_mul_add_bit {M : DFAO} (hwf : M.wf = true) (n b : Nat) (hb : b < 2) :
    M.evalState (2 * n + b) = if b = 0 then M.step0 (M.evalState n) else M.step1 (M.evalState n) := by
  have hcases : b = 0 ∨ b = 1 := by omega
  rcases hcases with rfl | rfl
  · simp [M.evalState_two_mul hwf]
  · simp [M.evalState_two_mul_add_one]

-- ============================================================================
-- Section 3: Reusable Carry-Offset Vector Compiler (Silicon Arithmetic -> DFAO)
-- ============================================================================

def allRange (n : Nat) (p : Nat → Bool) : Bool :=
  (List.range n).all p

theorem allRange_spec {n : Nat} {p : Nat → Bool} (h : allRange n p = true) :
    ∀ i < n, p i = true := by
  intro i hi
  simp only [allRange, List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def checkCarryXorModel (K : Nat) (M : DFAO) (vt : List (List Nat)) : Bool :=
  M.wf &&
  (0 < K) &&
  (vt.length == M.numStates) &&
  allRange K (fun c => (vt.getD M.q0 []).getD c 2 == popcount c % 2) &&
  allRange M.numStates (fun q =>
    (vt.getD q []).length == K &&
    (M.out q == (vt.getD q []).getD 0 2) &&
    allRange K (fun c =>
      let q0' := M.step0 q
      let q1' := M.step1 q
      ((vt.getD q0' []).getD c 2 == ((vt.getD q []).getD (c / 2) 2 + c % 2) % 2) &&
      ((vt.getD q1' []).getD c 2 == ((vt.getD q []).getD ((K + c) / 2) 2 + (K + c) % 2 + 1) % 2)))

theorem carryXorModel_sound (K : Nat) (M : DFAO) (vt : List (List Nat))
    (hchk : checkCarryXorModel K M vt = true) :
    ∀ n : Nat, carryXor K n = M.evalWord n := by
  simp only [checkCarryXorModel, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hwf, hK⟩, _hlen⟩, hinit⟩, hstep⟩
  have hvec : ∀ n c, c < K → (vt.getD (M.evalState n) []).getD c 2 = (popcount (K * n + c) + popcount n) % 2 := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro c hc
      cases n with
      | zero =>
        simp only [M.evalState_zero, Nat.mul_zero, Nat.zero_add, popcount_zero, Nat.add_zero]
        have hi := allRange_spec hinit c hc
        simpa [beq_iff_eq] using hi
      | succ m =>
        have hdiv : (m + 1) / 2 < m + 1 := by omega
        let q := M.evalState ((m + 1) / 2)
        have hq : q < M.numStates := M.evalState_lt hwf _
        have hqs := allRange_spec hstep q hq
        simp only [Bool.and_eq_true, beq_iff_eq] at hqs
        have hcs := allRange_spec hqs.2 c hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hcs
        by_cases hpar : (m + 1) % 2 = 0
        · have hm : m + 1 = 2 * ((m + 1) / 2) := by omega
          have hst : M.evalState (m + 1) = M.step0 q :=
            (congrArg M.evalState hm).trans (M.evalState_two_mul hwf _)
          rw [hst, hcs.1]
          have hih := ih ((m + 1) / 2) hdiv (c / 2) (by omega)
          rw [hih]
          have hkm : K * (m + 1) + c = 2 * (K * ((m + 1) / 2) + c / 2) + c % 2 :=
            calc K * (m + 1) + c = K * (2 * ((m + 1) / 2)) + c := congrArg (fun x => K * x + c) hm
              _ = 2 * (K * ((m + 1) / 2)) + c := by rw [Nat.mul_left_comm]
              _ = 2 * (K * ((m + 1) / 2) + c / 2) + c % 2 := by omega
          have hpm : popcount (m + 1) = popcount ((m + 1) / 2) :=
            (congrArg popcount hm).trans (popcount_two_mul _)
          rw [hkm, popcount_two_mul_add_bit _ _ (by omega), hpm]
          omega
        · have hm : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
          have hst : M.evalState (m + 1) = M.step1 q :=
            (congrArg M.evalState hm).trans (M.evalState_two_mul_add_one _)
          rw [hst, hcs.2]
          have hih := ih ((m + 1) / 2) hdiv ((K + c) / 2) (by omega)
          rw [hih]
          have hkm : K * (m + 1) + c = 2 * (K * ((m + 1) / 2) + (K + c) / 2) + (K + c) % 2 :=
            calc K * (m + 1) + c = K * (2 * ((m + 1) / 2) + 1) + c := congrArg (fun x => K * x + c) hm
              _ = 2 * (K * ((m + 1) / 2)) + K + c := by rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_one]
              _ = 2 * (K * ((m + 1) / 2) + (K + c) / 2) + (K + c) % 2 := by omega
          have hpm : popcount (m + 1) = 1 + popcount ((m + 1) / 2) :=
            (congrArg popcount hm).trans (popcount_two_mul_add_one _)
          rw [hkm, popcount_two_mul_add_bit _ _ (by omega), hpm]
          omega
  intro n
  have hq : M.evalState n < M.numStates := M.evalState_lt hwf n
  have hqs := allRange_spec hstep (M.evalState n) hq
  simp only [Bool.and_eq_true, beq_iff_eq] at hqs
  have h0 := hvec n 0 hK
  simp only [Nat.add_zero] at h0
  rw [carryXor, popcount_xor_mod_two, DFAO.evalWord, hqs.1.2, h0]

def checkCarryAndModel (K : Nat) (M : DFAO) (vt : List (List Nat)) : Bool :=
  M.wf &&
  (0 < K) &&
  (vt.length == M.numStates) &&
  allRange K (fun c => (vt.getD M.q0 []).getD c 2 == 0) &&
  allRange M.numStates (fun q =>
    (vt.getD q []).length == K &&
    (M.out q == (vt.getD q []).getD 0 2) &&
    allRange K (fun c =>
      let q0' := M.step0 q
      let q1' := M.step1 q
      ((vt.getD q0' []).getD c 2 == (vt.getD q []).getD (c / 2) 2) &&
      ((vt.getD q1' []).getD c 2 == ((vt.getD q []).getD ((K + c) / 2) 2 + (K + c) % 2) % 2)))

theorem carryAndModel_sound (K : Nat) (M : DFAO) (vt : List (List Nat))
    (hchk : checkCarryAndModel K M vt = true) :
    ∀ n : Nat, carryAnd K n = M.evalWord n := by
  simp only [checkCarryAndModel, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hwf, hK⟩, _hlen⟩, hinit⟩, hstep⟩
  have hvec : ∀ n c, c < K → (vt.getD (M.evalState n) []).getD c 2 = popcount ((K * n + c) &&& n) % 2 := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro c hc
      cases n with
      | zero =>
        simp only [M.evalState_zero, Nat.mul_zero, Nat.zero_add, Nat.and_zero, popcount_zero]
        have hi := allRange_spec hinit c hc
        simpa [beq_iff_eq] using hi
      | succ m =>
        have hdiv : (m + 1) / 2 < m + 1 := by omega
        let q := M.evalState ((m + 1) / 2)
        have hq : q < M.numStates := M.evalState_lt hwf _
        have hqs := allRange_spec hstep q hq
        simp only [Bool.and_eq_true, beq_iff_eq] at hqs
        have hcs := allRange_spec hqs.2 c hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hcs
        by_cases hpar : (m + 1) % 2 = 0
        · have hm : m + 1 = 2 * ((m + 1) / 2) := by omega
          have hst : M.evalState (m + 1) = M.step0 q :=
            (congrArg M.evalState hm).trans (M.evalState_two_mul hwf _)
          rw [hst, hcs.1]
          have hih := ih ((m + 1) / 2) hdiv (c / 2) (by omega)
          rw [hih]
          rw [popcount_and_step (K * (m + 1) + c) (m + 1)]
          have hkm : K * (m + 1) + c = 2 * (K * ((m + 1) / 2) + c / 2) + c % 2 :=
            calc K * (m + 1) + c = K * (2 * ((m + 1) / 2)) + c := congrArg (fun x => K * x + c) hm
              _ = 2 * (K * ((m + 1) / 2)) + c := by rw [Nat.mul_left_comm]
              _ = 2 * (K * ((m + 1) / 2) + c / 2) + c % 2 := by omega
          have h1 : (K * (m + 1) + c) / 2 = K * ((m + 1) / 2) + c / 2 := by omega
          rw [h1, hpar, Nat.mul_zero, Nat.zero_add]
        · have hm : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
          have hst : M.evalState (m + 1) = M.step1 q :=
            (congrArg M.evalState hm).trans (M.evalState_two_mul_add_one _)
          rw [hst, hcs.2]
          have hih := ih ((m + 1) / 2) hdiv ((K + c) / 2) (by omega)
          rw [hih]
          rw [popcount_and_step (K * (m + 1) + c) (m + 1)]
          have hkm : K * (m + 1) + c = 2 * (K * ((m + 1) / 2) + (K + c) / 2) + (K + c) % 2 :=
            calc K * (m + 1) + c = K * (2 * ((m + 1) / 2) + 1) + c := congrArg (fun x => K * x + c) hm
              _ = 2 * (K * ((m + 1) / 2)) + K + c := by rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_one]
              _ = 2 * (K * ((m + 1) / 2) + (K + c) / 2) + (K + c) % 2 := by omega
          have h1 : (K * (m + 1) + c) / 2 = K * ((m + 1) / 2) + (K + c) / 2 := by omega
          have h2 : (K * (m + 1) + c) % 2 = (K + c) % 2 := by omega
          have h3 : (m + 1) % 2 = 1 := by omega
          rw [h1, h2, h3, Nat.mul_one]
          omega
  intro n
  have hq : M.evalState n < M.numStates := M.evalState_lt hwf n
  have hqs := allRange_spec hstep (M.evalState n) hq
  simp only [Bool.and_eq_true, beq_iff_eq] at hqs
  have h0 := hvec n 0 hK
  simp only [Nat.add_zero] at h0
  rw [carryAnd, DFAO.evalWord, hqs.1.2, h0]

theorem outputWindow_eq_map (M : DFAO) (W n : Nat) :
    outputWindow M W n = (stateWindow M W n).map M.out := by
  simp [outputWindow, stateWindow, List.map_map, Function.comp, DFAO.evalWord]

theorem list_getD_map_range {f : Nat → Nat} {W k : Nat} (hk : k < W) :
    ((List.range W).map f).getD k 0 = f k := by
  simp [List.getD, hk]

theorem stepWindow_stateWindow {M : DFAO} (hwf : M.wf = true) (b : Bool) (W n : Nat) :
    stepWindow M b (stateWindow M W n) = stateWindow M W (2 * n + if b then 1 else 0) := by
  simp only [stepWindow, stateWindow, List.length_map, List.length_range]
  apply List.map_congr_left
  intro i hi
  have hiW : i < W := List.mem_range.mp hi
  let bNat : Nat := if b then 1 else 0
  have hbNat : bNat ≤ 1 := by cases b <;> decide
  have hidx : (bNat + i) / 2 < W := by omega
  change (if (bNat + i) % 2 == 0 then
            M.step0 ((List.map (fun i => M.evalState (n + i)) (List.range W)).getD ((bNat + i) / 2) 0)
          else
            M.step1 ((List.map (fun i => M.evalState (n + i)) (List.range W)).getD ((bNat + i) / 2) 0)) =
         M.evalState (2 * n + bNat + i)
  rw [list_getD_map_range hidx]
  have hsplit : 2 * n + bNat + i = 2 * (n + (bNat + i) / 2) + (bNat + i) % 2 := by omega
  by_cases hpar : (bNat + i) % 2 = 0
  · simp only [hpar, beq_self_eq_true, ↓reduceIte]
    rw [hsplit, hpar, Nat.add_zero, M.evalState_two_mul hwf]
  · have hpar1 : (bNat + i) % 2 = 1 := by omega
    simp only [hpar1, show (1 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte]
    rw [hsplit, hpar1, M.evalState_two_mul_add_one]

theorem windowCert_reach (M : DFAO) (W : Nat) (ok : List Nat → Bool) (cert : WindowCert)
    (h : checkWindowCert M W ok cert = true) :
    ∀ n : Nat, ∃ idx nd, cert.graph.get? idx = some nd ∧ nd.win = stateWindow M W n := by
  simp only [checkWindowCert, Bool.and_eq_true] at h
  rcases h with ⟨⟨hwf, hinit⟩, hall⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero =>
      cases h0 : cert.graph.get? 0 with
      | none => simp [h0] at hinit
      | some nd =>
        simp only [h0, beq_iff_eq] at hinit
        exact ⟨0, nd, h0, hinit⟩
    | succ m =>
      rcases ih ((m + 1) / 2) (by omega) with ⟨idx, nd, hget, hwin⟩
      have hnd := BTree.all_spec hall idx nd hget
      simp only [Bool.and_eq_true] at hnd
      by_cases hpar : (m + 1) % 2 = 0
      · cases hnext : cert.graph.get? nd.next0 with
        | none => simp [hnext] at hnd
        | some nd0 =>
          have h0 := hnd.1.2
          simp only [hnext, beq_iff_eq] at h0
          refine ⟨nd.next0, nd0, hnext, ?_⟩
          rw [h0, hwin, stepWindow_stateWindow hwf false W]
          have : 2 * ((m + 1) / 2) + 0 = m + 1 := by omega
          simpa using congrArg (stateWindow M W) this
      · cases hnext : cert.graph.get? nd.next1 with
        | none => simp [hnext] at hnd
        | some nd1 =>
          have h1 := hnd.2
          simp only [hnext, beq_iff_eq] at h1
          refine ⟨nd.next1, nd1, hnext, ?_⟩
          rw [h1, hwin, stepWindow_stateWindow hwf true W]
          have : 2 * ((m + 1) / 2) + 1 = m + 1 := by omega
          simpa using congrArg (stateWindow M W) this

/-- Layer 1 General Soundness Meta-Theorem: finite overlap-graph cert => ∀ n : Nat. -/
theorem windowCert_sound (M : DFAO) (W : Nat) (ok : List Nat → Bool) (cert : WindowCert)
    (h : checkWindowCert M W ok cert = true) :
    ∀ n : Nat, ok (outputWindow M W n) = true := by
  intro n
  rcases windowCert_reach M W ok cert h n with ⟨idx, nd, hget, hwin⟩
  simp only [checkWindowCert, Bool.and_eq_true] at h
  have hnd := BTree.all_spec h.2 idx nd hget
  simp only [Bool.and_eq_true] at hnd
  rw [outputWindow_eq_map, ← hwin]
  exact hnd.1.1.2

theorem syncCert_reach (M : DFAO) (cert : SyncCert) (h : checkSyncCert M cert = true) :
    ∀ n : Nat, ∃ idx nd, cert.graph.get? idx = some nd ∧
      nd.parity = decide (n % 2 = 1) ∧ nd.win = stateWindow M cert.width n := by
  simp only [checkSyncCert, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hwf, _hw⟩, hinit⟩, hall⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero =>
      cases h0 : cert.graph.get? 0 with
      | none => simp [h0] at hinit
      | some nd =>
        simp only [h0, Bool.and_eq_true, beq_iff_eq] at hinit
        exact ⟨0, nd, h0, by simpa using hinit.1, hinit.2⟩
    | succ m =>
      rcases ih ((m + 1) / 2) (by omega) with ⟨idx, nd, hget, _hpar, hwin⟩
      have hnd := BTree.all_spec hall idx nd hget
      simp only [Bool.and_eq_true] at hnd
      by_cases hp : (m + 1) % 2 = 0
      · cases hnext : cert.graph.get? nd.next0 with
        | none => simp [hnext] at hnd
        | some nd0 =>
          have h0 := hnd.1.2
          simp only [hnext, Bool.and_eq_true, beq_iff_eq] at h0
          refine ⟨nd.next0, nd0, hnext, ?_, ?_⟩
          · rw [h0.1]; simp [hp]
          · rw [h0.2, hwin, stepWindow_stateWindow hwf false cert.width]
            have : 2 * ((m + 1) / 2) + 0 = m + 1 := by omega
            simpa using congrArg (stateWindow M cert.width) this
      · cases hnext : cert.graph.get? nd.next1 with
        | none => simp [hnext] at hnd
        | some nd1 =>
          have h1 := hnd.2
          simp only [hnext, Bool.and_eq_true, beq_iff_eq] at h1
          refine ⟨nd.next1, nd1, hnext, ?_, ?_⟩
          · have hp1 : (m + 1) % 2 = 1 := by omega
            rw [h1.1]; simp [hp1]
          · rw [h1.2, hwin, stepWindow_stateWindow hwf true cert.width]
            have : 2 * ((m + 1) / 2) + 1 = m + 1 := by omega
            simpa using congrArg (stateWindow M cert.width) this

/-- Layer 2a Soundness: length-`cert.width` factor equality forces equal parity mod 2. -/
theorem syncCert_sound (M : DFAO) (cert : SyncCert) (h : checkSyncCert M cert = true) :
    ∀ n1 n2 : Nat,
      (∀ j < cert.width, M.evalWord (n1 + j) = M.evalWord (n2 + j)) →
      n1 % 2 = n2 % 2 := by
  intro n1 n2 hmatch
  rcases syncCert_reach M cert h n1 with ⟨i1, nd1, hg1, hp1, hw1⟩
  rcases syncCert_reach M cert h n2 with ⟨i2, nd2, hg2, hp2, hw2⟩
  simp only [checkSyncCert, Bool.and_eq_true] at h
  have h1 := BTree.all_spec h.2 i1 nd1 hg1
  have h2 := BTree.all_spec h.2 i2 nd2 hg2
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
  have houtEq : nd1.win.map M.out = nd2.win.map M.out := by
    rw [hw1, hw2, ← outputWindow_eq_map, ← outputWindow_eq_map]
    simp only [outputWindow]
    apply List.map_congr_left
    intro j hj
    exact hmatch j (List.mem_range.mp hj)
  have hparEq : nd1.parity = nd2.parity := by
    rw [← h1.1.1.2, ← h2.1.1.2, houtEq]
  rw [hp1, hp2] at hparEq
  by_cases h1m : n1 % 2 = 1 <;> by_cases h2m : n2 % 2 = 1 <;> simp_all <;> omega

theorem noPowerAtPeriod_sound {M : DFAO} {k p n : Nat} (hk : k ≥ 2)
    (h : noPowerAtPeriod k p (outputWindow M (k * p) n) = true) :
    ∃ j : Nat, j < (k - 1) * p ∧ M.evalWord (n + j) ≠ M.evalWord (n + p + j) := by
  simp only [noPowerAtPeriod, List.any_eq_true, List.mem_range, bne_iff_ne] at h
  rcases h with ⟨j, hj, hne⟩
  have h1 : j < k * p := by
    have : (k - 1) * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
    omega
  have h2 : j + p < k * p := by
    have : (k - 1) * p + p = k * p := by
      calc (k - 1) * p + p = (k - 1 + 1) * p := by rw [Nat.add_mul, Nat.one_mul]
        _ = k * p := by rw [Nat.sub_add_cancel (by omega)]
    omega
  simp only [outputWindow] at hne
  rw [list_getD_map_range h1, list_getD_map_range h2] at hne
  refine ⟨j, hj, ?_⟩
  have heq : n + (j + p) = n + p + j := by omega
  rw [heq] at hne
  exact hne

theorem checkBasePowerCerts_spec {M : DFAO} {k : Nat} :
    ∀ (p0 : Nat) (cs : List WindowCert),
      checkBasePowerCerts M k p0 cs = true →
      ∀ (i : Nat) (hi : i < cs.length),
        checkWindowCert M (k * (p0 + i)) (noPowerAtPeriod k (p0 + i)) (cs.get ⟨i, hi⟩) = true
  | _, [], _, _, hi => by simp at hi
  | p0, c :: cs, h, 0, _ => by
    simp only [checkBasePowerCerts, Bool.and_eq_true] at h
    simpa using h.1
  | p0, c :: cs, h, i + 1, hi => by
    simp only [checkBasePowerCerts, Bool.and_eq_true] at h
    have ih := checkBasePowerCerts_spec (p0 + 1) cs h.2 i (by simp at hi; omega)
    have heq : p0 + 1 + i = p0 + (i + 1) := by omega
    simpa [heq] using ih

/-- Layer 2 General Soundness Meta-Theorem:
    A single finite pure-data `PowerAvoidCert` proves ∀ n p, p ≥ 1, M avoids k-powers. -/
theorem powerAvoidCert_sound (M : DFAO) (k : Nat) (cert : PowerAvoidCert)
    (h : checkPowerAvoidCert M k cert = true) :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < (k - 1) * p ∧ M.evalWord (n + j) ≠ M.evalWord (n + p + j) := by
  simp only [checkPowerAvoidCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨hk, hsync⟩, hreach⟩, hinv⟩, ⟨hblen, hbases⟩⟩
  have hwf : M.wf = true := by
    simp only [checkSyncCert, Bool.and_eq_true] at hsync
    exact hsync.1.1.1
  -- Extract even-halving injectivity from reachCert + invEven
  have hevenInv : ∀ a : Nat, cert.invEven.getD (M.evalWord (2 * a)) M.numAlpha = M.evalWord a := by
    intro a
    rcases windowCert_reach M 1 (fun _ => true) cert.reachCert hreach a with ⟨idx, nd, hget, hwin⟩
    have hnd := BTree.all_spec hinv idx nd hget
    simp only [beq_iff_eq] at hnd
    have hq0 : nd.win.getD 0 0 = M.evalState a := by
      rw [hwin]
      simp [stateWindow]
    rw [hq0] at hnd
    rw [DFAO.evalWord, DFAO.evalWord, M.evalState_two_mul hwf]
    exact hnd
  have hevenInj : ∀ a b : Nat, M.evalWord (2 * a) = M.evalWord (2 * b) → M.evalWord a = M.evalWord b := by
    intro a b heq
    rw [← hevenInv a, ← hevenInv b, heq]
  let pSync := (cert.syncCert.width + k - 2) / (k - 1)
  -- Strong induction on period p
  intro n p hp
  induction p using Nat.strongRecOn generalizing n with
  | _ p ih =>
    by_cases hsmall : p < pSync
    · have hi : p - 1 < cert.baseCerts.length := by omega
      have hbc := checkBasePowerCerts_spec 1 cert.baseCerts hbases (p - 1) hi
      have hpEq : 1 + (p - 1) = p := by omega
      rw [hpEq] at hbc
      have hok := windowCert_sound M (k * p) (noPowerAtPeriod k p) _ hbc n
      exact noPowerAtPeriod_sound hk hok
    · -- Large period: p ≥ pSync => (k - 1) * p ≥ cert.syncCert.width
      have hbig : cert.syncCert.width ≤ (k - 1) * p := by
        have hk1 : 0 < k - 1 := by omega
        have hge : pSync ≤ p := by omega
        have hdiv : cert.syncCert.width + (k - 1) - 1 ≤ (k - 1) * pSync + (k - 1) - 1 := by
          have := Nat.div_add_mod (cert.syncCert.width + k - 2) (k - 1)
          have hmod : (cert.syncCert.width + k - 2) % (k - 1) < k - 1 := Nat.mod_lt _ hk1
          have : (k - 1) * pSync + (cert.syncCert.width + k - 2) % (k - 1) = cert.syncCert.width + k - 2 := by
            simpa [pSync] using this
          omega
        have hmul : (k - 1) * pSync ≤ (k - 1) * p := Nat.mul_le_mul_left (k - 1) hge
        omega
      -- Proof by contradiction using Classical.byContradiction (standard Lean axiom)
      apply Classical.byContradiction
      intro hno
      have hall : ∀ j < (k - 1) * p, M.evalWord (n + j) = M.evalWord (n + p + j) := by
        intro j hj
        apply Classical.byContradiction
        intro hne
        exact hno ⟨j, hj, hne⟩
      -- Parity sync forces p to be even
      have hparEq : n % 2 = (n + p) % 2 :=
        syncCert_sound M cert.syncCert hsync n (n + p) (fun j hj => hall j (by omega))
      have hpEven : p % 2 = 0 := by omega
      let p' := p / 2
      have hp'ge : p' ≥ 1 := by omega
      have hp'lt : p' < p := by omega
      -- Extract halved k-power at period p'
      by_cases hnEven : n % 2 = 0
      · let m := n / 2
        rcases ih p' hp'lt m hp'ge with ⟨i, hi, hne⟩
        have h2i : 2 * i < (k - 1) * p := by
          have hp2 : p = 2 * p' := by omega
          have hcomm : (k - 1) * (2 * p') = 2 * ((k - 1) * p') := by rw [Nat.mul_left_comm]
          rw [hp2, hcomm]; omega
        have hmatch := hall (2 * i) h2i
        have hL : n + 2 * i = 2 * (m + i) := by omega
        have hR : n + p + 2 * i = 2 * (m + p' + i) := by omega
        rw [hL, hR] at hmatch
        exact hne (hevenInj (m + i) (m + p' + i) hmatch)
      · let m := n / 2 + 1
        rcases ih p' hp'lt m hp'ge with ⟨i, hi, hne⟩
        have h2i : 2 * i + 1 < (k - 1) * p := by
          have hp2 : p = 2 * p' := by omega
          have hcomm : (k - 1) * (2 * p') = 2 * ((k - 1) * p') := by rw [Nat.mul_left_comm]
          rw [hp2, hcomm]; omega
        have hmatch := hall (2 * i + 1) h2i
        have hL : n + (2 * i + 1) = 2 * (m + i) := by omega
        have hR : n + p + (2 * i + 1) = 2 * (m + p' + i) := by omega
        rw [hL, hR] at hmatch
        exact hne (hevenInj (m + i) (m + p' + i) hmatch)

theorem noOverlapAtPeriod_sound {M : DFAO} {p n : Nat}
    (h : noOverlapAtPeriod p (outputWindow M (2 * p + 1) n) = true) :
    ∃ j : Nat, j ≤ p ∧ M.evalWord (n + j) ≠ M.evalWord (n + p + j) := by
  simp only [noOverlapAtPeriod, List.any_eq_true, List.mem_range, bne_iff_ne] at h
  rcases h with ⟨j, hj, hne⟩
  have h1 : j < 2 * p + 1 := by omega
  have h2 : j + p < 2 * p + 1 := by omega
  simp only [outputWindow] at hne
  rw [list_getD_map_range h1, list_getD_map_range h2] at hne
  refine ⟨j, by omega, ?_⟩
  have heq : n + (j + p) = n + p + j := by omega
  rw [heq] at hne
  exact hne

theorem checkBaseOverlapCerts_spec {M : DFAO} :
    ∀ (p0 : Nat) (cs : List WindowCert),
      checkBaseOverlapCerts M p0 cs = true →
      ∀ (i : Nat) (hi : i < cs.length),
        checkWindowCert M (2 * (p0 + i) + 1) (noOverlapAtPeriod (p0 + i)) (cs.get ⟨i, hi⟩) = true
  | _, [], _, _, hi => by simp at hi
  | p0, c :: cs, h, 0, _ => by
    simp only [checkBaseOverlapCerts, Bool.and_eq_true] at h
    simpa using h.1
  | p0, c :: cs, h, i + 1, hi => by
    simp only [checkBaseOverlapCerts, Bool.and_eq_true] at h
    have ih := checkBaseOverlapCerts_spec (p0 + 1) cs h.2 i (by simp at hi; omega)
    have heq : p0 + 1 + i = p0 + (i + 1) := by omega
    simpa [heq] using ih

theorem reachPar1_spec (M : DFAO) (rp : BTree SyncNode) (h : checkReachPar1 M rp = true) :
    ∀ n : Nat, ∃ idx nd, rp.get? idx = some nd ∧
      nd.parity = decide (n % 2 = 1) ∧ nd.win = stateWindow M 1 n := by
  simp only [checkReachPar1, Bool.and_eq_true] at h
  rcases h with ⟨⟨hwf, hinit⟩, hall⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero =>
      cases h0 : rp.get? 0 with
      | none => simp [h0] at hinit
      | some nd =>
        simp only [h0, Bool.and_eq_true, beq_iff_eq] at hinit
        exact ⟨0, nd, h0, by simpa using hinit.1, hinit.2⟩
    | succ m =>
      rcases ih ((m + 1) / 2) (by omega) with ⟨idx, nd, hget, _hpar, hwin⟩
      have hnd := BTree.all_spec hall idx nd hget
      simp only [Bool.and_eq_true] at hnd
      by_cases hp : (m + 1) % 2 = 0
      · cases hnext : rp.get? nd.next0 with
        | none => simp [hnext] at hnd
        | some nd0 =>
          have h0 := hnd.1.2
          simp only [hnext, Bool.and_eq_true, beq_iff_eq] at h0
          refine ⟨nd.next0, nd0, hnext, ?_, ?_⟩
          · rw [h0.1]; simp [hp]
          · rw [h0.2, hwin, stepWindow_stateWindow hwf false 1]
            have : 2 * ((m + 1) / 2) + 0 = m + 1 := by omega
            simpa using congrArg (stateWindow M 1) this
      · cases hnext : rp.get? nd.next1 with
        | none => simp [hnext] at hnd
        | some nd1 =>
          have h1 := hnd.2
          simp only [hnext, Bool.and_eq_true, beq_iff_eq] at h1
          refine ⟨nd.next1, nd1, hnext, ?_, ?_⟩
          · have hp1 : (m + 1) % 2 = 1 := by omega
            rw [h1.1]; simp [hp1]
          · rw [h1.2, hwin, stepWindow_stateWindow hwf true 1]
            have : 2 * ((m + 1) / 2) + 1 = m + 1 := by omega
            simpa using congrArg (stateWindow M 1) this

/-- Layer 3 General Soundness Meta-Theorem:
    A single finite pure-data `OverlapAvoidCert` proves ∀ n p, p ≥ 1, M is overlap-free. -/
theorem overlapAvoidCert_sound (M : DFAO) (cert : OverlapAvoidCert)
    (h : checkOverlapAvoidCert M cert = true) :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j ≤ p ∧ M.evalWord (n + j) ≠ M.evalWord (n + p + j) := by
  simp only [checkOverlapAvoidCert, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨hsync, hrp⟩, hdec⟩, hblen⟩, hbases⟩
  have hwf : M.wf = true := by
    simp only [checkSyncCert, Bool.and_eq_true] at hsync
    exact hsync.1.1.1
  have hLpos : 0 < cert.syncCert.width := by
    simp only [checkSyncCert, Bool.and_eq_true, decide_eq_true_eq] at hsync
    exact hsync.1.1.2
  -- Extract pair-decoding and parity-conditioned single-bit decoding
  have hpairInv : ∀ a : Nat,
      cert.invPair.getD (M.evalWord (2 * a) * M.numAlpha + M.evalWord (2 * a + 1)) M.numAlpha =
      M.evalWord a := by
    intro a
    rcases reachPar1_spec M cert.reachPar hrp a with ⟨idx, nd, hget, _hpar, hwin⟩
    have hnd := BTree.all_spec hdec idx nd hget
    simp only [Bool.and_eq_true, beq_iff_eq] at hnd
    have hq0 : nd.win.getD 0 0 = M.evalState a := by
      rw [hwin]
      simp [stateWindow]
    rw [hq0] at hnd
    rw [DFAO.evalWord, DFAO.evalWord, DFAO.evalWord, M.evalState_two_mul hwf, M.evalState_two_mul_add_one]
    exact hnd.1
  have hpairInj : ∀ a b : Nat,
      M.evalWord (2 * a) = M.evalWord (2 * b) →
      M.evalWord (2 * a + 1) = M.evalWord (2 * b + 1) →
      M.evalWord a = M.evalWord b := by
    intro a b h0 h1
    rw [← hpairInv a, ← hpairInv b, h0, h1]
  have hparBitInj : ∀ a b : Nat, a % 2 = b % 2 →
      (M.evalWord (2 * a) = M.evalWord (2 * b) → M.evalWord a = M.evalWord b) ∧
      (M.evalWord (2 * a + 1) = M.evalWord (2 * b + 1) → M.evalWord a = M.evalWord b) := by
    intro a b hpar
    rcases reachPar1_spec M cert.reachPar hrp a with ⟨ia, nda, hga, hpa, hwa⟩
    rcases reachPar1_spec M cert.reachPar hrp b with ⟨ib, ndb, hgb, hpb, hwb⟩
    have hda := BTree.all_spec hdec ia nda hga
    have hdb := BTree.all_spec hdec ib ndb hgb
    simp only [Bool.and_eq_true] at hda hdb
    have hqa : nda.win.getD 0 0 = M.evalState a := by
      rw [hwa]
      simp [stateWindow]
    have hqb : ndb.win.getD 0 0 = M.evalState b := by
      rw [hwb]
      simp [stateWindow]
    rw [hqa] at hda
    rw [hqb] at hdb
    by_cases ha0 : a % 2 = 0
    · have hpa' : nda.parity = false := by rw [hpa]; simp [ha0]
      have hpb' : ndb.parity = false := by rw [hpb]; simp [← hpar, ha0]
      have hda2 := hda.2
      have hdb2 := hdb.2
      simp only [hpa', hpb', ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hda2 hdb2
      constructor
      · intro heq
        rw [DFAO.evalWord, DFAO.evalWord, M.evalState_two_mul hwf, M.evalState_two_mul hwf] at heq
        rw [DFAO.evalWord, DFAO.evalWord, ← hda2.1, ← hdb2.1, heq]
      · intro heq
        rw [DFAO.evalWord, DFAO.evalWord, M.evalState_two_mul_add_one, M.evalState_two_mul_add_one] at heq
        rw [DFAO.evalWord, DFAO.evalWord, ← hda2.2, ← hdb2.2, heq]
    · have ha1 : a % 2 = 1 := by omega
      have hpa' : nda.parity = true := by rw [hpa]; simp [ha1]
      have hpb' : ndb.parity = true := by rw [hpb]; simp [← hpar, ha1]
      have hda2 := hda.2
      have hdb2 := hdb.2
      simp [hpa', hpb'] at hda2 hdb2
      constructor
      · intro heq
        rw [DFAO.evalWord, DFAO.evalWord, M.evalState_two_mul hwf, M.evalState_two_mul hwf] at heq
        rw [DFAO.evalWord, DFAO.evalWord, ← hda2.1, ← hdb2.1, heq]
      · intro heq
        rw [DFAO.evalWord, DFAO.evalWord, M.evalState_two_mul_add_one, M.evalState_two_mul_add_one] at heq
        rw [DFAO.evalWord, DFAO.evalWord, ← hda2.2, ← hdb2.2, heq]
  -- Strong induction on period p
  intro n p hp
  induction p using Nat.strongRecOn generalizing n with
  | _ p ih =>
    by_cases hsmall : p < 2 * cert.syncCert.width
    · have hi : p - 1 < cert.baseCerts.length := by omega
      have hbc := checkBaseOverlapCerts_spec 1 cert.baseCerts hbases (p - 1) hi
      have hpEq : 1 + (p - 1) = p := by omega
      rw [hpEq] at hbc
      have hok := windowCert_sound M (2 * p + 1) (noOverlapAtPeriod p) _ hbc n
      exact noOverlapAtPeriod_sound hok
    · apply Classical.byContradiction
      intro hno
      have hall : ∀ j ≤ p, M.evalWord (n + j) = M.evalWord (n + p + j) := by
        intro j hj
        apply Classical.byContradiction
        intro hne
        exact hno ⟨j, hj, hne⟩
      -- Step 1: p ≥ 2*L > L => parity sync forces p = 2*p'
      have hparEq : n % 2 = (n + p) % 2 :=
        syncCert_sound M cert.syncCert hsync n (n + p) (fun j hj => hall j (by omega))
      have hpEven : p % 2 = 0 := by omega
      let p' := p / 2
      have hp'L : cert.syncCert.width ≤ p' := by omega
      have hp'ge : p' ≥ 1 := by omega
      have hp'lt : p' < p := by omega
      -- Step 2: Use pairInj to get length-p' match at distance p', then syncCert forces p' even!
      have hp'Even : p' % 2 = 0 := by
        by_cases hnEven : n % 2 = 0
        · let m := n / 2
          have hpairMatch : ∀ j < cert.syncCert.width, M.evalWord (m + j) = M.evalWord (m + p' + j) := by
            intro j hj
            have h0 := hall (2 * j) (by omega)
            have h1 := hall (2 * j + 1) (by omega)
            have eL0 : n + 2 * j = 2 * (m + j) := by omega
            have eR0 : n + p + 2 * j = 2 * (m + p' + j) := by omega
            have eL1 : n + (2 * j + 1) = 2 * (m + j) + 1 := by omega
            have eR1 : n + p + (2 * j + 1) = 2 * (m + p' + j) + 1 := by omega
            rw [eL0, eR0] at h0
            rw [eL1, eR1] at h1
            exact hpairInj (m + j) (m + p' + j) h0 h1
          have hpm := syncCert_sound M cert.syncCert hsync m (m + p') hpairMatch
          omega
        · let m := n / 2 + 1
          have hpairMatch : ∀ j < cert.syncCert.width, M.evalWord (m + j) = M.evalWord (m + p' + j) := by
            intro j hj
            have h0 := hall (2 * j + 1) (by omega)
            have h1 := hall (2 * j + 2) (by omega)
            have eL0 : n + (2 * j + 1) = 2 * (m + j) := by omega
            have eR0 : n + p + (2 * j + 1) = 2 * (m + p' + j) := by omega
            have eL1 : n + (2 * j + 2) = 2 * (m + j) + 1 := by omega
            have eR1 : n + p + (2 * j + 2) = 2 * (m + p' + j) + 1 := by omega
            rw [eL0, eR0] at h0
            rw [eL1, eR1] at h1
            exact hpairInj (m + j) (m + p' + j) h0 h1
          have hpm := syncCert_sound M cert.syncCert hsync m (m + p') hpairMatch
          omega
      -- Step 3: Since p' is even, (m + i) % 2 = (m + p' + i) % 2, so single-bit halving gives exact overlap at p'!
      let m := n / 2
      rcases ih p' hp'lt m hp'ge with ⟨i, hi, hne⟩
      have h2i : 2 * i ≤ p := by omega
      have hmatch := hall (2 * i) h2i
      have hsamePar : (m + i) % 2 = (m + p' + i) % 2 := by omega
      by_cases hnEven : n % 2 = 0
      · have hL : n + 2 * i = 2 * (m + i) := by omega
        have hR : n + p + 2 * i = 2 * (m + p' + i) := by omega
        rw [hL, hR] at hmatch
        exact hne ((hparBitInj (m + i) (m + p' + i) hsamePar).1 hmatch)
      · have hL : n + 2 * i = 2 * (m + i) + 1 := by omega
        have hR : n + p + 2 * i = 2 * (m + p' + i) + 1 := by omega
        rw [hL, hR] at hmatch
        exact hne ((hparBitInj (m + i) (m + p' + i) hsamePar).2 hmatch)

-- ============================================================================
-- Section 7: Abelian Sliding-Window Sum Helper
-- ============================================================================

def listSum (xs : List Nat) : Nat := xs.foldl (· + ·) 0

def windowWeightInRange (lo hi : Nat) (outWin : List Nat) : Bool :=
  let s := listSum outWin
  decide (lo ≤ s) && decide (s ≤ hi)

theorem listSum_eq_sum_range (f : Nat → Nat) :
    ∀ W : Nat, listSum ((List.range W).map f) =
      (List.range W).foldl (fun acc i => acc + f i) 0 := by
  intro W
  simp [listSum, List.foldl_map]

def windowSum (f : Nat → Nat) (W n : Nat) : Nat :=
  listSum ((List.range W).map (fun i => f (n + i)))

theorem windowWeightInRange_sound {M : DFAO} {W lo hi n : Nat}
    (h : windowWeightInRange lo hi (outputWindow M W n) = true) :
    lo ≤ windowSum M.evalWord W n ∧ windowSum M.evalWord W n ≤ hi := by
  simp only [windowWeightInRange, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

-- ============================================================================
-- Section 8: Pure-Data DFAOs, Carry-Offset Tables & Certificates
-- ============================================================================

-- AUTO-GENERATED PURE-DATA DFAOs, STATE VECTORS & CERTIFICATES
def dfao_carryXor3 : DFAO :=
  { numStates := 6, numAlpha := 2, q0 := 0,
    d0 := [0, 2, 2, 4, 0, 1],
    d1 := [1, 3, 4, 3, 5, 5],
    tau := [0, 1, 1, 0, 0, 1] }

def dfao_carryAnd3 : DFAO :=
  { numStates := 6, numAlpha := 2, q0 := 0,
    d0 := [0, 2, 3, 3, 0, 4],
    d1 := [1, 2, 4, 5, 2, 4],
    tau := [0, 1, 1, 1, 0, 0] }

def dfao_carryAnd5 : DFAO :=
  { numStates := 10, numAlpha := 2, q0 := 0,
    d0 := [0, 2, 4, 6, 8, 2, 0, 3, 8, 3],
    d1 := [1, 3, 5, 7, 7, 7, 5, 5, 9, 2],
    tau := [0, 1, 1, 0, 1, 1, 0, 0, 1, 0] }

def dfao_carryXor5 : DFAO :=
  { numStates := 12, numAlpha := 2, q0 := 0,
    d0 := [0, 2, 4, 6, 7, 2, 0, 7, 10, 10, 6, 4],
    d1 := [1, 3, 5, 3, 8, 9, 5, 9, 1, 11, 8, 11],
    tau := [0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1] }

def dfao_grayMod4 : DFAO :=
  { numStates := 4, numAlpha := 4, q0 := 0,
    d0 := [0, 2, 2, 0],
    d1 := [1, 1, 3, 3],
    tau := [0, 1, 2, 3] }

def vecTable_carryXor3 : List (List Nat) :=
  [[0, 1, 1], [1, 0, 1], [1, 0, 0], [0, 0, 1], [0, 1, 0], [1, 1, 0]]

def vecTable_carryAnd3 : List (List Nat) :=
  [[0, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 0, 1], [0, 1, 0]]

def vecTable_carryAnd5 : List (List Nat) :=
  [[0, 0, 0, 0, 0], [1, 0, 1, 0, 1], [1, 1, 0, 0, 1], [0, 0, 1, 1, 0], [1, 1, 1, 1, 0], [1, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 1, 0, 0, 1], [1, 1, 1, 1, 1], [0, 1, 0, 1, 0]]

def vecTable_carryXor5 : List (List Nat) :=
  [[0, 1, 1, 0, 1], [1, 1, 0, 0, 1], [1, 0, 1, 0, 0], [0, 1, 0, 0, 1], [1, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 1, 1, 0, 0], [1, 0, 0, 1, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [0, 1, 0, 1, 1], [1, 0, 1, 1, 0]]

def cert_carryXor3_k4 : PowerAvoidCert :=
  { syncCert := { width := 7, parityMask := 0xd009002404030000c0202400900b00, graph := (.node (.node (.node (.node (.node (.node (.leaf ⟨false, [0, 1, 2, 3, 2, 4, 4], 0, 1⟩) (.leaf ⟨false, [2, 3, 2, 3, 1, 5, 0], 39, 40⟩)) (.leaf ⟨true, [4, 0, 5, 0, 1, 1, 5], 17, 18⟩)) (.node (.node (.leaf ⟨false, [2, 4, 0, 5, 0, 5, 4], 15, 16⟩) (.leaf ⟨true, [4, 4, 3, 2, 4, 4, 3], 10, 11⟩)) (.leaf ⟨true, [1, 1, 5, 0, 5, 4, 3], 32, 33⟩))) (.node (.node (.node (.leaf ⟨false, [2, 4, 4, 3, 2, 4, 0], 8, 9⟩) (.leaf ⟨false, [2, 3, 1, 5, 0, 1, 1], 43, 44⟩)) (.leaf ⟨true, [1, 1, 5, 0, 1, 1, 5], 32, 33⟩)) (.node (.node (.leaf ⟨false, [0, 5, 4, 3, 2, 4, 0], 23, 24⟩) (.leaf ⟨true, [4, 4, 3, 2, 3, 1, 5], 10, 11⟩)) (.leaf ⟨false, [1, 5, 0, 1, 2, 3, 2], 34, 35⟩)))) (.node (.node (.node (.node (.leaf ⟨false, [2, 3, 2, 4, 4, 3, 2], 4, 5⟩) (.leaf ⟨false, [2, 3, 1, 5, 0, 1, 2], 43, 44⟩)) (.leaf ⟨true, [5, 0, 1, 1, 5, 0, 1], 28, 29⟩)) (.node (.node (.leaf ⟨false, [0, 5, 0, 5, 4, 3, 2], 19, 20⟩) (.leaf ⟨true, [3, 2, 4, 4, 3, 2, 3], 6, 7⟩)) (.leaf ⟨false, [0, 1, 1, 5, 0, 1, 2], 30, 31⟩))) (.node (.node (.node (.leaf ⟨false, [4, 3, 2, 4, 0, 5, 0], 12, 13⟩) (.leaf ⟨true, [5, 0, 1, 2, 3, 2, 4], 28, 38⟩)) (.leaf ⟨true, [5, 0, 1, 1, 5, 0, 5], 28, 29⟩)) (.node (.node (.leaf ⟨true, [3, 2, 4, 0, 5, 0, 1], 6, 14⟩) (.leaf ⟨false, [0, 5, 4, 3, 2, 4, 4], 23, 24⟩)) (.leaf ⟨false, [0, 1, 2, 3, 2, 3, 1], 0, 1⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨true, [1, 2, 3, 2, 4, 4, 3], 2, 3⟩) (.leaf ⟨true, [3, 2, 3, 1, 5, 0, 1], 41, 42⟩)) (.leaf ⟨false, [0, 5, 0, 1, 1, 5, 0], 26, 27⟩)) (.node (.node (.leaf ⟨true, [4, 0, 5, 0, 5, 4, 3], 17, 18⟩) (.leaf ⟨false, [4, 3, 2, 4, 4, 3, 2], 12, 13⟩)) (.leaf ⟨false, [1, 5, 0, 5, 4, 3, 2], 36, 37⟩))) (.node (.node (.node (.leaf ⟨true, [4, 4, 3, 2, 4, 0, 5], 10, 11⟩) (.leaf ⟨true, [3, 1, 5, 0, 1, 1, 5], 45, 33⟩)) (.leaf ⟨false, [1, 5, 0, 1, 1, 5, 0], 34, 35⟩)) (.node (.node (.leaf ⟨true, [5, 4, 3, 2, 4, 0, 5], 25, 11⟩) (.leaf ⟨false, [4, 3, 2, 3, 1, 5, 0], 46, 47⟩)) (.leaf ⟨true, [5, 0, 1, 2, 3, 2, 3], 28, 38⟩)))) (.node (.node (.node (.node (.leaf ⟨true, [3, 2, 4, 4, 3, 2, 4], 6, 7⟩) (.leaf ⟨true, [3, 1, 5, 0, 1, 2, 3], 45, 33⟩)) (.leaf ⟨false, [0, 1, 1, 5, 0, 1, 1], 30, 31⟩)) (.node (.node (.leaf ⟨true, [5, 0, 5, 4, 3, 2, 4], 21, 22⟩) (.leaf ⟨false, [2, 4, 4, 3, 2, 3, 1], 8, 9⟩)) (.leaf ⟨true, [1, 1, 5, 0, 1, 2, 3], 32, 33⟩))) (.node (.node (.node (.leaf ⟨true, [3, 2, 4, 0, 5, 0, 5], 6, 14⟩) (.leaf ⟨false, [2, 4, 4, 3, 2, 4, 4], 8, 9⟩)) (.leaf ⟨false, [0, 1, 1, 5, 0, 5, 4], 30, 31⟩)) (.node (.node (.leaf ⟨false, [2, 4, 0, 5, 0, 1, 1], 15, 16⟩) (.leaf ⟨true, [5, 4, 3, 2, 4, 4, 3], 25, 11⟩)) (.leaf ⟨true, [1, 2, 3, 2, 3, 1, 5], 2, 3⟩)))))) },
    invEven := [0, 1],
    reachCert := { graph := (.node (.node (.node (.leaf ⟨[0], 0, 1⟩) (.leaf ⟨[4], 0, 5⟩)) (.leaf ⟨[2], 2, 4⟩)) (.node (.node (.leaf ⟨[1], 2, 3⟩) (.leaf ⟨[5], 1, 5⟩)) (.leaf ⟨[3], 4, 3⟩))) },
    baseCerts := [{ graph := (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3], 0, 1⟩) (.leaf ⟨[0, 1, 1, 5], 0, 1⟩)) (.node (.leaf ⟨[2, 4, 0, 5], 8, 9⟩) (.leaf ⟨[3, 1, 5, 0], 25, 22⟩))) (.node (.node (.leaf ⟨[2, 4, 4, 3], 8, 9⟩) (.leaf ⟨[5, 0, 1, 2], 18, 20⟩)) (.leaf ⟨[0, 5, 4, 3], 16, 17⟩))) (.node (.node (.node (.leaf ⟨[2, 3, 2, 4], 4, 5⟩) (.leaf ⟨[1, 5, 0, 1], 23, 24⟩)) (.leaf ⟨[0, 5, 0, 5], 16, 17⟩)) (.node (.node (.leaf ⟨[4, 3, 2, 4], 12, 13⟩) (.leaf ⟨[3, 2, 3, 1], 6, 3⟩)) (.leaf ⟨[0, 5, 0, 1], 16, 17⟩)))) (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 2], 2, 3⟩) (.leaf ⟨[1, 1, 5, 0], 21, 22⟩)) (.node (.leaf ⟨[4, 0, 5, 0], 14, 15⟩) (.leaf ⟨[4, 3, 2, 3], 12, 13⟩))) (.node (.node (.leaf ⟨[4, 4, 3, 2], 10, 11⟩) (.leaf ⟨[2, 3, 2, 3], 4, 5⟩)) (.leaf ⟨[5, 4, 3, 2], 19, 11⟩))) (.node (.node (.node (.leaf ⟨[3, 2, 4, 4], 6, 7⟩) (.leaf ⟨[1, 5, 0, 5], 23, 24⟩)) (.leaf ⟨[5, 0, 5, 4], 18, 15⟩)) (.node (.node (.leaf ⟨[3, 2, 4, 0], 6, 7⟩) (.leaf ⟨[2, 3, 1, 5], 4, 5⟩)) (.leaf ⟨[5, 0, 1, 1], 18, 20⟩))))) }, { graph := (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3, 2, 4, 4, 3], 0, 1⟩) (.leaf ⟨[0, 1, 2, 3, 2, 3, 1, 5], 0, 1⟩)) (.node (.leaf ⟨[2, 4, 0, 5, 0, 1, 1, 5], 16, 17⟩) (.leaf ⟨[2, 4, 4, 3, 2, 3, 1, 5], 8, 9⟩))) (.node (.node (.leaf ⟨[2, 4, 0, 5, 0, 5, 4, 3], 16, 17⟩) (.leaf ⟨[3, 1, 5, 0, 1, 1, 5, 0], 50, 35⟩)) (.leaf ⟨[0, 1, 1, 5, 0, 5, 4, 3], 32, 33⟩))) (.node (.node (.node (.leaf ⟨[2, 4, 4, 3, 2, 4, 0, 5], 8, 9⟩) (.leaf ⟨[2, 3, 1, 5, 0, 1, 2, 3], 48, 49⟩)) (.node (.leaf ⟨[0, 1, 1, 5, 0, 1, 1, 5], 32, 33⟩) (.leaf ⟨[0, 5, 4, 3, 2, 4, 4, 3], 24, 25⟩))) (.node (.node (.leaf ⟨[0, 5, 4, 3, 2, 4, 0, 5], 24, 25⟩) (.leaf ⟨[2, 4, 4, 3, 2, 4, 4, 3], 8, 9⟩)) (.leaf ⟨[0, 1, 1, 5, 0, 1, 2, 3], 32, 33⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 3, 2, 4, 4, 3, 2, 4], 4, 5⟩) (.leaf ⟨[2, 3, 2, 3, 1, 5, 0, 1], 44, 45⟩)) (.node (.leaf ⟨[0, 5, 0, 1, 1, 5, 0, 1], 28, 29⟩) (.leaf ⟨[4, 3, 2, 3, 1, 5, 0, 1], 52, 53⟩))) (.node (.node (.leaf ⟨[0, 5, 0, 5, 4, 3, 2, 4], 20, 21⟩) (.leaf ⟨[5, 0, 1, 2, 3, 2, 4, 4], 41, 42⟩)) (.leaf ⟨[1, 5, 0, 5, 4, 3, 2, 4], 39, 40⟩))) (.node (.node (.node (.leaf ⟨[4, 3, 2, 4, 0, 5, 0, 5], 12, 13⟩) (.leaf ⟨[3, 2, 3, 1, 5, 0, 1, 1], 46, 47⟩)) (.leaf ⟨[1, 5, 0, 1, 1, 5, 0, 5], 36, 37⟩)) (.node (.node (.leaf ⟨[4, 3, 2, 4, 0, 5, 0, 1], 12, 13⟩) (.leaf ⟨[4, 3, 2, 4, 4, 3, 2, 3], 12, 13⟩)) (.leaf ⟨[1, 5, 0, 1, 2, 3, 2, 3], 36, 37⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 2, 4, 4, 3, 2], 2, 3⟩) (.leaf ⟨[1, 2, 3, 2, 3, 1, 5, 0], 2, 43⟩)) (.node (.leaf ⟨[4, 0, 5, 0, 1, 1, 5, 0], 18, 27⟩) (.leaf ⟨[4, 4, 3, 2, 3, 1, 5, 0], 10, 51⟩))) (.node (.node (.leaf ⟨[4, 0, 5, 0, 5, 4, 3, 2], 18, 19⟩) (.leaf ⟨[1, 5, 0, 1, 2, 3, 2, 4], 36, 37⟩)) (.leaf ⟨[1, 1, 5, 0, 5, 4, 3, 2], 34, 38⟩))) (.node (.node (.node (.leaf ⟨[4, 4, 3, 2, 4, 0, 5, 0], 10, 11⟩) (.leaf ⟨[3, 1, 5, 0, 1, 2, 3, 2], 50, 35⟩)) (.node (.leaf ⟨[1, 1, 5, 0, 1, 1, 5, 0], 34, 35⟩) (.leaf ⟨[5, 4, 3, 2, 4, 4, 3, 2], 26, 11⟩))) (.node (.node (.leaf ⟨[5, 4, 3, 2, 4, 0, 5, 0], 26, 11⟩) (.leaf ⟨[4, 4, 3, 2, 4, 4, 3, 2], 10, 11⟩)) (.leaf ⟨[1, 1, 5, 0, 1, 2, 3, 2], 34, 35⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 2, 4, 4, 3, 2, 4, 0], 6, 7⟩) (.leaf ⟨[3, 2, 3, 1, 5, 0, 1, 2], 46, 47⟩)) (.node (.leaf ⟨[5, 0, 1, 1, 5, 0, 1, 1], 30, 31⟩) (.leaf ⟨[5, 0, 5, 4, 3, 2, 4, 4], 22, 23⟩))) (.node (.node (.leaf ⟨[5, 0, 5, 4, 3, 2, 4, 0], 22, 23⟩) (.leaf ⟨[3, 2, 4, 4, 3, 2, 4, 4], 6, 7⟩)) (.leaf ⟨[5, 0, 1, 1, 5, 0, 1, 2], 30, 31⟩))) (.node (.node (.node (.leaf ⟨[3, 2, 4, 0, 5, 0, 5, 4], 14, 15⟩) (.leaf ⟨[2, 3, 1, 5, 0, 1, 1, 5], 48, 49⟩)) (.leaf ⟨[5, 0, 1, 1, 5, 0, 5, 4], 30, 31⟩)) (.node (.node (.leaf ⟨[3, 2, 4, 0, 5, 0, 1, 1], 14, 15⟩) (.leaf ⟨[3, 2, 4, 4, 3, 2, 3, 1], 6, 7⟩)) (.leaf ⟨[5, 0, 1, 2, 3, 2, 3, 1], 41, 42⟩)))))) }] }

def cert_carryAnd3_k5 : PowerAvoidCert :=
  { syncCert := { width := 6, parityMask := 0x303d98000019bc0c, graph := (.node (.node (.node (.node (.node (.node (.leaf ⟨false, [0, 1, 2, 2, 3, 4], 0, 1⟩) (.leaf ⟨true, [1, 2, 2, 3, 5, 0], 2, 3⟩)) (.leaf ⟨true, [5, 4, 4, 0, 1, 3], 25, 26⟩)) (.node (.node (.leaf ⟨false, [3, 5, 0, 2, 3, 5], 15, 16⟩) (.leaf ⟨true, [4, 0, 1, 3, 4, 0], 29, 30⟩)) (.leaf ⟨true, [5, 4, 4, 0, 2, 0], 25, 26⟩))) (.node (.node (.node (.leaf ⟨false, [3, 4, 3, 4, 3, 5], 8, 9⟩) (.leaf ⟨true, [2, 0, 1, 3, 4, 0], 42, 43⟩)) (.leaf ⟨true, [1, 3, 4, 3, 5, 4], 33, 11⟩)) (.node (.node (.leaf ⟨true, [5, 0, 2, 3, 5, 4], 17, 18⟩) (.leaf ⟨true, [4, 3, 4, 3, 5, 4], 10, 11⟩)) (.leaf ⟨true, [2, 0, 2, 0, 1, 2], 39, 40⟩)))) (.node (.node (.node (.node (.leaf ⟨false, [2, 2, 3, 4, 3, 4], 4, 5⟩) (.leaf ⟨true, [2, 0, 2, 0, 1, 3], 39, 40⟩)) (.leaf ⟨true, [4, 0, 1, 3, 4, 3], 29, 30⟩)) (.node (.node (.leaf ⟨false, [0, 2, 3, 5, 0, 2], 19, 20⟩) (.leaf ⟨false, [3, 4, 0, 1, 2, 2], 46, 47⟩)) (.leaf ⟨true, [4, 0, 2, 0, 2, 0], 35, 36⟩))) (.node (.node (.node (.leaf ⟨false, [3, 4, 3, 5, 0, 2], 8, 12⟩) (.leaf ⟨true, [1, 3, 4, 0, 1, 3], 33, 45⟩)) (.leaf ⟨true, [4, 3, 5, 4, 4, 0], 13, 14⟩)) (.node (.node (.leaf ⟨true, [2, 3, 5, 4, 4, 0], 21, 22⟩) (.leaf ⟨false, [3, 5, 0, 2, 0, 1], 15, 16⟩)) (.leaf ⟨true, [2, 0, 1, 2, 2, 3], 42, 43⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨true, [1, 2, 2, 3, 4, 3], 2, 3⟩) (.leaf ⟨false, [2, 2, 3, 5, 0, 2], 4, 44⟩)) (.leaf ⟨false, [4, 4, 0, 1, 3, 4], 27, 28⟩)) (.node (.node (.leaf ⟨true, [5, 0, 2, 3, 5, 0], 17, 18⟩) (.leaf ⟨true, [1, 3, 4, 0, 1, 2], 33, 45⟩)) (.leaf ⟨false, [4, 4, 0, 2, 0, 2], 27, 34⟩))) (.node (.node (.node (.leaf ⟨true, [4, 3, 4, 3, 5, 0], 10, 11⟩) (.leaf ⟨false, [0, 1, 3, 4, 0, 1], 31, 32⟩)) (.leaf ⟨false, [3, 4, 3, 5, 4, 4], 8, 12⟩)) (.node (.node (.leaf ⟨false, [0, 2, 3, 5, 4, 4], 19, 20⟩) (.leaf ⟨true, [2, 3, 5, 0, 2, 0], 21, 22⟩)) (.leaf ⟨false, [0, 2, 0, 1, 2, 2], 37, 41⟩)))) (.node (.node (.node (.node (.leaf ⟨true, [2, 3, 4, 3, 4, 3], 6, 7⟩) (.leaf ⟨false, [0, 2, 0, 1, 3, 4], 37, 41⟩)) (.leaf ⟨false, [0, 1, 3, 4, 3, 5], 31, 32⟩)) (.node (.node (.leaf ⟨true, [2, 3, 5, 0, 2, 3], 21, 22⟩) (.leaf ⟨true, [4, 0, 1, 2, 2, 3], 29, 30⟩)) (.leaf ⟨false, [0, 2, 0, 2, 0, 1], 37, 38⟩))) (.node (.node (.node (.leaf ⟨true, [4, 3, 5, 0, 2, 3], 13, 14⟩) (.leaf ⟨false, [3, 4, 0, 1, 3, 4], 46, 47⟩)) (.leaf ⟨false, [3, 5, 4, 4, 0, 2], 23, 24⟩)) (.node (.node (.leaf ⟨false, [3, 5, 4, 4, 0, 1], 23, 24⟩) (.leaf ⟨true, [5, 0, 2, 0, 1, 2], 17, 40⟩)) (.leaf ⟨false, [0, 1, 2, 2, 3, 5], 0, 1⟩)))))) },
    invEven := [0, 1],
    reachCert := { graph := (.node (.node (.node (.leaf ⟨[0], 0, 1⟩) (.leaf ⟨[4], 0, 2⟩)) (.leaf ⟨[2], 3, 4⟩)) (.node (.node (.leaf ⟨[1], 2, 2⟩) (.leaf ⟨[5], 4, 4⟩)) (.leaf ⟨[3], 3, 5⟩))) },
    baseCerts := [{ graph := (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 2, 3], 0, 1⟩) (.leaf ⟨[2, 0, 1, 3, 4], 36, 37⟩)) (.leaf ⟨[4, 4, 0, 1, 3], 25, 26⟩)) (.node (.leaf ⟨[3, 5, 0, 2, 3], 14, 15⟩) (.leaf ⟨[4, 0, 2, 0, 2], 31, 32⟩))) (.node (.node (.node (.leaf ⟨[3, 4, 3, 4, 3], 8, 9⟩) (.leaf ⟨[3, 4, 0, 1, 2], 38, 39⟩)) (.leaf ⟨[3, 4, 3, 5, 4], 8, 9⟩)) (.node (.leaf ⟨[0, 2, 3, 5, 4], 18, 19⟩) (.leaf ⟨[2, 0, 1, 2, 2], 36, 37⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 2, 3, 4, 3], 4, 5⟩) (.leaf ⟨[1, 3, 4, 0, 1], 30, 11⟩)) (.leaf ⟨[0, 1, 3, 4, 3], 0, 29⟩)) (.node (.leaf ⟨[0, 2, 3, 5, 0], 18, 19⟩) (.leaf ⟨[2, 0, 2, 0, 1], 35, 17⟩))) (.node (.node (.node (.leaf ⟨[3, 4, 3, 5, 0], 8, 9⟩) (.leaf ⟨[3, 5, 0, 2, 0], 14, 15⟩)) (.leaf ⟨[5, 4, 4, 0, 2], 23, 24⟩)) (.node (.leaf ⟨[3, 5, 4, 4, 0], 14, 22⟩) (.leaf ⟨[2, 2, 3, 5, 0], 4, 5⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 2, 3, 4], 2, 3⟩) (.leaf ⟨[0, 1, 3, 4, 0], 0, 29⟩)) (.leaf ⟨[4, 0, 1, 3, 4], 27, 28⟩)) (.node (.leaf ⟨[5, 0, 2, 3, 5], 16, 17⟩) (.leaf ⟨[0, 2, 0, 2, 0], 33, 34⟩))) (.node (.node (.node (.leaf ⟨[4, 3, 4, 3, 5], 10, 11⟩) (.leaf ⟨[4, 0, 1, 2, 2], 27, 28⟩)) (.leaf ⟨[4, 3, 5, 4, 4], 12, 13⟩)) (.node (.leaf ⟨[2, 3, 5, 4, 4], 20, 21⟩) (.leaf ⟨[1, 2, 2, 3, 5], 2, 3⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 3, 4], 6, 7⟩) (.leaf ⟨[3, 4, 0, 1, 3], 38, 39⟩)) (.leaf ⟨[1, 3, 4, 3, 5], 30, 11⟩)) (.node (.leaf ⟨[2, 3, 5, 0, 2], 20, 21⟩) (.leaf ⟨[0, 2, 0, 1, 2], 33, 34⟩))) (.node (.node (.node (.leaf ⟨[4, 3, 5, 0, 2], 12, 13⟩) (.leaf ⟨[5, 0, 2, 0, 1], 16, 17⟩)) (.leaf ⟨[4, 4, 0, 2, 0], 25, 26⟩)) (.node (.leaf ⟨[5, 4, 4, 0, 1], 23, 24⟩) (.leaf ⟨[0, 2, 0, 1, 3], 33, 34⟩)))))) }] }

def cert_carryAnd5_k4 : PowerAvoidCert :=
  { syncCert := { width := 10, parityMask := 0xc3800000000000000042000001000040000600030000000001800060842200c5240000000000000000800001600000000000000000000000000000000000000006800001000000000000000024a30044210600018000000000c0006000020000800000420000000000000001c30000000000000000000, graph := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 7], 0, 1⟩) (.leaf ⟨true, [7, 8, 9, 3, 5, 4, 5, 3, 5, 0], 130, 131⟩)) (.leaf ⟨false, [8, 9, 3, 2, 6, 7, 4, 5, 0, 5], 64, 65⟩)) (.node (.leaf ⟨false, [8, 9, 3, 2, 6, 7, 2, 7, 8, 7], 64, 65⟩) (.leaf ⟨true, [7, 0, 1, 2, 7, 6, 7, 2, 7, 8], 121, 122⟩))) (.node (.node (.leaf ⟨false, [8, 9, 3, 5, 4, 5, 3, 5, 0, 1], 32, 33⟩) (.leaf ⟨true, [5, 3, 5, 4, 5, 3, 5, 0, 1, 2], 99, 100⟩)) (.node (.leaf ⟨false, [0, 1, 2, 3, 4, 5, 3, 5, 0, 5], 0, 1⟩) (.leaf ⟨false, [0, 5, 3, 5, 8, 7, 2, 7, 0, 1], 24, 25⟩)))) (.node (.node (.node (.leaf ⟨false, [8, 7, 2, 7, 0, 5, 3, 5, 8, 9], 16, 17⟩) (.leaf ⟨true, [5, 4, 5, 3, 5, 8, 9, 3, 5, 4], 38, 101⟩)) (.node (.leaf ⟨false, [8, 7, 2, 7, 6, 7, 2, 7, 0, 1], 74, 75⟩) (.leaf ⟨true, [7, 2, 7, 8, 9, 3, 2, 6, 7, 4], 58, 59⟩))) (.node (.node (.leaf ⟨false, [0, 1, 2, 7, 6, 7, 2, 7, 8, 9], 48, 49⟩) (.leaf ⟨false, [4, 5, 6, 7, 8, 7, 2, 7, 6, 7], 8, 9⟩)) (.node (.leaf ⟨false, [0, 5, 3, 5, 4, 5, 3, 5, 8, 9], 97, 98⟩) (.leaf ⟨true, [5, 3, 5, 0, 1, 2, 3, 4, 5, 3], 42, 43⟩))))) (.node (.node (.node (.node (.leaf ⟨false, [4, 5, 6, 7, 8, 7, 2, 7, 0, 5], 8, 9⟩) (.leaf ⟨false, [6, 7, 4, 5, 0, 5, 3, 5, 4, 5], 112, 113⟩)) (.node (.leaf ⟨false, [6, 7, 2, 7, 8, 7, 2, 7, 6, 7], 56, 57⟩) (.leaf ⟨true, [7, 6, 7, 2, 7, 8, 7, 2, 7, 6], 54, 55⟩))) (.node (.node (.leaf ⟨false, [4, 5, 3, 5, 0, 1, 2, 7, 6, 7], 40, 41⟩) (.leaf ⟨true, [5, 3, 5, 0, 1, 2, 3, 4, 5, 6], 42, 43⟩)) (.node (.leaf ⟨false, [4, 5, 3, 5, 0, 5, 3, 5, 4, 5], 40, 41⟩) (.leaf ⟨false, [8, 7, 2, 7, 0, 1, 2, 7, 6, 7], 16, 17⟩)))) (.node (.node (.node (.leaf ⟨false, [0, 5, 3, 5, 8, 9, 3, 5, 4, 5], 24, 25⟩) (.leaf ⟨false, [3, 5, 4, 5, 3, 5, 0, 5, 3, 5], 36, 37⟩)) (.node (.leaf ⟨false, [6, 7, 2, 7, 0, 1, 2, 3, 4, 5], 79, 80⟩) (.leaf ⟨false, [6, 7, 4, 5, 0, 5, 3, 5, 8, 7], 112, 113⟩))) (.node (.node (.leaf ⟨false, [6, 7, 2, 7, 8, 9, 3, 2, 6, 7], 56, 57⟩) (.leaf ⟨true, [7, 6, 7, 2, 7, 0, 1, 2, 7, 6], 54, 78⟩)) (.node (.leaf ⟨false, [4, 5, 3, 5, 8, 9, 3, 2, 6, 7], 102, 103⟩) (.leaf ⟨true, [7, 6, 7, 2, 7, 8, 9, 3, 5, 4], 54, 55⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨false, [2, 3, 4, 5, 6, 7, 8, 7, 2, 7], 4, 5⟩) (.leaf ⟨false, [3, 5, 8, 9, 3, 2, 6, 7, 2, 7], 28, 104⟩)) (.leaf ⟨false, [3, 2, 6, 7, 4, 5, 0, 5, 3, 5], 108, 109⟩)) (.node (.leaf ⟨false, [3, 2, 6, 7, 2, 7, 8, 7, 2, 7], 68, 69⟩) (.leaf ⟨true, [1, 2, 7, 6, 7, 2, 7, 8, 7, 2], 50, 51⟩))) (.node (.node (.leaf ⟨false, [3, 5, 4, 5, 3, 5, 0, 1, 2, 7], 36, 37⟩) (.leaf ⟨true, [5, 4, 5, 3, 5, 0, 1, 2, 3, 4], 38, 39⟩)) (.node (.leaf ⟨false, [2, 3, 4, 5, 3, 5, 0, 5, 3, 5], 88, 89⟩) (.leaf ⟨false, [3, 5, 8, 7, 2, 7, 0, 1, 2, 7], 125, 126⟩)))) (.node (.node (.node (.leaf ⟨false, [2, 7, 0, 5, 3, 5, 8, 9, 3, 5], 20, 21⟩) (.leaf ⟨false, [8, 9, 3, 5, 4, 5, 3, 5, 0, 5], 32, 33⟩)) (.node (.leaf ⟨false, [2, 7, 6, 7, 2, 7, 0, 1, 2, 3], 52, 53⟩) (.leaf ⟨true, [7, 8, 9, 3, 2, 6, 7, 4, 5, 0], 62, 63⟩))) (.node (.node (.leaf ⟨false, [2, 7, 6, 7, 2, 7, 8, 9, 3, 2], 52, 53⟩) (.leaf ⟨false, [6, 7, 8, 7, 2, 7, 6, 7, 2, 7], 12, 13⟩)) (.node (.leaf ⟨false, [3, 5, 4, 5, 3, 5, 8, 9, 3, 2], 36, 37⟩) (.leaf ⟨true, [5, 0, 1, 2, 3, 4, 5, 3, 5, 0], 118, 119⟩))))) (.node (.node (.node (.node (.leaf ⟨false, [6, 7, 8, 7, 2, 7, 0, 5, 3, 5], 12, 13⟩) (.leaf ⟨false, [4, 5, 0, 5, 3, 5, 4, 5, 3, 5], 116, 94⟩)) (.node (.leaf ⟨false, [2, 7, 8, 7, 2, 7, 6, 7, 2, 7], 73, 13⟩) (.leaf ⟨false, [8, 7, 2, 7, 6, 7, 2, 7, 8, 9], 74, 75⟩))) (.node (.node (.leaf ⟨false, [3, 5, 0, 1, 2, 7, 6, 7, 2, 7], 44, 45⟩) (.leaf ⟨true, [5, 0, 1, 2, 3, 4, 5, 6, 7, 8], 118, 119⟩)) (.node (.leaf ⟨false, [3, 5, 0, 5, 3, 5, 4, 5, 3, 5], 93, 94⟩) (.leaf ⟨false, [2, 7, 0, 1, 2, 3, 4, 5, 6, 7], 83, 84⟩)))) (.node (.node (.node (.leaf ⟨false, [3, 5, 8, 9, 3, 5, 4, 5, 3, 5], 28, 29⟩) (.leaf ⟨true, [5, 0, 5, 3, 5, 4, 5, 3, 5, 0], 95, 96⟩)) (.node (.leaf ⟨false, [2, 7, 0, 1, 2, 3, 4, 5, 3, 5], 83, 84⟩) (.leaf ⟨false, [4, 5, 0, 5, 3, 5, 8, 7, 2, 7], 116, 94⟩))) (.node (.node (.leaf ⟨false, [2, 7, 8, 9, 3, 2, 6, 7, 2, 7], 60, 61⟩) (.leaf ⟨true, [7, 2, 7, 0, 1, 2, 7, 6, 7, 2], 81, 82⟩)) (.node (.leaf ⟨false, [3, 5, 8, 9, 3, 2, 6, 7, 4, 5], 28, 104⟩) (.leaf ⟨true, [7, 2, 7, 8, 9, 3, 5, 4, 5, 3], 58, 59⟩))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨true, [1, 2, 3, 4, 5, 6, 7, 8, 7, 2], 2, 3⟩) (.leaf ⟨true, [5, 3, 5, 8, 9, 3, 2, 6, 7, 2], 26, 27⟩)) (.leaf ⟨true, [9, 3, 2, 6, 7, 4, 5, 0, 5, 3], 66, 107⟩)) (.node (.leaf ⟨true, [9, 3, 2, 6, 7, 2, 7, 8, 7, 2], 66, 67⟩) (.leaf ⟨false, [0, 1, 2, 7, 6, 7, 2, 7, 8, 7], 48, 49⟩))) (.node (.node (.leaf ⟨true, [9, 3, 5, 4, 5, 3, 5, 0, 1, 2], 34, 35⟩) (.leaf ⟨false, [3, 5, 4, 5, 3, 5, 0, 1, 2, 3], 36, 37⟩)) (.node (.leaf ⟨true, [1, 2, 3, 4, 5, 3, 5, 0, 5, 3], 2, 87⟩) (.leaf ⟨true, [5, 3, 5, 8, 7, 2, 7, 0, 1, 2], 123, 124⟩)))) (.node (.node (.node (.leaf ⟨true, [7, 2, 7, 0, 5, 3, 5, 8, 9, 3], 18, 19⟩) (.leaf ⟨false, [4, 5, 3, 5, 8, 9, 3, 5, 4, 5], 102, 103⟩)) (.node (.leaf ⟨true, [7, 2, 7, 6, 7, 2, 7, 0, 1, 2], 76, 77⟩) (.leaf ⟨false, [2, 7, 8, 9, 3, 2, 6, 7, 4, 5], 60, 61⟩))) (.node (.node (.leaf ⟨true, [1, 2, 7, 6, 7, 2, 7, 8, 9, 3], 50, 51⟩) (.leaf ⟨true, [5, 6, 7, 8, 7, 2, 7, 6, 7, 2], 10, 11⟩)) (.node (.leaf ⟨true, [5, 3, 5, 4, 5, 3, 5, 8, 9, 3], 99, 100⟩) (.leaf ⟨false, [3, 5, 0, 1, 2, 3, 4, 5, 3, 5], 44, 117⟩))))) (.node (.node (.node (.node (.leaf ⟨true, [5, 6, 7, 8, 7, 2, 7, 0, 5, 3], 10, 11⟩) (.leaf ⟨true, [7, 4, 5, 0, 5, 3, 5, 4, 5, 3], 114, 115⟩)) (.node (.leaf ⟨true, [7, 2, 7, 8, 7, 2, 7, 6, 7, 2], 71, 72⟩) (.leaf ⟨true, [7, 8, 7, 2, 7, 6, 7, 2, 7, 8], 14, 15⟩))) (.node (.node (.leaf ⟨true, [5, 3, 5, 0, 1, 2, 7, 6, 7, 2], 42, 43⟩) (.leaf ⟨false, [3, 5, 0, 1, 2, 3, 4, 5, 6, 7], 44, 117⟩)) (.node (.leaf ⟨true, [5, 3, 5, 0, 5, 3, 5, 4, 5, 3], 91, 92⟩) (.leaf ⟨true, [7, 2, 7, 0, 1, 2, 3, 4, 5, 6], 81, 82⟩)))) (.node (.node (.node (.leaf ⟨true, [5, 3, 5, 8, 9, 3, 5, 4, 5, 3], 26, 27⟩) (.leaf ⟨true, [5, 4, 5, 3, 5, 0, 5, 3, 5, 4], 38, 39⟩)) (.node (.leaf ⟨true, [7, 2, 7, 0, 1, 2, 3, 4, 5, 3], 81, 82⟩) (.leaf ⟨true, [7, 4, 5, 0, 5, 3, 5, 8, 7, 2], 114, 115⟩))) (.node (.node (.leaf ⟨true, [7, 2, 7, 8, 9, 3, 2, 6, 7, 2], 58, 59⟩) (.leaf ⟨false, [6, 7, 2, 7, 0, 1, 2, 7, 6, 7], 79, 80⟩)) (.node (.leaf ⟨true, [5, 3, 5, 8, 9, 3, 2, 6, 7, 4], 26, 27⟩) (.leaf ⟨false, [6, 7, 2, 7, 8, 9, 3, 5, 4, 5], 56, 57⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨true, [3, 4, 5, 6, 7, 8, 7, 2, 7, 0], 6, 7⟩) (.leaf ⟨true, [5, 8, 9, 3, 2, 6, 7, 2, 7, 8], 105, 106⟩)) (.leaf ⟨true, [2, 6, 7, 4, 5, 0, 5, 3, 5, 4], 110, 111⟩)) (.node (.leaf ⟨true, [2, 6, 7, 2, 7, 8, 7, 2, 7, 6], 70, 55⟩) (.leaf ⟨false, [2, 7, 6, 7, 2, 7, 8, 7, 2, 7], 52, 53⟩))) (.node (.node (.leaf ⟨true, [5, 4, 5, 3, 5, 0, 1, 2, 7, 6], 38, 39⟩) (.leaf ⟨false, [4, 5, 3, 5, 0, 1, 2, 3, 4, 5], 40, 41⟩)) (.node (.leaf ⟨true, [3, 4, 5, 3, 5, 0, 5, 3, 5, 4], 90, 39⟩) (.leaf ⟨true, [5, 8, 7, 2, 7, 0, 1, 2, 7, 6], 127, 128⟩)))) (.node (.node (.node (.leaf ⟨true, [7, 0, 5, 3, 5, 8, 9, 3, 5, 4], 22, 23⟩) (.leaf ⟨true, [9, 3, 5, 4, 5, 3, 5, 0, 5, 3], 34, 35⟩)) (.node (.leaf ⟨true, [7, 6, 7, 2, 7, 0, 1, 2, 3, 4], 54, 78⟩) (.leaf ⟨true, [2, 6, 7, 4, 5, 0, 5, 3, 5, 8], 110, 111⟩))) (.node (.node (.leaf ⟨true, [7, 6, 7, 2, 7, 8, 9, 3, 2, 6], 54, 55⟩) (.leaf ⟨false, [2, 7, 6, 7, 2, 7, 0, 1, 2, 7], 52, 53⟩)) (.node (.leaf ⟨true, [5, 4, 5, 3, 5, 8, 9, 3, 2, 6], 38, 101⟩) (.leaf ⟨false, [2, 7, 6, 7, 2, 7, 8, 9, 3, 5], 52, 53⟩))))) (.node (.node (.node (.node (.leaf ⟨true, [7, 8, 7, 2, 7, 0, 5, 3, 5, 8], 14, 15⟩) (.leaf ⟨false, [3, 5, 4, 5, 3, 5, 8, 9, 3, 5], 36, 37⟩)) (.node (.leaf ⟨true, [7, 8, 7, 2, 7, 6, 7, 2, 7, 0], 14, 15⟩) (.leaf ⟨true, [7, 2, 7, 6, 7, 2, 7, 8, 9, 3], 76, 77⟩))) (.node (.node (.leaf ⟨true, [5, 0, 1, 2, 7, 6, 7, 2, 7, 8], 46, 47⟩) (.leaf ⟨true, [3, 4, 5, 6, 7, 8, 7, 2, 7, 6], 6, 7⟩)) (.node (.leaf ⟨true, [5, 0, 5, 3, 5, 4, 5, 3, 5, 8], 95, 96⟩) (.leaf ⟨true, [7, 0, 1, 2, 3, 4, 5, 6, 7, 8], 85, 86⟩)))) (.node (.node (.node (.leaf ⟨true, [5, 8, 9, 3, 5, 4, 5, 3, 5, 0], 30, 31⟩) (.leaf ⟨false, [0, 5, 3, 5, 4, 5, 3, 5, 0, 1], 97, 98⟩)) (.node (.leaf ⟨true, [7, 0, 1, 2, 3, 4, 5, 3, 5, 0], 85, 86⟩) (.leaf ⟨true, [5, 0, 5, 3, 5, 8, 7, 2, 7, 0], 95, 96⟩))) (.node (.node (.leaf ⟨true, [7, 8, 9, 3, 2, 6, 7, 2, 7, 8], 62, 63⟩) (.leaf ⟨false, [2, 7, 0, 1, 2, 7, 6, 7, 2, 7], 83, 120⟩)) (.node (.leaf ⟨true, [5, 8, 9, 3, 2, 6, 7, 4, 5, 0], 105, 106⟩) (.leaf ⟨false, [2, 7, 8, 9, 3, 5, 4, 5, 3, 5], 60, 129⟩)))))))) },
    invEven := [0, 1],
    reachCert := { graph := (.node (.node (.node (.node (.leaf ⟨[0], 0, 1⟩) (.leaf ⟨[8], 8, 9⟩)) (.leaf ⟨[4], 8, 7⟩)) (.node (.leaf ⟨[2], 4, 5⟩) (.leaf ⟨[6], 0, 5⟩))) (.node (.node (.node (.leaf ⟨[1], 2, 3⟩) (.leaf ⟨[9], 3, 2⟩)) (.leaf ⟨[5], 2, 7⟩)) (.node (.leaf ⟨[3], 6, 7⟩) (.leaf ⟨[7], 3, 5⟩)))) },
    baseCerts := [{ graph := (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3], 0, 1⟩) (.leaf ⟨[8, 9, 3, 2], 32, 33⟩)) (.node (.leaf ⟨[8, 9, 3, 5], 32, 33⟩) (.leaf ⟨[3, 5, 8, 7], 28, 29⟩))) (.node (.node (.leaf ⟨[8, 7, 2, 7], 16, 17⟩) (.leaf ⟨[3, 4, 5, 3], 6, 7⟩)) (.leaf ⟨[0, 1, 2, 7], 0, 1⟩))) (.node (.node (.node (.leaf ⟨[4, 5, 6, 7], 8, 9⟩) (.leaf ⟨[2, 7, 8, 7], 20, 13⟩)) (.leaf ⟨[4, 5, 3, 5], 8, 37⟩)) (.node (.node (.leaf ⟨[0, 5, 3, 5], 24, 25⟩) (.leaf ⟨[2, 6, 7, 4], 47, 42⟩)) (.leaf ⟨[6, 7, 2, 7], 12, 43⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 5], 4, 5⟩) (.leaf ⟨[3, 2, 6, 7], 45, 46⟩)) (.leaf ⟨[3, 5, 4, 5], 28, 29⟩)) (.node (.node (.leaf ⟨[2, 7, 0, 5], 20, 21⟩) (.leaf ⟨[5, 0, 5, 3], 38, 39⟩)) (.leaf ⟨[2, 7, 6, 7], 20, 21⟩))) (.node (.node (.node (.leaf ⟨[6, 7, 8, 7], 12, 13⟩) (.leaf ⟨[2, 7, 0, 1], 20, 21⟩)) (.leaf ⟨[3, 5, 0, 1], 28, 9⟩)) (.node (.node (.leaf ⟨[3, 5, 8, 9], 28, 29⟩) (.leaf ⟨[7, 4, 5, 0], 48, 49⟩)) (.leaf ⟨[2, 7, 8, 9], 20, 13⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 4], 2, 3⟩) (.leaf ⟨[9, 3, 2, 6], 34, 44⟩)) (.node (.leaf ⟨[9, 3, 5, 4], 34, 35⟩) (.leaf ⟨[5, 8, 7, 2], 30, 31⟩))) (.node (.node (.leaf ⟨[7, 2, 7, 0], 18, 19⟩) (.leaf ⟨[3, 5, 0, 5], 28, 9⟩)) (.leaf ⟨[1, 2, 7, 6], 2, 40⟩))) (.node (.node (.node (.leaf ⟨[5, 6, 7, 8], 10, 11⟩) (.leaf ⟨[7, 2, 7, 6], 18, 19⟩)) (.leaf ⟨[5, 3, 5, 0], 26, 27⟩)) (.node (.node (.leaf ⟨[5, 3, 5, 8], 26, 27⟩) (.leaf ⟨[6, 7, 4, 5], 12, 13⟩)) (.leaf ⟨[7, 2, 7, 8], 18, 19⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 4, 5, 6], 6, 7⟩) (.leaf ⟨[2, 6, 7, 2], 47, 42⟩)) (.leaf ⟨[5, 4, 5, 3], 36, 7⟩)) (.node (.node (.leaf ⟨[7, 0, 5, 3], 22, 23⟩) (.leaf ⟨[5, 3, 5, 4], 26, 27⟩)) (.leaf ⟨[7, 6, 7, 2], 41, 42⟩))) (.node (.node (.node (.leaf ⟨[7, 8, 7, 2], 14, 15⟩) (.leaf ⟨[7, 0, 1, 2], 22, 23⟩)) (.leaf ⟨[5, 0, 1, 2], 38, 39⟩)) (.node (.node (.leaf ⟨[5, 8, 9, 3], 30, 31⟩) (.leaf ⟨[4, 5, 0, 5], 8, 9⟩)) (.leaf ⟨[7, 8, 9, 3], 14, 15⟩)))))) }, { graph := (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3, 4, 5, 6, 7], 0, 1⟩) (.leaf ⟨[8, 9, 3, 2, 6, 7, 4, 5], 64, 65⟩)) (.node (.leaf ⟨[8, 9, 3, 2, 6, 7, 2, 7], 64, 65⟩) (.leaf ⟨[8, 7, 2, 7, 0, 1, 2, 7], 16, 17⟩))) (.node (.node (.leaf ⟨[8, 9, 3, 5, 4, 5, 3, 5], 32, 33⟩) (.leaf ⟨[6, 7, 8, 7, 2, 7, 6, 7], 12, 13⟩)) (.leaf ⟨[0, 1, 2, 3, 4, 5, 3, 5], 0, 1⟩))) (.node (.node (.node (.leaf ⟨[8, 7, 2, 7, 0, 5, 3, 5], 16, 17⟩) (.leaf ⟨[3, 5, 4, 5, 3, 5, 0, 5], 36, 37⟩)) (.leaf ⟨[8, 7, 2, 7, 6, 7, 2, 7], 16, 17⟩)) (.node (.node (.leaf ⟨[0, 1, 2, 7, 6, 7, 2, 7], 48, 49⟩) (.leaf ⟨[7, 8, 9, 3, 2, 6, 7, 4], 62, 63⟩)) (.leaf ⟨[0, 5, 3, 5, 4, 5, 3, 5], 24, 25⟩)))) (.node (.node (.node (.node (.leaf ⟨[4, 5, 6, 7, 8, 7, 2, 7], 8, 9⟩) (.leaf ⟨[6, 7, 4, 5, 0, 5, 3, 5], 92, 93⟩)) (.node (.leaf ⟨[6, 7, 2, 7, 8, 7, 2, 7], 56, 57⟩) (.leaf ⟨[7, 2, 7, 8, 9, 3, 5, 4], 58, 59⟩))) (.node (.node (.leaf ⟨[4, 5, 3, 5, 0, 1, 2, 7], 40, 41⟩) (.leaf ⟨[7, 0, 1, 2, 7, 6, 7, 2], 77, 98⟩)) (.leaf ⟨[4, 5, 3, 5, 0, 5, 3, 5], 40, 41⟩))) (.node (.node (.node (.leaf ⟨[0, 5, 3, 5, 8, 9, 3, 5], 24, 25⟩) (.leaf ⟨[5, 3, 5, 0, 1, 2, 3, 4], 42, 43⟩)) (.leaf ⟨[6, 7, 2, 7, 0, 1, 2, 3], 56, 74⟩)) (.node (.node (.leaf ⟨[6, 7, 2, 7, 8, 9, 3, 2], 56, 57⟩) (.leaf ⟨[0, 5, 3, 5, 8, 7, 2, 7], 24, 25⟩)) (.leaf ⟨[4, 5, 3, 5, 8, 9, 3, 2], 40, 87⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 5, 6, 7, 8, 7], 4, 5⟩) (.leaf ⟨[3, 2, 6, 7, 4, 5, 0, 5], 68, 89⟩)) (.node (.leaf ⟨[3, 2, 6, 7, 2, 7, 8, 7], 68, 69⟩) (.leaf ⟨[5, 0, 1, 2, 3, 4, 5, 3], 46, 97⟩))) (.node (.node (.leaf ⟨[3, 5, 4, 5, 3, 5, 0, 1], 36, 37⟩) (.leaf ⟨[7, 2, 7, 0, 1, 2, 7, 6], 18, 19⟩)) (.leaf ⟨[2, 3, 4, 5, 3, 5, 0, 5], 4, 79⟩))) (.node (.node (.node (.leaf ⟨[2, 7, 0, 5, 3, 5, 8, 9], 20, 21⟩) (.leaf ⟨[5, 3, 5, 4, 5, 3, 5, 0], 85, 86⟩)) (.leaf ⟨[2, 7, 6, 7, 2, 7, 0, 1], 52, 53⟩)) (.node (.node (.leaf ⟨[2, 7, 6, 7, 2, 7, 8, 9], 52, 53⟩) (.leaf ⟨[4, 5, 0, 5, 3, 5, 8, 7], 96, 82⟩)) (.leaf ⟨[3, 5, 4, 5, 3, 5, 8, 9], 36, 37⟩)))) (.node (.node (.node (.node (.leaf ⟨[6, 7, 8, 7, 2, 7, 0, 5], 12, 13⟩) (.leaf ⟨[4, 5, 0, 5, 3, 5, 4, 5], 96, 82⟩)) (.node (.leaf ⟨[2, 7, 8, 7, 2, 7, 6, 7], 71, 13⟩) (.leaf ⟨[7, 8, 9, 3, 5, 4, 5, 3], 62, 103⟩))) (.node (.node (.leaf ⟨[3, 5, 0, 1, 2, 7, 6, 7], 44, 45⟩) (.leaf ⟨[7, 6, 7, 2, 7, 8, 7, 2], 54, 55⟩)) (.leaf ⟨[3, 5, 0, 5, 3, 5, 4, 5], 81, 82⟩))) (.node (.node (.node (.leaf ⟨[3, 5, 8, 9, 3, 5, 4, 5], 28, 29⟩) (.leaf ⟨[5, 0, 1, 2, 3, 4, 5, 6], 46, 97⟩)) (.leaf ⟨[2, 7, 0, 1, 2, 3, 4, 5], 75, 76⟩)) (.node (.node (.leaf ⟨[2, 7, 8, 9, 3, 2, 6, 7], 60, 61⟩) (.leaf ⟨[3, 5, 8, 7, 2, 7, 0, 1], 99, 100⟩)) (.leaf ⟨[3, 5, 8, 9, 3, 2, 6, 7], 28, 29⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 4, 5, 6, 7, 8], 2, 3⟩) (.leaf ⟨[9, 3, 2, 6, 7, 4, 5, 0], 66, 67⟩)) (.node (.leaf ⟨[9, 3, 2, 6, 7, 2, 7, 8], 66, 67⟩) (.leaf ⟨[7, 0, 1, 2, 3, 4, 5, 6], 77, 78⟩))) (.node (.node (.leaf ⟨[9, 3, 5, 4, 5, 3, 5, 0], 34, 35⟩) (.leaf ⟨[6, 7, 2, 7, 0, 1, 2, 7], 56, 74⟩)) (.leaf ⟨[1, 2, 3, 4, 5, 3, 5, 0], 2, 3⟩))) (.node (.node (.node (.leaf ⟨[7, 2, 7, 0, 5, 3, 5, 8], 18, 19⟩) (.leaf ⟨[5, 4, 5, 3, 5, 0, 5, 3], 38, 39⟩)) (.leaf ⟨[7, 2, 7, 6, 7, 2, 7, 0], 72, 73⟩)) (.node (.node (.leaf ⟨[1, 2, 7, 6, 7, 2, 7, 8], 50, 51⟩) (.leaf ⟨[7, 4, 5, 0, 5, 3, 5, 8], 94, 95⟩)) (.leaf ⟨[5, 3, 5, 4, 5, 3, 5, 8], 85, 86⟩)))) (.node (.node (.node (.node (.leaf ⟨[5, 6, 7, 8, 7, 2, 7, 0], 10, 11⟩) (.leaf ⟨[7, 4, 5, 0, 5, 3, 5, 4], 94, 95⟩)) (.node (.leaf ⟨[7, 2, 7, 8, 7, 2, 7, 6], 58, 59⟩) (.leaf ⟨[2, 7, 8, 9, 3, 5, 4, 5], 60, 61⟩))) (.node (.node (.leaf ⟨[5, 3, 5, 0, 1, 2, 7, 6], 42, 43⟩) (.leaf ⟨[2, 7, 6, 7, 2, 7, 8, 7], 52, 53⟩)) (.leaf ⟨[5, 3, 5, 0, 5, 3, 5, 4], 42, 43⟩))) (.node (.node (.node (.leaf ⟨[5, 3, 5, 8, 9, 3, 5, 4], 26, 27⟩) (.leaf ⟨[3, 5, 0, 1, 2, 3, 4, 5], 44, 45⟩)) (.leaf ⟨[7, 2, 7, 0, 1, 2, 3, 4], 18, 19⟩)) (.node (.node (.leaf ⟨[7, 2, 7, 8, 9, 3, 2, 6], 58, 59⟩) (.leaf ⟨[5, 3, 5, 8, 7, 2, 7, 0], 26, 27⟩)) (.leaf ⟨[5, 3, 5, 8, 9, 3, 2, 6], 26, 27⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[3, 4, 5, 6, 7, 8, 7, 2], 6, 7⟩) (.leaf ⟨[2, 6, 7, 4, 5, 0, 5, 3], 90, 91⟩)) (.node (.leaf ⟨[2, 6, 7, 2, 7, 8, 7, 2], 70, 55⟩) (.leaf ⟨[6, 7, 2, 7, 8, 9, 3, 5], 56, 57⟩))) (.node (.node (.leaf ⟨[5, 4, 5, 3, 5, 0, 1, 2], 38, 39⟩) (.leaf ⟨[2, 7, 0, 1, 2, 7, 6, 7], 75, 76⟩)) (.leaf ⟨[3, 4, 5, 3, 5, 0, 5, 3], 80, 39⟩))) (.node (.node (.node (.leaf ⟨[7, 0, 5, 3, 5, 8, 9, 3], 22, 23⟩) (.leaf ⟨[4, 5, 3, 5, 0, 1, 2, 3], 40, 41⟩)) (.leaf ⟨[7, 6, 7, 2, 7, 0, 1, 2], 54, 55⟩)) (.node (.node (.leaf ⟨[7, 6, 7, 2, 7, 8, 9, 3], 54, 55⟩) (.leaf ⟨[5, 0, 5, 3, 5, 8, 7, 2], 83, 84⟩)) (.leaf ⟨[5, 4, 5, 3, 5, 8, 9, 3], 38, 39⟩)))) (.node (.node (.node (.node (.leaf ⟨[7, 8, 7, 2, 7, 0, 5, 3], 14, 15⟩) (.leaf ⟨[4, 5, 3, 5, 8, 9, 3, 5], 40, 87⟩)) (.node (.leaf ⟨[7, 8, 7, 2, 7, 6, 7, 2], 14, 15⟩) (.leaf ⟨[5, 8, 9, 3, 2, 6, 7, 2], 30, 88⟩))) (.node (.node (.leaf ⟨[5, 0, 1, 2, 7, 6, 7, 2], 46, 47⟩) (.leaf ⟨[7, 2, 7, 6, 7, 2, 7, 8], 72, 73⟩)) (.leaf ⟨[5, 0, 5, 3, 5, 4, 5, 3], 83, 84⟩))) (.node (.node (.node (.leaf ⟨[5, 8, 9, 3, 5, 4, 5, 3], 30, 31⟩) (.leaf ⟨[5, 6, 7, 8, 7, 2, 7, 6], 10, 11⟩)) (.leaf ⟨[7, 0, 1, 2, 3, 4, 5, 3], 77, 78⟩)) (.node (.node (.leaf ⟨[7, 8, 9, 3, 2, 6, 7, 2], 62, 63⟩) (.leaf ⟨[5, 8, 7, 2, 7, 0, 1, 2], 101, 102⟩)) (.leaf ⟨[5, 8, 9, 3, 2, 6, 7, 4], 30, 88⟩))))))) }, { graph := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 2, 7], 0, 1⟩) (.leaf ⟨[0, 5, 3, 5, 8, 7, 2, 7, 0, 1, 2, 7], 145, 146⟩)) (.leaf ⟨[8, 9, 3, 2, 6, 7, 4, 5, 0, 5, 3, 5], 64, 121⟩)) (.node (.leaf ⟨[8, 9, 3, 2, 6, 7, 2, 7, 8, 7, 2, 7], 64, 65⟩) (.leaf ⟨[4, 5, 6, 7, 8, 7, 2, 7, 6, 7, 2, 7], 8, 9⟩))) (.node (.node (.node (.leaf ⟨[8, 9, 3, 5, 4, 5, 3, 5, 0, 1, 2, 7], 32, 33⟩) (.leaf ⟨[7, 0, 1, 2, 7, 6, 7, 2, 7, 8, 9, 3], 141, 142⟩)) (.leaf ⟨[3, 5, 4, 5, 3, 5, 0, 5, 3, 5, 4, 5], 36, 37⟩)) (.node (.leaf ⟨[0, 1, 2, 3, 4, 5, 3, 5, 0, 5, 3, 5], 0, 93⟩) (.leaf ⟨[2, 7, 8, 7, 2, 7, 6, 7, 2, 7, 8, 9], 75, 13⟩)))) (.node (.node (.node (.node (.leaf ⟨[8, 7, 2, 7, 0, 5, 3, 5, 8, 9, 3, 5], 16, 17⟩) (.leaf ⟨[2, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 7], 89, 90⟩)) (.leaf ⟨[5, 3, 5, 4, 5, 3, 5, 8, 9, 3, 5, 4], 109, 110⟩)) (.node (.leaf ⟨[8, 7, 2, 7, 6, 7, 2, 7, 0, 1, 2, 3], 78, 79⟩) (.leaf ⟨[7, 2, 7, 0, 1, 2, 7, 6, 7, 2, 7, 8], 87, 138⟩))) (.node (.node (.node (.leaf ⟨[0, 1, 2, 7, 6, 7, 2, 7, 8, 9, 3, 2], 48, 49⟩) (.leaf ⟨[7, 8, 9, 3, 5, 4, 5, 3, 5, 0, 1, 2], 158, 159⟩)) (.leaf ⟨[5, 4, 5, 3, 5, 0, 1, 2, 3, 4, 5, 6], 38, 39⟩)) (.node (.leaf ⟨[0, 5, 3, 5, 4, 5, 3, 5, 8, 9, 3, 2], 107, 108⟩) (.leaf ⟨[7, 8, 9, 3, 2, 6, 7, 4, 5, 0, 5, 3], 62, 63⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[4, 5, 6, 7, 8, 7, 2, 7, 0, 5, 3, 5], 8, 9⟩) (.leaf ⟨[8, 7, 2, 7, 0, 1, 2, 7, 6, 7, 2, 7], 153, 154⟩)) (.leaf ⟨[6, 7, 4, 5, 0, 5, 3, 5, 4, 5, 3, 5], 128, 129⟩)) (.node (.leaf ⟨[6, 7, 2, 7, 8, 7, 2, 7, 6, 7, 2, 7], 71, 72⟩) (.leaf ⟨[7, 2, 7, 6, 7, 2, 7, 0, 1, 2, 7, 6], 80, 81⟩))) (.node (.node (.node (.leaf ⟨[4, 5, 3, 5, 0, 1, 2, 7, 6, 7, 2, 7], 40, 41⟩) (.leaf ⟨[7, 6, 7, 2, 7, 8, 9, 3, 5, 4, 5, 3], 54, 55⟩)) (.leaf ⟨[5, 0, 5, 3, 5, 4, 5, 3, 5, 0, 1, 2], 105, 106⟩)) (.node (.leaf ⟨[4, 5, 3, 5, 0, 5, 3, 5, 4, 5, 3, 5], 99, 100⟩) (.leaf ⟨[7, 6, 7, 2, 7, 8, 9, 3, 2, 6, 7, 4], 54, 55⟩)))) (.node (.node (.node (.node (.leaf ⟨[0, 5, 3, 5, 8, 9, 3, 5, 4, 5, 3, 5], 24, 25⟩) (.leaf ⟨[5, 3, 5, 0, 1, 2, 3, 4, 5, 3, 5, 0], 42, 133⟩)) (.leaf ⟨[3, 5, 8, 9, 3, 5, 4, 5, 3, 5, 0, 5], 28, 29⟩)) (.node (.leaf ⟨[6, 7, 2, 7, 0, 1, 2, 3, 4, 5, 3, 5], 85, 86⟩) (.leaf ⟨[1, 2, 7, 6, 7, 2, 7, 8, 7, 2, 7, 6], 50, 51⟩))) (.node (.node (.node (.leaf ⟨[6, 7, 2, 7, 8, 9, 3, 2, 6, 7, 2, 7], 56, 57⟩) (.leaf ⟨[4, 5, 3, 5, 8, 9, 3, 2, 6, 7, 2, 7], 114, 115⟩)) (.leaf ⟨[5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 2], 136, 137⟩)) (.node (.leaf ⟨[4, 5, 3, 5, 8, 9, 3, 2, 6, 7, 4, 5], 114, 115⟩) (.leaf ⟨[6, 7, 4, 5, 0, 5, 3, 5, 8, 7, 2, 7], 128, 129⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 5, 6, 7, 8, 7, 2, 7, 0, 5], 4, 5⟩) (.leaf ⟨[3, 5, 8, 7, 2, 7, 0, 1, 2, 7, 6, 7], 149, 150⟩)) (.leaf ⟨[3, 2, 6, 7, 4, 5, 0, 5, 3, 5, 4, 5], 124, 125⟩)) (.node (.leaf ⟨[3, 2, 6, 7, 2, 7, 8, 7, 2, 7, 6, 7], 68, 69⟩) (.leaf ⟨[6, 7, 8, 7, 2, 7, 6, 7, 2, 7, 0, 1], 12, 13⟩))) (.node (.node (.node (.leaf ⟨[3, 5, 4, 5, 3, 5, 0, 1, 2, 7, 6, 7], 36, 37⟩) (.leaf ⟨[1, 2, 7, 6, 7, 2, 7, 8, 9, 3, 5, 4], 50, 51⟩)) (.leaf ⟨[5, 3, 5, 0, 5, 3, 5, 4, 5, 3, 5, 0], 101, 102⟩)) (.node (.leaf ⟨[2, 3, 4, 5, 3, 5, 0, 5, 3, 5, 4, 5], 96, 97⟩) (.leaf ⟨[8, 7, 2, 7, 6, 7, 2, 7, 8, 9, 3, 2], 78, 79⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 7, 0, 5, 3, 5, 8, 9, 3, 5, 4, 5], 20, 21⟩) (.leaf ⟨[5, 4, 5, 3, 5, 0, 1, 2, 3, 4, 5, 3], 38, 39⟩)) (.leaf ⟨[5, 4, 5, 3, 5, 8, 9, 3, 5, 4, 5, 3], 112, 113⟩)) (.node (.leaf ⟨[2, 7, 6, 7, 2, 7, 0, 1, 2, 3, 4, 5], 52, 82⟩) (.leaf ⟨[7, 0, 1, 2, 7, 6, 7, 2, 7, 8, 7, 2], 141, 142⟩))) (.node (.node (.node (.leaf ⟨[2, 7, 6, 7, 2, 7, 8, 9, 3, 2, 6, 7], 52, 53⟩) (.leaf ⟨[9, 3, 5, 4, 5, 3, 5, 0, 1, 2, 3, 4], 34, 35⟩)) (.leaf ⟨[5, 3, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8], 42, 133⟩)) (.node (.leaf ⟨[3, 5, 4, 5, 3, 5, 8, 9, 3, 2, 6, 7], 36, 111⟩) (.leaf ⟨[3, 2, 6, 7, 4, 5, 0, 5, 3, 5, 8, 7], 124, 125⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[6, 7, 8, 7, 2, 7, 0, 5, 3, 5, 8, 9], 12, 13⟩) (.leaf ⟨[6, 7, 2, 7, 0, 1, 2, 3, 4, 5, 6, 7], 85, 86⟩)) (.leaf ⟨[4, 5, 0, 5, 3, 5, 4, 5, 3, 5, 8, 9], 132, 104⟩)) (.node (.leaf ⟨[2, 7, 8, 7, 2, 7, 6, 7, 2, 7, 0, 1], 75, 13⟩) (.leaf ⟨[7, 6, 7, 2, 7, 0, 1, 2, 7, 6, 7, 2], 83, 84⟩))) (.node (.node (.node (.leaf ⟨[3, 5, 0, 1, 2, 7, 6, 7, 2, 7, 8, 9], 44, 45⟩) (.leaf ⟨[7, 2, 7, 8, 9, 3, 5, 4, 5, 3, 5, 0], 58, 155⟩)) (.leaf ⟨[5, 3, 5, 4, 5, 3, 5, 0, 1, 2, 3, 4], 109, 110⟩)) (.node (.leaf ⟨[3, 5, 0, 5, 3, 5, 4, 5, 3, 5, 8, 9], 103, 104⟩) (.leaf ⟨[7, 2, 7, 8, 9, 3, 2, 6, 7, 4, 5, 0], 58, 59⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 5, 8, 9, 3, 5, 4, 5, 3, 5, 0, 1], 28, 29⟩) (.leaf ⟨[5, 0, 1, 2, 3, 4, 5, 3, 5, 0, 5, 3], 136, 137⟩)) (.leaf ⟨[8, 9, 3, 5, 4, 5, 3, 5, 0, 5, 3, 5], 32, 33⟩)) (.node (.leaf ⟨[2, 7, 0, 1, 2, 3, 4, 5, 3, 5, 0, 5], 89, 90⟩) (.leaf ⟨[7, 6, 7, 2, 7, 8, 7, 2, 7, 6, 7, 2], 54, 55⟩))) (.node (.node (.node (.leaf ⟨[2, 7, 8, 9, 3, 2, 6, 7, 2, 7, 8, 7], 60, 61⟩) (.leaf ⟨[3, 5, 8, 9, 3, 2, 6, 7, 2, 7, 8, 7], 117, 118⟩)) (.leaf ⟨[2, 3, 4, 5, 6, 7, 8, 7, 2, 7, 6, 7], 4, 5⟩)) (.node (.leaf ⟨[3, 5, 8, 9, 3, 2, 6, 7, 4, 5, 0, 5], 117, 118⟩) (.leaf ⟨[4, 5, 0, 5, 3, 5, 8, 7, 2, 7, 0, 1], 132, 104⟩))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 4, 5, 6, 7, 8, 7, 2, 7, 0], 2, 3⟩) (.leaf ⟨[5, 3, 5, 8, 7, 2, 7, 0, 1, 2, 7, 6], 147, 148⟩)) (.leaf ⟨[9, 3, 2, 6, 7, 4, 5, 0, 5, 3, 5, 4], 122, 123⟩)) (.node (.leaf ⟨[9, 3, 2, 6, 7, 2, 7, 8, 7, 2, 7, 6], 66, 67⟩) (.leaf ⟨[5, 6, 7, 8, 7, 2, 7, 6, 7, 2, 7, 0], 10, 11⟩))) (.node (.node (.node (.leaf ⟨[9, 3, 5, 4, 5, 3, 5, 0, 1, 2, 7, 6], 34, 35⟩) (.leaf ⟨[0, 1, 2, 7, 6, 7, 2, 7, 8, 9, 3, 5], 48, 49⟩)) (.leaf ⟨[5, 4, 5, 3, 5, 0, 5, 3, 5, 4, 5, 3], 38, 39⟩)) (.node (.leaf ⟨[1, 2, 3, 4, 5, 3, 5, 0, 5, 3, 5, 4], 94, 95⟩) (.leaf ⟨[7, 8, 7, 2, 7, 6, 7, 2, 7, 8, 9, 3], 76, 77⟩)))) (.node (.node (.node (.node (.leaf ⟨[7, 2, 7, 0, 5, 3, 5, 8, 9, 3, 5, 4], 18, 19⟩) (.leaf ⟨[7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 2], 91, 92⟩)) (.leaf ⟨[3, 5, 4, 5, 3, 5, 8, 9, 3, 5, 4, 5], 36, 111⟩)) (.node (.leaf ⟨[7, 2, 7, 6, 7, 2, 7, 0, 1, 2, 3, 4], 80, 81⟩) (.leaf ⟨[2, 7, 0, 1, 2, 7, 6, 7, 2, 7, 8, 7], 139, 140⟩))) (.node (.node (.node (.leaf ⟨[1, 2, 7, 6, 7, 2, 7, 8, 9, 3, 2, 6], 50, 51⟩) (.leaf ⟨[8, 9, 3, 5, 4, 5, 3, 5, 0, 1, 2, 3], 32, 33⟩)) (.leaf ⟨[4, 5, 3, 5, 0, 1, 2, 3, 4, 5, 6, 7], 40, 41⟩)) (.node (.leaf ⟨[5, 3, 5, 4, 5, 3, 5, 8, 9, 3, 2, 6], 109, 110⟩) (.leaf ⟨[9, 3, 2, 6, 7, 4, 5, 0, 5, 3, 5, 8], 122, 123⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[5, 6, 7, 8, 7, 2, 7, 0, 5, 3, 5, 8], 10, 11⟩) (.leaf ⟨[7, 6, 7, 2, 7, 0, 1, 2, 3, 4, 5, 6], 83, 84⟩)) (.leaf ⟨[7, 4, 5, 0, 5, 3, 5, 4, 5, 3, 5, 8], 130, 131⟩)) (.node (.leaf ⟨[7, 2, 7, 8, 7, 2, 7, 6, 7, 2, 7, 0], 73, 74⟩) (.leaf ⟨[2, 7, 6, 7, 2, 7, 0, 1, 2, 7, 6, 7], 52, 82⟩))) (.node (.node (.node (.leaf ⟨[5, 3, 5, 0, 1, 2, 7, 6, 7, 2, 7, 8], 42, 43⟩) (.leaf ⟨[6, 7, 2, 7, 8, 9, 3, 5, 4, 5, 3, 5], 56, 57⟩)) (.leaf ⟨[0, 5, 3, 5, 4, 5, 3, 5, 0, 1, 2, 3], 107, 108⟩)) (.node (.leaf ⟨[5, 3, 5, 0, 5, 3, 5, 4, 5, 3, 5, 8], 101, 102⟩) (.leaf ⟨[6, 7, 2, 7, 8, 9, 3, 2, 6, 7, 4, 5], 56, 57⟩)))) (.node (.node (.node (.node (.leaf ⟨[5, 3, 5, 8, 9, 3, 5, 4, 5, 3, 5, 0], 26, 27⟩) (.leaf ⟨[3, 5, 0, 1, 2, 3, 4, 5, 3, 5, 0, 5], 134, 135⟩)) (.leaf ⟨[5, 8, 9, 3, 5, 4, 5, 3, 5, 0, 5, 3], 30, 31⟩)) (.node (.leaf ⟨[7, 2, 7, 0, 1, 2, 3, 4, 5, 3, 5, 0], 87, 88⟩) (.leaf ⟨[2, 7, 6, 7, 2, 7, 8, 7, 2, 7, 6, 7], 52, 53⟩))) (.node (.node (.node (.leaf ⟨[7, 2, 7, 8, 9, 3, 2, 6, 7, 2, 7, 8], 58, 59⟩) (.leaf ⟨[5, 3, 5, 8, 9, 3, 2, 6, 7, 2, 7, 8], 26, 116⟩)) (.leaf ⟨[1, 2, 3, 4, 5, 6, 7, 8, 7, 2, 7, 6], 2, 3⟩)) (.node (.leaf ⟨[5, 3, 5, 8, 9, 3, 2, 6, 7, 4, 5, 0], 26, 116⟩) (.leaf ⟨[7, 4, 5, 0, 5, 3, 5, 8, 7, 2, 7, 0], 130, 131⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨[3, 4, 5, 6, 7, 8, 7, 2, 7, 0, 5, 3], 6, 7⟩) (.leaf ⟨[5, 8, 7, 2, 7, 0, 1, 2, 7, 6, 7, 2], 151, 152⟩)) (.leaf ⟨[2, 6, 7, 4, 5, 0, 5, 3, 5, 4, 5, 3], 126, 127⟩)) (.node (.leaf ⟨[2, 6, 7, 2, 7, 8, 7, 2, 7, 6, 7, 2], 70, 55⟩) (.leaf ⟨[8, 7, 2, 7, 6, 7, 2, 7, 0, 1, 2, 7], 78, 79⟩))) (.node (.node (.node (.leaf ⟨[5, 4, 5, 3, 5, 0, 1, 2, 7, 6, 7, 2], 38, 39⟩) (.leaf ⟨[2, 7, 6, 7, 2, 7, 8, 9, 3, 5, 4, 5], 52, 53⟩)) (.leaf ⟨[3, 5, 0, 5, 3, 5, 4, 5, 3, 5, 0, 1], 103, 104⟩)) (.node (.leaf ⟨[3, 4, 5, 3, 5, 0, 5, 3, 5, 4, 5, 3], 98, 39⟩) (.leaf ⟨[7, 2, 7, 6, 7, 2, 7, 8, 9, 3, 2, 6], 80, 81⟩)))) (.node (.node (.node (.node (.leaf ⟨[7, 0, 5, 3, 5, 8, 9, 3, 5, 4, 5, 3], 22, 23⟩) (.leaf ⟨[4, 5, 3, 5, 0, 1, 2, 3, 4, 5, 3, 5], 40, 41⟩)) (.leaf ⟨[4, 5, 3, 5, 8, 9, 3, 5, 4, 5, 3, 5], 114, 115⟩)) (.node (.leaf ⟨[7, 6, 7, 2, 7, 0, 1, 2, 3, 4, 5, 3], 83, 84⟩) (.leaf ⟨[0, 1, 2, 7, 6, 7, 2, 7, 8, 7, 2, 7], 48, 49⟩))) (.node (.node (.node (.leaf ⟨[7, 6, 7, 2, 7, 8, 9, 3, 2, 6, 7, 2], 54, 55⟩) (.leaf ⟨[5, 4, 5, 3, 5, 8, 9, 3, 2, 6, 7, 2], 112, 113⟩)) (.leaf ⟨[3, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 7], 134, 135⟩)) (.node (.leaf ⟨[5, 4, 5, 3, 5, 8, 9, 3, 2, 6, 7, 4], 112, 113⟩) (.leaf ⟨[2, 6, 7, 4, 5, 0, 5, 3, 5, 8, 7, 2], 126, 127⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[7, 8, 7, 2, 7, 0, 5, 3, 5, 8, 9, 3], 14, 15⟩) (.leaf ⟨[7, 2, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8], 87, 88⟩)) (.leaf ⟨[0, 5, 3, 5, 4, 5, 3, 5, 8, 9, 3, 5], 107, 108⟩)) (.node (.leaf ⟨[7, 8, 7, 2, 7, 6, 7, 2, 7, 0, 1, 2], 76, 77⟩) (.leaf ⟨[6, 7, 2, 7, 0, 1, 2, 7, 6, 7, 2, 7], 85, 86⟩))) (.node (.node (.node (.leaf ⟨[5, 0, 1, 2, 7, 6, 7, 2, 7, 8, 9, 3], 46, 47⟩) (.leaf ⟨[2, 7, 8, 9, 3, 5, 4, 5, 3, 5, 0, 1], 156, 157⟩)) (.leaf ⟨[3, 5, 4, 5, 3, 5, 0, 1, 2, 3, 4, 5], 36, 37⟩)) (.node (.leaf ⟨[5, 0, 5, 3, 5, 4, 5, 3, 5, 8, 9, 3], 105, 106⟩) (.leaf ⟨[2, 7, 8, 9, 3, 2, 6, 7, 4, 5, 0, 5], 60, 61⟩)))) (.node (.node (.node (.node (.leaf ⟨[5, 8, 9, 3, 5, 4, 5, 3, 5, 0, 1, 2], 30, 31⟩) (.leaf ⟨[2, 7, 0, 1, 2, 7, 6, 7, 2, 7, 8, 9], 139, 140⟩)) (.leaf ⟨[9, 3, 5, 4, 5, 3, 5, 0, 5, 3, 5, 4], 34, 35⟩)) (.node (.leaf ⟨[7, 0, 1, 2, 3, 4, 5, 3, 5, 0, 5, 3], 91, 92⟩) (.leaf ⟨[7, 2, 7, 8, 7, 2, 7, 6, 7, 2, 7, 8], 73, 74⟩))) (.node (.node (.node (.leaf ⟨[7, 8, 9, 3, 2, 6, 7, 2, 7, 8, 7, 2], 62, 63⟩) (.leaf ⟨[5, 8, 9, 3, 2, 6, 7, 2, 7, 8, 7, 2], 119, 120⟩)) (.leaf ⟨[3, 4, 5, 6, 7, 8, 7, 2, 7, 6, 7, 2], 6, 7⟩)) (.node (.leaf ⟨[5, 8, 9, 3, 2, 6, 7, 4, 5, 0, 5, 3], 119, 120⟩) (.leaf ⟨[5, 0, 5, 3, 5, 8, 7, 2, 7, 0, 1, 2], 143, 144⟩)))))))) }] }

def cert_carryXor5_k6 : PowerAvoidCert :=
  { syncCert := { width := 13, parityMask := 0x100800000000000000000000000000000000000000000000002004000000000000000000000000000000000000000000000000000000000000000000000000300402800000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000000000000000009600400000000000000000000000000000002000000060000000000000000000000020000400000000400000004200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180000000000000000000000000000000000000000000008080420000020000000002400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002400000000040000042010100000000000000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004200000002000000002000040000000000000000000000060000000400000000000000000000000000000002006900000000000000000090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000140200c0000000000000000000000000000000000000000000000000000000000000000000000002004000000000000000000000000000000000000000000000010080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, graph := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨false, [0, 1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 0], 0, 1⟩) (.leaf ⟨false, [6, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7], 82, 83⟩)) (.leaf ⟨false, [4, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10], 109, 110⟩)) (.node (.node (.leaf ⟨false, [7, 9, 10, 11, 6, 8, 2, 3, 7, 8, 2, 9, 6], 58, 59⟩) (.leaf ⟨false, [4, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7], 121, 122⟩)) (.leaf ⟨false, [6, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2], 12, 71⟩))) (.node (.node (.node (.leaf ⟨false, [7, 9, 10, 1, 4, 5, 10, 11, 0, 1, 2, 9, 0], 32, 33⟩) (.leaf ⟨false, [7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0], 140, 141⟩)) (.leaf ⟨false, [10, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2], 128, 129⟩)) (.node (.leaf ⟨false, [0, 1, 2, 3, 4, 5, 10, 11, 0, 1, 2, 9, 0], 90, 91⟩) (.leaf ⟨true, [11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 8, 2, 9], 146, 147⟩)))) (.node (.node (.node (.node (.leaf ⟨false, [7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 1, 4], 16, 17⟩) (.leaf ⟨false, [6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4, 11, 0], 156, 157⟩)) (.leaf ⟨false, [6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 5, 10], 28, 29⟩)) (.node (.leaf ⟨false, [7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 3, 4], 74, 75⟩) (.leaf ⟨true, [11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 9], 130, 131⟩))) (.node (.node (.node (.leaf ⟨false, [0, 1, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6], 48, 49⟩) (.leaf ⟨false, [4, 5, 10, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7], 124, 125⟩)) (.leaf ⟨false, [4, 11, 0, 1, 2, 3, 4, 5, 6, 3, 7, 8, 2], 86, 87⟩)) (.node (.leaf ⟨false, [6, 3, 7, 9, 10, 11, 6, 8, 4, 11, 0, 5, 10], 54, 55⟩) (.leaf ⟨true, [3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11], 14, 15⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨false, [4, 5, 6, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7], 8, 9⟩) (.leaf ⟨false, [0, 1, 2, 9, 6, 8, 2, 3, 7, 9, 10, 1, 7], 148, 149⟩)) (.leaf ⟨false, [10, 1, 4, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10], 117, 118⟩)) (.node (.node (.leaf ⟨false, [6, 8, 2, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0], 66, 67⟩) (.leaf ⟨false, [7, 9, 10, 11, 6, 8, 2, 3, 7, 9, 10, 1, 7], 58, 59⟩)) (.leaf ⟨true, [11, 6, 8, 4, 11, 0, 5, 10, 1, 7, 8, 4, 11], 103, 104⟩))) (.node (.node (.node (.leaf ⟨false, [4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6, 3, 7], 40, 41⟩) (.leaf ⟨false, [0, 1, 2, 3, 4, 5, 10, 11, 0, 5, 10, 1, 4], 90, 91⟩)) (.leaf ⟨false, [10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 6], 136, 137⟩)) (.node (.leaf ⟨false, [2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 4], 20, 21⟩) (.leaf ⟨true, [9, 6, 8, 2, 3, 7, 8, 2, 9, 0, 5, 6, 3], 154, 65⟩)))) (.node (.node (.node (.node (.leaf ⟨false, [0, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0], 24, 25⟩) (.leaf ⟨false, [7, 9, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4], 164, 165⟩)) (.leaf ⟨false, [10, 1, 4, 5, 10, 11, 0, 5, 10, 1, 7, 8, 4], 36, 37⟩)) (.node (.leaf ⟨false, [6, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0], 82, 83⟩) (.leaf ⟨true, [1, 7, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3], 138, 139⟩))) (.node (.node (.node (.leaf ⟨false, [0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7], 24, 25⟩) (.leaf ⟨false, [0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 11, 6], 113, 114⟩)) (.leaf ⟨false, [2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 6, 8, 4], 4, 5⟩)) (.node (.leaf ⟨false, [10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 4, 5, 6], 101, 102⟩) (.leaf ⟨false, [7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 9, 6], 74, 75⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨false, [2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 0, 5, 6], 4, 5⟩) (.leaf ⟨false, [4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 9, 10], 144, 145⟩)) (.leaf ⟨false, [0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 1, 4], 113, 114⟩)) (.node (.node (.leaf ⟨false, [10, 11, 6, 8, 2, 3, 7, 8, 2, 9, 6, 8, 4], 62, 63⟩) (.leaf ⟨false, [6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 9, 10], 54, 55⟩)) (.leaf ⟨true, [9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 7, 8], 99, 100⟩))) (.node (.node (.node (.leaf ⟨false, [10, 1, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6], 36, 37⟩) (.leaf ⟨false, [4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 5, 10], 86, 87⟩)) (.leaf ⟨false, [0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4], 132, 133⟩)) (.node (.leaf ⟨false, [2, 3, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6], 94, 95⟩) (.leaf ⟨true, [1, 2, 9, 6, 8, 2, 3, 7, 8, 2, 9, 0, 5], 150, 151⟩)))) (.node (.node (.node (.node (.leaf ⟨false, [2, 9, 0, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10], 20, 21⟩) (.leaf ⟨false, [2, 3, 7, 9, 10, 1, 7, 8, 4, 11, 0, 1, 2], 160, 161⟩)) (.leaf ⟨false, [7, 9, 10, 1, 4, 5, 10, 11, 0, 5, 10, 1, 7], 32, 33⟩)) (.node (.leaf ⟨false, [2, 9, 6, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10], 78, 79⟩) (.leaf ⟨true, [5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 9, 6, 8], 134, 135⟩))) (.node (.node (.node (.leaf ⟨false, [2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2], 20, 21⟩) (.leaf ⟨false, [10, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10], 128, 110⟩)) (.leaf ⟨false, [0, 1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 6], 0, 1⟩)) (.node (.leaf ⟨false, [7, 9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 4], 97, 98⟩) (.leaf ⟨true, [8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8], 18, 19⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨false, [6, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10], 12, 13⟩) (.leaf ⟨false, [2, 9, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4], 152, 153⟩)) (.leaf ⟨false, [4, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0], 121, 122⟩)) (.node (.node (.leaf ⟨false, [2, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2], 70, 71⟩) (.leaf ⟨false, [10, 11, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4], 62, 63⟩)) (.leaf ⟨true, [8, 4, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1], 107, 108⟩))) (.node (.node (.node (.leaf ⟨false, [10, 11, 0, 1, 2, 9, 0, 5, 6, 3, 7, 9, 10], 44, 45⟩) (.leaf ⟨false, [2, 3, 4, 5, 10, 11, 0, 5, 10, 1, 4, 5, 6], 94, 95⟩)) (.leaf ⟨false, [7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 6, 3, 7], 140, 141⟩)) (.node (.leaf ⟨false, [0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 4, 11, 0], 24, 25⟩) (.leaf ⟨true, [8, 2, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9], 68, 69⟩)))) (.node (.node (.node (.node (.leaf ⟨false, [6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 1, 2], 28, 29⟩) (.leaf ⟨false, [10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10], 136, 137⟩)) (.leaf ⟨false, [4, 5, 10, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0], 124, 125⟩)) (.node (.leaf ⟨false, [4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 1, 2], 86, 87⟩) (.leaf ⟨true, [8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 8], 142, 143⟩))) (.node (.node (.node (.leaf ⟨false, [6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 8, 2], 54, 55⟩) (.leaf ⟨false, [10, 1, 4, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2], 117, 118⟩)) (.leaf ⟨false, [4, 5, 6, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0], 8, 9⟩)) (.node (.leaf ⟨false, [6, 8, 4, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7], 105, 106⟩) (.leaf ⟨false, [2, 9, 6, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2], 78, 79⟩))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨true, [1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 0, 5], 2, 3⟩) (.leaf ⟨true, [8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 9], 142, 143⟩)) (.leaf ⟨true, [11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 1], 111, 112⟩)) (.node (.node (.leaf ⟨true, [9, 10, 11, 6, 8, 2, 3, 7, 8, 2, 9, 6, 8], 60, 61⟩) (.leaf ⟨true, [5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 9], 52, 53⟩)) (.leaf ⟨false, [7, 9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 7], 97, 98⟩))) (.node (.node (.node (.leaf ⟨true, [9, 10, 1, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5], 34, 35⟩) (.leaf ⟨true, [8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 5], 84, 85⟩)) (.leaf ⟨true, [11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3], 130, 131⟩)) (.node (.leaf ⟨true, [1, 2, 3, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5], 92, 93⟩) (.leaf ⟨false, [0, 1, 2, 9, 6, 8, 2, 3, 7, 8, 2, 9, 0], 148, 149⟩)))) (.node (.node (.node (.node (.leaf ⟨true, [8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 1, 4, 5], 18, 19⟩) (.leaf ⟨true, [8, 2, 3, 7, 9, 10, 1, 7, 8, 4, 11, 0, 1], 158, 159⟩)) (.leaf ⟨true, [3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 5, 10, 1], 30, 31⟩)) (.node (.leaf ⟨true, [8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 3, 4, 5], 76, 77⟩) (.leaf ⟨false, [0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 9, 6], 132, 133⟩))) (.node (.node (.node (.leaf ⟨true, [1, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8], 50, 51⟩) (.leaf ⟨true, [5, 10, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9], 126, 127⟩)) (.leaf ⟨true, [11, 0, 1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9], 88, 89⟩)) (.node (.leaf ⟨true, [3, 7, 9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1], 56, 57⟩) (.leaf ⟨false, [7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6], 16, 17⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨true, [5, 6, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9], 10, 11⟩) (.leaf ⟨true, [1, 2, 9, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8], 150, 151⟩)) (.leaf ⟨true, [1, 4, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11], 119, 120⟩)) (.node (.node (.leaf ⟨true, [8, 2, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1], 68, 69⟩) (.leaf ⟨true, [9, 10, 11, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8], 60, 61⟩)) (.leaf ⟨false, [6, 8, 4, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0], 105, 106⟩))) (.node (.node (.node (.leaf ⟨true, [5, 10, 11, 0, 1, 2, 9, 0, 5, 6, 3, 7, 9], 42, 43⟩) (.leaf ⟨true, [1, 2, 3, 4, 5, 10, 11, 0, 5, 10, 1, 4, 5], 92, 93⟩)) (.leaf ⟨true, [1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 6, 3], 138, 139⟩)) (.node (.leaf ⟨true, [9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 4, 11], 22, 23⟩) (.leaf ⟨false, [6, 8, 2, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7], 66, 67⟩)))) (.node (.node (.node (.node (.leaf ⟨true, [5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 1], 26, 27⟩) (.leaf ⟨true, [9, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5], 166, 167⟩)) (.leaf ⟨true, [1, 4, 5, 10, 11, 0, 5, 10, 1, 7, 8, 4, 11], 38, 123⟩)) (.node (.leaf ⟨true, [8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 1], 84, 85⟩) (.leaf ⟨false, [7, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7], 140, 141⟩))) (.node (.node (.node (.leaf ⟨true, [5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 8], 52, 53⟩) (.leaf ⟨true, [5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 11, 6, 8], 115, 116⟩)) (.leaf ⟨true, [3, 4, 5, 6, 3, 7, 8, 2, 9, 6, 8, 4, 11], 6, 7⟩)) (.node (.leaf ⟨true, [11, 6, 8, 4, 11, 0, 5, 10, 1, 4, 5, 6, 3], 103, 104⟩) (.leaf ⟨true, [8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 9, 6, 8], 76, 77⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨true, [3, 4, 5, 6, 3, 7, 8, 2, 9, 0, 5, 6, 3], 6, 7⟩) (.leaf ⟨true, [11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 9, 10, 1], 146, 147⟩)) (.leaf ⟨true, [5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 1, 4, 5], 115, 116⟩)) (.node (.node (.leaf ⟨true, [11, 6, 8, 2, 3, 7, 8, 2, 9, 6, 8, 4, 11], 64, 65⟩) (.leaf ⟨true, [3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 9, 10, 1], 56, 57⟩)) (.leaf ⟨false, [10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 7, 8, 4], 101, 102⟩))) (.node (.node (.node (.leaf ⟨true, [1, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6, 3], 38, 39⟩) (.leaf ⟨true, [11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 5, 10, 1], 88, 89⟩)) (.leaf ⟨true, [5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5], 134, 135⟩)) (.node (.leaf ⟨true, [3, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6, 3], 96, 39⟩) (.leaf ⟨false, [2, 9, 6, 8, 2, 3, 7, 8, 2, 9, 0, 5, 6], 152, 153⟩)))) (.node (.node (.node (.node (.leaf ⟨true, [9, 0, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11], 22, 23⟩) (.leaf ⟨true, [3, 7, 9, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3], 162, 163⟩)) (.leaf ⟨true, [9, 10, 1, 4, 5, 10, 11, 0, 5, 10, 1, 7, 8], 34, 35⟩)) (.node (.leaf ⟨true, [9, 6, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11], 80, 81⟩) (.leaf ⟨false, [10, 1, 7, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2], 136, 137⟩))) (.node (.node (.node (.leaf ⟨true, [9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3], 22, 23⟩) (.leaf ⟨true, [11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 11], 111, 112⟩)) (.leaf ⟨true, [1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 6, 8], 2, 3⟩)) (.node (.leaf ⟨true, [9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 4, 5], 99, 100⟩) (.leaf ⟨true, [3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 9], 72, 73⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨true, [3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 1], 14, 15⟩) (.leaf ⟨true, [9, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4, 11], 154, 155⟩)) (.leaf ⟨true, [5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 5], 26, 27⟩)) (.node (.node (.leaf ⟨true, [3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 3], 72, 73⟩) (.leaf ⟨true, [11, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4, 11], 64, 155⟩)) (.leaf ⟨false, [4, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2], 109, 129⟩))) (.node (.node (.node (.leaf ⟨true, [11, 0, 1, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11], 46, 47⟩) (.leaf ⟨true, [3, 4, 5, 10, 11, 0, 5, 10, 1, 4, 5, 6, 3], 96, 123⟩)) (.leaf ⟨true, [8, 4, 11, 0, 1, 2, 3, 4, 5, 6, 3, 7, 8], 84, 85⟩)) (.node (.leaf ⟨true, [5, 6, 3, 7, 9, 10, 11, 6, 8, 4, 11, 0, 5], 52, 53⟩) (.leaf ⟨false, [2, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10], 70, 13⟩)))) (.node (.node (.node (.node (.leaf ⟨true, [3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 1, 2, 9], 30, 31⟩) (.leaf ⟨true, [1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11], 138, 139⟩)) (.leaf ⟨true, [5, 10, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1], 126, 127⟩)) (.node (.leaf ⟨true, [11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 1, 2, 9], 88, 89⟩) (.leaf ⟨false, [4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 8, 2], 144, 145⟩))) (.node (.node (.node (.leaf ⟨true, [3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 8, 2, 9], 56, 57⟩) (.leaf ⟨true, [1, 4, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3], 119, 120⟩)) (.leaf ⟨true, [5, 6, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1], 10, 11⟩)) (.node (.leaf ⟨true, [8, 4, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9], 107, 108⟩) (.leaf ⟨true, [9, 6, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3], 80, 81⟩)))))))) },
    invEven := [0, 1],
    reachCert := { graph := (.node (.node (.node (.node (.leaf ⟨[0], 0, 1⟩) (.leaf ⟨[8], 10, 1⟩)) (.leaf ⟨[4], 7, 8⟩)) (.node (.node (.leaf ⟨[2], 4, 5⟩) (.leaf ⟨[10], 6, 8⟩)) (.leaf ⟨[6], 0, 5⟩))) (.node (.node (.node (.leaf ⟨[1], 2, 3⟩) (.leaf ⟨[9], 10, 11⟩)) (.leaf ⟨[5], 2, 9⟩)) (.node (.node (.leaf ⟨[3], 6, 3⟩) (.leaf ⟨[11], 4, 11⟩)) (.leaf ⟨[7], 7, 9⟩)))) },
    baseCerts := [{ graph := (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3, 4, 5], 0, 1⟩) (.leaf ⟨[5, 10, 1, 7, 8, 4], 72, 73⟩)) (.leaf ⟨[6, 8, 2, 3, 7, 8], 54, 55⟩)) (.node (.leaf ⟨[7, 9, 10, 1, 4, 5], 28, 29⟩) (.leaf ⟨[10, 11, 6, 8, 4, 11], 50, 51⟩))) (.node (.node (.node (.leaf ⟨[7, 8, 2, 9, 0, 5], 16, 17⟩) (.leaf ⟨[2, 9, 6, 8, 2, 3], 59, 60⟩)) (.leaf ⟨[6, 8, 4, 11, 0, 1], 63, 64⟩)) (.node (.leaf ⟨[0, 1, 2, 9, 0, 5], 0, 44⟩) (.leaf ⟨[10, 1, 4, 5, 6, 3], 32, 33⟩)))) (.node (.node (.node (.node (.leaf ⟨[4, 5, 6, 3, 7, 8], 8, 9⟩) (.leaf ⟨[4, 11, 0, 1, 2, 9], 67, 41⟩)) (.leaf ⟨[7, 8, 2, 9, 6, 8], 16, 17⟩)) (.node (.leaf ⟨[4, 5, 10, 11, 0, 1], 36, 37⟩) (.leaf ⟨[4, 11, 0, 5, 10, 1], 67, 41⟩))) (.node (.node (.node (.leaf ⟨[0, 5, 6, 3, 7, 9], 24, 25⟩) (.leaf ⟨[2, 3, 7, 9, 10, 1], 58, 13⟩)) (.leaf ⟨[1, 2, 3, 4, 5, 10], 2, 3⟩)) (.node (.leaf ⟨[7, 9, 10, 11, 6, 8], 28, 47⟩) (.leaf ⟨[5, 10, 11, 0, 5, 10], 38, 39⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 5, 6, 3], 4, 5⟩) (.leaf ⟨[1, 7, 8, 4, 11, 0], 76, 77⟩)) (.leaf ⟨[2, 3, 7, 8, 2, 9], 58, 13⟩)) (.node (.leaf ⟨[10, 1, 4, 5, 10, 11], 32, 33⟩) (.leaf ⟨[6, 8, 4, 11, 0, 5], 63, 64⟩))) (.node (.node (.node (.leaf ⟨[2, 9, 0, 5, 6, 3], 20, 21⟩) (.leaf ⟨[6, 8, 2, 3, 7, 9], 54, 55⟩)) (.leaf ⟨[4, 11, 0, 1, 2, 3], 67, 41⟩)) (.node (.leaf ⟨[6, 3, 7, 9, 10, 11], 12, 13⟩) (.leaf ⟨[4, 5, 6, 3, 7, 9], 8, 9⟩)))) (.node (.node (.node (.node (.leaf ⟨[6, 3, 7, 8, 2, 9], 12, 13⟩) (.leaf ⟨[0, 1, 2, 9, 6, 8], 0, 44⟩)) (.leaf ⟨[2, 9, 6, 8, 4, 11], 59, 60⟩)) (.node (.leaf ⟨[10, 11, 0, 1, 2, 9], 40, 41⟩) (.leaf ⟨[0, 5, 10, 1, 4, 5], 70, 71⟩))) (.node (.node (.node (.leaf ⟨[6, 3, 7, 9, 10, 1], 12, 13⟩) (.leaf ⟨[7, 9, 10, 1, 7, 8], 28, 29⟩)) (.leaf ⟨[3, 4, 5, 10, 11, 0], 6, 35⟩)) (.node (.leaf ⟨[10, 11, 6, 8, 2, 3], 50, 51⟩) (.leaf ⟨[11, 0, 5, 10, 1, 7], 68, 69⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 4, 5, 6], 2, 3⟩) (.leaf ⟨[10, 1, 7, 8, 4, 11], 74, 75⟩)) (.leaf ⟨[8, 2, 3, 7, 8, 2], 56, 57⟩)) (.node (.leaf ⟨[9, 10, 1, 4, 5, 10], 30, 31⟩) (.leaf ⟨[11, 6, 8, 4, 11, 0], 52, 62⟩))) (.node (.node (.node (.leaf ⟨[8, 2, 9, 0, 5, 6], 18, 19⟩) (.leaf ⟨[9, 6, 8, 2, 3, 7], 61, 53⟩)) (.leaf ⟨[8, 4, 11, 0, 1, 2], 65, 66⟩)) (.node (.leaf ⟨[1, 2, 9, 0, 5, 6], 45, 46⟩) (.leaf ⟨[1, 4, 5, 6, 3, 7], 34, 7⟩)))) (.node (.node (.node (.node (.leaf ⟨[5, 6, 3, 7, 8, 2], 10, 11⟩) (.leaf ⟨[11, 0, 1, 2, 9, 6], 42, 43⟩)) (.leaf ⟨[8, 2, 9, 6, 8, 4], 18, 19⟩)) (.node (.leaf ⟨[5, 10, 11, 0, 1, 2], 38, 39⟩) (.leaf ⟨[11, 0, 5, 10, 1, 4], 68, 69⟩))) (.node (.node (.node (.leaf ⟨[5, 6, 3, 7, 9, 10], 10, 11⟩) (.leaf ⟨[3, 7, 9, 10, 1, 7], 26, 27⟩)) (.leaf ⟨[2, 3, 4, 5, 10, 11], 4, 5⟩)) (.node (.leaf ⟨[9, 10, 11, 6, 8, 2], 48, 49⟩) (.leaf ⟨[10, 11, 0, 5, 10, 1], 40, 41⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[3, 4, 5, 6, 3, 7], 6, 7⟩) (.leaf ⟨[7, 8, 4, 11, 0, 1], 78, 79⟩)) (.leaf ⟨[3, 7, 8, 2, 9, 6], 14, 15⟩)) (.node (.leaf ⟨[1, 4, 5, 10, 11, 0], 34, 35⟩) (.leaf ⟨[8, 4, 11, 0, 5, 10], 65, 66⟩))) (.node (.node (.node (.leaf ⟨[9, 0, 5, 6, 3, 7], 22, 23⟩) (.leaf ⟨[8, 2, 3, 7, 9, 10], 56, 57⟩)) (.leaf ⟨[11, 0, 1, 2, 3, 4], 42, 43⟩)) (.node (.leaf ⟨[3, 7, 9, 10, 11, 6], 26, 27⟩) (.leaf ⟨[4, 5, 10, 11, 0, 5], 36, 37⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 7, 8, 2, 9, 0], 14, 15⟩) (.leaf ⟨[1, 2, 9, 6, 8, 2], 45, 46⟩)) (.leaf ⟨[9, 6, 8, 4, 11, 0], 61, 62⟩)) (.node (.leaf ⟨[11, 0, 1, 2, 9, 0], 42, 43⟩) (.leaf ⟨[5, 10, 1, 4, 5, 6], 72, 73⟩))) (.node (.node (.node (.leaf ⟨[3, 7, 9, 10, 1, 4], 26, 27⟩) (.leaf ⟨[9, 10, 1, 7, 8, 4], 30, 31⟩)) (.leaf ⟨[9, 10, 11, 6, 8, 4], 48, 49⟩)) (.node (.leaf ⟨[11, 6, 8, 2, 3, 7], 52, 53⟩) (.leaf ⟨[0, 5, 10, 1, 7, 8], 70, 71⟩))))))) }, { graph := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9], 0, 1⟩) (.leaf ⟨[6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4, 11], 145, 146⟩)) (.leaf ⟨[11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10], 106, 107⟩)) (.node (.leaf ⟨[7, 9, 10, 11, 6, 8, 2, 3, 7, 8, 2, 9], 57, 58⟩) (.leaf ⟨[11, 6, 8, 4, 11, 0, 5, 10, 1, 7, 8, 4], 99, 79⟩))) (.node (.node (.node (.leaf ⟨[7, 9, 10, 1, 4, 5, 10, 11, 0, 1, 2, 9], 32, 33⟩) (.leaf ⟨[10, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9], 121, 105⟩)) (.leaf ⟨[0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3], 124, 125⟩)) (.node (.leaf ⟨[0, 1, 2, 3, 4, 5, 10, 11, 0, 1, 2, 9], 0, 88⟩) (.leaf ⟨[6, 8, 2, 3, 7, 8, 2, 9, 0, 5, 6, 3], 65, 66⟩)))) (.node (.node (.node (.node (.leaf ⟨[7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 1], 16, 17⟩) (.leaf ⟨[4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 5], 84, 85⟩)) (.leaf ⟨[7, 9, 10, 1, 4, 5, 10, 11, 0, 5, 10, 1], 32, 33⟩)) (.node (.leaf ⟨[7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 3], 72, 73⟩) (.leaf ⟨[7, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3], 132, 133⟩))) (.node (.node (.node (.leaf ⟨[0, 1, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11], 48, 49⟩) (.leaf ⟨[7, 9, 10, 11, 6, 8, 2, 3, 7, 9, 10, 1], 57, 58⟩)) (.leaf ⟨[1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 6], 2, 3⟩)) (.node (.leaf ⟨[3, 7, 9, 10, 11, 6, 8, 4, 11, 0, 5, 10], 55, 56⟩) (.leaf ⟨[9, 6, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2], 78, 79⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[4, 5, 6, 3, 7, 8, 2, 9, 0, 5, 6, 3], 8, 9⟩) (.leaf ⟨[7, 9, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3], 152, 153⟩)) (.leaf ⟨[1, 4, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10], 114, 7⟩)) (.node (.leaf ⟨[6, 8, 2, 3, 7, 8, 2, 9, 6, 8, 4, 11], 65, 66⟩) (.leaf ⟨[0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 9], 124, 125⟩))) (.node (.node (.node (.leaf ⟨[4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6, 3], 40, 41⟩) (.leaf ⟨[1, 4, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2], 114, 7⟩)) (.leaf ⟨[7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 6, 3], 132, 133⟩)) (.node (.leaf ⟨[9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 4], 22, 23⟩) (.leaf ⟨[8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6], 18, 19⟩)))) (.node (.node (.node (.node (.leaf ⟨[0, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11], 24, 25⟩) (.leaf ⟨[2, 3, 4, 5, 10, 11, 0, 5, 10, 1, 4, 5], 91, 92⟩)) (.leaf ⟨[4, 5, 10, 11, 0, 5, 10, 1, 7, 8, 4, 11], 117, 118⟩)) (.node (.leaf ⟨[6, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11], 80, 81⟩) (.leaf ⟨[0, 1, 2, 9, 6, 8, 2, 3, 7, 8, 2, 9], 138, 139⟩))) (.node (.node (.leaf ⟨[0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3], 24, 25⟩) (.leaf ⟨[5, 6, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0], 10, 11⟩)) (.node (.leaf ⟨[11, 6, 8, 4, 11, 0, 5, 10, 1, 4, 5, 6], 99, 79⟩) (.leaf ⟨[0, 1, 2, 9, 6, 8, 2, 3, 7, 9, 10, 1], 138, 139⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 0, 5], 4, 5⟩) (.leaf ⟨[2, 3, 7, 9, 10, 1, 7, 8, 4, 11, 0, 1], 149, 29⟩)) (.leaf ⟨[5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 1, 4], 110, 111⟩)) (.node (.leaf ⟨[10, 11, 6, 8, 2, 3, 7, 8, 2, 9, 6, 8], 61, 62⟩) (.leaf ⟨[8, 4, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0], 102, 103⟩))) (.node (.node (.node (.leaf ⟨[10, 1, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5], 36, 37⟩) (.leaf ⟨[5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 11, 6], 110, 111⟩)) (.leaf ⟨[10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5], 128, 129⟩)) (.node (.leaf ⟨[2, 3, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5], 91, 92⟩) (.leaf ⟨[2, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9], 69, 13⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 9, 0, 5, 6, 3, 7, 9, 10, 1, 4, 5], 20, 21⟩) (.leaf ⟨[0, 1, 2, 3, 4, 5, 10, 11, 0, 5, 10, 1], 0, 88⟩)) (.leaf ⟨[10, 1, 4, 5, 10, 11, 0, 5, 10, 1, 7, 8], 36, 37⟩)) (.node (.leaf ⟨[2, 9, 6, 8, 4, 11, 0, 1, 2, 3, 4, 5], 76, 77⟩) (.leaf ⟨[4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 8], 135, 45⟩))) (.node (.node (.node (.leaf ⟨[2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8], 20, 21⟩) (.leaf ⟨[10, 11, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8], 61, 62⟩)) (.leaf ⟨[3, 4, 5, 6, 3, 7, 8, 2, 9, 6, 8, 4], 6, 7⟩)) (.node (.leaf ⟨[9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 4], 95, 96⟩) (.leaf ⟨[4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 9], 135, 45⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[6, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9], 12, 13⟩) (.leaf ⟨[1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10], 130, 131⟩)) (.leaf ⟨[6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 5], 28, 29⟩)) (.node (.leaf ⟨[2, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1], 69, 13⟩) (.leaf ⟨[10, 1, 7, 8, 4, 11, 0, 1, 2, 9, 6, 8], 128, 129⟩))) (.node (.node (.node (.leaf ⟨[10, 11, 0, 1, 2, 9, 0, 5, 6, 3, 7, 9], 44, 45⟩) (.leaf ⟨[6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 9], 53, 54⟩)) (.leaf ⟨[4, 11, 0, 1, 2, 3, 4, 5, 6, 3, 7, 8], 84, 85⟩)) (.node (.leaf ⟨[5, 6, 3, 7, 9, 10, 11, 6, 8, 4, 11, 0], 26, 52⟩) (.leaf ⟨[8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 9, 6], 74, 75⟩)))) (.node (.node (.node (.node (.leaf ⟨[6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 1], 28, 29⟩) (.leaf ⟨[4, 5, 10, 11, 0, 5, 10, 1, 4, 5, 6, 3], 117, 118⟩)) (.leaf ⟨[10, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1], 121, 105⟩)) (.node (.leaf ⟨[4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 1], 84, 85⟩) (.leaf ⟨[2, 9, 6, 8, 2, 3, 7, 8, 2, 9, 0, 5], 142, 143⟩))) (.node (.node (.leaf ⟨[6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 8], 53, 54⟩) (.leaf ⟨[9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 7], 95, 96⟩)) (.node (.leaf ⟨[8, 4, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7], 102, 103⟩) (.leaf ⟨[2, 9, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8], 142, 143⟩))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 0], 2, 3⟩) (.leaf ⟨[8, 2, 3, 7, 9, 10, 1, 7, 8, 4, 11, 0], 147, 148⟩)) (.leaf ⟨[0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 1], 108, 109⟩)) (.node (.leaf ⟨[9, 10, 11, 6, 8, 2, 3, 7, 8, 2, 9, 6], 59, 60⟩) (.leaf ⟨[6, 8, 4, 11, 0, 5, 10, 1, 7, 8, 4, 11], 100, 101⟩))) (.node (.node (.node (.leaf ⟨[9, 10, 1, 4, 5, 10, 11, 0, 1, 2, 9, 0], 34, 35⟩) (.leaf ⟨[0, 5, 10, 1, 4, 5, 6, 3, 7, 9, 10, 11], 108, 109⟩)) (.leaf ⟨[5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4], 126, 127⟩)) (.node (.leaf ⟨[1, 2, 3, 4, 5, 10, 11, 0, 1, 2, 9, 0], 89, 90⟩) (.leaf ⟨[8, 2, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7], 67, 68⟩)))) (.node (.node (.node (.node (.leaf ⟨[8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 1, 4], 18, 19⟩) (.leaf ⟨[11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 5, 10], 86, 87⟩)) (.leaf ⟨[9, 10, 1, 4, 5, 10, 11, 0, 5, 10, 1, 7], 34, 35⟩)) (.node (.leaf ⟨[8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 3, 4], 74, 75⟩) (.leaf ⟨[8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3, 7], 82, 134⟩))) (.node (.node (.node (.leaf ⟨[1, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11, 6], 50, 51⟩) (.leaf ⟨[9, 10, 11, 6, 8, 2, 3, 7, 9, 10, 1, 7], 59, 60⟩)) (.leaf ⟨[2, 3, 4, 5, 6, 3, 7, 8, 2, 9, 6, 8], 4, 5⟩)) (.node (.leaf ⟨[7, 9, 10, 11, 6, 8, 4, 11, 0, 5, 10, 1], 57, 94⟩) (.leaf ⟨[6, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2, 3], 80, 81⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[5, 6, 3, 7, 8, 2, 9, 0, 5, 6, 3, 7], 10, 11⟩) (.leaf ⟨[9, 10, 1, 7, 8, 4, 11, 0, 1, 2, 3, 4], 154, 155⟩)) (.leaf ⟨[4, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11], 115, 116⟩)) (.node (.leaf ⟨[8, 2, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0], 67, 68⟩) (.leaf ⟨[5, 10, 1, 7, 8, 4, 11, 0, 1, 2, 9, 6], 126, 127⟩))) (.node (.node (.node (.leaf ⟨[5, 10, 11, 0, 1, 2, 9, 0, 5, 6, 3, 7], 42, 43⟩) (.leaf ⟨[4, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3], 115, 116⟩)) (.leaf ⟨[8, 4, 11, 0, 1, 2, 3, 4, 5, 6, 3, 7], 82, 83⟩)) (.node (.leaf ⟨[0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 4, 11], 24, 25⟩) (.leaf ⟨[7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2, 9], 72, 73⟩)))) (.node (.node (.node (.node (.leaf ⟨[5, 6, 3, 7, 9, 10, 1, 4, 5, 10, 11, 0], 26, 27⟩) (.leaf ⟨[3, 4, 5, 10, 11, 0, 5, 10, 1, 4, 5, 6], 93, 39⟩)) (.leaf ⟨[5, 10, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0], 119, 120⟩)) (.node (.leaf ⟨[8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11, 0], 82, 83⟩) (.leaf ⟨[1, 2, 9, 6, 8, 2, 3, 7, 8, 2, 9, 0], 140, 141⟩))) (.node (.node (.leaf ⟨[5, 6, 3, 7, 9, 10, 11, 6, 8, 2, 3, 7], 26, 52⟩) (.leaf ⟨[6, 3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1], 12, 13⟩)) (.node (.leaf ⟨[6, 8, 4, 11, 0, 5, 10, 1, 4, 5, 6, 3], 100, 101⟩) (.leaf ⟨[1, 2, 9, 6, 8, 2, 3, 7, 9, 10, 1, 7], 140, 141⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨[3, 4, 5, 6, 3, 7, 8, 2, 9, 0, 5, 6], 6, 7⟩) (.leaf ⟨[3, 7, 9, 10, 1, 7, 8, 4, 11, 0, 1, 2], 150, 151⟩)) (.leaf ⟨[10, 1, 4, 5, 6, 3, 7, 9, 10, 1, 4, 5], 112, 113⟩)) (.node (.leaf ⟨[11, 6, 8, 2, 3, 7, 8, 2, 9, 6, 8, 4], 63, 64⟩) (.leaf ⟨[4, 11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1], 104, 105⟩))) (.node (.node (.node (.leaf ⟨[1, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6], 38, 39⟩) (.leaf ⟨[10, 1, 4, 5, 6, 3, 7, 9, 10, 11, 6, 8], 112, 113⟩)) (.leaf ⟨[1, 7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 6], 130, 131⟩)) (.node (.leaf ⟨[3, 4, 5, 10, 11, 0, 1, 2, 9, 0, 5, 6], 93, 39⟩) (.leaf ⟨[7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10, 11], 16, 17⟩)))) (.node (.node (.node (.node (.leaf ⟨[9, 0, 5, 6, 3, 7, 9, 10, 1, 4, 5, 10], 22, 23⟩) (.leaf ⟨[1, 2, 3, 4, 5, 10, 11, 0, 5, 10, 1, 4], 89, 90⟩)) (.leaf ⟨[1, 4, 5, 10, 11, 0, 5, 10, 1, 7, 8, 4], 38, 39⟩)) (.node (.leaf ⟨[9, 6, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10], 78, 79⟩) (.leaf ⟨[11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 8, 2], 136, 137⟩))) (.node (.node (.node (.leaf ⟨[9, 0, 5, 6, 3, 7, 9, 10, 11, 6, 8, 2], 22, 23⟩) (.leaf ⟨[11, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4], 63, 64⟩)) (.leaf ⟨[4, 5, 6, 3, 7, 8, 2, 9, 6, 8, 4, 11], 8, 9⟩)) (.node (.leaf ⟨[10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 4, 5], 97, 98⟩) (.leaf ⟨[11, 0, 1, 2, 9, 6, 8, 2, 3, 7, 9, 10], 136, 137⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[3, 7, 8, 2, 9, 0, 5, 6, 3, 7, 9, 10], 14, 15⟩) (.leaf ⟨[7, 8, 4, 11, 0, 1, 2, 3, 4, 5, 10, 11], 132, 133⟩)) (.leaf ⟨[3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 5, 10], 30, 31⟩)) (.node (.leaf ⟨[3, 7, 8, 2, 9, 6, 8, 4, 11, 0, 1, 2], 70, 71⟩) (.leaf ⟨[1, 7, 8, 4, 11, 0, 1, 2, 9, 6, 8, 2], 130, 131⟩))) (.node (.node (.node (.leaf ⟨[11, 0, 1, 2, 9, 0, 5, 6, 3, 7, 9, 10], 46, 47⟩) (.leaf ⟨[3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 9, 10], 55, 56⟩)) (.leaf ⟨[11, 0, 1, 2, 3, 4, 5, 6, 3, 7, 8, 2], 86, 87⟩)) (.node (.leaf ⟨[6, 3, 7, 9, 10, 11, 6, 8, 4, 11, 0, 5], 53, 54⟩) (.leaf ⟨[2, 9, 6, 8, 4, 11, 0, 1, 2, 9, 6, 8], 76, 77⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 7, 9, 10, 1, 4, 5, 10, 11, 0, 1, 2], 30, 31⟩) (.leaf ⟨[5, 10, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7], 119, 120⟩)) (.leaf ⟨[11, 0, 5, 10, 1, 7, 8, 4, 11, 0, 1, 2], 122, 123⟩)) (.node (.leaf ⟨[11, 0, 1, 2, 3, 4, 5, 10, 11, 0, 1, 2], 86, 87⟩) (.leaf ⟨[9, 6, 8, 2, 3, 7, 8, 2, 9, 0, 5, 6], 144, 64⟩))) (.node (.node (.leaf ⟨[3, 7, 9, 10, 11, 6, 8, 2, 3, 7, 8, 2], 55, 56⟩) (.leaf ⟨[10, 11, 6, 8, 4, 11, 0, 5, 10, 1, 7, 8], 97, 98⟩)) (.node (.leaf ⟨[4, 11, 0, 5, 10, 1, 4, 5, 6, 3, 7, 9], 104, 105⟩) (.leaf ⟨[9, 6, 8, 2, 3, 7, 9, 10, 1, 7, 8, 4], 144, 64⟩)))))))) }] }

def cert_grayMod4_overlap : OverlapAvoidCert :=
  { syncCert := { width := 1, parityMask := 0xa, graph := (.node (.node (.leaf ⟨false, [0], 0, 1⟩) (.leaf ⟨false, [2], 2, 3⟩)) (.node (.leaf ⟨true, [1], 2, 1⟩) (.leaf ⟨true, [3], 0, 3⟩))) },
    reachPar := (.node (.node (.leaf ⟨false, [0], 0, 1⟩) (.leaf ⟨false, [2], 2, 3⟩)) (.node (.leaf ⟨true, [1], 2, 1⟩) (.leaf ⟨true, [3], 0, 3⟩))),
    invPair := [4, 0, 4, 3, 4, 4, 4, 4, 4, 1, 4, 2, 4, 4, 4, 4],
    invEvenPar0 := [0, 4, 2, 4],
    invEvenPar1 := [3, 4, 1, 4],
    invOddPar0 := [4, 0, 4, 2],
    invOddPar1 := [4, 1, 4, 3],
    baseCerts := [{ graph := (.node (.node (.node (.node (.leaf ⟨[0, 1, 2], 0, 1⟩) (.leaf ⟨[0, 3, 2], 12, 13⟩)) (.node (.leaf ⟨[2, 3, 2], 6, 7⟩) (.leaf ⟨[0, 1, 0], 0, 1⟩))) (.node (.node (.leaf ⟨[2, 1, 2], 4, 5⟩) (.leaf ⟨[0, 3, 0], 12, 13⟩)) (.node (.leaf ⟨[2, 3, 0], 6, 7⟩) (.leaf ⟨[2, 1, 0], 4, 5⟩)))) (.node (.node (.node (.leaf ⟨[1, 2, 1], 2, 3⟩) (.leaf ⟨[3, 2, 3], 8, 9⟩)) (.node (.leaf ⟨[3, 2, 1], 8, 9⟩) (.leaf ⟨[1, 0, 3], 14, 15⟩))) (.node (.node (.leaf ⟨[1, 2, 3], 2, 3⟩) (.leaf ⟨[3, 0, 1], 10, 11⟩)) (.node (.leaf ⟨[3, 0, 3], 10, 11⟩) (.leaf ⟨[1, 0, 1], 14, 15⟩))))) }] }

def cert_carryXor5_abelian_w6 : WindowCert :=
  { graph := (.node (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3, 4, 5], 0, 1⟩) (.leaf ⟨[5, 10, 1, 7, 8, 4], 72, 73⟩)) (.leaf ⟨[6, 8, 2, 3, 7, 8], 54, 55⟩)) (.node (.leaf ⟨[7, 9, 10, 1, 4, 5], 28, 29⟩) (.leaf ⟨[10, 11, 6, 8, 4, 11], 50, 51⟩))) (.node (.node (.node (.leaf ⟨[7, 8, 2, 9, 0, 5], 16, 17⟩) (.leaf ⟨[2, 9, 6, 8, 2, 3], 59, 60⟩)) (.leaf ⟨[6, 8, 4, 11, 0, 1], 63, 64⟩)) (.node (.leaf ⟨[0, 1, 2, 9, 0, 5], 0, 44⟩) (.leaf ⟨[10, 1, 4, 5, 6, 3], 32, 33⟩)))) (.node (.node (.node (.node (.leaf ⟨[4, 5, 6, 3, 7, 8], 8, 9⟩) (.leaf ⟨[4, 11, 0, 1, 2, 9], 67, 41⟩)) (.leaf ⟨[7, 8, 2, 9, 6, 8], 16, 17⟩)) (.node (.leaf ⟨[4, 5, 10, 11, 0, 1], 36, 37⟩) (.leaf ⟨[4, 11, 0, 5, 10, 1], 67, 41⟩))) (.node (.node (.node (.leaf ⟨[0, 5, 6, 3, 7, 9], 24, 25⟩) (.leaf ⟨[2, 3, 7, 9, 10, 1], 58, 13⟩)) (.leaf ⟨[1, 2, 3, 4, 5, 10], 2, 3⟩)) (.node (.leaf ⟨[7, 9, 10, 11, 6, 8], 28, 47⟩) (.leaf ⟨[5, 10, 11, 0, 5, 10], 38, 39⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 5, 6, 3], 4, 5⟩) (.leaf ⟨[1, 7, 8, 4, 11, 0], 76, 77⟩)) (.leaf ⟨[2, 3, 7, 8, 2, 9], 58, 13⟩)) (.node (.leaf ⟨[10, 1, 4, 5, 10, 11], 32, 33⟩) (.leaf ⟨[6, 8, 4, 11, 0, 5], 63, 64⟩))) (.node (.node (.node (.leaf ⟨[2, 9, 0, 5, 6, 3], 20, 21⟩) (.leaf ⟨[6, 8, 2, 3, 7, 9], 54, 55⟩)) (.leaf ⟨[4, 11, 0, 1, 2, 3], 67, 41⟩)) (.node (.leaf ⟨[6, 3, 7, 9, 10, 11], 12, 13⟩) (.leaf ⟨[4, 5, 6, 3, 7, 9], 8, 9⟩)))) (.node (.node (.node (.node (.leaf ⟨[6, 3, 7, 8, 2, 9], 12, 13⟩) (.leaf ⟨[0, 1, 2, 9, 6, 8], 0, 44⟩)) (.leaf ⟨[2, 9, 6, 8, 4, 11], 59, 60⟩)) (.node (.leaf ⟨[10, 11, 0, 1, 2, 9], 40, 41⟩) (.leaf ⟨[0, 5, 10, 1, 4, 5], 70, 71⟩))) (.node (.node (.node (.leaf ⟨[6, 3, 7, 9, 10, 1], 12, 13⟩) (.leaf ⟨[7, 9, 10, 1, 7, 8], 28, 29⟩)) (.leaf ⟨[3, 4, 5, 10, 11, 0], 6, 35⟩)) (.node (.leaf ⟨[10, 11, 6, 8, 2, 3], 50, 51⟩) (.leaf ⟨[11, 0, 5, 10, 1, 7], 68, 69⟩)))))) (.node (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 4, 5, 6], 2, 3⟩) (.leaf ⟨[10, 1, 7, 8, 4, 11], 74, 75⟩)) (.leaf ⟨[8, 2, 3, 7, 8, 2], 56, 57⟩)) (.node (.leaf ⟨[9, 10, 1, 4, 5, 10], 30, 31⟩) (.leaf ⟨[11, 6, 8, 4, 11, 0], 52, 62⟩))) (.node (.node (.node (.leaf ⟨[8, 2, 9, 0, 5, 6], 18, 19⟩) (.leaf ⟨[9, 6, 8, 2, 3, 7], 61, 53⟩)) (.leaf ⟨[8, 4, 11, 0, 1, 2], 65, 66⟩)) (.node (.leaf ⟨[1, 2, 9, 0, 5, 6], 45, 46⟩) (.leaf ⟨[1, 4, 5, 6, 3, 7], 34, 7⟩)))) (.node (.node (.node (.node (.leaf ⟨[5, 6, 3, 7, 8, 2], 10, 11⟩) (.leaf ⟨[11, 0, 1, 2, 9, 6], 42, 43⟩)) (.leaf ⟨[8, 2, 9, 6, 8, 4], 18, 19⟩)) (.node (.leaf ⟨[5, 10, 11, 0, 1, 2], 38, 39⟩) (.leaf ⟨[11, 0, 5, 10, 1, 4], 68, 69⟩))) (.node (.node (.node (.leaf ⟨[5, 6, 3, 7, 9, 10], 10, 11⟩) (.leaf ⟨[3, 7, 9, 10, 1, 7], 26, 27⟩)) (.leaf ⟨[2, 3, 4, 5, 10, 11], 4, 5⟩)) (.node (.leaf ⟨[9, 10, 11, 6, 8, 2], 48, 49⟩) (.leaf ⟨[10, 11, 0, 5, 10, 1], 40, 41⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[3, 4, 5, 6, 3, 7], 6, 7⟩) (.leaf ⟨[7, 8, 4, 11, 0, 1], 78, 79⟩)) (.leaf ⟨[3, 7, 8, 2, 9, 6], 14, 15⟩)) (.node (.leaf ⟨[1, 4, 5, 10, 11, 0], 34, 35⟩) (.leaf ⟨[8, 4, 11, 0, 5, 10], 65, 66⟩))) (.node (.node (.node (.leaf ⟨[9, 0, 5, 6, 3, 7], 22, 23⟩) (.leaf ⟨[8, 2, 3, 7, 9, 10], 56, 57⟩)) (.leaf ⟨[11, 0, 1, 2, 3, 4], 42, 43⟩)) (.node (.leaf ⟨[3, 7, 9, 10, 11, 6], 26, 27⟩) (.leaf ⟨[4, 5, 10, 11, 0, 5], 36, 37⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 7, 8, 2, 9, 0], 14, 15⟩) (.leaf ⟨[1, 2, 9, 6, 8, 2], 45, 46⟩)) (.leaf ⟨[9, 6, 8, 4, 11, 0], 61, 62⟩)) (.node (.leaf ⟨[11, 0, 1, 2, 9, 0], 42, 43⟩) (.leaf ⟨[5, 10, 1, 4, 5, 6], 72, 73⟩))) (.node (.node (.node (.leaf ⟨[3, 7, 9, 10, 1, 4], 26, 27⟩) (.leaf ⟨[9, 10, 1, 7, 8, 4], 30, 31⟩)) (.leaf ⟨[9, 10, 11, 6, 8, 4], 48, 49⟩)) (.node (.leaf ⟨[11, 6, 8, 2, 3, 7], 52, 53⟩) (.leaf ⟨[0, 5, 10, 1, 7, 8], 70, 71⟩))))))) }

def cert_carryXor3_abelian_w8 : WindowCert :=
  { graph := (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3, 2, 4, 4, 3], 0, 1⟩) (.leaf ⟨[0, 1, 2, 3, 2, 3, 1, 5], 0, 1⟩)) (.node (.leaf ⟨[2, 4, 0, 5, 0, 1, 1, 5], 16, 17⟩) (.leaf ⟨[2, 4, 4, 3, 2, 3, 1, 5], 8, 9⟩))) (.node (.node (.leaf ⟨[2, 4, 0, 5, 0, 5, 4, 3], 16, 17⟩) (.leaf ⟨[3, 1, 5, 0, 1, 1, 5, 0], 50, 35⟩)) (.leaf ⟨[0, 1, 1, 5, 0, 5, 4, 3], 32, 33⟩))) (.node (.node (.node (.leaf ⟨[2, 4, 4, 3, 2, 4, 0, 5], 8, 9⟩) (.leaf ⟨[2, 3, 1, 5, 0, 1, 2, 3], 48, 49⟩)) (.node (.leaf ⟨[0, 1, 1, 5, 0, 1, 1, 5], 32, 33⟩) (.leaf ⟨[0, 5, 4, 3, 2, 4, 4, 3], 24, 25⟩))) (.node (.node (.leaf ⟨[0, 5, 4, 3, 2, 4, 0, 5], 24, 25⟩) (.leaf ⟨[2, 4, 4, 3, 2, 4, 4, 3], 8, 9⟩)) (.leaf ⟨[0, 1, 1, 5, 0, 1, 2, 3], 32, 33⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 3, 2, 4, 4, 3, 2, 4], 4, 5⟩) (.leaf ⟨[2, 3, 2, 3, 1, 5, 0, 1], 44, 45⟩)) (.node (.leaf ⟨[0, 5, 0, 1, 1, 5, 0, 1], 28, 29⟩) (.leaf ⟨[4, 3, 2, 3, 1, 5, 0, 1], 52, 53⟩))) (.node (.node (.leaf ⟨[0, 5, 0, 5, 4, 3, 2, 4], 20, 21⟩) (.leaf ⟨[5, 0, 1, 2, 3, 2, 4, 4], 41, 42⟩)) (.leaf ⟨[1, 5, 0, 5, 4, 3, 2, 4], 39, 40⟩))) (.node (.node (.node (.leaf ⟨[4, 3, 2, 4, 0, 5, 0, 5], 12, 13⟩) (.leaf ⟨[3, 2, 3, 1, 5, 0, 1, 1], 46, 47⟩)) (.leaf ⟨[1, 5, 0, 1, 1, 5, 0, 5], 36, 37⟩)) (.node (.node (.leaf ⟨[4, 3, 2, 4, 0, 5, 0, 1], 12, 13⟩) (.leaf ⟨[4, 3, 2, 4, 4, 3, 2, 3], 12, 13⟩)) (.leaf ⟨[1, 5, 0, 1, 2, 3, 2, 3], 36, 37⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 2, 4, 4, 3, 2], 2, 3⟩) (.leaf ⟨[1, 2, 3, 2, 3, 1, 5, 0], 2, 43⟩)) (.node (.leaf ⟨[4, 0, 5, 0, 1, 1, 5, 0], 18, 27⟩) (.leaf ⟨[4, 4, 3, 2, 3, 1, 5, 0], 10, 51⟩))) (.node (.node (.leaf ⟨[4, 0, 5, 0, 5, 4, 3, 2], 18, 19⟩) (.leaf ⟨[1, 5, 0, 1, 2, 3, 2, 4], 36, 37⟩)) (.leaf ⟨[1, 1, 5, 0, 5, 4, 3, 2], 34, 38⟩))) (.node (.node (.node (.leaf ⟨[4, 4, 3, 2, 4, 0, 5, 0], 10, 11⟩) (.leaf ⟨[3, 1, 5, 0, 1, 2, 3, 2], 50, 35⟩)) (.node (.leaf ⟨[1, 1, 5, 0, 1, 1, 5, 0], 34, 35⟩) (.leaf ⟨[5, 4, 3, 2, 4, 4, 3, 2], 26, 11⟩))) (.node (.node (.leaf ⟨[5, 4, 3, 2, 4, 0, 5, 0], 26, 11⟩) (.leaf ⟨[4, 4, 3, 2, 4, 4, 3, 2], 10, 11⟩)) (.leaf ⟨[1, 1, 5, 0, 1, 2, 3, 2], 34, 35⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 2, 4, 4, 3, 2, 4, 0], 6, 7⟩) (.leaf ⟨[3, 2, 3, 1, 5, 0, 1, 2], 46, 47⟩)) (.node (.leaf ⟨[5, 0, 1, 1, 5, 0, 1, 1], 30, 31⟩) (.leaf ⟨[5, 0, 5, 4, 3, 2, 4, 4], 22, 23⟩))) (.node (.node (.leaf ⟨[5, 0, 5, 4, 3, 2, 4, 0], 22, 23⟩) (.leaf ⟨[3, 2, 4, 4, 3, 2, 4, 4], 6, 7⟩)) (.leaf ⟨[5, 0, 1, 1, 5, 0, 1, 2], 30, 31⟩))) (.node (.node (.node (.leaf ⟨[3, 2, 4, 0, 5, 0, 5, 4], 14, 15⟩) (.leaf ⟨[2, 3, 1, 5, 0, 1, 1, 5], 48, 49⟩)) (.leaf ⟨[5, 0, 1, 1, 5, 0, 5, 4], 30, 31⟩)) (.node (.node (.leaf ⟨[3, 2, 4, 0, 5, 0, 1, 1], 14, 15⟩) (.leaf ⟨[3, 2, 4, 4, 3, 2, 3, 1], 6, 7⟩)) (.leaf ⟨[5, 0, 1, 2, 3, 2, 3, 1], 41, 42⟩)))))) }

def cert_carryXor5_no4run : WindowCert :=
  { graph := (.node (.node (.node (.node (.node (.node (.leaf ⟨[0, 1, 2, 3], 0, 1⟩) (.leaf ⟨[8, 2, 9, 6], 17, 18⟩)) (.node (.leaf ⟨[9, 10, 1, 4], 27, 28⟩) (.leaf ⟨[1, 7, 8, 4], 52, 14⟩))) (.node (.node (.leaf ⟨[7, 8, 2, 9], 15, 16⟩) (.leaf ⟨[4, 11, 0, 5], 49, 36⟩)) (.leaf ⟨[1, 2, 9, 0], 2, 38⟩))) (.node (.node (.node (.leaf ⟨[4, 5, 6, 3], 8, 9⟩) (.leaf ⟨[8, 4, 11, 0], 47, 48⟩)) (.node (.leaf ⟨[5, 10, 11, 0], 33, 34⟩) (.leaf ⟨[2, 3, 7, 9], 4, 5⟩))) (.node (.node (.leaf ⟨[0, 5, 6, 3], 23, 24⟩) (.leaf ⟨[1, 4, 5, 6], 31, 7⟩)) (.leaf ⟨[11, 6, 8, 2], 40, 41⟩)))) (.node (.node (.node (.node (.leaf ⟨[2, 3, 4, 5], 4, 5⟩) (.leaf ⟨[9, 6, 8, 4], 45, 41⟩)) (.node (.leaf ⟨[1, 4, 5, 10], 31, 7⟩) (.leaf ⟨[1, 2, 9, 6], 2, 38⟩))) (.node (.node (.leaf ⟨[2, 9, 0, 5], 19, 20⟩) (.leaf ⟨[0, 5, 10, 1], 23, 50⟩)) (.leaf ⟨[9, 10, 11, 6], 27, 39⟩))) (.node (.node (.node (.leaf ⟨[6, 3, 7, 8], 12, 5⟩) (.leaf ⟨[3, 4, 5, 10], 6, 7⟩)) (.leaf ⟨[11, 0, 1, 2], 37, 22⟩)) (.node (.node (.leaf ⟨[3, 7, 9, 10], 13, 14⟩) (.leaf ⟨[5, 10, 1, 7], 33, 51⟩)) (.leaf ⟨[8, 2, 3, 7], 17, 44⟩))))) (.node (.node (.node (.node (.node (.leaf ⟨[1, 2, 3, 4], 2, 3⟩) (.leaf ⟨[2, 9, 6, 8], 19, 20⟩)) (.node (.leaf ⟨[10, 1, 4, 5], 29, 30⟩) (.leaf ⟨[7, 8, 4, 11], 15, 53⟩))) (.node (.node (.leaf ⟨[8, 2, 9, 0], 17, 18⟩) (.leaf ⟨[11, 0, 5, 10], 37, 22⟩)) (.leaf ⟨[7, 9, 10, 11], 25, 26⟩))) (.node (.node (.node (.leaf ⟨[5, 6, 3, 7], 10, 11⟩) (.leaf ⟨[4, 11, 0, 1], 49, 36⟩)) (.node (.leaf ⟨[10, 11, 0, 1], 35, 36⟩) (.leaf ⟨[9, 10, 1, 7], 27, 28⟩))) (.node (.node (.leaf ⟨[6, 3, 7, 9], 12, 5⟩) (.leaf ⟨[10, 11, 0, 5], 35, 36⟩)) (.leaf ⟨[6, 8, 2, 3], 42, 43⟩)))) (.node (.node (.node (.node (.leaf ⟨[3, 4, 5, 6], 6, 7⟩) (.leaf ⟨[6, 8, 4, 11], 42, 46⟩)) (.node (.leaf ⟨[4, 5, 10, 11], 8, 32⟩) (.leaf ⟨[9, 6, 8, 2], 45, 41⟩))) (.node (.node (.leaf ⟨[9, 0, 5, 6], 21, 22⟩) (.leaf ⟨[5, 10, 1, 4], 33, 51⟩)) (.leaf ⟨[10, 11, 6, 8], 35, 36⟩))) (.node (.node (.node (.leaf ⟨[3, 7, 8, 2], 13, 14⟩) (.leaf ⟨[11, 6, 8, 4], 40, 41⟩)) (.leaf ⟨[0, 1, 2, 9], 0, 1⟩)) (.node (.node (.leaf ⟨[7, 9, 10, 1], 25, 26⟩) (.leaf ⟨[10, 1, 7, 8], 29, 30⟩)) (.leaf ⟨[2, 3, 7, 8], 4, 5⟩)))))) }

-- ============================================================================
-- Section 9: Native Silicon Compilation Theorems (decide -> ∀ n : Nat)
-- ============================================================================

theorem carryXor3_eq_dfao : ∀ n : Nat, carryXor 3 n = dfao_carryXor3.evalWord n :=
  carryXorModel_sound 3 dfao_carryXor3 vecTable_carryXor3 (by decide)

theorem carryAnd3_eq_dfao : ∀ n : Nat, carryAnd 3 n = dfao_carryAnd3.evalWord n :=
  carryAndModel_sound 3 dfao_carryAnd3 vecTable_carryAnd3 (by decide)

theorem carryAnd5_eq_dfao : ∀ n : Nat, carryAnd 5 n = dfao_carryAnd5.evalWord n :=
  carryAndModel_sound 5 dfao_carryAnd5 vecTable_carryAnd5 (by decide)

theorem carryXor5_eq_dfao : ∀ n : Nat, carryXor 5 n = dfao_carryXor5.evalWord n :=
  carryXorModel_sound 5 dfao_carryXor5 vecTable_carryXor5 (by decide)

theorem grayMod4_eq_dfao : ∀ n : Nat, grayMod4 n = dfao_grayMod4.evalWord n := by
  have hwf : dfao_grayMod4.wf = true := by decide
  have hstate : ∀ n : Nat, dfao_grayMod4.evalState n = grayMod4 n := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      cases n with
      | zero => rfl
      | succ m =>
        have hdiv : (m + 1) / 2 < m + 1 := by omega
        have hih := ih ((m + 1) / 2) hdiv
        have hpar_g := popcount_gray_mod_two ((m + 1) / 2)
        have hlt : grayMod4 ((m + 1) / 2) < 4 := Nat.mod_lt _ (by omega)
        have hmod2 : grayMod4 ((m + 1) / 2) % 2 = ((m + 1) / 2) % 2 := by
          unfold grayMod4
          omega
        by_cases hp : (m + 1) % 2 = 0
        · have hm : m + 1 = 2 * ((m + 1) / 2) := by omega
          have hst : dfao_grayMod4.evalState (m + 1) = dfao_grayMod4.step0 (dfao_grayMod4.evalState ((m + 1) / 2)) :=
            (congrArg dfao_grayMod4.evalState hm).trans (dfao_grayMod4.evalState_two_mul hwf _)
          rw [hst, hih]
          have hstep := popcount_gray_step ((m + 1) / 2) 0 (by omega)
          have hgm : grayMod4 (m + 1) = (grayMod4 ((m + 1) / 2) + ((m + 1) / 2) % 2) % 4 := by
            unfold grayMod4
            have h3 : (m + 1) ^^^ ((m + 1) / 2) = (2 * ((m + 1) / 2) + 0) ^^^ ((m + 1) / 2) := by
              congr 1
            rw [h3, hstep]
            omega
          rw [hgm]
          have hcases : grayMod4 ((m + 1) / 2) = 0 ∨ grayMod4 ((m + 1) / 2) = 1 ∨
                        grayMod4 ((m + 1) / 2) = 2 ∨ grayMod4 ((m + 1) / 2) = 3 := by omega
          rcases hcases with h | h | h | h
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step0]; omega
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step0]; omega
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step0]; omega
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step0]; omega
        · have hm : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
          have hst : dfao_grayMod4.evalState (m + 1) = dfao_grayMod4.step1 (dfao_grayMod4.evalState ((m + 1) / 2)) :=
            (congrArg dfao_grayMod4.evalState hm).trans (dfao_grayMod4.evalState_two_mul_add_one _)
          rw [hst, hih]
          have hstep := popcount_gray_step ((m + 1) / 2) 1 (by omega)
          have hgm : grayMod4 (m + 1) = (grayMod4 ((m + 1) / 2) + (1 + ((m + 1) / 2) % 2) % 2) % 4 := by
            unfold grayMod4
            have h3 : (m + 1) ^^^ ((m + 1) / 2) = (2 * ((m + 1) / 2) + 1) ^^^ ((m + 1) / 2) := by
              congr 1
            rw [h3, hstep]
            omega
          rw [hgm]
          have hcases : grayMod4 ((m + 1) / 2) = 0 ∨ grayMod4 ((m + 1) / 2) = 1 ∨
                        grayMod4 ((m + 1) / 2) = 2 ∨ grayMod4 ((m + 1) / 2) = 3 := by omega
          rcases hcases with h | h | h | h
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step1]; omega
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step1]; omega
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step1]; omega
          · rw [h] at hmod2 ⊢; simp [dfao_grayMod4, DFAO.step1]; omega
  intro n
  rw [DFAO.evalWord, hstate n]
  have hlt : grayMod4 n < 4 := Nat.mod_lt _ (by omega)
  have hcases : grayMod4 n = 0 ∨ grayMod4 n = 1 ∨ grayMod4 n = 2 ∨ grayMod4 n = 3 := by omega
  rcases hcases with h | h | h | h <;> rw [h] <;> decide

-- ============================================================================
-- Section 10: Concrete Novel Infinite Pure-Silicon Theorems (T1..T8)
-- ============================================================================

/-- T1: Carry-XOR Parity `popcount((3*n) ^^^ n) % 2` avoids ALL 4th powers (∀ n, ∀ p ≥ 1). -/
theorem carryXor3_four_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 3 * p ∧ carryXor 3 (n + j) ≠ carryXor 3 (n + p + j) := by
  have h := powerAvoidCert_sound dfao_carryXor3 4 cert_carryXor3_k4 (by decide)
  intro n p hp
  rcases h n p hp with ⟨j, hj, hne⟩
  exact ⟨j, hj, by rwa [carryXor3_eq_dfao, carryXor3_eq_dfao]⟩

/-- T2: Carry-AND Overlap Parity `popcount((3*n) &&& n) % 2` avoids ALL 5th powers (∀ n, ∀ p ≥ 1). -/
theorem carryAnd3_five_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 4 * p ∧ carryAnd 3 (n + j) ≠ carryAnd 3 (n + p + j) := by
  have h := powerAvoidCert_sound dfao_carryAnd3 5 cert_carryAnd3_k5 (by decide)
  intro n p hp
  rcases h n p hp with ⟨j, hj, hne⟩
  exact ⟨j, hj, by rwa [carryAnd3_eq_dfao, carryAnd3_eq_dfao]⟩

/-- T3: Shift-4 Carry-AND Overlap Parity `popcount((5*n) &&& n) % 2` avoids ALL 4th powers (∀ n, ∀ p ≥ 1). -/
theorem carryAnd5_four_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 3 * p ∧ carryAnd 5 (n + j) ≠ carryAnd 5 (n + p + j) := by
  have h := powerAvoidCert_sound dfao_carryAnd5 4 cert_carryAnd5_k4 (by decide)
  intro n p hp
  rcases h n p hp with ⟨j, hj, hne⟩
  exact ⟨j, hj, by rwa [carryAnd5_eq_dfao, carryAnd5_eq_dfao]⟩

/-- T4: Shift-4 Carry-XOR Parity `popcount((5*n) ^^^ n) % 2` avoids ALL 6th powers (∀ n, ∀ p ≥ 1). -/
theorem carryXor5_six_power_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j < 5 * p ∧ carryXor 5 (n + j) ≠ carryXor 5 (n + p + j) := by
  have h := powerAvoidCert_sound dfao_carryXor5 6 cert_carryXor5_k6 (by decide)
  intro n p hp
  rcases h n p hp with ⟨j, hj, hne⟩
  exact ⟨j, hj, by rwa [carryXor5_eq_dfao, carryXor5_eq_dfao]⟩

/-- T5: Gray-Code Hamming Weight Mod 4 `popcount(n ^^^ (n / 2)) % 4` is OVERLAP-FREE (∀ n, ∀ p ≥ 1). -/
theorem grayMod4_overlap_free :
    ∀ n p : Nat, p ≥ 1 → ∃ j : Nat, j ≤ p ∧ grayMod4 (n + j) ≠ grayMod4 (n + p + j) := by
  have h := overlapAvoidCert_sound dfao_grayMod4 cert_grayMod4_overlap (by decide)
  intro n p hp
  rcases h n p hp with ⟨j, hj, hne⟩
  exact ⟨j, hj, by rwa [grayMod4_eq_dfao, grayMod4_eq_dfao]⟩

/-- T6: Tight Abelian Window Balance: every length-6 window of `carryXor 5` has Hamming weight in [2, 4]. -/
theorem carryXor5_abelian_window6 :
    ∀ n : Nat, 2 ≤ windowSum (carryXor 5) 6 n ∧ windowSum (carryXor 5) 6 n ≤ 4 := by
  have h := windowCert_sound dfao_carryXor5 6 (windowWeightInRange 2 4) cert_carryXor5_abelian_w6 (by decide)
  intro n
  have hw := windowWeightInRange_sound (h n)
  have heq : windowSum (carryXor 5) 6 n = windowSum dfao_carryXor5.evalWord 6 n := by
    simp [windowSum, carryXor5_eq_dfao]
  rwa [heq]

/-- T7: Abelian Window Balance: every length-8 window of `carryXor 3` has Hamming weight in [2, 6]. -/
theorem carryXor3_abelian_window8 :
    ∀ n : Nat, 2 ≤ windowSum (carryXor 3) 8 n ∧ windowSum (carryXor 3) 8 n ≤ 6 := by
  have h := windowCert_sound dfao_carryXor3 8 (windowWeightInRange 2 6) cert_carryXor3_abelian_w8 (by decide)
  intro n
  have hw := windowWeightInRange_sound (h n)
  have heq : windowSum (carryXor 3) 8 n = windowSum dfao_carryXor3.evalWord 8 n := by
    simp [windowSum, carryXor3_eq_dfao]
  rwa [heq]

/-- T8: `carryXor 5` avoids ALL 4-runs (p = 1), even though it contains a 5th power at period p = 3! -/
theorem carryXor5_no_four_run :
    ∀ n : Nat, ∃ j : Nat, j < 3 ∧ carryXor 5 (n + j) ≠ carryXor 5 (n + 1 + j) := by
  have h := windowCert_sound dfao_carryXor5 4 (noPowerAtPeriod 4 1) cert_carryXor5_no4run (by decide)
  intro n
  rcases noPowerAtPeriod_sound (k := 4) (p := 1) (by omega) (h n) with ⟨j, hj, hne⟩
  exact ⟨j, by omega, by rwa [carryXor5_eq_dfao, carryXor5_eq_dfao]⟩

-- ============================================================================
-- Section 11: Kernel-Checked Sharpness Counterexamples & Non-Vacuity Witnesses
-- ============================================================================

/-- Sharpness for T1: `carryXor 3` has an exact 3rd power (cube `000`) at n = 5, p = 1. -/
theorem carryXor3_has_cube :
    ∃ n p : Nat, p ≥ 1 ∧ ∀ j < 2 * p, carryXor 3 (n + j) = carryXor 3 (n + p + j) := by
  refine ⟨5, 1, by omega, ?_⟩
  intro j hj
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl <;> decide

/-- Sharpness for T2: `carryAnd 3` has an exact 4th power (`1111`) at n = 1, p = 1. -/
theorem carryAnd3_has_fourth_power :
    ∃ n p : Nat, p ≥ 1 ∧ ∀ j < 3 * p, carryAnd 3 (n + j) = carryAnd 3 (n + p + j) := by
  refine ⟨1, 1, by omega, ?_⟩
  intro j hj
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> decide

/-- Sharpness for T3: `carryAnd 5` has an exact fractional (7/2)-power at n = 37, p = 2
    (length 7 = 3.5 * 2: `0101010`), plus a cube `111` at n = 19, p = 1. -/
theorem carryAnd5_has_seven_half_power :
    ∃ n p : Nat, p ≥ 1 ∧ ∀ j < 5, carryAnd 5 (n + j) = carryAnd 5 (n + p + j) := by
  refine ⟨37, 2, by omega, ?_⟩
  intro j hj
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Sharpness for T4: `carryXor 5` has an exact 5th power of period p = 3 at n = 153 (`(010)^5`),
    showing T4 (6-power-free) is sharp even though T8 forbids all 4-runs at p = 1! -/
theorem carryXor5_has_fifth_power_period3 :
    ∃ n p : Nat, p ≥ 1 ∧ ∀ j < 4 * p, carryXor 5 (n + j) = carryXor 5 (n + p + j) := by
  refine ⟨153, 3, by omega, ?_⟩
  intro j hj
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => decide
  | j + 12 => omega

/-- Sharpness for T5: `grayMod4` has an exact square (`1212`) at n = 1, p = 2. -/
theorem grayMod4_has_square :
    ∃ n p : Nat, p ≥ 1 ∧ ∀ j < p, grayMod4 (n + j) = grayMod4 (n + p + j) := by
  refine ⟨1, 2, by omega, ?_⟩
  intro j hj
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl <;> decide

/-- Sharpness for T6: `carryXor 5` length-6 windows attain both extremes 2 (at n = 6) and 4 (at n = 0). -/
theorem carryXor5_abelian_window6_sharp :
    (∃ n, windowSum (carryXor 5) 6 n = 2) ∧ (∃ n, windowSum (carryXor 5) 6 n = 4) :=
  ⟨⟨6, by decide⟩, ⟨0, by decide⟩⟩

/-- Sharpness for T7: `carryXor 3` length-8 windows attain both extremes 2 (at n = 3) and 6 (at n = 19). -/
theorem carryXor3_abelian_window8_sharp :
    (∃ n, windowSum (carryXor 3) 8 n = 2) ∧ (∃ n, windowSum (carryXor 3) 8 n = 6) :=
  ⟨⟨3, by decide⟩, ⟨19, by decide⟩⟩

/-- Non-vacuity witness: all 5 silicon sequences are non-constant and all certificates are inhabited & valid. -/
theorem non_vacuity_witnesses :
    (carryXor 3 0 ≠ carryXor 3 1) ∧
    (carryAnd 3 0 ≠ carryAnd 3 1) ∧
    (carryAnd 5 0 ≠ carryAnd 5 1) ∧
    (carryXor 5 0 ≠ carryXor 5 1) ∧
    (grayMod4 0 = 0 ∧ grayMod4 1 = 1 ∧ grayMod4 2 = 2 ∧ grayMod4 5 = 3) ∧
    checkPowerAvoidCert dfao_carryXor3 4 cert_carryXor3_k4 = true ∧
    checkPowerAvoidCert dfao_carryAnd3 5 cert_carryAnd3_k5 = true ∧
    checkPowerAvoidCert dfao_carryAnd5 4 cert_carryAnd5_k4 = true ∧
    checkPowerAvoidCert dfao_carryXor5 6 cert_carryXor5_k6 = true ∧
    checkOverlapAvoidCert dfao_grayMod4 cert_grayMod4_overlap = true := by
  decide

-- ============================================================================
-- Section 12: Kernel-Checked Negative / Hostile Mutation Tests (checkCert = false)
-- ============================================================================

def mutateRootWindowEdge0 (c : WindowCert) : WindowCert :=
  let rec go : BTree WindowNode → BTree WindowNode
    | .empty => .empty
    | .leaf nd => .leaf { nd with next0 := nd.next0 + 1 }
    | .node l r => .node (go l) r
  { graph := go c.graph }

def mutateRootWindowInit (c : WindowCert) : WindowCert :=
  let rec go : BTree WindowNode → BTree WindowNode
    | .empty => .empty
    | .leaf nd => .leaf { nd with win := 99 :: nd.win.tail }
    | .node l r => .node (go l) r
  { graph := go c.graph }

def mutateSyncMask (M : DFAO) (c : SyncCert) : SyncCert :=
  let code0 := encodeWord M.numAlpha ((stateWindow M c.width 0).map M.out)
  { c with parityMask := c.parityMask ^^^ (1 <<< code0) }

def mutateRootSyncParity (c : SyncCert) : SyncCert :=
  let rec go : BTree SyncNode → BTree SyncNode
    | .empty => .empty
    | .leaf nd => .leaf { nd with parity := !nd.parity }
    | .node l r => .node (go l) r
  { c with graph := go c.graph }

/-- M1: Corrupted transition edge in WindowCert is rejected. -/
theorem neg_window_bad_edge0 :
    checkWindowCert dfao_carryXor3 8 (windowWeightInRange 2 6)
      (mutateRootWindowEdge0 cert_carryXor3_abelian_w8) = false := by decide

/-- M2: Corrupted initial state-window in WindowCert is rejected. -/
theorem neg_window_bad_init :
    checkWindowCert dfao_carryXor3 8 (windowWeightInRange 2 6)
      (mutateRootWindowInit cert_carryXor3_abelian_w8) = false := by decide

/-- M3: False tighter abelian claim [3, 5] on `carryXor 3` W=8 is rejected. -/
theorem neg_window_false_tighter_bound :
    checkWindowCert dfao_carryXor3 8 (windowWeightInRange 3 5)
      cert_carryXor3_abelian_w8 = false := by decide

/-- M4: Flipped bit in SyncCert parityMask is rejected. -/
theorem neg_sync_bad_mask :
    checkSyncCert dfao_carryXor3 (mutateSyncMask dfao_carryXor3 cert_carryXor3_k4.syncCert) = false := by decide

/-- M5: Corrupted node parity tag in SyncCert is rejected. -/
theorem neg_sync_bad_node_parity :
    checkSyncCert dfao_carryXor3 (mutateRootSyncParity cert_carryXor3_k4.syncCert) = false := by decide

/-- M6: Corrupted `invEven` decoder table in PowerAvoidCert is rejected. -/
theorem neg_power_bad_invEven :
    checkPowerAvoidCert dfao_carryXor3 4
      { cert_carryXor3_k4 with invEven := [1, 0] } = false := by decide

/-- M7: Truncated `baseCerts` in PowerAvoidCert is rejected. -/
theorem neg_power_missing_base :
    checkPowerAvoidCert dfao_carryXor3 4
      { cert_carryXor3_k4 with baseCerts := cert_carryXor3_k4.baseCerts.tail } = false := by decide

/-- M8: False stronger claim k = 3 (cube-free) on `carryXor 3` is rejected. -/
theorem neg_power_false_stronger_k3 :
    checkPowerAvoidCert dfao_carryXor3 3 cert_carryXor3_k4 = false := by decide

/-- M9: Corrupted `invPair` decoder in OverlapAvoidCert is rejected. -/
theorem neg_overlap_bad_invPair :
    checkOverlapAvoidCert dfao_grayMod4
      { cert_grayMod4_overlap with invPair := [1, 1, 1, 1] } = false := by decide

/-- M10: Corrupted `invOddPar1` decoder in OverlapAvoidCert is rejected. -/
theorem neg_overlap_bad_invOddPar1 :
    checkOverlapAvoidCert dfao_grayMod4
      { cert_grayMod4_overlap with invOddPar1 := [0, 0, 0, 0] } = false := by decide

/-- M11: Corrupted Carry-Offset Model table is rejected by `checkCarryXorModel`. -/
theorem neg_model_bad_vecTable :
    checkCarryXorModel 3 dfao_carryXor3 ([] :: vecTable_carryXor3.tail) = false := by decide

end SiliconAvoidance

-- ============================================================================
-- Section 13: Exhaustive Axiom Audit (must be subset of standard Lean axioms)
-- ============================================================================


