/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrayCarryMonodromyFreezing.Defs

/-!
# Theorems (`GrayCarryMonodromyFreezing`)

Dual Gray-Carry Infinite Lifting Mechanisms in Standalone Lean 4.36.0
  =====================================================================
  Worker: dynsil-5 (Thread 2: Bitwise Dynamics, T-Functions & Reversible Silicon Orbit Mechanisms)

  Two reusable pure-silicon infinite proof mechanisms for Gray-code + modular-increment
  hybrid dynamical systems (zero Mathlib, zero sorry, zero custom axioms):

  PART I  (BDFTR — Bidirectional Delay-Feedback Transducer Reduction):
    Compiles width-w bidirectional fixed-point / twisted equations `x >>> k = Φ_w(x)`
    into unidirectional LSB-to-MSB delay-feedback shift registers with an MSB zero-flush
    boundary condition, then lifts autonomous tail-absorption / sink-trapping laws to ∀ w.
    Proves:
      1. Universal 2^k twisted solution law for ((x ^^^ (x >>> k)) + c) % 2^w = x ^^^ m
         valid ∀ k ≥ 1, ∀ c, m < 2^L, ∀ w ≥ L + 2*k + 1 (plus exact N-stabilization).
      2. Bit-exact sharpness of w ≥ L + 2*k + 1 for EVERY k ≥ 1 (c = 2^(k+1) - 1 fails at 3*k+1).
      3. Sign-asymmetry complete annihilation: for d = 2^(2*k+1) - 2^k, the carry-driven dual
         (x ^^^ (x >>> k)) = (x + d) % 2^w has ZERO solutions ∀ k ≥ 1, ∀ w ≥ 2*k + 1.
      4. Sign-asymmetry single-trap law: for d = 1, (x ^^^ (x >>> k)) = (x + 1) % 2^w
         has EXACTLY 2^k - 1 solutions ∀ k ≥ 1, ∀ w ≥ 2*k.

  PART II (CPMF — Carry-Parity Monodromy Freezing Engine):
    For left-shift Gray-increment maps `L_{k,c}(x) = ((x ^^^ (x <<< k)) + c) % 2^w`,
    proves the universal pair-carry doubling conservation law (independent of bit `w` of `c`!)
    and compiles finite base-width monodromy+carry-parity certificates into exact infinite
    cycle decompositions valid ∀ w ≥ w0 and ∀ c ≡ c0 (mod 2^w0).
    Proves:
      1. Exact 5-cycle freezing ∀ c ≡ 9 (mod 32), ∀ w ≥ 5: lengths {2^(w-1): 1, 2^(w-3): 4}.
      2. Exact 7-cycle freezing ∀ c ≡ 19 (mod 64), ∀ w ≥ 6: lengths {2^(w-2): 3, 2^(w-4): 4}.
      3. Universal single-cycle law ∀ k ≥ 2, ∀ odd c, ∀ w ≥ 1: single full cycle of length 2^w.
      4. Sharpness counterexamples: k=1 (breaks single-cycle at w=2), even c (breaks at w=1),
         and c = 25 ≡ 9 (mod 16) (breaks 5-cycle freezing at w=6).
-/


namespace DualGrayCarry

/-! ## Section 0: Core Pure-Silicon Bitwise & Exact-Counting Primitives -/

/-- Majority of three booleans (full-adder carry bit). -/
def maj (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

theorem maj_xor_eq_borrow (x c b : Bool) :
    maj (xor x (xor c b)) c b = borrowBit x c b := by
  cases x <;> cases c <;> cases b <;> rfl

/-- Carry-in into bit `i` when computing `a + b + cin.toNat`. -/
def carryAt (a b : Nat) (cin : Bool) : Nat → Bool
  | 0 => cin
  | i + 1 => maj (a.testBit i) (b.testBit i) (carryAt a b cin i)

theorem carryAt_div2 (a b : Nat) (cin : Bool) :
    ∀ i, carryAt (a / 2) (b / 2) (maj (a.testBit 0) (b.testBit 0) cin) i =
         carryAt a b cin (i + 1)
  | 0 => rfl
  | i + 1 => by
    simp only [carryAt, carryAt_div2 a b cin i, Nat.testBit_div_two]

theorem testBit_add_carry (a b : Nat) (cin : Bool) :
    ∀ i, (a + b + cin.toNat).testBit i =
         xor (a.testBit i) (xor (b.testBit i) (carryAt a b cin i)) := by
  intro i
  induction i generalizing a b cin with
  | zero =>
    simp only [carryAt, Nat.testBit_zero]
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    cases cin <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [Bool.toNat, ha, hb] <;> omega
  | succ i ih =>
    rw [Nat.testBit_succ]
    have hdiv : (a + b + cin.toNat) / 2 =
        a / 2 + b / 2 + (maj (a.testBit 0) (b.testBit 0) cin).toNat := by
      simp only [Nat.testBit_zero, maj]
      have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
      cases cin <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp [Bool.toNat, ha, hb] <;> omega
    rw [hdiv, ih (a / 2) (b / 2) (maj (a.testBit 0) (b.testBit 0) cin)]
    rw [Nat.testBit_div_two, Nat.testBit_div_two, carryAt_div2]

theorem testBit_add (a b i : Nat) :
    (a + b).testBit i = xor (a.testBit i) (xor (b.testBit i) (carryAt a b false i)) := by
  have h := testBit_add_carry a b false i
  simpa [Bool.toNat] using h

theorem testBit_lt_of_le {x w i : Nat} (hx : x < 2 ^ w) (hwi : w ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hwi))

theorem carryAt_two_pow_of_lt {a w : Nat} (ha : a < 2 ^ w) :
    ∀ i, carryAt a (2 ^ w) false i = false
  | 0 => rfl
  | i + 1 => by
    simp only [carryAt, carryAt_two_pow_of_lt ha i, Nat.testBit_two_pow]
    by_cases hi : w = i
    · subst hi
      have h0 : a.testBit w = false := Nat.testBit_lt_two_pow ha
      simp [h0, maj]
    · simp [hi, maj]

theorem testBit_add_two_pow_of_lt {a w i : Nat} (ha : a < 2 ^ w) :
    (a + 2 ^ w).testBit i = if i = w then true else a.testBit i := by
  rw [testBit_add, carryAt_two_pow_of_lt ha i, Nat.testBit_two_pow]
  by_cases hi : i = w
  · subst hi
    have h0 : a.testBit i = false := Nat.testBit_lt_two_pow ha
    simp [h0]
  · have hne : w ≠ i := Ne.symm hi
    simp [hi, hne]

theorem evalBits_lt (f : Nat → Bool) : ∀ w, evalBits f w < 2 ^ w
  | 0 => by simp [evalBits]
  | w + 1 => by
    have ih := evalBits_lt f w
    simp only [evalBits, Nat.pow_succ]
    cases f w <;> simp <;> omega

theorem testBit_evalBits (f : Nat → Bool) :
    ∀ w i, (evalBits f w).testBit i = (decide (i < w) && f i)
  | 0, i => by simp [evalBits]
  | w + 1, i => by
    simp only [evalBits]
    cases hfw : f w
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [testBit_evalBits f w i]
      by_cases hi : i = w
      · subst hi; simp [hfw]
      · by_cases hlt : i < w
        · have hlt' : i < w + 1 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ (i < w + 1) := by omega
          simp [hlt, hlt']
    · simp only [↓reduceIte]
      rw [testBit_add_two_pow_of_lt (evalBits_lt f w), testBit_evalBits f w i]
      by_cases hi : i = w
      · subst hi; simp [hfw]
      · simp only [hi, ↓reduceIte]
        by_cases hlt : i < w
        · have hlt' : i < w + 1 := by omega
          simp [hlt, hlt']
        · have hlt' : ¬ (i < w + 1) := by omega
          simp [hlt, hlt']

theorem evalBits_eq_of_testBit {f : Nat → Bool} {x w : Nat}
    (hx : x < 2 ^ w) (h : ∀ i < w, x.testBit i = f i) :
    x = evalBits f w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_evalBits]
  by_cases hi : i < w
  · simp [hi, h i hi]
  · have h0 : x.testBit i = false := testBit_lt_of_le hx (by omega)
    simp [hi, h0]

theorem iterFn_add {α : Type} (f : α → α) (x : α) :
    ∀ a b, iterFn f b (iterFn f a x) = iterFn f (a + b) x
  | _, 0 => rfl
  | a, b + 1 => by
    show f (iterFn f b (iterFn f a x)) = f (iterFn f (a + b) x)
    rw [iterFn_add f x a b]

theorem countBelow_eq_length_filter (P : Nat → Bool) :
    ∀ n, countBelow P n = ((List.range n).filter P).length
  | 0 => rfl
  | n + 1 => by
    rw [countBelow, List.range_succ, List.filter_append, List.length_append,
        countBelow_eq_length_filter P n]
    simp only [List.filter]
    cases P n <;> simp

theorem countBelow_true : ∀ n, countBelow (fun _ => true) n = n
  | 0 => rfl
  | n + 1 => by simp [countBelow, countBelow_true n]

theorem countBelow_false : ∀ n, countBelow (fun _ => false) n = 0
  | 0 => rfl
  | n + 1 => by simp [countBelow, countBelow_false n]

theorem countBelow_congr {P Q : Nat → Bool} {n : Nat} (h : ∀ x < n, P x = Q x) :
    countBelow P n = countBelow Q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countBelow]
    rw [ih (fun x hx => h x (by omega)), h n (by omega)]

theorem countBelow_lt_of_false {P : Nat → Bool} {n a : Nat}
    (ha : a < n) (hP : P a = false) :
    countBelow P n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [countBelow]
    by_cases h : a = n
    · subst h
      rw [hP]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hle : countBelow P a ≤ a := by
        rw [countBelow_eq_length_filter]
        have := List.length_filter_le P (List.range a)
        simpa using this
      omega
    · have hlt := ih (by omega)
      cases P n <;> simp <;> omega

theorem countBelow_lt_pred {n : Nat} (hn : 0 < n) :
    countBelow (fun r => decide (r < n - 1)) n = n - 1 := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel, countBelow, Nat.lt_irrefl, decide_false,
               Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [countBelow_congr (Q := fun _ => true) (fun x hx => by simp [hx])]
    exact countBelow_true m

theorem nodup_filter (P : Nat → Bool) : ∀ (l : List Nat), l.Nodup → (l.filter P).Nodup
  | [], _ => List.nodup_nil
  | a :: xs, h => by
    have ⟨ha, hxs⟩ := List.nodup_cons.1 h
    simp only [List.filter_cons]
    cases P a with
    | false => exact nodup_filter P xs hxs
    | true =>
      refine List.nodup_cons.2 ⟨?_, nodup_filter P xs hxs⟩
      intro hmem
      exact ha (List.mem_filter.1 hmem).1

theorem nodup_map_of_inj_on (φ : Nat → Nat) :
    ∀ (l : List Nat), l.Nodup → (∀ x ∈ l, ∀ y ∈ l, φ x = φ y → x = y) → (l.map φ).Nodup
  | [], _, _ => List.nodup_nil
  | a :: xs, hnd, hinj => by
    have ⟨ha, hxs⟩ := List.nodup_cons.1 hnd
    simp only [List.map_cons]
    refine List.nodup_cons.2 ⟨?_, nodup_map_of_inj_on φ xs hxs
      (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))⟩
    intro hmem
    rcases List.mem_map.1 hmem with ⟨b, hb, hba⟩
    have heq := hinj b (by simp [hb]) a (by simp) hba
    subst heq
    exact ha hb

/-- Exact length equality for duplicate-free lists with identical membership. -/
theorem nodup_length_eq_of_mem_iff :
    ∀ (l₁ l₂ : List Nat), l₁.Nodup → l₂.Nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) →
      l₁.length = l₂.length
  | [], l₂, _, _, hmem => by
    cases l₂ with
    | nil => rfl
    | cons y ys =>
      have : y ∈ ([] : List Nat) := (hmem y).2 (by simp)
      simp at this
  | a :: xs, l₂, hnd₁, hnd₂, hmem => by
    have ha_in : a ∈ l₂ := (hmem a).1 (by simp)
    have ha_not : a ∉ xs := (List.nodup_cons.1 hnd₁).1
    have hxs_nd : xs.Nodup := (List.nodup_cons.1 hnd₁).2
    have hl₂'_nd : (l₂.erase a).Nodup := List.Nodup.erase a hnd₂
    have hmem' : ∀ x, x ∈ xs ↔ x ∈ l₂.erase a := by
      intro x
      constructor
      · intro hx
        have hne : x ≠ a := fun heq => ha_not (heq ▸ hx)
        have hxl₂ : x ∈ l₂ := (hmem x).1 (by simp [hx])
        exact (List.mem_erase_of_ne hne).2 hxl₂
      · intro hx
        have hne : x ≠ a := by
          intro heq
          subst heq
          exact (List.Nodup.not_mem_erase hnd₂) hx
        have hxl₂ : x ∈ l₂ := List.mem_of_mem_erase hx
        have hxa : x ∈ a :: xs := (hmem x).2 hxl₂
        rcases List.mem_cons.1 hxa with rfl | hxs
        · exact absurd rfl hne
        · exact hxs
    have ih := nodup_length_eq_of_mem_iff xs (l₂.erase a) hxs_nd hl₂'_nd hmem'
    have hlen : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha_in
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha_in
    simp only [List.length_cons]
    omega

/-- Exact cardinality equality from a bijection between filtered ranges. -/
theorem countBelow_eq_of_bij {P Q : Nat → Bool} {N M : Nat}
    (φ ψ : Nat → Nat)
    (hφ : ∀ r < M, Q r = true → φ r < N ∧ P (φ r) = true ∧ ψ (φ r) = r)
    (hψ : ∀ x < N, P x = true → ψ x < M ∧ Q (ψ x) = true ∧ φ (ψ x) = x) :
    countBelow P N = countBelow Q M := by
  rw [countBelow_eq_length_filter, countBelow_eq_length_filter]
  let lQ := (List.range M).filter Q
  let lP := (List.range N).filter P
  have hlQ_nd : lQ.Nodup := nodup_filter Q (List.range M) List.nodup_range
  have hlP_nd : lP.Nodup := nodup_filter P (List.range N) List.nodup_range
  have hmap_nd : (lQ.map φ).Nodup := by
    apply nodup_map_of_inj_on φ lQ hlQ_nd
    intro r₁ hr₁ r₂ hr₂ heq
    have hr₁' : r₁ < M ∧ Q r₁ = true := by simpa [lQ] using hr₁
    have hr₂' : r₂ < M ∧ Q r₂ = true := by simpa [lQ] using hr₂
    have h1 := (hφ r₁ hr₁'.1 hr₁'.2).2.2
    have h2 := (hφ r₂ hr₂'.1 hr₂'.2).2.2
    rw [← h1, ← h2, heq]
  have hmem : ∀ x, x ∈ lP ↔ x ∈ lQ.map φ := by
    intro x
    constructor
    · intro hx
      have hx' : x < N ∧ P x = true := by simpa [lP] using hx
      have h1 := hψ x hx'.1 hx'.2
      refine List.mem_map.2 ⟨ψ x, ?_, h1.2.2⟩
      simp [lQ, h1.1, h1.2.1]
    · intro hx
      rcases List.mem_map.1 hx with ⟨r, hr, rfl⟩
      have hr' : r < M ∧ Q r = true := by simpa [lQ] using hr
      have h1 := hφ r hr'.1 hr'.2
      simp [lP, h1.1, h1.2.1]
  have hlen := nodup_length_eq_of_mem_iff lP (lQ.map φ) hlP_nd hmap_nd hmem
  simpa [List.length_map] using hlen


/-- Transducer state `q_i` along the DFSR run from seed `r`. -/
def dfsrQ {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (r i : Nat) : Q :=
  (dfsrRun M k hk aux r i).q

theorem dfsr_buf_shift {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (r : Nat) :
    ∀ (m : Nat) (i : Nat) (hm : m < k),
      (dfsrRun M k hk aux r i).buf ⟨m, hm⟩ = dfsrBit M k hk aux r (i + m)
  | 0, i, _ => by simp [dfsrBit]
  | m + 1, i, hm => by
    have hstep : (dfsrRun M k hk aux r (i + 1)).buf ⟨m, by omega⟩ =
                 (dfsrRun M k hk aux r i).buf ⟨m + 1, hm⟩ := by
      simp [dfsrRun, dfsrStep, hm]
    rw [← hstep, dfsr_buf_shift M k hk aux r m (i + 1) (by omega)]
    have : i + 1 + m = i + (m + 1) := by omega
    rw [this]

theorem dfsrBit_seed {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (r j : Nat) (hj : j < k) :
    dfsrBit M k hk aux r j = r.testBit j := by
  have h := dfsr_buf_shift M k hk aux r j 0 hj
  simpa [dfsrRun, dfsrInit] using h.symm

theorem dfsrQ_succ {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (r i : Nat) :
    dfsrQ M k hk aux r (i + 1) =
      M.nextState (dfsrQ M k hk aux r i) (dfsrBit M k hk aux r i) (aux i) := rfl

theorem dfsrBit_add_k {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (r i : Nat) :
    dfsrBit M k hk aux r (i + k) =
      M.outBit (dfsrQ M k hk aux r i) (dfsrBit M k hk aux r i) (aux i) := by
  have h1 : (dfsrRun M k hk aux r (i + 1)).buf ⟨k - 1, by omega⟩ =
            dfsrBit M k hk aux r (i + 1 + (k - 1)) :=
    dfsr_buf_shift M k hk aux r (k - 1) (i + 1) (by omega)
  have hidx : i + 1 + (k - 1) = i + k := by omega
  rw [hidx] at h1
  rw [← h1]
  simp only [dfsrRun, dfsrStep]
  have hnot : ¬ (k - 1 + 1 < k) := by omega
  simp [hnot, dfsrQ, dfsrBit]

theorem dfsrFlush_iff {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (w r : Nat) :
    dfsrFlush M k hk aux w r = true ↔ ∀ j < k, dfsrBit M k hk aux r (w + j) = false := by
  simp only [dfsrFlush, decide_eq_true_eq]
  constructor
  · intro h j hj
    rw [← dfsr_buf_shift M k hk aux r j w hj]
    exact h ⟨j, hj⟩
  · intro h ⟨j, hj⟩
    rw [dfsr_buf_shift M k hk aux r j w hj]
    exact h j hj

/-- **BDFTR Soundness & Exact Bijection Theorem**:
    For ANY finite-state transducer `M`, shift `k ≥ 1`, auxiliary stream `aux`, and width `w ≥ k`,
    the bidirectional fixed-point solutions `x < 2^w` of `x >>> k = transducerEval M aux x w`
    are in exact bijection with the MSB-zero-flushed seeds `r < 2^k`. -/
theorem bdftr_exact_count {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (w : Nat) (hw : k ≤ w) :
    countBelow (fun x => decide (x >>> k = transducerEval M aux x w)) (2 ^ w) =
    countBelow (dfsrFlush M k hk aux w) (2 ^ k) := by
  let φ : Nat → Nat := fun r => evalBits (dfsrBit M k hk aux r) w
  let ψ : Nat → Nat := fun x => x % 2 ^ k
  apply countBelow_eq_of_bij φ ψ
  · -- Forward map: zero-flushed seed `r < 2^k` → solution `φ r < 2^w`
    intro r hr hflush
    have hfl := (dfsrFlush_iff M k hk aux w r).1 hflush
    have hφlt : φ r < 2 ^ w := evalBits_lt _ w
    have hstate : ∀ i ≤ w, runState M aux (φ r) i = dfsrQ M k hk aux r i := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        simp only [runState, dfsrQ_succ]
        rw [ih (by omega)]
        have hbi : (φ r).testBit i = dfsrBit M k hk aux r i := by
          simp only [φ, testBit_evalBits, show i < w by omega, decide_true, Bool.true_and]
        rw [hbi]
    have hsol : (φ r) >>> k = transducerEval M aux (φ r) w := by
      apply Nat.eq_of_testBit_eq
      intro i
      have hrhs := testBit_evalBits (transducerOut M aux (φ r)) w i
      rw [Nat.testBit_shiftRight, transducerEval, hrhs]
      by_cases hi : i < w
      · simp only [hi, decide_true, Bool.true_and, transducerOut]
        rw [hstate i (by omega)]
        have hbi : (φ r).testBit i = dfsrBit M k hk aux r i := by
          simp only [φ, testBit_evalBits, hi, decide_true, Bool.true_and]
        rw [hbi, ← dfsrBit_add_k M k hk aux r i]
        have hcomm : k + i = i + k := Nat.add_comm k i
        rw [hcomm, show (φ r).testBit (i + k) = (decide (i + k < w) && dfsrBit M k hk aux r (i + k)) from
          testBit_evalBits _ w (i + k)]
        by_cases hik : i + k < w
        · simp [hik]
        · simp only [hik, decide_false, Bool.false_and]
          have hj : i + k - w < k := by omega
          have heq : w + (i + k - w) = i + k := by omega
          have h0 := hfl (i + k - w) hj
          rw [heq] at h0
          exact h0.symm
      · simp only [hi, decide_false, Bool.false_and]
        rw [show (φ r).testBit (k + i) = (decide (k + i < w) && dfsrBit M k hk aux r (k + i)) from
          testBit_evalBits _ w (k + i)]
        have hki : ¬ (k + i < w) := by omega
        simp [hki]
    have hinv : ψ (φ r) = r := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [ψ, Nat.testBit_mod_two_pow]
      by_cases hi : i < k
      · simp only [hi, decide_true, Bool.true_and, φ, testBit_evalBits]
        have hiw : i < w := by omega
        simp [hiw, dfsrBit_seed M k hk aux r i hi]
      · simp only [hi, decide_false, Bool.false_and]
        exact (testBit_lt_of_le hr (by omega)).symm
    exact ⟨hφlt, decide_eq_true hsol, hinv⟩
  · -- Backward map: solution `x < 2^w` → zero-flushed seed `ψ x < 2^k`
    intro x hx hsol_dec
    have hsol : x >>> k = transducerEval M aux x w := of_decide_eq_true hsol_dec
    have hrlt : ψ x < 2 ^ k := Nat.mod_lt x (Nat.two_pow_pos k)
    have hmatch : ∀ i, i < w + k → x.testBit i = dfsrBit M k hk aux (ψ x) i := by
      intro i
      induction i using Nat.strongRecOn with
      | ind i ih =>
        intro hi
        by_cases hik : i < k
        · rw [dfsrBit_seed M k hk aux (ψ x) i hik]
          simp [ψ, Nat.testBit_mod_two_pow, hik]
        · have hj : i - k < w := by omega
          have hkj : k + (i - k) = i := by omega
          have hjk : i - k + k = i := by omega
          have hq : ∀ t ≤ i - k, runState M aux x t = dfsrQ M k hk aux (ψ x) t := by
            intro t ht
            induction t with
            | zero => rfl
            | succ t iht =>
              simp only [runState, dfsrQ_succ]
              rw [iht (by omega), ih t (by omega) (by omega)]
          have hbit_eq : (x >>> k).testBit (i - k) = (transducerEval M aux x w).testBit (i - k) :=
            congrArg (fun n => n.testBit (i - k)) hsol
          rw [Nat.testBit_shiftRight, hkj, transducerEval, testBit_evalBits] at hbit_eq
          simp only [hj, decide_true, Bool.true_and, transducerOut] at hbit_eq
          rw [hbit_eq, hq (i - k) (Nat.le_refl _), ih (i - k) (by omega) (by omega)]
          rw [← dfsrBit_add_k M k hk aux (ψ x) (i - k), hjk]
    have hfl : dfsrFlush M k hk aux w (ψ x) = true := by
      rw [dfsrFlush_iff]
      intro j hj
      rw [← hmatch (w + j) (by omega)]
      exact testBit_lt_of_le hx (by omega)
    have hφψ : φ (ψ x) = x := by
      symm
      apply evalBits_eq_of_testBit hx
      intro i hi
      exact hmatch i (by omega)
    exact ⟨hrlt, hfl, hφψ⟩

/-- General Autonomous Absorption Engine:
    If `aux i = a₀` for `i ≥ L` and `s_sink` is a fixed point of autonomous `dfsrStep`
    reached from every state in `D` steps, then every run is at `s_sink` for all `w ≥ L + D`. -/
theorem dfsr_autonomous_absorption {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (a₀ : Aux) (L D : Nat) (s_sink : DFSRState Q k)
    (haux : ∀ i ≥ L, aux i = a₀)
    (hsink : dfsrStep M k hk a₀ s_sink = s_sink)
    (habsorb : ∀ s : DFSRState Q k, iterFn (dfsrStep M k hk a₀) D s = s_sink) :
    ∀ r w, L + D ≤ w → dfsrRun M k hk aux r w = s_sink := by
  have haut : ∀ r n,
      dfsrRun M k hk aux r (L + n) = iterFn (dfsrStep M k hk a₀) n (dfsrRun M k hk aux r L) := by
    intro r n
    induction n with
    | zero => rfl
    | succ n ih =>
      show dfsrStep M k hk (aux (L + n)) (dfsrRun M k hk aux r (L + n)) =
           dfsrStep M k hk a₀ (iterFn (dfsrStep M k hk a₀) n (dfsrRun M k hk aux r L))
      rw [haux (L + n) (by omega), ih]
  intro r w hw
  have h1 : dfsrRun M k hk aux r (L + D) = s_sink := by
    rw [haut r D, habsorb]
  have hstay : ∀ m, dfsrRun M k hk aux r (L + D + m) = s_sink := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih =>
      show dfsrStep M k hk (aux (L + D + m)) (dfsrRun M k hk aux r (L + D + m)) = s_sink
      rw [haux (L + D + m) (by omega), ih, hsink]
  have hw_eq : L + D + (w - (L + D)) = w := by omega
  rw [← hw_eq]
  exact hstay (w - (L + D))

/-- General Trapped-Sink Lemma:
    If `s_trap` is a fixed point of autonomous `dfsrStep` (for `i ≥ L`) with `s_trap.buf ⟨0, hk⟩ = true`,
    and seed `r` reaches `s_trap` at step `s ≥ L`, then `dfsrFlush` is `false` for ALL `w ≥ s`. -/
theorem dfsr_trapped_no_flush {Q Aux : Type} (M : BitTransducer Q Aux) (k : Nat) (hk : 0 < k)
    (aux : Nat → Aux) (a₀ : Aux) (L s : Nat) (s_trap : DFSRState Q k) (r : Nat)
    (hL : L ≤ s)
    (haux : ∀ i ≥ L, aux i = a₀)
    (htrap : dfsrStep M k hk a₀ s_trap = s_trap)
    (hnonzero : s_trap.buf ⟨0, hk⟩ = true)
    (hreach : dfsrRun M k hk aux r s = s_trap) :
    ∀ w ≥ s, dfsrFlush M k hk aux w r = false := by
  have hstay : ∀ m, dfsrRun M k hk aux r (s + m) = s_trap := by
    intro m
    induction m with
    | zero => exact hreach
    | succ m ih =>
      show dfsrStep M k hk (aux (s + m)) (dfsrRun M k hk aux r (s + m)) = s_trap
      rw [haux (s + m) (by omega), ih, htrap]
  intro w hw
  have hrun : dfsrRun M k hk aux r w = s_trap := by
    have : s + (w - s) = w := by omega
    rw [← this]; exact hstay (w - s)
  cases hfl : dfsrFlush M k hk aux w r with
  | false => rfl
  | true =>
    have h0 := ((dfsrFlush_iff M k hk aux w r).1 hfl) 0 hk
    simp only [Nat.add_zero, dfsrBit, hrun, hnonzero] at h0
    contradiction


theorem borrowTransducer_nextState (b xi : Bool) (a : Bool × Bool) :
    borrowTransducer.nextState b xi a = borrowBit (xor xi a.2) a.1 b := rfl

theorem borrowTransducer_outBit (b xi : Bool) (a : Bool × Bool) :
    borrowTransducer.outBit b xi a = xor a.1 (xor a.2 b) := rfl

/-- Equivalence between the bidirectional modular equation and `borrowTransducer`. -/
theorem borrowTransducer_equiv (k c m w x : Nat) (hx : x < 2 ^ w) (hm : m < 2 ^ w) :
    ((x ^^^ (x >>> k)) + c) % 2 ^ w = x ^^^ m ↔
    x >>> k = transducerEval borrowTransducer (fun i => (c.testBit i, m.testBit i)) x w := by
  let y := x ^^^ (x >>> k)
  let aux : Nat → Bool × Bool := fun i => (c.testBit i, m.testBit i)
  have hy_bit : ∀ i, y.testBit i = xor (x.testBit i) ((x >>> k).testBit i) := by
    intro i; simp [y, Nat.testBit_xor]
  constructor
  · intro heq
    have hcarry : ∀ i ≤ w, carryAt y c false i = runState borrowTransducer aux x i := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        have hbit : (((y + c) % 2 ^ w).testBit i) = (x ^^^ m).testBit i :=
          congrArg (fun n => n.testBit i) heq
        have hiw : i < w := by omega
        rw [Nat.testBit_mod_two_pow, testBit_add, Nat.testBit_xor] at hbit
        simp only [hiw, decide_true, Bool.true_and] at hbit
        have hyi : y.testBit i =
            xor (xor (x.testBit i) (m.testBit i)) (xor (c.testBit i) (carryAt y c false i)) := by
          cases h1 : y.testBit i <;> cases h2 : c.testBit i <;>
          cases h3 : carryAt y c false i <;> cases h4 : x.testBit i <;>
          cases h5 : m.testBit i <;> simp_all
        simp only [carryAt, runState, borrowTransducer_nextState]
        rw [← ih (by omega), hyi, maj_xor_eq_borrow]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [transducerEval, testBit_evalBits]
    by_cases hi : i < w
    · simp only [hi, decide_true, Bool.true_and, transducerOut, borrowTransducer_outBit]
      change (x >>> k).testBit i = xor (c.testBit i) (xor (m.testBit i) (runState borrowTransducer aux x i))
      rw [← hcarry i (by omega)]
      have hbit : (((y + c) % 2 ^ w).testBit i) = (x ^^^ m).testBit i :=
        congrArg (fun n => n.testBit i) heq
      rw [Nat.testBit_mod_two_pow, testBit_add, hy_bit, Nat.testBit_xor] at hbit
      simp only [hi, decide_true, Bool.true_and] at hbit
      cases h1 : x.testBit i <;> cases h2 : (x >>> k).testBit i <;>
      cases h3 : c.testBit i <;> cases h4 : carryAt y c false i <;>
      cases h5 : m.testBit i <;> simp_all
    · simp only [hi, decide_false, Bool.false_and]
      rw [Nat.testBit_shiftRight]
      exact testBit_lt_of_le hx (by omega)
  · intro heq
    have hcarry : ∀ i ≤ w, carryAt y c false i = runState borrowTransducer aux x i := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        have hiw : i < w := by omega
        have hxk : (x >>> k).testBit i =
            xor (c.testBit i) (xor (m.testBit i) (runState borrowTransducer aux x i)) := by
          have h := congrArg (fun n => n.testBit i) heq
          rw [transducerEval, testBit_evalBits] at h
          simpa only [hiw, decide_true, Bool.true_and, transducerOut, borrowTransducer_outBit] using h
        have hyi : y.testBit i =
            xor (xor (x.testBit i) (m.testBit i)) (xor (c.testBit i) (carryAt y c false i)) := by
          rw [hy_bit, hxk, ← ih (by omega)]
          cases x.testBit i <;> cases c.testBit i <;> cases m.testBit i <;>
          cases carryAt y c false i <;> rfl
        simp only [carryAt, runState, borrowTransducer_nextState]
        rw [← ih (by omega), hyi, maj_xor_eq_borrow]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hi : i < w
    · simp only [hi, decide_true, Bool.true_and, testBit_add]
      change xor (y.testBit i) (xor (c.testBit i) (carryAt y c false i)) = xor (x.testBit i) (m.testBit i)
      rw [hy_bit]
      have hxk : (x >>> k).testBit i =
          xor (c.testBit i) (xor (m.testBit i) (carryAt y c false i)) := by
        have h := congrArg (fun n => n.testBit i) heq
        rw [transducerEval, testBit_evalBits] at h
        have h' : (x >>> k).testBit i = xor (c.testBit i) (xor (m.testBit i) (runState borrowTransducer aux x i)) := by
          simpa only [hi, decide_true, Bool.true_and, transducerOut, borrowTransducer_outBit] using h
        rw [h', ← hcarry i (by omega)]
      rw [hxk]
      cases x.testBit i <;> cases c.testBit i <;> cases m.testBit i <;>
      cases carryAt y c false i <;> rfl
    · simp only [hi, decide_false, Bool.false_and]
      have hx0 : x.testBit i = false := testBit_lt_of_le hx (by omega)
      have hm0 : m.testBit i = false := testBit_lt_of_le hm (by omega)
      simp [hx0, hm0]

/-- Autonomous borrow step `a₀ = (false, false)` absorbs EVERY `(k+1)`-bit state
    into `⟨false, fun _ => false⟩` in at most `2*k + 1` steps! -/
theorem borrow_universal_absorption (k : Nat) (hk : 0 < k) :
    ∀ s : DFSRState Bool k,
      iterFn (dfsrStep borrowTransducer k hk (false, false)) (2 * k + 1) s =
      ⟨false, fun _ => false⟩ := by
  let step : DFSRState Bool k → DFSRState Bool k := dfsrStep borrowTransducer k hk (false, false)
  let iterS : DFSRState Bool k → Nat → DFSRState Bool k := fun s n => iterFn step n s
  have hcomp : ∀ (s : DFSRState Bool k) (a b : Nat), iterS (iterS s a) b = iterS s (a + b) :=
    fun s a b => iterFn_add step s a b
  have hq_stay : ∀ (s : DFSRState Bool k) (n : Nat), s.q = false → (iterS s n).q = false := by
    intro s n hq
    induction n with
    | zero => exact hq
    | succ n ih =>
      show borrowBit (xor ((iterS s n).buf ⟨0, hk⟩) false) false (iterS s n).q = false
      rw [ih]; simp [borrowBit]
  have hflush_after_k : ∀ (s : DFSRState Bool k), s.q = false →
      iterS s k = ⟨false, fun _ => false⟩ := by
    intro s hq
    have hbuf : ∀ (t : Nat) (j : Fin k), k ≤ t + j.val → (iterS s t).buf j = false := by
      intro t
      induction t with
      | zero => intro j hj; exact absurd hj (by omega)
      | succ t ih =>
        intro j hj
        show (if h : j.val + 1 < k then (iterS s t).buf ⟨j.val + 1, h⟩
              else xor false (xor false (iterS s t).q)) = false
        by_cases h : j.val + 1 < k
        · simp only [h, ↓reduceDIte]
          exact ih ⟨j.val + 1, h⟩ (by simp; omega)
        · simp only [h, ↓reduceDIte]
          rw [hq_stay s t hq]; rfl
    have hq_k := hq_stay s k hq
    cases hst : iterS s k with
    | mk q b =>
      have hq' : q = false := by rw [hst] at hq_k; exact hq_k
      subst hq'
      congr
      funext j
      have hb := hbuf k j (by omega)
      rw [hst] at hb
      exact hb
  have hkill : ∀ s : DFSRState Bool k, (iterS s (k + 1)).q = false := by
    intro s
    by_cases h : (iterS s k).q = false
    · exact hq_stay (iterS s k) 1 h
    · have hall_true : ∀ t ≤ k, (iterS s t).q = true := by
        intro t ht
        cases hqt : (iterS s t).q with
        | true => rfl
        | false =>
          have hstay_k : (iterS (iterS s t) (k - t)).q = false :=
            hq_stay (iterS s t) (k - t) hqt
          rw [hcomp s t (k - t), Nat.add_sub_of_le ht] at hstay_k
          exact absurd hstay_k h
      have htrack : ∀ t, (ht1 : 1 ≤ t) → (htk : t ≤ k) → (iterS s t).buf ⟨k - t, by omega⟩ = true := by
        intro t
        induction t with
        | zero => intro ht1 _; omega
        | succ t ih =>
          intro ht1 htk
          by_cases ht0 : t = 0
          · subst ht0
            show (if h : (k - 1) + 1 < k then s.buf ⟨(k - 1) + 1, h⟩
                  else xor false (xor false s.q)) = true
            have hnot : ¬ ((k - 1) + 1 < k) := by omega
            have hs0 : s.q = true := hall_true 0 (by omega)
            simp [hnot, hs0]
          · show (if h : (k - (t + 1)) + 1 < k then (iterS s t).buf ⟨(k - (t + 1)) + 1, h⟩
                  else xor false (xor false (iterS s t).q)) = true
            have hlt : (k - (t + 1)) + 1 < k := by omega
            simp only [hlt, ↓reduceDIte]
            have hidx : (⟨(k - (t + 1)) + 1, hlt⟩ : Fin k) = ⟨k - t, by omega⟩ := by
              apply Fin.ext; simp; omega
            rw [hidx]
            exact ih (by omega) (by omega)
      have hbuf0 : (iterS s k).buf ⟨0, hk⟩ = true := by
        have htr := htrack k (by omega) (Nat.le_refl k)
        have hidx : (⟨k - k, by omega⟩ : Fin k) = ⟨0, hk⟩ := by apply Fin.ext; simp
        rw [hidx] at htr
        exact htr
      show borrowBit (xor ((iterS s k).buf ⟨0, hk⟩) false) false (iterS s k).q = false
      rw [hbuf0]; cases (iterS s k).q <;> rfl
  intro s
  change iterS s (2 * k + 1) = ⟨false, fun _ => false⟩
  have h2k1 : k + 1 + k = 2 * k + 1 := by omega
  rw [← h2k1, ← hcomp s (k + 1) k]
  exact hflush_after_k (iterS s (k + 1)) (hkill s)

/-- **THEOREM I.1 (Universal $2^k$ Twisted Gray-Carry Law via BDFTR)**:
    For EVERY shift `k ≥ 1`, bit-length bound `L`, increment `c < 2^L`, XOR-twist `m < 2^L`,
    and word width `w ≥ L + 2*k + 1`, the bidirectional equation
      `((x ^^^ (x >>> k)) + c) % 2^w = x ^^^ m`
    has **EXACTLY `2^k` solutions** in `{0, ..., 2^w - 1}`. -/
theorem grayRight_twisted_exact_count (k L c m w : Nat) (hk : 0 < k)
    (hc : c < 2 ^ L) (hm : m < 2 ^ L) (hw : L + 2 * k + 1 ≤ w) :
    countBelow (fun x => decide (((x ^^^ (x >>> k)) + c) % 2 ^ w = x ^^^ m)) (2 ^ w) = 2 ^ k := by
  let aux : Nat → Bool × Bool := fun i => (c.testBit i, m.testBit i)
  have hmw : m < 2 ^ w := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
  rw [countBelow_congr (Q := fun x => decide (x >>> k = transducerEval borrowTransducer aux x w)) (fun x hx => by
    exact decide_eq_decide.2 (borrowTransducer_equiv k c m w x hx hmw))]
  rw [bdftr_exact_count borrowTransducer k hk aux w (by omega)]
  have haux : ∀ i ≥ L, aux i = (false, false) := by
    intro i hi
    simp only [aux, testBit_lt_of_le hc hi, testBit_lt_of_le hm hi]
  have hsink : dfsrStep borrowTransducer k hk (false, false) ⟨false, fun _ => false⟩ =
               ⟨false, fun _ => false⟩ := by
    simp [dfsrStep, borrowTransducer_nextState, borrowTransducer_outBit, borrowBit]
  have habs := dfsr_autonomous_absorption borrowTransducer k hk aux (false, false)
    L (2 * k + 1) ⟨false, fun _ => false⟩ haux hsink (borrow_universal_absorption k hk)
  rw [countBelow_congr (Q := fun _ => true) (fun r _ => by
    simp [dfsrFlush, habs r w hw])]
  exact countBelow_true (2 ^ k)

/-- **Corollary I.1a (Universal $2^k$ Fixed-Point Law for Right-Shift Gray + Increment)**:
    For ALL `k ≥ 1`, `c < 2^L`, `w ≥ L + 2*k + 1`, the bijection `T_{k,c}(x) = ((x ^^^ (x >>> k)) + c) % 2^w`
    has **EXACTLY `2^k` fixed points**. -/
theorem grayRight_fixedPoint_exact_count (k L c w : Nat) (hk : 0 < k)
    (hc : c < 2 ^ L) (hw : L + 2 * k + 1 ≤ w) :
    countBelow (fun x => decide (((x ^^^ (x >>> k)) + c) % 2 ^ w = x)) (2 ^ w) = 2 ^ k := by
  have h := grayRight_twisted_exact_count k L c 0 w hk hc (Nat.two_pow_pos L) hw
  simpa using h

/-- **Corollary I.1b (Untruncated $\mathbb{N}$-Stabilization)**:
    Every seed `r < 2^k` generates a finite natural number `z < 2^(L + 2*k + 1)`
    satisfying the UNTRUNCATED equation `(z ^^^ (z >>> k)) + c = z ^^^ m` in `ℕ`! -/
theorem grayRight_nat_stabilization (k L c m r : Nat) (hk : 0 < k)
    (hc : c < 2 ^ L) (hm : m < 2 ^ L) :
    let w0 := L + 2 * k + 1
    let z := evalBits (dfsrBit borrowTransducer k hk (fun i => (c.testBit i, m.testBit i)) r) w0
    z < 2 ^ w0 ∧ (z ^^^ (z >>> k)) + c = z ^^^ m := by
  intro w0 z
  have hzlt : z < 2 ^ w0 := evalBits_lt _ w0
  let aux : Nat → Bool × Bool := fun i => (c.testBit i, m.testBit i)
  have haux : ∀ i ≥ L, aux i = (false, false) := by
    intro i hi
    simp only [aux, testBit_lt_of_le hc hi, testBit_lt_of_le hm hi]
  have hsink : dfsrStep borrowTransducer k hk (false, false) ⟨false, fun _ => false⟩ =
               ⟨false, fun _ => false⟩ := by
    simp [dfsrStep, borrowTransducer_nextState, borrowTransducer_outBit, borrowBit]
  have habs := dfsr_autonomous_absorption borrowTransducer k hk aux (false, false)
    L (2 * k + 1) ⟨false, fun _ => false⟩ haux hsink (borrow_universal_absorption k hk)
  have hz_eq : z = evalBits (dfsrBit borrowTransducer k hk aux r) (w0 + 1) := by
    simp only [evalBits]
    have hbit0 : dfsrBit borrowTransducer k hk aux r w0 = false := by
      simp [dfsrBit, habs r w0 (Nat.le_refl w0)]
    simp [z, aux, hbit0]
  have hfl : dfsrFlush borrowTransducer k hk aux (w0 + 1) r = true := by
    simp [dfsrFlush, habs r (w0 + 1) (by omega)]
  have hfl_bits := (dfsrFlush_iff borrowTransducer k hk aux (w0 + 1) r).1 hfl
  have hstate : ∀ i ≤ w0 + 1, runState borrowTransducer aux z i = dfsrQ borrowTransducer k hk aux r i := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [runState, dfsrQ_succ]
      rw [ih (by omega), hz_eq, testBit_evalBits]
      have hiw : i < w0 + 1 := by omega
      simp [hiw]
  have hsol_tr : z >>> k = transducerEval borrowTransducer aux z (w0 + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hrhs := testBit_evalBits (transducerOut borrowTransducer aux z) (w0 + 1) i
    rw [Nat.testBit_shiftRight, transducerEval, hrhs]
    by_cases hi : i < w0 + 1
    · simp only [hi, decide_true, Bool.true_and, transducerOut]
      rw [hstate i (by omega)]
      have hzi : z.testBit i = dfsrBit borrowTransducer k hk aux r i := by
        rw [hz_eq, testBit_evalBits]; simp [hi]
      rw [hzi, ← dfsrBit_add_k borrowTransducer k hk aux r i]
      have hcomm : k + i = i + k := Nat.add_comm k i
      rw [hcomm, hz_eq, testBit_evalBits]
      by_cases hik : i + k < w0 + 1
      · simp [hik]
      · simp only [hik, decide_false, Bool.false_and]
        have hj : i + k - (w0 + 1) < k := by omega
        have heq : (w0 + 1) + (i + k - (w0 + 1)) = i + k := by omega
        have h0 := hfl_bits (i + k - (w0 + 1)) hj
        rw [heq] at h0
        exact h0.symm
    · simp only [hi, decide_false, Bool.false_and]
      exact testBit_lt_of_le hzlt (by omega)
  have hz_lt1 : z < 2 ^ (w0 + 1) := Nat.lt_of_lt_of_le hzlt (Nat.pow_le_pow_right (by omega) (by omega))
  have hm_lt1 : m < 2 ^ (w0 + 1) := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
  have hmod := (borrowTransducer_equiv k c m (w0 + 1) z hz_lt1 hm_lt1).2 hsol_tr
  have hy_lt : z ^^^ (z >>> k) < 2 ^ w0 := by
    have hshr : z >>> k < 2 ^ w0 := Nat.lt_of_le_of_lt (Nat.shiftRight_le z k) hzlt
    exact Nat.xor_lt_two_pow hzlt hshr
  have hc_lt : c < 2 ^ w0 := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega))
  have hsum_lt : (z ^^^ (z >>> k)) + c < 2 ^ (w0 + 1) := by
    rw [Nat.pow_succ]; omega
  rw [Nat.mod_eq_of_lt hsum_lt] at hmod
  exact ⟨hzlt, hmod⟩


/-! ### Instantiation I.2: Bit-Exact Sharpness of `L + 2*k + 1` for EVERY `k ≥ 1` -/

theorem testBit_two_pow_sub_one (n i : Nat) :
    (2 ^ n - 1).testBit i = decide (i < n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have h1 : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + 2 ^ n := by
      have := Nat.two_pow_pos n; rw [Nat.pow_succ]; omega
    rw [h1, testBit_add_two_pow_of_lt (by have := Nat.two_pow_pos n; omega), ih]
    by_cases hi : i = n
    · subst hi; simp
    · simp only [hi, ↓reduceIte]
      by_cases hlt : i < n
      · have hlt' : i < n + 1 := by omega
        simp [hlt, hlt']
      · have hlt' : ¬ (i < n + 1) := by omega
        simp [hlt, hlt']

/-- **THEOREM I.2 (Bit-Exact Sharpness of `w ≥ L + 2*k + 1` for EVERY `k ≥ 1`)**:
    With `c = 2^(k+1) - 1` (`L = k + 1`), at `w = L + 2*k = 3*k + 1` (just 1 bit below threshold!),
    seed `r = 0` fails the MSB zero-flush condition, so there are strictly fewer than `2^k` fixed points! -/
theorem grayRight_threshold_sharp (k : Nat) (hk : 0 < k) :
    let c := 2 ^ (k + 1) - 1
    let w := 3 * k + 1
    countBelow (fun x => decide (((x ^^^ (x >>> k)) + c) % 2 ^ w = x)) (2 ^ w) < 2 ^ k := by
  intro c w
  let aux : Nat → Bool × Bool := fun i => (c.testBit i, (0 : Nat).testBit i)
  have haux : ∀ i, aux i = (decide (i < k + 1), false) := by
    intro i; simp [aux, c]
  rw [countBelow_congr (Q := fun x => decide (x >>> k = transducerEval borrowTransducer aux x w)) (fun x hx => by
    have h0 := borrowTransducer_equiv k c 0 w x hx (Nat.two_pow_pos w)
    simp only [Nat.xor_zero] at h0
    exact decide_eq_decide.2 h0)]
  rw [bdftr_exact_count borrowTransducer k hk aux w (by omega)]
  let xB := dfsrBit borrowTransducer k hk aux 0
  let qB := dfsrQ borrowTransducer k hk aux 0
  have hx0 : ∀ i < k, xB i = false := by
    intro i hi; simp [xB, dfsrBit_seed borrowTransducer k hk aux 0 i hi]
  have hq_p1 : ∀ i, 1 ≤ i → i ≤ k → qB i = true := by
    intro i h1 hik
    induction i with
    | zero => omega
    | succ i _ =>
      show borrowBit (xor (xB i) (aux i).2) (aux i).1 (qB i) = true
      rw [hx0 i (by omega), haux i]
      have hi_lt : i < k + 1 := by omega
      simp [hi_lt, borrowBit]
  have hxk : xB k = true := by
    have h := dfsrBit_add_k borrowTransducer k hk aux 0 0
    simp only [Nat.zero_add, borrowTransducer_outBit, haux 0] at h
    have h0lt : 0 < k + 1 := by omega
    have hq0 : dfsrQ borrowTransducer k hk aux 0 0 = false := rfl
    change dfsrBit borrowTransducer k hk aux 0 k = true
    rw [h, hq0]
    simp [h0lt]
  have hx_p2 : ∀ i, 1 ≤ i → i ≤ k → xB (i + k) = false := by
    intro i h1 hik
    have h := dfsrBit_add_k borrowTransducer k hk aux 0 i
    simp only [borrowTransducer_outBit, haux i] at h
    have hi_lt : i < k + 1 := by omega
    have hqi : dfsrQ borrowTransducer k hk aux 0 i = true := hq_p1 i h1 hik
    change dfsrBit borrowTransducer k hk aux 0 (i + k) = false
    rw [h, hqi]
    simp [hi_lt]
  have hqk1 : qB (k + 1) = true := by
    show borrowBit (xor (xB k) (aux k).2) (aux k).1 (qB k) = true
    rw [hxk, haux k, hq_p1 k (by omega) (Nat.le_refl k)]
    simp [borrowBit]
  have hq_p3 : ∀ t ≤ k, qB (k + 1 + t) = true := by
    intro t ht
    induction t with
    | zero => exact hqk1
    | succ t ih =>
      have hidx : k + 1 + (t + 1) = (k + 1 + t) + 1 := by omega
      rw [hidx]
      show borrowBit (xor (xB (k + 1 + t)) (aux (k + 1 + t)).2) (aux (k + 1 + t)).1 (qB (k + 1 + t)) = true
      have hx_zero : xB (k + 1 + t) = false := by
        have : t + 1 + k = k + 1 + t := by omega
        rw [← this]; exact hx_p2 (t + 1) (by omega) (by omega)
      rw [hx_zero, haux (k + 1 + t), ih (by omega)]
      simp [show ¬ (k + 1 + t < k + 1) by omega, borrowBit]
  have hx_fail : xB w = true := by
    have h := dfsrBit_add_k borrowTransducer k hk aux 0 (2 * k + 1)
    have hidx : 2 * k + 1 + k = w := by omega
    rw [hidx, borrowTransducer_outBit, haux (2 * k + 1)] at h
    have hq2k1 : dfsrQ borrowTransducer k hk aux 0 (2 * k + 1) = true := by
      have : k + 1 + k = 2 * k + 1 := by omega
      rw [← this]; exact hq_p3 k (Nat.le_refl k)
    change dfsrBit borrowTransducer k hk aux 0 w = true
    rw [h, hq2k1]
    simp [show ¬ (2 * k + 1 < k + 1) by omega]
  have hflush0 : dfsrFlush borrowTransducer k hk aux w 0 = false := by
    cases hfl : dfsrFlush borrowTransducer k hk aux w 0 with
    | false => rfl
    | true =>
      have h0 := ((dfsrFlush_iff borrowTransducer k hk aux w 0).1 hfl) 0 hk
      simp only [Nat.add_zero] at h0
      rw [show dfsrBit borrowTransducer k hk aux 0 w = true from hx_fail] at h0
      contradiction
  exact countBelow_lt_of_false (Nat.two_pow_pos k) hflush0


/-! ### Instantiation I.3 & I.4: Sign-Asymmetry Dual Carry Transducer (`G_k(x) - d ≡ x`) -/

/-- Dual 2-state carry transducer for `(x ^^^ (x >>> k)) = (x + d) % 2^w`
    (equivalently `((x ^^^ (x >>> k)) - d) ≡ x (mod 2^w)`). -/
def carryTransducer : BitTransducer Bool Bool where
  init := false
  nextState c xi di := maj xi di c
  outBit c _ di := xor di c

theorem carryTransducer_nextState (c xi di : Bool) :
    carryTransducer.nextState c xi di = maj xi di c := rfl

theorem carryTransducer_outBit (c xi di : Bool) :
    carryTransducer.outBit c xi di = xor di c := rfl

/-- Equivalence between `x ^^^ (x >>> k) = (x + d) % 2^w` and `carryTransducer`. -/
theorem carryTransducer_equiv (k d w x : Nat) (hx : x < 2 ^ w) :
    x ^^^ (x >>> k) = (x + d) % 2 ^ w ↔
    x >>> k = transducerEval carryTransducer (fun i => d.testBit i) x w := by
  let aux : Nat → Bool := fun i => d.testBit i
  have hcarry : ∀ i, carryAt x d false i = runState carryTransducer aux x i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => simp [carryAt, runState, carryTransducer_nextState, aux, ih]
  constructor
  · intro heq
    apply Nat.eq_of_testBit_eq
    intro i
    rw [transducerEval, testBit_evalBits]
    by_cases hi : i < w
    · simp only [hi, decide_true, Bool.true_and, transducerOut, carryTransducer_outBit]
      change (x >>> k).testBit i = xor (d.testBit i) (runState carryTransducer aux x i)
      rw [← hcarry i]
      have hbit := congrArg (fun n => n.testBit i) heq
      rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, testBit_add] at hbit
      simp only [hi, decide_true, Bool.true_and] at hbit
      cases h1 : x.testBit i <;> cases h2 : (x >>> k).testBit i <;> cases h3 : d.testBit i <;>
      cases h4 : carryAt x d false i <;> simp_all
    · simp only [hi, decide_false, Bool.false_and, Nat.testBit_shiftRight]
      exact testBit_lt_of_le hx (by omega)
  · intro heq
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow]
    by_cases hi : i < w
    · simp only [hi, decide_true, Bool.true_and, testBit_add]
      have hbit := congrArg (fun n => n.testBit i) heq
      rw [transducerEval, testBit_evalBits] at hbit
      have hbit' : (x >>> k).testBit i = xor (d.testBit i) (runState carryTransducer aux x i) := by
        simpa only [hi, decide_true, Bool.true_and, transducerOut, carryTransducer_outBit] using hbit
      rw [hbit', ← hcarry i]
    · simp only [hi, decide_false, Bool.false_and]
      have hx0 : x.testBit i = false := testBit_lt_of_le hx (by omega)
      have hxk0 : (x >>> k).testBit i = false := by
        rw [Nat.testBit_shiftRight]; exact testBit_lt_of_le hx (by omega)
      simp [hx0, hxk0]

/-- The non-zero carry-trap state `⟨true, fun _ => true⟩` is an absorbing fixed point
    of autonomous `carryTransducer` (`di = false`). -/
theorem carry_trap_fixed (k : Nat) (hk : 0 < k) :
    dfsrStep carryTransducer k hk false ⟨true, fun _ => true⟩ = ⟨true, fun _ => true⟩ := by
  simp [dfsrStep, carryTransducer_nextState, carryTransducer_outBit, maj]

theorem testBit_sub_two_pow (a b i : Nat) (hba : b ≤ a) :
    (2 ^ a - 2 ^ b).testBit i = decide (b ≤ i ∧ i < a) := by
  have heq : 2 ^ a - 2 ^ b = (2 ^ (a - b) - 1) <<< b := by
    rw [Nat.shiftLeft_eq]
    have hpow : 2 ^ (a - b) * 2 ^ b = 2 ^ a := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hba]
    have h1 : 1 ≤ 2 ^ (a - b) := Nat.two_pow_pos (a - b)
    rw [Nat.sub_mul, Nat.one_mul, hpow]
  rw [heq, Nat.testBit_shiftLeft, testBit_two_pow_sub_one]
  by_cases h1 : b ≤ i
  · by_cases h2 : i < a
    · have : i - b < a - b := by omega
      simp [h1, h2, this]
    · have : ¬ (i - b < a - b) := by omega
      simp [h1, h2, this]
  · simp [h1]

/-- **THEOREM I.3 (Sign-Asymmetry Complete Annihilation Law via Carry-Trap Sink)**:
    For EVERY `k ≥ 1`, letting `d = 2^(2*k+1) - 2^k`, EVERY seed `r < 2^k` enters the
    absorbing carry-trap sink `⟨true, 1^k⟩` at step `2*k + 1`. Consequently, for EVERY `w ≥ 2*k + 1`,
    the carry-driven dual `(x ^^^ (x >>> k)) = (x + d) % 2^w` has **EXACTLY ZERO solutions**
    (in stark contrast to `+d`, which has `2^k` solutions for all `w ≥ 4*k + 2`). -/
theorem grayRight_sub_complete_annihilation (k w : Nat) (hk : 0 < k) (hw : 2 * k + 1 ≤ w) :
    let d := 2 ^ (2 * k + 1) - 2 ^ k
    countBelow (fun x => decide ((x ^^^ (x >>> k)) = (x + d) % 2 ^ w)) (2 ^ w) = 0 := by
  intro d
  let aux : Nat → Bool := fun i => d.testBit i
  have haux : ∀ i, aux i = decide (k ≤ i ∧ i < 2 * k + 1) := by
    intro i; exact testBit_sub_two_pow (2 * k + 1) k i (by omega)
  rw [countBelow_congr (Q := fun x => decide (x >>> k = transducerEval carryTransducer aux x w)) (fun x hx =>
    decide_eq_decide.2 (carryTransducer_equiv k d w x hx))]
  rw [bdftr_exact_count carryTransducer k hk aux w (by omega)]
  have hall_trapped : ∀ r, dfsrFlush carryTransducer k hk aux w r = false := by
    intro r
    let xB := dfsrBit carryTransducer k hk aux r
    let qB := dfsrQ carryTransducer k hk aux r
    have hq_p1 : ∀ i ≤ k, qB i = false := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        show maj (xB i) (aux i) (qB i) = false
        have hdi : aux i = false := by rw [haux]; simp [show ¬ (k ≤ i) by omega]
        rw [hdi, ih (by omega)]; cases xB i <;> rfl
    have hx_p1 : ∀ i < k, xB (i + k) = false := by
      intro i hi
      have h := dfsrBit_add_k carryTransducer k hk aux r i
      rw [carryTransducer_outBit] at h
      have hdi : aux i = false := by rw [haux]; simp [show ¬ (k ≤ i) by omega]
      have hqi : dfsrQ carryTransducer k hk aux r i = false := hq_p1 i (by omega)
      change dfsrBit carryTransducer k hk aux r (i + k) = false
      rw [h, hdi, hqi]; rfl
    have hq_p2 : ∀ t ≤ k, qB (k + t) = false := by
      intro t ht
      induction t with
      | zero => exact hq_p1 k (Nat.le_refl k)
      | succ t ih =>
        have hidx : k + (t + 1) = (k + t) + 1 := by omega
        rw [hidx]
        show maj (xB (k + t)) (aux (k + t)) (qB (k + t)) = false
        have hxt : xB (k + t) = false := by
          have : t + k = k + t := by omega
          rw [← this]; exact hx_p1 t (by omega)
        rw [hxt, ih (by omega)]; cases aux (k + t) <;> rfl
    have hx_p2 : ∀ t ≤ k, xB (2 * k + t) = true := by
      intro t ht
      have h := dfsrBit_add_k carryTransducer k hk aux r (k + t)
      have hidx : k + t + k = 2 * k + t := by omega
      rw [hidx, carryTransducer_outBit] at h
      have hdi : aux (k + t) = true := by rw [haux]; simp [show k ≤ k + t ∧ k + t < 2 * k + 1 by omega]
      have hqt : dfsrQ carryTransducer k hk aux r (k + t) = false := hq_p2 t ht
      change dfsrBit carryTransducer k hk aux r (2 * k + t) = true
      rw [h, hdi, hqt]; rfl
    have hq_trap : qB (2 * k + 1) = true := by
      show maj (xB (2 * k)) (aux (2 * k)) (qB (2 * k)) = true
      have hx2k : xB (2 * k) = true := by simpa using hx_p2 0 (by omega)
      have hd2k : aux (2 * k) = true := by rw [haux]; simp [show k ≤ 2 * k ∧ 2 * k < 2 * k + 1 by omega]
      rw [hx2k, hd2k]; cases qB (2 * k) <;> rfl
    have hreach : dfsrRun carryTransducer k hk aux r (2 * k + 1) = ⟨true, fun _ => true⟩ := by
      cases hst : dfsrRun carryTransducer k hk aux r (2 * k + 1) with
      | mk q b =>
        have hq' : q = true := by
          have : (dfsrRun carryTransducer k hk aux r (2 * k + 1)).q = true := hq_trap
          rw [hst] at this; exact this
        subst hq'
        congr
        funext j
        have hb : b j = dfsrBit carryTransducer k hk aux r (2 * k + 1 + j.val) := by
          have hsh := dfsr_buf_shift carryTransducer k hk aux r j.val (2 * k + 1) j.isLt
          rw [hst] at hsh
          exact hsh
        have hidx : 2 * k + 1 + j.val = 2 * k + (j.val + 1) := by omega
        rw [hb, hidx]
        exact hx_p2 (j.val + 1) (by omega)
    have haux_tail : ∀ i ≥ 2 * k + 1, aux i = false := by
      intro i hi; rw [haux]; simp [show ¬ (i < 2 * k + 1) by omega]
    exact dfsr_trapped_no_flush carryTransducer k hk aux false (2 * k + 1) (2 * k + 1)
      ⟨true, fun _ => true⟩ r (Nat.le_refl _) haux_tail (carry_trap_fixed k hk) rfl hreach w hw
  rw [countBelow_congr (Q := fun _ => false) (fun r _ => hall_trapped r)]
  exact countBelow_false (2 ^ k)

/-- Constructive search for a zero bit below `k` whenever `r < 2^k - 1` (zero `Classical.choice`). -/
theorem exists_false_bit_of_lt_two_pow_sub_one :
    ∀ (k r : Nat), r < 2 ^ k - 1 → ∃ i < k, r.testBit i = false
  | 0, r, hr => by simp at hr
  | k + 1, r, hr => by
    by_cases heven : r % 2 = 0
    · refine ⟨0, by omega, ?_⟩
      simp [Nat.testBit_zero, heven]
    · have hlt : r / 2 < 2 ^ k - 1 := by
        have := Nat.two_pow_pos k
        rw [Nat.pow_succ] at hr
        omega
      rcases exists_false_bit_of_lt_two_pow_sub_one k (r / 2) hlt with ⟨i, hi, hbit⟩
      refine ⟨i + 1, by omega, ?_⟩
      rw [Nat.testBit_succ]
      exact hbit

/-- **THEOREM I.4 (Sign-Asymmetry Single-Trap Law for `d = 1`)**:
    For EVERY `k ≥ 1` and EVERY `w ≥ 2*k`, `(x ^^^ (x >>> k)) = (x + 1) % 2^w`
    has **EXACTLY `2^k - 1` solutions** (seed `2^k - 1` is trapped in `⟨true, 1^k⟩`,
    while every seed `r < 2^k - 1` flushes to `⟨false, 0^k⟩` by step `2*k`). -/
theorem grayRight_sub_one_exact_count (k w : Nat) (hk : 0 < k) (hw : 2 * k ≤ w) :
    countBelow (fun x => decide ((x ^^^ (x >>> k)) = (x + 1) % 2 ^ w)) (2 ^ w) = 2 ^ k - 1 := by
  let aux : Nat → Bool := fun i => (1 : Nat).testBit i
  have haux0 : aux 0 = true := by decide
  have haux_tail : ∀ i ≥ 1, aux i = false := by
    intro i hi
    exact testBit_lt_of_le (by omega : 1 < 2 ^ 1) hi
  rw [countBelow_congr (Q := fun x => decide (x >>> k = transducerEval carryTransducer aux x w)) (fun x hx =>
    decide_eq_decide.2 (carryTransducer_equiv k 1 w x hx))]
  rw [bdftr_exact_count carryTransducer k hk aux w (by omega)]
  have hchar : ∀ r < 2 ^ k, dfsrFlush carryTransducer k hk aux w r = decide (r < 2 ^ k - 1) := by
    intro r hr
    by_cases htop : r = 2 ^ k - 1
    · subst htop
      simp only [Nat.lt_irrefl, decide_false]
      have hreach : dfsrRun carryTransducer k hk aux (2 ^ k - 1) 1 = ⟨true, fun _ => true⟩ := by
        simp only [dfsrRun, dfsrStep, dfsrInit, carryTransducer_nextState, carryTransducer_outBit,
                   haux0, testBit_two_pow_sub_one, hk, decide_true, maj]
        congr
        funext j
        split
        · simp [show j.val + 1 < k by assumption]
        · rfl
      exact dfsr_trapped_no_flush carryTransducer k hk aux false 1 1
        ⟨true, fun _ => true⟩ (2 ^ k - 1) (Nat.le_refl 1) haux_tail
        (carry_trap_fixed k hk) rfl hreach w (by omega)
    · have hrlt : r < 2 ^ k - 1 := by omega
      simp only [hrlt, decide_true]
      rcases exists_false_bit_of_lt_two_pow_sub_one k r hrlt with ⟨i0, hi0, hbit0⟩
      let qB := dfsrQ carryTransducer k hk aux r
      have hq_dead : qB (i0 + 1) = false := by
        show maj (dfsrBit carryTransducer k hk aux r i0) (aux i0) (qB i0) = false
        rw [dfsrBit_seed carryTransducer k hk aux r i0 hi0, hbit0]
        by_cases h0 : i0 = 0
        · subst h0; rfl
        · rw [haux_tail i0 (by omega)]; cases qB i0 <;> rfl
      have hq_stay : ∀ m, qB (i0 + 1 + m) = false := by
        intro m
        induction m with
        | zero => exact hq_dead
        | succ m ih =>
          have hidx : i0 + 1 + (m + 1) = (i0 + 1 + m) + 1 := by omega
          rw [hidx]
          show maj (dfsrBit carryTransducer k hk aux r (i0 + 1 + m))
                   (aux (i0 + 1 + m)) (qB (i0 + 1 + m)) = false
          rw [haux_tail (i0 + 1 + m) (by omega), ih]
          cases dfsrBit carryTransducer k hk aux r (i0 + 1 + m) <;> rfl
      rw [dfsrFlush_iff]
      intro j hj
      have hidx : w + j = (w + j - k) + k := by omega
      rw [hidx, dfsrBit_add_k, carryTransducer_outBit]
      have hq0 : dfsrQ carryTransducer k hk aux r (w + j - k) = false := by
        have : i0 + 1 + (w + j - k - (i0 + 1)) = w + j - k := by omega
        rw [← this]; exact hq_stay _
      have hd0 : aux (w + j - k) = false := haux_tail (w + j - k) (by omega)
      rw [hd0, hq0]; rfl
  rw [countBelow_congr hchar]
  exact countBelow_lt_pred (Nat.two_pow_pos k)


theorem xorSum_add (g : Nat → Bool) (a : Nat) :
    ∀ b, xorSum g (a + b) = xor (xorSum g a) (xorSum (fun j => g (a + j)) b)
  | 0 => by simp [xorSum]
  | b + 1 => by
    rw [show a + (b + 1) = (a + b) + 1 by omega, xorSum, xorSum, xorSum_add g a b]
    cases xorSum g a <;> cases xorSum (fun j => g (a + j)) b <;> cases g (a + b) <;> rfl

theorem xorSum_xor (g h : Nat → Bool) :
    ∀ n, xorSum (fun j => xor (g j) (h j)) n = xor (xorSum g n) (xorSum h n)
  | 0 => rfl
  | n + 1 => by
    simp only [xorSum, xorSum_xor g h n]
    cases xorSum g n <;> cases xorSum h n <;> cases g n <;> cases h n <;> rfl

theorem xorSum_const (b : Bool) :
    ∀ n, xorSum (fun _ => b) n = (decide (n % 2 = 1) && b)
  | 0 => rfl
  | n + 1 => by
    rw [xorSum, xorSum_const b n]
    have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hpar with h0 | h1
    · have h1' : (n + 1) % 2 = 1 := by omega
      simp [h0, h1']
    · have h0' : (n + 1) % 2 = 0 := by omega
      cases b <;> simp [h1, h0']

theorem xorSum_congr {g h : Nat → Bool} {n : Nat} (heq : ∀ j < n, g j = h j) :
    xorSum g n = xorSum h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorSum, ih (fun j hj => heq j (by omega)), heq n (by omega)]

theorem xorSum_two_mul (g : Nat → Bool) (p : Nat) :
    xorSum g (2 * p) = xorSum (fun j => xor (g j) (g (j + p))) p := by
  have h2 : 2 * p = p + p := by omega
  rw [h2, xorSum_add, xorSum_xor]
  congr 1
  apply xorSum_congr
  intro j _
  rw [Nat.add_comm]

/-- Exact single-step bit-`w` flip of `lstep k c (w + 1)`. -/
def stepBit (k c w x : Nat) : Bool :=
  xor (shiftBit k w x) (xor (c.testBit w) (carryBit k c w x))

theorem lstep_lt (k c w x : Nat) : lstep k c w x < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

theorem iterFn_lstep_lt (k c w x : Nat) (hx : x < 2 ^ w) :
    ∀ n, iterFn (lstep k c w) n x < 2 ^ w
  | 0 => hx
  | _ + 1 => lstep_lt k c w _

theorem testBit_lgray (k x i : Nat) :
    (lgray k x).testBit i = xor (x.testBit i) (shiftBit k i x) := by
  simp only [lgray, Nat.testBit_xor, Nat.testBit_shiftLeft, shiftBit]
  by_cases h : k ≤ i
  · simp [h]
  · simp [h]

theorem lgray_mod_eq (k w x : Nat) :
    lgray k (x % 2 ^ w) % 2 ^ w = lgray k x % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, testBit_lgray, shiftBit]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and]
    by_cases hk : k ≤ i
    · have hik : i - k < w := by omega
      simp [hk, hik]
    · simp [hk]
  · simp [hi]

theorem lstep_mod_x (k c w x : Nat) : lstep k c w (x % 2 ^ w) = lstep k c w x := by
  simp only [lstep, lgray_mod_eq]

theorem lstep_mod_c (k c₁ c₂ w x : Nat) (hc : c₁ % 2 ^ w = c₂ % 2 ^ w) :
    lstep k c₁ w x = lstep k c₂ w x := by
  simp only [lstep]
  rw [Nat.add_mod, hc, ← Nat.add_mod]

theorem mod_two_pow_succ_mod (a w : Nat) : a % 2 ^ (w + 1) % 2 ^ w = a % 2 ^ w := by
  have hdvd : 2 ^ w ∣ 2 ^ (w + 1) := by
    rw [Nat.pow_succ]; exact Nat.dvd_mul_right (2 ^ w) 2
  exact Nat.mod_mod_of_dvd a hdvd

theorem lstep_proj (k c w x : Nat) :
    lstep k c (w + 1) x % 2 ^ w = lstep k c w (x % 2 ^ w) := by
  simp only [lstep, lgray_mod_eq]
  rw [mod_two_pow_succ_mod, Nat.add_mod, mod_two_pow_succ_mod, ← Nat.add_mod]
  rw [Nat.add_mod (lgray k x % 2 ^ w), Nat.mod_mod, ← Nat.add_mod]

theorem iterFn_lstep_proj (k c w x : Nat) :
    ∀ n, iterFn (lstep k c (w + 1)) n x % 2 ^ w = iterFn (lstep k c w) n (x % 2 ^ w)
  | 0 => rfl
  | n + 1 => by
    show lstep k c (w + 1) (iterFn (lstep k c (w + 1)) n x) % 2 ^ w =
         lstep k c w (iterFn (lstep k c w) n (x % 2 ^ w))
    rw [lstep_proj, iterFn_lstep_proj k c w x n]

theorem iterFn_lstep_mod_c (k c₁ c₂ w x : Nat) (hc : c₁ % 2 ^ w = c₂ % 2 ^ w) :
    ∀ n, iterFn (lstep k c₁ w) n x = iterFn (lstep k c₂ w) n x
  | 0 => rfl
  | n + 1 => by
    show lstep k c₁ w (iterFn (lstep k c₁ w) n x) = lstep k c₂ w (iterFn (lstep k c₂ w) n x)
    rw [iterFn_lstep_mod_c k c₁ c₂ w x hc n, lstep_mod_c k c₁ c₂ w _ hc]

/-- Bit `w` of `(a + b) % 2^(w + 1)` from bits `w` of `a, b` and low-word carry. -/
theorem testBit_add_mod_two_pow_succ (a b w : Nat) :
    ((a + b) % 2 ^ (w + 1)).testBit w =
      xor (a.testBit w) (xor (b.testBit w) (decide (2 ^ w ≤ a % 2 ^ w + b % 2 ^ w))) := by
  have h1 : ∀ n, n.testBit w = decide ((n / 2 ^ w) % 2 = 1) := by
    intro n
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
    cases h : (n / 2 ^ w) % 2 with
    | zero => rfl
    | succ m =>
      have : m = 0 := by
        have := Nat.mod_lt (n / 2 ^ w) (by omega : 0 < 2)
        omega
      subst this; rfl
  rw [h1, h1, h1]
  have hpow : 0 < 2 ^ w := Nat.two_pow_pos w
  have ha : a = a % 2 ^ w + 2 ^ w * (a / 2 ^ w) := (Nat.mod_add_div a (2 ^ w)).symm
  have hb : b = b % 2 ^ w + 2 ^ w * (b / 2 ^ w) := (Nat.mod_add_div b (2 ^ w)).symm
  have ha_lt : a % 2 ^ w < 2 ^ w := Nat.mod_lt a hpow
  have hb_lt : b % 2 ^ w < 2 ^ w := Nat.mod_lt b hpow
  have hmod_div : ((a + b) % 2 ^ (w + 1)) / 2 ^ w = ((a + b) / 2 ^ w) % 2 := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2]
    have hqr := Nat.mod_add_div (a + b) (2 ^ w)
    have hq2 := Nat.mod_add_div ((a + b) / 2 ^ w) 2
    have hrlt : (a + b) % 2 ^ w < 2 ^ w := Nat.mod_lt _ hpow
    have hqlt : ((a + b) / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hrem : (a + b) % (2 * 2 ^ w) = (a + b) % 2 ^ w + 2 ^ w * (((a + b) / 2 ^ w) % 2) := by
      have hdecomp : a + b = ((a + b) % 2 ^ w + 2 ^ w * (((a + b) / 2 ^ w) % 2)) +
          (2 * 2 ^ w) * (((a + b) / 2 ^ w) / 2) := by
        calc a + b = (a + b) % 2 ^ w + 2 ^ w * ((a + b) / 2 ^ w) := hqr.symm
          _ = (a + b) % 2 ^ w + 2 ^ w * (((a + b) / 2 ^ w) % 2 + 2 * (((a + b) / 2 ^ w) / 2)) := by
            rw [hq2]
          _ = _ := by
            rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ w) 2]; omega
      have hlt : (a + b) % 2 ^ w + 2 ^ w * (((a + b) / 2 ^ w) % 2) < 2 * 2 ^ w := by
        have hpar : ((a + b) / 2 ^ w) % 2 = 0 ∨ ((a + b) / 2 ^ w) % 2 = 1 := by omega
        rcases hpar with h0 | h1'
        · rw [h0]; omega
        · rw [h1']; omega
      have hm := congrArg (fun n => n % (2 * 2 ^ w)) hdecomp
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt] at hm
      exact hm
    rw [hrem, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hrlt, Nat.zero_add]
  rw [hmod_div, Nat.mod_mod]
  have hsum_div : (a + b) / 2 ^ w =
      a / 2 ^ w + b / 2 ^ w + if 2 ^ w ≤ a % 2 ^ w + b % 2 ^ w then 1 else 0 := by
    have hsplit : a + b = (a % 2 ^ w + b % 2 ^ w) + 2 ^ w * (a / 2 ^ w + b / 2 ^ w) := by
      rw [Nat.mul_add]; omega
    rw [hsplit, Nat.add_mul_div_left _ _ hpow]
    by_cases hc : 2 ^ w ≤ a % 2 ^ w + b % 2 ^ w
    · simp only [hc, ↓reduceIte]
      have hq : (a % 2 ^ w + b % 2 ^ w) / 2 ^ w = 1 := by
        have h1' : a % 2 ^ w + b % 2 ^ w = (a % 2 ^ w + b % 2 ^ w - 2 ^ w) + 2 ^ w * 1 := by omega
        rw [h1', Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt (by omega)]
      omega
    · simp only [hc, ↓reduceIte, Nat.add_zero]
      rw [Nat.div_eq_of_lt (by omega)]; omega
  rw [hsum_div]
  have hda : (a / 2 ^ w) % 2 = 0 ∨ (a / 2 ^ w) % 2 = 1 := by omega
  have hdb : (b / 2 ^ w) % 2 = 0 ∨ (b / 2 ^ w) % 2 = 1 := by omega
  by_cases hc : 2 ^ w ≤ a % 2 ^ w + b % 2 ^ w
  · simp only [hc, ↓reduceIte, decide_true]
    rcases hda with hda | hda <;> rcases hdb with hdb | hdb <;>
      simp [hda, hdb, show (a / 2 ^ w + b / 2 ^ w + 1) % 2 = (a / 2 ^ w % 2 + b / 2 ^ w % 2 + 1) % 2 by omega]
  · simp only [hc, ↓reduceIte, decide_false, Nat.add_zero]
    rcases hda with hda | hda <;> rcases hdb with hdb | hdb <;>
      simp [hda, hdb, show (a / 2 ^ w + b / 2 ^ w) % 2 = (a / 2 ^ w % 2 + b / 2 ^ w % 2) % 2 by omega]

/-- **Exact Affine Bit-Lift Equation for `lstep` (valid for ALL `k ≥ 1, c, w, x`)**:
    Bit `w` of `lstep k c (w + 1) x` flips `x.testBit w` by `stepBit k c w (x % 2^w)`,
    which depends ONLY on `x % 2^w`! -/
theorem testBit_lstep_succ (k c w x : Nat) (hk : 0 < k) :
    (lstep k c (w + 1) x).testBit w = xor (x.testBit w) (stepBit k c w (x % 2 ^ w)) := by
  simp only [lstep, stepBit, carryBit]
  rw [testBit_add_mod_two_pow_succ]
  rw [Nat.testBit_mod_two_pow]
  simp only [show w < w + 1 by omega, decide_true, Bool.true_and, testBit_lgray]
  rw [mod_two_pow_succ_mod, lgray_mod_eq]
  have hsh : shiftBit k w x = shiftBit k w (x % 2 ^ w) := by
    simp only [shiftBit]
    by_cases hkw : k ≤ w
    · have hlt : w - k < w := by omega
      simp [hkw, Nat.testBit_mod_two_pow, hlt]
    · simp [hkw]
  rw [hsh]
  cases x.testBit w <;> cases shiftBit k w (x % 2 ^ w) <;>
  cases c.testBit w <;> cases decide (2 ^ w ≤ lgray k x % 2 ^ w + c % 2 ^ w) <;> rfl

/-- Iterated bit-`w` monodromy law along an orbit of `lstep k c (w + 1)`. -/
theorem testBit_iterFn_lstep_succ (k c w x : Nat) (hk : 0 < k) :
    ∀ n, (iterFn (lstep k c (w + 1)) n x).testBit w =
      xor (x.testBit w) (xorSum (fun j => stepBit k c w (iterFn (lstep k c w) j (x % 2 ^ w))) n)
  | 0 => by simp [iterFn, xorSum]
  | n + 1 => by
    show (lstep k c (w + 1) (iterFn (lstep k c (w + 1)) n x)).testBit w = _
    rw [testBit_lstep_succ k c w _ hk, iterFn_lstep_proj, testBit_iterFn_lstep_succ k c w x hk n]
    simp only [xorSum]
    cases x.testBit w <;>
    cases xorSum (fun j => stepBit k c w (iterFn (lstep k c w) j (x % 2 ^ w))) n <;>
    cases stepBit k c w (iterFn (lstep k c w) n (x % 2 ^ w)) <;> rfl

/-- On any EVEN-length orbit, the `c.testBit w` term cancels, so the exact bit-`w` monodromy
    equals `orbitDelta k c w x p` (which is independent of `c.testBit w`!). -/
theorem xorSum_stepBit_eq_orbitDelta (k c w x p : Nat) (hp : p % 2 = 0) :
    xorSum (fun j => stepBit k c w (iterFn (lstep k c w) j x)) p = orbitDelta k c w x p := by
  have hsplit : ∀ j, stepBit k c w (iterFn (lstep k c w) j x) =
      xor (c.testBit w) (deltaBit k c w (iterFn (lstep k c w) j x)) := by
    intro j
    simp only [stepBit, deltaBit]
    cases shiftBit k w (iterFn (lstep k c w) j x) <;>
    cases c.testBit w <;>
    cases carryBit k c w (iterFn (lstep k c w) j x) <;> rfl
  rw [xorSum_congr (fun j _ => hsplit j), xorSum_xor, xorSum_const]
  have hne : ¬ (p % 2 = 1) := by omega
  simp [hne, orbitDelta]

/-- Helper: two numbers `< 2^(w+1)` with the same `% 2^w` are either equal or differ by `^^^ 2^w`. -/
theorem eq_or_eq_xor_two_pow {a b w : Nat} (ha : a < 2 ^ (w + 1)) (hb : b < 2 ^ (w + 1))
    (hmod : a % 2 ^ w = b % 2 ^ w) :
    (a.testBit w = b.testBit w → a = b) ∧ (a.testBit w ≠ b.testBit w → a = b ^^^ 2 ^ w) := by
  constructor
  · intro hbw
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · have h := congrArg (fun n => n.testBit i) hmod
      simpa [Nat.testBit_mod_two_pow, hi] using h
    · by_cases heq : i = w
      · subst heq; exact hbw
      · rw [testBit_lt_of_le ha (by omega), testBit_lt_of_le hb (by omega)]
  · intro hne
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases hi : i < w
    · have h := congrArg (fun n => n.testBit i) hmod
      have hne' : w ≠ i := by omega
      simpa [Nat.testBit_mod_two_pow, hi, hne'] using h
    · by_cases heq : i = w
      · subst heq
        cases h1 : a.testBit i <;> cases h2 : b.testBit i <;> simp_all
      · have hne' : w ≠ i := by omega
        have ha0 : a.testBit i = false := testBit_lt_of_le ha (by omega)
        have hb0 : b.testBit i = false := testBit_lt_of_le hb (by omega)
        simp [hne', ha0, hb0]

/-- Flipping bit `w` of `u < 2^(w+1)` keeps it `< 2^(w+1)`, preserves `% 2^w`, and flips bit `w`. -/
theorem xor_two_pow_props {u w : Nat} (hu : u < 2 ^ (w + 1)) :
    u ^^^ 2 ^ w < 2 ^ (w + 1) ∧ (u ^^^ 2 ^ w) % 2 ^ w = u % 2 ^ w ∧
    (u ^^^ 2 ^ w).testBit w = !(u.testBit w) := by
  refine ⟨?_, ?_, ?_⟩
  · have hlt : 2 ^ w < 2 ^ (w + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    exact Nat.xor_lt_two_pow hu hlt
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases hi : i < w
    · have hne : w ≠ i := by omega
      simp [hi, hne]
    · simp [hi]
  · simp [Nat.testBit_xor]

/-- **Orbit Doubling Lemma**:
    If `x < 2^w` has even minimal period `p` at width `w` and `orbitDelta k c w x p = true`,
    then `x` has exact minimal period `2 * p` at width `w + 1`, and its second half is the
    top-bit-flipped mirror of its first half: `iter (j + p) x = (iter j x) ^^^ 2^w`! -/
theorem orbit_doubling_of_delta (k c w x p : Nat) (hk : 0 < k) (hx : x < 2 ^ w)
    (hp_even : p % 2 = 0)
    (hper : HasMinPeriod (lstep k c w) x p)
    (hdelta : orbitDelta k c w x p = true) :
    HasMinPeriod (lstep k c (w + 1)) x (2 * p) ∧
    ∀ j, iterFn (lstep k c (w + 1)) (j + p) x = (iterFn (lstep k c (w + 1)) j x) ^^^ 2 ^ w := by
  have hx1 : x < 2 ^ (w + 1) := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))
  have hxmod : x % 2 ^ w = x := Nat.mod_eq_of_lt hx
  have hxp_mod : iterFn (lstep k c (w + 1)) p x % 2 ^ w = x % 2 ^ w := by
    rw [iterFn_lstep_proj, hxmod, hper.2.1]
  have hxp_bit : (iterFn (lstep k c (w + 1)) p x).testBit w ≠ x.testBit w := by
    rw [testBit_iterFn_lstep_succ k c w x hk p, hxmod, xorSum_stepBit_eq_orbitDelta k c w x p hp_even, hdelta]
    cases x.testBit w <;> decide
  have hxp : iterFn (lstep k c (w + 1)) p x = x ^^^ 2 ^ w :=
    (eq_or_eq_xor_two_pow (iterFn_lstep_lt k c (w + 1) x hx1 p) hx1 hxp_mod).2 hxp_bit
  have hhalf : ∀ j, iterFn (lstep k c (w + 1)) (j + p) x = (iterFn (lstep k c (w + 1)) j x) ^^^ 2 ^ w := by
    intro j
    rw [Nat.add_comm j p, ← iterFn_add, hxp]
    have hprops := xor_two_pow_props hx1
    have hlt1 := iterFn_lstep_lt k c (w + 1) (x ^^^ 2 ^ w) hprops.1 j
    have hlt2 := iterFn_lstep_lt k c (w + 1) x hx1 j
    have hmod_j : iterFn (lstep k c (w + 1)) j (x ^^^ 2 ^ w) % 2 ^ w =
                  iterFn (lstep k c (w + 1)) j x % 2 ^ w := by
      rw [iterFn_lstep_proj, iterFn_lstep_proj, hprops.2.1]
    have hbit_j : (iterFn (lstep k c (w + 1)) j (x ^^^ 2 ^ w)).testBit w ≠
                  (iterFn (lstep k c (w + 1)) j x).testBit w := by
      rw [testBit_iterFn_lstep_succ k c w (x ^^^ 2 ^ w) hk j,
          testBit_iterFn_lstep_succ k c w x hk j, hprops.2.1, hprops.2.2]
      cases x.testBit w <;>
      cases xorSum (fun i => stepBit k c w (iterFn (lstep k c w) i (x % 2 ^ w))) j <;> decide
    exact (eq_or_eq_xor_two_pow hlt1 hlt2 hmod_j).2 hbit_j
  have hp_pos : 0 < p := hper.1
  refine ⟨⟨by omega, ?_, ?_⟩, hhalf⟩
  · -- iter (2 * p) x = x
    have h2 : 2 * p = p + p := by omega
    rw [h2, hhalf p, hxp]
    apply Nat.eq_of_testBit_eq
    intro i; simp [Nat.testBit_xor]
  · -- minimal period: for 0 < j < 2 * p, iter j x ≠ x
    intro j hj0 hjlt heq
    by_cases hjp : j = p
    · subst hjp
      rw [hxp] at heq
      have hbw := congrArg (fun n => n.testBit w) heq
      rw [(xor_two_pow_props hx1).2.2] at hbw
      cases h : x.testBit w <;> simp [h] at hbw
    · -- Project to width w!
      have hmod := congrArg (fun n => n % 2 ^ w) heq
      rw [iterFn_lstep_proj, hxmod] at hmod
      by_cases hltp : j < p
      · exact hper.2.2 j hj0 hltp hmod
      · have hgtp : p < j := by omega
        have hsub : j = p + (j - p) := by omega
        rw [hsub, ← iterFn_add, hper.2.1] at hmod
        exact hper.2.2 (j - p) (by omega) (by omega) hmod

/-- **Universal Pair-Carry Conservation Law (Heart of CPMF)**:
    For EVERY `k ≥ 1`, `c`, `w`, and `u < 2^(w + 1)`, the XOR of the `(w+1)`-bit carries on the
    top-bit-flipped pair `{u, u ^^^ 2^w}` equals `c.testBit w ^^ carryBit k c w (u % 2^w)`! -/
theorem pair_carry_conservation (k c w u : Nat) (hk : 0 < k) (hu : u < 2 ^ (w + 1)) :
    xor (carryBit k c (w + 1) u) (carryBit k c (w + 1) (u ^^^ 2 ^ w)) =
      xor (c.testBit w) (carryBit k c w (u % 2 ^ w)) := by
  have hpow : 0 < 2 ^ w := Nat.two_pow_pos w
  let y0 := lgray k u % 2 ^ w
  have hy0_lt : y0 < 2 ^ w := Nat.mod_lt _ hpow
  -- Decompose lgray k u % 2^(w+1) and lgray k (u ^^^ 2^w) % 2^(w+1) into y0 and y0 + 2^w
  have hdecomp : ∀ v, v % 2 ^ (w + 1) = v % 2 ^ w + if v.testBit w then 2 ^ w else 0 := by
    intro v
    apply Nat.eq_of_testBit_eq
    intro i
    cases hbw : v.testBit w with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.testBit_mod_two_pow]
      by_cases hi : i < w
      · have hi1 : i < w + 1 := by omega
        simp [hi, hi1]
      · by_cases heq : i = w
        · subst heq; simp [hbw]
        · have hi1 : ¬ (i < w + 1) := by omega
          simp [hi, hi1]
    | true =>
      simp only [↓reduceIte]
      rw [testBit_add_two_pow_of_lt (Nat.mod_lt v hpow), Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      by_cases hi : i = w
      · subst hi; simp [hbw]
      · simp only [hi, ↓reduceIte]
        by_cases hlt : i < w
        · have hlt1 : i < w + 1 := by omega
          simp [hlt, hlt1]
        · have hlt1 : ¬ (i < w + 1) := by omega
          simp [hlt, hlt1]
  have hmod_pair : lgray k (u ^^^ 2 ^ w) % 2 ^ w = y0 := by
    have hpr := xor_two_pow_props hu
    rw [← lgray_mod_eq, hpr.2.1, lgray_mod_eq]
  have hbit_pair : (lgray k (u ^^^ 2 ^ w)).testBit w = !((lgray k u).testBit w) := by
    have hpr := xor_two_pow_props hu
    simp only [testBit_lgray, hpr.2.2]
    have hsh : shiftBit k w (u ^^^ 2 ^ w) = shiftBit k w u := by
      simp only [shiftBit]
      by_cases hkw : k ≤ w
      · have hne : w ≠ w - k := by omega
        simp [hkw, Nat.testBit_xor, hne]
      · simp [hkw]
    rw [hsh]
    cases u.testBit w <;> cases shiftBit k w u <;> rfl
  simp only [carryBit]
  rw [hdecomp (lgray k u), hdecomp (lgray k (u ^^^ 2 ^ w)), hdecomp c, hmod_pair, hbit_pair]
  rw [lgray_mod_eq]
  have hc_lt : c % 2 ^ w < 2 ^ w := Nat.mod_lt c hpow
  have h2pow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  rw [h2pow]
  cases (lgray k u).testBit w <;> cases c.testBit w <;>
    (by_cases hcar : 2 ^ w ≤ y0 + c % 2 ^ w <;> simp [y0, hcar] <;> omega)

/-- Pair-XOR of `shiftBit k (w + 1)` on `{u, u ^^^ 2^w}`: `true` if `k = 1`, `false` if `k ≥ 2`. -/
theorem pair_shift_xor (k w u : Nat) (hk : 0 < k) (hu : u < 2 ^ (w + 1)) :
    xor (shiftBit k (w + 1) u) (shiftBit k (w + 1) (u ^^^ 2 ^ w)) = decide (k = 1) := by
  have hpr := xor_two_pow_props hu
  by_cases hk1 : k = 1
  · subst hk1
    simp only [shiftBit, show 1 ≤ w + 1 by omega, ↓reduceIte, Nat.add_sub_cancel, hpr.2.2, decide_true]
    cases u.testBit w <;> rfl
  · have hge2 : 2 ≤ k := by omega
    simp only [hk1, decide_false, shiftBit]
    by_cases hkw : k ≤ w + 1
    · have hne : w ≠ w + 1 - k := by omega
      simp [hkw, Nat.testBit_xor, hne]
    · simp [hkw]

/-- **One-Step CPMF Freezing Theorem**:
    If `x < 2^w` has EVEN minimal period `p` at width `w` with `orbitDelta = true` and
    `orbitKappa = true`, then at width `w + 1` it has minimal period `2 * p` AND BOTH
    `orbitKappa = true` and `orbitDelta = true` are PRESERVED (for ANY `c`, regardless of `c.testBit w`)! -/
theorem cpmf_step (k c w x p : Nat) (hk : 0 < k) (hx : x < 2 ^ w)
    (hp_even : p % 2 = 0)
    (hper : HasMinPeriod (lstep k c w) x p)
    (hdelta : orbitDelta k c w x p = true)
    (hkappa : orbitKappa k c w x p = true) :
    HasMinPeriod (lstep k c (w + 1)) x (2 * p) ∧
    orbitKappa k c (w + 1) x (2 * p) = true ∧
    orbitDelta k c (w + 1) x (2 * p) = true := by
  have hdoub := orbit_doubling_of_delta k c w x p hk hx hp_even hper hdelta
  have hx1 : x < 2 ^ (w + 1) := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))
  have hxmod : x % 2 ^ w = x := Nat.mod_eq_of_lt hx
  have hne1 : ¬ (p % 2 = 1) := by omega
  -- 1. Carry-parity conservation: orbitKappa (w + 1) (2 * p) = orbitKappa w p = true
  have hkap1 : orbitKappa k c (w + 1) x (2 * p) = true := by
    rw [orbitKappa, xorSum_two_mul]
    have hpair : ∀ j < p,
        xor (carryBit k c (w + 1) (iterFn (lstep k c (w + 1)) j x))
            (carryBit k c (w + 1) (iterFn (lstep k c (w + 1)) (j + p) x)) =
        xor (c.testBit w) (carryBit k c w (iterFn (lstep k c w) j x)) := by
      intro j _
      rw [hdoub.2 j, pair_carry_conservation k c w _ hk (iterFn_lstep_lt k c (w + 1) x hx1 j),
          iterFn_lstep_proj, hxmod]
    rw [xorSum_congr hpair, xorSum_xor, xorSum_const]
    simp only [hne1, decide_false, Bool.false_and, Bool.false_xor]
    exact hkappa
  -- 2. Shift-XOR cancellation on doubled orbit: xorSum (shiftBit ...) (2 * p) = false!
  have hsh0 : xorSum (fun j => shiftBit k (w + 1) (iterFn (lstep k c (w + 1)) j x)) (2 * p) = false := by
    rw [xorSum_two_mul]
    have hpair : ∀ j < p,
        xor (shiftBit k (w + 1) (iterFn (lstep k c (w + 1)) j x))
            (shiftBit k (w + 1) (iterFn (lstep k c (w + 1)) (j + p) x)) = decide (k = 1) := by
      intro j _
      rw [hdoub.2 j, pair_shift_xor k w _ hk (iterFn_lstep_lt k c (w + 1) x hx1 j)]
    rw [xorSum_congr hpair, xorSum_const]
    simp [hne1]
  -- 3. Combine: orbitDelta (w + 1) (2 * p) = false ^^ orbitKappa = true!
  have hdel1 : orbitDelta k c (w + 1) x (2 * p) = true := by
    rw [orbitDelta]
    change xorSum (fun j => xor (shiftBit k (w + 1) (iterFn (lstep k c (w + 1)) j x))
                                (carryBit k c (w + 1) (iterFn (lstep k c (w + 1)) j x))) (2 * p) = true
    rw [xorSum_xor, hsh0]
    simpa [orbitKappa] using hkap1
  exact ⟨hdoub.1, hkap1, hdel1⟩

/-- **THEOREM II.0 (CPMF Infinite Orbit Lifting Engine)**:
    Any base-width-`w0` cycle `(x, p)` of `lstep k c0 w0` with even `p`, `orbitDelta = true`,
    and `orbitKappa = true` lifts to an EXACT cycle of length `p * 2^d` for ALL `d : Nat`
    and ALL `c` with `c % 2^w0 = c0 % 2^w0`! -/
theorem cpmf_infinite_orbit_lift (k c0 w0 x p : Nat) (hk : 0 < k) (hx : x < 2 ^ w0)
    (hp_even : p % 2 = 0)
    (hper0 : HasMinPeriod (lstep k c0 w0) x p)
    (hdelta0 : orbitDelta k c0 w0 x p = true)
    (hkappa0 : orbitKappa k c0 w0 x p = true) :
    ∀ c, c % 2 ^ w0 = c0 % 2 ^ w0 → ∀ d : Nat,
      HasMinPeriod (lstep k c (w0 + d)) x (p * 2 ^ d) ∧
      orbitDelta k c (w0 + d) x (p * 2 ^ d) = true ∧
      orbitKappa k c (w0 + d) x (p * 2 ^ d) = true := by
  intro c hc d
  induction d with
  | zero =>
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    have hiter : ∀ j, iterFn (lstep k c w0) j x = iterFn (lstep k c0 w0) j x :=
      iterFn_lstep_mod_c k c c0 w0 x hc
    have hper : HasMinPeriod (lstep k c w0) x p := by
      refine ⟨hper0.1, ?_, ?_⟩
      · rw [hiter p]; exact hper0.2.1
      · intro j hj0 hjp; rw [hiter j]; exact hper0.2.2 j hj0 hjp
    have hkap : orbitKappa k c w0 x p = true := by
      rw [← hkappa0]; unfold orbitKappa
      apply xorSum_congr; intro j _
      rw [hiter j]; simp [carryBit, hc]
    have hdel : orbitDelta k c w0 x p = true := by
      rw [← hdelta0]; unfold orbitDelta
      apply xorSum_congr; intro j _
      rw [hiter j]; simp [deltaBit, carryBit, hc]
    exact ⟨hper, hdel, hkap⟩
  | succ d ih =>
    have hx_d : x < 2 ^ (w0 + d) :=
      Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))
    have hp_d : (p * 2 ^ d) % 2 = 0 := by
      rw [Nat.mul_mod, hp_even]; simp
    have hstep := cpmf_step k c (w0 + d) x (p * 2 ^ d) hk hx_d hp_d ih.1 ih.2.1 ih.2.2
    have hidx : w0 + (d + 1) = (w0 + d) + 1 := by omega
    have hlen : p * 2 ^ (d + 1) = 2 * (p * 2 ^ d) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, ← Nat.mul_assoc, Nat.mul_comm p 2, Nat.mul_assoc]
    rw [hidx, hlen]
    exact ⟨hstep.1, hstep.2.2, hstep.2.1⟩

/-- Helper: general projection `iter (lstep k c (w0 + d)) n x % 2^w0 = iter (lstep k c w0) n (x % 2^w0)`. -/
theorem iterFn_lstep_proj_add (k c w0 x : Nat) :
    ∀ d n, iterFn (lstep k c (w0 + d)) n x % 2 ^ w0 = iterFn (lstep k c w0) n (x % 2 ^ w0)
  | 0, n => by
    simp only [Nat.add_zero]
    induction n with
    | zero => rfl
    | succ n ih =>
      show lstep k c w0 (iterFn (lstep k c w0) n x) % 2 ^ w0 =
           lstep k c w0 (iterFn (lstep k c w0) n (x % 2 ^ w0))
      rw [Nat.mod_eq_of_lt (lstep_lt k c w0 _), ← lstep_mod_x, ih]
  | d + 1, n => by
    have hdvd : 2 ^ w0 ∣ 2 ^ (w0 + d) := Nat.pow_dvd_pow 2 (by omega)
    rw [show w0 + (d + 1) = (w0 + d) + 1 by omega]
    rw [← Nat.mod_mod_of_dvd (iterFn (lstep k c ((w0 + d) + 1)) n x) hdvd,
        iterFn_lstep_proj, iterFn_lstep_proj_add k c w0 (x % 2 ^ (w0 + d)) d n,
        Nat.mod_mod_of_dvd _ hdvd]

/-- Helper: periodicity modulo `p` for `iterFn`. -/
theorem iterFn_mod_period {f : Nat → Nat} {x p : Nat} (_hp : 0 < p) (hper : iterFn f p x = x) :
    ∀ n, iterFn f n x = iterFn f (n % p) x := by
  intro n
  have hmul : ∀ q, iterFn f (p * q) x = x := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [Nat.mul_succ, ← iterFn_add, ih, hper]
  have hdecomp : p * (n / p) + n % p = n := Nat.div_add_mod n p
  calc iterFn f n x = iterFn f (p * (n / p) + n % p) x := by rw [hdecomp]
    _ = iterFn f (n % p) (iterFn f (p * (n / p)) x) := (iterFn_add f x _ _).symm
    _ = iterFn f (n % p) x := by rw [hmul]

theorem checkBaseOrbit_sound {k c0 w0 x p : Nat} (h : checkBaseOrbit k c0 w0 x p = true) :
    x < 2 ^ w0 ∧ p % 2 = 0 ∧ HasMinPeriod (lstep k c0 w0) x p ∧
    orbitDelta k c0 w0 x p = true ∧ orbitKappa k c0 w0 x p = true := by
  simp only [checkBaseOrbit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
             List.mem_range, Bool.or_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hx, hp0⟩, hpe⟩, hfix⟩, hmin⟩, hdel⟩, hkap⟩
  refine ⟨hx, hpe, ⟨hp0, hfix, ?_⟩, hdel, hkap⟩
  intro j hj0 hjp
  rcases hmin j hjp with hjz | hne
  · omega
  · exact hne

/-- **THEOREM II.0b (CPMF Full Cycle-Spectrum Freezing Compiler)**:
    If a finite base-width certificate `certs` passes `checkBaseCert k c0 w0 certs = true`
    (verified by the Lean kernel!), then for ALL `c ≡ c0 (mod 2^w0)` and ALL `d : Nat`
    (width `w = w0 + d`), `lstep k c w` decomposes `{0, ..., 2^w - 1}` into **EXACTLY**
    the `certs.length` disjoint cycles of lengths `{r.2 * 2^d | r ∈ certs}`! -/
theorem cpmf_full_partition_lift (k c0 w0 : Nat) (hk : 0 < k) (certs : List (Nat × Nat))
    (hcert : checkBaseCert k c0 w0 certs = true) :
    ∀ c, c % 2 ^ w0 = c0 % 2 ^ w0 → ∀ d : Nat,
      let w := w0 + d
      let f := lstep k c w
      (∀ r ∈ certs, HasMinPeriod f r.1 (r.2 * 2 ^ d)) ∧
      (∀ r₁ ∈ certs, ∀ r₂ ∈ certs, r₁ ≠ r₂ → ∀ a b, iterFn f a r₁.1 ≠ iterFn f b r₂.1) ∧
      (∀ y < 2 ^ w, ∃ r ∈ certs, ∃ j < r.2 * 2 ^ d, iterFn f j r.1 = y) := by
  simp only [checkBaseCert, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
             List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨horb, hcov0⟩, hdisj0⟩
  intro c hc d
  -- First establish the lifted orbit properties for EVERY r ∈ certs and EVERY d
  have hlift : ∀ r ∈ certs, ∀ t,
      HasMinPeriod (lstep k c (w0 + t)) r.1 (r.2 * 2 ^ t) ∧
      orbitDelta k c (w0 + t) r.1 (r.2 * 2 ^ t) = true ∧
      orbitKappa k c (w0 + t) r.1 (r.2 * 2 ^ t) = true := by
    intro r hr t
    have hb := checkBaseOrbit_sound (horb r hr)
    exact cpmf_infinite_orbit_lift k c0 w0 r.1 r.2 hk hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 c hc t
  -- 1. Exact minimal period for every r ∈ certs
  have hpart1 : ∀ r ∈ certs, HasMinPeriod (lstep k c (w0 + d)) r.1 (r.2 * 2 ^ d) :=
    fun r hr => (hlift r hr d).1
  -- 2. Pairwise disjointness at width w0 + d (projected down to width w0!)
  have hpart2 : ∀ r₁ ∈ certs, ∀ r₂ ∈ certs, r₁ ≠ r₂ →
      ∀ a b, iterFn (lstep k c (w0 + d)) a r₁.1 ≠ iterFn (lstep k c (w0 + d)) b r₂.1 := by
    intro r₁ hr₁ r₂ hr₂ hne a b heq
    have hb₁ := checkBaseOrbit_sound (horb r₁ hr₁)
    have hb₂ := checkBaseOrbit_sound (horb r₂ hr₂)
    have hproj := congrArg (fun n => n % 2 ^ w0) heq
    rw [iterFn_lstep_proj_add, iterFn_lstep_proj_add,
        Nat.mod_eq_of_lt hb₁.1, Nat.mod_eq_of_lt hb₂.1,
        iterFn_lstep_mod_c k c c0 w0 r₁.1 hc a,
        iterFn_lstep_mod_c k c c0 w0 r₂.1 hc b] at hproj
    rw [iterFn_mod_period hb₁.2.2.1.1 hb₁.2.2.1.2.1 a,
        iterFn_mod_period hb₂.2.2.1.1 hb₂.2.2.1.2.1 b] at hproj
    rcases hdisj0 r₁ hr₁ r₂ hr₂ with heq_r | hdis
    · exact hne heq_r
    · exact hdis (a % r₁.2) (Nat.mod_lt a hb₁.2.2.1.1) (b % r₂.2) (Nat.mod_lt b hb₂.2.2.1.1) hproj
  -- 3. Complete coverage of {0, ..., 2^(w0 + d) - 1} by constructive induction on d!
  have hpart3 : ∀ t, ∀ y < 2 ^ (w0 + t),
      ∃ r ∈ certs, ∃ j < r.2 * 2 ^ t, iterFn (lstep k c (w0 + t)) j r.1 = y := by
    intro t
    induction t with
    | zero =>
      intro y hy
      simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one] at hy ⊢
      rcases hcov0 y hy with ⟨r, hr, j, hj, hhit⟩
      refine ⟨r, hr, j, hj, ?_⟩
      rw [iterFn_lstep_mod_c k c c0 w0 r.1 hc j]
      exact hhit
    | succ t iht =>
      intro y hy
      have hidx : w0 + (t + 1) = (w0 + t) + 1 := by omega
      rw [hidx] at hy ⊢
      have hymod_lt : y % 2 ^ (w0 + t) < 2 ^ (w0 + t) := Nat.mod_lt y (Nat.two_pow_pos _)
      rcases iht (y % 2 ^ (w0 + t)) hymod_lt with ⟨r, hr, j, hj, hhit⟩
      have hb := checkBaseOrbit_sound (horb r hr)
      have hr_lt : r.1 < 2 ^ (w0 + t) :=
        Nat.lt_of_lt_of_le hb.1 (Nat.pow_le_pow_right (by omega) (by omega))
      have hr_lt1 : r.1 < 2 ^ ((w0 + t) + 1) :=
        Nat.lt_of_lt_of_le hr_lt (Nat.pow_le_pow_right (by omega) (by omega))
      have hpe : (r.2 * 2 ^ t) % 2 = 0 := by rw [Nat.mul_mod, hb.2.1]; simp
      have hdoub := orbit_doubling_of_delta k c (w0 + t) r.1 (r.2 * 2 ^ t) hk hr_lt hpe
        (hlift r hr t).1 (hlift r hr t).2.1
      let u := iterFn (lstep k c ((w0 + t) + 1)) j r.1
      have hu_lt : u < 2 ^ ((w0 + t) + 1) := iterFn_lstep_lt k c ((w0 + t) + 1) r.1 hr_lt1 j
      have hu_mod : u % 2 ^ (w0 + t) = y % 2 ^ (w0 + t) := by
        show iterFn (lstep k c ((w0 + t) + 1)) j r.1 % 2 ^ (w0 + t) = y % 2 ^ (w0 + t)
        rw [iterFn_lstep_proj, Nat.mod_eq_of_lt hr_lt, hhit]
      have hlen : r.2 * 2 ^ (t + 1) = 2 * (r.2 * 2 ^ t) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ t) 2, ← Nat.mul_assoc, Nat.mul_comm r.2 2, Nat.mul_assoc]
      by_cases hbw : u.testBit (w0 + t) = y.testBit (w0 + t)
      · refine ⟨r, hr, j, by omega, ?_⟩
        exact (eq_or_eq_xor_two_pow hu_lt hy hu_mod).1 hbw
      · refine ⟨r, hr, j + r.2 * 2 ^ t, by omega, ?_⟩
        rw [hdoub.2 j]
        have heq_y : y = u ^^^ 2 ^ (w0 + t) :=
          (eq_or_eq_xor_two_pow hy hu_lt hu_mod.symm).2 (Ne.symm hbw)
        exact heq_y.symm
  exact ⟨hpart1, hpart2, hpart3 d⟩


theorem cert_mod32_9_valid : checkBaseCert 1 9 5 cert_mod32_9 = true := by decide

/-- **THEOREM II.1 (Complete Frozen 5-Cycle Spectrum for `c ≡ 9 mod 32`)**:
    For EVERY `c` with `c % 32 = 9` and EVERY width `w ≥ 5`, `L_{1,c}(x) = ((x ^^^ (x <<< 1)) + c) % 2^w`
    decomposes `{0, ..., 2^w - 1}` into **EXACTLY 5 disjoint cycles**:
    `x = 0` of exact length `2^(w - 1)`, and `x ∈ {2, 3, 6, 7}` each of exact length `2^(w - 3)`. -/
theorem lgray1_mod32_9_exact_five_cycles (c w : Nat) (hc : c % 32 = 9) (hw : 5 ≤ w) :
    let f := lstep 1 c w
    HasMinPeriod f 0 (2 ^ (w - 1)) ∧
    HasMinPeriod f 2 (2 ^ (w - 3)) ∧
    HasMinPeriod f 3 (2 ^ (w - 3)) ∧
    HasMinPeriod f 6 (2 ^ (w - 3)) ∧
    HasMinPeriod f 7 (2 ^ (w - 3)) ∧
    (∀ r₁ ∈ cert_mod32_9, ∀ r₂ ∈ cert_mod32_9, r₁ ≠ r₂ → ∀ a b, iterFn f a r₁.1 ≠ iterFn f b r₂.1) ∧
    (∀ y < 2 ^ w, ∃ r ∈ cert_mod32_9, ∃ j < r.2 * 2 ^ (w - 5), iterFn f j r.1 = y) := by
  have hmain := cpmf_full_partition_lift 1 9 5 (by omega) cert_mod32_9 cert_mod32_9_valid c
    (by simpa using hc) (w - 5)
  have hw_eq : 5 + (w - 5) = w := by omega
  rw [hw_eq] at hmain
  have h16 : 16 * 2 ^ (w - 5) = 2 ^ (w - 1) := by
    have : (16 : Nat) = 2 ^ 4 := rfl
    rw [this, ← Nat.pow_add]; congr 1; omega
  have h4 : 4 * 2 ^ (w - 5) = 2 ^ (w - 3) := by
    have : (4 : Nat) = 2 ^ 2 := rfl
    rw [this, ← Nat.pow_add]; congr 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, hmain.2.1, hmain.2.2⟩
  · rw [← h16]; exact hmain.1 (0, 16) (by simp [cert_mod32_9])
  · rw [← h4];  exact hmain.1 (2, 4)  (by simp [cert_mod32_9])
  · rw [← h4];  exact hmain.1 (3, 4)  (by simp [cert_mod32_9])
  · rw [← h4];  exact hmain.1 (6, 4)  (by simp [cert_mod32_9])
  · rw [← h4];  exact hmain.1 (7, 4)  (by simp [cert_mod32_9])


theorem cert_mod64_19_valid : checkBaseCert 1 19 6 cert_mod64_19 = true := by decide

/-- **THEOREM II.2 (Complete Frozen 7-Cycle Spectrum for `c ≡ 19 mod 64`)**:
    For EVERY `c` with `c % 64 = 19` and EVERY width `w ≥ 6`, `L_{1,c}` decomposes `{0, ..., 2^w - 1}`
    into **EXACTLY 7 disjoint cycles**: `x ∈ {0, 1, 2}` of exact length `2^(w - 2)`,
    and `x ∈ {4, 7, 12, 15}` of exact length `2^(w - 4)`. -/
theorem lgray1_mod64_19_exact_seven_cycles (c w : Nat) (hc : c % 64 = 19) (hw : 6 ≤ w) :
    let f := lstep 1 c w
    HasMinPeriod f 0 (2 ^ (w - 2)) ∧
    HasMinPeriod f 1 (2 ^ (w - 2)) ∧
    HasMinPeriod f 2 (2 ^ (w - 2)) ∧
    HasMinPeriod f 4 (2 ^ (w - 4)) ∧
    HasMinPeriod f 7 (2 ^ (w - 4)) ∧
    HasMinPeriod f 12 (2 ^ (w - 4)) ∧
    HasMinPeriod f 15 (2 ^ (w - 4)) ∧
    (∀ r₁ ∈ cert_mod64_19, ∀ r₂ ∈ cert_mod64_19, r₁ ≠ r₂ → ∀ a b, iterFn f a r₁.1 ≠ iterFn f b r₂.1) ∧
    (∀ y < 2 ^ w, ∃ r ∈ cert_mod64_19, ∃ j < r.2 * 2 ^ (w - 6), iterFn f j r.1 = y) := by
  have hmain := cpmf_full_partition_lift 1 19 6 (by omega) cert_mod64_19 cert_mod64_19_valid c
    (by simpa using hc) (w - 6)
  have hw_eq : 6 + (w - 6) = w := by omega
  rw [hw_eq] at hmain
  have h16 : 16 * 2 ^ (w - 6) = 2 ^ (w - 2) := by
    have : (16 : Nat) = 2 ^ 4 := rfl
    rw [this, ← Nat.pow_add]; congr 1; omega
  have h4 : 4 * 2 ^ (w - 6) = 2 ^ (w - 4) := by
    have : (4 : Nat) = 2 ^ 2 := rfl
    rw [this, ← Nat.pow_add]; congr 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hmain.2.1, hmain.2.2⟩
  · rw [← h16]; exact hmain.1 (0, 16)  (by simp [cert_mod64_19])
  · rw [← h16]; exact hmain.1 (1, 16)  (by simp [cert_mod64_19])
  · rw [← h16]; exact hmain.1 (2, 16)  (by simp [cert_mod64_19])
  · rw [← h4];  exact hmain.1 (4, 4)   (by simp [cert_mod64_19])
  · rw [← h4];  exact hmain.1 (7, 4)   (by simp [cert_mod64_19])
  · rw [← h4];  exact hmain.1 (12, 4)  (by simp [cert_mod64_19])
  · rw [← h4];  exact hmain.1 (15, 4)  (by simp [cert_mod64_19])


/-! ### Instantiation II.3: Universal Single-Cycle Law for `k ≥ 2`, Odd `c`, ALL `w ≥ 1` -/

/-- **THEOREM II.3 (Universal Single-Cycle Law for Left-Shift Gray + Increment)**:
    For EVERY shift `k ≥ 2`, EVERY odd increment `c` (`c % 2 = 1`), and EVERY width `w ≥ 1`,
    `L_{k,c}(x) = ((x ^^^ (x <<< k)) + c) % 2^w` is a **SINGLE FULL CYCLE of length `2^w`**
    covering every element of `{0, ..., 2^w - 1}`! -/
theorem lgray_ge2_odd_single_cycle (k c w : Nat) (hk : 2 ≤ k) (hc : c % 2 = 1) (hw : 1 ≤ w) :
    HasMinPeriod (lstep k c w) 0 (2 ^ w) ∧
    ∀ y < 2 ^ w, ∃ j < 2 ^ w, iterFn (lstep k c w) j 0 = y := by
  -- Verify the 1-bit base certificate [(0, 2)] parametrically for ALL k ≥ 2!
  have hl0 : lgray k 0 % 2 = 0 := by simp [lgray]
  have hl1 : lgray k 1 % 2 = 1 := by
    have hpow2 : (2 : Nat) = 2 ^ 1 := rfl
    rw [hpow2]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow, lgray, Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases hi : i < 1
    · have hi0 : i = 0 := by omega
      subst hi0
      have hnk : ¬ (k ≤ 0) := by omega
      simp [hnk]
    · simp [hi]
      exact testBit_lt_of_le (w := 1) (by omega : 1 < 2 ^ 1) (by omega)
  have hstep0 : lstep k 1 1 0 = 1 := by simp [lstep, hl0]
  have hstep1 : lstep k 1 1 1 = 0 := by simp [lstep, hl1]
  have hcert : checkBaseCert k 1 1 [(0, 2)] = true := by
    simp only [checkBaseCert, checkBaseOrbit, List.all_cons, List.all_nil, List.any_cons,
               List.any_nil, Bool.and_true, Bool.or_false, List.range_succ, List.range_zero,
               List.nil_append, List.cons_append]
    simp only [iterFn, hstep0, hstep1, orbitDelta, orbitKappa, xorSum, deltaBit, carryBit,
               shiftBit, hl0, hl1, show ¬ (k ≤ 1) by omega, ↓reduceIte]
    rfl
  have hmain := cpmf_full_partition_lift k 1 1 (by omega) [(0, 2)] hcert c (by simpa using hc) (w - 1)
  have hw_eq : 1 + (w - 1) = w := by omega
  have hlen : 2 * 2 ^ (w - 1) = 2 ^ w := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
    congr 1; omega
  rw [hw_eq] at hmain
  refine ⟨?_, ?_⟩
  · rw [← hlen]; exact hmain.1 (0, 2) (by simp)
  · intro y hy
    rcases hmain.2.2 y hy with ⟨r, hr, j, hj, hhit⟩
    simp only [List.mem_singleton] at hr
    subst hr
    rw [hlen] at hj
    exact ⟨j, hj, hhit⟩


/-! ## Section 3: Kernel-Checked Non-Vacuity Witnesses, Sharpness Counterexamples & Axiom Audit -/

/-- Non-vacuity witness for Theorem I.1: `k = 1, L = 2, c = 3, m = 1, w = 5` has 2 solutions. -/
example : countBelow (fun x => decide (((x ^^^ (x >>> 1)) + 3) % 2 ^ 5 = x ^^^ 1)) (2 ^ 5) = 2 :=
  grayRight_twisted_exact_count 1 2 3 1 5 (by omega) (by omega) (by omega) (by omega)

/-- Non-vacuity witness for Theorem I.1a: `k = 2, L = 2, c = 3, w = 7` has 4 fixed points. -/
example : countBelow (fun x => decide (((x ^^^ (x >>> 2)) + 3) % 2 ^ 7 = x)) (2 ^ 7) = 4 :=
  grayRight_fixedPoint_exact_count 2 2 3 7 (by omega) (by omega) (by omega)

/-- Non-vacuity witness for Corollary I.1b: explicit `ℕ`-solution `(26 ^^^ (26 >>> 1)) + 3 = 26`. -/
example : (26 ^^^ (26 >>> 1)) + 3 = 26 ∧ (7 ^^^ (7 >>> 1)) + 3 = 7 := by decide

/-- Non-vacuity & sharpness witness for Theorem I.2: `k = 1, c = 3, w = 4` has `< 2` fixed points (exact count = 1). -/
example : countBelow (fun x => decide (((x ^^^ (x >>> 1)) + 3) % 2 ^ 4 = x)) (2 ^ 4) = 1 := by decide

/-- Non-vacuity witness for Theorem I.3: `k = 1, d = 6, w = 5` has 0 fixed points for `-6`. -/
example : countBelow (fun x => decide ((x ^^^ (x >>> 1)) = (x + 6) % 2 ^ 5)) (2 ^ 5) = 0 :=
  grayRight_sub_complete_annihilation 1 5 (by omega) (by omega)

/-- Non-vacuity witness for Theorem I.4: `k = 2, d = 1, w = 4` has `2^2 - 1 = 3` fixed points. -/
example : countBelow (fun x => decide ((x ^^^ (x >>> 2)) = (x + 1) % 2 ^ 4)) (2 ^ 4) = 3 :=
  grayRight_sub_one_exact_count 2 4 (by omega) (by omega)

/-- Sharpness counterexample for Theorem II.3 (shift `k = 1` breaks single-cycle at `w = 2`):
    `L_{1,1}` at `w = 2` has period `2 < 4` at `x = 0`! -/
theorem lgray1_not_single_cycle : HasMinPeriod (lstep 1 1 2) 0 2 := by
  refine ⟨by omega, by decide, ?_⟩
  intro j hj0 hj2
  have : j = 1 := by omega
  subst this; decide

/-- Sharpness counterexample for Theorem II.3 (even `c = 2` breaks single-cycle at `w = 1`):
    `L_{2,2}` at `w = 1` fixes `0` (period `1 < 2`)! -/
theorem lgray_even_not_single_cycle : HasMinPeriod (lstep 2 2 1) 0 1 := by
  refine ⟨by omega, by decide, ?_⟩
  intro j hj0 hj1; omega

/-- Sharpness counterexample for Theorem II.1 (`c = 25 ≡ 9 mod 16`, NOT `mod 32`, breaks 5-cycle freezing!):
    At `w = 6`, `x = 2` has period `4 ≠ 2^(6 - 3) = 8`! -/
theorem lgray1_mod16_9_breaks_at_25 :
    25 % 16 = 9 ∧ 25 % 32 ≠ 9 ∧ HasMinPeriod (lstep 1 25 6) 2 4 := by
  refine ⟨by decide, by decide, by omega, by decide, ?_⟩
  intro j hj0 hj4
  have : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl <;> decide

/-- Non-vacuity witness for Theorem II.1: `c = 41 = 9 + 32` at `w = 8` has exact period `128` at `0` and `32` at `2`. -/
example : HasMinPeriod (lstep 1 41 8) 0 128 ∧ HasMinPeriod (lstep 1 41 8) 2 32 :=
  let h := lgray1_mod32_9_exact_five_cycles 41 8 (by decide) (by omega)
  ⟨h.1, h.2.1⟩

/-- Non-vacuity witness for Theorem II.2: `c = 83 = 19 + 64` at `w = 8` has exact period `64` at `0` and `16` at `4`. -/
example : HasMinPeriod (lstep 1 83 8) 0 64 ∧ HasMinPeriod (lstep 1 83 8) 4 16 :=
  let h := lgray1_mod64_19_exact_seven_cycles 83 8 (by decide) (by omega)
  ⟨h.1, h.2.2.2.1⟩

/-- Non-vacuity witness for Theorem II.3: `k = 2, c = 5, w = 10` is a single cycle of length `1024`. -/
example : HasMinPeriod (lstep 2 5 10) 0 1024 :=
  (lgray_ge2_odd_single_cycle 2 5 10 (by omega) (by decide) (by omega)).1

end DualGrayCarry

-- Axiom Audit for ALL main theorems (must contain ONLY standard Lean axioms; zero sorryAx!)

