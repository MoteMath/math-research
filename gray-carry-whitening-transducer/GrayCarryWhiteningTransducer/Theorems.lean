/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrayCarryWhiteningTransducer.Defs

/-!
# Theorems (`gray-carry-whitening-transducer`)

Full proofs of the headline infinite theorems of Gray-code carry whitening via balanced-fiber transducer lifts.
-/

namespace GrayTransducerEngine


/-! ===========================================================================
    PART 0: Elementary Arithmetic & Bitwise Helpers
    =========================================================================== -/

theorem testBit_zero_eq_mod2 (n : Nat) : n.testBit 0 = (n % 2 == 1) := by
  simp [Nat.testBit, Nat.shiftRight_zero]

theorem testBit_succ_div2 (n i : Nat) : n.testBit (i + 1) = (n / 2).testBit i :=
  Nat.testBit_succ n i

theorem testBit_two_mul_add_bool (q : Nat) (b : Bool) :
    (2 * q + b.toNat).testBit 0 = b := by
  rw [testBit_zero_eq_mod2]
  cases b <;> simp <;> omega

theorem two_mul_add_bool_div2 (q : Nat) (b : Bool) :
    (2 * q + b.toNat) / 2 = q := by
  cases b <;> simp <;> omega

theorem nat_div2_decomp (n : Nat) : 2 * (n / 2) + (n.testBit 0).toNat = n := by
  rw [testBit_zero_eq_mod2]
  cases h : (n % 2 == 1) <;> simp_all <;> omega

theorem testBit_two_mul_add_bool_succ (q : Nat) (b : Bool) (i : Nat) :
    (2 * q + b.toNat).testBit (i + 1) = q.testBit i := by
  rw [testBit_succ_div2, two_mul_add_bool_div2]

theorem testBit_eq_false_of_lt_pow {n w i : Nat} (hn : n < 2 ^ w) (hi : w ≤ i) :
    n.testBit i = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hlt : n < 2 ^ i := Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) hi)
  rw [Nat.div_eq_of_lt hlt]
  rfl

theorem eq_of_testBit_lt {a b w : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : ∀ i, i < w → a.testBit i = b.testBit i) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · exact h i hi
  · rw [testBit_eq_false_of_lt_pow ha (by omega), testBit_eq_false_of_lt_pow hb (by omega)]

theorem xor_lt_two_pow {a b w : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (a ^^^ b) < 2 ^ w :=
  Nat.xor_lt_two_pow ha hb

theorem testBit_mod_two_pow (n w i : Nat) :
    (n % 2 ^ w).testBit i = (decide (i < w) && n.testBit i) :=
  Nat.testBit_mod_two_pow n w i

theorem testBit_pow_two_add {w a i : Nat} (ha : a < 2 ^ w) (hi : i < w) :
    (2 ^ w + a).testBit i = a.testBit i := by
  have h1 : (2 ^ w + a) % 2 ^ w = a := by
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt ha]
  have h2 := congrArg (fun x => x.testBit i) h1
  rw [testBit_mod_two_pow] at h2
  simp [hi] at h2
  exact h2

theorem testBit_pow_two_add_self {w a : Nat} (ha : a < 2 ^ w) :
    (2 ^ w + a).testBit w = true := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ w + a) / 2 ^ w = 1 := by
    rw [Nat.add_div_left _ (Nat.two_pow_pos w), Nat.div_eq_of_lt ha]
  rw [hdiv]
  rfl

theorem testBit_two_pow_eq (w i : Nat) : (2 ^ w).testBit i = decide (w = i) :=
  Nat.testBit_two_pow

/-! ===========================================================================
    PART 1: General Finite-State Binary Transducer Lifting Engine (Reusable)
    =========================================================================== -/

theorem stateAt_succ_shift {S Out : Type} (M : BinTransducer S Out) (s0 : S) (a b : Nat) :
    ∀ i, stateAt M s0 a b (i + 1) =
      stateAt M (M.step s0 (a.testBit 0) (b.testBit 0)) (a / 2) (b / 2) i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    change M.step (stateAt M s0 a b (i + 1)) (a.testBit (i + 1)) (b.testBit (i + 1)) =
      M.step (stateAt M (M.step s0 (a.testBit 0) (b.testBit 0)) (a / 2) (b / 2) i)
        ((a / 2).testBit i) ((b / 2).testBit i)
    rw [ih, testBit_succ_div2, testBit_succ_div2]

theorem outAt_succ_shift {S Out : Type} (M : BinTransducer S Out) (s0 : S) (a b i : Nat) :
    outAt M s0 a b (i + 1) =
      outAt M (M.step s0 (a.testBit 0) (b.testBit 0)) (a / 2) (b / 2) i := by
  simp only [outAt, stateAt_succ_shift, testBit_succ_div2]

/-- META-THEOREM 1 (Finite State-Invariant Lifter):
    A finite inductive state invariant `I` certifying output property `P` lifts to
    ALL natural numbers `a, b : Nat` and ALL bit positions `i : Nat`. -/
theorem transducer_invariant_lift {S Out : Type} (M : BinTransducer S Out)
    (I : S → Prop) (P : Out → Prop) (s0 : S)
    (h0 : I s0)
    (hstep : ∀ s x y, I s → I (M.step s x y))
    (hout : ∀ s x y, I s → P (M.out s x y)) :
    ∀ a b i, P (outAt M s0 a b i) := by
  intro a b i
  have hI : ∀ k, I (stateAt M s0 a b k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact hstep _ _ _ ih
  exact hout _ _ _ (hI i)

/-- META-THEOREM 2 (Finite State-Quotient Bisimulation Lifter):
    If `π : S1 → S2` intertwines transitions and outputs of `M1` and `M2`,
    their infinite bit-streams agree identically for ALL `a, b, i : Nat`. -/
theorem transducer_quotient_bisim {S1 S2 Out : Type}
    (M1 : BinTransducer S1 Out) (M2 : BinTransducer S2 Out)
    (π : S1 → S2)
    (hstep : ∀ s x y, π (M1.step s x y) = M2.step (π s) x y)
    (hout : ∀ s x y, M1.out s x y = M2.out (π s) x y) :
    ∀ s0 a b i, outAt M1 s0 a b i = outAt M2 (π s0) a b i := by
  intro s0 a b i
  have hst : ∀ k, π (stateAt M1 s0 a b k) = stateAt M2 (π s0) a b k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change π (M1.step (stateAt M1 s0 a b k) (a.testBit k) (b.testBit k)) =
        M2.step (stateAt M2 (π s0) a b k) (a.testBit k) (b.testBit k)
      rw [hstep, ih]
  simp only [outAt]
  rw [hout, hst]

theorem runPair_lt {S : Type} (M : BinTransducer S (Bool × Bool)) :
    ∀ w s0 a b, (runPair M s0 w a b).1 < 2 ^ w ∧ (runPair M s0 w a b).2 < 2 ^ w
  | 0, _, _, _ => by simp [runPair]
  | w + 1, s0, a, b => by
    simp only [runPair]
    have ih := runPair_lt M w (M.step s0 (a.testBit 0) (b.testBit 0)) (a / 2) (b / 2)
    have h1 : (M.out s0 (a.testBit 0) (b.testBit 0)).1.toNat ≤ 1 := by
      cases (M.out s0 (a.testBit 0) (b.testBit 0)).1 <;> decide
    have h2 : (M.out s0 (a.testBit 0) (b.testBit 0)).2.toNat ≤ 1 := by
      cases (M.out s0 (a.testBit 0) (b.testBit 0)).2 <;> decide
    rw [Nat.pow_succ]
    omega

theorem runPair_testBit {S : Type} (M : BinTransducer S (Bool × Bool)) :
    ∀ w s0 a b i, i < w →
      (runPair M s0 w a b).1.testBit i = (outAt M s0 a b i).1 ∧
      (runPair M s0 w a b).2.testBit i = (outAt M s0 a b i).2
  | 0, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | w + 1, s0, a, b, 0, _ => by
    simp only [runPair, outAt, stateAt]
    exact ⟨testBit_two_mul_add_bool _ _, testBit_two_mul_add_bool _ _⟩
  | w + 1, s0, a, b, i + 1, hi => by
    simp only [runPair, testBit_two_mul_add_bool_succ, outAt_succ_shift]
    exact runPair_testBit M w (M.step s0 (a.testBit 0) (b.testBit 0)) (a / 2) (b / 2) i (by omega)

/-- META-THEOREM 3 (Finite Local-Slice Bijection Lifter):
    If `M` and `Minv` are per-state single-bit slice inverses with synchronized
    next-states, then `runPair M s0 w` is an EXACT BIJECTION on `[0, 2^w)^2`
    for ALL bit-widths `w : Nat` and ALL initial states `s0 : S`, with explicit
    inverse `runPair Minv s0 w`. -/
theorem transducer_bijection_lift {S : Type}
    (M Minv : BinTransducer S (Bool × Bool))
    (hleft : ∀ s x y, Minv.out s (M.out s x y).1 (M.out s x y).2 = (x, y))
    (hright : ∀ s u v, M.out s (Minv.out s u v).1 (Minv.out s u v).2 = (u, v))
    (hsyncL : ∀ s x y, Minv.step s (M.out s x y).1 (M.out s x y).2 = M.step s x y)
    (hsyncR : ∀ s u v, M.step s (Minv.out s u v).1 (Minv.out s u v).2 = Minv.step s u v) :
    ∀ w s0,
      (∀ a b, a < 2 ^ w → b < 2 ^ w →
        let p := runPair M s0 w a b
        runPair Minv s0 w p.1 p.2 = (a, b)) ∧
      (∀ u v, u < 2 ^ w → v < 2 ^ w →
        let q := runPair Minv s0 w u v
        runPair M s0 w q.1 q.2 = (u, v)) := by
  intro w
  induction w with
  | zero =>
    intro s0
    constructor <;> (intro a b ha hb; simp [runPair]; omega)
  | succ w ih =>
    intro s0
    constructor
    · intro a b ha hb
      simp only [runPair, testBit_two_mul_add_bool, two_mul_add_bool_div2]
      rw [hleft, hsyncL]
      have ha' : a / 2 < 2 ^ w := by rw [Nat.pow_succ] at ha; omega
      have hb' : b / 2 < 2 ^ w := by rw [Nat.pow_succ] at hb; omega
      have hrec := (ih (M.step s0 (a.testBit 0) (b.testBit 0))).1 (a / 2) (b / 2) ha' hb'
      simp only [] at hrec
      rw [hrec]
      exact Prod.ext (nat_div2_decomp a) (nat_div2_decomp b)
    · intro u v hu hv
      simp only [runPair, testBit_two_mul_add_bool, two_mul_add_bool_div2]
      rw [hright, hsyncR]
      have hu' : u / 2 < 2 ^ w := by rw [Nat.pow_succ] at hu; omega
      have hv' : v / 2 < 2 ^ w := by rw [Nat.pow_succ] at hv; omega
      have hrec := (ih (Minv.step s0 (u.testBit 0) (v.testBit 0))).2 (u / 2) (v / 2) hu' hv'
      simp only [] at hrec
      rw [hrec]
      exact Prod.ext (nat_div2_decomp u) (nat_div2_decomp v)

/-! Exact finite sums and exact pair counting on `[0, 2^w) × [0, 2^w)`. -/

theorem sumNat_congr {n : Nat} {f g : Nat → Nat} (h : ∀ k, k < n → f k = g k) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat]
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

theorem sumNat_zero (n : Nat) : sumNat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumNat, ih]

theorem sumNat_add_fn (n : Nat) (f g : Nat → Nat) :
    sumNat n (fun k => f k + g k) = sumNat n f + sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, ih]; omega

theorem sumNat_split (m n : Nat) (f : Nat → Nat) :
    sumNat (m + n) f = sumNat m f + sumNat n (fun k => f (m + k)) := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih =>
    rw [Nat.add_succ]
    simp only [sumNat]
    rw [ih]
    omega

theorem sumNat_two_mul (n : Nat) (f : Nat → Nat) :
    sumNat (2 * n) f = sumNat n (fun k => f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1]
    simp only [sumNat]
    rw [ih]
    omega

theorem countPairs_congr {w : Nat} {P Q : Nat → Nat → Bool}
    (h : ∀ a b, a < 2 ^ w → b < 2 ^ w → P a b = Q a b) :
    countPairs w P = countPairs w Q := by
  unfold countPairs
  apply sumNat_congr
  intro a ha
  apply sumNat_congr
  intro b hb
  rw [h a b ha hb]

theorem countPairs_false (w : Nat) : countPairs w (fun _ _ => false) = 0 := by
  unfold countPairs
  simp [sumNat_zero]

theorem countPairs_succ (w : Nat) (P : Nat → Nat → Bool) :
    countPairs (w + 1) P =
      countPairs w (fun a b => P (2 * a)     (2 * b)) +
      countPairs w (fun a b => P (2 * a)     (2 * b + 1)) +
      countPairs w (fun a b => P (2 * a + 1) (2 * b)) +
      countPairs w (fun a b => P (2 * a + 1) (2 * b + 1)) := by
  unfold countPairs
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, sumNat_two_mul]
  have inner : ∀ a,
      sumNat (2 * 2 ^ w) (fun b => if P a b then 1 else 0) =
      sumNat (2 ^ w) (fun b => if P a (2 * b) then 1 else 0) +
      sumNat (2 ^ w) (fun b => if P a (2 * b + 1) then 1 else 0) := by
    intro a
    rw [sumNat_two_mul, sumNat_add_fn]
  simp only [inner, sumNat_add_fn]
  omega

/-- META-THEOREM 4 (Finite Balanced-Fiber Whitening Lifter):
    If `M` has state-independent single-step fiber multiplicities `sliceCount M s o = mult o`
    for ALL states `s` and outputs `o`, then ALL state-carry correlations cancel in the
    `w`-bit fiber counts: for EVERY `w : Nat`, EVERY initial state `s0`, and EVERY target
    output sequence `target` of length `w`, the exact cardinality of its fiber in `[0, 2^w)^2`
    is the pure product `∏_{o ∈ target} mult(o)`. -/
theorem transducer_balanced_fiber_lift {S Out : Type} [DecidableEq Out]
    (M : BinTransducer S Out) (mult : Out → Nat)
    (hbal : ∀ s o, sliceCount M s o = mult o) :
    ∀ (w : Nat) (s0 : S) (target : List Out), target.length = w →
      countPairs w (fun a b => decide (runList M s0 w a b = target)) =
        target.foldr (fun o acc => mult o * acc) 1 := by
  intro w
  induction w with
  | zero =>
    intro s0 target hlen
    cases target with
    | nil => simp [countPairs, sumNat, runList]
    | cons _ _ => simp at hlen
  | succ w ih =>
    intro s0 target hlen
    cases target with
    | nil => simp at hlen
    | cons o0 rest =>
      have hrest : rest.length = w := by simp at hlen; exact hlen
      rw [countPairs_succ]
      have branch : ∀ (x0 y0 : Bool),
          countPairs w (fun a b =>
            decide (runList M s0 (w + 1) (2 * a + x0.toNat) (2 * b + y0.toNat) = o0 :: rest)) =
          (if M.out s0 x0 y0 = o0 then 1 else 0) * rest.foldr (fun o acc => mult o * acc) 1 := by
        intro x0 y0
        have hstep_eq : ∀ a b,
            decide (runList M s0 (w + 1) (2 * a + x0.toNat) (2 * b + y0.toNat) = o0 :: rest) =
            (decide (M.out s0 x0 y0 = o0) &&
             decide (runList M (M.step s0 x0 y0) w a b = rest)) := by
          intro a b
          simp only [runList, testBit_two_mul_add_bool, two_mul_add_bool_div2, List.cons.injEq]
          by_cases h1 : M.out s0 x0 y0 = o0 <;> simp [h1]
        rw [countPairs_congr (fun a b _ _ => hstep_eq a b)]
        by_cases h1 : M.out s0 x0 y0 = o0
        · simp only [h1, decide_true, Bool.true_and, ↓reduceIte, Nat.one_mul]
          exact ih (M.step s0 x0 y0) rest hrest
        · simp only [h1, decide_false, Bool.false_and, ↓reduceIte, Nat.zero_mul]
          exact countPairs_false w
      have b00 := branch false false
      have b01 := branch false true
      have b10 := branch true false
      have b11 := branch true true
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at b00 b01 b10 b11
      rw [b00, b01, b10, b11]
      let R := rest.foldr (fun o acc => mult o * acc) 1
      change (if M.out s0 false false = o0 then 1 else 0) * R +
             (if M.out s0 false true  = o0 then 1 else 0) * R +
             (if M.out s0 true  false = o0 then 1 else 0) * R +
             (if M.out s0 true  true  = o0 then 1 else 0) * R =
             mult o0 * R
      have hcomb :
          (if M.out s0 false false = o0 then 1 else 0) * R +
          (if M.out s0 false true  = o0 then 1 else 0) * R +
          (if M.out s0 true  false = o0 then 1 else 0) * R +
          (if M.out s0 true  true  = o0 then 1 else 0) * R =
          sliceCount M s0 o0 * R := by
        unfold sliceCount
        rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
      rw [hcomb, hbal s0 o0]

/-! ===========================================================================
    PART 2: Pure-Silicon Gray-Code Arithmetic & Carry/Borrow Semantic Bridge
    =========================================================================== -/

theorem grayInvAux_eq_of_le : ∀ f1 f2 x, x ≤ f1 → x ≤ f2 →
    grayInvAux f1 x = grayInvAux f2 x
  | 0, f2, x, h1, _ => by
    have hx : x = 0 := by omega
    subst hx; cases f2 <;> rfl
  | f1 + 1, 0, x, _, h2 => by
    have hx : x = 0 := by omega
    subst hx; rfl
  | _ + 1, _ + 1, 0, _, _ => rfl
  | f1 + 1, f2 + 1, x + 1, h1, h2 => by
    simp only [grayInvAux]
    congr 1
    have hshr : (x + 1) >>> 1 ≤ x := by rw [Nat.shiftRight_eq_div_pow]; omega
    exact grayInvAux_eq_of_le f1 f2 ((x + 1) >>> 1) (by omega) (by omega)

theorem grayInv_eq (x : Nat) :
    grayInv x = if x = 0 then 0 else x ^^^ grayInv (x >>> 1) := by
  cases x with
  | zero => rfl
  | succ k =>
    simp only [grayInv, grayInvAux, Nat.succ_ne_zero, ↓reduceIte]
    congr 1
    have hshr : (k + 1) >>> 1 ≤ k := by rw [Nat.shiftRight_eq_div_pow]; omega
    exact grayInvAux_eq_of_le k ((k + 1) >>> 1) ((k + 1) >>> 1) hshr (Nat.le_refl _)

theorem parityAux_eq_of_le : ∀ f1 f2 x, x ≤ f1 → x ≤ f2 →
    parityAux f1 x = parityAux f2 x
  | 0, f2, x, h1, _ => by
    have hx : x = 0 := by omega
    subst hx; cases f2 <;> rfl
  | f1 + 1, 0, x, _, h2 => by
    have hx : x = 0 := by omega
    subst hx; rfl
  | _ + 1, _ + 1, 0, _, _ => rfl
  | f1 + 1, f2 + 1, x + 1, h1, h2 => by
    simp only [parityAux]
    congr 1
    have hshr : (x + 1) >>> 1 ≤ x := by rw [Nat.shiftRight_eq_div_pow]; omega
    exact parityAux_eq_of_le f1 f2 ((x + 1) >>> 1) (by omega) (by omega)

theorem parity_eq (x : Nat) :
    parity x = if x = 0 then false else Bool.xor (x.testBit 0) (parity (x >>> 1)) := by
  cases x with
  | zero => rfl
  | succ k =>
    simp only [parity, parityAux, Nat.succ_ne_zero, ↓reduceIte]
    congr 1
    have hshr : (k + 1) >>> 1 ≤ k := by rw [Nat.shiftRight_eq_div_pow]; omega
    exact parityAux_eq_of_le k ((k + 1) >>> 1) ((k + 1) >>> 1) hshr (Nat.le_refl _)

theorem popcountAux_eq_of_le : ∀ f1 f2 x, x ≤ f1 → x ≤ f2 →
    popcountAux f1 x = popcountAux f2 x
  | 0, f2, x, h1, _ => by
    have hx : x = 0 := by omega
    subst hx; cases f2 <;> rfl
  | f1 + 1, 0, x, _, h2 => by
    have hx : x = 0 := by omega
    subst hx; rfl
  | _ + 1, _ + 1, 0, _, _ => rfl
  | f1 + 1, f2 + 1, x + 1, h1, h2 => by
    simp only [popcountAux]
    congr 1
    have hdiv : (x + 1) / 2 ≤ x := by omega
    exact popcountAux_eq_of_le f1 f2 ((x + 1) / 2) (by omega) (by omega)

theorem popcount_eq (x : Nat) :
    popcount x = if x = 0 then 0 else (x % 2) + popcount (x / 2) := by
  cases x with
  | zero => rfl
  | succ k =>
    simp only [popcount, popcountAux, Nat.succ_ne_zero, ↓reduceIte]
    congr 1
    have hdiv : (k + 1) / 2 ≤ k := by omega
    exact popcountAux_eq_of_le k ((k + 1) / 2) ((k + 1) / 2) hdiv (Nat.le_refl _)

theorem testBit_gray (n i : Nat) :
    (gray n).testBit i = Bool.xor (n.testBit i) (n.testBit (i + 1)) := by
  simp [gray, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_comm]

theorem gray_xor (a b : Nat) : gray (a ^^^ b) = gray a ^^^ gray b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [testBit_gray, Nat.testBit_xor]
  cases a.testBit i <;> cases a.testBit (i + 1) <;>
    cases b.testBit i <;> cases b.testBit (i + 1) <;> rfl

theorem gray_shiftRight (n : Nat) : gray (n >>> 1) = (gray n) >>> 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [testBit_gray, Nat.testBit_shiftRight, Nat.add_assoc]

theorem grayInv_shiftRight (x : Nat) : grayInv x >>> 1 = grayInv (x >>> 1) := by
  refine Nat.strongRecOn (motive := fun x => grayInv x >>> 1 = grayInv (x >>> 1)) x ?_
  intro x ih
  by_cases hx : x = 0
  · subst hx; rfl
  · rw [grayInv_eq x]; simp only [hx, ↓reduceIte]
    have hlt : x >>> 1 < x := by rw [Nat.shiftRight_eq_div_pow]; omega
    have h1 : (x ^^^ grayInv (x >>> 1)) >>> 1 = (x >>> 1) ^^^ (grayInv (x >>> 1) >>> 1) := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp [Nat.testBit_shiftRight, Nat.testBit_xor]
    rw [h1, ih (x >>> 1) hlt]
    by_cases hx1 : x >>> 1 = 0
    · rw [hx1]; rfl
    · rw [grayInv_eq (x >>> 1)]; simp only [hx1, ↓reduceIte]

theorem gray_grayInv (x : Nat) : gray (grayInv x) = x := by
  by_cases hx : x = 0
  · subst hx; rfl
  · unfold gray
    rw [grayInv_shiftRight]
    have hx_eq : grayInv x = x ^^^ grayInv (x >>> 1) := by
      rw [grayInv_eq]; simp only [hx, ↓reduceIte]
    rw [hx_eq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem grayInv_gray (n : Nat) : grayInv (gray n) = n := by
  refine Nat.strongRecOn (motive := fun n => grayInv (gray n) = n) n ?_
  intro n ih
  by_cases hn : n = 0
  · subst hn; rfl
  · have hlt : n >>> 1 < n := by rw [Nat.shiftRight_eq_div_pow]; omega
    have hgne : gray n ≠ 0 := by
      intro h0
      have heq : n = n >>> 1 := by
        apply Nat.eq_of_testBit_eq
        intro i
        have hb := congrArg (fun z => z.testBit i) h0
        simp [gray, Nat.testBit_xor] at hb
        cases hn1 : n.testBit i <;> cases hn2 : (n >>> 1).testBit i <;> simp_all
      omega
    rw [grayInv_eq (gray n)]; simp only [hgne, ↓reduceIte]
    rw [← gray_shiftRight, ih (n >>> 1) hlt]
    unfold gray
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem gray_lt_two_pow {n w : Nat} (hn : n < 2 ^ w) : gray n < 2 ^ w := by
  unfold gray
  apply xor_lt_two_pow hn
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem grayInv_lt_two_pow {x w : Nat} (hx : x < 2 ^ w) : grayInv x < 2 ^ w := by
  refine Nat.strongRecOn (motive := fun x => x < 2 ^ w → grayInv x < 2 ^ w) x ?_ hx
  intro x ih hx
  by_cases h0 : x = 0
  · subst h0; exact Nat.two_pow_pos w
  · rw [grayInv_eq x]; simp only [h0, ↓reduceIte]
    have hlt : x >>> 1 < x := by rw [Nat.shiftRight_eq_div_pow]; omega
    exact xor_lt_two_pow hx (ih (x >>> 1) hlt (Nat.lt_trans hlt hx))

theorem testBit_grayInv_succ (x i : Nat) :
    (grayInv x).testBit (i + 1) = Bool.xor ((grayInv x).testBit i) (x.testBit i) := by
  have h := testBit_gray (grayInv x) i
  rw [gray_grayInv] at h
  cases h1 : (grayInv x).testBit i <;> cases h2 : (grayInv x).testBit (i + 1) <;>
    cases h3 : x.testBit i <;> simp_all

theorem testBit_grayInv_zero (x : Nat) : (grayInv x).testBit 0 = parity x := by
  refine Nat.strongRecOn (motive := fun x => (grayInv x).testBit 0 = parity x) x ?_
  intro x ih
  by_cases hx : x = 0
  · subst hx; rfl
  · rw [grayInv_eq x, parity_eq x]; simp only [hx, ↓reduceIte]
    rw [Nat.testBit_xor]
    have hlt : x >>> 1 < x := by rw [Nat.shiftRight_eq_div_pow]; omega
    rw [ih (x >>> 1) hlt]

theorem parity_gray (n : Nat) : parity (gray n) = n.testBit 0 := by
  rw [← testBit_grayInv_zero, grayInv_gray]

theorem parity_xor (a b : Nat) : parity (a ^^^ b) = Bool.xor (parity a) (parity b) := by
  rw [← testBit_grayInv_zero, ← testBit_grayInv_zero, ← testBit_grayInv_zero]
  have hgi : grayInv (a ^^^ b) = grayInv a ^^^ grayInv b := by
    rw [← grayInv_gray (grayInv a ^^^ grayInv b), gray_xor, gray_grayInv, gray_grayInv]
  rw [hgi, Nat.testBit_xor]

theorem popcount_two_mul_add_bool (q : Nat) (b : Bool) :
    popcount (2 * q + b.toNat) = b.toNat + popcount q := by
  by_cases h0 : 2 * q + b.toNat = 0
  · have hq : q = 0 := by cases b <;> simp at h0 <;> omega
    have hb : b = false := by cases b <;> simp at h0 <;> rfl
    subst hq; subst hb; rfl
  · rw [popcount_eq]; simp only [h0, ↓reduceIte]
    rw [two_mul_add_bool_div2]
    cases b <;> simp [Nat.add_mod]

theorem popcount_le_width : ∀ w z, z < 2 ^ w → popcount z ≤ w
  | 0, z, hz => by
    have : z = 0 := by omega
    subst this; decide
  | w + 1, z, hz => by
    have hq : z / 2 < 2 ^ w := by rw [Nat.pow_succ] at hz; omega
    have ih := popcount_le_width w (z / 2) hq
    rw [← nat_div2_decomp z, popcount_two_mul_add_bool]
    cases z.testBit 0 <;> simp <;> omega

/-- Gray-Code Doubling & Shift Law:
    `G(2n + b) = (G(n) <<< 1) ^^^ (parity(G(n)) ^^ b)` for all `n : Nat, b : Bool`. -/
theorem gray_double_add_bit (n : Nat) (b : Bool) :
    gray (2 * n + b.toNat) = ((gray n) <<< 1) ^^^ (Bool.xor (parity (gray n)) b).toNat := by
  rw [parity_gray]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_gray, Nat.testBit_xor, Nat.testBit_shiftLeft]
  cases i with
  | zero =>
    rw [testBit_two_mul_add_bool, testBit_two_mul_add_bool_succ]
    simp only [Nat.not_le_of_lt (Nat.zero_lt_one), decide_false, Bool.false_and, Bool.false_xor]
    cases n.testBit 0 <;> cases b <;> decide
  | succ j =>
    have hbit : ((Bool.xor (n.testBit 0) b).toNat).testBit (j + 1) = false := by
      cases Bool.xor (n.testBit 0) b <;> simp [testBit_succ_div2]
    rw [hbit, testBit_two_mul_add_bool_succ, testBit_two_mul_add_bool_succ]
    simp [testBit_gray]

/-- Pure Gray-Coordinate Doubling Law: `G(2 * G⁻¹(x)) = (x <<< 1) ^^^ (parity x)`. -/
theorem grayDouble_eq (x : Nat) : grayDouble x = (x <<< 1) ^^^ (parity x).toNat := by
  unfold grayDouble
  have h := gray_double_add_bit (grayInv x) false
  simp only [Bool.toNat_false, Nat.add_zero, gray_grayInv, Bool.xor_false] at h
  exact h

/-! Dyadic Sum Reindexing under `gray` and `grayInv`. -/

theorem sumNat_xor_const : ∀ w k, k < 2 ^ w → ∀ F : Nat → Nat,
    sumNat (2 ^ w) (fun n => F (n ^^^ k)) = sumNat (2 ^ w) F
  | 0, k, hk, F => by
    have : k = 0 := by omega
    subst this; simp [sumNat]
  | w + 1, k, hk, F => by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, sumNat_two_mul, sumNat_two_mul]
    have hk2 : k / 2 < 2 ^ w := by rw [Nat.pow_succ] at hk; omega
    have hbit : ∀ n (b : Bool),
        (2 * n + b.toNat) ^^^ k = 2 * (n ^^^ (k / 2)) + (Bool.xor b (k.testBit 0)).toNat := by
      intro n b
      apply Nat.eq_of_testBit_eq
      intro i
      cases i with
      | zero => rw [Nat.testBit_xor, testBit_two_mul_add_bool, testBit_two_mul_add_bool]
      | succ j =>
        rw [Nat.testBit_xor, testBit_two_mul_add_bool_succ, testBit_two_mul_add_bool_succ,
            testBit_succ_div2, Nat.testBit_xor]
    have h0 : ∀ n, (2 * n) ^^^ k = 2 * (n ^^^ (k / 2)) + (k.testBit 0).toNat := by
      intro n
      have h := hbit n false
      simpa using h
    have h1 : ∀ n, (2 * n + 1) ^^^ k = 2 * (n ^^^ (k / 2)) + (!(k.testBit 0)).toNat := by
      intro n
      have h := hbit n true
      simpa using h
    cases hk0 : k.testBit 0
    · simp only [h0, h1, hk0, Bool.toNat_false, Bool.not_false, Bool.toNat_true, Nat.add_zero]
      exact sumNat_xor_const w (k / 2) hk2 (fun m => F (2 * m) + F (2 * m + 1))
    · simp only [h0, h1, hk0, Bool.toNat_true, Bool.not_true, Bool.toNat_false, Nat.add_zero]
      have hcomm : ∀ n, F (2 * (n ^^^ (k / 2)) + 1) + F (2 * (n ^^^ (k / 2))) =
                        F (2 * (n ^^^ (k / 2))) + F (2 * (n ^^^ (k / 2)) + 1) :=
        fun n => Nat.add_comm _ _
      simp only [hcomm]
      exact sumNat_xor_const w (k / 2) hk2 (fun m => F (2 * m) + F (2 * m + 1))

theorem gray_pow_add {w n : Nat} (hn : n < 2 ^ w) :
    gray (2 ^ w + n) = 2 ^ w + (gray n ^^^ (if w = 0 then 0 else 2 ^ (w - 1))) := by
  have hlt1 : gray n ^^^ (if w = 0 then 0 else 2 ^ (w - 1)) < 2 ^ w := by
    apply xor_lt_two_pow (gray_lt_two_pow hn)
    split
    · exact Nat.two_pow_pos w
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · rw [testBit_gray, testBit_pow_two_add hn hi, testBit_pow_two_add hlt1 hi,
        Nat.testBit_xor, testBit_gray]
    by_cases hsucc : i + 1 < w
    · rw [testBit_pow_two_add hn hsucc]
      have hmask : (if w = 0 then 0 else 2 ^ (w - 1)).testBit i = false := by
        split
        · exact Nat.zero_testBit i
        · rw [testBit_two_pow_eq]
          have hne : ¬ (w - 1 = i) := by omega
          simp [hne]
      simp [hmask]
    · have hiw : i + 1 = w := by omega
      have hwnz : w ≠ 0 := by omega
      have hwm1 : w - 1 = i := by omega
      rw [hiw, testBit_pow_two_add_self hn, testBit_eq_false_of_lt_pow hn (Nat.le_refl w)]
      simp only [hwnz, ↓reduceIte, testBit_two_pow_eq, hwm1]
      simp
  · by_cases hiw : i = w
    · subst hiw
      rw [testBit_gray, testBit_pow_two_add_self hn, testBit_pow_two_add_self hlt1]
      have hlt2 : 2 ^ i + n < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
      rw [testBit_eq_false_of_lt_pow hlt2 (by omega)]
      rfl
    · have hlt2 : 2 ^ w + n < 2 ^ (w + 1) := by rw [Nat.pow_succ]; omega
      have hlt3 : 2 ^ w + (gray n ^^^ (if w = 0 then 0 else 2 ^ (w - 1))) < 2 ^ (w + 1) := by
        rw [Nat.pow_succ]; omega
      rw [testBit_eq_false_of_lt_pow (gray_lt_two_pow hlt2) (by omega),
          testBit_eq_false_of_lt_pow hlt3 (by omega)]

theorem sumNat_gray : ∀ w (F : Nat → Nat),
    sumNat (2 ^ w) (fun n => F (gray n)) = sumNat (2 ^ w) F
  | 0, F => by simp [sumNat, gray]
  | w + 1, F => by
    have h2 : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
    rw [h2, sumNat_split, sumNat_split]
    rw [sumNat_gray w F]
    congr 1
    have hhi : sumNat (2 ^ w) (fun n => F (gray (2 ^ w + n))) =
               sumNat (2 ^ w) (fun n => F (2 ^ w + (gray n ^^^ (if w = 0 then 0 else 2 ^ (w - 1))))) :=
      sumNat_congr fun n hn => by rw [gray_pow_add hn]
    rw [hhi]
    rw [sumNat_gray w (fun x => F (2 ^ w + (x ^^^ (if w = 0 then 0 else 2 ^ (w - 1)))))]
    have hm : (if w = 0 then 0 else 2 ^ (w - 1)) < 2 ^ w := by
      split
      · exact Nat.two_pow_pos w
      · exact Nat.pow_lt_pow_right (by omega) (by omega)
    exact sumNat_xor_const w _ hm (fun x => F (2 ^ w + x))

theorem sumNat_grayInv (w : Nat) (F : Nat → Nat) :
    sumNat (2 ^ w) (fun x => F (grayInv x)) = sumNat (2 ^ w) F := by
  rw [← sumNat_gray w (fun x => F (grayInv x))]
  apply sumNat_congr
  intro n _
  rw [grayInv_gray]

theorem countPairs_grayInv (w : Nat) (P : Nat → Nat → Bool) :
    countPairs w (fun x y => P (grayInv x) (grayInv y)) = countPairs w P := by
  unfold countPairs
  rw [sumNat_grayInv w (fun a => sumNat (2 ^ w) fun y => if P a (grayInv y) then 1 else 0)]
  apply sumNat_congr
  intro a _
  exact sumNat_grayInv w (fun b => if P a b then 1 else 0)

/-! Exact Bitwise Carry & Borrow Transducer Semantics on `Nat`. -/

theorem carryAt_succ_shift (a b : Nat) (c0 : Bool) :
    ∀ i, carryAt a b c0 (i + 1) =
      carryAt (a / 2) (b / 2) (maj (a.testBit 0) (b.testBit 0) c0) i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    change maj (a.testBit (i + 1)) (b.testBit (i + 1)) (carryAt a b c0 (i + 1)) =
      maj ((a / 2).testBit i) ((b / 2).testBit i)
        (carryAt (a / 2) (b / 2) (maj (a.testBit 0) (b.testBit 0) c0) i)
    rw [ih, testBit_succ_div2, testBit_succ_div2]

theorem borrowAt_succ_shift (a b : Nat) (b0 : Bool) :
    ∀ i, borrowAt a b b0 (i + 1) =
      borrowAt (a / 2) (b / 2) (maj (!(a.testBit 0)) (b.testBit 0) b0) i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    change maj (!(a.testBit (i + 1))) (b.testBit (i + 1)) (borrowAt a b b0 (i + 1)) =
      maj (!((a / 2).testBit i)) ((b / 2).testBit i)
        (borrowAt (a / 2) (b / 2) (maj (!(a.testBit 0)) (b.testBit 0) b0) i)
    rw [ih, testBit_succ_div2, testBit_succ_div2]

theorem add_div2_carry (a b : Nat) (c0 : Bool) :
    (a + b + c0.toNat) / 2 = a / 2 + b / 2 + (maj (a.testBit 0) (b.testBit 0) c0).toNat := by
  rw [testBit_zero_eq_mod2, testBit_zero_eq_mod2]
  cases ha : (a % 2 == 1) <;> cases hb : (b % 2 == 1) <;> cases c0 <;>
    simp [maj] at * <;> omega

theorem testBit_add_with_carry : ∀ i a b (c0 : Bool),
    (a + b + c0.toNat).testBit i =
      Bool.xor (Bool.xor (a.testBit i) (b.testBit i)) (carryAt a b c0 i)
  | 0, a, b, c0 => by
    simp only [carryAt, testBit_zero_eq_mod2]
    cases ha : (a % 2 == 1) <;> cases hb : (b % 2 == 1) <;> cases c0 <;>
      simp_all <;> omega
  | i + 1, a, b, c0 => by
    rw [testBit_succ_div2, add_div2_carry, testBit_add_with_carry i,
        carryAt_succ_shift, testBit_succ_div2, testBit_succ_div2]

theorem testBit_carryWord (a b : Nat) (c0 : Bool) (i : Nat) :
    (carryWord a b c0).testBit i = carryAt a b c0 i := by
  unfold carryWord
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_with_carry]
  cases a.testBit i <;> cases b.testBit i <;> cases carryAt a b c0 i <;> rfl

theorem testBit_gray_carryWord (a b : Nat) (c0 : Bool) (i : Nat) :
    (gray (carryWord a b c0)).testBit i =
      Bool.xor (carryAt a b c0 i) (maj (a.testBit i) (b.testBit i) (carryAt a b c0 i)) := by
  rw [testBit_gray, testBit_carryWord, testBit_carryWord]
  rfl

theorem sub_div2_borrow {a b : Nat} {b0 : Bool} (h : b + b0.toNat ≤ a) :
    (a - b - b0.toNat) / 2 =
      a / 2 - b / 2 - (maj (!(a.testBit 0)) (b.testBit 0) b0).toNat ∧
    b / 2 + (maj (!(a.testBit 0)) (b.testBit 0) b0).toNat ≤ a / 2 := by
  rw [testBit_zero_eq_mod2, testBit_zero_eq_mod2]
  cases ha : (a % 2 == 1) <;> cases hb : (b % 2 == 1) <;> cases b0 <;>
    simp [maj] at * <;> omega

theorem testBit_sub_with_borrow : ∀ i a b (b0 : Bool), b + b0.toNat ≤ a →
    (a - b - b0.toNat).testBit i =
      Bool.xor (Bool.xor (a.testBit i) (b.testBit i)) (borrowAt a b b0 i)
  | 0, a, b, b0, h => by
    simp only [borrowAt, testBit_zero_eq_mod2]
    cases ha : (a % 2 == 1) <;> cases hb : (b % 2 == 1) <;> cases b0 <;>
      simp_all <;> omega
  | i + 1, a, b, b0, h => by
    have ⟨hdiv, hle⟩ := sub_div2_borrow h
    rw [testBit_succ_div2, hdiv, testBit_sub_with_borrow i _ _ _ hle,
        borrowAt_succ_shift, testBit_succ_div2, testBit_succ_div2]

theorem testBit_borrowWord {a b : Nat} {b0 : Bool} (h : b + b0.toNat ≤ a) (i : Nat) :
    (borrowWord a b b0).testBit i = borrowAt a b b0 i := by
  unfold borrowWord
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_sub_with_borrow i a b b0 h]
  cases a.testBit i <;> cases b.testBit i <;> cases borrowAt a b b0 i <;> rfl

theorem testBit_gray_borrowWord {a b : Nat} {b0 : Bool} (h : b + b0.toNat ≤ a) (i : Nat) :
    (gray (borrowWord a b b0)).testBit i =
      Bool.xor (borrowAt a b b0 i) (maj (!(a.testBit i)) (b.testBit i) (borrowAt a b b0 i)) := by
  rw [testBit_gray, testBit_borrowWord h, testBit_borrowWord h]
  rfl

theorem borrowAt_pow_add {w a b : Nat} {b0 : Bool} (ha : a < 2 ^ w) :
    ∀ i, i ≤ w → borrowAt (2 ^ w + a) b b0 i = borrowAt a b b0 i
  | 0, _     => rfl
  | i + 1, hi => by
    simp only [borrowAt]
    rw [testBit_pow_two_add ha (by omega), borrowAt_pow_add ha i (by omega)]

theorem testBit_borrowWordFull {w a b : Nat} {b0 : Bool}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ∀ i, i ≤ w → (borrowWordFull w a b b0).testBit i = borrowAt a b b0 i := by
  intro i hi
  have hle : b + b0.toNat ≤ 2 ^ w + a := by cases b0 <;> simp <;> omega
  unfold borrowWordFull
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      testBit_sub_with_borrow i (2 ^ w + a) b b0 hle, borrowAt_pow_add ha i hi]
  by_cases hlt : i < w
  · rw [testBit_pow_two_add ha hlt, testBit_two_pow_eq]
    have hne : w ≠ i := by omega
    simp only [hne, decide_false, Bool.xor_false]
    cases a.testBit i <;> cases b.testBit i <;> cases borrowAt a b b0 i <;> rfl
  · have heq : i = w := by omega
    subst heq
    rw [testBit_pow_two_add_self ha, testBit_eq_false_of_lt_pow ha (by omega),
        testBit_eq_false_of_lt_pow hb (by omega), testBit_two_pow_eq]
    simp only [decide_true]
    cases borrowAt a b b0 i <;> rfl

theorem testBit_gray_borrowWordFull {w a b : Nat} {b0 : Bool}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) {i : Nat} (hi : i < w) :
    (gray (borrowWordFull w a b b0)).testBit i =
      Bool.xor (borrowAt a b b0 i) (maj (!(a.testBit i)) (b.testBit i) (borrowAt a b b0 i)) := by
  rw [testBit_gray, testBit_borrowWordFull ha hb i (by omega),
      testBit_borrowWordFull ha hb (i + 1) (by omega)]
  rfl

/-! ===========================================================================
    PART 3: The Concrete Transducers & Five Infinite Theorems
    =========================================================================== -/

/-! ### Theorem 0: The 8-State -> 4-State Parity-Seeded LSB Gray-Addition Transducer -/

/-- Finite 32-transition quotient bisimulation certificate (discharged by kernel). -/
theorem grayAdd8_to_4_bisim (s0 : Bool × Bool × Bool) (x y i : Nat) :
    outAt grayAddTransducer8 s0 x y i =
      outAt grayAddTransducer4 (grayAddQuotient s0) x y i := by
  apply transducer_quotient_bisim grayAddTransducer8 grayAddTransducer4 grayAddQuotient
  · intro ⟨a, b, c⟩ xi yi
    cases a <;> cases b <;> cases c <;> cases xi <;> cases yi <;> rfl
  · intro ⟨a, b, c⟩ xi yi
    cases a <;> cases b <;> cases c <;> cases xi <;> cases yi <;> rfl

theorem grayAddTransducer8_state (x y : Nat) (c0 : Bool) :
    ∀ i, stateAt grayAddTransducer8 (parity x, parity y, c0) x y i =
      ((grayInv x).testBit i, (grayInv y).testBit i, carryAt (grayInv x) (grayInv y) c0 i) := by
  intro i
  induction i with
  | zero =>
    simp only [stateAt, carryAt, testBit_grayInv_zero]
  | succ i ih =>
    change grayAddTransducer8.step
      (stateAt grayAddTransducer8 (parity x, parity y, c0) x y i) (x.testBit i) (y.testBit i) = _
    rw [ih]
    simp only [grayAddTransducer8, carryAt, testBit_grayInv_succ]

/-- THEOREM 0 (4-State Parity-Seeded LSB Gray-Addition Transducer Theorem):
    For ALL `x, y : Nat`, ALL carry-in `c0 : Bool`, and ALL bit positions `i : Nat`,
    bit `i` of `G(G⁻¹(x) + G⁻¹(y) + c0)` is computed by the 4-state LSB-first
    transducer `grayAddTransducer4` seeded at `(P(x) ^ P(y), P(x) ^ c0)`. -/
theorem grayAddWith_eq_transducer4 (x y : Nat) (c0 : Bool) (i : Nat) :
    (grayAddWith x y c0).testBit i =
      outAt grayAddTransducer4 (Bool.xor (parity x) (parity y), Bool.xor (parity x) c0) x y i := by
  have h8 : outAt grayAddTransducer8 (parity x, parity y, c0) x y i =
      (grayAddWith x y c0).testBit i := by
    unfold outAt grayAddWith
    rw [grayAddTransducer8_state]
    have hsum : grayInv x + grayInv y + c0.toNat =
        grayInv x ^^^ grayInv y ^^^ carryWord (grayInv x) (grayInv y) c0 := by
      unfold carryWord
      apply Nat.eq_of_testBit_eq
      intro k
      simp only [Nat.testBit_xor]
      cases (grayInv x + grayInv y + c0.toNat).testBit k <;>
        cases (grayInv x).testBit k <;> cases (grayInv y).testBit k <;> rfl
    rw [hsum, gray_xor, gray_xor, gray_grayInv, gray_grayInv,
        Nat.testBit_xor, Nat.testBit_xor, testBit_gray_carryWord]
    rfl
  rw [← h8, grayAdd8_to_4_bisim]
  rfl

/-! ### Theorem 1: Carry-Borrow Gray Orthogonality & Exact Mask Separation -/

theorem carryBorrowTransducer_state (a b : Nat) (c0 b0 : Bool) :
    ∀ i, stateAt carryBorrowTransducer (c0, b0) a b i =
      (carryAt a b c0 i, borrowAt a b b0 i) := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    change carryBorrowTransducer.step
      (stateAt carryBorrowTransducer (c0, b0) a b i) (a.testBit i) (b.testBit i) = _
    rw [ih]
    rfl

theorem carryBorrowTransducer_out (a b : Nat) (c0 b0 : Bool) (i : Nat) :
    outAt carryBorrowTransducer (c0, b0) a b i =
      (Bool.xor (carryAt a b c0 i) (maj (a.testBit i) (b.testBit i) (carryAt a b c0 i)),
       Bool.xor (borrowAt a b b0 i) (maj (!(a.testBit i)) (b.testBit i) (borrowAt a b b0 i))) := by
  unfold outAt
  rw [carryBorrowTransducer_state]
  rfl

/-- Finite 16-transition orthogonality certificate lifted via `transducer_invariant_lift`. -/
theorem carryBorrow_out_orthogonal (c0 b0 : Bool) (a b i : Nat) :
    ((outAt carryBorrowTransducer (c0, b0) a b i).1 &&
     (outAt carryBorrowTransducer (c0, b0) a b i).2) = false := by
  apply transducer_invariant_lift carryBorrowTransducer (fun _ => True)
    (fun p => (p.1 && p.2) = false) (c0, b0) trivial (fun _ _ _ _ => trivial)
  intro ⟨c, bor⟩ ai bi _
  cases c <;> cases bor <;> cases ai <;> cases bi <;> rfl

/-- THEOREM 1A (Carry-Borrow Gray Orthogonality):
    For ALL `a, b : Nat` and ALL `c0, b0 : Bool` with `b + b0 ≤ a`,
    the Gray-encoded carry word and Gray-encoded borrow word are strictly bit-disjoint:
    `G(C_{c0}(a, b)) &&& G(B_{b0}(a, b)) = 0`. -/
theorem gray_carry_borrow_orthogonal (a b : Nat) (c0 b0 : Bool) (h : b + b0.toNat ≤ a) :
    (gray (carryWord a b c0)) &&& (gray (borrowWord a b b0)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, testBit_gray_carryWord, testBit_gray_borrowWord h]
  have h1 := carryBorrow_out_orthogonal c0 b0 a b i
  rw [carryBorrowTransducer_out] at h1
  exact h1

/-- THEOREM 1B (Exact Mask Separation & Additive-XOR Collapse):
    For ALL `a, b : Nat` and `c0, b0 : Bool` with `b + b0 ≤ a`,
    the Gray-encoded carry and borrow words partition `G(a+b+c0) ^^^ G(a-b-b0)`
    strictly along `!(a ^^^ b)` and `(a ^^^ b)`, and satisfy
    `G(C) + G(B) = G(a+b+c0) ^^^ G(a-b-b0)`. -/
theorem gray_carry_borrow_mask_separation (a b : Nat) (c0 b0 : Bool) (h : b + b0.toNat ≤ a) :
    (∀ i, (gray (carryWord a b c0)).testBit i =
          (((gray (a + b + c0.toNat)) ^^^ (gray (a - b - b0.toNat))).testBit i &&
           !((a ^^^ b).testBit i))) ∧
    (∀ i, (gray (borrowWord a b b0)).testBit i =
          (((gray (a + b + c0.toNat)) ^^^ (gray (a - b - b0.toNat))).testBit i &&
           (a ^^^ b).testBit i)) ∧
    gray (carryWord a b c0) + gray (borrowWord a b b0) =
      gray (a + b + c0.toNat) ^^^ gray (a - b - b0.toNat) := by
  have hxor : gray (carryWord a b c0) ^^^ gray (borrowWord a b b0) =
      gray (a + b + c0.toNat) ^^^ gray (a - b - b0.toNat) := by
    rw [← gray_xor]
    unfold carryWord borrowWord
    have hinner :
        ((a + b + c0.toNat) ^^^ a ^^^ b) ^^^ ((a - b - b0.toNat) ^^^ a ^^^ b) =
        (a + b + c0.toNat) ^^^ (a - b - b0.toNat) := by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_xor]
      cases (a + b + c0.toNat).testBit i <;> cases (a - b - b0.toNat).testBit i <;>
        cases a.testBit i <;> cases b.testBit i <;> rfl
    rw [hinner, gray_xor]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [← hxor, Nat.testBit_xor, Nat.testBit_xor, testBit_gray_carryWord, testBit_gray_borrowWord h]
    cases a.testBit i <;> cases b.testBit i <;>
      cases carryAt a b c0 i <;> cases borrowAt a b b0 i <;> rfl
  · intro i
    rw [← hxor, Nat.testBit_xor, Nat.testBit_xor, testBit_gray_carryWord, testBit_gray_borrowWord h]
    cases a.testBit i <;> cases b.testBit i <;>
      cases carryAt a b c0 i <;> cases borrowAt a b b0 i <;> rfl
  · rw [← hxor]
    have horth := gray_carry_borrow_orthogonal a b c0 b0 h
    have hadd_xor : ∀ u v, u &&& v = 0 → u + v = u ^^^ v := by
      intro u v huv
      have h0 : carryWord u v false = 0 := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [testBit_carryWord, Nat.zero_testBit]
        induction k with
        | zero => rfl
        | succ k ih =>
          change maj (u.testBit k) (v.testBit k) (carryAt u v false k) = false
          rw [ih]
          have hk := congrArg (fun z => z.testBit k) huv
          rw [Nat.testBit_and, Nat.zero_testBit] at hk
          cases hu : u.testBit k <;> cases hv : v.testBit k <;> simp_all [maj]
      unfold carryWord at h0
      simp only [Bool.toNat_false, Nat.add_zero] at h0
      apply Nat.eq_of_testBit_eq
      intro k
      have hk := congrArg (fun z => z.testBit k) h0
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.zero_testBit] at hk
      rw [Nat.testBit_xor]
      cases h1 : (u + v).testBit k <;> cases h2 : u.testBit k <;> cases h3 : v.testBit k <;> simp_all
    exact hadd_xor _ _ horth

/-- Corollary in Gray Coordinates: for `G⁻¹(y) ≤ G⁻¹(x)`, the Gray-addition defect
    `Δ₊(x,y) = (x ⊞ y) ^^^ x ^^^ y` and Gray-subtraction defect `Δ₋(x,y) = (x ⊟ y) ^^^ x ^^^ y`
    are strictly bit-orthogonal and satisfy `Δ₊ + Δ₋ = (x ⊞ y) ^^^ (x ⊟ y)`. -/
theorem gray_coord_defect_orthogonal (x y : Nat) (h : grayInv y ≤ grayInv x) :
    ((grayAdd x y ^^^ x ^^^ y) &&& (graySub x y ^^^ x ^^^ y) = 0) ∧
    ((grayAdd x y ^^^ x ^^^ y) + (graySub x y ^^^ x ^^^ y) = grayAdd x y ^^^ graySub x y) := by
  have h1 : grayAdd x y ^^^ x ^^^ y = gray (carryWord (grayInv x) (grayInv y) false) := by
    unfold grayAdd grayAddWith carryWord
    rw [gray_xor, gray_xor, gray_grayInv, gray_grayInv]
  have h2 : graySub x y ^^^ x ^^^ y = gray (borrowWord (grayInv x) (grayInv y) false) := by
    unfold graySub graySubWith borrowWord
    rw [gray_xor, gray_xor, gray_grayInv, gray_grayInv]
  rw [h1, h2]
  have hle : grayInv y + false.toNat ≤ grayInv x := by simpa using h
  refine ⟨gray_carry_borrow_orthogonal _ _ false false hle, ?_⟩
  exact (gray_carry_borrow_mask_separation (grayInv x) (grayInv y) false false hle).2.2

/-! ### Theorem 2: The Carry-Borrow Gray Bijection `Φ_{w,c0,b0}` & Explicit 4-State Inverse -/

theorem phiTransducer_state (a b : Nat) (c0 b0 : Bool) :
    ∀ i, stateAt phiTransducer (c0, b0) a b i = (carryAt a b c0 i, borrowAt a b b0 i) := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    change phiTransducer.step
      (stateAt phiTransducer (c0, b0) a b i) (a.testBit i) (b.testBit i) = _
    rw [ih]
    rfl

theorem runPair_phi_eq_phiMap {w a b : Nat} (c0 b0 : Bool)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    runPair phiTransducer (c0, b0) w a b = phiMap w c0 b0 a b := by
  have hlt := runPair_lt phiTransducer w (c0, b0) a b
  have hphi1 : (phiMap w c0 b0 a b).1 < 2 ^ w := xor_lt_two_pow ha hb
  have hphi2 : (phiMap w c0 b0 a b).2 < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  apply Prod.ext
  · apply eq_of_testBit_lt hlt.1 hphi1
    intro i hi
    rw [(runPair_testBit phiTransducer w (c0, b0) a b i hi).1]
    unfold outAt phiMap
    rw [phiTransducer_state]
    simp [phiTransducer, Nat.testBit_xor]
  · apply eq_of_testBit_lt hlt.2 hphi2
    intro i hi
    rw [(runPair_testBit phiTransducer w (c0, b0) a b i hi).2]
    unfold outAt phiMap
    rw [phiTransducer_state, testBit_mod_two_pow]
    simp only [hi, decide_true, Bool.true_and, phiTransducer]
    have hxor_eq :
        gray (a + b + c0.toNat) ^^^ gray ((2 ^ w + a - b - b0.toNat) ^^^ 2 ^ w) =
        gray (carryWord a b c0) ^^^ gray (borrowWordFull w a b b0) := by
      rw [← gray_xor, ← gray_xor]
      unfold carryWord borrowWordFull
      congr 1
      apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_xor]
      cases (a + b + c0.toNat).testBit k <;>
        cases (2 ^ w + a - b - b0.toNat).testBit k <;>
        cases (2 ^ w).testBit k <;>
        cases a.testBit k <;> cases b.testBit k <;> rfl
    rw [hxor_eq, Nat.testBit_xor, testBit_gray_carryWord, testBit_gray_borrowWordFull ha hb hi]

/-- THEOREM 2 (Carry-Borrow Gray Bijection Theorem):
    For EVERY bit-width `w : Nat` and EVERY `(c0, b0) ∈ Bool²`,
    `phiMap w c0 b0 : [0, 2^w)^2 → [0, 2^w)^2` is an EXACT BIJECTION
    with explicit 4-state LSB inverse `phiMapInv w c0 b0`. -/
theorem phiMap_bijection (w : Nat) (c0 b0 : Bool) :
    (∀ a b, a < 2 ^ w → b < 2 ^ w →
      (phiMap w c0 b0 a b).1 < 2 ^ w ∧ (phiMap w c0 b0 a b).2 < 2 ^ w ∧
      phiMapInv w c0 b0 (phiMap w c0 b0 a b).1 (phiMap w c0 b0 a b).2 = (a, b)) ∧
    (∀ d t, d < 2 ^ w → t < 2 ^ w →
      (phiMapInv w c0 b0 d t).1 < 2 ^ w ∧ (phiMapInv w c0 b0 d t).2 < 2 ^ w ∧
      phiMap w c0 b0 (phiMapInv w c0 b0 d t).1 (phiMapInv w c0 b0 d t).2 = (d, t)) := by
  have hlift := transducer_bijection_lift phiTransducer phiInvTransducer
    (by intro ⟨c, bor⟩ x y; cases c <;> cases bor <;> cases x <;> cases y <;> rfl)
    (by intro ⟨c, bor⟩ u v; cases c <;> cases bor <;> cases u <;> cases v <;> rfl)
    (by intro ⟨c, bor⟩ x y; cases c <;> cases bor <;> cases x <;> cases y <;> rfl)
    (by intro ⟨c, bor⟩ u v; cases c <;> cases bor <;> cases u <;> cases v <;> rfl)
    w (c0, b0)
  constructor
  · intro a b ha hb
    have hlt := runPair_lt phiTransducer w (c0, b0) a b
    rw [← runPair_phi_eq_phiMap c0 b0 ha hb]
    exact ⟨hlt.1, hlt.2, hlift.1 a b ha hb⟩
  · intro d t hd ht
    have hlt := runPair_lt phiInvTransducer w (c0, b0) d t
    unfold phiMapInv
    rw [← runPair_phi_eq_phiMap c0 b0 hlt.1 hlt.2]
    exact ⟨hlt.1, hlt.2, hlift.2 d t hd ht⟩

/-! ### Theorem 3: Exact Joint Carry-Borrow Gray Fiber Cardinality Theorem -/

theorem pairBits_length (w u v : Nat) : (pairBits w u v).length = w := by
  induction w generalizing u v with
  | zero => rfl
  | succ w ih => simp [pairBits, ih]

theorem runList_carryBorrow_eq_pairBits : ∀ w c0 b0 a b,
    a < 2 ^ w → b < 2 ^ w →
    runList carryBorrowTransducer (c0, b0) w a b =
      pairBits w (gray (carryWord a b c0) % 2 ^ w) (gray (borrowWordFull w a b b0) % 2 ^ w) := by
  intro w
  have hget : ∀ (k : Nat) (s0 : Bool × Bool) (a b u v : Nat),
      (∀ i, i < k → outAt carryBorrowTransducer s0 a b i = (u.testBit i, v.testBit i)) →
      runList carryBorrowTransducer s0 k a b = pairBits k u v := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro s0 a b u v h
      simp only [runList, pairBits]
      have h0 := h 0 (by omega)
      simp only [outAt, stateAt] at h0
      rw [h0]
      congr 1
      apply ih
      intro i hi
      have hsi := h (i + 1) (by omega)
      rw [outAt_succ_shift, testBit_succ_div2, testBit_succ_div2] at hsi
      exact hsi
  intro c0 b0 a b ha hb
  apply hget
  intro i hi
  rw [carryBorrowTransducer_out, testBit_mod_two_pow, testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  rw [testBit_gray_carryWord, testBit_gray_borrowWordFull ha hb hi]

theorem pairBits_foldr_jointMult : ∀ w u v, u < 2 ^ w → v < 2 ^ w →
    (pairBits w u v).foldr (fun o acc => jointMult o * acc) 1 =
      if u &&& v = 0 then 2 ^ (w - popcount u - popcount v) else 0
  | 0, u, v, hu, hv => by
    have hu0 : u = 0 := by omega
    have hv0 : v = 0 := by omega
    subst hu0; subst hv0; rfl
  | w + 1, u, v, hu, hv => by
    have hu' : u / 2 < 2 ^ w := by rw [Nat.pow_succ] at hu; omega
    have hv' : v / 2 < 2 ^ w := by rw [Nat.pow_succ] at hv; omega
    have ih := pairBits_foldr_jointMult w (u / 2) (v / 2) hu' hv'
    simp only [pairBits, List.foldr_cons]
    rw [ih]
    have hpu : popcount u = (u.testBit 0).toNat + popcount (u / 2) := by
      rw [← popcount_two_mul_add_bool (u / 2) (u.testBit 0), nat_div2_decomp]
    have hpv : popcount v = (v.testBit 0).toNat + popcount (v / 2) := by
      rw [← popcount_two_mul_add_bool (v / 2) (v.testBit 0), nat_div2_decomp]
    have hand_iff : (u &&& v = 0) ↔ ((u.testBit 0 && v.testBit 0) = false ∧ (u / 2) &&& (v / 2) = 0) := by
      constructor
      · intro h0
        refine ⟨?_, ?_⟩
        · have hb := congrArg (fun z => z.testBit 0) h0
          rw [Nat.testBit_and, Nat.zero_testBit] at hb
          exact hb
        · apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_and, Nat.zero_testBit, ← testBit_succ_div2, ← testBit_succ_div2]
          have hb := congrArg (fun z => z.testBit (i + 1)) h0
          rw [Nat.testBit_and, Nat.zero_testBit] at hb
          exact hb
      · intro ⟨hb0, hrest⟩
        apply Nat.eq_of_testBit_eq
        intro i
        cases i with
        | zero => rw [Nat.testBit_and, Nat.zero_testBit]; exact hb0
        | succ j =>
          rw [Nat.testBit_and, Nat.zero_testBit, testBit_succ_div2, testBit_succ_div2]
          have hb := congrArg (fun z => z.testBit j) hrest
          rw [Nat.testBit_and, Nat.zero_testBit] at hb
          exact hb
    have hdisj_pop : ∀ k x y, x < 2 ^ k → y < 2 ^ k → x &&& y = 0 →
        popcount x + popcount y ≤ k := by
      intro k
      induction k with
      | zero =>
        intro x y hx hy _
        have hx0 : x = 0 := by omega
        have hy0 : y = 0 := by omega
        subst hx0; subst hy0; decide
      | succ k ihk =>
        intro x y hx hy hxy
        have hx' : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
        have hy' : y / 2 < 2 ^ k := by rw [Nat.pow_succ] at hy; omega
        have hb0 : (x.testBit 0 && y.testBit 0) = false := by
          have hb := congrArg (fun z => z.testBit 0) hxy
          rw [Nat.testBit_and, Nat.zero_testBit] at hb; exact hb
        have hxy' : (x / 2) &&& (y / 2) = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_and, Nat.zero_testBit, ← testBit_succ_div2, ← testBit_succ_div2]
          have hb := congrArg (fun z => z.testBit (i + 1)) hxy
          rw [Nat.testBit_and, Nat.zero_testBit] at hb; exact hb
        have ihxy := ihk (x / 2) (y / 2) hx' hy' hxy'
        have hpx : popcount x = (x.testBit 0).toNat + popcount (x / 2) := by
          rw [← popcount_two_mul_add_bool (x / 2) (x.testBit 0), nat_div2_decomp]
        have hpy : popcount y = (y.testBit 0).toNat + popcount (y / 2) := by
          rw [← popcount_two_mul_add_bool (y / 2) (y.testBit 0), nat_div2_decomp]
        rw [hpx, hpy]
        cases hx0 : x.testBit 0 <;> cases hy0 : y.testBit 0
        · simp only [Bool.toNat_false]; omega
        · simp only [Bool.toNat_false, Bool.toNat_true]; omega
        · simp only [Bool.toNat_false, Bool.toNat_true]; omega
        · simp [hx0, hy0] at hb0
    by_cases hrest0 : (u / 2) &&& (v / 2) = 0
    · have hdp := hdisj_pop w (u / 2) (v / 2) hu' hv' hrest0
      cases hu0 : u.testBit 0 <;> cases hv0 : v.testBit 0
      · have h0 : u &&& v = 0 := hand_iff.mpr ⟨by simp [hu0, hv0], hrest0⟩
        simp only [jointMult, hrest0, h0, ↓reduceIte, hpu, hpv, hu0, hv0, Bool.toNat_false, Nat.zero_add]
        have hexp : w + 1 - popcount (u / 2) - popcount (v / 2) = (w - popcount (u / 2) - popcount (v / 2)) + 1 := by omega
        rw [hexp, Nat.pow_succ, Nat.mul_comm]
      · have h0 : u &&& v = 0 := hand_iff.mpr ⟨by simp [hu0, hv0], hrest0⟩
        simp only [jointMult, hrest0, h0, ↓reduceIte, hpu, hpv, hu0, hv0,
                   Bool.toNat_false, Bool.toNat_true, Nat.zero_add, Nat.one_mul]
        congr 1; omega
      · have h0 : u &&& v = 0 := hand_iff.mpr ⟨by simp [hu0, hv0], hrest0⟩
        simp only [jointMult, hrest0, h0, ↓reduceIte, hpu, hpv, hu0, hv0,
                   Bool.toNat_false, Bool.toNat_true, Nat.zero_add, Nat.one_mul]
        congr 1; omega
      · have hne : ¬ (u &&& v = 0) := by
          intro h0; have := (hand_iff.mp h0).1; simp [hu0, hv0] at this
        simp [jointMult, hrest0, hne]
    · have hne : ¬ (u &&& v = 0) := fun h0 => hrest0 (hand_iff.mp h0).2
      simp [hrest0, hne]

/-- THEOREM 3 (Exact Joint Carry-Borrow Gray Fiber Cardinality Theorem):
    For EVERY `w : Nat`, EVERY `(c0, b0) ∈ Bool²`, and EVERY target pair `u, v < 2^w`,
    the exact count of `(a, b) ∈ [0, 2^w)^2` with
    `G(C_{c0}(a,b)) % 2^w = u` and `G(B^{full}_{w,b0}(a,b)) % 2^w = v` is
    `2^(w - popcount u - popcount v)` if `u &&& v = 0`, and `0` otherwise. -/
theorem gray_joint_carry_borrow_fiber_count (w : Nat) (c0 b0 : Bool) (u v : Nat)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w) :
    countPairs w (fun a b =>
      decide (gray (carryWord a b c0) % 2 ^ w = u ∧
              gray (borrowWordFull w a b b0) % 2 ^ w = v)) =
      if u &&& v = 0 then 2 ^ (w - popcount u - popcount v) else 0 := by
  have hlift := transducer_balanced_fiber_lift carryBorrowTransducer jointMult
    (by
      intro ⟨c, bor⟩ ⟨o1, o2⟩
      cases c <;> cases bor <;> cases o1 <;> cases o2 <;> rfl)
    w (c0, b0) (pairBits w u v) (pairBits_length w u v)
  rw [pairBits_foldr_jointMult w u v hu hv] at hlift
  rw [← hlift]
  apply countPairs_congr
  intro a b ha hb
  rw [runList_carryBorrow_eq_pairBits w c0 b0 a b ha hb]
  have hinj : ∀ k x1 y1 x2 y2, x1 < 2 ^ k → y1 < 2 ^ k → x2 < 2 ^ k → y2 < 2 ^ k →
      (pairBits k x1 y1 = pairBits k x2 y2 ↔ x1 = x2 ∧ y1 = y2) := by
    intro k
    induction k with
    | zero =>
      intro x1 y1 x2 y2 hx1 hy1 hx2 hy2
      simp [pairBits]; omega
    | succ k ih =>
      intro x1 y1 x2 y2 hx1 hy1 hx2 hy2
      simp only [pairBits, List.cons.injEq, Prod.mk.injEq]
      have hx1' : x1 / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx1; omega
      have hy1' : y1 / 2 < 2 ^ k := by rw [Nat.pow_succ] at hy1; omega
      have hx2' : x2 / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx2; omega
      have hy2' : y2 / 2 < 2 ^ k := by rw [Nat.pow_succ] at hy2; omega
      rw [ih _ _ _ _ hx1' hy1' hx2' hy2']
      constructor
      · intro ⟨⟨hb1, hb2⟩, hd1, hd2⟩
        constructor
        · rw [← nat_div2_decomp x1, ← nat_div2_decomp x2, hb1, hd1]
        · rw [← nat_div2_decomp y1, ← nat_div2_decomp y2, hb2, hd2]
      · intro ⟨h1, h2⟩; subst h1; subst h2; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
  have hlt1 : gray (carryWord a b c0) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hlt2 : gray (borrowWordFull w a b b0) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  by_cases h : gray (carryWord a b c0) % 2 ^ w = u ∧ gray (borrowWordFull w a b b0) % 2 ^ w = v
  · have h2 := (hinj w _ _ u v hlt1 hlt2 hu hv).mpr h
    simp [h]
  · have h2 : ¬ (pairBits w (gray (carryWord a b c0) % 2 ^ w)
                   (gray (borrowWordFull w a b b0) % 2 ^ w) = pairBits w u v) :=
      fun heq => h ((hinj w _ _ u v hlt1 hlt2 hu hv).mp heq)
    simp [h, h2]

/-! ### Theorem 4: The Gray-Code Carry-Defect Whitening Theorem -/

theorem wordBits_length (w z : Nat) : (wordBits w z).length = w := by
  induction w generalizing z with
  | zero => rfl
  | succ w ih => simp [wordBits, ih]

theorem carryDiffTransducer_state (a b : Nat) (c0 : Bool) :
    ∀ i, stateAt carryDiffTransducer c0 a b i = carryAt a b c0 i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    change carryDiffTransducer.step
      (stateAt carryDiffTransducer c0 a b i) (a.testBit i) (b.testBit i) = _
    rw [ih]
    rfl

theorem runList_carryDiff_eq_wordBits (w : Nat) (c0 : Bool) (a b : Nat) :
    runList carryDiffTransducer c0 w a b = wordBits w (gray (carryWord a b c0) % 2 ^ w) := by
  have hget : ∀ (k : Nat) (s0 : Bool) (a b z : Nat),
      (∀ i, i < k → outAt carryDiffTransducer s0 a b i = z.testBit i) →
      runList carryDiffTransducer s0 k a b = wordBits k z := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro s0 a b z h
      simp only [runList, wordBits]
      have h0 := h 0 (by omega)
      simp only [outAt, stateAt] at h0
      rw [h0]
      congr 1
      apply ih
      intro i hi
      have hsi := h (i + 1) (by omega)
      rw [outAt_succ_shift, testBit_succ_div2] at hsi
      exact hsi
  apply hget
  intro i hi
  unfold outAt
  rw [carryDiffTransducer_state, testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, carryDiffTransducer, testBit_gray_carryWord]

theorem wordBits_foldr_carryDiffMult : ∀ w z, z < 2 ^ w →
    (wordBits w z).foldr (fun o acc => carryDiffMult o * acc) 1 = 3 ^ (w - popcount z)
  | 0, z, hz => by
    have : z = 0 := by omega
    subst this; rfl
  | w + 1, z, hz => by
    have hz' : z / 2 < 2 ^ w := by rw [Nat.pow_succ] at hz; omega
    have ih := wordBits_foldr_carryDiffMult w (z / 2) hz'
    simp only [wordBits, List.foldr_cons]
    rw [ih]
    have hpz : popcount z = (z.testBit 0).toNat + popcount (z / 2) := by
      rw [← popcount_two_mul_add_bool (z / 2) (z.testBit 0), nat_div2_decomp]
    have hle := popcount_le_width w (z / 2) hz'
    cases hz0 : z.testBit 0
    · simp only [carryDiffMult, hpz, hz0, Bool.toNat_false, Nat.zero_add]
      have hexp : w + 1 - popcount (z / 2) = (w - popcount (z / 2)) + 1 := by omega
      rw [hexp, Nat.pow_succ, Nat.mul_comm]
    · simp only [carryDiffMult, hpz, hz0, Bool.toNat_true, Nat.one_mul]
      congr 1; omega

theorem wordBits_inj : ∀ w x y, x < 2 ^ w → y < 2 ^ w →
    (wordBits w x = wordBits w y ↔ x = y)
  | 0, x, y, hx, hy => by simp [wordBits]; omega
  | w + 1, x, y, hx, hy => by
    simp only [wordBits, List.cons.injEq]
    have hx' : x / 2 < 2 ^ w := by rw [Nat.pow_succ] at hx; omega
    have hy' : y / 2 < 2 ^ w := by rw [Nat.pow_succ] at hy; omega
    rw [wordBits_inj w (x / 2) (y / 2) hx' hy']
    constructor
    · intro ⟨hb, hd⟩
      rw [← nat_div2_decomp x, ← nat_div2_decomp y, hb, hd]
    · intro h; subst h; exact ⟨rfl, rfl⟩

/-- THEOREM 4A (Gray-Code Carry-Defect Whitening Law — Binary Coordinates):
    For EVERY `w : Nat`, EVERY carry-in `c0 : Bool`, and EVERY `z < 2^w`:
    `#{(a, b) ∈ [0, 2^w)^2 : G(C_{c0}(a, b)) % 2^w = z} = 3^(w - popcount z)`. -/
theorem gray_carry_whitening_binary (w : Nat) (c0 : Bool) (z : Nat) (hz : z < 2 ^ w) :
    countPairs w (fun a b => decide (gray (carryWord a b c0) % 2 ^ w = z)) =
      3 ^ (w - popcount z) := by
  have hlift := transducer_balanced_fiber_lift carryDiffTransducer carryDiffMult
    (by intro c o; cases c <;> cases o <;> rfl)
    w c0 (wordBits w z) (wordBits_length w z)
  rw [wordBits_foldr_carryDiffMult w z hz] at hlift
  rw [← hlift]
  apply countPairs_congr
  intro a b _ _
  rw [runList_carryDiff_eq_wordBits w c0 a b]
  have hlt : gray (carryWord a b c0) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  by_cases h : gray (carryWord a b c0) % 2 ^ w = z
  · have h2 := (wordBits_inj w _ z hlt hz).mpr h
    simp [h]
  · have h2 : ¬ (wordBits w (gray (carryWord a b c0) % 2 ^ w) = wordBits w z) :=
      fun heq => h ((wordBits_inj w _ z hlt hz).mp heq)
    simp [h, h2]

/-- THEOREM 4B (Gray-Code Carry-Defect Whitening Law — Pure Gray Coordinates):
    For EVERY `w : Nat`, EVERY carry-in `c0 : Bool`, and EVERY `z < 2^w`:
    `#{(x, y) ∈ [0, 2^w)^2 : (G(G⁻¹(x) + G⁻¹(y) + c0) ^^^ x ^^^ y) % 2^w = z} = 3^(w - popcount z)`. -/
theorem gray_carry_whitening_gray_coords (w : Nat) (c0 : Bool) (z : Nat) (hz : z < 2 ^ w) :
    countPairs w (fun x y => decide ((grayAddWith x y c0 ^^^ x ^^^ y) % 2 ^ w = z)) =
      3 ^ (w - popcount z) := by
  have hrew : ∀ x y, (grayAddWith x y c0 ^^^ x ^^^ y) % 2 ^ w =
      gray (carryWord (grayInv x) (grayInv y) c0) % 2 ^ w := by
    intro x y
    unfold grayAddWith carryWord
    rw [gray_xor, gray_xor, gray_grayInv, gray_grayInv]
  rw [countPairs_congr (fun x y _ _ => by rw [hrew x y])]
  rw [countPairs_grayInv w (fun a b => decide (gray (carryWord a b c0) % 2 ^ w = z))]
  exact gray_carry_whitening_binary w c0 z hz

/-! ### Theorem 5: Full Untruncated Parity-Closed Gray Carry-Defect Fiber Law -/

theorem carryWord_lt_two_pow_succ {w a b : Nat} {c0 : Bool}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    carryWord a b c0 < 2 ^ (w + 1) := by
  unfold carryWord
  have hsum : a + b + c0.toNat < 2 ^ (w + 1) := by
    rw [Nat.pow_succ]; cases c0 <;> simp <;> omega
  have ha' : a < 2 ^ (w + 1) := by rw [Nat.pow_succ]; omega
  have hb' : b < 2 ^ (w + 1) := by rw [Nat.pow_succ]; omega
  exact xor_lt_two_pow (xor_lt_two_pow hsum ha') hb'

theorem parity_gray_carryWord (a b : Nat) (c0 : Bool) :
    parity (gray (carryWord a b c0)) = c0 := by
  rw [parity_gray, testBit_carryWord]
  rfl

theorem parity_two_pow (k : Nat) : parity (2 ^ k) = true := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hne0 : 2 ^ (k + 1) ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos (k + 1))
    rw [parity_eq]; simp only [hne0, ↓reduceIte]
    have hbit0 : (2 ^ (k + 1)).testBit 0 = false := by
      rw [testBit_two_pow_eq]
      simp
    have hshr : (2 ^ (k + 1)) >>> 1 = 2 ^ k := by
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.pow_succ]; omega
    rw [hbit0, hshr, ih]
    rfl

theorem eq_of_mod_and_parity {w x y : Nat}
    (hx : x < 2 ^ (w + 1)) (hy : y < 2 ^ (w + 1))
    (hmod : x % 2 ^ w = y % 2 ^ w) (hpar : parity x = parity y) : x = y := by
  have hxor_split : ∀ n, n < 2 ^ (w + 1) →
      n = (n % 2 ^ w) ^^^ (if n.testBit w then 2 ^ w else 0) := by
    intro n hn
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, testBit_mod_two_pow]
    by_cases hlt : i < w
    · have hhi : (if n.testBit w then 2 ^ w else 0).testBit i = false := by
        cases n.testBit w
        · exact Nat.zero_testBit i
        · simp only [↓reduceIte, testBit_two_pow_eq]
          have hne : ¬ (w = i) := by omega
          simp [hne]
      simp [hlt, hhi]
    · by_cases hiw : i = w
      · subst hiw
        have hnotlt : ¬ (i < i) := Nat.lt_irrefl i
        simp only [hnotlt, decide_false, Bool.false_and, Bool.false_xor]
        cases hb : n.testBit i
        · simp
        · simp
      · have hnotlt : ¬ (i < w) := by omega
        have hhi : (if n.testBit w then 2 ^ w else 0).testBit i = false := by
          cases n.testBit w
          · exact Nat.zero_testBit i
          · simp only [↓reduceIte, testBit_two_pow_eq]
            have hne : ¬ (w = i) := by omega
            simp [hne]
        rw [testBit_eq_false_of_lt_pow hn (by omega)]
        simp [hnotlt, hhi]
  have hpar_split : ∀ n, n < 2 ^ (w + 1) →
      parity n = Bool.xor (parity (n % 2 ^ w)) (n.testBit w) := by
    intro n hn
    have hp := congrArg parity (hxor_split n hn)
    rw [hp, parity_xor]
    cases n.testBit w
    · rfl
    · simp only [↓reduceIte, parity_two_pow]
  have hbitw : x.testBit w = y.testBit w := by
    have px := hpar_split x hx
    have py := hpar_split y hy
    rw [hpar, hmod] at px
    rw [px] at py
    cases hpy0 : parity (y % 2 ^ w) <;> cases hxw : x.testBit w <;> cases hyw : y.testBit w <;>
      simp only [hpy0, hxw, hyw] at py <;> first | rfl | cases py
  rw [hxor_split x hx, hxor_split y hy, hmod, hbitw]

/-- THEOREM 5 (Full Untruncated Parity-Closed Gray Carry-Defect Fiber Law):
    For EVERY `w : Nat`, EVERY carry-in `c0 : Bool`, and EVERY untruncated target `z < 2^(w+1)`:
    `#{(a, b) ∈ [0, 2^w)^2 : G(C_{c0}(a, b)) = z} = 3^(w - popcount(z % 2^w))` if `parity z = c0`,
    and `0` if `parity z ≠ c0`. -/
theorem gray_carry_full_fiber_count (w : Nat) (c0 : Bool) (z : Nat) (hz : z < 2 ^ (w + 1)) :
    countPairs w (fun a b => decide (gray (carryWord a b c0) = z)) =
      if parity z = c0 then 3 ^ (w - popcount (z % 2 ^ w)) else 0 := by
  by_cases hp : parity z = c0
  · simp only [hp, ↓reduceIte]
    rw [← gray_carry_whitening_binary w c0 (z % 2 ^ w) (Nat.mod_lt z (Nat.two_pow_pos w))]
    apply countPairs_congr
    intro a b ha hb
    have hgc_lt : gray (carryWord a b c0) < 2 ^ (w + 1) :=
      gray_lt_two_pow (carryWord_lt_two_pow_succ ha hb)
    have hiff : gray (carryWord a b c0) = z ↔ gray (carryWord a b c0) % 2 ^ w = z % 2 ^ w := by
      constructor
      · intro heq; rw [heq]
      · intro hmod
        exact eq_of_mod_and_parity hgc_lt hz hmod (by rw [parity_gray_carryWord, hp])
    by_cases h : gray (carryWord a b c0) = z
    · simp [h]
    · have h2 : ¬ (gray (carryWord a b c0) % 2 ^ w = z % 2 ^ w) := fun hm => h (hiff.mpr hm)
      simp [h, h2]
  · simp only [hp, ↓reduceIte]
    rw [← countPairs_false w]
    apply countPairs_congr
    intro a b _ _
    have hne : gray (carryWord a b c0) ≠ z := by
      intro heq
      have := congrArg parity heq
      rw [parity_gray_carryWord] at this
      exact hp this.symm
    simp [hne]

/-! ===========================================================================
    PART 3B: General Radix-B Engine, Multi-Operand Impossibility & (k, B) Dichotomy
    =========================================================================== -/

/-! ### Theorem 6: Universal Base-B Carry-Transition Whitening Family (`∀ B ≥ 2, ∀ w`) -/

theorem sumNat_mul_const (n c : Nat) (f : Nat → Nat) :
    sumNat n (fun k => f k * c) = sumNat n f * c := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih => simp only [sumNat, ih, Nat.add_mul]

theorem sumNat_mul_split (B n : Nat) (f : Nat → Nat) :
    sumNat (B * n) f = sumNat n (fun q => sumNat B (fun r => f (B * q + r))) := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih =>
    have hmul : B * (k + 1) = B * k + B := Nat.mul_succ B k
    rw [hmul, sumNat_split, ih]
    rfl

theorem sumNat_swap (m n : Nat) (F : Nat → Nat → Nat) :
    sumNat m (fun i => sumNat n (fun j => F i j)) =
    sumNat n (fun j => sumNat m (fun i => F i j)) := by
  induction m with
  | zero => simp [sumNat, sumNat_zero]
  | succ k ih =>
    simp only [sumNat, ih]
    rw [← sumNat_add_fn]

theorem countPairsBase_congr {B w : Nat} {P Q : Nat → Nat → Bool}
    (h : ∀ a b, a < B ^ w → b < B ^ w → P a b = Q a b) :
    countPairsBase B w P = countPairsBase B w Q := by
  unfold countPairsBase
  apply sumNat_congr
  intro a ha
  apply sumNat_congr
  intro b hb
  rw [h a b ha hb]

theorem countPairsBase_false (B w : Nat) : countPairsBase B w (fun _ _ => false) = 0 := by
  unfold countPairsBase
  simp [sumNat_zero]

theorem countPairsBase_succ (B w : Nat) (P : Nat → Nat → Bool) :
    countPairsBase B (w + 1) P =
      sumNat B fun da => sumNat B fun db =>
        countPairsBase B w (fun a b => P (B * a + da) (B * b + db)) := by
  unfold countPairsBase
  rw [Nat.pow_succ, Nat.mul_comm (B ^ w) B, sumNat_mul_split]
  have hinner : ∀ a,
      sumNat (B * B ^ w) (fun b => if P a b then 1 else 0) =
      sumNat B (fun db => sumNat (B ^ w) (fun b => if P a (B * b + db) then 1 else 0)) := by
    intro a
    rw [sumNat_mul_split, sumNat_swap]
  simp only [hinner]
  rw [sumNat_swap (B ^ w) B]
  apply sumNat_congr
  intro da _
  rw [sumNat_swap (B ^ w) B]

/-- GENERAL RADIX-`B` BALANCED-FIBER WHITENING LIFTER:
    For ANY radix `B > 0` and ANY finite-state `RadixTransducer B S Out`,
    if `sliceCountBase B M s o = mult o` is independent of `s`, then
    for EVERY `w : Nat`, EVERY initial state `s0`, and EVERY `target : List Out`
    of length `w`, the exact fiber size in `[0, B^w)^2` is `∏_{o ∈ target} mult(o)`. -/
theorem radix_balanced_fiber_lift {B : Nat} (hB : 0 < B) {S Out : Type} [DecidableEq Out]
    (M : RadixTransducer B S Out) (mult : Out → Nat)
    (hbal : ∀ s o, sliceCountBase B M s o = mult o) :
    ∀ (w : Nat) (s0 : S) (target : List Out), target.length = w →
      countPairsBase B w (fun a b => decide (runListBase M s0 w a b = target)) =
        target.foldr (fun o acc => mult o * acc) 1 := by
  intro w
  induction w with
  | zero =>
    intro s0 target hlen
    cases target with
    | nil => simp [countPairsBase, sumNat, runListBase]
    | cons _ _ => simp at hlen
  | succ w ih =>
    intro s0 target hlen
    cases target with
    | nil => simp at hlen
    | cons o0 rest =>
      have hrest : rest.length = w := by simp at hlen; exact hlen
      rw [countPairsBase_succ]
      let R := rest.foldr (fun o acc => mult o * acc) 1
      have hbranch : ∀ da db, da < B → db < B →
          countPairsBase B w (fun a b =>
            decide (runListBase M s0 (w + 1) (B * a + da) (B * b + db) = o0 :: rest)) =
          (if M.out s0 da db = o0 then 1 else 0) * R := by
        intro da db hda hdb
        have hstep_eq : ∀ a b,
            decide (runListBase M s0 (w + 1) (B * a + da) (B * b + db) = o0 :: rest) =
            (decide (M.out s0 da db = o0) &&
             decide (runListBase M (M.step s0 da db) w a b = rest)) := by
          intro a b
          have hma : (B * a + da) % B = da := by
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hda]
          have hmb : (B * b + db) % B = db := by
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hdb]
          have hda' : (B * a + da) / B = a := by
            rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hda, Nat.add_zero]
          have hdb' : (B * b + db) / B = b := by
            rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hdb, Nat.add_zero]
          simp only [runListBase, hma, hmb, hda', hdb', List.cons.injEq]
          by_cases h1 : M.out s0 da db = o0 <;> simp [h1]
        rw [countPairsBase_congr (fun a b _ _ => hstep_eq a b)]
        by_cases h1 : M.out s0 da db = o0
        · simp only [h1, decide_true, Bool.true_and, ↓reduceIte, Nat.one_mul]
          exact ih (M.step s0 da db) rest hrest
        · simp only [h1, decide_false, Bool.false_and, ↓reduceIte, Nat.zero_mul]
          exact countPairsBase_false B w
      have hsum :
          (sumNat B fun da => sumNat B fun db =>
            countPairsBase B w (fun a b =>
              decide (runListBase M s0 (w + 1) (B * a + da) (B * b + db) = o0 :: rest))) =
          (sumNat B fun da => sumNat B fun db =>
            (if M.out s0 da db = o0 then 1 else 0) * R) := by
        apply sumNat_congr; intro da hda
        apply sumNat_congr; intro db hdb
        exact hbranch da db hda hdb
      rw [hsum]
      have hfact :
          (sumNat B fun da => sumNat B fun db => (if M.out s0 da db = o0 then 1 else 0) * R) =
          sliceCountBase B M s0 o0 * R := by
        unfold sliceCountBase
        have h1 : ∀ da,
            (sumNat B fun db => (if M.out s0 da db = o0 then 1 else 0) * R) =
            (sumNat B fun db => if M.out s0 da db = o0 then 1 else 0) * R :=
          fun da => sumNat_mul_const B R _
        simp only [h1, sumNat_mul_const]
      rw [hfact, hbal s0 o0]
      rfl

theorem carryDiffWordBase_lt (B : Nat) (c0 : Bool) (a b : Nat) :
    ∀ w, carryDiffWordBase B c0 a b w < 2 ^ w
  | 0     => by simp [carryDiffWordBase]
  | w + 1 => by
    simp only [carryDiffWordBase]
    have ih := carryDiffWordBase_lt B c0 a b w
    rw [Nat.pow_succ]
    cases Bool.xor (carryAtBase B a b c0 w) (carryAtBase B a b c0 (w + 1)) <;> simp <;> omega

theorem testBit_carryDiffWordBase (B : Nat) (c0 : Bool) (a b : Nat) :
    ∀ w i, i < w →
      (carryDiffWordBase B c0 a b w).testBit i =
        Bool.xor (carryAtBase B a b c0 i) (carryAtBase B a b c0 (i + 1))
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | w + 1, i, hi => by
    simp only [carryDiffWordBase]
    have hlt := carryDiffWordBase_lt B c0 a b w
    by_cases hltw : i < w
    · cases hb : Bool.xor (carryAtBase B a b c0 w) (carryAtBase B a b c0 (w + 1))
      · simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
        exact testBit_carryDiffWordBase B c0 a b w i hltw
      · simp only [Bool.toNat_true, Nat.one_mul]
        rw [Nat.add_comm, testBit_pow_two_add hlt hltw]
        exact testBit_carryDiffWordBase B c0 a b w i hltw
    · have heq : i = w := by omega
      subst heq
      cases hb : Bool.xor (carryAtBase B a b c0 i) (carryAtBase B a b c0 (i + 1))
      · simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
        exact testBit_eq_false_of_lt_pow hlt (Nat.le_refl i)
      · simp only [Bool.toNat_true, Nat.one_mul]
        rw [Nat.add_comm, testBit_pow_two_add_self hlt]

theorem carryAtBase_zero (B a b : Nat) (c0 : Bool) : carryAtBase B a b c0 0 = c0 := by
  unfold carryAtBase
  cases c0 <;> simp [Nat.mod_one]

theorem carryAtBase_succ_shift {B : Nat} (hB : 0 < B) (a b : Nat) (c0 : Bool) (i : Nat) :
    carryAtBase B a b c0 (i + 1) =
      carryAtBase B (a / B) (b / B) (decide (B ≤ a % B + b % B + c0.toNat)) i := by
  unfold carryAtBase
  have hpow : B ^ (i + 1) = B * B ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
  have hma : a % (B * B ^ i) = a % B + B * ((a / B) % B ^ i) := by
    rw [Nat.mod_mul, Nat.add_comm]
  have hmb : b % (B * B ^ i) = b % B + B * ((b / B) % B ^ i) := by
    rw [Nat.mod_mul, Nat.add_comm]
  rw [hpow, hma, hmb]
  have ha_mod : a % B < B := Nat.mod_lt a hB
  have hb_mod : b % B < B := Nat.mod_lt b hB
  let qa := (a / B) % B ^ i
  let qb := (b / B) % B ^ i
  let ra := a % B
  let rb := b % B
  change decide (B * B ^ i ≤ ra + B * qa + (rb + B * qb) + c0.toNat) =
         decide (B ^ i ≤ qa + qb + (decide (B ≤ ra + rb + c0.toNat)).toNat)
  have hre : ra + B * qa + (rb + B * qb) + c0.toNat = B * (qa + qb) + (ra + rb + c0.toNat) := by
    rw [Nat.mul_add]; omega
  rw [hre]
  by_cases h1 : B ≤ ra + rb + c0.toNat
  · simp only [h1, decide_true, Bool.toNat_true]
    have hlt2B : ra + rb + c0.toNat < 2 * B := by cases c0 <;> simp <;> omega
    have hiff : B * B ^ i ≤ B * (qa + qb) + (ra + rb + c0.toNat) ↔ B ^ i ≤ qa + qb + 1 := by
      constructor
      · intro hge
        by_cases hle : B ^ i ≤ qa + qb + 1
        · exact hle
        · have hle2 : qa + qb + 2 ≤ B ^ i := by omega
          have hmul : B * (qa + qb + 2) ≤ B * B ^ i := Nat.mul_le_mul_left B hle2
          have hexp : B * (qa + qb + 2) = B * (qa + qb) + 2 * B := by
            rw [Nat.mul_add, Nat.mul_comm B 2]
          omega
      · intro hge
        have hmul : B * B ^ i ≤ B * (qa + qb + 1) := Nat.mul_le_mul_left B hge
        rw [Nat.mul_add, Nat.mul_one] at hmul
        omega
    by_cases h2 : B ^ i ≤ qa + qb + 1
    · simp [h2, hiff.mpr h2]
    · have h2' : ¬ (B * B ^ i ≤ B * (qa + qb) + (ra + rb + c0.toNat)) := fun h => h2 (hiff.mp h)
      simp [h2, h2']
  · simp only [h1, decide_false, Bool.toNat_false, Nat.add_zero]
    have hiff : B * B ^ i ≤ B * (qa + qb) + (ra + rb + c0.toNat) ↔ B ^ i ≤ qa + qb := by
      constructor
      · intro hge
        by_cases hle : B ^ i ≤ qa + qb
        · exact hle
        · have hle2 : qa + qb + 1 ≤ B ^ i := by omega
          have hmul : B * (qa + qb + 1) ≤ B * B ^ i := Nat.mul_le_mul_left B hle2
          rw [Nat.mul_add, Nat.mul_one] at hmul
          omega
      · intro hge
        have hmul : B * B ^ i ≤ B * (qa + qb) := Nat.mul_le_mul_left B hge
        omega
    by_cases h2 : B ^ i ≤ qa + qb
    · simp [h2, hiff.mpr h2]
    · have h2' : ¬ (B * B ^ i ≤ B * (qa + qb) + (ra + rb + c0.toNat)) := fun h => h2 (hiff.mp h)
      simp [h2, h2']

theorem sumNat_id (n : Nat) : 2 * sumNat n (fun k => k) = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat, Nat.mul_add, ih]
    cases k with
    | zero => rfl
    | succ j =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul]
      omega

theorem sumNat_id_succ (n : Nat) : 2 * sumNat n (fun k => k + 1) = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat, Nat.mul_add, ih]
    rw [Nat.add_mul]
    omega

theorem sumNat_rev (n : Nat) (f : Nat → Nat) :
    sumNat n (fun k => f (n - 1 - k)) = sumNat n f := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : sumNat (k + 1) (fun j => f (k - j)) =
        f k + sumNat k (fun j => f (k - 1 - j)) := by
      have hsplit : sumNat (1 + k) (fun j => f (k - j)) =
          sumNat 1 (fun j => f (k - j)) + sumNat k (fun j => f (k - (1 + j))) :=
        sumNat_split 1 k (fun j => f (k - j))
      rw [Nat.add_comm 1 k] at hsplit
      rw [hsplit]
      simp only [sumNat, Nat.zero_add, Nat.sub_zero]
      congr 1
      apply sumNat_congr; intro j _; congr 1; omega
    have hsimp : sumNat (k + 1) (fun j => f (k + 1 - 1 - j)) =
        sumNat (k + 1) (fun j => f (k - j)) := by
      apply sumNat_congr; intro j _; congr 1
    rw [hsimp, h1, ih]
    simp only [sumNat]
    omega

theorem sumNat_ge_count (B m : Nat) (hm : m ≤ B) :
    sumNat B (fun db => if m ≤ db then 1 else 0) = B - m := by
  induction B with
  | zero => simp [sumNat]
  | succ k ih =>
    simp only [sumNat]
    by_cases hmk : m ≤ k
    · rw [ih hmk]; simp [hmk]; omega
    · have hmeq : m = k + 1 := by omega
      subst hmeq
      have h0 : sumNat k (fun db => if k + 1 ≤ db then 1 else 0) = sumNat k (fun _ => 0) := by
        apply sumNat_congr; intro db hdb
        have : ¬ (k + 1 ≤ db) := by omega
        simp [this]
      rw [h0, sumNat_zero]
      have : ¬ (k + 1 ≤ k) := by omega
      simp [this]

theorem sumNat_lt_count (B m : Nat) (hm : m ≤ B) :
    sumNat B (fun db => if db < m then 1 else 0) = m := by
  induction B with
  | zero => simp [sumNat]; omega
  | succ k ih =>
    simp only [sumNat]
    by_cases hmk : m ≤ k
    · rw [ih hmk]
      have : ¬ (k < m) := by omega
      simp [this]
    · have hmeq : m = k + 1 := by omega
      subst hmeq
      have hconst : ∀ n, sumNat n (fun _ => 1) = n := by
        intro n; induction n with | zero => rfl | succ j ihj => simp [sumNat, ihj]
      have hall : sumNat k (fun db => if db < k + 1 then 1 else 0) = sumNat k (fun _ => 1) := by
        apply sumNat_congr; intro db hdb
        have : db < k + 1 := by omega
        simp [this]
      rw [hall, hconst k]
      simp

/-- Infinite-family triangular-number balance certificate for ALL radices `B ≥ 2`. -/
theorem radixCarryDiff_balanced (B : Nat) (_hB : 2 ≤ B) (c o : Bool) :
    sliceCountBase B (radixCarryDiffTransducer B) c o = radixCarryDiffMult B o := by
  unfold sliceCountBase radixCarryDiffTransducer radixCarryDiffMult
  cases c <;> cases o
  · dsimp only
    have hinner : ∀ da, da < B →
        (sumNat B fun db => if (false ^^ decide (B ≤ da + db + false.toNat)) = false then 1 else 0) =
        B - da := by
      intro da hda
      rw [← sumNat_lt_count B (B - da) (by omega)]
      apply sumNat_congr; intro db _
      by_cases h : db < B - da
      · have h2 : ¬ (B ≤ da + db) := by omega
        simp [h, h2]
      · have h2 : B ≤ da + db := by omega
        simp [h, h2]
    rw [sumNat_congr hinner]
    have hrev : sumNat B (fun da => B - da) = sumNat B (fun da => da + 1) := by
      rw [← sumNat_rev B (fun da => da + 1)]
      apply sumNat_congr; intro da hda; omega
    rw [hrev]
    have h2 := sumNat_id_succ B
    omega
  · dsimp only
    have hinner : ∀ da, da < B →
        (sumNat B fun db => if (false ^^ decide (B ≤ da + db + false.toNat)) = true then 1 else 0) =
        da := by
      intro da hda
      have hge := sumNat_ge_count B (B - da) (by omega)
      have hsub : B - (B - da) = da := by omega
      have heq : (sumNat B fun db => if (false ^^ decide (B ≤ da + db + false.toNat)) = true then 1 else 0) =
                 (sumNat B fun db => if B - da ≤ db then 1 else 0) := by
        apply sumNat_congr; intro db _
        by_cases h : B - da ≤ db
        · have h2 : B ≤ da + db := by omega
          simp [h, h2]
        · have h2 : ¬ (B ≤ da + db) := by omega
          simp [h, h2]
      rw [heq, hge, hsub]
    rw [sumNat_congr hinner]
    have h2 := sumNat_id B
    omega
  · dsimp only
    have hinner : ∀ da, da < B →
        (sumNat B fun db => if (true ^^ decide (B ≤ da + db + true.toNat)) = false then 1 else 0) =
        da + 1 := by
      intro da hda
      have hge := sumNat_ge_count B (B - 1 - da) (by omega)
      have hsub : B - (B - 1 - da) = da + 1 := by omega
      have heq : (sumNat B fun db => if (true ^^ decide (B ≤ da + db + true.toNat)) = false then 1 else 0) =
                 (sumNat B fun db => if B - 1 - da ≤ db then 1 else 0) := by
        apply sumNat_congr; intro db _
        by_cases h : B - 1 - da ≤ db
        · have h2 : B ≤ da + db + 1 := by omega
          simp [h, h2]
        · have h2 : ¬ (B ≤ da + db + 1) := by omega
          simp [h, h2]
      rw [heq, hge, hsub]
    rw [sumNat_congr hinner]
    have h2 := sumNat_id_succ B
    omega
  · dsimp only
    have hinner : ∀ da, da < B →
        (sumNat B fun db => if (true ^^ decide (B ≤ da + db + true.toNat)) = true then 1 else 0) =
        B - 1 - da := by
      intro da hda
      rw [← sumNat_lt_count B (B - 1 - da) (by omega)]
      apply sumNat_congr; intro db _
      by_cases h : db < B - 1 - da
      · have h2 : ¬ (B ≤ da + db + 1) := by omega
        simp [h, h2]
      · have h2 : B ≤ da + db + 1 := by omega
        simp [h, h2]
    rw [sumNat_congr hinner, sumNat_rev B (fun da => da)]
    have h2 := sumNat_id B
    omega

theorem runListBase_carryDiff_eq_wordBits {B : Nat} (hB : 0 < B) :
    ∀ w c0 a b,
      runListBase (radixCarryDiffTransducer B) c0 w a b =
        wordBits w (carryDiffWordBase B c0 a b w) := by
  intro w
  induction w with
  | zero => intros; rfl
  | succ w ih =>
    intro c0 a b
    have hbit0 : (carryDiffWordBase B c0 a b (w + 1)).testBit 0 =
        Bool.xor c0 (decide (B ≤ a % B + b % B + c0.toNat)) := by
      rw [testBit_carryDiffWordBase B c0 a b (w + 1) 0 (by omega),
          carryAtBase_zero, carryAtBase_succ_shift hB, carryAtBase_zero]
    have hdiv2 : carryDiffWordBase B c0 a b (w + 1) / 2 =
        carryDiffWordBase B (decide (B ≤ a % B + b % B + c0.toNat)) (a / B) (b / B) w := by
      have hlt1 : carryDiffWordBase B c0 a b (w + 1) / 2 < 2 ^ w := by
        have := carryDiffWordBase_lt B c0 a b (w + 1)
        rw [Nat.pow_succ] at this; omega
      have hlt2 := carryDiffWordBase_lt B (decide (B ≤ a % B + b % B + c0.toNat)) (a / B) (b / B) w
      apply eq_of_testBit_lt hlt1 hlt2
      intro i hi
      rw [← testBit_succ_div2,
          testBit_carryDiffWordBase B c0 a b (w + 1) (i + 1) (by omega),
          testBit_carryDiffWordBase B _ (a / B) (b / B) w i hi,
          carryAtBase_succ_shift hB, carryAtBase_succ_shift hB]
    change Bool.xor c0 (decide (B ≤ a % B + b % B + c0.toNat)) ::
             runListBase (radixCarryDiffTransducer B) (decide (B ≤ a % B + b % B + c0.toNat)) w (a / B) (b / B) =
           (carryDiffWordBase B c0 a b (w + 1)).testBit 0 ::
             wordBits w (carryDiffWordBase B c0 a b (w + 1) / 2)
    rw [hbit0, hdiv2, ih]

theorem wordBits_foldr_radixMult (B : Nat) : ∀ w z, z < 2 ^ w →
    (wordBits w z).foldr (fun o acc => radixCarryDiffMult B o * acc) 1 =
      (B * (B + 1) / 2) ^ (w - popcount z) * (B * (B - 1) / 2) ^ (popcount z)
  | 0, z, hz => by
    have : z = 0 := by omega
    subst this; rfl
  | w + 1, z, hz => by
    have hz' : z / 2 < 2 ^ w := by rw [Nat.pow_succ] at hz; omega
    have ih := wordBits_foldr_radixMult B w (z / 2) hz'
    simp only [wordBits, List.foldr_cons]
    rw [ih]
    have hpz : popcount z = (z.testBit 0).toNat + popcount (z / 2) := by
      rw [← popcount_two_mul_add_bool (z / 2) (z.testBit 0), nat_div2_decomp]
    have hle := popcount_le_width w (z / 2) hz'
    let m0 := B * (B + 1) / 2
    let m1 := B * (B - 1) / 2
    cases hz0 : z.testBit 0
    · simp only [radixCarryDiffMult, hpz, hz0, Bool.toNat_false, Nat.zero_add]
      change m0 * (m0 ^ (w - popcount (z / 2)) * m1 ^ popcount (z / 2)) =
             m0 ^ (w + 1 - popcount (z / 2)) * m1 ^ popcount (z / 2)
      have hexp : w + 1 - popcount (z / 2) = (w - popcount (z / 2)) + 1 := by omega
      rw [hexp, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm m0 (m0 ^ (w - popcount (z / 2)))]
    · simp only [radixCarryDiffMult, hpz, hz0, Bool.toNat_true]
      change m1 * (m0 ^ (w - popcount (z / 2)) * m1 ^ popcount (z / 2)) =
             m0 ^ (w + 1 - (1 + popcount (z / 2))) * m1 ^ (1 + popcount (z / 2))
      have hexp1 : w + 1 - (1 + popcount (z / 2)) = w - popcount (z / 2) := by omega
      have hexp2 : 1 + popcount (z / 2) = popcount (z / 2) + 1 := by omega
      rw [hexp1, hexp2, Nat.pow_succ]
      rw [Nat.mul_left_comm m1 (m0 ^ (w - popcount (z / 2))) (m1 ^ popcount (z / 2))]
      rw [Nat.mul_comm m1 (m1 ^ popcount (z / 2))]

/-- THEOREM 6 (Universal Base-`B` Carry-Transition Whitening Family):
    For EVERY radix `B ≥ 2`, EVERY width `w : Nat`, EVERY carry-in `c0 : Bool`,
    and EVERY binary carry-transition word `z < 2^w`:
    `#{(a, b) ∈ [0, B^w)^2 : carryDiffWordBase B c0 a b w = z}`
    `= (B*(B+1)/2)^(w - popcount z) * (B*(B-1)/2)^(popcount z)`.
    Setting `B = 2` recovers Theorem 4 (`3^(w - popcount z)`). -/
theorem radix_carry_whitening_law (B : Nat) (hB : 2 ≤ B) (w : Nat) (c0 : Bool)
    (z : Nat) (hz : z < 2 ^ w) :
    countPairsBase B w (fun a b => decide (carryDiffWordBase B c0 a b w = z)) =
      (B * (B + 1) / 2) ^ (w - popcount z) * (B * (B - 1) / 2) ^ (popcount z) := by
  have hBpos : 0 < B := by omega
  have hlift := radix_balanced_fiber_lift hBpos (radixCarryDiffTransducer B) (radixCarryDiffMult B)
    (radixCarryDiff_balanced B hB) w c0 (wordBits w z) (wordBits_length w z)
  rw [wordBits_foldr_radixMult B w z hz] at hlift
  rw [← hlift]
  apply countPairsBase_congr
  intro a b _ _
  rw [runListBase_carryDiff_eq_wordBits hBpos w c0 a b]
  have hlt := carryDiffWordBase_lt B c0 a b w
  by_cases h : carryDiffWordBase B c0 a b w = z
  · have h2 := (wordBits_inj w _ z hlt hz).mpr h
    simp [h]
  · have h2 : ¬ (wordBits w (carryDiffWordBase B c0 a b w) = wordBits w z) :=
      fun heq => h ((wordBits_inj w _ z hlt hz).mp heq)
    simp [h, h2]

/-! ### Theorem 7: Multi-Operand Gray Carry-Defect Whitening Impossibility (`∀ k ≥ 3`) -/

theorem sumInt_congr {n : Nat} {f g : Nat → Int} (h : ∀ k, k < n → f k = g k) :
    sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

theorem sumInt_add_fn (n : Nat) (f g : Nat → Int) :
    sumInt n (fun k => f k + g k) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_neg (n : Nat) (f : Nat → Int) :
    sumInt n (fun k => - f k) = - sumInt n f := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_two_mul (n : Nat) (f : Nat → Int) :
    sumInt (2 * n) f = sumInt n (fun k => f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1]
    simp only [sumInt]
    rw [ih]
    omega

theorem natCast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Int.pow_succ]
    change (((2 ^ k : Nat) : Int) * (2 : Int)) = (2 : Int) ^ k * 2
    rw [ih]

theorem multiCarryBias_eq_sumInt (k c : Nat) :
    multiCarryBias k c =
      sumInt (2 ^ k) fun v => if (c + (c + popcount v) / 2) % 2 = 0 then 1 else -1 := by
  unfold multiCarryBias multiCarrySlice1
  have hgen : ∀ (n : Nat) (P : Nat → Prop) [DecidablePred P],
      (n : Int) - 2 * (sumNat n (fun v => if P v then 1 else 0) : Int) =
      sumInt n (fun v => if P v then -1 else 1) := by
    intro n P _
    induction n with
    | zero => rfl
    | succ m ih =>
      simp only [sumNat, sumInt]
      by_cases hp : P m <;> simp [hp] at ih ⊢ <;> omega
  have h1 := hgen (2 ^ k) (fun v => (c + (c + popcount v) / 2) % 2 = 1)
  rw [natCast_two_pow] at h1
  rw [h1]
  apply sumInt_congr
  intro v _
  by_cases h : (c + (c + popcount v) / 2) % 2 = 0
  · simp [h]
  · have heq : (c + (c + popcount v) / 2) % 2 = 1 := by omega
    simp [heq]

theorem multiCarryBias_eq_sign_carrySumBias (k c : Nat) :
    multiCarryBias k c = (if c % 2 = 0 then (1 : Int) else -1) * carrySumBias k c := by
  rw [multiCarryBias_eq_sumInt]
  unfold carrySumBias
  by_cases hc : c % 2 = 0
  · simp only [hc, ↓reduceIte, Int.one_mul]
    apply sumInt_congr; intro v _
    have hiff : (c + (c + popcount v) / 2) % 2 = 0 ↔ ((c + popcount v) / 2) % 2 = 0 := by omega
    by_cases h : ((c + popcount v) / 2) % 2 = 0
    · simp [h, hiff.mpr h]
    · have h2 : ¬ ((c + (c + popcount v) / 2) % 2 = 0) := fun hm => h (hiff.mp hm)
      simp [h, h2]
  · simp only [hc, ↓reduceIte, Int.neg_mul, Int.one_mul]
    rw [← sumInt_neg]
    apply sumInt_congr; intro v _
    have hiff : (c + (c + popcount v) / 2) % 2 = 0 ↔ ¬ (((c + popcount v) / 2) % 2 = 0) := by omega
    by_cases h : ((c + popcount v) / 2) % 2 = 0
    · have h2 : ¬ ((c + (c + popcount v) / 2) % 2 = 0) := fun hm => (hiff.mp hm) h
      simp [h, h2]
    · simp [h, hiff.mpr h]

theorem carrySumBias_add_two (k s0 : Nat) :
    carrySumBias k (s0 + 2) = - carrySumBias k s0 := by
  unfold carrySumBias
  rw [← sumInt_neg]
  apply sumInt_congr; intro v _
  have h1 : (s0 + 2 + popcount v) / 2 = (s0 + popcount v) / 2 + 1 := by omega
  rw [h1]
  by_cases h : ((s0 + popcount v) / 2) % 2 = 0
  · have h2 : ¬ (((s0 + popcount v) / 2 + 1) % 2 = 0) := by omega
    simp [h, h2]
  · have h2 : ((s0 + popcount v) / 2 + 1) % 2 = 0 := by omega
    simp [h, h2]

theorem carrySumBias_succ (k s0 : Nat) :
    carrySumBias (k + 1) s0 = carrySumBias k s0 + carrySumBias k (s0 + 1) := by
  unfold carrySumBias
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, sumInt_two_mul, sumInt_add_fn]
  congr 1
  · apply sumInt_congr; intro v _
    have hp : popcount (2 * v) = popcount v := by
      simpa using popcount_two_mul_add_bool v false
    rw [hp]
  · apply sumInt_congr; intro v _
    have hp : popcount (2 * v + 1) = 1 + popcount v := by
      simpa using popcount_two_mul_add_bool v true
    have hre : s0 + (1 + popcount v) = s0 + 1 + popcount v := by omega
    rw [hp, hre]

/-- Exact Gaussian-Integer Norm Identity:
    `S(k, 0)^2 + S(k, 1)^2 = 2^(k + 1)` for ALL `k : Nat`. -/
theorem carrySumBias_norm_sq : ∀ k,
    carrySumBias k 0 * carrySumBias k 0 + carrySumBias k 1 * carrySumBias k 1 = (2 : Int) ^ (k + 1)
  | 0 => by decide
  | k + 1 => by
    have ih := carrySumBias_norm_sq k
    rw [carrySumBias_succ k 0, carrySumBias_succ k 1, carrySumBias_add_two k 0]
    let A := carrySumBias k 0
    let B := carrySumBias k 1
    change (A + B) * (A + B) + (B + -A) * (B + -A) = (2 : Int) ^ (k + 1 + 1)
    have halg : (A + B) * (A + B) + (B + -A) * (B + -A) = 2 * (A * A + B * B) := by
      have h1 : (A + B) * (A + B) = A * A + 2 * (A * B) + B * B := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm B A]; omega
      have h2 : (B + -A) * (B + -A) = B * B - 2 * (A * B) + A * A := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_neg, Int.neg_mul,
            Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_comm B A]; omega
      omega
    rw [halg, ih, Int.mul_comm 2 ((2 : Int) ^ (k + 1)), ← Int.pow_succ]

theorem int_two_pow_pos (n : Nat) : (0 : Int) < (2 : Int) ^ n := by
  induction n with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

/-- THEOREM 7 (Multi-Operand Gray Carry-Defect Whitening Impossibility Dichotomy):
    1. Exact Gaussian-norm law: `D(k, 0)^2 + D(k, 1)^2 = 2^(k + 1)` and `D(k, 2) = -D(k, 0)` ∀ `k`.
    2. For EVERY `k ≥ 3`, the `k`-operand binary Gray carry-defect transducer CANNOT be
       slice-balanced across its reachable carry states `{0, ..., k - 1}`:
       either `c = 0` vs `c = 2` or `c = 0` vs `c = 1` exhibits strict imbalance.
    3. Together with `k = 2` (`multiCarrySlice1 2 0 = 1 ∧ multiCarrySlice1 2 1 = 1`),
       `k = 2` is the UNIQUE non-trivial arity (`k ≥ 2`) admitting balanced Gray carry whitening! -/
theorem k_operand_whitening_impossibility (k : Nat) (hk : 3 ≤ k) :
    multiCarrySlice1 k 0 ≠ multiCarrySlice1 k 2 ∨
    multiCarrySlice1 k 0 ≠ multiCarrySlice1 k 1 := by
  have _ := hk
  by_cases h02 : multiCarrySlice1 k 0 = multiCarrySlice1 k 2
  · by_cases h01 : multiCarrySlice1 k 0 = multiCarrySlice1 k 1
    · exfalso
      have hb02 : multiCarryBias k 0 = multiCarryBias k 2 := by
        unfold multiCarryBias; rw [h02]
      have hb01 : multiCarryBias k 0 = multiCarryBias k 1 := by
        unfold multiCarryBias; rw [h01]
      have hs0 : multiCarryBias k 0 = carrySumBias k 0 := by
        rw [multiCarryBias_eq_sign_carrySumBias]; simp
      have hs1 : multiCarryBias k 1 = - carrySumBias k 1 := by
        rw [multiCarryBias_eq_sign_carrySumBias]; simp
      have hs2 : multiCarryBias k 2 = - carrySumBias k 0 := by
        rw [multiCarryBias_eq_sign_carrySumBias, show (2 : Nat) = 0 + 2 from rfl,
            carrySumBias_add_two]; simp
      have hA0 : carrySumBias k 0 = 0 := by rw [hs0, hs2] at hb02; omega
      have hB0 : carrySumBias k 1 = 0 := by rw [hs0, hs1, hA0] at hb01; omega
      have hnorm := carrySumBias_norm_sq k
      rw [hA0, hB0] at hnorm
      have hpos := int_two_pow_pos (k + 1)
      omega
    · exact Or.inr h01
  · exact Or.inl h02

/-! ### Theorem 8: Binary Uniqueness of Carry-Borrow Orthogonality (`∀ B ≥ 3`) -/

/-- THEOREM 8 (Binary Uniqueness of Carry-Borrow Orthogonality):
    For EVERY radix `B ≥ 3`, there exist base-`B` digits `d1, d2 < B` (explicitly `1` and `B - 1`)
    such that from `(c, bor) = (false, false)`, BOTH the carry-transition bit `δ⁺` and the
    borrow-transition bit `δ⁻` equal `true` simultaneously. Thus `B = 2` is the UNIQUE radix
    where Carry-Borrow Gray Orthogonality holds. -/
theorem radix_carry_borrow_orthogonality_binary_unique (B : Nat) (hB : 3 ≤ B) :
    ∃ d1 d2, d1 < B ∧ d2 < B ∧
      Bool.xor false (decide (B ≤ d1 + d2)) = true ∧
      Bool.xor false (decide (d1 < d2)) = true := by
  refine ⟨1, B - 1, by omega, by omega, ?_, ?_⟩
  · have h1 : B ≤ 1 + (B - 1) := by omega
    simp [h1]
  · have h2 : 1 < B - 1 := by omega
    simp [h2]

/-! ===========================================================================
    PART 4: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples
    =========================================================================== -/

/-- Non-vacuity witness for Theorem 0: concrete non-trivial Gray addition with carries
    (`G⁻¹(13) = 9`, `G⁻¹(11) = 13`, `9 + 13 = 22`, `G(22) = 29`). -/
example : grayAddWith 13 11 false = 29 ∧
    (∀ i < 6, (grayAddWith 13 11 false).testBit i =
      outAt grayAddTransducer4 (Bool.xor (parity 13) (parity 11), parity 13) 13 11 i) := by
  decide

/-- Non-vacuity witness for Theorem 1: `a = 5, b = 3` where plain binary `C & B = 4 ≠ 0`
    yet Gray-encoded `G(C) & G(B) = 0` and `G(C) + G(B) = G(8) ^^^ G(2) = 15`. -/
example :
    (carryWord 5 3 false &&& borrowWord 5 3 false = 4) ∧
    (gray (carryWord 5 3 false) &&& gray (borrowWord 5 3 false) = 0) ∧
    (gray (carryWord 5 3 false) + gray (borrowWord 5 3 false) = gray 8 ^^^ gray 2) := by
  decide

/-- Non-vacuity witness for Theorem 2: explicit bijection round-trip at `w = 4`, `(a, b) = (11, 7)`. -/
example :
    let p := phiMap 4 false false 11 7
    p = (12, 13) ∧ phiMapInv 4 false false p.1 p.2 = (11, 7) := by
  decide

/-- Non-vacuity witness for Theorems 3, 4, 5 at `w = 3`:
    - Joint fiber `(u, v) = (5, 2)` (disjoint, weights 2 and 1): count = `2^(3 - 2 - 1) = 1`
    - Gray-coord whitening target `z = 5` (weight 2): count = `3^(3 - 2) = 3`
    - Full untruncated target `z = 13` (parity 1, `c0 = true`, `13 % 8 = 5`): count = `3^(3 - 2) = 3`. -/
example :
    countPairs 3 (fun a b =>
      decide (gray (carryWord a b false) % 8 = 5 ∧ gray (borrowWordFull 3 a b false) % 8 = 2)) = 1 ∧
    countPairs 3 (fun x y => decide ((grayAddWith x y false ^^^ x ^^^ y) % 8 = 5)) = 3 ∧
    countPairs 3 (fun a b => decide (gray (carryWord a b true) = 13)) = 3 := by
  decide

/-- Sharpness 1: Dropping `G` breaks Carry-Borrow Orthogonality at `(a, b) = (5, 3)`. -/
theorem sharpness_no_gray_breaks_orthogonality :
    carryWord 5 3 false &&& borrowWord 5 3 false ≠ 0 := by decide

/-- Sharpness 2: Replacing `G` by `G²` breaks Carry-Borrow Orthogonality at `(a, b) = (5, 3)`. -/
theorem sharpness_gray_squared_breaks_orthogonality :
    gray (gray (carryWord 5 3 false)) &&& gray (gray (borrowWord 5 3 false)) ≠ 0 := by decide

/-- Sharpness 3: Modular `w`-bit truncation (dropping bit `w` of carry/borrow) breaks
    orthogonality at `w = 3`, `(a, b) = (1, 3)`. -/
theorem sharpness_modular_truncation_breaks_orthogonality :
    let c3 := ((1 + 3) % 8) ^^^ 1 ^^^ 3
    let b3 := ((8 + 1 - 3) % 8) ^^^ 1 ^^^ 3
    gray c3 &&& gray b3 ≠ 0 := by decide

/-- Sharpness 4: Dropping `G` breaks the bijection `Phi_w` already at `w = 1`
    (collision: `(0, 0)` and `(1, 1)` have identical `(a ^^^ b, (C ^^^ B_full) % 2)`). -/
theorem sharpness_no_gray_breaks_bijection :
    (0 ^^^ 0, (carryWord 0 0 false ^^^ borrowWordFull 1 0 0 false) % 2) =
    (1 ^^^ 1, (carryWord 1 1 false ^^^ borrowWordFull 1 1 1 false) % 2) := by decide

/-- Sharpness 5: Dropping `G` breaks the `3^(w - popcount z)` whitening law already at `w = 1`. -/
theorem sharpness_no_gray_breaks_whitening :
    countPairs 1 (fun a b => decide (carryWord a b false % 2 = 1)) ≠ 3 ^ (1 - popcount 1) := by
  decide

/-- Sharpness 6: Violating parity-closure (`parity z ≠ c0`) in untruncated Theorem 5
    forces fiber count `0`, not `3^(w - popcount(z % 2^w))`. -/
theorem sharpness_parity_closure_necessary :
    countPairs 2 (fun a b => decide (gray (carryWord a b false) = 1)) = 0 ∧
    3 ^ (2 - popcount (1 % 4)) = 3 := by decide

/-- Non-vacuity witness for Theorems 6, 7, 8:
    - T6 at `B = 3, w = 2, z = 1` (`popcount 1 = 1`): count = `(3*4/2)^1 * (3*2/2)^1 = 18`
    - T7 positive/negative boundary: `k = 2` balanced (`1 = 1`), `k = 3` unbalanced (`4 ≠ 2`)
    - T8 at `B = 3`: `d1 = 1, d2 = 2` simultaneously triggers carry (`1+2 ≥ 3`) and borrow (`1 < 2`). -/
example :
    countPairsBase 3 2 (fun a b => decide (carryDiffWordBase 3 false a b 2 = 1)) = 18 ∧
    (multiCarrySlice1 2 0 = 1 ∧ multiCarrySlice1 2 1 = 1) ∧
    (multiCarrySlice1 3 0 = 4 ∧ multiCarrySlice1 3 1 = 2) := by
  decide

/-! ===========================================================================
    PART 5: Axiom Verification Receipts
    =========================================================================== -/

end GrayTransducerEngine
