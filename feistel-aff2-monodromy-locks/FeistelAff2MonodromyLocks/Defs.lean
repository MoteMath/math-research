/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`FeistelAff2MonodromyLocks`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace FeistelMonodromy
namespace Aff2
end Aff2

/-! ## Part 2: General Bit-Slice Monodromy Tower Engine (Finite → Infinite Bridge) -/

/-- A triangular (2-adic 1-Lipschitz) family of bit-vector round functions, equipped with
    its local bit-slice affine law `bit_k(f(R)) = (d_k(trunc_k R) && bit_k R) ^^ c_k(trunc_k R)`. -/
structure TriangularRoundFn where
  fn : (w : Nat) → BitVec w → BitVec w
  d  : (k : Nat) → BitVec k → Bool
  c  : (k : Nat) → BitVec k → Bool
  trunc_compat : ∀ (k : Nat) (R : BitVec (k + 1)),
    (fn (k + 1) R).setWidth k = fn k (R.setWidth k)
  topBit_law : ∀ (k : Nat) (R : BitVec (k + 1)),
    (fn (k + 1) R).getLsbD k = ((d k (R.setWidth k) && R.getLsbD k) ^^ c k (R.setWidth k))

/-- Balanced XOR-Feistel round on `BitVec w × BitVec w`. -/
def feistelStepF (f : TriangularRoundFn) (w : Nat) (s : BitVec w × BitVec w) :
    BitVec w × BitVec w :=
  (s.2, s.1 ^^^ f.fn w s.2)

/-- `n`-fold iteration of the Feistel round. -/
def feistelIter (f : TriangularRoundFn) (w : Nat) : Nat → (BitVec w × BitVec w) → (BitVec w × BitVec w)
  | 0, s => s
  | n + 1, s => feistelStepF f w (feistelIter f w n s)

/-- Minimal exact period predicate for a Feistel state. -/
def ExactPeriod (f : TriangularRoundFn) (w : Nat) (s : BitVec w × BitVec w) (p : Nat) : Prop :=
  0 < p ∧ feistelIter f w p s = s ∧ ∀ q, 0 < q → q < p → feistelIter f w q s ≠ s

/-! ## Part 3: Parametric Single-Trigger Compiler & Concrete Silicon BitVec Bridge -/

/-- Build a `BitVec w` whose `i`-th LSB is `g i` (for `i < w`). -/
def bvOfBits : (w : Nat) → (Nat → Bool) → BitVec w
  | 0, _ => 0#0
  | w + 1, g => BitVec.cons (g w) (bvOfBits w g)

theorem getLsbD_bvOfBits (w : Nat) (g : Nat → Bool) (i : Nat) (hi : i < w) :
    (bvOfBits w g).getLsbD i = g i := by
  induction w with
  | zero => omega
  | succ k ih =>
    simp only [bvOfBits, BitVec.getLsbD_cons]
    by_cases heq : i = k
    · subst heq; simp
    · have hik : i < k := by omega
      simp [heq, ih hik]

/-- The `w`-bit prefix of an infinite 2-adic trigger stream `τ : Nat → Bool`. -/
def triggerPrefix (τ : Nat → Bool) (w : Nat) : BitVec w :=
  bvOfBits w τ

theorem getLsbD_triggerPrefix (τ : Nat → Bool) (w i : Nat) (hi : i < w) :
    (triggerPrefix τ w).getLsbD i = τ i :=
  getLsbD_bvOfBits w τ i hi

/-- Decidable check whether bits `0 .. i-1` of `R` all match `τ`. -/
def prefixMatch (τ : Nat → Bool) (R : BitVec w) : Nat → Bool
  | 0 => true
  | i + 1 => prefixMatch τ R i && (R.getLsbD i == τ i)

theorem prefixMatch_iff (τ : Nat → Bool) {w : Nat} (R : BitVec w) :
    ∀ k, prefixMatch τ R k = true ↔ ∀ j, j < k → R.getLsbD j = τ j := by
  intro k
  induction k with
  | zero => simp [prefixMatch]
  | succ k ih =>
    simp only [prefixMatch, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjk : j < k
      · exact h1 j hjk
      · have : j = k := by omega
        subst this; exact h2
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k)⟩

theorem prefixMatch_eq_triggerPrefix (τ : Nat → Bool) (k : Nat) (R : BitVec (k + 1)) :
    prefixMatch τ R k = (R.setWidth k == triggerPrefix τ k) := by
  cases h : (R.setWidth k == triggerPrefix τ k)
  · simp only [beq_eq_false_iff_ne] at h
    cases hm : prefixMatch τ R k
    · rfl
    · exfalso; apply h
      have hall := (prefixMatch_iff τ R k).1 hm
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
          getLsbD_triggerPrefix τ k i hi, hall i hi]
  · simp only [beq_iff_eq] at h
    rw [(prefixMatch_iff τ R k).2]
    intro j hj
    have hbj := congrArg (fun v => v.getLsbD j) h
    rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and,
        getLsbD_triggerPrefix τ k j hj] at hbj
    exact hbj

/-- Parametric Single-Trigger Bit-Slice Round Function compiler for any 4-bit rule
    `(d_off, c_off, d_on, c_on)` and any 2-adic trigger stream `τ : Nat → Bool`. -/
def singleTriggerFn (d_off c_off d_on c_on : Bool) (τ : Nat → Bool) : TriangularRoundFn where
  fn w R := bvOfBits w fun i =>
    if prefixMatch τ R i
    then ((d_on && R.getLsbD i) ^^ c_on)
    else ((d_off && R.getLsbD i) ^^ c_off)
  d k R := if R == triggerPrefix τ k then d_on else d_off
  c k R := if R == triggerPrefix τ k then c_on else c_off
  trunc_compat k R := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hpm : prefixMatch τ R i = prefixMatch τ (R.setWidth k) i := by
      have hi' : i ≤ k := Nat.le_of_lt hi
      clear hi
      induction i with
      | zero => rfl
      | succ j ih =>
        have hjk : j < k := by omega
        simp only [prefixMatch, ih (Nat.le_of_lt hjk), BitVec.getLsbD_setWidth,
          decide_eq_true hjk, Bool.true_and]
    rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
        getLsbD_bvOfBits (k + 1) _ i (Nat.lt_succ_of_lt hi),
        getLsbD_bvOfBits k _ i hi, hpm,
        BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  topBit_law k R := by
    rw [getLsbD_bvOfBits (k + 1) _ k (Nat.lt_succ_self k), prefixMatch_eq_triggerPrefix]
    cases (R.setWidth k == triggerPrefix τ k) <;> rfl

/-! ## Part 4: Shared Orbit-Shift & Monodromy Lemmas -/

/-- Direct hardware Feistel iterator for any concrete `BitVec w → BitVec w` function. -/
def hwFeistelIter (g : (w : Nat) → BitVec w → BitVec w) (w : Nat) :
    Nat → (BitVec w × BitVec w) → (BitVec w × BitVec w)
  | 0, s => s
  | n + 1, s =>
    let u := hwFeistelIter g w n s
    (u.2, u.1 ^^^ g w u.2)

section TheoremIV

abbrev fIso (τ : Nat → Bool) : TriangularRoundFn :=
  singleTriggerFn false false false true τ

end TheoremIV
section TheoremI

abbrev fP12 (τ : Nat → Bool) : TriangularRoundFn :=
  singleTriggerFn true false false true τ

end TheoremI
section TheoremII

abbrev fAdd1 : TriangularRoundFn := singleTriggerFn true false true true (fun _ => true)
end TheoremII
section TheoremIII

abbrev fLsbGen (τ : Nat → Bool) : TriangularRoundFn :=
  singleTriggerFn false false true false τ

abbrev fLsb : TriangularRoundFn := fLsbGen (fun _ => false)

/-! ### Exact Binomial State/Cycle Count for `R &&& (-R)` (`fLsb`) -/

/-- Recursive enumeration of all `4^w` states in `(BitVec w)^2` aligned with the bit-slice tower. -/
def liftFour {k : Nat} (s : BitVec k × BitVec k) : List (BitVec (k + 1) × BitVec (k + 1)) :=
  [(BitVec.cons false s.1, BitVec.cons false s.2),
   (BitVec.cons false s.1, BitVec.cons true  s.2),
   (BitVec.cons true  s.1, BitVec.cons false s.2),
   (BitVec.cons true  s.1, BitVec.cons true  s.2)]

def allPairs : (w : Nat) → List (BitVec w × BitVec w)
  | 0 => [(0#0, 0#0)]
  | k + 1 => (allPairs k).flatMap liftFour

/-- Exact binomial coefficient `C(n, k)` (standalone core Lean 4). -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Decidable exact check for `ExactPeriod fLsb w s (3 ^ j)`. -/
def isPeriod3Pow (w j : Nat) (s : BitVec w × BitVec w) : Bool :=
  (feistelIter fLsb w (3 ^ j) s == s) &&
    (match j with
     | 0 => true
     | j' + 1 => !(feistelIter fLsb w (3 ^ j') s == s))

end TheoremIII
section NonVacuityAndSharpness
end NonVacuityAndSharpness
end FeistelMonodromy
