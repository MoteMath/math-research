/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CauchyHadamardFrobeniusReflect.Defs

/-!
# Cauchy–Hadamard–Frobenius Normal-Form Reflection Compiler (`certcomp-2`)

A self-contained, kernel-verified Lean 4.34.1 pure-silicon proof-reflection engine
for the double algebra `(^, &, clmul, <<<, >>>, 0, 1, allOnes)` over `BitVec w`.

Core Infinite Proof Mechanisms:
1. **Causal Projective-Limit Lifting Meta-Theorem** (`lift_stream_to_all_bitvec`):
   Lifts any equality of causal infinite bit-streams (`Nat → Bool ≅ F_2[[x]]`)
   uniformly to `∀ (w : Nat) (env : Nat → BitVec w)`.
2. **Verified Cauchy–Hadamard–Frobenius Normalizer & Certificate Checker**
   (`norm`, `cartierSplit`, `checkCert`, `reflect_all_bitvec`):
   Unifies Boolean-ring ANF (`^, &`), `F_2[x]` polynomial convolution (`clmul`),
   Frobenius squaring & residue-class fusion (`F^k`), E-mask shift/product collapse,
   Cartier 2-splitting (`ev, od`), and Gray-derivative cancellation (`Δ_r`) into a
   finite kernel-decidable certificate (`by decide`, 100% structural recursion).
3. **Dyadic Lane-Replication Lifting Meta-Theorem** (`reflect_all_scales_and_widths`):
   A single finite certificate at scale `r = 0` + syntactic `isLaneSafe` gate
   automatically discharges a **doubly infinite** family `∀ (r w : Nat), BitVec w`
   via Cartier bisimulation.

Zero `sorry`, zero `native_decide`, zero custom axioms, zero Mathlib/Lake overhead.
-/


-- ============================================================================
-- SECTION 1: Hardware BitVec Operations & Causal Bit-Stream Model (F_2[[x]])
-- ============================================================================

namespace CHReflect

/-- Stride-`2^r` left Gray derivative `Δ_r(a) = a ^^^ (a <<< 2^r)`. -/
def bvDelta {w : Nat} (r : Nat) (a : BitVec w) : BitVec w :=
  a ^^^ (a <<< (2 ^ r))

/-- Infinite causal bit-streams `Nat → Bool ≅ F_2[[x]]`. -/
abbrev Stream := Nat → Bool

/-- Finite XOR-sum `⨁_{i < n} f i` in `Bool`. -/
def xorSum : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, f => xorSum n f ^^ f n

def sZero : Stream := fun _ => false

def sOne : Stream := fun k => k == 0

def sAllOnes : Stream := fun _ => true

def sXor (a b : Stream) : Stream := fun k => a k ^^ b k

def sAnd (a b : Stream) : Stream := fun k => a k && b k

def sShl (a : Stream) (s : Nat) : Stream := fun k => if s ≤ k then a (k - s) else false

def sClmul (a b : Stream) : Stream :=
  fun k => xorSum (k + 1) (fun i => a i && b (k - i))

def sEv (a : Stream) : Stream := fun k => a (2 * k)

def sOd (a : Stream) : Stream := fun k => a (2 * k + 1)

def sFrob1 (a : Stream) : Stream := fun k => if k % 2 == 0 then a (k / 2) else false

def sFrob : Nat → Stream → Stream
  | 0, a => a
  | r + 1, a => sFrob1 (sFrob r a)

def sE (r : Nat) : Stream := sFrob r sAllOnes

-- Basic Bool helpers

theorem bxor_comm (a b : Bool) : (a ^^ b) = (b ^^ a) := by cases a <;> cases b <;> rfl

theorem bxor_assoc (a b c : Bool) : ((a ^^ b) ^^ c) = (a ^^ (b ^^ c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bxor_self (a : Bool) : (a ^^ a) = false := by cases a <;> rfl

theorem bxor_false (a : Bool) : (a ^^ false) = a := by cases a <;> rfl

theorem false_bxor (a : Bool) : (false ^^ a) = a := by cases a <;> rfl

theorem band_bxor_distrib_left (a b c : Bool) : (a && (b ^^ c)) = ((a && b) ^^ (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem band_bxor_distrib_right (a b c : Bool) : ((a ^^ b) && c) = ((a && c) ^^ (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

-- Lemmas on `xorSum`

theorem xorSum_congr (n : Nat) (f g : Nat → Bool) (h : ∀ i, i < n → f i = g i) :
    xorSum n f = xorSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorSum]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem xorSum_false (n : Nat) : xorSum n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorSum, ih]

theorem xorSum_eq_false (n : Nat) (f : Nat → Bool) (h : ∀ i, i < n → f i = false) :
    xorSum n f = false := by
  rw [xorSum_congr n f (fun _ => false) h]
  exact xorSum_false n

theorem xorSum_xor (n : Nat) (f g : Nat → Bool) :
    xorSum n (fun i => f i ^^ g i) = (xorSum n f ^^ xorSum n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorSum, ih]
    cases xorSum n f <;> cases xorSum n g <;> cases f n <;> cases g n <;> rfl

theorem xorSum_and_left (n : Nat) (c : Bool) (f : Nat → Bool) :
    xorSum n (fun i => c && f i) = (c && xorSum n f) := by
  induction n with
  | zero => cases c <;> rfl
  | succ n ih => simp only [xorSum, ih, band_bxor_distrib_left]

theorem xorSum_and_right (n : Nat) (f : Nat → Bool) (c : Bool) :
    xorSum n (fun i => f i && c) = (xorSum n f && c) := by
  induction n with
  | zero => cases c <;> rfl
  | succ n ih => simp only [xorSum, ih, band_bxor_distrib_right]

theorem xorSum_single (n j : Nat) (f : Nat → Bool) (hj : j < n)
    (h0 : ∀ i, i < n → i ≠ j → f i = false) :
    xorSum n f = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [xorSum]
    by_cases hjn : j = n
    · subst hjn
      rw [xorSum_eq_false j f (fun i hi => h0 i (by omega) (by omega)), false_bxor]
    · rw [ih (by omega) (fun i hi hne => h0 i (by omega) hne), h0 n (by omega) (Ne.symm hjn), bxor_false]

theorem xorSum_add (m n : Nat) (f : Nat → Bool) :
    xorSum (m + n) f = (xorSum m f ^^ xorSum n (fun i => f (m + i))) := by
  induction n with
  | zero => simp [xorSum]
  | succ n ih =>
    have h1 : m + (n + 1) = (m + n) + 1 := by omega
    rw [h1, xorSum, ih, xorSum, bxor_assoc]

theorem xorSum_succ_shift (n : Nat) (f : Nat → Bool) :
    xorSum (n + 1) f = (f 0 ^^ xorSum n (fun i => f (i + 1))) := by
  have h := xorSum_add 1 n f
  have h1 : 1 + n = n + 1 := by omega
  rw [h1] at h
  rw [h]
  simp only [xorSum, false_bxor]
  congr 1
  apply xorSum_congr
  intro i _; congr 1; omega

theorem xorSum_rev (n : Nat) (f : Nat → Bool) :
    xorSum n (fun i => f (n - 1 - i)) = xorSum n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorSum_succ_shift]
    have h0 : n + 1 - 1 - 0 = n := by omega
    rw [h0]
    have hsub : xorSum n (fun i => f (n + 1 - 1 - (i + 1))) = xorSum n (fun i => f (n - 1 - i)) := by
      apply xorSum_congr; intro i hi; congr 1; omega
    rw [hsub, ih, xorSum, bxor_comm]

theorem xorSum_swap (m n : Nat) (f : Nat → Nat → Bool) :
    xorSum m (fun i => xorSum n (fun j => f i j)) =
    xorSum n (fun j => xorSum m (fun i => f i j)) := by
  induction m with
  | zero => simp only [xorSum]; symm; exact xorSum_false n
  | succ m ih => simp only [xorSum]; rw [ih, ← xorSum_xor]

theorem xorSum_double (m : Nat) (f : Nat → Bool) :
    xorSum (2 * m) f = (xorSum m (fun i => f (2 * i)) ^^ xorSum m (fun i => f (2 * i + 1))) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h1, xorSum, xorSum, ih, xorSum, xorSum]
    cases xorSum m (fun i => f (2 * i)) <;>
    cases xorSum m (fun i => f (2 * i + 1)) <;>
    cases f (2 * m) <;>
    cases f (2 * m + 1) <;> rfl

theorem xorSum_symmetric (k : Nat) (f : Nat → Bool) (hsym : ∀ i, i ≤ k → f i = f (k - i)) :
    xorSum (k + 1) f = if k % 2 == 0 then f (k / 2) else false := by
  induction k using Nat.strongRecOn generalizing f with
  | ind k ih =>
    match k with
    | 0 => simp [xorSum]
    | 1 =>
      simp only [xorSum, false_bxor]
      have h01 : f 0 = f 1 := hsym 0 (by omega)
      rw [h01, bxor_self]; rfl
    | k' + 2 =>
      rw [xorSum, xorSum_succ_shift]
      have h0 : f 0 = f (k' + 2) := hsym 0 (by omega)
      rw [h0]
      have hcancel : ((f (k' + 2) ^^ xorSum (k' + 1) (fun i => f (i + 1))) ^^ f (k' + 2)) =
          xorSum (k' + 1) (fun i => f (i + 1)) := by
        cases f (k' + 2) <;> cases xorSum (k' + 1) (fun i => f (i + 1)) <;> rfl
      rw [hcancel]
      have hsym' : ∀ i, i ≤ k' → f (i + 1) = f (k' - i + 1) := by
        intro i hi
        have := hsym (i + 1) (by omega)
        have heq : k' + 2 - (i + 1) = k' - i + 1 := by omega
        rw [heq] at this; exact this
      rw [ih k' (by omega) (fun i => f (i + 1)) hsym']
      have hmod : (k' + 2) % 2 = k' % 2 := by omega
      have hdiv : (k' + 2) / 2 = k' / 2 + 1 := by omega
      rw [hmod, hdiv]

-- Algebraic Laws on `Stream`

theorem sXor_comm (a b : Stream) : sXor a b = sXor b a := by funext k; exact bxor_comm _ _

theorem sXor_assoc (a b c : Stream) : sXor (sXor a b) c = sXor a (sXor b c) := by funext k; exact bxor_assoc _ _ _

theorem sXor_self (a : Stream) : sXor a a = sZero := by funext k; exact bxor_self _

theorem sXor_zero (a : Stream) : sXor a sZero = a := by funext k; exact bxor_false _

theorem sZero_xor (a : Stream) : sXor sZero a = a := by funext k; exact false_bxor _

theorem sAnd_comm (a b : Stream) : sAnd a b = sAnd b a := by funext k; exact Bool.and_comm _ _

theorem sAnd_assoc (a b c : Stream) : sAnd (sAnd a b) c = sAnd a (sAnd b c) := by funext k; exact Bool.and_assoc _ _ _

theorem sAnd_self (a : Stream) : sAnd a a = a := by funext k; exact Bool.and_self _

theorem sAnd_zero (a : Stream) : sAnd a sZero = sZero := by funext k; exact Bool.and_false _

theorem sZero_and (a : Stream) : sAnd sZero a = sZero := by funext k; exact Bool.false_and _

theorem sAnd_allOnes (a : Stream) : sAnd a sAllOnes = a := by funext k; exact Bool.and_true _

theorem sAllOnes_and (a : Stream) : sAnd sAllOnes a = a := by funext k; exact Bool.true_and _

theorem sAnd_xor_left (a b c : Stream) : sAnd a (sXor b c) = sXor (sAnd a b) (sAnd a c) := by
  funext k; exact band_bxor_distrib_left _ _ _

theorem sAnd_xor_right (a b c : Stream) : sAnd (sXor a b) c = sXor (sAnd a c) (sAnd b c) := by
  funext k; exact band_bxor_distrib_right _ _ _

theorem sShl_zero (a : Stream) : sShl a 0 = a := by funext k; simp [sShl]

theorem sShl_sZero (s : Nat) : sShl sZero s = sZero := by funext k; simp [sShl, sZero]

theorem sShl_xor (a b : Stream) (s : Nat) : sShl (sXor a b) s = sXor (sShl a s) (sShl b s) := by
  funext k; simp only [sShl, sXor]; split <;> rfl

theorem sShl_and (a b : Stream) (s : Nat) : sShl (sAnd a b) s = sAnd (sShl a s) (sShl b s) := by
  funext k; simp only [sShl, sAnd]; split <;> rfl

theorem sShl_shl (a : Stream) (s t : Nat) : sShl (sShl a s) t = sShl a (s + t) := by
  funext k; simp only [sShl]
  by_cases ht : t ≤ k
  · by_cases hs : s ≤ k - t
    · have hst : s + t ≤ k := by omega
      have hsub : k - t - s = k - (s + t) := by omega
      simp [ht, hs, hst, hsub]
    · have hst : ¬ (s + t ≤ k) := by omega
      simp [ht, hs, hst]
  · have hst : ¬ (s + t ≤ k) := by omega
    simp [ht, hst]

theorem sClmul_comm (a b : Stream) : sClmul a b = sClmul b a := by
  funext k; simp only [sClmul]
  rw [← xorSum_rev (k + 1) (fun i => b i && a (k - i))]
  apply xorSum_congr; intro i hi
  have h1 : k + 1 - 1 - i = k - i := by omega
  have h2 : k - (k - i) = i := by omega
  rw [h1, h2, Bool.and_comm]

theorem sClmul_zero (a : Stream) : sClmul a sZero = sZero := by
  funext k; simp only [sClmul, sZero, Bool.and_false]; exact xorSum_false (k + 1)

theorem sZero_clmul (a : Stream) : sClmul sZero a = sZero := by
  rw [sClmul_comm]; exact sClmul_zero a

theorem sClmul_one (a : Stream) : sClmul a sOne = a := by
  funext k; simp only [sClmul, sOne]
  rw [xorSum_single (k + 1) k (fun i => a i && (k - i == 0)) (by omega)]
  · have h1 : k - k = 0 := by omega
    rw [h1]; simp
  · intro i hi hne
    have h1 : (k - i == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    rw [h1, Bool.and_false]

theorem sOne_clmul (a : Stream) : sClmul sOne a = a := by
  rw [sClmul_comm]; exact sClmul_one a

theorem sClmul_xor_left (a b c : Stream) :
    sClmul (sXor a b) c = sXor (sClmul a c) (sClmul b c) := by
  funext k; simp only [sClmul, sXor]; rw [← xorSum_xor]
  apply xorSum_congr; intro i _; exact band_bxor_distrib_right _ _ _

theorem sClmul_xor_right (a b c : Stream) :
    sClmul a (sXor b c) = sXor (sClmul a b) (sClmul a c) := by
  rw [sClmul_comm, sClmul_xor_left, sClmul_comm b a, sClmul_comm c a]

theorem sClmul_shl_left (a b : Stream) (s : Nat) :
    sClmul (sShl a s) b = sShl (sClmul a b) s := by
  funext k; simp only [sClmul, sShl]
  by_cases hsk : s ≤ k
  · simp only [hsk, ↓reduceIte]
    have hsplit : k + 1 = s + (k - s + 1) := by omega
    rw [hsplit, xorSum_add]
    have hz : xorSum s (fun i => (if s ≤ i then a (i - s) else false) && b (k - i)) = false := by
      apply xorSum_eq_false; intro i hi
      have hni : ¬ (s ≤ i) := by omega
      simp only [hni, ↓reduceIte, Bool.false_and]
    rw [hz, false_bxor]
    apply xorSum_congr; intro i hi
    have h1 : s ≤ s + i := by omega
    have h2 : s + i - s = i := by omega
    have h3 : k - (s + i) = k - s - i := by omega
    simp only [h1, ↓reduceIte, h2, h3]
  · simp only [hsk, ↓reduceIte]
    apply xorSum_eq_false; intro i hi
    have hni : ¬ (s ≤ i) := by omega
    simp only [hni, ↓reduceIte, Bool.false_and]

theorem sClmul_shl_right (a b : Stream) (s : Nat) :
    sClmul a (sShl b s) = sShl (sClmul a b) s := by
  rw [sClmul_comm, sClmul_shl_left, sClmul_comm]

theorem sClmul_assoc (a b c : Stream) :
    sClmul (sClmul a b) c = sClmul a (sClmul b c) := by
  funext k; simp only [sClmul]
  have hLHS :
      xorSum (k + 1) (fun t => xorSum (t + 1) (fun i => a i && b (t - i)) && c (k - t)) =
      xorSum (k + 1) (fun i => xorSum (k + 1) (fun j =>
        if i + j ≤ k then a i && b j && c (k - (i + j)) else false)) := by
    have hstep1 :
        xorSum (k + 1) (fun t => xorSum (t + 1) (fun i => a i && b (t - i)) && c (k - t)) =
        xorSum (k + 1) (fun t => xorSum (k + 1) (fun i =>
          if i ≤ t then a i && b (t - i) && c (k - t) else false)) := by
      apply xorSum_congr; intro t ht
      rw [← xorSum_and_right]
      have hlen : (t + 1) + (k - t) = k + 1 := by omega
      have hadd := xorSum_add (t + 1) (k - t) (fun i => if i ≤ t then a i && b (t - i) && c (k - t) else false)
      rw [hlen] at hadd
      rw [hadd]
      have htail : xorSum (k - t) (fun r =>
          if t + 1 + r ≤ t then a (t + 1 + r) && b (t - (t + 1 + r)) && c (k - t) else false) = false := by
        apply xorSum_eq_false; intro r _
        have hnt : ¬ (t + 1 + r ≤ t) := by omega
        simp only [hnt, ↓reduceIte]
      rw [htail, bxor_false]
      apply xorSum_congr; intro i hi
      have hit : i ≤ t := by omega
      simp only [hit, ↓reduceIte]
    rw [hstep1, xorSum_swap]
    apply xorSum_congr; intro i hi
    have hsplit1 : i + (k - i + 1) = k + 1 := by omega
    have hsplit2 : (k - i + 1) + i = k + 1 := by omega
    have hL := xorSum_add i (k - i + 1) (fun t => if i ≤ t then a i && b (t - i) && c (k - t) else false)
    rw [hsplit1] at hL
    have hR := xorSum_add (k - i + 1) i (fun j => if i + j ≤ k then a i && b j && c (k - (i + j)) else false)
    rw [hsplit2] at hR
    rw [hL, hR]
    have hpre : xorSum i (fun t => if i ≤ t then a i && b (t - i) && c (k - t) else false) = false := by
      apply xorSum_eq_false; intro t ht
      have hnt : ¬ (i ≤ t) := by omega
      simp only [hnt, ↓reduceIte]
    have hpost : xorSum i (fun r =>
        if i + (k - i + 1 + r) ≤ k then a i && b (k - i + 1 + r) && c (k - (i + (k - i + 1 + r))) else false) = false := by
      apply xorSum_eq_false; intro r _
      have hnk : ¬ (i + (k - i + 1 + r) ≤ k) := by omega
      simp only [hnk, ↓reduceIte]
    rw [hpre, false_bxor, hpost, bxor_false]
    apply xorSum_congr; intro j hj
    have h1 : i ≤ i + j := by omega
    have h2 : i + j - i = j := by omega
    have h3 : i + j ≤ k := by omega
    simp only [h1, h3, ↓reduceIte, h2]
  have hRHS :
      xorSum (k + 1) (fun i => a i && xorSum (k - i + 1) (fun j => b j && c (k - i - j))) =
      xorSum (k + 1) (fun i => xorSum (k + 1) (fun j =>
        if i + j ≤ k then a i && b j && c (k - (i + j)) else false)) := by
    apply xorSum_congr; intro i hi
    rw [← xorSum_and_left]
    have hsplit2 : (k - i + 1) + i = k + 1 := by omega
    have hR := xorSum_add (k - i + 1) i (fun j => if i + j ≤ k then a i && b j && c (k - (i + j)) else false)
    rw [hsplit2] at hR
    rw [hR]
    have hpost : xorSum i (fun r =>
        if i + (k - i + 1 + r) ≤ k then a i && b (k - i + 1 + r) && c (k - (i + (k - i + 1 + r))) else false) = false := by
      apply xorSum_eq_false; intro r _
      have hnk : ¬ (i + (k - i + 1 + r) ≤ k) := by omega
      simp only [hnk, ↓reduceIte]
    rw [hpost, bxor_false]
    apply xorSum_congr; intro j hj
    have h1 : i + j ≤ k := by omega
    have h2 : k - (i + j) = k - i - j := by omega
    simp only [h1, ↓reduceIte, h2, Bool.and_assoc]
  rw [hLHS, hRHS]

theorem sClmul_square_distrib (a b : Stream) :
    sClmul (sClmul a a) (sClmul b b) = sClmul (sClmul a b) (sClmul a b) := by
  calc
    sClmul (sClmul a a) (sClmul b b)
        = sClmul a (sClmul a (sClmul b b)) := sClmul_assoc a a (sClmul b b)
    _   = sClmul a (sClmul (sClmul a b) b) := by rw [← sClmul_assoc a b b]
    _   = sClmul a (sClmul b (sClmul a b)) := by rw [sClmul_comm (sClmul a b) b]
    _   = sClmul (sClmul a b) (sClmul a b) := (sClmul_assoc a b (sClmul a b)).symm

-- Cartier 2-Splitting Laws

theorem cartier_bisim (a b : Stream) (hev : sEv a = sEv b) (hod : sOd a = sOd b) : a = b := by
  funext k
  by_cases hm : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    rw [hk]; exact congrFun hev (k / 2)
  · have hk : k = 2 * (k / 2) + 1 := by omega
    rw [hk]; exact congrFun hod (k / 2)

theorem sEv_zero : sEv sZero = sZero := rfl

theorem sOd_zero : sOd sZero = sZero := rfl

theorem sEv_one : sEv sOne = sOne := by funext k; cases k <;> rfl

theorem sOd_one : sOd sOne = sZero := by funext k; simp [sOd, sOne, sZero]

theorem sEv_allOnes : sEv sAllOnes = sAllOnes := rfl

theorem sOd_allOnes : sOd sAllOnes = sAllOnes := rfl

theorem sEv_xor (a b : Stream) : sEv (sXor a b) = sXor (sEv a) (sEv b) := rfl

theorem sOd_xor (a b : Stream) : sOd (sXor a b) = sXor (sOd a) (sOd b) := rfl

theorem sEv_and (a b : Stream) : sEv (sAnd a b) = sAnd (sEv a) (sEv b) := rfl

theorem sOd_and (a b : Stream) : sOd (sAnd a b) = sAnd (sOd a) (sOd b) := rfl

theorem sEv_frob1 (a : Stream) : sEv (sFrob1 a) = a := by
  funext k; simp [sEv, sFrob1]

theorem sOd_frob1 (a : Stream) : sOd (sFrob1 a) = sZero := by
  funext k; simp only [sOd, sFrob1, sZero]
  have : ((2 * k + 1) % 2 == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  rw [this]; rfl

theorem sEv_shl_even (a : Stream) (q : Nat) : sEv (sShl a (2 * q)) = sShl (sEv a) q := by
  funext k; simp only [sEv, sShl]
  by_cases h : q ≤ k
  · have h2 : 2 * q ≤ 2 * k := by omega
    have hs : 2 * k - 2 * q = 2 * (k - q) := by omega
    simp only [h2, h, ↓reduceIte, hs]
  · have h2 : ¬ (2 * q ≤ 2 * k) := by omega
    simp only [h2, h, ↓reduceIte]

theorem sOd_shl_even (a : Stream) (q : Nat) : sOd (sShl a (2 * q)) = sShl (sOd a) q := by
  funext k; simp only [sOd, sShl]
  by_cases h : q ≤ k
  · have h2 : 2 * q ≤ 2 * k + 1 := by omega
    have hs : 2 * k + 1 - 2 * q = 2 * (k - q) + 1 := by omega
    simp only [h2, h, ↓reduceIte, hs]
  · have h2 : ¬ (2 * q ≤ 2 * k + 1) := by omega
    simp only [h2, h, ↓reduceIte]

theorem sEv_shl_odd (a : Stream) (q : Nat) : sEv (sShl a (2 * q + 1)) = sShl (sOd a) (q + 1) := by
  funext k; simp only [sEv, sOd, sShl]
  by_cases h : q + 1 ≤ k
  · have h2 : 2 * q + 1 ≤ 2 * k := by omega
    have hs : 2 * k - (2 * q + 1) = 2 * (k - (q + 1)) + 1 := by omega
    simp only [h2, h, ↓reduceIte, hs]
  · have h2 : ¬ (2 * q + 1 ≤ 2 * k) := by omega
    simp only [h2, h, ↓reduceIte]

theorem sOd_shl_odd (a : Stream) (q : Nat) : sOd (sShl a (2 * q + 1)) = sShl (sEv a) q := by
  funext k; simp only [sOd, sEv, sShl]
  by_cases h : q ≤ k
  · have h2 : 2 * q + 1 ≤ 2 * k + 1 := by omega
    have hs : 2 * k + 1 - (2 * q + 1) = 2 * (k - q) := by omega
    simp only [h2, h, ↓reduceIte, hs]
  · have h2 : ¬ (2 * q + 1 ≤ 2 * k + 1) := by omega
    simp only [h2, h, ↓reduceIte]

theorem sEv_clmul (a b : Stream) :
    sEv (sClmul a b) = sXor (sClmul (sEv a) (sEv b)) (sShl (sClmul (sOd a) (sOd b)) 1) := by
  funext k; simp only [sEv, sClmul, sXor, sShl, sOd]
  rw [xorSum, xorSum_double]
  cases k with
  | zero => simp [xorSum]
  | succ k' =>
    simp only [Nat.succ_le_succ_iff, Nat.zero_le, ↓reduceIte, Nat.add_sub_cancel]
    have hrearr : ∀ x y z : Bool, ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y) := by
      intro x y z; cases x <;> cases y <;> cases z <;> rfl
    rw [hrearr]
    congr 1
    · conv => rhs; rw [xorSum]
      congr 1
      · apply xorSum_congr; intro i hi
        have hs : 2 * (k' + 1) - 2 * i = 2 * (k' + 1 - i) := by omega
        rw [hs]
      · have hs : 2 * (k' + 1) - 2 * (k' + 1) = 2 * (k' + 1 - (k' + 1)) := by omega
        rw [hs]
    · apply xorSum_congr; intro i hi
      have hs : 2 * (k' + 1) - (2 * i + 1) = 2 * (k' - i) + 1 := by omega
      rw [hs]

theorem sOd_clmul (a b : Stream) :
    sOd (sClmul a b) = sXor (sClmul (sEv a) (sOd b)) (sClmul (sOd a) (sEv b)) := by
  funext k; simp only [sOd, sEv, sClmul, sXor]
  have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  rw [hlen, xorSum_double]
  congr 1
  · apply xorSum_congr; intro i hi
    have hs : 2 * k + 1 - 2 * i = 2 * (k - i) + 1 := by omega
    rw [hs]
  · apply xorSum_congr; intro i hi
    have hs : 2 * k + 1 - (2 * i + 1) = 2 * (k - i) := by omega
    rw [hs]

theorem sEv_clmul_frob1_right (a b : Stream) :
    sEv (sClmul a (sFrob1 b)) = sClmul (sEv a) b := by
  rw [sEv_clmul, sEv_frob1, sOd_frob1, sClmul_zero, sShl_sZero, sXor_zero]

theorem sOd_clmul_frob1_right (a b : Stream) :
    sOd (sClmul a (sFrob1 b)) = sClmul (sOd a) b := by
  rw [sOd_clmul, sEv_frob1, sOd_frob1, sClmul_zero, sZero_xor]

theorem sEv_clmul_frob1_left (a b : Stream) :
    sEv (sClmul (sFrob1 a) b) = sClmul a (sEv b) := by
  rw [sClmul_comm, sEv_clmul_frob1_right, sClmul_comm]

theorem sOd_clmul_frob1_left (a b : Stream) :
    sOd (sClmul (sFrob1 a) b) = sClmul a (sOd b) := by
  rw [sClmul_comm, sOd_clmul_frob1_right, sClmul_comm]

-- Frobenius Laws

theorem sClmul_self (a : Stream) : sClmul a a = sFrob1 a := by
  funext k; simp only [sClmul, sFrob1]
  have hsym : ∀ i, i ≤ k → (a i && a (k - i)) = (a (k - i) && a (k - (k - i))) := by
    intro i hi
    have h1 : k - (k - i) = i := by omega
    rw [h1, Bool.and_comm]
  rw [xorSum_symmetric k (fun i => a i && a (k - i)) hsym]
  split
  · rename_i hmod
    have hev : k % 2 = 0 := beq_iff_eq.mp hmod
    have h1 : k - k / 2 = k / 2 := by omega
    rw [h1, Bool.and_self]
  · rfl

theorem sFrob_succ_clmul (r : Nat) (a : Stream) :
    sFrob (r + 1) a = sClmul (sFrob r a) (sFrob r a) := by
  rw [sClmul_self]; rfl

theorem sFrob_add (r1 r2 : Nat) (a : Stream) : sFrob r1 (sFrob r2 a) = sFrob (r1 + r2) a := by
  induction r1 with
  | zero => simp [sFrob]
  | succ r1 ih =>
    have h1 : r1 + 1 + r2 = (r1 + r2) + 1 := by omega
    rw [h1, sFrob, sFrob, ih]

theorem sFrob1_xor (a b : Stream) : sFrob1 (sXor a b) = sXor (sFrob1 a) (sFrob1 b) := by
  apply cartier_bisim <;> simp [sEv_frob1, sOd_frob1, sEv_xor, sOd_xor, sXor_zero]

theorem sFrob1_and (a b : Stream) : sFrob1 (sAnd a b) = sAnd (sFrob1 a) (sFrob1 b) := by
  apply cartier_bisim <;> simp [sEv_frob1, sOd_frob1, sEv_and, sOd_and, sAnd_zero]

theorem sFrob1_one : sFrob1 sOne = sOne := by
  apply cartier_bisim <;> simp [sEv_frob1, sOd_frob1, sEv_one, sOd_one]

theorem sFrob1_zero : sFrob1 sZero = sZero := by
  apply cartier_bisim <;> simp [sEv_frob1, sOd_frob1, sEv_zero, sOd_zero]

theorem sFrob1_shl (a : Stream) (s : Nat) : sFrob1 (sShl a s) = sShl (sFrob1 a) (2 * s) := by
  apply cartier_bisim
  · rw [sEv_frob1, sEv_shl_even, sEv_frob1]
  · rw [sOd_frob1, sOd_shl_even, sOd_frob1, sShl_sZero]

theorem sFrob_xor (r : Nat) (a b : Stream) :
    sFrob r (sXor a b) = sXor (sFrob r a) (sFrob r b) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [sFrob, ih, sFrob1_xor]

theorem sFrob_and (r : Nat) (a b : Stream) :
    sFrob r (sAnd a b) = sAnd (sFrob r a) (sFrob r b) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [sFrob, ih, sFrob1_and]

theorem sFrob_one (r : Nat) : sFrob r sOne = sOne := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [sFrob, ih, sFrob1_one]

theorem sFrob_zero_stream (r : Nat) : sFrob r sZero = sZero := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [sFrob, ih, sFrob1_zero]

theorem sFrob_shl (r s : Nat) (a : Stream) :
    sFrob r (sShl a s) = sShl (sFrob r a) (s * 2 ^ r) := by
  induction r with
  | zero => simp [sFrob]
  | succ r ih =>
    simp only [sFrob, ih, sFrob1_shl]
    congr 1
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, ← Nat.mul_assoc, Nat.mul_comm 2 s, Nat.mul_assoc]

theorem sFrob_bit (r : Nat) (a : Stream) (k : Nat) :
    sFrob r a k = if k % 2 ^ r == 0 then a (k / 2 ^ r) else false := by
  induction r generalizing k with
  | zero => simp [sFrob, Nat.mod_one, Nat.div_one]
  | succ r ih =>
    simp only [sFrob, sFrob1]
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ]; omega
    rw [hpow]
    by_cases h2 : k % 2 = 0
    · have h2b : (k % 2 == 0) = true := beq_iff_eq.mpr h2
      rw [h2b]; simp only [↓reduceIte, ih (k / 2)]
      have hdiv : k / (2 * 2 ^ r) = k / 2 / 2 ^ r := by rw [Nat.div_div_eq_div_mul]
      rw [hdiv]
      have hmod : (k / 2 % 2 ^ r == 0) = (k % (2 * 2 ^ r) == 0) := by
        have hk : k = 2 * (k / 2) := by omega
        conv => rhs; rw [hk, Nat.mul_mod_mul_left]
        cases h : (k / 2 % 2 ^ r == 0)
        · rw [beq_eq_false_iff_ne] at h
          symm; rw [beq_eq_false_iff_ne]; omega
        · rw [beq_iff_eq] at h
          symm; rw [beq_iff_eq]; omega
      rw [hmod]
    · have h2b : (k % 2 == 0) = false := beq_eq_false_iff_ne.mpr h2
      have h2rb : (k % (2 * 2 ^ r) == 0) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        apply h2
        have hdm := Nat.div_add_mod k (2 * 2 ^ r)
        have hmul : k = 2 * (2 ^ r * (k / (2 * 2 ^ r))) := by
          rw [← Nat.mul_assoc]; omega
        rw [hmul, Nat.mul_mod_right]
      rw [h2b, h2rb]; rfl

theorem sFrob_and_orthogonal (r s1 s2 : Nat) (a b : Stream)
    (hne : s1 % 2 ^ r ≠ s2 % 2 ^ r) :
    sAnd (sShl (sFrob r a) s1) (sShl (sFrob r b) s2) = sZero := by
  induction r generalizing s1 s2 with
  | zero => simp [Nat.mod_one] at hne
  | succ r ih =>
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ]; omega
    by_cases hp1 : s1 % 2 = 0
    · have hs1 : s1 = 2 * (s1 / 2) := by omega
      by_cases hp2 : s2 % 2 = 0
      · have hs2 : s2 = 2 * (s2 / 2) := by omega
        have hne' : (s1 / 2) % 2 ^ r ≠ (s2 / 2) % 2 ^ r := by
          intro heq; apply hne
          rw [hpow, hs1, hs2, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, heq]
        apply cartier_bisim
        · rw [sEv_and, hs1, hs2, sEv_shl_even, sEv_shl_even, sFrob, sFrob, sEv_frob1, sEv_frob1, sEv_zero]
          exact ih (s1 / 2) (s2 / 2) hne'
        · rw [sOd_and, hs1, hs2, sOd_shl_even, sOd_shl_even, sFrob, sFrob, sOd_frob1, sShl_sZero, sZero_and, sOd_zero]
      · have hs2 : s2 = 2 * (s2 / 2) + 1 := by omega
        apply cartier_bisim
        · rw [sEv_and, hs1, hs2, sEv_shl_even, sEv_shl_odd, sFrob, sFrob, sOd_frob1, sShl_sZero, sAnd_zero, sEv_zero]
        · rw [sOd_and, hs1, hs2, sOd_shl_even, sOd_shl_odd, sFrob, sFrob, sOd_frob1, sShl_sZero, sZero_and, sOd_zero]
    · have hs1 : s1 = 2 * (s1 / 2) + 1 := by omega
      by_cases hp2 : s2 % 2 = 0
      · have hs2 : s2 = 2 * (s2 / 2) := by omega
        apply cartier_bisim
        · rw [sEv_and, hs1, hs2, sEv_shl_odd, sEv_shl_even, sFrob, sFrob, sOd_frob1, sShl_sZero, sZero_and, sEv_zero]
        · rw [sOd_and, hs1, hs2, sOd_shl_odd, sOd_shl_even, sFrob, sFrob, sOd_frob1, sShl_sZero, sAnd_zero, sOd_zero]
      · have hs2 : s2 = 2 * (s2 / 2) + 1 := by omega
        have hne' : (s1 / 2) % 2 ^ r ≠ (s2 / 2) % 2 ^ r := by
          intro heq; apply hne
          rw [hpow, hs1, hs2]
          have h1 : (2 * (s1 / 2) + 1) % (2 * 2 ^ r) = 2 * ((s1 / 2) % 2 ^ r) + 1 := by
            have hlt : 2 * ((s1 / 2) % 2 ^ r) + 1 < 2 * 2 ^ r := by
              have := Nat.mod_lt (s1 / 2) (Nat.pow_pos (a := 2) (n := r) (by omega)); omega
            have hd := Nat.div_add_mod (s1 / 2) (2 ^ r)
            have hx : 2 * (s1 / 2) + 1 = (2 * ((s1 / 2) % 2 ^ r) + 1) + (2 * 2 ^ r) * ((s1 / 2) / 2 ^ r) := by
              have hmul : (2 * 2 ^ r) * ((s1 / 2) / 2 ^ r) = 2 * (2 ^ r * ((s1 / 2) / 2 ^ r)) := by
                rw [Nat.mul_assoc]
              omega
            rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
          have h2 : (2 * (s2 / 2) + 1) % (2 * 2 ^ r) = 2 * ((s2 / 2) % 2 ^ r) + 1 := by
            have hlt : 2 * ((s2 / 2) % 2 ^ r) + 1 < 2 * 2 ^ r := by
              have := Nat.mod_lt (s2 / 2) (Nat.pow_pos (a := 2) (n := r) (by omega)); omega
            have hd := Nat.div_add_mod (s2 / 2) (2 ^ r)
            have hx : 2 * (s2 / 2) + 1 = (2 * ((s2 / 2) % 2 ^ r) + 1) + (2 * 2 ^ r) * ((s2 / 2) / 2 ^ r) := by
              have hmul : (2 * 2 ^ r) * ((s2 / 2) / 2 ^ r) = 2 * (2 ^ r * ((s2 / 2) / 2 ^ r)) := by
                rw [Nat.mul_assoc]
              omega
            rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
          rw [h1, h2, heq]
        apply cartier_bisim
        · rw [sEv_and, hs1, hs2, sEv_shl_odd, sEv_shl_odd, sFrob, sFrob, sOd_frob1, sShl_sZero, sZero_and, sEv_zero]
        · rw [sOd_and, hs1, hs2, sOd_shl_odd, sOd_shl_odd, sFrob, sFrob, sEv_frob1, sEv_frob1, sOd_zero]
          exact ih (s1 / 2) (s2 / 2) hne'

theorem sFrob_and_aligned (r s1 s2 : Nat) (a b : Stream)
    (heq : s1 % 2 ^ r = s2 % 2 ^ r) :
    sAnd (sShl (sFrob r a) s1) (sShl (sFrob r b) s2) =
    sShl (sFrob r (sAnd (sShl a (s1 / 2 ^ r)) (sShl b (s2 / 2 ^ r)))) (s1 % 2 ^ r) := by
  have h1 : (s1 / 2 ^ r) * 2 ^ r + s1 % 2 ^ r = s1 := by
    have := Nat.div_add_mod s1 (2 ^ r); rw [Nat.mul_comm]; exact this
  have h2 : (s2 / 2 ^ r) * 2 ^ r + s1 % 2 ^ r = s2 := by
    have := Nat.div_add_mod s2 (2 ^ r); rw [Nat.mul_comm, ← heq] at this; exact this
  rw [sFrob_and, sShl_and, sFrob_shl, sFrob_shl, sShl_shl, sShl_shl, h1, h2]

theorem sShl_allOnes_one : sShl sAllOnes 1 = sXor sAllOnes sOne := by
  funext k; cases k <;> rfl

theorem sShl_E_half (k : Nat) :
    sShl (sE (k + 1)) (2 ^ k) = sXor (sE k) (sE (k + 1)) := by
  induction k with
  | zero =>
    apply cartier_bisim
    · have h1 : sEv (sShl (sFrob1 sAllOnes) (2 * 0 + 1)) = sShl (sOd (sFrob1 sAllOnes)) (0 + 1) :=
        sEv_shl_odd (sFrob1 sAllOnes) 0
      simpa [sE, sFrob, sEv_xor, sEv_frob1, sOd_frob1, sEv_allOnes, sShl_sZero, sXor_self] using h1
    · have h2 : sOd (sShl (sFrob1 sAllOnes) (2 * 0 + 1)) = sShl (sEv (sFrob1 sAllOnes)) 0 :=
        sOd_shl_odd (sFrob1 sAllOnes) 0
      simpa [sE, sFrob, sOd_xor, sEv_frob1, sOd_frob1, sOd_allOnes, sShl_zero, sXor_zero] using h2
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    apply cartier_bisim
    · rw [hpow, sEv_shl_even, sEv_xor, sE, sE, sFrob, sFrob, sEv_frob1, sEv_frob1]
      exact ih
    · rw [hpow, sOd_shl_even, sOd_xor, sE, sE, sFrob, sFrob, sOd_frob1, sOd_frob1, sShl_sZero, sXor_zero]

theorem sShl_E_full (k : Nat) : sShl (sE k) (2 ^ k) = sXor (sE k) sOne := by
  have h1 := sFrob_shl k 1 sAllOnes
  rw [Nat.one_mul] at h1
  rw [sE, ← h1, sShl_allOnes_one, sFrob_xor, sFrob_one]

theorem sClmul_E_adj (k : Nat) :
    sClmul (sE k) (sE (k + 1)) = sXor (sE (k + 2)) (sShl (sE (k + 2)) (2 ^ k)) := by
  have h1 : sE k = sXor (sE (k + 1)) (sShl (sE (k + 1)) (2 ^ k)) := by
    rw [sShl_E_half, sXor_comm (sE k), ← sXor_assoc, sXor_self, sZero_xor]
  rw [h1, sClmul_xor_left, sClmul_shl_left]
  have hsq : sClmul (sE (k + 1)) (sE (k + 1)) = sE (k + 2) := by
    simp only [sE]; exact (sFrob_succ_clmul (k + 1) sAllOnes).symm
  rw [hsq]

theorem sClmul_delta_E (r : Nat) (a : Stream) :
    sClmul (sXor a (sShl a (2 ^ r))) (sE r) = a := by
  rw [sClmul_xor_left, sClmul_shl_left, ← sClmul_shl_right, sShl_E_full,
      sClmul_xor_right, sClmul_one, ← sXor_assoc, sXor_self, sZero_xor]

theorem sDelta_injective (r : Nat) (a b : Stream)
    (h : sXor a (sShl a (2 ^ r)) = sXor b (sShl b (2 ^ r))) : a = b := by
  have h1 := congrArg (fun x => sClmul x (sE r)) h
  rw [sClmul_delta_E, sClmul_delta_E] at h1
  exact h1

-- ============================================================================
-- SECTION 2: Causal Projective-Limit Lifting Meta-Theorem (Stream → BitVec w)
-- ============================================================================

theorem bvClmul_foldl_getLsbD {w : Nat} (a b : BitVec w) (k : Nat) (hk : k < w) (n : Nat) :
    ((List.range n).foldl
      (fun acc i => if b.getLsbD i then acc ^^^ (a <<< i) else acc)
      (0 : BitVec w)).getLsbD k =
    xorSum n (fun i => b.getLsbD i && (if i ≤ k then a.getLsbD (k - i) else false)) := by
  induction n with
  | zero => simp [xorSum]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, xorSum]
    by_cases hb : b.getLsbD n = true
    · simp only [hb, ↓reduceIte, BitVec.getLsbD_xor, ih, BitVec.getLsbD_shiftLeft,
                 Bool.true_and, hk, decide_true]
      by_cases hnk : n ≤ k
      · simp [hnk, Nat.not_lt.mpr hnk]
      · simp [hnk, Nat.lt_of_not_ge hnk]
    · have hbf : b.getLsbD n = false := Bool.eq_false_iff.mpr hb
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, Bool.false_and, bxor_false]
      exact ih

theorem bvClmul_getLsbD {w : Nat} (a b : BitVec w) (k : Nat) (hk : k < w) :
    (bvClmul a b).getLsbD k = sClmul (fun j => a.getLsbD j) (fun j => b.getLsbD j) k := by
  unfold bvClmul sClmul
  rw [bvClmul_foldl_getLsbD a b k hk w]
  have hsplit : (k + 1) + (w - (k + 1)) = w := by omega
  have hadd := xorSum_add (k + 1) (w - (k + 1))
    (fun i => b.getLsbD i && (if i ≤ k then a.getLsbD (k - i) else false))
  rw [hsplit] at hadd
  rw [hadd]
  have htail : xorSum (w - (k + 1))
      (fun r => b.getLsbD (k + 1 + r) && (if k + 1 + r ≤ k then a.getLsbD (k - (k + 1 + r)) else false)) = false := by
    apply xorSum_eq_false; intro r _
    have hnot : ¬ (k + 1 + r ≤ k) := by omega
    simp only [hnot, ↓reduceIte, Bool.and_false]
  rw [htail, bxor_false, ← xorSum_rev (k + 1)]
  apply xorSum_congr; intro i hi
  have h2 : k - i ≤ k := by omega
  have h3 : k - (k - i) = i := by omega
  simp [h2, h3, Bool.and_comm]

theorem bvFrob_getLsbD {w : Nat} (r : Nat) (a : BitVec w) (k : Nat) (hk : k < w) :
    (bvFrob r a).getLsbD k = sFrob r (fun j => a.getLsbD j) k := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
    simp only [bvFrob]
    rw [bvClmul_getLsbD _ _ k hk, sFrob_succ_clmul]
    simp only [sClmul]
    apply xorSum_congr; intro i hi
    rw [ih i (by omega), ih (k - i) (by omega)]

theorem bvE_getLsbD (w r k : Nat) (hk : k < w) :
    (bvE w r).getLsbD k = sE r k := by
  unfold bvE sE
  rw [bvFrob_getLsbD r (~~~(0 : BitVec w)) k hk, sFrob_bit, sFrob_bit]
  simp only [sAllOnes]
  split
  · have hdiv : k / 2 ^ r < w := Nat.lt_of_le_of_lt (Nat.div_le_self k (2 ^ r)) hk
    simp [hdiv]
  · rfl

theorem bvPr_getLsbD {w : Nat} (r : Nat) (a : BitVec w) (k : Nat) (hk : k < w) :
    (bvPr r a).getLsbD k = sClmul (fun j => a.getLsbD j) (sE r) k := by
  unfold bvPr
  rw [bvClmul_getLsbD _ _ k hk]
  simp only [sClmul]
  apply xorSum_congr; intro i hi
  rw [bvE_getLsbD w r (k - i) (by omega)]

theorem bvXorRange_getLsbD {w : Nat} (n : Nat) (f : Nat → BitVec w) (k : Nat) :
    (bvXorRange n f).getLsbD k = xorSum n (fun i => (f i).getLsbD k) := by
  induction n with
  | zero => simp [bvXorRange, xorSum]
  | succ n ih => simp [bvXorRange, xorSum, ih]

def Expr.eMask (r : Nat) : Expr := Expr.frob r .allOnes

def Expr.prefixR (r : Nat) (e : Expr) : Expr := .clmul e (Expr.eMask r)

def evalStream (σ : Nat → Stream) : Expr → Stream
  | .zero => sZero
  | .one => sOne
  | .allOnes => sAllOnes
  | .var i => σ i
  | .xor a b => sXor (evalStream σ a) (evalStream σ b)
  | .and a b => sAnd (evalStream σ a) (evalStream σ b)
  | .clmul a b => sClmul (evalStream σ a) (evalStream σ b)
  | .shl a s => sShl (evalStream σ a) s

theorem evalBV_frob (w : Nat) (env : Nat → BitVec w) (r : Nat) (e : Expr) :
    evalBV w env (Expr.frob r e) = bvFrob r (evalBV w env e) := by
  induction r with
  | zero => rfl
  | succ r ih => simp [Expr.frob, evalBV, bvFrob, ih]

theorem evalBV_eMask (w : Nat) (env : Nat → BitVec w) (r : Nat) :
    evalBV w env (Expr.eMask r) = bvE w r := by
  simp [Expr.eMask, evalBV_frob, evalBV, bvE]

theorem evalBV_prefixR (w : Nat) (env : Nat → BitVec w) (r : Nat) (e : Expr) :
    evalBV w env (Expr.prefixR r e) = bvPr r (evalBV w env e) := by
  simp [Expr.prefixR, evalBV, evalBV_eMask, bvPr]

theorem evalStream_frob (σ : Nat → Stream) (r : Nat) (e : Expr) :
    evalStream σ (Expr.frob r e) = sFrob r (evalStream σ e) := by
  induction r with
  | zero => rfl
  | succ r ih => simp [Expr.frob, evalStream, ih, sFrob_succ_clmul]

theorem evalBV_getLsbD_eq_evalStream (w : Nat) (env : Nat → BitVec w) (e : Expr)
    (k : Nat) (hk : k < w) :
    (evalBV w env e).getLsbD k = evalStream (fun i j => (env i).getLsbD j) e k := by
  induction e generalizing k with
  | zero => simp [evalBV, evalStream, sZero]
  | one =>
    simp only [evalBV, evalStream, sOne, BitVec.getLsbD_ofNat, hk, decide_true, Bool.true_and]
    cases k with
    | zero => rfl
    | succ k' =>
      have h1 : (1 : Nat).testBit (k' + 1) = false := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hlt : 1 < 2 ^ (k' + 1) := by
          have : 2 ≤ 2 ^ (k' + 1) := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ (k' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        rw [Nat.div_eq_of_lt hlt]; rfl
      simp [h1]
  | allOnes => simp [evalBV, evalStream, sAllOnes, hk]
  | var i => rfl
  | xor a b iha ihb => simp [evalBV, evalStream, sXor, iha k hk, ihb k hk]
  | and a b iha ihb => simp [evalBV, evalStream, sAnd, iha k hk, ihb k hk]
  | clmul a b iha ihb =>
    simp only [evalBV, evalStream]
    rw [bvClmul_getLsbD _ _ k hk]
    simp only [sClmul]
    apply xorSum_congr; intro i hi
    rw [iha i (by omega), ihb (k - i) (by omega)]
  | shl a s iha =>
    simp only [evalBV, evalStream, sShl, BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
    by_cases hsk : s ≤ k
    · have hnotlt : ¬ (k < s) := by omega
      simp [hsk, hnotlt, iha (k - s) (by omega)]
    · have hlt : k < s := by omega
      simp [hsk, hlt]

/-- **META-THEOREM 1 (Causal Stream-to-All-BitVec Lifting)**:
    Any stream identity lifts uniformly to `∀ w : Nat, ∀ env : Nat → BitVec w`. -/
theorem lift_stream_to_all_bitvec (e1 e2 : Expr)
    (h : ∀ σ : Nat → Stream, evalStream σ e1 = evalStream σ e2) :
    ∀ (w : Nat) (env : Nat → BitVec w), evalBV w env e1 = evalBV w env e2 := by
  intro w env
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [evalBV_getLsbD_eq_evalStream w env e1 i hi,
      evalBV_getLsbD_eq_evalStream w env e2 i hi]
  exact congrFun (h (fun j m => (env j).getLsbD m)) i

-- ============================================================================
-- SECTION 3: Single Non-Mutual Normal Form `NF` (100% Pure Structural Recursion!)
--   ZERO mutual inductives, ZERO `WellFounded.fix` -> native-speed kernel `decide`!
-- ============================================================================

/-- Exact stream semantics of `NF` (pure structural recursion on `NF`). -/
def evalNF (σ : Nat → Stream) : NF → Stream
  | .zero => sZero
  | .allOnes => sAllOnes
  | .one => sOne
  | .bitAt s => sShl sOne s
  | .var idx s => sShl (σ idx) s
  | .frob k m s => sShl (sFrob (k + 1) (evalNF σ m)) s
  | .conv fs s => sShl (evalNF σ fs) s
  | .andCons a rest => sAnd (evalNF σ a) (evalNF σ rest)
  | .xorCons m rest => sXor (evalNF σ m) (evalNF σ rest)
  | .mulCons p rest => sClmul (evalNF σ p) (evalNF σ rest)

theorem evalNF_mulAppend (σ : Nat → Stream) (ps1 ps2 : NF) :
    evalNF σ (mulAppend ps1 ps2) = sClmul (evalNF σ ps1) (evalNF σ ps2) := by
  induction ps1 with
  | mulCons p ps _ ih => simp [mulAppend, evalNF, ih, sClmul_assoc]
  | one => simp [mulAppend, evalNF, sOne_clmul]
  | zero | allOnes | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ => rfl

theorem evalNF_xorInsert (σ : Nat → Stream) (m p : NF) :
    evalNF σ (xorInsert m p) = sXor (evalNF σ m) (evalNF σ p) := by
  induction p with
  | xorCons h t _ ih =>
    simp only [xorInsert]
    by_cases heq : (m == h) = true
    · have hmh : m = h := beq_iff_eq.mp heq
      subst hmh
      simp [evalNF, ← sXor_assoc, sXor_self, sZero_xor]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      cases cmpNF m h <;> simp only [evalNF, ih]
      · rw [← sXor_assoc, sXor_comm (evalNF σ h) (evalNF σ m), sXor_assoc]
      · rw [← sXor_assoc, sXor_comm (evalNF σ h) (evalNF σ m), sXor_assoc]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ => rfl

theorem evalNF_xorPoly (σ : Nat → Stream) (p1 p2 : NF) :
    evalNF σ (xorPoly p1 p2) = sXor (evalNF σ p1) (evalNF σ p2) := by
  induction p1 generalizing p2 with
  | xorCons m ms _ ih =>
    simp only [xorPoly, evalNF]
    rw [ih, evalNF_xorInsert, ← sXor_assoc, sXor_comm (evalNF σ ms) (evalNF σ m), sXor_assoc]
  | zero => simp [xorPoly, evalNF, sZero_xor]
  | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
    exact evalNF_xorInsert σ _ p2

theorem evalNF_atomInsertPlain (σ : Nat → Stream) (a m : NF) :
    evalNF σ (atomInsertPlain a m) = sAnd (evalNF σ a) (evalNF σ m) := by
  induction m with
  | andCons h t _ ih =>
    simp only [atomInsertPlain]
    by_cases heq : (a == h) = true
    · have hah : a = h := beq_iff_eq.mp heq
      subst hah
      simp [evalNF, ← sAnd_assoc, sAnd_self]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      cases cmpNF a h <;> simp only [evalNF, ih]
      · rw [← sAnd_assoc, sAnd_comm (evalNF σ h) (evalNF σ a), sAnd_assoc]
      · rw [← sAnd_assoc, sAnd_comm (evalNF σ h) (evalNF σ a), sAnd_assoc]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | xorCons _ _ | mulCons _ _ => rfl

theorem evalNF_lt_minShift (σ : Nat → Stream) (a : NF) (j : Nat) (hj : j < atomMinShift a) :
    evalNF σ a j = false := by
  cases a with
  | bitAt s => simp only [atomMinShift] at hj; simp [evalNF, sShl, Nat.not_le.mpr hj]
  | var _ s => simp only [atomMinShift] at hj; simp [evalNF, sShl, Nat.not_le.mpr hj]
  | frob _ _ s => simp only [atomMinShift] at hj; simp [evalNF, sShl, Nat.not_le.mpr hj]
  | conv _ s => simp only [atomMinShift] at hj; simp [evalNF, sShl, Nat.not_le.mpr hj]
  | zero | allOnes | one | andCons _ _ | xorCons _ _ | mulCons _ _ => simp [atomMinShift] at hj

theorem sAnd_bitAt_eq_zero_of_lt (s : Nat) (x : Stream) (hx : x s = false) :
    sAnd (sShl sOne s) x = sZero := by
  funext k; simp only [sAnd, sShl, sOne, sZero]
  by_cases hks : k = s
  · subst hks; simp [hx]
  · split
    · have hne : (k - s == 0) = false := by rw [beq_eq_false_iff_ne]; omega
      simp [hne]
    · rfl

theorem evalNF_at_false_of_annihilated (σ : Nat → Stream) (t : Nat) (b : NF)
    (h : isBitAtAnnihilated t b = true) :
    evalNF σ b t = false := by
  unfold isBitAtAnnihilated at h
  by_cases hlt : t < atomMinShift b
  · exact evalNF_lt_minShift σ b t hlt
  · simp only [hlt, ↓reduceIte] at h
    cases b with
    | bitAt s =>
      simp only [evalNF, sShl, sOne]
      have hne : s ≠ t := by simp at h; exact h
      split
      · rw [beq_eq_false_iff_ne]; omega
      · rfl
    | frob k m s =>
      simp only [atomMinShift] at hlt
      simp only [evalNF, sShl]
      have hle : s ≤ t := by omega
      simp only [hle, ↓reduceIte, sFrob_bit]
      have hmod : (t - s) % 2 ^ (k + 1) ≠ 0 := by simp at h; exact h
      have hmb : ((t - s) % 2 ^ (k + 1) == 0) = false := beq_eq_false_iff_ne.mpr hmod
      rw [hmb]; rfl
    | zero | allOnes | one | var _ _ | conv _ _ | andCons _ _ | xorCons _ _ | mulCons _ _ => simp at h

theorem evalNF_makeEPoly (σ : Nat → Stream) (k : Nat) :
    evalNF σ (makeEPoly k) = sE k := by
  cases k with
  | zero => simp [makeEPoly, allOnesPoly, evalNF, sXor_zero, sE, sFrob]
  | succ k => simp [makeEPoly, singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero, sE]

theorem evalNF_of_extractELevel (σ : Nat → Stream) (p : NF) (k : Nat)
    (h : extractELevel p = some k) :
    evalNF σ p = sE k := by
  cases p with
  | xorCons m ms =>
    cases ms with
    | zero =>
      cases m with
      | allOnes =>
        simp [extractELevel] at h; subst h
        simp [evalNF, sXor_zero, sE, sFrob]
      | andCons a as =>
        cases as with
        | allOnes =>
          cases a with
          | frob fk fm fs =>
            cases fm with
            | allOnes =>
              cases fs with
              | zero =>
                simp [extractELevel] at h; subst h
                simp [evalNF, sXor_zero, sAnd_allOnes, sShl_zero, sE]
              | succ _ => simp [extractELevel] at h
            | _ => simp [extractELevel] at h
          | _ => simp [extractELevel] at h
        | _ => simp [extractELevel] at h
      | _ => simp [extractELevel] at h
    | _ => simp [extractELevel] at h
  | _ => simp [extractELevel] at h

theorem evalNF_extractMonoClmulParts (σ : Nat → Stream) (m : NF) :
    sShl (evalNF σ (extractMonoClmulParts m).2) (extractMonoClmulParts m).1 = evalNF σ m := by
  cases m with
  | andCons a as =>
    cases as with
    | allOnes =>
      cases a with
      | bitAt s => simp [extractMonoClmulParts, evalNF, sAnd_allOnes]
      | var i s => simp [extractMonoClmulParts, singleAtomPoly, evalNF, sAnd_allOnes, sXor_zero, sClmul_one, sShl_zero]
      | conv fs s => simp [extractMonoClmulParts, evalNF, sAnd_allOnes]
      | frob k fm s => simp [extractMonoClmulParts, singleAtomPoly, evalNF, sAnd_allOnes, sXor_zero, sClmul_one, sShl_zero]
      | _ => simp [extractMonoClmulParts, evalNF, sClmul_one, sXor_zero, sShl_zero]
    | _ => simp [extractMonoClmulParts, evalNF, sClmul_one, sXor_zero, sShl_zero]
  | _ => simp [extractMonoClmulParts, evalNF, sClmul_one, sXor_zero, sShl_zero]

theorem evalNF_insertSortedPoly (σ : Nat → Stream) (p ps : NF) :
    evalNF σ (insertSortedPoly p ps) = sClmul (evalNF σ p) (evalNF σ ps) := by
  induction ps with
  | mulCons h t _ ih =>
    simp only [insertSortedPoly]
    cases cmpNF p h <;> simp only [evalNF, ih]
    · rw [← sClmul_assoc, sClmul_comm (evalNF σ h) (evalNF σ p), sClmul_assoc]
    · rw [← sClmul_assoc, sClmul_comm (evalNF σ h) (evalNF σ p), sClmul_assoc]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ => rfl

theorem evalNF_sortPolys (σ : Nat → Stream) (ps : NF) :
    evalNF σ (sortPolys ps) = evalNF σ ps := by
  induction ps with
  | mulCons p ps _ ih => simp [sortPolys, evalNF_insertSortedPoly, evalNF, ih]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ => rfl

theorem evalNF_splitSquaresAux (σ : Nat → Stream) (prev : Option NF) (ps : NF) :
    sClmul (evalNF σ (splitSquaresAux prev ps).1)
           (sFrob 1 (evalNF σ (splitSquaresAux prev ps).2)) =
    match prev with
    | none => evalNF σ ps
    | some p => sClmul (evalNF σ p) (evalNF σ ps) := by
  induction ps generalizing prev with
  | mulCons p2 rest _ ih =>
    cases prev with
    | none => exact ih (some p2)
    | some p1 =>
      simp only [splitSquaresAux]
      by_cases heq : (p1 == p2) = true
      · have hp : p1 = p2 := beq_iff_eq.mp heq
        subst hp
        simp only [heq, ↓reduceIte, evalNF]
        have hih := ih none
        rw [sFrob_succ_clmul 0]; simp only [sFrob]
        rw [← sClmul_square_distrib, ← sClmul_assoc,
            sClmul_comm (evalNF σ (splitSquaresAux none rest).1),
            sClmul_assoc, sClmul_assoc]
        have hre : sClmul (evalNF σ (splitSquaresAux none rest).1)
                          (sClmul (evalNF σ (splitSquaresAux none rest).2)
                                  (evalNF σ (splitSquaresAux none rest).2)) =
                   evalNF σ rest := by
          have hsq : sFrob 1 (evalNF σ (splitSquaresAux none rest).2) =
              sClmul (evalNF σ (splitSquaresAux none rest).2)
                     (evalNF σ (splitSquaresAux none rest).2) := by
            rw [sFrob_succ_clmul 0]; rfl
          rw [← hsq]; exact hih
        rw [hre]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte, evalNF, sClmul_assoc]
        rw [ih (some p2)]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ =>
    cases prev <;> simp [splitSquaresAux, evalNF, sFrob_one, sClmul_one]

theorem evalNF_splitSquares (σ : Nat → Stream) (ps : NF) :
    sClmul (evalNF σ (splitSquares ps).1) (sFrob 1 (evalNF σ (splitSquares ps).2)) = evalNF σ ps :=
  evalNF_splitSquaresAux σ none ps

theorem evalNF_findShiftableE (σ : Nat → Stream) (tot : Nat) (fs : NF)
    (k : Nat) (rest : NF) (h : findShiftableE tot fs = some (k, rest)) :
    evalNF σ fs = sClmul (sE k) (evalNF σ rest) ∧
    (if k == 0 then 1 ≤ tot else 2 ^ (k - 1) ≤ tot) := by
  induction fs generalizing k rest with
  | mulCons fac fs _ ih =>
    simp only [findShiftableE] at h
    cases he : extractELevel fac with
    | none =>
      simp only [he] at h
      cases hf : findShiftableE tot fs with
      | none => simp [hf] at h
      | some p =>
        simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have ⟨heq, hle⟩ := ih p.1 p.2 hf
        refine ⟨?_, hle⟩
        simp only [evalNF, heq]
        rw [← sClmul_assoc, sClmul_comm (evalNF σ fac) (sE p.1), sClmul_assoc]
    | some ek =>
      simp only [he] at h
      cases ek with
      | zero =>
        by_cases h1 : 1 ≤ tot
        · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          refine ⟨?_, by simp [h1]⟩
          simp only [evalNF, evalNF_of_extractELevel σ fac 0 he]
        · simp only [h1, ↓reduceIte] at h
          cases hf : findShiftableE tot fs with
          | none => simp [hf] at h
          | some p =>
            simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have ⟨heq, hle⟩ := ih p.1 p.2 hf
            refine ⟨?_, hle⟩
            simp only [evalNF, heq]
            rw [← sClmul_assoc, sClmul_comm (evalNF σ fac) (sE p.1), sClmul_assoc]
      | succ k' =>
        by_cases h2 : 2 ^ k' ≤ tot
        · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          refine ⟨?_, by simp [h2]⟩
          simp only [evalNF, evalNF_of_extractELevel σ fac (k' + 1) he]
        · simp only [h2, ↓reduceIte] at h
          cases hf : findShiftableE tot fs with
          | none => simp [hf] at h
          | some p =>
            simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have ⟨heq, hle⟩ := ih p.1 p.2 hf
            refine ⟨?_, hle⟩
            simp only [evalNF, heq]
            rw [← sClmul_assoc, sClmul_comm (evalNF σ fac) (sE p.1), sClmul_assoc]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ =>
    simp [findShiftableE] at h

theorem evalNF_removeLevelE (σ : Nat → Stream) (target : Nat) (fs rest : NF)
    (h : removeLevelE target fs = some rest) :
    evalNF σ fs = sClmul (sE target) (evalNF σ rest) := by
  induction fs generalizing rest with
  | mulCons fac fs _ ih =>
    simp only [removeLevelE] at h
    by_cases heq : (extractELevel fac == some target) = true
    · simp only [heq, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hE := evalNF_of_extractELevel σ fac target (beq_iff_eq.mp heq)
      simp [evalNF, hE]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : removeLevelE target fs with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [evalNF, ih r hr]
        rw [← sClmul_assoc, sClmul_comm (evalNF σ fac) (sE target), sClmul_assoc]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ =>
    simp [removeLevelE] at h

theorem evalNF_findAdjacentE (σ : Nat → Stream) (fs : NF) (k : Nat) (rest : NF)
    (h : findAdjacentE fs = some (k, rest)) :
    evalNF σ fs = sClmul (sClmul (sE k) (sE (k + 1))) (evalNF σ rest) := by
  induction fs generalizing k rest with
  | mulCons fac fs _ ih =>
    simp only [findAdjacentE] at h
    cases he : extractELevel fac with
    | none =>
      simp only [he] at h
      cases hf : findAdjacentE fs with
      | none => simp [hf] at h
      | some p =>
        simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [evalNF, ih p.1 p.2 hf]
        rw [← sClmul_assoc, sClmul_comm (evalNF σ fac), sClmul_assoc]
    | some ek =>
      simp only [he] at h
      have hfac := evalNF_of_extractELevel σ fac ek he
      cases hr1 : removeLevelE (ek + 1) fs with
      | some rest' =>
        simp only [hr1, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [evalNF, hfac, evalNF_removeLevelE σ (ek + 1) fs rest' hr1, sClmul_assoc]
      | none =>
        simp only [hr1] at h
        cases ek with
        | zero =>
          cases hf : findAdjacentE fs with
          | none => simp [hf] at h
          | some p =>
            simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simp only [evalNF, ih p.1 p.2 hf]
            rw [← sClmul_assoc, sClmul_comm (evalNF σ fac), sClmul_assoc]
        | succ k' =>
          cases hr0 : removeLevelE k' fs with
          | some rest' =>
            simp only [hr0, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simp only [evalNF, hfac, evalNF_removeLevelE σ k' fs rest' hr0]
            rw [← sClmul_assoc, sClmul_comm (sE (k' + 1)) (sE k')]
          | none =>
            simp only [hr0] at h
            cases hf : findAdjacentE fs with
            | none => simp [hf] at h
            | some p =>
              simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simp only [evalNF, ih p.1 p.2 hf]
              rw [← sClmul_assoc, sClmul_comm (evalNF σ fac), sClmul_assoc]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ =>
    simp [findAdjacentE] at h

theorem evalNF_findFrobAtom (σ : Nat → Stream) (as : NF)
    (k : Nat) (m : NF) (s : Nat) (rest : NF)
    (h : findFrobAtom as = some (k, m, s, rest)) :
    evalNF σ as = sAnd (evalNF σ (.frob k m s)) (evalNF σ rest) := by
  induction as generalizing rest with
  | andCons a as _ ih =>
    cases a with
    | frob k' m' s' =>
      simp only [findFrobAtom, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl
    | zero | allOnes | one | bitAt _ | var _ _ | conv _ _ | andCons _ _ | xorCons _ _ | mulCons _ _ =>
      simp only [findFrobAtom] at h
      cases hf : findFrobAtom as with
      | none => simp [hf] at h
      | some p =>
        simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        change sAnd (evalNF σ _) (evalNF σ as) =
          sAnd (evalNF σ (.frob p.1 p.2.1 p.2.2.1)) (sAnd (evalNF σ _) (evalNF σ p.2.2.2))
        rw [ih p.2.2.2 hf, ← sAnd_assoc, sAnd_comm _ (evalNF σ (.frob p.1 p.2.1 p.2.2.1)), sAnd_assoc]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | xorCons _ _ | mulCons _ _ =>
    simp [findFrobAtom] at h

theorem evalNF_at_false_of_anyAnnihilates (σ : Nat → Stream) (t : Nat) (as : NF)
    (h : anyAnnihilates t as = true) :
    evalNF σ as t = false := by
  induction as with
  | andCons b bs _ ih =>
    simp only [anyAnnihilates, Bool.or_eq_true] at h
    simp only [evalNF, sAnd]
    rcases h with hb | hbs
    · rw [evalNF_at_false_of_annihilated σ t b hb, Bool.false_and]
    · rw [ih hbs, Bool.and_false]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | xorCons _ _ | mulCons _ _ =>
    simp [anyAnnihilates] at h

theorem sAnd_evalNF_zero_of_anyBitAt (σ : Nat → Stream) (a as : NF)
    (h : anyBitAtAnnihilatesAtom a as = true) :
    sAnd (evalNF σ a) (evalNF σ as) = sZero := by
  induction as with
  | andCons b bs _ ih =>
    cases b with
    | bitAt t =>
      simp only [anyBitAtAnnihilatesAtom, Bool.or_eq_true] at h
      simp only [evalNF]
      rcases h with ha | hbs
      · rw [← sAnd_assoc, sAnd_comm (evalNF σ a)]
        rw [sAnd_bitAt_eq_zero_of_lt t (evalNF σ a) (evalNF_at_false_of_annihilated σ t a ha), sZero_and]
      · rw [← sAnd_assoc, sAnd_comm (evalNF σ a), sAnd_assoc, ih hbs, sAnd_zero]
    | zero | allOnes | one | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ | mulCons _ _ =>
      simp only [anyBitAtAnnihilatesAtom] at h
      simp only [evalNF]
      rw [← sAnd_assoc, sAnd_comm (evalNF σ a), sAnd_assoc, ih h, sAnd_zero]
  | zero | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | xorCons _ _ | mulCons _ _ =>
    simp [anyBitAtAnnihilatesAtom] at h

theorem evalNF_shlAllOnesPoly (σ : Nat → Stream) (s : Nat) :
    evalNF σ (shlAllOnesPoly s) = sShl sAllOnes s := by
  induction s with
  | zero => simp [shlAllOnesPoly, allOnesPoly, evalNF, sXor_zero, sShl_zero]
  | succ s ih =>
    simp only [shlAllOnesPoly, evalNF_xorInsert, ih, evalNF, sAnd_allOnes]
    funext k; simp only [sXor, sShl, sOne, sAllOnes]
    by_cases h1 : s + 1 ≤ k
    · have h2 : s ≤ k := by omega
      have h3 : (k - s == 0) = false := by rw [beq_eq_false_iff_ne]; omega
      simp [h1, h2, h3]
    · by_cases h2 : s ≤ k
      · have h3 : k - s = 0 := by omega
        simp [h1, h2, h3]
      · simp [h1, h2]

-- ============================================================================
-- Pure Structurally Recursive Normalizer (`mkOps : Nat → Ops`)
-- ============================================================================

structure OpsSound (σ : Nat → Stream) (ops : Ops) : Prop where
  hShlAtom : ∀ a s, evalNF σ (ops.shlAtom a s) = sShl (evalNF σ a) s
  hShlMono : ∀ m s, evalNF σ (ops.shlMono m s) = sShl (evalNF σ m) s
  hShlPoly : ∀ p s, evalNF σ (ops.shlPoly p s) = sShl (evalNF σ p) s
  hFrobMono : ∀ k m, evalNF σ (ops.frobMono k m) = sFrob (k + 1) (evalNF σ m)
  hFrobPoly : ∀ k p, evalNF σ (ops.frobPoly k p) = sFrob (k + 1) (evalNF σ p)
  hInsertAtom : ∀ a m, evalNF σ (ops.insertAtom a m) = sAnd (evalNF σ a) (evalNF σ m)
  hAndPoly : ∀ p1 p2, evalNF σ (ops.andPoly p1 p2) = sAnd (evalNF σ p1) (evalNF σ p2)
  hConvFactors : ∀ fs s, evalNF σ (ops.convFactors fs s) = sShl (evalNF σ fs) s
  hClmulPoly : ∀ p1 p2, evalNF σ (ops.clmulPoly p1 p2) = sClmul (evalNF σ p1) (evalNF σ p2)

theorem andPolyOf_sound (σ : Nat → Stream) (ins : NF → NF → NF)
    (hIns : ∀ a m, evalNF σ (ins a m) = sAnd (evalNF σ a) (evalNF σ m)) :
    ∀ p1 p2, evalNF σ (andPolyOf ins p1 p2) = sAnd (evalNF σ p1) (evalNF σ p2) := by
  have hAWP : ∀ a p, evalNF σ (andAtomWithPolyOf ins a p) = sAnd (evalNF σ a) (evalNF σ p) := by
    intro a p; induction p with
    | xorCons m ms _ ih => simp only [andAtomWithPolyOf, evalNF_xorPoly, hIns, ih, evalNF, sAnd_xor_left]
    | zero => simp [andAtomWithPolyOf, evalNF, sAnd_zero]
    | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
      exact hIns a _
  have hALM : ∀ m p, evalNF σ (andMonoOntoPolyOf ins m p) = sAnd (evalNF σ m) (evalNF σ p) := by
    intro m; induction m with
    | andCons a rest _ ih =>
      intro p; simp only [andMonoOntoPolyOf, evalNF]
      rw [ih, hAWP, ← sAnd_assoc, sAnd_comm (evalNF σ rest) (evalNF σ a), sAnd_assoc]
    | allOnes => intro p; simp [andMonoOntoPolyOf, evalNF, sAllOnes_and]
    | zero | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | xorCons _ _ | mulCons _ _ =>
      intro p; exact hAWP _ p
  have hAM : ∀ m1 m2, evalNF σ (andMonoOf ins m1 m2) = sAnd (evalNF σ m1) (evalNF σ m2) := by
    intro m1 m2; simp [andMonoOf, hALM, evalNF, sXor_zero]
  have hAMP : ∀ m1 p2, evalNF σ (andMonoWithPolyOf ins m1 p2) = sAnd (evalNF σ m1) (evalNF σ p2) := by
    intro m1 p2; induction p2 with
    | xorCons m2 ms2 _ ih => simp only [andMonoWithPolyOf, evalNF_xorPoly, hAM, ih, evalNF, sAnd_xor_left]
    | zero => simp [andMonoWithPolyOf, evalNF, sAnd_zero]
    | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
      exact hAM m1 _
  intro p1 p2; induction p1 with
  | xorCons m1 ms1 _ ih => simp only [andPolyOf, evalNF_xorPoly, hAMP, ih, evalNF, sAnd_xor_right]
  | zero => simp [andPolyOf, evalNF, sZero_and]
  | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
    exact hAMP _ p2

theorem shlOf_sound (σ : Nat → Stream) (shA : NF → Nat → NF) (andP : NF → NF → NF)
    (hSA : ∀ a s, evalNF σ (shA a s) = sShl (evalNF σ a) s)
    (hAP : ∀ p1 p2, evalNF σ (andP p1 p2) = sAnd (evalNF σ p1) (evalNF σ p2)) :
    (∀ m s, evalNF σ (shlMonoOf shA andP m s) = sShl (evalNF σ m) s) ∧
    (∀ p s, evalNF σ (shlPolyOf (shlMonoOf shA andP) p s) = sShl (evalNF σ p) s) := by
  have hSM : ∀ m s, evalNF σ (shlMonoOf shA andP m s) = sShl (evalNF σ m) s := by
    intro m; induction m with
    | allOnes =>
      intro s; simp only [shlMonoOf]
      by_cases hs : s = 0
      · subst hs; simp [allOnesPoly, evalNF, sXor_zero, sShl_zero]
      · have hsb : (s == 0) = false := beq_eq_false_iff_ne.mpr hs
        simp only [hsb, Bool.false_eq_true, ↓reduceIte, evalNF, evalNF_shlAllOnesPoly]
    | andCons a rest _ ihr =>
      intro s; simp only [shlMonoOf]
      by_cases hs : s = 0
      · subst hs; simp [evalNF, sXor_zero, sShl_zero]
      · have hsb : (s == 0) = false := beq_eq_false_iff_ne.mpr hs
        simp only [hsb, Bool.false_eq_true, ↓reduceIte]
        cases rest with
        | allOnes => simp [hSA, evalNF, sAnd_allOnes]
        | zero | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ | mulCons _ _ =>
          rw [hAP, hSA, ihr s, ← sShl_and]; rfl
    | zero | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | xorCons _ _ | mulCons _ _ =>
      intro s; simp only [shlMonoOf]
      by_cases hs : s = 0
      · subst hs; simp [evalNF, sXor_zero, sShl_zero]
      · have hsb : (s == 0) = false := beq_eq_false_iff_ne.mpr hs
        simp only [hsb, Bool.false_eq_true, ↓reduceIte, hSA]
  refine ⟨hSM, ?_⟩
  intro p s; induction p with
  | xorCons m ms _ ih =>
    simp only [shlPolyOf]
    by_cases hs : s = 0
    · subst hs; simp [sShl_zero]
    · have hsb : (s == 0) = false := beq_eq_false_iff_ne.mpr hs
      simp only [hsb, Bool.false_eq_true, ↓reduceIte, evalNF_xorPoly, hSM, ih, evalNF, sShl_xor]
  | zero => simp [shlPolyOf, evalNF, sShl_sZero]
  | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
    simp only [shlPolyOf]
    by_cases hs : s = 0
    · subst hs; simp [sShl_zero]
    · have hsb : (s == 0) = false := beq_eq_false_iff_ne.mpr hs
      simp only [hsb, Bool.false_eq_true, ↓reduceIte, hSM]

theorem frobPolyOf_sound (σ : Nat → Stream) (frM : Nat → NF → NF)
    (hFM : ∀ k m, evalNF σ (frM k m) = sFrob (k + 1) (evalNF σ m)) :
    ∀ k p, evalNF σ (frobPolyOf frM k p) = sFrob (k + 1) (evalNF σ p) := by
  intro k p; induction p with
  | xorCons m ms _ ih => simp only [frobPolyOf, evalNF_xorPoly, hFM, ih, evalNF, sFrob_xor]
  | zero => simp [frobPolyOf, evalNF, sFrob_zero_stream]
  | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
    exact hFM k _

theorem convFactorsOf_sound (σ : Nat → Stream) (shA : NF → Nat → NF) (shP : NF → Nat → NF)
    (hSA : ∀ a s, evalNF σ (shA a s) = sShl (evalNF σ a) s)
    (hSP : ∀ p s, evalNF σ (shP p s) = sShl (evalNF σ p) s) :
    ∀ fs s, evalNF σ (convFactorsOf shA shP fs s) = sShl (evalNF σ fs) s := by
  intro fs s; cases fs with
  | one => simp [convFactorsOf, singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes]
  | mulCons p ps =>
    cases ps with
    | one => simp [convFactorsOf, hSP, evalNF, sClmul_one]
    | _ => simp only [convFactorsOf, hSA, evalNF, sShl_zero]
  | zero | allOnes | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ =>
    simp only [convFactorsOf, hSA, evalNF, sShl_zero]

theorem clmulPolyOf_sound (σ : Nat → Stream) (clM : NF → NF → NF)
    (hCM : ∀ m1 m2, evalNF σ (clM m1 m2) = sClmul (evalNF σ m1) (evalNF σ m2)) :
    ∀ p1 p2, evalNF σ (clmulPolyOf clM p1 p2) = sClmul (evalNF σ p1) (evalNF σ p2) := by
  have hCMP : ∀ m1 p2, evalNF σ (clmulMonoWithPolyOf clM m1 p2) = sClmul (evalNF σ m1) (evalNF σ p2) := by
    intro m1 p2; induction p2 with
    | xorCons m2 ms2 _ ih => simp only [clmulMonoWithPolyOf, evalNF_xorPoly, hCM, ih, evalNF, sClmul_xor_right]
    | zero => simp [clmulMonoWithPolyOf, evalNF, sClmul_zero]
    | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
      exact hCM m1 _
  intro p1 p2; induction p1 with
  | xorCons m1 ms1 _ ih => simp only [clmulPolyOf, evalNF_xorPoly, hCMP, ih, evalNF, sClmul_xor_left]
  | zero => simp [clmulPolyOf, evalNF, sZero_clmul]
  | allOnes | one | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | mulCons _ _ =>
    exact hCMP _ p2

theorem clmulSquaresOf_sound (σ : Nat → Stream) (clP : NF → NF → NF) (frP : Nat → NF → NF)
    (hCP : ∀ p1 p2, evalNF σ (clP p1 p2) = sClmul (evalNF σ p1) (evalNF σ p2))
    (hFP : ∀ k p, evalNF σ (frP k p) = sFrob (k + 1) (evalNF σ p)) :
    ∀ acc sqs, evalNF σ (clmulSquaresOf clP frP acc sqs) =
      sClmul (evalNF σ acc) (sFrob 1 (evalNF σ sqs)) := by
  intro acc sqs
  induction sqs generalizing acc with
  | mulCons sf rest _ ihs =>
    simp only [clmulSquaresOf, evalNF]
    rw [ihs, hCP, hFP 0 sf, sClmul_assoc]
    congr 1
    rw [sFrob_succ_clmul 0, sFrob_succ_clmul 0, sFrob_succ_clmul 0]
    simp only [sFrob]
    exact sClmul_square_distrib (evalNF σ sf) (evalNF σ rest)
  | one => simp [clmulSquaresOf, evalNF, sFrob_one, sClmul_one]
  | zero | allOnes | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ =>
    simp only [clmulSquaresOf, hCP, hFP 0]

theorem shlAtomBase_sound (σ : Nat → Stream) (a : NF) (s : Nat) :
    evalNF σ (shlAtomBase a s) = sShl (evalNF σ a) s := by
  unfold shlAtomBase
  by_cases hs : s = 0
  · subst hs; simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero]
  · have hsb : (s == 0) = false := beq_eq_false_iff_ne.mpr hs
    simp only [hsb, Bool.false_eq_true, ↓reduceIte]
    cases a <;> simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_shl]

theorem insertAtomNonBitAt_sound (σ : Nat → Stream) (a m : NF) :
    evalNF σ (if anyBitAtAnnihilatesAtom a m then .zero else .xorCons (atomInsertPlain a m) .zero) =
    sAnd (evalNF σ a) (evalNF σ m) := by
  by_cases hann : anyBitAtAnnihilatesAtom a m = true
  · simp only [hann, ↓reduceIte, evalNF]; symm; exact sAnd_evalNF_zero_of_anyBitAt σ a m hann
  · have hf : anyBitAtAnnihilatesAtom a m = false := Bool.eq_false_iff.mpr hann
    simp [hf, evalNF, evalNF_atomInsertPlain, sXor_zero]

theorem insertAtomBase_sound (σ : Nat → Stream) (a m : NF) :
    evalNF σ (insertAtomBase a m) = sAnd (evalNF σ a) (evalNF σ m) := by
  unfold insertAtomBase
  cases a with
  | bitAt t =>
    by_cases hann : anyAnnihilates t m = true
    · simp only [hann, ↓reduceIte, evalNF]
      symm; exact sAnd_bitAt_eq_zero_of_lt t (evalNF σ m)
        (evalNF_at_false_of_anyAnnihilates σ t m hann)
    · have hf : anyAnnihilates t m = false := Bool.eq_false_iff.mpr hann
      simp [hf, evalNF, evalNF_atomInsertPlain, sXor_zero]
  | zero | allOnes | one | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ | mulCons _ _ =>
    exact insertAtomNonBitAt_sound σ _ m

theorem shlAtomStep_sound (σ : Nat → Stream) (prev : Ops) (ih : OpsSound σ prev)
    (a : NF) (s : Nat) :
    evalNF σ (shlAtomStep prev a s) = sShl (evalNF σ a) s := by
  unfold shlAtomStep
  by_cases hs : s = 0
  · subst hs; simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero]
  · have hsb : (s == 0) = false := beq_eq_false_iff_ne.mpr hs
    simp only [hsb, Bool.false_eq_true, ↓reduceIte]
    cases a with
    | bitAt s0 => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_shl]
    | var i s0 => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_shl]
    | frob k m s0 =>
      cases m with
      | allOnes =>
        by_cases hle : 2 ^ k ≤ s0 + s
        · simp only [hle, ↓reduceIte, evalNF_xorPoly, ih.hShlPoly, ih.hShlAtom, evalNF_makeEPoly,
                     evalNF, sShl_zero]
          rw [← sShl_xor]
          have hE : sFrob (k + 1) sAllOnes = sE (k + 1) := rfl
          rw [hE, ← sShl_E_half k, sShl_shl, sShl_shl]
          have hadd : 2 ^ k + (s0 + s - 2 ^ k) = s0 + s := by omega
          rw [hadd]
        · simp [hle, singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_shl]
      | _ => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_shl]
    | conv fs s0 =>
      dsimp only
      cases hfind : findShiftableE (s0 + s) fs with
      | none => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_shl]
      | some p =>
        rcases p with ⟨ek, rest⟩
        have ⟨heq, hle⟩ := evalNF_findShiftableE σ (s0 + s) fs ek rest hfind
        cases ek with
        | zero =>
          simp only [beq_self_eq_true, ↓reduceIte] at hle
          simp only [evalNF_xorPoly, ih.hShlPoly, ih.hClmulPoly, ih.hConvFactors,
                     allOnesPoly, evalNF, sXor_zero, sShl_zero]
          rw [← sShl_xor, heq, sShl_shl]
          have hadd : 1 + (s0 + s - 1) = s0 + s := by omega
          rw [← hadd, ← sShl_shl, ← sClmul_shl_left, sE, sFrob, sShl_allOnes_one,
              sClmul_xor_left, sOne_clmul, sClmul_comm sAllOnes]
          congr 1; omega
        | succ k' =>
          have hne0 : ((k' + 1 == 0) : Bool) = false := by rw [beq_eq_false_iff_ne]; omega
          simp only [hne0, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel] at hle
          simp only [evalNF_xorPoly, ih.hShlPoly, ih.hClmulPoly, ih.hConvFactors,
                     evalNF_makeEPoly, sShl_zero]
          rw [← sShl_xor, evalNF, heq, sShl_shl]
          have hadd : 2 ^ k' + (s0 + s - 2 ^ k') = s0 + s := by omega
          rw [← hadd, ← sShl_shl, ← sClmul_shl_left, sShl_E_half k',
              sClmul_xor_left, sClmul_comm (sE k'), sClmul_comm (sE (k' + 1))]
          congr 1; omega
    | zero | allOnes | one | andCons _ _ | xorCons _ _ | mulCons _ _ =>
      simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes]

theorem insertAtomStep_sound (σ : Nat → Stream) (prev : Ops) (ih : OpsSound σ prev)
    (a m : NF) :
    evalNF σ (insertAtomStep prev a m) = sAnd (evalNF σ a) (evalNF σ m) := by
  unfold insertAtomStep
  cases a with
  | bitAt t =>
    by_cases hann : anyAnnihilates t m = true
    · simp only [hann, ↓reduceIte, evalNF]
      symm; exact sAnd_bitAt_eq_zero_of_lt t (evalNF σ m)
        (evalNF_at_false_of_anyAnnihilates σ t m hann)
    · have hf : anyAnnihilates t m = false := Bool.eq_false_iff.mpr hann
      simp [hf, evalNF, evalNF_atomInsertPlain, sXor_zero]
  | frob k1 m1 s1 =>
    by_cases hann : anyBitAtAnnihilatesAtom (.frob k1 m1 s1) m = true
    · simp only [hann, ↓reduceIte, evalNF]; symm; exact sAnd_evalNF_zero_of_anyBitAt σ _ m hann
    · have hf : anyBitAtAnnihilatesAtom (.frob k1 m1 s1) m = false := Bool.eq_false_iff.mpr hann
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      cases hfind : findFrobAtom m with
      | none => simp [evalNF, evalNF_atomInsertPlain, sXor_zero]
      | some p =>
        rcases p with ⟨k2, m2, s2, rest⟩
        have hlist := evalNF_findFrobAtom σ m k2 m2 s2 rest hfind
        rw [hlist, ← sAnd_assoc]
        have hle1 : Nat.min k1 k2 ≤ k1 := Nat.min_le_left k1 k2
        have hle2 : Nat.min k1 k2 ≤ k2 := Nat.min_le_right k1 k2
        have ha1 : evalNF σ (.frob k1 m1 s1) =
            sShl (sFrob (Nat.min k1 k2 + 1) (if k1 == Nat.min k1 k2 then evalNF σ m1
                                             else sFrob (k1 - Nat.min k1 k2) (evalNF σ m1))) s1 := by
          simp only [evalNF]
          by_cases hk : k1 = Nat.min k1 k2
          · have hkb : (k1 == Nat.min k1 k2) = true := beq_iff_eq.mpr hk
            simp only [hkb, ↓reduceIte]; rw [← hk]
          · have hkb : (k1 == Nat.min k1 k2) = false := beq_eq_false_iff_ne.mpr hk
            have hadd : Nat.min k1 k2 + 1 + (k1 - Nat.min k1 k2) = k1 + 1 := by omega
            simp only [hkb, Bool.false_eq_true, ↓reduceIte]
            rw [sFrob_add, hadd]
        have ha2 : evalNF σ (.frob k2 m2 s2) =
            sShl (sFrob (Nat.min k1 k2 + 1) (if k2 == Nat.min k1 k2 then evalNF σ m2
                                             else sFrob (k2 - Nat.min k1 k2) (evalNF σ m2))) s2 := by
          simp only [evalNF]
          by_cases hk : k2 = Nat.min k1 k2
          · have hkb : (k2 == Nat.min k1 k2) = true := beq_iff_eq.mpr hk
            simp only [hkb, ↓reduceIte]; rw [← hk]
          · have hkb : (k2 == Nat.min k1 k2) = false := beq_eq_false_iff_ne.mpr hk
            have hadd : Nat.min k1 k2 + 1 + (k2 - Nat.min k1 k2) = k2 + 1 := by omega
            simp only [hkb, Bool.false_eq_true, ↓reduceIte]
            rw [sFrob_add, hadd]
        by_cases hres : s1 % 2 ^ (Nat.min k1 k2 + 1) = s2 % 2 ^ (Nat.min k1 k2 + 1)
        · have hneb : (s1 % 2 ^ (Nat.min k1 k2 + 1) != s2 % 2 ^ (Nat.min k1 k2 + 1)) = false := by
            simp [hres]
          simp only [hneb, Bool.false_eq_true, ↓reduceIte, ih.hAndPoly, ih.hShlPoly, ih.hFrobPoly]
          have hrest : evalNF σ (.xorCons rest .zero) = evalNF σ rest := by
            simp [evalNF, sXor_zero]
          rw [hrest]
          congr 1
          rw [ha1, ha2, sFrob_and_aligned (Nat.min k1 k2 + 1) s1 s2 _ _ hres]
          congr 1; congr 1
          have hp1 : evalNF σ (if k1 == Nat.min k1 k2 then prev.shlMono m1 (s1 / 2 ^ (Nat.min k1 k2 + 1))
              else prev.shlPoly (prev.frobMono (k1 - Nat.min k1 k2 - 1) m1) (s1 / 2 ^ (Nat.min k1 k2 + 1))) =
              sShl (if k1 == Nat.min k1 k2 then evalNF σ m1 else sFrob (k1 - Nat.min k1 k2) (evalNF σ m1))
                   (s1 / 2 ^ (Nat.min k1 k2 + 1)) := by
            by_cases hk : k1 = Nat.min k1 k2
            · have hkb : (k1 == Nat.min k1 k2) = true := beq_iff_eq.mpr hk
              simp only [hkb, ↓reduceIte, ih.hShlMono]
            · have hkb : (k1 == Nat.min k1 k2) = false := beq_eq_false_iff_ne.mpr hk
              have hsub : k1 - Nat.min k1 k2 - 1 + 1 = k1 - Nat.min k1 k2 := by omega
              simp only [hkb, Bool.false_eq_true, ↓reduceIte, ih.hShlPoly, ih.hFrobMono, hsub]
          have hp2 : evalNF σ (if k2 == Nat.min k1 k2 then prev.shlMono m2 (s2 / 2 ^ (Nat.min k1 k2 + 1))
              else prev.shlPoly (prev.frobMono (k2 - Nat.min k1 k2 - 1) m2) (s2 / 2 ^ (Nat.min k1 k2 + 1))) =
              sShl (if k2 == Nat.min k1 k2 then evalNF σ m2 else sFrob (k2 - Nat.min k1 k2) (evalNF σ m2))
                   (s2 / 2 ^ (Nat.min k1 k2 + 1)) := by
            by_cases hk : k2 = Nat.min k1 k2
            · have hkb : (k2 == Nat.min k1 k2) = true := beq_iff_eq.mpr hk
              simp only [hkb, ↓reduceIte, ih.hShlMono]
            · have hkb : (k2 == Nat.min k1 k2) = false := beq_eq_false_iff_ne.mpr hk
              have hsub : k2 - Nat.min k1 k2 - 1 + 1 = k2 - Nat.min k1 k2 := by omega
              simp only [hkb, Bool.false_eq_true, ↓reduceIte, ih.hShlPoly, ih.hFrobMono, hsub]
          rw [hp1, hp2]
        · have hneb : (s1 % 2 ^ (Nat.min k1 k2 + 1) != s2 % 2 ^ (Nat.min k1 k2 + 1)) = true := by
            simp [hres]
          simp only [hneb, ↓reduceIte]
          change sZero = _
          rw [ha1, ha2, sFrob_and_orthogonal (Nat.min k1 k2 + 1) s1 s2 _ _ hres, sZero_and]
  | zero | allOnes | one | var _ _ | conv _ _ | andCons _ _ | xorCons _ _ | mulCons _ _ =>
    exact insertAtomNonBitAt_sound σ _ m

theorem frobMonoStep_sound (σ : Nat → Stream) (prev : Ops) (ih : OpsSound σ prev)
    (k : Nat) (m : NF) :
    evalNF σ (frobMonoStep prev k m) = sFrob (k + 1) (evalNF σ m) := by
  unfold frobMonoStep
  cases m with
  | allOnes => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero]
  | andCons a as =>
    cases as with
    | allOnes =>
      cases a with
      | bitAt s => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sFrob_shl, sFrob_one]
      | frob k0 m0 s0 =>
        simp only [ih.hShlAtom, evalNF, sAnd_allOnes, sShl_zero, sFrob_shl, sFrob_add]
        have hadd : k + 1 + (k0 + 1) = k + k0 + 1 + 1 := by omega
        rw [hadd]
      | _ => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero]
    | _ => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero]
  | _ => simp [singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero]

theorem clmulMonoStep_sound (σ : Nat → Stream) (prev : Ops) (ih : OpsSound σ prev)
    (m1 m2 : NF) :
    evalNF σ (clmulMonoStep prev m1 m2) = sClmul (evalNF σ m1) (evalNF σ m2) := by
  unfold clmulMonoStep
  have hprod : sShl (evalNF σ (sortPolys (mulAppend (extractMonoClmulParts m1).2 (extractMonoClmulParts m2).2)))
                    ((extractMonoClmulParts m1).1 + (extractMonoClmulParts m2).1) =
               sClmul (evalNF σ m1) (evalNF σ m2) := by
    rw [evalNF_sortPolys, evalNF_mulAppend, ← sShl_shl, ← sClmul_shl_left, ← sClmul_shl_right,
        evalNF_extractMonoClmulParts, evalNF_extractMonoClmulParts]
  rw [← hprod]
  have hsplit := evalNF_splitSquares σ (sortPolys (mulAppend (extractMonoClmulParts m1).2 (extractMonoClmulParts m2).2))
  revert hsplit
  cases hsp : splitSquares (sortPolys (mulAppend (extractMonoClmulParts m1).2 (extractMonoClmulParts m2).2)) with
  | mk dedup sq =>
    intro hsplit
    dsimp only
    simp only [hsp]
    cases sq with
    | one =>
      dsimp only
      simp only [evalNF, sFrob_one, sClmul_one] at hsplit
      rw [← hsplit]
      cases hadj : findAdjacentE dedup with
      | none => exact ih.hConvFactors dedup _
      | some p =>
        rcases p with ⟨ek, rest⟩
        have hded := evalNF_findAdjacentE σ dedup ek rest hadj
        rw [ih.hClmulPoly, ih.hConvFactors, evalNF_xorPoly, ih.hShlPoly, evalNF_makeEPoly,
            ← sClmul_E_adj ek, sClmul_shl_left, hded, sClmul_comm]
    | mulCons _ _ | zero | allOnes | bitAt _ | var _ _ | frob _ _ _ | conv _ _ | andCons _ _ | xorCons _ _ =>
      dsimp only
      rw [clmulSquaresOf_sound σ _ _ ih.hClmulPoly ih.hFrobPoly, ih.hConvFactors, sClmul_shl_left, hsplit]

theorem mkOps_sound (σ : Nat → Stream) (fuel : Nat) : OpsSound σ (mkOps fuel) := by
  induction fuel with
  | zero =>
    dsimp only [mkOps]
    have hSA := shlAtomBase_sound σ
    have hIns := insertAtomBase_sound σ
    have hAP := andPolyOf_sound σ _ hIns
    have ⟨hSM, hSP⟩ := shlOf_sound σ _ _ hSA hAP
    have hFM : ∀ k m, evalNF σ (frobMonoBase k m) = sFrob (k + 1) (evalNF σ m) := by
      intro k m; simp [frobMonoBase, singleAtomPoly, evalNF, sXor_zero, sAnd_allOnes, sShl_zero]
    have hFP := frobPolyOf_sound σ _ hFM
    have hCF := convFactorsOf_sound σ _ _ hSA hSP
    have hCM : ∀ m1 m2, evalNF σ (convFactorsOf shlAtomBase (shlPolyOf (shlMonoOf shlAtomBase (andPolyOf insertAtomBase)))
        (sortPolys (mulAppend (extractMonoClmulParts m1).2 (extractMonoClmulParts m2).2))
        ((extractMonoClmulParts m1).1 + (extractMonoClmulParts m2).1)) = sClmul (evalNF σ m1) (evalNF σ m2) := by
      intro m1 m2
      rw [hCF, evalNF_sortPolys, evalNF_mulAppend, ← sShl_shl, ← sClmul_shl_left, ← sClmul_shl_right,
          evalNF_extractMonoClmulParts, evalNF_extractMonoClmulParts]
    exact ⟨hSA, hSM, hSP, hFM, hFP, hIns, hAP, hCF, clmulPolyOf_sound σ _ hCM⟩
  | succ fuel' ih =>
    dsimp only [mkOps]
    have hSA := shlAtomStep_sound σ (mkOps fuel') ih
    have hIns := insertAtomStep_sound σ (mkOps fuel') ih
    have hAP := andPolyOf_sound σ _ hIns
    have ⟨hSM, hSP⟩ := shlOf_sound σ _ _ hSA hAP
    have hFM := frobMonoStep_sound σ (mkOps fuel') ih
    have hFP := frobPolyOf_sound σ _ hFM
    have hCF := convFactorsOf_sound σ _ _ hSA hSP
    have hCM := clmulMonoStep_sound σ (mkOps fuel') ih
    exact ⟨hSA, hSM, hSP, hFM, hFP, hIns, hAP, hCF, clmulPolyOf_sound σ _ hCM⟩

/-- **SOUNDNESS OF THE NORMALIZER**: `norm fuel e` is semantically exact for ALL `fuel, σ, e`. -/
theorem evalNF_norm (fuel : Nat) (σ : Nat → Stream) (e : Expr) :
    evalNF σ (norm fuel e) = evalStream σ e := by
  have hs := mkOps_sound σ fuel
  unfold norm
  induction e with
  | zero => rfl
  | one => simp [normWith, singleAtomPoly, evalNF, evalStream, sXor_zero, sAnd_allOnes, sShl_zero]
  | allOnes => simp [normWith, allOnesPoly, evalNF, evalStream, sXor_zero]
  | var i => simp [normWith, singleAtomPoly, evalNF, evalStream, sXor_zero, sAnd_allOnes, sShl_zero]
  | xor a b iha ihb => simp [normWith, evalNF_xorPoly, evalStream, iha, ihb]
  | and a b iha ihb => simp [normWith, hs.hAndPoly, evalStream, iha, ihb]
  | clmul a b iha ihb => simp [normWith, hs.hClmulPoly, evalStream, iha, ihb]
  | shl a s iha => simp [normWith, hs.hShlPoly, evalStream, iha]

-- ============================================================================
-- SECTION 4: Cartier 2-Splitting, Binary Certificate Checker, & Dyadic Lane Lifting
-- ============================================================================

theorem evalStream_isConst_independent (e : Expr) (hc : isConst e = true) (σ1 σ2 : Nat → Stream) :
    evalStream σ1 e = evalStream σ2 e := by
  induction e with
  | zero => rfl
  | one => rfl
  | allOnes => rfl
  | var _ => simp [isConst] at hc
  | xor a b iha ihb =>
    simp only [isConst, Bool.and_eq_true] at hc
    simp only [evalStream, iha hc.1, ihb hc.2]
  | and a b iha ihb =>
    simp only [isConst, Bool.and_eq_true] at hc
    simp only [evalStream, iha hc.1, ihb hc.2]
  | clmul a b iha ihb =>
    simp only [isConst, Bool.and_eq_true] at hc
    simp only [evalStream, iha hc.1, ihb hc.2]
  | shl a s iha =>
    simp only [isConst] at hc
    simp only [evalStream, iha hc]

def splitEnv (σ : Nat → Stream) : Nat → Stream :=
  fun j => if j % 2 == 0 then sEv (σ (j / 2)) else sOd (σ (j / 2))

theorem cartierSplit_sound (σ : Nat → Stream) (e : Expr) :
    evalStream (splitEnv σ) (cartierSplit e).1 = sEv (evalStream σ e) ∧
    evalStream (splitEnv σ) (cartierSplit e).2 = sOd (evalStream σ e) := by
  induction e with
  | zero => exact ⟨rfl, rfl⟩
  | one => exact ⟨sEv_one.symm, sOd_one.symm⟩
  | allOnes => exact ⟨rfl, rfl⟩
  | var i =>
    constructor
    · simp only [cartierSplit, evalStream, splitEnv]
      have h2 : (2 * i) / 2 = i := by omega
      simp [h2]
    · simp only [cartierSplit, evalStream, splitEnv]
      have h2 : (2 * i + 1) / 2 = i := by omega
      simp [h2]
  | xor a b iha ihb =>
    simp only [cartierSplit, evalStream, iha.1, iha.2, ihb.1, ihb.2, sEv_xor, sOd_xor, and_self]
  | and a b iha ihb =>
    simp only [cartierSplit, evalStream, iha.1, iha.2, ihb.1, ihb.2, sEv_and, sOd_and, and_self]
  | shl a s iha =>
    simp only [cartierSplit]
    by_cases hp : s % 2 = 0
    · have hpb : (s % 2 == 0) = true := beq_iff_eq.mpr hp
      have hs : s = 2 * (s / 2) := by omega
      simp only [hpb, ↓reduceIte, evalStream, iha.1, iha.2]
      constructor
      · conv => rhs; rw [hs]
        exact (sEv_shl_even _ _).symm
      · conv => rhs; rw [hs]
        exact (sOd_shl_even _ _).symm
    · have hpb : (s % 2 == 0) = false := beq_eq_false_iff_ne.mpr hp
      have hs : s = 2 * (s / 2) + 1 := by omega
      simp only [hpb, Bool.false_eq_true, ↓reduceIte, evalStream, iha.1, iha.2]
      constructor
      · conv => rhs; rw [hs]
        exact (sEv_shl_odd _ _).symm
      · conv => rhs; rw [hs]
        exact (sOd_shl_odd _ _).symm
  | clmul a b iha ihb =>
    simp only [cartierSplit]
    by_cases hab : (a == b) = true
    · have heq : a = b := beq_iff_eq.mp hab
      subst heq
      simp only [hab, ↓reduceIte]
      by_cases hc : isConst a = true
      · simp only [hc, ↓reduceIte, evalStream]
        rw [sClmul_self, sEv_frob1, sOd_frob1]
        exact ⟨evalStream_isConst_independent a hc (splitEnv σ) σ, rfl⟩
      · have hcf : isConst a = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ↓reduceIte, evalStream, iha.1, iha.2]
        constructor
        · exact (sEv_clmul _ _).symm
        · rw [sOd_clmul, sClmul_comm (sOd (evalStream σ a)) (sEv (evalStream σ a)), sXor_self]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte, evalStream, iha.1, iha.2, ihb.1, ihb.2,
                 sEv_clmul, sOd_clmul, and_self]

def mkCartierCert (fuel : Nat) : Nat → Cert
  | 0 => .normEq fuel
  | d + 1 => let sub := mkCartierCert fuel d; .cartierSplit sub sub

theorem checkCert_sound (e1 e2 : Expr) (c : Cert) (h : checkCert e1 e2 c = true) :
    ∀ σ : Nat → Stream, evalStream σ e1 = evalStream σ e2 := by
  induction c generalizing e1 e2 with
  | normEq fuel =>
    intro σ; simp only [checkCert, beq_iff_eq] at h
    rw [← evalNF_norm fuel σ e1, ← evalNF_norm fuel σ e2, h]
  | cartierSplit cEv cOd ihEv ihOd =>
    intro σ; simp only [checkCert, Bool.and_eq_true] at h
    apply cartier_bisim
    · rw [← (cartierSplit_sound σ e1).1, ← (cartierSplit_sound σ e2).1]
      exact ihEv _ _ h.1 (splitEnv σ)
    · rw [← (cartierSplit_sound σ e1).2, ← (cartierSplit_sound σ e2).2]
      exact ihOd _ _ h.2 (splitEnv σ)
  | cancelDelta r sub ih =>
    intro σ; simp only [checkCert] at h
    have hd := ih _ _ h σ
    simp only [Expr.deltaR, evalStream] at hd
    exact sDelta_injective r _ _ hd
  | symm sub ih =>
    intro σ; simp only [checkCert] at h; exact (ih e2 e1 h σ).symm
  | trans mid c1 c2 ih1 ih2 =>
    intro σ; simp only [checkCert, Bool.and_eq_true] at h
    exact (ih1 e1 mid h.1 σ).trans (ih2 mid e2 h.2 σ)
  | congXor c1 c2 ih1 ih2 =>
    intro σ; cases e1 <;> cases e2 <;> simp only [checkCert, Bool.false_eq_true] at h
    simp only [Bool.and_eq_true] at h; simp only [evalStream, ih1 _ _ h.1 σ, ih2 _ _ h.2 σ]
  | congAnd c1 c2 ih1 ih2 =>
    intro σ; cases e1 <;> cases e2 <;> simp only [checkCert, Bool.false_eq_true] at h
    simp only [Bool.and_eq_true] at h; simp only [evalStream, ih1 _ _ h.1 σ, ih2 _ _ h.2 σ]
  | congClmul c1 c2 ih1 ih2 =>
    intro σ; cases e1 <;> cases e2 <;> simp only [checkCert, Bool.false_eq_true] at h
    simp only [Bool.and_eq_true] at h; simp only [evalStream, ih1 _ _ h.1 σ, ih2 _ _ h.2 σ]
  | congShl sub ih =>
    intro σ; cases e1 <;> cases e2 <;> simp only [checkCert, Bool.false_eq_true] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hsub⟩; simp only [evalStream, ih _ _ hsub σ]

/-- **META-THEOREM 2 (Finite Certificate → All Bit-Widths `∀ w, BitVec w`)** -/
theorem reflect_all_bitvec (e1 e2 : Expr) (c : Cert) (h : checkCert e1 e2 c = true) :
    ∀ (w : Nat) (env : Nat → BitVec w), evalBV w env e1 = evalBV w env e2 :=
  lift_stream_to_all_bitvec e1 e2 (checkCert_sound e1 e2 c h)

-- ============================================================================
-- Dyadic Lane-Replication Lifting Meta-Theorem (Single Finite Cert → ∀ r w)
-- ============================================================================

theorem isLaneSafe_of_isConst (e : Expr) (hc : isConst e = true) : isLaneSafe e = true := by
  induction e with
  | zero | one | allOnes => rfl
  | var _ => simp [isConst] at hc
  | xor a b iha ihb => simp only [isConst, Bool.and_eq_true] at hc; simp [isLaneSafe, iha hc.1, ihb hc.2]
  | and a b iha ihb => simp only [isConst, Bool.and_eq_true] at hc; simp [isLaneSafe, iha hc.1, ihb hc.2]
  | clmul a b iha ihb => simp only [isConst, Bool.and_eq_true] at hc; simp [isLaneSafe, iha hc.1, hc.2]
  | shl a _ iha => simp only [isConst] at hc; simp [isLaneSafe, iha hc]

theorem evalStream_dilate_zero (σ : Nat → Stream) (e : Expr) (hs : isLaneSafe e = true) :
    evalStream σ (dilate 0 e) = evalStream σ e := by
  induction e with
  | zero => rfl
  | one =>
    simp only [dilate, Nat.pow_zero, evalStream, sShl_allOnes_one, ← sXor_assoc, sXor_self, sZero_xor]
  | allOnes => rfl
  | var _ => rfl
  | xor a b iha ihb =>
    simp only [isLaneSafe, Bool.and_eq_true] at hs
    simp [dilate, evalStream, iha hs.1, ihb hs.2]
  | and a b iha ihb =>
    simp only [isLaneSafe, Bool.and_eq_true] at hs
    simp [dilate, evalStream, iha hs.1, ihb hs.2]
  | shl a s iha =>
    simp only [isLaneSafe] at hs
    simp [dilate, evalStream, iha hs]
  | clmul a b iha ihb =>
    simp only [isLaneSafe, Bool.or_eq_true, Bool.and_eq_true] at hs
    simp only [dilate]
    by_cases hcb : isConst b = true
    · simp only [hcb, ↓reduceIte, Expr.frob, evalStream]
      rcases hs with ⟨hsa, _⟩ | ⟨hca, _⟩
      · rw [iha hsa]
      · rw [iha (isLaneSafe_of_isConst a hca)]
    · have hbf : isConst b = false := Bool.eq_false_iff.mpr hcb
      rcases hs with ⟨_, hcb'⟩ | ⟨hca, hsb⟩
      · exact absurd hcb' hcb
      · simp [hbf, hca, Expr.frob, evalStream, ihb hsb]

theorem cartier_dilate_succ (r : Nat) (σ : Nat → Stream) (e : Expr) (hs : isLaneSafe e = true) :
    sEv (evalStream σ (dilate (r + 1) e)) = evalStream (fun i => sEv (σ i)) (dilate r e) ∧
    sOd (evalStream σ (dilate (r + 1) e)) = evalStream (fun i => sOd (σ i)) (dilate r e) := by
  induction e with
  | zero => exact ⟨rfl, rfl⟩
  | one =>
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ]; omega
    simp only [dilate, evalStream, hpow, sEv_xor, sOd_xor, sEv_allOnes, sOd_allOnes,
               sEv_shl_even, sOd_shl_even, and_self]
  | allOnes => exact ⟨rfl, rfl⟩
  | var i => exact ⟨rfl, rfl⟩
  | xor a b iha ihb =>
    simp only [isLaneSafe, Bool.and_eq_true] at hs
    simp only [dilate, evalStream, sEv_xor, sOd_xor, (iha hs.1).1, (iha hs.1).2,
               (ihb hs.2).1, (ihb hs.2).2, and_self]
  | and a b iha ihb =>
    simp only [isLaneSafe, Bool.and_eq_true] at hs
    simp only [dilate, evalStream, sEv_and, sOd_and, (iha hs.1).1, (iha hs.1).2,
               (ihb hs.2).1, (ihb hs.2).2, and_self]
  | shl a s iha =>
    simp only [isLaneSafe] at hs
    have hmul : s * 2 ^ (r + 1) = 2 * (s * 2 ^ r) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, ← Nat.mul_assoc, Nat.mul_comm s 2, Nat.mul_assoc]
    simp only [dilate, evalStream, hmul, sEv_shl_even, sOd_shl_even, (iha hs).1, (iha hs).2, and_self]
  | clmul a b iha ihb =>
    simp only [isLaneSafe, Bool.or_eq_true, Bool.and_eq_true] at hs
    simp only [dilate]
    by_cases hcb : isConst b = true
    · have hsa : isLaneSafe a = true := by
        rcases hs with ⟨hsa, _⟩ | ⟨hca, _⟩
        · exact hsa
        · exact isLaneSafe_of_isConst a hca
      simp only [hcb, ↓reduceIte, evalStream, evalStream_frob, sFrob]
      rw [sEv_clmul_frob1_right, sOd_clmul_frob1_right, (iha hsa).1, (iha hsa).2]
      rw [evalStream_isConst_independent b hcb σ (fun i => sEv (σ i))]
      have hconst2 := evalStream_isConst_independent b hcb (fun i => sEv (σ i)) (fun i => sOd (σ i))
      exact ⟨rfl, by rw [hconst2]⟩
    · have hbf : isConst b = false := Bool.eq_false_iff.mpr hcb
      rcases hs with ⟨_, hcb'⟩ | ⟨hca, hsb⟩
      · exact absurd hcb' hcb
      · simp only [hbf, Bool.false_eq_true, ↓reduceIte, hca, evalStream, evalStream_frob, sFrob]
        rw [sEv_clmul_frob1_left, sOd_clmul_frob1_left, (ihb hsb).1, (ihb hsb).2]
        rw [evalStream_isConst_independent a hca σ (fun i => sEv (σ i))]
        have hconst2 := evalStream_isConst_independent a hca (fun i => sEv (σ i)) (fun i => sOd (σ i))
        exact ⟨rfl, by rw [hconst2]⟩

theorem dilate_sound_all_scales (e1 e2 : Expr)
    (hs1 : isLaneSafe e1 = true) (hs2 : isLaneSafe e2 = true)
    (h0 : ∀ σ : Nat → Stream, evalStream σ e1 = evalStream σ e2) :
    ∀ (r : Nat) (σ : Nat → Stream), evalStream σ (dilate r e1) = evalStream σ (dilate r e2) := by
  intro r; induction r with
  | zero =>
    intro σ; rw [evalStream_dilate_zero σ e1 hs1, evalStream_dilate_zero σ e2 hs2]; exact h0 σ
  | succ r ih =>
    intro σ; apply cartier_bisim
    · rw [(cartier_dilate_succ r σ e1 hs1).1, (cartier_dilate_succ r σ e2 hs2).1]
      exact ih (fun i => sEv (σ i))
    · rw [(cartier_dilate_succ r σ e1 hs1).2, (cartier_dilate_succ r σ e2 hs2).2]
      exact ih (fun i => sOd (σ i))

/-- **META-THEOREM 3 (Dyadic Lane-Replication Lifting: Single Finite Cert → ∀ r w, BitVec w)** -/
theorem reflect_all_scales_and_widths (e1 e2 : Expr) (c : Cert)
    (hs1 : isLaneSafe e1 = true) (hs2 : isLaneSafe e2 = true)
    (h : checkCert e1 e2 c = true) :
    ∀ (r w : Nat) (env : Nat → BitVec w),
      evalBV w env (dilate r e1) = evalBV w env (dilate r e2) := by
  intro r
  exact lift_stream_to_all_bitvec (dilate r e1) (dilate r e2)
    (dilate_sound_all_scales e1 e2 hs1 hs2 (checkCert_sound e1 e2 c h) r)

theorem bvFrob_add {w : Nat} (r k : Nat) (a : BitVec w) :
    bvFrob r (bvFrob k a) = bvFrob (r + k) a := by
  induction r with
  | zero => simp [bvFrob]
  | succ r ih =>
    have h1 : r + 1 + k = (r + k) + 1 := by omega
    rw [h1, bvFrob, bvFrob, ih]

theorem isConst_eMask (k : Nat) : isConst (Expr.eMask k) = true := by
  unfold Expr.eMask
  induction k with
  | zero => rfl
  | succ k ih => simp [Expr.frob, isConst, ih]

theorem evalBV_dilate_prefixR (r k w : Nat) (env : Nat → BitVec w) (e : Expr) :
    evalBV w env (dilate r (Expr.prefixR k e)) = bvPr (r + k) (evalBV w env (dilate r e)) := by
  simp only [Expr.prefixR, dilate, isConst_eMask, ↓reduceIte, evalBV, evalBV_frob, evalBV_eMask,
             bvPr, bvE, bvFrob_add]

-- ============================================================================
-- SECTION 5: Discharged Novel Infinite Theorem Families (Pure `BitVec w`!)
-- ============================================================================

-- FAMILY 1: Dyadic Rota–Baxter / Binary Itô–Leibniz Tower

def ito2LHS : Expr := .and (Expr.prefixR 0 (.var 0)) (Expr.prefixR 0 (.var 1))

def ito2RHS : Expr :=
  Expr.prefixR 0
    (.xor (.xor (.and (.var 0) (Expr.prefixR 0 (.var 1)))
                (.and (.var 1) (Expr.prefixR 0 (.var 0))))
          (.and (.var 0) (.var 1)))

/-- **THEOREM 1A (Doubly Infinite Weight-1 Rota–Baxter Law for `bvPr`)**. -/
theorem binary_ito2_all_scales_widths :
    ∀ (r w : Nat) (a b : BitVec w),
      bvPr r a &&& bvPr r b =
      bvPr r (((a &&& bvPr r b) ^^^ (b &&& bvPr r a)) ^^^ (a &&& b)) := by
  have hmain := reflect_all_scales_and_widths ito2LHS ito2RHS (.cancelDelta 0 (.normEq 4))
    (by decide) (by decide) (by decide)
  intro r w a b
  have h := hmain r w (fun i => if i == 0 then a else b)
  simpa [ito2LHS, ito2RHS, dilate, evalBV, evalBV_dilate_prefixR] using h

def ito3LHS : Expr :=
  .and (.and (Expr.prefixR 0 (.var 0)) (Expr.prefixR 0 (.var 1))) (Expr.prefixR 0 (.var 2))

def ito3RHS : Expr :=
  let a := Expr.var 0; let b := Expr.var 1; let c := Expr.var 2
  let pa := Expr.prefixR 0 a; let pb := Expr.prefixR 0 b; let pc := Expr.prefixR 0 c
  Expr.prefixR 0
    (.xor (.xor (.xor (.xor (.xor (.xor
      (.and (.and a pb) pc)
      (.and (.and b pa) pc))
      (.and (.and c pa) pb))
      (.and (.and a b) pc))
      (.and (.and a c) pb))
      (.and (.and b c) pa))
      (.and (.and a b) c))

/-- **THEOREM 1B (Doubly Infinite 3-Variable Binary Itô–Leibniz Law)**. -/
theorem binary_ito3_all_scales_widths :
    ∀ (r w : Nat) (a b c : BitVec w),
      bvPr r a &&& bvPr r b &&& bvPr r c =
      bvPr r (((((((a &&& bvPr r b &&& bvPr r c)
               ^^^ (b &&& bvPr r a &&& bvPr r c))
               ^^^ (c &&& bvPr r a &&& bvPr r b))
               ^^^ (a &&& b &&& bvPr r c))
               ^^^ (a &&& c &&& bvPr r b))
               ^^^ (b &&& c &&& bvPr r a))
               ^^^ (a &&& b &&& c)) := by
  have hmain := reflect_all_scales_and_widths ito3LHS ito3RHS (.cancelDelta 0 (.normEq 4))
    (by decide) (by decide) (by decide)
  intro r w a b c
  have h := hmain r w (fun i => if i == 0 then a else if i == 1 then b else c)
  simpa [ito3LHS, ito3RHS, dilate, evalBV, evalBV_dilate_prefixR] using h

def andRangeBool : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => andRangeBool n f && f n

theorem bvAndRange_getLsbD {w : Nat} (n : Nat) (f : Nat → BitVec w) (k : Nat) (hk : k < w) :
    (bvAndRange n f).getLsbD k = andRangeBool n (fun i => (f i).getLsbD k) := by
  induction n with
  | zero => simp [bvAndRange, andRangeBool, hk]
  | succ n ih => simp [bvAndRange, andRangeBool, ih]

theorem andRangeBool_congr (n : Nat) (f g : Nat → Bool) (h : ∀ i, i < n → f i = g i) :
    andRangeBool n f = andRangeBool n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [andRangeBool, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem bool_prod_xor_expansion' (n : Nat) (p a : Nat → Bool) :
    xorSum (2 ^ n) (fun m => andRangeBool n (fun i => if (m >>> i) % 2 == 1 then a i else p i)) =
    andRangeBool n (fun i => p i ^^ a i) := by
  induction n with
  | zero => simp [xorSum, andRangeBool]
  | succ n ih =>
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    rw [hpow, xorSum_add]
    have hlow : ∀ m, m < 2 ^ n → ((m >>> n) % 2 == 1) = false := by
      intro m hm; rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hm]; rfl
    have hhigh : ∀ m, m < 2 ^ n → (((2 ^ n + m) >>> n) % 2 == 1) = true := by
      intro m hm
      rw [Nat.shiftRight_eq_div_pow]
      have hpos : 0 < 2 ^ n := Nat.pow_pos (by omega)
      have h1 : 2 ^ n + m = m + 2 ^ n * 1 := by omega
      rw [h1, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hm]; rfl
    have hbit_low : ∀ m k, k < n → ((2 ^ n + m) >>> k) % 2 = (m >>> k) % 2 := by
      intro m k hk
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have hpowk : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← Nat.pow_add]; congr 1; omega
      have hposk : 0 < 2 ^ k := Nat.pow_pos (by omega)
      have h2div : 2 ^ (n - k) = 2 * 2 ^ (n - k - 1) := by
        have : n - k = (n - k - 1) + 1 := by omega
        conv => lhs; rw [this, Nat.pow_succ]
        omega
      have hadd : (2 ^ n + m) / 2 ^ k = m / 2 ^ k + 2 * 2 ^ (n - k - 1) := by
        rw [hpowk, h2div, Nat.add_comm, Nat.add_mul_div_left _ _ hposk]
      rw [hadd, Nat.add_mul_mod_self_left]
    have hL : xorSum (2 ^ n) (fun m =>
        andRangeBool (n + 1) (fun i => if (m >>> i) % 2 == 1 then a i else p i)) =
      xorSum (2 ^ n) (fun m =>
        andRangeBool n (fun i => if (m >>> i) % 2 == 1 then a i else p i) && p n) := by
      apply xorSum_congr; intro m hm; simp only [andRangeBool, hlow m hm, Bool.false_eq_true, ↓reduceIte]
    have hR : xorSum (2 ^ n) (fun m =>
        andRangeBool (n + 1) (fun i => if ((2 ^ n + m) >>> i) % 2 == 1 then a i else p i)) =
      xorSum (2 ^ n) (fun m =>
        andRangeBool n (fun i => if (m >>> i) % 2 == 1 then a i else p i) && a n) := by
      apply xorSum_congr; intro m hm
      simp only [andRangeBool, hhigh m hm, ↓reduceIte]
      congr 1
      apply andRangeBool_congr; intro k hk
      rw [hbit_low m k hk]
    rw [hL, hR, xorSum_and_right, xorSum_and_right, ih, ← band_bxor_distrib_left]
    rfl

/-- **THEOREM 1D (TRIPLE-INFINITE `n`-Variable Binary Itô–Leibniz / Quasi-Shuffle Theorem)**. -/
theorem binary_ito_general_n (n r w : Nat) (hn : 1 ≤ n) (xs : Nat → BitVec w) :
    bvAndRange n (fun i => bvPr r (xs i)) =
    bvPr r (bvXorRange (2 ^ n - 1) (fun m =>
      bvAndRange n (fun i => if ((m + 1) >>> i) % 2 == 1 then xs i else bvPr r (xs i)))) := by
  let sx : Nat → Stream := fun i j => (xs i).getLsbD j
  let sP : Nat → Stream := fun i => sClmul (sx i) (sE r)
  let sLHS : Stream := fun k => andRangeBool n (fun i => sP i k)
  let sBody : Stream := fun k =>
    xorSum (2 ^ n - 1) (fun m =>
      andRangeBool n (fun i => if ((m + 1) >>> i) % 2 == 1 then sx i k else sP i k))
  let sRHS : Stream := sClmul sBody (sE r)
  have hStream : sLHS = sRHS := by
    apply sDelta_injective r
    have hRHS_delta : sXor sRHS (sShl sRHS (2 ^ r)) = sBody := by
      dsimp only [sRHS]
      rw [← sClmul_shl_left, ← sClmul_xor_left, sClmul_delta_E]
    rw [hRHS_delta]
    funext k
    simp only [sXor, sShl, sLHS, sBody]
    have hpowpos : 1 ≤ 2 ^ n := Nat.pow_pos (by omega)
    have h2n : 2 ^ n = (2 ^ n - 1) + 1 := by omega
    have hshift : ∀ i, sShl (sP i) (2 ^ r) k = (sP i k ^^ sx i k) := by
      intro i
      have hd : sXor (sP i) (sShl (sP i) (2 ^ r)) = sx i := by
        have := sClmul_delta_E r (sx i)
        rw [sClmul_xor_left, sClmul_shl_left] at this
        exact this
      have hk := congrFun hd k
      simp only [sXor] at hk
      rw [← hk]; cases sP i k <;> cases sShl (sP i) (2 ^ r) k <;> rfl
    have hShlLHS : (if 2 ^ r ≤ k then andRangeBool n (fun i => sP i (k - 2 ^ r)) else false) =
        andRangeBool n (fun i => sP i k ^^ sx i k) := by
      by_cases hk : 2 ^ r ≤ k
      · simp only [hk, ↓reduceIte]
        apply andRangeBool_congr; intro i _
        have := hshift i
        simp only [sShl, hk, ↓reduceIte] at this
        exact this
      · simp only [hk, ↓reduceIte]
        have hzero_all : ∀ i, (sP i k ^^ sx i k) = false := by
          intro i
          have := hshift i
          simp only [sShl, hk, ↓reduceIte] at this
          exact this.symm
        match n, hn with
        | n' + 1, _ => simp only [andRangeBool, hzero_all n', Bool.and_false]
    rw [hShlLHS, ← bool_prod_xor_expansion' n (fun i => sP i k) (fun i => sx i k)]
    rw [h2n, xorSum_succ_shift]
    have hm0 : andRangeBool n (fun i => if (0 >>> i) % 2 == 1 then sx i k else sP i k) =
        andRangeBool n (fun i => sP i k) := by
      apply andRangeBool_congr; intro i _
      have : (0 >>> i) % 2 = 0 := by simp
      rw [this]; rfl
    rw [hm0, ← bxor_assoc, bxor_self, false_bxor]
    apply xorSum_congr; intro m _
    apply andRangeBool_congr; intro i _
    rfl
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [bvAndRange_getLsbD n _ k hk, bvPr_getLsbD r _ k hk]
  have hL : andRangeBool n (fun i => (bvPr r (xs i)).getLsbD k) = sLHS k := by
    apply andRangeBool_congr; intro i _; exact bvPr_getLsbD r (xs i) k hk
  have hR : sClmul (fun j => (bvXorRange (2 ^ n - 1) (fun m =>
        bvAndRange n (fun i => if ((m + 1) >>> i) % 2 == 1 then xs i else bvPr r (xs i)))).getLsbD j)
      (sE r) k = sRHS k := by
    simp only [sRHS, sClmul]
    apply xorSum_congr; intro j hj
    congr 1
    rw [bvXorRange_getLsbD]
    apply xorSum_congr; intro m _
    rw [bvAndRange_getLsbD n _ j (by omega)]
    apply andRangeBool_congr; intro i _
    split
    · rfl
    · exact bvPr_getLsbD r (xs i) j (by omega)
  rw [hL, hR]
  exact congrFun hStream k

/-- **THEOREM 1C (Doubly Infinite 4-Variable Binary Itô–Leibniz Law — Explicit 15-Term Expansion)**.
    Corresponds to the `n = 4` specialization of `binary_ito_general_n` (also compiled as a
    finite `CHReflect` certificate in `explore_and_verify.py`). -/
theorem binary_ito4_all_scales_widths (r w : Nat) (a b c d : BitVec w) :
    bvPr r a &&& bvPr r b &&& bvPr r c &&& bvPr r d =
    bvPr r (
      ((((((((((((((a &&& bvPr r b &&& bvPr r c &&& bvPr r d)
                ^^^ (bvPr r a &&& b &&& bvPr r c &&& bvPr r d))
                ^^^ (a &&& b &&& bvPr r c &&& bvPr r d))
                ^^^ (bvPr r a &&& bvPr r b &&& c &&& bvPr r d))
                ^^^ (a &&& bvPr r b &&& c &&& bvPr r d))
                ^^^ (bvPr r a &&& b &&& c &&& bvPr r d))
                ^^^ (a &&& b &&& c &&& bvPr r d))
                ^^^ (bvPr r a &&& bvPr r b &&& bvPr r c &&& d))
                ^^^ (a &&& bvPr r b &&& bvPr r c &&& d))
                ^^^ (bvPr r a &&& b &&& bvPr r c &&& d))
                ^^^ (a &&& b &&& bvPr r c &&& d))
                ^^^ (bvPr r a &&& bvPr r b &&& c &&& d))
                ^^^ (a &&& bvPr r b &&& c &&& d))
                ^^^ (bvPr r a &&& b &&& c &&& d))
                ^^^ (a &&& b &&& c &&& d)) := by
  have h := binary_ito_general_n 4 r w (by omega)
    (fun i => match i with | 0 => a | 1 => b | 2 => c | _ => d)
  have h0 : ∀ x : BitVec w, (~~~(0 : BitVec w)) &&& x = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
  have hx0 : ∀ x : BitVec w, (0 : BitVec w) ^^^ x = x := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]
  simpa [bvAndRange, bvXorRange, h0, hx0] using h

-- FAMILY 2: Doubly Infinite Dyadic Scale-Ladder Theorems

def selfLadderLHS : Expr := .and (Expr.prefixR 0 (.var 0)) (Expr.prefixR 1 (.var 0))

def selfLadderRHS : Expr :=
  .xor (Expr.prefixR 1 (.var 0))
       (Expr.prefixR 0 (.and (.var 0) (.xor (Expr.prefixR 0 (.var 0)) (Expr.prefixR 1 (.var 0)))))

/-- **THEOREM 2A (Doubly Infinite Dyadic Scale-Ladder Identity)**. -/
theorem self_scale_ladder_all_scales_widths :
    ∀ (r w : Nat) (a : BitVec w),
      bvPr r a &&& bvPr (r + 1) a =
      bvPr (r + 1) a ^^^ bvPr r (a &&& (bvPr r a ^^^ bvPr (r + 1) a)) := by
  have hmain := reflect_all_scales_and_widths selfLadderLHS selfLadderRHS (.cancelDelta 0 (.normEq 4))
    (by decide) (by decide) (by decide)
  intro r w a
  have h := hmain r w (fun _ => a)
  simpa [selfLadderLHS, selfLadderRHS, dilate, evalBV, evalBV_dilate_prefixR] using h

def twoLadderLHS : Expr := .and (Expr.prefixR 0 (.var 0)) (Expr.prefixR 2 (.var 0))

def twoLadderRHS : Expr :=
  Expr.prefixR 0
    (.xor (.and (.var 0) (Expr.prefixR 2 (.var 0)))
          (.and (.xor (.var 0) (Expr.prefixR 0 (.var 0)))
                (Expr.prefixR 0 (Expr.prefixR 1 (.var 0)))))

/-- **THEOREM 2B (Doubly Infinite Two-Scale Dyadic Ladder Identity)**. -/
theorem two_scale_ladder_all_scales_widths :
    ∀ (r w : Nat) (a : BitVec w),
      bvPr r a &&& bvPr (r + 2) a =
      bvPr r ((a &&& bvPr (r + 2) a) ^^^ ((a ^^^ bvPr r a) &&& bvPr r (bvPr (r + 1) a))) := by
  have hmain := reflect_all_scales_and_widths twoLadderLHS twoLadderRHS (.cancelDelta 0 (.normEq 5))
    (by decide) (by decide) (by decide)
  intro r w a
  have h := hmain r w (fun _ => a)
  simpa [twoLadderLHS, twoLadderRHS, dilate, evalBV, evalBV_dilate_prefixR] using h

-- FAMILY 3: Z/2^r Z-Graded Carryless–Hadamard Convolution Splitting

def buildResConvRHS (r t : Nat) : Nat → Expr
  | 0 => .zero
  | u + 1 =>
    let mod := 2 ^ r
    let v := (t + mod - u) % mod
    let term := .clmul (.and (.var 0) (.shl (Expr.eMask r) u))
                       (.and (.var 1) (.shl (Expr.eMask r) v))
    if u == 0 then term else .xor (buildResConvRHS r t u) term

def resConvLHS (r t : Nat) : Expr := .and (.clmul (.var 0) (.var 1)) (.shl (Expr.eMask r) t)

def resConvRHS (r t : Nat) : Expr := buildResConvRHS r t (2 ^ r)

/-- Concrete `r = 1, t = 0`: discharged purely by depth-1 Cartier certificate via `by decide`. -/
theorem residue_conv_split_r1_t0 :
    ∀ (w : Nat) (a b : BitVec w),
      bvClmul a b &&& bvE w 1 =
      bvClmul (a &&& bvE w 1) (b &&& bvE w 1) ^^^
      bvClmul (a &&& (bvE w 1 <<< 1)) (b &&& (bvE w 1 <<< 1)) := by
  have hmain := reflect_all_bitvec (resConvLHS 1 0) (resConvRHS 1 0) (mkCartierCert 4 1) (by decide)
  intro w a b
  have h := hmain w (fun i => if i == 0 then a else b)
  simpa [resConvLHS, resConvRHS, buildResConvRHS, evalBV, evalBV_eMask] using h

/-- Concrete `r = 1, t = 1`: discharged purely by depth-1 Cartier certificate via `by decide`. -/
theorem residue_conv_split_r1_t1 :
    ∀ (w : Nat) (a b : BitVec w),
      bvClmul a b &&& (bvE w 1 <<< 1) =
      bvClmul (a &&& bvE w 1) (b &&& (bvE w 1 <<< 1)) ^^^
      bvClmul (a &&& (bvE w 1 <<< 1)) (b &&& bvE w 1) := by
  have hmain := reflect_all_bitvec (resConvLHS 1 1) (resConvRHS 1 1) (mkCartierCert 4 1) (by decide)
  intro w a b
  have h := hmain w (fun i => if i == 0 then a else b)
  simpa [resConvLHS, resConvRHS, buildResConvRHS, evalBV, evalBV_eMask] using h

/-- Concrete `r = 2, t = 1` (4-channel mod-4 splitting): discharged by depth-2 Cartier cert via `by decide`. -/
theorem residue_conv_split_r2_t1 :
    ∀ (w : Nat) (env : Nat → BitVec w),
      evalBV w env (resConvLHS 2 1) = evalBV w env (resConvRHS 2 1) :=
  reflect_all_bitvec (resConvLHS 2 1) (resConvRHS 2 1) (mkCartierCert 4 2) (by decide)

/-- Concrete `r = 2, t = 3` (4-channel mod-4 splitting): discharged by depth-2 Cartier cert via `by decide`. -/
theorem residue_conv_split_r2_t3 :
    ∀ (w : Nat) (env : Nat → BitVec w),
      evalBV w env (resConvLHS 2 3) = evalBV w env (resConvRHS 2 3) :=
  reflect_all_bitvec (resConvLHS 2 3) (resConvRHS 2 3) (mkCartierCert 4 2) (by decide)

theorem sShl_sE_bit (r t k : Nat) (ht : t < 2 ^ r) :
    sShl (sE r) t k = (k % 2 ^ r == t) := by
  simp only [sShl, sE, sFrob_bit, sAllOnes]
  by_cases htk : t ≤ k
  · simp only [htk, ↓reduceIte]
    cases h : ((k - t) % 2 ^ r == 0)
    · rw [beq_eq_false_iff_ne] at h
      simp only [Bool.false_eq_true, ↓reduceIte]
      symm; rw [beq_eq_false_iff_ne]
      intro hmod; apply h
      have hd := Nat.div_add_mod k (2 ^ r)
      have hk : k - t = 2 ^ r * (k / 2 ^ r) := by omega
      rw [hk, Nat.mul_mod_right]
    · rw [beq_iff_eq] at h
      simp only [↓reduceIte]
      symm; rw [beq_iff_eq]
      have hd := Nat.div_add_mod (k - t) (2 ^ r)
      have hk : k = t + 2 ^ r * ((k - t) / 2 ^ r) := by omega
      rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  · simp only [htk, ↓reduceIte]
    symm; rw [beq_eq_false_iff_ne]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- **THEOREM 3 (UNIVERSAL `Z/2^r Z`-Graded Carryless–Hadamard Convolution Splitting)**. -/
theorem residue_conv_split_all_r_w (r t w : Nat) (ht : t < 2 ^ r) (a b : BitVec w) :
    bvClmul a b &&& (bvE w r <<< t) =
    bvXorRange (2 ^ r) (fun u =>
      bvClmul (a &&& (bvE w r <<< u))
              (b &&& (bvE w r <<< ((t + 2 ^ r - u) % 2 ^ r)))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, bvClmul_getLsbD a b k hk, bvXorRange_getLsbD]
  have hEmask : ∀ s, s < 2 ^ r → ∀ j, j < w →
      (bvE w r <<< s).getLsbD j = (j % 2 ^ r == s) := by
    intro s hs j hj
    rw [BitVec.getLsbD_shiftLeft]
    simp only [hj, decide_true, Bool.true_and]
    rw [← sShl_sE_bit r s j hs]
    simp only [sShl]
    by_cases hsj : s ≤ j
    · have hnot : ¬ (j < s) := by omega
      simp [hsj, hnot, bvE_getLsbD w r (j - s) (by omega)]
    · have hlt : j < s := by omega
      simp [hsj, hlt]
  rw [hEmask t ht k hk]
  have hRHS : xorSum (2 ^ r) (fun u =>
      (bvClmul (a &&& (bvE w r <<< u))
               (b &&& (bvE w r <<< ((t + 2 ^ r - u) % 2 ^ r)))).getLsbD k) =
      xorSum (2 ^ r) (fun u =>
        xorSum (k + 1) (fun i =>
          (a.getLsbD i && (i % 2 ^ r == u)) &&
          (b.getLsbD (k - i) && ((k - i) % 2 ^ r == (t + 2 ^ r - u) % 2 ^ r)))) := by
    apply xorSum_congr; intro u hu
    rw [bvClmul_getLsbD _ _ k hk]
    simp only [sClmul]
    apply xorSum_congr; intro i hi
    have hv : (t + 2 ^ r - u) % 2 ^ r < 2 ^ r := Nat.mod_lt _ (Nat.pow_pos (by omega))
    rw [BitVec.getLsbD_and, BitVec.getLsbD_and,
        hEmask u hu i (by omega), hEmask _ hv (k - i) (by omega)]
  rw [hRHS, xorSum_swap]
  simp only [sClmul, ← xorSum_and_right]
  apply xorSum_congr; intro i hi
  have hi_mod : i % 2 ^ r < 2 ^ r := Nat.mod_lt i (Nat.pow_pos (by omega))
  rw [xorSum_single (2 ^ r) (i % 2 ^ r) _ hi_mod]
  · simp only [beq_self_eq_true, Bool.and_true]
    have hmod_eq : ((k - i) % 2 ^ r == (t + 2 ^ r - i % 2 ^ r) % 2 ^ r) = (k % 2 ^ r == t) := by
      have hki : i + (k - i) = k := by omega
      have hpos : 0 < 2 ^ r := Nat.pow_pos (by omega)
      have h1 : (i % 2 ^ r + (k - i) % 2 ^ r) % 2 ^ r = k % 2 ^ r := by
        rw [← Nat.add_mod, hki]
      have h2 : (i % 2 ^ r + (t + 2 ^ r - i % 2 ^ r) % 2 ^ r) % 2 ^ r = t := by
        have hstep : (i % 2 ^ r + (t + 2 ^ r - i % 2 ^ r) % 2 ^ r) % 2 ^ r =
            (i % 2 ^ r + (t + 2 ^ r - i % 2 ^ r)) % 2 ^ r := by
          have ha := Nat.add_mod (i % 2 ^ r) ((t + 2 ^ r - i % 2 ^ r) % 2 ^ r) (2 ^ r)
          have hb := Nat.add_mod (i % 2 ^ r) (t + 2 ^ r - i % 2 ^ r) (2 ^ r)
          rw [ha, hb, Nat.mod_mod, Nat.mod_mod]
        have hsum : i % 2 ^ r + (t + 2 ^ r - i % 2 ^ r) = t + 2 ^ r := by omega
        rw [hstep, hsum, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
      cases h : (k % 2 ^ r == t)
      · rw [beq_eq_false_iff_ne] at h ⊢
        intro heq; apply h
        rw [heq] at h1; omega
      · rw [beq_iff_eq] at h ⊢
        rw [h] at h1
        have hltA : (k - i) % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpos
        have hltB : (t + 2 ^ r - i % 2 ^ r) % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpos
        have hmod_cancel : ∀ x y : Nat, x < 2 ^ r → y < 2 ^ r →
            (i % 2 ^ r + x) % 2 ^ r = (i % 2 ^ r + y) % 2 ^ r → x = y := by
          intro x y hx hy heqxy
          have hsub : ∀ z : Nat, z < 2 ^ r → ¬ (i % 2 ^ r + z < 2 ^ r) →
              (i % 2 ^ r + z) % 2 ^ r = i % 2 ^ r + z - 2 ^ r := by
            intro z hz hge
            have hlt2 : i % 2 ^ r + z - 2 ^ r < 2 ^ r := by omega
            have hadd : (i % 2 ^ r + z - 2 ^ r) + 2 ^ r = i % 2 ^ r + z := by omega
            calc (i % 2 ^ r + z) % 2 ^ r
                = ((i % 2 ^ r + z - 2 ^ r) + 2 ^ r) % 2 ^ r := by rw [hadd]
              _ = (i % 2 ^ r + z - 2 ^ r) % 2 ^ r := Nat.add_mod_right _ _
              _ = i % 2 ^ r + z - 2 ^ r := Nat.mod_eq_of_lt hlt2
          by_cases h1x : i % 2 ^ r + x < 2 ^ r
          · rw [Nat.mod_eq_of_lt h1x] at heqxy
            by_cases h1y : i % 2 ^ r + y < 2 ^ r
            · rw [Nat.mod_eq_of_lt h1y] at heqxy; omega
            · rw [hsub y hy h1y] at heqxy; omega
          · rw [hsub x hx h1x] at heqxy
            by_cases h1y : i % 2 ^ r + y < 2 ^ r
            · rw [Nat.mod_eq_of_lt h1y] at heqxy; omega
            · rw [hsub y hy h1y] at heqxy; omega
        exact hmod_cancel _ _ hltA hltB (h1.trans h2.symm)
    rw [hmod_eq, Bool.and_assoc]
  · intro u _ hne
    have hf : (i % 2 ^ r == u) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp [hf]

-- FAMILY 4: Frobenius–Hadamard Orthogonality, Residue-Filtered Convolution,
--   Sierpinski/Pascal Inverses, & Right-Shift Truncation Laws

/-- **THEOREM 4A (Universal Frobenius–Hadamard Residue Orthogonality)**. -/
theorem frob_hadamard_orthogonal_all (r s1 s2 w : Nat) (hne : s1 % 2 ^ r ≠ s2 % 2 ^ r)
    (a b : BitVec w) :
    (bvFrob r a <<< s1) &&& (bvFrob r b <<< s2) = 0 := by
  have h := lift_stream_to_all_bitvec
    (.and (.shl (Expr.frob r (.var 0)) s1) (.shl (Expr.frob r (.var 1)) s2))
    .zero
    (fun σ => by
      simp only [evalStream, evalStream_frob]
      exact sFrob_and_orthogonal r s1 s2 (σ 0) (σ 1) hne)
    w (fun i => if i == 0 then a else b)
  simpa [evalBV, evalBV_frob] using h

/-- **THEOREM 4B (Universal Residue-Filtered Convolution Law — Sharp at `s2 < 2^r`)**. -/
theorem res_mask_conv_all (r s1 s2 w : Nat) (hs2 : s2 < 2 ^ r) (a b : BitVec w) :
    bvClmul (bvFrob r a <<< s1) (b &&& (bvE w r <<< s2)) =
    bvClmul (bvFrob r a <<< s1) b &&& (bvE w r <<< (s1 + s2)) := by
  have h := lift_stream_to_all_bitvec
    (.clmul (.shl (Expr.frob r (.var 0)) s1) (.and (.var 1) (.shl (Expr.eMask r) s2)))
    (.and (.clmul (.shl (Expr.frob r (.var 0)) s1) (.var 1)) (.shl (Expr.eMask r) (s1 + s2)))
    (fun σ => by
      simp only [evalStream, evalStream_frob, Expr.eMask]
      change sClmul (sShl (sFrob r (σ 0)) s1) (sAnd (σ 1) (sShl (sE r) s2)) =
             sAnd (sClmul (sShl (sFrob r (σ 0)) s1) (σ 1)) (sShl (sE r) (s1 + s2))
      rw [sClmul_shl_left, sClmul_shl_left, Nat.add_comm s1 s2, ← sShl_shl (sE r) s2 s1, ← sShl_and]
      congr 1
      funext k
      simp only [sClmul, sAnd, sFrob_bit]
      rw [sShl_sE_bit r s2 k hs2, ← xorSum_and_right]
      apply xorSum_congr; intro i hi
      rw [sShl_sE_bit r s2 (k - i) hs2]
      by_cases hmi : i % 2 ^ r = 0
      · have hmib : (i % 2 ^ r == 0) = true := beq_iff_eq.mpr hmi
        simp only [hmib, ↓reduceIte]
        have hkeq : (k - i) % 2 ^ r = k % 2 ^ r := by
          have hd := Nat.div_add_mod i (2 ^ r)
          have h1 : k = (k - i) + 2 ^ r * (i / 2 ^ r) := by omega
          conv => rhs; rw [h1, Nat.add_mul_mod_self_left]
        rw [hkeq, Bool.and_assoc]
      · have hmib : (i % 2 ^ r == 0) = false := beq_eq_false_iff_ne.mpr hmi
        simp [hmib])
    w (fun i => if i == 0 then a else b)
  simpa [evalBV, evalBV_frob, evalBV_eMask, bvE] using h

def powClmul : Nat → Expr → Expr
  | 0, _ => .one
  | d + 1, e => .clmul (powClmul d e) e

def sierpinskiInvLHS (d : Nat) : Expr :=
  .clmul (powClmul d .allOnes) (powClmul d (.xor .one (.shl .one 1)))

/-- **THEOREM 4C (Sierpinski / Pascal Carryless Inverse Family `d = 1..6` via `by decide`)**. -/
theorem sierpinski_inverse_d1_to_d6 :
    (∀ w env, evalBV w env (sierpinskiInvLHS 1) = BitVec.ofNat w 1) ∧
    (∀ w env, evalBV w env (sierpinskiInvLHS 2) = BitVec.ofNat w 1) ∧
    (∀ w env, evalBV w env (sierpinskiInvLHS 3) = BitVec.ofNat w 1) ∧
    (∀ w env, evalBV w env (sierpinskiInvLHS 4) = BitVec.ofNat w 1) ∧
    (∀ w env, evalBV w env (sierpinskiInvLHS 5) = BitVec.ofNat w 1) ∧
    (∀ w env, evalBV w env (sierpinskiInvLHS 6) = BitVec.ofNat w 1) :=
  ⟨reflect_all_bitvec _ .one (.normEq 4) (by decide),
   reflect_all_bitvec _ .one (.normEq 4) (by decide),
   reflect_all_bitvec _ .one (.normEq 5) (by decide),
   reflect_all_bitvec _ .one (.normEq 5) (by decide),
   reflect_all_bitvec _ .one (.normEq 6) (by decide),
   reflect_all_bitvec _ .one (.normEq 6) (by decide)⟩

def buildPartUnity (r : Nat) : Nat → Expr
  | 0 => .zero
  | u + 1 =>
    let term := .shl (Expr.eMask r) u
    if u == 0 then term else .xor (buildPartUnity r u) term

/-- **THEOREM 4C' (Dyadic Residue-Mask Partition of Unity `r = 1, 2, 3` via `by decide`)**. -/
theorem partition_of_unity_r1_to_r3 :
    (∀ w env, evalBV w env (buildPartUnity 1 2) = ~~~(0 : BitVec w)) ∧
    (∀ w env, evalBV w env (buildPartUnity 2 4) = ~~~(0 : BitVec w)) ∧
    (∀ w env, evalBV w env (buildPartUnity 3 8) = ~~~(0 : BitVec w)) :=
  ⟨reflect_all_bitvec _ .allOnes (mkCartierCert 4 1) (by decide),
   reflect_all_bitvec _ .allOnes (mkCartierCert 4 2) (by decide),
   reflect_all_bitvec _ .allOnes (mkCartierCert 4 3) (by decide)⟩

/-- **THEOREM 4D (Universal Right-Shift Frobenius Truncation Law)**. -/
theorem shr_frob_trunc_all (r s w : Nat) (a : BitVec w) :
    (bvFrob r a) >>> (s * 2 ^ r) =
    bvFrob r (a >>> s) &&& ((~~~(0 : BitVec w)) >>> (s * 2 ^ r)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases hlt : s * 2 ^ r + k < w
  · rw [bvFrob_getLsbD r a (s * 2 ^ r + k) hlt,
        bvFrob_getLsbD r (a >>> s) k hk, sFrob_bit, sFrob_bit]
    have hmask : (~~~(0 : BitVec w)).getLsbD (s * 2 ^ r + k) = true := by simp [hlt]
    rw [hmask, Bool.and_true]
    have hpos : 0 < 2 ^ r := Nat.pow_pos (by omega)
    rw [Nat.add_comm (s * 2 ^ r) k, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hpos]
    split
    · rw [BitVec.getLsbD_ushiftRight, Nat.add_comm]
    · rfl
  · have hge : w ≤ s * 2 ^ r + k := by omega
    rw [BitVec.getLsbD_of_ge _ _ hge, BitVec.getLsbD_of_ge _ _ hge, Bool.and_false]

/-- **THEOREM 4E (Universal Right-Shift / Left-Shift Carryless Truncation Law)**. -/
theorem shr_clmul_shl_all (s w : Nat) (a b : BitVec w) :
    bvClmul (a <<< s) b >>> s = bvClmul a b &&& ((~~~(0 : BitVec w)) >>> s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases hlt : s + k < w
  · rw [bvClmul_getLsbD (a <<< s) b (s + k) hlt, bvClmul_getLsbD a b k hk]
    have hmask : (~~~(0 : BitVec w)).getLsbD (s + k) = true := by simp [hlt]
    rw [hmask, Bool.and_true]
    have hshl : sClmul (fun j => (a <<< s).getLsbD j) (fun j => b.getLsbD j) (s + k) =
        sClmul (sShl (fun j => a.getLsbD j) s) (fun j => b.getLsbD j) (s + k) := by
      simp only [sClmul]
      apply xorSum_congr; intro i hi
      congr 1
      rw [BitVec.getLsbD_shiftLeft]
      simp only [show i < w by omega, decide_true, Bool.true_and, sShl]
      by_cases hsi : s ≤ i
      · simp [hsi, Nat.not_lt.mpr hsi]
      · simp [hsi, Nat.lt_of_not_ge hsi]
    rw [hshl, sClmul_shl_left]
    simp [sShl]
  · have hge : w ≤ s + k := by omega
    rw [BitVec.getLsbD_of_ge _ _ hge, BitVec.getLsbD_of_ge _ _ hge, Bool.and_false]

-- ============================================================================
-- SECTION 6: Kernel-Checked Non-Vacuity Witnesses, Sharpness Counterexamples,
--   Certificate Mutation Rejection Tests, & Axiom Audits
-- ============================================================================

-- 6A. Non-Vacuity Witnesses (Non-Zero BitVec Instances)

example :
    let a : BitVec 8 := 0b10110101#8
    let b : BitVec 8 := 0b01101011#8
    bvPr 1 a &&& bvPr 1 b ≠ 0#8 ∧
    bvPr 1 a &&& bvPr 1 b = bvPr 1 (((a &&& bvPr 1 b) ^^^ (b &&& bvPr 1 a)) ^^^ (a &&& b)) := by
  decide

example :
    let a : BitVec 8 := 0b11010110#8
    let b : BitVec 8 := 0b10101101#8
    bvClmul a b &&& (bvE 8 2 <<< 1) ≠ 0#8 ∧
    bvClmul a b &&& (bvE 8 2 <<< 1) =
    bvXorRange 4 (fun u => bvClmul (a &&& (bvE 8 2 <<< u)) (b &&& (bvE 8 2 <<< ((1 + 4 - u) % 4)))) := by
  decide

example :
    let a : BitVec 8 := 0b10110011#8
    bvPr 1 a &&& bvPr 2 a ≠ 0#8 ∧
    bvPr 1 a &&& bvPr 2 a = bvPr 2 a ^^^ bvPr 1 (a &&& (bvPr 1 a ^^^ bvPr 2 a)) := by
  decide

-- 6B. Kernel-Checked Sharpness Counterexamples

example :
    let a : BitVec 1 := 1#1; let b : BitVec 1 := 1#1
    bvPr 0 a &&& bvPr 0 b ≠ bvPr 0 ((a &&& bvPr 0 b) ^^^ (b &&& bvPr 0 a)) := by decide

example :
    let a : BitVec 3 := 0b010#3; let b : BitVec 3 := 0b001#3
    bvClmul (bvFrob 1 a <<< 0) (b &&& (bvE 3 1 <<< 2)) ≠
    bvClmul (bvFrob 1 a <<< 0) b &&& (bvE 3 1 <<< 2) := by decide

example :
    let a : BitVec 4 := 3#4; let b : BitVec 4 := 3#4
    (a * b) &&& bvE 4 1 ≠
    ((a &&& bvE 4 1) * (b &&& bvE 4 1)) ^^^ ((a &&& (bvE 4 1 <<< 1)) * (b &&& (bvE 4 1 <<< 1))) := by decide

example :
    let a : BitVec 4 := 0b0100#4
    (bvFrob 1 a) >>> 2 ≠ bvFrob 1 (a >>> 1) := by decide

example :
    let a : BitVec 2 := 0b10#2; let b : BitVec 2 := 0b01#2
    bvClmul a b &&& bvE 2 1 ≠ bvClmul a b := by decide

-- 6C. Kernel-Checked Negative / Mutation Rejection Tests (`checkCert bad = false`)

example : isLaneSafe (.clmul (.var 0) (.var 1)) = false := by decide

example : checkCert (resConvLHS 2 1) (resConvRHS 2 1) (mkCartierCert 4 1) = false := by decide

example :
    checkCert
      (.and (Expr.prefixR 1 (.var 0)) (Expr.prefixR 1 (.var 1)))
      (Expr.prefixR 1 (.xor (.xor (.and (.var 0) (Expr.prefixR 1 (.var 1)))
                                  (.and (.var 1) (Expr.prefixR 1 (.var 0))))
                            (.and (.var 0) (.var 1))))
      (.cancelDelta 0 (.normEq 4)) = false := by decide

example :
    checkCert ito2LHS
      (Expr.prefixR 0 (.xor (.and (.var 0) (Expr.prefixR 0 (.var 1)))
                            (.and (.var 1) (Expr.prefixR 0 (.var 0)))))
      (.cancelDelta 0 (.normEq 4)) = false := by decide

example :
    checkCert
      (.clmul (Expr.frob 1 (.var 0)) (.and (.var 1) (.shl (Expr.eMask 1) 2)))
      (.and (.clmul (Expr.frob 1 (.var 0)) (.var 1)) (.shl (Expr.eMask 1) 2))
      (mkCartierCert 4 2) = false := by decide

example :
    checkCert selfLadderLHS selfLadderRHS (.trans (.var 0) (.normEq 4) (.normEq 4)) = false := by decide

example :
    checkCert (.and (Expr.frob 1 (.var 0)) (Expr.frob 1 (.var 1))) .zero (.normEq 4) = false := by decide

example :
    checkCert (resConvLHS 1 0)
      (.clmul (.and (.var 0) (Expr.eMask 1)) (.and (.var 1) (Expr.eMask 1)))
      (mkCartierCert 4 1) = false := by decide

example : checkCert ito2LHS ito2RHS (.cancelDelta 0 (.normEq 0)) = false := by decide


-- ============================================================================
-- 6D. Axiom Verification Audit (Must Show Only Standard Lean Axioms!)
-- ============================================================================

end CHReflect
