/-!
# Carry-Coupled Binary Automaton Correlation & Dual-Krylov L^4-Energy Proof Engine

Standalone Lean 4.36.0 formalization (zero Mathlib, zero `sorry`, zero `native_decide`,
zero floating-point).

## Contents
1. **Reusable Engine Core (`BinAuto d` & Universal Carry-Coupled Subdivision):**
   - Any signed/weighted LSB-first binary automaton `A : BinAuto d` with decidable finite
     zero-invariance `∀ q, init q = sig0 q * init (del0 q)`.
   - Universal bit-split laws (`eval_even`, `eval_odd`) for all `n : Nat`.
   - Exact carry-coupled aperiodic shift-correlation subdivision (`apCorr_even`, `apCorr_odd`)
     holding for all `d`, all `A : BinAuto d`, all `p q : Fin d`, and all `k t : Nat`.

2. **Reusable Mechanism A (Finite Left-Annihilator Compiler & Universal Bijective-Tail Family):**
   - General finite-to-infinite annihilator soundness theorem (`annihilator_sound`).
   - Exact pure-integer polynomial flatness & partial-sum Pythagorean theorem (`poly_flat_of_diag_zero`).
   - **Theorem 1 (Universal Parameterized Nonlinear Family, ∀ m : Nat, ∀ ψ : Fin (2^m) → Bool):**
     Exact IFF characterization of the 1-step De Bruijn trace annihilator (`debruijn_trace_annihilator_iff`),
     proving exact zero total autocorrelation, exact polynomial flatness, and exact partial-sum
     Pythagorean laws across all `2^(2^m)` arbitrarily high-degree nonlinear Boolean feedback functions.
   - **Concrete Cubic Witness (`m = 2, L = 4`):** Kernel-checked equivalence ∀ `n : Nat` between
     `eval (bijTailAuto 2 psiCubic) 0 n` and `(-1)^popcount(n & (((n <<< 1) & (n <<< 2)) ^^^ (n <<< 3)))`,
     plus kernel-checked sharpness counterexample (`broken111Auto`, giving `4 ≠ 0` at `k = 1, s = 1`).

3. **Reusable Mechanism B (Exact Finite-Dimensional QRZ & Dual-Krylov L^4-Energy Proof Compiler):**
   - Universal finite-dimensional closure of the infinite-shift quadratic autocorrelation tensors
     `(Q(k), R(k), Z(k))` under the sparse `O(D^2)` operator `primalStep` (`qrz_step`).
   - Sparse `O(D^2)` exact adjoint `dualStep` with kernel-proved adjointness (`innerQRZ_dualStep`).
   - Pure-data certificate checker `checkDualCert` and universal soundness theorem (`dual_krylov_sound`).
   - **Theorem 2 (Regular Paperfolding Exact L^4 Closed Form & 2-Adic Divisibility):**
     `∀ k ≥ 2, 21 * E4_PF(k) = 2 * 8^k + (63*k^2 - 693*k + 2317) * 2^k - 4440`,
     `∀ k ≥ 3, 8 ∣ E4_PF(k)`, with kernel-checked sharpness failures at `k = 0, 1` and `k = 2`.
   - **Theorem 3 (Baum-Sweet Exact Degree-5 L^4 Recurrence & Period-3 Parity Law):**
     `∀ k, E4_BS(k+5) = 2*E4_BS(k+4) + 6*E4_BS(k+3) - E4_BS(k+2) - 4*E4_BS(k+1) + 2*E4_BS(k)`,
     `∀ k, E4_BS(k) % 2 = 0 ↔ k % 3 = 1`, plus direct equivalence to the standard Baum-Sweet recurrence.
   - **Theorem 4 (L = 3 Complementary Parity Quadruplets `101 ^ 110` & `100 ^ 111`):**
     Exact sparse recurrence `T(k+5) = 2*T(k+4) + 16*T(k+2) + 256*T(k)`,
     exact 4-power conservation law `T(k+4) + 2*T(k+3) + 8*T(k+2) + 16*T(k+1) + 64*T(k) = 4^(k+6)`,
     exact 2-adic valuation `2^(k+2) ∣ T(k) ∧ ¬(2^(k+3) ∣ T(k))`,
     and non-trivial total-energy isospectrality `∀ k, T_6(k) = T_9(k)` paired with
     individual-state divergence `E4_6(0, 4) = 464 ≠ 528 = E4_9(0, 4)`.
   - **Benchmark Corollary (Rudin-Shapiro):** Exact Littlewood formula `∀ k ≥ 1, 3 * E4_RS(k) = 4^(k+1) - (-2)^k`.
   - **Kernel-Checked Mutation Tests:** Mutated Dual-Krylov certificates are rejected (`checkDualCert = false`).
-/

namespace PureSiliconAuto

-- ============================================================================
-- Section 0: Core Summation & Arithmetic Helpers (Pure Core Lean 4.36.0)
-- ============================================================================

/-- Sum of `f 0 + f 1 + ... + f (n - 1)`. -/
def sumRange (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | n + 1 => sumRange n f + f n

theorem sumRange_zero (f : Nat → Int) : sumRange 0 f = 0 := rfl

theorem sumRange_succ (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = sumRange n f + f n := rfl

theorem sumRange_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.add_mul]

theorem sumRange_zero_fn (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, ih]

theorem sumRange_succ_left (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = f 0 + sumRange n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ (n + 1) f, ih, sumRange_succ n (fun i => f (i + 1))]
    omega

theorem sumRange_even_odd (n : Nat) (f : Nat → Int) :
    sumRange (2 * n) f = sumRange n (fun i => f (2 * i)) + sumRange n (fun i => f (2 * i + 1)) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h1, sumRange, sumRange, ih, sumRange, sumRange]
    omega

theorem sumRange_even_odd_succ (n : Nat) (f : Nat → Int) :
    sumRange (2 * n + 1) f =
      sumRange (n + 1) (fun i => f (2 * i)) + sumRange n (fun i => f (2 * i + 1)) := by
  rw [sumRange, sumRange_even_odd, sumRange]
  omega

theorem sumRange_swap (m n : Nat) (f : Nat → Nat → Int) :
    sumRange m (fun i => sumRange n (fun j => f i j)) =
      sumRange n (fun j => sumRange m (fun i => f i j)) := by
  induction m with
  | zero => simp [sumRange, sumRange_zero_fn]
  | succ m ih =>
    simp only [sumRange, ih, sumRange_add]

/-- Sum over `Fin d`. -/
def sumFin (d : Nat) (f : Fin d → Int) : Int :=
  sumRange d (fun i => if h : i < d then f ⟨i, h⟩ else 0)

theorem sumFin_congr {d : Nat} {f g : Fin d → Int} (h : ∀ i, f i = g i) :
    sumFin d f = sumFin d g := by
  apply sumRange_congr
  intro i hi
  simp [hi, h ⟨i, hi⟩]

theorem sumFin_add (d : Nat) (f g : Fin d → Int) :
    sumFin d (fun i => f i + g i) = sumFin d f + sumFin d g := by
  unfold sumFin
  rw [← sumRange_add]
  apply sumRange_congr
  intro i hi
  simp [hi]

theorem sumFin_sub (d : Nat) (f g : Fin d → Int) :
    sumFin d (fun i => f i - g i) = sumFin d f - sumFin d g := by
  unfold sumFin
  rw [← sumRange_sub]
  apply sumRange_congr
  intro i hi
  simp [hi]

theorem sumFin_mul_left (d : Nat) (c : Int) (f : Fin d → Int) :
    sumFin d (fun i => c * f i) = c * sumFin d f := by
  unfold sumFin
  rw [← sumRange_mul_left]
  apply sumRange_congr
  intro i hi
  simp [hi]

theorem sumFin_mul_right (d : Nat) (c : Int) (f : Fin d → Int) :
    sumFin d (fun i => f i * c) = sumFin d f * c := by
  unfold sumFin
  rw [← sumRange_mul_right]
  apply sumRange_congr
  intro i hi
  simp [hi]

theorem sumFin_zero (d : Nat) : sumFin d (fun _ => 0) = 0 := by
  unfold sumFin
  calc sumRange d (fun i => if _ : i < d then (0 : Int) else 0)
      = sumRange d (fun _ => 0) := by apply sumRange_congr; intro i hi; simp [hi]
    _ = 0 := sumRange_zero_fn d

theorem sumFin_swap (m n : Nat) (f : Fin m → Fin n → Int) :
    sumFin m (fun i => sumFin n (fun j => f i j)) =
      sumFin n (fun j => sumFin m (fun i => f i j)) := by
  unfold sumFin
  calc sumRange m (fun i => if hi : i < m then sumRange n (fun j => if hj : j < n then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0)
      = sumRange m (fun i => sumRange n (fun j =>
          if hi : i < m then (if hj : j < n then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0)) := by
        apply sumRange_congr; intro i hi; simp [hi]
    _ = sumRange n (fun j => sumRange m (fun i =>
          if hi : i < m then (if hj : j < n then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0)) :=
        sumRange_swap m n _
    _ = sumRange n (fun j => if hj : j < n then sumRange m (fun i => if hi : i < m then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0) := by
        apply sumRange_congr; intro j hj; simp [hj]

theorem sumFin_ite_eq {d : Nat} (a : Fin d) (f : Fin d → Int) :
    sumFin d (fun i => if a = i then f i else 0) = f a := by
  unfold sumFin
  have helper : ∀ k (_hk : k ≤ d),
      sumRange k (fun i => if h : i < d then (if a = ⟨i, h⟩ then f ⟨i, h⟩ else 0) else 0) =
      if a.1 < k then f a else 0 := by
    intro k hk
    induction k with
    | zero => simp [sumRange]
    | succ k ih =>
      rw [sumRange, ih (by omega)]
      have hkd : k < d := by omega
      simp only [hkd, ↓reduceDIte]
      by_cases hlt : a.1 < k
      · have hne : a ≠ ⟨k, hkd⟩ := by
          intro heq
          have hv : a.1 = k := congrArg Fin.val heq
          omega
        have hlt' : a.1 < k + 1 := by omega
        simp [hlt, hlt', hne]
      · by_cases heq : a.1 = k
        · have ha : a = ⟨k, hkd⟩ := Fin.ext heq
          rw [ha]
          simp [Nat.lt_irrefl]
        · have hne : a ≠ ⟨k, hkd⟩ := by intro h; apply heq; exact congrArg Fin.val h
          have hlt' : ¬(a.1 < k + 1) := by omega
          simp [hlt, hlt', hne]
  rw [helper d (Nat.le_refl d)]
  simp [a.2]

theorem sumFin_ite_eq' {d : Nat} (a : Fin d) (f : Fin d → Int) :
    sumFin d (fun i => if i = a then f i else 0) = f a := by
  have h : (fun i : Fin d => if i = a then f i else 0) = (fun i => if a = i then f i else 0) := by
    funext i
    by_cases he : i = a
    · subst he; simp
    · have he' : a ≠ i := Ne.symm he; simp [he, he']
  rw [h, sumFin_ite_eq]

/-- Pair indexing `Fin d × Fin d ≃ Fin (d * d)`. -/
def pairIdx {d : Nat} (p q : Fin d) : Fin (d * d) :=
  ⟨p.1 * d + q.1, by
    have hp : p.1 + 1 ≤ d := p.2
    have hq : q.1 < d := q.2
    calc p.1 * d + q.1 < p.1 * d + d := Nat.add_lt_add_left hq _
    _ = (p.1 + 1) * d := by rw [Nat.succ_mul]
    _ ≤ d * d := Nat.mul_le_mul_right d hp⟩

theorem sumFin_mul_split (d : Nat) (f : Fin (d * d) → Int) :
    sumFin (d * d) f = sumFin d (fun p => sumFin d (fun q => f (pairIdx p q))) := by
  have hgen : ∀ m (_hm : m ≤ d),
      sumRange (m * d) (fun i => if h : i < d * d then f ⟨i, h⟩ else 0) =
      sumRange m (fun p => if hp : p < d then
        sumRange d (fun q => if hq : q < d then f (pairIdx ⟨p, hp⟩ ⟨q, hq⟩) else 0) else 0) := by
    intro m hm
    induction m with
    | zero => simp [sumRange]
    | succ m ih =>
      rw [sumRange, ← ih (by omega)]
      have hmd : m < d := by omega
      simp only [hmd, ↓reduceDIte]
      have hstep : ∀ q (_hq : q ≤ d),
          sumRange (m * d + q) (fun i => if h : i < d * d then f ⟨i, h⟩ else 0) =
          sumRange (m * d) (fun i => if h : i < d * d then f ⟨i, h⟩ else 0) +
          sumRange q (fun j => if hj : j < d then f (pairIdx ⟨m, hmd⟩ ⟨j, hj⟩) else 0) := by
        intro q hq
        induction q with
        | zero => simp [sumRange]
        | succ q ihq =>
          have h1 : m * d + (q + 1) = (m * d + q) + 1 := by omega
          rw [h1, sumRange, ihq (by omega), sumRange]
          have hqd : q < d := by omega
          have hlt : m * d + q < d * d := (pairIdx ⟨m, hmd⟩ ⟨q, hqd⟩).2
          simp only [hlt, hqd, ↓reduceDIte]
          have : (⟨m * d + q, hlt⟩ : Fin (d * d)) = pairIdx ⟨m, hmd⟩ ⟨q, hqd⟩ := rfl
          rw [this]
          omega
      have hmd_eq : (m + 1) * d = m * d + d := by rw [Nat.succ_mul]
      rw [hmd_eq, hstep d (Nat.le_refl d)]
  exact hgen d (Nat.le_refl d)

theorem pow2_succ (m : Nat) : 2 ^ (m + 1) = 2 * 2 ^ m := by
  rw [Nat.pow_succ]; omega

-- ============================================================================
-- Section 1: Core Engine — `BinAuto d` & Universal Carry-Coupled Subdivision
-- ============================================================================

/-- A signed/weighted LSB-first finite-state binary automaton on `d` states.
    The single finite compatibility law `zero_ok` guarantees leading-zero invariance
    and exact bit-splitting across all `n : Nat` (including `n = 0`). -/
structure BinAuto (d : Nat) where
  del0 : Fin d → Fin d
  del1 : Fin d → Fin d
  sig0 : Fin d → Int
  sig1 : Fin d → Int
  init : Fin d → Int
  zero_ok : ∀ q : Fin d, init q = sig0 q * init (del0 q)

/-- Exact LSB-first evaluation of state `q` on `n : Nat`. -/
def BinAuto.eval {d : Nat} (A : BinAuto d) (q : Fin d) (n : Nat) : Int :=
  if _h : n = 0 then A.init q
  else if n % 2 = 0 then A.sig0 q * A.eval (A.del0 q) (n / 2)
  else A.sig1 q * A.eval (A.del1 q) (n / 2)
termination_by n
decreasing_by
  all_goals omega

theorem BinAuto.eval_zero {d : Nat} (A : BinAuto d) (q : Fin d) :
    A.eval q 0 = A.init q := by
  rw [BinAuto.eval]; simp

theorem BinAuto.eval_even {d : Nat} (A : BinAuto d) (q : Fin d) (n : Nat) :
    A.eval q (2 * n) = A.sig0 q * A.eval (A.del0 q) n := by
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.mul_zero, BinAuto.eval_zero]
    exact A.zero_ok q
  · rw [BinAuto.eval]
    have h1 : 2 * n ≠ 0 := by omega
    have h2 : (2 * n) % 2 = 0 := by omega
    have h3 : (2 * n) / 2 = n := by omega
    simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte]

theorem BinAuto.eval_odd {d : Nat} (A : BinAuto d) (q : Fin d) (n : Nat) :
    A.eval q (2 * n + 1) = A.sig1 q * A.eval (A.del1 q) n := by
  rw [BinAuto.eval]
  have h1 : 2 * n + 1 ≠ 0 := by omega
  have h2 : (2 * n + 1) % 2 ≠ 0 := by omega
  have h3 : (2 * n + 1) / 2 = n := by omega
  simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte]

/-- Exact aperiodic shift-correlation over `[0, 2^k)`:
    `apCorr A p q k s = ∑_{n = 0}^{2^k - s - 1} f_p(n) * f_q(n + s)` (and `0` for `s ≥ 2^k`). -/
def apCorr {d : Nat} (A : BinAuto d) (p q : Fin d) (k s : Nat) : Int :=
  sumRange (2 ^ k - s) (fun n => A.eval p n * A.eval q (n + s))

theorem apCorr_ge {d : Nat} (A : BinAuto d) (p q : Fin d) (k s : Nat) (h : 2 ^ k ≤ s) :
    apCorr A p q k s = 0 := by
  unfold apCorr
  have h0 : 2 ^ k - s = 0 := by omega
  rw [h0, sumRange_zero]

theorem apCorr_zero_zero {d : Nat} (A : BinAuto d) (p q : Fin d) :
    apCorr A p q 0 0 = A.init p * A.init q := by
  simp [apCorr, sumRange, BinAuto.eval_zero]

theorem apCorr_zero_succ {d : Nat} (A : BinAuto d) (p q : Fin d) (s : Nat) :
    apCorr A p q 0 (s + 1) = 0 := by
  apply apCorr_ge; simp

theorem mul_four (a b c e : Int) : (a * c) * (b * e) = a * b * (c * e) := by
  calc (a * c) * (b * e) = a * (c * (b * e)) := Int.mul_assoc _ _ _
    _ = a * (b * (c * e)) := by rw [← Int.mul_assoc c b e, Int.mul_comm c b, Int.mul_assoc]
    _ = a * b * (c * e) := (Int.mul_assoc _ _ _).symm

/-- **THEOREM 1b (Universal Odd-Shift Carry-Coupled Subdivision Law):**
    Exact bit-pair carry into `t + 1` at odd shift `s = 2t + 1` for every `BinAuto d`,
    automatically aligned with the aperiodic boundary `2^(k+1) - (2t+1)`. -/
theorem apCorr_odd {d : Nat} (A : BinAuto d) (p q : Fin d) (k t : Nat) :
    apCorr A p q (k + 1) (2 * t + 1) =
      A.sig0 p * A.sig1 q * apCorr A (A.del0 p) (A.del1 q) k t +
      A.sig1 p * A.sig0 q * apCorr A (A.del1 p) (A.del0 q) k (t + 1) := by
  unfold apCorr
  by_cases hlt : t < 2 ^ k
  · have hlen : 2 ^ (k + 1) - (2 * t + 1) = 2 * (2 ^ k - (t + 1)) + 1 := by
      rw [Nat.pow_succ]; omega
    have hlen2 : (2 ^ k - (t + 1)) + 1 = 2 ^ k - t := by omega
    rw [hlen, sumRange_even_odd_succ, hlen2]
    have he : sumRange (2 ^ k - t) (fun n => A.eval p (2 * n) * A.eval q (2 * n + (2 * t + 1))) =
        A.sig0 p * A.sig1 q * sumRange (2 ^ k - t) (fun n => A.eval (A.del0 p) n * A.eval (A.del1 q) (n + t)) := by
      rw [← sumRange_mul_left]
      apply sumRange_congr; intro n _
      have hadd : 2 * n + (2 * t + 1) = 2 * (n + t) + 1 := by omega
      rw [hadd, BinAuto.eval_even, BinAuto.eval_odd, mul_four]
    have ho : sumRange (2 ^ k - (t + 1)) (fun n => A.eval p (2 * n + 1) * A.eval q (2 * n + 1 + (2 * t + 1))) =
        A.sig1 p * A.sig0 q * sumRange (2 ^ k - (t + 1)) (fun n => A.eval (A.del1 p) n * A.eval (A.del0 q) (n + (t + 1))) := by
      rw [← sumRange_mul_left]
      apply sumRange_congr; intro n _
      have hadd : 2 * n + 1 + (2 * t + 1) = 2 * (n + (t + 1)) := by omega
      rw [hadd, BinAuto.eval_odd, BinAuto.eval_even, mul_four]
    rw [he, ho]
  · have h1 : 2 ^ (k + 1) - (2 * t + 1) = 0 := by rw [Nat.pow_succ]; omega
    have h2 : 2 ^ k - t = 0 := by omega
    have h3 : 2 ^ k - (t + 1) = 0 := by omega
    simp [h1, h2, h3, sumRange]

-- ============================================================================
-- Section 2: Mechanism A — Finite Left-Annihilator Compiler & Bijective-Tail Family
-- ============================================================================

/-- Weighted correlation functional `∑_{p, q} w p q * apCorr A p q k s`. -/
def weightedCorr {d : Nat} (A : BinAuto d) (w : Fin d → Fin d → Int) (k s : Nat) : Int :=
  sumFin d (fun p => sumFin d (fun q => w p q * apCorr A p q k s))

/-- Finite left-action of `E = T00 + T11`, `O0 = T01`, `O1 = T10` on a weight table `w`. -/
def leftActE {d : Nat} (A : BinAuto d) (w : Fin d → Fin d → Int) (p' q' : Fin d) : Int :=
  sumFin d (fun p => sumFin d (fun q =>
    w p q * ((if A.del0 p = p' ∧ A.del0 q = q' then A.sig0 p * A.sig0 q else 0) +
             (if A.del1 p = p' ∧ A.del1 q = q' then A.sig1 p * A.sig1 q else 0))))

def leftActO0 {d : Nat} (A : BinAuto d) (w : Fin d → Fin d → Int) (p' q' : Fin d) : Int :=
  sumFin d (fun p => sumFin d (fun q =>
    w p q * (if A.del0 p = p' ∧ A.del1 q = q' then A.sig0 p * A.sig1 q else 0)))

def leftActO1 {d : Nat} (A : BinAuto d) (w : Fin d → Fin d → Int) (p' q' : Fin d) : Int :=
  sumFin d (fun p => sumFin d (fun q =>
    w p q * (if A.del1 p = p' ∧ A.del0 q = q' then A.sig1 p * A.sig0 q else 0)))

theorem sumFin4_swap (d : Nat) (F : Fin d → Fin d → Fin d → Fin d → Int) :
    sumFin d (fun p => sumFin d (fun q => sumFin d (fun p' => sumFin d (fun q' => F p q p' q')))) =
    sumFin d (fun p' => sumFin d (fun q' => sumFin d (fun p => sumFin d (fun q => F p q p' q')))) := by
  calc sumFin d (fun p => sumFin d (fun q => sumFin d (fun p' => sumFin d (fun q' => F p q p' q'))))
      = sumFin d (fun p => sumFin d (fun p' => sumFin d (fun q => sumFin d (fun q' => F p q p' q')))) := by
        apply sumFin_congr; intro p; exact sumFin_swap d d _
    _ = sumFin d (fun p' => sumFin d (fun p => sumFin d (fun q => sumFin d (fun q' => F p q p' q')))) :=
        sumFin_swap d d _
    _ = sumFin d (fun p' => sumFin d (fun p => sumFin d (fun q' => sumFin d (fun q => F p q p' q')))) := by
        apply sumFin_congr; intro p'; apply sumFin_congr; intro p; exact sumFin_swap d d _
    _ = sumFin d (fun p' => sumFin d (fun q' => sumFin d (fun p => sumFin d (fun q => F p q p' q')))) := by
        apply sumFin_congr; intro p'; exact sumFin_swap d d _

theorem pull_to_push_pair {d : Nat} (f g : Fin d → Fin d) (c : Fin d → Fin d → Int)
    (w : Fin d → Fin d → Int) (X : Fin d → Fin d → Int) :
    sumFin d (fun p => sumFin d (fun q => w p q * (c p q * X (f p) (g q)))) =
    sumFin d (fun p' => sumFin d (fun q' =>
      (sumFin d (fun p => sumFin d (fun q =>
        w p q * (if f p = p' ∧ g q = q' then c p q else 0)))) * X p' q')) := by
  have hinner : ∀ p q : Fin d,
      w p q * (c p q * X (f p) (g q)) =
      sumFin d (fun p' => sumFin d (fun q' =>
        w p q * (if f p = p' ∧ g q = q' then c p q else 0) * X p' q')) := by
    intro p q
    have hq : ∀ p' : Fin d,
        sumFin d (fun q' => w p q * (if f p = p' ∧ g q = q' then c p q else 0) * X p' q') =
        if f p = p' then w p q * c p q * X p' (g q) else 0 := by
      intro p'
      by_cases hp : f p = p'
      · simp only [hp, true_and, ↓reduceIte]
        have hstep : (fun q' : Fin d => w p q * (if g q = q' then c p q else 0) * X p' q') =
            (fun q' => if g q = q' then w p q * c p q * X p' q' else 0) := by
          funext q'; by_cases h : g q = q' <;> simp [h]
        rw [hstep, sumFin_ite_eq]
      · simp only [hp, false_and, ↓reduceIte, Int.mul_zero, Int.zero_mul, sumFin_zero]
    simp only [hq]
    rw [sumFin_ite_eq, Int.mul_assoc]
  calc sumFin d (fun p => sumFin d (fun q => w p q * (c p q * X (f p) (g q))))
      = sumFin d (fun p => sumFin d (fun q =>
          sumFin d (fun p' => sumFin d (fun q' =>
            w p q * (if f p = p' ∧ g q = q' then c p q else 0) * X p' q')))) := by
        apply sumFin_congr; intro p; apply sumFin_congr; intro q; exact hinner p q
    _ = sumFin d (fun p' => sumFin d (fun q' =>
          sumFin d (fun p => sumFin d (fun q =>
            w p q * (if f p = p' ∧ g q = q' then c p q else 0) * X p' q')))) :=
        sumFin4_swap d _
    _ = sumFin d (fun p' => sumFin d (fun q' =>
          (sumFin d (fun p => sumFin d (fun q =>
            w p q * (if f p = p' ∧ g q = q' then c p q else 0)))) * X p' q')) := by
        apply sumFin_congr; intro p'; apply sumFin_congr; intro q'
        rw [← sumFin_mul_right]
        apply sumFin_congr; intro p
        rw [← sumFin_mul_right]

/-- Automaton polynomial `P_{q, k}(X) = ∑_{n=0}^{2^k - 1} f_q(n) X^n`. -/
def polyEval {d : Nat} (A : BinAuto d) (q : Fin d) (k : Nat) (X : Int) : Int :=
  sumRange (2 ^ k) (fun n => A.eval q n * X ^ n)

/-- Reversed polynomial `P^{rev}_{q, k}(X) = ∑_{m=0}^{2^k - 1} f_q(m) X^{2^k - 1 - m}`. -/
def polyRevEval {d : Nat} (A : BinAuto d) (q : Fin d) (k : Nat) (X : Int) : Int :=
  sumRange (2 ^ k) (fun m => A.eval q m * X ^ (2 ^ k - 1 - m))

theorem sumRange_reverse (k : Nat) (g : Nat → Int) :
    sumRange k g = sumRange k (fun r => g (k - 1 - r)) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ihk =>
    rw [sumRange_succ_left, sumRange]
    have h0 : k + 1 - 1 - k = 0 := by omega
    rw [h0, Int.add_comm]
    congr 1
    rw [ihk (fun i => g (i + 1))]
    apply sumRange_congr
    intro r hr
    congr 1; omega

/-- Pure-integer Cauchy-product diagonal decomposition for ANY sequence `f : Nat → Int`. -/
theorem poly_prod_decomp (N : Nat) (hN : N ≥ 1) (f : Nat → Int) (X : Int) :
    (sumRange N (fun n => f n * X ^ n)) * (sumRange N (fun m => f m * X ^ (N - 1 - m))) =
    (sumRange N (fun n => f n * f n)) * X ^ (N - 1) +
    sumRange (N - 1) (fun r =>
      (sumRange (N - (r + 1)) (fun n => f n * f (n + (r + 1)))) *
        (X ^ (N - 1 - (r + 1)) + X ^ (N - 1 + (r + 1)))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  clear hN
  induction M with
  | zero => simp [sumRange]
  | succ M ih =>
    have hsplit_rev : ∀ k (_hk : k ≤ M + 1),
        sumRange k (fun m => f m * X ^ (M + 1 - m)) =
        X * sumRange k (fun m => f m * X ^ (M - m)) := by
      intro k hk
      induction k with
      | zero => simp [sumRange]
      | succ k ihk =>
        simp only [sumRange, ihk (by omega), Int.mul_add]
        congr 1
        have he : M + 1 - k = (M - k) + 1 := by omega
        rw [he, Int.pow_succ, Int.mul_comm (X ^ (M - k)) X, ← Int.mul_assoc, Int.mul_comm (f k) X, Int.mul_assoc]
    have hsub1 : M + 1 + 1 - 1 = M + 1 := by omega
    rw [hsub1]
    have hP : sumRange (M + 2) (fun n => f n * X ^ n) =
        sumRange (M + 1) (fun n => f n * X ^ n) + f (M + 1) * X ^ (M + 1) := rfl
    have hR : sumRange (M + 2) (fun m => f m * X ^ (M + 1 - m)) =
        X * sumRange (M + 1) (fun m => f m * X ^ (M - m)) + f (M + 1) := by
      rw [sumRange, hsplit_rev (M + 1) (Nat.le_refl _)]
      have h0 : M + 1 - (M + 1) = 0 := by omega
      rw [h0]
      simp
    rw [hP, hR]
    let A := sumRange (M + 1) (fun n => f n * X ^ n)
    let B := sumRange (M + 1) (fun m => f m * X ^ (M - m))
    have hexpand :
        (A + f (M + 1) * X ^ (M + 1)) * (X * B + f (M + 1)) =
        X * (A * B) + f (M + 1) * f (M + 1) * X ^ (M + 1) +
        (f (M + 1) * A + f (M + 1) * X ^ (M + 1) * (X * B)) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have h1 : A * (X * B) = X * (A * B) := by
        rw [← Int.mul_assoc, Int.mul_comm A X, Int.mul_assoc]
      have h2 : f (M + 1) * X ^ (M + 1) * f (M + 1) = f (M + 1) * f (M + 1) * X ^ (M + 1) := by
        rw [Int.mul_assoc, Int.mul_comm (X ^ (M + 1)) (f (M + 1)), ← Int.mul_assoc]
      have h3 : A * f (M + 1) = f (M + 1) * A := Int.mul_comm _ _
      omega
    change (A + f (M + 1) * X ^ (M + 1)) * (X * B + f (M + 1)) = _
    rw [hexpand]
    have hAB : A * B =
        sumRange (M + 1) (fun n => f n * f n) * X ^ M +
        sumRange M (fun r =>
          sumRange (M + 1 - (r + 1)) (fun n => f n * f (n + (r + 1))) *
            (X ^ (M - (r + 1)) + X ^ (M + (r + 1)))) := by
      simpa [A, B] using ih
    rw [hAB, Int.mul_add]
    have hdiag :
        X * (sumRange (M + 1) (fun n => f n * f n) * X ^ M) +
          f (M + 1) * f (M + 1) * X ^ (M + 1) =
        sumRange (M + 2) (fun n => f n * f n) * X ^ (M + 1) := by
      rw [sumRange_succ (M + 1), Int.add_mul]
      congr 1
      rw [Int.pow_succ, ← Int.mul_assoc, Int.mul_comm X, Int.mul_assoc, Int.mul_comm X (X ^ M)]
    have hA_rev : f (M + 1) * A =
        sumRange (M + 1) (fun r => f (M - r) * f (M + 1) * X ^ (M - r)) := by
      dsimp only [A]
      rw [sumRange_reverse (M + 1), ← sumRange_mul_left]
      apply sumRange_congr; intro r _
      have hmr : M + 1 - 1 - r = M - r := by omega
      rw [hmr, ← Int.mul_assoc, Int.mul_comm (f (M + 1)) (f (M - r))]
    have hB_rev : f (M + 1) * X ^ (M + 1) * (X * B) =
        sumRange (M + 1) (fun r => f (M - r) * f (M + 1) * X ^ (M + 1 + (r + 1))) := by
      dsimp only [B]
      rw [sumRange_reverse (M + 1), ← sumRange_mul_left, ← sumRange_mul_left]
      apply sumRange_congr; intro r hr
      have hmr : M + 1 - 1 - r = M - r := by omega
      have hsub : M - (M - r) = r := by omega
      rw [hmr, hsub]
      have hpow : X ^ (M + 1) * (X * X ^ r) = X ^ (M + 1 + (r + 1)) := by
        rw [Int.pow_add X (M + 1) (r + 1), Int.pow_succ X r, Int.mul_comm (X ^ r) X]
      rw [← Int.mul_assoc X (f (M - r)), Int.mul_comm X (f (M - r)), Int.mul_assoc (f (M - r)),
          Int.mul_assoc (f (M + 1)), ← Int.mul_assoc (X ^ (M + 1)) (f (M - r)),
          Int.mul_comm (X ^ (M + 1)) (f (M - r)), Int.mul_assoc (f (M - r)),
          ← Int.mul_assoc (f (M + 1)) (f (M - r)), Int.mul_comm (f (M + 1)) (f (M - r)), hpow]
    have hoff :
        X * sumRange M (fun r =>
          sumRange (M + 1 - (r + 1)) (fun n => f n * f (n + (r + 1))) *
            (X ^ (M - (r + 1)) + X ^ (M + (r + 1)))) +
        (f (M + 1) * A + f (M + 1) * X ^ (M + 1) * (X * B)) =
        sumRange (M + 1) (fun r =>
          sumRange (M + 2 - (r + 1)) (fun n => f n * f (n + (r + 1))) *
            (X ^ (M + 1 - (r + 1)) + X ^ (M + 1 + (r + 1)))) := by
      rw [hA_rev, hB_rev, ← sumRange_add, sumRange_succ M (fun r => _ + _),
          sumRange_succ M (fun r => sumRange (M + 2 - (r + 1)) _ * _)]
      have hlast :
          f (M - M) * f (M + 1) * X ^ (M - M) + f (M - M) * f (M + 1) * X ^ (M + 1 + (M + 1)) =
          sumRange (M + 2 - (M + 1)) (fun n => f n * f (n + (M + 1))) *
            (X ^ (M + 1 - (M + 1)) + X ^ (M + 1 + (M + 1))) := by
        have h1 : M - M = 0 := by omega
        have h2 : M + 2 - (M + 1) = 1 := by omega
        have h3 : M + 1 - (M + 1) = 0 := by omega
        rw [h1, h2, h3, sumRange, sumRange, Int.zero_add, Nat.zero_add, Int.mul_add]
      have hbody :
          X * sumRange M (fun r =>
            sumRange (M + 1 - (r + 1)) (fun n => f n * f (n + (r + 1))) *
              (X ^ (M - (r + 1)) + X ^ (M + (r + 1)))) +
          sumRange M (fun r =>
            f (M - r) * f (M + 1) * X ^ (M - r) +
              f (M - r) * f (M + 1) * X ^ (M + 1 + (r + 1))) =
          sumRange M (fun r =>
            sumRange (M + 2 - (r + 1)) (fun n => f n * f (n + (r + 1))) *
              (X ^ (M + 1 - (r + 1)) + X ^ (M + 1 + (r + 1)))) := by
        rw [← sumRange_mul_left, ← sumRange_add]
        apply sumRange_congr; intro r hr
        have hlen : M + 2 - (r + 1) = (M + 1 - (r + 1)) + 1 := by omega
        have hidx : M + 1 - (r + 1) = M - r := by omega
        have hidx2 : M - r + (r + 1) = M + 1 := by omega
        have hp1 : X * X ^ (M - (r + 1)) = X ^ (M + 1 - (r + 1)) := by
          have : M + 1 - (r + 1) = (M - (r + 1)) + 1 := by omega
          rw [this, Int.pow_succ, Int.mul_comm]
        have hp2 : X * X ^ (M + (r + 1)) = X ^ (M + 1 + (r + 1)) := by
          have : M + 1 + (r + 1) = (M + (r + 1)) + 1 := by omega
          rw [this, Int.pow_succ, Int.mul_comm]
        rw [hlen, sumRange, hidx, hidx2, Int.add_mul, Int.mul_add (f (M - r) * f (M + 1))]
        congr 1
        · rw [Int.mul_comm X, Int.mul_assoc, Int.add_mul,
              Int.mul_comm (X ^ (M - (r + 1))) X, Int.mul_comm (X ^ (M + (r + 1))) X,
              hp1, hp2, hidx, Int.mul_add]
      omega
    have hm2 : M + 1 + 1 = M + 2 := rfl
    rw [hm2]
    omega

/-- **THEOREM 1c (Pure-Silicon Polynomial Flatness & Partial-Sum Pythagorean Lifter):**
    If a diagonal linear combination `∑_q c_q * apCorr A q q k s = 0` for all `s ≥ 1`,
    then for EVERY `X : Int`:
    `∑_q c_q * P_{q, k}(X) * P^{rev}_{q, k}(X) = (∑_q c_q * apCorr A q q k 0) * X^(2^k - 1)`. -/
theorem poly_flat_of_diag_zero {d : Nat} (A : BinAuto d) (c : Fin d → Int) (k : Nat)
    (hzero : ∀ s, s ≥ 1 → sumFin d (fun q => c q * apCorr A q q k s) = 0) (X : Int) :
    sumFin d (fun q => c q * (polyEval A q k X * polyRevEval A q k X)) =
      sumFin d (fun q => c q * apCorr A q q k 0) * X ^ (2 ^ k - 1) := by
  have hpos : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have h1 : sumFin d (fun q => c q * (polyEval A q k X * polyRevEval A q k X)) =
      sumFin d (fun q => c q * (apCorr A q q k 0 * X ^ (2 ^ k - 1))) +
      sumFin d (fun q => c q * sumRange (2 ^ k - 1) (fun r =>
        apCorr A q q k (r + 1) * (X ^ (2 ^ k - 1 - (r + 1)) + X ^ (2 ^ k - 1 + (r + 1))))) := by
    rw [← sumFin_add]
    apply sumFin_congr; intro q
    rw [← Int.mul_add]
    congr 1
    unfold polyEval polyRevEval apCorr
    simpa [Nat.sub_zero, Nat.add_zero] using poly_prod_decomp (2 ^ k) hpos (A.eval q) X
  rw [h1]
  have hoff : sumFin d (fun q => c q * sumRange (2 ^ k - 1) (fun r =>
      apCorr A q q k (r + 1) * (X ^ (2 ^ k - 1 - (r + 1)) + X ^ (2 ^ k - 1 + (r + 1))))) = 0 := by
    calc sumFin d (fun q => c q * sumRange (2 ^ k - 1) (fun r =>
            apCorr A q q k (r + 1) * (X ^ (2 ^ k - 1 - (r + 1)) + X ^ (2 ^ k - 1 + (r + 1)))))
        = sumRange d (fun i => sumRange (2 ^ k - 1) (fun r =>
            if hi : i < d then c ⟨i, hi⟩ * (apCorr A ⟨i, hi⟩ ⟨i, hi⟩ k (r + 1) *
              (X ^ (2 ^ k - 1 - (r + 1)) + X ^ (2 ^ k - 1 + (r + 1)))) else 0)) := by
          unfold sumFin
          apply sumRange_congr; intro i hi
          simp only [hi, ↓reduceDIte, sumRange_mul_left]
      _ = sumRange (2 ^ k - 1) (fun r => sumRange d (fun i =>
            if hi : i < d then c ⟨i, hi⟩ * (apCorr A ⟨i, hi⟩ ⟨i, hi⟩ k (r + 1) *
              (X ^ (2 ^ k - 1 - (r + 1)) + X ^ (2 ^ k - 1 + (r + 1)))) else 0)) :=
          sumRange_swap d (2 ^ k - 1) _
      _ = sumRange (2 ^ k - 1) (fun r =>
            sumFin d (fun q => c q * apCorr A q q k (r + 1)) *
              (X ^ (2 ^ k - 1 - (r + 1)) + X ^ (2 ^ k - 1 + (r + 1)))) := by
          apply sumRange_congr; intro r _
          unfold sumFin
          rw [← sumRange_mul_right]
          apply sumRange_congr; intro i hi
          simp only [hi, ↓reduceDIte, Int.mul_assoc]
      _ = sumRange (2 ^ k - 1) (fun _ => 0) := by
          apply sumRange_congr; intro r _
          rw [hzero (r + 1) (by omega), Int.zero_mul]
      _ = 0 := sumRange_zero_fn _
  rw [hoff, Int.add_zero, ← sumFin_mul_right]
  apply sumFin_congr; intro q
  rw [Int.mul_assoc]

-- ----------------------------------------------------------------------------
-- NOVEL PARAMETERIZED INFINITE FAMILY: Bijective-Tail Nonlinear Parity Automata
-- (ALL widths L = m + 2 ≥ 2, ALL 2^(2^m) nonlinear Boolean functions ψ!)
-- ----------------------------------------------------------------------------

/-- De Bruijn shift-register transitions on `d = 2^(m+1)` states:
    `del0(q) = q / 2`, `del1(q) = 2^m + q / 2`. -/
def dbDel0 (m : Nat) (q : Fin (2 ^ (m + 1))) : Fin (2 ^ (m + 1)) :=
  ⟨q.1 / 2, by have hpow := pow2_succ m; have hq := q.2; omega⟩

def dbDel1 (m : Nat) (q : Fin (2 ^ (m + 1))) : Fin (2 ^ (m + 1)) :=
  ⟨2 ^ m + q.1 / 2, by have hpow := pow2_succ m; have hq := q.2; omega⟩

/-- General `±1`-signed De Bruijn sliding-window parity automaton of width `L = m + 2`,
    with `sig0(q) = 1` (leading zeros never flip sign) and arbitrary `sig1 : Fin (2^(m+1)) → Int`. -/
def debruijnAuto (m : Nat) (sig1 : Fin (2 ^ (m + 1)) → Int) : BinAuto (2 ^ (m + 1)) where
  del0 := dbDel0 m
  del1 := dbDel1 m
  sig0 := fun _ => 1
  sig1 := sig1
  init := fun _ => 1
  zero_ok := fun _ => by simp

/-- Diagonal trace weight `w(p, q) = 1` if `p = q` else `0`. -/
def traceW (d : Nat) (p q : Fin d) : Int :=
  if p = q then 1 else 0

theorem ite_double (P0 P1 : Prop) [Decidable P0] [Decidable P1] :
    ((if P0 then (1 : Int) * 1 else 0) + (if P1 then 1 else 0)) +
    ((if P0 then 1 * 1 else 0) + (if P1 then 1 else 0)) =
    (if P0 then 2 else 0) + (if P1 then 2 else 0) := by
  by_cases h0 : P0 <;> by_cases h1 : P1 <;> simp [h0, h1]

theorem sumRange_eq_of_eq {n1 n2 : Nat} (h : n1 = n2) (f : Nat → Int) :
    sumRange n1 f = sumRange n2 f := by
  subst h; rfl

/-- **THEOREM 1d (Exact IFF Classification of the 1-Step De Bruijn Trace Annihilator):**
    For EVERY `m : Nat` and EVERY `±1`-valued `sig1 : Fin (2^(m+1)) → Int`,
    the trace functional satisfies the 1-step annihilator `(w·E = 2w ∧ w·O0 = 0 ∧ w·O1 = 0)`
    IF AND ONLY IF the **Bijective-Tail Condition** holds:
    `∀ r : Fin (2^m), sig1(2*r) + sig1(2*r + 1) = 0`. -/
theorem debruijn_trace_annihilator_iff (m : Nat) (sig1 : Fin (2 ^ (m + 1)) → Int)
    (hsig : ∀ q, sig1 q * sig1 q = 1) :
    ((∀ p' q', leftActE (debruijnAuto m sig1) (traceW _) p' q' = 2 * traceW _ p' q') ∧
     (∀ p' q', leftActO0 (debruijnAuto m sig1) (traceW _) p' q' = 0) ∧
     (∀ p' q', leftActO1 (debruijnAuto m sig1) (traceW _) p' q' = 0)) ↔
    (∀ r : Fin (2 ^ m),
      sig1 ⟨2 * r.1, by have _hpow := pow2_succ m; omega⟩ +
      sig1 ⟨2 * r.1 + 1, by have _hpow := pow2_succ m; omega⟩ = 0) := by
  have hsum_pair : ∀ (f : Fin (2 ^ (m + 1)) → Int),
      sumFin (2 ^ (m + 1)) f = sumFin (2 ^ m) (fun r =>
        f ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ +
        f ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩) := by
    intro f
    unfold sumFin
    rw [sumRange_eq_of_eq (pow2_succ m), sumRange_even_odd, ← sumRange_add]
    apply sumRange_congr; intro r hr
    have hpow := pow2_succ m
    have h2r : 2 * r < 2 ^ (m + 1) := by omega
    have h2r1 : 2 * r + 1 < 2 ^ (m + 1) := by omega
    simp [hr, h2r, h2r1]
  have htrace_simp : ∀ (G : Fin (2 ^ (m + 1)) → Fin (2 ^ (m + 1)) → Int),
      sumFin (2 ^ (m + 1)) (fun p => sumFin (2 ^ (m + 1)) (fun q => traceW (2 ^ (m + 1)) p q * G p q)) =
      sumFin (2 ^ (m + 1)) (fun q => G q q) := by
    intro G
    apply sumFin_congr; intro p
    have h : (fun q : Fin (2 ^ (m + 1)) => traceW (2 ^ (m + 1)) p q * G p q) =
        (fun q => if p = q then G p q else 0) := by
      funext q; unfold traceW; by_cases heq : p = q <;> simp [heq]
    rw [h, sumFin_ite_eq]
  have hO0_eval : ∀ p' q' : Fin (2 ^ (m + 1)),
      leftActO0 (debruijnAuto m sig1) (traceW _) p' q' =
      if h : p'.1 < 2 ^ m ∧ q'.1 = 2 ^ m + p'.1 then
        sig1 ⟨2 * p'.1, by have hpow := pow2_succ m; omega⟩ +
        sig1 ⟨2 * p'.1 + 1, by have hpow := pow2_succ m; omega⟩
      else 0 := by
    intro p' q'
    unfold leftActO0
    rw [htrace_simp, hsum_pair]
    have hterm : ∀ r : Fin (2 ^ m),
        (if dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
            dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then
          1 * sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ else 0) +
        (if dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
            dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then
          1 * sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ else 0) =
        if r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1 then
          sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ +
          sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩
        else 0 := by
      intro r
      have h0 : (dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
                 dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q') ↔
                (r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1) := by
        simp only [dbDel0, dbDel1, Fin.ext_iff]; omega
      have h1 : (dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
                 dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q') ↔
                (r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1) := by
        simp only [dbDel0, dbDel1, Fin.ext_iff]; omega
      simp only [h0, h1]
      by_cases hc : r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1
      · simp [hc]
      · simp [hc]
    have hcongr : sumFin (2 ^ m) (fun r =>
        (if (debruijnAuto m sig1).del0 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
            (debruijnAuto m sig1).del1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then
          (debruijnAuto m sig1).sig0 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ *
          (debruijnAuto m sig1).sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ else 0) +
        (if (debruijnAuto m sig1).del0 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
            (debruijnAuto m sig1).del1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then
          (debruijnAuto m sig1).sig0 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ *
          (debruijnAuto m sig1).sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ else 0)) =
      sumFin (2 ^ m) (fun r =>
        if r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1 then
          sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ +
          sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩
        else 0) := by
      apply sumFin_congr; intro r; exact hterm r
    rw [hcongr]
    by_cases hpq : p'.1 < 2 ^ m ∧ q'.1 = 2 ^ m + p'.1
    · have hrew : (fun r : Fin (2 ^ m) =>
          if r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1 then
            sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ +
            sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩
          else 0) =
          (fun r : Fin (2 ^ m) =>
            if r = ⟨p'.1, hpq.1⟩ then
              sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ +
              sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩
            else 0) := by
        funext r
        have hiff : (r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1) ↔ r = ⟨p'.1, hpq.1⟩ := by
          simp [Fin.ext_iff, hpq.2]
        simp only [hiff]
      rw [hrew, sumFin_ite_eq']
      simp [hpq]
    · have hzero : (fun r : Fin (2 ^ m) =>
          if r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1 then
            sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ +
            sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩
          else 0) = fun _ => 0 := by
        funext r
        have hnot : ¬(r.1 = p'.1 ∧ q'.1 = 2 ^ m + p'.1) := by
          intro ⟨h1, h2⟩; apply hpq; exact ⟨h1 ▸ r.2, h2⟩
        simp only [hnot, ↓reduceIte]
      rw [hzero, sumFin_zero]
      simp [hpq]
  have hO1_eval : ∀ p' q' : Fin (2 ^ (m + 1)),
      leftActO1 (debruijnAuto m sig1) (traceW _) p' q' =
      leftActO0 (debruijnAuto m sig1) (traceW _) q' p' := by
    intro p' q'
    unfold leftActO1 leftActO0
    rw [htrace_simp, htrace_simp]
    apply sumFin_congr; intro q
    have hcomm : ((debruijnAuto m sig1).del1 q = p' ∧ (debruijnAuto m sig1).del0 q = q') ↔
                 ((debruijnAuto m sig1).del0 q = q' ∧ (debruijnAuto m sig1).del1 q = p') := and_comm
    simp only [hcomm, Int.mul_comm]
  have hE_always : ∀ p' q' : Fin (2 ^ (m + 1)),
      leftActE (debruijnAuto m sig1) (traceW _) p' q' = 2 * traceW _ p' q' := by
    intro p' q'
    unfold leftActE
    rw [htrace_simp, hsum_pair]
    have hterm : ∀ r : Fin (2 ^ m),
        ((if dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then (1 : Int) * 1 else 0) +
         (if dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then
            sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ * sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ else 0)) +
        ((if dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then (1 : Int) * 1 else 0) +
         (if dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then
            sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ * sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ else 0)) =
        (if r.1 = p'.1 ∧ p' = q' then (2 : Int) else 0) +
        (if 2 ^ m + r.1 = p'.1 ∧ p' = q' then (2 : Int) else 0) := by
      intro r
      rw [hsig, hsig]
      have h0e : (dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
                  dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q') ↔ (r.1 = p'.1 ∧ p' = q') := by
        simp only [dbDel0, Fin.ext_iff]; omega
      have h0o : (dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
                  dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q') ↔ (r.1 = p'.1 ∧ p' = q') := by
        simp only [dbDel0, Fin.ext_iff]; omega
      have h1e : (dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
                  dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q') ↔ (2 ^ m + r.1 = p'.1 ∧ p' = q') := by
        simp only [dbDel1, Fin.ext_iff]; omega
      have h1o : (dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
                  dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q') ↔ (2 ^ m + r.1 = p'.1 ∧ p' = q') := by
        simp only [dbDel1, Fin.ext_iff]; omega
      simp only [h0e, h0o, h1e, h1o]
      exact ite_double _ _
    have hcongr : sumFin (2 ^ m) (fun r =>
        ((if dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then (1 : Int) * 1 else 0) +
         (if dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then
            sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ * sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ else 0)) +
        ((if dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then (1 : Int) * 1 else 0) +
         (if dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then
            sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ * sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ else 0))) =
        sumFin (2 ^ m) (fun r => if r.1 = p'.1 ∧ p' = q' then (2 : Int) else 0) +
        sumFin (2 ^ m) (fun r => if 2 ^ m + r.1 = p'.1 ∧ p' = q' then (2 : Int) else 0) := by
      rw [← sumFin_add]
      apply sumFin_congr; intro r; exact hterm r
    change sumFin (2 ^ m) (fun r =>
        ((if dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel0 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then (1 : Int) * 1 else 0) +
         (if dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel1 m ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ = q' then
            sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ * sig1 ⟨2 * r.1, by have hpow := pow2_succ m; omega⟩ else 0)) +
        ((if dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel0 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then (1 : Int) * 1 else 0) +
         (if dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = p' ∧
             dbDel1 m ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ = q' then
            sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ * sig1 ⟨2 * r.1 + 1, by have hpow := pow2_succ m; omega⟩ else 0))) = _
    rw [hcongr]
    unfold traceW
    by_cases hpq : p' = q'
    · subst hpq
      have hite : (2 : Int) * (if p' = p' then 1 else 0) = 2 := by simp
      rw [hite]
      simp only [eq_self, and_true]
      by_cases hlt : p'.1 < 2 ^ m
      · have s1 : sumFin (2 ^ m) (fun r => if r.1 = p'.1 then (2 : Int) else 0) = 2 := by
          have : (fun r : Fin (2 ^ m) => if r.1 = p'.1 then (2 : Int) else 0) =
              (fun r : Fin (2 ^ m) => if r = ⟨p'.1, hlt⟩ then 2 else 0) := by
            funext r; by_cases h : r = ⟨p'.1, hlt⟩
            · simp [h]
            · have hne : r.1 ≠ p'.1 := by intro he; apply h; exact Fin.ext he
              simp [h, hne]
          rw [this, sumFin_ite_eq']
        have s2 : sumFin (2 ^ m) (fun r => if 2 ^ m + r.1 = p'.1 then (2 : Int) else 0) = 0 := by
          have : (fun r : Fin (2 ^ m) => if 2 ^ m + r.1 = p'.1 then (2 : Int) else 0) = fun _ => 0 := by
            funext r; have : 2 ^ m + r.1 ≠ p'.1 := by omega
            simp [this]
          rw [this, sumFin_zero]
        rw [s1, s2]; rfl
      · have hge : p'.1 - 2 ^ m < 2 ^ m := by
          have hpow := pow2_succ m; have hp2 := p'.2; omega
        have s1 : sumFin (2 ^ m) (fun r => if r.1 = p'.1 then (2 : Int) else 0) = 0 := by
          have : (fun r : Fin (2 ^ m) => if r.1 = p'.1 then (2 : Int) else 0) = fun _ => 0 := by
            funext r; have : r.1 ≠ p'.1 := by omega
            simp [this]
          rw [this, sumFin_zero]
        have s2 : sumFin (2 ^ m) (fun r => if 2 ^ m + r.1 = p'.1 then (2 : Int) else 0) = 2 := by
          have : (fun r : Fin (2 ^ m) => if 2 ^ m + r.1 = p'.1 then (2 : Int) else 0) =
              (fun r : Fin (2 ^ m) => if r = ⟨p'.1 - 2 ^ m, hge⟩ then 2 else 0) := by
            funext r
            have : 2 ^ m + r.1 = p'.1 ↔ r = ⟨p'.1 - 2 ^ m, hge⟩ := by
              simp [Fin.ext_iff]; omega
            simp only [this]
          rw [this, sumFin_ite_eq']
        rw [s1, s2]; rfl
    · simp only [hpq, ↓reduceIte, Int.mul_zero, and_false, sumFin_zero, Int.add_zero]
  constructor
  · intro ⟨_, hO0, _⟩ r
    have hr1 : r.1 < 2 ^ (m + 1) := by have hpow := pow2_succ m; omega
    have hr2 : 2 ^ m + r.1 < 2 ^ (m + 1) := by have hpow := pow2_succ m; omega
    have h := hO0 ⟨r.1, hr1⟩ ⟨2 ^ m + r.1, hr2⟩
    rw [hO0_eval] at h
    have hcond : r.1 < 2 ^ m ∧ 2 ^ m + r.1 = 2 ^ m + r.1 := ⟨r.2, rfl⟩
    simp only [hcond] at h
    exact h
  · intro hbij
    refine ⟨hE_always, ?_, ?_⟩
    · intro p' q'
      rw [hO0_eval]
      by_cases h : p'.1 < 2 ^ m ∧ q'.1 = 2 ^ m + p'.1
      · simp only [h]; exact hbij ⟨p'.1, h.1⟩
      · simp only [h, ↓reduceDIte]
    · intro p' q'
      rw [hO1_eval, hO0_eval]
      by_cases h : q'.1 < 2 ^ m ∧ p'.1 = 2 ^ m + q'.1
      · simp only [h]; exact hbij ⟨q'.1, h.1⟩
      · simp only [h, ↓reduceDIte]

/-- **Bijective-Tail Nonlinear Sliding-Window Parity Automaton** for ANY `m : Nat`
    (window length `L = m + 2`) and ANY Boolean feedback function `ψ : Fin (2^m) → Bool`:
    `sig1(q) = (-1)^(ψ(q/2) ⊕ (q % 2))`. -/
def bijTailSig1 (m : Nat) (ψ : Fin (2 ^ m) → Bool) (q : Fin (2 ^ (m + 1))) : Int :=
  let r : Fin (2 ^ m) := ⟨q.1 / 2, by have hpow := pow2_succ m; have hq := q.2; omega⟩
  if xor (ψ r) (q.1 % 2 == 1) then -1 else 1

def bijTailAuto (m : Nat) (ψ : Fin (2 ^ m) → Bool) : BinAuto (2 ^ (m + 1)) :=
  debruijnAuto m (bijTailSig1 m ψ)

/-- Nonlinear quadratic feedback `ψ(b1, b2) = b1 && b2` on `Fin 4` (`r = 3` iff `b1 = b2 = 1`). -/
def psiCubic (r : Fin 4) : Bool := r.1 == 3

/-- The genuinely cubic `L = 4` bijective-tail automaton:
    realizes `(-1)^(popcount(n & (((n <<< 1) & (n <<< 2)) ^^^ (n <<< 3))))`. -/
def cubicL4Auto : BinAuto 8 := bijTailAuto 2 psiCubic

/-- Exact binary popcount (pure core Lean 4). -/
def popcount (n : Nat) : Nat :=
  if _h : n = 0 then 0
  else (n % 2) + popcount (n / 2)
termination_by n
decreasing_by omega

/-- Direct bitwise parity formula for the cubic `L = 4` sequence:
    counts overlapping `(b_j = 1) ∧ ((b_{j-1} ∧ b_{j-2}) ⊕ b_{j-3})`. -/
def directCubicParity (n : Nat) : Int :=
  if popcount (n &&& (((n <<< 1) &&& (n <<< 2)) ^^^ (n <<< 3))) % 2 == 0 then 1 else -1

/-- General state-conditioned bitwise parity formula for `cubicL4Auto` at state `q < 8`. -/
def cubicAux (q : Fin 8) (n : Nat) : Nat :=
  let x := n * 8 + q.1
  let mask := (x / 8) &&& ((((x / 4) &&& (x / 2)) ^^^ x))
  popcount mask

theorem testBit_eq_div_mod (n k : Nat) :
    Nat.testBit n k = ((n / 2 ^ k) % 2 == 1) := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem popcount_zero : popcount 0 = 0 := by
  rw [popcount]; simp

theorem popcount_bit_split (m : Nat) :
    popcount m = m % 2 + popcount (m / 2) := by
  by_cases hm : m = 0
  · subst hm; rw [popcount_zero]
  · rw [popcount]; simp only [hm, ↓reduceDIte]

theorem cubic_step_bit (q : Fin 8) (n : Nat) (b : Nat) (hb : b < 2) :
    let q' : Fin 8 := if b = 0 then dbDel0 2 q else dbDel1 2 q
    let w : Nat := if b = 0 then 0 else if xor (psiCubic ⟨q.1 / 2, by omega⟩) (q.1 % 2 == 1) then 1 else 0
    cubicAux q (2 * n + b) = w + cubicAux q' n := by
  dsimp only [cubicAux]
  let x := (2 * n + b) * 8 + q.1
  let m := (x / 8) &&& (((x / 4) &&& (x / 2)) ^^^ x)
  change popcount m = _
  rw [popcount_bit_split m]
  have hlsb : m % 2 = (if b = 0 then 0 else if xor (psiCubic ⟨q.1 / 2, by omega⟩) (q.1 % 2 == 1) then 1 else 0) := by
    have hbit : m % 2 = if Nat.testBit m 0 then 1 else 0 := by
      rw [Nat.testBit_zero]; cases h : decide (m % 2 = 1) <;> simp_all <;> omega
    rw [hbit]
    have htest : Nat.testBit m 0 =
        (Nat.testBit (x / 8) 0 && ((Nat.testBit (x / 4) 0 && Nat.testBit (x / 2) 0) ^^ Nat.testBit x 0)) := by
      rw [show m = (x / 8) &&& (((x / 4) &&& (x / 2)) ^^^ x) from rfl,
          Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and]
    rw [htest]
    have hx8 : (x / 8) % 2 = b := by dsimp [x]; omega
    have hx4 : (x / 4) % 2 = (q.1 / 4) % 2 := by dsimp [x]; omega
    have hx2 : (x / 2) % 2 = (q.1 / 2) % 2 := by dsimp [x]; omega
    have hx1 : x % 2 = q.1 % 2 := by dsimp [x]; omega
    simp only [Nat.testBit_zero, hx8, hx4, hx2, hx1, psiCubic]
    have hq8 := q.2
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · simp
    · rcases (show q.1 = 0 ∨ q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 3 ∨ q.1 = 4 ∨ q.1 = 5 ∨ q.1 = 6 ∨ q.1 = 7 by omega) with
        h | h | h | h | h | h | h | h <;> simp [h]
  have hdiv : m / 2 =
      ((n * 8 + (if b = 0 then dbDel0 2 q else dbDel1 2 q).1) / 8) &&&
      ((((n * 8 + (if b = 0 then dbDel0 2 q else dbDel1 2 q).1) / 4) &&&
        ((n * 8 + (if b = 0 then dbDel0 2 q else dbDel1 2 q).1) / 2)) ^^^
        (n * 8 + (if b = 0 then dbDel0 2 q else dbDel1 2 q).1)) := by
    have hq_val : (if b = 0 then dbDel0 2 q else dbDel1 2 q).1 = b * 4 + q.1 / 2 := by
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp [dbDel0, dbDel1]
    rw [hq_val]
    have hx2 : x / 2 = n * 8 + (b * 4 + q.1 / 2) := by dsimp [x]; omega
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show m = (x / 8) &&& (((x / 4) &&& (x / 2)) ^^^ x) from rfl]
    simp only [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_xor]
    have h1 : (x / 8) / 2 ^ (i + 1) = (x / 2 / 8) / 2 ^ i := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.pow_succ]
      congr 1; omega
    have h2 : (x / 4) / 2 ^ (i + 1) = (x / 2 / 4) / 2 ^ i := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.pow_succ]
      congr 1; omega
    have h3 : x / 2 ^ (i + 1 + 1) = (x / 2) / 2 ^ (i + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]; congr 1; omega
    have h4 : x / 2 ^ (i + 1) = (x / 2) / 2 ^ i := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]; congr 1; omega
    rw [testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod,
        testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod,
        h1, h2, h3, h4, hx2]
  rw [hlsb, hdiv]

/-- **Concrete Non-Vacuity & Bitwise Equivalence Theorem for the Cubic `L = 4` Sequence:**
    For EVERY `n : Nat`, `cubicL4Auto.eval 0 n = (-1)^popcount(n & (((n <<< 1) & (n <<< 2)) ^^^ (n <<< 3)))`. -/
theorem cubicL4Auto_eq_direct (n : Nat) :
    cubicL4Auto.eval 0 n = directCubicParity n := by
  have hgen : ∀ n (q : Fin 8), cubicL4Auto.eval q n = if cubicAux q n % 2 == 0 then 1 else -1 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro q
      by_cases hn : n = 0
      · subst hn
        rw [BinAuto.eval_zero]
        have hz : cubicAux q 0 = 0 := by
          unfold cubicAux
          dsimp only
          have hq8 := q.2
          have h0 : (0 * 8 + q.1) / 8 = 0 := by omega
          have h00 : 0 &&& (((0 * 8 + q.1) / 4 &&& (0 * 8 + q.1) / 2) ^^^ (0 * 8 + q.1)) = 0 := by simp
          rw [h0, h00, popcount_zero]
        simp [cubicL4Auto, bijTailAuto, debruijnAuto, hz]
      · by_cases hp : n % 2 = 0
        · have hn2 : n = 2 * (n / 2) + 0 := by omega
          have hstep := cubic_step_bit q (n / 2) 0 (by omega)
          simp only [↓reduceIte, Nat.zero_add] at hstep
          have hev : cubicL4Auto.eval q n = cubicL4Auto.eval (dbDel0 2 q) (n / 2) := by
            conv => lhs; rw [show n = 2 * (n / 2) by omega]
            rw [BinAuto.eval_even]
            simp [cubicL4Auto, bijTailAuto, debruijnAuto]
          rw [hev, ih (n / 2) (by omega)]
          conv => rhs; rw [hn2, hstep]
        · have hn2 : n = 2 * (n / 2) + 1 := by omega
          have hstep := cubic_step_bit q (n / 2) 1 (by omega)
          simp only [show (1 : Nat) ≠ 0 by omega, ↓reduceIte] at hstep
          have hodd : cubicL4Auto.eval q n =
              bijTailSig1 2 psiCubic q * cubicL4Auto.eval (dbDel1 2 q) (n / 2) := by
            conv => lhs; rw [hn2]
            rw [BinAuto.eval_odd]
            rfl
          rw [hodd, ih (n / 2) (by omega)]
          conv => rhs; rw [hn2, hstep]
          unfold bijTailSig1
          by_cases hx : (xor (psiCubic ⟨q.1 / 2, by omega⟩) (q.1 % 2 == 1)) = true
          · simp only [hx, ↓reduceIte]
            by_cases hc : cubicAux (dbDel1 2 q) (n / 2) % 2 = 0
            · have h1 : (1 + cubicAux (dbDel1 2 q) (n / 2)) % 2 = 1 := by omega
              simp [hc, h1]
            · have h1 : (1 + cubicAux (dbDel1 2 q) (n / 2)) % 2 = 0 := by omega
              simp [hc, h1]
          · simp only [hx, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Nat.zero_add]
  rw [hgen n 0]
  unfold directCubicParity cubicAux
  have hmask : (n * 8 + (0 : Fin 8).1) / 8 &&&
      ((((n * 8 + (0 : Fin 8).1) / 4) &&& ((n * 8 + (0 : Fin 8).1) / 2)) ^^^ (n * 8 + (0 : Fin 8).1)) =
      n &&& (((n <<< 1) &&& (n <<< 2)) ^^^ (n <<< 3)) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.shiftLeft_eq]
    have hx : n * 8 + (0 : Fin 8).1 = n * 8 := by simp
    rw [hx]
    have h1 : (n * 8) / 8 = n := by omega
    have h2 : (n * 8) / 4 = n * 2 := by omega
    have h3 : (n * 8) / 2 = n * 4 := by omega
    rw [h1, h2, h3]
  simp only [hmask]

/-- **Sharpness Counterexample for Theorem 1:**
    Breaking the bijective-tail condition (pure `111`-parity without the `n <<< 3` tail bit)
    destroys flat-spectrum cancellation immediately at `k = 1, s = 1` (`sum = 4 ≠ 0`). -/
def broken111Auto : BinAuto 8 :=
  debruijnAuto 2 (fun q => if q.1 ≥ 6 then -1 else 1)

theorem broken111_sharpness_counterexample :
    sumFin 8 (fun q => apCorr broken111Auto q q 1 1) = 4 := by
  have h1 : ∀ q : Fin 8, apCorr broken111Auto q q 1 1 =
      broken111Auto.sig0 q * broken111Auto.sig1 q *
        (broken111Auto.init (broken111Auto.del0 q) * broken111Auto.init (broken111Auto.del1 q)) := by
    intro q
    have h := apCorr_odd broken111Auto q q 0 0
    simp only [Nat.mul_zero, Nat.zero_add, apCorr_zero_zero, apCorr_zero_succ, Int.mul_zero, Int.add_zero] at h
    exact h
  simp only [h1]
  decide

-- ============================================================================
-- Section 3: Mechanism B — Sparse O(D^2) QRZ & Dual-Krylov L^4-Energy Compiler
-- ============================================================================

theorem pos_of_fin_sq {d : Nat} (u : Fin (d * d)) : 0 < d :=
  Nat.pos_of_mul_pos_right (Nat.lt_of_le_of_lt (Nat.zero_le _) u.2)

/-- The 4 deterministic transition maps on `D = d * d` state-pairs `u = (p, q)`
    corresponding to `T00, T11, T01, T10`. -/
def pairStep {d : Nat} (A : BinAuto d) (tag : Fin 4) (u : Fin (d * d)) : Fin (d * d) :=
  let hd := pos_of_fin_sq u
  let p : Fin d := ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩
  let q : Fin d := ⟨u.1 % d, Nat.mod_lt u.1 hd⟩
  match tag.1 with
  | 0 => pairIdx (A.del0 p) (A.del0 q)
  | 1 => pairIdx (A.del1 p) (A.del1 q)
  | 2 => pairIdx (A.del0 p) (A.del1 q)
  | _ => pairIdx (A.del1 p) (A.del0 q)

def pairWeight {d : Nat} (A : BinAuto d) (tag : Fin 4) (u : Fin (d * d)) : Int :=
  let hd := pos_of_fin_sq u
  let p : Fin d := ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩
  let q : Fin d := ⟨u.1 % d, Nat.mod_lt u.1 hd⟩
  match tag.1 with
  | 0 => A.sig0 p * A.sig0 q
  | 1 => A.sig1 p * A.sig1 q
  | 2 => A.sig0 p * A.sig1 q
  | _ => A.sig1 p * A.sig0 q

/-- Pair-indexed aperiodic correlation `A_u(k, s)` for `u : Fin (d * d)`. -/
def apCorrU {d : Nat} (A : BinAuto d) (u : Fin (d * d)) (k s : Nat) : Int :=
  let hd := pos_of_fin_sq u
  apCorr A ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩ ⟨u.1 % d, Nat.mod_lt u.1 hd⟩ k s

theorem pairIdx_div_mod {d : Nat} (p q : Fin d) :
    (pairIdx p q).1 / d = p.1 ∧ (pairIdx p q).1 % d = q.1 := by
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  simp only [pairIdx]
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt q.2, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt q.2]

theorem apCorrU_pairIdx {d : Nat} (A : BinAuto d) (p q : Fin d) (k s : Nat) :
    apCorrU A (pairIdx p q) k s = apCorr A p q k s := by
  unfold apCorrU
  have ⟨h1, h2⟩ := pairIdx_div_mod p q
  have hp : (⟨(pairIdx p q).1 / d, Nat.div_lt_of_lt_mul (pairIdx p q).2⟩ : Fin d) = p := Fin.ext h1
  have hq : (⟨(pairIdx p q).1 % d, Nat.mod_lt (pairIdx p q).1 (pos_of_fin_sq (pairIdx p q))⟩ : Fin d) = q := Fin.ext h2
  rw [hp, hq]

theorem apCorrU_odd {d : Nat} (A : BinAuto d) (u : Fin (d * d)) (k t : Nat) :
    apCorrU A u (k + 1) (2 * t + 1) =
      pairWeight A 2 u * apCorrU A (pairStep A 2 u) k t +
      pairWeight A 3 u * apCorrU A (pairStep A 3 u) k (t + 1) := by
  have h2s : pairStep A 2 u = pairIdx (A.del0 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩)
      (A.del1 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩) := rfl
  have h3s : pairStep A 3 u = pairIdx (A.del1 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩)
      (A.del0 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩) := rfl
  have h2w : pairWeight A 2 u = A.sig0 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩ *
      A.sig1 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩ := rfl
  have h3w : pairWeight A 3 u = A.sig1 ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩ *
      A.sig0 ⟨u.1 % d, Nat.mod_lt u.1 (pos_of_fin_sq u)⟩ := rfl
  rw [h2s, h3s, h2w, h3w, apCorrU_pairIdx, apCorrU_pairIdx]
  exact apCorr_odd A _ _ k t

theorem apCorrU_ge {d : Nat} (A : BinAuto d) (u : Fin (d * d)) (k s : Nat) (h : 2 ^ k ≤ s) :
    apCorrU A u k s = 0 := apCorr_ge A _ _ k s h

/-- The three infinite-shift quadratic autocorrelation tensors `(Q, R, Z)` at scale `k`. -/
def qTensor {d : Nat} (A : BinAuto d) (k : Nat) (u v : Fin (d * d)) : Int :=
  sumRange (2 ^ k) (fun s => apCorrU A u k s * apCorrU A v k s)

def rTensor {d : Nat} (A : BinAuto d) (k : Nat) (u v : Fin (d * d)) : Int :=
  sumRange (2 ^ k) (fun s => apCorrU A u k s * apCorrU A v k (s + 1))

def zTensor {d : Nat} (A : BinAuto d) (k : Nat) (u v : Fin (d * d)) : Int :=
  apCorrU A u k 0 * apCorrU A v k 0

/-- Exact `L^4` autocorrelation energy of state `q` at length `2^k`:
    `E4 A q k = A_{q,q}(k, 0)^2 + 2 * ∑_{s=1}^{2^k - 1} A_{q,q}(k, s)^2`. -/
def E4State {d : Nat} (A : BinAuto d) (q : Fin d) (k : Nat) : Int :=
  apCorr A q q k 0 * apCorr A q q k 0 +
  2 * sumRange (2 ^ k - 1) (fun r => apCorr A q q k (r + 1) * apCorr A q q k (r + 1))

theorem E4State_eq_qrz {d : Nat} (A : BinAuto d) (q : Fin d) (k : Nat) :
    E4State A q k = 2 * qTensor A k (pairIdx q q) (pairIdx q q) - zTensor A k (pairIdx q q) (pairIdx q q) := by
  unfold E4State qTensor zTensor
  have hpos : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have hsplit : 2 ^ k = (2 ^ k - 1) + 1 := by omega
  conv => rhs; rw [hsplit, sumRange_succ_left]
  simp only [apCorrU_pairIdx]
  omega

/-- Total `L^4` energy across all `d` states of `A`. -/
def totE4 {d : Nat} (A : BinAuto d) (k : Nat) : Int :=
  sumFin d (fun q => E4State A q k)

/-- Exact state triple `QRZFn D` represented as three `D × D` integer functions. -/
structure QRZFn (D : Nat) where
  Q : Fin D → Fin D → Int
  R : Fin D → Fin D → Int
  Z : Fin D → Fin D → Int

def pull {d : Nat} (A : BinAuto d) (a b : Fin 4) (X : Fin (d * d) → Fin (d * d) → Int)
    (u v : Fin (d * d)) : Int :=
  pairWeight A a u * pairWeight A b v * X (pairStep A a u) (pairStep A b v)

/-- The exact finite-dimensional `QRZ` Energy Transfer Operator `primalStep`. -/
def primalStep {d : Nat} (A : BinAuto d) (S : QRZFn (d * d)) : QRZFn (d * d) where
  Q u v :=
    pull A 0 0 S.Q u v + pull A 0 1 S.Q u v + pull A 1 0 S.Q u v + pull A 1 1 S.Q u v +
    pull A 2 2 S.Q u v + pull A 3 3 (fun x y => S.Q x y - S.Z x y) u v +
    pull A 2 3 S.R u v + pull A 3 2 (fun x y => S.R y x) u v
  R u v :=
    pull A 0 2 S.Q u v + pull A 1 2 S.Q u v +
    pull A 3 0 (fun x y => S.Q x y - S.Z x y) u v + pull A 3 1 (fun x y => S.Q x y - S.Z x y) u v +
    pull A 0 3 S.R u v + pull A 1 3 S.R u v + pull A 2 0 S.R u v + pull A 2 1 S.R u v
  Z u v :=
    pull A 0 0 S.Z u v + pull A 0 1 S.Z u v + pull A 1 0 S.Z u v + pull A 1 1 S.Z u v

def qrzAt {d : Nat} (A : BinAuto d) (k : Nat) : QRZFn (d * d) where
  Q := qTensor A k
  R := rTensor A k
  Z := zTensor A k

theorem sumRange_shift_tail {d : Nat} (A : BinAuto d) (k : Nat) (x y : Fin (d * d)) :
    sumRange (2 ^ k) (fun t => apCorrU A x k (t + 1) * apCorrU A y k (t + 1)) =
    qTensor A k x y - zTensor A k x y := by
  unfold qTensor zTensor
  have h1 : sumRange (2 ^ k + 1) (fun t => apCorrU A x k t * apCorrU A y k t) =
      sumRange (2 ^ k) (fun t => apCorrU A x k t * apCorrU A y k t) := by
    rw [sumRange, apCorrU_ge A x k (2 ^ k) (Nat.le_refl _), Int.zero_mul, Int.add_zero]
  rw [sumRange_succ_left] at h1
  omega

theorem prod_two_add (a0 x0 a1 x1 b0 y0 b1 y1 : Int) :
    (a0 * x0 + a1 * x1) * (b0 * y0 + b1 * y1) =
    a0 * b0 * (x0 * y0) + a0 * b1 * (x0 * y1) + a1 * b0 * (x1 * y0) + a1 * b1 * (x1 * y1) := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add,
      mul_four a0 b0 x0 y0, mul_four a0 b1 x0 y1, mul_four a1 b0 x1 y0, mul_four a1 b1 x1 y1]
  omega

/-- Materialized `D × D` integer grid for fast kernel reduction (`decide`) without closure blowup. -/
abbrev Grid := List (List Int)

def getG (G : Grid) (u v : Nat) : Int :=
  (G.getD u []).getD v 0

def tabulateG (D : Nat) (f : Fin D → Fin D → Int) : Grid :=
  List.ofFn fun u => List.ofFn fun v => f u v

theorem getG_tabulateG (D : Nat) (f : Fin D → Fin D → Int) (u v : Fin D) :
    getG (tabulateG D f) u.1 v.1 = f u v := by
  unfold getG tabulateG
  have h1 : (List.ofFn fun u : Fin D => List.ofFn fun v : Fin D => f u v).getD u.1 [] =
      List.ofFn (fun v : Fin D => f u v) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [u.2]
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [v.2]

/-- Pure-data materialized Dual `QRZ` functional `(WQ, WR, WZ)`. -/
structure DualQRZ where
  WQ : Grid
  WR : Grid
  WZ : Grid
  deriving DecidableEq

/-- Frobenius inner product between a materialized `DualQRZ` and a functional `QRZFn`. -/
def innerGrid (D : Nat) (G : Grid) (X : Fin D → Fin D → Int) : Int :=
  sumFin D (fun u => sumFin D (fun v => getG G u.1 v.1 * X u v))

def innerQRZ (D : Nat) (W : DualQRZ) (S : QRZFn D) : Int :=
  innerGrid D W.WQ S.Q + innerGrid D W.WR S.R + innerGrid D W.WZ S.Z

/-- Pure-data initial evaluation `⟨W, qrzAt A 0⟩` without invoking well-founded `BinAuto.eval`! -/
def initPair {d : Nat} (A : BinAuto d) (u : Fin (d * d)) : Int :=
  let hd := pos_of_fin_sq u
  A.init ⟨u.1 / d, Nat.div_lt_of_lt_mul u.2⟩ * A.init ⟨u.1 % d, Nat.mod_lt u.1 hd⟩

def evalDualAtZero {d : Nat} (A : BinAuto d) (W : DualQRZ) : Int :=
  sumFin (d * d) (fun u => sumFin (d * d) (fun v =>
    (getG W.WQ u.1 v.1 + getG W.WZ u.1 v.1) * (initPair A u * initPair A v)))

theorem innerQRZ_qrzAt_zero {d : Nat} (A : BinAuto d) (W : DualQRZ) :
    innerQRZ (d * d) W (qrzAt A 0) = evalDualAtZero A W := by
  have hq0 : ∀ u v : Fin (d * d), (qrzAt A 0).Q u v = initPair A u * initPair A v := by
    intro u v
    dsimp [qrzAt, qTensor, apCorrU, initPair]
    simp [sumRange, apCorr_zero_zero]
  have hr0 : ∀ u v : Fin (d * d), (qrzAt A 0).R u v = 0 := by
    intro u v
    dsimp [qrzAt, rTensor, apCorrU]
    simp [sumRange, apCorr_zero_succ]
  have hz0 : ∀ u v : Fin (d * d), (qrzAt A 0).Z u v = initPair A u * initPair A v := by
    intro u v
    dsimp [qrzAt, zTensor, apCorrU, initPair]
    simp [apCorr_zero_zero]
  unfold innerQRZ innerGrid evalDualAtZero
  have hQ : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG W.WQ u.1 v.1 * (qrzAt A 0).Q u v)) =
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG W.WQ u.1 v.1 * (initPair A u * initPair A v))) := by
    apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hq0]
  have hR : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG W.WR u.1 v.1 * (qrzAt A 0).R u v)) = 0 := by
    simp [hr0, sumFin_zero]
  have hZ : sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG W.WZ u.1 v.1 * (qrzAt A 0).Z u v)) =
      sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG W.WZ u.1 v.1 * (initPair A u * initPair A v))) := by
    apply sumFin_congr; intro u; apply sumFin_congr; intro v; rw [hz0]
  rw [hQ, hR, hZ, Int.add_zero, ← sumFin_add]
  apply sumFin_congr; intro u
  rw [← sumFin_add]
  apply sumFin_congr; intro v
  rw [Int.add_mul]

/-- Precomputed preimage list for `pairStep A tag`: all `(u, pairWeight A tag u)` with `pairStep A tag u = u'`. -/
def preimages {d : Nat} (A : BinAuto d) (tag : Fin 4) (u' : Fin (d * d)) : List (Fin (d * d) × Int) :=
  (List.finRange (d * d)).filterMap fun u =>
    if pairStep A tag u = u' then
      let c := pairWeight A tag u
      if c = 0 then none else some (u, c)
    else none

/-- Precomputed preimage table for all 4 tags and all `u' : Fin (d * d)` (computed ONCE per certificate!). -/
abbrev PreTable (D : Nat) := List (List (List (Fin D × Int)))

def buildPreTable {d : Nat} (A : BinAuto d) : PreTable (d * d) :=
  List.ofFn fun tag : Fin 4 => List.ofFn fun u' : Fin (d * d) => preimages A tag u'

def getPre {D : Nat} (pt : PreTable D) (tag : Fin 4) (u' : Fin D) : List (Fin D × Int) :=
  (pt.getD tag.1 []).getD u'.1 []

theorem getPre_buildPreTable {d : Nat} (A : BinAuto d) (tag : Fin 4) (u' : Fin (d * d)) :
    getPre (buildPreTable A) tag u' = preimages A tag u' := by
  unfold getPre buildPreTable
  have h1 : (List.ofFn fun t : Fin 4 => List.ofFn fun x : Fin (d * d) => preimages A t x).getD tag.1 [] =
      List.ofFn fun x : Fin (d * d) => preimages A tag x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [tag.2]
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [u'.2]

/-- Fast sparse sum over preimage list. -/
def sumPre {D : Nat} (l : List (Fin D × Int)) (f : Fin D → Int → Int) : Int :=
  l.foldl (fun acc p => acc + f p.1 p.2) 0

theorem sumPre_eq_foldr {D : Nat} (l : List (Fin D × Int)) (f : Fin D → Int → Int) :
    sumPre l f = (l.map (fun p => f p.1 p.2)).sum := by
  unfold sumPre
  have hgen : ∀ (init : Int) (xs : List (Fin D × Int)),
      xs.foldl (fun acc p => acc + f p.1 p.2) init = init + (xs.map (fun p => f p.1 p.2)).sum := by
    intro init xs
    induction xs generalizing init with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      omega
  simpa using hgen 0 l

theorem list_map_zero_sum {α : Type} (xs : List α) :
    (xs.map fun _ => (0 : Int)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]

theorem list_ofFn_sum_eq_sumFin {D : Nat} (g : Fin D → Int) :
    (List.ofFn g).sum = sumFin D g := by
  unfold sumFin
  induction D with
  | zero => simp [sumRange]
  | succ D ih =>
    rw [List.ofFn_succ, List.sum_cons, ih (fun i : Fin D => g i.succ), sumRange_succ_left]
    simp only [Nat.zero_lt_succ, ↓reduceDIte]
    congr 1
    apply sumRange_congr; intro i hi
    have h1 : i + 1 < D + 1 := by omega
    simp [hi, h1]

theorem sum_map_filterMap_pre {D : Nat} (step : Fin D → Fin D) (wt : Fin D → Int)
    (u' : Fin D) (f : Fin D → Int → Int) (hf0 : ∀ u, f u 0 = 0) :
    sumPre ((List.finRange D).filterMap fun u =>
      if step u = u' then let c := wt u; if c = 0 then none else some (u, c) else none) f =
    sumFin D (fun u => if step u = u' then f u (wt u) else 0) := by
  rw [sumPre_eq_foldr]
  have hlist : ∀ (xs : List (Fin D)),
      ((xs.filterMap fun u =>
        if step u = u' then let c := wt u; if c = 0 then none else some (u, c) else none).map
        fun p => f p.1 p.2).sum =
      (xs.map fun u => if step u = u' then f u (wt u) else 0).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
      by_cases hs : step x = u'
      · by_cases hw : wt x = 0
        · simp [hs, hw, hf0, ih]
        · simp [hs, hw, ih]
      · simp [hs, ih]
  rw [hlist]
  have heq : (List.finRange D).map (fun u => if step u = u' then f u (wt u) else 0) =
      List.ofFn (fun u => if step u = u' then f u (wt u) else 0) := by
    rw [List.finRange, List.map_ofFn]; rfl
  rw [heq, list_ofFn_sum_eq_sumFin]

/-- Fast short-circuiting sparse entry `(u', v')` of `push a b G` (O(1) zero when either preimage is empty!). -/
def pushEntry {D : Nat} (pre : Fin 4 → Fin D → List (Fin D × Int))
    (a b : Fin 4) (G : Grid) (u' v' : Fin D) : Int :=
  match pre a u', pre b v' with
  | [], _ => 0
  | _, [] => 0
  | lu, lv =>
    sumPre lu fun u cu =>
      let row := G.getD u.1 []
      sumPre lv fun v cv =>
        row.getD v.1 0 * cu * cv

/-- Fast short-circuiting sparse entry `(u', v')` of `push` on `G^T`. -/
def pushEntryT {D : Nat} (pre : Fin 4 → Fin D → List (Fin D × Int))
    (a b : Fin 4) (G : Grid) (u' v' : Fin D) : Int :=
  match pre a u', pre b v' with
  | [], _ => 0
  | _, [] => 0
  | lu, lv =>
    sumPre lv fun v cv =>
      let row := G.getD v.1 []
      sumPre lu fun u cu =>
        row.getD u.1 0 * cu * cv

theorem pushEntry_eq_nested {D : Nat} (pre : Fin 4 → Fin D → List (Fin D × Int))
    (a b : Fin 4) (G : Grid) (u' v' : Fin D) :
    pushEntry pre a b G u' v' =
    sumPre (pre a u') (fun u cu => sumPre (pre b v') (fun v cv => getG G u.1 v.1 * cu * cv)) := by
  unfold pushEntry getG
  cases hlu : pre a u' with
  | nil => rfl
  | cons x xs =>
    cases hlv : pre b v' with
    | nil =>
      rw [sumPre_eq_foldr]
      exact (list_map_zero_sum (x :: xs)).symm
    | cons y ys => rfl

theorem sumPre_swap {D : Nat} (lu lv : List (Fin D × Int)) (f : Fin D → Int → Fin D → Int → Int) :
    sumPre lv (fun v cv => sumPre lu (fun u cu => f u cu v cv)) =
    sumPre lu (fun u cu => sumPre lv (fun v cv => f u cu v cv)) := by
  simp only [sumPre_eq_foldr]
  induction lv with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact (list_map_zero_sum lu).symm
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have hadd : ∀ (xs : List (Fin D × Int)) (g h : Fin D × Int → Int),
        (xs.map g).sum + (xs.map h).sum = (xs.map fun p => g p + h p).sum := by
      intro xs g h; induction xs with
      | nil => simp
      | cons x xs ihx => simp only [List.map_cons, List.sum_cons]; omega
    rw [hadd]

theorem pushEntryT_eq_nested {D : Nat} (pre : Fin 4 → Fin D → List (Fin D × Int))
    (a b : Fin 4) (G : Grid) (u' v' : Fin D) :
    pushEntryT pre a b G u' v' =
    sumPre (pre a u') (fun u cu => sumPre (pre b v') (fun v cv => getG G v.1 u.1 * cu * cv)) := by
  unfold pushEntryT getG
  cases hlu : pre a u' with
  | nil => rfl
  | cons x xs =>
    cases hlv : pre b v' with
    | nil =>
      rw [sumPre_eq_foldr]
      exact (list_map_zero_sum (x :: xs)).symm
    | cons y ys =>
      exact sumPre_swap (x :: xs) (y :: ys) (fun u cu v cv => (G.getD v.1 []).getD u.1 0 * cu * cv)

/-- **Exact Sparse `O(D^2)` Adjoint Step Given Precomputed Preimage Table `pt`:** -/
def dualStepPre (D : Nat) (pt : PreTable D) (W : DualQRZ) : DualQRZ :=
  let pre := getPre pt
  let pe := pushEntry pre
  let pet := pushEntryT pre
  { WQ := tabulateG D fun u' v' =>
      pe 0 0 W.WQ u' v' + pe 0 1 W.WQ u' v' + pe 1 0 W.WQ u' v' + pe 1 1 W.WQ u' v' +
      pe 2 2 W.WQ u' v' + pe 3 3 W.WQ u' v' +
      pe 0 2 W.WR u' v' + pe 1 2 W.WR u' v' + pe 3 0 W.WR u' v' + pe 3 1 W.WR u' v'
    WR := tabulateG D fun u' v' =>
      pe 2 3 W.WQ u' v' + pet 2 3 W.WQ u' v' +
      pe 0 3 W.WR u' v' + pe 1 3 W.WR u' v' + pe 2 0 W.WR u' v' + pe 2 1 W.WR u' v'
    WZ := tabulateG D fun u' v' =>
      pe 0 0 W.WZ u' v' + pe 0 1 W.WZ u' v' + pe 1 0 W.WZ u' v' + pe 1 1 W.WZ u' v' -
      pe 3 3 W.WQ u' v' - pe 3 0 W.WR u' v' - pe 3 1 W.WR u' v' }

def dualStep {d : Nat} (A : BinAuto d) (W : DualQRZ) : DualQRZ :=
  dualStepPre (d * d) (buildPreTable A) W

theorem pushEntry_adjoint {d : Nat} (A : BinAuto d) (a b : Fin 4)
    (G : Grid) (X : Fin (d * d) → Fin (d * d) → Int) :
    sumFin (d * d) (fun u' => sumFin (d * d) (fun v' =>
      pushEntry (preimages A) a b G u' v' * X u' v')) =
    sumFin (d * d) (fun u => sumFin (d * d) (fun v =>
      getG G u.1 v.1 * pull A a b X u v)) := by
  have hpe : ∀ u' v' : Fin (d * d),
      pushEntry (preimages A) a b G u' v' =
      sumFin (d * d) (fun u => sumFin (d * d) (fun v =>
        if pairStep A a u = u' ∧ pairStep A b v = v' then
          getG G u.1 v.1 * pairWeight A a u * pairWeight A b v
        else 0)) := by
    intro u' v'
    rw [pushEntry_eq_nested]
    unfold preimages
    rw [sum_map_filterMap_pre (pairStep A a) (pairWeight A a) u'
          (fun u cu => sumPre _ (fun v cv => getG G u.1 v.1 * cu * cv))
          (fun u => by
            rw [sumPre_eq_foldr]
            have h0 : (fun p : Fin (d * d) × Int => getG G u.1 p.1.1 * 0 * p.2) = fun _ => 0 := by
              funext p; simp
            rw [h0]; exact list_map_zero_sum _)]
    apply sumFin_congr; intro u
    by_cases hu : pairStep A a u = u'
    · simp only [hu, true_and, ↓reduceIte]
      rw [sum_map_filterMap_pre (pairStep A b) (pairWeight A b) v'
            (fun v cv => getG G u.1 v.1 * pairWeight A a u * cv)
            (fun v => by simp)]
    · simp only [hu, false_and, ↓reduceIte, sumFin_zero]
  simp only [hpe]
  have hterm : ∀ u v : Fin (d * d),
      getG G u.1 v.1 * pull A a b X u v =
      sumFin (d * d) (fun u' => sumFin (d * d) (fun v' =>
        (if pairStep A a u = u' ∧ pairStep A b v = v' then
          getG G u.1 v.1 * pairWeight A a u * pairWeight A b v
        else 0) * X u' v')) := by
    intro u v
    have hv : ∀ u' : Fin (d * d),
        sumFin (d * d) (fun v' =>
          (if pairStep A a u = u' ∧ pairStep A b v = v' then
            getG G u.1 v.1 * pairWeight A a u * pairWeight A b v
          else 0) * X u' v') =
        if pairStep A a u = u' then
          getG G u.1 v.1 * pairWeight A a u * pairWeight A b v * X u' (pairStep A b v)
        else 0 := by
      intro u'
      by_cases hu : pairStep A a u = u'
      · simp only [hu, true_and, ↓reduceIte]
        have h : (fun v' : Fin (d * d) =>
            (if pairStep A b v = v' then getG G u.1 v.1 * pairWeight A a u * pairWeight A b v else 0) * X u' v') =
            (fun v' => if pairStep A b v = v' then getG G u.1 v.1 * pairWeight A a u * pairWeight A b v * X u' v' else 0) := by
          funext v'; by_cases hv' : pairStep A b v = v' <;> simp [hv']
        rw [h, sumFin_ite_eq]
      · simp only [hu, false_and, ↓reduceIte, Int.zero_mul, sumFin_zero]
    simp only [hv, sumFin_ite_eq]
    unfold pull
    rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
  symm
  calc sumFin (d * d) (fun u => sumFin (d * d) (fun v => getG G u.1 v.1 * pull A a b X u v))
      = sumFin (d * d) (fun u => sumFin (d * d) (fun v => sumFin (d * d) (fun u' => sumFin (d * d) (fun v' =>
          (if pairStep A a u = u' ∧ pairStep A b v = v' then
            getG G u.1 v.1 * pairWeight A a u * pairWeight A b v
          else 0) * X u' v')))) := by
        apply sumFin_congr; intro u; apply sumFin_congr; intro v; exact hterm u v
    _ = sumFin (d * d) (fun u' => sumFin (d * d) (fun v' => sumFin (d * d) (fun u => sumFin (d * d) (fun v =>
          (if pairStep A a u = u' ∧ pairStep A b v = v' then
            getG G u.1 v.1 * pairWeight A a u * pairWeight A b v
          else 0) * X u' v')))) :=
        sumFin4_swap (d * d) _
    _ = sumFin (d * d) (fun u' => sumFin (d * d) (fun v' =>
          (sumFin (d * d) (fun u => sumFin (d * d) (fun v =>
            if pairStep A a u = u' ∧ pairStep A b v = v' then
              getG G u.1 v.1 * pairWeight A a u * pairWeight A b v
            else 0))) * X u' v')) := by
        apply sumFin_congr; intro u'; apply sumFin_congr; intro v'
        rw [← sumFin_mul_right]
        apply sumFin_congr; intro u
        rw [← sumFin_mul_right]

theorem pushEntryT_adjoint {d : Nat} (A : BinAuto d) (a b : Fin 4)
    (G : Grid) (X : Fin (d * d) → Fin (d * d) → Int) :
    sumFin (d * d) (fun u' => sumFin (d * d) (fun v' =>
      pushEntryT (preimages A) a b G u' v' * X u' v')) =
    sumFin (d * d) (fun u => sumFin (d * d) (fun v =>
      getG G u.1 v.1 * pull A b a (fun x y => X y x) u v)) := by
  have htr : ∀ u' v' : Fin (d * d),
      pushEntryT (preimages A) a b G u' v' =
      pushEntry (preimages A) a b (tabulateG (d * d) fun x y => getG G y.1 x.1) u' v' := by
    intro u' v'
    rw [pushEntryT_eq_nested, pushEntry_eq_nested]
    simp only [getG_tabulateG]
  simp only [htr]
  rw [pushEntry_adjoint]
  simp only [getG_tabulateG]
  rw [sumFin_swap (d * d) (d * d)]
  apply sumFin_congr; intro u; apply sumFin_congr; intro v
  unfold pull
  rw [Int.mul_comm (pairWeight A a v) (pairWeight A b u)]

/-- Fast list scaling `c * xs` (zero `getD`, zero `Fin`). -/
def scaleList (c : Int) : List Int → List Int
  | [] => []
  | x :: xs => (c * x) :: scaleList c xs

/-- Fast fused multiply-add `ys + c * xs` (O(1) short-circuit on empty `[]` rows). -/
def addScaledList (c : Int) : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => scaleList c xs
  | x :: xs, y :: ys => (y + c * x) :: addScaledList c xs ys

def addList : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addList xs ys

def subList : List Int → List Int → List Int
  | [], ys => scaleList (-1) ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x - y) :: subList xs ys

/-- Combine rows of `G` weighted by preimage list `lu` ONCE per `u'` (rank-2 factorization!). -/
def rowComb {D : Nat} (lu : List (Fin D × Int)) (G : Grid) : List Int :=
  lu.foldl (fun acc p => addScaledList p.2 (G.getD p.1.1 []) acc) []

/-- Combine columns of `G` weighted by preimage list `lu` ONCE per `u'` (for `Q^T`). -/
def rowCombCol {D : Nat} (lu : List (Fin D × Int)) (G : Grid) : List Int :=
  lu.foldl (fun acc p => addScaledList p.2 (G.map fun r => r.getD p.1.1 0) acc) []

/-- Sparse dot product of a pre-combined row with preimage list `lv` (O(1) on empty). -/
def dotRow {D : Nat} (row : List Int) (lv : List (Fin D × Int)) : Int :=
  match row, lv with
  | [], _ => 0
  | _, [] => 0
  | r, lv => sumPre lv fun v cv => r.getD v.1 0 * cv

/-- Packed per-state preimage triple `(pre0 ++ pre1, pre2, pre3)` for zero-`getD` `List.map` iteration. -/
abbrev PackedPre (D : Nat) := List (List (Fin D × Int) × List (Fin D × Int) × List (Fin D × Int))

def packPreTable {D : Nat} (pt : PreTable D) : PackedPre D :=
  List.ofFn fun u' : Fin D =>
    (getPre pt 0 u' ++ getPre pt 1 u', getPre pt 2 u', getPre pt 3 u')

/-- **Factorized Zero-`getD` `O(D^2)` Adjoint Step (`dualStepFast`):**
    Uses `(P_0 + P_1)` factorization and row-level pre-combination (`rowComb`) so every
    bilinear form `P_a G P_b^T` computes `P_a G` ONCE per row `u'` with zero `getD` on `pt`. -/
def dualStepFast {D : Nat} (pp : PackedPre D) (W : DualQRZ) : DualQRZ :=
  { WQ := pp.map fun (lu01, lu2, lu3) =>
      let r01 := addList (rowComb lu01 W.WQ) (rowComb lu3 W.WR)
      let r2  := addList (rowComb lu2 W.WQ)  (rowComb lu01 W.WR)
      let r3  := rowComb lu3 W.WQ
      match r01, r2, r3 with
      | [], [], [] => []
      | _, _, _ =>
        pp.map fun (lv01, lv2, lv3) =>
          dotRow r01 lv01 + dotRow r2 lv2 + dotRow r3 lv3
    WR := pp.map fun (lu01, lu2, _lu3) =>
      let r3  := addList (addList (rowComb lu2 W.WQ) (rowCombCol lu2 W.WQ)) (rowComb lu01 W.WR)
      let r01 := rowComb lu2 W.WR
      match r3, r01 with
      | [], [] => []
      | _, _ =>
        pp.map fun (lv01, _lv2, lv3) =>
          dotRow r3 lv3 + dotRow r01 lv01
    WZ := pp.map fun (lu01, _lu2, lu3) =>
      let r01 := subList (rowComb lu01 W.WZ) (rowComb lu3 W.WR)
      let r3  := rowComb lu3 W.WQ
      match r01, r3 with
      | [], [] => []
      | _, _ =>
        pp.map fun (lv01, _lv2, lv3) =>
          dotRow r01 lv01 - dotRow r3 lv3 }

theorem scaleList_getD (c : Int) (xs : List Int) (i : Nat) :
    (scaleList c xs).getD i 0 = c * xs.getD i 0 := by
  induction xs generalizing i with
  | nil => simp only [scaleList, List.getD_nil, Int.mul_zero]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [scaleList, List.getD_cons_succ, ih]

theorem addScaledList_getD (c : Int) (xs ys : List Int) (i : Nat) :
    (addScaledList c xs ys).getD i 0 = ys.getD i 0 + c * xs.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp only [addScaledList, List.getD_nil, Int.mul_zero, Int.add_zero]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [addScaledList, List.getD_nil, Int.zero_add, scaleList_getD]
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => simp only [addScaledList, List.getD_cons_succ, ih]

theorem addList_getD (xs ys : List Int) (i : Nat) :
    (addList xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp only [addList, List.getD_nil, Int.zero_add]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [addList, List.getD_nil, Int.add_zero]
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => simp only [addList, List.getD_cons_succ, ih]

theorem subList_getD (xs ys : List Int) (i : Nat) :
    (subList xs ys).getD i 0 = xs.getD i 0 - ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil =>
    simp only [subList, List.getD_nil, scaleList_getD]
    omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [subList, List.getD_nil, Int.sub_zero]
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => simp only [subList, List.getD_cons_succ, ih]

theorem sumPre_append {D : Nat} (l1 l2 : List (Fin D × Int)) (f : Fin D → Int → Int) :
    sumPre (l1 ++ l2) f = sumPre l1 f + sumPre l2 f := by
  simp only [sumPre_eq_foldr, List.map_append, List.sum_append]

theorem sumPre_mul_right {D : Nat} (l : List (Fin D × Int)) (f : Fin D → Int → Int) (c : Int) :
    sumPre l f * c = sumPre l (fun u cu => f u cu * c) := by
  simp only [sumPre_eq_foldr]
  induction l with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, Int.add_mul, ih]

theorem sumPre_add {D : Nat} (l : List (Fin D × Int)) (f g : Fin D → Int → Int) :
    sumPre l (fun u cu => f u cu + g u cu) = sumPre l f + sumPre l g := by
  simp only [sumPre_eq_foldr]
  induction l with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sumPre_sub {D : Nat} (l : List (Fin D × Int)) (f g : Fin D → Int → Int) :
    sumPre l (fun u cu => f u cu - g u cu) = sumPre l f - sumPre l g := by
  simp only [sumPre_eq_foldr]
  induction l with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem map_col_getD (G : Grid) (u v : Nat) :
    (G.map fun r => r.getD u 0).getD v 0 = getG G v u := by
  unfold getG
  induction G generalizing v with
  | nil => simp
  | cons r rs ih =>
    cases v with
    | zero => rfl
    | succ v => simpa only [List.map_cons, List.getD_cons_succ] using ih v

theorem rowComb_getD {D : Nat} (lu : List (Fin D × Int)) (G : Grid) (j : Nat) :
    (rowComb lu G).getD j 0 = sumPre lu (fun u cu => getG G u.1 j * cu) := by
  unfold rowComb sumPre getG
  have hgen : ∀ (acc : List Int) (xs : List (Fin D × Int)),
      (xs.foldl (fun a p => addScaledList p.2 (G.getD p.1.1 []) a) acc).getD j 0 =
      xs.foldl (fun a p => a + (G.getD p.1.1 []).getD j 0 * p.2) (acc.getD j 0) := by
    intro acc xs
    induction xs generalizing acc with
    | nil => rfl
    | cons p xs ih =>
      simp only [List.foldl_cons, ih, addScaledList_getD, Int.mul_comm]
  simpa using hgen [] lu

theorem rowCombCol_getD {D : Nat} (lu : List (Fin D × Int)) (G : Grid) (j : Nat) :
    (rowCombCol lu G).getD j 0 = sumPre lu (fun u cu => getG G j u.1 * cu) := by
  unfold rowCombCol sumPre
  have hgen : ∀ (acc : List Int) (xs : List (Fin D × Int)),
      (xs.foldl (fun a p => addScaledList p.2 (G.map fun r => r.getD p.1.1 0) a) acc).getD j 0 =
      xs.foldl (fun a p => a + getG G j p.1.1 * p.2) (acc.getD j 0) := by
    intro acc xs
    induction xs generalizing acc with
    | nil => rfl
    | cons p xs ih =>
      simp only [List.foldl_cons, ih, addScaledList_getD, map_col_getD, Int.mul_comm]
  simpa using hgen [] lu

theorem dotRow_eq {D : Nat} (row : List Int) (lv : List (Fin D × Int)) :
    dotRow row lv = sumPre lv (fun v cv => row.getD v.1 0 * cv) := by
  unfold dotRow
  cases row with
  | nil =>
    rw [sumPre_eq_foldr]
    have h0 : (fun p : Fin D × Int => (([] : List Int).getD p.1.1 0) * p.2) = fun _ => 0 := by
      funext p; simp
    rw [h0]; exact (list_map_zero_sum lv).symm
  | cons _ _ =>
    cases lv <;> rfl

theorem dotRow_addList {D : Nat} (r1 r2 : List Int) (lv : List (Fin D × Int)) :
    dotRow (addList r1 r2) lv = dotRow r1 lv + dotRow r2 lv := by
  simp only [dotRow_eq, addList_getD, Int.add_mul, sumPre_add]

theorem dotRow_subList {D : Nat} (r1 r2 : List Int) (lv : List (Fin D × Int)) :
    dotRow (subList r1 r2) lv = dotRow r1 lv - dotRow r2 lv := by
  simp only [dotRow_eq, subList_getD, Int.sub_mul, sumPre_sub]

theorem dotRow_rowComb {D : Nat} (lu lv : List (Fin D × Int)) (G : Grid) :
    dotRow (rowComb lu G) lv =
    sumPre lu (fun u cu => sumPre lv (fun v cv => getG G u.1 v.1 * cu * cv)) := by
  rw [dotRow_eq]
  have h1 : (fun (v : Fin D) (cv : Int) => (rowComb lu G).getD v.1 0 * cv) =
      (fun (v : Fin D) (cv : Int) => sumPre lu (fun u cu => getG G u.1 v.1 * cu * cv)) := by
    funext v cv
    rw [rowComb_getD, sumPre_mul_right]
  rw [h1, sumPre_swap]

theorem dotRow_rowCombCol {D : Nat} (lu lv : List (Fin D × Int)) (G : Grid) :
    dotRow (rowCombCol lu G) lv =
    sumPre lu (fun u cu => sumPre lv (fun v cv => getG G v.1 u.1 * cu * cv)) := by
  rw [dotRow_eq]
  have h1 : (fun (v : Fin D) (cv : Int) => (rowCombCol lu G).getD v.1 0 * cv) =
      (fun (v : Fin D) (cv : Int) => sumPre lu (fun u cu => getG G v.1 u.1 * cu * cv)) := by
    funext v cv
    rw [rowCombCol_getD, sumPre_mul_right]
  rw [h1, sumPre_swap]

theorem list_map_ofFn_getD {D : Nat} {α β : Type} (g : Fin D → α) (f : α → β) (d0 : β) (i : Fin D) :
    ((List.ofFn g).map f).getD i.1 d0 = f (g i) := by
  rw [List.map_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.2]

theorem empty_row_match3_getD {D : Nat} {α : Type} (g : Fin D → α) (r1 r2 r3 : List Int)
    (f : α → Int) (h0 : r1 = [] → r2 = [] → r3 = [] → ∀ x, f x = 0) (j : Fin D) :
    ((match r1, r2, r3 with | [], [], [] => [] | _, _, _ => (List.ofFn g).map f)).getD j.1 0 = f (g j) := by
  cases r1 with
  | nil =>
    cases r2 with
    | nil =>
      cases r3 with
      | nil => simpa using (h0 rfl rfl rfl (g j)).symm
      | cons _ _ => exact list_map_ofFn_getD g f 0 j
    | cons _ _ => exact list_map_ofFn_getD g f 0 j
  | cons _ _ => exact list_map_ofFn_getD g f 0 j

theorem empty_row_match2_getD {D : Nat} {α : Type} (g : Fin D → α) (r1 r2 : List Int)
    (f : α → Int) (h0 : r1 = [] → r2 = [] → ∀ x, f x = 0) (j : Fin D) :
    ((match r1, r2 with | [], [] => [] | _, _ => (List.ofFn g).map f)).getD j.1 0 = f (g j) := by
  cases r1 with
  | nil =>
    cases r2 with
    | nil => simpa using (h0 rfl rfl (g j)).symm
    | cons _ _ => exact list_map_ofFn_getD g f 0 j
  | cons _ _ => exact list_map_ofFn_getD g f 0 j

theorem getG_dualStepFast {D : Nat} (pt : PreTable D) (W : DualQRZ) (u' v' : Fin D) :
    getG (dualStepFast (packPreTable pt) W).WQ u'.1 v'.1 = getG (dualStepPre D pt W).WQ u'.1 v'.1 ∧
    getG (dualStepFast (packPreTable pt) W).WR u'.1 v'.1 = getG (dualStepPre D pt W).WR u'.1 v'.1 ∧
    getG (dualStepFast (packPreTable pt) W).WZ u'.1 v'.1 = getG (dualStepPre D pt W).WZ u'.1 v'.1 := by
  let g : Fin D → List (Fin D × Int) × List (Fin D × Int) × List (Fin D × Int) :=
    fun x => (getPre pt 0 x ++ getPre pt 1 x, getPre pt 2 x, getPre pt 3 x)
  have hpe : ∀ (a b : Fin 4) (G : Grid),
      pushEntry (getPre pt) a b G u' v' =
      dotRow (rowComb (getPre pt a u') G) (getPre pt b v') := by
    intro a b G; rw [pushEntry_eq_nested, dotRow_rowComb]
  have hpet : ∀ (a b : Fin 4) (G : Grid),
      pushEntryT (getPre pt) a b G u' v' =
      dotRow (rowCombCol (getPre pt a u') G) (getPre pt b v') := by
    intro a b G; rw [pushEntryT_eq_nested, dotRow_rowCombCol]
  have hrc_app : ∀ (l1 l2 lv : List (Fin D × Int)) (G : Grid),
      dotRow (rowComb (l1 ++ l2) G) lv = dotRow (rowComb l1 G) lv + dotRow (rowComb l2 G) lv := by
    intro l1 l2 lv G; simp only [dotRow_rowComb, sumPre_append]
  have hdr_app : ∀ (r : List Int) (l1 l2 : List (Fin D × Int)),
      dotRow r (l1 ++ l2) = dotRow r l1 + dotRow r l2 := by
    intro r l1 l2; simp only [dotRow_eq, sumPre_append]
  refine ⟨?_, ?_, ?_⟩
  · simp only [dualStepFast, dualStepPre, getG_tabulateG]
    unfold getG packPreTable
    rw [list_map_ofFn_getD g _ [] u']
    rw [empty_row_match3_getD g _ _ _ _ (fun h1 h2 h3 _ => by simp [h1, h2, h3, dotRow]) v']
    simp only [g, dotRow_addList, hdr_app, hrc_app, hpe]
    omega
  · simp only [dualStepFast, dualStepPre, getG_tabulateG]
    unfold getG packPreTable
    rw [list_map_ofFn_getD g _ [] u']
    rw [empty_row_match2_getD g _ _ _ (fun h1 h2 _ => by simp [h1, h2, dotRow]) v']
    simp only [g, dotRow_addList, hdr_app, hrc_app, hpe, hpet]
    omega
  · simp only [dualStepFast, dualStepPre, getG_tabulateG]
    unfold getG packPreTable
    rw [list_map_ofFn_getD g _ [] u']
    rw [empty_row_match2_getD g _ _ _ (fun h1 h2 _ => by simp [h1, h2, dotRow]) v']
    simp only [g, dotRow_subList, hdr_app, hrc_app, hpe]
    omega

/-- Iterate `dualStepFast` `n` times using a precomputed `PackedPre`. -/
def dualIterPre (D : Nat) (pp : PackedPre D) (W : DualQRZ) : Nat → DualQRZ
  | 0 => W
  | n + 1 => dualStepFast pp (dualIterPre D pp W n)

def dualIter {d : Nat} (A : BinAuto d) (W : DualQRZ) (n : Nat) : DualQRZ :=
  dualIterPre (d * d) (packPreTable (buildPreTable A)) W n

theorem dualIter_succ {d : Nat} (A : BinAuto d) (W : DualQRZ) (n : Nat) :
    dualIter A W (n + 1) = dualStepFast (packPreTable (buildPreTable A)) (dualIter A W n) := rfl

/-- Build `[W, T* W, ..., (T*)^N W]` using a single precomputed `PackedPre`! -/
def dualOrbitPre (D : Nat) (pp : PackedPre D) (W : DualQRZ) : Nat → List DualQRZ
  | 0 => [W]
  | n + 1 => W :: dualOrbitPre D pp (dualStepFast pp W) n

theorem dualIterPre_shift (D : Nat) (pp : PackedPre D) (W : DualQRZ) (j : Nat) :
    dualIterPre D pp (dualStepFast pp W) j = dualIterPre D pp W (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [dualIterPre, ih]

theorem dualOrbitPre_len (D : Nat) (pp : PackedPre D) (W : DualQRZ) (N : Nat) :
    (dualOrbitPre D pp W N).length = N + 1 := by
  induction N generalizing W with
  | zero => rfl
  | succ N ih => simp [dualOrbitPre, ih]

theorem dualOrbitPre_getD (D : Nat) (pp : PackedPre D) (W : DualQRZ) (N j : Nat) (hj : j ≤ N) :
    (dualOrbitPre D pp W N).getD j W = dualIterPre D pp W j := by
  induction N generalizing W j with
  | zero =>
    have : j = 0 := by omega
    subst this; rfl
  | succ N ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [dualOrbitPre, List.getD_cons_succ]
      have h1 := ih (dualStepFast pp W) j (by omega)
      have hlt : j < (dualOrbitPre D pp (dualStepFast pp W) N).length := by
        rw [dualOrbitPre_len]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at h1
      rw [h1, dualIterPre_shift]

/-- Pure-data Dual-Krylov recurrence certificate:
    `(k0, coeffs)` certifies that `W^{(k0 + r)} = ∑_{j=0}^{r-1} coeffs[j] * W^{(k0 + j)}`
    where `r = coeffs.length`. -/
structure DualCert where
  k0 : Nat
  coeffs : List Int

/-- Compute linear combination `∑_{j=0}^{r-1} c_j * getG (grids[j]) u v`. -/
def linCombGrid (coeffs : List Int) (grids : List Grid) (u v : Nat) : Int :=
  match coeffs, grids with
  | c :: cs, g :: gs => c * getG g u v + linCombGrid cs gs u v
  | _, _ => 0

/-- Pure-data Boolean certificate checker (checked by kernel `decide`, zero `Prop` fields!). -/
def checkDualCert {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (cert : DualCert) : Bool :=
  let D := d * d
  let r := cert.coeffs.length
  let pp := packPreTable (buildPreTable A)
  let orbit := dualOrbitPre D pp W0 (cert.k0 + r)
  let target := orbit.getD (cert.k0 + r) W0
  let window := (orbit.drop cert.k0).take r
  let gQ := window.map (·.WQ)
  let gR := window.map (·.WR)
  let gZ := window.map (·.WZ)
  (List.finRange D).all fun u =>
    (List.finRange D).all fun v =>
      (getG target.WQ u.1 v.1 == linCombGrid cert.coeffs gQ u.1 v.1) &&
      (getG target.WR u.1 v.1 == linCombGrid cert.coeffs gR u.1 v.1) &&
      (getG target.WZ u.1 v.1 == linCombGrid cert.coeffs gZ u.1 v.1)

/-- Linear combination of scalar sequence `f (start + j)` weighted by `coeffs`. -/
def evalRecurrence (coeffs : List Int) (f : Nat → Int) (start : Nat) : Int :=
  match coeffs with
  | [] => 0
  | c :: cs => c * f start + evalRecurrence cs f (start + 1)

theorem linCombGrid_inner (D : Nat) (coeffs : List Int) (ws : List DualQRZ)
    (proj : DualQRZ → Grid) (X : Fin D → Fin D → Int)
    (hlen : ws.length = coeffs.length) :
    sumFin D (fun u => sumFin D (fun v =>
      linCombGrid coeffs (ws.map proj) u.1 v.1 * X u v)) =
    (List.zipWith (fun c w => c * innerGrid D (proj w) X) coeffs ws).sum := by
  induction coeffs generalizing ws with
  | nil =>
    cases ws with
    | nil => simp [linCombGrid, sumFin_zero]
    | cons _ _ => simp at hlen
  | cons c cs ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [List.map_cons, linCombGrid, List.zipWith_cons_cons, List.sum_cons]
      have hsplit :
          sumFin D (fun u => sumFin D (fun v =>
            (c * getG (proj w) u.1 v.1 + linCombGrid cs (ws.map proj) u.1 v.1) * X u v)) =
          c * innerGrid D (proj w) X +
          sumFin D (fun u => sumFin D (fun v =>
            linCombGrid cs (ws.map proj) u.1 v.1 * X u v)) := by
        unfold innerGrid
        rw [← sumFin_mul_left, ← sumFin_add]
        apply sumFin_congr; intro u
        rw [← sumFin_mul_left, ← sumFin_add]
        apply sumFin_congr; intro v
        rw [Int.add_mul, Int.mul_assoc]
      rw [hsplit, ih ws (by simp at hlen; exact hlen)]

theorem zipWith_evalRec (coeffs : List Int) (start : Nat) (ws : List DualQRZ)
    (g : DualQRZ → Int) (f : Nat → Int)
    (hlen : ws.length = coeffs.length)
    (hmatch : ∀ j (hj : j < ws.length), g (ws[j]) = f (start + j)) :
    (List.zipWith (fun c w => c * g w) coeffs ws).sum = evalRecurrence coeffs f start := by
  induction coeffs generalizing ws start with
  | nil =>
    cases ws with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons c cs ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [List.zipWith_cons_cons, List.sum_cons, evalRecurrence]
      have h0 : g w = f start := by
        have hm := hmatch 0 (by simp)
        simpa using hm
      rw [h0]
      congr 1
      apply ih (start + 1) ws (by simp at hlen; exact hlen)
      intro j hj
      have h1 := hmatch (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at h1
      rw [h1]; congr 1; omega

/-- Pure-data Step-Witnessed Dual-Krylov Certificate (zero `Prop` fields!).
    Carries the materialized orbit `[W_0, W_1, ..., W_{k0 + r}]` so that Lean's kernel checks
    each transition `dualStepFast pp W_i == W_{i+1}` at **Depth 1** in linear time `O((k0 + r) * D^2)`. -/
structure WitnessedDualCert where
  k0 : Nat
  coeffs : List Int
  orbit : List DualQRZ

def eqDualQRZ (D : Nat) (W1 W2 : DualQRZ) : Bool :=
  (List.finRange D).all fun u =>
    (List.finRange D).all fun v =>
      (getG W1.WQ u.1 v.1 == getG W2.WQ u.1 v.1) &&
      (getG W1.WR u.1 v.1 == getG W2.WR u.1 v.1) &&
      (getG W1.WZ u.1 v.1 == getG W2.WZ u.1 v.1)

def checkOrbitSteps {D : Nat} (pp : PackedPre D) : List DualQRZ → Bool
  | [] => true
  | [_] => true
  | w1 :: w2 :: rest =>
    eqDualQRZ D (dualStepFast pp w1) w2 && checkOrbitSteps pp (w2 :: rest)

def checkWitnessedOrbit {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (orbit : List DualQRZ) : Bool :=
  let D := d * d
  match orbit with
  | [] => false
  | w0 :: _ =>
    eqDualQRZ D w0 W0 && checkOrbitSteps (packPreTable (buildPreTable A)) orbit

def checkWitnessedDualCert {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (cert : WitnessedDualCert) : Bool :=
  let D := d * d
  let r := cert.coeffs.length
  (cert.orbit.length == cert.k0 + r + 1) &&
  checkWitnessedOrbit A W0 cert.orbit &&
  (let target := cert.orbit.getD (cert.k0 + r) W0
   let window := (cert.orbit.drop cert.k0).take r
   let gQ := window.map (·.WQ)
   let gR := window.map (·.WR)
   let gZ := window.map (·.WZ)
   (List.finRange D).all fun u =>
     (List.finRange D).all fun v =>
       (getG target.WQ u.1 v.1 == linCombGrid cert.coeffs gQ u.1 v.1) &&
       (getG target.WR u.1 v.1 == linCombGrid cert.coeffs gR u.1 v.1) &&
       (getG target.WZ u.1 v.1 == linCombGrid cert.coeffs gZ u.1 v.1))

theorem eqDualQRZ_inner (D : Nat) (W1 W2 : DualQRZ) (S : QRZFn D)
    (heq : eqDualQRZ D W1 W2 = true) :
    innerQRZ D W1 S = innerQRZ D W2 S := by
  unfold eqDualQRZ at heq
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at heq
  unfold innerQRZ innerGrid
  congr 1; congr 1
  · apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(heq u (List.mem_finRange u) v (List.mem_finRange v)).1.1]
  · apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(heq u (List.mem_finRange u) v (List.mem_finRange v)).1.2]
  · apply sumFin_congr; intro u; apply sumFin_congr; intro v
    rw [(heq u (List.mem_finRange u) v (List.mem_finRange v)).2]

theorem checkOrbitSteps_step {D : Nat} (pp : PackedPre D) (orbit : List DualQRZ)
    (hok : checkOrbitSteps pp orbit = true) (j : Nat) (hj : j + 1 < orbit.length) :
    eqDualQRZ D (dualStepFast pp orbit[j]) orbit[j + 1] = true := by
  induction orbit generalizing j with
  | nil => simp at hj
  | cons w1 rest ih =>
    cases rest with
    | nil => simp at hj
    | cons w2 rest' =>
      simp only [checkOrbitSteps, Bool.and_eq_true] at hok
      cases j with
      | zero => exact hok.1
      | succ j' =>
        simp only [List.getElem_cons_succ]
        exact ih hok.2 j' (by simp only [List.length_cons] at hj ⊢; omega)

/-- Dual functional extracting `E4State A 0 k = 2 * Q_{0,0}(k) - Z_{0,0}(k)`. -/
def dualE4State0 (d : Nat) : DualQRZ where
  WQ := tabulateG (d * d) fun u v => if u.1 = 0 ∧ v.1 = 0 then 2 else 0
  WR := tabulateG (d * d) fun _ _ => 0
  WZ := tabulateG (d * d) fun u v => if u.1 = 0 ∧ v.1 = 0 then -1 else 0

theorem innerQRZ_dualE4State0 {d : Nat} (A : BinAuto (d + 1)) (k : Nat) :
    innerQRZ ((d + 1) * (d + 1)) (dualE4State0 (d + 1)) (qrzAt A k) = E4State A 0 k := by
  have hD : 0 < (d + 1) * (d + 1) := Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos d)
  let z0 : Fin ((d + 1) * (d + 1)) := ⟨0, hD⟩
  have hpair0 : pairIdx (0 : Fin (d + 1)) 0 = z0 := by
    apply Fin.ext; simp [pairIdx, z0]
  rw [E4State_eq_qrz, hpair0]
  unfold innerQRZ innerGrid dualE4State0
  simp only [getG_tabulateG]
  have hQ : sumFin ((d + 1) * (d + 1)) (fun u => sumFin ((d + 1) * (d + 1)) (fun v =>
      (if u.1 = 0 ∧ v.1 = 0 then (2 : Int) else 0) * (qrzAt A k).Q u v)) = 2 * (qrzAt A k).Q z0 z0 := by
    have hv : ∀ u : Fin ((d + 1) * (d + 1)),
        sumFin ((d + 1) * (d + 1)) (fun v => (if u.1 = 0 ∧ v.1 = 0 then (2 : Int) else 0) * (qrzAt A k).Q u v) =
        if u = z0 then 2 * (qrzAt A k).Q u z0 else 0 := by
      intro u
      by_cases hu : u = z0
      · subst hu
        have h : (fun v : Fin ((d + 1) * (d + 1)) => (if z0.1 = 0 ∧ v.1 = 0 then (2 : Int) else 0) * (qrzAt A k).Q z0 v) =
            (fun v => if v = z0 then 2 * (qrzAt A k).Q z0 v else 0) := by
          funext v; by_cases hv' : v = z0
          · subst hv'; simp [z0]
          · have hne : v.1 ≠ 0 := by intro h0; apply hv'; exact Fin.ext h0
            simp only [hv', hne, and_false, ↓reduceIte, Int.zero_mul]
        rw [h, sumFin_ite_eq']
        simp
      · have hne : u.1 ≠ 0 := by intro h0; apply hu; exact Fin.ext h0
        simp [hu, hne, sumFin_zero]
    simp only [hv, sumFin_ite_eq']
  have hR : sumFin ((d + 1) * (d + 1)) (fun u => sumFin ((d + 1) * (d + 1)) (fun v => (0 : Int) * (qrzAt A k).R u v)) = 0 := by
    simp [sumFin_zero]
  have hZ : sumFin ((d + 1) * (d + 1)) (fun u => sumFin ((d + 1) * (d + 1)) (fun v =>
      (if u.1 = 0 ∧ v.1 = 0 then (-1 : Int) else 0) * (qrzAt A k).Z u v)) = -(qrzAt A k).Z z0 z0 := by
    have hv : ∀ u : Fin ((d + 1) * (d + 1)),
        sumFin ((d + 1) * (d + 1)) (fun v => (if u.1 = 0 ∧ v.1 = 0 then (-1 : Int) else 0) * (qrzAt A k).Z u v) =
        if u = z0 then -(qrzAt A k).Z u z0 else 0 := by
      intro u
      by_cases hu : u = z0
      · subst hu
        have h : (fun v : Fin ((d + 1) * (d + 1)) => (if z0.1 = 0 ∧ v.1 = 0 then (-1 : Int) else 0) * (qrzAt A k).Z z0 v) =
            (fun v => if v = z0 then -(qrzAt A k).Z z0 v else 0) := by
          funext v; by_cases hv' : v = z0
          · subst hv'; simp [z0]
          · have hne : v.1 ≠ 0 := by intro h0; apply hv'; exact Fin.ext h0
            simp only [hv', hne, and_false, ↓reduceIte, Int.zero_mul]
        rw [h, sumFin_ite_eq']
        simp
      · have hne : u.1 ≠ 0 := by intro h0; apply hu; exact Fin.ext h0
        simp [hu, hne, sumFin_zero]
    simp only [hv, sumFin_ite_eq']
  rw [hQ, hR, hZ]
  dsimp [qrzAt]
  omega

/-- Dual functional extracting total `L^4` energy `totE4 A k = ∑_q E4State A q k`. -/
def dualTotE4 (d : Nat) : DualQRZ where
  WQ := tabulateG (d * d) fun u v =>
    if u.1 = v.1 ∧ u.1 / d = u.1 % d then 2 else 0
  WR := tabulateG (d * d) fun _ _ => 0
  WZ := tabulateG (d * d) fun u v =>
    if u.1 = v.1 ∧ u.1 / d = u.1 % d then -1 else 0

theorem innerQRZ_dualTotE4 {d : Nat} (A : BinAuto d) (k : Nat) :
    innerQRZ (d * d) (dualTotE4 d) (qrzAt A k) = totE4 A k := by
  unfold totE4
  simp only [E4State_eq_qrz]
  have hdiag_sum : ∀ (c : Int) (X : Fin (d * d) → Fin (d * d) → Int),
      sumFin (d * d) (fun u => sumFin (d * d) (fun v =>
        (if u.1 = v.1 ∧ u.1 / d = u.1 % d then c else 0) * X u v)) =
      sumFin d (fun q => c * X (pairIdx q q) (pairIdx q q)) := by
    intro c X
    have hv : ∀ u : Fin (d * d),
        sumFin (d * d) (fun v => (if u.1 = v.1 ∧ u.1 / d = u.1 % d then c else 0) * X u v) =
        if u.1 / d = u.1 % d then c * X u u else 0 := by
      intro u
      by_cases hu : u.1 / d = u.1 % d
      · simp only [hu, and_true, ↓reduceIte]
        have h : (fun v : Fin (d * d) => (if u.1 = v.1 then c else 0) * X u v) =
            (fun v => if u = v then c * X u v else 0) := by
          funext v; by_cases heq : u = v
          · subst heq; simp
          · have hne : u.1 ≠ v.1 := by intro h1; apply heq; exact Fin.ext h1
            simp [heq, hne]
        rw [h, sumFin_ite_eq]
      · simp [hu, sumFin_zero]
    simp only [hv]
    rw [sumFin_mul_split]
    apply sumFin_congr; intro p
    have hp : (fun q : Fin d => if (pairIdx p q).1 / d = (pairIdx p q).1 % d then
        c * X (pairIdx p q) (pairIdx p q) else 0) =
        (fun q => if p = q then c * X (pairIdx p q) (pairIdx p q) else 0) := by
      funext q
      have ⟨h1, h2⟩ := pairIdx_div_mod p q
      rw [h1, h2]
      by_cases heq : p = q
      · subst heq; simp
      · have hne : p.1 ≠ q.1 := by intro h; apply heq; exact Fin.ext h
        simp [heq, hne]
    rw [hp, sumFin_ite_eq]
  unfold innerQRZ innerGrid dualTotE4
  simp only [getG_tabulateG, Int.zero_mul, sumFin_zero, Int.add_zero]
  rw [hdiag_sum 2 (qrzAt A k).Q, hdiag_sum (-1) (qrzAt A k).Z, ← sumFin_add]
  apply sumFin_congr; intro q
  dsimp [qrzAt]
  omega

/-- Single-pass evaluation of `[⟨W0, qrzAt A 0⟩, ..., ⟨W0, qrzAt A N⟩]`. -/
def evalOrbitAtZero {d : Nat} (A : BinAuto d) (W0 : DualQRZ) (N : Nat) : List Int :=
  (dualOrbitPre (d * d) (packPreTable (buildPreTable A)) W0 N).map (evalDualAtZero A)

/-- Regular paperfolding automaton `g(n) = p(n+1)` on 3 states:
    `q0 = g(n)`, `q1 = (-1)^n`, `q2 = 1`. -/
def paperfoldingAuto : BinAuto 3 where
  del0 := fun q => match q.1 with | 0 => ⟨1, by omega⟩ | _ => ⟨2, by omega⟩
  del1 := fun q => match q.1 with | 0 => ⟨0, by omega⟩ | _ => ⟨2, by omega⟩
  sig0 := fun _ => 1
  sig1 := fun q => if q.1 = 1 then -1 else 1
  init := fun _ => 1
  zero_ok := fun _ => rfl

def pfCert : DualCert := ⟨3, [-192, 568, -660, 386, -119, 18]⟩

set_option maxRecDepth 4096 in
/-- Kernel-checked Dual-Krylov certificate for Paperfolding (zero `native_decide`!). -/
theorem pfCert_valid : checkDualCert paperfoldingAuto (dualE4State0 3) pfCert = true := by
  decide

set_option maxRecDepth 4096 in
/-- Kernel-checked negative mutation test: perturbing the leading coefficient is rejected! -/
theorem pfCert_mutated_rejected :
    checkDualCert paperfoldingAuto (dualE4State0 3) ⟨3, [-192, 568, -660, 386, -119, 19]⟩ = false := by
  decide

/-- Exact Paperfolding closed-form RHS: `2 * 8^k + (63*k^2 - 693*k + 2317) * 2^k - 4440`. -/
def pfFormula (k : Nat) : Int :=
  2 * (8 : Int) ^ k + (63 * (k : Int) * (k : Int) - 693 * (k : Int) + 2317) * (2 : Int) ^ k - 4440

set_option maxRecDepth 4096 in
/-- Single-pass base table for Paperfolding `E4(0..8)` (computed once in 8 steps instead of 36!). -/
theorem pf_base_orbit :
    evalOrbitAtZero paperfoldingAuto (dualE4State0 3) 8 =
      [1, 6, 20, 144, 600, 3560, 26056, 202888, 1607432] := by
  decide

/-- Minimal 2-state Baum-Sweet automaton (`sig1[1] = 0` eliminates the dead state):
    `q0 = b(n)`, `q1 = b(2n)`. -/
def baumSweetAuto : BinAuto 2 where
  del0 := fun q => if q.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  del1 := fun _ => ⟨0, by omega⟩
  sig0 := fun _ => 1
  sig1 := fun q => if q.1 = 0 then 1 else 0
  init := fun _ => 1
  zero_ok := fun _ => rfl

def bsCert : DualCert := ⟨0, [2, -2, -5, 5, 8, 1]⟩

theorem bsCert_valid : checkDualCert baumSweetAuto (dualE4State0 2) bsCert = true := by
  decide

theorem bsCert_mutated_rejected :
    checkDualCert baumSweetAuto (dualE4State0 2) ⟨0, [2, -2, -5, 5, 8, 2]⟩ = false := by
  decide

/-- `L = 3` bijective-tail automaton `mask = 6` (`101 ^ 110`): `ψ(0) = false, ψ(1) = true`. -/
def mask6Auto : BinAuto 4 := bijTailAuto 1 (fun r => r.1 == 1)

/-- `L = 3` bijective-tail automaton `mask = 9` (`100 ^ 111`): `ψ(0) = true, ψ(1) = false`. -/
def mask9Auto : BinAuto 4 := bijTailAuto 1 (fun r => r.1 == 0)

def mask6TotOrbit : List DualQRZ := [
  ⟨[[2], [], [], [], [], [0, 0, 0, 0, 0, 2], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
   [],
   [[-1], [], [], [], [], [0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]⟩,
  ⟨[[4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [0, 0, 4], [], [], [0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 4], [], [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 8], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]],
   [[-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], [], [], [], [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -4], [], [-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [], [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]]⟩,
  ⟨[[8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8], [0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [0, 0, 8, 0, 0, 0, 0, -8], [0, 0, 0, 8], [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 8], [0, 0, -8, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, -8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8], [0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 8], [0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, -16], [0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 16]],
   [[-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4], [], [], [], [0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, -8], [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4]]⟩,
  ⟨[[48, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16, 0, 0, 0, 0, 48], [0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 48], [0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [16, 0, 0, 0, 0, 48, 0, 0, 0, 0, 48, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 48], [0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 48], [16, 0, 0, 0, 0, 48, 0, 0, 0, 0, 48, 0, 0, 0, 0, 16], [0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48], [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [48, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16, 0, 0, 0, 0, 48]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, -32, 0, 0, 0, 0, -32], [0, 0, 0, 0, 0, 0, 0, 0, 0, -32], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -32], [0, 0, 0, 0, 0, 0, 0, 0, -32, 0, 0, 0, 0, -32]],
   [[-24, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, -24], [], [], [], [0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [-8, 0, 0, 0, 0, -24, 0, 0, 0, 0, -24, 0, 0, 0, 0, -8], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, -16], [0, 0, 0, 0, 0, 0, 0, 0, 0, -48], [-8, 0, 0, 0, 0, -24, 0, 0, 0, 0, -24, 0, 0, 0, 0, -8], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -48], [0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, -16], [0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [-24, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, -24]]⟩,
  ⟨[[160, 0, 0, 0, 0, 160, 0, 0, 0, 0, 96, 0, 0, 0, 0, 96], [0, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32], [0, 0, 96, 0, 0, 0, 0, 32], [0, 0, 0, 96], [0, 0, 0, 0, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32], [160, 0, 0, 0, 0, 160, 0, 0, 0, 0, 96, 0, 0, 0, 0, 96], [0, 0, 0, 0, 0, 0, 96], [0, 0, 32, 0, 0, 0, 0, 96], [0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 32], [0, 0, 0, 0, 0, 0, 0, 0, 0, 96], [96, 0, 0, 0, 0, 96, 0, 0, 0, 0, 160, 0, 0, 0, 0, 160], [0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96], [0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 96], [0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160], [96, 0, 0, 0, 0, 96, 0, 0, 0, 0, 160, 0, 0, 0, 0, 160]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 192], [0, 0, 0, 0, 0, 0, 0, 0, 0, 192], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 192], [0, 0, 0, 0, 0, 0, 0, 0, 192, 0, 0, 0, 0, 64]],
   [[-80, 0, 0, 0, 0, -80, 0, 0, 0, 0, -48, 0, 0, 0, 0, -48], [], [], [], [0, 0, 0, 0, -160, 0, 0, 0, 0, 0, 0, 0, 0, 0, -32], [-80, 0, 0, 0, 0, -80, 0, 0, 0, 0, -48, 0, 0, 0, 0, -48], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -96, 0, 0, 0, 0, -32], [0, 0, 0, 0, 0, 0, 0, 0, 0, -96], [-48, 0, 0, 0, 0, -48, 0, 0, 0, 0, -80, 0, 0, 0, 0, -80], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -96], [0, 0, 0, 0, 0, 0, 0, 0, -32, 0, 0, 0, 0, -96], [0, 0, 0, 0, -32, 0, 0, 0, 0, 0, 0, 0, 0, 0, -160], [-48, 0, 0, 0, 0, -48, 0, 0, 0, 0, -80, 0, 0, 0, 0, -80]]⟩,
  ⟨[[960, 0, 0, 0, 0, 448, 0, 0, 0, 0, 320, 0, 0, 0, 0, 320], [0, 448, 0, 0, 0, 0, 0, 0, 0, 0, 0, -64], [0, 0, 320, 0, 0, 0, 0, -64], [0, 0, 0, 320], [0, 0, 0, 0, 448, 0, 0, 0, 0, 0, 0, 0, 0, 0, -64], [448, 0, 0, 0, 0, 960, 0, 0, 0, 0, 320, 0, 0, 0, 0, 320], [0, 0, 0, 0, 0, 0, 320], [0, 0, -64, 0, 0, 0, 0, 320], [0, 0, 0, 0, 0, 0, 0, 0, 320, 0, 0, 0, 0, -64], [0, 0, 0, 0, 0, 0, 0, 0, 0, 320], [320, 0, 0, 0, 0, 320, 0, 0, 0, 0, 960, 0, 0, 0, 0, 448], [0, -64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 448], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 320], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 0, 0, 0, 320], [0, 0, 0, 0, -64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 448], [320, 0, 0, 0, 0, 320, 0, 0, 0, 0, 448, 0, 0, 0, 0, 960]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, -640, 0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, -640]],
   [[-480, 0, 0, 0, 0, -224, 0, 0, 0, 0, -160, 0, 0, 0, 0, -160], [], [], [], [0, 0, 0, 0, -448, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64], [-224, 0, 0, 0, 0, -480, 0, 0, 0, 0, -160, 0, 0, 0, 0, -160], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -320, 0, 0, 0, 0, 64], [0, 0, 0, 0, 0, 0, 0, 0, 0, -320], [-160, 0, 0, 0, 0, -160, 0, 0, 0, 0, -480, 0, 0, 0, 0, -224], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -320], [0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, -320], [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, -448], [-160, 0, 0, 0, 0, -160, 0, 0, 0, 0, -224, 0, 0, 0, 0, -480]]⟩,
  ⟨[[3712, 0, 0, 0, 0, 1152, 0, 0, 0, 0, 1920, 0, 0, 0, 0, 1408], [0, 1152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [0, 0, 1920, 0, 0, 0, 0, 128], [0, 0, 0, 1408], [0, 0, 0, 0, 1152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [1152, 0, 0, 0, 0, 3712, 0, 0, 0, 0, 1408, 0, 0, 0, 0, 1920], [0, 0, 0, 0, 0, 0, 1408], [0, 0, 128, 0, 0, 0, 0, 1920], [0, 0, 0, 0, 0, 0, 0, 0, 1920, 0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1408], [1920, 0, 0, 0, 0, 1408, 0, 0, 0, 0, 3712, 0, 0, 0, 0, 1152], [0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1152], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1408], [0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 1920], [0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1152], [1408, 0, 0, 0, 0, 1920, 0, 0, 0, 0, 1152, 0, 0, 0, 0, 3712]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0, -256], [0, 0, 0, 0, 0, 0, 0, 0, 0, -256], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256], [0, 0, 0, 0, 0, 0, 0, 0, -256, 0, 0, 0, 0, 256]],
   [[-1856, 0, 0, 0, 0, -576, 0, 0, 0, 0, -960, 0, 0, 0, 0, -704], [], [], [], [0, 0, 0, 0, -1152, 0, 0, 0, 0, 0, 0, 0, 0, 0, -128], [-576, 0, 0, 0, 0, -1856, 0, 0, 0, 0, -704, 0, 0, 0, 0, -960], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -1920, 0, 0, 0, 0, -128], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1408], [-960, 0, 0, 0, 0, -704, 0, 0, 0, 0, -1856, 0, 0, 0, 0, -576], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1408], [0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 0, 0, 0, -1920], [0, 0, 0, 0, -128, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1152], [-704, 0, 0, 0, 0, -960, 0, 0, 0, 0, -576, 0, 0, 0, 0, -1856]]⟩
]

def mask9TotOrbit : List DualQRZ := [
  ⟨[[2], [], [], [], [], [0, 0, 0, 0, 0, 2], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
   [],
   [[-1], [], [], [], [], [0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]⟩,
  ⟨[[4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [0, 0, 4], [], [], [0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 4], [], [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [], [0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 8], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]],
   [[-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], [], [], [], [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -4], [], [-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [], [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]]⟩,
  ⟨[[8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8], [0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [0, 0, 8, 0, 0, 0, 0, -8], [0, 0, 0, 8], [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 8], [0, 0, -8, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, -8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8], [0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 8], [0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8, 0, 0, 0, 0, 8]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, -16], [0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 16]],
   [[-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4], [], [], [], [0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8], [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, -8], [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8], [-4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4]]⟩,
  ⟨[[48, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16, 0, 0, 0, 0, 48], [0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 48], [0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [16, 0, 0, 0, 0, 48, 0, 0, 0, 0, 48, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 48], [0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 48], [16, 0, 0, 0, 0, 48, 0, 0, 0, 0, 48, 0, 0, 0, 0, 16], [0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48], [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16], [0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16], [48, 0, 0, 0, 0, 16, 0, 0, 0, 0, 16, 0, 0, 0, 0, 48]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, -32, 0, 0, 0, 0, -32], [0, 0, 0, 0, 0, 0, 0, 0, 0, -32], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -32], [0, 0, 0, 0, 0, 0, 0, 0, -32, 0, 0, 0, 0, -32]],
   [[-24, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, -24], [], [], [], [0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [-8, 0, 0, 0, 0, -24, 0, 0, 0, 0, -24, 0, 0, 0, 0, -8], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, -16], [0, 0, 0, 0, 0, 0, 0, 0, 0, -48], [-8, 0, 0, 0, 0, -24, 0, 0, 0, 0, -24, 0, 0, 0, 0, -8], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -48], [0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, -16], [0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16], [-24, 0, 0, 0, 0, -8, 0, 0, 0, 0, -8, 0, 0, 0, 0, -24]]⟩,
  ⟨[[160, 0, 0, 0, 0, 160, 0, 0, 0, 0, 96, 0, 0, 0, 0, 96], [0, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32], [0, 0, 96, 0, 0, 0, 0, 32], [0, 0, 0, 96], [0, 0, 0, 0, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32], [160, 0, 0, 0, 0, 160, 0, 0, 0, 0, 96, 0, 0, 0, 0, 96], [0, 0, 0, 0, 0, 0, 96], [0, 0, 32, 0, 0, 0, 0, 96], [0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 32], [0, 0, 0, 0, 0, 0, 0, 0, 0, 96], [96, 0, 0, 0, 0, 96, 0, 0, 0, 0, 160, 0, 0, 0, 0, 160], [0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96], [0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 96], [0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160], [96, 0, 0, 0, 0, 96, 0, 0, 0, 0, 160, 0, 0, 0, 0, 160]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 192], [0, 0, 0, 0, 0, 0, 0, 0, 0, 192], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 192], [0, 0, 0, 0, 0, 0, 0, 0, 192, 0, 0, 0, 0, 64]],
   [[-80, 0, 0, 0, 0, -80, 0, 0, 0, 0, -48, 0, 0, 0, 0, -48], [], [], [], [0, 0, 0, 0, -160, 0, 0, 0, 0, 0, 0, 0, 0, 0, -32], [-80, 0, 0, 0, 0, -80, 0, 0, 0, 0, -48, 0, 0, 0, 0, -48], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -96, 0, 0, 0, 0, -32], [0, 0, 0, 0, 0, 0, 0, 0, 0, -96], [-48, 0, 0, 0, 0, -48, 0, 0, 0, 0, -80, 0, 0, 0, 0, -80], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -96], [0, 0, 0, 0, 0, 0, 0, 0, -32, 0, 0, 0, 0, -96], [0, 0, 0, 0, -32, 0, 0, 0, 0, 0, 0, 0, 0, 0, -160], [-48, 0, 0, 0, 0, -48, 0, 0, 0, 0, -80, 0, 0, 0, 0, -80]]⟩,
  ⟨[[960, 0, 0, 0, 0, 448, 0, 0, 0, 0, 320, 0, 0, 0, 0, 320], [0, 448, 0, 0, 0, 0, 0, 0, 0, 0, 0, -64], [0, 0, 320, 0, 0, 0, 0, -64], [0, 0, 0, 320], [0, 0, 0, 0, 448, 0, 0, 0, 0, 0, 0, 0, 0, 0, -64], [448, 0, 0, 0, 0, 960, 0, 0, 0, 0, 320, 0, 0, 0, 0, 320], [0, 0, 0, 0, 0, 0, 320], [0, 0, -64, 0, 0, 0, 0, 320], [0, 0, 0, 0, 0, 0, 0, 0, 320, 0, 0, 0, 0, -64], [0, 0, 0, 0, 0, 0, 0, 0, 0, 320], [320, 0, 0, 0, 0, 320, 0, 0, 0, 0, 960, 0, 0, 0, 0, 448], [0, -64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 448], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 320], [0, 0, 0, 0, 0, 0, 0, 0, -64, 0, 0, 0, 0, 320], [0, 0, 0, 0, -64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 448], [320, 0, 0, 0, 0, 320, 0, 0, 0, 0, 448, 0, 0, 0, 0, 960]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, -640, 0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, -640]],
   [[-480, 0, 0, 0, 0, -224, 0, 0, 0, 0, -160, 0, 0, 0, 0, -160], [], [], [], [0, 0, 0, 0, -448, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64], [-224, 0, 0, 0, 0, -480, 0, 0, 0, 0, -160, 0, 0, 0, 0, -160], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -320, 0, 0, 0, 0, 64], [0, 0, 0, 0, 0, 0, 0, 0, 0, -320], [-160, 0, 0, 0, 0, -160, 0, 0, 0, 0, -480, 0, 0, 0, 0, -224], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -320], [0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, -320], [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, -448], [-160, 0, 0, 0, 0, -160, 0, 0, 0, 0, -224, 0, 0, 0, 0, -480]]⟩,
  ⟨[[3712, 0, 0, 0, 0, 1152, 0, 0, 0, 0, 1920, 0, 0, 0, 0, 1408], [0, 1152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [0, 0, 1920, 0, 0, 0, 0, 128], [0, 0, 0, 1408], [0, 0, 0, 0, 1152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128], [1152, 0, 0, 0, 0, 3712, 0, 0, 0, 0, 1408, 0, 0, 0, 0, 1920], [0, 0, 0, 0, 0, 0, 1408], [0, 0, 128, 0, 0, 0, 0, 1920], [0, 0, 0, 0, 0, 0, 0, 0, 1920, 0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1408], [1920, 0, 0, 0, 0, 1408, 0, 0, 0, 0, 3712, 0, 0, 0, 0, 1152], [0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1152], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1408], [0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 1920], [0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1152], [1408, 0, 0, 0, 0, 1920, 0, 0, 0, 0, 1152, 0, 0, 0, 0, 3712]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0, -256], [0, 0, 0, 0, 0, 0, 0, 0, 0, -256], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -256], [0, 0, 0, 0, 0, 0, 0, 0, -256, 0, 0, 0, 0, 256]],
   [[-1856, 0, 0, 0, 0, -576, 0, 0, 0, 0, -960, 0, 0, 0, 0, -704], [], [], [], [0, 0, 0, 0, -1152, 0, 0, 0, 0, 0, 0, 0, 0, 0, -128], [-576, 0, 0, 0, 0, -1856, 0, 0, 0, 0, -704, 0, 0, 0, 0, -960], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -1920, 0, 0, 0, 0, -128], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1408], [-960, 0, 0, 0, 0, -704, 0, 0, 0, 0, -1856, 0, 0, 0, 0, -576], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1408], [0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 0, 0, 0, -1920], [0, 0, 0, 0, -128, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1152], [-704, 0, 0, 0, 0, -960, 0, 0, 0, 0, -576, 0, 0, 0, 0, -1856]]⟩
]

def mask6E0Orbit : List DualQRZ := [
  ⟨[[2]],
   [],
   [[-1]]⟩,
  ⟨[[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [], [0, 0, 2], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 2], [], [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 4]],
   [[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -2], [], [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]⟩,
  ⟨[[2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0, -2], [0, 0, 2, 0, 0, 0, 0, -2], [0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2], [0, 0, -2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2], [0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, -4], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, -2, 0, 0, 0, 0, -4, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 2], [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2]],
   [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, -4], [0, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0, 0, 0, 0, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 4], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]],
   [[-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1], [], [], [], [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 2], [0, 0, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0, 0, 0, 4], [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1]]⟩,
  ⟨[[12, 4, 0, 0, 0, 4, -4, 0, 0, 0, 4, 4, 0, 0, 0, 12], [0, 4, -4, 0, 0, 0, 0, -4, 0, 0, 0, 4], [0, 0, 4, 4, 0, 0, 0, 4], [0, 0, 0, 12], [4, 0, 0, 0, 4, -4, 0, 0, 0, 0, -4, 0, 0, 0, 4, 4], [4, -4, 0, 0, 0, 12, 4, 0, 0, 0, 12, -4, 0, 0, 0, 4], [0, 0, -4, 0, 0, 0, 12, -4], [0, 0, 4, 4, 0, 0, 0, 4], [0, 0, 0, 0, -4, 0, 0, 0, 4, -4, 0, 0, 0, 4, -4], [-4, 0, 0, 0, 0, 4, 0, 0, 0, 12, 4, 0, 0, 0, 0, -4], [4, -4, 0, 0, 0, 12, 4, 0, 0, 0, 12, -4, 0, 0, 0, 4], [0, 4, -4, 0, 0, 0, 0, -4, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 12, 4], [0, 0, 0, 0, -4, 0, 0, 0, 4, -4, 0, 0, 0, 4, -4], [4, 0, 0, 0, 4, -4, 0, 0, 0, 0, -4, 0, 0, 0, 4, 4], [12, 4, 0, 0, 0, 4, -4, 0, 0, 0, 4, 4, 0, 0, 0, 12]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4], [0, 0, 0, 0, 4, 0, 0, 0, -8, 4, 0, 0, -4, -8, 4], [-4, 0, 0, 0, 0, 4, 0, 0, -4, -8, 4, 0, 0, -4, 0, -4], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -8, 4], [0, 0, 0, 0, 4, 0, 0, 0, -8, 4, 0, 0, -4, -8, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4]],
   [[-6, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -6], [], [], [], [-4, 0, 0, 0, -4, 4, 0, 0, 0, 0, 4, 0, 0, 0, -4, -4], [-2, 0, 0, 0, 0, -6, 0, 0, 0, 0, -6, 0, 0, 0, 0, -2], [], [], [0, 0, 0, 0, 4, 0, 0, 0, -4, 4, 0, 0, 0, -4, 4], [4, 0, 0, 0, 0, -4, 0, 0, 0, -12, -4, 0, 0, 0, 0, 4], [-2, 0, 0, 0, 0, -6, 0, 0, 0, 0, -6, 0, 0, 0, 0, -2], [], [0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, -12, -4], [0, 0, 0, 0, 4, 0, 0, 0, -4, 4, 0, 0, 0, -4, 4], [-4, 0, 0, 0, -4, 4, 0, 0, 0, 0, 4, 0, 0, 0, -4, -4], [-6, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -6]]⟩,
  ⟨[[40, -8, 0, 0, 0, 40, 0, 0, 0, 0, 24, 8, 0, 0, 0, 24], [0, 40, 0, 0, 0, 0, -16, -16, 0, 0, 0, 24], [0, 0, 24, 8, 0, 0, 0, 24], [0, 0, 0, 24], [-8, 0, 0, 0, 40, -8, 0, 0, 0, 0, 8, 0, 0, 0, -8, 8], [40, -8, 0, 0, 0, 40, 0, 0, 0, 0, 24, 8, 0, 0, 0, 24], [0, 0, 8, 0, 0, 0, 24, 8], [0, 0, -8, 8, 0, 0, 0, 24], [0, 0, 0, 0, 0, 0, 0, 0, 24, 8, 0, 0, 0, -8, -16], [0, 0, 0, 0, -16, 0, 0, 0, 0, 24, 0, 0, 0, 0, 16], [24, 8, 0, 0, 0, 24, 0, 0, 0, 0, 40, -8, 0, 0, 0, 40], [0, -8, -16, 0, 0, 0, 16, 0, 0, 0, 0, 40], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 24, 8], [0, 0, 0, 0, -16, 0, 0, 0, 24, 8, 0, 0, 0, 24], [8, 0, 0, 0, 24, 8, 0, 0, 0, 0, -8, 0, 0, 0, 40, -8], [24, 8, 0, 0, 0, 24, 0, 0, 0, 0, 40, -8, 0, 0, 0, 40]],
   [[], [0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, -16], [0, 0, 0, 0, -16, 0, 0, 0, 16, 8, 0, 0, 8, 48], [0, 0, 0, 0, -16, 0, 0, 0, 8, 48, 0, 0, 0, 8, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 48, 8], [0, 0, 0, 0, 0, 0, 0, 0, 48, 8, 0, 0, 8, 16, -16], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, -16]],
   [[-20, 0, 0, 0, 0, -20, 0, 0, 0, 0, -12, 0, 0, 0, 0, -12], [], [], [], [8, 0, 0, 0, -40, 8, 0, 0, 0, 0, -8, 0, 0, 0, 8, -8], [-20, 0, 0, 0, 0, -20, 0, 0, 0, 0, -12, 0, 0, 0, 0, -12], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -24, -8, 0, 0, 0, 8, 16], [0, 0, 0, 0, 16, 0, 0, 0, 0, -24, 0, 0, 0, 0, -16], [-12, 0, 0, 0, 0, -12, 0, 0, 0, 0, -20, 0, 0, 0, 0, -20], [], [0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, -24, -8], [0, 0, 0, 0, 16, 0, 0, 0, -24, -8, 0, 0, 0, -24], [-8, 0, 0, 0, -24, -8, 0, 0, 0, 0, 8, 0, 0, 0, -40, 8], [-12, 0, 0, 0, 0, -12, 0, 0, 0, 0, -20, 0, 0, 0, 0, -20]]⟩
]

def mask9E0Orbit : List DualQRZ := [
  ⟨[[2]],
   [],
   [[-1]]⟩,
  ⟨[[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [], [0, 0, 2], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 2], [], [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]],
   [[], [], [0, 0, 0, 0, 0, 0, 0, 0, 4]],
   [[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -2], [], [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]⟩,
  ⟨[[2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2], [0, 0, 2, 0, 0, 0, 0, -2], [0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2], [0, 0, -2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2], [0, 0, 0, 0, -4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, -2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 2], [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2]],
   [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, -4], [0, 0, 0, 0, 4, 0, 0, 0, 0, -4, 0, 0, 0, 0, -4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 4], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4]],
   [[-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1], [], [], [], [0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 4, 0, 0, 0, 0, -2, 0, 0, 0, 0, -4], [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1]]⟩,
  ⟨[[12, -4, 0, 0, 0, 4, -4, 0, 0, 0, 4, -4, 0, 0, 0, 12], [0, 4, -4, 0, 0, 0, 0, -4, 0, 0, 0, 4], [0, 0, 4, -4, 0, 0, 0, 4], [0, 0, 0, 12], [-4, 0, 0, 0, 4, 4, 0, 0, 0, 0, 4, 0, 0, 0, 4, -4], [4, 4, 0, 0, 0, 12, 4, 0, 0, 0, 12, 4, 0, 0, 0, 4], [0, 0, 4, 0, 0, 0, 12, 4], [0, 0, 4, -4, 0, 0, 0, 4], [0, 0, 0, 0, -4, 0, 0, 0, 4, 4, 0, 0, 0, 4, -4], [-4, 0, 0, 0, 0, 4, 0, 0, 0, 12, 4, 0, 0, 0, 0, -4], [4, 4, 0, 0, 0, 12, 4, 0, 0, 0, 12, 4, 0, 0, 0, 4], [0, 4, -4, 0, 0, 0, 0, -4, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 12, -4], [0, 0, 0, 0, -4, 0, 0, 0, 4, 4, 0, 0, 0, 4, -4], [-4, 0, 0, 0, 4, 4, 0, 0, 0, 0, 4, 0, 0, 0, 4, -4], [12, -4, 0, 0, 0, 4, -4, 0, 0, 0, 4, -4, 0, 0, 0, 12]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4], [0, 0, 0, 0, 4, 0, 0, 0, -8, -4, 0, 0, 4, -8, 4], [-4, 0, 0, 0, 0, 4, 0, 0, 4, -8, 4, 0, 0, 4, 0, -4], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, -8, -4], [0, 0, 0, 0, 4, 0, 0, 0, -8, -4, 0, 0, 4, -8, 4], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4]],
   [[-6, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -6], [], [], [], [4, 0, 0, 0, -4, -4, 0, 0, 0, 0, -4, 0, 0, 0, -4, 4], [-2, 0, 0, 0, 0, -6, 0, 0, 0, 0, -6, 0, 0, 0, 0, -2], [], [], [0, 0, 0, 0, 4, 0, 0, 0, -4, -4, 0, 0, 0, -4, 4], [4, 0, 0, 0, 0, -4, 0, 0, 0, -12, -4, 0, 0, 0, 0, 4], [-2, 0, 0, 0, 0, -6, 0, 0, 0, 0, -6, 0, 0, 0, 0, -2], [], [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -12, 4], [0, 0, 0, 0, 4, 0, 0, 0, -4, -4, 0, 0, 0, -4, 4], [4, 0, 0, 0, -4, -4, 0, 0, 0, 0, -4, 0, 0, 0, -4, 4], [-6, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -6]]⟩,
  ⟨[[40, -8, 0, 0, 0, 40, 0, 0, 0, 0, 24, 8, 0, 0, 0, 24], [0, 40, 0, 0, 0, 0, -16, 16, 0, 0, 0, -8], [0, 0, 24, 8, 0, 0, 0, -8], [0, 0, 0, 24], [-8, 0, 0, 0, 40, -8, 0, 0, 0, 0, 8, 0, 0, 0, 24, 8], [40, -8, 0, 0, 0, 40, 0, 0, 0, 0, 24, 8, 0, 0, 0, 24], [0, 0, 8, 0, 0, 0, 24, 8], [0, 0, 24, 8, 0, 0, 0, 24], [0, 0, 0, 0, 0, 0, 0, 0, 24, 8, 0, 0, 0, 24, 16], [0, 0, 0, 0, -16, 0, 0, 0, 0, 24, 0, 0, 0, 0, 16], [24, 8, 0, 0, 0, 24, 0, 0, 0, 0, 40, -8, 0, 0, 0, 40], [0, 24, 16, 0, 0, 0, 16, 0, 0, 0, 0, 40], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 24, 8], [0, 0, 0, 0, 16, 0, 0, 0, -8, 8, 0, 0, 0, 24], [8, 0, 0, 0, -8, 8, 0, 0, 0, 0, -8, 0, 0, 0, 40, -8], [24, 8, 0, 0, 0, 24, 0, 0, 0, 0, 40, -8, 0, 0, 0, 40]],
   [[], [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, -16], [0, 0, 0, 0, 16, 0, 0, 0, 16, 8, 0, 0, 8, 48], [0, 0, 0, 0, -16, 0, 0, 0, 8, 48, 0, 0, 0, 8, 16], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 48, 8], [0, 0, 0, 0, 0, 0, 0, 0, 48, 8, 0, 0, 8, 16, 16], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16]],
   [[-20, 0, 0, 0, 0, -20, 0, 0, 0, 0, -12, 0, 0, 0, 0, -12], [], [], [], [8, 0, 0, 0, -40, 8, 0, 0, 0, 0, -8, 0, 0, 0, -24, -8], [-20, 0, 0, 0, 0, -20, 0, 0, 0, 0, -12, 0, 0, 0, 0, -12], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -24, -8, 0, 0, 0, -24, -16], [0, 0, 0, 0, 16, 0, 0, 0, 0, -24, 0, 0, 0, 0, -16], [-12, 0, 0, 0, 0, -12, 0, 0, 0, 0, -20, 0, 0, 0, 0, -20], [], [0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, -24, -8], [0, 0, 0, 0, -16, 0, 0, 0, 8, -8, 0, 0, 0, -24], [-8, 0, 0, 0, 8, -8, 0, 0, 0, 0, 8, 0, 0, 0, -40, 8], [-12, 0, 0, 0, 0, -12, 0, 0, 0, 0, -20, 0, 0, 0, 0, -20]]⟩
]

def mask6Cert : WitnessedDualCert := ⟨1, [256, 0, 16, 0, 2], mask6TotOrbit⟩
def mask9Cert : WitnessedDualCert := ⟨1, [256, 0, 16, 0, 2], mask9TotOrbit⟩

theorem mask9Cert_valid : checkWitnessedDualCert mask9Auto (dualTotE4 4) mask9Cert = true := by
  decide

theorem mask6Cert_mutated_rejected :
    checkWitnessedDualCert mask6Auto (dualTotE4 4) ⟨1, [256, 0, 16, 0, 3], mask6TotOrbit⟩ = false := by
  decide

theorem mask6Orbit_mutated_rejected :
    checkWitnessedDualCert mask6Auto (dualTotE4 4) ⟨1, [256, 0, 16, 0, 2], mask6TotOrbit.reverse⟩ = false := by
  decide

theorem mask9TotOrbit_ok : checkWitnessedOrbit mask9Auto (dualTotE4 4) mask9TotOrbit = true := by
  have h := mask9Cert_valid
  unfold checkWitnessedDualCert at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem mask6E0Orbit_ok : checkWitnessedOrbit mask6Auto (dualE4State0 4) mask6E0Orbit = true := by
  decide

theorem mask9E0Orbit_ok : checkWitnessedOrbit mask9Auto (dualE4State0 4) mask9E0Orbit = true := by
  decide

def rudinShapiroAuto : BinAuto 2 := bijTailAuto 0 (fun _ => false)

def rsCert : DualCert := ⟨2, [-16, 4, 4]⟩

end PureSiliconAuto

-- ============================================================================
-- Section 5: Axiom Audit (`#print axioms` on EVERY Main Theorem)
-- ============================================================================
