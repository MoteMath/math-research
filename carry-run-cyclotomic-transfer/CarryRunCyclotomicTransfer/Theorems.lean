/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryRunCyclotomicTransfer.Defs

/-!
# Theorems (`CarryRunCyclotomicTransfer`)

# Pure-Silicon Carry-Propagation Depth & Run-Length Automaton Transfer Engine

Worker: `transducer-3` (Thread 1 — Carry, Transducer & Automatic Infinite Proof Engines)
Standalone Core Lean 4.34.1 (zero Mathlib, zero `sorry`, zero custom axioms).

This file implements:
1. **Reusable Infinite Proof Mechanism (`CarryTransferEngine`)**:
   - `CarryTransducer B N`: arbitrary finite-state weighted radix-`B` carry transducer on `N` states.
   - `arithSum_eq_transferPow`: Universal Bit-Slice Transfer Bridge proving that the `B^(2w)`-term
     arithmetic sum over all `x, y < B^w` equals `dot N T.readout (iterOp (transferOp T) w (basisVec T.q0))`.
   - `intertwining_lift`: Exact intertwining homomorphism lifter (`Φ (M v) = U (Φ v) → Φ (M^[w] v) = U^[w] (Φ v)`).
   - `scaled_periodic_lift`: Exact scaled-periodicity lifter (`M^[P] v = c • v → M^[w] v = c^(w/P) • M^[w%P] v`).
   - `trinomial_annihilator_recurrence`, `quad_annihilator_recurrence`, `trinomial_gf_cauchy`:
     Finite polynomial annihilator → infinite linear recurrence & exact rational generating-function
     Cauchy-product identity.

2. **Concrete Radix-`B` / Binary Arithmetic Semantics**:
   - Exact LSB-first ripple addition, `digitSum` (`popcount`), `maxRippleDepthLe`, `maxCarryRunLe`,
     and `carryAbsorptions` directly on `Nat`, with kernel-checked semantic bridges to `x + y`.

3. **Three Parametric Infinite Theorem Families (`∀ m ≥ 1, ∀ L ≥ 1, ∀ w : Nat`)**:
   - **Theorem 1 (Cyclotomic Carry-Run Collapse)**: Even-radix `B = 2m` and binary carry-run `≤ L`
     output-parity (`(-1)^popcount((x+y) % 2^w)` and full `(-1)^popcount(x+y)`) collapses to exact
     period `L + 2` (in `{-1, 0, +1}` and `{-2, 0, +1}` for `B = 2`) via hyperplane intertwining with
     cyclic rotation on `ℤ^(L+2)`.
   - **Theorem 2 (Universal 3-Parameter Ripple-Carry Annihilator & Monomial Input-Parity Collapse)**:
     Exact matrix annihilator `M^(L+1) - (k+p+g) M^L + g p^L I = 0` for all `L ≥ 1, k, p, g ∈ ℤ`,
     yielding exact rational GF `1 / (1 - (k+p+g)z + g p^L z^(L+1))`, unweighted binary recurrence
     `R(w+L+1) = 4 R(w+L) - 2^L R(w)`, and the exact period-`(L+1)` monomial collapse for input parity
     `(-1)^(σ_{2m}(x) + σ_{2m}(y))` (`0` when `(L+1) ∤ w`, `((-1)^(L+1) 2^L m^(L+1))^(w/(L+1))` when `(L+1) ∣ w`).
   - **Theorem 3 (Absorption-Weighted Carry-Run Generating-Function Law & `t = 0` Odd/Even Dichotomy)**:
     Universal 4-parameter carry-run annihilator `M^(L+2) - (a+r)M^(L+1) + (ar-bc)M^L + b c r^L I = 0`,
     yielding `A_L(t, w+L+2) = (1-t) A_L(t, w+L) + t A_L(t, w)` for all `t ∈ ℤ, L ≥ 1, w ∈ ℕ`,
     and at `t = 0` (zero carry absorptions): exact finite support `A_{2k+1}(0, w) = 0` for all `w ≥ 2k+1`,
     versus persistent oscillation `A_{2k}(0, w) = (-1)^w` for all `w ≥ 2k`.

4. **Non-Vacuity Witnesses & Sharpness Counterexamples (S1–S5)** verified by the Lean kernel.
-/


namespace SiliconCarryTransfer
@[simp] theorem sumNat_zero (f : Nat → Int) : sumNat 0 f = 0 := rfl
@[simp] theorem sumNat_succ (n : Nat) (f : Nat → Int) : sumNat (n + 1) f = sumNat n f + f n := rfl

theorem sumNat_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat_succ]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumNat_zero_fn (n : Nat) : sumNat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumNat_succ, ih]

theorem sumNat_add (n : Nat) (f g : Nat → Int) :
    sumNat n (fun i => f i + g i) = sumNat n f + sumNat n g := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [sumNat_succ, ih]
    omega

theorem sumNat_sub (n : Nat) (f g : Nat → Int) :
    sumNat n (fun i => f i - g i) = sumNat n f - sumNat n g := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [sumNat_succ, ih]
    omega

theorem sumNat_neg (n : Nat) (f : Nat → Int) :
    sumNat n (fun i => -f i) = -sumNat n f := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [sumNat_succ, ih]
    omega

theorem sumNat_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumNat n (fun i => c * f i) = c * sumNat n f := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [sumNat_succ, ih, Int.mul_add]

theorem sumNat_mul_right (n : Nat) (c : Int) (f : Nat → Int) :
    sumNat n (fun i => f i * c) = sumNat n f * c := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [sumNat_succ, ih, Int.add_mul]

theorem sumNat_swap (m n : Nat) (f : Nat → Nat → Int) :
    sumNat m (fun i => sumNat n (fun j => f i j)) =
    sumNat n (fun j => sumNat m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumNat_zero]
    symm
    exact sumNat_zero_fn n
  | succ k ih =>
    simp only [sumNat_succ, ih, sumNat_add]

theorem sumNat_split (a b : Nat) (f : Nat → Int) :
    sumNat (a + b) f = sumNat a f + sumNat b (fun j => f (a + j)) := by
  induction b with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, sumNat_succ, ih, sumNat_succ]
    omega

theorem sumNat_succ_front (n : Nat) (f : Nat → Int) :
    sumNat (n + 1) f = f 0 + sumNat n (fun i => f (i + 1)) := by
  rw [Nat.add_comm n 1, sumNat_split 1 n f]
  simp only [sumNat_succ, sumNat_zero, Int.zero_add]
  congr 1
  apply sumNat_congr
  intro i _
  rw [Nat.add_comm]

theorem sumNat_pred_front (n : Nat) (hn : 1 ≤ n) (f : Nat → Int) :
    sumNat n f = f 0 + sumNat (n - 1) (fun i => f (i + 1)) := by
  have h := sumNat_succ_front (n - 1) f
  have heq : n - 1 + 1 = n := by omega
  rw [heq] at h
  exact h

theorem sumNat_pred_back (n : Nat) (hn : 1 ≤ n) (f : Nat → Int) :
    sumNat n f = sumNat (n - 1) f + f (n - 1) := by
  have h := sumNat_succ (n - 1) f
  have heq : n - 1 + 1 = n := by omega
  rw [heq] at h
  exact h

theorem sumNat_mul_split (m B : Nat) (f : Nat → Int) :
    sumNat (m * B) f = sumNat m (fun q => sumNat B (fun r => f (q * B + r))) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sumNat_split, ih, sumNat_succ]

theorem sumNat_ite_eq (n k : Nat) (v : Int) (hk : k < n) :
    sumNat n (fun i => if i = k then v else 0) = v := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [sumNat_succ]
    by_cases hkm : k = m
    · subst hkm
      have h0 : sumNat k (fun i => if i = k then v else 0) = 0 := by
        rw [sumNat_congr (g := fun _ => 0)]
        · exact sumNat_zero_fn k
        · intro i hi
          have : i ≠ k := by omega
          simp [this]
      simp [h0]
    · have hk' : k < m := by omega
      have hne : m ≠ k := by omega
      simp [hne, ih hk']

theorem sumNat_ite_eq_symm (n k : Nat) (v : Int) (hk : k < n) :
    sumNat n (fun i => if k = i then v else 0) = v := by
  rw [sumNat_congr (g := fun i => if i = k then v else 0)]
  · exact sumNat_ite_eq n k v hk
  · intro i _
    by_cases h : k = i
    · subst h; simp
    · have h2 : i ≠ k := fun heq => h heq.symm
      simp [h, h2]

theorem sumNat_ite_eq_out (n k : Nat) (v : Int) (hk : n ≤ k) :
    sumNat n (fun i => if i = k then v else 0) = 0 := by
  rw [sumNat_congr (g := fun _ => 0)]
  · exact sumNat_zero_fn n
  · intro i hi
    have : i ≠ k := by omega
    simp [this]

def dot (N : Nat) (f v : Nat → Int) : Int :=
  sumNat N (fun i => f i * v i)

def basisVec (q0 : Nat) : Nat → Int :=
  fun i => if i = q0 then 1 else 0

def smulVec (c : Int) (v : Nat → Int) : Nat → Int :=
  fun i => c * v i

def addVec (u v : Nat → Int) : Nat → Int :=
  fun i => u i + v i

def subVec (u v : Nat → Int) : Nat → Int :=
  fun i => u i - v i

theorem dot_basisVec (N q0 : Nat) (f : Nat → Int) (hq0 : q0 < N) :
    dot N f (basisVec q0) = f q0 := by
  unfold dot basisVec
  rw [sumNat_congr (g := fun i => if i = q0 then f q0 else 0)]
  · exact sumNat_ite_eq N q0 (f q0) hq0
  · intro i _
    by_cases h : i = q0
    · subst h; simp
    · simp [h]

theorem dot_smul_right (N : Nat) (c : Int) (f v : Nat → Int) :
    dot N f (smulVec c v) = c * dot N f v := by
  unfold dot smulVec
  rw [← sumNat_mul_left]
  apply sumNat_congr
  intro i _
  rw [← Int.mul_assoc, Int.mul_comm (f i) c, Int.mul_assoc]

theorem dot_add_right (N : Nat) (f u v : Nat → Int) :
    dot N f (addVec u v) = dot N f u + dot N f v := by
  unfold dot addVec
  rw [← sumNat_add]
  apply sumNat_congr
  intro i _
  exact Int.mul_add (f i) (u i) (v i)

theorem dot_sub_right (N : Nat) (f u v : Nat → Int) :
    dot N f (subVec u v) = dot N f u - dot N f v := by
  unfold dot subVec
  rw [← sumNat_sub]
  apply sumNat_congr
  intro i _
  exact Int.mul_sub (f i) (u i) (v i)

@[simp] theorem iterOp_zero {α : Type} (F : α → α) (x : α) : iterOp F 0 x = x := rfl
@[simp] theorem iterOp_succ {α : Type} (F : α → α) (w : Nat) (x : α) :
    iterOp F (w + 1) x = F (iterOp F w x) := rfl

theorem iterOp_add {α : Type} (F : α → α) (a b : Nat) (x : α) :
    iterOp F (a + b) x = iterOp F a (iterOp F b x) := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_add, iterOp_succ, ih, iterOp_succ]

theorem iterOp_succ_right {α : Type} (F : α → α) (w : Nat) (x : α) :
    iterOp F (w + 1) x = iterOp F w (F x) := by
  rw [iterOp_add F w 1 x]
  rfl

-- Helper power lemmas for Int (using core Lean's Int.pow_zero / Int.pow_succ)
theorem int_pow_add (a : Int) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, Int.pow_succ, ih, Int.pow_succ, Int.mul_assoc]

theorem int_pow_mul (a : Int) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, int_pow_add, ih, Int.pow_succ]

-- ============================================================================
-- SECTION 2: Reusable Infinite Proof Mechanism — `CarryTransferEngine`
-- ============================================================================

/-- A finite-state weighted radix-`B` carry transducer on state space `{0, ..., N-1}`
    (plus implicit reject state `none`). -/
structure CarryTransducer (B N : Nat) where
  step    : Nat → Nat → Nat → Option Nat
  wt      : Nat → Nat → Nat → Int
  q0      : Nat
  readout : Nat → Int
  hB      : 0 < B
  hq0     : q0 < N
  hClosed : ∀ q, q < N → ∀ rx, rx < B → ∀ ry, ry < B →
              ∀ q', step q rx ry = some q' → q' < N

/-- Concrete `w`-digit LSB-first execution of `T` starting from state `q` on `(x, y)`. -/
def evalPair {B N : Nat} (T : CarryTransducer B N) : Nat → Nat → Nat → Nat → Int
  | 0, q, _, _ => T.readout q
  | w + 1, q, x, y =>
    match T.step q (x % B) (y % B) with
    | none => 0
    | some q' => T.wt q (x % B) (y % B) * evalPair T w q' (x / B) (y / B)

/-- Concrete `B^(2w)`-term arithmetic sum over all `(x, y) ∈ [0, B^w)^2` starting at state `q`. -/
def arithSumFrom {B N : Nat} (T : CarryTransducer B N) (w q : Nat) : Int :=
  sumNat (B ^ w) (fun x => sumNat (B ^ w) (fun y => evalPair T w q x y))

/-- Concrete `B^(2w)`-term arithmetic sum over all `(x, y) ∈ [0, B^w)^2` starting at `T.q0`. -/
def arithSum {B N : Nat} (T : CarryTransducer B N) (w : Nat) : Int :=
  arithSumFrom T w T.q0

/-- Backward (pullback) transfer operator on `Nat → Int`. -/
def pullbackOp {B N : Nat} (T : CarryTransducer B N) (g : Nat → Int) : Nat → Int :=
  fun q => sumNat B (fun rx => sumNat B (fun ry =>
    match T.step q rx ry with
    | none => 0
    | some q' => T.wt q rx ry * g q'))

/-- Forward (pushforward / column-matrix) integer transfer operator `M_T : ℤ^N → ℤ^N`. -/
def transferOp {B N : Nat} (T : CarryTransducer B N) (v : Nat → Int) : Nat → Int :=
  fun q' => sumNat N (fun q => sumNat B (fun rx => sumNat B (fun ry =>
    match T.step q rx ry with
    | none => 0
    | some q'' => if q'' = q' then T.wt q rx ry * v q else 0)))

/-- ENGINE THEOREM A1 (Pullback Bit-Slice Lifting):
    The `B^(2w)`-term arithmetic sum equals the `w`-fold pullback of `T.readout`. -/
theorem arithSumFrom_eq_pullbackPow {B N : Nat} (T : CarryTransducer B N) (w : Nat) :
    ∀ q, arithSumFrom T w q = iterOp (pullbackOp T) w T.readout q := by
  induction w with
  | zero =>
    intro q
    simp [arithSumFrom, evalPair]
  | succ k ih =>
    intro q
    unfold arithSumFrom
    rw [Nat.pow_succ]
    rw [sumNat_mul_split (B ^ k) B]
    rw [sumNat_congr (g := fun qx =>
      sumNat B (fun rx =>
        sumNat (B ^ k) (fun qy =>
          sumNat B (fun ry =>
            evalPair T (k + 1) q (qx * B + rx) (qy * B + ry)))))]
    · rw [sumNat_swap (B ^ k) B]
      rw [sumNat_congr (g := fun rx =>
        sumNat B (fun ry =>
          sumNat (B ^ k) (fun qx =>
            sumNat (B ^ k) (fun qy =>
              match T.step q rx ry with
              | none => 0
              | some q' => T.wt q rx ry * evalPair T k q' qx qy))))]
      · simp only [iterOp_succ, pullbackOp]
        apply sumNat_congr
        intro rx hrx
        apply sumNat_congr
        intro ry hry
        cases hstep : T.step q rx ry with
        | none =>
          rw [sumNat_congr (g := fun _ => 0)]
          · exact sumNat_zero_fn (B ^ k)
          · intro qx _
            exact sumNat_zero_fn (B ^ k)
        | some q' =>
          have hpull :
              sumNat (B ^ k) (fun qx => sumNat (B ^ k) (fun qy => T.wt q rx ry * evalPair T k q' qx qy)) =
              T.wt q rx ry * arithSumFrom T k q' := by
            unfold arithSumFrom
            rw [← sumNat_mul_left]
            apply sumNat_congr
            intro qx _
            rw [sumNat_mul_left]
          rw [hpull, ih q']
      · intro rx hrx
        rw [sumNat_congr (g := fun qx =>
          sumNat B (fun ry =>
            sumNat (B ^ k) (fun qy =>
              match T.step q rx ry with
              | none => 0
              | some q' => T.wt q rx ry * evalPair T k q' qx qy)))]
        · exact sumNat_swap (B ^ k) B _
        · intro qx _
          rw [sumNat_swap (B ^ k) B]
          apply sumNat_congr
          intro ry hry
          apply sumNat_congr
          intro qy _
          have hmodx : (qx * B + rx) % B = rx := by
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrx]
          have hdivx : (qx * B + rx) / B = qx := by
            rw [Nat.mul_comm, Nat.mul_add_div T.hB, Nat.div_eq_of_lt hrx, Nat.add_zero]
          have hmody : (qy * B + ry) % B = ry := by
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hry]
          have hdivy : (qy * B + ry) / B = qy := by
            rw [Nat.mul_comm, Nat.mul_add_div T.hB, Nat.div_eq_of_lt hry, Nat.add_zero]
          simp [evalPair, hmodx, hdivx, hmody, hdivy]
    · intro qx _
      apply sumNat_congr
      intro rx _
      exact sumNat_mul_split (B ^ k) B _

/-- Exact discrete adjointness between forward `transferOp` and backward `pullbackOp`. -/
theorem dot_transferOp_eq_dot_pullbackOp {B N : Nat} (T : CarryTransducer B N)
    (g v : Nat → Int) :
    dot N g (transferOp T v) = dot N (pullbackOp T g) v := by
  unfold dot transferOp pullbackOp
  rw [sumNat_congr (g := fun q' =>
    sumNat N (fun q => sumNat B (fun rx => sumNat B (fun ry =>
      match T.step q rx ry with
      | none => 0
      | some q'' => if q'' = q' then g q' * (T.wt q rx ry * v q) else 0))))]
  · rw [sumNat_swap N N]
    apply sumNat_congr
    intro q hq
    rw [← sumNat_mul_right]
    rw [sumNat_swap N B]
    apply sumNat_congr
    intro rx hrx
    rw [← sumNat_mul_right]
    rw [sumNat_swap N B]
    apply sumNat_congr
    intro ry hry
    cases hstep : T.step q rx ry with
    | none =>
      simp [sumNat_zero_fn]
    | some q'' =>
      have hq'' : q'' < N := T.hClosed q hq rx hrx ry hry q'' hstep
      rw [sumNat_congr (g := fun q' => if q'' = q' then g q'' * (T.wt q rx ry * v q) else 0)]
      · rw [sumNat_ite_eq_symm N q'' (g q'' * (T.wt q rx ry * v q)) hq'']
        rw [Int.mul_comm (g q''), Int.mul_assoc, Int.mul_comm (v q) (g q''), ← Int.mul_assoc]
      · intro q' _
        by_cases h : q'' = q'
        · subst h; simp
        · simp [h]
  · intro q' _
    rw [← sumNat_mul_left]
    apply sumNat_congr
    intro q _
    rw [← sumNat_mul_left]
    apply sumNat_congr
    intro rx _
    rw [← sumNat_mul_left]
    apply sumNat_congr
    intro ry _
    cases T.step q rx ry with
    | none => simp
    | some q'' =>
      by_cases h : q'' = q' <;> simp [h]

theorem dot_transferPow_eq_dot_pullbackPow {B N : Nat} (T : CarryTransducer B N)
    (w : Nat) (g v : Nat → Int) :
    dot N g (iterOp (transferOp T) w v) = dot N (iterOp (pullbackOp T) w g) v := by
  induction w generalizing g v with
  | zero => rfl
  | succ k ih =>
    rw [iterOp_succ, dot_transferOp_eq_dot_pullbackOp, ih, ← iterOp_succ_right]

/-- ENGINE THEOREM A (Universal Bit-Slice Transfer Bridge):
    For EVERY finite-state weighted carry transducer `T` and EVERY digit-width `w : Nat`,
    the `B^(2w)`-term arithmetic sum over `[0, B^w)^2` equals `⟨T.readout, M_T^w e_{q0}⟩`. -/
theorem arithSum_eq_transferPow {B N : Nat} (T : CarryTransducer B N) (w : Nat) :
    arithSum T w = dot N T.readout (iterOp (transferOp T) w (basisVec T.q0)) := by
  rw [dot_transferPow_eq_dot_pullbackPow, dot_basisVec N T.q0 _ T.hq0]
  exact arithSumFrom_eq_pullbackPow T w T.q0

/-- Replace `transferOp T` with an algebraically simplified operator `M` once proven equal on `< N`. -/
theorem iterOp_eq_of_agree {N : Nat} (M₁ M₂ : (Nat → Int) → (Nat → Int))
    (hAgree : ∀ u v, (∀ i, i < N → u i = v i) → ∀ i, i < N → M₁ u i = M₂ v i)
    (w : Nat) (v : Nat → Int) :
    ∀ i, i < N → iterOp M₁ w v i = iterOp M₂ w v i := by
  induction w with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hi
    exact hAgree _ _ ih i hi

theorem dot_congr_right (N : Nat) (f u v : Nat → Int) (h : ∀ i, i < N → u i = v i) :
    dot N f u = dot N f v := by
  unfold dot
  apply sumNat_congr
  intro i hi
  rw [h i hi]

/-- ENGINE THEOREM B (Exact Intertwining Homomorphism Lifter):
    A single-step intertwining certificate `Φ (M v) = U (Φ v)` lifts to ALL widths `w : Nat`. -/
theorem intertwining_lift {V W : Type} (M : V → V) (U : W → W) (Φ : V → W)
    (hCert : ∀ v, Φ (M v) = U (Φ v)) (w : Nat) (v : V) :
    Φ (iterOp M w v) = iterOp U w (Φ v) := by
  induction w with
  | zero => rfl
  | succ k ih =>
    simp only [iterOp_succ, hCert, ih]

/-- ENGINE THEOREM C (Exact Scaled-Periodicity Lifter):
    If `M` is homogeneous (`M (c • v) = c • M v`) and `M^[P] v = c • v`,
    then `M^[w] v = c^(w / P) • M^[w % P] v` for ALL widths `w : Nat`. -/
theorem scaled_periodic_lift (M : (Nat → Int) → (Nat → Int))
    (hHom : ∀ (c : Int) (u : Nat → Int) (i : Nat), M (smulVec c u) i = c * M u i)
    {P : Nat} (c : Int) (v : Nat → Int)
    (hPer : ∀ i, iterOp M P v i = c * v i) :
    ∀ (w i : Nat), iterOp M w v i = c ^ (w / P) * iterOp M (w % P) v i := by
  have hIterHom : ∀ (k : Nat) (a : Int) (u : Nat → Int) (i : Nat),
      iterOp M k (smulVec a u) i = a * iterOp M k u i := by
    intro k
    induction k with
    | zero => intro a u i; rfl
    | succ m ih =>
      intro a u i
      have heq : iterOp M m (smulVec a u) = smulVec a (iterOp M m u) := by
        funext j; exact ih a u j
      rw [iterOp_succ, heq, hHom, iterOp_succ]
  have hIterPer : ∀ (q : Nat) (i : Nat), iterOp M (P * q) v i = c ^ q * v i := by
    intro q
    induction q with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [Nat.mul_succ, Nat.add_comm (P * m) P, iterOp_add]
      have heq : iterOp M (P * m) v = smulVec (c ^ m) v := by
        funext j; exact ih j
      rw [heq, hIterHom, hPer, Int.pow_succ, Int.mul_assoc]
  intro w i
  have hdiv : P * (w / P) + w % P = w := Nat.div_add_mod w P
  conv => lhs; rw [← hdiv]
  rw [Nat.add_comm (P * (w / P)) (w % P), iterOp_add]
  have heq : iterOp M (P * (w / P)) v = smulVec (c ^ (w / P)) v := by
    funext j; exact hIterPer (w / P) j
  rw [heq, hIterHom]

/-- ENGINE THEOREM D1 (Finite Trinomial Annihilator → Infinite Recurrence):
    If `M^[d+1] u - α • M^[d] u + β • u = 0` for all `u`, then for EVERY readout `f` and `w`,
    the sequence `a(w) = dot N f (M^[w] v0)` obeys `a(w+d+1) = α * a(w+d) - β * a(w)`. -/
theorem trinomial_annihilator_recurrence {N : Nat} (M : (Nat → Int) → (Nat → Int))
    (d : Nat) (α β : Int)
    (hAnn : ∀ u i, i < N → iterOp M (d + 1) u i - α * iterOp M d u i + β * u i = 0)
    (f v0 : Nat → Int) (w : Nat) :
    dot N f (iterOp M (w + d + 1) v0) =
      α * dot N f (iterOp M (w + d) v0) - β * dot N f (iterOp M w v0) := by
  have h1 : w + d + 1 = (d + 1) + w := by omega
  have h2 : w + d = d + w := by omega
  rw [h1, h2, iterOp_add M (d + 1) w v0, iterOp_add M d w v0]
  let u := iterOp M w v0
  have hpt : ∀ i, i < N → iterOp M (d + 1) u i = α * iterOp M d u i - β * u i := by
    intro i hi
    have h0 := hAnn u i hi
    omega
  rw [dot_congr_right N f _ (subVec (smulVec α (iterOp M d u)) (smulVec β u)) hpt]
  rw [dot_sub_right, dot_smul_right, dot_smul_right]

/-- ENGINE THEOREM D2 (Finite 4-Term Annihilator → Infinite Recurrence):
    If `M^[d+2] u - c1 • M^[d+1] u + c2 • M^[d] u + c3 • u = 0` for all `u`, then `a(w)` satisfies
    `a(w+d+2) = c1 * a(w+d+1) - c2 * a(w+d) - c3 * a(w)` for ALL `w : Nat`. -/
theorem quad_annihilator_recurrence {N : Nat} (M : (Nat → Int) → (Nat → Int))
    (d : Nat) (c1 c2 c3 : Int)
    (hAnn : ∀ u i, i < N →
      iterOp M (d + 2) u i - c1 * iterOp M (d + 1) u i + c2 * iterOp M d u i + c3 * u i = 0)
    (f v0 : Nat → Int) (w : Nat) :
    dot N f (iterOp M (w + d + 2) v0) =
      c1 * dot N f (iterOp M (w + d + 1) v0) -
      c2 * dot N f (iterOp M (w + d) v0) -
      c3 * dot N f (iterOp M w v0) := by
  have h1 : w + d + 2 = (d + 2) + w := by omega
  have h2 : w + d + 1 = (d + 1) + w := by omega
  have h3 : w + d = d + w := by omega
  rw [h1, h2, h3, iterOp_add M (d + 2) w v0, iterOp_add M (d + 1) w v0, iterOp_add M d w v0]
  let u := iterOp M w v0
  have hpt : ∀ i, i < N →
      iterOp M (d + 2) u i =
        (c1 * iterOp M (d + 1) u i - c2 * iterOp M d u i) - c3 * u i := by
    intro i hi
    have h0 := hAnn u i hi
    omega
  rw [dot_congr_right N f _
      (subVec (subVec (smulVec c1 (iterOp M (d + 1) u)) (smulVec c2 (iterOp M d u)))
              (smulVec c3 u)) hpt]
  rw [dot_sub_right, dot_sub_right, dot_smul_right, dot_smul_right, dot_smul_right]

/-- Formal Cauchy product of two integer formal power series `P, Q : Nat → Int`. -/
def cauchyProd (P Q : Nat → Int) (w : Nat) : Int :=
  sumNat (w + 1) (fun j => P j * Q (w - j))

/-- Denominator polynomial `1 - α z + β z^(L+1)` as a formal power series coefficient sequence. -/
def trinomialDenom (L : Nat) (α β : Int) (j : Nat) : Int :=
  (if j = 0 then 1 else 0) + (if j = 1 then -α else 0) + (if j = L + 1 then β else 0)

/-- ENGINE THEOREM D3 (Exact Rational Generating-Function Cauchy-Product Lifter):
    If `a(w) = α^w` for `0 ≤ w ≤ L` and `a(w+L+1) = α*a(w+L) - β*a(w)` for all `w`,
    then `(1 - α z + β z^(L+1)) * Σ a(w) z^w = 1` (exact Cauchy product = `δ_{w, 0}` for ALL `w`). -/
theorem trinomial_gf_cauchy (L : Nat) (_hL : 1 ≤ L) (α β : Int) (a : Nat → Int)
    (hInit : ∀ w, w ≤ L → a w = α ^ w)
    (hRec : ∀ w, a (w + L + 1) = α * a (w + L) - β * a w)
    (w : Nat) :
    cauchyProd (trinomialDenom L α β) a w = if w = 0 then 1 else 0 := by
  unfold cauchyProd trinomialDenom
  have hsplit :
      sumNat (w + 1) (fun j =>
        ((if j = 0 then 1 else 0) + (if j = 1 then -α else 0) + (if j = L + 1 then β else 0)) * a (w - j)) =
      sumNat (w + 1) (fun j => (if j = 0 then 1 else 0) * a (w - j)) +
      sumNat (w + 1) (fun j => (if j = 1 then -α else 0) * a (w - j)) +
      sumNat (w + 1) (fun j => (if j = L + 1 then β else 0) * a (w - j)) := by
    rw [← sumNat_add, ← sumNat_add]
    apply sumNat_congr
    intro j _
    rw [Int.add_mul, Int.add_mul]
  rw [hsplit]
  have t0 : sumNat (w + 1) (fun j => (if j = 0 then 1 else 0) * a (w - j)) = a w := by
    rw [sumNat_congr (g := fun j => if j = 0 then a w else 0)]
    · exact sumNat_ite_eq (w + 1) 0 (a w) (Nat.zero_lt_succ w)
    · intro j _
      by_cases h : j = 0
      · subst h; simp
      · simp [h]
  rw [t0]
  cases w with
  | zero =>
    have t1 : sumNat 1 (fun j => (if j = 1 then -α else 0) * a (0 - j)) = 0 := by simp
    have t2 : sumNat 1 (fun j => (if j = L + 1 then β else 0) * a (0 - j)) = 0 := by
      simp [sumNat]
    rw [t1, t2, hInit 0 (Nat.zero_le L), Int.pow_zero]
    simp
  | succ k =>
    have t1 : sumNat (k + 2) (fun j => (if j = 1 then -α else 0) * a (k + 1 - j)) = -α * a k := by
      rw [sumNat_congr (g := fun j => if j = 1 then -α * a k else 0)]
      · exact sumNat_ite_eq (k + 2) 1 (-α * a k) (by omega)
      · intro j _
        by_cases h : j = 1
        · subst h; simp
        · simp [h]
    rw [t1]
    by_cases hkle : k + 1 ≤ L
    · have t2 : sumNat (k + 2) (fun j => (if j = L + 1 then β else 0) * a (k + 1 - j)) = 0 := by
        rw [sumNat_congr (g := fun j => if j = L + 1 then β * a (k + 1 - (L + 1)) else 0)]
        · exact sumNat_ite_eq_out (k + 2) (L + 1) _ (by omega)
        · intro j _
          by_cases h : j = L + 1
          · subst h; simp
          · simp [h]
      rw [t2, hInit (k + 1) hkle, hInit k (by omega), Int.pow_succ]
      simp only [show k + 1 ≠ 0 from by omega, ↓reduceIte]
      rw [Int.neg_mul, Int.mul_comm α (α ^ k)]
      omega
    · have hkgt : L + 1 ≤ k + 1 := by omega
      have t2 : sumNat (k + 2) (fun j => (if j = L + 1 then β else 0) * a (k + 1 - j)) =
          β * a (k + 1 - (L + 1)) := by
        rw [sumNat_congr (g := fun j => if j = L + 1 then β * a (k + 1 - (L + 1)) else 0)]
        · exact sumNat_ite_eq (k + 2) (L + 1) _ (by omega)
        · intro j _
          by_cases h : j = L + 1
          · subst h; simp
          · simp [h]
      rw [t2]
      let m := k - L
      have hm3 : k + 1 - (L + 1) = m := by omega
      have hm1 : k + 1 = m + L + 1 := by omega
      have hm2 : k = m + L := by omega
      rw [hm3, hm1, hm2, hRec m]
      simp only [show m + L + 1 ≠ 0 from by omega, ↓reduceIte]
      rw [Int.neg_mul]
      omega

@[simp] theorem paritySign_zero : paritySign 0 = 1 := rfl
@[simp] theorem paritySign_one : paritySign 1 = -1 := rfl

theorem paritySign_add (a b : Nat) : paritySign (a + b) = paritySign a * paritySign b := by
  unfold paritySign
  have hmod : (a + b) % 2 = (a % 2 + b % 2) % 2 := Nat.add_mod a b 2
  rw [hmod]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

theorem paritySign_succ (n : Nat) : paritySign (n + 1) = -paritySign n := by
  rw [paritySign_add, paritySign_one]
  omega

theorem digitSum_mod_pow (B : Nat) :
    ∀ w n, digitSum B w (n % B ^ w) = digitSum B w n := by
  intro w
  induction w with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    simp only [digitSum]
    have hpow1 : B ^ (k + 1) = B ^ k * B := Nat.pow_succ B k
    have hpow2 : B ^ (k + 1) = B * B ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : (n % B ^ (k + 1)) % B = n % B := by
      rw [hpow1, Nat.mod_mul_left_mod]
    have h2 : (n % B ^ (k + 1)) / B = (n / B) % B ^ k := by
      rw [hpow2, Nat.mod_mul_right_div_self]
    rw [h1, h2, ih]

/-- Exact LSB-first carry-out after `w` base-`B` digits of `x + y + c`. -/
def carryOut (B : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, c, _, _ => c
  | w + 1, c, x, y => carryOut B w ((x % B + y % B + c) / B) (x / B) (y / B)

/-- Exact sum of the `w` output digits produced by LSB-first ripple addition of `x + y + c`. -/
def addDigitSum (B : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | w + 1, c, x, y =>
    (x % B + y % B + c) % B + addDigitSum B w ((x % B + y % B + c) / B) (x / B) (y / B)

theorem nat_add3_mod (B x y c : Nat) :
    (x + y + c) % B = (x % B + y % B + c) % B := by
  have hx : x = B * (x / B) + x % B := (Nat.div_add_mod x B).symm
  have hy : y = B * (y / B) + y % B := (Nat.div_add_mod y B).symm
  conv => lhs; rw [hx, hy]
  have hr : B * (x / B) + x % B + (B * (y / B) + y % B) + c =
      (x % B + y % B + c) + B * (x / B + y / B) := by
    rw [Nat.mul_add]; omega
  rw [hr, Nat.add_mul_mod_self_left]

theorem nat_add3_div (B x y c : Nat) (hB : 0 < B) :
    (x + y + c) / B = x / B + y / B + (x % B + y % B + c) / B := by
  have hx : x = B * (x / B) + x % B := (Nat.div_add_mod x B).symm
  have hy : y = B * (y / B) + y % B := (Nat.div_add_mod y B).symm
  conv => lhs; rw [hx, hy]
  have hr : B * (x / B) + x % B + (B * (y / B) + y % B) + c =
      (x % B + y % B + c) + B * (x / B + y / B) := by
    rw [Nat.mul_add]; omega
  rw [hr, Nat.add_mul_div_left _ _ hB]
  omega

/-- Exact Bridge 1: LSB-first ripple-adder output digit sum equals `digitSum B w (x + y + c)`. -/
theorem addDigitSum_eq_digitSum (B : Nat) (hB : 0 < B) :
    ∀ w c x y, addDigitSum B w c x y = digitSum B w (x + y + c) := by
  intro w
  induction w with
  | zero => intro c x y; rfl
  | succ k ih =>
    intro c x y
    simp only [addDigitSum, digitSum]
    rw [nat_add3_mod B x y c, nat_add3_div B x y c hB, ih]

/-- Exact Bridge 2: LSB-first ripple-adder carry-out relates to `(x + y + c) / B^w`. -/
theorem carryOut_add_divs (B : Nat) (hB : 0 < B) :
    ∀ w c x y, x / B ^ w + y / B ^ w + carryOut B w c x y = (x + y + c) / B ^ w := by
  intro w
  induction w with
  | zero => intro c x y; simp [carryOut]
  | succ k ih =>
    intro c x y
    simp only [carryOut]
    have hpow : B ^ (k + 1) = B * B ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [nat_add3_div B x y c hB]
    exact ih ((x % B + y % B + c) / B) (x / B) (y / B)

theorem carryOut_eq_div_pow (B : Nat) (hB : 0 < B) (w c x y : Nat)
    (hx : x < B ^ w) (hy : y < B ^ w) :
    carryOut B w c x y = (x + y + c) / B ^ w := by
  have h := carryOut_add_divs B hB w c x y
  rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] at h
  omega

/-- Exact Bridge 3 (Binary Full Popcount): For `x, y < 2^w`, the full `popcount (w + 1) (x + y)`
    equals `popcount w (x + y) + carryOut 2 w 0 x y`. -/
theorem binary_full_popcount_split (w x y : Nat) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    popcount (w + 1) (x + y) = popcount w (x + y) + carryOut 2 w 0 x y := by
  have hdiv_lt : (x + y) / 2 ^ w < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega : 0 < 2))]
    omega
  have hsplit : ∀ k n, digitSum 2 (k + 1) n = digitSum 2 k n + (n / 2 ^ k) % 2 := by
    intro k
    induction k with
    | zero => intro n; simp [digitSum]
    | succ m ih =>
      intro n
      calc digitSum 2 (m + 2) n
          = n % 2 + digitSum 2 (m + 1) (n / 2) := rfl
        _ = n % 2 + (digitSum 2 m (n / 2) + (n / 2 / 2 ^ m) % 2) := by rw [ih (n / 2)]
        _ = (n % 2 + digitSum 2 m (n / 2)) + (n / (2 * 2 ^ m)) % 2 := by
            rw [Nat.div_div_eq_div_mul]; omega
        _ = digitSum 2 (m + 1) n + (n / 2 ^ (m + 1)) % 2 := by
            rw [show 2 * 2 ^ m = 2 ^ (m + 1) by rw [Nat.pow_succ, Nat.mul_comm]]; rfl
  unfold popcount
  rw [hsplit w (x + y)]
  have hco := carryOut_eq_div_pow 2 (by omega) w 0 x y hx hy
  simp only [Nat.add_zero] at hco
  rw [← hco]
  have hco_lt : carryOut 2 w 0 x y < 2 := by rw [hco]; exact hdiv_lt
  rw [Nat.mod_eq_of_lt hco_lt]

-- ============================================================================
-- SECTION 4: Even-Radix (B = 2m) Digit-Pair Parity Sum Identities
-- ============================================================================

theorem sumNat_parity_range (a len : Nat) :
    sumNat len (fun y => paritySign (a + y)) =
      if len % 2 = 0 then 0 else paritySign a := by
  induction len with
  | zero => simp
  | succ k ih =>
    rw [sumNat_succ, ih]
    by_cases hk : k % 2 = 0
    · have h1 : (k + 1) % 2 ≠ 0 := by omega
      have hpk : paritySign k = 1 := by unfold paritySign; simp [hk]
      simp only [hk, h1, ↓reduceIte, paritySign_add, hpk]
      omega
    · have h1 : (k + 1) % 2 = 0 := by omega
      have hpk : paritySign k = -1 := by unfold paritySign; simp [hk]
      simp only [hk, h1, ↓reduceIte, paritySign_add, hpk]
      omega

theorem sumNat_ite_lt (n t : Nat) (ht : t ≤ n) (f : Nat → Int) :
    sumNat n (fun y => if y < t then f y else 0) = sumNat t f := by
  have h := sumNat_split t (n - t) (fun y => if y < t then f y else 0)
  rw [Nat.add_sub_of_le ht] at h
  rw [h]
  have h1 : sumNat t (fun y => if y < t then f y else 0) = sumNat t f := by
    apply sumNat_congr; intro y hy; simp [hy]
  have h2 : sumNat (n - t) (fun j => if t + j < t then f (t + j) else 0) = 0 := by
    rw [sumNat_congr (g := fun _ => 0)]
    · exact sumNat_zero_fn _
    · intro j _; simp [show ¬ (t + j < t) by omega]
  rw [h1, h2, Int.add_zero]

theorem sumNat_ite_ge (n t : Nat) (ht : t ≤ n) (f : Nat → Int) :
    sumNat n (fun y => if t ≤ y then f y else 0) = sumNat (n - t) (fun j => f (t + j)) := by
  have h := sumNat_split t (n - t) (fun y => if t ≤ y then f y else 0)
  rw [Nat.add_sub_of_le ht] at h
  rw [h]
  have h1 : sumNat t (fun y => if t ≤ y then f y else 0) = 0 := by
    rw [sumNat_congr (g := fun _ => 0)]
    · exact sumNat_zero_fn _
    · intro y hy; simp [show ¬ (t ≤ y) by omega]
  have h2 : sumNat (n - t) (fun j => if t ≤ t + j then f (t + j) else 0) =
      sumNat (n - t) (fun j => f (t + j)) := by
    apply sumNat_congr; intro j _; simp [show t ≤ t + j by omega]
  rw [h1, h2, Int.zero_add]

theorem sumNat_odd_neg_one (m : Nat) :
    sumNat (2 * m) (fun x => if x % 2 = 0 then 0 else (-1 : Int)) = -(m : Int) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2, sumNat_succ, sumNat_succ, ih]
    simp [show (2 * k) % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega]
    omega

theorem sumNat_odd_pos_one (m : Nat) :
    sumNat (2 * m) (fun x => if x % 2 = 0 then 0 else (1 : Int)) = (m : Int) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2, sumNat_succ, sumNat_succ, ih]
    simp [show (2 * k) % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega]

theorem sumNat_even_neg_one (m : Nat) :
    sumNat (2 * m) (fun x => if x % 2 = 0 then (-1 : Int) else 0) = -(m : Int) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2, sumNat_succ, sumNat_succ, ih]
    simp [show (2 * k) % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega]
    omega

theorem sumNat_even_pos_one (m : Nat) :
    sumNat (2 * m) (fun x => if x % 2 = 0 then (1 : Int) else 0) = (m : Int) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2, sumNat_succ, sumNat_succ, ih]
    simp [show (2 * k) % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega]

/-- Helper: if `2*m ≤ s < 4*m`, then `s % (2*m) = s - 2*m`. -/
theorem mod_sub_of_ge_lt (B s : Nat) (hge : B ≤ s) (hlt : s < B + B) :
    s % B = s - B := by
  have heq : s = (s - B) + B := by omega
  have hlt' : s - B < B := by omega
  conv => lhs; rw [heq]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt']

/-- Even-radix `B = 2m` output-parity digit sum `a = ∑_{x+y < 2m} (-1)^((x+y) % 2m) = -m`. -/
theorem evenRadix_a_eq (m : Nat) :
    sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
      if x + y < 2 * m then paritySign ((x + y) % (2 * m)) else 0)) = -(m : Int) := by
  rw [sumNat_congr (g := fun x => if x % 2 = 0 then 0 else (-1 : Int))]
  · exact sumNat_odd_neg_one m
  · intro x hx
    rw [sumNat_congr (g := fun y => if y < 2 * m - x then paritySign (x + y) else 0)]
    · rw [sumNat_ite_lt (2 * m) (2 * m - x) (by omega), sumNat_parity_range]
      by_cases hxe : x % 2 = 0
      · have hlen : (2 * m - x) % 2 = 0 := by omega
        simp [hxe, hlen]
      · have hlen : (2 * m - x) % 2 = 1 := by omega
        have hpx : paritySign x = -1 := by unfold paritySign; simp [hxe]
        simp [hxe, hlen, hpx]
    · intro y _
      by_cases hlt : x + y < 2 * m
      · have hlt' : y < 2 * m - x := by omega
        simp [hlt, hlt', Nat.mod_eq_of_lt hlt]
      · have hlt' : ¬ (y < 2 * m - x) := by omega
        simp [hlt, hlt']

/-- Even-radix `B = 2m` output-parity digit sum `b = ∑_{x+y ≥ 2m} (-1)^((x+y) % 2m) = +m`. -/
theorem evenRadix_b_eq (m : Nat) :
    sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
      if 2 * m ≤ x + y then paritySign ((x + y) % (2 * m)) else 0)) = (m : Int) := by
  rw [sumNat_congr (g := fun x => if x % 2 = 0 then 0 else (1 : Int))]
  · exact sumNat_odd_pos_one m
  · intro x hx
    rw [sumNat_congr (g := fun y => if 2 * m - x ≤ y then paritySign (x + y) else 0)]
    · rw [sumNat_ite_ge (2 * m) (2 * m - x) (by omega)]
      have hsub : 2 * m - (2 * m - x) = x := by omega
      rw [hsub]
      rw [sumNat_congr (g := fun j => paritySign (2 * m + j))]
      · rw [sumNat_parity_range]
        have hp2m : paritySign (2 * m) = 1 := by unfold paritySign; simp
        rw [hp2m]
      · intro j _; congr 1; omega
    · intro y hy
      by_cases hge : 2 * m ≤ x + y
      · have hge' : 2 * m - x ≤ y := by omega
        have hmod : (x + y) % (2 * m) = x + y - 2 * m :=
          mod_sub_of_ge_lt (2 * m) (x + y) hge (by omega)
        have hpeq : paritySign (x + y - 2 * m) = paritySign (x + y) := by
          unfold paritySign
          simp [show (x + y - 2 * m) % 2 = (x + y) % 2 by omega]
        simp [hge, hge', hmod, hpeq]
      · have hge' : ¬ (2 * m - x ≤ y) := by omega
        simp [hge, hge']

/-- Even-radix `B = 2m` output-parity digit sum `c = ∑_{x+y+1 < 2m} (-1)^((x+y+1) % 2m) = -m`. -/
theorem evenRadix_c_eq (m : Nat) :
    sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
      if x + y + 1 < 2 * m then paritySign ((x + y + 1) % (2 * m)) else 0)) = -(m : Int) := by
  rw [sumNat_congr (g := fun x => if x % 2 = 0 then (-1 : Int) else 0)]
  · exact sumNat_even_neg_one m
  · intro x hx
    rw [sumNat_congr (g := fun y => if y < 2 * m - 1 - x then paritySign ((x + 1) + y) else 0)]
    · rw [sumNat_ite_lt (2 * m) (2 * m - 1 - x) (by omega), sumNat_parity_range]
      by_cases hxe : x % 2 = 0
      · have hlen : (2 * m - 1 - x) % 2 = 1 := by omega
        have hpx : paritySign (x + 1) = -1 := by
          unfold paritySign; simp [show (x + 1) % 2 = 1 by omega]
        simp [hxe, hlen, hpx]
      · have hlen : (2 * m - 1 - x) % 2 = 0 := by omega
        simp [hxe, hlen]
    · intro y _
      by_cases hlt : x + y + 1 < 2 * m
      · have hlt' : y < 2 * m - 1 - x := by omega
        have hmod : (x + y + 1) % (2 * m) = x + 1 + y := by
          rw [Nat.mod_eq_of_lt hlt]; omega
        simp only [hlt, hlt', ↓reduceIte, hmod]
      · have hlt' : ¬ (y < 2 * m - 1 - x) := by omega
        simp [hlt, hlt']

/-- Even-radix `B = 2m` output-parity digit sum `r = ∑_{x+y+1 ≥ 2m} (-1)^((x+y+1) % 2m) = +m`. -/
theorem evenRadix_r_eq (m : Nat) :
    sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
      if 2 * m ≤ x + y + 1 then paritySign ((x + y + 1) % (2 * m)) else 0)) = (m : Int) := by
  rw [sumNat_congr (g := fun x => if x % 2 = 0 then (1 : Int) else 0)]
  · exact sumNat_even_pos_one m
  · intro x hx
    rw [sumNat_congr (g := fun y => if 2 * m - 1 - x ≤ y then paritySign ((x + 1) + y) else 0)]
    · rw [sumNat_ite_ge (2 * m) (2 * m - 1 - x) (by omega)]
      have hsub : 2 * m - (2 * m - 1 - x) = x + 1 := by omega
      rw [hsub]
      rw [sumNat_congr (g := fun j => paritySign (2 * m + j))]
      · rw [sumNat_parity_range]
        have hp2m : paritySign (2 * m) = 1 := by unfold paritySign; simp
        rw [hp2m]
        by_cases hxe : x % 2 = 0
        · simp [hxe, show (x + 1) % 2 = 1 by omega]
        · simp [hxe, show (x + 1) % 2 = 0 by omega]
      · intro j _; congr 1; omega
    · intro y hy
      by_cases hge : 2 * m ≤ x + y + 1
      · have hge' : 2 * m - 1 - x ≤ y := by omega
        have hmod : (x + y + 1) % (2 * m) = x + y + 1 - 2 * m :=
          mod_sub_of_ge_lt (2 * m) (x + y + 1) hge (by omega)
        have hpeq : paritySign (x + y + 1 - 2 * m) = paritySign (x + 1 + y) := by
          unfold paritySign
          simp [show (x + y + 1 - 2 * m) % 2 = (x + 1 + y) % 2 by omega]
        simp [hge, hge', hmod, hpeq]
      · have hge' : ¬ (2 * m - 1 - x ≤ y) := by omega
        simp [hge, hge']

/-- Even-radix `B = 2m` input-parity Kill sum `k = ∑_{x+y+1 < 2m} (-1)^(x+y) = +m`. -/
theorem evenRadix_inKill_eq (m : Nat) :
    sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
      if x + y + 1 < 2 * m then paritySign (x + y) else 0)) = (m : Int) := by
  have h := evenRadix_c_eq m
  have hneg :
      sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
        if x + y + 1 < 2 * m then paritySign (x + y) else 0)) =
      -sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
        if x + y + 1 < 2 * m then paritySign ((x + y + 1) % (2 * m)) else 0)) := by
    rw [← sumNat_neg]
    apply sumNat_congr
    intro x _
    rw [← sumNat_neg]
    apply sumNat_congr
    intro y _
    by_cases hlt : x + y + 1 < 2 * m
    · simp only [hlt, ↓reduceIte, Nat.mod_eq_of_lt hlt, paritySign_succ]
      omega
    · simp [hlt]
  rw [hneg, h]; omega

/-- Even-radix `B = 2m` input-parity Propagate sum `p = ∑_{x+y = 2m-1} (-1)^(x+y) = -2m`. -/
theorem evenRadix_inProp_eq (m : Nat) :
    sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
      if x + y + 1 = 2 * m then paritySign (x + y) else 0)) = -(2 * (m : Int)) := by
  rw [sumNat_congr (g := fun _ => (-1 : Int))]
  · induction m with
    | zero => rfl
    | succ k ih =>
      have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h2, sumNat_succ, sumNat_succ, ih]; omega
  · intro x hx
    rw [sumNat_congr (g := fun y => if y = 2 * m - 1 - x then (-1 : Int) else 0)]
    · exact sumNat_ite_eq (2 * m) (2 * m - 1 - x) (-1) (by omega)
    · intro y _
      by_cases heq : x + y + 1 = 2 * m
      · have hy' : y = 2 * m - 1 - x := by omega
        have hp : paritySign (x + y) = -1 := by
          unfold paritySign; simp [show (x + y) % 2 = 1 by omega]
        simp only [heq, ↓reduceIte]
        rw [hp]
        simp [hy']
      · have hy' : y ≠ 2 * m - 1 - x := by omega
        simp [heq, hy']

/-- Even-radix `B = 2m` input-parity Generate sum `g = ∑_{x+y ≥ 2m} (-1)^(x+y) = +m`. -/
theorem evenRadix_inGen_eq (m : Nat) :
    sumNat (2 * m) (fun x => sumNat (2 * m) (fun y =>
      if 2 * m ≤ x + y then paritySign (x + y) else 0)) = (m : Int) := by
  rw [← evenRadix_b_eq m]
  apply sumNat_congr; intro x hx
  apply sumNat_congr; intro y hy
  by_cases hge : 2 * m ≤ x + y
  · simp only [hge, ↓reduceIte]
    have hmod : (x + y) % (2 * m) = x + y - 2 * m :=
      mod_sub_of_ge_lt (2 * m) (x + y) hge (by omega)
    rw [hmod]
    unfold paritySign
    simp [show (x + y - 2 * m) % 2 = (x + y) % 2 by omega]
  · simp [hge]

theorem rippleOp_at_zero (L : Nat) (k p g : Int) (v : Nat → Int) :
    rippleOp L k p g v 0 = k * sumNat (L + 1) v + p * v 0 := by
  unfold rippleOp; simp

theorem rippleOp_at_one (L : Nat) (k p g : Int) (v : Nat → Int) :
    rippleOp L k p g v 1 = g * sumNat (L + 1) v := by
  unfold rippleOp; simp

theorem rippleOp_at_mid (L : Nat) (k p g : Int) (v : Nat → Int) (i : Nat)
    (hi2 : 2 ≤ i) (hiL : i ≤ L) :
    rippleOp L k p g v i = p * v (i - 1) := by
  unfold rippleOp
  have hne0 : i ≠ 0 := by omega
  have hne1 : i ≠ 1 := by omega
  simp [hne0, hne1, hiL]

theorem rippleOp_at_out (L : Nat) (k p g : Int) (v : Nat → Int) (i : Nat)
    (hL : 1 ≤ L) (hi : L < i) :
    rippleOp L k p g v i = 0 := by
  unfold rippleOp
  have hne0 : i ≠ 0 := by omega
  have hne1 : i ≠ 1 := by omega
  have hnle : ¬ (i ≤ L) := by omega
  simp [hne0, hne1, hnle]

theorem rippleOp_hom (L : Nat) (k p g : Int) (c : Int) (v : Nat → Int) (i : Nat) :
    rippleOp L k p g (smulVec c v) i = c * rippleOp L k p g v i := by
  unfold rippleOp smulVec
  rw [sumNat_mul_left]
  split
  · rw [← Int.mul_assoc k c, Int.mul_comm k c, Int.mul_assoc c k,
        ← Int.mul_assoc p c, Int.mul_comm p c, Int.mul_assoc c p, ← Int.mul_add]
  · split
    · rw [← Int.mul_assoc g c, Int.mul_comm g c, Int.mul_assoc c g]
    · split
      · rw [← Int.mul_assoc p c, Int.mul_comm p c, Int.mul_assoc c p]
      · simp

/-- Key sum identity for `rippleOp`: `S(M v) = (k + p + g) * S(v) - p * v L`. -/
theorem rippleOp_sum (L : Nat) (hL : 1 ≤ L) (k p g : Int) (v : Nat → Int) :
    sumNat (L + 1) (rippleOp L k p g v) = (k + p + g) * sumNat (L + 1) v - p * v L := by
  rw [sumNat_succ_front, sumNat_pred_front L hL (fun j => rippleOp L k p g v (j + 1))]
  rw [rippleOp_at_zero, show (0 : Nat) + 1 = 1 from rfl, rippleOp_at_one]
  have hrrest : sumNat (L - 1) (fun i => rippleOp L k p g v (i + 1 + 1)) =
      p * sumNat (L - 1) (fun i => v (i + 1)) := by
    rw [← sumNat_mul_left]
    apply sumNat_congr
    intro i hi
    rw [rippleOp_at_mid L k p g v (i + 1 + 1) (by omega) (by omega)]
    rfl
  rw [hrrest]
  have hsumv : sumNat (L + 1) v = v 0 + sumNat (L - 1) (fun j => v (j + 1)) + v L := by
    rw [sumNat_succ, sumNat_pred_front L hL v]
  have hsub : v 0 + sumNat (L - 1) (fun j => v (j + 1)) = sumNat (L + 1) v - v L := by omega
  have hpmul : p * v 0 + p * sumNat (L - 1) (fun j => v (j + 1)) =
      p * sumNat (L + 1) v - p * v L := by
    rw [← Int.mul_add, hsub, Int.mul_sub]
  have hadd : (k + p + g) * sumNat (L + 1) v =
      k * sumNat (L + 1) v + p * sumNat (L + 1) v + g * sumNat (L + 1) v := by
    rw [Int.add_mul, Int.add_mul]
  rw [hadd]
  omega

/-- Subdiagonal shift law for `rippleOp`: for `1 ≤ i ≤ L` and `r < i`,
    `(M^[r] v) i = p^r * v (i - r)`. -/
theorem rippleOp_shift_lt (L : Nat) (k p g : Int) :
    ∀ r v i, 1 ≤ i → i ≤ L → r < i →
      iterOp (rippleOp L k p g) r v i = p ^ r * v (i - r) := by
  intro r
  induction r with
  | zero =>
    intro v i _ _ _
    simp
  | succ m ih =>
    intro v i hi hiL hlt
    rw [iterOp_succ, rippleOp_at_mid L k p g _ i (by omega) hiL]
    rw [ih v (i - 1) (by omega) (by omega) (by omega)]
    have hsub : i - 1 - m = i - (m + 1) := by omega
    rw [hsub, Int.pow_succ, ← Int.mul_assoc, Int.mul_comm p (p ^ m)]

/-- Subdiagonal entry-from-1 law for `rippleOp`: for `1 ≤ i ≤ L` and `i ≤ t`,
    `(M^[t] v) i = g * p^(i - 1) * S(M^[t - i] v)`. -/
theorem rippleOp_shift_ge (L : Nat) (k p g : Int) :
    ∀ i t v, 1 ≤ i → i ≤ L → i ≤ t →
      iterOp (rippleOp L k p g) t v i =
        g * p ^ (i - 1) * sumNat (L + 1) (iterOp (rippleOp L k p g) (t - i) v) := by
  intro i
  induction i with
  | zero => intro _ _ h; omega
  | succ m ih =>
    intro t v _ hmL hmt
    cases m with
    | zero =>
      have ht : t = (t - 1) + 1 := by omega
      conv => lhs; rw [ht, iterOp_succ, rippleOp_at_one]
      simp
    | succ m' =>
      have ht : t = (t - 1) + 1 := by omega
      conv => lhs; rw [ht, iterOp_succ, rippleOp_at_mid L k p g _ (m' + 2) (by omega) hmL]
      have hsub : m' + 2 - 1 = m' + 1 := by omega
      rw [hsub, ih (t - 1) v (by omega) (by omega) (by omega)]
      have hsub2 : t - 1 - (m' + 1) = t - (m' + 2) := by omega
      rw [hsub2, show m' + 1 - 1 = m' by omega, Int.pow_succ]
      rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm p g, Int.mul_assoc g p (p ^ m'),
          Int.mul_comm p (p ^ m')]

/-- **UNIVERSAL 3-PARAMETER RIPPLE-CARRY MATRIX ANNIHILATOR** (`∀ L ≥ 1, ∀ k, p, g ∈ ℤ`):
    `M_rip(L; k, p, g)^(L+1) v - (k + p + g) * M_rip(L; k, p, g)^L v + g * p^L * v = 0`
    on every coordinate `i ≤ L` and every vector `v`! -/
theorem rippleOp_annihilator (L : Nat) (hL : 1 ≤ L) (k p g : Int) (v : Nat → Int) :
    ∀ i, i < L + 1 →
      iterOp (rippleOp L k p g) (L + 1) v i -
        (k + p + g) * iterOp (rippleOp L k p g) L v i +
        g * p ^ L * v i = 0 := by
  have hpos : ∀ i, 1 ≤ i → i ≤ L →
      iterOp (rippleOp L k p g) (L + 1) v i -
        (k + p + g) * iterOp (rippleOp L k p g) L v i +
        g * p ^ L * v i = 0 := by
    intro i hi hiL
    rw [rippleOp_shift_ge L k p g i (L + 1) v hi hiL (by omega)]
    rw [rippleOp_shift_ge L k p g i L v hi hiL (by omega)]
    have hstep : L + 1 - i = (L - i) + 1 := by omega
    rw [hstep, iterOp_succ, rippleOp_sum L hL k p g]
    rw [rippleOp_shift_lt L k p g (L - i) v L hL (Nat.le_refl L) (by omega)]
    have hLi : L - (L - i) = i := by omega
    rw [hLi]
    have hpow : p ^ (i - 1) * (p * p ^ (L - i)) = p ^ L := by
      have hexp : i - 1 + 1 + (L - i) = L := by omega
      rw [← Int.mul_assoc, ← Int.pow_succ, ← int_pow_add, hexp]
    rw [Int.mul_sub]
    have hcomm :
        g * p ^ (i - 1) * ((k + p + g) * sumNat (L + 1) (iterOp (rippleOp L k p g) (L - i) v)) =
        (k + p + g) * (g * p ^ (i - 1) * sumNat (L + 1) (iterOp (rippleOp L k p g) (L - i) v)) := by
      rw [← Int.mul_assoc, Int.mul_comm (g * p ^ (i - 1)) (k + p + g), Int.mul_assoc]
    have hlast :
        g * p ^ (i - 1) * (p * (p ^ (L - i) * v i)) = g * p ^ L * v i := by
      rw [← Int.mul_assoc p (p ^ (L - i)) (v i)]
      rw [← Int.mul_assoc (g * p ^ (i - 1)), Int.mul_assoc g (p ^ (i - 1)) (p * p ^ (L - i))]
      rw [hpow]
    rw [hcomm, hlast]
    omega
  have hsum : sumNat (L + 1) (iterOp (rippleOp L k p g) (L + 1) v) -
      (k + p + g) * sumNat (L + 1) (iterOp (rippleOp L k p g) L v) +
      g * p ^ L * sumNat (L + 1) v = 0 := by
    rw [iterOp_succ, rippleOp_sum L hL k p g]
    rw [rippleOp_shift_ge L k p g L L v hL (Nat.le_refl L) (Nat.le_refl L)]
    simp only [Nat.sub_self, iterOp_zero]
    have hpow : p * (g * p ^ (L - 1)) = g * p ^ L := by
      have hexp : (L - 1).succ = L := by omega
      rw [Int.mul_comm p, Int.mul_assoc, ← Int.pow_succ, hexp]
    rw [← Int.mul_assoc p (g * p ^ (L - 1)), hpow]
    omega
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    let w : Nat → Int := fun j =>
      iterOp (rippleOp L k p g) (L + 1) v j -
        (k + p + g) * iterOp (rippleOp L k p g) L v j + g * p ^ L * v j
    have hsumw : sumNat (L + 1) w = 0 := by
      show sumNat (L + 1) (fun j =>
        iterOp (rippleOp L k p g) (L + 1) v j -
          (k + p + g) * iterOp (rippleOp L k p g) L v j + g * p ^ L * v j) = 0
      rw [sumNat_add, sumNat_sub, sumNat_mul_left, sumNat_mul_left]
      exact hsum
    rw [sumNat_succ_front] at hsumw
    have htail : sumNat L (fun j => w (j + 1)) = 0 := by
      rw [sumNat_congr (g := fun _ => 0)]
      · exact sumNat_zero_fn L
      · intro j hj
        exact hpos (j + 1) (by omega) (by omega)
    rw [htail, Int.add_zero] at hsumw
    exact hsumw
  · exact hpos i (by omega) (by omega)

/-- Initial values of `rippleOp`: for `0 ≤ w ≤ L`, `S(M_rip^w e_0) = (k + p + g)^w`. -/
theorem rippleOp_init_sum (L : Nat) (hL : 1 ≤ L) (k p g : Int) :
    ∀ w, w ≤ L → sumNat (L + 1) (iterOp (rippleOp L k p g) w (basisVec 0)) = (k + p + g) ^ w := by
  intro w
  induction w with
  | zero =>
    intro _
    simp only [iterOp_zero, Int.pow_zero]
    unfold basisVec
    exact sumNat_ite_eq (L + 1) 0 1 (by omega)
  | succ m ih =>
    intro hmL
    rw [iterOp_succ, rippleOp_sum L hL k p g, ih (by omega)]
    rw [rippleOp_shift_lt L k p g m (basisVec 0) L hL (Nat.le_refl L) (by omega)]
    have hne : L - m ≠ 0 := by omega
    simp only [basisVec, hne, ↓reduceIte, Int.mul_zero, Int.sub_zero]
    rw [Int.pow_succ, Int.mul_comm]

theorem runOp_at_zero (L : Nat) (a b c r : Int) (v : Nat → Int) :
    runOp L a b c r v 0 = a * v 0 + c * sumNat L (fun j => v (j + 1)) := by
  unfold runOp; simp

theorem runOp_at_one (L : Nat) (a b c r : Int) (v : Nat → Int) :
    runOp L a b c r v 1 = b * v 0 := by
  unfold runOp; simp

theorem runOp_at_mid (L : Nat) (a b c r : Int) (v : Nat → Int) (i : Nat)
    (hi2 : 2 ≤ i) (hiL : i ≤ L) :
    runOp L a b c r v i = r * v (i - 1) := by
  unfold runOp
  have hne0 : i ≠ 0 := by omega
  have hne1 : i ≠ 1 := by omega
  simp [hne0, hne1, hiL]

theorem runOp_hom (L : Nat) (a b c r : Int) (s : Int) (v : Nat → Int) (i : Nat) :
    runOp L a b c r (smulVec s v) i = s * runOp L a b c r v i := by
  unfold runOp smulVec
  rw [sumNat_mul_left]
  split
  · rw [← Int.mul_assoc a s, Int.mul_comm a s, Int.mul_assoc s a,
        ← Int.mul_assoc c s, Int.mul_comm c s, Int.mul_assoc s c, ← Int.mul_add]
  · split
    · rw [← Int.mul_assoc b s, Int.mul_comm b s, Int.mul_assoc s b]
    · split
      · rw [← Int.mul_assoc r s, Int.mul_comm r s, Int.mul_assoc s r]
      · simp

/-- Telescoping 2-step identity on coordinate `0` of `runOp`:
    `(M^2 v)_0 - (a + r) (M v)_0 + (a r - b c) v_0 = - c r v_L`. -/
theorem runOp_coord0_twoStep (L : Nat) (hL : 1 ≤ L) (a b c r : Int) (v : Nat → Int) :
    runOp L a b c r (runOp L a b c r v) 0 -
      (a + r) * runOp L a b c r v 0 +
      (a * r - b * c) * v 0 = -(c * r * v L) := by
  have hM0 := runOp_at_zero L a b c r v
  have hM20 := runOp_at_zero L a b c r (runOp L a b c r v)
  have htail : sumNat L (fun j => runOp L a b c r v (j + 1)) =
      b * v 0 + r * sumNat (L - 1) (fun j => v (j + 1)) := by
    rw [sumNat_pred_front L hL (fun j => runOp L a b c r v (j + 1))]
    rw [show (0 : Nat) + 1 = 1 from rfl, runOp_at_one]
    congr 1
    rw [← sumNat_mul_left]
    apply sumNat_congr
    intro j hj
    rw [runOp_at_mid L a b c r v (j + 1 + 1) (by omega) (by omega)]
    rfl
  have hsplitv : sumNat L (fun j => v (j + 1)) =
      sumNat (L - 1) (fun j => v (j + 1)) + v L := by
    rw [sumNat_pred_back L hL (fun j => v (j + 1))]
    congr 1; congr 1; omega
  rw [hM20, htail]
  let S := sumNat (L - 1) (fun j => v (j + 1))
  have hM0' : runOp L a b c r v 0 = a * v 0 + c * (S + v L) := by rw [hM0, hsplitv]
  have h1 : (a + r) * runOp L a b c r v 0 = a * runOp L a b c r v 0 + r * runOp L a b c r v 0 :=
    Int.add_mul a r _
  rw [h1, hM0']
  rw [Int.mul_add c (b * v 0), Int.mul_add r (a * v 0), Int.mul_add c S (v L),
      Int.mul_add r (c * S) (c * v L), Int.sub_mul]
  have hcb : c * (b * v 0) = b * c * v 0 := by rw [← Int.mul_assoc, Int.mul_comm c b]
  have hra : r * (a * v 0) = a * r * v 0 := by rw [← Int.mul_assoc, Int.mul_comm r a]
  have hcrS : c * (r * S) = r * (c * S) := by rw [← Int.mul_assoc, Int.mul_comm c r, Int.mul_assoc]
  have hrcv : r * (c * v L) = c * r * v L := by rw [← Int.mul_assoc, Int.mul_comm r c]
  rw [hcb, hra, hcrS, hrcv]
  omega

/-- Subdiagonal shift law for `runOp`: for `1 ≤ i ≤ L` and `k < i`,
    `(M^[k] v) i = r^k * v (i - k)`. -/
theorem runOp_shift_lt (L : Nat) (a b c r : Int) :
    ∀ k v i, 1 ≤ i → i ≤ L → k < i →
      iterOp (runOp L a b c r) k v i = r ^ k * v (i - k) := by
  intro k
  induction k with
  | zero => intro v i _ _ _; simp
  | succ m ih =>
    intro v i hi hiL hlt
    rw [iterOp_succ, runOp_at_mid L a b c r _ i (by omega) hiL]
    rw [ih v (i - 1) (by omega) (by omega) (by omega)]
    have hsub : i - 1 - m = i - (m + 1) := by omega
    rw [hsub, Int.pow_succ, ← Int.mul_assoc, Int.mul_comm r (r ^ m)]

/-- Subdiagonal entry-from-0 law for `runOp`: for `1 ≤ i ≤ L` and `i ≤ t`,
    `(M^[t] v) i = b * r^(i - 1) * (M^[t - i] v) 0`. -/
theorem runOp_shift_ge (L : Nat) (a b c r : Int) :
    ∀ i t v, 1 ≤ i → i ≤ L → i ≤ t →
      iterOp (runOp L a b c r) t v i =
        b * r ^ (i - 1) * iterOp (runOp L a b c r) (t - i) v 0 := by
  intro i
  induction i with
  | zero => intro _ _ h; omega
  | succ m ih =>
    intro t v _ hmL hmt
    cases m with
    | zero =>
      have ht : t = (t - 1) + 1 := by omega
      conv => lhs; rw [ht, iterOp_succ, runOp_at_one]
      simp
    | succ m' =>
      have ht : t = (t - 1) + 1 := by omega
      conv => lhs; rw [ht, iterOp_succ, runOp_at_mid L a b c r _ (m' + 2) (by omega) hmL]
      have hsub : m' + 2 - 1 = m' + 1 := by omega
      rw [hsub, ih (t - 1) v (by omega) (by omega) (by omega)]
      have hsub2 : t - 1 - (m' + 1) = t - (m' + 2) := by omega
      rw [hsub2, show m' + 1 - 1 = m' by omega, Int.pow_succ]
      rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm r b, Int.mul_assoc b r (r ^ m'),
          Int.mul_comm r (r ^ m')]

/-- **UNIVERSAL 4-PARAMETER CARRY-RUN MATRIX ANNIHILATOR** (`∀ L ≥ 1, ∀ a, b, c, r ∈ ℤ`):
    `M_run^(L+2) v - (a+r) M_run^(L+1) v + (a*r - b*c) M_run^L v + b*c*r^L * v = 0`
    on every coordinate `i ≤ L` and every vector `v`! -/
theorem runOp_annihilator (L : Nat) (hL : 1 ≤ L) (a b c r : Int) (v : Nat → Int) :
    ∀ i, i < L + 1 →
      iterOp (runOp L a b c r) (L + 2) v i -
        (a + r) * iterOp (runOp L a b c r) (L + 1) v i +
        (a * r - b * c) * iterOp (runOp L a b c r) L v i +
        b * c * r ^ L * v i = 0 := by
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    have h2 := runOp_coord0_twoStep L hL a b c r (iterOp (runOp L a b c r) L v)
    change iterOp (runOp L a b c r) (L + 2) v 0 -
        (a + r) * iterOp (runOp L a b c r) (L + 1) v 0 +
        (a * r - b * c) * iterOp (runOp L a b c r) L v 0 =
      -(c * r * iterOp (runOp L a b c r) L v L) at h2
    rw [runOp_shift_ge L a b c r L L v hL (Nat.le_refl L) (Nat.le_refl L)] at h2
    simp only [Nat.sub_self, iterOp_zero] at h2
    have hpow : c * r * (b * r ^ (L - 1) * v 0) = b * c * r ^ L * v 0 := by
      have hexp : (L - 1).succ = L := by omega
      calc c * r * (b * r ^ (L - 1) * v 0)
          = (c * r * (b * r ^ (L - 1))) * v 0 := (Int.mul_assoc _ _ _).symm
        _ = (c * (r * b) * r ^ (L - 1)) * v 0 := by
            rw [← Int.mul_assoc (c * r) b (r ^ (L - 1)), Int.mul_assoc c r b]
        _ = (b * c * (r ^ (L - 1) * r)) * v 0 := by
            rw [Int.mul_comm r b, ← Int.mul_assoc c b r, Int.mul_comm c b,
                Int.mul_assoc (b * c) r (r ^ (L - 1)), Int.mul_comm r (r ^ (L - 1))]
        _ = b * c * r ^ L * v 0 := by rw [← Int.pow_succ, hexp]
    rw [hpow] at h2
    omega
  · have hi1 : 1 ≤ i := by omega
    have hiL : i ≤ L := by omega
    rw [runOp_shift_ge L a b c r i (L + 2) v hi1 hiL (by omega)]
    rw [runOp_shift_ge L a b c r i (L + 1) v hi1 hiL (by omega)]
    rw [runOp_shift_ge L a b c r i L v hi1 hiL (by omega)]
    have h2 := runOp_coord0_twoStep L hL a b c r (iterOp (runOp L a b c r) (L - i) v)
    change iterOp (runOp L a b c r) (L - i + 2) v 0 -
        (a + r) * iterOp (runOp L a b c r) (L - i + 1) v 0 +
        (a * r - b * c) * iterOp (runOp L a b c r) (L - i) v 0 =
      -(c * r * iterOp (runOp L a b c r) (L - i) v L) at h2
    have heq2 : L + 2 - i = L - i + 2 := by omega
    have heq1 : L + 1 - i = L - i + 1 := by omega
    rw [heq2, heq1]
    rw [runOp_shift_lt L a b c r (L - i) v L hL (Nat.le_refl L) (by omega)] at h2
    have hLi : L - (L - i) = i := by omega
    rw [hLi] at h2
    have hmul : (b * r ^ (i - 1)) * (iterOp (runOp L a b c r) (L - i + 2) v 0 -
          (a + r) * iterOp (runOp L a b c r) (L - i + 1) v 0 +
          (a * r - b * c) * iterOp (runOp L a b c r) (L - i) v 0) =
        (b * r ^ (i - 1)) * (-(c * r * (r ^ (L - i) * v i))) :=
      congrArg ((b * r ^ (i - 1)) * ·) h2
    rw [Int.mul_add, Int.mul_sub] at hmul
    have hterm1 : (b * r ^ (i - 1)) * ((a + r) * iterOp (runOp L a b c r) (L - i + 1) v 0) =
        (a + r) * (b * r ^ (i - 1) * iterOp (runOp L a b c r) (L - i + 1) v 0) := by
      rw [← Int.mul_assoc, Int.mul_comm (b * r ^ (i - 1)) (a + r), Int.mul_assoc]
    have hterm2 : (b * r ^ (i - 1)) * ((a * r - b * c) * iterOp (runOp L a b c r) (L - i) v 0) =
        (a * r - b * c) * (b * r ^ (i - 1) * iterOp (runOp L a b c r) (L - i) v 0) := by
      rw [← Int.mul_assoc, Int.mul_comm (b * r ^ (i - 1)) (a * r - b * c), Int.mul_assoc]
    have hrhs : (b * r ^ (i - 1)) * (-(c * r * (r ^ (L - i) * v i))) = -(b * c * r ^ L * v i) := by
      rw [Int.mul_neg]
      congr 1
      have hexp : i - 1 + 1 + (L - i) = L := by omega
      have hpow : r ^ (i - 1) * (r * r ^ (L - i)) = r ^ L := by
        rw [← Int.mul_assoc, ← Int.pow_succ, ← int_pow_add, hexp]
      calc (b * r ^ (i - 1)) * (c * r * (r ^ (L - i) * v i))
          = (b * r ^ (i - 1)) * ((c * (r * r ^ (L - i))) * v i) := by
              rw [Int.mul_assoc c r, ← Int.mul_assoc r (r ^ (L - i)) (v i),
                  ← Int.mul_assoc c (r * r ^ (L - i)) (v i)]
        _ = ((b * r ^ (i - 1)) * (c * (r * r ^ (L - i)))) * v i := (Int.mul_assoc _ _ _).symm
        _ = ((b * (r ^ (i - 1) * c)) * (r * r ^ (L - i))) * v i := by
              rw [← Int.mul_assoc (b * r ^ (i - 1)) c (r * r ^ (L - i)), Int.mul_assoc b (r ^ (i - 1)) c]
        _ = (b * c * (r ^ (i - 1) * (r * r ^ (L - i)))) * v i := by
              rw [Int.mul_comm (r ^ (i - 1)) c, ← Int.mul_assoc b c (r ^ (i - 1)),
                  Int.mul_assoc (b * c) (r ^ (i - 1)) (r * r ^ (L - i))]
        _ = b * c * r ^ L * v i := by rw [hpow]
    rw [hterm1, hterm2, hrhs] at hmul
    omega

-- ----------------------------------------------------------------------------
-- Hyperplane Embedding & Cyclic Rotation Intertwining for `M_run(L; -m, m, -m, m)`
-- ----------------------------------------------------------------------------

/-- Hyperplane embedding `ι : ℤ^(L+1) ↪ ℤ^(L+2)` appending `-∑_{j=0}^L v_j` at index `L + 1`. -/
def hyperplaneEmbed (L : Nat) (v : Nat → Int) : Nat → Int :=
  fun i => if i < L + 1 then v i else if i = L + 1 then -sumNat (L + 1) v else 0

/-- Scaled cyclic right-rotation `(m • rotR_{L+2})(u)` on `ℤ^(L+2)`. -/
def scaledRotR (L : Nat) (m : Int) (u : Nat → Int) : Nat → Int :=
  fun i => if i = 0 then m * u (L + 1) else if i < L + 2 then m * u (i - 1) else 0

theorem scaledRotR_at_zero (L : Nat) (m : Int) (u : Nat → Int) :
    scaledRotR L m u 0 = m * u (L + 1) := by
  unfold scaledRotR; simp

theorem scaledRotR_at_pos (L : Nat) (m : Int) (u : Nat → Int) (i : Nat)
    (hi0 : i ≠ 0) (hi : i < L + 2) :
    scaledRotR L m u i = m * u (i - 1) := by
  unfold scaledRotR; simp [hi0, hi]

/-- **FINITE INTERTWINING CERTIFICATE**:
    For ALL `L ≥ 1`, ALL `m ∈ ℤ`, and ALL `v : ℤ^(L+1)`:
    `ι(M_run(L; -m, m, -m, m) v) = (m • rotR_{L+2})(ι(v))`! -/
theorem runOp_cyclotomic_intertwines (L : Nat) (hL : 1 ≤ L) (m : Int) (v : Nat → Int) :
    hyperplaneEmbed L (runOp L (-m) m (-m) m v) = scaledRotR L m (hyperplaneEmbed L v) := by
  funext i
  unfold hyperplaneEmbed scaledRotR
  by_cases hi0 : i = 0
  · subst hi0
    simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.lt_irrefl]
    rw [runOp_at_zero, sumNat_succ_front, Int.neg_mul, Int.neg_mul, Int.mul_neg, Int.mul_add]
    omega
  · by_cases hi1 : i = 1
    · subst hi1
      have h1lt : 1 < L + 1 := by omega
      have h1lt2 : 1 < L + 2 := by omega
      simp only [h1lt, ↓reduceIte, hi0, h1lt2, Nat.sub_self, Nat.zero_lt_succ]
      rw [runOp_at_one]
    · by_cases hiL : i < L + 1
      · have hiL2 : i < L + 2 := by omega
        have him1 : i - 1 < L + 1 := by omega
        simp only [hiL, ↓reduceIte, hi0, hiL2, him1]
        rw [runOp_at_mid L (-m) m (-m) m v i (by omega) (by omega)]
      · by_cases hiE : i = L + 1
        · subst hiE
          have hlt2 : L + 1 < L + 2 := by omega
          have hLlt : L < L + 1 := by omega
          simp only [Nat.lt_irrefl, ↓reduceIte, hi0, hlt2, show L + 1 - 1 = L by omega, hLlt]
          have hsumM : sumNat (L + 1) (runOp L (-m) m (-m) m v) = -(m * v L) := by
            rw [sumNat_succ_front, runOp_at_zero]
            have htail : sumNat L (fun j => runOp L (-m) m (-m) m v (j + 1)) =
                m * v 0 + m * sumNat (L - 1) (fun j => v (j + 1)) := by
              rw [sumNat_pred_front L hL (fun j => runOp L (-m) m (-m) m v (j + 1))]
              rw [show (0 : Nat) + 1 = 1 from rfl, runOp_at_one]
              congr 1
              rw [← sumNat_mul_left]
              apply sumNat_congr; intro j hj
              rw [runOp_at_mid L (-m) m (-m) m v (j + 1 + 1) (by omega) (by omega)]
              rfl
            have hsplitv : sumNat L (fun j => v (j + 1)) =
                sumNat (L - 1) (fun j => v (j + 1)) + v L := by
              rw [sumNat_pred_back L hL (fun j => v (j + 1))]
              congr 1; congr 1; omega
            rw [htail, hsplitv, Int.neg_mul, Int.neg_mul, Int.mul_add]
            omega
          rw [hsumM]
          omega
        · have hnotlt2 : ¬ (i < L + 2) := by omega
          simp [hiL, hiE, hi0, hnotlt2]

/-- Closed form of `w`-fold scaled cyclic right rotation on `ℤ^(L+2)`. -/
theorem scaledRotR_iter (L : Nat) (m : Int) (u : Nat → Int) :
    ∀ w i, i < L + 2 →
      iterOp (scaledRotR L m) w u i =
        m ^ w * u ((i + (L + 2) - w % (L + 2)) % (L + 2)) := by
  intro w
  induction w with
  | zero =>
    intro i hi
    simp only [iterOp_zero, Int.pow_zero, Nat.zero_mod, Nat.sub_zero, Int.one_mul]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  | succ k ih =>
    intro i hi
    rw [iterOp_succ]
    have hrem := Nat.mod_lt k (by omega : 0 < L + 2)
    have hsucc : (k + 1) % (L + 2) = if k % (L + 2) + 1 = L + 2 then 0 else k % (L + 2) + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < L + 2)]
      by_cases heq : k % (L + 2) + 1 = L + 2
      · simp [heq]
      · simp only [heq, ↓reduceIte, Nat.mod_eq_of_lt (by omega : k % (L + 2) + 1 < L + 2)]
    by_cases hi0 : i = 0
    · subst hi0
      rw [scaledRotR_at_zero, ih (L + 1) (by omega), Int.pow_succ, ← Int.mul_assoc,
          Int.mul_comm m (m ^ k)]
      congr 2
      rw [hsucc]
      split
      · rename_i heq
        have h1 : L + 1 + (L + 2) - k % (L + 2) = L + 2 := by omega
        rw [h1, Nat.mod_self]; simp
      · rename_i hne
        have h1 : L + 1 + (L + 2) - k % (L + 2) = (L + 2) + (L + 2 - (k % (L + 2) + 1)) := by omega
        have h2 : 0 + (L + 2) - (k % (L + 2) + 1) = L + 2 - (k % (L + 2) + 1) := by omega
        rw [h1, h2, Nat.add_mod_left]
    · rw [scaledRotR_at_pos L m _ i hi0 hi, ih (i - 1) (by omega), Int.pow_succ,
          ← Int.mul_assoc, Int.mul_comm m (m ^ k)]
      congr 2
      rw [hsucc]
      split
      · rename_i heq
        have h1 : i - 1 + (L + 2) - k % (L + 2) = i := by omega
        have h2 : i + (L + 2) - 0 = i + (L + 2) := by omega
        rw [h1, h2, Nat.add_mod_right]
      · rename_i hne
        have h1 : i - 1 + (L + 2) - k % (L + 2) = i + (L + 2) - (k % (L + 2) + 1) := by omega
        rw [h1]

/-- **EXACT COORDINATE CLOSED FORM** for `M_run(L; -m, m, -m, m)^w e_0` via Engine Theorem B! -/
theorem runOp_cyclotomic_exact_state (L : Nat) (hL : 1 ≤ L) (m : Int) (w : Nat) :
    (sumNat (L + 1) (iterOp (runOp L (-m) m (-m) m) w (basisVec 0)) =
      if w % (L + 2) = 0 then m ^ w
      else if w % (L + 2) = L + 1 then -(m ^ w)
      else 0) ∧
    (iterOp (runOp L (-m) m (-m) m) w (basisVec 0) 0 =
      if w % (L + 2) = 0 then m ^ w
      else if w % (L + 2) = 1 then -(m ^ w)
      else 0) := by
  have hint := intertwining_lift (runOp L (-m) m (-m) m) (scaledRotR L m) (hyperplaneEmbed L)
    (runOp_cyclotomic_intertwines L hL m) w (basisVec 0)
  have hsum0 : sumNat (L + 1) (basisVec 0) = 1 :=
    sumNat_ite_eq (L + 1) 0 1 (by omega)
  have hEmbed0 : ∀ j, hyperplaneEmbed L (basisVec 0) j =
      if j = 0 then 1 else if j = L + 1 then -1 else 0 := by
    intro j
    unfold hyperplaneEmbed
    rw [hsum0]
    unfold basisVec
    by_cases hj0 : j = 0
    · subst hj0; simp
    · by_cases hjlt : j < L + 1
      · have hne : j ≠ L + 1 := by omega
        simp [hj0, hjlt, hne]
      · by_cases hjE : j = L + 1
        · subst hjE; simp
        · simp [hj0, hjlt, hjE]
  have hrem := Nat.mod_lt w (by omega : 0 < L + 2)
  constructor
  · have hL1 := congrFun hint (L + 1)
    rw [scaledRotR_iter L m _ w (L + 1) (by omega), hEmbed0] at hL1
    unfold hyperplaneEmbed at hL1
    simp only [Nat.lt_irrefl, ↓reduceIte] at hL1
    by_cases hr0 : w % (L + 2) = 0
    · simp only [hr0, ↓reduceIte]
      rw [hr0] at hL1
      have hidx : (L + 1 + (L + 2) - 0) % (L + 2) = L + 1 := by
        rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hidx] at hL1
      simp only [show L + 1 ≠ 0 from by omega, ↓reduceIte] at hL1
      omega
    · by_cases hrL1 : w % (L + 2) = L + 1
      · simp only [hrL1, ↓reduceIte]
        rw [hrL1] at hL1
        have hidx : (L + 1 + (L + 2) - (L + 1)) % (L + 2) = 0 := by
          rw [show L + 1 + (L + 2) - (L + 1) = L + 2 by omega, Nat.mod_self]
        rw [hidx] at hL1
        simp only [↓reduceIte] at hL1
        omega
      · simp only [hr0, hrL1, ↓reduceIte]
        have hidx : (L + 1 + (L + 2) - w % (L + 2)) % (L + 2) = L + 1 - w % (L + 2) := by
          have h1 : L + 1 + (L + 2) - w % (L + 2) = (L + 1 - w % (L + 2)) + (L + 2) := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hidx] at hL1
        have hne0 : L + 1 - w % (L + 2) ≠ 0 := by omega
        have hneL1 : L + 1 - w % (L + 2) ≠ L + 1 := by omega
        simp only [hne0, hneL1, ↓reduceIte, Int.mul_zero] at hL1
        omega
  · have h0 := congrFun hint 0
    rw [scaledRotR_iter L m _ w 0 (by omega), hEmbed0] at h0
    unfold hyperplaneEmbed at h0
    simp only [Nat.zero_lt_succ, ↓reduceIte] at h0
    by_cases hr0 : w % (L + 2) = 0
    · simp only [hr0, ↓reduceIte]
      rw [hr0] at h0
      have hidx : (0 + (L + 2) - 0) % (L + 2) = 0 := by simp
      rw [hidx] at h0
      simp only [↓reduceIte, Int.mul_one] at h0
      exact h0
    · by_cases hr1 : w % (L + 2) = 1
      · simp only [hr1, ↓reduceIte]
        rw [hr1] at h0
        have hidx : (0 + (L + 2) - 1) % (L + 2) = L + 1 := by
          rw [show 0 + (L + 2) - 1 = L + 1 by omega, Nat.mod_eq_of_lt (by omega)]
        rw [hidx] at h0
        simp only [show L + 1 ≠ 0 from by omega, ↓reduceIte, Int.mul_neg, Int.mul_one] at h0
        exact h0
      · simp only [hr0, hr1, ↓reduceIte]
        have hidx : (0 + (L + 2) - w % (L + 2)) % (L + 2) = L + 2 - w % (L + 2) := by
          rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [hidx] at h0
        have hne0 : L + 2 - w % (L + 2) ≠ 0 := by omega
        have hneL1 : L + 2 - w % (L + 2) ≠ L + 1 := by omega
        simp only [hne0, hneL1, ↓reduceIte, Int.mul_zero] at h0
        exact h0

-- ============================================================================
-- SECTION 6: Concrete Transducers & The Main Parametric Infinite Theorems
-- ============================================================================

/-- Constructive `div = 0 ↔ lt` helper for positive divisor `B > 0` (no `Classical`). -/
theorem nat_div_eq_zero_iff_lt (a B : Nat) (hB : 0 < B) : a / B = 0 ↔ a < B := by
  constructor
  · intro h
    cases Nat.lt_or_ge a B with
    | inl hlt => exact hlt
    | inr hge =>
      have : 1 ≤ a / B := Nat.div_pos hge hB
      omega
  · exact Nat.div_eq_of_lt

-- ----------------------------------------------------------------------------
-- FAMILY 1: Carry-Run Output-Parity Transducer (Even Radix B = 2m & Binary B = 2)
-- ----------------------------------------------------------------------------

/-- Concrete radix-`B` carry-run `≤ L` output-parity transducer (`readout` parameterized). -/
def carryRunParityTransducer (B L : Nat) (hB : 0 < B) (readout : Nat → Int) :
    CarryTransducer B (L + 1) where
  step q rx ry :=
    let cin := if q = 0 then 0 else 1
    let cout := (rx + ry + cin) / B
    if cout = 0 then some 0
    else if q + 1 ≤ L then some (q + 1)
    else none
  wt q rx ry :=
    let cin := if q = 0 then 0 else 1
    paritySign ((rx + ry + cin) % B)
  q0 := 0
  readout := readout
  hB := hB
  hq0 := Nat.zero_lt_succ L
  hClosed := by
    intro q _ rx _ ry _ q' hstep
    dsimp only at hstep
    by_cases hco : (rx + ry + (if q = 0 then 0 else 1)) / B = 0
    · simp only [hco, ↓reduceIte] at hstep
      injection hstep with heq; omega
    · simp only [hco, ↓reduceIte] at hstep
      by_cases hqL : q + 1 ≤ L
      · simp only [hqL, ↓reduceIte] at hstep
        injection hstep with heq; omega
      · simp only [hqL, ↓reduceIte] at hstep
        contradiction

/-- Exact semantic equivalence between `carryRunParityTransducer` and concrete `Nat` addition! -/
theorem evalPair_carryRunParity (B L : Nat) (hB : 0 < B) :
    ∀ w q x y, q ≤ L →
      evalPair (carryRunParityTransducer B L hB (fun _ => 1)) w q x y =
        if carryRunBounded B L w q x y then
          paritySign (digitSum B w (x + y + (if q = 0 then 0 else 1)))
        else 0 := by
  intro w
  induction w with
  | zero =>
    intro q x y hq
    simp [evalPair, carryRunParityTransducer, carryRunBounded, digitSum, hq]
  | succ k ih =>
    intro q x y hq
    let cin := if q = 0 then 0 else 1
    let cout := (x % B + y % B + cin) / B
    have hmod := nat_add3_mod B x y (if q = 0 then 0 else 1)
    have hdiv := nat_add3_div B x y (if q = 0 then 0 else 1) hB
    have hstep_lhs :
        evalPair (carryRunParityTransducer B L hB (fun _ => 1)) (k + 1) q x y =
        match (if cout = 0 then some 0 else if q + 1 ≤ L then some (q + 1) else none) with
        | none => 0
        | some q' =>
          paritySign ((x % B + y % B + cin) % B) *
            evalPair (carryRunParityTransducer B L hB (fun _ => 1)) k q' (x / B) (y / B) := rfl
    have hstep_rhs :
        carryRunBounded B L (k + 1) q x y =
        (decide ((if cout = 0 then 0 else q + 1) ≤ L) &&
          carryRunBounded B L k (if cout = 0 then 0 else q + 1) (x / B) (y / B)) := rfl
    rw [hstep_lhs, hstep_rhs]
    by_cases hco : cout = 0
    · simp only [hco, ↓reduceIte, Nat.zero_le, decide_true, Bool.true_and]
      rw [ih 0 (x / B) (y / B) (Nat.zero_le L)]
      simp only [↓reduceIte, digitSum, hmod, hdiv]
      change paritySign ((x % B + y % B + cin) % B) *
          (if carryRunBounded B L k 0 (x / B) (y / B) = true then
            paritySign (digitSum B k (x / B + y / B + 0))
          else 0) =
        if carryRunBounded B L k 0 (x / B) (y / B) = true then
          paritySign ((x % B + y % B + cin) % B + digitSum B k (x / B + y / B + cout))
        else 0
      rw [hco]
      by_cases hb : carryRunBounded B L k 0 (x / B) (y / B) = true
      · simp [hb, paritySign_add]
      · simp [hb]
    · have hco1 : cout = 1 := by
        have hlt1 := Nat.mod_lt x hB
        have hlt2 := Nat.mod_lt y hB
        have hcin : cin ≤ 1 := by dsimp [cin]; split <;> omega
        have hge : B ≤ x % B + y % B + cin := by
          cases Nat.lt_or_ge (x % B + y % B + cin) B with
          | inl hlt => exact absurd (Nat.div_eq_of_lt hlt) hco
          | inr hge => exact hge
        have h1 : 1 ≤ cout := Nat.div_pos hge hB
        have h2 : cout < 2 := by
          dsimp [cout]; rw [Nat.div_lt_iff_lt_mul hB]; omega
        omega
      simp only [hco, ↓reduceIte]
      by_cases hqL : q + 1 ≤ L
      · simp only [hqL, ↓reduceIte, decide_true, Bool.true_and]
        rw [ih (q + 1) (x / B) (y / B) hqL]
        simp only [Nat.succ_ne_zero, ↓reduceIte, digitSum, hmod, hdiv]
        change paritySign ((x % B + y % B + cin) % B) *
            (if carryRunBounded B L k (q + 1) (x / B) (y / B) = true then
              paritySign (digitSum B k (x / B + y / B + 1))
            else 0) =
          if carryRunBounded B L k (q + 1) (x / B) (y / B) = true then
            paritySign ((x % B + y % B + cin) % B + digitSum B k (x / B + y / B + cout))
          else 0
        rw [hco1]
        by_cases hb : carryRunBounded B L k (q + 1) (x / B) (y / B) = true
        · simp [hb, paritySign_add]
        · simp [hb]
      · simp only [hqL, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true]

/-- Same exact semantic equivalence for full binary sum readout `fun q => if q = 0 then 1 else -1`! -/
theorem evalPair_carryRunFullParity (L : Nat) :
    ∀ w q x y, q ≤ L →
      evalPair (carryRunParityTransducer 2 L (by omega) (fun q => if q = 0 then 1 else -1)) w q x y =
        if carryRunBounded 2 L w q x y then
          paritySign (digitSum 2 w (x + y + (if q = 0 then 0 else 1)) +
            carryOut 2 w (if q = 0 then 0 else 1) x y)
        else 0 := by
  intro w
  induction w with
  | zero =>
    intro q x y hq
    simp only [evalPair, carryRunParityTransducer, carryRunBounded, digitSum, carryOut,
               hq, decide_true, ↓reduceIte, Nat.zero_add]
    split <;> simp
  | succ k ih =>
    intro q x y hq
    let cin := if q = 0 then 0 else 1
    let cout := (x % 2 + y % 2 + cin) / 2
    have hmod := nat_add3_mod 2 x y (if q = 0 then 0 else 1)
    have hdiv := nat_add3_div 2 x y (if q = 0 then 0 else 1) (by omega)
    have hstep_lhs :
        evalPair (carryRunParityTransducer 2 L (by omega) (fun q => if q = 0 then 1 else -1)) (k + 1) q x y =
        match (if cout = 0 then some 0 else if q + 1 ≤ L then some (q + 1) else none) with
        | none => 0
        | some q' =>
          paritySign ((x % 2 + y % 2 + cin) % 2) *
            evalPair (carryRunParityTransducer 2 L (by omega) (fun q => if q = 0 then 1 else -1)) k q' (x / 2) (y / 2) := rfl
    have hstep_rhs :
        carryRunBounded 2 L (k + 1) q x y =
        (decide ((if cout = 0 then 0 else q + 1) ≤ L) &&
          carryRunBounded 2 L k (if cout = 0 then 0 else q + 1) (x / 2) (y / 2)) := rfl
    rw [hstep_lhs, hstep_rhs]
    by_cases hco : cout = 0
    · simp only [hco, ↓reduceIte, Nat.zero_le, decide_true, Bool.true_and]
      rw [ih 0 (x / 2) (y / 2) (Nat.zero_le L)]
      simp only [↓reduceIte, digitSum, carryOut, hmod, hdiv]
      change paritySign ((x % 2 + y % 2 + cin) % 2) *
          (if carryRunBounded 2 L k 0 (x / 2) (y / 2) = true then
            paritySign (digitSum 2 k (x / 2 + y / 2 + 0) + carryOut 2 k 0 (x / 2) (y / 2))
          else 0) =
        if carryRunBounded 2 L k 0 (x / 2) (y / 2) = true then
          paritySign ((x % 2 + y % 2 + cin) % 2 +
            digitSum 2 k (x / 2 + y / 2 + cout) + carryOut 2 k cout (x / 2) (y / 2))
        else 0
      rw [hco]
      by_cases hb : carryRunBounded 2 L k 0 (x / 2) (y / 2) = true
      · simp [hb, paritySign_add, Nat.add_assoc]
      · simp [hb]
    · have hco1 : cout = 1 := by
        have hlt1 := Nat.mod_lt x (by omega : 0 < 2)
        have hlt2 := Nat.mod_lt y (by omega : 0 < 2)
        have hcin : cin ≤ 1 := by dsimp [cin]; split <;> omega
        dsimp [cout]; omega
      simp only [hco, ↓reduceIte]
      by_cases hqL : q + 1 ≤ L
      · simp only [hqL, ↓reduceIte, decide_true, Bool.true_and]
        rw [ih (q + 1) (x / 2) (y / 2) hqL]
        simp only [Nat.succ_ne_zero, ↓reduceIte, digitSum, carryOut, hmod, hdiv]
        change paritySign ((x % 2 + y % 2 + cin) % 2) *
            (if carryRunBounded 2 L k (q + 1) (x / 2) (y / 2) = true then
              paritySign (digitSum 2 k (x / 2 + y / 2 + 1) + carryOut 2 k 1 (x / 2) (y / 2))
            else 0) =
          if carryRunBounded 2 L k (q + 1) (x / 2) (y / 2) = true then
            paritySign ((x % 2 + y % 2 + cin) % 2 +
              digitSum 2 k (x / 2 + y / 2 + cout) + carryOut 2 k cout (x / 2) (y / 2))
          else 0
        rw [hco1]
        by_cases hb : carryRunBounded 2 L k (q + 1) (x / 2) (y / 2) = true
        · simp [hb, paritySign_add, Nat.add_assoc]
        · simp [hb]
      · simp only [hqL, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true]

/-- Operator identification: for even radix `B = 2m`, the forward transfer operator of
    `carryRunParityTransducer (2*m) L` equals `runOp L (-m) m (-m) m` on `< L + 1`! -/
theorem transferOp_carryRunParity_eq (m L : Nat) (hm : 0 < m) (hL : 1 ≤ L)
    (readout : Nat → Int) (u v : Nat → Int) (huv : ∀ i, i < L + 1 → u i = v i) :
    ∀ i, i < L + 1 →
      transferOp (carryRunParityTransducer (2 * m) L (by omega) readout) u i =
        runOp L (-(m : Int)) (m : Int) (-(m : Int)) (m : Int) v i := by
  intro i hi
  unfold transferOp carryRunParityTransducer runOp
  dsimp only
  have h2m : 0 < 2 * m := by omega
  by_cases hi0 : i = 0
  · subst hi0
    simp only [↓reduceIte]
    rw [sumNat_succ_front]
    have hq0 : sumNat (2 * m) (fun rx => sumNat (2 * m) (fun ry =>
        match (if (rx + ry + (if 0 = 0 then 0 else 1)) / (2 * m) = 0 then some 0
               else if 0 + 1 ≤ L then some (0 + 1) else none) with
        | none => 0
        | some q'' => if q'' = 0 then
            paritySign ((rx + ry + (if 0 = 0 then 0 else 1)) % (2 * m)) * u 0 else 0)) =
        -(m : Int) * v 0 := by
      rw [← evenRadix_a_eq m, ← sumNat_mul_right]
      apply sumNat_congr; intro rx _
      rw [← sumNat_mul_right]
      apply sumNat_congr; intro ry _
      rw [huv 0 (by omega)]
      simp only [↓reduceIte, Nat.add_zero]
      by_cases hlt : rx + ry < 2 * m
      · have hd : (rx + ry) / (2 * m) = 0 := (nat_div_eq_zero_iff_lt _ _ h2m).2 hlt
        simp [hlt, hd]
      · have hd : (rx + ry) / (2 * m) ≠ 0 := fun h => hlt ((nat_div_eq_zero_iff_lt _ _ h2m).1 h)
        simp only [hlt, hd, ↓reduceIte, Int.zero_mul]
        by_cases h1L : 0 + 1 ≤ L <;> simp [h1L]
    have hqt : sumNat L (fun j => sumNat (2 * m) (fun rx => sumNat (2 * m) (fun ry =>
        match (if (rx + ry + (if j + 1 = 0 then 0 else 1)) / (2 * m) = 0 then some 0
               else if j + 1 + 1 ≤ L then some (j + 1 + 1) else none) with
        | none => 0
        | some q'' => if q'' = 0 then
            paritySign ((rx + ry + (if j + 1 = 0 then 0 else 1)) % (2 * m)) * u (j + 1) else 0))) =
        -(m : Int) * sumNat L (fun j => v (j + 1)) := by
      rw [← sumNat_mul_left]
      apply sumNat_congr; intro j hj
      rw [← evenRadix_c_eq m, ← sumNat_mul_right]
      apply sumNat_congr; intro rx _
      rw [← sumNat_mul_right]
      apply sumNat_congr; intro ry _
      rw [huv (j + 1) (by omega)]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      by_cases hlt : rx + ry + 1 < 2 * m
      · have hd : (rx + ry + 1) / (2 * m) = 0 := (nat_div_eq_zero_iff_lt _ _ h2m).2 hlt
        simp [hlt, hd]
      · have hd : (rx + ry + 1) / (2 * m) ≠ 0 := fun h => hlt ((nat_div_eq_zero_iff_lt _ _ h2m).1 h)
        simp only [hlt, hd, ↓reduceIte, Int.zero_mul]
        by_cases hjL : j + 1 + 1 ≤ L <;> simp [hjL]
    rw [hq0, hqt]
  · by_cases hi1 : i = 1
    · subst hi1
      simp only [hi0, ↓reduceIte]
      rw [sumNat_succ_front]
      have hqt : sumNat L (fun j => sumNat (2 * m) (fun rx => sumNat (2 * m) (fun ry =>
          match (if (rx + ry + (if j + 1 = 0 then 0 else 1)) / (2 * m) = 0 then some 0
                 else if j + 1 + 1 ≤ L then some (j + 1 + 1) else none) with
          | none => 0
          | some q'' => if q'' = 1 then
              paritySign ((rx + ry + (if j + 1 = 0 then 0 else 1)) % (2 * m)) * u (j + 1) else 0))) = 0 := by
        rw [sumNat_congr (g := fun _ => 0)]
        · exact sumNat_zero_fn L
        · intro j _
          rw [sumNat_congr (g := fun _ => 0)]
          · exact sumNat_zero_fn (2 * m)
          · intro rx _
            rw [sumNat_congr (g := fun _ => 0)]
            · exact sumNat_zero_fn (2 * m)
            · intro ry _
              by_cases hd : (rx + ry + (if j + 1 = 0 then 0 else 1)) / (2 * m) = 0
              · simp only [hd, ↓reduceIte, show (0 : Nat) ≠ 1 by omega]
              · by_cases hjL : j + 1 + 1 ≤ L
                · simp only [hd, hjL, ↓reduceIte, show j + 1 + 1 ≠ 1 by omega]
                · simp only [hd, hjL, ↓reduceIte]
      rw [hqt, Int.add_zero]
      rw [← evenRadix_b_eq m, ← sumNat_mul_right]
      apply sumNat_congr; intro rx _
      rw [← sumNat_mul_right]
      apply sumNat_congr; intro ry _
      rw [huv 0 (by omega)]
      simp only [↓reduceIte, Nat.add_zero, hL]
      by_cases hge : 2 * m ≤ rx + ry
      · have hd : (rx + ry) / (2 * m) ≠ 0 := fun h => by
          have := (nat_div_eq_zero_iff_lt _ _ h2m).1 h; omega
        simp [hge, hd]
      · have hd : (rx + ry) / (2 * m) = 0 := (nat_div_eq_zero_iff_lt _ _ h2m).2 (by omega)
        simp [hge, hd]
    · have hiL : i ≤ L := by omega
      simp only [hi0, hi1, hiL, ↓reduceIte]
      have hsingle : ∀ q, q < L + 1 →
          sumNat (2 * m) (fun rx => sumNat (2 * m) (fun ry =>
            match (if (rx + ry + (if q = 0 then 0 else 1)) / (2 * m) = 0 then some 0
                   else if q + 1 ≤ L then some (q + 1) else none) with
            | none => 0
            | some q'' => if q'' = i then
                paritySign ((rx + ry + (if q = 0 then 0 else 1)) % (2 * m)) * u q else 0)) =
          if q = i - 1 then (m : Int) * v (i - 1) else 0 := by
        intro q hq
        by_cases hqi : q = i - 1
        · subst hqi
          simp only [↓reduceIte]
          have hqne0 : i - 1 ≠ 0 := by omega
          have hqeq : i - 1 + 1 = i := by omega
          rw [← evenRadix_r_eq m, ← sumNat_mul_right]
          apply sumNat_congr; intro rx _
          rw [← sumNat_mul_right]
          apply sumNat_congr; intro ry _
          rw [huv (i - 1) (by omega)]
          simp only [hqne0, ↓reduceIte, hqeq, hiL]
          by_cases hge : 2 * m ≤ rx + ry + 1
          · have hd : (rx + ry + 1) / (2 * m) ≠ 0 := fun h => by
              have := (nat_div_eq_zero_iff_lt _ _ h2m).1 h; omega
            simp [hge, hd]
          · have hd : (rx + ry + 1) / (2 * m) = 0 := (nat_div_eq_zero_iff_lt _ _ h2m).2 (by omega)
            simp [hge, hd, show (0 : Nat) ≠ i by omega]
        · simp only [hqi, ↓reduceIte]
          rw [sumNat_congr (g := fun _ => 0)]
          · exact sumNat_zero_fn (2 * m)
          · intro rx _
            rw [sumNat_congr (g := fun _ => 0)]
            · exact sumNat_zero_fn (2 * m)
            · intro ry _
              by_cases hd : (rx + ry + (if q = 0 then 0 else 1)) / (2 * m) = 0
              · simp [hd, show (0 : Nat) ≠ i by omega]
              · by_cases hqL : q + 1 ≤ L
                · simp [hd, hqL, show q + 1 ≠ i by omega]
                · simp [hd, hqL]
      rw [sumNat_congr hsingle]
      exact sumNat_ite_eq (L + 1) (i - 1) ((m : Int) * v (i - 1)) (by omega)

/-- **THEOREM 1A (Even-Radix Carry-Run Cyclotomic Period-`(L+2)` Collapse)**:
    For EVERY even radix `B = 2m` (`m ≥ 1`), EVERY carry-run bound `L ≥ 1`, and EVERY digit-width `w : Nat`:
    `∑_{x,y < (2m)^w, carryRun(x,y) ≤ L} (-1)^(σ_{2m}((x+y) mod (2m)^w))`
    equals `m^w` if `w ≡ 0`, `-m^w` if `w ≡ L+1`, and `0` otherwise `(mod L+2)`! -/
theorem evenRadix_carryRun_outputParity_collapse (m L : Nat) (hm : 1 ≤ m) (hL : 1 ≤ L) (w : Nat) :
    sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
      if maxCarryRunLe (2 * m) L w x y then paritySign (digitSum (2 * m) w ((x + y) % (2 * m) ^ w)) else 0)) =
    if w % (L + 2) = 0 then (m : Int) ^ w
    else if w % (L + 2) = L + 1 then -((m : Int) ^ w)
    else 0 := by
  let T := carryRunParityTransducer (2 * m) L (by omega) (fun _ => 1)
  have hsem :
      sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
        if maxCarryRunLe (2 * m) L w x y then
          paritySign (digitSum (2 * m) w ((x + y) % (2 * m) ^ w))
        else 0)) = arithSum T w := by
    unfold arithSum arithSumFrom maxCarryRunLe
    apply sumNat_congr; intro x _
    apply sumNat_congr; intro y _
    change (if carryRunBounded (2 * m) L w 0 x y = true then
        paritySign (digitSum (2 * m) w ((x + y) % (2 * m) ^ w)) else 0) =
      evalPair (carryRunParityTransducer (2 * m) L (by omega) (fun _ => 1)) w 0 x y
    rw [evalPair_carryRunParity (2 * m) L (by omega) w 0 x y (Nat.zero_le L)]
    simp only [↓reduceIte, Nat.add_zero, digitSum_mod_pow]
  rw [hsem, arithSum_eq_transferPow]
  have hq0 : T.q0 = 0 := rfl
  rw [hq0]
  have hagree := iterOp_eq_of_agree
    (transferOp T) (runOp L (-(m : Int)) (m : Int) (-(m : Int)) (m : Int))
    (transferOp_carryRunParity_eq m L (by omega) hL (fun _ => 1)) w (basisVec 0)
  rw [dot_congr_right (L + 1) T.readout _ _ hagree]
  have hdot : dot (L + 1) T.readout (iterOp (runOp L (-(m : Int)) (m : Int) (-(m : Int)) (m : Int)) w (basisVec 0)) =
      sumNat (L + 1) (iterOp (runOp L (-(m : Int)) (m : Int) (-(m : Int)) (m : Int)) w (basisVec 0)) := by
    unfold dot T carryRunParityTransducer
    apply sumNat_congr; intro i _; simp
  rw [hdot]
  exact (runOp_cyclotomic_exact_state L hL (m : Int) w).1

/-- **THEOREM 1B (Binary Carry-Run Low-Bit Thue–Morse Collapse)**:
    For EVERY `L ≥ 1` and EVERY bit-width `w : Nat`, out of all `4^w` pairs `(x, y) ∈ [0, 2^w)^2`,
    the Thue–Morse sum `∑ (-1)^popcount((x+y) % 2^w)` over pairs with `carryRun(x, y) ≤ L`
    collapses completely to `{-1, 0, +1}` with exact period `L + 2`! -/
theorem binary_carryRun_lowPopcount_collapse (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
      if maxCarryRunLe 2 L w x y then paritySign (popcount w ((x + y) % 2 ^ w)) else 0)) =
    if w % (L + 2) = 0 then 1
    else if w % (L + 2) = L + 1 then -1
    else 0 := by
  have h := evenRadix_carryRun_outputParity_collapse 1 L (Nat.le_refl 1) hL w
  simp only [Nat.mul_one, Int.natCast_one, Int.one_pow] at h
  exact h

/-- **THEOREM 1C (Binary Carry-Run Full-Sum Thue–Morse Collapse — Including MSB Carry-Out)**:
    For EVERY `L ≥ 1` and EVERY bit-width `w : Nat`,
    `∑_{x,y < 2^w, carryRun(x,y) ≤ L} (-1)^popcount(x + y)`
    has exact period `L + 2`, taking values `1` at `w ≡ 0` or `L+1`, `-2` at `w ≡ 1`, and `0` otherwise! -/
theorem binary_carryRun_fullPopcount_collapse (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
      if maxCarryRunLe 2 L w x y then paritySign (popcount (w + 1) (x + y)) else 0)) =
    if w % (L + 2) = 0 then 1
    else if w % (L + 2) = 1 then -2
    else if w % (L + 2) = L + 1 then 1
    else 0 := by
  let rd : Nat → Int := fun q => if q = 0 then 1 else -1
  let T := carryRunParityTransducer 2 L (by omega) rd
  have hsem :
      sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
        if maxCarryRunLe 2 L w x y then paritySign (popcount (w + 1) (x + y)) else 0)) =
      arithSum T w := by
    unfold arithSum arithSumFrom maxCarryRunLe
    apply sumNat_congr; intro x hx
    apply sumNat_congr; intro y hy
    change (if carryRunBounded 2 L w 0 x y = true then paritySign (popcount (w + 1) (x + y)) else 0) =
      evalPair (carryRunParityTransducer 2 L (by omega) (fun q => if q = 0 then 1 else -1)) w 0 x y
    rw [evalPair_carryRunFullParity L w 0 x y (Nat.zero_le L)]
    simp only [↓reduceIte, Nat.add_zero]
    rw [binary_full_popcount_split w x y hx hy]
  rw [hsem, arithSum_eq_transferPow]
  have hq0 : T.q0 = 0 := rfl
  rw [hq0]
  have hagree := iterOp_eq_of_agree
    (transferOp T) (runOp L (-1) 1 (-1) 1)
    (transferOp_carryRunParity_eq 1 L (by omega) hL rd) w (basisVec 0)
  rw [dot_congr_right (L + 1) T.readout _ _ hagree]
  let v := iterOp (runOp L (-1) 1 (-1) 1) w (basisVec 0)
  have hdot : dot (L + 1) T.readout v = 2 * v 0 - sumNat (L + 1) v := by
    unfold dot T carryRunParityTransducer rd
    dsimp only
    rw [sumNat_succ_front, sumNat_succ_front (f := v)]
    simp only [↓reduceIte, Int.one_mul]
    have hneg : sumNat L (fun i => (if i + 1 = 0 then (1 : Int) else -1) * v (i + 1)) =
        -sumNat L (fun i => v (i + 1)) := by
      rw [← sumNat_neg]
      apply sumNat_congr; intro i _; simp
    rw [hneg]
    omega
  rw [hdot]
  dsimp only [v]
  have hst := runOp_cyclotomic_exact_state L hL 1 w
  simp only [Int.one_pow] at hst
  rcases hst with ⟨hsum, hv0⟩
  rw [hsum, hv0]
  have hLne : L ≠ 0 := by omega
  by_cases h0 : w % (L + 2) = 0
  · simp [h0]
  · by_cases h1 : w % (L + 2) = 1
    · simp [h1, hLne]
    · by_cases hL1 : w % (L + 2) = L + 1
      · simp [hL1, hLne]
      · simp [h0, h1, hL1]

-- ----------------------------------------------------------------------------
-- FAMILY 2: Ripple-Carry Propagation Depth Transducer & Monomial Input-Parity Collapse
-- ----------------------------------------------------------------------------

/-- Concrete radix-`B` ripple-carry propagation depth `≤ L` transducer with arbitrary digit-pair weight `wtFn`. -/
def rippleTransducer (B L : Nat) (hB : 0 < B) (hL : 1 ≤ L) (wtFn : Nat → Nat → Int) :
    CarryTransducer B (L + 1) where
  step q rx ry :=
    let cin := if q = 0 then 0 else 1
    let cout := (rx + ry + cin) / B
    if cout = 0 then some 0
    else if B ≤ rx + ry then some 1
    else if q + 1 ≤ L then some (q + 1)
    else none
  wt _ rx ry := wtFn rx ry
  q0 := 0
  readout _ := 1
  hB := hB
  hq0 := Nat.zero_lt_succ L
  hClosed := by
    intro q _ rx _ ry _ q' hstep
    dsimp only at hstep
    by_cases hco : (rx + ry + (if q = 0 then 0 else 1)) / B = 0
    · simp only [hco, ↓reduceIte] at hstep; injection hstep with heq; omega
    · simp only [hco, ↓reduceIte] at hstep
      by_cases hgen : B ≤ rx + ry
      · simp only [hgen, ↓reduceIte] at hstep; injection hstep with heq; omega
      · simp only [hgen, ↓reduceIte] at hstep
        by_cases hqL : q + 1 ≤ L
        · simp only [hqL, ↓reduceIte] at hstep; injection hstep with heq; omega
        · simp only [hqL, ↓reduceIte] at hstep; contradiction

/-- Semantic bridge for ripple-carry input-parity transducer (`wtFn rx ry = (-1)^(rx + ry)`). -/
theorem evalPair_rippleInputParity (B L : Nat) (hB : 0 < B) (hL : 1 ≤ L) :
    ∀ w q x y, q ≤ L →
      evalPair (rippleTransducer B L hB hL (fun rx ry => paritySign (rx + ry))) w q x y =
        if rippleDepthBounded B L w q x y then
          paritySign (digitSum B w x + digitSum B w y)
        else 0 := by
  intro w
  induction w with
  | zero =>
    intro q x y hq
    simp [evalPair, rippleTransducer, rippleDepthBounded, digitSum, hq]
  | succ k ih =>
    intro q x y hq
    let xi := x % B
    let yi := y % B
    let cin := if q = 0 then 0 else 1
    let cout := (xi + yi + cin) / B
    have hps : paritySign (xi + yi) * paritySign (digitSum B k (x / B) + digitSum B k (y / B)) =
        paritySign (digitSum B (k + 1) x + digitSum B (k + 1) y) := by
      rw [← paritySign_add]; simp only [digitSum]; congr 1; dsimp [xi, yi]; omega
    have hstep_lhs :
        evalPair (rippleTransducer B L hB hL (fun rx ry => paritySign (rx + ry))) (k + 1) q x y =
        match (if cout = 0 then some 0 else if B ≤ xi + yi then some 1
               else if q + 1 ≤ L then some (q + 1) else none) with
        | none => 0
        | some q' =>
          paritySign (xi + yi) *
            evalPair (rippleTransducer B L hB hL (fun rx ry => paritySign (rx + ry))) k q' (x / B) (y / B) := rfl
    have hstep_rhs :
        rippleDepthBounded B L (k + 1) q x y =
        (decide ((if cout = 0 then 0 else if B ≤ xi + yi then 1 else q + 1) ≤ L) &&
          rippleDepthBounded B L k (if cout = 0 then 0 else if B ≤ xi + yi then 1 else q + 1)
            (x / B) (y / B)) := rfl
    rw [hstep_lhs, hstep_rhs]
    by_cases hco : cout = 0
    · simp only [hco, ↓reduceIte, Nat.zero_le, decide_true, Bool.true_and]
      rw [ih 0 (x / B) (y / B) (Nat.zero_le L)]
      by_cases hb : rippleDepthBounded B L k 0 (x / B) (y / B) = true
      · simp only [hb, ↓reduceIte]; exact hps
      · simp [hb]
    · simp only [hco, ↓reduceIte]
      by_cases hgen : B ≤ xi + yi
      · simp only [hgen, ↓reduceIte, hL, decide_true, Bool.true_and]
        rw [ih 1 (x / B) (y / B) hL]
        by_cases hb : rippleDepthBounded B L k 1 (x / B) (y / B) = true
        · simp only [hb, ↓reduceIte]; exact hps
        · simp [hb]
      · simp only [hgen, ↓reduceIte]
        by_cases hqL : q + 1 ≤ L
        · simp only [hqL, ↓reduceIte, decide_true, Bool.true_and]
          rw [ih (q + 1) (x / B) (y / B) hqL]
          by_cases hb : rippleDepthBounded B L k (q + 1) (x / B) (y / B) = true
          · simp only [hb, ↓reduceIte]; exact hps
          · simp [hb]
        · simp only [hqL, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true]

/-- Semantic bridge for unweighted binary ripple-carry transducer (`wtFn _ _ = 1`). -/
theorem evalPair_ripplePlain (L : Nat) (hL : 1 ≤ L) :
    ∀ w q x y, q ≤ L →
      evalPair (rippleTransducer 2 L (by omega) hL (fun _ _ => 1)) w q x y =
        if rippleDepthBounded 2 L w q x y then 1 else 0 := by
  intro w
  induction w with
  | zero =>
    intro q x y hq
    simp [evalPair, rippleTransducer, rippleDepthBounded, hq]
  | succ k ih =>
    intro q x y hq
    let xi := x % 2
    let yi := y % 2
    let cin := if q = 0 then 0 else 1
    let cout := (xi + yi + cin) / 2
    have hstep_lhs :
        evalPair (rippleTransducer 2 L (by omega) hL (fun _ _ => 1)) (k + 1) q x y =
        match (if cout = 0 then some 0 else if 2 ≤ xi + yi then some 1
               else if q + 1 ≤ L then some (q + 1) else none) with
        | none => 0
        | some q' =>
          1 * evalPair (rippleTransducer 2 L (by omega) hL (fun _ _ => 1)) k q' (x / 2) (y / 2) := rfl
    have hstep_rhs :
        rippleDepthBounded 2 L (k + 1) q x y =
        (decide ((if cout = 0 then 0 else if 2 ≤ xi + yi then 1 else q + 1) ≤ L) &&
          rippleDepthBounded 2 L k (if cout = 0 then 0 else if 2 ≤ xi + yi then 1 else q + 1)
            (x / 2) (y / 2)) := rfl
    rw [hstep_lhs, hstep_rhs]
    by_cases hco : cout = 0
    · simp only [hco, ↓reduceIte, Nat.zero_le, decide_true, Bool.true_and, Int.one_mul]
      exact ih 0 (x / 2) (y / 2) (Nat.zero_le L)
    · simp only [hco, ↓reduceIte]
      by_cases hgen : 2 ≤ xi + yi
      · simp only [hgen, ↓reduceIte, hL, decide_true, Bool.true_and, Int.one_mul]
        exact ih 1 (x / 2) (y / 2) hL
      · simp only [hgen, ↓reduceIte]
        by_cases hqL : q + 1 ≤ L
        · simp only [hqL, ↓reduceIte, decide_true, Bool.true_and, Int.one_mul]
          exact ih (q + 1) (x / 2) (y / 2) hqL
        · simp only [hqL, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true]

/-- General operator identification for ANY `rippleTransducer B L wtFn`:
    its forward transfer operator equals `rippleOp L k p g` where `k, p, g` are the
    exact Kill / Propagate / Generate weight sums over `[0, B)^2`! -/
theorem transferOp_ripple_eq (B L : Nat) (hB : 0 < B) (hL : 1 ≤ L)
    (wtFn : Nat → Nat → Int) (k p g : Int)
    (hk : sumNat B (fun rx => sumNat B (fun ry => if rx + ry + 1 < B then wtFn rx ry else 0)) = k)
    (hp : sumNat B (fun rx => sumNat B (fun ry => if rx + ry + 1 = B then wtFn rx ry else 0)) = p)
    (hg : sumNat B (fun rx => sumNat B (fun ry => if B ≤ rx + ry then wtFn rx ry else 0)) = g)
    (u v : Nat → Int) (huv : ∀ i, i < L + 1 → u i = v i) :
    ∀ i, i < L + 1 →
      transferOp (rippleTransducer B L hB hL wtFn) u i = rippleOp L k p g v i := by
  intro i hi
  unfold transferOp rippleTransducer rippleOp
  dsimp only
  have hkp : sumNat B (fun rx => sumNat B (fun ry => if rx + ry < B then wtFn rx ry else 0)) = k + p := by
    rw [← hk, ← hp, ← sumNat_add]
    apply sumNat_congr; intro rx _
    rw [← sumNat_add]
    apply sumNat_congr; intro ry _
    by_cases h1 : rx + ry + 1 < B
    · have h2 : rx + ry + 1 ≠ B := by omega
      have h3 : rx + ry < B := by omega
      simp [h1, h2, h3]
    · by_cases h2 : rx + ry + 1 = B
      · have h3 : rx + ry < B := by omega
        simp [h2, h3]
      · have h3 : ¬ (rx + ry < B) := by omega
        simp [h1, h2, h3]
  by_cases hi0 : i = 0
  · subst hi0
    simp only [↓reduceIte]
    rw [sumNat_succ_front, sumNat_succ_front (f := v)]
    have hq0 : sumNat B (fun rx => sumNat B (fun ry =>
        match (if (rx + ry + (if 0 = 0 then 0 else 1)) / B = 0 then some 0
               else if B ≤ rx + ry then some 1
               else if 0 + 1 ≤ L then some (0 + 1) else none) with
        | none => 0
        | some q'' => if q'' = 0 then wtFn rx ry * u 0 else 0)) = (k + p) * v 0 := by
      rw [← hkp, ← sumNat_mul_right]
      apply sumNat_congr; intro rx _
      rw [← sumNat_mul_right]
      apply sumNat_congr; intro ry _
      rw [huv 0 (by omega)]
      simp only [↓reduceIte, Nat.add_zero]
      by_cases hlt : rx + ry < B
      · have hd : (rx + ry) / B = 0 := (nat_div_eq_zero_iff_lt _ _ hB).2 hlt
        simp [hlt, hd]
      · have hd : (rx + ry) / B ≠ 0 := fun h => hlt ((nat_div_eq_zero_iff_lt _ _ hB).1 h)
        simp only [hlt, hd, ↓reduceIte, Int.zero_mul]
        by_cases hge : B ≤ rx + ry
        · simp [hge]
        · by_cases h1L : 0 + 1 ≤ L <;> simp [hge, h1L]
    have hqt : sumNat L (fun j => sumNat B (fun rx => sumNat B (fun ry =>
        match (if (rx + ry + (if j + 1 = 0 then 0 else 1)) / B = 0 then some 0
               else if B ≤ rx + ry then some 1
               else if j + 1 + 1 ≤ L then some (j + 1 + 1) else none) with
        | none => 0
        | some q'' => if q'' = 0 then wtFn rx ry * u (j + 1) else 0))) =
        k * sumNat L (fun j => v (j + 1)) := by
      rw [← sumNat_mul_left]
      apply sumNat_congr; intro j hj
      rw [← hk, ← sumNat_mul_right]
      apply sumNat_congr; intro rx _
      rw [← sumNat_mul_right]
      apply sumNat_congr; intro ry _
      rw [huv (j + 1) (by omega)]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      by_cases hlt : rx + ry + 1 < B
      · have hd : (rx + ry + 1) / B = 0 := (nat_div_eq_zero_iff_lt _ _ hB).2 hlt
        simp [hlt, hd]
      · have hd : (rx + ry + 1) / B ≠ 0 := fun h => hlt ((nat_div_eq_zero_iff_lt _ _ hB).1 h)
        simp only [hlt, hd, ↓reduceIte, Int.zero_mul]
        by_cases hge : B ≤ rx + ry
        · simp [hge]
        · by_cases hjL : j + 1 + 1 ≤ L <;> simp [hge, hjL]
    rw [hq0, hqt, Int.add_mul, Int.mul_add]
    omega
  · by_cases hi1 : i = 1
    · subst hi1
      simp only [hi0, ↓reduceIte]
      rw [← sumNat_mul_left]
      apply sumNat_congr; intro q hq
      rw [← hg, ← sumNat_mul_right]
      apply sumNat_congr; intro rx _
      rw [← sumNat_mul_right]
      apply sumNat_congr; intro ry _
      rw [huv q hq]
      by_cases hq0 : q = 0
      · subst hq0
        simp only [↓reduceIte, Nat.add_zero]
        by_cases hge : B ≤ rx + ry
        · have hd : (rx + ry) / B ≠ 0 := fun h => by
            have := (nat_div_eq_zero_iff_lt _ _ hB).1 h; omega
          simp [hge, hd]
        · have hd : (rx + ry) / B = 0 := (nat_div_eq_zero_iff_lt _ _ hB).2 (by omega)
          simp [hge, hd]
      · simp only [hq0, ↓reduceIte]
        by_cases hge : B ≤ rx + ry
        · have hd : (rx + ry + 1) / B ≠ 0 := fun h => by
            have := (nat_div_eq_zero_iff_lt _ _ hB).1 h; omega
          simp [hge, hd]
        · by_cases hlt : rx + ry + 1 < B
          · have hd : (rx + ry + 1) / B = 0 := (nat_div_eq_zero_iff_lt _ _ hB).2 hlt
            simp [hge, hd]
          · have hd : (rx + ry + 1) / B ≠ 0 := fun h => hlt ((nat_div_eq_zero_iff_lt _ _ hB).1 h)
            simp only [hge, hd, ↓reduceIte, Int.zero_mul]
            by_cases hqL : q + 1 ≤ L
            · simp [hqL, hq0]
            · simp [hqL]
    · have hiL : i ≤ L := by omega
      simp only [hi0, hi1, hiL, ↓reduceIte]
      have hsingle : ∀ q, q < L + 1 →
          sumNat B (fun rx => sumNat B (fun ry =>
            match (if (rx + ry + (if q = 0 then 0 else 1)) / B = 0 then some 0
                   else if B ≤ rx + ry then some 1
                   else if q + 1 ≤ L then some (q + 1) else none) with
            | none => 0
            | some q'' => if q'' = i then wtFn rx ry * u q else 0)) =
          if q = i - 1 then p * v (i - 1) else 0 := by
        intro q hq
        by_cases hqi : q = i - 1
        · subst hqi
          simp only [↓reduceIte]
          have hqne0 : i - 1 ≠ 0 := by omega
          have hqeq : i - 1 + 1 = i := by omega
          rw [← hp, ← sumNat_mul_right]
          apply sumNat_congr; intro rx _
          rw [← sumNat_mul_right]
          apply sumNat_congr; intro ry _
          rw [huv (i - 1) (by omega)]
          simp only [hqne0, ↓reduceIte, hqeq, hiL]
          by_cases heq : rx + ry + 1 = B
          · have hBB : B / B ≠ 0 := by rw [Nat.div_self hB]; omega
            have hnge : ¬ (B ≤ rx + ry) := by omega
            simp only [heq, hnge, hBB, ↓reduceIte]
          · by_cases hlt : rx + ry + 1 < B
            · have hd : (rx + ry + 1) / B = 0 := (nat_div_eq_zero_iff_lt _ _ hB).2 hlt
              simp [heq, hd, show (0 : Nat) ≠ i by omega]
            · have hge : B ≤ rx + ry := by omega
              have hd : (rx + ry + 1) / B ≠ 0 := fun h => hlt ((nat_div_eq_zero_iff_lt _ _ hB).1 h)
              simp [heq, hd, hge, show (1 : Nat) ≠ i by omega]
        · simp only [hqi, ↓reduceIte]
          rw [sumNat_congr (g := fun _ => 0)]
          · exact sumNat_zero_fn B
          · intro rx _
            rw [sumNat_congr (g := fun _ => 0)]
            · exact sumNat_zero_fn B
            · intro ry _
              by_cases hd : (rx + ry + (if q = 0 then 0 else 1)) / B = 0
              · simp [hd, show (0 : Nat) ≠ i by omega]
              · by_cases hge : B ≤ rx + ry
                · simp [hd, hge, show (1 : Nat) ≠ i by omega]
                · by_cases hqL : q + 1 ≤ L
                  · simp [hd, hge, hqL, show q + 1 ≠ i by omega]
                  · simp [hd, hge, hqL]
      rw [sumNat_congr hsingle]
      exact sumNat_ite_eq (L + 1) (i - 1) (p * v (i - 1)) (by omega)

/-- **THEOREM 2A (Universal 3-Parameter Ripple-Carry Generating Function Identity)**:
    For EVERY `L ≥ 1`, EVERY `(k, p, g) ∈ ℤ^3`, and EVERY `w : Nat`:
    the Cauchy product of `1 - (k+p+g) z + g p^L z^(L+1)` with `R(w) = S(M_rip(L; k,p,g)^w e_0)`
    equals `δ_{w, 0}`! -/
theorem rippleOp_universal_gf_cauchy (L : Nat) (hL : 1 ≤ L) (k p g : Int) (w : Nat) :
    cauchyProd (trinomialDenom L (k + p + g) (g * p ^ L))
      (fun n => sumNat (L + 1) (iterOp (rippleOp L k p g) n (basisVec 0))) w =
    if w = 0 then 1 else 0 := by
  apply trinomial_gf_cauchy L hL (k + p + g) (g * p ^ L)
  · exact rippleOp_init_sum L hL k p g
  · intro n
    have hrec := trinomial_annihilator_recurrence (rippleOp L k p g) L (k + p + g) (g * p ^ L)
      (rippleOp_annihilator L hL k p g) (fun _ => 1) (basisVec 0) n
    have hdot : ∀ u, dot (L + 1) (fun _ => 1) u = sumNat (L + 1) u := by
      intro u; unfold dot; apply sumNat_congr; intro i _; simp
    rw [hdot, hdot, hdot] at hrec
    exact hrec

/-- **THEOREM 2B (Even-Radix Ripple-Carry Input-Parity Period-`(L+1)` Monomial Collapse)**:
    For EVERY even radix `B = 2m` (`m ≥ 1`), EVERY ripple depth bound `L ≥ 1`, and EVERY width `w : Nat`:
    `∑_{x,y < (2m)^w, rippleDepth(x,y) ≤ L} (-1)^(σ_{2m}(x) + σ_{2m}(y))`
    vanishes identically whenever `(L + 1) ∤ w`, and equals
    `((-1)^(L+1) * 2^L * m^(L+1))^(w / (L + 1))` whenever `(L + 1) ∣ w`! -/
theorem evenRadix_rippleDepth_inputParity_collapse (m L : Nat) (hm : 1 ≤ m) (hL : 1 ≤ L) (w : Nat) :
    sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
      if maxRippleDepthLe (2 * m) L w x y then
        paritySign (digitSum (2 * m) w x + digitSum (2 * m) w y)
      else 0)) =
    if w % (L + 1) = 0 then
      (paritySign (L + 1) * (2 : Int) ^ L * (m : Int) ^ (L + 1)) ^ (w / (L + 1))
    else 0 := by
  let M := rippleOp L (m : Int) (-(2 * (m : Int))) (m : Int)
  let T := rippleTransducer (2 * m) L (by omega) hL (fun rx ry => paritySign (rx + ry))
  have hsem :
      sumNat ((2 * m) ^ w) (fun x => sumNat ((2 * m) ^ w) (fun y =>
        if maxRippleDepthLe (2 * m) L w x y then
          paritySign (digitSum (2 * m) w x + digitSum (2 * m) w y)
        else 0)) = arithSum T w := by
    unfold arithSum arithSumFrom maxRippleDepthLe
    apply sumNat_congr; intro x _
    apply sumNat_congr; intro y _
    exact (evalPair_rippleInputParity (2 * m) L (by omega) hL w 0 x y (Nat.zero_le L)).symm
  rw [hsem, arithSum_eq_transferPow]
  have hq0 : T.q0 = 0 := rfl
  rw [hq0]
  have hagree := iterOp_eq_of_agree (transferOp T) M
    (transferOp_ripple_eq (2 * m) L (by omega) hL _ (m : Int) (-(2 * (m : Int))) (m : Int)
      (evenRadix_inKill_eq m) (evenRadix_inProp_eq m) (evenRadix_inGen_eq m))
    w (basisVec 0)
  rw [dot_congr_right (L + 1) T.readout _ _ hagree]
  have hdot : dot (L + 1) T.readout (iterOp M w (basisVec 0)) =
      sumNat (L + 1) (iterOp M w (basisVec 0)) := by
    unfold dot T rippleTransducer; apply sumNat_congr; intro i _; simp
  rw [hdot]
  let c : Int := paritySign (L + 1) * (2 : Int) ^ L * (m : Int) ^ (L + 1)
  have hneg_gpL : -((m : Int) * (-(2 * (m : Int))) ^ L) = c := by
    have hpow_neg : ∀ n, (-(2 * (m : Int))) ^ n = paritySign n * (2 : Int) ^ n * (m : Int) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [Int.pow_succ, ih, paritySign_succ, Int.pow_succ, Int.pow_succ]
        rw [Int.neg_mul, Int.neg_mul, Int.mul_neg]
        congr 1
        rw [Int.mul_assoc (paritySign k * (2 : Int) ^ k), ← Int.mul_assoc ((m : Int) ^ k) 2,
            Int.mul_comm ((m : Int) ^ k) 2, Int.mul_assoc 2 ((m : Int) ^ k),
            ← Int.mul_assoc (paritySign k * (2 : Int) ^ k) 2, Int.mul_assoc (paritySign k) ((2 : Int) ^ k) 2]
    rw [hpow_neg L]
    dsimp [c]
    rw [paritySign_succ, Int.pow_succ, Int.neg_mul, Int.neg_mul]
    congr 1
    rw [Int.mul_comm (m : Int), Int.mul_assoc, Int.mul_comm ((m : Int) ^ L) (m : Int),
        ← Int.mul_assoc]
  have hPer : ∀ i, iterOp M (L + 1) (basisVec 0) i = c * basisVec 0 i := by
    intro i
    by_cases hi : i < L + 1
    · have hann := rippleOp_annihilator L hL (m : Int) (-(2 * (m : Int))) (m : Int) (basisVec 0) i hi
      have hzero : (m : Int) + -(2 * (m : Int)) + (m : Int) = 0 := by omega
      rw [hzero, Int.zero_mul, Int.sub_zero] at hann
      have hsub : iterOp M (L + 1) (basisVec 0) i =
          -((m : Int) * (-(2 * (m : Int))) ^ L) * basisVec 0 i := by
        dsimp only [M]; rw [Int.neg_mul]; omega
      rw [hsub, hneg_gpL]
    · have hzeroM : iterOp M (L + 1) (basisVec 0) i = 0 := by
        rw [iterOp_succ]
        exact rippleOp_at_out L _ _ _ _ i hL (by omega)
      have hzeroB : basisVec 0 i = 0 := by
        unfold basisVec; simp [show i ≠ 0 by omega]
      rw [hzeroM, hzeroB, Int.mul_zero]
  have hLift := scaled_periodic_lift M (rippleOp_hom L _ _ _) c (basisVec 0) hPer w
  rw [sumNat_congr (g := fun i => c ^ (w / (L + 1)) * iterOp M (w % (L + 1)) (basisVec 0) i)
      (fun i _ => hLift i)]
  rw [sumNat_mul_left]
  have hrem_le : w % (L + 1) ≤ L := Nat.lt_succ_iff.mp (Nat.mod_lt w (Nat.zero_lt_succ L))
  rw [rippleOp_init_sum L hL (m : Int) (-(2 * (m : Int))) (m : Int) (w % (L + 1)) hrem_le]
  have hT0 : (m : Int) + -(2 * (m : Int)) + (m : Int) = 0 := by omega
  rw [hT0]
  cases hr : w % (L + 1) with
  | zero => simp [c]
  | succ r' => simp [Int.pow_succ]

/-- **THEOREM 2B (Binary Specialization, `B = 2`)**:
    For EVERY ripple-carry depth bound `L ≥ 1` and EVERY bit-width `w : Nat`:
    `∑_{x,y < 2^w, rippleDepth(x,y) ≤ L} (-1)^(popcount(x) + popcount(y))`
    equals `((-1)^(L+1) * 2^L)^(w / (L + 1))` if `(L + 1) ∣ w`, and `0` otherwise! -/
theorem binary_rippleDepth_inputParity_collapse (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
      if maxRippleDepthLe 2 L w x y then paritySign (popcount w x + popcount w y) else 0)) =
    if w % (L + 1) = 0 then (paritySign (L + 1) * (2 : Int) ^ L) ^ (w / (L + 1)) else 0 := by
  have h := evenRadix_rippleDepth_inputParity_collapse 1 L (Nat.le_refl 1) hL w
  simp only [Nat.mul_one, Int.natCast_one, Int.one_pow, Int.mul_one] at h
  exact h

/-- **THEOREM 2C (Exact Unweighted Binary Ripple-Carry Recurrence)**:
    For EVERY `L ≥ 1` and EVERY `w : Nat`, let `R_L(w) = #{(x, y) ∈ [0, 2^w)^2 | rippleDepth(x,y) ≤ L}`.
    Then `R_L(w + L + 1) = 4 * R_L(w + L) - 2^L * R_L(w)`! -/
theorem binary_rippleDepth_plain_recurrence (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    let R := fun n => sumNat (2 ^ n) (fun x => sumNat (2 ^ n) (fun y =>
      if maxRippleDepthLe 2 L n x y then (1 : Int) else 0))
    R (w + L + 1) = 4 * R (w + L) - (2 : Int) ^ L * R w := by
  intro R
  let T := rippleTransducer 2 L (by omega) hL (fun _ _ => 1)
  have hR : ∀ n, R n = dot (L + 1) (fun _ => 1) (iterOp (rippleOp L 1 2 1) n (basisVec 0)) := by
    intro n
    have hsem : R n = arithSum T n := by
      unfold R arithSum arithSumFrom maxRippleDepthLe
      apply sumNat_congr; intro x _
      apply sumNat_congr; intro y _
      exact (evalPair_ripplePlain L hL n 0 x y (Nat.zero_le L)).symm
    rw [hsem, arithSum_eq_transferPow]
    have hq0 : T.q0 = 0 := rfl
    rw [hq0]
    have hagree := iterOp_eq_of_agree (transferOp T) (rippleOp L 1 2 1)
      (transferOp_ripple_eq 2 L (by omega) hL (fun _ _ => 1) 1 2 1
        (by decide) (by decide) (by decide)) n (basisVec 0)
    exact dot_congr_right (L + 1) T.readout _ _ hagree
  rw [hR (w + L + 1), hR (w + L), hR w]
  have hrec := trinomial_annihilator_recurrence (rippleOp L 1 2 1) L (1 + 2 + 1) (1 * (2 : Int) ^ L)
    (rippleOp_annihilator L hL 1 2 1) (fun _ => 1) (basisVec 0) w
  simp only [show (1 : Int) + 2 + 1 = 4 by decide, Int.one_mul] at hrec
  exact hrec

-- ----------------------------------------------------------------------------
-- FAMILY 3: Absorption-Weighted Binary Carry-Run Transducer & Odd/Even Dichotomy
-- ----------------------------------------------------------------------------

/-- Concrete binary carry-run `≤ L` transducer weighted by `(-1)^popcount((x+y) % 2^w) * t^absorptions(x,y)`. -/
def carryRunAbsTransducer (t : Int) (L : Nat) : CarryTransducer 2 (L + 1) where
  step q rx ry :=
    let cin := if q = 0 then 0 else 1
    let cout := (rx + ry + cin) / 2
    if cout = 0 then some 0
    else if q + 1 ≤ L then some (q + 1)
    else none
  wt q rx ry :=
    let cin := if q = 0 then 0 else 1
    let cout := (rx + ry + cin) / 2
    let s := (rx + ry + cin) % 2
    paritySign s * (if cin = 1 ∧ cout = 0 then t else 1)
  q0 := 0
  readout _ := 1
  hB := by omega
  hq0 := Nat.zero_lt_succ L
  hClosed := by
    intro q _ rx _ ry _ q' hstep
    dsimp only at hstep
    by_cases hco : (rx + ry + (if q = 0 then 0 else 1)) / 2 = 0
    · simp only [hco, ↓reduceIte] at hstep; injection hstep with heq; omega
    · simp only [hco, ↓reduceIte] at hstep
      by_cases hqL : q + 1 ≤ L
      · simp only [hqL, ↓reduceIte] at hstep; injection hstep with heq; omega
      · simp only [hqL, ↓reduceIte] at hstep; contradiction

/-- Exact semantic equivalence for `carryRunAbsTransducer t L`! -/
theorem evalPair_carryRunAbs (t : Int) (L : Nat) :
    ∀ w q x y, q ≤ L →
      evalPair (carryRunAbsTransducer t L) w q x y =
        if carryRunBounded 2 L w q x y then
          paritySign (digitSum 2 w (x + y + (if q = 0 then 0 else 1))) *
            t ^ carryAbsorptionsFrom 2 w (if q = 0 then 0 else 1) x y
        else 0 := by
  intro w
  induction w with
  | zero =>
    intro q x y hq
    simp [evalPair, carryRunAbsTransducer, carryRunBounded, digitSum, carryAbsorptionsFrom, hq]
  | succ k ih =>
    intro q x y hq
    let cin := if q = 0 then 0 else 1
    let cout := (x % 2 + y % 2 + cin) / 2
    have hmod := nat_add3_mod 2 x y (if q = 0 then 0 else 1)
    have hdiv := nat_add3_div 2 x y (if q = 0 then 0 else 1) (by omega)
    have hstep_lhs :
        evalPair (carryRunAbsTransducer t L) (k + 1) q x y =
        match (if cout = 0 then some 0 else if q + 1 ≤ L then some (q + 1) else none) with
        | none => 0
        | some q' =>
          (paritySign ((x % 2 + y % 2 + cin) % 2) * (if cin = 1 ∧ cout = 0 then t else 1)) *
            evalPair (carryRunAbsTransducer t L) k q' (x / 2) (y / 2) := rfl
    have hstep_rhs :
        carryRunBounded 2 L (k + 1) q x y =
        (decide ((if cout = 0 then 0 else q + 1) ≤ L) &&
          carryRunBounded 2 L k (if cout = 0 then 0 else q + 1) (x / 2) (y / 2)) := rfl
    rw [hstep_lhs, hstep_rhs]
    by_cases hco : cout = 0
    · simp only [hco, ↓reduceIte, Nat.zero_le, decide_true, Bool.true_and]
      rw [ih 0 (x / 2) (y / 2) (Nat.zero_le L)]
      simp only [↓reduceIte, digitSum, carryAbsorptionsFrom, hmod, hdiv]
      by_cases hb : carryRunBounded 2 L k 0 (x / 2) (y / 2) = true
      · simp only [hb, ↓reduceIte]
        change (paritySign ((x % 2 + y % 2 + cin) % 2) * (if cin = 1 ∧ True then t else 1)) *
            (paritySign (digitSum 2 k (x / 2 + y / 2 + 0)) * t ^ carryAbsorptionsFrom 2 k 0 (x / 2) (y / 2)) =
          paritySign ((x % 2 + y % 2 + cin) % 2 + digitSum 2 k (x / 2 + y / 2 + cout)) *
            t ^ ((if cin = 1 ∧ cout = 0 then 1 else 0) + carryAbsorptionsFrom 2 k cout (x / 2) (y / 2))
        rw [hco, paritySign_add]
        by_cases hcin1 : cin = 1
        · simp only [hcin1, and_self, ↓reduceIte]
          rw [Nat.add_comm 1, Int.pow_succ]
          rw [Int.mul_assoc, ← Int.mul_assoc t, Int.mul_comm t (paritySign _),
              Int.mul_assoc (paritySign _), ← Int.mul_assoc (paritySign _),
              Int.mul_comm t (t ^ _)]
        · simp only [hcin1, false_and, ↓reduceIte, Int.mul_one, Nat.zero_add, Int.mul_assoc]
      · simp [hb]
    · have hco1 : cout = 1 := by
        have hlt1 := Nat.mod_lt x (by omega : 0 < 2)
        have hlt2 := Nat.mod_lt y (by omega : 0 < 2)
        have hcin : cin ≤ 1 := by dsimp [cin]; split <;> omega
        dsimp [cout]; omega
      simp only [hco, ↓reduceIte]
      by_cases hqL : q + 1 ≤ L
      · simp only [hqL, ↓reduceIte, decide_true, Bool.true_and]
        rw [ih (q + 1) (x / 2) (y / 2) hqL]
        simp only [Nat.succ_ne_zero, ↓reduceIte, digitSum, carryAbsorptionsFrom, hmod, hdiv]
        by_cases hb : carryRunBounded 2 L k (q + 1) (x / 2) (y / 2) = true
        · simp only [hb, ↓reduceIte]
          change (paritySign ((x % 2 + y % 2 + cin) % 2) * (if cin = 1 ∧ False then t else 1)) *
              (paritySign (digitSum 2 k (x / 2 + y / 2 + 1)) * t ^ carryAbsorptionsFrom 2 k 1 (x / 2) (y / 2)) =
            paritySign ((x % 2 + y % 2 + cin) % 2 + digitSum 2 k (x / 2 + y / 2 + cout)) *
              t ^ ((if cin = 1 ∧ cout = 0 then 1 else 0) + carryAbsorptionsFrom 2 k cout (x / 2) (y / 2))
          rw [hco1, paritySign_add]
          simp [Int.mul_assoc]
        · simp [hb]
      · simp only [hqL, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true]

/-- Helper for evaluating a single state's 4 binary transitions in `carryRunAbsTransducer`. -/
theorem carryRunAbs_row_eval (t : Int) (L q i : Nat) (hL : 1 ≤ L) (vq : Int) :
    sumNat 2 (fun rx => sumNat 2 (fun ry =>
      match (carryRunAbsTransducer t L).step q rx ry with
      | none => 0
      | some q'' => if q'' = i then (carryRunAbsTransducer t L).wt q rx ry * vq else 0)) =
    if q = 0 then
      (if i = 0 then -1 * vq else if i = 1 then 1 * vq else 0)
    else
      (if i = 0 then -t * vq
       else if q + 1 ≤ L ∧ q + 1 = i then 1 * vq
       else 0) := by
  unfold carryRunAbsTransducer
  dsimp only [sumNat, paritySign]
  by_cases hq0 : q = 0
  · subst hq0
    simp only [↓reduceIte, hL]
    by_cases hi0 : i = 0
    · subst hi0; simp; omega
    · by_cases hi1 : i = 1
      · subst hi1; simp
      · have h0ne : (0 : Nat) ≠ i := fun h => hi0 h.symm
        have h1ne : (1 : Nat) ≠ i := fun h => hi1 h.symm
        simp [hi0, hi1, h0ne, h1ne]
  · simp only [hq0, ↓reduceIte]
    by_cases hqL : q + 1 ≤ L
    · simp only [hqL, ↓reduceIte, true_and]
      by_cases hi0 : i = 0
      · subst hi0
        simp [Int.neg_mul]
      · by_cases hqi : q + 1 = i
        · have h0ne : (0 : Nat) ≠ i := fun h => hi0 h.symm
          simp [hi0, hqi, h0ne]; omega
        · have h0ne : (0 : Nat) ≠ i := fun h => hi0 h.symm
          simp [hi0, hqi, h0ne]
    · simp only [hqL, ↓reduceIte, false_and]
      by_cases hi0 : i = 0
      · subst hi0; simp [Int.neg_mul]
      · have h0ne : (0 : Nat) ≠ i := fun h => hi0 h.symm
        simp [hi0, h0ne]

/-- Operator identification: `transferOp (carryRunAbsTransducer t L) = runOp L (-1) 1 (-t) 1`. -/
theorem transferOp_carryRunAbs_eq (t : Int) (L : Nat) (hL : 1 ≤ L)
    (u v : Nat → Int) (huv : ∀ i, i < L + 1 → u i = v i) :
    ∀ i, i < L + 1 →
      transferOp (carryRunAbsTransducer t L) u i = runOp L (-1) 1 (-t) 1 v i := by
  intro i hi
  unfold transferOp runOp
  rw [sumNat_congr (g := fun q =>
    if q = 0 then (if i = 0 then -1 * v q else if i = 1 then 1 * v q else 0)
    else (if i = 0 then -t * v q else if q + 1 ≤ L ∧ q + 1 = i then 1 * v q else 0))]
  · by_cases hi0 : i = 0
    · subst hi0
      simp only [↓reduceIte]
      rw [sumNat_succ_front]
      simp only [↓reduceIte]
      congr 1
      rw [← sumNat_mul_left]
      apply sumNat_congr; intro j _; simp
    · by_cases hi1 : i = 1
      · subst hi1
        simp only [hi0, ↓reduceIte]
        rw [sumNat_succ_front]
        simp only [↓reduceIte]
        have htail : sumNat L (fun j =>
            if j + 1 = 0 then 1 * v (j + 1)
            else if j + 1 + 1 ≤ L ∧ j + 1 + 1 = 1 then 1 * v (j + 1) else 0) = 0 := by
          rw [sumNat_congr (g := fun _ => 0)]
          · exact sumNat_zero_fn L
          · intro j _; simp
        rw [htail, Int.add_zero]
      · have hiL : i ≤ L := by omega
        simp only [hi0, hi1, hiL, ↓reduceIte]
        rw [sumNat_congr (g := fun q => if q = i - 1 then 1 * v (i - 1) else 0)]
        · exact sumNat_ite_eq (L + 1) (i - 1) (1 * v (i - 1)) (by omega)
        · intro q _
          by_cases hqi : q = i - 1
          · subst hqi
            have hqne0 : i - 1 ≠ 0 := by omega
            have hqeq : i - 1 + 1 = i := by omega
            simp [hqne0, hqeq, hiL]
          · by_cases hq0 : q = 0
            · subst hq0; simp [hqi]
            · have hne : q + 1 ≠ i := by omega
              simp [hq0, hqi, hne]
  · intro q hq
    rw [huv q hq]
    exact carryRunAbs_row_eval t L q i hL (v q)

theorem carryRunAbsSum_eq_runOp (t : Int) (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    carryRunAbsSum t L w = sumNat (L + 1) (iterOp (runOp L (-1) 1 (-t) 1) w (basisVec 0)) := by
  let T := carryRunAbsTransducer t L
  have hsem : carryRunAbsSum t L w = arithSum T w := by
    unfold carryRunAbsSum arithSum arithSumFrom maxCarryRunLe carryAbsorptions
    apply sumNat_congr; intro x _
    apply sumNat_congr; intro y _
    change (if carryRunBounded 2 L w 0 x y = true then
        paritySign (popcount w ((x + y) % 2 ^ w)) * t ^ carryAbsorptionsFrom 2 w 0 x y else 0) =
      evalPair (carryRunAbsTransducer t L) w 0 x y
    rw [evalPair_carryRunAbs t L w 0 x y (Nat.zero_le L)]
    simp only [↓reduceIte, Nat.add_zero, digitSum_mod_pow]
  rw [hsem, arithSum_eq_transferPow]
  have hq0 : T.q0 = 0 := rfl
  rw [hq0]
  have hagree := iterOp_eq_of_agree (transferOp T) (runOp L (-1) 1 (-t) 1)
    (transferOp_carryRunAbs_eq t L hL) w (basisVec 0)
  rw [dot_congr_right (L + 1) T.readout _ _ hagree]
  unfold dot T carryRunAbsTransducer
  apply sumNat_congr; intro i _; simp

/-- **THEOREM 3A (Exact Bivariate Absorption-Weighted Carry-Run 3-Term Recurrence)**:
    For EVERY integer absorption weight `t ∈ ℤ`, EVERY `L ≥ 1`, and EVERY bit-width `w : Nat`:
    `A_L(t, w + L + 2) = (1 - t) * A_L(t, w + L) + t * A_L(t, w)`! -/
theorem binary_carryRun_absorption_recurrence (t : Int) (L : Nat) (hL : 1 ≤ L) (w : Nat) :
    carryRunAbsSum t L (w + L + 2) =
      (1 - t) * carryRunAbsSum t L (w + L) + t * carryRunAbsSum t L w := by
  rw [carryRunAbsSum_eq_runOp t L hL (w + L + 2),
      carryRunAbsSum_eq_runOp t L hL (w + L),
      carryRunAbsSum_eq_runOp t L hL w]
  have hrec := quad_annihilator_recurrence (runOp L (-1) 1 (-t) 1) L
    (-1 + 1) ((-1) * 1 - 1 * (-t)) (1 * (-t) * (1 : Int) ^ L)
    (runOp_annihilator L hL (-1) 1 (-t) 1) (fun _ => 1) (basisVec 0) w
  have hdot : ∀ u, dot (L + 1) (fun _ => 1) u = sumNat (L + 1) u := by
    intro u; unfold dot; apply sumNat_congr; intro i _; simp
  rw [hdot, hdot, hdot, hdot] at hrec
  simp only [Int.one_pow, Int.mul_one, Int.one_mul] at hrec
  rw [hrec]
  have h0 : (-1 + 1 : Int) = 0 := by decide
  have hc : (-1 - -t : Int) = -(1 - t) := by omega
  rw [h0, Int.zero_mul, hc, Int.neg_mul, Int.neg_mul]
  omega

/-- Exact state vector at `t = 0` (zero carry absorptions) for `runOp L (-1) 1 0 1`! -/
theorem runOp_zeroAbs_state (L : Nat) (hL : 1 ≤ L) :
    ∀ w i, i < L + 1 →
      iterOp (runOp L (-1) 1 0 1) w (basisVec 0) i =
        if i = 0 then paritySign w
        else if i ≤ w then paritySign (w - i)
        else 0 := by
  intro w
  induction w with
  | zero =>
    intro i _
    simp only [iterOp_zero, basisVec, paritySign_zero]
    by_cases hi0 : i = 0
    · simp [hi0]
    · simp [hi0, show ¬ (i ≤ 0) by omega]
  | succ k ih =>
    intro i hi
    rw [iterOp_succ]
    by_cases hi0 : i = 0
    · subst hi0
      rw [runOp_at_zero, Int.zero_mul, Int.add_zero, ih 0 (by omega)]
      simp only [↓reduceIte, paritySign_succ]
      omega
    · by_cases hi1 : i = 1
      · subst hi1
        rw [runOp_at_one, Int.one_mul, ih 0 (by omega)]
        simp
      · rw [runOp_at_mid L (-1) 1 0 1 _ i (by omega) (by omega), Int.one_mul, ih (i - 1) (by omega)]
        have him1_ne0 : i - 1 ≠ 0 := by omega
        simp only [hi0, him1_ne0, ↓reduceIte]
        by_cases hle : i ≤ k + 1
        · have hle' : i - 1 ≤ k := by omega
          have hsub : k - (i - 1) = k + 1 - i := by omega
          simp [hle, hle', hsub]
        · have hle' : ¬ (i - 1 ≤ k) := by omega
          simp [hle, hle']

/-- **THEOREM 3B (Zero-Absorption Odd/Even Dichotomy at `t = 0`)**:
    Over all `w`-bit pairs `(x, y)` with `carryRun(x, y) ≤ L` and ZERO carry absorptions:
    - For EVERY **odd** `L = 2k + 1` and EVERY `w ≥ L`: `A_{2k+1}(0, w) = 0` (exact finite support!).
    - For EVERY **even** `L = 2k` (`k ≥ 1`) and EVERY `w ≥ L`: `A_{2k}(0, w) = (-1)^w` (persistent oscillation!). -/
theorem binary_zeroAbsorption_dichotomy (L : Nat) (hL : 1 ≤ L) (w : Nat) (hw : L ≤ w) :
    carryRunAbsSum 0 L w = if L % 2 = 1 then 0 else paritySign w := by
  rw [carryRunAbsSum_eq_runOp 0 L hL w]
  have hneg0 : -(0 : Int) = 0 := rfl
  rw [hneg0]
  rw [sumNat_congr (g := fun i => paritySign (w - i))]
  · have hrev : sumNat (L + 1) (fun i => paritySign (w - i)) =
        sumNat (L + 1) (fun j => paritySign ((w - L) + j)) := by
      have hsame : ∀ n a, n ≤ a + 1 →
          sumNat n (fun i => paritySign (a - i)) =
          sumNat n (fun j => paritySign ((a + 1 - n) + j)) := by
        intro n
        induction n with
        | zero => intro a _; rfl
        | succ m ih =>
          intro a hma
          rw [sumNat_succ, sumNat_succ_front]
          rw [ih a (by omega)]
          have hfirst : a + 1 - (m + 1) + 0 = a - m := by omega
          rw [hfirst, Int.add_comm]
          congr 1
          apply sumNat_congr
          intro j hj
          congr 1; omega
      have h := hsame (L + 1) w (by omega)
      have hsimp : w + 1 - (L + 1) = w - L := by omega
      rw [hsimp] at h
      exact h
    rw [hrev, sumNat_parity_range]
    by_cases hodd : L % 2 = 1
    · simp [hodd, show (L + 1) % 2 = 0 by omega]
    · have h1 : (L + 1) % 2 = 1 := by omega
      have hpeq : paritySign (w - L) = paritySign w := by
        unfold paritySign
        simp [show (w - L) % 2 = w % 2 by omega]
      simp [hodd, h1, hpeq]
  · intro i hi
    rw [runOp_zeroAbs_state L hL w i hi]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · simp [hi0, show i ≤ w by omega]

-- ============================================================================
-- SECTION 7: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples
-- ============================================================================

/-- Non-Vacuity Witness 1: There exist concrete pairs `(x, y)` with non-trivial carry runs,
    ripple depths, and carry absorptions inhabiting all theorem hypotheses (`L = 2, w = 4`). -/
theorem nonvacuity_witness_carry_chains :
    ∃ (x y : Nat),
      x < 2 ^ 4 ∧ y < 2 ^ 4 ∧
      maxCarryRunLe 2 2 4 x y = true ∧
      maxCarryRunLe 2 1 4 x y = false ∧
      maxRippleDepthLe 2 2 4 x y = true ∧
      carryAbsorptions 2 4 x y = 1 := by
  exact ⟨3, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Non-Vacuity Witness 2: Strict separation between `rippleDepth` and `carryRun`!
    At `w = 3`, `x = 7 (111₂), y = 7 (111₂)` has `carryRun = 3 > 1` (fails `maxCarryRunLe 2 1`),
    yet `rippleDepth = 1 ≤ 1` (passes `maxRippleDepthLe 2 1`, because every bit is Generate `G`)! -/
theorem nonvacuity_witness_ripple_vs_run_separation :
    maxRippleDepthLe 2 1 3 7 7 = true ∧ maxCarryRunLe 2 1 3 7 7 = false := by
  decide

/-- Sharpness Counterexample S1 (Swapping Carry-Run + Input Parity Breaks BOTH Collapses):
    For `L = 1, w = 3`, the input-parity sum over `carryRun ≤ 1` is `-1 ≠ 0` (breaks Theorem 2's
    period-2 vanishing), and at `w = 4` it equals `2` (breaks Theorem 1's `{-1, 0, +1}` bound)! -/
theorem sharpness_S1_carryRun_inputParity_breaks :
    sumNat (2 ^ 3) (fun x => sumNat (2 ^ 3) (fun y =>
      if maxCarryRunLe 2 1 3 x y then paritySign (popcount 3 x + popcount 3 y) else 0)) = -1 ∧
    sumNat (2 ^ 4) (fun x => sumNat (2 ^ 4) (fun y =>
      if maxCarryRunLe 2 1 4 x y then paritySign (popcount 4 x + popcount 4 y) else 0)) = 2 := by
  decide

/-- Sharpness Counterexample S2 (Swapping Ripple-Depth + Output Parity Breaks Bounded Collapse):
    For `L = 1, w = 3`, the output-parity sum over `rippleDepth ≤ 1` equals `4` (outside `{-1,0,1}`)! -/
theorem sharpness_S2_rippleDepth_outputParity_breaks :
    sumNat (2 ^ 3) (fun x => sumNat (2 ^ 3) (fun y =>
      if maxRippleDepthLe 2 1 3 x y then paritySign (popcount 3 ((x + y) % 2 ^ 3)) else 0)) = 4 := by
  decide

/-- Sharpness Counterexample S3 (Odd Radix `B = 3` Breaks BOTH Collapses Immediately at `w = 1, L = 1`):
    - Ripple-depth input-parity sum = `1 ≠ 0` (violates `(L+1) ∤ w → 0`),
    - Carry-run output-parity sum = `3 ∉ {-1, 0, +1}` (violates cyclotomic collapse)! -/
theorem sharpness_S3_odd_radix_breaks :
    sumNat (3 ^ 1) (fun x => sumNat (3 ^ 1) (fun y =>
      if maxRippleDepthLe 3 1 1 x y then paritySign (digitSum 3 1 x + digitSum 3 1 y) else 0)) = 1 ∧
    sumNat (3 ^ 1) (fun x => sumNat (3 ^ 1) (fun y =>
      if maxCarryRunLe 3 1 1 x y then paritySign (digitSum 3 1 ((x + y) % 3 ^ 1)) else 0)) = 3 := by
  decide

/-- Sharpness Counterexample S4 (Non-Unit Absorption Weight `t = -1` Breaks Periodicity):
    For `L = 1, t = -1, w = 4`, `carryRunAbsSum (-1) 1 4 = 2 ∉ {-1, 0, +1}`! -/
theorem sharpness_S4_absorption_weight_breaks :
    carryRunAbsSum (-1) 1 4 = 2 := by
  decide

/-- Sharpness Counterexample S5 (Odd vs Even `L` Sharpness at Zero Absorption `t = 0`):
    At `w = 3`, odd `L = 1` gives `0` (vanishes), whereas even `L = 2` gives `-1 ≠ 0`! -/
theorem sharpness_S5_zeroAbs_odd_vs_even :
    carryRunAbsSum 0 1 3 = 0 ∧ carryRunAbsSum 0 2 3 = -1 := by
  decide

end SiliconCarryTransfer

-- ============================================================================
-- SECTION 8: Kernel Axiom Audit (`#print axioms` on Every Main Theorem)
-- ============================================================================


