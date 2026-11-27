/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CaTorsionLyapunovFluxCompiler.Defs

/-!
# Proofs for the CA Torsion / Lyapunov Flux Compiler

Bit-slicing and window-evolution lemmas, the general soundness meta-theorems
(finite certificate => all ring widths `w >= 1`), and the infinite theorems discharged by kernel `decide`.
-/

namespace CAFluxCompiler

-- ============================================================================
-- Section 1: Pure-Silicon Bit Packing & Bitring Primitives
-- ============================================================================

theorem packBits_lt (w : Nat) (f : Nat → Bool) : packBits w f < 2 ^ w := by
  induction w with
  | zero => simp [packBits]
  | succ w ih =>
    simp only [packBits, Nat.pow_succ]
    cases f w <;> simp <;> omega

theorem testBit_packBits (w : Nat) (f : Nat → Bool) (i : Nat) (hi : i < w) :
    (packBits w f).testBit i = f i := by
  induction w with
  | zero => omega
  | succ w ih =>
    simp only [packBits]
    by_cases hEq : i = w
    · subst hEq
      have hlt := packBits_lt i f
      cases hf : f i
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
        rfl
      · simp only [↓reduceIte]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
        have hdiv : (packBits i f + 2 ^ i) / 2 ^ i = 1 := by
          have : packBits i f / 2 ^ i = 0 := Nat.div_eq_of_lt hlt
          rw [Nat.add_div_right _ hpos, this]
        rw [hdiv]; rfl
    · have hlt : i < w := by omega
      cases hf : f w
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact ih hlt
      · simp only [↓reduceIte]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ w = 2 ^ i * 2 ^ (w - i) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
        have hdiv : (packBits w f + 2 ^ w) / 2 ^ i =
                    packBits w f / 2 ^ i + 2 ^ (w - i) := by
          rw [hpow, Nat.add_mul_div_left _ _ hpos]
        rw [hdiv]
        have heven : 2 ∣ 2 ^ (w - i) := by
          have hsub : w - i = (w - i - 1) + 1 := by omega
          rw [hsub, Nat.pow_succ]
          exact Nat.dvd_mul_left 2 _
        rcases heven with ⟨q, hq⟩
        have hmod : (packBits w f / 2 ^ i + 2 ^ (w - i)) % 2 =
                    (packBits w f / 2 ^ i) % 2 := by
          rw [hq, Nat.add_mul_mod_self_left]
        have hand : ∀ n : Nat, (1 &&& n) = n % 2 := by
          intro n; rw [Nat.and_comm]; exact Nat.and_one_is_mod n
        rw [hand, hmod, ← hand]
        have ih' := ih hlt
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow] at ih'
        exact ih'

theorem getLsbD_bvOfFn (w : Nat) (f : Nat → Bool) (i : Nat) (hi : i < w) :
    (bvOfFn w f).getLsbD i = f i := by
  simp only [bvOfFn, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  exact testBit_packBits w f i hi

theorem ringBit_mod {w : Nat} (x : BitVec w) (i : Nat) :
    ringBit x (i % w) = ringBit x i := by
  simp [ringBit]

theorem ringBit_add_w {w : Nat} (x : BitVec w) (i : Nat) :
    ringBit x (i + w) = ringBit x i := by
  simp [ringBit, Nat.add_mod_right]

theorem ringBit_congr {w : Nat} (x : BitVec w) {i j : Nat} (h : i % w = j % w) :
    ringBit x i = ringBit x j := by
  simp [ringBit, h]

theorem ringBit_ringRot {w : Nat} (hw : 0 < w) (s : Nat) (x : BitVec w) (i : Nat) :
    ringBit (ringRot s x) i = ringBit x (i + s) := by
  have hi : i % w < w := Nat.mod_lt i hw
  simp only [ringBit, ringRot]
  rw [getLsbD_bvOfFn w _ (i % w) hi]
  apply ringBit_congr
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem ringRot_zero {w : Nat} (x : BitVec w) : ringRot 0 x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ringRot]
  rw [getLsbD_bvOfFn w _ i hi]
  simp only [ringBit, Nat.add_zero, Nat.mod_eq_of_lt hi]

theorem ringBit_eq_imp_eq {w : Nat} {x y : BitVec w}
    (h : ∀ i : Nat, i < w → ringBit x i = ringBit y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h0 := h i hi
  simpa [ringBit, Nat.mod_eq_of_lt hi] using h0

theorem ringRot_inj {w : Nat} (hw : 0 < w) (s : Nat) {x y : BitVec w}
    (h : ringRot s x = ringRot s y) : x = y := by
  apply ringBit_eq_imp_eq
  intro i _hi
  have h1 : ringBit (ringRot s x) (i + w - (s % w)) =
            ringBit (ringRot s y) (i + w - (s % w)) := by rw [h]
  rw [ringBit_ringRot hw, ringBit_ringRot hw] at h1
  have hmod : (i + w - (s % w) + s) % w = i % w := by
    have hs : s % w < w := Nat.mod_lt s hw
    have hdiv : s = w * (s / w) + s % w := (Nat.div_add_mod s w).symm
    have hmul : w * (s / w + 1) = w * (s / w) + w := by rw [Nat.mul_add, Nat.mul_one]
    have hEq : i + w - (s % w) + s = i + w * (s / w + 1) := by omega
    rw [hEq, Nat.add_mul_mod_self_left]
  rw [ringBit_congr x hmod, ringBit_congr y hmod] at h1
  exact h1

theorem window_lt (m : Nat) {w : Nat} (x : BitVec w) (i : Nat) :
    window m x i < 2 ^ m := by
  induction m generalizing i with
  | zero => simp [window]
  | succ m ih =>
    simp only [window, Nat.pow_succ]
    have h := ih (i + 1)
    cases ringBit x i <;> simp <;> omega

theorem window_congr (m : Nat) {w : Nat} (x : BitVec w) {i j : Nat}
    (h : i % w = j % w) : window m x i = window m x j := by
  induction m generalizing i j with
  | zero => rfl
  | succ m ih =>
    simp only [window]
    have hb : ringBit x i = ringBit x j := ringBit_congr x h
    have h1 : (i + 1) % w = (j + 1) % w := by
      rw [Nat.add_mod, h, ← Nat.add_mod]
    rw [hb, ih h1]

theorem window_add_w (m : Nat) {w : Nat} (x : BitVec w) (i : Nat) :
    window m x (i + w) = window m x i :=
  window_congr m x (Nat.add_mod_right i w)

theorem subWin_lt (u a p : Nat) : subWin u a p < 2 ^ p :=
  Nat.mod_lt _ (Nat.two_pow_pos p)

theorem window_div_two (m : Nat) {w : Nat} (x : BitVec w) (i : Nat) :
    window (m + 1) x i / 2 = window m x (i + 1) := by
  simp only [window]
  cases ringBit x i <;> simp <;> omega

theorem window_mod_two (m : Nat) {w : Nat} (x : BitVec w) (i : Nat) :
    window (m + 1) x i % 2 = if ringBit x i then 1 else 0 := by
  simp only [window]
  cases ringBit x i <;> simp <;> omega

theorem window_div_pow (a m : Nat) {w : Nat} (x : BitVec w) (i : Nat) :
    window (a + m) x i / (2 ^ a) = window m x (i + a) := by
  induction a generalizing i with
  | zero => simp [Nat.add_zero]
  | succ a ih =>
    have h1 : a + 1 + m = (a + m) + 1 := by omega
    rw [h1, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    have h2 : window (a + m + 1) x i / (2 ^ a) / 2 =
              (window (a + m + 1) x i / 2) / (2 ^ a) := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [h2, window_div_two, ih (i + 1)]
    have h3 : i + 1 + a = i + (a + 1) := by omega
    rw [h3]

theorem window_mod_pow (p r : Nat) {w : Nat} (x : BitVec w) (i : Nat) :
    window (p + r) x i % (2 ^ p) = window p x i := by
  induction p generalizing i with
  | zero => simp [window, Nat.mod_one]
  | succ p ih =>
    have h1 : p + 1 + r = (p + r) + 1 := by omega
    rw [h1, window, window, Nat.pow_succ]
    have hrec := ih (i + 1)
    have hmod : ∀ (b y d : Nat), b ≤ 1 → (b + 2 * y) % (d * 2) = b + 2 * (y % d) := by
      intro b y d hb
      have hdm : y = d * (y / d) + y % d := (Nat.div_add_mod y d).symm
      have hmul2 : (d * 2) * (y / d) = 2 * (d * (y / d)) := by
        rw [Nat.mul_comm d 2, Nat.mul_assoc]
      have hdiv : b + 2 * y = (d * 2) * (y / d) + (b + 2 * (y % d)) := by omega
      by_cases hd : d = 0
      · subst hd; simp
      · have hlt2 : b + 2 * (y % d) < d * 2 := by
          have := Nat.mod_lt y (Nat.pos_of_ne_zero hd)
          omega
        rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt2]
    cases hb : ringBit x i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hmod 0 (window (p + r) x (i + 1)) (2 ^ p) (by omega), hrec]
    · simp only [↓reduceIte]
      rw [hmod 1 (window (p + r) x (i + 1)) (2 ^ p) (by omega), hrec]

/-- Exact bit-slicing theorem: extracting `[a, a+p)` from an `M`-bit window gives
    the `p`-bit window at `i + a`. -/
theorem subWin_window {M a p : Nat} (h : a + p ≤ M) {w : Nat} (x : BitVec w) (i : Nat) :
    subWin (window M x i) a p = window p x (i + a) := by
  have hM : M = a + (p + (M - (a + p))) := by omega
  rw [hM, subWin, window_div_pow, window_mod_pow]

/-- Exact single-bit extraction from an `M`-bit window. -/
theorem testBit_window {M a : Nat} (h : a < M) {w : Nat} (x : BitVec w) (i : Nat) :
    (window M x i).testBit a = ringBit x (i + a) := by
  have hsub : subWin (window M x i) a 1 = window 1 x (i + a) :=
    subWin_window (by omega) x i
  have htb : (window M x i).testBit a = ((window M x i / 2 ^ a) % 2 == 1) := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    simp
  rw [htb]
  simp only [subWin, Nat.pow_one] at hsub
  rw [hsub]
  simp only [window, Nat.mul_zero, Nat.add_zero]
  cases ringBit x (i + a) <;> rfl

-- ============================================================================
-- Section 2: Cellular Automaton Step, Composition, and Window Evolution
-- ============================================================================

theorem caIter_succ (k off rule t : Nat) {w : Nat} (x : BitVec w) :
    caIter k off rule (t + 1) x = caStep k off rule (caIter k off rule t x) := rfl

theorem caIter_add (k off rule t1 t2 : Nat) {w : Nat} (x : BitVec w) :
    caIter k off rule (t1 + t2) x = caIter k off rule t2 (caIter k off rule t1 x) := by
  induction t2 with
  | zero => rfl
  | succ t2 ih =>
    rw [← Nat.add_assoc, caIter_succ, ih, caIter_succ]

theorem ringBit_caStep (k off rule : Nat) {w : Nat} (hw : 0 < w) (x : BitVec w) (i : Nat) :
    ringBit (caStep k off rule x) (i + off) = rule.testBit (window k x i) := by
  have hi : (i + off) % w < w := Nat.mod_lt _ hw
  simp only [ringBit, caStep]
  rw [getLsbD_bvOfFn w _ ((i + off) % w) hi]
  congr 1
  apply window_congr
  have hoff : off % w < w := Nat.mod_lt off hw
  have hdiv : off = w * (off / w) + off % w := (Nat.div_add_mod off w).symm
  have hmul : w * (off / w + 1) = w * (off / w) + w := by rw [Nat.mul_add, Nat.mul_one]
  have h1 : ((i + off) % w + w - off % w) % w = (i + off + w - off % w) % w := by
    have hq : i + off = w * ((i + off) / w) + (i + off) % w := (Nat.div_add_mod _ w).symm
    have hEq : i + off + w - off % w = ((i + off) % w + w - off % w) + w * ((i + off) / w) := by omega
    rw [hEq, Nat.add_mul_mod_self_left]
  rw [h1]
  have h2 : i + off + w - off % w = i + w * (off / w + 1) := by omega
  rw [h2, Nat.add_mul_mod_self_left]

/-- Translation equivariance: `T` commutes with cyclic rotation `ringRot s`. -/
theorem caStep_ringRot (k off rule s : Nat) {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep k off rule (ringRot s x) = ringRot s (caStep k off rule x) := by
  apply ringRot_inj hw off
  apply ringBit_eq_imp_eq
  intro i _hi
  rw [ringBit_ringRot hw, ringBit_caStep k off rule hw]
  rw [ringBit_ringRot hw, ringBit_ringRot hw]
  have hcomm : i + off + s = (i + s) + off := by omega
  rw [hcomm, ringBit_caStep k off rule hw]
  congr 1
  have hwin : ∀ m j, window m (ringRot s x) j = window m x (j + s) := by
    intro m
    induction m with
    | zero => intro j; rfl
    | succ m ih =>
      intro j
      simp only [window, ringBit_ringRot hw, ih]
      have : j + 1 + s = j + s + 1 := by omega
      rw [this]
  exact hwin k i

theorem nextWindowAux_lt (k rule p j u : Nat) : nextWindowAux k rule p j u < 2 ^ p := by
  induction p generalizing j with
  | zero => simp [nextWindowAux]
  | succ p ih =>
    simp only [nextWindowAux, Nat.pow_succ]
    have h := ih (j + 1)
    cases rule.testBit (subWin u j k) <;> simp <;> omega

theorem nextWindow_lt (k rule p u : Nat) : nextWindow k rule p u < 2 ^ p :=
  nextWindowAux_lt k rule p 0 u

theorem window_caStep_aux (k off rule : Nat) {w : Nat} (hw : 0 < w)
    (x : BitVec w) (i M : Nat) :
    ∀ (p j : Nat), j + p + k ≤ M + 1 → p ≥ 1 →
      window p (caStep k off rule x) (i + j + off) =
      nextWindowAux k rule p j (window M x i) := by
  intro p
  induction p with
  | zero => intro _ _ hp; omega
  | succ p ih =>
    intro j hM _
    simp only [window, nextWindowAux]
    have hjk : j + k ≤ M := by omega
    rw [ringBit_caStep k off rule hw, subWin_window hjk]
    cases p with
    | zero => simp [window, nextWindowAux]
    | succ p' =>
      have hrec := ih (j + 1) (by omega) (by omega)
      have hidx : i + j + off + 1 = i + (j + 1) + off := by omega
      rw [hidx, hrec]

theorem window_caStep (k off rule p M : Nat) (hp : 1 ≤ p) (hM : p + k ≤ M + 1)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (i : Nat) :
    window p (caStep k off rule x) (i + off) = nextWindow k rule p (window M x i) := by
  have h := window_caStep_aux k off rule hw x i M p 0 (by omega) hp
  simpa [nextWindow] using h

/-- Exact 2-step composition bridge theorem: for ANY `k=3, off=1` CA rule and ANY bitring
    of ANY length `w ≥ 1`, stepping once by the compiled `k=5, off=2` rule equals stepping
    twice by the original `k=3` rule! -/
theorem caStep_compose2 (rule : Nat) {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep 5 2 (compose2Rule rule) x = caStep 3 1 rule (caStep 3 1 rule x) := by
  apply ringRot_inj hw 2
  apply ringBit_eq_imp_eq
  intro i _hi
  rw [ringBit_ringRot hw, ringBit_ringRot hw]
  rw [ringBit_caStep 5 2 (compose2Rule rule) hw]
  have h2 : i + 2 = (i + 1) + 1 := by omega
  rw [h2, ringBit_caStep 3 1 rule hw]
  rw [window_caStep 3 1 rule 3 5 (by omega) (by omega) hw]
  have hlt : window 5 x i < 32 := window_lt 5 x i
  exact testBit_packBits 32 (fun u => rule.testBit (nextWindow 3 rule 3 u)) (window 5 x i) hlt

theorem caIter_compose2 (rule t : Nat) {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caIter 5 2 (compose2Rule rule) t x = caIter 3 1 rule (2 * t) x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [caIter_succ, ih, caStep_compose2 rule hw]
    have h2 : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
    rw [h2, caIter_succ, caIter_succ]

-- ============================================================================
-- Section 3: Exact Segment Sums, Discrete Telescoping, and Shift Invariance
-- ============================================================================

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih]; omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih]; omega

theorem sumRange_const (n : Nat) (c : Int) :
    sumRange n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.natCast_succ]
    rw [Int.add_mul, Int.one_mul]

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    rw [Int.mul_add]

theorem sumRange_congr (n : Nat) {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumRange_le (n : Nat) {f g : Nat → Int}
    (h : ∀ i, i < n → f i ≤ g i) : sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    omega

theorem sumRange_zero_of_eq (n : Nat) {f : Nat → Int}
    (h : ∀ i, i < n → f i = 0) : sumRange n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange, ih (fun i hi => h i (by omega)), h n (by omega)]
    omega

theorem sumRange_dvd (n : Nat) (d : Int) {f : Nat → Int}
    (h : ∀ i, i < n → f i % d = 0) : sumRange n f % d = 0 := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    rw [Int.add_emod, h1, h2]
    simp

/-- Constructive pigeonhole lemma (ZERO Classical.choice!): if a sum of `N` natural
    numbers is strictly less than `N`, then at least one term is `0`. -/
theorem exists_zero_of_sum_lt (N : Nat) (f : Nat → Nat)
    (h : sumRange N (fun t => (f t : Int)) < (N : Int)) :
    ∃ t, t < N ∧ f t = 0 := by
  induction N with
  | zero => simp [sumRange] at h
  | succ N ih =>
    simp only [sumRange] at h
    by_cases hf : f N = 0
    · exact ⟨N, by omega, hf⟩
    · have hge : (1 : Int) ≤ (f N : Int) := by omega
      have hlt : sumRange N (fun t => (f t : Int)) < (N : Int) := by omega
      rcases ih hlt with ⟨t, ht, h0⟩
      exact ⟨t, by omega, h0⟩

/-- Discrete 1D Gauss Divergence / Telescoping Lemma. -/
theorem sumRange_telescoping (n : Nat) (h : Nat → Int) :
    sumRange n (fun i => h (i + 1) - h i) = h n - h 0 := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    omega

/-- Shift invariance of a full-period sum on a periodic sequence. -/
theorem sumRange_periodic_shift1 (w : Nat) (f : Nat → Int)
    (hper : ∀ i, f (i + w) = f i) :
    sumRange w (fun i => f (i + 1)) = sumRange w f := by
  have htel := sumRange_telescoping w f
  rw [sumRange_sub] at htel
  have h0 : f w = f 0 := by simpa [Nat.zero_add] using hper 0
  omega

theorem sumRange_periodic_shift (w s : Nat) (f : Nat → Int)
    (hper : ∀ i, f (i + w) = f i) :
    sumRange w (fun i => f (i + s)) = sumRange w f := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hper' : ∀ i, f (i + w + s) = f (i + s) := by
      intro i
      have : i + w + s = (i + s) + w := by omega
      rw [this, hper]
    have h1 : sumRange w (fun i => f ((i + 1) + s)) = sumRange w (fun i => f (i + s)) :=
      sumRange_periodic_shift1 w (fun i => f (i + s)) hper'
    have h2 : (fun i => f (i + (s + 1))) = (fun i => f ((i + 1) + s)) := by
      funext i; congr 1; omega
    rw [h2, h1, ih]

theorem rangeMin_le (n : Nat) (f : Nat → Int) {u : Nat} (hu : u < n) :
    rangeMin n f ≤ f u := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [rangeMin]
    cases m with
    | zero =>
      have : u = 0 := by omega
      subst this; simp
    | succ m' =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
      by_cases hEq : u = m' + 1
      · subst hEq; exact Int.min_le_right _ _
      · exact Int.le_trans (Int.min_le_left _ _) (ih (by omega))

theorem le_rangeMax (n : Nat) (f : Nat → Int) {u : Nat} (hu : u < n) :
    f u ≤ rangeMax n f := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [rangeMax]
    cases m with
    | zero =>
      have : u = 0 := by omega
      subst this; simp
    | succ m' =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
      by_cases hEq : u = m' + 1
      · subst hEq; exact Int.le_max_right _ _
      · exact Int.le_trans (ih (by omega)) (Int.le_max_left _ _)

-- ============================================================================
-- Section 4: Pure-Data Certificate Format & Kernel-Decidable Verifiers
-- ============================================================================

theorem shiftEq_self_iff {w : Nat} (hw : 0 < w) (off : Nat) (y x : BitVec w) :
    shiftEq off off y x ↔ y = x := by
  constructor
  · exact ringRot_inj hw off
  · intro h; rw [shiftEq, h]

theorem shiftEq_rotL_iff {w : Nat} (hw : 0 < w) (off s : Nat) (y x : BitVec w) :
    shiftEq off (off + s) y x ↔ y = ringRot s x := by
  constructor
  · intro h
    apply ringRot_inj hw off
    rw [h]
    apply ringBit_eq_imp_eq
    intro i _hi
    rw [ringBit_ringRot hw, ringBit_ringRot hw, ringBit_ringRot hw]
    congr 1; omega
  · intro h
    rw [shiftEq, h]
    apply ringBit_eq_imp_eq
    intro i _hi
    rw [ringBit_ringRot hw, ringBit_ringRot hw, ringBit_ringRot hw]
    congr 1; omega

theorem checkAll_true_iff (n : Nat) (pred : Nat → Bool) :
    checkAll n pred = true ↔ ∀ u, u < n → pred u = true := by
  induction n with
  | zero => simp [checkAll]
  | succ n ih =>
    simp only [checkAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ u hu
      by_cases hEq : u = n
      · subst hEq; exact h2
      · exact h1 u (by omega)
    · intro h
      exact ⟨fun u hu => h u (by omega), h n (by omega)⟩

-- ============================================================================
-- Section 5: General Soundness Meta-Theorems (Finite Certificate -> ∀ w ≥ 1)
-- ============================================================================

/-- Helper unpacking `checkWidths cert = true`. -/
theorem widths_of_checkWidths {cert : CACert} (h : checkWidths cert = true) :
    1 ≤ cert.k ∧ 1 ≤ cert.p ∧ 1 ≤ cert.q ∧
    cert.p + cert.k ≤ cert.M + 1 ∧ cert.q + 1 ≤ cert.M ∧
    cert.align + cert.p ≤ cert.M ∧ cert.k ≤ cert.M := by
  simp only [checkWidths, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- Key pointwise identity linking `localDelta cert (window M x i)` to ring evaluations. -/
theorem localDelta_at_window {cert : CACert} (hw_ok : checkWidths cert = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (i : Nat) :
    localDelta cert (window cert.M x i) =
      (tableAt cert.phi (window cert.p (caStep cert.k cert.off cert.rule x) (i + cert.off)) -
       tableAt cert.phi (window cert.p x (i + cert.align))) +
      (tableAt cert.psi (window cert.q x (i + 1)) -
       tableAt cert.psi (window cert.q x i)) := by
  rcases widths_of_checkWidths hw_ok with ⟨_, hp, _, hpk, hq1, hap, _⟩
  simp only [localDelta]
  rw [window_caStep cert.k cert.off cert.rule cert.p cert.M hp hpk hw x i]
  rw [subWin_window hap x i]
  have h1q : 1 + cert.q ≤ cert.M := by omega
  rw [subWin_window h1q x i]
  have h0q : 0 + cert.q ≤ cert.M := by omega
  rw [subWin_window h0q x i]
  simp only [Nat.add_zero]
  omega

/-- Shared segment summation identity: summing `localDelta` over `[0, n)` telescopes
    the flux `ψ` to `ψ(W_q(x, n)) - ψ(W_q(x, 0))`. -/
theorem sumRange_localDelta_seg {cert : CACert} (hw_ok : checkWidths cert = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (n : Nat) :
    sumRange n (fun i => localDelta cert (window cert.M x i)) =
      (segPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) cert.off n -
       segPotential cert.p cert.phi x cert.align n) +
      (tableAt cert.psi (window cert.q x n) -
       tableAt cert.psi (window cert.q x 0)) := by
  rw [sumRange_congr n (fun i _ => localDelta_at_window hw_ok hw x i)]
  rw [sumRange_add, sumRange_sub]
  rw [sumRange_telescoping n (fun i => tableAt cert.psi (window cert.q x i))]
  rfl

/-- Shared full-ring summation identity: on any periodic ring `w ≥ 1`, summing `localDelta`
    over `[0, w)` cancels the flux completely and yields `Φ(T(x)) - Φ(x)`. -/
theorem sumRange_localDelta_ring {cert : CACert} (hw_ok : checkWidths cert = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    sumRange w (fun i => localDelta cert (window cert.M x i)) =
      ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) -
      ringPotential cert.p cert.phi x := by
  rw [sumRange_localDelta_seg hw_ok hw x w]
  have hper_psi : window cert.q x w = window cert.q x 0 := by
    simpa [Nat.zero_add] using window_add_w cert.q x 0
  rw [hper_psi]
  have hsn : segPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) cert.off w =
      ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) :=
    sumRange_periodic_shift w cert.off
      (fun i => tableAt cert.phi (window cert.p (caStep cert.k cert.off cert.rule x) i))
      (fun i => by rw [window_add_w])
  have hso : segPotential cert.p cert.phi x cert.align w =
      ringPotential cert.p cert.phi x :=
    sumRange_periodic_shift w cert.align
      (fun i => tableAt cert.phi (window cert.p x i))
      (fun i => by rw [window_add_w])
  rw [hsn, hso]
  omega

/-- Meta-Theorem 0 (Discrete Gauss / Open-Segment Continuity Equation):
    For ANY `checkConservation`-verified certificate, ANY ring `x : BitVec w` (`w ≥ 1`),
    and ANY open segment `[0, n)`, the change in segment potential equals the exact
    difference of boundary fluxes `ψ(W_q(x, 0)) - ψ(W_q(x, n))`. -/
theorem soundness_openSegment_balance (cert : CACert)
    (hcert : checkConservation cert = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (n : Nat) :
    segPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) cert.off n -
    segPotential cert.p cert.phi x cert.align n =
    tableAt cert.psi (window cert.q x 0) - tableAt cert.psi (window cert.q x n) := by
  simp only [checkConservation, Bool.and_eq_true] at hcert
  rcases hcert with ⟨hw_ok, hall⟩
  rw [checkAll_true_iff] at hall
  have hsum0 : sumRange n (fun i => localDelta cert (window cert.M x i)) = 0 := by
    apply sumRange_zero_of_eq
    intro i _
    have hEq := hall (window cert.M x i) (window_lt cert.M x i)
    simpa [beq_iff_eq] using hEq
  rw [sumRange_localDelta_seg hw_ok hw x n] at hsum0
  omega

/-- Meta-Theorem 1 (Exact Infinite-Length Periodic Conservation Law):
    `checkConservation cert = true` proves `Φ(T^t(x)) = Φ(x)` for ALL `w ≥ 1`,
    ALL `x : BitVec w`, and ALL `t : Nat`. -/
theorem soundness_conservation_step (cert : CACert)
    (hcert : checkConservation cert = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) =
    ringPotential cert.p cert.phi x := by
  simp only [checkConservation, Bool.and_eq_true] at hcert
  rcases hcert with ⟨hw_ok, hall⟩
  rw [checkAll_true_iff] at hall
  have hsum0 : sumRange w (fun i => localDelta cert (window cert.M x i)) = 0 := by
    apply sumRange_zero_of_eq
    intro i _
    have hEq := hall (window cert.M x i) (window_lt cert.M x i)
    simpa [beq_iff_eq] using hEq
  rw [sumRange_localDelta_ring hw_ok hw x] at hsum0
  omega

theorem soundness_conservation (cert : CACert)
    (hcert : checkConservation cert = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential cert.p cert.phi (caIter cert.k cert.off cert.rule t x) =
    ringPotential cert.p cert.phi x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [caIter_succ, soundness_conservation_step cert hcert hw, ih]

/-- Meta-Theorem 2 (Pure Torsion Z/dZ Modular Conservation Law):
    `checkModConservation cert d = true` proves `Φ(T^t(x)) % d = Φ(x) % d` for ALL `w ≥ 1`,
    ALL `x : BitVec w`, and ALL `t : Nat`. -/
theorem soundness_modConservation_step (cert : CACert) (d : Nat)
    (hcert : checkModConservation cert d = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) % (d : Int) =
    ringPotential cert.p cert.phi x % (d : Int) := by
  simp only [checkModConservation, Bool.and_eq_true, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨hw_ok, _hd⟩, hall⟩
  rw [checkAll_true_iff] at hall
  have hdvd : sumRange w (fun i => localDelta cert (window cert.M x i)) % (d : Int) = 0 := by
    apply sumRange_dvd
    intro i _
    have hEq := hall (window cert.M x i) (window_lt cert.M x i)
    simpa [beq_iff_eq] using hEq
  rw [sumRange_localDelta_ring hw_ok hw x] at hdvd
  have hsub : ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) =
      ringPotential cert.p cert.phi x +
      (ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) -
       ringPotential cert.p cert.phi x) := by omega
  conv => lhs; rw [hsub, Int.add_emod, hdvd]
  simp

theorem soundness_modConservation (cert : CACert) (d : Nat)
    (hcert : checkModConservation cert d = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential cert.p cert.phi (caIter cert.k cert.off cert.rule t x) % (d : Int) =
    ringPotential cert.p cert.phi x % (d : Int) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [caIter_succ, soundness_modConservation_step cert d hcert hw, ih]

/-- Meta-Theorem 3 (Monotonic Lyapunov Potential Law):
    `checkLyapunov cert = true` proves `Φ(T(x)) ≤ Φ(x)` for ALL `w ≥ 1`, `x : BitVec w`. -/
theorem soundness_lyapunov_step (cert : CACert)
    (hcert : checkLyapunov cert = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) ≤
    ringPotential cert.p cert.phi x := by
  simp only [checkLyapunov, Bool.and_eq_true] at hcert
  rcases hcert with ⟨hw_ok, hall⟩
  rw [checkAll_true_iff] at hall
  have hle : sumRange w (fun i => localDelta cert (window cert.M x i)) ≤ 0 := by
    have h0 := sumRange_le w (f := fun i => localDelta cert (window cert.M x i)) (g := fun _ => 0)
      (fun i _ => by
        have h := hall (window cert.M x i) (window_lt cert.M x i)
        simpa [decide_eq_true_eq] using h)
    simpa [sumRange_const] using h0
  rw [sumRange_localDelta_ring hw_ok hw x] at hle
  omega

/-- Helper: `shiftHammingDist` as an integer sum is non-negative and equals `0` iff `shiftEq`. -/
theorem shiftHammingSum_nonneg (off cmp : Nat) {w : Nat} (y x : BitVec w) :
    0 ≤ sumRange w (fun i => if ringBit y (i + off) != ringBit x (i + cmp) then (1 : Int) else 0) := by
  have h := sumRange_le w (f := fun _ => (0 : Int))
    (g := fun i => if ringBit y (i + off) != ringBit x (i + cmp) then (1 : Int) else 0)
    (fun i _ => by split <;> omega)
  simpa [sumRange_const] using h

theorem shiftHammingDist_cast (off cmp : Nat) {w : Nat} (y x : BitVec w) :
    (shiftHammingDist off cmp y x : Int) =
    sumRange w (fun i => if ringBit y (i + off) != ringBit x (i + cmp) then (1 : Int) else 0) := by
  simp only [shiftHammingDist]
  exact Int.toNat_of_nonneg (shiftHammingSum_nonneg off cmp y x)

theorem sumRange_nonneg_eq_zero_iff (n : Nat) (f : Nat → Int)
    (hnn : ∀ i, i < n → 0 ≤ f i) :
    sumRange n f = 0 ↔ ∀ i, i < n → f i = 0 := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange]
    have hsn : 0 ≤ sumRange n f := by
      have h := sumRange_le n (f := fun _ => (0 : Int)) (g := f) (fun i hi => hnn i (by omega))
      simpa [sumRange_const] using h
    have hn := hnn n (by omega)
    constructor
    · intro h i hi
      have h1 : sumRange n f = 0 := by omega
      have h2 : f n = 0 := by omega
      by_cases hEq : i = n
      · subst hEq; exact h2
      · exact (ih (fun j hj => hnn j (by omega))).mp h1 i (by omega)
    · intro h
      have h1 := (ih (fun j hj => hnn j (by omega))).mpr (fun j hj => h j (by omega))
      have h2 := h n (by omega)
      omega

theorem shiftHammingDist_eq_zero_iff {w : Nat} (hw : 0 < w) (off cmp : Nat) (y x : BitVec w) :
    shiftHammingDist off cmp y x = 0 ↔ shiftEq off cmp y x := by
  have hcast := shiftHammingDist_cast off cmp y x
  constructor
  · intro h0
    have hs0 : sumRange w (fun i =>
        if ringBit y (i + off) != ringBit x (i + cmp) then (1 : Int) else 0) = 0 := by
      omega
    rw [sumRange_nonneg_eq_zero_iff w _ (fun i _ => by split <;> omega)] at hs0
    apply ringBit_eq_imp_eq
    intro i hi
    rw [ringBit_ringRot hw, ringBit_ringRot hw]
    have hi0 := hs0 i hi
    by_cases hneq : (ringBit y (i + off) != ringBit x (i + cmp)) = true
    · simp [hneq] at hi0
    · simpa [bne_eq_false_iff_eq] using hneq
  · intro heq
    have hs0 : sumRange w (fun i =>
        if ringBit y (i + off) != ringBit x (i + cmp) then (1 : Int) else 0) = 0 := by
      apply sumRange_zero_of_eq
      intro i _hi
      have hb : ringBit (ringRot off y) i = ringBit (ringRot cmp x) i := by rw [heq]
      rw [ringBit_ringRot hw, ringBit_ringRot hw] at hb
      simp [hb]
    omega

/-- Meta-Theorem 4a (Exact Strict Hamming-Dissipation Inequality):
    `checkStrictLyapunov cert cmp c = true` proves
    `Φ(x) - Φ(T(x)) ≥ c * d_H(rot_off(T(x)), rot_cmp(x))` for ALL `w ≥ 1`, `x : BitVec w`. -/
theorem soundness_strictLyapunov_dissipation (cert : CACert) (cmp c : Nat)
    (hcert : checkStrictLyapunov cert cmp c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ringPotential cert.p cert.phi x -
    ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) ≥
    (c : Int) * (shiftHammingDist cert.off cmp (caStep cert.k cert.off cert.rule x) x : Int) := by
  simp only [checkStrictLyapunov, Bool.and_eq_true, decide_eq_true_eq] at hcert
  rcases hcert with ⟨⟨⟨hw_ok, hcmp⟩, _hc⟩, hall⟩
  rw [checkAll_true_iff] at hall
  rcases widths_of_checkWidths hw_ok with ⟨_, _, _, _, _, _, hkM⟩
  have hsum_le :
      sumRange w (fun i =>
        if ringBit (caStep cert.k cert.off cert.rule x) (i + cert.off) != ringBit x (i + cmp)
        then (c : Int) else 0) ≤
      sumRange w (fun i => -localDelta cert (window cert.M x i)) := by
    apply sumRange_le
    intro i _
    have hu := hall (window cert.M x i) (window_lt cert.M x i)
    simp only [decide_eq_true_eq] at hu
    have hk0 : 0 + cert.k ≤ cert.M := by omega
    have hsw : subWin (window cert.M x i) 0 cert.k = window cert.k x i := by
      simpa using subWin_window hk0 x i
    have htb : (window cert.M x i).testBit cmp = ringBit x (i + cmp) :=
      testBit_window hcmp x i
    have hstep : cert.rule.testBit (window cert.k x i) =
        ringBit (caStep cert.k cert.off cert.rule x) (i + cert.off) :=
      (ringBit_caStep cert.k cert.off cert.rule hw x i).symm
    rw [hsw, htb, hstep] at hu
    exact hu
  have hlhs : sumRange w (fun i =>
      if ringBit (caStep cert.k cert.off cert.rule x) (i + cert.off) != ringBit x (i + cmp)
      then (c : Int) else 0) =
      (c : Int) * (shiftHammingDist cert.off cmp (caStep cert.k cert.off cert.rule x) x : Int) := by
    rw [shiftHammingDist_cast, ← sumRange_mul_left]
    apply sumRange_congr
    intro i _
    split <;> simp
  have hrhs : sumRange w (fun i => -localDelta cert (window cert.M x i)) =
      ringPotential cert.p cert.phi x -
      ringPotential cert.p cert.phi (caStep cert.k cert.off cert.rule x) := by
    have hneg : sumRange w (fun i => -localDelta cert (window cert.M x i)) =
        -(sumRange w (fun i => localDelta cert (window cert.M x i))) := by
      have h1 := sumRange_mul_left w (-1) (fun i => localDelta cert (window cert.M x i))
      have h2 : (fun i => (-1 : Int) * localDelta cert (window cert.M x i)) =
          (fun i => -localDelta cert (window cert.M x i)) := by
        funext i; omega
      rw [h2] at h1; omega
    rw [hneg, sumRange_localDelta_ring hw_ok hw x]
    omega
  rw [hlhs, hrhs] at hsum_le
  omega

/-- Bounds on `ringPotential`: `w * min(φ) ≤ Φ(x) ≤ w * max(φ)`. -/
theorem ringPotential_bounds (cert : CACert) {w : Nat} (x : BitVec w) :
    (w : Int) * rangeMin (2 ^ cert.p) (tableAt cert.phi) ≤ ringPotential cert.p cert.phi x ∧
    ringPotential cert.p cert.phi x ≤ (w : Int) * rangeMax (2 ^ cert.p) (tableAt cert.phi) := by
  constructor
  · rw [← sumRange_const]
    exact sumRange_le w (fun i _ => rangeMin_le _ _ (window_lt cert.p x i))
  · rw [← sumRange_const]
    exact sumRange_le w (fun i _ => le_rangeMax _ _ (window_lt cert.p x i))

theorem ringPotential_diff_le_spread (cert : CACert) {w : Nat} (x y : BitVec w) :
    ringPotential cert.p cert.phi x - ringPotential cert.p cert.phi y ≤
    ((phiSpread cert * w : Nat) : Int) := by
  have hx := (ringPotential_bounds cert x).2
  have hy := (ringPotential_bounds cert y).1
  have hnn : 0 ≤ rangeMax (2 ^ cert.p) (tableAt cert.phi) -
                 rangeMin (2 ^ cert.p) (tableAt cert.phi) := by
    have h0 := rangeMin_le (2 ^ cert.p) (tableAt cert.phi) (Nat.two_pow_pos cert.p)
    have h1 := le_rangeMax (2 ^ cert.p) (tableAt cert.phi) (Nat.two_pow_pos cert.p)
    omega
  have hsp : (phiSpread cert : Int) =
      rangeMax (2 ^ cert.p) (tableAt cert.phi) - rangeMin (2 ^ cert.p) (tableAt cert.phi) :=
    Int.toNat_of_nonneg hnn
  have hmul : ((phiSpread cert * w : Nat) : Int) =
      (w : Int) * rangeMax (2 ^ cert.p) (tableAt cert.phi) -
      (w : Int) * rangeMin (2 ^ cert.p) (tableAt cert.phi) := by
    rw [Int.natCast_mul, hsp, Int.mul_comm, Int.mul_sub]
  omega

/-- Meta-Theorem 4b (Cumulative Trajectory Activity Bound):
    Total shifted Hamming activity over ANY `N` steps is bounded by `spread * w / c`. -/
theorem soundness_strictLyapunov_activity (cert : CACert) (cmp c : Nat)
    (hcert : checkStrictLyapunov cert cmp c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (N : Nat) :
    (c : Int) * sumRange N (fun t =>
      (shiftHammingDist cert.off cmp
        (caIter cert.k cert.off cert.rule (t + 1) x)
        (caIter cert.k cert.off cert.rule t x) : Int)) ≤
    ringPotential cert.p cert.phi x -
    ringPotential cert.p cert.phi (caIter cert.k cert.off cert.rule N x) := by
  induction N with
  | zero => simp [sumRange, caIter]
  | succ N ih =>
    simp only [sumRange]
    rw [Int.mul_add]
    have hstep := soundness_strictLyapunov_dissipation cert cmp c hcert hw
      (caIter cert.k cert.off cert.rule N x)
    rw [caIter_succ]
    omega

/-- Once a configuration reaches the traveling-wave attractor `shiftEq off cmp (T y) y`,
    it remains locked on the attractor for all subsequent steps! -/
theorem shiftEq_preserved (k off rule cmp : Nat) {w : Nat} (hw : 0 < w)
    (y : BitVec w) (h : shiftEq off cmp (caStep k off rule y) y) :
    shiftEq off cmp (caStep k off rule (caStep k off rule y)) (caStep k off rule y) := by
  simp only [shiftEq] at h ⊢
  rw [← caStep_ringRot k off rule off hw, h, caStep_ringRot k off rule cmp hw]

theorem shiftEq_preserved_iter (k off rule cmp : Nat) {w : Nat} (hw : 0 < w)
    (y : BitVec w) (h : shiftEq off cmp (caStep k off rule y) y) (d : Nat) :
    shiftEq off cmp (caStep k off rule (caIter k off rule d y)) (caIter k off rule d y) := by
  induction d with
  | zero => exact h
  | succ d ih =>
    rw [caIter_succ]
    exact shiftEq_preserved k off rule cmp hw _ ih

/-- Meta-Theorem 4c (Universal Linear-Time Convergence to Traveling-Wave / Fixed-Point Attractor):
    Constructive proof (ZERO `Classical.choice`!): for ALL `w ≥ 1` and ALL `x : BitVec w`,
    letting `N = (phiSpread cert * w) / c`, `T^N(x)` satisfies `shiftEq off cmp (T (T^N x)) (T^N x)`! -/
theorem soundness_strictLyapunov_convergence (cert : CACert) (cmp c : Nat)
    (hcert : checkStrictLyapunov cert cmp c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let y := caIter cert.k cert.off cert.rule (maxTransient cert c w) x
    shiftEq cert.off cmp (caStep cert.k cert.off cert.rule y) y := by
  have hc_pos : 1 ≤ c := by
    simp only [checkStrictLyapunov, Bool.and_eq_true, decide_eq_true_eq] at hcert
    omega
  let N := maxTransient cert c w
  let act := fun t => shiftHammingDist cert.off cmp
      (caIter cert.k cert.off cert.rule (t + 1) x)
      (caIter cert.k cert.off cert.rule t x)
  have hact : (c : Int) * sumRange (N + 1) (fun t => (act t : Int)) ≤
      ringPotential cert.p cert.phi x -
      ringPotential cert.p cert.phi (caIter cert.k cert.off cert.rule (N + 1) x) :=
    soundness_strictLyapunov_activity cert cmp c hcert hw x (N + 1)
  have hsp := ringPotential_diff_le_spread cert x (caIter cert.k cert.off cert.rule (N + 1) x)
  have hsum_nn : 0 ≤ sumRange (N + 1) (fun t => (act t : Int)) := by
    have h := sumRange_le (N + 1) (f := fun _ => (0 : Int)) (g := fun t => (act t : Int))
      (fun _ _ => Int.natCast_nonneg _)
    simpa [sumRange_const] using h
  have hdiv : phiSpread cert * w < c * (N + 1) := by
    have hdm := Nat.div_add_mod (phiSpread cert * w) c
    have hmod := Nat.mod_lt (phiSpread cert * w) (by omega : 0 < c)
    have hN : N = (phiSpread cert * w) / c := rfl
    rw [hN, Nat.mul_add, Nat.mul_one]
    omega
  have hlt : sumRange (N + 1) (fun t => (act t : Int)) < ((N + 1 : Nat) : Int) := by
    -- If sum ≥ N + 1, then c * (N + 1) ≤ c * sum ≤ spread * w, contradicting hdiv!
    by_cases hge : ((N + 1 : Nat) : Int) ≤ sumRange (N + 1) (fun t => (act t : Int))
    · have hmul : (c : Int) * ((N + 1 : Nat) : Int) ≤
          (c : Int) * sumRange (N + 1) (fun t => (act t : Int)) :=
        Int.mul_le_mul_of_nonneg_left hge (by omega)
      have hbound_int : ((c * (N + 1) : Nat) : Int) ≤ ((phiSpread cert * w : Nat) : Int) := by
        rw [Int.natCast_mul]; omega
      have hbound_nat : c * (N + 1) ≤ phiSpread cert * w := Int.ofNat_le.mp hbound_int
      omega
    · omega
  rcases exists_zero_of_sum_lt (N + 1) act hlt with ⟨t, ht, hz⟩
  have hz' : shiftEq cert.off cmp
      (caStep cert.k cert.off cert.rule (caIter cert.k cert.off cert.rule t x))
      (caIter cert.k cert.off cert.rule t x) := by
    exact (shiftHammingDist_eq_zero_iff hw _ _ _ _).mp hz
  have hN : N = t + (N - t) := by omega
  change shiftEq cert.off cmp
    (caStep cert.k cert.off cert.rule (caIter cert.k cert.off cert.rule N x))
    (caIter cert.k cert.off cert.rule N x)
  rw [hN, caIter_add]
  exact shiftEq_preserved_iter cert.k cert.off cert.rule cmp hw _ hz' (N - t)

/-- Meta-Theorem 4d (Exact Fixed-Point Termination when `cmp = off`):
    For ALL `w ≥ 1` and ALL `x : BitVec w`, `T(T^{N_max(w)}(x)) = T^{N_max(w)}(x)`. -/
theorem soundness_fixedPoint_termination (cert : CACert) (c : Nat)
    (hcert : checkStrictLyapunov cert cert.off c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let y := caIter cert.k cert.off cert.rule (maxTransient cert c w) x
    caStep cert.k cert.off cert.rule y = y := by
  have h := soundness_strictLyapunov_convergence cert cert.off c hcert hw x
  exact (shiftEq_self_iff hw cert.off _ _).mp h

/-- Meta-Theorem 4e (Global Acyclicity — Zero Cycles of Any Period `P ≥ 2`):
    If `checkStrictLyapunov cert cert.off c = true`, then for ALL `w ≥ 1`, `x : BitVec w`,
    and `P ≥ 1`, `T^P(x) = x → T(x) = x`. -/
theorem soundness_global_acyclicity (cert : CACert) (c : Nat)
    (hcert : checkStrictLyapunov cert cert.off c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (P : Nat) (hP : 1 ≤ P)
    (hcyc : caIter cert.k cert.off cert.rule P x = x) :
    caStep cert.k cert.off cert.rule x = x := by
  have hc_pos : 1 ≤ c := by
    simp only [checkStrictLyapunov, Bool.and_eq_true, decide_eq_true_eq] at hcert
    omega
  let act := fun t => shiftHammingDist cert.off cert.off
      (caIter cert.k cert.off cert.rule (t + 1) x)
      (caIter cert.k cert.off cert.rule t x)
  have hact : (c : Int) * sumRange P (fun t => (act t : Int)) ≤
      ringPotential cert.p cert.phi x -
      ringPotential cert.p cert.phi (caIter cert.k cert.off cert.rule P x) :=
    soundness_strictLyapunov_activity cert cert.off c hcert hw x P
  rw [hcyc] at hact
  have hnn : 0 ≤ sumRange P (fun t => (act t : Int)) := by
    have h := sumRange_le P (f := fun _ => (0 : Int)) (g := fun t => (act t : Int))
      (fun _ _ => Int.natCast_nonneg _)
    simpa [sumRange_const] using h
  have hle0 : (c : Int) * sumRange P (fun t => (act t : Int)) ≤ 0 := by omega
  have hsum0 : sumRange P (fun t => (act t : Int)) = 0 := by
    by_cases hpos : 1 ≤ sumRange P (fun t => (act t : Int))
    · have hm : (c : Int) * 1 ≤ (c : Int) * sumRange P (fun t => (act t : Int)) :=
        Int.mul_le_mul_of_nonneg_left hpos (by omega)
      omega
    · omega
  rw [sumRange_nonneg_eq_zero_iff P _ (fun _ _ => Int.natCast_nonneg _)] at hsum0
  have h0 := hsum0 0 (by omega)
  have h0nat : shiftHammingDist cert.off cert.off (caStep cert.k cert.off cert.rule x) x = 0 := by
    simpa [act, caIter] using Int.ofNat.inj h0
  exact (shiftEq_self_iff hw cert.off _ _).mp ((shiftHammingDist_eq_zero_iff hw _ _ _ _).mp h0nat)

/-- Meta-Theorem 4f (Exact Left-Moving Traveling-Wave Locking when `cmp = off + s`): -/
theorem soundness_travelingWave_locking (cert : CACert) (s c : Nat)
    (hcert : checkStrictLyapunov cert (cert.off + s) c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let y := caIter cert.k cert.off cert.rule (maxTransient cert c w) x
    caStep cert.k cert.off cert.rule y = ringRot s y := by
  have h := soundness_strictLyapunov_convergence cert (cert.off + s) c hcert hw x
  exact (shiftEq_rotL_iff hw cert.off s _ _).mp h

/-- Meta-Theorem 5 (2-Step Period-2 Blinker Convergence & Zero Cycles of Period ≥ 3):
    If the compiled `k=5` 2-step rule `compose2Rule rule` passes `checkStrictLyapunov`
    with `cmp = 2`, then the original `k=3` CA rule converges in `≤ 2 * N_max(w)` steps
    to a fixed point or period-2 blinker, has ZERO cycles of even period ≥ 4 (any
    `T^{2P}(x) = x` implies `T^2(x) = x`), and ZERO non-trivial odd cycles (`T^{2m+1}(x) = x → T(x) = x`)! -/
theorem soundness_blinker_convergence (rule : Nat) (cert : CACert) (c : Nat)
    (hk : cert.k = 5) (hoff : cert.off = 2) (hrule : cert.rule = compose2Rule rule)
    (hcert : checkStrictLyapunov cert 2 c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let y := caIter 3 1 rule (2 * maxTransient cert c w) x
    caStep 3 1 rule (caStep 3 1 rule y) = y := by
  have hfp := soundness_fixedPoint_termination cert c (hoff ▸ hcert) hw x
  dsimp only at hfp
  rw [hk, hoff, hrule] at hfp
  rw [caStep_compose2 rule hw, caIter_compose2 rule _ hw] at hfp
  exact hfp

theorem soundness_no_even_period_ge4 (rule : Nat) (cert : CACert) (c : Nat)
    (hk : cert.k = 5) (hoff : cert.off = 2) (hrule : cert.rule = compose2Rule rule)
    (hcert : checkStrictLyapunov cert 2 c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (P : Nat) (hP : 1 ≤ P)
    (hcyc : caIter 3 1 rule (2 * P) x = x) :
    caStep 3 1 rule (caStep 3 1 rule x) = x := by
  have hacyc := soundness_global_acyclicity cert c (hoff ▸ hcert) hw x P hP
  rw [hk, hoff, hrule] at hacyc
  rw [caIter_compose2 rule P hw] at hacyc
  have h := hacyc hcyc
  rwa [caStep_compose2 rule hw] at h

theorem soundness_no_odd_cycles (rule : Nat) (cert : CACert) (c : Nat)
    (hk : cert.k = 5) (hoff : cert.off = 2) (hrule : cert.rule = compose2Rule rule)
    (hcert : checkStrictLyapunov cert 2 c = true)
    {w : Nat} (hw : 0 < w) (x : BitVec w) (m : Nat)
    (hcyc : caIter 3 1 rule (2 * m + 1) x = x) :
    caStep 3 1 rule x = x := by
  have h2cyc : caIter 3 1 rule (2 * (2 * m + 1)) x = x := by
    have hsplit : 2 * (2 * m + 1) = (2 * m + 1) + (2 * m + 1) := by omega
    rw [hsplit, caIter_add, hcyc, hcyc]
  have hT2 : caStep 3 1 rule (caStep 3 1 rule x) = x :=
    soundness_no_even_period_ge4 rule cert c hk hoff hrule hcert hw x (2 * m + 1) (by omega) h2cyc
  have hT2m : ∀ k, caIter 3 1 rule (2 * k) x = x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [h2, caIter_succ, caIter_succ, ih, hT2]
  rw [caIter_succ, hT2m m] at hcyc
  exact hcyc

-- ============================================================================
-- Section 6: Six Novel Infinite Binary Theorems Discharged via Kernel `decide`
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Theorem 1a: Higher-Order Non-Number-Conserving 3-Bit `101`-Motif Invariant
--             on Nonlinear k=4 CA `rule = 0xac8c` (44172)
-- ----------------------------------------------------------------------------

theorem cert_pat101_0xac8c_valid : checkConservation cert_pat101_0xac8c = true := by
  decide

/-- Infinite Theorem 1a: For EVERY ring width `w ≥ 1`, EVERY `x : BitVec w`, and EVERY `t : Nat`,
    nonlinear `k=4` CA `0xac8c` conserves the exact count of `101` 3-bit motifs! -/
theorem thm_pat101_conservation_0xac8c {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 3 cert_pat101_0xac8c.phi (caIter 4 1 0xac8c t x) =
    ringPotential 3 cert_pat101_0xac8c.phi x :=
  soundness_conservation cert_pat101_0xac8c cert_pat101_0xac8c_valid hw x t

-- ----------------------------------------------------------------------------
-- Theorem 1b: Domain-Wall `01+10` Exact Conservation + Open-Segment Flux Balance
--             on Nonlinear k=4 CA `rule = 0x04ce` (1230)
-- ----------------------------------------------------------------------------

theorem cert_walls_0x04ce_valid : checkConservation cert_walls_0x04ce = true := by
  decide

/-- Infinite Theorem 1b: Exact domain-wall (`01 + 10`) conservation on `k=4` CA `0x04ce`
    for ALL `w ≥ 1`, `x : BitVec w`, `t : Nat`. -/
theorem thm_walls_conservation_0x04ce {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 2 cert_walls_0x04ce.phi (caIter 4 1 0x04ce t x) =
    ringPotential 2 cert_walls_0x04ce.phi x :=
  soundness_conservation cert_walls_0x04ce cert_walls_0x04ce_valid hw x t

/-- Infinite Theorem 1c: Exact Discrete Gauss / Open-Segment Continuity Equation on `0x04ce`. -/
theorem thm_openSegment_flux_balance_0x04ce {w : Nat} (hw : 0 < w) (x : BitVec w) (n : Nat) :
    segPotential 2 cert_walls_0x04ce.phi (caStep 4 1 0x04ce x) 1 n -
    segPotential 2 cert_walls_0x04ce.phi x 1 n =
    tableAt cert_walls_0x04ce.psi (window 4 x 0) -
    tableAt cert_walls_0x04ce.psi (window 4 x n) :=
  soundness_openSegment_balance cert_walls_0x04ce cert_walls_0x04ce_valid hw x n

-- ----------------------------------------------------------------------------
-- Theorem 2: Flux-Mediated Strict Fixed-Point Termination & Global Acyclicity
--            on Nonlinear Non-Monotone k=4 CA `rule = 0x2c48` (11336)
-- ----------------------------------------------------------------------------

theorem cert_strict_fp_0x2c48_valid :
    checkStrictLyapunov cert_strict_fp_0x2c48 1 1 = true := by
  decide

theorem cert_strict_fp_0x2c48_spread : phiSpread cert_strict_fp_0x2c48 = 4 := by
  decide

/-- Infinite Theorem 2a: Nonlinear non-monotone `k=4` CA `0x2c48` terminates at an
    exact fixed point in at most `4 * w` steps on EVERY ring `w ≥ 1`! -/
theorem thm_strict_fp_termination_0x2c48 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep 4 1 0x2c48 (caIter 4 1 0x2c48 (4 * w) x) = caIter 4 1 0x2c48 (4 * w) x := by
  have h := soundness_fixedPoint_termination cert_strict_fp_0x2c48 1
    cert_strict_fp_0x2c48_valid hw x
  dsimp only at h
  have hmt : maxTransient cert_strict_fp_0x2c48 1 w = 4 * w := by
    simp [maxTransient, cert_strict_fp_0x2c48_spread]
  rw [hmt] at h
  exact h

/-- Infinite Theorem 2b: Global acyclicity of `0x2c48` — ZERO periodic orbits of
    period `P ≥ 2` exist on ANY bitring of ANY length `w ≥ 1`! -/
theorem thm_global_acyclicity_0x2c48 {w : Nat} (hw : 0 < w) (x : BitVec w)
    (P : Nat) (hP : 1 ≤ P) (hcyc : caIter 4 1 0x2c48 P x = x) :
    caStep 4 1 0x2c48 x = x :=
  soundness_global_acyclicity cert_strict_fp_0x2c48 1 cert_strict_fp_0x2c48_valid hw x P hP hcyc

-- ----------------------------------------------------------------------------
-- Theorem 3: Shift-Velocity Traveling-Wave Locking on Non-Monotone Rule 152 (0x98)
-- ----------------------------------------------------------------------------

theorem cert_tw_rule152_valid : checkStrictLyapunov cert_tw_rule152 2 1 = true := by
  decide

theorem cert_tw_rule152_spread : phiSpread cert_tw_rule152 = 3 := by
  decide

/-- Infinite Theorem 3: Every configuration on EVERY ring `w ≥ 1` under Rule 152 locks
    into a rigid velocity-1 left-moving traveling wave `T(y) = ringRot 1 y` in `≤ 3 * w` steps! -/
theorem thm_travelingWave_locking_rule152 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep 3 1 152 (caIter 3 1 152 (3 * w) x) = ringRot 1 (caIter 3 1 152 (3 * w) x) := by
  have h := soundness_travelingWave_locking cert_tw_rule152 1 1 cert_tw_rule152_valid hw x
  dsimp only at h
  have hmt : maxTransient cert_tw_rule152 1 w = 3 * w := by
    simp [maxTransient, cert_tw_rule152_spread]
  rw [hmt] at h
  exact h

-- ----------------------------------------------------------------------------
-- Theorem 4: Microcanonical Coupled Conservative-Dissipative k=4 CA `0xf0e0` (61664)
--            Simultaneous Exact Domino-`11` Conservation + Velocity-1 Wave Locking
-- ----------------------------------------------------------------------------

theorem cert_micro_cons_0xf0e0_valid : checkConservation cert_micro_cons_0xf0e0 = true := by
  decide

theorem cert_micro_lyap_0xf0e0_valid : checkStrictLyapunov cert_micro_lyap_0xf0e0 2 1 = true := by
  decide

theorem cert_micro_lyap_0xf0e0_spread : phiSpread cert_micro_lyap_0xf0e0 = 1 := by
  decide

/-- Infinite Theorem 4 (Microcanonical Equilibrium Law on `k=4` CA `0xf0e0`):
    For EVERY `w ≥ 1` and EVERY `x : BitVec w`, let `x* = T^w(x)`. Then SIMULTANEOUSLY:
      (1) `x*` is a rigid velocity-1 traveling wave: `T(x*) = ringRot 1 x*`, AND
      (2) `x*` preserves the EXACT initial count of `11` dominoes: `#11(x*) = #11(x)`! -/
theorem thm_microcanonical_0xf0e0 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let xStar := caIter 4 1 0xf0e0 w x
    caStep 4 1 0xf0e0 xStar = ringRot 1 xStar ∧
    ringPotential 2 cert_micro_cons_0xf0e0.phi xStar =
    ringPotential 2 cert_micro_cons_0xf0e0.phi x := by
  constructor
  · have h := soundness_travelingWave_locking cert_micro_lyap_0xf0e0 1 1
      cert_micro_lyap_0xf0e0_valid hw x
    dsimp only at h
    have hmt : maxTransient cert_micro_lyap_0xf0e0 1 w = w := by
      simp [maxTransient, cert_micro_lyap_0xf0e0_spread]
    rw [hmt] at h
    exact h
  · exact soundness_conservation cert_micro_cons_0xf0e0 cert_micro_cons_0xf0e0_valid hw x w

-- ----------------------------------------------------------------------------
-- Theorem 5: 2-Step Period-2 Blinker Convergence & Absence of Cycles of Period ≥ 3
--            on ECA Rule 108 (via Compiled k=5 Rule `compose2Rule 108 = 0x309050f0`)
-- ----------------------------------------------------------------------------

theorem cert_blinker_rule108_rule_val : compose2Rule 108 = 0x309050f0 := by
  decide

theorem cert_blinker_rule108_valid : checkStrictLyapunov cert_blinker_rule108 2 1 = true := by
  decide

theorem cert_blinker_rule108_spread : phiSpread cert_blinker_rule108 = 1 := by
  decide

/-- Infinite Theorem 5a: On EVERY bitring `w ≥ 1`, ECA Rule 108 converges in at most `2 * w`
    steps to an exact fixed point or period-2 blinker `T^2(y) = y`. -/
theorem thm_blinker_convergence_rule108 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let y := caIter 3 1 108 (2 * w) x
    caStep 3 1 108 (caStep 3 1 108 y) = y := by
  have h := soundness_blinker_convergence 108 cert_blinker_rule108 1
    rfl rfl rfl cert_blinker_rule108_valid hw x
  dsimp only at h
  have hmt : maxTransient cert_blinker_rule108 1 w = w := by
    simp [maxTransient, cert_blinker_rule108_spread]
  rw [hmt] at h
  exact h

/-- Infinite Theorem 5b: ECA Rule 108 has ZERO non-trivial odd cycles on ANY ring `w ≥ 1`! -/
theorem thm_no_odd_cycles_rule108 {w : Nat} (hw : 0 < w) (x : BitVec w) (m : Nat)
    (hcyc : caIter 3 1 108 (2 * m + 1) x = x) :
    caStep 3 1 108 x = x :=
  soundness_no_odd_cycles 108 cert_blinker_rule108 1 rfl rfl rfl cert_blinker_rule108_valid hw x m hcyc

/-- Infinite Theorem 5c: ECA Rule 108 has ZERO cycles of even period ≥ 4 on ANY ring `w ≥ 1`! -/
theorem thm_no_even_period_ge4_rule108 {w : Nat} (hw : 0 < w) (x : BitVec w)
    (P : Nat) (hP : 1 ≤ P) (hcyc : caIter 3 1 108 (2 * P) x = x) :
    caStep 3 1 108 (caStep 3 1 108 x) = x :=
  soundness_no_even_period_ge4 108 cert_blinker_rule108 1 rfl rfl rfl cert_blinker_rule108_valid hw x P hP hcyc

-- ----------------------------------------------------------------------------
-- Theorem 6a: Pure Z/3Z Torsion Conservation on Nonlinear k=4 CA `0xb0f0` (45296)
--             (Conserves `#1 + #11 (mod 3)`, ZERO integer lift!)
-- ----------------------------------------------------------------------------

theorem cert_mod3_0xb0f0_valid : checkModConservation cert_mod3_0xb0f0 3 = true := by
  decide

/-- Infinite Theorem 6a: Nonlinear `k=4` CA `0xb0f0` conserves `#1(x) + #11(x) (mod 3)`
    for ALL `w ≥ 1`, `x : BitVec w`, `t : Nat` (while breaking conservation over `Z`!). -/
theorem thm_mod3_torsion_0xb0f0 {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 2 cert_mod3_0xb0f0.phi (caIter 4 1 0xb0f0 t x) % 3 =
    ringPotential 2 cert_mod3_0xb0f0.phi x % 3 :=
  soundness_modConservation cert_mod3_0xb0f0 3 cert_mod3_0xb0f0_valid hw x t

-- ----------------------------------------------------------------------------
-- Theorem 6b: Pure Z/2Z Parity Torsion Conservation on Nonlinear k=4 CA `0x83bc` (33724)
--             (Conserves `popcount(x) (mod 2)` with long period-3w cycles, NO integer lift!)
-- ----------------------------------------------------------------------------

theorem cert_mod2_0x83bc_valid : checkModConservation cert_mod2_0x83bc 2 = true := by
  decide

/-- Infinite Theorem 6b: Nonlinear `k=4` CA `0x83bc` conserves total bit-parity
    `popcount(T^t(x)) ≡ popcount(x) (mod 2)` for ALL `w ≥ 1`, `x : BitVec w`, `t : Nat`. -/
theorem thm_mod2_torsion_0x83bc {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 2 cert_mod2_0x83bc.phi (caIter 4 1 0x83bc t x) % 2 =
    ringPotential 2 cert_mod2_0x83bc.phi x % 2 :=
  soundness_modConservation cert_mod2_0x83bc 2 cert_mod2_0x83bc_valid hw x t

-- ============================================================================
-- Section 7: Kernel-Checked Non-Vacuity & Sharpness Witnesses
-- ============================================================================

/-- 7.1 Non-constancy of `cert_pat101_0xac8c` potential on `w = 6` + non-conservation of popcount. -/
example : ringPotential 3 cert_pat101_0xac8c.phi (0b000000#6) = 0 ∧
          ringPotential 3 cert_pat101_0xac8c.phi (0b101010#6) = 3 := by decide

example : ringPotential 1 [0, 1] (0b000011#6) = 2 ∧
          ringPotential 1 [0, 1] (caStep 4 1 0xac8c (0b000011#6)) = 1 := by decide

/-- 7.2 Non-constancy + non-number-conservation + open-segment boundary-flux witness on `0x04ce`:
    On open segment `[0, 3)` of `x = 0b000111#6`, the potential is NOT conserved because
    the boundary flux `ψ(W_4(x, 0)) - ψ(W_4(x, 3))` is non-zero! -/
example : ringPotential 2 cert_walls_0x04ce.phi (0b000000#6) = 0 ∧
          ringPotential 2 cert_walls_0x04ce.phi (0b101010#6) = 6 := by decide

example : ringPotential 1 [0, 1] (0b000001#6) = 1 ∧
          ringPotential 1 [0, 1] (caStep 4 1 0x04ce (0b000001#6)) = 2 := by decide

example : segPotential 2 cert_walls_0x04ce.phi (caStep 4 1 0x04ce (0b000001#6)) 1 3 = 1 ∧
          segPotential 2 cert_walls_0x04ce.phi (0b000001#6) 1 3 = 0 := by decide

/-- 7.3 Non-monotonicity of `0x2c48` (flips BOTH `0→1` and `1→0`) + multi-step transient witness:
    On `w = 6`, `x = 0b010111#6` is NOT yet fixed after 3 steps, and reaches a fixed point at step 4. -/
example : (0x2c48 : Nat).testBit 13 = true ∧ ((13 : Nat).testBit 1 = false) ∧
          (0x2c48 : Nat).testBit 2 = false ∧ ((2 : Nat).testBit 1 = true) := by decide

example : caStep 4 1 0x2c48 (caIter 4 1 0x2c48 3 (0b010111#6)) ≠ caIter 4 1 0x2c48 3 (0b010111#6) ∧
          caStep 4 1 0x2c48 (caIter 4 1 0x2c48 4 (0b010111#6)) = caIter 4 1 0x2c48 4 (0b010111#6) := by
  decide

/-- 7.4 Genuine moving traveling wave on Rule 152 (fixed-point convergence is FALSE!) +
    sharp `w - 1 = 5` transient witness on `w = 6` (`0b011111#6`). -/
example : caStep 3 1 152 (0b001001#6) ≠ (0b001001#6) ∧
          caStep 3 1 152 (0b001001#6) = ringRot 1 (0b001001#6) := by decide

example : caStep 3 1 152 (caIter 3 1 152 4 (0b011111#6)) ≠ ringRot 1 (caIter 3 1 152 4 (0b011111#6)) ∧
          caStep 3 1 152 (caIter 3 1 152 5 (0b011111#6)) = ringRot 1 (caIter 3 1 152 5 (0b011111#6)) := by
  decide

/-- 7.5 Genuine moving soliton + non-constant domino count on microcanonical `0xf0e0`. -/
example : caStep 4 1 0xf0e0 (0b001100#6) ≠ (0b001100#6) ∧
          caStep 4 1 0xf0e0 (0b001100#6) = ringRot 1 (0b001100#6) ∧
          ringPotential 2 cert_micro_cons_0xf0e0.phi (0b001100#6) = 1 ∧
          ringPotential 2 cert_micro_cons_0xf0e0.phi (0b000000#6) = 0 := by decide

/-- 7.6 Genuine period-2 blinker on ECA Rule 108 (proving 1-step fixed-point convergence is FALSE!). -/
example : caStep 3 1 108 (0b00101#5) ≠ (0b00101#5) ∧
          caStep 3 1 108 (caStep 3 1 108 (0b00101#5)) = (0b00101#5) := by decide

/-- 7.7 Pure torsion sharpness for `0xb0f0` (mod 3): integer conservation is FALSE (`5 → 2`,
    jump `-3`), AND all three residues `{0, 1, 2} (mod 3)` are realized on `w = 4`! -/
example : ringPotential 2 cert_mod3_0xb0f0.phi (0b0111#4) = 5 ∧
          ringPotential 2 cert_mod3_0xb0f0.phi (caStep 4 1 0xb0f0 (0b0111#4)) = 2 ∧
          ringPotential 2 cert_mod3_0xb0f0.phi (0b0000#4) % 3 = 0 ∧
          ringPotential 2 cert_mod3_0xb0f0.phi (0b0001#4) % 3 = 1 ∧
          ringPotential 2 cert_mod3_0xb0f0.phi (0b0111#4) % 3 = 2 := by decide

/-- 7.8 Pure torsion sharpness for `0x83bc` (mod 2): integer popcount is NOT conserved
    (`w = 5`, `0b01110#5` jumps in popcount by 2), while both parities `{0, 1}` are realized! -/
example : ringPotential 2 cert_mod2_0x83bc.phi (0b00001#5) = 1 ∧
          ringPotential 2 cert_mod2_0x83bc.phi (caStep 4 1 0x83bc (0b00001#5)) = 3 ∧
          ringPotential 2 cert_mod2_0x83bc.phi (0b00000#5) % 2 = 0 ∧
          ringPotential 2 cert_mod2_0x83bc.phi (0b00001#5) % 2 = 1 := by decide

-- ============================================================================
-- Section 8: Kernel-Checked Negative / Mutation Rejection Tests
-- ============================================================================

-- 8.1 Zero-flux ablations (proving flux `ψ` is strictly essential in every case!)
example : checkConservation { cert_pat101_0xac8c with psi := List.replicate 16 0 } = false := by decide
example : checkConservation { cert_walls_0x04ce with psi := List.replicate 16 0 } = false := by decide
example : checkStrictLyapunov { cert_strict_fp_0x2c48 with psi := List.replicate 8 0 } 1 1 = false := by decide
example : checkStrictLyapunov { cert_tw_rule152 with psi := [0, 0, 0, 0] } 2 1 = false := by decide
example : checkConservation { cert_micro_cons_0xf0e0 with psi := List.replicate 8 0 } = false := by decide
example : checkStrictLyapunov { cert_micro_lyap_0xf0e0 with psi := List.replicate 8 0 } 2 1 = false := by decide
example : checkModConservation { cert_mod3_0xb0f0 with psi := List.replicate 16 0 } 3 = false := by decide
example : checkModConservation { cert_mod2_0x83bc with psi := List.replicate 8 0 } 2 = false := by decide

-- 8.2 Single-entry flux mutations (`ψ[idx] + 1`)
example : checkConservation { cert_walls_0x04ce with
    psi := [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1] } = false := by decide
example : checkStrictLyapunov { cert_strict_fp_0x2c48 with
    psi := [0, 0, 0, 0, 0, 0, 0, 3] } 1 1 = false := by decide
example : checkModConservation { cert_mod3_0xb0f0 with
    psi := [0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 2, 2] } 3 = false := by decide

-- 8.3 Single-entry potential mutations (`φ[idx] + 1`)
example : checkConservation { cert_pat101_0xac8c with
    phi := [0, 0, 0, 0, 0, 2, 0, 0] } = false := by decide
example : checkStrictLyapunov { cert_strict_fp_0x2c48 with
    phi := [0, 3, 5, 3] } 1 1 = false := by decide
example : checkModConservation { cert_mod3_0xb0f0 with
    phi := [0, 1, 1, 2] } 3 = false := by decide

-- 8.4 Single-bit CA rule mutations (`rule ^^^ (1 <<< u)`)
example : checkConservation { cert_pat101_0xac8c with rule := 0xac8c ^^^ 1 } = false := by decide
example : checkConservation { cert_walls_0x04ce with rule := 0x04ce ^^^ 2 } = false := by decide
example : checkStrictLyapunov { cert_strict_fp_0x2c48 with rule := 0x2c48 ^^^ 1 } 1 1 = false := by decide
example : checkStrictLyapunov { cert_tw_rule152 with rule := 152 ^^^ 1 } 2 1 = false := by decide
example : checkModConservation { cert_mod3_0xb0f0 with rule := 0xb0f0 ^^^ 1 } 3 = false := by decide
example : checkModConservation { cert_mod2_0x83bc with rule := 0x83bc ^^^ 1 } 2 = false := by decide

-- 8.5 Over-tightened dissipation constant (`c = 2`), wrong velocity (`cmp`), wrong modulus (`d`),
--     and integer lift failure on torsion certificates
example : checkStrictLyapunov cert_strict_fp_0x2c48 1 2 = false := by decide
example : checkStrictLyapunov cert_tw_rule152 2 2 = false := by decide
example : checkStrictLyapunov cert_tw_rule152 1 1 = false := by decide
example : checkStrictLyapunov cert_micro_lyap_0xf0e0 2 2 = false := by decide
example : checkStrictLyapunov cert_micro_lyap_0xf0e0 1 1 = false := by decide
example : checkStrictLyapunov cert_blinker_rule108 2 2 = false := by decide
example : checkConservation cert_mod3_0xb0f0 = false := by decide
example : checkModConservation cert_mod3_0xb0f0 2 = false := by decide
example : checkConservation cert_mod2_0x83bc = false := by decide
example : checkModConservation cert_mod2_0x83bc 3 = false := by decide

end CAFluxCompiler
