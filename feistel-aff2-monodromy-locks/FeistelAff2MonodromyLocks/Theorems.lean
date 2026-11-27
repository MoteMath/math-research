/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FeistelAff2MonodromyLocks.Defs

/-!
# Theorems (`FeistelAff2MonodromyLocks`)

Bit-Slice Aff(F_2^2)-Monodromy Tower Engine for Bitwise-Arithmetic Feistel Networks
  Standalone Lean 4.34.1 (zero Mathlib, zero sorry, zero custom axioms)
-/


namespace FeistelMonodromy

/-! ## Part 1: Finite Affine Monodromy Group Aff(F_2^2) -/

/-- An element `(M, v)` of the affine group `Aff(F_2^2)` acting on `Bool × Bool`. -/
structure Aff2 where
  m00 : Bool
  m01 : Bool
  m10 : Bool
  m11 : Bool
  v0  : Bool
  v1  : Bool
  deriving DecidableEq, Repr

namespace Aff2

def id : Aff2 := ⟨true, false, false, true, false, false⟩

def apply (T : Aff2) (x : Bool × Bool) : Bool × Bool :=
  ((((T.m00 && x.1) ^^ (T.m01 && x.2)) ^^ T.v0),
   (((T.m10 && x.1) ^^ (T.m11 && x.2)) ^^ T.v1))

def comp (T2 T1 : Aff2) : Aff2 :=
  ⟨((T2.m00 && T1.m00) ^^ (T2.m01 && T1.m10)),
   ((T2.m00 && T1.m01) ^^ (T2.m01 && T1.m11)),
   ((T2.m10 && T1.m00) ^^ (T2.m11 && T1.m10)),
   ((T2.m10 && T1.m01) ^^ (T2.m11 && T1.m11)),
   (((T2.m00 && T1.v0) ^^ (T2.m01 && T1.v1)) ^^ T2.v0),
   (((T2.m10 && T1.v0) ^^ (T2.m11 && T1.v1)) ^^ T2.v1)⟩

def pow (T : Aff2) : Nat → Aff2
  | 0 => id
  | n + 1 => comp T (pow T n)

def det (T : Aff2) : Bool :=
  ((T.m00 && T.m11) ^^ (T.m01 && T.m10))

/-- Single-step Feistel bit-slice monodromy with local Jacobian bit `d` and carry/offset `c`.
    Maps `(a, b) ↦ (b, a ^^ (d && b) ^^ c)`. -/
def feistelStep (d c : Bool) : Aff2 :=
  ⟨false, true, true, d, false, c⟩

private theorem bool_aff_row (p0 p1 q00 q01 q10 q11 u0 u1 w a b : Bool) :
    (((((p0 && q00) ^^ (p1 && q10)) && a) ^^ (((p0 && q01) ^^ (p1 && q11)) && b)) ^^
      (((p0 && u0) ^^ (p1 && u1)) ^^ w)) =
    (((p0 && (((q00 && a) ^^ (q01 && b)) ^^ u0)) ^^
      (p1 && (((q10 && a) ^^ (q11 && b)) ^^ u1))) ^^ w) := by
  cases p0 <;> cases p1 <;> cases a <;> cases b <;> cases w <;>
    simp [Bool.xor_comm, Bool.xor_left_comm]

theorem apply_id (x : Bool × Bool) : apply id x = x := by
  cases x with | mk a b => cases a <;> cases b <;> rfl

theorem apply_comp (T2 T1 : Aff2) (x : Bool × Bool) :
    apply (comp T2 T1) x = apply T2 (apply T1 x) := by
  cases T2; cases T1; cases x with | mk a b =>
  simp only [apply, comp, Prod.mk.injEq]
  exact ⟨bool_aff_row _ _ _ _ _ _ _ _ _ _ _, bool_aff_row _ _ _ _ _ _ _ _ _ _ _⟩

theorem id_comp (T : Aff2) : comp id T = T := by
  cases T; simp [comp, id]

theorem comp_id (T : Aff2) : comp T id = T := by
  cases T; simp [comp, id]

private theorem bool_mat_assoc (a0 a1 b00 b01 b10 b11 c0 c1 : Bool) :
    ((((a0 && b00) ^^ (a1 && b10)) && c0) ^^ (((a0 && b01) ^^ (a1 && b11)) && c1)) =
    ((a0 && ((b00 && c0) ^^ (b01 && c1))) ^^ (a1 && ((b10 && c0) ^^ (b11 && c1)))) := by
  cases a0 <;> cases a1 <;> cases c0 <;> cases c1 <;>
    simp [Bool.xor_comm, Bool.xor_left_comm]

theorem comp_assoc (T3 T2 T1 : Aff2) :
    comp (comp T3 T2) T1 = comp T3 (comp T2 T1) := by
  cases T3; cases T2; cases T1
  simp only [comp, mk.injEq]
  refine ⟨bool_mat_assoc _ _ _ _ _ _ _ _, bool_mat_assoc _ _ _ _ _ _ _ _,
          bool_mat_assoc _ _ _ _ _ _ _ _, bool_mat_assoc _ _ _ _ _ _ _ _,
          bool_aff_row _ _ _ _ _ _ _ _ _ _ _, bool_aff_row _ _ _ _ _ _ _ _ _ _ _⟩

theorem pow_add (T : Aff2) (m n : Nat) : pow T (m + n) = comp (pow T m) (pow T n) := by
  induction m with
  | zero => simp [pow, id_comp]
  | succ m ih =>
    rw [Nat.succ_add, pow, ih, pow, comp_assoc]

theorem pow_mul (T : Aff2) (m n : Nat) : pow T (m * n) = pow (pow T m) n := by
  induction n with
  | zero => simp [pow]
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, pow_add, ih, pow]

theorem det_id : det id = true := rfl

theorem det_feistelStep (d c : Bool) : det (feistelStep d c) = true := by
  cases d <;> cases c <;> rfl

private theorem det_comp_bool :
    ∀ a00 a01 a10 a11 b00 b01 b10 b11 : Bool,
      (((((a00 && b00) ^^ (a01 && b10)) && ((a10 && b01) ^^ (a11 && b11))) ^^
        (((a00 && b01) ^^ (a01 && b11)) && ((a10 && b00) ^^ (a11 && b10)))) =
       (((a00 && a11) ^^ (a01 && a10)) && ((b00 && b11) ^^ (b01 && b10)))) := by
  decide

theorem det_comp (T2 T1 : Aff2) : det (comp T2 T1) = (det T2 && det T1) := by
  cases T2; cases T1
  exact det_comp_bool _ _ _ _ _ _ _ _

private theorem invertible_orbit_bool :
    ∀ a00 a01 a10 a11 v0 v1 x0 x1 : Bool,
      let T : Aff2 := ⟨a00, a01, a10, a11, v0, v1⟩
      let x : Bool × Bool := (x0, x1)
      det T = true →
      (apply (pow T 1) x = x) ∨
      (apply (pow T 2) x = x ∧ apply (pow T 1) x ≠ x) ∨
      (apply (pow T 3) x = x ∧ apply (pow T 1) x ≠ x ∧ apply (pow T 2) x ≠ x) ∨
      (apply (pow T 4) x = x ∧ apply (pow T 1) x ≠ x ∧ apply (pow T 2) x ≠ x ∧ apply (pow T 3) x ≠ x) := by
  decide

/-- Exact order classification in `Aff(F_2^2)`: for every invertible affine map `T`
    and every `x ∈ F_2^2`, its orbit length is in `{1, 2, 3, 4}`. -/
theorem invertible_orbit_in_1234 (T : Aff2) (hdet : det T = true) (x : Bool × Bool) :
    (apply (pow T 1) x = x) ∨
    (apply (pow T 2) x = x ∧ apply (pow T 1) x ≠ x) ∨
    (apply (pow T 3) x = x ∧ apply (pow T 1) x ≠ x ∧ apply (pow T 2) x ≠ x) ∨
    (apply (pow T 4) x = x ∧ apply (pow T 1) x ≠ x ∧ apply (pow T 2) x ≠ x ∧ apply (pow T 3) x ≠ x) := by
  cases T; cases x
  exact invertible_orbit_bool _ _ _ _ _ _ _ _ hdet

private theorem pow12_bool :
    ∀ a00 a01 a10 a11 v0 v1 : Bool,
      let T : Aff2 := ⟨a00, a01, a10, a11, v0, v1⟩
      det T = true → pow T 12 = id := by
  decide

/-- Every invertible element of `Aff(F_2^2)` has order dividing 12. -/
theorem pow12_of_det (T : Aff2) (hdet : det T = true) : pow T 12 = id := by
  cases T
  exact pow12_bool _ _ _ _ _ _ hdet

/-- Canonical Feistel step generators. -/
abbrev J0 : Aff2 := feistelStep false false
abbrev J1 : Aff2 := feistelStep true false
abbrev T_on_1001 : Aff2 := feistelStep false true
abbrev T_on_1011 : Aff2 := feistelStep true true

theorem J0_sq : comp J0 J0 = id := rfl
theorem J1_cube : comp J1 (comp J1 J1) = id := rfl

theorem J0_pow_two_mul (k : Nat) : pow J0 (2 * k) = id := by
  rw [pow_mul]; induction k with
  | zero => rfl
  | succ k ih => rw [pow, ih, comp_id]; rfl

theorem J0_pow_two_mul_succ (k : Nat) : pow J0 (2 * k + 1) = J0 := by
  rw [pow_add, J0_pow_two_mul, id_comp]; rfl

theorem J1_pow_three_mul (k : Nat) : pow J1 (3 * k) = id := by
  rw [pow_mul]; induction k with
  | zero => rfl
  | succ k ih => rw [pow, ih, comp_id]; rfl

/-- Key Finite-Group Identity for Theorem I (Period-12 Lock):
    `T_on ∘ J1^2 ∘ T_on = J1 = J1^4`. -/
theorem period12_hit_pairing :
    comp T_on_1001 (comp J1 (comp J1 T_on_1001)) = J1 := rfl

/-- Key Finite-Group Identity for Theorem II (Period-6 Lock):
    `J1^2 ∘ T_on_1011` is pure translation by `(true, false)` (preserving `b`),
    so its square is `id`. -/
theorem period6_half_block :
    comp J1 (comp J1 T_on_1011) = ⟨true, false, false, true, true, false⟩ := rfl

theorem period6_carry_cancel :
    comp (comp J1 (comp J1 T_on_1011)) (comp J1 (comp J1 T_on_1011)) = id := rfl

/-- Key Finite-Group Identity for Theorem IIIb (`ctz(τ)` Phase Transition):
    `(J0 ∘ J1)^2 = id`. -/
theorem ctz_even_hit_cancel :
    comp (comp J0 J1) (comp J0 J1) = id := rfl

/-- Key Finite-Group Identity for Theorem II Sharpness (`R - 1` Exponential Escape):
    `T_on_1011 ∘ J1 ∘ T_on_1011 = (I, (true, true))`. -/
theorem sub1_double_hit_shift :
    comp T_on_1011 (comp J1 T_on_1011) = ⟨true, false, false, true, true, true⟩ := rfl

end Aff2
def truncPair (k : Nat) (s : BitVec (k + 1) × BitVec (k + 1)) : BitVec k × BitVec k :=
  (s.1.setWidth k, s.2.setWidth k)

def topBitPair (k : Nat) (s : BitVec (k + 1) × BitVec (k + 1)) : Bool × Bool :=
  (s.1.getLsbD k, s.2.getLsbD k)

/-- Bit-slice monodromy accumulated over `n` steps from base state `s` at width `k`. -/
def monodromy (f : TriangularRoundFn) (k : Nat) (s : BitVec k × BitVec k) : Nat → Aff2
  | 0 => Aff2.id
  | n + 1 =>
    let cur := feistelIter f k n s
    Aff2.comp (Aff2.feistelStep (f.d k cur.2) (f.c k cur.2)) (monodromy f k s n)

theorem pair_eq_of_trunc_top {k : Nat} {s1 s2 : BitVec (k + 1) × BitVec (k + 1)}
    (ht : truncPair k s1 = truncPair k s2)
    (hb : topBitPair k s1 = topBitPair k s2) : s1 = s2 := by
  rcases s1 with ⟨l1, r1⟩
  rcases s2 with ⟨l2, r2⟩
  simp only [truncPair, topBitPair, Prod.mk.injEq] at ht hb ⊢
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h : i < k
    · have := congrArg (fun v => v.getLsbD i) ht.1
      simpa [BitVec.getLsbD_setWidth, h] using this
    · have hik : i = k := by omega
      subst hik; exact hb.1
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h : i < k
    · have := congrArg (fun v => v.getLsbD i) ht.2
      simpa [BitVec.getLsbD_setWidth, h] using this
    · have hik : i = k := by omega
      subst hik; exact hb.2

theorem feistelIter_add (f : TriangularRoundFn) (w m n : Nat) (s : BitVec w × BitVec w) :
    feistelIter f w (m + n) s = feistelIter f w m (feistelIter f w n s) := by
  induction m with
  | zero => simp [feistelIter]
  | succ m ih => rw [Nat.succ_add, feistelIter, ih, feistelIter]

theorem feistelIter_truncate (f : TriangularRoundFn) (k n : Nat)
    (s : BitVec (k + 1) × BitVec (k + 1)) :
    truncPair k (feistelIter f (k + 1) n s) = feistelIter f k n (truncPair k s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [feistelIter]
    rw [← ih]
    simp only [feistelStepF, truncPair, BitVec.setWidth_xor, f.trunc_compat]

theorem feistelIter_topBit (f : TriangularRoundFn) (k n : Nat)
    (s : BitVec (k + 1) × BitVec (k + 1)) :
    topBitPair k (feistelIter f (k + 1) n s) =
      Aff2.apply (monodromy f k (truncPair k s) n) (topBitPair k s) := by
  induction n with
  | zero =>
    simp [feistelIter, monodromy, Aff2.apply_id]
  | succ n ih =>
    simp only [feistelIter, monodromy]
    rw [Aff2.apply_comp, ← ih]
    have htr := feistelIter_truncate f k n s
    have hu2 : (feistelIter f k n (truncPair k s)).2 = (feistelIter f (k + 1) n s).2.setWidth k := by
      rw [← htr]; rfl
    rw [hu2]
    generalize feistelIter f (k + 1) n s = u
    simp only [feistelStepF, topBitPair, Aff2.apply, Aff2.feistelStep, Prod.mk.injEq]
    constructor
    · cases u.1.getLsbD k <;> cases u.2.getLsbD k <;> rfl
    · rw [BitVec.getLsbD_xor, f.topBit_law]
      cases u.1.getLsbD k <;> cases (f.d k (u.2.setWidth k)) <;>
        cases u.2.getLsbD k <;> cases (f.c k (u.2.setWidth k)) <;> rfl

theorem monodromy_det (f : TriangularRoundFn) (k n : Nat) (s : BitVec k × BitVec k) :
    Aff2.det (monodromy f k s n) = true := by
  induction n with
  | zero => exact Aff2.det_id
  | succ n ih =>
    simp only [monodromy]
    rw [Aff2.det_comp, Aff2.det_feistelStep, ih]; rfl

theorem monodromy_add (f : TriangularRoundFn) (k m n : Nat) (s : BitVec k × BitVec k) :
    monodromy f k s (m + n) =
      Aff2.comp (monodromy f k (feistelIter f k n s) m) (monodromy f k s n) := by
  induction m with
  | zero => simp [monodromy, Aff2.id_comp]
  | succ m ih =>
    rw [Nat.succ_add, monodromy, ih, monodromy, Aff2.comp_assoc, feistelIter_add]

theorem feistelIter_mul_of_fixed (f : TriangularRoundFn) (w p : Nat) (s : BitVec w × BitVec w)
    (hp : feistelIter f w p s = s) : ∀ n, feistelIter f w (n * p) s = s := by
  intro n
  induction n with
  | zero => simp [feistelIter]
  | succ n ih => rw [Nat.succ_mul, Nat.add_comm, feistelIter_add, ih, hp]

theorem monodromy_mul_of_fixed (f : TriangularRoundFn) (k p m : Nat) (s : BitVec k × BitVec k)
    (hp : feistelIter f k p s = s) :
    monodromy f k s (m * p) = Aff2.pow (monodromy f k s p) m := by
  induction m with
  | zero => simp [monodromy, Aff2.pow]
  | succ m ih =>
    rw [Nat.succ_mul, Nat.add_comm, monodromy_add, feistelIter_mul_of_fixed f k p s hp m, ih, Aff2.pow]

/-- Core Engine Lifting Theorem: if `trunc_k s` is fixed by `F_k^p`, then `F_{k+1}^{m*p}(s) = s`
    if and only if the `m`-th power of the cycle monodromy fixes `topBit_k s`. -/
theorem feistel_period_lift (f : TriangularRoundFn) (k p m : Nat)
    (s : BitVec (k + 1) × BitVec (k + 1))
    (hp : feistelIter f k p (truncPair k s) = truncPair k s) :
    feistelIter f (k + 1) (m * p) s = s ↔
      Aff2.apply (Aff2.pow (monodromy f k (truncPair k s) p) m) (topBitPair k s) =
        topBitPair k s := by
  have hfix := feistelIter_mul_of_fixed f k p (truncPair k s) hp m
  constructor
  · intro h
    have ht := congrArg (topBitPair k) h
    rw [feistelIter_topBit, monodromy_mul_of_fixed f k p m (truncPair k s) hp] at ht
    exact ht
  · intro hb
    apply pair_eq_of_trunc_top
    · rw [feistelIter_truncate, hfix]
    · rw [feistelIter_topBit, monodromy_mul_of_fixed f k p m (truncPair k s) hp]
      exact hb

theorem exactPeriod_dvd {f : TriangularRoundFn} {w p n : Nat} {s : BitVec w × BitVec w}
    (hex : ExactPeriod f w s p) (hn : feistelIter f w n s = s) : p ∣ n := by
  have hpos := hex.1
  have hrem : feistelIter f w (n % p) s = s := by
    have hdiv : n = (n % p) + (n / p) * p := by
      have hdm := Nat.div_add_mod n p
      rw [Nat.mul_comm] at hdm
      omega
    rw [hdiv, feistelIter_add, feistelIter_mul_of_fixed f w p s hex.2.1 (n / p)] at hn
    exact hn
  by_cases hz : n % p = 0
  · exact Nat.dvd_of_mod_eq_zero hz
  · exfalso
    exact hex.2.2 (n % p) (Nat.pos_of_ne_zero hz) (Nat.mod_lt n hpos) hrem

/-- Exact Period Lift Theorem: lifting an `ExactPeriod p` state through `monodromy`
    multiplies its exact period by an integer `m ∈ {1, 2, 3, 4}`. -/
theorem exactPeriod_lift (f : TriangularRoundFn) (k p : Nat)
    (s : BitVec (k + 1) × BitVec (k + 1))
    (hex : ExactPeriod f k (truncPair k s) p) :
    ∃ m, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) ∧ ExactPeriod f (k + 1) s (m * p) := by
  have hdet := monodromy_det f k p (truncPair k s)
  have horb := Aff2.invertible_orbit_in_1234 (monodromy f k (truncPair k s) p) hdet (topBitPair k s)
  have mk_exact : ∀ m, 0 < m →
      Aff2.apply (Aff2.pow (monodromy f k (truncPair k s) p) m) (topBitPair k s) = topBitPair k s →
      (∀ r, 0 < r → r < m →
        Aff2.apply (Aff2.pow (monodromy f k (truncPair k s) p) r) (topBitPair k s) ≠ topBitPair k s) →
      ExactPeriod f (k + 1) s (m * p) := by
    intro m hm hfix hmin
    refine ⟨Nat.mul_pos hm hex.1, (feistel_period_lift f k p m s hex.2.1).2 hfix, ?_⟩
    intro q hq0 hqlt hqfix
    have htr : feistelIter f k q (truncPair k s) = truncPair k s := by
      have := congrArg (truncPair k) hqfix
      rwa [feistelIter_truncate] at this
    have hdvd : p ∣ q := exactPeriod_dvd hex htr
    rcases hdvd with ⟨r, rfl⟩
    rw [Nat.mul_comm] at hqfix hq0 hqlt
    have hr0 : 0 < r := by
      rcases r with _ | r
      · simp at hq0
      · exact Nat.succ_pos _
    have hrlt : r < m := by
      by_cases hlt : r < m
      · exact hlt
      · exfalso
        have hge : m ≤ r := Nat.le_of_not_lt hlt
        have hmul := Nat.mul_le_mul_right p hge
        exact Nat.not_lt.mpr hmul hqlt
    exact hmin r hr0 hrlt ((feistel_period_lift f k p r s hex.2.1).1 hqfix)
  rcases horb with h1 | ⟨h2, h1n⟩ | ⟨h3, h1n, h2n⟩ | ⟨h4, h1n, h2n, h3n⟩
  · refine ⟨1, Or.inl rfl, mk_exact 1 (by omega) h1 (by intro r hr0 hrlt; omega)⟩
  · refine ⟨2, Or.inr (Or.inl rfl), mk_exact 2 (by omega) h2 ?_⟩
    intro r hr0 hrlt
    have : r = 1 := by omega
    subst this; exact h1n
  · refine ⟨3, Or.inr (Or.inr (Or.inl rfl)), mk_exact 3 (by omega) h3 ?_⟩
    intro r hr0 hrlt
    have : r = 1 ∨ r = 2 := by omega
    rcases this with rfl | rfl <;> assumption
  · refine ⟨4, Or.inr (Or.inr (Or.inr rfl)), mk_exact 4 (by omega) h4 ?_⟩
    intro r hr0 hrlt
    have : r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl <;> assumption

/-- Universal `2^a * 3^b` Period Law: for EVERY triangular round function `f`,
    EVERY bit-width `w`, and EVERY state `s`, its exact minimal period has the form `2^a * 3^b`
    with `a ≤ 2 * w` and `b ≤ w`. -/
theorem feistel_universal_2_3_period (f : TriangularRoundFn) :
    ∀ (w : Nat) (s : BitVec w × BitVec w),
      ∃ a b, a ≤ 2 * w ∧ b ≤ w ∧ ExactPeriod f w s (2 ^ a * 3 ^ b) := by
  intro w
  induction w with
  | zero =>
    intro s
    refine ⟨0, 0, by omega, by omega, by omega, ?_, by intro q h1 h2; omega⟩
    rcases s with ⟨l, r⟩
    simp only [feistelIter, feistelStepF, Prod.mk.injEq]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | succ k ih =>
    intro s
    rcases ih (truncPair k s) with ⟨a, b, ha, hb, hex⟩
    rcases exactPeriod_lift f k (2 ^ a * 3 ^ b) s hex with ⟨m, hm, hex'⟩
    rcases hm with rfl | rfl | rfl | rfl
    · refine ⟨a, b, by omega, by omega, ?_⟩; simpa using hex'
    · refine ⟨a + 1, b, by omega, by omega, ?_⟩
      have heq : 2 ^ (a + 1) * 3 ^ b = 2 * (2 ^ a * 3 ^ b) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [heq]; exact hex'
    · refine ⟨a, b + 1, by omega, by omega, ?_⟩
      have heq : 2 ^ a * 3 ^ (b + 1) = 3 * (2 ^ a * 3 ^ b) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [heq]; exact hex'
    · refine ⟨a + 2, b, by omega, by omega, ?_⟩
      have heq : 2 ^ (a + 2) * 3 ^ b = 4 * (2 ^ a * 3 ^ b) := by
        rw [Nat.pow_succ, Nat.pow_succ]
        have h4 : 2 * 2 = 4 := rfl
        calc 2 ^ a * 2 * 2 * 3 ^ b = (2 * 2) * (2 ^ a * 3 ^ b) := by ac_rfl
          _ = 4 * (2 ^ a * 3 ^ b) := by rw [h4]
      rw [heq]; exact hex'

theorem setWidth_triggerPrefix (τ : Nat → Bool) (k : Nat) :
    (triggerPrefix τ (k + 1)).setWidth k = triggerPrefix τ k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
      getLsbD_triggerPrefix τ (k + 1) i (Nat.lt_succ_of_lt hi),
      getLsbD_triggerPrefix τ k i hi]

/-! ### Exact Ripple-Carry & Ripple-Borrow Lemmas for Real `BitVec w` Hardware Ops -/

/-- Exact carry bit into position `i` of `R + 1`: true iff all bits `j < i` of `R` are `true`. -/
theorem carry_add_one {w : Nat} (R : BitVec w) :
    ∀ i, i ≤ w → BitVec.carry i R (1#w) false =
      if i = 0 then false else prefixMatch (fun _ => true) R i := by
  intro i hi
  induction i with
  | zero => simp [BitVec.carry, Nat.mod_one]
  | succ j ih =>
    rw [BitVec.carry_succ, ih (by omega)]
    cases j with
    | zero =>
      have hw : 0 < w := by omega
      have h10 : (1#w).getLsbD 0 = true := by simp [hw]
      simp only [↓reduceIte, prefixMatch, Bool.true_and, h10]
      cases R.getLsbD 0 <;> rfl
    | succ m =>
      have h1 : (1#w).getLsbD (m + 1) = false := by
        simp [BitVec.getLsbD_ofNat, Nat.testBit_succ]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, h1]
      change Bool.atLeastTwo (R.getLsbD (m + 1)) false (prefixMatch (fun _ => true) R (m + 1)) =
        (prefixMatch (fun _ => true) R (m + 1) && (R.getLsbD (m + 1) == true))
      cases prefixMatch (fun _ => true) R (m + 1) <;> cases R.getLsbD (m + 1) <;> rfl

/-- Exact bit-slice formula for hardware increment `R + 1`. -/
theorem getLsbD_add_one {w : Nat} (R : BitVec w) (i : Nat) (hi : i < w) :
    (R + 1#w).getLsbD i = (R.getLsbD i ^^ prefixMatch (fun _ => true) R i) := by
  rw [BitVec.getLsbD_add hi, carry_add_one R i (Nat.le_of_lt hi)]
  cases i with
  | zero =>
    simp [hi, prefixMatch]
  | succ j =>
    have h1 : (1#w).getLsbD (j + 1) = false := by
      simp [BitVec.getLsbD_ofNat, Nat.testBit_succ]
    simp [h1]

/-- Exact bit-slice formula for hardware two's-complement negation `-R`. -/
theorem getLsbD_neg_eq {w : Nat} (R : BitVec w) (i : Nat) (hi : i < w) :
    (-R).getLsbD i = ((!R.getLsbD i) ^^ prefixMatch (fun _ => false) R i) := by
  have hneg : -R = ~~~R + 1#w := BitVec.neg_eq_not_add R
  rw [hneg, getLsbD_add_one (~~~R) i hi, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]
  have hpm : prefixMatch (fun _ => true) (~~~R) i = prefixMatch (fun _ => false) R i := by
    have hle : i ≤ w := Nat.le_of_lt hi
    clear hi
    induction i with
    | zero => rfl
    | succ j ih =>
      have hjw : j < w := by omega
      simp only [prefixMatch, ih (Nat.le_of_lt hjw), BitVec.getLsbD_not, decide_eq_true hjw,
        Bool.true_and]
      cases R.getLsbD j <;> rfl
  rw [hpm]

/-- Exact bit-slice formula for hardware decrement `R - 1`. -/
theorem getLsbD_sub_one {w : Nat} (R : BitVec w) (i : Nat) (hi : i < w) :
    (R - 1#w).getLsbD i = (R.getLsbD i ^^ prefixMatch (fun _ => false) R i) := by
  have hsub : R - 1#w = ~~~(~~~R + 1#w) := by
    have h2 : ~~~R + 1#w = -R := (BitVec.neg_eq_not_add R).symm
    have h3 : ~~~(-R) + 1#w = R := by
      rw [← BitVec.neg_eq_not_add, BitVec.neg_neg]
    calc R - 1#w = (~~~(-R) + 1#w) - 1#w := by rw [h3]
      _ = ~~~(-R) := BitVec.add_sub_cancel _ _
      _ = ~~~(~~~R + 1#w) := by rw [h2]
  rw [hsub, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and,
      getLsbD_add_one (~~~R) i hi, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]
  have hpm : prefixMatch (fun _ => true) (~~~R) i = prefixMatch (fun _ => false) R i := by
    have hle : i ≤ w := Nat.le_of_lt hi
    clear hi
    induction i with
    | zero => rfl
    | succ j ih =>
      have hjw : j < w := by omega
      simp only [prefixMatch, ih (Nat.le_of_lt hjw), BitVec.getLsbD_not, decide_eq_true hjw,
        Bool.true_and]
      cases R.getLsbD j <;> rfl
  rw [hpm]
  cases R.getLsbD i <;> cases prefixMatch (fun _ => false) R i <;> rfl

/-! ### Bit-for-Bit Identifications of All 8 Concrete Hardware Mixed-Op Round Functions -/

/-- 1. `R + 1` matches `singleTriggerFn (true, false, true, true)` with `τ ≡ true`. -/
theorem hw_add_one_eq (w : Nat) (R : BitVec w) :
    R + 1#w = (singleTriggerFn true false true true (fun _ => true)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_add_one R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => true) R i <;> cases R.getLsbD i <;> rfl

/-- 2. `R - 1` matches `singleTriggerFn (true, false, true, true)` with `τ ≡ false`. -/
theorem hw_sub_one_eq (w : Nat) (R : BitVec w) :
    R - 1#w = (singleTriggerFn true false true true (fun _ => false)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_sub_one R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => false) R i <;> cases R.getLsbD i <;> rfl

/-- 3. `R ||| (R + 1)` matches `singleTriggerFn (true, false, false, true)` with `τ ≡ true`. -/
theorem hw_or_add_one_eq (w : Nat) (R : BitVec w) :
    R ||| (R + 1#w) = (singleTriggerFn true false false true (fun _ => true)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_or, getLsbD_add_one R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => true) R i <;> cases R.getLsbD i <;> rfl

/-- 4. `R ||| (R - 1)` matches `singleTriggerFn (true, false, false, true)` with `τ ≡ false`. -/
theorem hw_or_sub_one_eq (w : Nat) (R : BitVec w) :
    R ||| (R - 1#w) = (singleTriggerFn true false false true (fun _ => false)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_or, getLsbD_sub_one R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => false) R i <;> cases R.getLsbD i <;> rfl

/-- 5. `R ^^^ (R + 1)` matches `singleTriggerFn (false, false, false, true)` with `τ ≡ true`. -/
theorem hw_xor_add_one_eq (w : Nat) (R : BitVec w) :
    R ^^^ (R + 1#w) = (singleTriggerFn false false false true (fun _ => true)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_add_one R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => true) R i <;> cases R.getLsbD i <;> rfl

/-- 6. `R ^^^ (R - 1)` matches `singleTriggerFn (false, false, false, true)` with `τ ≡ false`. -/
theorem hw_xor_sub_one_eq (w : Nat) (R : BitVec w) :
    R ^^^ (R - 1#w) = (singleTriggerFn false false false true (fun _ => false)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_sub_one R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => false) R i <;> cases R.getLsbD i <;> rfl

/-- 7. `R &&& (-R)` (isolate lowest set bit) matches `singleTriggerFn (false, false, true, false)`
    with `τ ≡ false`. -/
theorem hw_lsb_eq (w : Nat) (R : BitVec w) :
    R &&& (-R) = (singleTriggerFn false false true false (fun _ => false)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, getLsbD_neg_eq R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => false) R i <;> cases R.getLsbD i <;> rfl

/-- 8. `R &&& ~~~(R + 1)` (trailing-ones mask) matches `singleTriggerFn (false, false, true, false)`
    with `τ ≡ true`. -/
theorem hw_trail_ones_eq (w : Nat) (R : BitVec w) :
    R &&& ~~~(R + 1#w) = (singleTriggerFn false false true false (fun _ => true)).fn w R := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and,
      getLsbD_add_one R i hi]
  simp only [singleTriggerFn, getLsbD_bvOfBits w _ i hi]
  cases prefixMatch (fun _ => true) R i <;> cases R.getLsbD i <;> rfl

theorem hwFeistelIter_eq_feistelIter (g : (w : Nat) → BitVec w → BitVec w)
    (f : TriangularRoundFn) (h : ∀ w R, g w R = f.fn w R) (w n : Nat)
    (s : BitVec w × BitVec w) :
    hwFeistelIter g w n s = feistelIter f w n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [hwFeistelIter, feistelIter, feistelStepF, ih, h]

theorem feistelStepF_inj (f : TriangularRoundFn) (w : Nat) {s1 s2 : BitVec w × BitVec w}
    (h : feistelStepF f w s1 = feistelStepF f w s2) : s1 = s2 := by
  rcases s1 with ⟨l1, r1⟩
  rcases s2 with ⟨l2, r2⟩
  simp only [feistelStepF, Prod.mk.injEq] at h
  rcases h with ⟨hr, hl⟩
  subst hr
  have hl' : (l1 ^^^ f.fn w r1) ^^^ f.fn w r1 = (l2 ^^^ f.fn w r1) ^^^ f.fn w r1 :=
    congrArg (· ^^^ f.fn w r1) hl
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at hl'
  rw [hl']

theorem feistelIter_inj (f : TriangularRoundFn) (w n : Nat) {s1 s2 : BitVec w × BitVec w}
    (h : feistelIter f w n s1 = feistelIter f w n s2) : s1 = s2 := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (feistelStepF_inj f w h)

theorem exactPeriod_shift (f : TriangularRoundFn) (w p r : Nat) (s : BitVec w × BitVec w) :
    ExactPeriod f w (feistelIter f w r s) p ↔ ExactPeriod f w s p := by
  have hcomm : ∀ q, feistelIter f w q (feistelIter f w r s) =
      feistelIter f w r (feistelIter f w q s) := by
    intro q; rw [← feistelIter_add, ← feistelIter_add, Nat.add_comm]
  constructor
  · rintro ⟨hp, hfix, hmin⟩
    refine ⟨hp, ?_, ?_⟩
    · apply feistelIter_inj f w r
      rw [← hcomm p]; exact hfix
    · intro q hq0 hqlt hqfix
      apply hmin q hq0 hqlt
      rw [hcomm q, hqfix]
  · rintro ⟨hp, hfix, hmin⟩
    refine ⟨hp, ?_, ?_⟩
    · rw [hcomm p, hfix]
    · intro q hq0 hqlt hqfix
      apply hmin q hq0 hqlt
      apply feistelIter_inj f w r
      rw [← hcomm q]; exact hqfix

theorem feistelIter_eq_mod (f : TriangularRoundFn) (w p n : Nat) (s : BitVec w × BitVec w)
    (hp : feistelIter f w p s = s) :
    feistelIter f w n s = feistelIter f w (n % p) s := by
  have hdiv : n = (n % p) + (n / p) * p := by
    have hdm := Nat.div_add_mod n p
    rw [Nat.mul_comm] at hdm; omega
  conv => lhs; rw [hdiv]
  rw [feistelIter_add, feistelIter_mul_of_fixed f w p s hp]

theorem monodromy_const (f : TriangularRoundFn) (k n : Nat) (s : BitVec k × BitVec k)
    (d c : Bool)
    (h : ∀ t, t < n → f.d k (feistelIter f k t s).2 = d ∧ f.c k (feistelIter f k t s).2 = c) :
    monodromy f k s n = Aff2.pow (Aff2.feistelStep d c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [monodromy, Aff2.pow]
    have hn := h n (Nat.lt_succ_self n)
    rw [hn.1, hn.2, ih (fun t ht => h t (Nat.lt_succ_of_lt ht))]

/-- Helper: in `singleTriggerFn`, `R == triggerPrefix τ (k+1)` splits cleanly into
    truncation equality and top-bit equality. -/
theorem eq_triggerPrefix_succ_iff (τ : Nat → Bool) (k : Nat) (R : BitVec (k + 1)) :
    R = triggerPrefix τ (k + 1) ↔ (R.setWidth k = triggerPrefix τ k ∧ R.getLsbD k = τ k) := by
  constructor
  · intro h; subst h
    exact ⟨setWidth_triggerPrefix τ k, getLsbD_triggerPrefix τ (k + 1) k (Nat.lt_succ_self k)⟩
  · rintro ⟨htr, htop⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h : i < k
    · have := congrArg (fun v => v.getLsbD i) htr
      rw [BitVec.getLsbD_setWidth, decide_eq_true h, Bool.true_and,
          getLsbD_triggerPrefix τ k i h] at this
      rw [getLsbD_triggerPrefix τ (k + 1) i hi, this]
    · have hik : i = k := by omega
      rw [hik, getLsbD_triggerPrefix τ (k + 1) k (Nat.lt_succ_self k), htop]

theorem bitvec1_eq_cons (x : BitVec 1) : x = BitVec.cons (x.getLsbD 0) 0#0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi0 : i = 0 := by omega
  rw [hi0, BitVec.getLsbD_cons]; simp

theorem pair1_eq_cons (s : BitVec 1 × BitVec 1) :
    s = (BitVec.cons (s.1.getLsbD 0) 0#0, BitVec.cons (s.2.getLsbD 0) 0#0) :=
  Prod.ext (bitvec1_eq_cons s.1) (bitvec1_eq_cons s.2)

/-! ## Part 5: Theorem IV — Universal Trigger-Independent Isoperiodic `2^(w+1)` Law
    (`Rule (0,0,0,1)`, all 2-adic triggers `τ`, including `R ^^^ (R + 1)` and `R ^^^ (R - 1)`) -/

section TheoremIV
/-- Parity-split XOR accumulator for `fIso`: tracks even-step and odd-step trigger hits. -/
def isoHitEven (τ : Nat → Bool) (k : Nat) (s : BitVec k × BitVec k) : Nat → Bool
  | 0 => false
  | n + 1 =>
    let hit := ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k)
    if n % 2 = 0 then (isoHitEven τ k s n ^^ hit) else isoHitEven τ k s n

def isoHitOdd (τ : Nat → Bool) (k : Nat) (s : BitVec k × BitVec k) : Nat → Bool
  | 0 => false
  | n + 1 =>
    let hit := ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k)
    if n % 2 = 1 then (isoHitOdd τ k s n ^^ hit) else isoHitOdd τ k s n

/-- Exact closed form of the `n`-step monodromy of `fIso τ` in terms of even/odd hit parities. -/
theorem monodromy_fIso (τ : Nat → Bool) (k n : Nat) (s : BitVec k × BitVec k) :
    monodromy (fIso τ) k s n =
      if n % 2 = 0
      then ⟨true, false, false, true, isoHitEven τ k s n, isoHitOdd τ k s n⟩
      else ⟨false, true, true, false, isoHitOdd τ k s n, isoHitEven τ k s n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [monodromy]
    rw [ih]
    have hd : (fIso τ).d k (feistelIter (fIso τ) k n s).2 = false := by
      dsimp only [fIso, singleTriggerFn]
      split <;> rfl
    have hc : (fIso τ).c k (feistelIter (fIso τ) k n s).2 =
        ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k) := by
      dsimp only [fIso, singleTriggerFn]
      split <;> simp_all
    rw [hd, hc]
    by_cases he : n % 2 = 0
    · have hne : (n + 1) % 2 ≠ 0 := by omega
      simp only [he, ↓reduceIte, hne, isoHitEven, isoHitOdd, Nat.zero_ne_one]
      generalize ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k) = h
      cases isoHitEven τ k s n <;> cases isoHitOdd τ k s n <;> cases h <;> rfl
    · have ho : n % 2 = 1 := by omega
      have hne : (n + 1) % 2 = 0 := by omega
      simp only [ho, ↓reduceIte, hne, isoHitEven, isoHitOdd, Nat.one_ne_zero]
      generalize ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k) = h
      cases isoHitEven τ k s n <;> cases isoHitOdd τ k s n <;> cases h <;> rfl

theorem isoHitEven_unique (τ : Nat → Bool) (k n t0 : Nat) (s : BitVec k × BitVec k)
    (ht0 : t0 < n) (heven : t0 % 2 = 0)
    (huniq : ∀ t, t < n → t % 2 = 0 →
      ((feistelIter (fIso τ) k t s).2 = triggerPrefix τ k ↔ t = t0)) :
    isoHitEven τ k s n = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [isoHitEven]
    by_cases hnt : n = t0
    · subst hnt
      simp only [heven, ↓reduceIte]
      have hhit : ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k) = true := by
        rw [beq_iff_eq]; exact (huniq n (Nat.lt_succ_self n) heven).2 rfl
      have hzero : ∀ m, m ≤ n → isoHitEven τ k s m = false := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          simp only [isoHitEven]
          by_cases hme : m % 2 = 0
          · simp only [hme, ↓reduceIte, ihm (by omega), Bool.false_xor]
            rw [beq_eq_false_iff_ne]
            intro heq
            have := (huniq m (by omega) hme).1 heq
            omega
          · simp only [hme, ↓reduceIte, ihm (by omega)]
      rw [hzero n (Nat.le_refl n), hhit]; rfl
    · have ht0' : t0 < n := by omega
      have hih := ih ht0' (fun t ht hte => huniq t (Nat.lt_succ_of_lt ht) hte)
      by_cases hne : n % 2 = 0
      · simp only [hne, ↓reduceIte, hih]
        have hno : ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k) = false := by
          rw [beq_eq_false_iff_ne]
          intro heq
          exact hnt ((huniq n (Nat.lt_succ_self n) hne).1 heq)
        rw [hno]; rfl
      · simp only [hne, ↓reduceIte, hih]

theorem isoHitOdd_unique (τ : Nat → Bool) (k n t1 : Nat) (s : BitVec k × BitVec k)
    (ht1 : t1 < n) (hodd : t1 % 2 = 1)
    (huniq : ∀ t, t < n → t % 2 = 1 →
      ((feistelIter (fIso τ) k t s).2 = triggerPrefix τ k ↔ t = t1)) :
    isoHitOdd τ k s n = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [isoHitOdd]
    by_cases hnt : n = t1
    · subst hnt
      simp only [hodd, ↓reduceIte]
      have hhit : ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k) = true := by
        rw [beq_iff_eq]; exact (huniq n (Nat.lt_succ_self n) hodd).2 rfl
      have hzero : ∀ m, m ≤ n → isoHitOdd τ k s m = false := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          simp only [isoHitOdd]
          by_cases hmo : m % 2 = 1
          · simp only [hmo, ↓reduceIte, ihm (by omega), Bool.false_xor]
            rw [beq_eq_false_iff_ne]
            intro heq
            have := (huniq m (by omega) hmo).1 heq
            omega
          · simp only [hmo, ↓reduceIte, ihm (by omega)]
      rw [hzero n (Nat.le_refl n), hhit]; rfl
    · have ht1' : t1 < n := by omega
      have hih := ih ht1' (fun t ht hto => huniq t (Nat.lt_succ_of_lt ht) hto)
      by_cases hno : n % 2 = 1
      · simp only [hno, ↓reduceIte, hih]
        have hnohit : ((feistelIter (fIso τ) k n s).2 == triggerPrefix τ k) = false := by
          rw [beq_eq_false_iff_ne]
          intro heq
          exact hnt ((huniq n (Nat.lt_succ_self n) hno).1 heq)
        rw [hnohit]; rfl
      · simp only [hno, ↓reduceIte, hih]

/-- Inductive Isoperiodic Invariant for `Rule (0,0,0,1)` at width `k = n + 1`. -/
structure IsoInv (τ : Nat → Bool) (k : Nat) (s : BitVec k × BitVec k) : Prop where
  exact_per : ExactPeriod (fIso τ) k s (2 ^ (k + 1))
  even_hit : ∃ t0, t0 < 2 ^ (k + 1) ∧ t0 % 2 = 0 ∧
    ∀ t, t < 2 ^ (k + 1) → t % 2 = 0 →
      ((feistelIter (fIso τ) k t s).2 = triggerPrefix τ k ↔ t = t0)
  odd_hit : ∃ t1, t1 < 2 ^ (k + 1) ∧ t1 % 2 = 1 ∧
    ∀ t, t < 2 ^ (k + 1) → t % 2 = 1 →
      ((feistelIter (fIso τ) k t s).2 = triggerPrefix τ k ↔ t = t1)

private theorem isoInv_base_bool :
    ∀ t0 l r : Bool,
      let τ : Nat → Bool := fun _ => t0
      let s : BitVec 1 × BitVec 1 := (BitVec.cons l 0#0, BitVec.cons r 0#0)
      feistelIter (fIso τ) 1 4 s = s ∧
      feistelIter (fIso τ) 1 1 s ≠ s ∧
      feistelIter (fIso τ) 1 2 s ≠ s ∧
      feistelIter (fIso τ) 1 3 s ≠ s ∧
      (((feistelIter (fIso τ) 1 0 s).2 == triggerPrefix τ 1) ^^
        ((feistelIter (fIso τ) 1 2 s).2 == triggerPrefix τ 1)) = true ∧
      (((feistelIter (fIso τ) 1 1 s).2 == triggerPrefix τ 1) ^^
        ((feistelIter (fIso τ) 1 3 s).2 == triggerPrefix τ 1)) = true := by
  decide

theorem isoInv_base (τ : Nat → Bool) (s : BitVec 1 × BitVec 1) : IsoInv τ 1 s := by
  -- At width 1, `fIso τ` and `triggerPrefix τ 1` depend only on `τ 0`
  have hfeq : ∀ n, feistelIter (fIso τ) 1 n s = feistelIter (fIso (fun _ => τ 0)) 1 n s := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [feistelIter, feistelStepF, ih]
      refine Prod.ext rfl (congrArg (_ ^^^ ·) ?_)
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]
      simp only [fIso, singleTriggerFn, getLsbD_bvOfBits 1 _ 0 (by omega), prefixMatch]
  have htpeq : triggerPrefix τ 1 = triggerPrefix (fun _ => τ 0) 1 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hi0 : i = 0 := by omega
    rw [hi0, getLsbD_triggerPrefix τ 1 0 (by omega), getLsbD_triggerPrefix (fun _ => τ 0) 1 0 (by omega)]
  have hs := pair1_eq_cons s
  have hb := isoInv_base_bool (τ 0) (s.1.getLsbD 0) (s.2.getLsbD 0)
  rw [← hs] at hb
  rcases hb with ⟨h4, h1, h2, h3, hev, hod⟩
  constructor
  · refine ⟨by omega, ?_, ?_⟩
    · rw [hfeq 4]; exact h4
    · intro q hq0 hqlt
      rw [hfeq q]
      have : q = 1 ∨ q = 2 ∨ q = 3 := by omega
      rcases this with rfl | rfl | rfl <;> assumption
  · cases h0 : ((feistelIter (fIso (fun _ => τ 0)) 1 0 s).2 == triggerPrefix (fun _ => τ 0) 1)
    · rw [h0, Bool.false_xor] at hev
      refine ⟨2, by omega, by omega, ?_⟩
      intro t ht hte
      rw [hfeq t, htpeq]
      have : t = 0 ∨ t = 2 := by omega
      rcases this with rfl | rfl
      · simp [beq_eq_false_iff_ne.1 h0]
      · simp [beq_iff_eq.1 hev]
    · rw [h0, Bool.true_xor] at hev
      have h2f : ((feistelIter (fIso (fun _ => τ 0)) 1 2 s).2 == triggerPrefix (fun _ => τ 0) 1) = false := by
        cases h2b : ((feistelIter (fIso (fun _ => τ 0)) 1 2 s).2 == triggerPrefix (fun _ => τ 0) 1)
        · rfl
        · rw [h2b] at hev; cases hev
      refine ⟨0, by omega, by omega, ?_⟩
      intro t ht hte
      rw [hfeq t, htpeq]
      have : t = 0 ∨ t = 2 := by omega
      rcases this with rfl | rfl
      · simp [beq_iff_eq.1 h0]
      · simp [beq_eq_false_iff_ne.1 h2f]
  · cases h1b : ((feistelIter (fIso (fun _ => τ 0)) 1 1 s).2 == triggerPrefix (fun _ => τ 0) 1)
    · rw [h1b, Bool.false_xor] at hod
      refine ⟨3, by omega, by omega, ?_⟩
      intro t ht hto
      rw [hfeq t, htpeq]
      have : t = 1 ∨ t = 3 := by omega
      rcases this with rfl | rfl
      · simp [beq_eq_false_iff_ne.1 h1b]
      · simp [beq_iff_eq.1 hod]
    · rw [h1b, Bool.true_xor] at hod
      have h3f : ((feistelIter (fIso (fun _ => τ 0)) 1 3 s).2 == triggerPrefix (fun _ => τ 0) 1) = false := by
        cases h3b : ((feistelIter (fIso (fun _ => τ 0)) 1 3 s).2 == triggerPrefix (fun _ => τ 0) 1)
        · rfl
        · rw [h3b] at hod; cases hod
      refine ⟨1, by omega, by omega, ?_⟩
      intro t ht hto
      rw [hfeq t, htpeq]
      have : t = 1 ∨ t = 3 := by omega
      rcases this with rfl | rfl
      · simp [beq_iff_eq.1 h1b]
      · simp [beq_eq_false_iff_ne.1 h3f]

theorem isoInv_step (τ : Nat → Bool) (k : Nat)
    (s : BitVec (k + 1) × BitVec (k + 1)) (ih : IsoInv τ k (truncPair k s)) :
    IsoInv τ (k + 1) s := by
  let p := 2 ^ (k + 1)
  have hp_even : p % 2 = 0 := by
    have : p = 2 * 2 ^ k := by simp [p, Nat.pow_succ, Nat.mul_comm]
    omega
  have hp2 : 2 ^ (k + 1 + 1) = 2 * p := by
    simp [p, Nat.pow_succ, Nat.mul_comm]
  rcases ih.even_hit with ⟨t0, ht0, ht0e, huniq0⟩
  rcases ih.odd_hit with ⟨t1, ht1, ht1o, huniq1⟩
  have hmono : monodromy (fIso τ) k (truncPair k s) p = ⟨true, false, false, true, true, true⟩ := by
    rw [monodromy_fIso]
    simp only [hp_even, ↓reduceIte,
        isoHitEven_unique τ k p t0 (truncPair k s) ht0 ht0e huniq0,
        isoHitOdd_unique τ k p t1 (truncPair k s) ht1 ht1o huniq1]
  have hfix2 : Aff2.apply (Aff2.pow (monodromy (fIso τ) k (truncPair k s) p) 2) (topBitPair k s) =
      topBitPair k s := by
    rw [hmono]
    rcases topBitPair k s with ⟨a, b⟩; cases a <;> cases b <;> rfl
  have hne1 : Aff2.apply (Aff2.pow (monodromy (fIso τ) k (truncPair k s) p) 1) (topBitPair k s) ≠
      topBitPair k s := by
    rw [hmono]
    rcases topBitPair k s with ⟨a, b⟩; cases a <;> cases b <;> decide
  have hex2 : ExactPeriod (fIso τ) (k + 1) s (2 * p) := by
    refine ⟨by omega, (feistel_period_lift (fIso τ) k p 2 s ih.exact_per.2.1).2 hfix2, ?_⟩
    intro q hq0 hqlt hqfix
    have htr : feistelIter (fIso τ) k q (truncPair k s) = truncPair k s := by
      have := congrArg (truncPair k) hqfix
      rwa [feistelIter_truncate] at this
    have hdvd : p ∣ q := exactPeriod_dvd ih.exact_per htr
    rcases hdvd with ⟨r, rfl⟩
    have hr1 : r = 1 := by
      rcases r with _ | r
      · simp at hq0
      · rcases r with _ | r
        · rfl
        · exfalso
          have hle : 2 * p ≤ p * (r + 2) := by
            rw [Nat.mul_comm 2 p]
            exact Nat.mul_le_mul_left p (by omega)
          exact Nat.not_lt.mpr hle hqlt
    subst hr1
    rw [Nat.mul_one] at hqfix
    have h1 := (feistel_period_lift (fIso τ) k p 1 s ih.exact_per.2.1).1 (by simpa using hqfix)
    exact hne1 h1
  -- Top bit of R flips after +p steps because both `I` and `J0` fix `(1, 1)`!
  have hflip : ∀ t, (feistelIter (fIso τ) (k + 1) (t + p) s).2.getLsbD k =
      !(feistelIter (fIso τ) (k + 1) t s).2.getLsbD k := by
    intro t
    have htp := feistelIter_topBit (fIso τ) k (t + p) s
    have ht := feistelIter_topBit (fIso τ) k t s
    rw [monodromy_add, ih.exact_per.2.1, hmono, Aff2.apply_comp] at htp
    have hcomm : ∀ (T : Aff2) (x : Bool × Bool),
        (T.m00 = true ∧ T.m01 = false ∧ T.m10 = false ∧ T.m11 = true ∨
         T.m00 = false ∧ T.m01 = true ∧ T.m10 = true ∧ T.m11 = false) →
        (Aff2.apply T (Aff2.apply ⟨true, false, false, true, true, true⟩ x)).2 = !(Aff2.apply T x).2 := by
      intro T x hlin
      rcases T with ⟨m00, m01, m10, m11, v0, v1⟩
      rcases x with ⟨a, b⟩
      rcases hlin with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
        cases v0 <;> cases v1 <;> cases a <;> cases b <;> rfl
    have hlin : let T := monodromy (fIso τ) k (truncPair k s) t
        (T.m00 = true ∧ T.m01 = false ∧ T.m10 = false ∧ T.m11 = true ∨
         T.m00 = false ∧ T.m01 = true ∧ T.m10 = true ∧ T.m11 = false) := by
      rw [monodromy_fIso]
      split
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    have h2 : (topBitPair k (feistelIter (fIso τ) (k + 1) (t + p) s)).2 =
        !(topBitPair k (feistelIter (fIso τ) (k + 1) t s)).2 := by
      rw [htp, ht]
      exact hcomm _ _ hlin
    exact h2
  have htr_hit : ∀ t, (feistelIter (fIso τ) (k + 1) t s).2.setWidth k =
      (feistelIter (fIso τ) k t (truncPair k s)).2 := by
    intro t
    have := congrArg Prod.snd (feistelIter_truncate (fIso τ) k t s)
    exact this
  -- Helper: reducing `t ≥ p` mod `p` on the base trajectory
  have hshift_base : ∀ t, ¬t < p →
      feistelIter (fIso τ) k t (truncPair k s) = feistelIter (fIso τ) k (t - p) (truncPair k s) := by
    intro t hge
    have hsub : t = (t - p) + p := by omega
    conv => lhs; rw [hsub]
    rw [feistelIter_add, ih.exact_per.2.1]
  have hnot_self : ∀ b : Bool, (!b) = b → False := by
    intro b h; cases b <;> cases h
  refine ⟨by rw [hp2]; exact hex2, ?_, ?_⟩
  · -- Unique even hit in `{t0, t0 + p}`
    by_cases hmatch : (feistelIter (fIso τ) (k + 1) t0 s).2.getLsbD k = τ k
    · refine ⟨t0, by omega, ht0e, ?_⟩
      intro t ht hte
      rw [eq_triggerPrefix_succ_iff, htr_hit]
      constructor
      · rintro ⟨htr, htop⟩
        by_cases hlt : t < p
        · exact (huniq0 t hlt hte).1 htr
        · rw [hshift_base t hlt] at htr
          have hte' : (t - p) % 2 = 0 := by omega
          have htm : t - p = t0 := (huniq0 (t - p) (by omega) hte').1 htr
          have ht_eq : t = t0 + p := by omega
          rw [ht_eq, hflip t0, hmatch] at htop
          exact absurd htop (hnot_self (τ k))
      · intro ht_eq
        rw [ht_eq]
        exact ⟨(huniq0 t0 ht0 ht0e).2 rfl, hmatch⟩
    · refine ⟨t0 + p, by omega, by omega, ?_⟩
      intro t ht hte
      rw [eq_triggerPrefix_succ_iff, htr_hit]
      constructor
      · rintro ⟨htr, htop⟩
        by_cases hlt : t < p
        · have heq := (huniq0 t hlt hte).1 htr
          rw [heq] at htop; exact absurd htop hmatch
        · rw [hshift_base t hlt] at htr
          have hte' : (t - p) % 2 = 0 := by omega
          have htm : t - p = t0 := (huniq0 (t - p) (by omega) hte').1 htr
          omega
      · intro ht_eq
        rw [ht_eq]
        refine ⟨?_, ?_⟩
        · rw [feistelIter_add, ih.exact_per.2.1]
          exact (huniq0 t0 ht0 ht0e).2 rfl
        · rw [hflip t0]
          cases h1 : (feistelIter (fIso τ) (k + 1) t0 s).2.getLsbD k <;>
            cases h2 : τ k <;> simp_all
  · -- Unique odd hit in `{t1, t1 + p}`
    by_cases hmatch : (feistelIter (fIso τ) (k + 1) t1 s).2.getLsbD k = τ k
    · refine ⟨t1, by omega, ht1o, ?_⟩
      intro t ht hto
      rw [eq_triggerPrefix_succ_iff, htr_hit]
      constructor
      · rintro ⟨htr, htop⟩
        by_cases hlt : t < p
        · exact (huniq1 t hlt hto).1 htr
        · rw [hshift_base t hlt] at htr
          have hto' : (t - p) % 2 = 1 := by omega
          have htm : t - p = t1 := (huniq1 (t - p) (by omega) hto').1 htr
          have ht_eq : t = t1 + p := by omega
          rw [ht_eq, hflip t1, hmatch] at htop
          exact absurd htop (hnot_self (τ k))
      · intro ht_eq
        rw [ht_eq]
        exact ⟨(huniq1 t1 ht1 ht1o).2 rfl, hmatch⟩
    · refine ⟨t1 + p, by omega, by omega, ?_⟩
      intro t ht hto
      rw [eq_triggerPrefix_succ_iff, htr_hit]
      constructor
      · rintro ⟨htr, htop⟩
        by_cases hlt : t < p
        · have heq := (huniq1 t hlt hto).1 htr
          rw [heq] at htop; exact absurd htop hmatch
        · rw [hshift_base t hlt] at htr
          have hto' : (t - p) % 2 = 1 := by omega
          have htm : t - p = t1 := (huniq1 (t - p) (by omega) hto').1 htr
          omega
      · intro ht_eq
        rw [ht_eq]
        refine ⟨?_, ?_⟩
        · rw [feistelIter_add, ih.exact_per.2.1]
          exact (huniq1 t1 ht1 ht1o).2 rfl
        · rw [hflip t1]
          cases h1 : (feistelIter (fIso τ) (k + 1) t1 s).2.getLsbD k <;>
            cases h2 : τ k <;> simp_all

/-- **THEOREM IV (Universal Trigger-Independent Isoperiodic `2^(w+1)` Law):**
    For EVERY 2-adic trigger `τ : Nat → Bool`, EVERY bit-width `w ≥ 1`, and EVERY state
    `s ∈ (BitVec w)^2`, the Feistel map `(L, R) ↦ (R, L ^^^ fIso(τ)(R))` has EXACT minimal
    period `2^(w+1)` (partitioning all `4^w` states into `2^(w-1)` equal cycles). -/
theorem theorem_IV_universal_isoperiodic (τ : Nat → Bool) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      ExactPeriod (fIso τ) w s (2 ^ (w + 1)) := by
  intro w hw
  have hmain : ∀ n (s : BitVec (n + 1) × BitVec (n + 1)), IsoInv τ (n + 1) s := by
    intro n
    induction n with
    | zero => exact isoInv_base τ
    | succ k ih => intro s; exact isoInv_step τ (k + 1) s (ih (truncPair (k + 1) s))
  cases w with
  | zero => omega
  | succ n => intro s; exact (hmain n s).exact_per

/-- Concrete Hardware Corollary IVa: `(L, R) ↦ (R, L ^^^ (R ^^^ (R + 1)))` is strictly
    isoperiodic of exact period `2^(w+1)` for every `w ≥ 1` and every `(L, R)`. -/
theorem corollary_IVa_hw_xor_add_one (w : Nat) (hw : 1 ≤ w) (s : BitVec w × BitVec w) :
    hwFeistelIter (fun w R => R ^^^ (R + 1#w)) w (2 ^ (w + 1)) s = s ∧
    ∀ q, 0 < q → q < 2 ^ (w + 1) →
      hwFeistelIter (fun w R => R ^^^ (R + 1#w)) w q s ≠ s := by
  have hex := theorem_IV_universal_isoperiodic (fun _ => true) w hw s
  have heq : ∀ n, hwFeistelIter (fun w R => R ^^^ (R + 1#w)) w n s =
      feistelIter (fIso (fun _ => true)) w n s :=
    fun n => hwFeistelIter_eq_feistelIter _ _ hw_xor_add_one_eq w n s
  exact ⟨by rw [heq]; exact hex.2.1, fun q h1 h2 => by rw [heq]; exact hex.2.2 q h1 h2⟩

/-- Concrete Hardware Corollary IVb: `(L, R) ↦ (R, L ^^^ (R ^^^ (R - 1)))` is strictly
    isoperiodic of exact period `2^(w+1)` for every `w ≥ 1` and every `(L, R)`. -/
theorem corollary_IVb_hw_xor_sub_one (w : Nat) (hw : 1 ≤ w) (s : BitVec w × BitVec w) :
    hwFeistelIter (fun w R => R ^^^ (R - 1#w)) w (2 ^ (w + 1)) s = s ∧
    ∀ q, 0 < q → q < 2 ^ (w + 1) →
      hwFeistelIter (fun w R => R ^^^ (R - 1#w)) w q s ≠ s := by
  have hex := theorem_IV_universal_isoperiodic (fun _ => false) w hw s
  have heq : ∀ n, hwFeistelIter (fun w R => R ^^^ (R - 1#w)) w n s =
      feistelIter (fIso (fun _ => false)) w n s :=
    fun n => hwFeistelIter_eq_feistelIter _ _ hw_xor_sub_one_eq w n s
  exact ⟨by rw [heq]; exact hex.2.1, fun q h1 h2 => by rw [heq]; exact hex.2.2 q h1 h2⟩

end TheoremIV

/-! ## Part 6: Theorem I — Universal Trigger-Independent Period-12 Lock
    (`Rule (1,0,0,1)`, all 2-adic triggers `τ`, including `R ||| (R + 1)` and `R ||| (R - 1)`) -/

section TheoremI
/-- A 4-step window `[u, F(u), F^2(u), F^3(u)]` is a `GoodBlock4` if its trigger hits are
    either completely absent (`0000`) or paired at endpoints `(0, 3)` (`1001`). -/
def GoodBlock4 (τ : Nat → Bool) (k : Nat) (u : BitVec k × BitVec k) : Prop :=
  (∀ j, j < 4 → (feistelIter (fP12 τ) k j u).2 ≠ triggerPrefix τ k) ∨
  ((feistelIter (fP12 τ) k 0 u).2 = triggerPrefix τ k ∧
   (feistelIter (fP12 τ) k 1 u).2 ≠ triggerPrefix τ k ∧
   (feistelIter (fP12 τ) k 2 u).2 ≠ triggerPrefix τ k ∧
   (feistelIter (fP12 τ) k 3 u).2 = triggerPrefix τ k)

private theorem fP12_step_eq (τ : Nat → Bool) (k : Nat) (R : BitVec k) :
    Aff2.feistelStep ((fP12 τ).d k R) ((fP12 τ).c k R) =
      if R = triggerPrefix τ k then Aff2.T_on_1001 else Aff2.J1 := by
  dsimp only [fP12, singleTriggerFn]
  by_cases h : R = triggerPrefix τ k
  · simp [h, Aff2.T_on_1001]
  · simp [h, Aff2.J1]

/-- Key Block Monodromy Lemma: EVERY `GoodBlock4` has exact 4-step monodromy `J1`. -/
theorem goodBlock4_monodromy (τ : Nat → Bool) (k : Nat) (u : BitVec k × BitVec k)
    (hg : GoodBlock4 τ k u) :
    monodromy (fP12 τ) k u 4 = Aff2.J1 := by
  simp only [monodromy, fP12_step_eq]
  rcases hg with hnone | ⟨h0, h1, h2, h3⟩
  · have hn0 := hnone 0 (by omega)
    have hn1 := hnone 1 (by omega)
    have hn2 := hnone 2 (by omega)
    have hn3 := hnone 3 (by omega)
    simp only [hn0, hn1, hn2, hn3, ↓reduceIte]; rfl
  · simp only [h0, h1, h2, h3, ↓reduceIte]; rfl

/-- Key Block Lifting Lemma: lifting ANY `GoodBlock4` to width `k + 1` preserves `GoodBlock4`,
    because the 3-step monodromy `J1^2 ∘ T_on_1001` preserves the top `R`-bit! -/
theorem goodBlock4_lift (τ : Nat → Bool) (k : Nat) (U : BitVec (k + 1) × BitVec (k + 1))
    (hg : GoodBlock4 τ k (truncPair k U)) :
    GoodBlock4 τ (k + 1) U := by
  have htr : ∀ j, (feistelIter (fP12 τ) (k + 1) j U).2.setWidth k =
      (feistelIter (fP12 τ) k j (truncPair k U)).2 :=
    fun j => congrArg Prod.snd (feistelIter_truncate (fP12 τ) k j U)
  rcases hg with hnone | ⟨h0, h1, h2, h3⟩
  · left
    intro j hj heq
    rw [eq_triggerPrefix_succ_iff, htr j] at heq
    exact hnone j hj heq.1
  · -- Compute top bit at step 3 via `J1 ∘ J1 ∘ T_on_1001`, which preserves `b`!
    have hm3 : monodromy (fP12 τ) k (truncPair k U) 3 =
        Aff2.comp Aff2.J1 (Aff2.comp Aff2.J1 Aff2.T_on_1001) := by
      simp only [monodromy, fP12_step_eq, h0, h1, h2, ↓reduceIte]; rfl
    have hb3 : (feistelIter (fP12 τ) (k + 1) 3 U).2.getLsbD k = U.2.getLsbD k := by
      have ht := congrArg Prod.snd (feistelIter_topBit (fP12 τ) k 3 U)
      rw [hm3] at ht
      change (topBitPair k (feistelIter (fP12 τ) (k + 1) 3 U)).2 = (topBitPair k U).2
      rw [ht]
      rcases topBitPair k U with ⟨a, b⟩
      cases a <;> cases b <;> rfl
    by_cases htop : U.2.getLsbD k = τ k
    · right
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [eq_triggerPrefix_succ_iff, htr 0]; exact ⟨h0, htop⟩
      · intro heq; rw [eq_triggerPrefix_succ_iff, htr 1] at heq; exact h1 heq.1
      · intro heq; rw [eq_triggerPrefix_succ_iff, htr 2] at heq; exact h2 heq.1
      · rw [eq_triggerPrefix_succ_iff, htr 3, hb3]; exact ⟨h3, htop⟩
    · left
      intro j hj heq
      rw [eq_triggerPrefix_succ_iff, htr j] at heq
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact htop heq.2
      · exact h1 heq.1
      · exact h2 heq.1
      · rw [hb3] at heq; exact htop heq.2

/-- Complete inductive orbit invariant for `Rule (1,0,0,1)` at width `k ≥ 1`. -/
def P12Inv (τ : Nat → Bool) (k : Nat) (s : BitVec k × BitVec k) : Prop :=
  (ExactPeriod (fP12 τ) k s 4 ∧ ∃ r, r < 4 ∧ GoodBlock4 τ k (feistelIter (fP12 τ) k r s)) ∨
  (ExactPeriod (fP12 τ) k s 12 ∧ ∃ r, r < 12 ∧
    GoodBlock4 τ k (feistelIter (fP12 τ) k r s) ∧
    GoodBlock4 τ k (feistelIter (fP12 τ) k (r + 4) s) ∧
    GoodBlock4 τ k (feistelIter (fP12 τ) k (r + 8) s))

private theorem p12Inv_base_bool :
    ∀ t0 l r : Bool,
      let τ : Nat → Bool := fun _ => t0
      let s : BitVec 1 × BitVec 1 := (BitVec.cons l 0#0, BitVec.cons r 0#0)
      feistelIter (fP12 τ) 1 4 s = s ∧
      feistelIter (fP12 τ) 1 1 s ≠ s ∧
      feistelIter (fP12 τ) 1 2 s ≠ s ∧
      feistelIter (fP12 τ) 1 3 s ≠ s ∧
      (∃ sh : Fin 4,
        let u := feistelIter (fP12 τ) 1 sh.val s
        (feistelIter (fP12 τ) 1 0 u).2 = triggerPrefix τ 1 ∧
        (feistelIter (fP12 τ) 1 1 u).2 ≠ triggerPrefix τ 1 ∧
        (feistelIter (fP12 τ) 1 2 u).2 ≠ triggerPrefix τ 1 ∧
        (feistelIter (fP12 τ) 1 3 u).2 = triggerPrefix τ 1) := by
  decide

theorem p12Inv_base (τ : Nat → Bool) (s : BitVec 1 × BitVec 1) : P12Inv τ 1 s := by
  have hfeq : ∀ n, feistelIter (fP12 τ) 1 n s = feistelIter (fP12 (fun _ => τ 0)) 1 n s := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [feistelIter, feistelStepF, ih]
      refine Prod.ext rfl (congrArg (_ ^^^ ·) ?_)
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]; simp only [fP12, singleTriggerFn, getLsbD_bvOfBits 1 _ 0 (by omega), prefixMatch]
  have htpeq : triggerPrefix τ 1 = triggerPrefix (fun _ => τ 0) 1 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hi0 : i = 0 := by omega
    rw [hi0, getLsbD_triggerPrefix τ 1 0 (by omega), getLsbD_triggerPrefix (fun _ => τ 0) 1 0 (by omega)]
  have hs := pair1_eq_cons s
  have hb := p12Inv_base_bool (τ 0) (s.1.getLsbD 0) (s.2.getLsbD 0)
  rw [← hs] at hb
  rcases hb with ⟨h4, h1, h2, h3, ⟨sh, hb0, hb1, hb2, hb3⟩⟩
  left
  refine ⟨⟨by omega, by rw [hfeq]; exact h4, ?_⟩, sh.val, sh.isLt, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · intro q hq0 hqlt; rw [hfeq]
    have : q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  · rw [← feistelIter_add, hfeq, feistelIter_add, htpeq]; exact hb0
  · rw [← feistelIter_add, hfeq, feistelIter_add, htpeq]; exact hb1
  · rw [← feistelIter_add, hfeq, feistelIter_add, htpeq]; exact hb2
  · rw [← feistelIter_add, hfeq, feistelIter_add, htpeq]; exact hb3

theorem p12Inv_step (τ : Nat → Bool) (k : Nat) (s : BitVec (k + 1) × BitVec (k + 1))
    (ih : P12Inv τ k (truncPair k s)) : P12Inv τ (k + 1) s := by
  rcases ih with ⟨hex4, r, hr, hgb⟩ | ⟨hex12, r, hr, hgb0, hgb1, hgb2⟩
  · -- Lift a 4-cycle via monodromy `J1` into `(1, 3)` (one 4-cycle + one 12-cycle)
    let U := feistelIter (fP12 τ) (k + 1) r s
    have htrU : truncPair k U = feistelIter (fP12 τ) k r (truncPair k s) :=
      feistelIter_truncate (fP12 τ) k r s
    have hexU4 : ExactPeriod (fP12 τ) k (truncPair k U) 4 := by
      rw [htrU]; exact (exactPeriod_shift (fP12 τ) k 4 r (truncPair k s)).2 hex4
    have hgbU : GoodBlock4 τ k (truncPair k U) := by rw [htrU]; exact hgb
    have hmono : monodromy (fP12 τ) k (truncPair k U) 4 = Aff2.J1 :=
      goodBlock4_monodromy τ k (truncPair k U) hgbU
    cases ha : (topBitPair k U).1 <;> cases hb : (topBitPair k U).2
    · -- Top bit `(false, false)` is fixed by `J1` → Type 4
      have htop : topBitPair k U = (false, false) := Prod.ext ha hb
      have hfix1 : Aff2.apply (Aff2.pow (monodromy (fP12 τ) k (truncPair k U) 4) 1) (topBitPair k U) =
          topBitPair k U := by rw [hmono, htop]; rfl
      have hexU4' : ExactPeriod (fP12 τ) (k + 1) U 4 := by
        refine ⟨by omega, by simpa using (feistel_period_lift (fP12 τ) k 4 1 U hexU4.2.1).2 hfix1, ?_⟩
        intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix
        rw [feistelIter_truncate] at this
        exact hexU4.2.2 q hq0 hqlt this
      left
      exact ⟨(exactPeriod_shift (fP12 τ) (k + 1) 4 r s).1 hexU4',
             r, hr, goodBlock4_lift τ k U hgbU⟩
    all_goals
      -- Top bit in `{(false,true), (true,false), (true,true)}`: exact 3-cycle of `J1` → Type 12!
      have hfix3 : Aff2.apply (Aff2.pow (monodromy (fP12 τ) k (truncPair k U) 4) 3) (topBitPair k U) =
          topBitPair k U := by
        rw [hmono]; have htop : topBitPair k U = (_, _) := Prod.ext ha hb; rw [htop]; rfl
      have hne1 : Aff2.apply (Aff2.pow (monodromy (fP12 τ) k (truncPair k U) 4) 1) (topBitPair k U) ≠
          topBitPair k U := by
        rw [hmono]; have htop : topBitPair k U = (_, _) := Prod.ext ha hb; rw [htop]; decide
      have hne2 : Aff2.apply (Aff2.pow (monodromy (fP12 τ) k (truncPair k U) 4) 2) (topBitPair k U) ≠
          topBitPair k U := by
        rw [hmono]; have htop : topBitPair k U = (_, _) := Prod.ext ha hb; rw [htop]; decide
      have hexU12 : ExactPeriod (fP12 τ) (k + 1) U 12 := by
        refine ⟨by omega, (feistel_period_lift (fP12 τ) k 4 3 U hexU4.2.1).2 hfix3, ?_⟩
        intro q hq0 hqlt hqfix
        have htrq : feistelIter (fP12 τ) k q (truncPair k U) = truncPair k U := by
          have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate] at this
        rcases exactPeriod_dvd hexU4 htrq with ⟨m, rfl⟩
        have : m = 1 ∨ m = 2 := by omega
        rcases this with rfl | rfl
        · exact hne1 ((feistel_period_lift (fP12 τ) k 4 1 U hexU4.2.1).1 (by simpa using hqfix))
        · exact hne2 ((feistel_period_lift (fP12 τ) k 4 2 U hexU4.2.1).1 (by simpa [Nat.mul_comm] using hqfix))
      right
      refine ⟨(exactPeriod_shift (fP12 τ) (k + 1) 12 r s).1 hexU12, r, by omega, ?_, ?_, ?_⟩
      · exact goodBlock4_lift τ k U hgbU
      · apply goodBlock4_lift τ k
        rw [feistelIter_truncate, Nat.add_comm r 4, feistelIter_add, ← htrU, hexU4.2.1]
        exact hgbU
      · apply goodBlock4_lift τ k
        rw [feistelIter_truncate, Nat.add_comm r 8, feistelIter_add, ← htrU]
        have h8 : feistelIter (fP12 τ) k 8 (truncPair k U) = truncPair k U :=
          feistelIter_mul_of_fixed (fP12 τ) k 4 (truncPair k U) hexU4.2.1 2
        rw [h8]; exact hgbU
  · -- Lift a 12-cycle via monodromy `J1^3 = id` into `(1,1,1,1)` (four 12-cycles)
    let U := feistelIter (fP12 τ) (k + 1) r s
    have htrU : truncPair k U = feistelIter (fP12 τ) k r (truncPair k s) :=
      feistelIter_truncate (fP12 τ) k r s
    have hexU12 : ExactPeriod (fP12 τ) k (truncPair k U) 12 := by
      rw [htrU]; exact (exactPeriod_shift (fP12 τ) k 12 r (truncPair k s)).2 hex12
    have hm0 : monodromy (fP12 τ) k (truncPair k U) 4 = Aff2.J1 :=
      goodBlock4_monodromy τ k (truncPair k U) (by rw [htrU]; exact hgb0)
    have hm1 : monodromy (fP12 τ) k (feistelIter (fP12 τ) k 4 (truncPair k U)) 4 = Aff2.J1 := by
      rw [htrU, ← feistelIter_add, Nat.add_comm 4 r]
      exact goodBlock4_monodromy τ k _ hgb1
    have hm2 : monodromy (fP12 τ) k (feistelIter (fP12 τ) k 8 (truncPair k U)) 4 = Aff2.J1 := by
      rw [htrU, ← feistelIter_add, Nat.add_comm 8 r]
      exact goodBlock4_monodromy τ k _ hgb2
    have hmono : monodromy (fP12 τ) k (truncPair k U) 12 = Aff2.id := by
      have h12 : (12 : Nat) = 4 + (4 + 4) := rfl
      rw [h12, monodromy_add, monodromy_add, hm0, hm1, hm2]; rfl
    have hfix1 : Aff2.apply (Aff2.pow (monodromy (fP12 τ) k (truncPair k U) 12) 1) (topBitPair k U) =
        topBitPair k U := by
      rw [hmono]; simp [Aff2.pow, Aff2.comp_id, Aff2.apply_id]
    have hexU12' : ExactPeriod (fP12 τ) (k + 1) U 12 := by
      refine ⟨by omega, by simpa using (feistel_period_lift (fP12 τ) k 12 1 U hexU12.2.1).2 hfix1, ?_⟩
      intro q hq0 hqlt hqfix
      have := congrArg (truncPair k) hqfix
      rw [feistelIter_truncate] at this
      exact hexU12.2.2 q hq0 hqlt this
    right
    refine ⟨(exactPeriod_shift (fP12 τ) (k + 1) 12 r s).1 hexU12', r, hr, ?_, ?_, ?_⟩
    · exact goodBlock4_lift τ k U (by rw [htrU]; exact hgb0)
    · apply goodBlock4_lift τ k
      rw [feistelIter_truncate]; exact hgb1
    · apply goodBlock4_lift τ k
      rw [feistelIter_truncate]; exact hgb2

/-- **THEOREM I (Universal Trigger-Independent Period-12 Lock):**
    For EVERY 2-adic trigger `τ : Nat → Bool`, EVERY bit-width `w ≥ 1`, and EVERY state
    `s ∈ (BitVec w)^2`, the Feistel network `(L, R) ↦ (R, L ^^^ fP12(τ)(R))` locks to
    exact period dividing 12: every state has exact minimal period EITHER 4 or 12,
    hence `F^{12}(s) = s` universally for all `w ≥ 1`. -/
theorem theorem_I_universal_period12_lock (τ : Nat → Bool) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      (ExactPeriod (fP12 τ) w s 4 ∨ ExactPeriod (fP12 τ) w s 12) ∧
      feistelIter (fP12 τ) w 12 s = s := by
  intro w hw
  have hinv : ∀ n (s : BitVec (n + 1) × BitVec (n + 1)), P12Inv τ (n + 1) s := by
    intro n
    induction n with
    | zero => exact p12Inv_base τ
    | succ k ih => intro s; exact p12Inv_step τ (k + 1) s (ih (truncPair (k + 1) s))
  cases w with
  | zero => omega
  | succ n =>
    intro s
    rcases hinv n s with ⟨h4, _⟩ | ⟨h12, _⟩
    · exact ⟨Or.inl h4, feistelIter_mul_of_fixed (fP12 τ) (n + 1) 4 s h4.2.1 3⟩
    · exact ⟨Or.inr h12, h12.2.1⟩

/-- Concrete Hardware Corollary Ia: `(L, R) ↦ (R, L ^^^ (R ||| (R + 1)))` satisfies
    `F^{12}(L, R) = (L, R)` for ALL bit-widths `w ≥ 1` and ALL `(L, R)`. -/
theorem corollary_Ia_hw_or_add_one (w : Nat) (hw : 1 ≤ w) (s : BitVec w × BitVec w) :
    hwFeistelIter (fun w R => R ||| (R + 1#w)) w 12 s = s := by
  rw [hwFeistelIter_eq_feistelIter _ _ hw_or_add_one_eq]
  exact (theorem_I_universal_period12_lock (fun _ => true) w hw s).2

/-- Concrete Hardware Corollary Ib: `(L, R) ↦ (R, L ^^^ (R ||| (R - 1)))` satisfies
    `F^{12}(L, R) = (L, R)` for ALL bit-widths `w ≥ 1` and ALL `(L, R)`. -/
theorem corollary_Ib_hw_or_sub_one (w : Nat) (hw : 1 ≤ w) (s : BitVec w × BitVec w) :
    hwFeistelIter (fun w R => R ||| (R - 1#w)) w 12 s = s := by
  rw [hwFeistelIter_eq_feistelIter _ _ hw_or_sub_one_eq]
  exact (theorem_I_universal_period12_lock (fun _ => false) w hw s).2

end TheoremI

/-! ## Part 7: Theorem II — Exact Period-6 Lock for `R + 1` vs Infinite Exponential
    Escape (`3 * 2^(w-1)`) for `R - 1` (`Rule (1,0,1,1)`) -/

section TheoremII
abbrev fSub1 : TriangularRoundFn := singleTriggerFn true false true true (fun _ => false)

private theorem fAdd1_step_eq (k : Nat) (R : BitVec k) :
    Aff2.feistelStep (fAdd1.d k R) (fAdd1.c k R) =
      if R = triggerPrefix (fun _ => true) k then Aff2.T_on_1011 else Aff2.J1 := by
  dsimp only [fAdd1, singleTriggerFn]
  by_cases h : R = triggerPrefix (fun _ => true) k
  · simp [h, Aff2.T_on_1011]
  · simp [h, Aff2.J1]

private theorem fSub1_step_eq (k : Nat) (R : BitVec k) :
    Aff2.feistelStep (fSub1.d k R) (fSub1.c k R) =
      if R = triggerPrefix (fun _ => false) k then Aff2.T_on_1011 else Aff2.J1 := by
  dsimp only [fSub1, singleTriggerFn]
  by_cases h : R = triggerPrefix (fun _ => false) k
  · simp [h, Aff2.T_on_1011]
  · simp [h, Aff2.J1]

/-- A 3-step block for `fAdd1`: either all 3 miss `allOnes`, or only step 0 hits `allOnes`. -/
def GoodBlock3 (k : Nat) (u : BitVec k × BitVec k) : Prop :=
  (∀ j, j < 3 → (feistelIter fAdd1 k j u).2 ≠ triggerPrefix (fun _ => true) k) ∨
  ((feistelIter fAdd1 k 0 u).2 = triggerPrefix (fun _ => true) k ∧
   (feistelIter fAdd1 k 1 u).2 ≠ triggerPrefix (fun _ => true) k ∧
   (feistelIter fAdd1 k 2 u).2 ≠ triggerPrefix (fun _ => true) k)

/-- Inductive orbit invariant for `fAdd1` (`R + 1`) at width `k ≥ 1`. -/
def Add1Inv (k : Nat) (s : BitVec k × BitVec k) : Prop :=
  (s = (triggerPrefix (fun _ => true) k, triggerPrefix (fun _ => true) k) ∧
   ExactPeriod fAdd1 k s 1) ∨
  (ExactPeriod fAdd1 k s 3 ∧ ∃ r, r < 3 ∧
    (feistelIter fAdd1 k r s).2 = triggerPrefix (fun _ => true) k ∧
    (feistelIter fAdd1 k (r + 1) s).2 ≠ triggerPrefix (fun _ => true) k ∧
    (feistelIter fAdd1 k (r + 2) s).2 ≠ triggerPrefix (fun _ => true) k) ∨
  (ExactPeriod fAdd1 k s 6 ∧ ∃ r, r < 6 ∧
    ((∀ j, j < 6 → (feistelIter fAdd1 k j (feistelIter fAdd1 k r s)).2 ≠ triggerPrefix (fun _ => true) k) ∨
     (∀ j, j < 6 → ((feistelIter fAdd1 k j (feistelIter fAdd1 k r s)).2 = triggerPrefix (fun _ => true) k ↔
        j = 0 ∨ j = 3))))

private theorem add1Inv_base_bool :
    ∀ l r : Bool,
      let s : BitVec 1 × BitVec 1 := (BitVec.cons l 0#0, BitVec.cons r 0#0)
      (s = (triggerPrefix (fun _ => true) 1, triggerPrefix (fun _ => true) 1) ∧
       feistelIter fAdd1 1 1 s = s) ∨
      (feistelIter fAdd1 1 3 s = s ∧
       feistelIter fAdd1 1 1 s ≠ s ∧
       feistelIter fAdd1 1 2 s ≠ s ∧
       ∃ sh : Fin 3,
         (feistelIter fAdd1 1 sh.val s).2 = triggerPrefix (fun _ => true) 1 ∧
         (feistelIter fAdd1 1 (sh.val + 1) s).2 ≠ triggerPrefix (fun _ => true) 1 ∧
         (feistelIter fAdd1 1 (sh.val + 2) s).2 ≠ triggerPrefix (fun _ => true) 1) := by
  decide

theorem add1Inv_base (s : BitVec 1 × BitVec 1) : Add1Inv 1 s := by
  have hs := pair1_eq_cons s
  have hb := add1Inv_base_bool (s.1.getLsbD 0) (s.2.getLsbD 0)
  rw [← hs] at hb
  rcases hb with ⟨heq, h1⟩ | ⟨h3, h1n, h2n, ⟨sh, h0, h1, h2⟩⟩
  · left; exact ⟨heq, ⟨by omega, h1, fun q hq0 hqlt => by omega⟩⟩
  · right; left
    refine ⟨⟨by omega, h3, ?_⟩, sh.val, sh.isLt, h0, h1, h2⟩
    intro q hq0 hqlt
    have : q = 1 ∨ q = 2 := by omega
    rcases this with rfl | rfl <;> assumption

theorem add1Inv_step (k : Nat) (s : BitVec (k + 1) × BitVec (k + 1))
    (ih : Add1Inv k (truncPair k s)) : Add1Inv (k + 1) s := by
  have htr : ∀ (U : BitVec (k + 1) × BitVec (k + 1)) j,
      (feistelIter fAdd1 (k + 1) j U).2.setWidth k = (feistelIter fAdd1 k j (truncPair k U)).2 :=
    fun U j => congrArg Prod.snd (feistelIter_truncate fAdd1 k j U)
  rcases ih with ⟨hfp, hex1⟩ | ⟨hex3, r, hr, h0, h1, h2⟩ | ⟨hex6, r, hr, hhits⟩
  · -- Lift fixed point `(allOnes k, allOnes k)` via `T_on_1011` → 1 fixed point + 1 unique 3-cycle
    have hmono : monodromy fAdd1 k (truncPair k s) 1 = Aff2.T_on_1011 := by
      simp only [monodromy, fAdd1_step_eq]
      have : (truncPair k s).2 = triggerPrefix (fun _ => true) k := congrArg Prod.snd hfp
      simp only [feistelIter, this, ↓reduceIte]; rfl
    cases ha : (topBitPair k s).1 <;> cases hb : (topBitPair k s).2
    · -- `(false, false)` → 3-cycle, hits `true` uniquely at step 1!
      have htop : topBitPair k s = (false, false) := Prod.ext ha hb
      have hfix3 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 3) (topBitPair k s) =
          topBitPair k s := by rw [hmono, htop]; rfl
      have hne1 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 1) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      have hne2 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 2) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      right; left
      refine ⟨⟨by omega, by simpa using (feistel_period_lift fAdd1 k 1 3 s hex1.2.1).2 hfix3, ?_⟩,
              1, by omega, ?_, ?_, ?_⟩
      · intro q hq0 hqlt hqfix
        have : q = 1 ∨ q = 2 := by omega
        rcases this with rfl | rfl
        · exact hne1 ((feistel_period_lift fAdd1 k 1 1 s hex1.2.1).1 (by simpa using hqfix))
        · exact hne2 ((feistel_period_lift fAdd1 k 1 2 s hex1.2.1).1 (by simpa using hqfix))
      · rw [eq_triggerPrefix_succ_iff, htr s 1]
        have ht1 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 1 s)
        rw [hmono, htop] at ht1
        exact ⟨by rw [feistelIter_mul_of_fixed fAdd1 k 1 (truncPair k s) hex1.2.1 1]; exact congrArg Prod.snd hfp,
               by exact ht1⟩
      · intro heq; rw [eq_triggerPrefix_succ_iff] at heq
        have ht2 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 2 s)
        have hm2 : monodromy fAdd1 k (truncPair k s) 2 = Aff2.pow Aff2.T_on_1011 2 := by
          have := monodromy_mul_of_fixed fAdd1 k 1 2 (truncPair k s) hex1.2.1
          simpa [hmono] using this
        rw [hm2, htop] at ht2
        have hb2 : (feistelIter fAdd1 (k + 1) 2 s).2.getLsbD k = false := ht2
        rw [hb2] at heq; exact absurd heq.2 (by decide)
      · intro heq; rw [eq_triggerPrefix_succ_iff] at heq
        have ht3 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 3 s)
        have hm3 : monodromy fAdd1 k (truncPair k s) 3 = Aff2.pow Aff2.T_on_1011 3 := by
          have := monodromy_mul_of_fixed fAdd1 k 1 3 (truncPair k s) hex1.2.1
          simpa [hmono] using this
        rw [hm3, htop] at ht3
        have hb3 : (feistelIter fAdd1 (k + 1) 3 s).2.getLsbD k = false := ht3
        rw [hb3] at heq; exact absurd heq.2 (by decide)
    · -- `(false, true)` → 3-cycle, hits `true` uniquely at step 0!
      have htop : topBitPair k s = (false, true) := Prod.ext ha hb
      have hfix3 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 3) (topBitPair k s) =
          topBitPair k s := by rw [hmono, htop]; rfl
      have hne1 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 1) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      have hne2 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 2) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      right; left
      refine ⟨⟨by omega, by simpa using (feistel_period_lift fAdd1 k 1 3 s hex1.2.1).2 hfix3, ?_⟩,
              0, by omega, ?_, ?_, ?_⟩
      · intro q hq0 hqlt hqfix
        have : q = 1 ∨ q = 2 := by omega
        rcases this with rfl | rfl
        · exact hne1 ((feistel_period_lift fAdd1 k 1 1 s hex1.2.1).1 (by simpa using hqfix))
        · exact hne2 ((feistel_period_lift fAdd1 k 1 2 s hex1.2.1).1 (by simpa using hqfix))
      · rw [eq_triggerPrefix_succ_iff, htr s 0]
        exact ⟨congrArg Prod.snd hfp, hb⟩
      · intro heq; rw [eq_triggerPrefix_succ_iff] at heq
        have ht1 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 1 s)
        rw [hmono, htop] at ht1
        have hb1 : (feistelIter fAdd1 (k + 1) 1 s).2.getLsbD k = false := ht1
        rw [hb1] at heq; exact absurd heq.2 (by decide)
      · intro heq; rw [eq_triggerPrefix_succ_iff] at heq
        have ht2 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 2 s)
        have hm2 : monodromy fAdd1 k (truncPair k s) 2 = Aff2.pow Aff2.T_on_1011 2 := by
          have := monodromy_mul_of_fixed fAdd1 k 1 2 (truncPair k s) hex1.2.1
          simpa [hmono] using this
        rw [hm2, htop] at ht2
        have hb2 : (feistelIter fAdd1 (k + 1) 2 s).2.getLsbD k = false := ht2
        rw [hb2] at heq; exact absurd heq.2 (by decide)
    · -- `(true, false)` → 3-cycle, hits `true` uniquely at step 2!
      have htop : topBitPair k s = (true, false) := Prod.ext ha hb
      have hfix3 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 3) (topBitPair k s) =
          topBitPair k s := by rw [hmono, htop]; rfl
      have hne1 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 1) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      have hne2 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 2) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      right; left
      refine ⟨⟨by omega, by simpa using (feistel_period_lift fAdd1 k 1 3 s hex1.2.1).2 hfix3, ?_⟩,
              2, by omega, ?_, ?_, ?_⟩
      · intro q hq0 hqlt hqfix
        have : q = 1 ∨ q = 2 := by omega
        rcases this with rfl | rfl
        · exact hne1 ((feistel_period_lift fAdd1 k 1 1 s hex1.2.1).1 (by simpa using hqfix))
        · exact hne2 ((feistel_period_lift fAdd1 k 1 2 s hex1.2.1).1 (by simpa using hqfix))
      · rw [eq_triggerPrefix_succ_iff, htr s 2]
        have ht2 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 2 s)
        have hm2 : monodromy fAdd1 k (truncPair k s) 2 = Aff2.pow Aff2.T_on_1011 2 := by
          have := monodromy_mul_of_fixed fAdd1 k 1 2 (truncPair k s) hex1.2.1
          simpa [hmono] using this
        rw [hm2, htop] at ht2
        exact ⟨by rw [feistelIter_mul_of_fixed fAdd1 k 1 (truncPair k s) hex1.2.1 2]; exact congrArg Prod.snd hfp,
               by exact ht2⟩
      · intro heq; rw [eq_triggerPrefix_succ_iff] at heq
        have ht3 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 3 s)
        have hm3 : monodromy fAdd1 k (truncPair k s) 3 = Aff2.pow Aff2.T_on_1011 3 := by
          have := monodromy_mul_of_fixed fAdd1 k 1 3 (truncPair k s) hex1.2.1
          simpa [hmono] using this
        rw [hm3, htop] at ht3
        have hb3 : (feistelIter fAdd1 (k + 1) 3 s).2.getLsbD k = false := ht3
        rw [hb3] at heq; exact absurd heq.2 (by decide)
      · intro heq; rw [eq_triggerPrefix_succ_iff] at heq
        have ht4 := congrArg Prod.snd (feistelIter_topBit fAdd1 k 4 s)
        have hm4 : monodromy fAdd1 k (truncPair k s) 4 = Aff2.pow Aff2.T_on_1011 4 := by
          have := monodromy_mul_of_fixed fAdd1 k 1 4 (truncPair k s) hex1.2.1
          simpa [hmono] using this
        rw [hm4, htop] at ht4
        have hb4 : (feistelIter fAdd1 (k + 1) 4 s).2.getLsbD k = false := ht4
        rw [hb4] at heq; exact absurd heq.2 (by decide)
    · -- `(true, true)` → fixed point `(allOnes (k+1), allOnes (k+1))`!
      have htop : topBitPair k s = (true, true) := Prod.ext ha hb
      have hfix1 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k s) 1) 1) (topBitPair k s) =
          topBitPair k s := by rw [hmono, htop]; rfl
      left
      refine ⟨?_, ⟨by omega, by simpa using (feistel_period_lift fAdd1 k 1 1 s hex1.2.1).2 hfix1,
                   fun q hq0 hqlt => by omega⟩⟩
      rcases s with ⟨sl, sr⟩
      simp only [Prod.mk.injEq]
      exact ⟨(eq_triggerPrefix_succ_iff (fun _ => true) k sl).2 ⟨congrArg Prod.fst hfp, ha⟩,
             (eq_triggerPrefix_succ_iff (fun _ => true) k sr).2 ⟨congrArg Prod.snd hfp, hb⟩⟩
  · -- Lift the unique 3-cycle via `J1^2 ∘ T_on_1011 = (I, (true, false))` → two 6-cycles!
    let U := feistelIter fAdd1 (k + 1) r s
    have htrU : truncPair k U = feistelIter fAdd1 k r (truncPair k s) :=
      feistelIter_truncate fAdd1 k r s
    have hexU3 : ExactPeriod fAdd1 k (truncPair k U) 3 := by
      rw [htrU]; exact (exactPeriod_shift fAdd1 k 3 r (truncPair k s)).2 hex3
    have hU0 : (feistelIter fAdd1 k 0 (truncPair k U)).2 = triggerPrefix (fun _ => true) k := by
      rw [htrU]; exact h0
    have hU1 : (feistelIter fAdd1 k 1 (truncPair k U)).2 ≠ triggerPrefix (fun _ => true) k := by
      rw [htrU, ← feistelIter_add, Nat.add_comm 1 r]; exact h1
    have hU2 : (feistelIter fAdd1 k 2 (truncPair k U)).2 ≠ triggerPrefix (fun _ => true) k := by
      rw [htrU, ← feistelIter_add, Nat.add_comm 2 r]; exact h2
    have hmono : monodromy fAdd1 k (truncPair k U) 3 = ⟨true, false, false, true, true, false⟩ := by
      simp only [monodromy, fAdd1_step_eq, hU0, hU1, hU2, ↓reduceIte]; rfl
    have hfix2 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k U) 3) 2) (topBitPair k U) =
        topBitPair k U := by
      rw [hmono]; rcases topBitPair k U with ⟨a, b⟩; cases a <;> cases b <;> rfl
    have hne1 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k U) 3) 1) (topBitPair k U) ≠
        topBitPair k U := by
      rw [hmono]; rcases topBitPair k U with ⟨a, b⟩; cases a <;> cases b <;> decide
    have hexU6 : ExactPeriod fAdd1 (k + 1) U 6 := by
      refine ⟨by omega, (feistel_period_lift fAdd1 k 3 2 U hexU3.2.1).2 hfix2, ?_⟩
      intro q hq0 hqlt hqfix
      have htrq : feistelIter fAdd1 k q (truncPair k U) = truncPair k U := by
        have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate] at this
      rcases exactPeriod_dvd hexU3 htrq with ⟨m, rfl⟩
      have hm1 : m = 1 := by omega
      subst hm1
      exact hne1 ((feistel_period_lift fAdd1 k 3 1 U hexU3.2.1).1 (by simpa using hqfix))
    -- Note `U` and `F^3 U` have IDENTICAL `R[k]` bit since `v1 = false`!
    have hb3 : (feistelIter fAdd1 (k + 1) 3 U).2.getLsbD k = U.2.getLsbD k := by
      have ht := congrArg Prod.snd (feistelIter_topBit fAdd1 k 3 U)
      rw [hmono] at ht
      change (topBitPair k (feistelIter fAdd1 (k + 1) 3 U)).2 = (topBitPair k U).2
      rw [ht]; rcases topBitPair k U with ⟨a, b⟩; cases a <;> cases b <;> rfl
    right; right
    refine ⟨(exactPeriod_shift fAdd1 (k + 1) 6 r s).1 hexU6, r, by omega, ?_⟩
    by_cases htop : U.2.getLsbD k = true
    · right
      intro j hj
      rw [eq_triggerPrefix_succ_iff, htr U j]
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨fun _ => Or.inl rfl, fun _ => ⟨hU0, htop⟩⟩
      · simp [hU1]
      · simp [hU2]
      · exact ⟨fun _ => Or.inr rfl, fun _ => ⟨by rw [hexU3.2.1]; exact hU0, by rw [hb3]; exact htop⟩⟩
      · have h4 : feistelIter fAdd1 k 4 (truncPair k U) = feistelIter fAdd1 k 1 (truncPair k U) := by
          rw [show (4 : Nat) = 1 + 3 from rfl, feistelIter_add, hexU3.2.1]
        simp [h4, hU1]
      · have h5 : feistelIter fAdd1 k 5 (truncPair k U) = feistelIter fAdd1 k 2 (truncPair k U) := by
          rw [show (5 : Nat) = 2 + 3 from rfl, feistelIter_add, hexU3.2.1]
        simp [h5, hU2]
    · left
      intro j hj heq
      rw [eq_triggerPrefix_succ_iff, htr U j] at heq
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · exact htop heq.2
      · exact hU1 heq.1
      · exact hU2 heq.1
      · rw [hb3] at heq; exact htop heq.2
      · have h4 : feistelIter fAdd1 k 4 (truncPair k U) = feistelIter fAdd1 k 1 (truncPair k U) := by
          rw [show (4 : Nat) = 1 + 3 from rfl, feistelIter_add, hexU3.2.1]
        rw [h4] at heq; exact hU1 heq.1
      · have h5 : feistelIter fAdd1 k 5 (truncPair k U) = feistelIter fAdd1 k 2 (truncPair k U) := by
          rw [show (5 : Nat) = 2 + 3 from rfl, feistelIter_add, hexU3.2.1]
        rw [h5] at heq; exact hU2 heq.1
  · -- Lift a 6-cycle (either 0 hits or paired `{0, 3}` hits): monodromy is ALWAYS `id`!
    let U := feistelIter fAdd1 (k + 1) r s
    have htrU : truncPair k U = feistelIter fAdd1 k r (truncPair k s) :=
      feistelIter_truncate fAdd1 k r s
    have hexU6 : ExactPeriod fAdd1 k (truncPair k U) 6 := by
      rw [htrU]; exact (exactPeriod_shift fAdd1 k 6 r (truncPair k s)).2 hex6
    rcases hhits with hnone | hpair
    · have hmono : monodromy fAdd1 k (truncPair k U) 6 = Aff2.id := by
        simp only [monodromy, fAdd1_step_eq]
        have hn : ∀ j, j < 6 → (feistelIter fAdd1 k j (truncPair k U)).2 ≠ triggerPrefix (fun _ => true) k :=
          fun j hj => by rw [htrU]; exact hnone j hj
        simp only [hn 0 (by omega), hn 1 (by omega), hn 2 (by omega),
                   hn 3 (by omega), hn 4 (by omega), hn 5 (by omega), ↓reduceIte]; rfl
      have hfix1 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k U) 6) 1) (topBitPair k U) =
          topBitPair k U := by rw [hmono]; simp [Aff2.pow, Aff2.comp_id, Aff2.apply_id]
      have hexU6' : ExactPeriod fAdd1 (k + 1) U 6 := by
        refine ⟨by omega, by simpa using (feistel_period_lift fAdd1 k 6 1 U hexU6.2.1).2 hfix1, ?_⟩
        intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
        exact hexU6.2.2 q hq0 hqlt this
      right; right
      refine ⟨(exactPeriod_shift fAdd1 (k + 1) 6 r s).1 hexU6', r, hr, Or.inl ?_⟩
      intro j hj heq
      rw [eq_triggerPrefix_succ_iff, htr U j, htrU] at heq
      exact hnone j hj heq.1
    · have hp : ∀ j, j < 6 → ((feistelIter fAdd1 k j (truncPair k U)).2 = triggerPrefix (fun _ => true) k ↔
          j = 0 ∨ j = 3) := fun j hj => by rw [htrU]; exact hpair j hj
      have h0 : (feistelIter fAdd1 k 0 (truncPair k U)).2 = triggerPrefix (fun _ => true) k := (hp 0 (by omega)).2 (Or.inl rfl)
      have h1 : (feistelIter fAdd1 k 1 (truncPair k U)).2 ≠ triggerPrefix (fun _ => true) k := by intro h; rcases (hp 1 (by omega)).1 h with h | h <;> omega
      have h2 : (feistelIter fAdd1 k 2 (truncPair k U)).2 ≠ triggerPrefix (fun _ => true) k := by intro h; rcases (hp 2 (by omega)).1 h with h | h <;> omega
      have h3 : (feistelIter fAdd1 k 3 (truncPair k U)).2 = triggerPrefix (fun _ => true) k := (hp 3 (by omega)).2 (Or.inr rfl)
      have h4 : (feistelIter fAdd1 k 4 (truncPair k U)).2 ≠ triggerPrefix (fun _ => true) k := by intro h; rcases (hp 4 (by omega)).1 h with h | h <;> omega
      have h5 : (feistelIter fAdd1 k 5 (truncPair k U)).2 ≠ triggerPrefix (fun _ => true) k := by intro h; rcases (hp 5 (by omega)).1 h with h | h <;> omega
      have hmono : monodromy fAdd1 k (truncPair k U) 6 = Aff2.id := by
        simp only [monodromy, fAdd1_step_eq, h0, h1, h2, h3, h4, h5, ↓reduceIte]; rfl
      have hmono3 : monodromy fAdd1 k (truncPair k U) 3 = ⟨true, false, false, true, true, false⟩ := by
        simp only [monodromy, fAdd1_step_eq, h0, h1, h2, ↓reduceIte]; rfl
      have hfix1 : Aff2.apply (Aff2.pow (monodromy fAdd1 k (truncPair k U) 6) 1) (topBitPair k U) =
          topBitPair k U := by rw [hmono]; simp [Aff2.pow, Aff2.comp_id, Aff2.apply_id]
      have hexU6' : ExactPeriod fAdd1 (k + 1) U 6 := by
        refine ⟨by omega, by simpa using (feistel_period_lift fAdd1 k 6 1 U hexU6.2.1).2 hfix1, ?_⟩
        intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
        exact hexU6.2.2 q hq0 hqlt this
      have hb3 : (feistelIter fAdd1 (k + 1) 3 U).2.getLsbD k = U.2.getLsbD k := by
        have ht := congrArg Prod.snd (feistelIter_topBit fAdd1 k 3 U)
        rw [hmono3] at ht
        change (topBitPair k (feistelIter fAdd1 (k + 1) 3 U)).2 = (topBitPair k U).2
        rw [ht]; rcases topBitPair k U with ⟨a, b⟩; cases a <;> cases b <;> rfl
      right; right
      refine ⟨(exactPeriod_shift fAdd1 (k + 1) 6 r s).1 hexU6', r, hr, ?_⟩
      by_cases htop : U.2.getLsbD k = true
      · right
        intro j hj
        rw [eq_triggerPrefix_succ_iff, htr U j]
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨fun _ => Or.inl rfl, fun _ => ⟨h0, htop⟩⟩
        · simp [h1]
        · simp [h2]
        · exact ⟨fun _ => Or.inr rfl, fun _ => ⟨h3, by rw [hb3]; exact htop⟩⟩
        · simp [h4]
        · simp [h5]
      · left
        intro j hj heq
        rw [eq_triggerPrefix_succ_iff, htr U j] at heq
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl
        · exact htop heq.2
        · exact h1 heq.1
        · exact h2 heq.1
        · rw [hb3] at heq; exact htop heq.2
        · exact h4 heq.1
        · exact h5 heq.1

/-- **THEOREM IIa (Exact Period-6 Lock for `R + 1`):**
    For EVERY bit-width `w ≥ 1` and EVERY state `(L, R) ∈ (BitVec w)^2`, the mixed
    XOR/ADD Feistel map `(L, R) ↦ (R, L ^^^ (R + 1))` has exact minimal period in `{1, 3, 6}`,
    and universally satisfies `F^6(L, R) = (L, R)`. -/
theorem theorem_IIa_add_one_period6_lock :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      (ExactPeriod fAdd1 w s 1 ∨ ExactPeriod fAdd1 w s 3 ∨ ExactPeriod fAdd1 w s 6) ∧
      hwFeistelIter (fun w R => R + 1#w) w 6 s = s := by
  intro w hw
  have hinv : ∀ n (s : BitVec (n + 1) × BitVec (n + 1)), Add1Inv (n + 1) s := by
    intro n
    induction n with
    | zero => exact add1Inv_base
    | succ k ih => intro s; exact add1Inv_step (k + 1) s (ih (truncPair (k + 1) s))
  cases w with
  | zero => omega
  | succ n =>
    intro s
    rw [hwFeistelIter_eq_feistelIter _ _ hw_add_one_eq]
    rcases hinv n s with ⟨_, h1⟩ | ⟨h3, _⟩ | ⟨h6, _⟩
    · exact ⟨Or.inl h1, feistelIter_mul_of_fixed fAdd1 (n + 1) 1 s h1.2.1 6⟩
    · exact ⟨Or.inr (Or.inl h3), feistelIter_mul_of_fixed fAdd1 (n + 1) 3 s h3.2.1 2⟩
    · exact ⟨Or.inr (Or.inr h6), h6.2.1⟩

/-- Inductive Exponential Escape Invariant for `fSub1` (`R - 1`) on `(0#w, 0#w)`. -/
structure Sub1ZeroInv (n : Nat) : Prop where
  exact_per : ExactPeriod fSub1 (n + 1) (0#(n + 1), 0#(n + 1)) (3 * 2 ^ n)
  hits : ∀ t, t < 3 * 2 ^ n →
    ((feistelIter fSub1 (n + 1) t (0#(n + 1), 0#(n + 1))).2 = triggerPrefix (fun _ => false) (n + 1) ↔
     t = 0 ∨ t = 3 * 2 ^ n - 1)

private theorem zero_eq_triggerPrefix_false (w : Nat) :
    0#w = triggerPrefix (fun _ => false) w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_triggerPrefix (fun _ => false) w i hi]; simp

private theorem sub1ZeroInv_base : Sub1ZeroInv 0 := by
  have hcheck :
      feistelIter fSub1 1 3 (0#1, 0#1) = (0#1, 0#1) ∧
      feistelIter fSub1 1 1 (0#1, 0#1) ≠ (0#1, 0#1) ∧
      feistelIter fSub1 1 2 (0#1, 0#1) ≠ (0#1, 0#1) ∧
      (feistelIter fSub1 1 0 (0#1, 0#1)).2 = triggerPrefix (fun _ => false) 1 ∧
      (feistelIter fSub1 1 1 (0#1, 0#1)).2 ≠ triggerPrefix (fun _ => false) 1 ∧
      (feistelIter fSub1 1 2 (0#1, 0#1)).2 = triggerPrefix (fun _ => false) 1 := by decide
  rcases hcheck with ⟨h3, h1n, h2n, hz0, hz1, hz2⟩
  refine ⟨⟨by omega, h3, ?_⟩, ?_⟩
  · intro q hq0 hqlt
    have : q = 1 ∨ q = 2 := by omega
    rcases this with rfl | rfl <;> assumption
  · intro t ht
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp [hz0]
    · simp [hz1]
    · simp [hz2]

private theorem sub1ZeroInv_step (n : Nat) (ih : Sub1ZeroInv n) : Sub1ZeroInv (n + 1) := by
  let k := n + 1
  let p := 3 * 2 ^ n
  let s0 : BitVec (k + 1) × BitVec (k + 1) := (0#(k + 1), 0#(k + 1))
  have htr0 : truncPair k s0 = (0#k, 0#k) := by
    simp [s0, truncPair]
  have htop0 : topBitPair k s0 = (false, false) := by
    simp [s0, topBitPair]
  have hp3 : 3 ≤ p := by
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    omega
  have hp2 : 3 * 2 ^ (n + 1) = 2 * p := by
    simp only [p, Nat.pow_succ]; ac_rfl
  -- Monodromy of `(0#k, 0#k)` over `p` steps: step 0 is `T_on_1011`, steps `1..p-2` are `J1`,
  -- step `p-1` is `T_on_1011`. Since `p - 2 = 3 * (2^n - 1) + 1`, `J1^(p-2) = J1`!
  have hmid : monodromy fSub1 k (feistelIter fSub1 k 1 (0#k, 0#k)) (p - 2) = Aff2.J1 := by
    have hconst : monodromy fSub1 k (feistelIter fSub1 k 1 (0#k, 0#k)) (p - 2) =
        Aff2.pow Aff2.J1 (p - 2) := by
      apply monodromy_const fSub1 k (p - 2) (feistelIter fSub1 k 1 (0#k, 0#k)) true false
      intro t ht
      rw [← feistelIter_add]
      have hne : (feistelIter fSub1 k (t + 1) (0#k, 0#k)).2 ≠ triggerPrefix (fun _ => false) k := by
        intro heq
        rcases (ih.hits (t + 1) (by omega)).1 heq with h | h <;> omega
      constructor
      · dsimp only [fSub1, singleTriggerFn]; split <;> rfl
      · dsimp only [fSub1, singleTriggerFn]
        split
        · rename_i heqb; exact absurd (beq_iff_eq.1 heqb) hne
        · rfl
    rw [hconst]
    have hq : p - 2 = 3 * (2 ^ n - 1) + 1 := by
      have h2 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega
    rw [hq, Aff2.pow_add, Aff2.J1_pow_three_mul, Aff2.id_comp]; rfl
  have hm_step0 : monodromy fSub1 k (0#k, 0#k) 1 = Aff2.T_on_1011 := by
    simp only [monodromy, fSub1_step_eq]
    have h0 : (feistelIter fSub1 k 0 (0#k, 0#k)).2 = triggerPrefix (fun _ => false) k :=
      (ih.hits 0 (by omega)).2 (Or.inl rfl)
    simp only [h0, ↓reduceIte]; rfl
  have hm_pm1 : monodromy fSub1 k (0#k, 0#k) (p - 1) = Aff2.comp Aff2.J1 Aff2.T_on_1011 := by
    have hsplit : p - 1 = (p - 2) + 1 := by omega
    rw [hsplit, monodromy_add, hmid, hm_step0]
  have hmono : monodromy fSub1 k (0#k, 0#k) p = ⟨true, false, false, true, true, true⟩ := by
    have hsplit : p = 1 + (p - 1) := by omega
    rw [hsplit, monodromy_add, hm_pm1]
    have hlast : monodromy fSub1 k (feistelIter fSub1 k (p - 1) (0#k, 0#k)) 1 = Aff2.T_on_1011 := by
      simp only [monodromy, fSub1_step_eq]
      have hl : (feistelIter fSub1 k (p - 1) (0#k, 0#k)).2 = triggerPrefix (fun _ => false) k :=
        (ih.hits (p - 1) (by omega)).2 (Or.inr rfl)
      simp only [feistelIter, hl, ↓reduceIte]; rfl
    rw [hlast]; rfl
  have hfix2 : Aff2.apply (Aff2.pow (monodromy fSub1 k (truncPair k s0) p) 2) (topBitPair k s0) =
      topBitPair k s0 := by rw [htr0, hmono, htop0]; rfl
  have hne1 : Aff2.apply (Aff2.pow (monodromy fSub1 k (truncPair k s0) p) 1) (topBitPair k s0) ≠
      topBitPair k s0 := by rw [htr0, hmono, htop0]; decide
  have hex2 : ExactPeriod fSub1 (k + 1) s0 (2 * p) := by
    refine ⟨by omega, (feistel_period_lift fSub1 k p 2 s0 (by rw [htr0]; exact ih.exact_per.2.1)).2 hfix2, ?_⟩
    intro q hq0 hqlt hqfix
    have htrq : feistelIter fSub1 k q (0#k, 0#k) = (0#k, 0#k) := by
      have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate, htr0] at this
    rcases exactPeriod_dvd ih.exact_per htrq with ⟨m, rfl⟩
    have hm1 : m = 1 := by
      rcases m with _ | m
      · simp at hq0
      · rcases m with _ | m
        · rfl
        · exfalso
          have hle : 2 * p ≤ p * (m + 2) := by
            rw [Nat.mul_comm 2 p]; exact Nat.mul_le_mul_left p (by omega)
          exact Nat.not_lt.mpr hle hqlt
    subst hm1
    exact hne1 ((feistel_period_lift fSub1 k p 1 s0 (by rw [htr0]; exact ih.exact_per.2.1)).1 (by simpa using hqfix))
  -- Exact top bits at the 4 candidate hit indices `{0, p - 1, p, 2*p - 1}`:
  have hb_pm1 : (feistelIter fSub1 (k + 1) (p - 1) s0).2.getLsbD k = true := by
    have ht := congrArg Prod.snd (feistelIter_topBit fSub1 k (p - 1) s0)
    rw [htr0, hm_pm1, htop0] at ht; exact ht
  have hb_p : (feistelIter fSub1 (k + 1) p s0).2.getLsbD k = true := by
    have ht := congrArg Prod.snd (feistelIter_topBit fSub1 k p s0)
    rw [htr0, hmono, htop0] at ht; exact ht
  have hb_2pm1 : (feistelIter fSub1 (k + 1) (2 * p - 1) s0).2.getLsbD k = false := by
    have hsp : 2 * p - 1 = (p - 1) + p := by omega
    rw [hsp]
    have ht := congrArg Prod.snd (feistelIter_topBit fSub1 k ((p - 1) + p) s0)
    rw [htr0, monodromy_add, ih.exact_per.2.1, hm_pm1, hmono, htop0] at ht
    exact ht
  refine ⟨by rw [hp2]; exact hex2, ?_⟩
  intro t ht
  rw [hp2] at ht ⊢
  rw [eq_triggerPrefix_succ_iff]
  have htrt : (feistelIter fSub1 (k + 1) t s0).2.setWidth k = (feistelIter fSub1 k t (0#k, 0#k)).2 := by
    have := congrArg Prod.snd (feistelIter_truncate fSub1 k t s0)
    rwa [htr0] at this
  rw [htrt]
  constructor
  · rintro ⟨htr_eq, htop_eq⟩
    by_cases hlt : t < p
    · rcases (ih.hits t hlt).1 htr_eq with rfl | rfl
      · exact Or.inl rfl
      · rw [hb_pm1] at htop_eq; cases htop_eq
    · have hsub : t = (t - p) + p := by omega
      have hmod : feistelIter fSub1 k t (0#k, 0#k) = feistelIter fSub1 k (t - p) (0#k, 0#k) := by
        conv => lhs; rw [hsub]
        rw [feistelIter_add, ih.exact_per.2.1]
      rw [hmod] at htr_eq
      rcases (ih.hits (t - p) (by omega)).1 htr_eq with htp | htp
      · have ht_eq : t = p := by omega
        rw [ht_eq, hb_p] at htop_eq; cases htop_eq
      · exact Or.inr (by omega)
  · rintro (rfl | rfl)
    · exact ⟨(ih.hits 0 (by omega)).2 (Or.inl rfl), by change (0#(k + 1)).getLsbD k = false; simp⟩
    · refine ⟨?_, hb_2pm1⟩
      have hsp : 2 * p - 1 = (p - 1) + p := by omega
      rw [hsp, feistelIter_add, ih.exact_per.2.1]
      exact (ih.hits (p - 1) (by omega)).2 (Or.inr rfl)

/-- **THEOREM IIb (Sharp Infinite Exponential Escape for `R - 1`):**
    Flipping ONLY `+ 1` to `- 1` in Theorem IIa shatters the constant period-6 lock into
    unbounded exponential growth: for EVERY bit-width `w ≥ 1`, the state `(0#w, 0#w)` under
    `(L, R) ↦ (R, L ^^^ (R - 1))` has EXACT minimal period `3 * 2^(w-1)`. -/
theorem theorem_IIb_sub_one_exponential_escape :
    ∀ (w : Nat), 1 ≤ w →
      hwFeistelIter (fun w R => R - 1#w) w (3 * 2 ^ (w - 1)) (0#w, 0#w) = (0#w, 0#w) ∧
      ∀ q, 0 < q → q < 3 * 2 ^ (w - 1) →
        hwFeistelIter (fun w R => R - 1#w) w q (0#w, 0#w) ≠ (0#w, 0#w) := by
  have hinv : ∀ n, Sub1ZeroInv n := by
    intro n
    induction n with
    | zero => exact sub1ZeroInv_base
    | succ n ih => exact sub1ZeroInv_step n ih
  intro w hw
  cases w with
  | zero => omega
  | succ n =>
    have hex := (hinv n).exact_per
    have heq : ∀ m, hwFeistelIter (fun w R => R - 1#w) (n + 1) m (0#(n + 1), 0#(n + 1)) =
        feistelIter fSub1 (n + 1) m (0#(n + 1), 0#(n + 1)) :=
      fun m => hwFeistelIter_eq_feistelIter _ _ hw_sub_one_eq (n + 1) m _
    simp only [Nat.add_sub_cancel]
    exact ⟨by rw [heq]; exact hex.2.1, fun q h1 h2 => by rw [heq]; exact hex.2.2 q h1 h2⟩

end TheoremII

/-! ## Part 8: Theorem III — Exact Binomial Power-of-3 Spectrum (`R &&& (-R)`) &
    Sharp `ctz(τ)` Period-Lock Phase Transition (`Rule (0,0,1,0)`) -/

section TheoremIII
private theorem fLsbGen_step_eq (τ : Nat → Bool) (k : Nat) (R : BitVec k) :
    Aff2.feistelStep ((fLsbGen τ).d k R) ((fLsbGen τ).c k R) =
      if R = triggerPrefix τ k then Aff2.J1 else Aff2.J0 := by
  dsimp only [fLsbGen, singleTriggerFn]
  by_cases h : R = triggerPrefix τ k
  · simp [h, Aff2.J1]
  · simp [h, Aff2.J0]

private theorem three_pow_odd (e : Nat) : (3 ^ e) % 2 = 1 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [Nat.pow_succ]; omega

private theorem monodromy_fLsbGen_no_hits (τ : Nat → Bool) (k n : Nat) (u : BitVec k × BitVec k)
    (hnone : ∀ t, t < n → (feistelIter (fLsbGen τ) k t u).2 ≠ triggerPrefix τ k) :
    monodromy (fLsbGen τ) k u n = Aff2.pow Aff2.J0 n := by
  apply monodromy_const (fLsbGen τ) k n u false false
  intro t ht
  have hne := hnone t ht
  constructor
  · dsimp only [fLsbGen, singleTriggerFn]
    split
    · rename_i heqb; exact absurd (beq_iff_eq.1 heqb) hne
    · rfl
  · dsimp only [fLsbGen, singleTriggerFn]; split <;> rfl

/-- Exact monodromy of an odd-length cycle with a single hit at `t = 0`: always `J1`. -/
private theorem monodromy_fLsbGen_one_hit (τ : Nat → Bool) (k p : Nat) (u : BitVec k × BitVec k)
    (hodd : p % 2 = 1)
    (h0 : (feistelIter (fLsbGen τ) k 0 u).2 = triggerPrefix τ k)
    (hrest : ∀ t, 0 < t → t < p → (feistelIter (fLsbGen τ) k t u).2 ≠ triggerPrefix τ k) :
    monodromy (fLsbGen τ) k u p = Aff2.J1 := by
  have hp1 : p = (p - 1) + 1 := by omega
  rw [hp1, monodromy_add]
  have hm0 : monodromy (fLsbGen τ) k u 1 = Aff2.J1 := by
    simp only [monodromy, fLsbGen_step_eq, h0, ↓reduceIte]; rfl
  have hmrest : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k 1 u) (p - 1) =
      Aff2.pow Aff2.J0 (p - 1) := by
    apply monodromy_fLsbGen_no_hits
    intro t ht
    rw [← feistelIter_add]
    exact hrest (t + 1) (by omega) (by omega)
  have heven : p - 1 = 2 * ((p - 1) / 2) := by omega
  rw [hm0, hmrest, heven, Aff2.J0_pow_two_mul, Aff2.id_comp]

/-- Inductive invariant for the prefix-zero regime (`∀ j < k, τ j = false`):
    every state has exact period `3^e` (`e ≤ k`) and hits `triggerPrefix τ k` uniquely. -/
structure LsbZeroInv (τ : Nat → Bool) (k : Nat) (s : BitVec k × BitVec k) : Type where
  exp : Nat
  exp_le : exp ≤ k
  exact_per : ExactPeriod (fLsbGen τ) k s (3 ^ exp)
  uniq_hit : ∃ r, r < 3 ^ exp ∧ ∀ t, t < 3 ^ exp →
    ((feistelIter (fLsbGen τ) k t s).2 = triggerPrefix τ k ↔ t = r)

def lsbZeroInv_base (τ : Nat → Bool) (s : BitVec 0 × BitVec 0) : LsbZeroInv τ 0 s :=
  ⟨0, Nat.le_refl 0, ⟨by omega, by
      rcases s with ⟨l, r⟩
      simp only [feistelIter, feistelStepF, Prod.mk.injEq]
      exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
      fun q h1 h2 => by omega⟩,
   0, by omega, by
      intro t ht
      have ht0 : t = 0 := by omega
      subst ht0
      exact ⟨fun _ => rfl, fun _ => Subsingleton.elim _ _⟩⟩

def lsbZeroInv_step (τ : Nat → Bool) (k : Nat) (hτk : τ k = false)
    (s : BitVec (k + 1) × BitVec (k + 1)) (ih : LsbZeroInv τ k (truncPair k s)) :
    LsbZeroInv τ (k + 1) s := by
  let p := 3 ^ ih.exp
  let stays : Bool := (feistelIter (fLsbGen τ) (k + 1) p s == s)
  refine ⟨if stays then ih.exp else ih.exp + 1, ?_, ?_, ?_⟩
  · cases stays
    · exact Nat.succ_le_succ ih.exp_le
    · exact Nat.le_succ_of_le ih.exp_le
  all_goals
    rcases ih.uniq_hit with ⟨r, hr, huniq⟩
    let U := feistelIter (fLsbGen τ) (k + 1) r s
    have htrU : truncPair k U = feistelIter (fLsbGen τ) k r (truncPair k s) :=
      feistelIter_truncate (fLsbGen τ) k r s
    have hexU : ExactPeriod (fLsbGen τ) k (truncPair k U) p := by
      rw [htrU]; exact (exactPeriod_shift (fLsbGen τ) k p r (truncPair k s)).2 ih.exact_per
    have hU_hits : ∀ t, t < p → ((feistelIter (fLsbGen τ) k t (truncPair k U)).2 = triggerPrefix τ k ↔ t = 0) := by
      intro t ht
      rw [htrU, ← feistelIter_add, feistelIter_eq_mod (fLsbGen τ) k p (t + r) (truncPair k s) ih.exact_per.2.1]
      rw [huniq ((t + r) % p) (Nat.mod_lt _ ih.exact_per.1)]
      constructor
      · intro heq
        by_cases hsum : t + r < p
        · rw [Nat.mod_eq_of_lt hsum] at heq; omega
        · have hlt2 : t + r - p < p := by omega
          have hmeq : (t + r) % p = t + r - p := by
            have : t + r = (t + r - p) + 1 * p := by omega
            conv => lhs; rw [this]
            rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
          rw [hmeq] at heq; omega
      · rintro rfl; rw [Nat.zero_add, Nat.mod_eq_of_lt hr]
    have hmono : monodromy (fLsbGen τ) k (truncPair k U) p = Aff2.J1 :=
      monodromy_fLsbGen_one_hit τ k p (truncPair k U) (three_pow_odd ih.exp)
        ((hU_hits 0 ih.exact_per.1).2 rfl)
        (fun t ht0 htp heq => by have := (hU_hits t htp).1 heq; omega)
    have htr_j : ∀ j, (feistelIter (fLsbGen τ) (k + 1) j U).2.setWidth k =
        (feistelIter (fLsbGen τ) k j (truncPair k U)).2 :=
      fun j => congrArg Prod.snd (feistelIter_truncate (fLsbGen τ) k j U)
    have hstays_iff : stays = true ↔ topBitPair k U = (false, false) := by
      simp only [stays, beq_iff_eq]
      have hsh : feistelIter (fLsbGen τ) (k + 1) p s = s ↔ feistelIter (fLsbGen τ) (k + 1) p U = U := by
        have hcomm : feistelIter (fLsbGen τ) (k + 1) p U =
            feistelIter (fLsbGen τ) (k + 1) r (feistelIter (fLsbGen τ) (k + 1) p s) := by
          simp only [U, ← feistelIter_add, Nat.add_comm]
        constructor
        · intro h; rw [hcomm, h]
        · intro h; apply feistelIter_inj (fLsbGen τ) (k + 1) r; rw [← hcomm]; exact h
      rw [hsh]
      have hpl := feistel_period_lift (fLsbGen τ) k p 1 U hexU.2.1
      simp only [Nat.one_mul, hmono] at hpl
      rw [hpl]
      rcases topBitPair k U with ⟨a, b⟩
      cases a <;> cases b <;> decide
    cases ha : (topBitPair k U).1 <;> cases hb : (topBitPair k U).2
    · have htop : topBitPair k U = (false, false) := Prod.ext ha hb
      have hst : stays = true := hstays_iff.2 htop
      simp only [hst, ↓reduceIte]
      have hfix1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) p) 1) (topBitPair k U) =
          topBitPair k U := by rw [hmono, htop]; rfl
      have hexU' : ExactPeriod (fLsbGen τ) (k + 1) U p := by
        refine ⟨ih.exact_per.1, by simpa using (feistel_period_lift (fLsbGen τ) k p 1 U hexU.2.1).2 hfix1, ?_⟩
        intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
        exact hexU.2.2 q hq0 hqlt this
      first
      | exact (exactPeriod_shift (fLsbGen τ) (k + 1) p r s).1 hexU'
      | (refine ⟨r, hr, fun t ht => ?_⟩
         have htr_s : (feistelIter (fLsbGen τ) (k + 1) t s).2.setWidth k =
             (feistelIter (fLsbGen τ) k t (truncPair k s)).2 :=
           congrArg Prod.snd (feistelIter_truncate (fLsbGen τ) k t s)
         rw [eq_triggerPrefix_succ_iff, htr_s]
         constructor
         · rintro ⟨htr_eq, _⟩; exact (huniq t ht).1 htr_eq
         · intro hte; rw [hte]
           exact ⟨(huniq r hr).2 rfl, by rw [hτk]; exact hb⟩)
    all_goals
      have htop : topBitPair k U = (_, _) := Prod.ext ha hb
      have hst : stays = false := by
        cases hs : stays
        · rfl
        · have := hstays_iff.1 hs; rw [htop] at this; cases this
      simp only [hst, Bool.false_eq_true, ↓reduceIte]
      have hfix3 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) p) 3) (topBitPair k U) =
          topBitPair k U := by rw [hmono, htop]; rfl
      have hne1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) p) 1) (topBitPair k U) ≠
          topBitPair k U := by rw [hmono, htop]; decide
      have hne2 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) p) 2) (topBitPair k U) ≠
          topBitPair k U := by rw [hmono, htop]; decide
      have hp0 : 0 < p := ih.exact_per.1
      have hexU' : ExactPeriod (fLsbGen τ) (k + 1) U (3 * p) := by
        refine ⟨by omega, (feistel_period_lift (fLsbGen τ) k p 3 U hexU.2.1).2 hfix3, ?_⟩
        intro q hq0 hqlt hqfix
        have htrq : feistelIter (fLsbGen τ) k q (truncPair k U) = truncPair k U := by
          have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate] at this
        rcases exactPeriod_dvd hexU htrq with ⟨m, rfl⟩
        have hm : m = 1 ∨ m = 2 := by
          rcases m with _ | m
          · simp at hq0
          · rcases m with _ | m
            · exact Or.inl rfl
            · rcases m with _ | m
              · exact Or.inr rfl
              · exfalso
                have hle : 3 * p ≤ p * (m + 3) := by
                  rw [Nat.mul_comm 3 p]; exact Nat.mul_le_mul_left p (by omega)
                exact Nat.not_lt.mpr hle hqlt
        rcases hm with rfl | rfl
        · exact hne1 ((feistel_period_lift (fLsbGen τ) k p 1 U hexU.2.1).1 (by simpa using hqfix))
        · exact hne2 ((feistel_period_lift (fLsbGen τ) k p 2 U hexU.2.1).1 (by simpa [Nat.mul_comm] using hqfix))
      have hp3 : 3 ^ (ih.exp + 1) = 3 * p := by simp only [p, Nat.pow_succ, Nat.mul_comm]
      have hex_s' : ExactPeriod (fLsbGen τ) (k + 1) s (3 * p) :=
        (exactPeriod_shift (fLsbGen τ) (k + 1) (3 * p) r s).1 hexU'
      first
      | (rw [hp3]; exact hex_s')
      | (have hb0 : (feistelIter (fLsbGen τ) (k + 1) 0 U).2.getLsbD k = (topBitPair k U).2 := rfl
         have hb1 : (feistelIter (fLsbGen τ) (k + 1) p U).2.getLsbD k = (Aff2.apply Aff2.J1 (topBitPair k U)).2 := by
           have := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) k p U); rwa [hmono] at this
         have hb2 : (feistelIter (fLsbGen τ) (k + 1) (2 * p) U).2.getLsbD k =
             (Aff2.apply (Aff2.pow Aff2.J1 2) (topBitPair k U)).2 := by
           have := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) k (2 * p) U)
           rwa [monodromy_mul_of_fixed (fLsbGen τ) k p 2 (truncPair k U) hexU.2.1, hmono] at this
         have hU_uniq : ∃ j0, j0 < 3 * p ∧ ∀ t, t < 3 * p →
             ((feistelIter (fLsbGen τ) (k + 1) t U).2 = triggerPrefix τ (k + 1) ↔ t = j0) := by
           have hcand : ∀ t, t < 3 * p →
               (feistelIter (fLsbGen τ) k t (truncPair k U)).2 = triggerPrefix τ k →
               t = 0 ∨ t = p ∨ t = 2 * p := by
             intro t ht hhit
             rw [feistelIter_eq_mod (fLsbGen τ) k p t (truncPair k U) hexU.2.1] at hhit
             have hm0 : t % p = 0 := (hU_hits (t % p) (Nat.mod_lt _ hp0)).1 hhit
             have hdiv : t = p * (t / p) := by have := Nat.div_add_mod t p; omega
             have hlt3 : t / p < 3 := by
               by_cases h3 : t / p < 3
               · exact h3
               · exfalso
                 have hle := Nat.mul_le_mul_left p (Nat.le_of_not_lt h3)
                 rw [← hdiv, Nat.mul_comm p 3] at hle
                 exact Nat.not_lt.mpr hle ht
             match hq : t / p with
             | 0 => left; rw [hdiv, hq]; simp
             | 1 => right; left; rw [hdiv, hq]; simp
             | 2 => right; right; rw [hdiv, hq, Nat.mul_comm]
             | n + 3 => exfalso; omega
           rw [htop] at hb0 hb1 hb2
           first
           | (refine ⟨2 * p, by omega, fun t ht => ?_⟩
              rw [eq_triggerPrefix_succ_iff, htr_j t, hτk]
              constructor
              · rintro ⟨htr_e, htop_e⟩
                rcases hcand t ht htr_e with rfl | rfl | rfl
                · rw [hb0] at htop_e; cases htop_e
                · rw [hb1] at htop_e; cases htop_e
                · rfl
              · intro hte; rw [hte]
                exact ⟨by rw [feistelIter_mul_of_fixed (fLsbGen τ) k p (truncPair k U) hexU.2.1 2]; exact (hU_hits 0 hp0).2 rfl,
                       hb2⟩)
           | (refine ⟨0, by omega, fun t ht => ?_⟩
              rw [eq_triggerPrefix_succ_iff, htr_j t, hτk]
              constructor
              · rintro ⟨htr_e, htop_e⟩
                rcases hcand t ht htr_e with rfl | rfl | rfl
                · rfl
                · rw [hb1] at htop_e; cases htop_e
                · rw [hb2] at htop_e; cases htop_e
              · intro hte; rw [hte]
                exact ⟨(hU_hits 0 hp0).2 rfl, hb0⟩)
           | (refine ⟨p, by omega, fun t ht => ?_⟩
              rw [eq_triggerPrefix_succ_iff, htr_j t, hτk]
              constructor
              · rintro ⟨htr_e, htop_e⟩
                rcases hcand t ht htr_e with rfl | rfl | rfl
                · rw [hb0] at htop_e; cases htop_e
                · rfl
                · rw [hb2] at htop_e; cases htop_e
              · intro hte; rw [hte]
                exact ⟨by rw [hexU.2.1]; exact (hU_hits 0 hp0).2 rfl, hb1⟩)
         rcases hU_uniq with ⟨j0, hj0, hUj⟩
         rw [hp3]
         refine ⟨(j0 + r) % (3 * p), Nat.mod_lt _ (by omega), fun t ht => ?_⟩
         let u_idx := (t + (3 * p - r)) % (3 * p)
         have hshift_eq : feistelIter (fLsbGen τ) (k + 1) t s = feistelIter (fLsbGen τ) (k + 1) u_idx U := by
           simp only [U, ← feistelIter_add]
           rw [feistelIter_eq_mod (fLsbGen τ) (k + 1) (3 * p) (u_idx + r) s hex_s'.2.1]
           have hmod : (u_idx + r) % (3 * p) = t := by
             have h1 : (u_idx + r) % (3 * p) = (t + (3 * p - r) + r) % (3 * p) := by
               simp only [u_idx]; rw [Nat.mod_add_mod]
             rw [h1]
             have h2 : t + (3 * p - r) + r = t + 1 * (3 * p) := by omega
             rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
           rw [hmod]
         rw [hshift_eq, hUj u_idx (Nat.mod_lt _ (by omega))]
         constructor
         · intro hu
           have h1 : (j0 + r) % (3 * p) = (u_idx + r) % (3 * p) := by rw [hu]
           rw [h1]
           have h2 : (u_idx + r) % (3 * p) = (t + (3 * p - r) + r) % (3 * p) := by
             simp only [u_idx]; rw [Nat.mod_add_mod]
           rw [h2]
           have h3 : t + (3 * p - r) + r = t + 1 * (3 * p) := by omega
           rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
         · intro hte
           simp only [u_idx]
           rw [hte, Nat.mod_add_mod]
           have h3 : j0 + r + (3 * p - r) = j0 + 1 * (3 * p) := by omega
           rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj0])

/-- Exact prefix-zero lift: for any `τ` with `∀ j < w, τ j = false`, EVERY state at width `w`
    satisfies `LsbZeroInv τ w s`. -/
def lsbZeroInv_all (τ : Nat → Bool) :
    ∀ (w : Nat), (∀ j, j < w → τ j = false) → ∀ (s : BitVec w × BitVec w), LsbZeroInv τ w s
  | 0, _, s => lsbZeroInv_base τ s
  | k + 1, hτ, s =>
    lsbZeroInv_step τ k (hτ k (Nat.lt_succ_self k)) s
      (lsbZeroInv_all τ k (fun j hj => hτ j (Nat.lt_succ_of_lt hj)) (truncPair k s))

theorem length_allPairs (w : Nat) : (allPairs w).length = 4 ^ w := by
  induction w with
  | zero => rfl
  | succ k ih =>
    simp only [allPairs, List.length_flatMap]
    have hsum : ∀ (xs : List (BitVec k × BitVec k)),
        (xs.map (fun x => (liftFour x).length)).sum = 4 * xs.length := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ihx =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ihx]
        have h4 : (liftFour x).length = 4 := rfl
        rw [h4]; omega
    rw [hsum, ih, Nat.pow_succ, Nat.mul_comm]

private theorem bv_cons_head_ne {k : Nat} (z : BitVec k) :
    BitVec.cons false z ≠ BitVec.cons true z := by
  intro h
  have hget := congrArg (fun v => v.getLsbD k) h
  rw [BitVec.getLsbD_cons, BitVec.getLsbD_cons] at hget
  simp at hget

private theorem bv_eq_cons_trunc {k : Nat} (x : BitVec (k + 1)) :
    x = BitVec.cons (x.getLsbD k) (x.setWidth k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_cons]
  by_cases hik : i = k
  · subst hik; simp
  · have hlt : i < k := by omega
    simp [hik, hlt]

/-- Completeness of `allPairs w`: EVERY state in `(BitVec w)^2` appears in `allPairs w`. -/
theorem mem_allPairs : ∀ (w : Nat) (s : BitVec w × BitVec w), s ∈ allPairs w := by
  intro w
  induction w with
  | zero =>
    intro ⟨l, r⟩
    have hl : l = 0#0 := Subsingleton.elim _ _
    have hr : r = 0#0 := Subsingleton.elim _ _
    subst hl; subst hr; simp [allPairs]
  | succ k ih =>
    intro s
    simp only [allPairs, List.mem_flatMap]
    refine ⟨truncPair k s, ih (truncPair k s), ?_⟩
    have hs : s = (BitVec.cons (s.1.getLsbD k) (s.1.setWidth k),
                   BitVec.cons (s.2.getLsbD k) (s.2.setWidth k)) :=
      Prod.ext (bv_eq_cons_trunc s.1) (bv_eq_cons_trunc s.2)
    simp only [truncPair, liftFour, List.mem_cons, List.not_mem_nil, or_false]
    cases ha : s.1.getLsbD k <;> cases hb : s.2.getLsbD k <;> rw [ha, hb] at hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr hs))

/-- Duplicate-freeness of `allPairs w`: every state in `(BitVec w)^2` appears EXACTLY ONCE. -/
theorem nodup_allPairs : ∀ (w : Nat), (allPairs w).Nodup := by
  intro w
  induction w with
  | zero => simp [allPairs]
  | succ k ih =>
    simp only [allPairs]
    have htrunc_cons : ∀ (b : Bool) (v : BitVec k), (BitVec.cons b v).setWidth k = v := by
      intro b v
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, BitVec.getLsbD_cons]
      simp [Nat.ne_of_lt hi]
    have htrunc_lift : ∀ (z : BitVec k × BitVec k) (u : BitVec (k + 1) × BitVec (k + 1)),
        u ∈ liftFour z → truncPair k u = z := by
      intro ⟨zl, zr⟩ u hz
      simp only [liftFour, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> simp [truncPair, htrunc_cons]
    have hflat : ∀ (xs : List (BitVec k × BitVec k)), xs.Nodup → (xs.flatMap liftFour).Nodup := by
      intro xs hnd
      induction xs with
      | nil => simp
      | cons x xs ihx =>
        rcases List.nodup_cons.1 hnd with ⟨hnotmem, hndxs⟩
        rw [List.flatMap_cons, List.nodup_append]
        refine ⟨?_, ihx hndxs, ?_⟩
        · simp [liftFour, bv_cons_head_ne, Ne.symm]
        · intro u hu1 v hv2 heq
          subst heq
          rcases List.mem_flatMap.1 hv2 with ⟨y, hy, huy⟩
          have hxy : x = y := by rw [← htrunc_lift x u hu1, htrunc_lift y u huy]
          exact hnotmem (hxy ▸ hy)
    exact hflat (allPairs k) ih

theorem isPeriod3Pow_iff (w j : Nat) (s : BitVec w × BitVec w) :
    isPeriod3Pow w j s = true ↔ ExactPeriod fLsb w s (3 ^ j) := by
  have hinv := lsbZeroInv_all (fun _ => false) w (fun _ _ => rfl) s
  have hex := hinv.exact_per
  have hpow_dvd : ∀ a b, 3 ^ a ∣ 3 ^ b ↔ a ≤ b := by
    intro a b
    constructor
    · intro hdvd
      by_cases hle : a ≤ b
      · exact hle
      · exfalso
        have hgt : b < a := Nat.lt_of_not_ge hle
        have hlt : 3 ^ b < 3 ^ a := Nat.pow_lt_pow_right (by omega) hgt
        have hle2 : 3 ^ a ≤ 3 ^ b := Nat.le_of_dvd (Nat.pow_pos (by omega)) hdvd
        omega
    · intro hle
      refine ⟨3 ^ (b - a), ?_⟩
      rw [← Nat.pow_add, Nat.add_sub_of_le hle]
  constructor
  · intro hb
    cases j with
    | zero =>
      simp only [isPeriod3Pow, Bool.and_true, beq_iff_eq] at hb
      have hdvd : 3 ^ hinv.exp ∣ 3 ^ 0 := exactPeriod_dvd hex hb
      have he0 : hinv.exp = 0 := Nat.eq_zero_of_le_zero ((hpow_dvd hinv.exp 0).1 hdvd)
      rw [← he0]; exact hex
    | succ j' =>
      simp only [isPeriod3Pow, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hb
      have hdvd : 3 ^ hinv.exp ∣ 3 ^ (j' + 1) := exactPeriod_dvd hex hb.1
      have hle : hinv.exp ≤ j' + 1 := (hpow_dvd hinv.exp (j' + 1)).1 hdvd
      have hne : ¬(hinv.exp ≤ j') := by
        intro hle'
        rcases (hpow_dvd hinv.exp j').2 hle' with ⟨m, hm⟩
        have hfix : feistelIter fLsb w (3 ^ j') s = s := by
          rw [hm, Nat.mul_comm]
          exact feistelIter_mul_of_fixed fLsb w (3 ^ hinv.exp) s hex.2.1 m
        exact hb.2 hfix
      have heq : hinv.exp = j' + 1 := by omega
      rw [← heq]; exact hex
  · intro hexj
    cases j with
    | zero =>
      simp only [isPeriod3Pow, Bool.and_true, beq_iff_eq]
      exact hexj.2.1
    | succ j' =>
      simp only [isPeriod3Pow, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        beq_eq_false_iff_ne]
      refine ⟨hexj.2.1, hexj.2.2 (3 ^ j') (Nat.pow_pos (by omega)) (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self j'))⟩

/-- Exact monodromy of `fLsb` on ANY state `s` over its exact period `3^e` is in `{J1, J1^2}`
    (so among the 4 lifts in `liftFour s`, EXACTLY 1 keeps period `3^e` and 3 triple to `3^(e+1)`!). -/
private theorem monodromy_fLsb_order3 (k : Nat) (s : BitVec k × BitVec k)
    (inv : LsbZeroInv (fun _ => false) k s) :
    monodromy fLsb k s (3 ^ inv.exp) = Aff2.J1 ∨
    monodromy fLsb k s (3 ^ inv.exp) = Aff2.comp Aff2.J1 Aff2.J1 := by
  let p := 3 ^ inv.exp
  rcases inv.uniq_hit with ⟨r, hr, huniq⟩
  have h1 : monodromy fLsb k s r = Aff2.pow Aff2.J0 r := by
    apply monodromy_fLsbGen_no_hits
    intro t ht heq
    have := (huniq t (by omega)).1 heq; omega
  have h2 : monodromy fLsb k (feistelIter fLsb k r s) 1 = Aff2.J1 := by
    simp only [monodromy, fLsb, fLsbGen_step_eq]
    have hhit : (feistelIter fLsb k 0 (feistelIter fLsb k r s)).2 = triggerPrefix (fun _ => false) k :=
      (huniq r hr).2 rfl
    simp only [hhit, ↓reduceIte]; rfl
  have h3 : monodromy fLsb k (feistelIter fLsb k (r + 1) s) (p - r - 1) = Aff2.pow Aff2.J0 (p - r - 1) := by
    apply monodromy_fLsbGen_no_hits
    intro t ht heq
    rw [← feistelIter_add] at heq
    have := (huniq (t + (r + 1)) (by omega)).1 heq; omega
  have hsplit : p = (p - r - 1) + (1 + r) := by omega
  have hcomp : monodromy fLsb k s p =
      Aff2.comp (Aff2.pow Aff2.J0 (p - r - 1)) (Aff2.comp Aff2.J1 (Aff2.pow Aff2.J0 r)) := by
    conv => lhs; rw [hsplit]
    rw [monodromy_add, monodromy_add, Nat.add_comm 1 r, h3, h2, h1]
  rw [hcomp]
  have hodd : p % 2 = 1 := three_pow_odd inv.exp
  by_cases hre : r % 2 = 0
  · have hja : Aff2.pow Aff2.J0 r = Aff2.id := by
      rw [show r = 2 * (r / 2) by omega, Aff2.J0_pow_two_mul]
    have hjb : Aff2.pow Aff2.J0 (p - r - 1) = Aff2.id := by
      rw [show p - r - 1 = 2 * ((p - r - 1) / 2) by omega, Aff2.J0_pow_two_mul]
    rw [hja, hjb, Aff2.comp_id, Aff2.id_comp]
    exact Or.inl rfl
  · have hja : Aff2.pow Aff2.J0 r = Aff2.J0 := by
      rw [show r = 2 * (r / 2) + 1 by omega, Aff2.J0_pow_two_mul_succ]
    have hjb : Aff2.pow Aff2.J0 (p - r - 1) = Aff2.J0 := by
      rw [show p - r - 1 = 2 * ((p - r - 1) / 2) + 1 by omega, Aff2.J0_pow_two_mul_succ]
    rw [hja, hjb]
    exact Or.inr rfl

private theorem count_liftFour_fLsb (k j : Nat) (s : BitVec k × BitVec k) :
    ((liftFour s).filter (isPeriod3Pow (k + 1) j)).length =
      (if isPeriod3Pow k j s then 1 else 0) +
      (match j with
       | 0 => 0
       | j' + 1 => if isPeriod3Pow k j' s then 3 else 0) := by
  have inv := lsbZeroInv_all (fun _ => false) k (fun _ _ => rfl) s
  have hmono := monodromy_fLsb_order3 k s inv
  let p := 3 ^ inv.exp
  -- For each of the 4 lifts `(a, b)`, exact period is `3^inv.exp` iff `(a, b) = (false, false)`,
  -- else `3^(inv.exp + 1)`!
  have hlift_ex : ∀ a b : Bool,
      let u : BitVec (k + 1) × BitVec (k + 1) := (BitVec.cons a s.1, BitVec.cons b s.2)
      ExactPeriod fLsb (k + 1) u (if (a = false ∧ b = false) then 3 ^ inv.exp else 3 ^ (inv.exp + 1)) := by
    intro a b
    let u : BitVec (k + 1) × BitVec (k + 1) := (BitVec.cons a s.1, BitVec.cons b s.2)
    have htr : truncPair k u = s := by
      rcases s with ⟨sl, sr⟩
      simp only [u, truncPair, Prod.mk.injEq]
      constructor <;> (apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, BitVec.getLsbD_cons]; simp [Nat.ne_of_lt hi])
    have htop : topBitPair k u = (a, b) := by
      simp only [u, topBitPair, BitVec.getLsbD_cons, ↓reduceIte]
    have hp3 : 3 ^ (inv.exp + 1) = 3 * p := by simp only [p, Nat.pow_succ, Nat.mul_comm]
    cases a <;> cases b
    · simp only [and_self, ↓reduceIte]
      have hfix1 : Aff2.apply (Aff2.pow (monodromy fLsb k (truncPair k u) p) 1) (topBitPair k u) =
          topBitPair k u := by
        rw [htr, htop]; rcases hmono with h | h <;> rw [h] <;> rfl
      refine ⟨inv.exact_per.1, by simpa using (feistel_period_lift fLsb k p 1 u (by rw [htr]; exact inv.exact_per.2.1)).2 hfix1, ?_⟩
      intro q hq0 hqlt hqfix
      have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate, htr] at this
      exact inv.exact_per.2.2 q hq0 hqlt this
    all_goals
      rw [hp3]
      change ExactPeriod fLsb (k + 1) u (3 * p)
      have hfix3 : Aff2.apply (Aff2.pow (monodromy fLsb k (truncPair k u) p) 3) (topBitPair k u) =
          topBitPair k u := by
        rw [htr, htop]; rcases hmono with h | h <;> rw [h] <;> rfl
      have hne1 : Aff2.apply (Aff2.pow (monodromy fLsb k (truncPair k u) p) 1) (topBitPair k u) ≠
          topBitPair k u := by
        rw [htr, htop]; rcases hmono with h | h <;> rw [h] <;> decide
      have hne2 : Aff2.apply (Aff2.pow (monodromy fLsb k (truncPair k u) p) 2) (topBitPair k u) ≠
          topBitPair k u := by
        rw [htr, htop]; rcases hmono with h | h <;> rw [h] <;> decide
      have hp0 : 0 < p := inv.exact_per.1
      refine ⟨Nat.mul_pos (by omega) hp0, (feistel_period_lift fLsb k p 3 u (by rw [htr]; exact inv.exact_per.2.1)).2 hfix3, ?_⟩
      intro q hq0 hqlt hqfix
      have htrq : feistelIter fLsb k q s = s := by
        have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate, htr] at this
      rcases exactPeriod_dvd inv.exact_per htrq with ⟨m, rfl⟩
      have hm : m = 1 ∨ m = 2 := by
        rcases m with _ | m
        · simp at hq0
        · rcases m with _ | m
          · exact Or.inl rfl
          · rcases m with _ | m
            · exact Or.inr rfl
            · exfalso
              have hle : 3 * p ≤ p * (m + 3) := by
                rw [Nat.mul_comm 3 p]; exact Nat.mul_le_mul_left p (by omega)
              exact Nat.not_lt.mpr hle hqlt
      rcases hm with rfl | rfl
      · exact hne1 ((feistel_period_lift fLsb k p 1 u (by rw [htr]; exact inv.exact_per.2.1)).1 (by simpa using hqfix))
      · exact hne2 ((feistel_period_lift fLsb k p 2 u (by rw [htr]; exact inv.exact_per.2.1)).1 (by simpa [Nat.mul_comm] using hqfix))
  have hex_uniq : ∀ {w p1 p2} {x : BitVec w × BitVec w},
      ExactPeriod fLsb w x p1 → ExactPeriod fLsb w x p2 → p1 = p2 := by
    intro w p1 p2 x h1 h2
    have d1 := exactPeriod_dvd h1 h2.2.1
    have d2 := exactPeriod_dvd h2 h1.2.1
    exact Nat.dvd_antisymm d1 d2
  have hpow_inj : ∀ a b, 3 ^ a = 3 ^ b → a = b := by
    intro a b h
    by_cases hlt : a < b
    · exfalso; exact Nat.ne_of_lt (Nat.pow_lt_pow_right (by omega) hlt) h
    · by_cases hgt : b < a
      · exfalso; exact Nat.ne_of_gt (Nat.pow_lt_pow_right (by omega) hgt) h
      · omega
  have his_s : ∀ m, isPeriod3Pow k m s = decide (m = inv.exp) := by
    intro m
    cases hb : decide (m = inv.exp)
    · simp only [decide_eq_false_iff_not] at hb
      cases hpm : isPeriod3Pow k m s
      · rfl
      · exfalso; apply hb
        exact hpow_inj m inv.exp (hex_uniq ((isPeriod3Pow_iff k m s).1 hpm) inv.exact_per)
    · simp only [decide_eq_true_eq] at hb
      rw [hb]
      exact (isPeriod3Pow_iff k inv.exp s).2 inv.exact_per
  have his_lift : ∀ a b : Bool,
      isPeriod3Pow (k + 1) j (BitVec.cons a s.1, BitVec.cons b s.2) =
        decide (j = if (a = false ∧ b = false) then inv.exp else inv.exp + 1) := by
    intro a b
    have hexab := hlift_ex a b
    let tgt := if (a = false ∧ b = false) then inv.exp else inv.exp + 1
    have hexab' : ExactPeriod fLsb (k + 1) (BitVec.cons a s.1, BitVec.cons b s.2) (3 ^ tgt) := by
      cases a <;> cases b <;> simpa [tgt] using hexab
    cases hb : decide (j = tgt)
    · simp only [decide_eq_false_iff_not] at hb
      cases hpm : isPeriod3Pow (k + 1) j (BitVec.cons a s.1, BitVec.cons b s.2)
      · rfl
      · exfalso; apply hb
        exact hpow_inj j tgt (hex_uniq ((isPeriod3Pow_iff (k + 1) j _).1 hpm) hexab')
    · simp only [decide_eq_true_eq] at hb
      rw [hb]
      exact (isPeriod3Pow_iff (k + 1) tgt _).2 hexab'
  simp only [liftFour, List.filter_cons, List.filter_nil, his_lift, his_s]
  cases j with
  | zero =>
    by_cases h0 : 0 = inv.exp
    · rw [← h0]; rfl
    · simp [h0]
  | succ j' =>
    by_cases h1 : j' + 1 = inv.exp
    · have h2 : j' ≠ inv.exp := by omega
      simp [h1, h2]
    · by_cases h2 : j' = inv.exp
      · simp [h2]
      · simp [h1, h2]

private theorem sum_filter_flatMap {α β : Type} (xs : List α) (g : α → List β) (p : β → Bool) :
    ((xs.flatMap g).filter p).length = (xs.map (fun x => ((g x).filter p).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.flatMap_cons, List.filter_append, List.length_append, ih]

private theorem count_eq_sum_ite {α : Type} (xs : List α) (p : α → Bool) :
    (xs.map (fun x => if p x then 1 else 0)).sum = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x <;> simp [hx, ih, Nat.add_comm]

private theorem count_eq_sum_ite3 {α : Type} (xs : List α) (p : α → Bool) :
    (xs.map (fun x => if p x then 3 else 0)).sum = 3 * (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x <;> simp [hx, ih] <;> omega

private theorem sum_map_add {α : Type} (xs : List α) (f1 f2 : α → Nat) :
    (xs.map (fun x => f1 x + f2 x)).sum = (xs.map f1).sum + (xs.map f2).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

/-- **THEOREM IIIa (Exact Binomial Power-of-3 Spectrum for `R &&& (-R)`):**
    For EVERY bit-width `w : Nat` and EVERY exponent `j : Nat`:
    1. Every state `s ∈ (BitVec w)^2` under `(L, R) ↦ (R, L ^^^ (R &&& (-R)))` has exact
       minimal period `3^e` for some `e ≤ w`, hence `F^{3^w}(s) = s` universally.
    2. The EXACT number of states in `(BitVec w)^2` having exact minimal period `3^j` is
       `Nat.choose w j * 3^j` (equivalently, EXACTLY `Nat.choose w j` disjoint cycles of
       length `3^j`, summing to `2^w` cycles in total).
    3. The maximum period `3^w` is attained constructively by `(BitVec.allOnes w, 0#w)`. -/
theorem theorem_IIIa_lsb_binomial_spectrum :
    (∀ (w : Nat) (s : BitVec w × BitVec w),
      (∃ e, e ≤ w ∧ ExactPeriod fLsb w s (3 ^ e)) ∧
      hwFeistelIter (fun _ R => R &&& (-R)) w (3 ^ w) s = s) ∧
    (∀ (w j : Nat),
      ((allPairs w).filter (isPeriod3Pow w j)).length = binom w j * 3 ^ j) ∧
    (∀ (w : Nat),
      ExactPeriod fLsb w (BitVec.allOnes w, 0#w) (3 ^ w)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w s
    have hinv := lsbZeroInv_all (fun _ => false) w (fun _ _ => rfl) s
    refine ⟨⟨hinv.exp, hinv.exp_le, hinv.exact_per⟩, ?_⟩
    rw [hwFeistelIter_eq_feistelIter _ _ hw_lsb_eq]
    have hdiv : 3 ^ w = 3 ^ (w - hinv.exp) * 3 ^ hinv.exp := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hinv.exp_le]
    rw [hdiv]
    exact feistelIter_mul_of_fixed fLsb w (3 ^ hinv.exp) s hinv.exact_per.2.1 _
  · intro w
    induction w with
    | zero =>
      intro j
      cases j with
      | zero => decide
      | succ j' =>
        have hfalse : isPeriod3Pow 0 (j' + 1) (0#0, 0#0) = false := by
          simp only [isPeriod3Pow, Bool.and_eq_false_iff, Bool.not_eq_false', beq_iff_eq]
          right
          have hsub : ∀ s1 s2 : BitVec 0 × BitVec 0, s1 = s2 := fun ⟨a, b⟩ ⟨c, d⟩ =>
            Prod.ext (Subsingleton.elim a c) (Subsingleton.elim b d)
          exact hsub _ _
        simp [allPairs, hfalse, binom]
    | succ k ih =>
      intro j
      simp only [allPairs, sum_filter_flatMap]
      have hfn : (allPairs k).map (fun x => ((liftFour x).filter (isPeriod3Pow (k + 1) j)).length) =
          (allPairs k).map (fun x =>
            (if isPeriod3Pow k j x then 1 else 0) +
            (match j with | 0 => 0 | j' + 1 => if isPeriod3Pow k j' x then 3 else 0)) := by
        apply List.map_congr_left
        intro x _; exact count_liftFour_fLsb k j x
      rw [hfn, sum_map_add, count_eq_sum_ite]
      cases j with
      | zero =>
        have hz : ((allPairs k).map (fun _ => 0)).sum = 0 := by
          clear ih hfn
          induction (allPairs k) with
          | nil => rfl
          | cons _ xs ihx => simp [ihx]
        rw [hz, Nat.add_zero, ih 0]
        simp [binom]
      | succ j' =>
        rw [count_eq_sum_ite3, ih (j' + 1), ih j']
        change binom k (j' + 1) * 3 ^ (j' + 1) + 3 * (binom k j' * 3 ^ j') =
          (binom k j' + binom k (j' + 1)) * 3 ^ (j' + 1)
        have hpow : 3 ^ (j' + 1) = 3 * 3 ^ j' := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow, Nat.add_mul, Nat.add_comm]
        congr 1; ac_rfl
  · intro w
    induction w with
    | zero =>
      refine ⟨by omega, ?_, fun q h1 h2 => by omega⟩
      simp only [feistelIter, feistelStepF, Prod.mk.injEq]
      exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    | succ k ih =>
      let s : BitVec (k + 1) × BitVec (k + 1) := (BitVec.allOnes (k + 1), 0#(k + 1))
      have htr : truncPair k s = (BitVec.allOnes k, 0#k) := by
        simp only [s, truncPair, Prod.mk.injEq]
        constructor
        · apply BitVec.eq_of_getLsbD_eq; intro i hi
          rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
              BitVec.getLsbD_allOnes, BitVec.getLsbD_allOnes, decide_eq_true hi,
              decide_eq_true (Nat.lt_succ_of_lt hi)]
        · simp
      have htop : topBitPair k s = (true, false) := by
        simp only [s, topBitPair, BitVec.getLsbD_allOnes, Nat.lt_succ_self, decide_true,
          BitVec.getLsbD_zero]
      have inv := lsbZeroInv_all (fun _ => false) k (fun _ _ => rfl) (BitVec.allOnes k, 0#k)
      -- At `t = 0`, `R = 0#k = triggerPrefix`, so `r = 0` and monodromy is literally `J1`!
      have hmono : monodromy fLsb k (truncPair k s) (3 ^ k) = Aff2.J1 := by
        rw [htr]
        have h0 : (feistelIter fLsb k 0 (BitVec.allOnes k, 0#k)).2 = triggerPrefix (fun _ => false) k :=
          zero_eq_triggerPrefix_false k
        have heq_exp : 3 ^ inv.exp = 3 ^ k := by
          have d1 := exactPeriod_dvd inv.exact_per ih.2.1
          have d2 := exactPeriod_dvd ih inv.exact_per.2.1
          exact Nat.dvd_antisymm d1 d2
        rcases inv.uniq_hit with ⟨r, hr, huniq⟩
        have hr0 : r = 0 := ((huniq 0 inv.exact_per.1).1 h0).symm
        subst hr0
        apply monodromy_fLsbGen_one_hit (fun _ => false) k (3 ^ k) (BitVec.allOnes k, 0#k) (three_pow_odd k) h0
        intro t ht0 htk heq
        rw [← heq_exp] at htk
        have := (huniq t htk).1 heq; omega
      have hfix3 : Aff2.apply (Aff2.pow (monodromy fLsb k (truncPair k s) (3 ^ k)) 3) (topBitPair k s) =
          topBitPair k s := by rw [hmono, htop]; rfl
      have hne1 : Aff2.apply (Aff2.pow (monodromy fLsb k (truncPair k s) (3 ^ k)) 1) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      have hne2 : Aff2.apply (Aff2.pow (monodromy fLsb k (truncPair k s) (3 ^ k)) 2) (topBitPair k s) ≠
          topBitPair k s := by rw [hmono, htop]; decide
      have hp3 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp3]
      refine ⟨by have := Nat.pow_pos (a := 3) (n := k) (by omega); omega,
              (feistel_period_lift fLsb k (3 ^ k) 3 s (by rw [htr]; exact ih.2.1)).2 hfix3, ?_⟩
      intro q hq0 hqlt hqfix
      have htrq : feistelIter fLsb k q (BitVec.allOnes k, 0#k) = (BitVec.allOnes k, 0#k) := by
        have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate, htr] at this
      rcases exactPeriod_dvd ih htrq with ⟨m, rfl⟩
      have hm : m = 1 ∨ m = 2 := by
        rcases m with _ | m
        · simp at hq0
        · rcases m with _ | m
          · exact Or.inl rfl
          · rcases m with _ | m
            · exact Or.inr rfl
            · exfalso
              have hle : 3 * 3 ^ k ≤ 3 ^ k * (m + 3) := by
                rw [Nat.mul_comm 3 (3 ^ k)]; exact Nat.mul_le_mul_left (3 ^ k) (by omega)
              exact Nat.not_lt.mpr hle hqlt
      rcases hm with rfl | rfl
      · exact hne1 ((feistel_period_lift fLsb k (3 ^ k) 1 s (by rw [htr]; exact ih.2.1)).1 (by simpa using hqfix))
      · exact hne2 ((feistel_period_lift fLsb k (3 ^ k) 2 s (by rw [htr]; exact ih.2.1)).1 (by simpa [Nat.mul_comm] using hqfix))

/-! ### Half IIIb: Sharp `ctz(τ) = m` Period-Lock Phase Transition (`Rule (0,0,1,0)`) -/

/-- Monodromy of an odd-length cycle of `fLsbGen τ` with 2 hits at `0` and odd `Δ < p`:
    equals `J0 ∘ J1^2` (an involution fixing `a = false` and swapping `(true, false) ↔ (true, true)`!). -/
private theorem monodromy_fLsbGen_two_odd_hits (τ : Nat → Bool) (k p Δ : Nat)
    (u : BitVec k × BitVec k) (hodd : p % 2 = 1) (hΔ0 : 0 < Δ) (hΔp : Δ < p) (hΔodd : Δ % 2 = 1)
    (huniq : ∀ t, t < p → ((feistelIter (fLsbGen τ) k t u).2 = triggerPrefix τ k ↔ t = 0 ∨ t = Δ)) :
    monodromy (fLsbGen τ) k u Δ = Aff2.J1 ∧
    monodromy (fLsbGen τ) k u p = Aff2.comp Aff2.J0 (Aff2.comp Aff2.J1 Aff2.J1) := by
  have hm0 : monodromy (fLsbGen τ) k u 1 = Aff2.J1 := by
    simp only [monodromy, fLsbGen_step_eq]
    have h0 := (huniq 0 (by omega)).2 (Or.inl rfl)
    simp only [h0, ↓reduceIte]; rfl
  have hm_mid1 : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k 1 u) (Δ - 1) = Aff2.id := by
    have hc : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k 1 u) (Δ - 1) = Aff2.pow Aff2.J0 (Δ - 1) := by
      apply monodromy_fLsbGen_no_hits
      intro t ht heq; rw [← feistelIter_add] at heq
      rcases (huniq (t + 1) (by omega)).1 heq with h | h <;> omega
    rw [hc, show Δ - 1 = 2 * ((Δ - 1) / 2) by omega, Aff2.J0_pow_two_mul]
  have hmΔ : monodromy (fLsbGen τ) k u Δ = Aff2.J1 := by
    rw [show Δ = (Δ - 1) + 1 by omega, monodromy_add, hm_mid1, hm0, Aff2.id_comp]
  have hm_hit2 : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k Δ u) 1 = Aff2.J1 := by
    simp only [monodromy, fLsbGen_step_eq]
    have hΔ := (huniq Δ hΔp).2 (Or.inr rfl)
    simp only [feistelIter, hΔ, ↓reduceIte]; rfl
  have hm_mid2 : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k (Δ + 1) u) (p - Δ - 1) = Aff2.J0 := by
    have hc : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k (Δ + 1) u) (p - Δ - 1) =
        Aff2.pow Aff2.J0 (p - Δ - 1) := by
      apply monodromy_fLsbGen_no_hits
      intro t ht heq; rw [← feistelIter_add] at heq
      rcases (huniq (t + (Δ + 1)) (by omega)).1 heq with h | h <;> omega
    rw [hc, show p - Δ - 1 = 2 * ((p - Δ - 1) / 2) + 1 by omega, Aff2.J0_pow_two_mul_succ]
  refine ⟨hmΔ, ?_⟩
  rw [show p = (p - Δ - 1) + (1 + Δ) by omega, monodromy_add, monodromy_add,
      Nat.add_comm 1 Δ, hm_mid2, hm_hit2, hmΔ]

/-- Monodromy of an even-length cycle of `fLsbGen τ` with 2 hits at `0` and even `Δ < 2*p`:
    equals `id` (`(J0 ∘ J1)^2 = id`), AND `monodromy u Δ = J0 ∘ J1` preserves the `R`-top-bit `b`! -/
private theorem monodromy_fLsbGen_two_even_hits (τ : Nat → Bool) (k p2 Δ : Nat)
    (u : BitVec k × BitVec k) (heven : p2 % 2 = 0) (hΔ0 : 0 < Δ) (hΔp : Δ < p2) (hΔeven : Δ % 2 = 0)
    (huniq : ∀ t, t < p2 → ((feistelIter (fLsbGen τ) k t u).2 = triggerPrefix τ k ↔ t = 0 ∨ t = Δ)) :
    monodromy (fLsbGen τ) k u Δ = Aff2.comp Aff2.J0 Aff2.J1 ∧
    monodromy (fLsbGen τ) k u p2 = Aff2.id := by
  have hm0 : monodromy (fLsbGen τ) k u 1 = Aff2.J1 := by
    simp only [monodromy, fLsbGen_step_eq]
    have h0 := (huniq 0 (by omega)).2 (Or.inl rfl)
    simp only [h0, ↓reduceIte]; rfl
  have hm_mid1 : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k 1 u) (Δ - 1) = Aff2.J0 := by
    have hc : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k 1 u) (Δ - 1) = Aff2.pow Aff2.J0 (Δ - 1) := by
      apply monodromy_fLsbGen_no_hits
      intro t ht heq; rw [← feistelIter_add] at heq
      rcases (huniq (t + 1) (by omega)).1 heq with h | h <;> omega
    rw [hc, show Δ - 1 = 2 * ((Δ - 1) / 2) + 1 by omega, Aff2.J0_pow_two_mul_succ]
  have hmΔ : monodromy (fLsbGen τ) k u Δ = Aff2.comp Aff2.J0 Aff2.J1 := by
    rw [show Δ = (Δ - 1) + 1 by omega, monodromy_add, hm_mid1, hm0]
  have hm_hit2 : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k Δ u) 1 = Aff2.J1 := by
    simp only [monodromy, fLsbGen_step_eq]
    have hΔ := (huniq Δ hΔp).2 (Or.inr rfl)
    simp only [feistelIter, hΔ, ↓reduceIte]; rfl
  have hm_mid2 : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k (Δ + 1) u) (p2 - Δ - 1) = Aff2.J0 := by
    have hc : monodromy (fLsbGen τ) k (feistelIter (fLsbGen τ) k (Δ + 1) u) (p2 - Δ - 1) =
        Aff2.pow Aff2.J0 (p2 - Δ - 1) := by
      apply monodromy_fLsbGen_no_hits
      intro t ht heq; rw [← feistelIter_add] at heq
      rcases (huniq (t + (Δ + 1)) (by omega)).1 heq with h | h <;> omega
    rw [hc, show p2 - Δ - 1 = 2 * ((p2 - Δ - 1) / 2) + 1 by omega, Aff2.J0_pow_two_mul_succ]
  refine ⟨hmΔ, ?_⟩
  rw [show p2 = (p2 - Δ - 1) + (1 + Δ) by omega, monodromy_add, monodromy_add,
      Nat.add_comm 1 Δ, hm_mid2, hm_hit2, hmΔ]; rfl

/-- Post-transition inductive invariant at widths `k ≥ m + 1` once `τ m = true` has fired:
    every cycle has period `p ∣ 3^(m+1)` (odd, 0 or 2 odd-separated hits) or `2*p`
    (even, 0 or 2 even-separated hits). -/
def CtzPhaseInv (τ : Nat → Bool) (m k : Nat) (s : BitVec k × BitVec k) : Prop :=
  (∃ p, p ∣ 3 ^ (m + 1) ∧ p % 2 = 1 ∧ ExactPeriod (fLsbGen τ) k s p ∧
    ((∀ t, t < p → (feistelIter (fLsbGen τ) k t s).2 ≠ triggerPrefix τ k) ∨
     (∃ r Δ, 0 < Δ ∧ Δ < p ∧ Δ % 2 = 1 ∧
        ∀ t, t < p → ((feistelIter (fLsbGen τ) k t (feistelIter (fLsbGen τ) k r s)).2 = triggerPrefix τ k ↔
          t = 0 ∨ t = Δ)))) ∨
  (∃ p, p ∣ 3 ^ (m + 1) ∧ p % 2 = 1 ∧ ExactPeriod (fLsbGen τ) k s (2 * p) ∧
    ((∀ t, t < 2 * p → (feistelIter (fLsbGen τ) k t s).2 ≠ triggerPrefix τ k) ∨
     (∃ r Δ, 0 < Δ ∧ Δ < 2 * p ∧ Δ % 2 = 0 ∧
        ∀ t, t < 2 * p → ((feistelIter (fLsbGen τ) k t (feistelIter (fLsbGen τ) k r s)).2 = triggerPrefix τ k ↔
          t = 0 ∨ t = Δ))))

/-- Transition entry at width `k = m + 1`: crossing the first `true` bit `τ m = true`
    converts every unique-hit cycle of `LsbZeroInv τ m` into either 0 hits (fixed lift)
    or 2 odd-separated hits (3-cycle lift), entering `CtzPhaseInv τ m (m + 1)`. -/
theorem ctzPhaseInv_entry (τ : Nat → Bool) (m : Nat)
    (hpre : ∀ j, j < m → τ j = false) (hm : τ m = true)
    (s : BitVec (m + 1) × BitVec (m + 1)) :
    CtzPhaseInv τ m (m + 1) s := by
  have ih := lsbZeroInv_all τ m hpre (truncPair m s)
  let p := 3 ^ ih.exp
  have hp_dvd_m : p ∣ 3 ^ m := by
    refine ⟨3 ^ (m - ih.exp), ?_⟩
    rw [← Nat.pow_add, Nat.add_sub_of_le ih.exp_le]
  have hp_dvd_m1 : p ∣ 3 ^ (m + 1) := by
    rcases hp_dvd_m with ⟨q, hq⟩
    refine ⟨q * 3, ?_⟩
    rw [Nat.pow_succ, hq]; ac_rfl
  have h3p_dvd_m1 : 3 * p ∣ 3 ^ (m + 1) := by
    rcases hp_dvd_m with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [Nat.pow_succ, hq]; ac_rfl
  rcases ih.uniq_hit with ⟨r, hr, huniq⟩
  let U := feistelIter (fLsbGen τ) (m + 1) r s
  have htrU : truncPair m U = feistelIter (fLsbGen τ) m r (truncPair m s) :=
    feistelIter_truncate (fLsbGen τ) m r s
  have hexU : ExactPeriod (fLsbGen τ) m (truncPair m U) p := by
    rw [htrU]; exact (exactPeriod_shift (fLsbGen τ) m p r (truncPair m s)).2 ih.exact_per
  have hU_hits : ∀ t, t < p → ((feistelIter (fLsbGen τ) m t (truncPair m U)).2 = triggerPrefix τ m ↔ t = 0) := by
    intro t ht
    rw [htrU, ← feistelIter_add, feistelIter_eq_mod (fLsbGen τ) m p (t + r) (truncPair m s) ih.exact_per.2.1]
    rw [huniq ((t + r) % p) (Nat.mod_lt _ ih.exact_per.1)]
    constructor
    · intro heq
      by_cases hsum : t + r < p
      · rw [Nat.mod_eq_of_lt hsum] at heq; omega
      · have hlt2 : t + r - p < p := by omega
        have hmeq : (t + r) % p = t + r - p := by
          have : t + r = (t + r - p) + 1 * p := by omega
          conv => lhs; rw [this]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
        rw [hmeq] at heq; omega
    · rintro rfl; rw [Nat.zero_add, Nat.mod_eq_of_lt hr]
  have hmono : monodromy (fLsbGen τ) m (truncPair m U) p = Aff2.J1 :=
    monodromy_fLsbGen_one_hit τ m p (truncPair m U) (three_pow_odd ih.exp)
      ((hU_hits 0 ih.exact_per.1).2 rfl)
      (fun t ht0 htp heq => by have := (hU_hits t htp).1 heq; omega)
  have htr_j : ∀ j, (feistelIter (fLsbGen τ) (m + 1) j U).2.setWidth m =
      (feistelIter (fLsbGen τ) m j (truncPair m U)).2 :=
    fun j => congrArg Prod.snd (feistelIter_truncate (fLsbGen τ) m j U)
  left
  cases ha : (topBitPair m U).1 <;> cases hb : (topBitPair m U).2
  · -- Fixed lift `(false, false)`: `b = false ≠ true = τ m` → 0 hits!
    have htop : topBitPair m U = (false, false) := Prod.ext ha hb
    have hfix1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) m (truncPair m U) p) 1) (topBitPair m U) =
        topBitPair m U := by rw [hmono, htop]; rfl
    have hexU' : ExactPeriod (fLsbGen τ) (m + 1) U p := by
      refine ⟨ih.exact_per.1, by simpa using (feistel_period_lift (fLsbGen τ) m p 1 U hexU.2.1).2 hfix1, ?_⟩
      intro q hq0 hqlt hqfix
      have := congrArg (truncPair m) hqfix; rw [feistelIter_truncate] at this
      exact hexU.2.2 q hq0 hqlt this
    refine ⟨p, hp_dvd_m1, three_pow_odd ih.exp,
            (exactPeriod_shift (fLsbGen τ) (m + 1) p r s).1 hexU', Or.inl ?_⟩
    intro t ht heq
    have htr_s : (feistelIter (fLsbGen τ) (m + 1) t s).2.setWidth m =
        (feistelIter (fLsbGen τ) m t (truncPair m s)).2 :=
      congrArg Prod.snd (feistelIter_truncate (fLsbGen τ) m t s)
    rw [eq_triggerPrefix_succ_iff, htr_s, hm] at heq
    have htr_r : t = r := (huniq t ht).1 heq.1
    rw [htr_r] at heq
    have hb_eq : (topBitPair m U).2 = true := heq.2
    rw [hb] at hb_eq; cases hb_eq
  all_goals
    -- 3-cycle lift: `b = true = τ m` occurs TWICE among `{0, p, 2*p}`, at odd separation `p`!
    have htop : topBitPair m U = (_, _) := Prod.ext ha hb
    have hfix3 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) m (truncPair m U) p) 3) (topBitPair m U) =
        topBitPair m U := by rw [hmono, htop]; rfl
    have hne1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) m (truncPair m U) p) 1) (topBitPair m U) ≠
        topBitPair m U := by rw [hmono, htop]; decide
    have hne2 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) m (truncPair m U) p) 2) (topBitPair m U) ≠
        topBitPair m U := by rw [hmono, htop]; decide
    have hp0 : 0 < p := ih.exact_per.1
    have hexU' : ExactPeriod (fLsbGen τ) (m + 1) U (3 * p) := by
      refine ⟨by omega, (feistel_period_lift (fLsbGen τ) m p 3 U hexU.2.1).2 hfix3, ?_⟩
      intro q hq0 hqlt hqfix
      have htrq : feistelIter (fLsbGen τ) m q (truncPair m U) = truncPair m U := by
        have := congrArg (truncPair m) hqfix; rwa [feistelIter_truncate] at this
      rcases exactPeriod_dvd hexU htrq with ⟨q', rfl⟩
      have hq12 : q' = 1 ∨ q' = 2 := by
        rcases q' with _ | q'
        · simp at hq0
        · rcases q' with _ | q'
          · exact Or.inl rfl
          · rcases q' with _ | q'
            · exact Or.inr rfl
            · exfalso
              have hle : 3 * p ≤ p * (q' + 3) := by
                rw [Nat.mul_comm 3 p]; exact Nat.mul_le_mul_left p (by omega)
              exact Nat.not_lt.mpr hle hqlt
      rcases hq12 with rfl | rfl
      · exact hne1 ((feistel_period_lift (fLsbGen τ) m p 1 U hexU.2.1).1 (by simpa using hqfix))
      · exact hne2 ((feistel_period_lift (fLsbGen τ) m p 2 U hexU.2.1).1 (by simpa [Nat.mul_comm] using hqfix))
    have hb0 : (feistelIter (fLsbGen τ) (m + 1) 0 U).2.getLsbD m = (topBitPair m U).2 := rfl
    have hb1 : (feistelIter (fLsbGen τ) (m + 1) p U).2.getLsbD m = (Aff2.apply Aff2.J1 (topBitPair m U)).2 := by
      have := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) m p U); rwa [hmono] at this
    have hb2 : (feistelIter (fLsbGen τ) (m + 1) (2 * p) U).2.getLsbD m =
        (Aff2.apply (Aff2.pow Aff2.J1 2) (topBitPair m U)).2 := by
      have := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) m (2 * p) U)
      rwa [monodromy_mul_of_fixed (fLsbGen τ) m p 2 (truncPair m U) hexU.2.1, hmono] at this
    rw [htop] at hb0 hb1 hb2
    have hcand : ∀ t, t < 3 * p →
        (feistelIter (fLsbGen τ) m t (truncPair m U)).2 = triggerPrefix τ m →
        t = 0 ∨ t = p ∨ t = 2 * p := by
      intro t ht hhit
      rw [feistelIter_eq_mod (fLsbGen τ) m p t (truncPair m U) hexU.2.1] at hhit
      have hm0 : t % p = 0 := (hU_hits (t % p) (Nat.mod_lt _ ih.exact_per.1)).1 hhit
      have hdiv : t = p * (t / p) := by have := Nat.div_add_mod t p; omega
      have hlt3 : t / p < 3 := by
        by_cases h3 : t / p < 3
        · exact h3
        · exfalso
          have hle := Nat.mul_le_mul_left p (Nat.le_of_not_lt h3)
          rw [← hdiv, Nat.mul_comm p 3] at hle
          exact Nat.not_lt.mpr hle ht
      match hq : t / p with
      | 0 => left; rw [hdiv, hq]; simp
      | 1 => right; left; rw [hdiv, hq]; simp
      | 2 => right; right; rw [hdiv, hq, Nat.mul_comm]
      | n + 3 => exfalso; omega
    have h3odd : (3 * p) % 2 = 1 := by have := three_pow_odd ih.exp; omega
    have hpodd : p % 2 = 1 := three_pow_odd ih.exp
    refine ⟨3 * p, h3p_dvd_m1, h3odd, (exactPeriod_shift (fLsbGen τ) (m + 1) (3 * p) r s).1 hexU', Or.inr ?_⟩
    -- Shift to the first of the two `b = true` hits among `{0, p, 2*p}`!
    first
    | -- `(false, true)`: hits at `0` and `p` (`Δ = p`, shift `r`!)
      (refine ⟨r, p, ih.exact_per.1, by omega, hpodd, fun t ht => ?_⟩
       change (feistelIter (fLsbGen τ) (m + 1) t U).2 = triggerPrefix τ (m + 1) ↔ t = 0 ∨ t = p
       rw [eq_triggerPrefix_succ_iff, htr_j t, hm]
       constructor
       · rintro ⟨htr_e, htop_e⟩
         rcases hcand t ht htr_e with rfl | rfl | rfl
         · exact Or.inl rfl
         · exact Or.inr rfl
         · rw [hb2] at htop_e; cases htop_e
       · rintro (rfl | rfl)
         · exact ⟨(hU_hits 0 ih.exact_per.1).2 rfl, hb0⟩
         · exact ⟨by rw [hexU.2.1]; exact (hU_hits 0 ih.exact_per.1).2 rfl, hb1⟩)
    | -- `(true, false)`: hits at `p` and `2*p` (`Δ = p`, shift `p + r`!)
      (refine ⟨p + r, p, ih.exact_per.1, by omega, hpodd, fun t ht => ?_⟩
       have hsh : feistelIter (fLsbGen τ) (m + 1) t (feistelIter (fLsbGen τ) (m + 1) (p + r) s) =
           feistelIter (fLsbGen τ) (m + 1) ((t + p) % (3 * p)) U := by
         have h1 : feistelIter (fLsbGen τ) (m + 1) t (feistelIter (fLsbGen τ) (m + 1) (p + r) s) =
             feistelIter (fLsbGen τ) (m + 1) (t + p) U := by
           rw [← feistelIter_add, ← Nat.add_assoc, feistelIter_add]
         rw [h1, feistelIter_eq_mod (fLsbGen τ) (m + 1) (3 * p) (t + p) U hexU'.2.1]
       rw [hsh, eq_triggerPrefix_succ_iff, htr_j _, hm]
       constructor
       · rintro ⟨htr_e, htop_e⟩
         rcases hcand _ (Nat.mod_lt _ (by omega)) htr_e with h0 | h1 | h2
         · rw [h0, hb0] at htop_e; cases htop_e
         · left
           by_cases hlt : t + p < 3 * p
           · rw [Nat.mod_eq_of_lt hlt] at h1; omega
           · have hmeq : (t + p) % (3 * p) = t + p - 3 * p := by
               have hsub : t + p = (t + p - 3 * p) + 1 * (3 * p) := by omega
               conv => lhs; rw [hsub]
               rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
             rw [hmeq] at h1; omega
         · right
           by_cases hlt : t + p < 3 * p
           · rw [Nat.mod_eq_of_lt hlt] at h2; omega
           · have hmeq : (t + p) % (3 * p) = t + p - 3 * p := by
               have hsub : t + p = (t + p - 3 * p) + 1 * (3 * p) := by omega
               conv => lhs; rw [hsub]
               rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
             rw [hmeq] at h2; omega
       · rintro (rfl | rfl)
         · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
           exact ⟨by rw [hexU.2.1]; exact (hU_hits 0 ih.exact_per.1).2 rfl, hb1⟩
         · rw [show p + p = 2 * p by omega, Nat.mod_eq_of_lt (by omega)]
           exact ⟨by rw [feistelIter_mul_of_fixed (fLsbGen τ) m p (truncPair m U) hexU.2.1 2]; exact (hU_hits 0 ih.exact_per.1).2 rfl, hb2⟩)
    | -- `(true, true)`: hits at `2*p` and `0` (`Δ = p` from `2*p`, shift `2*p + r`!)
      (refine ⟨2 * p + r, p, ih.exact_per.1, by omega, hpodd, fun t ht => ?_⟩
       have hsh : feistelIter (fLsbGen τ) (m + 1) t (feistelIter (fLsbGen τ) (m + 1) (2 * p + r) s) =
           feistelIter (fLsbGen τ) (m + 1) ((t + 2 * p) % (3 * p)) U := by
         have h1 : feistelIter (fLsbGen τ) (m + 1) t (feistelIter (fLsbGen τ) (m + 1) (2 * p + r) s) =
             feistelIter (fLsbGen τ) (m + 1) (t + 2 * p) U := by
           rw [← feistelIter_add, ← Nat.add_assoc, feistelIter_add]
         rw [h1, feistelIter_eq_mod (fLsbGen τ) (m + 1) (3 * p) (t + 2 * p) U hexU'.2.1]
       rw [hsh, eq_triggerPrefix_succ_iff, htr_j _, hm]
       constructor
       · rintro ⟨htr_e, htop_e⟩
         rcases hcand _ (Nat.mod_lt _ (by omega)) htr_e with h0 | h1 | h2
         · right
           by_cases hlt : t + 2 * p < 3 * p
           · rw [Nat.mod_eq_of_lt hlt] at h0; omega
           · have hmeq : (t + 2 * p) % (3 * p) = t + 2 * p - 3 * p := by
               have hsub : t + 2 * p = (t + 2 * p - 3 * p) + 1 * (3 * p) := by omega
               conv => lhs; rw [hsub]
               rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
             rw [hmeq] at h0; omega
         · rw [h1, hb1] at htop_e; cases htop_e
         · left
           by_cases hlt : t + 2 * p < 3 * p
           · rw [Nat.mod_eq_of_lt hlt] at h2; omega
           · have hmeq : (t + 2 * p) % (3 * p) = t + 2 * p - 3 * p := by
               have hsub : t + 2 * p = (t + 2 * p - 3 * p) + 1 * (3 * p) := by omega
               conv => lhs; rw [hsub]
               rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
             rw [hmeq] at h2; omega
       · rintro (rfl | rfl)
         · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
           exact ⟨by rw [feistelIter_mul_of_fixed (fLsbGen τ) m p (truncPair m U) hexU.2.1 2]; exact (hU_hits 0 ih.exact_per.1).2 rfl, hb2⟩
         · rw [show p + 2 * p = 3 * p by omega, Nat.mod_self]
           exact ⟨(hU_hits 0 ih.exact_per.1).2 rfl, hb0⟩)

/-- Inductive preservation of `CtzPhaseInv τ m k` for ALL `k ≥ m + 1` (arbitrary `τ k ∈ Bool`!). -/
theorem ctzPhaseInv_step (τ : Nat → Bool) (m k : Nat)
    (s : BitVec (k + 1) × BitVec (k + 1)) (ih : CtzPhaseInv τ m k (truncPair k s)) :
    CtzPhaseInv τ m (k + 1) s := by
  have htr : ∀ (U : BitVec (k + 1) × BitVec (k + 1)) j,
      (feistelIter (fLsbGen τ) (k + 1) j U).2.setWidth k = (feistelIter (fLsbGen τ) k j (truncPair k U)).2 :=
    fun U j => congrArg Prod.snd (feistelIter_truncate (fLsbGen τ) k j U)
  rcases ih with ⟨p, hdvd, hodd, hexp, hhits⟩ | ⟨p, hdvd, hodd, hex2p, hhits⟩
  · -- ODD branch: `ExactPeriod ... p`
    rcases hhits with hnone | ⟨r, Δ, hΔ0, hΔp, hΔodd, huniq⟩
    · -- 0 hits: monodromy = `J0^p = J0` (order 2!)
      have hmono : monodromy (fLsbGen τ) k (truncPair k s) p = Aff2.J0 := by
        rw [monodromy_fLsbGen_no_hits τ k p (truncPair k s) hnone,
            show p = 2 * (p / 2) + 1 by omega, Aff2.J0_pow_two_mul_succ]
      have hnone' : ∀ q, q < 2 * p → (feistelIter (fLsbGen τ) (k + 1) q s).2 ≠ triggerPrefix τ (k + 1) := by
        intro q _ heq
        rw [eq_triggerPrefix_succ_iff, htr s q,
            feistelIter_eq_mod (fLsbGen τ) k p q (truncPair k s) hexp.2.1] at heq
        exact hnone (q % p) (Nat.mod_lt _ hexp.1) heq.1
      cases ha : (topBitPair k s).1 <;> cases hb : (topBitPair k s).2
      · -- `(false, false)` fixed by `J0` → Odd, 0 hits
        have htop : topBitPair k s = (false, false) := Prod.ext ha hb
        have hfix1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k s) p) 1) (topBitPair k s) =
            topBitPair k s := by rw [hmono, htop]; rfl
        left
        refine ⟨p, hdvd, hodd, ⟨hexp.1, by simpa using (feistel_period_lift (fLsbGen τ) k p 1 s hexp.2.1).2 hfix1, ?_⟩,
                Or.inl (fun t ht => hnone' t (by omega))⟩
        intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
        exact hexp.2.2 q hq0 hqlt this
      · -- `(false, true)` 2-cycle of `J0` → Even, 0 hits
        have htop : topBitPair k s = (false, true) := Prod.ext ha hb
        have hfix2 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k s) p) 2) (topBitPair k s) =
            topBitPair k s := by rw [hmono, htop]; rfl
        have hne1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k s) p) 1) (topBitPair k s) ≠
            topBitPair k s := by rw [hmono, htop]; decide
        right
        refine ⟨p, hdvd, hodd, ⟨by omega, (feistel_period_lift (fLsbGen τ) k p 2 s hexp.2.1).2 hfix2, ?_⟩,
                Or.inl hnone'⟩
        intro q hq0 hqlt hqfix
        have htrq : feistelIter (fLsbGen τ) k q (truncPair k s) = truncPair k s := by
          have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate] at this
        rcases exactPeriod_dvd hexp htrq with ⟨q', rfl⟩
        have hq1 : q' = 1 := by
          rcases q' with _ | q'
          · simp at hq0
          · rcases q' with _ | q'
            · rfl
            · exfalso
              have hle : 2 * p ≤ p * (q' + 2) := by
                rw [Nat.mul_comm 2 p]; exact Nat.mul_le_mul_left p (by omega)
              exact Nat.not_lt.mpr hle hqlt
        subst hq1
        exact hne1 ((feistel_period_lift (fLsbGen τ) k p 1 s hexp.2.1).1 (by simpa using hqfix))
      · -- `(true, false)` 2-cycle of `J0` → Even, 0 hits
        have htop : topBitPair k s = (true, false) := Prod.ext ha hb
        have hfix2 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k s) p) 2) (topBitPair k s) =
            topBitPair k s := by rw [hmono, htop]; rfl
        have hne1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k s) p) 1) (topBitPair k s) ≠
            topBitPair k s := by rw [hmono, htop]; decide
        right
        refine ⟨p, hdvd, hodd, ⟨by omega, (feistel_period_lift (fLsbGen τ) k p 2 s hexp.2.1).2 hfix2, ?_⟩,
                Or.inl hnone'⟩
        intro q hq0 hqlt hqfix
        have htrq : feistelIter (fLsbGen τ) k q (truncPair k s) = truncPair k s := by
          have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate] at this
        rcases exactPeriod_dvd hexp htrq with ⟨q', rfl⟩
        have hq1 : q' = 1 := by
          rcases q' with _ | q'
          · simp at hq0
          · rcases q' with _ | q'
            · rfl
            · exfalso
              have hle : 2 * p ≤ p * (q' + 2) := by
                rw [Nat.mul_comm 2 p]; exact Nat.mul_le_mul_left p (by omega)
              exact Nat.not_lt.mpr hle hqlt
        subst hq1
        exact hne1 ((feistel_period_lift (fLsbGen τ) k p 1 s hexp.2.1).1 (by simpa using hqfix))
      · -- `(true, true)` fixed by `J0` → Odd, 0 hits
        have htop : topBitPair k s = (true, true) := Prod.ext ha hb
        have hfix1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k s) p) 1) (topBitPair k s) =
            topBitPair k s := by rw [hmono, htop]; rfl
        left
        refine ⟨p, hdvd, hodd, ⟨hexp.1, by simpa using (feistel_period_lift (fLsbGen τ) k p 1 s hexp.2.1).2 hfix1, ?_⟩,
                Or.inl (fun t ht => hnone' t (by omega))⟩
        intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
        exact hexp.2.2 q hq0 hqlt this
    · -- 2 odd-separated hits at `0` and `Δ` from `U = F^r s`: monodromy = `J0 ∘ J1^2` (involution!)
      let U := feistelIter (fLsbGen τ) (k + 1) r s
      have htrU : truncPair k U = feistelIter (fLsbGen τ) k r (truncPair k s) :=
        feistelIter_truncate (fLsbGen τ) k r s
      have hexU : ExactPeriod (fLsbGen τ) k (truncPair k U) p := by
        rw [htrU]; exact (exactPeriod_shift (fLsbGen τ) k p r (truncPair k s)).2 hexp
      have hUuniq : ∀ t, t < p → ((feistelIter (fLsbGen τ) k t (truncPair k U)).2 = triggerPrefix τ k ↔ t = 0 ∨ t = Δ) := by
        intro t ht; rw [htrU]; exact huniq t ht
      have ⟨hmΔ, hmono⟩ := monodromy_fLsbGen_two_odd_hits τ k p Δ (truncPair k U) hodd hΔ0 hΔp hΔodd hUuniq
      cases ha : (topBitPair k U).1
      · -- `a = false`: FIXED by `J0 ∘ J1^2`! And `b` at `Δ` equals `b` at `0`!
        have hfix1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) p) 1) (topBitPair k U) =
            topBitPair k U := by
          rw [hmono]; rcases htp : topBitPair k U with ⟨a, b⟩; rw [htp] at ha; cases ha; cases b <;> rfl
        have hexU' : ExactPeriod (fLsbGen τ) (k + 1) U p := by
          refine ⟨hexp.1, by simpa using (feistel_period_lift (fLsbGen τ) k p 1 U hexU.2.1).2 hfix1, ?_⟩
          intro q hq0 hqlt hqfix
          have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
          exact hexU.2.2 q hq0 hqlt this
        have hbΔ : (feistelIter (fLsbGen τ) (k + 1) Δ U).2.getLsbD k = U.2.getLsbD k := by
          have ht := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) k Δ U)
          rw [hmΔ] at ht
          change (topBitPair k (feistelIter (fLsbGen τ) (k + 1) Δ U)).2 = (topBitPair k U).2
          rw [ht]; rcases htp : topBitPair k U with ⟨a, b⟩; rw [htp] at ha; cases ha; cases b <;> rfl
        left
        refine ⟨p, hdvd, hodd, (exactPeriod_shift (fLsbGen τ) (k + 1) p r s).1 hexU', ?_⟩
        by_cases htop : U.2.getLsbD k = τ k
        · right
          refine ⟨r, Δ, hΔ0, hΔp, hΔodd, fun t ht => ?_⟩
          change (feistelIter (fLsbGen τ) (k + 1) t U).2 = triggerPrefix τ (k + 1) ↔ t = 0 ∨ t = Δ
          rw [eq_triggerPrefix_succ_iff, htr U t]
          constructor
          · rintro ⟨htr_e, _⟩; exact (hUuniq t ht).1 htr_e
          · rintro (ht0 | htΔ)
            · rw [ht0]; exact ⟨(hUuniq 0 hexp.1).2 (Or.inl rfl), htop⟩
            · rw [htΔ]; exact ⟨(hUuniq Δ hΔp).2 (Or.inr rfl), by rw [hbΔ]; exact htop⟩
        · left
          intro t ht heq
          have hex_s' := (exactPeriod_shift (fLsbGen τ) (k + 1) p r s).1 hexU'
          -- Shift `F^t s` into `U`
          let t' := (t + (p - r % p)) % p
          have hsh : feistelIter (fLsbGen τ) (k + 1) t s = feistelIter (fLsbGen τ) (k + 1) t' U := by
            simp only [U, ← feistelIter_add]
            rw [feistelIter_eq_mod (fLsbGen τ) (k + 1) p (t' + r) s hex_s'.2.1]
            have hmod : (t' + r) % p = t := by
              have h1 : (t' + r) % p = (t' + r % p) % p := by rw [Nat.add_mod_mod]
              rw [h1]; simp only [t']; rw [Nat.mod_add_mod]
              have hrlt : r % p < p := Nat.mod_lt r hexp.1
              have h2 : t + (p - r % p) + r % p = t + 1 * p := by omega
              rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
            rw [hmod]
          rw [hsh, eq_triggerPrefix_succ_iff, htr U t'] at heq
          rcases (hUuniq t' (Nat.mod_lt _ hexp.1)).1 heq.1 with h0 | hΔ
          · rw [h0] at heq; exact htop heq.2
          · rw [hΔ, hbΔ] at heq; exact htop heq.2
      · -- `a = true`: 2-cycle of `J0 ∘ J1^2` → period doubles to `2*p`, 2 EVEN-separated hits!
        have hfix2 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) p) 2) (topBitPair k U) =
            topBitPair k U := by
          rw [hmono]; rcases htp : topBitPair k U with ⟨a, b⟩; rw [htp] at ha; cases ha; cases b <;> rfl
        have hne1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) p) 1) (topBitPair k U) ≠
            topBitPair k U := by
          rw [hmono]; rcases htp : topBitPair k U with ⟨a, b⟩; rw [htp] at ha; cases ha; cases b <;> decide
        have hexU2 : ExactPeriod (fLsbGen τ) (k + 1) U (2 * p) := by
          refine ⟨by omega, (feistel_period_lift (fLsbGen τ) k p 2 U hexU.2.1).2 hfix2, ?_⟩
          intro q hq0 hqlt hqfix
          have htrq : feistelIter (fLsbGen τ) k q (truncPair k U) = truncPair k U := by
            have := congrArg (truncPair k) hqfix; rwa [feistelIter_truncate] at this
          rcases exactPeriod_dvd hexU htrq with ⟨q', rfl⟩
          have hq1 : q' = 1 := by
            rcases q' with _ | q'
            · simp at hq0
            · rcases q' with _ | q'
              · rfl
              · exfalso
                have hle : 2 * p ≤ p * (q' + 2) := by
                  rw [Nat.mul_comm 2 p]; exact Nat.mul_le_mul_left p (by omega)
                exact Nat.not_lt.mpr hle hqlt
          subst hq1
          exact hne1 ((feistel_period_lift (fLsbGen τ) k p 1 U hexU.2.1).1 (by simpa using hqfix))
        -- Top `R`-bits at `{0, Δ, p, p + Δ}` are `(b, !b, !b, b)`!
        have hbΔ : (feistelIter (fLsbGen τ) (k + 1) Δ U).2.getLsbD k = !(U.2.getLsbD k) := by
          have ht := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) k Δ U)
          rw [hmΔ] at ht
          change (topBitPair k (feistelIter (fLsbGen τ) (k + 1) Δ U)).2 = !(topBitPair k U).2
          rw [ht]; rcases htp : topBitPair k U with ⟨a, b⟩; rw [htp] at ha; cases ha; cases b <;> rfl
        have hbp : (feistelIter (fLsbGen τ) (k + 1) p U).2.getLsbD k = !(U.2.getLsbD k) := by
          have ht := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) k p U)
          rw [hmono] at ht
          change (topBitPair k (feistelIter (fLsbGen τ) (k + 1) p U)).2 = !(topBitPair k U).2
          rw [ht]; rcases htp : topBitPair k U with ⟨a, b⟩; rw [htp] at ha; cases ha; cases b <;> rfl
        have hbpΔ : (feistelIter (fLsbGen τ) (k + 1) (Δ + p) U).2.getLsbD k = U.2.getLsbD k := by
          have ht := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) k (Δ + p) U)
          rw [monodromy_add, hexU.2.1, hmΔ, hmono] at ht
          change (topBitPair k (feistelIter (fLsbGen τ) (k + 1) (Δ + p) U)).2 = (topBitPair k U).2
          rw [ht]; rcases htp : topBitPair k U with ⟨a, b⟩; rw [htp] at ha; cases ha; cases b <;> rfl
        have hcand : ∀ t, t < 2 * p →
            (feistelIter (fLsbGen τ) k t (truncPair k U)).2 = triggerPrefix τ k →
            t = 0 ∨ t = Δ ∨ t = p ∨ t = Δ + p := by
          intro t ht hhit
          by_cases hlt : t < p
          · rcases (hUuniq t hlt).1 hhit with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
          · have hsub : t = (t - p) + p := by omega
            have hmod : feistelIter (fLsbGen τ) k t (truncPair k U) =
                feistelIter (fLsbGen τ) k (t - p) (truncPair k U) := by
              conv => lhs; rw [hsub]; rw [feistelIter_add, hexU.2.1]
            rw [hmod] at hhit
            rcases (hUuniq (t - p) (by omega)).1 hhit with h0 | hΔ
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inr (Or.inr (by omega)))
        right
        refine ⟨p, hdvd, hodd, (exactPeriod_shift (fLsbGen τ) (k + 1) (2 * p) r s).1 hexU2, Or.inr ?_⟩
        by_cases htop : U.2.getLsbD k = τ k
        · -- Hits at `0` and `Δ + p` (EVEN separation `Δ + p`!)
          refine ⟨r, Δ + p, by omega, by omega, by omega, fun t ht => ?_⟩
          change (feistelIter (fLsbGen τ) (k + 1) t U).2 = triggerPrefix τ (k + 1) ↔ t = 0 ∨ t = Δ + p
          rw [eq_triggerPrefix_succ_iff, htr U t]
          constructor
          · rintro ⟨htr_e, htop_e⟩
            rcases hcand t ht htr_e with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · rw [hbΔ, htop] at htop_e; exact absurd htop_e (by cases τ k <;> decide)
            · rw [hbp, htop] at htop_e; exact absurd htop_e (by cases τ k <;> decide)
            · exact Or.inr rfl
          · rintro (ht0 | htΔ)
            · rw [ht0]; exact ⟨(hUuniq 0 hexp.1).2 (Or.inl rfl), htop⟩
            · rw [htΔ]; exact ⟨by rw [feistelIter_add, hexU.2.1]; exact (hUuniq Δ hΔp).2 (Or.inr rfl), by rw [hbpΔ]; exact htop⟩
        · -- Hits at `Δ` and `p` (EVEN separation `p - Δ`, shifted to `Δ + r`!)
          have hnot_eq : (!U.2.getLsbD k) = τ k := by
            cases h1 : U.2.getLsbD k <;> cases h2 : τ k <;> simp_all
          refine ⟨Δ + r, p - Δ, by omega, by omega, by omega, fun t ht => ?_⟩
          have hsh : feistelIter (fLsbGen τ) (k + 1) t (feistelIter (fLsbGen τ) (k + 1) (Δ + r) s) =
              feistelIter (fLsbGen τ) (k + 1) ((t + Δ) % (2 * p)) U := by
            have h1 : feistelIter (fLsbGen τ) (k + 1) t (feistelIter (fLsbGen τ) (k + 1) (Δ + r) s) =
                feistelIter (fLsbGen τ) (k + 1) (t + Δ) U := by
              simp only [U, ← feistelIter_add, Nat.add_assoc]
            rw [h1, feistelIter_eq_mod (fLsbGen τ) (k + 1) (2 * p) (t + Δ) U hexU2.2.1]
          rw [hsh, eq_triggerPrefix_succ_iff, htr U _]
          constructor
          · rintro ⟨htr_e, htop_e⟩
            rcases hcand _ (Nat.mod_lt _ (by omega)) htr_e with h0 | hΔ | hp_c | hpΔ
            · rw [h0] at htop_e; exact absurd htop_e htop
            · left
              by_cases hlt : t + Δ < 2 * p
              · rw [Nat.mod_eq_of_lt hlt] at hΔ; omega
              · have hmeq : (t + Δ) % (2 * p) = t + Δ - 2 * p := by
                  have hsub : t + Δ = (t + Δ - 2 * p) + 1 * (2 * p) := by omega
                  conv => lhs; rw [hsub]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
                rw [hmeq] at hΔ; omega
            · right
              by_cases hlt : t + Δ < 2 * p
              · rw [Nat.mod_eq_of_lt hlt] at hp_c; omega
              · have hmeq : (t + Δ) % (2 * p) = t + Δ - 2 * p := by
                  have hsub : t + Δ = (t + Δ - 2 * p) + 1 * (2 * p) := by omega
                  conv => lhs; rw [hsub]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
                rw [hmeq] at hp_c; omega
            · rw [hpΔ, hbpΔ] at htop_e; exact absurd htop_e htop
          · rintro (rfl | rfl)
            · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
              exact ⟨(hUuniq Δ hΔp).2 (Or.inr rfl), by rw [hbΔ]; exact hnot_eq⟩
            · rw [show p - Δ + Δ = p by omega, Nat.mod_eq_of_lt (by omega)]
              exact ⟨by rw [hexU.2.1]; exact (hUuniq 0 hexp.1).2 (Or.inl rfl), by rw [hbp]; exact hnot_eq⟩
  · -- EVEN branch: `ExactPeriod ... (2 * p)` — monodromy is ALWAYS `id`!
    rcases hhits with hnone | ⟨r, Δ, hΔ0, hΔp, hΔeven, huniq⟩
    · have hmono : monodromy (fLsbGen τ) k (truncPair k s) (2 * p) = Aff2.id := by
        rw [monodromy_fLsbGen_no_hits τ k (2 * p) (truncPair k s) hnone, Aff2.J0_pow_two_mul]
      have hfix1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k s) (2 * p)) 1) (topBitPair k s) =
          topBitPair k s := by rw [hmono]; simp [Aff2.pow, Aff2.comp_id, Aff2.apply_id]
      right
      refine ⟨p, hdvd, hodd,
              ⟨by omega, by simpa using (feistel_period_lift (fLsbGen τ) k (2 * p) 1 s hex2p.2.1).2 hfix1, ?_⟩,
              Or.inl ?_⟩
      · intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
        exact hex2p.2.2 q hq0 hqlt this
      · intro t ht heq
        rw [eq_triggerPrefix_succ_iff, htr s t] at heq
        exact hnone t ht heq.1
    · let U := feistelIter (fLsbGen τ) (k + 1) r s
      have htrU : truncPair k U = feistelIter (fLsbGen τ) k r (truncPair k s) :=
        feistelIter_truncate (fLsbGen τ) k r s
      have hexU : ExactPeriod (fLsbGen τ) k (truncPair k U) (2 * p) := by
        rw [htrU]; exact (exactPeriod_shift (fLsbGen τ) k (2 * p) r (truncPair k s)).2 hex2p
      have hUuniq : ∀ t, t < 2 * p → ((feistelIter (fLsbGen τ) k t (truncPair k U)).2 = triggerPrefix τ k ↔ t = 0 ∨ t = Δ) := by
        intro t ht; rw [htrU]; exact huniq t ht
      have ⟨hmΔ, hmono⟩ := monodromy_fLsbGen_two_even_hits τ k (2 * p) Δ (truncPair k U) (by omega) hΔ0 hΔp hΔeven hUuniq
      have hfix1 : Aff2.apply (Aff2.pow (monodromy (fLsbGen τ) k (truncPair k U) (2 * p)) 1) (topBitPair k U) =
          topBitPair k U := by rw [hmono]; simp [Aff2.pow, Aff2.comp_id, Aff2.apply_id]
      have hexU' : ExactPeriod (fLsbGen τ) (k + 1) U (2 * p) := by
        refine ⟨by omega, by simpa using (feistel_period_lift (fLsbGen τ) k (2 * p) 1 U hexU.2.1).2 hfix1, ?_⟩
        intro q hq0 hqlt hqfix
        have := congrArg (truncPair k) hqfix; rw [feistelIter_truncate] at this
        exact hexU.2.2 q hq0 hqlt this
      have hbΔ : (feistelIter (fLsbGen τ) (k + 1) Δ U).2.getLsbD k = U.2.getLsbD k := by
        have ht := congrArg Prod.snd (feistelIter_topBit (fLsbGen τ) k Δ U)
        rw [hmΔ] at ht
        change (topBitPair k (feistelIter (fLsbGen τ) (k + 1) Δ U)).2 = (topBitPair k U).2
        rw [ht]; rcases topBitPair k U with ⟨a, b⟩; cases a <;> cases b <;> rfl
      right
      refine ⟨p, hdvd, hodd, (exactPeriod_shift (fLsbGen τ) (k + 1) (2 * p) r s).1 hexU', ?_⟩
      by_cases htop : U.2.getLsbD k = τ k
      · right
        refine ⟨r, Δ, hΔ0, hΔp, hΔeven, fun t ht => ?_⟩
        change (feistelIter (fLsbGen τ) (k + 1) t U).2 = triggerPrefix τ (k + 1) ↔ t = 0 ∨ t = Δ
        rw [eq_triggerPrefix_succ_iff, htr U t]
        constructor
        · rintro ⟨htr_e, _⟩; exact (hUuniq t ht).1 htr_e
        · rintro (ht0 | htΔ)
          · rw [ht0]; exact ⟨(hUuniq 0 (by omega)).2 (Or.inl rfl), htop⟩
          · rw [htΔ]; exact ⟨(hUuniq Δ hΔp).2 (Or.inr rfl), by rw [hbΔ]; exact htop⟩
      · left
        intro t ht heq
        have hex_s' := (exactPeriod_shift (fLsbGen τ) (k + 1) (2 * p) r s).1 hexU'
        let t' := (t + (2 * p - r % (2 * p))) % (2 * p)
        have hsh : feistelIter (fLsbGen τ) (k + 1) t s = feistelIter (fLsbGen τ) (k + 1) t' U := by
          simp only [U, ← feistelIter_add]
          rw [feistelIter_eq_mod (fLsbGen τ) (k + 1) (2 * p) (t' + r) s hex_s'.2.1]
          have hmod : (t' + r) % (2 * p) = t := by
            have h1 : (t' + r) % (2 * p) = (t' + r % (2 * p)) % (2 * p) := by rw [Nat.add_mod_mod]
            rw [h1]; simp only [t']; rw [Nat.mod_add_mod]
            have hrlt : r % (2 * p) < 2 * p := Nat.mod_lt r (by omega)
            have h2 : t + (2 * p - r % (2 * p)) + r % (2 * p) = t + 1 * (2 * p) := by omega
            rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
          rw [hmod]
        rw [hsh, eq_triggerPrefix_succ_iff, htr U t'] at heq
        rcases (hUuniq t' (Nat.mod_lt _ (by omega))).1 heq.1 with h0 | hΔ
        · rw [h0] at heq; exact htop heq.2
        · rw [hΔ, hbΔ] at heq; exact htop heq.2

/-- **THEOREM IIIb (Sharp `ctz(τ)` Period-Lock Phase Transition):**
    For EVERY 2-adic trigger `τ : Nat → Bool` with first `true` bit at index `m`
    (`∀ j < m, τ j = false` and `τ m = true`), the exponential `3^w` growth of Theorem IIIa
    SHARPLY COLLAPSES into a constant global period lock at `2 * 3^(m+1)`:
    for EVERY bit-width `w ≥ 1` and EVERY state `s ∈ (BitVec w)^2`,
    `feistelIter (fLsbGen τ) w (2 * 3^(m+1)) s = s`. -/
theorem theorem_IIIb_ctz_period_lock (τ : Nat → Bool) (m : Nat)
    (hpre : ∀ j, j < m → τ j = false) (hm : τ m = true) :
    ∀ (w : Nat), 1 ≤ w → ∀ (s : BitVec w × BitVec w),
      feistelIter (fLsbGen τ) w (2 * 3 ^ (m + 1)) s = s := by
  have hge : ∀ d (s : BitVec (m + 1 + d) × BitVec (m + 1 + d)), CtzPhaseInv τ m (m + 1 + d) s := by
    intro d
    induction d with
    | zero => exact ctzPhaseInv_entry τ m hpre hm
    | succ d ih =>
      intro s
      exact ctzPhaseInv_step τ m (m + 1 + d) s (ih (truncPair (m + 1 + d) s))
  intro w hw s
  by_cases hle : w ≤ m
  · have hinv := lsbZeroInv_all τ w (fun j hj => hpre j (by omega)) s
    have hdiv : 2 * 3 ^ (m + 1) = (2 * 3 ^ (m + 1 - hinv.exp)) * 3 ^ hinv.exp := by
      have h1 : hinv.exp ≤ m + 1 := Nat.le_trans hinv.exp_le (by omega)
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel h1]
    rw [hdiv]
    exact feistelIter_mul_of_fixed (fLsbGen τ) w (3 ^ hinv.exp) s hinv.exact_per.2.1 _
  · have hd : ∃ d, w = m + 1 + d := ⟨w - (m + 1), by omega⟩
    rcases hd with ⟨d, rfl⟩
    rcases hge d s with ⟨p, ⟨q, hq⟩, _, hex, _⟩ | ⟨p, ⟨q, hq⟩, _, hex, _⟩
    · have hdiv : 2 * 3 ^ (m + 1) = (2 * q) * p := by rw [hq]; ac_rfl
      rw [hdiv]; exact feistelIter_mul_of_fixed (fLsbGen τ) _ p s hex.2.1 (2 * q)
    · have hdiv : 2 * 3 ^ (m + 1) = q * (2 * p) := by rw [hq]; ac_rfl
      rw [hdiv]; exact feistelIter_mul_of_fixed (fLsbGen τ) _ (2 * p) s hex.2.1 q

/-- Concrete Hardware Corollary IIIb: the trailing-ones Feistel map
    `(L, R) ↦ (R, L ^^^ (R &&& ~~~(R + 1)))` (`τ ≡ true`, `ctz = 0`) locks universally
    to period 6 for ALL bit-widths `w ≥ 1` (contrasting directly with `R &&& (-R)` which
    has unbounded period `3^w`!). -/
theorem corollary_IIIb_hw_trail_ones_period6 (w : Nat) (hw : 1 ≤ w) (s : BitVec w × BitVec w) :
    hwFeistelIter (fun w R => R &&& ~~~(R + 1#w)) w 6 s = s := by
  rw [hwFeistelIter_eq_feistelIter _ _ hw_trail_ones_eq]
  exact theorem_IIIb_ctz_period_lock (fun _ => true) 0 (fun _ h => by omega) rfl w hw s

end TheoremIII

/-! ## Part 9: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples -/

section NonVacuityAndSharpness

/-- Non-Vacuity Witness 1: Theorem I (`R ||| (R + 1)`) genuinely attains exact period 12 at `w = 2`. -/
theorem witness_nonvac_period12_exact :
    hwFeistelIter (fun w R => R ||| (R + 1#w)) 2 12 (0#2, 1#2) = (0#2, 1#2) ∧
    hwFeistelIter (fun w R => R ||| (R + 1#w)) 2 4 (0#2, 1#2) ≠ (0#2, 1#2) ∧
    hwFeistelIter (fun w R => R ||| (R + 1#w)) 2 6 (0#2, 1#2) ≠ (0#2, 1#2) := by
  decide

/-- Non-Vacuity Witness 2: Theorem IIa (`R + 1`) genuinely attains exact period 6 at `w = 2`. -/
theorem witness_nonvac_period6_exact :
    hwFeistelIter (fun w R => R + 1#w) 2 6 (0#2, 0#2) = (0#2, 0#2) ∧
    hwFeistelIter (fun w R => R + 1#w) 2 2 (0#2, 0#2) ≠ (0#2, 0#2) ∧
    hwFeistelIter (fun w R => R + 1#w) 2 3 (0#2, 0#2) ≠ (0#2, 0#2) := by
  decide

/-- Non-Vacuity Witness 3: Theorem IIIa (`R &&& (-R)`) attains exact period `3^3 = 27` at `w = 3`. -/
theorem witness_nonvac_lsb_27 :
    hwFeistelIter (fun _ R => R &&& (-R)) 3 27 (7#3, 0#3) = (7#3, 0#3) ∧
    hwFeistelIter (fun _ R => R &&& (-R)) 3 9 (7#3, 0#3) ≠ (7#3, 0#3) := by
  decide

/-- Non-Vacuity Witness 4: Theorem IIIb (`ctz(τ) = 1`, `τ = 2`) attains exact period `2 * 3^2 = 18` at `w = 3`. -/
theorem witness_nonvac_ctz1_exact18 :
    let τ : Nat → Bool := fun k => decide (k = 1)
    feistelIter (fLsbGen τ) 3 18 (2#3, 5#3) = (2#3, 5#3) ∧
    feistelIter (fLsbGen τ) 3 9 (2#3, 5#3) ≠ (2#3, 5#3) ∧
    feistelIter (fLsbGen τ) 3 6 (2#3, 5#3) ≠ (2#3, 5#3) := by
  decide

/-- Non-Vacuity Witness 5: Theorem IIIb hardware corollary `R &&& ~~~(R + 1)` attains exact period 6 at `w = 2`. -/
theorem witness_nonvac_trail_ones_6 :
    hwFeistelIter (fun w R => R &&& ~~~(R + 1#w)) 2 6 (2#2, 1#2) = (2#2, 1#2) ∧
    hwFeistelIter (fun w R => R &&& ~~~(R + 1#w)) 2 2 (2#2, 1#2) ≠ (2#2, 1#2) ∧
    hwFeistelIter (fun w R => R &&& ~~~(R + 1#w)) 2 3 (2#2, 1#2) ≠ (2#2, 1#2) := by
  decide

/-- Sharpness Counterexample 1: Replacing `+ 1` by `+ 3` in Theorem I (`R ||| (R + 3)`)
    breaks the period-12 lock already at `w = 3` (state `(0#3, 1#3)` has period 36 > 12). -/
theorem sharpness_or_add3_breaks_period12 :
    hwFeistelIter (fun w R => R ||| (R + 3#w)) 3 12 (0#3, 1#3) ≠ (0#3, 1#3) ∧
    hwFeistelIter (fun w R => R ||| (R + 3#w)) 3 36 (0#3, 1#3) = (0#3, 1#3) := by
  decide

/-- Sharpness Counterexample 2: Flipping 1 rule bit from `(1,0,0,1)` to `(1,0,0,0)`
    (`R &&& (R - 1)`, clear lowest set bit) breaks the period-12 lock at `w = 4` (period 16). -/
theorem sharpness_clear_lsb_breaks_period12 :
    hwFeistelIter (fun w R => R &&& (R - 1#w)) 4 12 (0#4, 15#4) ≠ (0#4, 15#4) ∧
    hwFeistelIter (fun w R => R &&& (R - 1#w)) 4 16 (0#4, 15#4) = (0#4, 15#4) := by
  decide

/-- Sharpness Counterexample 3: Replacing `+ 1` by `+ 2` (even carry) in Theorem IV
    (`R ^^^ (R + 2)`) breaks the `2^(w+1)` isoperiodic law at `w = 2` (collapses to period 4). -/
theorem sharpness_xor_add2_breaks_isoperiodic :
    hwFeistelIter (fun w R => R ^^^ (R + 2#w)) 2 4 (0#2, 0#2) = (0#2, 0#2) := by
  decide

/-- Sharpness Counterexample 4: Violating triangularity with a right-shift
    `f(R) = R + (R >>> 1)` breaks the Universal `2^a * 3^b` Period Law at `w = 2`:
    state `(1#2, 2#2)` has exact prime period `5` (neither 2 nor 3 divides 5!). -/
theorem sharpness_right_shift_breaks_2_3_law :
    hwFeistelIter (fun _ R => R + (R >>> 1)) 2 5 (1#2, 2#2) = (1#2, 2#2) ∧
    hwFeistelIter (fun _ R => R + (R >>> 1)) 2 1 (1#2, 2#2) ≠ (1#2, 2#2) ∧
    hwFeistelIter (fun _ R => R + (R >>> 1)) 2 2 (1#2, 2#2) ≠ (1#2, 2#2) ∧
    hwFeistelIter (fun _ R => R + (R >>> 1)) 2 3 (1#2, 2#2) ≠ (1#2, 2#2) ∧
    hwFeistelIter (fun _ R => R + (R >>> 1)) 2 4 (1#2, 2#2) ≠ (1#2, 2#2) := by
  decide

end NonVacuityAndSharpness

end FeistelMonodromy

/-! ## Part 10: Kernel Axiom Verification Receipts (`#print axioms`) -/



