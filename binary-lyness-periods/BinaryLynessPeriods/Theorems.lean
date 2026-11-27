/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BinaryLynessPeriods.Defs

/-!
# Proofs of the Binary Lyness Period-6 & Period-12 Dichotomies (Pure `Init`)

Proves all five headline theorems constructively using only Lean 4's core `Init` library
(zero Mathlib, zero `Classical.choice`).
-/

namespace BinaryLynessPeriods

/-! ## Section 1: Pure-`Init` Bitwise Helpers -/

theorem testBit_two_mul_add_zero (a b : Nat) (hb : b < 2) :
    (2 * a + b).testBit 0 = (b == 1) := by
  rw [Nat.testBit_zero]
  have hmod : (2 * a + b) % 2 = b := by omega
  rw [hmod]
  cases b with
  | zero => rfl
  | succ b' =>
    have : b' = 0 := by omega
    subst this; rfl

theorem testBit_two_mul_add_succ (a b r : Nat) (hb : b < 2) :
    (2 * a + b).testBit (r + 1) = a.testBit r := by
  rw [Nat.testBit_succ]
  have hdiv : (2 * a + b) / 2 = a := by omega
  rw [hdiv]

theorem xor_two_mul_add (a b c d : Nat) (hb : b < 2) (hd : d < 2) :
    (2 * a + b) ^^^ (2 * c + d) = 2 * (a ^^^ c) + (b ^^^ d) := by
  have hbd : b ^^^ d < 2 := by
    have hb2 : b = 0 ∨ b = 1 := by omega
    have hd2 : d = 0 ∨ d = 1 := by omega
    rcases hb2 with rfl | rfl <;> rcases hd2 with rfl | rfl <;> decide
  apply Nat.eq_of_testBit_eq
  intro r
  cases r with
  | zero =>
    rw [Nat.testBit_xor, testBit_two_mul_add_zero a b hb, testBit_two_mul_add_zero c d hd,
        testBit_two_mul_add_zero (a ^^^ c) (b ^^^ d) hbd]
    have hb2 : b = 0 ∨ b = 1 := by omega
    have hd2 : d = 0 ∨ d = 1 := by omega
    rcases hb2 with rfl | rfl <;> rcases hd2 with rfl | rfl <;> decide
  | succ r' =>
    rw [Nat.testBit_xor, testBit_two_mul_add_succ a b r' hb, testBit_two_mul_add_succ c d r' hd,
        testBit_two_mul_add_succ (a ^^^ c) (b ^^^ d) r' hbd, Nat.testBit_xor]

theorem xor_two_mul (a c : Nat) : (2 * a) ^^^ (2 * c) = 2 * (a ^^^ c) := by
  have h := xor_two_mul_add a 0 c 0 (by omega) (by omega)
  simpa using h

theorem xor_two_mul_even_odd (a c : Nat) :
    (2 * a) ^^^ (2 * c + 1) = 2 * (a ^^^ c) + 1 := by
  have h := xor_two_mul_add a 0 c 1 (by omega) (by omega)
  simpa using h

theorem xor_two_mul_odd_even (a c : Nat) :
    (2 * a + 1) ^^^ (2 * c) = 2 * (a ^^^ c) + 1 := by
  have h := xor_two_mul_add a 1 c 0 (by omega) (by omega)
  simpa using h

theorem xor_two_mul_odd_odd (a c : Nat) :
    (2 * a + 1) ^^^ (2 * c + 1) = 2 * (a ^^^ c) := by
  have h := xor_two_mul_add a 1 c 1 (by omega) (by omega)
  simpa using h

theorem or_two_mul_add (a b c d : Nat) (hb : b < 2) (hd : d < 2) :
    (2 * a + b) ||| (2 * c + d) = 2 * (a ||| c) + (b ||| d) := by
  have hbd : b ||| d < 2 := by
    have hb2 : b = 0 ∨ b = 1 := by omega
    have hd2 : d = 0 ∨ d = 1 := by omega
    rcases hb2 with rfl | rfl <;> rcases hd2 with rfl | rfl <;> decide
  apply Nat.eq_of_testBit_eq
  intro r
  cases r with
  | zero =>
    rw [Nat.testBit_or, testBit_two_mul_add_zero a b hb, testBit_two_mul_add_zero c d hd,
        testBit_two_mul_add_zero (a ||| c) (b ||| d) hbd]
    have hb2 : b = 0 ∨ b = 1 := by omega
    have hd2 : d = 0 ∨ d = 1 := by omega
    rcases hb2 with rfl | rfl <;> rcases hd2 with rfl | rfl <;> decide
  | succ r' =>
    rw [Nat.testBit_or, testBit_two_mul_add_succ a b r' hb, testBit_two_mul_add_succ c d r' hd,
        testBit_two_mul_add_succ (a ||| c) (b ||| d) r' hbd, Nat.testBit_or]

theorem xor_cancel_right (a b : Nat) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_cancel_left (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem xor_mod_two_pow (a b m : Nat) :
    (a ^^^ b) % 2 ^ m = (a % 2 ^ m) ^^^ (b % 2 ^ m) := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases h : r < m <;> simp [h]

theorem add_two_pow_eq_xor {a k : Nat} (ha : a < 2 ^ k) : a + 2 ^ k = a ^^^ 2 ^ k := by
  induction k generalizing a with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; rfl
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hdiv_lt : a / 2 < 2 ^ k := by omega
    have h1 : a + 2 ^ (k + 1) = 2 * (a / 2 + 2 ^ k) + a % 2 := by omega
    have h2 : a ^^^ 2 ^ (k + 1) = 2 * (a / 2 ^^^ 2 ^ k) + a % 2 := by
      have ha_eq : a = 2 * (a / 2) + a % 2 := by omega
      have hp_eq : 2 ^ (k + 1) = 2 * 2 ^ k + 0 := by omega
      calc a ^^^ 2 ^ (k + 1)
          = (2 * (a / 2) + a % 2) ^^^ (2 * 2 ^ k + 0) := by rw [← ha_eq, ← hp_eq]
        _ = 2 * (a / 2 ^^^ 2 ^ k) + (a % 2 ^^^ 0) := xor_two_mul_add _ _ _ _ (by omega) (by omega)
        _ = 2 * (a / 2 ^^^ 2 ^ k) + a % 2 := by rw [Nat.xor_zero]
    rw [h1, h2, ih hdiv_lt]

theorem iter_add {α : Type} (g : α → α) (m n : Nat) (x : α) :
    iter g (m + n) x = iter g n (iter g m x) := by
  induction m generalizing x with
  | zero => simp [iter]
  | succ m ih =>
    have : m + 1 + n = (m + n) + 1 := by omega
    rw [this]
    exact ih (g x)

theorem iter_comm_step {α : Type} (g : α → α) (n : Nat) (x : α) :
    iter g n (g x) = g (iter g n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (g x)

/-! ## Section 2: General Carry-Renormalization Theorems (Periods 6 & 12) -/

/-- Three steps of `feistelStep f` on `(2a, 2b)` when `f(2k) = 2k + 1` and `f(2k + 1) = 2 * h k`. -/
theorem feistelStep_iter_three_even (f h : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * h k)
    (a b : Nat) :
    iter (feistelStep f) 3 (2 * a, 2 * b) =
      (2 * (b ^^^ h (a ^^^ b)), 2 * (a ^^^ h (a ^^^ b))) := by
  simp only [iter, feistelStep, heven, hodd, xor_two_mul_even_odd, xor_two_mul, xor_two_mul_odd_odd]
  have h1 : (a ^^^ b) ^^^ (b ^^^ h (a ^^^ b)) = a ^^^ h (a ^^^ b) := by
    apply Nat.eq_of_testBit_eq; intro r
    simp only [Nat.testBit_xor]
    cases a.testBit r <;> cases b.testBit r <;> cases (h (a ^^^ b)).testBit r <;> rfl
  rw [h1]

/-- Theorem 1 (General even-carry period-6 law):
for ANY `f h : Nat → Nat` with `f (2k) = 2k + 1` and `f (2k + 1) = 2 * h k`,
every pair `(x, y)` outside the odd-odd sector returns to itself in 6 steps. -/
theorem feistelStep_iter_six_of_even_parity (f h : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * h k)
    (x y : Nat) (hpar : x % 2 = 0 ∨ y % 2 = 0) :
    iter (feistelStep f) 6 (x, y) = (x, y) := by
  have h6_even : ∀ a b : Nat, iter (feistelStep f) 6 (2 * a, 2 * b) = (2 * a, 2 * b) := by
    intro a b
    rw [show (6 : Nat) = 3 + 3 from rfl, iter_add, feistelStep_iter_three_even f h heven hodd,
        feistelStep_iter_three_even f h heven hodd]
    have hinv : (b ^^^ h (a ^^^ b)) ^^^ (a ^^^ h (a ^^^ b)) = a ^^^ b := by
      apply Nat.eq_of_testBit_eq; intro r
      simp only [Nat.testBit_xor]
      cases a.testBit r <;> cases b.testBit r <;> cases (h (a ^^^ b)).testBit r <;> rfl
    rw [hinv, xor_cancel_right, xor_cancel_right]
  by_cases hx : x % 2 = 0
  · by_cases hy : y % 2 = 0
    · rw [show x = 2 * (x / 2) by omega, show y = 2 * (y / 2) by omega]
      exact h6_even (x / 2) (y / 2)
    · have hpre : feistelStep f (2 * (y / 2 ^^^ x / 2), 2 * (x / 2)) = (x, y) := by
        simp only [feistelStep, heven, xor_two_mul_even_odd, xor_cancel_right]
        exact Prod.ext (by omega) (by omega)
      rw [← hpre, iter_comm_step, h6_even]
  · have hy : y % 2 = 0 := by omega
    let u := x / 2
    let b := y / 2 ^^^ h u
    let a := u ^^^ b
    have hpre : iter (feistelStep f) 2 (2 * a, 2 * b) = (x, y) := by
      simp only [iter, feistelStep, heven, hodd, xor_two_mul_even_odd, xor_two_mul]
      have hab : a ^^^ b = u := xor_cancel_right u b
      have hbh : b ^^^ h u = y / 2 := xor_cancel_right (y / 2) (h u)
      rw [hab, hbh]
      exact Prod.ext (by omega) (by omega)
    rw [← hpre, ← iter_add, show 2 + 6 = 6 + 2 from rfl, iter_add, h6_even]

/-- Four steps of `feistelStep f` on `(2a, 2b)` when `f(2k) = 2k + 1` and `f(2k + 1) = 2 * g k + 1`:
under `(a, b) ↦ (u, v) = (a ^^^ b, b ^^^ g(a ^^^ b))`, `F^4` acts as pure linear Fibonacci `(u, v) ↦ (v, u ^^^ v)`. -/
theorem feistelStep_iter_four_odd_parity (f g : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * g k + 1)
    (a b : Nat) :
    iter (feistelStep f) 4 (2 * a, 2 * b) =
      (2 * ((a ^^^ b) ^^^ g (b ^^^ g (a ^^^ b))),
       2 * ((b ^^^ g (a ^^^ b)) ^^^ ((a ^^^ b) ^^^ g (b ^^^ g (a ^^^ b))))) := by
  simp only [iter, feistelStep, heven, hodd, xor_two_mul_even_odd, xor_two_mul_odd_odd]

/-- Theorem 2 (General odd-carry period-12 law):
for ANY `f g : Nat → Nat` with `f (2k) = 2k + 1` and `f (2k + 1) = 2 * g k + 1`,
EVERY pair `(x, y) : Nat × Nat` returns to itself in 12 steps. -/
theorem feistelStep_iter_twelve_of_odd_parity (f g : Nat → Nat)
    (heven : ∀ k, f (2 * k) = 2 * k + 1)
    (hodd : ∀ k, f (2 * k + 1) = 2 * g k + 1)
    (x y : Nat) :
    iter (feistelStep f) 12 (x, y) = (x, y) := by
  have h12_even : ∀ a b : Nat, iter (feistelStep f) 12 (2 * a, 2 * b) = (2 * a, 2 * b) := by
    intro a b
    let u := a ^^^ b
    let v := b ^^^ g u
    have h4 : iter (feistelStep f) 4 (2 * a, 2 * b) = (2 * (u ^^^ g v), 2 * (v ^^^ (u ^^^ g v))) :=
      feistelStep_iter_four_odd_parity f g heven hodd a b
    have hu1 : (u ^^^ g v) ^^^ (v ^^^ (u ^^^ g v)) = v := by
      apply Nat.eq_of_testBit_eq; intro r; simp only [Nat.testBit_xor]
      cases u.testBit r <;> cases v.testBit r <;> cases (g v).testBit r <;> rfl
    have hv1 : (v ^^^ (u ^^^ g v)) ^^^ g v = u ^^^ v := by
      apply Nat.eq_of_testBit_eq; intro r; simp only [Nat.testBit_xor]
      cases u.testBit r <;> cases v.testBit r <;> cases (g v).testBit r <;> rfl
    have h8 : iter (feistelStep f) 8 (2 * a, 2 * b) =
        (2 * (v ^^^ g (u ^^^ v)), 2 * ((u ^^^ v) ^^^ (v ^^^ g (u ^^^ v)))) := by
      rw [show (8 : Nat) = 4 + 4 from rfl, iter_add, h4,
          feistelStep_iter_four_odd_parity f g heven hodd, hu1, hv1]
    have hu2 : (v ^^^ g (u ^^^ v)) ^^^ ((u ^^^ v) ^^^ (v ^^^ g (u ^^^ v))) = u ^^^ v := by
      apply Nat.eq_of_testBit_eq; intro r; simp only [Nat.testBit_xor]
      cases u.testBit r <;> cases v.testBit r <;> cases (g (u ^^^ v)).testBit r <;> rfl
    have hv2 : ((u ^^^ v) ^^^ (v ^^^ g (u ^^^ v))) ^^^ g (u ^^^ v) = u := by
      apply Nat.eq_of_testBit_eq; intro r; simp only [Nat.testBit_xor]
      cases u.testBit r <;> cases v.testBit r <;> cases (g (u ^^^ v)).testBit r <;> rfl
    have h12 : iter (feistelStep f) 12 (2 * a, 2 * b) =
        (2 * ((u ^^^ v) ^^^ g u), 2 * (u ^^^ ((u ^^^ v) ^^^ g u))) := by
      rw [show (12 : Nat) = 8 + 4 from rfl, iter_add, h8,
          feistelStep_iter_four_odd_parity f g heven hodd, hu2, hv2]
    rw [h12]
    have ha_back : (u ^^^ v) ^^^ g u = a := by
      apply Nat.eq_of_testBit_eq; intro r; simp only [u, v, Nat.testBit_xor]
      cases a.testBit r <;> cases b.testBit r <;> cases (g (a ^^^ b)).testBit r <;> rfl
    have hb_back : u ^^^ a = b := by
      apply Nat.eq_of_testBit_eq; intro r; simp only [u, Nat.testBit_xor]
      cases a.testBit r <;> cases b.testBit r <;> rfl
    rw [ha_back, hb_back]
  -- Invert feistelStep f to hit an even-even pair in ≤ 3 inverse steps!
  let inv : Nat × Nat → Nat × Nat := fun p => (p.2 ^^^ f p.1, p.1)
  have hright : ∀ p, feistelStep f (inv p) = p := by
    intro ⟨a, b⟩
    simp only [feistelStep, inv, xor_cancel_right]
  have h12_of_step : ∀ p, iter (feistelStep f) 12 p = p →
      iter (feistelStep f) 12 (feistelStep f p) = feistelStep f p := by
    intro p hp; rw [iter_comm_step, hp]
  have hstep_par : ∀ p : Nat × Nat,
      (inv p).1 % 2 = (p.2 + 1) % 2 ∧ (inv p).2 % 2 = p.1 % 2 := by
    intro ⟨a, b⟩
    have hf_odd : f a % 2 = 1 := by
      by_cases ha : a % 2 = 0
      · rw [show a = 2 * (a / 2) by omega, heven]; omega
      · rw [show a = 2 * (a / 2) + 1 by omega, hodd]; omega
    have hxor_mod : (b ^^^ f a) % 2 = (b + 1) % 2 := by
      have h1 : b = 2 * (b / 2) + b % 2 := by omega
      have h2 : f a = 2 * (f a / 2) + 1 := by omega
      have h3 : b ^^^ f a = 2 * (b / 2 ^^^ f a / 2) + (b % 2 ^^^ 1) := by
        calc b ^^^ f a = (2 * (b / 2) + b % 2) ^^^ (2 * (f a / 2) + 1) := by rw [← h1, ← h2]
          _ = 2 * (b / 2 ^^^ f a / 2) + (b % 2 ^^^ 1) := xor_two_mul_add _ _ _ _ (by omega) (by omega)
      rw [h3]
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases hb2 with h0 | h1'
      · rw [h0, Nat.zero_xor]; omega
      · rw [h1', Nat.xor_self]; omega
    exact ⟨hxor_mod, rfl⟩
  have h12_of_even_pair : ∀ p : Nat × Nat, p.1 % 2 = 0 → p.2 % 2 = 0 →
      iter (feistelStep f) 12 p = p := by
    intro ⟨a, b⟩ ha hb
    rw [show a = 2 * (a / 2) by omega, show b = 2 * (b / 2) by omega]
    exact h12_even (a / 2) (b / 2)
  by_cases hx : x % 2 = 0
  · by_cases hy : y % 2 = 0
    · exact h12_of_even_pair (x, y) hx hy
    · have hp1 := hstep_par (x, y)
      have h12_p1 := h12_of_even_pair (inv (x, y)) (by omega) (by omega)
      have h0 := h12_of_step (inv (x, y)) h12_p1
      rwa [hright] at h0
  · by_cases hy : y % 2 = 0
    · have hp1 := hstep_par (x, y)
      have hp2 := hstep_par (inv (x, y))
      have hp3 := hstep_par (inv (inv (x, y)))
      have h12_p3 := h12_of_even_pair (inv (inv (inv (x, y)))) (by omega) (by omega)
      have h12_p2 := h12_of_step _ h12_p3; rw [hright] at h12_p2
      have h12_p1 := h12_of_step _ h12_p2; rw [hright] at h12_p1
      have h12_p0 := h12_of_step _ h12_p1; rwa [hright] at h12_p0
    · have hp1 := hstep_par (x, y)
      have hp2 := hstep_par (inv (x, y))
      have h12_p2 := h12_of_even_pair (inv (inv (x, y))) (by omega) (by omega)
      have h12_p1 := h12_of_step _ h12_p2; rw [hright] at h12_p1
      have h12_p0 := h12_of_step _ h12_p1; rwa [hright] at h12_p0

/-! ## Section 3: Exact Power-of-Two Period-6 Dichotomy for Binary Lyness -/

/-- Exact period 6 at `c = 1` over unbounded `Nat × Nat`, by strong induction on `x + y`. -/
theorem lynessStep_one_period_six (x y : Nat) :
    iter (lynessStep 1) 6 (x, y) = (x, y) := by
  suffices h : ∀ s x y : Nat, x + y = s → iter (lynessStep 1) 6 (x, y) = (x, y) from
    h (x + y) x y rfl
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro x y hsum
    by_cases hpar : x % 2 = 0 ∨ y % 2 = 0
    · exact feistelStep_iter_six_of_even_parity (fun k => k + 1) (fun k => k + 1)
        (fun _ => rfl) (fun k => by omega) x y hpar
    · let a := x / 2
      let b := y / 2
      have hlift : ∀ n u v : Nat,
          iter (lynessStep 1) n (2 * u + 1, 2 * v + 1) =
            (2 * (iter (lynessStep 1) n (u, v)).1 + 1,
             2 * (iter (lynessStep 1) n (u, v)).2 + 1) := by
        intro n
        induction n with
        | zero => intro u v; rfl
        | succ n ihn =>
          intro u v
          simp only [iter, lynessStep, feistelStep]
          have hstep : (2 * u + 1) ^^^ (2 * v + 1 + 1) = 2 * (u ^^^ (v + 1)) + 1 := by
            rw [show 2 * v + 1 + 1 = 2 * (v + 1) by omega, xor_two_mul_odd_even]
          rw [hstep]
          exact ihn v (u ^^^ (v + 1))
      have hih := ih (a + b) (by omega) a b rfl
      rw [show x = 2 * a + 1 by omega, show y = 2 * b + 1 by omega, hlift, hih]

/-- Pure `XOR` (`c = 0`) has period 3 (hence period 6). -/
theorem lynessStep_zero_period_three (x y : Nat) :
    iter (lynessStep 0) 3 (x, y) = (x, y) := by
  simp only [iter, lynessStep, feistelStep, Nat.add_zero]
  have h1 : y ^^^ (x ^^^ y) = x := by
    rw [Nat.xor_comm x y, xor_cancel_left]
  rw [h1, Nat.xor_comm x y, xor_cancel_right]

/-- Bit-0 product splitting for `lynessStep (2 * c)`. -/
theorem lynessStep_two_mul_split (c n x y : Nat) :
    iter (lynessStep (2 * c)) n (x, y) =
      (2 * (iter (lynessStep c) n (x / 2, y / 2)).1 + (iter (lynessStep 0) n (x % 2, y % 2)).1,
       2 * (iter (lynessStep c) n (x / 2, y / 2)).2 + (iter (lynessStep 0) n (x % 2, y % 2)).2) := by
  induction n generalizing x y with
  | zero =>
    simp only [iter]
    exact Prod.ext (by omega) (by omega)
  | succ n ih =>
    simp only [iter, lynessStep, feistelStep, Nat.add_zero]
    have hstep : x ^^^ (y + 2 * c) =
        2 * (x / 2 ^^^ (y / 2 + c)) + (x % 2 ^^^ y % 2) := by
      have hx : x = 2 * (x / 2) + x % 2 := by omega
      have hy : y + 2 * c = 2 * (y / 2 + c) + y % 2 := by omega
      calc x ^^^ (y + 2 * c)
          = (2 * (x / 2) + x % 2) ^^^ (2 * (y / 2 + c) + y % 2) := by rw [← hx, ← hy]
        _ = 2 * (x / 2 ^^^ (y / 2 + c)) + (x % 2 ^^^ y % 2) :=
            xor_two_mul_add _ _ _ _ (by omega) (by omega)
    have hlt2 : x % 2 ^^^ y % 2 < 2 := by
      have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hx2 with h1 | h1 <;> rcases hy2 with h2 | h2 <;> rw [h1, h2] <;> decide
    have hdiv : (x ^^^ (y + 2 * c)) / 2 = x / 2 ^^^ (y / 2 + c) := by rw [hstep]; omega
    have hmod : (x ^^^ (y + 2 * c)) % 2 = x % 2 ^^^ y % 2 := by rw [hstep]; omega
    have hnext := ih y (x ^^^ (y + 2 * c))
    rw [hdiv, hmod] at hnext
    exact hnext

/-- Theorem 3 (Universal period 6 for Binary Lyness at every power of 2):
for every `r : Nat` and all `x y : Nat`, `F_{2^r}^6(x, y) = (x, y)`. -/
theorem lynessStep_pow_two_period_six (r x y : Nat) :
    iter (lynessStep (2 ^ r)) 6 (x, y) = (x, y) := by
  induction r generalizing x y with
  | zero => exact lynessStep_one_period_six x y
  | succ r ih =>
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, lynessStep_two_mul_split, ih]
    have h06 : iter (lynessStep 0) 6 (x % 2, y % 2) = (x % 2, y % 2) := by
      rw [show (6 : Nat) = 3 + 3 from rfl, iter_add, lynessStep_zero_period_three,
          lynessStep_zero_period_three]
    rw [h06]
    exact Prod.ext (by omega) (by omega)

/-- Causal modularity: `lynessStep c` commutes with reduction modulo `2 ^ m`. -/
theorem lynessStep_iter_mod (c m n x y : Nat) :
    ((iter (lynessStep c) n (x, y)).1 % 2 ^ m, (iter (lynessStep c) n (x, y)).2 % 2 ^ m) =
      ((iter (lynessStep (c % 2 ^ m)) n (x % 2 ^ m, y % 2 ^ m)).1 % 2 ^ m,
       (iter (lynessStep (c % 2 ^ m)) n (x % 2 ^ m, y % 2 ^ m)).2 % 2 ^ m) := by
  induction n generalizing x y with
  | zero => simp [iter]
  | succ n ih =>
    simp only [iter, lynessStep, feistelStep]
    have hmod_eq : (x ^^^ (y + c)) % 2 ^ m =
        (x % 2 ^ m ^^^ (y % 2 ^ m + c % 2 ^ m)) % 2 ^ m := by
      rw [xor_mod_two_pow, xor_mod_two_pow, Nat.mod_mod, Nat.add_mod, Nat.add_mod (y % 2 ^ m),
          Nat.mod_mod, Nat.mod_mod]
    have h1 := ih y (x ^^^ (y + c))
    have h2 := ih (y % 2 ^ m) (x % 2 ^ m ^^^ (y % 2 ^ m + c % 2 ^ m))
    -- The right-hand side has lynessStep (c % 2^m), so prove a 2-step version for arbitrary c1, c2 with the same residue.
    have hstep_mod : ∀ c1 c2 x1 y1 x2 y2 : Nat,
        c1 % 2 ^ m = c2 % 2 ^ m → x1 % 2 ^ m = x2 % 2 ^ m → y1 % 2 ^ m = y2 % 2 ^ m →
        ((iter (lynessStep c1) n (x1, y1)).1 % 2 ^ m, (iter (lynessStep c1) n (x1, y1)).2 % 2 ^ m) =
        ((iter (lynessStep c2) n (x2, y2)).1 % 2 ^ m, (iter (lynessStep c2) n (x2, y2)).2 % 2 ^ m) := by
      clear h1 h2 hmod_eq ih x y c
      induction n with
      | zero =>
        intro c1 c2 x1 y1 x2 y2 _ hx hy
        simp only [iter, hx, hy]
      | succ k ihk =>
        intro c1 c2 x1 y1 x2 y2 hc hx hy
        simp only [iter, lynessStep, feistelStep]
        refine ihk c1 c2 y1 (x1 ^^^ (y1 + c1)) y2 (x2 ^^^ (y2 + c2)) hc hy ?_
        rw [xor_mod_two_pow, xor_mod_two_pow, hx, Nat.add_mod y1, Nat.add_mod y2, hy, hc]
    exact hstep_mod c (c % 2 ^ m) y (x ^^^ (y + c)) (y % 2 ^ m)
      (x % 2 ^ m ^^^ (y % 2 ^ m + c % 2 ^ m)) (Nat.mod_mod _ _).symm (Nat.mod_mod _ _).symm hmod_eq

/-- Helper: every odd `c ≥ 3` can be written `c = 1 + 2^(t + 1) + s * 2^(t + 2)`. -/
private theorem odd_ge_three_decomp (c : Nat) (hodd : c % 2 = 1) (hge : 3 ≤ c) :
    ∃ t s : Nat, c = 1 + 2 ^ (t + 1) + s * 2 ^ (t + 2) := by
  have hpos : c / 2 ≥ 1 := by omega
  suffices h : ∀ q : Nat, 1 ≤ q → ∃ t s : Nat, q = 2 ^ t + s * 2 ^ (t + 1) by
    rcases h (c / 2) hpos with ⟨t, s, hq⟩
    refine ⟨t, s, ?_⟩
    have hp1 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
    have hp2 : s * 2 ^ (t + 2) = 2 * (s * 2 ^ (t + 1)) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (s * 2 ^ (t + 1)) 2]
    omega
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro hq1
    by_cases hqodd : q % 2 = 1
    · exact ⟨0, q / 2, by omega⟩
    · have hdiv_pos : 1 ≤ q / 2 := by omega
      rcases ih (q / 2) (by omega) hdiv_pos with ⟨t, s, hsub⟩
      refine ⟨t + 1, s, ?_⟩
      have hp1 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
      have hp2 : s * 2 ^ (t + 1 + 1) = 2 * (s * 2 ^ (t + 1)) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (s * 2 ^ (t + 1)) 2]
      omega

/-- Explicit witness breaking period 6 for EVERY odd `c ≥ 3`:
writing `c = 1 + H + s * 2H` (`H = 2^(t+1)`), `F_c^6(0, 2H - 2) ≡ (2H, 4H - 2) (mod 4H)`. -/
theorem lynessStep_odd_ge_three_not_period_six (c : Nat) (hodd : c % 2 = 1) (hge : 3 ≤ c) :
    ∃ x y : Nat, iter (lynessStep c) 6 (x, y) ≠ (x, y) := by
  rcases odd_ge_three_decomp c hodd hge with ⟨t, s, hc⟩
  let H := 2 ^ (t + 1)
  have hH2 : 2 ≤ H := by
    have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    change 2 ≤ 2 ^ (t + 1)
    rw [Nat.pow_succ]; omega
  have h2H : 2 ^ (t + 2) = 2 * H := by
    change 2 ^ (t + 2) = 2 * 2 ^ (t + 1)
    rw [Nat.pow_succ, Nat.mul_comm]
  have h4H : 2 ^ (t + 3) = 4 * H := by
    change 2 ^ (t + 3) = 4 * 2 ^ (t + 1)
    rw [Nat.pow_succ, Nat.pow_succ]; omega
  refine ⟨0, 2 * H - 2, ?_⟩
  intro hfix
  have hmod := congrArg (fun p : Nat × Nat => p.1 % 2 ^ (t + 3)) hfix
  have hcm := lynessStep_iter_mod c (t + 3) 6 0 (2 * H - 2)
  have hfst : (iter (lynessStep c) 6 (0, 2 * H - 2)).1 % 2 ^ (t + 3) =
      (iter (lynessStep (c % 2 ^ (t + 3))) 6 (0 % 2 ^ (t + 3), (2 * H - 2) % 2 ^ (t + 3))).1 % 2 ^ (t + 3) :=
    congrArg Prod.fst hcm
  rw [hfst] at hmod
  have h0m : (0 : Nat) % 2 ^ (t + 3) = 0 := by simp
  have hy0m : (2 * H - 2) % 2 ^ (t + 3) = 2 * H - 2 := Nat.mod_eq_of_lt (by omega)
  let b := s % 2
  have hb2 : b = 0 ∨ b = 1 := by omega
  have hc_mod : c % 2 ^ (t + 3) = 1 + H + b * (2 * H) := by
    have h1 : c = (1 + H + b * (2 * H)) + (s / 2) * (4 * H) := by
      have hs : s = b + 2 * (s / 2) := by omega
      have hmul : s * (2 * H) = b * (2 * H) + (s / 2) * (4 * H) := by
        calc s * (2 * H) = (b + 2 * (s / 2)) * (2 * H) := by rw [← hs]
          _ = b * (2 * H) + 2 * (s / 2) * (2 * H) := Nat.add_mul _ _ _
          _ = b * (2 * H) + (s / 2) * (4 * H) := by
              congr 1
              rw [Nat.mul_assoc, Nat.mul_left_comm 2 (s / 2) (2 * H)]
              congr 1; omega
      have hc' : c = 1 + H + s * (2 * H) := by rw [hc, h2H]
      omega
    rw [h4H, h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
    rcases hb2 with hb0 | hb1
    · rw [hb0]; omega
    · rw [hb1]; omega
  rw [h0m, hy0m, hc_mod] at hmod
  have hxor_key : (2 * H - 2) ^^^ (1 + H + b * (2 * H)) = (H - 1) + b * (2 * H) := by
    apply Nat.eq_of_testBit_eq
    intro u
    rw [Nat.testBit_xor]
    have htest_2Hm2 : (2 * H - 2).testBit u = decide (1 ≤ u ∧ u < t + 2) := by
      have h1 : 2 * H - 2 = 2 * (2 ^ (t + 1) - 1) := by change 2 * 2 ^ (t + 1) - 2 = _; omega
      rw [h1]
      cases u with
      | zero => simp [Nat.testBit_zero]
      | succ u' =>
        rw [Nat.testBit_succ, Nat.mul_div_right _ (by omega), Nat.testBit_two_pow_sub_one]
        by_cases hu : u' < t + 1
        · have : 1 ≤ u' + 1 ∧ u' + 1 < t + 2 := by omega
          simp [hu, this]
        · have : ¬(1 ≤ u' + 1 ∧ u' + 1 < t + 2) := by omega
          simp [hu]
    have htest_Hm1b : ((H - 1) + b * (2 * H)).testBit u =
        decide (u < t + 1 ∨ (b = 1 ∧ u = t + 2)) := by
      rcases hb2 with hb0 | hb1
      · rw [hb0, Nat.zero_mul, Nat.add_zero]
        change (2 ^ (t + 1) - 1).testBit u = _
        rw [Nat.testBit_two_pow_sub_one]
        by_cases hu : u < t + 1 <;> simp [hu]
      · rw [hb1, Nat.one_mul, ← h2H]
        rw [add_two_pow_eq_xor (by omega), Nat.testBit_xor, Nat.testBit_two_pow]
        change ((2 ^ (t + 1) - 1).testBit u ^^ decide (t + 2 = u)) = _
        rw [Nat.testBit_two_pow_sub_one]
        by_cases hu1 : u < t + 1
        · have hne : t + 2 ≠ u := by omega
          simp [hu1, hne]
        · by_cases hu2 : u = t + 2
          · subst hu2; simp [hu1]
          · have hne : t + 2 ≠ u := by omega
            simp [hu1, hu2, hne]
    have htest_c : (1 + H + b * (2 * H)).testBit u =
        decide (u = 0 ∨ u = t + 1 ∨ (b = 1 ∧ u = t + 2)) := by
      have hH_ev : H = 2 * 2 ^ t := by change 2 ^ (t + 1) = _; rw [Nat.pow_succ, Nat.mul_comm]
      have hax1 : 1 + (H + b * (2 * H)) = 1 ^^^ (H + b * (2 * H)) := by
        have hm : H + b * (2 * H) = 2 * (2 ^ t + b * H) := by
          rw [hH_ev]
          rcases hb2 with hb0 | hb1
          · rw [hb0]; omega
          · rw [hb1]; omega
        calc 1 + (H + b * (2 * H)) = 2 * (2 ^ t + b * H) + 1 := by omega
          _ = (2 * 0 + 1) ^^^ (2 * (2 ^ t + b * H)) := by rw [xor_two_mul_odd_even, Nat.zero_xor]
          _ = 1 ^^^ (H + b * (2 * H)) := by rw [← hm]
      rw [Nat.add_assoc, hax1, Nat.testBit_xor]
      have h1u : (1 : Nat).testBit u = decide (u = 0) := by
        cases u with
        | zero => rfl
        | succ u' =>
          have : (1 : Nat).testBit (u' + 1) = false :=
            Nat.testBit_lt_two_pow (by have : 1 ≤ 2 ^ u' := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega)
          simp [this]
      rw [h1u]
      rcases hb2 with hb0 | hb1
      · rw [hb0, Nat.zero_mul, Nat.add_zero]
        change (decide (u = 0) ^^ (2 ^ (t + 1)).testBit u) = _
        rw [Nat.testBit_two_pow]
        by_cases h0 : u = 0
        · subst h0; simp
        · by_cases h1 : u = t + 1
          · subst h1; simp
          · have hne : t + 1 ≠ u := by omega
            simp [h0, h1, hne]
      · rw [hb1, Nat.one_mul, ← h2H, add_two_pow_eq_xor (by omega), Nat.testBit_xor]
        change (decide (u = 0) ^^ ((2 ^ (t + 1)).testBit u ^^ (2 ^ (t + 2)).testBit u)) = _
        rw [Nat.testBit_two_pow, Nat.testBit_two_pow]
        by_cases h0 : u = 0
        · subst h0; simp
        · by_cases h1 : u = t + 1
          · subst h1; simp
          · by_cases h2 : u = t + 2
            · subst h2; simp
            · have hn1 : t + 1 ≠ u := by omega
              have hn2 : t + 2 ≠ u := by omega
              simp [h0, h1, h2, hn1, hn2]
    rw [htest_2Hm2, htest_c, htest_Hm1b]
    by_cases hu0 : u = 0
    · subst hu0; simp
    · by_cases hu1 : u < t + 1
      · have hlt2 : u < t + 2 := by omega
        have hge1 : 1 ≤ u := by omega
        have hn1 : u ≠ t + 1 := by omega
        have hn2 : u ≠ t + 2 := by omega
        simp [hu0, hu1, hlt2, hge1, hn1, hn2]
      · by_cases hut1 : u = t + 1
        · subst hut1; simp
        · by_cases hut2 : u = t + 2
          · subst hut2
            rcases hb2 with h | h <;> simp [h]
          · have hnot : ¬(1 ≤ u ∧ u < t + 2) := by omega
            simp [hu0, hu1, hut1, hut2, hnot]
  let c' := 1 + H + b * (2 * H)
  have hstep1 : lynessStep c' (0, 2 * H - 2) = (2 * H - 2, 3 * H - 1 + b * (2 * H)) := by
    simp only [lynessStep, feistelStep, Nat.zero_xor]
    exact Prod.ext rfl (by change 2 * H - 2 + (1 + H + b * (2 * H)) = _; omega)
  have hstep2_mod : (lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H))).1 % (4 * H) =
      (3 * H - 1 + b * (2 * H)) % (4 * H) ∧
      (lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H))).2 % (4 * H) = 2 * H - 2 := by
    simp only [lynessStep, feistelStep]
    refine ⟨trivial, ?_⟩
    have hsum : 3 * H - 1 + b * (2 * H) + c' = (1 + b) * (4 * H) := by
      change 3 * H - 1 + b * (2 * H) + (1 + H + b * (2 * H)) = (1 + b) * (4 * H)
      rcases hb2 with hb0 | hb1
      · rw [hb0]; omega
      · rw [hb1]; omega
    rw [← h4H, xor_mod_two_pow, h4H, hsum, Nat.mul_mod_left, Nat.xor_zero, Nat.mod_eq_of_lt (by omega)]
  have h6_eq : (iter (lynessStep c') 6 (0, 2 * H - 2)).1 % 2 ^ (t + 3) = 2 * H := by
    rw [show (6 : Nat) = 2 + 4 from rfl, iter_add]
    have h2_val : iter (lynessStep c') 2 (0, 2 * H - 2) =
        lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H)) := by
      simp only [iter, hstep1]
    rw [h2_val]
    have hcm4 := lynessStep_iter_mod c' (t + 3) 4
      (lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H))).1
      (lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H))).2
    have hfst4 := congrArg Prod.fst hcm4
    dsimp only at hfst4
    have hpair_eta : lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H)) =
        ((lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H))).1,
         (lynessStep c' (2 * H - 2, 3 * H - 1 + b * (2 * H))).2) := rfl
    rw [hpair_eta, hfst4]
    have hc'_lt : c' < 2 ^ (t + 3) := by
      rw [h4H]; change 1 + H + b * (2 * H) < 4 * H
      rcases hb2 with hb0 | hb1
      · rw [hb0]; omega
      · rw [hb1]; omega
    rw [Nat.mod_eq_of_lt hc'_lt, h4H, hstep2_mod.1, hstep2_mod.2]
    let x2m := (3 * H - 1 + b * (2 * H)) % (4 * H)
    have hx4_mod : (x2m ^^^ (2 * H - 2 + c')) % (4 * H) = 0 := by
      have harg : (2 * H - 2 + c') % (4 * H) = x2m := by
        change (2 * H - 2 + (1 + H + b * (2 * H))) % (4 * H) = (3 * H - 1 + b * (2 * H)) % (4 * H)
        congr 1; omega
      rw [← h4H, xor_mod_two_pow, h4H, Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega)), harg, Nat.xor_self]
    rw [show (4 : Nat) = 1 + 3 from rfl, iter_add]
    have hstep3 : iter (lynessStep c') 1 (x2m, 2 * H - 2) = (2 * H - 2, x2m ^^^ (2 * H - 2 + c')) := rfl
    rw [hstep3]
    have hcm3 := lynessStep_iter_mod c' (t + 3) 3 (2 * H - 2) (x2m ^^^ (2 * H - 2 + c'))
    have hfst3 := congrArg Prod.fst hcm3
    dsimp only at hfst3
    have hy2m : (2 * H - 2) % (4 * H) = 2 * H - 2 := Nat.mod_eq_of_lt (by omega)
    rw [← h4H, hfst3, Nat.mod_eq_of_lt hc'_lt, h4H, hy2m, hx4_mod]
    simp only [iter, lynessStep, feistelStep, Nat.zero_add, Nat.zero_xor]
    have hxor_key' : 2 * H - 2 ^^^ c' = H - 1 + b * (2 * H) := hxor_key
    rw [hxor_key']
    have hfinal : (H - 1) + b * (2 * H) + c' = 2 * H + b * (4 * H) := by
      change (H - 1) + b * (2 * H) + (1 + H + b * (2 * H)) = 2 * H + b * (4 * H)
      rcases hb2 with hb0 | hb1
      · rw [hb0]; omega
      · rw [hb1]; omega
    rw [hfinal, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h6_eq] at hmod
  omega

/-- Theorem 4 (Exact power-of-two period-6 dichotomy over unbounded `Nat × Nat`):
`F_c(x, y) = (y, x ^^^ (y + c))` satisfies `F_c^6 = id` on all of `Nat × Nat` if and only if
`c = 0` or `c = 2^r` for some `r : Nat`. -/
theorem lynessStep_period_six_iff (c : Nat) :
    (∀ x y : Nat, iter (lynessStep c) 6 (x, y) = (x, y)) ↔
    (c = 0 ∨ ∃ r : Nat, c = 2 ^ r) := by
  constructor
  · intro hper
    suffices h : ∀ n : Nat, (∀ x y : Nat, iter (lynessStep n) 6 (x, y) = (x, y)) →
        n = 0 ∨ ∃ r : Nat, n = 2 ^ r from h c hper
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h0 : n = 0
      · exact Or.inl h0
      · by_cases hodd : n % 2 = 1
        · by_cases h1 : n = 1
          · exact Or.inr ⟨0, h1⟩
          · exfalso
            rcases lynessStep_odd_ge_three_not_period_six n hodd (by omega) with ⟨x, y, hne⟩
            exact hne (hn x y)
        · have hn_eq : n = 2 * (n / 2) := by omega
          have hhalf : ∀ x y : Nat, iter (lynessStep (n / 2)) 6 (x, y) = (x, y) := by
            intro x y
            have h2 := hn (2 * x) (2 * y)
            rw [hn_eq, lynessStep_two_mul_split] at h2
            have hx0 : (2 * x) % 2 = 0 := by omega
            have hy0 : (2 * y) % 2 = 0 := by omega
            have hxd : (2 * x) / 2 = x := by omega
            have hyd : (2 * y) / 2 = y := by omega
            have h06 : iter (lynessStep 0) 6 (0, 0) = (0, 0) := rfl
            rw [hx0, hy0, hxd, hyd, h06] at h2
            exact Prod.ext (by have := congrArg Prod.fst h2; omega)
              (by have := congrArg Prod.snd h2; omega)
          rcases ih (n / 2) (by omega) hhalf with hz | ⟨r, hr⟩
          · omega
          · refine Or.inr ⟨r + 1, ?_⟩
            rw [Nat.pow_succ, Nat.mul_comm, ← hr]; omega
  · rintro (rfl | ⟨r, rfl⟩)
    · intro x y
      rw [show (6 : Nat) = 3 + 3 from rfl, iter_add, lynessStep_zero_period_three,
          lynessStep_zero_period_three]
    · intro x y
      exact lynessStep_pow_two_period_six r x y

/-! ## Section 4: Universal Period 12 for Bitwise-OR Binary Lyness `H_{2^r}` -/

/-- Exact period 12 at `c = 1` for `orLynessStep`: immediate corollary of Theorem 2! -/
theorem orLynessStep_one_period_twelve (x y : Nat) :
    iter (orLynessStep 1) 12 (x, y) = (x, y) := by
  refine feistelStep_iter_twelve_of_odd_parity (fun k => k ||| (k + 1)) (fun k => k ||| (k + 1))
    ?_ ?_ x y
  · intro k
    have h := or_two_mul_add k 0 k 1 (by omega) (by omega)
    simpa [Nat.or_self] using h
  · intro k
    have h := or_two_mul_add k 1 (k + 1) 0 (by omega) (by omega)
    simpa [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] using h

/-- Bit-0 product splitting for `orLynessStep (2 * c)`. -/
theorem orLynessStep_two_mul_split (c n x y : Nat) :
    iter (orLynessStep (2 * c)) n (x, y) =
      (2 * (iter (orLynessStep c) n (x / 2, y / 2)).1 + (iter (lynessStep 0) n (x % 2, y % 2)).1,
       2 * (iter (orLynessStep c) n (x / 2, y / 2)).2 + (iter (lynessStep 0) n (x % 2, y % 2)).2) := by
  induction n generalizing x y with
  | zero =>
    simp only [iter]
    exact Prod.ext (by omega) (by omega)
  | succ n ih =>
    simp only [iter, orLynessStep, lynessStep, feistelStep, Nat.add_zero]
    have hor : y ||| (y + 2 * c) = 2 * (y / 2 ||| (y / 2 + c)) + y % 2 := by
      have hy1 : y = 2 * (y / 2) + y % 2 := by omega
      have hy2 : y + 2 * c = 2 * (y / 2 + c) + y % 2 := by omega
      calc y ||| (y + 2 * c)
          = (2 * (y / 2) + y % 2) ||| (2 * (y / 2 + c) + y % 2) := by rw [← hy1, ← hy2]
        _ = 2 * (y / 2 ||| (y / 2 + c)) + (y % 2 ||| y % 2) :=
            or_two_mul_add _ _ _ _ (by omega) (by omega)
        _ = 2 * (y / 2 ||| (y / 2 + c)) + y % 2 := by rw [Nat.or_self]
    have hstep : x ^^^ (y ||| (y + 2 * c)) =
        2 * (x / 2 ^^^ (y / 2 ||| (y / 2 + c))) + (x % 2 ^^^ y % 2) := by
      have hx : x = 2 * (x / 2) + x % 2 := by omega
      calc x ^^^ (y ||| (y + 2 * c))
          = (2 * (x / 2) + x % 2) ^^^ (2 * (y / 2 ||| (y / 2 + c)) + y % 2) := by rw [← hx, hor]
        _ = 2 * (x / 2 ^^^ (y / 2 ||| (y / 2 + c))) + (x % 2 ^^^ y % 2) :=
            xor_two_mul_add _ _ _ _ (by omega) (by omega)
    have hlt2 : x % 2 ^^^ y % 2 < 2 := by
      have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hx2 with h1 | h1 <;> rcases hy2 with h2 | h2 <;> rw [h1, h2] <;> decide
    have hdiv : (x ^^^ (y ||| (y + 2 * c))) / 2 = x / 2 ^^^ (y / 2 ||| (y / 2 + c)) := by
      rw [hstep]; omega
    have hmod : (x ^^^ (y ||| (y + 2 * c))) % 2 = x % 2 ^^^ y % 2 := by
      rw [hstep]; omega
    have hnext := ih y (x ^^^ (y ||| (y + 2 * c)))
    rw [hdiv, hmod] at hnext
    exact hnext

/-- Theorem 5 (Universal period 12 for the Bitwise-OR Binary Lyness twin at every power of 2):
for every `r : Nat` and all `x y : Nat`, `H_{2^r}^{12}(x, y) = (x, y)`. -/
theorem orLynessStep_pow_two_period_twelve (r x y : Nat) :
    iter (orLynessStep (2 ^ r)) 12 (x, y) = (x, y) := by
  induction r generalizing x y with
  | zero => exact orLynessStep_one_period_twelve x y
  | succ r ih =>
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, orLynessStep_two_mul_split, ih]
    have h012 : iter (lynessStep 0) 12 (x % 2, y % 2) = (x % 2, y % 2) := by
      rw [show (12 : Nat) = 3 + (3 + (3 + 3)) from rfl,
          iter_add, lynessStep_zero_period_three,
          iter_add, lynessStep_zero_period_three,
          iter_add, lynessStep_zero_period_three,
          lynessStep_zero_period_three]
    rw [h012]
    exact Prod.ext (by omega) (by omega)

end BinaryLynessPeriods
