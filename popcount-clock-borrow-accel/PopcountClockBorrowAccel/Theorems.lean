/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PopcountClockBorrowAccel.Defs

/-!
# Quadratic Bit-Moment Clocks & Hardware Borrow-Acceleration for Popcount-Driven Bitwise Flows

Standalone Lean 4.34.1 formalization (zero Mathlib, zero external dependencies).
Worker: `dynsil-11` (Thread 2: Bitwise Dynamics, T-Functions & Reversible Silicon Orbit Mechanisms).

## Architecture
1. **Bitwise Primitives & Stability Engine:** structurally recursive width-independent `popcount`,
   arbitrary-weight `weightSum μ`, `indexSum`, binary inversion energy `phi`, and exact
   single-bit-flip laws.
2. **Mechanism I (`ClockCert` — Linear-Quadratic Silicon Clock Compiler):**
   A reusable finite-to-infinite proof engine lifting two local finite-difference equations
   for an arbitrary addressing schedule `h : Nat → Nat` and weight/potential pair `(μ, g)`
   to global infinite-width exact unit-clock (`V(T^t x) = V(x) - t`) and inversion-clock
   (`Φ(T x) = Φ(x) - bit_{h(p)}(x)`) theorems, acyclicity, and exact synchronization laws.
3. **Mechanism II (`BorrowAcceleration` — Carry-Free ↔ Hardware-Borrow Equivalence):**
   Proves that hardware subtraction `x - 2^(p + c)` is bit-for-bit identical to iterating
   carry-free XOR `x ^^^ 2^(p + c)` across the trailing-zero gap `1 + ctz(x >>> (p + c))`,
   automatically compiling the XOR inversion clock into an exact unit-step borrow clock
   independent of borrow-chain length.
4. **Infinite Theorems:**
   - **Theorem 1:** Infinite-width universal Mersenne coalescence & exact synchronous collision
     law `(∃ t, T_xor^[t] x = T_xor^[t] y) ↔ V(x) = V(y)` for `T_xor x = x ^^^ 2^(s_2 x)`.
   - **Theorem 2:** Sharp phase transition at `c = -1`: global termination to `0` on `Nat` with
     exact stopping time `2 * indexSum x - (s_2 x - 1)^2 + 1` for every `x ≥ 1`.
   - **Theorem 3:** Exact borrow-acceleration equivalence and exact Mersenne/zero hitting times
     `phi x` (for `c = 0`) and `phi x + s_2 x` (for `c = -1`).
   - **Theorem 4:** Finite-width modular global attractors for arbitrary width `w ≥ 1`:
     * General permuted carry-free wrap-around flow `F_wrap w π k` → unique global attractor
       cycle of exact length `2 * (w - k)` (hence `2 * w` for `x ^^^ 2^(s_2 x % w)`).
     * Borrow-coupled modular flow `F_sub_wrap w` → unique global attractor cycle of exact
       length `w + 1`.
     * Exact bitwise-complement conjugacy transporting the `(w + 1)`-cycle to the
       carry-synchronized dual `F_add_dual_wrap w x = (x + 2^((w - s_2 x) % w)) % 2^w`.
   - **Theorem 5:** Machine-checked sharpness counterexamples (carry-vs-borrow desynchronization
     at `w = 3`, non-injective `h(p) = p / 2` breaking any unit clock, non-coprime stride
     `a = 2, w = 4` shattering the unique cycle) and non-vacuity witnesses (including the
     non-monotone involution `h(p) = p ^^^ 1`).
-/


-- ============================================================================
-- Section 1: Bitwise Primitives, Stability, and Single-Bit-Flip Laws
-- ============================================================================

namespace Dynsil11

theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

theorem iter_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = iter f n (f x) := rfl

theorem iter_succ_right {α : Type} (f : α → α) :
    ∀ n x, iter f (n + 1) x = f (iter f n x)
  | 0, _ => rfl
  | n + 1, x => iter_succ_right f n (f x)

theorem iter_add {α : Type} (f : α → α) :
    ∀ a b x, iter f (a + b) x = iter f b (iter f a x)
  | 0, b, x => by simp [iter]
  | a + 1, b, x => by
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h, iter_succ, iter_succ, iter_add f a b (f x)]

theorem lt_two_pow_bitLenAux : ∀ fuel n : Nat, n ≤ fuel → n < 2 ^ bitLenAux fuel n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this; decide
  | succ fuel ih =>
    intro n hn
    unfold bitLenAux
    by_cases h0 : n = 0
    · subst h0; simp only [↓reduceIte]; decide
    · simp only [h0, ↓reduceIte]
      have hdiv : n / 2 ≤ fuel := by omega
      have hrec := ih (n / 2) hdiv
      rw [Nat.pow_succ]
      omega

theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n :=
  lt_two_pow_bitLenAux n n (Nat.le_refl n)

theorem testBit_eq_false_of_lt_two_pow {x k B : Nat} (hx : x < 2 ^ B) (hBk : B ≤ k) :
    x.testBit k = false := by
  have hlt : x < 2 ^ k := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hBk)
  exact Nat.testBit_lt_two_pow hlt

theorem popcountBelow_le (x : Nat) : ∀ B, popcountBelow x B ≤ B
  | 0 => Nat.le_refl 0
  | B + 1 => by
    unfold popcountBelow
    have ih := popcountBelow_le x B
    cases x.testBit B <;> simp <;> omega

theorem popcountBelow_stable {x B : Nat} (hx : x < 2 ^ B) :
    ∀ B', B ≤ B' → popcountBelow x B' = popcountBelow x B := by
  intro B' hle
  induction B' with
  | zero =>
    have hB : B = 0 := by omega
    subst hB; rfl
  | succ k ih =>
    by_cases hEq : B = k + 1
    · subst hEq; rfl
    · have hBk : B ≤ k := by omega
      have hbit : x.testBit k = false := testBit_eq_false_of_lt_two_pow hx hBk
      simp [popcountBelow, hbit, ih hBk]

theorem weightSumBelow_stable (μ : Nat → Int) {x B : Nat} (hx : x < 2 ^ B) :
    ∀ B', B ≤ B' → weightSumBelow μ x B' = weightSumBelow μ x B := by
  intro B' hle
  induction B' with
  | zero =>
    have hB : B = 0 := by omega
    subst hB; rfl
  | succ k ih =>
    by_cases hEq : B = k + 1
    · subst hEq; rfl
    · have hBk : B ≤ k := by omega
      have hbit : x.testBit k = false := testBit_eq_false_of_lt_two_pow hx hBk
      simp [weightSumBelow, hbit, ih hBk]

theorem popcount_eq_below {x B : Nat} (hx : x < 2 ^ B) :
    popcount x = popcountBelow x B := by
  unfold popcount
  let M := max (bitLen x) B
  have h1 := popcountBelow_stable (lt_two_pow_bitLen x) M (Nat.le_max_left _ _)
  have h2 := popcountBelow_stable hx M (Nat.le_max_right _ _)
  omega

theorem weightSum_eq_below (μ : Nat → Int) {x B : Nat} (hx : x < 2 ^ B) :
    weightSum μ x = weightSumBelow μ x B := by
  unfold weightSum
  let M := max (bitLen x) B
  have h1 := weightSumBelow_stable μ (lt_two_pow_bitLen x) M (Nat.le_max_left _ _)
  have h2 := weightSumBelow_stable μ hx M (Nat.le_max_right _ _)
  omega

theorem popcount_zero : popcount 0 = 0 := by
  rw [popcount_eq_below (B := 0) (by decide)]
  rfl

theorem weightSum_zero (μ : Nat → Int) : weightSum μ 0 = 0 := by
  rw [weightSum_eq_below μ (B := 0) (by decide)]
  rfl

theorem popcount_le_of_lt_two_pow {x B : Nat} (hx : x < 2 ^ B) : popcount x ≤ B := by
  rw [popcount_eq_below hx]
  exact popcountBelow_le x B

theorem xor_lt_two_pow {x y B : Nat} (hx : x < 2 ^ B) (hy : y < 2 ^ B) :
    x ^^^ y < 2 ^ B :=
  Nat.xor_lt_two_pow hx hy

theorem two_pow_lt_two_pow {k B : Nat} (hk : k < B) : 2 ^ k < 2 ^ B :=
  Nat.pow_lt_pow_right (by decide) hk

theorem testBit_xor_two_pow_self (x k : Nat) :
    (x ^^^ 2 ^ k).testBit k = !x.testBit k := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases x.testBit k <;> rfl

theorem testBit_xor_two_pow_ne (x k j : Nat) (hne : k ≠ j) :
    (x ^^^ 2 ^ k).testBit j = x.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  simp [hne]

/-- Single-bit-flip change of `popcountBelow`. -/
theorem popcountBelow_xor_two_pow_false {x k B : Nat} (hk : k < B) (hbit : x.testBit k = false) :
    popcountBelow (x ^^^ 2 ^ k) B = popcountBelow x B + 1 := by
  induction B with
  | zero => omega
  | succ b ih =>
    unfold popcountBelow
    by_cases hkb : k = b
    · subst hkb
      have hbelow : ∀ m ≤ k, popcountBelow (x ^^^ 2 ^ k) m = popcountBelow x m := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          simp [popcountBelow, ihm (by omega), testBit_xor_two_pow_ne x k m (by omega)]
      rw [hbelow k (Nat.le_refl k), testBit_xor_two_pow_self, hbit]
      simp
    · have hk' : k < b := by omega
      rw [ih hk', testBit_xor_two_pow_ne x k b hkb]
      cases x.testBit b <;> simp <;> omega

theorem popcountBelow_xor_two_pow_true {x k B : Nat} (hk : k < B) (hbit : x.testBit k = true) :
    popcountBelow (x ^^^ 2 ^ k) B + 1 = popcountBelow x B := by
  have h1 : (x ^^^ 2 ^ k).testBit k = false := by
    rw [testBit_xor_two_pow_self, hbit]; rfl
  have h2 := popcountBelow_xor_two_pow_false (x := x ^^^ 2 ^ k) hk h1
  have hcancel : (x ^^^ 2 ^ k) ^^^ 2 ^ k = x := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_xor]
  rw [hcancel] at h2
  exact h2.symm

/-- Single-bit-flip change of `weightSumBelow`. -/
theorem weightSumBelow_xor_two_pow_false (μ : Nat → Int) {x k B : Nat}
    (hk : k < B) (hbit : x.testBit k = false) :
    weightSumBelow μ (x ^^^ 2 ^ k) B = weightSumBelow μ x B + μ k := by
  induction B with
  | zero => omega
  | succ b ih =>
    unfold weightSumBelow
    by_cases hkb : k = b
    · subst hkb
      have hbelow : ∀ m ≤ k, weightSumBelow μ (x ^^^ 2 ^ k) m = weightSumBelow μ x m := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          simp [weightSumBelow, ihm (by omega), testBit_xor_two_pow_ne x k m (by omega)]
      rw [hbelow k (Nat.le_refl k), testBit_xor_two_pow_self, hbit]
      simp
    · have hk' : k < b := by omega
      rw [ih hk', testBit_xor_two_pow_ne x k b hkb]
      cases x.testBit b <;> simp <;> omega

theorem weightSumBelow_xor_two_pow_true (μ : Nat → Int) {x k B : Nat}
    (hk : k < B) (hbit : x.testBit k = true) :
    weightSumBelow μ (x ^^^ 2 ^ k) B = weightSumBelow μ x B - μ k := by
  have h1 : (x ^^^ 2 ^ k).testBit k = false := by
    rw [testBit_xor_two_pow_self, hbit]; rfl
  have h2 := weightSumBelow_xor_two_pow_false μ (x := x ^^^ 2 ^ k) hk h1
  have hcancel : (x ^^^ 2 ^ k) ^^^ 2 ^ k = x := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_xor]
  rw [hcancel] at h2
  omega

/-- Width-independent single-bit-flip laws for `popcount` and `weightSum`. -/
theorem popcount_xor_two_pow_false {x k : Nat} (hbit : x.testBit k = false) :
    popcount (x ^^^ 2 ^ k) = popcount x + 1 := by
  let B := max (bitLen x) (k + 1)
  have hx : x < 2 ^ B := Nat.lt_of_lt_of_le (lt_two_pow_bitLen x)
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hk : k < B := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)
  have hxk : x ^^^ 2 ^ k < 2 ^ B := xor_lt_two_pow hx (two_pow_lt_two_pow hk)
  rw [popcount_eq_below hxk, popcount_eq_below hx]
  exact popcountBelow_xor_two_pow_false hk hbit

theorem popcount_xor_two_pow_true {x k : Nat} (hbit : x.testBit k = true) :
    popcount (x ^^^ 2 ^ k) + 1 = popcount x := by
  let B := max (bitLen x) (k + 1)
  have hx : x < 2 ^ B := Nat.lt_of_lt_of_le (lt_two_pow_bitLen x)
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hk : k < B := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)
  have hxk : x ^^^ 2 ^ k < 2 ^ B := xor_lt_two_pow hx (two_pow_lt_two_pow hk)
  rw [popcount_eq_below hxk, popcount_eq_below hx]
  exact popcountBelow_xor_two_pow_true hk hbit

theorem weightSum_xor_two_pow_false (μ : Nat → Int) {x k : Nat} (hbit : x.testBit k = false) :
    weightSum μ (x ^^^ 2 ^ k) = weightSum μ x + μ k := by
  let B := max (bitLen x) (k + 1)
  have hx : x < 2 ^ B := Nat.lt_of_lt_of_le (lt_two_pow_bitLen x)
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hk : k < B := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)
  have hxk : x ^^^ 2 ^ k < 2 ^ B := xor_lt_two_pow hx (two_pow_lt_two_pow hk)
  rw [weightSum_eq_below μ hxk, weightSum_eq_below μ hx]
  exact weightSumBelow_xor_two_pow_false μ hk hbit

theorem weightSum_xor_two_pow_true (μ : Nat → Int) {x k : Nat} (hbit : x.testBit k = true) :
    weightSum μ (x ^^^ 2 ^ k) = weightSum μ x - μ k := by
  let B := max (bitLen x) (k + 1)
  have hx : x < 2 ^ B := Nat.lt_of_lt_of_le (lt_two_pow_bitLen x)
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hk : k < B := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)
  have hxk : x ^^^ 2 ^ k < 2 ^ B := xor_lt_two_pow hx (two_pow_lt_two_pow hk)
  rw [weightSum_eq_below μ hxk, weightSum_eq_below μ hx]
  exact weightSumBelow_xor_two_pow_true μ hk hbit

theorem popcount_eq_zero_iff (x : Nat) : popcount x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.zero_testBit]
    cases hbk : x.testBit k
    · rfl
    · have h1 := popcount_xor_two_pow_true hbk
      omega
  · intro h; subst h; exact popcount_zero

theorem popcount_pos_of_ne_zero {x : Nat} (hx : x ≠ 0) : 1 ≤ popcount x := by
  have : popcount x ≠ 0 := fun h => hx ((popcount_eq_zero_iff x).mp h)
  omega

/-- Self-contained helper: `(a ^^^ b) / 2 = (a / 2) ^^^ (b / 2)`. -/
theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]

/-- Self-contained helper: `a % 2 = b % 2` from `testBit 0`. -/
theorem mod_two_eq_of_testBit_zero {a b : Nat} (h : a.testBit 0 = b.testBit 0) :
    a % 2 = b % 2 := by
  rw [Nat.testBit_zero, Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb] at h ⊢

/-- Arithmetic-XOR single-bit lemma: `x.testBit k = false → x ^^^ 2^k = x + 2^k`. -/
theorem xor_two_pow_eq_add : ∀ {k x : Nat}, x.testBit k = false → x ^^^ 2 ^ k = x + 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro x hbit
    have hdiv : (x ^^^ 1) / 2 = (x + 1) / 2 := by
      rw [xor_div_two]
      have h1 : 1 / 2 = 0 := rfl
      rw [h1, Nat.xor_zero]
      rw [Nat.testBit_zero] at hbit
      have hmod : x % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one x with h | h
        · exact h
        · simp [h] at hbit
      omega
    have hmod : (x ^^^ 1) % 2 = (x + 1) % 2 := by
      apply mod_two_eq_of_testBit_zero
      rw [Nat.testBit_xor, hbit]
      rw [Nat.testBit_zero] at hbit ⊢
      have hm : x % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one x with h | h
        · exact h
        · simp [h] at hbit
      have h1 : (x + 1) % 2 = 1 := by omega
      simp [h1]
    have h20 : (2 : Nat) ^ 0 = 1 := rfl
    rw [h20]
    omega
  | succ k ih =>
    intro x hbit
    have hbit' : (x / 2).testBit k = false := by
      rwa [← Nat.testBit_succ]
    have hrec := ih hbit'
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hdiv : (x ^^^ 2 ^ (k + 1)) / 2 = (x + 2 ^ (k + 1)) / 2 := by
      rw [xor_div_two, hpow]
      have h1 : (2 * 2 ^ k) / 2 = 2 ^ k := by omega
      have h2 : (x + 2 * 2 ^ k) / 2 = x / 2 + 2 ^ k := by omega
      rw [h1, h2, hrec]
    have hmod : (x ^^^ 2 ^ (k + 1)) % 2 = (x + 2 ^ (k + 1)) % 2 := by
      apply mod_two_eq_of_testBit_zero
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      have hne : decide (k + 1 = 0) = false := by simp
      rw [hne, Bool.xor_false, Nat.testBit_zero, Nat.testBit_zero, hpow]
      have : (x + 2 * 2 ^ k) % 2 = x % 2 := by omega
      rw [this]
    omega

theorem xor_two_pow_add_eq {x k : Nat} (hbit : x.testBit k = true) :
    (x ^^^ 2 ^ k) + 2 ^ k = x := by
  have h0 : (x ^^^ 2 ^ k).testBit k = false := by
    rw [testBit_xor_two_pow_self, hbit]; rfl
  have h1 := xor_two_pow_eq_add h0
  have hcancel : (x ^^^ 2 ^ k) ^^^ 2 ^ k = x := by
    apply Nat.eq_of_testBit_eq
    intro i; simp [Nat.testBit_xor]
  rw [hcancel] at h1
  exact h1.symm

theorem two_pow_le_of_testBit_true {x k : Nat} (hbit : x.testBit k = true) :
    2 ^ k ≤ x := by
  have h := xor_two_pow_add_eq hbit
  omega

theorem xor_two_pow_eq_sub {x k : Nat} (hbit : x.testBit k = true) :
    x ^^^ 2 ^ k = x - 2 ^ k := by
  have h := xor_two_pow_add_eq hbit
  omega

-- ============================================================================
-- Section 2: Binary Inversion Energy `phi` and Mersenne Characterization
-- ============================================================================

theorem two_mul_choose_two (p : Nat) :
    2 * ((p * (p - 1)) / 2) = p * (p - 1) := by
  have heven : 2 ∣ p * (p - 1) := by
    cases p with
    | zero => exact ⟨0, rfl⟩
    | succ k =>
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · refine ⟨(k + 1) * (k / 2), ?_⟩
        have h1 : k = 2 * (k / 2) := by omega
        calc (k + 1) * k = (k + 1) * (2 * (k / 2)) := by rw [← h1]
          _ = 2 * ((k + 1) * (k / 2)) := by rw [Nat.mul_left_comm]
      · refine ⟨((k + 1) / 2) * k, ?_⟩
        have h1 : k + 1 = 2 * ((k + 1) / 2) := by omega
        calc (k + 1) * k = (2 * ((k + 1) / 2)) * k := by rw [← h1]
          _ = 2 * (((k + 1) / 2) * k) := by rw [Nat.mul_assoc]
  exact Nat.mul_div_cancel' heven

theorem two_mul_phi (x : Nat) :
    2 * phi x = 2 * indexSum x - ((popcount x : Int) * ((popcount x : Int) - 1)) := by
  unfold phi
  have h2 := two_mul_choose_two (popcount x)
  have hcast : ((popcount x * (popcount x - 1) : Nat) : Int) =
      (popcount x : Int) * ((popcount x : Int) - 1) := by
    cases popcount x with
    | zero => rfl
    | succ k =>
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub, Int.natCast_mul]
      have h1 : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
      rw [h1]
  have h2i : 2 * (((popcount x * (popcount x - 1)) / 2 : Nat) : Int) =
      ((popcount x * (popcount x - 1) : Nat) : Int) := by
    have := congrArg (fun n : Nat => (n : Int)) h2
    simpa [Int.natCast_mul] using this
  omega

/-- Auxiliary: `testBit` of `2^m - 1`. -/
theorem testBit_two_pow_sub_one (m i : Nat) :
    (2 ^ m - 1).testBit i = decide (i < m) :=
  Nat.testBit_two_pow_sub_one m i

theorem popcount_two_pow_sub_one (m : Nat) : popcount (2 ^ m - 1) = m := by
  have hlt : 2 ^ m - 1 < 2 ^ m := Nat.sub_lt (Nat.two_pow_pos m) (by decide)
  rw [popcount_eq_below hlt]
  suffices ∀ k ≤ m, popcountBelow (2 ^ m - 1) k = k from this m (Nat.le_refl m)
  intro k hk
  induction k with
  | zero => rfl
  | succ j ih =>
    unfold popcountBelow
    rw [ih (by omega), testBit_two_pow_sub_one]
    have hjm : j < m := by omega
    simp [hjm]

theorem indexSum_two_pow_sub_one (m : Nat) :
    2 * indexSum (2 ^ m - 1) = (m : Int) * ((m : Int) - 1) := by
  have hlt : 2 ^ m - 1 < 2 ^ m := Nat.sub_lt (Nat.two_pow_pos m) (by decide)
  unfold indexSum
  rw [weightSum_eq_below _ hlt]
  suffices ∀ k ≤ m, 2 * weightSumBelow (fun i => (i : Int)) (2 ^ m - 1) k =
      (k : Int) * ((k : Int) - 1) from this m (Nat.le_refl m)
  intro k hk
  induction k with
  | zero => rfl
  | succ j ih =>
    unfold weightSumBelow
    rw [testBit_two_pow_sub_one]
    have hjm : j < m := by omega
    simp only [hjm, decide_true, ↓reduceIte]
    have hij := ih (by omega)
    have hmul : 2 * (weightSumBelow (fun i => (i : Int)) (2 ^ m - 1) j + (j : Int)) =
        2 * weightSumBelow (fun i => (i : Int)) (2 ^ m - 1) j + 2 * (j : Int) := by omega
    rw [hmul, hij]
    have hstep : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    rw [hstep]
    have hsub : (j : Int) + 1 - 1 = (j : Int) := by omega
    rw [hsub]
    calc (j : Int) * ((j : Int) - 1) + 2 * (j : Int)
        = (j : Int) * (j : Int) - (j : Int) + 2 * (j : Int) := by rw [Int.mul_sub, Int.mul_one]
      _ = (j : Int) * (j : Int) + (j : Int) := by omega
      _ = ((j : Int) + 1) * (j : Int) := by rw [Int.add_mul, Int.one_mul]

theorem phi_two_pow_sub_one (m : Nat) : phi (2 ^ m - 1) = 0 := by
  have h1 := two_mul_phi (2 ^ m - 1)
  rw [popcount_two_pow_sub_one, indexSum_two_pow_sub_one] at h1
  omega

/-- Core inductive lemma: `2 * indexSumBelow x B ≥ p * (p - 1)`. -/
theorem indexSumBelow_ge_choose (x : Nat) : ∀ B,
    2 * weightSumBelow (fun i => (i : Int)) x B ≥
      (popcountBelow x B : Int) * ((popcountBelow x B : Int) - 1) := by
  intro B
  induction B with
  | zero => simp [weightSumBelow, popcountBelow]
  | succ b ih =>
    unfold weightSumBelow popcountBelow
    have hle : popcountBelow x b ≤ b := popcountBelow_le x b
    cases hbit : x.testBit b
    · simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero, Nat.add_zero]
      exact ih
    · simp only [↓reduceIte]
      have hstep : ((popcountBelow x b + 1 : Nat) : Int) = (popcountBelow x b : Int) + 1 := by omega
      have halg : ((popcountBelow x b + 1 : Nat) : Int) * (((popcountBelow x b + 1 : Nat) : Int) - 1) =
          (popcountBelow x b : Int) * ((popcountBelow x b : Int) - 1) + 2 * (popcountBelow x b : Int) := by
        rw [hstep]
        have hsub : (popcountBelow x b : Int) + 1 - 1 = (popcountBelow x b : Int) := by omega
        rw [hsub, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
        omega
      rw [halg]
      omega

theorem phi_nonneg (x : Nat) : 0 ≤ phi x := by
  have h1 := two_mul_phi x
  have h2 := indexSumBelow_ge_choose x (bitLen x)
  change 2 * indexSum x ≥ (popcount x : Int) * ((popcount x : Int) - 1) at h2
  omega

/-- Equality characterization on `B`: if `2 * indexSumBelow x B = p * (p - 1)`,
    then for every `i < B`, `x.testBit i = decide (i < p)`. -/
theorem testBit_eq_of_indexSumBelow_eq (x : Nat) : ∀ B,
    2 * weightSumBelow (fun i => (i : Int)) x B =
      (popcountBelow x B : Int) * ((popcountBelow x B : Int) - 1) →
    ∀ i < B, x.testBit i = decide (i < popcountBelow x B) := by
  intro B
  induction B with
  | zero => intro _ i hi; omega
  | succ b ih =>
    intro heq i hi
    unfold weightSumBelow popcountBelow at heq
    have hle : popcountBelow x b ≤ b := popcountBelow_le x b
    have hge := indexSumBelow_ge_choose x b
    cases hbit : x.testBit b
    · rw [hbit] at heq
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero, Nat.add_zero] at heq
      have hpop : popcountBelow x (b + 1) = popcountBelow x b := by
        simp [popcountBelow, hbit]
      rw [hpop]
      by_cases hib : i = b
      · subst hib
        rw [hbit]
        have hnotlt : ¬ (i < popcountBelow x i) := by omega
        simp [hnotlt]
      · exact ih heq i (by omega)
    · rw [hbit] at heq
      simp only [↓reduceIte] at heq
      have hstep : ((popcountBelow x b + 1 : Nat) : Int) = (popcountBelow x b : Int) + 1 := by omega
      have halg : ((popcountBelow x b + 1 : Nat) : Int) * (((popcountBelow x b + 1 : Nat) : Int) - 1) =
          (popcountBelow x b : Int) * ((popcountBelow x b : Int) - 1) + 2 * (popcountBelow x b : Int) := by
        rw [hstep]
        have hsub : (popcountBelow x b : Int) + 1 - 1 = (popcountBelow x b : Int) := by omega
        rw [hsub, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
        omega
      rw [halg] at heq
      have hp_eq_b : popcountBelow x b = b := by omega
      have heq_b : 2 * weightSumBelow (fun i => (i : Int)) x b =
          (popcountBelow x b : Int) * ((popcountBelow x b : Int) - 1) := by
        omega
      have hpop : popcountBelow x (b + 1) = b + 1 := by
        unfold popcountBelow; rw [hbit]; simp [hp_eq_b]
      rw [hpop]
      simp only [hi, decide_true]
      by_cases hib : i = b
      · subst hib; exact hbit
      · have hprev := ih heq_b i (by omega)
        rw [hp_eq_b] at hprev
        have hib' : i < b := by omega
        simpa [hib'] using hprev

/-- Exact Mersenne characterization: `phi x = 0 ↔ x = 2^(popcount x) - 1`. -/
theorem phi_eq_zero_iff (x : Nat) : phi x = 0 ↔ x = 2 ^ popcount x - 1 := by
  constructor
  · intro hphi
    have h1 := two_mul_phi x
    rw [hphi] at h1
    have heq : 2 * weightSumBelow (fun i => (i : Int)) x (bitLen x) =
        (popcountBelow x (bitLen x) : Int) * ((popcountBelow x (bitLen x) : Int) - 1) := by
      change 2 * indexSum x = (popcount x : Int) * ((popcount x : Int) - 1)
      omega
    have hbits := testBit_eq_of_indexSumBelow_eq x (bitLen x) heq
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_two_pow_sub_one]
    by_cases hi : i < bitLen x
    · exact hbits i hi
    · have hnotlt : ¬ (i < popcount x) := by
        have hle := popcountBelow_le x (bitLen x)
        change popcount x ≤ bitLen x at hle
        omega
      have hbf : x.testBit i = false :=
        testBit_eq_false_of_lt_two_pow (lt_two_pow_bitLen x) (by omega)
      simp [hbf, hnotlt]
  · intro hx
    calc phi x = phi (2 ^ popcount x - 1) := congrArg phi hx
      _ = 0 := phi_two_pow_sub_one (popcount x)

/-- If `x < 2^m`, then `x = 2^m - 1 ↔ popcount x = m`. -/
theorem eq_two_pow_sub_one_iff_popcount {x m : Nat} (hx : x < 2 ^ m) :
    x = 2 ^ m - 1 ↔ popcount x = m := by
  constructor
  · intro h; subst h; exact popcount_two_pow_sub_one m
  · intro hp
    have hall : ∀ B ≤ m, popcountBelow x B = B → ∀ i < B, x.testBit i = true := by
      intro B hBm hpb
      induction B with
      | zero => intro i hi; omega
      | succ b ih =>
        intro i hi
        unfold popcountBelow at hpb
        have hleb := popcountBelow_le x b
        cases hbb : x.testBit b
        · rw [hbb] at hpb; simp at hpb; omega
        · rw [hbb] at hpb; simp at hpb
          by_cases hib : i = b
          · subst hib; exact hbb
          · exact ih (by omega) (by omega) i (by omega)
    rw [popcount_eq_below hx] at hp
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_two_pow_sub_one]
    by_cases hi : i < m
    · simp [hi, hall m (Nat.le_refl m) hp i hi]
    · have hmi : m ≤ i := by omega
      simp [hi, testBit_eq_false_of_lt_two_pow hx hmi]

/-- Crucial non-underflow lemma: if `phi x > 0`, there is a set bit at index `≥ popcount x`. -/
theorem exists_set_bit_ge_popcount {x : Nat} (hphi : 0 < phi x) :
    ∃ q, popcount x ≤ q ∧ x.testBit q = true := by
  apply Classical.byContradiction
  intro hno
  have hlt : x < 2 ^ popcount x := by
    have hmask : x = x % 2 ^ popcount x := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases hi : i < popcount x
      · simp [hi]
      · have hbf : x.testBit i = false := by
          cases hbi : x.testBit i
          · rfl
          · exfalso; exact hno ⟨i, by omega, hbi⟩
        simp [hi, hbf]
    calc x = x % 2 ^ popcount x := hmask
      _ < 2 ^ popcount x := Nat.mod_lt x (Nat.two_pow_pos _)
  have hEq : x = 2 ^ popcount x - 1 := (eq_two_pow_sub_one_iff_popcount hlt).mpr rfl
  have h0 : phi x = 0 := (phi_eq_zero_iff x).mpr hEq
  omega

/-- Subcritical non-underflow lemma: if `x ≠ 0`, there is a set bit at index `≥ popcount x - 1`. -/
theorem exists_set_bit_ge_popcount_sub_one {x : Nat} (hx : x ≠ 0) :
    ∃ q, popcount x - 1 ≤ q ∧ x.testBit q = true := by
  have hp : 1 ≤ popcount x := popcount_pos_of_ne_zero hx
  apply Classical.byContradiction
  intro hno
  have hlt : x < 2 ^ (popcount x - 1) := by
    have hmask : x = x % 2 ^ (popcount x - 1) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases hi : i < popcount x - 1
      · simp [hi]
      · have hbf : x.testBit i = false := by
          cases hbi : x.testBit i
          · rfl
          · exfalso; exact hno ⟨i, by omega, hbi⟩
        simp [hi, hbf]
    calc x = x % 2 ^ (popcount x - 1) := hmask
      _ < 2 ^ (popcount x - 1) := Nat.mod_lt x (Nat.two_pow_pos _)
  have hle := popcount_le_of_lt_two_pow hlt
  omega

-- ============================================================================
-- Section 3: MECHANISM I — Reusable Linear-Quadratic Silicon Clock Compiler
-- ============================================================================

/-- **Mechanism I (`ClockCert`)**:
    A finite algebraic certificate `(h, μ, g, δ_up, δ_down)` on an arbitrary addressing
    schedule `h : Nat → Nat` and active domain predicate `Dom : Nat → Prop`. -/
structure ClockCert where
  h      : Nat → Nat
  μ      : Nat → Int
  g      : Nat → Int
  δ_up   : Int
  δ_down : Int
  Dom    : Nat → Prop
  diff_up   : ∀ p, Dom p → μ (h p) - (g (p + 1) - g p) = -δ_up
  diff_down : ∀ p, Dom p → 1 ≤ p → -μ (h p) - (g (p - 1) - g p) = -δ_down

/-- Self-addressing carry-free bit-flip operator induced by `C.h`. -/
def ClockCert.step (C : ClockCert) (x : Nat) : Nat :=
  x ^^^ 2 ^ C.h (popcount x)

/-- Quadratic-linear silicon bit-moment potential `V_C(x) = ∑ μ(i) x_i - g(s_2(x))`. -/
def ClockCert.pot (C : ClockCert) (x : Nat) : Int :=
  weightSum C.μ x - C.g (popcount x)

/-- **Master Lifting Theorem (Engine I):**
    Pointwise certificate equations lift automatically to arbitrary bit-width `x : Nat`. -/
theorem ClockCert.pot_step (C : ClockCert) {x : Nat} (hdom : C.Dom (popcount x)) :
    C.pot (C.step x) =
      C.pot x - if x.testBit (C.h (popcount x)) then C.δ_down else C.δ_up := by
  unfold ClockCert.pot ClockCert.step
  cases hbit : x.testBit (C.h (popcount x))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [weightSum_xor_two_pow_false C.μ hbit, popcount_xor_two_pow_false hbit]
    have hd := C.diff_up (popcount x) hdom
    omega
  · simp only [↓reduceIte]
    have hpop := popcount_xor_two_pow_true hbit
    have hp1 : 1 ≤ popcount x := by omega
    have hpop' : popcount (x ^^^ 2 ^ C.h (popcount x)) = popcount x - 1 := by omega
    rw [weightSum_xor_two_pow_true C.μ hbit, hpop']
    have hd := C.diff_down (popcount x) hdom hp1
    omega

/-- **Unit-Clock Compilation Theorem:**
    When `δ_up = δ_down = 1` and `Dom` holds globally, `C.pot` ticks down by exact unit steps. -/
theorem ClockCert.unit_clock_iter (C : ClockCert)
    (hup : C.δ_up = 1) (hdn : C.δ_down = 1)
    (hdom : ∀ y, C.Dom (popcount y)) :
    ∀ t x, C.pot (iter C.step t x) = C.pot x - (t : Int) := by
  intro t
  induction t with
  | zero => intro x; simp [iter]
  | succ t ih =>
    intro x
    rw [iter_succ, ih (C.step x), C.pot_step (hdom x), hup, hdn]
    cases x.testBit (C.h (popcount x)) <;> simp <;> omega

/-- **Universal Acyclicity & Phase-Separation Theorems (Engine I):** -/
theorem ClockCert.no_cycles (C : ClockCert)
    (hup : C.δ_up = 1) (hdn : C.δ_down = 1)
    (hdom : ∀ y, C.Dom (popcount y))
    {t : Nat} (ht : 0 < t) (x : Nat) :
    iter C.step t x ≠ x := by
  intro hEq
  have hpot := C.unit_clock_iter hup hdn hdom t x
  rw [hEq] at hpot
  omega

theorem ClockCert.no_sync_collision_of_pot_ne (C : ClockCert)
    (hup : C.δ_up = 1) (hdn : C.δ_down = 1)
    (hdom : ∀ y, C.Dom (popcount y))
    {x y : Nat} (hne : C.pot x ≠ C.pot y) (t : Nat) :
    iter C.step t x ≠ iter C.step t y := by
  intro hEq
  have hx := C.unit_clock_iter hup hdn hdom t x
  have hy := C.unit_clock_iter hup hdn hdom t y
  rw [hEq] at hx
  omega

/-- **Automatic Bijective-Address Certificate Compiler:**
    ANY bijection `(h, hInv)` on `Nat` compiles into a global unit-clock certificate! -/
def bijectiveUnitClockCert (h hInv : Nat → Nat) (hleft : ∀ p, hInv (h p) = p) : ClockCert where
  h := h
  μ := fun i => 2 * (hInv i : Int)
  g := fun p => (p : Int) * (p : Int)
  δ_up := 1
  δ_down := 1
  Dom := fun _ => True
  diff_up := fun p _ => by
    rw [hleft p]
    have h1 : ((p + 1 : Nat) : Int) = (p : Int) + 1 := by omega
    rw [h1, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
    omega
  diff_down := fun p _ hp1 => by
    rw [hleft p]
    have h1 : ((p - 1 : Nat) : Int) = (p : Int) - 1 := by omega
    rw [h1, Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one]
    omega

/-- **Automatic Inversion-Clock Certificate (`δ_up = 0, δ_down = 1`) for `h = id`:** -/
def inversionClockCert0 : ClockCert where
  h := id
  μ := fun i => (i : Int)
  g := fun p => ((p * (p - 1)) / 2 : Nat)
  δ_up := 0
  δ_down := 1
  Dom := fun _ => True
  diff_up := fun p _ => by
    simp only [id]
    have h1 := two_mul_choose_two (p + 1)
    have h2 := two_mul_choose_two p
    have hsub : p + 1 - 1 = p := by omega
    rw [hsub] at h1
    have hmul : (p + 1) * p = p * (p - 1) + 2 * p := by
      cases p with
      | zero => rfl
      | succ k =>
        have hk : k + 1 - 1 = k := by omega
        rw [hk]
        calc (k + 1 + 1) * (k + 1)
            = (k + 1) * (k + 1) + (k + 1) := by rw [Nat.add_mul, Nat.one_mul]
          _ = (k + 1) * k + (k + 1) + (k + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = (k + 1) * k + 2 * (k + 1) := by omega
    have hdiv : ((p + 1) * p) / 2 = (p * (p - 1)) / 2 + p := by omega
    rw [hsub, hdiv]
    omega
  diff_down := fun p _ hp1 => by
    simp only [id]
    have h1 := two_mul_choose_two p
    have h2 := two_mul_choose_two (p - 1)
    have hmul : p * (p - 1) = (p - 1) * (p - 1 - 1) + 2 * (p - 1) := by
      cases p with
      | zero => omega
      | succ k =>
        cases k with
        | zero => rfl
        | succ m =>
          have h1' : m + 1 + 1 - 1 = m + 1 := by omega
          have h2' : m + 1 - 1 = m := by omega
          rw [h1', h2']
          calc (m + 1 + 1) * (m + 1)
              = (m + 1) * (m + 1) + (m + 1) := by rw [Nat.add_mul, Nat.one_mul]
            _ = (m + 1) * m + (m + 1) + (m + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ = (m + 1) * m + 2 * (m + 1) := by omega
    have hdiv : (p * (p - 1)) / 2 = ((p - 1) * (p - 1 - 1)) / 2 + (p - 1) := by omega
    rw [hdiv]
    omega

-- ============================================================================
-- Section 4: Theorem 1 — Infinite-Width Coalescence & Exact Collision Criterion
-- ============================================================================

def unitClockCert0 : ClockCert := bijectiveUnitClockCert id id (fun _ => rfl)

theorem weightSumBelow_two_mul (x : Nat) : ∀ B,
    weightSumBelow (fun i => 2 * (i : Int)) x B =
    2 * weightSumBelow (fun i => (i : Int)) x B
  | 0 => rfl
  | b + 1 => by
    unfold weightSumBelow
    rw [weightSumBelow_two_mul x b]
    cases x.testBit b <;> simp <;> omega

theorem V_unit_eq_cert_pot (x : Nat) : V_unit x = unitClockCert0.pot x := by
  change 2 * weightSumBelow (fun i => (i : Int)) x (bitLen x) - (popcount x : Int) * (popcount x : Int) =
         weightSumBelow (fun i => 2 * (i : Int)) x (bitLen x) - (popcount x : Int) * (popcount x : Int)
  rw [weightSumBelow_two_mul]

theorem V_unit_eq_two_phi_sub_pop (x : Nat) :
    V_unit x = 2 * phi x - (popcount x : Int) := by
  unfold V_unit
  have h := two_mul_phi x
  have halg : (popcount x : Int) * ((popcount x : Int) - 1) =
      (popcount x : Int) * (popcount x : Int) - (popcount x : Int) := by
    rw [Int.mul_sub, Int.mul_one]
  omega

/-- **Theorem 1A (Exact Unit-Clock Law on `Nat`):** -/
theorem T_xor_unit_clock (t x : Nat) : V_unit (iter T_xor t x) = V_unit x - (t : Int) := by
  have hstep : T_xor = unitClockCert0.step := rfl
  rw [hstep, V_unit_eq_cert_pot, V_unit_eq_cert_pot]
  exact unitClockCert0.unit_clock_iter rfl rfl (fun _ => trivial) t x

/-- **Theorem 1B (Exact Inversion-Clock Law for `T_xor`):** -/
theorem T_xor_phi_step (x : Nat) :
    phi (T_xor x) = phi x - if x.testBit (popcount x) then 1 else 0 := by
  have h1 : phi x = inversionClockCert0.pot x := rfl
  have h2 : phi (T_xor x) = inversionClockCert0.pot (inversionClockCert0.step x) := rfl
  rw [h2, inversionClockCert0.pot_step trivial, ← h1]
  rfl

/-- Stepping along the Mersenne spine: `T_xor (2^m - 1) = 2^(m+1) - 1`. -/
theorem T_xor_mersenne (m : Nat) : T_xor (2 ^ m - 1) = 2 ^ (m + 1) - 1 := by
  unfold T_xor
  rw [popcount_two_pow_sub_one]
  have hbit : (2 ^ m - 1).testBit m = false := by
    rw [testBit_two_pow_sub_one]; simp
  rw [xor_two_pow_eq_add hbit, Nat.pow_succ]
  have hpos : 1 ≤ 2 ^ m := Nat.two_pow_pos m
  omega

theorem T_xor_iter_mersenne (t m : Nat) :
    iter T_xor t (2 ^ m - 1) = 2 ^ (m + t) - 1 := by
  induction t generalizing m with
  | zero => simp [iter]
  | succ t ih =>
    rw [iter_succ, T_xor_mersenne, ih (m + 1)]
    have : m + 1 + t = m + (t + 1) := by omega
    rw [this]

/-- Key closure lemma: if `x < 2^m` and `x ≠ 2^m - 1`, then `T_xor x < 2^m`. -/
theorem T_xor_lt_two_pow {x m : Nat} (hx : x < 2 ^ m) (hne : x ≠ 2 ^ m - 1) :
    T_xor x < 2 ^ m := by
  have hple : popcount x ≤ m := popcount_le_of_lt_two_pow hx
  have hpne : popcount x ≠ m := fun h => hne ((eq_two_pow_sub_one_iff_popcount hx).mpr h)
  have hplt : popcount x < m := by omega
  exact xor_lt_two_pow hx (two_pow_lt_two_pow hplt)

/-- Exact non-negativity and zero locus of `V_unit x + m` on `x < 2^m`. -/
theorem V_unit_add_width_nonneg {x m : Nat} (hx : x < 2 ^ m) :
    0 ≤ V_unit x + (m : Int) := by
  rw [V_unit_eq_two_phi_sub_pop]
  have h1 := phi_nonneg x
  have h2 := popcount_le_of_lt_two_pow hx
  omega

theorem V_unit_add_width_eq_zero_iff {x m : Nat} (hx : x < 2 ^ m) :
    V_unit x + (m : Int) = 0 ↔ x = 2 ^ m - 1 := by
  constructor
  · intro h
    rw [V_unit_eq_two_phi_sub_pop] at h
    have h1 := phi_nonneg x
    have h2 := popcount_le_of_lt_two_pow hx
    have hpm : popcount x = m := by omega
    exact (eq_two_pow_sub_one_iff_popcount hx).mpr hpm
  · intro h
    subst h
    rw [V_unit_eq_two_phi_sub_pop, phi_two_pow_sub_one, popcount_two_pow_sub_one]
    omega

/-- **Theorem 1C (Exact Universal Mersenne Coalescence on `Nat`):**
    For EVERY `x < 2^m`, `T_xor` hits `2^m - 1` in **EXACTLY `V_unit x + m`** steps. -/
theorem T_xor_hits_mersenne_exact : ∀ (N m x : Nat),
    x < 2 ^ m → V_unit x + (m : Int) = (N : Int) →
    iter T_xor N x = 2 ^ m - 1 := by
  intro N
  induction N with
  | zero =>
    intro m x hx hV
    rw [iter_zero]
    exact (V_unit_add_width_eq_zero_iff hx).mp hV
  | succ N ih =>
    intro m x hx hV
    have hne : x ≠ 2 ^ m - 1 := by
      intro heq
      have := (V_unit_add_width_eq_zero_iff hx).mpr heq
      omega
    have hx' : T_xor x < 2 ^ m := T_xor_lt_two_pow hx hne
    have hV' : V_unit (T_xor x) + (m : Int) = (N : Int) := by
      have htick := T_xor_unit_clock 1 x
      simp [iter] at htick
      omega
    rw [iter_succ]
    exact ih m (T_xor x) hx' hV'

/-- **Theorem 1D (Asymptotic Mersenne Ray Formula):**
    For ALL `x < 2^m` and ALL `t ≥ (V_unit x + m).toNat`,
    `iter T_xor t x = 2 ^ (t - V_unit x) - 1`. -/
theorem T_xor_mersenne_ray {x m t : Nat} (hx : x < 2 ^ m)
    (ht : V_unit x + (m : Int) ≤ (t : Int)) :
    iter T_xor t x = 2 ^ ((t : Int) - V_unit x).toNat - 1 := by
  have hnn := V_unit_add_width_nonneg hx
  let N := (V_unit x + (m : Int)).toNat
  have hN : (N : Int) = V_unit x + (m : Int) := Int.toNat_of_nonneg hnn
  have hNt : N ≤ t := by omega
  have hsplit : t = N + (t - N) := by omega
  have h1 : iter T_xor t x = iter T_xor (N + (t - N)) x := congrArg (fun k => iter T_xor k x) hsplit
  rw [h1, iter_add, T_xor_hits_mersenne_exact N m x hx hN.symm, T_xor_iter_mersenne]
  have hexp : m + (t - N) = ((t : Int) - V_unit x).toNat := by omega
  rw [hexp]

/-- **Theorem 1E (Exact Synchronous Collision Equivalence on `Nat`):**
    Two arbitrary natural numbers `x, y : Nat` synchronously collide under `T_xor`
    **if and only if** they have the exact same quadratic bit-moment potential `V_unit`. -/
theorem T_xor_sync_collision_iff (x y : Nat) :
    (∃ t : Nat, iter T_xor t x = iter T_xor t y) ↔ V_unit x = V_unit y := by
  constructor
  · rintro ⟨t, heq⟩
    have hx := T_xor_unit_clock t x
    have hy := T_xor_unit_clock t y
    rw [heq] at hx
    omega
  · intro hV
    let m := max (bitLen x) (bitLen y)
    have hx : x < 2 ^ m := Nat.lt_of_lt_of_le (lt_two_pow_bitLen x)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
    have hy : y < 2 ^ m := Nat.lt_of_lt_of_le (lt_two_pow_bitLen y)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
    have hnn := V_unit_add_width_nonneg hx
    refine ⟨(V_unit x + (m : Int)).toNat, ?_⟩
    have hN : ((V_unit x + (m : Int)).toNat : Int) = V_unit x + (m : Int) := Int.toNat_of_nonneg hnn
    rw [T_xor_hits_mersenne_exact _ m x hx hN.symm,
        T_xor_hits_mersenne_exact _ m y hy (by omega)]

-- ============================================================================
-- Section 5: Theorem 2 — Sharp Phase Transition at c = -1 (Global Termination)
-- ============================================================================

/-- Subcritical (`c = -1`) carry-free popcount-pointer flow on `Nat`. -/
def T_xor_m1 (x : Nat) : Nat :=
  if x = 0 then 0 else x ^^^ 2 ^ (popcount x - 1)

/-- Subcritical unit-clock potential `V_{-1}(x) = 2 * indexSum x - (s_2(x) - 1)^2`. -/
def V_sub1 (x : Nat) : Int :=
  2 * indexSum x - ((popcount x : Int) - 1) * ((popcount x : Int) - 1)

/-- Certificate instance for `c = -1` on domain `p ≥ 1`. -/
def subcriticalClockCert : ClockCert where
  h := fun p => p - 1
  μ := fun i => 2 * (i : Int)
  g := fun p => ((p : Int) - 1) * ((p : Int) - 1)
  δ_up := 1
  δ_down := 1
  Dom := fun p => 1 ≤ p
  diff_up := fun p hp => by
    have h1 : ((p - 1 : Nat) : Int) = (p : Int) - 1 := by omega
    have h2 : ((p + 1 : Nat) : Int) = (p : Int) + 1 := by omega
    rw [h1, h2]
    have hsub : (p : Int) + 1 - 1 = (p : Int) := by omega
    rw [hsub]
    have halg : ((p : Int) - 1) * ((p : Int) - 1) =
        (p : Int) * (p : Int) - 2 * (p : Int) + 1 := by
      rw [Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one]
      omega
    rw [halg]
    omega
  diff_down := fun p hp _ => by
    have h1 : ((p - 1 : Nat) : Int) = (p : Int) - 1 := by omega
    rw [h1]
    have halg1 : ((p : Int) - 1 - 1) * ((p : Int) - 1 - 1) =
        ((p : Int) - 1) * ((p : Int) - 1) - 2 * ((p : Int) - 1) + 1 := by
      rw [Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one]
      omega
    rw [halg1]
    omega

theorem V_sub1_eq_cert_pot (x : Nat) : V_sub1 x = subcriticalClockCert.pot x := by
  change 2 * weightSumBelow (fun i => (i : Int)) x (bitLen x) -
           ((popcount x : Int) - 1) * ((popcount x : Int) - 1) =
         weightSumBelow (fun i => 2 * (i : Int)) x (bitLen x) -
           ((popcount x : Int) - 1) * ((popcount x : Int) - 1)
  rw [weightSumBelow_two_mul]

theorem V_sub1_eq_two_phi_add_pop_sub_one (x : Nat) :
    V_sub1 x = 2 * phi x + (popcount x : Int) - 1 := by
  unfold V_sub1
  have h := two_mul_phi x
  have halg1 : (popcount x : Int) * ((popcount x : Int) - 1) =
      (popcount x : Int) * (popcount x : Int) - (popcount x : Int) := by
    rw [Int.mul_sub, Int.mul_one]
  have halg2 : ((popcount x : Int) - 1) * ((popcount x : Int) - 1) =
      (popcount x : Int) * (popcount x : Int) - 2 * (popcount x : Int) + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one]
    omega
  omega

theorem V_sub1_nonneg {x : Nat} (hx : x ≠ 0) : 0 ≤ V_sub1 x := by
  rw [V_sub1_eq_two_phi_add_pop_sub_one]
  have h1 := phi_nonneg x
  have h2 := popcount_pos_of_ne_zero hx
  omega

theorem V_sub1_eq_zero_iff {x : Nat} (hx : x ≠ 0) : V_sub1 x = 0 ↔ x = 1 := by
  constructor
  · intro h
    rw [V_sub1_eq_two_phi_add_pop_sub_one] at h
    have h1 := phi_nonneg x
    have h2 := popcount_pos_of_ne_zero hx
    have hphi0 : phi x = 0 := by omega
    have hp1 : popcount x = 1 := by omega
    have hmer := (phi_eq_zero_iff x).mp hphi0
    rw [hp1] at hmer
    exact hmer
  · intro h; subst h
    have h1 : popcount 1 = 1 := popcount_two_pow_sub_one 1
    have h2 : phi 1 = 0 := phi_two_pow_sub_one 1
    rw [V_sub1_eq_two_phi_add_pop_sub_one, h1, h2]
    omega

theorem T_xor_m1_step_pot {x : Nat} (hx : x ≠ 0) :
    V_sub1 (T_xor_m1 x) = V_sub1 x - 1 := by
  have hstep : T_xor_m1 x = subcriticalClockCert.step x := by
    unfold T_xor_m1 ClockCert.step subcriticalClockCert
    simp [hx]
  rw [hstep, V_sub1_eq_cert_pot, V_sub1_eq_cert_pot]
  have hdom : subcriticalClockCert.Dom (popcount x) := popcount_pos_of_ne_zero hx
  rw [subcriticalClockCert.pot_step hdom]
  cases x.testBit (subcriticalClockCert.h (popcount x)) <;> rfl

theorem T_xor_m1_eq_zero_iff {x : Nat} (hx : x ≠ 0) : T_xor_m1 x = 0 ↔ x = 1 := by
  constructor
  · intro h0
    have hpot := T_xor_m1_step_pot hx
    rw [h0] at hpot
    have hV0 : V_sub1 0 = -1 := by
      unfold V_sub1 indexSum
      rw [weightSum_zero, popcount_zero]
      decide
    rw [hV0] at hpot
    exact (V_sub1_eq_zero_iff hx).mp (by omega)
  · intro h1; subst h1
    unfold T_xor_m1
    rw [popcount_two_pow_sub_one 1]
    decide

/-- **Theorem 2 (Sharp Phase Transition — Exact Global Termination at `c = -1`):**
    For EVERY positive integer `x : Nat` (`x ≠ 0`), `T_xor_m1` hits `1` in
    **EXACTLY `V_sub1 x`** steps and hits `0` in **EXACTLY `V_sub1 x + 1`** steps! -/
theorem T_xor_m1_hits_one_exact : ∀ (N x : Nat),
    x ≠ 0 → V_sub1 x = (N : Int) → iter T_xor_m1 N x = 1 := by
  intro N
  induction N with
  | zero =>
    intro x hx hV
    rw [iter_zero]
    exact (V_sub1_eq_zero_iff hx).mp hV
  | succ N ih =>
    intro x hx hV
    have hxne1 : x ≠ 1 := by
      intro h1
      have := (V_sub1_eq_zero_iff hx).mpr h1
      omega
    have hx'ne0 : T_xor_m1 x ≠ 0 := fun h0 => hxne1 ((T_xor_m1_eq_zero_iff hx).mp h0)
    have hV' : V_sub1 (T_xor_m1 x) = (N : Int) := by
      have := T_xor_m1_step_pot hx
      omega
    rw [iter_succ]
    exact ih (T_xor_m1 x) hx'ne0 hV'

theorem T_xor_m1_terminates_exact {x : Nat} (hx : x ≠ 0) :
    iter T_xor_m1 ((V_sub1 x).toNat + 1) x = 0 := by
  have hnn := V_sub1_nonneg hx
  have hN : ((V_sub1 x).toNat : Int) = V_sub1 x := Int.toNat_of_nonneg hnn
  rw [iter_succ_right, T_xor_m1_hits_one_exact (V_sub1 x).toNat x hx hN.symm]
  exact (T_xor_m1_eq_zero_iff (by decide)).mpr rfl

-- ============================================================================
-- Section 6: MECHANISM II — Hardware Borrow-Acceleration Engine & Theorem 3
-- ============================================================================

theorem testBit_ctzPosAux_eq_true : ∀ fuel n : Nat,
    n ≠ 0 → n ≤ fuel → n.testBit (ctzPosAux fuel n) = true := by
  intro fuel
  induction fuel with
  | zero => intro n hn hle; omega
  | succ fuel ih =>
    intro n hn hle
    unfold ctzPosAux
    simp only [hn, ↓reduceIte]
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte, Nat.testBit_zero]
      simp
    · simp only [hodd, ↓reduceIte]
      have hdiv_ne : n / 2 ≠ 0 := by omega
      have hdiv_le : n / 2 ≤ fuel := by omega
      rw [Nat.testBit_succ]
      exact ih (n / 2) hdiv_ne hdiv_le

theorem testBit_lt_ctzPosAux_eq_false : ∀ fuel n j : Nat,
    n ≠ 0 → n ≤ fuel → j < ctzPosAux fuel n → n.testBit j = false := by
  intro fuel
  induction fuel with
  | zero => intro n j _ _ hj; unfold ctzPosAux at hj; omega
  | succ fuel ih =>
    intro n j hn hle hj
    unfold ctzPosAux at hj
    simp only [hn, ↓reduceIte] at hj
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte] at hj; omega
    · simp only [hodd, ↓reduceIte] at hj
      cases j with
      | zero =>
        rw [Nat.testBit_zero]
        have hev : n % 2 = 0 := by omega
        simp [hev]
      | succ j' =>
        have hdiv_ne : n / 2 ≠ 0 := by omega
        have hdiv_le : n / 2 ≤ fuel := by omega
        rw [Nat.testBit_succ]
        exact ih (n / 2) j' hdiv_ne hdiv_le (by omega)

theorem testBit_ctzPos_eq_true {n : Nat} (hn : n ≠ 0) : n.testBit (ctzPos n) = true :=
  testBit_ctzPosAux_eq_true n n hn (Nat.le_refl n)

theorem testBit_lt_ctzPos_eq_false {n j : Nat} (hn : n ≠ 0) (hj : j < ctzPos n) :
    n.testBit j = false :=
  testBit_lt_ctzPosAux_eq_false n n j hn (Nat.le_refl n) hj

theorem shiftRight_ne_zero_of_exists_bit {x p q : Nat} (hpq : p ≤ q) (hbit : x.testBit q = true) :
    x >>> p ≠ 0 := by
  intro h0
  have h1 : (x >>> p).testBit (q - p) = true := by
    rw [Nat.testBit_shiftRight]
    have : p + (q - p) = q := by omega
    rw [this]; exact hbit
  rw [h0, Nat.zero_testBit] at h1
  cases h1

/-- **Mechanism II Core Telescope (`borrow_acceleration_c0`):**
    If `x` has `d` consecutive `0`-bits starting at `p = popcount x` followed by a `1`-bit
    at `p + d`, iterating `T_xor` exactly `d + 1` times equals hardware subtraction `x - 2^p`,
    and decrements `phi` by **EXACTLY `1`** independent of `d`! -/
theorem borrow_acceleration_c0 : ∀ (d x : Nat),
    (∀ j < d, x.testBit (popcount x + j) = false) →
    x.testBit (popcount x + d) = true →
    iter T_xor (d + 1) x = x - 2 ^ popcount x ∧
    phi (iter T_xor (d + 1) x) = phi x - 1 := by
  intro d
  induction d with
  | zero =>
    intro x _ hbit
    simp only [Nat.add_zero] at hbit
    have h1 : iter T_xor 1 x = T_xor x := rfl
    rw [h1]
    constructor
    · exact xor_two_pow_eq_sub hbit
    · rw [T_xor_phi_step, hbit]; simp
  | succ d ih =>
    intro x hzeros htop
    have hbit0 : x.testBit (popcount x) = false := by
      simpa using hzeros 0 (Nat.zero_lt_succ d)
    let p := popcount x
    have hx'_eq : T_xor x = x + 2 ^ p := xor_two_pow_eq_add hbit0
    have hp' : popcount (T_xor x) = p + 1 := popcount_xor_two_pow_false hbit0
    have hphi' : phi (T_xor x) = phi x := by
      rw [T_xor_phi_step, hbit0]; simp
    have hzeros' : ∀ j < d, (T_xor x).testBit (popcount (T_xor x) + j) = false := by
      intro j hj
      rw [hp']
      unfold T_xor
      rw [testBit_xor_two_pow_ne x p (p + 1 + j) (by omega)]
      have : p + 1 + j = p + (j + 1) := by omega
      rw [this]
      exact hzeros (j + 1) (by omega)
    have htop' : (T_xor x).testBit (popcount (T_xor x) + d) = true := by
      rw [hp']
      unfold T_xor
      rw [testBit_xor_two_pow_ne x p (p + 1 + d) (by omega)]
      have : p + 1 + d = p + (d + 1) := by omega
      rw [this]
      exact htop
    have ⟨hsub', hphi_final⟩ := ih (T_xor x) hzeros' htop'
    have hge_top : 2 ^ (popcount x + (d + 1)) ≤ x := two_pow_le_of_testBit_true htop
    have hge_p1 : 2 ^ (popcount x + 1) ≤ 2 ^ (popcount x + (d + 1)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow : 2 ^ (popcount x + 1) = 2 ^ popcount x + 2 ^ popcount x := by rw [Nat.pow_succ]; omega
    rw [iter_succ]
    constructor
    · rw [hsub', hp', hx'_eq]
      change x + 2 ^ popcount x - 2 ^ (popcount x + 1) = x - 2 ^ popcount x
      omega
    · rw [hphi_final, hphi']

/-- **Theorem 3A (Hardware Borrow-Acceleration Equivalence & Exact Inversion Clock, `c = 0`):** -/
theorem T_sub_borrow_acceleration {x : Nat} (hphi : 0 < phi x) :
    2 ^ popcount x ≤ x ∧
    T_sub x = iter T_xor (ctzPos (x >>> popcount x) + 1) x ∧
    phi (T_sub x) = phi x - 1 := by
  obtain ⟨q, hpq, hq⟩ := exists_set_bit_ge_popcount hphi
  have hge : 2 ^ popcount x ≤ x :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hpq) (two_pow_le_of_testBit_true hq)
  have hsh_ne : x >>> popcount x ≠ 0 := shiftRight_ne_zero_of_exists_bit hpq hq
  let d := ctzPos (x >>> popcount x)
  have hzeros : ∀ j < d, x.testBit (popcount x + j) = false := by
    intro j hj
    have := testBit_lt_ctzPos_eq_false hsh_ne hj
    rwa [Nat.testBit_shiftRight] at this
  have htop : x.testBit (popcount x + d) = true := by
    have := testBit_ctzPos_eq_true hsh_ne
    rwa [Nat.testBit_shiftRight] at this
  have ⟨heq, hph⟩ := borrow_acceleration_c0 d x hzeros htop
  refine ⟨hge, heq.symm, ?_⟩
  unfold T_sub
  rw [← heq]
  exact hph

/-- **Theorem 3B (Exact Mersenne Hitting Time for `T_sub`):**
    For EVERY `x : Nat`, `T_sub` hits a Mersenne number `2^k - 1` in **EXACTLY `phi x`** steps! -/
theorem T_sub_hits_mersenne_exact : ∀ (N x : Nat),
    phi x = (N : Int) →
    iter T_sub N x = 2 ^ popcount (iter T_sub N x) - 1 := by
  intro N
  induction N with
  | zero =>
    intro x hphi
    rw [iter_zero]
    exact (phi_eq_zero_iff x).mp hphi
  | succ N ih =>
    intro x hphi
    have hpos : 0 < phi x := by omega
    have ⟨_, _, hphi'⟩ := T_sub_borrow_acceleration hpos
    rw [iter_succ]
    exact ih (T_sub x) (by omega)

/-- Subcritical (`c = -1`) borrow-accelerated flow `T_sub_m1 x = x - 2^(s_2 x - 1)`. -/
def T_sub_m1 (x : Nat) : Nat :=
  if x = 0 then 0 else x - 2 ^ (popcount x - 1)

/-- Subcritical inversion-weight clock `psi x = phi x + popcount x`. -/
def psi (x : Nat) : Int := phi x + (popcount x : Int)

theorem T_xor_m1_psi_step {x : Nat} (hx : x ≠ 0) :
    psi (T_xor_m1 x) = psi x - if x.testBit (popcount x - 1) then 1 else 0 := by
  have hp1 : 1 ≤ popcount x := popcount_pos_of_ne_zero hx
  have hstep : T_xor_m1 x = x ^^^ 2 ^ (popcount x - 1) := by unfold T_xor_m1; simp [hx]
  have h1 := two_mul_phi x
  have h2 := two_mul_phi (T_xor_m1 x)
  unfold psi
  cases hbit : x.testBit (popcount x - 1)
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.sub_zero]
    rw [hstep] at h2 ⊢
    rw [popcount_xor_two_pow_false hbit] at h2 ⊢
    unfold indexSum at h1 h2
    rw [weightSum_xor_two_pow_false _ hbit] at h2
    have hcast1 : ((popcount x + 1 : Nat) : Int) = (popcount x : Int) + 1 := by omega
    have hcast2 : ((popcount x - 1 : Nat) : Int) = (popcount x : Int) - 1 := by omega
    have halg : ((popcount x + 1 : Nat) : Int) * (((popcount x + 1 : Nat) : Int) - 1) =
        (popcount x : Int) * ((popcount x : Int) - 1) + 2 * (popcount x : Int) := by
      rw [hcast1]
      have : (popcount x : Int) + 1 - 1 = (popcount x : Int) := by omega
      rw [this, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
      omega
    rw [halg, hcast2] at h2
    omega
  · simp only [↓reduceIte]
    rw [hstep] at h2 ⊢
    have hpop := popcount_xor_two_pow_true hbit
    have hpop' : popcount (x ^^^ 2 ^ (popcount x - 1)) = popcount x - 1 := by omega
    rw [hpop'] at h2 ⊢
    unfold indexSum at h1 h2
    rw [weightSum_xor_two_pow_true _ hbit] at h2
    have hcast2 : ((popcount x - 1 : Nat) : Int) = (popcount x : Int) - 1 := by omega
    have halg : ((popcount x - 1 : Nat) : Int) * (((popcount x - 1 : Nat) : Int) - 1) =
        (popcount x : Int) * ((popcount x : Int) - 1) - 2 * ((popcount x : Int) - 1) := by
      rw [hcast2, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.one_mul, Int.mul_one]
      omega
    rw [halg, hcast2] at h2
    omega

/-- Borrow-acceleration telescope for `c = -1`. -/
theorem borrow_acceleration_m1 : ∀ (d x : Nat),
    x ≠ 0 →
    (∀ j < d, x.testBit (popcount x - 1 + j) = false) →
    x.testBit (popcount x - 1 + d) = true →
    iter T_xor_m1 (d + 1) x = x - 2 ^ (popcount x - 1) ∧
    psi (iter T_xor_m1 (d + 1) x) = psi x - 1 := by
  intro d
  induction d with
  | zero =>
    intro x hx _ hbit
    simp only [Nat.add_zero] at hbit
    have h1 : iter T_xor_m1 1 x = T_xor_m1 x := rfl
    rw [h1]
    constructor
    · unfold T_xor_m1; simp only [hx, ↓reduceIte]; exact xor_two_pow_eq_sub hbit
    · rw [T_xor_m1_psi_step hx, hbit]; simp
  | succ d ih =>
    intro x hx hzeros htop
    have hp1 : 1 ≤ popcount x := popcount_pos_of_ne_zero hx
    have hbit0 : x.testBit (popcount x - 1) = false := by
      simpa using hzeros 0 (Nat.zero_lt_succ d)
    let q := popcount x - 1
    have hstep : T_xor_m1 x = x ^^^ 2 ^ q := by unfold T_xor_m1; simp [hx, q]
    have hx'_eq : T_xor_m1 x = x + 2 ^ q := by rw [hstep]; exact xor_two_pow_eq_add hbit0
    have hx'_ne : T_xor_m1 x ≠ 0 := by rw [hx'_eq]; have := Nat.two_pow_pos q; omega
    have hp' : popcount (T_xor_m1 x) = popcount x + 1 := by
      rw [hstep]; exact popcount_xor_two_pow_false hbit0
    have hq' : popcount (T_xor_m1 x) - 1 = q + 1 := by omega
    have hpsi' : psi (T_xor_m1 x) = psi x := by
      rw [T_xor_m1_psi_step hx, hbit0]; simp
    have hzeros' : ∀ j < d, (T_xor_m1 x).testBit (popcount (T_xor_m1 x) - 1 + j) = false := by
      intro j hj
      rw [hq', hstep, testBit_xor_two_pow_ne x q (q + 1 + j) (by omega)]
      have : q + 1 + j = q + (j + 1) := by omega
      rw [this]
      exact hzeros (j + 1) (by omega)
    have htop' : (T_xor_m1 x).testBit (popcount (T_xor_m1 x) - 1 + d) = true := by
      rw [hq', hstep, testBit_xor_two_pow_ne x q (q + 1 + d) (by omega)]
      have : q + 1 + d = q + (d + 1) := by omega
      rw [this]
      exact htop
    have ⟨hsub', hpsi_final⟩ := ih (T_xor_m1 x) hx'_ne hzeros' htop'
    have hge_top : 2 ^ (popcount x - 1 + (d + 1)) ≤ x := two_pow_le_of_testBit_true htop
    have hge_q1 : 2 ^ (popcount x - 1 + 1) ≤ 2 ^ (popcount x - 1 + (d + 1)) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow : 2 ^ (popcount x - 1 + 1) = 2 ^ (popcount x - 1) + 2 ^ (popcount x - 1) := by
      rw [Nat.pow_succ]; omega
    rw [iter_succ]
    constructor
    · rw [hsub', hq', hx'_eq]
      change x + 2 ^ (popcount x - 1) - 2 ^ (popcount x - 1 + 1) = x - 2 ^ (popcount x - 1)
      omega
    · rw [hpsi_final, hpsi']

/-- **Theorem 3C (Subcritical Borrow Acceleration & Exact Global Termination in `phi x + s_2 x` Steps):** -/
theorem T_sub_m1_borrow_acceleration {x : Nat} (hx : x ≠ 0) :
    2 ^ (popcount x - 1) ≤ x ∧
    T_sub_m1 x = iter T_xor_m1 (ctzPos (x >>> (popcount x - 1)) + 1) x ∧
    psi (T_sub_m1 x) = psi x - 1 := by
  obtain ⟨q, hpq, hq⟩ := exists_set_bit_ge_popcount_sub_one hx
  have hge : 2 ^ (popcount x - 1) ≤ x :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hpq) (two_pow_le_of_testBit_true hq)
  have hsh_ne : x >>> (popcount x - 1) ≠ 0 := shiftRight_ne_zero_of_exists_bit hpq hq
  let d := ctzPos (x >>> (popcount x - 1))
  have hzeros : ∀ j < d, x.testBit (popcount x - 1 + j) = false := by
    intro j hj
    have := testBit_lt_ctzPos_eq_false hsh_ne hj
    rwa [Nat.testBit_shiftRight] at this
  have htop : x.testBit (popcount x - 1 + d) = true := by
    have := testBit_ctzPos_eq_true hsh_ne
    rwa [Nat.testBit_shiftRight] at this
  have ⟨heq, hps⟩ := borrow_acceleration_m1 d x hx hzeros htop
  have hdef : T_sub_m1 x = x - 2 ^ (popcount x - 1) := by unfold T_sub_m1; simp [hx]
  refine ⟨hge, by rw [hdef, heq], ?_⟩
  rw [hdef, ← heq]
  exact hps

theorem psi_nonneg (x : Nat) : 0 ≤ psi x := by
  unfold psi; have := phi_nonneg x; omega

theorem psi_eq_zero_iff (x : Nat) : psi x = 0 ↔ x = 0 := by
  unfold psi
  have h1 := phi_nonneg x
  constructor
  · intro h
    have hp0 : popcount x = 0 := by omega
    exact (popcount_eq_zero_iff x).mp hp0
  · intro h; subst h
    have : phi 0 = 0 := (phi_eq_zero_iff 0).mpr rfl
    rw [this, popcount_zero]; omega

theorem T_sub_m1_hits_zero_exact : ∀ (N x : Nat),
    psi x = (N : Int) → iter T_sub_m1 N x = 0 := by
  intro N
  induction N with
  | zero =>
    intro x hpsi
    rw [iter_zero]
    exact (psi_eq_zero_iff x).mp hpsi
  | succ N ih =>
    intro x hpsi
    have hx : x ≠ 0 := fun h0 => by
      have := (psi_eq_zero_iff x).mpr h0; omega
    have ⟨_, _, hpsi'⟩ := T_sub_m1_borrow_acceleration hx
    rw [iter_succ]
    exact ih (T_sub_m1 x) (by omega)

-- ============================================================================
-- Section 7: Theorem 4 — Finite-Width Wrapping Attractors & Complement Duality
-- ============================================================================

/-- Finite-width bit permutation on `Fin w`. -/
structure BitPerm (w : Nat) where
  f    : Fin w → Fin w
  inv  : Fin w → Fin w
  left  : ∀ i, inv (f i) = i
  right : ∀ i, f (inv i) = i

/-- General permuted carry-free modular flow on `[0, 2^w)` with wrap-around index `k : Fin w`. -/
def F_wrap (w : Nat) (π : BitPerm w) (k : Fin w) (x : Nat) : Nat :=
  if h : popcount x < w then
    x ^^^ 2 ^ (π.f ⟨popcount x, h⟩).val
  else
    x ^^^ 2 ^ (π.f k).val

/-- Permuted unit-clock potential `V_π(x) = 2 * ∑_{r < w} r * x_{π(r)} - s_2(x)^2`. -/
def V_perm (w : Nat) (π : BitPerm w) (x : Nat) : Int :=
  weightSum (fun i => if h : i < w then 2 * ((π.inv ⟨i, h⟩).val : Int) else 0) x
    - (popcount x : Int) * (popcount x : Int)

/-- Permuted ClockCert for `F_wrap` on active domain `p < w`. -/
def permClockCert (w : Nat) (π : BitPerm w) (k : Fin w) : ClockCert where
  h := fun p => if hp : p < w then (π.f ⟨p, hp⟩).val else (π.f k).val
  μ := fun i => if hi : i < w then 2 * ((π.inv ⟨i, hi⟩).val : Int) else 0
  g := fun p => (p : Int) * (p : Int)
  δ_up := 1
  δ_down := 1
  Dom := fun p => p < w
  diff_up := fun p hp => by
    simp only [hp, ↓reduceDIte, Fin.isLt, Fin.eta, π.left]
    have h1 : ((p + 1 : Nat) : Int) = (p : Int) + 1 := by omega
    rw [h1, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
    omega
  diff_down := fun p hp hp1 => by
    simp only [hp, ↓reduceDIte, Fin.isLt, Fin.eta, π.left]
    have h1 : ((p - 1 : Nat) : Int) = (p : Int) - 1 := by omega
    rw [h1, Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one]
    omega

/-- Permuted bit-word: bit `r` of `pullbackBits w π x w` is bit `π.f r` of `x`. -/
def pullbackBits (w : Nat) (π : BitPerm w) (x : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 =>
    pullbackBits w π x b +
      if hb : b < w then (if x.testBit (π.f ⟨b, hb⟩).val then 2 ^ b else 0) else 0

theorem pullbackBits_lt_two_pow (w : Nat) (π : BitPerm w) (x : Nat) :
    ∀ b, pullbackBits w π x b < 2 ^ b
  | 0 => by simp [pullbackBits]
  | b + 1 => by
    unfold pullbackBits
    have ih := pullbackBits_lt_two_pow w π x b
    rw [Nat.pow_succ]
    split
    · split <;> omega
    · omega

theorem testBit_pullbackBits (w : Nat) (π : BitPerm w) (x : Nat) :
    ∀ b i, (pullbackBits w π x b).testBit i =
      if i < b then
        if hw : i < w then x.testBit (π.f ⟨i, hw⟩).val else false
      else false := by
  intro b
  induction b with
  | zero => intro i; simp [pullbackBits]
  | succ b ih =>
    intro i
    unfold pullbackBits
    have hlt := pullbackBits_lt_two_pow w π x b
    split
    · next hb =>
      cases hbit : x.testBit (π.f ⟨b, hb⟩).val
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [ih i]
        by_cases hib : i = b
        · subst hib; simp [hb, hbit]
        · by_cases hi : i < b
          · simp [hi, show i < b + 1 by omega]
          · simp [hi, show ¬ (i < b + 1) by omega]
      · simp only [↓reduceIte]
        have hbf : (pullbackBits w π x b).testBit b = false := Nat.testBit_lt_two_pow hlt
        rw [← xor_two_pow_eq_add hbf]
        by_cases hib : i = b
        · subst hib; simp [hbf, hb, hbit]
        · rw [testBit_xor_two_pow_ne _ b i (Ne.symm hib), ih i]
          by_cases hi : i < b
          · simp [hi, show i < b + 1 by omega]
          · simp [hi, show ¬ (i < b + 1) by omega]
    · next hnb =>
      simp only [Nat.add_zero]
      rw [ih i]
      by_cases hib : i = b
      · subst hib; simp [hnb]
      · by_cases hi : i < b
        · simp [hi, show i < b + 1 by omega]
        · simp [hi, show ¬ (i < b + 1) by omega]

/-- Helper: `pullbackBits` commutes with flipping a single bit `j < w` to `π.inv j`. -/
theorem pullbackBits_xor_bit (w : Nat) (π : BitPerm w) (x : Nat) {j : Nat} (hjlt : j < w) :
    pullbackBits w π (x ^^^ 2 ^ j) w = pullbackBits w π x w ^^^ 2 ^ (π.inv ⟨j, hjlt⟩).val := by
  let r := (π.inv ⟨j, hjlt⟩).val
  have hrlt : r < w := (π.inv ⟨j, hjlt⟩).isLt
  have hfr : (π.f ⟨r, hrlt⟩).val = j := congrArg Fin.val (π.right ⟨j, hjlt⟩)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pullbackBits, Nat.testBit_xor, testBit_pullbackBits, Nat.testBit_two_pow]
  by_cases hiw : i < w
  · simp only [hiw, ↓reduceIte, ↓reduceDIte]
    by_cases hir : r = i
    · subst hir
      simp only [hfr]
      rw [testBit_xor_two_pow_self]
      have hdec : decide ((π.inv ⟨j, hjlt⟩).val = r) = true := by simp [r]
      rw [hdec]
      cases x.testBit j <;> rfl
    · have hneq : (π.f ⟨i, hiw⟩).val ≠ j := by
        intro heq
        have hinv := congrArg π.inv (Fin.ext heq : π.f ⟨i, hiw⟩ = ⟨j, hjlt⟩)
        rw [π.left] at hinv
        exact hir (congrArg Fin.val hinv).symm
      have hbf : decide ((π.inv ⟨j, hjlt⟩).val = i) = false := by
        have : (π.inv ⟨j, hjlt⟩).val ≠ i := hir
        simp [this]
      rw [hbf, Bool.xor_false]
      exact testBit_xor_two_pow_ne x j (π.f ⟨i, hiw⟩).val hneq.symm
  · have hri : (π.inv ⟨j, hjlt⟩).val ≠ i := by omega
    simp [hiw, hri]

theorem pullbackBits_zero (w : Nat) (π : BitPerm w) : pullbackBits w π 0 w = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pullbackBits, Nat.zero_testBit]
  by_cases hi : i < w <;> simp [hi]

theorem weightSumBelow_zero_val (μ : Nat → Int) : ∀ B, weightSumBelow μ 0 B = 0
  | 0 => rfl
  | b + 1 => by simp [weightSumBelow, weightSumBelow_zero_val μ b]

/-- General bijection-sum preservation under `pullbackBits` (proved by peeling lowest set bit). -/
theorem weightSumBelow_pullback_eq (w : Nat) (π : BitPerm w) (g : Nat → Int) :
    ∀ x < 2 ^ w,
      weightSumBelow (fun r => if hr : r < w then g (π.f ⟨r, hr⟩).val else 0)
        (pullbackBits w π x w) w =
      weightSumBelow g x w := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [pullbackBits_zero, weightSumBelow_zero_val, weightSumBelow_zero_val]
    · let j := ctzPos x
      have hjbit : x.testBit j = true := testBit_ctzPos_eq_true hx0
      have hjlt : j < w := by
        apply Classical.byContradiction
        intro hge
        have hge' : w ≤ j := by omega
        have := testBit_eq_false_of_lt_two_pow hx hge'
        rw [this] at hjbit; cases hjbit
      let x' := x ^^^ 2 ^ j
      have hx'lt_x : x' < x := by
        have := xor_two_pow_add_eq hjbit; have := Nat.two_pow_pos j; omega
      have hx'lt_2w : x' < 2 ^ w := Nat.lt_trans hx'lt_x hx
      let r := (π.inv ⟨j, hjlt⟩).val
      have hrlt : r < w := (π.inv ⟨j, hjlt⟩).isLt
      have hfr : (π.f ⟨r, hrlt⟩).val = j := congrArg Fin.val (π.right ⟨j, hjlt⟩)
      have hrbit : (pullbackBits w π x w).testBit r = true := by
        rw [testBit_pullbackBits]; simp [hrlt, hfr, hjbit]
      have hih := ih x' hx'lt_x hx'lt_2w
      rw [show pullbackBits w π x' w = pullbackBits w π x w ^^^ 2 ^ r from
            pullbackBits_xor_bit w π x hjlt] at hih
      rw [weightSumBelow_xor_two_pow_true _ hrlt hrbit] at hih
      rw [weightSumBelow_xor_two_pow_true _ hjlt hjbit] at hih
      simp only [hrlt, ↓reduceDIte, hfr] at hih
      omega

theorem popcount_pullback_eq (w : Nat) (π : BitPerm w) {x : Nat} (hx : x < 2 ^ w) :
    popcount (pullbackBits w π x w) = popcount x := by
  have hlt := pullbackBits_lt_two_pow w π x w
  rw [popcount_eq_below hlt, popcount_eq_below hx]
  have h1 := weightSumBelow_pullback_eq w π (fun _ => 1) x hx
  have hws_one : ∀ y B, weightSumBelow (fun _ => (1 : Int)) y B = (popcountBelow y B : Int) := by
    intro y B; induction B with
    | zero => rfl
    | succ b ih => unfold weightSumBelow popcountBelow; rw [ih]; cases y.testBit b <;> simp <;> omega
  have hws_one_ite : ∀ y B, B ≤ w →
      weightSumBelow (fun r => if _ : r < w then (1 : Int) else 0) y B = (popcountBelow y B : Int) := by
    intro y B hBw; induction B with
    | zero => rfl
    | succ b ih =>
      unfold weightSumBelow popcountBelow; rw [ih (by omega)]
      have hb : b < w := by omega
      simp only [hb, ↓reduceDIte]
      cases y.testBit b <;> simp <;> omega
  rw [hws_one_ite _ w (Nat.le_refl w), hws_one] at h1
  omega

theorem V_perm_eq_V_unit_pullback (w : Nat) (π : BitPerm w) {x : Nat} (hx : x < 2 ^ w) :
    V_perm w π x = V_unit (pullbackBits w π x w) := by
  unfold V_perm V_unit indexSum
  rw [popcount_pullback_eq w π hx]
  have hlt := pullbackBits_lt_two_pow w π x w
  rw [weightSum_eq_below _ hx, weightSum_eq_below _ hlt]
  have hbij := weightSumBelow_pullback_eq w π
    (fun i => if h : i < w then 2 * ((π.inv ⟨i, h⟩).val : Int) else 0) x hx
  have hsimp : ∀ y B, B ≤ w →
      weightSumBelow
        (fun r => if hr : r < w then
          (if h : (π.f ⟨r, hr⟩).val < w then 2 * ((π.inv ⟨(π.f ⟨r, hr⟩).val, h⟩).val : Int) else 0)
        else 0) y B =
      2 * weightSumBelow (fun i => (i : Int)) y B := by
    intro y B hBw
    induction B with
    | zero => rfl
    | succ b ih =>
      unfold weightSumBelow
      rw [ih (by omega)]
      have hb : b < w := by omega
      simp only [hb, ↓reduceDIte, Fin.isLt, Fin.eta, π.left]
      cases y.testBit b <;> simp <;> omega
  rw [hsimp _ w (Nat.le_refl w)] at hbij
  rw [← hbij]

theorem F_wrap_lt_two_pow (w : Nat) (π : BitPerm w) (k : Fin w) {x : Nat} (hx : x < 2 ^ w) :
    F_wrap w π k x < 2 ^ w := by
  unfold F_wrap
  split
  · next h => exact xor_lt_two_pow hx (two_pow_lt_two_pow (π.f ⟨popcount x, h⟩).isLt)
  · exact xor_lt_two_pow hx (two_pow_lt_two_pow (π.f k).isLt)

theorem V_perm_step {w : Nat} (π : BitPerm w) (k : Fin w) {x : Nat}
    (hx : x < 2 ^ w) (hne : x ≠ 2 ^ w - 1) :
    V_perm w π (F_wrap w π k x) = V_perm w π x - 1 := by
  have hple : popcount x ≤ w := popcount_le_of_lt_two_pow hx
  have hpne : popcount x ≠ w := fun h => hne ((eq_two_pow_sub_one_iff_popcount hx).mpr h)
  have hplt : popcount x < w := by omega
  have hpot1 : V_perm w π x = (permClockCert w π k).pot x := rfl
  have hpot2 : V_perm w π (F_wrap w π k x) =
      (permClockCert w π k).pot ((permClockCert w π k).step x) := by
    unfold V_perm ClockCert.pot ClockCert.step F_wrap permClockCert
    simp only [hplt, ↓reduceDIte]
  rw [hpot2, (permClockCert w π k).pot_step hplt, ← hpot1]
  cases x.testBit ((permClockCert w π k).h (popcount x)) <;> rfl

theorem V_perm_add_w_nonneg (w : Nat) (π : BitPerm w) {x : Nat} (hx : x < 2 ^ w) :
    0 ≤ V_perm w π x + (w : Int) := by
  rw [V_perm_eq_V_unit_pullback w π hx]
  exact V_unit_add_width_nonneg (pullbackBits_lt_two_pow w π x w)

theorem V_perm_add_w_eq_zero_iff (w : Nat) (π : BitPerm w) {x : Nat} (hx : x < 2 ^ w) :
    V_perm w π x + (w : Int) = 0 ↔ x = 2 ^ w - 1 := by
  rw [V_perm_eq_V_unit_pullback w π hx,
      V_unit_add_width_eq_zero_iff (pullbackBits_lt_two_pow w π x w),
      eq_two_pow_sub_one_iff_popcount (pullbackBits_lt_two_pow w π x w),
      popcount_pullback_eq w π hx,
      ← eq_two_pow_sub_one_iff_popcount hx]

/-- **Theorem 4A (Exact Hitting Time to `2^w - 1` for ANY Permuted Modular Flow):** -/
theorem F_wrap_hits_all_ones_exact (w : Nat) (π : BitPerm w) (k : Fin w) :
    ∀ (N x : Nat), x < 2 ^ w → V_perm w π x + (w : Int) = (N : Int) →
    iter (F_wrap w π k) N x = 2 ^ w - 1 ∧
    (∀ t < N, iter (F_wrap w π k) t x ≠ 2 ^ w - 1) := by
  intro N
  induction N with
  | zero =>
    intro x hx hV
    exact ⟨(V_perm_add_w_eq_zero_iff w π hx).mp hV, fun t ht => by omega⟩
  | succ N ih =>
    intro x hx hV
    have hne : x ≠ 2 ^ w - 1 := fun h => by
      have := (V_perm_add_w_eq_zero_iff w π hx).mpr h; omega
    have hx' : F_wrap w π k x < 2 ^ w := F_wrap_lt_two_pow w π k hx
    have hV' : V_perm w π (F_wrap w π k x) + (w : Int) = (N : Int) := by
      have := V_perm_step π k hx hne; omega
    have ⟨hhit, hmin⟩ := ih (F_wrap w π k x) hx' hV'
    constructor
    · rw [iter_succ]; exact hhit
    · intro t ht
      cases t with
      | zero => exact hne
      | succ t' => rw [iter_succ]; exact hmin t' (by omega)

/-- **Theorem 4B (Unique Global Attractor Cycle of Exact Length `2 * (w - k)`):** -/
theorem F_wrap_unique_cycle_exact_period (w : Nat) (π : BitPerm w) (k : Fin w) :
    iter (F_wrap w π k) (2 * (w - k.val)) (2 ^ w - 1) = 2 ^ w - 1 ∧
    (∀ t, 0 < t → t < 2 * (w - k.val) → iter (F_wrap w π k) t (2 ^ w - 1) ≠ 2 ^ w - 1) := by
  have hklt : k.val < w := k.isLt
  have h1lt : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) (by decide)
  have hpop1 : popcount (2 ^ w - 1) = w := popcount_two_pow_sub_one w
  let x1 := F_wrap w π k (2 ^ w - 1)
  have hx1_def : x1 = (2 ^ w - 1) ^^^ 2 ^ (π.f k).val := by
    change F_wrap w π k (2 ^ w - 1) = _
    unfold F_wrap; simp [hpop1]
  have hx1_lt : x1 < 2 ^ w := F_wrap_lt_two_pow w π k h1lt
  have hbitk : (2 ^ w - 1).testBit (π.f k).val = true := by
    rw [testBit_two_pow_sub_one]; simp [(π.f k).isLt]
  have hV_all1 : V_perm w π (2 ^ w - 1) = -(w : Int) := by
    have := (V_perm_add_w_eq_zero_iff w π h1lt).mpr rfl; omega
  have hV_x1 : V_perm w π x1 + (w : Int) = ((2 * (w - k.val) - 1 : Nat) : Int) := by
    unfold V_perm at hV_all1 ⊢
    rw [hx1_def]
    have hpop_x1 : popcount ((2 ^ w - 1) ^^^ 2 ^ (π.f k).val) = w - 1 := by
      have := popcount_xor_two_pow_true hbitk; omega
    rw [weightSum_xor_two_pow_true _ hbitk, hpop_x1]
    rw [hpop1] at hV_all1
    simp only [(π.f k).isLt, ↓reduceDIte, Fin.eta, π.left]
    have hw1 : ((w - 1 : Nat) : Int) = (w : Int) - 1 := by omega
    rw [hw1]
    have hsq : ((w : Int) - 1) * ((w : Int) - 1) = (w : Int) * (w : Int) - 2 * (w : Int) + 1 := by
      rw [Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one]; omega
    rw [hsq]
    omega
  have ⟨hhit, hmin⟩ := F_wrap_hits_all_ones_exact w π k (2 * (w - k.val) - 1) x1 hx1_lt hV_x1
  have hper : 2 * (w - k.val) = (2 * (w - k.val) - 1) + 1 := by omega
  constructor
  · rw [hper, iter_succ]; exact hhit
  · intro t ht0 htlt
    cases t with
    | zero => omega
    | succ t' => rw [iter_succ]; exact hmin t' (by omega)

/-- Corollary for the canonical modular carry-free flow `x ^^^ 2^(popcount x % w)` (period `2 * w`). -/
def idPerm (w : Nat) : BitPerm w where
  f := id
  inv := id
  left := fun _ => rfl
  right := fun _ => rfl

theorem F_xor_wrap_eq_F_wrap {w : Nat} (hw : 0 < w) {x : Nat} (hx : x < 2 ^ w) :
    F_xor_wrap w x = F_wrap w (idPerm w) ⟨0, hw⟩ x := by
  unfold F_xor_wrap F_wrap idPerm
  have hle : popcount x ≤ w := popcount_le_of_lt_two_pow hx
  by_cases hlt : popcount x < w
  · simp [hlt, Nat.mod_eq_of_lt hlt]
  · have heq : popcount x = w := by omega
    simp [heq]

theorem F_xor_wrap_iter_eq {w : Nat} (hw : 0 < w) :
    ∀ t x, x < 2 ^ w → iter (F_xor_wrap w) t x = iter (F_wrap w (idPerm w) ⟨0, hw⟩) t x := by
  intro t
  induction t with
  | zero => intro x _; rfl
  | succ t ih =>
    intro x hx
    rw [iter_succ, iter_succ, F_xor_wrap_eq_F_wrap hw hx]
    exact ih _ (F_wrap_lt_two_pow w (idPerm w) ⟨0, hw⟩ hx)

/-- **Theorem 4C (Canonical Carry-Free Modular Flow: Exact Unique `2w`-Cycle for All `w ≥ 1`):** -/
theorem F_xor_wrap_unique_2w_cycle {w : Nat} (hw : 0 < w) :
    (∀ x < 2 ^ w, ∃ t, iter (F_xor_wrap w) t x = 2 ^ w - 1) ∧
    iter (F_xor_wrap w) (2 * w) (2 ^ w - 1) = 2 ^ w - 1 ∧
    (∀ t, 0 < t → t < 2 * w → iter (F_xor_wrap w) t (2 ^ w - 1) ≠ 2 ^ w - 1) := by
  have h1lt : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) (by decide)
  have ⟨hper, hmin⟩ := F_wrap_unique_cycle_exact_period w (idPerm w) ⟨0, hw⟩
  simp only [Nat.sub_zero] at hper hmin
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hnn := V_perm_add_w_nonneg w (idPerm w) hx
    refine ⟨(V_perm w (idPerm w) x + (w : Int)).toNat, ?_⟩
    rw [F_xor_wrap_iter_eq hw _ x hx]
    exact (F_wrap_hits_all_ones_exact w (idPerm w) ⟨0, hw⟩ _ x hx (Int.toNat_of_nonneg hnn).symm).1
  · rw [F_xor_wrap_iter_eq hw (2 * w) (2 ^ w - 1) h1lt]; exact hper
  · intro t ht0 htlt
    rw [F_xor_wrap_iter_eq hw t (2 ^ w - 1) h1lt]; exact hmin t ht0 htlt

-- ----------------------------------------------------------------------------
-- Theorem 4D: Borrow-Coupled Modular Flow `F_sub_wrap w` (Unique `(w+1)`-Cycle)
-- ----------------------------------------------------------------------------

theorem F_sub_wrap_lt_two_pow (w : Nat) (x : Nat) :
    F_sub_wrap w x < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

theorem F_sub_wrap_of_phi_pos {w x : Nat} (hx : x < 2 ^ w) (hphi : 0 < phi x) :
    F_sub_wrap w x = T_sub x := by
  have hne : x ≠ 2 ^ w - 1 := fun h => by
    rw [h, phi_two_pow_sub_one] at hphi; omega
  have hple : popcount x ≤ w := popcount_le_of_lt_two_pow hx
  have hpne : popcount x ≠ w := fun h => hne ((eq_two_pow_sub_one_iff_popcount hx).mpr h)
  have hplt : popcount x < w := by omega
  have ⟨hge, _, _⟩ := T_sub_borrow_acceleration hphi
  unfold F_sub_wrap T_sub
  rw [Nat.mod_eq_of_lt hplt]
  have hrew : x + 2 ^ w - 2 ^ popcount x = (x - 2 ^ popcount x) + 2 ^ w := by omega
  have hlt_sub : x - 2 ^ popcount x < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le x _) hx
  rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_sub]

/-- All `w` Mersenne numbers `2^p - 1` (`p < w`) collide in 1 step onto `2^w - 1`! -/
theorem F_sub_wrap_mersenne_collision {w p : Nat} (hp : p < w) :
    F_sub_wrap w (2 ^ p - 1) = 2 ^ w - 1 := by
  unfold F_sub_wrap
  rw [popcount_two_pow_sub_one, Nat.mod_eq_of_lt hp]
  have h1 : 1 ≤ 2 ^ p := Nat.two_pow_pos p
  have h2 : 1 ≤ 2 ^ w := Nat.two_pow_pos w
  have hrew : 2 ^ p - 1 + 2 ^ w - 2 ^ p = 2 ^ w - 1 := by omega
  rw [hrew, Nat.mod_eq_of_lt (by omega)]

theorem F_sub_wrap_all_ones {w : Nat} (hw : 0 < w) :
    F_sub_wrap w (2 ^ w - 1) = 2 ^ w - 2 := by
  unfold F_sub_wrap
  rw [popcount_two_pow_sub_one, Nat.mod_self]
  have h2 : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    simpa using this
  have hrew : 2 ^ w - 1 + 2 ^ w - 2 ^ 0 = (2 ^ w - 2) + 2 ^ w := by omega
  have hlt2 : 2 ^ w - 2 < 2 ^ w := by omega
  rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]

/-- Exact inversion energy of `2^w - 2`: `phi (2^w - 2) = w - 1`. -/
theorem phi_two_pow_sub_two {w : Nat} (hw : 0 < w) :
    phi (2 ^ w - 2) = (w : Int) - 1 := by
  have hbit0 : (2 ^ w - 1).testBit 0 = true := by
    rw [testBit_two_pow_sub_one]; simp [hw]
  have h1 : 2 ^ w - 2 = (2 ^ w - 1) ^^^ 2 ^ 0 := by
    rw [xor_two_pow_eq_sub hbit0]
    have : (2 : Nat) ^ 0 = 1 := rfl
    omega
  have hpop : popcount (2 ^ w - 2) = w - 1 := by
    rw [h1]
    have := popcount_xor_two_pow_true hbit0
    rw [popcount_two_pow_sub_one] at this
    omega
  have hidx : indexSum (2 ^ w - 2) = indexSum (2 ^ w - 1) := by
    rw [h1]; unfold indexSum
    rw [weightSum_xor_two_pow_true _ hbit0]
    simp
  have h2 := two_mul_phi (2 ^ w - 2)
  rw [hpop, hidx, indexSum_two_pow_sub_one] at h2
  have hw1 : ((w - 1 : Nat) : Int) = (w : Int) - 1 := by omega
  rw [hw1] at h2
  have halg : ((w : Int) - 1) * ((w : Int) - 1 - 1) =
      (w : Int) * ((w : Int) - 1) - 2 * ((w : Int) - 1) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.one_mul, Int.mul_one]
    omega
  rw [halg] at h2
  omega

/-- Every `x < 2^w` with `x ≠ 2^w - 1` hits `2^w - 1` under `F_sub_wrap w` in **EXACTLY `phi x + 1`** steps! -/
theorem F_sub_wrap_hits_all_ones_exact {w : Nat} :
    ∀ (N x : Nat), x < 2 ^ w → x ≠ 2 ^ w - 1 → phi x = (N : Int) →
    iter (F_sub_wrap w) (N + 1) x = 2 ^ w - 1 ∧
    (∀ t ≤ N, iter (F_sub_wrap w) t x ≠ 2 ^ w - 1) := by
  intro N
  induction N with
  | zero =>
    intro x hx hne hphi
    have hmer : x = 2 ^ popcount x - 1 := (phi_eq_zero_iff x).mp hphi
    have hplt : popcount x < w := by
      have hle := popcount_le_of_lt_two_pow hx
      have hpne : popcount x ≠ w := fun h => hne ((eq_two_pow_sub_one_iff_popcount hx).mpr h)
      omega
    constructor
    · rw [iter_succ, iter_zero, hmer]
      exact F_sub_wrap_mersenne_collision hplt
    · intro t ht
      have ht0 : t = 0 := by omega
      subst ht0; exact hne
  | succ N ih =>
    intro x hx hne hphi
    have hpos : 0 < phi x := by omega
    have hstep : F_sub_wrap w x = T_sub x := F_sub_wrap_of_phi_pos hx hpos
    have ⟨hge, _, hphi'⟩ := T_sub_borrow_acceleration hpos
    have h2w : 1 ≤ 2 ^ w := Nat.two_pow_pos w
    have hx'lt : T_sub x < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le x _) hx
    have hx'ne : T_sub x ≠ 2 ^ w - 1 := by
      intro heq
      have h2p : 1 ≤ 2 ^ popcount x := Nat.two_pow_pos _
      unfold T_sub at heq
      omega
    have ⟨hhit, hmin⟩ := ih (T_sub x) hx'lt hx'ne (by omega)
    constructor
    · rw [iter_succ, hstep]; exact hhit
    · intro t ht
      cases t with
      | zero => exact hne
      | succ t' => rw [iter_succ, hstep]; exact hmin t' (by omega)

/-- **Theorem 4D (Borrow-Coupled Modular Flow: Unique Global `(w + 1)`-Cycle for ALL `w ≥ 1`):** -/
theorem F_sub_wrap_unique_cycle {w : Nat} (hw : 0 < w) :
    (∀ x < 2 ^ w, ∃ t, iter (F_sub_wrap w) t x = 2 ^ w - 1) ∧
    iter (F_sub_wrap w) (w + 1) (2 ^ w - 1) = 2 ^ w - 1 ∧
    (∀ t, 0 < t → t < w + 1 → iter (F_sub_wrap w) t (2 ^ w - 1) ≠ 2 ^ w - 1) := by
  have h2lt : 2 ^ w - 2 < 2 ^ w := by
    have : 2 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
    omega
  have h2ne : 2 ^ w - 2 ≠ 2 ^ w - 1 := by
    have : 2 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
    omega
  have hphi2 : phi (2 ^ w - 2) = ((w - 1 : Nat) : Int) := by
    rw [phi_two_pow_sub_two hw]; omega
  have ⟨hhit2, hmin2⟩ := F_sub_wrap_hits_all_ones_exact (w := w) (w - 1) (2 ^ w - 2) h2lt h2ne hphi2
  have hw1 : (w - 1) + 1 = w := by omega
  rw [hw1] at hhit2
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases h1 : x = 2 ^ w - 1
    · exact ⟨0, h1⟩
    · have hnn := phi_nonneg x
      refine ⟨(phi x).toNat + 1, ?_⟩
      exact (F_sub_wrap_hits_all_ones_exact (w := w) (phi x).toNat x hx h1 (Int.toNat_of_nonneg hnn).symm).1
  · rw [iter_succ, F_sub_wrap_all_ones hw]; exact hhit2
  · intro t ht0 htlt
    cases t with
    | zero => omega
    | succ t' =>
      rw [iter_succ, F_sub_wrap_all_ones hw]
      exact hmin2 t' (by omega)

-- ----------------------------------------------------------------------------
-- Theorem 4E: Exact Bitwise-Complement Carry-Borrow Duality
-- ----------------------------------------------------------------------------

theorem comp_invol {w x : Nat} (hx : x < 2 ^ w) : comp w (comp w x) = x := by
  unfold comp; omega

theorem comp_lt_two_pow {w x : Nat} (hx : x < 2 ^ w) : comp w x < 2 ^ w := by
  unfold comp; have := Nat.two_pow_pos w; omega

/-- Helper: `comp w x = (2^w - 1) ^^^ x` for `x < 2^w`, proved by induction on `w`. -/
theorem comp_eq_xor : ∀ w x, x < 2 ^ w → comp w x = (2 ^ w - 1) ^^^ x := by
  intro w
  induction w with
  | zero =>
    intro x hx
    have : x = 0 := by omega
    subst this; decide
  | succ w ih =>
    intro x hx
    have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
    have hdiv_lt : x / 2 < 2 ^ w := by omega
    have hih := ih (x / 2) hdiv_lt
    unfold comp at hih ⊢
    have h2w : 1 ≤ 2 ^ w := Nat.two_pow_pos w
    have hdiv_l : (2 ^ (w + 1) - 1 - x) / 2 = 2 ^ w - 1 - x / 2 := by omega
    have hdiv_r : ((2 ^ (w + 1) - 1) ^^^ x) / 2 = (2 ^ w - 1) ^^^ (x / 2) := by
      rw [xor_div_two]
      have : (2 ^ (w + 1) - 1) / 2 = 2 ^ w - 1 := by omega
      rw [this]
    have hmod_eq : (2 ^ (w + 1) - 1 - x) % 2 = ((2 ^ (w + 1) - 1) ^^^ x) % 2 := by
      apply mod_two_eq_of_testBit_zero
      rw [Nat.testBit_xor, testBit_two_pow_sub_one]
      have h0 : 0 < w + 1 := Nat.zero_lt_succ w
      simp only [h0, decide_true, Bool.true_xor]
      rw [Nat.testBit_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one x with hm | hm
      · have hodd : (2 ^ (w + 1) - 1 - x) % 2 = 1 := by omega
        simp [hm, hodd]
      · have hev : (2 ^ (w + 1) - 1 - x) % 2 = 0 := by omega
        simp [hm, hev]
    omega

theorem testBit_comp {w x i : Nat} (hx : x < 2 ^ w) (hi : i < w) :
    (comp w x).testBit i = !x.testBit i := by
  rw [comp_eq_xor w x hx, Nat.testBit_xor, testBit_two_pow_sub_one]
  simp [hi]

theorem popcount_comp {w x : Nat} (hx : x < 2 ^ w) :
    popcount (comp w x) = w - popcount x := by
  have hlt : comp w x < 2 ^ w := comp_lt_two_pow hx
  rw [popcount_eq_below hlt, popcount_eq_below hx]
  suffices ∀ B ≤ w, popcountBelow (comp w x) B + popcountBelow x B = B by
    have := this w (Nat.le_refl w); omega
  intro B hBw
  induction B with
  | zero => rfl
  | succ b ih =>
    unfold popcountBelow
    rw [testBit_comp hx (by omega)]
    have hih := ih (by omega)
    cases x.testBit b <;> simp <;> omega

/-- **Theorem 4E (Exact Complement Carry-Borrow Conjugacy):** -/
theorem complement_carry_borrow_conjugacy {w x : Nat} (hw : 0 < w) (hx : x < 2 ^ w) :
    comp w (F_sub_wrap w (comp w x)) = F_add_dual_wrap w x := by
  have hpc : popcount (comp w x) = w - popcount x := popcount_comp hx
  unfold F_sub_wrap F_add_dual_wrap
  rw [hpc]
  unfold comp
  let s := 2 ^ ((w - popcount x) % w)
  have hs_lt : s < 2 ^ w := two_pow_lt_two_pow (Nat.mod_lt _ hw)
  have hs_pos : 1 ≤ s := Nat.two_pow_pos _
  have h2w : 1 ≤ 2 ^ w := Nat.two_pow_pos w
  change 2 ^ w - 1 - (2 ^ w - 1 - x + 2 ^ w - s) % 2 ^ w = (x + s) % 2 ^ w
  by_cases hsum : x + s < 2 ^ w
  · have hmod1 : (x + s) % 2 ^ w = x + s := Nat.mod_eq_of_lt hsum
    have hmod2 : (2 ^ w - 1 - x + 2 ^ w - s) % 2 ^ w = 2 ^ w - 1 - (x + s) := by
      have hrew : 2 ^ w - 1 - x + 2 ^ w - s = (2 ^ w - 1 - (x + s)) + 2 ^ w := by omega
      rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod1, hmod2]; omega
  · have hmod1 : (x + s) % 2 ^ w = x + s - 2 ^ w := by
      have hrew : x + s = (x + s - 2 ^ w) + 2 ^ w := by omega
      calc (x + s) % 2 ^ w = ((x + s - 2 ^ w) + 2 ^ w) % 2 ^ w := congrArg (· % 2 ^ w) hrew
        _ = (x + s - 2 ^ w) % 2 ^ w := Nat.add_mod_right _ _
        _ = x + s - 2 ^ w := Nat.mod_eq_of_lt (by omega)
    have hmod2 : (2 ^ w - 1 - x + 2 ^ w - s) % 2 ^ w = 2 ^ w - 1 - (x + s - 2 ^ w) := by
      have hrew : 2 ^ w - 1 - x + 2 ^ w - s = 2 ^ w - 1 - (x + s - 2 ^ w) := by omega
      rw [hrew, Nat.mod_eq_of_lt (by omega)]
    rw [hmod1, hmod2]; omega

theorem F_add_dual_wrap_iter_conjugacy {w : Nat} (hw : 0 < w) :
    ∀ t x, x < 2 ^ w →
      iter (F_add_dual_wrap w) t x = comp w (iter (F_sub_wrap w) t (comp w x)) := by
  intro t
  induction t with
  | zero => intro x hx; simp [iter, comp_invol hx]
  | succ t ih =>
    intro x hx
    rw [iter_succ, iter_succ]
    have hstep_lt : F_sub_wrap w (comp w x) < 2 ^ w := F_sub_wrap_lt_two_pow w _
    have hfx_lt : F_add_dual_wrap w x < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    rw [ih (F_add_dual_wrap w x) hfx_lt, ← complement_carry_borrow_conjugacy hw hx,
        comp_invol hstep_lt]

/-- **Corollary 4F (Unique `(w + 1)`-Cycle at `0` for Carry-Synchronized Dual `F_add_dual_wrap w`):** -/
theorem F_add_dual_wrap_unique_cycle {w : Nat} (hw : 0 < w) :
    (∀ x < 2 ^ w, ∃ t, iter (F_add_dual_wrap w) t x = 0) ∧
    iter (F_add_dual_wrap w) (w + 1) 0 = 0 ∧
    (∀ t, 0 < t → t < w + 1 → iter (F_add_dual_wrap w) t 0 ≠ 0) := by
  have ⟨hall, hper, hmin⟩ := F_sub_wrap_unique_cycle hw
  have h0lt : 0 < 2 ^ w := Nat.two_pow_pos w
  have hc0 : comp w 0 = 2 ^ w - 1 := by unfold comp; omega
  have hc1 : comp w (2 ^ w - 1) = 0 := by unfold comp; omega
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht⟩ := hall (comp w x) (comp_lt_two_pow hx)
    refine ⟨t, ?_⟩
    rw [F_add_dual_wrap_iter_conjugacy hw t x hx, ht, hc1]
  · rw [F_add_dual_wrap_iter_conjugacy hw (w + 1) 0 h0lt, hc0, hper, hc1]
  · intro t ht0 htlt heq
    rw [F_add_dual_wrap_iter_conjugacy hw t 0 h0lt, hc0] at heq
    have hstep_lt : iter (F_sub_wrap w) t (2 ^ w - 1) < 2 ^ w := by
      cases t with
      | zero => omega
      | succ t' => rw [iter_succ_right]; exact F_sub_wrap_lt_two_pow w _
    have hcomp_eq : iter (F_sub_wrap w) t (2 ^ w - 1) = 2 ^ w - 1 := by
      have := congrArg (comp w) heq
      rw [comp_invol hstep_lt, hc0] at this
      exact this
    exact hmin t ht0 htlt hcomp_eq

-- ============================================================================
-- Section 8: Theorem 5 — Kernel-Checked Sharpness Counterexamples & Non-Vacuity
-- ============================================================================

/-- **Sharpness 1 (Carry vs. Borrow Desynchronization at `w = 3`):**
    `F_add_desync 3` has TWO disjoint cycles: a 4-cycle through `0` and a 3-cycle through `2`. -/
def F_add_desync (w x : Nat) : Nat := (x + 2 ^ (popcount x % w)) % 2 ^ w

theorem iter_mod_of_period {α : Type} (f : α → α) {P : Nat}
    {x : α} (hper : iter f P x = x) : ∀ t, iter f t x = iter f (t % P) x := by
  intro t
  have hdiv : t = P * (t / P) + t % P := (Nat.div_add_mod t P).symm
  have hmul : ∀ k, iter f (P * k) x = x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Nat.mul_succ, iter_add, ih, hper]
  have h1 : iter f t x = iter f (P * (t / P) + t % P) x :=
    congrArg (fun k => iter f k x) hdiv
  rw [h1, iter_add, hmul (t / P)]

theorem sharpness_carry_desync_w3 :
    iter (F_add_desync 3) 4 0 = 0 ∧
    iter (F_add_desync 3) 3 2 = 2 ∧
    (∀ t, iter (F_add_desync 3) t 0 ≠ 2) := by
  have h4 : iter (F_add_desync 3) 4 0 = 0 := by decide
  have h3 : iter (F_add_desync 3) 3 2 = 2 := by decide
  refine ⟨h4, h3, ?_⟩
  intro t
  rw [iter_mod_of_period (F_add_desync 3) h4 t]
  have hm : t % 4 < 4 := Nat.mod_lt t (by decide)
  match t % 4, hm with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | _ + 4, hm => omega

/-- **Sharpness 2 (Non-Injective Address Map `h(p) = p / 2` Breaks Any Unit Clock):** -/
def T_noninj (x : Nat) : Nat := x ^^^ 2 ^ (popcount x / 2)

theorem sharpness_non_injective_no_clock :
    T_noninj 0 = 1 ∧ T_noninj 1 = 0 ∧
    (∀ V : Nat → Int, ¬ (∀ x, V (T_noninj x) = V x - 1)) := by
  have h0 : T_noninj 0 = 1 := by decide
  have h1 : T_noninj 1 = 0 := by decide
  refine ⟨h0, h1, ?_⟩
  intro V hV
  have a := hV 0
  have b := hV 1
  rw [h0] at a
  rw [h1] at b
  omega

/-- **Sharpness 3 (Non-Coprime Affine Stride `a = 2, w = 4` Splits Unique `2w`-Cycle):** -/
def F_stride (w a x : Nat) : Nat := x ^^^ 2 ^ ((a * popcount x) % w)

theorem sharpness_non_coprime_stride :
    iter (F_stride 4 2) 4 0 = 0 ∧
    iter (F_stride 4 2) 4 2 = 2 ∧
    (∀ t, iter (F_stride 4 2) t 0 ≠ 2) := by
  have h0 : iter (F_stride 4 2) 4 0 = 0 := by decide
  have h2 : iter (F_stride 4 2) 4 2 = 2 := by decide
  refine ⟨h0, h2, ?_⟩
  intro t
  rw [iter_mod_of_period (F_stride 4 2) h0 t]
  have hm : t % 4 < 4 := Nat.mod_lt t (by decide)
  match t % 4, hm with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | _ + 4, hm => omega

/-- **Non-Vacuity Witness 1 (Non-Monotone Involution `h(p) = p ^^^ 1` in Engine I):** -/
def involutionCert : ClockCert :=
  bijectiveUnitClockCert (fun p => p ^^^ 1) (fun p => p ^^^ 1) (fun p => by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_xor])

theorem nonvacuity_involution_unit_clock (t x : Nat) :
    involutionCert.pot (iter involutionCert.step t x) = involutionCert.pot x - (t : Int) :=
  involutionCert.unit_clock_iter rfl rfl (fun _ => trivial) t x

theorem nonvacuity_involution_acyclic {t : Nat} (ht : 0 < t) (x : Nat) :
    iter involutionCert.step t x ≠ x :=
  involutionCert.no_cycles rfl rfl (fun _ => trivial) ht x

/-- **Non-Vacuity Witness 2 (Exact Synchronous Collision vs. Permanent Phase Separation):** -/
theorem nonvacuity_collision_and_separation :
    (V_unit 0 = V_unit 5 ∧ iter T_xor 1 0 = iter T_xor 1 5) ∧
    (V_unit 0 ≠ V_unit 1 ∧ ∀ t, iter T_xor t 0 ≠ iter T_xor t 1) := by
  have hV05 : V_unit 0 = V_unit 5 := by decide
  have hcol : iter T_xor 1 0 = iter T_xor 1 5 := by decide
  have hV01 : V_unit 0 ≠ V_unit 1 := by decide
  refine ⟨⟨hV05, hcol⟩, ⟨hV01, ?_⟩⟩
  intro t heq
  have := (T_xor_sync_collision_iff 0 1).mp ⟨t, heq⟩
  exact hV01 this

/-- **Sharp Quantitative Upper Bounds on Inversion Energy & Hitting Time (`∀ w, ∀ x < 2^w`):**
    1. `phi x ≤ popcount x * (w - popcount x)` and `4 * phi x ≤ w * w`.
    2. `2 * (V_unit x + w) ≤ w * (w + 1)` (i.e. exact hitting time `≤ C(w + 1, 2)`). -/
theorem indexSumBelow_le_top_block (x : Nat) : ∀ B,
    2 * weightSumBelow (fun i => (i : Int)) x B ≤
      (popcountBelow x B : Int) * (2 * (B : Int) - (popcountBelow x B : Int) - 1) := by
  intro B
  induction B with
  | zero => simp [weightSumBelow, popcountBelow]
  | succ b ih =>
    unfold weightSumBelow popcountBelow
    have hle : popcountBelow x b ≤ b := popcountBelow_le x b
    cases hbit : x.testBit b
    · simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero, Nat.add_zero]
      have hstep : ((b + 1 : Nat) : Int) = (b : Int) + 1 := by omega
      rw [hstep]
      have hmul : (popcountBelow x b : Int) * (2 * ((b : Int) + 1) - (popcountBelow x b : Int) - 1) =
          (popcountBelow x b : Int) * (2 * (b : Int) - (popcountBelow x b : Int) - 1) +
          2 * (popcountBelow x b : Int) := by
        have hrew : 2 * ((b : Int) + 1) - (popcountBelow x b : Int) - 1 =
            (2 * (b : Int) - (popcountBelow x b : Int) - 1) + 2 := by omega
        rw [hrew, Int.mul_add]
        omega
      rw [hmul]
      omega
    · simp only [↓reduceIte]
      have hstepb : ((b + 1 : Nat) : Int) = (b : Int) + 1 := by omega
      have hstepp : ((popcountBelow x b + 1 : Nat) : Int) = (popcountBelow x b : Int) + 1 := by omega
      rw [hstepb, hstepp]
      have halg : ((popcountBelow x b : Int) + 1) * (2 * ((b : Int) + 1) - ((popcountBelow x b : Int) + 1) - 1) =
          (popcountBelow x b : Int) * (2 * (b : Int) - (popcountBelow x b : Int) - 1) + 2 * (b : Int) := by
        have hrew : 2 * ((b : Int) + 1) - ((popcountBelow x b : Int) + 1) - 1 =
            2 * (b : Int) - (popcountBelow x b : Int) := by omega
        rw [hrew, Int.add_mul, Int.one_mul]
        have hrew2 : 2 * (b : Int) - (popcountBelow x b : Int) =
            (2 * (b : Int) - (popcountBelow x b : Int) - 1) + 1 := by omega
        have hstep1 : (popcountBelow x b : Int) * (2 * (b : Int) - (popcountBelow x b : Int)) =
            (popcountBelow x b : Int) * ((2 * (b : Int) - (popcountBelow x b : Int) - 1) + 1) :=
          congrArg (fun z => (popcountBelow x b : Int) * z) hrew2
        rw [hstep1, Int.mul_add, Int.mul_one]
        omega
      rw [halg]
      omega

theorem phi_le_pop_mul_sub {w x : Nat} (hx : x < 2 ^ w) :
    phi x ≤ (popcount x : Int) * ((w : Int) - (popcount x : Int)) := by
  have h1 := two_mul_phi x
  have h2 := indexSumBelow_le_top_block x w
  rw [← popcount_eq_below hx] at h2
  have hws : weightSumBelow (fun i => (i : Int)) x w = indexSum x := (weightSum_eq_below _ hx).symm
  rw [hws] at h2
  have halg : (popcount x : Int) * (2 * (w : Int) - (popcount x : Int) - 1) -
      (popcount x : Int) * ((popcount x : Int) - 1) =
      2 * ((popcount x : Int) * ((w : Int) - (popcount x : Int))) := by
    rw [← Int.mul_sub]
    have hrew : 2 * (w : Int) - (popcount x : Int) - 1 - ((popcount x : Int) - 1) =
        2 * ((w : Int) - (popcount x : Int)) := by omega
    rw [hrew, Int.mul_left_comm]
  omega

theorem four_mul_phi_le_sq {w x : Nat} (hx : x < 2 ^ w) :
    4 * phi x ≤ (w : Int) * (w : Int) := by
  have h1 := phi_le_pop_mul_sub hx
  have hsq : 0 ≤ ((w : Int) - 2 * (popcount x : Int)) * ((w : Int) - 2 * (popcount x : Int)) := by
    by_cases h : 0 ≤ (w : Int) - 2 * (popcount x : Int)
    · exact Int.mul_nonneg h h
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hexp : ((w : Int) - 2 * (popcount x : Int)) * ((w : Int) - 2 * (popcount x : Int)) =
      (w : Int) * (w : Int) - 4 * ((popcount x : Int) * ((w : Int) - (popcount x : Int))) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub]
    have hcomm : (w : Int) * (2 * (popcount x : Int)) = (2 * (popcount x : Int)) * (w : Int) :=
      Int.mul_comm _ _
    have h4a : 4 * ((popcount x : Int) * (w : Int)) = 2 * ((2 * (popcount x : Int)) * (w : Int)) := by
      rw [Int.mul_assoc]; omega
    have h4b : 4 * ((popcount x : Int) * (popcount x : Int)) =
        (2 * (popcount x : Int)) * (2 * (popcount x : Int)) := by
      calc 4 * ((popcount x : Int) * (popcount x : Int))
          = (2 * 2) * ((popcount x : Int) * (popcount x : Int)) := rfl
        _ = 2 * (2 * ((popcount x : Int) * (popcount x : Int))) := Int.mul_assoc _ _ _
        _ = 2 * ((popcount x : Int) * (2 * (popcount x : Int))) :=
            congrArg (2 * ·) (Int.mul_left_comm 2 _ _)
        _ = (2 * (popcount x : Int)) * (2 * (popcount x : Int)) := (Int.mul_assoc _ _ _).symm
    omega
  omega

theorem two_mul_hitting_time_le_tri {w x : Nat} (hx : x < 2 ^ w) :
    2 * (V_unit x + (w : Int)) ≤ (w : Int) * ((w : Int) + 1) := by
  have h1 := phi_le_pop_mul_sub hx
  rw [V_unit_eq_two_phi_sub_pop]
  have hsq : 0 ≤ ((w : Int) - 2 * (popcount x : Int)) * ((w : Int) - 2 * (popcount x : Int) - 1) := by
    by_cases h : (w : Int) - 2 * (popcount x : Int) ≥ 1
    · exact Int.mul_nonneg (by omega) (by omega)
    · have hle : (w : Int) - 2 * (popcount x : Int) ≤ 0 := by omega
      have hle1 : (w : Int) - 2 * (popcount x : Int) - 1 ≤ 0 := by omega
      exact Int.mul_nonneg_of_nonpos_of_nonpos hle hle1
  have hdist : (popcount x : Int) * ((w : Int) - (popcount x : Int)) =
      (popcount x : Int) * (w : Int) - (popcount x : Int) * (popcount x : Int) :=
    Int.mul_sub _ _ _
  have hexp : ((w : Int) - 2 * (popcount x : Int)) * ((w : Int) - 2 * (popcount x : Int) - 1) =
      (w : Int) * ((w : Int) + 1) -
      2 * (2 * ((popcount x : Int) * (w : Int) - (popcount x : Int) * (popcount x : Int)) -
           (popcount x : Int) + (w : Int)) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_one, Int.mul_add, Int.mul_one]
    have hcomm : (w : Int) * (2 * (popcount x : Int)) = (2 * (popcount x : Int)) * (w : Int) :=
      Int.mul_comm _ _
    have h4a : 4 * ((popcount x : Int) * (w : Int)) = 2 * ((2 * (popcount x : Int)) * (w : Int)) := by
      rw [Int.mul_assoc]; omega
    have h4b : 4 * ((popcount x : Int) * (popcount x : Int)) =
        (2 * (popcount x : Int)) * (2 * (popcount x : Int)) := by
      calc 4 * ((popcount x : Int) * (popcount x : Int))
          = (2 * 2) * ((popcount x : Int) * (popcount x : Int)) := rfl
        _ = 2 * (2 * ((popcount x : Int) * (popcount x : Int))) := Int.mul_assoc _ _ _
        _ = 2 * ((popcount x : Int) * (2 * (popcount x : Int))) :=
            congrArg (2 * ·) (Int.mul_left_comm 2 _ _)
        _ = (2 * (popcount x : Int)) * (2 * (popcount x : Int)) := (Int.mul_assoc _ _ _).symm
    omega
  omega

/-- **Non-Vacuity Witness 3 (Concrete Borrow-Acceleration Jump of Length `d = 3` at `x = 16`):** -/
theorem nonvacuity_borrow_jump_x16 :
    T_sub 16 = 14 ∧
    iter T_xor 4 16 = 14 ∧
    phi 16 = 4 ∧
    phi 14 = 3 := by
  decide


-- ============================================================================
-- Section 9: Axiom Verification Receipts (`#print axioms`)
-- ============================================================================

end Dynsil11
